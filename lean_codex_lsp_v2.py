#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Optional
from urllib.parse import quote, unquote, urlparse

DECL_RE = re.compile(
    r"^\s*(?:@[A-Za-z0-9_.\[\]`' -]+\s+)*"
    r"(theorem|lemma|example|def|instance|structure|class|inductive|abbrev|opaque|axiom|mutual)\b"
)
NAMESPACE_OPEN_RE = re.compile(r"^\s*(namespace|section)\b")
NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\b")


class JsonRpcError(RuntimeError):
    pass


@dataclass
class DiagnosticState:
    version: Optional[int]
    diagnostics: list[dict[str, Any]]
    updated_at: float


class LeanCodexLspV2:
    """
    Persistent newline-delimited JSON wrapper around `lake serve`.

    v2 improvements over v1:
      - incremental range edits (`apply_edit` / `apply_edits`)
      - declaration-scoped packets (`check_decl`)
      - hash-based omission of unchanged declaration/goal payloads
      - reads current text from the in-memory open document, not disk
      - compact packet mode for lower token usage
    """

    def __init__(self, workspace: Path, lake_cmd: Optional[list[str]] = None, verbose: bool = False):
        self.workspace = workspace.resolve()
        self.verbose = verbose
        self.lake_cmd = lake_cmd or ["lake", "serve"]
        self.proc: Optional[subprocess.Popen[bytes]] = None
        self._next_id = 1
        self._write_lock = threading.Lock()
        self._pending: dict[int, queue.Queue[Any]] = {}
        self._reader_thread: Optional[threading.Thread] = None
        self._stderr_thread: Optional[threading.Thread] = None
        self._running = False
        self._opened: dict[str, dict[str, Any]] = {}
        self._diagnostics: dict[str, DiagnosticState] = {}

    # -----------------------------
    # lifecycle
    # -----------------------------

    def _log(self, *parts: Any) -> None:
        if self.verbose:
            print(*parts, file=sys.stderr)

    def start(self) -> None:
        if self.proc is not None:
            return
        self.proc = subprocess.Popen(
            self.lake_cmd,
            cwd=str(self.workspace),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self._running = True
        self._reader_thread = threading.Thread(target=self._reader_loop, daemon=True)
        self._reader_thread.start()
        self._stderr_thread = threading.Thread(target=self._stderr_loop, daemon=True)
        self._stderr_thread.start()
        self._initialize()

    def stop(self) -> None:
        if self.proc is None:
            return
        try:
            self.request("shutdown", {})
        except Exception:
            pass
        try:
            self.notify("exit", {})
        except Exception:
            pass
        self._running = False
        try:
            self.proc.terminate()
            self.proc.wait(timeout=2)
        except Exception:
            try:
                self.proc.kill()
            except Exception:
                pass
        self.proc = None

    # -----------------------------
    # JSON-RPC transport
    # -----------------------------

    def _stderr_loop(self) -> None:
        assert self.proc is not None and self.proc.stderr is not None
        for raw in iter(self.proc.stderr.readline, b""):
            if not raw:
                break
            self._log("[lake-serve]", raw.decode("utf-8", errors="replace").rstrip())

    def _reader_loop(self) -> None:
        assert self.proc is not None and self.proc.stdout is not None
        stream = self.proc.stdout
        try:
            while self._running:
                headers: dict[str, str] = {}
                while True:
                    line = stream.readline()
                    if not line:
                        return
                    if line in (b"\r\n", b"\n"):
                        break
                    text = line.decode("ascii", errors="replace").strip()
                    if ":" in text:
                        k, v = text.split(":", 1)
                        headers[k.strip().lower()] = v.strip()
                length_s = headers.get("content-length")
                if not length_s:
                    continue
                body = stream.read(int(length_s))
                msg = json.loads(body.decode("utf-8"))
                self._handle_server_message(msg)
        except Exception as exc:
            self._log("reader loop failed:", repr(exc))

    def _send(self, payload: dict[str, Any]) -> None:
        assert self.proc is not None and self.proc.stdin is not None
        data = json.dumps(payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        header = f"Content-Length: {len(data)}\r\n\r\n".encode("ascii")
        with self._write_lock:
            self.proc.stdin.write(header)
            self.proc.stdin.write(data)
            self.proc.stdin.flush()

    def request(self, method: str, params: Any, timeout: float = 30.0) -> Any:
        msg_id = self._next_id
        self._next_id += 1
        q: queue.Queue[Any] = queue.Queue(maxsize=1)
        self._pending[msg_id] = q
        self._send({"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params})
        try:
            resp = q.get(timeout=timeout)
        except queue.Empty as exc:
            self._pending.pop(msg_id, None)
            raise TimeoutError(f"Timed out waiting for {method}") from exc
        if isinstance(resp, Exception):
            raise resp
        return resp

    def notify(self, method: str, params: Any) -> None:
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def _handle_server_message(self, msg: dict[str, Any]) -> None:
        if "id" in msg and "method" not in msg:
            q = self._pending.pop(int(msg["id"]), None)
            if q is not None:
                if "error" in msg:
                    err = msg["error"]
                    q.put(JsonRpcError(f"{err.get('code')}: {err.get('message')}"))
                else:
                    q.put(msg.get("result"))
            return

        method = msg.get("method")
        params = msg.get("params", {})

        if method == "textDocument/publishDiagnostics":
            uri = params.get("uri")
            if uri:
                self._diagnostics[uri] = DiagnosticState(
                    version=params.get("version"),
                    diagnostics=list(params.get("diagnostics", [])),
                    updated_at=time.time(),
                )
            return

        if "id" in msg and method:
            self._handle_server_request(msg)
            return

    def _handle_server_request(self, msg: dict[str, Any]) -> None:
        method = msg.get("method")
        params = msg.get("params", {})
        if method == "workspace/configuration":
            items = params.get("items", [])
            result = [None for _ in items]
        elif method in {
            "window/workDoneProgress/create",
            "client/registerCapability",
            "client/unregisterCapability",
        }:
            result = None
        else:
            result = None
        self._send({"jsonrpc": "2.0", "id": msg["id"], "result": result})

    def _initialize(self) -> None:
        root_uri = path_to_uri(self.workspace)
        caps = {
            "workspace": {"configuration": True},
            "textDocument": {
                "publishDiagnostics": {"relatedInformation": True},
                "hover": {"contentFormat": ["markdown", "plaintext"]},
                "definition": {"linkSupport": True},
                "synchronization": {"didSave": False, "dynamicRegistration": False, "willSave": False},
            },
            "window": {"workDoneProgress": True},
        }
        self.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": root_uri,
                "workspaceFolders": [{"uri": root_uri, "name": self.workspace.name}],
                "capabilities": caps,
                "clientInfo": {"name": "lean-codex-lsp-v2", "version": "0.2.0"},
                "initializationOptions": {"editDelay": 0},
            },
            timeout=60.0,
        )
        self.notify("initialized", {})

    # -----------------------------
    # document state
    # -----------------------------

    def current_text(self, path: Path) -> str:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        rec = self._opened.get(uri)
        if rec is not None:
            return str(rec["text"])
        return path.read_text(encoding="utf-8")

    def current_lines(self, path: Path) -> list[str]:
        return self.current_text(path).splitlines()

    def open_file(self, path: Path, text: Optional[str] = None, dependency_build_mode: Optional[str] = None) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        text = text if text is not None else path.read_text(encoding="utf-8")
        uri = path_to_uri(path)
        rec = self._opened.get(uri)
        if rec is None:
            rec = {"version": 1, "path": path, "text": text}
            self._opened[uri] = rec
            params: dict[str, Any] = {
                "textDocument": {
                    "uri": uri,
                    "languageId": "lean",
                    "version": rec["version"],
                    "text": text,
                }
            }
            if dependency_build_mode is not None:
                params["dependencyBuildMode"] = dependency_build_mode
            self.notify("textDocument/didOpen", params)
        else:
            if text != rec["text"]:
                rec["version"] += 1
                rec["text"] = text
                self.notify(
                    "textDocument/didChange",
                    {
                        "textDocument": {"uri": uri, "version": rec["version"]},
                        "contentChanges": [{"text": text}],
                    },
                )
        return {"uri": uri, "version": rec["version"]}

    def ensure_open(self, path: Path, text: Optional[str] = None, dependency_build_mode: Optional[str] = None) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if uri not in self._opened:
            return self.open_file(path, text=text, dependency_build_mode=dependency_build_mode)
        if text is not None and text != self._opened[uri]["text"]:
            return self.open_file(path, text=text)
        return {"uri": uri, "version": self._opened[uri]["version"]}

    def reopen_file(self, path: Path, text: Optional[str] = None, dependency_build_mode: Optional[str] = None) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if text is None:
            text = path.read_text(encoding="utf-8")
        self.close_file(path)
        self._diagnostics.pop(uri, None)
        return self.open_file(path, text=text, dependency_build_mode=dependency_build_mode)

    def close_file(self, path: Path) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if uri in self._opened:
            self.notify("textDocument/didClose", {"textDocument": {"uri": uri}})
            self._opened.pop(uri, None)
        return {"uri": uri, "closed": True}

    def _set_text_and_notify(self, path: Path, new_text: str) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        rec = self._opened.get(uri)
        if rec is None:
            return self.open_file(path, text=new_text)
        if rec["text"] == new_text:
            return {"uri": uri, "version": rec["version"]}
        rec["version"] += 1
        rec["text"] = new_text
        self.notify(
            "textDocument/didChange",
            {
                "textDocument": {"uri": uri, "version": rec["version"]},
                "contentChanges": [{"text": new_text}],
            },
        )
        return {"uri": uri, "version": rec["version"]}

    def apply_edits(self, path: Path, edits: list[dict[str, Any]], wait_for_diagnostics: bool = True, timeout: float = 60.0) -> dict[str, Any]:
        """
        Apply localized 1-based user-coordinate edits to the in-memory document and send
        ranged didChange notifications to Lean. Each edit:
          {startLine,startColumn,endLine,endColumn,text}
        Columns are 1-based codepoint columns in the local wrapper API.
        """
        path = resolve_under_workspace(self.workspace, path)
        info = self.ensure_open(path)
        uri = info["uri"]
        rec = self._opened[uri]
        text = str(rec["text"])
        lines = text.splitlines(keepends=True)
        if text.endswith("\n"):
            logical_lines = text.splitlines()
            trailing_newline = True
        else:
            logical_lines = text.splitlines()
            trailing_newline = False
        if not logical_lines and text == "":
            logical_lines = [""]

        # Sort descending by start offset to preserve user coordinates.
        prepared: list[tuple[int, int, dict[str, Any]]] = []
        for e in edits:
            sl = int(e["startLine"])
            sc = int(e["startColumn"])
            el = int(e.get("endLine", sl))
            ec = int(e.get("endColumn", sc))
            start_off = text_offset_from_user(text, sl, sc)
            end_off = text_offset_from_user(text, el, ec)
            prepared.append((start_off, end_off, e))
        prepared.sort(key=lambda t: (t[0], t[1]), reverse=True)

        new_text = text
        content_changes: list[dict[str, Any]] = []
        for start_off, end_off, e in prepared:
            sl = int(e["startLine"])
            sc = int(e["startColumn"])
            el = int(e.get("endLine", sl))
            ec = int(e.get("endColumn", sc))
            replacement = str(e.get("text", ""))
            old_lines = new_text.splitlines()
            start_char = user_column_to_utf16(old_lines[sl - 1] if 0 < sl <= len(old_lines) else "", sc)
            end_char = user_column_to_utf16(old_lines[el - 1] if 0 < el <= len(old_lines) else "", ec)
            new_text = new_text[:start_off] + replacement + new_text[end_off:]
            content_changes.append(
                {
                    "range": {
                        "start": {"line": sl - 1, "character": start_char},
                        "end": {"line": el - 1, "character": end_char},
                    },
                    "text": replacement,
                }
            )

        rec["version"] += 1
        rec["text"] = new_text
        self.notify(
            "textDocument/didChange",
            {
                "textDocument": {"uri": uri, "version": rec["version"]},
                "contentChanges": content_changes,
            },
        )
        if wait_for_diagnostics:
            self.wait_for_diagnostics(path, version=rec["version"], timeout=timeout)
        return {
            "ok": True,
            "uri": uri,
            "version": rec["version"],
            "editCount": len(edits),
            "changedBytes": len(new_text.encode("utf-8")) - len(text.encode("utf-8")),
        }

    def wait_for_diagnostics(self, path: Path, version: Optional[int] = None, timeout: float = 60.0) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if version is None:
            info = self.ensure_open(path)
            version = int(info["version"])
        self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version}, timeout=timeout)
        state = self._diagnostics.get(uri)
        return {
            "uri": uri,
            "version": version,
            "diagnosticCount": len(state.diagnostics) if state else 0,
        }

    # -----------------------------
    # LSP convenience
    # -----------------------------

    def diagnostics(self, path: Path) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        state = self._diagnostics.get(uri)
        return {
            "uri": uri,
            "version": state.version if state else None,
            "diagnostics": state.diagnostics if state else [],
        }

    def hover(self, path: Path, line: int, column: int) -> Any:
        path = resolve_under_workspace(self.workspace, path)
        self.ensure_open(path)
        return self.request(
            "textDocument/hover",
            {"textDocument": {"uri": path_to_uri(path)}, "position": lsp_position_from_user_lines(self.current_lines(path), line, column)},
        )

    def definition(self, path: Path, line: int, column: int) -> Any:
        path = resolve_under_workspace(self.workspace, path)
        self.ensure_open(path)
        return self.request(
            "textDocument/definition",
            {"textDocument": {"uri": path_to_uri(path)}, "position": lsp_position_from_user_lines(self.current_lines(path), line, column)},
        )

    def plain_goal(self, path: Path, line: int, column: int) -> Any:
        path = resolve_under_workspace(self.workspace, path)
        self.ensure_open(path)
        return self.request(
            "$/lean/plainGoal",
            {"textDocument": {"uri": path_to_uri(path)}, "position": lsp_position_from_user_lines(self.current_lines(path), line, column)},
        )

    def plain_term_goal(self, path: Path, line: int, column: int) -> Any:
        path = resolve_under_workspace(self.workspace, path)
        self.ensure_open(path)
        return self.request(
            "$/lean/plainTermGoal",
            {"textDocument": {"uri": path_to_uri(path)}, "position": lsp_position_from_user_lines(self.current_lines(path), line, column)},
        )

    # -----------------------------
    # high-level packets
    # -----------------------------

    def _first_diagnostic(self, path: Path) -> tuple[Optional[dict[str, Any]], list[dict[str, Any]], Optional[int]]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        state = self._diagnostics.get(uri)
        diags = sorted((state.diagnostics if state else []), key=diagnostic_sort_key)
        first = next((d for d in diags if d.get("severity") == 1), diags[0] if diags else None)
        return first, diags, state.version if state else None

    def check(self, path: Path, text: Optional[str] = None, context: int = 20, dependency_build_mode: Optional[str] = None) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if text is None and uri in self._opened:
            info = self.reopen_file(path, dependency_build_mode=dependency_build_mode)
        else:
            info = self.open_file(path, text=text, dependency_build_mode=dependency_build_mode)
        self.wait_for_diagnostics(path, version=int(info["version"]))
        return self.first_error_packet(path, context=context)

    def first_error_packet(self, path: Path, context: int = 20) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        src = self.current_text(path)
        lines = src.splitlines()
        first, diags, version = self._first_diagnostic(path)
        packet: dict[str, Any] = {
            "ok": not any(d.get("severity") == 1 for d in diags),
            "path": str(path),
            "uri": path_to_uri(path),
            "version": version,
            "diagnosticCount": len(diags),
        }
        if first is None:
            packet["summary"] = "No diagnostics available."
            return packet
        start = first.get("range", {}).get("start", {"line": 0, "character": 0})
        line1 = int(start.get("line", 0)) + 1
        col1 = utf16_column_to_user_column(lines[line1 - 1] if 0 < line1 <= len(lines) else "", int(start.get("character", 0)))
        packet["firstDiagnostic"] = diagnostic_payload(first, line1, col1)
        packet["declHeader"] = find_decl_header(lines, line1)
        packet["sourceContext"] = context_block(lines, line1, context)
        try:
            packet["plainGoal"] = self.plain_goal(path, line1, col1)
        except Exception as exc:
            packet["plainGoal"] = {"error": str(exc)}
        try:
            packet["plainTermGoal"] = self.plain_term_goal(path, line1, col1)
        except Exception as exc:
            packet["plainTermGoal"] = {"error": str(exc)}
        return packet

    def check_decl(
        self,
        path: Path,
        text: Optional[str] = None,
        dependency_build_mode: Optional[str] = None,
        known_decl_hash: Optional[str] = None,
        known_goal_hash: Optional[str] = None,
        include_term_goal: bool = True,
    ) -> dict[str, Any]:
        path = resolve_under_workspace(self.workspace, path)
        uri = path_to_uri(path)
        if text is None and uri in self._opened:
            info = self.reopen_file(path, dependency_build_mode=dependency_build_mode)
        else:
            info = self.open_file(path, text=text, dependency_build_mode=dependency_build_mode)
        self.wait_for_diagnostics(path, version=int(info["version"]))

        src = self.current_text(path)
        lines = src.splitlines()
        first, diags, version = self._first_diagnostic(path)
        packet: dict[str, Any] = {
            "ok": not any(d.get("severity") == 1 for d in diags),
            "path": str(path),
            "uri": path_to_uri(path),
            "version": version,
            "diagnosticCount": len(diags),
        }
        if first is None:
            packet["summary"] = "No diagnostics available."
            return packet

        start = first.get("range", {}).get("start", {"line": 0, "character": 0})
        line1 = int(start.get("line", 0)) + 1
        col1 = utf16_column_to_user_column(lines[line1 - 1] if 0 < line1 <= len(lines) else "", int(start.get("character", 0)))
        packet["firstDiagnostic"] = diagnostic_payload(first, line1, col1)
        packet["diagnosticHash"] = stable_hash_json(packet["firstDiagnostic"])

        region = find_decl_region(lines, line1)
        decl_text = region["text"]
        decl_hash = stable_hash_text(decl_text)
        packet["decl"] = {
            "startLine": region["startLine"],
            "endLine": region["endLine"],
            "headerLine": region["headerLine"],
            "headerText": region["headerText"],
            "hash": decl_hash,
            "sameAsKnown": decl_hash == known_decl_hash,
        }
        if decl_hash != known_decl_hash:
            packet["decl"]["text"] = decl_text

        goal_payload: dict[str, Any] = {}
        try:
            goal_payload["plainGoal"] = self.plain_goal(path, line1, col1)
        except Exception as exc:
            goal_payload["plainGoal"] = {"error": str(exc)}
        if include_term_goal:
            try:
                goal_payload["plainTermGoal"] = self.plain_term_goal(path, line1, col1)
            except Exception as exc:
                goal_payload["plainTermGoal"] = {"error": str(exc)}
        goal_hash = stable_hash_json(goal_payload)
        packet["goal"] = {"hash": goal_hash, "sameAsKnown": goal_hash == known_goal_hash}
        if goal_hash != known_goal_hash:
            packet["goal"].update(goal_payload)

        packet["compactPromptSeed"] = {
            "task": "Fix only the first Lean diagnostic.",
            "focus": [
                "Use the diagnostic plus the enclosing declaration only.",
                "Ignore later diagnostics.",
                "Prefer a minimal localized edit.",
                "If decl.sameAsKnown or goal.sameAsKnown is true, reuse prior context instead of asking for it again.",
            ],
        }
        return packet

    # -----------------------------
    # external command protocol
    # -----------------------------

    def handle_command(self, req: dict[str, Any]) -> dict[str, Any]:
        cmd = req.get("cmd")
        if not isinstance(cmd, str):
            raise ValueError("Missing string field 'cmd'")

        if cmd == "open":
            out = self.open_file(Path(req["path"]), text=req.get("text"), dependency_build_mode=req.get("dependencyBuildMode"))
            if req.get("waitForDiagnostics", True):
                self.wait_for_diagnostics(Path(req["path"]), version=int(out["version"]), timeout=float(req.get("timeout", 60.0)))
            return {"ok": True, **out}

        if cmd == "update":
            out = self._set_text_and_notify(Path(req["path"]), str(req.get("text", "")))
            if req.get("waitForDiagnostics", True):
                self.wait_for_diagnostics(Path(req["path"]), version=int(out["version"]), timeout=float(req.get("timeout", 60.0)))
            return {"ok": True, **out}

        if cmd == "apply_edit":
            edit = {
                "startLine": req["startLine"],
                "startColumn": req["startColumn"],
                "endLine": req.get("endLine", req["startLine"]),
                "endColumn": req.get("endColumn", req["startColumn"]),
                "text": req.get("text", ""),
            }
            return self.apply_edits(Path(req["path"]), [edit], wait_for_diagnostics=req.get("waitForDiagnostics", True), timeout=float(req.get("timeout", 60.0)))

        if cmd == "apply_edits":
            return self.apply_edits(Path(req["path"]), list(req["edits"]), wait_for_diagnostics=req.get("waitForDiagnostics", True), timeout=float(req.get("timeout", 60.0)))

        if cmd == "close":
            return {"ok": True, **self.close_file(Path(req["path"]))}

        if cmd == "wait":
            return {"ok": True, **self.wait_for_diagnostics(Path(req["path"]), version=req.get("version"), timeout=float(req.get("timeout", 60.0)))}

        if cmd == "diagnostics":
            return {"ok": True, **self.diagnostics(Path(req["path"]))}

        if cmd == "check":
            return self.check(Path(req["path"]), text=req.get("text"), context=int(req.get("context", 20)), dependency_build_mode=req.get("dependencyBuildMode"))

        if cmd == "check_decl":
            return self.check_decl(
                Path(req["path"]),
                text=req.get("text"),
                dependency_build_mode=req.get("dependencyBuildMode"),
                known_decl_hash=req.get("knownDeclHash"),
                known_goal_hash=req.get("knownGoalHash"),
                include_term_goal=bool(req.get("includeTermGoal", True)),
            )

        if cmd == "plain_goal":
            return {"ok": True, "result": self.plain_goal(Path(req["path"]), int(req["line"]), int(req["column"]))}

        if cmd == "plain_term_goal":
            return {"ok": True, "result": self.plain_term_goal(Path(req["path"]), int(req["line"]), int(req["column"]))}

        if cmd == "hover":
            return {"ok": True, "result": self.hover(Path(req["path"]), int(req["line"]), int(req["column"]))}

        if cmd == "definition":
            return {"ok": True, "result": self.definition(Path(req["path"]), int(req["line"]), int(req["column"]))}

        if cmd == "shutdown":
            self.stop()
            return {"ok": True, "shutdown": True}

        raise ValueError(f"Unknown command: {cmd}")

    def serve_stdio(self) -> int:
        self.start()
        for raw in sys.stdin:
            raw = raw.strip()
            if not raw:
                continue
            try:
                req = json.loads(raw)
                resp = self.handle_command(req)
            except Exception as exc:
                resp = {"ok": False, "error": str(exc)}
            sys.stdout.write(json.dumps(resp, ensure_ascii=False) + "\n")
            sys.stdout.flush()
            if resp.get("shutdown"):
                return 0
        self.stop()
        return 0


# -----------------------------
# helper functions
# -----------------------------


def path_to_uri(path: Path) -> str:
    path = path.resolve()
    return "file://" + quote(str(path).replace(os.sep, "/"), safe="/:+-._~")


def uri_to_path(uri: str) -> Path:
    parsed = urlparse(uri)
    if parsed.scheme != "file":
        raise ValueError(f"Unsupported URI scheme: {parsed.scheme}")
    return Path(unquote(parsed.path))


def resolve_under_workspace(workspace: Path, path: Path) -> Path:
    p = path if path.is_absolute() else (workspace / path)
    return p.resolve()


def severity_name(sev: Any) -> str:
    return {1: "error", 2: "warning", 3: "information", 4: "hint"}.get(sev, str(sev))


def diagnostic_sort_key(d: dict[str, Any]) -> tuple[int, int, int, int, int]:
    rng = d.get("range", {})
    start = rng.get("start", {})
    end = rng.get("end", {})
    return (
        int(start.get("line", 0)),
        int(start.get("character", 0)),
        int(end.get("line", 0)),
        int(end.get("character", 0)),
        int(d.get("severity", 99)),
    )


def stable_hash_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]


def stable_hash_json(obj: Any) -> str:
    blob = json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return stable_hash_text(blob)


def user_column_to_utf16(line: str, column1: int) -> int:
    column1 = max(1, column1)
    prefix = line[: column1 - 1]
    return len(prefix.encode("utf-16-le")) // 2


def utf16_column_to_user_column(line: str, utf16_col0: int) -> int:
    target_units = max(0, utf16_col0)
    units = 0
    for idx, ch in enumerate(line, start=1):
        ch_units = len(ch.encode("utf-16-le")) // 2
        if units >= target_units:
            return idx
        units += ch_units
        if units > target_units:
            return idx
    return len(line) + 1


def lsp_position_from_user_lines(lines: list[str], line1: int, column1: int) -> dict[str, int]:
    if line1 < 1 or line1 > max(1, len(lines)):
        raise ValueError(f"line out of range: {line1}")
    line = lines[line1 - 1] if lines else ""
    return {"line": line1 - 1, "character": user_column_to_utf16(line, column1)}


def text_offset_from_user(text: str, line1: int, column1: int) -> int:
    if line1 < 1:
        raise ValueError(f"line out of range: {line1}")
    parts = text.splitlines(keepends=True)
    if not parts:
        parts = [""]
    if line1 > len(parts):
        if line1 == len(parts) + 1 and parts[-1].endswith("\n"):
            return len(text)
        raise ValueError(f"line out of range: {line1}")
    prefix = "".join(parts[: line1 - 1])
    line = parts[line1 - 1]
    line_no_nl = line[:-1] if line.endswith("\n") else line
    col = max(1, column1)
    if col > len(line_no_nl) + 1:
        raise ValueError(f"column out of range: {column1}")
    return len(prefix) + (col - 1)


def diagnostic_payload(d: dict[str, Any], line1: int, col1: int) -> dict[str, Any]:
    return {
        "severity": severity_name(d.get("severity")),
        "message": d.get("message", ""),
        "line": line1,
        "column": col1,
        "range": d.get("range"),
        "source": d.get("source"),
        "code": d.get("code"),
    }


def find_decl_header(src_lines: list[str], line_no: int) -> Optional[dict[str, Any]]:
    if not src_lines:
        return None
    idx = min(max(line_no - 1, 0), len(src_lines) - 1)
    for i in range(idx, -1, -1):
        line = src_lines[i]
        if DECL_RE.match(line):
            return {"line": i + 1, "text": line.rstrip()}
    return None


def context_block(src_lines: list[str], line_no: int, radius: int) -> dict[str, Any]:
    if not src_lines:
        return {"startLine": None, "endLine": None, "text": None}
    start = max(1, line_no - radius)
    end = min(len(src_lines), line_no + radius)
    numbered = []
    for i in range(start, end + 1):
        marker = ">>" if i == line_no else "  "
        numbered.append(f"{marker} {i:4d}: {src_lines[i - 1]}")
    return {"startLine": start, "endLine": end, "text": "\n".join(numbered)}


def find_decl_region(src_lines: list[str], line_no: int) -> dict[str, Any]:
    """
    Heuristic declaration region: nearest preceding declaration header to the line,
    continuing until the next declaration header at top level-ish or EOF.
    """
    if not src_lines:
        return {"startLine": 1, "endLine": 1, "headerLine": None, "headerText": None, "text": ""}
    header = find_decl_header(src_lines, line_no)
    if header is None:
        ctx = context_block(src_lines, line_no, 20)
        return {
            "startLine": ctx["startLine"],
            "endLine": ctx["endLine"],
            "headerLine": None,
            "headerText": None,
            "text": ctx["text"] or "",
        }
    start = int(header["line"])
    end = len(src_lines)
    nesting = 0
    for i in range(start, len(src_lines)):
        line = src_lines[i]
        if i + 1 > start and DECL_RE.match(line) and nesting == 0:
            end = i
            break
        if NAMESPACE_OPEN_RE.match(line):
            nesting += 1
        elif NAMESPACE_CLOSE_RE.match(line):
            nesting = max(0, nesting - 1)
    text = "\n".join(src_lines[start - 1 : end])
    return {
        "startLine": start,
        "endLine": end,
        "headerLine": header["line"],
        "headerText": header["text"],
        "text": text,
    }


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Persistent Codex-friendly wrapper around lake serve (v2)")
    p.add_argument("--workspace", default=".", help="Lean project root")
    p.add_argument("--verbose", action="store_true")
    p.add_argument("--lake-cmd", nargs="+", help="Override lake command, e.g. --lake-cmd lake serve")
    return p.parse_args()


def main() -> int:
    ns = parse_args()
    srv = LeanCodexLspV2(Path(ns.workspace), lake_cmd=ns.lake_cmd, verbose=ns.verbose)
    try:
        return srv.serve_stdio()
    finally:
        srv.stop()


if __name__ == "__main__":
    raise SystemExit(main())
