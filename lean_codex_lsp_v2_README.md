# lean_codex_lsp_v2.py

Persistent Codex-friendly wrapper around `lake serve` for Lean projects.

## Start the server

```bash
python3 lean_codex_lsp_v2.py --workspace /path/to/project
```

Keep it running and send one JSON command per line on stdin.

## Recommended repair loop

### 1) Open/check the file

```json
{"cmd":"check_decl","path":"SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean","dependencyBuildMode":"once"}
```

This returns:

- `firstDiagnostic`
- `diagnosticHash`
- `decl` with `hash`, `headerText`, line range, and `text` unless unchanged
- `goal` with `hash`, `plainGoal`, and `plainTermGoal` unless unchanged
- `compactPromptSeed`

### 2) Re-check without resending unchanged declaration/goal text

```json
{"cmd":"check_decl","path":"SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean","knownDeclHash":"<last decl hash>","knownGoalHash":"<last goal hash>"}
```

If the hashes match, the response sets `sameAsKnown: true` and omits the bulky `text` / goal payloads.

### 3) Apply a tiny localized edit

```json
{"cmd":"apply_edit","path":"SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean","startLine":142,"startColumn":7,"endLine":142,"endColumn":11,"text":"simp [foo]","waitForDiagnostics":true}
```

Or multiple edits at once:

```json
{
  "cmd":"apply_edits",
  "path":"SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean",
  "edits":[
    {"startLine":142,"startColumn":7,"endLine":142,"endColumn":11,"text":"simp [foo]"},
    {"startLine":145,"startColumn":3,"endLine":145,"endColumn":3,"text":"  have h := ...\n"}
  ]
}
```

## Other commands

- `open`
- `update` (full file replacement)
- `wait`
- `diagnostics`
- `check` (v1-style first-error packet with a file window)
- `plain_goal`
- `plain_term_goal`
- `hover`
- `definition`
- `close`
- `shutdown`

## Suggested Codex instructions

Use this tool as a persistent subprocess.

- Start with `check_decl`.
- Only fix the **first** diagnostic.
- Reuse prior declaration/goal context when `sameAsKnown` is true.
- Prefer `apply_edit` / `apply_edits` over full-file `update`.
- Only fall back to `check` when the error is outside a declaration or the declaration heuristic looks wrong.

## Notes

- `dependencyBuildMode` is passed only on `didOpen`. Useful values are `"once"` and `"never"`.
- Columns in the wrapper API are **1-based user columns**.
- The wrapper is meant to stay alive across many commands. If stdin closes, it shuts down the LSP.
