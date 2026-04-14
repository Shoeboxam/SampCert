/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import SampCert.Extractor.Translate
import SampCert.Extractor.IRToDafny

namespace Lean.ToDafny

syntax (name := export_dafny) "export_dafny" : attr

open Meta

def saveMethod (m : Method) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"{m.print}")

def stringToName (s : String) : Name :=
  s.splitOn "." |>.foldl Name.str Name.anonymous

def prefixName (prefixNm : Name) (suffix : Name) : Name :=
  match suffix with
  | .anonymous => prefixNm
  | .str p s => .str (prefixName prefixNm p) s
  | .num p i => .num (prefixName prefixNm p) i

def resolveCalleeNames (s : String) : List Name :=
  let base := stringToName s
  [base, prefixName (Name.str Name.anonymous "SLang") base]

mutual

partial def ensureMethodDependencies (m : Method) : MetaM Unit := do
  for callee in m.monadicCalls.eraseDups do
    let st : State := extension.getState (← getEnv)
    if st.glob.contains callee then
      pure ()
    else
      for calleeName in resolveCalleeNames callee do
        try
          let info ← getConstInfo calleeName
          if ← IsWFMonadic info.type then
            toDafnyMethod calleeName
        catch _ =>
          pure ()

partial def toDafnyMethod(declName: Name) : MetaM Unit := do
  let method ← CodeGen (← toDafnySLangDefIn declName)
  saveMethod method
  ensureMethodDependencies method

end

initialize
  registerBuiltinAttribute {
    ref   := by exact decl_name%
    name  := `export_dafny
    descr := "instruct Lean to convert the given definition to a Dafny method"
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName _ _attrKind =>
      let go : MetaM Unit :=
        do
          toDafnyMethod declName
      discard <| go.run {} {}
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
