/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Extractor.IR

namespace Lean.ToDafny

def concatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ concatMap f xs

inductive Statement where
  | vardecl (lhs : String) (rhs : Expression)
  | assignment (lhs : String) (rhs : Expression)
  | loop (cond : Expression) (body: List Statement)
  | conditional (cond : Expression) (ifso ifnot : List Statement)
  | expect (cond : Expression) (msg : Expression)
  | ret (e : Expression)

structure Method where
  name : String
  inParamType : List Typ
  outParamType : Typ
  inParam : List String
  body : List Statement

def indent (depth : Nat) : String :=
  match depth with
  | 0 => ""
  | Nat.succ n => "  " ++ indent n

mutual

def Statement.print (s : Statement) (depth: Nat) : String :=
  match s with
  | .vardecl lhs rhs =>
    indent depth ++ s!"var {lhs} := {rhs};\n"
  | .assignment lhs rhs =>
    indent depth ++ s!"{lhs} := {rhs};\n"
  | .loop cond body =>
    indent depth ++ s!"while {cond}\n" ++
    (indent (depth + 1)) ++ s!"decreases *\n" ++
    indent depth ++ s!"\{\n" ++
    s!"{sjoin body (depth + 1)}" ++
    indent depth ++ s!"}\n"
  | .conditional cond ifso ifnot =>
    (indent depth) ++ s!"if {cond} \{\n{sjoin ifso (depth + 1)}" ++
    (indent depth) ++ s!"} else \{\n{sjoin ifnot (depth + 1)}" ++
    (indent depth) ++ "}\n"
  | .expect e msg =>
    indent depth ++ s!"expect !({e}), {msg};\n"
  | .ret e =>
    indent depth ++ s!"o := {e};\n"

def sjoin (s : List Statement) (depth: Nat) : String :=
  match s with
  | [] => ""
  | [a] => a.print depth
  | a::as => a.print depth ++ sjoin as depth

end

def Method.print (m : Method) : String :=
  let method_args := m.inParam.zip m.inParamType
  let method_args := method_args.filter (λ (_,y) => match y with | .dependent _ => false | _ => true)
  let method_args := method_args.unzip
  let method_requires := m.inParamType.filter (λ x => match x with | .dependent _ => true | _ => false)
  (indent 2) ++ s!"method \{:verify false} {m.name} ({printArgs method_args.1 method_args.2})\n" ++
  (indent 3) ++ s!"returns (o: {m.outParamType.print})\n" ++
  printRequires method_requires (indent 3) ++
  (indent 3) ++ s!"modifies this\n" ++
  (indent 3) ++ s!"decreases *\n" ++
  (indent 2) ++ s!"\{\n{sjoin m.body 3}" ++
  (indent 2) ++"}\n\n"

mutual

partial def Expression.monadicCalls (e : Expression) : List String :=
  match e with
  | .tr | .fa | .num _ | .str _ | .name _ => []
  | .letb _ rhs body => rhs.monadicCalls ++ body.monadicCalls
  | .ite cond left right => cond.monadicCalls ++ left.monadicCalls ++ right.monadicCalls
  | .bind rhs body => rhs.monadicCalls ++ body.monadicCalls
  | .lam _ body => body.monadicCalls
  | .pure e => e.monadicCalls
  | .throw e => e.monadicCalls
  | .prob_until body cond => body.monadicCalls ++ cond.monadicCalls
  | .prob_while cond body init => cond.monadicCalls ++ body.monadicCalls ++ init.monadicCalls
  | .unop _ rhs => rhs.monadicCalls
  | .binop _ lhs rhs => lhs.monadicCalls ++ rhs.monadicCalls
  | .index base idx => base.monadicCalls ++ idx.monadicCalls
  | .proj name _ => name.monadicCalls
  | .pair left right => left.monadicCalls ++ right.monadicCalls
  | .monadic name args => name :: concatMap Expression.monadicCalls args

partial def Statement.monadicCalls (s : Statement) : List String :=
  match s with
  | .vardecl _ rhs => rhs.monadicCalls
  | .assignment _ rhs => rhs.monadicCalls
  | .loop cond body => cond.monadicCalls ++ concatMap Statement.monadicCalls body
  | .conditional cond ifso ifnot =>
      cond.monadicCalls ++ concatMap Statement.monadicCalls ifso ++ concatMap Statement.monadicCalls ifnot
  | .expect cond msg => cond.monadicCalls ++ msg.monadicCalls
  | .ret e => e.monadicCalls

end

def Method.monadicCalls (m : Method) : List String :=
  concatMap Statement.monadicCalls m.body

end Lean.ToDafny
