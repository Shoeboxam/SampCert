/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import Lean
import SampCert.Extractor.IR
import SampCert.Extractor.Extension
import SampCert.SLang

namespace Lean.ToDafny

partial def IsWFMonadic (e: Expr) : MetaM Bool :=
  match e with
  | .app (.const ``SLang ..) _ => return true
  | .app .. => return true -- Need to work out details of this one, related to translation of dependent types
  | .forallE _ _ range _ => IsWFMonadic range
  | _ => return false -- throwError "IsWFMonadic {e}"

def chopLambda (e : Expr) : Expr :=
  match e with
  | .lam _ _ body _ => body
  | _ => e

mutual

partial def isFinType (e : Expr) : MetaM Bool := do
  match (← Meta.whnf e) with
  | .app (.const ``Fin ..) _ => return true
  | _ => return false

partial def toDafnyTyp (env : List String) (e : Expr) : MetaM Typ := do
  match e with
  | .bvar .. => throwError "toDafnyTyp: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyTyp: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyTyp: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyTyp: not supported -- sort {e}"
  | .const ``Nat .. => return .nat
  | .const ``PNat .. => return .pos
  | .const ``Bool .. => return .bool
  | .const ``Int .. => return .int
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      match name with
      | ``Fin => return .nat
      | ``List => return .seq (← toDafnyTyp env args[0]!)
      | ``Prod => return .prod (← toDafnyTyp env args[0]!) (← toDafnyTyp env args[1]!)
      | ``PProd => return .prod (← toDafnyTyp env args[0]!) (← toDafnyTyp env args[1]!)
      | ``SLang => return (← toDafnyTyp env args[0]!)
      | _ =>
          let e' ← Meta.whnf e
          if e' == e then
            return .dependent (← toDafnyExpr "dummycalledfromtoDafnyTyp" env e)
          else
            toDafnyTyp env e'
      else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  | .lam .. => throwError "toDafnyTyp: not supported -- lambda abstraction {e}"
  | .forallE _ domain range _ =>
      if ← isFinType domain
      then
        return .seq (← toDafnyTyp env range)
      else
        throwError "toDafnyTyp: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyTyp: not supported -- let expressions {e}"
  | .lit .. => throwError "toDafnyTyp: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyTyp: not supported -- metadata {e}"
  | .proj .. => throwError "toDafnyTyp: not supported -- projection {e}"
  | .const .. =>
      let e' ← Meta.whnf e
      if e' == e then
        throwError "toDafnyTyp: not supported -- constant {e}"
      else
        toDafnyTyp env e'

partial def defaultExprForTyp : Typ → MetaM Expression
  | .bool => return .fa
  | .int => return .num 0
  | .nat => return .num 0
  | .pos => return .num 1
  | .prod left right => return .pair (← defaultExprForTyp left) (← defaultExprForTyp right)
  | .dependent _ => return .num 0
  | .seq _ => throwError "defaultExprForTyp: sequences not supported"

partial def runtimeArgs (env : List String) (type : Expr) (args : List Expr) : MetaM (List Expr) := do
  match (← Meta.whnf type), args with
  | .forallE _ domain body _, arg :: args =>
      let body := body.instantiate1 arg
      let keep ←
        match (← Meta.whnf domain) with
        | .sort _ => pure false
        | _ =>
            try
              let typ ← toDafnyTyp env domain
              pure <| match typ with
                | Typ.dependent _ => false
                | _ => true
            catch _ =>
              pure false
      let rest ← runtimeArgs env body args
      return if keep then arg :: rest else rest
  | _, _ => return []

partial def localSeqApp? (dname : String) (env : List String) (fn : Expr) (args : Array Expr) :
    MetaM (Option Expression) := do
  if args.size != 1 then
    return none
  match fn with
  | .bvar i =>
      return some <|
        .index (.name (env[i]!)) (← toDafnyExpr dname env args[0]!)
  | _ => pure ()
  let fnType ← Meta.whnf (← Meta.inferType fn)
  match fnType with
  | .forallE _ domain _ _ =>
      if ← isFinType domain then
        return some <|
          .index (← toDafnyExpr dname env fn) (← toDafnyExpr dname env args[0]!)
      else
        return none
  | _ => return none

partial def toDafnyExpr (dname : String) (env : List String) (e : Expr) : MetaM Expression := do
  match e with
  | .bvar i => return .name (env[i]!)
  | .fvar .. => throwError "toDafnyExpr: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExpr: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExpr: not supported -- sort {e}"
  | .const ``true .. => return .tr
  | .const ``false .. => return .fa
  | .const ``PUnit.unit .. => throwError "WF: all conditions are if then else, including the ones to throw errors"
  | .const .. => throwError "toDafnyExpr: not supported -- constant {e}"
  | .app .. => (e.withApp fun fn args => do
      if let .const name .. := fn then
      let info ← getConstInfo name
      match name with
      | ``pure => return .pure (← toDafnyExpr dname env args[3]!)
      | ``bind => return .bind (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``ite => return .ite (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[3]!) (← toDafnyExpr dname env args[4]!)
      | ``dite => return .ite (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname ("dummy" :: env) (chopLambda args[3]!)) (← toDafnyExpr dname ("dummy" :: env) (chopLambda args[4]!))
      | ``throwThe => return .throw (← toDafnyExpr dname env args[4]!)
      | ``SLang.probWhile => return .prob_while (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``SLang.probUntil => return .prob_until (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``OfNat.ofNat => toDafnyExpr dname env args[1]!
      | ``HAdd.hAdd => return .binop .addition (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HSub.hSub => return .binop .substraction (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HMul.hMul => return .binop .multiplication (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HDiv.hDiv => return .binop .division (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HPow.hPow => return .binop .pow (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``HMod.hMod => return .binop .mod (← toDafnyExpr dname env args[4]!) (← toDafnyExpr dname env args[5]!)
      | ``Eq => return .binop .equality (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``Ne => return .binop .inequality (← toDafnyExpr dname env args[1]!) (← toDafnyExpr dname env args[2]!)
      | ``And => return .binop .conjunction (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Or => return .binop .disjunction (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Not => return .unop .negation (← toDafnyExpr dname env args[0]!)
      | ``LT.lt => return .binop .least (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``LE.le => return .binop .leastequal (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``Nat.lt => return .binop .least (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Nat.le => return .binop .leastequal (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``Nat.succ =>
          return .binop .addition (← toDafnyExpr dname env args[0]!) (.num 1)
      | ``GT.gt => return .binop .greater (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``GE.ge => return .binop .greaterequal (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``Nat.log => return .binop .log (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | ``decide => toDafnyExpr dname env args[0]!
      | ``_root_.Rat.den => return .unop .denominator (← toDafnyExpr dname env args[0]!)
      | ``_root_.Rat.num => return .unop .numerator (← toDafnyExpr dname env args[0]!)
      | ``Nat.cast => toDafnyExpr dname env args[2]!
      | ``Int.cast => toDafnyExpr dname env args[2]!
      | ``default =>
          defaultExprForTyp (← toDafnyTyp env args[0]!)
      | ``Fin.mk => toDafnyExpr dname env args[1]!
      | ``Fin.val => toDafnyExpr dname env args[1]!
      | ``Prod.fst => return .proj (← toDafnyExpr dname env args[2]!) 1
      | ``Prod.snd => return .proj (← toDafnyExpr dname env args[2]!) 2
      | ``Prod.mk => return .pair (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``PProd.fst => return .proj (← toDafnyExpr dname env args[2]!) 1
      | ``PProd.snd => return .proj (← toDafnyExpr dname env args[2]!) 2
      | ``PProd.mk => return .pair (← toDafnyExpr dname env args[2]!) (← toDafnyExpr dname env args[3]!)
      | ``Neg.neg => return .unop .minus (← toDafnyExpr dname env args[2]!)
      | ``abs => return .unop .abs (← toDafnyExpr dname env args[2]!)
      | ``Int.natAbs => return .unop .abs (← toDafnyExpr dname env args[0]!)
      | ``OfScientific.ofScientific => toDafnyExpr dname env args[4]!
      | ``PNat.val => toDafnyExpr dname env args[0]!
      | ``Subtype.mk => toDafnyExpr dname env args[2]!
      | ``Int.sub => return .binop .substraction (← toDafnyExpr dname env args[0]!) (← toDafnyExpr dname env args[1]!)
      | _ =>
        if ← IsWFMonadic info.type
        then
          let st : State := extension.getState (← getEnv)
          if let some defn := st.glob.find? name.toString
          then
            -- Translate only arguments that correspond to non-dependent types
            let args1 := defn.inParamType.zip args.toList
            let args2 := args1.filter (λ (x,_) => match x with | .dependent _ => false | _ => true)
            let args3 := args2.map (λ (_,y) => y)
            let args' ← args3.mapM (toDafnyExpr dname env)
            return .monadic name.toString args'
          else
            let runtime ← runtimeArgs env info.type args.toList
            let args' ← runtime.mapM (toDafnyExpr dname env)
            return .monadic name.toString args'
        else throwError "toDafnyExpr: not supported -- application of {fn} to {args}, info.type {info.type}"
      else if let some e ← localSeqApp? dname env fn args then
        return e
      else if let .bvar _ := fn
           then return .monadic dname [(← toDafnyExpr dname env args[0]!)]
           else throwError "toDafnyExpr: OOL {fn} {args}"
    )
  | .lam binderName _ body _  => return (.lam binderName.toString (← toDafnyExpr dname (binderName.toString :: env) body))
  | .forallE .. => throwError "toDafnyExpr: not supported -- pi {e}"
  | .letE lhs _ rhs body _ => return (.letb lhs.toString (← toDafnyExpr dname env rhs) (← toDafnyExpr dname (lhs.toString :: env) body))
  | .lit (.natVal n) => return .num n
  | .lit (.strVal s) => return .str s
  | .mdata .. => throwError "toDafnyExpr: not supported -- meta {e}"
  | .proj _ idx body => return .proj (← toDafnyExpr dname env body) (idx + 1)

end

def toDafnyTypTop (env : List String) (e: Expr) : MetaM ((List Typ) × Typ) := do
  match e with
  | .forallE _ (.sort _) _ _ => throwError "toDafnyTypTop: Polymorphism not supported yet"
  | (.app (.const ``SLang ..) arg) => return ([],← toDafnyTyp [] arg)
  | .forallE binder domain range _ =>
    let nenv := binder.toString :: env
    let r ← toDafnyTypTop nenv range
    return ((← toDafnyTyp env domain) :: r.1 , r.2)
  | _ => throwError "toDafnyTypTop: error"

partial def toDafnyExprTop (dname : String) (num_args : Nat) (names : List String) (e : Expr) : MetaM (List String × Expression) := do
  match e with
  | .bvar .. => throwError "toDafnyExprTop: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyExprTop: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyExprTop: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyExprTop: not supported -- sort {e}"
  | .const .. => throwError "toDafnyExprTop: not supported -- constant {e}"
  | .app .. =>
    e.withApp fun fn args =>
      if let .const ``WellFounded.fix .. := fn
      then toDafnyExprTop dname num_args names (args[4]!)
      else if let .const ``WellFounded.Nat.fix .. := fn
      then toDafnyExprTop dname num_args names (args[args.size - 1]!)
      else throwError "toDafnyExprTop: not supported -- application {e}"
  | .lam binderName _ body _ =>
    let sig_names := names ++ [binderName.toString]
    if num_args = List.length names + 1
    then
      match body with
      | (.lam _ _ body _) => return (sig_names, ← toDafnyExpr dname ("dummy" :: sig_names.reverse) (chopLambda body))
      | _ => return (sig_names, ← toDafnyExpr dname sig_names.reverse body)
    else toDafnyExprTop dname num_args sig_names body
  | .forallE .. => throwError "toDafnyExprTop: not supported -- pi {e}"
  | .letE .. => throwError "toDafnyExprTop: not supported -- let expression {e}"
  | .lit .. => throwError "toDafnyExprTop: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyExprTop: not supported -- meta {e}"
  | .proj .. => throwError "toDafnyExprTop: not supported -- projection {e}"

def printParamTypes (params : List Typ) : String :=
  match params with
  | [] => ""
  | param :: params => s!"{param.print}, {printParamTypes params}"

def toDafnySLangDefIn (declName: Name) : MetaM MDef := do
  let info ← getConstInfo declName
  match info with
    | ConstantInfo.defnInfo _ =>
      if ← IsWFMonadic info.type then
        let (inParamTyp, outParamTyp) ← toDafnyTypTop [] info.type
        let (inParam, body) ←  toDafnyExprTop declName.toString (List.length inParamTyp) [] info.value!
        let defn := MDef.mk (declName.toString) inParamTyp outParamTyp inParam body
        return defn
      else throwError "This extractor works for SLang monadic computations only (1)"
    | _ => throwError "This extractor works for SLang monadic computations only (2)"

end Lean.ToDafny
