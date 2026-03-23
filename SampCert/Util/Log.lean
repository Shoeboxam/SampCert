/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan, Markus de Medeiros
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Lean.Elab.Tactic


/-!
# Logarithm on ENNReal

In this file we extend the logarithm to ``ENNReal``.

The main definitions in this file are
- ``ofEReal : EReal -> ENNReal`` : Casting ``EReal`` to ``ENNReal`` by truncation
- ``eexp : EReal -> ENNReal`` : Exponential extended to the ``EReal``s
- ``elog : ENNReal -> EReal`` : Logarithm extended to the ``ENNReal``s
-/

noncomputable section

open scoped Classical
open ENNReal EReal Real



section EReal_conv_cases
/-!
### Case analysis lemmas

Most conversion proofs follow by splitting into cases, and then simplifying. However
explicitly performing case analysis can be unwieldy and lead to lots of duplicate work,
depending on which simplification rules are used. These tactics allow us to fine-tune the
case splits at the start of a conversion proof in order to reduce the number of cases we must
prove by hand.


Tactic overview:

Real numbers:
- ``case_Real_zero``: A real number is zero or nonzero
- ``case_Real_sign``: A real number is negative, zero, or positive
- ``case_nonneg_zero``: Given ``0 ≤ r``, `r` is zero or positive
- ``case_Real_nonnegative`` : A real number is negative or nonnegative

Extended nonnegative real numbers:
- ``case_ENNReal_isReal``: An ``ENNReal`` is ⊤, or the cast of a real number
- ``case_ENNReal_isReal_zero``: An ``ENNReal`` is ⊤, zero, or the cast of a real number

Extended reals:
- ``case_EReal_isReal``: An ``EReal`` is ⊤, ⊥, or the cast of a real number
- ``case_EReal_isENNReal``: An `EReal`` is negative, or the cast of an ``ENNReal``
-/


/--
A real number is either zero or nonzero
-/
lemma Real_cases_zero (r : ℝ) : r = 0 ∨ r ≠ 0 := by
  exact eq_or_ne r (OfNat.ofNat 0)

syntax "case_Real_zero" term : tactic
macro_rules
| `(tactic| case_Real_zero $r:term ) =>
    `(tactic| rcases (eq_or_ne $r (OfNat.ofNat 0)) with _ | _ <;> try simp_all)



/--
A real number is either negative, zero, or postive
-/
lemma Real_cases_sign (r : ℝ) : r < 0 ∨ r = 0 ∨ 0 < r := by exact lt_trichotomy r (OfNat.ofNat 0)

syntax "case_Real_sign" term : tactic
macro_rules
| `(tactic| case_Real_sign $r:term ) =>
    `(tactic| rcases (Real_cases_sign $r) with _ | _ | _ <;> try simp_all)

/--
A nonnegative number is either zero or positive
-/
syntax "case_nonneg_zero" term : tactic
macro_rules
| `(tactic| case_nonneg_zero $H:term ) =>
    `(tactic| rcases (eq_or_lt_of_le $H) with _ | _ <;> try simp_all)



/--
A real number is either negative, or nonzero
-/
lemma Real_cases_nonnegative (r : ℝ) : r < 0 ∨ 0 ≤ r := by exact lt_or_ge r (OfNat.ofNat 0)

syntax "case_Real_nonnegative " term : tactic
macro_rules
| `(tactic| case_Real_nonnegative $r:term ) =>
    `(tactic| rcases (Real_cases_nonnegative $r) with _  | _  <;> try simp_all)


lemma ENNReal_isReal_cases (x : ENNReal) : x = ⊤ ∨ (∃ v : ℝ, x = ENNReal.ofReal v ∧ 0 ≤ v) := by
  cases x
  · left
    simp
  · right
    rename_i v
    rcases v with ⟨ r, Hr ⟩
    exists r
    apply And.intro
    · simp [ENNReal.ofReal, Real.toNNReal]
      congr
      rw [max_eq_left Hr]
    · assumption

syntax "case_ENNReal_isReal" term : tactic
macro_rules
| `(tactic| case_ENNReal_isReal $w:term ) =>
    `(tactic| rcases (ENNReal_isReal_cases $w) with  _ | ⟨ _, _, _⟩ <;> try simp_all)

/--
An ENNReal is either top, zero, or the lift if a positive real
-/
lemma ENNReal_isReal_zero_cases (x : ENNReal) : x = ⊤ ∨ x = 0 ∨ (∃ v : ℝ, x = ENNReal.ofReal v ∧ 0 < v) := by
  case_ENNReal_isReal x
  rename_i r Hr1 Hr2
  case_nonneg_zero Hr2
  right
  exists r

syntax "case_ENNReal_isReal_zero" term : tactic
macro_rules
| `(tactic| case_ENNReal_isReal_zero $w:term ) =>
    `(tactic| rcases (ENNReal_isReal_zero_cases $w) with  _ | _ | ⟨ _, _, _⟩ <;> try simp_all)

/--
An EReal is either ⊤, ⊥, or the lift of some real number.
-/
lemma EReal_isReal_cases (w : EReal) : w = ⊥ ∨ w = ⊤ ∨ (∃ v : ℝ, w = Real.toEReal v) := by
  cases w
  · left
    rfl
  simp_all
  tauto

syntax "case_EReal_isReal" term : tactic
macro_rules
| `(tactic| case_EReal_isReal $w:term ) =>
    `(tactic| rcases (EReal_isReal_cases $w) with _ | _ | ⟨ _, _ ⟩ <;> try simp_all)

/--
An EReal is either negative, or the lift of an ENNReal
-/
lemma EReal_isENNReal_cases (w : EReal) : (w < 0) ∨ (∃ v : ENNReal, w = ENNReal.toEReal v) := by
  case_EReal_isReal w
  · right
    exact ⟨⊤, by simp⟩
  · rename_i w' Hw'
    case_Real_nonnegative w'
    rename_i Hw''
    right
    exists (ENNReal.ofReal w')
    simp only [coe_ennreal_ofReal, EReal.coe_eq_coe_iff]
    rw [max_eq_left Hw'']

syntax "case_EReal_isENNReal" term : tactic
macro_rules
| `(tactic| case_EReal_isENNReal $w:term ) =>
    `(tactic| rcases (EReal_isENNReal_cases $w) with _ | ⟨ _, _ ⟩ <;> try simp_all)


end EReal_conv_cases



namespace ENNReal

section ofEReal
/-!
### Coercion from EReals to ENNreals
-/


/--
Truncate an `EReal` to an `ENNReal`
-/
noncomputable def ofEReal (e : EReal) : ENNReal :=
  e.toENNReal

@[simp]
lemma ofEReal_bot : ofEReal ⊥ = 0 := by simp [ofEReal]

@[simp]
lemma ofEReal_top : ofEReal ⊤ = ⊤ := by simp [ofEReal]

@[simp]
lemma ofEReal_zero : ofEReal 0 = 0 := by simp [ofEReal]

@[simp]
lemma ofEReal_real (r : ℝ) : ofEReal r = ENNReal.ofReal r := by
  exact EReal.real_coe_toENNReal r


lemma ofEReal_eq_zero_iff (w : EReal) : w ≤ 0 <-> ofEReal w = 0 := by
  simpa [ofEReal] using (EReal.toENNReal_eq_zero_iff (x := w)).symm

/--
``ofEReal`` is injective for for positive EReals
-/
lemma ofEReal_nonneg_inj {w z : EReal} (Hw : 0 <= w) (Hz : 0 <= z) :
  w = z <-> (ofEReal w = ofEReal z) := by
  simpa [ofEReal] using (EReal.toENNReal_eq_toENNReal (x := w) (y := z) Hw Hz).symm

@[simp]
lemma toEReal_ofENNReal_nonneg {w : EReal} (H : 0 ≤ w) : ENNReal.toEReal (ofEReal w) = w := by
  simpa [ofEReal] using EReal.coe_toENNReal (x := w) H

@[simp]
lemma ofEReal_toENNReal {x : ENNReal} : ofEReal (ENNReal.toEReal x) = x := by
  simp [ofEReal, EReal.toENNReal_coe (x := x)]

/-
`ENNReal.ofReal` is the composition of cases from Real to EReal to ENNReal
-/
@[simp]
lemma ofEReal_ofReal_toENNReal : ENNReal.ofEReal (Real.toEReal r) = ENNReal.ofReal r := by
  exact EReal.real_coe_toENNReal r


lemma ofEReal_le_mono {w z : EReal} (H : w ≤ z) : ofEReal w ≤ ofEReal z := by
  simpa [ofEReal] using EReal.toENNReal_le_toENNReal H

lemma ofEReal_le_mono_conv_nonneg {w z : EReal} (Hw : 0 ≤ w) (Hz : 0 ≤ z) (Hle : ofEReal w ≤ ofEReal z) : w ≤ z := by
  have Hle' : ((ofEReal w : ENNReal) : EReal) ≤ ofEReal z := by
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr Hle
  simpa [ofEReal, EReal.coe_toENNReal Hw, EReal.coe_toENNReal Hz] using Hle'


 @[simp]
 lemma ofEReal_plus_nonneg (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w + z) = ofEReal w + ofEReal z := by
   simpa [ofEReal] using EReal.toENNReal_add (x := w) (y := z) Hw Hz



@[simp]
lemma ofEReal_mul_nonneg (Hw : 0 ≤ w) (_Hz : 0 ≤ z) : ofEReal (w * z) = ofEReal w * ofEReal z := by
  simpa [ofEReal] using EReal.toENNReal_mul (x := w) (y := z) Hw



lemma ofEReal_nonneg_scal_l {r : ℝ} {w : EReal} (H1 : 0 < r) (H2 : 0 ≤ r * w) : 0 ≤ w := by
  case_EReal_isReal w
  · exfalso
    simp [EReal.mul_bot_of_pos (EReal.coe_pos.mpr H1)] at H2
  · exact le_top
  · rename_i w' Hw'
    rw [← EReal.coe_mul] at H2
    exact nonneg_of_mul_nonneg_right (EReal.coe_nonneg.mp H2) H1


lemma galois_connection_ofReal : GaloisConnection ENNReal.ofEReal ENNReal.toEReal := by
  intro a b
  apply Iff.intro
  · intro hab
    by_cases ha : 0 ≤ a
    · have hab' : ((ofEReal a : ENNReal) : EReal) ≤ (b : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr hab
      simpa [ofEReal, EReal.coe_toENNReal ha] using hab'
    · exact le_trans (le_of_not_ge ha) (EReal.coe_ennreal_nonneg b)
  · intro hab
    simpa [ofEReal] using EReal.toENNReal_le_toENNReal hab

end ofEReal


/--
``ENNReal.ofReal`` is injective for for positive EReals
-/
lemma ofReal_injective_nonneg {r s : ℝ} (HR : 0 ≤ r) (HS : 0 ≤ s) (H : ENNReal.ofReal r = ENNReal.ofReal s) : r = s := by
  apply (Real.toNNReal_eq_toNNReal_iff HR HS).mp
  simp [ENNReal.ofReal] at H
  assumption




section elog_eexp

/--
The extended logarithm
-/
def elog (x : ENNReal) : EReal :=
  ENNReal.log x

/--
The extended exponential

Mathlib's has an extended ``rpow`` function of type ``ℝ≥0∞ → ℝ → ℝ≥0∞``, however we
want the exponent to be of type ``EReal``.
-/
def eexp (y : EReal) : ENNReal :=
  EReal.exp y

-- MARKUSDE: cleanup?
@[simp]
lemma elog_of_pos_real {r : ℝ} (H : 0 < r) : elog (ENNReal.ofReal r) = Real.log r := by
  simpa [elog] using ENNReal.log_ofReal_of_pos H

@[simp]
lemma elog_zero : elog 0 = ⊥ := by simp [elog]

@[simp]
lemma elog_top : elog ⊤ = ⊤ := by simp [elog]

@[simp]
lemma eexp_bot : eexp ⊥ = 0 := by simp [eexp]

@[simp]
lemma eexp_top : eexp ⊤ = ⊤ := by simp [eexp]

@[simp]
lemma eexp_zero : eexp 0 = 1 := by simp [eexp]

@[simp]
lemma eexp_ofReal {r : ℝ} : eexp r = ENNReal.ofReal (Real.exp r) := by
  simp [eexp]

@[simp]
lemma elog_eexp {x : ENNReal} : eexp (elog x) = x := by
  simp [elog, eexp, ENNReal.exp_log x]


@[simp]
lemma eexp_elog {w : EReal} : (elog (eexp w)) = w := by
  simp [elog, eexp, EReal.log_exp w]

lemma elog_ENNReal_ofReal_of_pos {x : ℝ} (H : 0 < x) : (ENNReal.ofReal x).elog = x.log.toEReal := by
  simpa [elog] using ENNReal.log_ofReal_of_pos H

@[simp]
lemma elog_mul {x y : ENNReal} : elog x + elog y = elog (x * y) := by
  simpa [elog] using (ENNReal.log_mul_add (x := x) (y := y)).symm


@[simp]
lemma eexp_add {w z : EReal} : eexp w * eexp z = eexp (w + z) := by
  simpa [eexp] using (EReal.exp_add w z).symm


lemma eexp_injective {w z : EReal} : eexp w = eexp z -> w = z := by
  intro h
  exact EReal.exp_strictMono.injective h


lemma elog_injective {x y : ENNReal} : elog x = elog y -> x = y := by
  intro h
  exact ENNReal.log_injective h


lemma eexp_zero_iff {w : EReal} : eexp w = 0 <-> w = ⊥ := by
  simp [eexp]


lemma elog_bot_iff {x : ENNReal} : elog x = ⊥ <-> x = 0 := by
  simp [elog]



lemma eexp_mono_lt {w z : EReal} : (w < z) <-> eexp w < eexp z := by
  simp [eexp]



lemma eexp_mono_le {w z : EReal} : (w <= z) <-> eexp w <= eexp z := by
  simp [eexp]


lemma eexp_mul_nonneg {r w : EReal} (HR : 0 ≤ r) (HR2 : r ≠ ⊤) : eexp (r * w) = (eexp w) ^ (EReal.toReal r) := by
  have HRbot : r ≠ ⊥ := by
    exact ne_bot_of_gt <| lt_of_lt_of_le bot_lt_zero HR
  rw [← EReal.coe_toReal HR2 HRbot]
  simpa [eexp, mul_comm] using EReal.exp_mul w r.toReal


lemma elog_mono_lt {x y : ENNReal} : (x < y) <-> elog x < elog y := by
  simp [elog]


lemma elog_mono_le {x y : ENNReal} : (x <= y) <-> elog x <= elog y := by
  simp [elog]

lemma galois_connection_eexp : GaloisConnection eexp elog := by
  rw [GaloisConnection]
  intro a b
  apply Iff.intro
  · intro H
    rw [<- @eexp_elog a]
    exact elog_mono_le.mp H
  · intro H
    rw [<- @elog_eexp b]
    exact eexp_mono_le.mp H


end elog_eexp





section misc


lemma mul_mul_inv_le_mul_cancel {x y : ENNReal} : (x * y⁻¹) * y ≤ x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

lemma mul_mul_inv_eq_mul_cancel {x y : ENNReal} (H : y = 0 -> x = 0) (H2 : ¬(x ≠ 0 ∧ y = ⊤)) : (x * y⁻¹) * y = x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

lemma ereal_smul_le_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w ≤ s * z) : w ≤ z := by
  have hs_ne_bot : s ≠ ⊥ := ne_bot_of_gt Hr1
  have hs_ne_top : s ≠ ⊤ := ne_of_lt Hr2
  have hs_ne_zero : s ≠ 0 := ne_of_gt Hr1
  have Hdiv : (s * w) / s ≤ (s * z) / s :=
    EReal.div_le_div_right_of_nonneg (le_of_lt Hr1) H
  rw [← EReal.mul_div s w s, EReal.mul_div_cancel hs_ne_bot hs_ne_top hs_ne_zero] at Hdiv
  rw [← EReal.mul_div s z s, EReal.mul_div_cancel hs_ne_bot hs_ne_top hs_ne_zero] at Hdiv
  exact Hdiv

lemma ereal_smul_eq_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w = s * z) : w = z := by
  apply LE.le.antisymm
  · apply ereal_smul_le_left s Hr1 Hr2 (le_of_eq H)
  · apply ereal_smul_le_left s Hr1 Hr2 (le_of_eq (id (Eq.symm H)))

lemma ereal_smul_lt_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w < s * z) : w < z := by
  cases LE.le.lt_or_eq (ereal_smul_le_left s Hr1 Hr2 (LT.lt.le H))
  · assumption
  · simp_all

lemma ereal_smul_distr_le_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) :
    s * (w + z) = s * w + s * z := by
  exact EReal.left_distrib_of_nonneg_of_ne_top (le_of_lt Hr1) (ne_of_lt Hr2) w z


lemma ereal_le_smul_left {w z : EReal} (s : EReal) (Hr1 : 0 < s) (_Hr2 : s < ⊤) (H : w ≤ z) : s * w ≤ s * z := by
  simpa using mul_le_mul_of_nonneg_left H (le_of_lt Hr1)


lemma ereal_smul_inv_cancel_1 {s : EReal} (HS0 : 0 < s) (HS1 : s < ⊤) (x : EReal) :
 s * (ENNReal.toEReal (ENNReal.ofEReal s)⁻¹) * x = x := by
   case_EReal_isENNReal s
   · rename_i H
     rw [(ofEReal_eq_zero_iff s).mp ?G1]
     case G1 => exact le_of_lt H
     exfalso
     exact (not_le_of_gt H) (le_of_lt HS0)
   · rename_i r _
     rw [← coe_ennreal_mul]
     rw [← DivInvMonoid.div_eq_mul_inv]
     rw [ENNReal.div_self ?G1 ?G2]
     case G1 => exact Ne.symm (ne_of_lt HS0)
     simp
     intro
     simp_all

lemma ereal_smul_inv_cancel_2 {s : EReal} (HS0 : 0 < s) (HS1 : s < ⊤) (x : EReal) :
 (ENNReal.toEReal (ENNReal.ofEReal s)⁻¹) * s * x = x := by
   case_EReal_isENNReal s
   · rename_i H
     rw [(ofEReal_eq_zero_iff s).mp ?G1]
     case G1 => exact le_of_lt H
     exfalso
     exact (not_le_of_gt H) (le_of_lt HS0)
   · rename_i r _
     rw [← coe_ennreal_mul]
     conv =>
       enter [1, 1]
       rw [mul_comm]
     rw [← DivInvMonoid.div_eq_mul_inv]
     rw [ENNReal.div_self ?G1 ?G2]
     case G1 => exact Ne.symm (ne_of_lt HS0)
     simp
     intro
     simp_all

lemma galois_connection_smul_l {s : EReal} (HS0 : 0 < s) (HS1 : s < ⊤) :
    GaloisConnection (HMul.hMul s) (fun (x : EReal) => (ENNReal.toEReal (ENNReal.ofEReal s)⁻¹) * x) := by
  rw [GaloisConnection]
  intro a b
  apply Iff.intro
  · intro
    rw [<- ereal_smul_inv_cancel_2 HS0 HS1 a]
    rw [mul_assoc]
    apply (ereal_le_smul_left _ ?G1 ?G2)
    case G1 =>
      apply coe_ennreal_pos.mpr
      apply bot_lt_iff_ne_bot.mpr
      simp
      intro H
      rw [<- ofEReal_top] at H
      have X := (@ofEReal_nonneg_inj s ⊤ ?G4 ?G5).mpr H
      case G4 => exact le_of_lt HS0
      case G5 => exact OrderTop.le_top 0
      simp_all
    case G2 =>
      apply lt_top_iff_ne_top.mpr
      intro htop
      have hs_zero : ofEReal s = 0 := (ENNReal.inv_eq_top).mp (EReal.coe_ennreal_eq_top_iff.mp htop)
      exact (not_le_of_gt HS0) ((ofEReal_eq_zero_iff s).2 hs_zero)
    assumption
  · intro
    rw [<- ereal_smul_inv_cancel_1 HS0 HS1 b]
    rw [mul_assoc]
    apply (ereal_le_smul_left _ HS0 HS1)
    assumption

end misc

end ENNReal


/-!
### Coercion from PNat to NNReal

Really, we would want to coerce this to a posreal, but there is no posreal type in mathlib, so it would be a lot of work.
-/
@[simp]
def NNReal.ofPNat (p : PNat) : NNReal := ⟨ p.1, Nat.cast_nonneg p.1 ⟩

instance : Coe PNat NNReal where
  coe := NNReal.ofPNat
