/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import SampCert.Samplers.Laplace.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import SampCert.Util.UtilMathlib
import SampCert.Samplers.Gaussian.Code
import SampCert.Util.Gaussian.DiscreteGaussian

/-!
# ``DiscreteGaussianSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteGaussianSample``.
-/

noncomputable section

open Classical PMF Nat Real

namespace SLang

@[simp]
lemma ite_simpl_gaussian_1 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) false
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

@[simp]
lemma ite_simpl_gaussian_2 (num den t: ℕ+) (x a : ℤ) :
  @ite ENNReal (x = a) (propDecidable (x = a)) 0
  (if a = x then
    DiscreteLaplaceSample t 1 x *
      BernoulliExpNegSample (Int.natAbs (Int.sub (|x| * ↑↑t * ↑↑den) ↑↑num) ^ 2) (2 * num * t ^ 2 * den) true
  else 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

@[simp]
lemma if_simpl_4' {α : Type} [DecidableEq α] (x n : α) (a b c : ENNReal) :
  (if x = n then 0 else a * ((if n = x ∧ true = false then b else 0) + if n = x then c else 0)) = 0 := by
  by_cases h : x = n
  · simp [h]
  · have hn : n ≠ x := by simpa [eq_comm] using h
    simp [h, hn]

@[simp]
lemma if_simpl_5' {α : Type} [DecidableEq α] (x a : α) (d : ENNReal) :
  (if x = a then 0 else if a = x then d else 0) = 0 := by
  by_cases h : x = a
  · simp [h]
  · have ha : a ≠ x := by simpa [eq_comm] using h
    simp [h, ha]

/--
Gaussian sampling attempt is a proper distribution.
-/
@[simp]
theorem DiscreteGaussianSampleLoop_normalizes (num den t : ℕ+) (mix : ℕ) :
  ∑' x, (DiscreteGaussianSampleLoop num den t mix) x = 1 := by
  rw [ENNReal.tsum_prod']
  have hsplit :
      ∀ a : ℤ,
        (∑' b : Bool, DiscreteGaussianSampleLoop num den t mix (a, b)) =
          DiscreteLaplaceSample t 1 a := by
    intro a
    rw [tsum_bool]
    have hfalse :
        DiscreteGaussianSampleLoop num den t mix (a, false) =
          DiscreteLaplaceSample t 1 a *
            BernoulliExpNegSample (Int.natAbs (Int.sub (|a| * ↑↑t * ↑↑den) ↑↑num) ^ 2)
              (2 * num * t ^ 2 * den) false := by
      unfold DiscreteGaussianSampleLoop
      simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
      rw [DiscreteLaplaceSampleMixed_equiv]
      rw [tsum_eq_single a]
      · simp
      · intro a₁ ha₁
        have hne : ¬ a = a₁ := by simpa [eq_comm] using ha₁
        simp [hne]
    have htrue :
        DiscreteGaussianSampleLoop num den t mix (a, true) =
          DiscreteLaplaceSample t 1 a *
            BernoulliExpNegSample (Int.natAbs (Int.sub (|a| * ↑↑t * ↑↑den) ↑↑num) ^ 2)
              (2 * num * t ^ 2 * den) true := by
      unfold DiscreteGaussianSampleLoop
      simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
      rw [DiscreteLaplaceSampleMixed_equiv]
      rw [tsum_eq_single a]
      · simp
      · intro a₁ ha₁
        have hne : ¬ a = a₁ := by simpa [eq_comm] using ha₁
        simp [hne]
    rw [hfalse, htrue, ← mul_add, ← tsum_bool, BernoulliExpNegSample_normalizes]
    simp
  simp_rw [hsplit]
  exact DiscreteLaplaceSample_normalizes (num := t) (den := 1)

lemma bind_bind_pair_apply_true (D : SLang ℤ) (f : ℤ → SLang Bool) (n : ℤ) :
  (Bind.bind D (fun y => Bind.bind (f y) (fun c => Pure.pure (y, c)))) (n, true) = D n * f n true := by
  simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply, Prod.mk.injEq, tsum_bool,
    and_true, mul_ite, mul_one]
  rw [tsum_eq_single n]
  · simp
  · intro b hb
    have hnb : n ≠ b := by simpa [eq_comm] using hb
    simp [hnb]

@[simp]
lemma ite_simpl_1' (num den t : PNat) (x : ℤ) (n : ℤ) :
  (@ite ENNReal (x = n) (propDecidable (x = n)) 0
  (@ite ENNReal (n = x) (n.instDecidableEq x)
  (ENNReal.ofReal (((t : ℝ)⁻¹.exp - 1) / ((t : ℝ)⁻¹.exp + 1) * (-(@abs ℝ DistribLattice.toLattice AddGroupWithOne.toAddGroup ↑x / (t : ℝ))).exp) *
    ENNReal.ofReal (-(((|x| * t * den).sub num).natAbs ^ 2 / ((2 : ℕ+) * num * (t : ℝ) ^ 2 * den))).exp)
  0)) = 0 := by
  split
  · simp
  · rename_i h
    simp
    intro h
    subst h
    contradiction

/--
Evaluation of the discrete Gaussian sample loop distribution when the termination flag is ``true``.
-/
@[simp]
theorem DiscreteGaussianSampleLoop_apply_true (num den t : ℕ+) (n : ℤ) (mix : ℕ) :
  (DiscreteGaussianSampleLoop num den t mix) (n, true)
    = ENNReal.ofReal ((rexp (t)⁻¹ - 1) / (rexp (t)⁻¹ + 1)) * ENNReal.ofReal (rexp (-(Int.natAbs n / t)) *
    rexp (-((Int.natAbs (Int.sub (|n| * t * den) ↑↑num)) ^ 2 / ((2 : ℕ+) * num * ↑↑t ^ 2 * den)))) := by
  rw [DiscreteGaussianSampleLoop, DiscreteLaplaceSampleMixed_equiv]
  rw [bind_bind_pair_apply_true]
  simp only [BernoulliExpNegSample_apply_true, DiscreteLaplaceSample_apply, Int.natCast_natAbs,
    NNReal.coe_natCast, PNat.one_coe, cast_one, NNReal.coe_one, div_one, one_div, Int.cast_abs,
    cast_pow, NNReal.coe_pow, PNat.mul_coe, PNat.pow_coe, cast_mul, NNReal.coe_mul]
  rw [ENNReal.ofReal_mul]
  have A : 0 ≤ rexp (-(|↑n| / ↑↑t)) := by
    positivity
  · conv =>
      lhs
      rw [mul_assoc]
      arg 2
      rw [← ENNReal.ofReal_mul A]
    simp [Nat.cast_natAbs, Int.cast_abs]
  · apply div_nonneg
    · simp only [sub_nonneg, one_le_exp_iff, inv_nonneg, cast_nonneg]
    · positivity

@[simp]
lemma if_simpl_2' (x_1 x : ℤ) (a : ENNReal) :
  @ite ENNReal (x_1 = x) (propDecidable (x_1 = x)) 0 (a * (@ite ENNReal (x = x_1) (propDecidable (x = (x_1, true).1))) 1 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      subst h2
      contradiction
    · simp

@[simp]
lemma if_simpl_3' (x_1 x : ℤ) (a b : ENNReal) :
  (if x_1 = x then 0 else a * (if x = x_1 then 1 else 0) + b * (if x = x_1 then 1 else 0)) = 0 := by
  by_cases h : x_1 = x
  · simp [h]
  · have hx : x ≠ x_1 := by simpa [eq_comm] using h
    simp [h, hx]

lemma alg_auto (num den : ℕ+) (x : ℤ) :
  ENNReal.ofReal (
  rexp (-((Int.natAbs x) / ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1))) *
    rexp (-((Int.natAbs (Int.sub (|x| * (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den + 1) * den ^ 2) (num ^ 2))) ^ 2 /
          ((2 : ℕ+) * num ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2 * den ^ 2))))
  = ENNReal.ofReal (rexp (-((num ^ 2) / (2 * den ^ 2 * ((@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + 1) ^ 2)))) *
      ENNReal.ofReal (rexp (- ((x ^ 2 * den ^ 2) /(2 * num ^ 2)))) := by
  let τ := (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ)
  have Tau : (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) = τ := rfl
  rw [Tau]

  have Tau_ne0 : τ ≠ 0 := by
    rw [ne_iff_lt_or_gt]
    right
    apply cast_add_one_pos

  rw [← ENNReal.ofReal_mul]
  · congr 1
    simp [← exp_add]
    simp [division_def]
    rw [(neg_add _ _).symm]
    rw [(neg_add _ _).symm]
    congr 1
    rw [pow_two]
    have A : ∀ x y : ℤ, ((Int.sub x y) : ℝ) = (x : ℝ) - (y : ℝ) := by
      intro x y
      rw [← @Int.cast_sub]
      rfl
    rw [A]
    clear A

    rw [sub_mul]
    rw [mul_sub]
    rw [mul_sub]
    rw [sub_mul]
    rw [sub_mul]
    rw [sub_mul]
    simp

    have X : (@HDiv.hDiv ℤ ℤ ℤ instHDiv num den) + (1 : ℝ) = (@HDiv.hDiv ℕ ℕ ℕ instHDiv num den) + (1 : ℝ) := by
      rfl
    rw [X]
    clear X

    rw [Tau]

    let α := (num : ℝ) ^ 2
    have Alpha : ((num : ℕ+) : ℝ) ^ 2 = α := rfl
    rw [Alpha]

    let β := (den : ℝ) ^ 2
    have Beta : ((den : ℕ+) : ℝ) ^ 2  = β := rfl
    rw [Beta]

    let y := |(x : ℝ)|
    have Y : y = |(x : ℝ)| := rfl

    have Alpha_ne0 : α ≠ 0 := by
      dsimp [α]
      positivity

    have Beta_ne0 : β ≠ 0 := by
      dsimp [β]
      positivity

    field_simp [Alpha_ne0, Beta_ne0, Tau_ne0]
    have xsq_eq_ysq : (x : ℝ) ^ 2 = y ^ 2 := by
      rw [Y]
      simp [sq_abs]
    rw [xsq_eq_ysq]
    ring

  · positivity

lemma alg_auto' (num den : ℕ+) (x : ℤ) :
  -((x : ℝ) ^ 2 * (den : ℝ) ^ 2 / ((2 : ℝ) * (num : ℝ) ^ 2)) = -(x : ℝ) ^ 2 / ((2 : ℝ) * ((num : ℝ) ^ 2 / (den : ℝ) ^ 2)) := by
  ring_nf ; simp ; ring_nf

lemma Add1 (n : Nat) : 0 < n + 1 := by
  simp [Nat.succ_pos n]

/--
Closed form evaluation of the discrete Gaussian sampler
-/
@[simp]
theorem DiscreteGaussianSample_apply (num : PNat) (den : PNat) (mix : ℕ) (x : ℤ) :
  (DiscreteGaussianSample num den mix) x =
  ENNReal.ofReal (discrete_gaussian ((num : ℝ) / (den : ℝ)) 0 x) := by
  unfold discrete_gaussian
  unfold gauss_term_ℝ
  simp
  simp only [DiscreteGaussianSample, Bind.bind, Pure.pure, SLang.bind_apply]
  have A := DiscreteGaussianSampleLoop_normalizes (num ^ 2) (den ^ 2)
    { val := ↑num / ↑den + 1, property := (Add1 (↑num / ↑den) : 0 < ↑num / ↑den + 1) } mix

  simp_rw [probUntil_apply_norm _ _ _ A]
  clear A

  simp only [ENNReal.tsum_prod', tsum_bool, ↓reduceIte, DiscreteGaussianSampleLoop_apply_true,
    PNat.mk_coe, cast_add, cast_one, PNat.pow_coe, cast_pow, ite_mul,
    zero_mul, SLang.pure_apply, div_pow]
  rw [ENNReal.tsum_eq_add_tsum_ite x]
  simp [↓reduceIte, mul_one, tsum_zero, add_zero]

  let τn : ℕ := ↑num / ↑den
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.mul_inv]
  · rw [mul_assoc]
    conv =>
      left
      right
      rw [mul_comm]
      rw [mul_assoc]
    rw [← mul_assoc]
    rw [ENNReal.mul_inv_cancel]
    · simp only [one_mul]
      rw [mul_comm]
      rw [← division_def]
      rw [ENNReal.ofReal_div_of_pos]
      · have hcalc_num := alg_auto num den x
        simp [Nat.cast_natAbs, Int.cast_abs] at hcalc_num ⊢
        rw [hcalc_num]
        have hcalc_tsum :
            (∑' (i : ℤ),
              ENNReal.ofReal
                (rexp (-(|(i : ℝ)| / ((τn : ℝ) + 1))) *
                  rexp
                    (-(((↑((|i| * (τn + 1) * (den : ℕ) ^ 2).sub ((num : ℕ) ^ 2)) : ℝ) ^ 2) /
                        (2 * (num : ℝ) ^ 2 * (((τn : ℝ) + 1) ^ 2) * (den : ℝ) ^ 2))))) =
            ∑' (i : ℤ),
              ENNReal.ofReal
                (rexp (-((num : ℝ) ^ 2 / (2 * (den : ℝ) ^ 2 * (((τn : ℝ) + 1) ^ 2))))) *
                ENNReal.ofReal
                  (rexp (-((i : ℝ) ^ 2 * (den : ℝ) ^ 2 / ((2 : ℝ) * (num : ℝ) ^ 2)))) := by
          congr with i
          simpa [τn, Nat.cast_natAbs, Int.cast_abs] using alg_auto num den i
        have hcalc_tsum' := hcalc_tsum
        simp [τn] at hcalc_tsum'
        rw [hcalc_tsum']
        rw [ENNReal.tsum_mul_left]
        rw [ENNReal.div_eq_inv_mul]
        rw [← mul_assoc]
        let c : ENNReal :=
          ENNReal.ofReal
            (rexp (-((num : ℝ) ^ 2 /
              (2 * (den : ℝ) ^ 2 * ((((↑num / ↑den : ℕ) : ℝ) + 1) ^ 2)))))
        let s : ENNReal :=
          ∑' (i : ℤ), ENNReal.ofReal (rexp (-(↑i ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))
        have A : c ≠ 0 := by
          dsimp [c]
          exact ne_of_gt <| (ENNReal.ofReal_pos).2 <| exp_pos _
        have B : c ≠ ⊤ := by
          dsimp [c]
          exact ENNReal.ofReal_ne_top
        rw [ENNReal.mul_inv]
        · calc
            c⁻¹ * s⁻¹ * c * ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))
                = ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2)))) * s⁻¹ := by
                    calc
                      c⁻¹ * s⁻¹ * c * ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))
                          = (s⁻¹ * ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))) * c⁻¹ * c := by
                              ac_rfl
                      _ = s⁻¹ * ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2)))) := by
                              rw [ENNReal.inv_mul_cancel_right A B]
                      _ = ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2)))) * s⁻¹ := by
                              ac_rfl
            _ = ENNReal.ofReal (rexp (-(↑x ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2)))) /
                  (∑' (i : ℤ), ENNReal.ofReal (rexp (-(↑i ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))) := by
                    rw [← division_def]
          congr
          · rw [alg_auto']
          · have hden :
                (∑' (i : ℤ), ENNReal.ofReal (rexp (-(↑i ^ 2 * ↑↑den ^ 2 / (2 * ↑↑num ^ 2))))) =
                  ENNReal.ofReal (∑' (x : ℤ), rexp (-↑x ^ 2 / (2 * (↑↑num ^ 2 / ↑↑den ^ 2)))) := by
                rw [← ENNReal.ofReal_tsum_of_nonneg]
                · congr with i
                  rw [alg_auto']
                · intro n
                  simp only [exp_nonneg]
                · have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
                    simp
                  have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
                  unfold gauss_term_ℝ at Y
                  simpa [div_pow, pow_two, division_def, mul_assoc, mul_left_comm, mul_comm] using Y
            rw [hden]
        · exact Or.inl A
        · exact Or.inl B
      · have A : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
          simp
        have Y := @summable_gauss_term' ((num : ℝ) / (den : ℝ)) A 0
        unfold gauss_term_ℝ at Y
        simp at Y
        have hpos : 0 < ∑' (i : ℤ), rexp (-↑i ^ 2 / (2 * (((num : ℝ) / (den : ℝ)) ^ 2))) := by
          exact Y.tsum_pos (fun i => by positivity) 0 (by positivity)
        simpa [div_pow, pow_two, division_def, mul_assoc, mul_left_comm, mul_comm] using hpos
    · exact ne_of_gt <| (ENNReal.ofReal_pos).2 <| by
        have ht : 0 < ((τn : ℝ) + 1) := by
          exact cast_add_one_pos τn
        apply _root_.div_pos
        · rw [sub_pos, one_lt_exp_iff]
          exact inv_pos.mpr ht
        · positivity
    · exact ENNReal.ofReal_ne_top
  · exact Or.inl <| ne_of_gt <| (ENNReal.ofReal_pos).2 <| by
      have ht : 0 < ((τn : ℝ) + 1) := by
        exact cast_add_one_pos τn
      apply _root_.div_pos
      · rw [sub_pos, one_lt_exp_iff]
        exact inv_pos.mpr ht
      · positivity
  · exact Or.inl ENNReal.ofReal_ne_top

/--
Discrete Gaussian is a proper distribution
-/
@[simp]
theorem DiscreteGaussianSample_normalizes (num : PNat) (den : PNat) (mix : ℕ) :
  ∑' x : ℤ, (DiscreteGaussianSample num den mix) x = 1 := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  simp_rw [DiscreteGaussianSample_apply]
  rw [← ENNReal.ofReal_tsum_of_nonneg]
  · rw [ENNReal.ofReal_one.symm]
    congr 1
    apply discrete_gaussian_normalizes A
  · intro n
    apply discrete_gaussian_nonneg A 0 n
  · apply discrete_gaussian_summable A

theorem DiscreteGaussianSample_HasSum1 (num : PNat) (den : PNat) (mix : ℕ) :
  HasSum (DiscreteGaussianSample num den mix) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  apply DiscreteGaussianSample_normalizes

def DiscreteGaussianPMF (num : PNat) (den : PNat) (mix : ℕ) : PMF ℤ :=
  ⟨ DiscreteGaussianSample num den mix , DiscreteGaussianSample_HasSum1 num den mix ⟩

end SLang
