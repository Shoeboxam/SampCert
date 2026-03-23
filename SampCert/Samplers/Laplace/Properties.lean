/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Util
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Basic
import SampCert.Samplers.Geometric.Basic
import Mathlib.Data.ENNReal.Inv
import SampCert.Samplers.Laplace.Code

/-!
# ``DiscreteLaplaceSample`` Properties

This file proves evaluation and normalization properties of ``DiscreteLaplaceSample``.
-/

noncomputable section

open Classical PMF Nat Real BigOperators Finset

namespace SLang

@[simp]
theorem DiscreteLaplaceSampleLoopIn1Aux_normalizes (t : PNat) :
  (∑' x : ℕ × Bool, (DiscreteLaplaceSampleLoopIn1Aux t) x) = 1 := by
  rw [ENNReal.tsum_prod']
  have hsplit :
      ∀ a : ℕ,
        (∑' b : Bool, DiscreteLaplaceSampleLoopIn1Aux t (a, b)) = UniformSample t a := by
    intro a
    rw [tsum_bool]
    have hfalse :
        DiscreteLaplaceSampleLoopIn1Aux t (a, false) =
          UniformSample t a * BernoulliExpNegSample a t false := by
      unfold DiscreteLaplaceSampleLoopIn1Aux
      simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
      rw [tsum_eq_single a]
      · simp
      · intro a₁ ha₁
        have hne : ¬ a = a₁ := by simpa [eq_comm] using ha₁
        simp [hne]
    have htrue :
        DiscreteLaplaceSampleLoopIn1Aux t (a, true) =
          UniformSample t a * BernoulliExpNegSample a t true := by
      unfold DiscreteLaplaceSampleLoopIn1Aux
      simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
      rw [tsum_eq_single a]
      · simp
      · intro a₁ ha₁
        have hne : ¬ a = a₁ := by simpa [eq_comm] using ha₁
        simp [hne]
    rw [hfalse, htrue, ← mul_add, ← tsum_bool, BernoulliExpNegSample_normalizes]
    simp
  simp_rw [hsplit]
  exact UniformSample_normalizes t


theorem DiscreteLaplaceSampleLoopIn1Aux_apply_true (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, true)
    = if n < t then ENNReal.ofReal (rexp (- (n / t))) / t else 0 := by
  have hpoint :
      DiscreteLaplaceSampleLoopIn1Aux t (n, true) =
        UniformSample t n * BernoulliExpNegSample n t true := by
    unfold DiscreteLaplaceSampleLoopIn1Aux
    simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
    rw [tsum_eq_single n]
    · simp
    · intro a ha
      have hne : ¬ n = a := by simpa [eq_comm] using ha
      simp [hne]
  rw [hpoint]
  rw [UniformSample_apply', BernoulliExpNegSample_apply_true]
  by_cases h : n < t
  · simp [h, division_def, mul_comm]
  · simp [h]

theorem DiscreteLaplaceSampleLoopIn1Aux_apply_false (t : PNat) (n : ℕ) :
  DiscreteLaplaceSampleLoopIn1Aux t (n, false)
    = if n < t then (1 - ENNReal.ofReal (rexp (- (n / t)))) / t else 0 := by
  have hpoint :
      DiscreteLaplaceSampleLoopIn1Aux t (n, false) =
        UniformSample t n * BernoulliExpNegSample n t false := by
    unfold DiscreteLaplaceSampleLoopIn1Aux
    simp only [Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
    rw [tsum_eq_single n]
    · simp
    · intro a ha
      have hne : ¬ n = a := by simpa [eq_comm] using ha
      simp [hne]
  rw [hpoint]
  rw [UniformSample_apply', BernoulliExpNegSample_apply_false]
  by_cases h : n < t
  · simp [h, division_def, mul_comm]
  · simp [h]

theorem DiscreteLaplaceSampleLoopIn1_apply_pre (t : PNat) (n : ℕ) :
  (DiscreteLaplaceSampleLoopIn1 t) n =
    DiscreteLaplaceSampleLoopIn1Aux t (n, true) * (∑' (a : ℕ), DiscreteLaplaceSampleLoopIn1Aux t (a, true))⁻¹ := by
  simp only [DiscreteLaplaceSampleLoopIn1, Bind.bind, Pure.pure, SLang.bind_apply, SLang.pure_apply]
  simp_rw [probUntil_apply_norm _ _ _ (DiscreteLaplaceSampleLoopIn1Aux_normalizes t)]
  rw [ENNReal.tsum_prod']
  simp only [tsum_bool]
  simp only [↓reduceIte, ite_mul, zero_mul]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp only [↓reduceIte, mul_one, Bool.false_eq_true, zero_add]
  have htail :
      (∑' x : ℕ,
        if x = n then 0
        else
          DiscreteLaplaceSampleLoopIn1Aux t (x, true) *
            (∑' (a : ℕ × Bool), if a.2 = true then DiscreteLaplaceSampleLoopIn1Aux t a else 0)⁻¹ *
            if n = x then 1 else 0) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x = n
    · simp [hx]
    · have hx' : n ≠ x := by simpa [eq_comm] using hx
      simp [hx, hx']
  simp
  have hden :
      (∑' (a : ℕ × Bool), if a.2 = true then DiscreteLaplaceSampleLoopIn1Aux t a else 0) =
        ∑' a : ℕ, DiscreteLaplaceSampleLoopIn1Aux t (a, true) := by
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro a
    rw [tsum_bool]
    simp
  rw [hden]
  have htail' :
      (∑' x : ℕ,
        if x = n then 0
        else
          if n = x then
            DiscreteLaplaceSampleLoopIn1Aux t (x, true) *
              (∑' a : ℕ, DiscreteLaplaceSampleLoopIn1Aux t (a, true))⁻¹
          else 0) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x = n
    · simp [hx]
    · have hx' : n ≠ x := by simpa [eq_comm] using hx
      simp [hx, hx']
  simp [htail']

theorem DiscreteLaplaceSampleLoopIn1_apply (t : PNat) (n : ℕ) (support : n < t) :
  (DiscreteLaplaceSampleLoopIn1 t) n = (ENNReal.ofReal ((rexp (-ENNReal.toReal (n / t))) * ((1 - rexp (- 1 / t)) / (1 - rexp (- 1))))) := by
  rw [DiscreteLaplaceSampleLoopIn1_apply_pre]
  rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
  simp only [support, ↓reduceIte]
  simp_rw [DiscreteLaplaceSampleLoopIn1Aux_apply_true]

  have hsum :
      (∑' (a : ℕ), if a < ↑t then ENNReal.ofReal (rexp (-(↑a / ↑↑t))) / ↑↑t else 0) =
        Finset.sum (Finset.range t) (fun a => ENNReal.ofReal (rexp (-(↑a / ↑↑t))) / ↑↑t) := by
    rw [← ENNReal.sum_add_tsum_compl (s := Finset.range t)
      (f := fun a : ℕ => if a < ↑t then ENNReal.ofReal (rexp (-(↑a / ↑↑t))) / ↑↑t else 0)]
    have htail :
        (∑' a : ↥((↑(Finset.range t) : Set ℕ)ᶜ),
          if (a : ℕ) < ↑t then ENNReal.ofReal (rexp (-(↑(a : ℕ) / ↑↑t))) / ↑↑t else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro a
      have ha : ¬ ((a : ℕ) < ↑t) := by
        simpa [Finset.mem_range] using a.property
      simp [ha]
    rw [htail, add_zero]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have ha' : a < ↑t := by
      simpa [Finset.mem_range] using ha
    simp [ha']
  rw [hsum]

  simp_rw [division_def]

  have A :
      (∑ x ∈ Finset.range t, ENNReal.ofReal (rexp (-(↑x * (↑↑t)⁻¹)))) * (↑↑t)⁻¹ =
        ∑ x ∈ Finset.range t, ENNReal.ofReal (rexp (-(↑x * (↑↑t)⁻¹))) * (↑↑t)⁻¹ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (@sum_mul ℕ ENNReal _ (Finset.range t)
        (fun x => ENNReal.ofReal (rexp (-(↑x * (↑↑t)⁻¹)))) ((↑↑t)⁻¹))
  rw [← A]
  clear A

  conv_rhs =>
    change ENNReal.ofReal
      (Real.exp (-ENNReal.toReal (n / t)) *
        ((1 - Real.exp (-1 / t)) * (1 - Real.exp (-1))⁻¹))
    rw [ENNReal.ofReal_mul (exp_nonneg _)]
  rw [division_def]
  rw [mul_assoc]
  congr

  · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv]
    simp

  · have A : ∀ i ∈ range t, 0 ≤ rexp (-(↑i * (↑↑t)⁻¹)) := by
      intro i _
      apply exp_nonneg (-(↑i * (↑↑t)⁻¹))

    rw [← ENNReal.ofReal_sum_of_nonneg A]
    clear A

    have A : rexp (- 1 / t) ≠ 1 := by
      rw [← Real.exp_zero]
      by_contra h
      simp only [exp_zero, exp_eq_one_iff, div_eq_zero_iff, neg_eq_zero, one_ne_zero, cast_eq_zero,
        PNat.ne_zero, or_self] at h
    have X := @geom_sum_Ico' ℝ _ (rexp (- 1 / t)) A 0 t (Nat.zero_le t)
    simp only [Ico_zero_eq_range, _root_.pow_zero] at X
    rw [← exp_nat_mul] at X
    rw [mul_div_cancel₀ _ (NeZero.natCast_ne ↑t ℝ)] at X

    have hpow :
        Finset.sum (range t) (fun i => rexp (-(↑i * (↑↑t)⁻¹))) =
          Finset.sum (range t) (fun i => (rexp (- 1 / t)) ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (-(↑i * (↑↑t : ℝ)⁻¹)) = (i : ℝ) * (-1 / t) by
        rw [neg_mul_eq_mul_neg, inv_eq_one_div]
        ring]
      rw [Real.exp_nat_mul]
    rw [hpow]
    rw [X]
    clear X
    rw [ENNReal.mul_inv]
    · rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel]
      · rw [← ENNReal.ofReal_inv_of_pos]
        · have hpos1 : 0 < 1 - rexp (-1) := by
            have hexp : rexp (-1 : ℝ) < 1 := by
              simp [Real.exp_lt_one_iff.mpr]
            linarith
          have hpos2 : 0 < 1 - rexp (-1 / (↑↑t : ℝ)) := by
            have hneg : (-1 / (↑↑t : ℝ)) < 0 := by
              have ht : (0 : ℝ) < ↑↑t := by exact_mod_cast t.pos
              rw [neg_div]
              exact neg_neg_iff_pos.mpr (one_div_pos.mpr ht)
            have hexp : rexp (-1 / (↑↑t : ℝ)) < 1 := by
              simpa using (Real.exp_lt_one_iff.mpr hneg)
            linarith
          field_simp [ne_of_gt hpos1, ne_of_gt hpos2]
          simp
        · have hpos1 : 0 < 1 - rexp (-1) := by
            have hexp : rexp (-1 : ℝ) < 1 := by
              simp [Real.exp_lt_one_iff.mpr]
            linarith
          have hpos2 : 0 < 1 - rexp (-1 / (↑↑t : ℝ)) := by
            have hneg : (-1 / (↑↑t : ℝ)) < 0 := by
              have ht : (0 : ℝ) < ↑↑t := by exact_mod_cast t.pos
              rw [neg_div]
              exact neg_neg_iff_pos.mpr (one_div_pos.mpr ht)
            have hexp : rexp (-1 / (↑↑t : ℝ)) < 1 := by
              simpa using (Real.exp_lt_one_iff.mpr hneg)
            linarith
          exact mul_pos hpos1 (inv_pos.mpr hpos2)
      · simp only [ne_eq, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, not_false_eq_true]
      · simp only [ne_eq, ENNReal.inv_eq_top, cast_eq_zero, PNat.ne_zero, not_false_eq_true]
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, ENNReal.inv_eq_top, cast_eq_zero,
      PNat.ne_zero, not_false_eq_true, or_true]
    · simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true, ENNReal.inv_eq_zero,
      ENNReal.natCast_ne_top, or_self]

@[simp]
theorem DiscreteLaplaceSampleLoopIn2_eq (num : Nat) (den : PNat) :
  DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat)
    = probGeometric (BernoulliExpNegSample num den) := by
  unfold DiscreteLaplaceSampleLoopIn2
  unfold DiscreteLaplaceSampleLoopIn2Aux
  unfold probGeometric
  unfold geoLoopCond
  unfold geoLoopBody
  rfl



@[simp]
theorem DiscreteLaplaceSampleLoop_apply (num : PNat) (den : PNat) (n : ℕ) (b : Bool) :
  (DiscreteLaplaceSampleLoop num den) (b,n)
    = ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) * ((2 : ℕ+): ENNReal)⁻¹ := by
  simp [DiscreteLaplaceSampleLoop, DiscreteLaplaceSampleLoopIn2_eq, probGeometric_apply,
    BernoulliSample_apply]
  rw [tsum_eq_single (n + 1)]
  · cases b <;> simp
  · intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxne : n ≠ x - 1 := by
        intro h
        apply hx
        calc
          x = x - 1 + 1 := (succ_pred hx0).symm
          _ = n + 1 := by rw [h]
      cases b <;> simp [hx0, hxne]

@[simp]
theorem ite_simpl_1 (x y : ℕ) (a : ENNReal) : ite (x = y) 0 (ite (y = x) a 0) = 0 := by
  split
  · simp
  · rename_i h
    simp
    intro h
    subst h
    contradiction

@[simp]
theorem ite_simpl_2 (x y : ℕ) (a : ENNReal) : ite (x = 0) 0 (ite ((y : ℤ) = -(x : ℤ)) a 0) = 0 := by
  split
  · simp
  · split
    · rename_i h1 h2
      have A : (y : ℤ) ≥ 0 := Int.NonNeg.mk (y + 0)
      rw [h2] at A
      simp at *
      subst A
      contradiction
    · simp

@[simp]
theorem ite_simpl_3 (x y : ℕ) (a : ENNReal) : ite (x = y + 1) 0 (ite (x = 0) 0 (ite (y = x - 1) a 0)) = 0 := by
  split
  · simp
  · split
    · simp
    · split
      · rename_i h1 h2 h3
        subst h3
        cases x
        · contradiction
        · simp at h1
      · simp

@[simp]
theorem ite_simpl_4 (x y : ℕ) (a : ENNReal) : ite ((x : ℤ) = - (y : ℤ)) (ite (y = 0) 0 a) 0 = 0 := by
  split
  · split
    · simp
    · rename_i h1 h2
      have B : (y : ℤ) ≥ 0 := by exact Int.NonNeg.mk (y + 0)
      have C : -(y : ℤ) ≥ 0 := by exact le_iff_exists_sup.mpr (Exists.intro (Int.ofNat x) (id h1.symm))
      cases y
      · contradiction
      · rename_i n
        simp at C
        contradiction
  · simp

@[simp]
theorem ite_simpl_5 (n c : ℕ) (a : ENNReal) (h : n ≠ 0) : ite (- (n : ℤ) = (c : ℤ)) a 0 = 0 := by
  split
  · rename_i h'
    have A : (n : ℤ) ≥ 0 := by exact Int.NonNeg.mk (n + 0)
    have B : -(n : ℤ) ≥ 0 := by exact le_iff_exists_sup.mpr (Exists.intro (Int.ofNat c) h')
    cases n
    · contradiction
    · rename_i n
      simp at B
      contradiction
  · simp

@[simp]
theorem DiscreteLaplaceSampleLoop_normalizes (num : PNat) (den : PNat) :
  (∑' x, (DiscreteLaplaceSampleLoop num den) x) = 1 := by
  let q : ENNReal := ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp only [DiscreteLaplaceSampleLoop_apply]
  have hq_lt_one : q < 1 := by
    dsimp [q]
    apply ENNReal.ofReal_lt_one.mpr
    apply Real.exp_lt_one_iff.mpr
    have hnum : (0 : ℝ) < ↑↑num := by exact_mod_cast num.pos
    have hden : (0 : ℝ) < ↑↑den := by exact_mod_cast den.pos
    have : (0 : ℝ) < ↑↑den / ↑↑num := div_pos hden hnum
    linarith
  have hsub_ne_zero : 1 - q ≠ 0 := by
    exact pos_iff_ne_zero.mp (by simpa [tsub_pos_iff_lt] using hq_lt_one)
  have hsub_ne_top : 1 - q ≠ ⊤ := by
    simp
  have hgeom : ∑' n : ℕ, q ^ n * (1 - q) = 1 := by
    simpa [q, mul_comm] using
      (probGeometric_normalizes'
        (trial := BernoulliExpNegSample (↑den) num)
        (by
          have h := BernoulliExpNegSample_normalizes den num
          simpa [tsum_bool, add_comm] using h)
        (by simp))
  have hhalf :
      (∑' b : ℕ, q ^ b * (1 - q) * (((2 : ℕ+) : ENNReal)⁻¹)) = (((2 : ℕ+) : ENNReal)⁻¹) := by
    exact (by
      have hh := congrArg (fun z : ENNReal => z * (((2 : ℕ+) : ENNReal)⁻¹)) hgeom
      simpa [ENNReal.tsum_mul_right, mul_assoc] using hh)
  rw [hhalf]
  simpa [one_div] using (ENNReal.add_halves (1 : ENNReal))

theorem avoid_double_counting (num den : PNat) :
  (∑' (x : Bool × ℕ), if x.1 = true → ¬x.2 = 0 then DiscreteLaplaceSampleLoop num den x else 0)
    = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  let q : ENNReal := ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))
  let h : ENNReal := (((2 : ℕ+) : ENNReal))⁻¹
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp only [DiscreteLaplaceSampleLoop_apply, Bool.false_eq_true]
  have hq_lt_one : q < 1 := by
    dsimp [q]
    apply ENNReal.ofReal_lt_one.mpr
    apply Real.exp_lt_one_iff.mpr
    have hnum : (0 : ℝ) < ↑↑num := by exact_mod_cast num.pos
    have hden : (0 : ℝ) < ↑↑den := by exact_mod_cast den.pos
    have : (0 : ℝ) < ↑↑den / ↑↑num := div_pos hden hnum
    linarith
  have hsub_ne_zero : 1 - q ≠ 0 := by
    exact pos_iff_ne_zero.mp (by simpa [tsub_pos_iff_lt] using hq_lt_one)
  have hsub_ne_top : 1 - q ≠ ⊤ := by
    simp
  have hgeom : ∑' n : ℕ, q ^ n * (1 - q) = 1 := by
    simpa [q, mul_comm] using
      (probGeometric_normalizes'
        (trial := BernoulliExpNegSample (↑den) num)
        (by
          have h' := BernoulliExpNegSample_normalizes den num
          simpa [tsum_bool, add_comm] using h')
        (by simp))
  have hseries : ∑' n : ℕ, q ^ n * (1 - q) * h = h := by
    have hh := congrArg (fun z : ENNReal => z * h) hgeom
    simpa [ENNReal.tsum_mul_right, mul_assoc] using hh
  have htail :
      (∑' n : ℕ, if n = 0 then 0 else q ^ n * (1 - q) * h) = q * h := by
    rw [tsum_shift'_1]
    rw [show (fun n : ℕ => q ^ (n + 1) * (1 - q) * h) =
        fun n : ℕ => q * (q ^ n * (1 - q) * h) by
          funext n
          rw [_root_.pow_succ']
          simp [mul_assoc, mul_left_comm, mul_comm]]
    rw [ENNReal.tsum_mul_left]
    rw [hseries]
  have hseries' : (∑' b : ℕ, h * (q ^ b * (1 - q))) = h := by
    have hh := congrArg (fun z : ENNReal => h * z) hgeom
    simpa [ENNReal.tsum_mul_left] using hh
  have htail' : (∑' b : ℕ, if b = 0 then 0 else h * (q ^ b * (1 - q))) = q * h := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using htail
  have hsum :
      (∑' b : ℕ, h * (q ^ b * (1 - q))) +
        (∑' b : ℕ, if b = 0 then 0 else h * (q ^ b * (1 - q))) =
        (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
    rw [hseries', htail']
    calc
      h + q * h = h * 1 + h * q := by rw [mul_comm q h, mul_one]
      _ = h * (1 + q) := by rw [mul_add]
      _ = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
        rfl
  simpa [q, h, mul_assoc, mul_left_comm, mul_comm] using hsum

theorem laplace_loop_zero_mass (num den : PNat) :
  (∑' (x : Bool × ℕ), if x.1 = false ∨ ¬x.2 = 0 then 0 else DiscreteLaplaceSampleLoop num den x)
    = (((2 : ℕ+) : ENNReal))⁻¹ * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp only [DiscreteLaplaceSampleLoop_apply, true_or, ↓reduceIte]
  rw [tsum_eq_single 0]
  · simp
    rw [mul_comm]
  · intro b hb
    simp

theorem laplace_loop_nonzero_mass (num den : PNat) :
  1 - (∑' (x : Bool × ℕ), if x.1 = false ∨ ¬x.2 = 0 then 0 else DiscreteLaplaceSampleLoop num den x)
    = (((2 : ℕ+) : ENNReal))⁻¹ * (1 + ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) := by
  let q : ENNReal := ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))
  let h : ENNReal := (((2 : ℕ+) : ENNReal))⁻¹
  rw [laplace_loop_zero_mass]
  change 1 - (h * (1 - q)) = h * (1 + q)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    apply ENNReal.ofReal_lt_one.mpr
    apply Real.exp_lt_one_iff.mpr
    have hnum : (0 : ℝ) < ↑↑num := by exact_mod_cast num.pos
    have hden : (0 : ℝ) < ↑↑den := by exact_mod_cast den.pos
    have : (0 : ℝ) < ↑↑den / ↑↑num := div_pos hden hnum
    linarith
  have hle : h * (1 - q) ≤ 1 := by
    have hqle : q ≤ 1 := le_of_lt hq_lt_one
    have hsub : 1 - q ≤ 1 := by
      simp
    calc
      h * (1 - q) ≤ h * 1 := by gcongr
      _ ≤ 1 := by
        dsimp [h]
        simp
  have hb_ne_top : h * (1 - q) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · dsimp [h]
      simp
    · simp
  refine ((ENNReal.cancel_of_ne hb_ne_top).tsub_eq_iff_eq_add_of_le hle).2 ?_
  have hsumq : (1 + q) + (1 - q) = 2 := by
    calc
      (1 + q) + (1 - q) = 1 + (q + (1 - q)) := by rw [add_assoc]
      _ = 1 + 1 := by rw [add_comm q (1 - q), tsub_add_cancel_of_le (le_of_lt hq_lt_one)]
      _ = 2 := by norm_num
  calc
    1 = h * 2 := by
      dsimp [h]
      simpa [mul_comm] using
        (ENNReal.inv_mul_cancel
          (by simp : (((2 : ℕ+) : ENNReal)) ≠ 0)
          (by simp : (((2 : ℕ+) : ENNReal)) ≠ ⊤)).symm
    _ = h * ((1 + q) + (1 - q)) := by
      rw [hsumq]
    _ = h * (1 + q) + h * (1 - q) := by rw [mul_add]

theorem laplace_normalizer_swap (num den : ℕ+) :
  (1 - rexp (-(↑↑den / ↑↑num))) * (1 + rexp (-(↑↑den / ↑↑num)))⁻¹ =
  (rexp (↑↑den / ↑↑num) - 1) * (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by

  have X : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
  have Y : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))

  have A : rexp (↑↑den / ↑↑num) + 1 ≠ 0 := by
    apply _root_.ne_of_gt
    apply Right.add_pos_of_nonneg_of_pos Y
    simp
  have B : 1 + rexp (-(↑↑den / ↑↑num)) ≠ 0 := by
    apply _root_.ne_of_gt
    apply Right.add_pos_of_pos_of_nonneg _ X
    simp

  rw [← division_def]
  rw [div_eq_iff B]
  rw [mul_comm]
  rw [← mul_assoc]
  rw [← division_def]

  apply Eq.symm
  rw [div_eq_iff A]

  rw [mul_add]
  rw [_root_.sub_mul]
  rw [_root_.sub_mul]
  rw [add_mul]
  rw [_root_.mul_sub]
  rw [_root_.mul_sub]
  have hmul :
      rexp (-(↑↑den / ↑↑num)) * rexp (↑↑den / ↑↑num) = 1 := by
    rw [← Real.exp_add]
    rw [neg_add_cancel]
    simp
  rw [hmul]
  ring

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
  theorem DiscreteLaplaceSample_apply (num den : PNat) (x : ℤ) :
  (DiscreteLaplaceSample num den) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply,
    ENNReal.tsum_prod', tsum_bool, ↓reduceIte, SLang.pure_apply,
    mul_ite, mul_one, mul_zero, one_div, Int.cast_abs]
  simp

  have OR : x ≥ 0 ∨ x < 0 := by exact le_or_gt 0 x
  cases OR
  · rename_i h1
    lift x to ℕ using h1
    conv =>
      left
      left
      rw [ENNReal.tsum_eq_add_tsum_ite x]

    simp (config := { contextual := true }) only [↓reduceIte, Nat.cast_inj, ite_simpl_1, tsum_zero,
      add_zero, ite_simpl_4]
    conv =>
      right
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, Int.cast_natCast, Complex.ofReal_natCast,
        Int.abs_natCast]
    conv =>
      right
      right
      left
      rw [division_def]
    rw [laplace_loop_nonzero_mass]
    rw [ENNReal.mul_inv]
    · simp only [inv_inv]

      have A : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
      have B : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))
      have habsx : (|↑x| : ℝ) = (x : ℕ) := by simp

      -- Start of first rewrite

      rw [ENNReal.ofReal_mul]
      conv =>
        right
        rw [mul_comm]
        left
        right
        rw [division_def]
        rw [neg_mul_eq_mul_neg]
        rw [habsx]
        rw [Real.exp_nat_mul]
        rw [inv_div]

      rw [ENNReal.ofReal_pow]

      conv =>
        left
        left
        rw [mul_assoc]
      conv =>
        left
        rw [mul_assoc]

      congr

      --end of first rewrite

      have X : ((2 : ℕ+) : ENNReal) ≠ 0 := by simp
      have Y : ((2 : ℕ+) : ENNReal) ≠ ⊤ := by simp
      have htwo : (2⁻¹ : ENNReal) * (((2 : ℕ+) : ENNReal)) = 1 := by
        simpa using (ENNReal.inv_mul_cancel X Y)

      rw [← mul_assoc]
      conv =>
        left
        left
        rw [mul_assoc]
        right
        rw [htwo]

      simp only [mul_one]

      clear X Y

      -- end of second rewrite

      rw [ENNReal.ofReal_one.symm]
      rw [← ENNReal.ofReal_add]
      rw [← ENNReal.ofReal_sub]
      rw [← ENNReal.ofReal_inv_of_pos]
      rw [← ENNReal.ofReal_mul]

      congr 1

      -- end of 3rd rewrite
      rw [laplace_normalizer_swap]

      · apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        simp
        rw [div_nonneg_iff]
        left
        simp only [cast_nonneg, and_self]
      · refine Right.add_pos_of_pos_of_nonneg ?inl.intro.e_a.ha A
        simp only [zero_lt_one] -- 0 < 1 + rexp (-(↑↑den / ↑↑num))
      · exact A
      · simp only [zero_le_one] -- 0 ≤ 1
      · exact A
      · exact A
      · have X : 0 ≤ (rexp (↑↑den / ↑↑num) - 1) := by
          apply sub_nonneg.mpr
          apply one_le_exp_iff.mpr
          exact div_nonneg (by exact_mod_cast den.pos.le) (by exact_mod_cast num.pos.le)
        have Y : 0 ≤ (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
          rw [inv_nonneg]
          refine Right.add_nonneg B ?hb
          simp only [zero_le_one]
        exact mul_nonneg X Y
    · simp
    · simp
  · rename_i h1
    have A : ∃ n : ℕ, - n = x := by
      cases x
      · contradiction
      · rename_i a
        exists (a + 1)
    cases A
    rename_i n h2
    conv =>
      left
      right
      rw [ENNReal.tsum_eq_add_tsum_ite n]

    subst h2
    have X : n ≠ 0 := by
      by_contra h
      subst h
      simp only [CharP.cast_eq_zero, neg_zero, lt_self_iff_false] at h1
    simp (config := { contextual := true }) [X]
    conv =>
      right
      simp only [PNat.val_ofNat, reduceSucc, cast_ofNat, Int.cast_natCast, Complex.ofReal_neg,
        Complex.ofReal_natCast, map_neg_eq_map, Int.abs_natCast]
    conv =>
      right
      right
      left
      rw [division_def]
    rw [laplace_loop_nonzero_mass]
    rw [ENNReal.mul_inv]
    · simp only [inv_inv]

      have A : 0 ≤ rexp (-(↑↑den / ↑↑num)) := by apply exp_nonneg (-(↑↑den / ↑↑num))
      have B : 0 ≤ rexp ((↑↑den / ↑↑num)) := by apply exp_nonneg ((↑↑den / ↑↑num))
      have habsn : (|(-↑n : ℤ)| : ℝ) = (n : ℕ) := by simp

      -- Start of first rewrite

      rw [ENNReal.ofReal_mul]
      conv =>
        right
        rw [mul_comm]
        left
        right
        rw [division_def]
        rw [neg_mul_eq_mul_neg]
        rw [Real.exp_nat_mul]
        rw [inv_div]

      rw [ENNReal.ofReal_pow]

      conv =>
        left
        left
        rw [mul_assoc]
      conv =>
        left
        rw [mul_assoc]

      congr

      --end of first rewrite

      have X : ((2 : ℕ+) : ENNReal) ≠ 0 := by simp
      have Y : ((2 : ℕ+) : ENNReal) ≠ ⊤ := by simp
      have htwo : (2 : ENNReal)⁻¹ * (((2 : ℕ+) : ENNReal)) = 1 := by
        simpa using (ENNReal.inv_mul_cancel X Y)

      rw [← mul_assoc]
      conv =>
        left
        left
        rw [mul_assoc]
        right
        rw [htwo]

      simp only [mul_one]

      clear X Y

      -- end of second rewrite

      rw [ENNReal.ofReal_one.symm]
      rw [← ENNReal.ofReal_add]
      rw [← ENNReal.ofReal_sub]
      rw [← ENNReal.ofReal_inv_of_pos]
      rw [← ENNReal.ofReal_mul]

      congr 1

      rw [laplace_normalizer_swap]
      · apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        exact neg_nonpos.mpr <|
          div_nonneg
            (show (0 : ℝ) ≤ ↑↑den by exact_mod_cast den.pos.le)
            (show (0 : ℝ) ≤ ↑↑num by exact_mod_cast num.pos.le)
      · apply Right.add_pos_of_pos_of_nonneg
        simp only [zero_lt_one]
        exact A
      · exact A
      · simp only [zero_le_one] -- 0 ≤ 1
      · exact A
      · exact A
      · have X : 0 ≤ (rexp (↑↑den / ↑↑num) - 1) := by
          apply sub_nonneg.mpr
          apply one_le_exp_iff.mpr
          exact div_nonneg (by exact_mod_cast den.pos.le) (by exact_mod_cast num.pos.le)
        have Y : 0 ≤ (rexp (↑↑den / ↑↑num) + 1)⁻¹ := by
          rw [inv_nonneg]
          refine Right.add_nonneg B ?hb
          simp only [zero_le_one]
        exact mul_nonneg X Y

    · left
      norm_num
    · left
      simp only [ne_eq, ENNReal.inv_eq_top, cast_eq_zero, PNat.ne_zero, not_false_eq_true]

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSample_normalizes (num den : PNat) :
  ∑' x : ℤ, (DiscreteLaplaceSample num den) x = 1 := by
  simp only [DiscreteLaplaceSample, Bind.bind, not_and, Pure.pure, SLang.bind_apply]
  have A := DiscreteLaplaceSampleLoop_normalizes num den
  simp_rw [probUntil_apply_norm _ _ _ A]
  simp only [ENNReal.tsum_prod']

  -- Commuting the integer and natural summand makes the proof simpler
  rw [ENNReal.tsum_comm]
  nth_rewrite 2 [ENNReal.tsum_comm]

  simp only [decide_eq_true_eq, tsum_bool, ↓reduceIte, forall_true_left, ite_not, ite_mul,
    zero_mul, SLang.pure_apply, mul_ite, mul_one, mul_zero]

  let q : ENNReal := ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))
  let h : ENNReal := (2 : ENNReal)⁻¹
  let c : ENNReal := (∑' b : ℕ, (q ^ b * (1 - q) * h + if b = 0 then 0 else q ^ b * (1 - q) * h))⁻¹
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp_rw [DiscreteLaplaceSampleLoop_apply]
  simp
  change
    ((∑' a : ℤ, ∑' b : ℕ, if a = ↑b then q ^ b * (1 - q) * h * c else 0) +
      ∑' a : ℤ, ∑' b : ℕ, if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h * c else 0) = 1
  have hinner1 :
      ∀ a : ℤ,
        (∑' b : ℕ, if a = ↑b then q ^ b * (1 - q) * h * c else 0) =
          (∑' b : ℕ, if a = ↑b then q ^ b * (1 - q) * h else 0) * c := by
    intro a
    calc
      (∑' b : ℕ, if a = ↑b then q ^ b * (1 - q) * h * c else 0)
        = ∑' b : ℕ, (if a = ↑b then q ^ b * (1 - q) * h else 0) * c := by
            apply tsum_congr
            intro b
            split <;> simp [mul_assoc]
      _ = (∑' b : ℕ, if a = ↑b then q ^ b * (1 - q) * h else 0) * c := by
            rw [ENNReal.tsum_mul_right]
  have hinner2 :
      ∀ a : ℤ,
        (∑' b : ℕ, if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h * c else 0) =
          (∑' b : ℕ, if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h else 0) * c := by
    intro a
    calc
      (∑' b : ℕ, if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h * c else 0)
        = ∑' b : ℕ, (if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h else 0) * c := by
            apply tsum_congr
            intro b
            split <;> simp [mul_assoc]
      _ = (∑' b : ℕ, if a = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h else 0) * c := by
            rw [ENNReal.tsum_mul_right]
  simp_rw [hinner1, hinner2]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_right]
  rw [← add_mul]

  have hsum :
      ((∑' i : ℤ, ∑' b : ℕ, if i = ↑b then q ^ b * (1 - q) * h else 0) +
        ∑' i : ℤ, ∑' b : ℕ, if i = -↑b then if b = 0 then 0 else q ^ b * (1 - q) * h else 0) =
      (∑' b : ℕ, (q ^ b * (1 - q) * h + if b = 0 then 0 else q ^ b * (1 - q) * h)) := by
    nth_rewrite 1 [ENNReal.tsum_comm]
    nth_rewrite 2 [ENNReal.tsum_comm]
    rw [← @ENNReal.tsum_add]
    apply tsum_congr
    intro b
    rw [tsum_eq_single (↑b : ℤ)]
    · rw [tsum_eq_single (-↑b : ℤ)]
      · by_cases hb : b = 0
        · subst hb
          simp [q, h]
        · simp [hb, q, h]
      · intro a ha
        simp [ha]
    · intro a ha
      simp [ha]
  rw [hsum]
  simp [c]
  have hden :
      (∑' b : ℕ, (q ^ b * (1 - q) * h + if b = 0 then 0 else q ^ b * (1 - q) * h)) = h * (1 + q) := by
    have hq_lt_one : q < 1 := by
      dsimp [q]
      apply ENNReal.ofReal_lt_one.mpr
      apply Real.exp_lt_one_iff.mpr
      have hnum : (0 : ℝ) < ↑↑num := by exact_mod_cast num.pos
      have hden : (0 : ℝ) < ↑↑den := by exact_mod_cast den.pos
      have : (0 : ℝ) < ↑↑den / ↑↑num := div_pos hden hnum
      linarith
    have hgeom : ∑' n : ℕ, q ^ n * (1 - q) = 1 := by
      simpa [q, mul_comm] using
        (probGeometric_normalizes'
          (trial := BernoulliExpNegSample (↑den) num)
          (by
            have h' := BernoulliExpNegSample_normalizes den num
            simpa [tsum_bool, add_comm] using h')
          (by simp))
    have hseries : ∑' b : ℕ, q ^ b * (1 - q) * h = h := by
      have hh := congrArg (fun z : ENNReal => z * h) hgeom
      simpa [ENNReal.tsum_mul_right, mul_assoc] using hh
    have htail : (∑' b : ℕ, if b = 0 then 0 else q ^ b * (1 - q) * h) = q * h := by
      rw [tsum_shift'_1]
      rw [show (fun n : ℕ => q ^ (n + 1) * (1 - q) * h) =
          fun n : ℕ => q * (q ^ n * (1 - q) * h) by
            funext n
            rw [_root_.pow_succ']
            simp [mul_assoc, mul_left_comm, mul_comm]]
      rw [ENNReal.tsum_mul_left]
      rw [hseries]
    rw [ENNReal.tsum_add, hseries, htail]
    calc
      h + q * h = h + h * q := by
        rw [mul_comm q h]
      _ = h * 1 + h * q := by
        rw [mul_one]
      _ = h * (1 + q) := by
        rw [mul_add, mul_one]
  have hden_ne_zero : h * (1 + q) ≠ 0 := by
    apply mul_ne_zero
    · simp [h]
    · have hq_pos : 0 < q := by
        dsimp [q]
        exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
      exact add_ne_zero.mpr <| Or.inl (by simp : (1 : ENNReal) ≠ 0)
  have hden_ne_top : h * (1 + q) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [h]
    · simp [q]
  exact by
    simpa [c, hden] using (ENNReal.mul_inv_cancel hden_ne_zero hden_ne_top)


/--
PMF for the geometric distribution as seen in literature
-/
def Geo (r : ENNReal) : SLang ℕ := (fun n => (1 - r) ^ n * r)

/-
``probGeometric`` in terms of ``Geo``
-/
lemma probGeometric_apply_Geo (t : SLang Bool) (trial_spec : t false + t true = 1)
  (trial_spec' : t true < 1) (x : ℕ) :
    probGeometric t x = if x = 0 then 0 else Geo (1 - t true) (x - 1) := by
  rw [probGeometric_apply]
  split <;> try simp
  rw [Geo]
  congr
  · rw [ENNReal.sub_sub_cancel] <;> try simp
    exact le_of_lt trial_spec'
  · exact trial_one_minus t trial_spec


/--
Closed for for partial geometric series
-/
lemma partial_geometric_series {p : ENNReal} (HP2 : p < 1) (B : ℕ) :
    (∑' (a : ℕ), if a < B then p ^ a else 0) = (1 - p ^ B) / (1 - p) := by
  induction B
  · simp
  · rename_i n IH
    have H (a : ℕ) D : @ite ENNReal (a < n + 1) D (p^a) 0 = (if (a < n) then p^a else 0) + (if a = n then p^a else 0):= by
      split
      · rename_i H
        split
        · split
          · exfalso
            linarith
          · simp
        · split
          · simp
          · exfalso
            apply le_of_lt_succ at H
            apply Nat.le_iff_lt_or_eq.mp at H
            cases H
            · trivial
            · trivial
      · split
        · exfalso
          linarith
        · split
          · exfalso
            linarith
          · simp
    conv =>
      enter [1, 1, a]
      rw [H]
    clear H
    rw [ENNReal.tsum_add]
    rw [IH]
    rw [tsum_eq_single n ?G1]
    case G1 =>
      intro _ _
      simp
      intro _
      trivial
    simp

    have SC1 : (1 - p) ≠ 0 := by
      apply pos_iff_ne_zero.mp
      simp_all only [tsub_pos_iff_lt]
    have SC2 : (1 - p) ≠ ⊤ := by
      apply ENNReal.sub_ne_top
      simp
    have SC3 : 0 < p → p < 1 → p ^ n ≠ ⊤ := by
      intro _ _
      apply ENNReal.pow_ne_top
      exact LT.lt.ne_top HP2

    apply (ENNReal.mul_right_inj SC1 SC2).mp
    calc
      (1 - p) * ((1 - p ^ n) / (1 - p) + p ^ n)
          = (1 - p) * ((1 - p ^ n) / (1 - p)) + (1 - p) * p ^ n := by rw [mul_add]
      _ = (1 - p ^ n) + ((1 - p) * p ^ n) := by
        rw [division_def]
        rw [show (1 - p) * ((1 - p ^ n) * (1 - p)⁻¹) = ((1 - p) * (1 - p)⁻¹) * (1 - p ^ n) by
          ac_rfl]
        rw [ENNReal.mul_inv_cancel SC1 SC2]
        simp
      _ = 1 - p ^ n + (p ^ n - p ^ n * p) := by
        rw [mul_comm (1 - p) (p ^ n)]
        rw [ENNReal.mul_sub SC3]
        simp [mul_comm]
      _ = (1 - p) * ((1 - p ^ (n + 1)) / (1 - p)) := by
        have hpow : p ^ n * p = p ^ (n + 1) := by
          rw [_root_.pow_succ', mul_comm]
        have hpow_le : p ^ (n + 1) ≤ p ^ n := by
          rw [← hpow]
          calc
            p ^ n * p ≤ p ^ n * 1 := by
              gcongr
            _ = p ^ n := by simp
        have hpow_n_le_one : p ^ n ≤ 1 := by
          exact pow_le_one' (le_of_lt HP2) n
        have hmain : 1 - p ^ n + (p ^ n - p ^ n * p) = 1 - p ^ (n + 1) := by
          refine (ENNReal.sub_eq_of_eq_add'
            (a := (1 : ENNReal))
            (b := p ^ (n + 1))
            (c := 1 - p ^ n + (p ^ n - p ^ n * p))
            (by simp) ?_).symm
          have hs : p ^ n - p ^ n * p = p ^ n - p ^ (n + 1) := by
            rw [hpow]
          calc
            1 = (1 - p ^ n) + p ^ n := by
              exact (tsub_add_cancel_of_le hpow_n_le_one).symm
            _ = (1 - p ^ n) + ((p ^ n - p ^ (n + 1)) + p ^ (n + 1)) := by
              rw [tsub_add_cancel_of_le hpow_le]
            _ = (1 - p ^ n + (p ^ n - p ^ (n + 1))) + p ^ (n + 1) := by
              rw [add_assoc]
            _ = (1 - p ^ n + (p ^ n - p ^ n * p)) + p ^ (n + 1) := by
              rw [hs]
        rw [hmain]
        rw [division_def]
        rw [show (1 - p) * ((1 - p ^ (n + 1)) * (1 - p)⁻¹) = ((1 - p) * (1 - p)⁻¹) * (1 - p ^ (n + 1)) by
          ac_rfl]
        rw [ENNReal.mul_inv_cancel SC1 SC2]
        simp


/--
Integer division of a geometric distribution is a geometric distribution
-/
lemma geo_div_geo (k n : ℕ) (p : ENNReal) (Hp : p < 1) (Hn : 0 < n) :
      (Geo (1-p) >>= (fun v => Pure.pure (v / n))) k = Geo (1-(p ^ n)) k := by
  rw [Geo]
  simp

  -- Convert integer division equality into integer inequalities
  have H : (∑' (a : ℕ), if k = a / n then Geo (1 - p) a else 0) =
           (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then Geo (1 - p) a else 0) := by
      apply tsum_congr
      intro b
      congr
      apply propext
      apply @nat_div_eq_le_lt_iff k b n Hn
  rw [H]
  clear H

  -- Eliminate constant factor from Geo and simplify
  conv =>
    enter [1, 1, a]
    rw [Geo]
  have H : (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then (1 - (1 - p)) ^ a * (1 - p) else 0) =
           (∑' (a : ℕ), (1 - p) * if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then p ^ a else 0) := by
    apply tsum_congr
    intro b
    split
    · rw [mul_comm]
      congr
      apply ENNReal.sub_sub_cancel
      · simp
      · exact le_of_lt Hp
    · rw [mul_zero]
  rw [H]
  clear H
  rw [ENNReal.tsum_mul_left]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply Right.pow_le_one_of_le
    exact le_of_lt Hp

  have SC1 : (1 - p) ≠ 0 := by
    apply pos_iff_ne_zero.mp
    simp_all only [tsub_pos_iff_lt]
  have SC2 : (1 - p) ≠ ⊤ := by
    apply ENNReal.sub_ne_top
    simp

  -- Rewrite to difference of partial geometric series
  have H : (∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then p ^ a else 0) =
           (∑' (a : ℕ), if a < (k + 1) * n then p ^ a else 0) -  (∑' (a : ℕ), if a < k * n then p ^ a else 0) := by
    have hbig_ne_top :
        (∑' (a : ℕ), if a < (k + 1) * n then p ^ a else 0) ≠ ⊤ := by
      rw [partial_geometric_series Hp]
      rw [division_def]
      apply ENNReal.mul_ne_top
      · apply ENNReal.sub_ne_top
        simp
      · simp [ENNReal.inv_eq_top, SC1]
    refine ENNReal.eq_sub_of_add_eq'
      (a := ∑' (a : ℕ), if ((k * n ≤ a) ∧ (a < (k + 1) * n)) then p ^ a else 0)
      (b := ∑' (a : ℕ), if a < (k + 1) * n then p ^ a else 0)
      (c := ∑' (a : ℕ), if a < k * n then p ^ a else 0)
      hbig_ne_top ?_
    rw [<- ENNReal.tsum_add]
    apply tsum_congr
    intro b
    split
    · rename_i H
      rcases H with ⟨ H1, H2 ⟩
      split
      · exfalso
        linarith
      · simp
    · rename_i HK
      simp
      split
      · split
        · trivial
        · exfalso
          linarith
      · split
        · exfalso
          apply HK
          apply And.intro
          · linarith
          · trivial
        · trivial
  rw [H]
  clear H

  -- Evaluate partial geometric series
  rw [partial_geometric_series Hp]
  rw [partial_geometric_series Hp]

  -- Conclude by simplification

  rw [ENNReal.mul_sub ?G1]
  case G1 =>
    intro _ _
    apply SC2

  conv =>
    lhs
    congr
    · rw [division_def]
      rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel SC1 SC2]
      simp
    · rw [division_def]
      rw [mul_comm]
      rw [mul_assoc]
      rw [ENNReal.inv_mul_cancel SC1 SC2]
      simp
  suffices ((1 - p ^ ((k + 1) * n) - (1 - p ^ (k * n))).toReal = ((p ^ n) ^ k * (1 - p ^ n)).toReal) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    cases this
    · trivial
    · simp_all
      rename_i HK
      rcases HK with ⟨ _ , HK ⟩
      apply ENNReal.mul_eq_top.mp at HK
      simp_all only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not, and_imp, ENNReal.sub_eq_top_iff,
        ENNReal.one_ne_top, ENNReal.pow_eq_top_iff, false_and, and_false, false_or, not_top_lt]
  simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    cases (Classical.em (p = 0))
    · rename_i H
      rw [H]
      simp
      rw [zero_pow_eq]
      split
      · rw [zero_pow_eq]
        split
        · simp
        · exfalso
          simp_all
      · simp_all
    · apply (ENNReal.sub_le_sub_iff_left ?G3 ?G4).mpr
      case G3 =>
        apply pow_le_one'
        exact le_of_lt Hp
      case G4 =>
        simp
      rw [add_mul]
      simp
      rw [pow_add]
      -- conv =>
      --   rhs
      --   rw [<- (mul_one (p^(k*n)))]
      apply ENNReal.mul_le_of_le_div'
      rw [division_def]
      rw [ENNReal.mul_inv_cancel ?G3 ?G4]
      case G3 =>
        apply ENNReal.pow_ne_zero
        trivial
      case G4 =>
        apply ENNReal.pow_ne_top
        exact LT.lt.ne_top Hp
      apply Right.pow_le_one_of_le
      exact le_of_lt Hp
  case G2 =>
    apply ENNReal.sub_ne_top
    simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  simp
  rw [ENNReal.toReal_sub_of_le ?G1 ?G2]
  case G1 =>
    apply pow_le_one'
    exact le_of_lt Hp
  case G2 => simp
  simp
  rw [mul_sub]
  simp
  congr 1
  · exact pow_mul' p.toReal k n
  · conv =>
      rhs
      rw [<- pow_mul']
    rw [<- pow_add]
    congr
    exact succ_mul k n


/--
Equivalence between sampling loops
-/
theorem DiscreteLaplaceSampleLoop_equiv (num : PNat) (den : PNat) :
  DiscreteLaplaceSampleLoop num den = DiscreteLaplaceSampleLoop' num den := by
  apply SLang.ext
  intro ⟨ b, n ⟩
  simp [DiscreteLaplaceSampleLoop_apply]
  simp only [DiscreteLaplaceSampleLoop']


  -- Evaluate the indepenent Bern(1/2) sample
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
        Pure.pure (B, (U + ↑num * (v - 1)) / ↑den)) (b, n) =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        Pure.pure ((U + ↑num * (v - 1)) / ↑den)) (n) * 2⁻¹ := by
      simp
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro x
      rw [mul_assoc]
      congr
      rw [<- ENNReal.tsum_mul_right]
      congr
      apply funext
      intro y
      split <;> try simp
      repeat rw [mul_assoc]
      by_cases hy : n = (x + ↑num * (y - 1)) / ↑den
      · cases b <;> simp [hy, mul_left_comm, mul_comm]
      · cases b <;> simp [mul_left_comm, mul_comm]
  rw [H]
  clear H
  congr

  -- Evaluate the DiscreteSampleLoopIn2 term to geometric distribution and reindex
  have H :
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← DiscreteLaplaceSampleLoopIn2 1 1
        (Pure.pure ((U + ↑num * (v - 1)) / ↑den))) n =
    (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
        let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
        (Pure.pure ((U + ↑num * v) / ↑den))) n := by
    simp only [Bind.bind, DiscreteLaplaceSampleLoopIn2_eq, bind_apply]
    apply tsum_congr
    intro a
    congr 1

    have S1 : BernoulliExpNegSample 1 1 false + BernoulliExpNegSample 1 1 true = 1 := by
      have A := BernoulliExpNegSample_normalizes 1 1
      rw [tsum_bool] at A
      assumption
    have S2 : BernoulliExpNegSample 1 1 true < 1 := by
      rw [BernoulliExpNegSample_apply_true]
      apply ENNReal.ofReal_lt_one.mpr
      apply exp_lt_one_iff.mpr
      simp
    conv =>
      enter [1, 1, b]
      rw [probGeometric_apply_Geo _ S1 S2]
    conv =>
      enter [2]
      rw [<- tsum_shift_1]
    apply tsum_congr
    intro b
    split <;> try simp
  rw [H]
  clear H

  -- Separate X and Y
  have H : (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
             let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
             Pure.pure ((U + ↑num * v) / ↑den)) =
           (DiscreteLaplaceSampleLoopIn1 num >>= fun U => do
             let v ← Geo (1 - ENNReal.ofReal (Real.exp (- 1)))
             Pure.pure ((U + ↑num * v))) >>=
           (fun X =>  Pure.pure (X / ↑den)) := by simp
  rw [H]
  clear H

  generalize HX : (do
          let U ← DiscreteLaplaceSampleLoopIn1 num
          let v ← Geo (1 - ENNReal.ofReal (Real.exp (-1)))
          Pure.pure (U + ↑num * v) : SLang ℕ) = X

  -- Fold the left hand side into Geo
  have H : ENNReal.ofReal (rexp (-(↑↑den / ↑↑num))) ^ n * (1 - ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))) =
           Geo (1 - ENNReal.ofReal (Real.exp (-((den : ℝ) / (num : ℝ))))) n := by
    rw [Geo]
    rw [ENNReal.sub_sub_cancel]
    · simp
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp
    apply div_nonneg
    · exact cast_nonneg ↑den
    · exact cast_nonneg ↑num
  rw [H]
  clear H

  -- Apply the Geo lemma
  have H : Geo (1 - ENNReal.ofReal (Real.exp (-(↑↑den / ↑↑num)))) n = Geo (1 - (ENNReal.ofReal (Real.exp (-(1 / ↑↑num)))) ^ (den : ℕ)) n := by
    congr
    suffices (ENNReal.ofReal (rexp (-(↑↑den / ↑↑num)))).toReal =
             (ENNReal.ofReal (rexp (-(1 / ↑↑num))) ^ (den : ℕ)).toReal by
      apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
      cases this
      · trivial
      · simp_all
    simp_all
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 => apply exp_nonneg
    rw [ENNReal.toReal_ofReal ?G1]
    case G1 => apply exp_nonneg
    rw [← exp_nat_mul]
    congr
    simp [division_def]
  rw [H]
  clear H
  rw [<- geo_div_geo n den (ENNReal.ofReal (Real.exp (-(1 / ↑↑num)))) ?G1 ?G2]
  case G1 =>
    apply ENNReal.ofReal_lt_one.mpr
    apply exp_lt_one_iff.mpr
    simp
  case G2 => exact PNat.pos den
  simp only [Bind.bind, Pure.pure, bind_apply, pure_apply, mul_ite, mul_one, mul_zero]
  apply tsum_congr
  intro b
  congr 1

  -- Prove that X is geometric
  rw [<- HX]
  clear HX

  -- Decompose b by Euclidean division, in order to obtain independent samples
  rcases euclidean_division b (PNat.pos num) with ⟨ bu, bv, Hbv, Hb ⟩
  rw [Hb]
  simp only [one_div, Bind.bind, Pure.pure, bind_apply, pure_apply]

  -- Evaluate the sum (as a singleton)
  conv =>
    enter [2, 1, x]
    rw [<- ENNReal.tsum_mul_left]
  rw [<- ENNReal.tsum_prod]
  rw [tsum_eq_single (bv, bu) ?G1]
  case G1 =>
    intro ⟨ b'v, b'u ⟩ Hne
    simp
    intro He
    cases (Classical.em (b'v < num))
    · rename_i Hsupport
      exfalso
      apply Hne
      have W := (euclidean_division_uniquness bv b'v bu b'u (PNat.pos num) Hbv Hsupport).mp He
      simp_all
    · rename_i Hnsupport
      left
      simp [DiscreteLaplaceSampleLoopIn1]
      simp [DiscreteLaplaceSampleLoopIn1Aux_apply_true]
      intro Hk
      exfalso
      apply Hnsupport
      apply Hk

  -- Simplify RHS
  simp
  rw [Geo]
  rw [Geo]
  rw [DiscreteLaplaceSampleLoopIn1_apply _ _ Hbv]
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp
  rw [ENNReal.sub_sub_cancel ?G1 ?G2]
  case G1 => simp
  case G2 =>
    apply ENNReal.ofReal_le_one.mpr
    apply exp_le_one_iff.mpr
    simp


  suffices ENNReal.toReal (ENNReal.ofReal (rexp (-num.val.cast⁻¹)) ^ (bv + num.val * bu) * (OfNat.ofNat 1 - ENNReal.ofReal (rexp (-num.val.cast⁻¹)))) =
           ENNReal.toReal (ENNReal.ofReal (rexp (-(ENNReal.toReal (bv.cast / num.val.cast))) * ((OfNat.ofNat 1 - rexp (-OfNat.ofNat 1 / num.val.cast)) / (OfNat.ofNat 1 - rexp (-OfNat.ofNat 1)))) *
             (ENNReal.ofReal (rexp (-OfNat.ofNat 1)) ^ bu * (OfNat.ofNat 1 - ENNReal.ofReal (rexp (-OfNat.ofNat 1))))) by
    apply (ENNReal.toReal_eq_toReal_iff _ _).mp at this
    cases this
    · trivial
    · exfalso
      simp_all
      rename_i h
      rcases h with ⟨ _ , B ⟩ | ⟨ B , _ ⟩
      · apply ENNReal.mul_eq_top.mp at B
        simp at B
        rcases B with ⟨ _ , B ⟩
        apply ENNReal.mul_eq_top.mp at B
        simp at B
      · apply ENNReal.mul_eq_top.mp at B
        simp at B

  simp_all
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply exp_nonneg
  rw [ENNReal.toReal_ofReal ?G1]
  case G1 =>
    apply mul_nonneg
    · apply exp_nonneg
    · rw [division_def]
      apply mul_nonneg
      · apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        apply div_nonpos_iff.mpr
        right
        apply And.intro
        · apply toNNReal_eq_zero.mp
          simp only [toNNReal_eq_zero, Left.neg_nonpos_iff, zero_le_one]
        · apply cast_nonneg
      · apply inv_nonneg_of_nonneg
        apply sub_nonneg.mpr
        apply exp_le_one_iff.mpr
        simp

  rw [ENNReal.toReal_ofReal ?G1]
  case G1 => apply exp_nonneg
  conv =>
    enter [2, 1, 2]
    rw [division_def]
  repeat rw [<- mul_assoc]
  rw [<- Real.exp_nat_mul]
  simp
  have H : (1 : ℝ) = OfNat.ofNat (1 : ℕ) := by rfl
  conv =>
    enter [2]
    rw [mul_assoc]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
    rw [mul_assoc]
    enter [2]
    rw [H]
  rw [mul_inv_cancel₀ ?G1]
  case G1 =>
    apply sub_ne_zero.mpr
    apply _root_.ne_of_gt
    apply exp_lt_one_iff.mpr
    simp
  simp
  conv =>
    enter [2]
    rw [mul_assoc]
    enter [2]
    rw [mul_comm]
  rw [H]
  rw [<- mul_assoc]
  congr
  · rw [<- Real.exp_nat_mul]
    rw [<- Real.exp_add]
    congr
    simp
    rw [div_eq_mul_inv]
    rw [← neg_add_rev]
    congr 1
    rw [add_mul]
    rw [add_comm]
    congr
    have hnum_ne_zero : (↑↑num : ℝ) ≠ 0 := by
      exact_mod_cast num.ne_zero
    calc
      (↑↑num : ℝ) * ↑bu * (↑↑num : ℝ)⁻¹ = ↑bu * ((↑↑num : ℝ) * (↑↑num : ℝ)⁻¹) := by
        ring_nf
      _ = ↑bu * 1 := by
        rw [mul_inv_cancel₀ hnum_ne_zero]
      _ = ↑bu := by
        simp
  · rw [division_def]
    simp

/--
Equivalence between discrete Laplace sampelrs
-/
lemma DiscreteLaplaceSample_equiv (num den : PNat) :
    DiscreteLaplaceSample num den = DiscreteLaplaceSampleOptimized num den := by
  rw [DiscreteLaplaceSample, DiscreteLaplaceSampleOptimized, DiscreteLaplaceSampleLoop_equiv]

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSampleOptimized_normalizes (num den : PNat) :
    ∑' x : ℤ, (DiscreteLaplaceSampleOptimized num den) x = 1 := by
  rw [<- DiscreteLaplaceSample_equiv]
  apply DiscreteLaplaceSample_normalizes

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSampleOptimized_apply (num den : PNat) (x : ℤ) :
    (DiscreteLaplaceSampleOptimized num den) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  rw [<- DiscreteLaplaceSample_equiv]
  apply DiscreteLaplaceSample_apply

/--
``SLang`` Laplace sampler is a proper distribution.
-/
@[simp]
theorem DiscreteLaplaceSampleMixed_normalizes (num den : PNat) (mix : ℕ) :
    ∑' x : ℤ, (DiscreteLaplaceSampleMixed num den mix) x = 1 := by
  rw [DiscreteLaplaceSampleMixed]
  simp only [Bind.bind, Pure.pure, bind_pure]
  split
  · exact DiscreteLaplaceSample_normalizes num den
  · exact DiscreteLaplaceSampleOptimized_normalizes num den

/--
Closed form for the evaluation of the ``SLang`` Laplace sampler.
-/
@[simp]
theorem DiscreteLaplaceSampleMixed_apply (num den : PNat) (mix : ℕ) (x : ℤ) :
    (DiscreteLaplaceSampleMixed num den mix) x = ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs x / ((num : NNReal) / (den : NNReal)))))) := by
  rw [DiscreteLaplaceSampleMixed]
  simp only [Bind.bind, Pure.pure, bind_pure]
  split
  · exact DiscreteLaplaceSample_apply num den x
  · exact DiscreteLaplaceSampleOptimized_apply num den x

/--
Equivalence between discrete Laplace sampelrs
-/
lemma DiscreteLaplaceSampleMixed_equiv (num den : PNat) (mix : ℕ) :
    DiscreteLaplaceSampleMixed num den mix = DiscreteLaplaceSample num den := by
  rw [DiscreteLaplaceSampleMixed]
  simp only [Bind.bind, Pure.pure, bind_pure]
  split
  · rfl
  · symm
    apply DiscreteLaplaceSample_equiv

end SLang
