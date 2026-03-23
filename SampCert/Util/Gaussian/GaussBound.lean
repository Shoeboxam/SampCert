/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Gaussian.DiscreteGaussian
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Gauss Bound

This file contains a proof that the sum of Gaussian terms with any mean (over the integers)
is bounded above by the sum of mean-zero Gaussian terms.

The argument transforms the series into a Fourier series, and eliminates the Fourier basis functions by
bounding them above by their absolute value. This has the effect of shifting the mean to zero; since
the sum of Fourier coefficients equals the sum of mean-zero Gaussian terms. The Poisson summation formula
justifies the transformation between series of ``gauss_term_ℝ ...`` and ``𝓕 (gauss_term_ℂ ...)``.
-/

noncomputable section

open Classical Nat BigOperators Real
open FourierTransform GaussianFourier Filter Asymptotics Complex
open ContinuousMap Function

local instance : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite

/--
This is copied from MathLib; it was made private in the release of 4.10 with the suggestion that it would be
auto-generated in 4.11. It wasn't clear if it would become public again at that point.

See: https://github.com/leanprover-community/mathlib4/pull/15340
-/
theorem local_ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => Complex.ext h.1 h.2⟩

/--
The sum of any gaussian function over ℤ is bounded above by the sum of the mean-zero gaussian function over ℤ.
-/
theorem sum_gauss_term_bound {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) :
  (∑' (n : ℤ), ((gauss_term_ℝ σ μ) n)) ≤ ∑' (n : ℤ), ((gauss_term_ℝ σ 0) n) := by
  let g : ℝ → ℂ := fun x => (𝓕 (⇑(gauss_term_ℂ σ 0))) x

  have A : (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = (∑' (n : ℤ), (gauss_term_ℝ σ 0) ((- μ) + n)) := by
    refine tsum_congr ?_
    intro n
    simp [gauss_term_ℝ, sub_eq_add_neg, add_comm]

  have Sshift : Summable fun n : ℤ => gauss_term_ℝ σ 0 (-μ + n) := by
    refine Summable.congr (summable_gauss_term' h μ) ?_
    intro n
    simp [gauss_term_ℝ, sub_eq_add_neg, add_comm]

  have B : (∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)) = |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)| := by
    rw [_root_.abs_of_nonneg]
    have hμ : 0 ≤ ∑' (n : ℤ), (gauss_term_ℝ σ μ) n := sum_gauss_term_nonneg h μ
    rwa [A] at hμ

  have C : |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)| =
      ‖∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)‖ := by
    calc
      |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)| =
          ‖((((∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)) : ℝ)) : ℂ)‖ := by
            simp
      _ = ‖∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)‖ := by
            simpa using congrArg norm
              (Complex.ofReal_tsum (fun n : ℤ => (gauss_term_ℝ σ 0) (-μ + n)))

  have Pmu : (∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)) =
      ∑' (n : ℤ), g n * (_root_.fourier n) (-μ : UnitAddCircle) := by
    calc
      (∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)) =
          ∑' (n : ℤ), gauss_term_ℂ σ 0 (-μ + n) := by
            exact tsum_congr (fun n : ℤ => (gauss_term_swap σ 0 (-μ + n)).symm)
      _ = ∑' (n : ℤ), g n * (_root_.fourier n) (-μ : UnitAddCircle) := by
            simpa [g] using (poisson_gauss_term h (-μ))

  have E : ‖∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)‖ =
      ‖∑' (n : ℤ), g n * (_root_.fourier n) (-μ : UnitAddCircle)‖ := by
    exact congrArg norm Pmu

  have F : (∑' (i : ℤ), ‖g i * ((_root_.fourier i) (-μ : UnitAddCircle))‖) =
      ∑' (i : ℤ), ‖g i‖ := by
    refine tsum_congr ?_
    intro i
    rw [norm_mul]
    have X : ‖(_root_.fourier i) (-μ : UnitAddCircle)‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [X, mul_one]

  let x : ℝ := (π * σ ^ 2 * 2)⁻¹
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity

  have cpow_half_ofReal :
      (((x : ℝ) : ℂ) ^ ((2 : ℂ)⁻¹)) = (((x ^ ((2 : ℝ)⁻¹)) : ℝ) : ℂ) := by
    symm
    simpa using (Complex.ofReal_cpow hx_nonneg ((2 : ℝ)⁻¹))

  have Sg : Summable fun i : ℤ => g i := by
    simpa [g] using (summable_fourier_gauss_term h)

  have g_eq_ofReal : ∀ a : ℤ, g a =
      (((Real.exp (-2 * (π * σ * (a : ℝ)) ^ 2) / (x ^ ((2 : ℝ)⁻¹))) : ℝ) : ℂ) := by
    intro a
    have hg : g a = fourier_gauss_term σ (a : ℝ) := by
      dsimp [g]
      simpa using (congrFun (fourier_gauss_term_correspondance h) (a : ℝ))
    have hbase : (((((↑π * ↑σ ^ 2 * 2 : ℂ)⁻¹)) ^ ((2 : ℂ)⁻¹))) = (((x ^ ((2 : ℝ)⁻¹)) : ℝ) : ℂ) := by
      rw [show ((↑π * ↑σ ^ 2 * 2 : ℂ)⁻¹) = ((x : ℝ) : ℂ) by simp [x]]
      exact cpow_half_ofReal
    have hexp : (-2 * (↑π * ↑σ * (a : ℝ)) ^ 2 : ℂ) = (((-2 * (π * σ * (a : ℝ)) ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring
    calc
      g a = fourier_gauss_term σ (a : ℝ) := hg
      _ = (((Real.exp (-2 * (π * σ * (a : ℝ)) ^ 2) / (x ^ ((2 : ℝ)⁻¹))) : ℝ) : ℂ) := by
        rw [fourier_gauss_term, hbase, hexp, ← Complex.ofReal_exp, ← Complex.ofReal_div]

  have g_nonneg : ∀ a : ℤ,
      0 ≤ Real.exp (-2 * (π * σ * (a : ℝ)) ^ 2) / (x ^ ((2 : ℝ)⁻¹)) := by
    intro a
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.rpow_pos_of_pos hx_pos _))

  have g_norm : ∀ a : ℤ, (((‖g a‖ : ℝ) : ℂ)) = g a := by
    intro a
    let y : ℝ := Real.exp (-2 * (π * σ * (a : ℝ)) ^ 2) / (x ^ ((2 : ℝ)⁻¹))
    have hy : 0 ≤ y := by
      dsimp [y]
      exact g_nonneg a
    rw [g_eq_ofReal a]
    change (((‖((y : ℝ) : ℂ)‖ : ℝ) : ℂ)) = ((y : ℝ) : ℂ)
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy]

  have G : (((∑' (i : ℤ), ‖g i‖) : ℝ) : ℂ) = ∑' (i : ℤ), g i := by
    calc
      (((∑' (i : ℤ), ‖g i‖) : ℝ) : ℂ) = ∑' (i : ℤ), (((‖g i‖ : ℝ) : ℂ)) := by
        exact Complex.ofReal_tsum (fun i : ℤ => ‖g i‖)
      _ = ∑' (i : ℤ), g i := by
        exact tsum_congr g_norm

  have P0 : (∑' (n : ℤ), gauss_term_ℂ σ 0 (0 + n)) =
      ∑' (n : ℤ), g n * (_root_.fourier n) (0 : UnitAddCircle) := by
    simpa [g] using (poisson_gauss_term h 0)

  have H : (∑' (n : ℤ), g n) = ∑' (n : ℤ), (gauss_term_ℂ σ 0) n := by
    simpa [fourier_eval_zero] using P0.symm

  have I : (∑' (n : ℤ), (gauss_term_ℂ σ 0) n) = (((∑' (n : ℤ), (gauss_term_ℝ σ 0) n) : ℝ) : ℂ) := by
    calc
      (∑' (n : ℤ), (gauss_term_ℂ σ 0) n) = ∑' (n : ℤ), (((gauss_term_ℝ σ 0 n) : ℝ) : ℂ) := by
        exact tsum_congr (fun n : ℤ => gauss_term_swap σ 0 n)
      _ = (((∑' (n : ℤ), (gauss_term_ℝ σ 0) n) : ℝ) : ℂ) := by
        symm
        exact Complex.ofReal_tsum (fun n : ℤ => gauss_term_ℝ σ 0 n)

  have GI : (∑' (i : ℤ), ‖g i‖) = ∑' (n : ℤ), (gauss_term_ℝ σ 0) n := by
    have X : (((∑' (i : ℤ), ‖g i‖) : ℝ) : ℂ) = (((∑' (n : ℤ), (gauss_term_ℝ σ 0) n) : ℝ) : ℂ) := by
      calc
        (((∑' (i : ℤ), ‖g i‖) : ℝ) : ℂ) = ∑' (i : ℤ), g i := G
        _ = ∑' (n : ℤ), (gauss_term_ℂ σ 0) n := H
        _ = (((∑' (n : ℤ), (gauss_term_ℝ σ 0) n) : ℝ) : ℂ) := I
    simpa using congrArg Complex.re X

  have S : Summable fun (n : ℤ) => g n * (_root_.fourier n) (-μ : UnitAddCircle) := by
    simpa [g] using (summable_fourier_gauss_term' h μ)

  have J : ‖∑' (i : ℤ), g i * (_root_.fourier i) (-μ : UnitAddCircle)‖ ≤
      ∑' (i : ℤ), ‖g i * (_root_.fourier i) (-μ : UnitAddCircle)‖ := by
    simpa using
      (norm_tsum_le_tsum_norm (f := fun i : ℤ => g i * (_root_.fourier i) (-μ : UnitAddCircle)) S.norm)

  calc
    (∑' (n : ℤ), ((gauss_term_ℝ σ μ) n))
        = |∑' (n : ℤ), (gauss_term_ℝ σ 0) (-μ + n)| := by
          rw [A]
          exact B
    _ = ‖∑' (n : ℤ), (((gauss_term_ℝ σ 0) (-μ + n)) : ℂ)‖ := C
    _ = ‖∑' (n : ℤ), g n * (_root_.fourier n) (-μ : UnitAddCircle)‖ := E
    _ ≤ ∑' (i : ℤ), ‖g i * (_root_.fourier i) (-μ : UnitAddCircle)‖ := J
    _ = ∑' (i : ℤ), ‖g i‖ := F
    _ = ∑' (n : ℤ), ((gauss_term_ℝ σ 0) n) := GI
