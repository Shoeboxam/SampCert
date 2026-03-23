/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Gaussian.GaussConvergence

/-!
# Discrete Gaussian Periodicity

This file contains lemmas related to the periodicity of the ``gauss_term`` function,
as well as the sum of the ``gauss_term`` function.
-/


/--
Shifting ``gauss_term_ℝ`` is equivalent to shifting its mean.
-/
theorem shifted_gauss_mean_pos (μ σ : ℝ) (n : ℤ) (k : ℤ) :
  (gauss_term_ℝ σ μ) (((n + k) : ℤ) : ℝ) = (gauss_term_ℝ σ (μ - k)) n := by
  simp [gauss_term_ℝ, gauss_term_ℝ]
  ring_nf

/--
Shifting ``gauss_term_ℝ`` is equivalent to shifting its mean.
-/
theorem shifted_gauss_mean_neg {σ : ℝ} (μ : ℝ) (n : ℤ) (k : ℤ) :
  (gauss_term_ℝ σ μ) (((-(n + k)) : ℤ) : ℝ) = (gauss_term_ℝ σ (-(μ + k))) n := by
  simp [gauss_term_ℝ, gauss_term_ℝ]
  ring_nf

/--
``gauss_term_ℝ`` is summable under any shift.
-/
theorem shifted_gauss_summable_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((n + k) : ℤ) := by
  refine Summable.congr (gauss_convergence_nat_pos h (μ := μ - k)) ?_
  intro n
  symm
  simpa using (shifted_gauss_mean_pos μ σ (n : ℤ) k)

/--
``gauss_term_ℝ`` is summable under any shift.
-/
theorem shifted_gauss_summable_neg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  Summable fun (n : ℕ) => (gauss_term_ℝ σ μ) ((-(n + k)) : ℤ) := by
  refine Summable.congr (gauss_convergence_nat_pos h (μ := -(μ + k))) ?_
  intro n
  symm
  simpa using (shifted_gauss_mean_neg (σ := σ) μ (n : ℤ) k)

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by 1.
-/
theorem gauss_sum_1_periodic {σ : ℝ} (_h : σ ≠ 0) (μ : ℝ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + 1)) n := by
  have A : ∀ n : ℤ, (gauss_term_ℝ σ (μ + 1)) n = (gauss_term_ℝ σ μ) (n - 1) := by
    intro n
    simp [gauss_term_ℝ, gauss_term_ℝ]
    ring_nf
  let e : ℤ ≃ ℤ :=
    { toFun := fun n => n - 1
      invFun := fun n => n + 1
      left_inv := by
        intro n
        ring_nf
      right_inv := by
        intro n
        ring_nf }
  have hshift : (∑' n : ℤ, (gauss_term_ℝ σ μ) (n - 1)) = ∑' n : ℤ, (gauss_term_ℝ σ μ) n := by
    simpa [e] using (e.tsum_eq (fun n : ℤ => (gauss_term_ℝ σ μ) n))
  calc
    (∑' (n : ℤ), (gauss_term_ℝ σ μ) n)
      = ∑' (n : ℤ), (gauss_term_ℝ σ μ) (n - 1) := by
          exact hshift.symm
    _ = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + 1)) n := by
          refine tsum_congr ?_
          intro n
          symm
          exact A n

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by a positive integer.
-/
theorem shifted_gauss_sum_pos {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℕ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + k)) n := by
  revert μ
  induction k
  · simp
  · intro μ
    rename_i n IH
    simp
    rw [← add_assoc]
    rw [IH]
    rw [gauss_sum_1_periodic h]

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by a negative integer.
-/
theorem shifted_gauss_sum_neg {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℕ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ - k)) n := by
  revert μ
  induction k
  · simp
  · intro μ
    rename_i n IH
    simp
    rw [sub_add_eq_sub_sub]
    rw [IH]
    have X : μ - n = (μ - n - 1) + 1 := by
      simp
    rw [X]
    rw [← gauss_sum_1_periodic h]
    simp

/--
The sum of ``gauss_term_ℝ`` does not change when the mean shifts by any integer.
-/
theorem shifted_gauss_sum {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (k : ℤ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ (μ + k)) n := by
  cases k
  · apply shifted_gauss_sum_pos h
  · simp
    have X : ∀ a : ℕ, -(1: ℝ) + -a = - (((1 + a) : ℕ)) := by
      intro a
      simp
      ring_nf
    rw [X]
    rw [@Mathlib.Tactic.RingNF.add_neg]
    apply shifted_gauss_sum_neg h

/--
The sum of ``gauss_term_ℝ`` equals the sum of the gaussian with mean zero.
-/
theorem shifted_gauss_sum_0 {σ : ℝ} (h : σ ≠ 0) (μ : ℤ) :
  (∑' (n : ℤ), (gauss_term_ℝ σ μ) n) = ∑' (n : ℤ), (gauss_term_ℝ σ 0) n := by
  have X := shifted_gauss_sum h 0 μ
  rw [X]
  simp
