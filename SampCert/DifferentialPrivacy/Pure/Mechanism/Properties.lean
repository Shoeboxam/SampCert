/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Code
import SampCert.Samplers.LaplaceGen.Basic

/-!
# Properties of ``privNoisedQueryPure``

This file proves pure differential privacy for ``privNoisedQueryPure``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

lemma natAbs_to_abs (a b : ℤ) :
  (a - b).natAbs = |(a : ℝ) - (b : ℝ)| := by
  rw [Nat.cast_natAbs]
  simp only [cast_abs, Int.cast_sub]

lemma normalizing_constant_nonzero (ε₁ ε₂ Δ : ℕ+) :
  (rexp (ε₁ / (Δ * ε₂)) - 1) / (rexp (ε₁ / (Δ * ε₂)) + 1) ≠ 0 := by
  apply div_ne_zero
  · have hpos : 0 < (ε₁ : ℝ) / (Δ * ε₂) := by
      apply _root_.div_pos
      · exact_mod_cast ε₁.pos
      · exact_mod_cast mul_pos Δ.pos ε₂.pos
    have hexp : 1 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
      rw [← exp_zero]
      exact exp_lt_exp.mpr hpos
    linarith
  · have : 0 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) + 1 := by
      apply Right.add_pos_of_nonneg_of_pos
      · apply exp_nonneg
      · simp
    linarith

/--
Differential privacy bound for a ``privNoisedQueryPure``
-/
theorem privNoisedQueryPure_DP_bound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  DP (privNoisedQueryPure query Δ ε₁ ε₂) ((ε₁ : ℝ) / ε₂) := by
  rw [event_eq_singleton] at *
  simp [DP_singleton] at *
  intros l₁ l₂ neighbours x
  simp [privNoisedQueryPure]
  simp [DiscreteLaplaceGenSamplePMF]
  simp [DFunLike.coe]
  rw [← ENNReal.ofReal_div_of_pos]
  · apply ofReal_le_ofReal
    rw [division_def]
    rw [mul_inv]
    rw [← mul_assoc]
    conv =>
      left
      left
      rw [mul_assoc]
      right
      rw [mul_comm]
    conv =>
      left
      left
      rw [← mul_assoc]
      left
      rw [mul_inv_cancel₀ (normalizing_constant_nonzero ε₁ ε₂ Δ)]
    simp only [one_mul]
    rw [← division_def]
    rw [← exp_sub]
    simp only [sub_neg_eq_add, exp_le_exp]
    rw [neg_div']
    rw [← add_div]
    rw [division_def]
    let d : ℝ := ↑↑Δ * ↑↑ε₂ / ↑↑ε₁
    have hgoal : (-(|↑x - ↑(query l₁)| : ℝ) + (|↑x - ↑(query l₂)| : ℝ)) ≤ (↑↑ε₁ / ↑↑ε₂) * d := by
      have B : (ε₁ : ℝ) / ε₂ * d = Δ := by
        dsimp [d]
        ring_nf
        field_simp
      rw [B]
      clear B

      rw [add_comm]
      ring_nf
      -- Triangle inequality
      have C := abs_sub_abs_le_abs_sub ((x : ℝ) - (query l₂ : ℝ)) ((x : ℝ) - (query l₁ : ℝ))
      apply le_trans C
      clear C
      simp

      simp [sensitivity] at bounded_sensitivity
      replace bounded_sensitivity := bounded_sensitivity l₁ l₂ neighbours

      rw [← natAbs_to_abs]
      exact Nat.cast_le.mpr bounded_sensitivity
    have hd_pos : 0 < d := by
      dsimp [d]
      positivity
    have hscaled :=
      mul_le_mul_of_nonneg_right hgoal (inv_nonneg.mpr hd_pos.le)
    have hmain : (-(|↑x - ↑(query l₁)| : ℝ) + (|↑x - ↑(query l₂)| : ℝ)) * d⁻¹ ≤ ↑↑ε₁ / ↑↑ε₂ := by
      refine hscaled.trans ?_
      rw [mul_assoc, mul_inv_cancel₀ (show d ≠ 0 by linarith), mul_one]
    simpa [d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmain
  · apply _root_.mul_pos
    · apply _root_.div_pos
      · have A : 1 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) := by
          rw [← exp_zero]
          apply exp_lt_exp.mpr
          apply _root_.div_pos
          · exact_mod_cast ε₁.pos
          · exact_mod_cast mul_pos Δ.pos ε₂.pos
        linarith
      · have : 0 < rexp ((ε₁ : ℝ) / (Δ * ε₂)) + 1 := by
          apply Right.add_pos_of_nonneg_of_pos
          · apply exp_nonneg
          · simp
        linarith
    · exact exp_pos _


/--
Laplace noising mechanism ``privNoisedQueryPure`` produces a pure ``ε₁/ε₂``-DP mechanism from a Δ-sensitive query.
-/
theorem privNoisedQueryPure_DP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  PureDP (privNoisedQueryPure query Δ ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  simp [PureDP]
  apply privNoisedQueryPure_DP_bound
  apply bounded_sensitivity

end SLang
