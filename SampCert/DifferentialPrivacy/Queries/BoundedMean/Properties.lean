/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

/-!
# ``privNoisedBoundedMean`` Properties

This file proves abstract differential privacy for ``privNoisedBoundedMean``.
-/

open Classical Nat Int Real Rat

noncomputable section

namespace SLang

lemma budget_split (ε₁ ε₂ : ℕ+) :
  (ε₁ : NNReal) / (ε₂ : NNReal) = (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) + (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) := by
  have hεne : (ε₂ : NNReal) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast ε₂.pos)
  have hsplit : (((2 * ε₂ : PNat) : NNReal)⁻¹ * 2 : NNReal) = (ε₂ : NNReal)⁻¹ := by
    apply mul_right_injective₀ hεne
    calc
      (ε₂ : NNReal) * ((((2 * ε₂ : PNat) : NNReal)⁻¹ * 2 : NNReal))
        = (((2 * ε₂ : PNat) : NNReal)⁻¹) * ((2 : NNReal) * ε₂) := by ac_rfl
      _ = 1 := by
            have htwoε : (((2 * ε₂ : PNat) : NNReal)) = (2 : NNReal) * (ε₂ : NNReal) := by simp
            rw [← htwoε, inv_mul_cancel₀]
            exact ne_of_gt (by
              have : (0 : ℕ) < ↑(2 * ε₂ : PNat) := PNat.pos (2 * ε₂)
              exact_mod_cast this)
      _ = (ε₂ : NNReal) * (ε₂ : NNReal)⁻¹ := by rw [mul_inv_cancel₀ hεne]
  calc
    (ε₁ : NNReal) * (ε₂ : NNReal)⁻¹
      = (ε₁ : NNReal) * ((((2 * ε₂ : PNat) : NNReal)⁻¹) * 2) := by rw [hsplit.symm]
    _ = (ε₁ : NNReal) * ((((2 * ε₂ : PNat) : NNReal)⁻¹) + (((2 * ε₂ : PNat) : NNReal)⁻¹)) := by
          rw [mul_two]
    _ = (ε₁ : NNReal) * (((2 * ε₂ : PNat) : NNReal)⁻¹) + (ε₁ : NNReal) * (((2 * ε₂ : PNat) : NNReal)⁻¹) := by
          rw [left_distrib]

/--
DP bound for noised mean.
-/
theorem privNoisedBoundedMean_DP [dps : DPSystem ℕ] (U : ℕ+) (ε₁ ε₂ : ℕ+) :
  dps.prop (privNoisedBoundedMean U ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  unfold privNoisedBoundedMean
  rw [bind_bind_indep]
  apply dps.postprocess_prop
  rw [budget_split]
  apply dps.compose_prop
  · apply privNoisedBoundedSum_DP
  · apply privNoisedCount_DP

end SLang
