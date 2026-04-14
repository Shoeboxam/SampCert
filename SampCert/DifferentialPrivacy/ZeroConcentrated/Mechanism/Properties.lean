/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code

/-!
# ``privNoisedQuery`` Implementation

This file proves differential privacy for ``privNoisedQuery``.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang


/--
The zCDP mechanism with bounded sensitivity satisfies a
`((ε₁ / ε₂)^2 / 2)`-zCDP bound.
-/
theorem privNoisedQuery_zCDPBound (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDPBound (privNoisedQuery query Δ ε₁ ε₂)
    ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  simp [zCDPBound, privNoisedQuery]
  intros α h1 l₁ l₂ h2
  have A := @discrete_GaussianGenSample_ZeroConcentrated α h1 (Δ * ε₂) ε₁ (query l₁) (query l₂)
  apply le_trans A
  clear A

  -- Turn it into an equality ASAP
  rw [sensitivity] at bounded_sensitivity
  have bounded_sensitivity := bounded_sensitivity l₁ l₂ h2
  have X :
    (ENNReal.ofReal α *
      (ENNReal.ofReal ((query l₁ - query l₂).cast ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) ≤
  (ENNReal.ofReal α *
      (ENNReal.ofReal (Δ ^ OfNat.ofNat 2) /
        (OfNat.ofNat 2 * (ofNNReal (NNReal.ofPNat (Δ * ε₂)) / ofNNReal (NNReal.ofPNat ε₁)) ^ OfNat.ofNat 2))) := by
      refine (ENNReal.mul_le_mul_iff_right ?G1 ?G2).mpr ?G3
      case G1 =>
        intro HK
        simp_all
        linarith
      case G2 => exact ofReal_ne_top
      refine ENNReal.div_le_div ?G4 ?G5
      case G5 => rfl
      apply ofReal_le_ofReal
      refine sq_le_sq.mpr ?G4.h.a
      simp only [NNReal.ofPNat, Nonneg.mk_natCast]
      have X1 : (query l₁ - query l₂).natAbs ≤ (Δ : ℕ) := by
        simpa using bounded_sensitivity
      have X2 : (((query l₁ - query l₂).natAbs : ℕ) : ℝ) ≤ (((Δ : ℕ) : ℝ)) := by
        exact_mod_cast X1
      simpa [Int.cast_sub] using X2
  apply le_trans
  · apply X
  clear X
  apply Eq.le
  rw [ENNReal.ofReal_mul ?G1]
  case G1 =>
    positivity
  rw [ENNReal.ofReal_mul ?G1]
  case G1 => simp
  rw [mul_comm]
  congr
  repeat rw [division_def]
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 => left ; simp
  case G2 => left ; simp
  simp
  rw [mul_comm]
  repeat rw [mul_assoc]
  congr
  · apply (ENNReal.toReal_eq_toReal_iff' (by
      apply ENNReal.mul_ne_top
      · apply ENNReal.inv_ne_top.mpr
        apply ENNReal.pow_ne_zero
        apply mul_ne_zero
        · exact ENNReal.coe_ne_zero.mpr (show ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal)) ≠ 0 by simp)
        · exact ENNReal.inv_ne_zero.mpr (by simp)
      · simp) (by simp)).mp
    have hnonneg : 0 ≤ ((((ε₁ : ℕ+) : ℝ) * (((ε₂ : ℕ+) : ℝ)⁻¹)) ^ 2) := by
      positivity
    have htoReal :
        (ENNReal.ofReal ((((ε₁ : ℕ+) : ℝ) * (((ε₂ : ℕ+) : ℝ)⁻¹)) ^ 2)).toReal =
          ((((ε₁ : ℕ+) : ℝ) * (((ε₂ : ℕ+) : ℝ)⁻¹)) ^ 2) := by
      simpa using (ENNReal.toReal_ofReal hnonneg)
    have hΔ : ((Δ : ℕ+) : ℝ) ≠ 0 := by
      have hΔgt : (0 : ℝ) < (Δ : ℝ) := by
        have hΔgt' : (0 : NNReal) < NNReal.ofPNat Δ := by
          change (0 : NNReal) < (((Δ : ℕ) : NNReal))
          exact_mod_cast Δ.2
        exact_mod_cast hΔgt'
      linarith
    have hΔε₂ : ((Δ * ε₂ : ℕ+) : ℝ) ≠ 0 := by
      have hΔε₂gt : (0 : ℝ) < ((Δ * ε₂ : ℕ+) : ℝ) := by
        have hΔε₂gt' : (0 : NNReal) < NNReal.ofPNat (Δ * ε₂) := by
          change (0 : NNReal) < ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal))
          exact_mod_cast (Δ * ε₂).2
        exact_mod_cast hΔε₂gt'
      linarith
    have hε₁ : ((ε₁ : ℕ+) : ℝ) ≠ 0 := by
      have hε₁gt : (0 : ℝ) < (ε₁ : ℝ) := by
        have hε₁gt' : (0 : NNReal) < NNReal.ofPNat ε₁ := by
          change (0 : NNReal) < (((ε₁ : ℕ) : NNReal))
          exact_mod_cast ε₁.2
        exact_mod_cast hε₁gt'
      linarith
    have hε₂ : ((ε₂ : ℕ+) : ℝ) ≠ 0 := by
      have hε₂gt : (0 : ℝ) < (ε₂ : ℝ) := by
        have hε₂gt' : (0 : NNReal) < NNReal.ofPNat ε₂ := by
          change (0 : NNReal) < (((ε₂ : ℕ) : NNReal))
          exact_mod_cast ε₂.2
        exact_mod_cast hε₂gt'
      linarith
    norm_num
    have hmul :
        (↑(NNReal.ofPNat (Δ * ε₂)) : ℝ) =
          (↑(NNReal.ofPNat Δ) : ℝ) * (↑(NNReal.ofPNat ε₂) : ℝ) := by
      change ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal) : ℝ) =
          ((((Δ : ℕ) : NNReal) : ℝ) * ((((ε₂ : ℕ) : NNReal) : ℝ)))
      norm_num
    have hmul' : (((Δ * ε₂ : ℕ+) : ℝ)) = (((Δ : ℕ+) : ℝ) * ((ε₂ : ℕ+) : ℝ)) := by
      simpa using hmul
    have hmulENN : (((Δ * ε₂ : ℕ+) : ENNReal)) = (((Δ : ℕ+) : ENNReal) * ((ε₂ : ℕ+) : ENNReal)) := by
      change ((((Δ * ε₂ : ℕ+) : ℕ) : ENNReal)) =
          ((((Δ : ℕ+) : ℕ) : ENNReal) * ((((ε₂ : ℕ+) : ℕ) : ENNReal)))
      norm_num
    have hmain := by
      change ((((((Δ * ε₂ : ℕ+) : ENNReal) * (((ε₁ : ℕ+) : ENNReal)⁻¹)) ^ (2 : ℕ))⁻¹ *
          (((Δ : ℕ+) : ENNReal) ^ (2 : ℕ))).toReal =
        ((((ε₁ : ℕ+) : ℝ) * (((ε₂ : ℕ+) : ℝ)⁻¹)) ^ 2))
      simp
      have hsimp :
          ((((Δ * ε₂ : ℕ+) : ℝ) * (((ε₁ : ℕ+) : ℝ)⁻¹)) ^ 2)⁻¹ * ((Δ : ℕ+) : ℝ) ^ 2 =
            ((ε₁ : ℕ+) : ℝ) ^ 2 * ((Δ : ℕ+) : ℝ) ^ 2 / (((Δ * ε₂ : ℕ+) : ℝ) ^ 2) := by
        field_simp [hΔ, hΔε₂, hε₁]
      have hmul_sq : (((Δ * ε₂ : ℕ+) : ℝ) ^ 2) = (((Δ : ℕ+) : ℝ) ^ 2 * ((ε₂ : ℕ+) : ℝ) ^ 2) := by
        rw [hmul']
        ring
      have hdiv :
          (((Δ : ℕ+) : ℝ) ^ 2) / (((Δ * ε₂ : ℕ+) : ℝ) ^ 2) =
            1 / (((ε₂ : ℕ+) : ℝ) ^ 2) := by
        rw [hmul_sq]
        field_simp [hΔ, hΔε₂, hε₂]
      calc
        ((((Δ * ε₂ : ℕ+) : ℝ) * (((ε₁ : ℕ+) : ℝ)⁻¹)) ^ 2)⁻¹ * ((Δ : ℕ+) : ℝ) ^ 2
            = ((ε₁ : ℕ+) : ℝ) ^ 2 * ((Δ : ℕ+) : ℝ) ^ 2 / (((Δ * ε₂ : ℕ+) : ℝ) ^ 2) := hsimp
        _
            = ((ε₁ : ℕ+) : ℝ) ^ 2 * ((((Δ : ℕ+) : ℝ) ^ 2) / (((Δ * ε₂ : ℕ+) : ℝ) ^ 2)) := by
                ring
        _ = ((ε₁ : ℕ+) : ℝ) ^ 2 * (1 / (((ε₂ : ℕ+) : ℝ) ^ 2)) := by
              rw [hdiv]
        _ = ((((ε₁ : ℕ+) : ℝ) * (((ε₂ : ℕ+) : ℝ)⁻¹)) ^ 2) := by
              ring
    simpa using (hmain.trans htoReal.symm)
lemma discrete_gaussian_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ x : ℤ) :
  discrete_gaussian σ μ (x - τ) = discrete_gaussian σ (μ + τ) (x) := by
  simp [discrete_gaussian]
  congr 1
  · simp [gauss_term_ℝ]
    congr 3
    ring_nf
  · rw [shifted_gauss_sum h]

/--
privNoisedQuery preserves absolute continuity between neighbours
-/
def privNoisedQuery_AC (query : List T -> ℤ) (Δ ε₁ ε₂ : ℕ+) : ACNeighbour (privNoisedQuery query Δ ε₁ ε₂) := by
  rw [ACNeighbour]
  intro l₁ l₂ _
  rw [AbsCts]
  intro n Hk
  exfalso
  simp [privNoisedQuery, DiscreteGaussianGenPMF, DiscreteGaussianGenSample, DFunLike.coe] at Hk
  have Hk := Hk (n - query l₂)
  simp at Hk
  have X := @discrete_gaussian_pos (Δ.val.cast * ε₂.val.cast / ε₁.val.cast) ?G1 0 (n - query l₂)
  case G1 =>
    cases Δ
    cases ε₁
    cases ε₂
    aesop
  simp at *
  linarith

/--
The zCDP mechanism is `((ε₁ / ε₂)^2 / 2)`-zCDP.
-/
theorem privNoisedQuery_zCDP (query : List T → ℤ) (Δ ε₁ ε₂ : ℕ+) (bounded_sensitivity : sensitivity query Δ) :
  zCDP (privNoisedQuery query Δ ε₁ ε₂)
    ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  simp [zCDP]
  apply And.intro
  · exact privNoisedQuery_AC query Δ ε₁ ε₂
  · simpa using privNoisedQuery_zCDPBound query Δ ε₁ ε₂ bounded_sensitivity


end SLang
