import SampCert.DifferentialPrivacy.AdditiveNoise.Regular
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing

/-!
# Thresholded key release

This file packages thresholded key release as a postprocessing layer over the
regular additive-noise vector mechanisms.

The release is extractable: sample noisy values for each key, then keep only the
key-value pairs whose noisy value exceeds the threshold.
-/

noncomputable section

open Classical

namespace SLang

variable {T ι : Type}
variable [Fintype ι] [DecidableEq ι]

/-- Release the key-value pairs whose value is at least the threshold. -/
def thresholdKeyRelease (τ : ℤ) (x : ι → ℤ) : List (ι × ℤ) :=
  (Finset.univ : Finset ι).toList.filterMap fun i =>
    let v := x i
    if τ ≤ v then some (i, v) else none

/-- Thresholded key release with regular vector discrete-Laplace noise. -/
def privThresholdKeyReleasePureVec
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  privPostProcess
    (privNoisedQueryPureVec query Δ ε₁ ε₂)
    (thresholdKeyRelease τ)

/-- Thresholded key release with regular correlated discrete-Laplace noise. -/
def privThresholdKeyReleasePureVecCorr
    [Inhabited ι]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  privPostProcess
    (privNoisedQueryPureVecCorr center query Δ ε₁ ε₂)
    (thresholdKeyRelease τ)

/-- Thresholded key release with regular vector discrete-Gaussian noise. -/
def privThresholdKeyReleaseVec
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  privPostProcess
    (privNoisedQueryVec query Δ ε₁ ε₂)
    (thresholdKeyRelease τ)

/-- Thresholded key release with regular correlated discrete-Gaussian noise. -/
def privThresholdKeyReleaseVecCorr
    [Inhabited ι]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  privPostProcess
    (privNoisedQueryVecCorr center query Δ ε₁ ε₂)
    (thresholdKeyRelease τ)

theorem privThresholdKeyReleasePureVec_DP
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularSensitivityL1 query Δ) :
    PureDP
      (privThresholdKeyReleasePureVec query Δ ε₁ ε₂ τ)
      (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  apply PureDP_PostProcess
  exact privNoisedQueryPureVec_DP query Δ ε₁ ε₂ hquery

theorem privThresholdKeyReleasePureVecCorr_DP
    [Inhabited ι]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularCorrelatedSensitivityL1 center query Δ) :
    PureDP
      (privThresholdKeyReleasePureVecCorr center query Δ ε₁ ε₂ τ)
      (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  apply PureDP_PostProcess
  exact privNoisedQueryPureVecCorr_DP center query Δ ε₁ ε₂ hquery

theorem privThresholdKeyReleaseVec_zCDP
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularSensitivityL2 query Δ) :
    zCDP
      (privThresholdKeyReleaseVec query Δ ε₁ ε₂ τ)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  apply privPostProcess_zCDP
  exact privNoisedQueryVec_zCDP query Δ ε₁ ε₂ hquery

theorem privThresholdKeyReleaseVecCorr_zCDP
    [Inhabited ι]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularCorrelatedSensitivityL2 center query Δ) :
    zCDP
      (privThresholdKeyReleaseVecCorr center query Δ ε₁ ε₂ τ)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  apply privPostProcess_zCDP
  exact privNoisedQueryVecCorr_zCDP center query Δ ε₁ ε₂ hquery

theorem privThresholdKeyReleasePureVec_ApproxDP
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularSensitivityL1 query Δ) :
    ∀ δ : NNReal,
      ApproximateDP
        (privThresholdKeyReleasePureVec query Δ ε₁ ε₂ τ)
        (((ε₁ : NNReal) / ε₂ : NNReal))
        δ := by
  intro δ
  exact ApproximateDP_of_DP _ _ (privThresholdKeyReleasePureVec_DP query Δ ε₁ ε₂ τ hquery) δ

theorem privThresholdKeyReleasePureVecCorr_ApproxDP
    [Inhabited ι]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularCorrelatedSensitivityL1 center query Δ) :
    ∀ δ : NNReal,
      ApproximateDP
        (privThresholdKeyReleasePureVecCorr center query Δ ε₁ ε₂ τ)
        (((ε₁ : NNReal) / ε₂ : NNReal))
        δ := by
  intro δ
  exact ApproximateDP_of_DP _ _
    (privThresholdKeyReleasePureVecCorr_DP center query Δ ε₁ ε₂ τ hquery) δ

theorem privThresholdKeyReleaseVec_ApproxDP
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularSensitivityL2 query Δ) :
    ∀ δ : NNReal, (0 < (δ : ℝ)) →
      ApproximateDP
        (privThresholdKeyReleaseVec query Δ ε₁ ε₂ τ)
        ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ) ^ 2 / 2 +
          (((ε₁ : NNReal) / ε₂ : NNReal) : ℝ) *
            (2 * Real.log (1 / δ)) ^ (1 / 2 : ℝ))
        δ := by
  intro δ hδ
  rcases privThresholdKeyReleaseVec_zCDP query Δ ε₁ ε₂ τ hquery with ⟨hac, hbound⟩
  let ρ : ℝ := (((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  simpa [ρ, Real.sqrt_sq_eq_abs, abs_of_nonneg hρ, division_def, mul_assoc, mul_left_comm, mul_comm] using
    (ApproximateDP_of_zCDP _ _ (by positivity) hbound hac δ hδ)

theorem privThresholdKeyReleaseVecCorr_ApproxDP
    [Inhabited ι]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (hquery : regularCorrelatedSensitivityL2 center query Δ) :
    ∀ δ : NNReal, (0 < (δ : ℝ)) →
      ApproximateDP
        (privThresholdKeyReleaseVecCorr center query Δ ε₁ ε₂ τ)
        ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ) ^ 2 / 2 +
          (((ε₁ : NNReal) / ε₂ : NNReal) : ℝ) *
            (2 * Real.log (1 / δ)) ^ (1 / 2 : ℝ))
        δ := by
  intro δ hδ
  rcases privThresholdKeyReleaseVecCorr_zCDP center query Δ ε₁ ε₂ τ hquery with ⟨hac, hbound⟩
  let ρ : ℝ := (((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)
  have hρ : 0 ≤ ρ := by positivity
  simpa [ρ, Real.sqrt_sq_eq_abs, abs_of_nonneg hρ, division_def, mul_assoc, mul_left_comm, mul_comm] using
    (ApproximateDP_of_zCDP _ _ (by positivity) hbound hac δ hδ)

end SLang
