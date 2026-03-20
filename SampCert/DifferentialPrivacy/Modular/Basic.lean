import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Code
import SampCert.DifferentialPrivacy.Pure.Mechanism.Properties
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Properties
import SampCert.DifferentialPrivacy.ZeroConcentrated.ConcentratedBound
import SampCert.Samplers.LaplaceGen.Basic
import SampCert.Samplers.LaplaceGen.Properties
import SampCert.Samplers.GaussianGen.Basic
import SampCert.Samplers.GaussianGen.Properties

/-!
# Finite-dimensional modular discrete Laplace and Gaussian mechanisms

Queries return vectors `ι → ZMod m`, and neighboring
output differences are witnessed by integer vectors `τ : ι → ℤ`.

The intended concrete instantiation is `ι = Fin d`.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure BigOperators

namespace SLang

variable {T ι : Type}
variable [Fintype ι] [DecidableEq ι]

/-- Componentwise modular difference witness with bounded modular `ℓ₁` norm. -/
def modSensitivityL1
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ,
      (∑ i, Int.natAbs (τ i)) ≤ Δ ∧
      (∀ i, ((τ i : ZMod m) = query l₁ i - query l₂ i))

/-- Componentwise modular difference witness with bounded modular `ℓ₂` norm,
expressed as a bound on the squared Euclidean norm. -/
def modSensitivityL2
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ,
      (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 ∧
      (∀ i, ((τ i : ZMod m) = query l₁ i - query l₂ i))

/-- Abstract wrapped finite-dimensional discrete-Laplace law centered at `μ`.

Semantically, this should be the law obtained by sampling independent integer
Discrete-Laplace noises on each coordinate and reducing the shifted result
modulo `m` coordinatewise.
-/
axiom wrappedDiscreteLaplaceVecPMF
    (m : ℕ+) (num den : ℕ+) (μ : ι → ZMod m) : PMF (ι → ZMod m)

/-- Abstract wrapped finite-dimensional discrete-Gaussian law centered at `μ`.

Semantically, this should be the law obtained by sampling independent integer
Discrete-Gaussian noises on each coordinate and reducing the shifted result
modulo `m` coordinatewise.
-/
axiom wrappedDiscreteGaussianVecPMF
    (m : ℕ+) (num den : ℕ+) (μ : ι → ZMod m) : PMF (ι → ZMod m)

/-- Finite-dimensional modular discrete-Laplace mechanism. -/
def privNoisedQueryPureVecMod
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ (query l)

/-- Finite-dimensional modular discrete-Gaussian mechanism. -/
def privNoisedQueryVecMod
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ (query l)

@[simp] lemma privNoisedQueryPureVecMod_eq_wrapped
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryPureVecMod m query Δ ε₁ ε₂ l =
      wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ (query l) := by
  rfl

@[simp] lemma privNoisedQueryVecMod_eq_wrapped
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryVecMod m query Δ ε₁ ε₂ l =
      wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ (query l) := by
  rfl

/-!
## Core finite-dimensional modular proof obligations

These are the exact wrapped-law facts needed for the outer privacy theorems.
-/

/-- Singleton-event DP bound for wrapped finite-dimensional discrete Laplace
under an `ℓ₁` modular witness. -/
axiom wrappedDiscreteLaplaceVec_DP_singleton
    (m : ℕ+) (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ZMod m) (τ : ι → ℤ)
    (hτ : (∑ i, Int.natAbs (τ i)) ≤ Δ)
    (hmod : ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)) :
    ∀ r : ι → ZMod m,
      wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ μ₁ r /
        wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ μ₂ r
      ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)))

/-- Absolute continuity for any pair of wrapped finite-dimensional
Discrete-Gaussian laws. -/
axiom wrappedDiscreteGaussianVec_AC
    (m : ℕ+) (num den : ℕ+) (μ₁ μ₂ : ι → ZMod m) :
    AbsCts (wrappedDiscreteGaussianVecPMF m num den μ₁)
      (wrappedDiscreteGaussianVecPMF m num den μ₂)

/-- zCDP / Rényi bound for wrapped finite-dimensional discrete Gaussian under
an `ℓ₂` modular witness. -/
axiom wrappedDiscreteGaussianVec_zCDPBound_pointwise
    (m : ℕ+) (α : ℝ) (hα : 1 < α)
    (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ZMod m) (τ : ι → ℤ)
    (hτ : (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2)
    (hmod : ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)) :
    RenyiDivergence
      (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ μ₁)
      (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ μ₂)
      α
      ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α)

/-!
## Finite-dimensional modular discrete Laplace
-/

/-- Singleton-event DP bound for the finite-dimensional modular
Discrete-Laplace mechanism. -/
theorem privNoisedQueryPureVecMod_DP_singleton
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL1 m query Δ) :
    DP_singleton (privNoisedQueryPureVecMod m query Δ ε₁ ε₂)
      ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
  intro l₁ l₂ hneigh r
  rcases hquery l₁ l₂ hneigh with ⟨τ, hτ, hmod⟩
  simpa [privNoisedQueryPureVecMod_eq_wrapped] using
    wrappedDiscreteLaplaceVec_DP_singleton m Δ ε₁ ε₂ (query l₁) (query l₂) τ hτ hmod r

/-- Pure DP for the finite-dimensional modular discrete-Laplace mechanism. -/
theorem privNoisedQueryPureVecMod_DP
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL1 m query Δ) :
    PureDP (privNoisedQueryPureVecMod m query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  rw [PureDP]
  exact (event_eq_singleton _ ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))).2
    (privNoisedQueryPureVecMod_DP_singleton m query Δ ε₁ ε₂ hquery)

/-!
## Finite-dimensional modular discrete Gaussian
-/

/-- Absolute continuity for the finite-dimensional modular
Discrete-Gaussian mechanism. -/
def privNoisedQueryVecMod_AC
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+) :
    ACNeighbour (privNoisedQueryVecMod m query Δ ε₁ ε₂) := by
  intro l₁ l₂ _hneigh
  simpa [privNoisedQueryVecMod_eq_wrapped] using
    wrappedDiscreteGaussianVec_AC m (Δ * ε₂) ε₁ (query l₁) (query l₂)

/-- zCDP bound for the finite-dimensional modular discrete-Gaussian mechanism. -/
theorem privNoisedQueryVecMod_zCDPBound
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL2 m query Δ) :
    zCDPBound (privNoisedQueryVecMod m query Δ ε₁ ε₂)
      ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
  intro α hα l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, hτ, hmod⟩
  simpa [privNoisedQueryVecMod_eq_wrapped] using
    wrappedDiscreteGaussianVec_zCDPBound_pointwise
      m α hα Δ ε₁ ε₂ (query l₁) (query l₂) τ hτ hmod

/-- zCDP for the finite-dimensional modular discrete-Gaussian mechanism. -/
theorem privNoisedQueryVecMod_zCDP
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL2 m query Δ) :
    zCDP (privNoisedQueryVecMod m query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  refine And.intro ?_ ?_
  · exact privNoisedQueryVecMod_AC m query Δ ε₁ ε₂
  · exact privNoisedQueryVecMod_zCDPBound m query Δ ε₁ ε₂ hquery

end SLang
