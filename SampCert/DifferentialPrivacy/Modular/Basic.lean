import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Code
import SampCert.DifferentialPrivacy.Pure.Mechanism.Properties
import SampCert.DifferentialPrivacy.AdditiveNoise.Basic
import SampCert.DifferentialPrivacy.AdditiveNoise.Regular
import SampCert.DifferentialPrivacy.Pure.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Code
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Properties
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.ConcentratedBound
import SampCert.Samplers.LaplaceGen.Basic
import SampCert.Samplers.LaplaceGen.Properties
import SampCert.Samplers.GaussianGen.Basic
import SampCert.Samplers.GaussianGen.Properties
import Mathlib.Data.ZMod.ValMinAbs

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
variable [Fintype ι]

/-- Componentwise modular difference witness with bounded modular `ℓ₁` norm. -/
def modSensitivityL1
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  modularSensitivityL1 m query Δ

/-- Componentwise modular difference witness with bounded modular `ℓ₂` norm,
expressed as a bound on the squared Euclidean norm. -/
def modSensitivityL2
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  modularSensitivityL2 m query Δ

def wrapToMod (m : ℕ+) (μ : ι → ZMod m) (z : ι → ℤ) : ι → ZMod m :=
  fun i => μ i + (z i : ZMod m)

def wrappedDiscreteLaplacePMF
    (m : ℕ+) (num den : ℕ+) (μ : ZMod m) : PMF (ZMod m) :=
  (DiscreteLaplaceGenSamplePMF num den 0).map (fun z : ℤ => μ + (z : ZMod m))

@[simp] lemma wrappedDiscreteLaplacePMF_eq_map
    (m : ℕ+) (num den : ℕ+) (μ : ZMod m) :
    wrappedDiscreteLaplacePMF m num den μ =
      (DiscreteLaplaceGenSamplePMF num den 0).map (fun z : ℤ => μ + (z : ZMod m)) := by
  rfl

def wrappedDiscreteGaussianPMF
    (m : ℕ+) (num den : ℕ+) (μ : ZMod m) : PMF (ZMod m) :=
  (DiscreteGaussianGenPMF num den 0).map (fun z : ℤ => μ + (z : ZMod m))

@[simp] lemma wrappedDiscreteGaussianPMF_eq_map
    (m : ℕ+) (num den : ℕ+) (μ : ZMod m) :
    wrappedDiscreteGaussianPMF m num den μ =
      (DiscreteGaussianGenPMF num den 0).map (fun z : ℤ => μ + (z : ZMod m)) := by
  rfl

def translateIntVecEquiv (τ : ι → ℤ) : (ι → ℤ) ≃ (ι → ℤ) where
  toFun z i := z i + τ i
  invFun z i := z i - τ i
  left_inv z := by
    funext i
    simp [sub_eq_add_neg, add_assoc]
  right_inv z := by
    funext i
    simp [sub_eq_add_neg, add_assoc]

lemma wrapToMod_translateIntVecEquiv
    (m : ℕ+) (μ₁ μ₂ : ι → ZMod m) (τ : ι → ℤ)
    (hmod : ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)) :
    (wrapToMod m μ₂) ∘ (translateIntVecEquiv τ) = wrapToMod m μ₁ := by
  funext z
  funext i
  dsimp [Function.comp, wrapToMod, translateIntVecEquiv]
  calc
    μ₂ i + (((z i + τ i : ℤ) : ZMod m)) = μ₂ i + (z i : ZMod m) + (τ i : ZMod m) := by
      simp [add_assoc]
    _ = μ₂ i + (z i : ZMod m) + (μ₁ i - μ₂ i) := by rw [hmod i]
    _ = μ₁ i + (z i : ZMod m) := by
      abel

/-- Wrapped finite-dimensional discrete-Laplace law centered at `μ`. -/
def wrappedDiscreteLaplaceVecPMF
    (m : ℕ+) (num den : ℕ+) (μ : ι → ZMod m) : PMF (ι → ZMod m) :=
  (discreteLaplaceVecPMF num den (fun _ => 0)).map (wrapToMod m μ)

/-- Wrapped finite-dimensional discrete-Gaussian law centered at `μ`. -/
def wrappedDiscreteGaussianVecPMF
    (m : ℕ+) (num den : ℕ+) (μ : ι → ZMod m) : PMF (ι → ZMod m) :=
  (discreteGaussianVecPMF num den (fun _ => 0)).map (wrapToMod m μ)

/-- Finite-dimensional modular discrete-Laplace mechanism. -/
def privNoisedQueryPureVecMod
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  (discreteLaplaceVecPMF (Δ * ε₂) ε₁ (fun _ => 0)).map (wrapToMod m (query l))

/-- Finite-dimensional modular discrete-Gaussian mechanism. -/
def privNoisedQueryVecMod
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  (discreteGaussianVecPMF (Δ * ε₂) ε₁ (fun _ => 0)).map (wrapToMod m (query l))

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
lemma discreteLaplaceVecPMF_translate
    (num den : ℕ+) (τ : ι → ℤ) :
    (discreteLaplaceVecPMF num den (fun _ => 0)).map (translateIntVecEquiv τ) =
      discreteLaplaceVecPMF num den τ := by
  classical
  ext r
  rw [map_apply_equiv (e := translateIntVecEquiv τ)]
  rw [discreteLaplaceVecPMF_apply, discreteLaplaceVecPMF_apply]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  change DiscreteLaplaceGenSample num den 0 (r i - τ i) =
    DiscreteLaplaceGenSample num den (τ i) (r i)
  rw [DiscreteLaplaceGenSample_periodic, DiscreteLaplaceGenSample_periodic]
  simp

theorem wrappedDiscreteLaplaceVec_DP_singleton
    (m : ℕ+) (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ZMod m) (τ : ι → ℤ)
    (hτ : (∑ i, Int.natAbs (τ i)) ≤ Δ)
    (hmod : ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)) :
    ∀ r : ι → ZMod m,
      wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ μ₁ r /
      wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁ μ₂ r
      ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
  classical
  let num : ℕ+ := Δ * ε₂
  let p0 : PMF (ι → ℤ) := discreteLaplaceVecPMF num ε₁ (fun _ => 0)
  let pτ : PMF (ι → ℤ) := discreteLaplaceVecPMF num ε₁ τ
  let nq : List Unit → PMF (ι → ℤ) := switchMechanism p0 pτ
  have hτneg : (∑ i, Int.natAbs (-τ i)) ≤ Δ := by
    simpa using hτ
  have hp0τ :
      ∀ x : ι → ℤ,
        p0 x / pτ x
          ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
    intro x
    simpa [p0, pτ] using
      (discreteLaplaceVec_DP_singleton
        Δ ε₁ ε₂ (fun _ => 0) τ (fun i => -τ i) hτneg (by
          intro i
          simp) x)
  have hpτ0 :
      ∀ x : ι → ℤ,
        pτ x / p0 x
          ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
    intro x
    simpa [p0, pτ] using
      (discreteLaplaceVec_DP_singleton
        Δ ε₁ ε₂ τ (fun _ => 0) τ hτ (by
          intro i
          simp) x)
  have hself :
      ∀ x : ι → ℤ,
        pτ x / pτ x
          ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
    intro x
    have hx : pτ x ≠ 0 := by
      change discreteLaplaceVecPMF num ε₁ τ x ≠ 0
      rw [discreteLaplaceVecPMF_apply]
      exact Finset.prod_ne_zero_iff.mpr
        (fun i _hi => (discreteLaplaceGenSamplePMF_pos num ε₁ (τ i) (x i)).ne')
    have hexp :
        (1 : ENNReal)
          ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
      exact (ENNReal.one_le_ofReal).2 (Real.one_le_exp (by positivity))
    have hx_top : pτ x ≠ ⊤ := pτ.apply_ne_top x
    calc
      pτ x / pτ x = 1 := ENNReal.div_self hx hx_top
      _ ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := hexp
  have hswitchPure :
      PureDP nq (((ε₁ : NNReal) / ε₂ : NNReal)) := by
    rw [PureDP, event_eq_singleton]
    intro l₁ l₂ hneigh x
    cases hneigh with
    | Addition hl₁ hl₂ =>
        rename_i a b u
        subst hl₁ hl₂
        by_cases hnil : a ++ b = []
        · simpa [nq, switchMechanism, hnil] using hp0τ x
        · have hcons : a ++ [u] ++ b ≠ [] := by simp
          simpa [nq, switchMechanism, hnil, hcons] using hself x
    | Deletion hl₁ hl₂ =>
        rename_i a u b
        subst hl₁ hl₂
        by_cases hnil : a ++ b = []
        · simpa [nq, switchMechanism, hnil] using hpτ0 x
        · have hcons : a ++ [u] ++ b ≠ [] := by simp
          simpa [nq, switchMechanism, hnil, hcons] using hself x
  have hmapτ :
      pτ.map (wrapToMod m μ₂) = wrappedDiscreteLaplaceVecPMF m num ε₁ μ₁ := by
    calc
      pτ.map (wrapToMod m μ₂)
          = ((discreteLaplaceVecPMF num ε₁ (fun _ => 0)).map (translateIntVecEquiv τ)).map
              (wrapToMod m μ₂) := by
                simpa [pτ] using congrArg (fun p => p.map (wrapToMod m μ₂))
                  (discreteLaplaceVecPMF_translate (ι := ι) num ε₁ τ).symm
      _ = (discreteLaplaceVecPMF num ε₁ (fun _ => 0)).map
            ((wrapToMod m μ₂) ∘ (translateIntVecEquiv τ)) := by
              simpa using
                (PMF.map_comp (p := discreteLaplaceVecPMF num ε₁ (fun _ => 0))
                  (f := translateIntVecEquiv τ) (g := wrapToMod m μ₂))
      _ = (discreteLaplaceVecPMF num ε₁ (fun _ => 0)).map (wrapToMod m μ₁) := by
              simp [wrapToMod_translateIntVecEquiv, hmod]
      _ = wrappedDiscreteLaplaceVecPMF m num ε₁ μ₁ := by
              rfl
  have hpost :
      PureDP
        (privPostProcess nq (wrapToMod m μ₂))
        (((ε₁ : NNReal) / ε₂ : NNReal)) := by
    simpa using
      (PureDP_PostProcess
        (f := wrapToMod m μ₂)
        nq (((ε₁ : NNReal) / ε₂ : NNReal)) hswitchPure)
  have hpost_singleton :
      DP_singleton
        (privPostProcess nq (wrapToMod m μ₂))
        ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
    exact (event_eq_singleton _ _).mp hpost
  have hneigh : Neighbour ([()] : List Unit) [] := by
    exact Neighbour.Deletion (a := []) (n := ()) (b := []) rfl rfl
  have hleft :
      privPostProcess nq (wrapToMod m μ₂) [()] =
        wrappedDiscreteLaplaceVecPMF m num ε₁ μ₁ := by
    change pτ.bind (PMF.pure ∘ wrapToMod m μ₂) = wrappedDiscreteLaplaceVecPMF m num ε₁ μ₁
    rw [PMF.bind_pure_comp]
    exact hmapτ
  have hright :
      privPostProcess nq (wrapToMod m μ₂) [] =
        wrappedDiscreteLaplaceVecPMF m num ε₁ μ₂ := by
    change p0.bind (PMF.pure ∘ wrapToMod m μ₂) = wrappedDiscreteLaplaceVecPMF m num ε₁ μ₂
    rw [PMF.bind_pure_comp]
    simp [p0, wrappedDiscreteLaplaceVecPMF]
  intro r
  have hresult := hpost_singleton [()] [] hneigh r
  rw [hleft, hright] at hresult
  exact hresult

lemma wrapToMod_preimage
    (m : ℕ+) (μ r : ι → ZMod m) :
    wrapToMod m μ (fun i => (r i - μ i).valMinAbs) = r := by
  funext i
  simp [wrapToMod, ZMod.coe_valMinAbs]

lemma wrappedDiscreteGaussianVecPMF_pos
    (m : ℕ+) (num den : ℕ+) (μ r : ι → ZMod m) :
    0 < wrappedDiscreteGaussianVecPMF m num den μ r := by
  classical
  let z : ι → ℤ := fun i => (r i - μ i).valMinAbs
  let f : (ι → ℤ) → ENNReal :=
    fun a => if r = wrapToMod m μ a then discreteGaussianVecPMF num den (fun _ => 0) a else 0
  rw [wrappedDiscreteGaussianVecPMF, PMF.map_apply]
  have hz : wrapToMod m μ z = r := by
    simpa [z] using wrapToMod_preimage (ι := ι) m μ r
  have hbase : 0 < discreteGaussianVecPMF num den (fun _ => 0) z := by
    rw [discreteGaussianVecPMF_apply]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi => (discreteGaussianGenPMF_pos num den 0 (z i)).ne')
  have hterm : 0 < f z := by
    simpa [f, hz] using hbase
  have hle : f z ≤ ∑' a, f a := ENNReal.le_tsum z
  simpa [f] using lt_of_lt_of_le hterm hle

/-- Absolute continuity for any pair of wrapped finite-dimensional
Discrete-Gaussian laws. -/
theorem wrappedDiscreteGaussianVec_AC
    (m : ℕ+) (num den : ℕ+) (μ₁ μ₂ : ι → ZMod m) :
    AbsCts (wrappedDiscreteGaussianVecPMF m num den μ₁)
      (wrappedDiscreteGaussianVecPMF m num den μ₂) := by
  intro r hr
  exfalso
  exact (wrappedDiscreteGaussianVecPMF_pos m num den μ₂ r).ne' hr

lemma discreteGaussianVecPMF_translate
    (num den : ℕ+) (τ : ι → ℤ) :
    (discreteGaussianVecPMF num den (fun _ => 0)).map (translateIntVecEquiv τ) =
      discreteGaussianVecPMF num den τ := by
  classical
  ext r
  rw [map_apply_equiv (e := translateIntVecEquiv τ)]
  rw [discreteGaussianVecPMF_apply, discreteGaussianVecPMF_apply]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  change DiscreteGaussianGenSample num den 0 (r i - τ i) =
    DiscreteGaussianGenSample num den (τ i) (r i)
  rw [DiscreteGaussianGenSample_apply, DiscreteGaussianGenSample_apply]
  have hσ : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
    have hnumNN : (0 : NNReal) < (num : NNReal) := by
      change (0 : NNReal) < ((num : ℕ) : NNReal)
      simp
    have hdenNN : (0 : NNReal) < (den : NNReal) := by
      change (0 : NNReal) < ((den : ℕ) : NNReal)
      simp
    have hnum : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnumNN
    have hden : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hdenNN
    exact ne_of_gt (div_pos hnum hden)
  simpa [Int.cast_sub] using
    congrArg ENNReal.ofReal (discrete_gaussian_shift hσ 0 (τ i) (r i))

/-- zCDP / Rényi bound for wrapped finite-dimensional discrete Gaussian under
an `ℓ₂` modular witness. -/
theorem wrappedDiscreteGaussianVec_zCDPBound_pointwise
    (m : ℕ+) (α : ℝ) (hα : 1 < α)
    (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ZMod m) (τ : ι → ℤ)
    (hτ : (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2)
    (hmod : ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)) :
    RenyiDivergence
      (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ μ₁)
      (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁ μ₂)
      α
      ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α) := by
  classical
  let num : ℕ+ := Δ * ε₂
  let p0 : PMF (ι → ℤ) := discreteGaussianVecPMF num ε₁ (fun _ => 0)
  let pτ : PMF (ι → ℤ) := discreteGaussianVecPMF num ε₁ τ
  let nq : List Unit → PMF (ι → ℤ) := switchMechanism p0 pτ
  have hτneg : (∑ i, (Int.natAbs (-τ i)) ^ 2) ≤ Δ ^ 2 := by
    simpa using hτ
  have hp0τ :
      ∀ β : ℝ, 1 < β →
        RenyiDivergence p0 pτ β
          ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * β) := by
    intro β hβ
    simpa [p0, pτ] using
      (discreteGaussianVec_zCDPBound_pointwise
        β hβ Δ ε₁ ε₂ (fun _ => 0) τ (fun i => -τ i) hτneg (by
          intro i
          simp))
  have hpτ0 :
      ∀ β : ℝ, 1 < β →
        RenyiDivergence pτ p0 β
          ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * β) := by
    intro β hβ
    simpa [p0, pτ] using
      (discreteGaussianVec_zCDPBound_pointwise
        β hβ Δ ε₁ ε₂ τ (fun _ => 0) τ hτ (by
          intro i
          simp))
  have hswitchBound :
      zCDPBound nq
        ((((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) : NNReal) : ℝ) := by
    intro β hβ l₁ l₂ hneigh
    have hbound_nonneg :
        0 ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * β) := by
      positivity
    cases hneigh with
    | Addition hl₁ hl₂ =>
        rename_i a b u
        subst hl₁ hl₂
        by_cases hnil : a ++ b = []
        · simpa [nq, switchMechanism, hnil] using hp0τ β hβ
        · have hcons : a ++ [u] ++ b ≠ [] := by simp
          have hzero : RenyiDivergence pτ pτ β = 0 := by
            exact (RenyiDivergence_aux_zero _ _ hβ (AbsCts_refl _)).mp rfl
          simp [nq, switchMechanism, hnil, hcons, hzero, hbound_nonneg]
    | Deletion hl₁ hl₂ =>
        rename_i a u b
        subst hl₁ hl₂
        by_cases hnil : a ++ b = []
        · simpa [nq, switchMechanism, hnil] using hpτ0 β hβ
        · have hcons : a ++ [u] ++ b ≠ [] := by simp
          have hzero : RenyiDivergence pτ pτ β = 0 := by
            exact (RenyiDivergence_aux_zero _ _ hβ (AbsCts_refl _)).mp rfl
          simp [nq, switchMechanism, hnil, hcons, hzero, hbound_nonneg]
  have hswitchAC :
      ACNeighbour nq := by
    exact switchMechanism_AC p0 pτ
      (discreteGaussianVec_AC num ε₁ (fun _ => 0) τ)
      (discreteGaussianVec_AC num ε₁ τ (fun _ => 0))
  have hmapτ :
      pτ.map (wrapToMod m μ₂) = wrappedDiscreteGaussianVecPMF m num ε₁ μ₁ := by
    calc
      pτ.map (wrapToMod m μ₂)
          = ((discreteGaussianVecPMF num ε₁ (fun _ => 0)).map (translateIntVecEquiv τ)).map (wrapToMod m μ₂) := by
              simpa [pτ] using congrArg (fun p => p.map (wrapToMod m μ₂))
                (discreteGaussianVecPMF_translate (ι := ι) num ε₁ τ).symm
      _ = (discreteGaussianVecPMF num ε₁ (fun _ => 0)).map ((wrapToMod m μ₂) ∘ (translateIntVecEquiv τ)) := by
              simpa using
                (PMF.map_comp (p := discreteGaussianVecPMF num ε₁ (fun _ => 0))
                  (f := translateIntVecEquiv τ) (g := wrapToMod m μ₂))
      _ = (discreteGaussianVecPMF num ε₁ (fun _ => 0)).map (wrapToMod m μ₁) := by
              simp [wrapToMod_translateIntVecEquiv, hmod]
      _ = wrappedDiscreteGaussianVecPMF m num ε₁ μ₁ := by
              rfl
  have hpost := privPostProcess_zCDPBound
    (nq := nq)
    (ε := ((((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) : NNReal) : ℝ))
    hswitchBound
    (wrapToMod m μ₂)
    hswitchAC
  have hneigh : Neighbour ([()] : List Unit) [] := by
    exact Neighbour.Deletion (a := []) (n := ()) (b := []) rfl rfl
  have hleft :
      privPostProcess nq (wrapToMod m μ₂) [()] =
        wrappedDiscreteGaussianVecPMF m num ε₁ μ₁ := by
    change pτ.bind (PMF.pure ∘ wrapToMod m μ₂) = wrappedDiscreteGaussianVecPMF m num ε₁ μ₁
    rw [PMF.bind_pure_comp]
    exact hmapτ
  have hright :
      privPostProcess nq (wrapToMod m μ₂) [] =
        wrappedDiscreteGaussianVecPMF m num ε₁ μ₂ := by
    change p0.bind (PMF.pure ∘ wrapToMod m μ₂) = wrappedDiscreteGaussianVecPMF m num ε₁ μ₂
    rw [PMF.bind_pure_comp]
    simp [p0, wrappedDiscreteGaussianVecPMF]
  have hresult := hpost α hα [()] [] hneigh
  rw [hleft, hright] at hresult
  exact hresult

section Correlated

variable [DecidableEq ι] [Inhabited ι]

def correlatedModularLift
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) :
    List T → (Option ι → ZMod m)
  | l, none => (center l : ZMod m)
  | l, some i => query l i - (center l : ZMod m)

def correlatedModularUnlift
    (m : ℕ+) (x : Option ι → ZMod m) : ι → ZMod m :=
  fun i => x (some i) + x none

def correlatedModularCombine
    (m : ℕ+) (z : ZMod m × (ι → ZMod m)) : ι → ZMod m :=
  fun i => z.2 i + z.1

def wrapModPair
    (m : ℕ+) (μ₀ : ZMod m) (μs : ι → ZMod m) :
    ℤ × (ι → ℤ) → ZMod m × (ι → ZMod m)
  | ⟨z₀, zs⟩ => (μ₀ + (z₀ : ZMod m), wrapToMod m μs zs)

@[simp] lemma wrapModPair_eq
    (m : ℕ+) (μ₀ : ZMod m) (μs : ι → ZMod m) :
    wrapModPair m μ₀ μs =
      fun z : ℤ × (ι → ℤ) => (μ₀ + (z.1 : ZMod m), wrapToMod m μs z.2) := by
  funext z
  cases z
  rfl

lemma correlatedModularUnlift_optionFunEquiv_symm
    (m : ℕ+) :
    correlatedModularUnlift m ∘ (optionFunEquiv (α := ι) (ZMod m)).symm =
      correlatedModularCombine m := by
  funext z
  funext i
  rfl

lemma wrapToMod_optionFunEquiv_symm
    (m : ℕ+) (μ : Option ι → ZMod m) :
    wrapToMod m μ ∘ (optionFunEquiv (α := ι) ℤ).symm =
      (optionFunEquiv (α := ι) (ZMod m)).symm ∘
        wrapModPair m (μ none) (fun i => μ (some i)) := by
  funext z
  cases z with
  | mk z0 zs =>
      funext j
      cases j with
      | none =>
          simp [wrapToMod, wrapModPair, optionFunEquiv]
      | some i =>
          simp [wrapToMod, wrapModPair, optionFunEquiv]

lemma wrappedDiscreteLaplaceVecPMF_option
    [DecidableEq ι]
    (m : ℕ+) (num den : ℕ+) (μ : Option ι → ZMod m) :
    wrappedDiscreteLaplaceVecPMF m num den μ =
      (prodPMF
        (wrappedDiscreteLaplacePMF m num den (μ none))
        (wrappedDiscreteLaplaceVecPMF m num den (fun i => μ (some i)))).map
        (optionFunEquiv (α := ι) (ZMod m)).symm := by
  calc
    wrappedDiscreteLaplaceVecPMF m num den μ
        = ((prodPMF
            (DiscreteLaplaceGenSamplePMF num den 0)
            (discreteLaplaceVecPMF num den (fun _ => 0))).map
            (optionFunEquiv (α := ι) ℤ).symm).map
            (wrapToMod m μ) := by
              rw [wrappedDiscreteLaplaceVecPMF, discreteLaplaceVecPMF_option]
    _ = (prodPMF
          (DiscreteLaplaceGenSamplePMF num den 0)
          (discreteLaplaceVecPMF num den (fun _ => 0))).map
          (wrapToMod m μ ∘ (optionFunEquiv (α := ι) ℤ).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteLaplaceGenSamplePMF num den 0)
                  (discreteLaplaceVecPMF num den (fun _ => 0)))
                (f := (optionFunEquiv (α := ι) ℤ).symm)
                (g := wrapToMod m μ))
    _ = (prodPMF
          (DiscreteLaplaceGenSamplePMF num den 0)
          (discreteLaplaceVecPMF num den (fun _ => 0))).map
          ((optionFunEquiv (α := ι) (ZMod m)).symm ∘
            wrapModPair m (μ none) (fun i => μ (some i))) := by
              simp [wrapToMod_optionFunEquiv_symm]
    _ = ((prodPMF
          (DiscreteLaplaceGenSamplePMF num den 0)
          (discreteLaplaceVecPMF num den (fun _ => 0))).map
          (wrapModPair m (μ none) (fun i => μ (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteLaplaceGenSamplePMF num den 0)
                  (discreteLaplaceVecPMF num den (fun _ => 0)))
                (f := wrapModPair m (μ none) (fun i => μ (some i)))
                (g := (optionFunEquiv (α := ι) (ZMod m)).symm)).symm
    _ = (prodPMF
          (wrappedDiscreteLaplacePMF m num den (μ none))
          (wrappedDiscreteLaplaceVecPMF m num den (fun i => μ (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm := by
            have hpair :
                PMF.map (wrapModPair m (μ none) (fun i => μ (some i)))
                  (prodPMF (DiscreteLaplaceGenSamplePMF num den 0)
                    (discreteLaplaceVecPMF num den (fun _ => 0))) =
                prodPMF
                  (wrappedDiscreteLaplacePMF m num den (μ none))
                  (wrappedDiscreteLaplaceVecPMF m num den (fun i => μ (some i))) := by
              simpa [wrapModPair_eq, wrappedDiscreteLaplacePMF_eq_map,
                wrappedDiscreteLaplaceVecPMF] using
                (prodPMF_map_prod
                  (p := DiscreteLaplaceGenSamplePMF num den 0)
                  (q := discreteLaplaceVecPMF num den (fun _ => 0))
                  (f := fun z₀ => μ none + (z₀ : ZMod m))
                  (g := wrapToMod m (fun i => μ (some i)))).symm
            simpa [wrappedDiscreteLaplacePMF, wrappedDiscreteLaplaceVecPMF] using
              congrArg (PMF.map ((optionFunEquiv (α := ι) (ZMod m)).symm)) hpair

lemma wrappedDiscreteGaussianVecPMF_option
    [DecidableEq ι]
    (m : ℕ+) (num den : ℕ+) (μ : Option ι → ZMod m) :
    wrappedDiscreteGaussianVecPMF m num den μ =
      (prodPMF
        (wrappedDiscreteGaussianPMF m num den (μ none))
        (wrappedDiscreteGaussianVecPMF m num den (fun i => μ (some i)))).map
        (optionFunEquiv (α := ι) (ZMod m)).symm := by
  calc
    wrappedDiscreteGaussianVecPMF m num den μ
        = ((prodPMF
            (DiscreteGaussianGenPMF num den 0)
            (discreteGaussianVecPMF num den (fun _ => 0))).map
            (optionFunEquiv (α := ι) ℤ).symm).map
            (wrapToMod m μ) := by
              rw [wrappedDiscreteGaussianVecPMF, discreteGaussianVecPMF_option]
    _ = (prodPMF
          (DiscreteGaussianGenPMF num den 0)
          (discreteGaussianVecPMF num den (fun _ => 0))).map
          (wrapToMod m μ ∘ (optionFunEquiv (α := ι) ℤ).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteGaussianGenPMF num den 0)
                  (discreteGaussianVecPMF num den (fun _ => 0)))
                (f := (optionFunEquiv (α := ι) ℤ).symm)
                (g := wrapToMod m μ))
    _ = (prodPMF
          (DiscreteGaussianGenPMF num den 0)
          (discreteGaussianVecPMF num den (fun _ => 0))).map
          ((optionFunEquiv (α := ι) (ZMod m)).symm ∘
            wrapModPair m (μ none) (fun i => μ (some i))) := by
              simp [wrapToMod_optionFunEquiv_symm]
    _ = ((prodPMF
          (DiscreteGaussianGenPMF num den 0)
          (discreteGaussianVecPMF num den (fun _ => 0))).map
          (wrapModPair m (μ none) (fun i => μ (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteGaussianGenPMF num den 0)
                  (discreteGaussianVecPMF num den (fun _ => 0)))
                (f := wrapModPair m (μ none) (fun i => μ (some i)))
                (g := (optionFunEquiv (α := ι) (ZMod m)).symm)).symm
    _ = (prodPMF
          (wrappedDiscreteGaussianPMF m num den (μ none))
          (wrappedDiscreteGaussianVecPMF m num den (fun i => μ (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm := by
            have hpair :
                PMF.map (wrapModPair m (μ none) (fun i => μ (some i)))
                  (prodPMF (DiscreteGaussianGenPMF num den 0)
                    (discreteGaussianVecPMF num den (fun _ => 0))) =
                prodPMF
                  (wrappedDiscreteGaussianPMF m num den (μ none))
                  (wrappedDiscreteGaussianVecPMF m num den (fun i => μ (some i))) := by
              simpa [wrapModPair_eq, wrappedDiscreteGaussianPMF_eq_map,
                wrappedDiscreteGaussianVecPMF] using
                (prodPMF_map_prod
                  (p := DiscreteGaussianGenPMF num den 0)
                  (q := discreteGaussianVecPMF num den (fun _ => 0))
                  (f := fun z₀ => μ none + (z₀ : ZMod m))
                  (g := wrapToMod m (fun i => μ (some i)))).symm
            simpa [wrappedDiscreteGaussianPMF, wrappedDiscreteGaussianVecPMF] using
              congrArg (PMF.map ((optionFunEquiv (α := ι) (ZMod m)).symm)) hpair

def modularCorrelatedSensitivityL1
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ, ∃ κ : ℤ,
      (∑ i, Int.natAbs (τ i)) ≤ Δ ∧
      AdditiveNoiseSpace.commonComponent κ τ ∧
      (κ = center l₁ - center l₂) ∧
      (∀ i, ((τ i : ZMod m) = query l₁ i - query l₂ i))

def modularCorrelatedSensitivityL2
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ, ∃ κ : ℤ,
      (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 ∧
      AdditiveNoiseSpace.commonComponent κ τ ∧
      (κ = center l₁ - center l₂) ∧
      (∀ i, ((τ i : ZMod m) = query l₁ i - query l₂ i))

lemma correlatedModularLift_sensitivityL1
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ : ℕ+)
    (hquery : modularCorrelatedSensitivityL1 m center query Δ) :
    modularSensitivityL1 m (correlatedModularLift m center query) Δ := by
  intro l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, κ, hτ, hcommon, hk, hdiff⟩
  have hkz : (κ : ZMod m) = (center l₁ : ZMod m) - (center l₂ : ZMod m) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod m)) hk
  refine ⟨AdditiveNoiseSpace.liftWitness κ τ, ?_, ?_, ?_⟩
  · exact le_trans (commonComponent_l1_bound κ τ hcommon) hτ
  · trivial
  · intro j
    cases j with
    | none =>
        simpa [correlatedModularLift, hk, AdditiveNoiseSpace.liftWitness]
    | some i =>
        calc
          (((AdditiveNoiseSpace.liftWitness κ τ (some i)) : ZMod m))
              = ((τ i : ℤ) : ZMod m) - (κ : ZMod m) := by
                  simp [AdditiveNoiseSpace.liftWitness, sub_eq_add_neg]
          _ = (query l₁ i - query l₂ i) - ((center l₁ : ZMod m) - (center l₂ : ZMod m)) := by
                rw [hdiff i, hkz]
          _ = (query l₁ i - (center l₁ : ZMod m)) - (query l₂ i - (center l₂ : ZMod m)) := by
                abel

lemma correlatedModularLift_sensitivityL2
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ : ℕ+)
    (hquery : modularCorrelatedSensitivityL2 m center query Δ) :
    modularSensitivityL2 m (correlatedModularLift m center query) Δ := by
  intro l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, κ, hτ, hcommon, hk, hdiff⟩
  have hkz : (κ : ZMod m) = (center l₁ : ZMod m) - (center l₂ : ZMod m) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod m)) hk
  refine ⟨AdditiveNoiseSpace.liftWitness κ τ, ?_, ?_, ?_⟩
  · exact le_trans (commonComponent_l2_bound κ τ hcommon) hτ
  · trivial
  · intro j
    cases j with
    | none =>
        simpa [correlatedModularLift, hk, AdditiveNoiseSpace.liftWitness]
    | some i =>
        calc
          (((AdditiveNoiseSpace.liftWitness κ τ (some i)) : ZMod m))
              = ((τ i : ℤ) : ZMod m) - (κ : ZMod m) := by
                  simp [AdditiveNoiseSpace.liftWitness, sub_eq_add_neg]
          _ = (query l₁ i - query l₂ i) - ((center l₁ : ZMod m) - (center l₂ : ZMod m)) := by
                rw [hdiff i, hkz]
          _ = (query l₁ i - (center l₁ : ZMod m)) - (query l₂ i - (center l₂ : ZMod m)) := by
                abel

/-- Proof helper: correlated modular finite-dimensional discrete-Laplace
mechanism as a lifted additive query followed by postprocessing. -/
private def privNoisedQueryPureVecModCorrLifted
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  privPostProcess
    (privAdditiveQuery (wrappedDiscreteLaplaceVecPMF m) (correlatedModularLift m center query) Δ ε₁ ε₂)
    (correlatedModularUnlift m)
    l

/-- Correlated modular finite-dimensional discrete-Laplace mechanism:
sample a wrapped shared scalar and a wrapped residual vector, then add them. -/
def privNoisedQueryPureVecModCorr
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  (prodPMF
    (wrappedDiscreteLaplacePMF m (Δ * ε₂) ε₁ (center l))
    (wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
      (fun i => query l i - (center l : ZMod m)))).map
    (correlatedModularCombine m)

/-- Proof helper: correlated modular finite-dimensional discrete-Gaussian
mechanism as a lifted additive query followed by postprocessing. -/
private def privNoisedQueryVecModCorrLifted
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  privPostProcess
    (privAdditiveQuery (wrappedDiscreteGaussianVecPMF m) (correlatedModularLift m center query) Δ ε₁ ε₂)
    (correlatedModularUnlift m)
    l

/-- Correlated modular finite-dimensional discrete-Gaussian mechanism:
sample a wrapped shared scalar and a wrapped residual vector, then add them. -/
def privNoisedQueryVecModCorr
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ZMod m) :=
  (prodPMF
    (wrappedDiscreteGaussianPMF m (Δ * ε₂) ε₁ (center l))
    (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
      (fun i => query l i - (center l : ZMod m)))).map
    (correlatedModularCombine m)

@[simp] private lemma privNoisedQueryPureVecModCorrLifted_eq
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) :
    privNoisedQueryPureVecModCorrLifted m center query Δ ε₁ ε₂ l =
      privNoisedQueryPureVecModCorr m center query Δ ε₁ ε₂ l := by
  calc
    privNoisedQueryPureVecModCorrLifted m center query Δ ε₁ ε₂ l
        = (wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
            (correlatedModularLift m center query l)).map
            (correlatedModularUnlift m) := by
              rw [privNoisedQueryPureVecModCorrLifted, privPostProcess]
              simpa [privAdditiveQuery] using
                (PMF.bind_pure_comp
                  (p := wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
                    (correlatedModularLift m center query l))
                  (f := correlatedModularUnlift m))
    _ = ((prodPMF
          (wrappedDiscreteLaplacePMF m (Δ * ε₂) ε₁
            ((correlatedModularLift m center query l) none))
          (wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
            (fun i => (correlatedModularLift m center query l) (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm).map
          (correlatedModularUnlift m) := by
            rw [wrappedDiscreteLaplaceVecPMF_option]
    _ = (prodPMF
          (wrappedDiscreteLaplacePMF m (Δ * ε₂) ε₁
            ((correlatedModularLift m center query l) none))
          (wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
            (fun i => (correlatedModularLift m center query l) (some i)))).map
          (correlatedModularUnlift m ∘
            (optionFunEquiv (α := ι) (ZMod m)).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (wrappedDiscreteLaplacePMF m (Δ * ε₂) ε₁
                    ((correlatedModularLift m center query l) none))
                  (wrappedDiscreteLaplaceVecPMF m (Δ * ε₂) ε₁
                    (fun i => (correlatedModularLift m center query l) (some i))))
                (f := (optionFunEquiv (α := ι) (ZMod m)).symm)
                (g := correlatedModularUnlift m))
    _ = privNoisedQueryPureVecModCorr m center query Δ ε₁ ε₂ l := by
            simp [privNoisedQueryPureVecModCorr, correlatedModularLift,
              correlatedModularUnlift_optionFunEquiv_symm]

@[simp] private lemma privNoisedQueryVecModCorrLifted_eq
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) :
    privNoisedQueryVecModCorrLifted m center query Δ ε₁ ε₂ l =
      privNoisedQueryVecModCorr m center query Δ ε₁ ε₂ l := by
  calc
    privNoisedQueryVecModCorrLifted m center query Δ ε₁ ε₂ l
        = (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
            (correlatedModularLift m center query l)).map
            (correlatedModularUnlift m) := by
              rw [privNoisedQueryVecModCorrLifted, privPostProcess]
              simpa [privAdditiveQuery] using
                (PMF.bind_pure_comp
                  (p := wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
                    (correlatedModularLift m center query l))
                  (f := correlatedModularUnlift m))
    _ = ((prodPMF
          (wrappedDiscreteGaussianPMF m (Δ * ε₂) ε₁
            ((correlatedModularLift m center query l) none))
          (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
            (fun i => (correlatedModularLift m center query l) (some i)))).map
          (optionFunEquiv (α := ι) (ZMod m)).symm).map
          (correlatedModularUnlift m) := by
            rw [wrappedDiscreteGaussianVecPMF_option]
    _ = (prodPMF
          (wrappedDiscreteGaussianPMF m (Δ * ε₂) ε₁
            ((correlatedModularLift m center query l) none))
          (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
            (fun i => (correlatedModularLift m center query l) (some i)))).map
          (correlatedModularUnlift m ∘
            (optionFunEquiv (α := ι) (ZMod m)).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (wrappedDiscreteGaussianPMF m (Δ * ε₂) ε₁
                    ((correlatedModularLift m center query l) none))
                  (wrappedDiscreteGaussianVecPMF m (Δ * ε₂) ε₁
                    (fun i => (correlatedModularLift m center query l) (some i))))
                (f := (optionFunEquiv (α := ι) (ZMod m)).symm)
                (g := correlatedModularUnlift m))
    _ = privNoisedQueryVecModCorr m center query Δ ε₁ ε₂ l := by
            simp [privNoisedQueryVecModCorr, correlatedModularLift,
              correlatedModularUnlift_optionFunEquiv_symm]

end Correlated

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
  refine privAdditiveQuery_DP_singleton
    (space := modularSpace (ι := ι) m)
    (noise := wrappedDiscreteLaplaceVecPMF m)
    ?_ query Δ ε₁ ε₂ hquery
  intro Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hmod r
  simpa using
    wrappedDiscreteLaplaceVec_DP_singleton m Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hmod r

/-- Pure DP for the finite-dimensional modular discrete-Laplace mechanism. -/
theorem privNoisedQueryPureVecMod_DP
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL1 m query Δ) :
    PureDP (privNoisedQueryPureVecMod m query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  have hdp := privAdditiveQuery_DP
    (space := modularSpace (ι := ι) m)
    (noise := wrappedDiscreteLaplaceVecPMF m)
    (hnoise := by
      intro Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hmod r
      simpa using
        wrappedDiscreteLaplaceVec_DP_singleton m Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hmod r)
    query Δ ε₁ ε₂ hquery
  simpa [privNoisedQueryPureVecMod, privAdditiveQuery] using hdp

/-- Pure DP for the finite-dimensional modular correlated discrete-Laplace
mechanism. -/
theorem privNoisedQueryPureVecModCorr_DP
    [DecidableEq ι] [Inhabited ι]
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modularCorrelatedSensitivityL1 m center query Δ) :
    PureDP (privNoisedQueryPureVecModCorr m center query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  have hlifted :
      PureDP (privNoisedQueryPureVecModCorrLifted m center query Δ ε₁ ε₂)
        (((ε₁ : NNReal) / ε₂ : NNReal)) := by
    apply PureDP_PostProcess
    exact privNoisedQueryPureVecMod_DP
      m (correlatedModularLift m center query) Δ ε₁ ε₂
      (correlatedModularLift_sensitivityL1 m center query Δ hquery)
  rw [PureDP, DP] at hlifted ⊢
  intro l₁ l₂ hneigh S
  simpa [privNoisedQueryPureVecModCorrLifted_eq] using hlifted l₁ l₂ hneigh S

/-!
## Finite-dimensional modular discrete Gaussian
-/

/-- Absolute continuity for the finite-dimensional modular
Discrete-Gaussian mechanism. -/
def privNoisedQueryVecMod_AC
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+) :
    ACNeighbour (privNoisedQueryVecMod m query Δ ε₁ ε₂) := by
  have hac := privAdditiveQuery_AC
    (noise := wrappedDiscreteGaussianVecPMF m)
    (hnoise := wrappedDiscreteGaussianVec_AC m)
    query Δ ε₁ ε₂
  simpa [privNoisedQueryVecMod, privAdditiveQuery] using hac

/-- zCDP bound for the finite-dimensional modular discrete-Gaussian mechanism. -/
theorem privNoisedQueryVecMod_zCDPBound
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL2 m query Δ) :
    zCDPBound (privNoisedQueryVecMod m query Δ ε₁ ε₂)
      ((((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) : NNReal) : ℝ) := by
  refine privAdditiveQuery_zCDPBound
    (space := modularSpace (ι := ι) m)
    (noise := wrappedDiscreteGaussianVecPMF m)
    ?_ query Δ ε₁ ε₂ hquery
  intro α hα Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hmod
  simpa using
    wrappedDiscreteGaussianVec_zCDPBound_pointwise
      m α hα Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hmod

/-- zCDP for the finite-dimensional modular discrete-Gaussian mechanism. -/
theorem privNoisedQueryVecMod_zCDP
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modSensitivityL2 m query Δ) :
    zCDP (privNoisedQueryVecMod m query Δ ε₁ ε₂)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  have hzcdp := privAdditiveQuery_zCDP
    (space := modularSpace (ι := ι) m)
    (noise := wrappedDiscreteGaussianVecPMF m)
    (hac := wrappedDiscreteGaussianVec_AC m)
    (hnoise := by
      intro α hα Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hmod
      simpa using
        wrappedDiscreteGaussianVec_zCDPBound_pointwise
          m α hα Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hmod)
    query Δ ε₁ ε₂ hquery
  simpa [privNoisedQueryVecMod, privAdditiveQuery] using hzcdp

/-- zCDP for the finite-dimensional modular correlated discrete-Gaussian
mechanism. -/
theorem privNoisedQueryVecModCorr_zCDP
    [DecidableEq ι] [Inhabited ι]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (m : ℕ+) (center : List T → ℤ) (query : List T → (ι → ZMod m)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : modularCorrelatedSensitivityL2 m center query Δ) :
    zCDP (privNoisedQueryVecModCorr m center query Δ ε₁ ε₂)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  have hlifted :
      zCDP (privNoisedQueryVecModCorrLifted m center query Δ ε₁ ε₂)
        ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
    apply privPostProcess_zCDP
    exact privNoisedQueryVecMod_zCDP
      m (correlatedModularLift m center query) Δ ε₁ ε₂
      (correlatedModularLift_sensitivityL2 m center query Δ hquery)
  rcases hlifted with ⟨hac, hbound⟩
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ hneigh
    simpa [privNoisedQueryVecModCorrLifted_eq] using hac l₁ l₂ hneigh
  · intro α hα l₁ l₂ hneigh
    simpa [privNoisedQueryVecModCorrLifted_eq] using hbound α hα l₁ l₂ hneigh

end SLang
