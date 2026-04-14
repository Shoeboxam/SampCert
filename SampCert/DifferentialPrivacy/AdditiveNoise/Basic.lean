import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP

/-!
# Unified additive-noise privacy reductions

This file factors the outer privacy proof for additive-noise mechanisms into:

- a notion of how neighboring outputs are related by an integer witness `τ`;
- an optional admissibility condition on `τ` (for instance same-direction /
  monotone witnesses for correlated noise);
- pointwise privacy obligations for the underlying centered noise law.

The intent is to let regular vs. modular arithmetic, and correlated vs.
uncorrelated noise, vary independently while reusing the same outer proof.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure BigOperators

namespace SLang

/-- Difference semantics for an additive-noise proof, together with an optional
admissibility side-condition on witness vectors. -/
structure AdditiveNoiseSpace (U ι : Type) where
  diff : U → U → (ι → ℤ) → Prop
  admissible : (ι → ℤ) → Prop := fun _ => True

namespace AdditiveNoiseSpace

variable {U ι : Type}

/-- Strengthen an additive-noise space with an extra admissibility condition. -/
def constrain (space : AdditiveNoiseSpace U ι) (extra : (ι → ℤ) → Prop) :
    AdditiveNoiseSpace U ι where
  diff := space.diff
  admissible τ := space.admissible τ ∧ extra τ

/-- All coordinates of the witness move in the same direction. -/
def sameDirection (τ : ι → ℤ) : Prop :=
  (∀ i, 0 ≤ τ i) ∨ ∀ i, τ i ≤ 0

/-- `κ` is a common signed component contained in every coordinate of `τ`. -/
def commonComponent (κ : ℤ) (τ : ι → ℤ) : Prop :=
  (0 ≤ κ ∧ ∀ i, κ ≤ τ i) ∨ (κ ≤ 0 ∧ ∀ i, τ i ≤ κ)

/-- Witness on `Option ι` obtained by splitting off the common component `κ`. -/
def liftWitness (κ : ℤ) (τ : ι → ℤ) : Option ι → ℤ
  | none => κ
  | some i => τ i - κ

variable {T : Type} [Fintype ι]

/-- An `ℓ₁` sensitivity witness for an additive-noise space. -/
def SensitivityL1 (space : AdditiveNoiseSpace U ι)
    (query : List T → U) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ,
      (∑ i, Int.natAbs (τ i)) ≤ Δ ∧
      space.admissible τ ∧
      space.diff (query l₁) (query l₂) τ

/-- An `ℓ₂` sensitivity witness for an additive-noise space, expressed using
the squared Euclidean norm. -/
def SensitivityL2 (space : AdditiveNoiseSpace U ι)
    (query : List T → U) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ,
      (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 ∧
      space.admissible τ ∧
      space.diff (query l₁) (query l₂) τ

end AdditiveNoiseSpace

section CommonComponentBounds

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι]

lemma commonComponent_residual_natAbs_le
    (κ : ℤ) (τ : ι → ℤ)
    (hκ : AdditiveNoiseSpace.commonComponent κ τ) :
    ∀ i, Int.natAbs (τ i - κ) ≤ Int.natAbs (τ i) := by
  intro i
  rcases hκ with ⟨hk0, hkle⟩ | ⟨hk0, hkle⟩
  · have hτ0 : 0 ≤ τ i := le_trans hk0 (hkle i)
    have hres0 : 0 ≤ τ i - κ := sub_nonneg.mpr (hkle i)
    apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg hres0, Int.natAbs_of_nonneg hτ0]
    omega
  · have hτ0 : τ i ≤ 0 := le_trans (hkle i) hk0
    have hres0 : τ i - κ ≤ 0 := sub_nonpos.mpr (hkle i)
    apply Int.ofNat_le.mp
    rw [Int.ofNat_natAbs_of_nonpos hres0, Int.ofNat_natAbs_of_nonpos hτ0]
    omega

lemma commonComponent_cancel_l1
    (κ : ℤ) (τ : ι → ℤ)
    (hκ : AdditiveNoiseSpace.commonComponent κ τ) :
    Int.natAbs κ + Int.natAbs (τ default - κ) ≤ Int.natAbs (τ default) := by
  rcases hκ with ⟨hk0, hkle⟩ | ⟨hk0, hkle⟩
  · have hτ0 : 0 ≤ τ default := le_trans hk0 (hkle default)
    have hres0 : 0 ≤ τ default - κ := sub_nonneg.mpr (hkle default)
    apply Int.ofNat_le.mp
    rw [Nat.cast_add, Int.natAbs_of_nonneg hk0, Int.natAbs_of_nonneg hres0, Int.natAbs_of_nonneg hτ0]
    omega
  · have hτ0 : τ default ≤ 0 := le_trans (hkle default) hk0
    have hres0 : τ default - κ ≤ 0 := sub_nonpos.mpr (hkle default)
    apply Int.ofNat_le.mp
    rw [Nat.cast_add, Int.ofNat_natAbs_of_nonpos hk0, Int.ofNat_natAbs_of_nonpos hres0,
      Int.ofNat_natAbs_of_nonpos hτ0]
    omega

lemma commonComponent_cancel_l2
    (κ : ℤ) (τ : ι → ℤ)
    (hκ : AdditiveNoiseSpace.commonComponent κ τ) :
    (Int.natAbs κ) ^ 2 + (Int.natAbs (τ default - κ)) ^ 2 ≤ (Int.natAbs (τ default)) ^ 2 := by
  rcases hκ with ⟨hk0, hkle⟩ | ⟨hk0, hkle⟩
  · have hτ0 : 0 ≤ τ default := le_trans hk0 (hkle default)
    have hres0 : 0 ≤ τ default - κ := sub_nonneg.mpr (hkle default)
    apply Int.ofNat_le.mp
    have hkabs : ((Int.natAbs κ : ℕ) : ℤ) = κ := Int.natAbs_of_nonneg hk0
    have hresabs : ((Int.natAbs (τ default - κ) : ℕ) : ℤ) = τ default - κ :=
      Int.natAbs_of_nonneg hres0
    have hτabs : ((Int.natAbs (τ default) : ℕ) : ℤ) = τ default :=
      Int.natAbs_of_nonneg hτ0
    calc
      (((Int.natAbs κ) ^ 2 + (Int.natAbs (τ default - κ)) ^ 2 : ℕ) : ℤ)
          = κ ^ 2 + (τ default - κ) ^ 2 := by
              rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, hkabs, hresabs]
      _ ≤ τ default ^ 2 := by nlinarith [hk0, hkle default]
      _ = (((Int.natAbs (τ default)) ^ 2 : ℕ) : ℤ) := by
            rw [Nat.cast_pow, hτabs]
  · have hτ0 : τ default ≤ 0 := le_trans (hkle default) hk0
    have hres0 : τ default - κ ≤ 0 := sub_nonpos.mpr (hkle default)
    apply Int.ofNat_le.mp
    have hkabs : ((Int.natAbs κ : ℕ) : ℤ) = -κ := Int.ofNat_natAbs_of_nonpos hk0
    have hresabs : ((Int.natAbs (τ default - κ) : ℕ) : ℤ) = -(τ default - κ) :=
      Int.ofNat_natAbs_of_nonpos hres0
    have hτabs : ((Int.natAbs (τ default) : ℕ) : ℤ) = -(τ default) :=
      Int.ofNat_natAbs_of_nonpos hτ0
    calc
      (((Int.natAbs κ) ^ 2 + (Int.natAbs (τ default - κ)) ^ 2 : ℕ) : ℤ)
          = (-κ) ^ 2 + (-(τ default - κ)) ^ 2 := by
              rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, hkabs, hresabs]
      _ ≤ (-(τ default)) ^ 2 := by nlinarith [hk0, hkle default]
      _ = (((Int.natAbs (τ default)) ^ 2 : ℕ) : ℤ) := by
            rw [Nat.cast_pow, hτabs]

lemma commonComponent_l1_bound
    (κ : ℤ) (τ : ι → ℤ)
    (hκ : AdditiveNoiseSpace.commonComponent κ τ) :
    (∑ j : Option ι, Int.natAbs (AdditiveNoiseSpace.liftWitness κ τ j))
      ≤ ∑ i, Int.natAbs (τ i) := by
  classical
  have hmem : (default : ι) ∈ (Finset.univ : Finset ι) := Finset.mem_univ default
  have hsum :
      Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x - κ))
        ≤ Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x)) := by
    exact Finset.sum_le_sum (fun x hx => commonComponent_residual_natAbs_le κ τ hκ x)
  have hsplit_res :
      (∑ i : ι, Int.natAbs (τ i - κ)) =
        Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x - κ))
          + Int.natAbs (τ default - κ) := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_eq_sum_diff_singleton_add
        (s := Finset.univ) (i := default) (f := fun i : ι => Int.natAbs (τ i - κ)) hmem)
  have hsplit_tau :
      (∑ i : ι, Int.natAbs (τ i)) =
        Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x))
          + Int.natAbs (τ default) := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_eq_sum_diff_singleton_add
        (s := Finset.univ) (i := default) (f := fun i : ι => Int.natAbs (τ i)) hmem)
  have hsplit_option :
      (∑ j : Option ι, Int.natAbs (AdditiveNoiseSpace.liftWitness κ τ j)) =
        Int.natAbs κ + ∑ i : ι, Int.natAbs (τ i - κ) := by
    simpa [univ_option, AdditiveNoiseSpace.liftWitness]
  have hmain :
      Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x - κ))
          + (Int.natAbs κ + Int.natAbs (τ default - κ))
        ≤ (Finset.sum (Finset.univ.erase default) (fun x => Int.natAbs (τ x))
            + Int.natAbs (τ default)) := by
    exact Nat.add_le_add hsum (commonComponent_cancel_l1 κ τ hκ)
  rw [hsplit_option]
  rw [hsplit_res, hsplit_tau]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

lemma commonComponent_l2_bound
    (κ : ℤ) (τ : ι → ℤ)
    (hκ : AdditiveNoiseSpace.commonComponent κ τ) :
    (∑ j : Option ι, (Int.natAbs (AdditiveNoiseSpace.liftWitness κ τ j)) ^ 2)
      ≤ ∑ i, (Int.natAbs (τ i)) ^ 2 := by
  classical
  have hmem : (default : ι) ∈ (Finset.univ : Finset ι) := Finset.mem_univ default
  have hsum :
      Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x - κ)) ^ 2)
        ≤ Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x)) ^ 2) := by
    exact Finset.sum_le_sum
      (fun x hx => Nat.pow_le_pow_left (commonComponent_residual_natAbs_le κ τ hκ x) 2)
  have hsplit_res :
      (∑ i : ι, (Int.natAbs (τ i - κ)) ^ 2) =
        Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x - κ)) ^ 2)
          + (Int.natAbs (τ default - κ)) ^ 2 := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_eq_sum_diff_singleton_add
        (s := Finset.univ) (i := default) (f := fun i : ι => (Int.natAbs (τ i - κ)) ^ 2) hmem)
  have hsplit_tau :
      (∑ i : ι, (Int.natAbs (τ i)) ^ 2) =
        Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x)) ^ 2)
          + (Int.natAbs (τ default)) ^ 2 := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_eq_sum_diff_singleton_add
        (s := Finset.univ) (i := default) (f := fun i : ι => (Int.natAbs (τ i)) ^ 2) hmem)
  have hsplit_option :
      (∑ j : Option ι, (Int.natAbs (AdditiveNoiseSpace.liftWitness κ τ j)) ^ 2) =
        (Int.natAbs κ) ^ 2 + ∑ i : ι, (Int.natAbs (τ i - κ)) ^ 2 := by
    simpa [univ_option, AdditiveNoiseSpace.liftWitness]
  have hmain :
      Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x - κ)) ^ 2)
          + ((Int.natAbs κ) ^ 2 + (Int.natAbs (τ default - κ)) ^ 2)
        ≤ (Finset.sum (Finset.univ.erase default) (fun x => (Int.natAbs (τ x)) ^ 2)
            + (Int.natAbs (τ default)) ^ 2) := by
    exact Nat.add_le_add hsum (commonComponent_cancel_l2 κ τ hκ)
  rw [hsplit_option]
  rw [hsplit_res, hsplit_tau]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

end CommonComponentBounds

section Spaces

variable {ι : Type}

/-- Regular arithmetic on integer vectors: the witness is the literal
coordinatewise difference. -/
def regularSpace : AdditiveNoiseSpace (ι → ℤ) ι where
  diff μ₁ μ₂ τ := ∀ i, τ i = μ₁ i - μ₂ i

/-- Modular arithmetic on `ZMod m`-valued vectors: the witness matches the
coordinatewise difference after reduction modulo `m`. -/
def modularSpace (m : ℕ+) : AdditiveNoiseSpace (ι → ZMod m) ι where
  diff μ₁ μ₂ τ := ∀ i, ((τ i : ZMod m) = μ₁ i - μ₂ i)

/-- Regular arithmetic with the same-direction side condition used by the
correlated-noise arguments. -/
def regularMonotoneSpace : AdditiveNoiseSpace (ι → ℤ) ι :=
  (regularSpace (ι := ι)).constrain AdditiveNoiseSpace.sameDirection

/-- Modular arithmetic with the same-direction side condition used by the
correlated-noise arguments. -/
def modularMonotoneSpace (m : ℕ+) : AdditiveNoiseSpace (ι → ZMod m) ι :=
  (modularSpace (ι := ι) m).constrain AdditiveNoiseSpace.sameDirection

end Spaces

section SensitivityAliases

variable {T ι : Type} [Fintype ι]

def regularSensitivityL1 (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL1 (space := regularSpace (ι := ι)) query Δ

def regularSensitivityL2 (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL2 (space := regularSpace (ι := ι)) query Δ

def regularMonotoneSensitivityL1 (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL1 (space := regularMonotoneSpace (ι := ι)) query Δ

def regularMonotoneSensitivityL2 (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL2 (space := regularMonotoneSpace (ι := ι)) query Δ

def modularSensitivityL1
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL1 (space := modularSpace (ι := ι) m) query Δ

def modularSensitivityL2
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL2 (space := modularSpace (ι := ι) m) query Δ

def modularMonotoneSensitivityL1
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL1 (space := modularMonotoneSpace (ι := ι) m) query Δ

def modularMonotoneSensitivityL2
    (m : ℕ+) (query : List T → (ι → ZMod m)) (Δ : ℕ+) : Prop :=
  AdditiveNoiseSpace.SensitivityL2 (space := modularMonotoneSpace (ι := ι) m) query Δ

end SensitivityAliases

section GenericPrivacy

variable {T U ι : Type}
variable [Fintype ι]

/-- A query followed by an additive-noise law centered at the query output. -/
def privAdditiveQuery
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF U :=
  noise (Δ * ε₂) ε₁ (query l)

@[simp] lemma privAdditiveQuery_eq
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privAdditiveQuery noise query Δ ε₁ ε₂ l =
      noise (Δ * ε₂) ε₁ (query l) := by
  rfl

/-- Generic singleton-event DP reduction for additive-noise mechanisms. -/
theorem privAdditiveQuery_DP_singleton
    (space : AdditiveNoiseSpace U ι)
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (hnoise :
      ∀ (Δ ε₁ ε₂ : ℕ+) μ₁ μ₂ τ,
        space.admissible τ →
        (∑ i, Int.natAbs (τ i)) ≤ Δ →
        space.diff μ₁ μ₂ τ →
        ∀ r,
          noise (Δ * ε₂) ε₁ μ₁ r / noise (Δ * ε₂) ε₁ μ₂ r
            ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)))
    )
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+)
    (hquery : AdditiveNoiseSpace.SensitivityL1 (space := space) query Δ) :
    DP_singleton (privAdditiveQuery noise query Δ ε₁ ε₂)
      ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
  intro l₁ l₂ hneigh r
  rcases hquery l₁ l₂ hneigh with ⟨τ, hτ, hadm, hdiff⟩
  simpa [privAdditiveQuery_eq] using
    hnoise Δ ε₁ ε₂ (query l₁) (query l₂) τ hadm hτ hdiff r

/-- Generic pure-DP reduction for additive-noise mechanisms. -/
theorem privAdditiveQuery_DP
    (space : AdditiveNoiseSpace U ι)
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (hnoise :
      ∀ (Δ ε₁ ε₂ : ℕ+) μ₁ μ₂ τ,
        space.admissible τ →
        (∑ i, Int.natAbs (τ i)) ≤ Δ →
        space.diff μ₁ μ₂ τ →
        ∀ r,
          noise (Δ * ε₂) ε₁ μ₁ r / noise (Δ * ε₂) ε₁ μ₂ r
            ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)))
    )
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+)
    (hquery : AdditiveNoiseSpace.SensitivityL1 (space := space) query Δ) :
    PureDP (privAdditiveQuery noise query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  rw [PureDP]
  exact (event_eq_singleton _ ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))).2
    (privAdditiveQuery_DP_singleton space noise hnoise query Δ ε₁ ε₂ hquery)

/-- Absolute continuity reduction for additive-noise mechanisms. -/
def privAdditiveQuery_AC
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (hnoise : ∀ num den μ₁ μ₂, AbsCts (noise num den μ₁) (noise num den μ₂))
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+) :
    ACNeighbour (privAdditiveQuery noise query Δ ε₁ ε₂) := by
  intro l₁ l₂ _hneigh
  simpa [privAdditiveQuery_eq] using
    hnoise (Δ * ε₂) ε₁ (query l₁) (query l₂)

/-- Generic zCDP-bound reduction for additive-noise mechanisms. -/
theorem privAdditiveQuery_zCDPBound
    (space : AdditiveNoiseSpace U ι)
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (hnoise :
      ∀ α, 1 < α → ∀ (Δ ε₁ ε₂ : ℕ+) μ₁ μ₂ τ,
        space.admissible τ →
        (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 →
        space.diff μ₁ μ₂ τ →
        RenyiDivergence
          (noise (Δ * ε₂) ε₁ μ₁)
          (noise (Δ * ε₂) ε₁ μ₂)
          α
          ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α)
    )
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+)
    (hquery : AdditiveNoiseSpace.SensitivityL2 (space := space) query Δ) :
    zCDPBound (privAdditiveQuery noise query Δ ε₁ ε₂)
      ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
  intro α hα l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, hτ, hadm, hdiff⟩
  simpa [privAdditiveQuery_eq] using
    hnoise α hα Δ ε₁ ε₂ (query l₁) (query l₂) τ hadm hτ hdiff

/-- Generic zCDP reduction for additive-noise mechanisms. -/
theorem privAdditiveQuery_zCDP
    (space : AdditiveNoiseSpace U ι)
    (noise : ℕ+ → ℕ+ → U → PMF U)
    (hac : ∀ num den μ₁ μ₂, AbsCts (noise num den μ₁) (noise num den μ₂))
    (hnoise :
      ∀ α, 1 < α → ∀ (Δ ε₁ ε₂ : ℕ+) μ₁ μ₂ τ,
        space.admissible τ →
        (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 →
        space.diff μ₁ μ₂ τ →
        RenyiDivergence
          (noise (Δ * ε₂) ε₁ μ₁)
          (noise (Δ * ε₂) ε₁ μ₂)
          α
          ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α)
    )
    (query : List T → U) (Δ ε₁ ε₂ : ℕ+)
    (hquery : AdditiveNoiseSpace.SensitivityL2 (space := space) query Δ) :
    zCDP (privAdditiveQuery noise query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  refine And.intro ?_ ?_
  · exact privAdditiveQuery_AC noise hac query Δ ε₁ ε₂
  · exact privAdditiveQuery_zCDPBound space noise hnoise query Δ ε₁ ε₂ hquery

end GenericPrivacy

end SLang
