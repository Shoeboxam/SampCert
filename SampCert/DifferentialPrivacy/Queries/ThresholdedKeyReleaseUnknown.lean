import SampCert.DifferentialPrivacy.AdditiveNoise.Regular
import SampCert.DifferentialPrivacy.Approximate.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Properties

/-!
# Unknown-domain thresholded key release

This file captures the proof pattern from unknown-domain key release analyses:

1. prove privacy on the "good" outputs, where no revealing keys are released;
2. bound the probability of the complementary "bad" outputs by `δ`.

Combining these yields an approximate-DP guarantee.
-/

noncomputable section

open Classical

namespace SLang

variable {T U : Type}

/-- Unknown-domain thresholding proof pattern:
privacy holds on `good` outputs, and the remaining bad mass is at most `δ`. -/
theorem ApproximateDP_of_good_output
    (m : Mechanism T U) (ε : ℝ) (δ : NNReal)
    (good : List T → List T → Set U)
    (hgood :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        ∀ S : Set U,
          S ⊆ good l₁ l₂ →
            (∑' x : U, if x ∈ S then m l₁ x else 0) ≤
              ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0))
    (hbad :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        (∑' x : U, if x ∈ (good l₁ l₂)ᶜ then m l₁ x else 0) ≤ δ) :
    ApproximateDP m ε δ := by
  rw [ApproximateDP, DP']
  intro l₁ l₂ hneigh S
  let Sgood : Set U := S ∩ good l₁ l₂
  let Sbad : Set U := S ∩ (good l₁ l₂)ᶜ
  have hsplit :
      (∑' x : U, if x ∈ S then m l₁ x else 0) =
        (∑' x : U, if x ∈ Sgood then m l₁ x else 0) +
        (∑' x : U, if x ∈ Sbad then m l₁ x else 0) := by
    calc
      (∑' x : U, if x ∈ S then m l₁ x else 0)
        = ∑' x : U, ((if x ∈ Sgood then m l₁ x else 0) + (if x ∈ Sbad then m l₁ x else 0)) := by
            apply tsum_congr
            intro x
            by_cases hxS : x ∈ S
            · by_cases hxg : x ∈ good l₁ l₂
              · simp [Sgood, Sbad, hxS, hxg]
              · simp [Sgood, Sbad, hxS, hxg]
            · simp [Sgood, Sbad, hxS]
      _ = (∑' x : U, if x ∈ Sgood then m l₁ x else 0) +
            (∑' x : U, if x ∈ Sbad then m l₁ x else 0) := by
            rw [ENNReal.tsum_add]
  have hgood' :
      (∑' x : U, if x ∈ Sgood then m l₁ x else 0) ≤
        ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ Sgood then m l₂ x else 0) := by
    simpa [Sgood] using hgood l₁ l₂ hneigh Sgood (by
      intro x hx
      exact hx.2)
  have hgood_mono :
      ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ Sgood then m l₂ x else 0) ≤
        ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0) := by
    have hsum_mono :
        (∑' x : U, if x ∈ Sgood then m l₂ x else 0) ≤
          (∑' x : U, if x ∈ S then m l₂ x else 0) := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hxSgood : x ∈ Sgood
      · have hxSgood' : x ∈ Sgood := hxSgood
        rcases hxSgood with ⟨hxS, _hxg⟩
        simp [hxSgood', hxS]
      · by_cases hxS : x ∈ S
        · simp [Sgood, hxSgood, hxS]
        · simp [Sgood, hxSgood, hxS]
    exact mul_le_mul_left' hsum_mono _
  have hbad' :
      (∑' x : U, if x ∈ Sbad then m l₁ x else 0) ≤ δ := by
    refine le_trans ?_ (hbad l₁ l₂ hneigh)
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : x ∈ Sbad
    · have hxgcompl : x ∈ (good l₁ l₂)ᶜ := hx.2
      simp [Sbad, hx, hxgcompl]
    · by_cases hxgcompl : x ∈ (good l₁ l₂)ᶜ
      · simp [Sbad, hx, hxgcompl]
      · simp [Sbad, hx, hxgcompl]
  calc
    (∑' x : U, if x ∈ S then m l₁ x else 0)
        = (∑' x : U, if x ∈ Sgood then m l₁ x else 0) +
            (∑' x : U, if x ∈ Sbad then m l₁ x else 0) := hsplit
    _ ≤ ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ Sgood then m l₂ x else 0) + δ := by
          exact add_le_add hgood' hbad'
    _ ≤ ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0) + δ := by
          exact add_le_add hgood_mono le_rfl
    _ = δ + ENNReal.ofReal (Real.exp ε) * (∑' x : U, if x ∈ S then m l₂ x else 0) := by
          rw [add_comm]

section SparseThreshold

variable {ι : Type} [DecidableEq ι]

/-- Noise and threshold a single present key. -/
def singleThresholdKeyRelease
    (noise : ℤ → PMF ℤ) (τ : ℤ) (kv : ι × ℤ) : PMF (List (ι × ℤ)) :=
  (noise kv.2).map fun z => if τ ≤ z then [(kv.1, z)] else []

/-- Thresholded key release over a sparse list of present keys. Only present keys are noised. -/
def sparseThresholdKeyReleaseWith
    (noise : ℤ → PMF ℤ) (τ : ℤ) : List (ι × ℤ) → PMF (List (ι × ℤ))
  | [] => PMF.pure []
  | kv :: xs =>
      (prodPMF (singleThresholdKeyRelease noise τ kv)
          (sparseThresholdKeyReleaseWith noise τ xs)).map (fun z => z.1 ++ z.2)

/-- Sparse thresholded key release with discrete-Laplace noise. -/
def privSparseThresholdKeyReleasePure
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  fun l => sparseThresholdKeyReleaseWith (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁) τ (query l)

/-- Sparse thresholded key release with discrete-Gaussian noise. -/
def privSparseThresholdKeyRelease
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ) :
    Mechanism T (List (ι × ℤ)) :=
  fun l => sparseThresholdKeyReleaseWith (DiscreteGaussianGenPMF (Δ * ε₂) ε₁) τ (query l)

/-- Centered upper-tail mass for the integer discrete-Laplace law. -/
def laplaceThresholdTail (num den : ℕ+) (cutoff : ℤ) : ENNReal :=
  ∑' z : ℤ, if cutoff ≤ z then DiscreteLaplaceGenSamplePMF num den 0 z else 0

/-- Centered upper-tail mass for the integer discrete-Gaussian law. -/
def gaussianThresholdTail (num den : ℕ+) (cutoff : ℤ) : ENNReal :=
  ∑' z : ℤ, if cutoff ≤ z then DiscreteGaussianGenPMF num den 0 z else 0

lemma pmf_split_lt_ge (p : PMF ℤ) (cutoff : ℤ) :
    (∑' z : ℤ, if z < cutoff then p z else 0) +
      (∑' z : ℤ, if cutoff ≤ z then p z else 0) = 1 := by
  calc
    (∑' z : ℤ, if z < cutoff then p z else 0) +
        (∑' z : ℤ, if cutoff ≤ z then p z else 0)
      = ∑' z : ℤ, ((if z < cutoff then p z else 0) + (if cutoff ≤ z then p z else 0)) := by
          rw [← ENNReal.tsum_add]
    _ = ∑' z : ℤ, p z := by
          apply tsum_congr
          intro z
          by_cases hz : z < cutoff
          · have hnot : ¬ cutoff ≤ z := by omega
            simp [hz, hnot]
          · have hge : cutoff ≤ z := by omega
            simp [hz, hge]
    _ = 1 := by simpa using PMF.tsum_coe p

lemma laplaceThresholdTail_mono {num den : ℕ+} {c₁ c₂ : ℤ} (h : c₁ ≤ c₂) :
    laplaceThresholdTail num den c₂ ≤ laplaceThresholdTail num den c₁ := by
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz₂ : c₂ ≤ z
  · have hz₁ : c₁ ≤ z := le_trans h hz₂
    simp [laplaceThresholdTail, hz₂, hz₁]
  · by_cases hz₁ : c₁ ≤ z
    · simp [laplaceThresholdTail, hz₂, hz₁]
    · simp [laplaceThresholdTail, hz₂, hz₁]

lemma gaussianThresholdTail_mono {num den : ℕ+} {c₁ c₂ : ℤ} (h : c₁ ≤ c₂) :
    gaussianThresholdTail num den c₂ ≤ gaussianThresholdTail num den c₁ := by
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz₂ : c₂ ≤ z
  · have hz₁ : c₁ ≤ z := le_trans h hz₂
    simp [gaussianThresholdTail, hz₂, hz₁]
  · by_cases hz₁ : c₁ ≤ z
    · simp [gaussianThresholdTail, hz₂, hz₁]
    · simp [gaussianThresholdTail, hz₂, hz₁]

lemma laplaceThresholdTail_shift (num den : ℕ+) (τ μ : ℤ) :
    (∑' z : ℤ, if τ ≤ z then DiscreteLaplaceGenSamplePMF num den μ z else 0) =
      laplaceThresholdTail num den (τ - μ) := by
  let f : ℤ → ENNReal := fun z => if τ ≤ z then DiscreteLaplaceGenSamplePMF num den μ z else 0
  calc
    ∑' z : ℤ, f z = ∑' z : ℤ, f (z + μ) := by
      simpa [f] using ((Equiv.addRight μ).tsum_eq (f := f)).symm
    _ = laplaceThresholdTail num den (τ - μ) := by
      apply tsum_congr
      intro z
      have hcut : τ ≤ z + μ ↔ τ - μ ≤ z := by omega
      dsimp [f, laplaceThresholdTail]
      change (if τ ≤ z + μ then DiscreteLaplaceGenSample num den μ (z + μ) else 0) =
        if τ - μ ≤ z then DiscreteLaplaceGenSample num den 0 z else 0
      rw [DiscreteLaplaceGenSample_periodic, DiscreteLaplaceGenSample_periodic]
      by_cases hz : τ - μ ≤ z
      · have hz' : τ ≤ z + μ := by omega
        simp [hz, hz']
      · have hz' : ¬ τ ≤ z + μ := by omega
        simp [hz, hz']

lemma gaussianThresholdTail_shift (num den : ℕ+) (τ μ : ℤ) :
    (∑' z : ℤ, if τ ≤ z then DiscreteGaussianGenPMF num den μ z else 0) =
      gaussianThresholdTail num den (τ - μ) := by
  let f : ℤ → ENNReal := fun z => if τ ≤ z then DiscreteGaussianGenPMF num den μ z else 0
  calc
    ∑' z : ℤ, f z = ∑' z : ℤ, f (z + μ) := by
      simpa [f] using ((Equiv.addRight μ).tsum_eq (f := f)).symm
    _ = gaussianThresholdTail num den (τ - μ) := by
      apply tsum_congr
      intro z
      dsimp [f, gaussianThresholdTail]
      have hpmf : DiscreteGaussianGenPMF num den μ (z + μ) =
          DiscreteGaussianGenPMF num den 0 z := by
        change DiscreteGaussianGenSample num den μ (z + μ) =
          DiscreteGaussianGenSample num den 0 z
        rw [DiscreteGaussianGenSample_apply, DiscreteGaussianGenSample_apply]
        have hnumNN : (0 : NNReal) < (num : NNReal) := by
          change (0 : NNReal) < ((num : ℕ) : NNReal)
          simp
        have hdenNN : (0 : NNReal) < (den : NNReal) := by
          change (0 : NNReal) < ((den : ℕ) : NNReal)
          simp
        have hnum : (0 : ℝ) < (num : ℝ) := by exact_mod_cast hnumNN
        have hden : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hdenNN
        have hσ : ((num : ℝ) / (den : ℝ)) ≠ 0 := ne_of_gt (div_pos hnum hden)
        simpa [Int.cast_add, Int.cast_sub] using
          congrArg ENNReal.ofReal (discrete_gaussian_shift hσ 0 μ (z + μ)).symm
      rw [hpmf]
      by_cases hz : τ - μ ≤ z
      · have hz' : τ ≤ z + μ := by omega
        simp [hz, hz']
      · have hz' : ¬ τ ≤ z + μ := by omega
        simp [hz, hz']

@[simp] theorem singleThresholdKeyRelease_nil
    (noise : ℤ → PMF ℤ) (τ : ℤ) (kv : ι × ℤ) :
    singleThresholdKeyRelease noise τ kv [] =
      ∑' z : ℤ, if z < τ then noise kv.2 z else 0 := by
  classical
  rw [singleThresholdKeyRelease, PMF.map_apply]
  apply tsum_congr
  intro z
  by_cases hτ : τ ≤ z
  · have hne : ([] : List (ι × ℤ)) ≠ [(kv.1, z)] := by simp
    simp [hτ, hne, not_lt.mpr hτ]
  · have hlt : z < τ := lt_of_not_ge hτ
    simp [hτ, hlt]

@[simp] theorem sparseThresholdKeyReleaseWith_nil
    (noise : ℤ → PMF ℤ) (τ : ℤ) :
    sparseThresholdKeyReleaseWith noise τ ([] : List (ι × ℤ)) [] = 1 := by
  simp [sparseThresholdKeyReleaseWith]

@[simp] theorem sparseThresholdKeyReleaseWith_cons_nil
    (noise : ℤ → PMF ℤ) (τ : ℤ) (kv : ι × ℤ) (xs : List (ι × ℤ)) :
    sparseThresholdKeyReleaseWith noise τ (kv :: xs) [] =
      singleThresholdKeyRelease noise τ kv [] * sparseThresholdKeyReleaseWith noise τ xs [] := by
  classical
  rw [sparseThresholdKeyReleaseWith, PMF.map_apply]
  rw [tsum_eq_single ([], [])]
  · simp [prodPMF_apply]
  · intro z hz
    by_cases hnil : z.1 ++ z.2 = []
    · have hz1 : z.1 = [] := (List.append_eq_nil_iff.mp hnil).1
      have hz2 : z.2 = [] := (List.append_eq_nil_iff.mp hnil).2
      rcases z with ⟨a, b⟩
      simp at hz1 hz2
      subst a
      subst b
      exact (hz rfl).elim
    · simp [hnil]

theorem sparseThresholdKeyReleaseWith_empty_prob_ge
    (noise : ℤ → PMF ℤ) (τ : ℤ) (δsingle : ENNReal) :
    ∀ xs : List (ι × ℤ),
      (∀ kv ∈ xs, (1 - δsingle) ≤ singleThresholdKeyRelease noise τ kv []) →
      (1 - δsingle) ^ xs.length ≤ sparseThresholdKeyReleaseWith noise τ xs [] := by
  intro xs
  induction xs with
  | nil =>
      intro _hdrop
      simp
  | cons kv xs ih =>
      intro hdrop
      have hhead : (1 - δsingle) ≤ singleThresholdKeyRelease noise τ kv [] := by
        exact hdrop kv (by simp)
      have htail :
          (1 - δsingle) ^ xs.length ≤ sparseThresholdKeyReleaseWith noise τ xs [] := by
        apply ih
        intro kv' hkv'
        exact hdrop kv' (List.mem_cons_of_mem _ hkv')
      calc
        (1 - δsingle) ^ (List.length xs + 1)
            = (1 - δsingle) ^ List.length xs * (1 - δsingle) := by
                rw [pow_succ]
        _ ≤ sparseThresholdKeyReleaseWith noise τ xs [] * singleThresholdKeyRelease noise τ kv [] := by
              exact mul_le_mul' htail hhead
        _ = singleThresholdKeyRelease noise τ kv [] * sparseThresholdKeyReleaseWith noise τ xs [] := by
              rw [mul_comm]
        _ = sparseThresholdKeyReleaseWith noise τ (kv :: xs) [] := by
              rw [sparseThresholdKeyReleaseWith_cons_nil]

lemma sparseThresholdKeyReleaseWith_nonempty_mass_add_empty
    (noise : ℤ → PMF ℤ) (τ : ℤ) (xs : List (ι × ℤ)) :
    sparseThresholdKeyReleaseWith noise τ xs [] +
      (∑' out : List (ι × ℤ),
        if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0) = 1 := by
  classical
  let p := sparseThresholdKeyReleaseWith noise τ xs
  calc
    p [] + (∑' out : List (ι × ℤ), if out ≠ [] then p out else 0)
        = p [] + ∑' out : List (ι × ℤ), @ite ENNReal (out = []) (propDecidable (out = [])) 0 (p out) := by
            congr 1
            apply tsum_congr
            intro out
            by_cases hout : out = []
            · subst hout
              simp
            · simp [hout]
    _ = 1 := by
          have hsplit :
              (∑' out : List (ι × ℤ), p out) =
                p [] + ∑' out : List (ι × ℤ), @ite ENNReal (out = []) (propDecidable (out = [])) 0 (p out) := by
            exact
              (ENNReal.tsum_eq_add_tsum_ite ([] : List (ι × ℤ))
                (f := fun out : List (ι × ℤ) => p out))
          have hnorm : (∑' out : List (ι × ℤ), p out) = 1 := by
            simpa [p] using PMF.tsum_coe p
          exact hsplit.symm.trans hnorm

theorem sparseThresholdKeyReleaseWith_bad_mass_le
    (noise : ℤ → PMF ℤ) (τ : ℤ) (δsingle : ENNReal) (xs : List (ι × ℤ))
    (hdrop : ∀ kv ∈ xs, (1 - δsingle) ≤ singleThresholdKeyRelease noise τ kv []) :
    (∑' out : List (ι × ℤ),
      if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0) ≤
      1 - (1 - δsingle) ^ xs.length := by
  have hempty :
      (1 - δsingle) ^ xs.length ≤ sparseThresholdKeyReleaseWith noise τ xs [] := by
    exact sparseThresholdKeyReleaseWith_empty_prob_ge noise τ δsingle xs hdrop
  have hsum :
      (1 - δsingle) ^ xs.length +
          (∑' out : List (ι × ℤ),
            if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0) ≤ 1 := by
    calc
      (1 - δsingle) ^ xs.length +
          (∑' out : List (ι × ℤ),
            if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0)
          ≤ sparseThresholdKeyReleaseWith noise τ xs [] +
              (∑' out : List (ι × ℤ),
                if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hempty
                      (∑' out : List (ι × ℤ),
                        if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0)
      _ = 1 := sparseThresholdKeyReleaseWith_nonempty_mass_add_empty noise τ xs
  have hsum' :
      (∑' out : List (ι × ℤ),
        if out ≠ [] then sparseThresholdKeyReleaseWith noise τ xs out else 0) +
          (1 - δsingle) ^ xs.length ≤ 1 := by
    simpa [add_comm, add_left_comm, add_assoc] using hsum
  exact ENNReal.le_sub_of_add_le_right (by simp) hsum'

lemma singleThresholdKeyRelease_empty_ge_laplace
    (num den : ℕ+) (τ Δinf : ℤ) (kv : ι × ℤ) (hkv : kv.2 ≤ Δinf) :
    1 - laplaceThresholdTail num den (τ - Δinf) ≤
      singleThresholdKeyRelease (DiscreteLaplaceGenSamplePMF num den) τ kv [] := by
  have hempty :
      singleThresholdKeyRelease (DiscreteLaplaceGenSamplePMF num den) τ kv [] =
        1 - laplaceThresholdTail num den (τ - kv.2) := by
    rw [singleThresholdKeyRelease_nil]
    have hsplit := pmf_split_lt_ge (DiscreteLaplaceGenSamplePMF num den kv.2) τ
    have htail :
        (∑' z : ℤ, if τ ≤ z then DiscreteLaplaceGenSamplePMF num den kv.2 z else 0) =
          laplaceThresholdTail num den (τ - kv.2) := by
      exact laplaceThresholdTail_shift num den τ kv.2
    exact ENNReal.eq_sub_of_add_eq' (by simp) (by simpa [htail, add_comm] using hsplit)
  have htail_mono :
      laplaceThresholdTail num den (τ - kv.2) ≤ laplaceThresholdTail num den (τ - Δinf) := by
    apply laplaceThresholdTail_mono
    omega
  rw [hempty]
  exact tsub_le_tsub_left htail_mono 1

lemma singleThresholdKeyRelease_empty_ge_gaussian
    (num den : ℕ+) (τ Δinf : ℤ) (kv : ι × ℤ) (hkv : kv.2 ≤ Δinf) :
    1 - gaussianThresholdTail num den (τ - Δinf) ≤
      singleThresholdKeyRelease (DiscreteGaussianGenPMF num den) τ kv [] := by
  have hempty :
      singleThresholdKeyRelease (DiscreteGaussianGenPMF num den) τ kv [] =
        1 - gaussianThresholdTail num den (τ - kv.2) := by
    rw [singleThresholdKeyRelease_nil]
    have hsplit := pmf_split_lt_ge (DiscreteGaussianGenPMF num den kv.2) τ
    have htail :
        (∑' z : ℤ, if τ ≤ z then DiscreteGaussianGenPMF num den kv.2 z else 0) =
          gaussianThresholdTail num den (τ - kv.2) := by
      exact gaussianThresholdTail_shift num den τ kv.2
    exact ENNReal.eq_sub_of_add_eq' (by simp) (by simpa [htail, add_comm] using hsplit)
  have htail_mono :
      gaussianThresholdTail num den (τ - kv.2) ≤ gaussianThresholdTail num den (τ - Δinf) := by
    apply gaussianThresholdTail_mono
    omega
  rw [hempty]
  exact tsub_le_tsub_left htail_mono 1

/-- OpenDP-style bad-output mass for thresholded discrete-Laplace noise with `count`
potentially revealing keys. -/
def laplaceThresholdDelta
    (num den : ℕ+) (count : ℕ) (τ Δinf : ℤ) : ENNReal :=
  1 - (1 - laplaceThresholdTail num den (τ - Δinf)) ^ count

/-- OpenDP-style bad-output mass for thresholded discrete-Gaussian noise with `count`
potentially revealing keys. -/
def gaussianThresholdDelta
    (num den : ℕ+) (count : ℕ) (τ Δinf : ℤ) : ENNReal :=
  1 - (1 - gaussianThresholdTail num den (τ - Δinf)) ^ count

/-- `NNReal` packaging of the Laplace threshold bad-output mass. -/
def laplaceThresholdDeltaNNReal
    (num den : ℕ+) (count : ℕ) (τ Δinf : ℤ) : NNReal :=
  (laplaceThresholdDelta num den count τ Δinf).toNNReal

/-- `NNReal` packaging of the Gaussian threshold bad-output mass. -/
def gaussianThresholdDeltaNNReal
    (num den : ℕ+) (count : ℕ) (τ Δinf : ℤ) : NNReal :=
  (gaussianThresholdDelta num den count τ Δinf).toNNReal

theorem sparseThresholdKeyReleaseWith_bad_mass_le_laplace
    (num den : ℕ+) (τ Δinf : ℤ) (xs : List (ι × ℤ))
    (hxs : ∀ kv ∈ xs, kv.2 ≤ Δinf) :
    (∑' out : List (ι × ℤ),
      if out ≠ [] then
        sparseThresholdKeyReleaseWith (DiscreteLaplaceGenSamplePMF num den) τ xs out
      else 0) ≤
      laplaceThresholdDelta num den xs.length τ Δinf := by
  simpa [laplaceThresholdDelta] using
    (sparseThresholdKeyReleaseWith_bad_mass_le
      (noise := DiscreteLaplaceGenSamplePMF num den)
      (τ := τ)
      (δsingle := laplaceThresholdTail num den (τ - Δinf))
      (xs := xs)
      (by
        intro kv hkv
        exact singleThresholdKeyRelease_empty_ge_laplace num den τ Δinf kv (hxs kv hkv)))

theorem sparseThresholdKeyReleaseWith_bad_mass_le_gaussian
    (num den : ℕ+) (τ Δinf : ℤ) (xs : List (ι × ℤ))
    (hxs : ∀ kv ∈ xs, kv.2 ≤ Δinf) :
    (∑' out : List (ι × ℤ),
      if out ≠ [] then
        sparseThresholdKeyReleaseWith (DiscreteGaussianGenPMF num den) τ xs out
      else 0) ≤
      gaussianThresholdDelta num den xs.length τ Δinf := by
  simpa [gaussianThresholdDelta] using
    (sparseThresholdKeyReleaseWith_bad_mass_le
      (noise := DiscreteGaussianGenPMF num den)
      (τ := τ)
      (δsingle := gaussianThresholdTail num den (τ - Δinf))
      (xs := xs)
      (by
        intro kv hkv
        exact singleThresholdKeyRelease_empty_ge_gaussian num den τ Δinf kv (hxs kv hkv)))

theorem privSparseThresholdKeyReleasePure_bad_mass_le
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ Δinf : ℤ) (l : List T)
    (hquery : ∀ kv ∈ query l, kv.2 ≤ Δinf) :
    (∑' out : List (ι × ℤ),
      if out ≠ [] then (privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ l) out else 0) ≤
      laplaceThresholdDelta (Δ * ε₂) ε₁ (query l).length τ Δinf := by
  simpa [privSparseThresholdKeyReleasePure] using
    sparseThresholdKeyReleaseWith_bad_mass_le_laplace (Δ * ε₂) ε₁ τ Δinf (query l) hquery

theorem privSparseThresholdKeyRelease_bad_mass_le
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ Δinf : ℤ) (l : List T)
    (hquery : ∀ kv ∈ query l, kv.2 ≤ Δinf) :
    (∑' out : List (ι × ℤ),
      if out ≠ [] then (privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ l) out else 0) ≤
      gaussianThresholdDelta (Δ * ε₂) ε₁ (query l).length τ Δinf := by
  simpa [privSparseThresholdKeyRelease] using
    sparseThresholdKeyReleaseWith_bad_mass_le_gaussian (Δ * ε₂) ε₁ τ Δinf (query l) hquery

theorem privSparseThresholdKeyReleasePure_ApproxDP_of_good_output
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (ε : ℝ) (Δ0 : ℕ) (Δinf : ℤ)
    (good : List T → List T → Set (List (ι × ℤ)))
    (hgood :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        ∀ S : Set (List (ι × ℤ)),
          S ⊆ good l₁ l₂ →
            (∑' out : List (ι × ℤ),
              if out ∈ S then (privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ l₁) out else 0) ≤
              ENNReal.ofReal (Real.exp ε) *
                (∑' out : List (ι × ℤ),
                  if out ∈ S then (privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ l₂) out else 0))
    (hbad :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        (∑' out : List (ι × ℤ),
          if out ∈ (good l₁ l₂)ᶜ then
            (privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ l₁) out
          else 0) ≤
          laplaceThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf) :
    ApproximateDP
      (privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ)
      ε
      (laplaceThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf) := by
  exact ApproximateDP_of_good_output
    (m := privSparseThresholdKeyReleasePure query Δ ε₁ ε₂ τ)
    (ε := ε)
    (δ := laplaceThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf)
    (good := good)
    hgood hbad

theorem privSparseThresholdKeyRelease_ApproxDP_of_good_output
    (query : List T → List (ι × ℤ)) (Δ ε₁ ε₂ : ℕ+) (τ : ℤ)
    (ε : ℝ) (Δ0 : ℕ) (Δinf : ℤ)
    (good : List T → List T → Set (List (ι × ℤ)))
    (hgood :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        ∀ S : Set (List (ι × ℤ)),
          S ⊆ good l₁ l₂ →
            (∑' out : List (ι × ℤ),
              if out ∈ S then (privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ l₁) out else 0) ≤
              ENNReal.ofReal (Real.exp ε) *
                (∑' out : List (ι × ℤ),
                  if out ∈ S then (privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ l₂) out else 0))
    (hbad :
      ∀ l₁ l₂, Neighbour l₁ l₂ →
        (∑' out : List (ι × ℤ),
          if out ∈ (good l₁ l₂)ᶜ then
            (privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ l₁) out
          else 0) ≤
          gaussianThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf) :
    ApproximateDP
      (privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ)
      ε
      (gaussianThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf) := by
  exact ApproximateDP_of_good_output
    (m := privSparseThresholdKeyRelease query Δ ε₁ ε₂ τ)
    (ε := ε)
    (δ := gaussianThresholdDeltaNNReal (Δ * ε₂) ε₁ Δ0 τ Δinf)
    (good := good)
    hgood hbad

end SparseThreshold
end SLang
