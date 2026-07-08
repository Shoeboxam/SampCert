import SampCert.DifferentialPrivacy.AdditiveNoise.Basic
import SampCert.DifferentialPrivacy.Pure.Mechanism.Properties
import SampCert.DifferentialPrivacy.Pure.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.AdaptiveComposition
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import SampCert.DifferentialPrivacy.RenyiDivergence
import SampCert.Samplers.LaplaceGen.Properties
import SampCert.Samplers.GaussianGen.Properties
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Fin.Tuple
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Regular additive-noise mechanisms

This file packages regular-arithmetic additive-noise mechanisms in the unified
framework, covering both uncorrelated and correlated noise laws.
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure BigOperators

namespace SLang

variable {T ι : Type}
variable [Fintype ι]

section LaplaceVector

variable {α β γ η : Type}

def prodPMF (p : PMF α) (q : PMF β) : PMF (α × β) := do
  let a ← p
  (q.map (Prod.mk a))

@[simp] lemma prodPMF_apply (p : PMF α) (q : PMF β) (z : α × β) :
    prodPMF p q z = p z.1 * q z.2 := by
  classical
  rcases z with ⟨a, b⟩
  change (p.bind fun a' => PMF.map (Prod.mk a') q) (a, b) = p a * q b
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply]
    congr 1
    rw [tsum_eq_single b]
    · simp
    · intro b' hb'
      by_cases h : b = b'
      · exact (hb' h.symm).elim
      · simp [h]
  · intro a' ha'
    have hinner : (∑' a₂ : β, if a = a' ∧ b = a₂ then q a₂ else 0) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      intro a₂
      by_cases h : a = a'
      · exact (ha' h.symm).elim
      · simp [h]
    simp [hinner]

lemma prodPMF_map_prod (p : PMF α) (q : PMF β) (f : α → γ) (g : β → η) :
    prodPMF (p.map f) (q.map g) =
      (prodPMF p q).map (fun z => (f z.1, g z.2)) := by
  change PMF.bind (PMF.map f p) (fun a => PMF.map (Prod.mk a) (PMF.map g q)) =
    PMF.map (fun z => (f z.1, g z.2)) (PMF.bind p fun a => PMF.map (Prod.mk a) q)
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg (PMF.bind p) ?_
  funext a
  change PMF.map (Prod.mk (f a)) (PMF.map g q) =
    PMF.map (fun z => (f z.1, g z.2)) (PMF.map (Prod.mk a) q)
  rw [PMF.map_comp, PMF.map_comp]
  rfl

lemma map_apply_equiv [DecidableEq β] (e : α ≃ β) (p : PMF α) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp
  · intro a ha
    by_cases hab : b = e a
    · exfalso
      apply ha
      simpa [hab] using (e.left_inv a).symm
    · simp [hab]

def reindexFunEquiv (e : α ≃ β) : (β → γ) ≃ (α → γ) where
  toFun f a := f (e a)
  invFun g b := g (e.symm b)
  left_inv f := by
    funext b
    simp
  right_inv g := by
    funext a
    simp

abbrev optionFunEquiv (γ : Type) : (Option α → γ) ≃ γ × (α → γ) :=
  Equiv.piOptionEquivProd

def discreteLaplaceFinPMF (num den : ℕ+) :
    ∀ n, (Fin n → ℤ) → PMF (Fin n → ℤ)
  | 0, _ => PMF.pure (fun i => Fin.elim0 i)
  | n + 1, μ =>
      (prodPMF
        (DiscreteLaplaceGenSamplePMF num den (μ 0))
        (discreteLaplaceFinPMF num den n (fun i => μ i.succ))).map
        (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))

@[simp] lemma discreteLaplaceFinPMF_apply
    (num den : ℕ+) :
    ∀ n (μ r : Fin n → ℤ),
      discreteLaplaceFinPMF num den n μ r =
        ∏ i, DiscreteLaplaceGenSamplePMF num den (μ i) (r i)
  | 0, μ, r => by
      have hr : r = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hr
      simp [discreteLaplaceFinPMF]
  | n + 1, μ, r => by
      rw [discreteLaplaceFinPMF]
      rw [map_apply_equiv (e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))]
      rw [prodPMF_apply, discreteLaplaceFinPMF_apply]
      simp [Fin.prod_univ_succ, Fin.tail, Fin.cons_zero, Fin.cons_succ]

/-- Regular finite-dimensional discrete-Laplace law centered at `μ`. -/
def discreteLaplaceVecPMF
    (num den : ℕ+) (μ : ι → ℤ) : PMF (ι → ℤ) :=
  let e := Fintype.equivFin ι
  (discreteLaplaceFinPMF num den (Fintype.card ι) (fun j => μ (e.symm j))).map (reindexFunEquiv e)

@[simp] lemma discreteLaplaceVecPMF_apply
    [DecidableEq ι]
    (num den : ℕ+) (μ r : ι → ℤ) :
    discreteLaplaceVecPMF num den μ r =
      ∏ i, DiscreteLaplaceGenSamplePMF num den (μ i) (r i) := by
  classical
  rw [discreteLaplaceVecPMF]
  rw [map_apply_equiv (e := reindexFunEquiv (Fintype.equivFin ι))]
  simpa [discreteLaplaceFinPMF_apply, reindexFunEquiv] using
    ((Fintype.equivFin ι).symm.prod_comp
      (fun i : ι => DiscreteLaplaceGenSamplePMF num den (μ i) (r i)))

lemma discreteLaplaceVecPMF_option
    [DecidableEq ι]
    (num den : ℕ+) (μ : Option ι → ℤ) :
    discreteLaplaceVecPMF num den μ =
      (prodPMF
        (DiscreteLaplaceGenSamplePMF num den (μ none))
        (discreteLaplaceVecPMF num den (fun i => μ (some i)))).map
        (optionFunEquiv (α := ι) ℤ).symm := by
  classical
  ext x
  rw [map_apply_equiv (e := (optionFunEquiv (α := ι) ℤ).symm)]
  rw [prodPMF_apply, discreteLaplaceVecPMF_apply, discreteLaplaceVecPMF_apply]
  simp [Fintype.prod_option, mul_comm, mul_left_comm, mul_assoc]

lemma discreteLaplaceGenSamplePMF_pos
    (num den : ℕ+) (μ x : ℤ) :
    0 < DiscreteLaplaceGenSamplePMF num den μ x := by
  let d : ℝ := (num : ℝ) / (den : ℝ)
  let c : ℝ := (Real.exp ((den : ℝ) / (num : ℝ)) - 1) / (Real.exp ((den : ℝ) / (num : ℝ)) + 1)
  change 0 < DiscreteLaplaceGenSample num den μ x
  rw [DiscreteLaplaceGenSample_apply]
  apply ENNReal.ofReal_pos.mpr
  have hd_pos : 0 < d := by
    change 0 < (((num : NNReal) / den : NNReal) : ℝ)
    have hnum : (0 : NNReal) < (num : NNReal) := by
      change (0 : NNReal) < ((num : ℕ) : NNReal)
      simp
    have hden : (0 : NNReal) < (den : NNReal) := by
      change (0 : NNReal) < ((den : ℕ) : NNReal)
      simp
    exact_mod_cast div_pos hnum hden
  have hc_pos : 0 < c := by
    dsimp [c]
    have hexp : 1 < Real.exp ((den : ℝ) / (num : ℝ)) := by
      have hden : (0 : NNReal) < (den : NNReal) := by
        change (0 : NNReal) < ((den : ℕ) : NNReal)
        simp
      have hnum : (0 : NNReal) < (num : NNReal) := by
        change (0 : NNReal) < ((num : ℕ) : NNReal)
        simp
      have hdiv : (0 : NNReal) < (den : NNReal) / num := div_pos hden hnum
      have h : Real.exp 0 < Real.exp ((den : ℝ) / (num : ℝ)) := by
        exact Real.exp_lt_exp.mpr (by exact_mod_cast hdiv)
      simpa using h
    have hden : 0 < Real.exp ((den : ℝ) / (num : ℝ)) + 1 := by positivity
    exact div_pos (sub_pos.mpr hexp) hden
  simpa [d, c, NNReal.coe_div] using mul_pos hc_pos (Real.exp_pos _)

lemma discreteLaplaceGenSamplePMF_DP_singleton
    (num den : ℕ+) (μ₁ μ₂ x : ℤ) :
    DiscreteLaplaceGenSamplePMF num den μ₁ x /
        DiscreteLaplaceGenSamplePMF num den μ₂ x
      ≤ ENNReal.ofReal
          (Real.exp
            (((Int.natAbs (μ₁ - μ₂) : ℝ)) /
              ((((num : NNReal) / den : NNReal) : ℝ)))) := by
  let d : ℝ := (num : ℝ) / (den : ℝ)
  let c : ℝ := (Real.exp ((den : ℝ) / (num : ℝ)) - 1) / (Real.exp ((den : ℝ) / (num : ℝ)) + 1)
  have hμ₁ :
      DiscreteLaplaceGenSamplePMF num den μ₁ x =
        ENNReal.ofReal (c * Real.exp (- (|(x : ℝ) - (μ₁ : ℝ)| / d))) := by
    change DiscreteLaplaceGenSample num den μ₁ x =
      ENNReal.ofReal (c * Real.exp (- (|(x : ℝ) - (μ₁ : ℝ)| / d)))
    rw [DiscreteLaplaceGenSample_apply]
    congr 1
    norm_num [d, c]
    norm_cast
  have hμ₂ :
      DiscreteLaplaceGenSamplePMF num den μ₂ x =
        ENNReal.ofReal (c * Real.exp (- (|(x : ℝ) - (μ₂ : ℝ)| / d))) := by
    change DiscreteLaplaceGenSample num den μ₂ x =
      ENNReal.ofReal (c * Real.exp (- (|(x : ℝ) - (μ₂ : ℝ)| / d)))
    rw [DiscreteLaplaceGenSample_apply]
    congr 1
    norm_num [d, c]
    norm_cast
  rw [hμ₁, hμ₂]
  have hd_pos : 0 < d := by
    change 0 < (((num : NNReal) / den : NNReal) : ℝ)
    have hnum : (0 : NNReal) < (num : NNReal) := by
      change (0 : NNReal) < ((num : ℕ) : NNReal)
      simp
    have hden : (0 : NNReal) < (den : NNReal) := by
      change (0 : NNReal) < ((den : ℕ) : NNReal)
      simp
    exact_mod_cast div_pos hnum hden
  have hc_pos : 0 < c := by
    dsimp [c]
    have hexp : 1 < Real.exp ((den : ℝ) / (num : ℝ)) := by
      have hden : (0 : NNReal) < (den : NNReal) := by
        change (0 : NNReal) < ((den : ℕ) : NNReal)
        simp
      have hnum : (0 : NNReal) < (num : NNReal) := by
        change (0 : NNReal) < ((num : ℕ) : NNReal)
        simp
      have hdiv : (0 : NNReal) < (den : NNReal) / num := div_pos hden hnum
      have h : Real.exp 0 < Real.exp ((den : ℝ) / (num : ℝ)) := by
        exact Real.exp_lt_exp.mpr (by exact_mod_cast hdiv)
      simpa using h
    have hden : 0 < Real.exp ((den : ℝ) / (num : ℝ)) + 1 := by positivity
    exact div_pos (sub_pos.mpr hexp) hden
  rw [← ENNReal.ofReal_div_of_pos]
  · apply ENNReal.ofReal_le_ofReal
    rw [mul_div_mul_left _ _ hc_pos.ne']
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have habs :
        |(x : ℝ) - (μ₂ : ℝ)| - |(x : ℝ) - (μ₁ : ℝ)|
          ≤ (Int.natAbs (μ₁ - μ₂) : ℝ) := by
      calc
        |(x : ℝ) - (μ₂ : ℝ)| - |(x : ℝ) - (μ₁ : ℝ)|
            ≤ |((x : ℝ) - (μ₂ : ℝ)) - ((x : ℝ) - (μ₁ : ℝ))| :=
              abs_sub_abs_le_abs_sub _ _
        _ = |(μ₁ : ℝ) - (μ₂ : ℝ)| := by
              congr 1
              ring
        _ = (Int.natAbs (μ₁ - μ₂) : ℝ) := by
              rw [← natAbs_to_abs μ₁ μ₂]
    have hscaled :=
      mul_le_mul_of_nonneg_right habs (inv_nonneg.mpr hd_pos.le)
    simpa [d, div_eq_mul_inv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  · exact mul_pos hc_pos (Real.exp_pos _)

end LaplaceVector

section GaussianVector

def discreteGaussianFinPMF (num den : ℕ+) :
    ∀ n, (Fin n → ℤ) → PMF (Fin n → ℤ)
  | 0, _ => PMF.pure (fun i => Fin.elim0 i)
  | n + 1, μ =>
      (prodPMF
        (DiscreteGaussianGenPMF num den (μ 0))
        (discreteGaussianFinPMF num den n (fun i => μ i.succ))).map
        (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))

@[simp] lemma discreteGaussianFinPMF_apply
    (num den : ℕ+) :
    ∀ n (μ r : Fin n → ℤ),
      discreteGaussianFinPMF num den n μ r =
        ∏ i, DiscreteGaussianGenPMF num den (μ i) (r i)
  | 0, μ, r => by
      have hr : r = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hr
      simp [discreteGaussianFinPMF]
  | n + 1, μ, r => by
      rw [discreteGaussianFinPMF]
      rw [map_apply_equiv (e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))]
      rw [prodPMF_apply, discreteGaussianFinPMF_apply]
      simp [Fin.prod_univ_succ, Fin.tail, Fin.cons_zero, Fin.cons_succ]

lemma discreteGaussianGenPMF_pos_aux
    (num den : ℕ+) (μ x : ℤ) :
    0 < DiscreteGaussianGenPMF num den μ x := by
  have hσ : ((num : ℝ) / (den : ℝ)) ≠ 0 := by
    have hnum : (0 : ℝ) < (num : ℝ) := by
      cases num with
      | mk n hn =>
          change (0 : ℝ) < n
          exact_mod_cast hn
    have hden : (0 : ℝ) < (den : ℝ) := by
      cases den with
      | mk n hn =>
          change (0 : ℝ) < n
          exact_mod_cast hn
    exact ne_of_gt (div_pos hnum hden)
  change 0 < DiscreteGaussianGenSample num den μ x
  rw [DiscreteGaussianGenSample_apply]
  exact ENNReal.ofReal_pos.mpr (discrete_gaussian_pos hσ μ x)

lemma discreteGaussianFinPMF_pos
    (num den : ℕ+) :
    ∀ n (μ r : Fin n → ℤ), 0 < discreteGaussianFinPMF num den n μ r
  | 0, μ, r => by
      have hr : r = (fun i => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      subst hr
      simp [discreteGaussianFinPMF]
  | n + 1, μ, r => by
      rw [discreteGaussianFinPMF_apply]
      rw [pos_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr
        (fun i _hi => (discreteGaussianGenPMF_pos_aux num den (μ i) (r i)).ne')

lemma discreteGaussianFinPMF_AC
    (num den : ℕ+) :
    ∀ n (μ₁ μ₂ : Fin n → ℤ),
      AbsCts (discreteGaussianFinPMF num den n μ₁)
        (discreteGaussianFinPMF num den n μ₂)
  | 0, μ₁, μ₂ => by
      intro r hr
      exfalso
      exact (discreteGaussianFinPMF_pos num den 0 μ₂ r).ne' hr
  | n + 1, μ₁, μ₂ => by
      intro r hr
      exfalso
      exact (discreteGaussianFinPMF_pos num den (n + 1) μ₂ r).ne' hr

/-- Regular finite-dimensional discrete-Gaussian law centered at `μ`. -/
def discreteGaussianVecPMF
    (num den : ℕ+) (μ : ι → ℤ) : PMF (ι → ℤ) :=
  let e := Fintype.equivFin ι
  (discreteGaussianFinPMF num den (Fintype.card ι) (fun j => μ (e.symm j))).map (reindexFunEquiv e)

@[simp] lemma discreteGaussianVecPMF_apply
    [DecidableEq ι]
    (num den : ℕ+) (μ r : ι → ℤ) :
    discreteGaussianVecPMF num den μ r =
      ∏ i, DiscreteGaussianGenPMF num den (μ i) (r i) := by
  classical
  rw [discreteGaussianVecPMF]
  rw [map_apply_equiv (e := reindexFunEquiv (Fintype.equivFin ι))]
  simpa [discreteGaussianFinPMF_apply, reindexFunEquiv] using
    ((Fintype.equivFin ι).symm.prod_comp
      (fun i : ι => DiscreteGaussianGenPMF num den (μ i) (r i)))

lemma discreteGaussianVecPMF_option
    [DecidableEq ι]
    (num den : ℕ+) (μ : Option ι → ℤ) :
    discreteGaussianVecPMF num den μ =
      (prodPMF
        (DiscreteGaussianGenPMF num den (μ none))
        (discreteGaussianVecPMF num den (fun i => μ (some i)))).map
        (optionFunEquiv (α := ι) ℤ).symm := by
  classical
  ext x
  rw [map_apply_equiv (e := (optionFunEquiv (α := ι) ℤ).symm)]
  rw [prodPMF_apply, discreteGaussianVecPMF_apply, discreteGaussianVecPMF_apply]
  simp [Fintype.prod_option, mul_comm, mul_left_comm, mul_assoc]

lemma discreteGaussianGenPMF_pos
    (num den : ℕ+) (μ x : ℤ) :
    0 < DiscreteGaussianGenPMF num den μ x := by
  exact discreteGaussianGenPMF_pos_aux num den μ x

lemma discreteGaussianGenPMF_AC
    (num den : ℕ+) (μ₁ μ₂ : ℤ) :
    AbsCts (DiscreteGaussianGenPMF num den μ₁)
      (DiscreteGaussianGenPMF num den μ₂) := by
  intro x hx
  exfalso
  exact (discreteGaussianGenPMF_pos num den μ₂ x).ne' hx

theorem discreteGaussianVec_AC
    (num den : ℕ+) (μ₁ μ₂ : ι → ℤ) :
    AbsCts (discreteGaussianVecPMF num den μ₁)
      (discreteGaussianVecPMF num den μ₂) := by
  classical
  intro r hr
  rw [discreteGaussianVecPMF_apply] at hr ⊢
  exfalso
  rcases Finset.prod_eq_zero_iff.mp hr with ⟨i, _hi, hi⟩
  exact (discreteGaussianGenPMF_pos num den (μ₂ i) (r i)).ne' hi

end GaussianVector

lemma RenyiDivergence_map_equiv
    {α β : Type} [DecidableEq β]
    (e : α ≃ β) (p q : PMF α) (a : ℝ) :
    RenyiDivergence (p.map e) (q.map e) a = RenyiDivergence p q a := by
  unfold RenyiDivergence RenyiDivergence_def
  congr 1
  congr 1
  have htsum :
      ∑' x : β, (p.map e x) ^ a * (q.map e x) ^ (1 - a) =
        ∑' x : α, (p x) ^ a * (q x) ^ (1 - a) := by
    calc
      ∑' x : β, (p.map e x) ^ a * (q.map e x) ^ (1 - a)
          = ∑' x : β, (p (e.symm x)) ^ a * (q (e.symm x)) ^ (1 - a) := by
              apply tsum_congr
              intro x
              rw [map_apply_equiv (e := e), map_apply_equiv (e := e)]
      _ = ∑' x : α, (p x) ^ a * (q x) ^ (1 - a) := by
            simpa using (e.symm.tsum_eq (fun x : α => (p x) ^ a * (q x) ^ (1 - a)))
  rw [htsum]

section ProductRenyi

variable {U V : Type}
variable [Inhabited U] [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
variable [Inhabited V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

def switchMechanism (p₀ p₁ : PMF U) : List Unit → PMF U
  | [] => p₀
  | _ => p₁

lemma switchMechanism_AC
    (p₀ p₁ : PMF U)
    (h₀₁ : AbsCts p₀ p₁)
    (h₁₀ : AbsCts p₁ p₀) :
    ACNeighbour (switchMechanism p₀ p₁) := by
  intro l₁ l₂ hneigh
  cases hneigh with
  | Addition hl₁ hl₂ =>
      rename_i a b n
      subst hl₁ hl₂
      by_cases hnil : a ++ b = []
      · have ha : a = [] := (List.append_eq_nil_iff.mp hnil).1
        have hb : b = [] := (List.append_eq_nil_iff.mp hnil).2
        subst ha
        subst hb
        simpa [switchMechanism] using h₀₁
      · have hcons : a ++ [()] ++ b ≠ [] := by simp
        simpa [switchMechanism, hnil, hcons] using AbsCts_refl p₁
  | Deletion hl₁ hl₂ =>
      rename_i a n b
      subst hl₁ hl₂
      by_cases hnil : a ++ b = []
      · have ha : a = [] := (List.append_eq_nil_iff.mp hnil).1
        have hb : b = [] := (List.append_eq_nil_iff.mp hnil).2
        subst ha
        subst hb
        simpa [switchMechanism] using h₁₀
      · have hcons : a ++ [()] ++ b ≠ [] := by simp
        simpa [switchMechanism, hnil, hcons] using AbsCts_refl p₁

lemma prodPMF_renyi_bound
    (p₁ p₂ : PMF U) (q₁ q₂ : PMF V)
    (h₁₂ : AbsCts p₁ p₂) (h₂₁ : AbsCts p₂ p₁)
    (hq₁₂ : AbsCts q₁ q₂) (hq₂₁ : AbsCts q₂ q₁)
    {α : ℝ} (hα : 1 < α) :
    RenyiDivergence (prodPMF p₁ q₁) (prodPMF p₂ q₂) α
      ≤ RenyiDivergence p₁ p₂ α + RenyiDivergence q₁ q₂ α := by
  let nq₁ : List Unit → PMF U := switchMechanism p₁ p₂
  let nq₂ : U → List Unit → PMF V := fun _ => switchMechanism q₁ q₂
  have hN : Neighbour ([] : List Unit) [()] := by
    exact Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl
  have hac₁ : ACNeighbour nq₁ := switchMechanism_AC p₁ p₂ h₁₂ h₂₁
  have hac₂ : ∀ u, ACNeighbour (nq₂ u) := fun _ => switchMechanism_AC q₁ q₂ hq₁₂ hq₂₁
  have hcomp := privComposeAdaptive_renyi_bound
    (nq1 := nq₁) (nq2 := nq₂) (α := α) hα hN hac₁ hac₂
  have hleft :
      privComposeAdaptive nq₁ nq₂ [] = prodPMF p₁ q₁ := by
    ext z
    rcases z with ⟨u, v⟩
    change (privComposeAdaptive nq₁ nq₂ ([] : List Unit)) (u, v) = (prodPMF p₁ q₁) (u, v)
    rw [prodPMF_apply]
    exact privComposeChainRule nq₁ nq₂ ([] : List Unit) u v
  have hright :
      privComposeAdaptive nq₁ nq₂ [()] = prodPMF p₂ q₂ := by
    ext z
    rcases z with ⟨u, v⟩
    change (privComposeAdaptive nq₁ nq₂ ([()] : List Unit)) (u, v) = (prodPMF p₂ q₂) (u, v)
    rw [prodPMF_apply]
    exact privComposeChainRule nq₁ nq₂ ([()] : List Unit) u v
  rw [hleft, hright] at hcomp
  simpa [nq₁, nq₂, switchMechanism, iSup_const] using hcomp

end ProductRenyi

theorem discreteGaussianFinPMF_renyi_bound
    {α : ℝ} (hα : 1 < α) (num den : ℕ+) :
    ∀ n (μ₁ μ₂ : Fin n → ℤ),
      RenyiDivergence
        (discreteGaussianFinPMF num den n μ₁)
        (discreteGaussianFinPMF num den n μ₂)
        α
      ≤ ∑ i, RenyiDivergence
          (DiscreteGaussianGenPMF num den (μ₁ i))
          (DiscreteGaussianGenPMF num den (μ₂ i))
          α
  | 0, μ₁, μ₂ => by
      have hEq :
          discreteGaussianFinPMF num den 0 μ₁ =
            discreteGaussianFinPMF num den 0 μ₂ := by
        simp [discreteGaussianFinPMF]
      have hzero :
          RenyiDivergence
            (discreteGaussianFinPMF num den 0 μ₁)
            (discreteGaussianFinPMF num den 0 μ₂)
            α = 0 := by
        rw [hEq]
        exact (RenyiDivergence_aux_zero _ _ hα (AbsCts_refl _)).mp rfl
      rw [hzero]
      simp
  | n + 1, μ₁, μ₂ => by
      let p₁ := DiscreteGaussianGenPMF num den (μ₁ 0)
      let p₂ := DiscreteGaussianGenPMF num den (μ₂ 0)
      let q₁ := discreteGaussianFinPMF num den n (fun i => μ₁ i.succ)
      let q₂ := discreteGaussianFinPMF num den n (fun i => μ₂ i.succ)
      calc
        RenyiDivergence
            (discreteGaussianFinPMF num den (n + 1) μ₁)
            (discreteGaussianFinPMF num den (n + 1) μ₂)
            α
            =
          RenyiDivergence (prodPMF p₁ q₁) (prodPMF p₂ q₂) α := by
              rw [discreteGaussianFinPMF, discreteGaussianFinPMF]
              simpa [p₁, p₂, q₁, q₂] using
                (RenyiDivergence_map_equiv
                  (e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ))
                  (p := prodPMF p₁ q₁)
                  (q := prodPMF p₂ q₂)
                  (a := α))
        _ ≤ RenyiDivergence p₁ p₂ α + RenyiDivergence q₁ q₂ α := by
              apply prodPMF_renyi_bound
              · simpa [p₁, p₂] using discreteGaussianGenPMF_AC num den (μ₁ 0) (μ₂ 0)
              · simpa [p₁, p₂] using discreteGaussianGenPMF_AC num den (μ₂ 0) (μ₁ 0)
              · simpa [q₁, q₂] using discreteGaussianFinPMF_AC num den n (fun i => μ₁ i.succ) (fun i => μ₂ i.succ)
              · simpa [q₁, q₂] using discreteGaussianFinPMF_AC num den n (fun i => μ₂ i.succ) (fun i => μ₁ i.succ)
              · exact hα
        _ ≤ RenyiDivergence p₁ p₂ α +
              ∑ i : Fin n, RenyiDivergence
                (DiscreteGaussianGenPMF num den (μ₁ i.succ))
                (DiscreteGaussianGenPMF num den (μ₂ i.succ))
                α := by
              gcongr
              simpa [q₁, q₂] using
                discreteGaussianFinPMF_renyi_bound hα num den n (fun i => μ₁ i.succ) (fun i => μ₂ i.succ)
        _ = ∑ i : Fin (n + 1), RenyiDivergence
              (DiscreteGaussianGenPMF num den (μ₁ i))
              (DiscreteGaussianGenPMF num den (μ₂ i))
              α := by
              simp [p₁, p₂, Fin.sum_univ_succ]

/-- Regular finite-dimensional discrete-Laplace mechanism. -/
def privNoisedQueryPureVec
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  discreteLaplaceVecPMF (Δ * ε₂) ε₁ (query l)

/-- Regular finite-dimensional discrete-Gaussian mechanism. -/
def privNoisedQueryVec
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  discreteGaussianVecPMF (Δ * ε₂) ε₁ (query l)

@[simp] lemma privNoisedQueryPureVec_eq
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryPureVec query Δ ε₁ ε₂ l =
      discreteLaplaceVecPMF (Δ * ε₂) ε₁ (query l) := by
  rfl

@[simp] lemma privNoisedQueryVec_eq
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryVec query Δ ε₁ ε₂ l =
      discreteGaussianVecPMF (Δ * ε₂) ε₁ (query l) := by
  rfl

/-- Singleton-event DP bound for the regular vector Laplace mechanism. -/
theorem discreteLaplaceVec_DP_singleton
    (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ℤ) (τ : ι → ℤ)
    (hτ : (∑ i, Int.natAbs (τ i)) ≤ Δ)
    (hdiff : ∀ i, τ i = μ₁ i - μ₂ i) :
    ∀ r : ι → ℤ,
      discreteLaplaceVecPMF (Δ * ε₂) ε₁ μ₁ r /
        discreteLaplaceVecPMF (Δ * ε₂) ε₁ μ₂ r
      ≤ ENNReal.ofReal (Real.exp ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ))) := by
  classical
  intro r
  rw [discreteLaplaceVecPMF_apply, discreteLaplaceVecPMF_apply]
  have hdiv :
      (∏ i, DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₁ i) (r i) /
          DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₂ i) (r i))
        =
      (∏ i, DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₁ i) (r i)) /
        (∏ i, DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₂ i) (r i)) := by
    simpa using ENNReal.prod_div_distrib_of_ne_zero
      (s := Finset.univ)
      (f := fun i => DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₁ i) (r i))
      (g := fun i => DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₂ i) (r i))
      (by
        intro i _hi
        exact (discreteLaplaceGenSamplePMF_pos (Δ * ε₂) ε₁ (μ₂ i) (r i)).ne')
  rw [← hdiv]
  have hcoord :
      (∏ i, DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₁ i) (r i) /
          DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (μ₂ i) (r i))
        ≤
      ∏ i, ENNReal.ofReal
        (Real.exp
          (((Int.natAbs (τ i) : ℝ)) /
            (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ)))) := by
    refine Finset.prod_le_prod' ?_
    intro i _hi
    simpa [hdiff i] using
      discreteLaplaceGenSamplePMF_DP_singleton (Δ * ε₂) ε₁ (μ₁ i) (μ₂ i) (r i)
  refine hcoord.trans ?_
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_sum]
    have hsum :
        (∑ i, ((Int.natAbs (τ i) : ℝ) / (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ))))
          ≤ ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
      have hd_pos : 0 < (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ)) := by
        change 0 < ((((Δ * ε₂ : ℕ+) : NNReal) / ε₁ : NNReal) : ℝ)
        have hnum : (0 : NNReal) < ((Δ * ε₂ : ℕ+) : NNReal) := by
          change (0 : NNReal) < ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal))
          simp
        have hden : (0 : NNReal) < (ε₁ : NNReal) := by
          change (0 : NNReal) < ((ε₁ : ℕ) : NNReal)
          simp
        exact_mod_cast div_pos hnum hden
      have hτ_real : (∑ i, (Int.natAbs (τ i) : ℝ)) ≤ (Δ : ℝ) := by
        have hτ_nat : (∑ i, Int.natAbs (τ i) : ℕ) ≤ (Δ : ℕ) := by
          simpa using hτ
        calc
          (∑ i, (Int.natAbs (τ i) : ℝ)) = (((∑ i, Int.natAbs (τ i) : ℕ) : ℝ)) := by
            simp [Nat.cast_sum]
          _ ≤ (Δ : ℝ) := by
            have hτ_nat_real : (((∑ i, Int.natAbs (τ i) : ℕ) : ℕ) : ℝ) ≤ ((Δ : ℕ) : ℝ) := by
              exact_mod_cast hτ_nat
            simpa using hτ_nat_real
      calc
        (∑ i, ((Int.natAbs (τ i) : ℝ) / (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ))))
            = ((∑ i, (Int.natAbs (τ i) : ℝ)) / (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ))) := by
                simp [div_eq_mul_inv, Finset.sum_mul]
        _ ≤ ((Δ : ℝ) / (((Δ * ε₂ : ℕ+) : ℝ) / (ε₁ : ℝ))) := by
              exact div_le_div_of_nonneg_right hτ_real hd_pos.le
        _ = ((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) := by
              have hmulNN : (((Δ * ε₂ : ℕ+) : NNReal)) = (Δ : NNReal) * (ε₂ : NNReal) := by
                change ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal)) = (((Δ : ℕ) : NNReal) * ((ε₂ : ℕ) : NNReal))
                norm_num
              have hmul : (((Δ * ε₂ : ℕ+) : ℝ)) = (Δ : ℝ) * (ε₂ : ℝ) := by
                exact_mod_cast hmulNN
              rw [hmul, NNReal.coe_div]
              have hΔ : (0 : NNReal) < (Δ : NNReal) := by
                change (0 : NNReal) < ((Δ : ℕ) : NNReal)
                simp
              have hε₁ : (0 : NNReal) < (ε₁ : NNReal) := by
                change (0 : NNReal) < ((ε₁ : ℕ) : NNReal)
                simp
              have hε₂ : (0 : NNReal) < (ε₂ : NNReal) := by
                change (0 : NNReal) < ((ε₂ : ℕ) : NNReal)
                simp
              field_simp [hΔ.ne', hε₁.ne', hε₂.ne']
    exact Real.exp_le_exp.mpr hsum
  · intro i _hi
    exact le_of_lt (Real.exp_pos _)

/-- zCDP / Rényi bound for the regular vector discrete-Gaussian mechanism. -/
theorem discreteGaussianVec_zCDPBound_pointwise
    (α : ℝ) (hα : 1 < α)
    (Δ ε₁ ε₂ : ℕ+) (μ₁ μ₂ : ι → ℤ) (τ : ι → ℤ)
    (hτ : (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2)
    (hdiff : ∀ i, τ i = μ₁ i - μ₂ i) :
    RenyiDivergence
      (discreteGaussianVecPMF (Δ * ε₂) ε₁ μ₁)
      (discreteGaussianVecPMF (Δ * ε₂) ε₁ μ₂)
      α
      ≤ ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α) := by
  classical
  let e := Fintype.equivFin ι
  let num : ℕ+ := Δ * ε₂
  let μ₁' : Fin (Fintype.card ι) → ℤ := fun j => μ₁ (e.symm j)
  let μ₂' : Fin (Fintype.card ι) → ℤ := fun j => μ₂ (e.symm j)
  let D : ENNReal :=
    ((2 : ENNReal) * (((num : ENNReal) / (ε₁ : ENNReal)) ^ 2) : ENNReal)
  have hvec :
      RenyiDivergence
        (discreteGaussianVecPMF (Δ * ε₂) ε₁ μ₁)
        (discreteGaussianVecPMF (Δ * ε₂) ε₁ μ₂)
        α
        =
      RenyiDivergence
        (discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₁')
        (discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₂')
        α := by
    simpa [discreteGaussianVecPMF, e, μ₁', μ₂'] using
      (RenyiDivergence_map_equiv
        (e := reindexFunEquiv e)
        (p := discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₁')
        (q := discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₂')
        (a := α))
  have hτ_fin :
      (∑ j : Fin (Fintype.card ι), (Int.natAbs (τ (e.symm j))) ^ 2) ≤ Δ ^ 2 := by
    rw [Equiv.sum_comp e.symm (fun i : ι => (Int.natAbs (τ i)) ^ 2)]
    exact hτ
  have hsum_real :
      (∑ j : Fin (Fintype.card ι), ((((τ (e.symm j)) : ℤ) ^ 2 : ℤ) : ℝ))
        ≤ (Δ : ℝ) ^ 2 := by
    have hcast :
        (∑ j : Fin (Fintype.card ι), ((((τ (e.symm j)) : ℤ) ^ 2 : ℤ) : ℝ))
          =
        (((∑ j : Fin (Fintype.card ι), (Int.natAbs (τ (e.symm j))) ^ 2 : ℕ) : ℕ) : ℝ) := by
      simp [Nat.cast_sum, Int.natAbs_sq]
    have hτ_fin_real :
        (((∑ j : Fin (Fintype.card ι), (Int.natAbs (τ (e.symm j))) ^ 2 : ℕ) : ℕ) : ℝ)
          ≤ (((Δ ^ 2 : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast hτ_fin
    rw [hcast]
    simpa [pow_two] using hτ_fin_real
  have hnum :
      ∑ j : Fin (Fintype.card ι), ENNReal.ofReal ((((τ (e.symm j)) : ℤ) ^ 2 : ℤ) : ℝ)
        ≤ ENNReal.ofReal ((Δ : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · exact ENNReal.ofReal_le_ofReal hsum_real
    · intro j _hj
      positivity
  rw [hvec]
  calc
    RenyiDivergence
        (discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₁')
        (discreteGaussianFinPMF (Δ * ε₂) ε₁ (Fintype.card ι) μ₂')
        α
        ≤
      ∑ j : Fin (Fintype.card ι), RenyiDivergence
        (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ (μ₁' j))
        (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ (μ₂' j))
        α := by
          simpa [μ₁', μ₂'] using
            discreteGaussianFinPMF_renyi_bound hα (Δ * ε₂) ε₁ (Fintype.card ι) μ₁' μ₂'
    _ ≤
      ∑ j : Fin (Fintype.card ι),
        (ENNReal.ofReal α) *
          (ENNReal.ofReal ((((τ (e.symm j)) : ℤ) ^ 2 : ℤ) : ℝ) / D) := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            simpa [μ₁', μ₂', D, hdiff (e.symm j)] using
              discrete_GaussianGenSample_ZeroConcentrated hα
                num ε₁ (μ₁' j) (μ₂' j)
    _ =
      (ENNReal.ofReal α) *
        ((∑ j : Fin (Fintype.card ι),
            ENNReal.ofReal ((((τ (e.symm j)) : ℤ) ^ 2 : ℤ) : ℝ)) / D) := by
          rw [← Finset.mul_sum]
          congr 1
          simp [div_eq_mul_inv, Finset.sum_mul]
    _ ≤
      (ENNReal.ofReal α) * (ENNReal.ofReal ((Δ : ℝ) ^ 2) / D) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_left' (ENNReal.div_le_div_right hnum D) (ENNReal.ofReal α)
    _ = ENNReal.ofReal ((1 / 2) * (((((ε₁ : NNReal) / ε₂ : NNReal) : ℝ)) ^ 2) * α) := by
          have hα_nonneg : 0 ≤ α := by linarith
          have hΔNN : (0 : NNReal) < (Δ : NNReal) := by
            change (0 : NNReal) < ((Δ : ℕ) : NNReal)
            simp
          have hε₁NN : (0 : NNReal) < (ε₁ : NNReal) := by
            change (0 : NNReal) < ((ε₁ : ℕ) : NNReal)
            simp
          have hε₂NN : (0 : NNReal) < (ε₂ : NNReal) := by
            change (0 : NNReal) < ((ε₂ : ℕ) : NNReal)
            simp
          have hΔ : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔNN
          have hε₁ : (0 : ℝ) < (ε₁ : ℝ) := by exact_mod_cast hε₁NN
          have hε₂ : (0 : ℝ) < (ε₂ : ℝ) := by exact_mod_cast hε₂NN
          have hdiv :
              ((num : ENNReal) / (ε₁ : ENNReal))
                = ENNReal.ofReal (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) := by
            have hdiv₁ :
                ((num : ENNReal) / (ε₁ : ENNReal)) =
                  (((num : NNReal) / (ε₁ : NNReal) : NNReal) : ENNReal) := by
              simpa using
                (ENNReal.coe_div (p := (num : NNReal)) (r := (ε₁ : NNReal)) hε₁NN.ne').symm
            have hdiv₂ :
                ((((num : NNReal) / (ε₁ : NNReal) : NNReal) : ENNReal)) =
                  ENNReal.ofReal (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) := by
              simpa using
                (ENNReal.coe_nnreal_eq ((num : NNReal) / (ε₁ : NNReal)))
            exact hdiv₁.trans hdiv₂
          have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
          have hnum_nonneg : 0 ≤ (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) := by positivity
          have hsq :
              (((num : ENNReal) / (ε₁ : ENNReal)) ^ 2)
                = ENNReal.ofReal ((((num : ℕ+) : ℝ) / (ε₁ : ℝ)) ^ 2) := by
            rw [pow_two, hdiv, ← ENNReal.ofReal_mul hnum_nonneg]
            simp [pow_two]
          have hD :
              D = ENNReal.ofReal (2 * (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) ^ 2) := by
            change ((2 : ENNReal) * (((num : ENNReal) / (ε₁ : ENNReal)) ^ 2) : ENNReal) =
              ENNReal.ofReal (2 * (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) ^ 2)
            rw [hsq, show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul htwo_nonneg]
          have hDpos : 0 < 2 * (((num : ℕ+) : ℝ) / (ε₁ : ℝ)) ^ 2 := by
            have hnumNN : (0 : NNReal) < (num : NNReal) := by
              change (0 : NNReal) < ((num : ℕ) : NNReal)
              simp
            have hnumpos : 0 < ((num : ℕ+) : ℝ) / (ε₁ : ℝ) := by
              exact div_pos (by exact_mod_cast hnumNN) hε₁
            nlinarith [sq_pos_of_pos hnumpos]
          rw [hD, ← ENNReal.ofReal_div_of_pos hDpos, ← ENNReal.ofReal_mul hα_nonneg]
          apply congrArg ENNReal.ofReal
          have hmulNN : ((num : ℕ+) : NNReal) = (Δ : NNReal) * (ε₂ : NNReal) := by
            change ((((Δ * ε₂ : ℕ+) : ℕ) : NNReal)) =
              (((Δ : ℕ) : NNReal) * ((ε₂ : ℕ) : NNReal))
            norm_num
          have hmul : ((num : ℕ+) : ℝ) = (Δ : ℝ) * (ε₂ : ℝ) := by
            exact_mod_cast hmulNN
          rw [hmul, NNReal.coe_div]
          field_simp [hΔ.ne', hε₁.ne', hε₂.ne']

section Correlated

variable [DecidableEq ι] [Inhabited ι]

/-- Query lifted with a shared center coordinate. -/
def correlatedRegularLift
    (center : List T → ℤ) (query : List T → (ι → ℤ)) :
    List T → (Option ι → ℤ)
  | l, none => center l
  | l, some i => query l i - center l

/-- Recover the original vector by re-adding the shared center coordinate. -/
def correlatedRegularUnlift (x : Option ι → ℤ) : ι → ℤ :=
  fun i => x (some i) + x none

def correlatedRegularCombine (z : ℤ × (ι → ℤ)) : ι → ℤ :=
  fun i => z.2 i + z.1

lemma correlatedRegularUnlift_optionFunEquiv_symm :
    correlatedRegularUnlift ∘ (optionFunEquiv (α := ι) ℤ).symm = correlatedRegularCombine := by
  funext z
  funext i
  rfl

def regularCorrelatedSensitivityL1
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ, ∃ κ : ℤ,
      (∑ i, Int.natAbs (τ i)) ≤ Δ ∧
      AdditiveNoiseSpace.commonComponent κ τ ∧
      (κ = center l₁ - center l₂) ∧
      (∀ i, τ i = query l₁ i - query l₂ i)

def regularCorrelatedSensitivityL2
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ : ℕ+) : Prop :=
  ∀ l₁ l₂, Neighbour l₁ l₂ →
    ∃ τ : ι → ℤ, ∃ κ : ℤ,
      (∑ i, (Int.natAbs (τ i)) ^ 2) ≤ Δ ^ 2 ∧
      AdditiveNoiseSpace.commonComponent κ τ ∧
      (κ = center l₁ - center l₂) ∧
      (∀ i, τ i = query l₁ i - query l₂ i)

lemma correlatedRegularLift_sensitivityL1
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ : ℕ+)
    (hquery : regularCorrelatedSensitivityL1 center query Δ) :
    regularSensitivityL1 (correlatedRegularLift center query) Δ := by
  intro l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, κ, hτ, hcommon, hk, hdiff⟩
  refine ⟨AdditiveNoiseSpace.liftWitness κ τ, ?_, ?_, ?_⟩
  · exact le_trans (commonComponent_l1_bound κ τ hcommon) hτ
  · trivial
  · intro j
    cases j with
    | none =>
        simpa [correlatedRegularLift, hk, AdditiveNoiseSpace.liftWitness, regularSpace]
    | some i =>
        calc
          AdditiveNoiseSpace.liftWitness κ τ (some i) = τ i - κ := by rfl
          _ = (query l₁ i - query l₂ i) - (center l₁ - center l₂) := by rw [hdiff i, hk]
          _ = (query l₁ i - center l₁) - (query l₂ i - center l₂) := by ring

lemma correlatedRegularLift_sensitivityL2
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ : ℕ+)
    (hquery : regularCorrelatedSensitivityL2 center query Δ) :
    regularSensitivityL2 (correlatedRegularLift center query) Δ := by
  intro l₁ l₂ hneigh
  rcases hquery l₁ l₂ hneigh with ⟨τ, κ, hτ, hcommon, hk, hdiff⟩
  refine ⟨AdditiveNoiseSpace.liftWitness κ τ, ?_, ?_, ?_⟩
  · exact le_trans (commonComponent_l2_bound κ τ hcommon) hτ
  · trivial
  · intro j
    cases j with
    | none =>
        simpa [correlatedRegularLift, hk, AdditiveNoiseSpace.liftWitness, regularSpace]
    | some i =>
        calc
          AdditiveNoiseSpace.liftWitness κ τ (some i) = τ i - κ := by rfl
          _ = (query l₁ i - query l₂ i) - (center l₁ - center l₂) := by rw [hdiff i, hk]
          _ = (query l₁ i - center l₁) - (query l₂ i - center l₂) := by ring

/-- Proof helper: correlated regular finite-dimensional discrete-Laplace mechanism
as a lifted additive query followed by postprocessing. -/
private def privNoisedQueryPureVecCorrLifted
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  privPostProcess
    (privAdditiveQuery discreteLaplaceVecPMF (correlatedRegularLift center query) Δ ε₁ ε₂)
    correlatedRegularUnlift
    l
/-- Correlated regular finite-dimensional discrete-Laplace mechanism:
sample a shared scalar and a residual vector, then add them. -/
def privNoisedQueryPureVecCorr
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  (prodPMF
    (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ (center l))
    (discreteLaplaceVecPMF (Δ * ε₂) ε₁ (fun i => query l i - center l))).map
    correlatedRegularCombine

/-- Proof helper: correlated regular finite-dimensional discrete-Gaussian mechanism
as a lifted additive query followed by postprocessing. -/
private def privNoisedQueryVecCorrLifted
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  privPostProcess
    (privAdditiveQuery discreteGaussianVecPMF (correlatedRegularLift center query) Δ ε₁ ε₂)
    correlatedRegularUnlift
    l
/-- Correlated regular finite-dimensional discrete-Gaussian mechanism:
sample a shared scalar and a residual vector, then add them. -/
def privNoisedQueryVecCorr
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (l : List T) : PMF (ι → ℤ) :=
  (prodPMF
    (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ (center l))
    (discreteGaussianVecPMF (Δ * ε₂) ε₁ (fun i => query l i - center l))).map
    correlatedRegularCombine

@[simp] private lemma privNoisedQueryPureVecCorrLifted_eq
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryPureVecCorrLifted center query Δ ε₁ ε₂ l =
      privNoisedQueryPureVecCorr center query Δ ε₁ ε₂ l := by
  calc
    privNoisedQueryPureVecCorrLifted center query Δ ε₁ ε₂ l
        = (discreteLaplaceVecPMF (Δ * ε₂) ε₁ (correlatedRegularLift center query l)).map
            correlatedRegularUnlift := by
              rw [privNoisedQueryPureVecCorrLifted, privPostProcess]
              simpa [privAdditiveQuery] using
                (PMF.bind_pure_comp
                  (p := discreteLaplaceVecPMF (Δ * ε₂) ε₁ (correlatedRegularLift center query l))
                  (f := correlatedRegularUnlift))
    _ = ((prodPMF
          (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
          (discreteLaplaceVecPMF (Δ * ε₂) ε₁
            (fun i => (correlatedRegularLift center query l) (some i)))).map
          (optionFunEquiv (α := ι) ℤ).symm).map correlatedRegularUnlift := by
            rw [discreteLaplaceVecPMF_option]
    _ = (prodPMF
          (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
          (discreteLaplaceVecPMF (Δ * ε₂) ε₁
            (fun i => (correlatedRegularLift center query l) (some i)))).map
          (correlatedRegularUnlift ∘ (optionFunEquiv (α := ι) ℤ).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
                  (discreteLaplaceVecPMF (Δ * ε₂) ε₁
                    (fun i => (correlatedRegularLift center query l) (some i))))
                (f := (optionFunEquiv (α := ι) ℤ).symm)
                (g := correlatedRegularUnlift))
    _ = privNoisedQueryPureVecCorr center query Δ ε₁ ε₂ l := by
            simp [privNoisedQueryPureVecCorr, correlatedRegularLift,
              correlatedRegularUnlift_optionFunEquiv_symm]

@[simp] private lemma privNoisedQueryVecCorrLifted_eq
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) (l : List T) :
    privNoisedQueryVecCorrLifted center query Δ ε₁ ε₂ l =
      privNoisedQueryVecCorr center query Δ ε₁ ε₂ l := by
  calc
    privNoisedQueryVecCorrLifted center query Δ ε₁ ε₂ l
        = (discreteGaussianVecPMF (Δ * ε₂) ε₁ (correlatedRegularLift center query l)).map
            correlatedRegularUnlift := by
              rw [privNoisedQueryVecCorrLifted, privPostProcess]
              simpa [privAdditiveQuery] using
                (PMF.bind_pure_comp
                  (p := discreteGaussianVecPMF (Δ * ε₂) ε₁ (correlatedRegularLift center query l))
                  (f := correlatedRegularUnlift))
    _ = ((prodPMF
          (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
          (discreteGaussianVecPMF (Δ * ε₂) ε₁
            (fun i => (correlatedRegularLift center query l) (some i)))).map
          (optionFunEquiv (α := ι) ℤ).symm).map correlatedRegularUnlift := by
            rw [discreteGaussianVecPMF_option]
    _ = (prodPMF
          (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
          (discreteGaussianVecPMF (Δ * ε₂) ε₁
            (fun i => (correlatedRegularLift center query l) (some i)))).map
          (correlatedRegularUnlift ∘ (optionFunEquiv (α := ι) ℤ).symm) := by
            simpa using
              (PMF.map_comp
                (p := prodPMF
                  (DiscreteGaussianGenPMF (Δ * ε₂) ε₁ ((correlatedRegularLift center query l) none))
                  (discreteGaussianVecPMF (Δ * ε₂) ε₁
                    (fun i => (correlatedRegularLift center query l) (some i))))
                (f := (optionFunEquiv (α := ι) ℤ).symm)
                (g := correlatedRegularUnlift))
    _ = privNoisedQueryVecCorr center query Δ ε₁ ε₂ l := by
            simp [privNoisedQueryVecCorr, correlatedRegularLift,
              correlatedRegularUnlift_optionFunEquiv_symm]

end Correlated

theorem privNoisedQueryPureVec_DP
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : regularSensitivityL1 query Δ) :
    PureDP (privNoisedQueryPureVec query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  have hdp := privAdditiveQuery_DP
    (space := regularSpace (ι := ι))
    (noise := discreteLaplaceVecPMF)
    (hnoise := by
      intro Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hdiff r
      simpa using discreteLaplaceVec_DP_singleton Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hdiff r)
    query Δ ε₁ ε₂ hquery
  simpa [privNoisedQueryPureVec, privAdditiveQuery] using hdp

theorem privNoisedQueryPureVecCorr_DP
    [DecidableEq ι] [Inhabited ι]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : regularCorrelatedSensitivityL1 center query Δ) :
    PureDP (privNoisedQueryPureVecCorr center query Δ ε₁ ε₂) (((ε₁ : NNReal) / ε₂ : NNReal)) := by
  have hlifted :
      PureDP (privNoisedQueryPureVecCorrLifted center query Δ ε₁ ε₂)
        (((ε₁ : NNReal) / ε₂ : NNReal)) := by
    apply PureDP_PostProcess
    exact privNoisedQueryPureVec_DP
      (correlatedRegularLift center query) Δ ε₁ ε₂
      (correlatedRegularLift_sensitivityL1 center query Δ hquery)
  rw [PureDP, DP] at hlifted ⊢
  intro l₁ l₂ hneigh S
  simpa [privNoisedQueryPureVecCorrLifted_eq] using hlifted l₁ l₂ hneigh S

def privNoisedQueryVec_AC
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+) :
    ACNeighbour (privNoisedQueryVec query Δ ε₁ ε₂) := by
  have hac := privAdditiveQuery_AC
    (noise := discreteGaussianVecPMF)
    (hnoise := discreteGaussianVec_AC)
    query Δ ε₁ ε₂
  simpa [privNoisedQueryVec, privAdditiveQuery] using hac

theorem privNoisedQueryVec_zCDP
    (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : regularSensitivityL2 query Δ) :
    zCDP (privNoisedQueryVec query Δ ε₁ ε₂)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  have hzcdp := privAdditiveQuery_zCDP
    (space := regularSpace (ι := ι))
    (noise := discreteGaussianVecPMF)
    (hac := discreteGaussianVec_AC)
    (hnoise := by
      intro α hα Δ' ε₁' ε₂' μ₁ μ₂ τ _ hτ hdiff
      simpa using
        discreteGaussianVec_zCDPBound_pointwise α hα Δ' ε₁' ε₂' μ₁ μ₂ τ hτ hdiff)
    query Δ ε₁ ε₂ hquery
  simpa [privNoisedQueryVec, privAdditiveQuery] using hzcdp

theorem privNoisedQueryVecCorr_zCDP
    [DecidableEq ι] [Inhabited ι]
    [MeasurableSpace T] [MeasurableSingletonClass T]
    (center : List T → ℤ) (query : List T → (ι → ℤ)) (Δ ε₁ ε₂ : ℕ+)
    (hquery : regularCorrelatedSensitivityL2 center query Δ) :
    zCDP (privNoisedQueryVecCorr center query Δ ε₁ ε₂)
      ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
  have hlifted :
      zCDP (privNoisedQueryVecCorrLifted center query Δ ε₁ ε₂)
        ((1 / 2 : NNReal) * (((ε₁ : NNReal) / ε₂ : NNReal) ^ 2)) := by
    apply privPostProcess_zCDP
    exact privNoisedQueryVec_zCDP
      (correlatedRegularLift center query) Δ ε₁ ε₂
      (correlatedRegularLift_sensitivityL2 center query Δ hquery)
  rcases hlifted with ⟨hac, hbound⟩
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ hneigh
    simpa [privNoisedQueryVecCorrLifted_eq] using hac l₁ l₂ hneigh
  · intro α hα l₁ l₂ hneigh
    simpa [privNoisedQueryVecCorrLifted_eq] using hbound α hα l₁ l₂ hneigh

end SLang
