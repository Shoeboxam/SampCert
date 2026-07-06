/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenDP contributors
-/

import SampCert.Samplers.RoundedGaussian.Basic
import SampCert.DifferentialPrivacy.RenyiDivergence
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import SampCert.Samplers.BernoulliNegativeExponential.Properties
import SampCert.Samplers.GaussianGen.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Rounded Gaussian proof obligations

This file records the proof shape for the finite-native rounded Gaussian
sampler.  The main theorem is deliberately abstract: once local sampler and
finalization obligations are discharged, the global RDP accounting should not
depend on the low-level sampler implementation.

The existing SampCert proofs for discrete Gaussian and Bernoulli
negative-exponential samplers are imported here as intended proof dependencies.
They prove exact distribution/normalization facts.  The rounded native path
adds finite-budget lemmas around those primitives: comparison-prefix tails,
capped Bernoulli-factory depth, and finalization comb soundness.
-/

noncomputable section

open Classical Real

namespace SLang
namespace RoundedGaussian

variable {Ω : Type}

/-- RDP upper bound as used elsewhere in SampCert. -/
def RDPLe (p q : PMF Ω) (α : ℝ) (ε : EReal) : Prop :=
  RenyiDivergence_def p q α ≤ ε

/-- The unlogged Renyi divergence sum. -/
def renyiSum (p q : PMF Ω) (α : ℝ) : ENNReal :=
  ∑' x : Ω, (p x)^α * (q x)^(1 - α)

/-- Deterministic postprocessing cannot increase the unlogged Renyi sum.  This
is the support-space-to-output-space bridge used by the rounded sampler: once
the finite-budget proof is carried out over exact traces, rounding by a
deterministic lattice map preserves the same RDP bound.

The proof reuses SampCert's zCDP postprocessing fiber/Jensen lemma by
instantiating it with the two-list mechanism `[] ↦ p`, `[()] ↦ q`. -/
theorem renyiSum_map_le
    {U V : Type}
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U] [Inhabited U]
    (f : U → V)
    (p q : PMF U)
    {α : ℝ}
    (hα : 1 < α)
    (hpq : AbsCts p q)
    (hqp : AbsCts q p) :
    renyiSum (PMF.map f p) (PMF.map f q) α ≤ renyiSum p q α := by
  unfold renyiSum
  let nq : List Unit → PMF U := fun l => if l = [] then p else q
  have hnq_nil : nq [] = p := by simp [nq]
  have hnq_single : nq [()] = q := by simp [nq]
  have hnorm : ∀ l, HasSum (nq l) 1 := by
    intro l
    by_cases hl : l = []
    · simp [nq, hl, PMF.hasSum_coe_one]
    · simp [nq, hl, PMF.hasSum_coe_one]
  have hpre :=
    privPostPocess_DP_pre (nq := nq) hnorm f hα
      (Neighbour.Addition (a := []) (b := []) (n := ()) rfl rfl)
      (by simpa [hnq_nil, hnq_single] using hpq)
      (by simpa [hnq_nil, hnq_single] using hqp)
  simpa [PMF.map_apply, hnq_nil, hnq_single] using hpre

/-- Probability mass of a public event under a PMF. -/
def eventMass (p : PMF Ω) (s : Set Ω) : ENNReal :=
  ∑' x : Ω, s.indicator p x

theorem eventMass_ne_top (p : PMF Ω) (s : Set Ω) :
    eventMass p s ≠ ⊤ := by
  exact p.tsum_coe_indicator_ne_top s

theorem eventMass_le_one (p : PMF Ω) (s : Set Ω) :
    eventMass p s ≤ 1 := by
  unfold eventMass
  calc
    (∑' x : Ω, s.indicator p x)
        ≤ ∑' x : Ω, p x :=
          ENNReal.tsum_le_tsum (fun x => Set.indicator_apply_le fun _ => le_rfl)
    _ = 1 := p.tsum_coe

theorem eventMass_add_compl (p : PMF Ω) (s : Set Ω) :
    eventMass p s + eventMass p sᶜ = 1 := by
  unfold eventMass
  rw [← ENNReal.tsum_add]
  have hpoint :
      (fun x => s.indicator p x + sᶜ.indicator p x) = p := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_notMem (by simpa using hx)]
      simp
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_mem (by simpa using hx)]
      simp
  rw [hpoint, p.tsum_coe]

theorem eventMass_eq_one_sub_compl (p : PMF Ω) (s : Set Ω) :
    eventMass p s = 1 - eventMass p sᶜ :=
  ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (eventMass_add_compl p s)

/-- A public upper bound on the rejected/complement event gives a lower bound
on the retained event. -/
theorem eventMass_lower_of_compl_upper
    {p : PMF Ω}
    {s : Set Ω}
    {δ : ℝ}
    (hδ_nonneg : 0 ≤ δ)
    (hcompl : eventMass p sᶜ ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (1 - δ) ≤ eventMass p s := by
  rw [eventMass_eq_one_sub_compl]
  rw [ENNReal.ofReal_sub 1 hδ_nonneg]
  simp only [ENNReal.ofReal_one]
  exact tsub_le_tsub_left hcompl 1

theorem eventMass_pos_of_filterable
    {p : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support) :
    0 < eventMass p s := by
  rcases h with ⟨x, hx, hpx⟩
  exact lt_of_lt_of_le
    (by
      rw [PMF.apply_pos_iff]
      exact hpx)
    (by
      unfold eventMass
      calc
        p x = s.indicator p x := by
          rw [Set.indicator_of_mem hx]
        _ ≤ ∑' y : Ω, s.indicator p y := ENNReal.le_tsum x)

theorem eventMass_filterable_of_pos
    {p : PMF Ω}
    {s : Set Ω}
    (hpos : 0 < eventMass p s) :
    ∃ x ∈ s, x ∈ p.support := by
  by_contra h
  push_neg at h
  have hzero : eventMass p s = 0 := by
    unfold eventMass
    rw [ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact (p.apply_eq_zero_iff x).mpr (h x hx)
    · rw [Set.indicator_of_notMem hx]
  exact hpos.ne' hzero

theorem eventMass_filterable_of_lower
    {p : PMF Ω}
    {s : Set Ω}
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s) :
    ∃ x ∈ s, x ∈ p.support :=
  eventMass_filterable_of_pos
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlambda_pos) hlambda_le)

theorem filter_apply_le_eventMass_inv_mul
    {p : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    (x : Ω) :
    p.filter s h x ≤ (eventMass p s)⁻¹ * p x := by
  rw [PMF.filter_apply]
  unfold eventMass
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    rw [mul_comm]
  · rw [Set.indicator_of_notMem hx, zero_mul]
    exact zero_le _

theorem eventMass_inv_le_ofReal_inv
    {p : PMF Ω}
    {s : Set Ω}
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s) :
    (eventMass p s)⁻¹ ≤ ENNReal.ofReal (lambda⁻¹) := by
  calc
    (eventMass p s)⁻¹
        ≤ (ENNReal.ofReal lambda)⁻¹ := ENNReal.inv_le_inv' hlambda_le
    _ = ENNReal.ofReal (lambda⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos hlambda_pos]

/-- If a public retained event has mass at least `lambda`, filtering by that
event can inflate any point probability by at most `1 / lambda`. -/
theorem filter_apply_le_of_eventMass_lower
    {p : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (x : Ω) :
    p.filter s h x ≤ ENNReal.ofReal (lambda⁻¹) * p x := by
  calc
    p.filter s h x
        ≤ (eventMass p s)⁻¹ * p x :=
          filter_apply_le_eventMass_inv_mul h x
    _ = p x * (eventMass p s)⁻¹ := by
          rw [mul_comm]
    _ ≤ p x * ENNReal.ofReal (lambda⁻¹) := by
          exact mul_le_mul_right
            (eventMass_inv_le_ofReal_inv hlambda_pos hlambda_le) (p x)
    _ = ENNReal.ofReal (lambda⁻¹) * p x := by
          rw [mul_comm]

private lemma Real.exp_alpha_log_one_div_eq_rpow_neg
    {α lambda : ℝ}
    (hlambda_pos : 0 < lambda) :
    Real.exp (α * log (1 / lambda)) = lambda ^ (-α) := by
  rw [one_div, log_inv, Real.rpow_def_of_pos hlambda_pos]
  congr 1
  ring

private lemma ofReal_exp_alpha_log_one_div_eq_rpow_neg
    {α lambda : ℝ}
    (hlambda_pos : 0 < lambda) :
    ENNReal.ofReal (Real.exp (α * log (1 / lambda))) =
      (ENNReal.ofReal lambda) ^ (-α) := by
  rw [Real.exp_alpha_log_one_div_eq_rpow_neg hlambda_pos,
    ENNReal.ofReal_rpow_of_pos hlambda_pos]

private lemma ofReal_exp_conditioningFactor
    {α lambda : ℝ}
    (hα : 1 < α)
    (hlambda_pos : 0 < lambda) :
    ENNReal.ofReal
        (Real.exp ((α - 1) * (α * (α - 1)⁻¹ * log (1 / lambda)))) =
      (ENNReal.ofReal lambda) ^ (-α) := by
  have hα_ne : α - 1 ≠ 0 := by linarith
  rw [show (α - 1) * (α * (α - 1)⁻¹ * log (1 / lambda)) =
      α * log (1 / lambda) by
        field_simp [hα_ne]]
  exact ofReal_exp_alpha_log_one_div_eq_rpow_neg hlambda_pos

/-- Filtering the left-hand distribution by a public event with retained mass
at least `lambda` inflates the `α` power at a point by at most `lambda^{-α}`. -/
theorem filter_apply_rpow_le_of_eventMass_lower
    {p : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (hα_nonneg : 0 ≤ α)
    (x : Ω) :
    (p.filter s h x)^α ≤
      (ENNReal.ofReal lambda)^(-α) * (p x)^α := by
  have hfilter :
      p.filter s h x ≤ ENNReal.ofReal (lambda⁻¹) * p x :=
    filter_apply_le_of_eventMass_lower h hlambda_pos hlambda_le x
  calc
    (p.filter s h x)^α
        ≤ (ENNReal.ofReal (lambda⁻¹) * p x)^α :=
          ENNReal.rpow_le_rpow hfilter hα_nonneg
    _ = (ENNReal.ofReal (lambda⁻¹))^α * (p x)^α := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα_nonneg]
    _ = (ENNReal.ofReal lambda)^(-α) * (p x)^α := by
          rw [ENNReal.ofReal_inv_of_pos hlambda_pos,
            ENNReal.inv_rpow, ← ENNReal.rpow_neg]

/-- Pointwise Renyi-density bound for filtering the left-hand distribution. -/
theorem filter_left_renyiTerm_le_of_eventMass_lower
    {p q : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (hα_nonneg : 0 ≤ α)
    (x : Ω) :
    (p.filter s h x)^α * (q x)^(1 - α) ≤
      (ENNReal.ofReal lambda)^(-α) * ((p x)^α * (q x)^(1 - α)) := by
  calc
    (p.filter s h x)^α * (q x)^(1 - α)
        = (q x)^(1 - α) * (p.filter s h x)^α := by
          rw [mul_comm]
    _ ≤ (q x)^(1 - α) * ((ENNReal.ofReal lambda)^(-α) * (p x)^α) := by
          exact mul_le_mul_right
            (filter_apply_rpow_le_of_eventMass_lower h hlambda_pos hlambda_le
              hα_nonneg x)
            ((q x)^(1 - α))
    _ = (ENNReal.ofReal lambda)^(-α) * ((p x)^α * (q x)^(1 - α)) := by
          ac_rfl

/-- Renyi-sum bound for filtering the left-hand distribution.  This is the
normalization-cost core used by the public sampler-success and comb stages. -/
theorem filter_left_renyiSum_le_of_eventMass_lower
    {p q : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (hα_nonneg : 0 ≤ α) :
    renyiSum (p.filter s h) q α ≤
      (ENNReal.ofReal lambda)^(-α) * renyiSum p q α := by
  unfold renyiSum
  calc
    (∑' x : Ω, (p.filter s h x)^α * (q x)^(1 - α))
        ≤ ∑' x : Ω,
            (ENNReal.ofReal lambda)^(-α) * ((p x)^α * (q x)^(1 - α)) :=
          ENNReal.tsum_le_tsum
            (filter_left_renyiTerm_le_of_eventMass_lower h hlambda_pos
              hlambda_le hα_nonneg)
    _ = (ENNReal.ofReal lambda)^(-α) *
          ∑' x : Ω, (p x)^α * (q x)^(1 - α) := by
          rw [ENNReal.tsum_mul_left]

theorem filter_apply_ge_of_mem
    {p : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {x : Ω}
    (hx : x ∈ s) :
    p x ≤ p.filter s h x := by
  rw [PMF.filter_apply]
  rw [Set.indicator_of_mem hx]
  calc
    p x = p x * 1 := by rw [mul_one]
    _ ≤ p x * (∑' a', s.indicator p a')⁻¹ := by
          exact mul_le_mul_right
            (ENNReal.one_le_inv.mpr
              (by simpa [eventMass] using eventMass_le_one p s)) (p x)

private theorem ennreal_rpow_le_rpow_of_exponent_nonpos
    {x y : ENNReal}
    {z : ℝ}
    (hxy : x ≤ y)
    (hz : z ≤ 0) :
    y^z ≤ x^z := by
  have hneg : 0 ≤ -z := neg_nonneg.mpr hz
  calc
    y^z = y^(-(-z)) := by rw [neg_neg]
    _ = (y^(-z))⁻¹ := ENNReal.rpow_neg y (-z)
    _ ≤ (x^(-z))⁻¹ := ENNReal.inv_le_inv'
          (ENNReal.rpow_le_rpow hxy hneg)
    _ = x^(-(-z)) := (ENNReal.rpow_neg x (-z)).symm
    _ = x^z := by rw [neg_neg]

/-- Once the left-hand distribution has no mass outside the public event,
filtering the right-hand distribution by that same event only decreases the
Renyi sum for orders `α > 1`. -/
theorem filter_right_renyiTerm_le_of_support_subset
    {p q : PMF Ω}
    {s : Set Ω}
    (hq : ∃ x ∈ s, x ∈ q.support)
    {α : ℝ}
    (hα : 1 < α)
    (hp_zero : ∀ x, x ∉ s → p x = 0)
    (x : Ω) :
    (p x)^α * (q.filter s hq x)^(1 - α) ≤
      (p x)^α * (q x)^(1 - α) := by
  by_cases hx : x ∈ s
  · exact mul_le_mul_right
      (ennreal_rpow_le_rpow_of_exponent_nonpos
        (filter_apply_ge_of_mem hq hx)
        (by linarith))
      ((p x)^α)
  · rw [hp_zero x hx]
    simp [ENNReal.zero_rpow_of_pos (zero_lt_one.trans hα)]

theorem filter_right_renyiSum_le_of_support_subset
    {p q : PMF Ω}
    {s : Set Ω}
    (hq : ∃ x ∈ s, x ∈ q.support)
    {α : ℝ}
    (hα : 1 < α)
    (hp_zero : ∀ x, x ∉ s → p x = 0) :
    renyiSum p (q.filter s hq) α ≤ renyiSum p q α := by
  unfold renyiSum
  exact ENNReal.tsum_le_tsum
    (filter_right_renyiTerm_le_of_support_subset hq hα hp_zero)

/-- Conditioning both neighboring distributions on the same public event costs
only the left retained-mass factor. -/
theorem filter_both_renyiSum_le_of_eventMass_lower
    {p q : PMF Ω}
    {s : Set Ω}
    (hp : ∃ x ∈ s, x ∈ p.support)
    (hq : ∃ x ∈ s, x ∈ q.support)
    {lambda α : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (hα : 1 < α) :
    renyiSum (p.filter s hp) (q.filter s hq) α ≤
      (ENNReal.ofReal lambda)^(-α) * renyiSum p q α := by
  have hα_nonneg : 0 ≤ α := le_of_lt (zero_lt_one.trans hα)
  calc
    renyiSum (p.filter s hp) (q.filter s hq) α
        ≤ renyiSum (p.filter s hp) q α :=
          filter_right_renyiSum_le_of_support_subset hq hα
            (fun x hx => PMF.filter_apply_eq_zero_of_notMem hp hx)
    _ ≤ (ENNReal.ofReal lambda)^(-α) * renyiSum p q α :=
          filter_left_renyiSum_le_of_eventMass_lower hp hlambda_pos hlambda_le
            hα_nonneg

theorem renyiSum_le_of_pointwise
    {p₀ q₀ p q : PMF Ω}
    {α : ℝ}
    {factor : ENNReal}
    (hpointwise :
      ∀ x,
        (p x)^α * (q x)^(1 - α) ≤
          factor * ((p₀ x)^α * (q₀ x)^(1 - α))) :
    renyiSum p q α ≤ factor * renyiSum p₀ q₀ α := by
  unfold renyiSum
  calc
    (∑' x : Ω, (p x)^α * (q x)^(1 - α))
        ≤ ∑' x : Ω, factor * ((p₀ x)^α * (q₀ x)^(1 - α)) :=
          ENNReal.tsum_le_tsum hpointwise
    _ = factor * ∑' x : Ω, (p₀ x)^α * (q₀ x)^(1 - α) := by
          rw [ENNReal.tsum_mul_left]

/-- Output mass obtained by pushing support weights through a rounded output
map. -/
def roundedOutputMass
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (round : Support → lattice.Output)
    (weight : Support → ENNReal)
    (y : lattice.Output) : ENNReal :=
  letI := lattice.outputDecidableEq
  ∑' x : Support, if round x = y then weight x else 0

/-- Summing pushed-forward output masses is the same as summing the underlying
support weights. -/
theorem roundedOutputMass_tsum_eq_tsum_weight
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (round : Support → lattice.Output)
    (weight : Support → ENNReal) :
    (∑' y : lattice.Output, roundedOutputMass round weight y) =
      ∑' x : Support, weight x := by
  letI := lattice.outputDecidableEq
  calc
    ∑' y : lattice.Output, roundedOutputMass round weight y
        = ∑' y : lattice.Output,
            ∑' x : Support, if round x = y then weight x else 0 := rfl
    _ = ∑' x : Support,
            ∑' y : lattice.Output, if round x = y then weight x else 0 := by
          rw [ENNReal.tsum_comm]
    _ = ∑' x : Support, weight x := by
          apply tsum_congr
          intro x
          rw [tsum_eq_single (round x)]
          · simp
          · intro y hy
            by_cases h : round x = y
            · exact False.elim (hy h.symm)
            · simp [h]

/-- Pushing normalized support weights through a rounded output map preserves
total mass. -/
theorem roundedOutputMass_hasSum
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (round : Support → lattice.Output)
    (weight : Support → ENNReal)
    (hweight : HasSum weight 1) :
    HasSum (roundedOutputMass round weight) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  calc
    ∑' y : lattice.Output, roundedOutputMass round weight y
        = ∑' x : Support, weight x :=
          roundedOutputMass_tsum_eq_tsum_weight round weight
    _ = 1 := hweight.tsum_eq

/-- Constructor for rounded dyadic Gaussian laws from normalized support
weights.  This removes the need to separately prove that the output masses
normalize: normalization is just pushforward of `hweight`. -/
def RoundedDyadicGaussianLaw.ofNormalizedWeights
    {lattice : DyadicOutputLattice}
    (Support : Type)
    (point : Support → DyadicSupportPoint)
    (rejected : Support → Prop)
    (weight : Support → ENNReal)
    (hweight : HasSum weight 1)
    (hzero : ∀ x, rejected x → weight x = 0)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value) :
    RoundedDyadicGaussianLaw lattice where
  support := Support
  point := point
  round := fun x => lattice.round (point x).value
  rejected := rejected
  weight := weight
  outputMass := roundedOutputMass (fun x => lattice.round (point x).value) weight
  weight_zero_of_rejected := hzero
  round_eq_lattice_round := by intro x; rfl
  point_mem_round_cell := hcell
  outputMass_eq := by intro y; rfl
  hasSum_outputMass :=
    roundedOutputMass_hasSum (fun x => lattice.round (point x).value) weight hweight

/-- Constructor for rounded dyadic Gaussian laws obtained by conditioning a
raw support PMF on a public acceptance event, then rounding.  Rejected support
points are exactly those outside the event, and receive zero filtered mass. -/
def RoundedDyadicGaussianLaw.ofFilteredPMF
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value) :
    RoundedDyadicGaussianLaw lattice :=
  RoundedDyadicGaussianLaw.ofNormalizedWeights
    Support
    point
    (fun x => x ∉ accept)
    (fun x => raw.filter accept haccept x)
    (PMF.hasSum_coe_one (raw.filter accept haccept))
    (fun _ hx => PMF.filter_apply_eq_zero_of_notMem haccept hx)
    hcell

@[simp]
theorem RoundedDyadicGaussianLaw.ofFilteredPMF_weight
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value)
    (x : Support) :
    (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).weight x =
      raw.filter accept haccept x := rfl

@[simp]
theorem RoundedDyadicGaussianLaw.ofFilteredPMF_round
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value)
    (x : Support) :
    (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).round x =
      lattice.round (point x).value := rfl

/-- The support weights inside any rounded dyadic Gaussian law normalize to
one.  This follows from the law's output-mass equation and output
normalization. -/
theorem RoundedDyadicGaussianLaw.hasSum_weight
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) :
    HasSum law.weight 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  calc
    ∑' x : law.support, law.weight x
        = ∑' y : lattice.Output, roundedOutputMass law.round law.weight y :=
          (roundedOutputMass_tsum_eq_tsum_weight law.round law.weight).symm
    _ = ∑' y : lattice.Output, law.outputMass y := by
          apply tsum_congr
          intro y
          rw [law.outputMass_eq y]
          rfl
    _ = 1 := law.hasSum_outputMass.tsum_eq

/-- PMF on support points induced by a rounded dyadic Gaussian law. -/
def RoundedDyadicGaussianLaw.supportPMF
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) : PMF law.support :=
  ⟨law.weight, law.hasSum_weight⟩

/-- The rounded output PMF is the deterministic pushforward of the support PMF
through the law's rounding map. -/
theorem RoundedDyadicGaussianLaw.toPMF_eq_map_supportPMF
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) :
    law.toPMF = PMF.map law.round law.supportPMF := by
  letI := lattice.outputDecidableEq
  ext y
  change law.outputMass y = PMF.map law.round law.supportPMF y
  rw [PMF.map_apply, law.outputMass_eq y]
  apply tsum_congr
  intro x
  by_cases h : law.round x = y
  · simp [h]
    rfl
  · simp [h, ne_comm.mp h]

/-- The support PMF of `ofFilteredPMF` is exactly the filtered raw support
PMF. -/
theorem RoundedDyadicGaussianLaw.ofFilteredPMF_supportPMF_eq
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value) :
    (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).supportPMF =
      raw.filter accept haccept := by
  ext x
  rfl

/-- The output PMF of `ofFilteredPMF` is the rounded pushforward of the
filtered raw support PMF. -/
theorem RoundedDyadicGaussianLaw.ofFilteredPMF_toPMF_eq_map_filter
    {lattice : DyadicOutputLattice}
    {Support : Type}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value) :
    (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).toPMF =
      PMF.map
        (fun x => lattice.round (point x).value)
        (raw.filter accept haccept) := by
  rw [RoundedDyadicGaussianLaw.toPMF_eq_map_supportPMF]
  rw [RoundedDyadicGaussianLaw.ofFilteredPMF_supportPMF_eq]
  ext y
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  rfl

/-- The rounded law emits the deterministic pushforward of its own support
PMF. -/
theorem RoundedDyadicGaussianLaw.emits_map_supportPMF
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) :
    EmitsRoundedDyadicGaussian (PMF.map law.round law.supportPMF) law :=
  by
    constructor
    intro y
    exact congrFun (congrArg DFunLike.coe law.toPMF_eq_map_supportPMF) y |>.symm

/-- Semantic emission target for executable samplers: the implementation first
emits support points with exactly the law's weights, then deterministically
rounds them. -/
structure EmitsRoundedSupportWeights
    {lattice : DyadicOutputLattice}
    (algorithm : PMF lattice.Output)
    (law : RoundedDyadicGaussianLaw lattice) : Type where
  supportAlgorithm : PMF law.support
  support_apply_eq_weight : ∀ x, supportAlgorithm x = law.weight x
  algorithm_eq_map : algorithm = PMF.map law.round supportAlgorithm

theorem EmitsRoundedSupportWeights.supportAlgorithm_eq_supportPMF
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    {law : RoundedDyadicGaussianLaw lattice}
    (h : EmitsRoundedSupportWeights algorithm law) :
    h.supportAlgorithm = law.supportPMF := by
  ext x
  exact h.support_apply_eq_weight x

theorem EmitsRoundedSupportWeights.emitsRoundedDyadicGaussian
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    {law : RoundedDyadicGaussianLaw lattice}
    (h : EmitsRoundedSupportWeights algorithm law) :
    EmitsRoundedDyadicGaussian algorithm law := by
  constructor
  intro y
  have hmap :
      algorithm = PMF.map law.round law.supportPMF := by
    rw [h.algorithm_eq_map, h.supportAlgorithm_eq_supportPMF]
  have hpmf : law.toPMF = PMF.map law.round law.supportPMF :=
    law.toPMF_eq_map_supportPMF
  calc
    algorithm y = (PMF.map law.round law.supportPMF) y := by rw [hmap]
    _ = law.toPMF y := by rw [hpmf]
    _ = law.outputMass y := rfl

/-- Emission theorem for the filtered-support constructor.  This is the direct
semantic target for a public-resampling implementation: prove that the returned
output PMF is the rounded map of the filtered raw support PMF. -/
theorem emitsRoundedDyadicGaussian_ofFilteredPMF_map_filter
    {lattice : DyadicOutputLattice}
    {Support : Type}
    {algorithm : PMF lattice.Output}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value)
    (halg :
      algorithm =
        PMF.map
          (fun x => lattice.round (point x).value)
          (raw.filter accept haccept)) :
    EmitsRoundedDyadicGaussian algorithm
      (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell) := by
  constructor
  intro y
  have hpmf :
      (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).toPMF =
        PMF.map
          (fun x => lattice.round (point x).value)
          (raw.filter accept haccept) :=
    RoundedDyadicGaussianLaw.ofFilteredPMF_toPMF_eq_map_filter
      raw accept haccept point hcell
  calc
    algorithm y =
        (PMF.map
          (fun x => lattice.round (point x).value)
          (raw.filter accept haccept)) y := by rw [halg]
    _ = (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).toPMF y := by
        rw [hpmf]
    _ = (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell).outputMass y := rfl

/-- Support-weight version of the filtered-support emission theorem. -/
def emitsRoundedSupportWeights_ofFilteredPMF_map_filter
    {lattice : DyadicOutputLattice}
    {Support : Type}
    {algorithm : PMF lattice.Output}
    (raw : PMF Support)
    (accept : Set Support)
    (haccept : ∃ x ∈ accept, x ∈ raw.support)
    (point : Support → DyadicSupportPoint)
    (hcell :
      ∀ x,
        DyadicInterval.Contains
          (lattice.cell (lattice.round (point x).value))
          (point x).value)
    (halg :
      algorithm =
        PMF.map
          (fun x => lattice.round (point x).value)
          (raw.filter accept haccept)) :
    EmitsRoundedSupportWeights algorithm
      (RoundedDyadicGaussianLaw.ofFilteredPMF raw accept haccept point hcell) := by
  refine
    { supportAlgorithm := raw.filter accept haccept
      support_apply_eq_weight := ?_
      algorithm_eq_map := ?_ }
  · intro x
    rfl
  · rw [halg]
    ext y
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro x
    rfl

/-- Packaged semantic model for a native run that samples raw support points,
conditions on a public acceptance event, and rounds the accepted support point.
This is meant to be the local target for the executable sampler semantics. -/
structure FilteredSupportModel (lattice : DyadicOutputLattice) : Type 1 where
  Support : Type
  raw : PMF Support
  accept : Set Support
  accept_nonempty : ∃ x ∈ accept, x ∈ raw.support
  point : Support → DyadicSupportPoint
  point_mem_cell :
    ∀ x,
      DyadicInterval.Contains
        (lattice.cell (lattice.round (point x).value))
        (point x).value

/-- Rounded law induced by a filtered-support model. -/
def FilteredSupportModel.law
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) :
    RoundedDyadicGaussianLaw lattice :=
  RoundedDyadicGaussianLaw.ofFilteredPMF
    model.raw model.accept model.accept_nonempty
    model.point model.point_mem_cell

/-- Output PMF induced by a filtered-support model. -/
def FilteredSupportModel.outputPMF
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) : PMF lattice.Output :=
  PMF.map
    (fun x => lattice.round (model.point x).value)
    (model.raw.filter model.accept model.accept_nonempty)

/-- Any rounded law can be seen as a filtered-support model with the trivial
acceptance event.  This shows that `FilteredSupportModel` is a packaging layer,
not a stronger mathematical assumption. -/
def FilteredSupportModel.ofLaw
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) :
    FilteredSupportModel lattice where
  Support := law.support
  raw := law.supportPMF
  accept := Set.univ
  accept_nonempty := by
    rcases law.supportPMF.support_nonempty with ⟨x, hx⟩
    exact ⟨x, trivial, hx⟩
  point := law.point
  point_mem_cell := by
    intro x
    simpa [law.round_eq_lattice_round x] using law.point_mem_round_cell x

theorem FilteredSupportModel.law_toPMF_eq_outputPMF
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) :
    model.law.toPMF = model.outputPMF :=
  RoundedDyadicGaussianLaw.ofFilteredPMF_toPMF_eq_map_filter
    model.raw model.accept model.accept_nonempty
    model.point model.point_mem_cell

theorem FilteredSupportModel.law_supportPMF_eq_filter
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) :
    model.law.supportPMF =
      model.raw.filter model.accept model.accept_nonempty :=
  RoundedDyadicGaussianLaw.ofFilteredPMF_supportPMF_eq
    model.raw model.accept model.accept_nonempty
    model.point model.point_mem_cell

/-- A filtered-support model's canonical output PMF emits its rounded law. -/
theorem FilteredSupportModel.outputPMF_emits
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) :
    EmitsRoundedDyadicGaussian model.outputPMF model.law :=
  emitsRoundedDyadicGaussian_ofFilteredPMF_map_filter
    model.raw model.accept model.accept_nonempty
    model.point model.point_mem_cell rfl

/-- Support-weight emission for a filtered-support model's canonical output
PMF. -/
def FilteredSupportModel.outputPMF_emitsSupportWeights
    {lattice : DyadicOutputLattice}
    (model : FilteredSupportModel lattice) :
    EmitsRoundedSupportWeights model.outputPMF model.law :=
  emitsRoundedSupportWeights_ofFilteredPMF_map_filter
    model.raw model.accept model.accept_nonempty
    model.point model.point_mem_cell rfl

/-- If an implementation has the same output PMF as a filtered-support model,
then it emits the model's rounded law. -/
theorem FilteredSupportModel.emits_of_outputPMF_eq
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    (model : FilteredSupportModel lattice)
    (halg : algorithm = model.outputPMF) :
    EmitsRoundedDyadicGaussian algorithm model.law := by
  rw [halg]
  exact model.outputPMF_emits

/-- Every output mass of a rounded dyadic Gaussian law is a finite
sub-probability mass. -/
theorem RoundedDyadicGaussianLaw.outputMass_le_one
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice)
    (y : lattice.Output) :
    law.outputMass y ≤ 1 := by
  simpa [RoundedDyadicGaussianLaw.toPMF]
    using PMF.coe_le_one law.toPMF y

/-- Every output mass of a rounded dyadic Gaussian law is finite. -/
theorem RoundedDyadicGaussianLaw.outputMass_ne_top
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice)
    (y : lattice.Output) :
    law.outputMass y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (law.outputMass_le_one y)

/-- A support point's weight is included in the mass of the output it rounds
to. -/
theorem RoundedDyadicGaussianLaw.weight_le_outputMass_of_round
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice)
    (x : law.support)
    (y : lattice.Output)
    (hround : law.round x = y) :
    law.weight x ≤ law.outputMass y := by
  letI := lattice.outputDecidableEq
  rw [law.outputMass_eq y]
  change law.weight x ≤
    ∑' z : law.support, (if law.round z = y then law.weight z else 0)
  calc
    law.weight x = (if law.round x = y then law.weight x else 0) := by
      simp [hround]
    _ ≤ ∑' z : law.support,
        (if law.round z = y then law.weight z else 0) :=
        ENNReal.le_tsum x

/-- A support point's weight is included in the mass of its rounded output. -/
theorem RoundedDyadicGaussianLaw.weight_le_outputMass
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice)
    (x : law.support) :
    law.weight x ≤ law.outputMass (law.round x) :=
  law.weight_le_outputMass_of_round x (law.round x) rfl

/-- Pointwise equality between an implementation PMF and a rounded dyadic
Gaussian law lifts to equality of PMFs. -/
theorem pmf_eq_of_emitsRoundedDyadicGaussian
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    {law : RoundedDyadicGaussianLaw lattice}
    (h : EmitsRoundedDyadicGaussian algorithm law) :
    algorithm = law.toPMF := by
  ext y
  exact h.apply_eq_outputMass y

/-- PMF equality with a rounded dyadic Gaussian law is enough to establish the
algorithm-emission obligation. -/
theorem emitsRoundedDyadicGaussian_of_pmf_eq
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    {law : RoundedDyadicGaussianLaw lattice}
    (h : algorithm = law.toPMF) :
    EmitsRoundedDyadicGaussian algorithm law := by
  constructor
  intro y
  rw [h]
  rfl

/-- The rounded law's own PMF emits the law. -/
theorem emitsRoundedDyadicGaussian_toPMF
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) :
    EmitsRoundedDyadicGaussian law.toPMF law :=
  emitsRoundedDyadicGaussian_of_pmf_eq rfl

/-- Emission is exactly pointwise/PMF equality with the rounded law. -/
theorem emitsRoundedDyadicGaussian_iff_pmf_eq
    {lattice : DyadicOutputLattice}
    {algorithm : PMF lattice.Output}
    {law : RoundedDyadicGaussianLaw lattice} :
    EmitsRoundedDyadicGaussian algorithm law ↔ algorithm = law.toPMF :=
  ⟨pmf_eq_of_emitsRoundedDyadicGaussian, emitsRoundedDyadicGaussian_of_pmf_eq⟩

/-- RDP statement for two rounded dyadic Gaussian laws.  This is the second
major target after algorithm correctness: once the implementation is shown to
emit these laws, privacy is proved entirely at the dyadic PMF level. -/
def RoundedDyadicGaussianRDP
    {lattice : DyadicOutputLattice}
    (law₁ law₂ : RoundedDyadicGaussianLaw lattice)
    (α ε : ℝ) : Prop :=
  RDPLe law₁.toPMF law₂.toPMF α (ε : EReal)

/-- If two algorithms emit the corresponding rounded dyadic Gaussian laws, then
an RDP proof for those laws transfers to the algorithms. -/
theorem algorithmRDP_of_roundedDyadicGaussianRDP
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₁ law₂ : RoundedDyadicGaussianLaw lattice}
    {α ε : ℝ}
    (h₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (h₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hrdp : RoundedDyadicGaussianRDP law₁ law₂ α ε) :
    RDPLe algorithm₁ algorithm₂ α (ε : EReal) := by
  rw [pmf_eq_of_emitsRoundedDyadicGaussian h₁,
    pmf_eq_of_emitsRoundedDyadicGaussian h₂]
  exact hrdp

/-- RDP transfer from two filtered-support models to two implementations that
match those models' output PMFs. -/
theorem algorithmRDP_of_filteredSupportModels
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    (model₁ model₂ : FilteredSupportModel lattice)
    {α ε : ℝ}
    (halg₁ : algorithm₁ = model₁.outputPMF)
    (halg₂ : algorithm₂ = model₂.outputPMF)
    (hrdp : RoundedDyadicGaussianRDP model₁.law model₂.law α ε) :
    RDPLe algorithm₁ algorithm₂ α (ε : EReal) :=
  algorithmRDP_of_roundedDyadicGaussianRDP
    (model₁.emits_of_outputPMF_eq halg₁)
    (model₂.emits_of_outputPMF_eq halg₂)
    hrdp

/-- Algorithm RDP bridge from the support-weight semantic target. -/
theorem algorithmRDP_of_roundedSupportWeights
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₁ law₂ : RoundedDyadicGaussianLaw lattice}
    {α ε : ℝ}
    (hemits₁ : EmitsRoundedSupportWeights algorithm₁ law₁)
    (hemits₂ : EmitsRoundedSupportWeights algorithm₂ law₂)
    (hrdp : RoundedDyadicGaussianRDP law₁ law₂ α ε) :
    RDPLe algorithm₁ algorithm₂ α (ε : EReal) :=
  algorithmRDP_of_roundedDyadicGaussianRDP
    hemits₁.emitsRoundedDyadicGaussian
    hemits₂.emitsRoundedDyadicGaussian
    hrdp

/-- Named overhead for conditioning the left-hand distribution on a public
event with retained mass at least `lambda`. -/
def retainedMassOverhead (alpha lambda : ℝ) : ℝ :=
  alpha * (alpha - 1)⁻¹ * log (1 / lambda)

/-- The three normalization terms in the finite-budget theorem. -/
def finiteBudgetOverhead (α C lambdaS δb : ℝ) : ℝ :=
  (α - 1)⁻¹ * log (1 / C)
  + α * (α - 1)⁻¹ * log (1 / lambdaS)
  + α * (α - 1)⁻¹ * log (1 / (1 - δb))

/-- Concrete public bounds derived from a native profile.  `structuralTail`,
`samplerFailure`, and `combFailure` are probabilities, not RDP terms. -/
structure BudgetBounds where
  structuralTail : ℝ
  samplerFailure : ℝ
  combFailure : ℝ
  structuralTail_nonneg : 0 ≤ structuralTail
  samplerFailure_nonneg : 0 ≤ samplerFailure
  combFailure_nonneg : 0 ≤ combFailure
  structuralTail_lt_one : structuralTail < 1
  samplerFailure_lt_one : samplerFailure < 1
  combFailure_lt_one : combFailure < 1

def BudgetBounds.C (b : BudgetBounds) : ℝ := 1 - b.structuralTail
def BudgetBounds.lambdaS (b : BudgetBounds) : ℝ := 1 - b.samplerFailure
def BudgetBounds.δb (b : BudgetBounds) : ℝ := b.combFailure

theorem BudgetBounds.C_pos (b : BudgetBounds) : 0 < b.C := by
  unfold BudgetBounds.C
  linarith [b.structuralTail_lt_one]

theorem BudgetBounds.C_le_one (b : BudgetBounds) : b.C ≤ 1 := by
  unfold BudgetBounds.C
  linarith [b.structuralTail_nonneg]

theorem BudgetBounds.lambdaS_pos (b : BudgetBounds) : 0 < b.lambdaS := by
  unfold BudgetBounds.lambdaS
  linarith [b.samplerFailure_lt_one]

theorem BudgetBounds.lambdaS_le_one (b : BudgetBounds) : b.lambdaS ≤ 1 := by
  unfold BudgetBounds.lambdaS
  linarith [b.samplerFailure_nonneg]

theorem BudgetBounds.delta_nonneg (b : BudgetBounds) : 0 ≤ b.δb := by
  exact b.combFailure_nonneg

theorem BudgetBounds.one_sub_delta_pos (b : BudgetBounds) : 0 < 1 - b.δb := by
  unfold BudgetBounds.δb
  linarith [b.combFailure_lt_one]

theorem BudgetBounds.one_sub_delta_le_one (b : BudgetBounds) : 1 - b.δb ≤ 1 := by
  unfold BudgetBounds.δb
  linarith [b.combFailure_nonneg]

theorem BudgetBounds.samplerEventMass_lower_of_failureBound
    (b : BudgetBounds)
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hfailure :
      eventMass p samplerEventᶜ ≤ ENNReal.ofReal b.samplerFailure) :
    ENNReal.ofReal b.lambdaS ≤ eventMass p samplerEvent := by
  simpa [BudgetBounds.lambdaS]
    using eventMass_lower_of_compl_upper b.samplerFailure_nonneg hfailure

theorem BudgetBounds.combEventMass_lower_of_failureBound
    (b : BudgetBounds)
    {p : PMF Ω}
    {combEvent : Set Ω}
    (hfailure :
      eventMass p combEventᶜ ≤ ENNReal.ofReal b.δb) :
    ENNReal.ofReal (1 - b.δb) ≤ eventMass p combEvent := by
  exact eventMass_lower_of_compl_upper b.delta_nonneg hfailure

def structuralOverhead (α : ℝ) (bounds : BudgetBounds) : ℝ :=
  (α - 1)⁻¹ * log (1 / bounds.C)

def samplerSuccessOverhead (α : ℝ) (bounds : BudgetBounds) : ℝ :=
  retainedMassOverhead α bounds.lambdaS

def combOverhead (α : ℝ) (bounds : BudgetBounds) : ℝ :=
  retainedMassOverhead α (1 - bounds.δb)

private lemma log_one_div_nonneg_of_pos_le_one {x : ℝ}
    (hx_pos : 0 < x)
    (hx_le_one : x ≤ 1) :
    0 ≤ log (1 / x) := by
  have hone : 1 ≤ 1 / x := by
    rw [one_div]
    exact (one_le_inv₀ hx_pos).mpr hx_le_one
  exact log_nonneg hone

theorem structuralOverhead_nonneg
    {α : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds) :
    0 ≤ structuralOverhead α bounds := by
  unfold structuralOverhead
  exact mul_nonneg
    (inv_nonneg.mpr (sub_nonneg.mpr hα.le))
    (log_one_div_nonneg_of_pos_le_one (bounds.C_pos) (bounds.C_le_one))

theorem samplerSuccessOverhead_nonneg
    {α : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds) :
    0 ≤ samplerSuccessOverhead α bounds := by
  unfold samplerSuccessOverhead
  exact mul_nonneg
    (mul_nonneg (le_of_lt (zero_lt_one.trans hα))
      (inv_nonneg.mpr (sub_nonneg.mpr hα.le)))
    (log_one_div_nonneg_of_pos_le_one (bounds.lambdaS_pos) (bounds.lambdaS_le_one))

theorem combOverhead_nonneg
    {α : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds) :
    0 ≤ combOverhead α bounds := by
  unfold combOverhead
  exact mul_nonneg
    (mul_nonneg (le_of_lt (zero_lt_one.trans hα))
      (inv_nonneg.mpr (sub_nonneg.mpr hα.le)))
    (log_one_div_nonneg_of_pos_le_one
      (bounds.one_sub_delta_pos) (bounds.one_sub_delta_le_one))

theorem finiteBudgetOverhead_nonneg
    {α : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds) :
    0 ≤ finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb := by
  simpa [finiteBudgetOverhead, structuralOverhead, samplerSuccessOverhead,
    combOverhead, retainedMassOverhead, add_assoc]
    using add_nonneg
    (add_nonneg
      (structuralOverhead_nonneg hα bounds)
      (samplerSuccessOverhead_nonneg hα bounds))
    (combOverhead_nonneg hα bounds)

private lemma ofReal_exp_mul (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y) =
      ENNReal.ofReal (Real.exp (x + y)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg x), Real.exp_add]

private lemma finiteBudgetOverhead_exp_factor
    (α : ℝ) (bounds : BudgetBounds) :
    ENNReal.ofReal (Real.exp ((α - 1) * combOverhead α bounds)) *
        ENNReal.ofReal (Real.exp ((α - 1) * samplerSuccessOverhead α bounds)) *
        ENNReal.ofReal (Real.exp ((α - 1) * structuralOverhead α bounds)) =
      ENNReal.ofReal
        (Real.exp
          ((α - 1) * finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb)) := by
  rw [ofReal_exp_mul, ofReal_exp_mul]
  congr 1
  unfold finiteBudgetOverhead structuralOverhead samplerSuccessOverhead combOverhead
    retainedMassOverhead
  unfold BudgetBounds.C BudgetBounds.lambdaS BudgetBounds.δb
  ring_nf

private lemma finiteBudget_exp_mul_base
    (α ε overhead : ℝ) :
    ENNReal.ofReal (Real.exp ((α - 1) * overhead)) *
        ENNReal.eexp (((α : EReal) - 1) * (ε : EReal)) =
      ENNReal.eexp (((α : EReal) - 1) * ((ε + overhead : ℝ) : EReal)) := by
  change
    ENNReal.eexp (((α - 1) * overhead : ℝ) : EReal) *
        ENNReal.eexp (((α - 1) * ε : ℝ) : EReal) =
      ENNReal.eexp (((α - 1) * (ε + overhead) : ℝ) : EReal)
  rw [ENNReal.eexp_add]
  congr 1
  simp only [← EReal.coe_add]
  congr 1
  ring

private lemma ereal_mul_le_cancel_coe_pos
    {a : ℝ}
    (ha : 0 < a)
    {x y : EReal}
    (h : (a : EReal) * x ≤ (a : EReal) * y) :
    x ≤ y := by
  cases x <;> cases y
  · simp
  · simp
  · simp
  · simp_all [EReal.coe_mul_bot_of_pos ha, ← EReal.coe_mul]
  · rename_i x y
    simp only [← EReal.coe_mul, EReal.coe_le_coe_iff] at h ⊢
    nlinarith
  · exact le_top
  · simpa [EReal.coe_mul_top_of_pos ha, EReal.coe_mul_bot_of_pos ha] using h
  · rename_i y
    simp [EReal.coe_mul_top_of_pos ha, ← EReal.coe_mul] at h
  · simp

/-- Deterministic postprocessing preserves an RDP upper bound. -/
theorem RDPLe_map
    {U V : Type}
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U] [Inhabited U]
    (f : U → V)
    (p q : PMF U)
    {α : ℝ}
    {ε : EReal}
    (hα : 1 < α)
    (hpq : AbsCts p q)
    (hqp : AbsCts q p)
    (hrdp : RDPLe p q α ε) :
    RDPLe (PMF.map f p) (PMF.map f q) α ε := by
  have hcoeff_pos_real : 0 < α - 1 := sub_pos.mpr hα
  have hdiv :
      RenyiDivergence_def (PMF.map f p) (PMF.map f q) α ≤
        RenyiDivergence_def p q α := by
    apply ereal_mul_le_cancel_coe_pos hcoeff_pos_real
    rw [ENNReal.eexp_mono_le]
    change
      ENNReal.eexp (((α : EReal) - 1) *
          RenyiDivergence_def (PMF.map f p) (PMF.map f q) α) ≤
        ENNReal.eexp (((α : EReal) - 1) * RenyiDivergence_def p q α)
    rw [RenyiDivergence_def_exp (PMF.map f p) (PMF.map f q) hα]
    change
      (∑' x : V, (PMF.map f p x)^α * (PMF.map f q x)^(1 - α)) ≤
        ENNReal.eexp (((α : EReal) - 1) * RenyiDivergence_def p q α)
    rw [RenyiDivergence_def_exp p q hα]
    exact renyiSum_map_le f p q hα hpq hqp
  exact hdiv.trans hrdp

/-- A single Renyi-sum conditioning step with a named overhead. -/
structure RenyiSumOverhead
    (p₀ q₀ p q : PMF Ω)
    (overhead : ℝ → ℝ) : Prop where
  renyi_sum_le :
    ∀ {α : ℝ},
      1 < α →
      renyiSum p q α ≤
        ENNReal.ofReal (Real.exp ((α - 1) * overhead α)) *
          renyiSum p₀ q₀ α

theorem RenyiSumOverhead.of_pointwise
    {p₀ q₀ p q : PMF Ω}
    {overhead : ℝ → ℝ}
    (hpointwise :
      ∀ {α : ℝ},
        1 < α →
        ∀ x,
          (p x)^α * (q x)^(1 - α) ≤
            ENNReal.ofReal (Real.exp ((α - 1) * overhead α)) *
              ((p₀ x)^α * (q₀ x)^(1 - α))) :
    RenyiSumOverhead p₀ q₀ p q overhead := by
  constructor
  intro α hα
  exact renyiSum_le_of_pointwise (hpointwise hα)

/-- A retained-mass lower bound gives the exact Renyi overhead for conditioning
the left-hand distribution.  This theorem is intentionally local: sampler
success and comb rejection only need to prove the public event and its retained
mass bound. -/
theorem RenyiSumOverhead.filter_left_of_eventMass_lower
    {p q : PMF Ω}
    {s : Set Ω}
    (h : ∃ x ∈ s, x ∈ p.support)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s) :
    RenyiSumOverhead p q (p.filter s h) q
      (fun α => retainedMassOverhead α lambda) := by
  constructor
  intro α hα
  have hα_nonneg : 0 ≤ α := le_of_lt (zero_lt_one.trans hα)
  calc
    renyiSum (p.filter s h) q α
        ≤ (ENNReal.ofReal lambda)^(-α) * renyiSum p q α :=
          filter_left_renyiSum_le_of_eventMass_lower h hlambda_pos hlambda_le hα_nonneg
    _ = ENNReal.ofReal (Real.exp ((α - 1) * retainedMassOverhead α lambda)) *
          renyiSum p q α := by
          congr 1
          rw [retainedMassOverhead]
          exact (ofReal_exp_conditioningFactor hα hlambda_pos).symm

/-- Packaged same-public-event conditioning theorem.  Both neighboring PMFs are
filtered, but the Renyi overhead is only the retained-mass cost for the
left-hand PMF. -/
theorem RenyiSumOverhead.filter_both_of_eventMass_lower
    {p q : PMF Ω}
    {s : Set Ω}
    (hp : ∃ x ∈ s, x ∈ p.support)
    (hq : ∃ x ∈ s, x ∈ q.support)
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s) :
    RenyiSumOverhead p q (p.filter s hp) (q.filter s hq)
      (fun α => retainedMassOverhead α lambda) := by
  constructor
  intro α hα
  calc
    renyiSum (p.filter s hp) (q.filter s hq) α
        ≤ (ENNReal.ofReal lambda)^(-α) * renyiSum p q α :=
          filter_both_renyiSum_le_of_eventMass_lower hp hq hlambda_pos
            hlambda_le hα
    _ = ENNReal.ofReal (Real.exp ((α - 1) * retainedMassOverhead α lambda)) *
          renyiSum p q α := by
          congr 1
          rw [retainedMassOverhead]
          exact (ofReal_exp_conditioningFactor hα hlambda_pos).symm

/-- Same-public-event conditioning with the filter witnesses derived from mass
facts.  The left-hand lower bound determines the Renyi overhead; the right-hand
positive mass only makes `q.filter` well formed. -/
theorem RenyiSumOverhead.filter_both_of_eventMass_lower_and_pos
    {p q : PMF Ω}
    {s : Set Ω}
    {lambda : ℝ}
    (hlambda_pos : 0 < lambda)
    (hlambda_le : ENNReal.ofReal lambda ≤ eventMass p s)
    (hq_pos : 0 < eventMass q s) :
    RenyiSumOverhead
      p q
      (p.filter s (eventMass_filterable_of_lower hlambda_pos hlambda_le))
      (q.filter s (eventMass_filterable_of_pos hq_pos))
      (fun α => retainedMassOverhead α lambda) :=
  RenyiSumOverhead.filter_both_of_eventMass_lower
    (eventMass_filterable_of_lower hlambda_pos hlambda_le)
    (eventMass_filterable_of_pos hq_pos)
    hlambda_pos hlambda_le

/-- The finite-budget conditioning proof should be built by composing these
three stage lemmas. -/
structure FiniteBudgetConditioningStages
    (p₀ q₀ pK qK pS qS p q : PMF Ω)
    (bounds : BudgetBounds) : Prop where
  structural :
    RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds)
  samplerSuccess :
    RenyiSumOverhead pK qK pS qS (fun α => samplerSuccessOverhead α bounds)
  comb :
    RenyiSumOverhead pS qS p q (fun α => combOverhead α bounds)

/-- Construct the three finite-budget stages from the natural public-event
view: a structural stage, a sampler-success event, and a comb-acceptance event.

The sampler and comb stages are both same-event conditionings.  Their only
privacy cost is the lower bound on the retained mass of the left-hand law. -/
theorem finiteBudgetConditioningStages_of_publicEvents
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass (pK.filter samplerEvent hpSampler) combEvent) :
    FiniteBudgetConditioningStages
      p₀ q₀
      pK qK
      (pK.filter samplerEvent hpSampler)
      (qK.filter samplerEvent hqSampler)
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      bounds := by
  refine
    { structural := hstruct
      samplerSuccess := ?_
      comb := ?_ }
  · simpa [samplerSuccessOverhead]
      using RenyiSumOverhead.filter_both_of_eventMass_lower
        hpSampler hqSampler bounds.lambdaS_pos hsamplerMass
  · simpa [combOverhead]
      using RenyiSumOverhead.filter_both_of_eventMass_lower
        hpComb hqComb bounds.one_sub_delta_pos hcombMass

/-- Public-event stage constructor stated in terms of the failure/rejection
events: the complement of sampler success and the complement of comb
acceptance. -/
theorem finiteBudgetConditioningStages_of_publicEventFailures
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      eventMass pK samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    FiniteBudgetConditioningStages
      p₀ q₀
      pK qK
      (pK.filter samplerEvent hpSampler)
      (qK.filter samplerEvent hqSampler)
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      bounds :=
  finiteBudgetConditioningStages_of_publicEvents
    hstruct hpSampler hqSampler
    (bounds.samplerEventMass_lower_of_failureBound hsamplerFailure)
    hpComb hqComb
    (bounds.combEventMass_lower_of_failureBound hcombFailure)

/-- Public-event stage constructor where all filter witnesses are derived from
mass facts.  The quantitative lower bounds are only required on the left-hand
law; the right-hand law only needs positive retained mass so that its filters
are well formed. -/
theorem finiteBudgetConditioningStages_of_publicEventMasses
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hqSamplerMass_pos : 0 < eventMass qK samplerEvent)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass
          (pK.filter samplerEvent
            (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass))
          combEvent)
    (hqCombMass_pos :
      0 <
        eventMass
          (qK.filter samplerEvent
            (eventMass_filterable_of_pos hqSamplerMass_pos))
          combEvent) :
    FiniteBudgetConditioningStages
      p₀ q₀
      pK qK
      (pK.filter samplerEvent
        (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass))
      (qK.filter samplerEvent
        (eventMass_filterable_of_pos hqSamplerMass_pos))
      ((pK.filter samplerEvent
          (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass)).filter
        combEvent
        (eventMass_filterable_of_lower bounds.one_sub_delta_pos hcombMass))
      ((qK.filter samplerEvent
          (eventMass_filterable_of_pos hqSamplerMass_pos)).filter
        combEvent
        (eventMass_filterable_of_pos hqCombMass_pos))
      bounds := by
  exact finiteBudgetConditioningStages_of_publicEvents
    hstruct
    (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass)
    (eventMass_filterable_of_pos hqSamplerMass_pos)
    hsamplerMass
    (eventMass_filterable_of_lower bounds.one_sub_delta_pos hcombMass)
    (eventMass_filterable_of_pos hqCombMass_pos)
    hcombMass

/-- A concrete relationship between the base law and the final finite-budget
law, expressed at the Renyi-sum level.  This is the actionable middle theorem:
it should be proved from structural common normalization, sampler-success
conditioning, and public-comb rejection. -/
structure FiniteBudgetConditioning
    (p₀ q₀ p q : PMF Ω)
    (bounds : BudgetBounds) : Prop where
  renyi_sum_le :
    ∀ {α : ℝ},
      1 < α →
      renyiSum p q α ≤
        ENNReal.ofReal
          (Real.exp ((α - 1) * finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb))
        * renyiSum p₀ q₀ α

/-- Composes structural, sampler-success, and comb conditioning stages into the
single conditioning relation consumed by `finiteBudgetTerms`. -/
theorem finiteBudgetConditioning_of_stages
    {p₀ q₀ pK qK pS qS p q : PMF Ω}
    {bounds : BudgetBounds}
    (hstages : FiniteBudgetConditioningStages p₀ q₀ pK qK pS qS p q bounds) :
    FiniteBudgetConditioning p₀ q₀ p q bounds := by
  constructor
  intro α hα
  let A : ENNReal :=
    ENNReal.ofReal (Real.exp ((α - 1) * structuralOverhead α bounds))
  let B : ENNReal :=
    ENNReal.ofReal (Real.exp ((α - 1) * samplerSuccessOverhead α bounds))
  let C : ENNReal :=
    ENNReal.ofReal (Real.exp ((α - 1) * combOverhead α bounds))
  have hstruct :
      renyiSum pK qK α ≤ A * renyiSum p₀ q₀ α := by
    simpa [A] using hstages.structural.renyi_sum_le hα
  have hsampler :
      renyiSum pS qS α ≤ B * renyiSum pK qK α := by
    simpa [B] using hstages.samplerSuccess.renyi_sum_le hα
  have hcomb :
      renyiSum p q α ≤ C * renyiSum pS qS α := by
    simpa [C] using hstages.comb.renyi_sum_le hα
  calc
    renyiSum p q α
        ≤ C * renyiSum pS qS α := hcomb
    _ ≤ C * (B * renyiSum pK qK α) := by
        exact mul_le_mul_right hsampler C
    _ ≤ C * (B * (A * renyiSum p₀ q₀ α)) := by
        exact mul_le_mul_right (mul_le_mul_right hstruct B) C
    _ = (C * B * A) * renyiSum p₀ q₀ α := by
        ac_rfl
    _ = ENNReal.ofReal
          (Real.exp
            ((α - 1) * finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb))
          * renyiSum p₀ q₀ α := by
        congr 1
        simpa [A, B, C] using finiteBudgetOverhead_exp_factor α bounds

/-- Public-event version of finite-budget conditioning.  This is the most
direct theorem for the native proof once structural truncation, sampler-success
retained mass, and comb retained mass have been proved. -/
theorem finiteBudgetConditioning_of_publicEvents
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass (pK.filter samplerEvent hpSampler) combEvent) :
    FiniteBudgetConditioning
      p₀ q₀
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      bounds :=
  finiteBudgetConditioning_of_stages
    (finiteBudgetConditioningStages_of_publicEvents
      hstruct hpSampler hqSampler hsamplerMass hpComb hqComb hcombMass)

/-- Public-event finite-budget conditioning from upper bounds on sampler
failure and comb rejection. -/
theorem finiteBudgetConditioning_of_publicEventFailures
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      eventMass pK samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    FiniteBudgetConditioning
      p₀ q₀
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      bounds :=
  finiteBudgetConditioning_of_stages
    (finiteBudgetConditioningStages_of_publicEventFailures
      hstruct hpSampler hqSampler hsamplerFailure hpComb hqComb hcombFailure)

/-- Public-event finite-budget conditioning with filter witnesses derived from
mass facts. -/
theorem finiteBudgetConditioning_of_publicEventMasses
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {bounds : BudgetBounds}
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hqSamplerMass_pos : 0 < eventMass qK samplerEvent)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass
          (pK.filter samplerEvent
            (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass))
          combEvent)
    (hqCombMass_pos :
      0 <
        eventMass
          (qK.filter samplerEvent
            (eventMass_filterable_of_pos hqSamplerMass_pos))
          combEvent) :
    FiniteBudgetConditioning
      p₀ q₀
      ((pK.filter samplerEvent
          (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass)).filter
        combEvent
        (eventMass_filterable_of_lower bounds.one_sub_delta_pos hcombMass))
      ((qK.filter samplerEvent
          (eventMass_filterable_of_pos hqSamplerMass_pos)).filter
        combEvent
        (eventMass_filterable_of_pos hqCombMass_pos))
      bounds :=
  finiteBudgetConditioning_of_stages
    (finiteBudgetConditioningStages_of_publicEventMasses
      hstruct hsamplerMass hqSamplerMass_pos hcombMass hqCombMass_pos)

/-- Conservative comparison-failure bound used by the native profile. -/
def comparisonUndecidedBound (profile : NativeProfile) : ℝ :=
  4 * 2 ^ (-(profile.samplerBits : ℝ))

/-- Conservative decreasing-sequence tail for the capped Bernoulli factories. -/
def factoryDepthBound (profile : NativeProfile) : ℝ :=
  1 / ((Nat.factorial (profile.factoryDepth + 1) : ℕ) : ℝ)

/-- Primitive facts sufficient to instantiate the local rounded-native proof
obligations for any public profile.  These are where existing SampCert sampler
proofs should be connected to the finite-budget wrapper. -/
structure PrimitiveProofs
    (profile : NativeProfile)
    (lattice : DyadicOutputLattice)
    (spec : NativeSamplerSpec profile lattice) : Prop where
  psrn_comparison_undecided_bound :
    ∀ kind,
      comparisonUndecidedProbability profile kind ≤
        comparisonUndecidedBound profile
  bernoulli_factory_depth_bound :
    ∀ kind,
      factoryDepthFailureProbability profile kind ≤
        factoryDepthBound profile
  finalization_rejections_subset_public_comb :
    ∀ input trace,
      SupportCondition profile input →
      TraceWithinProfile profile trace →
      spec.finalize trace FinalizationResult.rejectedComb →
      InPublicComb profile input trace

/-- Local obligations that should be proved for the native sampler primitives.

The abstract probability hooks in `Basic.lean` should eventually be replaced by
the exact PSRN, Bernoulli-factory, and finalization semantics. -/
structure LocalObligations
    (profile : NativeProfile)
    (bounds : BudgetBounds)
    (lattice : DyadicOutputLattice)
    (spec : NativeSamplerSpec profile lattice) : Prop where
  structural_cap_declares_retained_law :
    bounds.C = 1 - bounds.structuralTail
  psrn_comparison_undecided_bound :
    ∀ kind,
      comparisonUndecidedProbability profile kind ≤
        comparisonUndecidedBound profile
  bernoulli_factory_depth_bound :
    ∀ kind,
      factoryDepthFailureProbability profile kind ≤
        factoryDepthBound profile
  finalization_rejections_subset_public_comb :
    ∀ input trace,
      SupportCondition profile input →
      TraceWithinProfile profile trace →
      spec.finalize trace FinalizationResult.rejectedComb →
      InPublicComb profile input trace
  resource_limits_fail_closed_or_declared :
    (∀ r, spec.attempt r → r = AttemptResult.resourceLimit → False) ∧
    (∀ trace r, spec.finalize trace r → r = FinalizationResult.resourceLimit → False)

/-- Primitive sampler and finalization facts imply the local obligations used by
the global finite-budget theorem. -/
theorem localObligations_of_primitiveProofs
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hprimitive : PrimitiveProofs profile lattice spec) :
    LocalObligations profile bounds lattice spec := by
  constructor
  · rfl
  · exact hprimitive.psrn_comparison_undecided_bound
  · exact hprimitive.bernoulli_factory_depth_bound
  · exact hprimitive.finalization_rejections_subset_public_comb
  · exact ⟨spec.attempt_resource_limits_fail_closed,
      spec.finalization_resource_limits_fail_closed⟩

/-- Abstract finite-budget accounting theorem.

`p₀,q₀` are the retained unnormalized-law distributions before sampler-success
conditioning and comb rejection. `p,q` are the final returned distributions.
The exact relationship between these PMFs is supplied by the conditioning
hypotheses, represented here by `LocalObligations` plus the named budget
parameters. -/
theorem finiteBudgetTerms
    {profile : NativeProfile}
    {p₀ q₀ p q : PMF Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (_hlocal : LocalObligations profile bounds lattice spec)
    (hconditioned : FiniteBudgetConditioning p₀ q₀ p q bounds) :
    RDPLe p q α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  let overhead : ℝ := finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb
  let coeff : EReal := (α : EReal) - 1
  let factor : ENNReal := ENNReal.ofReal (Real.exp ((α - 1) * overhead))
  change RenyiDivergence_def p q α ≤ ((εbar + overhead : ℝ) : EReal)
  have hcoeff_pos_real : 0 < α - 1 := sub_pos.mpr hα
  have hcoeff_pos : 0 < coeff := by
    simpa [coeff, ← EReal.coe_one, ← EReal.coe_sub, EReal.coe_pos] using hcoeff_pos_real
  have hbase_exp :
      renyiSum p₀ q₀ α ≤ ENNReal.eexp (coeff * (εbar : EReal)) := by
    change (∑' x : Ω, (p₀ x)^α * (q₀ x)^(1 - α)) ≤
      ENNReal.eexp (coeff * (εbar : EReal))
    rw [← RenyiDivergence_def_exp p₀ q₀ hα]
    exact ENNReal.eexp_mono_le.mp (mul_le_mul_of_nonneg_left hbase hcoeff_pos.le)
  have hsum_le :
      renyiSum p q α ≤ factor * ENNReal.eexp (coeff * (εbar : EReal)) := by
    calc
      renyiSum p q α
          ≤ factor * renyiSum p₀ q₀ α := by
            simpa [factor, overhead] using hconditioned.renyi_sum_le hα
      _ ≤ factor * ENNReal.eexp (coeff * (εbar : EReal)) := by
            exact mul_le_mul_right hbase_exp factor
  apply ereal_mul_le_cancel_coe_pos hcoeff_pos_real
  rw [ENNReal.eexp_mono_le]
  change
    ENNReal.eexp (((α : EReal) - 1) * RenyiDivergence_def p q α) ≤
      ENNReal.eexp (((α : EReal) - 1) * ((εbar + overhead : ℝ) : EReal))
  rw [RenyiDivergence_def_exp p q hα]
  calc
    renyiSum p q α
        ≤ factor * ENNReal.eexp (coeff * (εbar : EReal)) := hsum_le
    _ = ENNReal.eexp (coeff * ((εbar + overhead : ℝ) : EReal)) := by
        simpa [factor, coeff] using finiteBudget_exp_mul_base α εbar overhead

/-- Finite-budget accounting directly from the three natural stage
conditioning lemmas. -/
theorem finiteBudgetTerms_of_stages
    {profile : NativeProfile}
    {p₀ q₀ pK qK pS qS p q : PMF Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstages : FiniteBudgetConditioningStages p₀ q₀ pK qK pS qS p q bounds) :
    RDPLe p q α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice) hα bounds hbase hlocal
    (finiteBudgetConditioning_of_stages hstages)

/-- Finite-budget RDP accounting from the public-event proof obligations for
sampler success and comb acceptance. -/
theorem finiteBudgetTerms_of_publicEvents
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass (pK.filter samplerEvent hpSampler) combEvent) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice)
    hα bounds hbase hlocal
    (finiteBudgetConditioning_of_publicEvents
      hstruct hpSampler hqSampler hsamplerMass hpComb hqComb hcombMass)

/-- Finite-budget RDP accounting from upper bounds on sampler failure and comb
rejection. -/
theorem finiteBudgetTerms_of_publicEventFailures
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      eventMass pK samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice)
    hα bounds hbase hlocal
    (finiteBudgetConditioning_of_publicEventFailures
      hstruct hpSampler hqSampler hsamplerFailure hpComb hqComb hcombFailure)

/-- Finite-budget RDP accounting from public-event mass facts.  This version
derives the filter witnesses internally. -/
theorem finiteBudgetTerms_of_publicEventMasses
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hqSamplerMass_pos : 0 < eventMass qK samplerEvent)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass
          (pK.filter samplerEvent
            (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass))
          combEvent)
    (hqCombMass_pos :
      0 <
        eventMass
          (qK.filter samplerEvent
            (eventMass_filterable_of_pos hqSamplerMass_pos))
          combEvent) :
    RDPLe
      ((pK.filter samplerEvent
          (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass)).filter
        combEvent
        (eventMass_filterable_of_lower bounds.one_sub_delta_pos hcombMass))
      ((qK.filter samplerEvent
          (eventMass_filterable_of_pos hqSamplerMass_pos)).filter
        combEvent
        (eventMass_filterable_of_pos hqCombMass_pos))
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice)
    hα bounds hbase hlocal
    (finiteBudgetConditioning_of_publicEventMasses
      hstruct hsamplerMass hqSamplerMass_pos hcombMass hqCombMass_pos)

/-- Finite-budget accounting from pointwise Renyi-density bounds for each
stage.  This is often the most convenient target for local sampler proofs. -/
theorem finiteBudgetTerms_of_pointwiseStages
    {profile : NativeProfile}
    {p₀ q₀ pK qK pS qS p q : PMF Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstruct :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (pK x)^β * (qK x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * structuralOverhead β bounds)) *
              ((p₀ x)^β * (q₀ x)^(1 - β)))
    (hsampler :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (pS x)^β * (qS x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * samplerSuccessOverhead β bounds)) *
              ((pK x)^β * (qK x)^(1 - β)))
    (hcomb :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (p x)^β * (q x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * combOverhead β bounds)) *
              ((pS x)^β * (qS x)^(1 - β))) :
    RDPLe p q α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_stages (profile := profile) (lattice := lattice)
    hα bounds hbase hlocal
    { structural := RenyiSumOverhead.of_pointwise hstruct
      samplerSuccess := RenyiSumOverhead.of_pointwise hsampler
      comb := RenyiSumOverhead.of_pointwise hcomb }

/-- Substantive end-to-end target for the native proof.

The first hypothesis is the algorithm-correctness proof: the bounded native
sampler plus public resampling emits exactly the rounded dyadic Gaussian law.
The second hypothesis is the finite-budget RDP proof for that law. -/
theorem nativeAlgorithmRDP_of_emitsRoundedDyadicGaussian
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₁ law₂ : RoundedDyadicGaussianLaw lattice}
    {α ε : ℝ}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hrdp : RoundedDyadicGaussianRDP law₁ law₂ α ε) :
    RDPLe algorithm₁ algorithm₂ α (ε : EReal) :=
  algorithmRDP_of_roundedDyadicGaussianRDP hemits₁ hemits₂ hrdp

/-- f32 specialization of the generic algorithm-to-law-to-RDP bridge. -/
theorem nativeF32AlgorithmRDP_of_emitsRoundedDyadicGaussian
    {algorithm₁ algorithm₂ : PMF extF32Lattice.Output}
    {law₁ law₂ : RoundedF32GaussianLaw}
    {α ε : ℝ}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hrdp : RoundedDyadicGaussianRDP law₁ law₂ α ε) :
    RDPLe algorithm₁ algorithm₂ α (ε : EReal) :=
  nativeAlgorithmRDP_of_emitsRoundedDyadicGaussian hemits₁ hemits₂ hrdp

/-- RDP target for rounded dyadic Gaussian laws obtained by structural cap,
sampler-success rejection, and public comb rejection.  This theorem should
eventually instantiate `finiteBudgetTerms` with the PMFs induced by
`RoundedDyadicGaussianLaw.toPMF`. -/
theorem roundedDyadicGaussianRDP_of_finiteBudget
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {law₀₁ law₀₂ law₁ law₂ : RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hconditioned :
      FiniteBudgetConditioning law₀₁.toPMF law₀₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RoundedDyadicGaussianRDP law₁ law₂ α
      (εbar + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice) hα bounds hbase hlocal
    hconditioned

/-- RDP target for rounded dyadic Gaussian laws, using the three stage
conditioning lemmas directly. -/
theorem roundedDyadicGaussianRDP_of_finiteBudgetStages
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RoundedDyadicGaussianRDP law₁ law₂ α
      (εbar + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb) := by
  exact roundedDyadicGaussianRDP_of_finiteBudget hα bounds hbase hlocal
    (finiteBudgetConditioning_of_stages hstages)

/-- End-to-end native algorithm RDP theorem from law-emission, base rounded-law
RDP, local native obligations, and the three finite-budget stage lemmas. -/
theorem nativeAlgorithmRDP_of_finiteBudgetStages
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact algorithmRDP_of_roundedDyadicGaussianRDP hemits₁ hemits₂
    (roundedDyadicGaussianRDP_of_finiteBudgetStages hα bounds hbase hlocal hstages)

/-- End-to-end native algorithm RDP theorem from support-weight emission,
base rounded-law RDP, local native obligations, and finite-budget stages. -/
theorem nativeAlgorithmRDP_of_supportWeights_finiteBudgetStages
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (hemits₁ : EmitsRoundedSupportWeights algorithm₁ law₁)
    (hemits₂ : EmitsRoundedSupportWeights algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact algorithmRDP_of_roundedSupportWeights hemits₁ hemits₂
    (roundedDyadicGaussianRDP_of_finiteBudgetStages hα bounds hbase hlocal hstages)

/-- End-to-end native algorithm RDP theorem from filtered-support semantic
models, base rounded-law RDP, local native obligations, and finite-budget
stages. -/
theorem nativeAlgorithmRDP_of_filteredSupportModels_finiteBudgetStages
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    (model₁ model₂ : FilteredSupportModel lattice)
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ :
      RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (halg₁ : algorithm₁ = model₁.outputPMF)
    (halg₂ : algorithm₂ = model₂.outputPMF)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF
        model₁.law.toPMF model₂.law.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact algorithmRDP_of_filteredSupportModels model₁ model₂ halg₁ halg₂
    (roundedDyadicGaussianRDP_of_finiteBudgetStages
      hα bounds hbase hlocal hstages)

/-- End-to-end native algorithm RDP theorem from pointwise bounds for each
finite-budget stage. -/
theorem nativeAlgorithmRDP_of_pointwiseStages
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {algorithm₁ algorithm₂ : PMF lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedDyadicGaussianLaw lattice}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec profile lattice}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hstruct :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (lawK₁.toPMF x)^β * (lawK₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * structuralOverhead β bounds)) *
              ((law₀₁.toPMF x)^β * (law₀₂.toPMF x)^(1 - β)))
    (hsampler :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (lawS₁.toPMF x)^β * (lawS₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * samplerSuccessOverhead β bounds)) *
              ((lawK₁.toPMF x)^β * (lawK₂.toPMF x)^(1 - β)))
    (hcomb :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (law₁.toPMF x)^β * (law₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * combOverhead β bounds)) *
              ((lawS₁.toPMF x)^β * (lawS₂.toPMF x)^(1 - β))) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact algorithmRDP_of_roundedDyadicGaussianRDP hemits₁ hemits₂
    (finiteBudgetTerms_of_pointwiseStages
      (profile := profile)
      (lattice := lattice)
      hα bounds hbase hlocal hstruct hsampler hcomb)

/-- Fixed-profile corollary for the current Rust native path. -/
theorem finiteBudgetTerms_fixedF32
    {p₀ q₀ p q : PMF Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hconditioned : FiniteBudgetConditioning p₀ q₀ p q bounds) :
    RDPLe p q α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := fixedF32Profile) (lattice := extF32Lattice) hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive) hconditioned

/-- Fixed-profile finite-budget RDP accounting from public sampler-success and
comb-acceptance events. -/
theorem finiteBudgetTerms_fixedF32_of_publicEvents
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass (pK.filter samplerEvent hpSampler) combEvent) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_publicEvents
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive)
    hstruct hpSampler hqSampler hsamplerMass hpComb hqComb hcombMass

/-- Fixed-profile finite-budget RDP accounting from upper bounds on sampler
failure and comb rejection. -/
theorem finiteBudgetTerms_fixedF32_of_publicEventFailures
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      eventMass pK samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_publicEventFailures
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive)
    hstruct hpSampler hqSampler hsamplerFailure hpComb hqComb hcombFailure

/-- Fixed-profile finite-budget RDP accounting from public-event mass facts,
with filter witnesses derived internally. -/
theorem finiteBudgetTerms_fixedF32_of_publicEventMasses
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hsamplerMass :
      ENNReal.ofReal bounds.lambdaS ≤ eventMass pK samplerEvent)
    (hqSamplerMass_pos : 0 < eventMass qK samplerEvent)
    (hcombMass :
      ENNReal.ofReal (1 - bounds.δb) ≤
        eventMass
          (pK.filter samplerEvent
            (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass))
          combEvent)
    (hqCombMass_pos :
      0 <
        eventMass
          (qK.filter samplerEvent
            (eventMass_filterable_of_pos hqSamplerMass_pos))
          combEvent) :
    RDPLe
      ((pK.filter samplerEvent
          (eventMass_filterable_of_lower bounds.lambdaS_pos hsamplerMass)).filter
        combEvent
        (eventMass_filterable_of_lower bounds.one_sub_delta_pos hcombMass))
      ((qK.filter samplerEvent
          (eventMass_filterable_of_pos hqSamplerMass_pos)).filter
        combEvent
        (eventMass_filterable_of_pos hqCombMass_pos))
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_publicEventMasses
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive)
    hstruct hsamplerMass hqSamplerMass_pos hcombMass hqCombMass_pos

/-- Fixed-profile end-to-end theorem for the Rust native f32 path. -/
theorem nativeF32AlgorithmRDP_of_finiteBudgetStages
    {algorithm₁ algorithm₂ : PMF extF32Lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedF32GaussianLaw}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact nativeAlgorithmRDP_of_finiteBudgetStages
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hemits₁ hemits₂ hbase
    (localObligations_of_primitiveProofs hprimitive) hstages

/-- Fixed-profile end-to-end theorem from support-weight emission. -/
theorem nativeF32AlgorithmRDP_of_supportWeights_finiteBudgetStages
    {algorithm₁ algorithm₂ : PMF extF32Lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedF32GaussianLaw}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hemits₁ : EmitsRoundedSupportWeights algorithm₁ law₁)
    (hemits₂ : EmitsRoundedSupportWeights algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF law₁.toPMF law₂.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact nativeAlgorithmRDP_of_supportWeights_finiteBudgetStages
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hemits₁ hemits₂ hbase
    (localObligations_of_primitiveProofs hprimitive) hstages

/-- Fixed-profile end-to-end theorem from filtered-support semantic models. -/
theorem nativeF32AlgorithmRDP_of_filteredSupportModels_finiteBudgetStages
    {algorithm₁ algorithm₂ : PMF extF32Lattice.Output}
    (model₁ model₂ : FilteredSupportModel extF32Lattice)
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ :
      RoundedF32GaussianLaw}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (halg₁ : algorithm₁ = model₁.outputPMF)
    (halg₂ : algorithm₂ = model₂.outputPMF)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstages :
      FiniteBudgetConditioningStages
        law₀₁.toPMF law₀₂.toPMF lawK₁.toPMF lawK₂.toPMF
        lawS₁.toPMF lawS₂.toPMF
        model₁.law.toPMF model₂.law.toPMF bounds) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact nativeAlgorithmRDP_of_filteredSupportModels_finiteBudgetStages
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    model₁ model₂
    hα bounds halg₁ halg₂ hbase
    (localObligations_of_primitiveProofs hprimitive) hstages

/-- Fixed-profile end-to-end theorem for the Rust native f32 path, stated with
pointwise finite-budget stage bounds. -/
theorem nativeF32AlgorithmRDP_of_pointwiseStages
    {algorithm₁ algorithm₂ : PMF extF32Lattice.Output}
    {law₀₁ law₀₂ lawK₁ lawK₂ lawS₁ lawS₂ law₁ law₂ :
      RoundedF32GaussianLaw}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hemits₁ : EmitsRoundedDyadicGaussian algorithm₁ law₁)
    (hemits₂ : EmitsRoundedDyadicGaussian algorithm₂ law₂)
    (hbase : RoundedDyadicGaussianRDP law₀₁ law₀₂ α εbar)
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (lawK₁.toPMF x)^β * (lawK₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * structuralOverhead β bounds)) *
              ((law₀₁.toPMF x)^β * (law₀₂.toPMF x)^(1 - β)))
    (hsampler :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (lawS₁.toPMF x)^β * (lawS₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * samplerSuccessOverhead β bounds)) *
              ((lawK₁.toPMF x)^β * (lawK₂.toPMF x)^(1 - β)))
    (hcomb :
      ∀ {β : ℝ},
        1 < β →
        ∀ x,
          (law₁.toPMF x)^β * (law₂.toPMF x)^(1 - β) ≤
            ENNReal.ofReal (Real.exp ((β - 1) * combOverhead β bounds)) *
              ((lawS₁.toPMF x)^β * (lawS₂.toPMF x)^(1 - β))) :
    RDPLe algorithm₁ algorithm₂ α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact nativeAlgorithmRDP_of_pointwiseStages
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hemits₁ hemits₂ hbase
    (localObligations_of_primitiveProofs hprimitive)
    hstruct hsampler hcomb

/-- Conservative conversion when the comb is bounded under the original
Gaussian law instead of the post-sampler, pre-comb law. -/
theorem combProbability_after_conditioning
    {δbar C lambdaS : ℝ}
    (hC : 0 < C) (hlambda : 0 < lambdaS) :
    δbar / (C * lambdaS) = δbar * (1 / C) * (1 / lambdaS) := by
  field_simp [hC.ne', hlambda.ne']

/-- Fixed-profile sampler constants, matching the Rust reference implementation
and the scratch whitepaper. -/
def fixedF32BudgetBounds (combFailure : ℝ)
    (hcomb_nonneg : 0 ≤ combFailure)
    (hcomb_lt_one : combFailure < 1) : BudgetBounds where
  structuralTail := 2 ^ (-(145.1 : ℝ))
  samplerFailure := 2 ^ (-(83.97 : ℝ)) + 2 ^ (-(80.57 : ℝ))
  combFailure := combFailure
  structuralTail_nonneg := by positivity
  samplerFailure_nonneg := by positivity
  combFailure_nonneg := hcomb_nonneg
  structuralTail_lt_one := by
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  samplerFailure_lt_one := by
    have h₁ :
        (2 : ℝ) ^ (-(83.97 : ℝ)) < (1 / 4 : ℝ) := by
      calc
        (2 : ℝ) ^ (-(83.97 : ℝ))
            < (2 : ℝ) ^ (-(2 : ℝ)) :=
              Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by norm_num)
        _ = (1 / 4 : ℝ) := by
              norm_num [Real.rpow_neg_ofNat]
    have h₂ :
        (2 : ℝ) ^ (-(80.57 : ℝ)) < (1 / 4 : ℝ) := by
      calc
        (2 : ℝ) ^ (-(80.57 : ℝ))
            < (2 : ℝ) ^ (-(2 : ℝ)) :=
              Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by norm_num)
        _ = (1 / 4 : ℝ) := by
              norm_num [Real.rpow_neg_ofNat]
    linarith
  combFailure_lt_one := hcomb_lt_one

/-!
## Profile-derived sampler-failure budget

The `samplerFailure` field of `BudgetBounds` was previously supplied as a magic
constant.  The lemmas below instead *derive* a sampler-failure bound from the
public profile: a union bound over the (finitely many) prefix comparisons and
Bernoulli factories, each certified by the corresponding `LocalObligations`
field.  This makes `psrn_comparison_undecided_bound` and
`bernoulli_factory_depth_bound` load-bearing for the numeric budget.

These lemmas bridge from a public sampler-failure event to the retained-mass
hypothesis used by `finiteBudgetTerms`.  The remaining semantic gap is local:
one must prove that the concrete sampler-failure event is contained in, or has
mass bounded by, the union of the declared comparison and Bernoulli-factory
failure events.  That future proof should live in the probabilistic semantics
of `NativeSamplerSpec`; the global RDP accounting below only consumes the
packaged bound. -/

theorem comparisonUndecidedBound_nonneg (profile : NativeProfile) :
    0 ≤ comparisonUndecidedBound profile := by
  unfold comparisonUndecidedBound
  positivity

theorem factoryDepthBound_nonneg (profile : NativeProfile) :
    0 ≤ factoryDepthBound profile := by
  unfold factoryDepthBound
  positivity

/-- Conservative union bound on total sampler-side failure for one run: at most
`comparisonCountBound` prefix comparisons, each undecided with probability at
most `comparisonUndecidedBound`, plus at most `factoryCountBound` Bernoulli
factories, each exceeding the public depth cap with probability at most
`factoryDepthBound`. -/
def profileSamplerFailureBound (profile : NativeProfile) : ℝ :=
  (profile.comparisonCountBound : ℝ) * comparisonUndecidedBound profile
  + (profile.factoryCountBound : ℝ) * factoryDepthBound profile

theorem profileSamplerFailureBound_nonneg (profile : NativeProfile) :
    0 ≤ profileSamplerFailureBound profile := by
  unfold profileSamplerFailureBound
  have hc := comparisonUndecidedBound_nonneg profile
  have hf := factoryDepthBound_nonneg profile
  positivity

/-- Union bound: if one run's sampler-side failure decomposes into per-instance
failure probabilities `compFail`/`factFail`, each tagged by a comparison or
factory kind and dominated by that kind's undecided/depth probability, then the
total failure is at most `profileSamplerFailureBound`.

The `LocalObligations` hypothesis is used here through its per-kind sampler
bounds, so this is the first result in the file where those fields do real
work. -/
theorem totalSamplerFailure_le_profileBound
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hlocal : LocalObligations profile bounds lattice spec)
    (compKind : Fin profile.comparisonCountBound → ComparisonKind)
    (factKind : Fin profile.factoryCountBound → FactoryKind)
    (compFail : Fin profile.comparisonCountBound → ℝ)
    (factFail : Fin profile.factoryCountBound → ℝ)
    (hcomp : ∀ i, compFail i ≤ comparisonUndecidedProbability profile (compKind i))
    (hfact : ∀ j, factFail j ≤ factoryDepthFailureProbability profile (factKind j)) :
    (∑ i, compFail i) + (∑ j, factFail j) ≤ profileSamplerFailureBound profile := by
  have hc : ∀ i, compFail i ≤ comparisonUndecidedBound profile := fun i =>
    (hcomp i).trans (hlocal.psrn_comparison_undecided_bound (compKind i))
  have hf : ∀ j, factFail j ≤ factoryDepthBound profile := fun j =>
    (hfact j).trans (hlocal.bernoulli_factory_depth_bound (factKind j))
  have hsum_c :
      (∑ i, compFail i)
        ≤ (profile.comparisonCountBound : ℝ) * comparisonUndecidedBound profile := by
    calc
      (∑ i, compFail i)
          ≤ ∑ _i : Fin profile.comparisonCountBound, comparisonUndecidedBound profile :=
            Finset.sum_le_sum (fun i _ => hc i)
      _ = (profile.comparisonCountBound : ℝ) * comparisonUndecidedBound profile := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum_f :
      (∑ j, factFail j)
        ≤ (profile.factoryCountBound : ℝ) * factoryDepthBound profile := by
    calc
      (∑ j, factFail j)
          ≤ ∑ _j : Fin profile.factoryCountBound, factoryDepthBound profile :=
            Finset.sum_le_sum (fun j _ => hf j)
      _ = (profile.factoryCountBound : ℝ) * factoryDepthBound profile := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (∑ i, compFail i) + (∑ j, factFail j)
        ≤ (profile.comparisonCountBound : ℝ) * comparisonUndecidedBound profile
          + (profile.factoryCountBound : ℝ) * factoryDepthBound profile :=
          add_le_add hsum_c hsum_f
    _ = profileSamplerFailureBound profile := rfl

/-- Local decomposition of the public sampler-failure event into bounded
comparison-prefix and Bernoulli-factory failures.

This structure is intended to be the Lean-facing boundary between executable
sampler semantics and the global RDP accounting: semantics prove one value of
this structure, and the accounting lemmas below consume it without inspecting
the sampler trace model. -/
structure SamplerFailureDecomposition
    (profile : NativeProfile)
    (p : PMF Ω)
    (samplerEvent : Set Ω) : Type where
  compKind : Fin profile.comparisonCountBound → ComparisonKind
  factKind : Fin profile.factoryCountBound → FactoryKind
  compFail : Fin profile.comparisonCountBound → ℝ
  factFail : Fin profile.factoryCountBound → ℝ
  compFail_nonneg : ∀ i, 0 ≤ compFail i
  factFail_nonneg : ∀ j, 0 ≤ factFail j
  comp_bound :
    ∀ i, compFail i ≤ comparisonUndecidedProbability profile (compKind i)
  fact_bound :
    ∀ j, factFail j ≤ factoryDepthFailureProbability profile (factKind j)
  event_bound :
    eventMass p samplerEventᶜ ≤
      ENNReal.ofReal ((∑ i, compFail i) + (∑ j, factFail j))

theorem SamplerFailureDecomposition.total_nonneg
    {profile : NativeProfile}
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hdecomp : SamplerFailureDecomposition profile p samplerEvent) :
    0 ≤ (∑ i, hdecomp.compFail i) + (∑ j, hdecomp.factFail j) := by
  exact add_nonneg
    (Finset.sum_nonneg (fun i _ => hdecomp.compFail_nonneg i))
    (Finset.sum_nonneg (fun j _ => hdecomp.factFail_nonneg j))

theorem SamplerFailureDecomposition.total_le_profileBound
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hdecomp : SamplerFailureDecomposition profile p samplerEvent) :
    (∑ i, hdecomp.compFail i) + (∑ j, hdecomp.factFail j) ≤
      profileSamplerFailureBound profile :=
  totalSamplerFailure_le_profileBound hlocal
    hdecomp.compKind hdecomp.factKind
    hdecomp.compFail hdecomp.factFail
    hdecomp.comp_bound hdecomp.fact_bound

theorem SamplerFailureDecomposition.event_le_profileBound
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hdecomp : SamplerFailureDecomposition profile p samplerEvent) :
    eventMass p samplerEventᶜ ≤
      ENNReal.ofReal (profileSamplerFailureBound profile) :=
  hdecomp.event_bound.trans
    (ENNReal.ofReal_le_ofReal
      (hdecomp.total_le_profileBound hlocal))

theorem SamplerFailureDecomposition.event_le_budget
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hdecomp : SamplerFailureDecomposition profile p samplerEvent) :
    eventMass p samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure := by
  simpa [hbudget] using hdecomp.event_le_profileBound hlocal

/-- Packaged public-event obligations for the finite-budget native theorem
when the sampler-failure budget is derived from the native profile. -/
structure ProfileFailureEvents
    (profile : NativeProfile)
    (bounds : BudgetBounds)
    (pK qK : PMF Ω)
    (samplerEvent combEvent : Set Ω) : Type where
  hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support
  hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support
  samplerFailure : SamplerFailureDecomposition profile pK samplerEvent
  hpComb : ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support
  hqComb : ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support
  combFailure :
    eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
      ENNReal.ofReal bounds.δb

theorem ProfileFailureEvents.samplerFailure_le_budget
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hevents :
      ProfileFailureEvents profile bounds pK qK samplerEvent combEvent) :
    eventMass pK samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure :=
  hevents.samplerFailure.event_le_budget hlocal hbudget

theorem ProfileFailureEvents.toConditioningStages
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hevents :
      ProfileFailureEvents profile bounds pK qK samplerEvent combEvent) :
    FiniteBudgetConditioningStages
      p₀ q₀
      pK qK
      (pK.filter samplerEvent hevents.hpSampler)
      (qK.filter samplerEvent hevents.hqSampler)
      ((pK.filter samplerEvent hevents.hpSampler).filter combEvent hevents.hpComb)
      ((qK.filter samplerEvent hevents.hqSampler).filter combEvent hevents.hqComb)
      bounds :=
  finiteBudgetConditioningStages_of_publicEventFailures
    hstruct
    hevents.hpSampler hevents.hqSampler
    (hevents.samplerFailure_le_budget hlocal hbudget)
    hevents.hpComb hevents.hqComb hevents.combFailure

theorem ProfileFailureEvents.toConditioning
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hevents :
      ProfileFailureEvents profile bounds pK qK samplerEvent combEvent) :
    FiniteBudgetConditioning
      p₀ q₀
      ((pK.filter samplerEvent hevents.hpSampler).filter combEvent hevents.hpComb)
      ((qK.filter samplerEvent hevents.hqSampler).filter combEvent hevents.hqComb)
      bounds :=
  finiteBudgetConditioning_of_stages
    (hevents.toConditioningStages hlocal hbudget hstruct)

/-!
## Staged trace semantics

The next package is the local target for executable native semantics.  It keeps
the global RDP accounting on public events over exact traces:

* `samplerEvent` is the bounded-work sampler success event.
* `combEvent` is the static public-comb acceptance event.
* `supportPMF` is the exact trace law after both public filters.
* `toFilteredSupportModel` turns that filtered trace law into the rounded
  dyadic Gaussian law emitted by deterministic finalization.

No privacy theorem below inspects low-level PSRN or Bernoulli-factory code; the
executable proof only has to construct this model and the sampler-failure
decomposition consumed by `ProfileFailureEvents`. -/

/-- A one-input staged model for the native rounded sampler.  It records that
accepted traces finalize to the deterministic rounded output, while rejected
accepted-sampler traces are precisely the public comb. -/
structure StagedTraceModel
    (profile : NativeProfile)
    (lattice : DyadicOutputLattice)
    (spec : NativeSamplerSpec profile lattice)
    (input : NativeInput) : Type 1 where
  Support : Type
  raw : PMF Support
  samplerEvent : Set Support
  hpSampler : ∃ x ∈ samplerEvent, x ∈ raw.support
  combEvent : Set Support
  hpComb : ∃ x ∈ combEvent, x ∈ (raw.filter samplerEvent hpSampler).support
  point : Support → DyadicSupportPoint
  sampler_within :
    ∀ x, x ∈ samplerEvent → TraceWithinProfile profile (point x).trace
  comb_accept_iff :
    ∀ x, x ∈ samplerEvent →
      (x ∈ combEvent ↔ ¬ InPublicComb profile input (point x).trace)
  finalizes_output :
    ∀ x,
      x ∈ samplerEvent →
      x ∈ combEvent →
      spec.finalize (point x).trace
        (FinalizationResult.output (lattice.round (point x).value))
  finalizes_rejectedComb :
    ∀ x,
      x ∈ samplerEvent →
      x ∉ combEvent →
      spec.finalize (point x).trace FinalizationResult.rejectedComb
  point_mem_cell :
    ∀ x,
      DyadicInterval.Contains
        (lattice.cell (lattice.round (point x).value))
        (point x).value

/-- The exact support law after bounded-sampler success and public-comb
acceptance. -/
def StagedTraceModel.supportPMF
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    PMF model.Support :=
  (model.raw.filter model.samplerEvent model.hpSampler).filter
    model.combEvent model.hpComb

/-- The filtered-support rounded law induced by a staged trace model. -/
def StagedTraceModel.toFilteredSupportModel
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    FilteredSupportModel lattice where
  Support := model.Support
  raw := model.raw.filter model.samplerEvent model.hpSampler
  accept := model.combEvent
  accept_nonempty := model.hpComb
  point := model.point
  point_mem_cell := model.point_mem_cell

/-- Output PMF obtained by deterministic rounding after the two public filters. -/
def StagedTraceModel.outputPMF
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    PMF lattice.Output :=
  model.toFilteredSupportModel.outputPMF

theorem StagedTraceModel.supportPMF_eq_law_supportPMF
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    model.toFilteredSupportModel.law.supportPMF = model.supportPMF :=
  model.toFilteredSupportModel.law_supportPMF_eq_filter

theorem StagedTraceModel.outputPMF_emits
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    EmitsRoundedDyadicGaussian model.outputPMF
      model.toFilteredSupportModel.law :=
  model.toFilteredSupportModel.outputPMF_emits

/-- Support-weight form of `outputPMF_emits`, useful when later proofs want the
exact trace PMF rather than only output masses. -/
def StagedTraceModel.outputPMF_emitsSupportWeights
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input) :
    EmitsRoundedSupportWeights model.outputPMF
      model.toFilteredSupportModel.law :=
  model.toFilteredSupportModel.outputPMF_emitsSupportWeights

theorem StagedTraceModel.not_comb_accept_iff_publicComb
    {profile : NativeProfile}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input)
    (x : model.Support)
    (hsampler : x ∈ model.samplerEvent) :
    (x ∉ model.combEvent ↔
      InPublicComb profile input (model.point x).trace) := by
  have h := model.comb_accept_iff x hsampler
  tauto

theorem StagedTraceModel.rejected_trace_in_publicComb
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input)
    (hlocal : LocalObligations profile bounds lattice spec)
    (hinput : SupportCondition profile input)
    (x : model.Support)
    (hsampler : x ∈ model.samplerEvent)
    (hreject : x ∉ model.combEvent) :
    InPublicComb profile input (model.point x).trace :=
  hlocal.finalization_rejections_subset_public_comb
    input (model.point x).trace hinput
    (model.sampler_within x hsampler)
    (model.finalizes_rejectedComb x hsampler hreject)

theorem StagedTraceModel.rejected_trace_in_publicComb_iff
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input : NativeInput}
    (model : StagedTraceModel profile lattice spec input)
    (_hlocal : LocalObligations profile bounds lattice spec)
    (_hinput : SupportCondition profile input)
    (x : model.Support)
    (hsampler : x ∈ model.samplerEvent) :
    (x ∉ model.combEvent ↔
      InPublicComb profile input (model.point x).trace) :=
  model.not_comb_accept_iff_publicComb x hsampler

/-- A paired staged model with common public events over a common support.  This
is the natural boundary for finite-budget conditioning: the left distribution
supplies the sampler-failure and comb-failure bounds, while both distributions
use the same public retained events. -/
structure PairedStagedTraceModel
    (profile : NativeProfile)
    (bounds : BudgetBounds)
    (lattice : DyadicOutputLattice)
    (spec : NativeSamplerSpec profile lattice)
    (input₁ input₂ : NativeInput) : Type 1 where
  Support : Type
  pRaw : PMF Support
  qRaw : PMF Support
  samplerEvent : Set Support
  combEvent : Set Support
  hpSampler : ∃ x ∈ samplerEvent, x ∈ pRaw.support
  hqSampler : ∃ x ∈ samplerEvent, x ∈ qRaw.support
  samplerFailure : SamplerFailureDecomposition profile pRaw samplerEvent
  hpComb : ∃ x ∈ combEvent, x ∈ (pRaw.filter samplerEvent hpSampler).support
  hqComb : ∃ x ∈ combEvent, x ∈ (qRaw.filter samplerEvent hqSampler).support
  combFailure :
    eventMass (pRaw.filter samplerEvent hpSampler) combEventᶜ ≤
      ENNReal.ofReal bounds.δb
  point₁ : Support → DyadicSupportPoint
  point₂ : Support → DyadicSupportPoint
  sampler_within₁ :
    ∀ x, x ∈ samplerEvent → TraceWithinProfile profile (point₁ x).trace
  sampler_within₂ :
    ∀ x, x ∈ samplerEvent → TraceWithinProfile profile (point₂ x).trace
  comb_accept_iff₁ :
    ∀ x, x ∈ samplerEvent →
      (x ∈ combEvent ↔ ¬ InPublicComb profile input₁ (point₁ x).trace)
  comb_accept_iff₂ :
    ∀ x, x ∈ samplerEvent →
      (x ∈ combEvent ↔ ¬ InPublicComb profile input₂ (point₂ x).trace)
  finalizes_output₁ :
    ∀ x,
      x ∈ samplerEvent →
      x ∈ combEvent →
      spec.finalize (point₁ x).trace
        (FinalizationResult.output (lattice.round (point₁ x).value))
  finalizes_output₂ :
    ∀ x,
      x ∈ samplerEvent →
      x ∈ combEvent →
      spec.finalize (point₂ x).trace
        (FinalizationResult.output (lattice.round (point₂ x).value))
  finalizes_rejectedComb₁ :
    ∀ x,
      x ∈ samplerEvent →
      x ∉ combEvent →
      spec.finalize (point₁ x).trace FinalizationResult.rejectedComb
  finalizes_rejectedComb₂ :
    ∀ x,
      x ∈ samplerEvent →
      x ∉ combEvent →
      spec.finalize (point₂ x).trace FinalizationResult.rejectedComb
  point_mem_cell₁ :
    ∀ x,
      DyadicInterval.Contains
        (lattice.cell (lattice.round (point₁ x).value))
        (point₁ x).value
  point_mem_cell₂ :
    ∀ x,
      DyadicInterval.Contains
        (lattice.cell (lattice.round (point₂ x).value))
        (point₂ x).value

def PairedStagedTraceModel.left
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input₁ input₂ : NativeInput}
    (model : PairedStagedTraceModel profile bounds lattice spec input₁ input₂) :
    StagedTraceModel profile lattice spec input₁ where
  Support := model.Support
  raw := model.pRaw
  samplerEvent := model.samplerEvent
  hpSampler := model.hpSampler
  combEvent := model.combEvent
  hpComb := model.hpComb
  point := model.point₁
  sampler_within := model.sampler_within₁
  comb_accept_iff := model.comb_accept_iff₁
  finalizes_output := model.finalizes_output₁
  finalizes_rejectedComb := model.finalizes_rejectedComb₁
  point_mem_cell := model.point_mem_cell₁

def PairedStagedTraceModel.right
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input₁ input₂ : NativeInput}
    (model : PairedStagedTraceModel profile bounds lattice spec input₁ input₂) :
    StagedTraceModel profile lattice spec input₂ where
  Support := model.Support
  raw := model.qRaw
  samplerEvent := model.samplerEvent
  hpSampler := model.hqSampler
  combEvent := model.combEvent
  hpComb := model.hqComb
  point := model.point₂
  sampler_within := model.sampler_within₂
  comb_accept_iff := model.comb_accept_iff₂
  finalizes_output := model.finalizes_output₂
  finalizes_rejectedComb := model.finalizes_rejectedComb₂
  point_mem_cell := model.point_mem_cell₂

def PairedStagedTraceModel.toProfileFailureEvents
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input₁ input₂ : NativeInput}
    (model : PairedStagedTraceModel profile bounds lattice spec input₁ input₂) :
    ProfileFailureEvents profile bounds model.pRaw model.qRaw
      model.samplerEvent model.combEvent where
  hpSampler := model.hpSampler
  hqSampler := model.hqSampler
  samplerFailure := model.samplerFailure
  hpComb := model.hpComb
  hqComb := model.hqComb
  combFailure := model.combFailure

theorem PairedStagedTraceModel.supportConditioningStages
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input₁ input₂ : NativeInput}
    (model : PairedStagedTraceModel profile bounds lattice spec input₁ input₂)
    {p₀ q₀ : PMF model.Support}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ model.pRaw model.qRaw
        (fun α => structuralOverhead α bounds)) :
    FiniteBudgetConditioningStages
      p₀ q₀
      model.pRaw model.qRaw
      (model.pRaw.filter model.samplerEvent model.hpSampler)
      (model.qRaw.filter model.samplerEvent model.hqSampler)
      model.left.supportPMF
      model.right.supportPMF
      bounds := by
  exact (model.toProfileFailureEvents).toConditioningStages hlocal hbudget hstruct

theorem PairedStagedTraceModel.supportRDP
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {input₁ input₂ : NativeInput}
    {α εbar : ℝ}
    (model : PairedStagedTraceModel profile bounds lattice spec input₁ input₂)
    {p₀ q₀ : PMF model.Support}
    (hα : 1 < α)
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ model.pRaw model.qRaw
        (fun α => structuralOverhead α bounds)) :
    RDPLe model.left.supportPMF model.right.supportPMF α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms (profile := profile) (lattice := lattice)
    hα bounds hbase hlocal
    (finiteBudgetConditioning_of_stages
      (model.supportConditioningStages hlocal hbudget hstruct))

/-- If the public sampler-failure event is itself bounded by a sum of concrete
comparison and factory failure terms, then the profile union bound supplies the
`BudgetBounds` sampler-failure hypothesis consumed by the finite-budget RDP
theorems. -/
theorem samplerFailureEvent_le_budget_of_profileDecomposition
    {profile : NativeProfile}
    {bounds : BudgetBounds}
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    {p : PMF Ω}
    {samplerEvent : Set Ω}
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (compKind : Fin profile.comparisonCountBound → ComparisonKind)
    (factKind : Fin profile.factoryCountBound → FactoryKind)
    (compFail : Fin profile.comparisonCountBound → ℝ)
    (factFail : Fin profile.factoryCountBound → ℝ)
    (hcomp : ∀ i, compFail i ≤ comparisonUndecidedProbability profile (compKind i))
    (hfact : ∀ j, factFail j ≤ factoryDepthFailureProbability profile (factKind j))
    (hfailureEvent :
      eventMass p samplerEventᶜ ≤
        ENNReal.ofReal ((∑ i, compFail i) + (∑ j, factFail j))) :
    eventMass p samplerEventᶜ ≤ ENNReal.ofReal bounds.samplerFailure := by
  have htotal :
      (∑ i, compFail i) + (∑ j, factFail j) ≤
        profileSamplerFailureBound profile :=
    totalSamplerFailure_le_profileBound hlocal
      compKind factKind compFail factFail hcomp hfact
  exact hfailureEvent.trans (by
    rw [hbudget]
    exact ENNReal.ofReal_le_ofReal htotal)

/-- Finite-budget RDP accounting where the sampler-failure event is bounded by
a concrete comparison/factory decomposition, which is then discharged by the
profile-level primitive bounds. -/
theorem finiteBudgetTerms_of_profileSamplerFailureDecomposition
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (compKind : Fin profile.comparisonCountBound → ComparisonKind)
    (factKind : Fin profile.factoryCountBound → FactoryKind)
    (compFail : Fin profile.comparisonCountBound → ℝ)
    (factFail : Fin profile.factoryCountBound → ℝ)
    (hcomp : ∀ i, compFail i ≤ comparisonUndecidedProbability profile (compKind i))
    (hfact : ∀ j, factFail j ≤ factoryDepthFailureProbability profile (factKind j))
    (hsamplerFailureEvent :
      eventMass pK samplerEventᶜ ≤
        ENNReal.ofReal ((∑ i, compFail i) + (∑ j, factFail j)))
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_publicEventFailures
    (profile := profile)
    (lattice := lattice)
    hα bounds hbase hlocal hstruct hpSampler hqSampler
    (samplerFailureEvent_le_budget_of_profileDecomposition
      hlocal hbudget compKind factKind compFail factFail hcomp hfact
      hsamplerFailureEvent)
    hpComb hqComb hcombFailure

/-- Finite-budget RDP accounting from a packaged sampler-failure
decomposition.  This is the preferred theorem boundary for future executable
semantics: the sampler proof constructs `SamplerFailureDecomposition`, while
this theorem handles the profile union bound and RDP conditioning overhead. -/
theorem finiteBudgetTerms_of_samplerFailureDecomposition
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      SamplerFailureDecomposition profile pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_publicEventFailures
    (profile := profile)
    (lattice := lattice)
    hα bounds hbase hlocal hstruct hpSampler hqSampler
    (hsamplerFailure.event_le_budget hlocal hbudget)
    hpComb hqComb hcombFailure

/-- Fixed-profile version of
`finiteBudgetTerms_of_samplerFailureDecomposition`, using the primitive proof
package already expected by the Rust native f32 path. -/
theorem finiteBudgetTerms_fixedF32_of_samplerFailureDecomposition
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound fixedF32Profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      SamplerFailureDecomposition fixedF32Profile pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal bounds.δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_samplerFailureDecomposition
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive)
    hbudget hstruct hpSampler hqSampler hsamplerFailure
    hpComb hqComb hcombFailure

/-- Finite-budget RDP accounting from packaged public-event obligations. -/
theorem finiteBudgetTerms_of_profileFailureEvents
    {profile : NativeProfile}
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {lattice : DyadicOutputLattice}
    {spec : NativeSamplerSpec profile lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hlocal : LocalObligations profile bounds lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hevents :
      ProfileFailureEvents profile bounds pK qK samplerEvent combEvent) :
    RDPLe
      ((pK.filter samplerEvent hevents.hpSampler).filter combEvent hevents.hpComb)
      ((qK.filter samplerEvent hevents.hqSampler).filter combEvent hevents.hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_samplerFailureDecomposition
    (profile := profile)
    (lattice := lattice)
    hα bounds hbase hlocal hbudget hstruct
    hevents.hpSampler hevents.hqSampler hevents.samplerFailure
    hevents.hpComb hevents.hqComb hevents.combFailure

/-- Fixed-profile finite-budget accounting from packaged public-event
obligations. -/
theorem finiteBudgetTerms_fixedF32_of_profileFailureEvents
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar : ℝ}
    (hα : 1 < α)
    (bounds : BudgetBounds)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hbudget : bounds.samplerFailure = profileSamplerFailureBound fixedF32Profile)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK (fun α => structuralOverhead α bounds))
    (hevents :
      ProfileFailureEvents fixedF32Profile bounds pK qK samplerEvent combEvent) :
    RDPLe
      ((pK.filter samplerEvent hevents.hpSampler).filter combEvent hevents.hpComb)
      ((qK.filter samplerEvent hevents.hqSampler).filter combEvent hevents.hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α bounds.C bounds.lambdaS bounds.δb : ℝ) : EReal) := by
  exact finiteBudgetTerms_of_profileFailureEvents
    (profile := fixedF32Profile)
    (lattice := extF32Lattice)
    hα bounds hbase
    (localObligations_of_primitiveProofs hprimitive)
    hbudget hstruct hevents

/-- Build a `BudgetBounds` whose sampler-failure component is the
profile-derived union bound rather than a magic constant.  The structural-tail
and comb components are still supplied by the caller (their derivation needs the
noise-tail and finalization analyses respectively). -/
def budgetBoundsOfProfile
    (profile : NativeProfile)
    (structuralTail combFailure : ℝ)
    (hst_nonneg : 0 ≤ structuralTail) (hst_lt : structuralTail < 1)
    (hcf_nonneg : 0 ≤ combFailure) (hcf_lt : combFailure < 1)
    (hsf_lt : profileSamplerFailureBound profile < 1) : BudgetBounds where
  structuralTail := structuralTail
  samplerFailure := profileSamplerFailureBound profile
  combFailure := combFailure
  structuralTail_nonneg := hst_nonneg
  samplerFailure_nonneg := profileSamplerFailureBound_nonneg profile
  combFailure_nonneg := hcf_nonneg
  structuralTail_lt_one := hst_lt
  samplerFailure_lt_one := hsf_lt
  combFailure_lt_one := hcf_lt

theorem budgetBoundsOfProfile_samplerFailure
    (profile : NativeProfile)
    (structuralTail combFailure : ℝ)
    (hst_nonneg : 0 ≤ structuralTail) (hst_lt : structuralTail < 1)
    (hcf_nonneg : 0 ≤ combFailure) (hcf_lt : combFailure < 1)
    (hsf_lt : profileSamplerFailureBound profile < 1) :
    (budgetBoundsOfProfile profile structuralTail combFailure
      hst_nonneg hst_lt hcf_nonneg hcf_lt hsf_lt).samplerFailure =
      profileSamplerFailureBound profile := rfl

theorem profileSamplerFailureBound_fixedF32_lt_one :
    profileSamplerFailureBound fixedF32Profile < 1 := by
  have hcc : (fixedF32Profile.comparisonCountBound : ℝ) = 11024 := by
    norm_num [NativeProfile.comparisonCountBound, NativeProfile.factoryCountBound,
      fixedF32Profile]
  have hfc : (fixedF32Profile.factoryCountBound : ℝ) = 212 := by
    norm_num [NativeProfile.factoryCountBound, fixedF32Profile]
  have hsb : fixedF32Profile.samplerBits = 96 := rfl
  have hfd : fixedF32Profile.factoryDepth = 26 := rfl
  -- comparison contribution
  have e96 : (2 : ℝ) ^ (-(96 : ℝ)) ≤ (2 : ℝ) ^ (-(17 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have e17 : (2 : ℝ) ^ (-(17 : ℝ)) = 1 / 131072 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hcompContrib :
      (fixedF32Profile.comparisonCountBound : ℝ) * comparisonUndecidedBound fixedF32Profile
        < 1 / 2 := by
    rw [hcc]
    unfold comparisonUndecidedBound
    rw [hsb]
    have : (11024 : ℝ) * (4 * (2 : ℝ) ^ (-(96 : ℝ)))
        ≤ 11024 * (4 * (1 / 131072)) := by
      have := e96.trans_eq e17
      nlinarith [this, (by positivity : (0 : ℝ) ≤ (11024 : ℝ) * 4)]
    calc
      (11024 : ℝ) * (4 * (2 : ℝ) ^ (-((96 : ℕ) : ℝ)))
          = 11024 * (4 * (2 : ℝ) ^ (-(96 : ℝ))) := by norm_num
      _ ≤ 11024 * (4 * (1 / 131072)) := this
      _ < 1 / 2 := by norm_num
  -- factory contribution
  have hfac720 : (720 : ℝ) ≤ (Nat.factorial 27 : ℝ) := by
    have h6 : Nat.factorial 6 = 720 := by decide
    have hle : Nat.factorial 6 ≤ Nat.factorial 27 := Nat.factorial_le (by norm_num)
    have : (720 : ℕ) ≤ Nat.factorial 27 := by rw [← h6]; exact hle
    exact_mod_cast this
  have hfactContrib :
      (fixedF32Profile.factoryCountBound : ℝ) * factoryDepthBound fixedF32Profile
        < 1 / 2 := by
    rw [hfc]
    unfold factoryDepthBound
    rw [hfd]
    have hpos : (0 : ℝ) < (Nat.factorial 27 : ℝ) := by
      have : 0 < Nat.factorial 27 := Nat.factorial_pos 27
      exact_mod_cast this
    have hinv : (1 : ℝ) / (Nat.factorial (26 + 1) : ℝ) ≤ 1 / 720 := by
      have h27 : (26 + 1 : ℕ) = 27 := by norm_num
      rw [h27]
      exact one_div_le_one_div_of_le (by norm_num) hfac720
    calc
      (212 : ℝ) * (1 / (Nat.factorial (26 + 1) : ℝ))
          ≤ 212 * (1 / 720) := by
            apply mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ < 1 / 2 := by norm_num
  have := add_lt_add hcompContrib hfactContrib
  unfold profileSamplerFailureBound
  linarith [this]

/-- Fixed-profile budget with the sampler-failure component derived from the
public profile via `profileSamplerFailureBound`.  Compare with
`fixedF32BudgetBounds`, whose sampler-failure component is a hard-coded
constant. -/
def fixedF32BudgetBoundsFromProfile (combFailure : ℝ)
    (hcomb_nonneg : 0 ≤ combFailure)
    (hcomb_lt_one : combFailure < 1) : BudgetBounds :=
  budgetBoundsOfProfile fixedF32Profile
    (2 ^ (-(145.1 : ℝ))) combFailure
    (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num))
    hcomb_nonneg hcomb_lt_one
    profileSamplerFailureBound_fixedF32_lt_one

theorem fixedF32BudgetBoundsFromProfile_samplerFailure
    (combFailure : ℝ)
    (hcomb_nonneg : 0 ≤ combFailure)
    (hcomb_lt_one : combFailure < 1) :
    (fixedF32BudgetBoundsFromProfile combFailure
      hcomb_nonneg hcomb_lt_one).samplerFailure =
      profileSamplerFailureBound fixedF32Profile := rfl

/-- Concrete fixed-profile finite-budget theorem using the profile-derived
sampler-failure budget.  This is the cleanest current target for the Rust
native f32 path: the caller supplies the base RDP proof, structural-stage
Renyi bound, packaged sampler-failure decomposition, and public comb-failure
bound. -/
theorem finiteBudgetTerms_fixedF32_fromProfile_of_samplerFailureDecomposition
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar combFailure : ℝ}
    (hα : 1 < α)
    (hcomb_nonneg : 0 ≤ combFailure)
    (hcomb_lt_one : combFailure < 1)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK
        (fun α =>
          structuralOverhead α
            (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one)))
    (hpSampler : ∃ x ∈ samplerEvent, x ∈ pK.support)
    (hqSampler : ∃ x ∈ samplerEvent, x ∈ qK.support)
    (hsamplerFailure :
      SamplerFailureDecomposition fixedF32Profile pK samplerEvent)
    (hpComb :
      ∃ x ∈ combEvent, x ∈ (pK.filter samplerEvent hpSampler).support)
    (hqComb :
      ∃ x ∈ combEvent, x ∈ (qK.filter samplerEvent hqSampler).support)
    (hcombFailure :
      eventMass (pK.filter samplerEvent hpSampler) combEventᶜ ≤
        ENNReal.ofReal
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).δb) :
    RDPLe
      ((pK.filter samplerEvent hpSampler).filter combEvent hpComb)
      ((qK.filter samplerEvent hqSampler).filter combEvent hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).C
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).lambdaS
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).δb : ℝ) :
        EReal) := by
  exact finiteBudgetTerms_fixedF32_of_samplerFailureDecomposition
    hα
    (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one)
    hbase hprimitive
    (fixedF32BudgetBoundsFromProfile_samplerFailure
      combFailure hcomb_nonneg hcomb_lt_one)
    hstruct hpSampler hqSampler hsamplerFailure hpComb hqComb hcombFailure

/-- Concrete fixed-profile finite-budget theorem using the profile-derived
sampler-failure budget and packaged public-event obligations. -/
theorem finiteBudgetTerms_fixedF32_fromProfile_of_profileFailureEvents
    {p₀ q₀ pK qK : PMF Ω}
    {samplerEvent combEvent : Set Ω}
    {α εbar combFailure : ℝ}
    (hα : 1 < α)
    (hcomb_nonneg : 0 ≤ combFailure)
    (hcomb_lt_one : combFailure < 1)
    {spec : NativeSamplerSpec fixedF32Profile extF32Lattice}
    (hbase : RDPLe p₀ q₀ α (εbar : EReal))
    (hprimitive : PrimitiveProofs fixedF32Profile extF32Lattice spec)
    (hstruct :
      RenyiSumOverhead p₀ q₀ pK qK
        (fun α =>
          structuralOverhead α
            (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one)))
    (hevents :
      ProfileFailureEvents fixedF32Profile
        (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one)
        pK qK samplerEvent combEvent) :
    RDPLe
      ((pK.filter samplerEvent hevents.hpSampler).filter combEvent hevents.hpComb)
      ((qK.filter samplerEvent hevents.hqSampler).filter combEvent hevents.hqComb)
      α
      ((εbar
        + finiteBudgetOverhead α
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).C
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).lambdaS
          (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one).δb : ℝ) :
        EReal) := by
  exact finiteBudgetTerms_fixedF32_of_profileFailureEvents
    hα
    (fixedF32BudgetBoundsFromProfile combFailure hcomb_nonneg hcomb_lt_one)
    hbase hprimitive
    (fixedF32BudgetBoundsFromProfile_samplerFailure
      combFailure hcomb_nonneg hcomb_lt_one)
    hstruct hevents

end RoundedGaussian
end SLang
