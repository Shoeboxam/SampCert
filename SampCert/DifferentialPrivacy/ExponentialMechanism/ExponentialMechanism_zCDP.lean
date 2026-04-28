/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.Privacy
import SampCert.DifferentialPrivacy.ExponentialMechanism.ExponentialMechanism_DPBridge
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Zero-Concentrated DP for the Exponential Mechanism

**Main theorem** (Theorem A.3 in the final report):
The exponential mechanism satisfies ρ-zCDP with ρ = Δ²·ε₁²/(2·ε₂²).

**Proof strategy** (Cesar & Rogers 2021, Theorem 8):
1. **ε-BR**: EM satisfies `2Δ·ε₁/ε₂`-bounded-range (BR) privacy.
   The existing `exponentialMechSLang_range_privacy` already proves:
     `exp(-(2d·ε₁/ε₂)) · Pr[M(q)=r] ≤ Pr[M(q')=r]`
   which is exactly the BR condition (in both directions by `rangeDistance_comm`).

2. **BR → zCDP**: `ε`-BR implies `ε²/8`-zCDP.
   The key step uses **Hoeffding's lemma**: a bounded log-likelihood ratio
   `|log(M(q)(r)/M(q')(r))| ≤ ε` implies that the moment generating function
   of the LLR satisfies `E[exp(t·LLR)] ≤ exp(t²ε²/2)` for t ∈ [0,1],
   which bounds Rényi divergences as `D_α ≤ α·ε²/8`.

3. **Budget**: With `ε = 2Δ·ε₁/ε₂`:
     ρ = (2Δ·ε₁/ε₂)²/8 = Δ²·ε₁²/(2·ε₂²).

**Status**: The BR property is proved. The BR → zCDP conversion (step 2)
requires formalizing Hoeffding's lemma and connecting it to SampCert's
Rényi divergence infrastructure -- this is the remaining sorry below.
-/

noncomputable section

open Classical
open Real

namespace SLang
namespace ExponentialMechanism

open PermuteAndFlip

/-! ### Step 1: Algebraic identity -/

-- Step 1 key lemma: p^a * q^(1-a) = q * (p/q)^a
-- Proof: q^(1-a) = q * q^(-a) by rpow_add, then merge p^a * (q^-1)^a = (p/q)^a.
-- Requires q ne 0, q ne top, p ne top.
lemma ennreal_rpow_factored (p q : ENNReal) (α : ℝ)
    (hq : q ≠ 0) (hq' : q ≠ ⊤) (hp' : p ≠ ⊤) :
    p ^ α * q ^ (1 - α) = q * (p / q) ^ α := by
  have hinv : q⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hq
  rw [show (1 : ℝ) - α = 1 + (-α) from by ring,
      ENNReal.rpow_add 1 (-α) hq hq',
      ENNReal.rpow_one,
      ENNReal.rpow_neg q α,
      ← ENNReal.inv_rpow q α,
      mul_left_comm (p ^ α) q ((q⁻¹) ^ α),
      ← ENNReal.mul_rpow_of_ne_top hp' hinv,
      ← div_eq_mul_inv p q]

-- Zero case: q = 0 forces p = 0 from BR, so both sides are 0.
lemma ennreal_rpow_factored_zero (α : ℝ) (hα : 0 < α) :
    (0 : ENNReal) ^ α * (0 : ENNReal) ^ (1 - α) = 0 * ((0 : ENNReal) / 0) ^ α := by
  simp [ENNReal.zero_rpow_of_pos hα]

/-! ### Step 2: Ratio bound from BR -/

-- Step 2: From BR (forward) exp(-e)*p <= q, we get p <= exp(e)*q, hence (p/q)^a <= exp(ae).
-- From BR (reverse) exp(-e)*q <= p, we get exp(-ae) <= (p/q)^a.
-- Together: (p/q)^a in [exp(-ae), exp(ae)].

-- Upper bound on (p/q)^a from one-sided BR.
-- ENNReal.div_le_iff (h1 h2): x/y ≤ z ↔ x ≤ z*y
-- ENNReal.div_le_of_le_mul (h : a ≤ b*c): a/c ≤ b  (no side conditions)
lemma ennreal_rpow_div_le_of_BR {p q : ENNReal} (α ε : ℝ) (hα : 0 < α)
    (hBR : ENNReal.ofReal (Real.exp (-ε)) * p ≤ q) :
    (p / q) ^ α ≤ ENNReal.ofReal (Real.exp (α * ε)) := by
  -- Show p/q ≤ exp(ε): from exp(-ε)*p ≤ q, multiply by exp(ε) to get p ≤ exp(ε)*q.
  have hpq_le : p / q ≤ ENNReal.ofReal (Real.exp ε) := by
    have hmul : ENNReal.ofReal (Real.exp ε) * (ENNReal.ofReal (Real.exp (-ε)) * p) ≤
        ENNReal.ofReal (Real.exp ε) * q :=
      mul_le_mul_of_nonneg_left hBR (by positivity)
    have hple : p ≤ ENNReal.ofReal (Real.exp ε) * q := by
      rwa [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
           show ε + -ε = 0 from by ring, Real.exp_zero, ENNReal.ofReal_one, one_mul] at hmul
    exact ENNReal.div_le_of_le_mul hple
  -- Raise both sides to α > 0; exp(ε)^α = exp(α*ε).
  calc (p / q) ^ α
      ≤ ENNReal.ofReal (Real.exp ε) ^ α :=
          ENNReal.rpow_le_rpow hpq_le hα.le
    _ = ENNReal.ofReal (Real.exp (α * ε)) := by
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

-- Lower bound on (p/q)^a from reverse BR.
-- ENNReal.le_div_iff_mul_le (h0 : b≠0∨c≠0) (ht : b≠∞∨c≠∞): a ≤ c/b ↔ a*b ≤ c
lemma ennreal_le_rpow_div_of_BR {p q : ENNReal} (α ε : ℝ) (hα : 0 < α)
    (hBR_rev : ENNReal.ofReal (Real.exp (-ε)) * q ≤ p)
    (hq : q ≠ 0) (hq' : q ≠ ⊤) :
    ENNReal.ofReal (Real.exp (-(α * ε))) ≤ (p / q) ^ α := by
  -- Show exp(-ε) ≤ p/q: a ≤ c/b ↔ a*b ≤ c with a=exp(-ε), b=q, c=p.
  have hpq_ge : ENNReal.ofReal (Real.exp (-ε)) ≤ p / q := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hq) (Or.inl hq')]
    exact hBR_rev
  -- Raise both sides to α; exp(-ε)^α = exp(-(α*ε)).
  calc ENNReal.ofReal (Real.exp (-(α * ε)))
      = ENNReal.ofReal (Real.exp (-ε)) ^ α := by
          rw [show -(α * ε) = (-ε) * α from by ring, Real.exp_mul,
              ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
    _ ≤ (p / q) ^ α :=
          ENNReal.rpow_le_rpow hpq_ge hα.le

/-! ### Bounded-range property -/

/--
ε-bounded-range (BR) privacy for a SLang mechanism `m`:
for all neighbouring datasets and all outputs u,
  `exp(-ε) * m(l₁)(u) ≤ m(l₂)(u)`.

Equivalently: `|log(m(l₁)(u) / m(l₂)(u))| ≤ ε`.
-/
def BoundedRange {T U : Type} (m : List T → SLang U) (ε : ℝ) : Prop :=
  ∀ (l₁ l₂ : List T), Neighbour l₁ l₂ → ∀ (u : U),
    ENNReal.ofReal (exp (-ε)) * m l₁ u ≤ m l₂ u

/--
The exponential mechanism satisfies `2Δ·ε₁/ε₂`-bounded-range privacy.

**Proof**: `exponentialMechSLang_range_privacy` gives
`privacyBase^(2d) · M(q)(r) ≤ M(q')(r)`.
Since `d ≤ Δ`, we have `exp(-2Δ·η) ≤ privacyBase^(2d)`, giving the BR bound.
-/
theorem exponentialMechSLang_BoundedRange
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    BoundedRange (fun l => exponentialMechSLang n (score l) ε₁ ε₂)
      (2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ)) := by
  intro l₁ l₂ hneigh r
  have h_privacy := exponentialMechSLang_range_privacy
    (q := score l₁) (q' := score l₂) (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
  have hd : RangePrivacy.rangeDistance (score l₁) (score l₂) ≤ Δ := hΔ l₁ l₂ hneigh
  have hε₁ : (0 : ℝ) ≤ (ε₁ : ℝ) := Nat.cast_nonneg _
  have hε₂ : (0 : ℝ) < (ε₂ : ℝ) := by exact_mod_cast ε₂.pos
  have hscale : ENNReal.ofReal (exp (-(2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ)))) ≤
      privacyBase ε₁ ε₂ ^ (2 * RangePrivacy.rangeDistance (score l₁) (score l₂)) := by
    simp only [privacyBase, ← ENNReal.ofReal_pow (exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [← exp_nat_mul]; apply exp_le_exp.mpr
    have hd' : (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hd
    have h_le : 2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (ε₁ / ε₂) ≤
        2 * (Δ : ℝ) * (ε₁ / ε₂) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hd' (by norm_num)
      · exact div_nonneg hε₁ hε₂.le
    push_cast
    have key1 : 2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (-(↑ε₁ / ↑↑ε₂)) =
        -(2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (↑ε₁ / ↑↑ε₂)) := by ring
    have key2 : 2 * (Δ : ℝ) * (↑ε₁ / ↑↑ε₂) = 2 * ↑Δ * ↑ε₁ / ↑↑ε₂ := by ring
    linarith [h_le, key1, key2]
  exact (mul_le_mul_of_nonneg_right hscale (by positivity)).trans h_privacy

/-! ### BR → zCDP (Cesar-Rogers 2021) -/

/- 
ε-bounded-range privacy implies ε²/8-zCDP.

**Statement** (Cesar & Rogers 2021, Theorem 8; Durfee & Rogers 2019).

**Proof sketch**: The BR bound gives `|LLR(r)| ≤ ε` for all outputs r.
By Hoeffding's lemma applied to the log-likelihood ratio (a bounded random
variable), the moment generating function satisfies
  `E_{r ∼ M(q)}[exp(t · log(M(q)(r)/M(q')(r)))] ≤ exp(t²ε²/2)`
for t ∈ [0,1]. Taking t = α-1 and using the Rényi divergence definition
  `D_α(M(q) ∥ M(q')) = (1/(α-1)) log E[ratio^(α-1)]`
gives `D_α ≤ α·ε²/8`, hence ε²/8-zCDP.

**Remaining work**: Requires formalizing Hoeffding's lemma and connecting
to SampCert's `RenyiDivergence` infrastructure, which operates on PMF
(not SLang). The type gap (SLang vs PMF) and the MGF bound are the
two main proof obligations.
-/
/- The first attempt at this file stated a fully general
`BoundedRange → zCDP` theorem for arbitrary `m : List T → SLang U`.
That statement is not valid as written: `SLang U` is only `U → ENNReal`,
with no normalization invariant in the type, and the one-sided inequality in
`BoundedRange` is not the tight bounded-range loss-width property used by
Cesar and Rogers.  The theorem we actually need for the project is the
EM-specific Rényi bound below, proved directly from the softmax formula. -/

/-! ### Direct EM Rényi bound (elementary Hoeffding, no measure theory) -/

/-
The key mathematical structure for the EM's Rényi divergence:

Let d_r = gap(q, r) - gap(q', r) ∈ [-Δ, Δ] (integer differences bounded by range distance).
Let η = ε₁/ε₂ and P = M(q) (the EM distribution).

Step A (partition function):
  Z_{q'} = Z_q · E_P[exp(η · d)]
  since ∑_r exp(-η·g'_r) = ∑_r exp(-η·g_r)·exp(η·(g_r-g'_r)) = Z_q · E_P[exp(η·d)].

Step B (Rényi decomposition):
  ∑_r P_r^α · Q_r^{1-α}
  = (Z_P/Z_Q)^{1-α} · E_P[exp((1-α)·η·d)]
  = E_P[exp(η·d)]^{α-1} · E_P[exp((1-α)·η·d)]   [from Step A]

Step C (Hoeffding applied twice):
  With µ = E_P[d] and using Hoeffding for d ∈ [-Δ, Δ]:
  log(E_P[exp(η·d)])     ≤ η·µ + η²·Δ²/2
  log(E_P[exp((1-α)η·d)]) ≤ (1-α)·η·µ + (1-α)²·η²·Δ²/2

Step D (cancellation):
  log(∑ P^α Q^{1-α})
  ≤ (α-1)·[η·µ + η²·Δ²/2] + [(1-α)·η·µ + (1-α)²·η²·Δ²/2]
  = 0·η·µ  +  [(α-1) + (α-1)²]·η²·Δ²/2    [µ terms cancel!]
  = (α-1)·α·η²·Δ²/2
  = (α-1)·α·ε²/8                            [where ε = 2Δη]

This elementary approach uses ONLY:
  - The explicit EM formula (exponentialMechSLang_apply)
  - Hoeffding for FINITE sums in ℝ (no measure theory needed)
  - Algebraic manipulation
-/

-- Hoeffding's inequality for finite discrete distributions in ℝ.
-- For X_i ∈ [-c, c] and probabilities p_i ≥ 0 with ∑ p_i = 1:
--   ∑ p_i * exp(t * X_i) ≤ exp(t * µ + t² * c² / 2)  where µ = ∑ p_i * X_i
--
-- Proof sketch (three steps):
-- Step 1 (convexity, using Real.convexOn_exp):
--   For x ∈ [-c, c]: exp(t*x) ≤ (c-x)/(2c)*exp(-tc) + (c+x)/(2c)*exp(tc).
-- Step 2 (linear algebra):
--   Multiply by p_i and sum: ∑ p_i*exp(t*x_i) ≤ (c-µ)/(2c)*exp(-tc) + (c+µ)/(2c)*exp(tc).
-- Step 3 (binary Hoeffding MGF bound):
--   (c-µ)/(2c)*exp(-tc) + (c+µ)/(2c)*exp(tc) ≤ exp(t*µ + t²c²/2).
--   Proof: this is E[exp(t*X)] for binary X on {-c, c} with E[X] = µ.
--   By Hoeffding for bounded RV: E[exp(t*(X-µ))] ≤ exp(t²*(2c)²/8) = exp(t²c²/2).
--   Equivalently: log E[exp(t*X)] - t*µ ≤ t²c²/2, proven by bounding φ''(t) ≤ c²
--   via Popoviciu's variance inequality (Var(X) ≤ (max-min)²/4 = c²).
lemma hoeffding_finite_sum {n : ℕ} (p x : Fin n → ℝ) (t c : ℝ)
    (hc : 0 ≤ c)
    (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1)
    (hx : ∀ i, |x i| ≤ c) :
    ∑ i, p i * Real.exp (t * x i) ≤
      Real.exp (t * ∑ i, p i * x i + t ^ 2 * c ^ 2 / 2) := by
  -- Build a PMF from p (PMF constructor expects HasSum, not tsum = 1).
  have htsum : ∑' i : Fin n, ENNReal.ofReal (p i) = 1 := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hpsum,
        ENNReal.ofReal_one]
  have hpsum_enn : HasSum (fun i : Fin n => ENNReal.ofReal (p i)) 1 := by
    rw [← htsum]; exact ENNReal.summable.hasSum
  set pmf : PMF (Fin n) := ⟨fun i => ENNReal.ofReal (p i), hpsum_enn⟩
  -- IsProbabilityMeasure: automatic for PMF.toMeasure.
  haveI : MeasureTheory.IsProbabilityMeasure pmf.toMeasure := inferInstance
  -- PMF integral = weighted sum: ∫ f dpmf = ∑ p_i * f_i.
  have hint : ∀ (f : Fin n → ℝ), ∫ i, f i ∂pmf.toMeasure = ∑ i, p i * f i := fun f => by
    rw [PMF.integral_eq_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [pmf, smul_eq_mul]
    exact congr_arg (· * f i) (ENNReal.toReal_ofReal (hp i))
  -- x is AEMeasurable: finite type with discrete sigma-algebra.
  -- AEMeasurable is a top-level abbreviation, not in MeasureTheory namespace.
  have hm : AEMeasurable x pmf.toMeasure :=
    (measurable_of_finite x).aemeasurable
  -- x ∈ [-c, c] everywhere under pmf.
  have hx_icc : ∀ᵐ i ∂pmf.toMeasure, x i ∈ Set.Icc (-c) c :=
    MeasureTheory.ae_of_all pmf.toMeasure fun i =>
      ⟨neg_le_of_abs_le (hx i), le_of_abs_le (hx i)⟩
  -- Apply Mathlib's Hoeffding/sub-Gaussian lemma for bounded random variables.
  -- Result: HasSubgaussianMGF (x - E[x]) ((‖c-(-c)‖₊/2)^2) pmf.
  -- With a = -c, b = c: ‖c-(-c)‖₊/2 = c, so the parameter = c^2.
  -- hasSubgaussianMGF_of_mem_Icc is in ProbabilityTheory namespace (namespace ProbabilityTheory,
  -- section HoeffdingLemma in SubGaussian.lean, after end HasSubgaussianMGF at line 820).
  have hsgf := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hx_icc
  -- Extract: ∫ exp(t*(x-E[x])) ∂pmf ≤ exp(c^2·t^2/2).
  -- mgf is in ProbabilityTheory namespace.
  have hmgf_raw := hsgf.mgf_le t
  simp only [ProbabilityTheory.mgf] at hmgf_raw
  -- The NNReal sub-Gaussian parameter equals c^2 as a real:
  -- (‖c - (-c)‖₊ / 2)^2 = (2c/2)^2 = c^2.
  have hparam : ((‖c - -c‖₊ / 2 : NNReal) ^ 2 : ℝ) = c ^ 2 := by
    rw [NNReal.coe_div]
    simp only [coe_nnnorm, NNReal.coe_ofNat, Real.norm_eq_abs]
    rw [show c - -c = 2 * c from by ring, abs_of_nonneg (by linarith)]
    ring
  -- Compute E[x] = ∑ p_i * x_i.
  have hEX : ∫ i, x i ∂pmf.toMeasure = ∑ i, p i * x i := hint x
  -- Factor the centered MGF: ∫ exp(t*(x-µ)) = exp(-t*µ) * ∫ exp(t*x).
  set mu := ∑ i, p i * x i
  have hfact : ∫ i : Fin n, Real.exp (t * (x i - mu)) ∂pmf.toMeasure =
      Real.exp (-(t * mu)) * ∫ i : Fin n, Real.exp (t * x i) ∂pmf.toMeasure := by
    -- Use hint to convert both integrals to weighted sums, then factor out the constant.
    rw [hint (fun i => Real.exp (t * (x i - mu))),
        hint (fun i => Real.exp (t * x i))]
    simp_rw [show ∀ i : Fin n, Real.exp (t * (x i - mu)) =
               Real.exp (-(t * mu)) * Real.exp (t * x i) from fun i => by
              rw [show t * (x i - mu) = -(t * mu) + t * x i from by ring, Real.exp_add]]
    -- Reorder: p i * (exp(-t*mu) * exp(t*x i)) = exp(-t*mu) * (p i * exp(t*x i))
    simp_rw [show ∀ i : Fin n,
        p i * (Real.exp (-(t * mu)) * Real.exp (t * x i)) =
        Real.exp (-(t * mu)) * (p i * Real.exp (t * x i)) from fun i => by ring]
    rw [← Finset.mul_sum]
  -- Rewrite hmgf_raw: replace ∫ x ∂pmf with mu, then factor exp(-t*mu).
  rw [hEX] at hmgf_raw
  rw [hfact] at hmgf_raw
  -- hmgf_raw : exp(-t*µ) * ∫ exp(t*x) ≤ exp(c^2 * t^2 / 2).
  -- Multiply both sides by exp(t*µ): ∫ exp(t*x) ≤ exp(t*µ + c^2*t^2/2).
  have hbound : ∫ i : Fin n, Real.exp (t * x i) ∂pmf.toMeasure ≤
      Real.exp (t * mu + t ^ 2 * c ^ 2 / 2) := by
    have hexp_mu_pos : 0 < Real.exp (t * mu) := Real.exp_pos _
    -- Rewrite hmgf_raw in terms of the real c^2.
    have hmgf : Real.exp (-(t * mu)) * ∫ i : Fin n, Real.exp (t * x i) ∂pmf.toMeasure ≤
        Real.exp (c ^ 2 * t ^ 2 / 2) := by
      calc Real.exp (-(t * mu)) * _ ≤ Real.exp (↑((‖c - -c‖₊ / 2 : NNReal) ^ 2) * t ^ 2 / 2) :=
              hmgf_raw
        _ = Real.exp (c ^ 2 * t ^ 2 / 2) := by rw [NNReal.coe_pow, hparam]
    rw [show t * mu + t ^ 2 * c ^ 2 / 2 = t * mu + c ^ 2 * t ^ 2 / 2 from by ring,
        Real.exp_add]
    have := mul_le_mul_of_nonneg_left hmgf hexp_mu_pos.le
    rw [← mul_assoc, ← Real.exp_add,
        show t * mu + -(t * mu) = 0 from by ring, Real.exp_zero, one_mul] at this
    exact this
  -- Convert: ∑ p_i * exp(t*x_i) = ∫ exp(t*x) ∂pmf ≤ exp(t*µ + t^2*c^2/2).
  rw [← hint (fun i => Real.exp (t * x i))]
  exact hbound

-- Direct EM-specific Rényi bound via the partition function decomposition.
-- All analysis in ℝ; avoids measure theory entirely.
-- Proof: (Step A) Z' = Z · E_P[exp(η·d)], (Step B) Rényi = E_P[exp(η·d)]^{α-1} · E_P[exp((1-α)η·d)],
--        (Step C) Hoeffding on each factor, (Step D) µ terms cancel → (α-1)α·η²·Δ²/2.
theorem exponentialMechSLang_renyi_direct
    {n : CandidateCount} (q q' : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) (Δ : ℕ)
    (hΔ : RangePrivacy.rangeDistance q q' ≤ Δ)
    (α : ℝ) (hα : 1 < α) :
    -- Real-valued Rényi sum using raw weights (not ENNReal)
    let w  : Fin n.succ → ℝ := fun r => Real.exp (-((gap q  r * ε₁ : ℕ) : ℝ) / ε₂)
    let w' : Fin n.succ → ℝ := fun r => Real.exp (-((gap q' r * ε₁ : ℕ) : ℝ) / ε₂)
    let Z  := ∑ r, w r
    let Z' := ∑ r, w' r
    ∑ r : Fin n.succ, (w r / Z) ^ α * (w' r / Z') ^ (1 - α) ≤
      Real.exp ((α - 1) * α * ((Δ : ℝ) ^ 2 * (ε₁ : ℝ) ^ 2 / (2 * (ε₂ : ℝ) ^ 2))) := by
  have hε₂_pos : (0 : ℝ) < (ε₂ : ℝ) := by exact_mod_cast ε₂.pos
  have hα_pos : 0 < α := by linarith
  -- Unfold the let-bindings from the theorem statement so rewrites can match
  dsimp only
  -- Introduce names matching the let-bound quantities in the statement
  set η : ℝ := (ε₁ : ℝ) / (ε₂ : ℝ) with hη_def
  set w  : Fin n.succ → ℝ := fun r => Real.exp (-((gap q  r * ε₁ : ℕ) : ℝ) / ε₂)
  set w' : Fin n.succ → ℝ := fun r => Real.exp (-((gap q' r * ε₁ : ℕ) : ℝ) / ε₂)
  set Z  : ℝ := ∑ r, w r
  set Z' : ℝ := ∑ r, w' r
  have hw_pos  : ∀ r, 0 < w r  := fun r => Real.exp_pos _
  have hw'_pos : ∀ r, 0 < w' r := fun r => Real.exp_pos _
  have hZ_pos  : 0 < Z  := Finset.sum_pos (fun r _ => hw_pos r) ⟨0, Finset.mem_univ _⟩
  have hZ'_pos : 0 < Z' := Finset.sum_pos (fun r _ => hw'_pos r) ⟨0, Finset.mem_univ _⟩
  -- Probability vectors under M(q) and M(q')
  set P  : Fin n.succ → ℝ := fun r => w r  / Z
  set P' : Fin n.succ → ℝ := fun r => w' r / Z'
  have hP_pos  : ∀ r, 0 < P r  := fun r => div_pos (hw_pos r) hZ_pos
  have hP'_pos : ∀ r, 0 < P' r := fun r => div_pos (hw'_pos r) hZ'_pos
  have hP_sum  : ∑ r : Fin n.succ, P r = 1 := by
    simp only [P]; rw [← Finset.sum_div, div_self hZ_pos.ne']
  -- Gap differences: d_r = gap q r - gap q' r, bounded by Δ
  set d : Fin n.succ → ℝ := fun r => (gap q r : ℝ) - (gap q' r : ℝ)
  -- The range distance bound implies |d_r| ≤ Δ · ε₁/ε₂ in the exponent
  -- Specifically, |gap q r - gap q' r| ≤ rangeDistance q q' ≤ Δ
  have hd_bound : ∀ r, |d r| ≤ (Δ : ℝ) := by
    intro r
    simp only [d]
    rw [abs_le]
    constructor
    · -- -(Δ:ℝ) ≤ gap q r - gap q' r, i.e., gap q' r ≤ gap q r + Δ
      -- gap_le_gap_add_rangeDistance q q' r : gap q' r ≤ gap q r + rangeDistance q q'
      have h : gap q' r ≤ gap q r + RangePrivacy.rangeDistance q q' :=
        gap_le_gap_add_rangeDistance q q' r
      have hle : gap q' r ≤ gap q r + Δ := Nat.le_trans h (Nat.add_le_add_left hΔ _)
      have hle' : (gap q' r : ℝ) ≤ (gap q r : ℝ) + (Δ : ℝ) := by exact_mod_cast hle
      linarith
    · -- gap q r - gap q' r ≤ Δ
      -- gap_le_gap_add_rangeDistance q' q r : gap q r ≤ gap q' r + rangeDistance q' q
      have h : gap q r ≤ gap q' r + RangePrivacy.rangeDistance q' q :=
        gap_le_gap_add_rangeDistance q' q r
      have hcomm : RangePrivacy.rangeDistance q' q ≤ Δ := by rwa [← rangeDistance_comm]
      have hle : gap q r ≤ gap q' r + Δ := Nat.le_trans h (Nat.add_le_add_left hcomm _)
      have hle' : (gap q r : ℝ) ≤ (gap q' r : ℝ) + (Δ : ℝ) := by exact_mod_cast hle
      linarith
  -- Define the two key expectations (MGFs of d under P)
  set T  := ∑ r : Fin n.succ, P r * Real.exp (η * d r)      -- E_P[exp(η·d)]
  set T₁ := ∑ r : Fin n.succ, P r * Real.exp ((1-α) * η * d r)  -- E_P[exp((1-α)η·d)]
  -- Step A: w' r = w r · exp(η · d r), hence Z' = Z · T = Z · E_P[exp(η·d)]
  have hw'_eq : ∀ r, w' r = w r * Real.exp (η * d r) := by
    intro r
    simp only [w, w', d, η]
    rw [← Real.exp_add]
    congr 1
    push_cast
    field_simp [hε₂_pos.ne']
    ring
  have hZ'_eq : Z' = Z * T := by
    have step1 : Z' = ∑ r : Fin n.succ, w r * Real.exp (η * d r) :=
      Finset.sum_congr rfl (fun r _ => hw'_eq r)
    rw [step1]
    simp only [T, P, Finset.mul_sum]
    congr 1; funext r
    field_simp [hZ_pos.ne']
  -- Step B: Rényi decomposition (T and T₁ defined above)
  have hT_pos  : 0 < T  := Finset.sum_pos (fun r _ => mul_pos (hP_pos r) (Real.exp_pos _))
                              ⟨0, Finset.mem_univ _⟩
  have hT₁_pos : 0 < T₁ := Finset.sum_pos (fun r _ => mul_pos (hP_pos r) (Real.exp_pos _))
                              ⟨0, Finset.mem_univ _⟩
  -- The Rényi sum (in terms of w r / Z) equals T^{α-1} · T₁
  -- Algebraic computation:
  --   ∑ r (w r/Z)^α * (w' r/Z')^{1-α}
  --   = ∑ r (w r/Z)^α * (w r · exp(η·d r) / (Z·T))^{1-α}   [using hw'_eq and hZ'_eq]
  --   = ∑ r (w r/Z)^α * (w r/Z)^{1-α} * (exp(η·d r)/T)^{1-α}
  --   = ∑ r (w r/Z) * (exp(η·d r)/T)^{1-α}
  --   = T^{-(1-α)} · ∑ r P r · exp((1-α)·η·d r)   [pulling out T^{1-α}]
  --   = T^{α-1} · T₁                                [T^{-(1-α)} = T^{α-1}]
  -- Pointwise identity: (w r/Z)^α * (w'r/Z')^{1-α} = (w r/Z) * T^{α-1} * exp((1-α)η·d r)
  -- Proof sketch: w'/Z' = (w·exp(η·d))/(Z·T), then split rpow, use a^α·a^{1-α}=a, T^{-(1-α)}=T^{α-1}
  have hpoint : ∀ r : Fin n.succ,
      (w r / Z) ^ α * (w' r / Z') ^ (1 - α) =
      (w r / Z) * T ^ (α - 1) * Real.exp ((1 - α) * η * d r) := by
    intro r
    have hPr_pos : 0 < w r / Z := div_pos (hw_pos r) hZ_pos
    -- Substitute w'r = w r * exp(η * d r) and Z' = Z * T
    rw [hw'_eq r, hZ'_eq]
    -- Rewrite to form (w r/Z) * (exp(η*d r) / T) applied to the second factor
    rw [show w r * Real.exp (η * d r) / (Z * T) =
           (w r / Z) * (Real.exp (η * d r) / T) from by
          field_simp [hZ_pos.ne', hT_pos.ne']]
    -- Split: (a * b)^{1-α} = a^{1-α} * b^{1-α}
    rw [Real.mul_rpow hPr_pos.le (div_nonneg (Real.exp_nonneg _) hT_pos.le)]
    -- Rearrange so a^α * a^{1-α} are adjacent
    rw [← mul_assoc]
    -- Merge: a^α * a^{1-α} = a^(α + (1-α)) = a^1 = a
    rw [← Real.rpow_add hPr_pos, show α + (1 - α) = 1 from by ring, Real.rpow_one]
    -- Split: (exp(η*d r) / T)^{1-α} = exp(η*d r)^{1-α} / T^{1-α}
    rw [Real.div_rpow (Real.exp_nonneg _) hT_pos.le]
    -- Rewrite exp^{1-α}: (exp x)^y = exp(x*y)
    rw [← Real.exp_mul, show η * d r * (1 - α) = (1 - α) * η * d r from by ring]
    -- Rewrite 1/T^{1-α} = T^{α-1} using explicit div_eq_mul_inv on the T term
    rw [div_eq_mul_inv (Real.exp ((1 - α) * η * d r)) (T ^ (1 - α)),
        ← Real.rpow_neg hT_pos.le, show -(1 - α) = α - 1 from by ring]
    ring
  have hrenyi_eq : ∑ r : Fin n.succ, (w r / Z) ^ α * (w' r / Z') ^ (1 - α) =
      T ^ (α - 1) * T₁ := by
    simp_rw [hpoint]
    -- Reorder to pull T^{α-1} out of the sum
    simp_rw [show ∀ r : Fin n.succ,
        w r / Z * T ^ (α - 1) * Real.exp ((1 - α) * η * d r) =
        T ^ (α - 1) * (w r / Z * Real.exp ((1 - α) * η * d r)) from fun r => by ring]
    rw [← Finset.mul_sum]
    -- T₁ is definitionally ∑ r, P r * exp = ∑ r, w r/Z * exp, so this closes by rfl
  rw [hrenyi_eq]
  -- Step C: Apply Hoeffding to T and T₁
  -- For the d-variable: |d r · η| ≤ Δ · η = Δ · ε₁/ε₂
  -- Hoeffding: log T ≤ η · µ + η² · Δ² / 2
  -- Hoeffding: log T₁ ≤ (1-α)·η·µ + (1-α)²·η²·Δ²/2
  -- where µ = ∑ r, P r · d r
  set mu := ∑ r : Fin n.succ, P r * d r
  -- Step C: Hoeffding applied to T and T₁ (using hd_bound: |d r| ≤ Δ)
  have hT_hoeffding : T ≤ Real.exp (η * mu + η ^ 2 * (Δ : ℝ) ^ 2 / 2) :=
    hoeffding_finite_sum P d η (Δ : ℝ) (by positivity) (fun r => (hP_pos r).le) hP_sum hd_bound
  have hT₁_hoeffding : T₁ ≤ Real.exp ((1 - α) * η * mu + ((1 - α) * η) ^ 2 * (Δ : ℝ) ^ 2 / 2) :=
    hoeffding_finite_sum P d ((1 - α) * η) (Δ : ℝ) (by positivity)
      (fun r => (hP_pos r).le) hP_sum hd_bound
  -- Step D: Combine and use T^{α-1} ≤ exp((α-1)·(η·mu + η²·Δ²/2))
  have hT_rpow : T ^ (α - 1) ≤ Real.exp ((α - 1) * (η * mu + η ^ 2 * (Δ : ℝ) ^ 2 / 2)) := by
    have hα1 : 0 ≤ α - 1 := by linarith
    rw [← Real.exp_log hT_pos, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log hT_pos hT_hoeffding
    rw [Real.log_exp] at hlog
    nlinarith [mul_le_mul_of_nonneg_right hlog hα1]
  calc T ^ (α - 1) * T₁
      ≤ Real.exp ((α-1) * (η*mu + η^2 * (Δ:ℝ)^2 / 2)) *
          Real.exp ((1-α)*η*mu + ((1-α)*η)^2 * (Δ:ℝ)^2 / 2) :=
          mul_le_mul hT_rpow hT₁_hoeffding hT₁_pos.le (by positivity)
    _ = Real.exp ((α-1) * α * ((Δ:ℝ)^2 * (ε₁:ℝ)^2 / (2 * (ε₂:ℝ)^2))) := by
          rw [← Real.exp_add]; congr 1
          -- µ terms cancel: (α-1)·η·µ + (1-α)·η·µ = 0
          -- Δ² terms: (α-1)·η²·Δ²/2 + (α-1)²·η²·Δ²/2 = (α-1)·α·η²·Δ²/2
          simp only [η]; field_simp [hε₂_pos.ne']; ring

/-! ### Main zCDP theorem -/

/--
The exponential mechanism satisfies ρ-zCDP with ρ = Δ²·ε₁²/(2·ε₂²).

This is the dataset-level wrapper around the direct finite-dimensional
Rényi calculation `exponentialMechSLang_renyi_direct`.
-/
theorem exponentialMechSLang_zCDP_renyi
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    ∀ (α : ℝ), 1 < α →
    ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
    let w  : Fin n.succ → ℝ :=
      fun r => Real.exp (-((gap (score l₁) r * ε₁ : ℕ) : ℝ) / ε₂)
    let w' : Fin n.succ → ℝ :=
      fun r => Real.exp (-((gap (score l₂) r * ε₁ : ℕ) : ℝ) / ε₂)
    let Z  := ∑ r, w r
    let Z' := ∑ r, w' r
    ∑ r : Fin n.succ, (w r / Z) ^ α * (w' r / Z') ^ (1 - α) ≤
      Real.exp ((α - 1) * α *
        ((Δ : ℝ)^2 * (ε₁ : ℝ)^2 / (2 * (ε₂ : ℝ)^2))) := by
  intro α hα l₁ l₂ hneigh
  simpa using
    exponentialMechSLang_renyi_direct
      (q := score l₁) (q' := score l₂) (ε₁ := ε₁) (ε₂ := ε₂) (Δ := Δ)
      (hΔ l₁ l₂ hneigh) α hα

end ExponentialMechanism
end SLang
