/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.Privacy
import SampCert.DifferentialPrivacy.ExponentialMechanism.ExponentialMechanism_DPBridge

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

/--
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
lemma boundedRange_implies_zCDP_slang {T U : Type}
    (m : List T → SLang U) (ε : ℝ)
    (hBR : BoundedRange m ε) :
    ∀ (α : ℝ), 1 < α →
    ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
    ∑' u : U, (m l₁ u) ^ α * (m l₂ u) ^ (1 - α) ≤
      ENNReal.ofReal (Real.exp ((α - 1) * α * ε ^ 2 / 8)) := by
  sorry
  -- Proof requires:
  -- 1. Hoeffding's lemma: for bounded LLR, E[exp(t·LLR)] ≤ exp(t²ε²/2)
  -- 2. Rényi divergence bound: D_α ≤ α·ε²/8
  -- 3. Full formalization in SampCert's Rényi infrastructure

/-! ### Main zCDP theorem -/

/--
The exponential mechanism satisfies ρ-zCDP with ρ = Δ²·ε₁²/(2·ε₂²).

This follows from the BR → zCDP conversion applied to the BR bound
`exponentialMechSLang_BoundedRange`.

**Note**: The `sorry` in `boundedRange_implies_zCDP_slang` is the
remaining proof obligation (Hoeffding's lemma for the Rényi divergence
computation). The BR property itself is fully proved.
-/
theorem exponentialMechSLang_zCDP_renyi
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    ∀ (α : ℝ), 1 < α →
    ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
    ∑' r : Fin n.succ,
      (exponentialMechSLang n (score l₁) ε₁ ε₂ r) ^ α *
      (exponentialMechSLang n (score l₂) ε₁ ε₂ r) ^ (1 - α) ≤
      ENNReal.ofReal (Real.exp ((α - 1) * α *
        ((Δ : ℝ)^2 * (ε₁ : ℝ)^2 / (2 * (ε₂ : ℝ)^2)))) := by
  have hBR := exponentialMechSLang_BoundedRange score Δ ε₁ ε₂ hΔ
  have hrenyi := boundedRange_implies_zCDP_slang _ _ hBR
  intro α hα l₁ l₂ hneigh
  have h := hrenyi α hα l₁ l₂ hneigh
  -- (2Δ·ε₁/ε₂)²/8 = Δ²·ε₁²/(2·ε₂²)
  convert h using 2
  have hε₂ : (ε₂ : ℝ) ≠ 0 := by exact_mod_cast ε₂.pos.ne'
  field_simp [hε₂]
  ring_nf

end ExponentialMechanism
end SLang
