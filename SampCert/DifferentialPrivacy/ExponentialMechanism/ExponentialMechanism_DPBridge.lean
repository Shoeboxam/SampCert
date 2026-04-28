/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.Privacy
import SampCert.DifferentialPrivacy.Pure.DP

/-!
# Pure DP bridge for the Exponential Mechanism

This file connects the pointwise range-distance privacy theorem to a
dataset-level pure DP statement.

Since `exponentialMechSLang` returns a `SLang` (not a `PMF`), we state
the DP property directly in the `DP_singleton` style (pointwise ratio bound
over datasets) rather than through `SLang.Mechanism T U = List T → PMF U`.

**Result**: The EM with parameters `ε₁/ε₂` and a `Δ`-range-sensitive score
function satisfies the pointwise ε-DP ratio bound with `ε = 2·Δ·ε₁/ε₂`.
-/

noncomputable section

open Classical
open Real

namespace SLang
namespace ExponentialMechanism

open PermuteAndFlip

/-! ### Range sensitivity -/

/--
The score map has range sensitivity `Δ` when neighbouring datasets induce
score vectors whose range distance is at most `Δ`.
-/
def rangeSensitive {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) : Prop :=
  ∀ l₁ l₂ : List T, Neighbour l₁ l₂ →
    RangePrivacy.rangeDistance (score l₁) (score l₂) ≤ Δ

/-! ### DP singleton (pointwise ratio) bound -/

/--
The EM satisfies the pointwise ratio bound over neighbouring datasets.

For all outputs `r` and neighbours `l₁ ~ l₂`:
```
exponentialMechSLang(score l₁) r / exponentialMechSLang(score l₂) r
  ≤ exp(2 · Δ · ε₁/ε₂)
```

**Proof**: Apply `exponentialMechSLang_range_privacy` with the actual
range distance `d = rangeDistance(score l₁, score l₂) ≤ Δ`, then scale up
from `privacyBase^(2d)` to the fixed budget `exp(2Δ·ε₁/ε₂)`.
-/
theorem exponentialMechSLang_DP_singleton
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ r : Fin n.succ,
      exponentialMechSLang n (score l₁) ε₁ ε₂ r /
      exponentialMechSLang n (score l₂) ε₁ ε₂ r ≤
      ENNReal.ofReal (exp (2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ))) := by
  intro l₁ l₂ hneigh r
  have h_privacy := exponentialMechSLang_range_privacy
    (q := score l₁) (q' := score l₂) (r := r) (ε₁ := ε₁) (ε₂ := ε₂)
  have hd : RangePrivacy.rangeDistance (score l₁) (score l₂) ≤ Δ := hΔ l₁ l₂ hneigh
  have hε₁ : (0 : ℝ) ≤ (ε₁ : ℝ) := Nat.cast_nonneg _
  have hε₂ : (0 : ℝ) < (ε₂ : ℝ) := by exact_mod_cast ε₂.pos
  -- exp(-2Δη) ≤ privacyBase^(2d) since d ≤ Δ
  have hscale : ENNReal.ofReal (exp (-(2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ)))) ≤
      privacyBase ε₁ ε₂ ^ (2 * RangePrivacy.rangeDistance (score l₁) (score l₂)) := by
    simp only [privacyBase, ← ENNReal.ofReal_pow (exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [← exp_nat_mul]; apply exp_le_exp.mpr
    have hd' : (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hd
    -- Need: -(2Δε₁/ε₂) ≤ 2*rangeDistance*(-(ε₁/ε₂)), i.e., 2*d*ε₁/ε₂ ≤ 2*Δ*ε₁/ε₂
    have h_le : 2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (ε₁ / ε₂) ≤
        2 * (Δ : ℝ) * (ε₁ / ε₂) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hd' (by norm_num)
      · exact div_nonneg hε₁ hε₂.le
    -- Need: -(2Δε₁/ε₂) ≤ 2d*(-(ε₁/ε₂)); use ring to equate 2d*(-(ε₁/ε₂)) = -(2d*(ε₁/ε₂)).
    -- Then from h_le: 2d*(ε₁/ε₂) ≤ 2Δ*(ε₁/ε₂), negate to get the result.
    push_cast
    -- key1: relate d*(-(ε₁/ε₂)) to -(d*(ε₁/ε₂))
    have key1 : 2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (-(↑ε₁ / ↑↑ε₂)) =
        -(2 * (RangePrivacy.rangeDistance (score l₁) (score l₂) : ℝ) * (↑ε₁ / ↑↑ε₂)) := by ring
    -- key2: unify Δ*(ε₁/ε₂) with Δ*ε₁/ε₂ (different parenthesisation in `at`)
    have key2 : 2 * (Δ : ℝ) * (↑ε₁ / ↑↑ε₂) = 2 * ↑Δ * ↑ε₁ / ↑↑ε₂ := by ring
    linarith [h_le, key1, key2]
  -- exp(-2Δη) * M(q₁) r ≤ M(q₂) r
  have h1 : ENNReal.ofReal (exp (-(2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ)))) *
        exponentialMechSLang n (score l₁) ε₁ ε₂ r ≤
        exponentialMechSLang n (score l₂) ε₁ ε₂ r :=
    (mul_le_mul_of_nonneg_right hscale (by positivity)).trans h_privacy
  -- M(q₁)/M(q₂) ≤ exp(2Δη):
  -- From h1: exp(-ε)*M₁ ≤ M₂. Multiply by exp(ε): M₁ ≤ exp(ε)*M₂.
  -- Hence M₁/M₂ ≤ exp(ε).
  calc exponentialMechSLang n (score l₁) ε₁ ε₂ r
        / exponentialMechSLang n (score l₂) ε₁ ε₂ r
      ≤ ENNReal.ofReal (exp (2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ))) := by
          apply ENNReal.div_le_of_le_mul
          calc exponentialMechSLang n (score l₁) ε₁ ε₂ r
              = 1 * exponentialMechSLang n (score l₁) ε₁ ε₂ r := (one_mul _).symm
            _ = (ENNReal.ofReal (exp (2 * (Δ : ℝ) * ε₁ / ε₂)) *
                  ENNReal.ofReal (exp (-(2 * (Δ : ℝ) * ε₁ / ε₂)))) *
                  exponentialMechSLang n (score l₁) ε₁ ε₂ r := by
                    rw [← ENNReal.ofReal_mul (exp_nonneg _), ← exp_add]; norm_num
            _ = ENNReal.ofReal (exp (2 * (Δ : ℝ) * ε₁ / ε₂)) *
                  (ENNReal.ofReal (exp (-(2 * (Δ : ℝ) * ε₁ / ε₂))) *
                    exponentialMechSLang n (score l₁) ε₁ ε₂ r) := by ring
            _ ≤ ENNReal.ofReal (exp (2 * (Δ : ℝ) * ε₁ / ε₂)) *
                  exponentialMechSLang n (score l₂) ε₁ ε₂ r :=
                    mul_le_mul_of_nonneg_left h1 (by positivity)

/--
Equivalently: the EM is `(2 · Δ · ε₁/ε₂)`-differentially private at the
pointwise (output-by-output) level over neighbouring datasets.

This is the `DP_singleton` formulation: the ratio of output probabilities is
bounded by `exp(ε)` for each output and each pair of neighbouring inputs.
-/
theorem exponentialMechSLang_pureDP_of_rangeSensitive
    {T : Type} {n : CandidateCount}
    (score : List T → Scores n) (Δ : ℕ) (ε₁ : ℕ) (ε₂ : ℕ+)
    (hΔ : rangeSensitive score Δ) :
    ∀ l₁ l₂ : List T, Neighbour l₁ l₂ → ∀ r : Fin n.succ,
      exponentialMechSLang n (score l₁) ε₁ ε₂ r /
      exponentialMechSLang n (score l₂) ε₁ ε₂ r ≤
      ENNReal.ofReal (exp (2 * (Δ : ℝ) * (ε₁ : ℝ) / (ε₂ : ℝ))) :=
  exponentialMechSLang_DP_singleton score Δ ε₁ ε₂ hΔ

end ExponentialMechanism
end SLang
