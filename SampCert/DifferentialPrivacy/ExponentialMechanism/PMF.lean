/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.Code

/-!
PMF characterization of the exponential mechanism.

Main theorem: `exponentialMechSLang_apply` — the output distribution is the
softmax `exp(-gap(q, r) · ε₁/ε₂) / Σᵢ exp(-gap(q, i) · ε₁/ε₂)`.
-/

noncomputable section

open scoped Classical
open PMF ENNReal

namespace SLang
namespace ExponentialMechanism

open PermuteAndFlip

/--
The PMF loop body at `(r, b)` equals `uniform r * exactCoinPMF (gap q r * ε₁) ε₂ b`.
-/
theorem expMechPMF_apply (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (r : Fin n.succ) (b : Bool) :
    expMechPMF n q ε₁ ε₂ (r, b) =
      PMF.uniformOfFintype (Fin n.succ) r * exactCoinPMF (gap q r * ε₁) ε₂ b := by
  -- simp with PMF.bind_apply unfolds the do-block; it converts the Bool tsum to ifs
  -- and the Fin tsum to a finset sum.
  simp [expMechPMF, PMF.bind_apply, PMF.pure_apply]
  -- Collapse ∑ a over Fin n.succ: only a = r is nonzero.
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ _) (fun a _ ha => by simp [ha.symm])]
  -- Match exactCoinPMF by cases on b.
  cases b
  · simp [exactCoinPMF_apply_false]
  · -- Simplify the two ite conditions: r=r∧true=true → exp(A), r=r∧true=false → 0.
    simp only [true_and, ite_true]
    rw [if_neg (by decide : ¬(true = false)), add_zero]
    -- Now: (n+1)⁻¹ * ofReal(exp(A)) = (n+1)⁻¹ * exactCoinPMF ... true
    congr 1
    rw [exactCoinPMF_apply_true]
    apply congr_arg ENNReal.ofReal; apply congr_arg Real.exp
    simp [Nat.cast_mul]

/-- The loop body sums to 1. -/
theorem expMechLoop_normalizes (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    ∑' x : Fin n.succ × Bool, expMechLoop n q ε₁ ε₂ x = 1 := by
  rw [expMechLoop_eq_expMechPMF]
  exact PMF.tsum_coe _

/-- The loop body mass at `(r, true)` in the explicit exponential form. -/
theorem expMechLoop_apply_true (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (r : Fin n.succ) :
    expMechLoop n q ε₁ ε₂ (r, true) =
      PMF.uniformOfFintype (Fin n.succ) r *
        ENNReal.ofReal (Real.exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) := by
  rw [expMechLoop_eq_expMechPMF, expMechPMF_apply, exactCoinPMF_apply_true]
  -- Remaining: -(a/b) vs -a/b; both equal in ℝ by ring.
  congr 1; apply congr_arg ENNReal.ofReal; apply congr_arg Real.exp; ring

/--
After the `probUntil` loop, the mass at `(r, true)` is the normalized softmax weight.
The `1/(n+1)` factors from the uniform distribution cancel.
-/
theorem expUntil_apply (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (r : Fin n.succ) :
    probUntil (expMechLoop n q ε₁ ε₂) (fun x => x.2) (r, true) =
      ENNReal.ofReal (Real.exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) /
        ∑' i : Fin n.succ,
          ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)) := by
  rw [probUntil_apply_norm _ _ _ (expMechLoop_normalizes n q ε₁ ε₂)]
  simp only [ite_true, expMechLoop_apply_true]
  -- Simplify the denominator: Σ_{(i,b)} [if b then loop(i,b) else 0] = (n+1)⁻¹ · Z
  have hden : ∑' x : Fin n.succ × Bool, (if x.2 then expMechLoop n q ε₁ ε₂ x else 0) =
      (↑(Fintype.card (Fin n.succ)) : ℝ≥0∞)⁻¹ *
        ∑' i : Fin n.succ,
          ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)) := by
    rw [ENNReal.tsum_prod']
    -- simp_rw (not simp) to avoid tsum_fintype converting to a Finset.sum prematurely.
    simp_rw [tsum_bool]
    -- The Bool sum yields `if (false = true : Prop) then ...` not `if false then ...`.
    -- Rewrite the Prop condition to False, then ite_false fires.
    simp only [show (false : Bool) = true ↔ False from by decide, ite_false, zero_add, ite_true]
    simp_rw [expMechLoop_apply_true, PMF.uniformOfFintype_apply]
    rw [ENNReal.tsum_mul_left]
  rw [hden, PMF.uniformOfFintype_apply, Fintype.card_fin]
  -- Goal: (↑(n+1))⁻¹ * A * ((↑(n+1))⁻¹ * Z)⁻¹ = A / Z
  -- In ENNReal, a / b = a * b⁻¹ by definition, so this rfl reduces to mul_div_mul_left.
  have h_rfl : (↑(Nat.succ n) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (Real.exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) *
        ((↑(Nat.succ n) : ℝ≥0∞)⁻¹ *
          ∑' i, ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)))⁻¹ =
      (↑(Nat.succ n) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (Real.exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) /
        ((↑(Nat.succ n) : ℝ≥0∞)⁻¹ *
          ∑' i, ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂))) := rfl
  rw [h_rfl]
  apply ENNReal.mul_div_mul_left
  · rw [ne_eq, ENNReal.inv_eq_zero]; exact ENNReal.natCast_ne_top _
  · rw [ne_eq, ENNReal.inv_eq_top]; simp

/--
The exponential mechanism outputs the softmax PMF:
`Pr[M_EM(q) = r] = exp(-gap(q, r) · ε₁/ε₂) / Σᵢ exp(-gap(q, i) · ε₁/ε₂)`.
-/
theorem exponentialMechSLang_apply (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (r : Fin n.succ) :
    exponentialMechSLang n q ε₁ ε₂ r =
      ENNReal.ofReal (Real.exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) /
        ∑' i : Fin n.succ,
          ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)) := by
  -- Reduce to probUntil at (r, true), then apply expUntil_apply.
  suffices h : exponentialMechSLang n q ε₁ ε₂ r =
      probUntil (expMechLoop n q ε₁ ε₂) (fun x => x.2) (r, true) by
    rw [h, expUntil_apply]
  -- The do-block is probBind (probUntil ...) (fun x => probPure x.1).
  -- Use 'show' to make the >>= explicit as probBind (definitionally equal).
  simp only [exponentialMechSLang]
  show probBind (probUntil (expMechLoop n q ε₁ ε₂) (fun x => x.2)) (fun x => probPure x.1) r = _
  simp only [probBind, probPure]
  -- Apply tsum_eq_single directly on the pair type: only (r, true) contributes.
  rw [tsum_eq_single (r, true) (fun ⟨i, b⟩ h => by
    cases b with
    | false => simp [probUntil_apply_unsat]
    | true =>
        -- (i, true) ≠ (r, true) means i ≠ r; the condition appears as `if r = i` (reversed).
        have hi : i ≠ r := by rintro rfl; exact h rfl
        -- Ne.symm hi : r ≠ i; if_neg eliminates `if r = i then A else 0 = 0`.
        rw [if_neg (Ne.symm hi)]
        exact mul_zero _)]
  simp

end ExponentialMechanism
end SLang
