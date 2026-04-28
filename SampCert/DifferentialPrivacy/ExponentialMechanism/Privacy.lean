/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.PMF
import SampCert.DifferentialPrivacy.PermuteAndFlip.Privacy

/-!
Range-distance privacy theorem for the exponential mechanism.

Main theorem: `exponentialMechSLang_range_privacy`.

The proof bounds the softmax ratio using two exponential contractions:
- **Numerator**: `privacyBase^d · exp(-gap(q,r)·η) ≤ exp(-gap(q',r)·η)`, using `gap(q',r) ≤ gap(q,r) + d`.
- **Denominator**: `privacyBase^d · Σᵢ exp(-gap(q',i)·η) ≤ Σᵢ exp(-gap(q,i)·η)`, by the same bound with `q` and `q'` swapped.

Together these give `privacyBase^(2d) · Pr[M(q)=r] ≤ Pr[M(q')=r]`.
-/

noncomputable section

open scoped Classical
open ENNReal Real

namespace SLang
namespace ExponentialMechanism

-- Open PermuteAndFlip but hide the IntScores-based rangeDistance from Reduction.lean
-- to avoid ambiguity with RangePrivacy.rangeDistance.
open PermuteAndFlip hiding rangeDistance

/-! ### Gap arithmetic -/

/--
`gap(q', r) ≤ gap(q, r) + rangeDistance(q, q')`.
-/
lemma gap_le_gap_add_rangeDistance {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) :
    gap q' r ≤ gap q r + RangePrivacy.rangeDistance q q' := by
  rw [gap_eq_maxScore_sub, gap_eq_maxScore_sub]
  have hqr  : q r  ≤ maxScore q  := Finset.le_sup (s := Finset.univ) (f := q)  (by simp)
  have hq'r : q' r ≤ maxScore q' := Finset.le_sup (s := Finset.univ) (f := q') (by simp)
  zify [hqr, hq'r]
  open PermuteAndFlip.RangePrivacy in
  have hrd_nn : (0 : ℤ) ≤ diffMax q q' - diffMin q q' :=
    Int.sub_nonneg.mpr (Finset.min'_le _ _ (Finset.max'_mem _ (diffSet_nonempty q q')))
  open PermuteAndFlip.RangePrivacy in
  have hrd : (RangePrivacy.rangeDistance q q' : ℤ) = diffMax q q' - diffMin q q' := by
    simp only [RangePrivacy.rangeDistance]
    rw [Int.toNat_of_nonneg hrd_nn]
  rw [hrd]
  open PermuteAndFlip.RangePrivacy in
  have h_maxdiff : (maxScore q' : ℤ) - maxScore q ≤ diffMax q q' := by
    obtain ⟨j, hj⟩ := exists_argmax q'
    have hqj : q j ≤ maxScore q := Finset.le_sup (s := Finset.univ) (f := q) (by simp)
    calc (maxScore q' : ℤ) - maxScore q
        = q' j - maxScore q := by rw [← hj]
      _ ≤ q' j - q j := by linarith [show (q j : ℤ) ≤ maxScore q from by exact_mod_cast hqj]
      _ = scoreDiff q q' j := by simp [scoreDiff]
      _ ≤ diffMax q q' := Finset.le_max' _ _ (by simp [diffSet])
  open PermuteAndFlip.RangePrivacy in
  have h_rdiff : (q r : ℤ) - q' r ≤ -diffMin q q' := by
    have : diffMin q q' ≤ scoreDiff q q' r := Finset.min'_le _ _ (by simp [diffSet])
    simp [scoreDiff] at this; omega
  linarith

/-- Range distance is symmetric. -/
lemma rangeDistance_comm {n : CandidateCount} (q q' : Scores n) :
    RangePrivacy.rangeDistance q q' = RangePrivacy.rangeDistance q' q := by
  open PermuteAndFlip.RangePrivacy in
  simp only [rangeDistance]
  -- scoreDiff q' q = -scoreDiff q q', so diffSet q' q = neg-image of diffSet q q'
  have hscoreDiff : ∀ i, scoreDiff q' q i = -scoreDiff q q' i := fun i => by
    simp [scoreDiff]
  have hdiffSet : diffSet q' q = (diffSet q q').image (-·) := by
    ext d; simp only [diffSet, Finset.mem_image]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact ⟨scoreDiff q q' i, ⟨i, Finset.mem_univ _, rfl⟩, (hscoreDiff i).symm⟩
    · rintro ⟨d', ⟨i, _, rfl⟩, rfl⟩
      exact ⟨i, Finset.mem_univ _, hscoreDiff i⟩
  -- max of neg-image = -min of original, and vice versa.
  -- Avoid `rw [diffMax, hdiffSet]` directly: the motive is ill-typed because the
  -- nonemptiness proof depends on `diffSet q' q`. Instead, prove via membership.
  -- In Lean 4, Finset.le_max' (s x hx) : x ≤ s.max' ⟨x,hx⟩ (no separate Nonempty arg).
  -- Similarly Finset.min'_le (s x hx) : s.min' ⟨x,hx⟩ ≤ x.
  have hmax : diffMax q' q = -diffMin q q' := by
    apply le_antisymm
    · -- max{-d_i} ≤ -min{d_i}: each -d_i ≤ -min{d_i} since d_i ≥ min{d_i}
      simp only [diffMax, diffMin]
      apply Finset.max'_le _ (diffSet_nonempty q' q)
      intro d hd
      rw [hdiffSet] at hd
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
      exact neg_le_neg (Finset.min'_le _ d' hd')
    · -- -min{d_i} ≤ max{-d_i}: -min' is in the image so ≤ max'
      have hmem : -diffMin q q' ∈ diffSet q' q := by
        rw [hdiffSet]; exact Finset.mem_image.mpr ⟨diffMin q q', Finset.min'_mem _ _, rfl⟩
      simp only [diffMax]
      exact Finset.le_max' _ (-diffMin q q') hmem
  have hmin : diffMin q' q = -diffMax q q' := by
    apply le_antisymm
    · -- min{-d_i} ≤ -max{d_i}: -max' is in the image so ≥ min'
      have hmem : -diffMax q q' ∈ diffSet q' q := by
        rw [hdiffSet]; exact Finset.mem_image.mpr ⟨diffMax q q', Finset.max'_mem _ _, rfl⟩
      simp only [diffMin]
      exact Finset.min'_le _ (-diffMax q q') hmem
    · -- -max{d_i} ≤ min{-d_i}: each -d_i ≥ -max{d_i} since d_i ≤ max{d_i}
      simp only [diffMin, diffMax]
      apply Finset.le_min' _ (diffSet_nonempty q' q)
      intro d hd
      rw [hdiffSet] at hd
      obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
      exact neg_le_neg (Finset.le_max' _ d' hd')
  -- After rw [hmax, hmin], RHS = -diffMin q q' - -diffMax q q' = diffMax q q' - diffMin q q'.
  congr 1; rw [hmax, hmin]; ring

/-! ### Exponential contraction -/

/--
`privacyBase^d · exp(-gap(q,r)·η) ≤ exp(-gap(q',r)·η)`,
because `gap(q',r) ≤ gap(q,r) + d`.
-/
lemma exactCoin_contraction {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ)
    (ε₁ : ℕ) (ε₂ : ℕ+) :
    privacyBase ε₁ ε₂ ^ RangePrivacy.rangeDistance q q' *
        ENNReal.ofReal (exp (- ((gap q r * ε₁ : ℕ) : NNReal) / ε₂)) ≤
      ENNReal.ofReal (exp (- ((gap q' r * ε₁ : ℕ) : NNReal) / ε₂)) := by
  rw [privacyBase, ← ENNReal.ofReal_pow (exp_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← exp_nat_mul, ← exp_add]
  apply exp_le_exp.mpr
  -- Goal: d * -(ε₁/ε₂) + -(gap(q,r)·ε₁/ε₂) ≤ -(gap(q',r)·ε₁/ε₂)
  -- Equivalently: gap(q',r)·ε₁/ε₂ ≤ gap(q,r)·ε₁/ε₂ + d·ε₁/ε₂
  have hε₁ : (0 : ℝ) ≤ (ε₁ : ℝ) := Nat.cast_nonneg _
  have hε₂ : (0 : ℝ) < (ε₂ : ℝ) := by exact_mod_cast ε₂.pos
  have hle' : (gap q' r : ℝ) ≤ (gap q r : ℝ) + (RangePrivacy.rangeDistance q q' : ℝ) :=
    by exact_mod_cast gap_le_gap_add_rangeDistance q q' r
  -- Build the key product inequality in explicit expanded form.
  have hprod : (gap q' r : ℝ) * ε₁ / ε₂ ≤
      (gap q r : ℝ) * ε₁ / ε₂ + (RangePrivacy.rangeDistance q q' : ℝ) * ε₁ / ε₂ := by
    have h : (gap q' r : ℝ) * ε₁ ≤
        ((gap q r : ℝ) + RangePrivacy.rangeDistance q q') * ε₁ :=
      mul_le_mul_of_nonneg_right hle' hε₁
    have step : (gap q' r : ℝ) * ε₁ / ε₂ ≤
        ((gap q r : ℝ) + RangePrivacy.rangeDistance q q') * ε₁ / ε₂ := by gcongr
    linarith [show ((gap q r : ℝ) + RangePrivacy.rangeDistance q q') * ε₁ / ε₂ =
        (gap q r : ℝ) * ε₁ / ε₂ + (RangePrivacy.rangeDistance q q' : ℝ) * ε₁ / ε₂ from by ring]
  push_cast at *
  -- ring_nf normalises -(a*b)/c and d*-(e/f) to matching atoms so linarith can close.
  ring_nf at *
  linarith [hprod]

/--
`privacyBase^d · Σᵢ exp(-gap(q',i)·η) ≤ Σᵢ exp(-gap(q,i)·η)`.
-/
lemma exactCoin_sum_contraction {n : CandidateCount} (q q' : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    privacyBase ε₁ ε₂ ^ RangePrivacy.rangeDistance q q' *
        ∑' i : Fin n.succ, ENNReal.ofReal (exp (- ((gap q' i * ε₁ : ℕ) : NNReal) / ε₂)) ≤
      ∑' i : Fin n.succ, ENNReal.ofReal (exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum; intro i
  rw [rangeDistance_comm]
  exact exactCoin_contraction q' q i ε₁ ε₂

/-! ### Main theorem -/

/--
Pointwise range-distance privacy for the exponential mechanism:

  `privacyBase^(2d) · Pr[M_EM(q) = r] ≤ Pr[M_EM(q') = r]`.
-/
theorem exponentialMechSLang_range_privacy
    {n : CandidateCount} (q q' : Scores n) (r : Fin n.succ) (ε₁ : ℕ) (ε₂ : ℕ+) :
    privacyBase ε₁ ε₂ ^ (2 * RangePrivacy.rangeDistance q q') *
        exponentialMechSLang n q ε₁ ε₂ r ≤
      exponentialMechSLang n q' ε₁ ε₂ r := by
  rw [exponentialMechSLang_apply, exponentialMechSLang_apply]
  rw [show 2 * RangePrivacy.rangeDistance q q' =
        RangePrivacy.rangeDistance q q' + RangePrivacy.rangeDistance q q' from by ring,
      pow_add]
  set A  := ENNReal.ofReal (exp (- ((gap q  r * ε₁ : ℕ) : NNReal) / ε₂))
  set A' := ENNReal.ofReal (exp (- ((gap q' r * ε₁ : ℕ) : NNReal) / ε₂))
  set Z  := ∑' i : Fin n.succ, ENNReal.ofReal (exp (- ((gap q  i * ε₁ : ℕ) : NNReal) / ε₂))
  set Z' := ∑' i : Fin n.succ, ENNReal.ofReal (exp (- ((gap q' i * ε₁ : ℕ) : NNReal) / ε₂))
  set α  := privacyBase ε₁ ε₂ ^ RangePrivacy.rangeDistance q q'
  have h_num : α * A  ≤ A' := exactCoin_contraction q q' r ε₁ ε₂
  have h_den : α * Z' ≤ Z  := exactCoin_sum_contraction q q' ε₁ ε₂
  have h_cross : α * α * A * Z' ≤ A' * Z :=
    calc α * α * A * Z' = (α * A) * (α * Z') := by ring
      _ ≤ A' * Z := mul_le_mul' h_num h_den
  -- Z and Z' are positive and finite (finite sums of positive finite terms).
  have hZ_pos : 0 < Z := lt_of_lt_of_le (by positivity) (ENNReal.le_tsum 0)
  have hZ_fin : Z ≠ ⊤ := by
    have heq : Z = ∑ i : Fin n.succ,
        ENNReal.ofReal (Real.exp (- ((gap q i * ε₁ : ℕ) : NNReal) / ε₂)) := tsum_fintype _
    simp [heq, ENNReal.ofReal_ne_top]
  have hZ'_pos : 0 < Z' := lt_of_lt_of_le (by positivity) (ENNReal.le_tsum 0)
  have hZ'_fin : Z' ≠ ⊤ := by
    have heq : Z' = ∑ i : Fin n.succ,
        ENNReal.ofReal (Real.exp (- ((gap q' i * ε₁ : ℕ) : NNReal) / ε₂)) := tsum_fintype _
    simp [heq, ENNReal.ofReal_ne_top]
  -- α² · (A/Z) ≤ A'/Z' from h_cross: α²·A·Z' ≤ A'·Z.
  -- Proof: α²A/Z = α²AZ'/(ZZ') ≤ A'Z/(ZZ') = A'/Z' by div_le_div_right.
  rw [mul_div_assoc']
  -- Convert /  to * ⁻¹, expand (a*b)⁻¹ = a⁻¹*b⁻¹, rearrange, cancel.
  have eq1 : α * α * A * Z' / (Z * Z') = α * α * A / Z := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hZ_pos.ne') (Or.inl hZ_fin)]
    calc α * α * A * Z' * (Z⁻¹ * Z'⁻¹)
        = α * α * A * Z' * Z'⁻¹ * Z⁻¹ := by rw [mul_comm Z⁻¹ Z'⁻¹, ← mul_assoc]
      _ = α * α * A * (Z' * Z'⁻¹) * Z⁻¹ := by rw [mul_assoc (α * α * A)]
      _ = α * α * A * Z⁻¹ := by rw [ENNReal.mul_inv_cancel hZ'_pos.ne' hZ'_fin, mul_one]
      _ = α * α * A / Z := (div_eq_mul_inv _ _).symm
  have eq2 : A' * Z / (Z * Z') = A' / Z' := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hZ_pos.ne') (Or.inl hZ_fin)]
    calc A' * Z * (Z⁻¹ * Z'⁻¹)
        = A' * Z * Z⁻¹ * Z'⁻¹ := by rw [← mul_assoc]
      _ = A' * (Z * Z⁻¹) * Z'⁻¹ := by rw [mul_assoc A']
      _ = A' * Z'⁻¹ := by rw [ENNReal.mul_inv_cancel hZ_pos.ne' hZ_fin, mul_one]
      _ = A' / Z' := (div_eq_mul_inv _ _).symm
  rw [← eq1, ← eq2]
  exact ENNReal.div_le_div_right h_cross _

end ExponentialMechanism
end SLang
