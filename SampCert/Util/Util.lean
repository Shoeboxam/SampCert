/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Util

This file contains general SampCert utility lemmas
-/

open Function Nat Set BigOperators Finset

theorem in_subset_satisfies (P : ℕ → Prop) (x : { x // P x }) : P x := by
  cases x
  simp
  trivial

/--
Simplify a sum over a step function
-/
@[simp]
theorem sum_simple (bound : ℕ) (k : ENNReal) :
 (∑' (a : ℕ), if a < bound then k else 0) = k * bound := by
  rw [tsum_eq_sum (s := Finset.range bound)]
  · calc
      Finset.sum (Finset.range bound) (fun x => if x < bound then k else 0)
        = Finset.sum (Finset.range bound) (fun _ => k) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact if_pos (Finset.mem_range.mp hx)
      _ = bound • k := by simp
      _ = k * bound := by rw [nsmul_eq_mul, mul_comm]
  · intro x hx
    rw [Finset.mem_range] at hx
    exact if_neg hx


/--
Simplify guarded series when series indices satisfy the guard
-/
theorem tsum_simpl_ite_left (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i}), if cond x then f x else g x)
    = (∑' (x : { i : T | cond i}), f x) := by
  apply tsum_congr
  intro b
  split
  · simp
  · rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = true := by exact P
    simp [A] at h

/--
Simplify guarded series when series indices never satisfy the guard
-/
theorem tsum_simpl_ite_right (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | ¬ cond i}), if cond x then f x else g x)
    = ((∑' (x : { i : T | ¬ cond i}), g x)) := by
  apply tsum_congr
  intro b
  split
  · rename_i h
    cases b
    rename_i b P
    simp at *
    have A : ¬ cond b = true := by exact P
    simp [A] at h
  · simp

/--
Partition series indices based on conditional guard
-/
theorem tsum_split_ite (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i then f i else g i)
    = (∑' (i : { i : T | cond i}), f i) + (∑' (i : { i : T | ¬ cond i}), g i) := by
  rw [_root_.tsum_subtype, _root_.tsum_subtype, ← ENNReal.tsum_add]
  apply tsum_congr
  intro i
  by_cases h : cond i
  · simp [h]
  · simp [h]

/--
Simplify guarded series based on index type
-/
theorem tsum_simpl_ite_left' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i}), if cond x = false then f x else g x)
    = (∑' (x : { i : T | cond i}), g x) := by
  apply tsum_congr
  intro b
  split
  · rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = true := by exact P
    simp [A] at h
  · simp

/--
Simplify guarded series based on index type
-/
theorem tsum_simpl_ite_right' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (x : { i : T | cond i = false}), if cond x = false then f x else g x)
    = ((∑' (x : { i : T | cond i = false}), f x)) := by
  apply tsum_congr
  intro b
  split
  · simp
  · rename_i h
    cases b
    rename_i b P
    simp at *
    have A : cond b = false := by exact P
    simp [A] at h

/--
Partition series indices based on negation of conditional guard
-/
theorem tsum_split_ite' (cond : T → Bool) (f g : T → ENNReal) :
  (∑' (i : T), if cond i = false then f i else g i)
    = (∑' (i : { i : T | cond i = false}), f i) + (∑' (i : { i : T | cond i = true}), g i) := by
  rw [_root_.tsum_subtype, _root_.tsum_subtype, ← ENNReal.tsum_add]
  apply tsum_congr
  intro i
  by_cases h : cond i = false
  · simp [h]
  · have h' : cond i = true := by cases hcond : cond i <;> simp_all
    simp [h]

/--
Add vacuous guard to series based on index type
-/
theorem tsum_split_coe_right (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = true}), f i)
    = (∑' (i : T), if cond i = true then f i else 0) := by
  rw [tsum_split_ite]
  simp

/--
Add vacuous guard to series based on index type
-/
theorem tsum_split_coe_left (cond : T → Bool) (f : T → ENNReal) :
  (∑' (i : { i : T | cond i = false}), f i)
    = (∑' (i : T), if cond i = false then f i else 0) := by
  rw [tsum_split_ite']
  simp

/--
Bound a (nonnegative) guarded series above by an unguarded one
-/
theorem tsum_split_less (cond : ℕ → Bool) (f : ℕ → ENNReal) :
  (∑' i : ℕ, if cond i then f i else 0) ≤ ∑' i : ℕ, f i := by
  exact ENNReal.tsum_le_tsum (fun i => by by_cases h : cond i <;> simp [h])

/--
Remove leading zero from series
-/
theorem tsum_shift_1 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else f (n-1)) =
    ∑' n : ℕ, f n := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  let S : ℕ → ENNReal := fun i => Finset.sum (Finset.range i) (fun a => if a = 0 then 0 else f (a - 1))
  have A : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [S]
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 1]
  rw [iSup_congr]
  intro i
  induction i with
  | zero =>
      dsimp [S]
      simp
  | succ i IH =>
      dsimp [S]
      dsimp [S] at IH
      calc
        Finset.sum (Finset.range (i + 2)) (fun a => if a = 0 then 0 else f (a - 1))
          = Finset.sum (Finset.range (i + 1)) (fun a => if a = 0 then 0 else f (a - 1)) + f i := by
              rw [sum_range_succ]
              simp
        _ = Finset.sum (Finset.range i) (fun a => f a) + f i := by rw [IH]
        _ = Finset.sum (Finset.range (i + 1)) (fun a => f a) := by rw [sum_range_succ]

/--
Remove leading zero from series
-/
theorem tsum_shift'_1 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else f n) =
    ∑' n : ℕ, f (n + 1) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  let S : ℕ → ENNReal := fun i => Finset.sum (Finset.range i) (fun a => if a = 0 then 0 else f a)
  have A : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [S]
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 1]
  rw [iSup_congr]
  intro i
  induction i with
  | zero =>
      dsimp [S]
      simp
  | succ i IH =>
      dsimp [S]
      dsimp [S] at IH
      calc
        Finset.sum (Finset.range (i + 2)) (fun a => if a = 0 then 0 else f a)
          = Finset.sum (Finset.range (i + 1)) (fun a => if a = 0 then 0 else f a) + f (i + 1) := by
              rw [sum_range_succ]
              simp
        _ = Finset.sum (Finset.range i) (fun a => f (a + 1)) + f (i + 1) := by rw [IH]
        _ = Finset.sum (Finset.range (i + 1)) (fun a => f (a + 1)) := by rw [sum_range_succ]

/--
Remove two leading zeroes from series
-/
theorem tsum_shift'_2 (f : ℕ → ENNReal) :
  (∑' n : ℕ, if n = 0 then 0 else if n = 1 then 0 else f n) =
    ∑' n : ℕ, f (n + 2) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  rw [ENNReal.tsum_eq_iSup_nat]
  let S : ℕ → ENNReal := fun i => Finset.sum (Finset.range i) (fun a => if a = 0 then 0 else if a = 1 then 0 else f a)
  have A : Monotone S := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [S]
    rw [sum_range_succ]
    simp
  rw [← Monotone.iSup_nat_add A 2]
  rw [iSup_congr]
  intro i
  induction i with
  | zero =>
      dsimp [S]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp
  | succ i IH =>
      dsimp [S]
      dsimp [S] at IH
      calc
        Finset.sum (Finset.range (i + 3)) (fun a => if a = 0 then 0 else if a = 1 then 0 else f a)
          = Finset.sum (Finset.range (i + 2)) (fun a => if a = 0 then 0 else if a = 1 then 0 else f a) + f (i + 2) := by
              rw [sum_range_succ]
              simp
        _ = Finset.sum (Finset.range i) (fun a => f (a + 2)) + f (i + 2) := by rw [IH]
        _ = Finset.sum (Finset.range (i + 1)) (fun a => f (a + 2)) := by rw [sum_range_succ]

/--
Specialize Euclidean division from ℤ to ℕ
-/
lemma euclidean_division (n : ℕ) {D : ℕ} (HD : 0 < D) :
  ∃ q r : ℕ, (r < D) ∧ n = r + D * q := by
  exists (n / D)
  exists (n % D)
  apply And.intro
  · exact mod_lt n HD
  · apply ((@Nat.cast_inj ℤ).mp)
    simp
    conv =>
      lhs
      rw [<- EuclideanDomain.mod_add_div (n : ℤ) (D : ℤ)]

/--
Euclidiean division is unique
-/
lemma euclidean_division_uniquness (r1 r2 q1 q2 : ℕ) {D : ℕ} (HD : 0 < D) (Hr1 : r1 < D) (Hr2 : r2 < D) :
    r1 + D * q1 = r2 + D * q2 <-> (r1 = r2 ∧ q1 = q2) := by
  apply Iff.intro
  · intro H
    cases (Classical.em (r1 = r2))
    · aesop
    cases (Classical.em (q1 = q2))
    · aesop
    rename_i Hne1 Hne2
    exfalso

    have Contra1 (W X Y Z : ℕ) (HY : Y < D) (HK : W < X) : (Y + D * W < Z + D * X) := by
      suffices (D * W < D * X) by
        have A : (1 + W ≤ X) := by exact one_add_le_iff.mpr HK
        have _ : (D * (1 + W) ≤ D * X) := by exact Nat.mul_le_mul_left D A
        have _ : (D + D * W ≤ D * X) := by linarith
        have _ : (Y + D * W < D * X) := by linarith
        have _ : (Y + D * W < Z + D * X) := by linarith
        assumption
      exact Nat.mul_lt_mul_of_pos_left HK HD

    rcases (lt_trichotomy q1 q2) with HK' | ⟨ HK' | HK' ⟩
    · exact (LT.lt.ne (Contra1 q1 q2 r1 r2 Hr1 HK') H)
    · exact Hne2 HK'
    · apply (LT.lt.ne (Contra1 q2 q1 r2 r1 Hr2 HK') (Eq.symm H))

  · intro ⟨ _, _ ⟩
    simp_all


lemma nat_div_eq_le_lt_iff {a b c : ℕ} (Hc : 0 < c) : a = b / c <-> (a * c ≤ b ∧ b < (a +  1) * c) := by
  apply Iff.intro
  · intro H
    apply And.intro
    · apply (Nat.le_div_iff_mul_le Hc).mp
      exact Nat.le_of_eq H
    · apply (Nat.div_lt_iff_lt_mul Hc).mp
      apply Nat.lt_succ_iff.mpr
      exact Nat.le_of_eq (id (Eq.symm H))
  · intro ⟨ H1, H2 ⟩
    apply LE.le.antisymm
    · apply (Nat.le_div_iff_mul_le Hc).mpr
      apply H1
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul Hc).2 H2)
