/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Shift Util

This file contains lemmas about invariance of sums under integer shifts.
-/

open Summable

/--
A series is right-ℕ-shift-invariant provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift₁ (f : ℤ → ℝ) (μ : ℕ)
  (_h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (x + μ))
  (_h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) + μ))
  :
  (∑' x : ℤ, f x) = ∑' x : ℤ, f (x + μ) := by
  simpa using ((Equiv.addRight (μ : ℤ)).tsum_eq (f := f)).symm


/--
A series is left-ℕ-shift-invariant provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift₂ (f : ℤ → ℝ) (μ : ℕ)
  (_h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (x - μ))
  (_h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) - μ)) :
  ∑' x : ℤ, f (x - μ) = (∑' x : ℤ, f x) := by
  simpa [sub_eq_add_neg] using ((Equiv.subRight (μ : ℤ)).tsum_eq (f := f))

/--
A series is invariant under integer shifts provided its shifted positive and negative parts are summable.
-/
theorem tsum_shift (f : ℤ → ℝ) (μ : ℤ)
  (h₀ : ∀ μ : ℤ, Summable fun x : ℤ => f (x + μ)) :
  ∑' x : ℤ, f (x + μ) = (∑' x : ℤ, f x) := by
  have h : ∀ μ : ℤ, Summable fun x : ℕ => f (x + μ) := by
    intro μ
    have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun x => f (x + μ))
    replace A := A.1 (h₀ μ)
    cases A
    rename_i X Y
    exact X
  have h' : ∀ μ : ℤ, Summable fun x : ℕ => f (-(x + 1) + μ) := by
    intro μ
    have A := @summable_int_iff_summable_nat_and_neg_add_zero ℝ _ _ _ _ (fun x => f (x + μ))
    replace A := A.1 (h₀ μ)
    cases A
    rename_i X Y
    exact Y
  have h1 : ∀ μ : ℕ, Summable fun x : ℕ => f (x + μ) := by
    intro μ
    apply h
  have h2 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) + μ) := by
    intro μ
    apply h'
  have h3 : ∀ μ : ℕ, Summable fun x : ℕ => f (x - μ) := by
    intro μ
    apply h
  have h4 : ∀ μ : ℕ, Summable fun x : ℕ => f (-(x + 1) - μ) := by
    intro μ
    apply h'
  cases μ
  · rename_i μ
    rw [tsum_shift₁ f μ h1 h2]
    simp
  · rename_i μ
    rw [← tsum_shift₂ f (μ + 1) h3 h4]
    apply tsum_congr
    intro b
    congr
