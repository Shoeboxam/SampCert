/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import Mathlib.Probability.Distributions.Uniform
import SampCert.Samplers.Bernoulli.Code

/-!
# Bernoulli Sampler Properties

This file proves normalization and evaluation properties of the ``BernoulliSample`` sampler.
-/

noncomputable section

open PMF Finset BigOperators Nat

namespace SLang

/--
Bernoulli sampler evaluates to ``true`` with probability ``num/den``.
-/
@[simp]
theorem BernoulliSample_apply_true (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample num den wf true = num / den := by
  unfold BernoulliSample
  simp
  have hsum :
      (∑' (a : ℕ), if a < num then UniformSample den a else 0) =
        Finset.sum (Finset.range num) (fun a => UniformSample den a) := by
    calc
      (∑' (a : ℕ), if a < num then UniformSample den a else 0)
        = Finset.sum (Finset.range num) (fun a => if a < num then UniformSample den a else 0) := by
            exact tsum_eq_sum (s := Finset.range num) (by
              intro a ha
              have hlt : ¬ a < num := by simpa [Finset.mem_range] using ha
              simp [hlt])
      _ = Finset.sum (Finset.range num) (fun a => UniformSample den a) := by
            apply Finset.sum_congr rfl
            intro a ha
            simp [Finset.mem_range.mp ha]
  rw [hsum, UniformSample_support_Sum _ _ wf]

/--
Bernoulli sampler evaluates to ``false`` with probability ``num/den``.
-/
@[simp]
theorem BernoulliSample_apply_false (num : Nat) (den : PNat) (wf : num ≤ den) :
  BernoulliSample num den wf false = 1 - (num / den) := by
  unfold BernoulliSample
  simp
  have htrue :
      (∑' (a : ℕ), if a < num then UniformSample den a else 0) = num / den := by
    have hsum :
        (∑' (a : ℕ), if a < num then UniformSample den a else 0) =
          Finset.sum (Finset.range num) (fun a => UniformSample den a) := by
      calc
        (∑' (a : ℕ), if a < num then UniformSample den a else 0)
          = Finset.sum (Finset.range num) (fun a => if a < num then UniformSample den a else 0) := by
              exact tsum_eq_sum (s := Finset.range num) (by
                intro a ha
                have hlt : ¬ a < num := by simpa [Finset.mem_range] using ha
                simp [hlt])
        _ = Finset.sum (Finset.range num) (fun a => UniformSample den a) := by
              apply Finset.sum_congr rfl
              intro a ha
              simp [Finset.mem_range.mp ha]
    rw [hsum, UniformSample_support_Sum _ _ wf]
  have hsplit := tsum_split_ite' (fun a => decide (num ≤ a)) (fun a => UniformSample den a)
    (fun a => UniformSample den a)
  rw [tsum_split_coe_right, tsum_split_coe_left] at hsplit
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le] at hsplit
  have hnorm : (∑' (i : ℕ), if i < num then UniformSample den i else UniformSample den i) = 1 := by
    simp [UniformSample_normalizes den]
  rw [hnorm, htrue] at hsplit
  apply ENNReal.eq_sub_of_add_eq
  · have B : ↑num / ↑↑den < (⊤ : ENNReal) := by
      apply ENNReal.div_lt_top
      · simp
      · simp
    exact lt_top_iff_ne_top.mp B
  · simpa [add_comm] using hsplit.symm

/--
Total mass of the Bernoulli sampler is 1.
-/
@[simp]
theorem BernoulliSample_normalizes (num : Nat) (den : PNat) (wf : num ≤ den) :
  ∑' b : Bool, BernoulliSample num den wf b = 1 := by
  rw [tsum_bool, BernoulliSample_apply_true, BernoulliSample_apply_false]
  have hp_le : ((num : ENNReal) / (den : ENNReal)) ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul]
    · simpa using (show (num : ENNReal) ≤ den by exact_mod_cast wf)
    · simp
    · simp
  simpa using (tsub_add_cancel_of_le hp_le)

/--
Total mass of the Bernoulli sampler is 1.
-/
theorem BernoulliSample_normalizes' (num : Nat) (den : PNat) (wf : num ≤ den) :
  ∑ b : Bool, BernoulliSample num den wf b = 1 := by
  simpa [tsum_bool] using BernoulliSample_normalizes num den wf

/--
Closed form for evaulation of Bernoulli distribution in terms of its paramater ``num/den``.
-/
@[simp]
theorem BernoulliSample_apply (num : Nat) (den : PNat) (wf : num ≤ den) (b : Bool) :
  BernoulliSample num den wf b = if b then ((num : ENNReal) / (den : ENNReal)) else ((1 : ENNReal) - ((num : ENNReal) / (den : ENNReal))) := by
  cases b
  · simp
  · simp

/--
``SLang`` Bernoulli program is a proper distribution.
-/
def BernoulliSamplePMF (num : Nat) (den : PNat) (wf : num ≤ den) : PMF Bool := PMF.ofFintype (BernoulliSample num den wf) (BernoulliSample_normalizes' num den wf)

namespace SLang
