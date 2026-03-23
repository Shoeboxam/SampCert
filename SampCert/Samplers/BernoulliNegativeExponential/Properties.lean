/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform.Basic
import SampCert.Samplers.Bernoulli.Basic
import SampCert.Samplers.BernoulliNegativeExponential.Code
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# ``BernoulliNegExpSample`` Properties

This file proves evaluation and normalization for ``BernoulliNegExpSample``.
-/

noncomputable section

open PMF Nat Finset
open scoped BigOperators

namespace SLang

theorem ite_eq_ite_propDecidable {α : Sort _} (p : Prop) (d : Decidable p) (t e : α) :
    @ite α p d t e = @ite α p (Classical.propDecidable p) t e := by
  by_cases h : p <;> simp [h]

@[simp]
theorem BernoulliExpNegSampleUnitAux_zero (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) 0 st st' = 0 := by
  simp [probWhileCut]

@[simp]
theorem BernoulliExpNegSampleUnitAux_returns_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (true, r) = 0 := by
  revert st r
  induction fuel
  · simp [probWhileCut]
  · rename_i fuel IH
    intro st r
    simp [probWhileCut, probWhileFunctional]
    unfold probBind
    unfold probPure
    simp [ite_apply]
    split
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      have hIH : ∀ a, probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf)
          fuel a (true, r) = 0 := by
        intro a
        exact IH a r
      simp_rw [hIH]
      simp
    · rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_ite_simpl (x r : ℕ+) (k : ENNReal) :
  (if x = r + 1 then 0 else if x = r + 1 then k else 0) = 0 := by
  by_cases h : x = r + 1 <;> simp [h]

@[simp]
theorem tsum_BernoulliExpNegSampleUnitLoop_two_terms (r : ℕ+) (α β : ENNReal)
    (f : Bool × ℕ+ → ENNReal) :
    (∑' a : Bool × ℕ+,
        ((if a = (true, r) then α else 0) + if a = (false, r) then β else 0) * f a)
      = α * f (true, r) + β * f (false, r) := by
  have htf : ((true, r) : Bool × ℕ+) ≠ (false, r) := by simp
  have hrewrite :
      (fun a : Bool × ℕ+ =>
        ((if a = (true, r) then α else 0) + if a = (false, r) then β else 0) * f a)
        = fun a : Bool × ℕ+ => if a = (true, r) then α * f a else if a = (false, r) then β * f a else 0 := by
    funext a
    by_cases h1 : a = (true, r) <;> by_cases h2 : a = (false, r) <;> simp [h1, h2, htf] at *
  rw [hrewrite]
  rw [ENNReal.tsum_eq_add_tsum_ite (true, r)]
  simp
  rw [ENNReal.tsum_eq_add_tsum_ite (false, r)]
  simp
  let g : Bool × ℕ+ → ENNReal := fun x =>
    if x = (false, r) then 0
    else if x = (true, r) then 0 else if x = (true, r) then α * f x else if x = (false, r) then β * f x else 0
  have hzero :
      (∑' x : Bool × ℕ+, g x) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    dsimp [g]
    by_cases h1 : x = (true, r) <;> by_cases h2 : x = (false, r) <;> simp [h1, h2, htf] at *
  have hhead :
      (if (false, r) = (true, r) then 0
        else if (false, r) = (true, r) then α * f (false, r)
        else if (false, r) = (false, r) then β * f (false, r) else 0) = β * f (false, r) := by
    simp
  have hsum :
      α * f (true, r) +
        ((if (false, r) = (true, r) then 0
          else if (false, r) = (true, r) then α * f (false, r)
          else if (false, r) = (false, r) then β * f (false, r) else 0)
          + ∑' (x : Bool × ℕ+), g x)
        = α * f (true, r) + β * f (false, r) := by
    rw [hhead, hzero]
    simp
  simpa [g, ite_eq_ite_propDecidable] using hsum


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (true, r + 1) st
    + (1 - (num / (r * den))) * probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st := by
  cases st
  rename_i b' r'
  simpa [probWhileCut, probWhileFunctional, BernoulliExpNegSampleUnitLoop, add_comm] using
    (tsum_BernoulliExpNegSampleUnitLoop_two_terms (r := r + 1)
      (α := (num : ENNReal) / (r * den))
      (β := 1 - (num : ENNReal) / (r * den))
      (f := fun a => probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel a (b', r')))


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (false, r) st =
  if st = (false,r) then 1 else 0 := by
  cases st
  simp [probWhileCut, probWhileFunctional]

@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_counter (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  · simp
  · rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    · simp
      exact Ne.symm (h1 rfl)
    · simp [BernoulliExpNegSampleUnitAux_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact eq_or_lt_of_le h2
        cases OR
        · rename_i h
          subst h
          exact _root_.ne_of_gt le.refl
        · rename_i h
          exact _root_.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by
        simp
      rw [IH _ A]
      rw [IH _ B]
      simp
      exact le.step h2
      exact le.step h2

-- The following two functions are useful to keep the dependent definition of PNat under control
-- Otherwise, the terms become large and unreadable

def plus_one (k : ℕ) : ℕ+ := ⟨ k + (1 : ℕ+) , Nat.add_pos_right k le.refl ⟩

def plus_two (k fuel : ℕ) : ℕ+ := ⟨ fuel + k + 2 , Nat.add_pos_right (fuel + k) (le.step le.refl) ⟩

@[simp]
theorem plus_one_p1 (k e : ℕ) :
  plus_one k + e = plus_one (k + e) := by
  simp [plus_one]
  conv =>
    right
    rw [add_assoc]
    right
    rw [add_comm]
  conv =>
    right
    rw [← add_assoc]

theorem plus_one_prop (k : ℕ) :
  plus_one k = k + 1 := by
  simp [plus_one]

theorem plus_two_zero_prop (k : ℕ) :
  plus_two k 0 = k + 2 := by
  simp [plus_two]

theorem nm2p2 (n : ℕ) (h : n > 1) :
  n - 2 + 2 = n := by
  exact Nat.sub_add_cancel h

-- Warning! BernoulliExpNegSampleUnitAux has a transition phase
-- This min is suspicious: (min (fuel + 2) (fuel + k + 1) - 2)
@[simp]
theorem BernoulliExpNegSampleUnitAux_progress (num : ℕ) (den : ℕ+) (fuel k : ℕ) (wf : num ≤ den) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel ) = (Finset.prod (Finset.range fuel) (fun i => (num : ENNReal) / ((k + 1 + i) * den))) * (1 - ((num : ENNReal) / ((fuel + k + 1) * den))) := by
  revert k
  induction fuel
  · intro k
    simp
    split
    · rename_i h
      rw [plus_one_prop]
      simp
    · rename_i h
      have A : ¬ k + 2 = k + 2 := by
        conv =>
          right
          congr
          · rw [← plus_two_zero_prop]
          · change k + (1 + 1)
            rw [← add_assoc]
            rw [← plus_one_prop]
        refine (Function.Injective.ne_iff ?hf).mpr h
        exact PNat.coe_injective
      contradiction
  · rename_i fuel IH
    intro k
    rw [BernoulliExpNegSampleUnitAux_succ_true]
    rw [BernoulliExpNegSampleUnitAux_succ_false]
    have IH' := IH (k + 1)
    clear IH
    have A : plus_one (k + 1) = plus_one k + 1 := rfl
    have B : plus_two (k + 1) fuel = plus_two k (succ fuel) := by
      simp [plus_two]
      have X : fuel + (k + 1) + 2 = succ fuel + k + 2 := by
        conv =>
          left
          left
          right
          rw [add_comm]
        rw [← add_assoc]
      conv =>
        left
        left
        rw [X]
    rw [← A]
    rw [← B]
    rw [IH']
    have C : ¬ plus_two (k + 1) fuel = plus_one (k + 1) := by
      by_contra h
      simp [plus_one, plus_two] at h
      cases h
    simp [C]
    have E : fuel + (k + (1 : ENNReal)) + (1 : ENNReal) = ↑fuel + 1 + ↑k + 1 := by -- duplicate later on
      conv =>
        left
        left
        right
        rw [add_comm]
      rw [← add_assoc]
    rw [E]
    clear IH' A B C E
    simp [prod_range_succ']
    rw [plus_one_prop]
    conv =>
      right
      left
      rw [mul_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      right
      rw [add_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      rw [← add_assoc]
    simp
    rw [mul_assoc]

theorem adhoc (n : ℕ) (h : n > 1) :
  n - 2 + 1 = n - 1 := by
  rw [← tsub_tsub_assoc]
  · exact h
  · exact le.step le.refl

theorem adhoc' (n : ℕ) (h : n > 1) :
  (n : ENNReal) - 2 + 1 = (n : ENNReal) - 1 := by
  have C := @congrArg ℕ ENNReal (n - 2 + 1) (n - 1) Nat.cast  (adhoc n h)
  simp at C
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_progress' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1 ) (false, ⟨ n , lt_of_succ_lt h ⟩ ) = (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  have prog := BernoulliExpNegSampleUnitAux_progress num den (n - 2) 0 wf
  have A := nm2p2 n h
  rw [A] at prog
  have B : plus_two 0 (n - 2) = ⟨ n , lt_of_succ_lt h ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [A]
  rw [B] at prog
  simp [plus_one] at prog
  have C := adhoc' n h
  rw [C] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation (num : ℕ) (den : ℕ+) (fuel fuel' k : ℕ) (wf : num ≤ den) (h1 : fuel ≥ fuel') :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (1 + fuel + 2) (true, plus_one k ) (false, plus_two k fuel')
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel') := by
  revert fuel' k
  induction fuel
  · intro fuel' k h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [BernoulliExpNegSampleUnitAux_succ_true]
    -- rewrites of plus_* properties do not work because the type is wrong
    have B : ¬ plus_two k 0 = plus_one k + 1 + 1 := by
      simp [plus_two, plus_one]
      by_contra h
      cases h -- similar proof in BernoulliExpNegSampleUnitAux_progress
    simp [B]
  · rename_i fuel IH
    intro fuel' k h1
    conv =>
      congr
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
      · rw [BernoulliExpNegSampleUnitAux_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (k + 1) Pre
    clear IH
    cases fuel'
    · rw [BernoulliExpNegSampleUnitAux_succ_false]
      rw [BernoulliExpNegSampleUnitAux_succ_false]
      have C : plus_two k Nat.zero = plus_one k + 1 := by   -- Useful for cleanup
        simp [plus_two, plus_one]
        rfl
      rw [C]
      simp
    · rename_i fuel'
      have C : succ fuel' - 1 = fuel' := by exact rfl
      rw [C] at IH'
      have D : plus_two (k + 1) fuel' = plus_two k (succ fuel') := by -- Important example for cleanup
        simp [plus_two]
        have X : fuel' + (k + 1) + 2 = succ fuel' + k + 2 := by
          conv =>
            left
            left
            right
            rw [add_comm]
          rw [← add_assoc]
        conv =>
          left
          left
          rw [X]
      rw [D] at IH'
      have E : plus_one (k + 1) = plus_one k + 1 := by  -- Useful for cleanup
        simp [plus_one]
        rfl
      rw [E] at IH'
      rw [IH']
      exact rfl

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation' (num : ℕ) (den : ℕ+) (n m : ℕ) (wf : num ≤ den) (h1 : m > 1) (h2 : n ≥ m) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (n + 1) (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩ )
    = probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩) := by
  have X : n - 2 ≥ m - 2 := by exact Nat.sub_le_sub_right h2 2
  have prog := BernoulliExpNegSampleUnitAux_preservation num den (n - 2) (m - 2) 0 wf X
  have A : 1 + (n - 2) + 2 = n + 1 := by
    rw [add_assoc]
    rw [add_comm]
    rw [_root_.add_left_inj]
    rw [nm2p2 n (Nat.lt_of_lt_of_le h1 h2)]
  have B := nm2p2 n (Nat.lt_of_lt_of_le h1 h2)
  have C : plus_one 0 = 1 := by
    simp [plus_one]
  have D : plus_two 0 (m - 2) = ⟨ m, zero_lt_of_lt h1 ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [nm2p2 m h1]
  rw [A, B, C, D] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_characterization (num : ℕ) (den : ℕ+) (n extra : ℕ) (wf : num ≤ den) (h : n > 1) :
  probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (extra + n) (true, 1) (false, ⟨ n, by exact zero_lt_of_lt h ⟩)
    =  (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  revert n
  induction extra
  · simp
    intro n h
    apply BernoulliExpNegSampleUnitAux_progress' num den n wf h
  · rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    rw [← BernoulliExpNegSampleUnitAux_preservation'] at IH'
    · have B : extra + n + 1 = succ extra + n := by
        clear IH'
        clear IH'
        conv =>
          left
          rw [add_comm]
          rw [← add_assoc]
        rw [add_left_inj]
        exact one_add extra
      rw [← B]
      trivial
    · trivial
    · exact Nat.le_add_left n extra

theorem BernoulliExpNegSampleUnitAux_sup (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  ⨆ i, probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) i (true, 1) (false, n)
    = if n = 1 then 0 else (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  apply iSup_eq_of_tendsto
  · apply probWhileCut_monotonic
  · rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat n)]
    split
    · rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [BernoulliExpNegSampleUnitAux_monotone_counter]
    · rename_i h
      have h' : n > 1 := by
        by_contra h0
        simp at *
        subst h0
        contradiction
      have hconst :
          (fun E : ℕ => probWhileCut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf)
            (E + n) (true, 1) (false, n))
            = fun _ => (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) *
                (1 - ((num : ENNReal) / ((n - 1) * den))) := by
        funext E
        simpa using (BernoulliExpNegSampleUnitAux_characterization num den n E wf h')
      rw [hconst]
      rw [tendsto_const_nhds_iff]

@[simp]
theorem BernoulliExpNegSampleUnitAux_at_zero (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 0 = 0 := by
  simp only [BernoulliExpNegSampleUnitAux, Bind.bind, Pure.pure, SLang.bind_apply, probWhile,
    SLang.pure_apply, ENNReal.tsum_eq_zero, _root_.mul_eq_zero, ENNReal.iSup_eq_zero, Prod.forall,
    Bool.forall_bool, BernoulliExpNegSampleUnitAux_returns_false, forall_const, true_or, and_true]
  intro b
  right
  split
  · rename_i h
    cases b
    rename_i b pb
    subst h
    contradiction
  simp only

theorem if_simpl' (num : ℕ) (den : ℕ+) (x n : ℕ+) :
  (if x = n then 0 else if n = x then if x = 1 then 0 else
    ((Finset.prod (Finset.range (↑x - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
      (1 - ↑num / ((↑↑x - 1) * ↑↑den))) else 0) = 0 := by
  by_cases hxn : x = n
  · simp [hxn]
  · by_cases hnx : n = x
    · subst hnx
      contradiction
    · simp [hxn, hnx]

theorem BernoulliExpNegSampleUnitAux_apply (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
    if n = 1 then 0 else (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  simp [BernoulliExpNegSampleUnitAux]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [probWhile]
  simp [BernoulliExpNegSampleUnitAux_sup]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  let g : ℕ+ → ENNReal := fun x =>
    if x = n then 0 else if n = x then if x = 1 then 0 else
      (Finset.prod (Finset.range (↑x - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
        (1 - ↑num / ((↑↑x - 1) * ↑↑den)) else 0
  have hzero :
      (∑' x : ℕ+, g x) = 0 := by
    rw [ENNReal.tsum_eq_zero]
    intro x
    dsimp [g]
    exact if_simpl' num den x n
  have hz := congrArg (fun t =>
    (if n = 1 then 0 else
      (Finset.prod (Finset.range (↑n - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
        (1 - ↑num / ((↑↑n - 1) * ↑↑den))) + t) hzero
  have hhead :
      (if n = n then
        if n = 1 then 0 else
          (Finset.prod (Finset.range (↑n - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
            (1 - ↑num / ((↑↑n - 1) * ↑↑den))
      else 0)
        = if n = 1 then 0 else
            (Finset.prod (Finset.range (↑n - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
              (1 - ↑num / ((↑↑n - 1) * ↑↑den)) := by
    simp
  have hsum :
      (if n = n then
        if n = 1 then 0 else
          (Finset.prod (Finset.range (↑n - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
            (1 - ↑num / ((↑↑n - 1) * ↑↑den))
      else 0) + ∑' (x : ℕ+), g x
      = if n = 1 then 0 else
          (Finset.prod (Finset.range (↑n - 2)) (fun i => ↑num / (((1 : ENNReal) + ↑i) * ↑↑den))) *
            (1 - ↑num / ((↑↑n - 1) * ↑↑den)) := by
    rw [hhead, hzero]
    simp
  simpa [g, ite_eq_ite_propDecidable] using hsum


@[simp]
theorem BernoulliExpNegSampleUnitAux_at_one (num : ℕ) (den : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) 1 = 0 := by
  change (BernoulliExpNegSampleUnitAux num den wf) (1 : ℕ+) = 0
  rw [BernoulliExpNegSampleUnitAux_apply]
  simp

theorem gamma_extract' (num : Nat) (den : PNat) (x : ENNReal) (h1 : x ≠ 0) (h2 : x ≠ ⊤) :
  ((num : ENNReal) / (x * den)) = ((num : ENNReal) / (den : ENNReal)) * x⁻¹ := by
  rw [division_def, division_def, ENNReal.mul_inv]
  · ac_rfl
  · exact Or.inl h1
  · exact Or.inl h2


theorem gamma_extract (num : Nat) (den : PNat) (n : ℕ) (h : n > 1) :
  (Finset.prod (Finset.range (n - 2)) (fun i => (num : ENNReal) / ((1 + i) * den))) =
  (((num : ENNReal) / (den : ENNReal))^(n - 2) * ((factorial (n - 2)) : ENNReal)⁻¹) := by
  have X : ∀ i : ℕ, (1 : ENNReal) + i ≠ 0 := by
    intro i
    simp
  have Y : ∀ i : ℕ, (1 : ENNReal) + i ≠ ⊤ := by
    intro i
    simp
  conv =>
    left
    right
    intro i
    rw [gamma_extract' _ _ _ (X i) (Y i)]
  rw [prod_mul_distrib]
  rw [← pow_eq_prod_const]
  congr
  rw [← prod_range_add_one_eq_factorial]
  rw [cast_prod]
  conv =>
    right
    right
    right
    intro i
    rw [cast_add]
    rw [add_comm]
    simp
  clear X Y
  cases n
  · contradiction
  · rename_i n
    cases n
    · contradiction
    · rename_i n
      clear h
      induction n
      · simp
      · rename_i n IH
        have A : succ (succ (succ n)) - 2 = succ n := rfl
        rw [A]
        rw [prod_range_succ]
        rw [prod_range_succ]
        have B : succ (succ n) - 2 = n := rfl
        rw [B] at IH
        rw [IH]
        rw [ENNReal.mul_inv]
        · simp
        · simp

noncomputable def mass (n : ℕ) (γ : ENNReal) := (γ^(n - 2) * (((n - 2)!) : ENNReal)⁻¹) * (1 - (γ * ((n : ENNReal) - 1)⁻¹))

theorem BernoulliExpNegSampleUnitAux_apply' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnitAux num den wf) n = mass n γ := by
  unfold mass
  cases n
  · contradiction
  · rename_i n
    let m : ℕ+ := ⟨ succ n , by exact Fin.pos { val := n, isLt := le.refl } ⟩
    have A : n + 1 = m := rfl
    rw [A]
    rw [BernoulliExpNegSampleUnitAux_apply num den m wf]
    split
    · rename_i h'
      rw [h'] at A
      rw [A] at h
      contradiction
    · rename_i h'
      cases n
      · contradiction
      · rename_i n
        rw [gamma_extract]
        · rw [← A]
          simp only [succ_sub_succ_eq_sub, add_tsub_cancel_right, cast_succ,
            ne_eq, ENNReal.one_ne_top, not_false_eq_true, ENNReal.add_sub_cancel_right]
          have B : (n : ENNReal) + 1 ≠ 0 := by exact cast_add_one_ne_zero n
          have C : (n : ENNReal) + 1 ≠ ⊤ := by simp
          rw [gamma_extract' num den (↑n + 1) B C]
          simp only [gam]
        · rw [← A]
          simp only [gt_iff_lt, one_lt_succ_succ]

noncomputable def mass' (n : ℕ) (γ : ENNReal) := (γ^n * (((n)!) : ENNReal)⁻¹)

theorem mass'_neq_top (n : ℕ) (γ : ENNReal) (h : γ ≠ ⊤) :
  mass' n γ ≠ ⊤ := by
  unfold mass'
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · induction n
    · simp
    · rename_i n IH
      rw [_root_.pow_succ]
      rw [ENNReal.mul_lt_top_iff]
      left
      constructor
      · trivial
      · exact Ne.lt_top h
  · have A : n ! > 0 := by exact factorial_pos n
    rw [@ENNReal.inv_lt_iff_inv_lt]
    simp
    exact A

theorem mass'_series_exp (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ).toReal = Real.exp (γ.toReal) := by
  unfold mass'
  rw [ENNReal.tsum_toReal_eq]
  · simp_rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp_rw [← division_def]
    rw [Real.exp_eq_exp_ℝ]
    have hexp := congrArg (fun f : ℝ → ℝ => f (γ.toReal))
      ((NormedSpace.exp_eq_tsum_div : NormedSpace.exp = fun x => ∑' (n : ℕ), x ^ n / (↑(n !) : ℝ)))
    simpa using hexp.symm
  · intro a
    exact mass'_neq_top _ _ h

theorem mass'_series_converges (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ) ≠ ⊤ := by
  by_contra h'
  have A := mass'_series_exp γ h
  rw [h'] at A
  simp at A
  have B := Real.exp_pos (ENNReal.toReal γ)
  rw [← A] at B
  simp at B

theorem mass'_series_converges' (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [ENNReal.tsum_eq_add_tsum_ite 0] at A
  have B :
      (∑' (n : ℕ), @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0 (mass' n γ))
        = ∑' (i : ℕ), mass' (i + 1) γ := by
    simpa using (tsum_shift'_1 (fun x => mass' x γ))
  have Bx :
      (∑' (x : ℕ), @ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (mass' x γ))
        = ∑' (i : ℕ), mass' (i + 1) γ := by
    simpa using B
  have Bx' :
      (∑' (x : ℕ), @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0 (mass' x γ))
        = ∑' (i : ℕ), mass' (i + 1) γ := by
    simpa [ite_eq_ite_propDecidable] using Bx
  by_contra h'
  apply A
  rw [ENNReal.add_eq_top]
  right
  exact Bx'.trans h'


theorem mass'_series_converges'_even (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd] at A
  · by_contra h'
    rw [h'] at A
    simp at A
  · exact ENNReal.summable
  · exact ENNReal.summable

theorem mass'_series_converges'_odd (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' (2 * i + 1) γ) ≠ ⊤ := by
  have A := mass'_series_converges γ h
  rw [← tsum_even_add_odd] at A
  · by_contra h'
    rw [h'] at A
    simp at A
  · exact ENNReal.summable
  · exact ENNReal.summable

theorem mass'_series_exp' (γ : ENNReal) (h : γ ≠ ⊤) :
  (∑' (i : ℕ), mass' i γ) = ENNReal.ofReal (Real.exp (γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (i : ℕ), mass' i γ)]
  · exact congrArg ENNReal.ofReal (mass'_series_exp γ h)
  · exact mass'_series_converges _ h

theorem mass_simpl (n : ℕ) (γ : ENNReal) (h : n ≥ 2) :
  mass n γ = mass' (n - 2) γ - mass' (n - 1) γ := by
  unfold mass
  unfold mass'
  rw [ENNReal.mul_sub]
  · simp only [mul_one]
    rw [mul_mul_mul_comm]
    conv =>
      left
      right
      left
      rw [mul_comm]
      rw [← _root_.pow_succ']
    rw [adhoc n h]
    congr
    rw [← ENNReal.mul_inv]
    · rw [inv_eq_iff_eq_inv]
      rw [inv_inv]
      rw [mul_comm]
      have A := @Nat.mul_factorial_pred (n - 1) (Nat.sub_ne_zero_of_lt h)
      have B : n - 1 - 1 = n - 2 := rfl
      rw [B] at A
      clear B
      rw [← A]
      simp only [cast_mul, ENNReal.natCast_sub, cast_one]
    · simp only [ne_eq, cast_eq_zero, ENNReal.sub_eq_top_iff, ENNReal.natCast_ne_top,
      ENNReal.one_ne_top, not_false_eq_true, and_true, or_true]
    · simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true, true_or]
  · intro h1 h2
    rw [ne_iff_lt_or_gt] -- Proof to simplify with mass'_neq_top
    left
    rw [ENNReal.mul_lt_top_iff]
    left
    constructor
    · have X : γ ≠ ⊤ := by
        by_contra htop
        subst htop
        simp only [ge_iff_le, ne_eq, ENNReal.inv_eq_zero, ENNReal.sub_eq_top_iff,
          ENNReal.natCast_ne_top, ENNReal.one_ne_top, not_false_eq_true, and_true, ENNReal.top_mul,
          ENNReal.zero_lt_top, not_top_lt] at *
      clear h1 h2
      induction n
      · simp only [_root_.zero_le, tsub_eq_zero_of_le, _root_.pow_zero,
        ENNReal.one_lt_top]
      · rename_i n IH
        have OR : n = 1 ∨ n ≥ 2 := by
          clear IH γ X
          cases n
          · simp at h
          · rename_i n
            cases n
            · simp
            · rename_i n
              right
              exact AtLeastTwo.prop
        cases OR
        · rename_i h'
          subst h'
          simp only [le_refl, tsub_eq_zero_of_le, _root_.pow_zero,
            ENNReal.one_lt_top]
        · rename_i h'
          have IH' := IH h'
          clear IH
          have A : succ n - 2 = succ (n - 2) := by
            cases n
            · contradiction
            · rename_i n
              cases n
              · contradiction
              · rename_i n
                rfl
          rw [A]
          rw [_root_.pow_succ]
          rw [ENNReal.mul_lt_top_iff]
          left
          constructor
          · exact IH'
          · exact Ne.lt_top X
    · have A : 0 < ((n - 2)! : ENNReal) := by
        exact_mod_cast (factorial_pos (n - 2))
      rw [@ENNReal.inv_lt_iff_inv_lt]
      simp only [ENNReal.inv_top]
      exact A

theorem if_ge_2 (x : ℕ) (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (if x = 0 then 0 else if x = 1 then 0 else BernoulliExpNegSampleUnitAux num den wf x)
    = if x = 0 then 0 else if x = 1 then 0 else mass x γ := by
  split
  · simp
  · split
    · simp
    · rename_i h1 h2
      rw [BernoulliExpNegSampleUnitAux_apply']
      · exact one_lt_iff_ne_zero_and_ne_one.mpr { left := h1, right := h2 }
      · exact gam

theorem if_split_minus (x : ℕ) (γ : ENNReal) :
  (if x = 0 then 0 else if x = 1 then 0 else (mass' (x - 2) γ - mass' (x - 1) γ))
    = (if x = 0 then 0 else if x = 1 then 0 else mass' (x - 2) γ)
      - (if x = 0 then 0 else if x = 1 then 0 else mass' (x - 1) γ) := by
  by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> simp [hx0, hx1]

theorem mass'_antitone (n : ℕ) (γ : ENNReal) (h : γ ≤ 1) :
  mass' n γ ≥ mass' (n + 1) γ  := by
  unfold mass'
  rw [pow_add]
  simp [factorial]
  rw [ENNReal.mul_inv]
  · have A : γ ^ n * γ * (((n : ENNReal) + 1)⁻¹ * (↑n !)⁻¹) = (γ ^ n * (↑n !)⁻¹) * (γ * ((n : ENNReal) + 1)⁻¹) := by
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      conv =>
        right
        rw [mul_comm]
      rw [mul_assoc]
    rw [A]
    clear A
    have C : γ * ((n : ENNReal) + 1)⁻¹ ≤ 1 := by
      have D : ((n : ENNReal) + 1)⁻¹ ≤ 1 := by
        simp only [ENNReal.inv_le_one, self_le_add_left]
      exact mul_le_one' h D
    exact mul_le_of_le_one_right' C
  · simp
  · simp

theorem mass'_series_converges'_sub (γ : ENNReal) (h1 : γ ≠ ⊤) (h2 : γ ≤ 1) :
  ∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ) ≠ ⊤ := by
  rw [ENNReal.tsum_sub]
  · have A := mass'_series_converges'_even _ h1
    apply ENNReal.sub_ne_top A
  · apply mass'_series_converges'_odd _ h1
  · rw [Pi.le_def]
    intro i
    rw [← ge_iff_le]
    apply mass'_antitone _ _ h2

theorem γ_ne_top (num : ℕ) (den : ℕ+) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≠ ⊤ := by
  subst gam
  rw [ne_iff_lt_or_gt]
  left
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_lt_top_iff]
  left
  constructor
  · rw [ENNReal.inv_lt_top]
    apply NeZero.pos
  · apply (cmp_eq_gt_iff _ _).mp
    rfl

theorem γ_le_1 (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  γ ≤ 1 := by
  subst gam
  have hden0 : (den : ENNReal) ≠ 0 := NeZero.natCast_ne (↑den) ENNReal
  have hdenTop : (den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top ↑den
  refine (ENNReal.div_le_iff hden0 hdenTop).2 ?_
  simpa using wf

theorem BernoulliExpNegSampleUnitAux_normalizes (num : ℕ) (den : ℕ+) (wf : num ≤ den) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  ∑' n : ℕ, (BernoulliExpNegSampleUnitAux num den wf) n = 1 := by
  rw [ENNReal.tsum_eq_add_tsum_ite 1]
  rw [ENNReal.tsum_eq_add_tsum_ite 0]
  simp
  have hif : ∀ x : ℕ,
      (@ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
        (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (BernoulliExpNegSampleUnitAux num den wf x)))
        = @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
            (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)) := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · simpa [hx0, hx1] using (if_ge_2 x num den wf gam)
  have hif_tsum :
      (∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
          (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (BernoulliExpNegSampleUnitAux num den wf x)))
        = ∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
            (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)) := by
    apply tsum_congr
    intro x
    exact hif x
  calc
    (∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
        (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (BernoulliExpNegSampleUnitAux num den wf x)))
        = ∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
            (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)) := hif_tsum
    _ = 1 := by
      have hshift :
          (∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
              (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)))
            = ∑' n : ℕ, mass (n + 2) γ := by
        calc
          (∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
              (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)))
              = (∑' (x : ℕ), if x = 0 then 0 else if x = 1 then 0 else mass x γ) := by
                  apply tsum_congr
                  intro x
                  by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;> simp [hx0, hx1]
          _ = ∑' n : ℕ, mass (n + 2) γ := by
              simpa using (tsum_shift'_2 (fun n => mass n γ))
      calc
        (∑' x : ℕ, @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
            (@ite ENNReal (x = 1) (Classical.propDecidable (x = 1)) 0 (mass x γ)))
            = ∑' n : ℕ, mass (n + 2) γ := hshift
        _ = ∑' n : ℕ, (mass' n γ - mass' (n + 1) γ) := by
              apply tsum_congr
              intro n
              simpa [add_assoc, add_left_comm, add_comm, two_mul] using
                (mass_simpl (n + 2) γ (by simp))
        _ = 1 := by
            rw [ENNReal.tsum_sub]
            · have X :
                  (∑' (n : ℕ), @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0 (mass' n γ))
                    = ∑' (i : ℕ), mass' (i + 1) γ := by
                simpa using (tsum_shift'_1 (fun n => mass' n γ))
              rw [ENNReal.tsum_eq_add_tsum_ite 0]
              have hsum :
                  mass' 0 γ + (∑' (x : ℕ), @ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (mass' x γ))
                    = mass' 0 γ + ∑' (i : ℕ), mass' (i + 1) γ := by
                have Xx : (∑' (x : ℕ), @ite ENNReal (x = 0) (instDecidableEqNat x 0) 0 (mass' x γ))
                    = ∑' (i : ℕ), mass' (i + 1) γ := by
                  simpa using X
                rw [Xx]
              have hsum' :
                  mass' 0 γ
                    + (∑' (x : ℕ), @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0 (mass' x γ))
                    = mass' 0 γ + ∑' (i : ℕ), mass' (i + 1) γ := by
                simpa [ite_eq_ite_propDecidable] using hsum
              calc
                (mass' 0 γ
                    + ∑' (x : ℕ), @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0 (mass' x γ))
                    - ∑' (i : ℕ), mass' (i + 1) γ
                    = (mass' 0 γ + ∑' (i : ℕ), mass' (i + 1) γ) - ∑' (i : ℕ), mass' (i + 1) γ := by
                        rw [hsum']
                _ = mass' 0 γ := by
                      rw [ENNReal.add_sub_cancel_right]
                      exact mass'_series_converges' _ (γ_ne_top num den gam)
                _ = 1 := by simp [mass']
            · exact mass'_series_converges' _ (γ_ne_top num den gam)
            · rw [@Pi.le_def]
              intro i
              rw [← ge_iff_le]
              rw [gam]
              exact mass'_antitone _ _ (γ_le_1 num den wf rfl)


theorem series_step_1 (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' (a : ℕ), if a % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf a else 0)
    = (∑' (n : ℕ), mass (2 * (n + 1)) γ) := by
  rw [← tsum_even_add_odd]
  · have he :
        (fun k : ℕ => if (2 * k) % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf (2 * k) else 0)
          = fun k : ℕ => BernoulliExpNegSampleUnitAux num den wf (2 * k) := by
      funext k
      simp
    have ho :
        (fun k : ℕ => if (2 * k + 1) % 2 = 0 then BernoulliExpNegSampleUnitAux num den wf (2 * k + 1) else 0)
          = fun _ : ℕ => 0 := by
      funext k
      simp
    rw [he, ho, tsum_zero, add_zero]
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    simp only [mul_zero, BernoulliExpNegSampleUnitAux_at_zero, zero_add]
    have X :
        (∑' (n : ℕ), @ite ENNReal (n = 0) (instDecidableEqNat n 0) 0
            (BernoulliExpNegSampleUnitAux num den wf (2 * n)))
          = ∑' (i : ℕ), BernoulliExpNegSampleUnitAux num den wf (2 * (i + 1)) := by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using
        (tsum_shift'_1 (fun n => BernoulliExpNegSampleUnitAux num den wf (2 * n)))
    have Xx :
        (∑' (x : ℕ), @ite ENNReal (x = 0) (instDecidableEqNat x 0) 0
            (BernoulliExpNegSampleUnitAux num den wf (2 * x)))
          = ∑' (i : ℕ), BernoulliExpNegSampleUnitAux num den wf (2 * (i + 1)) := by
      simpa using X
    have C : ∀ n, 2 * (n + 1) > 1 := by
      intro n
      omega
    calc
      (∑' (x : ℕ),
          @ite ENNReal (x = 0) (Classical.propDecidable (x = 0)) 0
            (BernoulliExpNegSampleUnitAux num den wf (2 * x)))
          = ∑' (i : ℕ), BernoulliExpNegSampleUnitAux num den wf (2 * (i + 1)) := by
              simpa [ite_eq_ite_propDecidable] using Xx
      _ = ∑' (n : ℕ), mass (2 * (n + 1)) γ := by
            apply tsum_congr
            intro k
            rw [BernoulliExpNegSampleUnitAux_apply' _ _ _ wf (C k) γ gam]
  · exact ENNReal.summable
  · exact ENNReal.summable


theorem series_step_3 (γ : ENNReal) :
  (∑' n : ℕ, mass (2 * (n + 1)) γ)
    = ∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ) := by
  have A : ∀ n : ℕ, 2 * (n + 1) ≥ 2 := by
    intro n
    simp
  have hsub1 : ∀ n : ℕ, 2 * (n + 1) - 2 = 2 * n := by
    intro n
    omega
  have hsub2 : ∀ n : ℕ, 2 * (n + 1) - 1 = 2 * n + 1 := by
    intro n
    omega
  apply tsum_congr
  intro n
  rw [mass_simpl (2 * (n + 1)) γ (A n), hsub1 n, hsub2 n]

noncomputable def mass'' (n : ℕ) (γ : ℝ) := (γ^n * (((n)!) : ℝ)⁻¹)

theorem series_step_4_pre (γ : ENNReal) (h : γ ≠ ⊤) (h' : γ ≤ 1) :
  (∑' n : ℕ, (mass' (2 * n) γ - mass' (2 * n + 1) γ))
    = ENNReal.ofReal (∑' n : ℕ, mass'' n (- γ.toReal)) := by
  rw [← @ENNReal.ofReal_toReal (∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ))]
  · rw [ENNReal.tsum_sub]
    · congr
      rw [ENNReal.toReal_sub_of_le]
      · rw [ENNReal.tsum_toReal_eq]
        · rw [ENNReal.tsum_toReal_eq]
          · unfold mass'
            simp_rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
            simp
            have A : Summable fun k => mass'' (2 * k) (-ENNReal.toReal γ) := by
              have X0 : Summable (fun n : ℕ => mass'' n (-ENNReal.toReal γ)) := by
                simpa [mass'', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                  (Real.summable_pow_div_factorial (-ENNReal.toReal γ))
              have Y := @Summable.comp_injective ℝ ℕ ℕ _ _ _
                (fun n => mass'' n (-ENNReal.toReal γ)) _ (fun n => 2 * n) X0 (by
                  intro a b h
                  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (by simpa using h))
              simpa [Function.comp] using Y
            have B : Summable fun k => mass'' (2 * k + 1) (-ENNReal.toReal γ) := by
              have X0 : Summable (fun n : ℕ => mass'' n (-ENNReal.toReal γ)) := by
                simpa [mass'', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                  (Real.summable_pow_div_factorial (-ENNReal.toReal γ))
              have Y := @Summable.comp_injective ℝ ℕ ℕ _ _ _
                (fun n => mass'' n (-ENNReal.toReal γ)) _ (fun n => 2 * n + 1) X0 (by
                  intro a b h
                  have h' := congrArg Nat.pred h
                  have h'' : 2 * a = 2 * b := by
                    simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using h'
                  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h'')
              simpa [Function.comp] using Y
            have X := @tsum_even_add_odd ℝ _ _ _ _ (fun k => mass'' k (-ENNReal.toReal γ)) A B
            conv =>
              right
              rw [← X]
            simp
            clear A B X
            unfold mass''
            simp
            have A : ∀ k : ℕ, (-ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹ = - ((ENNReal.toReal γ) ^ (2 * k + 1) * (↑(2 * k + 1)!)⁻¹) := by
              intro k
              rw [neg_mul_eq_neg_mul]
              congr
              rw [Odd.neg_pow (Exists.intro k rfl) (ENNReal.toReal γ)]
            simp_rw [A]
            rw [tsum_neg]
            rfl
          · intro a
            apply mass'_neq_top _ _ h
        · intro a
          apply mass'_neq_top _ _ h
      · apply ENNReal.tsum_le_tsum
        intro a
        rw [← ge_iff_le]
        apply mass'_antitone
        exact h'
      · apply mass'_series_converges'_even _ h
    · apply mass'_series_converges'_odd _ h
    · rw [Pi.le_def]
      intro i
      rw [← ge_iff_le]
      apply mass'_antitone
      exact h'
  · apply mass'_series_converges'_sub _ h
    exact h'

theorem series_step_4 (γ : ENNReal) (h : γ ≠ ⊤) (h' : γ ≤ 1) :
  (∑' (n : ℕ), (mass' (2 * n) γ - mass' (2 * n + 1) γ))
    = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  rw [series_step_4_pre _ h h']
  congr
  unfold mass''
  rw [Real.exp_eq_exp_ℝ]
  have hexp := congrArg (fun f : ℝ → ℝ => f (-γ.toReal))
    ((NormedSpace.exp_eq_tsum_div : NormedSpace.exp = fun x => ∑' (n : ℕ), x ^ n / (↑(n !) : ℝ)))
  simpa using hexp.symm

@[simp]
theorem BernoulliExpNegSampleUnit_apply_true (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) true = ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [series_step_1 num den wf γ gam]
  rw [series_step_3 γ]
  rw [series_step_4 γ]
  · apply γ_ne_top num den gam
  · apply γ_le_1 num den wf gam

theorem BernoulliExpNegSampleAux_split (num : Nat) (den : PNat)  (wf : num ≤ den) :
  (∑' (a : ℕ), BernoulliExpNegSampleUnitAux num den wf a)
    = (BernoulliExpNegSampleUnit num den wf) false
      +
      (BernoulliExpNegSampleUnit num den wf) true := by
  simp [BernoulliExpNegSampleUnit, ite_apply]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro b
  split
  · simp
  · simp

theorem BernoulliExpNegSampleUnit_normalizes (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (∑' b : Bool, (BernoulliExpNegSampleUnit num den wf) b) = 1 := by
  calc
    (∑' b : Bool, (BernoulliExpNegSampleUnit num den wf) b)
      = ∑' (a : ℕ), BernoulliExpNegSampleUnitAux num den wf a := by
          symm
          simpa [tsum_bool, add_comm] using (BernoulliExpNegSampleAux_split num den wf)
    _ = 1 := BernoulliExpNegSampleUnitAux_normalizes num den wf gam

@[simp]
theorem BernoulliExpNegSampleUnit_apply_false (num : Nat) (den : PNat)  (wf : num ≤ den) (γ : ENNReal) (gam : γ = (num : ENNReal) / (den : ENNReal)) :
  (BernoulliExpNegSampleUnit num den wf) false = 1 - ENNReal.ofReal (Real.exp (- (γ.toReal))) := by
  have A := BernoulliExpNegSampleUnit_normalizes num den wf γ gam
  have B : ENNReal.ofReal (Real.exp (-γ.toReal)) + (BernoulliExpNegSampleUnit num den wf) false = 1 := by
    simpa [tsum_bool, add_comm, BernoulliExpNegSampleUnit_apply_true num den wf γ gam] using A
  have B' : (BernoulliExpNegSampleUnit num den wf) false + ENNReal.ofReal (Real.exp (-γ.toReal)) = 1 := by
    simpa [add_comm] using B
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top B'

theorem BernoulliExpNegSampleGenLoop_normalizes (iter : Nat) :
  (∑' b : Bool, (BernoulliExpNegSampleGenLoop iter) b) = 1 := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop]
  · rename_i iter IH
    rw [BernoulliExpNegSampleGenLoop]
    simp [BernoulliExpNegSampleUnit_apply_true, BernoulliExpNegSampleUnit_apply_false]
    have IH' : BernoulliExpNegSampleGenLoop iter false + BernoulliExpNegSampleGenLoop iter true = 1 := by
      simpa [tsum_bool, add_comm] using IH
    calc
      ENNReal.ofReal (Real.exp (-1)) * BernoulliExpNegSampleGenLoop iter true +
          (ENNReal.ofReal (Real.exp (-1)) * BernoulliExpNegSampleGenLoop iter false +
            (1 - ENNReal.ofReal (Real.exp (-1))))
          = ENNReal.ofReal (Real.exp (-1)) *
              (BernoulliExpNegSampleGenLoop iter true + BernoulliExpNegSampleGenLoop iter false) +
              (1 - ENNReal.ofReal (Real.exp (-1))) := by
                rw [← add_assoc, ← left_distrib]
      _ = ENNReal.ofReal (Real.exp (-1)) * 1 + (1 - ENNReal.ofReal (Real.exp (-1))) := by
            simpa [add_comm] using congrArg (fun t => ENNReal.ofReal (Real.exp (-1)) * t + (1 - ENNReal.ofReal (Real.exp (-1)))) IH'
      _ = 1 := by simp

theorem BernoulliExpNegSampleGenLoop_apply_true (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) true = ENNReal.ofReal (Real.exp (- iter)) := by
  induction iter
  · simp [BernoulliExpNegSampleGenLoop]
  · rename_i iter IH
    unfold BernoulliExpNegSampleGenLoop
    split
    · contradiction
    · rename_i h
      simp
      simp [IH]
      clear IH
      have hnn : 0 ≤ Real.exp (-↑iter) := Real.exp_nonneg _
      calc
        ENNReal.ofReal (Real.exp (-1)) * ENNReal.ofReal (Real.exp (-↑iter))
            = ENNReal.ofReal (Real.exp (-1) * Real.exp (-↑iter)) := by
                rw [ENNReal.ofReal_mul' hnn]
        _ = ENNReal.ofReal (Real.exp (-1 + -↑iter)) := by
              rw [Real.exp_add]

theorem BernoulliExpNegSampleGenLoop_apply_false (iter : Nat) :
  (BernoulliExpNegSampleGenLoop iter) false = 1 - ENNReal.ofReal (Real.exp (- iter)) := by
  have A := BernoulliExpNegSampleGenLoop_normalizes iter
  simp at A
  rw [BernoulliExpNegSampleGenLoop_apply_true] at A
  rw [← A]
  simp

/--
Bernoulli negative exponential sampler is a proper distribution
-/
@[simp]
theorem BernoulliExpNegSample_normalizes (num : Nat) (den : PNat) :
  (∑' b : Bool, (BernoulliExpNegSample num den) b) = 1 := by
  unfold BernoulliExpNegSample
  split
  · rename_i h
    simpa using (BernoulliExpNegSampleUnit_normalizes num den h ((num : NNReal) / (den : NNReal)) rfl)
  · rename_i h
    simp
    have A : BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den) false +
        BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den) true = 1 := by
      simpa [tsum_bool, add_comm] using
        (BernoulliExpNegSampleUnit_normalizes (num % den) den (rat_less_floor_le1 num den)
          (((num % (den : ℕ)) : ENNReal) / (den : ENNReal)) rfl)
    have B : BernoulliExpNegSampleGenLoop (num / den) false + BernoulliExpNegSampleGenLoop (num / den) true = 1 := by
      simpa [tsum_bool, add_comm] using (BernoulliExpNegSampleGenLoop_normalizes (num / den))
    calc
      BernoulliExpNegSampleGenLoop (num / den) true * ENNReal.ofReal (Real.exp (-(↑(num % ↑den) / ↑↑den))) +
          (BernoulliExpNegSampleGenLoop (num / den) true *
              (1 - ENNReal.ofReal (Real.exp (-(↑(num % ↑den) / ↑↑den)))) +
            BernoulliExpNegSampleGenLoop (num / den) false)
          = BernoulliExpNegSampleGenLoop (num / den) true *
              ((BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) true +
                (BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) false) +
              BernoulliExpNegSampleGenLoop (num / den) false := by
                have hgamma : ((((num % (den : ℕ)) : ENNReal) / (den : ENNReal)).toReal) = (↑(num % ↑den) / ↑↑den) := by
                  rw [ENNReal.toReal_div]
                  simp
                have htrue := BernoulliExpNegSampleUnit_apply_true (num := num % den) (den := den)
                  (wf := rat_less_floor_le1 num den)
                  (γ := (((num % (den : ℕ)) : ENNReal) / (den : ENNReal))) (gam := rfl)
                have hfalse := BernoulliExpNegSampleUnit_apply_false (num := num % den) (den := den)
                  (wf := rat_less_floor_le1 num den)
                  (γ := (((num % (den : ℕ)) : ENNReal) / (den : ENNReal))) (gam := rfl)
                have htrue' : (BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) true =
                    ENNReal.ofReal (Real.exp (-(↑(num % ↑den) / ↑↑den))) := by
                  rw [htrue]
                  rw [hgamma]
                have hfalse' : (BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) false =
                    1 - ENNReal.ofReal (Real.exp (-(↑(num % ↑den) / ↑↑den))) := by
                  rw [hfalse]
                  rw [hgamma]
                rw [htrue', hfalse']
                rw [← add_assoc, ← mul_add]
      _ = BernoulliExpNegSampleGenLoop (num / den) true * 1 + BernoulliExpNegSampleGenLoop (num / den) false := by
            have A' : (BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) true +
                (BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)) false = 1 := by
              simpa [add_comm] using A
            rw [A']
      _ = 1 := by simpa [add_comm] using B

theorem ENNReal_Real_mul_absorb (a : ENNReal) (b : ℝ) (h1 : b ≥ 0) :
  ENNReal.toReal a * b = ENNReal.toReal (a * (ENNReal.ofReal b)) := by
  simp
  left
  exact (ENNReal.toReal_ofReal h1).symm

theorem Nat_eq_to_ENNReal_eq (a b : ℕ) (h : a = b) :
  (a : ENNReal) = (b : ENNReal) := by
  exact congrArg Nat.cast h

theorem ENNReal_eq_to_Real_eq (a b : ENNReal) (h : a = b) :
  a.toReal = b.toReal := by
  exact congrArg ENNReal.toReal h

/--
Evaluation of Bernoulli negative exponential sampler at ``true``
-/
@[simp]
theorem BernoulliExpNegSample_apply_true (num : Nat) (den : PNat):
  (BernoulliExpNegSample num den) true = ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  simp [BernoulliExpNegSample]
  split
  · rename_i h
    rw [BernoulliExpNegSampleUnit_apply_true num den h ((num : NNReal) / (den : NNReal)) rfl]
    congr
    rw [ENNReal.toReal_div]
    simp
  · rename_i h
    simp [BernoulliExpNegSampleGenLoop_apply_true, BernoulliExpNegSampleUnit_apply_true]
    rw [← ENNReal.ofReal_mul' (Real.exp_nonneg _)]
    rw [← Real.exp_add]
    congr 1
    have hden : (den : ℝ) ≠ 0 := by
      exact_mod_cast (show (↑den : ℕ) ≠ 0 from PNat.ne_zero den)
    have hsum : ((num % ↑den : ℕ) : ℝ) / (den : ℝ) + ((num / ↑den : ℕ) : ℝ) = (num : ℝ) / (den : ℝ) := by
      apply (eq_div_iff hden).2
      have hnatR : ((num % ↑den : ℕ) : ℝ) + (den : ℝ) * ((num / ↑den : ℕ) : ℝ) = (num : ℝ) := by
        exact_mod_cast (Nat.mod_add_div num ↑den)
      calc
        ((((num % ↑den : ℕ) : ℝ) / (den : ℝ) + ((num / ↑den : ℕ) : ℝ)) * (den : ℝ))
            = ((num % ↑den : ℕ) : ℝ) + (den : ℝ) * ((num / ↑den : ℕ) : ℝ) := by
                field_simp [hden]
        _ = (num : ℝ) := by simpa [mul_comm, mul_left_comm, mul_assoc] using hnatR
    have hrem : ((((num % ↑den : ℕ) : NNReal) / (den : NNReal)) : ℝ) = ((num % ↑den : ℕ) : ℝ) / (den : ℝ) := by
      simp
    have hquo : (((num : NNReal) / (den : NNReal)) : ℝ) = (num : ℝ) / (den : ℝ) := by
      simp
    have hsum' : ((((num % ↑den : ℕ) : NNReal) / (den : NNReal)) : ℝ) + ((num / ↑den : ℕ) : ℝ)
        = (((num : NNReal) / (den : NNReal)) : ℝ) := by
      simpa [hrem, hquo] using hsum
    have hneg : -(((((num % ↑den : ℕ) : NNReal) / (den : NNReal)) : ℝ) + ((num / ↑den : ℕ) : ℝ))
        = -((((num : NNReal) / (den : NNReal)) : ℝ)) := by
      linarith [hsum']
    simpa [neg_add_rev] using hneg

/--
Evaluation of Bernoulli negative exponential sampler at ``false``
-/
@[simp]
theorem BernoulliExpNegSample_apply_false (num : Nat) (den : PNat) :
  (BernoulliExpNegSample num den) false = 1 - ENNReal.ofReal (Real.exp (- ((num : NNReal) / (den : NNReal)))) := by
  have A := BernoulliExpNegSample_normalizes num den
  simp at A
  rw [← A]
  simp

end SLang
