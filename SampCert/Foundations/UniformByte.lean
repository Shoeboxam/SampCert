/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Util.Util
import SampCert.Foundations.Auto
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import SampCert.Foundations.Monad


/-!
# ``probUniformByte`` Properties

This file contains lemmas about ``probUniformByte``, a ``SLang`` sampler for the
uniform distribution on bytes.

It also contains the derivation that ``probUniformP2`` is a uniform distribution.
-/


open Classical Nat PMF



namespace SLang




private def uint8EquivFin256 : UInt8 ≃ Fin 256 where
  toFun v := ⟨v.toNat, by simp [UInt8.toNat_lt v]⟩
  invFun v := UInt8.ofNatLT v (by simp [v.2])
  left_inv v := by
    cases v
    simp [UInt8.ofNatLT, UInt8.toNat]
  right_inv v := by
    apply Fin.ext
    simp [UInt8.ofNatLT, UInt8.toNat]

local instance : Finite UInt8 := by
  exact ⟨uint8EquivFin256⟩



/--
ProbUniformByte is a proper distribution
-/
def probUniformByte_normalizes : HasSum probUniformByte 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold SLang.probUniformByte
  rw [division_def]
  rw [ENNReal.tsum_mul_right]
  simp only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_one_iff _).mp
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.tsum_toReal_eq ?G1]
  case G1 => simp
  simp only [ENNReal.toReal_one, tsum_const, nsmul_eq_mul]
  rw [Nat.card_congr uint8EquivFin256]
  simp [ENNReal.toReal_inv]

/--
ProbUniformByte as a PMF
-/
def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

/--
Evaluation of ``probUniformByteUpperBits`` for inside the support
-/
def probUniformByteUpperBits_eval_support {i x : ℕ} (Hx : x < 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 2^(8 - i) / UInt8.size := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [probUniformByte]
  cases (Classical.em (i < 8))

  · -- Simplify body
    rw [max_eq_left (by linarith)]
    rw [min_eq_right (by linarith)] at Hx
    conv =>
      enter [1, 1, a]
      rw [Nat.shiftRight_eq_div_pow]
    conv =>
      enter [1, 1, a]
      rw [<- mul_one (256)⁻¹]
      rw [<- mul_zero (256)⁻¹]
      rw [<- mul_ite]
    rw [ENNReal.tsum_mul_left]
    rw [division_def]
    rw [mul_comm]
    congr 1

    -- Restruct sum to type where body is constant
    rw [<- (@tsum_subtype_eq_of_support_subset  _ _ _ _ _ { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } ?G1)]
    case G1 => simp [Function.support]
    generalize HT : { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } = T
    have H (x1 : T) : (@ite _ (x = (x1 : UInt8).toNat / 2 ^ (8 - i)) _ (1 : ENNReal) (0 : ENNReal)) = 1 := by
      apply ite_eq_iff.mpr
      simp
      rcases x1
      rename_i h val property
      subst HT
      simp_all only
      simp_all only [Set.mem_setOf_eq]
    conv =>
      enter [1, 1, a]
      rw [H a]
    clear H

    -- Rewrite to real sum
    -- Simplify me
    suffices ENNReal.toReal (∑' (_ : T), 1) = ENNReal.toReal (2 ^ (8 - i)) by
      refine (ENNReal.toReal_eq_toReal_iff' ?G1 ?G2).mp this
      case G1 =>
        rw [tsum_eq_finsum ?G1]
        case G1 => simp [Function.support, Set.toFinite (Set.univ : Set T)]
        simp
        have R := @finsum_induction ENNReal T _ (fun _ => 1) (fun z => z ≠ ⊤) (by simp) (by aesop) (by simp)
        simp at R
        trivial
      case G2 => simp

    -- Rewrite to set cardinality
    rw [ENNReal.tsum_toReal_eq ?G1]
    case G1 => simp
    simp [tsum_const]


    -- Evaluate set cardinality as the range of a finite interval map
    have hpow256 : 2 ^ i * 2 ^ (8 - i) = 256 := by
      rw [← pow_add]
      have hi : i + (8 - i) = 8 := Nat.add_sub_of_le (by linarith)
      rw [hi]
      norm_num
    have hxle : x + 1 ≤ 2 ^ i := Nat.succ_le_of_lt Hx
    have hf_lt (k : Fin (2 ^ (8 - i))) : x * 2 ^ (8 - i) + k.1 < 256 := by
      have hlt : x * 2 ^ (8 - i) + k.1 < x * 2 ^ (8 - i) + 2 ^ (8 - i) := by
        exact Nat.add_lt_add_left k.2 (x * 2 ^ (8 - i))
      have hmul : x * 2 ^ (8 - i) + 2 ^ (8 - i) = (x + 1) * 2 ^ (8 - i) := by
        rw [Nat.add_mul, one_mul]
      refine lt_of_lt_of_le (hmul ▸ hlt) ?_
      calc
        (x + 1) * 2 ^ (8 - i) ≤ 2 ^ i * 2 ^ (8 - i) := Nat.mul_le_mul_right _ hxle
        _ = 256 := hpow256
    let f : Fin (2 ^ (8 - i)) → UInt8 := fun k =>
      UInt8.ofNatLT (x * 2 ^ (8 - i) + k.1) (by
        rw [UInt8.size]
        exact hf_lt k)
    have hT : T = Set.range f := by
      rw [← HT]
      ext b
      constructor
      · intro hb
        have hden : 0 < 2 ^ (8 - i) := by
          exact pow_pos (by omega) _
        have hlow : x * 2 ^ (8 - i) ≤ b.toNat := by
          exact (Nat.le_div_iff_mul_le hden).mp (Eq.le hb)
        have hupp : b.toNat < (x + 1) * 2 ^ (8 - i) := by
          have hle : b.toNat / 2 ^ (8 - i) ≤ x := by
            exact Eq.ge hb
          exact (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_iff.mpr hle)
        refine ⟨⟨b.toNat - x * 2 ^ (8 - i), ?_⟩, ?_⟩
        · have hsub : b.toNat - x * 2 ^ (8 - i) < (x + 1) * 2 ^ (8 - i) - x * 2 ^ (8 - i) := by
            exact Nat.sub_lt_sub_right hlow hupp
          refine lt_of_lt_of_le hsub ?_
          rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
        · apply UInt8.toNat_inj.mp
          have hb256 : b.toNat < 256 := by simpa [UInt8.size] using UInt8.toNat_lt b
          have harg256 : x * 2 ^ (8 - i) + (b.toNat - x * 2 ^ (8 - i)) < 256 := by omega
          calc
            (f ⟨b.toNat - x * 2 ^ (8 - i), by
              have hsub : b.toNat - x * 2 ^ (8 - i) < (x + 1) * 2 ^ (8 - i) - x * 2 ^ (8 - i) := by
                exact Nat.sub_lt_sub_right hlow hupp
              refine lt_of_lt_of_le hsub ?_
              rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]⟩).toNat
                = x * 2 ^ (8 - i) + (b.toNat - x * 2 ^ (8 - i)) := by
                    simp [f, UInt8.ofNatLT_eq_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt harg256]
            _ = b.toNat := Nat.add_sub_of_le hlow
      · rintro ⟨k, rfl⟩
        have hk256 : x * 2 ^ (8 - i) + k.1 < 256 := hf_lt k
        have hden : 0 < 2 ^ (8 - i) := by
          exact pow_pos (by omega) _
        simp only [Set.mem_setOf_eq]
        rw [show (f k).toNat = x * 2 ^ (8 - i) + k.1 by
          simp [f, UInt8.ofNatLT_eq_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hk256]]
        refine (nat_div_eq_le_lt_iff hden).mpr ?_
        constructor
        · exact Nat.le_add_right _ _
        · calc
            x * 2 ^ (8 - i) + k.1 < x * 2 ^ (8 - i) + 2 ^ (8 - i) := by
              exact Nat.add_lt_add_left k.2 _
            _ = (x + 1) * 2 ^ (8 - i) := by
              rw [Nat.add_mul, one_mul]
    rw [hT, Set.ncard_range_of_injective]
    · simp
    · intro a b hab
      apply Fin.ext
      have hab' := congrArg UInt8.toNat hab
      have ha256 : x * 2 ^ (8 - i) + a.1 < 256 := by
        exact hf_lt a
      have hb256 : x * 2 ^ (8 - i) + b.1 < 256 := by
        exact hf_lt b
      have : x * 2 ^ (8 - i) + a.1 = x * 2 ^ (8 - i) + b.1 := by
        simpa [f, UInt8.ofNatLT_eq_ofNat, UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha256,
          Nat.mod_eq_of_lt hb256] using hab'
      omega
  · rw [max_eq_right (by linarith)]
    rw [min_eq_left (by linarith)] at Hx
    rw [tsum_eq_single (UInt8.ofNatLT x (by simpa [UInt8.size] using Hx)) ?G1]
    case G1 =>
      intro b' Hb'
      simp
      intro Hx'
      exfalso
      apply Hb'
      apply UInt8.toNat_inj.mp
      rw [UInt8.ofNatLT_eq_ofNat, UInt8.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by simpa [UInt8.size] using Hx)]
      exact Hx'.symm
    simp


/--
Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-/
def probUniformByteUpperBits_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 0 := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [probUniformByte]
  intro v H1
  exfalso
  cases (Classical.em (i < 8))
  · -- i < 8
    rename_i Hi
    rw [max_eq_left (by linarith)] at H1
    rw [min_eq_right (by linarith)] at Hx
    simp_all
    rw [Nat.shiftRight_eq_div_pow] at *
    have H2 := UInt8.toNat_lt v
    apply Nat.mul_le_of_le_div (2 ^ (8 - i)) (2 ^ i) v.toNat at Hx
    rw [<- pow_add] at Hx
    have X : (i + (8 - i)) = 8 := by
      apply add_sub_of_le
      linarith
    rw [X] at Hx
    clear X
    linarith
  · -- i >= 8
    rename_i Hi
    rw [max_eq_right (by linarith)] at H1
    rw [min_eq_left (by linarith)] at Hx
    have H2 := UInt8.toNat_lt v
    simp_all
    linarith


lemma UIint8_cast_lt_size (a : UInt8) : a.toNat < UInt8.size := by
  rcases a with ⟨ ⟨ a', Ha' ⟩ ⟩
  rw [UInt8.toNat]
  simp
  apply Ha'


/--
Evaluation of ``probUniformP2`` for inside the support
-/
def probUniformP2_eval_support {i x : ℕ} (Hx : x < 2 ^ i):
    probUniformP2 i x = (1 / 2 ^ i) := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    rw [probUniformP2]
    split
    · rename_i h
      rw [probUniformByteUpperBits_eval_support]
      · rw [UInt8.size]
        have X : 256 = 2^8 := by simp
        rw [X]
        clear X
        rw [cast_pow]
        apply (ENNReal.div_eq_div_iff _ _ _ _).mpr <;> try simp
        rw [← pow_add]
        congr 1
        rw [add_tsub_cancel_iff_le]
        linarith
      · rw [min_eq_right ?G1]
        case G1 => linarith
        exact Hx
    ·
      simp [probUniformByte]

      -- Simplify, rewrite to indicator function
      conv =>
        enter [1, 1, a]
        rw [<- ENNReal.tsum_mul_left]
        enter [1, b]
        rw [<- mul_one (probUniformP2 (i - 8) b)]
        rw [<- mul_zero (probUniformP2 (i - 8) b)]
        rw [<- mul_ite]
        rw [<- mul_assoc]

      -- Similar to the Laplace proof: use Euclidean division to rewrite
      -- to product of indicator functions
      rcases @euclidean_division x UInt8.size (by simp) with ⟨ p, q, Hq, Hx ⟩
      have X (a : UInt8) (b : ℕ) D :
          (@ite _ (q + UInt8.size * p = UInt8.size * b + a.toNat) D (1 : ENNReal) 0) =
          (if p = b then (1 : ENNReal) else 0) * (if q = a.toNat then (1 : ENNReal) else 0) := by
        split
        · rename_i He
          conv at He =>
            enter [2]
            rw [add_comm]
          have R := (euclidean_division_uniquness _ _ _ _ (by simp) Hq ?G3).mp He
          case G3 => apply UIint8_cast_lt_size
          rcases R with ⟨ R1 , R2 ⟩
          simp_all
        · rename_i He
          suffices (p ≠ b) ∨ (q ≠ a.toNat) by
            rcases this with Ht | Ht
            · rw [ite_eq_right_iff.mpr]
              · simp
              · intro Hk
                exfalso
                apply Ht Hk
            · rw [mul_comm]
              rw [ite_eq_right_iff.mpr]
              · simp
              · intro Hk
                exfalso
                apply Ht Hk
          by_cases hp : p = b
          · right
            intro hq
            apply He
            simp [hp, hq, add_comm]
          · exact Or.inl hp
      conv =>
        enter [1, 1, a, 1, b]
        rw [Hx]
        rw [X a b]
      clear X

      -- Separate the sums
      conv =>
        enter [1, 1, a, 1, b]
        repeat rw [mul_assoc]
      conv =>
        enter [1, 1, a]
        rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_left]
      conv =>
        enter [1, 2, 1, a, 1, b]
        rw [<- mul_assoc]
        rw [mul_comm]
      conv =>
        enter [1, 2, 1, a]
        rw [ENNReal.tsum_mul_left]
      conv =>
        enter [1, 2]
        rw [ENNReal.tsum_mul_right]
      simp

      -- Simplify the singleton sums
      rw [tsum_eq_single p ?G1]
      case G1 =>
        intro _ HK
        simp
        intro HK'
        exfalso
        exact HK (id (Eq.symm HK'))
      have X : (UInt8.ofNatLT q (by simpa [UInt8.size] using Hq)).toNat = q := by
        rw [UInt8.ofNatLT_eq_ofNat, UInt8.toNat_ofNat']
        simpa [UInt8.size] using Nat.mod_eq_of_lt Hq
      rw [tsum_eq_single (UInt8.ofNatLT q (by simpa [UInt8.size] using Hq)) ?G1]
      case G1 =>
        simp
        intro b HK' HK''
        apply HK'
        rcases b with ⟨ ⟨ b' , Hb' ⟩ ⟩
        apply UInt8.toNat_inj.mp
        rw [X]
        exact HK''.symm
      rw [X]
      clear X
      simp

      -- Apply the IH
      rw [ih]
      · simp
        rw [<- ENNReal.mul_inv ?G1 ?G2]
        case G1 => simp
        case G2 => simp
        congr 1
        have H256 : (256 : ENNReal) = (256 : ℕ) := by simp
        rw [H256]
        have X : (256 : ℕ) = 2^8 := by simp
        rw [X]
        rw [cast_pow]
        rw [cast_two]
        rw [← pow_add]
        congr 1
        apply add_sub_of_le
        linarith
      · simp
        linarith
      ·
        have Hx'' : UInt8.size * p < (2 ^ i : ℕ) := by
          have hxpow : x < 2 ^ i := by
            assumption
          have hp : UInt8.size * p ≤ x := by
            rw [Hx]
            exact Nat.le_add_left _ _
          exact lt_of_le_of_lt hp hxpow
        rw [UInt8.size] at Hx''
        have Y : 256 = 2^8 := by simp
        rw [Y] at Hx''
        clear Y
        have hdiv : 2 ^ 8 ∣ 2 ^ i := by
          apply Nat.pow_dvd_pow (OfNat.ofNat 2)
          linarith
        have W : p < 2 ^ i / 2 ^ 8 := by
          rw [Nat.lt_div_iff_mul_lt' hdiv]
          simpa [Nat.mul_comm] using Hx''
        apply (LT.lt.trans_eq W)
        apply Nat.pow_div <;> linarith

/--
Evaluation of ``probUniformP2`` for zero-shifts outside of the support
-/
def probUniformP2_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ i):
    probUniformP2 i x = 0 := by
  induction i using Nat.strong_induction_on generalizing x with
  | h i ih =>
    rw [probUniformP2]
    split
    · apply probUniformByteUpperBits_eval_zero
      rw [min_eq_right]
      · trivial
      · linarith
    · simp
      intro i1
      right
      intro i2 Hi
      apply ih
      · apply sub_lt
        · linarith
        · simp
      · rw [Hi] at Hx
        simp_all
        suffices 2^ i ≤ UInt8.size * i2 by
          rw [UInt8.size] at this
          rw [← Nat.pow_div (by trivial) ?G1]
          case G1 => simp
          exact Nat.div_le_of_le_mul this
        have H : (i1.toNat < UInt8.size) := by exact UIint8_cast_lt_size i1

        -- Establish this bound by the uniqueness of Euclidean division
        rcases @euclidean_division (2^i) (2^8) (by simp) with ⟨ p, q, Hq, H ⟩
        have Hple : (p ≤ i2) := by linarith
        have Heuc' : q + 2 ^ 8 * p = 0 + 2 ^ 8 * (2 ^ (i - 8)) := by
          rw [<- H]
          rw [zero_add]
          rw [<- pow_add]
          congr 1
          symm
          apply add_sub_of_le
          trivial
        have W := (euclidean_division_uniquness _ _ _ _ (by simp) Hq (by simp)).mp Heuc'
        simp_all

end SLang
