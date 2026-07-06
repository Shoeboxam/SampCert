/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenDP contributors
-/

import SampCert.SLang
import Mathlib.Data.Real.Basic

/-!
# Rounded Gaussian sampler model

This file sketches the mathematical interface for the native rounded Gaussian
sampler used by OpenDP.  It is intentionally small: the global privacy proof
should depend on this public profile and the local obligations stated in
`Properties.lean`, not on Rust implementation details.
-/

namespace SLang
namespace RoundedGaussian

noncomputable section

/-- A signed dyadic real `mantissa * 2^exponent`.  This is the common exact
support language for finite native prefixes, `f32` cell boundaries, and snapped
scales. -/
structure Dyadic where
  mantissa : ℤ
  exponent : ℤ
deriving DecidableEq, Repr

/-- Mathematical interpretation of a dyadic. -/
def Dyadic.toReal (x : Dyadic) : ℝ :=
  (x.mantissa : ℝ) * (2 : ℝ) ^ x.exponent

/-- A possibly unbounded dyadic interval.  It represents one exact output cell
or one public comb interval. -/
structure DyadicInterval where
  lower : Option Dyadic
  upper : Option Dyadic
deriving Inhabited, Repr

/-- Membership in a dyadic interval. -/
def DyadicInterval.Contains (interval : DyadicInterval) (x : Dyadic) : Prop :=
  (match interval.lower with
    | none => True
    | some lower => lower.toReal ≤ x.toReal) ∧
  (match interval.upper with
    | none => True
    | some upper => x.toReal ≤ upper.toReal)

/-- The extended `f32` output alphabet.  The finite case stores the IEEE bit
pattern as one of the `2^32` possible bit strings. -/
inductive ExtF32 where
  | negInf
  | finite (bits : Fin (2 ^ 32))
  | posInf
deriving DecidableEq, Inhabited, Repr

/-- An output dtype/lattice whose cells have dyadic boundaries.  This is the
generic target for rounded dyadic Gaussian laws: `f32`, `f64`, `bf16`, fixed
point, and integer grids should be instances of this structure. -/
structure DyadicOutputLattice where
  Output : Type
  [outputDecidableEq : DecidableEq Output]
  cell : Output → DyadicInterval
  round : Dyadic → Output

/-- Concrete f32 cell hook.  The actual IEEE cell definition will be supplied by
the f32 arithmetic formalization. -/
opaque extF32Cell : ExtF32 → DyadicInterval

/-- Concrete f32 rounding hook. -/
opaque roundDyadicToExtF32 : Dyadic → ExtF32

/-- Concrete f32 lattice. -/
def extF32Lattice : DyadicOutputLattice where
  Output := ExtF32
  cell := extF32Cell
  round := roundDyadicToExtF32

/-- Public finite native profile. -/
structure NativeProfile where
  kMax : ℕ
  factoryDepth : ℕ
  samplerBits : ℕ
  finalizationBits : ℕ
  comparisonWindow : ℕ
  clipScaleMaxRatio : ℚ

/-- The fixed profile currently used by the Rust native reference path. -/
def fixedF32Profile : NativeProfile where
  kMax := 14
  factoryDepth := 26
  samplerBits := 96
  finalizationBits := 96
  comparisonWindow := 192
  clipScaleMaxRatio := (15 : ℚ) / 2

/-- A parameterized native profile.  This is the main formalization target;
`fixedF32Profile` is only the concrete Rust instantiation. -/
def nativeProfile
    (kMax factoryDepth samplerBits finalizationBits comparisonWindow : ℕ)
    (clipScaleMaxRatio : ℚ) : NativeProfile where
  kMax := kMax
  factoryDepth := factoryDepth
  samplerBits := samplerBits
  finalizationBits := finalizationBits
  comparisonWindow := comparisonWindow
  clipScaleMaxRatio := clipScaleMaxRatio

def NativeProfile.factoryCountBound (profile : NativeProfile) : ℕ :=
  profile.kMax * profile.kMax + profile.kMax + 2

def NativeProfile.comparisonCountBound (profile : NativeProfile) : ℕ :=
  2 * profile.factoryDepth * profile.factoryCountBound

/-- Public parameters after scale snapping.  `sigma` is the public scale
actually used by the mechanism, for example the upward-snapped `f32` scale. -/
structure NativeInput where
  mu : ℝ
  sigma : ℝ
  range : ℝ

/-- The fixed-profile clipped native path is used only when the public clipped
range fits inside the structural support provided by the `K` cap. -/
def SupportCondition (profile : NativeProfile) (input : NativeInput) : Prop :=
  0 < input.sigma ∧
  0 ≤ input.range ∧
  2 * input.range < input.sigma * ((profile.kMax : ℝ) + 1) ∧
  input.range < (profile.clipScaleMaxRatio : ℝ) * input.sigma

/-- PSRN interval for the fractional part `U ∈ [num / 2^bits,
(num + 1) / 2^bits)`. -/
structure PSRNPrefix where
  num : ℕ
  bits : ℕ
deriving Repr

/-- Accepted ideal normal trace before final rounding. -/
structure NormalTrace where
  negative : Bool
  k : ℕ
  frac : PSRNPrefix
deriving Repr

/-- Public structural cap for the integer part of the Karney decomposition. -/
def TraceWithinProfile (profile : NativeProfile) (trace : NormalTrace) : Prop :=
  trace.k ≤ profile.kMax ∧ trace.frac.bits ≤ profile.finalizationBits

inductive ComparisonKind where
  | uniformGreaterThanUniform
  | uniformLessThanHalf
deriving DecidableEq, Repr

inductive FactoryKind where
  | expHalf
  | expUniform
  | expHalfXSquared
deriving DecidableEq, Repr

/-- Finalization result of one accepted trace under the native proof model. -/
inductive FinalizationResult (Output : Type) where
  | output (y : Output)
  | rejectedComb
  | resourceLimit
deriving Repr

/-- Result of one bounded native sampler attempt before wrapper resampling. -/
inductive AttemptResult where
  | output (trace : NormalTrace)
  | ordinaryReject
  | rejectedSampler
  | resourceLimit
deriving Repr

/-- The implementation should refine this relation: every Rust output or
declared rejection maps to one of these mathematical cases. -/
structure NativeSamplerSpec (profile : NativeProfile) (lattice : DyadicOutputLattice) where
  attempt : AttemptResult → Prop
  finalize : NormalTrace → FinalizationResult lattice.Output → Prop
  attempt_resource_limits_fail_closed :
    ∀ r, attempt r → r = AttemptResult.resourceLimit → False
  finalization_resource_limits_fail_closed :
    ∀ trace r, finalize trace r → r = FinalizationResult.resourceLimit → False

/-- Abstract probability that a sampler-side comparison remains undecided at
the public prefix cap.  The concrete proof should replace this abstraction by
the exact PSRN comparison semantics. -/
opaque comparisonUndecidedProbability :
  NativeProfile → ComparisonKind → ℝ

/-- Abstract probability that a Bernoulli factory survives past the public
depth cap. -/
opaque factoryDepthFailureProbability :
  NativeProfile → FactoryKind → ℝ

/-- Public comb membership for finalization rejections. -/
opaque InPublicComb :
  NativeProfile → NativeInput → NormalTrace → Prop

/-- Discrete pre-rounding support used by the native proof.  A support point is
dyadic, rounds to an extended `f32` output, and may be rejected by the public
comb/finalization rule. -/
structure DyadicSupportPoint where
  value : Dyadic
  trace : NormalTrace
deriving Repr

/-- A rounded discrete Gaussian law after finite-budget sampler and comb
rejections.  The probability of an output is the sum of the accepted dyadic
weights that round to that output.  The concrete proof should instantiate
`weight` from the Karney/DFW trace probability and show that it is zero on
rejected sampler/comb traces. -/
structure RoundedDyadicGaussianLaw (lattice : DyadicOutputLattice) where
  support : Type
  point : support → DyadicSupportPoint
  round : support → lattice.Output
  rejected : support → Prop
  weight : support → ENNReal
  outputMass : lattice.Output → ENNReal
  weight_zero_of_rejected : ∀ x, rejected x → weight x = 0
  round_eq_lattice_round :
    ∀ x, round x = lattice.round (point x).value
  point_mem_round_cell :
    ∀ x, DyadicInterval.Contains (lattice.cell (round x)) (point x).value
  outputMass_eq :
    ∀ y, outputMass y =
      (letI := lattice.outputDecidableEq
       ∑' x : support, if round x = y then weight x else 0)
  hasSum_outputMass :
    HasSum outputMass 1

/-- PMF over rounded outputs induced by a rounded dyadic Gaussian law. -/
def RoundedDyadicGaussianLaw.toPMF
    {lattice : DyadicOutputLattice}
    (law : RoundedDyadicGaussianLaw lattice) : PMF lattice.Output :=
  ⟨law.outputMass, law.hasSum_outputMass⟩

/-- A native algorithm proof target: the algorithm's returned-output PMF agrees
pointwise with a rounded dyadic Gaussian law. -/
structure EmitsRoundedDyadicGaussian
    {lattice : DyadicOutputLattice}
    (algorithm : PMF lattice.Output)
    (law : RoundedDyadicGaussianLaw lattice) : Prop where
  apply_eq_outputMass : ∀ y, algorithm y = law.outputMass y

/-- Convenient alias for the f32 instantiation. -/
abbrev RoundedF32GaussianLaw : Type 1 :=
  RoundedDyadicGaussianLaw extF32Lattice

end

end RoundedGaussian
end SLang
