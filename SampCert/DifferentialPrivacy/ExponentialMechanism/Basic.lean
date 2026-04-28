/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.ExponentialMechanism.ExponentialMechanism_DPBridge
import SampCert.DifferentialPrivacy.ExponentialMechanism.ExponentialMechanism_zCDP

/-!
# Facade module for the Exponential Mechanism formalization.

## Algorithm

The Exponential Mechanism (`exponentialMechSLang`) selects a candidate from a finite set
by sampling proportional to `exp(-gap * ε₁/ε₂)`, where `gap` is the score distance to
the optimal candidate.

## Paper-to-code map

### Implementation
- SLang do-notation loop: `Code.exponentialMechSLang`
- Rejection-sampling primitive: `Code.expMechLoop`

### PMF characterization (Theorem 3.1 / softmax formula)
- Loop body PMF: `PMF.expMechPMF_apply`
- Normalization: `PMF.expMechLoop_normalizes`
- Full mechanism PMF: `PMF.exponentialMechSLang_apply`
  ```
  M(q)(r) = exp(-gap(q,r)·ε₁/ε₂) / ∑ᵢ exp(-gap(q,i)·ε₁/ε₂)
  ```

### Pure ε-DP (Theorem A.3 / Appendix)
- Pointwise range-distance privacy: `Privacy.exponentialMechSLang_range_privacy`
- Dataset-level DP singleton: `ExponentialMechanism_DPBridge.exponentialMechSLang_DP_singleton`
- Pure DP from range sensitivity: `ExponentialMechanism_DPBridge.exponentialMechSLang_pureDP_of_rangeSensitive`

### ρ-zCDP (Theorem A.3 / Appendix, ρ = Δ²ε₁²/(2ε₂²))
- Bounded-range property: `ExponentialMechanism_zCDP.exponentialMechSLang_BoundedRange`
- Rényi divergence bound: `ExponentialMechanism_zCDP.exponentialMechSLang_zCDP_renyi`
  (one `sorry` remains for the Hoeffding/BR→zCDP conversion)

## Main entry theorems

### Pure DP
- `ExponentialMechanism.SLang.exponentialMechSLang_pureDP_of_rangeSensitive`

### Bounded-range (intermediate)
- `ExponentialMechanism.SLang.exponentialMechSLang_BoundedRange`

### zCDP (Rényi divergence formulation)
- `ExponentialMechanism.SLang.exponentialMechSLang_zCDP_renyi`
-/
