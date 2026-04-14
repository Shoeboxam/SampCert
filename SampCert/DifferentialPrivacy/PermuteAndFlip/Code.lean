import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Uniform.Code

/-!
# `PermuteAndFlipSample` Implementation

## Implementation note
The identifier `PermuteAndFlipSample` violates our naming scheme, but this is
currently necessary for extraction.
-/

noncomputable section

namespace SLang

/--
`2^n`, implemented as an extraction-friendly recursive sampler wrapper.
-/
def PermuteAndFlipPow2 (n : ℕ) : SLang ℕ := do
  if h : n = 0 then
    return 1
  else
    let p ← PermuteAndFlipPow2 (n - 1)
    return 2 * p
termination_by n
decreasing_by
  exact Nat.sub_lt (Nat.pos_of_ne_zero h) (by simp)

/--
Bitmask with the low `n + 1` bits set.
-/
def PermuteAndFlipFullMask (n : PermuteAndFlip.CandidateCount) : SLang ℕ := do
  if h : n = 0 then
    return 1
  else
    let mask ← PermuteAndFlipFullMask (n - 1)
    return 2 * mask + 1
termination_by n
decreasing_by
  exact Nat.sub_lt (Nat.pos_of_ne_zero h) (by simp)

/--
Test whether bit `i` is active in `mask`.
-/
def PermuteAndFlipHasBit (mask i : ℕ) : SLang Bool := do
  let p ← PermuteAndFlipPow2 i
  return (mask / p) % 2 = 1

/--
Clear bit `i` from `mask`.
-/
def PermuteAndFlipClearBit {n : PermuteAndFlip.CandidateCount}
    (mask : ℕ) (i : Fin n.succ) : SLang ℕ := do
  let p ← PermuteAndFlipPow2 i
  let active ← PermuteAndFlipHasBit mask i
  if active then
    return mask - p
  else
    return mask

/--
State transition for the `k`-th-active scan loop.
-/
def PermuteAndFlipKthActiveLoop (n : PermuteAndFlip.CandidateCount) (mask : ℕ)
    (state : Bool × (ℕ × (Fin n.succ × ℕ))) :
    SLang (Bool × (ℕ × (Fin n.succ × ℕ))) := do
  let k := state.2.1
  let found := state.2.2.1
  let rem := state.2.2.2
  if hrem : rem = 0 then
    return (true, (k, (found, rem)))
  else
    let curr := n.succ - rem
    let i : Fin n.succ := ⟨curr, Nat.sub_lt (Nat.succ_pos _) (Nat.pos_of_ne_zero hrem)⟩
    let active ← PermuteAndFlipHasBit mask curr
    if active then
      if k = 0 then
        return (true, (k, (i, rem)))
      else
        return (false, (k - 1, (found, rem - 1)))
    else
      return (false, (k, (found, rem - 1)))

/--
Select the `k`-th active candidate from the current active-set mask.
-/
def PermuteAndFlipKthActive (n : PermuteAndFlip.CandidateCount)
    (mask k : ℕ) : SLang (Fin n.succ) := do
  let st ← probWhile
    (fun state : Bool × (ℕ × (Fin n.succ × ℕ)) => ¬ state.1)
    (PermuteAndFlipKthActiveLoop n mask)
    (false, (k, (default, n.succ)))
  return st.2.2.1

/--
Extraction-friendly gap wrapper for permute-and-flip.
-/
def PermuteAndFlipGapLoop (n : PermuteAndFlip.CandidateCount)
    (q : PermuteAndFlip.Scores n) (target : Fin n.succ)
    (state : ℕ × ℕ) : SLang (ℕ × ℕ) := do
  let best := state.1
  let rem := state.2
  if hrem : rem = 0 then
    return state
  else
    let curr := n.succ - rem
    let i : Fin n.succ := ⟨curr, Nat.sub_lt (Nat.succ_pos _) (Nat.pos_of_ne_zero hrem)⟩
    let cand := q i - q target
    let best' := if best < cand then cand else best
    return (best', rem - 1)

/--
Extraction-friendly gap wrapper for permute-and-flip.
-/
def PermuteAndFlipGap (n : PermuteAndFlip.CandidateCount)
    (q : PermuteAndFlip.Scores n) (target : Fin n.succ) : SLang ℕ := do
  let st ← probWhile
    (fun state : ℕ × ℕ => state.2 ≠ 0)
    (PermuteAndFlipGapLoop n q target)
    (0, n.succ)
  return st.1

/--
Executable sampling loop: choose uniformly among the remaining active candidates,
test the sampled candidate, and stop at the first acceptance.
-/
def PermuteAndFlipSampleLoop (n : PermuteAndFlip.CandidateCount)
    (q : PermuteAndFlip.Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (state : Bool × (Fin n.succ × (ℕ × ℕ))) :
    SLang (Bool × (Fin n.succ × (ℕ × ℕ))) := do
  let result := state.2.1
  let mask := state.2.2.1
  let rem := state.2.2.2
  if hrem : rem = 0 then
    return (true, (result, (mask, rem)))
  else
    let k ← UniformSample ⟨rem, by omega⟩
    let i ← PermuteAndFlipKthActive n mask k
    let g ← PermuteAndFlipGap n q i
    let accept ← BernoulliExpNegSample (g * ε₁) ε₂
    if accept then
      return (true, (i, (mask, rem)))
    else
      let mask' ← PermuteAndFlipClearBit mask i
      return (false, (result, (mask', rem - 1)))

/--
Executable sampling loop wrapper.
-/
def PermuteAndFlipSampleCore (n : PermuteAndFlip.CandidateCount)
    (q : PermuteAndFlip.Scores n) (ε₁ : ℕ) (ε₂ : ℕ+)
    (mask rem : ℕ) : SLang (Fin n.succ) := do
  let st ← probWhile
    (fun state : Bool × (Fin n.succ × (ℕ × ℕ)) => ¬ state.1)
    (PermuteAndFlipSampleLoop n q ε₁ ε₂)
    (false, (default, (mask, rem)))
  return st.2.1

/--
Extraction-friendly executable permute-and-flip mechanism without an explicit
`Equiv.Perm` draw.
-/
def PermuteAndFlipSample (n : PermuteAndFlip.CandidateCount)
    (q : PermuteAndFlip.Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    SLang (Fin n.succ) := do
  let mask ← PermuteAndFlipFullMask n
  PermuteAndFlipSampleCore n q ε₁ ε₂ mask n.succ

end SLang
