/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvin Ye, Michael Shoemate
-/
import SampCert.DifferentialPrivacy.PermuteAndFlip.Mechanism.Core
import SampCert.Foundations.Until

noncomputable section

open scoped Classical
open PMF

namespace SLang
namespace ExponentialMechanism

open PermuteAndFlip

/--
PMF version of the exponential mechanism loop body.
Samples `i` uniformly from `Fin n.succ`, then draws from `exactCoinPMF (gap q i * ε₁) ε₂`.
-/
def expMechPMF (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    PMF (Fin n.succ × Bool) := do
  let i ← PMF.uniformOfFintype (Fin n.succ)
  let b ← exactCoinPMF (gap q i * ε₁) ε₂
  return (i, b)

/--
SLang loop body for the exponential mechanism rejection sampler.
Samples `i` uniformly, accepts with probability `exp(-gap(q, i) · ε₁/ε₂)`.
-/
def expMechLoop (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    SLang (Fin n.succ × Bool) := do
  let i ← ((PMF.uniformOfFintype (Fin n.succ)) : SLang (Fin n.succ))
  let b ← BernoulliExpNegSample (gap q i * ε₁) ε₂
  return (i, b)

/-- The SLang loop body equals the PMF loop body pointwise. -/
theorem expMechLoop_eq_expMechPMF (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    expMechLoop n q ε₁ ε₂ = expMechPMF n q ε₁ ε₂ := by
  ext ⟨r, b⟩
  simp [expMechLoop, expMechPMF, bernoulliExpNegSample_eq_exactCoinPMF]

/--
The exponential mechanism (Algorithm 2): rejection-sample until acceptance, return the candidate.
-/
def exponentialMechSLang (n : CandidateCount) (q : Scores n) (ε₁ : ℕ) (ε₂ : ℕ+) :
    SLang (Fin n.succ) := do
  let r ← probUntil (expMechLoop n q ε₁ ε₂) (fun x => x.2)
  return r.1

end ExponentialMechanism
end SLang
