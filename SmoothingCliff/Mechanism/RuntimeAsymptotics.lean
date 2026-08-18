import SmoothingCliff.Mechanism.Runtime
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Formal asymptotic form of the mechanism runtime certificate

`Runtime.lean` proves exact operation counts in the paper's unit-cost model.
This file connects those exact counts to Mathlib's `IsBigO` relation.  The
comparison functions retain the discrete `Nat.clog 2 (K + 1)` used by the
heap model, so the statements are total at `K = 0` and do not hide an edge
case behind informal logarithmic notation.
-/

namespace SmoothingCliff.Mechanism

open Asymptotics Filter

/-- The direct sequential sampler has the formal `O(nK)` bound, uniformly
along any filter on pairs `(n,K)`; in fact the two functions are equal. -/
theorem directSequentialSamplerCost_isBigO
    (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ => (directSequentialSamplerCost p.1 p.2 : ℝ))
      =O[l] (fun p : ℕ × ℕ => ((p.1 * p.2 : ℕ) : ℝ)) := by
  apply Filter.EventuallyEq.isBigO
  exact Filter.Eventually.of_forall fun p => by
    simpa using congrArg (fun m : ℕ => (m : ℝ))
      (directSequentialSamplerCost_eq p.1 p.2)

/-- The size-`K` heap scan has the formal
`O(n (1 + ceil(log₂(K+1))))` bound; again the count is exact. -/
theorem gumbelTopKHeapCost_isBigO
    (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ => (gumbelTopKHeapCost p.1 p.2 : ℝ))
      =O[l] (fun p : ℕ × ℕ =>
        ((p.1 * (1 + Nat.clog 2 (p.2 + 1)) : ℕ) : ℝ)) := by
  apply Filter.EventuallyEq.isBigO
  exact Filter.Eventually.of_forall fun p => by
    simpa using congrArg (fun m : ℕ => (m : ℝ))
      (gumbelTopKHeapCost_eq p.1 p.2)

/-- Retaining the optional sorting term gives the exact comparison function
`n(1+ceil(log₂(K+1))) + K ceil(log₂(K+1))`. -/
theorem gumbelTopKSortedCost_isBigO
    (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ => (gumbelTopKSortedCost p.1 p.2 : ℝ))
      =O[l] (fun p : ℕ × ℕ =>
        ((p.1 * (1 + Nat.clog 2 (p.2 + 1)) +
          p.2 * Nat.clog 2 (p.2 + 1) : ℕ) : ℝ)) := by
  apply Filter.EventuallyEq.isBigO
  exact Filter.Eventually.of_forall fun p => by
    simpa using congrArg (fun m : ℕ => (m : ℝ))
      (gumbelTopKSortedCost_eq p.1 p.2)

/-- One resampling object and one estimator update per report are formally
linear in the number of reports. -/
theorem singleCallWrapperCost_isBigO (l : Filter ℕ) :
    (fun n : ℕ => (singleCallWrapperCost n : ℝ))
      =O[l] (fun n : ℕ => (n : ℝ)) := by
  rw [Asymptotics.isBigO_iff_isBigOWith]
  refine ⟨2, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  exact Filter.Eventually.of_forall fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      singleCallWrapperCost_eq]
    norm_num

/-- The paper's four runtime clauses collected using Mathlib's actual
asymptotic relation rather than only prose `O(·)` notation. -/
theorem mechanismRuntimeAsymptoticCertificate :
    (fun p : ℕ × ℕ => (directSequentialSamplerCost p.1 p.2 : ℝ))
        =O[atTop] (fun p : ℕ × ℕ => ((p.1 * p.2 : ℕ) : ℝ)) ∧
    (fun p : ℕ × ℕ => (gumbelTopKHeapCost p.1 p.2 : ℝ))
        =O[atTop] (fun p : ℕ × ℕ =>
          ((p.1 * (1 + Nat.clog 2 (p.2 + 1)) : ℕ) : ℝ)) ∧
    (fun p : ℕ × ℕ => (gumbelTopKSortedCost p.1 p.2 : ℝ))
        =O[atTop] (fun p : ℕ × ℕ =>
          ((p.1 * (1 + Nat.clog 2 (p.2 + 1)) +
            p.2 * Nat.clog 2 (p.2 + 1) : ℕ) : ℝ)) ∧
    (fun n : ℕ => (singleCallWrapperCost n : ℝ))
        =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  exact ⟨directSequentialSamplerCost_isBigO atTop,
    gumbelTopKHeapCost_isBigO atTop,
    gumbelTopKSortedCost_isBigO atTop,
    singleCallWrapperCost_isBigO atTop⟩

end SmoothingCliff.Mechanism
