import Mathlib.Data.Nat.Log

/-!
# Counted-loop core of the mechanism runtime claim

This file gives an executable, unit-cost accounting model for Proposition
`prop:mechanism_runtime`.  It does not pretend to verify a particular heap or
random-number-generator implementation.  Instead it makes the cost model in
the paper explicit: a scan charges once per eligible bidder, a bounded heap
update charges at most `ceil(log₂(K+1))`, and the wrapper performs a constant
amount of work per report.
-/

namespace SmoothingCliff.Mechanism

/-- Cost of executing `rounds` iterations that each charge `unitCost`. -/
def repeatCost (unitCost : ℕ) : ℕ → ℕ
  | 0 => 0
  | rounds + 1 => unitCost + repeatCost unitCost rounds

@[simp]
theorem repeatCost_zero (unitCost : ℕ) : repeatCost unitCost 0 = 0 := rfl

@[simp]
theorem repeatCost_succ (unitCost rounds : ℕ) :
    repeatCost unitCost (rounds + 1) =
      unitCost + repeatCost unitCost rounds := rfl

/-- A counted loop has exactly the expected product cost. -/
theorem repeatCost_eq_mul (unitCost rounds : ℕ) :
    repeatCost unitCost rounds = rounds * unitCost := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      simp [repeatCost, ih, Nat.succ_mul, Nat.add_comm]

/-- The direct sequential sampler scans at most `n` agents in each of `K`
selection rounds. -/
def directSequentialSamplerCost (n K : ℕ) : ℕ := repeatCost n K

/-- Exact counted-loop form of the paper's `O(nK)` direct-sampler bound. -/
theorem directSequentialSamplerCost_eq (n K : ℕ) :
    directSequentialSamplerCost n K = n * K := by
  rw [directSequentialSamplerCost, repeatCost_eq_mul]
  exact Nat.mul_comm K n

/-- Worst-case comparison depth for a size-`K` binary heap.  The `K+1`
convention also makes the empty-heap case total. -/
def heapUpdateDepth (K : ℕ) : ℕ := Nat.clog 2 (K + 1)

/-- One Gumbel key plus one bounded-heap update per eligible bidder. -/
def gumbelTopKHeapCost (n K : ℕ) : ℕ :=
  repeatCost (1 + heapUpdateDepth K) n

/-- Sorting the retained at-most-`K` keys by a comparison sort. -/
def retainedKeySortCost (K : ℕ) : ℕ :=
  repeatCost (heapUpdateDepth K) K

/-- Perturb-and-select cost when the retained keys are also sorted. -/
def gumbelTopKSortedCost (n K : ℕ) : ℕ :=
  gumbelTopKHeapCost n K + retainedKeySortCost K

/-- Exact counted-loop form of the paper's `O(n log K)` heap statement. -/
theorem gumbelTopKHeapCost_eq (n K : ℕ) :
    gumbelTopKHeapCost n K =
      n * (1 + Nat.clog 2 (K + 1)) := by
  simp [gumbelTopKHeapCost, heapUpdateDepth, repeatCost_eq_mul]

/-- The optional retained-key sort contributes the displayed
`K ceil(log₂(K+1))` comparisons. -/
theorem gumbelTopKSortedCost_eq (n K : ℕ) :
    gumbelTopKSortedCost n K =
      n * (1 + Nat.clog 2 (K + 1)) +
        K * Nat.clog 2 (K + 1) := by
  simp [gumbelTopKSortedCost, gumbelTopKHeapCost, retainedKeySortCost,
    heapUpdateDepth, repeatCost_eq_mul]

/-- A concrete two-unit-per-report model for constructing one resampling
object and updating one realized-allocation estimator. -/
def singleCallWrapperCost (n : ℕ) : ℕ := repeatCost 2 n

/-- Exact counted-loop form of the wrapper's linear-work statement. -/
theorem singleCallWrapperCost_eq (n : ℕ) :
    singleCallWrapperCost n = 2 * n := by
  rw [singleCallWrapperCost, repeatCost_eq_mul]
  exact Nat.mul_comm n 2

/-- The three operation counts collected in one kernel-checked certificate. -/
theorem mechanismRuntimeCostCertificate (n K : ℕ) :
    directSequentialSamplerCost n K = n * K ∧
    gumbelTopKHeapCost n K = n * (1 + Nat.clog 2 (K + 1)) ∧
    gumbelTopKSortedCost n K =
      n * (1 + Nat.clog 2 (K + 1)) + K * Nat.clog 2 (K + 1) ∧
    singleCallWrapperCost n = 2 * n := by
  exact ⟨directSequentialSamplerCost_eq n K,
    gumbelTopKHeapCost_eq n K,
    gumbelTopKSortedCost_eq n K,
    singleCallWrapperCost_eq n⟩

end SmoothingCliff.Mechanism
