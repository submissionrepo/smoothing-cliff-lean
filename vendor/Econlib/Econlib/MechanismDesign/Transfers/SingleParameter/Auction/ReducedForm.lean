/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Environment

/-!
# Symmetric IID auctions: Reduced-form bridge

The **Myerson 1981 reduction** of a multi-agent auction to `n` independent single-agent screening
problems. The key identity is that an expected ex-post quantity equals the expectation of its
reduced form: Averaging bidder `i`'s ex-post allocation `x θ i` over the full IID profile equals
averaging the interim allocation `interimAlloc X i` over bidder `i`'s own type.

## Main statements

* `ExPostAlloc.expected_interimAlloc_eq` — the ex-post → interim bridge identity.

## Notes

The bridge runs ex-post → interim only; there is no claim that an arbitrary interim allocation is
implementable ex-post (that direction is Border's theorem).

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, reduced form, interim allocation, Myerson
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ExPostAlloc

variable {A : AuctionEnv} (X : ExPostAlloc A)

/-- Each bidder's ex-post allocation is integrable against the joint law (bounded measurable on a
probability measure). -/
lemma integrable_x (i : Fin A.n) : Integrable (fun θ => X.x θ i) A.jointLaw := by
  refine ⟨(X.measurable i).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ fun θ => ?_)⟩
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [X.nonneg θ i], X.le_one θ i⟩

/-- **Ex-post → interim bridge.** The expected ex-post allocation to bidder `i` (averaged over the
whole IID profile) equals the expectation of `i`'s reduced-form interim allocation over its own
type. -/
theorem expected_interimAlloc_eq (i : Fin A.n) :
    ∫ θ, X.x θ i ∂A.jointLaw = A.base.dist.expect (X.interimAlloc i) := by
  have hreduce := ContDist.integral_piMeasure_reduce (d := A.base.dist) (n := A.n) i
    (h := fun θ => X.x θ i) (X.integrable_x i)
  rw [A.base.dist.expect_eq_measure_integral]
  simp only [AuctionEnv.jointLaw_def, ExPostAlloc.interimAlloc_def] at hreduce ⊢
  exact hreduce

end ExPostAlloc

end Econlib.MechanismDesign.Transfers.SingleParameter
