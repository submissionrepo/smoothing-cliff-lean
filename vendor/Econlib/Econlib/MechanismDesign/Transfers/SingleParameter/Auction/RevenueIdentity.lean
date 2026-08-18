/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Mechanism
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity

/-!
# Symmetric IID auctions: The revenue identity

The auction analog of Myerson's revenue identity. Expected total revenue equals expected total
**virtual surplus**:

`𝔼_θ[∑ᵢ pay θ i] = ∑ᵢ 𝔼[ψ(θᵢ) · x̄ᵢ(θᵢ)]`,

where `x̄ᵢ` is bidder `i`'s reduced-form interim allocation and `ψ` the shared virtual value.

## Main statements

* `AuctionMechanism.expected_interimPay_eq` — bidder `i`'s expected ex-post payment equals the
  expectation of its reduced-form interim payment.
* `AuctionMechanism.expected_interimPay_eq_virtual_surplus` — under BIC and zero lowest-type rent,
  each bidder's expected interim payment equals its expected virtual surplus.
* `AuctionMechanism.expected_revenue_eq_virtual_surplus` — total expected revenue equals total
  expected virtual surplus.
* `AuctionMechanism.expected_revenue_le_virtual_surplus` — for every individually rational BIC
  auction, total expected revenue is at most total expected virtual surplus (no zero-rent
  normalization).

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, revenue identity, virtual surplus, myerson, mechanism design
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionMechanism

variable {A : AuctionEnv} (M : AuctionMechanism A)

/-- **Ex-post → interim payment bridge.** Bidder `i`'s expected ex-post payment equals the
expectation of its reduced-form interim payment. -/
theorem expected_interimPay_eq (i : Fin A.n) :
    ∫ θ, M.pay θ i ∂A.jointLaw = A.base.dist.expect (M.interimPay i) := by
  have hreduce := ContDist.integral_piMeasure_reduce (d := A.base.dist) (n := A.n) i
    (h := fun θ => M.pay θ i) (M.pay_integrable i)
  rw [A.base.dist.expect_eq_measure_integral]
  simpa only [AuctionEnv.jointLaw_def, AuctionMechanism.interimPay_def] using hreduce

/-- **Per-bidder revenue identity.** Under incentive compatibility and a normalized lowest-type
rent, each bidder's expected interim payment equals its expected virtual surplus. -/
theorem expected_interimPay_eq_virtual_surplus (hbic : M.IsBIC)
    (hU0 : ∀ i, (M.reducedMechanism i).interimUtil A.base.θlo = 0) (i : Fin A.n) :
    A.base.dist.expect (M.interimPay i)
      = A.base.dist.expect (fun t => A.base.virtualValue t * M.alloc.interimAlloc i t) := by
  simpa only [reducedMechanism_p, reducedMechanism_x] using
    (M.reducedMechanism i).expected_revenue_eq_virtual_surplus (hbic i) (hU0 i)

/-- **Auction revenue identity.** Total expected revenue equals total expected virtual surplus:
`𝔼[∑ᵢ payᵢ] = ∑ᵢ 𝔼[ψ · x̄ᵢ]`. The objective the revenue-optimal auction maximizes. -/
theorem expected_revenue_eq_virtual_surplus (hbic : M.IsBIC)
    (hU0 : ∀ i, (M.reducedMechanism i).interimUtil A.base.θlo = 0) :
    (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      = ∑ i, A.base.dist.expect (fun t => A.base.virtualValue t * M.alloc.interimAlloc i t) := by
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => M.pay_integrable i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [M.expected_interimPay_eq i, M.expected_interimPay_eq_virtual_surplus hbic hU0 i]

/-- **Per-bidder revenue bound.** Under incentive compatibility and individual rationality, each
bidder's expected interim payment is at most its expected virtual surplus. -/
theorem expected_interimPay_le_virtual_surplus (hbic : M.IsBIC) (hbir : M.IsBIR) (i : Fin A.n) :
    A.base.dist.expect (M.interimPay i)
      ≤ A.base.dist.expect (fun t => A.base.virtualValue t * M.alloc.interimAlloc i t) := by
  simpa only [reducedMechanism_p, reducedMechanism_x] using
    (M.reducedMechanism i).expected_revenue_le_virtual_surplus (hbic i) (hbir i)

/-- **Auction revenue bound.** Total expected revenue is at most total expected virtual surplus:
`𝔼[∑ᵢ payᵢ] ≤ ∑ᵢ 𝔼[ψ · x̄ᵢ]`. Unlike `expected_revenue_eq_virtual_surplus`, this needs no zero-rent
normalization: Individual rationality alone (`U_i(θlo) ≥ 0`) bounds the revenue identity's slack,
so the inequality holds for every individually rational BIC auction. -/
theorem expected_revenue_le_virtual_surplus (hbic : M.IsBIC) (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      ≤ ∑ i, A.base.dist.expect (fun t => A.base.virtualValue t * M.alloc.interimAlloc i t) := by
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => M.pay_integrable i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [M.expected_interimPay_eq i]
  exact M.expected_interimPay_le_virtual_surplus hbic hbir i

end AuctionMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
