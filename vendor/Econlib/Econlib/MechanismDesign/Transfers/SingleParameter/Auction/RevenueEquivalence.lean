/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Mechanism
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueEquivalence

/-!
# Symmetric IID auctions: Revenue equivalence

The auction **revenue equivalence theorem** (Myerson 1981; Riley and Samuelson 1981): Two Bayesian
incentive-compatible auction mechanisms that give every bidder the same interim allocation and give
every bidder's lowest type the same interim utility charge identical interim payments — hence raise
the same expected revenue.

This is the format-independence behind, e.g., first-price and second-price auctions raising equal
expected revenue in the symmetric IPV model: Both reduce to the same monotone interim allocation
with zero rent at the lowest type.

## Main statements

* `AuctionMechanism.revenue_equivalence`: Auction-level revenue equivalence theorem.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).
* Riley, John G., and William F. Samuelson. 1981. “Optimal Auctions.” *The American Economic
  Review* 71 (3): 381–92.

## Tags

auction, revenue equivalence, incentive compatibility, bayesian incentive compatible
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionMechanism

variable {A : AuctionEnv}

/-- **Auction revenue equivalence.** If two auction mechanisms are incentive compatible, give every
bidder the same interim allocation on the type interval, and give every bidder's lowest type the
same interim utility, then they charge identical interim payments to every bidder throughout the
interval. -/
theorem revenue_equivalence {M₁ M₂ : AuctionMechanism A} (h₁ : M₁.IsBIC) (h₂ : M₂.IsBIC)
    (hx : ∀ (i : Fin A.n), ∀ θ ∈ A.base.types,
      M₁.alloc.interimAlloc i θ = M₂.alloc.interimAlloc i θ)
    (hU0 : ∀ (i : Fin A.n),
      (M₁.reducedMechanism i).interimUtil A.base.θlo
        = (M₂.reducedMechanism i).interimUtil A.base.θlo)
    (i : Fin A.n) {θ : ℝ} (hθ : θ ∈ A.base.types) :
    M₁.interimPay i θ = M₂.interimPay i θ :=
  SingleParameter.revenue_equivalence (h₁ i) (h₂ i) (fun s hs => hx i s hs) (hU0 i) hθ

end AuctionMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
