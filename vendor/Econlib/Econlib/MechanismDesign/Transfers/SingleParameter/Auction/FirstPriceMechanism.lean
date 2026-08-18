/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Achievable
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPrice

/-!
# Symmetric IID auctions: The first-price auction mechanism (direct representation)

The **first-price auction in its direct (reduced) representation** as an `AuctionMechanism`: A
value-report mechanism whose payment rule already applies the symmetric equilibrium bid
`firstPriceBid` to the report (Myerson 1981). The unit goes to the highest-value bidder, and the
winner pays `firstPriceBid` of its reported value.

Incentive compatibility of the direct mechanism reduces to the best-response property of the
equilibrium bid: A bidder's reduced report-utility is the mimicry payoff `firstPriceInterimUtil`,
so `firstPriceBid_isBestResponse` delivers `IsBIC`. The lowest type wins with probability zero and
bids its own value, so it earns no rent — the normalization under which revenue equivalence
determines interim payments.

## Main definitions

* `AuctionEnv.firstPriceMechanism` — `highestValueAlloc` paired with pay-your-bid payments.

## Main statements

* `AuctionEnv.firstPriceMechanism_interimPay` — interim payment factorizes as `b(t) · F(t)^{n-1}`.
* `AuctionEnv.firstPriceMechanism_reportUtil` — the reduced report-utility is the mimicry payoff.
* `AuctionEnv.firstPriceMechanism_isBIC` — the first-price auction is Bayesian incentive compatible.
* `AuctionEnv.firstPriceMechanism_interimUtil_θlo` — the lowest type earns no rent.

## Notes

This is not the indirect bid game. That the schedule `b = firstPriceBid` is a Bayes–Nash
equilibrium of the auction in which bidders choose arbitrary bids — not value reports — is proved
in `FirstPriceGame.lean` (`firstPriceBid_isEquilibriumBid`), where this direct mechanism is
recovered as that game played truthfully through `b` (`firstPriceMechanism_eq_equilibriumPayoff`).
The ex-post allocation is the shared `highestValueAlloc` (see `Achievable.lean`): The winner is the
value-maximizer and the unit is never withheld (the first-price auction has no reserve), with
order-statistic reduced form `F(t)^{n-1}` at every type.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, first-price, mechanism, incentive compatibility, revenue equivalence
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionEnv

variable (A : AuctionEnv)

/-- The **first-price auction mechanism** (direct representation): The highest-value bidder wins
and pays `firstPriceBid` of its reported value; losers pay nothing. The indirect bid game and its
Bayes–Nash equilibrium are in `FirstPriceGame.lean`. -/
def firstPriceMechanism : AuctionMechanism A where
  alloc := A.highestValueAlloc
  pay θ i := A.base.firstPriceBid A.n (θ i) * A.highestValueAlloc.x θ i
  pay_measurable i :=
    ((A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply i)).mul
      (A.highestValueAlloc.measurable i)
  pay_integrable i := by
    -- The bid is bounded on the type interval (`θlo ≤ b(t) ≤ t ≤ θhi`), so the bid factor is
    -- integrable; the allocation factor is bounded by one.
    have hb_bound : ∀ t ∈ Icc A.base.θlo A.base.θhi,
        |A.base.firstPriceBid A.n t| ≤ max |A.base.θlo| |A.base.θhi| := by
      intro t ht
      rw [abs_le]
      constructor
      · calc -(max |A.base.θlo| |A.base.θhi|)
            ≤ -|A.base.θlo| := neg_le_neg (le_max_left _ _)
          _ ≤ A.base.θlo := neg_abs_le _
          _ ≤ A.base.firstPriceBid A.n t := A.base.θlo_le_firstPriceBid A.n ht
      · calc A.base.firstPriceBid A.n t
            ≤ t := A.base.firstPriceBid_le_self A.n ht
          _ ≤ A.base.θhi := ht.2
          _ ≤ |A.base.θhi| := le_abs_self _
          _ ≤ max |A.base.θlo| |A.base.θhi| := le_max_right _ _
    have hb_int : Integrable (fun θ : A.Profile => A.base.firstPriceBid A.n (θ i)) A.jointLaw :=
      A.integrable_comp_eval (A.base.firstPriceBid_measurable A.n) hb_bound i
    have hmul : Integrable
        (fun θ : A.Profile => A.highestValueAlloc.x θ i * A.base.firstPriceBid A.n (θ i))
        A.jointLaw :=
      hb_int.bdd_mul (f := fun θ => A.highestValueAlloc.x θ i) (c := 1)
        (A.highestValueAlloc.measurable i).aestronglyMeasurable
        (ae_of_all _ fun θ => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith [A.highestValueAlloc.nonneg θ i], A.highestValueAlloc.le_one θ i⟩)
    exact hmul.congr (ae_of_all _ fun θ => mul_comm _ _)
  pay_measurable_update i t := by
    -- After splicing, the own-bid factor is the constant `b(t)` (the spliced report equals `t`),
    -- so the integrand is `const · (spliced allocation)`, and the spliced allocation is measurable.
    have heq : (fun θ : A.Profile =>
          A.base.firstPriceBid A.n ((update θ i t) i) * A.highestValueAlloc.x (update θ i t) i)
        = fun θ : A.Profile =>
          A.base.firstPriceBid A.n t * A.highestValueAlloc.x (update θ i t) i := by
      funext θ; rw [update_self]
    rw [heq]
    exact measurable_const.mul (A.highestValueAlloc.measurable_interim_integrand i t)
  pay_integrable_update i t := by
    -- The spliced own-bid factor is the constant `b(t)`; the spliced allocation is bounded in
    -- `[0, 1]` and integrable, so the product is integrable (constant times integrable).
    have heq : (fun θ : A.Profile =>
          A.base.firstPriceBid A.n ((update θ i t) i) * A.highestValueAlloc.x (update θ i t) i)
        = fun θ : A.Profile =>
          A.base.firstPriceBid A.n t * A.highestValueAlloc.x (update θ i t) i := by
      funext θ; rw [update_self]
    rw [heq]
    exact (A.highestValueAlloc.integrable_interim_integrand i t).const_mul _

@[simp] lemma firstPriceMechanism_alloc : A.firstPriceMechanism.alloc = A.highestValueAlloc := rfl

@[simp] lemma firstPriceMechanism_pay (θ : A.Profile) (i : Fin A.n) :
    A.firstPriceMechanism.pay θ i
      = A.base.firstPriceBid A.n (θ i) * A.highestValueAlloc.x θ i := rfl

/-- **The interim payment factorizes**: Own bid times own interim winning probability,
`b(t) · F(t)^{n-1}`. -/
lemma firstPriceMechanism_interimPay (i : Fin A.n) (t : ℝ) :
    A.firstPriceMechanism.interimPay i t
      = A.base.firstPriceBid A.n t * (A.base.dist.cdf t) ^ (A.n - 1) := by
  rw [AuctionMechanism.interimPay_def]
  have hpt : ∀ θ : A.Profile, A.firstPriceMechanism.pay (update θ i t) i
      = A.base.firstPriceBid A.n t * A.highestValueAlloc.x (update θ i t) i := by
    intro θ; rw [firstPriceMechanism_pay, update_self]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    ← ExPostAlloc.interimAlloc_def, highestValueAlloc_interimAlloc]

/-- **The reduced report-utility is the mimicry payoff.** A type-`θ` bidder reporting `r` to the
first-price mechanism gets exactly `firstPriceInterimUtil n θ r = (θ − b(r)) · F(r)^{n-1}`. -/
lemma firstPriceMechanism_reportUtil (i : Fin A.n) (θ r : ℝ) :
    (A.firstPriceMechanism.reducedMechanism i).reportUtil θ r
      = A.base.firstPriceInterimUtil A.n θ r := by
  simp only [DirectMechanism.reportUtil_def, DirectMechanism.x_def,
    AuctionMechanism.reducedMechanism, firstPriceMechanism_alloc,
    ExPostAlloc.reducedAlloc_x, highestValueAlloc_interimAlloc,
    firstPriceMechanism_interimPay, ScreeningEnv.firstPriceInterimUtil]
  ring

/-- **The first-price auction is Bayesian incentive compatible.** Away from the lowest type this is
the best-response property of the equilibrium bid (`firstPriceBid_isBestResponse`); the lowest type
wins with probability zero against any report priced at `b ≥ θlo`, so no misreport is profitable
there either. -/
theorem firstPriceMechanism_isBIC (hn : 2 ≤ A.n) : A.firstPriceMechanism.IsBIC := by
  intro i θ hθ r hr
  rw [← DirectMechanism.reportUtil_self, firstPriceMechanism_reportUtil,
    firstPriceMechanism_reportUtil]
  rcases eq_or_lt_of_le hθ.1 with hlo | hlo
  · -- Lowest type: every report yields a nonpositive payoff, and the truthful payoff is `0`.
    rw [← hlo]
    have hb := A.base.θlo_le_firstPriceBid A.n hr
    have hF : (0:ℝ) ≤ A.base.dist.cdf r ^ (A.n - 1) :=
      pow_nonneg (A.base.dist.cdf_nonneg r) _
    have hr_nonpos : A.base.firstPriceInterimUtil A.n A.base.θlo r ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨by linarith, hF⟩)
    have hself : A.base.firstPriceInterimUtil A.n A.base.θlo A.base.θlo = 0 := by
      simp [ScreeningEnv.firstPriceInterimUtil]
    rw [hself]
    exact hr_nonpos
  · exact A.base.firstPriceBid_isBestResponse A.n hn ⟨hlo, hθ.2⟩ hr

/-- **The lowest type earns no rent**: It wins with probability zero and bids its own value, the
normalization under which revenue equivalence determines the first-price interim payments. -/
lemma firstPriceMechanism_interimUtil_θlo (i : Fin A.n) :
    (A.firstPriceMechanism.reducedMechanism i).interimUtil A.base.θlo = 0 := by
  rw [← DirectMechanism.reportUtil_self, firstPriceMechanism_reportUtil]
  simp [ScreeningEnv.firstPriceInterimUtil]

end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
