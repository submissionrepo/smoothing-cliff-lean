/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPriceMechanism

/-!
# The first-price auction as an indirect game: Equilibrium bidding

This file proves that the symmetric schedule `σ = firstPriceBid` is a **Bayes–Nash equilibrium** of
the indirect **first-price auction** (Vickrey 1961; Riley and Samuelson 1981). The auction has bid
space `ℝ`: Each bidder submits a bid, the highest bid wins (the strictly increasing `firstPriceBid`
makes the highest-value bidder the highest bidder), and the winner pays its own bid. Against rivals
playing `σ`, a type-`θ` bidder submitting bid `b` wins with probability `firstPriceWinProb i b` and
earns `firstPriceDevPayoff i θ b = (θ − b) · firstPriceWinProb i b`. The main theorem proves `σ(θ)`
is a best response against every bid `b ∈ ℝ` — not just the on-path mimicry bids `b(z)`.

## Main definitions

* `AuctionEnv.firstPriceBidProfile` — the equilibrium bid profile `σ ∘ θ` induced by a type profile.
* `AuctionEnv.firstPriceWinProb` — interim winning probability of an arbitrary bid against `σ`.
* `AuctionEnv.firstPriceDevPayoff` — interim (pay-your-bid) payoff of an arbitrary bid against `σ`.
* `AuctionEnv.IsBestBid` — bid optimality: No bid does strictly better for the given type.

## Main statements

* `AuctionEnv.firstPriceBid_isEquilibriumBid` — `σ(θ)` is a best response against every bid: The
  first-price auction's symmetric Bayes–Nash equilibrium.
* `AuctionEnv.firstPriceMechanism_eq_equilibriumPayoff` — the direct mechanism's truthful interim
  utility equals the indirect game's equilibrium interim payoff.

## Notes

This is the equilibrium statement behind `FirstPriceMechanism.lean`, which builds the auction in
its direct (reduced) representation — a value-report mechanism whose payment rule already applies
`firstPriceBid` to the report. That representation is what revenue equivalence consumes; on its own
it does not assert that bidding `b(θ)` is an equilibrium of the game where bidders choose bids,
rather than value reports. The direct mechanism is recovered as this game played truthfully through
`σ` (`firstPriceMechanism_eq_equilibriumPayoff`): Its truthful interim utility is the indirect
game's equilibrium interim payoff.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).
* Riley, John G., and William F. Samuelson. 1981. “Optimal Auctions.” *The American Economic
  Review* 71 (3): 381–92.

## Tags

auction, first-price, bayes-nash equilibrium, indirect mechanism, bid shading
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionEnv

variable (A : AuctionEnv)

/-- The **equilibrium bid profile** induced by a type profile: Every bidder bids the symmetric
schedule `σ = firstPriceBid` of its own value. Bids live in `ℝ`, the same carrier as values. -/
def firstPriceBidProfile (θ : A.Profile) : A.Profile := fun j => A.base.firstPriceBid A.n (θ j)

@[simp] lemma firstPriceBidProfile_apply (θ : A.Profile) (j : Fin A.n) :
    A.firstPriceBidProfile θ j = A.base.firstPriceBid A.n (θ j) := rfl

/-- The **interim winning probability of submitting bid `b`** when every rival bids the equilibrium
schedule `σ`: The highest bid wins (score `exp`, strictly monotone, so highest bid = highest `σ`),
averaged over the rivals' types. The bidder's own type is overwritten by the chosen bid `b`. -/
def firstPriceWinProb (i : Fin A.n) (b : ℝ) : ℝ :=
  ∫ θ, A.highestValueAlloc.x (update (A.firstPriceBidProfile θ) i b) i ∂A.jointLaw

/-- The **interim payoff of submitting bid `b`** for a type-`θ` bidder in the pay-your-bid
first-price auction, when every rival bids the equilibrium schedule `σ`: `(θ − b)` times the chance
of winning. -/
def firstPriceDevPayoff (i : Fin A.n) (θ b : ℝ) : ℝ :=
  (θ - b) * A.firstPriceWinProb i b

lemma firstPriceDevPayoff_def (i : Fin A.n) (θ b : ℝ) :
    A.firstPriceDevPayoff i θ b = (θ - b) * A.firstPriceWinProb i b := rfl

variable {A}

/-- **Order transport.** When all bidders' values lie in the support, applying the strictly
increasing equilibrium schedule `σ` to a profile does not change who wins the highest-bid contest:
The highest `σ`-bid is the highest value. This turns the highest-bid allocation into the
highest-value order statistic on the equilibrium path. -/
lemma isTopBidder_firstPriceBidProfile_iff {ρ : A.Profile} {i : Fin A.n}
    (hρ : ∀ j, ρ j ∈ Icc A.base.θlo A.base.θhi) (hn : 2 ≤ A.n) :
    A.IsTopBidder Real.exp (A.firstPriceBidProfile ρ) i ↔ A.IsTopBidder Real.exp ρ i := by
  have hmono : StrictMonoOn (A.base.firstPriceBid A.n) (Icc A.base.θlo A.base.θhi) :=
    A.base.firstPriceBid_strictMonoOn_Icc A.n hn
  -- `exp` is strictly monotone and `σ` is strictly monotone on the type box, so every score
  -- comparison `exp (σ (ρ j)) ⋚ exp (σ (ρ i))` matches `exp (ρ j) ⋚ exp (ρ i)` pointwise.
  simp only [AuctionEnv.isTopBidder_iff, firstPriceBidProfile_apply, Real.exp_le_exp,
    Real.exp_lt_exp]
  refine and_congr (iff_of_true (Real.exp_pos _).le (Real.exp_pos _).le) (and_congr ?_ ?_)
  · exact forall_congr' fun j => hmono.le_iff_le (hρ j) (hρ i)
  · exact forall_congr' fun j => imp_congr_right fun _ => hmono.lt_iff_lt (hρ j) (hρ i)

variable (A)

/-- **On-path winning probability.** Submitting the bid a type-`z` bidder would (`b(z)`, with
`z ∈ [θlo, θhi]`) wins with the top order-statistic probability `F(z)^{n-1}`: By order transport
the highest-bid event coincides a.s. with the highest-value event, whose interim form is
`F(z)^{n-1}`. -/
lemma firstPriceWinProb_firstPriceBid (hn : 2 ≤ A.n) (i : Fin A.n) {z : ℝ}
    (hz : z ∈ Icc A.base.θlo A.base.θhi) :
    A.firstPriceWinProb i (A.base.firstPriceBid A.n z) = (A.base.dist.cdf z) ^ (A.n - 1) := by
  -- Overwriting bidder `i`'s bid by `σ(z)` is the same as overwriting its *value* by `z` and then
  -- applying `σ` to the whole profile.
  have hupd : ∀ θ : A.Profile,
      update (A.firstPriceBidProfile θ) i (A.base.firstPriceBid A.n z)
        = A.firstPriceBidProfile (update θ i z) := by
    intro θ
    funext j
    by_cases hj : j = i
    · subst hj; rw [update_self, firstPriceBidProfile_apply, update_self]
    · rw [update_of_ne hj, firstPriceBidProfile_apply, firstPriceBidProfile_apply,
        update_of_ne hj]
  -- On the support, order transport turns the highest-*bid* winner indicator into the
  -- highest-*value* one, whose interim integral is the order statistic `F(z) ^ (n-1)`.
  rw [firstPriceWinProb]
  simp only [hupd]
  rw [show (A.base.dist.cdf z) ^ (A.n - 1) = A.highestValueAlloc.interimAlloc i z from
    (A.highestValueAlloc_interimAlloc i z).symm, ExPostAlloc.interimAlloc_def]
  refine integral_congr_ae ?_
  filter_upwards [A.ae_forall_mem_Icc] with θ hθ
  have hmem : ∀ j, (update θ i z) j ∈ Icc A.base.θlo A.base.θhi := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [update_self]; exact hz
    · rw [update_of_ne hj]; exact hθ j
  by_cases htop : A.IsTopBidder Real.exp (update θ i z) i
  · rw [highestValueAlloc_x_of_top ((isTopBidder_firstPriceBidProfile_iff hmem hn).mpr htop),
      highestValueAlloc_x_of_top htop]
  · rw [highestValueAlloc_x_of_not_top
      (fun h => htop ((isTopBidder_firstPriceBidProfile_iff hmem hn).mp h)),
      highestValueAlloc_x_of_not_top htop]

/-- **On-path payoff is the mimicry payoff.** Submitting `b(z)` yields exactly
`firstPriceInterimUtil n θ z = (θ − b(z)) · F(z)^{n-1}`. -/
lemma firstPriceDevPayoff_firstPriceBid (hn : 2 ≤ A.n) (i : Fin A.n) {θ z : ℝ}
    (hz : z ∈ Icc A.base.θlo A.base.θhi) :
    A.firstPriceDevPayoff i θ (A.base.firstPriceBid A.n z)
      = A.base.firstPriceInterimUtil A.n θ z := by
  rw [A.firstPriceDevPayoff_def, A.firstPriceWinProb_firstPriceBid hn i hz,
    ScreeningEnv.firstPriceInterimUtil]

/-- The win-probability integrand `θ ↦ x (update (σ∘θ) i b) i` is measurable: The equilibrium bid
profile is measurable per coordinate, overwriting coordinate `i` by the fixed bid `b` preserves
measurability, and the winner indicator is measurable. -/
lemma measurable_firstPriceWinProb_integrand (i : Fin A.n) (b : ℝ) :
    Measurable (fun θ => A.highestValueAlloc.x (update (A.firstPriceBidProfile θ) i b) i) := by
  have hprofile : Measurable (fun θ : A.Profile => A.firstPriceBidProfile θ) :=
    measurable_pi_lambda _ fun j =>
      (A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply j)
  exact (A.highestValueAlloc.measurable i).comp (measurable_update_left.comp hprofile)

/-- The win-probability integrand is integrable against the joint law: It is measurable and bounded
in `[0, 1]`, and the joint law is a probability measure. -/
lemma integrable_firstPriceWinProb_integrand (i : Fin A.n) (b : ℝ) :
    Integrable (fun θ => A.highestValueAlloc.x (update (A.firstPriceBidProfile θ) i b) i)
      A.jointLaw := by
  refine ⟨(A.measurable_firstPriceWinProb_integrand i b).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ fun θ => ?_)⟩
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [A.highestValueAlloc.nonneg (update (A.firstPriceBidProfile θ) i b) i],
    A.highestValueAlloc.le_one (update (A.firstPriceBidProfile θ) i b) i⟩

/-- The winning probability is nonnegative. -/
lemma firstPriceWinProb_nonneg (i : Fin A.n) (b : ℝ) : 0 ≤ A.firstPriceWinProb i b :=
  integral_nonneg fun _θ => A.highestValueAlloc.nonneg _ i

/-- The winning probability never exceeds `1`. -/
lemma firstPriceWinProb_le_one (i : Fin A.n) (b : ℝ) : A.firstPriceWinProb i b ≤ 1 := by
  calc A.firstPriceWinProb i b
      ≤ ∫ _θ, (1 : ℝ) ∂A.jointLaw :=
        integral_mono (A.integrable_firstPriceWinProb_integrand i b) (integrable_const 1)
          (fun θ => A.highestValueAlloc.le_one (update (A.firstPriceBidProfile θ) i b) i)
    _ = 1 := by simp

/-- **Underbidding never wins.** A bid at or below the lowest type wins with probability zero:
Every rival bids strictly above `θlo` almost surely (its value exceeds `θlo` a.s. and `σ` is
strictly increasing from `σ(θlo) = θlo`). -/
lemma firstPriceWinProb_eq_zero_of_le_θlo (hn : 2 ≤ A.n) (i : Fin A.n) {b : ℝ}
    (hb : b ≤ A.base.θlo) : A.firstPriceWinProb i b = 0 := by
  -- With at least two bidders there is a rival `j₀ ≠ i`.
  haveI : Nontrivial (Fin A.n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  -- The rival's value exceeds `θlo` almost surely: `{θ | θ j₀ ≤ θlo}` is null because its joint-law
  -- measure marginalizes to `F(θlo) = 0`.
  have haej₀ : ∀ᵐ θ ∂A.jointLaw, A.base.θlo < θ j₀ := by
    rw [ae_iff]
    have heq : {θ : A.Profile | ¬ A.base.θlo < θ j₀}
        = Function.eval j₀ ⁻¹' (Iic A.base.θlo) := by
      ext θ; simp only [mem_setOf_eq, not_lt, Set.mem_preimage, Function.eval, Set.mem_Iic]
    rw [heq, ← Measure.map_apply (measurable_pi_apply j₀) measurableSet_Iic,
      A.map_eval_jointLaw j₀]
    haveI : IsProbabilityMeasure A.base.dist.toMeasure := A.base.dist.toMeasure_isProbability
    have htoReal : (A.base.dist.toMeasure (Iic A.base.θlo)).toReal = 0 := by
      rw [A.base.dist.toReal_measure_Iic_eq_cdf, A.base.cdf_θlo_eq_zero]
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h0 | htop
    · exact h0
    · exact absurd htop (measure_ne_top _ _)
  -- For such a profile, bidder `i`'s winning bid `b ≤ θlo` is below the rival's bid
  -- `σ(θ j₀) > θlo`, so `i` is not the top bidder and its indicator vanishes.
  rw [firstPriceWinProb]
  rw [integral_eq_zero_of_ae]
  filter_upwards [haej₀, A.ae_forall_mem_Icc] with θ hθj₀ hθIcc
  refine highestValueAlloc_x_of_not_top (fun htop => ?_)
  obtain ⟨_, hmax, _⟩ := htop
  have hj₀_bid : A.base.θlo < A.base.firstPriceBid A.n (θ j₀) := by
    have := A.base.firstPriceBid_strictMonoOn_Icc A.n hn A.base.θlo_mem_types (hθIcc j₀) hθj₀
    rwa [A.base.firstPriceBid_θlo] at this
  have hmax_j₀ := hmax j₀
  rw [update_of_ne hj₀, firstPriceBidProfile_apply, update_self] at hmax_j₀
  -- `exp` is strictly monotone, so the rival's higher bid contradicts the top-bidder inequality.
  have : b < A.base.firstPriceBid A.n (θ j₀) := lt_of_le_of_lt hb hj₀_bid
  exact absurd (Real.exp_le_exp.mp hmax_j₀) (not_le.mpr this)

/-- **Every on-path bid is attained.** By the intermediate value theorem (the schedule is
continuous and runs from `σ(θlo) = θlo` to `σ(θhi)`), every bid `b ∈ [θlo, b(θhi)]` is `b(z)` for
some type `z ∈ [θlo, θhi]`. -/
-- `hn` is intentionally unused; continuity (the IVT input) holds for every `n`, but the hypothesis
-- is kept for uniformity with the other on-/off-path bid lemmas and the equilibrium theorem.
lemma exists_firstPriceBid_eq (_hn : 2 ≤ A.n) {b : ℝ}
    (hb : b ∈ Icc A.base.θlo (A.base.firstPriceBid A.n A.base.θhi)) :
    ∃ z ∈ Icc A.base.θlo A.base.θhi, A.base.firstPriceBid A.n z = b := by
  -- The schedule is continuous and runs from `σ(θlo) = θlo` to `σ(θhi)`, so the IVT hits every `b`
  -- in between.
  have hsub := intermediate_value_Icc A.base.hθ.le (A.base.firstPriceBid_continuousOn A.n)
  rw [A.base.firstPriceBid_θlo] at hsub
  obtain ⟨z, hz, hzeq⟩ := hsub hb
  exact ⟨z, hz, hzeq⟩

/-- **Bid optimality.** A bid `b` is a best response for a type-`θ` bidder (rivals at `σ`) if no
bid does strictly better. -/
def IsBestBid (i : Fin A.n) (θ b : ℝ) : Prop :=
  ∀ b' : ℝ, A.firstPriceDevPayoff i θ b' ≤ A.firstPriceDevPayoff i θ b

/-- **The equilibrium bid is a best response against every bid.** For a type-`θ` bidder facing
rivals who bid the symmetric schedule `σ = firstPriceBid`, no bid `b ∈ ℝ` beats the bid `b(θ)`.
Hence `σ` is a symmetric Bayes–Nash equilibrium of the indirect first-price auction — the
equilibrium statement that the direct mechanism's `BIC` only encodes in reduced form. This per-type
best-response statement is upgraded to the canonical continuous-type equilibrium predicate
`GameTheory.MeasBayesianGame.IsBNE` in `Auction.FirstPriceBNE` (`firstPriceBid_isBNE`). -/
theorem firstPriceBid_isEquilibriumBid (hn : 2 ≤ A.n) (i : Fin A.n) {θ : ℝ}
    (hθ : θ ∈ Icc A.base.θlo A.base.θhi) :
    A.IsBestBid i θ (A.base.firstPriceBid A.n θ) := by
  have hn1 : A.n - 1 ≠ 0 := by omega
  have hθlo : A.base.θlo ∈ Icc A.base.θlo A.base.θhi := A.base.θlo_mem_types
  have hθhi : A.base.θhi ∈ Icc A.base.θlo A.base.θhi := A.base.θhi_mem_types
  -- The truthful (mimicry) payoff at the lowest type is `0`, and it is dominated by `Π(θ, θ)`, so
  -- the equilibrium payoff is nonnegative. This bounds both underbidding and excessive overbidding.
  have hR_nonneg : 0 ≤ A.base.firstPriceInterimUtil A.n θ θ := by
    have hlo0 : A.base.firstPriceInterimUtil A.n θ A.base.θlo = 0 := by
      simp only [ScreeningEnv.firstPriceInterimUtil, A.base.cdf_θlo_eq_zero, zero_pow hn1, mul_zero]
    calc (0 : ℝ) = A.base.firstPriceInterimUtil A.n θ A.base.θlo := hlo0.symm
      _ ≤ A.base.firstPriceInterimUtil A.n θ θ :=
          A.base.firstPriceBid_isBestResponse_Icc A.n hn hθ hθlo
  intro b'
  rw [A.firstPriceDevPayoff_firstPriceBid hn i hθ]
  rcases le_or_gt b' A.base.θlo with hlo | hlo
  · -- **Underbidding** `b' ≤ θlo`: win probability is `0`, so the deviation earns nothing.
    rw [A.firstPriceDevPayoff_def, A.firstPriceWinProb_eq_zero_of_le_θlo hn i hlo, mul_zero]
    exact hR_nonneg
  · rcases lt_or_ge b' (A.base.firstPriceBid A.n A.base.θhi) with hhi | hhi
    · -- **On-path** `θlo < b' < σ(θhi)`: `b'` is some `σ(z)`, so the deviation is the mimicry
      -- payoff, and the existing best-response lemma applies.
      have hb' : b' ∈ Icc A.base.θlo (A.base.firstPriceBid A.n A.base.θhi) := ⟨hlo.le, hhi.le⟩
      obtain ⟨z, hz, rfl⟩ := A.exists_firstPriceBid_eq hn hb'
      rw [A.firstPriceDevPayoff_firstPriceBid hn i hz]
      exact A.base.firstPriceBid_isBestResponse_Icc A.n hn hθ hz
    · -- **Overbidding** `σ(θhi) ≤ b'`: the payoff is capped and dominated by the `z = θhi` bid.
      rw [A.firstPriceDevPayoff_def]
      rcases le_or_gt θ b' with hθb | hθb
      · -- `θ ≤ b'`: the markup `θ − b'` is nonpositive, so the deviation payoff is `≤ 0 ≤ R`.
        have hW_nonneg : 0 ≤ A.firstPriceWinProb i b' := A.firstPriceWinProb_nonneg i b'
        have : (θ - b') * A.firstPriceWinProb i b' ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hW_nonneg
        linarith [hR_nonneg]
      · -- `b' < θ`: cap the win probability at `1`; overpaying past `σ(θhi)` is beaten by the
        -- `z = θhi` mimicry bid.
        have hmargin_nonneg : 0 ≤ θ - b' := by linarith
        have hW_le_one : A.firstPriceWinProb i b' ≤ 1 := A.firstPriceWinProb_le_one i b'
        have hhi_util : A.base.firstPriceInterimUtil A.n θ A.base.θhi
            = θ - A.base.firstPriceBid A.n A.base.θhi := by
          simp only [ScreeningEnv.firstPriceInterimUtil, A.base.cdf_θhi_eq_one, one_pow, mul_one]
        -- `(θ−b')·W ≤ (θ−b') ≤ θ−σ(θhi) = Π(θ,θhi) ≤ Π(θ,θ) = R`.
        calc (θ - b') * A.firstPriceWinProb i b'
            ≤ (θ - b') * 1 := by
              exact mul_le_mul_of_nonneg_left hW_le_one hmargin_nonneg
          _ = θ - b' := mul_one _
          _ ≤ θ - A.base.firstPriceBid A.n A.base.θhi := by linarith
          _ = A.base.firstPriceInterimUtil A.n θ A.base.θhi := hhi_util.symm
          _ ≤ A.base.firstPriceInterimUtil A.n θ θ :=
              A.base.firstPriceBid_isBestResponse_Icc A.n hn hθ hθhi

/-- **The direct mechanism is the indirect game played truthfully.** A type-`θ` bidder's truthful
interim utility in the direct first-price mechanism equals its equilibrium interim payoff in the
indirect first-price game (both are the mimicry payoff `firstPriceInterimUtil n θ θ`): The direct
representation is the game played through the equilibrium schedule `σ`. -/
theorem firstPriceMechanism_eq_equilibriumPayoff (hn : 2 ≤ A.n) (i : Fin A.n) {θ : ℝ}
    (hθ : θ ∈ Icc A.base.θlo A.base.θhi) :
    (A.firstPriceMechanism.reducedMechanism i).reportUtil θ θ
      = A.firstPriceDevPayoff i θ (A.base.firstPriceBid A.n θ) := by
  rw [firstPriceMechanism_reportUtil, A.firstPriceDevPayoff_firstPriceBid hn i hθ]

end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
