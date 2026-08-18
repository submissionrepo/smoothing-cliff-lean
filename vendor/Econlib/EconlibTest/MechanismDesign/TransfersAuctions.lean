/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.MechanismDesign.UniformRevenueEquivalence
import Mathlib

/-!
# Auction-format non-vacuity witnesses (first-price, second-price, BNE)

Compile-time semantic witnesses for the `Transfers.SingleParameter` **auction-format** layer: The
second-price (Vickrey) mechanism (`secondPrice_pointwise_dominance`,
`secondPriceMechanism_pay_of_{top,not_top}`, `rivalMax_*`,
`secondPriceMechanism_interimPay_eq_myersonPayment`), the first-price schedule and its strict
shading (`firstPriceBid_lt_self`, `θlo_le_firstPriceBid`, `firstPriceBid_le_self`,
`firstPriceMechanism_{alloc,pay,interimPay}`), the indirect first-price game's Bayes–Nash
equilibrium (`firstPriceBid_isBNE`, `firstPriceWinProb_firstPriceBid`, `exists_firstPriceBid_eq`,
`isTopBidder_firstPriceBidProfile_iff`), and the reduced-form / interim-payment glue
(`AuctionMechanism.interimPay_*`, `ExpostAlloc.interimAlloc_{nonneg,le_one}`,
`expected_interimAlloc_eq`, `integrable_comp_eval`).

Anchored on the symmetric `n`-bidder uniform-`[0, 1]` IPV auction `uniformAuction` of
`EconlibExamples.MechanismDesign.UniformRevenueEquivalence`, where (for `n = 2`):

* the symmetric first-price bid is `b(θ) = θ − θ/2 = θ/2` — **strict shading**: A type bids *half*
  its value, strictly below it (for `θ > 0`).
* truthful bidding ex-post weakly dominates in the second-price auction (Vickrey), with the winner
  paying the rival's value and a loser paying nothing.
* the two formats are revenue equivalent — the Vickrey interim payment equals the Myerson payment.

## What each block catches

* **Vickrey ex-post dominance** (`secondPrice_pointwise_dominance`,
  `secondPrice_strict_dominance_witness`): Truthful bidding ex-post weakly dominates every
  misreport. On a concrete rival profile (rival max `3/8`) truthful reporting earns `1/8` while
  misreporting `1/4` *loses* and earns `0` — a genuine **strict** gap `0 < 1/8` where the reverse
  inequality is false.
* **Strict shading** (`firstPriceBid_lt_self`): The equilibrium bid is *strictly* below value
  (`bid < value`, not `≥`); for `n = 2` it is `θ/2`. A shading error (bid ≥ value) loses money.
* **Revenue equivalence** (`interimPay_eq_myersonPayment_half`, `firstPriceBid_isBNE`): The Vickrey
  interim payment equals the Myerson payment — both anchored at `t = 1/2` to the concrete value
  `1/8` (not just an equality) — and the first-price schedule is a genuine BNE.
* **Winner-pays / loser-free** (`secondPriceMechanism_pay_of_{top,not_top}`,
  `vickrey_concrete_payments`): The winner pays the second-highest value, a loser pays `0`. On the
  concrete profile `(1/2, 1/4)` bidder `0` pays exactly `1/4` and bidder `1` pays `0`.
* **Reduced-form consistency** (`expected_interimAlloc_eq`, `interimAlloc_{nonneg,le_one}`): The
  interim allocation lies in `[0, 1]` and averages to the ex-post allocation.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.TransfersAuctions

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.Probability
open Set MeasureTheory
open EconlibExamples.MechanismDesign.UniformRevenueEquivalence
  (uniformBase uniformBase_θlo uniformBase_θhi uniformBase_cdf uniformAuction uniformAuction_base
    uniformAuction_n uniformFirstPrice uniformSecondPrice firstPriceBid_eq
    uniformFirstPrice_interimAlloc uniformSecondPrice_interimAlloc uniformFirstPrice_isBIC
    uniformSecondPrice_isBIC)

/-- The concrete two-bidder uniform auction used throughout. -/
private abbrev A2 : AuctionEnv := uniformAuction 2 (by norm_num)

private theorem hn2 : 2 ≤ A2.n := by rw [uniformAuction_n]

/-! ## Block 1: The first-price bid schedule and its strict shading

For `n = 2` the symmetric first-price bid is `b(θ) = θ − θ/2 = θ/2`: Half the value. The
shading is *strict* for every type above the lowest. -/

/-- **`firstPriceBid_eq` — the bid schedule is `θ/2`** for `n = 2`. A type bids half its value.
Checked at `θ = 1/2`, giving `1/4`. -/
theorem firstPriceBid_half_witness :
    uniformBase.firstPriceBid 2 (1 / 2) = 1 / 4 := by
  rw [firstPriceBid_eq 2 (by norm_num) (by norm_num)]; norm_num

/-- **`firstPriceBid_lt_self` — STRICT shading** (`bid < value`): For a type above the lowest, the
first-price bid is *strictly* below the value. A non-strict / reversed bound would say a bidder
bids *at or above* its value, an immediate money-loser. Anchored at `θ = 1/2`:
`b(1/2) = 1/4 < 1/2`. -/
theorem firstPriceBid_lt_self_witness {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) 1) :
    uniformBase.firstPriceBid 2 θ < θ := by
  have h := uniformBase.firstPriceBid_lt_self 2 (by norm_num) (θ := θ) (by
    rw [uniformBase_θlo, uniformBase_θhi]; exact hθ)
  exact h

/-- A concrete numeric instance of strict shading: `b(1/2) = 1/4 < 1/2`. The strict gap `1/4` is the
**bid-shading gap** (the difference between value and submitted bid), *not* the expected rent: at
`θ = 1/2` the interim bidder rent and the interim seller payment are each `1/8`
(`firstPriceMechanism_interimPay_witness`), since both are scaled by the win probability `1/2`. -/
theorem firstPriceBid_lt_self_half : uniformBase.firstPriceBid 2 (1 / 2) < 1 / 2 := by
  rw [firstPriceBid_half_witness]; norm_num

/-- **`θlo_le_firstPriceBid`** — the bid never falls below the lowest type `0`: `b(θ) ≥ 0`. A
negative bid would be nonsensical. -/
theorem θlo_le_firstPriceBid_witness {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    uniformBase.θlo ≤ uniformBase.firstPriceBid 2 θ :=
  uniformBase.θlo_le_firstPriceBid 2 (by rw [uniformBase_θlo, uniformBase_θhi]; exact hθ)

/-- **`θlo_le_firstPriceBid` at the concrete `θ = 1/2`**: `θlo = 0 ≤ 1/4 = b(1/2)`, a numeric
non-vacuity anchor (the generic witness above left `θ` abstract). -/
theorem θlo_le_firstPriceBid_half : uniformBase.θlo ≤ uniformBase.firstPriceBid 2 (1 / 2) := by
  rw [uniformBase_θlo, firstPriceBid_half_witness]; norm_num

/-- **`firstPriceBid_le_self`** (weak version, every `n`, closed interval): `b(θ) ≤ θ`. Together
with `θlo_le_firstPriceBid` this brackets the bid in `[0, θ]`. -/
theorem firstPriceBid_le_self_witness {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    uniformBase.firstPriceBid 2 θ ≤ θ :=
  uniformBase.firstPriceBid_le_self 2 (by rw [uniformBase_θlo, uniformBase_θhi]; exact hθ)

/-! ## Block 2: The first-price direct (reduced) mechanism -/

/-- **`firstPriceMechanism_alloc`** — the first-price mechanism's allocation is the highest-value
allocation (efficient: Highest value wins). -/
theorem firstPriceMechanism_alloc_witness :
    A2.firstPriceMechanism.alloc = A2.highestValueAlloc :=
  A2.firstPriceMechanism_alloc

/-- **`firstPriceMechanism_pay`** — the ex-post payment factorizes: Own bid times the winner
indicator, `b(θᵢ) · 𝟙{i wins}`. A losing bidder (indicator `0`) pays nothing; the winner pays its
own (shaded) bid — the defining pay-your-bid rule. -/
theorem firstPriceMechanism_pay_witness (θ : A2.Profile) (i : Fin A2.n) :
    A2.firstPriceMechanism.pay θ i
      = A2.base.firstPriceBid A2.n (θ i) * A2.highestValueAlloc.x θ i :=
  A2.firstPriceMechanism_pay θ i

/-- **`firstPriceMechanism_interimPay`** — the interim payment factorizes: Own bid times own
interim winning probability, `b(t) · F(t)^{n-1}`. For `n = 2` at `t = 1/2`:
`b(1/2)·F(1/2)^1 = 1/4·1/2 = 1/8`. -/
theorem firstPriceMechanism_interimPay_witness :
    A2.firstPriceMechanism.interimPay ⟨0, by norm_num⟩ (1 / 2) = 1 / 8 := by
  rw [A2.firstPriceMechanism_interimPay, uniformAuction_base, uniformAuction_n,
    uniformBase_cdf (by norm_num), firstPriceBid_eq 2 (by norm_num) (by norm_num)]
  norm_num

/-! ## Block 3: The indirect first-price game and its Bayes–Nash equilibrium

The symmetric schedule `σ = firstPriceBid` is a genuine BNE of the indirect first-price game,
where messages are arbitrary bids `b ∈ ℝ` and the winner pays its *submitted* bid. -/

/-- **`firstPriceBid_isBNE` — the symmetric schedule is a Bayes–Nash equilibrium** of the indirect
first-price auction, tied to the canonical `MeasBayesianGame.IsBNE`. Discharged from `2 ≤ n`. This
is the non-vacuity endpoint: Truthful-schedule bidding is *an equilibrium*, not merely an
outcome. -/
theorem firstPriceBid_isBNE_witness : A2.firstPriceMeasGame.IsBNE A2.firstPriceStrategy :=
  A2.firstPriceBid_isBNE hn2

/-- **`firstPriceWinProb_firstPriceBid`** — submitting the bid a type-`z` bidder would, `b(z)`,
wins with the top order-statistic probability `F(z)^{n-1}`, **anchored to the closed value `1/2`**
for `n = 2` at `z = 1/2`: `F(1/2)^(2−1) = (1/2)^1 = 1/2`. (The previous witness left the RHS as the
symbolic `cdf(1/2)^(n−1)`; we discharge the uniform CDF and the `n = 2` exponent here.) -/
theorem firstPriceWinProb_firstPriceBid_witness (i : Fin A2.n) :
    A2.firstPriceWinProb i (A2.base.firstPriceBid A2.n (1 / 2)) = 1 / 2 := by
  rw [A2.firstPriceWinProb_firstPriceBid hn2 i
      (by rw [Set.mem_Icc, uniformAuction_base, uniformBase_θlo, uniformBase_θhi]; norm_num),
    uniformAuction_base, uniformAuction_n, uniformBase_cdf (by norm_num)]
  norm_num

/-- **`exists_firstPriceBid_eq`** — every on-path bid is attained: By the IVT, every bid in
`[θlo, b(θhi)]` equals `b(z)` for some type `z ∈ [θlo, θhi]`. We feed the **interior** bid `1/4`
(*not* the boundary value `θlo = 0`, which the schedule attains trivially at `z = θlo`); since
`b(1/2) = 1/4`, the IVT must produce an interior preimage `z`. This exercises the genuine
range-sweeping / IVT content. -/
theorem exists_firstPriceBid_eq_witness :
    ∃ z ∈ Icc A2.base.θlo A2.base.θhi, A2.base.firstPriceBid A2.n z = 1 / 4 := by
  -- `1/4 ∈ [θlo, b(θhi)]`: it is `≥ θlo = 0` and `= b(1/2) ≤ b(θhi)`.
  refine A2.exists_firstPriceBid_eq hn2 ⟨?_, ?_⟩
  · rw [uniformAuction_base, uniformBase_θlo]; norm_num
  · -- `b(θhi) = b(1) = 1/2 ≥ 1/4`.
    rw [show A2.base.firstPriceBid A2.n A2.base.θhi = 1 / 2 from by
      rw [uniformAuction_base, uniformAuction_n, uniformBase_θhi,
        firstPriceBid_eq 2 (by norm_num) (by norm_num)]; norm_num]
    norm_num

/-- **`isTopBidder_firstPriceBidProfile_iff` — order transport**: Applying the strictly increasing
schedule `σ` to a profile does not change who wins the highest-bid contest. The highest `σ`-bid is
the highest value — the crux that turns the highest-*bid* rule into the highest-*value* order
statistic on the equilibrium path. -/
theorem isTopBidder_firstPriceBidProfile_iff_witness {ρ : A2.Profile} {i : Fin A2.n}
    (hρ : ∀ j, ρ j ∈ Icc A2.base.θlo A2.base.θhi) :
    A2.IsTopBidder Real.exp (A2.firstPriceBidProfile ρ) i ↔ A2.IsTopBidder Real.exp ρ i :=
  A2.isTopBidder_firstPriceBidProfile_iff hρ hn2

/-! ## Block 4: The second-price (Vickrey) mechanism

Truthful bidding ex-post weakly dominates (Vickrey), the winner pays the second-highest value,
a loser pays nothing, and the rival-max glue behaves. -/

/-- **`rivalMax_update_self`** — the rival max does not depend on the bidder's own slot. -/
theorem rivalMax_update_self_witness (θ : A2.Profile) (i : Fin A2.n) (t : ℝ) :
    A2.rivalMax hn2 (Function.update θ i t) i = A2.rivalMax hn2 θ i :=
  A2.rivalMax_update_self hn2 θ i t

/-- **`rivalMax_measurable`** — the rival max is measurable in the profile (needed to integrate the
Vickrey ex-post payoff). -/
theorem rivalMax_measurable_witness (i : Fin A2.n) :
    Measurable fun θ : A2.Profile => A2.rivalMax hn2 θ i :=
  A2.rivalMax_measurable hn2 i

/-- **`rivalMax_mem_Icc`** — on a profile inside the type box, the rival max lies in `[θlo, θhi]`
(so the Vickrey price is a feasible value). -/
theorem rivalMax_mem_Icc_witness {θ : A2.Profile}
    (hθ : ∀ j, θ j ∈ Icc A2.base.θlo A2.base.θhi) (i : Fin A2.n) :
    A2.rivalMax hn2 θ i ∈ Icc A2.base.θlo A2.base.θhi :=
  A2.rivalMax_mem_Icc hn2 hθ i

/-- **`isTopBidder_update_of_rivalMax_lt`** — a report strictly above every rival wins. -/
theorem isTopBidder_update_of_rivalMax_lt_witness {θ : A2.Profile} {i : Fin A2.n} {t : ℝ}
    (h : A2.rivalMax hn2 θ i < t) :
    A2.IsTopBidder Real.exp (Function.update θ i t) i :=
  A2.isTopBidder_update_of_rivalMax_lt hn2 h

/-- **`rivalMax_le_of_isTopBidder`** — a winning report weakly clears every rival, so the rival max
is at most the report. -/
theorem rivalMax_le_of_isTopBidder_witness {θ : A2.Profile} {i : Fin A2.n} {t : ℝ}
    (h : A2.IsTopBidder Real.exp (Function.update θ i t) i) :
    A2.rivalMax hn2 θ i ≤ t :=
  A2.rivalMax_le_of_isTopBidder hn2 h

/-- **`secondPriceMechanism_pay_of_top` — the winner pays the second-highest value** (`rivalMax`).
A winner overpaying (its own bid) or underpaying (`0`) would break the Vickrey/VCG identity. -/
theorem secondPriceMechanism_pay_of_top_witness {θ : A2.Profile} {i : Fin A2.n}
    (h : A2.IsTopBidder Real.exp θ i) :
    (A2.secondPriceMechanism hn2).pay θ i = A2.rivalMax hn2 θ i :=
  A2.secondPriceMechanism_pay_of_top hn2 h

/-- **`secondPriceMechanism_pay_of_not_top` — a losing bidder pays nothing** (`0`). A loser charged
a positive amount would violate ex-post IR. -/
theorem secondPriceMechanism_pay_of_not_top_witness {θ : A2.Profile} {i : Fin A2.n}
    (h : ¬ A2.IsTopBidder Real.exp θ i) :
    (A2.secondPriceMechanism hn2).pay θ i = 0 :=
  A2.secondPriceMechanism_pay_of_not_top hn2 h

/-- A **concrete** two-bidder value profile `(bidder 0 → 1/2, bidder 1 → 1/4)`. -/
private def vickreyProfile : A2.Profile := ![1 / 2, 1 / 4]

private lemma vickreyProfile_val0 : vickreyProfile (0 : Fin 2) = 1 / 2 := by
  norm_num [vickreyProfile]

private lemma vickreyProfile_val1 : vickreyProfile (1 : Fin 2) = 1 / 4 := by
  norm_num [vickreyProfile]

/-- Bidder `0` is the top bidder on `vickreyProfile`: its value `1/2` is the highest (`exp` is
strictly monotone, so `exp(1/4) < exp(1/2)`), and there is no lower-indexed bidder. -/
private lemma vickreyProfile_top0 : A2.IsTopBidder Real.exp vickreyProfile (0 : Fin 2) := by
  have : NeZero A2.n := ⟨by rw [uniformAuction_n]; norm_num⟩
  refine ⟨(Real.exp_pos _).le, fun j => ?_, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
  fin_cases j
  · exact le_refl _
  · refine Real.exp_le_exp.mpr ?_
    change vickreyProfile (1 : Fin 2) ≤ vickreyProfile (0 : Fin 2)
    rw [vickreyProfile_val0, vickreyProfile_val1]; norm_num

/-- Bidder `1` is **not** the top bidder: a lower-indexed bidder (`0`, value `1/2`) outscores it. -/
private lemma vickreyProfile_not_top1 : ¬ A2.IsTopBidder Real.exp vickreyProfile (1 : Fin 2) := by
  rintro ⟨_, _, hlt⟩
  have hkey := hlt (0 : Fin 2) (by decide)
  -- `exp(θ 0) < exp(θ 1)` would require `1/2 < 1/4`, false.
  rw [Real.exp_lt_exp, vickreyProfile_val0, vickreyProfile_val1] at hkey
  norm_num at hkey

/-- `rivalMax vickreyProfile 0 = θ 1 = 1/4` (the only rival of bidder `0`). -/
private lemma vickreyProfile_rivalMax0 : A2.rivalMax hn2 vickreyProfile (0 : Fin 2) = 1 / 4 := by
  rw [Econlib.MechanismDesign.Transfers.SingleParameter.AuctionEnv.rivalMax, ← vickreyProfile_val1]
  -- The erase set is `{1}`, so the `sup'` is `vickreyProfile 1`. Prove by antisymmetry.
  have hA2n : NeZero A2.n := ⟨by rw [uniformAuction_n]; norm_num⟩
  refine le_antisymm (Finset.sup'_le _ _ (fun j hj => ?_)) (Finset.le_sup' _ ?_)
  · -- Every `j ∈ univ.erase 0` is `1` (in `Fin 2`), so `vickreyProfile j = vickreyProfile 1`.
    have hj0 : j ≠ (0 : Fin A2.n) := Finset.ne_of_mem_erase hj
    have hj1 : j = (1 : Fin 2) := by fin_cases j <;> simp_all
    rw [hj1]
  · exact Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩

/-- **The winner pays the second-highest value, the loser pays nothing — CONCRETELY**: on
`(1/2, 1/4)` bidder `0` (the winner) pays exactly the rival value `1/4`, and bidder `1` (the loser)
pays `0`. This discharges the `IsTopBidder` hypotheses on real data, so an accidentally-impossible
`IsTopBidder` or wrong tie-break could not make the implication witnesses above vacuous. -/
theorem vickrey_concrete_payments :
    (A2.secondPriceMechanism hn2).pay vickreyProfile (0 : Fin 2) = 1 / 4 ∧
    (A2.secondPriceMechanism hn2).pay vickreyProfile (1 : Fin 2) = 0 := by
  refine ⟨?_, A2.secondPriceMechanism_pay_of_not_top hn2 vickreyProfile_not_top1⟩
  rw [A2.secondPriceMechanism_pay_of_top hn2 vickreyProfile_top0, vickreyProfile_rivalMax0]

/-- **`secondPrice_pointwise_dominance` — Vickrey ex-post dominance** (THE canonical
flipped-inequality site): For every fixed rival profile, truthful reporting maximizes the ex-post
payoff `(θ − rivalMax) · 𝟙{win}`. A reversed inequality would make misreporting weakly optimal —
the silent IC bug this witness guards against. Surfaced at type `θ = 1/2`, misreport `r = 1/4`. -/
theorem secondPrice_pointwise_dominance_witness (i : Fin A2.n) (θ' : A2.Profile) :
    ((1 : ℝ) / 2 - A2.rivalMax hn2 θ' i)
        * A2.highestValueAlloc.x (Function.update θ' i (1 / 4)) i
      ≤ ((1 : ℝ) / 2 - A2.rivalMax hn2 θ' i)
        * A2.highestValueAlloc.x (Function.update θ' i (1 / 2)) i :=
  A2.secondPrice_pointwise_dominance hn2 i (1 / 2) (1 / 4) θ'

/-- A **concrete** rival profile with rival max `3/8`, for the *strict* Vickrey-dominance site. -/
private def domProfile : A2.Profile := ![0, 3 / 8]

private lemma domProfile_val1 : domProfile (1 : Fin 2) = 3 / 8 := by norm_num [domProfile]

/-- Reporting `1/2` (truthfully) wins against rival max `3/8`: bidder `0` is the top bidder. -/
private lemma domProfile_top_truthful :
    A2.IsTopBidder Real.exp (Function.update domProfile (0 : Fin 2) (1 / 2)) (0 : Fin 2) := by
  have : NeZero A2.n := ⟨by rw [uniformAuction_n]; norm_num⟩
  refine ⟨(Real.exp_pos _).le, fun j => ?_, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
  fin_cases j
  · exact le_refl _
  · refine Real.exp_le_exp.mpr ?_
    change (Function.update domProfile (0 : Fin 2) (1 / 2)) (1 : Fin 2)
      ≤ (Function.update domProfile (0 : Fin 2) (1 / 2)) (0 : Fin 2)
    rw [Function.update_self, Function.update_of_ne (by decide), domProfile_val1]; norm_num

/-- Reporting `1/4` loses against rival max `3/8`: bidder `0` is **not** the top bidder (bidder `1`
scores higher). -/
private lemma domProfile_not_top_misreport :
    ¬ A2.IsTopBidder Real.exp (Function.update domProfile (0 : Fin 2) (1 / 4)) (0 : Fin 2) := by
  rintro ⟨_, hmax, _⟩
  have hkey := hmax (1 : Fin 2)
  rw [Real.exp_le_exp, Function.update_self, Function.update_of_ne (by decide),
    domProfile_val1] at hkey
  norm_num at hkey

/-- **STRICT Vickrey ex-post dominance** on a concrete rival profile (rival max `3/8`): a type-`1/2`
bidder earns `(1/2 − 3/8)·1 = 1/8` by truthful reporting, but only `(1/2 − 3/8)·0 = 0` by
misreporting `1/4` (which now *loses*). So `0 < 1/8` — a genuine strict gap where the reverse
inequality is false. (The parametric witness above allows the degenerate `rivalMax` choices where
both sides tie; this one forces the strict site.) -/
theorem secondPrice_strict_dominance_witness :
    ((1 : ℝ) / 2 - A2.rivalMax hn2 domProfile (0 : Fin 2))
        * A2.highestValueAlloc.x (Function.update domProfile (0 : Fin 2) (1 / 4)) (0 : Fin 2)
      < ((1 : ℝ) / 2 - A2.rivalMax hn2 domProfile (0 : Fin 2))
        * A2.highestValueAlloc.x (Function.update domProfile (0 : Fin 2) (1 / 2)) (0 : Fin 2) := by
  -- `rivalMax domProfile 0 = 3/8`.
  have hrm : A2.rivalMax hn2 domProfile (0 : Fin 2) = 3 / 8 := by
    rw [Econlib.MechanismDesign.Transfers.SingleParameter.AuctionEnv.rivalMax, ← domProfile_val1]
    have : NeZero A2.n := ⟨by rw [uniformAuction_n]; norm_num⟩
    refine le_antisymm (Finset.sup'_le _ _ (fun j hj => ?_)) (Finset.le_sup' _ ?_)
    · have hj1 : j = (1 : Fin 2) := by
        have := Finset.ne_of_mem_erase hj; fin_cases j <;> simp_all
      rw [hj1]
    · exact Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩
  -- truthful: x = 1 (wins); misreport: x = 0 (loses).
  rw [Econlib.MechanismDesign.Transfers.SingleParameter.AuctionEnv.highestValueAlloc,
    A2.highestAlloc_x_of_top Real.measurable_exp domProfile_top_truthful,
    A2.highestAlloc_x_of_not_top Real.measurable_exp domProfile_not_top_misreport, hrm]
  norm_num

/-- **`secondPriceMechanism_interimPay_eq_myersonPayment` — revenue equivalence**: The Vickrey
interim payment equals the Myerson payment of the same highest-value allocation,
`t·F(t)^{n-1} − ∫_{θlo}^t F(s)^{n-1} ds`. A sign error in either expression breaks the equivalence
between the two formats. Checked on the type box at a generic `t`. -/
theorem secondPriceMechanism_interimPay_eq_myersonPayment_witness (i : Fin A2.n)
    {t : ℝ} (ht : t ∈ Icc A2.base.θlo A2.base.θhi) :
    (A2.secondPriceMechanism hn2).interimPay i t
      = (A2.highestValueAlloc.reducedAlloc i).myersonPayment t :=
  A2.secondPriceMechanism_interimPay_eq_myersonPayment hn2 i ht

/-- **Revenue equivalence, anchored numerically at `t = 1/2`**: the Vickrey interim payment and the
Myerson payment of the highest-value allocation are **both `1/8`**:
`p(1/2) = 1/2·F(1/2)^1 − ∫₀^{1/2} F(s)^1 ds = 1/2·(1/2) − ∫₀^{1/2} s ds = 1/4 − 1/8 = 1/8`. A
shared sign/convention error in the Myerson-payment side (which an equality-only witness could not
catch) would move this off `1/8`. -/
theorem interimPay_eq_myersonPayment_half (i : Fin A2.n) :
    (A2.secondPriceMechanism hn2).interimPay i (1 / 2) = 1 / 8 ∧
    (A2.highestValueAlloc.reducedAlloc i).myersonPayment (1 / 2) = 1 / 8 := by
  -- The reduced allocation is `x(s) = F(s)^1 = s` on `[0,1]`.
  have hx : ∀ s ∈ Icc (0 : ℝ) 1, (A2.highestValueAlloc.reducedAlloc i).x s = s := by
    intro s hs
    rw [ExPostAlloc.reducedAlloc_x, A2.highestValueAlloc_interimAlloc, uniformAuction_n,
      uniformAuction_base, uniformBase_cdf hs]
    norm_num
  -- The point value `x(1/2) = 1/2` and the integral `∫₀^{1/2} x = 1/8`, computed separately.
  have hpoint : (A2.highestValueAlloc.reducedAlloc i).x (1 / 2) = 1 / 2 := hx (1 / 2) (by norm_num)
  have hθlo : A2.base.θlo = 0 := by rw [uniformAuction_base, uniformBase_θlo]
  have hint : (∫ s in A2.base.θlo..(1 / 2), (A2.highestValueAlloc.reducedAlloc i).x s) = 1 / 8 := by
    rw [hθlo,
      show (∫ s in (0 : ℝ)..(1 / 2), (A2.highestValueAlloc.reducedAlloc i).x s)
          = ∫ s in (0 : ℝ)..(1 / 2), s from
        intervalIntegral.integral_congr (fun s hs => hx s (by
          rw [Set.uIcc_of_le (by norm_num)] at hs; exact ⟨hs.1, hs.2.trans (by norm_num)⟩)),
      integral_id]
    norm_num
  -- Compute the Myerson payment `1/2·x(1/2) − ∫₀^{1/2} x = 1/2·(1/2) − 1/8 = 1/8`.
  have hmyerson : (A2.highestValueAlloc.reducedAlloc i).myersonPayment (1 / 2) = 1 / 8 := by
    rw [AllocationRule.myersonPayment, hpoint, hint]; norm_num
  exact ⟨by rw [A2.secondPriceMechanism_interimPay_eq_myersonPayment hn2 i
      (by rw [uniformAuction_base, uniformBase_θlo, uniformBase_θhi]; norm_num), hmyerson],
    hmyerson⟩

/-! ## Block 5: Reduced-form / interim-payment glue -/

/-- **`AuctionMechanism.interimPay_def`** — the interim payment is the report-spliced expectation
`∫ pay(update θ i t) i`. Surfaced on the second-price mechanism. -/
theorem interimPay_def_witness (i : Fin A2.n) (t : ℝ) :
    (A2.secondPriceMechanism hn2).interimPay i t
      = ∫ θ, (A2.secondPriceMechanism hn2).pay (Function.update θ i t) i ∂A2.jointLaw :=
  (A2.secondPriceMechanism hn2).interimPay_def i t

/-- **`AuctionMechanism.interimPay_integrand_integrable`** — the interim-payment integrand is
integrable at every own report, so `interimPay i t` is a genuine expectation (not a silent `0` from
the Bochner integral of a non-integrable integrand). The honesty contract for the pointwise reading
of BIC. -/
theorem interimPay_integrand_integrable_witness (i : Fin A2.n) (t : ℝ) :
    Integrable (fun θ : Fin A2.n → ℝ => (A2.secondPriceMechanism hn2).pay (Function.update θ i t) i)
      A2.jointLaw :=
  (A2.secondPriceMechanism hn2).interimPay_integrand_integrable i t

/-- **`AuctionMechanism.interimPay_integrand_measurable`** — the interim-payment integrand is
measurable at every own report. -/
theorem interimPay_integrand_measurable_witness (i : Fin A2.n) (t : ℝ) :
    Measurable
      fun θ : Fin A2.n → ℝ => (A2.secondPriceMechanism hn2).pay (Function.update θ i t) i :=
  (A2.secondPriceMechanism hn2).interimPay_integrand_measurable i t

/-- **`AuctionMechanism.interimPay_measurable`** — the interim payment is measurable in the own
report, so the own-type expectation (the reduced-form revenue) is a genuine integral. -/
theorem interimPay_measurable_witness (i : Fin A2.n) :
    Measurable ((A2.secondPriceMechanism hn2).interimPay i) :=
  (A2.secondPriceMechanism hn2).interimPay_measurable i

/-- **`ExPostAlloc.interimAlloc_nonneg`** / **`interimAlloc_le_one`** — the interim allocation lies
in `[0, 1]` (a winning probability), surfaced generically. -/
theorem interimAlloc_mem_unitInterval (i : Fin A2.n) (t : ℝ) :
    0 ≤ A2.highestValueAlloc.interimAlloc i t ∧ A2.highestValueAlloc.interimAlloc i t ≤ 1 :=
  ⟨A2.highestValueAlloc.interimAlloc_nonneg i t, A2.highestValueAlloc.interimAlloc_le_one i t⟩

/-- **The order-statistic anchor `x̄(1/2) = 1/2`**: the highest-value interim allocation at the
midpoint is `F(1/2)^(2−1) = (1/2)^1 = 1/2` (and indeed lies in `[0,1]`). This pins the concrete
order-statistic value the generic membership bound above leaves symbolic. -/
theorem interimAlloc_half_eq (i : Fin A2.n) :
    A2.highestValueAlloc.interimAlloc i (1 / 2) = 1 / 2 := by
  rw [A2.highestValueAlloc_interimAlloc, uniformAuction_n, uniformAuction_base,
    uniformBase_cdf (by norm_num)]
  norm_num

/-- **`ExPostAlloc.expected_interimAlloc_eq` — reduced-form consistency**: The expected ex-post
allocation to bidder `i` (over the whole IID profile) equals the expectation of `i`'s reduced-form
interim allocation over its own type. The ex-post → interim bridge. -/
theorem expected_interimAlloc_eq_witness (i : Fin A2.n) :
    (∫ θ, A2.highestValueAlloc.x θ i ∂A2.jointLaw)
      = A2.base.dist.expect (A2.highestValueAlloc.interimAlloc i) :=
  A2.highestValueAlloc.expected_interimAlloc_eq i

/-- **`AuctionEnv.integrable_comp_eval`** — a bounded-on-support measurable function of one bidder's
type alone is integrable against the joint law (the shared density vanishes off `[θlo, θhi]`).
Checked on the **nonconstant** `g(t) = t`, which is unbounded globally but bounded by `1` on the
support `[0,1]` — so the witness genuinely exercises the *support-bounded* content (a constant
`g ≡ 1` is integrable under any probability measure, testing nothing about the support argument). -/
theorem integrable_comp_eval_witness (i : Fin A2.n) :
    Integrable (fun θ : A2.Profile => (fun t : ℝ => t) (θ i)) A2.jointLaw :=
  A2.integrable_comp_eval (g := fun t => t) measurable_id (C := 1)
    (fun t ht => by
      rw [uniformAuction_base, uniformBase_θlo, uniformBase_θhi] at ht
      rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩) i

/-! ## Block 6: The first-price interim allocation and BIC (anchored)

The first-price (= highest-value) allocation's interim form is the top order statistic, and the
direct reduced first-price mechanism is BIC (the equilibrium bid is a best response). -/

/-- **`uniformFirstPrice_interimAlloc`** anchored: The first-price interim allocation at `t = 1/2`
is `(1/2)^{n-1} = 1/2` for `n = 2`. -/
theorem firstPrice_interimAlloc_half (i : Fin A2.n) :
    (uniformFirstPrice 2 (by norm_num)).alloc.interimAlloc i (1 / 2) = 1 / 2 := by
  rw [uniformFirstPrice_interimAlloc 2 (by norm_num) i (by norm_num)]; norm_num

/-- **The second-price interim allocation matches** (`uniformSecondPrice_interimAlloc`): Both
formats implement the same order-statistic interim allocation `1/2` at `t = 1/2` — the
shared-allocation ingredient of revenue equivalence. -/
theorem secondPrice_interimAlloc_half (i : Fin A2.n) :
    (uniformSecondPrice 2 (by norm_num) (by norm_num)).alloc.interimAlloc i (1 / 2) = 1 / 2 := by
  rw [uniformSecondPrice_interimAlloc 2 (by norm_num) (by norm_num) i (by norm_num)]; norm_num

/-- **`firstPriceMechanism_isBIC`** (via `uniformFirstPrice_isBIC`) — the direct reduced first-price
mechanism is Bayesian incentive compatible: Truthfully reporting one's value is a best response. -/
theorem firstPrice_isBIC_witness : (uniformFirstPrice 2 (by norm_num)).IsBIC :=
  uniformFirstPrice_isBIC 2 (by norm_num) (by norm_num)

/-- **`secondPriceMechanism_isBIC`** (via `uniformSecondPrice_isBIC`) — the second-price
mechanism is BIC, by the ex-post Vickrey dominance argument integrated over the rivals' law. -/
theorem secondPrice_isBIC_witness : (uniformSecondPrice 2 (by norm_num) (by norm_num)).IsBIC :=
  uniformSecondPrice_isBIC 2 (by norm_num) (by norm_num)

end EconlibTest.MechanismDesign.TransfersAuctions

end
