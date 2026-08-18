import Mathlib
import Econlib

/-!
# The Second-Price (Vickrey) Auction is VCG

The single-item second-price auction is the textbook instance of a Vickrey–Clarke–Groves
mechanism. Two bidders each privately value the item; the auctioneer awards it to the highest
bidder and charges the winner the *second*-highest bid. Vickrey's insight is that this is exactly
the VCG mechanism for the single-item allocation problem: the efficient allocation gives the item
to the bidder who values it most, and the Clarke pivot charges each agent the externality it
imposes on the others — which, for the winner, is the value the item would have created for the
runner-up, i.e. the second-highest bid.

We model it as an `AllocationEnvironment` — the diamond-free single-item specialization where the
outcome is which agent wins (`Outcome := Agent`, one `DecidableEq`). Two bidders `Fin 2` draw bids
from `Fin (B + 1)` (integer valuations `0, …, B`), and agent `i`'s valuation of winning at type `t`
is just `t`. The single-item structure (`welfareExcl`, `clarkePivot`, winner/loser payments) is
pre-proved once in `Transfers.General.Allocation`, so here we only specialize it to two bidders.

Against this environment the general VCG theorems fire directly:

* `secondPriceAuction_isEfficient` — the item goes to a value-maximizing bidder;
* `secondPriceAuction_isDSIC` — truthful bidding is a dominant strategy (Vickrey's theorem);
* `secondPriceAuction_isExPostIR` — no bidder ever regrets participating (values are nonnegative);
* `secondPriceAuction_isNoDeficit` — the auctioneer never pays out on net.

We then exercise the cohesion bridge `isDSIC_iff_isDominantStrategy_truthful`
(`secondPriceAuction_truthful_isDominantStrategy`) and pin the economic content with
`secondPriceAuction_clarkePivot`: each agent's Clarke pivot is exactly the *other* bidder's bid
(for a *winning* bidder, this is the second-highest bid; for a losing bidder the rival is the
winner, whose bid is the highest) — so a winning bidder pays the runner-up's bid and a losing bidder
pays nothing (`secondPriceAuction_winner_payment`, `secondPriceAuction_loser_payment`). The general
`n`-bidder fact — the pivot is the highest *competing* bid, i.e. the second order statistic at the
winner — is the library lemma `AllocationEnvironment.toQuasilinear_clarkePivot`; this file
exhibits only its two-bidder collapse, where "highest competing bid" is "the rival's bid".

For the second-price auction with a *continuum* of types at the interim layer — `n` symmetric IID
bidders, ex-post Vickrey payments, BIC via pointwise dominance, and the interim payment identified
with the Myerson payment by revenue equivalence — see `AuctionEnv.secondPriceMechanism` in
`Econlib.MechanismDesign.Transfers.SingleParameter.Auction.SecondPriceMechanism`.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.SecondPriceAuction

open Econlib.MechanismDesign.Transfers.General
open Econlib.GameTheory Econlib.Probability

variable (B : ℕ)

/-- **The two-bidder second-price auction** as a single-item allocation environment. Agents are
`Fin 2`; a bid is an integer valuation in `Fin (B + 1)`; agent `i` values winning at `t` at `t`
itself. The prior is irrelevant to the VCG guarantees, so we take the uniform distribution over bid
profiles. -/
def secondPriceAuction : AllocationEnvironment where
  Agent := Fin 2
  Theta := fun _ => Fin (B + 1)
  bid _ t := (t.val : ℝ)
  bid_nonneg _ t := Nat.cast_nonneg t.val
  prior := FinDist.uniform

/-- The VCG mechanism for the second-price auction. -/
abbrev spaMechanism : DirectMechanism (secondPriceAuction B).toQuasilinear :=
  vcgMechanism (secondPriceAuction B).toQuasilinear

/-! ## The VCG guarantees, instantiated

The Vickrey auction is the VCG mechanism for this environment, so all four classical guarantees are
direct instances of the general theorems. -/

/-- The auction is efficient: the item goes to a value-maximizing bidder. -/
theorem secondPriceAuction_isEfficient : (spaMechanism B).IsEfficient :=
  vcgMechanism_isEfficient

/-- **Vickrey's theorem:** truthful bidding is a dominant strategy. -/
theorem secondPriceAuction_isDSIC : (spaMechanism B).IsDSIC :=
  vcgMechanism_isDSIC

/-- No bidder regrets participating: ex-post utility is nonnegative. (Free from `bid_nonneg`.) -/
theorem secondPriceAuction_isExPostIR : (spaMechanism B).IsExPostIR :=
  vcgMechanism_isExPostIR (secondPriceAuction B).toQuasilinear_participation

/-- The auctioneer never pays out on net. -/
theorem secondPriceAuction_isNoDeficit : (spaMechanism B).IsNoDeficit :=
  vcgMechanism_isNoDeficit

/-- The same guarantee read through the cohesion bridge: truthful bidding is a (weakly)
dominant-strategy equilibrium of the induced Bayesian game — the GameTheory notion of dominant
strategy. -/
theorem secondPriceAuction_truthful_isDominantStrategy :
    (spaMechanism B).toIndirect.IsDominantStrategy (fun _ θ_i => θ_i) :=
  (DirectMechanism.isDSIC_iff_isDominantStrategy_truthful _).mp (secondPriceAuction_isDSIC B)

/-! ## The second price: the winner pays the rival's bid

With two bidders, the externality a bidder imposes is exactly the rival's bid (for a winning bidder
this rival bid is the second-highest bid overall; for a loser the rival is the winner).

The `n`-bidder version of this fact is not proved here — it already lives in the library:
`AllocationEnvironment.toQuasilinear_clarkePivot` shows the pivot equals
`sup'_o (if o = i then 0 else bid o (θ o))`, the highest competing bid. What is bespoke to this
file is only the two-agent collapse of that `sup'`: agent `i`'s own slot contributes the `0` floor,
so the maximum is the rival's (nonnegative) bid. -/

/-- The rival bidder (`0 ↦ 1`, `1 ↦ 0`). -/
def other (i : Fin 2) : Fin 2 := i + 1

lemma other_ne (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

/-- For `Fin 2`, "not me" is "the rival". -/
lemma ne_iff_eq_other {i o : Fin 2} : o ≠ i ↔ o = other i := by
  fin_cases i <;> fin_cases o <;> decide

/-- The others-value at the rival's outcome is exactly the rival's bid. -/
lemma spa_welfareExcl_rival (i : Fin 2) (θ : (secondPriceAuction B).TypeProfile) :
    (secondPriceAuction B).toQuasilinear.welfareExcl i (other i) θ = ((θ (other i)).val : ℝ) := by
  rw [AllocationEnvironment.toQuasilinear_welfareExcl]
  split_ifs with h
  · exact absurd h (other_ne i)
  · rfl

/-- The **Clarke pivot is the rival's bid** (for a *winning* bidder, the second-highest bid; for a
loser, the winner's higher bid — but the loser pays nothing regardless). The pivot is the maximal
others-value: among the two outcomes, agent `i`'s own slot contributes `0` and the rival's slot
contributes the rival's bid, which (being nonnegative) is the maximum. -/
lemma secondPriceAuction_clarkePivot (i : Fin 2) (θ : (secondPriceAuction B).TypeProfile) :
    (secondPriceAuction B).toQuasilinear.clarkePivot i θ = ((θ (other i)).val : ℝ) := by
  apply le_antisymm
  · rw [QuasilinearEnvironment.clarkePivot]
    refine Finset.sup'_le _ _ fun o _ => ?_
    rw [AllocationEnvironment.toQuasilinear_welfareExcl]
    split_ifs with h
    · exact Nat.cast_nonneg _
    · rw [ne_iff_eq_other.mp h]; exact le_rfl
  · rw [← spa_welfareExcl_rival]
    exact (secondPriceAuction B).toQuasilinear.welfareExcl_le_clarkePivot i (other i) θ

/-- **A winning bidder pays the rival's (second-highest) bid.** -/
theorem secondPriceAuction_winner_payment (i : Fin 2) (θ : (secondPriceAuction B).TypeProfile)
    (hwin : (secondPriceAuction B).toQuasilinear.efficientAlloc θ = i) :
    (spaMechanism B).transfer i θ = -((θ (other i)).val : ℝ) := by
  rw [(secondPriceAuction B).vcg_winner_transfer i θ hwin, secondPriceAuction_clarkePivot]

/-- **A losing bidder pays nothing.** -/
theorem secondPriceAuction_loser_payment (i : Fin 2) (θ : (secondPriceAuction B).TypeProfile)
    (hlose : (secondPriceAuction B).toQuasilinear.efficientAlloc θ ≠ i) :
    (spaMechanism B).transfer i θ = 0 :=
  (secondPriceAuction B).vcg_loser_transfer i θ hlose

end EconlibExamples.MechanismDesign.SecondPriceAuction
