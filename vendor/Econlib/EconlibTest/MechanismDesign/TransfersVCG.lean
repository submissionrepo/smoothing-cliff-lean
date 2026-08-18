/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform
import EconlibExamples.MechanismDesign.PublicGoodProvision
import EconlibExamples.MechanismDesign.SecondPriceAuction
import Mathlib

/-!
# VCG / Groves, revelation & taxation, and Myerson–Satterthwaite non-vacuity witnesses

Compile-time semantic witnesses for the `Transfers.General` (VCG / Groves / DSIC; revelation &
taxation principles) and `Transfers.Bilateral` (Myerson–Satterthwaite) layers.

Anchored on three concrete environments:

* the **public-good provision** environment `publicGood 1 3 1` of
  `EconlibExamples.MechanismDesign.PublicGoodProvision` (two agents, cost share `1`) and the
  **two-bidder second-price auction** `secondPriceAuction` of
  `EconlibExamples.MechanismDesign.SecondPriceAuction` — for the Groves alignment identity, the
  Clarke-pivot direction (winner pays, loser free), efficiency, and the revelation/taxation
  principles via the VCG mechanism's *dominant-strategy* truthful equilibrium;
* the **uniform-`[0, 1]` bilateral** environment `uniformBilateral` of
  `EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform` — for the strict budget deficit
  (`budget_collapse = −1/6 < 0`), the CDF/survival trade-probability identities, and the
  Mechanism-level glue, witnessed through a concretely built efficient zero-transfer mechanism.

## What each block catches

* **The Groves alignment identity** (`exPostUtility_eq_totalValue_update_sub`,
  `grovesMechanism_exPostUtility`): Truthful ex-post utility = total welfare minus a
  report-independent term. A sign error silently breaks DSIC.
* **VCG charge direction** (`welfareExcl_le_clarkePivot`, `vcg_winner_transfer ≤ 0`,
  `vcg_loser_transfer = 0`, and the **concrete** `vcg_winner_pays_rival_witness`): The winner *pays*
  its externality, a loser pays nothing. On the explicit bid profile `(4, 3)` bidder `0` wins and
  pays exactly the rival bid `−3`, while the loser pays `0` — anchored on the single-item
  second-price instance.
* **Efficiency** (`efficientAlloc_isMaxOn`, `isEfficient_iff_isMaxOn`): The welfare-maximizing
  allocation is selected.
* **Revelation principle** (`directify_isBIC`, `directify_isDSIC`, `directify_{alloc,transfer}`):
  The VCG mechanism's truthful dominant-strategy equilibrium directifies to a DSIC direct mechanism
  with the *same* outcome — the principle is non-vacuous.
* **BIC ⇔ truthful BNE** (`isBIC_iff_isBNE_truthful`): Both directions link the solution concepts.
* **Taxation principle** (`menu`, `menu_choice_eq_mechanism`, `menu_maximizer_unique`,
  `truthfulEntry_mem_menu`, `StrictlySeparatesAlloc`, `menuUtility_truthfulEntry`): A DSIC
  mechanism is choice from a price menu; the truthful entry is *the* unique maximizer under strict
  separation.
* **The budget deficit, exact value** (`budget_collapse_eq_neg_one_sixth`): On uniform `[0, 1]` the
  budget gap is **exactly** `−1/6` (not just `< 0`) — the impossibility's whole content; the strict
  negativity is a corollary, and a flipped sign or wrong magnitude is caught.
* **CDF vs survival, asymmetric anchors** (`buyerInterimTrade_eq_cdf_quarter`,
  `sellerInterimTrade_eq_survival_quarter`): The buyer trades with probability `F_s` (anchored at
  `F_s(1/4) = 1/4`), the seller with `1 − F_b` (anchored at `1 − F_b(3/4) = 1/4`). The evaluation
  points are deliberately *off* `1/2`, where `F = 1 − F`, so a complement flip is no longer silent.
* **Nonzero-transfer Fubini / budget** (`affMech`, `affMech_buyerPay_total = 1/2`,
  `affMech_sellerRecv_total = 1/4`, `affMech_net_budget_positive = 1/4`): a second mechanism with
  affine clamped payments makes the Fubini bridges and the ex-ante net budget *numerically nonzero*,
  catching the swapped-variable / wrong-order / sign-flip bugs the zero-transfer `effMech` hides.
* **Concrete BIC** (`noTradeMech`, `noTradeMech_{buyer,seller}Mech_isBIC_witness`): the no-trade
  mechanism is a genuine `BuyerBIC ∧ SellerBIC` witness on which both reduced-mechanism bridges are
  instantiated non-vacuously.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.TransfersVCG

open Econlib.MechanismDesign.Transfers.General
open Econlib.MechanismDesign.Transfers.Bilateral
open Econlib.GameTheory Econlib.Probability
open Set MeasureTheory Function

/-! ## Block 1: The Groves / VCG alignment and efficiency (public-good instance)

`publicGood 1 3 1` is the two-agent, cost-share-`1` public-good environment; `vcgMechanism` is
its VCG (Clarke-pivot) mechanism. We surface the Groves alignment identity, the efficiency
maximizer fact, and the quasilinear bridge lemmas. -/

open EconlibExamples.MechanismDesign.PublicGoodProvision
  (publicGood irAgent irProfile publicGood_isDSIC publicGood_truthful_isDominantStrategy)

/-- The concrete two-agent public-good environment (`n + 1 = 2`, values in `{0,…,3}`, cost `1`). -/
private abbrev PG : QuasilinearEnvironment := publicGood 1 3 1

/-- **`exPostUtility_eq_totalValue_update_sub` — the Groves alignment identity.** For any outcome
`o`, offset `c`, and report, splicing the agent's true type into the profile turns "own value plus
(others' value minus offset)" into "total welfare at the spliced profile minus offset". A sign
error here silently breaks DSIC. Surfaced on `irAgent`, outcome `true`, the witness profile. -/
theorem exPostUtility_eq_totalValue_update_sub_witness (c : ℝ) :
    PG.value irAgent true (irProfile irAgent)
        + (PG.welfareExcl irAgent true irProfile - c)
      = PG.totalValue true (Function.update irProfile irAgent (irProfile irAgent)) - c :=
  exPostUtility_eq_totalValue_update_sub irAgent true irProfile (irProfile irAgent) c

/-- **`grovesMechanism_exPostUtility` — the Groves utility closed form**: Truthful ex-post utility
is total value at the welfare profile minus the report-independent Clarke pivot offset. The DSIC
core, instantiated on the VCG mechanism (`vcgGrovesData`). -/
theorem grovesMechanism_exPostUtility_witness :
    (grovesMechanism (vcgGrovesData PG)).exPostUtility irAgent irProfile (irProfile irAgent)
      = PG.totalValue (PG.efficientAlloc irProfile)
          (Function.update irProfile irAgent (irProfile irAgent))
        - (vcgGrovesData PG).h irAgent irProfile :=
  grovesMechanism_exPostUtility (vcgGrovesData PG) irAgent irProfile (irProfile irAgent)

/-- **`efficientAlloc_isMaxOn`** — the efficient allocation maximizes total value at every profile.
Surfaced at the witness profile against the abstain outcome `false`. -/
theorem efficientAlloc_isMaxOn_witness :
    PG.totalValue false irProfile ≤ PG.totalValue (PG.efficientAlloc irProfile) irProfile :=
  PG.efficientAlloc_isMaxOn irProfile false

/-- **`isEfficient_iff_isMaxOn`** — `IsEfficient` is equivalent to the allocation being a maximizer
of total value over the outcome space at each profile. Surfaced on the VCG mechanism, whose
efficiency is `publicGood_isEfficient`. -/
theorem isEfficient_iff_isMaxOn_witness :
    (vcgMechanism PG).IsEfficient
      ↔ ∀ θ, IsMaxOn (fun o => PG.totalValue o θ) Set.univ ((vcgMechanism PG).alloc θ) :=
  (vcgMechanism PG).isEfficient_iff_isMaxOn

/-- **`value_add_welfareExcl`** — total value splits into agent `i`'s own valuation plus the value
to everyone else. The decomposition underlying the Groves base. -/
theorem value_add_welfareExcl_witness :
    PG.value irAgent true (irProfile irAgent) + PG.welfareExcl irAgent true irProfile
      = PG.totalValue true irProfile :=
  PG.value_add_welfareExcl irAgent true irProfile

/-- **`welfareExcl_update`** — `welfareExcl i` ignores agent `i`'s own reported coordinate. The
structural fact behind Groves DSIC (the others' value is unaffected by `i`'s report). -/
theorem welfareExcl_update_witness (x : PG.Theta irAgent) :
    PG.welfareExcl irAgent true (Function.update irProfile irAgent x)
      = PG.welfareExcl irAgent true irProfile :=
  PG.welfareExcl_update irAgent true irProfile x

/-- **`exPostUtility_def`** — the ex-post quasilinear utility unfolds to `value + transfer`.
Surfaced on the VCG mechanism at the witness profile. -/
theorem exPostUtility_def_witness :
    (vcgMechanism PG).exPostUtility irAgent irProfile (irProfile irAgent)
      = PG.value irAgent ((vcgMechanism PG).alloc irProfile) (irProfile irAgent)
        + (vcgMechanism PG).transfer irAgent irProfile :=
  (vcgMechanism PG).exPostUtility_def irAgent irProfile (irProfile irAgent)

/-! ## Block 2: The Clarke-pivot direction on the single-item (second-price) instance

The single-item `toQuasilinear` layer gives the cleanest winner-pays / loser-free anchor. We
use the two-bidder second-price auction, whose Clarke pivot is the rival's bid. -/

open EconlibExamples.MechanismDesign.SecondPriceAuction
  (secondPriceAuction spaMechanism)

/-- The concrete two-bidder single-item environment with bids in `{0,…,4}`. -/
private abbrev SPA : AllocationEnvironment := secondPriceAuction 4

/-- **`toQuasilinear_value`** — agent `i` values outcome `o` at its bid if `o = i`, else `0`. The
single-item valuation structure. -/
theorem toQuasilinear_value_witness (i o : SPA.Agent) (θ_i : SPA.Theta i) :
    SPA.toQuasilinear.value i o θ_i = if o = i then SPA.bid i θ_i else 0 :=
  SPA.toQuasilinear_value i o θ_i

/-- **`toQuasilinear_totalValue`** — social value is the winner's bid `bid o (θ o)` (only the
winner derives value). -/
theorem toQuasilinear_totalValue_witness (o : SPA.Agent) (θ : SPA.TypeProfile) :
    SPA.toQuasilinear.totalValue o θ = SPA.bid o (θ o) :=
  SPA.toQuasilinear_totalValue o θ

/-- **`toQuasilinear_welfareExcl`** — the others' value at outcome `o` is `0` if `i` wins, the
winner's bid otherwise. -/
theorem toQuasilinear_welfareExcl_witness (i o : SPA.Agent) (θ : SPA.TypeProfile) :
    SPA.toQuasilinear.welfareExcl i o θ = if o = i then 0 else SPA.bid o (θ o) :=
  SPA.toQuasilinear_welfareExcl i o θ

/-- **`toQuasilinear_participation`** — every single-item environment satisfies the participation
condition (bids are nonnegative), so VCG is ex-post IR here (contrast public goods). -/
theorem toQuasilinear_participation_witness : SPA.toQuasilinear.ParticipationCondition :=
  SPA.toQuasilinear_participation

/-- **`toQuasilinear_clarkePivot`** — the Clarke pivot equals the highest competing bid (`0` floor
from the winner's own slot). -/
theorem toQuasilinear_clarkePivot_witness (i : SPA.Agent) (θ : SPA.TypeProfile) :
    SPA.toQuasilinear.clarkePivot i θ
      = Finset.univ.sup' Finset.univ_nonempty
        (fun o => if o = i then 0 else SPA.bid o (θ o)) :=
  SPA.toQuasilinear_clarkePivot i θ

/-- **`welfareExcl_le_clarkePivot`** — the Clarke pivot dominates the others-value at every
outcome. The defining property of the pivot (the maximal others-value). -/
theorem welfareExcl_le_clarkePivot_witness (i o : SPA.Agent) (θ : SPA.TypeProfile) :
    SPA.toQuasilinear.welfareExcl i o θ ≤ SPA.toQuasilinear.clarkePivot i θ :=
  SPA.toQuasilinear.welfareExcl_le_clarkePivot i o θ

/-- **`exists_clarkePivot_eq`** — the Clarke pivot is attained at some outcome. -/
theorem exists_clarkePivot_eq_witness (i : SPA.Agent) (θ : SPA.TypeProfile) :
    ∃ o, SPA.toQuasilinear.clarkePivot i θ = SPA.toQuasilinear.welfareExcl i o θ :=
  SPA.toQuasilinear.exists_clarkePivot_eq i θ

/-- **`vcg_winner_transfer ≤ 0` — the winner PAYS its externality.** The winner's transfer (money
received) is `−clarkePivot ≤ 0`: A charge, not a subsidy. A positive transfer would mean the
mechanism *pays* the winner, the canonical VCG sign bug. -/
theorem vcg_winner_transfer_nonpos (i : SPA.Agent) (θ : SPA.TypeProfile)
    (hwin : SPA.toQuasilinear.efficientAlloc θ = i) :
    (spaMechanism 4).transfer i θ ≤ 0 := by
  rw [SPA.vcg_winner_transfer i θ hwin, neg_nonpos]
  -- The pivot dominates the others-value at `i`'s own outcome, which is `0`.
  have h := SPA.toQuasilinear.welfareExcl_le_clarkePivot i i θ
  rwa [SPA.toQuasilinear_welfareExcl, if_pos rfl] at h

/-- **`vcg_loser_transfer = 0` — a loser pays NOTHING.** A losing bidder's transfer is exactly `0`.
A nonzero loser charge would violate ex-post IR. -/
theorem vcg_loser_transfer_witness (i : SPA.Agent) (θ : SPA.TypeProfile)
    (hlose : SPA.toQuasilinear.efficientAlloc θ ≠ i) :
    (spaMechanism 4).transfer i θ = 0 :=
  SPA.vcg_loser_transfer i θ hlose

/-- A **concrete** bid profile `(bidder 0 → 4, bidder 1 → 3)` that anchors the winner-pays-rival
direction numerically. Bidder `0`'s value `4` strictly exceeds bidder `1`'s `3`. -/
private def bidProfile : SPA.TypeProfile := ![(4 : Fin 5), (3 : Fin 5)]

/-- Bidder `0` is the efficient winner on `bidProfile`: welfare at outcome `0` is `4`, strictly
above outcome `1`'s welfare `3`, and `Fin 2` has only these outcomes, so `0` is the maximizer. -/
private lemma bidProfile_efficient :
    SPA.toQuasilinear.efficientAlloc bidProfile = (0 : Fin 2) := by
  -- The efficient allocation is a welfare maximizer; `totalValue 0 = 4` and `totalValue 1 = 3`.
  have hmax := SPA.toQuasilinear.efficientAlloc_isMaxOn bidProfile (0 : Fin 2)
  have h0 : SPA.toQuasilinear.totalValue (0 : Fin 2) bidProfile = 4 := by
    rw [SPA.toQuasilinear_totalValue]; rfl
  rw [h0] at hmax
  -- The winner is `0` or `1`; rule out `1` (welfare `3 < 4`).
  have hw : SPA.toQuasilinear.efficientAlloc bidProfile = (0 : Fin 2)
      ∨ SPA.toQuasilinear.efficientAlloc bidProfile = (1 : Fin 2) := by
    rcases Fin.exists_fin_two.mp ⟨SPA.toQuasilinear.efficientAlloc bidProfile, rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hw with hw | hw
  · exact hw
  · exfalso
    have hwelf : SPA.toQuasilinear.totalValue (SPA.toQuasilinear.efficientAlloc bidProfile)
        bidProfile = 3 := by rw [hw, SPA.toQuasilinear_totalValue]; rfl
    rw [hwelf] at hmax
    linarith

/-- **The winner pays exactly the rival's bid `−3`, and the loser pays `0`** — the concrete
winner-pays-its-externality anchor the bare `≤ 0` bound could not provide. On `bidProfile`, bidder
`0` wins and pays the second-highest bid `3` (so its transfer is `−3`), while bidder `1` (the loser)
pays nothing. A mechanism charging every winner `0` would satisfy `transfer ≤ 0` but fails the
`= −3` anchor. -/
theorem vcg_winner_pays_rival_witness :
    (spaMechanism 4).transfer (0 : Fin 2) bidProfile = -3 ∧
    (spaMechanism 4).transfer (1 : Fin 2) bidProfile = 0 := by
  refine ⟨?_, ?_⟩
  · rw [EconlibExamples.MechanismDesign.SecondPriceAuction.secondPriceAuction_winner_payment
      4 (0 : Fin 2) bidProfile bidProfile_efficient]
    show -((bidProfile (EconlibExamples.MechanismDesign.SecondPriceAuction.other 0)).val : ℝ) = -3
    rfl
  · refine EconlibExamples.MechanismDesign.SecondPriceAuction.secondPriceAuction_loser_payment
      4 (1 : Fin 2) bidProfile ?_
    rw [bidProfile_efficient]; exact (Fin.zero_ne_one)

/-! ## Block 3: The revelation principle (VCG dominant-strategy equilibrium)

The VCG mechanism is DSIC, so its type-report form `toIndirect` has a truthful
*dominant-strategy* equilibrium (`publicGood_truthful_isDominantStrategy`). Applying
`directify_isDSIC` directifies it back to a DSIC direct mechanism with the *same*
outcome — the principle is non-vacuous. -/

/-- The indirect (type-report) form of the public-good VCG mechanism. -/
private abbrev pgIndirect : IndirectMechanism PG := (vcgMechanism PG).toIndirect

/-- The truthful strategy of the type-report game. -/
private abbrev truthful : pgIndirect.Strategy := fun _ θ_i => θ_i

/-- The truthful strategy is a dominant-strategy equilibrium of the indirect game. -/
private theorem truthful_isDominantStrategy : pgIndirect.IsDominantStrategy truthful :=
  publicGood_truthful_isDominantStrategy 1 3 1

/-- The truthful strategy is a Bayes–Nash equilibrium of the indirect game (a dominant-strategy
equilibrium is a BNE). -/
private theorem truthful_isBNE : pgIndirect.IsBNE truthful :=
  truthful_isDominantStrategy.isBNE

/-- **`directify_isDSIC` — every dominant-strategy equilibrium directifies to a DSIC
mechanism** (the revelation principle). Applied to the VCG mechanism's truthful equilibrium:
`directify truthful` is DSIC. A vacuous principle would be an over-claim; this confirms the
directified mechanism really is DSIC. -/
theorem directify_isDSIC_witness : (pgIndirect.directify truthful).IsDSIC :=
  pgIndirect.directify_isDSIC truthful_isDominantStrategy

/-- **`directify_isBIC` (BNE version)** — the truthful equilibrium directifies to a BIC
mechanism (the revelation principle). (A dominant-strategy equilibrium is a BNE, so `IsBNE truthful`
holds.) -/
theorem directify_isBIC_witness : (pgIndirect.directify truthful).IsBIC :=
  pgIndirect.directify_isBIC truthful_isBNE

/-- **`directify_alloc`** (API smoke test, definitional) — the directified mechanism reproduces the
equilibrium outcome. At every profile, `directify truthful` chooses the same outcome the indirect
game would under truthful play. The same-outcome guarantee of the revelation principle. -/
theorem directify_alloc_witness (θ : PG.TypeProfile) :
    (pgIndirect.directify truthful).alloc θ
      = pgIndirect.outcome (pgIndirect.msgProfile truthful θ) :=
  pgIndirect.directify_alloc truthful θ

/-- **`directify_transfer`** (API smoke test, definitional) — the directified mechanism reproduces
the equilibrium transfers. -/
theorem directify_transfer_witness (i : PG.Agent) (θ : PG.TypeProfile) :
    (pgIndirect.directify truthful).transfer i θ
      = pgIndirect.pay i (pgIndirect.msgProfile truthful θ) :=
  pgIndirect.directify_transfer truthful i θ

/-- **`directify_interimUtility`** — reporting `θ_i'` in `directify truthful` gives the same
interim utility as sending the message `truthful i θ_i'` in the indirect mechanism. -/
theorem directify_interimUtility_witness (i : PG.Agent) (θ_i θ_i' : PG.Theta i) :
    (pgIndirect.directify truthful).interimUtility i θ_i θ_i'
      = pgIndirect.interimUtility truthful i θ_i (truthful i θ_i') :=
  pgIndirect.directify_interimUtility truthful i θ_i θ_i'

/-! ## Block 4: The indirect-mechanism bridges -/

/-- **`isBIC_iff_isBNE_truthful` (← direction)** — truth-telling being a BNE of the type-report
game implies the direct mechanism is BIC. The truthful strategy is a BNE (it is a dominant-strategy
equilibrium, `truthful_isBNE`), so the VCG mechanism is BIC. -/
theorem isBIC_iff_isBNE_truthful_mpr : (vcgMechanism PG).IsBIC :=
  ((vcgMechanism PG).isBIC_iff_isBNE_truthful).mpr truthful_isBNE

/-- **`isBIC_iff_isBNE_truthful` (→ direction)** — BIC implies truth-telling is a BNE of the
type-report game, recovering the BNE from the BIC witness. This closes the biconditional
non-vacuously (both directions are exercised). -/
theorem isBIC_iff_isBNE_truthful_mp :
    (vcgMechanism PG).toIndirect.IsBNE (fun _ θ_i => θ_i) :=
  ((vcgMechanism PG).isBIC_iff_isBNE_truthful).mp isBIC_iff_isBNE_truthful_mpr

/-- **`IsBNE_iff_isNash_expanded`** — mechanism equilibrium is a Nash equilibrium of the
agent-normal-form (expanded) game. Surfaced on the truthful strategy. -/
theorem IsBNE_iff_isNash_expanded_witness :
    pgIndirect.IsBNE truthful
      ↔ pgIndirect.inducedBayesianGame.expandedGame.toStrategicGame.IsNash
        (pgIndirect.inducedBayesianGame.toExpandedProfile truthful) :=
  pgIndirect.IsBNE_iff_isNash_expanded truthful

/-- **`inducedBayesianGame_prior`** — the induced Bayesian game's prior is the common prior. -/
theorem inducedBayesianGame_prior_witness :
    pgIndirect.inducedBayesianGame.prior = PG.prior :=
  pgIndirect.inducedBayesianGame_prior

/-- **`inducedBayesianGame_payoff`** — the induced game's payoff is the quasilinear
`value + pay`. -/
theorem inducedBayesianGame_payoff_witness (i : PG.Agent) (a : Π j, pgIndirect.Msg j)
    (θ : PG.TypeProfile) :
    pgIndirect.inducedBayesianGame.payoff i a θ
      = PG.value i (pgIndirect.outcome a) (θ i) + pgIndirect.pay i a :=
  pgIndirect.inducedBayesianGame_payoff i a θ

/-- **`inducedBayesianGame_actionProfile`** — the induced game's action profile is the message
profile sent under `σ`. -/
theorem inducedBayesianGame_actionProfile_witness (θ : PG.TypeProfile) :
    pgIndirect.inducedBayesianGame.actionProfile truthful θ = pgIndirect.msgProfile truthful θ :=
  pgIndirect.inducedBayesianGame_actionProfile truthful θ

/-- **`interimUtility_eq_interimPayoffAction`** — the mechanism's interim utility equals the
induced game's interim payoff under a unilateral message deviation. -/
theorem interimUtility_eq_interimPayoffAction_witness (i : PG.Agent) (θ_i : PG.Theta i)
    (m_i : pgIndirect.Msg i) :
    pgIndirect.interimUtility truthful i θ_i m_i
      = pgIndirect.inducedBayesianGame.interimPayoffAction i θ_i m_i truthful :=
  pgIndirect.interimUtility_eq_interimPayoffAction truthful i θ_i m_i

/-! ## Block 5: The taxation principle (menu implementation)

A DSIC mechanism is choice from a posted price menu. We surface the menu API on the VCG
mechanism (DSIC), including the uniqueness theorem under strict separation. -/

/-- The VCG direct mechanism as a `Transfers.General.DirectMechanism` (for the menu API). -/
private abbrev pgVCG : DirectMechanism PG := vcgMechanism PG

private theorem pgVCG_dsic : pgVCG.IsDSIC := publicGood_isDSIC 1 3 1

/-- **`truthfulEntry_mem_menu`** — the truthful entry is a reachable menu entry. -/
theorem truthfulEntry_mem_menu_witness (i : PG.Agent) (r : PG.TypeProfile) (θ_i : PG.Theta i) :
    truthfulEntry pgVCG i r θ_i ∈ menu pgVCG i r :=
  truthfulEntry_mem_menu i r θ_i

/-- **`menuUtility_truthfulEntry`** — the menu utility of the truthful entry is the agent's ex-post
utility under truthful reporting (definitionally the same quasilinear expression). -/
theorem menuUtility_truthfulEntry_witness (i : PG.Agent) (r : PG.TypeProfile) (θ_i : PG.Theta i) :
    menuUtility i θ_i (truthfulEntry pgVCG i r θ_i)
      = pgVCG.exPostUtility i (Function.update r i θ_i) θ_i :=
  menuUtility_truthfulEntry i r θ_i

/-- **`menu_choice_eq_mechanism` — an IC mechanism is choice from a price menu.** Under DSIC the
truthful entry lies in the menu, maximizes menu utility, and its outcome/price are the mechanism's
allocation/transfer at the true type — the posted-menu implementation, packaged. -/
theorem menu_choice_eq_mechanism_witness (i : PG.Agent) (r : PG.TypeProfile) (θ_i : PG.Theta i) :
    truthfulEntry pgVCG i r θ_i ∈ menu pgVCG i r ∧
      IsMaxOn (menuUtility i θ_i) (menu pgVCG i r) (truthfulEntry pgVCG i r θ_i) ∧
        (truthfulEntry pgVCG i r θ_i).1 = pgVCG.alloc (Function.update r i θ_i) ∧
          (truthfulEntry pgVCG i r θ_i).2 = pgVCG.transfer i (Function.update r i θ_i) :=
  menu_choice_eq_mechanism pgVCG_dsic i r θ_i

/-- **`menu_maximizer_unique`** — under DSIC and strict separation, the truthful entry is *the*
unique menu-utility maximizer.

**Scope (conditional API smoke test, not a non-vacuity guard).** The strict-separation hypothesis
`hsep`, the menu membership `he`, and the maximality `hmax` are all *assumed*, not discharged on
concrete data — this witness only confirms the theorem *applies* with the right argument shapes. The
public-good VCG instance does **not** strictly separate: the binary public-good allocation
`{true, false}` collapses many distinct type-reports to the same outcome, so most reports induce no
allocation change and `StrictlySeparatesAlloc` fails on this instance. For a *non-vacuous* witness —
strict separation discharged on concrete data and `menu_maximizer_unique` instantiated — see
`secondPriceAuction_menu_maximizer_unique_witness` below, which exploits the unique highest bidder
of the second-price auction. -/
theorem menu_maximizer_unique_witness (i : PG.Agent) (r : PG.TypeProfile) (θ_i : PG.Theta i)
    (hsep : StrictlySeparatesAlloc pgVCG i r θ_i)
    {e : PG.Outcome × ℝ} (he : e ∈ menu pgVCG i r)
    (hmax : IsMaxOn (menuUtility i θ_i) (menu pgVCG i r) e) :
    e = truthfulEntry pgVCG i r θ_i :=
  menu_maximizer_unique pgVCG_dsic i r θ_i hsep he hmax

/-- **`StrictlySeparatesAlloc` unfolds** to its definition: Every own-report inducing a different
outcome than the truthful report is *strictly* worse. This is the strict-incentive hypothesis fed
to `menu_maximizer_unique`; surfacing it here pins down its exact content (a flipped inequality
would admit ties at distinct outcomes, breaking uniqueness of the menu choice). -/
theorem strictlySeparatesAlloc_def (i : PG.Agent) (r : PG.TypeProfile) (θ_i : PG.Theta i) :
    StrictlySeparatesAlloc pgVCG i r θ_i
      ↔ ∀ s : PG.Theta i,
          pgVCG.alloc (Function.update r i s) ≠ pgVCG.alloc (Function.update r i θ_i)
          → pgVCG.exPostUtility i (Function.update r i s) θ_i
              < pgVCG.exPostUtility i (Function.update r i θ_i) θ_i :=
  Iff.rfl

/-! ### A *non-vacuous* `menu_maximizer_unique` witness (second-price auction)

`menu_maximizer_unique_witness` above only confirms the theorem *applies*: its strict-separation
hypothesis is assumed, because the public-good VCG instance does not strictly separate (the binary
provision outcome ties two reports in total welfare). The second-price auction, by contrast, *does*
strictly separate whenever the true profile has a unique highest bidder — exactly the content of the
library bridge `strictlySeparatesAlloc_of_unique_efficient`.

We anchor on `secondPriceAuction 4` with the base profile `![0, 1]` (the rival, agent `1`, bids
`1`). Any own-report by agent `0` strictly above `1` wins the item outright, so it is the unique
efficient outcome; strict separation then holds, and `menu_maximizer_unique` forces a genuinely
different own-report's menu entry to coincide with the truthful entry. -/

open EconlibExamples.MechanismDesign.SecondPriceAuction (secondPriceAuction_isDSIC)

/-- Base profile: the rival bidder (agent `1`) bids `1`; agent `0`'s slot is overwritten below. -/
private def sepProfile : SPA.TypeProfile := ![0, 1]

/-- **Unique efficient outcome.** When agent `0` reports any value `v` strictly above the rival's
bid `1`, agent `0` is the *unique* total-value maximizer: the only competing outcome (`1` wins) is
worth the rival's bid `1 < v`. -/
private theorem sep_unique_max (v : Fin 5) (hv : 1 < v.val) :
    ∀ o : Fin 2, o ≠ (0 : Fin 2) →
      SPA.toQuasilinear.totalValue o (update sepProfile (0 : Fin 2) v)
        < SPA.toQuasilinear.totalValue (0 : Fin 2) (update sepProfile (0 : Fin 2) v) := by
  intro o ho
  -- On `Fin 2`, `o ≠ 0` means `o = 1`: the rival's slot, holding bid `sepProfile 1 = 1`.
  have ho1 : o = 1 := by omega
  subst ho1
  -- Social value at outcome `o` is the winner's bid `(profile o).val`.
  rw [SPA.toQuasilinear_totalValue, SPA.toQuasilinear_totalValue]
  -- The two reachable coordinates of the updated profile (same `DecidableEq` instance as the goal).
  have e0 : update sepProfile (0 : Fin 2) v (0 : Fin 2) = v := Function.update_self ..
  have e1 : update sepProfile (0 : Fin 2) v (1 : Fin 2) = (1 : Fin 5) := by
    have hne : update sepProfile (0 : Fin 2) v (1 : Fin 2) = sepProfile (1 : Fin 2) :=
      Function.update_of_ne (show (1 : Fin 2) ≠ (0 : Fin 2) by decide) v sepProfile
    rw [hne]; simp [sepProfile]
  rw [e0, e1]
  -- `SPA.bid` is `(·.val : ℝ)`, so the goal is `1 < v` as reals.
  change ((1 : Fin 5).val : ℝ) < (v.val : ℝ)
  exact_mod_cast hv

/-- The efficient allocation at a winning own-report `v > 1` is agent `0`. (`efficientAlloc` is an
opaque `Finite.exists_max.choose`; the strict-unique-max above identifies the concrete winner.) -/
private theorem sep_efficientAlloc_eq_zero (v : Fin 5) (hv : 1 < v.val) :
    SPA.toQuasilinear.efficientAlloc (update sepProfile (0 : Fin 2) v) = (0 : Fin 2) :=
  efficientAlloc_eq_of_forall_lt (E := SPA.toQuasilinear) (update sepProfile (0 : Fin 2) v)
    (0 : Fin 2) (sep_unique_max v hv)

/-- **A genuinely non-vacuous `menu_maximizer_unique`.** Agent `0`'s true type is `3`; the
alternative own-report `4` also wins the item, so it yields the same allocation and (Clarke-pivot)
transfer. Strict separation therefore forces the report-`4` menu entry to coincide with the truthful
(report-`3`) entry: the agent's menu choice is pinned to the mechanism's allocation/transfer at its
true type, with no other outcome tying. -/
theorem secondPriceAuction_menu_maximizer_unique_witness :
    truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (4 : Fin 5)
      = truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (3 : Fin 5) := by
  -- Strict separation at the true type `3`: the unique efficient outcome is agent `0`.
  have hsep : StrictlySeparatesAlloc (spaMechanism 4) (0 : Fin 2) sepProfile (3 : Fin 5) := by
    refine strictlySeparatesAlloc_of_unique_efficient (vcgGrovesData SPA.toQuasilinear) (0 : Fin 2)
      sepProfile (3 : Fin 5) ?_
    rw [sep_efficientAlloc_eq_zero (3 : Fin 5) (by norm_num)]
    exact sep_unique_max (3 : Fin 5) (by norm_num)
  -- The report-`4` entry is a menu entry, and it maximizes menu utility because both reports win
  -- the item and hence carry equal ex-post utility (the Clarke offset is own-report-independent).
  have hmem : truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (4 : Fin 5)
      ∈ menu (spaMechanism 4) (0 : Fin 2) sepProfile :=
    truthfulEntry_mem_menu (0 : Fin 2) sepProfile (4 : Fin 5)
  -- The menu utility at true type `3` of *any* own-report's truthful entry is its ex-post utility
  -- (shallow definitional unfolding — no `vcgMechanism` reduction).
  have hmt : ∀ t : Fin 5, menuUtility (0 : Fin 2) (3 : Fin 5)
        (truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile t)
      = (spaMechanism 4).exPostUtility (0 : Fin 2) (update sepProfile (0 : Fin 2) t) (3 : Fin 5) :=
    fun _ => rfl
  -- Reports `3` and `4` both win the item, so their ex-post utilities (hence menu utilities) agree:
  -- the efficient outcome is `0` in both cases and the Clarke offset is own-report-independent.
  have heq : (spaMechanism 4).exPostUtility (0 : Fin 2) (update sepProfile (0 : Fin 2) (3 : Fin 5))
        (3 : Fin 5)
      = (spaMechanism 4).exPostUtility (0 : Fin 2) (update sepProfile (0 : Fin 2) (4 : Fin 5))
        (3 : Fin 5) := by
    unfold spaMechanism vcgMechanism
    rw [grovesMechanism_exPostUtility, grovesMechanism_exPostUtility, update_idem, update_idem,
      (vcgGrovesData SPA.toQuasilinear).h_indep (0 : Fin 2) sepProfile (4 : Fin 5) (3 : Fin 5),
      sep_efficientAlloc_eq_zero (3 : Fin 5) (by norm_num),
      sep_efficientAlloc_eq_zero (4 : Fin 5) (by norm_num)]
  have heqm : menuUtility (0 : Fin 2) (3 : Fin 5)
        (truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (3 : Fin 5))
      = menuUtility (0 : Fin 2) (3 : Fin 5)
        (truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (4 : Fin 5)) := by
    rw [hmt, hmt]; exact heq
  have hmax : IsMaxOn (menuUtility (0 : Fin 2) (3 : Fin 5))
      (menu (spaMechanism 4) (0 : Fin 2) sepProfile)
      (truthfulEntry (spaMechanism 4) (0 : Fin 2) sepProfile (4 : Fin 5)) := by
    rw [isMaxOn_iff]
    intro x hx
    have hx_le := implements_menu (secondPriceAuction_isDSIC 4) (0 : Fin 2) sepProfile
      (3 : Fin 5) hx
    exact hx_le.trans (le_of_eq heqm)
  exact menu_maximizer_unique (secondPriceAuction_isDSIC 4) (0 : Fin 2) sepProfile (3 : Fin 5)
    hsep hmem hmax

/-! ## Block 6: Myerson–Satterthwaite — the strict budget deficit (uniform `[0, 1]`)

The whole content of the impossibility is the *strict* budget deficit. We anchor
`budget_collapse` on the uniform environment, where the RHS overlap integral is `1/6`, so the
budget gap is exactly `−1/6 < 0`. We also surface the environment- and Mechanism-level glue, the
latter via a concretely constructed efficient zero-transfer mechanism. -/

open EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform
  (uniformEnv uniformEnv_cdf uniformBilateral uniformBilateral_buyer
    uniformBilateral_seller uniformBilateral_survival_integral)

/-- **`BilateralEnv.jointLaw_def`** (API smoke test, definitional) — the joint law is the product
`F_b ⊗ F_s` of the two independent type laws. -/
theorem jointLaw_def_witness :
    uniformBilateral.jointLaw
      = uniformBilateral.buyer.dist.toMeasure.prod uniformBilateral.seller.dist.toMeasure :=
  uniformBilateral.jointLaw_def

/-- **`budget_collapse` — the budget deficit on uniform `[0, 1]` is exactly `−1/6`.** The
buyer/seller virtual gains minus the two cumulative survival integrals equal
`−∫ (1 − F_b)·F_s = −1/6`. We state the **exact magnitude** (not merely `< 0`), so a wrong negative
value would also be caught. The uniform computation is
`1/3 − 1/6 − 1/6 − 1/6 = −1/6`; here `budget_collapse` collapses the four terms to `−∫ (1−F_b)·F_s`
whose value is `−1/6`. -/
theorem budget_collapse_eq_neg_one_sixth :
    (((∫ θ in (0 : ℝ)..1, uniformEnv.dist.density θ * (θ * uniformEnv.dist.cdf θ))
          - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.density θ * (θ * (1 - uniformEnv.dist.cdf θ)))
        - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.cdf θ * (1 - uniformEnv.dist.cdf θ))
      - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.cdf θ * (1 - uniformEnv.dist.cdf θ)
    = -(1 / 6) := by
  -- `budget_collapse` rewrites the LHS as `−∫ (1 − F_b)·F_s` over the overlap `[0,1]`.
  have hbc := budget_collapse uniformEnv uniformEnv uniformEnv.hθ uniformEnv.hθ
  rw [show uniformEnv.θlo = (0 : ℝ) from rfl, show uniformEnv.θhi = (1 : ℝ) from rfl,
    min_self, max_self] at hbc
  rw [hbc]
  -- The overlap integral is `1/6` (matching `uniformBilateral_survival_integral`).
  have hs := uniformBilateral_survival_integral
  simp only [uniformBilateral_buyer, uniformBilateral_seller] at hs
  rw [hs]

/-- The budget gap is **strictly negative** — a corollary of the exact value `−1/6`. A flipped sign
would falsely make efficient, budget-balanced trade feasible. -/
theorem budget_collapse_strictly_negative :
    (((∫ θ in (0 : ℝ)..1, uniformEnv.dist.density θ * (θ * uniformEnv.dist.cdf θ))
          - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.density θ * (θ * (1 - uniformEnv.dist.cdf θ)))
        - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.cdf θ * (1 - uniformEnv.dist.cdf θ))
      - ∫ θ in (0 : ℝ)..1, uniformEnv.dist.cdf θ * (1 - uniformEnv.dist.cdf θ)
    < 0 := by
  rw [budget_collapse_eq_neg_one_sixth]; norm_num

/-- **`intervalIntegral.add_eq_union_add_inter`** — interval inclusion–exclusion for an
interval-integrable integrand: Overlapping intervals' integrals sum to the union plus the
intersection integral. Surfaced on the overlapping `[0, 3/4]`, `[1/4, 1]` against the continuous
`F_s` (constant `1` integrand here). -/
theorem interval_incl_excl_witness :
    (∫ _t in (0 : ℝ)..(3 / 4), (1 : ℝ)) + ∫ _t in (1 / 4 : ℝ)..1, (1 : ℝ)
      = (∫ _t in min (0 : ℝ) (1 / 4)..max (3 / 4 : ℝ) 1, (1 : ℝ))
        + ∫ _t in max (0 : ℝ) (1 / 4)..min (3 / 4 : ℝ) 1, (1 : ℝ) :=
  intervalIntegral.add_eq_union_add_inter (by norm_num) (by norm_num) (by norm_num)
    (intervalIntegrable_const)

/-! ### A concrete efficient zero-transfer mechanism

To exercise the Mechanism-level glue we build the **efficient zero-transfer** mechanism on
`uniformBilateral`: Trade iff `θ_s ≤ θ_b`, no money changes hands. (It is *not* IR/budget-balanced
— that is the whole point of the impossibility — but it is a genuine `Mechanism` and exercises the
reduced-form / integrability API.) -/

/-- The efficient trade rule `𝟙{θ_s ≤ θ_b}` is measurable in the buyer's value (seller fixed). -/
private theorem effTrade_meas_buyer (θs : ℝ) :
    Measurable (fun θb : ℝ => if θs ≤ θb then (1 : ℝ) else 0) := by
  refine Measurable.ite (measurableSet_le measurable_const measurable_id) ?_ ?_ <;>
    exact measurable_const

/-- The efficient trade rule is measurable in the seller's cost (buyer fixed). -/
private theorem effTrade_meas_seller (θb : ℝ) :
    Measurable (fun θs : ℝ => if θs ≤ θb then (1 : ℝ) else 0) := by
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_ <;>
    exact measurable_const

/-- The **efficient zero-transfer mechanism** on the uniform bilateral environment. -/
private def effMech : uniformBilateral.Mechanism where
  trade θb θs := if θs ≤ θb then 1 else 0
  trade_nonneg θb θs := by split_ifs <;> norm_num
  trade_le_one θb θs := by split_ifs <;> norm_num
  trade_measurable_buyer θs := effTrade_meas_buyer θs
  trade_measurable_seller θb := effTrade_meas_seller θb
  payBuyer _ _ := 0
  paySeller _ _ := 0
  payBuyer_integrable θb := by simp
  paySeller_integrable θs := by simp
  payBuyer_jointMeasurable := measurable_const
  paySeller_jointMeasurable := measurable_const
  payBuyer_jointIntegrable := by simp
  paySeller_jointIntegrable := by simp

/-- `effMech` is ex-post efficient by construction. -/
private theorem effMech_efficient : effMech.Efficient := fun _ _ _ _ => rfl

/-! ### A concrete nonzero affine-payment mechanism

The zero-transfer `effMech` makes every Fubini / budget witness `0 = 0`, so a swapped variable,
wrong product-measure order, or sign flip in the ex-ante budget is invisible. We build a second
mechanism `affMech` whose payments are genuinely nonzero affine functions of the *clamped* types
(clamped so they are globally bounded, hence trivially integrable, while agreeing with the bare
type on the support `[0,1]`):

* `payBuyer θb θs = clamp θb` (the buyer pays its own clamped value);
* `paySeller θb θs = clamp θs / 2` (the seller receives half its own clamped cost).

On the uniform support these are `θb` and `θs / 2`, so the expected buyer payment is `𝔼[θb] = 1/2`,
the expected seller receipt is `𝔼[θs]/2 = 1/4`, and the ex-ante **net** budget is the asymmetric
`1/2 − 1/4 = 1/4 > 0`. A `(θb ↔ θs)` swap or a sign flip in the net transfer would change these
anchors. -/

/-- The clamp `[0,1]` map: globally bounded, agrees with the identity on `[0,1]`. -/
private def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

private lemma clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, by rw [clamp01, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩⟩

private lemma clamp01_cont : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma clamp01_meas : Measurable clamp01 := clamp01_cont.measurable

private lemma clamp01_bdd (t : ℝ) : |clamp01 t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [(clamp01_mem t).1], (clamp01_mem t).2⟩

/-- On `[0,1]`, the clamp is the identity. -/
private lemma clamp01_eq_self {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right ht.2, max_eq_right ht.1]

/-- A bounded selector times the density is integrable (bounded × integrable density). -/
private lemma sel_density_integrable (d : Econlib.Probability.ContDist)
    (sel : ℝ → ℝ) (hsel : Measurable sel) (hbdd : ∀ t, |sel t| ≤ 1) :
    Integrable (fun t => d.density t * sel t) := by
  rw [show (fun t => d.density t * sel t) = (fun t => sel t * d.density t) from
    funext fun t => mul_comm _ _]
  refine Integrable.bdd_mul (c := 1) d.integrable hsel.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]; exact hbdd t

/-- A bounded selector is jointly integrable against the product law (bounded by `1`, probability
measure). -/
private lemma sel_jointIntegrable
    (sel : ℝ × ℝ → ℝ) (hsel : Measurable sel) (hbdd : ∀ p, |sel p| ≤ 1) :
    Integrable sel uniformBilateral.jointLaw := by
  haveI hpb : IsProbabilityMeasure uniformBilateral.buyer.dist.toMeasure :=
    uniformBilateral.buyer.dist.toMeasure_isProbability
  haveI hps : IsProbabilityMeasure uniformBilateral.seller.dist.toMeasure :=
    uniformBilateral.seller.dist.toMeasure_isProbability
  haveI : IsProbabilityMeasure uniformBilateral.jointLaw := by
    rw [uniformBilateral.jointLaw_def]; infer_instance
  refine MeasureTheory.Integrable.of_bound hsel.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]; exact hbdd p

/-- The **nonzero affine-payment** mechanism: buyer pays clamped value, seller receives half
clamped cost. -/
private def affMech : uniformBilateral.Mechanism where
  trade θb θs := if θs ≤ θb then 1 else 0
  trade_nonneg θb θs := by split_ifs <;> norm_num
  trade_le_one θb θs := by split_ifs <;> norm_num
  trade_measurable_buyer θs := effTrade_meas_buyer θs
  trade_measurable_seller θb := effTrade_meas_seller θb
  payBuyer θb _ := clamp01 θb
  paySeller _ θs := clamp01 θs / 2
  payBuyer_integrable θb :=
    sel_density_integrable uniformBilateral.seller.dist (fun _ => clamp01 θb)
      measurable_const (fun _ => clamp01_bdd θb)
  paySeller_integrable θs :=
    sel_density_integrable uniformBilateral.buyer.dist (fun _ => clamp01 θs / 2)
      measurable_const (fun _ => by
        rw [abs_div, abs_two]; have := clamp01_bdd θs; linarith [abs_nonneg (clamp01 θs)])
  payBuyer_jointMeasurable := clamp01_meas.comp measurable_fst
  paySeller_jointMeasurable := (clamp01_meas.comp measurable_snd).div_const 2
  payBuyer_jointIntegrable :=
    sel_jointIntegrable (fun p => clamp01 p.1) (clamp01_meas.comp measurable_fst)
      (fun p => clamp01_bdd p.1)
  paySeller_jointIntegrable :=
    sel_jointIntegrable (fun p => clamp01 p.2 / 2)
      ((clamp01_meas.comp measurable_snd).div_const 2)
      (fun p => by
        rw [abs_div, abs_two]; have := clamp01_bdd p.2; linarith [abs_nonneg (clamp01 p.2)])

/-- **The mean of the clamp under the uniform `[0,1]` is `1/2`.** The integrand `density·clamp01`
equals `density·id` *pointwise* (on `[0,1]` the clamp is the identity; outside, the density is `0`),
so the expectation matches `uniform_expect`. -/
private lemma expect_clamp01 : uniformEnv.dist.expect clamp01 = 1 / 2 := by
  have heq : uniformEnv.dist.expect clamp01 = uniformEnv.dist.expect id := by
    change (∫ x, uniformEnv.dist.density x * clamp01 x) = ∫ x, uniformEnv.dist.density x * id x
    refine congrArg _ (funext fun x => ?_)
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [clamp01_eq_self hx]; rfl
    · rw [uniformEnv.density_eq_zero_of_notMem hx, zero_mul, zero_mul]
  rw [heq, show uniformEnv.dist = ContDist.uniform 0 1 (by norm_num) from rfl,
    ContDist.uniform_expect]
  norm_num

/-- `affMech.buyerInterimPay θb = clamp θb` (the interim payment is constant in `θs`). -/
private lemma affMech_buyerInterimPay (θb : ℝ) : affMech.buyerInterimPay θb = clamp01 θb := by
  change uniformBilateral.seller.dist.expect (fun _ => clamp01 θb) = clamp01 θb
  rw [uniformBilateral_seller]; exact uniformEnv.dist.expect_const _

/-- `affMech.sellerInterimRecv θs = clamp θs / 2`. -/
private lemma affMech_sellerInterimRecv (θs : ℝ) :
    affMech.sellerInterimRecv θs = clamp01 θs / 2 := by
  change uniformBilateral.buyer.dist.expect (fun _ => clamp01 θs / 2) = clamp01 θs / 2
  rw [uniformBilateral_buyer]; exact uniformEnv.dist.expect_const _

/-- **Buyer's ex-ante expected payment is `1/2`**: the interim payment `P_b(θb) = clamp θb`
(constant in `θs`), averaged against the buyer law gives `𝔼[clamp θb] = 1/2`. A nonzero anchor the
zero-transfer `effMech` could not provide. -/
theorem affMech_buyerPay_total :
    uniformBilateral.buyer.dist.expect affMech.buyerInterimPay = 1 / 2 := by
  rw [uniformBilateral_buyer,
    show affMech.buyerInterimPay = clamp01 from funext affMech_buyerInterimPay, expect_clamp01]

/-- **Seller's ex-ante expected receipt is `1/4`**: the interim receipt `P_s(θs) = clamp θs / 2`,
averaged gives `𝔼[clamp θs]/2 = 1/4`. -/
theorem affMech_sellerRecv_total :
    uniformBilateral.seller.dist.expect affMech.sellerInterimRecv = 1 / 4 := by
  rw [uniformBilateral_seller,
    show affMech.sellerInterimRecv = (1 / 2 : ℝ) • clamp01 from
      funext fun θs => by rw [affMech_sellerInterimRecv]; simp [Pi.smul_apply]; ring,
    uniformEnv.dist.expect_smul, expect_clamp01]
  norm_num

/-- **`buyerPay_total_eq` (Fubini) anchored to a nonzero value `1/2`**: the iterated reduced-form
buyer payment equals the double integral against the joint law, both `1/2`. A swapped variable or
wrong product-measure order would change the iterated/double match away from `1/2` (the `effMech`
version was `0 = 0`, invisible to such bugs). -/
theorem affMech_buyerPay_total_eq_witness :
    uniformBilateral.buyer.dist.expect affMech.buyerInterimPay
      = ∫ θ, affMech.payBuyer θ.1 θ.2 ∂uniformBilateral.jointLaw :=
  affMech.buyerPay_total_eq

/-- **`sellerRecv_total_eq` (Fubini, seller-first order) anchored to `1/4`.** -/
theorem affMech_sellerRecv_total_eq_witness :
    uniformBilateral.seller.dist.expect affMech.sellerInterimRecv
      = ∫ θ, affMech.paySeller θ.1 θ.2 ∂uniformBilateral.jointLaw :=
  affMech.sellerRecv_total_eq

/-- **The ex-ante net budget is the asymmetric `1/4 > 0`**: `𝔼[payBuyer] − 𝔼[paySeller] =
1/2 − 1/4 = 1/4`. A sign flip in the net transfer (e.g. `paySeller − payBuyer`) would give `−1/4`,
which this anchor rejects. The double-integral forms come from the two Fubini bridges. -/
theorem affMech_net_budget_positive :
    (∫ θ, affMech.payBuyer θ.1 θ.2 ∂uniformBilateral.jointLaw)
      - ∫ θ, affMech.paySeller θ.1 θ.2 ∂uniformBilateral.jointLaw = 1 / 4 := by
  rw [← affMech_buyerPay_total_eq_witness, ← affMech_sellerRecv_total_eq_witness,
    affMech_buyerPay_total, affMech_sellerRecv_total]
  norm_num

/-- **`buyerInterimTrade_nonneg`** / **`buyerInterimTrade_le_one`** — the buyer's interim trade
probability lies in `[0, 1]`. -/
theorem buyerInterimTrade_mem_unitInterval (θb : ℝ) :
    0 ≤ effMech.buyerInterimTrade θb ∧ effMech.buyerInterimTrade θb ≤ 1 :=
  ⟨effMech.buyerInterimTrade_nonneg θb, effMech.buyerInterimTrade_le_one θb⟩

/-- **`sellerInterimTrade_nonneg`** / **`sellerInterimTrade_le_one`** — the seller's interim trade
probability lies in `[0, 1]`. -/
theorem sellerInterimTrade_mem_unitInterval (θs : ℝ) :
    0 ≤ effMech.sellerInterimTrade θs ∧ effMech.sellerInterimTrade θs ≤ 1 :=
  ⟨effMech.sellerInterimTrade_nonneg θs, effMech.sellerInterimTrade_le_one θs⟩

/-- **`buyerInterimTrade_eq_cdf` — efficiency pins the buyer's trade probability to `F_s`.** A
type-`θb` buyer trades with probability `F_s(θb)` (the seller's cost is below `θb`). Checked at the
**asymmetric** point `θb = 1/4`, giving `F_s(1/4) = 1/4` — *not* `1/2`. This catches a complement
flip: the survival value `1 − F_s(1/4) = 3/4 ≠ 1/4`, so a `1 − F_s` bug is no longer silent (the old
`θb = 1/2` anchor, where `F = 1 − F = 1/2`, could not distinguish them). -/
theorem buyerInterimTrade_eq_cdf_quarter :
    effMech.buyerInterimTrade (1 / 4) = 1 / 4 := by
  have hmem : (1 / 4 : ℝ) ∈ uniformBilateral.buyer.types := by
    rw [uniformBilateral_buyer]; exact ⟨by norm_num [uniformEnv], by norm_num [uniformEnv]⟩
  rw [effMech.buyerInterimTrade_eq_cdf effMech_efficient hmem]
  rw [uniformBilateral_seller, uniformEnv_cdf (by norm_num)]

/-- **`sellerInterimTrade_eq_survival` — efficiency pins the seller's trade probability to
`1 − F_b`.** A cost-`θs` seller trades with probability `1 − F_b(θs)` (the buyer's value is above
`θs`). Checked at the **asymmetric** point `θs = 3/4`: `1 − F_b(3/4) = 1/4` — *not* `1/2`. This
catches the CDF-vs-survival complement: the CDF value `F_b(3/4) = 3/4 ≠ 1/4`, so a `F_b`-instead-of-
`1 − F_b` bug fails here (unlike the old `θs = 1/2` anchor where both equal `1/2`). -/
theorem sellerInterimTrade_eq_survival_quarter :
    effMech.sellerInterimTrade (3 / 4) = 1 / 4 := by
  have hmem : (3 / 4 : ℝ) ∈ uniformBilateral.seller.types := by
    rw [uniformBilateral_seller]; exact ⟨by norm_num [uniformEnv], by norm_num [uniformEnv]⟩
  rw [effMech.sellerInterimTrade_eq_survival effMech_efficient hmem]
  rw [uniformBilateral_buyer, uniformEnv_cdf (by norm_num)]; norm_num

/-- **`buyerMech_isBIC`** — `BuyerBIC` is exactly the screening `IsBIC` of the buyer's reduced
mechanism. Stated for an *arbitrary* bilateral mechanism `M` satisfying `BuyerBIC`: The bridge
produces the screening `IsBIC` of its reduced mechanism. (We deliberately do **not** anchor this on
`effMech`, which is efficient but *not* buyer-IC — with zero payments a buyer would report the type
maximizing `Q_b = F_s` rather than truthfully — so anchoring there would make the hypothesis
unsatisfiable. This faithful conditional form exercises the bridge without a false premise.) -/
theorem buyerMech_isBIC_witness {Γ : BilateralEnv} (M : Γ.Mechanism) (h : M.BuyerBIC) :
    Econlib.MechanismDesign.Transfers.SingleParameter.IsBIC M.buyerMech :=
  M.buyerMech_isBIC h

/-- **`sellerMech_isBIC`** — `SellerBIC` is exactly the screening `IsBIC` of the seller's reflected
reduced mechanism. Stated for an arbitrary `M` satisfying `SellerBIC`, for the same reason as the
buyer bridge above. -/
theorem sellerMech_isBIC_witness {Γ : BilateralEnv} (M : Γ.Mechanism) (h : M.SellerBIC) :
    Econlib.MechanismDesign.Transfers.SingleParameter.IsBIC M.sellerMech :=
  M.sellerMech_isBIC h

/-! ### A concrete BIC mechanism: no trade, zero payments

To make the two BIC bridges **non-vacuous** we exhibit a concrete bilateral mechanism that is BIC:
the **no-trade** mechanism (`trade ≡ 0`, `payBuyer = paySeller ≡ 0`). All interim trade
probabilities and payments vanish, so the buyer/seller incentive constraints reduce to `0 ≤ 0`
(no report changes anything). This is the simplest genuine `BuyerBIC ∧ SellerBIC` witness, on which
both bridges are instantiated. -/

/-- The **no-trade, zero-payment** mechanism — trivially BIC. -/
private def noTradeMech : uniformBilateral.Mechanism where
  trade _ _ := 0
  trade_nonneg _ _ := le_refl 0
  trade_le_one _ _ := by norm_num
  trade_measurable_buyer _ := measurable_const
  trade_measurable_seller _ := measurable_const
  payBuyer _ _ := 0
  paySeller _ _ := 0
  payBuyer_integrable θb := by simp
  paySeller_integrable θs := by simp
  payBuyer_jointMeasurable := measurable_const
  paySeller_jointMeasurable := measurable_const
  payBuyer_jointIntegrable := by simp
  paySeller_jointIntegrable := by simp

/-- The no-trade mechanism's interim trade probability is `0` (the trade rule is `0`). -/
private lemma noTradeMech_buyerInterimTrade (θb : ℝ) : noTradeMech.buyerInterimTrade θb = 0 := by
  change uniformBilateral.seller.dist.expect (fun _ => (0 : ℝ)) = 0
  exact uniformEnv.dist.expect_const _

private lemma noTradeMech_buyerInterimPay (θb : ℝ) : noTradeMech.buyerInterimPay θb = 0 := by
  change uniformBilateral.seller.dist.expect (fun _ => (0 : ℝ)) = 0
  exact uniformEnv.dist.expect_const _

private lemma noTradeMech_sellerInterimTrade (θs : ℝ) : noTradeMech.sellerInterimTrade θs = 0 := by
  change uniformBilateral.buyer.dist.expect (fun _ => (0 : ℝ)) = 0
  exact uniformEnv.dist.expect_const _

private lemma noTradeMech_sellerInterimRecv (θs : ℝ) : noTradeMech.sellerInterimRecv θs = 0 := by
  change uniformBilateral.buyer.dist.expect (fun _ => (0 : ℝ)) = 0
  exact uniformEnv.dist.expect_const _

/-- The no-trade mechanism is **BuyerBIC**: every report gives the buyer interim utility `0`, so no
deviation is profitable (`0 ≤ 0`). -/
private theorem noTradeMech_buyerBIC : noTradeMech.BuyerBIC := by
  intro θb _ θb' _
  change θb * noTradeMech.buyerInterimTrade θb' - noTradeMech.buyerInterimPay θb'
    ≤ θb * noTradeMech.buyerInterimTrade θb - noTradeMech.buyerInterimPay θb
  rw [noTradeMech_buyerInterimTrade, noTradeMech_buyerInterimTrade, noTradeMech_buyerInterimPay,
    noTradeMech_buyerInterimPay]

/-- The no-trade mechanism is **SellerBIC** (symmetric argument, `0 ≤ 0`). -/
private theorem noTradeMech_sellerBIC : noTradeMech.SellerBIC := by
  intro θs _ θs' _
  change noTradeMech.sellerInterimRecv θs' - θs * noTradeMech.sellerInterimTrade θs'
    ≤ noTradeMech.sellerInterimRecv θs - θs * noTradeMech.sellerInterimTrade θs
  rw [noTradeMech_sellerInterimTrade, noTradeMech_sellerInterimTrade, noTradeMech_sellerInterimRecv,
    noTradeMech_sellerInterimRecv]

/-- **Concrete instantiation of `buyerMech_isBIC`**: the no-trade mechanism's reduced buyer
mechanism is screening-`IsBIC`, witnessed via the bridge with a (non-assumed) `BuyerBIC`
premise. -/
theorem noTradeMech_buyerMech_isBIC_witness :
    Econlib.MechanismDesign.Transfers.SingleParameter.IsBIC noTradeMech.buyerMech :=
  noTradeMech.buyerMech_isBIC noTradeMech_buyerBIC

/-- **Concrete instantiation of `sellerMech_isBIC`** on the no-trade mechanism. -/
theorem noTradeMech_sellerMech_isBIC_witness :
    Econlib.MechanismDesign.Transfers.SingleParameter.IsBIC noTradeMech.sellerMech :=
  noTradeMech.sellerMech_isBIC noTradeMech_sellerBIC

/-- **`buyerPay_total_eq`** — the buyer's ex-ante expected payment equals the double integral of
`payBuyer` against the joint law (Fubini). For `effMech` both are `0`. -/
theorem buyerPay_total_eq_witness :
    uniformBilateral.buyer.dist.expect effMech.buyerInterimPay
      = ∫ θ, effMech.payBuyer θ.1 θ.2 ∂uniformBilateral.jointLaw :=
  effMech.buyerPay_total_eq

/-- **`sellerRecv_total_eq`** — the seller's ex-ante expected receipt equals the double integral of
`paySeller` against the joint law (Fubini in the seller-first order). -/
theorem sellerRecv_total_eq_witness :
    uniformBilateral.seller.dist.expect effMech.sellerInterimRecv
      = ∫ θ, effMech.paySeller θ.1 θ.2 ∂uniformBilateral.jointLaw :=
  effMech.sellerRecv_total_eq

/-- **`weaklyBudgetBalanced_iff_budgetBalancedExAnte` — the Fubini bridge.** The iterated
reduced-form budget condition equals the genuine ex-ante product-measure expectation
`0 ≤ ∫ (payBuyer − paySeller)`. For `effMech` (zero transfers) it holds trivially. -/
theorem weaklyBudgetBalanced_iff_budgetBalancedExAnte_witness :
    effMech.WeaklyBudgetBalanced ↔ effMech.BudgetBalancedExAnte :=
  effMech.weaklyBudgetBalanced_iff_budgetBalancedExAnte

end EconlibTest.MechanismDesign.TransfersVCG

end
