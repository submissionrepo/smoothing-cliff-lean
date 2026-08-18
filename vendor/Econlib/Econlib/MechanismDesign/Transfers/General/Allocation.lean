/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Groves.VCGProperties

/-!
# Single-item allocation environments

An `AllocationEnvironment` is a single-item auction environment: A finite set of agents, a finite
private type space per agent, a nonnegative valuation `bid i θ_i` for receiving the item, and a
common prior. The social outcome is which agent wins, so the induced `QuasilinearEnvironment`
(`toQuasilinear`) takes `Outcome := Agent`. Specializing the resulting Vickrey–Clarke–Groves
mechanism gives the second-price auction.

## Main definitions

* `AllocationEnvironment`: A single-item environment — agents, type spaces, a nonneg valuation
  `bid`, and a common prior. `Outcome := Agent` is supplied by `toQuasilinear`.
* `AllocationEnvironment.toQuasilinear`: The induced `QuasilinearEnvironment`.

## Main statements

* `toQuasilinear_totalValue`: Social value at outcome `o` is the winner's bid `bid o (θ o)`.
* `toQuasilinear_welfareExcl`: The others' value is `0` if `i` wins, else the winner's bid.
* `toQuasilinear_clarkePivot`: The Clarke pivot equals the highest competing bid.
* `vcg_winner_transfer` / `vcg_loser_transfer`: A winner pays the second-highest bid; a loser pays
  nothing.
* `toQuasilinear_participation`: Every single-item environment satisfies the participation
  condition.

## Notes

A general `QuasilinearEnvironment` keeps the agent set and the outcome set as independent type
fields, the right generality for public-good problems (`Outcome := Bool ≠ Agent`). Setting
`Outcome := Agent` on such an environment would introduce two `DecidableEq` instances on the same
carrier (`instDecEqAgent` and `instDecEqOutcome`), causing an instance diamond in the VCG payment
computation. `AllocationEnvironment` instead carries a single `Agent` type with a single
`DecidableEq`; the outcome type `Outcome := Agent` is introduced only inside `toQuasilinear`, so
all lemmas about `value`, `totalValue`, `welfareExcl`, `clarkePivot`, and VCG transfers resolve
against the same instance.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, single-item auction, vcg, vickrey, second price, clarke pivot
-/

@[expose] public section

open Function BigOperators Econlib.Probability Econlib.GameTheory

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

/-- A finite **single-item allocation environment**: A set of agents, a private type space per
agent, and a nonneg valuation `bid i θ_i` for receiving the item. The social outcome is which agent
wins; the induced `QuasilinearEnvironment` (`toQuasilinear`) takes `Outcome := Agent` with a single
`DecidableEq`. -/
structure AllocationEnvironment where
  /-- The (finite) set of agents. -/
  Agent : Type*
  /-- Agent `i`'s private type space. -/
  Theta : Agent → Type*
  /-- Agent `i`'s valuation of receiving the item at its own type `θ_i`. -/
  bid : (i : Agent) → Theta i → ℝ
  /-- Valuations are nonnegative (free disposal); this gives the participation condition / IR. -/
  bid_nonneg : ∀ (i : Agent) (θ_i : Theta i), 0 ≤ bid i θ_i
  [instFintypeAgent : Fintype Agent]
  [instDecEqAgent : DecidableEq Agent]
  [instInhabitedAgent : Inhabited Agent]
  [instFintypeTheta : ∀ i, Fintype (Theta i)]
  [instDecEqTheta : ∀ i, DecidableEq (Theta i)]
  [instInhabitedTheta : ∀ i, Inhabited (Theta i)]
  /-- Common prior over type profiles. -/
  prior : @TypeDist Agent instFintypeAgent instDecEqAgent Theta instFintypeTheta instDecEqTheta

attribute [instance] AllocationEnvironment.instFintypeAgent AllocationEnvironment.instDecEqAgent
  AllocationEnvironment.instInhabitedAgent AllocationEnvironment.instFintypeTheta
  AllocationEnvironment.instDecEqTheta AllocationEnvironment.instInhabitedTheta

namespace AllocationEnvironment

variable (A : AllocationEnvironment)

/-- The induced quasilinear environment: Outcomes are agents (who wins), and agent `i` values
outcome `o` at its bid if `o = i` and at `0` otherwise. -/
def toQuasilinear : QuasilinearEnvironment where
  Agent := A.Agent
  Outcome := A.Agent
  Theta := A.Theta
  value i o θ_i := if o = i then A.bid i θ_i else 0
  prior := A.prior

@[simp] lemma toQuasilinear_value (i o : A.Agent) (θ_i : A.Theta i) :
    A.toQuasilinear.value i o θ_i = if o = i then A.bid i θ_i else 0 := rfl

/-- A type profile of the single-item environment. -/
abbrev TypeProfile := A.toQuasilinear.TypeProfile

/-- **Social value is the winner's bid.** Only the winning agent `o` derives value at outcome `o`,
so the utilitarian total collapses to that single term. -/
lemma toQuasilinear_totalValue (o : A.Agent) (θ : A.TypeProfile) :
    A.toQuasilinear.totalValue o θ = A.bid o (θ o) := by
  rw [QuasilinearEnvironment.totalValue]
  refine (Finset.sum_eq_single_of_mem o (Finset.mem_univ o)
    (fun k _ hko => by rw [toQuasilinear_value, if_neg (Ne.symm hko)])).trans ?_
  rw [toQuasilinear_value, if_pos rfl]

/-- **The value accruing to the others** at outcome `o`: Zero if agent `i` wins, the winner's bid
otherwise. -/
lemma toQuasilinear_welfareExcl (i o : A.Agent) (θ : A.TypeProfile) :
    A.toQuasilinear.welfareExcl i o θ = if o = i then 0 else A.bid o (θ o) := by
  rw [QuasilinearEnvironment.welfareExcl]
  by_cases h : o = i
  · rw [if_pos h]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [toQuasilinear_value, if_neg fun hok => (Finset.mem_erase.mp hk).1 (hok.symm.trans h)]
  · rw [if_neg h]
    refine (Finset.sum_eq_single_of_mem o (Finset.mem_erase.mpr ⟨h, Finset.mem_univ o⟩)
      (fun k _ hko => by rw [toQuasilinear_value, if_neg (Ne.symm hko)])).trans ?_
    rw [toQuasilinear_value, if_pos rfl]

/-- Valuations are nonneg, so every single-item allocation environment satisfies the participation
condition. -/
lemma toQuasilinear_participation : A.toQuasilinear.ParticipationCondition := by
  intro i o θ_i
  rw [toQuasilinear_value]
  split_ifs
  · exact A.bid_nonneg i θ_i
  · exact le_refl 0

/-- The efficient single-item allocation gives the item to a **highest bidder**: Total value at the
efficient outcome dominates every agent's bid. -/
lemma bid_le_efficientAlloc_bid (θ : A.TypeProfile) (o : A.Agent) :
    A.bid o (θ o)
      ≤ A.bid (A.toQuasilinear.efficientAlloc θ) (θ (A.toQuasilinear.efficientAlloc θ)) := by
  have h := A.toQuasilinear.efficientAlloc_isMaxOn θ o
  rwa [toQuasilinear_totalValue, toQuasilinear_totalValue] at h

/-- The Clarke pivot equals the highest competing bid (`0` as a floor from the winning agent's own
slot). -/
lemma toQuasilinear_clarkePivot (i : A.Agent) (θ : A.TypeProfile) :
    A.toQuasilinear.clarkePivot i θ
      = Finset.univ.sup' Finset.univ_nonempty (fun o => if o = i then 0 else A.bid o (θ o)) := by
  rw [QuasilinearEnvironment.clarkePivot]
  refine Finset.sup'_congr _ rfl fun o _ => ?_
  rw [toQuasilinear_welfareExcl]

/-- **A winning bidder pays its Clarke pivot** — the highest competing bid, i.e. the second-highest
bid overall. -/
lemma vcg_winner_transfer (i : A.Agent) (θ : A.TypeProfile)
    (hwin : A.toQuasilinear.efficientAlloc θ = i) :
    (vcgMechanism A.toQuasilinear).transfer i θ = -A.toQuasilinear.clarkePivot i θ := by
  change A.toQuasilinear.welfareExcl i (A.toQuasilinear.efficientAlloc θ) θ
      - A.toQuasilinear.clarkePivot i θ = _
  rw [hwin, toQuasilinear_welfareExcl, if_pos rfl, zero_sub]

/-- **A losing bidder pays nothing.** -/
lemma vcg_loser_transfer (i : A.Agent) (θ : A.TypeProfile)
    (hlose : A.toQuasilinear.efficientAlloc θ ≠ i) :
    (vcgMechanism A.toQuasilinear).transfer i θ = 0 := by
  have hw : A.toQuasilinear.welfareExcl i (A.toQuasilinear.efficientAlloc θ) θ
      = A.bid (A.toQuasilinear.efficientAlloc θ) (θ (A.toQuasilinear.efficientAlloc θ)) := by
    rw [toQuasilinear_welfareExcl]
    split_ifs with h
    · exact absurd h hlose
    · rfl
  have hpiv : A.toQuasilinear.clarkePivot i θ
      = A.bid (A.toQuasilinear.efficientAlloc θ) (θ (A.toQuasilinear.efficientAlloc θ)) := by
    refine le_antisymm (Finset.sup'_le _ _ fun o _ => ?_) ?_
    · rw [toQuasilinear_welfareExcl]
      split_ifs with h
      · exact A.bid_nonneg _ _
      · exact A.bid_le_efficientAlloc_bid θ o
    · rw [← hw]; exact A.toQuasilinear.welfareExcl_le_clarkePivot i _ θ
  change A.toQuasilinear.welfareExcl i (A.toQuasilinear.efficientAlloc θ) θ
      - A.toQuasilinear.clarkePivot i θ = 0
  rw [hw, hpiv, sub_self]

end AllocationEnvironment

end Econlib.MechanismDesign.Transfers.General
end
