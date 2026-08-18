/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Groves.VCG

/-!
# Individual rationality and no-deficit for VCG

The Clarke pivot makes every VCG transfer nonpositive (each agent pays the externality it imposes),
so the mechanism never runs a deficit. Under a participation condition (all valuations nonnegative,
e.g. free disposal of a desirable good), VCG is also ex-post individually rational.

## Main statements

* `vcgMechanism_transfer_nonpos`: Each VCG transfer is `≤ 0`.
* `vcgMechanism_exPostUtility_of_nonpivotal`: A non-pivotal agent's truthful utility is its own
  valuation of the efficient outcome (its Clarke tax is zero).
* `vcgMechanism_isNoDeficit`: VCG runs no deficit.
* `vcgMechanism_isExPostIR`: Under `ParticipationCondition`, VCG is ex-post individually rational.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).
* Clarke, Edward H. 1971. “Multipart Pricing of Public Goods.” *Public Choice* 11 (1): 17–33.
  [https://doi.org/10.1007/bf01726210](https://doi.org/10.1007/bf01726210).

## Tags

vcg, individual rationality, no deficit, budget feasibility
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment}

/-- **Participation condition.** Every valuation is nonnegative — e.g. the outcome space includes a
"no-trade" option and the good is desirable, so opting out yields `0`. -/
def QuasilinearEnvironment.ParticipationCondition (E : QuasilinearEnvironment) : Prop :=
  ∀ (i : E.Agent) (o : E.Outcome) (θ_i : E.Theta i), 0 ≤ E.value i o θ_i

/-- Each VCG transfer is nonpositive: An agent receives the others' realized value minus the
maximal value they could have achieved without it, which the Clarke pivot dominates. -/
theorem vcgMechanism_transfer_nonpos (i : E.Agent) (θ : E.TypeProfile) :
    (vcgMechanism E).transfer i θ ≤ 0 := by
  have hle := E.welfareExcl_le_clarkePivot i (E.efficientAlloc θ) θ
  change E.welfareExcl i (E.efficientAlloc θ) θ - E.clarkePivot i θ ≤ 0
  linarith [hle]

/-- **A non-pivotal agent's truthful VCG utility is just its own valuation of the efficient
outcome.** An agent is *non-pivotal* at `report` when its presence does not change the welfare the
others can secure — i.e. the Clarke pivot equals the others' realized value at the efficient
outcome, `E.clarkePivot i report = E.welfareExcl i (E.efficientAlloc report) report`. Then its
Clarke tax is zero, so its ex-post utility (reporting truthfully) collapses to
`E.value i (E.efficientAlloc report) (report i)`: It consumes the efficient outcome at no charge.
This is the general-VCG analog of `vcg_loser_transfer` for the single-item case. -/
theorem vcgMechanism_exPostUtility_of_nonpivotal (i : E.Agent) (report : E.TypeProfile)
    (hnonpiv :
      E.clarkePivot i report = E.welfareExcl i (E.efficientAlloc report) report) :
    (vcgMechanism E).exPostUtility i report (report i)
      = E.value i (E.efficientAlloc report) (report i) := by
  rw [DirectMechanism.exPostUtility_def]
  -- The VCG transfer is `welfareExcl i o* report - clarkePivot i report`; non-pivotality makes the
  -- two welfare terms cancel, leaving `0`, so utility is the agent's own valuation alone.
  -- `(vcgMechanism E).alloc = E.efficientAlloc` and the transfer form hold by definition.
  change E.value i (E.efficientAlloc report) (report i)
      + (E.welfareExcl i (E.efficientAlloc report) report - E.clarkePivot i report) = _
  rw [hnonpiv, sub_self, add_zero]

/-- **VCG runs no deficit:** the sum of transfers (money paid out) is at most zero. -/
theorem vcgMechanism_isNoDeficit : (vcgMechanism E).IsNoDeficit := fun θ =>
  Finset.sum_nonpos fun i _ => vcgMechanism_transfer_nonpos i θ

/-- **VCG is ex-post individually rational** under the participation condition. -/
theorem vcgMechanism_isExPostIR (hpart : E.ParticipationCondition) :
    (vcgMechanism E).IsExPostIR := by
  intro i θ
  rw [vcgMechanism, grovesMechanism_exPostUtility, Function.update_eq_self]
  obtain ⟨o, ho⟩ := E.exists_clarkePivot_eq i θ
  have hsplit := E.value_add_welfareExcl i o θ
  have hbound : (vcgGrovesData E).h i θ ≤ E.totalValue o θ := by
    change E.clarkePivot i θ ≤ E.totalValue o θ
    rw [ho]; linarith [hpart i o (θ i), hsplit]
  have heff := E.efficientAlloc_isMaxOn θ o
  linarith [hbound, heff]

end Econlib.MechanismDesign.Transfers.General
end
