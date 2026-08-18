/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Groves.Payments

/-!
# Groves mechanisms are efficient and dominant-strategy incentive compatible

Every Groves mechanism implements the efficient allocation in dominant strategies.

## Main statements

* `grovesMechanism_exPostUtility`: Closed form for an agent's Groves utility.
* `grovesMechanism_isEfficient`: The Groves allocation maximizes total value.
* `grovesMechanism_isDSIC`: Truth-telling is a dominant strategy.

## References

* Groves, Theodore. 1973. “Incentives in Teams.” *Econometrica* 41 (4): 617.
  [https://doi.org/10.2307/1914085](https://doi.org/10.2307/1914085).

## Tags

groves mechanism, dominant strategy, dsic, efficiency
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment} (g : GrovesData E)

/-- Closed form for an agent's ex-post utility in a Groves mechanism: Total value at the welfare
profile (own true type spliced into the report) minus the own-report-independent offset. -/
lemma grovesMechanism_exPostUtility
    (i : E.Agent) (report : E.TypeProfile) (θ_i : E.Theta i) :
    (grovesMechanism g).exPostUtility i report θ_i
      = E.totalValue (E.efficientAlloc report) (update report i θ_i) - g.h i report := by
  exact exPostUtility_eq_totalValue_update_sub i (E.efficientAlloc report) report θ_i (g.h i report)

/-- The Groves allocation maximizes total value at every reported profile. -/
theorem grovesMechanism_isEfficient : (grovesMechanism g).IsEfficient :=
  fun θ o => E.efficientAlloc_isMaxOn θ o

/-- **Groves mechanisms are dominant-strategy incentive compatible** (Groves 1973). For any reports
of the other agents, an agent's truthful report maximizes its ex-post utility. -/
theorem grovesMechanism_isDSIC : (grovesMechanism g).IsDSIC := by
  intro i r θ_i θ_i'
  rw [grovesMechanism_exPostUtility, grovesMechanism_exPostUtility,
    update_idem, update_idem]
  rw [g.h_indep i r θ_i' θ_i]
  have hmax := E.efficientAlloc_isMaxOn (update r i θ_i) (E.efficientAlloc (update r i θ_i'))
  linarith [hmax]

end Econlib.MechanismDesign.Transfers.General
end
