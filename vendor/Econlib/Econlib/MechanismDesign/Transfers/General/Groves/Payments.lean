/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.SolutionConcepts

/-!
# Groves mechanisms

A **Groves mechanism** chooses an efficient (total-value-maximizing) allocation and pays each agent
the realized value to the other agents, offset by a function `h i` of the others' reports alone.
Because `h i` is independent of agent `i`'s own report and the allocation is efficient, each
agent's ex-post utility equals total welfare minus an own-report-independent term — so
truth-telling is a dominant strategy.

## Main definitions

* `QuasilinearEnvironment.efficientAlloc`: A total-value-maximizing outcome at each profile.
* `GrovesData`: The offset family `h i` with the independence-of-own-report constraint baked in.
* `grovesMechanism`: The direct mechanism with efficient allocation and Groves transfers.

## Main statements

* `efficientAlloc_isMaxOn`: The efficient allocation maximizes total value.
* `grovesMechanism_exPostUtility`: An agent's Groves utility equals total value at the welfare
  profile minus the own-report-independent offset.

## References

* Groves, Theodore. 1973. “Incentives in Teams.” *Econometrica* 41 (4): 617.
  [https://doi.org/10.2307/1914085](https://doi.org/10.2307/1914085).

## Tags

groves mechanism, efficiency, vcg, dominant strategy
-/
@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

namespace QuasilinearEnvironment

variable (E : QuasilinearEnvironment)

/-- A total-value-maximizing outcome at a reported profile. Well-defined because the outcome space
is a nonempty finite type. -/
def efficientAlloc (θ : E.TypeProfile) : E.Outcome :=
  (Finite.exists_max (fun o => E.totalValue o θ)).choose

/-- The efficient allocation maximizes total value: No outcome attains more total value at the
reported profile. -/
lemma efficientAlloc_isMaxOn (θ : E.TypeProfile) (o : E.Outcome) :
    E.totalValue o θ ≤ E.totalValue (E.efficientAlloc θ) θ :=
  (Finite.exists_max (fun o => E.totalValue o θ)).choose_spec o

end QuasilinearEnvironment

variable {E : QuasilinearEnvironment}

/-- The data of a Groves mechanism: An offset `h i` for each agent that may depend on the full
reported profile but not on agent `i`'s own report. The independence constraint is a field, so a
malformed Groves mechanism is inexpressible. -/
structure GrovesData (E : QuasilinearEnvironment) where
  /-- Offset charged to agent `i`, a function of the others' reports. -/
  h : E.Agent → E.TypeProfile → ℝ
  /-- `h i` does not depend on agent `i`'s own reported coordinate. -/
  h_indep : ∀ (i : E.Agent) (r : E.TypeProfile) (θ_i θ_i' : E.Theta i),
    h i (update r i θ_i) = h i (update r i θ_i')

/-- The Groves mechanism associated to offset data `g`: Allocate efficiently and pay each agent the
value accruing to the others, minus `g.h i`. -/
def grovesMechanism (g : GrovesData E) : DirectMechanism E where
  alloc := E.efficientAlloc
  transfer i θ := E.welfareExcl i (E.efficientAlloc θ) θ - g.h i θ

/-- An agent's ex-post utility under a transfer of the form "value to others minus an offset"
equals total value at the welfare profile (own true type spliced into the reported profile) minus
the offset. -/
lemma exPostUtility_eq_totalValue_update_sub
    (i : E.Agent) (o : E.Outcome) (report : E.TypeProfile) (θ_i : E.Theta i) (c : ℝ) :
    E.value i o θ_i + (E.welfareExcl i o report - c)
      = E.totalValue o (update report i θ_i) - c := by
  -- Splice `θ_i` into the profile: `welfareExcl` is own-report independent, and adding back
  -- `i`'s value recovers `totalValue` at the spliced profile.
  have hsplit := E.value_add_welfareExcl i o (update report i θ_i)
  rw [update_self, E.welfareExcl_update] at hsplit
  linarith [hsplit]

end Econlib.MechanismDesign.Transfers.General
end
