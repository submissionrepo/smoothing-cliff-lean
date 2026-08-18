/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Environment

/-!
# Direct mechanisms

A `DirectMechanism` for a `QuasilinearEnvironment` maps reported type profiles to a social outcome
and a monetary transfer for each agent. By the revelation principle (Myerson 1981), this is without
loss of generality: Every equilibrium outcome of an arbitrary message-game mechanism is realized by
an incentive-compatible direct mechanism.

Agent `i`'s **ex-post utility** when its true type is `θ_i` and the reported profile is `report` is
quasilinear: `value i (alloc report) θ_i + transfer i report`. The transfer is money *received*, so
a payment charged to the agent enters with a negative sign.

## Main definitions

* `DirectMechanism`: An allocation rule and a per-agent transfer rule on reported type profiles.
* `DirectMechanism.exPostUtility`: Agent `i`'s realized quasilinear utility.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, direct mechanism, revelation principle, quasilinear utility
-/

@[expose] public section

open BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment}

/-- A direct (revelation) mechanism: Agents report types, and the mechanism chooses an outcome and
a monetary transfer for each agent as a function of the reported profile. -/
structure DirectMechanism (E : QuasilinearEnvironment) where
  /-- Allocation rule: The social outcome chosen at a reported type profile. -/
  alloc : E.TypeProfile → E.Outcome
  /-- Transfer rule: Net money received by agent `i` at a reported type profile. -/
  transfer : E.Agent → E.TypeProfile → ℝ

namespace DirectMechanism

variable (M : DirectMechanism E)

/-- Agent `i`'s ex-post quasilinear utility: Its valuation of the chosen outcome at its true type
`θ_i`, plus the transfer it receives, as a function of the reported profile. This is the library
quasilinear utility `E.quasilinearUtility i θ_i` evaluated at the chosen outcome and the
transfer. -/
def exPostUtility (i : E.Agent) (report : E.TypeProfile) (θ_i : E.Theta i) : ℝ :=
  (E.quasilinearUtility i θ_i).u (M.alloc report) (M.transfer i report)

@[simp] lemma exPostUtility_def (i : E.Agent) (report : E.TypeProfile) (θ_i : E.Theta i) :
    M.exPostUtility i report θ_i = E.value i (M.alloc report) θ_i + M.transfer i report := rfl

end DirectMechanism

end Econlib.MechanismDesign.Transfers.General
end
