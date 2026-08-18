/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.TypeDist
public import Econlib.Preferences.Utility.Quasilinear

/-!
# Quasilinear mechanism-design environments

A `QuasilinearEnvironment` packages the primitives of a finite mechanism-design problem with
transferable utility: A finite set of agents, a finite type space per agent, a finite set of social
outcomes, a per-agent valuation `value i outcome θ_i`, and a common prior over type profiles.
Utility is quasilinear: `uᵢ = valueᵢ + transferᵢ`, where `transfer i θ` is the net money *received*
by agent `i` (a tax is a negative transfer).

The instance battery (`Fintype`/`DecidableEq`/`Inhabited` on agents, type spaces, and outcomes) is
carried as named bracket fields. Well-formedness is part of the type; incentive compatibility,
individual rationality, efficiency, and budget balance are separate economic predicates.

## Main definitions

* `QuasilinearEnvironment`: Agents, type spaces, outcomes, valuations, and a common prior.
* `QuasilinearEnvironment.totalValue`: Utilitarian social value `∑ i, value i outcome (θ i)`.
* `QuasilinearEnvironment.welfareExcl`: Total value excluding agent `i` (the Groves base).

## Main statements

* `QuasilinearEnvironment.value_add_welfareExcl`: Total value splits into agent `i`'s own valuation
  plus the value accruing to all others.
* `QuasilinearEnvironment.welfareExcl_update`: `welfareExcl i` does not depend on the type reported
  by agent `i`.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, quasilinear, transferable utility, vcg, groves
-/

@[expose] public section

open Function BigOperators Econlib.Probability Econlib.GameTheory

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

/-- A finite quasilinear mechanism-design environment. Agents have private types drawn from finite
type spaces under a common prior, and share a finite outcome space. `value i outcome θ_i` is agent
`i`'s valuation of an outcome at its own type; utility is quasilinear in the monetary transfer. -/
structure QuasilinearEnvironment where
  /-- The (finite) set of agents. -/
  Agent : Type*
  /-- The (finite) set of social outcomes. -/
  Outcome : Type*
  /-- Agent `i`'s private type space. -/
  Theta : Agent → Type*
  /-- Agent `i`'s valuation of an outcome at its own type `θ_i`. -/
  value : (i : Agent) → Outcome → Theta i → ℝ
  [instFintypeAgent : Fintype Agent]
  [instDecEqAgent : DecidableEq Agent]
  [instInhabitedAgent : Inhabited Agent]
  [instFintypeTheta : ∀ i, Fintype (Theta i)]
  [instDecEqTheta : ∀ i, DecidableEq (Theta i)]
  [instInhabitedTheta : ∀ i, Inhabited (Theta i)]
  [instFintypeOutcome : Fintype Outcome]
  [instDecEqOutcome : DecidableEq Outcome]
  [instInhabitedOutcome : Inhabited Outcome]
  /-- Common prior over type profiles. -/
  prior : @TypeDist Agent instFintypeAgent instDecEqAgent Theta instFintypeTheta instDecEqTheta

attribute [instance] QuasilinearEnvironment.instFintypeAgent QuasilinearEnvironment.instDecEqAgent
  QuasilinearEnvironment.instInhabitedAgent QuasilinearEnvironment.instFintypeTheta
  QuasilinearEnvironment.instDecEqTheta QuasilinearEnvironment.instInhabitedTheta
  QuasilinearEnvironment.instFintypeOutcome QuasilinearEnvironment.instDecEqOutcome
  QuasilinearEnvironment.instInhabitedOutcome

namespace QuasilinearEnvironment

variable (E : QuasilinearEnvironment)

/-- A type profile assigns each agent a private type. -/
abbrev TypeProfile := Π i, E.Theta i

/-- Agent `i`'s quasilinear utility over outcomes at true type `θ_i`, as the library primitive
`Preferences.QuasilinearUtility` with valuation `o ↦ value i o θ_i`. The monetary transfer is
supplied by the mechanism at the assembly site (`DirectMechanism.exPostUtility`,
`TaxationPrinciple.menuUtility`), so it does not appear here. -/
def quasilinearUtility (i : E.Agent) (θ_i : E.Theta i) :
    Econlib.Preferences.QuasilinearUtility E.Outcome :=
  ⟨fun o => E.value i o θ_i⟩

@[simp] lemma quasilinearUtility_v (i : E.Agent) (θ_i : E.Theta i) (o : E.Outcome) :
    (E.quasilinearUtility i θ_i).v o = E.value i o θ_i := rfl

/-- Utilitarian social value of an outcome at a type profile: The sum of all agents' valuations. -/
def totalValue (outcome : E.Outcome) (θ : E.TypeProfile) : ℝ :=
  ∑ i, E.value i outcome (θ i)

@[simp] lemma totalValue_def (outcome : E.Outcome) (θ : E.TypeProfile) :
    E.totalValue outcome θ = ∑ i, E.value i outcome (θ i) := rfl

/-- Total value of an outcome excluding agent `i`. This is the base from which Groves payments
charge each agent the externality it imposes on the others. -/
def welfareExcl (i : E.Agent) (outcome : E.Outcome) (θ : E.TypeProfile) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, E.value j outcome (θ j)

@[simp] lemma welfareExcl_def (i : E.Agent) (outcome : E.Outcome) (θ : E.TypeProfile) :
    E.welfareExcl i outcome θ = ∑ j ∈ Finset.univ.erase i, E.value j outcome (θ j) := rfl

/-- Total value splits into agent `i`'s own valuation plus the value to everyone else. -/
lemma value_add_welfareExcl (i : E.Agent) (outcome : E.Outcome) (θ : E.TypeProfile) :
    E.value i outcome (θ i) + E.welfareExcl i outcome θ = E.totalValue outcome θ := by
  rw [welfareExcl_def, totalValue_def]
  exact Finset.add_sum_erase Finset.univ (fun j => E.value j outcome (θ j)) (Finset.mem_univ i)

/-- `welfareExcl i` ignores agent `i`'s own reported coordinate: Changing slot `i` does not affect
the value accruing to the others. This is the structural fact behind Groves dominant-strategy
incentive compatibility. -/
lemma welfareExcl_update (i : E.Agent) (outcome : E.Outcome) (θ : E.TypeProfile) (x : E.Theta i) :
    E.welfareExcl i outcome (Function.update θ i x) = E.welfareExcl i outcome θ := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end QuasilinearEnvironment

end Econlib.MechanismDesign.Transfers.General
end
