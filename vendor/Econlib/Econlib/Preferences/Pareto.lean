/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic

/-!
# Componentwise Pareto dominance

`ParetoDominates R x y` is the welfare kernel shared by social choice and general equilibrium.
Given an index `I` of agents, a preference profile `R : I → PreferenceRel β`, and two outcome
profiles `x y : I → β`, the outcome profile `x` Pareto dominates `y` when every agent weakly
prefers its own `x`-component and at least one strictly prefers it.

## Main definitions

* `ParetoDominates` — componentwise Pareto dominance of one outcome profile over another.

## Main statements

* `not_paretoDominates_self` — Pareto dominance is irreflexive.

## Notes

Two specializations recur, both building on this single definition rather than re-deriving welfare
comparisons. Social choice evaluates a shared pair `x₀ y₀ : β` at every agent — the constant case
`ParetoDominates R (fun _ => x₀) (fun _ => y₀)` (`Econlib.SocialChoice.ParetoDominates`). Exchange
and production economies evaluate agent-specific bundles `x a, y a` under agent-specific
preferences (`Econlib.Equilibrium.Economy.ParetoDominates` and friends).

## Tags

pareto dominance, welfare, preference profile
-/

@[expose] public section

namespace Econlib.Preferences

/-- Componentwise Pareto dominance: Outcome profile `x` Pareto dominates `y` under the preference
profile `R` when every agent weakly prefers its `x`-component and at least one strictly prefers
it. -/
def ParetoDominates {I β : Type*} (R : I → PreferenceRel β) (x y : I → β) : Prop :=
  (∀ i, x i ≽[R i] y i) ∧ ∃ i, x i ≻[R i] y i

/-- Pareto dominance is irreflexive: No outcome profile Pareto dominates itself, since any strict
improvement would require some agent to strictly prefer a component to itself. -/
lemma not_paretoDominates_self {I β : Type*} (R : I → PreferenceRel β) (x : I → β) :
    ¬ ParetoDominates R x x := by
  rintro ⟨-, i, hi⟩
  exact (R i).lt_irrefl (x i) hi

end Econlib.Preferences
