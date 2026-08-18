/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.WelfareFunction.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Properties of social welfare functions

Standard axiomatic properties of social welfare functions, comprising the conditions of Arrow's
impossibility theorem (Arrow 1963): **weak Pareto**, **independence of irrelevant alternatives**,
and **non-dictatorship**. Each property is stated relative to the welfare function's `domain`, so a
universal-domain assumption appears as a separate hypothesis on theorems that need it.

## Main definitions

* `WeakPareto`: Unanimous strict preference implies social strict preference.
* `StrongPareto`: Unanimous weak preference with at least one strict preference implies social
  strict preference.
* `ParetoIndifference`: Unanimous indifference implies social indifference.
* `IIA`: Society's ranking of `{x, y}` depends only on each voter's ranking of `{x, y}`.
* `IsDictator`: A voter whose strict preferences are always adopted by society.
* `NonDictatorship`: No voter is a dictator.
* `Anonymity`: Permuting voters leaves the social ranking unchanged.

## Notes

Because `PreferenceRel` admits ties, `≻` and `≽` are not Boolean duals. The axioms are therefore
stated in a form that survives indifference, and `IIA` is stated on both directions of `≽`.

## References

* Arrow, Kenneth J. 1963. *Social Choice and Individual Values*. 2nd ed. Wiley.

## Tags

social welfare function, pareto, independence of irrelevant alternatives, arrow, dictatorship,
anonymity
-/

@[expose] public section

namespace Econlib.SocialChoice.WelfareFunction

open Econlib.Preferences Econlib.SocialChoice

variable {Voter Alt : Type*}

/-- **Weak Pareto.** If every voter strictly prefers `x` to `y`, society does. -/
def WeakPareto (f : WelfareFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ x y : Alt,
    (∀ i, (P i).lt x y) → (f.aggregate P).lt x y

/-- **Strong Pareto.** If every voter weakly prefers `x` to `y` and at least one strictly does,
society strictly does. -/
def StrongPareto (f : WelfareFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ x y : Alt,
    (∀ i, (P i).le x y) → (∃ i, (P i).lt x y) → (f.aggregate P).lt x y

/-- **Pareto indifference.** If every voter is indifferent between `x` and `y`, society is. -/
def ParetoIndifference (f : WelfareFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ x y : Alt,
    (∀ i, (P i).indiff x y) → (f.aggregate P).indiff x y

/-- **Independence of irrelevant alternatives.** Society's pairwise ranking of `{x, y}` depends
only on each voter's pairwise ranking of `{x, y}`. -/
def IIA (f : WelfareFunction Voter Alt) : Prop :=
  ∀ P Q : Profile Voter Alt, P ∈ f.domain → Q ∈ f.domain →
    ∀ x y : Alt,
      (∀ i, ((P i).le x y ↔ (Q i).le x y) ∧ ((P i).le y x ↔ (Q i).le y x)) →
      ((f.aggregate P).le x y ↔ (f.aggregate Q).le x y) ∧
        ((f.aggregate P).le y x ↔ (f.aggregate Q).le y x)

/-- Voter `i` is a dictator: Society always inherits `i`'s strict preferences. -/
def IsDictator (f : WelfareFunction Voter Alt) (i : Voter) : Prop :=
  ∀ P ∈ f.domain, ∀ x y : Alt, (P i).lt x y → (f.aggregate P).lt x y

/-- **Non-dictatorship.** No voter is a dictator. -/
def NonDictatorship (f : WelfareFunction Voter Alt) : Prop :=
  ¬ ∃ i : Voter, IsDictator f i

/-- **Anonymity.** Permuting the voters does not change the social ranking. -/
def Anonymity [DecidableEq Voter] (f : WelfareFunction Voter Alt) : Prop :=
  ∀ P : Profile Voter Alt, P ∈ f.domain → ∀ σ : Equiv.Perm Voter,
    (P ∘ σ) ∈ f.domain → f.aggregate (P ∘ σ) = f.aggregate P

end Econlib.SocialChoice.WelfareFunction
