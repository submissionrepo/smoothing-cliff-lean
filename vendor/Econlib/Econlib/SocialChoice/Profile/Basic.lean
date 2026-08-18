/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic
public import Econlib.Preferences.Pareto
public import Mathlib.Logic.Function.Basic

/-!
# Preference profiles

A `Profile Voter Alt` assigns each voter a complete weak preference relation over alternatives.
Profiles are the input to social-welfare and social-choice functions. The `StrictPref` predicate
carves out preference relations whose only indifference classes are singletons; combined with the
totality of `PreferenceRel`, such a relation is a strict linear order.

This file also records profile-level Pareto dominance and optimality, the pointwise `update` and
`restrict` operations on profiles, and the pullback `comap` of a preference along a map of
alternatives.

## Main definitions

* `Profile` — a map from voters to weak preference relations over alternatives.
* `PreferenceRel.comap` — the pullback of a preference along `e : Alt' → Alt`.
* `StrictPref` — preference relations with no nontrivial indifference.
* `ParetoDominates` — the profile-level dominance relation: Every voter weakly prefers `x` and at
  least one strictly.
* `ParetoOptimal` — membership in the feasible set together with undominatedness within it.
* `Profile.update`, `Profile.restrict`, `Profile.IsStrict` — pointwise update at one voter,
  restriction along an embedding of alternatives, and the profilewise strictness predicate.

## Main statements

* `strictPref_preferenceOfUtilityIn` — a preference induced by an injective utility is strict.
* `StrictPref.lt_or_lt_of_ne` — under a strict preference, distinct alternatives are strictly
  comparable.
* `Profile.restrict_lt_iff` — restriction preserves every surviving pairwise comparison.
* `isStrict_of_injective_utilities` — a profile of utility-induced ballots is strict when each
  backing utility is injective.

## Tags

social choice, preference profile, strict preference, pareto dominance, pareto optimal
-/

@[expose] public section

namespace Econlib.Preferences.PreferenceRel

variable {Alt Alt' : Type*}

/-- Pull a preference back along a map `e : Alt' → Alt`: An alternative of the subtype is weakly
preferred to another iff its image under `e` is weakly preferred. Reflexivity, transitivity, and
totality transport directly from `R`. This underlies restricting an election to a subset of
candidates while keeping every surviving pairwise comparison. -/
def comap (e : Alt' → Alt) (R : PreferenceRel Alt) : PreferenceRel Alt' where
  le x y := R.le (e x) (e y)
  le_refl x := R.le_refl (e x)
  le_trans _ _ _ hxy hyz := R.le_trans _ _ _ hxy hyz
  le_total x y := R.le_total (e x) (e y)

@[simp] lemma comap_le_iff (e : Alt' → Alt) (R : PreferenceRel Alt) (x y : Alt') :
    (R.comap e).le x y ↔ R.le (e x) (e y) := Iff.rfl

/-- The strict part of a restricted preference: `x ≻ y` under `R.comap e` iff `e x ≻ e y` under
`R`. -/
@[simp] lemma comap_lt_iff (e : Alt' → Alt) (R : PreferenceRel Alt) (x y : Alt') :
    (R.comap e).lt x y ↔ R.lt (e x) (e y) := Iff.rfl

end Econlib.Preferences.PreferenceRel

namespace Econlib.SocialChoice

open Econlib.Preferences

/-- A preference profile assigns each voter a weak preference over alternatives. -/
abbrev Profile (Voter Alt : Type*) : Type _ := Voter → PreferenceRel Alt

/-- A preference relation is strict when it admits no nontrivial indifference. -/
def StrictPref {Alt : Type*} (R : PreferenceRel Alt) : Prop :=
  ∀ x y : Alt, (x ~[R] y) → x = y

/-- A preference induced by an injective utility is strict: Distinct alternatives receive distinct
utilities, so the only indifferences are reflexive. -/
lemma strictPref_preferenceOfUtilityIn {X U : Type*} [LinearOrder U] {u : X → U}
    (hu : Function.Injective u) : StrictPref (preferenceOfUtilityIn u) :=
  fun _ _ h => hu (le_antisymm h.2 h.1)

/-- Under a strict preference, distinct alternatives are strictly comparable. -/
lemma StrictPref.lt_or_lt_of_ne {Alt : Type*} {R : PreferenceRel Alt}
    (h : StrictPref R) {x y : Alt} (hxy : x ≠ y) :
    (x ≻[R] y) ∨ (y ≻[R] x) := by
  -- Trichotomy gives strict comparison in either direction or indifference;
  -- under `StrictPref` the indifference case forces `x = y`, contradicting `hxy`.
  rcases R.trichotomy x y with hlt | hgt | hindiff
  · exact Or.inl hlt
  · exact Or.inr hgt
  · exact absurd (h x y hindiff) hxy

/-- Restricting an injective embedding preserves strictness: Distinct sub-alternatives have
distinct images, so the only surviving indifferences come from `R`-indifferences, which
`StrictPref R` collapses. -/
lemma StrictPref.comap {Alt Alt' : Type*} {R : PreferenceRel Alt} (h : StrictPref R)
    {e : Alt' → Alt} (he : Function.Injective e) :
    StrictPref (R.comap e) :=
  fun x y hxy => he (h (e x) (e y) hxy)

/-! ## Pareto dominance and optimality over a profile

`ParetoDominates` is the profile-level dominance relation (every voter weakly prefers `x`, at
least one strictly), and `ParetoOptimal P S x` asks that `x ∈ S` be undominated within the feasible
set `S`. -/

/-- Alternative `x` Pareto dominates `y` under profile `P`: Every voter weakly prefers `x`, and at
least one strictly prefers it. -/
def ParetoDominates {Voter Alt : Type*} (P : Profile Voter Alt) (x y : Alt) : Prop :=
  Econlib.Preferences.ParetoDominates P (fun _ => x) (fun _ => y)

/-- Alternative `x` is Pareto optimal within `S` under profile `P`: It lies in `S` and no member of
`S` Pareto dominates it. -/
structure ParetoOptimal {Voter Alt : Type*} (P : Profile Voter Alt) (S : Set Alt) (x : Alt) :
    Prop where
  /-- The alternative is feasible. -/
  mem : x ∈ S
  /-- No feasible alternative Pareto dominates `x`. -/
  undominated : ¬ ∃ y ∈ S, ParetoDominates P y x

namespace Profile

/-- Pointwise updating of a profile at a single voter. -/
def update {Voter Alt : Type*} [DecidableEq Voter]
    (P : Profile Voter Alt) (i : Voter) (R : PreferenceRel Alt) :
    Profile Voter Alt :=
  Function.update P i R

/-- A profile is strict when every voter's ranking has no nontrivial indifference. -/
def IsStrict {Voter Alt : Type*} (P : Profile Voter Alt) : Prop :=
  ∀ i, Econlib.SocialChoice.StrictPref (P i)

/-- Restrict a profile over `Alt` to a profile over `Alt'` along an embedding `e : Alt' → Alt`:
Each voter's ballot is pulled back by `e` (`comap`). This compares the same electorate on a smaller
field of alternatives without touching any surviving pairwise comparison. -/
def restrict {Voter Alt Alt' : Type*} (e : Alt' → Alt) (P : Profile Voter Alt) :
    Profile Voter Alt' :=
  fun i => (P i).comap e

/-- **Restriction preserves every surviving pairwise comparison.** Voter `i` strictly prefers `x`
to `y` in the restricted profile iff they strictly prefer `e x` to `e y` in the original. -/
@[simp] lemma restrict_lt_iff {Voter Alt Alt' : Type*} (e : Alt' → Alt) (P : Profile Voter Alt)
    (i : Voter) (x y : Alt') :
    ((restrict e P) i).lt x y ↔ (P i).lt (e x) (e y) := Iff.rfl

/-- An injective restriction of a strict profile is strict. -/
lemma IsStrict.restrict {Voter Alt Alt' : Type*} {P : Profile Voter Alt} (hP : IsStrict P)
    {e : Alt' → Alt} (he : Function.Injective e) :
    IsStrict (Profile.restrict e P) :=
  fun i => (hP i).comap he

variable {Voter Alt : Type*} [DecidableEq Voter]

@[simp] lemma update_self (P : Profile Voter Alt) (i : Voter) (R : PreferenceRel Alt) :
    P.update i R i = R := by
  simp [update]

lemma update_of_ne (P : Profile Voter Alt) {i j : Voter} (hij : i ≠ j)
    (R : PreferenceRel Alt) : P.update i R j = P j := by
  simp [update, Function.update, hij.symm]

end Profile

/-- A profile of utility-induced ballots is strict whenever each voter's backing utility is
injective: Distinct alternatives carry distinct utilities, so the only indifferences are
reflexive. -/
lemma isStrict_of_injective_utilities {Voter Alt U : Type*} [LinearOrder U] {u : Voter → Alt → U}
    (hu : ∀ i, Function.Injective (u i)) :
    Profile.IsStrict (fun i => preferenceOfUtilityIn (u i)) :=
  fun i => strictPref_preferenceOfUtilityIn (hu i)

end Econlib.SocialChoice
