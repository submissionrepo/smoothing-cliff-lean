/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Representation.Finite
public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Econlib.SocialChoice.Profile.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card

/-!
# Plurality

Defines the **plurality** voting rule as a `ChoiceFunction`. A voter's ballot is their top-ranked
alternative under their preference relation. Under indifference, ties within a voter's top set are
broken deterministically by the lex-minimum of a `LinearOrder Alt` instance.

## Main definitions

* `topSet` — the set of alternatives weakly preferred to all others under a given preference.
* `topPick` — the lex-minimum of a voter's top set.
* `pluralityScore` — the number of voters whose top pick is a given alternative.
* `pluralityWinners` — the set of alternatives achieving the maximum plurality score.
* `pluralityRule` — the plurality social choice function.

## Main statements

* `topSet_eq_singleton`, `topPick_eq` — under a strict preference the top set is a singleton and
  `topPick` returns its weakly-top element.
* `topSet_nonempty`, `pluralityWinners_nonempty` — the top set and the winner set are nonempty.
* `pluralityScore_eq_card`, `mem_pluralityWinners` — the plurality score and winner-membership read
  off explicit sets.

## Tags

social choice, voting, plurality
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Alt : Type*} [Fintype Alt]

/-- The set of alternatives weakly preferred to all others under `R`.

Noncomputable by design: The filter predicate `∀ b, R.le a b` is `Prop`-valued over the abstract
`PreferenceRel.le` and is decided classically rather than via a threaded `Decidable` bracket field
(see `majorityCount` for the full rationale; the same applies to
`pluralityScore`/`pluralityWinners` below). -/
noncomputable def topSet (R : PreferenceRel Alt) : Finset Alt :=
  letI : DecidablePred (fun a : Alt => ∀ b : Alt, R.le a b) := Classical.decPred _
  Finset.univ.filter (fun a : Alt => ∀ b : Alt, R.le a b)

lemma mem_topSet {R : PreferenceRel Alt} {a : Alt} :
    a ∈ topSet R ↔ ∀ b : Alt, R.le a b := by
  letI : DecidablePred (fun a : Alt => ∀ b : Alt, R.le a b) := Classical.decPred _
  rw [topSet, Finset.mem_filter_univ]

/-- Under a strict preference, if `m` is weakly top (i.e., `R.le m b` for all `b`), then the top
set collapses to `{m}`. -/
lemma topSet_eq_singleton {R : PreferenceRel Alt} (hR : StrictPref R) {m : Alt}
    (hm : ∀ b : Alt, R.le m b) : topSet R = {m} := by
  ext a
  rw [mem_topSet, Finset.mem_singleton]
  constructor
  · intro ha
    exact hR a m ⟨ha m, hm a⟩
  · rintro rfl
    exact hm

/-- The top set is nonempty under any `PreferenceRel` over a nonempty fintype: A total preorder has
a greatest element on a finite nonempty set. -/
lemma topSet_nonempty [Nonempty Alt] (R : PreferenceRel Alt) :
    (topSet R).Nonempty := by
  obtain ⟨a, -, ha_max⟩ := R.exists_greatest_on Set.univ_nonempty
  exact ⟨a, mem_topSet.mpr (fun b => ha_max b trivial)⟩

variable [LinearOrder Alt]

/-- Voter `i`'s deterministic top pick: The lex-minimum of their top set. -/
noncomputable def topPick [Nonempty Alt] (R : PreferenceRel Alt) : Alt :=
  Finset.min' (topSet R) (topSet_nonempty R)

/-- Under a strict preference, if `m` is weakly top, then `topPick R = m`. -/
lemma topPick_eq [Nonempty Alt] {R : PreferenceRel Alt} (hR : StrictPref R) {m : Alt}
    (hm : ∀ b : Alt, R.le m b) : topPick R = m := by
  rw [topPick]
  simp [topSet_eq_singleton hR hm]

variable {Voter : Type*} [Fintype Voter]

/-- The plurality score of `a` under profile `P`: Number of voters whose deterministic top pick is
`a`. -/
noncomputable def pluralityScore [Nonempty Alt] (P : Profile Voter Alt) (a : Alt) : ℕ :=
  letI : DecidablePred (fun i : Voter => topPick (P i) = a) := Classical.decPred _
  (Finset.univ.filter (fun i : Voter => topPick (P i) = a)).card

/-- If `s` is the set of voters whose top pick is `a`, then `pluralityScore P a = s.card`. -/
lemma pluralityScore_eq_card [Nonempty Alt] (P : Profile Voter Alt) (a : Alt)
    (s : Finset Voter) (h : ∀ i, topPick (P i) = a ↔ i ∈ s) :
    pluralityScore P a = s.card := by
  classical
  unfold pluralityScore
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

/-- The set of alternatives maximizing the plurality score. -/
noncomputable def pluralityWinners [Nonempty Alt] (P : Profile Voter Alt) :
    Finset Alt :=
  letI : DecidablePred (fun a : Alt =>
      ∀ b : Alt, pluralityScore P b ≤ pluralityScore P a) := Classical.decPred _
  Finset.univ.filter (fun a : Alt =>
    ∀ b : Alt, pluralityScore P b ≤ pluralityScore P a)

lemma mem_pluralityWinners [Nonempty Alt] {P : Profile Voter Alt} {a : Alt} :
    a ∈ pluralityWinners P ↔
      ∀ b : Alt, pluralityScore P b ≤ pluralityScore P a := by
  letI : DecidablePred (fun a : Alt =>
      ∀ b : Alt, pluralityScore P b ≤ pluralityScore P a) := Classical.decPred _
  rw [pluralityWinners, Finset.mem_filter_univ]

lemma pluralityWinners_nonempty [Nonempty Alt] (P : Profile Voter Alt) :
    (pluralityWinners P).Nonempty := by
  obtain ⟨a, _, ha_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Alt) (fun a => pluralityScore P a)
      Finset.univ_nonempty
  exact ⟨a, mem_pluralityWinners.mpr (fun b => ha_max b (Finset.mem_univ _))⟩

/-- The plurality social choice function: The winners are the alternatives maximizing the plurality
score. Ties are reported as a multi-element set. -/
noncomputable def pluralityRule [Nonempty Alt] :
    ChoiceFunction Voter Alt where
  domain := Set.univ
  winners := fun P => ↑(pluralityWinners P)
  winners_nonempty := fun P _ => Finset.coe_nonempty.mpr (pluralityWinners_nonempty P)

end Econlib.SocialChoice
