/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Econlib.SocialChoice.Profile.Basic
public import Econlib.SocialChoice.Rule.Borda
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card

/-!
# Resolute scoring rules

A **resolute** social choice rule returns a single winner on every admissible profile. The generic
construction here resolves a `score : Alt → σ` (any `LinearOrder`-valued score, in practice the
total Borda or plurality score) to a unique winner by a deterministic lexicographic tie-break:
Among the `score`-maximizers, take the `Finset.min'` under a `LinearOrder Alt`. Resolute rules are
the setting for the Gibbard–Satterthwaite theorem (Gibbard 1973; Satterthwaite 1975), and
`resoluteBorda` is the canonical rule behind its manipulation examples.

## Main definitions

* `scoreArgmax`: The `Finset` of `score`-maximal alternatives.
* `scoreWinner`: The lexicographically smallest `score`-maximizer (the resolute winner).
* `ChoiceFunction.resoluteOf`: Package a per-profile score into a resolute `ChoiceFunction` whose
  winners-set is the singleton `{scoreWinner …}`.
* `resoluteBorda`: Borda count made resolute on the strict domain, ranking by total Borda score and
  breaking ties lexicographically.

## Main statements

* `scoreWinner_mem`, `scoreWinner_max`: The winner is a `score`-maximizer.
* `scoreWinner_eq_of_strict_max`: If `w` is the strict `score`-maximizer, it is the winner and the
  tie-break never fires.
* `ChoiceFunction.resoluteOf_resolute`: A resolute rule has at most one winner on every admissible
  profile.

## References

* Gibbard, Allan. 1973. “Manipulation of Voting Schemes: A General Result.” *Econometrica* 41 (4):
  587. [https://doi.org/10.2307/1914083](https://doi.org/10.2307/1914083).
* Satterthwaite, Mark Allen. 1975. “Strategy-Proofness and Arrow's Conditions: Existence and
  Correspondence Theorems for Voting Procedures and Social Welfare Functions.” *Journal of Economic
  Theory* 10 (2): 187–217. [https://doi.org/10.1016/0022-0531(75)90050-2](https://doi.org/10.1016/0022-0531(75)90050-2).

## Tags

social choice, resolute, tie-break, argmax, scoring rule, borda
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Alt : Type*} [Fintype Alt] [Nonempty Alt]

/-! ### The argmax of a score function -/

/-- The set of alternatives maximizing `score`.

Noncomputable by design: The `∀`-quantified comparison predicate is decided classically rather than
via a threaded `Decidable` bracket field, matching the convention of the other scoring rules (see
`majorityCount` in `Rule/Majority.lean` for the rationale). -/
noncomputable def scoreArgmax {σ : Type*} [LinearOrder σ] (score : Alt → σ) : Finset Alt :=
  letI : DecidablePred (fun a : Alt => ∀ b : Alt, score b ≤ score a) := Classical.decPred _
  Finset.univ.filter (fun a : Alt => ∀ b : Alt, score b ≤ score a)

omit [Nonempty Alt] in
lemma mem_scoreArgmax {σ : Type*} [LinearOrder σ] {score : Alt → σ} {a : Alt} :
    a ∈ scoreArgmax score ↔ ∀ b : Alt, score b ≤ score a := by
  letI : DecidablePred (fun a : Alt => ∀ b : Alt, score b ≤ score a) := Classical.decPred _
  rw [scoreArgmax, Finset.mem_filter_univ]

/-- The argmax is nonempty: A finite nonempty type has a score-maximal element. -/
lemma scoreArgmax_nonempty {σ : Type*} [LinearOrder σ] (score : Alt → σ) :
    (scoreArgmax score).Nonempty := by
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Alt) score Finset.univ_nonempty
  exact ⟨a, mem_scoreArgmax.mpr (fun b => ha b (Finset.mem_univ _))⟩

/-! ### The resolute winner -/

variable [LinearOrder Alt]

/-- The resolute winner of a score function: The lexicographically smallest `score`-maximizer. -/
noncomputable def scoreWinner {σ : Type*} [LinearOrder σ] (score : Alt → σ) : Alt :=
  (scoreArgmax score).min' (scoreArgmax_nonempty score)

/-- The resolute winner is a `score`-maximizer. -/
lemma scoreWinner_mem {σ : Type*} [LinearOrder σ] (score : Alt → σ) :
    scoreWinner score ∈ scoreArgmax score :=
  Finset.min'_mem _ _

/-- The resolute winner achieves the maximum score. -/
lemma scoreWinner_max {σ : Type*} [LinearOrder σ] (score : Alt → σ) (b : Alt) :
    score b ≤ score (scoreWinner score) :=
  mem_scoreArgmax.mp (scoreWinner_mem score) b

/-- **Strict maximizer determines the resolute winner.** If `score` agrees with the explicit table
`s` and `w` strictly maximizes `s` (every other alternative scores strictly lower), then
`scoreWinner score = w`. -/
lemma scoreWinner_eq_of_strict_max {σ : Type*} [LinearOrder σ] (score : Alt → σ) (s : Alt → σ)
    (hs : ∀ a, score a = s a) {w : Alt} (hw : ∀ b, b ≠ w → s b < s w) :
    scoreWinner score = w := by
  have hargmax : scoreArgmax score = {w} := by
    ext a
    rw [mem_scoreArgmax, Finset.mem_singleton]
    constructor
    · intro hmax
      by_contra ha
      have hb := hmax w
      rw [hs a, hs w] at hb
      exact absurd hb (not_le.mpr (hw a ha))
    · rintro rfl b
      rw [hs b, hs a]
      rcases eq_or_ne b a with rfl | hb
      · exact le_rfl
      · exact (hw b hb).le
  rw [scoreWinner]
  simp only [hargmax, Finset.min'_singleton]

/-! ### Packaging a score as a resolute `ChoiceFunction` -/

variable {Voter : Type*}

/-- Package a per-profile score `score : Profile → Alt → σ` into a resolute social choice function
on the given `domain`: On every admissible profile the sole winner is `scoreWinner (score P)`. -/
noncomputable def ChoiceFunction.resoluteOf {σ : Type*} [LinearOrder σ]
    (domain : Set (Profile Voter Alt)) (score : Profile Voter Alt → Alt → σ) :
    ChoiceFunction Voter Alt where
  domain := domain
  winners := fun P => {scoreWinner (score P)}
  winners_nonempty := fun _ _ => Set.singleton_nonempty _

@[simp] lemma ChoiceFunction.resoluteOf_winners {σ : Type*} [LinearOrder σ]
    (domain : Set (Profile Voter Alt)) (score : Profile Voter Alt → Alt → σ)
    (P : Profile Voter Alt) :
    (ChoiceFunction.resoluteOf domain score).winners P = {scoreWinner (score P)} := rfl

@[simp] lemma ChoiceFunction.resoluteOf_domain {σ : Type*} [LinearOrder σ]
    (domain : Set (Profile Voter Alt)) (score : Profile Voter Alt → Alt → σ) :
    (ChoiceFunction.resoluteOf domain score).domain = domain := rfl

/-- Every admissible profile of a resolute rule has at most one winner — in fact exactly the
singleton `{scoreWinner …}`. -/
lemma ChoiceFunction.resoluteOf_resolute {σ : Type*} [LinearOrder σ]
    (domain : Set (Profile Voter Alt)) (score : Profile Voter Alt → Alt → σ) :
    ∀ P ∈ (ChoiceFunction.resoluteOf domain score).domain,
      ((ChoiceFunction.resoluteOf domain score).winners P).Subsingleton :=
  fun _ _ => Set.subsingleton_singleton

/-! ### Canonical resolute Borda count -/

variable [Fintype Voter]

/-- **Borda count made resolute**, on the strict domain: Rank alternatives by total Borda score and
return the lexicographically smallest top-scorer as the unique winner. This is the canonical
resolute rule behind the Gibbard–Satterthwaite manipulation example. -/
noncomputable def resoluteBorda : ChoiceFunction Voter Alt :=
  ChoiceFunction.resoluteOf (strictDomain Voter Alt) bordaScore

/-- The resolute Borda winner of `P` is `scoreWinner (bordaScore P)`. -/
lemma resoluteBorda_winners (P : Profile Voter Alt) :
    (resoluteBorda (Voter := Voter)).winners P = {scoreWinner (bordaScore P)} := rfl

@[simp] lemma resoluteBorda_domain :
    (resoluteBorda (Voter := Voter) (Alt := Alt)).domain = strictDomain Voter Alt := rfl

end Econlib.SocialChoice
