/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic
public import Econlib.SocialChoice.Profile.Domain
public import Econlib.SocialChoice.WelfareFunction.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Borda count

For a strict preference `R`, the **Borda score** of `a` is the number of alternatives ranked
strictly below `a` (Borda 1781). Summing over voters gives the total Borda score; ranking
alternatives by total Borda score yields the **Borda preference relation**.

The `bordaScoreOf` and `bordaScore` definitions typecheck for arbitrary `PreferenceRel`s under the
indifference convention "indifferent alternatives are not counted." For non-strict preferences the
resulting rule is not the textbook Borda count, so the canonical welfare function
`bordaWelfareFunction` restricts the domain to strict profiles.

## Main definitions

* `bordaScoreOf` — the Borda score of an alternative under a single preference.
* `bordaScore` — the total Borda score of an alternative under a profile.
* `bordaRel` — the Borda preference relation, ranking alternatives by total Borda score.
* `bordaWelfareFunction` — the Borda social welfare function on the strict domain.

## Main statements

* `bordaScoreOf_eq_card` — reads the Borda score off an explicit beaten-set.
* `bordaScoreOf_le_card` — the Borda score is at most `Fintype.card Alt`.
* `bordaScoreOf_lt_of_lt` — strict preference strictly increases the Borda score.

## Notes

The generic scoring-rule abstraction is `Rule/Scoring.lean`; Borda is the specialization with score
vector `score k = (Fintype.card Alt - 1) - k`.

## References

* Borda, Jean-Charles de. 1781. “Memoire Sur Les Elections Au Scrutin.” In *Histoire De L'academie
  Royale Des Sciences*. Paris.

## Tags

social choice, voting, borda count, scoring rule
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter Alt : Type*} [Fintype Alt]

/-- `a`'s Borda score under preference `R`: The number of alternatives strictly worse than `a`.

Noncomputable by design: The filter predicate `R.lt a b` is `Prop`-valued over the abstract
`PreferenceRel.le` and is decided classically rather than via a threaded `Decidable` bracket field
(see `majorityCount` for the full rationale). -/
noncomputable def bordaScoreOf (R : PreferenceRel Alt) (a : Alt) : ℕ :=
  letI : DecidablePred (fun b : Alt => R.lt a b) := Classical.decPred _
  (Finset.univ.filter (fun b : Alt => R.lt a b)).card

/-- The total Borda score of `a` under profile `P`: Sum of individual Borda scores. -/
noncomputable def bordaScore [Fintype Voter] (P : Profile Voter Alt) (a : Alt) : ℕ :=
  ∑ i : Voter, bordaScoreOf (P i) a

/-- The Borda preference: Rank alternatives by total Borda score. -/
noncomputable def bordaRel [Fintype Voter] (P : Profile Voter Alt) : PreferenceRel Alt :=
  preferenceOfUtilityIn (fun a => bordaScore P a)

/-- The **Borda social welfare function**. Restricted to the strict domain so the score vector
accurately captures rank. -/
noncomputable def bordaWelfareFunction [Fintype Voter] :
    WelfareFunction Voter Alt where
  domain := strictDomain Voter Alt
  aggregate := bordaRel

/-- If `s` is exactly the set of alternatives that `a` strictly beats under `R`, then
`bordaScoreOf R a = s.card`. -/
lemma bordaScoreOf_eq_card (R : PreferenceRel Alt) (a : Alt)
    (s : Finset Alt) (h : ∀ b, R.lt a b ↔ b ∈ s) :
    bordaScoreOf R a = s.card := by
  classical
  change (Finset.univ.filter (fun b : Alt => R.lt a b)).card = s.card
  congr 1
  ext b
  simp [h b]

/-- Borda score of a utility-induced preference, read off an explicit beaten-set: If `s` is exactly
the set of alternatives with utility strictly below `a`'s, then `a`'s Borda score is `s.card`. -/
lemma bordaScoreOf_utility_eq_card {U : Type*} [LinearOrder U] (u : Alt → U) (a : Alt)
    (s : Finset Alt) (h : ∀ b : Alt, u b < u a ↔ b ∈ s) :
    bordaScoreOf (preferenceOfUtilityIn u) a = s.card :=
  bordaScoreOf_eq_card _ a s fun b => by rw [preferenceOfUtilityIn_lt_iff]; exact h b

/-- Total Borda score read off per-voter beaten-sets: If `s i` is exactly the set of alternatives
that `a` strictly beats under `P i`, then `bordaScore P a = ∑ i, (s i).card`. -/
lemma bordaScore_eq_sum_card [Fintype Voter] (P : Profile Voter Alt) (a : Alt)
    (s : Voter → Finset Alt) (h : ∀ i b, (P i).lt a b ↔ b ∈ s i) :
    bordaScore P a = ∑ i, (s i).card := by
  rw [bordaScore]
  exact Finset.sum_congr rfl fun i _ => bordaScoreOf_eq_card (P i) a (s i) (h i)

/-- Total Borda score of a utility-induced profile, read off per-voter beaten-sets: If `s i` is
exactly the set of alternatives with utility strictly below `a`'s under `u i`, then
`bordaScore (fun i => preferenceOfUtilityIn (u i)) a = ∑ i, (s i).card`. -/
lemma bordaScore_ofUtilities {U : Type*} [LinearOrder U] [Fintype Voter]
    (u : Voter → Alt → U) (a : Alt) (s : Voter → Finset Alt)
    (h : ∀ i b, u i b < u i a ↔ b ∈ s i) :
    bordaScore (fun i => preferenceOfUtilityIn (u i)) a = ∑ i, (s i).card :=
  bordaScore_eq_sum_card _ a s fun i b => by rw [preferenceOfUtilityIn_lt_iff]; exact h i b

/-- Total Borda score of a unanimous profile: When every voter holds the same preference `R`, the
total score is `Fintype.card Voter` copies of the per-voter score. -/
lemma bordaScore_const [Fintype Voter] (R : PreferenceRel Alt) (a : Alt) :
    bordaScore (fun _ : Voter => R) a = Fintype.card Voter * bordaScoreOf R a := by
  rw [bordaScore, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The Borda score of any alternative is at most `Fintype.card Alt`. -/
lemma bordaScoreOf_le_card (R : PreferenceRel Alt) (a : Alt) :
    bordaScoreOf R a ≤ Fintype.card Alt := by
  classical
  exact (Finset.card_filter_le Finset.univ _).trans_eq Finset.card_univ

/-- Strict preference strictly increases the Borda score: If `x ≻ y` under `R`, then `y`'s
beaten-set is a proper subset of `x`'s — contained via transitivity, with `y` itself separating
them — so `bordaScoreOf R y < bordaScoreOf R x`. This is the per-voter content of "Borda satisfies
Weak Pareto." -/
lemma bordaScoreOf_lt_of_lt (R : PreferenceRel Alt) {x y : Alt} (h : x ≻[R] y) :
    bordaScoreOf R y < bordaScoreOf R x := by
  classical
  rw [bordaScoreOf_eq_card R y (Finset.univ.filter fun b => R.lt y b) (fun b => by simp),
    bordaScoreOf_eq_card R x (Finset.univ.filter fun b => R.lt x b) (fun b => by simp)]
  -- `y`'s beaten-set sits inside `x`'s: anything below `y` is below `x` by transitivity.
  have hsub : (Finset.univ.filter fun b => R.lt y b) ⊆ Finset.univ.filter fun b => R.lt x b := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact R.lt_of_lt_of_le h hb.1
  -- The inclusion is proper: `x` beats `y` itself, which `y` does not.
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨y, ?_, ?_⟩)
  · simp [h]
  · simp

end Econlib.SocialChoice
