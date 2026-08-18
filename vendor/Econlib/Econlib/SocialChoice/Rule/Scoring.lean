/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic
public import Econlib.SocialChoice.Profile.Domain
public import Econlib.SocialChoice.Rule.Borda
public import Econlib.SocialChoice.Rule.Plurality
public import Econlib.SocialChoice.WelfareFunction.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Scoring rules

A **scoring rule** assigns a real-valued score to each alternative based on its rank in a voter's
preference. The total score of an alternative is the sum across voters of its individual scores,
and the induced social welfare function ranks alternatives by total score.

The rank of an alternative under `R` is its number of strict-betters:
`numStrictBetters R a = |{ b | b ≻ a }|`. For strict preferences this gives a bijection between
alternatives and `{0, 1, ..., card - 1}`. For non-strict preferences indifferent alternatives share
the same rank, so the resulting score may not equal the textbook score; the canonical Borda and
plurality welfare functions therefore restrict the domain to strict profiles.

## Main definitions

* `numStrictBetters` — the rank of an alternative as its number of strict-betters.
* `ScoringRule` — a scoring rule, given by a rank-to-score function.
* `ScoringRule.scoreOf`, `ScoringRule.totalScore`, `ScoringRule.toWelfareFunction` — the score a
  voter assigns, the total score under a profile, and the induced welfare function.
* `bordaScoringRule` — the **Borda count** (Borda 1781) as the scoring rule
  `score k = card - 1 - k`.
* `pluralityScoringRule` — **plurality** as the scoring rule `score 0 = 1`, `score (k + 1) = 0`.
* `pluralityRel`, `pluralityWelfareFunction` — the plurality preference relation and the canonical
  plurality social welfare function, the plurality analogs of `bordaRel` and `bordaWelfareFunction`.

## Main statements

* `bordaScoringRule_scoreOf`, `bordaScoringRule_aggregate_le_iff` — on the strict domain the Borda
  scoring rule reproduces `bordaScoreOf` and induces the same ranking as `bordaWelfareFunction`.
* `pluralityScoringRule_aggregate_le_iff` — on the strict domain the plurality scoring rule's
  welfare function agrees with `pluralityWelfareFunction`.
* `mem_pluralityWinners_iff_isTop` — the maximizers of `pluralityRel` are exactly the
  `pluralityRule` choice function's `pluralityWinners`.

## References

* Borda, Jean-Charles de. 1781. “Memoire Sur Les Elections Au Scrutin.” In *Histoire De L'academie
  Royale Des Sciences*. Paris.

## Tags

social choice, voting, scoring rule, borda count, plurality
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Alt : Type*} [Fintype Alt]

/-- The number of alternatives strictly preferred to `a` under `R`. For strict preferences this is
`a`'s zero-indexed rank from the top.

Noncomputable by design: The filter predicate `R.lt b a` is `Prop`-valued over the abstract
`PreferenceRel.le` and is decided classically rather than via a threaded `Decidable` bracket field
(see `majorityCount` for the full rationale). -/
noncomputable def numStrictBetters (R : PreferenceRel Alt) (a : Alt) : ℕ :=
  letI : DecidablePred (fun b : Alt => R.lt b a) := Classical.decPred _
  (Finset.univ.filter (fun b : Alt => R.lt b a)).card

/-- If `s` is exactly the set of alternatives strictly beating `a` under `R`, then
`numStrictBetters R a = s.card`. -/
lemma numStrictBetters_eq_card (R : PreferenceRel Alt) (a : Alt)
    (s : Finset Alt) (h : ∀ b, R.lt b a ↔ b ∈ s) :
    numStrictBetters R a = s.card := by
  classical
  change (Finset.univ.filter (fun b : Alt => R.lt b a)).card = s.card
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h b

/-- A scoring rule on `Alt` is determined by a function from rank to score. -/
structure ScoringRule (Alt : Type*) [Fintype Alt] where
  /-- The score awarded to an alternative whose rank is `k`. -/
  score : ℕ → ℝ

namespace ScoringRule

variable (s : ScoringRule Alt)

/-- The score voter `R` assigns to alternative `a`. -/
noncomputable def scoreOf (R : PreferenceRel Alt) (a : Alt) : ℝ :=
  s.score (numStrictBetters R a)

/-- The total score of `a` under profile `P`: Sum of individual scores. -/
noncomputable def totalScore {Voter : Type*} [Fintype Voter]
    (P : Profile Voter Alt) (a : Alt) : ℝ :=
  ∑ i : Voter, s.scoreOf (P i) a

/-- The scoring social welfare function. Restricted to the strict domain so the rank function
accurately captures position. -/
noncomputable def toWelfareFunction {Voter : Type*} [Fintype Voter] :
    WelfareFunction Voter Alt where
  domain := strictDomain Voter Alt
  aggregate := fun P => preferenceOfRealUtility (fun a => s.totalScore P a)

end ScoringRule

/-- Borda as scoring rule: The `k`th alternative from the top receives `card - 1 - k` points. -/
noncomputable def bordaScoringRule : ScoringRule Alt where
  score := fun k => (Fintype.card Alt - 1 - k : ℕ)

/-- **Partition identity.** Under a strict preference, every alternative other than `a` is either
strictly worse than `a` (counted by `bordaScoreOf`) or strictly better (counted by
`numStrictBetters`), so the two counts sum to `card - 1`. -/
lemma bordaScoreOf_add_numStrictBetters {R : PreferenceRel Alt} (h : StrictPref R) (a : Alt) :
    bordaScoreOf R a + numStrictBetters R a = Fintype.card Alt - 1 := by
  classical
  have hb : bordaScoreOf R a = (Finset.univ.filter (fun b : Alt => R.lt a b)).card := by
    unfold bordaScoreOf; rfl
  have hn : numStrictBetters R a = (Finset.univ.filter (fun b : Alt => R.lt b a)).card := by
    unfold numStrictBetters; rfl
  rw [hb, hn]
  have hdisj : Disjoint (Finset.univ.filter (fun b : Alt => R.lt a b))
      (Finset.univ.filter (fun b : Alt => R.lt b a)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    exact R.not_lt_both (Finset.mem_filter.mp hb1).2 (Finset.mem_filter.mp hb2).2
  -- The two strict sides exhaust every alternative other than `a`.
  have hunion : (Finset.univ.filter (fun b : Alt => R.lt a b))
      ∪ (Finset.univ.filter (fun b : Alt => R.lt b a)) = Finset.univ.erase a := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
      Finset.mem_erase]
    constructor
    · rintro (hlt | hlt) he <;> exact R.lt_irrefl a (he ▸ hlt)
    · intro hbne
      exact (h.lt_or_lt_of_ne hbne).symm
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] at hcard
  omega

/-- **Borda is the scoring rule `card - 1 - rank`.** On a strict preference the Borda scoring
rule's score for `a` equals its textbook Borda score (the number of alternatives ranked strictly
below). -/
lemma bordaScoringRule_scoreOf {R : PreferenceRel Alt} (h : StrictPref R) (a : Alt) :
    bordaScoringRule.scoreOf R a = (bordaScoreOf R a : ℝ) := by
  have hid : Fintype.card Alt - 1 - numStrictBetters R a = bordaScoreOf R a := by
    have := bordaScoreOf_add_numStrictBetters h a; omega
  -- `scoreOf` is defeq to the cast of the nat rank-score, so cast `hid`.
  exact congrArg Nat.cast hid

/-- On a strict profile, the Borda scoring rule's total score equals the natural-number total Borda
score. -/
lemma bordaScoringRule_totalScore {Voter : Type*} [Fintype Voter] {P : Profile Voter Alt}
    (hP : Profile.IsStrict P) (a : Alt) :
    bordaScoringRule.totalScore P a = (bordaScore P a : ℝ) := by
  rw [show bordaScore P a = ∑ i, bordaScoreOf (P i) a from rfl, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun i _ => bordaScoringRule_scoreOf (hP i) a)

/-- **Welfare-level agreement.** On the strict domain the Borda scoring rule's welfare function and
the direct `bordaWelfareFunction` rank every pair of alternatives identically. -/
lemma bordaScoringRule_aggregate_le_iff {Voter : Type*} [Fintype Voter]
    {P : Profile Voter Alt} (hP : Profile.IsStrict P) (x y : Alt) :
    (bordaScoringRule.toWelfareFunction.aggregate P).le x y ↔ (bordaRel P).le x y := by
  change (preferenceOfUtilityIn (fun a => bordaScoringRule.totalScore P a)).le x y
    ↔ (bordaRel P).le x y
  simp only [bordaRel, preferenceOfUtilityIn_le_iff]
  rw [bordaScoringRule_totalScore hP, bordaScoringRule_totalScore hP, Nat.cast_le]

/-- Plurality as a scoring rule: Only the top-ranked alternative receives a point. -/
noncomputable def pluralityScoringRule : ScoringRule Alt where
  score := fun k => if k = 0 then 1 else 0

/-- **Top iff zero strict-betters.** An alternative has rank `0` (no one strictly above it) exactly
when it weakly dominates every alternative. Totality of `PreferenceRel` does all the work; no
strictness is needed. -/
lemma numStrictBetters_eq_zero_iff {R : PreferenceRel Alt} (a : Alt) :
    numStrictBetters R a = 0 ↔ ∀ b : Alt, R.le a b := by
  classical
  rw [numStrictBetters, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h b
    by_contra hab
    exact h (Finset.mem_univ b) ⟨(R.le_total a b).resolve_left hab, hab⟩
  · intro h b _ hlt
    exact hlt.2 (h b)

/-- **Plurality scoring picks out the top.** On a strict ballot the plurality scoring rule awards
`1` to the deterministic top pick `topPick R` and `0` to everyone else. -/
lemma pluralityScoringRule_scoreOf [Nonempty Alt] [LinearOrder Alt] {R : PreferenceRel Alt}
    (hR : StrictPref R) (a : Alt) :
    pluralityScoringRule.scoreOf R a = if topPick R = a then 1 else 0 := by
  change (if numStrictBetters R a = 0 then (1 : ℝ) else 0) = if topPick R = a then 1 else 0
  by_cases htop : topPick R = a
  · -- `a` is the top pick, so it weakly dominates everyone and has zero strict-betters.
    have ha_top : a ∈ topSet R := by
      have hmem : topPick R ∈ topSet R := by rw [topPick]; exact Finset.min'_mem _ _
      rwa [htop] at hmem
    rw [if_pos ((numStrictBetters_eq_zero_iff a).mpr (mem_topSet.mp ha_top)), if_pos htop]
  · -- `a` is not the top pick; a zero rank would force it to be, by `topPick_eq`.
    rw [if_neg htop,
        if_neg (fun h0 => htop (topPick_eq hR ((numStrictBetters_eq_zero_iff a).mp h0)))]

/-- On a strict profile, the plurality scoring rule's total score equals the natural-number
`pluralityScore` (the number of voters whose top pick is `a`). -/
lemma pluralityScoringRule_totalScore
    [Nonempty Alt] [LinearOrder Alt] {Voter : Type*} [Fintype Voter]
    {P : Profile Voter Alt} (hP : Profile.IsStrict P) (a : Alt) :
    pluralityScoringRule.totalScore P a = (pluralityScore P a : ℝ) := by
  classical
  rw [ScoringRule.totalScore]
  simp only [pluralityScoringRule_scoreOf (hP _)]
  rw [Finset.sum_boole,
    pluralityScore_eq_card P a (Finset.univ.filter (fun i => topPick (P i) = a))
      (fun i => by simp)]

/-- **Plurality preference**: Rank alternatives by total plurality score (number of voters who
place them first). The strict-domain analog of `bordaRel`. -/
noncomputable def pluralityRel [Nonempty Alt] [LinearOrder Alt] {Voter : Type*} [Fintype Voter]
    (P : Profile Voter Alt) : PreferenceRel Alt :=
  preferenceOfUtilityIn (fun a => pluralityScore P a)

/-- **The canonical plurality social welfare function.** Ranks alternatives by total plurality
score, restricted to the strict domain so that `topPick` (hence the score) is well defined per
ballot. This is the plurality analog of `bordaWelfareFunction`. -/
noncomputable def pluralityWelfareFunction
    [Nonempty Alt] [LinearOrder Alt] {Voter : Type*} [Fintype Voter] :
    WelfareFunction Voter Alt where
  domain := strictDomain Voter Alt
  aggregate := pluralityRel

/-- **Welfare-level agreement.** On the strict domain the plurality *scoring* rule's welfare
function and the canonical `pluralityWelfareFunction` (via `pluralityRel`) rank every pair of
alternatives identically. The plurality analog of `bordaScoringRule_aggregate_le_iff`. -/
lemma pluralityScoringRule_aggregate_le_iff [Nonempty Alt] [LinearOrder Alt] {Voter : Type*}
    [Fintype Voter] {P : Profile Voter Alt} (hP : Profile.IsStrict P) (x y : Alt) :
    (pluralityScoringRule.toWelfareFunction.aggregate P).le x y ↔ (pluralityRel P).le x y := by
  change (preferenceOfUtilityIn (fun a => pluralityScoringRule.totalScore P a)).le x y
    ↔ (pluralityRel P).le x y
  simp only [pluralityRel, preferenceOfUtilityIn_le_iff]
  rw [pluralityScoringRule_totalScore hP, pluralityScoringRule_totalScore hP, Nat.cast_le]

/-- **Connection to the plurality choice function.** The maximizers of the plurality welfare
relation `pluralityRel` are exactly the `pluralityWinners` selected by the `pluralityRule` choice
function: Both pick the alternatives of maximal plurality score. -/
lemma mem_pluralityWinners_iff_isTop [Nonempty Alt] [LinearOrder Alt]
    {Voter : Type*} [Fintype Voter] {P : Profile Voter Alt} {a : Alt} :
    a ∈ pluralityWinners P ↔ ∀ b : Alt, (pluralityRel P).le a b := by
  rw [mem_pluralityWinners]
  simp only [pluralityRel, preferenceOfUtilityIn_le_iff]

end Econlib.SocialChoice
