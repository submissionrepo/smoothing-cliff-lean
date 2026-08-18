/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card

/-!
# Pairwise majority and Condorcet winners

For each ordered pair `(x, y)`, `majorityCount P x y` counts the voters who strictly prefer `x` to
`y` under profile `P`. The **pairwise-majority relation** `pairwiseMajority P x y` holds when
strictly more voters rank `x ≻ y` than `y ≻ x`. A **Condorcet winner** is an alternative that beats
every other alternative pairwise (Condorcet 1785).

## Main definitions

* `majorityCount` — the number of voters strictly preferring one alternative to another.
* `pairwiseMajority`, `majorityRelation` — the pairwise-majority relation.
* `CondorcetWinner` — an alternative that beats every other alternative pairwise.

## Main statements

* `majorityCount_eq_card` — the majority count reads off an explicit set of voters.
* `majorityCount_comp_perm` — the majority count is invariant under permutation of voters.
* `majorityCount_update_add_one`, `majorityCount_update_iff`, `majorityCount_update_le_of_not_lt` —
  the effect of a single voter changing their ballot on the majority count.

## Notes

The pairwise-majority relation is not in general transitive: Condorcet's paradox exhibits the
profile `(a≻b≻c, b≻c≻a, c≻a≻b)`, in which the relation cycles. A majority-rule social welfare
function therefore exists only on restricted domains (single-peaked, single-crossing, and so on).

## References

* Condorcet, Marquis de. 1785. *Essai Sur L'application De L'analyze a La Probabilite Des Decisions
  Rendues a La Pluralite Des Voix*. Imprimerie Royale.

## Tags

social choice, voting, condorcet winner, pairwise majority, condorcet paradox
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter Alt : Type*} [Fintype Voter]

/-- The number of voters who strictly prefer `x` to `y` under profile `P`.

**Noncomputable by design.** The filter predicate `(P i).lt x y` is `Prop`-valued over the abstract
`PreferenceRel.le`, which carries no `Decidable` instance; decidability is supplied classically
rather than threaded as a `[∀ i, Decidable ((P i).lt x y)]` bracket field. The latter is avoided
deliberately: The analogous predicates across the scoring/plurality/median rules are heterogeneous
(over voters, over alternatives, `∀`-quantified `le`, `topPick`-equality), so no single bracket
field serves all, and concrete `Fin n` instantiations would risk instance diamonds. These rules are
proof vehicles for the Arrow/Gibbard–Satterthwaite/May results, not evaluation engines, so
computability buys nothing. -/
noncomputable def majorityCount (P : Profile Voter Alt) (x y : Alt) : ℕ :=
  letI : DecidablePred (fun i : Voter => (P i).lt x y) := Classical.decPred _
  (Finset.univ.filter (fun i : Voter => (P i).lt x y)).card

/-- If `s` is exactly the set of voters who strictly prefer `x` to `y`, then
`majorityCount P x y = s.card`. -/
lemma majorityCount_eq_card (P : Profile Voter Alt) (x y : Alt)
    (s : Finset Voter) (h : ∀ i, (P i).lt x y ↔ i ∈ s) :
    majorityCount P x y = s.card := by
  classical
  change (Finset.univ.filter (fun i : Voter => (P i).lt x y)).card = s.card
  congr 1
  ext i
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h i

/-- `majorityCount` is invariant under permutation of voters. Underwrites anonymity of any
majority-based rule. -/
lemma majorityCount_comp_perm (P : Profile Voter Alt) (σ : Equiv.Perm Voter) (a b : Alt) :
    majorityCount (P ∘ σ) a b = majorityCount P a b := by
  classical
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
    exact hi
  · intro i _ j _ hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] at hj ⊢
    exact hj

/-- A voter switching toward `x ≻ y` — the old ballot did not rank `x ≻ y`, the new one does —
raises the majority count by exactly one. -/
lemma majorityCount_update_add_one [DecidableEq Voter] {P : Profile Voter Alt} {i : Voter}
    {R' : PreferenceRel Alt} {x y : Alt} (hP : ¬ (P i).lt x y) (hR' : R'.lt x y) :
    majorityCount (Function.update P i R') x y = majorityCount P x y + 1 := by
  classical
  have hPcount : majorityCount P x y = (Finset.univ.filter (fun j => (P j).lt x y)).card :=
    majorityCount_eq_card P x y _ (fun j => by simp)
  have hi_notin : i ∉ Finset.univ.filter (fun j => (P j).lt x y) := by simp [hP]
  have hUpd : majorityCount (Function.update P i R') x y
      = (insert i (Finset.univ.filter (fun j => (P j).lt x y))).card := by
    refine majorityCount_eq_card _ x y _ (fun j => ?_)
    rw [Finset.mem_insert]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; simp [hR']
    · rw [Function.update_of_ne hj]
      exact ⟨Or.inr, fun h => h.resolve_left hj⟩
  rw [hUpd, hPcount, Finset.card_insert_of_notMem hi_notin]

/-- A ballot change that does not flip voter `i`'s `x ≻ y` verdict leaves the majority count
unchanged. -/
lemma majorityCount_update_iff [DecidableEq Voter] {P : Profile Voter Alt} {i : Voter}
    {R' : PreferenceRel Alt} {x y : Alt} (h : (P i).lt x y ↔ R'.lt x y) :
    majorityCount (Function.update P i R') x y = majorityCount P x y := by
  classical
  have hP : majorityCount P x y = (Finset.univ.filter (fun j => (P j).lt x y)).card :=
    majorityCount_eq_card P x y _ (fun j => by simp)
  rw [hP]
  refine majorityCount_eq_card _ x y _ (fun j => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact h.symm
  · rw [Function.update_of_ne hj]

/-- If voter `i`'s new ballot does not rank `x ≻ y`, the majority count for `x` over `y` does not
increase. -/
lemma majorityCount_update_le_of_not_lt [DecidableEq Voter] {P : Profile Voter Alt} {i : Voter}
    {R' : PreferenceRel Alt} {x y : Alt} (hR' : ¬ R'.lt x y) :
    majorityCount (Function.update P i R') x y ≤ majorityCount P x y := by
  by_cases hP : (P i).lt x y
  · have h := majorityCount_update_add_one (P := Function.update P i R') (i := i) (R' := P i)
      (x := x) (y := y) (by rw [Function.update_self]; exact hR') hP
    rw [Function.update_idem, Function.update_eq_self] at h
    omega
  · rw [majorityCount_update_iff (iff_of_false hP hR')]

/-- `x` beats `y` by pairwise majority iff strictly more voters rank `x ≻ y` than `y ≻ x`. -/
def pairwiseMajority (P : Profile Voter Alt) (x y : Alt) : Prop :=
  majorityCount P y x < majorityCount P x y

/-- The pairwise-majority relation as a binary relation. Generally not transitive (Condorcet's
paradox); see the docstring for this file. -/
def majorityRelation (P : Profile Voter Alt) : Alt → Alt → Prop :=
  pairwiseMajority P

/-- An alternative is a **Condorcet winner** iff it beats every other alternative pairwise. -/
def CondorcetWinner (P : Profile Voter Alt) (x : Alt) : Prop :=
  ∀ y : Alt, y ≠ x → pairwiseMajority P x y

namespace CondorcetWinner

variable {P : Profile Voter Alt} {x : Alt}

lemma beats (h : CondorcetWinner P x) {y : Alt} (hy : y ≠ x) :
    pairwiseMajority P x y := h y hy

end CondorcetWinner

end Econlib.SocialChoice
