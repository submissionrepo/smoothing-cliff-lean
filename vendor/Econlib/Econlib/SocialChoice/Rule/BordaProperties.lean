/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Transform
public import Econlib.SocialChoice.Rule.Borda
public import Econlib.SocialChoice.WelfareFunction.Properties
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Linarith

/-!
# Axiomatic properties of the Borda welfare function

The Borda social welfare function `bordaWelfareFunction` (Borda 1781), which ranks alternatives by
total Borda score, satisfies **Weak Pareto** and, on any electorate of at least two voters over at
least two alternatives, is **non-dictatorial**. Both properties are stated domain-generically
through the aggregator `bordaRel`, so they hold for the canonical strict-domain
`bordaWelfareFunction` and for any other domain (such as the universal domain used in
Arrow-independence witnesses).

## Main statements

* `bordaRel_lt_of_forall_lt` — a unanimous strict preference is inherited by `bordaRel` (the
  domain-free Weak Pareto core).
* `bordaWelfareFunction.WeakPareto` — the Borda welfare function satisfies Weak Pareto.
* `exists_strictProfile_bordaRel_not_lt_of_dictator` — over `2 ≤ card Voter` and `2 ≤ card Alt`, no
  voter's strict preferences always pass through `bordaRel` (the domain-free non-dictatorship core).
* `bordaWelfareFunction.nonDictatorship` — the Borda welfare function is non-dictatorial.

## References

* Borda, Jean-Charles de. 1781. “Memoire Sur Les Elections Au Scrutin.” In *Histoire De L'academie
  Royale Des Sciences*. Paris.

## Tags

social choice, borda count, weak pareto, non-dictatorship, arrow
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter Alt : Type*} [Fintype Voter] [Fintype Alt]

/-! ### Weak Pareto -/

/-- **Weak-Pareto core for Borda.** If every voter strictly prefers `x` to `y`, then `x` strictly
out-scores `y` in total Borda score, so the Borda ranking `bordaRel P` strictly prefers `x`. This
is domain-free: `Finset.sum_lt_sum_of_nonempty` over the per-voter monotonicity
`bordaScoreOf_lt_of_lt`. -/
lemma bordaRel_lt_of_forall_lt [Nonempty Voter] (P : Profile Voter Alt) {x y : Alt}
    (h : ∀ i, (P i).lt x y) : (bordaRel P).lt x y := by
  rw [bordaRel, preferenceOfUtilityIn_lt_iff]
  simp only [bordaScore]
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i _ => bordaScoreOf_lt_of_lt (P i) (h i))

/-- **Weak Pareto for the Borda welfare function.** If every voter ranks `x ≻ y`, so does society
under `bordaWelfareFunction`. -/
theorem bordaWelfareFunction.WeakPareto [Nonempty Voter] :
    (bordaWelfareFunction (Voter := Voter) (Alt := Alt)).WeakPareto :=
  fun P _ _ _ h => bordaRel_lt_of_forall_lt P h

/-! ### Non-dictatorship

The Borda rule defers to a majority, so with at least two voters no single voter dictates. -/

variable [DecidableEq Alt]

/-- Swapping two alternatives in a preference mirrors every Borda score: The score of `z` under
`swapPref R a c` equals the score of `Equiv.swap a c z` under `R`, because the swap is a bijection
of the beaten-set. -/
lemma bordaScoreOf_swapPref (R : PreferenceRel Alt) (a c z : Alt) :
    bordaScoreOf (swapPref R a c) z = bordaScoreOf R (Equiv.swap a c z) := by
  classical
  rw [bordaScoreOf_eq_card (swapPref R a c) z
        (Finset.univ.filter fun b => (swapPref R a c).lt z b) (fun b => by simp),
      bordaScoreOf_eq_card R (Equiv.swap a c z)
        (Finset.univ.filter fun b => R.lt (Equiv.swap a c z) b) (fun b => by simp)]
  -- `b ↦ swap a c b` carries `z`'s beaten-set under `swapPref` onto `(swap z)`'s under `R`.
  refine Finset.card_bij (fun b _ => Equiv.swap a c b) ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, swapPref_lt_iff] at hb ⊢
    exact hb
  · intro b₁ _ b₂ _ h
    exact (Equiv.swap a c).injective h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨Equiv.swap a c b, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, swapPref_lt_iff,
      Equiv.swap_apply_self]
    exact hb

variable [DecidableEq Voter]

/-- The non-dictatorship witness profile: Voter `i` keeps ballot `R`, every other voter reports `R`
with `a` and `c` swapped. -/
private def loneFanProfile (R : PreferenceRel Alt) (i : Voter) (a c : Alt) :
    Profile Voter Alt :=
  fun j => if j = i then R else swapPref R a c

/-- Under the lone-fan profile the total Borda score of `a` mixes one copy of `R`'s score of `a`
with `(card Voter - 1)` copies of `R`'s score of `c` (the swap mirrors `a` onto `c`). -/
private lemma loneFanProfile_bordaScore (R : PreferenceRel Alt) (i : Voter) (a c z : Alt) :
    bordaScore (loneFanProfile R i a c) z
      = bordaScoreOf R z
        + (Fintype.card Voter - 1) * bordaScoreOf R (Equiv.swap a c z) := by
  classical
  rw [bordaScore]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hi : bordaScoreOf (loneFanProfile R i a c i) z = bordaScoreOf R z := by
    rw [loneFanProfile, if_pos rfl]
  have hrest : ∀ j ∈ (Finset.univ.erase i),
      bordaScoreOf (loneFanProfile R i a c j) z
        = bordaScoreOf R (Equiv.swap a c z) := by
    intro j hj
    rw [loneFanProfile, if_neg (Finset.ne_of_mem_erase hj), bordaScoreOf_swapPref]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, hi, smul_eq_mul]
  omega

omit [DecidableEq Alt] [DecidableEq Voter] in
/-- **Non-dictatorship core for Borda.** Over at least two voters and two alternatives, no voter
`i` is a `bordaRel`-dictator: There is a strict profile and a pair `x ≻ y` for voter `i` that
society does not strictly rank `x ≻ y`. Domain-free, so it refutes dictatorship on any admissible
domain. -/
lemma exists_strictProfile_bordaRel_not_lt_of_dictator
    (hV : 2 ≤ Fintype.card Voter) (hA : 2 ≤ Fintype.card Alt) (i : Voter) :
    ∃ P : Profile Voter Alt, Profile.IsStrict P ∧ ∃ x y : Alt,
      (P i).lt x y ∧ ¬ (bordaRel P).lt x y := by
  classical
  -- A strict base ballot from the canonical injective utility, and two distinct alternatives.
  set R₀ : PreferenceRel Alt := preferenceOfUtilityIn (Fintype.equivFin Alt) with hR₀
  have hR₀_strict : StrictPref R₀ :=
    strictPref_preferenceOfUtilityIn (Fintype.equivFin Alt).injective
  obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (α := Alt) (by omega)
  -- Orient the pair so voter `i` strictly prefers `x ≻ y` under `R₀`.
  obtain ⟨x, y, hxy_lt, hxy_pair⟩ :
      ∃ x y : Alt, (R₀.lt x y) ∧ ((x = a ∧ y = c) ∨ (x = c ∧ y = a)) := by
    rcases hR₀_strict.lt_or_lt_of_ne hac with h | h
    · exact ⟨a, c, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨c, a, h, Or.inr ⟨rfl, rfl⟩⟩
  refine ⟨loneFanProfile R₀ i x y, ?_, x, y, ?_, ?_⟩
  · -- Strictness: every ballot is `R₀` or a swap of it, both strict.
    intro j
    rw [loneFanProfile]
    by_cases hj : j = i
    · rw [if_pos hj]; exact hR₀_strict
    · rw [if_neg hj]; exact hR₀_strict.swapPref x y
  · -- Voter `i`'s ballot is `R₀`, which prefers `x ≻ y`.
    rw [loneFanProfile, if_pos rfl]; exact hxy_lt
  · -- Society ties or reverses: the two scores are mirror images, and `card Voter - 1 ≥ 1`.
    rw [bordaRel, preferenceOfUtilityIn_lt_iff]
    rw [loneFanProfile_bordaScore, loneFanProfile_bordaScore,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    -- `bordaScore x = p + k·q`, `bordaScore y = q + k·p`; `p = score x`, `q = score y`, `k ≥ 1`.
    set p := bordaScoreOf R₀ x with hp
    set q := bordaScoreOf R₀ y with hq
    set k := Fintype.card Voter - 1 with hk
    have hk1 : 1 ≤ k := by omega
    have hpq : q < p := bordaScoreOf_lt_of_lt R₀ hxy_lt
    -- Goal: `¬ (q + k·p < p + k·q)`; since `q < p` and `k ≥ 1`, the LHS dominates the RHS.
    intro hlt
    nlinarith [hpq, hk1, hlt]

omit [DecidableEq Alt] [DecidableEq Voter] in
/-- **The Borda welfare function is non-dictatorial** over at least two voters and two
alternatives: Society defers to a majority, so no single voter's strict preferences always pass
through. -/
theorem bordaWelfareFunction.nonDictatorship
    (hV : 2 ≤ Fintype.card Voter) (hA : 2 ≤ Fintype.card Alt) :
    (bordaWelfareFunction (Voter := Voter) (Alt := Alt)).NonDictatorship := by
  rintro ⟨i, hi⟩
  obtain ⟨P, hP_strict, x, y, hxy, hnot⟩ :=
    exists_strictProfile_bordaRel_not_lt_of_dictator hV hA i
  exact hnot (hi P hP_strict x y hxy)

end Econlib.SocialChoice
