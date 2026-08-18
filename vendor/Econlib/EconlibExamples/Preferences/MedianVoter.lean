/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Black's Median Voter Theorem: A Concrete Three-Voter Electorate

Black's **median voter theorem** is the foundational result of spatial voting theory: When every
voter has *single-peaked* preferences over a one-dimensional policy line, the policy that is the
**median of the voters' ideal points** is a *Condorcet winner* — it defeats every other policy in a
pairwise majority vote. For an odd electorate the median peak is unambiguous and such a Condorcet
winner is guaranteed to exist, escaping the usual cycling pathologies of majority rule.

## The model

Three voters, `Voter := Fin 3`, choose a policy on the real line, `Alt := ℝ`. Each voter `i` has
*quadratic-loss* utility `uᵢ(x) = -(x - peakᵢ)²`, maximized at the voter's ideal point `peakᵢ`, and
falling strictly with squared distance from it. The ideal points are

`peak = ![1, 2, 3]`,

so the median ideal point is `2`. Because there are three (an odd number of) voters, a strict
majority — two of the three — have a peak weakly above `2`, and a strict majority have a peak
weakly below `2`. These two pivot conditions are exactly what Black's theorem needs.

## The mathematics

Quadratic loss is single-peaked: `SinglePeaked.quadraticLoss` packages the strict monotonicity on
each side of the peak, and `SinglePeaked.toRel` turns the cardinal utility into the ordinal
relation-level `SinglePeakedRel` that the social-choice layer consumes. The pivot lemma
`condorcetWinner_of_majority_pivot` then says: If `2 * #{i | m ≤ peakᵢ} > n` and
`2 * #{i | peakᵢ ≤ m} > n`, the policy `m` is a Condorcet winner. At `m = 2` both filtered counts
equal `2` (voters `{1, 2}` and `{0, 1}` respectively) and `2 * 2 = 4 > 3 = n`, so the median `2`
wins every pairwise majority contest. Existence follows from the odd-cardinality theorem
`exists_condorcetWinner_of_singlePeaked` applied to the same single-peaked profile.

The two filtered-cardinality goals are decidable over `Fin 3`, so once `(sp i).peak` is rewritten
to `peak i` (which holds definitionally — `quadraticLoss` sets `peak := peak` and `toRel` copies
it, so the rewrite is `rfl`) the counting is closed by `decide`.

## Main definitions and theorems

* `peak : Fin 3 → ℝ` — the three ideal points `![1, 2, 3]`.
* `P : Profile (Fin 3) ℝ` — the quadratic-loss preference profile.
* `sp i : SinglePeakedRel (P i)` — the single-peakedness witness for each voter.
* `median_is_condorcetWinner : CondorcetWinner P 2` — the median policy `2` is a Condorcet winner.
* `exists_condorcetWinner : ∃ m, CondorcetWinner P m` — a Condorcet winner exists (odd electorate).
* `median_beats : ∀ y ≠ 2, pairwiseMajority P 2 y` — `2` beats every other policy pairwise.
-/

noncomputable section

namespace EconlibExamples.Preferences.MedianVoter

open Econlib.Preferences
open Econlib.SocialChoice

/-- The three voters: An odd electorate `{0, 1, 2}`. -/
abbrev Voter := Fin 3

/-- Policies live on the real line, the canonical one-dimensional spatial model. -/
abbrev Alt := ℝ

/-- The voters' ideal points: `peak 0 = 1`, `peak 1 = 2`, `peak 2 = 3`. The median is `2`. -/
def peak : Voter → ℝ := ![1, 2, 3]

/-- The preference profile: Voter `i` has quadratic-loss utility `x ↦ -(x - peak i)²`, turned into
the ordinal `PreferenceRel` via `preferenceOfRealUtility`. -/
def P : Profile Voter Alt := fun i => preferenceOfRealUtility (fun x => -(x - peak i) ^ 2)

/-- Each voter's preferences are single-peaked at their ideal point. The witness is built from the
cardinal quadratic-loss constructor `SinglePeaked.quadraticLoss` and pushed to the relation level
with `SinglePeaked.toRel`. -/
def sp : (i : Voter) → SinglePeakedRel (P i) :=
  fun i => (SinglePeaked.quadraticLoss (peak i)).toRel

/-- The single-peaked peak of voter `i` is exactly their ideal point `peak i`. This is
definitional: `SinglePeaked.quadraticLoss peak` sets its `peak` field to `peak`, and
`SinglePeaked.toRel` copies that field verbatim, so the equality is `rfl`. -/
@[simp] lemma sp_peak (i : Voter) : (sp i).peak = peak i := rfl

/-! ## The median policy `2` is a Condorcet winner -/

/-- **Black's median voter theorem on this electorate.** The median ideal point `2` is a Condorcet
winner: It defeats every other policy in a pairwise majority vote.

We apply the upstream pivot lemma `condorcetWinner_of_majority_pivot`. Its two hypotheses are
strict-majority counts of voters whose peak lies weakly above (resp. below) `2`; after rewriting
`(sp i).peak` to `peak i` both filtered `Fin 3`-cardinalities are `2`, and `2 * 2 = 4 > 3`, which
`decide` discharges. -/
theorem median_is_condorcetWinner : CondorcetWinner P (2 : Alt) := by
  -- The peaks `≥ 2` are voters `{1, 2}`; the peaks `≤ 2` are voters `{0, 1}`. Both have card `2`.
  -- Both pivot goals unfold membership the same way (simp + fin_cases + peak rewrite), then
  -- discharge the numeric comparisons: `norm_num <;> decide` for the ≥ branch (one equality case),
  -- `norm_num` alone for the ≤ branch (all strict comparisons).
  refine condorcetWinner_of_majority_pivot sp 2 ?_ ?_
  · -- A strict majority have peak ≥ 2, namely voters `{1, 2}`: `2 * 2 = 4 > 3 = card (Fin 3)`.
    have hset : ({i : Voter | 2 ≤ (sp i).peak} : Finset Voter) = ({1, 2} : Finset Voter) := by
      ext i
      simp only [sp_peak, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases i <;> simp only [peak] <;> norm_num <;> decide
    rw [hset, Fintype.card_fin]
    decide
  · -- A strict majority have peak ≤ 2, namely voters `{0, 1}`: `2 * 2 = 4 > 3 = card (Fin 3)`.
    -- `norm_num` closes all three cases here without `decide` (strict ≤ comparisons suffice).
    have hset : ({i : Voter | (sp i).peak ≤ 2} : Finset Voter) = ({0, 1} : Finset Voter) := by
      ext i
      simp only [sp_peak, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases i <;> simp only [peak] <;> norm_num
    rw [hset, Fintype.card_fin]
    decide

/-! ## A Condorcet winner exists (odd electorate of single-peaked voters) -/

/-- **Existence form of Black's theorem.** Because the electorate is odd (`card (Fin 3) = 3`) and
every voter is single-peaked, the upstream theorem `exists_condorcetWinner_of_singlePeaked`
guarantees a Condorcet winner. This statement only asserts existence; the witness is not named
here — it is identified concretely as the median `2` by the separate `median_is_condorcetWinner`. -/
theorem exists_condorcetWinner : ∃ m : Alt, CondorcetWinner P m :=
  exists_condorcetWinner_of_singlePeaked sp (by rw [Fintype.card_fin]; decide)

/-! ## The median beats every other policy in a head-to-head vote -/

/-- Unpacking the Condorcet property: The median `2` wins the pairwise majority contest against
every distinct policy `y`. This is just `CondorcetWinner.beats` applied to
`median_is_condorcetWinner`. -/
theorem median_beats : ∀ y : Alt, y ≠ 2 → pairwiseMajority P 2 y :=
  fun _ hy => median_is_condorcetWinner.beats hy

end EconlibExamples.Preferences.MedianVoter
