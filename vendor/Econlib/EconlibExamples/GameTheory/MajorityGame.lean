/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# The 3-Player Simple Majority Game

The **simple majority game** on three players is the canonical textbook example used to illustrate
the gap between two solution concepts for cooperative games with transferable utility: The *Shapley
value* and the *core*. Three players must split a unit surplus; any two of them can guarantee the
entire unit by forming a coalition, while a singleton or the empty set is worth nothing.
Concretely, the characteristic function is

v(S) = 1 if |S| ≥ 2,    v(S) = 0 otherwise.

Two facts make this game pedagogically central.

**Shapley uniqueness.** The Shapley value is the unique value rule satisfying efficiency, symmetry,
the dummy axiom, and linearity — see `TUGameOn.shapleyValue_unique`. Since the three players are
interchangeable, symmetry alone forces `φ G i = φ G j` for all `i, j`, and efficiency fixes the
common value at `1 / 3`. This is the canonical illustration that the Shapley axioms uniquely
determine each player's share.

**Bondareva–Shapley.** A TU game has a nonempty core iff it is *balanced*; this is the
Bondareva–Shapley theorem (`TUGameOn.core_nonempty_iff_balanced`). The majority game is the
canonical small example with an empty core: Each of the three two-player coalitions demands the full
unit (coalitional rationality `xᵢ + xⱼ ≥ 1`), but summing those three constraints counts every
player exactly twice, giving `2 (x₀ + x₁ + x₂) ≥ 3`, while efficiency forces `x₀ + x₁ + x₂ = 1` — so
the demands collapse to the impossible `2 ≥ 3`. We give a direct counting proof here rather than
route through balancedness — for `Fin 3` the inequalities are short enough that no general lemma
earns its keep.

## Main definitions and theorems

* `majority3 : TUGameOn (Fin 3)` — the 3-player simple majority game.
* `majority3_shapleyValue` — each player's Shapley value is `1 / 3`.
* `majority3_shapleyValue_total` — efficiency: The three Shapley values sum to `1`.
* `majority3_core_empty` — the core of the majority game is empty.
-/

noncomputable section

namespace EconlibExamples.GameTheory.MajorityGame

open Econlib.GameTheory

/-! ## The Game -/

/-- **The 3-player simple majority game.** Players are `Fin 3`. A coalition `S` is "winning" — and
worth `1` — iff it contains at least two of the three players; otherwise it is worth `0`. The empty
coalition is worth `0` by construction. -/
def majority3 : TUGameOn (Fin 3) where
  value S := if 2 ≤ S.card then (1 : ℝ) else 0
  value_empty := by simp

/-! ## Symmetry of Players -/

/-- The characteristic function of `majority3` depends only on the *cardinality* of the coalition,
not its identity. This is the engine of the symmetry argument: Swapping two players does not change
the value of any coalition that excludes both, because the coalition's cardinality is preserved
when adding either of them. -/
lemma majority3_value (S : Finset (Fin 3)) :
    majority3.value S = if 2 ≤ S.card then (1 : ℝ) else 0 := rfl

/-- **Symmetry of marginal contributions.** For any two players `i ≠ j` and any coalition `S`
containing neither, the marginal contributions of `i` and `j` to `S` agree. This is the hypothesis
required by the Shapley value rule's symmetry axiom (`ValueRule.SatisfiesSymmetry.apply`). -/
lemma majority3_marginal_eq (i j : Fin 3) (S : Finset (Fin 3))
    (hiS : i ∉ S) (hjS : j ∉ S) :
    majority3.marginalContribution i S = majority3.marginalContribution j S := by
  -- Marginal contribution = v(S ∪ {·}) − v(S). Since `i ∉ S` and `j ∉ S`, both inserts
  -- increase the cardinality by exactly one, so they fall in the same value bucket.
  unfold TUGameOn.marginalContribution
  have hi : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
  have hj : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hjS
  simp [majority3_value, hi, hj]

/-! ## Shapley Value: Each Player Gets 1/3 -/

/-- **All three Shapley values are equal.** Because every pair of players satisfies the
marginal-contribution symmetry hypothesis (`majority3_marginal_eq`), the symmetry axiom of the
Shapley value rule forces all three values to coincide. -/
lemma majority3_shapleyValue_eq (i j : Fin 3) :
    majority3.shapleyValue i = majority3.shapleyValue j := by
  -- `shapleyValue = ValueRule.shapley`, and `shapley` satisfies symmetry.
  exact ValueRule.shapley_satisfiesSymmetry.apply majority3
    (fun S _ _ => majority3_marginal_eq i j S ‹_› ‹_›)

/-- **The grand coalition is worth `1`.** All three players form a winning coalition, so
`v(Fin 3) = 1`. -/
lemma majority3_value_univ :
    majority3.value (Finset.univ : Finset (Fin 3)) = 1 := by
  simp [majority3_value]

/-- **Main theorem (Shapley value).** Each player's Shapley value in the 3-player simple majority
game is exactly `1 / 3`.

*Proof.* By `majority3_shapleyValue_eq`, the three values are equal; call the common value `c`. By
efficiency (`ValueRule.shapley_satisfiesEfficiency`), `c + c + c = v(Fin 3)
= 1`, so `c = 1 / 3`. -/
theorem majority3_shapleyValue (i : Fin 3) :
    majority3.shapleyValue i = 1 / 3 := by
  -- All Shapley values equal the value at player 0.
  have hsym : ∀ k : Fin 3, majority3.shapleyValue k = majority3.shapleyValue 0 :=
    fun k => majority3_shapleyValue_eq k 0
  -- Efficiency: the three values sum to the grand coalition's worth, which is 1.
  have heff : ∑ k : Fin 3, majority3.shapleyValue k = 1 := by
    have := ValueRule.shapley_satisfiesEfficiency.apply majority3
    -- `ValueRule.shapley G = G.shapleyValue` unfolds definitionally.
    rw [majority3_value_univ] at this
    exact this
  -- Sum out the three terms and use the symmetry to write the sum as `3 · shapley 0`.
  rw [Fin.sum_univ_three] at heff
  rw [hsym 0, hsym 1, hsym 2] at heff
  rw [hsym i]
  linarith

/-- **Efficiency.** The three Shapley values sum to `1`, the value of the grand coalition. This is
an immediate corollary of `majority3_shapleyValue`, but we also record it directly from the Shapley
axioms for didactic clarity. -/
theorem majority3_shapleyValue_total :
    ∑ i : Fin 3, majority3.shapleyValue i = 1 := by
  have := ValueRule.shapley_satisfiesEfficiency.apply majority3
  rw [majority3_value_univ] at this
  exact this

/-! ## The Core Is Empty -/

/-- **Two-player coalitions are worth `1`.** For any pair `{i, j}` with `i ≠ j` in `Fin 3`, the
value is `1` because the coalition has cardinality `2`. -/
lemma majority3_pair_value {i j : Fin 3} (hij : i ≠ j) :
    majority3.value ({i, j} : Finset (Fin 3)) = 1 := by
  have hcard : ({i, j} : Finset (Fin 3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
  simp [majority3_value, hcard]

/-- **Pair coalition payoff = sum of the two coordinates.** Tautological unfolding of
`coalitionPayoff` for a two-element finset `{i, j}`. -/
lemma majority3_pair_coalitionPayoff (x : Fin 3 → ℝ) {i j : Fin 3} (hij : i ≠ j) :
    majority3.coalitionPayoff x ({i, j} : Finset (Fin 3)) = x i + x j := by
  unfold TUGameOn.coalitionPayoff
  rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]

/-- **Main theorem (empty core).** The core of the 3-player simple majority game is empty.

*Proof.* Suppose `x : Fin 3 → ℝ` is in the core. Efficiency forces `x 0 + x 1 + x 2 = 1`.
Coalitional rationality for each of the three two-player coalitions forces `x i + x j ≥ 1` for
every pair `i ≠ j`. Summing the three pair inequalities gives `2 (x 0 + x 1 + x 2) ≥ 3`, i.e.
`2 ≥ 3`, a contradiction. -/
theorem majority3_core_empty :
    ¬ ∃ x : majority3.PayoffVector, majority3.IsCore x := by
  rintro ⟨x, ⟨heff, hcoal⟩⟩
  -- Efficiency: `x 0 + x 1 + x 2 = v(Fin 3) = 1`.
  have hsum : x 0 + x 1 + x 2 = 1 := by
    simp only [TUGameOn.isEfficient_iff_sum_univ, TUGameOn.grandCoalition,
               majority3_value_univ, Fin.sum_univ_three] at heff
    linarith
  -- Each two-player coalition is worth 1, so its members must collectively get ≥ 1.
  have h01 : x 0 + x 1 ≥ 1 := by
    have := hcoal ({0, 1} : Finset (Fin 3))
    rw [majority3_pair_value (by decide : (0 : Fin 3) ≠ 1),
        majority3_pair_coalitionPayoff x (by decide : (0 : Fin 3) ≠ 1)] at this
    exact this
  have h02 : x 0 + x 2 ≥ 1 := by
    have := hcoal ({0, 2} : Finset (Fin 3))
    rw [majority3_pair_value (by decide : (0 : Fin 3) ≠ 2),
        majority3_pair_coalitionPayoff x (by decide : (0 : Fin 3) ≠ 2)] at this
    exact this
  have h12 : x 1 + x 2 ≥ 1 := by
    have := hcoal ({1, 2} : Finset (Fin 3))
    rw [majority3_pair_value (by decide : (1 : Fin 3) ≠ 2),
        majority3_pair_coalitionPayoff x (by decide : (1 : Fin 3) ≠ 2)] at this
    exact this
  -- Adding the three pair inequalities gives `2 · 1 = 2 ≥ 3`, contradiction.
  linarith

end EconlibExamples.GameTheory.MajorityGame

end
