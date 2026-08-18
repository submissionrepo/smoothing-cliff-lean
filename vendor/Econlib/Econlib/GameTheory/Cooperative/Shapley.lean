/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.ValueRule
import Econlib.Math.Combinatorics.BooleanMobius
import Econlib.Math.Combinatorics.FiniteOrder

/-!
# The Shapley value

This file defines the **Shapley value** `shapleyValue : TUGameOn Player → Player → ℝ` from the
classical weighted-marginal-contribution formula (Shapley 1953), gives its Harsanyi-dividend
representation, and proves the axiomatic uniqueness theorem: The Shapley value is the unique value
rule satisfying efficiency, symmetry, the dummy axiom, and linearity. The canonical
`ValueRule.shapley` packages the construction at the value-rule level and is shown to satisfy each
of the four axioms.

## Main definitions

* `TUGameOn.shapleyWeight`: The Shapley coefficient for a marginal contribution.
* `TUGameOn.shapleyValue`: The Shapley payoff vector of a TU game.
* `ValueRule.shapley`: The canonical Shapley value rule.

## Main statements

* `TUGameOn.shapleyValue_eq_harsanyi`: Harsanyi-dividend representation of the Shapley value.
* `TUGameOn.shapleyValue_unique`: Uniqueness from the Shapley axioms.
* `ValueRule.shapley_satisfiesShapleyAxioms`: The Shapley value satisfies the bundled axioms.

## References

* Shapley, Lloyd S. 1953. “A Value for n-Person Games.” In *Contributions to the Theory of Games,
  Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

cooperative game, shapley value, harsanyi dividend
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

open Finset

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Shapley coefficient for a coalition not containing player `i`. -/
def shapleyWeight (_i : Player) (S : Finset Player) : ℝ :=
  Finset.booleanShapleyWeight _i S

private lemma shapley_coeff_cancel_arith {n k : ℕ} (hk0 : 0 < k) (hkn : k < n) :
    k * ((k - 1).factorial * (n - k).factorial / (n.factorial : ℝ)) =
      (n - k : ℕ) * (k.factorial * (n - k - 1).factorial / n.factorial) := by
  have hnfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hnfac]
  have hkfac : k * (k - 1).factorial = k.factorial :=
    Nat.mul_factorial_pred (Nat.ne_of_gt hk0)
  have hnkfac : (n - k) * (n - k - 1).factorial = (n - k).factorial :=
    Nat.mul_factorial_pred (Nat.ne_of_gt (Nat.sub_pos_of_lt hkn))
  have hnat : k.factorial * (n - k).factorial =
      (n - k) * k.factorial * (n - k - 1).factorial := by
    rw [← hnkfac]; ring
  rw [← Nat.cast_mul, hkfac]
  exact_mod_cast hnat

private lemma shapley_coeff_grand_arith {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (((n - 1).factorial : ℝ) * ((0).factorial : ℝ) / (n.factorial : ℝ)) = 1 := by
  have hnfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hnfac]
  rw [← Nat.cast_mul, Nat.mul_factorial_pred (Nat.ne_of_gt hn)]
  norm_num

private def shapleyPositiveCoeff (_G : TUGameOn Player) (T : Finset Player) : ℝ :=
  ∑ i ∈ T, shapleyWeight (Player := Player) i (T.erase i)

private def shapleyNegativeCoeff (_G : TUGameOn Player) (T : Finset Player) : ℝ :=
  ∑ i ∈ (Finset.univ.filter (fun i : Player => i ∉ T)),
    shapleyWeight (Player := Player) i T

private def shapleyCoeff (G : TUGameOn Player) (T : Finset Player) : ℝ :=
  G.shapleyPositiveCoeff T - G.shapleyNegativeCoeff T

private lemma shapleyPositiveCoeff_eq (G : TUGameOn Player) (T : Finset Player)
    (hT : T.Nonempty) :
    G.shapleyPositiveCoeff T =
      (T.card : ℝ) * (((T.card - 1).factorial : ℝ) *
        ((Fintype.card Player - T.card).factorial : ℝ) / (Fintype.card Player).factorial) := by
  unfold shapleyPositiveCoeff shapleyWeight booleanShapleyWeight
  have hTle : T.card ≤ Fintype.card Player := Finset.card_le_univ T
  have hTpos : 0 < T.card := Finset.card_pos.mpr hT
  have hconst : ∀ i ∈ T,
      (T.erase i).card.factorial * ((Fintype.card Player - (T.erase i).card - 1).factorial : ℝ) /
        (Fintype.card Player).factorial = ((T.card - 1).factorial *
          (Fintype.card Player - T.card).factorial  / (Fintype.card Player).factorial) := by
    intro i hi
    have hcard : (T.erase i).card = T.card - 1 := Finset.card_erase_of_mem hi
    have hsub : Fintype.card Player - (T.card - 1) - 1 = Fintype.card Player - T.card := by omega
    rw [hcard, hsub]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

private lemma shapleyNegativeCoeff_eq (G : TUGameOn Player) (T : Finset Player) :
    G.shapleyNegativeCoeff T =
      ((Fintype.card Player - T.card : ℕ) : ℝ) *
        ((T.card.factorial : ℝ) *
          ((Fintype.card Player - T.card - 1).factorial : ℝ) /
            (Fintype.card Player).factorial) := by
  unfold shapleyNegativeCoeff shapleyWeight booleanShapleyWeight
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfilter :
      Finset.univ.filter (fun i : Player => i ∉ T) = (Finset.univ : Finset Player) \ T := by
    ext i; simp
  have hcard : (Finset.univ.filter (fun i : Player => i ∉ T)).card =
      Fintype.card Player - T.card := by
    rw [hfilter, Finset.card_sdiff]; simp
  exact_mod_cast hcard

private lemma shapleyCoeff_eq_zero_of_nonempty_ne_univ (G : TUGameOn Player)
    (T : Finset Player) (hT : T.Nonempty) (hTne : T ≠ Finset.univ) :
    G.shapleyCoeff T = 0 := by
  unfold shapleyCoeff
  rw [G.shapleyPositiveCoeff_eq T hT, G.shapleyNegativeCoeff_eq T]
  have hk0 : 0 < T.card := Finset.card_pos.mpr hT
  have hkn : T.card < Fintype.card Player := by
    have hss : T ⊂ (Finset.univ : Finset Player) :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨Finset.subset_univ T, hTne⟩
    simpa [Finset.card_univ] using Finset.card_lt_card hss
  rw [shapley_coeff_cancel_arith hk0 hkn]; ring

private lemma shapleyCoeff_univ_of_nonempty (G : TUGameOn Player)
    (hN : (Finset.univ : Finset Player).Nonempty) :
    G.shapleyCoeff Finset.univ = 1 := by
  unfold shapleyCoeff
  rw [G.shapleyPositiveCoeff_eq Finset.univ hN, G.shapleyNegativeCoeff_eq Finset.univ]
  have hn : 0 < Fintype.card Player := by
    simpa [Finset.card_univ] using Finset.card_pos.mpr hN
  simpa [Nat.sub_self, Nat.factorial_zero, one_mul] using
    (shapley_coeff_grand_arith (n := Fintype.card Player) hn)

private lemma shapley_positive_reindex (G : TUGameOn Player) :
    (∑ i : Player,
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        shapleyWeight (Player := Player) i S * G.value (insert i S)) =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.shapleyPositiveCoeff T * G.value T := by
  unfold shapleyPositiveCoeff
  rw [Finset.sum_sigma']
  conv_rhs => arg 2; intro T; rw [Finset.sum_mul]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _hx => ⟨insert x.fst x.snd, x.fst⟩)
    (fun y _hy => ⟨y.snd, y.fst.erase y.snd⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset (Finset.mem_univ _)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hx).1)), ?_⟩
    simp
  · intro y hy
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hy ⊢
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hy.1)),
        by simp⟩
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    have hiS : x.fst ∉ x.snd := (Finset.mem_filter.mp hx).2
    ext <;> simp [hiS]
  · intro y hy
    simp only [Finset.mem_sigma] at hy
    ext <;> simp [hy.2]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    have hiS : x.fst ∉ x.snd := (Finset.mem_filter.mp hx).2
    simp [hiS]

private lemma shapley_negative_reindex (G : TUGameOn Player) :
    (∑ i : Player,
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        shapleyWeight (Player := Player) i S * G.value S) =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.shapleyNegativeCoeff T * G.value T := by
  unfold shapleyNegativeCoeff
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∉ T <;> simp [hi]

private lemma shapleyValue_sum_reindex (G : TUGameOn Player) :
    (∑ i : Player,
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        shapleyWeight (Player := Player) i S * G.marginalContribution i S) =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.shapleyCoeff T * G.value T := by
  unfold marginalContribution shapleyCoeff
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [G.shapley_positive_reindex, G.shapley_negative_reindex, ← Finset.sum_sub_distrib]
  simp only [sub_mul]

/-- The **Shapley value** of a fixed-player TU game (Shapley 1953): The weighted average of player
`i`'s marginal contributions over all coalitions not containing `i`. -/
def shapleyValue (G : TUGameOn Player) (i : Player) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
    shapleyWeight (Player := Player) i S * G.marginalContribution i S

/-- Harsanyi-dividend representation of the Shapley value. -/
theorem shapleyValue_eq_harsanyi (G : TUGameOn Player) (i : Player) :
    G.shapleyValue i =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.harsanyiDividend T *
          (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
  unfold shapleyValue marginalContribution TUGameOn.harsanyiDividend
  exact Finset.sum_booleanShapleyWeight_marginal_eq_mobius_share
    G.value i

end TUGameOn

namespace ValueRule

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- The canonical Shapley value rule on fixed-player TU games. -/
def shapley : ValueRule Player :=
  fun G => G.shapleyValue

end ValueRule

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- **Shapley value uniqueness** (Shapley 1953): Any value rule satisfying efficiency, symmetry,
the dummy axiom, and linearity agrees with the Shapley value on every fixed-player game. -/
theorem shapleyValue_unique (G : TUGameOn Player)
    (φ : ValueRule Player)
    (heff : ValueRule.SatisfiesEfficiency φ)
    (hsym : ValueRule.SatisfiesSymmetry φ)
    (hdummy : ValueRule.SatisfiesDummy φ)
    (hlin : ValueRule.SatisfiesLinearity φ) :
    φ G = G.shapleyValue := by
  funext i
  calc
    φ G i = φ G.harsanyiExpansion i := by rw [TUGameOn.harsanyiExpansion_eq G]
    _ = ∑ T ∈ (Finset.univ : Finset Player).powerset,
          G.harsanyiDividend T * φ (TUGameOn.unanimity T) i := by rw [hlin.harsanyiExpansion]
    _ = ∑ T ∈ (Finset.univ : Finset Player).powerset,
          G.harsanyiDividend T *
            (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [congrFun (ValueRule.unanimity_unique heff hsym hdummy T) i]
    _ = G.shapleyValue i := by rw [G.shapleyValue_eq_harsanyi i]

end TUGameOn

namespace ValueRule

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- The Shapley value satisfies additivity. -/
theorem shapley_satisfiesAdditivity :
    SatisfiesAdditivity (shapley : ValueRule Player) := by
  intro G H i
  simp only [shapley]
  rw [(G.add H).shapleyValue_eq_harsanyi i, G.shapleyValue_eq_harsanyi i,
    H.shapleyValue_eq_harsanyi i]
  calc
    ∑ T ∈ (Finset.univ : Finset Player).powerset,
        (G.add H).harsanyiDividend T * (if i ∈ T then 1 / (T.card : ℝ) else 0)
        =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        (G.harsanyiDividend T + H.harsanyiDividend T) *
          (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        congr 1
        simp [TUGameOn.harsanyiDividend, TUGameOn.add, booleanMobiusCoeff_add]
    _ =
      (∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.harsanyiDividend T * (if i ∈ T then 1 / (T.card : ℝ) else 0)) +
      (∑ T ∈ (Finset.univ : Finset Player).powerset,
        H.harsanyiDividend T * (if i ∈ T then 1 / (T.card : ℝ) else 0)) := by
        simp only [add_mul, Finset.sum_add_distrib]

/-- The Shapley value satisfies homogeneity. -/
theorem shapley_satisfiesHomogeneity :
    SatisfiesHomogeneity (shapley : ValueRule Player) := by
  intro a G i
  simp only [shapley]
  rw [(G.smul a).shapleyValue_eq_harsanyi i, G.shapleyValue_eq_harsanyi i]
  calc
    ∑ T ∈ (Finset.univ : Finset Player).powerset,
        (G.smul a).harsanyiDividend T * (if i ∈ T then 1 / (T.card : ℝ) else 0)
        =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        (a * G.harsanyiDividend T) * (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        congr 1
        simp [TUGameOn.harsanyiDividend, TUGameOn.smul, booleanMobiusCoeff_smul]
    _ =
      a *
        (∑ T ∈ (Finset.univ : Finset Player).powerset,
          G.harsanyiDividend T * (if i ∈ T then 1 / (T.card : ℝ) else 0)) := by
        simp only [mul_assoc, Finset.mul_sum]

/-- The Shapley value satisfies linearity. -/
theorem shapley_satisfiesLinearity :
    SatisfiesLinearity (shapley : ValueRule Player) :=
  ⟨shapley_satisfiesAdditivity, shapley_satisfiesHomogeneity⟩

/-- The Shapley value satisfies symmetry. -/
theorem shapley_satisfiesSymmetry :
    SatisfiesSymmetry (shapley : ValueRule Player) := by
  intro G i j hij
  change G.shapleyValue i = G.shapleyValue j
  rw [TUGameOn.shapleyValue_eq_harsanyi G i, TUGameOn.shapleyValue_eq_harsanyi G j]
  exact sum_mobius_share_eq_of_symmetric_marginal
    G.value (fun S hiS hjS => by simpa [TUGameOn.marginalContribution] using hij S hiS hjS)

/-- The Shapley value satisfies the dummy-player axiom. -/
theorem shapley_satisfiesDummy :
    SatisfiesDummy (shapley : ValueRule Player) := by
  intro G i hi
  unfold shapley TUGameOn.shapleyValue
  calc
    ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        TUGameOn.shapleyWeight (Player := Player) i S * G.marginalContribution i S
        =
      ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        TUGameOn.shapleyWeight (Player := Player) i S * G.value {i} := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [hi S (Finset.mem_filter.mp hS).2]
    _ =
      (∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
        TUGameOn.shapleyWeight (Player := Player) i S) * G.value {i} := by rw [Finset.sum_mul]
    _ = G.value {i} := by
        have hweights :
            ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset Player => i ∉ S),
              TUGameOn.shapleyWeight (Player := Player) i S = 1 := by
          simpa [TUGameOn.shapleyWeight] using (sum_booleanShapleyWeight_not_mem (α := Player) i)
        rw [hweights, one_mul]

/-- The Shapley value satisfies efficiency.

This is the value-rule statement; the single-game `shapleyValue_efficient` form lives in
`Core.lean`. -/
theorem shapley_satisfiesEfficiency :
    SatisfiesEfficiency (shapley : ValueRule Player) := by
  intro G
  unfold shapley TUGameOn.shapleyValue
  rw [G.shapleyValue_sum_reindex]
  by_cases hN : (Finset.univ : Finset Player).Nonempty
  · rw [Finset.sum_eq_single (Finset.univ : Finset Player)]
    · rw [G.shapleyCoeff_univ_of_nonempty hN, one_mul]
    · intro T _ hTne
      by_cases hTempty : T = ∅
      · simp [hTempty, G.value_empty]
      · rw [G.shapleyCoeff_eq_zero_of_nonempty_ne_univ T
          (Finset.nonempty_iff_ne_empty.mpr hTempty) hTne, zero_mul]
    · exact fun hnot => (hnot (Finset.mem_powerset.mpr (Finset.subset_univ _))).elim
  · have h_univ_empty : (Finset.univ : Finset Player) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hN
    simp [h_univ_empty, TUGameOn.shapleyCoeff, TUGameOn.shapleyPositiveCoeff,
      TUGameOn.shapleyNegativeCoeff, G.value_empty]

/-- The Shapley value satisfies the bundled Shapley axioms. -/
theorem shapley_satisfiesShapleyAxioms :
    SatisfiesShapleyAxioms (shapley : ValueRule Player) :=
  ⟨shapley_satisfiesEfficiency, shapley_satisfiesSymmetry,
    shapley_satisfiesDummy, shapley_satisfiesLinearity⟩

end ValueRule

end Econlib.GameTheory
