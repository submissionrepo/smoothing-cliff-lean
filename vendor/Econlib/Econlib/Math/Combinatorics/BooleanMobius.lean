/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Finset.Interval
/-!
# Möbius inversion on finite Boolean lattices

This file collects finite inclusion-exclusion identities for functions on `Finset α`. It defines
the Boolean-lattice Möbius coefficient and the Shapley weights on subsets, and proves the
inclusion- exclusion summation identities together with the marginal-contribution / Möbius-share
relations.

## Main definitions

* `Finset.booleanMobiusCoeff` — the Möbius coefficient `∑_{S ⊆ T} (-1)^{|T|-|S|} f S`.
* `Finset.booleanShapleyWeight` — the Shapley weight of a coalition `S` for player `i`.

## Main statements

* `Finset.sum_powerset_booleanMobiusCoeff`, `Finset.sum_univ_powerset_booleanMobiusCoeff_indicator`
  — inclusion-exclusion summation identities.
* `Finset.sum_booleanShapleyWeight_marginal_eq_mobius_share` — the Shapley-weighted sum of marginal
  contributions equals the Möbius share.
* `Finset.sum_mobius_share_eq_of_symmetric_marginal` — symmetric marginals give equal Möbius shares.

## Tags

Möbius inversion, inclusion-exclusion, Boolean lattice, Shapley weight
-/

@[expose] public noncomputable section

namespace Finset

variable {α : Type*}

/-- The Boolean-lattice Möbius coefficient of `f` at `T`. -/
def booleanMobiusCoeff (f : Finset α → ℝ) (T : Finset α) : ℝ :=
  ∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * f S

/-- The Möbius coefficient at `∅` is the value at `∅`. -/
@[simp] theorem booleanMobiusCoeff_empty (f : Finset α → ℝ) :
    booleanMobiusCoeff f ∅ = f ∅ := by
  simp [booleanMobiusCoeff]

/-- The Möbius coefficient is additive in the function argument. -/
theorem booleanMobiusCoeff_add (f g : Finset α → ℝ) (T : Finset α) :
    booleanMobiusCoeff (fun S => f S + g S) T =
      booleanMobiusCoeff f T + booleanMobiusCoeff g T := by
  unfold booleanMobiusCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _hS
  ring

/-- The Möbius coefficient is homogeneous in the function argument. -/
theorem booleanMobiusCoeff_smul (a : ℝ) (f : Finset α → ℝ) (T : Finset α) :
    booleanMobiusCoeff (fun S => a * f S) T = a * booleanMobiusCoeff f T := by
  unfold booleanMobiusCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _hS
  ring

/-- Boolean-lattice Möbius inversion in subset-sum form. -/
theorem sum_powerset_booleanMobiusCoeff (f : Finset α → ℝ) (S : Finset α) :
    ∑ T ∈ S.powerset, booleanMobiusCoeff f T = f S := by
  classical
  revert f
  induction S using Finset.induction_on with
  | empty =>
      intro f
      simp [booleanMobiusCoeff]
  | insert a S haS ih =>
      intro f
      have hmobius_insert :
          ∀ T ∈ S.powerset,
            booleanMobiusCoeff f (insert a T)
              = - booleanMobiusCoeff f T
                + booleanMobiusCoeff (fun U => f (insert a U)) T := by
        intro T hT
        have hTS : T ⊆ S := Finset.mem_powerset.mp hT
        have haT : a ∉ T := fun haT => haS (hTS haT)
        rw [booleanMobiusCoeff, Finset.sum_powerset_insert haT]
        have hfirst :
            (∑ U ∈ T.powerset,
                (-1 : ℝ) ^ ((insert a T).card - U.card) * f U)
              = - booleanMobiusCoeff f T := by
          rw [booleanMobiusCoeff]
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUT : U ⊆ T := Finset.mem_powerset.mp hU
          have hcard : (insert a T).card - U.card = (T.card - U.card) + 1 := by
            have hcard_le : U.card ≤ T.card := Finset.card_le_card hUT
            rw [Finset.card_insert_of_notMem haT]
            omega
          rw [hcard, pow_succ]
          ring
        have hsecond :
            (∑ U ∈ T.powerset,
                (-1 : ℝ) ^ ((insert a T).card - (insert a U).card)
                  * f (insert a U))
              = booleanMobiusCoeff (fun U => f (insert a U)) T := by
          rw [booleanMobiusCoeff]
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUT : U ⊆ T := Finset.mem_powerset.mp hU
          have haU : a ∉ U := fun haU => haT (hUT haU)
          have hcard :
              (insert a T).card - (insert a U).card = T.card - U.card := by
            have hcard_le : U.card ≤ T.card := Finset.card_le_card hUT
            rw [Finset.card_insert_of_notMem haT, Finset.card_insert_of_notMem haU]
            omega
          rw [hcard]
        rw [hfirst, hsecond]
      rw [Finset.sum_powerset_insert haS]
      rw [ih f]
      calc
        f S + ∑ T ∈ S.powerset, booleanMobiusCoeff f (insert a T)
            = f S
              + ∑ T ∈ S.powerset,
                  (- booleanMobiusCoeff f T
                    + booleanMobiusCoeff (fun U => f (insert a U)) T) := by
                congr 1
                exact Finset.sum_congr rfl hmobius_insert
        _ = f S
              + (-(∑ T ∈ S.powerset, booleanMobiusCoeff f T)
                + ∑ T ∈ S.powerset,
                    booleanMobiusCoeff (fun U => f (insert a U)) T) := by
                simp [Finset.sum_add_distrib]
        _ = f (insert a S) := by
                rw [ih f, ih (fun U => f (insert a U))]
                ring

/-- Boolean-lattice reconstruction as a sum over all coalitions, using the unanimity-basis
indicator. The empty coefficient drops out when `f ∅ = 0`. -/
theorem sum_univ_powerset_booleanMobiusCoeff_indicator [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (hf_empty : f ∅ = 0) (S : Finset α) :
    ∑ T ∈ (Finset.univ : Finset α).powerset,
      booleanMobiusCoeff f T * (if T.Nonempty ∧ T ⊆ S then 1 else 0) = f S := by
  calc
    ∑ T ∈ (Finset.univ : Finset α).powerset,
        booleanMobiusCoeff f T * (if T.Nonempty ∧ T ⊆ S then 1 else 0)
        = ∑ T ∈ S.powerset,
            booleanMobiusCoeff f T * (if T.Nonempty ∧ T ⊆ S then 1 else 0) := by
          symm
          refine Finset.sum_subset (fun T hT => ?_) ?_
          · exact Finset.mem_powerset.mpr
              ((Finset.mem_powerset.mp hT).trans (fun _ _ => Finset.mem_univ _))
          · intro T _hTuniv hTS
            have hnot : ¬ T ⊆ S := fun h => hTS (Finset.mem_powerset.mpr h)
            simp [hnot]
    _ = ∑ T ∈ S.powerset, booleanMobiusCoeff f T := by
          apply Finset.sum_congr rfl
          intro T hT
          have hTS : T ⊆ S := Finset.mem_powerset.mp hT
          by_cases hTnon : T.Nonempty
          · simp [hTnon, hTS]
          · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTnon
            simp [hTempty, hf_empty]
    _ = f S := sum_powerset_booleanMobiusCoeff f S

/-- The Shapley coefficient attached to a predecessor set `S` in a finite Boolean lattice,
`|S|! · (n - |S| - 1)! / n!` with `n = Fintype.card α`. -/
def booleanShapleyWeight [Fintype α] (_i : α) (S : Finset α) : ℝ :=
  (S.card.factorial : ℝ) *
    ((Fintype.card α - S.card - 1).factorial : ℝ) /
      (Fintype.card α).factorial

private def booleanShapleyWeightCard (n : ℕ) (S : Finset α) : ℝ :=
  (S.card.factorial : ℝ) * ((n - S.card - 1).factorial : ℝ) / (n.factorial : ℝ)

private lemma booleanShapleyWeightCard_pair_arith {n k : ℕ} (hk : k < n) :
    (k.factorial : ℝ) * ((n + 1 - k - 1).factorial : ℝ) / ((n + 1).factorial : ℝ)
      + ((k + 1).factorial : ℝ) * ((n + 1 - (k + 1) - 1).factorial : ℝ) /
          ((n + 1).factorial : ℝ)
        = (k.factorial : ℝ) * ((n - k - 1).factorial : ℝ) / (n.factorial : ℝ) := by
  have hnfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp1fac : ((n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hn_sub_pos : 0 < n - k := Nat.sub_pos_of_lt hk
  have hn_sub_ne : n - k ≠ 0 := Nat.ne_of_gt hn_sub_pos
  have hsub1 : n + 1 - k - 1 = n - k := by omega
  have hsub2 : n + 1 - (k + 1) - 1 = n - k - 1 := by omega
  have hsucc : (k + 1).factorial = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]
  have hpred : (n - k).factorial = (n - k) * (n - k - 1).factorial :=
    (Nat.mul_factorial_pred hn_sub_ne).symm
  have hnp1 : (n + 1).factorial = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]
  have hsub_add : ((n - k : ℕ) : ℝ) + (k : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hk)
  rw [hsub1, hsub2]
  field_simp [hnfac, hnp1fac]
  norm_num [hsucc, hpred, hnp1]
  grind

private lemma sum_booleanShapleyWeightCard_union_powerset [DecidableEq α]
    (B R : Finset α) (hBR : Disjoint B R) :
    ∑ V ∈ R.powerset,
      booleanShapleyWeightCard (α := α) (B.card + R.card + 1) (B ∪ V)
        = 1 / ((B.card + 1 : ℕ) : ℝ) := by
  revert B
  induction R using Finset.induction_on with
  | empty =>
      intro B _hBR
      simp [booleanShapleyWeightCard]
      have hfac : (((B.card + 1).factorial : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (B.card + 1)
      field_simp [hfac]
      norm_num [Nat.factorial_succ]
      ring
  | insert a R haR ih =>
      intro B hBR
      have haB : a ∉ B := fun haB =>
        (Finset.disjoint_left.mp hBR) haB (Finset.mem_insert_self a R)
      have hBR' : Disjoint B R := hBR.mono_right (Finset.subset_insert _ _)
      rw [Finset.sum_powerset_insert haR]
      have hpair :
          ∀ V ∈ R.powerset,
            booleanShapleyWeightCard (α := α) (B.card + (insert a R).card + 1) (B ∪ V)
              + booleanShapleyWeightCard (α := α) (B.card + (insert a R).card + 1)
                  (B ∪ insert a V)
                =
              booleanShapleyWeightCard (α := α) (B.card + R.card + 1) (B ∪ V) := by
        intro V hV
        have hVR : V ⊆ R := Finset.mem_powerset.mp hV
        have haV : a ∉ V := fun haV => haR (hVR haV)
        have hBV : Disjoint B V := hBR'.mono_right hVR
        have hBcard : (B ∪ V).card = B.card + V.card := Finset.card_union_of_disjoint hBV
        have hBinsert_card : (B ∪ insert a V).card = (B ∪ V).card + 1 := by
          have hunion : B ∪ insert a V = insert a (B ∪ V) := by
            ext x
            by_cases hxa : x = a
            · subst hxa
              simp
            · simp [Finset.mem_union, Finset.mem_insert, hxa]
          rw [hunion, Finset.card_insert_of_notMem]
          simp [Finset.mem_union, haB, haV]
        have hn_insert : B.card + (insert a R).card + 1 = (B.card + R.card + 1) + 1 := by
          rw [Finset.card_insert_of_notMem haR]
          omega
        have hklt : (B ∪ V).card < B.card + R.card + 1 := by
          rw [hBcard]
          have hVle : V.card ≤ R.card := Finset.card_le_card hVR
          omega
        unfold booleanShapleyWeightCard
        rw [hn_insert, hBinsert_card]
        exact booleanShapleyWeightCard_pair_arith hklt
      calc
        (∑ V ∈ R.powerset,
              booleanShapleyWeightCard (α := α) (B.card + (insert a R).card + 1) (B ∪ V))
            + ∑ V ∈ R.powerset,
              booleanShapleyWeightCard (α := α) (B.card + (insert a R).card + 1)
                (B ∪ insert a V)
            =
          ∑ V ∈ R.powerset,
            booleanShapleyWeightCard (α := α) (B.card + R.card + 1) (B ∪ V) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl hpair
        _ = 1 / ((B.card + 1 : ℕ) : ℝ) := ih B hBR'

private lemma booleanShapleyWeight_eq_card [Fintype α] (i : α) (S : Finset α) :
    booleanShapleyWeight i S = booleanShapleyWeightCard (α := α) (Fintype.card α) S := by
  rfl

private lemma sum_booleanShapleyWeight_Icc_erase [Fintype α] [DecidableEq α]
    (i : α) (U : Finset α) (hiU : i ∉ U) :
    ∑ S ∈ Finset.Icc U ((Finset.univ : Finset α).erase i), booleanShapleyWeight i S =
      1 / ((U.card + 1 : ℕ) : ℝ) := by
  let R : Finset α := (Finset.univ.erase i) \ U
  have hUsub : U ⊆ (Finset.univ : Finset α).erase i := fun x hx =>
    Finset.mem_erase.mpr ⟨fun hxi => hiU (hxi ▸ hx), Finset.mem_univ x⟩
  have hUR : Disjoint U R := disjoint_sdiff_self_right
  have hcardR : R.card = (Finset.univ.erase i).card - U.card := by
    change ((Finset.univ.erase i \ U).card = (Finset.univ.erase i).card - U.card)
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUsub]
  have huniv_erase_card : (Finset.univ.erase i : Finset α).card = Fintype.card α - 1 :=
    Finset.card_erase_of_mem (Finset.mem_univ i)
  have htotal : U.card + R.card + 1 = Fintype.card α := by
    have hcard_pos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [hcardR, huniv_erase_card]
    have hUle : U.card ≤ Fintype.card α - 1 := by
      rw [← huniv_erase_card]
      exact Finset.card_le_card hUsub
    omega
  rw [Finset.Icc_eq_image_powerset hUsub]
  rw [Finset.sum_image]
  · have hsum :=
      sum_booleanShapleyWeightCard_union_powerset
        (α := α) U R hUR
    calc
      ∑ x ∈ (Finset.univ.erase i \ U).powerset, booleanShapleyWeight i (U ∪ x)
          = ∑ x ∈ R.powerset,
              booleanShapleyWeightCard (α := α) (U.card + R.card + 1) (U ∪ x) := by
            apply Finset.sum_congr
            · simp [R]
            · intro x _hx
              rw [booleanShapleyWeight_eq_card, ← htotal]
      _ = 1 / ↑(U.card + 1) := hsum
  · intro V hV W hW hVW
    have hVR : V ⊆ R := Finset.mem_powerset.mp hV
    have hWR : W ⊆ R := Finset.mem_powerset.mp hW
    ext x
    constructor
    · intro hxV
      have hxUnion : x ∈ U ∪ W := by
        simpa [hVW] using (Finset.mem_union_right U hxV : x ∈ U ∪ V)
      rcases Finset.mem_union.mp hxUnion with hxU | hxW
      · exact absurd hxU
          (Disjoint.notMem_of_mem_left_finset (Disjoint.symm hUR) (hVR hxV))
      · exact hxW
    · intro hxW
      have hxUnion : x ∈ U ∪ V := by
        simpa [hVW] using (Finset.mem_union_right U hxW : x ∈ U ∪ W)
      rcases Finset.mem_union.mp hxUnion with hxU | hxV
      · exact absurd hxU
          (Disjoint.notMem_of_mem_left_finset (Disjoint.symm hUR) (hWR hxW))
      · exact hxV

/-- The Shapley predecessor weights over all subsets excluding `i` sum to one. -/
theorem sum_booleanShapleyWeight_not_mem [Fintype α] [DecidableEq α] (i : α) :
    ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∉ S),
      booleanShapleyWeight i S = 1 := by
  have hfilter :
      (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∉ S) =
        Finset.Icc ∅ ((Finset.univ : Finset α).erase i) := by
    ext S
    constructor
    · intro hS
      have hnot : i ∉ S := (Finset.mem_filter.mp hS).2
      exact Finset.mem_Icc.mpr
        ⟨bot_le, fun x hxS =>
          Finset.mem_erase.mpr ⟨fun hxi => hnot (hxi ▸ hxS), Finset.mem_univ x⟩⟩
    · intro hS
      have hnot : i ∉ S := fun hiS =>
        Finset.notMem_erase i Finset.univ ((Finset.mem_Icc.mp hS).2 hiS)
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hnot⟩
  rw [hfilter]
  simpa using sum_booleanShapleyWeight_Icc_erase i (∅ : Finset α) (by simp)

private lemma boolean_marginal_eq_sum_mobius_insert [DecidableEq α]
    (f : Finset α → ℝ) {i : α} {S : Finset α} (hiS : i ∉ S) :
    f (insert i S) - f S =
      ∑ U ∈ S.powerset, booleanMobiusCoeff f (insert i U) := by
  have hinsert := (sum_powerset_booleanMobiusCoeff f (insert i S)).symm
  have hS := (sum_powerset_booleanMobiusCoeff f S).symm
  rw [Finset.sum_powerset_insert hiS] at hinsert
  rw [hinsert, hS]
  ring

/-- **Harsanyi-dividend representation:** the Shapley-weighted sum of marginal increments of `i`
over predecessor sets equals the sum of Möbius shares `μ(T)/|T|` over coalitions `T` containing
`i`. -/
theorem sum_booleanShapleyWeight_marginal_eq_mobius_share [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (i : α) :
    ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∉ S),
      booleanShapleyWeight i S * (f (insert i S) - f S) =
        ∑ T ∈ (Finset.univ : Finset α).powerset,
          booleanMobiusCoeff f T * (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
  let A : Finset α := (Finset.univ : Finset α).erase i
  have hfilter :
      (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∉ S)
        = A.powerset := by
    ext S
    simp [A, Finset.subset_iff]
  have hleft :
      ∑ S ∈ A.powerset,
        booleanShapleyWeight i S * (f (insert i S) - f S)
        =
      ∑ U ∈ A.powerset,
        (∑ S ∈ Finset.Icc U A, booleanShapleyWeight i S) *
          booleanMobiusCoeff f (insert i U) := by
    calc
      ∑ S ∈ A.powerset,
          booleanShapleyWeight i S * (f (insert i S) - f S)
          =
        ∑ S ∈ A.powerset,
          booleanShapleyWeight i S *
            (∑ U ∈ S.powerset, booleanMobiusCoeff f (insert i U)) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hiS : i ∉ S := fun h =>
              Finset.notMem_erase i Finset.univ (Finset.mem_powerset.mp hS h)
            rw [boolean_marginal_eq_sum_mobius_insert f hiS]
      _ =
        ∑ S ∈ A.powerset,
          ∑ U ∈ S.powerset,
            booleanShapleyWeight i S * booleanMobiusCoeff f (insert i U) := by
            simp [Finset.mul_sum]
      _ =
        ∑ U ∈ A.powerset,
          ∑ S ∈ Finset.Icc U A,
            booleanShapleyWeight i S * booleanMobiusCoeff f (insert i U) := by
            rw [Finset.sum_sigma']
            rw [Finset.sum_sigma']
            refine Finset.sum_bij'
              (fun x _hx => ⟨x.snd, x.fst⟩)
              (fun y _hy => ⟨y.snd, y.fst⟩) ?_ ?_ ?_ ?_ ?_
            · intro x hx
              simp only [Finset.mem_sigma] at hx ⊢
              rcases hx with ⟨hS, hU⟩
              have hUA : x.snd ⊆ A :=
                (Finset.mem_powerset.mp hU).trans (Finset.mem_powerset.mp hS)
              exact ⟨Finset.mem_powerset.mpr hUA,
                Finset.mem_Icc.mpr ⟨Finset.mem_powerset.mp hU, Finset.mem_powerset.mp hS⟩⟩
            · intro y hy
              simp only [Finset.mem_sigma] at hy ⊢
              rcases hy with ⟨hU, hS⟩
              have hUS : y.fst ⊆ y.snd := (Finset.mem_Icc.mp hS).1
              have hSA : y.snd ⊆ A := (Finset.mem_Icc.mp hS).2
              exact ⟨Finset.mem_powerset.mpr hSA, Finset.mem_powerset.mpr hUS⟩
            · intro x hx
              rfl
            · intro y hy
              rfl
            · intro x hx
              rfl
      _ =
        ∑ U ∈ A.powerset,
          (∑ S ∈ Finset.Icc U A, booleanShapleyWeight i S) *
            booleanMobiusCoeff f (insert i U) := by
            apply Finset.sum_congr rfl
            intro U _hU
            rw [Finset.sum_mul]
  rw [hfilter]
  rw [hleft]
  calc
    ∑ U ∈ A.powerset,
        (∑ S ∈ Finset.Icc U A, booleanShapleyWeight i S) *
          booleanMobiusCoeff f (insert i U)
        =
      ∑ U ∈ A.powerset,
        booleanMobiusCoeff f (insert i U) * (1 / ((U.card + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro U hU
        have hiU : i ∉ U := fun h =>
          Finset.notMem_erase i Finset.univ (Finset.mem_powerset.mp hU h)
        rw [sum_booleanShapleyWeight_Icc_erase i U hiU]
        ring
    _ =
      ∑ T ∈ (Finset.univ : Finset α).powerset.filter (fun T : Finset α => i ∈ T),
        booleanMobiusCoeff f T * (1 / (T.card : ℝ)) := by
        refine Finset.sum_bij'
          (fun U _hU => insert i U)
          (fun T _hT => T.erase i) ?_ ?_ ?_ ?_ ?_
        · intro U hU
          refine Finset.mem_filter.mpr ?_
          constructor
          · exact Finset.mem_powerset.mpr (fun x _hx => Finset.mem_univ x)
          · exact Finset.mem_insert_self i U
        · intro T hT
          rcases Finset.mem_filter.mp hT with ⟨_hTuniv, hiT⟩
          exact Finset.mem_powerset.mpr (by
            intro x hx
            exact Finset.mem_erase.mpr ⟨fun hxi => by simp [hxi] at hx, Finset.mem_univ x⟩)
        · intro U hU
          have hiU : i ∉ U := fun h =>
            Finset.notMem_erase i Finset.univ (Finset.mem_powerset.mp hU h)
          ext x
          simp [hiU]
        · intro T hT
          rcases Finset.mem_filter.mp hT with ⟨_hTuniv, hiT⟩
          exact Finset.insert_erase hiT
        · intro U hU
          have hiU : i ∉ U := fun h =>
            Finset.notMem_erase i Finset.univ (Finset.mem_powerset.mp hU h)
          rw [Finset.card_insert_of_notMem hiU]
    _ =
      ∑ T ∈ (Finset.univ : Finset α).powerset,
        booleanMobiusCoeff f T * (if i ∈ T then 1 / (T.card : ℝ) else 0) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro T _hT
        by_cases hiT : i ∈ T <;> simp [hiT]

/-- Symmetric marginal increments give equal Harsanyi-dividend Shapley shares. -/
theorem sum_mobius_share_eq_of_symmetric_marginal [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) {i j : α}
    (hij : ∀ S, i ∉ S → j ∉ S → f (insert i S) - f S = f (insert j S) - f S) :
    (∑ T ∈ (Finset.univ : Finset α).powerset,
      booleanMobiusCoeff f T * (if i ∈ T then 1 / (T.card : ℝ) else 0)) =
    (∑ T ∈ (Finset.univ : Finset α).powerset,
      booleanMobiusCoeff f T * (if j ∈ T then 1 / (T.card : ℝ) else 0)) := by
  rcases eq_or_ne i j with rfl | hne
  · rfl
  -- Transposition τ swapping i and j on α.
  let τ : α → α := fun x => if x = i then j else if x = j then i else x
  have hτi : τ i = j := if_pos rfl
  have hτj : τ j = i := by simp [τ]
  have hτelse : ∀ x, x ≠ i → x ≠ j → τ x = x := fun x hxi hxj => by
    simp only [τ]
    rw [if_neg hxi, if_neg hxj]
  have hτinvol : ∀ x, τ (τ x) = x := fun x => by
    by_cases hxi : x = i
    · subst hxi; rw [hτi, hτj]
    · by_cases hxj : x = j
      · subst hxj; rw [hτj, hτi]
      · rw [hτelse x hxi hxj, hτelse x hxi hxj]
  have hτinj : Function.Injective τ := Function.Involutive.injective hτinvol
  -- Set-level swap σ via image of τ.
  let σ : Finset α → Finset α := fun T => T.image τ
  have hσmem : ∀ (T : Finset α) (x : α), x ∈ σ T ↔ τ x ∈ T := fun T x => by
    refine ⟨?_, ?_⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, hτa⟩
      have hτx : τ x = a := hτa ▸ hτinvol a
      rw [hτx]; exact ha
    · intro hτx
      exact Finset.mem_image.mpr ⟨τ x, hτx, hτinvol x⟩
  have hσcard : ∀ T : Finset α, (σ T).card = T.card := fun T =>
    Finset.card_image_of_injective T hτinj
  have hσinvol : ∀ T : Finset α, σ (σ T) = T := fun T => by
    ext x; rw [hσmem, hσmem, hτinvol]
  have hσinj : Function.Injective σ := Function.Involutive.injective hσinvol
  have hσsubset : ∀ S T : Finset α, S ⊆ T → σ S ⊆ σ T := fun S T hST x hx => by
    rw [hσmem] at hx ⊢; exact hST hx
  have hσsubset_iff : ∀ S T : Finset α, σ S ⊆ σ T ↔ S ⊆ T := fun S T => by
    refine ⟨?_, hσsubset S T⟩
    intro h
    have h2 : σ (σ S) ⊆ σ (σ T) := hσsubset _ _ h
    rwa [hσinvol, hσinvol] at h2
  have hσmem_i : ∀ T, i ∈ σ T ↔ j ∈ T := fun T => by rw [hσmem, hτi]
  have hσmem_j : ∀ T, j ∈ σ T ↔ i ∈ T := fun T => by rw [hσmem, hτj]
  have hσpow : ∀ T : Finset α, T ∈ (Finset.univ : Finset α).powerset →
      σ T ∈ (Finset.univ : Finset α).powerset := fun T _ =>
    Finset.mem_powerset.mpr (fun x _ => Finset.mem_univ x)
  -- Key: μ(σ T) = μ T whenever T contains exactly one of i, j.
  have hμswap_pos : ∀ T : Finset α, i ∈ T → j ∉ T →
      booleanMobiusCoeff f (σ T) = booleanMobiusCoeff f T := by
    intros T hiT hjT
    have hpwrσ : (σ T).powerset = T.powerset.image σ := by
      ext S
      rw [Finset.mem_powerset, Finset.mem_image]
      refine ⟨?_, ?_⟩
      · intro hS
        refine ⟨σ S, Finset.mem_powerset.mpr ?_, hσinvol S⟩
        rw [show T = σ (σ T) from (hσinvol T).symm]
        exact hσsubset _ _ hS
      · rintro ⟨U, hU, rfl⟩
        rw [Finset.mem_powerset] at hU
        exact hσsubset U T hU
    unfold booleanMobiusCoeff
    rw [hpwrσ, Finset.sum_image (fun S _ S' _ h => hσinj h), hσcard T]
    apply Finset.sum_congr rfl
    intros S hS
    have hST : S ⊆ T := Finset.mem_powerset.mp hS
    have hjS : j ∉ S := fun h => hjT (hST h)
    rw [hσcard]
    by_cases hiS : i ∈ S
    · -- σ S = (S.erase i).insert j
      have hσS_eq : σ S = insert j (S.erase i) := by
        ext x
        rw [hσmem, Finset.mem_insert, Finset.mem_erase]
        by_cases hxi : x = i
        · subst hxi; rw [hτi]
          refine ⟨fun hjS' => absurd hjS' hjS, ?_⟩
          rintro (hji | ⟨hii, _⟩)
          · exact absurd hji hne
          · exact absurd rfl hii
        · by_cases hxj : x = j
          · subst hxj; rw [hτj]
            exact ⟨fun _ => Or.inl rfl, fun _ => hiS⟩
          · rw [hτelse x hxi hxj]
            refine ⟨fun hxS => Or.inr ⟨hxi, hxS⟩, ?_⟩
            rintro (rfl | ⟨_, hxS⟩)
            · exact absurd rfl hxj
            · exact hxS
      rw [hσS_eq]
      have hi_erase : i ∉ S.erase i := Finset.notMem_erase i S
      have hj_erase : j ∉ S.erase i := fun h => hjS (Finset.mem_of_mem_erase h)
      have heq := hij (S.erase i) hi_erase hj_erase
      rw [Finset.insert_erase hiS] at heq
      have hfeq : f (insert j (S.erase i)) = f S := by linarith
      rw [hfeq]
    · -- σ S = S since neither i nor j is in S.
      have hσS_eq : σ S = S := by
        ext x
        rw [hσmem]
        by_cases hxi : x = i
        · subst hxi; rw [hτi]
          exact ⟨fun h => absurd h hjS, fun h => absurd h hiS⟩
        · by_cases hxj : x = j
          · subst hxj; rw [hτj]
            exact ⟨fun h => absurd h hiS, fun h => absurd h hjS⟩
          · rw [hτelse x hxi hxj]
      rw [hσS_eq]
  have hμswap_neg : ∀ T : Finset α, i ∉ T → j ∈ T →
      booleanMobiusCoeff f (σ T) = booleanMobiusCoeff f T := by
    intros T hiT hjT
    have hiσ : i ∈ σ T := (hσmem_i T).mpr hjT
    have hjσ : j ∉ σ T := fun h => hiT ((hσmem_j T).mp h)
    have h1 := hμswap_pos (σ T) hiσ hjσ
    rw [hσinvol] at h1
    exact h1.symm
  -- Antisymmetric difference function over u.
  set u : Finset (Finset α) := (Finset.univ : Finset α).powerset with hu_def
  let h : Finset α → ℝ := fun T =>
    booleanMobiusCoeff f T *
      ((if i ∈ T then 1 / (T.card : ℝ) else 0) - (if j ∈ T then 1 / (T.card : ℝ) else 0))
  -- (LHS) - (RHS) = ∑ T ∈ u, h T.
  have hcombine :
    (∑ T ∈ u, booleanMobiusCoeff f T * (if i ∈ T then 1 / (T.card : ℝ) else 0))
    - (∑ T ∈ u, booleanMobiusCoeff f T * (if j ∈ T then 1 / (T.card : ℝ) else 0))
    = ∑ T ∈ u, h T := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros T _
    ring
  -- Pointwise antisymmetry: h(σ T) = -h(T).
  have hanti : ∀ T ∈ u, h (σ T) = -(h T) := by
    intros T _
    change booleanMobiusCoeff f (σ T) *
      ((if i ∈ σ T then 1 / ((σ T).card : ℝ) else 0)
        - (if j ∈ σ T then 1 / ((σ T).card : ℝ) else 0)) = -(h T)
    change _ = -(booleanMobiusCoeff f T *
      ((if i ∈ T then 1 / (T.card : ℝ) else 0)
        - (if j ∈ T then 1 / (T.card : ℝ) else 0)))
    rw [hσcard]
    by_cases hiT : i ∈ T
    · by_cases hjT : j ∈ T
      · have hiσ : i ∈ σ T := (hσmem_i T).mpr hjT
        have hjσ : j ∈ σ T := (hσmem_j T).mpr hiT
        simp [hiT, hjT, hiσ, hjσ]
      · have hiσ : i ∉ σ T := fun h => hjT ((hσmem_i T).mp h)
        have hjσ : j ∈ σ T := (hσmem_j T).mpr hiT
        rw [hμswap_pos T hiT hjT]
        simp [hiT, hjT, hiσ, hjσ]
    · by_cases hjT : j ∈ T
      · have hiσ : i ∈ σ T := (hσmem_i T).mpr hjT
        have hjσ : j ∉ σ T := fun h => hiT ((hσmem_j T).mp h)
        rw [hμswap_neg T hiT hjT]
        simp [hiT, hjT, hiσ, hjσ]
      · have hiσ : i ∉ σ T := fun h => hjT ((hσmem_i T).mp h)
        have hjσ : j ∉ σ T := fun h => hiT ((hσmem_j T).mp h)
        simp [hiT, hjT, hiσ, hjσ]
  -- Bijection σ on u: ∑ h T = ∑ h (σ T).
  have hbij : (∑ T ∈ u, h T) = ∑ T ∈ u, h (σ T) := by
    refine (Finset.sum_bij' (fun T _ => σ T) (fun T _ => σ T)
      hσpow hσpow ?_ ?_ ?_).symm
    · intros T _; exact hσinvol T
    · intros T _; exact hσinvol T
    · intros T _; rfl
  -- Combine to ∑ h = -∑ h, hence ∑ h = 0.
  have hsum_zero : (∑ T ∈ u, h T) = 0 := by
    have h_eq_neg : (∑ T ∈ u, h T) = -(∑ T ∈ u, h T) := by
      calc (∑ T ∈ u, h T)
          = ∑ T ∈ u, h (σ T) := hbij
        _ = ∑ T ∈ u, -(h T) := Finset.sum_congr rfl hanti
        _ = -(∑ T ∈ u, h T) := Finset.sum_neg_distrib h
    linarith
  -- Conclude LHS = RHS.
  linarith [hcombine, hsum_zero]

end Finset
