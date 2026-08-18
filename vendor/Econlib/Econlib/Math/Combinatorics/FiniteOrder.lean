/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Combinatorics.BooleanMobius
public import Mathlib.Data.Finset.Powerset
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Finite orders and predecessor sets

This module provides the finite-combinatorics API for random-order arguments: A finite order on `α`
as a bijective rank map into `Fin (Fintype.card α)`, the sets of predecessors of an element (within
the whole type or within a subset), and counting and averaging identities over orders with a
prescribed predecessor set.

## Main definitions

* `FiniteOrder` — a finite order, i.e. a bijection `α ≃ Fin (Fintype.card α)`.
* `FiniteOrder.predecessors`, `FiniteOrder.predecessorsWithin` — predecessor sets of an element.
* `FiniteOrder.ordersWithPredecessors` — orders with a prescribed predecessor set for an element.

## Main statements

* `FiniteOrder.card_ordersWithPredecessors` — counts orders with a prescribed predecessor set.
* `FiniteOrder.weighted_marginal_eq_order_sum_div_factorial`,
  `FiniteOrder.sum_marginal_predecessorsWithin_eq` — averaging identities over random orders.
* `FiniteOrder.value_le_sum_marginal_predecessors_of_marginal_mono` — a marginal-monotonicity bound.

## Tags

finite order, ranking, predecessor set, random order
-/

@[expose] public noncomputable section

open Finset

/-- A finite order on `α`, represented by a bijective rank map into `Fin (Fintype.card α)`. -/
abbrev FiniteOrder (α : Type*) [Fintype α] := α ≃ Fin (Fintype.card α)

namespace FiniteOrder

variable {α : Type*} [Fintype α]

/-- The rank of an element in a finite order. -/
def rank (ω : FiniteOrder α) (i : α) : Fin (Fintype.card α) :=
  ω i

/-- Elements strictly before `i` in the order `ω`. -/
def predecessors (ω : FiniteOrder α) (i : α) : Finset α :=
  Finset.univ.filter (fun j : α => (ω.rank j).val < (ω.rank i).val)

/-- Elements of `S` strictly before `i` in the order `ω`. -/
def predecessorsWithin (ω : FiniteOrder α) (S : Finset α) (i : α) : Finset α :=
  S.filter (fun j : α => (ω.rank j).val < (ω.rank i).val)

/-- Membership in `predecessors`: `j` precedes `i` iff its rank is strictly smaller. -/
@[simp] theorem mem_predecessors_iff (ω : FiniteOrder α) (i j : α) :
    j ∈ ω.predecessors i ↔ (ω.rank j).val < (ω.rank i).val := by
  simp [predecessors]

/-- An element is not among its own predecessors. -/
@[simp] theorem self_notMem_predecessors (ω : FiniteOrder α) (i : α) :
    i ∉ ω.predecessors i := by
  simp [predecessors]

/-- Membership in `predecessorsWithin`: `j` lies in `S` and precedes `i` in rank. -/
@[simp] theorem mem_predecessorsWithin_iff (ω : FiniteOrder α)
    (S : Finset α) (i j : α) :
    j ∈ ω.predecessorsWithin S i ↔
      j ∈ S ∧ (ω.rank j).val < (ω.rank i).val := by
  simp [predecessorsWithin]

/-- The predecessors of `i` within `S` form a subset of `S`. -/
theorem predecessorsWithin_subset (ω : FiniteOrder α) (S : Finset α) (i : α) :
    ω.predecessorsWithin S i ⊆ S := by
  intro j hj
  exact (mem_predecessorsWithin_iff ω S i j).mp hj |>.1

/-- The predecessors of `i` within `S` form a subset of all predecessors of `i`. -/
theorem predecessorsWithin_subset_predecessors (ω : FiniteOrder α)
    (S : Finset α) (i : α) :
    ω.predecessorsWithin S i ⊆ ω.predecessors i := by
  intro j hj
  exact (mem_predecessors_iff ω i j).mpr
    ((mem_predecessorsWithin_iff ω S i j).mp hj |>.2)

/-- An element is not among its own predecessors within `S`. -/
@[simp] theorem self_notMem_predecessorsWithin (ω : FiniteOrder α)
    (S : Finset α) (i : α) :
    i ∉ ω.predecessorsWithin S i := by
  simp [predecessorsWithin]

variable [DecidableEq α]

/-- Orders whose predecessor set for `i` is exactly `S`. -/
def ordersWithPredecessors (i : α) (S : Finset α) : Finset (FiniteOrder α) :=
  Finset.univ.filter (fun ω : FiniteOrder α => ω.predecessors i = S)

/-- Membership in `ordersWithPredecessors`: `ω` has predecessor set exactly `S` for `i`. -/
@[simp] theorem mem_ordersWithPredecessors_iff
    (i : α) (S : Finset α) (ω : FiniteOrder α) :
    ω ∈ ordersWithPredecessors i S ↔ ω.predecessors i = S := by
  simp [ordersWithPredecessors]

omit [DecidableEq α] in
/-- For an order `ω` whose predecessors of `i` are exactly `S`, the rank of `i` equals `S.card`. -/
private lemma rank_of_predecessors_eq (i : α) (S : Finset α)
    (ω : FiniteOrder α) (hω : ω.predecessors i = S) :
    (ω.rank i).val = S.card := by
  have h : (ω.predecessors i).card = S.card := by rw [hω]
  rw [predecessors] at h
  -- Filter cardinality via the bijection ω.rank.
  have h1 : (Finset.univ.filter
      (fun j : α => (ω.rank j).val < (ω.rank i).val)).card =
      (Finset.Iio (ω.rank i)).card := by
    refine Finset.card_bij (fun j _ => ω.rank j) ?_ ?_ ?_
    · intros j hj
      have hjlt : (ω.rank j).val < (ω.rank i).val := (Finset.mem_filter.mp hj).2
      exact Finset.mem_Iio.mpr (Fin.lt_def.mpr hjlt)
    · intros j₁ _ j₂ _ heq
      exact ω.injective heq
    · intros k hk
      refine ⟨ω.symm k, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change (ω.rank (ω.symm k)).val < (ω.rank i).val
        have hrk : ω.rank (ω.symm k) = k := ω.apply_symm_apply k
        rw [hrk]
        exact Fin.lt_def.mp (Finset.mem_Iio.mp hk)
      · change ω.rank (ω.symm k) = k
        exact ω.apply_symm_apply k
  rwa [h1, Fin.card_Iio] at h

/-- An element outside `S` and distinct from `i` lies in the complement of `insert i S`. -/
private lemma mem_sdiff_insert (i : α) (S : Finset α) {x : α}
    (hxS : x ∉ S) (hxi : x ≠ i) :
    x ∈ (Finset.univ : Finset α) \ insert i S :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
    (Finset.mem_insert.mp h).elim hxi hxS⟩

/-- An element of the complement of `insert i S` is outside `S` and distinct from `i`. -/
private lemma notMem_and_ne_of_mem_sdiff_insert (i : α) (S : Finset α) {x : α}
    (hxR : x ∈ (Finset.univ : Finset α) \ insert i S) :
    x ∉ S ∧ x ≠ i :=
  let hxnotin := (Finset.mem_sdiff.mp hxR).2
  ⟨fun h => hxnotin (Finset.mem_insert_of_mem h),
   fun h => hxnotin (h ▸ Finset.mem_insert_self _ _)⟩

/-- The number of finite orders whose predecessor set for `i` is exactly `S`.

The count is `|S|! (n-|S|-1)!`, the numerator of the Shapley weight. -/
theorem card_ordersWithPredecessors (i : α) (S : Finset α) (hiS : i ∉ S) :
    (ordersWithPredecessors i S).card =
      S.card.factorial * (Fintype.card α - S.card - 1).factorial := by
  -- Strategy: build an `Equiv`
  --   {ω // ω.predecessors i = S} ≃ ({x // x ∈ S} ≃ Fin m) ×
  --                                  ({x // x ∈ R} ≃ Fin (n - m - 1))
  -- where m = S.card, R = univ \ insert i S, n = Fintype.card α. Then use
  -- `Fintype.card_equiv` and `Fintype.card_prod`.
  set n : ℕ := Fintype.card α with hn_def
  set m : ℕ := S.card with hm_def
  -- Bounds.
  have hiS_card : (insert i S).card = m + 1 := Finset.card_insert_of_notMem hiS
  have hiS_le : (insert i S).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (insert i S))
    simpa [hn_def] using this
  have hm1_le : m + 1 ≤ n := by rw [← hiS_card]; exact hiS_le
  have hm_lt : m < n := by omega
  have hm_le : m ≤ n := le_of_lt hm_lt
  have hR_card : ((Finset.univ : Finset α) \ insert i S).card = n - m - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [hiS_card]
    change Fintype.card α - (m + 1) = n - m - 1
    omega
  -- Reduce LHS to `Fintype.card`.
  have hcard_lhs :
      (ordersWithPredecessors i S).card =
        Fintype.card {ω : FiniteOrder α // ω.predecessors i = S} :=
    (Fintype.subtype_card (ordersWithPredecessors i S)
      (fun ω => mem_ordersWithPredecessors_iff i S ω)).symm
  rw [hcard_lhs]
  -- Helper: rank of i equals m.
  have rank_i_of_pred_eq : ∀ (ω : FiniteOrder α), ω.predecessors i = S →
      (ω.rank i).val = m := fun ω hω => rank_of_predecessors_eq i S ω hω
  -- Helper: for x ∈ S, (ω x).val < m.
  have rank_S_lt : ∀ (ω : FiniteOrder α) (hω : ω.predecessors i = S)
      (x : α) (hxS : x ∈ S), (ω x).val < m := by
    intros ω hω x hxS
    rw [← rank_i_of_pred_eq ω hω]
    have : x ∈ ω.predecessors i := by rw [hω]; exact hxS
    exact (mem_predecessors_iff ω i x).mp this
  -- Helper: for x ∉ insert i S, (ω x).val ≥ m + 1.
  have rank_R_ge : ∀ (ω : FiniteOrder α) (hω : ω.predecessors i = S)
      (x : α) (hxS : x ∉ S) (hxi : x ≠ i),
      m + 1 ≤ (ω x).val := by
    intros ω hω x hxS hxi
    have hxnotpred : x ∉ ω.predecessors i := by rw [hω]; exact hxS
    have hge : (ω.rank i).val ≤ (ω x).val := by
      by_contra hlt
      exact hxnotpred ((mem_predecessors_iff ω i x).mpr (Nat.lt_of_not_ge hlt))
    have hne : (ω x).val ≠ (ω.rank i).val := by
      intro h
      have hrank : ω x = ω i := Fin.ext h
      exact hxi (ω.injective hrank)
    rw [rank_i_of_pred_eq ω hω] at hge hne
    omega
  -- Forward map: ω ↦ (σ_S, σ_R).
  let toFun : {ω : FiniteOrder α // ω.predecessors i = S} →
      ({x // x ∈ S} ≃ Fin m) × ({x // x ∈ (Finset.univ : Finset α) \ insert i S} ≃
        Fin (n - m - 1)) := fun ⟨ω, hω⟩ =>
    ⟨{ toFun := fun ⟨x, hxS⟩ => ⟨(ω x).val, rank_S_lt ω hω x hxS⟩,
       invFun := fun ⟨k, hk⟩ =>
         ⟨ω.symm ⟨k, lt_of_lt_of_le hk hm_le⟩, by
           have hpre : ω.symm ⟨k, lt_of_lt_of_le hk hm_le⟩ ∈ ω.predecessors i := by
             rw [mem_predecessors_iff]
             have hap : ω.rank (ω.symm ⟨k, lt_of_lt_of_le hk hm_le⟩) =
                 ⟨k, lt_of_lt_of_le hk hm_le⟩ := ω.apply_symm_apply _
             rw [hap]
             change k < (ω.rank i).val
             rw [rank_i_of_pred_eq ω hω]
             exact hk
           rw [hω] at hpre; exact hpre⟩,
       left_inv := by
         rintro ⟨x, hxS⟩
         apply Subtype.ext
         change ω.symm ⟨(ω x).val, _⟩ = x
         rw [Fin.eta]; exact ω.symm_apply_apply x,
       right_inv := by
         rintro ⟨k, hk⟩
         apply Fin.ext
         change (ω (ω.symm ⟨k, lt_of_lt_of_le hk hm_le⟩)).val = k
         rw [ω.apply_symm_apply] },
     { toFun := fun ⟨x, hxR⟩ =>
         ⟨(ω x).val - m - 1, by
           obtain ⟨hxS, hxi⟩ := notMem_and_ne_of_mem_sdiff_insert i S hxR
           have h1 : m + 1 ≤ (ω x).val := rank_R_ge ω hω x hxS hxi
           have h2 : (ω x).val < n := (ω x).isLt
           omega⟩,
       invFun := fun ⟨k, hk⟩ =>
         ⟨ω.symm ⟨k + m + 1, by omega⟩, by
           refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
           intro hin
           have hap : ω.rank (ω.symm ⟨k + m + 1, by omega⟩) =
               ⟨k + m + 1, by omega⟩ := ω.apply_symm_apply _
           have hkn : k + m + 1 < n := by omega
           rcases Finset.mem_insert.mp hin with hi | hS
           · have heq : ω (ω.symm ⟨k + m + 1, hkn⟩) = ω i := by rw [hi]
             rw [ω.apply_symm_apply] at heq
             have hri : (ω i).val = m := rank_i_of_pred_eq ω hω
             have hval : k + m + 1 = (ω i).val := congrArg Fin.val heq
             rw [hri] at hval
             omega
           · have hpre : ω.symm ⟨k + m + 1, hkn⟩ ∈ ω.predecessors i := by
               rw [hω]; exact hS
             rw [mem_predecessors_iff, hap] at hpre
             have hri : (ω.rank i).val = m := rank_i_of_pred_eq ω hω
             rw [hri] at hpre
             -- hpre : (⟨k + m + 1, _⟩).val < m, but k + m + 1 ≥ m + 1 > m.
             change k + m + 1 < m at hpre
             omega⟩,
       left_inv := by
         rintro ⟨x, hxR⟩
         apply Subtype.ext
         obtain ⟨hxS, hxi⟩ := notMem_and_ne_of_mem_sdiff_insert i S hxR
         have h1 : m + 1 ≤ (ω x).val := rank_R_ge ω hω x hxS hxi
         have h2 : (ω x).val < n := (ω x).isLt
         change ω.symm ⟨(ω x).val - m - 1 + m + 1, _⟩ = x
         have heq : (⟨(ω x).val - m - 1 + m + 1, by omega⟩ : Fin n) = ω x := by
           apply Fin.ext; change (ω x).val - m - 1 + m + 1 = (ω x).val; omega
         rw [heq]; exact ω.symm_apply_apply x,
       right_inv := by
         rintro ⟨k, hk⟩
         apply Fin.ext
         change (ω (ω.symm ⟨k + m + 1, _⟩)).val - m - 1 = k
         rw [ω.apply_symm_apply]
         change k + m + 1 - m - 1 = k; omega }⟩
  -- Backward map: glue (σ_S, σ_R) into ω.
  let invFun : ({x // x ∈ S} ≃ Fin m) × ({x // x ∈ (Finset.univ : Finset α) \
        insert i S} ≃ Fin (n - m - 1)) →
      {ω : FiniteOrder α // ω.predecessors i = S} := fun ⟨σS, σR⟩ =>
    let f : α → Fin n := fun x =>
      if hxS : x ∈ S then ⟨(σS ⟨x, hxS⟩).val, lt_of_lt_of_le (σS ⟨x, hxS⟩).isLt hm_le⟩
      else if hxi : x = i then ⟨m, hm_lt⟩
      else
        have hxR : x ∈ (Finset.univ : Finset α) \ insert i S :=
          mem_sdiff_insert i S hxS hxi
        ⟨(σR ⟨x, hxR⟩).val + m + 1, by
          have h1 : (σR ⟨x, hxR⟩).val < n - m - 1 := (σR ⟨x, hxR⟩).isLt
          omega⟩
    let g : Fin n → α := fun k =>
      if hk1 : k.val < m then σS.symm ⟨k.val, hk1⟩
      else if hk2 : k.val = m then i
      else
        have hk4 : k.val - m - 1 < n - m - 1 := by have := k.isLt; omega
        σR.symm ⟨k.val - m - 1, hk4⟩
    have left_inv : ∀ x, g (f x) = x := by
      intro x
      by_cases hxS : x ∈ S
      · have hlt : (σS ⟨x, hxS⟩).val < m := (σS ⟨x, hxS⟩).isLt
        have hltn : (σS ⟨x, hxS⟩).val < n := lt_of_lt_of_le hlt hm_le
        have hf : f x = ⟨(σS ⟨x, hxS⟩).val, hltn⟩ := by
          change (if _ : x ∈ S then _ else _) = _
          rw [dif_pos hxS]
        rw [hf]
        change (if _ : (⟨(σS ⟨x, hxS⟩).val, hltn⟩ : Fin n).val < m then _ else _) = x
        rw [dif_pos hlt]
        rw [Fin.eta, σS.symm_apply_apply]
      · by_cases hxi : x = i
        · subst hxi
          have hf : f x = ⟨m, hm_lt⟩ := by
            change (if _ : x ∈ S then _ else _) = _
            rw [dif_neg hxS]
            change (if _ : x = x then _ else _) = _
            rw [dif_pos rfl]
          rw [hf]
          change (if _ : (⟨m, hm_lt⟩ : Fin n).val < m then _ else _) = x
          rw [dif_neg (lt_irrefl m)]
          change (if _ : (⟨m, hm_lt⟩ : Fin n).val = m then x else _) = x
          rw [dif_pos rfl]
        · have hxR : x ∈ (Finset.univ : Finset α) \ insert i S :=
            mem_sdiff_insert i S hxS hxi
          have hRlt : (σR ⟨x, hxR⟩).val < n - m - 1 := (σR ⟨x, hxR⟩).isLt
          have hsumlt : (σR ⟨x, hxR⟩).val + m + 1 < n := by omega
          have hf : f x = ⟨(σR ⟨x, hxR⟩).val + m + 1, hsumlt⟩ := by
            change (if _ : x ∈ S then _ else _) = _
            rw [dif_neg hxS]
            change (if _ : x = i then _ else _) = _
            rw [dif_neg hxi]
          rw [hf]
          have hlt1 : ¬ ((σR ⟨x, hxR⟩).val + m + 1 < m) := by omega
          have hne : (σR ⟨x, hxR⟩).val + m + 1 ≠ m := by omega
          change (if _ : (⟨(σR ⟨x, hxR⟩).val + m + 1, hsumlt⟩ : Fin n).val < m then _ else _) = x
          rw [dif_neg hlt1]
          change (if _ : (⟨(σR ⟨x, hxR⟩).val + m + 1, hsumlt⟩ : Fin n).val = m then i else _) = x
          rw [dif_neg hne]
          have hidx_eq : (σR ⟨x, hxR⟩).val + m + 1 - m - 1 = (σR ⟨x, hxR⟩).val := by omega
          have hidx_lt : (σR ⟨x, hxR⟩).val + m + 1 - m - 1 < n - m - 1 := by
            rw [hidx_eq]; exact hRlt
          change σR.symm ⟨(σR ⟨x, hxR⟩).val + m + 1 - m - 1, hidx_lt⟩ = x
          rw [show (⟨(σR ⟨x, hxR⟩).val + m + 1 - m - 1, hidx_lt⟩ : Fin (n - m - 1)) =
                σR ⟨x, hxR⟩ from Fin.ext hidx_eq, σR.symm_apply_apply]
    have right_inv : ∀ k, f (g k) = k := by
      intro k
      by_cases hk1 : k.val < m
      · have hg : g k = σS.symm ⟨k.val, hk1⟩ := by
          change (if _ : k.val < m then _ else _) = _
          rw [dif_pos hk1]
        rw [hg]
        have hxS : (σS.symm ⟨k.val, hk1⟩ : α) ∈ S := (σS.symm ⟨k.val, hk1⟩).2
        change (if _ : (σS.symm ⟨k.val, hk1⟩ : α) ∈ S then _ else _) = k
        rw [dif_pos hxS]
        apply Fin.ext
        change (σS ⟨(σS.symm ⟨k.val, hk1⟩ : α), hxS⟩).val = k.val
        rw [Subtype.coe_eta, σS.apply_symm_apply]
      · by_cases hk2 : k.val = m
        · have hg : g k = i := by
            change (if _ : k.val < m then _ else _) = _
            rw [dif_neg hk1]
            change (if _ : k.val = m then i else _) = _
            rw [dif_pos hk2]
          rw [hg]
          change (if _ : i ∈ S then _ else _) = k
          rw [dif_neg hiS]
          change (if _ : i = i then _ else _) = k
          rw [dif_pos rfl]
          apply Fin.ext
          change m = k.val; exact hk2.symm
        · have hk4 : k.val - m - 1 < n - m - 1 := by have := k.isLt; omega
          have hg : g k = σR.symm ⟨k.val - m - 1, hk4⟩ := by
            change (if _ : k.val < m then _ else _) = _
            rw [dif_neg hk1]
            change (if _ : k.val = m then _ else _) = _
            rw [dif_neg hk2]
          rw [hg]
          have hxR : (σR.symm ⟨k.val - m - 1, hk4⟩ : α) ∈
              (Finset.univ : Finset α) \ insert i S :=
            (σR.symm ⟨k.val - m - 1, hk4⟩).2
          obtain ⟨hxnotS, hxnoti⟩ := notMem_and_ne_of_mem_sdiff_insert i S hxR
          change (if _ : (σR.symm ⟨k.val - m - 1, hk4⟩ : α) ∈ S then _ else _) = k
          rw [dif_neg hxnotS]
          change (if _ : (σR.symm ⟨k.val - m - 1, hk4⟩ : α) = i then _ else _) = k
          rw [dif_neg hxnoti]
          apply Fin.ext
          change (σR ⟨(σR.symm ⟨k.val - m - 1, hk4⟩ : α), hxR⟩).val + m + 1 = k.val
          rw [Subtype.coe_eta, σR.apply_symm_apply]
          change k.val - m - 1 + m + 1 = k.val; omega
    let ω : FiniteOrder α :=
      show α ≃ Fin n from
      { toFun := f, invFun := g, left_inv := left_inv, right_inv := right_inv }
    have hpred : ω.predecessors i = S := by
      ext x
      rw [mem_predecessors_iff]
      change (ω x).val < (ω i).val ↔ x ∈ S
      have hωi : ω i = ⟨m, hm_lt⟩ := by
        change f i = _
        change (if _ : i ∈ S then _ else _) = _
        rw [dif_neg hiS]
        change (if _ : i = i then _ else _) = _
        rw [dif_pos rfl]
      rw [hωi]
      change (ω x).val < m ↔ x ∈ S
      constructor
      · intro hlt
        by_contra hxS
        by_cases hxi : x = i
        · subst hxi; rw [hωi] at hlt; exact lt_irrefl _ hlt
        · have hxR : x ∈ (Finset.univ : Finset α) \ insert i S :=
            mem_sdiff_insert i S hxS hxi
          have hRlt : (σR ⟨x, hxR⟩).val < n - m - 1 := (σR ⟨x, hxR⟩).isLt
          have hsumlt : (σR ⟨x, hxR⟩).val + m + 1 < n := by omega
          have hfx : ω x = ⟨(σR ⟨x, hxR⟩).val + m + 1, hsumlt⟩ := by
            change f x = _
            change (if _ : x ∈ S then _ else _) = _
            rw [dif_neg hxS]
            change (if _ : x = i then _ else _) = _
            rw [dif_neg hxi]
          rw [hfx] at hlt
          change (σR ⟨x, hxR⟩).val + m + 1 < m at hlt
          omega
      · intro hxS
        have hSlt_inner : (σS ⟨x, hxS⟩).val < m := (σS ⟨x, hxS⟩).isLt
        have hSltn : (σS ⟨x, hxS⟩).val < n := lt_of_lt_of_le hSlt_inner hm_le
        have hfx : ω x = ⟨(σS ⟨x, hxS⟩).val, hSltn⟩ := by
          change f x = _
          change (if _ : x ∈ S then _ else _) = _
          rw [dif_pos hxS]
        rw [hfx]
        exact (σS ⟨x, hxS⟩).isLt
    ⟨ω, hpred⟩
  -- Build the Equiv.
  have equiv :
      {ω : FiniteOrder α // ω.predecessors i = S} ≃
        ({x // x ∈ S} ≃ Fin m) ×
        ({x // x ∈ (Finset.univ : Finset α) \ insert i S} ≃ Fin (n - m - 1)) :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        rintro ⟨ω, hω⟩
        apply Subtype.ext
        apply Equiv.ext
        intro x
        apply Fin.ext
        -- Goal: (invFun (toFun ⟨ω, hω⟩) x).val = (ω x).val
        by_cases hxS : x ∈ S
        · change (if hxS' : x ∈ S then _ else _ : Fin n).val = (ω x).val
          rw [dif_pos hxS]
          rfl
        · by_cases hxi : x = i
          · subst hxi
            change (if _ : x ∈ S then _ else _ : Fin n).val = (ω x).val
            rw [dif_neg hxS]
            change (if _ : x = x then _ else _ : Fin n).val = (ω x).val
            rw [dif_pos rfl]
            simpa using (rank_i_of_pred_eq ω hω).symm
          · have hxR : x ∈ (Finset.univ : Finset α) \ insert i S :=
              mem_sdiff_insert i S hxS hxi
            change (if _ : x ∈ S then _ else _ : Fin n).val = (ω x).val
            rw [dif_neg hxS]
            change (if _ : x = i then _ else _ : Fin n).val = (ω x).val
            rw [dif_neg hxi]
            have h1 : m + 1 ≤ (ω x).val := rank_R_ge ω hω x hxS hxi
            change (ω x).val - m - 1 + m + 1 = (ω x).val
            omega
      right_inv := by
        rintro ⟨σS, σR⟩
        ext1
        · -- σS component
          apply Equiv.ext
          rintro ⟨x, hxS⟩
          apply Fin.ext
          change ((((invFun (σS, σR)).1 : α ≃ Fin n) x).val) = (σS ⟨x, hxS⟩).val
          change (if _ : x ∈ S then _ else _ : Fin n).val = (σS ⟨x, hxS⟩).val
          rw [dif_pos hxS]
        · -- σR component
          apply Equiv.ext
          rintro ⟨x, hxR⟩
          apply Fin.ext
          obtain ⟨hxS, hxi⟩ := notMem_and_ne_of_mem_sdiff_insert i S hxR
          change ((((invFun (σS, σR)).1 : α ≃ Fin n) x).val) - m - 1 = (σR ⟨x, hxR⟩).val
          change (if _ : x ∈ S then _ else _ : Fin n).val - m - 1 = _
          rw [dif_neg hxS]
          change (if _ : x = i then _ else _ : Fin n).val - m - 1 = _
          rw [dif_neg hxi]
          change (σR ⟨x, hxR⟩).val + m + 1 - m - 1 = (σR ⟨x, hxR⟩).val
          omega }
  rw [Fintype.card_congr equiv, Fintype.card_prod,
    Fintype.card_equiv (Finset.equivFin S),
    Fintype.card_equiv (Finset.equivFinOfCardEq hR_card),
    Fintype.card_coe, Fintype.card_coe, hR_card]

/-- The subset-weight Shapley marginal formula equals the uniform sum over finite orders, scaled by
`n!`. -/
theorem weighted_marginal_eq_order_sum_div_factorial
    (f : Finset α → ℝ) (i : α) :
    (∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∉ S),
      booleanShapleyWeight i S * (f (insert i S) - f S)) =
        (∑ ω : FiniteOrder α,
          (f (insert i (ω.predecessors i)) - f (ω.predecessors i))) /
          ((Fintype.card α).factorial : ℝ) := by
  classical
  set n := Fintype.card α with hn_def
  set g : Finset α → ℝ := fun S => f (insert i S) - f S with hg_def
  have hn_fac_ne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  -- Step 1: rewrite ∑ ω, g(ω.pred) by partitioning over predecessor sets.
  have hsum_form : (∑ ω : FiniteOrder α, g (ω.predecessors i)) =
      ∑ S ∈ (Finset.univ : Finset α).powerset,
        ((ordersWithPredecessors i S).card : ℝ) * g S := by
    have hcong : ∀ ω : FiniteOrder α, g (ω.predecessors i) =
        ∑ S ∈ (Finset.univ : Finset α).powerset,
          (if ω.predecessors i = S then (1 : ℝ) else 0) * g S := by
      intro ω
      have hmem : ω.predecessors i ∈ (Finset.univ : Finset α).powerset :=
        Finset.mem_powerset.mpr (fun x _ => Finset.mem_univ x)
      rw [Finset.sum_eq_single (ω.predecessors i)]
      · simp
      · intros S _ hS; simp [hS.symm]
      · intro h; exact absurd hmem h
    rw [show (∑ ω : FiniteOrder α, g (ω.predecessors i)) =
            ∑ ω : FiniteOrder α, ∑ S ∈ (Finset.univ : Finset α).powerset,
              (if ω.predecessors i = S then (1 : ℝ) else 0) * g S from
        Finset.sum_congr rfl (fun ω _ => hcong ω)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros S _
    rw [← Finset.sum_mul]
    congr 1
    rw [ordersWithPredecessors, ← Finset.sum_boole]
  -- Step 2: orders with i ∈ predecessor-set are impossible.
  have hzero_iS : ∀ S : Finset α, i ∈ S →
      ((ordersWithPredecessors i S).card : ℝ) * g S = 0 := by
    intros S hiS
    have : ordersWithPredecessors i S = ∅ := by
      ext ω
      simp only [mem_ordersWithPredecessors_iff, Finset.notMem_empty, iff_false]
      intro h
      exact (self_notMem_predecessors ω i) (h ▸ hiS)
    rw [this]; simp
  -- Step 3: drop the parts where i ∈ S.
  have hsum_filter :
      ∑ S ∈ (Finset.univ : Finset α).powerset,
        ((ordersWithPredecessors i S).card : ℝ) * g S =
      ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S => i ∉ S),
        ((ordersWithPredecessors i S).card : ℝ) * g S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intros S hS hSnot
    have hiS : i ∈ S := by
      by_contra hi
      exact hSnot (Finset.mem_filter.mpr ⟨hS, hi⟩)
    exact hzero_iS S hiS
  -- Combine and rearrange to identify booleanShapleyWeight.
  rw [hsum_form, hsum_filter, eq_div_iff hn_fac_ne, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros S hS
  have hiS : i ∉ S := (Finset.mem_filter.mp hS).2
  rw [card_ordersWithPredecessors i S hiS]
  change booleanShapleyWeight i S * g S * (n.factorial : ℝ) =
       ((S.card.factorial * (n - S.card - 1).factorial : ℕ) : ℝ) * g S
  unfold booleanShapleyWeight
  push_cast
  field_simp
  ring

/-- Telescoping identity for building a finite set according to an arbitrary finite order. -/
theorem sum_marginal_predecessorsWithin_eq
    (f : Finset α → ℝ) (hf_empty : f ∅ = 0)
    (ω : FiniteOrder α) (S : Finset α) :
    ∑ i ∈ S, (f (insert i (ω.predecessorsWithin S i)) -
      f (ω.predecessorsWithin S i)) = f S := by
  classical
  -- Strong induction on |S|. At each step pick the maximal-rank element a ∈ S;
  -- predW S a = S.erase a, and predW S j = predW (S.erase a) j for j ∈ S.erase a.
  suffices hclaim : ∀ n, ∀ S : Finset α, S.card = n →
      ∑ i ∈ S, (f (insert i (ω.predecessorsWithin S i)) -
        f (ω.predecessorsWithin S i)) = f S from hclaim S.card S rfl
  intro n
  induction n with
  | zero =>
    intros S hS
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS
    subst hSempty
    simp [hf_empty]
  | succ n ih =>
    intros S hS
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, haS, ha_max⟩ := S.exists_max_image (fun j => (ω.rank j).val) hSne
    have ha_rank_max : ∀ b ∈ S, b ≠ a → (ω.rank b).val < (ω.rank a).val := by
      intros b hbS hba
      rcases lt_or_eq_of_le (ha_max b hbS) with h | h
      · exact h
      · exact absurd (ω.injective (Fin.ext h)) hba
    -- predW S a = S.erase a
    have h_predW_S_a : ω.predecessorsWithin S a = S.erase a := by
      ext j
      simp only [mem_predecessorsWithin_iff, Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro ⟨hjS, hlt⟩
        refine ⟨?_, hjS⟩
        intro h; subst h; exact absurd hlt (lt_irrefl _)
      · rintro ⟨hja, hjS⟩
        exact ⟨hjS, ha_rank_max j hjS hja⟩
    -- For j ∈ S.erase a: predW S j = predW (S.erase a) j
    have h_predW_T : ∀ j ∈ S.erase a,
        ω.predecessorsWithin S j = ω.predecessorsWithin (S.erase a) j := by
      intros j hj
      obtain ⟨hja, hjS⟩ := Finset.mem_erase.mp hj
      have hjlt : (ω.rank j).val < (ω.rank a).val := ha_rank_max j hjS hja
      ext k
      simp only [mem_predecessorsWithin_iff, Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro ⟨hkS, hlt⟩
        refine ⟨⟨?_, hkS⟩, hlt⟩
        intro h; subst h
        exact absurd (lt_trans hjlt hlt) (lt_irrefl _)
      · rintro ⟨⟨_, hkS⟩, hlt⟩
        exact ⟨hkS, hlt⟩
    have hT_card : (S.erase a).card = n := by
      rw [Finset.card_erase_of_mem haS]; omega
    -- Split the sum at `a`.
    rw [← Finset.sum_erase_add S _ haS, h_predW_S_a, Finset.insert_erase haS,
      show ∑ i ∈ S.erase a, (f (insert i (ω.predecessorsWithin S i)) -
              f (ω.predecessorsWithin S i)) =
            ∑ i ∈ S.erase a, (f (insert i (ω.predecessorsWithin (S.erase a) i)) -
              f (ω.predecessorsWithin (S.erase a) i)) from
        Finset.sum_congr rfl (fun j hj => by rw [h_predW_T j hj]),
      ih (S.erase a) hT_card]
    ring

/-- If marginal increments are monotone in the predecessor set, then for each finite order, the sum
of all-predecessor marginal increments of members of `S` dominates the telescoping value of `S`. -/
theorem value_le_sum_marginal_predecessors_of_marginal_mono
    (f : Finset α → ℝ) (hf_empty : f ∅ = 0)
    (hmono : ∀ {A B : Finset α} {i : α}, A ⊆ B → i ∉ B →
      f (insert i A) - f A ≤ f (insert i B) - f B)
    (ω : FiniteOrder α) (S : Finset α) :
    f S ≤ ∑ i ∈ S, (f (insert i (ω.predecessors i)) - f (ω.predecessors i)) := by
  rw [← sum_marginal_predecessorsWithin_eq f hf_empty ω S]
  refine Finset.sum_le_sum ?_
  intro i hiS
  exact hmono
    (predecessorsWithin_subset_predecessors ω S i)
    (self_notMem_predecessors ω i)

end FiniteOrder
