/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.LinearAlgebra.FarkasCone
public import Econlib.Math.MeasureTheory.DiracSum
public import Econlib.Optimization.OptimalTransport.KantorovichRubinstein
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite Kantorovich–Rubinstein duality

This file proves finite-dimensional linear-programing duality for Kantorovich–Rubinstein transport.
The finite problem is stated on `Fin n`: Couplings are nonnegative matrices with prescribed row and
column sums, the cost is a finite metric matrix, and dual variables are finite **1-Lipschitz**
potentials. The main theorem equates the supremum of the Lipschitz-potential objective with the
infimum of the coupling cost.

## Main definitions

* `finCouplings` — nonnegative coupling matrices with fixed marginals.
* `finLipschitz`, `finLipschitzZero` — finite 1-Lipschitz potentials and their basepoint
  normalization.
* `IsFiniteMetricCost` — the metric axioms (nonnegativity, identity of indiscernibles, symmetry,
  triangle inequality) on a finite cost matrix.

## Main statements

* `fin_kr_duality` — finite-dimensional Kantorovich–Rubinstein duality: The Lipschitz-potential
  supremum equals the coupling-cost infimum for a finite metric cost between probability vectors.
* `fin_two_potential_strict_lower_bound` — the Farkas separation step underlying strong duality.
* `krDist_eq_krTransportCost_of_finsupp` — Kantorovich–Rubinstein duality for laws supported on a
  finite subset of a compact metric space.

## References

* Kantorovich, Leonid V. 1942. “On the Translocation of Masses.” *Doklady Akademii Nauk SSSR* 37 :
  199–201.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

kantorovich-rubinstein, optimal transport, linear programing, duality, farkas, coupling
-/

@[expose] public section

open MeasureTheory Set Matrix
open Econlib.Probability Econlib.Probability.ProbDist
open scoped BigOperators

namespace Econlib.Optimization.OptimalTransport

/-- Finite couplings as nonnegative matrices with fixed marginals. -/
def finCouplings (n : ℕ) (p q : Fin n → ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  { π | (∀ i j, 0 ≤ π i j)
      ∧ (∀ i, ∑ j, π i j = p i)
      ∧ (∀ j, ∑ i, π i j = q j) }

/-- The finite coupling polytope is closed. -/
lemma finCouplings_isClosed (n : ℕ) (p q : Fin n → ℝ) :
    IsClosed (finCouplings n p q) := by
  change IsClosed {π : Matrix (Fin n) (Fin n) ℝ |
      (∀ i j, 0 ≤ π i j)
        ∧ (∀ i, ∑ j, π i j = p i)
        ∧ (∀ j, ∑ i, π i j = q j)}
  have hnonneg : IsClosed {π : Matrix (Fin n) (Fin n) ℝ | ∀ i j, 0 ≤ π i j} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun i =>
        isClosed_iInter (fun j =>
          isClosed_le continuous_const (continuous_apply_apply i j)))
  have hrow : IsClosed {π : Matrix (Fin n) (Fin n) ℝ |
      ∀ i, ∑ j, π i j = p i} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun i =>
        isClosed_eq
          (continuous_finset_sum _ fun j _ => continuous_apply_apply i j)
          continuous_const)
  have hcol : IsClosed {π : Matrix (Fin n) (Fin n) ℝ |
      ∀ j, ∑ i, π i j = q j} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun j =>
        isClosed_eq
          (continuous_finset_sum _ fun i _ => continuous_apply_apply i j)
          continuous_const)
  simpa [and_assoc] using hnonneg.inter (hrow.inter hcol)

/-- The finite coupling polytope is coordinatewise bounded. -/
lemma finCouplings_entry_bounded (n : ℕ) (p q : Fin n → ℝ) :
    ∃ C : ℝ, ∀ π ∈ finCouplings n p q, ∀ i j, |π i j| ≤ C := by
  refine ⟨∑ i, |p i|, ?_⟩
  intro π hπ i j
  rcases hπ with ⟨hnonneg, hrow, hcol⟩
  have hentry_le_row : π i j ≤ ∑ k, π i k :=
    Finset.single_le_sum (fun k _ => hnonneg i k) (Finset.mem_univ j)
  have hentry_le_p : π i j ≤ p i := by
    simpa [hrow i] using hentry_le_row
  have hp_le_sum : |p i| ≤ ∑ k, |p k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (p k)) (Finset.mem_univ i)
  calc |π i j|
      = π i j := abs_of_nonneg (hnonneg i j)
    _ ≤ p i := hentry_le_p
    _ ≤ |p i| := le_abs_self (p i)
    _ ≤ ∑ k, |p k| := hp_le_sum

/-- The finite coupling polytope is compact. -/
lemma finCouplings_isCompact (n : ℕ) (p q : Fin n → ℝ) :
    IsCompact (finCouplings n p q) := by
  obtain ⟨C, hC⟩ := finCouplings_entry_bounded n p q
  have hbox : IsCompact ((Set.Icc (-C) C).matrix :
      Set (Matrix (Fin n) (Fin n) ℝ)) :=
    (isCompact_Icc : IsCompact (Set.Icc (-C) C)).matrix
  exact hbox.of_isClosed_subset (finCouplings_isClosed n p q) (by
    intro π hπ
    rw [Set.mem_matrix]
    intro i j
    exact abs_le.mp (hC π hπ i j))

/-- Product weights give a finite coupling whenever both marginals are probability vectors. -/
lemma finCouplings_nonempty (n : ℕ) (p q : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    (finCouplings n p q).Nonempty := by
  refine ⟨fun i j => p i * q j, ?_⟩
  constructor
  · intro i j
    exact mul_nonneg (hp i) (hq j)
  constructor
  · intro i
    calc ∑ j, p i * q j
        = p i * ∑ j, q j := by rw [Finset.mul_sum]
      _ = p i := by rw [hq_sum, mul_one]
  · intro j
    calc ∑ i, p i * q j
        = (∑ i, p i) * q j := by rw [Finset.sum_mul]
      _ = q j := by rw [hp_sum, one_mul]

/-- Finite 1-Lipschitz potentials for a cost matrix. -/
def finLipschitz (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  { φ | ∀ i j, φ i - φ j ≤ d i j }

/-- Finite Lipschitz potentials form a closed set. -/
lemma finLipschitz_isClosed (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ) :
    IsClosed (finLipschitz n d) := by
  simpa [finLipschitz, Set.setOf_forall] using
    isClosed_iInter (fun i =>
      isClosed_iInter (fun j =>
        isClosed_le
          ((show Continuous (fun φ : Fin n → ℝ => φ i) from continuous_apply i).sub
            (show Continuous (fun φ : Fin n → ℝ => φ j) from continuous_apply j))
          continuous_const))

/-- Normalized finite Lipschitz potentials. -/
def finLipschitzZero (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ) :
    Set (Fin n → ℝ) :=
  finLipschitz n d ∩ {φ | ∀ h : (0 : ℕ) < n, φ ⟨0, h⟩ = 0}

/-- Normalized finite Lipschitz potentials are compact. -/
lemma finLipschitzZero_isCompact (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ)
    (hd_nonneg : ∀ i j, 0 ≤ d i j)
    (hd_symm : ∀ i j, d i j = d j i)
    (hd_triangle : ∀ i j k, d i k ≤ d i j + d j k) :
    IsCompact (finLipschitzZero n d) := by
  have _htriangle := hd_triangle
  have hnorm_closed : IsClosed
      {φ : Fin n → ℝ | ∀ h : (0 : ℕ) < n, φ ⟨0, h⟩ = 0} := by
    by_cases hn : (0 : ℕ) < n
    · let z : Fin n := ⟨0, hn⟩
      have hset :
          {φ : Fin n → ℝ | ∀ h : (0 : ℕ) < n, φ ⟨0, h⟩ = 0}
            = {φ : Fin n → ℝ | φ z = 0} := by
        ext φ
        constructor
        · intro hφ
          exact hφ hn
        · intro hφ h
          simpa using hφ
      rw [hset]
      exact isClosed_eq
        (show Continuous (fun φ : Fin n → ℝ => φ z) from
          continuous_apply z)
        continuous_const
    · have hset :
          {φ : Fin n → ℝ | ∀ h : (0 : ℕ) < n, φ ⟨0, h⟩ = 0}
            = Set.univ := by
        ext φ
        simp [hn]
      rw [hset]
      exact isClosed_univ
  have hclosed : IsClosed (finLipschitzZero n d) := by
    simpa [finLipschitzZero] using (finLipschitz_isClosed n d).inter hnorm_closed
  by_cases hn : (0 : ℕ) < n
  · let z : Fin n := ⟨0, hn⟩
    let C : ℝ := ∑ i, d i z
    have hbox : IsCompact
        (Set.univ.pi fun _i : Fin n => Set.Icc (-C) C) :=
      isCompact_univ_pi fun _i : Fin n => isCompact_Icc
    exact hbox.of_isClosed_subset hclosed (by
      intro φ hφ
      rcases hφ with ⟨hLip, hzero⟩
      rw [Set.mem_pi]
      intro i _hi
      have hi_le_C : d i z ≤ C :=
        Finset.single_le_sum (fun k _ => hd_nonneg k z) (Finset.mem_univ i)
      have hz_le_C : d z i ≤ C := by
        rw [hd_symm z i]
        exact hi_le_C
      have hupper : φ i ≤ C := by
        have hLip_i : φ i - φ z ≤ d i z := hLip i z
        have hz_zero : φ z = 0 := hzero hn
        linarith
      have hlower : -C ≤ φ i := by
        have hLip_z : φ z - φ i ≤ d z i := hLip z i
        have hz_zero : φ z = 0 := hzero hn
        linarith
      exact ⟨hlower, hupper⟩)
  · have hbox : IsCompact
        (Set.univ.pi fun _i : Fin n => Set.Icc (0 : ℝ) 0) :=
      isCompact_univ_pi fun _i : Fin n => isCompact_Icc
    exact hbox.of_isClosed_subset hclosed (by
      intro φ hφ
      rw [Set.mem_pi]
      intro i _hi
      exact False.elim (hn (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)))

/-- Metric-cost axioms for a finite cost matrix. -/
structure IsFiniteMetricCost (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ d i j
  eq_zero_iff : ∀ i j, d i j = 0 ↔ i = j
  symm : ∀ i j, d i j = d j i
  triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- Farkas separation for the finite transport LP: Every strict lower bound on the primal value is
beaten by feasible two-potential dual variables. -/
lemma fin_two_potential_strict_lower_bound (n : ℕ)
    (d : Matrix (Fin n) (Fin n) ℝ)
    (hd_nonneg : ∀ i j, 0 ≤ d i j)
    (p q : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1)
    (R : ℝ)
    (hR : R < sInf
      ((fun π : Matrix (Fin n) (Fin n) ℝ => ∑ i, ∑ j, π i j * d i j)
        '' finCouplings n p q)) :
    ∃ u v : Fin n → ℝ,
      (∀ i j, u i + v j ≤ d i j) ∧
      R < (∑ i, u i * p i) + (∑ j, v j * q j) := by
  classical
  let primalObj : Matrix (Fin n) (Fin n) ℝ → ℝ := fun π => ∑ i, ∑ j, π i j * d i j
  let Pset : Set ℝ := primalObj '' finCouplings n p q
  change R < sInf Pset at hR
  have hP_bddBelow : BddBelow Pset := by
    refine ⟨0, ?_⟩
    rintro y ⟨π, hπ, rfl⟩
    rcases hπ with ⟨hπ_nonneg, _hπ_row, _hπ_col⟩
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (hπ_nonneg i j) (hd_nonneg i j)
  let Var : Type := (Fin n × Fin n) ⊕ Unit
  let code : Var → ℕ := fun x => ((Fintype.equivFin Var) x).val
  let σ : Finset ℕ := (Finset.univ : Finset Var).image code
  let col : Var → EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ (Fin n ⊕ Fin n)))) :=
    fun x =>
      match x with
      | Sum.inl ij =>
          augVector (α := Fin n ⊕ Fin n) (d ij.1 ij.2)
            (fun a =>
              match a with
              | Sum.inl i => if i = ij.1 then 1 else 0
              | Sum.inr j => if j = ij.2 then 1 else 0)
      | Sum.inr _ =>
          augVector (α := Fin n ⊕ Fin n) 1 (fun _ => 0)
  let b : ℕ → EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ (Fin n ⊕ Fin n)))) :=
    fun k =>
      if h : ∃ x : Var, code x = k then col (Classical.choose h) else 0
  let c : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ (Fin n ⊕ Fin n)))) :=
    augVector (α := Fin n ⊕ Fin n) R
      (fun a =>
        match a with
        | Sum.inl i => p i
        | Sum.inr j => q j)
  have hcode_inj : Function.Injective code := by
    intro x y hxy
    dsimp [code] at hxy
    exact (Fintype.equivFin Var).injective (Fin.ext hxy)
  have hb_code : ∀ x : Var, b (code x) = col x := by
    intro x
    dsimp [b]
    rw [dif_pos ⟨x, rfl⟩]
    exact congrArg col (hcode_inj (Classical.choose_spec
      (show ∃ y : Var, code y = code x from ⟨x, rfl⟩)))
  have hnot_cone :
      ¬ ∃ mu : σ → ℝ, (∀ k, 0 ≤ mu k) ∧
        c = ∑ k : σ, mu k • b k := by
    rintro ⟨mu, hmu_nonneg, hc⟩
    let weight : Var → ℝ := fun x =>
      mu ⟨code x, by
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
    haveI : Inhabited Var := ⟨Sum.inr ()⟩
    let codeEquiv : Var ≃ σ := {
      toFun x := ⟨code x, by
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
      invFun k :=
        if h : ∃ x : Var, code x = k then Classical.choose h else default
      left_inv x := by
        dsimp
        rw [dif_pos ⟨x, rfl⟩]
        exact hcode_inj (Classical.choose_spec
          (show ∃ y : Var, code y = code x from ⟨x, rfl⟩))
      right_inv k := by
        apply Subtype.ext
        dsimp
        have hk : ∃ x : Var, code x = k := by
          rcases Finset.mem_image.mp k.property with ⟨x, _hx, hxcode⟩
          exact ⟨x, hxcode⟩
        rw [dif_pos hk]
        exact Classical.choose_spec hk
    }
    have sum_over_sigma (F : Var → ℝ) :
        (∑ k : σ,
            mu k *
              (if h : ∃ x : Var, code x = k then F (Classical.choose h) else 0))
          = ∑ x : Var, weight x * F x := by
      symm
      refine Fintype.sum_equiv codeEquiv
        (fun x : Var => weight x * F x)
        (fun k : σ =>
          mu k *
            (if h : ∃ x : Var, code x = k then F (Classical.choose h) else 0)) ?_
      intro x
      dsimp [codeEquiv, weight]
      rw [dif_pos ⟨x, rfl⟩]
      have hchoose : Classical.choose
          (show ∃ y : Var, code y = code x from ⟨x, rfl⟩) = x := by
        exact hcode_inj (Classical.choose_spec
          (show ∃ y : Var, code y = code x from ⟨x, rfl⟩))
      simp [hchoose]
    let π : Matrix (Fin n) (Fin n) ℝ := fun i j => weight (Sum.inl (i, j))
    let slack : ℝ := weight (Sum.inr ())
    have hπ_nonneg : ∀ i j, 0 ≤ π i j := by
      intro i j
      exact hmu_nonneg ⟨code (Sum.inl (i, j)), by
        exact Finset.mem_image.mpr ⟨Sum.inl (i, j), Finset.mem_univ _, rfl⟩⟩
    have hslack_nonneg : 0 ≤ slack := by
      exact hmu_nonneg ⟨code (Sum.inr ()), by
        exact Finset.mem_image.mpr ⟨Sum.inr (), Finset.mem_univ _, rfl⟩⟩
    have hrow : ∀ i, ∑ j, π i j = p i := by
      intro i
      have hcoord := congrArg
        (fun z => augPlayer (α := Fin n ⊕ Fin n) z (Sum.inl i)) hc
      have hcoord' :
          p i =
            ∑ x : Var, weight x * augPlayer (α := Fin n ⊕ Fin n)
              (col x) (Sum.inl i) := by
        calc
          p i =
              augPlayer (α := Fin n ⊕ Fin n) c (Sum.inl i) := by
                simp [c]
          _ = augPlayer (α := Fin n ⊕ Fin n)
                (∑ k : σ, mu k • b k) (Sum.inl i) := by
                simpa using hcoord
          _ = ∑ k : σ,
                mu k * augPlayer (α := Fin n ⊕ Fin n) (b k) (Sum.inl i) := by
                simp
          _ = ∑ k : σ,
                mu k *
                  (if h : ∃ x : Var, code x = k then
                    augPlayer (α := Fin n ⊕ Fin n) (col (Classical.choose h))
                      (Sum.inl i)
                  else 0) := by
                apply Finset.sum_congr rfl
                intro k _hk
                by_cases h : ∃ x : Var, code x = k
                · simp [b, h]
                · simp [b, h]
          _ = ∑ x : Var, weight x * augPlayer (α := Fin n ⊕ Fin n)
                (col x) (Sum.inl i) := by
                exact sum_over_sigma (fun x =>
                  augPlayer (α := Fin n ⊕ Fin n) (col x) (Sum.inl i))
      rw [hcoord']
      rw [Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type]
      simp [col, π]
    have hcol : ∀ j, ∑ i, π i j = q j := by
      intro j
      have hcoord := congrArg
        (fun z => augPlayer (α := Fin n ⊕ Fin n) z (Sum.inr j)) hc
      have hcoord' :
          q j =
            ∑ x : Var, weight x * augPlayer (α := Fin n ⊕ Fin n)
              (col x) (Sum.inr j) := by
        calc
          q j =
              augPlayer (α := Fin n ⊕ Fin n) c (Sum.inr j) := by
                simp [c]
          _ = augPlayer (α := Fin n ⊕ Fin n)
                (∑ k : σ, mu k • b k) (Sum.inr j) := by
                simpa using hcoord
          _ = ∑ k : σ,
                mu k * augPlayer (α := Fin n ⊕ Fin n) (b k) (Sum.inr j) := by
                simp
          _ = ∑ k : σ,
                mu k *
                  (if h : ∃ x : Var, code x = k then
                    augPlayer (α := Fin n ⊕ Fin n) (col (Classical.choose h))
                      (Sum.inr j)
                  else 0) := by
                apply Finset.sum_congr rfl
                intro k _hk
                by_cases h : ∃ x : Var, code x = k
                · simp [b, h]
                · simp [b, h]
          _ = ∑ x : Var, weight x * augPlayer (α := Fin n ⊕ Fin n)
                (col x) (Sum.inr j) := by
                exact sum_over_sigma (fun x =>
                  augPlayer (α := Fin n ⊕ Fin n) (col x) (Sum.inr j))
      rw [hcoord']
      rw [Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type_right]
      simp [col, π]
    have hcost_slack : primalObj π + slack = R := by
      have hcoord := congrArg (fun z => augScalar (α := Fin n ⊕ Fin n) z) hc
      have hcoord' :
          R =
            ∑ x : Var, weight x * augScalar (α := Fin n ⊕ Fin n)
              (col x) := by
        calc
          R = augScalar (α := Fin n ⊕ Fin n) c := by
                simp [c]
          _ = augScalar (α := Fin n ⊕ Fin n)
                (∑ k : σ, mu k • b k) := by
                simpa using hcoord
          _ = ∑ k : σ,
                mu k * augScalar (α := Fin n ⊕ Fin n) (b k) := by
                simp
          _ = ∑ k : σ,
                mu k *
                  (if h : ∃ x : Var, code x = k then
                    augScalar (α := Fin n ⊕ Fin n) (col (Classical.choose h))
                  else 0) := by
                apply Finset.sum_congr rfl
                intro k _hk
                by_cases h : ∃ x : Var, code x = k
                · simp [b, h]
                · simp [b, h]
          _ = ∑ x : Var, weight x * augScalar (α := Fin n ⊕ Fin n)
                (col x) := by
                exact sum_over_sigma (fun x =>
                  augScalar (α := Fin n ⊕ Fin n) (col x))
      rw [hcoord']
      rw [Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type]
      simp [col, primalObj, π, slack]
    have hπ : π ∈ finCouplings n p q := ⟨hπ_nonneg, hrow, hcol⟩
    have hcost_mem : primalObj π ∈ Pset := ⟨π, hπ, rfl⟩
    have hinf_le_cost : sInf Pset ≤ primalObj π :=
      csInf_le hP_bddBelow hcost_mem
    linarith
  have hsep :
      ∃ z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ (Fin n ⊕ Fin n)))),
        (∀ i ∈ (∅ : Finset ℕ), inner ℝ ((fun _ => 0) i) z = 0) ∧
        (∀ i ∈ σ, inner ℝ (b i) z ≥ 0) ∧ inner ℝ c z < 0 := by
    by_contra hno
    apply hnot_cone
    rcases (Farkas (τ := (∅ : Finset ℕ)) (σ := σ)
        (a := fun _ => (0 :
          EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ (Fin n ⊕ Fin n))))))
        (b := b) (c := c)).mpr hno with ⟨lam, mu, hmu, hc⟩
    refine ⟨mu, hmu, ?_⟩
    simpa using hc
  rcases hsep with ⟨z, _hz_eq, hz_nonneg, hz_neg⟩
  let s : ℝ := augScalar (α := Fin n ⊕ Fin n) z
  let row : Fin n → ℝ := fun i => augPlayer (α := Fin n ⊕ Fin n) z (Sum.inl i)
  let column : Fin n → ℝ := fun j => augPlayer (α := Fin n ⊕ Fin n) z (Sum.inr j)
  have hs_nonneg : 0 ≤ s := by
    have h := hz_nonneg (code (Sum.inr ())) (by
      exact Finset.mem_image.mpr ⟨Sum.inr (), Finset.mem_univ _, rfl⟩)
    simpa [hb_code, s, col, inner_augVector] using h
  have hrowcol : ∀ i j, 0 ≤ d i j * s + row i + column j := by
    intro i j
    have h := hz_nonneg (code (Sum.inl (i, j))) (by
      exact Finset.mem_image.mpr ⟨Sum.inl (i, j), Finset.mem_univ _, rfl⟩)
    simpa [hb_code, row, column, s, col, inner_augVector, add_assoc] using h
  have htarget_neg :
      R * s + (∑ i, p i * row i) + (∑ j, q j * column j) < 0 := by
    simpa [c, s, row, column, inner_augVector, add_assoc] using hz_neg
  have hs_pos : 0 < s := by
    refine lt_of_le_of_ne' hs_nonneg ?_
    intro hs_zero
    have hrowcol_zero : ∀ i j, 0 ≤ row i + column j := by
      intro i j
      simpa [hs_zero, add_assoc] using hrowcol i j
    have hprod_nonneg :
        0 ≤ ∑ i, ∑ j, (p i * q j) * (row i + column j) := by
      exact Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hp i) (hq j)) (hrowcol_zero i j)
    have hprod_eq :
        ∑ i, ∑ j, (p i * q j) * (row i + column j)
          = (∑ i, p i * row i) + (∑ j, q j * column j) := by
      have hfirst :
          ∑ i, ∑ j, (p i * q j) * row i = ∑ i, p i * row i := by
        calc
          ∑ i, ∑ j, (p i * q j) * row i
              = ∑ i, (p i * row i) * ∑ j, q j := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _hj
                  ring
          _ = ∑ i, p i * row i := by
                  simp [hq_sum]
      have hsecond :
          ∑ i, ∑ j, (p i * q j) * column j = ∑ j, q j * column j := by
        calc
          ∑ i, ∑ j, (p i * q j) * column j
              = ∑ j, ∑ i, (p i * q j) * column j := by
                  rw [Finset.sum_comm]
          _ = ∑ j, (q j * column j) * ∑ i, p i := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _hi
                  ring
          _ = ∑ j, q j * column j := by
                  simp [hp_sum]
      calc
        ∑ i, ∑ j, (p i * q j) * (row i + column j)
            = ∑ i, ∑ j, (p i * q j) * row i
                + ∑ i, ∑ j, (p i * q j) * column j := by
                simp [mul_add, Finset.sum_add_distrib]
        _ = (∑ i, p i * row i) + (∑ j, q j * column j) := by
                rw [hfirst, hsecond]
    have htarget_zero :
        (∑ i, p i * row i) + (∑ j, q j * column j) < 0 := by
      simpa [hs_zero] using htarget_neg
    have hprod_nonneg' :
        0 ≤ (∑ i, p i * row i) + (∑ j, q j * column j) := by
      simpa [hprod_eq] using hprod_nonneg
    linarith
  let u : Fin n → ℝ := fun i => - row i / s
  let v : Fin n → ℝ := fun j => - column j / s
  refine ⟨u, v, ?_, ?_⟩
  · intro i j
    have h := hrowcol i j
    have hspos : 0 < s := hs_pos
    dsimp [u, v]
    have hle_div : (-row i - column j) / s ≤ d i j := by
      rw [div_le_iff₀ hspos]
      nlinarith
    calc
      -row i / s + -column j / s
          = (-row i - column j) / s := by
              field_simp [ne_of_gt hspos]
              ring
      _ ≤ d i j := hle_div
  · have htarget_div :
        R < (∑ i, (-row i / s) * p i) + (∑ j, (-column j / s) * q j) := by
      have hspos : 0 < s := hs_pos
      have hmul_rhs :
          ((∑ i, (-row i / s) * p i) + (∑ j, (-column j / s) * q j)) * s
            = -((∑ i, p i * row i) + (∑ j, q j * column j)) := by
        have hsum_row :
            (∑ i, (-row i / s) * p i) * s = -∑ i, p i * row i := by
          rw [Finset.sum_mul]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          field_simp [ne_of_gt hspos]
        have hsum_col :
            (∑ j, (-column j / s) * q j) * s = -∑ j, q j * column j := by
          rw [Finset.sum_mul]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _hj
          field_simp [ne_of_gt hspos]
        rw [add_mul, hsum_row, hsum_col]
        ring
      have hmul_lt :
          R * s <
            ((∑ i, (-row i / s) * p i) + (∑ j, (-column j / s) * q j)) * s := by
        rw [hmul_rhs]
        nlinarith
      exact lt_of_mul_lt_mul_right hmul_lt hspos.le
    simpa [u, v, mul_comm] using htarget_div

/-- **Finite-dimensional Kantorovich–Rubinstein duality** (Kantorovich 1942). For a finite metric
cost `d` between probability vectors `p, q`, the supremum of `∑ i, φ i * (p i − q i)` over
1-Lipschitz potentials `φ` equals the infimum of `∑ i j, π i j * d i j` over couplings `π`. -/
theorem fin_kr_duality (n : ℕ) (d : Matrix (Fin n) (Fin n) ℝ)
    (hd_metric : IsFiniteMetricCost n d)
    (p q : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq : ∀ j, 0 ≤ q j) (hq_sum : ∑ j, q j = 1) :
    sSup ((fun φ : Fin n → ℝ => ∑ i, φ i * (p i - q i)) '' finLipschitz n d) =
    sInf ((fun π : Matrix (Fin n) (Fin n) ℝ => ∑ i, ∑ j, π i j * d i j)
      '' finCouplings n p q) := by
  classical
  by_cases hn_zero : n = 0
  · subst n
    norm_num at hp_sum
  let dualObj : (Fin n → ℝ) → ℝ := fun φ => ∑ i, φ i * (p i - q i)
  let primalObj : Matrix (Fin n) (Fin n) ℝ → ℝ := fun π => ∑ i, ∑ j, π i j * d i j
  have hcouplings_nonempty : (finCouplings n p q).Nonempty :=
    finCouplings_nonempty n p q hp hp_sum hq hq_sum
  have hweak : ∀ φ ∈ finLipschitz n d, ∀ π ∈ finCouplings n p q,
      dualObj φ ≤ primalObj π := by
    intro φ hφ π hπ
    rcases hπ with ⟨hπ_nonneg, hπ_row, hπ_col⟩
    have hdual_expand :
        dualObj φ = ∑ i, ∑ j, π i j * (φ i - φ j) := by
      calc dualObj φ
          = ∑ i, φ i * p i - ∑ j, φ j * q j := by
              simp [dualObj, Finset.sum_sub_distrib, mul_sub]
        _ = ∑ i, φ i * (∑ j, π i j) - ∑ j, φ j * (∑ i, π i j) := by
              simp [hπ_row, hπ_col]
        _ = ∑ i, ∑ j, π i j * φ i - ∑ j, ∑ i, π i j * φ j := by
              simp [Finset.mul_sum, mul_comm]
        _ = ∑ i, ∑ j, π i j * φ i - ∑ i, ∑ j, π i j * φ j := by
              congr 1
              exact Finset.sum_comm
        _ = ∑ i, ∑ j, π i j * (φ i - φ j) := by
              simp [Finset.sum_sub_distrib, mul_sub]
    rw [hdual_expand]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hφ i j) (hπ_nonneg i j)
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_zero
  have hfin_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  have htwo_to_one :
      ∀ u v : Fin n → ℝ,
        (∀ i j, u i + v j ≤ d i j) →
        ∃ φ ∈ finLipschitz n d,
          (∑ i, u i * p i) + (∑ j, v j * q j) ≤ dualObj φ := by
    intro u v huv
    let φ : Fin n → ℝ := fun i =>
      (Finset.univ : Finset (Fin n)).inf' hfin_nonempty (fun j => d i j - v j)
    have hu_le_φ : ∀ i, u i ≤ φ i := by
      intro i
      dsimp [φ]
      refine Finset.le_inf' hfin_nonempty (fun j => d i j - v j) ?_
      intro j _hj
      linarith [huv i j]
    have hφ_le_neg_v : ∀ i, φ i ≤ -v i := by
      intro i
      have hle := Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => d i j - v j) (b := i) (Finset.mem_univ i)
      have hdii : d i i = 0 := (hd_metric.eq_zero_iff i i).mpr rfl
      dsimp [φ]
      linarith
    have hφ_lip : φ ∈ finLipschitz n d := by
      intro i k
      obtain ⟨j, _hjmem, hj_eq⟩ :=
        Finset.exists_mem_eq_inf' hfin_nonempty (fun j => d k j - v j)
      have hφi_le : φ i ≤ d i j - v j := by
        dsimp [φ]
        exact Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun j => d i j - v j) (b := j) (Finset.mem_univ j)
      have htri : d i j ≤ d i k + d k j := hd_metric.triangle i k j
      change φ k = d k j - v j at hj_eq
      linarith
    refine ⟨φ, hφ_lip, ?_⟩
    have hp_part : ∑ i, u i * p i ≤ ∑ i, φ i * p i := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hu_le_φ i) (hp i)
    have hq_part : ∑ j, v j * q j ≤ ∑ j, (-φ j) * q j := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (by linarith [hφ_le_neg_v j]) (hq j)
    have hdual_eq : dualObj φ = ∑ i, φ i * p i + ∑ j, (-φ j) * q j := by
      calc dualObj φ
          = ∑ i, (φ i * p i - φ i * q i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              simp [mul_sub]
        _ = ∑ i, φ i * p i - ∑ i, φ i * q i := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ i, φ i * p i + ∑ j, (-φ j) * q j := by
              simp [sub_eq_add_neg, neg_mul]
    linarith
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨fun _i => 0, ?_, by simp⟩
      intro i j
      simpa using hd_metric.nonneg i j
    · rintro y ⟨φ, hφ, rfl⟩
      refine le_csInf ?_ ?_
      · rcases hcouplings_nonempty with ⟨π₀, hπ₀⟩
        exact ⟨primalObj π₀, π₀, hπ₀, rfl⟩
      · rintro z ⟨π, hπ, rfl⟩
        exact hweak φ hφ π hπ
  · -- Hard direction: finite-dimensional LP strong duality.
    -- This is the separating-hyperplane/Farkas step: separate
    -- `(t, p, q)` from the epigraph of the finite transport polytope,
    -- identify the separating functional with LP dual variables, then
    -- reduce the two-potential LP dual to the metric Lipschitz potential
    -- by the c-transform.
    let Dset : Set ℝ := dualObj '' finLipschitz n d
    let Pset : Set ℝ := primalObj '' finCouplings n p q
    change sInf Pset ≤ sSup Dset
    have hD_bddAbove : BddAbove Dset := by
      rcases hcouplings_nonempty with ⟨π₀, hπ₀⟩
      refine ⟨primalObj π₀, ?_⟩
      rintro y ⟨φ, hφ, rfl⟩
      exact hweak φ hφ π₀ hπ₀
    have hstrong_two :
        ∀ R : ℝ, R < sInf Pset →
          ∃ u v : Fin n → ℝ,
            (∀ i j, u i + v j ≤ d i j) ∧
            R < (∑ i, u i * p i) + (∑ j, v j * q j) := by
      intro R hR
      exact fin_two_potential_strict_lower_bound n d hd_metric.nonneg p q
        hp hp_sum hq hq_sum R (by
          simpa [Pset, primalObj] using hR)
    have happrox : ∀ R : ℝ, R < sInf Pset → R < sSup Dset := by
      intro R hR
      obtain ⟨u, v, huv, hobj⟩ := hstrong_two R hR
      obtain ⟨φ, hφ, hφobj⟩ := htwo_to_one u v huv
      have hmem : dualObj φ ∈ Dset := ⟨φ, hφ, rfl⟩
      exact lt_of_lt_of_le (lt_of_lt_of_le hobj hφobj) (le_csSup hD_bddAbove hmem)
    by_contra hle
    have hlt : sSup Dset < sInf Pset := not_le.mp hle
    let R : ℝ := (sInf Pset + sSup Dset) / 2
    have hR_lt_inf : R < sInf Pset := by
      dsimp [R]
      linarith
    have hsup_lt_R : sSup Dset < R := by
      dsimp [R]
      linarith
    have hR_lt_sup : R < sSup Dset := happrox R hR_lt_inf
    linarith

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] [CompactSpace Ω]

omit [BorelSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- KR duality for laws supported on one finite subset of the compact metric space. -/
theorem krDist_eq_krTransportCost_of_finsupp [MeasurableSingletonClass Ω]
    {S : Finset Ω} (μ ν : ProbabilityMeasure Ω)
    (hμ_supp : μ.toMeasure (S : Set Ω) = 1)
    (hν_supp : ν.toMeasure (S : Set Ω) = 1) :
    krDist μ ν = krTransportCost μ ν := by
  classical
  refine le_antisymm (krDist_le_krTransportCost μ ν) ?_
  let n : ℕ := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let atom : Fin n → Ω := fun i => (e i : Ω)
  let p : Fin n → ℝ := fun i => μ.toMeasure.real {atom i}
  let q : Fin n → ℝ := fun i => ν.toMeasure.real {atom i}
  let d : Matrix (Fin n) (Fin n) ℝ := fun i j => dist (atom i) (atom j)
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    exact measureReal_nonneg
  have hq : ∀ i, 0 ≤ q i := by
    intro i
    exact measureReal_nonneg
  have hp_sum : ∑ i, p i = 1 := by
    have hconst :=
      integral_eq_finset_sum_of_support (Ω := Ω) (S := S) (μ := μ)
        hμ_supp (f := fun _ : Ω => (1 : ℝ)) (integrable_const 1)
    have hsumS : (∑ x ∈ S, μ.toMeasure.real {x} * (1 : ℝ)) = 1 := by
      simpa using hconst.symm
    calc
      ∑ i : Fin n, p i = ∑ x : S, μ.toMeasure.real {(x : Ω)} * (1 : ℝ) := by
        refine Fintype.sum_equiv e (fun i : Fin n => p i)
          (fun x : S => μ.toMeasure.real {(x : Ω)} * (1 : ℝ)) ?_
        intro i
        simp [p, atom]
      _ = ∑ x ∈ S, μ.toMeasure.real {x} * (1 : ℝ) := by
        simpa using
          (Finset.sum_attach S (fun x : Ω => μ.toMeasure.real {x} * (1 : ℝ)))
      _ = 1 := hsumS
  have hq_sum : ∑ i, q i = 1 := by
    have hconst :=
      integral_eq_finset_sum_of_support (Ω := Ω) (S := S) (μ := ν)
        hν_supp (f := fun _ : Ω => (1 : ℝ)) (integrable_const 1)
    have hsumS : (∑ x ∈ S, ν.toMeasure.real {x} * (1 : ℝ)) = 1 := by
      simpa using hconst.symm
    calc
      ∑ i : Fin n, q i = ∑ x : S, ν.toMeasure.real {(x : Ω)} * (1 : ℝ) := by
        refine Fintype.sum_equiv e (fun i : Fin n => q i)
          (fun x : S => ν.toMeasure.real {(x : Ω)} * (1 : ℝ)) ?_
        intro i
        simp [q, atom]
      _ = ∑ x ∈ S, ν.toMeasure.real {x} * (1 : ℝ) := by
        simpa using
          (Finset.sum_attach S (fun x : Ω => ν.toMeasure.real {x} * (1 : ℝ)))
      _ = 1 := hsumS
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hsum_zero : ∑ i : Fin n, p i = 0 := by
      haveI : IsEmpty (Fin n) := by
        rw [hn0]
        infer_instance
      exact Finset.sum_eq_zero fun i _hi => False.elim (isEmptyElim i)
    linarith
  have hfin_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  have hd_metric : IsFiniteMetricCost n d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      exact dist_nonneg
    · intro i j
      constructor
      · intro hij
        have hsep : Inseparable (atom i) (atom j) :=
          (Metric.inseparable_iff).mpr hij
        have hatom_eq : atom i = atom j := hsep.eq
        exact e.injective (Subtype.ext hatom_eq)
      · intro hij
        subst hij
        simp [d]
    · intro i j
      exact dist_comm (atom i) (atom j)
    · intro i j k
      exact dist_triangle (atom i) (atom j) (atom k)
  let dualFin : Set ℝ :=
    (fun φ : Fin n → ℝ => ∑ i, φ i * (p i - q i)) '' finLipschitz n d
  let primalFin : Set ℝ :=
    (fun π : Matrix (Fin n) (Fin n) ℝ => ∑ i, ∑ j, π i j * d i j)
      '' finCouplings n p q
  have hfinite : sSup dualFin = sInf primalFin := by
    simpa [dualFin, primalFin, p, q, d] using
      fin_kr_duality n d hd_metric p q hp hp_sum hq hq_sum
  have htransport_le_fin : krTransportCost μ ν ≤ sInf primalFin := by
    have hprimal_nonempty : primalFin.Nonempty := by
      obtain ⟨π, hπ⟩ := finCouplings_nonempty n p q hp hp_sum hq hq_sum
      exact ⟨∑ i, ∑ j, π i j * d i j, π, hπ, rfl⟩
    refine le_csInf hprimal_nonempty ?_
    rintro y ⟨π, hπ, rfl⟩
    rcases hπ with ⟨hπ_nonneg, hπ_row, hπ_col⟩
    let jointMeasure : Measure (Ω × Ω) :=
      ∑ i : Fin n, ∑ j : Fin n,
        ENNReal.ofReal (π i j) • Measure.dirac (atom i, atom j)
    have hπ_sum : ∑ i, ∑ j, π i j = 1 := by
      calc
        ∑ i, ∑ j, π i j = ∑ i, p i := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hπ_row i
        _ = 1 := hp_sum
    have hjoint_prob : IsProbabilityMeasure jointMeasure := by
      constructor
      change jointMeasure Set.univ = 1
      simp only [jointMeasure, Measure.coe_finset_sum, Finset.sum_apply,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
        Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
      calc
        ∑ i : Fin n, ∑ j : Fin n, ENNReal.ofReal (π i j)
            = ∑ i : Fin n, ENNReal.ofReal (∑ j : Fin n, π i j) := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [ENNReal.ofReal_sum_of_nonneg (fun j _hj => hπ_nonneg i j)]
        _ = ∑ i : Fin n, ENNReal.ofReal (p i) := by
              simp [hπ_row]
        _ = ENNReal.ofReal (∑ i : Fin n, p i) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun i _hi => hp i)]
        _ = 1 := by
              rw [hp_sum, ENNReal.ofReal_one]
    let piProb : ProbabilityMeasure (Ω × Ω) := ⟨jointMeasure, hjoint_prob⟩
    have hμ_atoms :
        μ.toMeasure = ∑ x ∈ S, μ.toMeasure {x} • Measure.dirac x :=
      measure_eq_finset_sum_dirac_of_support (Ω := Ω) (S := S) (μ := μ) hμ_supp
    have hν_atoms :
        ν.toMeasure = ∑ x ∈ S, ν.toMeasure {x} • Measure.dirac x :=
      measure_eq_finset_sum_dirac_of_support (Ω := Ω) (S := S) (μ := ν) hν_supp
    have hp_ofReal : ∀ i, ENNReal.ofReal (p i) = μ.toMeasure {atom i} := by
      intro i
      exact ENNReal.ofReal_toReal (measure_ne_top μ.toMeasure {atom i})
    have hq_ofReal : ∀ j, ENNReal.ofReal (q j) = ν.toMeasure {atom j} := by
      intro j
      exact ENNReal.ofReal_toReal (measure_ne_top ν.toMeasure {atom j})
    have hfst : map piProb Prod.fst measurable_fst = μ := by
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map Prod.fst piProb.toMeasure = μ.toMeasure
      dsimp [piProb]
      rw [hμ_atoms]
      calc
        Measure.map Prod.fst jointMeasure
            = ∑ i : Fin n, μ.toMeasure {atom i} • Measure.dirac (atom i) := by
              simp only [jointMeasure]
              rw [measure_map_finset_sum measurable_fst]
              refine Finset.sum_congr rfl fun i _hi => ?_
              rw [measure_map_finset_sum measurable_fst]
              simp_rw [Measure.map_smul, Measure.map_dirac' measurable_fst]
              rw [← Finset.sum_smul]
              have hinner :
                  ∑ j : Fin n, ENNReal.ofReal (π i j) = μ.toMeasure {atom i} := by
                rw [← ENNReal.ofReal_sum_of_nonneg (fun j _hj => hπ_nonneg i j),
                  hπ_row i, hp_ofReal i]
              rw [hinner]
        _ = ∑ x : S, μ.toMeasure {(x : Ω)} • Measure.dirac (x : Ω) := by
              refine Fintype.sum_equiv e
                (fun i : Fin n => μ.toMeasure {atom i} • Measure.dirac (atom i))
                (fun x : S => μ.toMeasure {(x : Ω)} • Measure.dirac (x : Ω)) ?_
              intro i
              simp [atom]
        _ = ∑ x ∈ S, μ.toMeasure {x} • Measure.dirac x := by
              simpa using
                (Finset.sum_attach S (fun x : Ω => μ.toMeasure {x} • Measure.dirac x))
    have hsnd : map piProb Prod.snd measurable_snd = ν := by
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map Prod.snd piProb.toMeasure = ν.toMeasure
      dsimp [piProb]
      rw [hν_atoms]
      calc
        Measure.map Prod.snd jointMeasure
            = ∑ j : Fin n, ν.toMeasure {atom j} • Measure.dirac (atom j) := by
              simp only [jointMeasure]
              rw [measure_map_finset_sum measurable_snd]
              simp_rw [measure_map_finset_sum measurable_snd,
                Measure.map_smul, Measure.map_dirac' measurable_snd]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _hj => ?_
              rw [← Finset.sum_smul]
              have hinner :
                  ∑ i : Fin n, ENNReal.ofReal (π i j) = ν.toMeasure {atom j} := by
                rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => hπ_nonneg i j),
                  hπ_col j, hq_ofReal j]
              rw [hinner]
        _ = ∑ x : S, ν.toMeasure {(x : Ω)} • Measure.dirac (x : Ω) := by
              refine Fintype.sum_equiv e
                (fun j : Fin n => ν.toMeasure {atom j} • Measure.dirac (atom j))
                (fun x : S => ν.toMeasure {(x : Ω)} • Measure.dirac (x : Ω)) ?_
              intro j
              simp [atom]
        _ = ∑ x ∈ S, ν.toMeasure {x} • Measure.dirac x := by
              simpa using
                (Finset.sum_attach S (fun x : Ω => ν.toMeasure {x} • Measure.dirac x))
    have hpi_coupling : piProb ∈ couplings μ ν := ⟨hfst, hsnd⟩
    have hcost :
        ∫ z, dist z.1 z.2 ∂piProb.toMeasure = ∑ i, ∑ j, π i j * d i j := by
      dsimp [piProb, jointMeasure]
      rw [integral_finset_sum_measure (fun i _hi => by
        refine integrable_finset_sum_measure.mpr fun j _hj => ?_
        exact (integrable_dirac' continuous_dist.stronglyMeasurable
          (a := (atom i, atom j)) ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun i _hi => ?_
      rw [integral_finset_sum_measure (fun j _hj =>
        (integrable_dirac' continuous_dist.stronglyMeasurable
          (a := (atom i, atom j)) ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun j _hj => ?_
      rw [integral_smul_measure, integral_dirac' _ _ continuous_dist.stronglyMeasurable,
        ENNReal.toReal_ofReal (hπ_nonneg i j), smul_eq_mul]
    let dBC : BoundedContinuousFunction (Ω × Ω) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩
    have hC_lo : ∀ z : Ω × Ω, -‖dBC‖ ≤ dist z.1 z.2 := fun z =>
      le_trans (neg_nonpos.mpr (norm_nonneg dBC)) dist_nonneg
    have hC_hi : ∀ z : Ω × Ω, dist z.1 z.2 ≤ ‖dBC‖ := fun z => by
      have h := BoundedContinuousFunction.norm_coe_le_norm dBC z
      simpa [dBC, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h
    calc
      krTransportCost μ ν
          ≤ ∫ z, dist z.1 z.2 ∂piProb.toMeasure := by
            unfold krTransportCost
            exact transportCost_le_integral_of_bdd continuous_dist.measurable μ ν
              hC_lo hC_hi hpi_coupling
      _ = ∑ i, ∑ j, π i j * d i j := hcost
  have hfin_dual_le_kr : sSup dualFin ≤ krDist μ ν := by
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨fun _ => 0, ?_, by simp⟩
      intro i j
      simp [d]
    · rintro y ⟨φ, hφ, rfl⟩
      let Φ : Ω → ℝ := fun x =>
        (Finset.univ : Finset (Fin n)).inf' hfin_nonempty
          (fun i => φ i + dist x (atom i))
      have hΦ_atom : ∀ i, Φ (atom i) = φ i := by
        intro i
        apply le_antisymm
        · have hle := Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
            (f := fun k => φ k + dist (atom i) (atom k)) (b := i) (Finset.mem_univ i)
          dsimp [Φ]
          simpa using hle
        · dsimp [Φ]
          refine Finset.le_inf' hfin_nonempty
            (fun k => φ k + dist (atom i) (atom k)) ?_
          intro k _hk
          have hik : φ i - φ k ≤ d i k := hφ i k
          dsimp [d] at hik
          linarith
      have hΦ_lip : LipschitzWith 1 Φ := by
        refine LipschitzWith.of_dist_le_mul ?_
        intro x y
        rw [Real.dist_eq, NNReal.coe_one, one_mul]
        have hxy : Φ x - Φ y ≤ dist x y := by
          obtain ⟨i, _hi, hi_eq⟩ :=
            Finset.exists_mem_eq_inf' hfin_nonempty
              (fun i => φ i + dist y (atom i))
          have hle_x := Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
            (f := fun k => φ k + dist x (atom k)) (b := i) (Finset.mem_univ i)
          have htri : dist x (atom i) ≤ dist x y + dist y (atom i) :=
            dist_triangle x y (atom i)
          change Φ y = φ i + dist y (atom i) at hi_eq
          change Φ x ≤ φ i + dist x (atom i) at hle_x
          linarith
        have hyx : Φ y - Φ x ≤ dist x y := by
          obtain ⟨i, _hi, hi_eq⟩ :=
            Finset.exists_mem_eq_inf' hfin_nonempty
              (fun i => φ i + dist x (atom i))
          have hle_y := Finset.inf'_le (s := (Finset.univ : Finset (Fin n)))
            (f := fun k => φ k + dist y (atom k)) (b := i) (Finset.mem_univ i)
          have htri : dist y (atom i) ≤ dist y x + dist x (atom i) :=
            dist_triangle y x (atom i)
          change Φ x = φ i + dist x (atom i) at hi_eq
          change Φ y ≤ φ i + dist y (atom i) at hle_y
          rw [dist_comm y x] at htri
          linarith
        exact abs_sub_le_iff.mpr ⟨hxy, hyx⟩
      have hΦ_cont : Continuous Φ := hΦ_lip.continuous
      let ΦBCF : BoundedContinuousFunction Ω ℝ :=
        BoundedContinuousFunction.mkOfCompact ⟨Φ, hΦ_cont⟩
      have hΦ_int_μ : Integrable Φ μ.toMeasure := ΦBCF.integrable μ.toMeasure
      have hΦ_int_ν : Integrable Φ ν.toMeasure := ΦBCF.integrable ν.toMeasure
      have hμ_expect : expect μ Φ = ∑ i, p i * φ i := by
        calc
          expect μ Φ = ∑ x ∈ S, μ.toMeasure.real {x} * Φ x := by
            exact integral_eq_finset_sum_of_support (Ω := Ω) (S := S) (μ := μ)
              hμ_supp hΦ_int_μ
          _ = ∑ x : S, μ.toMeasure.real {(x : Ω)} * Φ x := by
            symm
            simpa using
              (Finset.sum_attach S (fun x : Ω => μ.toMeasure.real {x} * Φ x))
          _ = ∑ i : Fin n, p i * φ i := by
            symm
            refine Fintype.sum_equiv e (fun i : Fin n => p i * φ i)
              (fun x : S => μ.toMeasure.real {(x : Ω)} * Φ x) ?_
            intro i
            simp [p, atom, hΦ_atom i]
      have hν_expect : expect ν Φ = ∑ i, q i * φ i := by
        calc
          expect ν Φ = ∑ x ∈ S, ν.toMeasure.real {x} * Φ x := by
            exact integral_eq_finset_sum_of_support (Ω := Ω) (S := S) (μ := ν)
              hν_supp hΦ_int_ν
          _ = ∑ x : S, ν.toMeasure.real {(x : Ω)} * Φ x := by
            symm
            simpa using
              (Finset.sum_attach S (fun x : Ω => ν.toMeasure.real {x} * Φ x))
          _ = ∑ i : Fin n, q i * φ i := by
            symm
            refine Fintype.sum_equiv e (fun i : Fin n => q i * φ i)
              (fun x : S => ν.toMeasure.real {(x : Ω)} * Φ x) ?_
            intro i
            simp [q, atom, hΦ_atom i]
      have hobj :
          ∑ i, φ i * (p i - q i) = expect μ Φ - expect ν Φ := by
        rw [hμ_expect, hν_expect]
        simp [Finset.sum_sub_distrib, mul_sub, mul_comm]
      change ∑ i, φ i * (p i - q i) ≤ krDist μ ν
      rw [hobj]
      exact le_csSup (bddAbove_krDist_setOf μ ν) ⟨Φ, hΦ_lip, rfl⟩
  calc
    krTransportCost μ ν ≤ sInf primalFin := htransport_le_fin
    _ = sSup dualFin := hfinite.symm
    _ ≤ krDist μ ν := hfin_dual_le_kr

end Econlib.Optimization.OptimalTransport
