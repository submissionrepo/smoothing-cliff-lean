/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Hom
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Geometry.Convex.Cone.DualFinite
public import Mathlib.RingTheory.Finiteness.Prod
public import Optlib.Convex.Farkas

/-!
# Finite Farkas cone lemma and augmented LP coordinates

This file proves an algebraic finite **Farkas lemma** for an image cone whose dual is finitely
generated, and defines coordinates for feeding a `Unit ⊕ α`-indexed augmented vector `(r, x)` into
a `Fin n` Farkas theorem. The augmented vector is realized in
`EuclideanSpace ℝ (Fin (card (Unit ⊕ α)))`, and the scalar and player projection maps `augScalar`,
`augPlayer`, together with their additivity, homogeneity and inner-product lemmas, let a caller
read off the LP coordinates of any element of that space.

## Main definitions

* `augEquiv` — the coordinate equivalence `Fin (card (Unit ⊕ α)) ≃ Unit ⊕ α`.
* `augVector` — the augmented vector `(r, x)` as an element of `EuclideanSpace ℝ _`.
* `augScalar`, `augPlayer` — the scalar and player coordinates of an augmented vector.

## Main statements

* `PointedCone.map_mem_iff_forall_dual_nonneg` — finite Farkas lemma: For a dually finitely
  generated image cone, membership in the image is equivalent to nonnegativity against every dual
  vector that is nonnegative on the source cone.
* `inner_augVector` — the inner product of an augmented vector against any `z` splits into its
  scalar and player contributions.

## Notes

The `DualFG` hypothesis is the finite/polyhedral condition that avoids the closure issue present in
the topological `ProperCone.map` API.

## Tags

farkas lemma, convex cone, linear programing, duality
-/

@[expose] public noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

section Farkas

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Finite Farkas lemma** for an image cone. If the image cone is dually finitely generated,
membership in the image is equivalent to nonnegativity against every dual vector that is
nonnegative on the source cone. -/
theorem PointedCone.map_mem_iff_forall_dual_nonneg
    (C : PointedCone ℝ E) (f : E →ₗ[ℝ] F) (b : F)
    (hdual :
      (C.map f).DualFG
        (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] F →ₗ[ℝ] ℝ)) :
    b ∈ C.map f ↔
      ∀ φ : Module.Dual ℝ F,
        (∀ x : E, x ∈ C → 0 ≤ φ (f x)) → 0 ≤ φ b := by
  constructor
  · intro hb φ hφ
    rcases hb with ⟨x, hx, rfl⟩
    exact hφ x hx
  · intro hb
    have hmem :
        b ∈ PointedCone.dual
          (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] F →ₗ[ℝ] ℝ)
          (PointedCone.dual
            (LinearMap.id : Module.Dual ℝ F →ₗ[ℝ] F →ₗ[ℝ] ℝ).flip
            (C.map f)) := by
      intro φ hφ
      exact hb φ (by
        intro x hx
        exact hφ ⟨x, hx, rfl⟩)
    rw [hdual.dual_dual_flip] at hmem
    exact hmem

end Farkas

section CoreFarkasCoordinates

variable {α : Type*} [Fintype α]

/-- The real inner product is multiplication. -/
@[simp] theorem real_inner_real (r y : ℝ) :
    inner ℝ r y = r * y :=
  mul_comm y r

/-- Coordinate equivalence used to feed a `Unit ⊕ α`-indexed augmented vector into Optlib's `Fin n`
Farkas theorem. -/
noncomputable def augEquiv :
    Fin (Fintype.card (Unit ⊕ α)) ≃ Unit ⊕ α :=
  (Fintype.equivFin (Unit ⊕ α)).symm

/-- Augmented vector `(r, x)` represented as an element of
`EuclideanSpace ℝ (Fin (card (Unit ⊕ α)))`. -/
noncomputable def augVector (r : ℝ) (x : α → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α))) :=
  WithLp.toLp 2 fun k =>
    match augEquiv (α := α) k with
    | Sum.inl _ => r
    | Sum.inr i => x i

/-- Scalar coordinate of an augmented vector. -/
noncomputable def augScalar
    (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) : ℝ :=
  z ((augEquiv (α := α)).symm (Sum.inl ()))

/-- Player coordinate of an augmented vector. -/
noncomputable def augPlayer
    (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) (i : α) : ℝ :=
  z ((augEquiv (α := α)).symm (Sum.inr i))

/-- The scalar coordinate of `augVector r x` is `r`. -/
@[simp] theorem augVector_scalar (r : ℝ) (x : α → ℝ) :
    augScalar (augVector (α := α) r x) = r := by
  simp [augScalar, augVector, augEquiv]

/-- The `i`-th player coordinate of `augVector r x` is `x i`. -/
@[simp] theorem augVector_player (r : ℝ) (x : α → ℝ) (i : α) :
    augPlayer (augVector (α := α) r x) i = x i := by
  simp [augPlayer, augVector, augEquiv]

/-- The scalar coordinate of the zero vector is zero. -/
@[simp] theorem augScalar_zero :
    augScalar (α := α) (0 : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) = 0 := by
  simp [augScalar]

/-- Every player coordinate of the zero vector is zero. -/
@[simp] theorem augPlayer_zero (i : α) :
    augPlayer (α := α) (0 : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) i = 0 := by
  simp [augPlayer]

/-- The scalar coordinate is additive. -/
@[simp] theorem augScalar_add
    (z z' : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    augScalar (α := α) (z + z') =
      augScalar (α := α) z + augScalar (α := α) z' := by
  simp [augScalar]

/-- Each player coordinate is additive. -/
@[simp] theorem augPlayer_add
    (z z' : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) (i : α) :
    augPlayer (α := α) (z + z') i =
      augPlayer (α := α) z i + augPlayer (α := α) z' i := by
  simp [augPlayer]

/-- The scalar coordinate is homogeneous. -/
@[simp] theorem augScalar_smul
    (r : ℝ) (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    augScalar (α := α) (r • z) = r * augScalar (α := α) z := by
  simp [augScalar]

/-- Each player coordinate is homogeneous. -/
@[simp] theorem augPlayer_smul
    (r : ℝ) (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) (i : α) :
    augPlayer (α := α) (r • z) i = r * augPlayer (α := α) z i := by
  simp [augPlayer]

/-- The scalar coordinate commutes with finite sums. -/
@[simp] theorem augScalar_sum {ι : Type*} (s : Finset ι)
    (z : ι → EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    augScalar (α := α) (∑ i ∈ s, z i) =
      ∑ i ∈ s, augScalar (α := α) (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

/-- Each player coordinate commutes with finite sums. -/
@[simp] theorem augPlayer_sum {ι : Type*} (s : Finset ι)
    (z : ι → EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) (i : α) :
    augPlayer (α := α) (∑ j ∈ s, z j) i =
      ∑ j ∈ s, augPlayer (α := α) (z j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

/-- The inner product of an augmented vector `(r, x)` against any `z` splits into the scalar
contribution `r * augScalar z` and the player contribution `∑ i, x i * augPlayer z i`. -/
theorem inner_augVector
    (r : ℝ) (x : α → ℝ)
    (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    inner ℝ (augVector (α := α) r x) z =
      r * augScalar z + ∑ i : α, x i * augPlayer z i := by
  rw [PiLp.inner_apply]
  let e : Fin (Fintype.card (Unit ⊕ α)) ≃ Unit ⊕ α := augEquiv (α := α)
  calc
    ∑ k : Fin (Fintype.card (Unit ⊕ α)),
        inner ℝ ((augVector (α := α) r x).ofLp k) (z.ofLp k)
        =
      ∑ q : Unit ⊕ α,
        inner ℝ ((augVector (α := α) r x).ofLp (e.symm q)) (z.ofLp (e.symm q)) := by
        refine Fintype.sum_equiv e
          (fun k => inner ℝ ((augVector (α := α) r x).ofLp k) (z.ofLp k))
          (fun q => inner ℝ ((augVector (α := α) r x).ofLp (e.symm q))
            (z.ofLp (e.symm q))) ?_
        intro k
        simp
    _ = r * augScalar z + ∑ i : α, x i * augPlayer z i := by
        simp only [augEquiv, Equiv.symm_symm, augVector, Equiv.symm_apply_apply,
          real_inner_real, Fintype.sum_sum_type, Finset.univ_unique, PUnit.default_eq_unit,
          Finset.sum_singleton, augScalar, augPlayer, e]

end CoreFarkasCoordinates
