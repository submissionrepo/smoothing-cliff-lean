/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Danskin
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Intrinsic
public import Optlib.Convex.Subgradient

open Set InnerProductSpace

/-!
# Faces of a convex function

Face geometry associated to a function `f : E → ℝ` on a finite-dimensional real inner product
space, following Caravenna–Daneri (2010). A *projected face* `F_y` is the gradient level set
`{x ∈ dom ∇f | ∇f x = y}`; a *subgradient face* `P(x)` is the set of points where the supporting
affine functional through `x` agrees with `f`. At a differentiability point the two decompositions
coincide.

## Main definitions

* `domGrad f` — the set of differentiability points of `f`.
* `tangentHyperplane f x y` — the affine hyperplane `{(z, w) | w = f x + ⟪y, z - x⟫}` in `E × ℝ`.
* `projectedFace f y` — the gradient level set `{x ∈ domGrad f | ∇f x = y}`.
* `subgradientFace f x` — the points `z` with `f z - f x = ⟪y, z - x⟫` for some `y ∈ ∂f x`.
* `subgradientFace_dom f x` — the restriction `subgradientFace f x ∩ domGrad f`.
* `faceDim f y`, `relIntFace f y`, `kFacePoints f k` — the affine dimension of a projected face,
  the relative interior of a projected face, and the union of relative interiors of dimension `k`.

## Main statements

* `subgradientFace_dom_eq_projectedFace` — at a differentiability point of a convex `f`, the
  restricted subgradient face equals the projected face at `∇f x`.
* `relIntFace_disjoint_of_ne`, `kFacePoints_disjoint_of_ne` — the relative-interior faces, and the
  `k`-face sets, are pairwise disjoint.
* `measurableSet_domGrad`, `measurable_gradient` — measurability of `dom ∇f` and of `∇f`.

## References

* Caravenna, L., and S. Daneri. 2010. “The Disintegration of the Lebesgue Measure on the Faces of a
  Convex Function.” *Journal of Functional Analysis* 258 (11): 3604–61.
  [https://doi.org/10.1016/j.jfa.2010.01.024](https://doi.org/10.1016/j.jfa.2010.01.024).

## Tags

convex function, face, subgradient, gradient, tangent hyperplane, relative interior
-/

@[expose] public section

/-! ### §1  Differentiability domain -/

/-- The set of differentiability points of `f`.  In the paper (Caravenna–Daneri 2010, line 432)
this is `dom ∇f`. -/
def domGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) : Set E :=
  {x | DifferentiableAt ℝ f x}

@[simp] lemma mem_domGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x : E} : x ∈ domGrad f ↔ DifferentiableAt ℝ f x :=
  Iff.rfl

/-- `dom ∇f` is a Borel measurable set. -/
lemma measurableSet_domGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) : MeasurableSet (domGrad f) :=
  measurableSet_of_differentiableAt ℝ f

/-- The gradient `∇f : E → E`, defined (by Mathlib's convention) as zero outside `dom ∇f`, is Borel
measurable. -/
lemma measurable_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) : Measurable (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.measurable.comp
    (measurable_fderiv ℝ f)

/-! ### §2  Tangent hyperplane -/

/-- The *tangent hyperplane* to the graph of `f` at `(x, f x)` with slope `y`, i.e. the affine
hyperplane in `E × ℝ` given by `{(z, w) | w = f x + ⟪y, z - x⟫}`. This is Definition 3.1 of
Caravenna–Daneri 2010. -/
def tangentHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x y : E) : Set (E × ℝ) :=
  {p : E × ℝ | p.2 = f x + @inner ℝ E _ y (p.1 - x)}

@[simp] lemma mem_tangentHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x y : E} {p : E × ℝ} :
    p ∈ tangentHyperplane f x y ↔ p.2 = f x + @inner ℝ E _ y (p.1 - x) :=
  Iff.rfl

/-! ### §3  Projected face and subgradient face -/

/-- The *projected face* `F_y := ∇f⁻¹(y) ∩ dom ∇f` (Caravenna–Daneri 2010, line 484, Definition
3.2).  This is the gradient level set, the set of differentiability points at which the gradient
equals `y`. -/
def projectedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (f : E → ℝ) (y : E) : Set E :=
  {x | x ∈ domGrad f ∧ gradient f x = y}

@[simp] lemma mem_projectedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {y x : E} :
    x ∈ projectedFace f y ↔ DifferentiableAt ℝ f x ∧ gradient f x = y :=
  Iff.rfl

/-- The *subgradient face* `P(x)` at `x` (Caravenna–Daneri 2010, eq. 4.10): The set of points `z`
such that `f z - f x = ⟪y, z - x⟫` for some `y ∈ ∂f(x)` (the subdifferential of `f` at `x` over
`Set.univ`).

This is the projection onto `E` of the intersection of the graph of `f` with the union of
supporting hyperplanes over all subgradients at `x`. -/
def subgradientFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : Set E :=
  {z : E | ∃ y ∈ SubderivWithinAt f Set.univ x,
    f z - f x = @inner ℝ E _ y (z - x)}

@[simp] lemma mem_subgradientFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x z : E} :
    z ∈ subgradientFace f x ↔
      ∃ y ∈ SubderivWithinAt f Set.univ x,
        f z - f x = @inner ℝ E _ y (z - x) :=
  Iff.rfl

/-- The *restricted subgradient face* `R(x) := P(x) ∩ dom ∇f` (line just after eq. 4.10 of
Caravenna–Daneri 2010).  When `x ∈ dom ∇f` this coincides with the projected face `F_{∇f x}` (see
`subgradientFace_dom_eq_projectedFace`). -/
def subgradientFace_dom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : Set E :=
  subgradientFace f x ∩ domGrad f

@[simp] lemma mem_subgradientFace_dom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {x z : E} :
    z ∈ subgradientFace_dom f x ↔
      z ∈ subgradientFace f x ∧ DifferentiableAt ℝ f z :=
  Iff.rfl

/-! ### §4  Relative interior faces, k-face sets, face dimension -/

section RelativeInteriors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The (affine) dimension of the projected face `F_y`, defined as the `ℝ`-rank of the direction
subspace of the affine span of `projectedFace f y`.  This is the `k` of the paper's `F_y^k`
(Caravenna–Daneri 2010 §3.2). -/
noncomputable def faceDim (f : E → ℝ) (y : E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (projectedFace f y)).direction

/-- The relative interior of the projected face `F_y` (the paper's `E_y`, line 484). This is the
intrinsic interior of `projectedFace f y` in the topology of its affine hull. -/
noncomputable def relIntFace (f : E → ℝ) (y : E) : Set E :=
  intrinsicInterior ℝ (projectedFace f y)

/-- The set `E^k` of points lying in the relative interior of some projected face of affine
dimension exactly `k`. -/
noncomputable def kFacePoints (f : E → ℝ) (k : ℕ) : Set E :=
  ⋃ (y : E) (_ : faceDim f y = k), relIntFace f y

omit [FiniteDimensional ℝ E] in
@[simp] lemma mem_kFacePoints {f : E → ℝ} {k : ℕ} {x : E} :
    x ∈ kFacePoints f k ↔ ∃ y, faceDim f y = k ∧ x ∈ relIntFace f y := by
  simp [kFacePoints]

end RelativeInteriors

/-! ### §5  Basic inclusions -/

section BasicInclusions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
lemma relIntFace_subset_projectedFace (f : E → ℝ) (y : E) :
    relIntFace f y ⊆ projectedFace f y :=
  intrinsicInterior_subset

omit [FiniteDimensional ℝ E] in
lemma projectedFace_subset_domGrad (f : E → ℝ) (y : E) :
    projectedFace f y ⊆ domGrad f :=
  fun _ hx => hx.1

omit [FiniteDimensional ℝ E] in
lemma relIntFace_subset_domGrad (f : E → ℝ) (y : E) :
    relIntFace f y ⊆ domGrad f :=
  (relIntFace_subset_projectedFace f y).trans (projectedFace_subset_domGrad f y)

omit [FiniteDimensional ℝ E] in
lemma kFacePoints_subset_domGrad (f : E → ℝ) (k : ℕ) :
    kFacePoints f k ⊆ domGrad f := by
  intro x hx
  rw [mem_kFacePoints] at hx
  obtain ⟨y, _, hxy⟩ := hx
  exact relIntFace_subset_domGrad f y hxy

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma subgradientFace_dom_subset_domGrad (f : E → ℝ) (x : E) :
    subgradientFace_dom f x ⊆ domGrad f :=
  fun _ h => h.2

end BasicInclusions

/-! ### §6  Gradient identification on projected faces -/

section GradientOnFaces

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- Every point of `projectedFace f y` has gradient equal to `y`. -/
lemma gradient_eq_of_mem_projectedFace {f : E → ℝ} {y x : E}
    (hx : x ∈ projectedFace f y) : gradient f x = y :=
  hx.2

omit [FiniteDimensional ℝ E] in
/-- Every point of `relIntFace f y` has gradient equal to `y`. -/
lemma gradient_eq_of_mem_relIntFace {f : E → ℝ} {y x : E}
    (hx : x ∈ relIntFace f y) : gradient f x = y :=
  gradient_eq_of_mem_projectedFace (relIntFace_subset_projectedFace f y hx)

omit [FiniteDimensional ℝ E] in
/-- The relative-interior projected faces for different gradients `y` and `y'` are disjoint. -/
lemma relIntFace_disjoint_of_ne {f : E → ℝ} {y y' : E} (hyy' : y ≠ y') :
    Disjoint (relIntFace f y) (relIntFace f y') := by
  rw [Set.disjoint_iff_forall_ne]
  rintro x hx z hz rfl
  have h1 : gradient f x = y  := gradient_eq_of_mem_relIntFace hx
  have h2 : gradient f x = y' := gradient_eq_of_mem_relIntFace hz
  exact hyy' (h1.symm.trans h2)

omit [FiniteDimensional ℝ E] in
/-- The sets `kFacePoints f k` are pairwise disjoint over distinct `k`. -/
lemma kFacePoints_disjoint_of_ne (f : E → ℝ) {k k' : ℕ} (hkk' : k ≠ k') :
    Disjoint (kFacePoints f k) (kFacePoints f k') := by
  rw [Set.disjoint_iff_forall_ne]
  intro x hx z hz hxz
  rw [mem_kFacePoints] at hx hz
  obtain ⟨y,  hyk,  hxy⟩ := hx
  obtain ⟨y', hy'k', hzy'⟩ := hz
  subst hxz
  by_cases h : y = y'
  · subst h; exact hkk' (hyk.symm.trans hy'k')
  · exact h ((gradient_eq_of_mem_relIntFace hxy).symm.trans
              (gradient_eq_of_mem_relIntFace hzy'))

end GradientOnFaces

/-! ### §7  Bridge: Projected face ↔ subgradient face at differentiability points -/

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- For convex `f` and a differentiability point `x`, every point of `projectedFace f (∇f x)` lies
in `subgradientFace_dom f x`.

This is the easy direction of Caravenna–Daneri 2010 (line just after eq. 4.10): Along a projected
face, the supporting affine functional `z ↦ f x + ⟪∇f x, z − x⟫` agrees with `f`. -/
lemma projectedFace_subset_subgradientFace_dom
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x : E} (hx : DifferentiableAt ℝ f x) :
    projectedFace f (gradient f x) ⊆ subgradientFace_dom f x := by
  intro z hz
  have hz_dom  : DifferentiableAt ℝ f z := hz.1
  have hz_grad : gradient f z = gradient f x := hz.2
  -- ∇f x ∈ ∂f(x) (subdifferential over Set.univ).
  have h_sub_x : gradient f x ∈ SubderivWithinAt f Set.univ x :=
    gradient_mem_SubderivWithinAt f hf hx
  -- ∇f z = ∇f x ∈ ∂f(z).
  have h_sub_z : gradient f x ∈ SubderivWithinAt f Set.univ z := by
    have := gradient_mem_SubderivWithinAt f hf hz_dom
    rwa [hz_grad] at this
  -- From ∂f(x): f x + ⟪∇f x, z - x⟫ ≤ f z.
  have h1 : f x + @inner ℝ E _ (gradient f x) (z - x) ≤ f z :=
    h_sub_x z (Set.mem_univ _)
  -- From ∂f(z): f z + ⟪∇f x, x - z⟫ ≤ f x.
  have h2 : f z + @inner ℝ E _ (gradient f x) (x - z) ≤ f x :=
    h_sub_z x (Set.mem_univ _)
  -- ⟪∇f x, x - z⟫ = -⟪∇f x, z - x⟫, so the two subgradient inequalities force the gap exactly.
  have h_inner : @inner ℝ E _ (gradient f x) (x - z) =
      -@inner ℝ E _ (gradient f x) (z - x) := by
    rw [show (x - z : E) = -(z - x) from (neg_sub z x).symm, inner_neg_right]
  -- Combine to get f z - f x = ⟪∇f x, z - x⟫.
  have h_eq : f z - f x = @inner ℝ E _ (gradient f x) (z - x) := by linarith [h_inner ▸ h2]
  exact ⟨⟨gradient f x, h_sub_x, h_eq⟩, hz_dom⟩

omit [FiniteDimensional ℝ E] in
/-- For convex `f` and a differentiability point `x`, every point of `subgradientFace_dom f x` lies
in `projectedFace f (∇f x)`.

This is the reverse direction: The §4 multivalued `R(x)` lands inside the §3 partition class
`F_{∇f x}`. -/
lemma subgradientFace_dom_subset_projectedFace
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x : E} (hx : DifferentiableAt ℝ f x) :
    subgradientFace_dom f x ⊆ projectedFace f (gradient f x) := by
  intro z hz
  obtain ⟨⟨y', hy'_sub, hy'_eq⟩, hz_dom⟩ := hz
  -- Since x is a differentiability point, ∂f(x) = {∇f x}.
  have hy'_eq_grad : y' = gradient f x :=
    SubderivWithinAt.subset_singleton_of_differentiableAt f hx hy'_sub
  subst hy'_eq_grad
  -- So f z - f x = ⟪∇f x, z - x⟫.
  -- Claim: ∇f x ∈ ∂f(z), so by singleton property, ∇f x = ∇f z.
  have h_sub_x : gradient f x ∈ SubderivWithinAt f Set.univ x :=
    gradient_mem_SubderivWithinAt f hf hx
  have h_sub_z : gradient f x ∈ SubderivWithinAt f Set.univ z := by
    intro w _
    have h_w : f x + @inner ℝ E _ (gradient f x) (w - x) ≤ f w :=
      h_sub_x w (Set.mem_univ _)
    -- f z = f x + ⟪∇f x, z - x⟫
    have hz_val : f z = f x + @inner ℝ E _ (gradient f x) (z - x) := by linarith
    -- ⟪∇f x, w - x⟫ = ⟪∇f x, z - x⟫ + ⟪∇f x, w - z⟫
    have h_split : @inner ℝ E _ (gradient f x) (w - x) =
        @inner ℝ E _ (gradient f x) (z - x) +
        @inner ℝ E _ (gradient f x) (w - z) := by
      rw [← inner_add_right]
      congr 1; abel
    linarith [h_w, hz_val, h_split]
  -- ∇f x ∈ ∂f(z) = {∇f z}, so ∇f x = ∇f z.
  have h_mem : (gradient f x : E) ∈ ({gradient f z} : Set E) :=
    SubderivWithinAt.subset_singleton_of_differentiableAt f hz_dom h_sub_z
  rw [Set.mem_singleton_iff] at h_mem
  exact ⟨hz_dom, h_mem.symm⟩

omit [FiniteDimensional ℝ E] in
/-- For convex `f` and a differentiability point `x`, the subgradient face domain and the projected
face at `∇f x` coincide (Caravenna–Daneri 2010, line just after eq. 4.10). -/
lemma subgradientFace_dom_eq_projectedFace
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x : E} (hx : DifferentiableAt ℝ f x) :
    subgradientFace_dom f x = projectedFace f (gradient f x) :=
  Set.Subset.antisymm
    (subgradientFace_dom_subset_projectedFace hf hx)
    (projectedFace_subset_subgradientFace_dom hf hx)

end Bridge

/-! ### §8  Face dimension of singleton faces -/

section SingletonFaces

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- When `projectedFace f y` is a singleton, its affine dimension is zero. -/
lemma faceDim_eq_zero_of_singleton {f : E → ℝ} {y x : E}
    (h : projectedFace f y = {x}) : faceDim f y = 0 := by
  unfold faceDim
  rw [h, direction_affineSpan, vectorSpan_singleton]
  simp

end SingletonFaces
