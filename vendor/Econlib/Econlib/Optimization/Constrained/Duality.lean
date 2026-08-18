/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Constrained.Problem
public import Econlib.Optimization.Constrained.Slater
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Strong duality for scalar-constrained convex programs

For a compact convex feasible set `X` in a real topological module, a concave continuous objective
`f`, and a convex continuous inequality constraint `g x ≤ 0`, Slater's condition (a strictly
feasible point) implies zero duality gap: `primalValue = dualValue`. The dual infimum is moreover
attained at an optimal multiplier.

## Main definitions

* `scalarFeasible`: Feasible set `{x ∈ X | g x ≤ 0}`.
* `lagrangianScalar`: Scalar Lagrangian `f x - λ · g x`.
* `primalValueScalar`: Supremum of `f` over the feasible set.
* `dualObjectiveScalar`: Supremum of the Lagrangian over `X` at a fixed multiplier.
* `dualValueScalar`: Infimum of the dual objective over nonneg multipliers.
* `achievableSet`: Achievable hypograph `{(u, v) | ∃ x ∈ X, g x ≤ u ∧ v ≤ f x}`.
* `toUnitConstrainedProblem`: Bridge embedding scalar data into `ConstrainedProblem`.

## Main statements

* `primalValueScalar_le_dualValueScalar`: Weak duality.
* `strongDuality_scalar_of_isSlater`: Strong duality under Slater's condition.
* `dualAttainment_scalar_of_isSlater`: The dual infimum is attained at an optimal multiplier under
  Slater's condition.
* `strongDuality_scalar_of_parametricSlater`: Strong duality under parametric Slater.

## References

* Slater, Morton. 1950. “Lagrange Multipliers Revisited.” *Cowles Commission Discussion Paper:
  Mathematics* 403.
* Boyd, Stephen P. 2006. *Convex Optimization*. Cambridge University Press. Chapter 5.

## Tags

convex optimization, duality, lagrangian, slater condition, hahn-banach
-/

@[expose] public section

open Pointwise Set

namespace Econlib.Optimization

section ScalarDuality

variable {E : Type*} [TopologicalSpace E]

/-- Feasible set of a scalar-constrained program: `x ∈ X` with `g x ≤ 0`. -/
def scalarFeasible (X : Set E) (g : E → ℝ) : Set E :=
  {x ∈ X | g x ≤ 0}

/-- Scalar Lagrangian `f x - λ · g x`. -/
noncomputable def lagrangianScalar (f g : E → ℝ) (x : E) (lam : ℝ) : ℝ :=
  f x - lam * g x

/-- Primal value (scalar constraint): Supremum of `f` over feasible points. -/
noncomputable def primalValueScalar (X : Set E) (f g : E → ℝ) : ℝ :=
  sSup (f '' scalarFeasible X g)

/-- Dual objective at multiplier `lam`: Supremum of the Lagrangian over `X`. -/
noncomputable def dualObjectiveScalar (X : Set E) (f g : E → ℝ) (lam : ℝ) : ℝ :=
  sSup ((fun x => lagrangianScalar f g x lam) '' X)

/-- Dual value: Infimum of dual objective over nonnegative multipliers. -/
noncomputable def dualValueScalar (X : Set E) (f g : E → ℝ) : ℝ :=
  sInf (dualObjectiveScalar X f g '' Ici 0)

/-- For `lam ≥ 0`, the Lagrangian image `{f x - lam * g x | x ∈ X}` is bounded above (image of a
compact set under a continuous function). -/
private lemma lagrangianScalar_image_bddAbove
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    (lam : ℝ) :
    BddAbove ((fun x => lagrangianScalar f g x lam) '' X) := by
  have hcont : ContinuousOn (fun x => lagrangianScalar f g x lam) X := by
    unfold lagrangianScalar
    exact hf_cont.sub ((continuousOn_const (c := lam)).mul hg_cont)
  exact (hcompact.image_of_continuousOn hcont).bddAbove

/-- For any feasible `x` and `lam ≥ 0`, `f x ≤ dualObjectiveScalar X f g lam`. -/
private lemma scalarFeasible_le_dualObjectiveScalar
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    {lam : ℝ} (hlam : 0 ≤ lam)
    {x : E} (hx : x ∈ scalarFeasible X g) :
    f x ≤ dualObjectiveScalar X f g lam := by
  obtain ⟨hxX, hgx⟩ := hx
  have hfx_le : f x ≤ lagrangianScalar f g x lam := by
    unfold lagrangianScalar
    have : lam * g x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam hgx
    linarith
  have hmem : lagrangianScalar f g x lam ∈ (fun x => lagrangianScalar f g x lam) '' X :=
    ⟨x, hxX, rfl⟩
  have hbdd := lagrangianScalar_image_bddAbove hcompact hf_cont hg_cont lam
  exact hfx_le.trans (le_csSup hbdd hmem)

/-- Weak duality: `primalValueScalar ≤ dualValueScalar`. Holds for any compact-continuous primal
with nonempty feasible set. -/
theorem primalValueScalar_le_dualValueScalar
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    (hfeas_ne : (scalarFeasible X g).Nonempty) :
    primalValueScalar X f g ≤ dualValueScalar X f g := by
  have hfeas_img_ne : (f '' scalarFeasible X g).Nonempty := hfeas_ne.image f
  have hdual_img_ne : (dualObjectiveScalar X f g '' Ici 0).Nonempty :=
    ⟨dualObjectiveScalar X f g 0, 0, self_mem_Ici, rfl⟩
  refine le_csInf hdual_img_ne ?_
  rintro y ⟨lam, hlam, rfl⟩
  refine csSup_le hfeas_img_ne ?_
  rintro v ⟨x, hx, rfl⟩
  exact scalarFeasible_le_dualObjectiveScalar hcompact hf_cont hg_cont hlam hx

/-! ### Membership-level bounds for the dual side

`dualObjectiveScalar` is a `sSup` and `dualValueScalar` is a `sInf`; these wrap the standard
`le_csSup` / `csSup_le` / `csInf_le` / `le_csInf` ceremony (with the requisite boundedness side
conditions) so consumers touching the dual side need not rediscover it. -/

omit [TopologicalSpace E] in
/-- A point `x ∈ X` lower-bounds the dual objective: `f x - λ·g x ≤ φ(λ)`. -/
lemma le_dualObjectiveScalar {X : Set E} {f g : E → ℝ} {lam : ℝ}
    (hbdd : BddAbove ((fun x => lagrangianScalar f g x lam) '' X))
    {x : E} (hx : x ∈ X) :
    lagrangianScalar f g x lam ≤ dualObjectiveScalar X f g lam :=
  le_csSup hbdd ⟨x, hx, rfl⟩

omit [TopologicalSpace E] in
/-- A uniform Lagrangian bound upper-bounds the dual objective: If `f x - λ·g x ≤ b` for all
`x ∈ X` (and `X` is nonempty), then `φ(λ) ≤ b`. -/
lemma dualObjectiveScalar_le {X : Set E} {f g : E → ℝ} {lam b : ℝ}
    (hX_ne : X.Nonempty)
    (hbound : ∀ x ∈ X, lagrangianScalar f g x lam ≤ b) :
    dualObjectiveScalar X f g lam ≤ b :=
  csSup_le (hX_ne.image _) (by rintro v ⟨x, hx, rfl⟩; exact hbound x hx)

omit [TopologicalSpace E] in
/-- Membership lower bound for the dual value: For `λ ≥ 0`, `dualValue ≤ φ(λ)`. Needs the dual
objective image to be bounded below (the existence of a uniform Lagrangian lower bound). -/
lemma dualValueScalar_le {X : Set E} {f g : E → ℝ}
    (hbdd : BddBelow (dualObjectiveScalar X f g '' Ici 0))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    dualValueScalar X f g ≤ dualObjectiveScalar X f g lam :=
  csInf_le hbdd ⟨lam, hlam, rfl⟩

omit [TopologicalSpace E] in
/-- Lower-bound form for the dual value: If `b ≤ φ(λ)` for every `λ ≥ 0`, then `b ≤ dualValue`. -/
lemma le_dualValueScalar {X : Set E} {f g : E → ℝ} {b : ℝ}
    (hbound : ∀ lam, 0 ≤ lam → b ≤ dualObjectiveScalar X f g lam) :
    b ≤ dualValueScalar X f g :=
  le_csInf ⟨dualObjectiveScalar X f g 0, 0, self_mem_Ici, rfl⟩
    (by rintro w ⟨lam, hlam, rfl⟩; exact hbound lam hlam)

omit [TopologicalSpace E] in
/-- If `v` is the least element of the dual-objective image over `Ici 0`, the dual value equals `v`
(and is attained). -/
lemma dualValueScalar_eq_of_isLeast {X : Set E} {f g : E → ℝ} {v : ℝ}
    (hv : IsLeast (dualObjectiveScalar X f g '' Ici 0) v) :
    dualValueScalar X f g = v :=
  hv.csInf_eq

/-- The achievable hypograph: All pairs `(u, v) ∈ ℝ²` for which some `x ∈ X` has `g x ≤ u` and
`f x ≥ v`. Convex and closed (when `X` is compact and `f, g` are continuous), and the point
`(0, primalValueScalar + ε)` lies outside it. -/
def achievableSet (X : Set E) (f g : E → ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x ∈ X, g x ≤ p.1 ∧ p.2 ≤ f x}

omit [TopologicalSpace E] in
/-- The achievable set is convex when `X` is convex, and `f` and `g` are convex on `X`. -/
private lemma achievableSet_convex [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f g : E → ℝ}
    (hX_convex : Convex ℝ X)
    (hf_concave : ConcaveOn ℝ X f)
    (hg_convex : ConvexOn ℝ X g) :
    Convex ℝ (achievableSet X f g) := by
  rintro ⟨u₁, v₁⟩ ⟨x₁, hx₁X, hgu₁, hvf₁⟩ ⟨u₂, v₂⟩ ⟨x₂, hx₂X, hgu₂, hvf₂⟩
  intro a b ha hb hab
  simp only at hgu₁ hvf₁ hgu₂ hvf₂
  refine ⟨a • x₁ + b • x₂, hX_convex hx₁X hx₂X ha hb hab, ?_, ?_⟩
  · have hconv := hg_convex.2 hx₁X hx₂X ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have ha1 : a • g x₁ ≤ a * u₁ := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left hgu₁ ha
    have hb1 : b • g x₂ ≤ b * u₂ := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left hgu₂ hb
    linarith
  · have hconv := hf_concave.2 hx₁X hx₂X ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have ha1 : a * v₁ ≤ a • f x₁ := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left hvf₁ ha
    have hb1 : b * v₂ ≤ b • f x₂ := by
      rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left hvf₂ hb
    linarith

omit [TopologicalSpace E] in
/-- Alternative representation of the achievable set as a Minkowski sum of the `(g, f)`-image of
`X` with the closed convex cone `Ici 0 × Iic 0`. -/
private lemma achievableSet_eq_image_add
    (X : Set E) (f g : E → ℝ) :
    achievableSet X f g =
      (fun x => (g x, f x)) '' X + (Ici (0 : ℝ)) ×ˢ (Iic (0 : ℝ)) := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨x, hxX, hgu, hvf⟩
    refine ⟨(g x, f x), ⟨x, hxX, rfl⟩, (u - g x, v - f x), ?_, ?_⟩
    · exact ⟨sub_nonneg.mpr hgu, sub_nonpos.mpr hvf⟩
    · simp [add_sub_cancel]
  · rintro ⟨⟨u₀, v₀⟩, ⟨x, hxX, hxeq⟩, ⟨a, b⟩, hab_mem, hsum⟩
    obtain ⟨ha, hb⟩ := hab_mem
    simp only at ha hb
    rw [Prod.mk.injEq] at hxeq
    obtain ⟨hgx, hfx⟩ := hxeq
    have hu : u₀ + a = u := (Prod.mk.injEq _ _ _ _).mp hsum |>.1
    have hv : v₀ + b = v := (Prod.mk.injEq _ _ _ _).mp hsum |>.2
    refine ⟨x, hxX, ?_, ?_⟩
    · rw [← hu, ← hgx]; linarith [mem_Ici.mp ha]
    · rw [← hv, ← hfx]; linarith [mem_Iic.mp hb]

/-- The achievable set is closed when `X` is compact and `f, g` are continuous on `X`. -/
private lemma achievableSet_isClosed
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X) :
    IsClosed (achievableSet X f g) := by
  rw [achievableSet_eq_image_add]
  have himg_compact : IsCompact ((fun x => (g x, f x)) '' X) :=
    hcompact.image_of_continuousOn (hg_cont.prodMk hf_cont)
  have hcone_closed : IsClosed ((Ici (0 : ℝ)) ×ˢ (Iic (0 : ℝ))) :=
    isClosed_Ici.prod isClosed_Iic
  exact hcone_closed.add_left_of_isCompact himg_compact

omit [TopologicalSpace E] in
/-- `(g x, f x) ∈ achievableSet X f g` for every `x ∈ X`. -/
private lemma image_mem_achievableSet
    {X : Set E} {f g : E → ℝ} {x : E} (hx : x ∈ X) :
    (g x, f x) ∈ achievableSet X f g :=
  ⟨x, hx, le_rfl, le_rfl⟩

omit [TopologicalSpace E] in
/-- If `x ∈ scalarFeasible X g`, then `(0, f x) ∈ achievableSet X f g`. -/
private lemma feasible_image_mem_achievableSet
    {X : Set E} {f g : E → ℝ} {x : E} (hx : x ∈ scalarFeasible X g) :
    ((0 : ℝ), f x) ∈ achievableSet X f g :=
  ⟨x, hx.1, hx.2, le_rfl⟩

/-- The exclusion property: `(0, primalValueScalar X f g + ε) ∉ achievableSet X f g` for every
`ε > 0`, when the feasible set is nonempty and bounded above on `X`. -/
private lemma not_mem_achievableSet_of_gt_primalValue
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    -- kept to match the docstring's stated nonempty-feasible-set contract; the proof
    -- below derives feasibility of the witness point directly from membership in `A`
    (_hfeas_ne : (scalarFeasible X g).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (0, primalValueScalar X f g + ε) ∉ achievableSet X f g := by
  rintro ⟨x, hxX, hgx, hVε_le_fx⟩
  have hx_feas : x ∈ scalarFeasible X g := ⟨hxX, hgx⟩
  have hmem : f x ∈ f '' scalarFeasible X g := ⟨x, hx_feas, rfl⟩
  have hsub : f '' scalarFeasible X g ⊆ f '' X := Set.image_mono (fun _ h => h.1)
  have hbdd_X : BddAbove (f '' X) := (hcompact.image_of_continuousOn hf_cont).bddAbove
  have hbdd : BddAbove (f '' scalarFeasible X g) := hbdd_X.mono hsub
  have hle : f x ≤ primalValueScalar X f g := le_csSup hbdd hmem
  linarith

/-- For any continuous linear functional `L : ℝ × ℝ →L[ℝ] ℝ`, we have the pointwise decomposition
`L (u, v) = u * L (1, 0) + v * L (0, 1)`. -/
private lemma prod_apply_eq (L : (ℝ × ℝ) →L[ℝ] ℝ) (u v : ℝ) :
    L (u, v) = u * L (1, 0) + v * L (0, 1) := by
  have h1 : (u, v) = u • ((1, 0) : ℝ × ℝ) + v • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [h1, L.map_add, L.map_smul, L.map_smul]
  simp [smul_eq_mul]

omit [TopologicalSpace E] in
/-- Comprehensiveness of the achievable set: If `(u, v) ∈ A` and `u' ≥ u`, `v' ≤ v`, then
`(u', v') ∈ A`. -/
private lemma achievableSet_comprehensive
    {X : Set E} {f g : E → ℝ} {u u' v v' : ℝ}
    (hp : (u, v) ∈ achievableSet X f g) (hu : u ≤ u') (hv : v' ≤ v) :
    (u', v') ∈ achievableSet X f g := by
  obtain ⟨x, hxX, hgu, hvf⟩ := hp
  exact ⟨x, hxX, hgu.trans hu, hv.trans hvf⟩

/-- **Strong duality** under `IsSlater` (Slater 1950; Boyd and Vandenberghe 2004): For a compact
convex feasible set, concave continuous objective, and convex continuous constraint satisfying
Slater's strict-feasibility condition, the primal and dual values agree. -/
theorem strongDuality_scalar_of_isSlater [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hf_concave : ConcaveOn ℝ X f)
    (hg_cont : ContinuousOn g X)
    (hg_convex : ConvexOn ℝ X g)
    (hslater : IsSlater X (fun _ : Unit => g)) :
    primalValueScalar X f g = dualValueScalar X f g := by
  obtain ⟨x₀, hx₀X, hg_x₀⟩ := hslater.strict_feasible
  have hg_x₀_lt : g x₀ < 0 := hg_x₀ ()
  have hfeas_ne : (scalarFeasible X g).Nonempty :=
    ⟨x₀, hx₀X, hg_x₀_lt.le⟩
  have hweak :=
    primalValueScalar_le_dualValueScalar hcompact hf_cont hg_cont hfeas_ne
  refine le_antisymm hweak ?_
  set V := primalValueScalar X f g with hV_def
  by_contra hlt
  push Not at hlt
  set ε := (dualValueScalar X f g - V) / 2 with hε_def
  have hε_pos : 0 < ε := by
    have : 0 < dualValueScalar X f g - V := sub_pos.mpr hlt
    positivity
  have hVε_lt : V + ε < dualValueScalar X f g := by
    rw [hε_def]; linarith
  have hA_convex := achievableSet_convex hslater.convex_X hf_concave hg_convex
  have hA_closed := achievableSet_isClosed hcompact hf_cont hg_cont
  have hA_excl := not_mem_achievableSet_of_gt_primalValue hcompact hf_cont hfeas_ne hε_pos
  obtain ⟨L, c, hLx, hLA⟩ :=
    geometric_hahn_banach_point_closed hA_convex hA_closed hA_excl
  set α := L (1, 0) with hα_def
  set β := L (0, 1) with hβ_def
  have hL_decomp : ∀ u v : ℝ, L (u, v) = u * α + v * β := fun u v =>
    prod_apply_eq L u v
  have hsep_x : (V + ε) * β < c := by
    have := hLx
    rw [hL_decomp] at this
    linarith
  have hsep_A : ∀ p ∈ achievableSet X f g, c < p.1 * α + p.2 * β := by
    intro p hp
    have := hLA p hp
    rw [hL_decomp] at this
    linarith
  have hp₀_mem : (g x₀, f x₀) ∈ achievableSet X f g := image_mem_achievableSet hx₀X
  -- α ≥ 0: if α < 0 comprehensiveness lets u grow without bound, breaking separation.
  have hα_nonneg : 0 ≤ α := by
    by_contra hαneg
    push Not at hαneg
    have hαne : α ≠ 0 := ne_of_lt hαneg
    set K : ℝ := c - α * g x₀ - f x₀ * β with hK_def
    set δ : ℝ := (|K| + 1) * (-1 / α) with hδ_def
    have hinv_pos : 0 < -1 / α := by
      rw [neg_div]; exact neg_pos.mpr (div_neg_of_pos_of_neg one_pos hαneg)
    have hδ_pos : 0 < δ := by
      apply mul_pos _ hinv_pos
      linarith [abs_nonneg K]
    have hmem : (g x₀ + δ, f x₀) ∈ achievableSet X f g := by
      refine achievableSet_comprehensive hp₀_mem ?_ le_rfl
      linarith
    have hsep : c < (g x₀ + δ) * α + f x₀ * β := hsep_A (g x₀ + δ, f x₀) hmem
    have hαδ : α * δ = -(|K| + 1) := by
      rw [hδ_def]
      field_simp
    have hexpand : (g x₀ + δ) * α + f x₀ * β = α * g x₀ + α * δ + f x₀ * β := by ring
    rw [hexpand, hαδ] at hsep
    have hKlt : K < -(|K| + 1) := by rw [hK_def]; linarith
    linarith [abs_nonneg K, neg_abs_le K]
  -- β ≤ 0: symmetric argument via comprehensiveness in the v-direction.
  have hβ_nonpos : β ≤ 0 := by
    by_contra hβpos
    push Not at hβpos
    have hβne : β ≠ 0 := ne_of_gt hβpos
    set K : ℝ := c - g x₀ * α - β * f x₀ with hK_def
    set δ : ℝ := (|K| + 1) / β with hδ_def
    have hδ_pos : 0 < δ := by
      apply div_pos _ hβpos
      linarith [abs_nonneg K]
    have hmem : (g x₀, f x₀ - δ) ∈ achievableSet X f g := by
      refine achievableSet_comprehensive hp₀_mem le_rfl ?_
      linarith
    have hsep : c < g x₀ * α + (f x₀ - δ) * β := hsep_A (g x₀, f x₀ - δ) hmem
    have hβδ : β * δ = |K| + 1 := by
      rw [hδ_def]
      field_simp
    have hexpand : g x₀ * α + (f x₀ - δ) * β = g x₀ * α + β * f x₀ - β * δ := by ring
    rw [hexpand, hβδ] at hsep
    have hKlt : K < -(|K| + 1) := by rw [hK_def]; linarith
    linarith [abs_nonneg K, neg_abs_le K]
  -- Slater forces β < 0: if β = 0 then α · g x₀ > c, but α ≥ 0 and g x₀ < 0 give a contradiction.
  have hβ_neg : β < 0 := by
    rcases lt_or_eq_of_le hβ_nonpos with hβlt | hβeq
    · exact hβlt
    · exfalso
      -- With `β = 0` the separation collapses to `0 < c < α · g x₀ ≤ 0`.
      have hVε_mul_β : (V + ε) * β = 0 := by rw [hβeq]; ring
      have hc_pos : 0 < c := by linarith
      have hmem_sep := hsep_A (g x₀, f x₀) hp₀_mem
      have hfx₀β : f x₀ * β = 0 := by rw [hβeq]; ring
      have hα_gx₀_le : α * g x₀ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hα_nonneg hg_x₀_lt.le
      nlinarith [hmem_sep, hα_gx₀_le, hfx₀β]
  set lamStar : ℝ := -α / β with hlamStar_def
  have hlamStar_nonneg : 0 ≤ lamStar := by
    rw [hlamStar_def]
    exact div_nonneg_of_nonpos (neg_nonpos_of_nonneg hα_nonneg) hβ_neg.le
  -- Dividing the separation inequality by β < 0 reverses the sign and bounds the Lagrangian.
  have hdual_bound : ∀ x ∈ X, lagrangianScalar f g x lamStar ≤ c / β := by
    intro x hxX
    have hmem := hsep_A (g x, f x) (image_mem_achievableSet hxX)
    unfold lagrangianScalar
    rw [hlamStar_def]
    have hβne : β ≠ 0 := ne_of_lt hβ_neg
    have : (g x * α + f x * β) / β < c / β :=
      div_lt_div_of_neg_of_lt hβ_neg hmem
    have heq : (g x * α + f x * β) / β = f x + α * g x / β := by
      field_simp
      ring
    rw [heq] at this
    have hsub : f x - -α / β * g x = f x + α * g x / β := by
      field_simp
      ring
    linarith
  have hX_ne : X.Nonempty := ⟨x₀, hx₀X⟩
  have hdualObj_img_ne :
      ((fun x => lagrangianScalar f g x lamStar) '' X).Nonempty := hX_ne.image _
  have hdualObj_le : dualObjectiveScalar X f g lamStar ≤ c / β := by
    unfold dualObjectiveScalar
    refine csSup_le hdualObj_img_ne ?_
    rintro y ⟨x, hxX, rfl⟩
    exact hdual_bound x hxX
  have hc_div : c / β < V + ε := by
    have hβne : β ≠ 0 := ne_of_lt hβ_neg
    have hstep : c / β < (V + ε) * β / β := div_lt_div_of_neg_of_lt hβ_neg hsep_x
    rwa [mul_div_assoc, div_self hβne, mul_one] at hstep
  have hdualValue_le : dualValueScalar X f g ≤ dualObjectiveScalar X f g lamStar := by
    unfold dualValueScalar
    have hmem : dualObjectiveScalar X f g lamStar ∈ dualObjectiveScalar X f g '' Ici 0 :=
      ⟨lamStar, hlamStar_nonneg, rfl⟩
    refine csInf_le ?_ hmem
    -- f x₀ is a lower bound: for any lam ≥ 0, x₀ feasible gives f x₀ ≤ dualObjective lam.
    refine ⟨f x₀, ?_⟩
    rintro w ⟨lam, hlam, rfl⟩
    exact scalarFeasible_le_dualObjectiveScalar hcompact hf_cont hg_cont hlam ⟨hx₀X, hg_x₀_lt.le⟩
  linarith

/-! ### Dual attainment under Slater

The dual objective `φ(λ) = sup_{x∈X}(f x − λ·g x)` is Lipschitz in `λ` (it is a supremum of
functions affine in `λ` with slopes `−g x` uniformly bounded on the compact set `X`). Slater's
strictly feasible point `x₀` forces `φ(λ) → ∞` as `λ → ∞`, so the infimum over `λ ≥ 0` is attained
on a compact interval — the dual infimum is a minimum, achieved by an optimal multiplier
`λ* ≥ 0`. -/

/-- A uniform bound `G` on `|g|` over the compact set `X`: `|g x| ≤ G` for all `x ∈ X`. -/
private lemma exists_abs_g_bound {X : Set E} {g : E → ℝ}
    (hcompact : IsCompact X) (hg_cont : ContinuousOn g X) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x ∈ X, |g x| ≤ G := by
  rcases X.eq_empty_or_nonempty with hX | hX
  · exact ⟨0, le_rfl, fun x hx => by simp [hX] at hx⟩
  · obtain ⟨x_max, _, hmax⟩ :=
      hcompact.exists_isMaxOn hX (hg_cont.abs)
    exact ⟨|g x_max|, abs_nonneg _, fun x hx => hmax hx⟩

/-- **The dual objective is Lipschitz in the multiplier.** The one-sided shift
`φ(λ₁) ≤ φ(λ₂) + G·|λ₁ − λ₂|`, where `G` bounds `|g|` on `X`. -/
private lemma dualObjectiveScalar_lipschitz {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X) (hf_cont : ContinuousOn f X) (hg_cont : ContinuousOn g X)
    (hX_ne : X.Nonempty) {G : ℝ} (hG_bound : ∀ x ∈ X, |g x| ≤ G)
    (lam₁ lam₂ : ℝ) :
    dualObjectiveScalar X f g lam₁ ≤ dualObjectiveScalar X f g lam₂ + G * |lam₁ - lam₂| := by
  refine dualObjectiveScalar_le hX_ne (fun x hx => ?_)
  have hbdd₂ := lagrangianScalar_image_bddAbove hcompact hf_cont hg_cont lam₂
  have hle₂ : lagrangianScalar f g x lam₂ ≤ dualObjectiveScalar X f g lam₂ :=
    le_dualObjectiveScalar hbdd₂ hx
  -- `(λ₂ − λ₁)·g x ≤ |λ₁ − λ₂|·G` bounds the shift between the two Lagrangians.
  have hshift : lagrangianScalar f g x lam₁ ≤ lagrangianScalar f g x lam₂ + G * |lam₁ - lam₂| := by
    have hgx : (lam₂ - lam₁) * g x ≤ G * |lam₁ - lam₂| := by
      calc (lam₂ - lam₁) * g x
          ≤ |(lam₂ - lam₁) * g x| := le_abs_self _
        _ = |lam₁ - lam₂| * |g x| := by rw [abs_mul, abs_sub_comm]
        _ ≤ |lam₁ - lam₂| * G := mul_le_mul_of_nonneg_left (hG_bound x hx) (abs_nonneg _)
        _ = G * |lam₁ - lam₂| := mul_comm _ _
    simp only [lagrangianScalar]; nlinarith [hgx]
  linarith

/-- The dual objective is continuous in the multiplier (it is Lipschitz). -/
private lemma dualObjectiveScalar_continuous {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X) (hf_cont : ContinuousOn f X) (hg_cont : ContinuousOn g X)
    (hX_ne : X.Nonempty) :
    Continuous (dualObjectiveScalar X f g) := by
  obtain ⟨G, hG_nonneg, hG_bound⟩ := exists_abs_g_bound hcompact hg_cont
  -- Two-sided Lipschitz bound `|φ(λ₁) − φ(λ₂)| ≤ G·|λ₁ − λ₂|` from the one-sided shift both ways.
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal G) (fun lam₁ lam₂ => ?_)).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal G hG_nonneg]
  have hfwd := dualObjectiveScalar_lipschitz hcompact hf_cont hg_cont hX_ne hG_bound lam₁ lam₂
  have hbwd := dualObjectiveScalar_lipschitz hcompact hf_cont hg_cont hX_ne hG_bound lam₂ lam₁
  rw [abs_sub_comm lam₂ lam₁] at hbwd
  rw [abs_le]
  constructor <;> linarith

/-- **Dual attainment under Slater** (Slater 1950; Boyd and Vandenberghe 2004). Under a compact
convex feasible set, continuous concave objective, continuous convex constraint, and Slater's
condition, the dual infimum is attained: There is an optimal multiplier `λ* ≥ 0` with
`IsLeast (φ '' Ici 0) (φ λ*)`, where `φ` is the dual objective. -/
theorem dualAttainment_scalar_of_isSlater [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    -- Concavity/convexity of the primal data are not needed for *dual* attainment (the dual
    -- objective is automatically convex and continuous); they are kept so the hypothesis set
    -- matches `strongDuality_scalar_of_isSlater`, letting consumers pass identical arguments.
    (_hf_concave : ConcaveOn ℝ X f)
    (hg_cont : ContinuousOn g X)
    (_hg_convex : ConvexOn ℝ X g)
    (hslater : IsSlater X (fun _ : Unit => g)) :
    ∃ lam, 0 ≤ lam ∧
      IsLeast (dualObjectiveScalar X f g '' Ici 0) (dualObjectiveScalar X f g lam) := by
  classical
  obtain ⟨x₀, hx₀X, hg_x₀⟩ := hslater.strict_feasible
  have hg_x₀_lt : g x₀ < 0 := hg_x₀ ()
  have hX_ne : X.Nonempty := ⟨x₀, hx₀X⟩
  have hcont : Continuous (dualObjectiveScalar X f g) :=
    dualObjectiveScalar_continuous hcompact hf_cont hg_cont hX_ne
  -- Slater lower bound: `φ(λ) ≥ f x₀ + λ·(−g x₀)`, with `−g x₀ > 0`.
  have hslater_lb : ∀ lam : ℝ, f x₀ + lam * (-g x₀) ≤ dualObjectiveScalar X f g lam := by
    intro lam
    have hbdd := lagrangianScalar_image_bddAbove hcompact hf_cont hg_cont lam
    have hle := le_dualObjectiveScalar hbdd hx₀X
    simp only [lagrangianScalar] at hle
    have hrw : f x₀ - lam * g x₀ = f x₀ + lam * (-g x₀) := by ring
    linarith [hrw ▸ hle]
  set B := dualObjectiveScalar X f g 0 with hB_def
  -- Multipliers above `M` exceed the reference value `B = φ(0)`, so the search is over `[0, M]`.
  set M : ℝ := max 0 ((B - f x₀) / (-g x₀)) with hM_def
  have hM_nonneg : 0 ≤ M := le_max_left _ _
  have hneg_g_pos : 0 < -g x₀ := neg_pos.mpr hg_x₀_lt
  -- For `λ > M`, `φ(λ) > B`.
  have h_large : ∀ lam : ℝ, M < lam → B < dualObjectiveScalar X f g lam := by
    intro lam hlam
    have hMge : (B - f x₀) / (-g x₀) ≤ M := le_max_right _ _
    have hbig : (B - f x₀) / (-g x₀) < lam := lt_of_le_of_lt hMge hlam
    have hstep : B - f x₀ < lam * (-g x₀) := by
      rw [div_lt_iff₀ hneg_g_pos] at hbig; linarith
    linarith [hslater_lb lam]
  -- `φ` attains a minimum on the compact interval `[0, M]`.
  obtain ⟨lamStar, hlamStar_mem, hlamStar_min⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMinOn
      (Set.nonempty_Icc.mpr hM_nonneg) hcont.continuousOn
  obtain ⟨hlamStar_0, hlamStar_M⟩ := Set.mem_Icc.mp hlamStar_mem
  refine ⟨lamStar, hlamStar_0, ⟨⟨lamStar, mem_Ici.mpr hlamStar_0, rfl⟩, ?_⟩⟩
  -- `lamStar` is a global minimizer over `Ici 0`.
  rintro v ⟨lam, hlam, rfl⟩
  rw [mem_Ici] at hlam
  rcases le_or_gt lam M with hlamM | hlamM
  · -- `lam ∈ [0, M]`: directly use the interval minimum.
    exact hlamStar_min (Set.mem_Icc.mpr ⟨hlam, hlamM⟩)
  · -- `lam > M`: `φ(lam) > B = φ(0) ≥ φ(lamStar)` since `0 ∈ [0, M]`.
    have hB_ge : dualObjectiveScalar X f g lamStar ≤ B :=
      hlamStar_min (Set.mem_Icc.mpr ⟨le_rfl, hM_nonneg⟩)
    linarith [h_large lam hlamM]

end ScalarDuality

section ParametricSlater

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **Strong duality** under `IsParametricSlater` (Slater 1950; Boyd and Vandenberghe 2004): For a
compact feasible set, concave continuous objective, and convex continuous constraint satisfying
parametric Slater's condition at `p₀`, the primal and dual values at `p₀` agree. -/
theorem strongDuality_scalar_of_parametricSlater
    {P : Type*} [TopologicalSpace P]
    {X : Set E} {f : P → E → ℝ} {g : P → E → ℝ} {p₀ : P}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn (f p₀) X)
    (hf_concave : ConcaveOn ℝ X (f p₀))
    (hg_cont : ContinuousOn (g p₀) X)
    (hg_convex : ConvexOn ℝ X (g p₀))
    (hslater : IsParametricSlater X (fun p (_ : Unit) => g p) p₀) :
    primalValueScalar X (f p₀) (g p₀) = dualValueScalar X (f p₀) (g p₀) :=
  strongDuality_scalar_of_isSlater hcompact hf_cont hf_concave hg_cont hg_convex
    hslater.toIsSlater

end ParametricSlater

/-! ### Bridge to the unified `ConstrainedProblem` core

The scalar API (`g : E → ℝ`, `lam : ℝ`) is a `Unit`-indexed, `Empty`-equality specialization of
`ConstrainedProblem` / `lagrangian`. These lemmas make that correspondence definitional. -/

section Bridge

variable {E : Type*}

/-- Promote a scalar pair `(f, g : E → ℝ)` to a `Unit`-indexed, `Empty`-equality
`ConstrainedProblem`. -/
def toUnitConstrainedProblem (f g : E → ℝ) : ConstrainedProblem E Unit Empty where
  f := f
  g := fun _ => g
  h := Empty.elim

/-- Scalar Lagrangian agrees with the `Unit`-indexed unified `lagrangian`. -/
lemma lagrangianScalar_eq_lagrangian (f g : E → ℝ) (x : E) (lam : ℝ) :
    lagrangianScalar f g x lam =
      lagrangian (toUnitConstrainedProblem f g) x (fun _ => lam) Empty.elim := by
  simp [lagrangianScalar, lagrangian, toUnitConstrainedProblem]

/-- The scalar feasibility set agrees with the `Unit`-indexed `feasibleSetIneq` intersected with
the ambient `X`. -/
lemma scalarFeasible_eq (X : Set E) (g : E → ℝ) :
    scalarFeasible X g =
      X ∩ ConstrainedProblem.feasibleSetIneq
        (toUnitConstrainedProblem (fun _ => (0 : ℝ)) g) := by
  ext x
  simp [scalarFeasible, ConstrainedProblem.feasibleSetIneq, toUnitConstrainedProblem]

end Bridge

end Econlib.Optimization
