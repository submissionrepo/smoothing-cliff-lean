/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Order.BourbakiWitt
public import Optlib.Convex.Subgradient

/-!
# Danskin's theorem (convex envelope form)

Let `E` be a real inner product space, `Z` a compact topological space, and `f : E → Z → ℝ`. The
value function is `V(x) = sup_{z ∈ Z} f(x, z)` and the optimizer set is
`Z*(x) = argmax_{z ∈ Z} f(x, z)`. Under joint continuity of `f` on `X × Z` and convexity of
`f(·, z)` on `X` for each `z`, **Danskin's theorem** describes the convexity and differential
structure of `V`: It is convex with nonempty optimizer set, its directional derivative is the
maximum of directional derivatives over optimizers, and its subdifferential is the closed convex
hull of the subdifferentials at optimizers. When `f(·, z)` is differentiable and the optimizers
share a common gradient (in particular when the optimizer is unique), `V` is differentiable with
that gradient.

## Main definitions

* `valueFunction` — the value function `V(x) = ⨆ z, f x z`.
* `argmax_iSup` — the optimizer set `Z*(x)`.
* `HasRightDirDerivAt` — the right-sided directional derivative.
* `ContinuousOnProd`, `ConvexOnFiber` — the joint-continuity and fiberwise-convexity hypotheses.

## Main statements

* `convexOn_valueFunction_argmax` — convexity, finiteness, and nonempty optimizer set.
* `hasRightDirDeriv_iSup` — the directional derivative equals the maximum over optimizers.
* `subderivWithinAt_valueFunction` — the subdifferential is the closed convex hull of the
  subdifferentials at optimizers.
* `hasGradientAt_iSup_of_const_grad`, `hasGradientAt_iSup_of_unique` — differentiability of `V`
  under a common-gradient (respectively unique-optimizer) hypothesis.

## References

* Danskin, John M. 1967. *The Theory of Max-Min and Its Application to Weapons Allocation
  Problems*. Springer.
* Milgrom, Paul, and Ilya Segal. 2002. “Envelope Theorems for Arbitrary Choice Sets.”
  *Econometrica* 70 (2): 583–601. [https://doi.org/10.1111/1468-0262.00296](https://doi.org/10.1111/1468-0262.00296).
-/

@[expose] public section

open Set Filter Topology InnerProductSpace

namespace Danskin

/-! ### Core Definitions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]

/-- The value function `V(x) = sup_{z ∈ Z} f(x, z)`. -/
noncomputable def valueFunction (f : E → Z → ℝ) (x : E) : ℝ :=
  ⨆ z : Z, f x z

/-- The optimizer set `Z*(x) = {z : Z | f(x, z) = V(x)}`. -/
def argmax_iSup (f : E → Z → ℝ) (x : E) : Set Z :=
  { z : Z | f x z = valueFunction f x }

/-- Right-sided directional derivative of `g` at `x` in direction `v`. -/
def HasRightDirDerivAt (g : E → ℝ) (x v : E) (d : ℝ) : Prop :=
  Filter.Tendsto (fun t ↦ (g (x + t • v) - g x) / t)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)

/-! ### Hypotheses -/

/-- Joint continuity of `f` on `X × Z`. -/
def ContinuousOnProd (f : E → Z → ℝ) (X : Set E) : Prop :=
  ContinuousOn (fun p : E × Z ↦ f p.1 p.2) (X ×ˢ univ)

/-- Convexity of `f(·, z)` on `X` for each `z`. -/
def ConvexOnFiber (f : E → Z → ℝ) (X : Set E) : Prop :=
  ∀ z : Z, ConvexOn ℝ X (fun x ↦ f x z)

/-! ### Auxiliary Lemmas -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] [CompactSpace Z] [Nonempty Z] in
/-- Continuity of `z ↦ f(x, z)` for fixed `x ∈ X`, extracted from joint continuity. -/
lemma ContinuousOnProd.continuous_right {f : E → Z → ℝ} {X : Set E}
    (h_cont : ContinuousOnProd f X) (x : E) (hx : x ∈ X) :
    Continuous (fun z ↦ f x z) := by
  rw [show (fun z ↦ f x z) = (fun p : E × Z ↦ f p.1 p.2) ∘ (fun z ↦ (x, z)) from rfl]
  apply ContinuousOn.comp_continuous h_cont
    (continuous_prodMk.mpr ⟨continuous_const, continuous_id'⟩)
  intro z; exact ⟨hx, mem_univ z⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The supremum `⨆ z, f x z` is attained when `Z` is compact and `z ↦ f x z` is continuous. -/
lemma exists_eq_ciSup {x : E} (f : E → Z → ℝ)
    (hf : Continuous (fun z ↦ f x z)) :
    ∃ z : Z, f x z = ⨆ z : Z, f x z := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨z, le_antisymm
    (le_ciSup (isCompact_range hf).bddAbove z)
    (ciSup_le fun z' ↦ hz (mem_univ z'))⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The optimizer set is nonempty when `z ↦ f x z` is continuous. -/
lemma argmax_iSup_nonempty {x : E} (f : E → Z → ℝ)
    (hf : Continuous (fun z ↦ f x z)) :
    (argmax_iSup f x).Nonempty :=
  (exists_eq_ciSup f hf).imp fun _ hz ↦ hz

/-! ### Subdifferential at differentiability points -/

omit [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z] in
/-- For `f : E → ℝ` differentiable at `x`, the ray `t ↦ f(x + t • w)` has derivative `⟪∇f x, w⟫` at
`0` (chain rule, gradient form). -/
private lemma hasDerivAt_ray_inner_gradient (f : E → ℝ) {x : E} (hx : DifferentiableAt ℝ f x)
    (w : E) :
    HasDerivAt (fun t : ℝ => f (x + t • w)) (@inner ℝ E _ (gradient f x) w) 0 := by
  have hsmul : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const w
    rw [one_smul] at h
    have h3 := (hasDerivAt_const (0 : ℝ) x).add h
    rwa [zero_add] at h3
  have hf_at : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • w) := by
    simp only [zero_smul, add_zero]; exact hx.hasFDerivAt
  have h_chain : HasDerivAt (fun t : ℝ => f (x + t • w)) (fderiv ℝ f x w) 0 :=
    hf_at.comp_hasDerivAt 0 hsmul
  have h_inner : fderiv ℝ f x w = @inner ℝ E _ (gradient f x) w := by simp [gradient]
  rwa [h_inner] at h_chain

omit [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z] in
/-- The `gradient`/`DifferentiableAt` form of optlib's `SubderivWithinAt_eq_gradient`: For
`f : E → ℝ` convex on `Set.univ` and differentiable at `x`, the gradient `∇f x` is in
`SubderivWithinAt f Set.univ x`. -/
lemma _root_.gradient_mem_SubderivWithinAt (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f) {x : E} (hx : DifferentiableAt ℝ f x) :
    gradient f x ∈ SubderivWithinAt f Set.univ x := by
  -- optlib computes the whole subderiv at an interior point as the gradient singleton.
  have h_eq : SubderivWithinAt f Set.univ x = {gradient f x} :=
    SubderivWithinAt_eq_gradient (s := Set.univ) (by simp) hf hx.hasGradientAt
  rw [h_eq]; exact Set.mem_singleton _

omit [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z] in
/-- For `f : E → ℝ` differentiable at `x`, optlib's `SubderivWithinAt f Set.univ x` is contained in
the singleton `{gradient f x}`. Convexity is not required, so this strengthens optlib's
`SubderivWithinAt_eq_gradient` on the inclusion side. -/
lemma _root_.SubderivWithinAt.subset_singleton_of_differentiableAt (f : E → ℝ) {x : E}
    (hx : DifferentiableAt ℝ f x) :
    SubderivWithinAt f Set.univ x ⊆ {gradient f x} := by
  intro p hp
  rw [Set.mem_singleton_iff]
  -- Use ext_inner_right: suffices ∀ v, ⟪p, v⟫ = ⟪gradient f x, v⟫.
  refine ext_inner_right ℝ ?_
  intro v
  -- Show both ⟪p, v⟫ ≤ ⟪∇f x, v⟫ and ⟪p, v⟫ ≥ ⟪∇f x, v⟫.
  have h_le : ∀ w : E, @inner ℝ E _ p w ≤ @inner ℝ E _ (gradient f x) w := by
    intro w
    -- g(t) = f(x + t • w); g'(0) = ⟪∇f x, w⟫.
    have hg_deriv : HasDerivAt (fun t : ℝ => f (x + t • w))
        (@inner ℝ E _ (gradient f x) w) 0 :=
      hasDerivAt_ray_inner_gradient f hx w
    -- For t > 0: ⟪p, w⟫ ≤ slope g 0 t.
    have h_slope_ge : ∀ᶠ t in 𝓝[>] (0 : ℝ), @inner ℝ E _ p w ≤ slope (fun t => f (x + t • w)) 0 t
        := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h_pos : (0 : ℝ) < t := ht
      have h_sub : f x + @inner ℝ E _ p (t • w) ≤ f (x + t • w) := by
        have h := hp (x + t • w) (Set.mem_univ _)
        simp only [add_sub_cancel_left] at h
        exact h
      rw [real_inner_smul_right] at h_sub
      have h_slope_eq : slope (fun t => f (x + t • w)) 0 t = (f (x + t • w) - f x) / t := by
        rw [slope_def_field]; simp
      rw [h_slope_eq, le_div_iff₀ h_pos]
      linarith
    -- Tendsto slope → ⟪∇f x, w⟫.
    have h_tendsto : Tendsto (slope (fun t => f (x + t • w)) 0) (𝓝[>] (0 : ℝ))
        (𝓝 (@inner ℝ E _ (gradient f x) w)) := by
      have h_subset : {t : ℝ | 0 < t} ⊆ {t : ℝ | t ≠ 0} := fun t ht => ne_of_gt ht
      exact hg_deriv.tendsto_slope.mono_left (nhdsWithin_mono _ h_subset)
    exact ge_of_tendsto h_tendsto h_slope_ge
  -- Sandwich with v and -v.
  have h1 := h_le v
  have h2 := h_le (-v)
  rw [inner_neg_right, inner_neg_right] at h2
  linarith

omit [CompleteSpace E] [TopologicalSpace Z] [CompactSpace Z] in
/-- The value function `V(x) = ⨆ z, f x z` is convex on `X` when each fiber `f(·, z)` is convex and
the supremum is bounded above pointwise. -/
lemma convexOn_valueFunction {f : E → Z → ℝ} {X : Set E}
    (hX : Convex ℝ X)
    (h_conv : ConvexOnFiber f X)
    (h_bdd : ∀ x ∈ X, BddAbove (range (fun z ↦ f x z))) :
    ConvexOn ℝ X (valueFunction f) := by
  constructor
  · exact hX
  · intro x hx y hy a b ha hb hab
    apply ciSup_le
    intro z
    calc f (a • x + b • y) z
        ≤ a * f x z + b * f y z := (h_conv z).2 hx hy ha hb hab
      _ ≤ a * valueFunction f x + b * valueFunction f y := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (le_ciSup (h_bdd x hx) z) ha
          · exact mul_le_mul_of_nonneg_left (le_ciSup (h_bdd y hy) z) hb

/-! ### Part (i): Attainment, Finiteness, and Convexity -/

omit [CompleteSpace E] in
/-- **Danskin Part 1.** Under joint continuity and pointwise convexity, the value function `V` is
convex, the supremum is bounded, and the optimizer set is nonempty. -/
theorem convexOn_valueFunction_argmax (f : E → Z → ℝ) (X : Set E)
    (hX_convex : Convex ℝ X)
    (h_cont : ContinuousOnProd f X) (h_conv : ConvexOnFiber f X)
    (x : E) (hx : x ∈ X) :
    ConvexOn ℝ X (valueFunction f) ∧
    BddAbove (range (f x)) ∧
    (argmax_iSup f x).Nonempty := by
  have hfx := ContinuousOnProd.continuous_right h_cont x hx
  exact ⟨convexOn_valueFunction hX_convex h_conv fun y hy ↦
      (isCompact_range (ContinuousOnProd.continuous_right h_cont y hy)).bddAbove,
    (isCompact_range hfx).bddAbove,
    argmax_iSup_nonempty f hfx⟩

/-! ### Part (ii): Directional Derivative Formula -/

omit [CompleteSpace E] in
/-- **Danskin Part (ii).** The right directional derivative of the value function exists and equals
the maximum of directional derivatives over the optimizer set:
`V'(x; v) = max_{z ∈ Z*(x)} f'(x, z; v)`. The conclusion delivers this maximum explicitly: The
value `d` is attained at some `z_max ∈ Z*(x)`, and it dominates the directional derivative at every
optimizer. -/
theorem hasRightDirDeriv_iSup (f : E → Z → ℝ) (X : Set E)
    (hX_open : IsOpen X) (hX_convex : Convex ℝ X)
    (h_cont : ContinuousOnProd f X) (h_conv : ConvexOnFiber f X)
    (x v : E) (hx : x ∈ X)
    (h_dir : ∀ z ∈ argmax_iSup f x,
      ∃ d : ℝ, HasRightDirDerivAt (fun w ↦ f w z) x v d) :
    ∃ d : ℝ, HasRightDirDerivAt (valueFunction f) x v d ∧
      (∃ z_max ∈ argmax_iSup f x,
        HasRightDirDerivAt (fun w ↦ f w z_max) x v d) ∧
      ∀ z ∈ argmax_iSup f x, ∀ d_z : ℝ,
        HasRightDirDerivAt (fun w ↦ f w z) x v d_z → d_z ≤ d := by
  have hfx_cont := ContinuousOnProd.continuous_right h_cont x hx
  have ⟨hV_convex, hbdd_x, hopt_ne⟩ :=
    convexOn_valueFunction_argmax f X hX_convex h_cont h_conv x hx
  have h_ray_cts : Continuous (fun t : ℝ ↦ x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- x + tv ∈ X for small t (X is open)
  have h_small_t : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), x + t • v ∈ X := by
    have : Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
      simpa using h_ray_cts.tendsto 0
    exact (this.eventually (hX_open.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
  have h_bdd_at : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      BddAbove (range (fun z ↦ f (x + t • v) z)) := by
    filter_upwards [h_small_t] with t ht
    exact (isCompact_range (ContinuousOnProd.continuous_right h_cont _ ht)).bddAbove
  /- ## Step 1: Reduce to existence of g'(0+) for g(t) = V(x + tv)
     g is convex on the preimage interval S = {t | x + tv ∈ X}
     Since V is convex on X and the map t ↦ x + tv is affine, g is convex on S.
     S is open (preimage of open set under continuous map) and contains 0.
     By ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior, g has a right derivative at 0.
     This right derivative is the directional derivative of V. -/
  let ray : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t ↦ x + t • v
      linear := (LinearMap.lsmul ℝ E).flip v
      map_vadd' := by intro p q; simp [vadd_eq_add, add_smul]; abel }
  let S := (fun t : ℝ ↦ x + t • v) ⁻¹' X
  have hS_open : IsOpen S := hX_open.preimage h_ray_cts
  have h0_in_S : (0 : ℝ) ∈ S := by simp [S, hx]
  have h0_interior : (0 : ℝ) ∈ interior S := by rwa [hS_open.interior_eq]
  -- g is convex on S, the preimage of X under the affine ray.
  have hg_convex : ConvexOn ℝ S (fun t ↦ valueFunction f (x + t • v)) :=
    hV_convex.comp_affineMap ray
  -- g has a right derivative at 0 — convert to HasRightDirDerivAt
  set d_V := derivWithin (fun t : ℝ ↦ valueFunction f (x + t • v)) (Ioi 0) (0 : ℝ)
  have hV_dir : HasRightDirDerivAt (valueFunction f) x v d_V := by
    rw [HasRightDirDerivAt]
    have hg_deriv := hg_convex.hasDerivWithinAt_rightDeriv_of_mem_interior h0_interior
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)] at hg_deriv
    have : (fun t : ℝ ↦ (valueFunction f (x + t • v) - valueFunction f x) / t) =
        slope (fun t ↦ valueFunction f (x + t • v)) 0 := by
      ext t; simp [slope, sub_zero, div_eq_inv_mul]
    rw [this]; exact hg_deriv
  -- ── Step 2: Lower bound — d_V ≥ d_z for any z ∈ Z*(x) ──
  have h_lower_bound : ∀ z ∈ argmax_iSup f x,
      ∀ d_z, HasRightDirDerivAt (fun w ↦ f w z) x v d_z → d_z ≤ d_V := by
    intro z hz d_z hd_z
    /- V(x+tv) ≥ f(x+tv, z) and V(x) = f(x, z) since z ∈ Z*(x)
       So (V(x+tv) - V(x))/t ≥ (f(x+tv, z) - f(x, z))/t for t > 0
       Taking limits: d_V ≥ d_z -/
    apply le_of_tendsto_of_tendsto hd_z hV_dir
    filter_upwards [h_small_t, h_bdd_at, self_mem_nhdsWithin] with t ht_X ht_bdd ht_pos
    rw [Set.mem_Ioi] at ht_pos
    apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
    have hle : f (x + t • v) z ≤ valueFunction f (x + t • v) := le_ciSup ht_bdd z
    rw [hz]; linarith
  /- ## Step 3: Upper bound — d_V ≤ d_{z̄} for some z̄ ∈ Z*(x)
     This is the sequential compactness argument.
     For the existential conclusion, we need to find z_max with d_V = d_{z_max}.
     From Step 2, d_V ≥ d_z for all z ∈ Z*(x).
     The upper bound d_V ≤ max_{z ∈ Z*(x)} d_z requires:
       (a) choosing optimizers z_t at x+tv (IsCompact.exists_isMaxOn)
       (b) extracting z_t → z̄ (IsCompact.tendsto_subseq)
       (c) showing z̄ ∈ Z*(x) (joint continuity + Berge)
       (d) showing d_V ≤ d_{z̄} (convex slope monotonicity + continuity) -/
  have h_upper_bound : ∃ zb : Z, zb ∈ argmax_iSup f x ∧
      ∃ db : ℝ, HasRightDirDerivAt (fun w ↦ f w zb) x v db ∧ d_V ≤ db := by
    -- ### (a) Choose optimizers z_t at x+tv via classical choice
    have h_opt_choice : ∃ zc : ℝ → Z, ∀ t : ℝ, x + t • v ∈ X →
        f (x + t • v) (zc t) = valueFunction f (x + t • v) := by
      have : ∀ t : ℝ, ∃ z : Z, x + t • v ∈ X →
          f (x + t • v) z = valueFunction f (x + t • v) := by
        intro t; by_cases ht : x + t • v ∈ X
        · exact ⟨_, fun _ ↦ exists_eq_ciSup f
            (ContinuousOnProd.continuous_right h_cont _ ht) |>.choose_spec⟩
        · exact ⟨Classical.arbitrary Z, fun h ↦ absurd h ht⟩
      exact ⟨fun t ↦ (this t).choose, fun t ht ↦ (this t).choose_spec ht⟩
    obtain ⟨zc, hzc_opt⟩ := h_opt_choice
    -- ### (b) Extract cluster point z̄ of z_t as t → 0⁺ (compactness of Z)
    have hne : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
    obtain ⟨z_bar, hz_cluster⟩ : ∃ z_bar : Z,
        MapClusterPt z_bar (nhdsWithin (0 : ℝ) (Ioi 0)) zc := by
      obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace
        (map zc (nhdsWithin (0 : ℝ) (Ioi 0)))
      exact ⟨z, by rwa [mapClusterPt_def]⟩
    -- ### (c) Show z̄ ∈ Z*(x) via Berge-style argument
    have hz_bar_opt : z_bar ∈ argmax_iSup f x := by
      apply le_antisymm (le_ciSup ((isCompact_range hfx_cont).bddAbove) z_bar)
      -- V(x) ≤ f(x, z̄): cluster point of V(x+tv) = f(x+tv, z_t) at f(x, z̄),
      -- and f(x+tv, z_star) → V(x) ≤ f(x+tv, z_t), squeeze gives V(x) ≤ f(x, z̄)
      obtain ⟨z_star, hz_star⟩ := hopt_ne
      set Vx := valueFunction f x
      have h_ray_tends : Tendsto (fun t : ℝ ↦ x + t • v)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x) := by
        have : Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
          conv => arg 3; rw [show x = x + (0 : ℝ) • v by simp]
          exact tendsto_const_nhds.add
            (continuous_id.tendsto 0 |>.smul tendsto_const_nhds)
        exact this.mono_left nhdsWithin_le_nhds
      have h_pair : MapClusterPt (x, z_bar) (nhdsWithin (0 : ℝ) (Ioi 0))
          (fun t ↦ ((x + t • v : E), zc t)) := by
        rw [mapClusterPt_iff_frequently]; intro s hs; rw [nhds_prod_eq] at hs
        obtain ⟨u, hu, w, hw, huw⟩ := Filter.mem_prod_iff.mp hs
        exact (hz_cluster.frequently hw).and_eventually
          (h_ray_tends.eventually hu) |>.mono fun t ⟨hzw, hxu⟩ ↦ huw ⟨hxu, hzw⟩
      have h_fcluster : MapClusterPt (f x z_bar) (nhdsWithin (0 : ℝ) (Ioi 0))
          (fun t ↦ f (x + t • v) (zc t)) :=
        ((h_cont (x, z_bar) ⟨hx, mem_univ z_bar⟩).continuousAt
          ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_bar⟩)).mapClusterPt h_pair
      have h_fz_tends : Tendsto (fun t : ℝ ↦ f (x + t • v) z_star)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds Vx) := by
        rw [show Vx = f x z_star from hz_star.symm]
        exact ((h_cont (x, z_star) ⟨hx, mem_univ z_star⟩).continuousAt
          ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_star⟩)).tendsto.comp
          (Tendsto.prodMk_nhds h_ray_tends tendsto_const_nhds)
      have h_le_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          f (x + t • v) z_star ≤ f (x + t • v) (zc t) := by
        filter_upwards [h_small_t, h_bdd_at] with t ht_mem ht_bdd
        rw [hzc_opt t ht_mem]; exact le_ciSup ht_bdd z_star
      by_contra hlt; push Not at hlt
      -- f(x, z̄) < Vx, midpoint squeeze contradiction
      change f x z_bar < Vx at hlt
      have hm1 : f x z_bar < (Vx + f x z_bar) / 2 := by linarith
      have hm2 : (Vx + f x z_bar) / 2 < Vx := by linarith
      exact (h_fcluster.frequently (Iio_mem_nhds hm1))
        (by filter_upwards [h_le_ev, h_fz_tends.eventually (Ioi_mem_nhds hm2)]
            with t hle hfm; linarith)
    -- ### (d) Get directional derivative at z̄ and show d_V ≤ d_{z̄}
    obtain ⟨db, hdb⟩ := h_dir z_bar hz_bar_opt
    refine ⟨z_bar, hz_bar_opt, db, hdb, ?_⟩
    -- Use ge_of_tendsto: db is the limit of slopes of g_{z̄}, and d_V ≤ each slope
    apply ge_of_tendsto hdb
    /- For T > 0 in S: d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
       via slope chain: d_V ≤ slope g_V 0 t ≤ slope g_{z_t} 0 t ≤ slope g_{z_t} 0 T
       then cluster point argument for fixed T. -/
    have h_S_ev : ∀ᶠ T in nhdsWithin (0 : ℝ) (Ioi 0), T ∈ S :=
      nhdsWithin_le_nhds (hS_open.mem_nhds h0_in_S)
    filter_upwards [h_S_ev, self_mem_nhdsWithin (s := Ioi 0)] with T hT_S hT_pos_mem
    rw [mem_Ioi] at hT_pos_mem
    -- For this fixed T: show d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
    have hT_mem_X : x + T • v ∈ X := by rw [show S = _ from rfl] at hT_S; exact hT_S
    have h_bound_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        d_V ≤ (f (x + T • v) (zc t) - f x (zc t)) / T := by
      filter_upwards [nhdsWithin_le_nhds (hS_open.mem_nhds h0_in_S),
        nhdsWithin_le_nhds (Iio_mem_nhds hT_pos_mem),
        self_mem_nhdsWithin (s := Ioi 0)] with t ht_S ht_lt ht_pos
      rw [mem_Ioi] at ht_pos; rw [mem_Iio] at ht_lt
      have ht_mem_X : x + t • v ∈ X := by rw [show S = _ from rfl] at ht_S; exact ht_S
      have h1 : d_V ≤ slope (fun s ↦ valueFunction f (x + s • v)) 0 t := by
        rw [show d_V = derivWithin _ _ _ from rfl]
        exact hg_convex.rightDeriv_le_slope_of_mem_interior h0_interior ht_S ht_pos
      have h_slope_eq : slope (fun s ↦ valueFunction f (x + s • v)) 0 t =
          (valueFunction f (x + t • v) - valueFunction f x) / t := by
        simp [slope, sub_zero, div_eq_inv_mul]
      -- (V(x+tv) - V(x))/t ≤ (f(x+tv, z_t) - f(x, z_t))/t
      have h2 : (valueFunction f (x + t • v) - valueFunction f x) / t ≤
          (f (x + t • v) (zc t) - f x (zc t)) / t := by
        apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
        have hfx_le : f x (zc t) ≤ valueFunction f x :=
          le_ciSup ((isCompact_range hfx_cont).bddAbove) (zc t)
        rw [hzc_opt t ht_mem_X]; linarith
      -- slope g_{z_t} 0 t ≤ slope g_{z_t} 0 T
      have hgz : ConvexOn ℝ S (fun s ↦ f (x + s • v) (zc t)) :=
        (h_conv (zc t)).comp_affineMap ray
      have h_slt : slope (fun s ↦ f (x + s • v) (zc t)) 0 t =
          (f (x + t • v) (zc t) - f x (zc t)) / t := by
        simp [slope, sub_zero, div_eq_inv_mul]
      have h_slT : slope (fun s ↦ f (x + s • v) (zc t)) 0 T =
          (f (x + T • v) (zc t) - f x (zc t)) / T := by
        simp [slope, sub_zero, div_eq_inv_mul]
      have h3 := hgz.slope_mono h0_in_S ⟨ht_S, ne_of_gt ht_pos⟩
          ⟨hT_S, ne_of_gt (lt_trans ht_pos ht_lt)⟩ (le_of_lt ht_lt)
      rw [h_slt, h_slT] at h3
      linarith [h_slope_eq]
    -- Cluster point: d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
    have hfT_cont : Continuous (fun z : Z ↦ f (x + T • v) z) :=
      ContinuousOnProd.continuous_right h_cont _ hT_mem_X
    have h_comp : MapClusterPt ((f (x + T • v) z_bar - f x z_bar) / T)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (fun t ↦ (f (x + T • v) (zc t) - f x (zc t)) / T) :=
      ((hfT_cont.sub hfx_cont).div_const T).continuousAt.mapClusterPt hz_cluster
    rw [hz_bar_opt] at h_comp ⊢
    by_contra hlt; push Not at hlt
    obtain ⟨t, ht1, ht2⟩ :=
      ((h_comp.frequently (Iio_mem_nhds hlt)).and_eventually h_bound_ev).exists
    exact absurd ht2 (not_le.mpr ht1)
  -- ## Step 4: Combine
  obtain ⟨zb, hzb, db, hdb, hle⟩ := h_upper_bound
  -- From Step 2: db ≤ d_V, from upper bound: d_V ≤ db, so d_V = db
  have h_eq : d_V = db := le_antisymm hle (h_lower_bound zb hzb db hdb)
  -- `d_V` is the maximum: attained at `zb` (upper bound) and dominating every optimizer (Step 2)
  exact ⟨d_V, hV_dir, ⟨zb, hzb, h_eq ▸ hdb⟩, h_lower_bound⟩

omit [CompleteSpace E] in
/-- For `p ∈ SubderivWithinAt g X x` where `g` is convex on an open convex set `X`, the inner
product `⟪p, v⟫` is bounded above by the right directional derivative
`g'(x; v) = derivWithin (g ∘ ray) (Ioi 0) 0`. -/
lemma _root_.SubderivWithinAt.inner_le_rightDeriv (g : E → ℝ) (X : Set E) (x p v : E)
    (hX_open : IsOpen X) (hX_convex : Convex ℝ X) (hx : x ∈ X)
    (hg_convex : ConvexOn ℝ X g) (hp : p ∈ SubderivWithinAt g X x) :
    @inner ℝ E _ p v ≤
    derivWithin (fun t : ℝ ↦ g (x + t • v)) (Ioi 0) 0 := by
  have h_ray_cts : Continuous (fun t : ℝ ↦ x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  let ray : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t ↦ x + t • v
      linear := (LinearMap.lsmul ℝ E).flip v
      map_vadd' := by intro p q; simp [vadd_eq_add, add_smul]; abel }
  let S := (fun t : ℝ ↦ x + t • v) ⁻¹' X
  -- S is convex (preimage of convex X under the affine ray); kept explicit so that the
  -- `hX_convex` hypothesis remains load-bearing for this lemma's contract.
  have hS_convex : Convex ℝ S := hX_convex.affine_preimage ray
  have hS_open : IsOpen S := hX_open.preimage h_ray_cts
  have h0S : (0 : ℝ) ∈ S := by change x + (0 : ℝ) • v ∈ X; simp [hx]
  have h0_int : (0 : ℝ) ∈ interior S := by rwa [hS_open.interior_eq]
  -- g is convex on S, the preimage of X under the affine ray.
  have hg_ray_convex : ConvexOn ℝ S (fun t ↦ g (x + t • v)) :=
    ⟨hS_convex, (hg_convex.comp_affineMap ray).2⟩
  -- derivWithin = sInf of slopes; every slope ≥ ⟪p,v⟫
  rw [hg_ray_convex.rightDeriv_eq_sInf_slope_of_mem_interior h0_int]
  apply le_csInf
  · -- Nonempty: S open at 0, so contains some t > 0
    obtain ⟨ε, hε, hε_sub⟩ := Metric.isOpen_iff.mp hS_open 0 h0S
    exact ⟨slope (fun t ↦ g (x + t • v)) 0 (ε / 2),
      ⟨ε / 2, ⟨hε_sub (by simp [Metric.mem_ball, abs_of_pos hε]; linarith),
        half_pos hε⟩, rfl⟩⟩
  · rintro _ ⟨t, ⟨ht_mem, ht_pos⟩, rfl⟩
    rw [slope_def_field]; simp only [zero_smul, add_zero, sub_zero]
    rw [le_div_iff₀ ht_pos]
    have h1 := hp (x + t • v) ht_mem
    rw [add_sub_cancel_left, real_inner_smul_right] at h1; linarith

omit [CompleteSpace E] in
/-- For a convex function on an open set, the right directional derivative exists (as
`HasRightDirDerivAt`). -/
lemma ConvexOn.hasRightDirDeriv (g : E → ℝ) (X : Set E) (x v : E)
    (hX_open : IsOpen X) (hx : x ∈ X)
    (hg : ConvexOn ℝ X g) :
    ∃ d : ℝ, HasRightDirDerivAt g x v d := by
  let ray : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t ↦ x + t • v
      linear := (LinearMap.lsmul ℝ E).flip v
      map_vadd' := by intro p q; simp [vadd_eq_add, add_smul]; abel }
  let S := (fun t : ℝ ↦ x + t • v) ⁻¹' X
  have hS_open : IsOpen S := hX_open.preimage
    (continuous_const.add (continuous_id.smul continuous_const))
  have h0_int : (0 : ℝ) ∈ interior S := by
    rw [hS_open.interior_eq]; change x + (0 : ℝ) • v ∈ X; simp [hx]
  have hg_ray : ConvexOn ℝ S (fun t ↦ g (x + t • v)) := hg.comp_affineMap ray
  have hg_deriv := hg_ray.hasDerivWithinAt_rightDeriv_of_mem_interior h0_int
  rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)] at hg_deriv
  set d := derivWithin (fun (t : ℝ) ↦ g (x + t • v)) (Ioi 0) (0 : ℝ) with hd_def
  refine ⟨d, ?_⟩
  rw [HasRightDirDerivAt]
  have key : (fun t : ℝ ↦ (g (x + t • v) - g x) / t) = slope (fun t ↦ g (x + t • v)) 0 := by
    ext t; simp [slope, sub_zero, div_eq_inv_mul]
  rw [key]; exact hg_deriv

omit [CompleteSpace E] [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z] in
/-- A right directional derivative determines the one-sided `derivWithin` of the ray restriction:
If `HasRightDirDerivAt h x v d` then `derivWithin (t ↦ h (x + t • v)) (Ioi 0) 0 = d`. -/
private lemma HasRightDirDerivAt.derivWithin_eq {h : E → ℝ} {x v : E} {d : ℝ}
    (hd : HasRightDirDerivAt h x v d) :
    derivWithin (fun t : ℝ ↦ h (x + t • v)) (Ioi 0) 0 = d := by
  have h_deriv : HasDerivWithinAt (fun t : ℝ ↦ h (x + t • v)) d (Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)]
    rw [HasRightDirDerivAt] at hd
    have key : (fun t : ℝ ↦ (h (x + t • v) - h x) / t) = slope (fun t ↦ h (x + t • v)) 0 := by
      ext t; simp [slope, sub_zero, div_eq_inv_mul]
    rwa [key] at hd
  exact h_deriv.derivWithin (uniqueDiffWithinAt_Ioi 0)

/-! #### Support function theorem for convex subdifferentials -/

/-- Support function theorem for convex subdifferentials: For a convex function `g` on an open
convex set `X` in a Hilbert space, there exists a subgradient `q ∈ ∂g(x)` such that
`⟪q, v⟫ = g'(x; v)`. -/
lemma ConvexOn.exists_subderiv_eq_rightDeriv (g : E → ℝ) (X : Set E) (x v : E)
    (hX_open : IsOpen X) (hx : x ∈ X)
    (hg_convex : ConvexOn ℝ X g) (hg_cont : ContinuousOn g X) :
    ∃ q : E, q ∈ SubderivWithinAt g X x ∧
    @inner ℝ E _ q v = derivWithin (fun t : ℝ ↦ g (x + t • v)) (Ioi 0) 0 := by
  -- ## Step 1: Setup N, d, ray convexity, interior membership
  set N : E → ℝ := fun w ↦ derivWithin (fun t : ℝ ↦ g (x + t • w)) (Ioi 0) 0 with hN_def
  set d := N v with hd_def
  have h_ray_convex : ∀ w : E, ConvexOn ℝ ((fun t : ℝ ↦ x + t • w) ⁻¹' X)
      (fun t ↦ g (x + t • w)) := by
    intro w
    let ray : ℝ →ᵃ[ℝ] E :=
      { toFun := fun t ↦ x + t • w
        linear := (LinearMap.lsmul ℝ E).flip w
        map_vadd' := by intro p q; simp [vadd_eq_add, add_smul]; abel }
    exact hg_convex.comp_affineMap ray
  have h_open_pre : ∀ w : E, IsOpen ((fun t : ℝ ↦ x + t • w) ⁻¹' X) := by
    intro w; exact hX_open.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0_mem : ∀ w : E, (0 : ℝ) ∈ (fun t : ℝ ↦ x + t • w) ⁻¹' X := by
    intro w; change x + (0 : ℝ) • w ∈ X; simp [hx]
  have h0_int : ∀ w : E, (0 : ℝ) ∈ interior ((fun t : ℝ ↦ x + t • w) ⁻¹' X) := by
    intro w; rw [(h_open_pre w).interior_eq]; exact h0_mem w
  -- ## Step 2: N(y-x) ≤ g(y) - g(x) for all y ∈ X
  -- (subgradient inequality: rightDeriv ≤ slope at t=1)
  have hN_subdiff : ∀ y ∈ X, N (y - x) ≤ g y - g x := by
    intro y hy
    set w := y - x
    have h1_S : (1 : ℝ) ∈ (fun t : ℝ ↦ x + t • w) ⁻¹' X := by
      simp [w, hy]
    have h_le := (h_ray_convex w).rightDeriv_le_slope_of_mem_interior
      (h0_int w) h1_S (by norm_num : (0:ℝ) < 1)
    simp [slope, w] at h_le; linarith
  -- ## Step 3: N is bounded: ∃ L, ∀ w, N w ≤ L * ‖w‖
  -- (Lipschitz of g on a small ball, then rightDeriv ≤ slope ≤ Lip·‖w‖)
  have hN_le : ∃ L : ℝ, 0 ≤ L ∧ ∀ w : E, N w ≤ L * ‖w‖ := by
    obtain ⟨r₀, hr₀, hr₀_sub⟩ := Metric.isOpen_iff.mp hX_open x hx
    have hg_cts_at : ContinuousAt g x := (hg_cont x hx).continuousAt (hX_open.mem_nhds hx)
    obtain ⟨δ, hδ, hδ_bound⟩ := Metric.continuousAt_iff.mp hg_cts_at 1 one_pos
    set r := min r₀ δ with hr_def
    have hr_pos : 0 < r := by positivity
    set M := |g x| + 1
    have h_abs_le : ∀ a, dist a x < r → |g a| ≤ M := by
      intro a ha
      have had : dist a x < δ := lt_of_lt_of_le ha (min_le_right _ _)
      have h1 := hδ_bound had; rw [Real.dist_eq] at h1
      calc |g a| = |g a| - |g x| + |g x| := by ring
        _ ≤ |g a - g x| + |g x| := by linarith [abs_sub_abs_le_abs_sub (g a) (g x)]
        _ ≤ |g x| + 1 := by linarith
    set ε := r / 2
    have hε_pos : 0 < ε := by positivity
    have hg_ball : ConvexOn ℝ (Metric.ball x r) g :=
      hg_convex.subset (fun y hy ↦ hr₀_sub (lt_of_lt_of_le (Metric.mem_ball.mp hy)
        (min_le_left _ _))) (convex_ball x r)
    have hK := hg_ball.lipschitzOnWith_of_abs_le hε_pos
      (fun a ha ↦ h_abs_le a (Metric.mem_ball.mp ha))
    set K := (2 * M / ε).toNNReal
    refine ⟨K, K.coe_nonneg, fun w ↦ ?_⟩
    by_cases hw : w = 0
    · subst hw; simp only [smul_zero, add_zero, norm_zero, mul_zero, hN_def]
      have : (fun (_ : ℝ) ↦ g x) = Function.const ℝ (g x) := rfl
      rw [this, derivWithin_const]; simp
    · set t₀ := ε / (2 * ‖w‖)
      have h_nw : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have ht₀_pos : 0 < t₀ := by positivity
      have ht₀_mem : x + t₀ • w ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (le_of_lt ht₀_pos)]
        have : t₀ * ‖w‖ = ε / 2 := by change ε / (2 * ‖w‖) * ‖w‖ = ε / 2; field_simp
        linarith
      -- ball x ε ⊆ ball x (r - ε) since ε = r/2
      have hε_eq : ε = r - ε := by ring
      have ht₀_in_lip : x + t₀ • w ∈ Metric.ball x (r - ε) := by rwa [← hε_eq]
      have hx_in_lip : x ∈ Metric.ball x (r - ε) := by
        rw [← hε_eq]
        exact Metric.mem_ball_self hε_pos
      have ht₀_S : t₀ ∈ (fun t : ℝ ↦ x + t • w) ⁻¹' X :=
        hr₀_sub (Metric.ball_subset_ball (by linarith [min_le_left r₀ δ] : ε ≤ r₀) ht₀_mem)
      have h_le := (h_ray_convex w).rightDeriv_le_slope_of_mem_interior (h0_int w) ht₀_S ht₀_pos
      have h_slope_eq : slope (fun t ↦ g (x + t • w)) 0 t₀ =
          (g (x + t₀ • w) - g x) / t₀ := by
        simp [slope, sub_zero, div_eq_inv_mul, zero_smul]
      rw [h_slope_eq] at h_le
      have h_lip := hK.dist_le_mul x hx_in_lip (x + t₀ • w) ht₀_in_lip
      have h_dist_simp : dist x (x + t₀ • w) = t₀ * ‖w‖ := by
        rw [dist_eq_norm, show x - (x + t₀ • w) = -(t₀ • w) by abel, norm_neg, norm_smul,
            Real.norm_of_nonneg (le_of_lt ht₀_pos)]
      rw [h_dist_simp] at h_lip
      have h_abs : g (x + t₀ • w) - g x ≤ ↑K * (t₀ * ‖w‖) := by
        have : |g x - g (x + t₀ • w)| ≤ ↑K * (t₀ * ‖w‖) := by rwa [← Real.dist_eq]
        linarith [le_abs_self (g (x + t₀ • w) - g x), abs_sub_comm (g (x + t₀ • w)) (g x)]
      have : (g (x + t₀ • w) - g x) / t₀ ≤ ↑K * ‖w‖ := by
        rw [div_le_iff₀ ht₀_pos]; linarith [mul_comm (↑K * ‖w‖) t₀, mul_assoc (↑K : ℝ) t₀ ‖w‖]
      exact le_trans h_le this
  obtain ⟨L, hL_pos, hN_bound⟩ := hN_le
  -- ## Step 4: N(c•w) = c * N(w) for c > 0
  have hN_hom : ∀ (c : ℝ), 0 < c → ∀ (w : E), N (c • w) = c * N w := by
    intro c hc w
    change derivWithin (fun t : ℝ ↦ g (x + t • (c • w))) (Ioi 0) 0 =
      c * derivWithin (fun t : ℝ ↦ g (x + t • w)) (Ioi 0) 0
    set S_w := (fun t : ℝ ↦ x + t • w) ⁻¹' X
    have h_deriv_w := (h_ray_convex w).hasDerivWithinAt_rightDeriv_of_mem_interior (h0_int w)
    have h_map : MapsTo (· * c) (Ioi 0) (Ioi 0) := fun t ht ↦ mul_pos (mem_Ioi.mp ht) hc
    have h_deriv_at_0c : HasDerivWithinAt (fun t ↦ g (x + t • w))
        (derivWithin (fun t : ℝ ↦ g (x + t • w)) (Ioi 0) 0) (Ioi 0) (0 * c) := by
      rw [zero_mul]; exact h_deriv_w
    have h_comp := h_deriv_at_0c.scomp (0 : ℝ)
      (hasDerivAt_mul_const c).hasDerivWithinAt h_map
    have h_fun_eq : (fun t : ℝ ↦ g (x + t • (c • w))) =
        ((fun t ↦ g (x + t • w)) ∘ (· * c)) := by
      ext t; simp [Function.comp, smul_smul]
    rw [h_fun_eq, show c * derivWithin (fun t : ℝ ↦ g (x + t • w)) (Ioi 0) 0 =
        c • derivWithin (fun t : ℝ ↦ g (x + t • w)) (Ioi 0) 0 from
        (smul_eq_mul _ _).symm]
    exact h_comp.derivWithin (uniqueDiffWithinAt_Ioi 0)
  have hN0 : N 0 = 0 := by
    change derivWithin (fun t : ℝ ↦ g (x + t • (0 : E))) (Ioi 0) 0 = 0
    have : (fun t : ℝ ↦ g (x + t • (0 : E))) = (fun _ ↦ g x) := by ext t; simp
    rw [this, show (fun (_ : ℝ) ↦ g x) = Function.const ℝ (g x) from rfl, derivWithin_const]; simp
  /- ## Step 5: N(w1+w2) ≤ N(w1) + N(w2)
     For each t > 0 (small enough): g(x+t(w1+w2)) ≤ (1/2)g(x+2tw1) + (1/2)g(x+2tw2)
     So the slope of the sum ray ≤ sum of slopes of individual rays at 2t.
     Taking t → 0+: N(w1+w2) ≤ N(w1) + N(w2). -/
  have hN_sub : ∀ (w1 w2 : E), N (w1 + w2) ≤ N w1 + N w2 := by
    intro w1 w2
    -- Use: N(w1+w2) ≤ slope(0, t) for the (w1+w2) ray (rightDeriv ≤ slope, convexity)
    -- and slope(0, t) ≤ slope_w1(0, 2t) + slope_w2(0, 2t) (midpoint convexity)
    -- Then take limit as t → 0+.
    -- Show: N(w1+w2) ≤ sum of slopes at 2t (eventually), slopes → N(w1)+N(w2)
    letI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
    apply ge_of_tendsto (x := 𝓝[>] (0 : ℝ))
    · -- Tendsto of RHS: slopes at 2t converge to N(w1) + N(w2)
      have h_dw1 := (h_ray_convex w1).hasDerivWithinAt_rightDeriv_of_mem_interior (h0_int w1)
      have h_dw2 := (h_ray_convex w2).hasDerivWithinAt_rightDeriv_of_mem_interior (h0_int w2)
      rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)] at h_dw1 h_dw2
      have h2_tends : Tendsto (fun t : ℝ ↦ 2 * t) (nhdsWithin (0 : ℝ) (Ioi 0))
          (nhdsWithin (0 : ℝ) (Ioi 0)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
          have : ContinuousAt (fun t : ℝ ↦ 2 * t) 0 := by fun_prop
          simpa using this.tendsto
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mul_pos two_pos (mem_Ioi.mp ht)
      exact (h_dw1.comp h2_tends).add (h_dw2.comp h2_tends)
    · -- Eventually: N(w1+w2) ≤ slope_w1(0, 2t) + slope_w2(0, 2t)
      have h_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          t ∈ (fun s : ℝ ↦ x + s • (w1+w2)) ⁻¹' X ∧
          2 * t ∈ (fun s : ℝ ↦ x + s • w1) ⁻¹' X ∧
          2 * t ∈ (fun s : ℝ ↦ x + s • w2) ⁻¹' X := by
        have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ (fun s : ℝ ↦ x + s • (w1+w2)) ⁻¹' X :=
          nhdsWithin_le_nhds ((h_open_pre (w1+w2)).mem_nhds (h0_mem (w1+w2)))
        -- For each `w`, `2t` eventually lands in the ray-preimage of `X` as `t → 0⁺`.
        have h_two : ∀ w : E, ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
            2 * t ∈ (fun s : ℝ ↦ x + s • w) ⁻¹' X := by
          intro w
          have h2t : Tendsto (2 * · : ℝ → ℝ) (nhds 0) (nhds 0) := by
            have : ContinuousAt (fun t : ℝ ↦ 2 * t) 0 := by fun_prop
            simpa using this.tendsto
          exact (h2t.eventually ((h_open_pre w).mem_nhds (h0_mem w))).filter_mono
            nhdsWithin_le_nhds
        exact h1.and ((h_two w1).and (h_two w2))
      filter_upwards [h_ev, self_mem_nhdsWithin (s := Ioi 0)] with t ⟨ht_sum, ht_w1, ht_w2⟩ ht_pos
      rw [mem_Ioi] at ht_pos
      -- N(w1+w2) ≤ slope of sum ray at t
      have h_le_slope := (h_ray_convex (w1+w2)).rightDeriv_le_slope_of_mem_interior
        (h0_int (w1+w2)) ht_sum ht_pos
      have h_slope_sum : slope (fun s ↦ g (x + s • (w1 + w2))) 0 t =
          (g (x + t • (w1 + w2)) - g x) / t := by
        simp [slope, sub_zero, div_eq_inv_mul, zero_smul]
      rw [h_slope_sum] at h_le_slope
      -- Midpoint convexity: x + t(w1+w2) = (1/2)(x+2tw1) + (1/2)(x+2tw2)
      have h_mid : x + t • (w1 + w2) = (1/2 : ℝ) • (x + (2*t) • w1) +
          (1/2 : ℝ) • (x + (2*t) • w2) := by
        simp [smul_add, smul_smul]; module
      have h_conv_ineq : g (x + t • (w1 + w2)) ≤
          (1/2) * g (x + (2*t) • w1) + (1/2) * g (x + (2*t) • w2) := by
        rw [h_mid]
        have h_w1_X : x + (2*t) • w1 ∈ X := ht_w1
        have h_w2_X : x + (2*t) • w2 ∈ X := ht_w2
        exact hg_convex.2 h_w1_X h_w2_X (by norm_num) (by norm_num) (by norm_num)
      set a := g (x + (2*t) • w1) with ha_def
      set b := g (x + (2*t) • w2) with hb_def
      set c := g x with hc_def
      have h_slope_w1 : slope (fun s ↦ g (x + s • w1)) 0 (2*t) = (a - c) / (2*t) := by
        simp [slope, sub_zero, div_eq_inv_mul, zero_smul, ha_def, hc_def]
      have h_slope_w2 : slope (fun s ↦ g (x + s • w2)) 0 (2*t) = (b - c) / (2*t) := by
        simp [slope, sub_zero, div_eq_inv_mul, zero_smul, hb_def, hc_def]
      simp only [Function.comp] at *
      rw [h_slope_w1, h_slope_w2]
      have h2t_pos : 0 < 2 * t := by positivity
      calc N (w1+w2) ≤ (g (x + t • (w1 + w2)) - c) / t := h_le_slope
        _ ≤ ((1/2) * a + (1/2) * b - c) / t := by
            apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos); linarith [h_conv_ineq]
        _ = (a - c) / (2*t) + (b - c) / (2*t) := by field_simp; ring
  -- ## Step 6: case split on v
  by_cases hv : v = 0
  · -- v = 0: derivWithin of constant = 0, and ⟪q, 0⟫ = 0 for any q in subdiff
    subst hv
    -- `derivWithin (t ↦ g (x + t • 0)) (Ioi 0) 0 = 0` is exactly `N 0 = 0`.
    have hd_zero : derivWithin (fun t : ℝ ↦ g (x + t • (0 : E))) (Ioi 0) 0 = 0 := hN0
    -- Use Hahn-Banach with the zero PMap on ⊥ to get a subgradient
    set φ₀ : E →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
    have hφ₀_dom : ∀ w : ↥φ₀.domain, (φ₀ w : ℝ) ≤ N (w : E) := by
      intro ⟨w, hw⟩
      have := (Submodule.mem_bot ℝ).mp hw; subst this
      simp only [φ₀]; change (0 : ℝ) ≤ N 0; rw [hN0]
    obtain ⟨ψ, _, hψ_le⟩ := exists_extension_of_le_sublinear φ₀ N hN_hom hN_sub hφ₀_dom
    have hψ_bound : ∀ w, ‖ψ w‖ ≤ L * ‖w‖ := by
      intro w; rw [Real.norm_eq_abs, abs_le]; constructor
      · have h1 := hψ_le (-w); rw [map_neg] at h1
        have h2 := hN_bound (-w); rw [norm_neg] at h2; linarith
      · linarith [hψ_le w, hN_bound w]
    set ψ_clm := ψ.mkContinuous L hψ_bound
    set q := (toDual ℝ E).symm ψ_clm
    have hq_eq : ∀ w, @inner ℝ E _ q w = ψ w := by
      intro w
      change (toDual ℝ E) ((toDual ℝ E).symm ψ_clm) w = ψ w
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact LinearMap.mkContinuous_apply ψ L hψ_bound w
    refine ⟨q, ?_, ?_⟩
    · intro y hy; rw [hq_eq]; linarith [hψ_le (y - x), hN_subdiff y hy]
    · rw [inner_zero_right, hd_zero]
  · -- v ≠ 0: Use Hahn-Banach with mkSpanSingleton
    -- ### Step 6b: α*d ≤ N(α•v) for all α
    have hαd_le : ∀ α : ℝ, α * d ≤ N (α • v) := by
      intro α
      rcases le_or_gt 0 α with hα | hα
      · rcases eq_or_lt_of_le hα with rfl | hα_pos
        · -- α = 0: 0 * d ≤ N(0 • v) = N(0) = 0
          simp only [zero_mul, zero_smul]; rw [hN0]
        · rw [hN_hom α hα_pos v, hd_def]
      · have hα_neg : 0 < -α := neg_pos.mpr hα
        have h1 : N ((-α) • v) = (-α) * N v := hN_hom (-α) hα_neg v
        have h2 : N (α • v + (-α) • v) ≤ N (α • v) + N ((-α) • v) := hN_sub (α • v) ((-α) • v)
        have h3 : α • v + (-α) • v = 0 := by simp
        rw [h3] at h2
        rw [hN0, h1] at h2; linarith
    -- ## Step 7: Hahn-Banach + Riesz
    set φ : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton v d hv
    have hφ_dom : ∀ w : ↥φ.domain, (φ w : ℝ) ≤ N (w : E) := by
      intro ⟨w, hw⟩
      have hw' : w ∈ Submodule.span ℝ {v} := hw
      rw [Submodule.mem_span_singleton] at hw'; obtain ⟨α, rfl⟩ := hw'
      have : (φ ⟨α • v, hw⟩ : ℝ) = α • d := by
        simp only [φ, LinearPMap.mkSpanSingleton, LinearPMap.mkSpanSingleton'_apply]
        rfl
      rw [this, smul_eq_mul]; exact hαd_le α
    obtain ⟨ψ, hψ_ext, hψ_le⟩ := exists_extension_of_le_sublinear φ N hN_hom hN_sub hφ_dom
    have hψ_bound : ∀ w, ‖ψ w‖ ≤ L * ‖w‖ := by
      intro w; rw [Real.norm_eq_abs, abs_le]; constructor
      · have h1 := hψ_le (-w); rw [map_neg] at h1
        have h2 := hN_bound (-w); rw [norm_neg] at h2; linarith
      · linarith [hψ_le w, hN_bound w]
    set ψ_clm := ψ.mkContinuous L hψ_bound
    set q := (toDual ℝ E).symm ψ_clm
    have hq_eq : ∀ w, @inner ℝ E _ q w = ψ w := by
      intro w
      rw [toDual_symm_apply]
      exact LinearMap.mkContinuous_apply ψ L hψ_bound w
    refine ⟨q, ?_, ?_⟩
    · intro y hy; rw [hq_eq]; linarith [hψ_le (y - x), hN_subdiff y hy]
    · rw [hq_eq]
      have hv_mem : v ∈ φ.domain := Submodule.mem_span_singleton_self v
      have h := hψ_ext ⟨v, hv_mem⟩
      rw [h, LinearPMap.mkSpanSingleton_apply]

/-! ### Part (iii): Subdifferential Formula -/

/-- **Danskin Part (iii).** The `SubderivWithinAt` of the value function equals the closed convex
hull of the union of `SubderivWithinAt`s at optimizers:
`∂V(x) = cl(conv(⋃_{z ∈ Z*(x)} ∂_x f(x, z)))`. -/
theorem subderivWithinAt_valueFunction (f : E → Z → ℝ) (X : Set E)
    (hX_open : IsOpen X) (hX_convex : Convex ℝ X)
    (h_cont : ContinuousOnProd f X) (h_conv : ConvexOnFiber f X)
    (x : E) (hx : x ∈ X) :
    SubderivWithinAt (valueFunction f) X x =
      closure (convexHull ℝ (⋃ z ∈ argmax_iSup f x,
        SubderivWithinAt (fun y ↦ f y z) X x)) := by
  have hfx_cont := ContinuousOnProd.continuous_right h_cont x hx
  apply le_antisymm
  · -- (⊆): ∂V(x) ⊆ cl(conv(⋃ ∂f))
    -- Strategy: by_contra + Hahn-Banach strict separation.
    -- If p ∈ ∂V(x) but p ∉ C := cl(conv(⋃ ∂f)), separate p from C.
    -- Then derive ⟪p,v⟫ ≤ V'(x;v) ≤ u < ⟪v,p⟫, contradiction.
    intro p hp
    by_contra hp_not
    -- Hahn-Banach: separate p from the closed convex set C
    obtain ⟨ℓ, u, hℓC, hℓp⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _).closure isClosed_closure hp_not
    -- Convert to inner product via Riesz representation
    set v := (InnerProductSpace.toDual ℝ E).symm ℓ
    have hv_C : ∀ q ∈ closure (convexHull ℝ (⋃ z ∈ argmax_iSup f x,
        SubderivWithinAt (fun y ↦ f y z) X x)), @inner ℝ E _ v q < u := fun q hq => by
      rw [InnerProductSpace.toDual_symm_apply]; exact hℓC q hq
    have hv_p : u < @inner ℝ E _ v p := by
      rw [InnerProductSpace.toDual_symm_apply]; exact hℓp
    -- Every subgradient at an optimizer is in C, hence has ⟪v, q⟫ < u
    have h_in_C : ∀ z ∈ argmax_iSup f x,
        SubderivWithinAt (fun y ↦ f y z) X x ⊆
          closure (convexHull ℝ (⋃ z ∈ argmax_iSup f x,
            SubderivWithinAt (fun y ↦ f y z) X x)) :=
      fun z hz _ hq => subset_closure (subset_convexHull ℝ _ (Set.mem_biUnion hz hq))
    -- V is convex on X (from convexOn_valueFunction)
    have hV_convex : ConvexOn ℝ X (valueFunction f) :=
      convexOn_valueFunction hX_convex h_conv fun y hy ↦
        (isCompact_range (ContinuousOnProd.continuous_right h_cont y hy)).bddAbove
    -- Key established fact: ⟪p, v⟫ ≤ V'(x; v)
    have h_inner_le := SubderivWithinAt.inner_le_rightDeriv (valueFunction f) X x p v
      hX_open hX_convex hx hV_convex hp
    have h_deriv_le_u :
        derivWithin (fun t : ℝ ↦ valueFunction f (x + t • v)) (Ioi 0) 0 ≤ u := by
      -- Step 1: Directional derivatives exist at all optimizers (convexity + open domain)
      have h_dir : ∀ z ∈ argmax_iSup f x,
          ∃ d : ℝ, HasRightDirDerivAt (fun w ↦ f w z) x v d :=
        fun z _hz ↦ ConvexOn.hasRightDirDeriv _ X x v hX_open hx (h_conv z)
      -- Step 2: Apply Part (ii) to get z_max ∈ Z*(x) with d_V = f'(x, z_max; v); the maximality
      -- clause is not needed here (we only use that the maximum is attained at some optimizer).
      obtain ⟨d, hd_V, ⟨z_max, hz_max, hd_fiber⟩, _⟩ :=
        hasRightDirDeriv_iSup f X hX_open hX_convex h_cont h_conv x v hx h_dir
      -- Step 3: d = derivWithin (V ∘ ray) (Ioi 0) 0 (from HasRightDirDerivAt)
      rw [hd_V.derivWithin_eq]
      -- Step 4: f(·, z_max) is continuous on X (from joint continuity)
      have hfz_cont : ContinuousOn (fun y ↦ f y z_max) X := by
        exact h_cont.comp (continuousOn_id.prodMk continuousOn_const)
          (fun y hy ↦ ⟨hy, trivial⟩)
      -- Step 5: d = derivWithin of f(·, z_max) fiber (same argument)
      have hd_fiber_eq : derivWithin (fun t : ℝ ↦ f (x + t • v) z_max) (Ioi 0) 0 = d :=
        hd_fiber.derivWithin_eq
      -- Step 6: Support function theorem gives q ∈ ∂f(·, z_max)(x) with ⟪q, v⟫ = d
      obtain ⟨q, hq_subdiff, hq_inner⟩ := ConvexOn.exists_subderiv_eq_rightDeriv
        (fun y ↦ f y z_max) X x v hX_open hx (h_conv z_max) hfz_cont
      rw [hd_fiber_eq] at hq_inner
      -- Step 7: q ∈ C (via h_in_C), so ⟪v, q⟫ < u, giving d = ⟪q, v⟫ < u
      have hq_in_C := h_in_C z_max hz_max hq_subdiff
      have := hv_C q hq_in_C
      -- ⟪v, q⟫ < u and d = ⟪q, v⟫ = ⟪v, q⟫ (by real_inner_comm)
      rw [← hq_inner, real_inner_comm]; linarith
    linarith [real_inner_comm v p]
  · -- (⊇): cl(conv(⋃ ∂f)) ⊆ ∂V(x)
    -- Step 1: show ⋃_{z∈Z*(x)} ∂_x f(·,z)(x) ⊆ ∂V(x)
    -- Step 2: ∂V(x) is convex → convexHull ⊆ ∂V(x)
    -- Step 3: ∂V(x) is closed → closure ⊆ ∂V(x)
    apply closure_minimal
    · apply convexHull_min
      · intro q hq
        simp only [Set.mem_iUnion] at hq
        obtain ⟨z, hz_opt, hq_sub⟩ := hq
        -- q ∈ ∂_x f(·, z)(x) and z ∈ Z*(x), need: q ∈ ∂V(x)
        intro y hy
        -- V(x) + ⟪q, y-x⟫ = f(x,z) + ⟪q, y-x⟫ ≤ f(y,z) ≤ V(y)
        calc valueFunction f x + @inner ℝ E _ q (y - x)
            = f x z + @inner ℝ E _ q (y - x) := by rw [← hz_opt]
          _ ≤ f y z := hq_sub y hy
          _ ≤ valueFunction f y := le_ciSup
              (isCompact_range
                (ContinuousOnProd.continuous_right h_cont y hy)).bddAbove z
      · exact SubderivWithinAt.convex x hx
    · exact SubderivWithinAt.isClosed x

/-! ### Part (iv): The Smooth Case (Gradient Recovery) -/
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
open Asymptotics in
/-- Squeeze lemma for `IsLittleO` of `ℝ`-valued functions: If `g ≤ f ≤ h` eventually and both `g`
and `h` are `o(‖y - x₀‖)`, then so is `f`. -/
lemma IsLittleO.of_squeeze {f g h : E → ℝ} {x₀ : E}
    (hfg : ∀ᶠ y in nhds x₀, g y ≤ f y)
    (hfh : ∀ᶠ y in nhds x₀, f y ≤ h y)
    (hg : g =o[nhds x₀] fun y ↦ y - x₀) (hh : h =o[nhds x₀] fun y ↦ y - x₀) :
    f =o[nhds x₀] fun y ↦ y - x₀ := by
  rw [Asymptotics.isLittleO_iff] at hg hh ⊢
  intro c hc
  have hc2 := half_pos hc
  filter_upwards [hfg, hfh, hg hc2, hh hc2] with y hgf hfh hgk hhk
  simp only [Real.norm_eq_abs] at *
  rw [abs_le]
  constructor
  · have := (abs_le.mp hgk).1
    linarith [mul_le_mul_of_nonneg_right (half_le_self (le_of_lt hc)) (norm_nonneg (y - x₀))]
  · have := (abs_le.mp hhk).2
    linarith [mul_le_mul_of_nonneg_right (half_le_self (le_of_lt hc)) (norm_nonneg (y - x₀))]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Berge upper hemicontinuity (cluster-point form).**  Every cluster point of an optimizer
selection at nearby points lies in `argmax_iSup f x`: If `(z_y)` selects an optimizer at each `y`
in a neighborhood of `x` and `z_bar` is any cluster point of `z_y` along `nhds x`, then
`f x z_bar = valueFunction f x`.

This is the uniqueness-free core of `tendsto_argmax_of_unique`. -/
lemma argmax_iSup_clusterPt_mem
    (f : E → Z → ℝ) (X : Set E) (h_cont : ContinuousOnProd f X) (hX_open : IsOpen X)
    (x : E) (hx : x ∈ X)
    (z_y : E → Z) (hz_y : ∀ᶠ y in nhds x, y ∈ X ∧ f y (z_y y) = valueFunction f y)
    {z_bar : Z} (h_clust : MapClusterPt z_bar (nhds x) z_y) :
    z_bar ∈ argmax_iSup f x := by
  -- Reduce to f x z_bar = valueFunction f x.
  change f x z_bar = valueFunction f x
  apply le_antisymm
  · exact le_ciSup (isCompact_range
      (ContinuousOnProd.continuous_right h_cont x hx)).bddAbove z_bar
  · -- Need: V(x) ≤ f(x, z_bar). Strategy: f(y, z_y y) clusters at f(x, z_bar) by joint
    -- continuity, f(y, z_star) → V(x) by continuity, and f(y, z_star) ≤ f(y, z_y y) = V(y).
    -- A cluster point of a sequence that is eventually ≥ a convergent sequence is ≥ its limit.
    -- (y, z_y y) clusters at (x, z_bar) in E × Z.
    have h_pair : MapClusterPt (x, z_bar) (nhds x) (fun y => (y, z_y y)) := by
      rw [mapClusterPt_iff_frequently]
      intro s hs
      rw [nhds_prod_eq] at hs
      obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hs
      exact ((h_clust.frequently hv).and_eventually hu).mono
        fun y ⟨hzv, hyu⟩ => huv ⟨hyu, hzv⟩
    -- Joint continuity at (x, z_bar) gives f(y, z_y y) clusters at f(x, z_bar).
    have h_cont_at : ContinuousAt (fun p : E × Z => f p.1 p.2) (x, z_bar) :=
      (h_cont (x, z_bar) ⟨hx, mem_univ z_bar⟩).continuousAt
        ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_bar⟩)
    have h_fcluster : MapClusterPt (f x z_bar) (nhds x) (fun y => f y (z_y y)) :=
      h_cont_at.mapClusterPt h_pair
    -- Pick any maximizer z_star at x (nonempty by compactness + continuity).
    obtain ⟨z_star, hz_star_eq⟩ : (argmax_iSup f x).Nonempty :=
      argmax_iSup_nonempty f (ContinuousOnProd.continuous_right h_cont x hx)
    -- f(y, z_star) → V(x) as y → x (by continuity of f at (x, z_star)).
    have h_cont_at_star : ContinuousAt (fun p : E × Z => f p.1 p.2) (x, z_star) :=
      (h_cont (x, z_star) ⟨hx, mem_univ z_star⟩).continuousAt
        ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_star⟩)
    have h_fz_tends : Tendsto (fun y => f y z_star) (nhds x) (nhds (valueFunction f x)) := by
      rw [← hz_star_eq]
      exact h_cont_at_star.tendsto.comp
        (Tendsto.prodMk_nhds tendsto_id tendsto_const_nhds)
    -- f(y, z_star) ≤ f(y, z_y y) = V(y) eventually.
    have h_le : ∀ᶠ y in nhds x, f y z_star ≤ f y (z_y y) := by
      filter_upwards [hz_y] with y ⟨hy_mem, hy_eq⟩
      rw [hy_eq]
      exact le_ciSup (isCompact_range
        (ContinuousOnProd.continuous_right h_cont y hy_mem)).bddAbove z_star
    -- Conclude by contradiction: if f(x,z_bar) < V(x), then f(y,z_y y) is eventually above
    -- the midpoint (since f(y,z_star) → V(x)) but frequently below it (since cluster at f(x,z_bar))
    by_contra h
    push Not at h
    have hma : (valueFunction f x + f x z_bar) / 2 < valueFunction f x := by linarith
    have hmb : f x z_bar < (valueFunction f x + f x z_bar) / 2 := by linarith
    exact (h_fcluster.frequently (Iio_mem_nhds hmb))
      (by filter_upwards [h_le, h_fz_tends.eventually (Ioi_mem_nhds hma)]
          with y hfg hfm; linarith)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- **Berge upper hemicontinuity, gradient form.**  Suppose all optimizers `z ∈ argmax_iSup f x`
share a common gradient `g = grad_f x z` of the inner objective at `x`.  Then the gradient
`grad_f x (z_y y)` of any optimizer-selection at nearby points tends to `g` as `y → x`.

This relaxes the uniqueness of the optimizer in `tendsto_argmax_of_unique` to uniqueness of its
gradient image. -/
lemma tendsto_grad_argmax_of_const_grad
    (f : E → Z → ℝ) (grad_f : E → Z → E) (X : Set E)
    (h_cont : ContinuousOnProd f X) (hX_open : IsOpen X)
    (x : E) (hx : x ∈ X) (g : E)
    (h_grad_cont : ContinuousOn (fun p : E × Z ↦ grad_f p.1 p.2) (X ×ˢ univ))
    (h_grad_const : ∀ z ∈ argmax_iSup f x, grad_f x z = g)
    (z_y : E → Z) (hz_y : ∀ᶠ y in nhds x, y ∈ X ∧ f y (z_y y) = valueFunction f y) :
    Tendsto (fun y => grad_f x (z_y y)) (nhds x) (nhds g) := by
  -- Continuity of `grad_f x : Z → E` (restriction of jointly continuous `grad_f` at `x`).
  have h_grad_x_cont : Continuous (fun z => grad_f x z) := by
    rw [show (fun z ↦ grad_f x z) = (fun p : E × Z ↦ grad_f p.1 p.2) ∘ (fun z ↦ (x, z)) from rfl]
    exact ContinuousOn.comp_continuous h_grad_cont
      (continuous_prodMk.mpr ⟨continuous_const, continuous_id'⟩)
      (fun z ↦ ⟨hx, mem_univ z⟩)
  -- Image of compact `Z` under `grad_f x` is compact in `E`; provides a compactness cage.
  have h_compact : IsCompact (range (fun z => grad_f x z)) :=
    isCompact_range h_grad_x_cont
  apply h_compact.le_nhds_of_unique_clusterPt
  · -- `range (grad_f x) ∈ Filter.map (grad_f x ∘ z_y) (nhds x)` since the image is in `range`.
    rw [Filter.mem_map]
    exact Filter.univ_mem' (fun y => mem_range_self _)
  · -- For every cluster point `p` of the pushforward in `range (grad_f x)`, we show `p = g`.
    intro p _hp_range hp_clust
    -- Recast as `MapClusterPt` and use the ultrafilter characterization.
    change MapClusterPt p (nhds x) (fun y => grad_f x (z_y y)) at hp_clust
    rw [mapClusterPt_iff_ultrafilter] at hp_clust
    obtain ⟨U, hU_le, hU_tends⟩ := hp_clust
    -- Push `z_y` through `U`: an ultrafilter on the compact `Z` that converges to its `lim`.
    set V := Ultrafilter.map z_y U with hV_def
    have hz_y_tends : Tendsto z_y ↑U (nhds V.lim) := V.le_nhds_lim
    -- `V.lim` is a cluster point of `z_y` along `nhds x` (via the ultrafilter `U`).
    have hVlim_clust : MapClusterPt V.lim (nhds x) z_y := by
      rw [mapClusterPt_iff_ultrafilter]
      exact ⟨U, hU_le, hz_y_tends⟩
    -- `V.lim ∈ argmax_iSup f x` by Berge UHC; hence `grad_f x V.lim = g`.
    have hVlim_argmax : V.lim ∈ argmax_iSup f x :=
      argmax_iSup_clusterPt_mem f X h_cont hX_open x hx z_y hz_y hVlim_clust
    have h_grad_Vlim : grad_f x V.lim = g := h_grad_const _ hVlim_argmax
    -- `(grad_f x ∘ z_y)` tends to `grad_f x V.lim` along `↑U` by continuity.
    have h_image_tends : Tendsto (fun y => grad_f x (z_y y)) ↑U (nhds (grad_f x V.lim)) :=
      (h_grad_x_cont.tendsto _).comp hz_y_tends
    -- Hausdorff uniqueness of limits in `E` forces `p = grad_f x V.lim = g`.
    rw [← h_grad_Vlim]
    exact tendsto_nhds_unique hU_tends h_image_tends

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Upper hemicontinuity of the optimizer correspondence when the optimizer is unique. If
`Z*(x) = {z_star}`, then any selection of optimizers `z_y` at nearby points `y` converges to
`z_star` as `y → x`.

A direct corollary of `argmax_iSup_clusterPt_mem`: Every cluster point of `z_y` lies in
`argmax_iSup f x = {z_star}`, hence equals `z_star`; combined with compactness of `Z`, this gives
convergence. -/
lemma tendsto_argmax_of_unique
    (f : E → Z → ℝ) (X : Set E) (h_cont : ContinuousOnProd f X) (hX_open : IsOpen X)
    (x : E) (hx : x ∈ X) (z_star : Z) (h_unique : argmax_iSup f x = {z_star})
    (z_y : E → Z) (hz_y : ∀ᶠ y in nhds x, y ∈ X ∧ f y (z_y y) = valueFunction f y) :
    Tendsto z_y (nhds x) (nhds z_star) := by
  apply le_nhds_of_unique_clusterPt
  intro z_bar hz_bar
  rw [← mapClusterPt_def] at hz_bar
  have hmem : z_bar ∈ argmax_iSup f x :=
    argmax_iSup_clusterPt_mem f X h_cont hX_open x hx z_y hz_y hz_bar
  rw [h_unique] at hmem; exact hmem

omit [Nonempty Z] in
/-- Uniform differentiability remainder: For `y` near `x` and ALL `z ∈ Z`, the gradient remainder
`|f(y,z) - f(x,z) - ⟪∇f(x,z), y-x⟫|` is at most `ε ‖y - x‖`.

Uses the mean value theorem along `[x,y]`, continuity of `grad_f` on `X × Z`, and compactness of
`Z` to get a uniform modulus of continuity. -/
lemma HasGradientAt.uniform_remainder
    (f : E → Z → ℝ) (grad_f : E → Z → E) (X : Set E) (hX_open : IsOpen X)
    (h_diff : ∀ z, ∀ y ∈ X, HasGradientAt (fun w ↦ f w z) (grad_f y z) y)
    (h_grad_cont : ContinuousOn (fun p : E × Z ↦ grad_f p.1 p.2) (X ×ˢ univ))
    (x : E) (hx : x ∈ X) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in nhds x, y ∈ X ∧
      ∀ z : Z, |f y z - f x z - @inner ℝ E _ (grad_f x z) (y - x)| ≤ ε * ‖y - x‖ := by
  have h_unif : ∀ᶠ w in nhds x, w ∈ X ∧ ∀ z : Z, ‖grad_f w z - grad_f x z‖ < ε := by
    have hk : IsCompact (univ : Set Z) := isCompact_univ
    have hu : {p : E × E | ‖p.1 - p.2‖ < ε} ∈ uniformity E := by
      rw [Metric.uniformity_basis_dist.mem_iff]
      exact ⟨ε, hε, fun ⟨a, b⟩ h ↦ by simpa [dist_eq_norm] using h⟩
    obtain ⟨v, hv_nhds, hv_bound⟩ := hk.mem_uniformity_of_prod
      (show ContinuousOn (Function.uncurry grad_f) _ from h_grad_cont) hx hu
    rw [hX_open.nhdsWithin_eq hx] at hv_nhds
    filter_upwards [hv_nhds, hX_open.mem_nhds hx] with w hwv hwX
    exact ⟨hwX, fun z ↦ by simpa using hv_bound w hwv z (mem_univ z)⟩
  rw [Metric.eventually_nhds_iff_ball] at h_unif
  obtain ⟨r, hr, hr_sub⟩ := h_unif
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hyX : y ∈ X := (hr_sub y hy).1
  refine ⟨hyX, fun z ↦ ?_⟩
  have h_ball_convex : Convex ℝ (Metric.ball x r) := convex_ball x r
  have h_fderiv_within : ∀ w ∈ Metric.ball x r,
      HasFDerivWithinAt (fun v ↦ f v z)
        ((InnerProductSpace.toDual ℝ E) (grad_f w z)) (Metric.ball x r) w :=
    fun w hw ↦ ((h_diff z w (hr_sub w hw).1).hasFDerivAt).hasFDerivWithinAt
  have h_bound : ∀ w ∈ Metric.ball x r,
      ‖(InnerProductSpace.toDual ℝ E) (grad_f w z) -
       (InnerProductSpace.toDual ℝ E) (grad_f x z)‖ ≤ ε := by
    intro w hw
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact le_of_lt ((hr_sub w hw).2 z)
  have key := h_ball_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    h_fderiv_within h_bound (Metric.mem_ball_self hr) hy
  rwa [Real.norm_eq_abs] at key

/-- **Generalized Danskin Part (iv).**  When the gradient of `f(·, z)` at `x` is constant across
all optimizers `z ∈ argmax_iSup f x`, the value function has gradient equal to that common value at
`x`.

This strengthens the unique-optimizer case `hasGradientAt_iSup_of_unique`: Uniqueness of the
gradient image of the optimizer set already suffices for differentiability, even when the optimizer
set itself is not a singleton. -/
theorem hasGradientAt_iSup_of_const_grad
    (f : E → Z → ℝ) (grad_f : E → Z → E) (X : Set E)
    (hX_open : IsOpen X)
    (h_cont : ContinuousOnProd f X)
    (h_diff : ∀ z, ∀ y ∈ X, HasGradientAt (fun w ↦ f w z) (grad_f y z) y)
    (h_grad_cont : ContinuousOn (fun p : E × Z ↦ grad_f p.1 p.2) (X ×ˢ univ))
    (x : E) (hx : x ∈ X) (g : E)
    (h_argmax_ne : (argmax_iSup f x).Nonempty)
    (h_grad_const : ∀ z ∈ argmax_iSup f x, grad_f x z = g) :
    HasGradientAt (valueFunction f) g x := by
  rw [hasGradientAt_iff_isLittleO]
  -- Pick any optimizer z_star (nonempty by hypothesis) — its gradient is g.
  obtain ⟨z_star, hz_star_mem⟩ := h_argmax_ne
  have hz_star_eq : f x z_star = valueFunction f x := hz_star_mem
  have h_grad_z_star : grad_f x z_star = g := h_grad_const z_star hz_star_mem
  have hfx_cont := ContinuousOnProd.continuous_right h_cont x hx
  have hX_mem : X ∈ nhds x := hX_open.mem_nhds hx
  -- ### Lower bound
  -- f(·, z_star) has gradient g at x, so its remainder is o(‖y-x‖).
  have h_lower_o : (fun y ↦ f y z_star - f x z_star - @inner ℝ E _ g (y - x))
      =o[nhds x] fun y ↦ y - x := by
    rw [← h_grad_z_star, ← hasGradientAt_iff_isLittleO]
    exact h_diff z_star x hx
  -- V(y) ≥ f(y, z_star), so the V-remainder ≥ the f-remainder.
  have h_lower_ineq : ∀ᶠ y in nhds x,
      f y z_star - f x z_star - @inner ℝ E _ g (y - x) ≤
      valueFunction f y - valueFunction f x - @inner ℝ E _ g (y - x) := by
    filter_upwards [hX_mem] with y hy
    have hle : f y z_star ≤ valueFunction f y :=
      le_ciSup (isCompact_range
        (ContinuousOnProd.continuous_right h_cont y hy)).bddAbove z_star
    linarith [hz_star_eq]
  -- ### Upper bound
  -- For each y ∈ X, pick an optimizer z_y at y (compact Z + continuous fibre).
  have h_cont_fiber : ∀ y ∈ X, Continuous (fun z ↦ f y z) :=
    fun y hy ↦ ContinuousOnProd.continuous_right h_cont y hy
  have h_opt_choice : ∃ z_y : E → Z, ∀ y ∈ X, f y (z_y y) = valueFunction f y := by
    have : ∀ y : E, ∃ z : Z, y ∈ X → f y z = ⨆ z, f y z := by
      intro y
      by_cases hy : y ∈ X
      · exact ⟨_, fun _ ↦ (exists_eq_ciSup f (h_cont_fiber y hy)).choose_spec⟩
      · exact ⟨Classical.arbitrary Z, fun h ↦ absurd h hy⟩
    exact ⟨fun y ↦ (this y).choose, fun y hy ↦ (this y).choose_spec hy⟩
  obtain ⟨z_y, hz_y_opt⟩ := h_opt_choice
  have hz_y_eventually : ∀ᶠ y in nhds x, y ∈ X ∧ f y (z_y y) = valueFunction f y := by
    filter_upwards [hX_mem] with y hy; exact ⟨hy, hz_y_opt y hy⟩
  -- Berge UHC, gradient form: `grad_f x (z_y y) → g` (replaces `z_y → z_star` of the
  -- unique-optimizer case; what matters is gradient convergence, not point convergence).
  have h_grad_tends : Tendsto (fun y ↦ grad_f x (z_y y)) (nhds x) (nhds g) :=
    tendsto_grad_argmax_of_const_grad f grad_f X h_cont hX_open x hx g
      h_grad_cont h_grad_const z_y hz_y_eventually
  -- Upper bound is o(‖y-x‖): for any c > 0, eventually ‖remainder‖ ≤ c‖y-x‖.
  have h_upper_o : (fun y ↦ valueFunction f y - valueFunction f x -
      @inner ℝ E _ g (y - x)) =o[nhds x] fun y ↦ y - x := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hc2 : (0 : ℝ) < c / 2 := half_pos hc
    -- (1) Uniform differentiability: |f(y,z) - f(x,z) - ⟪grad_f x z, y-x⟫| ≤ (c/2)‖y-x‖.
    have h_unif :=
      HasGradientAt.uniform_remainder f grad_f X hX_open h_diff h_grad_cont x hx (c/2) hc2
    -- (2) Gradient convergence: ‖grad_f x (z_y y) - g‖ < c/2.
    have h_grad_near : ∀ᶠ y in nhds x, ‖grad_f x (z_y y) - g‖ < c / 2 :=
      (Metric.tendsto_nhds.mp h_grad_tends (c / 2) hc2).mono fun y hy ↦ by
        rwa [dist_eq_norm] at hy
    filter_upwards [hX_mem, h_unif, h_grad_near] with y hy ⟨_, h_rem⟩ h_gnear
    simp only [Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · -- Lower: V(y) - V(x) ≥ f(y,z_star) - f(x,z_star) and use h_rem at z_star.
      have hle_z_star : f y z_star ≤ valueFunction f y :=
        le_ciSup (isCompact_range (h_cont_fiber y hy)).bddAbove z_star
      have h_rem_star := h_rem z_star
      rw [abs_le] at h_rem_star
      rw [h_grad_z_star] at h_rem_star
      linarith [hz_star_eq]
    · -- Upper: V(y) = f(y, z_y y), and f(x, z_y y) ≤ V(x).
      have hV_eq : valueFunction f y = f y (z_y y) := (hz_y_opt y hy).symm
      have hf_le_V : f x (z_y y) ≤ valueFunction f x :=
        le_ciSup ((isCompact_range hfx_cont).bddAbove) (z_y y)
      have h_rem_zy := h_rem (z_y y)
      rw [abs_le] at h_rem_zy
      -- |⟪grad_f x z_y - g, y-x⟫| ≤ ‖grad_f x z_y - g‖ · ‖y-x‖ < (c/2)‖y-x‖.
      have h_inner_bound : @inner ℝ E _ (grad_f x (z_y y) - g) (y - x) ≤
          c / 2 * ‖y - x‖ := by
        calc @inner ℝ E _ (grad_f x (z_y y) - g) (y - x)
            ≤ |@inner ℝ E _ (grad_f x (z_y y) - g) (y - x)| := le_abs_self _
          _ ≤ ‖grad_f x (z_y y) - g‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
          _ ≤ c / 2 * ‖y - x‖ := by
              apply mul_le_mul_of_nonneg_right (le_of_lt h_gnear) (norm_nonneg _)
      have h_rearrange : valueFunction f y - valueFunction f x -
          @inner ℝ E _ g (y - x) ≤
          (f y (z_y y) - f x (z_y y) - @inner ℝ E _ (grad_f x (z_y y)) (y - x)) +
          @inner ℝ E _ (grad_f x (z_y y) - g) (y - x) := by
        rw [hV_eq, inner_sub_left]
        linarith
      linarith [h_rem_zy.2, h_inner_bound]
  exact IsLittleO.of_squeeze h_lower_ineq
    (Filter.Eventually.of_forall fun _ ↦ le_refl _) h_lower_o h_upper_o

/-- **Danskin Part (iv), unique-optimizer case.**  If `f(·, z)` is differentiable with jointly
continuous gradient and the optimizer is unique `argmax_iSup f x = {z_star}`, then `V` is
differentiable at `x` with `∇V(x) = ∇_x f(x, z_star)`.

A direct corollary of `hasGradientAt_iSup_of_const_grad`: When `argmax_iSup f x` is the singleton
`{z_star}`, the "common gradient" hypothesis is trivially satisfied with `g = grad_f x z_star`. -/
theorem hasGradientAt_iSup_of_unique (f : E → Z → ℝ) (grad_f : E → Z → E) (X : Set E)
    (hX_open : IsOpen X)
    (h_cont : ContinuousOnProd f X)
    (h_diff : ∀ z, ∀ y ∈ X, HasGradientAt (fun w ↦ f w z) (grad_f y z) y)
    (h_grad_cont : ContinuousOn (fun p : E × Z ↦ grad_f p.1 p.2) (X ×ˢ univ))
    (x : E) (hx : x ∈ X) (z_star : Z)
    (h_unique : argmax_iSup f x = {z_star}) :
    HasGradientAt (valueFunction f) (grad_f x z_star) x := by
  refine hasGradientAt_iSup_of_const_grad f grad_f X hX_open h_cont h_diff h_grad_cont
    x hx (grad_f x z_star) ⟨z_star, ?_⟩ ?_
  · -- z_star ∈ argmax_iSup f x.
    rw [h_unique]; rfl
  · -- The only optimizer is z_star, so gradient is grad_f x z_star.
    intro z hz
    rw [h_unique] at hz
    rcases hz with rfl
    rfl

end Danskin
