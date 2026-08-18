/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Brouwer
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Kakutani fixed-point theorem

Let `s` be a nonempty compact convex subset of a finite-dimensional real normed space, and let `f`
be a set-valued map on `s` with closed graph whose values `f x` are nonempty, convex, and contained
in `s`. Then `f` has a fixed point: Some `x ∈ s` with `x ∈ f x`.

## Main definitions

* `IsClosedGraph` — a set-valued map whose graph is closed in the product
* `KakutaniApprox` — bundled approximation data for the fixed-point construction

## Main statements

* `UpperHemicontinuous.isClosedGraph` — a closed-valued upper hemicontinuous map has a closed graph
* `IsClosedGraph.image_subtypeVal` — a closed graph transfers from a closed subtype to the ambient
  space
* `setValuedMapApproxFixedPoint` — existence of approximate fixed points for a set-valued map
* `kakutaniFixedPoint` — Kakutani's fixed-point theorem

## Tags

kakutani, fixed point, set-valued map, closed graph
-/

@[expose] public section

open Filter Topology

/-! ### Closed graph property -/

/-- A set-valued map `f : X → Set Y` has a closed graph: The set `{(x, y) | y ∈ f x}` is closed in
`X × Y`. -/
def IsClosedGraph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Set Y) : Prop :=
  IsClosed { z : X × Y | z.2 ∈ f z.1 }

/-- An **upper hemicontinuous** closed-valued set-valued map into a regular space has a closed
graph. -/
theorem UpperHemicontinuous.isClosedGraph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [RegularSpace Y] {f : X → Set Y} (huhc : UpperHemicontinuous f)
    (hclosed : ∀ x, IsClosed (f x)) : IsClosedGraph f := by
  -- A point in the closure of the graph is a cluster point; project the cluster filter onto each
  -- coordinate and feed the resulting convergent nets to the UHC characterization.
  change IsClosed { z : X × Y | z.2 ∈ f z.1 }
  rw [isClosed_iff_clusterPt]
  rintro ⟨x₀, y₀⟩ hcp
  set l : Filter (X × Y) := 𝓝 (x₀, y₀) ⊓ Filter.principal { z : X × Y | z.2 ∈ f z.1 } with hl
  haveI : l.NeBot := by rw [hl]; exact hcp
  have hx : Filter.Tendsto (Prod.fst : X × Y → X) l (𝓝 x₀) :=
    (continuous_fst.tendsto _).mono_left inf_le_left
  have hy : Filter.Tendsto (Prod.snd : X × Y → Y) l (𝓝 y₀) :=
    (continuous_snd.tendsto _).mono_left inf_le_left
  have hev : ∀ᶠ z in l, z.2 ∈ f z.1 :=
    (Filter.eventually_principal.2 fun z hz => hz).filter_mono inf_le_right
  exact UpperHemicontinuousAt.mem_of_tendsto (huhc x₀) (hclosed x₀) hx hev.frequently hy

/-- A closed graph transfers from a closed subtype to the ambient space: If a set-valued map into
the subtype `↑S` of a closed set `S` has a closed graph, so does the map composed with the
inclusion `↑S ↪ Y`. -/
theorem IsClosedGraph.image_subtypeVal {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set Y} (hS : IsClosed S) {f : X → Set ↑S} (hf : IsClosedGraph f) :
    IsClosedGraph fun x => Subtype.val '' f x := by
  -- The ambient graph is the image of the subtype graph under `id × val`, a closed embedding.
  have h_emb : Topology.IsClosedEmbedding (Prod.map (id : X → X) (Subtype.val : ↑S → Y)) := by
    refine ⟨Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [Set.range_prodMap, Set.range_id, Subtype.range_val]
    exact isClosed_univ.prod hS
  have h_eq : { z : X × Y | z.2 ∈ Subtype.val '' f z.1 } =
      Prod.map id Subtype.val '' { z : X × ↑S | z.2 ∈ f z.1 } := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(x, w), hw, rfl⟩
    · rintro ⟨⟨x', w⟩, hw, heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      exact ⟨w, hw, rfl⟩
  rw [IsClosedGraph, h_eq]
  exact h_emb.isClosedMap _ hf

/-! ### Bundled approximation state -/

/-- All data for one step of the Kakutani approximation sequence, bundled so that the product
topology and compactness are automatic. -/
structure KakutaniApprox {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : ℕ) (s : Set V) where
  x : s
  y : Fin (k + 1) → s
  z : Fin (k + 1) → s
  w : Fin (k + 1) → Set.Icc (0 : ℝ) 1

/-! ### Carathéodory padding -/

/-- Given x ∈ convexHull s, produce a representation as a convex combination of exactly k+1 points
in s (padding with zeros if fewer are needed). Internal Carathéodory padding for the Kakutani
approximation. -/
private lemma caratheodoryPad {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (k : ℕ) (hk : k = Module.finrank ℝ V) {x : V}
    (hx : x ∈ convexHull ℝ s) :
    ∃ (z : Fin (k + 1) → V) (a : Fin (k + 1) → ℝ),
      Set.range z ⊆ s ∧
      a ∈ stdSimplex ℝ (Fin (k + 1)) ∧
      x = Finset.univ.centerMass a z := by
  -- Get the Carathéodory representation with ≤ k+1 affinely independent points
  obtain ⟨I, hI, z1, α, h_range, h_indep, h_pos, h_sum, h_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  have h_card : hI.card ≤ k + 1 := by
    apply le_trans (AffineIndependent.card_le_finrank_succ h_indep)
    rw [hk, add_le_add_iff_right]
    exact Submodule.finrank_le (vectorSpan ℝ (Set.range z1))
  -- Pad: embed the ≤ k+1 points into exactly k+1 slots
  let g1 := hI.equivFin
  let g2 : Fin hI.card → Fin (k + 1) := fun i ↦ Fin.ofNat _ i.1
  let g3 := g2 ∘ g1
  have hg3 : Function.Injective g3 := by
    unfold g3
    refine (Equiv.injective_comp g1 g2).mpr ?_
    intro i1 i2 h5
    unfold g2 at h5
    simp only [Fin.ofNat_eq_cast] at h5
    rw [← Fin.val_eq_val] at h5 ⊢
    rwa [Fin.val_cast_of_lt, Fin.val_cast_of_lt] at h5
    · exact lt_of_lt_of_le i2.2 h_card
    · exact lt_of_lt_of_le i1.2 h_card
  have hsne : s.Nonempty := convexHull_nonempty_iff.mp (Set.nonempty_of_mem hx)
  obtain ⟨sdef, hsdef⟩ := hsne
  -- Extend α and z1 to all of Fin (k+1), filling unused slots with 0/sdef
  let β := Function.extend g3 α (fun _ ↦ 0)
  let z2 := Function.extend g3 z1 (fun _ ↦ sdef)
  have h5 : Set.range z2 ⊆ s := by
    intro y hy
    obtain ⟨i1, hi1⟩ := hy
    rw [← hi1]
    unfold z2
    by_cases h5 : ∃ i2, g3 i2 = i1
    · apply h_range
      obtain ⟨i2, hi2⟩ := h5
      use i2
      rw [← hi2, Function.Injective.extend_apply hg3]
    · rwa [Function.extend_apply' _ _ _ h5]
  use z2, β
  have h6 : ∑ i, β i = 1 := by
    rw [← h_sum]; symm
    apply Fintype.sum_of_injective g3 hg3
    · exact fun i a ↦ Function.extend_apply' α (fun _ ↦ 0) i a
    · exact fun i ↦ Eq.symm (Function.Injective.extend_apply hg3 α (fun _ ↦ 0) i)
  have h7 : x = ∑ i, β i • z2 i := by
    rw [← h_eq]
    apply Fintype.sum_of_injective g3 hg3
    · intro i h7
      simp only [smul_eq_zero]
      exact Or.inl (Function.extend_apply' α (fun _ ↦ 0) i h7)
    · intro i
      unfold β z2
      rw [Function.Injective.extend_apply hg3, Function.Injective.extend_apply hg3]
  have h9 : ∀ i, 0 ≤ β i := by
    intro i; unfold β
    by_cases h : ∃ j, g3 j = i
    · obtain ⟨j, rfl⟩ := h
      rw [Function.Injective.extend_apply hg3]
      exact le_of_lt (h_pos j)
    · rw [Function.extend_apply' _ _ _ h]
  refine ⟨h5, ⟨h9, h6⟩, ?_⟩
  rw [Finset.centerMass, h6, inv_one, one_smul, ← h7]

/-- Each coordinate of a point in the standard simplex lies in `[0, 1]`. -/
private lemma sub_icc_of_simplex {k : ℕ} {a : Fin k → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin k)) : a ∈ Set.Icc 0 1 := by
  simp only [Set.mem_Icc]
  exact ⟨ha.1, fun i => by
    simp only [Pi.one_apply]
    rw [← ha.2]
    apply Finset.single_le_sum (fun j _ ↦ ha.1 j)
    simp only [Finset.mem_univ]⟩

/-! ### Approximate fixed points -/

/-- Using Brouwer, produce an ε-approximate fixed point for a set-valued map. -/
lemma setValuedMapApproxFixedPoint {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcmpct : IsCompact s) (hcvx : Convex ℝ s) (hne : s.Nonempty)
    (f : s → Set V) (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty)
    (k : ℕ) (hk : k = Module.finrank ℝ V) (eps : ℝ) (heps : 0 < eps) :
    ∃ (a : s) (y : Fin (k + 1) → s) (z : Fin (k + 1) → V) (α : Fin (k + 1) → ℝ),
      α ∈ stdSimplex ℝ (Fin (k + 1)) ∧
      a.1 = Finset.univ.centerMass α z ∧
      ∀ i, dist a (y i) < eps ∧ z i ∈ f (y i) := by
  -- Use a continuous selection from the convex hull of nearby f-values
  let G : s → Set V := fun x ↦ convexHull ℝ { z | ∃ y, dist x y < eps ∧ z ∈ f y }
  have hG1 : ∀ x, Convex ℝ (G x) := fun x ↦ convex_convexHull ℝ _
  haveI : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
  have h2 := exists_continuous_forall_mem_convex_of_local_const hG1
  have h3 : ∃ g : C(s, V), ∀ x, g x ∈ G x := by
    apply h2
    intro x
    obtain ⟨z, hz⟩ := (h1 x).2.2
    use z
    apply Metric.eventually_nhds_iff.mpr
    use eps
    exact ⟨heps, fun y h3 ↦ subset_convexHull _ _ ⟨x, h3, hz⟩⟩
  obtain ⟨g, hg⟩ := h3
  have h6 : ∀ x, g x ∈ s := by
    intro x
    suffices G x ⊆ s from this (hg x)
    exact convexHull_min (fun z ⟨y, _, hz⟩ ↦ (h1 y).1 hz) hcvx
  -- Apply Brouwer to the continuous selection
  have h5 : ∃ x, g x = x := by
    let g2 : s → s := fun x ↦ ⟨g x, h6 x⟩
    have h7 : Continuous g2 := Continuous.subtype_mk g.continuous h6
    let g3 : C(s, s) := ⟨g2, h7⟩
    obtain ⟨x, hx⟩ := brouwerFixedPoint s hcvx hcmpct hne g3
    use x; nth_rewrite 2 [← hx]; rfl
  obtain ⟨a, ha⟩ := h5
  -- Decompose the fixed point via Carathéodory
  have h_in_G : a.1 ∈ G a := by rw [← ha]; exact hg a
  obtain ⟨z, α, h7_range, h7_simplex, h7_eq⟩ := caratheodoryPad _ k hk h_in_G
  use a
  have h8 : ∀ i, ∃ y, dist a y < eps ∧ z i ∈ f y := by
    intro i; exact h7_range (Set.mem_range_self i)
  choose y hy using h8
  exact ⟨y, z, α, h7_simplex, h7_eq, hy⟩

/-! ### Main theorem -/

/-- **Kakutani's fixed-point theorem**: Let `s` be a nonempty compact convex subset of a
finite-dimensional normed space. If `f : s → Set V` has a closed graph and each `f x` is nonempty,
convex, and contained in `s`, then there exists `x ∈ s` with `x ∈ f x`. -/
theorem kakutaniFixedPoint {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : s → Set V) (hcg : IsClosedGraph f)
    (h1 : ∀ x, f x ⊆ s ∧ Convex ℝ (f x) ∧ (f x).Nonempty) :
    ∃ x : s, x.1 ∈ f x := by
  let k := Module.finrank ℝ V
  have h2 := setValuedMapApproxFixedPoint s hcmpct hcvx hne f h1 k rfl
  -- Build approximation sequences for each ε = 1/(i+1)
  have h3 (i : ℕ) := h2 ((1 : ℝ) / (i + 1)) (Nat.one_div_pos_of_nat)
  choose a y z α h_simplex h_eq h_prop using h3
  -- Bundle all approximation data for ultrafilter extraction
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu_atTop : ↑u ≤ (atTop : Filter ℕ) := Ultrafilter.of_le atTop
  haveI : CompactSpace ↑s := isCompact_iff_compactSpace.mp hcmpct
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- Use the bundled KakutaniApprox structure for clean limit extraction
  have hz_in_s (i : ℕ) (j : Fin (k + 1)) : z i j ∈ s := (h1 _).1 (h_prop i j).2
  let z' (i : ℕ) (j : Fin (k + 1)) : s := ⟨z i j, hz_in_s i j⟩
  have ha_icc (i : ℕ) (j : Fin (k + 1)) : α i j ∈ Set.Icc 0 1 :=
    ⟨(sub_icc_of_simplex (h_simplex i)).1 j,
     (sub_icc_of_simplex (h_simplex i)).2 j⟩
  let α' (i : ℕ) (j : Fin (k + 1)) : Set.Icc (0 : ℝ) 1 := ⟨α i j, ha_icc i j⟩
  -- Bundle into a product type for compactness
  let Btype := s × (Fin (k + 1) → s) × (Fin (k + 1) → s) × (Fin (k + 1) → Set.Icc (0 : ℝ) 1)
  let B : ℕ → Btype := fun i => (a i, y i, z' i, α' i)
  obtain ⟨B0, -, hB_lim⟩ := isCompact_univ.ultrafilter_le_nhds (u.map B) (by simp)
  let x_star := B0.1
  let y_star := B0.2.1
  let z_star := B0.2.2.1
  let α_star := B0.2.2.2
  -- Extract component-wise limits
  have ha_lim : Tendsto a u (nhds x_star) :=
    (continuous_fst.tendsto B0).comp hB_lim
  have hy_lim (j) : Tendsto (fun i => y i j) u (nhds (y_star j)) :=
    ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).tendsto B0 |>.comp hB_lim
  have hz_lim (j) : Tendsto (fun i => z' i j) u (nhds (z_star j)) :=
    ((continuous_apply j).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).tendsto B0 |>.comp hB_lim
  have hα_lim (j) : Tendsto (fun i => α' i j) u (nhds (α_star j)) :=
    ((continuous_apply j).comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).tendsto B0 |>.comp hB_lim
  -- y_star j = x_star for all j (distances → 0)
  have hy_x_star (j) : y_star j = x_star := by
    have h_dist : Tendsto (fun i => dist (a i).1 (y i j).1) u (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      · exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hu_atTop
      · exact Eventually.of_forall fun i => dist_nonneg
      · exact Eventually.of_forall fun i => le_of_lt (h_prop i j).1
    have h_dist2 : Tendsto (fun i => dist (a i).1 (y i j).1) u
        (nhds (dist x_star.1 (y_star j).1)) :=
      (continuous_dist.tendsto (x_star.1, (y_star j).1)).comp
        (Tendsto.prodMk_nhds
          (continuous_subtype_val.tendsto x_star |>.comp ha_lim)
          (continuous_subtype_val.tendsto (y_star j) |>.comp (hy_lim j)))
    ext; exact dist_eq_zero.mp (tendsto_nhds_unique h_dist2 h_dist) |>.symm
  -- z_star j ∈ f(x_star) by closed graph
  have h8 (j) : (z_star j).1 ∈ f x_star := by
    rw [← hy_x_star j]
    let yzj (i : ℕ) : s × V := (y i j, (z' i j).1)
    have h10 (i) : yzj i ∈ { p : s × V | p.2 ∈ f p.1 } := (h_prop i j).2
    have h11 : Tendsto yzj u (nhds (y_star j, (z_star j).1)) :=
      Tendsto.prodMk_nhds (hy_lim j)
        (continuous_subtype_val.tendsto (z_star j) |>.comp (hz_lim j))
    exact hcg.mem_of_tendsto h11 (Eventually.of_forall h10)
  -- The limit weights still sum to one (taking the limit of each ∑ⱼ αⁱⱼ = 1)
  have h_sum_α : ∑ j, (α_star j).1 = 1 := by
    have h_sum_i (i : ℕ) : ∑ j, (α' i j).1 = 1 := (h_simplex i).2
    have h_lim_sum : Tendsto (fun i => ∑ j, (α' i j).1) u (nhds (∑ j, (α_star j).1)) :=
      tendsto_finset_sum Finset.univ fun j _ =>
        continuous_subtype_val.tendsto (α_star j) |>.comp (hα_lim j)
    exact tendsto_nhds_unique h_lim_sum (by simp_rw [h_sum_i]; exact tendsto_const_nhds)
  -- x_star is the center of mass of z_star with weights α_star
  have h_conv : x_star.1 = Finset.univ.centerMass
      (fun j => (α_star j).1) (fun j => (z_star j).1) := by
    have h_a_eq (i : ℕ) : (a i).1 = ∑ j, (α' i j).1 • (z' i j).1 := by
      rw [h_eq i, Finset.centerMass, (h_simplex i).2, inv_one, one_smul]
    have h_lim_a : Tendsto (fun i => (a i).1) u (nhds x_star.1) :=
      continuous_subtype_val.tendsto x_star |>.comp ha_lim
    have h_lim_rhs : Tendsto (fun i => ∑ j, (α' i j).1 • (z' i j).1) u
        (nhds (∑ j, (α_star j).1 • (z_star j).1)) :=
      tendsto_finset_sum Finset.univ fun j _ =>
        Tendsto.smul
          (continuous_subtype_val.tendsto (α_star j) |>.comp (hα_lim j))
          (continuous_subtype_val.tendsto (z_star j) |>.comp (hz_lim j))
    have h_eq_lim := tendsto_nhds_unique h_lim_a (by simp_rw [h_a_eq]; exact h_lim_rhs)
    rw [Finset.centerMass, h_sum_α, inv_one, one_smul, ← h_eq_lim]
  -- Conclude: x_star ∈ f(x_star) by convexity of f(x_star)
  use x_star
  rw [h_conv]
  apply (h1 x_star).2.1.centerMass_mem
  · intro j _; exact (α_star j).2.1
  · rw [h_sum_α]; exact zero_lt_one
  · intro j _; exact h8 j
