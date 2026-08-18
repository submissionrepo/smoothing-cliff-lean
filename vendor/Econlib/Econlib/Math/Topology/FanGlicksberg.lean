/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Kakutani

/-!
# Kakutani–Fan–Glicksberg fixed-point theorem

Let `K` be a nonempty compact convex subset of a locally convex Hausdorff topological ℝ-vector
space, and let `Φ` be a set-valued map on `K` with closed graph whose values are nonempty convex
subsets of `K`. Then `Φ` has a fixed point: Some `x ∈ K` with `x ∈ Φ x`.

## Main statements

* `exists_mem_nhds_isClosed_convex_neg_eq` — a closed convex symmetric neighborhood basis of `0` in
  a locally convex space
* `kakutaniFixedPoint_convexHull_finite` — Kakutani's theorem on the convex hull of a finite set in
  a Hausdorff topological vector space
* `fanGlicksbergFixedPoint` — the Kakutani–Fan–Glicksberg fixed-point theorem

## Notes

This generalizes `kakutaniFixedPoint` from finite-dimensional normed spaces to locally convex
spaces.

## References

* Fan, Ky. 1952. “Fixed-Point and Minimax Theorems in Locally Convex Topological Linear Spaces.”
  *Proceedings of the National Academy of Sciences* 38 (2): 121–26.
  [https://doi.org/10.1073/pnas.38.2.121](https://doi.org/10.1073/pnas.38.2.121).
* Glicksberg, I. L. 1952. “A Further Generalization of the Kakutani Fixed Point Theorem, With
  Application to Nash Equilibrium Points.” *Proceedings of the American Mathematical Society* 3
  (1): 170. [https://doi.org/10.2307/2032478](https://doi.org/10.2307/2032478).

## Tags

kakutani, fan, glicksberg, fixed point, locally convex space
-/

@[expose] public section

open Filter Topology Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- In a locally convex topological vector space, every neighborhood of `0` contains a closed,
convex, symmetric neighborhood of `0`. -/
theorem exists_mem_nhds_isClosed_convex_neg_eq [LocallyConvexSpace ℝ E]
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ V ∈ 𝓝 (0 : E), IsClosed V ∧ Convex ℝ V ∧ -V = V ∧ V ⊆ W := by
  obtain ⟨W₁, hW₁_mem, hW₁_closed, hW₁_sub⟩ := exists_mem_nhds_isClosed_subset hW
  obtain ⟨C, hC_mem, hC_cvx, hC_sub⟩ :=
    (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp ‹_› W₁ hW₁_mem
  set D := closure C with hD_def
  have hD_cvx : Convex ℝ D := hC_cvx.closure
  have hD_closed : IsClosed D := isClosed_closure
  have hD_mem : D ∈ 𝓝 (0 : E) := Filter.mem_of_superset hC_mem subset_closure
  have hD_sub : D ⊆ W₁ := closure_minimal hC_sub hW₁_closed
  -- Symmetrize: `V = D ∩ -D` is closed, convex, symmetric, a neighborhood, and `⊆ W`.
  refine ⟨D ∩ -D, Filter.inter_mem hD_mem (neg_mem_nhds_zero E hD_mem),
    hD_closed.inter hD_closed.neg, hD_cvx.inter hD_cvx.neg, ?_, ?_⟩
  · rw [Set.inter_neg, neg_neg, Set.inter_comm]
  · exact (Set.inter_subset_left.trans hD_sub).trans hW₁_sub

/-- **Kakutani's fixed-point theorem on the convex hull of a finite set** in a Hausdorff
topological vector space. -/
theorem kakutaniFixedPoint_convexHull_finite [T2Space E]
    (F : Finset E) (hne : (F : Set E).Nonempty)
    (Ψ : convexHull ℝ (F : Set E) → Set E) (hcg : IsClosedGraph Ψ)
    (h1 : ∀ x, Ψ x ⊆ convexHull ℝ (F : Set E) ∧ Convex ℝ (Ψ x) ∧ (Ψ x).Nonempty) :
    ∃ x, x.1 ∈ Ψ x := by
  classical
  let M : Submodule ℝ E := Submodule.span ℝ (F : Set E)
  haveI : FiniteDimensional ℝ M := Module.Finite.span_of_finite ℝ F.finite_toSet
  have hC_subM : convexHull ℝ (F : Set E) ⊆ (M : Set E) :=
    convexHull_min Submodule.subset_span M.convex
  let n : ℕ := Module.finrank ℝ M
  let e : M ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ M).equivFunL
  have hval_cont : Continuous (Subtype.val : M → E) := continuous_subtype_val
  let CM : Set M := Subtype.val ⁻¹' convexHull ℝ (F : Set E)
  let C' : Set (Fin n → ℝ) := e '' CM
  have hCM_cvx : Convex ℝ CM :=
    (convex_convexHull ℝ (F : Set E)).linear_preimage (M.subtype : M →ₗ[ℝ] E)
  have hC_cpct : IsCompact (convexHull ℝ (F : Set E)) :=
    (F.finite_toSet).isCompact_convexHull ℝ
  have hCM_cpct : IsCompact CM := by
    have hrange : convexHull ℝ (F : Set E) ⊆ Set.range (Subtype.val : M → E) := by
      rw [Subtype.range_val]; exact hC_subM
    exact Topology.IsInducing.subtypeVal.isCompact_preimage' hC_cpct hrange
  have hC'_cvx : Convex ℝ C' := hCM_cvx.linear_image (e : M →ₗ[ℝ] (Fin n → ℝ))
  have hC'_cpct : IsCompact C' := hCM_cpct.image e.continuous
  have hCM_ne : CM.Nonempty := by
    obtain ⟨f, hf⟩ := hne
    have hfC : f ∈ convexHull ℝ (F : Set E) := subset_convexHull ℝ (F : Set E) hf
    exact ⟨⟨f, hC_subM hfC⟩, hfC⟩
  have hC'_ne : C'.Nonempty := hCM_ne.image e
  have hback_mem : ∀ y : C', ((e.symm y.1 : M) : E) ∈ convexHull ℝ (F : Set E) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm_mem, rfl⟩ := hy
    simpa using hm_mem
  let backC : C' → convexHull ℝ (F : Set E) :=
    fun y => ⟨((e.symm y.1 : M) : E), hback_mem y⟩
  have hbackC_cont : Continuous backC := by
    apply Continuous.subtype_mk
    exact hval_cont.comp (e.symm.continuous.comp continuous_subtype_val)
  let Ψ' : C' → Set (Fin n → ℝ) := fun y => e '' (Subtype.val ⁻¹' (Ψ (backC y)))
  have hΨ'_mem : ∀ (y : C') (z : Fin n → ℝ),
      z ∈ Ψ' y ↔ ((e.symm z : M) : E) ∈ Ψ (backC y) := by
    intro y z
    constructor
    · rintro ⟨m, hm, rfl⟩; simpa using hm
    · intro hz
      exact ⟨e.symm z, hz, by simp⟩
  have hΨ'_props : ∀ y, Ψ' y ⊆ C' ∧ Convex ℝ (Ψ' y) ∧ (Ψ' y).Nonempty := by
    intro y
    obtain ⟨hsub, hcvx, hne'⟩ := h1 (backC y)
    refine ⟨?_, ?_, ?_⟩
    · rintro z ⟨m, hm, rfl⟩
      exact ⟨m, hsub (Set.mem_preimage.mp hm), rfl⟩
    · change Convex ℝ (e '' (Subtype.val ⁻¹' Ψ (backC y)))
      have hpre_cvx : Convex ℝ (Subtype.val ⁻¹' Ψ (backC y) : Set M) :=
        hcvx.linear_preimage (M.subtype : M →ₗ[ℝ] E)
      exact hpre_cvx.linear_image (e : M →ₗ[ℝ] (Fin n → ℝ))
    · obtain ⟨w, hw⟩ := hne'
      have hwM : w ∈ (M : Set E) := hC_subM (hsub hw)
      exact ⟨e ⟨w, hwM⟩, ⟨w, hwM⟩, Set.mem_preimage.mpr hw, rfl⟩
  -- `Ψ'` has closed graph: it is the preimage of `Ψ`'s closed graph under a continuous map.
  have hΨ'_cg : IsClosedGraph Ψ' := by
    have hg_cont : Continuous
        (fun p : C' × (Fin n → ℝ) => (backC p.1, ((e.symm p.2 : M) : E))) :=
      (hbackC_cont.comp continuous_fst).prodMk
        (hval_cont.comp (e.symm.continuous.comp continuous_snd))
    have hpre : {p : C' × (Fin n → ℝ) | p.2 ∈ Ψ' p.1} =
        (fun p : C' × (Fin n → ℝ) => (backC p.1, ((e.symm p.2 : M) : E))) ⁻¹'
          {q : convexHull ℝ (F : Set E) × E | q.2 ∈ Ψ q.1} := by
      ext ⟨y, z⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hΨ'_mem]
    rw [IsClosedGraph, hpre]
    exact hcg.preimage hg_cont
  obtain ⟨y, hy⟩ := kakutaniFixedPoint C' hC'_cvx hC'_cpct hC'_ne Ψ' hΨ'_cg hΨ'_props
  exact ⟨backC y, (hΨ'_mem y y.1).mp hy⟩

/-- Given a closed convex symmetric neighborhood `V` of `0`, there are `x ∈ K` and `y ∈ Φ x` with
`x - y ∈ V`. -/
private theorem fanGlicksberg_approx [T2Space E]
    (K : Set E) (hKcp : IsCompact K) (hKcv : Convex ℝ K) (hne : K.Nonempty)
    (Φ : K → Set E) (hcg : IsClosedGraph Φ)
    (h1 : ∀ x, Φ x ⊆ K ∧ Convex ℝ (Φ x) ∧ (Φ x).Nonempty)
    {V : Set E} (hVnhds : V ∈ 𝓝 (0 : E)) (hVclosed : IsClosed V) (hVcvx : Convex ℝ V)
    (hVsymm : -V = V) :
    ∃ (x : K) (y : E), y ∈ Φ x ∧ x.1 - y ∈ V := by
  classical
  have hintV_nhds : interior V ∈ 𝓝 (0 : E) := interior_mem_nhds.mpr hVnhds
  have hzero_mem : (0 : E) ∈ interior V := mem_interior_iff_mem_nhds.mpr hVnhds
  have hcover_nhds : ∀ k ∈ K, ({k} + interior V) ∈ 𝓝 k := by
    intro k _
    refine (isOpen_interior.add_left).mem_nhds ?_
    have : k + (0 : E) ∈ {k} + interior V := Set.add_mem_add (Set.mem_singleton k) hzero_mem
    simpa using this
  obtain ⟨F, hF_subK, hF_cover⟩ :=
    hKcp.elim_nhds_subcover (fun k => {k} + interior V) hcover_nhds
  obtain ⟨k₀, hk₀⟩ := hne
  obtain ⟨S, hS_mem, hk₀S⟩ := Set.mem_iUnion₂.mp (hF_cover hk₀)
  have hF_ne : (F : Set E).Nonempty := ⟨S, hS_mem⟩
  have hC_subK : convexHull ℝ (F : Set E) ⊆ K :=
    convexHull_min (fun x hx => hF_subK x hx) hKcv
  let inclCK : convexHull ℝ (F : Set E) → K := fun z => ⟨z.1, hC_subK z.2⟩
  have hinclCK_cont : Continuous inclCK :=
    Continuous.subtype_mk continuous_subtype_val _
  have hK_closed : IsClosed K := hKcp.isClosed
  let Ψ : convexHull ℝ (F : Set E) → Set E :=
    fun z => (Φ (inclCK z) + V) ∩ convexHull ℝ (F : Set E)
  have hΨ_props : ∀ z, Ψ z ⊆ convexHull ℝ (F : Set E) ∧ Convex ℝ (Ψ z) ∧ (Ψ z).Nonempty := by
    intro z
    refine ⟨Set.inter_subset_right, ?_, ?_⟩
    · exact ((h1 (inclCK z)).2.1.add hVcvx).inter (convex_convexHull ℝ _)
    · obtain ⟨y, hy⟩ := (h1 (inclCK z)).2.2
      have hyK : y ∈ K := (h1 (inclCK z)).1 hy
      obtain ⟨S', hS'_mem, hyS'⟩ := Set.mem_iUnion₂.mp (hF_cover hyK)
      rw [Set.singleton_add, Set.mem_image] at hyS'
      obtain ⟨v, hv_int, hv_eq⟩ := hyS'
      have hv_V : v ∈ V := interior_subset hv_int
      -- `y ∈ {S'} + interior V`, so `S' = y + (-v)` with `-v ∈ -V = V`.
      have hnegv : -v ∈ V := by rw [← hVsymm]; exact Set.neg_mem_neg.mpr hv_V
      have hS'_sum : S' ∈ Φ (inclCK z) + V := by
        have : y + -v = S' := by rw [← hv_eq]; abel
        exact this ▸ Set.add_mem_add hy hnegv
      have hS'_C : S' ∈ convexHull ℝ (F : Set E) :=
        subset_convexHull ℝ _ hS'_mem
      exact ⟨S', hS'_sum, hS'_C⟩
  -- The Minkowski-sum graph of `Ψ` is closed by projecting off the compact factor `K`.
  have hΨ_cg : IsClosedGraph Ψ := by
    have hsum_closed :
        IsClosed {p : convexHull ℝ (F : Set E) × E | p.2 ∈ Φ (inclCK p.1) + V} := by
      haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcp
      let S : Set ((convexHull ℝ (F : Set E) × E) × K) :=
        {q | (inclCK q.1.1, (q.2 : E)) ∈ {z : K × E | z.2 ∈ Φ z.1} ∧ q.1.2 - (q.2 : E) ∈ V}
      have hS_closed : IsClosed S := by
        have hg1 : Continuous fun q : (convexHull ℝ (F : Set E) × E) × K =>
            (inclCK q.1.1, (q.2 : E)) :=
          (hinclCK_cont.comp (continuous_fst.comp continuous_fst)).prodMk
            (continuous_subtype_val.comp continuous_snd)
        have hg2 : Continuous fun q : (convexHull ℝ (F : Set E) × E) × K =>
            q.1.2 - (q.2 : E) :=
          (continuous_snd.comp continuous_fst).sub
            (continuous_subtype_val.comp continuous_snd)
        exact (hcg.preimage hg1).inter (hVclosed.preimage hg2)
      have hproj : {p : convexHull ℝ (F : Set E) × E | p.2 ∈ Φ (inclCK p.1) + V} =
          Prod.fst '' S := by
        ext ⟨z, w⟩
        simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, Set.mem_add]
        constructor
        · rintro ⟨y, hy, v, hv, rfl⟩
          have hyK : y ∈ K := (h1 (inclCK z)).1 hy
          exact ⟨z, y + v, ⟨y, hyK⟩, ⟨hy, by simpa using hv⟩, rfl⟩
        · rintro ⟨z', w', ⟨y, hyK⟩, ⟨hy, hv⟩, heq⟩
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
          exact ⟨y, hy, w' - y, hv, by abel⟩
      rw [hproj]
      exact isClosedMap_fst_of_compactSpace S hS_closed
    have hCcp : IsCompact (convexHull ℝ (F : Set E)) := (F.finite_toSet).isCompact_convexHull ℝ
    have hC_closed : IsClosed {p : convexHull ℝ (F : Set E) × E | p.2 ∈ convexHull ℝ (F : Set E)} :=
      hCcp.isClosed.preimage continuous_snd
    have hgraph_eq : {p : convexHull ℝ (F : Set E) × E | p.2 ∈ Ψ p.1} =
        {p : convexHull ℝ (F : Set E) × E | p.2 ∈ Φ (inclCK p.1) + V} ∩
          {p : convexHull ℝ (F : Set E) × E | p.2 ∈ convexHull ℝ (F : Set E)} := by
      ext ⟨z, w⟩; rfl
    rw [IsClosedGraph, hgraph_eq]
    exact hsum_closed.inter hC_closed
  obtain ⟨z₀, hz₀⟩ := kakutaniFixedPoint_convexHull_finite F hF_ne Ψ hΨ_cg hΨ_props
  obtain ⟨hz₀_sum, -⟩ := hz₀
  rw [Set.mem_add] at hz₀_sum
  obtain ⟨y, hy, v, hv, hsum⟩ := hz₀_sum
  refine ⟨inclCK z₀, y, hy, ?_⟩
  have hxy : (z₀.1 : E) - y = v := by rw [← hsum]; abel
  rw [hxy]; exact hv

/-- **Kakutani–Fan–Glicksberg fixed-point theorem.** A set-valued self-map with closed graph and
nonempty convex values on a nonempty compact convex subset of a locally convex Hausdorff
topological ℝ-vector space has a fixed point. -/
theorem fanGlicksbergFixedPoint [LocallyConvexSpace ℝ E] [T2Space E]
    (K : Set E) (hKcp : IsCompact K) (hKcv : Convex ℝ K) (hne : K.Nonempty)
    (Φ : K → Set E) (hcg : IsClosedGraph Φ)
    (h1 : ∀ x, Φ x ⊆ K ∧ Convex ℝ (Φ x) ∧ (Φ x).Nonempty) :
    ∃ x : K, x.1 ∈ Φ x := by
  classical
  -- Index: closed convex symmetric neighborhoods of `0`, directed by reverse inclusion (`Jᵒᵈ`).
  let J : Type _ := {V : Set E // V ∈ 𝓝 (0 : E) ∧ IsClosed V ∧ Convex ℝ V ∧ -V = V}
  haveI hJ_ne : Nonempty J := by
    obtain ⟨V, hVnhds, hVcl, hVcvx, hVsymm, -⟩ :=
      exists_mem_nhds_isClosed_convex_neg_eq (W := (Set.univ : Set E)) Filter.univ_mem
    exact ⟨⟨V, hVnhds, hVcl, hVcvx, hVsymm⟩⟩
  haveI hJ_dir : IsCodirectedOrder J := by
    refine ⟨fun a b => ?_⟩
    have hint : (a.1 ∩ b.1) ∈ 𝓝 (0 : E) := Filter.inter_mem a.2.1 b.2.1
    obtain ⟨c, hc_nhds, hc_cl, hc_cvx, hc_symm, hc_sub⟩ :=
      exists_mem_nhds_isClosed_convex_neg_eq hint
    refine ⟨⟨c, hc_nhds, hc_cl, hc_cvx, hc_symm⟩, ?_, ?_⟩
    · exact hc_sub.trans Set.inter_subset_left
    · exact hc_sub.trans Set.inter_subset_right
  haveI hJod_dir : IsDirectedOrder Jᵒᵈ := OrderDual.isDirected_le
  haveI hatTop : (atTop : Filter Jᵒᵈ).NeBot := atTop_neBot
  have happrox : ∀ D : J, ∃ (x : K) (y : K), (y : E) ∈ Φ x ∧ (x : E) - (y : E) ∈ D.1 := by
    intro D
    obtain ⟨x, y, hyΦ, hxy⟩ :=
      fanGlicksberg_approx K hKcp hKcv hne Φ hcg h1 D.2.1 D.2.2.1 D.2.2.2.1 D.2.2.2.2
    exact ⟨x, ⟨y, (h1 x).1 hyΦ⟩, hyΦ, hxy⟩
  choose xf yf hyΦ hxy using happrox
  let u : Ultrafilter J := @Ultrafilter.of Jᵒᵈ (atTop : Filter Jᵒᵈ) hatTop
  have hu_le : (↑u : Filter J) ≤ (atTop : Filter Jᵒᵈ) :=
    @Ultrafilter.of_le Jᵒᵈ (atTop : Filter Jᵒᵈ) hatTop
  let q : J → K × K := fun D => (xf D, yf D)
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcp
  obtain ⟨B0, -, hB_le⟩ := isCompact_univ.ultrafilter_le_nhds (u.map q) (by simp)
  rw [Ultrafilter.coe_map] at hB_le
  set x_star : K := B0.1 with hxstar
  set y_star : K := B0.2 with hystar
  have hq_lim : Tendsto q (↑u) (𝓝 B0) := hB_le
  have hx_lim : Tendsto xf (↑u) (𝓝 x_star) :=
    (continuous_fst.tendsto B0).comp hq_lim
  have hy_lim : Tendsto yf (↑u) (𝓝 y_star) :=
    (continuous_snd.tendsto B0).comp hq_lim
  -- The displacement `(xf D) - (yf D)` tends to `0` along `atTop`: for any nice `V₀`, all
  -- refinements `D ⊆ V₀` (i.e. `D ≥ V₀` in `Jᵒᵈ`) keep the displacement inside `V₀ ⊆ W`.
  have hdiff_atTop :
      Tendsto (fun D : J => (xf D : E) - (yf D : E)) (atTop : Filter Jᵒᵈ) (𝓝 (0 : E)) := by
    refine tendsto_iff_forall_eventually_mem.2 fun W hW => ?_
    obtain ⟨V₀, hV₀_nhds, hV₀_cl, hV₀_cvx, hV₀_symm, hV₀_sub⟩ :=
      exists_mem_nhds_isClosed_convex_neg_eq hW
    let hV₀J : J := ⟨V₀, hV₀_nhds, hV₀_cl, hV₀_cvx, hV₀_symm⟩
    filter_upwards [eventually_ge_atTop (OrderDual.toDual hV₀J)] with D hD
    have hle : (OrderDual.ofDual D) ≤ hV₀J := hD
    have hDsub : ((OrderDual.ofDual D : J) : Set E) ⊆ V₀ :=
      fun _ hx => Subtype.coe_le_coe.mpr hle hx
    exact hV₀_sub (hDsub (hxy (OrderDual.ofDual D)))
  have hdiff_u : Tendsto (fun D : J => (xf D : E) - (yf D : E)) (↑u) (𝓝 (0 : E)) :=
    hdiff_atTop.mono_left hu_le
  have hdiff_lim : Tendsto (fun D : J => (xf D : E) - (yf D : E)) (↑u)
      (𝓝 ((x_star : E) - (y_star : E))) :=
    (continuous_subtype_val.tendsto x_star |>.comp hx_lim).sub
      (continuous_subtype_val.tendsto y_star |>.comp hy_lim)
  have hxy_eq : (x_star : E) = (y_star : E) :=
    sub_eq_zero.mp (tendsto_nhds_unique hdiff_lim hdiff_u)
  have hyz_mem : ∀ D : J, (xf D, (yf D : E)) ∈ {p : K × E | p.2 ∈ Φ p.1} :=
    fun D => hyΦ D
  have hyz_lim : Tendsto (fun D : J => (xf D, (yf D : E))) (↑u) (𝓝 (x_star, (y_star : E))) :=
    Tendsto.prodMk_nhds hx_lim (continuous_subtype_val.tendsto y_star |>.comp hy_lim)
  have hy_star_mem : (y_star : E) ∈ Φ x_star :=
    hcg.mem_of_tendsto hyz_lim (Eventually.of_forall hyz_mem)
  exact ⟨x_star, hxy_eq ▸ hy_star_mem⟩
