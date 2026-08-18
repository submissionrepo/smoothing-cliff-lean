/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Filter Topology

/-!
# Measurable selection from singleton-a.e. correspondences

Given a set-valued map `F : Y → Set (EuclideanSpace ℝ (Fin n))` that is `ν`-almost-everywhere a
singleton, has a topologically closed graph, and is uniformly contained in a fixed compact set,
this file extracts a measurable function `f : Y → EuclideanSpace ℝ (Fin n)` and a measurable subset
`Y₀ ⊆ Y` of full measure where `F y = {f y}` exactly (not just `f y ∈ F y` a.e.).

## Main statements

* `exists_measurable_selection_of_singleton_ae` — a closed-graph, compact-bounded, singleton-a.e.
  correspondence admits a measurable selector agreeing with `F` on a full-measure set.

## Notes

The regularity hypotheses are not removable: For any non-measurable `g : Y → X` the correspondence
`F y := {g y}` is everywhere a singleton but admits no measurable selector. A closed graph together
with a uniform compact bound make `F` upper-hemicontinuous, which suffices to build a Borel
selector by coordinate-wise supremum on `Fin n`.

Compared to the Kuratowski–Ryll-Nardzewski selection theorem this version is strictly weaker
(Polish target replaced by `ℝⁿ`, Borel graph replaced by closed graph, compactness replaced by a
uniform compact bound), but it matches the hypotheses available for a closed-graph contact
correspondence on a fixed compact set.

## References

* Kechris, A. S. 1995. *Classical Descriptive Set Theory*. Springer-Verlag. Theorem 12.13.
* Kuratowski, Kazimierz, and Czeslaw Ryll-Nardzewski. 1965. “A General Theorem on Selectors.”
  *Bulletin De L'academie Polonaise Des Sciences, Serie Des Sciences Mathematiques, Astronomiques
  Et Physiques* 13 : 397–403.

## Tags

measurable selection, correspondence, upper-hemicontinuous, closed graph, descriptive set theory
-/

@[expose] public section

namespace MeasureTheory

/-! ### Upper-hemicontinuity infrastructure

For a set-valued `F : Y → Set X` with closed graph and `F y ⊆ K` for a fixed compact `K`, `F`
is *upper-hemicontinuous*: The pullback of any closed set is closed. -/

/-- For a closed-graph correspondence uniformly contained in a fixed compact `K`, each fiber `F y`
is compact (closed subset of `K`). -/
lemma isCompact_fibre_of_closedGraph_compactBound
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {F : Y → Set X}
    {K : Set X} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed : IsClosed {p : Y × X | p.2 ∈ F p.1})
    (y : Y) :
    IsCompact (F y) := by
  have hF_closed : IsClosed (F y) := by
    have h_slice : F y = {x : X | (y, x) ∈ {p : Y × X | p.2 ∈ F p.1}} := by
      ext; simp
    rw [h_slice]
    exact hF_graph_closed.preimage (continuous_const.prodMk continuous_id)
  exact hK_compact.of_isClosed_subset hF_closed (hF_sub_K y)

/-- For a closed-graph correspondence `F` uniformly contained in a compact `K` and any closed `C`,
the set `{y : F y ∩ C ≠ ∅}` is closed. -/
lemma isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {F : Y → Set X}
    {K : Set X} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed : IsClosed {p : Y × X | p.2 ∈ F p.1})
    {C : Set X} (hC_closed : IsClosed C) :
    IsClosed {y : Y | (F y ∩ C).Nonempty} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y₀ hy₀
  have h_empty : F y₀ ∩ C = ∅ := by
    have h_not : ¬ (F y₀ ∩ C).Nonempty := hy₀
    rwa [Set.not_nonempty_iff_eq_empty] at h_not
  have hAB_closed :
      IsClosed ({p : Y × X | p.2 ∈ F p.1} ∩ (Set.univ ×ˢ C)) :=
    hF_graph_closed.inter (isClosed_univ.prod hC_closed)
  have h_disjoint : ({y₀} : Set Y) ×ˢ K ⊆
      ({p : Y × X | p.2 ∈ F p.1} ∩ (Set.univ ×ˢ C))ᶜ := by
    rintro ⟨y, x⟩ ⟨hy, hx⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rintro ⟨h_in_F, _, h_in_C⟩
    exact (Set.not_nonempty_iff_eq_empty.mpr h_empty) ⟨x, h_in_F, h_in_C⟩
  obtain ⟨U, V, hU_open, _hV_open, hy₀_U, hK_V, hUV⟩ :=
    generalized_tube_lemma (s := ({y₀} : Set Y)) isCompact_singleton
      hK_compact hAB_closed.isOpen_compl h_disjoint
  refine Filter.mem_of_superset (hU_open.mem_nhds (hy₀_U rfl)) ?_
  intro y hy_U h_nonempty
  obtain ⟨x, hx_F, hx_C⟩ := h_nonempty
  have hx_K : x ∈ K := hF_sub_K y hx_F
  have h_in_compl := hUV (Set.mk_mem_prod hy_U (hK_V hx_K))
  exact h_in_compl ⟨hx_F, Set.mem_univ y, hx_C⟩

/-- The set `{y : F y ⊆ U}` is open whenever `U` is open and `F` is upper- hemicontinuous (closed
graph + uniform compact bound). -/
lemma isOpen_setOf_subset_of_closedGraph_compactBound
    {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {F : Y → Set X}
    {K : Set X} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed : IsClosed {p : Y × X | p.2 ∈ F p.1})
    {U : Set X} (hU_open : IsOpen U) :
    IsOpen {y : Y | F y ⊆ U} := by
  rw [← isClosed_compl_iff]
  have h_eq : {y : Y | F y ⊆ U}ᶜ = {y : Y | (F y ∩ Uᶜ).Nonempty} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.not_subset, Set.nonempty_def,
      Set.mem_inter_iff]
  rw [h_eq]
  exact isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
    hK_compact hF_sub_K hF_graph_closed hU_open.isClosed_compl

/-- For an upper-hemicontinuous compact-valued correspondence `F` and continuous `g : X → ℝ`,
`y ↦ sSup (g '' F y)` is Borel measurable.

When `F y = ∅`, `sSup` returns the convention value `0`; the result is still measurable. -/
lemma measurable_sSup_image_of_closedGraph_compactBound
    {Y X : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [TopologicalSpace X]
    {F : Y → Set X}
    {K : Set X} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed : IsClosed {p : Y × X | p.2 ∈ F p.1})
    {g : X → ℝ} (hg : Continuous g) :
    Measurable (fun y : Y => sSup (g '' F y)) := by
  apply measurable_of_Iio
  intro t
  have hY₁_closed : IsClosed {y : Y | (F y).Nonempty} := by
    have h := isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
      hK_compact hF_sub_K hF_graph_closed (C := Set.univ) isClosed_univ
    convert h using 1
    ext y; simp
  have h_open : IsOpen {y : Y | F y ⊆ g ⁻¹' Set.Iio t} :=
    isOpen_setOf_subset_of_closedGraph_compactBound
      hK_compact hF_sub_K hF_graph_closed (hg.isOpen_preimage _ isOpen_Iio)
  -- `sSup` characterization when `F y` is nonempty.
  have h_sup_lt :
      ∀ y, (F y).Nonempty → (sSup (g '' F y) < t ↔ F y ⊆ g ⁻¹' Set.Iio t) := by
    intro y hy_ne
    have h_compact : IsCompact (F y) :=
      isCompact_fibre_of_closedGraph_compactBound hK_compact hF_sub_K
        hF_graph_closed y
    have h_bdd : BddAbove (g '' F y) := (h_compact.image hg).bddAbove
    -- The sup is attained at some `xs ∈ F y` (compact domain, continuous `g`).
    obtain ⟨xs, hxs_F, h_sup_eq, _⟩ := h_compact.exists_sSup_image_eq_and_ge hy_ne hg.continuousOn
    refine ⟨fun h_lt x hx_F => ?_, fun h_sub => ?_⟩
    · have h_g_le : g x ≤ sSup (g '' F y) :=
        le_csSup h_bdd ⟨x, hx_F, rfl⟩
      simp only [Set.mem_preimage, Set.mem_Iio]
      linarith
    · rw [h_sup_eq]
      simpa [Set.mem_preimage, Set.mem_Iio] using h_sub hxs_F
  by_cases ht : 0 < t
  · -- {y : sSup < t} = {y : F y ⊆ g⁻¹[Iio t]} (open).
    have h_eq : (fun y => sSup (g '' F y)) ⁻¹' Set.Iio t
        = {y : Y | F y ⊆ g ⁻¹' Set.Iio t} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq]
      by_cases hF_ne : (F y).Nonempty
      · exact h_sup_lt y hF_ne
      · rw [Set.not_nonempty_iff_eq_empty] at hF_ne
        rw [hF_ne, Set.image_empty, Real.sSup_empty]
        exact iff_of_true ht (Set.empty_subset _)
    rw [h_eq]
    exact h_open.measurableSet
  · -- {y : sSup < t} = {F y nonempty} ∩ {y : F y ⊆ g⁻¹[Iio t]} (closed ∩ open).
    push Not at ht
    have h_eq : (fun y => sSup (g '' F y)) ⁻¹' Set.Iio t
        = {y : Y | (F y).Nonempty} ∩ {y : Y | F y ⊆ g ⁻¹' Set.Iio t} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_inter_iff, Set.mem_setOf_eq]
      by_cases hF_ne : (F y).Nonempty
      · rw [h_sup_lt y hF_ne]
        exact ⟨fun h => ⟨hF_ne, h⟩, fun h => h.2⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hF_ne
        rw [hF_ne, Set.image_empty, Real.sSup_empty]
        refine iff_of_false (fun h0lt => ?_) (fun ⟨h_ne, _⟩ => ?_)
        · linarith
        · exact h_ne.ne_empty rfl
    rw [h_eq]
    exact hY₁_closed.measurableSet.inter h_open.measurableSet

/-! ### Main theorem -/

/-- **Measurable selection from a singleton-a.e. closed-graph compact-valued correspondence.**

Let `Y` be a Borel-measurable topological space and `F : Y →
Set (EuclideanSpace ℝ (Fin n))` a
set-valued map satisfying:

* `hK_compact`: There is a compact `K ⊆ ℝⁿ` ...
* `hF_sub_K`:  ... that contains every `F y`;
* `hF_graph_closed`: The graph `{(y, x) : x ∈ F y}` is closed in `Y × ℝⁿ`;
* `hF_singleton`: `F y` is a singleton for `ν`-a.e. `y`.

Then there exists a measurable `f : Y → ℝⁿ` and a measurable subset `Y₀ ⊆ Y` of full `ν`-measure on
which `F y = {f y}` exactly. -/
theorem exists_measurable_selection_of_singleton_ae
    {n : ℕ}
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {ν : MeasureTheory.Measure Y}
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_singleton : ∀ᵐ y ∂ν, ∃ x, F y = {x}) :
    ∃ f : Y → EuclideanSpace ℝ (Fin n), Measurable f ∧
      ∃ Y₀ : Set Y, MeasurableSet Y₀ ∧ ν Y₀ᶜ = 0 ∧ ∀ y ∈ Y₀, F y = {f y} := by
  -- Coordinate-wise sup gives a measurable selector.
  let coords : Y → Fin n → ℝ := fun y i =>
    sSup ((fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) '' F y)
  have h_coord_meas : ∀ i, Measurable (fun y => coords y i) := fun i =>
    measurable_sSup_image_of_closedGraph_compactBound hK_compact hF_sub_K
      hF_graph_closed (PiLp.continuous_apply 2 _ i)
  have h_coords_meas : Measurable coords :=
    measurable_pi_iff.mpr h_coord_meas
  let f : Y → EuclideanSpace ℝ (Fin n) := fun y => WithLp.toLp 2 (coords y)
  have hf_meas : Measurable f :=
    (PiLp.continuous_toLp 2 _).measurable.comp h_coords_meas
  -- Diameter: Fsq(y) := F y × F y, then sSup of ‖x - x'‖.
  let Fsq : Y → Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun y => F y ×ˢ F y
  have h_Fsq_graph_closed :
      IsClosed {p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
        p.2 ∈ Fsq p.1} := by
    have h₁ :
        Continuous fun p : Y × (EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin n)) => (p.1, p.2.1) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have h₂ :
        Continuous fun p : Y × (EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin n)) => (p.1, p.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    have h_set_eq :
        {p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
            p.2 ∈ Fsq p.1}
          = ((fun p : Y × (EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin n)) => (p.1, p.2.1)) ⁻¹'
              {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) ∩
            ((fun p : Y × (EuclideanSpace ℝ (Fin n) ×
                EuclideanSpace ℝ (Fin n)) => (p.1, p.2.2)) ⁻¹'
              {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) := by
      ext ⟨y, x, x'⟩
      simp [Fsq]
    rw [h_set_eq]
    exact (hF_graph_closed.preimage h₁).inter (hF_graph_closed.preimage h₂)
  have h_Fsq_sub : ∀ y, Fsq y ⊆ K ×ˢ K :=
    fun y => Set.prod_mono (hF_sub_K y) (hF_sub_K y)
  have h_Ksq_compact : IsCompact (K ×ˢ K) := hK_compact.prod hK_compact
  have h_diff_norm_cont :
      Continuous fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖p.1 - p.2‖ :=
    (continuous_fst.sub continuous_snd).norm
  let diamF : Y → ℝ := fun y =>
    sSup ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖p.1 - p.2‖) '' Fsq y)
  have h_diamF_meas : Measurable diamF :=
    measurable_sSup_image_of_closedGraph_compactBound
      h_Ksq_compact h_Fsq_sub h_Fsq_graph_closed h_diff_norm_cont
  -- Y₀ := {F y nonempty} ∩ {diamF y ≤ 0}.
  let Y₀ : Set Y := {y | (F y).Nonempty} ∩ {y | diamF y ≤ 0}
  have hY_ne_meas : MeasurableSet {y : Y | (F y).Nonempty} := by
    have h := isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
      hK_compact hF_sub_K hF_graph_closed (C := Set.univ) isClosed_univ
    have h_eq : {y : Y | (F y ∩ Set.univ).Nonempty} = {y : Y | (F y).Nonempty} := by
      ext y; simp
    rw [h_eq] at h
    exact h.measurableSet
  have hY₀_meas : MeasurableSet Y₀ :=
    hY_ne_meas.inter (h_diamF_meas measurableSet_Iic)
  -- When `F y = {x}`, `diamF y = 0`.
  have h_diamF_singleton : ∀ y x, F y = {x} → diamF y = 0 := by
    intro y x hx
    have h_image :
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖p.1 - p.2‖) '' Fsq y = {0} := by
      have hx_mem : x ∈ F y := by rw [hx]; rfl
      ext z
      refine ⟨?_, ?_⟩
      · rintro ⟨p, ⟨ha, hb⟩, rfl⟩
        rw [hx, Set.mem_singleton_iff] at ha hb
        simp [ha, hb]
      · rintro rfl
        exact ⟨(x, x), ⟨hx_mem, hx_mem⟩, by simp⟩
    change sSup ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖p.1 - p.2‖) '' Fsq y) = 0
    rw [h_image]
    exact csSup_singleton 0
  -- Y₀ᶜ ⊆ {y : ¬ (∃ x, F y = {x})}, which is ν-null.
  have hY₀_full : ν Y₀ᶜ = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hF_singleton
    intro y hy
    have hy' : ¬ ((F y).Nonempty ∧ diamF y ≤ 0) := hy
    rintro ⟨x, hx⟩
    have hF_ne : (F y).Nonempty := by rw [hx]; exact ⟨x, rfl⟩
    have h_diam_zero : diamF y = 0 := h_diamF_singleton y x hx
    exact hy' ⟨hF_ne, le_of_eq h_diam_zero⟩
  refine ⟨f, hf_meas, Y₀, hY₀_meas, hY₀_full, ?_⟩
  -- Final: on Y₀, F y = {f y}.
  intro y ⟨hy_ne, hy_diam⟩
  -- F y is a nonempty subsingleton.
  have h_compact : IsCompact (F y) :=
    isCompact_fibre_of_closedGraph_compactBound hK_compact hF_sub_K
      hF_graph_closed y
  -- The image whose sup is `diamF y` is compact, hence bounded above; reused below.
  have h_diam_bdd :
      BddAbove ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖p.1 - p.2‖) '' Fsq y) :=
    ((h_compact.prod h_compact).image h_diff_norm_cont).bddAbove
  -- diamF y ≥ 0 always.
  have h_diam_nn : 0 ≤ diamF y := by
    obtain ⟨x, hx⟩ := hy_ne
    have h_zero_in : (0 : ℝ) ∈
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖p.1 - p.2‖) '' Fsq y := by
      refine ⟨(x, x), ⟨hx, hx⟩, by simp⟩
    exact le_csSup h_diam_bdd h_zero_in
  -- So diamF y = 0.
  have h_diam_eq : diamF y = 0 := le_antisymm hy_diam h_diam_nn
  -- F y is a subsingleton.
  have h_subsing : ∀ a ∈ F y, ∀ b ∈ F y, a = b := by
    intro a ha b hb
    have h_ab_in :
        ‖a - b‖ ∈ (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖p.1 - p.2‖) '' Fsq y :=
      ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    have h_le_diam : ‖a - b‖ ≤ diamF y :=
      le_csSup h_diam_bdd h_ab_in
    have h_norm_zero : ‖a - b‖ = 0 :=
      le_antisymm (h_diam_eq ▸ h_le_diam) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  -- Pick any x* ∈ F y, then F y = {x*}.
  obtain ⟨xs, hxs⟩ := hy_ne
  have hF_eq : F y = {xs} := by
    ext z
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · rw [Set.mem_singleton_iff]
      exact (h_subsing z hz xs hxs)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact hxs
  -- Compute f y = xs.
  have h_coords_eq : ∀ i, coords y i = xs.ofLp i := by
    intro i
    change sSup ((fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) '' F y) = xs.ofLp i
    rw [hF_eq]
    simp [csSup_singleton]
  have h_f_eq : f y = xs := by
    change WithLp.toLp 2 (coords y) = xs
    have h_fun_eq : coords y = xs.ofLp := funext h_coords_eq
    rw [h_fun_eq, WithLp.toLp_ofLp]
  rw [hF_eq, h_f_eq]

end MeasureTheory
