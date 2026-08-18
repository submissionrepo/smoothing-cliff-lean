/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.PolishRefinement
public import Mathlib

/-!
# Lusin's continuity theorem and Carathéodory approximation

**Lusin's theorem**: A Borel-measurable map from a Polish space carrying a finite Borel measure
into a second-countable space is continuous on a compact set whose complement has measure at most
`ε`.

On top of Lusin this file builds a Carathéodory-function toolkit for payoff continuity in
distributional-strategy equilibrium existence. A jointly measurable function `u : T × A → ℝ`
continuous in `a ∈ A` (compact metrizable) for each fixed `t` packages into a measurable map
`T → C(A, ℝ)`, and Lusin together with Tietze extension produces a bounded continuous approximant
agreeing with `u` on a compact slab whose base has co-measure `≤ ε` (Milgrom and Weber's condition
R1*).

## Main statements

* `MeasureTheory.Measurable.exists_isCompact_continuousOn` — Lusin's continuity theorem.
* `MeasureTheory.measurable_continuousMapMk` — a Carathéodory function packages measurably into
  `C(A, ℝ)`.
* `MeasureTheory.exists_boundedContinuous_eqOn_compact_prod` — bounded continuous approximation of
  a Carathéodory integrand off a compact slab of small co-measure (R1*).

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

lusin, luzin, caratheodory, tietze, polish space
-/

@[expose] public section

open scoped ENNReal
open TopologicalSpace

namespace MeasureTheory

/-- On a set `K` compact for a finer topology `t'`, a `t'`-continuous map is `ContinuousOn K` for
any coarser `T2` topology `t`.

The `T2` hypothesis is on the coarser topology `t`, not on the codomain: A `t'`-continuous
injection of a `t'`-compact set into a non-`T2` coarsening can fail to be `t`-continuous. -/
private theorem continuousOn_of_finer_compact_t2
    {Y Z : Type*} (t t' : TopologicalSpace Y) [TopologicalSpace Z]
    (ht2 : @T2Space Y t) (hle : t' ≤ t) {f : Y → Z} {K : Set Y}
    (hK : @IsCompact Y t' K) (hf : @Continuous Y Z t' _ f) :
    @ContinuousOn Y Z t _ f K := by
  rw [@continuousOn_iff_continuous_restrict Y Z t _ f K]
  have hcs : @CompactSpace ↥K (TopologicalSpace.induced Subtype.val t') :=
    @isCompact_iff_compactSpace Y t' K |>.mp hK
  have ht2sub : @T2Space ↥K (TopologicalSpace.induced Subtype.val t) :=
    @T2Space.of_injective_continuous ↥K Y (TopologicalSpace.induced Subtype.val t) t ht2
      Subtype.val Subtype.val_injective (@continuous_induced_dom ↥K Y Subtype.val t)
  have hle_sub : (TopologicalSpace.induced (Subtype.val (p := (· ∈ K))) t')
      ≤ TopologicalSpace.induced Subtype.val t := induced_mono hle
  have hid : @Continuous ↥K ↥K (TopologicalSpace.induced Subtype.val t')
      (TopologicalSpace.induced Subtype.val t) id := continuous_id_iff_le.mpr hle_sub
  -- The compact-to-T2 bijection `id : t'-sub → t-sub` has continuous inverse, so the two
  -- subspace topologies agree.
  have htop_eq : (TopologicalSpace.induced (Subtype.val (p := (· ∈ K))) t)
      = TopologicalSpace.induced Subtype.val t' := by
    refine le_antisymm ?_ hle_sub
    have hsymm := @Continuous.continuous_symm_of_equiv_compact_to_t2 ↥K ↥K
      (TopologicalSpace.induced Subtype.val t') (TopologicalSpace.induced Subtype.val t)
      hcs ht2sub (Equiv.refl ↥K) hid
    rw [show ((Equiv.refl ↥K).symm : ↥K → ↥K) = id from rfl] at hsymm
    exact (@continuous_id_iff_le ↥K (TopologicalSpace.induced Subtype.val t)
      (TopologicalSpace.induced Subtype.val t')).mp hsymm
  change @Continuous ↥K Z (TopologicalSpace.induced Subtype.val t) _ (K.restrict f)
  rw [htop_eq]
  exact hf.comp (@continuous_subtype_val Y t' _)

/-- **Lusin's continuity theorem.** A Borel-measurable map from a Polish space with a finite Borel
measure into a second-countable (opens-measurable) space is continuous on a compact set whose
complement has measure at most `ε`. -/
theorem Measurable.exists_isCompact_continuousOn
    {Y Z : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    {f : Y → Z} (hf : Measurable f) (μ : Measure Y) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set Y, IsCompact K ∧ μ Kᶜ ≤ ε ∧ ContinuousOn f K := by
  -- Name the ambient topology before the Polish refinement, so instance synthesis cannot pick `t'`
  -- when we need the coarser topology `tY`.
  let tY : TopologicalSpace Y := inferInstance
  have htY2 : @T2Space Y tY := inferInstance
  obtain ⟨t', ht'_le, ht'_polish, ht'_cont, hborel⟩ :=
    exists_finer_polish_continuous_countable (Y := Y) (ι := Unit) (X := fun _ => Z)
      (fun _ => f) (fun _ => hf)
  have hf_t'_cont : @Continuous Y Z t' _ f := ht'_cont ()
  have hborelSpace : @BorelSpace Y t' _ := ⟨BorelSpace.measurable_eq.trans hborel.symm⟩
  have htight : @IsTightMeasureSet Y _ t' {μ} :=
    @isTightMeasureSet_singleton Y _ t'
      (@TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace Y t'
        (@PolishSpace.toIsCompletelyMetrizableSpace Y t' ht'_polish))
      (@PolishSpace.toSecondCountableTopology Y t' ht'_polish)
      hborelSpace μ _
  obtain ⟨K, hK_t'_compact, hK_meas⟩ :=
    (@isTightMeasureSet_iff_exists_isCompact_measure_compl_le Y _ {μ} t').1
      htight ε (pos_iff_ne_zero.2 hε)
  have hμK : μ Kᶜ ≤ ε := hK_meas μ rfl
  have ht'_le_tY : t' ≤ tY := ht'_le
  have hK_tY_compact : @IsCompact Y tY K := by
    have := @IsCompact.image Y Y t' tY K id hK_t'_compact (continuous_id_of_le ht'_le_tY)
    rwa [Set.image_id] at this
  have hcontOn : @ContinuousOn Y Z tY _ f K :=
    @continuousOn_of_finer_compact_t2 Y Z tY t' _ htY2 ht'_le_tY f K hK_t'_compact hf_t'_cont
  exact ⟨K, hK_tY_compact, hμK, hcontOn⟩

/-- For a fixed `h : C(A, ℝ)`, the map `t ↦ dist (⟨u (t, ·), hcont t⟩) h` is measurable. -/
private theorem measurable_dist_continuousMapMk
    {T A : Type*} [MeasurableSpace T] [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    {u : T × A → ℝ} (hmeas : Measurable u) (hcont : ∀ t, Continuous fun a => u (t, a))
    (h : C(A, ℝ)) :
    Measurable fun t => dist (⟨fun a => u (t, a), hcont t⟩ : C(A, ℝ)) h := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense A
  have hpt_cont : ∀ t : T, Continuous fun a => dist (u (t, a)) (h a) := fun t =>
    (hcont t).dist h.continuous
  have key : (fun t => dist (⟨fun a => u (t, a), hcont t⟩ : C(A, ℝ)) h)
      = fun t => ⨆ a : ↥D, dist (u (t, (a : A))) (h (a : A)) := by
    funext t
    rw [ContinuousMap.dist_eq_iSup]
    exact (hD_dense.ciSup' (f := fun a => dist (u (t, a)) (h a)) (hpt_cont t)).symm
  rw [key]
  have : Countable ↥D := hD_count.to_subtype
  refine Measurable.iSup (fun a => ?_)
  exact (hmeas.comp (measurable_id.prodMk measurable_const)).dist measurable_const

/-- **Carathéodory packaging.** A jointly measurable function `T × A → ℝ`, continuous in the second
argument over a compact metrizable `A`, is a measurable map into `C(A, ℝ)`.

The Borel σ-algebra on `C(A, ℝ)` (a Polish space under the sup metric) is supplied explicitly so
the statement does not depend on a global `MeasurableSpace C(A, ℝ)` instance. -/
theorem measurable_continuousMapMk
    {T A : Type*} [MeasurableSpace T] [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace C(A, ℝ)] [BorelSpace C(A, ℝ)]
    {u : T × A → ℝ} (hmeas : Measurable u) (hcont : ∀ t, Continuous fun a => u (t, a)) :
    Measurable fun t => (⟨fun a => u (t, a), hcont t⟩ : C(A, ℝ)) := by
  set G : T → C(A, ℝ) := fun t => (⟨fun a => u (t, a), hcont t⟩ : C(A, ℝ)) with hG
  refine measurable_of_isClosed' (fun S hS_closed hS_ne _hS_ne_univ => ?_)
  obtain ⟨D, hD_sub, hD_count, hS_sub_closure⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hclosure_D : closure D = S :=
    le_antisymm (hS_closed.closure_subset_iff.mpr hD_sub) hS_sub_closure
  have hmem : ∀ t, G t ∈ S ↔ Metric.infDist (G t) D = 0 := by
    intro t
    rw [hS_closed.mem_iff_infDist_zero hS_ne, ← hclosure_D, Metric.infDist_closure]
  have hinfDist_meas : Measurable fun t => Metric.infDist (G t) D := by
    have hrw : (fun t => Metric.infDist (G t) D)
        = fun t => ⨅ d : ↥D, dist (G t) (d : C(A, ℝ)) := by
      funext t; rw [Metric.infDist_eq_iInf]
    rw [hrw]
    have : Countable ↥D := hD_count.to_subtype
    refine Measurable.iInf (fun d => ?_)
    exact measurable_dist_continuousMapMk hmeas hcont (d : C(A, ℝ))
  have hpre : G ⁻¹' S = {t | Metric.infDist (G t) D = 0} := by ext t; exact hmem t
  rw [hpre]
  exact hinfDist_meas (measurableSet_singleton 0)

/-- **Bounded continuous approximation off a compact slab** (Milgrom–Weber's R1*). A bounded
Carathéodory integrand `u : T × A → ℝ` (jointly measurable, continuous in `a`) over a Polish `T`
with finite Borel measure `μ` and compact metrizable `A` agrees with some bounded continuous
`V : T × A →ᵇ ℝ`, with the same bound, on a slab `K × A` whose base has co-measure `≤ ε`. -/
theorem exists_boundedContinuous_eqOn_compact_prod
    {T A : Type*} [TopologicalSpace T] [PolishSpace T] [MeasurableSpace T] [BorelSpace T]
    [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure T) [IsFiniteMeasure μ]
    {u : T × A → ℝ} (hmeas : Measurable u) (hcont : ∀ t, Continuous fun a => u (t, a))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p, |u p| ≤ B) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (K : Set T) (V : BoundedContinuousFunction (T × A) ℝ), IsCompact K ∧ μ Kᶜ ≤ ε ∧
      ‖V‖ ≤ B ∧ ∀ p : T × A, p.1 ∈ K → V p = u p := by
  classical
  letI : MeasurableSpace C(A, ℝ) := borel _
  letI : BorelSpace C(A, ℝ) := ⟨rfl⟩
  set F : T → C(A, ℝ) := fun t => (⟨fun a => u (t, a), hcont t⟩ : C(A, ℝ)) with hF
  have hF_meas : Measurable F := measurable_continuousMapMk hmeas hcont
  obtain ⟨K, hK_compact, hμK, hF_contOn⟩ :=
    Measurable.exists_isCompact_continuousOn hF_meas μ hε
  set S : Set (T × A) := K ×ˢ (Set.univ : Set A) with hS
  have hS_compact : IsCompact S := hK_compact.prod isCompact_univ
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hu_contOn : ContinuousOn u S := by
    have heq : ∀ p ∈ S, u p = (F p.1) p.2 := fun p _ => rfl
    refine ContinuousOn.congr ?_ heq
    have hF_fst : ContinuousOn (fun p : T × A => F p.1) S :=
      hF_contOn.comp continuousOn_fst (fun p hp => hp.1)
    exact hF_fst.eval continuousOn_snd
  have hu_restr_cont : Continuous (S.restrict u) := continuousOn_iff_continuous_restrict.1 hu_contOn
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.1 hS_compact
  set f₀ : BoundedContinuousFunction (↥S) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨S.restrict u, hu_restr_cont⟩ with hf₀
  have hf₀_apply : ∀ x : ↥S, f₀ x = u (x : T × A) := fun x => rfl
  obtain ⟨V, hV_norm, hV_restr⟩ :=
    BoundedContinuousFunction.exists_norm_eq_restrict_eq_of_closed f₀ hS_closed
  refine ⟨K, V, hK_compact, hμK, ?_, ?_⟩
  · rw [hV_norm]
    -- The slab `↥S` can be empty when `K = ∅`; case on whether `T × A` is nonempty.
    rcases isEmpty_or_nonempty (T × A) with hPe | hPne
    · haveI : IsEmpty ↥S := Subtype.isEmpty_of_false (fun p _ => (hPe.false p).elim)
      rw [BoundedContinuousFunction.norm_eq_zero_of_empty f₀]
      exact hB0
    · rw [BoundedContinuousFunction.norm_le hB0]
      intro x
      rw [hf₀_apply x, Real.norm_eq_abs]
      exact hB (x : T × A)
  · intro p hp
    have hpS : p ∈ S := ⟨hp, Set.mem_univ _⟩
    have hVp : V p = (V.restrict S) ⟨p, hpS⟩ := rfl
    rw [hVp, hV_restr, hf₀_apply ⟨p, hpS⟩]

end MeasureTheory
