/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Portmanteau integral helpers

This file collects weak-convergence facts for expectations of bounded upper-semicontinuous
integrands. Mathlib already supplies the **portmanteau** closed-set and open-set inequalities and
continuity of finite product probability measures; the results below package the expectation-level
consequence for finite-market signal design: A bounded upper-semicontinuous integrand remains upper
semicontinuous after integration against weakly convergent probability laws supported on a common
compact set.

## Main statements

* `continuous_pi_const` — continuity of the constant-coordinate product-measure map.
* `upperSemicontinuousOn_integral_of_bounded_upperSemicontinuousOn_compactSupport` — integration
  preserves upper semicontinuity for bounded, compactly supported integrands.
* `upperSemicontinuousOn_integral_comp_of_bounded_upperSemicontinuousOn_compactSupport` — the
  composed-kernel version of the same.

## Tags

portmanteau, weak convergence, upper semicontinuous, probability measure
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

noncomputable section

variable {ι X : Type*}

/-- The i.i.d. finite-product probability law depends continuously on its common marginal. -/
@[fun_prop]
theorem continuous_pi_const [Fintype ι] [MeasurableSpace X] [TopologicalSpace X]
    [SecondCountableTopology X] [PseudoMetrizableSpace X] [OpensMeasurableSpace X] :
    Continuous (fun μ : ProbabilityMeasure X =>
      ProbabilityMeasure.pi (fun _ : ι => μ)) :=
  ProbabilityMeasure.continuous_pi.comp (_root_.continuous_pi fun _ => continuous_id)

/-- **Portmanteau integral inequality** for bounded upper-semicontinuous integrands with common
compact support: The expectation functional `μ ↦ ∫ f ∂μ` is upper semicontinuous on the set of
probability measures concentrated on `K`, for `f` bounded and upper semicontinuous on `K`. -/
theorem upperSemicontinuousOn_integral_of_bounded_upperSemicontinuousOn_compactSupport
    {X : Type*} [TopologicalSpace X] [T2Space X] [PseudoMetrizableSpace X] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ}
    (hfBounded : ∃ B : ℝ, ∀ x ∈ K, |f x| ≤ B)
    (hfUSC : UpperSemicontinuousOn f K) :
    UpperSemicontinuousOn
      (fun μ : ProbabilityMeasure X => ∫ x, f x ∂(μ : Measure X))
      {μ : ProbabilityMeasure X | (μ : Measure X) K = 1} := by
  classical
  -- Setup constants. WLOG `B ≥ 0`.
  obtain ⟨B₀, hB₀⟩ := hfBounded
  set B : ℝ := max B₀ 0
  have hB_nn : (0 : ℝ) ≤ B := le_max_right _ _
  have hB : ∀ x ∈ K, |f x| ≤ B := fun x hx => (hB₀ x hx).trans (le_max_left _ _)
  have hfb_lower : ∀ x ∈ K, -B ≤ f x := fun x hx => (abs_le.mp (hB x hx)).1
  have hfb_upper : ∀ x ∈ K, f x ≤ B := fun x hx => (abs_le.mp (hB x hx)).2
  have hKclosed : IsClosed K := hK.isClosed
  have hKmeas : MeasurableSet K := hKclosed.measurableSet
  -- The shifted, indicator-restricted function `gK := indicator K (f + B)`.
  set gK : X → ℝ := fun x => if x ∈ K then f x + B else 0 with hgKdef
  have hgK_usc : UpperSemicontinuous gK := by
    rw [hgKdef]
    refine upperSemicontinuous_iff_isClosed_preimage.2 ?_
    intro a
    by_cases ha : a ≤ 0
    · have : {x | a ≤ (if x ∈ K then f x + B else 0)} = Set.univ := by
        ext x
        by_cases hx : x ∈ K
        · simp [hx]
          -- needs `0 ≤ f x + B`
          have hx_lower : -B ≤ f x := hfb_lower x hx
          linarith
        · simp [hx, ha]
      change IsClosed {x | a ≤ if x ∈ K then f x + B else 0}
      rw [this]
      exact isClosed_univ
    · have hapos : 0 < a := lt_of_not_ge ha
      have :
          {x | a ≤ (if x ∈ K then f x + B else 0)}
            = K ∩ {x | a ≤ f x + B} := by
        ext x
        by_cases hx : x ∈ K
        · simp [hx]
        · simp [hx, hapos.not_ge]
      change IsClosed {x | a ≤ if x ∈ K then f x + B else 0}
      rw [this]
      have hCompact_shift : IsCompact (K ∩ f ⁻¹' Ici (a - B)) :=
        hfUSC.isCompact_inter_preimage_Ici hK (a - B)
      have hClosed_shift : IsClosed (K ∩ f ⁻¹' Ici (a - B)) :=
        hCompact_shift.isClosed
      convert hClosed_shift using 1
      ext x
      simp
  have hgK_meas : Measurable gK :=
    hgK_usc.measurable
  have hgK_nn : ∀ x, 0 ≤ gK x := by
    intro x
    by_cases hxK : x ∈ K
    · have := hfb_lower x hxK
      simp only [gK, hxK, ite_true]; linarith
    · simp [gK, hxK]
  have hgK_le : ∀ x, gK x ≤ 2 * B := by
    intro x
    by_cases hxK : x ∈ K
    · have := hfb_upper x hxK
      simp only [gK, hxK, ite_true]; linarith
    · simp only [gK, hxK, ite_false]; linarith
  have hgK_norm_le : ∀ x, ‖gK x‖ ≤ 2 * B := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hgK_nn x)]; exact hgK_le x
  -- Concentration: for `μ ∈ S`, `μ`-a.e. point lies in `K`.
  have hμK_ae : ∀ μ : ProbabilityMeasure X, (μ : Measure X) K = 1 →
      ∀ᵐ x ∂(μ : Measure X), x ∈ K := by
    intro μ hμK
    have hKcompl_zero : (μ : Measure X) Kᶜ = 0 :=
      (prob_compl_eq_zero_iff hKmeas).mpr hμK
    rw [ae_iff]
    exact hKcompl_zero
  -- Integrability of `gK` against any probability measure.
  have hgK_int : ∀ μ : ProbabilityMeasure X, Integrable gK (μ : Measure X) := fun μ =>
    ⟨hgK_meas.aestronglyMeasurable,
      (hasFiniteIntegral_const (2 * B)).mono' (Filter.Eventually.of_forall hgK_norm_le)⟩
  -- For `μ ∈ S`: `∫ f dμ = ∫ gK dμ - B`.
  have hint_eq : ∀ μ : ProbabilityMeasure X, (μ : Measure X) K = 1 →
      ∫ x, f x ∂(μ : Measure X) = ∫ x, gK x ∂(μ : Measure X) - B := by
    intro μ hμ
    have hae := hμK_ae μ hμ
    have hf_ae : (fun x => f x) =ᵐ[(μ : Measure X)] (fun x => gK x - B) := by
      filter_upwards [hae] with x hxK
      simp only [gK, hxK, ite_true]; ring
    rw [integral_congr_ae hf_ae, integral_sub (hgK_int μ) (integrable_const _),
        integral_const, probReal_univ, one_smul]
  -- Each level set is closed (and hence measurable).
  have hClosed_levelset : ∀ t : ℝ, 0 < t → IsClosed {x : X | t ≤ gK x} := by
    intro t ht
    have hset_eq : {x : X | t ≤ gK x} = K ∩ f ⁻¹' Set.Ici (t - B) := by
      ext x
      by_cases hxK : x ∈ K
      · simp only [Set.mem_setOf_eq, gK, hxK, ite_true, Set.mem_inter_iff,
          Set.mem_preimage, Set.mem_Ici, true_and]
        constructor <;> intro h <;> linarith
      · simp only [Set.mem_setOf_eq, gK, hxK, ite_false, Set.mem_inter_iff, false_and,
          iff_false, not_le]
        linarith
    rw [hset_eq]
    obtain ⟨v, hv_closed, hv_eq⟩ := upperSemicontinuousOn_iff_preimage_Ici.mp hfUSC (t - B)
    rw [hv_eq]
    exact hKclosed.inter hv_closed
  have hMeas_levelset : ∀ t : ℝ, 0 < t → MeasurableSet {x : X | t ≤ gK x} := fun t ht =>
    (hClosed_levelset t ht).measurableSet
  -- Above `2B`, the level set is empty.
  have hLevel_empty : ∀ t : ℝ, 2 * B < t → {x : X | t ≤ gK x} = ∅ := by
    intro t ht
    ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have := hgK_le x; linarith
  -- Layer-cake (lintegral form): ∫⁻ gK dμ = ∫⁻ t in Ioi 0, μ {gK ≥ t}.
  have hlayer_lintegral : ∀ μ : ProbabilityMeasure X,
      ∫⁻ x, ENNReal.ofReal (gK x) ∂(μ : Measure X) =
        ∫⁻ t in Set.Ioi (0 : ℝ), (μ : Measure X) {x | t ≤ gK x} :=
    fun μ => lintegral_eq_lintegral_meas_le _ (Filter.Eventually.of_forall hgK_nn)
      hgK_meas.aemeasurable
  -- Bochner integral = ENNReal.toReal of lintegral, since gK ≥ 0 and integrable.
  have hBochner_eq : ∀ μ : ProbabilityMeasure X,
      ∫ x, gK x ∂(μ : Measure X) =
        (∫⁻ x, ENNReal.ofReal (gK x) ∂(μ : Measure X)).toReal := fun μ =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgK_nn)
      hgK_meas.aestronglyMeasurable
  -- Restrict the layer-cake to Ioc 0 (2B): outside this range the integrand is 0.
  have hlayer_Ioc : ∀ μ : ProbabilityMeasure X,
      ∫⁻ x, ENNReal.ofReal (gK x) ∂(μ : Measure X) =
        ∫⁻ t in Set.Ioc (0 : ℝ) (2 * B), (μ : Measure X) {x | t ≤ gK x} := by
    intro μ
    rw [hlayer_lintegral μ]
    -- Split Ioi 0 = Ioc 0 (2B) ∪ Ioi (2B)
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) (2 * B) ∪ Set.Ioi (2 * B) := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht
        rcases le_or_gt t (2 * B) with hle | hgt
        · exact Or.inl ⟨ht, hle⟩
        · exact Or.inr hgt
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · linarith
    rw [hsplit, MeasureTheory.lintegral_union measurableSet_Ioi (by
        rw [Set.disjoint_left]
        intro t ⟨_, htle⟩ htgt
        exact absurd htgt (not_lt.mpr htle))]
    -- Top piece is zero.
    have htop : ∫⁻ t in Set.Ioi (2 * B), (μ : Measure X) {x | t ≤ gK x} = 0 := by
      rw [setLIntegral_congr_fun (g := fun _ => 0) measurableSet_Ioi]
      · simp
      · intro t ht
        simp only
        rw [hLevel_empty t ht]; simp
    rw [htop, add_zero]
  -- Upper semicontinuity at each point of the constraint set, via the frequently characterization.
  refine UpperSemicontinuousOn.of_frequently (fun μ₀ hμ₀ y hy_freq => ?_)
  by_contra hlt
  push Not at hlt
  -- Translate to `gK`: `∫ gK dμ₀ < y + B`.
  set y' : ℝ := y + B
  have hμ₀_eq : ∫ x, f x ∂(μ₀ : Measure X) = ∫ x, gK x ∂(μ₀ : Measure X) - B :=
    hint_eq μ₀ hμ₀
  have hlt' : ∫ x, gK x ∂(μ₀ : Measure X) < y' := by
    rw [hμ₀_eq] at hlt; linarith
  -- Define the constraint set and translate `hy_freq` to gK frequently.
  set S : Set (ProbabilityMeasure X) :=
    {μ : ProbabilityMeasure X | μ.toMeasure K = 1}
  have hμ₀S : μ₀ ∈ S := hμ₀
  have hyle_freq : ∃ᶠ ν in 𝓝[S] μ₀, y' ≤ ∫ x, gK x ∂ν.toMeasure := by
    have h_evS : ∀ᶠ ν in 𝓝[S] μ₀, ν ∈ S := self_mem_nhdsWithin
    refine hy_freq.mp (h_evS.mono ?_)
    intro ν hνS hyle
    have hν_K : ν.toMeasure K = 1 := hνS
    have := hint_eq ν hν_K
    rw [this] at hyle
    linarith
  -- Combine: frequently `(y' ≤ ∫ gK dν) ∧ ν ∈ S`.
  have hcomb : ∃ᶠ ν in 𝓝[S] μ₀,
      (y' ≤ ∫ x, gK x ∂ν.toMeasure) ∧ (ν.toMeasure K = 1) :=
    hyle_freq.and_eventually self_mem_nhdsWithin
  -- Extract sequence using first-countability.
  obtain ⟨νs, hνs_tend, hνs_props⟩ :=
    Filter.exists_seq_forall_of_frequently hcomb
  have hνsS : ∀ n, (νs n : Measure X) K = 1 := fun n => (hνs_props n).2
  have hνs_y : ∀ n, y' ≤ ∫ x, gK x ∂(νs n : Measure X) := fun n => (hνs_props n).1
  have hνs_lim : Filter.Tendsto νs Filter.atTop (𝓝 μ₀) :=
    hνs_tend.mono_right inf_le_left
  -- Portmanteau closed-set inequality at each level `t > 0`.
  have hPort_pointwise : ∀ t : ℝ, 0 < t →
      Filter.limsup (fun n => (νs n : Measure X) {x | t ≤ gK x}) Filter.atTop ≤
      (μ₀ : Measure X) {x | t ≤ gK x} :=
    fun t ht =>
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hνs_lim (hClosed_levelset t ht)
  -- Reverse Fatou over `t` (with bound 1).
  have hFatou :
      Filter.limsup (fun n =>
          ∫⁻ t in Set.Ioc (0 : ℝ) (2 * B), (νs n : Measure X) {x | t ≤ gK x})
        Filter.atTop ≤
      ∫⁻ t in Set.Ioc (0 : ℝ) (2 * B), (μ₀ : Measure X) {x | t ≤ gK x} := by
    -- Use `limsup_lintegral_le` with bound `g t = 1` on the bounded interval.
    set g_bound : ℝ → ℝ≥0∞ := fun _ => 1
    -- Build the sequence as fn t = (νs n).toMeasure {gK ≥ t}.
    -- Their lintegrals over Ioc 0 (2B) and bounded by (1 measure of Ioc).
    have hbd : ∀ n, (fun t => (νs n : Measure X) {x | t ≤ gK x}) ≤ᵐ[volume.restrict
        (Set.Ioc (0 : ℝ) (2 * B))] g_bound := by
      intro n
      refine Filter.Eventually.of_forall fun t => ?_
      have h_le : (νs n : Measure X) {x | t ≤ gK x} ≤ (νs n : Measure X) Set.univ :=
        measure_mono (Set.subset_univ _)
      simpa [g_bound] using h_le
    have hg_fin : ∫⁻ t in Set.Ioc (0 : ℝ) (2 * B), g_bound t ≠ ∞ := by
      have hvol : volume (Set.Ioc (0 : ℝ) (2 * B)) ≠ ∞ := by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      simp only [g_bound, MeasureTheory.lintegral_const, one_mul,
        MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hvol
    -- Each `t ↦ (νs n).toMeasure {gK ≥ t}` is antitone in t, hence measurable.
    have hAnti : ∀ ν : ProbabilityMeasure X, Antitone
        (fun t => (ν : Measure X) {x | t ≤ gK x}) := by
      intro ν s t hst
      exact measure_mono (fun x hx => le_trans hst hx)
    have hf_meas : ∀ n, Measurable
        (fun t => (νs n : Measure X) {x | t ≤ gK x}) := fun n => (hAnti _).measurable
    have hμ₀_meas : Measurable (fun t => (μ₀ : Measure X) {x | t ≤ gK x}) :=
      (hAnti _).measurable
    -- Apply `limsup_lintegral_le`.
    have hRev :=
      MeasureTheory.limsup_lintegral_le (μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * B)))
        (f := fun n t => (νs n : Measure X) {x | t ≤ gK x})
        g_bound hf_meas hbd hg_fin
    -- Now bound the limsup integrand pointwise via Portmanteau, then integrate.
    refine hRev.trans ?_
    apply MeasureTheory.lintegral_mono_ae
    refine Filter.Eventually.of_forall fun t => ?_
    rcases lt_or_ge t 0 with ht_neg | ht_nonneg
    · -- For t < 0, the level set is `univ`, so both sides equal 1.
      have h_univ : {x : X | t ≤ gK x} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans ht_neg.le (hgK_nn x)
      simp_rw [h_univ]
      simp
    · -- t ≥ 0. If t = 0, level set is univ; if t > 0, use Portmanteau.
      rcases (lt_or_eq_of_le ht_nonneg).symm with ht_eq | ht_pos
      · -- t = 0
        subst ht_eq
        have h_univ : {x : X | (0 : ℝ) ≤ gK x} = Set.univ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          exact hgK_nn x
        simp_rw [h_univ]; simp
      · exact hPort_pointwise t ht_pos
  -- Translate `hFatou` to `∫⁻ gK dνs n` via layer-cake.
  have hLimsup_lintegral : Filter.limsup
      (fun n => ∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X)) Filter.atTop ≤
      ∫⁻ x, ENNReal.ofReal (gK x) ∂(μ₀ : Measure X) := by
    simp_rw [hlayer_Ioc]
    exact hFatou
  -- Translate to Bochner: `limsup ∫ gK dνs n ≤ ∫ gK dμ₀`.
  -- Uniform `2B` bound on the lintegrals of `gK` against any probability measure.
  have hlintegral_le : ∀ μ : ProbabilityMeasure X,
      ∫⁻ x, ENNReal.ofReal (gK x) ∂(μ : Measure X) ≤ ENNReal.ofReal (2 * B) := fun μ =>
    (MeasureTheory.lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hgK_le x)).trans_eq
      (by rw [MeasureTheory.lintegral_const, measure_univ, mul_one])
  have hgK_lintegral_ne : ∀ μ : ProbabilityMeasure X,
      ∫⁻ x, ENNReal.ofReal (gK x) ∂(μ : Measure X) ≠ ∞ := fun μ =>
    (lt_of_le_of_lt (hlintegral_le μ) ENNReal.ofReal_lt_top).ne
  have hLimsup_le_real :
      Filter.limsup (fun n => ∫ x, gK x ∂(νs n : Measure X)) Filter.atTop ≤
      ∫ x, gK x ∂(μ₀ : Measure X) := by
    -- Each Bochner integral = lintegral.toReal.
    have hBochner_νs : ∀ n, ∫ x, gK x ∂(νs n : Measure X) =
        (∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X)).toReal := fun n => hBochner_eq _
    have hBochner_μ₀ : ∫ x, gK x ∂(μ₀ : Measure X) =
        (∫⁻ x, ENNReal.ofReal (gK x) ∂(μ₀ : Measure X)).toReal := hBochner_eq _
    rw [hBochner_μ₀]
    -- Each lintegral is `≠ ∞`.
    have h_ne_top : ∀ᶠ n in Filter.atTop,
        ∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X) ≠ ∞ :=
      Filter.Eventually.of_forall fun n => hgK_lintegral_ne _
    -- toReal-limsup conversion.
    have h_bd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun a => (∫⁻ x, ENNReal.ofReal (gK x) ∂(νs a : Measure X)).toReal) := by
      apply Filter.isBoundedUnder_of
      refine ⟨(2 * B), fun n => ?_⟩
      have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlintegral_le (νs n))
      have h2B_nn : (0 : ℝ) ≤ 2 * B := mul_nonneg (by norm_num) hB_nn
      rwa [ENNReal.toReal_ofReal h2B_nn] at hmono
    have h_toReal_eq :
        (Filter.limsup (fun n => ∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X))
            Filter.atTop).toReal =
        Filter.limsup (fun n => (∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X)).toReal)
            Filter.atTop :=
      ENNReal.toReal_limsup h_ne_top h_bd
    -- Use the conversion to get the inequality.
    rw [show (fun n => ∫ x, gK x ∂(νs n : Measure X)) =
        (fun n => (∫⁻ x, ENNReal.ofReal (gK x) ∂(νs n : Measure X)).toReal)
        from funext hBochner_νs]
    rw [← h_toReal_eq]
    exact ENNReal.toReal_mono (hgK_lintegral_ne μ₀) hLimsup_lintegral
  -- The sequence ∫ gK dνs n is bounded above by 2 * B.
  have hνs_bd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => ∫ x, gK x ∂(νs n : Measure X)) := by
    refine Filter.isBoundedUnder_of ⟨(2 * B), fun n => ?_⟩
    have h_le : ∫ x, gK x ∂(νs n : Measure X) ≤ ∫ _, (2 * B) ∂(νs n : Measure X) :=
      integral_mono (hgK_int _) (integrable_const _) hgK_le
    rwa [integral_const, probReal_univ, one_smul] at h_le
  -- Final contradiction.
  have hy'_le : y' ≤ ∫ x, gK x ∂(μ₀ : Measure X) :=
    le_trans (Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall hνs_y) hνs_bd)
      hLimsup_le_real
  exact absurd hy'_le (not_le.mpr hlt')

/-- Composition form of the compact-support bounded-USC Portmanteau integral theorem. -/
theorem upperSemicontinuousOn_integral_comp_of_bounded_upperSemicontinuousOn_compactSupport
    {Θ X : Type*} [TopologicalSpace Θ]
    [TopologicalSpace X] [T2Space X] [PseudoMetrizableSpace X] [SeparableSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {S : Set Θ} {K : Set X}
    {P : Θ → ProbabilityMeasure X} {f : X → ℝ}
    (hPContinuous : ContinuousOn P S)
    (hPSupport : ∀ θ ∈ S, (P θ : Measure X) K = 1)
    (hK : IsCompact K)
    (hfBounded : ∃ B : ℝ, ∀ x ∈ K, |f x| ≤ B)
    (hfUSC : UpperSemicontinuousOn f K) :
    UpperSemicontinuousOn
      (fun θ : Θ => ∫ x, f x ∂(P θ : Measure X)) S :=
  (upperSemicontinuousOn_integral_of_bounded_upperSemicontinuousOn_compactSupport
    hK hfBounded hfUSC).comp hPContinuous hPSupport

end

end ProbabilityMeasure

end MeasureTheory
