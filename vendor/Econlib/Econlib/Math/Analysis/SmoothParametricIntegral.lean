/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Smooth parametric integrals

**Differentiation under the integral sign** for a parametric integral `x ↦ ∫ a, f x a ∂μ`, packaged
on open neighborhoods and under compact support. The neighborhood results take the standard
dominated-differentiation hypotheses (measurability, integrability, an integrable bound on the
fibrewise derivative, and fibrewise differentiability holding `μ`-almost everywhere) and conclude
that the integral is differentiable, strictly differentiable, or `C^1`. The compact-support results
strengthen this to `C^∞` for measures supported on a compact set, by integrating the iterated
derivatives levelwise.

## Main definitions

* `SmoothSlice` — the property that each fiber `x ↦ f x a` is `C^∞` on a set.

## Main statements

* `eventually_hasFDerivAt_integralOn` — the derivative formula holds at every nearby point.
* `hasStrictFDerivAt_integral`, `hasStrictFDerivAt_integralOn` — strict differentiability.
* `contDiffAt_one_integralOn` — the `C^1` package on an open neighborhood.
* `continuous_integral_of_support_subset_compact` — continuity of the integral for a fixed measure
  with compact support and a jointly continuous integrand.
* `contDiffAt_integralOn_top_of_compact`, `contDiffAt_integral_top_of_support_subset_compact` — the
  `C^∞` packages under compact support.

## Tags

differentiation under the integral sign, parametric integral, dominated convergence, smoothness
-/

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {α : Type*} [MeasurableSpace α]
  {μ : Measure α}

/-! ### Part 1: Neighborhood versions of differentiation under the integral -/

section HasFDerivAt

omit [CompleteSpace E] [CompleteSpace F] in
/-- If the dominated differentiation hypotheses hold on an open neighborhood `s`, then the
derivative formula for the integral is valid at every nearby point. -/
theorem eventually_hasFDerivAt_integralOn
    {f : E → α → F} {f' : E → α → E →L[ℝ] F} {x₀ : E} {s : Set E}
    (hs_open : IsOpen s) (hx₀ : x₀ ∈ s)
    (hf_meas : ∀ x ∈ s, AEStronglyMeasurable (f x) μ)
    (hf_int : ∀ x ∈ s, Integrable (f x) μ)
    (hf'_meas : ∀ x ∈ s, AEStronglyMeasurable (f' x) μ)
    {bound : α → ℝ}
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖f' x a‖ ≤ bound a)
    (hbound_int : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (f · a) (f' x a) x) :
    ∀ᶠ x in 𝓝 x₀,
      HasFDerivAt (fun y ↦ ∫ a, f y a ∂μ) (∫ a, f' x a ∂μ) x := by
  filter_upwards [hs_open.mem_nhds hx₀] with x hx
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (hs_open.mem_nhds hx)
    (Filter.eventually_of_mem (hs_open.mem_nhds hx) hf_meas) (hf_int x hx) (hf'_meas x hx)
    h_bound hbound_int h_diff

omit [CompleteSpace E] [CompleteSpace F] in
/-- Strict differentiability for a parametric integral once the derivative formula is already known
in a neighborhood and the derivative integral is continuous at the base point. -/
theorem hasStrictFDerivAt_integral
    {f : E → α → F} {f' : E → α → E →L[ℝ] F} {x₀ : E}
    (h_deriv :
      ∀ᶠ x in 𝓝 x₀,
        HasFDerivAt (fun y ↦ ∫ a, f y a ∂μ) (∫ a, f' x a ∂μ) x)
    (h_cont : ContinuousAt (fun x ↦ ∫ a, f' x a ∂μ) x₀) :
    HasStrictFDerivAt (fun x ↦ ∫ a, f x a ∂μ) (∫ a, f' x₀ a ∂μ) x₀ := by
  simpa using hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt h_deriv h_cont

omit [CompleteSpace E] [CompleteSpace F] in
/-- Strict differentiability under the integral on an open neighborhood. -/
theorem hasStrictFDerivAt_integralOn
    {f : E → α → F} {f' : E → α → E →L[ℝ] F} {x₀ : E} {s : Set E}
    (hs_open : IsOpen s) (hx₀ : x₀ ∈ s)
    (hf_meas : ∀ x ∈ s, AEStronglyMeasurable (f x) μ)
    (hf_int : ∀ x ∈ s, Integrable (f x) μ)
    (hf'_meas : ∀ x ∈ s, AEStronglyMeasurable (f' x) μ)
    {bound : α → ℝ}
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖f' x a‖ ≤ bound a)
    (hbound_int : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (f · a) (f' x a) x)
    (h_cont : ContinuousAt (fun x ↦ ∫ a, f' x a ∂μ) x₀) :
    HasStrictFDerivAt (fun x ↦ ∫ a, f x a ∂μ) (∫ a, f' x₀ a ∂μ) x₀ :=
  hasStrictFDerivAt_integral
    (eventually_hasFDerivAt_integralOn hs_open hx₀ hf_meas hf_int hf'_meas h_bound hbound_int
      h_diff)
    h_cont

omit [CompleteSpace E] [CompleteSpace F] in
/-- A `C^1` differentiation-under-the-integral package on an open neighborhood. -/
theorem contDiffAt_one_integralOn
    {f : E → α → F} {f' : E → α → E →L[ℝ] F} {x₀ : E} {s : Set E}
    (hs_open : IsOpen s) (hx₀ : x₀ ∈ s)
    (hf_meas : ∀ x ∈ s, AEStronglyMeasurable (f x) μ)
    (hf_int : ∀ x ∈ s, Integrable (f x) μ)
    (hf'_meas : ∀ x ∈ s, AEStronglyMeasurable (f' x) μ)
    {bound : α → ℝ}
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖f' x a‖ ≤ bound a)
    (hbound_int : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (f · a) (f' x a) x)
    (h_cont : ContinuousOn (fun x ↦ ∫ a, f' x a ∂μ) s) :
    ContDiffAt ℝ 1 (fun x ↦ ∫ a, f x a ∂μ) x₀ := by
  rw [contDiffAt_one_iff]
  refine ⟨fun x ↦ ∫ a, f' x a ∂μ, s, hs_open.mem_nhds hx₀, h_cont, ?_⟩
  intro x hx
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (hs_open.mem_nhds hx)
    (Filter.eventually_of_mem (hs_open.mem_nhds hx) hf_meas) (hf_int x hx) (hf'_meas x hx)
    h_bound hbound_int h_diff

end HasFDerivAt

/-- A measure is almost-everywhere concentrated on any set containing its support. -/
private lemma ae_mem_of_support_subset
    {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [HereditarilyLindelofSpace β]
    {ν : Measure β} {K : Set β} (h_support : ν.support ⊆ K) :
    ∀ᵐ a ∂ν, a ∈ K := by
  rw [ae_iff]
  -- The set `{a | a ∉ K}` lies in the complement of the support, which is null.
  refine le_antisymm
    ((measure_mono (fun a (ha : a ∉ K) hmem ↦ ha (h_support hmem))).trans ?_) bot_le
  exact (Measure.measure_compl_support (μ := ν)).le

section CompactSupport

variable
  {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [TopologicalSpace α] [OpensMeasurableSpace α]
  [HereditarilyLindelofSpace α]
  [SecondCountableTopologyEither α G] [IsLocallyFiniteMeasure μ]

omit [CompleteSpace G] in
/-- For a fixed measure with compact support, a jointly continuous integrand yields a continuous
parametric integral. -/
theorem continuous_integral_of_support_subset_compact
    {g : X → α → G} {K : Set α}
    (hg : Continuous g.uncurry) (hK : IsCompact K) (h_support : μ.support ⊆ K) :
    Continuous (fun x ↦ ∫ a, g x a ∂μ) := by
  have h_mem_K : ∀ᵐ a ∂μ, a ∈ K := ae_mem_of_support_subset h_support
  have hset :
      Continuous (fun x ↦ ∫ a in K, g x a ∂μ) :=
    continuous_parametric_integral_of_continuous (μ := μ) (f := g) (s := K) hg hK
  have hEq :
      (fun x ↦ ∫ a, g x a ∂μ) = fun x ↦ ∫ a in K, g x a ∂μ := by
    funext x
    exact integral_eq_setIntegral h_mem_K (g x)
  simpa [hEq] using hset

end CompactSupport

section SmoothCompactSupport

variable
  [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α]
  [HereditarilyLindelofSpace α] [IsLocallyFiniteMeasure μ]

/-- The fiber `x ↦ f x a` of a parametric integrand is `C^∞` on the set `s`. -/
abbrev SmoothSlice (f : E → α → F) (a : α) (s : Set E) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ f x a) s

omit [CompleteSpace E] [CompleteSpace F] [HereditarilyLindelofSpace α] in
/-- Compact-support `C^∞` differentiation under the integral sign for a set integral over `K`: If
each fiber is `C^∞` on the open set `s` and the iterated derivatives are jointly continuous on
`L ×ˢ K`, then `x ↦ ∫ a in K, f x a ∂μ` is `C^∞` at `x₀`. -/
theorem contDiffAt_integralOn_top_of_compact
    {f : E → α → F}
    {x₀ : E}
    {s L : Set E}
    {K : Set α}
    (hs_open : IsOpen s)
    (hx₀ : x₀ ∈ s)
    (hsL : s ⊆ L)
    (hL_compact : IsCompact L)
    (hK_compact : IsCompact K)
    (hf_smooth : ∀ a, a ∈ K → SmoothSlice f a s)
    (hf_joint :
      ∀ n : ℕ,
        ContinuousOn (fun p : E × α ↦ iteratedFDeriv ℝ n (fun x ↦ f x p.2) p.1) (L ×ˢ K)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x ↦ ∫ a in K, f x a ∂μ) x₀ := by
  let p : E → FormalMultilinearSeries ℝ E F := fun x n ↦
    ∫ a, iteratedFDeriv ℝ n (f · a) x ∂(μ.restrict K)
  have hp : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x ↦ ∫ a in K, f x a ∂μ) p s := by
    rw [hasFTaylorSeriesUpToOn_top_iff' le_rfl]
    constructor
    · intro x hx
      have hxL : x ∈ L := hsL hx
      have h0_int :
          Integrable (fun a ↦ ContinuousMultilinearMap.uncurry0 ℝ E (f x a))
            (μ.restrict K) := by
        simpa [iteratedFDeriv_zero_eq_comp, IntegrableOn] using
          ((hf_joint 0).comp
            (show ContinuousOn (fun a : α ↦ (x, a)) K by fun_prop)
            (fun a ha ↦ ⟨hxL, ha⟩)).integrableOn_compact' (μ := μ)
              hK_compact hK_compact.measurableSet
      simpa [p, iteratedFDeriv_zero_eq_comp] using
        (ContinuousMultilinearMap.integral_apply
          (φ := fun a ↦ ContinuousMultilinearMap.uncurry0 ℝ E (f x a)) h0_int ![])
    · intro m x hx
      let fm : E → α → E [×m]→L[ℝ] F := fun y a ↦ iteratedFDeriv ℝ m (f · a) y
      let fm' : E → α → E →L[ℝ] (E [×m]→L[ℝ] F) := fun y a ↦
        (iteratedFDeriv ℝ (m + 1) (f · a) y).curryLeft
      have hxL : x ∈ L := hsL hx
      have hslice
          (n : ℕ) {y : E} (hyL : y ∈ L) :
          ContinuousOn (fun a ↦ iteratedFDeriv ℝ n (f · a) y) K := by
        simpa using
          (hf_joint n).comp
            (show ContinuousOn (fun a : α ↦ (y, a)) K by fun_prop)
            (fun a ha ↦ ⟨hyL, ha⟩)
      have hslice'
          {y : E} (hyL : y ∈ L) :
          ContinuousOn (fun a ↦ fm' y a) K := by
        have hcur :
            Continuous
              (fun z : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) F ↦ z.curryLeft) := by
          simpa using
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).continuous
        simpa [fm'] using hcur.comp_continuousOn (hslice (m + 1) hyL)
      have hfm_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (fm y) (μ.restrict K) := by
        filter_upwards [hs_open.mem_nhds hx] with y hy
        exact (hslice m (hsL hy)).aestronglyMeasurable_of_isCompact hK_compact
          hK_compact.measurableSet
      have hfm_int : Integrable (fm x) (μ.restrict K) := by
        simpa [fm, IntegrableOn] using
          (hslice m hxL).integrableOn_compact' (μ := μ) hK_compact hK_compact.measurableSet
      have hfm'_meas : AEStronglyMeasurable (fm' x) (μ.restrict K) :=
        (hslice' hxL).aestronglyMeasurable_of_isCompact hK_compact hK_compact.measurableSet
      have hfm'_int : Integrable (fm' x) (μ.restrict K) := by
        simpa [fm', IntegrableOn] using
          (hslice' hxL).integrableOn_compact' (μ := μ) hK_compact hK_compact.measurableSet
      obtain ⟨M, hM⟩ :=
        (hL_compact.prod hK_compact).bddAbove_image ((hf_joint (m + 1)).norm)
      have h_bound : ∀ᵐ a ∂(μ.restrict K), ∀ y ∈ s, ‖fm' y a‖ ≤ M := by
        filter_upwards [ae_restrict_mem hK_compact.measurableSet] with a ha y hy
        have hpair : (y, a) ∈ L ×ˢ K := ⟨hsL hy, ha⟩
        have h := hM (Set.mem_image_of_mem _ hpair)
        simpa [fm', ContinuousMultilinearMap.curryLeft_norm] using h
      have hbound_int : Integrable (fun _ : α ↦ M) (μ.restrict K) := by
        letI : IsFiniteMeasure (μ.restrict K) :=
          ⟨by simpa using hK_compact.measure_lt_top (μ := μ)⟩
        exact integrable_const M
      have h_diff :
          ∀ᵐ a ∂(μ.restrict K), ∀ y ∈ s, HasFDerivAt (fm · a) (fm' y a) y := by
        filter_upwards [ae_restrict_mem hK_compact.measurableSet] with a ha y hy
        have hcontAt := (hf_smooth a ha).contDiffAt (hs_open.mem_nhds hy)
        have hderiv :
            HasFDerivAt (iteratedFDeriv ℝ m (f · a))
              (fderiv ℝ (iteratedFDeriv ℝ m (f · a)) y) y :=
          (hcontAt.differentiableAt_iteratedFDeriv
            (by
              exact_mod_cast (show (m : ℕ∞) < (⊤ : ℕ∞) by simp))).hasFDerivAt
        rw [fderiv_iteratedFDeriv, Function.comp_apply] at hderiv
        simpa [fm, fm'] using hderiv
      have hmain :=
        hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ.restrict K) (s := s) (x₀ := x)
          (F := fm) (F' := fm') (hs_open.mem_nhds hx) hfm_meas hfm_int hfm'_meas
          h_bound hbound_int h_diff
      have hiter_int :
          Integrable (fun a ↦ iteratedFDeriv ℝ (m + 1) (f · a) x) (μ.restrict K) := by
        simpa [IntegrableOn] using
          (hslice (m + 1) hxL).integrableOn_compact' (μ := μ) hK_compact
            hK_compact.measurableSet
      have hEqDeriv :
          (∫ a, fm' x a ∂(μ.restrict K)) = (p x (m + 1)).curryLeft := by
        ext u v
        calc
          ((∫ a, fm' x a ∂(μ.restrict K)) u) v =
              ∫ a, ((fm' x a) u) v ∂(μ.restrict K) := by
            rw [ContinuousLinearMap.integral_apply hfm'_int,
              ContinuousMultilinearMap.integral_apply]
            exact hfm'_int.apply_continuousLinearMap u
          _ = ∫ a, (iteratedFDeriv ℝ (m + 1) (f · a) x) (Fin.cons u v) ∂(μ.restrict K) := by
            simp [fm', ContinuousMultilinearMap.curryLeft_apply]
          _ = (∫ a, iteratedFDeriv ℝ (m + 1) (f · a) x ∂(μ.restrict K)) (Fin.cons u v) := by
            symm
            exact ContinuousMultilinearMap.integral_apply hiter_int (Fin.cons u v)
          _ = ((p x (m + 1)).curryLeft u) v := by
            simp [p, ContinuousMultilinearMap.curryLeft_apply]
      have hmain' :
          HasFDerivWithinAt (fun y ↦ ∫ a, fm y a ∂(μ.restrict K))
            ((p x (m + 1)).curryLeft) s x :=
        hmain.hasFDerivWithinAt.congr_fderiv hEqDeriv
      simpa [p, fm] using hmain'
  have hcd : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ ∫ a in K, f x a ∂μ) s := hp.contDiffOn
  simpa using hcd.contDiffAt (hs_open.mem_nhds hx₀)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Compact-support `C^∞` differentiation under the full integral, obtained by reducing to the set
integral over a compact set containing the support of the measure. -/
theorem contDiffAt_integral_top_of_support_subset_compact
    {f : E → α → F}
    {x₀ : E}
    {s L : Set E}
    {K : Set α}
    (hs_open : IsOpen s)
    (hx₀ : x₀ ∈ s)
    (hsL : s ⊆ L)
    (hL_compact : IsCompact L)
    (hK_compact : IsCompact K)
    (h_support : μ.support ⊆ K)
    (hf_smooth : ∀ a, a ∈ K → SmoothSlice f a s)
    (hf_joint :
      ∀ n : ℕ,
        ContinuousOn (fun p : E × α ↦ iteratedFDeriv ℝ n (fun x ↦ f x p.2) p.1) (L ×ˢ K)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x ↦ ∫ a, f x a ∂μ) x₀ := by
  have hset :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x ↦ ∫ a in K, f x a ∂μ) x₀ :=
    contDiffAt_integralOn_top_of_compact hs_open hx₀ hsL hL_compact hK_compact hf_smooth
      hf_joint
  have h_mem_K : ∀ᵐ a ∂μ, a ∈ K := ae_mem_of_support_subset h_support
  refine hset.congr_of_eventuallyEq ?_
  filter_upwards with x
  exact integral_eq_setIntegral h_mem_K (f x)

end SmoothCompactSupport
