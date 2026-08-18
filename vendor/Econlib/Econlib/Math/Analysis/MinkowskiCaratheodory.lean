/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Minkowski–Carathéodory in finite dimension

In a finite-dimensional space, a compact convex set `K` equals the convex hull of its extreme
points (the closure-free strengthening of Krein–Milman). Combining this with Carathéodory's
theorem, every point `x ∈ K` is a positive convex combination of finitely many extreme points,
which packages into a probability measure `ν` on `ℝⁿ` supported on `Set.extremePoints ℝ K` with
mean `x`.

Mathlib provides only the closure version `closure_convexHull_extremePoints`
(`closure (convexHull ℝ (extremePoints ℝ K)) = K`) and the finite-dimensional Carathéodory
representation `eq_pos_convex_span_of_mem_convexHull`. The closure-free strengthening in finite
dimension is flagged as missing in `Mathlib/Analysis/Convex/KreinMilman.lean`; this file supplies
it and the extreme-point measure representation it unlocks.

## Main statements

* `subset_convexHull_extremePoints_of_compact_convex` — closure-free Minkowski: Every point of a
  compact convex `K` lies in the convex hull of its extreme points.
* `isCompact_convexHull_of_isCompact` — the convex hull of a compact set is compact.
* `closure_convexHull_of_isCompact` — the convex hull of a compact set is closed.
* `extremePoints_closure_convexHull_subset_of_isCompact` — Milman's theorem in the compact case.
* `exists_extremePoint_measure_of_compact_convex` — the extreme-point measure representation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology Pointwise

/-! ## Dirac-mixture probability measure from a positive convex combination -/

/-- **Dirac mixture from a positive convex combination.**  Given a finite family of points
`z : ι → E` in a measurable set `S` with positive weights `w` summing to `1`, the measure
`∑ i, ENNReal.ofReal (w i) • dirac (z i)` is a probability measure concentrated on `S` with mean
`∑ i, w i • z i`. -/
lemma exists_dirac_combination_of_pos_convex_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSingletonClass E]
    {ι : Type*} [Fintype ι]
    {w : ι → ℝ} {z : ι → E}
    (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    {S : Set E} (hzS : ∀ i, z i ∈ S) :
    ∃ ν : Measure E,
      IsProbabilityMeasure ν ∧ ν S = 1 ∧ ∫ y, y ∂ν = ∑ i, w i • z i := by
  classical
  refine ⟨∑ i, ENNReal.ofReal (w i) • Measure.dirac (z i), ?_, ?_, ?_⟩
  · -- IsProbabilityMeasure: ν univ = 1.
    refine ⟨?_⟩
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw_pos i).le), hw_sum,
      ENNReal.ofReal_one]
  · -- ν S = 1.
    rw [Measure.finset_sum_apply]
    have h_each : ∀ i ∈ (Finset.univ : Finset ι),
        (ENNReal.ofReal (w i) • Measure.dirac (z i)) S = ENNReal.ofReal (w i) := by
      intro i _
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem (hzS i), smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl h_each]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw_pos i).le), hw_sum,
      ENNReal.ofReal_one]
  · -- ∫ y, y ∂ν = ∑ i, w i • z i.
    have h_int : ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun y : E => y) (ENNReal.ofReal (w i) • Measure.dirac (z i)) := by
      intro i _
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    rw [integral_finset_sum_measure h_int]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_smul_measure, integral_dirac (fun y : E => y) (z i),
      ENNReal.toReal_ofReal (hw_pos i).le]

/-! ## The closure-free Minkowski theorem -/

/-- The inductive hypothesis shared by the Minkowski helpers: Closure-free Minkowski holds for
every finite-dimensional normed space of `finrank ≤ n`. -/
private abbrev MinkowskiIH.{u} (n : ℕ) : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
    Module.finrank ℝ F ≤ n → ∀ {K' : Set F},
    IsCompact K' → Convex ℝ K' →
    K' ⊆ convexHull ℝ (Set.extremePoints ℝ K')

/-- Extreme points commute with images under injective linear maps. The variant of Mathlib's
`Set.image_extremePoints` for a linear injection (e.g. a submodule inclusion) rather than a
`LinearEquivClass`. -/
private lemma extremePoints_image_of_injective {E F : Type*}
    [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (hf : Function.Injective f) (s : Set E) :
    f '' Set.extremePoints ℝ s = Set.extremePoints ℝ (f '' s) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_extremePoints] at ha
    refine (mem_extremePoints).mpr ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro x₁ ⟨a₁, ha₁, rfl⟩ x₂ ⟨a₂, ha₂, rfl⟩ hmid
    have himg : f '' openSegment ℝ a₁ a₂ = openSegment ℝ (f a₁) (f a₂) :=
      image_openSegment ℝ f.toAffineMap a₁ a₂
    rw [← himg] at hmid
    obtain ⟨y, hy_seg, hy_eq⟩ := hmid
    have hya : y = a := hf hy_eq
    rw [hya] at hy_seg
    obtain ⟨hya₁, hya₂⟩ := ha.2 a₁ ha₁ a₂ ha₂ hy_seg
    exact ⟨congrArg f hya₁, congrArg f hya₂⟩
  · intro hb
    rw [mem_extremePoints] at hb
    obtain ⟨⟨a, ha, rfl⟩, hext⟩ := hb
    refine ⟨a, (mem_extremePoints).mpr ⟨ha, ?_⟩, rfl⟩
    intro x₁ hx₁ x₂ hx₂ ha_seg
    have hmid : f a ∈ openSegment ℝ (f x₁) (f x₂) := by
      have heq : f '' openSegment ℝ x₁ x₂ = openSegment ℝ (f x₁) (f x₂) :=
        image_openSegment ℝ f.toAffineMap x₁ x₂
      rw [← heq]
      exact ⟨a, ha_seg, rfl⟩
    obtain ⟨hfx₁, hfx₂⟩ := hext (f x₁) ⟨x₁, hx₁, rfl⟩ (f x₂) ⟨x₂, hx₂, rfl⟩ hmid
    exact ⟨hf hfx₁, hf hfx₂⟩

/-- Translation invariance of extreme points: For a real vector space, the extreme points of a
translate are the translate of the extreme points. -/
private lemma extremePoints_vadd {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : E) (s : Set E) :
    Set.extremePoints ℝ (v +ᵥ s) = v +ᵥ Set.extremePoints ℝ s := by
  ext z
  rw [Set.mem_vadd_set]
  refine ⟨?_, ?_⟩
  · intro hz
    rw [mem_extremePoints] at hz
    obtain ⟨⟨a, ha, hae⟩, hext⟩ := hz
    refine ⟨a, ?_, hae⟩
    rw [mem_extremePoints]
    refine ⟨ha, ?_⟩
    intro x₁ hx₁ x₂ hx₂ hseg
    have hseg' : z ∈ openSegment ℝ (v +ᵥ x₁) (v +ᵥ x₂) := by
      rcases hseg with ⟨α, β, hα, hβ, hαβ, h⟩
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      have hz_eq : z = v + a := by rw [← hae]; rfl
      have hra : α • (v + x₁) + β • (v + x₂) = (α + β) • v + (α • x₁ + β • x₂) := by
        module
      rw [hz_eq, show v +ᵥ x₁ = v + x₁ from rfl, show v +ᵥ x₂ = v + x₂ from rfl,
        hra, hαβ, one_smul, h]
    obtain ⟨h1, h2⟩ := hext _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hseg'
    have hz_eq2 : v + a = z := hae
    have hax₁ : v + x₁ = v + a := by
      have : v +ᵥ x₁ = z := h1
      rw [show v +ᵥ x₁ = v + x₁ from rfl] at this
      rw [this, ← hz_eq2]
    have hax₂ : v + x₂ = v + a := by
      have : v +ᵥ x₂ = z := h2
      rw [show v +ᵥ x₂ = v + x₂ from rfl] at this
      rw [this, ← hz_eq2]
    exact ⟨add_left_cancel hax₁, add_left_cancel hax₂⟩
  · rintro ⟨a, ha, rfl⟩
    rw [mem_extremePoints] at ha
    obtain ⟨ha_s, hext⟩ := ha
    rw [mem_extremePoints]
    refine ⟨⟨a, ha_s, rfl⟩, ?_⟩
    rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hseg
    have hseg' : a ∈ openSegment ℝ x₁ x₂ := by
      rcases hseg with ⟨α, β, hα, hβ, hαβ, h⟩
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      simp only at h
      have hra : α • (v +ᵥ x₁) + β • (v +ᵥ x₂) = (α + β) • v + (α • x₁ + β • x₂) := by
        change α • (v + x₁) + β • (v + x₂) = (α + β) • v + (α • x₁ + β • x₂)
        module
      rw [hra, hαβ, one_smul] at h
      have hv_eq : v + (α • x₁ + β • x₂) = v + a := h
      exact add_left_cancel hv_eq
    obtain ⟨h1, h2⟩ := hext _ hx₁ _ hx₂ hseg'
    exact ⟨by rw [h1], by rw [h2]⟩

/-- Descent helper for closure-free Minkowski: If `vectorSpan ℝ K` has `finrank ≤ n`, then `K` lies
in the convex hull of its extreme points, obtained from the inductive hypothesis on the submodule
`vectorSpan ℝ K`. -/
private lemma minkowski_descent_aux.{u} {n : ℕ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (IH : MinkowskiIH.{u} n) {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (h_vs : Module.finrank ℝ (vectorSpan ℝ K) ≤ n) :
    K ⊆ convexHull ℝ (Set.extremePoints ℝ K) := by
  -- Empty case: trivial.
  rcases K.eq_empty_or_nonempty with hK_empty | ⟨x₀, hx₀⟩
  · rw [hK_empty]; exact Set.empty_subset _
  -- Translate K by -x₀ so the translated set passes through 0, hence lies in V.
  set V : Submodule ℝ E := vectorSpan ℝ K with hV_def
  set K' : Set E := (-x₀) +ᵥ K with hK'_def
  have hK'_compact : IsCompact K' := hK_compact.vadd (-x₀)
  have hK'_convex : Convex ℝ K' := hK_convex.vadd (-x₀)
  -- K' ⊆ V.
  have hK'_sub_V : K' ⊆ (V : Set E) := by
    intro y hy
    obtain ⟨a, haK, hay⟩ := hy
    have hyeq : y = a -ᵥ x₀ := by
      have : y = -x₀ + a := hay.symm
      simpa [vsub_eq_sub, sub_eq_neg_add, add_comm] using this
    rw [hyeq]
    exact vsub_mem_vectorSpan ℝ haK hx₀
  -- View K' as a subset of ↥V.
  let K'' : Set V := (V.subtype : V → E) ⁻¹' K'
  haveI : FiniteDimensional ℝ V := Submodule.finiteDimensional_of_le le_top
  have hV_finrank : Module.finrank ℝ V ≤ n := h_vs
  -- V is closed (finite-dimensional submodule), so subtype is a closed embedding.
  have hV_closed : IsClosed (V : Set E) := Submodule.closed_of_finiteDimensional V
  have hsubtype_emb : Topology.IsClosedEmbedding (V.subtype : V → E) :=
    hV_closed.isClosedEmbedding_subtypeVal
  have hK''_compact : IsCompact K'' := hsubtype_emb.isCompact_preimage hK'_compact
  have hK''_convex : Convex ℝ K'' := hK'_convex.linear_preimage V.subtype
  -- Apply IH.
  have hIH : K'' ⊆ convexHull ℝ (Set.extremePoints ℝ K'') :=
    IH (F := ↥V) hV_finrank hK''_compact hK''_convex
  -- V.subtype '' K'' = K' (since K' ⊆ V).
  have hK'_eq : (V.subtype : V → E) '' K'' = K' := by
    rw [Set.image_preimage_eq_iff]
    intro y hy
    have : y ∈ (V : Set E) := hK'_sub_V hy
    rw [← V.range_subtype] at this
    exact this
  have h_inj : Function.Injective (V.subtype : V → E) := V.subtype_injective
  -- Step: K' ⊆ convexHull (extremePoints K').
  have hK'_step : K' ⊆ convexHull ℝ (Set.extremePoints ℝ K') := by
    have himg_hull :
        (V.subtype : V → E) '' (convexHull ℝ (Set.extremePoints ℝ K'')) =
          convexHull ℝ ((V.subtype : V → E) '' Set.extremePoints ℝ K'') :=
      V.subtype.image_convexHull _
    have hep_eq : (V.subtype : V → E) '' Set.extremePoints ℝ K'' =
        Set.extremePoints ℝ ((V.subtype : V → E) '' K'') :=
      extremePoints_image_of_injective V.subtype h_inj K''
    rw [show K' = (V.subtype : V → E) '' K'' from hK'_eq.symm]
    rintro _ ⟨v, hv, rfl⟩
    have hv_hull := hIH hv
    have hmem : V.subtype v ∈
        (V.subtype : V → E) '' (convexHull ℝ (Set.extremePoints ℝ K'')) :=
      ⟨v, hv_hull, rfl⟩
    rw [himg_hull, hep_eq] at hmem
    exact hmem
  -- Translate back.
  intro y hyK
  have hy' : (-x₀) +ᵥ y ∈ K' := ⟨y, hyK, rfl⟩
  have hy'_hull := hK'_step hy'
  -- extremePoints ℝ K' = (-x₀) +ᵥ extremePoints ℝ K (translation invariance).
  rw [show K' = (-x₀) +ᵥ K from rfl, extremePoints_vadd, convexHull_vadd] at hy'_hull
  -- (-x₀) +ᵥ y ∈ (-x₀) +ᵥ convexHull (extremePoints K), so y ∈ convexHull (extremePoints K).
  obtain ⟨w, hw_hull, hwy⟩ := hy'_hull
  have hy_eq : y = w := by
    have h1 : -x₀ +ᵥ w = -x₀ +ᵥ y := hwy
    have h2 : -x₀ + w = -x₀ + y := h1
    exact (add_left_cancel h2).symm
  rw [hy_eq]; exact hw_hull

/-- Interior helper for closure-free Minkowski: For a full-dimensional `K` and `x ∈ interior K`,
writes `x` as a convex combination of an extreme point and a frontier point of `K`, then concludes
via the frontier case.

The frontier conclusion is taken as an explicit hypothesis `frontier_case` so that this lemma can
be stated before `minkowski_frontier_aux`, which supplies it. -/
private lemma minkowski_interior_aux.{u} {n : ℕ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (_IH : MinkowskiIH.{u} n) {K : Set E}
    (hK_compact : IsCompact K)
    -- Unused here: kept so this lemma's signature matches `minkowski_descent_aux` /
    -- `minkowski_frontier_aux` for uniform call sites in `minkowski_aux`.
    (_hK_convex : Convex ℝ K)
    (_h_dim : Module.finrank ℝ E ≤ n + 1)
    (_h_vs : n < Module.finrank ℝ (vectorSpan ℝ K))
    (frontier_case : ∀ z ∈ K, z ∉ interior K →
      z ∈ convexHull ℝ (Set.extremePoints ℝ K))
    {x : E} (hxK : x ∈ K) (hx_int : x ∈ interior K) :
    x ∈ convexHull ℝ (Set.extremePoints ℝ K) := by
  -- Step 1: pick an extreme point `e` of `K`.
  obtain ⟨e, he_ext⟩ := hK_compact.extremePoints_nonempty ⟨x, hxK⟩
  have he_K : e ∈ K := extremePoints_subset he_ext
  by_cases hxe : x = e
  · exact subset_convexHull ℝ _ (hxe ▸ he_ext)
  -- Step 2: the ray φ(t) = e + t • (x - e).
  set φ : ℝ → E := fun t => e + t • (x - e) with hφ_def
  have hφ_cont : Continuous φ := by fun_prop
  have hφ_zero : φ 0 = e := by simp [hφ_def]
  have hφ_one : φ 1 = x := by simp [hφ_def]
  set T : Set ℝ := φ ⁻¹' K with hT_def
  have hT_zero : (0 : ℝ) ∈ T := by simp [hT_def, hφ_zero, he_K]
  have hT_one : (1 : ℝ) ∈ T := by simp [hT_def, hφ_one, hxK]
  have hT_closed : IsClosed T := hK_compact.isClosed.preimage hφ_cont
  have hT_nonempty : T.Nonempty := ⟨0, hT_zero⟩
  have hxe_ne : x - e ≠ 0 := sub_ne_zero.mpr hxe
  have hxe_norm_pos : 0 < ‖x - e‖ := norm_pos_iff.mpr hxe_ne
  obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall e
  have hT_bddAbove : BddAbove T := by
    refine ⟨R / ‖x - e‖, ?_⟩
    intro t ht
    have ht_K : φ t ∈ K := ht
    have hball : φ t ∈ Metric.closedBall e R := hR ht_K
    rw [Metric.mem_closedBall, dist_eq_norm] at hball
    have hdiff : φ t - e = t • (x - e) := by simp [hφ_def]
    have hnorm : ‖t • (x - e)‖ ≤ R := hdiff ▸ hball
    have htnorm : ‖t‖ * ‖x - e‖ ≤ R := by simpa [norm_smul] using hnorm
    have ht_norm_le : ‖t‖ ≤ R / ‖x - e‖ := by
      rw [le_div_iff₀ hxe_norm_pos]; exact htnorm
    have ht_abs : |t| ≤ R / ‖x - e‖ := by simpa [Real.norm_eq_abs] using ht_norm_le
    exact (abs_le.mp ht_abs).2
  set t_star : ℝ := sSup T with ht_star_def
  have ht_star_mem : t_star ∈ T := hT_closed.csSup_mem hT_nonempty hT_bddAbove
  have ht_star_ge_one : 1 ≤ t_star := le_csSup hT_bddAbove hT_one
  -- Whenever `φ c` lands in the open interior, the ray can be pushed strictly past `c` and still
  -- stay in `K`, so `t_star` (the sup of `T`) sits strictly above `c`.  Used at `c = 1` (Step 3)
  -- and `c = t_star` (Step 4).
  have h_int_push : ∀ c : ℝ, φ c ∈ interior K → c < t_star := by
    intro c hc_int
    have hpre : φ ⁻¹' interior K ∈ nhds c :=
      hφ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hc_int)
    rw [Metric.mem_nhds_iff] at hpre
    obtain ⟨ε, hε_pos, hε_sub⟩ := hpre
    have hball : (c + ε / 2 : ℝ) ∈ Metric.ball c ε := by
      rw [Metric.mem_ball, Real.dist_eq, show (c + ε / 2 - c : ℝ) = ε / 2 from by ring,
        abs_of_pos (by linarith)]
      linarith
    have hmem : (c + ε / 2 : ℝ) ∈ T :=
      show φ (c + ε / 2) ∈ K from interior_subset (hε_sub hball)
    have h_le : (c + ε / 2 : ℝ) ≤ t_star := le_csSup hT_bddAbove hmem
    linarith
  -- Step 3: 1 < t_star, by x ∈ interior K.
  have ht_star_gt_one : 1 < t_star := h_int_push 1 (hφ_one ▸ hx_int)
  -- Step 4: y := φ t* is in K \ interior K.
  set y : E := φ t_star with hy_def
  have hy_K : y ∈ K := ht_star_mem
  have hy_not_int : y ∉ interior K := fun hy_int =>
    lt_irrefl t_star (h_int_push t_star hy_int)
  -- Step 5: x as a convex combination of e and y.
  set α : ℝ := 1 / t_star with hα_def
  set β : ℝ := 1 - α with hβ_def
  have ht_star_pos : 0 < t_star := by linarith
  have ht_star_ne_zero : t_star ≠ 0 := ne_of_gt ht_star_pos
  have hα_pos : 0 < α := by rw [hα_def]; exact one_div_pos.mpr ht_star_pos
  have hα_le_one : α ≤ 1 := by rw [hα_def, div_le_one ht_star_pos]; exact ht_star_ge_one
  have hβ_nonneg : 0 ≤ β := by rw [hβ_def]; linarith
  have hαβ_sum : β + α = 1 := by rw [hβ_def]; ring
  have hα_t : α * t_star = 1 := by
    rw [hα_def, one_div, inv_mul_cancel₀ ht_star_ne_zero]
  have hx_combo : x = β • e + α • y := by
    -- y = e + t_star • (x - e); α • y = α • e + (α • t_star) • (x - e) = α • e + (x - e).
    have hy_eq : y = e + t_star • (x - e) := rfl
    have hαy : α • y = α • e + (x - e) := by
      have : α • y = α • e + (α * t_star) • (x - e) := by
        rw [hy_eq, smul_add, smul_smul]
      rw [this, hα_t, one_smul]
    rw [hαy, hβ_def, sub_smul, one_smul]
    abel
  -- Step 6: y is in the hull, via the frontier helper hypothesis.
  have hy_hull : y ∈ convexHull ℝ (Set.extremePoints ℝ K) :=
    frontier_case y hy_K hy_not_int
  have he_hull : e ∈ convexHull ℝ (Set.extremePoints ℝ K) :=
    subset_convexHull ℝ _ he_ext
  have h_hull_convex : Convex ℝ (convexHull ℝ (Set.extremePoints ℝ K)) :=
    convex_convexHull ℝ _
  rw [hx_combo]
  exact h_hull_convex he_hull hy_hull hβ_nonneg hα_pos.le hαβ_sum

/-- Frontier helper for closure-free Minkowski: For a full-dimensional `K` and
`x ∈ K \ interior K`, a supporting hyperplane at `x` cuts out a proper exposed face `F` of
dimension `≤ n`, whose extreme points are extreme in `K`; the inductive hypothesis then places `x`
in the convex hull of the extreme points of `K`. -/
private lemma minkowski_frontier_aux.{u} {n : ℕ} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (IH : MinkowskiIH.{u} n) {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (h_dim : Module.finrank ℝ E ≤ n + 1)
    (h_vs : n < Module.finrank ℝ (vectorSpan ℝ K))
    {x : E} (hxK : x ∈ K) (hx_not_int : x ∉ interior K) :
    x ∈ convexHull ℝ (Set.extremePoints ℝ K) := by
  -- Step 1: interior K is nonempty.  vectorSpan K is a submodule of E with finrank
  -- both > n (from h_vs) and ≤ finrank E ≤ n+1, so vectorSpan K = ⊤.
  have h_vs_le_E : Module.finrank ℝ (vectorSpan ℝ K) ≤ Module.finrank ℝ E :=
    Submodule.finrank_le _
  have h_finrank_E : Module.finrank ℝ E = n + 1 := by omega
  have h_vs_top : vectorSpan ℝ K = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    omega
  have hK_nonempty : K.Nonempty := ⟨x, hxK⟩
  have h_affineSpan_top : affineSpan ℝ K = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E hK_nonempty).mpr
      h_vs_top
  have h_int_ne : (interior K).Nonempty :=
    hK_convex.interior_nonempty_iff_affineSpan_eq_top.mpr h_affineSpan_top
  -- Step 2: supporting hyperplane.  geometric_hahn_banach gives an f strictly less
  -- than f x on interior K; extend the inequality to all of K by closure.
  obtain ⟨f, hf_lt⟩ :=
    geometric_hahn_banach_open_point hK_convex.interior isOpen_interior hx_not_int
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_K_sub_clos_int : K ⊆ closure (interior K) := by
    have hcl := hK_convex.closure_interior_eq_closure_of_nonempty_interior h_int_ne
    have hKcl : K ⊆ closure K := subset_closure
    rw [← hcl] at hKcl; exact hKcl
  have hf_le : ∀ y ∈ K, f y ≤ f x := by
    intro y hyK
    have hy_clos : y ∈ closure (interior K) := h_K_sub_clos_int hyK
    -- Continuity: f(closure(interior K)) ⊆ closure(f '' interior K) ⊆ Iic (f x).
    have h_img_sub : f '' interior K ⊆ Set.Iio (f x) := by
      rintro _ ⟨a, ha, rfl⟩; exact hf_lt a ha
    have h_clos_img_sub : closure (f '' interior K) ⊆ Set.Iic (f x) :=
      closure_minimal (h_img_sub.trans Set.Iio_subset_Iic_self) isClosed_Iic
    have hfy_clos : f y ∈ closure (f '' interior K) := by
      have hmap : f '' closure (interior K) ⊆ closure (f '' interior K) :=
        f.continuous.continuousOn.image_closure
      exact hmap ⟨y, hy_clos, rfl⟩
    exact h_clos_img_sub hfy_clos
  -- Step 3: define the exposed face F = {y ∈ K | f y = f x}.
  set F : Set E := {y ∈ K | f y = f x} with hF_def
  have hxF : x ∈ F := ⟨hxK, rfl⟩
  have hF_nonempty : F.Nonempty := ⟨x, hxF⟩
  have hF_sub_K : F ⊆ K := fun _ hy => hy.1
  -- F is exposed via the functional f: y ∈ F ↔ y ∈ K ∧ f maximized at y over K.
  have hF_exposed : IsExposed ℝ K F := by
    intro _
    refine ⟨f, ?_⟩
    ext y
    refine ⟨fun hy => ⟨hy.1, fun z hz => ?_⟩, fun hy => ⟨hy.1, ?_⟩⟩
    · rw [hy.2]; exact hf_le z hz
    · exact le_antisymm (hf_le y hy.1) (hy.2 x hxK)
  -- F is closed (intersection of closed K with preimage of singleton under cts f).
  have hF_closed : IsClosed F := by
    have h_eq : F = K ∩ (f ⁻¹' {f x}) := rfl
    rw [h_eq]
    exact hK_closed.inter (isClosed_singleton.preimage f.continuous)
  have hF_compact : IsCompact F :=
    hK_compact.of_isClosed_subset hF_closed hF_sub_K
  have hF_convex : Convex ℝ F := hF_exposed.convex hK_convex
  -- Step 4: F is extreme in K, so extremePoints F ⊆ extremePoints K.
  have hF_extreme : IsExtreme ℝ K F := hF_exposed.isExtreme
  have hF_extPts_sub : Set.extremePoints ℝ F ⊆ Set.extremePoints ℝ K :=
    hF_extreme.extremePoints_subset_extremePoints
  -- Step 5: vectorSpan F ≤ ker f and ker f has finrank n.
  -- f ≠ 0: otherwise hf_lt a : 0 < 0 at any a ∈ interior K.
  have hf_ne_zero : f ≠ 0 := by
    intro hf0
    obtain ⟨a, ha⟩ := h_int_ne
    have hcontra := hf_lt a ha
    rw [hf0] at hcontra
    exact lt_irrefl _ hcontra
  have hf_lin_ne : (f : E →ₗ[ℝ] ℝ) ≠ 0 := fun hf0 =>
    hf_ne_zero (by ext a; simpa using LinearMap.congr_fun hf0 a)
  have h_vs_F_le_ker : vectorSpan ℝ F ≤ LinearMap.ker (f : E →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    change y₁ -ᵥ y₂ ∈ LinearMap.ker (f : E →ₗ[ℝ] ℝ)
    rw [vsub_eq_sub]
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub]
    rw [hy₁.2, hy₂.2, sub_self]
  -- range f is a nonzero submodule of ℝ, hence equal to ⊤, hence finrank 1.
  have h_range_top : LinearMap.range (f : E →ₗ[ℝ] ℝ) = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range (f : E →ₗ[ℝ] ℝ)) with h | h
    · exfalso; apply hf_lin_ne; rwa [LinearMap.range_eq_bot] at h
    · exact h
  have h_range_finrank : Module.finrank ℝ (LinearMap.range (f : E →ₗ[ℝ] ℝ)) = 1 := by
    rw [h_range_top]; simp
  have h_ker_finrank : Module.finrank ℝ (LinearMap.ker (f : E →ₗ[ℝ] ℝ)) = n := by
    have h_rn := LinearMap.finrank_range_add_finrank_ker (f : E →ₗ[ℝ] ℝ)
    rw [h_range_finrank, h_finrank_E] at h_rn
    omega
  have h_vs_F_finrank : Module.finrank ℝ (vectorSpan ℝ F) ≤ n := by
    have hmono := Submodule.finrank_mono (R := ℝ) (M := E) h_vs_F_le_ker
    rw [h_ker_finrank] at hmono
    exact hmono
  -- Step 6: descend onto F via IH (using descent helper).
  have hF_sub_hull : F ⊆ convexHull ℝ (Set.extremePoints ℝ F) :=
    minkowski_descent_aux IH hF_compact hF_convex h_vs_F_finrank
  have hxF_hull : x ∈ convexHull ℝ (Set.extremePoints ℝ F) := hF_sub_hull hxF
  -- Step 7: assemble — extremePoints F ⊆ extremePoints K monotonicity gives the goal.
  exact convexHull_mono hF_extPts_sub hxF_hull

/-- Closure-free Minkowski parametrized by dimension: For every finite-dimensional normed space `E`
with `finrank ℝ E ≤ n` and every compact convex `K ⊆ E`, `K ⊆ convexHull ℝ (extremePoints ℝ K)`.
Proved by induction on `n`. -/
private theorem minkowski_aux : ∀ (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    Module.finrank ℝ E ≤ n → ∀ {K : Set E},
    IsCompact K → Convex ℝ K →
    K ⊆ convexHull ℝ (Set.extremePoints ℝ K) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ h_dim K _ _ x hxK
    -- finrank E = 0 ⇒ Subsingleton E; so K ⊆ {0} and 0 is extreme.
    rw [Nat.le_zero] at h_dim
    haveI : Subsingleton E := (Module.finrank_eq_zero_iff_of_free ℝ E).mp h_dim
    have h_K_sub : K = {x} := by
      ext y
      refine ⟨fun _ => Subsingleton.elim y x ▸ rfl, fun hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hxK
    rw [h_K_sub, extremePoints_singleton (x := x)]
    exact subset_convexHull ℝ _ rfl
  | succ n IH =>
    intro E _ _ _ h_dim K hK_compact hK_convex
    -- Strategy: at every dimension, either K's `vectorSpan` is already ≤ n
    -- (so K fits in a smaller normed space and we apply IH via descent), or
    -- we apply the boundary/interior argument in E proper.
    --
    -- This is split into three named helpers:
    -- * `minkowski_descent_aux` — handles `vectorSpan K ≤ n` via Submodule.
    -- * `minkowski_interior_aux` — `x ∈ interior K` (ray to boundary).
    -- * `minkowski_frontier_aux` — `x ∈ K \ interior K` (supporting hyperplane
    --   yields a proper exposed face).
    by_cases h_vs : Module.finrank ℝ (vectorSpan ℝ K) ≤ n
    · exact minkowski_descent_aux IH hK_compact hK_convex h_vs
    · push Not at h_vs
      -- vectorSpan K has dim > n, but ≤ dim E ≤ n+1, so dim = n+1.
      -- Hence affineSpan K = ⊤ and K has nonempty interior in E.
      intro x hxK
      by_cases hx_int : x ∈ interior K
      · exact minkowski_interior_aux IH hK_compact hK_convex h_dim h_vs
          (fun z hzK hz_not_int =>
            minkowski_frontier_aux IH hK_compact hK_convex h_dim h_vs hzK hz_not_int)
          hxK hx_int
      · exact minkowski_frontier_aux IH hK_compact hK_convex h_dim h_vs hxK hx_int

/-- **Closure-free Minkowski theorem in finite dimension.**  For a compact convex set `K` in
`EuclideanSpace ℝ (Fin n)`, every point of `K` lies in the convex hull of the extreme points of `K`
— the closure-free strengthening of Mathlib's `closure_convexHull_extremePoints`. -/
theorem subset_convexHull_extremePoints_of_compact_convex {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    K ⊆ convexHull ℝ (Set.extremePoints ℝ K) :=
  minkowski_aux n (finrank_euclideanSpace_fin (n := n)).le hK_compact hK_convex

/-! ## Compact convex hull in finite dimension and Milman's theorem -/

/-- **Compact convex hull in finite dimension.**  The convex hull of a compact subset of
`EuclideanSpace ℝ (Fin n)` is compact, generalizing Mathlib's finite-set version
`Set.Finite.isCompact_convexHull`. -/
theorem isCompact_convexHull_of_isCompact {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    IsCompact (convexHull ℝ A) := by
  classical
  rcases A.eq_empty_or_nonempty with hA_empty | ⟨a₀, ha₀⟩
  · rw [hA_empty, convexHull_empty]; exact isCompact_empty
  -- Parameter space P := stdSimplex × A^(n+1) and combination map f.
  set P : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → EuclideanSpace ℝ (Fin n))) :=
    stdSimplex ℝ (Fin (n + 1)) ×ˢ Set.univ.pi (fun _ : Fin (n + 1) => A) with hP_def
  have hP_compact : IsCompact P :=
    (isCompact_stdSimplex ℝ (Fin (n + 1))).prod (isCompact_univ_pi (fun _ => hA))
  let f : (Fin (n + 1) → ℝ) × (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) →
          EuclideanSpace ℝ (Fin n) := fun p => ∑ i, p.1 i • p.2 i
  have hf_cont : Continuous f := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((continuous_apply i).comp continuous_fst).smul
            ((continuous_apply i).comp continuous_snd)
  suffices h_image : f '' P = convexHull ℝ A by
    rw [← h_image]; exact hP_compact.image hf_cont
  apply Set.eq_of_subset_of_subset
  · -- f '' P ⊆ convexHull A: any convex combo of A-points is in convexHull A.
    rintro y ⟨⟨lam, xfun⟩, ⟨hlam_simp, hx_mem⟩, rfl⟩
    have hx_in_A : ∀ i, xfun i ∈ A := fun i => hx_mem i (Set.mem_univ _)
    have hlam_nn : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ lam i :=
      fun i _ => hlam_simp.1 i
    have hlam_sum : ∑ i, lam i = 1 := hlam_simp.2
    have h_cm : (Finset.univ : Finset (Fin (n + 1))).centerMass lam xfun
                = ∑ i, lam i • xfun i := by
      rw [Finset.centerMass, hlam_sum, inv_one, one_smul]
    change (∑ i, lam i • xfun i) ∈ convexHull ℝ A
    rw [← h_cm]
    exact Finset.centerMass_mem_convexHull _ hlam_nn
      (by rw [hlam_sum]; exact zero_lt_one) (fun i _ => hx_in_A i)
  · -- convexHull A ⊆ f '' P: padding step using Carathéodory finite-dim.
    intro y hy
    obtain ⟨ι, hι_fin, z, w, hzs, hzi, hw_pos, hw_sum, hw_combo⟩ :=
      eq_pos_convex_span_of_mem_convexHull hy
    letI : Fintype ι := hι_fin
    -- Cardinality bound from affine independence in finrank-n space.
    have hcard_le : Fintype.card ι ≤ n + 1 := by
      have hAI := hzi.card_le_finrank_succ
      have hvs_le : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z))
                    ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) :=
        Submodule.finrank_le _
      rw [finrank_euclideanSpace_fin] at hvs_le
      linarith
    -- Pad ι to Fin (n+1) via Fintype.equivFin + Fin.castLE.
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let g : ι → Fin (n + 1) := fun i => (e i).castLE hcard_le
    have hg_inj : Function.Injective g := by
      intro i j hij
      exact e.injective (Fin.castLE_injective _ hij)
    -- Padded weight and value functions.
    let lam : Fin (n + 1) → ℝ := fun k =>
      if h : ∃ i, g i = k then w h.choose else 0
    let xfun : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun k =>
      if h : ∃ i, g i = k then z h.choose else a₀
    -- Helper: at k = g i, the Classical.choose picks i back (by injectivity).
    have h_choose : ∀ i,
        (⟨i, rfl⟩ : ∃ j, g j = g i).choose = i := by
      intro i
      have hex : ∃ j, g j = g i := ⟨i, rfl⟩
      exact hg_inj hex.choose_spec
    have h_lam_g : ∀ i, lam (g i) = w i := by
      intro i
      have hex : ∃ j, g j = g i := ⟨i, rfl⟩
      change (if h : ∃ j, g j = g i then w h.choose else 0) = w i
      rw [dif_pos hex]
      congr 1; exact h_choose i
    have h_xfun_g : ∀ i, xfun (g i) = z i := by
      intro i
      have hex : ∃ j, g j = g i := ⟨i, rfl⟩
      change (if h : ∃ j, g j = g i then z h.choose else a₀) = z i
      rw [dif_pos hex]
      congr 1; exact h_choose i
    have h_lam_not_g : ∀ k, (¬ ∃ i, g i = k) → lam k = 0 := by
      intro k hk
      change (if h : ∃ i, g i = k then w h.choose else 0) = 0
      exact dif_neg hk
    -- Shared partition of `Fin (n+1)` into the image of `g` and its complement, with the
    -- complement carrying no `g`-preimage.  Reused by both the weight-sum and the value-sum below.
    have h_split : (Finset.univ : Finset (Fin (n + 1)))
                    = (Finset.univ : Finset ι).image g ∪
                      ((Finset.univ : Finset (Fin (n + 1))) \
                        (Finset.univ : Finset ι).image g) := by
      ext k; simp
    have h_disj : Disjoint ((Finset.univ : Finset ι).image g)
                    ((Finset.univ : Finset (Fin (n + 1))) \
                      (Finset.univ : Finset ι).image g) := Finset.disjoint_sdiff
    have h_not_image : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))) \
                            (Finset.univ : Finset ι).image g, ¬ ∃ i, g i = k := by
      intro k hk ⟨i, hi⟩
      rw [Finset.mem_sdiff] at hk
      exact hk.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    -- (lam, xfun) ∈ P.
    have h_in_P : (lam, xfun) ∈ P := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- lam k ≥ 0
        intro k
        by_cases h : ∃ i, g i = k
        · change (if h' : ∃ i, g i = k then w h'.choose else 0) ≥ 0
          rw [dif_pos h]; exact (hw_pos _).le
        · change (if h' : ∃ i, g i = k then w h'.choose else 0) ≥ 0
          rw [dif_neg h]
      · -- ∑ k, lam k = 1
        rw [h_split, Finset.sum_union h_disj]
        rw [Finset.sum_eq_zero (fun k hk => h_lam_not_g k (h_not_image k hk)), add_zero]
        rw [Finset.sum_image (fun i _ j _ hij => hg_inj hij)]
        rw [Finset.sum_congr rfl (fun i _ => h_lam_g i)]
        exact hw_sum
      · -- xfun k ∈ A.
        intro k _
        by_cases h : ∃ i, g i = k
        · change (if h' : ∃ i, g i = k then z h'.choose else a₀) ∈ A
          rw [dif_pos h]; exact hzs (Set.mem_range_self _)
        · change (if h' : ∃ i, g i = k then z h'.choose else a₀) ∈ A
          rw [dif_neg h]; exact ha₀
    -- f (lam, xfun) = y.
    have h_image_eq : f (lam, xfun) = y := by
      change ∑ k, lam k • xfun k = y
      rw [h_split, Finset.sum_union h_disj]
      have h_zero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))) \
                            (Finset.univ : Finset ι).image g,
                      lam k • xfun k = 0 := fun k hk => by
        rw [h_lam_not_g k (h_not_image k hk), zero_smul]
      rw [Finset.sum_eq_zero h_zero, add_zero]
      rw [Finset.sum_image (fun i _ j _ hij => hg_inj hij)]
      have h_terms : ∀ i ∈ (Finset.univ : Finset ι),
          lam (g i) • xfun (g i) = w i • z i := by
        intro i _; rw [h_lam_g i, h_xfun_g i]
      rw [Finset.sum_congr rfl h_terms]
      exact hw_combo
    exact ⟨(lam, xfun), h_in_P, h_image_eq⟩

/-- The convex hull of a compact subset of `EuclideanSpace ℝ (Fin n)` is closed, so closure is
redundant on it. -/
theorem closure_convexHull_of_isCompact {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    closure (convexHull ℝ A) = convexHull ℝ A :=
  (isCompact_convexHull_of_isCompact hA).isClosed.closure_eq

/-- **Milman's theorem (finite-dim, compact case).**  For a compact subset `A` of
`EuclideanSpace ℝ (Fin n)`, every extreme point of `closure (convexHull A)` lies in `A`. -/
theorem extremePoints_closure_convexHull_subset_of_isCompact {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A) :
    Set.extremePoints ℝ (closure (convexHull ℝ A)) ⊆ A := by
  rw [closure_convexHull_of_isCompact hA]
  exact extremePoints_convexHull_subset

/-! ## Dirac-supported representation on extreme points -/

/-- **Minkowski–Carathéodory probability representation.**  For a compact convex
`K ⊆ EuclideanSpace ℝ (Fin n)` and `x ∈ K`, there exists a probability measure `ν` supported on
`Set.extremePoints ℝ K` with mean `x`.

Used downstream by `extremePoint_caratheodory_finite_dim` in
`Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.MeasurableChoquet`. -/
theorem exists_extremePoint_measure_of_compact_convex {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) :
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
      IsProbabilityMeasure ν ∧
      ν (Set.extremePoints ℝ K) = 1 ∧
      ∫ y, y ∂ν = x := by
  -- x ∈ K ⊆ convexHull (extremePoints K).
  have hx_hull : x ∈ convexHull ℝ (Set.extremePoints ℝ K) :=
    subset_convexHull_extremePoints_of_compact_convex hK_compact hK_convex hx
  -- Carathéodory: positive convex span by ≤ finrank+1 affinely independent points.
  obtain ⟨ι, hι_fin, z, w, hz_range, _hz_ind, hw_pos, hw_sum, hz_combo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_hull
  letI : Fintype ι := hι_fin
  have hzS : ∀ i, z i ∈ Set.extremePoints ℝ K :=
    fun i => hz_range (Set.mem_range_self i)
  obtain ⟨ν, hν_prob, hν_supp, hν_mean⟩ :=
    exists_dirac_combination_of_pos_convex_span (E := EuclideanSpace ℝ (Fin n))
      (w := w) (z := z) hw_pos hw_sum (S := Set.extremePoints ℝ K) hzS
  exact ⟨ν, hν_prob, hν_supp, by rw [hν_mean]; exact hz_combo⟩
