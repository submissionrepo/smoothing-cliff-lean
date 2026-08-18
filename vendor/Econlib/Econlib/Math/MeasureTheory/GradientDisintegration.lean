/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexFaces
public import Econlib.Math.Analysis.ConvexRademacher
public import Econlib.Math.MeasureTheory.AbstractDisintegration
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory Set Function ProbabilityTheory

/-!
# Disintegration of a measure along the gradient fibers of a function

For a standard Borel finite-dimensional inner product real space `E` with a finite measure `μ`, and
for an arbitrary function `f : E → ℝ`, the partition induced by the gradient of `f` — fibers
`∇f⁻¹(y)` for `y ∈ Im ∇f` together with the singular set `{x : ¬ DifferentiableAt ℝ f x}` as one
extra class — admits a strongly consistent disintegration. This is the abstract setoid
disintegration `exists_unique_consistentDisintegration_of_standardBorel` specialized to the
gradient fibers, where the quotient admits a measurable injection into `ℝ` via the gradient.

No convexity of `f` is assumed for the main existence result: The fibers are the level sets of
`∇f`, and they are not claimed here to be convex faces. The convex setting enters only in the
singleton-fibers specialization `consistentDisintegration_eq_dirac_of_singleton_faces`, where a
convexity hypothesis on `f` lets convex-Rademacher discard the singular set.

## Main definitions

* `gradSetoid` — the equivalence relation grouping points by gradient (and grouping all
  non-differentiability points into one class).
* `gradSetoid.quotientEmbedReal` — the measurable injection `Quotient (gradSetoid f) → ℝ`.

## Main statements

* `exists_gradientDisintegration` — existence of a strongly consistent disintegration of `μ` over
  the gradient fibers, for an arbitrary `f : E → ℝ`.
* `class_eq_projectedFace_of_mem_domGrad` — the fiber of a differentiability point `x` is the
  gradient level set `projectedFace f (∇f x)`.
* `consistentDisintegration_eq_dirac_of_singleton_faces` — when `f` is convex and every gradient
  fiber is a singleton, each conditional measure is a Dirac mass.

## References

* Caravenna, L., and S. Daneri. 2010. “The Disintegration of the Lebesgue Measure on the Faces of a
  Convex Function.” *Journal of Functional Analysis* 258 (11): 3604–61.
  [https://doi.org/10.1016/j.jfa.2010.01.024](https://doi.org/10.1016/j.jfa.2010.01.024).

## Tags

disintegration, gradient, gradient fiber, dirac measure, standard borel space
-/

@[expose] public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### The gradient setoid -/

/-- The gradient setoid: `x ~ y` iff both are non-differentiability points, or both are
differentiability points with the same gradient. -/
def gradSetoid (f : E → ℝ) : Setoid E where
  r x y :=
    (x ∈ domGrad f ∧ y ∈ domGrad f ∧ gradient f x = gradient f y) ∨
      (x ∉ domGrad f ∧ y ∉ domGrad f)
  iseqv :=
    { refl := fun x => by
        by_cases h : x ∈ domGrad f
        · exact Or.inl ⟨h, h, rfl⟩
        · exact Or.inr ⟨h, h⟩
      symm := by
        rintro x y (⟨hx, hy, h⟩ | ⟨hx, hy⟩)
        · exact Or.inl ⟨hy, hx, h.symm⟩
        · exact Or.inr ⟨hy, hx⟩
      trans := by
        rintro x y z (⟨hx, hy, hxy⟩ | ⟨hx, hy⟩) (⟨hy', hz, hyz⟩ | ⟨hy', hz⟩)
        · exact Or.inl ⟨hx, hz, hxy.trans hyz⟩
        · exact (hy' hy).elim
        · exact (hy hy').elim
        · exact Or.inr ⟨hx, hz⟩ }

/-! ### The measurable embedding `Quotient (gradSetoid f) ↪ ℝ` -/

namespace gradSetoid

section EmbeddingChain

variable [StandardBorelSpace E]

/-- The auxiliary map `φ : E → ℝ × ℝ` sending `x ∈ dom ∇f` to `(embeddingReal E (∇f x), 1)` and
`x ∉ dom ∇f` to `(0, 0)`.  This is constant on equivalence classes of `gradSetoid f`, descends to
an injection `Quotient (gradSetoid f) → ℝ × ℝ`, and is Borel measurable.  Combined with
`embeddingReal (ℝ × ℝ)`, it produces the measurable injection into `ℝ` required by the abstract
disintegration theorem for strong consistency. -/
noncomputable
def classEncoding (f : E → ℝ) : E → ℝ × ℝ := fun x =>
  ((domGrad f).indicator (fun x => embeddingReal E (gradient f x)) x,
   (domGrad f).indicator (fun _ => (1 : ℝ)) x)

lemma measurable_classEncoding (f : E → ℝ) : Measurable (classEncoding f) := by
  unfold classEncoding
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.indicator
      ((measurable_embeddingReal E).comp (measurable_gradient f))
      (measurableSet_domGrad f)
  · exact Measurable.indicator measurable_const (measurableSet_domGrad f)

omit [BorelSpace E] in
lemma classEncoding_dom {f : E → ℝ} {x : E} (hx : x ∈ domGrad f) :
    classEncoding f x = (embeddingReal E (gradient f x), 1) := by
  unfold classEncoding
  simp [Set.indicator_of_mem hx]

omit [BorelSpace E] in
lemma classEncoding_not_dom {f : E → ℝ} {x : E} (hx : x ∉ domGrad f) :
    classEncoding f x = (0, 0) := by
  unfold classEncoding
  simp [Set.indicator_of_notMem hx]

omit [BorelSpace E] in
lemma classEncoding_eq_of_setoid {f : E → ℝ} {x y : E}
    (h : (gradSetoid f).r x y) : classEncoding f x = classEncoding f y := by
  rcases h with ⟨hx, hy, hxy⟩ | ⟨hx, hy⟩
  · rw [classEncoding_dom hx, classEncoding_dom hy, hxy]
  · rw [classEncoding_not_dom hx, classEncoding_not_dom hy]

/-- The descent of `classEncoding` to `Quotient (gradSetoid f)`. -/
noncomputable
def quotMap (f : E → ℝ) : Quotient (gradSetoid f) → ℝ × ℝ :=
  Quotient.lift (classEncoding f) (fun _ _ h => classEncoding_eq_of_setoid h)

omit [BorelSpace E] in
lemma quotMap_mk (f : E → ℝ) (x : E) :
    quotMap f (@Quotient.mk' _ (gradSetoid f) x) = classEncoding f x := rfl

omit [BorelSpace E] in
lemma injective_quotMap (f : E → ℝ) : Injective (quotMap f) := by
  refine fun α β => ?_
  refine Quotient.inductionOn₂ α β ?_
  intro x y h
  change classEncoding f x = classEncoding f y at h
  change @Quotient.mk' _ (gradSetoid f) x = @Quotient.mk' _ (gradSetoid f) y
  rw [Quotient.eq']
  by_cases hx : x ∈ domGrad f
  · by_cases hy : y ∈ domGrad f
    · rw [classEncoding_dom hx, classEncoding_dom hy] at h
      have : gradient f x = gradient f y :=
        (measurableEmbedding_embeddingReal E).injective (Prod.mk.inj h).1
      exact Or.inl ⟨hx, hy, this⟩
    · rw [classEncoding_dom hx, classEncoding_not_dom hy] at h
      exact absurd (Prod.mk.inj h).2 one_ne_zero
  · by_cases hy : y ∈ domGrad f
    · rw [classEncoding_not_dom hx, classEncoding_dom hy] at h
      exact absurd (Prod.mk.inj h).2 zero_ne_one
    · exact Or.inr ⟨hx, hy⟩

lemma measurable_quotMap (f : E → ℝ) : Measurable (quotMap f) := by
  rw [measurable_from_quotient]
  exact measurable_classEncoding f

/-- The measurable injection `Quotient (gradSetoid f) → ℝ`, witnessing the hypothesis needed for
strong consistency of the gradient disintegration.

We use the standard Borel embedding `ℝ × ℝ → ℝ` to land into `ℝ` from the intermediate space
`ℝ × ℝ` used by `classEncoding`. -/
noncomputable
def quotientEmbedReal (f : E → ℝ) : Quotient (gradSetoid f) → ℝ :=
  embeddingReal (ℝ × ℝ) ∘ quotMap f

lemma measurable_quotientEmbedReal (f : E → ℝ) :
    Measurable (quotientEmbedReal f) :=
  (measurable_embeddingReal _).comp (measurable_quotMap f)

omit [BorelSpace E] in
lemma injective_quotientEmbedReal (f : E → ℝ) :
    Injective (quotientEmbedReal f) :=
  (measurableEmbedding_embeddingReal _).injective.comp (injective_quotMap f)

end EmbeddingChain

end gradSetoid

/-! ### Main theorem: Gradient disintegration -/

/-- **Strongly consistent disintegration of a finite measure along the gradient fibers.**

Let `E` be a nonempty standard Borel finite-dimensional real inner product space and `μ` a finite
measure on `E`.  For an arbitrary `f : E → ℝ` (no convexity assumed), there exists a consistent
disintegration of `μ` over `Quotient (gradSetoid f)`, and it is strongly consistent.

This applies `exists_unique_consistentDisintegration_of_standardBorel` to the gradient setoid,
using the measurable injection `gradSetoid.quotientEmbedReal f : Quotient (gradSetoid f) → ℝ` to
witness strong consistency. -/
theorem exists_gradientDisintegration
    [StandardBorelSpace E] [Nonempty E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → ℝ) :
    ∃ D : ConsistentDisintegration μ (gradSetoid f),
      D.IsStronglyConsistent := by
  obtain ⟨⟨D, _hD_unique⟩, hStrong⟩ :=
    exists_unique_consistentDisintegration_of_standardBorel μ (gradSetoid f)
  exact ⟨D, hStrong (gradSetoid.quotientEmbedReal f)
    (gradSetoid.measurable_quotientEmbedReal f)
    (gradSetoid.injective_quotientEmbedReal f) D⟩

/-! ### Class characterization -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A `gradSetoid` class containing a differentiability point `x` is exactly
`projectedFace f (∇f x)`. -/
lemma class_eq_projectedFace_of_mem_domGrad
    [CompleteSpace E]
    (f : E → ℝ) {x : E} (hx : x ∈ domGrad f) :
    {y : E | (gradSetoid f).r y x} = projectedFace f (gradient f x) := by
  ext y
  simp only [Set.mem_setOf_eq, projectedFace, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hy_dom, _, hgr⟩ | ⟨hy_nd, hx_nd⟩)
    · exact ⟨hy_dom, hgr⟩
    · exact absurd hx hx_nd
  · rintro ⟨hy_dom, hgr⟩
    exact Or.inl ⟨hy_dom, hx, hgr⟩

/-! ### Helper lemmas for the singleton-faces theorem -/

-- TODO: these two should eventually go upstream to Mathlib.

/-- Probability measure concentrated on a singleton equals Dirac at that point. -/
private lemma eq_dirac_of_apply_compl_singleton_eq_zero
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure α} [IsProbabilityMeasure μ] {x : α}
    (hμ : μ {x}ᶜ = 0) : μ = Measure.dirac x := by
  refine Measure.ext fun A hA => ?_
  by_cases hxA : x ∈ A
  · -- μ A = 1: use that μ {x} = 1 (from μ {x}ᶜ = 0).
    have h_singleton : μ {x} = 1 := (prob_compl_eq_zero_iff (MeasurableSet.singleton x)).mp hμ
    have hμA : μ A = 1 := by
      apply le_antisymm prob_le_one
      exact h_singleton ▸ measure_mono (Set.singleton_subset_iff.mpr hxA)
    rw [hμA, Measure.dirac_apply' _ hA, Set.indicator_of_mem hxA]
    rfl
  · have hxAc : A ⊆ {x}ᶜ := fun y hy hy' => hxA (hy' ▸ hy)
    have hμA : μ A = 0 := measure_mono_null hxAc hμ
    rw [hμA, Measure.dirac_apply' _ hA, Set.indicator_of_notMem hxA]

/-- The 0-dimensional Hausdorff measure restricted to a singleton equals Dirac at that point. -/
private lemma hausdorffMeasure_zero_restrict_singleton
    {F : Type*} [EMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    (x : F) :
    (Measure.hausdorffMeasure (0 : ℝ)).restrict ({x} : Set F) = Measure.dirac x := by
  haveI : IsProbabilityMeasure
      ((Measure.hausdorffMeasure (0 : ℝ)).restrict ({x} : Set F)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact MeasureTheory.Measure.hausdorffMeasure_zero_singleton x⟩
  refine eq_dirac_of_apply_compl_singleton_eq_zero ?_
  rw [Measure.restrict_apply (MeasurableSet.compl (MeasurableSet.singleton x))]
  rw [Set.compl_inter_self, measure_empty]

/-! ### Saturation of the singular set under the gradient setoid -/

/-- The complement of `domGrad f` (the singular set) is saturated under `gradSetoid f`: Its
`Quotient.mk'`-preimage of its `Quotient.mk'`-image equals itself. -/
private lemma gradSetoid_compl_domGrad_saturated
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (f : G → ℝ) :
    @Quotient.mk' G (gradSetoid f) ⁻¹'
      (@Quotient.mk' G (gradSetoid f) '' (domGrad f)ᶜ) =
    (domGrad f)ᶜ := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, mem_domGrad]
  constructor
  · rintro ⟨y, hy_nd, hyx⟩
    -- Quotient.mk' y = Quotient.mk' x means y ~ x in gradSetoid f
    have h_rel : (gradSetoid f).r y x := Quotient.exact hyx
    rcases h_rel with ⟨hy_dom, _, _⟩ | ⟨_, hx_nd⟩
    · exact absurd hy_dom hy_nd
    · exact hx_nd
  · intro hx
    exact ⟨x, hx, rfl⟩

/-! ### Singleton-faces theorem -/

/-- **Singleton-faces case of the gradient disintegration.**

When every projected face of `f` is a singleton (e.g., `f` strictly convex), each conditional
measure of any consistent disintegration of `volume.restrict K` over the gradient setoid equals the
Dirac measure at the unique base point.

The mutual absolute continuity statement of Caravenna–Daneri Theorem 3.3 is strengthened here to
equality with the Dirac measure. -/
theorem consistentDisintegration_eq_dirac_of_singleton_faces
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    [StandardBorelSpace E'] [Nonempty E']
    {f : E' → ℝ} {K : Set E'}
    (hf : ConvexOn ℝ Set.univ f)
    (h_sing : ∀ x ∈ domGrad f,
                projectedFace f (gradient f x) = {x})
    (hK : MeasurableSet K) (hKvol : (volume : Measure E') K ≠ ⊤)
    (D : ConsistentDisintegration ((volume : Measure E').restrict K) (gradSetoid f)) :
    ∀ᵐ α ∂(((volume : Measure E').restrict K).map
        (@Quotient.mk' E' (gradSetoid f))),
      ∃ x : E', @Quotient.mk' E' (gradSetoid f) x = α ∧
        x ∈ domGrad f ∧
        x ∈ K ∧
        D.μα α = Measure.dirac x := by
  letI : Setoid E' := gradSetoid f
  haveI : IsFiniteMeasure ((volume : Measure E').restrict K) :=
    ⟨by simpa [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hKvol⟩
  -- Obtain a strongly consistent disintegration D₀.
  obtain ⟨D₀, hStrong⟩ := exists_gradientDisintegration (volume.restrict K) f
  -- Relate D to D₀ via uniqueness: D.μα =ᵐ D₀.μα.
  have h_unique : D.μα =ᵐ[((volume : Measure E').restrict K).map
      (@Quotient.mk' E' (gradSetoid f))] D₀.μα :=
    consistentDisintegration_unique _ _ D D₀
  -- Three a.e. conditions on D₀.
  -- 1. Marginal puts zero mass on the image of the singular set.
  have h_sing_ae : ∀ᵐ α ∂(((volume : Measure E').restrict K).map
      (@Quotient.mk' E' (gradSetoid f))),
      α ∉ @Quotient.mk' E' (gradSetoid f) ''
            (domGrad f : Set E')ᶜ := by
    rw [MeasureTheory.ae_iff]
    -- The set of bad α is exactly the image of the singular set.
    have h_set_eq : {α : Quotient (gradSetoid f) |
        ¬ α ∉ @Quotient.mk' E' (gradSetoid f) ''
                (domGrad f : Set E')ᶜ} =
        @Quotient.mk' E' (gradSetoid f) '' (domGrad f : Set E')ᶜ := by
      ext α; simp
    rw [h_set_eq]
    -- Apply Measure.map_quotient_mk_image_of_isNull.
    have hN_meas : MeasurableSet (domGrad f : Set E')ᶜ :=
      (measurableSet_domGrad f).compl
    have hN_null : ((volume : Measure E').restrict K)
        (domGrad f : Set E')ᶜ = 0 := by
      -- (volume.restrict K) N = volume (N ∩ K) ≤ volume N = 0.
      rw [Measure.restrict_apply hN_meas]
      apply measure_mono_null Set.inter_subset_left
      -- volume (domGrad f)ᶜ = 0 by convex Rademacher.
      have h_rademacher := ConvexOn.ae_differentiableAt hf (E := E')
      rwa [MeasureTheory.ae_iff] at h_rademacher
    have hN_sat : @Quotient.mk' E' (gradSetoid f) ⁻¹'
        (@Quotient.mk' E' (gradSetoid f) '' (domGrad f : Set E')ᶜ) =
        (domGrad f : Set E')ᶜ :=
      gradSetoid_compl_domGrad_saturated (G := E') f
    exact Measure.map_quotient_mk_image_of_isNull hN_meas hN_null hN_sat
  -- 2. Conditional measures of D₀ concentrate on K.
  have h_K_ae : ∀ᵐ α ∂(((volume : Measure E').restrict K).map
      (@Quotient.mk' E' (gradSetoid f))),
      D₀.μα α Kᶜ = 0 :=
    ConsistentDisintegration.ae_apply_compl_of_restrict D₀ hK
  -- 3. Strong consistency: D₀.μα α concentrates on the class of α.
  have h_str_ae : ∀ᵐ α ∂(((volume : Measure E').restrict K).map
      (@Quotient.mk' E' (gradSetoid f))),
      D₀.μα α {z | @Quotient.mk' E' (gradSetoid f) z ≠ α} = 0 :=
    hStrong
  -- Combine all four a.e. conditions (including the uniqueness of D vs D₀).
  filter_upwards [h_unique, h_sing_ae, h_K_ae, h_str_ae]
      with α h_eq h_dom h_K_α h_str_α
  -- Extract a representative x for α.
  obtain ⟨x, hx_class⟩ := Quotient.exists_rep α
  -- x must be in domGrad f (else α would be in the image of the singular set).
  have hx_dom : x ∈ domGrad f := by
    by_contra h
    exact h_dom ⟨x, h, hx_class⟩
  -- The equivalence class of α (as a set in E') equals {x}.
  have h_class_eq :
      {z : E' | @Quotient.mk' E' (gradSetoid f) z = α} = {x} := by
    rw [← hx_class]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hr : (gradSetoid f).r z x := Quotient.exact h
      -- Under singleton-faces, gradSetoid r z x ↔ z = x.
      rcases hr with ⟨hz_dom, _, hgrad⟩ | ⟨_, hx_nd⟩
      · -- Both in domGrad with same gradient; h_sing forces z = x.
        have hz_face := h_sing z hz_dom
        rw [hgrad] at hz_face
        have hx_face := h_sing x hx_dom
        have : ({z} : Set E') = {x} := hz_face.symm.trans hx_face
        exact Set.singleton_eq_singleton_iff.mp this
      · exact absurd hx_dom hx_nd
    · rintro rfl; rfl
  -- D₀.μα α concentrates on {x}: {x}ᶜ ⊆ {z | Quotient.mk' z ≠ α}.
  have h_compl_eq : ({x} : Set E')ᶜ =
      {z : E' | @Quotient.mk' E' (gradSetoid f) z ≠ α} := by
    rw [← h_class_eq]; ext z; simp
  have h_conc : D₀.μα α ({x} : Set E')ᶜ = 0 := by
    rw [h_compl_eq]; exact h_str_α
  -- D₀ is a probability measure on E', so it equals Dirac x.
  haveI : IsProbabilityMeasure (D₀.μα α) := D₀.isProbabilityMeasure α
  have h_dirac_D₀ : D₀.μα α = Measure.dirac x :=
    eq_dirac_of_apply_compl_singleton_eq_zero h_conc
  -- x ∈ K: otherwise D₀.μα α K = 0 but also = 1, contradiction.
  have hx_in_K : x ∈ K := by
    by_contra h_xnotK
    have h_K_sub : K ⊆ ({x} : Set E')ᶜ := fun y hy => by
      simp only [mem_compl_iff, mem_singleton_iff]; rintro rfl; exact h_xnotK hy
    have h_K_zero : D₀.μα α K = 0 := measure_mono_null h_K_sub h_conc
    have h_K_one : D₀.μα α K = 1 := (prob_compl_eq_zero_iff hK).mp h_K_α
    rw [h_K_zero] at h_K_one
    exact absurd h_K_one (by simp)
  -- D.μα α = D₀.μα α a.e.; at this α, h_eq gives D.μα α = D₀.μα α.
  exact ⟨x, hx_class, hx_dom, hx_in_K, h_eq.trans h_dirac_D₀⟩

end MeasureTheory
