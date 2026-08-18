/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Abstract disintegration along a setoid partition

For a standard Borel space `X` with a finite measure `μ` and a partition of `X` encoded as a
`Setoid`, we construct a consistent disintegration of `μ` over the quotient space, prove its
uniqueness up to a `μ.map Quotient.mk'`-null set, and show it is strongly consistent whenever the
quotient admits a measurable injection into `ℝ`.

## Main definitions

* `ConsistentDisintegration` — a family `μα : Quotient s → Measure X` of probability measures with
  measurable evaluation and satisfying the disintegration formula.
* `ConsistentDisintegration.IsStronglyConsistent` — each `μα α` is concentrated on the partition
  class of `α`, `μ.map Quotient.mk'`-a.e.

## Main statements

* `exists_consistentDisintegration` — existence of a consistent disintegration.
* `consistentDisintegration_unique` — uniqueness up to a `μ.map Quotient.mk'`-null set.
* `ConsistentDisintegration.isStronglyConsistent_of_injection` — strong consistency under a
  measurable injection of the quotient into `ℝ`.
* `exists_unique_consistentDisintegration_of_standardBorel` — the combined statement.

## Notes

This is the abstract disintegration theorem of Caravenna–Daneri (2010), §2, Theorem 2.3. The
countably-generated hypothesis of the paper is strengthened here to
`[StandardBorelSpace X] [Nonempty X]`, which is sufficient for our purposes and which matches the
only application in the paper (`X = ℝⁿ`, §3.1).

## References

* Caravenna, L., and S. Daneri. 2010. “The Disintegration of the Lebesgue Measure on the Faces of a
  Convex Function.” *Journal of Functional Analysis* 258 (11): 3604–61.
  [https://doi.org/10.1016/j.jfa.2010.01.024](https://doi.org/10.1016/j.jfa.2010.01.024).

## Tags

disintegration, conditional measure, standard borel space, setoid partition
-/

@[expose] public section

open MeasureTheory Set Filter MeasurableSpace ProbabilityTheory Function
open scoped ENNReal MeasureTheory Topology

namespace MeasureTheory

/-! ## Definition 2.1 (Disintegration)

A disintegration of `μ : Measure X` consistent with the partition induced by a setoid `s` is a
family `μα : Quotient s → Measure X` of probability measures satisfying

* the **measurability** of `α ↦ μα α E` for every measurable `E ⊆ X`;
* the **disintegration formula**
  `μ (E ∩ Quotient.mk' ⁻¹' F) = ∫⁻ α in F, μα α E ∂(μ.map Quotient.mk')` for all measurable `E ⊆ X`
  and `F ⊆ Quotient s`. -/

variable {X : Type*}

/-- A disintegration of `μ : Measure X` consistent with a partition encoded by `s : Setoid X`. -/
structure ConsistentDisintegration [MeasurableSpace X]
    (μ : Measure X) (s : Setoid X) where
  /-- The family of conditional probability measures. -/
  μα : Quotient s → Measure X
  /-- Each conditional measure is a probability measure. -/
  isProbabilityMeasure : ∀ α, IsProbabilityMeasure (μα α)
  /-- For every measurable `E ⊆ X`, the function `α ↦ μα α E` is measurable. -/
  measurable_apply : ∀ ⦃E : Set X⦄, MeasurableSet E → Measurable fun α => μα α E
  /-- The disintegration formula `μ (E ∩ p ⁻¹' F) = ∫⁻ α in F, μα α E ∂(μ.map p)`, where
  `p = Quotient.mk'`. -/
  apply_eq_setLIntegral :
    ∀ ⦃E : Set X⦄ ⦃F : Set (Quotient s)⦄, MeasurableSet E → MeasurableSet F →
      μ (E ∩ (Quotient.mk' : X → Quotient s) ⁻¹' F) =
        ∫⁻ α in F, μα α E ∂(μ.map (Quotient.mk' : X → Quotient s))

attribute [instance] ConsistentDisintegration.isProbabilityMeasure

/-- The disintegration is **strongly consistent** with `p` when each `μα α` is concentrated on the
partition class `p⁻¹{α}`, for `μ.map p`-a.e. `α`. -/
def ConsistentDisintegration.IsStronglyConsistent
    [MeasurableSpace X] {μ : Measure X} {s : Setoid X}
    (D : ConsistentDisintegration μ s) : Prop :=
  ∀ᵐ α ∂(μ.map (Quotient.mk' : X → Quotient s)),
    D.μα α {x | (Quotient.mk' x : Quotient s) ≠ α} = 0

/-! ## The standard Borel disintegration kernel

The disintegration kernel is `MeasureTheory.Measure.condKernel` applied to the joint measure on
`Quotient s × X` obtained by pushing `μ` forward along `x ↦ (Quotient.mk x, x)`. -/

section StandardBorel

variable [MeasurableSpace X]

/-- Push-forward of `μ` along `x ↦ (Quotient.mk' x, x) : X → Quotient s × X`. This is the joint
distribution of `(p, id)` under `μ`. -/
noncomputable
def joint (μ : Measure X) (s : Setoid X) : Measure (Quotient s × X) :=
  μ.map (fun x => ((Quotient.mk' x : Quotient s), x))

lemma measurable_joint_map {s : Setoid X} :
    Measurable (fun x : X => ((Quotient.mk' x : Quotient s), x)) :=
  measurable_quotient_mk''.prodMk measurable_id

instance {μ : Measure X} [IsFiniteMeasure μ] {s : Setoid X} :
    IsFiniteMeasure (joint μ s) := by
  unfold joint; infer_instance

lemma joint_apply (μ : Measure X) (s : Setoid X)
    {E : Set X} {F : Set (Quotient s)}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    joint μ s (F ×ˢ E) = μ (E ∩ (Quotient.mk' : X → Quotient s) ⁻¹' F) := by
  rw [joint, Measure.map_apply measurable_joint_map (hF.prod hE)]
  congr 1
  ext x
  simp [and_comm]

lemma joint_fst (μ : Measure X) (s : Setoid X) :
    (joint μ s).fst = μ.map (Quotient.mk' : X → Quotient s) := by
  rw [joint, Measure.fst, Measure.map_map measurable_fst measurable_joint_map]
  rfl

variable [StandardBorelSpace X] [Nonempty X]

/-- The Markov kernel that disintegrates `μ` along the quotient map: This is `Measure.condKernel`
applied to the joint measure. -/
noncomputable
def baseKernel (μ : Measure X) [IsFiniteMeasure μ] (s : Setoid X) :
    Kernel (Quotient s) X :=
  (joint μ s).condKernel

instance {μ : Measure X} [IsFiniteMeasure μ] {s : Setoid X} :
    IsMarkovKernel (baseKernel μ s) := by
  unfold baseKernel; infer_instance

lemma baseKernel_disintegrate (μ : Measure X) [IsFiniteMeasure μ]
    (s : Setoid X) :
    (joint μ s).fst ⊗ₘ baseKernel μ s = joint μ s :=
  (joint μ s).disintegrate (joint μ s).condKernel

end StandardBorel

/-! ### Existence of a consistent disintegration -/

section Existence

variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsFiniteMeasure μ] (s : Setoid X)

/-- **Existence of the consistent disintegration** (first half of Theorem 2.3). -/
theorem exists_consistentDisintegration :
    Nonempty (ConsistentDisintegration μ s) := by
  refine ⟨{
    μα := baseKernel μ s
    isProbabilityMeasure := fun α => inferInstance
    measurable_apply := fun E hE => Kernel.measurable_coe (baseKernel μ s) hE
    apply_eq_setLIntegral := ?_ }⟩
  intro E F hE hF
  -- Combine the disintegration `(joint μ s).fst ⊗ₘ baseKernel = joint μ s`
  -- with the identification of `(joint μ s).fst` with `μ.map Quotient.mk'`.
  calc μ (E ∩ (Quotient.mk' : X → Quotient s) ⁻¹' F)
      = joint μ s (F ×ˢ E) := (joint_apply μ s hE hF).symm
    _ = ((joint μ s).fst ⊗ₘ baseKernel μ s) (F ×ˢ E) := by
        rw [baseKernel_disintegrate]
    _ = ∫⁻ α in F, baseKernel μ s α E ∂(joint μ s).fst :=
        Measure.compProd_apply_prod hF hE
    _ = ∫⁻ α in F, baseKernel μ s α E ∂(μ.map (Quotient.mk' : X → Quotient s)) := by
        rw [joint_fst μ s]

end Existence

/-! ### Uniqueness of consistent disintegrations -/

section Uniqueness

variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsFiniteMeasure μ] (s : Setoid X)

/-- The kernel built from `D.μα`, considered as a `Kernel (Quotient s) X`. -/
noncomputable
def kernelOfDisintegration (D : ConsistentDisintegration μ s) :
    Kernel (Quotient s) X :=
  ⟨D.μα, Measure.measurable_of_measurable_coe _ fun _ hE => D.measurable_apply hE⟩

instance (D : ConsistentDisintegration μ s) :
    IsMarkovKernel (kernelOfDisintegration μ s D) :=
  ⟨fun α => D.isProbabilityMeasure α⟩

omit [StandardBorelSpace X] [Nonempty X] in
/-- A consistent disintegration `D` of `μ` yields a Markov kernel that disintegrates the joint
measure `(p, id)_# μ` on `Quotient s × X` along its first marginal. -/
lemma kernel_of_consistentDisintegration
    (D : ConsistentDisintegration μ s) :
    (joint μ s).fst ⊗ₘ kernelOfDisintegration μ s D = joint μ s := by
  set κ := kernelOfDisintegration μ s D
  -- It suffices to compare the two finite measures on measurable rectangles.
  refine Measure.ext_prod ?_
  intro F E hF hE
  -- LHS: (joint.fst ⊗ₘ κ)(F ×ˢ E) = ∫_F κ α E ∂joint.fst
  rw [Measure.compProd_apply_prod hF hE]
  -- RHS: joint(F ×ˢ E) = μ (E ∩ p⁻¹(F))
  rw [joint_apply μ s hE hF]
  -- Use D's disintegration formula and `joint_fst`.
  rw [joint_fst μ s]
  exact (D.apply_eq_setLIntegral hE hF).symm

/-- **Uniqueness of the consistent disintegration**: Any two consistent disintegrations of `μ` give
the same conditional measure `μ.map p`-a.e., where `p = Quotient.mk'`.  This is the standard
"unique up to a `μ.map p`-null set" statement of Definition 2.1. -/
theorem consistentDisintegration_unique
    (D D' : ConsistentDisintegration μ s) :
    D.μα =ᵐ[μ.map (Quotient.mk' : X → Quotient s)] D'.μα := by
  set κ₁ := kernelOfDisintegration μ s D
  set κ₂ := kernelOfDisintegration μ s D'
  have h1 : joint μ s = (joint μ s).fst ⊗ₘ κ₁ :=
    (kernel_of_consistentDisintegration μ s D).symm
  have h2 : joint μ s = (joint μ s).fst ⊗ₘ κ₂ :=
    (kernel_of_consistentDisintegration μ s D').symm
  have hae1 : ∀ᵐ α ∂(joint μ s).fst, κ₁ α = (joint μ s).condKernel α :=
    eq_condKernel_of_measure_eq_compProd κ₁ h1
  have hae2 : ∀ᵐ α ∂(joint μ s).fst, κ₂ α = (joint μ s).condKernel α :=
    eq_condKernel_of_measure_eq_compProd κ₂ h2
  have hae : ∀ᵐ α ∂(joint μ s).fst, κ₁ α = κ₂ α := by
    filter_upwards [hae1, hae2] with α h1 h2
    rw [h1, h2]
  rwa [joint_fst μ s] at hae

/-- A weaker form: Pointwise (per-set) `μ.map p`-a.e. agreement of two consistent disintegrations
on each measurable `E`. -/
lemma consistentDisintegration_apply_ae_eq
    (D D' : ConsistentDisintegration μ s) (E : Set X) :
    (fun α => D.μα α E)
      =ᵐ[μ.map (Quotient.mk' : X → Quotient s)]
      (fun α => D'.μα α E) := by
  filter_upwards [consistentDisintegration_unique μ s D D'] with α h
  rw [h]

end Uniqueness

/-! ### General disintegration facts -/

section GeneralFacts

variable [MeasurableSpace X]

/-- For any `ConsistentDisintegration D` of `μ.restrict S` where `S` is measurable, the conditional
measures `D.μα α` are concentrated on `S` for `(μ.restrict S).map Quotient.mk'`-a.e. `α`. -/
lemma ConsistentDisintegration.ae_apply_compl_of_restrict
    {μ : Measure X} {s : Setoid X} {S : Set X}
    (D : ConsistentDisintegration (μ.restrict S) s) (hS : MeasurableSet S) :
    ∀ᵐ α ∂((μ.restrict S).map (Quotient.mk' : X → Quotient s)),
      D.μα α Sᶜ = 0 := by
  -- Apply the disintegration formula with E = Sᶜ, F = univ.
  have h_univ : MeasurableSet (Set.univ : Set (Quotient s)) := MeasurableSet.univ
  have h_disint := D.apply_eq_setLIntegral hS.compl h_univ
  rw [Set.preimage_univ, Set.inter_univ] at h_disint
  rw [Measure.restrict_apply hS.compl, Set.inter_comm, Set.inter_compl_self,
      measure_empty] at h_disint
  rw [setLIntegral_univ] at h_disint
  exact (lintegral_eq_zero_iff (D.measurable_apply hS.compl)).mp h_disint.symm

/-- The pushforward of a measure through `Quotient.mk'` assigns zero mass to the image
`Quotient.mk' '' N` of any null measurable set `N` that is saturated under the equivalence relation
(i.e. `Quotient.mk' ⁻¹' (Quotient.mk' '' N) = N`). -/
lemma Measure.map_quotient_mk_image_of_isNull
    {μ : Measure X} {s : Setoid X}
    {N : Set X} (hN_meas : MeasurableSet N) (hN_null : μ N = 0)
    (hN_closed : (Quotient.mk' : X → Quotient s) ⁻¹'
                   ((Quotient.mk' : X → Quotient s) '' N) = N) :
    μ.map (Quotient.mk' : X → Quotient s)
      ((Quotient.mk' : X → Quotient s) '' N) = 0 := by
  -- The image is measurable: its preimage under `Quotient.mk'` equals `N`
  -- (by hN_closed), which is measurable.
  have h_img_meas : MeasurableSet ((Quotient.mk' : X → Quotient s) '' N) := by
    rw [measurableSet_quotient]
    show MeasurableSet ((Quotient.mk'' : X → Quotient s) ⁻¹'
      ((Quotient.mk' : X → Quotient s) '' N))
    have : (Quotient.mk'' : X → Quotient s) = (Quotient.mk' : X → Quotient s) := rfl
    rw [this, hN_closed]
    exact hN_meas
  rw [Measure.map_apply measurable_quotient_mk' h_img_meas, hN_closed, hN_null]

end GeneralFacts

/-! ### Strong consistency under a measurable injection to ℝ -/

section StrongConsistency

variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsFiniteMeasure μ] {s : Setoid X}

omit [StandardBorelSpace X] [Nonempty X] in
/-- If `Quotient s` admits a measurable injection into `(ℝ, B(ℝ))` then every consistent
disintegration of `μ` is strongly consistent. -/
theorem ConsistentDisintegration.isStronglyConsistent_of_injection
    (D : ConsistentDisintegration μ s)
    {i : Quotient s → ℝ} (hi_meas : Measurable i) (hi_inj : Injective i) :
    D.IsStronglyConsistent := by
  -- Work with the joint set `H := {(α, x) | i α ≠ i (p x)}`, whose `μ.map p`-marginal slices
  -- recover the partition complements `{x | p x ≠ α}` by injectivity of `i`. Since `joint μ s H`
  -- is `μ` of the diagonal `{x | i (p x) ≠ i (p x)} = ∅`, the disintegration forces the slice
  -- masses to vanish `μ.map p`-a.e.
  let p : X → Quotient s := Quotient.mk'
  set ν : Measure (Quotient s) := μ.map p with hν
  -- The diagonal-complement set
  let H : Set (Quotient s × X) := {q | i q.1 ≠ i (p q.2)}
  have hH_meas : MeasurableSet H := by
    have h1 : Measurable (fun q : Quotient s × X => i q.1) := hi_meas.comp measurable_fst
    have h2 : Measurable (fun q : Quotient s × X => i (p q.2)) :=
      (hi_meas.comp measurable_quotient_mk'').comp measurable_snd
    exact (measurableSet_eq_fun h1 h2).compl
  -- The non-diagonal set on the X-side:
  let G : Quotient s → Set X := fun α => {x | i α ≠ i (p x)}
  have hG_meas : ∀ α, MeasurableSet (G α) := fun α => by
    have : Measurable (fun x : X => i (p x)) :=
      (hi_meas.comp measurable_quotient_mk'')
    exact (measurableSet_eq_fun measurable_const this).compl
  -- Connect G α and the partition complement: by injectivity of i,
  --   G α = {x | p x ≠ α}.
  have hG_eq : ∀ α, G α = {x : X | p x ≠ α} := by
    intro α
    ext x
    simp only [G, p, mem_setOf_eq, ne_eq]
    exact ⟨fun h h' => h (h' ▸ rfl), fun h h' => h (hi_inj h'.symm)⟩
  -- The slice masses `α ↦ μα α (G α)` live on the diagonal, so they are accessed through the
  -- joint integral of `H` rather than the bare disintegration formula.
  have hjoint_H : joint μ s H = 0 := by
    -- (joint μ s)(H) = μ ((fun x => (p x, x)) ⁻¹' H) = μ {x | i (p x) ≠ i (p x)} = 0
    rw [joint, Measure.map_apply (measurable_joint_map (s := s)) hH_meas]
    convert measure_empty (μ := μ)
    ext x
    simp [H, p]
  -- Under the disintegration `joint = ν ⊗ₘ κ`, `compProd_apply` rewrites `joint H` as
  -- `∫⁻ α, κ α (slice α) ∂ν` with `slice α = G α`, identifying it with the slice masses.
  set κ := kernelOfDisintegration μ s D
  have hjoint_compProd : joint μ s = (joint μ s).fst ⊗ₘ κ :=
    (kernel_of_consistentDisintegration μ s D).symm
  -- Measurability of `α ↦ κ α (G α)`: rewrite `G α` as `Prod.mk α ⁻¹' H`
  -- and apply `measurable_kernel_prodMk_left`.
  have h_slice : ∀ α, Prod.mk α ⁻¹' H = G α := by
    intro α; ext x; simp [H, G, p]
  have h_meas_int : Measurable (fun α => κ α (G α)) := by
    -- `measurable_kernel_prodMk_left` gives measurability of the `H`-slice
    -- `α ↦ κ α (Prod.mk α ⁻¹' H)`, which equals `α ↦ κ α (G α)` by `h_slice`.
    simp_rw [← h_slice]
    exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hH_meas
  have h_int_eq :
      ∫⁻ α, κ α (G α) ∂((joint μ s).fst) = joint μ s H := by
    conv_rhs => rw [hjoint_compProd]
    rw [Measure.compProd_apply hH_meas]
    refine lintegral_congr ?_
    intro α; rw [h_slice]
  rw [hjoint_H] at h_int_eq
  have hae : ∀ᵐ α ∂(joint μ s).fst, κ α (G α) = 0 :=
    (lintegral_eq_zero_iff h_meas_int).mp h_int_eq
  rw [joint_fst] at hae
  -- Convert `κ α (G α) = 0` to `D.μα α {x | p x ≠ α} = 0`.
  filter_upwards [hae] with α hα
  show D.μα α {x | (Quotient.mk' x : Quotient s) ≠ α} = 0
  -- `κ α = D.μα α` definitionally, so `hα : κ α (G α) = 0` is `D.μα α (G α) = 0`;
  -- `hG_eq` identifies `G α` with the partition complement.
  rw [← hG_eq]; exact hα

end StrongConsistency

/-! ### The combined existence + uniqueness + strong consistency statement -/

section ExistsUnique

variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
variable (μ : Measure X) [IsFiniteMeasure μ] (s : Setoid X)

/-- **Existence, uniqueness, and strong consistency of the disintegration.**

Let `X` be a nonempty standard Borel space with a finite measure `μ`.  Then for every partition of
`X` (encoded as a setoid `s`) there is a consistent disintegration `{μα}_α` of `μ` over the
quotient `Quotient s`, uniquely determined `μ.map Quotient.mk'`-a.e.  Moreover, whenever
`Quotient s` admits a measurable injection into `(ℝ, B(ℝ))`, every consistent disintegration is
strongly consistent. -/
theorem exists_unique_consistentDisintegration_of_standardBorel :
    (∃ D : ConsistentDisintegration μ s,
        ∀ D' : ConsistentDisintegration μ s,
          D.μα =ᵐ[μ.map (Quotient.mk' : X → Quotient s)] D'.μα) ∧
    (∀ (i : Quotient s → ℝ), Measurable i → Injective i →
        ∀ D : ConsistentDisintegration μ s, D.IsStronglyConsistent) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨D⟩ := exists_consistentDisintegration μ s
    exact ⟨D, fun D' => consistentDisintegration_unique μ s D D'⟩
  · intro i hi hinj D
    exact D.isStronglyConsistent_of_injection μ hi hinj

end ExistsUnique

end MeasureTheory
