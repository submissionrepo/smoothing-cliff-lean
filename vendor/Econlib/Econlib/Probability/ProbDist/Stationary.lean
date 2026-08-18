/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Tychonoff
public import Econlib.Probability.ProbDist.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Invariance

/-!
# Feller kernels and existence of invariant probability measures

A Markov kernel is **Feller** if its measure-valued map `a ↦ κ a` is weak-* continuous into
`ProbabilityMeasure β`. On a nonempty compact metrizable space such a kernel admits an invariant
probability law: The **Krylov–Bogolyubov theorem**, obtained here by embedding
`ProbabilityMeasure α` into a locally convex space and applying the Tychonoff fixed-point theorem
to the kernel action.

## Main definitions

* `ProbabilityTheory.IsFellerKernel` — a Markov kernel whose measure-valued map `a ↦ κ a` is
  continuous into `ProbabilityMeasure β` (weak-* topology).

## Main statements

* `ProbabilityTheory.IsFellerKernel.boundedContinuousFunction_integral_kernel` — integrating a
  bounded continuous function against a Feller kernel yields a bounded continuous function.
* `ProbabilityTheory.IsFellerKernel.continuous_compMeasure` — `μ ↦ κ ∘ₘ μ` is continuous on
  `ProbabilityMeasure`.
* `exists_invariant_probDist` — **Krylov–Bogolyubov theorem**: Every Feller kernel on a nonempty
  compact metrizable space has an invariant probability measure.

## References

* Krylov, Nikolai, and Nikolai Bogolyubov. 1937. “La Theorie Generale De La Mesure Dans Son
  Application a L'etude Des Systemes Dynamiques De La Mecanique Non Lineaire.” *Annals of
  Mathematics* 38 (1): 65–113.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BoundedContinuousFunction

/-! ## Feller kernels -/

namespace ProbabilityTheory

/-- The map `a ↦ κ a` viewed as a function into `ProbabilityMeasure β`. -/
noncomputable def Kernel.toProbabilityMeasure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] : α → ProbabilityMeasure β :=
  fun a => ⟨κ a, inferInstance⟩

/-- A Markov kernel is **Feller** if the map `a ↦ κ a` is continuous into `ProbabilityMeasure β`
(weak-* topology).

Equivalently: For every bounded continuous `f`, the map `a ↦ ∫ f d(κ a)` is continuous. -/
class IsFellerKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace α] [TopologicalSpace β] [OpensMeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] : Prop where
  /-- The kernel map into probability measures is continuous. -/
  continuous_toProbabilityMeasure : Continuous κ.toProbabilityMeasure

variable {α β : Type*}
  [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]

/-- Integrating a bounded continuous function against a Feller kernel yields a bounded continuous
function: If `κ` is Feller and `f : BoundedContinuousFunction β ℝ`, then `a ↦ ∫ x, f x ∂(κ a)` is
bounded continuous. -/
noncomputable def IsFellerKernel.boundedContinuousFunction_integral_kernel
    (κ : Kernel α β) [IsMarkovKernel κ] [IsFellerKernel κ]
    (f : BoundedContinuousFunction β ℝ) :
    BoundedContinuousFunction α ℝ where
  toFun a := ∫ x, f x ∂(κ a)
  continuous_toFun := by
    -- Compose: a ↦ ⟨κ a⟩ (continuous by Feller) with μ ↦ ∫ f dμ (continuous by Mathlib).
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
      IsFellerKernel.continuous_toProbabilityMeasure
  map_bounded' := by
    refine ⟨2 * ‖f‖, fun x y => ?_⟩
    calc dist (∫ z, f z ∂κ x) (∫ z, f z ∂κ y)
        ≤ ‖∫ z, f z ∂κ x‖ + ‖∫ z, f z ∂κ y‖ := dist_le_norm_add_norm ..
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_integral_le_norm (κ x))
                          (f.norm_integral_le_norm (κ y))
      _ = 2 * ‖f‖ := by ring

omit [OpensMeasurableSpace α] in
private theorem lintegral_lt_top_of_isMarkovKernel
    (κ : Kernel α α) [IsMarkovKernel κ]
    (f : BoundedContinuousFunction α NNReal) (a : α) :
    ∫⁻ x, ↑(f x) ∂(κ a) < ⊤ :=
  calc ∫⁻ x, ↑(f x) ∂(κ a)
      ≤ edist 0 f * (κ a) Set.univ := f.lintegral_le_edist_mul (κ a)
    _ = edist 0 f * 1 := by rw [measure_univ]
    _ = edist 0 f := mul_one _
    _ < ⊤ := edist_lt_top _ _

/-- The inner lintegral of a NNReal BCF against a Feller kernel is a NNReal BCF. -/
noncomputable def IsFellerKernel.lintegralBCF
    (κ : Kernel α α) [IsMarkovKernel κ] [IsFellerKernel κ]
    (f : BoundedContinuousFunction α NNReal) :
    BoundedContinuousFunction α NNReal where
  toFun a := (∫⁻ x, ↑(f x) ∂(κ a)).toNNReal
  continuous_toFun := by
    have hg := (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction f).comp
      (IsFellerKernel.continuous_toProbabilityMeasure (κ := κ))
    have hne : ∀ a, ∫⁻ x, ↑(f x) ∂(κ a) ≠ ⊤ :=
      fun a => ne_of_lt (lintegral_lt_top_of_isMarkovKernel κ f a)
    exact ENNReal.continuousOn_toNNReal.comp_continuous hg (fun a => hne a)
  map_bounded' := by
    -- Each value (∫⁻ f dκ(a)).toNNReal ≤ nndist f 0, so distance ≤ 2 * nndist f 0.
    refine ⟨2 * nndist f 0, fun x y => ?_⟩
    -- dist on NNReal is |a - b| as reals; bound by a + b ≤ 2C.
    simp only [NNReal.dist_eq]
    have hbound : ∀ a, (↑(∫⁻ z, ↑(f z) ∂κ a).toNNReal : ℝ) ≤ ↑(nndist f 0) := by
      intro a
      exact_mod_cast ENNReal.toNNReal_mono (ENNReal.coe_ne_top) (calc
        (∫⁻ z, ↑(f z) ∂κ a)
          ≤ edist 0 f * (κ a) Set.univ := f.lintegral_le_edist_mul (κ a)
        _ = edist 0 f := by rw [measure_univ, mul_one]
        _ = ↑(nndist f 0) := by rw [edist_nndist]; simp [nndist_comm])
    have h_nonneg : ∀ a, (0 : ℝ) ≤ (∫⁻ z, ↑(f z) ∂κ a).toNNReal :=
      fun a => NNReal.coe_nonneg _
    calc |↑(∫⁻ z, ↑(f z) ∂κ x).toNNReal - ↑(∫⁻ z, ↑(f z) ∂κ y).toNNReal|
        ≤ (nndist f 0 : ℝ) := by
          rw [abs_sub_le_iff]
          exact ⟨by linarith [hbound x, h_nonneg y],
                 by linarith [hbound y, h_nonneg x]⟩
      _ ≤ 2 * (nndist f 0 : ℝ) := by linarith [NNReal.coe_nonneg (nndist f 0)]

/-- The composition map `μ ↦ κ ∘ₘ μ` is continuous on `ProbabilityMeasure α` for a Feller kernel
`κ`. -/
theorem IsFellerKernel.continuous_compMeasure
    (κ : Kernel α α) [IsMarkovKernel κ] [IsFellerKernel κ] :
    Continuous (show ProbabilityMeasure α → ProbabilityMeasure α from
      fun μ => ⟨κ ∘ₘ μ.toMeasure, inferInstance⟩) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_lintegral]
  intro f
  simp only [ProbabilityMeasure.coe_mk]
  -- Rewrite ∫⁻ f d(κ ∘ₘ μ) = ∫⁻ (∫⁻ f dκ(a)) dμ via lintegral_bind
  have hκ_meas : ∀ μ : ProbabilityMeasure α,
      ∫⁻ ω, ↑(f ω) ∂(κ ∘ₘ μ.toMeasure) =
      ∫⁻ a, ∫⁻ ω, ↑(f ω) ∂(κ a) ∂μ.toMeasure := by
    intro μ
    exact Measure.lintegral_bind (Kernel.measurable κ).aemeasurable
      (measurable_coe_nnreal_ennreal.comp f.continuous.measurable).aemeasurable
  simp_rw [hκ_meas]
  -- The inner function g(a) = ∫⁻ f dκ(a) equals ↑(lintegralBCF κ f a)
  -- since lintegralBCF is defined as toNNReal of the lintegral.
  let g := IsFellerKernel.lintegralBCF κ f
  have hg_eq : ∀ μ : ProbabilityMeasure α,
      ∫⁻ a, ∫⁻ ω, ↑(f ω) ∂(κ a) ∂μ.toMeasure =
      ∫⁻ a, ↑(g a) ∂μ.toMeasure := by
    intro μ
    congr 1; ext a
    exact (ENNReal.coe_toNNReal
      (ne_of_lt (lintegral_lt_top_of_isMarkovKernel κ f a))).symm
  simp_rw [hg_eq]
  exact ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction g

end ProbabilityTheory

/-! ## Embedding into a locally convex TVS -/

section Embedding

open ProbabilityTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- The integration embedding: Sends a probability measure to the functional `f ↦ ∫ f dμ` on
bounded continuous functions. -/
noncomputable def ProbabilityMeasure.toIntegralFunctional
    (μ : ProbabilityMeasure α) : BoundedContinuousFunction α ℝ → ℝ :=
  fun f => ∫ x, f x ∂μ.toMeasure

/-- The integration embedding is continuous: The weak-* topology on `ProbabilityMeasure α` is the
initial topology induced by the functionals `μ ↦ ∫ f dμ`. -/
theorem ProbabilityMeasure.continuous_toIntegralFunctional :
    Continuous (ProbabilityMeasure.toIntegralFunctional (α := α)) := by
  -- The ProbabilityMeasure topology is the initial topology for these functionals.
  rw [continuous_pi_iff]
  intro f
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

omit [OpensMeasurableSpace α] in
/-- The integration embedding is injective: A probability measure is determined by the integrals of
all bounded continuous functions against it. -/
theorem ProbabilityMeasure.injective_toIntegralFunctional
    [T2Space α] [BorelSpace α] [HasOuterApproxClosed α] :
    Function.Injective (ProbabilityMeasure.toIntegralFunctional (α := α)) := by
  intro μ ν h
  exact ProbabilityMeasure.toMeasure_injective
    (ext_of_forall_integral_eq_of_IsFiniteMeasure (congr_fun h))

/-- On a compact Hausdorff space the integration embedding is a topological embedding of
`ProbabilityMeasure α` into the function space `BoundedContinuousFunction α ℝ → ℝ`. -/
theorem ProbabilityMeasure.isEmbedding_toIntegralFunctional
    [CompactSpace α] [T2Space α] [BorelSpace α] [HasOuterApproxClosed α] :
    Topology.IsEmbedding (ProbabilityMeasure.toIntegralFunctional (α := α)) := by
  -- Continuous injection from compact to Hausdorff is a closed embedding.
  exact (ProbabilityMeasure.continuous_toIntegralFunctional.isClosedEmbedding
    ProbabilityMeasure.injective_toIntegralFunctional).isEmbedding

/-- The image of `ProbabilityMeasure α` under the integration embedding is convex. -/
theorem ProbabilityMeasure.convex_range_toIntegralFunctional :
    Convex ℝ (Set.range (ProbabilityMeasure.toIntegralFunctional (α := α))) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  -- Build the convex combination measure: a • μ + b • ν
  have hprob : IsProbabilityMeasure
      (ENNReal.ofReal a • μ.toMeasure + ENNReal.ofReal b • ν.toMeasure) := by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab]; simp
  refine ⟨⟨_, hprob⟩, funext fun f => ?_⟩
  -- ∫ f d(aμ + bν) = a ∫ f dμ + b ∫ f dν
  simp only [toIntegralFunctional, ProbabilityMeasure.coe_mk, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  haveI : IsFiniteMeasure (ENNReal.ofReal a • μ.toMeasure) :=
    μ.toMeasure.smul_finite ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (ENNReal.ofReal b • ν.toMeasure) :=
    ν.toMeasure.smul_finite ENNReal.ofReal_ne_top
  rw [integral_add_measure (f.integrable _) (f.integrable _),
    integral_smul_measure, integral_smul_measure]
  simp [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

end Embedding

/-! ## Krylov–Bogolyubov theorem -/

namespace Econlib.Probability

open ProbabilityTheory Filter

/-- **Krylov–Bogolyubov theorem.** Every Feller kernel on a nonempty compact metrizable space has
at least one invariant probability measure. -/
theorem exists_invariant_probDist
    {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [TopologicalSpace.MetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    [Nonempty α]
    (κ : Kernel α α) [IsMarkovKernel κ] [IsFellerKernel κ] :
    ∃ μ : ProbDist α, Kernel.Invariant κ μ.toMeasure := by
  -- The ambient locally convex TVS
  let E := BoundedContinuousFunction α ℝ → ℝ
  let ι := ProbabilityMeasure.toIntegralFunctional (α := α)
  -- The kernel action as a self-map of ProbabilityMeasure
  let T : ProbabilityMeasure α → ProbabilityMeasure α :=
    fun μ => ⟨κ ∘ₘ μ.toMeasure, inferInstance⟩
  have hT_cont : Continuous T := IsFellerKernel.continuous_compMeasure κ
  -- Image K := ι '' ProbabilityMeasure α is compact convex nonempty in E.
  let K := Set.range ι
  have hK_compact : IsCompact K :=
    isCompact_range ProbabilityMeasure.continuous_toIntegralFunctional
  have hK_convex : Convex ℝ K := ProbabilityMeasure.convex_range_toIntegralFunctional
  haveI : Nonempty (ProbabilityMeasure α) :=
    let ⟨a⟩ := ‹Nonempty α›; ⟨⟨Measure.dirac a, inferInstance⟩⟩
  have hK_ne : K.Nonempty := Set.range_nonempty ι
  -- Build a continuous self-map of K by conjugating T through ι.
  have hι_emb := ProbabilityMeasure.isEmbedding_toIntegralFunctional (α := α)
  have hι_inj := ProbabilityMeasure.injective_toIntegralFunctional (α := α)
  -- ι is a homeomorphism onto K (continuous bijection from compact to Hausdorff)
  let ιK : ProbabilityMeasure α → K := fun μ => ⟨ι μ, μ, rfl⟩
  have hιK_cont : Continuous ιK :=
    ProbabilityMeasure.continuous_toIntegralFunctional.subtype_mk _
  have hιK_bij : Function.Bijective ιK := by
    constructor
    · intro μ₁ μ₂ h; exact hι_inj (congr_arg Subtype.val h)
    · rintro ⟨y, μ, rfl⟩; exact ⟨μ, rfl⟩
  -- ιK⁻¹ is continuous (continuous bijection from compact to Hausdorff has continuous inverse)
  haveI : CompactSpace (ProbabilityMeasure α) := inferInstance
  haveI : T2Space K := instT2SpaceSubtype
  let ιK_equiv : ProbabilityMeasure α ≃ K := Equiv.ofBijective ιK hιK_bij
  let ιK_homeo : ProbabilityMeasure α ≃ₜ K :=
    hιK_cont.homeoOfEquivCompactToT2 (f := ιK_equiv)
  -- Conjugate: g = ιK ∘ T ∘ ιK⁻¹
  let g : C(K, K) :=
    ⟨ιK_homeo ∘ T ∘ ιK_homeo.symm,
     ιK_homeo.continuous.comp (hT_cont.comp ιK_homeo.symm.continuous)⟩
  -- Apply Tychonoff
  obtain ⟨⟨y, hy⟩, hfp⟩ := tychonoffFixedPoint K hK_convex hK_compact hK_ne g
  -- Pull back: g(y) = y means T(ιK⁻¹(y)) = ιK⁻¹(y)
  let μ := ιK_homeo.symm ⟨y, hy⟩
  use ⟨μ.toMeasure, μ.prop⟩
  change κ ∘ₘ μ.toMeasure = μ.toMeasure
  have hfp' : T μ = μ := by
    apply hι_inj
    -- ι (T μ) = (ιK_homeo (T μ)).val and ι μ = (ιK_homeo μ).val
    change (ιK_homeo (T μ)).val = (ιK_homeo μ).val
    have h1 : ιK_homeo μ = ⟨y, hy⟩ := ιK_homeo.apply_symm_apply ⟨y, hy⟩
    have h2 : ιK_homeo (T μ) = ⟨y, hy⟩ := hfp
    rw [h1, h2]
  exact congr_arg ProbabilityMeasure.toMeasure hfp'

end Econlib.Probability
