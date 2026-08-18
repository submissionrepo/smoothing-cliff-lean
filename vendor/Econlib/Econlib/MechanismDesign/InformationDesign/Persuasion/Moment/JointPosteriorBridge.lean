/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Perturbation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.CompositionLipschitz
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.MartingaleExtension
public import Econlib.Probability.ProbDist.Borel
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.Kernel.Disintegration.Integral
public import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Joint–posterior bridge for moment persuasion

This file establishes the equivalence of the two formulations of the moment-persuasion primal
problem.

* **Joint formulation.**  `momentPrimal s v = sSup { ∫ v(x) dπ(x, ω) : π ∈ Π(μ₀) }`, the supremum
  over feasible joints `π : ProbDist (X × Ω)` whose `Ω`-marginal is the prior and which satisfies a
  martingale constraint.
* **Posterior formulation.**  `concaveClosure V μ₀ = sSup { ∫ V(μ) dτ(μ) : τ ∈ T(μ₀) }`, the
  supremum over Bayes-plausible distributions of posteriors `τ : ProbDist (ProbDist Ω)`, with the
  lifted objective `V(μ) := v(E_μ[m])`.

The two formulations are connected by `jointFromBayesian` (forward: `τ ↦ π` via
`τ.bind (μ ↦ δ_{E_μ[m]} ⊗ μ)`) and `bayesianFromJoint` (backward: `π ↦ τ` via disintegration of `π`
over its `X`-marginal). The backward direction uses `Measure.condKernel`; the compact metrizable T2
second-countable assumptions on `Ω` supply the required standard-Borel structure.

## Main definitions

* `jointFromBayesian` — forward bridge construction.
* `bayesianFromJoint` — backward bridge construction.

## Main statements

* `momentPrimal_eq_concaveClosure_composedValue` — equality of primal and concave-closure values.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Section 4.

## Tags

persuasion, moment persuasion, joint distribution, disintegration
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

variable {n : ℕ}

/-! ## 1. Forward direction: Bayes-plausible distribution → feasible joint -/

/-- The kernel `μ ↦ δ_{E_μ[m]} ⊗ μ` underlying `jointFromBayesian`. -/
noncomputable def jointFromBayesianKernel (s : MomentSetup Ω n) :
    ProbDist Ω → Measure (EuclideanSpace ℝ (Fin n) × Ω) :=
  fun μ => (Measure.dirac (s.posteriorMoment μ)).prod μ.toMeasure

/-- Measurability of the coordinate `μ ↦ (s.posteriorMoment μ).ofLp i`. -/
lemma MomentSetup.measurable_posteriorMoment_ofLp (s : MomentSetup Ω n) (i : Fin n) :
    Measurable (fun μ : ProbDist Ω => (s.posteriorMoment μ).ofLp i) := by
  have h_cont : Continuous (fun ω => (s.m ω).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp s.m_continuous)
  let g : BoundedContinuousFunction Ω ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun ω => (s.m ω).ofLp i, h_cont⟩
  have h_int_cont : Continuous (fun μ : ProbDist Ω => ∫ ω, g ω ∂(μ : Measure Ω)) :=
    MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
  have h_eq : (fun μ : ProbDist Ω => (s.posteriorMoment μ).ofLp i)
      = (fun μ : ProbDist Ω => ∫ ω, g ω ∂(μ : Measure Ω)) := by
    funext μ
    exact s.posteriorMoment_ofLp μ i
  rw [h_eq]
  exact h_int_cont.measurable

/-- Measurability of `μ ↦ s.posteriorMoment μ`. -/
lemma MomentSetup.measurable_posteriorMoment (s : MomentSetup Ω n) :
    Measurable (fun μ : ProbDist Ω => s.posteriorMoment μ) := by
  rw [show (fun μ : ProbDist Ω => s.posteriorMoment μ)
      = (MeasurableEquiv.toLp 2 (Fin n → ℝ)) ∘
        (fun μ : ProbDist Ω => fun i => (s.posteriorMoment μ).ofLp i) from rfl]
  refine (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp ?_
  exact measurable_pi_lambda _ (fun i => s.measurable_posteriorMoment_ofLp i)

/-- The dirac kernel `μ ↦ δ_{E_μ[m]}` is measurable from `ProbDist Ω` to
`ProbDist (EuclideanSpace ℝ (Fin n))`. -/
lemma MomentSetup.measurable_diracPosteriorMoment (s : MomentSetup Ω n) :
    Measurable (fun μ : ProbDist Ω =>
      (⟨Measure.dirac (s.posteriorMoment μ), Measure.dirac.isProbabilityMeasure⟩ :
        ProbDist (EuclideanSpace ℝ (Fin n)))) := by
  exact Measurable.subtype_mk (Measure.measurable_dirac.comp s.measurable_posteriorMoment)

/-- Measurability of the joint kernel `μ ↦ δ_{E_μ[m]} ⊗ μ`. -/
lemma MomentSetup.measurable_jointFromBayesianKernel (s : MomentSetup Ω n) :
    Measurable (jointFromBayesianKernel s) := by
  unfold jointFromBayesianKernel
  let pair : ProbDist Ω →
      ProbDist (EuclideanSpace ℝ (Fin n)) × ProbDist Ω :=
    fun μ => (⟨Measure.dirac (s.posteriorMoment μ), Measure.dirac.isProbabilityMeasure⟩, μ)
  have h_pair : Measurable pair :=
    (s.measurable_diracPosteriorMoment).prodMk measurable_id
  exact (MeasureTheory.ProbabilityMeasure.measurable_fun_prod
    (α := EuclideanSpace ℝ (Fin n)) (β := Ω)).comp h_pair

omit [T2Space Ω] [SecondCountableTopology Ω] in
/-- The posterior moment lies in the convex compact moment set. -/
lemma MomentSetup.posteriorMoment_mem_X (s : MomentSetup Ω n) (μ : ProbDist Ω) :
    s.posteriorMoment μ ∈ s.X := by
  unfold MomentSetup.posteriorMoment
  refine Convex.integral_mem s.X_convex s.X_compact.isClosed ?_ (s.m_integrable μ)
  exact ae_of_all _ s.m_mem_X

/-- Forward bridge construction.  Given a distribution of posteriors `τ`, the joint
`jointFromBayesian s τ` is defined by the kernel `μ ↦ δ_{E_μ[m]} ⊗ μ` mixed against `τ`:

`(jointFromBayesian s τ)(A × B) = ∫ [E_μ[m] ∈ A] · μ(B) dτ(μ)`.

This places the `X`-marginal at the moment vector and the `Ω`-marginal at the posterior itself,
then averages against `τ`. -/
noncomputable def jointFromBayesian (s : MomentSetup Ω n)
    (τ : ProbDist (ProbDist Ω)) :
    ProbDist (EuclideanSpace ℝ (Fin n) × Ω) :=
  ⟨τ.toMeasure.bind (jointFromBayesianKernel s),
    isProbabilityMeasure_bind
      (s.measurable_jointFromBayesianKernel).aemeasurable
      (Filter.Eventually.of_forall (fun μ => by
        unfold jointFromBayesianKernel
        infer_instance))⟩

/-- The `Ω`-marginal of `jointFromBayesian s τ` recovers the prior when `τ` is Bayes-plausible. -/
lemma snd_marginal_jointFromBayesian (s : MomentSetup Ω n)
    {τ : ProbDist (ProbDist Ω)} (hτ : IsBayesPlausible s.prior τ) :
    ProbDist.map (jointFromBayesian s τ) Prod.snd measurable_snd = s.prior := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Prod.snd (τ.toMeasure.bind (jointFromBayesianKernel s)) = s.prior.toMeasure
  rw [show Measure.map Prod.snd (τ.toMeasure.bind (jointFromBayesianKernel s))
      = τ.toMeasure.bind (fun μ : ProbDist Ω => μ.toMeasure) from ?_]
  · exact IsBayesPlausible.bind_eval_eq hτ
  · ext t ht
    rw [Measure.map_apply measurable_snd ht]
    rw [Measure.bind_apply (ht.preimage measurable_snd)
      (s.measurable_jointFromBayesianKernel.aemeasurable)]
    rw [show ((τ.toMeasure.bind fun μ : ProbDist Ω => μ.toMeasure) t)
        = ∫⁻ μ, μ.toMeasure t ∂τ.toMeasure from
      Measure.bind_apply ht measurable_subtype_coe.aemeasurable]
    congr 1
    funext μ
    unfold jointFromBayesianKernel
    rw [← Set.univ_prod]
    rw [Measure.prod_prod]
    simp

/-- The `X`-marginal of `jointFromBayesian s τ` is supported in `s.X`. -/
lemma jointFromBayesian_fst_supportsOn (s : MomentSetup Ω n)
    (τ : ProbDist (ProbDist Ω)) :
    (jointFromBayesian s τ).toMeasure (Prod.fst ⁻¹' s.X) = 1 := by
  have hX_meas : MeasurableSet s.X := s.X_compact.isClosed.measurableSet
  have hpre_meas :
      MeasurableSet
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    hX_meas.preimage (measurable_fst :
      Measurable (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)))
  change (τ.toMeasure.bind (jointFromBayesianKernel s))
    ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) = 1
  rw [Measure.bind_apply hpre_meas (s.measurable_jointFromBayesianKernel.aemeasurable)]
  have hkernel :
      ∀ μ : ProbDist Ω, (jointFromBayesianKernel s μ)
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) = 1 := by
    intro μ
    unfold jointFromBayesianKernel
    rw [← Set.prod_univ]
    rw [Measure.prod_prod]
    simp [Measure.dirac_apply_of_mem (s.posteriorMoment_mem_X μ)]
  simp [hkernel]

/-- `jointFromBayesian s τ` is the pushforward of the compProd measure `τ ⊗ kernelEval` along the
posterior-moment map `q ↦ (E_{q.1}[m], q.2)`. Both objective/martingale integral computations
factor through this identity. -/
lemma jointFromBayesian_eq_map_compProd (s : MomentSetup Ω n)
    (τ : ProbDist (ProbDist Ω)) :
    (jointFromBayesian s τ).toMeasure
      = Measure.map (fun q : ProbDist Ω × Ω => (s.posteriorMoment q.1, q.2))
          (τ.toMeasure.compProd (kernelEval Ω)) := by
  set T : ProbDist Ω × Ω → EuclideanSpace ℝ (Fin n) × Ω :=
    fun q => (s.posteriorMoment q.1, q.2)
  have hT_meas : Measurable T :=
    (s.measurable_posteriorMoment.comp measurable_fst).prodMk measurable_snd
  ext A hA
  change (τ.toMeasure.bind (jointFromBayesianKernel s)) A
    = (Measure.map T (τ.toMeasure.compProd (kernelEval Ω))) A
  rw [Measure.bind_apply hA (s.measurable_jointFromBayesianKernel.aemeasurable)]
  rw [Measure.map_apply hT_meas hA]
  rw [Measure.compProd_apply (hA.preimage hT_meas)]
  congr 1
  funext μ
  unfold jointFromBayesianKernel T
  rw [Measure.dirac_prod]
  rw [Measure.map_apply measurable_prodMk_left hA]
  rfl

/-- The martingale test integral on `jointFromBayesian s τ` vanishes: For any bounded continuous
`φ : ℝⁿ → ℝ` and coordinate `i`, `∫ φ(p.1) · (m(p.2)_i − p.1_i) d(jointFromBayesian s τ) = 0`. -/
lemma jointFromBayesian_martingale (s : MomentSetup Ω n)
    (τ : ProbDist (ProbDist Ω))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ_cont : Continuous φ) (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) (i : Fin n) :
    ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂(jointFromBayesian s τ).toMeasure = 0 := by
  let T : ProbDist Ω × Ω → EuclideanSpace ℝ (Fin n) × Ω :=
    fun q => (s.posteriorMoment q.1, q.2)
  let F : EuclideanSpace ℝ (Fin n) × Ω → ℝ :=
    fun p => φ p.1 * ((s.m p.2).ofLp i - p.1.ofLp i)
  let G : ProbDist Ω × Ω → ℝ := fun q => F (T q)
  have hT_meas : Measurable T :=
    (s.measurable_posteriorMoment.comp measurable_fst).prodMk measurable_snd
  have hF_meas : Measurable F := by
    dsimp [F]
    have hm_coord :
        Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => (s.m p.2).ofLp i) := by
      exact ((continuous_apply i).comp
        ((PiLp.continuous_ofLp 2 _).comp (s.m_continuous.comp continuous_snd))).measurable
    have hx_coord :
        Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1.ofLp i) := by
      exact ((continuous_apply i).comp
        ((PiLp.continuous_ofLp 2 _).comp continuous_fst)).measurable
    exact (hφ_cont.measurable.comp measurable_fst).mul (hm_coord.sub hx_coord)
  have hG_meas : Measurable G := hF_meas.comp hT_meas
  have hjoint_map :
      (jointFromBayesian s τ).toMeasure
        = Measure.map T (τ.toMeasure.compProd (kernelEval Ω)) :=
    jointFromBayesian_eq_map_compProd s τ
  obtain ⟨M, hM⟩ := hφ_bdd
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have hcoord_bound :
      ∀ x ∈ s.X, |x.ofLp i| ≤ |R| := by
    intro x hx
    have hcoord_norm : ‖x.ofLp i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    have hx_norm : ‖x‖ ≤ R := hR x hx
    have : ‖x.ofLp i‖ ≤ |R| := hcoord_norm.trans (hx_norm.trans (le_abs_self R))
    simpa [Real.norm_eq_abs] using this
  have hG_bound : ∀ q : ProbDist Ω × Ω, ‖G q‖ ≤ |M| * (2 * |R|) := by
    intro q
    have hφM : |φ (s.posteriorMoment q.1)| ≤ |M| :=
      (hM _).trans (le_abs_self M)
    have hmR : |(s.m q.2).ofLp i| ≤ |R| :=
      hcoord_bound (s.m q.2) (s.m_mem_X q.2)
    have hpR : |(s.posteriorMoment q.1).ofLp i| ≤ |R| :=
      hcoord_bound (s.posteriorMoment q.1) (s.posteriorMoment_mem_X q.1)
    have hdiff :
        |(s.m q.2).ofLp i - (s.posteriorMoment q.1).ofLp i| ≤ 2 * |R| := by
      have htri :
          |(s.m q.2).ofLp i - (s.posteriorMoment q.1).ofLp i|
            ≤ |(s.m q.2).ofLp i| + |(s.posteriorMoment q.1).ofLp i| := by
        simpa [sub_eq_add_neg] using
          abs_add_le ((s.m q.2).ofLp i) (-(s.posteriorMoment q.1).ofLp i)
      calc
        |(s.m q.2).ofLp i - (s.posteriorMoment q.1).ofLp i|
            ≤ |(s.m q.2).ofLp i| + |(s.posteriorMoment q.1).ofLp i| := htri
        _ ≤ |R| + |R| := add_le_add hmR hpR
        _ = 2 * |R| := by ring
    dsimp [G, F, T]
    calc
      |φ (s.posteriorMoment q.1) *
          ((s.m q.2).ofLp i - (s.posteriorMoment q.1).ofLp i)|
          = |φ (s.posteriorMoment q.1)| *
              |(s.m q.2).ofLp i - (s.posteriorMoment q.1).ofLp i| := abs_mul _ _
      _ ≤ |M| * (2 * |R|) :=
          mul_le_mul hφM hdiff (abs_nonneg _) (abs_nonneg _)
  have hG_int : Integrable G (τ.toMeasure.compProd (kernelEval Ω)) := by
    haveI : IsFiniteMeasure (τ.toMeasure.compProd (kernelEval Ω)) := inferInstance
    exact Integrable.of_bound hG_meas.aestronglyMeasurable (|M| * (2 * |R|))
      (Filter.Eventually.of_forall hG_bound)
  have hinner :
      ∀ μ : ProbDist Ω, ∫ ω, G (μ, ω) ∂μ.toMeasure = 0 := by
    intro μ
    dsimp [G, F, T]
    rw [MeasureTheory.integral_const_mul]
    have hcoord_int : Integrable (fun ω => (s.m ω).ofLp i) μ.toMeasure :=
      s.coord_integrable μ i
    have hconst_int :
        Integrable (fun _ : Ω => (s.posteriorMoment μ).ofLp i) μ.toMeasure :=
      integrable_const _
    rw [MeasureTheory.integral_sub hcoord_int hconst_int]
    have hcoord_eq :
        ∫ ω, (s.m ω).ofLp i ∂μ.toMeasure = (s.posteriorMoment μ).ofLp i := by
      simpa [ProbDist.expect] using (s.posteriorMoment_ofLp μ i).symm
    rw [hcoord_eq]
    simp
  rw [hjoint_map]
  rw [MeasureTheory.integral_map hT_meas.aemeasurable hF_meas.aestronglyMeasurable]
  rw [Measure.integral_compProd hG_int]
  apply integral_eq_zero_of_ae
  filter_upwards with μ
  simpa [kernelEval_apply] using hinner μ

/-- **Forward bridge.**  A Bayes-plausible distribution of posteriors yields a feasible joint. -/
lemma isFeasibleJoint_jointFromBayesian (s : MomentSetup Ω n)
    {τ : ProbDist (ProbDist Ω)} (hτ : IsBayesPlausible s.prior τ) :
    IsFeasibleJoint s (jointFromBayesian s τ) where
  marginal := snd_marginal_jointFromBayesian s hτ
  fst_supportsOn := jointFromBayesian_fst_supportsOn s τ
  martingale := jointFromBayesian_martingale s τ

/-- The objective on `jointFromBayesian s τ` equals the posterior-formulation objective on `τ`:
`∫ v(p.1) d(jointFromBayesian s τ) = primalValue (composedValue v) τ`. -/
lemma integral_v_fst_jointFromBayesian (s : MomentSetup Ω n)
    (τ : ProbDist (ProbDist Ω))
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_meas : Measurable v)
    (hv_bdd : ∃ M, ∀ x, |v x| ≤ M) :
    ∫ p, v p.1 ∂(jointFromBayesian s τ).toMeasure
      = primalValue (s.composedValue v) τ := by
  let T : ProbDist Ω × Ω → EuclideanSpace ℝ (Fin n) × Ω :=
    fun q => (s.posteriorMoment q.1, q.2)
  let F : EuclideanSpace ℝ (Fin n) × Ω → ℝ := fun p => v p.1
  let G : ProbDist Ω × Ω → ℝ := fun q => F (T q)
  have hT_meas : Measurable T :=
    (s.measurable_posteriorMoment.comp measurable_fst).prodMk measurable_snd
  have hF_meas : Measurable F := hv_meas.comp measurable_fst
  have hG_meas : Measurable G := hF_meas.comp hT_meas
  have hjoint_map :
      (jointFromBayesian s τ).toMeasure
        = Measure.map T (τ.toMeasure.compProd (kernelEval Ω)) :=
    jointFromBayesian_eq_map_compProd s τ
  obtain ⟨M, hM⟩ := hv_bdd
  have hG_bound : ∀ q : ProbDist Ω × Ω, ‖G q‖ ≤ |M| := by
    intro q
    dsimp [G, F, T]
    exact (hM _).trans (le_abs_self M)
  have hG_int : Integrable G (τ.toMeasure.compProd (kernelEval Ω)) := by
    haveI : IsFiniteMeasure (τ.toMeasure.compProd (kernelEval Ω)) := inferInstance
    exact Integrable.of_bound hG_meas.aestronglyMeasurable |M|
      (Filter.Eventually.of_forall hG_bound)
  rw [hjoint_map]
  rw [MeasureTheory.integral_map hT_meas.aemeasurable hF_meas.aestronglyMeasurable]
  rw [Measure.integral_compProd hG_int]
  unfold primalValue MomentSetup.composedValue
  apply integral_congr_ae
  filter_upwards with μ
  simp [G, F, T, kernelEval_apply]

/-! ## 2. Backward direction: Feasible joint → Bayes-plausible distribution -/

variable [Inhabited Ω]

/-- Backward bridge construction.  Given a feasible joint `pi`, disintegrate over the `X`-marginal
via `Measure.condKernel` to obtain a kernel `x ↦ μ_x : ProbDist Ω`, then return the pushforward of
`pi_X` along this map. The standard-Borel structure on `Ω` is derived from the compact metrizable
T2 second-countable assumptions. -/
-- `s` is unused in the body: the construction only disintegrates `pi`, independent of the moment
-- setup. It is kept as an explicit argument to mirror `jointFromBayesian s τ` (the forward
-- direction) and so call sites like `bayesianFromJoint s pi` read against the same `s` used in
-- `isBayesPlausible_bayesianFromJoint s hpi` right below.
noncomputable def bayesianFromJoint (_s : MomentSetup Ω n)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :
    ProbDist (ProbDist Ω) :=
  letI : MetricSpace Ω := MetricSpace.ofT0PseudoMetricSpace Ω
  letI : CompleteSpace Ω := complete_of_compact
  letI : PolishSpace Ω := inferInstance
  letI : StandardBorelSpace Ω := standardBorel_of_polish
  let κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n)) Ω := pi.toMeasure.condKernel
  let posterior : EuclideanSpace ℝ (Fin n) → ProbDist Ω :=
    fun x => ⟨κ x, inferInstance⟩
  have h_meas : Measurable posterior := Measurable.subtype_mk κ.measurable
  ProbDist.map ⟨pi.toMeasure.fst, inferInstance⟩ posterior h_meas

/-- **Backward bridge.**  A feasible joint yields a Bayes-plausible distribution of posteriors. -/
lemma isBayesPlausible_bayesianFromJoint (s : MomentSetup Ω n)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)} (hpi : IsFeasibleJoint s pi) :
    IsBayesPlausible s.prior (bayesianFromJoint s pi) := by
  letI : MetricSpace Ω := MetricSpace.ofT0PseudoMetricSpace Ω
  letI : CompleteSpace Ω := complete_of_compact
  letI : PolishSpace Ω := inferInstance
  letI : StandardBorelSpace Ω := standardBorel_of_polish
  intro f
  set κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n)) Ω :=
    pi.toMeasure.condKernel with hκ
  set posterior : EuclideanSpace ℝ (Fin n) → ProbDist Ω :=
    fun x => ⟨κ x, inferInstance⟩
  have h_meas : Measurable posterior := Measurable.subtype_mk κ.measurable
  have h_bayes :
      (bayesianFromJoint s pi : ProbDist (ProbDist Ω)) =
        ProbDist.map ⟨pi.toMeasure.fst, inferInstance⟩ posterior h_meas := rfl
  have hf_meas : Measurable (f : Ω → ℝ) := f.continuous.measurable
  have hf_int : Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => f p.2) pi.toMeasure :=
    BoundedContinuousFunction.integrable pi.toMeasure
      (f.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have h_disint :
      ∫ p, (f p.2 : ℝ) ∂pi.toMeasure
        = ∫ x, (∫ ω, (f ω : ℝ) ∂κ x) ∂pi.toMeasure.fst := by
    rw [hκ]
    exact (MeasureTheory.Measure.integral_condKernel hf_int).symm
  have h_snd_int : ∫ p, (f p.2 : ℝ) ∂pi.toMeasure
      = ∫ ω, (f ω : ℝ) ∂pi.toMeasure.snd := by
    rw [Measure.snd, integral_map measurable_snd.aemeasurable
      hf_meas.aestronglyMeasurable]
  have h_marg : pi.toMeasure.snd = s.prior.toMeasure := by
    have := hpi.marginal
    have h := congrArg (fun d : ProbDist Ω => (d : Measure Ω)) this
    simp only [ProbDist.map_toMeasure] at h
    rw [Measure.snd]
    exact h
  have h_expect_meas : Measurable (fun μ : ProbDist Ω => μ.expect f) :=
    (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).measurable
  calc ∫ μ, μ.expect ⇑f ∂(bayesianFromJoint s pi).toMeasure
      = ∫ x, ((posterior x).expect ⇑f) ∂pi.toMeasure.fst := by
        rw [h_bayes]
        rw [show ((ProbDist.map (⟨pi.toMeasure.fst, inferInstance⟩ : ProbDist _)
              posterior h_meas).toMeasure)
            = Measure.map posterior pi.toMeasure.fst from rfl]
        exact integral_map h_meas.aemeasurable h_expect_meas.aestronglyMeasurable
    _ = ∫ x, (∫ ω, (f ω : ℝ) ∂κ x) ∂pi.toMeasure.fst := rfl
    _ = ∫ p, (f p.2 : ℝ) ∂pi.toMeasure := h_disint.symm
    _ = ∫ ω, (f ω : ℝ) ∂pi.toMeasure.snd := h_snd_int
    _ = ∫ ω, (f ω : ℝ) ∂s.prior.toMeasure := by rw [h_marg]
    _ = s.prior.expect ⇑f := rfl

/-- The objective on `bayesianFromJoint s π` equals the joint-formulation objective on `π`:
`primalValue (s.composedValue v) (bayesianFromJoint s π) = ∫ v(p.1) dπ`. -/
lemma integral_composedValue_bayesianFromJoint (s : MomentSetup Ω n)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)} (hpi : IsFeasibleJoint s pi)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_meas : Measurable v)
    (hv_bdd : ∃ M, ∀ x, |v x| ≤ M) :
    primalValue (s.composedValue v) (bayesianFromJoint s pi)
      = ∫ p, v p.1 ∂pi.toMeasure := by
  obtain ⟨_Mv, _hMv⟩ := hv_bdd
  letI : MetricSpace Ω := MetricSpace.ofT0PseudoMetricSpace Ω
  letI : CompleteSpace Ω := complete_of_compact
  letI : PolishSpace Ω := inferInstance
  letI : StandardBorelSpace Ω := standardBorel_of_polish
  set κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n)) Ω :=
    pi.toMeasure.condKernel with hκ
  set posterior : EuclideanSpace ℝ (Fin n) → ProbDist Ω :=
    fun x => ⟨κ x, inferInstance⟩
  have h_meas : Measurable posterior := Measurable.subtype_mk κ.measurable
  have h_bayes :
      (bayesianFromJoint s pi : ProbDist (ProbDist Ω)) =
        ProbDist.map ⟨pi.toMeasure.fst, inferInstance⟩ posterior h_meas := rfl
  have h_post_eq : ∀ᵐ x ∂pi.toMeasure.fst, s.posteriorMoment (posterior x) = x := by
    obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
    have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
      s.X_compact.isClosed.measurableSet
    have h_fst_meas : MeasurableSet
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
      h_X_meas.preimage measurable_fst
    have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
      rw [MeasureTheory.ae_iff]
      have h_set_eq :
          {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
            = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
                ⁻¹' s.X)ᶜ := rfl
      rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_fst_meas]
      exact hpi.fst_supportsOn
    have h_ae_x : ∀ᵐ x ∂pi.toMeasure.fst, x ∈ s.X := by
      rw [Measure.fst]
      exact (ae_map_iff measurable_fst.aemeasurable h_X_meas).mpr h_ae_p1
    have h_coord_zero : ∀ i : Fin n,
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (∫ ω, (s.m ω).ofLp i ∂κ x) - x.ofLp i)
          =ᵐ[pi.toMeasure.fst] 0 := by
      intro i
      have h_proj : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
        (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
      have h_m_meas : Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => (s.m p.2).ofLp i) :=
        (h_proj.measurable.comp s.m_continuous.measurable).comp measurable_snd
      have h_x_meas : Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1.ofLp i) :=
        h_proj.measurable.comp measurable_fst
      have h_x_fst_meas : Measurable
          (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
        h_proj.measurable
      have h_m_int : Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => (s.m p.2).ofLp i) pi.toMeasure := by
        refine Integrable.of_bound h_m_meas.aestronglyMeasurable R ?_
        refine Filter.Eventually.of_forall (fun p => ?_)
        have h_m_i : ‖(s.m p.2).ofLp i‖ ≤ R :=
          (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
        simpa using h_m_i
      have h_x_int : Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1.ofLp i) pi.toMeasure := by
        refine Integrable.of_bound h_x_meas.aestronglyMeasurable R ?_
        filter_upwards [h_ae_p1] with p hp
        have h_p_i : ‖p.1.ofLp i‖ ≤ R :=
          (PiLp.norm_apply_le p.1 i).trans (hR _ hp)
        simpa using h_p_i
      have h_x_fst_int : Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) pi.toMeasure.fst := by
        refine Integrable.of_bound h_x_fst_meas.aestronglyMeasurable R ?_
        filter_upwards [h_ae_x] with x hx
        have h_x_i : ‖x.ofLp i‖ ≤ R :=
          (PiLp.norm_apply_le x i).trans (hR _ hx)
        simpa using h_x_i
      have h_inner_int : Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ∫ ω, (s.m ω).ofLp i ∂κ x) pi.toMeasure.fst := by
        rw [hκ]
        simpa using h_m_int.integral_condKernel
      set Φ : EuclideanSpace ℝ (Fin n) → ℝ :=
        fun x => (∫ ω, (s.m ω).ofLp i ∂κ x) - x.ofLp i with hΦ_def
      have hΦ_int : Integrable Φ pi.toMeasure.fst := by
        simpa [hΦ_def] using h_inner_int.sub h_x_fst_int
      refine hΦ_int.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ => ?_
      have h_first :
          ∫ x in A, (∫ ω, (s.m ω).ofLp i ∂κ x) ∂pi.toMeasure.fst
            = ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2).ofLp i ∂pi.toMeasure := by
        rw [hκ]
        exact MeasureTheory.Measure.setIntegral_condKernel_univ_right (ρ := pi.toMeasure)
          hA h_m_int.integrableOn
      have h_second :
          ∫ x in A, x.ofLp i ∂pi.toMeasure.fst
            = ∫ p in A ×ˢ (Set.univ : Set Ω), p.1.ofLp i ∂pi.toMeasure := by
        rw [Measure.fst,
          MeasureTheory.setIntegral_map (f := fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i)
            hA h_proj.stronglyMeasurable.aestronglyMeasurable measurable_fst.aemeasurable,
          ← Set.prod_univ (β := Ω)]
      have h_mart_set := hpi.setIntegral_m_eq_setIntegral_fst_ofLp hA i
      have h_sub_out :
          ∫ x in A, Φ x ∂pi.toMeasure.fst
            = (∫ x in A, (∫ ω, (s.m ω).ofLp i ∂κ x) ∂pi.toMeasure.fst)
              - (∫ x in A, x.ofLp i ∂pi.toMeasure.fst) := by
        simp only [hΦ_def]
        exact MeasureTheory.integral_sub h_inner_int.integrableOn h_x_fst_int.integrableOn
      rw [h_sub_out, h_first, h_second, h_mart_set, sub_self]
    filter_upwards [Filter.eventually_all.mpr (fun i : Fin n => h_coord_zero i)] with x hx
    ext i
    have hcoord : (s.posteriorMoment (posterior x)).ofLp i
        = ∫ ω, (s.m ω).ofLp i ∂κ x := by
      rw [s.posteriorMoment_ofLp (posterior x) i]
      simp [ProbDist.expect, posterior]
    have hzero := hx i
    simp only [Pi.zero_apply] at hzero
    linarith
  have hV_meas : Measurable (s.composedValue v) := by
    unfold MomentSetup.composedValue
    exact hv_meas.comp s.measurable_posteriorMoment
  have h_left :
      primalValue (s.composedValue v) (bayesianFromJoint s pi)
        = ∫ x, s.composedValue v (posterior x) ∂pi.toMeasure.fst := by
    unfold primalValue
    rw [h_bayes]
    rw [show ((ProbDist.map (⟨pi.toMeasure.fst, inferInstance⟩ : ProbDist _)
          posterior h_meas).toMeasure : Measure (ProbDist Ω))
        = Measure.map posterior pi.toMeasure.fst from rfl]
    exact MeasureTheory.integral_map h_meas.aemeasurable hV_meas.aestronglyMeasurable
  have h_comp_ae :
      (fun x => s.composedValue v (posterior x))
        =ᵐ[pi.toMeasure.fst] fun x => v x := by
    filter_upwards [h_post_eq] with x hx
    unfold MomentSetup.composedValue
    rw [hx]
  have h_mid :
      ∫ x, s.composedValue v (posterior x) ∂pi.toMeasure.fst
        = ∫ x, v x ∂pi.toMeasure.fst :=
    MeasureTheory.integral_congr_ae h_comp_ae
  have h_right :
      ∫ x, v x ∂pi.toMeasure.fst
        = ∫ p, v p.1 ∂pi.toMeasure := by
    rw [Measure.fst]
    exact MeasureTheory.integral_map measurable_fst.aemeasurable hv_meas.aestronglyMeasurable
  rw [h_left, h_mid, h_right]

/-! ## 3. Bridge equality -/

/-- **Joint–posterior bridge.**  The moment-primal value equals the concave-closure of the lifted
objective `V(μ) := v(E_μ[m])` at the prior `μ₀`:
`momentPrimal s v = concaveClosure (s.composedValue v) s.prior`. -/
theorem momentPrimal_eq_concaveClosure_composedValue
    -- `hm_lip` and `hv_usc` are not used by this proof (compactness of `s.X` and Lipschitz `v`
    -- already give the integrability/measurability needed), but are kept as hypotheses since they
    -- are the standing regularity conditions of the moment-persuasion bridge this theorem states.
    (s : MomentSetup Ω n) (_hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    (_hv_usc : UpperSemicontinuous v) :
    momentPrimal s v = concaveClosure (s.composedValue v) s.prior := by
  have hv_meas : Measurable v := hv.continuous.measurable
  have h_set_eq :
      {y : ℝ | ∃ pi ∈ feasibleJoint s, y = ∫ p, v p.1 ∂pi.toMeasure}
        = {y : ℝ | ∃ τ ∈ feasiblePrimal s.prior,
            y = primalValue (s.composedValue v) τ} := by
    ext y
    constructor
    · rintro ⟨pi, hpi, rfl⟩
      refine ⟨bayesianFromJoint s pi,
        isBayesPlausible_bayesianFromJoint s hpi, ?_⟩
      exact (integral_composedValue_bayesianFromJoint s hpi hv_meas hv_bdd).symm
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨jointFromBayesian s τ,
        isFeasibleJoint_jointFromBayesian s hτ, ?_⟩
      exact (integral_v_fst_jointFromBayesian s τ hv_meas hv_bdd).symm
  exact congrArg sSup h_set_eq

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
