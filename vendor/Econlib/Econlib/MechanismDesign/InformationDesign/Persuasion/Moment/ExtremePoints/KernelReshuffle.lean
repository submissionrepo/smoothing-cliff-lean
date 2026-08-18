/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre
public import Econlib.Probability.ProbDist.Borel

/-!
# Kernel reshuffling at extreme contact fibers

Replacing the disintegration kernel of a feasible joint with a measurable kernel that satisfies
Bayes plausibility and the mean constraint preserves feasibility and the first marginal, and forces
the state image into the extreme points of the contact fiber almost everywhere. When the original
joint is primal-optimal, the replacement is too.

## Main statements

* `feasible_of_kernel_replacement`: A kernel replacement yields a feasible joint whose first
  marginal agrees with the original and whose `m`-image lies in the extreme points of
  `Gamma_x s v S` almost everywhere.
* `value_preserving_kernel_replacement`: The kernel replacement preserves primal optimality.

## Tags

persuasion, moment persuasion, extreme points, kernel reshuffle
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}
variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

/-! ## Reshuffle infrastructure -/

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- Given a feasible joint `pi`, an active set `S`, and a measurable kernel `κ' : ℝⁿ → ProbDist Ω`
satisfying Bayes plausibility and the mean constraint, the Bayesian joint built from the reshuffled
posteriors `κ' ∘ pi_X` is feasible, has the same first marginal as `pi`, and satisfies
`m(p.2) ∈ extremePoints (Gamma_x s v S p.1)` for almost every `p`. -/
lemma feasible_of_kernel_replacement (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (_hpi : pi ∈ feasibleJoint s)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (κ' : EuclideanSpace ℝ (Fin n) → ProbDist Ω)
    (hκ'_meas : Measurable (fun x => (κ' x).toMeasure))
    (hκ'_mean :
      ∀ᵐ x ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∫ ω, s.m ω ∂(κ' x).toMeasure = x)
    (hκ'_bayes :
      ProbDist.bind (ProbDist.map pi Prod.fst measurable_fst) κ' hκ'_meas
        = s.prior)
    (hκ'_supp :
      ∀ᵐ x ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        (κ' x).toMeasure (s.m ⁻¹' Set.extremePoints ℝ (Gamma_x s v S x)) = 1)
    (hG_meas : MeasurableSet
      {p : EuclideanSpace ℝ (Fin n) × Ω |
        s.m p.2 ∈ Set.extremePoints ℝ (Gamma_x s v S p.1)}) :
    ∃ pi' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
      pi' ∈ feasibleJoint s ∧
      ProbDist.map pi' Prod.fst measurable_fst
        = ProbDist.map pi Prod.fst measurable_fst ∧
      ∀ᵐ p ∂pi'.toMeasure,
        s.m p.2 ∈ Set.extremePoints ℝ (Gamma_x s v S p.1) := by
  set pi_X : ProbDist (EuclideanSpace ℝ (Fin n)) :=
    ProbDist.map pi Prod.fst measurable_fst with hpi_X_def
  have hκ'_subtype_meas : Measurable κ' := Measurable.subtype_mk hκ'_meas
  set τ' : ProbDist (ProbDist Ω) :=
    ProbDist.map pi_X κ' hκ'_subtype_meas with hτ'_def
  have hτ'_bayes : IsBayesPlausible s.prior τ' := by
    intro f
    have h_expect_meas : Measurable (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
      have h_cont : Continuous
          (fun μ : ProbabilityMeasure Ω => ∫ x, f x ∂(μ : Measure Ω)) :=
        MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
      exact h_cont.measurable
    have h_expect_aesm : AEStronglyMeasurable
        (fun μ : ProbDist Ω => ProbDist.expect μ f) τ'.toMeasure :=
      h_expect_meas.aestronglyMeasurable
    have h_step1 : ∫ μ, ProbDist.expect μ f ∂τ'.toMeasure
        = ∫ x, ProbDist.expect (κ' x) f ∂pi_X.toMeasure := by
      have h := MeasureTheory.integral_map (μ := pi_X.toMeasure)
        (φ := κ') (f := fun μ : ProbDist Ω => ProbDist.expect μ f)
        hκ'_subtype_meas.aemeasurable h_expect_aesm
      simpa [hτ'_def, ProbDist.map_toMeasure] using h
    have h_bind_meas : pi_X.toMeasure.bind (fun x => (κ' x).toMeasure)
        = s.prior.toMeasure := by
      have h := congrArg (fun d : ProbDist Ω => d.toMeasure) hκ'_bayes
      simpa [ProbDist.bind_toMeasure] using h
    let kKer : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n)) Ω :=
      { toFun := fun x => (κ' x).toMeasure
        measurable' := hκ'_meas }
    haveI : ProbabilityTheory.IsMarkovKernel kKer := ⟨fun x => (κ' x).prop⟩
    have hkKer_apply : ∀ x, kKer x = (κ' x).toMeasure := fun _ => rfl
    have h_compProd_snd : (pi_X.toMeasure.compProd kKer).snd
        = pi_X.toMeasure.bind (fun x => (κ' x).toMeasure) :=
      Measure.snd_compProd pi_X.toMeasure kKer
    haveI hcompProd_prob : IsProbabilityMeasure (pi_X.toMeasure.compProd kKer) :=
      inferInstance
    let fcompBCF : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n) × Ω) ℝ :=
      f.compContinuous ⟨Prod.snd, continuous_snd⟩
    have hf_int_compProd : Integrable
        (fun z : EuclideanSpace ℝ (Fin n) × Ω => (f z.2 : ℝ))
        (pi_X.toMeasure.compProd kKer) :=
      fcompBCF.integrable (pi_X.toMeasure.compProd kKer)
    have h_inner :
        ∫ x, ProbDist.expect (κ' x) f ∂pi_X.toMeasure
          = ∫ ω, (f ω : ℝ) ∂s.prior.toMeasure := by
      have h_inner_eq : ∫ x, ProbDist.expect (κ' x) f ∂pi_X.toMeasure
          = ∫ x, ∫ ω, f ω ∂kKer x ∂pi_X.toMeasure := by
        apply integral_congr_ae
        filter_upwards with x
        simp [ProbDist.expect, hkKer_apply]
      rw [h_inner_eq]
      rw [← Measure.integral_compProd hf_int_compProd]
      rw [show (∫ z, (f z.2 : ℝ) ∂(pi_X.toMeasure.compProd kKer))
          = ∫ ω, (f ω : ℝ) ∂(pi_X.toMeasure.compProd kKer).snd from
        (MeasureTheory.integral_map measurable_snd.aemeasurable
          f.continuous.aestronglyMeasurable).symm]
      rw [h_compProd_snd, h_bind_meas]
    rw [h_step1, h_inner]
    rfl
  set pi' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) := jointFromBayesian s τ' with hpi'_def
  have hpi'_feas : pi' ∈ feasibleJoint s :=
    isFeasibleJoint_jointFromBayesian s hτ'_bayes
  have h_pi'_meas : pi'.toMeasure
      = τ'.toMeasure.bind (jointFromBayesianKernel s) := rfl
  have h_τ'_toMeas : τ'.toMeasure = Measure.map κ' pi_X.toMeasure := by
    simp [hτ'_def, ProbDist.map_toMeasure]
  refine ⟨pi', hpi'_feas, ?_, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map Prod.fst pi'.toMeasure : Measure _) = pi_X.toMeasure
    ext A hA
    rw [Measure.map_apply measurable_fst hA]
    rw [h_pi'_meas]
    rw [Measure.bind_apply (hA.preimage measurable_fst)
      s.measurable_jointFromBayesianKernel.aemeasurable]
    have hkernel_apply : ∀ μ : ProbDist Ω,
        (jointFromBayesianKernel s μ) ((Prod.fst : _ × Ω → _) ⁻¹' A)
          = Measure.dirac (s.posteriorMoment μ) A := by
      intro μ
      unfold jointFromBayesianKernel
      rw [show ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' A)
          = A ×ˢ (Set.univ : Set Ω) from by ext ⟨x, ω⟩; simp]
      rw [Measure.prod_prod]
      simp
    have h_lint_eq :
        ∫⁻ μ, (jointFromBayesianKernel s μ) ((Prod.fst : _ × Ω → _) ⁻¹' A) ∂τ'.toMeasure
          = (Measure.map (s.posteriorMoment) τ'.toMeasure) A := by
      rw [show (∫⁻ μ, (jointFromBayesianKernel s μ)
            ((Prod.fst : _ × Ω → _) ⁻¹' A) ∂τ'.toMeasure)
          = ∫⁻ μ, Measure.dirac (s.posteriorMoment μ) A ∂τ'.toMeasure from
        lintegral_congr (fun μ => hkernel_apply μ)]
      have h_dirac_meas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
          (Measure.dirac y) A) :=
        (Measure.measurable_coe hA).comp Measure.measurable_dirac
      rw [show (∫⁻ μ, Measure.dirac (s.posteriorMoment μ) A ∂τ'.toMeasure)
          = ∫⁻ y, (Measure.dirac y) A
              ∂(Measure.map s.posteriorMoment τ'.toMeasure) from
        (MeasureTheory.lintegral_map h_dirac_meas s.measurable_posteriorMoment).symm]
      simp_rw [Measure.dirac_apply' _ hA]
      rw [MeasureTheory.lintegral_indicator_one hA]
    rw [h_lint_eq]
    rw [h_τ'_toMeas]
    rw [Measure.map_map s.measurable_posteriorMoment hκ'_subtype_meas]
    have h_ae_eq : (s.posteriorMoment ∘ κ') =ᵐ[pi_X.toMeasure] id := by
      filter_upwards [hκ'_mean] with x hx
      simpa [MomentSetup.posteriorMoment] using hx
    rw [Measure.map_congr h_ae_eq, Measure.map_id]
  · set Eset : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)) :=
      fun x => Set.extremePoints ℝ (Gamma_x s v S x) with hEset_def
    set N : Set (EuclideanSpace ℝ (Fin n) × Ω) :=
      {p | s.m p.2 ∉ Eset p.1} with hN_def
    have hN_meas : MeasurableSet N := by
      have h_eq : N = {p | s.m p.2 ∈ Eset p.1}ᶜ := by
        ext p; simp [hN_def]
      rw [h_eq]
      exact hG_meas.compl
    have hSx_meas : ∀ x, MeasurableSet (s.m ⁻¹' Eset x) := by
      intro x
      have h_eq : s.m ⁻¹' Eset x =
          (Prod.mk x) ⁻¹' {p : EuclideanSpace ℝ (Fin n) × Ω | s.m p.2 ∈ Eset p.1} := by
        ext ω; simp
      rw [h_eq]
      exact hG_meas.preimage measurable_prodMk_left
    rw [MeasureTheory.ae_iff]
    change pi'.toMeasure N = 0
    rw [h_pi'_meas]
    rw [Measure.bind_apply hN_meas s.measurable_jointFromBayesianKernel.aemeasurable]
    rw [h_τ'_toMeas]
    have h_kernel_meas : Measurable (fun μ : ProbDist Ω => (jointFromBayesianKernel s μ) N) :=
      Measure.measurable_coe hN_meas |>.comp s.measurable_jointFromBayesianKernel
    rw [lintegral_map h_kernel_meas hκ'_subtype_meas]
    have h_kernel_apply : ∀ μ : ProbDist Ω,
        (jointFromBayesianKernel s μ) N
          = μ.toMeasure ((s.m ⁻¹' Eset (s.posteriorMoment μ))ᶜ) := by
      intro μ
      unfold jointFromBayesianKernel
      rw [Measure.dirac_prod]
      rw [Measure.map_apply measurable_prodMk_left hN_meas]
      rfl
    rw [show (∫⁻ x, (jointFromBayesianKernel s (κ' x)) N ∂pi_X.toMeasure)
        = ∫⁻ x, (κ' x).toMeasure ((s.m ⁻¹' Eset (s.posteriorMoment (κ' x)))ᶜ)
            ∂pi_X.toMeasure from
      lintegral_congr (fun x => h_kernel_apply (κ' x))]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hκ'_mean, hκ'_supp] with x hx_mean hx_supp
    have h_post : s.posteriorMoment (κ' x) = x := by
      simpa [MomentSetup.posteriorMoment] using hx_mean
    rw [h_post]
    exact (MeasureTheory.prob_compl_eq_zero_iff (hSx_meas x)).mpr hx_supp

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The kernel replacement construction preserves primal optimality when the original joint is
primal-optimal. -/
lemma value_preserving_kernel_replacement (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_meas : Measurable v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    (hpi_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (κ' : EuclideanSpace ℝ (Fin n) → ProbDist Ω)
    (hκ'_meas : Measurable (fun x => (κ' x).toMeasure))
    (hκ'_mean :
      ∀ᵐ x ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∫ ω, s.m ω ∂(κ' x).toMeasure = x)
    (hκ'_bayes :
      ProbDist.bind (ProbDist.map pi Prod.fst measurable_fst) κ' hκ'_meas
        = s.prior)
    (hκ'_supp :
      ∀ᵐ x ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        (κ' x).toMeasure (s.m ⁻¹' Set.extremePoints ℝ (Gamma_x s v S x)) = 1)
    (hG_meas : MeasurableSet
      {p : EuclideanSpace ℝ (Fin n) × Ω |
        s.m p.2 ∈ Set.extremePoints ℝ (Gamma_x s v S p.1)}) :
    ∃ pi' ∈ feasibleJoint s,
      (∫ p, v p.1 ∂pi'.toMeasure = momentPrimal s v) ∧
      (∀ᵐ p ∂pi'.toMeasure,
        s.m p.2 ∈ Set.extremePoints ℝ (Gamma_x s v S p.1)) := by
  obtain ⟨pi', hpi'_feas, h_marg, h_supp⟩ :=
    feasible_of_kernel_replacement s hpi S κ' hκ'_meas hκ'_mean hκ'_bayes hκ'_supp hG_meas
  refine ⟨pi', hpi'_feas, ?_, h_supp⟩
  rw [mean_preserving_value_invariance hv_meas h_marg, hpi_opt]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
