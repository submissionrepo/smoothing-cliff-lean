/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.PrimalAttainment
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbDist.Borel
public import Econlib.Probability.ProbDist.Disintegration

/-!
# Perturbation kernel via KR duality

A Bayes-plausible distribution of posteriors `τ` for a prior `μ₀` can be transported into a
feasible plan for a perturbed prior `η₀`, with the transport quality controlled by the
Kantorovich–Rubinstein distance `d_KR(μ₀, η₀)`.  This perturbation lemma underlies the KR-Lipschitz
preservation of the concave closure used in `KRStrongDuality`.

## Main definitions

* `kernelEval` — the evaluation Markov kernel `μ ↦ μ.toMeasure : ProbDist Ω → Ω`.

## Main statements

* `IsBayesPlausible.bind_eval_eq` — Bayes-plausibility in kernel form: The bind of `τ` along
  `kernelEval` reproduces the prior.
* `exists_perturbation_of_kr_duality` — perturbation kernel parameterized over the
  Kantorovich–Rubinstein duality hypothesis.
* `exists_perturbation` — same statement with the duality theorem inlined.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.2, Lemma 3.

## Tags

persuasion, duality, perturbation, Kantorovich-Rubinstein, optimal transport
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## KR-Lipschitz objectives and the perturbation kernel -/

section LipschitzPreservation

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-! ### Perturbation kernel -/

/-- The "evaluation" Markov kernel `μ ↦ μ.toMeasure : ProbDist Ω → Ω`.  Used to encode
Bayes-plausibility as a `compProd` identity. -/
noncomputable def kernelEval (Ω : Type*) [MeasurableSpace Ω] :
    ProbabilityTheory.Kernel (ProbDist Ω) Ω where
  toFun μ := μ.toMeasure
  measurable' := measurable_subtype_coe

/-- The evaluation kernel sends `μ` to its underlying measure. -/
@[simp] lemma kernelEval_apply (Ω : Type*) [MeasurableSpace Ω] (μ : ProbDist Ω) :
    kernelEval Ω μ = μ.toMeasure := rfl

/-- `kernelEval` is a Markov kernel, since each `μ.toMeasure` is a probability measure. -/
instance instIsMarkovKernelKernelEval (Ω : Type*) [MeasurableSpace Ω] :
    ProbabilityTheory.IsMarkovKernel (kernelEval Ω) :=
  ⟨fun μ => μ.prop⟩

/-- **Bayes-plausibility, kernel form.**  If `τ` is Bayes-plausible for `μ₀`, the bind of `τ` along
the evaluation kernel reproduces `μ₀` as a measure on `Ω`. -/
lemma IsBayesPlausible.bind_eval_eq [CompactSpace Ω] [BorelSpace Ω]
    [SecondCountableTopology Ω] [T2Space Ω]
    {μ₀ : ProbDist Ω} {τ : ProbDist (ProbDist Ω)}
    (hτ : IsBayesPlausible μ₀ τ) :
    τ.toMeasure.bind (fun μ => μ.toMeasure) = μ₀.toMeasure := by
  haveI : IsProbabilityMeasure
      (τ.toMeasure.bind (fun μ : ProbDist Ω => μ.toMeasure)) :=
    isProbabilityMeasure_bind measurable_subtype_coe.aemeasurable
      (Filter.Eventually.of_forall fun μ => μ.prop)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [show τ.toMeasure.bind (fun μ : ProbDist Ω => μ.toMeasure)
        = (τ.toMeasure.compProd (kernelEval Ω)).snd from
      (Measure.snd_compProd τ.toMeasure (kernelEval Ω)).symm]
  have hf_int : Integrable (fun z : ProbDist Ω × Ω => f z.2)
      (τ.toMeasure.compProd (kernelEval Ω)) := by
    haveI : IsProbabilityMeasure (τ.toMeasure.compProd (kernelEval Ω)) :=
      inferInstance
    let fcompBCF : (ProbDist Ω × Ω) →ᵇ ℝ :=
      f.compContinuous ⟨Prod.snd, continuous_snd⟩
    exact fcompBCF.integrable (τ.toMeasure.compProd (kernelEval Ω))
  have hsnd_def :
      (τ.toMeasure.compProd (kernelEval Ω)).snd
        = Measure.map Prod.snd (τ.toMeasure.compProd (kernelEval Ω)) := rfl
  rw [hsnd_def, MeasureTheory.integral_map measurable_snd.aemeasurable
    f.continuous.aestronglyMeasurable]
  rw [Measure.integral_compProd hf_int]
  simp only [kernelEval_apply]
  exact hτ f

/-- **Perturbation kernel, modulo Kantorovich–Rubinstein duality.**

Same conclusion as `exists_perturbation`, but parameterized over the duality hypothesis
`krDist μ ν = krTransportCost μ ν`. -/
theorem exists_perturbation_of_kr_duality [CompactSpace Ω] [BorelSpace Ω]
    [SecondCountableTopology Ω] [T2Space Ω]
    {μ₀ η₀ : ProbDist Ω} {τ : ProbDist (ProbDist Ω)}
    (hτ : IsBayesPlausible μ₀ τ)
    (hKR : ∀ μ ν : ProbDist Ω,
      krDist μ ν = krTransportCost μ ν) :
    ∃ η : ProbDist Ω → ProbDist Ω, Measurable η ∧
      (∀ f : Ω →ᵇ ℝ, ∫ μ, ProbDist.expect (η μ) f ∂τ.toMeasure
                      = ProbDist.expect η₀ f) ∧
      Integrable (fun μ => krDist μ (η μ)) τ.toMeasure ∧
      ∫ μ, krDist μ (η μ) ∂τ.toMeasure
        = krDist μ₀ η₀ := by
  haveI : Nonempty Ω := μ₀.nonempty
  let dBC : (Ω × Ω) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun z : Ω × Ω => dist z.1 z.2, continuous_dist⟩
  obtain ⟨lam, hlam_mem, hlam_eq⟩ :=
    exists_optimal_coupling dBC μ₀ η₀
  have hlam_kr :
      krDist μ₀ η₀ = ∫ z, dist z.1 z.2 ∂lam.toMeasure := by
    rw [hKR]
    unfold krTransportCost
    exact hlam_eq
  let kLam : Ω → ProbDist Ω := Econlib.Probability.ProbDist.condFst lam
  have kLam_meas : Measurable (fun ω => (kLam ω).toMeasure) :=
    Econlib.Probability.ProbDist.condFst_measurable lam
  let η : ProbDist Ω → ProbDist Ω :=
    fun μ => Econlib.Probability.ProbDist.bind μ kLam kLam_meas
  let kLamKernel : ProbabilityTheory.Kernel Ω Ω :=
    { toFun := fun ω => (kLam ω).toMeasure
      measurable' := kLam_meas }
  haveI hkLam_markov : ProbabilityTheory.IsMarkovKernel kLamKernel :=
    ⟨fun ω => (kLam ω).prop⟩
  have kLamKernel_apply : ∀ ω, kLamKernel ω = (kLam ω).toMeasure := fun _ => rfl
  have hbayes : τ.toMeasure.bind (fun μ => μ.toMeasure) = μ₀.toMeasure :=
    hτ.bind_eval_eq
  have hlam_fst : lam.toMeasure.fst = μ₀.toMeasure := by
    have heq := congrArg (fun d : ProbDist Ω => d.toMeasure) hlam_mem.fst_marginal
    simpa [Measure.fst, ProbDist.map_toMeasure] using heq
  have hlam_snd : lam.toMeasure.snd = η₀.toMeasure := by
    have heq := congrArg (fun d : ProbDist Ω => d.toMeasure) hlam_mem.snd_marginal
    simpa [Measure.snd, ProbDist.map_toMeasure] using heq
  have hcompProd_lam : μ₀.toMeasure.compProd kLamKernel = lam.toMeasure := by
    have h := Econlib.Probability.ProbDist.condFst_compProd lam
    rw [← hlam_fst]
    convert h using 2
  have hη_meas_aux : Measurable η := by
    have hbind_meas : Measurable (fun μ : ProbDist Ω =>
        μ.toMeasure.bind (fun ω => (kLam ω).toMeasure)) :=
      (Measure.measurable_bind' kLam_meas).comp measurable_subtype_coe
    exact Measurable.subtype_mk hbind_meas
  have hη_avg_aux : ∀ f : Ω →ᵇ ℝ,
      ∫ μ, ProbDist.expect (η μ) f ∂τ.toMeasure = ProbDist.expect η₀ f := by
    intro f
    have hexpect_cont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
      simpa [ProbDist.expect] using
        MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f
    have hstepA : ∀ μ : ProbDist Ω,
        ProbDist.expect (η μ) f
          = ∫ ω, ProbDist.expect (kLam ω) f ∂μ.toMeasure := by
      intro μ
      change ∫ x, f x ∂(η μ).toMeasure = _
      have htoMeas :
          (η μ).toMeasure = (μ.toMeasure.compProd kLamKernel).snd := by
        change μ.toMeasure.bind (fun ω => (kLam ω).toMeasure) = _
        rw [show (fun ω => (kLam ω).toMeasure) = ⇑kLamKernel from rfl,
            ← Measure.snd_compProd μ.toMeasure kLamKernel]
      rw [htoMeas]
      have hsnd_def : (μ.toMeasure.compProd kLamKernel).snd
          = Measure.map Prod.snd (μ.toMeasure.compProd kLamKernel) := rfl
      rw [hsnd_def, MeasureTheory.integral_map measurable_snd.aemeasurable
        f.continuous.aestronglyMeasurable]
      have hf_int : Integrable (fun z : Ω × Ω => f z.2)
          (μ.toMeasure.compProd kLamKernel) := by
        haveI : IsProbabilityMeasure (μ.toMeasure.compProd kLamKernel) := inferInstance
        let fcompBCF : (Ω × Ω) →ᵇ ℝ :=
          f.compContinuous ⟨Prod.snd, continuous_snd⟩
        exact fcompBCF.integrable (μ.toMeasure.compProd kLamKernel)
      rw [Measure.integral_compProd hf_int]
      rfl
    have hgoal_eq :
        ∫ μ, ProbDist.expect (η μ) f ∂τ.toMeasure
          = ∫ μ, ∫ ω, ProbDist.expect (kLam ω) f ∂μ.toMeasure ∂τ.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hstepA
    rw [hgoal_eq]
    set Ψ : Ω → ℝ := fun ω => ProbDist.expect (kLam ω) f with hΨ_def
    have hΨ_smeas : MeasureTheory.StronglyMeasurable Ψ := by
      exact MeasureTheory.StronglyMeasurable.integral_kernel
        (κ := kLamKernel) f.continuous.stronglyMeasurable
    have hΨ_meas : Measurable Ψ := hΨ_smeas.measurable
    have hΨ_bdd : ∀ ω, |Ψ ω| ≤ ‖f‖ := by
      intro ω
      have hle : ‖∫ y, f y ∂(kLam ω).toMeasure‖ ≤ ‖f‖ := by
        haveI : IsProbabilityMeasure (kLam ω).toMeasure := (kLam ω).prop
        calc ‖∫ y, f y ∂(kLam ω).toMeasure‖
            ≤ ∫ y, ‖f y‖ ∂(kLam ω).toMeasure :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ _, ‖f‖ ∂(kLam ω).toMeasure := by
              apply integral_mono_ae
              · exact (f.integrable (kLam ω).toMeasure).norm
              · exact integrable_const _
              · exact Filter.Eventually.of_forall fun y =>
                  BoundedContinuousFunction.norm_coe_le_norm f y
          _ = ‖f‖ := by simp
      simpa [Real.norm_eq_abs] using hle
    have hΨcomp_int : Integrable (fun z : ProbDist Ω × Ω => Ψ z.2)
        (τ.toMeasure.compProd (kernelEval Ω)) := by
      haveI : IsProbabilityMeasure (τ.toMeasure.compProd (kernelEval Ω)) := inferInstance
      refine ⟨(hΨ_meas.comp measurable_snd).aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const ‖f‖).mono' ?_
      refine Filter.Eventually.of_forall fun z => ?_
      simpa [Real.norm_eq_abs] using hΨ_bdd z.2
    have hcomp :
        ∫ μ, ∫ ω, Ψ ω ∂μ.toMeasure ∂τ.toMeasure
          = ∫ z, Ψ z.2 ∂(τ.toMeasure.compProd (kernelEval Ω)) := by
      rw [Measure.integral_compProd hΨcomp_int]
      rfl
    rw [hcomp]
    have hsnd_def : (τ.toMeasure.compProd (kernelEval Ω)).snd
        = Measure.map Prod.snd (τ.toMeasure.compProd (kernelEval Ω)) := rfl
    rw [show (∫ z, Ψ z.2 ∂(τ.toMeasure.compProd (kernelEval Ω)))
          = ∫ ω, Ψ ω ∂(τ.toMeasure.compProd (kernelEval Ω)).snd from by
        rw [hsnd_def, MeasureTheory.integral_map measurable_snd.aemeasurable
          hΨ_meas.aestronglyMeasurable]]
    rw [Measure.snd_compProd τ.toMeasure (kernelEval Ω)]
    change ∫ ω, Ψ ω ∂(τ.toMeasure.bind (fun μ => μ.toMeasure)) = ProbDist.expect η₀ f
    rw [hbayes]
    have hf_int_lam : Integrable (fun z : Ω × Ω => f z.2)
        (μ₀.toMeasure.compProd kLamKernel) := by
      haveI : IsProbabilityMeasure (μ₀.toMeasure.compProd kLamKernel) := inferInstance
      let fcompBCF : (Ω × Ω) →ᵇ ℝ :=
        f.compContinuous ⟨Prod.snd, continuous_snd⟩
      exact fcompBCF.integrable (μ₀.toMeasure.compProd kLamKernel)
    calc ∫ ω, Ψ ω ∂μ₀.toMeasure
        = ∫ ω, ∫ y, f y ∂(kLam ω).toMeasure ∂μ₀.toMeasure := rfl
      _ = ∫ z, f z.2 ∂(μ₀.toMeasure.compProd kLamKernel) := by
          rw [Measure.integral_compProd hf_int_lam]
          rfl
      _ = ∫ z, f z.2 ∂lam.toMeasure := by rw [hcompProd_lam]
      _ = ∫ y, f y ∂lam.toMeasure.snd := by
          change _ = ∫ y, f y ∂Measure.map Prod.snd lam.toMeasure
          rw [MeasureTheory.integral_map measurable_snd.aemeasurable
            f.continuous.aestronglyMeasurable]
      _ = ∫ y, f y ∂η₀.toMeasure := by rw [hlam_snd]
      _ = ProbDist.expect η₀ f := rfl
  set B : ProbDist Ω → ℝ :=
    fun μ => ∫ z, dist z.1 z.2 ∂(μ.toMeasure.compProd kLamKernel) with hB_def
  -- `G ω` is the average distance from `ω` to its perturbed posterior `kLam ω`; `B μ`
  -- is the `μ`-average of `G`, and both are bounded by `‖dBC‖`.
  set G : Ω → ℝ := fun ω => ∫ y, dist ω y ∂kLamKernel ω with hG_def
  have hG_smeas : MeasureTheory.StronglyMeasurable G :=
    MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
      (κ := kLamKernel) continuous_dist.stronglyMeasurable
  have hG_bdd : ∀ ω, |G ω| ≤ ‖dBC‖ := by
    intro ω
    haveI : IsProbabilityMeasure (kLamKernel ω) := hkLam_markov.isProbabilityMeasure ω
    have h₁ : |G ω| ≤ ∫ y, |dist ω y| ∂kLamKernel ω := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := kLamKernel ω)
          (fun y => dist ω y))
    have hd_int : Integrable (fun y => dist ω y) (kLamKernel ω) := by
      have hcont_dist : Continuous (fun y => dist ω y) := continuous_const.dist continuous_id
      let hd_bcf : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, hcont_dist⟩
      exact hd_bcf.integrable (kLamKernel ω)
    have hd_abs_int : Integrable (fun y => |dist ω y|) (kLamKernel ω) := by
      simpa [abs_of_nonneg dist_nonneg] using hd_int
    have h₂ : ∫ y, |dist ω y| ∂kLamKernel ω ≤ ∫ _, ‖dBC‖ ∂kLamKernel ω := by
      apply integral_mono_ae hd_abs_int (integrable_const _)
      exact Filter.Eventually.of_forall fun y => by
        have h := BoundedContinuousFunction.norm_coe_le_norm dBC (ω, y)
        have hdBC_z : dBC (ω, y) = dist ω y := rfl
        rw [hdBC_z, Real.norm_eq_abs] at h
        exact h
    have h₃ : ∫ _, ‖dBC‖ ∂kLamKernel ω = ‖dBC‖ := by simp
    linarith
  have hB_eq : ∀ μ : ProbDist Ω, B μ = ∫ ω, G ω ∂μ.toMeasure := by
    intro μ
    have hd_int : Integrable (fun z : Ω × Ω => dist z.1 z.2)
        (μ.toMeasure.compProd kLamKernel) := dBC.integrable _
    simpa [B, kLamKernel_apply, G] using Measure.integral_compProd hd_int
  have hπ_coupling : ∀ μ : ProbDist Ω,
      ∃ π : ProbDist (Ω × Ω), π ∈ couplings μ (η μ) ∧
        π.toMeasure = μ.toMeasure.compProd kLamKernel := by
    intro μ
    haveI : IsProbabilityMeasure (μ.toMeasure.compProd kLamKernel) := inferInstance
    refine ⟨⟨μ.toMeasure.compProd kLamKernel, inferInstance⟩, ?_, rfl⟩
    refine ⟨?_, ?_⟩
    · apply ProbabilityMeasure.toMeasure_injective
      exact Measure.fst_compProd μ.toMeasure kLamKernel
    · apply ProbabilityMeasure.toMeasure_injective
      change (μ.toMeasure.compProd kLamKernel).snd = _
      rw [Measure.snd_compProd μ.toMeasure kLamKernel]
      rfl
  have hkr_le_B : ∀ μ : ProbDist Ω,
      krDist μ (η μ) ≤ B μ := by
    intro μ
    obtain ⟨π, hπ_mem, hπ_eq⟩ := hπ_coupling μ
    calc krDist μ (η μ)
        ≤ krTransportCost μ (η μ) :=
          krDist_le_krTransportCost μ (η μ)
      _ ≤ ∫ z, dist z.1 z.2 ∂π.toMeasure :=
          transportCost_le_integral_of_bdd
            (continuous_dist (α := Ω)).measurable μ (η μ)
            (fun z => le_trans (neg_nonpos.mpr (norm_nonneg dBC)) dist_nonneg)
            (fun z => by
              have h := BoundedContinuousFunction.norm_coe_le_norm dBC z
              have hdBC_z : dBC z = dist z.1 z.2 := rfl
              rw [hdBC_z, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at h
              exact h)
            hπ_mem
      _ = B μ := by rw [hπ_eq]
  have hkr_nonneg : ∀ μ : ProbDist Ω,
      0 ≤ krDist μ (η μ) := by
    intro μ
    refine le_csSup (bddAbove_krDist_setOf μ (η μ)) ?_
    refine ⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [ProbDist.expect]
  -- `G` is bounded by `‖dBC‖`, hence integrable against any probability measure.
  have hG_int : ∀ μ : ProbDist Ω, Integrable G μ.toMeasure := by
    intro μ
    refine ⟨hG_smeas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const ‖dBC‖).mono' ?_
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hG_bdd ω
  -- `|B μ| = |∫ G dμ| ≤ ∫ |G| dμ ≤ ‖dBC‖` since `|G| ≤ ‖dBC‖` pointwise.
  have hB_bdd : ∀ μ, |B μ| ≤ ‖dBC‖ := by
    intro μ
    rw [hB_eq]
    have h₁ : |∫ ω, G ω ∂μ.toMeasure| ≤ ∫ ω, |G ω| ∂μ.toMeasure := by
      simpa [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (μ := μ.toMeasure) G)
    have h₂ : ∫ ω, |G ω| ∂μ.toMeasure ≤ ∫ _, ‖dBC‖ ∂μ.toMeasure :=
      integral_mono_ae (hG_int μ).abs (integrable_const _)
        (Filter.Eventually.of_forall hG_bdd)
    have h₃ : ∫ _, ‖dBC‖ ∂μ.toMeasure = ‖dBC‖ := by simp
    linarith
  have hB_smeas : MeasureTheory.StronglyMeasurable B := by
    have hB_eq' : B = fun μ : ProbDist Ω => ∫ ω, G ω ∂(kernelEval Ω) μ := by
      funext μ
      rw [hB_eq]; rfl
    rw [hB_eq']
    exact MeasureTheory.StronglyMeasurable.integral_kernel
      (κ := kernelEval Ω) hG_smeas
  have hB_int : Integrable B τ.toMeasure := by
    refine ⟨hB_smeas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const ‖dBC‖).mono' ?_
    refine Filter.Eventually.of_forall fun μ => ?_
    simpa [Real.norm_eq_abs] using hB_bdd μ
  -- `krDist` is LSC as a supremum of continuous functions, hence Borel measurable.
  have hkr_int_meas : Measurable
      (fun μ : ProbDist Ω => krDist μ (η μ)) := by
    let Lip1 : Type _ := {p : Ω → ℝ // LipschitzWith 1 p}
    haveI : Nonempty Lip1 :=
      ⟨⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp)⟩⟩
    have hcomp_cont : ∀ p : Lip1, Continuous
        (fun q : ProbDist Ω × ProbDist Ω =>
          ProbDist.expect q.1 (p : Ω → ℝ) - ProbDist.expect q.2 (p : Ω → ℝ)) := by
      intro p
      have hp_cont : Continuous (p : Ω → ℝ) := p.2.continuous
      let pBCF : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨_, hp_cont⟩
      have hexpect_cont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ (p : Ω → ℝ)) := by
        simpa [ProbDist.expect] using
          MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
            (X := Ω) pBCF
      exact (hexpect_cont.comp continuous_fst).sub (hexpect_cont.comp continuous_snd)
    have hkr_iSup : ∀ q : ProbDist Ω × ProbDist Ω,
        (⨆ p : Lip1, ProbDist.expect q.1 (p : Ω → ℝ) - ProbDist.expect q.2 (p : Ω → ℝ))
          = krDist q.1 q.2 := by
      intro q
      unfold krDist
      apply le_antisymm
      · refine ciSup_le ?_
        intro p
        refine le_csSup (bddAbove_krDist_setOf q.1 q.2) ?_
        exact ⟨p.1, p.2, rfl⟩
      · refine csSup_le ?_ ?_
        · refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
          simp [ProbDist.expect]
        rintro x ⟨p, hp_lip, rfl⟩
        refine le_ciSup_of_le ?_ ⟨p, hp_lip⟩ le_rfl
        refine ⟨krTransportCost q.1 q.2, ?_⟩
        rintro y ⟨p, rfl⟩
        exact lipschitz_expect_sub_le_krTransportCost q.1 q.2 p.2
    have hbddAbove : ∀ q : ProbDist Ω × ProbDist Ω,
        BddAbove (Set.range fun p : Lip1 =>
          ProbDist.expect q.1 (p : Ω → ℝ) - ProbDist.expect q.2 (p : Ω → ℝ)) := by
      intro q
      refine ⟨krTransportCost q.1 q.2, ?_⟩
      rintro y ⟨p, rfl⟩
      exact lipschitz_expect_sub_le_krTransportCost q.1 q.2 p.2
    have hkr_lsc : LowerSemicontinuous
        (fun q : ProbDist Ω × ProbDist Ω => krDist q.1 q.2) := by
      have h := lowerSemicontinuous_ciSup (f := fun (p : Lip1) (q : ProbDist Ω × ProbDist Ω) =>
        ProbDist.expect q.1 (p : Ω → ℝ) - ProbDist.expect q.2 (p : Ω → ℝ))
        hbddAbove
        (fun p => (hcomp_cont p).lowerSemicontinuous)
      have h' : (fun q : ProbDist Ω × ProbDist Ω =>
          ⨆ p : Lip1, ProbDist.expect q.1 (p : Ω → ℝ) - ProbDist.expect q.2 (p : Ω → ℝ))
          = fun q => krDist q.1 q.2 := by
        funext q; exact hkr_iSup q
      rw [← h']; exact h
    have hkr_meas : Measurable
        (fun q : ProbDist Ω × ProbDist Ω => krDist q.1 q.2) :=
      hkr_lsc.measurable
    have hpair_meas : Measurable (fun μ : ProbDist Ω => (μ, η μ)) :=
      measurable_id.prodMk hη_meas_aux
    exact hkr_meas.comp hpair_meas
  have hkr_int : Integrable
      (fun μ : ProbDist Ω => krDist μ (η μ)) τ.toMeasure := by
    refine ⟨hkr_int_meas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const ‖dBC‖).mono' ?_
    refine Filter.Eventually.of_forall fun μ => ?_
    have hbnd : krDist μ (η μ) ≤ ‖dBC‖ :=
      le_trans (hkr_le_B μ) (le_trans (le_abs_self _) (hB_bdd μ))
    have hnn : 0 ≤ krDist μ (η μ) := hkr_nonneg μ
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hbnd
  refine ⟨η, ?hη_meas, ?hη_avg, ?hKR_int, ?hKR_eq⟩
  case hη_meas => exact hη_meas_aux
  case hη_avg => exact hη_avg_aux
  case hKR_int => exact hkr_int
  case hKR_eq =>
    apply le_antisymm
    · have h₁ : ∫ μ, krDist μ (η μ) ∂τ.toMeasure
          ≤ ∫ μ, B μ ∂τ.toMeasure :=
        integral_mono_ae hkr_int hB_int (Filter.Eventually.of_forall hkr_le_B)
      have hB_int_eq : ∫ μ, B μ ∂τ.toMeasure
          = ∫ μ, ∫ ω, G ω ∂μ.toMeasure ∂τ.toMeasure :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hB_eq)
      have hGcomp_int : Integrable (fun z : ProbDist Ω × Ω => G z.2)
          (τ.toMeasure.compProd (kernelEval Ω)) := by
        haveI : IsProbabilityMeasure (τ.toMeasure.compProd (kernelEval Ω)) := inferInstance
        refine ⟨(hG_smeas.measurable.comp measurable_snd).aestronglyMeasurable, ?_⟩
        refine (hasFiniteIntegral_const ‖dBC‖).mono' ?_
        refine Filter.Eventually.of_forall fun z => ?_
        simpa [Real.norm_eq_abs] using hG_bdd z.2
      have hcompProd_step :
          ∫ μ, ∫ ω, G ω ∂μ.toMeasure ∂τ.toMeasure
            = ∫ z, G z.2 ∂(τ.toMeasure.compProd (kernelEval Ω)) := by
        rw [Measure.integral_compProd hGcomp_int]
        rfl
      have hsnd_step :
          ∫ z, G z.2 ∂(τ.toMeasure.compProd (kernelEval Ω))
            = ∫ ω, G ω ∂(τ.toMeasure.compProd (kernelEval Ω)).snd := by
        have hsnd_def : (τ.toMeasure.compProd (kernelEval Ω)).snd
            = Measure.map Prod.snd (τ.toMeasure.compProd (kernelEval Ω)) := rfl
        rw [hsnd_def, MeasureTheory.integral_map measurable_snd.aemeasurable
          hG_smeas.aestronglyMeasurable]
      have hbayes_step :
          ∫ ω, G ω ∂(τ.toMeasure.compProd (kernelEval Ω)).snd
            = ∫ ω, G ω ∂μ₀.toMeasure := by
        rw [Measure.snd_compProd τ.toMeasure (kernelEval Ω)]
        change ∫ ω, G ω ∂(τ.toMeasure.bind (fun μ => μ.toMeasure))
              = ∫ ω, G ω ∂μ₀.toMeasure
        rw [hbayes]
      have hd_int_lam : Integrable (fun z : Ω × Ω => dist z.1 z.2)
          (μ₀.toMeasure.compProd kLamKernel) := dBC.integrable _
      have hG_to_lam :
          ∫ ω, G ω ∂μ₀.toMeasure = ∫ z, dist z.1 z.2 ∂lam.toMeasure := by
        calc ∫ ω, G ω ∂μ₀.toMeasure
            = ∫ ω, ∫ y, dist ω y ∂kLamKernel ω ∂μ₀.toMeasure := rfl
          _ = ∫ z, dist z.1 z.2 ∂(μ₀.toMeasure.compProd kLamKernel) := by
              rw [Measure.integral_compProd hd_int_lam]
          _ = ∫ z, dist z.1 z.2 ∂lam.toMeasure := by rw [hcompProd_lam]
      have hB_chain :
          ∫ μ, B μ ∂τ.toMeasure = krDist μ₀ η₀ := by
        rw [hB_int_eq, hcompProd_step, hsnd_step, hbayes_step, hG_to_lam, ← hlam_kr]
      linarith
    · have hge :=
        krDist_le_integral_krDist_pair μ₀ η₀ τ
          (ν := η) hη_meas_aux hτ hη_avg_aux hkr_int
      exact hge

/-- **Existence of the perturbation kernel.**  Given a Bayes-plausible distribution of posteriors
`τ` for prior `μ₀` and any target prior `η₀`, there exists a measurable function
`η : ProbDist Ω → ProbDist Ω` such that:

* The perturbed posteriors `η μ` average to `η₀` under `τ`: For every bounded continuous `f`,
  `∫ (η μ).expect f dτ(μ) = η₀.expect f`.
* The average KR-distance between `μ` and `η μ` equals the KR-distance between the priors `μ₀` and
  `η₀` (with the integrand integrable). -/
theorem exists_perturbation [CompactSpace Ω] [BorelSpace Ω]
    [SecondCountableTopology Ω] [T2Space Ω]
    {μ₀ η₀ : ProbDist Ω} {τ : ProbDist (ProbDist Ω)}
    (hτ : IsBayesPlausible μ₀ τ) :
    ∃ η : ProbDist Ω → ProbDist Ω, Measurable η ∧
      (∀ f : Ω →ᵇ ℝ, ∫ μ, ProbDist.expect (η μ) f ∂τ.toMeasure
                      = ProbDist.expect η₀ f) ∧
      Integrable (fun μ => krDist μ (η μ)) τ.toMeasure ∧
      ∫ μ, krDist μ (η μ) ∂τ.toMeasure
        = krDist μ₀ η₀ :=
  exists_perturbation_of_kr_duality hτ
    krDist_eq_krTransportCost

end LipschitzPreservation

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
