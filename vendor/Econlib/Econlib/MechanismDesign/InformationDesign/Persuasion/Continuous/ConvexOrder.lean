/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Basic
public import Econlib.Probability.Order.Convex.Basic
public import Econlib.Probability.ProbDist.Supported

/-!
# Continuous persuasion: Convex-order Bayes plausibility on `ℝ`

The equal-mean Bayes-plausibility relation between laws on `ℝ` is the law-level condition needed
for convex-order refinements of continuous persuasion problems. This file relates it to the
posterior-mean law of an experiment, shows that posterior-mean laws are convex-order dominated by a
prior supported on `[a, b]`, and records that full disclosure reproduces the prior.

## Main definitions

* `HasEqualMean` — first-moment equality between two laws on `ℝ`; the law-level Bayes-plausibility
  condition.
* `posteriorMeanLaw` — the law of the posterior mean of an experiment.

## Main statements

* `bayesPlausibleLaw_posteriorMean` — the posterior-mean law has the same mean as the prior.
* `posteriorMeanLaw_convexOrderOnIcc` — the posterior-mean law of any experiment is convex-order
  dominated by a prior supported on `[a, b]`, the **mean-preserving spread** characterization of
  Bayes plausibility (Gentzkow and Kamenica 2016).
* `posteriorMeanLaw_id_eq_prior` — full disclosure reproduces the prior.

## Notes

`HasEqualMean` is symmetric and reflexive, so it records only the first-moment identity. The
directed mean-preserving-spread order is `Econlib.Probability.ConvexOrderOnIcc`, connected here by
`HasEqualMean.of_convexOrderOnIcc`.

## References

* Gentzkow, Matthew, and Emir Kamenica. 2016. “A Rothschild-Stiglitz Approach to Bayesian
  Persuasion.” *American Economic Review* 106 (5): 597–601. [https://doi.org/10.1257/aer.p20161049](https://doi.org/10.1257/aer.p20161049).

## Tags

persuasion, continuous persuasion, convex order, bayes plausibility, mean-preserving spread
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- `prior` and `posterior` have **equal mean** — the law-level Bayes-plausibility condition on
`ℝ`. This is bare first-moment equality: Symmetric and reflexive, so it carries none of the
directed mean-preserving-spread content (that lives in `ConvexOrderOnIcc`, which refines this
relation via `HasEqualMean.of_convexOrderOnIcc`). -/
def HasEqualMean (prior posterior : ProbabilityMeasure ℝ) : Prop :=
  ∫ x, x ∂prior.toMeasure = ∫ x, x ∂posterior.toMeasure

/-- `HasEqualMean` is reflexive. -/
@[simp] lemma HasEqualMean.refl (prior : ProbabilityMeasure ℝ) :
    HasEqualMean prior prior := rfl

/-- `HasEqualMean` is symmetric. -/
lemma HasEqualMean.symm {prior posterior : ProbabilityMeasure ℝ}
    (h : HasEqualMean prior posterior) :
    HasEqualMean posterior prior :=
  Eq.symm h

/-- `HasEqualMean` is transitive. -/
lemma HasEqualMean.trans {prior posterior next : ProbabilityMeasure ℝ}
    (h₁ : HasEqualMean prior posterior)
    (h₂ : HasEqualMean posterior next) :
    HasEqualMean prior next :=
  Eq.trans h₁ h₂

/-- The interval convex order refines the equal-mean relation: `μ ≼cx[a,b] ν` implies
`HasEqualMean μ ν`. -/
lemma HasEqualMean.of_convexOrderOnIcc {a b : ℝ} {prior posterior : ProbabilityMeasure ℝ}
    (h : Econlib.Probability.ConvexOrderOnIcc a b prior posterior) :
    HasEqualMean prior posterior :=
  h.mean_eq

/-- A posterior-mean law is just a law of a real-valued statistic of the signal. -/
noncomputable def posteriorMeanLaw (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean) :
    ProbabilityMeasure ℝ :=
  statisticLaw prior experiment posteriorMean h_posteriorMean

@[simp] lemma posteriorMeanLaw_toMeasure (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean) :
    ((posteriorMeanLaw prior experiment posteriorMean h_posteriorMean :
        ProbabilityMeasure ℝ) : Measure ℝ) =
      Measure.map posteriorMean (signalLaw prior experiment).toMeasure := rfl

/-- **Full disclosure reproduces the prior.** The posterior-mean law of the identity experiment
(the signal is the state) is the prior itself: The posterior at signal `x` is `δ_x`, so the
posterior mean is the state. -/
lemma posteriorMeanLaw_id (prior : ProbabilityMeasure ℝ) :
    posteriorMeanLaw prior (Kernel.id : Kernel ℝ ℝ)
        (posteriorValue prior Kernel.id id)
        ((stronglyMeasurable_posteriorValue prior Kernel.id stronglyMeasurable_id).measurable)
      = prior := by
  apply Subtype.ext
  change Measure.map (posteriorValue prior (Kernel.id : Kernel ℝ ℝ) id)
      (signalLaw prior (Kernel.id : Kernel ℝ ℝ)).toMeasure = prior.toMeasure
  have hsig : (signalLaw prior (Kernel.id : Kernel ℝ ℝ)).toMeasure = prior.toMeasure := by
    rw [signalLaw_toMeasure, Measure.id_comp]
  -- The posterior of full disclosure is the Dirac kernel, so the posterior mean is the state.
  have hae : posteriorValue prior (Kernel.id : Kernel ℝ ℝ) id =ᵐ[prior.toMeasure] id := by
    filter_upwards [ProbabilityTheory.posterior_id prior.toMeasure] with x hx
    rw [posteriorValue, posteriorKernel, hx, Kernel.id_apply, integral_dirac]
  rw [hsig, Measure.map_congr hae, Measure.map_id]

/-- If the posterior mean lies in a measurable set `s` almost everywhere under the signal law, then
the posterior-mean law is supported on `s`. -/
lemma posteriorMeanLaw_supportsOn_of_ae_mem (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean)
    {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ᵐ x ∂(signalLaw prior experiment).toMeasure, posteriorMean x ∈ s) :
    Econlib.Probability.ProbDist.supportsOn
      (posteriorMeanLaw prior experiment posteriorMean h_posteriorMean) s := by
  unfold Econlib.Probability.ProbDist.supportsOn
  rw [posteriorMeanLaw_toMeasure]
  have hnull : (signalLaw prior experiment).toMeasure {x | posteriorMean x ∉ s} = 0 := by
    simpa [ae_iff] using h
  have hmapnull :
      Measure.map posteriorMean (signalLaw prior experiment).toMeasure sᶜ = 0 := by
    rw [Measure.map_apply h_posteriorMean hs.compl]
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.preimage] using hnull
  calc
    Measure.map posteriorMean (signalLaw prior experiment).toMeasure s
      = Measure.map posteriorMean (signalLaw prior experiment).toMeasure Set.univ :=
        measure_of_measure_compl_eq_zero hmapnull
    _ = 1 := by
      rw [Measure.map_apply h_posteriorMean MeasurableSet.univ]
      simp

/-- If the posterior mean lies in a measurable set `s` everywhere, then the posterior-mean law is
supported on `s`. -/
lemma posteriorMeanLaw_supportsOn_of_mem (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean)
    {s : Set ℝ} (hs : MeasurableSet s) (h : ∀ x, posteriorMean x ∈ s) :
    Econlib.Probability.ProbDist.supportsOn
      (posteriorMeanLaw prior experiment posteriorMean h_posteriorMean) s :=
  posteriorMeanLaw_supportsOn_of_ae_mem prior experiment posteriorMean h_posteriorMean hs
    (ae_of_all _ h)

/-- If the posterior mean equals a constant `c` almost everywhere under the signal law, the
posterior-mean law is the Dirac mass at `c`. -/
lemma posteriorMeanLaw_eq_dirac_of_ae_eq_const (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean)
    {c : ℝ}
    (hconst : ∀ᵐ x ∂(signalLaw prior experiment).toMeasure, posteriorMean x = c) :
    posteriorMeanLaw prior experiment posteriorMean h_posteriorMean =
      Econlib.Probability.ProbDist.dirac c := by
    apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro s hs
    by_cases hc : c ∈ s
    · have hmem : ∀ᵐ x ∂(signalLaw prior experiment).toMeasure, posteriorMean x ∈ s := by
        filter_upwards [hconst] with x hx
        simp [hx, hc]
      have hsupport :
          Econlib.Probability.ProbDist.supportsOn
            (posteriorMeanLaw prior experiment posteriorMean h_posteriorMean) s :=
        posteriorMeanLaw_supportsOn_of_ae_mem prior experiment posteriorMean h_posteriorMean hs hmem
      unfold Econlib.Probability.ProbDist.supportsOn at hsupport
      calc
        (((posteriorMeanLaw prior experiment posteriorMean h_posteriorMean : ProbabilityMeasure ℝ) :
            Measure ℝ) s) = 1 := hsupport
        _ = (((Econlib.Probability.ProbDist.dirac c : ProbabilityMeasure ℝ) : Measure ℝ) s) := by
          simp [Econlib.Probability.ProbDist.dirac, hs, hc]
    · rw [posteriorMeanLaw_toMeasure, Measure.map_apply h_posteriorMean hs]
      have hnull :
          (signalLaw prior experiment).toMeasure (posteriorMean ⁻¹' s) = 0 := by
        have hnotpre :
            ∀ᵐ x ∂(signalLaw prior experiment).toMeasure, x ∈ (posteriorMean ⁻¹' s)ᶜ := by
          filter_upwards [hconst] with x hx
          simp [Set.mem_preimage, Set.mem_compl_iff, hx, hc]
        have hnull' :
            (signalLaw prior experiment).toMeasure {x | x ∉ (posteriorMean ⁻¹' s)ᶜ} = 0 := by
          simpa only [ae_iff, Set.mem_setOf_eq] using hnotpre
        simpa using hnull'
      simpa [Econlib.Probability.ProbDist.dirac, hs, hc] using hnull

/-- If the posterior mean equals a constant `c` everywhere, the posterior-mean law is the Dirac
mass at `c`. -/
lemma posteriorMeanLaw_eq_dirac_of_eq_const (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (posteriorMean : β → ℝ) (h_posteriorMean : Measurable posteriorMean)
    {c : ℝ} (hconst : ∀ x, posteriorMean x = c) :
    posteriorMeanLaw prior experiment posteriorMean h_posteriorMean =
      Econlib.Probability.ProbDist.dirac c :=
  posteriorMeanLaw_eq_dirac_of_ae_eq_const prior experiment posteriorMean h_posteriorMean
    (ae_of_all _ hconst)

/-- For a continuous convex `φ` on `[a, b]` and a prior supported on `[a, b]`, the posterior-mean
law gives a smaller `φ`-expectation than the prior: The convex-order inequality witnessing that the
posterior mean is a contraction of the prior. -/
lemma convex_expect_posteriorMeanLaw_le_of_supportsOn_Icc (prior : ProbabilityMeasure ℝ)
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    {a b : ℝ} (hprior : Econlib.Probability.ProbDist.supportsOn prior (Set.Icc a b))
    {φ : ℝ → ℝ} (hφ_conv : ConvexOn ℝ (Set.Icc a b) φ)
    (hφ_cont : ContinuousOn φ (Set.Icc a b)) :
    Econlib.Probability.ProbDist.expect
      (posteriorMeanLaw prior experiment (posteriorValue prior experiment id)
        (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable) φ
      ≤ Econlib.Probability.ProbDist.expect prior φ := by
  let m : β → ℝ := posteriorValue prior experiment id
  let hm : Measurable m :=
    (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable
  have hm_ae : ∀ᵐ x ∂(signalLaw prior experiment).toMeasure, m x ∈ Set.Icc a b :=
    ae_posteriorValue_mem_Icc_of_supportsOn_Icc prior experiment hprior
  have hm_support :
      Econlib.Probability.ProbDist.supportsOn
        (posteriorMeanLaw prior experiment m hm) (Set.Icc a b) :=
    posteriorMeanLaw_supportsOn_of_ae_mem prior experiment m hm measurableSet_Icc hm_ae
  have hφ_prior_int : Integrable φ prior.toMeasure :=
    Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc hprior hφ_cont
  have hφ_mean_int : Integrable φ (posteriorMeanLaw prior experiment m hm).toMeasure :=
    Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc hm_support hφ_cont
  have hleft_int : Integrable (fun x ↦ φ (m x)) (signalLaw prior experiment).toMeasure := by
    rw [posteriorMeanLaw_toMeasure] at hφ_mean_int
    simpa [m, Function.comp] using
      (integrable_map_measure hφ_mean_int.aestronglyMeasurable hm.aemeasurable).mp hφ_mean_int
  have hright_int :
      Integrable (posteriorValue prior experiment φ) (signalLaw prior experiment).toMeasure :=
    integrable_posteriorValue prior experiment hφ_prior_int
  have hJensen :
      ∀ᵐ x ∂(signalLaw prior experiment).toMeasure,
        φ (m x) ≤ posteriorValue prior experiment φ x := by
    filter_upwards
      [ae_posteriorLaw_supportsOn_of_supportsOn prior experiment measurableSet_Icc hprior]
      with x hx
    have hx_mem :
        ∀ᵐ y ∂(posteriorLaw prior experiment x).toMeasure, y ∈ Set.Icc a b :=
      Econlib.Probability.ProbDist.ae_mem_of_supportsOn measurableSet_Icc hx
    have hx_id_int : Integrable id (posteriorLaw prior experiment x).toMeasure :=
      Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc hx
    have hx_φ_int : Integrable φ (posteriorLaw prior experiment x).toMeasure :=
      Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc hx hφ_cont
    have hx_jensen :
        φ (∫ y, id y ∂(posteriorLaw prior experiment x).toMeasure) ≤
          ∫ y, φ (id y) ∂(posteriorLaw prior experiment x).toMeasure :=
      hφ_conv.map_integral_le hφ_cont isClosed_Icc hx_mem hx_id_int (by
        simpa [Function.comp] using hx_φ_int)
    simpa [m, posteriorLaw_toMeasure, posteriorValue, Function.comp] using hx_jensen
  calc
    Econlib.Probability.ProbDist.expect (posteriorMeanLaw prior experiment m hm) φ
      = ∫ x, φ (m x) ∂(signalLaw prior experiment).toMeasure :=
          Econlib.Probability.ProbDist.expect_map
            (signalLaw prior experiment) m hm φ hφ_mean_int.aestronglyMeasurable
    _ ≤ ∫ x, posteriorValue prior experiment φ x ∂(signalLaw prior experiment).toMeasure :=
          integral_mono_ae hleft_int hright_int hJensen
    _ = Econlib.Probability.ProbDist.expect prior φ := by
          simpa [Econlib.Probability.ProbDist.expect] using
            integral_posteriorValue prior experiment hφ_prior_int

/-- **Bayes plausibility.** The posterior-mean law of an experiment has the same mean as the prior
(Gentzkow and Kamenica 2016), whenever the identity is prior-integrable. -/
lemma bayesPlausibleLaw_posteriorMean (prior : ProbabilityMeasure ℝ)
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    (h_prior : Integrable id prior.toMeasure) :
    HasEqualMean prior
      (posteriorMeanLaw prior experiment (posteriorValue prior experiment id)
        (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable) := by
  let h_meas : Measurable (posteriorValue prior experiment id) :=
    (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable
  unfold HasEqualMean
  calc
    ∫ x, x ∂prior.toMeasure
      = ∫ y, posteriorValue prior experiment id y ∂(signalLaw prior experiment).toMeasure :=
          (integral_posteriorValue prior experiment h_prior).symm
    _ = ∫ y, y
          ∂(posteriorMeanLaw prior
            experiment (posteriorValue prior experiment id) h_meas).toMeasure := by
          rw [posteriorMeanLaw_toMeasure, MeasureTheory.integral_map h_meas.aemeasurable]
          exact aestronglyMeasurable_id

/-- The posterior-mean law of any experiment is convex-order dominated by a prior supported on
`[a, b]`. -/
lemma posteriorMeanLaw_convexOrderOnIcc {a b : ℝ}
    (sp : Econlib.Probability.SupportedProbDist (Set.Icc a b))
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] :
    Econlib.Probability.ConvexOrderOnIcc a b
      (posteriorMeanLaw sp.law experiment (posteriorValue sp.law experiment id)
        (stronglyMeasurable_posteriorValue sp.law experiment stronglyMeasurable_id).measurable)
      sp.law := by
  set prior : ProbabilityMeasure ℝ := sp.law with hprior_def
  have hprior : Econlib.Probability.ProbDist.supportsOn prior (Set.Icc a b) := sp.supported
  let hm : Measurable (posteriorValue prior experiment id) :=
    (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable
  refine ⟨?_, hprior, ?_, ?_⟩
  · exact posteriorMeanLaw_supportsOn_of_ae_mem prior experiment
      (posteriorValue prior experiment id) hm measurableSet_Icc
      (ae_posteriorValue_mem_Icc_of_supportsOn_Icc prior experiment hprior)
  · have hbp :=
      bayesPlausibleLaw_posteriorMean prior experiment
        (Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc hprior)
    unfold HasEqualMean at hbp
    simpa [Econlib.Probability.ProbDist.expect] using hbp.symm
  · intro φ hφ_conv hφ_cont
    exact convex_expect_posteriorMeanLaw_le_of_supportsOn_Icc prior experiment hprior
      hφ_conv hφ_cont

/-- Unit-interval specialization of `posteriorMeanLaw_convexOrderOnIcc`. -/
lemma posteriorMeanLaw_convexOrder
    (sp : Econlib.Probability.SupportedProbDist (Set.Icc 0 1))
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] :
    Econlib.Probability.ConvexOrder
      (posteriorMeanLaw sp.law experiment (posteriorValue sp.law experiment id)
        (stronglyMeasurable_posteriorValue sp.law experiment stronglyMeasurable_id).measurable)
      sp.law :=
  posteriorMeanLaw_convexOrderOnIcc sp experiment

/-- Under full disclosure the posterior mean is the state almost everywhere: The posterior at each
signal is a Dirac mass. -/
lemma posteriorValue_id_ae_eq (prior : ProbabilityMeasure ℝ) :
    posteriorValue prior (Kernel.id : ContinuousExperiment ℝ ℝ) id =ᵐ[prior.toMeasure] id := by
  filter_upwards [ProbabilityTheory.posterior_id prior.toMeasure] with x hx
  have hdirac :
      posteriorKernel prior (Kernel.id : ContinuousExperiment ℝ ℝ) x = Measure.dirac x := by
    simpa [posteriorKernel, Kernel.id] using hx
  simp [posteriorValue, hdirac]

/-- **Full disclosure reproduces the prior.** The posterior-mean law of the identity experiment is
the prior itself. -/
lemma posteriorMeanLaw_id_eq_prior (prior : ProbabilityMeasure ℝ) :
    posteriorMeanLaw prior (Kernel.id : ContinuousExperiment ℝ ℝ)
      (posteriorValue prior (Kernel.id : ContinuousExperiment ℝ ℝ) id)
      (stronglyMeasurable_posteriorValue prior
        (Kernel.id : ContinuousExperiment ℝ ℝ) stronglyMeasurable_id).measurable
      = prior := by
  ext s hs
  have hsignal :
      ((signalLaw prior (Kernel.id : ContinuousExperiment ℝ ℝ) : ProbabilityMeasure ℝ) :
        Measure ℝ) = prior.toMeasure := by
    rw [signalLaw_toMeasure]
    exact MeasureTheory.Measure.id_comp
  rw [posteriorMeanLaw_toMeasure, hsignal, Measure.map_congr (posteriorValue_id_ae_eq prior),
    Measure.map_id]

/-- If the posterior value is a.e. constant `c`, the dirac at `c` is convex-order below a prior
supported on `[a, b]`. -/
lemma dirac_convexOrderOnIcc_of_ae_posteriorValue_eq_const {a b c : ℝ}
    (sp : Econlib.Probability.SupportedProbDist (Set.Icc a b))
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    (hconst :
      ∀ᵐ x ∂(signalLaw sp.law experiment).toMeasure, posteriorValue sp.law experiment id x = c) :
    Econlib.Probability.ConvexOrderOnIcc a b (Econlib.Probability.ProbDist.dirac c) sp.law := by
  set prior : ProbabilityMeasure ℝ := sp.law with hprior_def
  let hm : Measurable (posteriorValue prior experiment id) :=
    (stronglyMeasurable_posteriorValue prior experiment stronglyMeasurable_id).measurable
  have hdirac :
      posteriorMeanLaw prior experiment (posteriorValue prior experiment id) hm =
        Econlib.Probability.ProbDist.dirac c :=
    posteriorMeanLaw_eq_dirac_of_ae_eq_const prior experiment (posteriorValue prior experiment id)
      hm hconst
  have hcx :
      Econlib.Probability.ConvexOrderOnIcc a b
        (posteriorMeanLaw prior experiment (posteriorValue prior experiment id) hm) prior :=
    posteriorMeanLaw_convexOrderOnIcc sp experiment
  simpa [hdirac] using hcx

/-- Unit-interval specialization of `dirac_convexOrderOnIcc_of_ae_posteriorValue_eq_const`. -/
lemma dirac_convexOrder_of_ae_posteriorValue_eq_const
    (sp : Econlib.Probability.SupportedProbDist (Set.Icc 0 1))
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    {c : ℝ}
    (hconst :
      ∀ᵐ x ∂(signalLaw sp.law experiment).toMeasure, posteriorValue sp.law experiment id x = c) :
    Econlib.Probability.ConvexOrder (Econlib.Probability.ProbDist.dirac c) sp.law :=
  dirac_convexOrderOnIcc_of_ae_posteriorValue_eq_const sp experiment hconst

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
