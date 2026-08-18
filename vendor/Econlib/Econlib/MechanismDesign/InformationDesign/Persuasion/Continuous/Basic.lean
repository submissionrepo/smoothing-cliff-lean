/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Convex.Basic
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbDist.Stationary
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Kernel.Posterior

/-!
# Continuous persuasion: Experiment kernels and posteriors

This file defines **Bayesian persuasion** experiments with continuous state and signal spaces. A
continuous experiment is a Markov kernel from states to signals; together with a prior, it induces
a signal law and a posterior kernel by Bayes' rule. Averaging posterior values against the signal
law recovers the prior value, the law-level Bayes-plausibility identity behind the convex-order
viewpoint on persuasion.

## Main definitions

* `ContinuousExperiment α β` — Markov kernel from states `α` to signals `β`.
* `signalLaw` — marginal signal distribution under the experiment.
* `statisticLaw` — distribution of a real-valued statistic of the signal.
* `posteriorKernel` — posterior distribution kernel `β → ProbDist α`.
* `posteriorLaw` — posterior at a particular signal.
* `posteriorValue` — integral of a state statistic against the posterior.

## Main statements

* `integral_posteriorValue` — the signal-law average of a posterior value equals the prior average:
  Posteriors average back to the prior.
* `ae_posteriorLaw_supportsOn_of_supportsOn` — almost every posterior is supported on any set that
  carries the full prior.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).
* Gentzkow, Matthew, and Emir Kamenica. 2016. “A Rothschild-Stiglitz Approach to Bayesian
  Persuasion.” *American Economic Review* 106 (5): 597–601. [https://doi.org/10.1257/aer.p20161049](https://doi.org/10.1257/aer.p20161049).

## Tags

persuasion, continuous persuasion, posterior, Markov kernel, mean-preserving spread
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

variable {α β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]

/-- A continuous experiment is a Markov kernel from states to signals. -/
abbrev ContinuousExperiment (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  Kernel α β

/-- The marginal signal law induced by a prior and a kernel experiment. -/
noncomputable def signalLaw (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment] :
    ProbabilityMeasure β :=
  ⟨experiment ∘ₘ prior.toMeasure, inferInstance⟩

/-- The law of a real-valued signal statistic under the marginal signal law. -/
noncomputable def statisticLaw (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (statistic : β → ℝ) (h_stat : Measurable statistic) : ProbabilityMeasure ℝ :=
  Econlib.Probability.ProbDist.map (signalLaw prior experiment) statistic h_stat

@[simp] lemma signalLaw_toMeasure (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment] :
    (signalLaw prior experiment : Measure β) = experiment ∘ₘ prior.toMeasure := rfl

@[simp] lemma statisticLaw_toMeasure (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [IsMarkovKernel experiment]
    (statistic : β → ℝ) (h_stat : Measurable statistic) :
    ((statisticLaw prior experiment statistic h_stat : ProbabilityMeasure ℝ) : Measure ℝ) =
      Measure.map statistic (signalLaw prior experiment).toMeasure :=
  Econlib.Probability.ProbDist.map_toMeasure (signalLaw prior experiment) statistic h_stat

/-- The posterior kernel attached to a prior and continuous experiment. -/
noncomputable def posteriorKernel (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] : Kernel β α :=
  ProbabilityTheory.posterior experiment prior.toMeasure

@[simp] lemma posteriorKernel_comp_signalLaw (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] :
    posteriorKernel prior experiment ∘ₘ (signalLaw prior experiment).toMeasure
      = prior.toMeasure := by
  simp [posteriorKernel, signalLaw_toMeasure]

/-- Integrate a real-valued state statistic against the posterior kernel. -/
noncomputable def posteriorValue (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] (u : α → ℝ) : β → ℝ :=
  fun x ↦ ∫ a, u a ∂posteriorKernel prior experiment x

/-- The posterior section at a signal as a probability law. -/
noncomputable def posteriorLaw (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] (x : β) : ProbabilityMeasure α :=
  ⟨posteriorKernel prior experiment x,
    (inferInstance : IsMarkovKernel
      (ProbabilityTheory.posterior experiment prior.toMeasure)).isProbabilityMeasure x⟩

@[simp] lemma posteriorLaw_toMeasure (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] (x : β) :
    ((posteriorLaw prior experiment x : ProbabilityMeasure α) : Measure α) =
      posteriorKernel prior experiment x := rfl

/-- The posterior value of a strongly measurable state statistic is strongly measurable in the
signal. -/
lemma stronglyMeasurable_posteriorValue (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] {u : α → ℝ} (hu : StronglyMeasurable u) :
    StronglyMeasurable (posteriorValue prior experiment u) := by
  simpa [posteriorValue] using
    (MeasureTheory.StronglyMeasurable.integral_kernel
      (κ := posteriorKernel prior experiment) hu)

/-- Bridge the prior `u`-integrability through the constant kernel used to turn the measure-level
composition `posteriorKernel ∘ₘ signalLaw` into the kernel composition `∘ₖ` that Mathlib's
`Integrable.integral_comp`/`Kernel.integral_comp` expect. -/
private lemma integrable_u_comp_constSignal (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] {u : α → ℝ} (hu : Integrable u prior.toMeasure) :
    Integrable u
      ((posteriorKernel prior experiment ∘ₖ
        Kernel.const Unit (signalLaw prior experiment).toMeasure) ()) := by
  rw [show ((posteriorKernel prior experiment ∘ₖ
        Kernel.const Unit (signalLaw prior experiment).toMeasure) ()) =
      posteriorKernel prior experiment ∘ₘ (signalLaw prior experiment).toMeasure by simp,
    posteriorKernel_comp_signalLaw]
  exact hu

/-- The posterior value is integrable against the signal law whenever the state statistic is
integrable against the prior. -/
lemma integrable_posteriorValue (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] {u : α → ℝ} (hu : Integrable u prior.toMeasure) :
    Integrable (posteriorValue prior experiment u) (signalLaw prior experiment).toMeasure := by
  let constSignal : Kernel Unit β := Kernel.const Unit (signalLaw prior experiment).toMeasure
  have hiter :
      Integrable (fun x ↦ ∫ a, u a ∂posteriorKernel prior experiment x) (constSignal ()) :=
    MeasureTheory.Integrable.integral_comp
      (a := ()) (κ := constSignal) (η := posteriorKernel prior experiment) (f := u)
      (integrable_u_comp_constSignal prior experiment hu)
  simpa [posteriorValue, constSignal] using hiter

/-- **Posteriors average to the prior.** The signal-law average of the posterior value of a
prior-integrable state statistic equals its prior average (Kamenica and Gentzkow 2011). -/
lemma integral_posteriorValue (prior : ProbabilityMeasure α)
    (experiment : ContinuousExperiment α β) [StandardBorelSpace α] [Nonempty α]
    [IsMarkovKernel experiment] {u : α → ℝ} (hu : Integrable u prior.toMeasure) :
    ∫ x, posteriorValue prior experiment u x ∂(signalLaw prior experiment).toMeasure
      = ∫ a, u a ∂prior.toMeasure := by
  let signalMeasure : Measure β := (signalLaw prior experiment).toMeasure
  let constSignal : Kernel Unit β := Kernel.const Unit signalMeasure
  have hconst :
      ((posteriorKernel prior experiment ∘ₖ constSignal) ()) =
        posteriorKernel prior experiment ∘ₘ signalMeasure := by
    simp [constSignal, signalMeasure]
  calc
    ∫ x, posteriorValue prior experiment u x ∂(signalLaw prior experiment).toMeasure
      = ∫ x, ∫ a, u a ∂posteriorKernel prior experiment x ∂constSignal () := by
          simp [posteriorValue, constSignal, signalMeasure]
    _ = ∫ a, u a ∂((posteriorKernel prior experiment ∘ₖ constSignal) ()) :=
          (ProbabilityTheory.Kernel.integral_comp
            (a := ()) (κ := constSignal) (η := posteriorKernel prior experiment) (f := u)
            (integrable_u_comp_constSignal prior experiment hu)).symm
    _ = ∫ a, u a ∂prior.toMeasure := by
          rw [hconst, posteriorKernel_comp_signalLaw]

/-- If the prior is supported on a measurable set `s`, then almost every posterior law (under the
signal law) is also supported on `s`. -/
lemma ae_posteriorLaw_supportsOn_of_supportsOn (prior : ProbabilityMeasure ℝ)
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    {s : Set ℝ} (hs : MeasurableSet s)
    (hprior : Econlib.Probability.ProbDist.supportsOn prior s) :
    ∀ᵐ x ∂(signalLaw prior experiment).toMeasure,
      Econlib.Probability.ProbDist.supportsOn (posteriorLaw prior experiment x) s := by
  have hzero : prior.toMeasure sᶜ = 0 := by
    calc
      prior.toMeasure sᶜ = prior.toMeasure Set.univ - prior.toMeasure s := by
        rw [measure_compl hs (measure_ne_top prior.toMeasure s)]
      _ = 1 - 1 := by
        rw [hprior, MeasureTheory.measure_univ]
      _ = 0 := by simp
  have hlin :
      ∫⁻ x, posteriorKernel prior experiment x sᶜ ∂(signalLaw prior experiment).toMeasure = 0 := by
    have hcomp :
        (posteriorKernel prior experiment ∘ₘ
          (signalLaw prior experiment).toMeasure) sᶜ = 0 := by
      rw [posteriorKernel_comp_signalLaw]
      exact hzero
    rw [Measure.bind_apply hs.compl (Kernel.aemeasurable _)] at hcomp
    exact hcomp
  have hae0 :
      (fun x ↦ posteriorKernel prior experiment x sᶜ)
        =ᵐ[(signalLaw prior experiment).toMeasure] 0 :=
    (lintegral_eq_zero_iff ((posteriorKernel prior experiment).measurable_coe hs.compl)).1 hlin
  filter_upwards [hae0] with x hx
  unfold Econlib.Probability.ProbDist.supportsOn posteriorLaw
  have hx0 : posteriorKernel prior experiment x sᶜ = 0 := by
    simpa using hx
  calc
    posteriorKernel prior experiment x s = posteriorKernel prior experiment x Set.univ :=
      measure_of_measure_compl_eq_zero hx0
    _ = 1 := by
      rw [posteriorKernel]
      haveI : IsProbabilityMeasure (ProbabilityTheory.posterior experiment prior.toMeasure x) :=
        IsMarkovKernel.isProbabilityMeasure x
      exact measure_univ

/-- If the prior is supported on `[a, b]`, then almost every posterior mean (under the signal law)
lies in `[a, b]`. -/
lemma ae_posteriorValue_mem_Icc_of_supportsOn_Icc (prior : ProbabilityMeasure ℝ)
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment]
    {a b : ℝ} (hprior : Econlib.Probability.ProbDist.supportsOn prior (Set.Icc a b)) :
    ∀ᵐ x ∂(signalLaw prior experiment).toMeasure,
      posteriorValue prior experiment id x ∈ Set.Icc a b := by
  filter_upwards
    [ae_posteriorLaw_supportsOn_of_supportsOn prior experiment measurableSet_Icc hprior]
    with x hx
  simpa [posteriorLaw_toMeasure, posteriorValue, Econlib.Probability.ProbDist.expect] using
    (Econlib.Probability.ProbDist.expect_mem_Icc hx)

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
