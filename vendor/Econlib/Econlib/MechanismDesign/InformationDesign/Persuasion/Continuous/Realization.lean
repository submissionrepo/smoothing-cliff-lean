/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.ConvexOrder
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Optimality
public import Econlib.Probability.Order.Strassen

/-!
# Continuous persuasion: Realization of feasible signals as experiments

The convex-order formulation of persuasion calls a posterior-mean law `ν` a **feasible signal**
relative to a prior `d` when `ν ≼cx[a,b] d` (`IsFeasibleSignal`). The forward direction — every
experiment's posterior-mean law is convex-order dominated by the prior — is
`posteriorMeanLaw_convexOrderOnIcc`. This file supplies the **converse realization**: Every
convex-order-dominated law is in fact the posterior-mean law of an actual Bayes-plausible
experiment. Together they upgrade the reduced-form convex-order certificates (in `Optimality` and
`Threshold/Optimality`) to honest statements over signal structures.

The realization is the **Blackwell–Strassen** bridge. From `ν ≼cx[a,b] d`, Strassen's theorem
(`exists_martingaleCoupling_of_convexOrderOnIcc`) yields a martingale coupling `π` of `(ν, d)`:
`X ∼ ν` is the posterior mean, `Y ∼ d` is the state, and `𝔼π[Y ∣ X] = X`. The realizing experiment
is the Bayes reverse `Y ↦ X`, namely the conditional kernel of `π.swap`; its signal law is `ν` and
its Bayes posterior (by uniqueness of the Bayes inverse, `ae_eq_posterior_of_compProd_eq`) agrees
with `π.condKernel`, whose fiber means are the signals themselves. Hence the posterior-mean law is
`ν`.

## Main statements

* `exists_experiment_of_isFeasibleSignal` — converse realization (hard direction): A feasible
  signal is the posterior-mean law of some Markov experiment.
* `isFeasibleSignal_of_exists_experiment` — forward direction: Any experiment's posterior-mean law
  supported on the prior's interval is feasible.
* `isFeasibleSignal_iff_exists_experiment` — the realization equivalence.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).
* Gentzkow, Matthew, and Emir Kamenica. 2016. “A Rothschild-Stiglitz Approach to Bayesian
  Persuasion.” *American Economic Review* 106 (5): 597–601. [https://doi.org/10.1257/aer.p20161049](https://doi.org/10.1257/aer.p20161049).

## Tags

persuasion, bayes plausibility, convex order, strassen, realization, mean-preserving spread
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

open Econlib.Probability

variable {a b : ℝ}

/-- **Realization of feasible signals (hard direction).** Every feasible signal `ν ≼cx[a,b] d` is
the posterior-mean law of an actual Markov experiment on the line — the Bayes reverse of the
Strassen martingale coupling of `(ν, d)`. Combined with `isFeasibleSignal_of_exists_experiment`
this shows the convex-order ("feasible signal") condition is exactly realizability by a
Bayes-plausible signal structure. -/
theorem exists_experiment_of_isFeasibleSignal {d ν : ProbDist ℝ}
    (hfeas : IsFeasibleSignal a b d ν) :
    ∃ (experiment : ContinuousExperiment ℝ ℝ) (hmark : IsMarkovKernel experiment),
      letI := hmark
      posteriorMeanLaw d experiment (posteriorValue d experiment id)
          (stronglyMeasurable_posteriorValue d experiment stronglyMeasurable_id).measurable
        = ν := by
  -- Strassen's hard direction: a martingale coupling `π` of `(ν, d)` with `𝔼π[Y ∣ X] = X`.
  obtain ⟨π, hπ⟩ := Econlib.Probability.exists_martingaleCoupling_of_convexOrderOnIcc a b hfeas
  -- The realizing experiment is the Bayes reverse `Y ↦ X`: the conditional kernel of `π.swap`.
  let experiment : Kernel ℝ ℝ := (π.toMeasure.map Prod.swap).condKernel
  haveI : IsMarkovKernel experiment := inferInstance
  refine ⟨experiment, inferInstance, ?_⟩
  -- The swapped joint law, whose fst-marginal is `d` and snd-marginal is `ν`.
  have hd_fst : (π.toMeasure.map Prod.swap).fst = d.toMeasure := by
    rw [Measure.fst_map_swap, hπ.snd_measure]
  have hν_snd : (π.toMeasure.map Prod.swap).snd = ν.toMeasure := by
    rw [Measure.snd_map_swap, hπ.fst_measure]
  -- The defining disintegration of the swapped law: `d ⊗ₘ experiment = π.swap`.
  have hdisint : d.toMeasure ⊗ₘ experiment = π.toMeasure.map Prod.swap := by
    have h := (π.toMeasure.map Prod.swap).disintegrate (π.toMeasure.map Prod.swap).condKernel
    rwa [hd_fst] at h
  -- Step A: the signal law `experiment ∘ₘ d.toMeasure` is `ν.toMeasure`.
  have hsignal : experiment ∘ₘ d.toMeasure = ν.toMeasure := by
    rw [← Measure.snd_compProd d.toMeasure experiment, hdisint, hν_snd]
  -- Step B: the Bayes posterior agrees with `π.condKernel` (a.e. under `ν`).
  have hposterior : π.toMeasure.condKernel
      =ᵐ[ν.toMeasure] posteriorKernel d experiment := by
    -- `posteriorKernel d experiment = experiment † d.toMeasure`; apply uniqueness of the posterior.
    have hcompProd : (experiment ∘ₘ d.toMeasure) ⊗ₘ π.toMeasure.condKernel
        = (d.toMeasure ⊗ₘ experiment).map Prod.swap := by
      -- LHS: rewrite the base measure to `π.fst` and disintegrate.
      rw [hsignal, ← hπ.fst_measure,
        (π.toMeasure).disintegrate π.toMeasure.condKernel]
      -- RHS: `d ⊗ₘ experiment = π.swap`, and swapping again undoes it.
      rw [hdisint, Measure.map_map measurable_swap measurable_swap]
      simp
    have hae := ProbabilityTheory.ae_eq_posterior_of_compProd_eq
      (κ := experiment) (μ := d.toMeasure) (η := π.toMeasure.condKernel) hcompProd
    rw [hsignal] at hae
    exact hae
  -- Step C: the posterior mean equals the identity `ν`-a.e.
  have hmean : ∀ᵐ x ∂ν.toMeasure, posteriorValue d experiment id x = x := by
    filter_upwards [hposterior, hπ.ae_conditional_mean_eq] with x hx_post hx_mean
    -- The posterior mean at `x` integrates `id` against `posteriorKernel d experiment x`.
    rw [posteriorValue, show (id : ℝ → ℝ) = fun y => y from rfl, ← hx_post]
    -- which equals `∫ y, y ∂(π.condKernel x) = x` by the martingale identity.
    exact hx_mean
  -- Step D: assemble the posterior-mean law equality at the `Measure` level.
  apply ProbabilityMeasure.toMeasure_injective
  rw [posteriorMeanLaw_toMeasure, signalLaw_toMeasure, hsignal,
    Measure.map_congr hmean, Measure.map_id']

/-- **Forward direction.** If some Markov experiment realizes `ν` as its posterior-mean law and the
prior is supported on `[a, b]`, then `ν` is a feasible signal. This is
`posteriorMeanLaw_convexOrderOnIcc` rephrased through `IsFeasibleSignal`. -/
theorem isFeasibleSignal_of_exists_experiment {d ν : ProbDist ℝ}
    (hd : d.supportsOn (Icc a b))
    (h : ∃ (experiment : ContinuousExperiment ℝ ℝ) (hmark : IsMarkovKernel experiment),
      letI := hmark
      posteriorMeanLaw d experiment (posteriorValue d experiment id)
          (stronglyMeasurable_posteriorValue d experiment stronglyMeasurable_id).measurable = ν) :
    IsFeasibleSignal a b d ν := by
  obtain ⟨experiment, hmark, hpm⟩ := h
  letI := hmark
  -- Bundle `d` with its support so the convex-order witness applies.
  let sp : Econlib.Probability.SupportedProbDist (Set.Icc a b) := ⟨d, hd⟩
  -- The forward convex-order bound, with the posterior-mean law rewritten to `ν` via `hpm`.
  have hcx := posteriorMeanLaw_convexOrderOnIcc sp experiment
  rw [hpm] at hcx
  exact hcx

/-- **The realization equivalence.** Relative to a prior supported on `[a, b]`, a law `ν` is a
feasible signal (a mean-preserving contraction of the prior) if and only if it is the
posterior-mean law of an actual Bayes-plausible experiment. The convex-order optimality
certificates therefore range over genuine signal structures, not merely reduced-form posterior-mean
laws. -/
theorem isFeasibleSignal_iff_exists_experiment {d ν : ProbDist ℝ}
    (hd : d.supportsOn (Icc a b)) :
    IsFeasibleSignal a b d ν ↔
    ∃ (experiment : ContinuousExperiment ℝ ℝ) (hmark : IsMarkovKernel experiment),
      letI := hmark
      posteriorMeanLaw d experiment (posteriorValue d experiment id)
          (stronglyMeasurable_posteriorValue d experiment stronglyMeasurable_id).measurable = ν :=
  ⟨fun hfeas => exists_experiment_of_isFeasibleSignal hfeas,
    fun h => isFeasibleSignal_of_exists_experiment hd h⟩

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
