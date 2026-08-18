/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.MechanismDesign.GradeInflation
import Mathlib

/-!
# Continuous persuasion: Posterior-mean convex order and threshold/cutoff witnesses

Compile-time semantic witnesses for two slices of
`Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous`, anchored on the **uniform
ability prior on `[0,1]`** and the **cutoff experiment** of
`EconlibExamples.MechanismDesign.GradeInflation` (the grade-inflation model, `r = 3/4`, cutoff
`u = 1/2`).

* **Chunk 3 — posterior-mean convex order** (`Continuous/Basic`, `Continuous/ConvexOrder`,
  `Continuous/Optimality`). The reduction of Gentzkow–Kamenica / Rothschild–Stiglitz:

  * `posteriorMeanLaw_id` / `posteriorMeanLaw_id_eq_prior` — full disclosure reproduces the prior
    (the posterior-mean law of the identity experiment **is** the prior; a normalization or sign
    bug here is silent);
  * `posteriorMeanLaw_convexOrder` / `_convexOrderOnIcc` — the **Blackwell direction**: Every
    experiment's posterior-mean law is convex-order **dominated by the prior** (the prior is the
    mean-preserving *spread*, the garbling's posterior-mean law is the *contraction* — `law ≼cx
    prior`, never the reverse);
  * `dirac_convexOrder_of_ae_posteriorValue_eq_const` — the no-information experiment collapses to
    the Dirac at the prior mean, the convex-order *least* element;
  * `posteriorKernel_comp_signalLaw`, `integral_posteriorValue`,
    `ae_posteriorValue_mem_Icc_of_supportsOn_Icc`, `expect_mono_of_supportsOn`,
    `convex_expect_posteriorMeanLaw_le_of_supportsOn_Icc` — the martingale / measurability /
    integrability glue.
* **Chunk 4 — threshold / cutoff persuasion** (`Continuous/Threshold/*`). The grade-inflation
  optimal policy:

  * `thresholdTwoPointLaw_expect`, `thresholdTwoPointLaw_expect_id_eq_prior` — the pass/fail law
    **preserves the prior mean** (Bayes plausibility, an exact equality);
  * `thresholdTwoPointLaw_convexOrder`, `_supportsOn_Icc`, `thresholdPartition_cellMass_pos`,
    `threshold_conditionalExpect_id_mem_subintervals`, `truncate_expect_eq_conditionalExpect` —
    feasibility anatomy;
  * cutoff existence: `exists_cutoff_of_probInterval_open`,
    `exists_thresholdLaw_convexOrder_of_{left,right}PosteriorMean`,
    `exists_twoPointFinMixture_of_{left,right}PosteriorMean`, `probInterval_left_strictMonoOn`;
  * the cutoff-experiment kernel surface: `signalLaw_cutoffExperiment_{true,false}`,
    `posteriorLaw_eq_canonical`, `posteriorValue_cutoffExperiment_{true,false}` (the two cells on
    the **correct sides** of the cutoff — pass mean `3/4 ∈ [u, 1]`, fail mean `1/4 ∈ [0, u]`),
    `PositiveSignal.mk{True,False}`, `contDist_toMeasure_{Ici,Iio}`;
  * optimality: `thresholdTwoPointLaw_isOptimal_excessOverThreshold` — the threshold signal is
    **optimal** (it maximizes over *every* feasible signal), not merely feasible, for the
    excess-over-threshold hinge payoff; `thresholdTwoPointLaw_expect_hinge`,
    `contDist_expect_hinge_eq`.

## Hand computation (`r = 3/4`, cutoff `u = 1/2`, uniform prior)

* Prior mean `𝔼[θ] = 1/2`.
* Fail cell `[0, 1/2]`: Conditional mean `1/4`; pass cell `[1/2, 1]`: Conditional mean `3/4`.
* Pass mass `P(θ ≥ 1/2) = 1/2`; the two-point law puts weight `(1/2, 1/2)` on `(1/4, 3/4)`,
  averaging back to `1/2` — exactly the prior mean (mean preservation).
* The pass mean `3/4` sits on the **upper** side `[1/2, 1]`, the fail mean `1/4` on the **lower**
  side `[0, 1/2]`: An `Ici`/`Iio` endpoint flip would swap them.

## What each direction reversal would break

* **Convex order points the Blackwell way.** `posteriorMeanLaw_convexOrder_witness` is
  `posterior-mean law ≼cx prior`; the reversed `prior ≼cx posterior-mean law` is false for an
  informative experiment.
* **Mean preservation is exact.** `thresholdTwoPointLaw_mean_preserved` checks
  `(1/2)·(1/4) + (1/2)·(3/4) = 1/2 = 𝔼[θ]`.
* **Cells on the right side of the cutoff.** `cutoff_cells_correct_side` evaluates the pass mean to
  `3/4` (upper) and fail mean to `1/4` (lower).
* **The threshold signal attains the optimum.** `thresholdTwoPointLaw_isOptimal_witness` is
  `IsOptimalSignal` — it beats *every* feasible signal, not just satisfies a one-sided bound.
* **Which side is positive.** `positiveSignal_true_witness` / `positiveSignal_false_witness` assert
  the constructed positive signal is specifically `true` / `false` (not merely `Nonempty`), and
  `posteriorLaw_eq_canonical_{pass,fail}` instantiate the Bayes-posterior identity on the concrete
  pass / fail signals.
* **Numeric anchors are pinned, not symbolic.** `ray_masses_eq_half` (`= 1/2` each),
  `hinge_value_eq_one_eighth` (`= 1/8`), and `cutoff_eq_half_witness` (`u = 1/2`) discharge the
  closed-form values the structural witnesses leave abstract.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.PersuasionContinuous

open MeasureTheory Set ProbabilityTheory
open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

open EconlibExamples.MechanismDesign.GradeInflation
  (prior priorSupported prior_support prior_density_pos prior_density_cont prior_mean
   prior_conditionalExpect prior_prob_interval)

/-! ## Anchoring facts on the uniform `[0,1]` prior

`prior = ContDist.uniform 0 1`; `priorSupported : SupportedProbDist (Icc 0 1)`. The density is
`1` on `[0,1]` and `0` outside; the mean is `1/2`. We reuse the closed forms from
`GradeInflation`. -/

/-- The interior cutoff `u = 1/2` (the grade-inflation cutoff at `r = 3/4`). -/
private def u : ℝ := 1 / 2

private lemma u_pos : (0 : ℝ) < u := by norm_num [u]

private lemma u_lt_one : u < 1 := by norm_num [u]

/-- The prior mean is `1/2`, expressed via the `ProbDist.expect id` the threshold API uses. -/
private lemma prior_expect_id : prior.toProbDist.expect id = 1 / 2 := prior_mean

/-! ## Chunk 3: Posterior-mean convex order

We exercise the Blackwell reduction on the uniform prior, with the cutoff experiment as the
concrete informative experiment and the constant (no-information) experiment as the degenerate
case. -/

/-- **Full disclosure reproduces the prior** (`posteriorMeanLaw_id`): The posterior-mean law of the
identity experiment is the prior itself — the posterior at signal `x` is `δ_x`, so the posterior
mean is the state. A normalization bug here is silent. -/
theorem posteriorMeanLaw_id_witness :
    posteriorMeanLaw prior.toProbDist (Kernel.id : Kernel ℝ ℝ)
        (posteriorValue prior.toProbDist Kernel.id id)
        ((stronglyMeasurable_posteriorValue prior.toProbDist Kernel.id
          stronglyMeasurable_id).measurable)
      = prior.toProbDist :=
  posteriorMeanLaw_id prior.toProbDist

/-- **Full disclosure reproduces the prior** (`posteriorMeanLaw_id_eq_prior`): The `Kernel.id`
posterior-mean law equals the prior, stated with the experiment typed as a
`ContinuousExperiment`. -/
theorem posteriorMeanLaw_id_eq_prior_witness :
    posteriorMeanLaw prior.toProbDist (Kernel.id : ContinuousExperiment ℝ ℝ)
        (posteriorValue prior.toProbDist (Kernel.id : ContinuousExperiment ℝ ℝ) id)
        (stronglyMeasurable_posteriorValue prior.toProbDist
          (Kernel.id : ContinuousExperiment ℝ ℝ) stronglyMeasurable_id).measurable
      = prior.toProbDist :=
  posteriorMeanLaw_id_eq_prior prior.toProbDist

/-- **The Blackwell direction** (`posteriorMeanLaw_convexOrderOnIcc`): Every experiment's
posterior-mean law is convex-order-dominated by the prior on `[0,1]` (the prior is the
mean-preserving spread, the garbling is the contraction). Witnessed on the cutoff experiment. The
**reversed** order `prior ≼cx posterior-mean law` would be false for an informative experiment. -/
theorem posteriorMeanLaw_convexOrderOnIcc_witness :
    ConvexOrderOnIcc 0 1
      (posteriorMeanLaw priorSupported.law (cutoffExperiment u)
        (posteriorValue priorSupported.law (cutoffExperiment u) id)
        (stronglyMeasurable_posteriorValue priorSupported.law (cutoffExperiment u)
          stronglyMeasurable_id).measurable)
      priorSupported.law :=
  posteriorMeanLaw_convexOrderOnIcc priorSupported (cutoffExperiment u)

/-- **The Blackwell direction, unit-interval form** (`posteriorMeanLaw_convexOrder`): The
posterior-mean law `≼cx` the prior. -/
theorem posteriorMeanLaw_convexOrder_witness :
    ConvexOrder
      (posteriorMeanLaw priorSupported.law (cutoffExperiment u)
        (posteriorValue priorSupported.law (cutoffExperiment u) id)
        (stronglyMeasurable_posteriorValue priorSupported.law (cutoffExperiment u)
          stronglyMeasurable_id).measurable)
      priorSupported.law :=
  posteriorMeanLaw_convexOrder priorSupported (cutoffExperiment u)

/-- **Convex test functions decrease under the posterior-mean law**
(`convex_expect_posteriorMeanLaw_le_of_supportsOn_Icc`): For a convex continuous `φ`, the
posterior-mean law's `φ`-expectation is at most the prior's — the integral form of the convex
order. Witnessed on `φ = x ↦ x²`. -/
theorem convex_expect_posteriorMeanLaw_le_witness :
    ProbDist.expect
        (posteriorMeanLaw prior.toProbDist (cutoffExperiment u)
          (posteriorValue prior.toProbDist (cutoffExperiment u) id)
          (stronglyMeasurable_posteriorValue prior.toProbDist (cutoffExperiment u)
            stronglyMeasurable_id).measurable)
        (fun x => x ^ 2)
      ≤ ProbDist.expect prior.toProbDist (fun x => x ^ 2) := by
  have hsupp : prior.toProbDist.supportsOn (Icc (0 : ℝ) 1) := priorSupported.supported
  exact convex_expect_posteriorMeanLaw_le_of_supportsOn_Icc prior.toProbDist (cutoffExperiment u)
    hsupp ((convexOn_pow 2).subset Icc_subset_Ici_self (convex_Icc 0 1)) (by fun_prop)

/-- **No information collapses to the prior-mean Dirac**
(`dirac_convexOrder_of_ae_posteriorValue_eq_const`): When the posterior value is a.e. the constant
prior mean `1/2`, the Dirac at `1/2` is convex-order **below** the prior — the least element. We
use the one-point (no-information) experiment, whose unique posterior is the prior. -/
theorem dirac_convexOrder_of_ae_const_witness :
    ConvexOrder (ProbDist.dirac (1 / 2))
      priorSupported.law := by
  -- The no-information experiment emits a single signal; its posterior is the prior, mean `1/2`.
  refine dirac_convexOrder_of_ae_posteriorValue_eq_const priorSupported
    (Kernel.const ℝ (Measure.dirac ())) ?_
  -- On the one-point signal space `Unit`, the posterior value is constantly the prior mean.
  filter_upwards with x
  have hint : Integrable id priorSupported.law.toMeasure := priorSupported.integrable_id
  have hkey := integral_posteriorValue priorSupported.law (Kernel.const ℝ (Measure.dirac ())) hint
  -- The integrand `posteriorValue ... id` is constant on the `Unit` signal space.
  have hconst :
      (fun y => posteriorValue priorSupported.law (Kernel.const ℝ (Measure.dirac ())) id y)
      = fun _ : Unit =>
          posteriorValue priorSupported.law (Kernel.const ℝ (Measure.dirac ())) id x :=
    funext fun y => by rw [Subsingleton.elim y x]
  haveI : IsProbabilityMeasure
      (signalLaw priorSupported.law (Kernel.const ℝ (Measure.dirac ()))).toMeasure := inferInstance
  rw [hconst, integral_const, probReal_univ, one_smul] at hkey
  rw [hkey]
  change (∫ a, id a ∂priorSupported.law.toMeasure) = 1 / 2
  exact prior_mean

/-- **The posterior kernel composed with the signal law is the prior**
(`posteriorKernel_comp_signalLaw`): The martingale / law-of-total-probability identity, witnessed
on the cutoff experiment. -/
theorem posteriorKernel_comp_signalLaw_witness :
    posteriorKernel prior.toProbDist (cutoffExperiment u)
        ∘ₘ (signalLaw prior.toProbDist (cutoffExperiment u)).toMeasure
      = prior.toProbDist.toMeasure :=
  posteriorKernel_comp_signalLaw prior.toProbDist (cutoffExperiment u)

/-- **The posterior value averages to the prior mean** (`integral_posteriorValue`): Integrating the
posterior mean against the signal law recovers `∫ id dprior = 1/2`. Bayes plausibility in integral
form. -/
theorem integral_posteriorValue_witness :
    ∫ x, posteriorValue prior.toProbDist (cutoffExperiment u) id x
        ∂(signalLaw prior.toProbDist (cutoffExperiment u)).toMeasure
      = ∫ a, id a ∂prior.toProbDist.toMeasure :=
  integral_posteriorValue prior.toProbDist (cutoffExperiment u) priorSupported.integrable_id

/-- **Posterior values stay in `[0,1]`** (`ae_posteriorValue_mem_Icc_of_supportsOn_Icc`): A.e. the
posterior mean lies in the support `[0,1]` — the posterior never leaves the prior's range. -/
theorem ae_posteriorValue_mem_Icc_witness :
    ∀ᵐ x ∂(signalLaw prior.toProbDist (cutoffExperiment u)).toMeasure,
      posteriorValue prior.toProbDist (cutoffExperiment u) id x ∈ Icc (0 : ℝ) 1 :=
  ae_posteriorValue_mem_Icc_of_supportsOn_Icc prior.toProbDist (cutoffExperiment u)
    priorSupported.supported

/-! ## Chunk 4: Threshold / cutoff persuasion (grade inflation)

The cutoff `u = 1/2` partitions `[0,1]` into the fail cell `[0, 1/2]` (conditional mean `1/4`)
and the pass cell `[1/2, 1]` (conditional mean `3/4`). The two-point law puts weight `1/2` on
each. -/

/-- The fail cell's conditional mean is `1/4` (the midpoint of `[0, 1/2]`). -/
private lemma fail_mean : prior.conditionalExpectOrZero id (Icc 0 u) = 1 / 4 := by
  rw [prior_conditionalExpect le_rfl (by norm_num [u]) (by norm_num [u])]; norm_num [u]

/-- The pass cell's conditional mean is `3/4` (the midpoint of `[1/2, 1]`). -/
private lemma pass_mean : prior.conditionalExpectOrZero id (Icc u 1) = 3 / 4 := by
  rw [prior_conditionalExpect (by norm_num [u]) (by norm_num [u]) le_rfl]; norm_num [u]

/-- **The pass cell sits on the upper side, the fail cell on the lower side**
(`posteriorValue_cutoffExperiment_{true,false}`): The pass (`true`) posterior mean is
`3/4 ∈ [u, 1]` and the fail (`false`) posterior mean is `1/4 ∈ [0, u]`. An `Ici`/`Iio` endpoint
flip would swap them. -/
theorem cutoff_cells_correct_side :
    posteriorValue prior.toProbDist (cutoffExperiment u) id true = 3 / 4 ∧
    posteriorValue prior.toProbDist (cutoffExperiment u) id false = 1 / 4 := by
  refine ⟨?_, ?_⟩
  · rw [posteriorValue_cutoffExperiment_true prior u_pos u_lt_one prior_support prior_density_pos
      prior_density_cont, pass_mean]
  · rw [posteriorValue_cutoffExperiment_false prior u_pos u_lt_one prior_support prior_density_pos
      prior_density_cont, fail_mean]

/-- **The pass mass is the prior mass above the cutoff** (`signalLaw_cutoffExperiment_true`):
`P(signal = pass) = P(θ ≥ 1/2)`. -/
theorem signalLaw_cutoffExperiment_true_witness :
    (signalLaw prior.toProbDist (cutoffExperiment u)).toMeasure {true}
      = prior.toProbDist.toMeasure (Ici u) :=
  signalLaw_cutoffExperiment_true prior.toProbDist u

/-- **The fail mass is the prior mass below the cutoff** (`signalLaw_cutoffExperiment_false`):
`P(signal = fail) = P(θ < 1/2)`. -/
theorem signalLaw_cutoffExperiment_false_witness :
    (signalLaw prior.toProbDist (cutoffExperiment u)).toMeasure {false}
      = prior.toProbDist.toMeasure (Iio u) :=
  signalLaw_cutoffExperiment_false prior.toProbDist u

/-- The prior ray masses on `[0,1]` (`contDist_toMeasure_{Ici,Iio}`): The mass above `1/2` is
`prob_interval (1/2) 1 = 1/2` and the mass below is `prob_interval 0 (1/2) = 1/2`. -/
theorem contDist_toMeasure_Ici_witness :
    prior.toMeasure (Ici u) = ENNReal.ofReal (prior.prob_interval u 1) :=
  contDist_toMeasure_Ici prior u_lt_one.le prior_support

theorem contDist_toMeasure_Iio_witness :
    prior.toMeasure (Iio u) = ENNReal.ofReal (prior.prob_interval 0 u) :=
  contDist_toMeasure_Iio prior u_pos.le u_lt_one.le prior_support

/-- **The ray masses are each exactly `1/2`** (numeric anchor): `P(θ ≥ 1/2) = P(θ < 1/2) =
1/2`, i.e. both `= ENNReal.ofReal (1/2)`. The previous witnesses left the masses as the symbolic
`prob_interval`; here they are pinned to `1/2`. -/
theorem ray_masses_eq_half :
    prior.toMeasure (Ici u) = ENNReal.ofReal (1 / 2) ∧
    prior.toMeasure (Iio u) = ENNReal.ofReal (1 / 2) := by
  refine ⟨?_, ?_⟩
  · rw [contDist_toMeasure_Ici prior u_lt_one.le prior_support,
      prior_prob_interval u_pos.le u_lt_one.le le_rfl]; norm_num [u]
  · rw [contDist_toMeasure_Iio prior u_pos.le u_lt_one.le prior_support,
      prior_prob_interval le_rfl u_pos.le u_lt_one.le]; norm_num [u]

/-- The pass side has positive prior mass (`P(θ ≥ 1/2) = 1/2 ≠ 0`). -/
private lemma pass_mass_ne : prior.toProbDist.toMeasure (Ici u) ≠ 0 := by
  rw [ContDist.toProbDist_toMeasure, contDist_toMeasure_Ici prior u_lt_one.le prior_support,
    prior_prob_interval u_pos.le u_lt_one.le le_rfl]
  norm_num [u]

/-- The fail side has positive prior mass (`P(θ < 1/2) = 1/2 ≠ 0`). -/
private lemma fail_mass_ne : prior.toProbDist.toMeasure (Iio u) ≠ 0 := by
  rw [ContDist.toProbDist_toMeasure,
    contDist_toMeasure_Iio prior u_pos.le u_lt_one.le prior_support,
    prior_prob_interval le_rfl u_pos.le u_lt_one.le]
  norm_num [u]

/-- **The PASS signal is positive** (`PositiveSignal.mkTrue`): there is a positive signal whose
value is specifically `true` — the prior puts positive mass above the cutoff. (The previous witness
asserted `Nonempty`, erasing *which* side was constructed.) -/
theorem positiveSignal_true_witness :
    ∃ s : PositiveSignal prior.toProbDist u, s.val = true :=
  ⟨PositiveSignal.mkTrue prior.toProbDist u pass_mass_ne, rfl⟩

/-- **The FAIL signal is positive** (`PositiveSignal.mkFalse`): there is a positive signal whose
value is specifically `false`. -/
theorem positiveSignal_false_witness :
    ∃ s : PositiveSignal prior.toProbDist u, s.val = false :=
  ⟨PositiveSignal.mkFalse prior.toProbDist u fail_mass_ne, rfl⟩

/-- **The Bayes posterior coincides with the cutoff-geometry posterior**
(`posteriorLaw_eq_canonical`) for an arbitrary positive signal `s`. -/
theorem posteriorLaw_eq_canonical_witness (s : PositiveSignal prior.toProbDist u) :
    (posteriorLaw prior.toProbDist (cutoffExperiment u) s.val).toMeasure
      = canonicalPosterior prior.toProbDist u s.val :=
  posteriorLaw_eq_canonical prior.toProbDist u s

/-- **At the concrete PASS signal** the Bayes posterior is the canonical pass posterior (prior
conditioned on `[1/2, ∞)`). Instantiated on `PositiveSignal.mkTrue`, not an assumed subtype
element. -/
theorem posteriorLaw_eq_canonical_pass :
    (posteriorLaw prior.toProbDist (cutoffExperiment u) true).toMeasure
      = canonicalPosterior prior.toProbDist u true :=
  posteriorLaw_eq_canonical prior.toProbDist u
    (PositiveSignal.mkTrue prior.toProbDist u pass_mass_ne)

/-- **At the concrete FAIL signal** the Bayes posterior is the canonical fail posterior (prior
conditioned on `(-∞, 1/2)`). Instantiated on `PositiveSignal.mkFalse`. -/
theorem posteriorLaw_eq_canonical_fail :
    (posteriorLaw prior.toProbDist (cutoffExperiment u) false).toMeasure
      = canonicalPosterior prior.toProbDist u false :=
  posteriorLaw_eq_canonical prior.toProbDist u
    (PositiveSignal.mkFalse prior.toProbDist u fail_mass_ne)

/-- **The two-point law's expectation is a Bernoulli average over the two cell means**
(`thresholdTwoPointLaw_expect`): For `φ = id`, the value is `(1/2)·(1/4) + (1/2)·(3/4)`. -/
theorem thresholdTwoPointLaw_expect_witness :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).expect id
      = (1 - prior.prob_interval u 1) * prior.conditionalExpectOrZero id (Icc 0 u)
        + prior.prob_interval u 1 * prior.conditionalExpectOrZero id (Icc u 1) :=
  thresholdTwoPointLaw_expect prior 0 u 1 u_lt_one.le id aestronglyMeasurable_id

/-- **The two-point law preserves the prior mean** (`thresholdTwoPointLaw_expect_id_eq_prior`):
`𝔼[two-point law] = 𝔼[θ] = 1/2`. The exact Bayes-plausibility equality. -/
theorem thresholdTwoPointLaw_expect_id_eq_prior_witness :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).expect id = prior.toProbDist.expect id :=
  thresholdTwoPointLaw_expect_id_eq_prior prior u_pos u_lt_one prior_support prior_density_cont

/-- The pass mass is `P(θ ≥ 1/2) = 1/2`. -/
private lemma pass_prob : prior.prob_interval u 1 = 1 / 2 := by
  rw [prior_prob_interval u_pos.le u_lt_one.le le_rfl]; norm_num [u]

/-- **Mean preservation, anchored numerically from the cells**: the two-point expectation expands
*explicitly* to the Bernoulli average `(1 − 1/2)·(1/4) + (1/2)·(3/4) = 1/2`, built from the pass
mass `1/2` and the two cell means `1/4`, `3/4` — not by rewriting through the library's
mean-preservation theorem. A weight or cell-mean error is caught. -/
theorem thresholdTwoPointLaw_mean_preserved :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).expect id = 1 / 2 := by
  rw [thresholdTwoPointLaw_expect_witness, fail_mean, pass_mean, pass_prob]
  norm_num

/-- **The two-point law is a mean-preserving CONTRACTION of the prior**
(`thresholdTwoPointLaw_convexOrder`): the formal statement `two-point law ≼cx prior` means the prior
is the mean-preserving *spread* and the (pooled) two-point law is the convex-order-dominated
*contraction* — pooling destroys information. (The economic interpretation is the Blackwell
direction: garbling reduces convex-order; do not read this as "the two-point law spreads the
prior".) -/
theorem thresholdTwoPointLaw_convexOrder_witness :
    thresholdTwoPointLaw prior 0 u 1 u_lt_one.le ≼cx prior.toProbDist :=
  thresholdTwoPointLaw_convexOrder prior u_pos u_lt_one prior_support prior_density_pos
    prior_density_cont

/-- **The two-point law is supported on `[0,1]`** (`thresholdTwoPointLaw_supportsOn_Icc`): Both
posterior means stay inside the prior's support. -/
theorem thresholdTwoPointLaw_supportsOn_Icc_witness :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).supportsOn (Icc (0 : ℝ) 1) :=
  thresholdTwoPointLaw_supportsOn_Icc prior u_pos u_lt_one prior_support prior_density_pos
    prior_density_cont

/-- **Both cells carry positive mass** (`thresholdPartition_cellMass_pos`): The fail and pass cells
both have positive prior mass. -/
theorem thresholdPartition_cellMass_pos_witness :
    ∀ j, 0 < cellMass prior (thresholdPartition u_pos u_lt_one) j :=
  thresholdPartition_cellMass_pos prior u_pos u_lt_one prior_density_pos prior_density_cont

/-- **The conditional means lie in their subintervals**
(`threshold_conditionalExpect_id_mem_subintervals`): `𝔼[θ | θ ≤ 1/2] ∈ [0, 1/2]` and
`𝔼[θ | θ ≥ 1/2] ∈ [1/2, 1]`. -/
theorem threshold_conditionalExpect_id_mem_subintervals_witness :
    prior.conditionalExpectOrZero id (Icc 0 u) ∈ Icc 0 u ∧
      prior.conditionalExpectOrZero id (Icc u 1) ∈ Icc u 1 :=
  threshold_conditionalExpect_id_mem_subintervals prior u_pos u_lt_one prior_density_pos
    prior_density_cont

/-- The prior cell mass below the cutoff is positive (`P(0 ≤ θ ≤ 1/2) = 1/2 > 0`). -/
private lemma fail_prob_pos : 0 < prior.prob_interval 0 u := by
  rw [prior_prob_interval le_rfl u_pos.le u_lt_one.le]; norm_num [u]

/-- The set-integral gate for `conditionalExpect` on `[0, 1/2]`: `∫ density > 0`. -/
private lemma fail_setIntegral_pos : 0 < ∫ x in Icc 0 u, prior.density x := by
  have h := fail_prob_pos
  rwa [Econlib.Probability.ContDist.prob_interval] at h

/-- **The truncated expectation is the conditional expectation**
(`truncate_expect_eq_conditionalExpect`): Truncating the prior to `[0, 1/2]` and taking the mean
gives `𝔼[θ | θ ∈ [0, 1/2]]`. -/
theorem truncate_expect_eq_conditionalExpect_witness :
    (prior.truncate 0 u u_pos fail_prob_pos).expect id
      = prior.conditionalExpect id (Icc 0 u) fail_setIntegral_pos :=
  truncate_expect_eq_conditionalExpect prior 0 u u_pos fail_prob_pos id
    (((prior_density_cont.mono (Icc_subset_Icc le_rfl u_lt_one.le)).mul
      continuousOn_id).integrableOn_Icc)

/-! ### Cutoff existence on the uniform prior -/

/-- **An interior cutoff exists for any target mass** (`exists_cutoff_of_probInterval_open`): For
the mass `1/2`, there is a cutoff `u ∈ (0, 1)` with `P(0 ≤ θ ≤ u) = 1/2`. -/
theorem exists_cutoff_of_probInterval_open_witness :
    ∃ u ∈ Ioo (0 : ℝ) 1, prior.prob_interval 0 u = 1 / 2 := by
  refine exists_cutoff_of_probInterval_open prior (by norm_num) (1 / 2) ?_
  rw [prior_prob_interval le_rfl (by norm_num) le_rfl]
  norm_num

/-- **The explicit cutoff is `u = 1/2`** (the concrete grade-inflation cutoff): `1/2 ∈ (0,1)` and
`P(0 ≤ θ ≤ 1/2) = 1/2` exactly. This pins the intended witness the existential above left abstract
(the strict monotonicity of `v ↦ P(0 ≤ θ ≤ v)`, `probInterval_left_strictMonoOn_witness`, makes it
unique). -/
theorem cutoff_eq_half_witness :
    (u ∈ Ioo (0 : ℝ) 1) ∧ prior.prob_interval 0 u = 1 / 2 := by
  refine ⟨⟨u_pos, u_lt_one⟩, ?_⟩
  rw [prior_prob_interval le_rfl u_pos.le u_lt_one.le]; norm_num [u]

/-- **`P(0 ≤ θ ≤ u)` is strictly increasing in the cutoff** (`probInterval_left_strictMonoOn`): The
cutoff mass is a strictly monotone function of `u` on `[0,1]`. -/
theorem probInterval_left_strictMonoOn_witness :
    StrictMonoOn (fun v => prior.prob_interval 0 v) (Icc (0 : ℝ) 1) :=
  probInterval_left_strictMonoOn prior (by norm_num) prior_density_pos prior_density_cont

/-- **A convex-order threshold law exists for any admissible right posterior mean**
(`exists_thresholdLaw_convexOrder_of_rightPosteriorMean`): For the pass mean `3/4 ∈ (1/2, 1)`, the
threshold two-point law at the matching cutoff is convex-order *dominated by* (a mean-preserving
contraction of) the prior — `thresholdTwoPointLaw ≼cx prior`. -/
theorem exists_thresholdLaw_convexOrder_of_rightPosteriorMean_witness :
    ∃ v, ∃ hv : v ∈ Ioo (0 : ℝ) 1,
      prior.conditionalExpectOrZero id (Icc v 1) = 3 / 4 ∧
      ConvexOrderOnIcc 0 1 (thresholdTwoPointLaw prior 0 v 1 hv.2.le) prior.toProbDist := by
  refine exists_thresholdLaw_convexOrder_of_rightPosteriorMean prior (by norm_num) prior_support
    prior_density_pos prior_density_cont ?_
  rw [prior_expect_id]; constructor <;> norm_num

/-- **A convex-order threshold law exists for any admissible left posterior mean**
(`exists_thresholdLaw_convexOrder_of_leftPosteriorMean`): For the fail mean `1/4 ∈ (0, 1/2)`. -/
theorem exists_thresholdLaw_convexOrder_of_leftPosteriorMean_witness :
    ∃ v, ∃ hv : v ∈ Ioo (0 : ℝ) 1,
      prior.conditionalExpectOrZero id (Icc 0 v) = 1 / 4 ∧
      ConvexOrderOnIcc 0 1 (thresholdTwoPointLaw prior 0 v 1 hv.2.le) prior.toProbDist := by
  refine exists_thresholdLaw_convexOrder_of_leftPosteriorMean prior (by norm_num) prior_support
    prior_density_pos prior_density_cont ?_
  rw [prior_expect_id]; constructor <;> norm_num

/-- **A two-point finite mixture exists for the right posterior mean**
(`exists_twoPointFinMixture_of_rightPosteriorMean`): The threshold law is a Bernoulli mixture of
Diracs at the two cell means, averaging to the prior mean. -/
theorem exists_twoPointFinMixture_of_rightPosteriorMean_witness :
    ∃ v, ∃ hv : v ∈ Ioo (0 : ℝ) 1, ∃ mL ∈ Ioo (0 : ℝ) (1 / 2),
      prior.prob_interval 0 v * mL + prior.prob_interval v 1 * (3 / 4) = 1 / 2 ∧
      thresholdTwoPointLaw prior 0 v 1 hv.2.le =
        ProbDist.finMixture
          (FinDist.bernoulli (prior.prob_interval v 1)
            (prior.prob_interval_nonneg v 1) (prior.prob_interval_le_one v 1))
          (fun i : Fin 2 => ProbDist.dirac (if i = 0 then mL else 3 / 4)) := by
  have h := exists_twoPointFinMixture_of_rightPosteriorMean prior (a := 0) (b := 1) (mR := 3 / 4)
    (by norm_num) prior_support prior_density_pos prior_density_cont
    (by rw [prior_expect_id]; constructor <;> norm_num)
  obtain ⟨v, hv, mL, hmL, hmean, hmix⟩ := h
  rw [prior_expect_id] at hmL hmean
  exact ⟨v, hv, mL, hmL, hmean, hmix⟩

/-- **A two-point finite mixture exists for the left posterior mean**
(`exists_twoPointFinMixture_of_leftPosteriorMean`): The dual of the previous witness, with the fail
mean `1/4` fixed. -/
theorem exists_twoPointFinMixture_of_leftPosteriorMean_witness :
    ∃ v, ∃ hv : v ∈ Ioo (0 : ℝ) 1, ∃ mR ∈ Ioo (1 / 2 : ℝ) 1,
      prior.prob_interval 0 v * (1 / 4) + prior.prob_interval v 1 * mR = 1 / 2 ∧
      thresholdTwoPointLaw prior 0 v 1 hv.2.le =
        ProbDist.finMixture
          (FinDist.bernoulli (prior.prob_interval v 1)
            (prior.prob_interval_nonneg v 1) (prior.prob_interval_le_one v 1))
          (fun i : Fin 2 => ProbDist.dirac (if i = 0 then 1 / 4 else mR)) := by
  have h := exists_twoPointFinMixture_of_leftPosteriorMean prior (a := 0) (b := 1) (mL := 1 / 4)
    (by norm_num) prior_support prior_density_pos prior_density_cont
    (by rw [prior_expect_id]; constructor <;> norm_num)
  obtain ⟨v, hv, mR, hmR, hmean, hmix⟩ := h
  rw [prior_expect_id] at hmR hmean
  exact ⟨v, hv, mR, hmR, hmean, hmix⟩

/-! ### Optimality: The threshold signal is optimal, not just feasible -/

/-- **The two-point law's hinge value is `P(θ ≥ u)·(𝔼[θ | θ ≥ u] − u)`**
(`thresholdTwoPointLaw_expect_hinge`): For the excess-over-threshold payoff `max (m − u) 0`, only
the pass cell contributes. Here `(1/2)·(3/4 − 1/2) = 1/8`. -/
theorem thresholdTwoPointLaw_expect_hinge_witness :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).expect (fun m => max (m - u) 0)
      = prior.prob_interval u 1 * (prior.conditionalExpectOrZero id (Icc u 1) - u) :=
  thresholdTwoPointLaw_expect_hinge prior u_pos u_lt_one prior_density_pos prior_density_cont

/-- **The prior's hinge value equals the two-point law's** (`contDist_expect_hinge_eq`): The
tightness identity behind optimality — only the mass above the cutoff contributes. -/
theorem contDist_expect_hinge_eq_witness :
    prior.toProbDist.expect (fun m => max (m - u) 0)
      = prior.prob_interval u 1 * (prior.conditionalExpectOrZero id (Icc u 1) - u) :=
  contDist_expect_hinge_eq prior u_pos u_lt_one prior_support prior_density_pos prior_density_cont

/-- **The hinge value is exactly `1/8`** (numeric anchor): both the two-point law's and the prior's
excess-over-threshold expectations equal `P(θ ≥ 1/2)·(𝔼[θ | θ ≥ 1/2] − 1/2) = (1/2)·(3/4 − 1/2) =
1/8`. The witnesses above left this as the symbolic `prob_interval·(condExpect − u)`. -/
theorem hinge_value_eq_one_eighth :
    (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le).expect (fun m => max (m - u) 0) = 1 / 8 ∧
    prior.toProbDist.expect (fun m => max (m - u) 0) = 1 / 8 := by
  refine ⟨?_, ?_⟩
  · rw [thresholdTwoPointLaw_expect_hinge_witness, pass_mean, pass_prob]; norm_num [u]
  · rw [contDist_expect_hinge_eq_witness, pass_mean, pass_prob]; norm_num [u]

/-- **The threshold signal is OPTIMAL** (`thresholdTwoPointLaw_isOptimal_excessOverThreshold`): For
the excess-over-threshold (hinge) payoff `max (m − u) 0`, the threshold two-point law maximizes
expected payoff over **every** feasible (Bayes-plausible) signal — not merely satisfies a one-sided
bound. This is `IsOptimalSignal`, the strong optimality claim. -/
theorem thresholdTwoPointLaw_isOptimal_witness :
    IsOptimalSignal 0 1 prior.toProbDist (fun m => max (m - u) 0)
      (thresholdTwoPointLaw prior 0 u 1 u_lt_one.le) :=
  thresholdTwoPointLaw_isOptimal_excessOverThreshold prior u_pos u_lt_one prior_support
    prior_density_pos prior_density_cont

/-- **The optimal threshold signal is realized by an actual experiment**
(`exists_experiment_of_isFeasibleSignal`): the Blackwell–Strassen converse turns the reduced-form
feasibility of the optimal threshold two-point law into an honest Markov experiment whose
posterior-mean law it is — witnessing that the optimality certificate ranges over genuine signal
structures, not merely convex-order posterior-mean laws. -/
theorem thresholdTwoPointLaw_realizable_witness :
    ∃ (experiment : ContinuousExperiment ℝ ℝ) (hmark : IsMarkovKernel experiment),
      letI := hmark
      posteriorMeanLaw prior.toProbDist experiment (posteriorValue prior.toProbDist experiment id)
          (stronglyMeasurable_posteriorValue prior.toProbDist experiment
            stronglyMeasurable_id).measurable
        = thresholdTwoPointLaw prior 0 u 1 u_lt_one.le :=
  exists_experiment_of_isFeasibleSignal thresholdTwoPointLaw_isOptimal_witness.1

/-- **Support-aware monotonicity of expectation** (`expect_mono_of_supportsOn`): On the prior
(supported on `[0,1]`), `m ↦ max (m − u) 0 ≤ m ↦ m` pointwise on `[0,1]`, so the hinge expectation
is at most the mean. Catches a reversed hinge sign. -/
theorem expect_mono_of_supportsOn_witness :
    prior.toProbDist.expect (fun m => max (m - u) 0) ≤ prior.toProbDist.expect id := by
  refine expect_mono_of_supportsOn priorSupported.supported (by fun_prop) continuousOn_id ?_
  intro x hx
  simp only [id_eq]
  rcases le_or_gt (x - u) 0 with h | h
  · rw [max_eq_right h]; linarith [hx.1]
  · rw [max_eq_left h.le]; linarith [u_pos]

end EconlibTest.MechanismDesign.PersuasionContinuous

end
