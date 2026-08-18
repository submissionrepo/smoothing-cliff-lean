/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Grade Inflation: Optimal Pass/Fail Disclosure (Continuous Persuasion)

Inspired by Ostrovsky and Schwarz (2010). A school that designs a grading policy for students of
ability `θ ~ U[0, 1]`. An employer hires a student iff the expected ability given the grade is at
least `r ∈ (1/2, 1)`; the school wants every student hired. Under full transparency only the top
`1 - r` of students clear the bar, and with no grades nobody does (the prior mean is `1/2 < r`).
The school's optimal policy is **grade inflation**: A pass/fail cutoff at `2r - 1` that pools the
top `2(1 - r)` of students into a single "pass" grade whose conditional mean is exactly `r` so that
the employer is just willing to hire every passing student. The resulting hire rate is exactly
double full transparency.

## The story

* Ability `θ` is uniform on `[0, 1]`; the school commits to a grading experiment (a Markov kernel
  from abilities to grades) before observing `θ`.
* The employer is Bayesian: Seeing grade `x`, they hire iff `𝔼[θ ∣ x] ≥ r` (with the tie broken
  toward hiring) — the rational rule for payoff `θ - r` from hiring, `0` from passing
  (`hire_iff_mean_ge`).
* The school's payoff is the hire probability, regardless of ability.

## Why a cutoff at `2r - 1` is optimal

The school's value depends on the experiment only through the distribution of the posterior mean,
and every achievable posterior-mean law is dominated by the prior in the convex order
(`posteriorMeanLaw_convexOrderOnIcc` — the Rothschild–Stiglitz / Gentzkow–Kamenica reduction). A
Markov bound through the hinge `(x - (2r-1))⁺` — a Dworczak–Martini-style price function — caps the
mass any such law can put on `[r, 1]` at `2(1 - r)`. The pass/fail cutoff at `2r - 1` attains the
cap: Passing students have conditional mean `(2r-1+1)/2 = r` exactly, so the high atom sits
*precisely at* the employer's threshold, and any higher pass rate would drag the pass-grade mean
below `r`. Pooling is load-bearing: Revealing more about the top students wastes persuasion margin,
and the unique cutoff whose pass-mean is `r` is `2r - 1` (`gradeInflation_cutoff_unique`).

## What this file proves

* `hire_iff_mean_ge` — *receiver rationality*: Hiring is optimal at posterior mean `m` iff `r ≤ m`.
* `hireProbability_le` — *the universal bound*: Every grading experiment, on any signal space,
  yields hire probability at most `2(1 - r)`.
* `gradeInflation_hireProbability` — *attainment*: The cutoff experiment at `2r - 1` achieves
  `2(1 - r)`; its pass-grade mean is exactly `r` (`gradeInflation_pass_mean`) and its fail-grade
  mean is `r - 1/2` (`gradeInflation_fail_mean`).
* `hireProbability_fullDisclosure` — *transparency benchmark*: Full disclosure yields `1 - r`, so
  optimal persuasion exactly doubles it (`gradeInflation_doubles_fullDisclosure`).
* `hireProbability_noGrades` — *no-grades benchmark*: The uninformative experiment hires nobody
  (hire probability `0`), since the prior mean `1/2` lies below the threshold `r`.
* `gradeInflation_cutoff_unique` — *uniqueness*: `2r - 1` is the only interior cutoff whose
  pass-grade mean is `r`.
* `gradeInflation_convexOrder` / `gradeInflation_hasEqualMean` — *feasibility anatomy*: The optimal
  posterior-mean law is dominated by the prior in the interval convex order (pooling is a
  garbling), hence has equal mean (Bayes plausibility).

At `r = 3/4` (`section ThreeQuarters`): The cutoff is `1/2`, the two grades carry posterior means
`1/4` and `3/4` with equal weights, and the hire probability is `1/2` — against `1/4` under full
transparency and `0` with no grades.

## Main definitions and theorems

* `prior` — uniform ability prior on `[0, 1]` (`prior_density`, `prior_cdf`, `prior_mean`,
  `prior_conditionalExpect`, `prior_prob_interval` — closed forms).
* `hireProbability` — the school's value of an experiment: The mass its posterior-mean law puts on
  `[r, 1]`; equals the signal-law probability that the employer hires
  (`hireProbability_eq_prob_hire`).
* `hire_iff_mean_ge`, `hireProbability_le`, `gradeInflation_pass_mean`, `gradeInflation_fail_mean`,
  `gradeInflation_hireProbability`, `hireProbability_fullDisclosure`,
  `gradeInflation_doubles_fullDisclosure`, `gradeInflation_cutoff_unique`,
  `gradeInflation_convexOrder`, `gradeInflation_hasEqualMean`.
* `section ThreeQuarters` — the worked `r = 3/4` instance: `threeQuarters_pass_mean` (`= 3/4`),
  `threeQuarters_fail_mean` (`= 1/4`), `threeQuarters_hireProbability` (`= 1/2`),
  `threeQuarters_hireProbability_le` (`≤ 1/2`), `threeQuarters_fullDisclosure` (`= 1/4`),
  `threeQuarters_noGrades` (`= 0`).

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. "Bayesian Persuasion." *American Economic Review* 101
  (6): 2590–2615. https://doi.org/10.1257/aer.101.6.2590.
* Ostrovsky, Michael, and Michael Schwarz. 2010. “Information Disclosure and Unraveling in
  Matching Markets.” *American Economic Journal: Microeconomics* 2 (2): 34–63.
  https://doi.org/10.1257/mic.2.2.34.
* Gentzkow, Matthew, and Emir Kamenica. 2016. “A Rothschild-Stiglitz Approach to Bayesian
  Persuasion.” *American Economic Review* 106 (5): 597–601. https://doi.org/10.1257/aer.p20161049.
* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. https://doi.org/10.1086/701813.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.GradeInflation

open Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
open Econlib.Probability
open Set MeasureTheory ProbabilityTheory

/-! ## The ability prior: Closed forms -/

/-- Student ability: Uniform on `[0, 1]`. -/
def prior : ContDist := ContDist.uniform 0 1 (by norm_num)

/-- The prior is the uniform distribution on `[0, 1]` (definitional). -/
lemma prior_def : prior = ContDist.uniform 0 1 one_pos := rfl

/-- The ability density vanishes outside `[0, 1]`. -/
lemma prior_support : ∀ x ∉ Icc (0 : ℝ) 1, prior.density x = 0 :=
  fun _ hx => ContDist.uniform_density_eq_zero_of_not_mem 0 1 (by norm_num) hx

/-- On the support `[0, 1]`, the ability density is `1`. -/
lemma prior_density {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : prior.density x = 1 := by
  rw [prior_def, ContDist.uniform_density_of_mem 0 1 one_pos hx]
  norm_num

/-- The ability density is strictly positive on `[0, 1]`. -/
lemma prior_density_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < prior.density x := by
  intro x hx
  rw [prior_density hx]
  norm_num

/-- The ability density is continuous on `[0, 1]` (constant `1`). -/
lemma prior_density_cont : ContinuousOn prior.density (Icc (0 : ℝ) 1) :=
  continuousOn_const.congr fun _x hx => prior_density hx

/-- On the support `[0, 1]`, the ability CDF is the identity. -/
lemma prior_cdf {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : prior.cdf t = t := by
  rw [prior_def, ContDist.uniform_cdf_of_mem 0 1 one_pos ht]
  ring

/-- Interval probabilities of the ability prior: `P(c ≤ θ ≤ e) = e - c` inside `[0, 1]`. -/
lemma prior_prob_interval {c e : ℝ} (hc : 0 ≤ c) (hce : c ≤ e) (he : e ≤ 1) :
    prior.prob_interval c e = e - c := by
  rw [prior.prob_interval_eq_of_le hce, prior_cdf ⟨hc.trans hce, he⟩, prior_cdf ⟨hc, hce.trans he⟩]

/-- The mean ability is `1/2`. -/
lemma prior_mean : prior.toProbDist.expect id = 1 / 2 := by
  rw [← ContDist.expect_eq_probDist_expect, prior_def, ContDist.uniform_expect]
  norm_num

/-- Conditional mean ability on a subinterval `[c, e] ⊆ [0, 1]` is its midpoint. -/
lemma prior_conditionalExpect {c e : ℝ} (hc : 0 ≤ c) (hce : c < e) (he : e ≤ 1) :
    prior.conditionalExpectOrZero id (Icc c e) = (c + e) / 2 := by
  have hsub : Icc c e ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hc he
  have hmass : ∫ x in Icc c e, prior.density x = e - c := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => prior_density (hsub hx)),
      setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le hce.le]
  have hnum : ∫ x in Icc c e, prior.density x * id x = (e ^ 2 - c ^ 2) / 2 := by
    rw [setIntegral_congr_fun (g := fun x => x) measurableSet_Icc
        (fun x hx => by rw [prior_density (hsub hx), one_mul]; rfl),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hce.le, integral_id]
  have hpos : 0 < ∫ x in Icc c e, prior.density x := by rw [hmass]; linarith
  rw [prior.conditionalExpectOrZero_eq_of_pos id (Icc c e) hpos, hnum, hmass]
  have hec : e - c ≠ 0 := by linarith
  field_simp
  ring

/-- The ability prior, packaged with its support certificate for the feasibility theorem. -/
def priorSupported : SupportedProbDist (Icc (0 : ℝ) 1) :=
  ⟨prior.toProbDist,
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside prior prior_support⟩

/-! ## The employer: A threshold receiver

The employer's payoff is `θ - r` from hiring and `0` from passing. Facing a posterior belief,
the rational rule depends only on its mean: Hire iff the posterior mean weakly clears `r`. The
indifferent case `m = r` is broken toward hiring — the standard tie-breaking in persuasion, and
exactly the knife-edge the optimal policy exploits. -/

variable {r : ℝ}

/-- **Receiver rationality.** Hiring is (weakly) optimal against a posterior belief iff its mean
ability is at least the employer's threshold `r`. -/
theorem hire_iff_mean_ge (π : ProbDist ℝ) (hint : Integrable id π.toMeasure) (r : ℝ) :
    0 ≤ π.expect (fun θ => θ - r) ↔ r ≤ π.expect id := by
  have hsplit : π.expect (fun θ => θ - r) = π.expect id - r := by
    have hint' : Integrable (fun x : ℝ => x) π.toMeasure := hint
    simp only [ProbDist.expect]
    rw [integral_sub hint' (integrable_const r), integral_const, probReal_univ, one_smul]
    rfl
  rw [hsplit]
  constructor <;> intro h <;> linarith

/-! ## The school's problem -/

/-- **The school's value of a grading experiment**: The probability that the employer hires, i.e.
the mass the experiment's posterior-mean law puts on `[r, 1]`. -/
def hireProbability (r : ℝ) {β : Type*} [MeasurableSpace β]
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] : ℝ :=
  (posteriorMeanLaw prior.toProbDist experiment
      (posteriorValue prior.toProbDist experiment id)
      ((stronglyMeasurable_posteriorValue prior.toProbDist experiment
        stronglyMeasurable_id).measurable)).toMeasure.real (Ici r)

/-- The school's value is literally the signal-law probability of the hire event `{x : r ≤ 𝔼[θ∣x]}`
— the mass of grades after which the employer hires. -/
lemma hireProbability_eq_prob_hire {β : Type*} [MeasurableSpace β]
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] (r : ℝ) :
    hireProbability r experiment
      = (signalLaw prior.toProbDist experiment).toMeasure.real
          {x | r ≤ posteriorValue prior.toProbDist experiment id x} := by
  unfold hireProbability
  rw [measureReal_def, posteriorMeanLaw_toMeasure,
    Measure.map_apply ((stronglyMeasurable_posteriorValue prior.toProbDist experiment
      stronglyMeasurable_id).measurable) measurableSet_Ici, ← measureReal_def]
  rfl

/-! ## The universal upper bound

Every experiment's posterior-mean law is dominated by the prior in the interval convex order
(the Rothschild–Stiglitz feasibility constraint), so a Markov bound through the hinge price
function `(x - (2r-1))⁺` caps the hire probability at `2(1 - r)` — for any experiment on any signal
space. -/

/-- **No grading policy hires more than `2(1 - r)` of students.** The bound holds for every
experiment with an arbitrary signal space. -/
theorem hireProbability_le (hr : r ∈ Ioo (1 / 2 : ℝ) 1)
    {β : Type*} [MeasurableSpace β]
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] :
    hireProbability r experiment ≤ 2 * (1 - r) := by
  -- Feasibility: the posterior-mean law is a mean-preserving contraction of the prior.
  have hcx : Econlib.Probability.ConvexOrderOnIcc 0 1
      (posteriorMeanLaw prior.toProbDist experiment
        (posteriorValue prior.toProbDist experiment id)
        ((stronglyMeasurable_posteriorValue prior.toProbDist experiment
          stronglyMeasurable_id).measurable))
      prior.toProbDist :=
    posteriorMeanLaw_convexOrderOnIcc priorSupported experiment
  -- Markov/price-function bound through the hinge at `s = 2r - 1`.
  have hbound :=
    Econlib.Probability.mul_measureReal_Ici_le_stopLoss_of_convexOrderOnIcc hcx (2 * r - 1) r
  -- The uniform stop-loss at `2r - 1` is `2(1 - r)²`.
  have hz : (2 * r - 1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hsl : prior.toProbDist.toMeasure.stopLoss (2 * r - 1) = 2 * (1 - r) ^ 2 := by
    have huniform := ContDist.uniform_stopLoss 0 1 (by norm_num) hz
    calc prior.toProbDist.toMeasure.stopLoss (2 * r - 1)
        = (1 - (2 * r - 1)) ^ 2 / (2 * (1 - 0)) := huniform
      _ = 2 * (1 - r) ^ 2 := by ring
  rw [hsl] at hbound
  -- `(1 - r) · hireProbability ≤ 2 (1 - r)²` with `1 - r > 0` gives the bound.
  have h1r : (0 : ℝ) < 1 - r := by linarith [hr.2]
  unfold hireProbability
  nlinarith [hbound]

/-! ## The optimal policy: Pass/fail at `2r - 1` -/

/-- **The pass grade carries conditional mean exactly `r`.** The employer is just willing to hire
every passing student — the persuasion margin is fully spent. -/
theorem gradeInflation_pass_mean (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    posteriorValue prior.toProbDist (cutoffExperiment (2 * r - 1)) id true = r := by
  rw [posteriorValue_cutoffExperiment_true prior
      (show (0 : ℝ) < 2 * r - 1 by linarith [hr.1]) (show 2 * r - 1 < 1 by linarith [hr.2])
      prior_support prior_density_pos prior_density_cont,
    prior_conditionalExpect (by linarith [hr.1]) (by linarith [hr.2]) le_rfl]
  ring

/-- The fail grade carries conditional mean `r - 1/2 < r`: Failing students are not hired. -/
theorem gradeInflation_fail_mean (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    posteriorValue prior.toProbDist (cutoffExperiment (2 * r - 1)) id false = r - 1 / 2 := by
  rw [posteriorValue_cutoffExperiment_false prior
      (show (0 : ℝ) < 2 * r - 1 by linarith [hr.1]) (show 2 * r - 1 < 1 by linarith [hr.2])
      prior_support prior_density_pos prior_density_cont,
    prior_conditionalExpect le_rfl (by linarith [hr.1]) (by linarith [hr.2])]
  ring

/-- **The pass/fail cutoff at `2r - 1` attains the bound**: The hire probability is exactly
`2(1 - r)`. -/
theorem gradeInflation_hireProbability (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    hireProbability r (cutoffExperiment (2 * r - 1)) = 2 * (1 - r) := by
  have h0u : (0 : ℝ) < 2 * r - 1 := by linarith [hr.1]
  have hu1 : (2 * r - 1 : ℝ) < 1 := by linarith [hr.2]
  unfold hireProbability
  rw [posteriorMeanLaw_cutoffExperiment prior h0u hu1
    prior_support prior_density_pos prior_density_cont]
  -- The two-point law puts its `Ici r` mass exactly on the pass atom.
  have hmass : (thresholdTwoPointLaw prior 0 (2 * r - 1) 1 hu1.le).toMeasure.real (Ici r)
      = (thresholdTwoPointLaw prior 0 (2 * r - 1) 1 hu1.le).expect
          ((Ici r).indicator fun _ => 1) := by
    rw [ProbDist.expect, MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ici,
      smul_eq_mul, mul_one]
  rw [hmass, thresholdTwoPointLaw_expect prior 0 (2 * r - 1) 1 hu1.le _
    ((measurable_const.indicator measurableSet_Ici).aestronglyMeasurable)]
  -- Evaluate the indicator at the two atoms: fail mean `r - 1/2 < r`, pass mean `r ∈ Ici r`.
  rw [prior_conditionalExpect le_rfl (by linarith) hu1.le,
    prior_conditionalExpect (by linarith) hu1 le_rfl]
  rw [indicator_of_notMem (by rw [mem_Ici]; push Not; linarith : (0 + (2 * r - 1)) / 2 ∉ Ici r),
    indicator_of_mem (by rw [mem_Ici]; linarith : (2 * r - 1 + 1) / 2 ∈ Ici r)]
  rw [prior_prob_interval (by linarith) hu1.le le_rfl]
  ring

/-- **Optimal persuasion exactly doubles transparency**: Full disclosure hires the top `1 - r` of
students. -/
theorem hireProbability_fullDisclosure (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    hireProbability r (Kernel.id : Kernel ℝ ℝ) = 1 - r := by
  unfold hireProbability
  rw [posteriorMeanLaw_id]
  -- The prior's own mass on `[r, ∞)` is `1 - r`.
  have htail : prior.prob_interval r 1 = 1 - r :=
    prior_prob_interval (by linarith [hr.1]) hr.2.le le_rfl
  have hnn : (0 : ℝ) ≤ prior.prob_interval r 1 := by rw [htail]; linarith [hr.2]
  rw [measureReal_def, ContDist.toProbDist_toMeasure,
    contDist_toMeasure_Ici prior hr.2.le prior_support,
    ENNReal.toReal_ofReal hnn, htail]

/-- Grade inflation doubles the hire rate of full transparency. -/
theorem gradeInflation_doubles_fullDisclosure (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    hireProbability r (cutoffExperiment (2 * r - 1))
      = 2 * hireProbability r (Kernel.id : Kernel ℝ ℝ) := by
  rw [gradeInflation_hireProbability hr, hireProbability_fullDisclosure hr]

/-! ## The no-grades benchmark

With no grades the employer learns nothing: every posterior is the prior, whose mean ability is
`1/2 < r`, so nobody clears the bar. We model "no grades" as the uninformative experiment that
ignores ability and emits a single fixed signal; its posterior-mean law collapses to a point mass at
the prior mean `1/2`, whose `[r, 1]` mass is zero. -/

/-- **No grades**: the uninformative experiment that ignores ability and emits a single fixed
signal (a constant kernel to the one-point signal space `Unit`). -/
def noGrades : ContinuousExperiment ℝ Unit := Kernel.const ℝ (Measure.dirac ())

instance : IsMarkovKernel noGrades := by unfold noGrades; infer_instance

/-- Under no grades every posterior is the prior, so the posterior mean is the prior mean `1/2` at
the (unique) signal. -/
lemma noGrades_posteriorValue (x : Unit) :
    posteriorValue prior.toProbDist noGrades id x = 1 / 2 := by
  have hint : Integrable id prior.toProbDist.toMeasure := priorSupported.integrable_id
  have hkey := integral_posteriorValue prior.toProbDist noGrades hint
  have hmean : (∫ a, id a ∂prior.toProbDist.toMeasure) = 1 / 2 := prior_mean
  rw [hmean] at hkey
  -- The integrand is constant over the one-point signal space `Unit`.
  have hconst : (fun y => posteriorValue prior.toProbDist noGrades id y)
      = fun _ : Unit => posteriorValue prior.toProbDist noGrades id x :=
    funext fun y => by rw [Subsingleton.elim y x]
  haveI : IsProbabilityMeasure (signalLaw prior.toProbDist noGrades).toMeasure := inferInstance
  rw [hconst, integral_const, probReal_univ, one_smul] at hkey
  exact hkey

/-- **No grading policy hires anyone**: the no-grades hire probability is `0`. The posterior-mean
law is the point mass at the prior mean `1/2`, which lies strictly below the threshold `r`. -/
theorem hireProbability_noGrades (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    hireProbability r noGrades = 0 := by
  unfold hireProbability
  rw [posteriorMeanLaw_eq_dirac_of_eq_const prior.toProbDist noGrades _ _ noGrades_posteriorValue,
    ProbDist.dirac_toMeasure, measureReal_def, Measure.dirac_apply' _ measurableSet_Ici,
    Set.indicator_of_notMem (by simp only [mem_Ici, not_le]; exact hr.1)]
  simp

/-- **The cutoff is uniquely determined**: `2r - 1` is the unique interior cutoff whose pass-grade
conditional mean is exactly the employer's threshold `r`. -/
theorem gradeInflation_cutoff_unique (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    ∀ u ∈ Ioo (0 : ℝ) 1, prior.conditionalExpectOrZero id (Icc u 1) = r ↔ u = 2 * r - 1 := by
  have hmem : r ∈ Ioo (prior.toProbDist.expect id) 1 := by
    rw [prior_mean]; exact hr
  obtain ⟨u₀, ⟨hu₀, hval₀⟩, huniq⟩ :=
    existsUnique_cutoff_of_rightPosteriorMean prior (by norm_num)
      prior_support prior_density_pos prior_density_cont hmem
  have hwitness : (2 * r - 1 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
      prior.conditionalExpectOrZero id (Icc (2 * r - 1) 1) = r := by
    refine ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [prior_conditionalExpect (by linarith [hr.1]) (by linarith [hr.2]) le_rfl]
    ring
  intro u hu
  constructor
  · intro hval
    rw [huniq u ⟨hu, hval⟩, huniq (2 * r - 1) hwitness]
  · rintro rfl
    exact hwitness.2

/-! ## Feasibility anatomy

The optimal posterior-mean law is a garbling of full disclosure — dominated by the prior in the
interval convex order — and in particular Bayes-plausible (equal means). These are the relations
the upper bound runs on, exhibited on the optimal policy itself. -/

/-- The optimal two-point law is dominated by the prior in the interval convex order: Pooling
destroys information, so the prior is a mean-preserving spread of the posterior-mean law. -/
theorem gradeInflation_convexOrder (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    Econlib.Probability.ConvexOrderOnIcc 0 1
      (thresholdTwoPointLaw prior 0 (2 * r - 1) 1 (by linarith [hr.2] : (2 * r - 1 : ℝ) ≤ 1))
      prior.toProbDist :=
  thresholdTwoPointLaw_convexOrderOnIcc prior (by linarith [hr.1]) (by linarith [hr.2])
    prior_support prior_density_pos prior_density_cont

/-- Bayes plausibility of the optimal law, via the convex-order → equal-mean bridge. -/
theorem gradeInflation_hasEqualMean (hr : r ∈ Ioo (1 / 2 : ℝ) 1) :
    HasEqualMean
      (thresholdTwoPointLaw prior 0 (2 * r - 1) 1 (by linarith [hr.2] : (2 * r - 1 : ℝ) ≤ 1))
      prior.toProbDist :=
  HasEqualMean.of_convexOrderOnIcc (gradeInflation_convexOrder hr)

/-! ## The worked instance: `r = 3/4`

The cutoff is `1/2`: Pass/fail grading with posterior means `1/4` (fail) and `3/4` (pass),
equal weights. Half the students are hired — double the quarter hired under full transparency,
against zero with no grades (the prior mean `1/2` is below the bar). -/

section ThreeQuarters

/-- At `r = 3/4`, passing students have expected ability exactly `3/4`. -/
theorem threeQuarters_pass_mean :
    posteriorValue prior.toProbDist (cutoffExperiment (2 * (3 / 4) - 1)) id true = 3 / 4 :=
  gradeInflation_pass_mean (by norm_num)

/-- At `r = 3/4`, failing students have expected ability `1/4`. -/
theorem threeQuarters_fail_mean :
    posteriorValue prior.toProbDist (cutoffExperiment (2 * (3 / 4) - 1)) id false = 1 / 4 := by
  rw [gradeInflation_fail_mean (by norm_num)]
  norm_num

/-- At `r = 3/4`, half the students are hired. -/
theorem threeQuarters_hireProbability :
    hireProbability (3 / 4) (cutoffExperiment (2 * (3 / 4) - 1)) = 1 / 2 := by
  rw [gradeInflation_hireProbability (by norm_num)]
  norm_num

/-- At `r = 3/4`, no grading policy hires more than half the students. -/
theorem threeQuarters_hireProbability_le {β : Type*} [MeasurableSpace β]
    (experiment : ContinuousExperiment ℝ β) [IsMarkovKernel experiment] :
    hireProbability (3 / 4) experiment ≤ 1 / 2 := by
  have h := hireProbability_le (by norm_num : (3 / 4 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1) experiment
  linarith [h]

/-- At `r = 3/4`, full transparency hires only a quarter of the students. -/
theorem threeQuarters_fullDisclosure :
    hireProbability (3 / 4) (Kernel.id : Kernel ℝ ℝ) = 1 / 4 := by
  rw [hireProbability_fullDisclosure (by norm_num)]
  norm_num

/-- At `r = 3/4`, with no grades nobody is hired. -/
theorem threeQuarters_noGrades : hireProbability (3 / 4) noGrades = 0 :=
  hireProbability_noGrades (by norm_num : (3 / 4 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1)

end ThreeQuarters

end EconlibExamples.MechanismDesign.GradeInflation
