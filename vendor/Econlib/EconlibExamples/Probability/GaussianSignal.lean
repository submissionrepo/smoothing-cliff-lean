/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Gaussian Signals: MLRP ⇒ FOSD ⇒ Comparative Statics, Posterior Odds & Conjugate Updating

This capstone example runs the central comparative-statics engine of information economics end to
end on a continuum family. A state (or "type") `θ` is observed through a normally
distributed signal `X ~ N(θ, v)` with fixed variance. We show:

1. The likelihood family `f(x ∣ θ)` has the **monotone likelihood ratio property** (MLRP) — and in
   fact the *strict* MLRP;
2. Hence a higher type `θ` induces a signal distribution that **first-order stochastically
   dominates** the lower one;
3. Hence the expectation of any monotone statistic of the signal is **increasing in the type `θ`**
   (strictly monotone statistics respond strictly); and, reading the statistic as the agent's
   *optimal action* in an explicit supermodular decision problem, a higher type leads the agent to
   take a **weakly higher action** — the monotone comparative statics, not just a relabeled
   integral;
4. Placing a Gaussian prior `θ ~ N(μ₀, v₀)` on the state and inverting the likelihood by Bayes'
   rule, the **posterior odds on higher states are increasing in the observed signal `x`** — the
   qualitative Bayesian "a higher signal shifts belief upward" conclusion that underpins screening
   and auctions;
5. And quantitatively, the model is **conjugate**: The posterior is again Gaussian, with mean the
   *precision-weighted average* `μ⋆ = (τ₀·μ₀ + τ·x)/(τ₀ + τ)` of prior mean and signal
   (`τ₀ = 1/v₀`, `τ = 1/v`) and variance `v⋆ = (τ₀ + τ)⁻¹`. The posterior mean is strictly
   increasing in the signal, observing the signal strictly reduces variance, and — for a signal
   above the prior mean — a more precise signal moves the posterior mean strictly closer to the
   signal: the signal-extraction closed forms behind Kalman filtering, reputation, and global games.

Steps 1–3 are comparative statics in the type `θ` (no Bayesian updating); steps 4–5 are the
posterior statements, built from the same MLRP via
`HasMonotoneLikelihoodRatio.posteriorRatioMonotone` and from the conjugacy theorem
`ContDist.gaussian_posterior`. The Gaussian location family is the textbook MLRP example.

## The mathematics

Write the density as `f(x ∣ θ) = C · exp(-(x-θ)² / (2v))`, where the normalizing constant
`C = (√(2πv))⁻¹` does not depend on `θ`. The MLRP cross-product inequality
`f(x₁∣θ₂)·f(x₂∣θ₁) ≤ f(x₂∣θ₂)·f(x₁∣θ₁)` (for `θ₁ < θ₂`, `x₁ ≤ x₂`) reduces, after cancelling `C²`
and taking logs, to comparing exponents. The difference of exponents is exactly
`2(θ₂-θ₁)(x₂-x₁) / (2v) ≥ 0`, which drives everything downstream — and is strictly positive when
both orderings are strict, giving the strict MLRP.

For step 3 we use the bounded monotone statistic `arctan` (bounded by `π/2`), which keeps the
integrability side conditions to a one-line domination by the density; the general monotone
statistic is `higher_type_higher_expectation_general`. Reading the statistic as an optimal action,
step 3′ (`higher_type_higher_optimal_action`) turns this into decision-theoretic comparative
statics: A supermodular payoff gives a monotone optimal policy by Topkis, which a compact action set
makes bounded (hence integrable), so the expected optimal action rises with the type. For steps 4–5
the Bayes side conditions
(integrability of the prior-weighted likelihood, positivity of the evidence) come from the
normal-normal factorization `N(θ; μ₀, v₀)·N(x; θ, v) = N(x; μ₀, v₀+v)·N(θ; μ⋆, v⋆)` packaged
upstream in `Econlib.Probability.Distributions.GaussianConjugate`.

## Main definitions and theorems

* `gaussianLocation_mlrp`, `gaussianLocation_strict_mlrp` — the Gaussian location family has the
  (strict) MLRP.
* `higher_mean_fosd` — `θ₁ ≤ θ₂` makes the `θ₂`-signal FOSD-dominate the `θ₁`-signal.
* `higher_type_higher_expectation` — `θ ↦ E[arctan(X) ∣ θ]` is increasing in the type;
  `higher_type_strictly_higher_expectation` — strictly, for `θ₁ < θ₂`;
  `higher_type_higher_expectation_general` / `higher_type_strictly_higher_expectation_general` — the
  general monotone / strictly monotone statistic.
* `optimalAction` / `higher_type_higher_optimal_action` — the decision-theoretic payoff: With a
  supermodular payoff over a compact action set, the agent's expected optimal action is weakly
  increasing in the type (Topkis's monotone optimal policy composed with the FOSD engine).
* `higher_signal_raises_posterior_odds` — with any Gaussian prior over the state, the posterior
  odds on a higher state are nondecreasing in the observed signal.
* `posterior_is_gaussian` — conjugacy: The posterior given signal `x` is `N(μ⋆, v⋆)`;
  `posterior_mean_eq`, `posterior_variance_eq` — the closed forms.
* `posterior_mean_strictMono_signal` — a strictly higher signal strictly raises the posterior mean.
* `learning_reduces_variance` — the posterior variance is strictly below the prior variance.
* `sharper_signal_moves_belief_more` — for a signal above the prior mean, a more precise signal
  pulls the posterior mean strictly closer to the signal.
-/

noncomputable section

namespace EconlibExamples.Probability.GaussianSignal

open Econlib.Probability Econlib.Optimization ProbabilityTheory MeasureTheory
open scoped Real

variable (v : ℝ) (hv : 0 < v)

/-! ## Step 1: The Gaussian location family has the MLRP -/

/-- **The Gaussian location family is MLRP.** Fixing the variance `v`, the density family
`f(x, θ) = (gaussian θ v).density x` satisfies the monotone likelihood ratio property. -/
theorem gaussianLocation_mlrp :
    HasMLRP (fun θ => ContDist.gaussian θ v hv) :=
  ContDist.gaussianLocation_hasMLRP v hv

/-- **The Gaussian location family is strictly MLRP.** When both the types and the signals are
strictly ordered, the cross-product inequality in the MLRP is strict. -/
theorem gaussianLocation_strict_mlrp :
    HasStrictMLRP (fun θ => ContDist.gaussian θ v hv) :=
  ContDist.gaussianLocation_hasStrictMLRP v hv

/-! ## Step 2: Higher type ⇒ first-order stochastic dominance -/

/-- **MLRP ⇒ FOSD.** When `θ₁ ≤ θ₂`, the signal distribution at the higher type `θ₂` first-order
stochastically dominates the one at `θ₁`. -/
theorem higher_mean_fosd {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) :
    FOSD (ContDist.gaussian θ₂ v hv).toProbDist (ContDist.gaussian θ₁ v hv).toProbDist :=
  (gaussianLocation_mlrp v hv).fosd hθ

/-! ## Step 3: Monotone comparative statics in the type -/

/-- `density · arctan` is integrable: `arctan` is bounded by `π/2`, so the integrand is dominated
by `(π/2) · density`, and the density is integrable. -/
lemma gaussian_arctan_integrable (m : ℝ) :
    Integrable (fun x => (ContDist.gaussian m v hv).density x * Real.arctan x) := by
  refine Integrable.mono'
    (g := fun x => Real.pi / 2 * (ContDist.gaussian m v hv).density x)
    ((ContDist.gaussian m v hv).integrable.const_mul _)
    ((ContDist.gaussian m v hv).integrable.aestronglyMeasurable.mul
      Real.continuous_arctan.measurable.aestronglyMeasurable)
    ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((ContDist.gaussian m v hv).nonneg x),
    mul_comm (Real.pi / 2)]
  apply mul_le_mul_of_nonneg_left _ ((ContDist.gaussian m v hv).nonneg x)
  rw [abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩

/-- **Comparative statics in the type.** The expectation of any bounded monotone statistic of the
signal — here `arctan` — is increasing in the type `θ`: A higher type induces a stochastically
larger signal (step 2), so every monotone statistic has weakly higher expectation. This is
comparative statics in the parameter `θ`, not Bayesian updating — for the posterior statement see
`higher_signal_raises_posterior_odds`. Reading the statistic as an agent's *optimal action* (a
monotone function of the signal) turns this into the decision-theoretic "higher type ⇒ higher
action" — formalized with an explicit decision problem in `higher_type_higher_optimal_action`. -/
theorem higher_type_higher_expectation {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) :
    (ContDist.gaussian θ₁ v hv).expect Real.arctan
      ≤ (ContDist.gaussian θ₂ v hv).expect Real.arctan :=
  (gaussianLocation_mlrp v hv).expectMonotone Real.arctan Real.arctan_strictMono.monotone hθ
    (gaussian_arctan_integrable v hv θ₁) (gaussian_arctan_integrable v hv θ₂)

/-- **The general monotone statistic.** The `arctan` instance above is one witness of the fully
general engine: any monotone statistic of the signal (with the two integrability side conditions)
has expectation increasing in the type. -/
theorem higher_type_higher_expectation_general (g : ℝ → ℝ) (hg : Monotone g)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (hInt₁ : Integrable (fun x => (ContDist.gaussian θ₁ v hv).density x * g x))
    (hInt₂ : Integrable (fun x => (ContDist.gaussian θ₂ v hv).density x * g x)) :
    (ContDist.gaussian θ₁ v hv).expect g ≤ (ContDist.gaussian θ₂ v hv).expect g :=
  (gaussianLocation_mlrp v hv).expectMonotone g hg hθ hInt₁ hInt₂

/-- **Strict comparative statics.** Because the Gaussian family is *strictly* MLRP and its
densities are everywhere positive, a strictly higher type yields a strictly higher expectation of
any strictly monotone statistic — here `arctan`. -/
theorem higher_type_strictly_higher_expectation {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    (ContDist.gaussian θ₁ v hv).expect Real.arctan
      < (ContDist.gaussian θ₂ v hv).expect Real.arctan :=
  HasStrictMLRP.expectStrictMono_of_pos (gaussianLocation_strict_mlrp v hv)
    Real.arctan Real.arctan_strictMono hθ
    (gaussian_arctan_integrable v hv θ₁) (gaussian_arctan_integrable v hv θ₂)
    (fun t => gaussianPDFReal_pos θ₁ _ t (gaussianVarianceNNReal_ne_zero v hv))

/-- **The general strictly monotone statistic.** The `arctan` instance above is one witness of the
fully general strict engine: any strictly monotone statistic of the signal (with the two
integrability side conditions) has expectation strictly increasing in the type, because the
Gaussian family is strictly MLRP with everywhere-positive density. This is the strict counterpart of
`higher_type_higher_expectation_general`. -/
theorem higher_type_strictly_higher_expectation_general (g : ℝ → ℝ) (hg : StrictMono g)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hInt₁ : Integrable (fun x => (ContDist.gaussian θ₁ v hv).density x * g x))
    (hInt₂ : Integrable (fun x => (ContDist.gaussian θ₂ v hv).density x * g x)) :
    (ContDist.gaussian θ₁ v hv).expect g < (ContDist.gaussian θ₂ v hv).expect g :=
  HasStrictMLRP.expectStrictMono_of_pos (gaussianLocation_strict_mlrp v hv) g hg hθ hInt₁ hInt₂
    (fun t => gaussianPDFReal_pos θ₁ _ t (gaussianVarianceNNReal_ne_zero v hv))

/-! ## Step 3′: A decision problem — higher type ⇒ higher optimal action

Steps 1–3 move the expectation of an exogenous statistic of the signal. Here we close the loop
with an actual single-agent decision problem and show the agent's *optimal action* is monotone
comparative statics in the type — formalizing the prose "a higher type leads the agent to take a
(weakly) higher action," with an explicit action set, payoff, and optimal policy rather than a bare
statistic.

After observing the signal `x`, the agent chooses an action `a` from a compact feasible set `A` to
maximize a payoff `u x a` that is **supermodular** in `(signal, action)` — increasing differences,
i.e. the marginal value of a higher action rises with the signal. Topkis's theorem
(`sSup_argmax_monotone_of_supermodular`) makes the optimal-action policy `optimalAction` monotone in
the signal; the feasible set being compact makes it bounded, hence integrable against the Gaussian
density; composing with the monotone-statistic engine of step 3
(`higher_type_higher_expectation_general`) makes the *expected optimal action* increasing in the
type. -/

variable {A : Set ℝ} {u : ℝ → ℝ → ℝ}

/-- The agent's **optimal-action policy**: The largest maximizer of the payoff `u x ·` over the
feasible set `A`, as a function of the observed signal `x`. The `sSup` selects a definite action
from the (possibly flat-top) argmax set. This is a totalized selector: outside the standing
hypotheses of the theorems below (`A` compact and nonempty with continuous objectives) the argmax
set may be empty or unbounded and the `sSup` returns junk — those hypotheses are what
`optimalAction_monotone`/`optimalAction_mem` supply. -/
def optimalAction (u : ℝ → ℝ → ℝ) (A : Set ℝ) (x : ℝ) : ℝ := sSup (argmax (u x) A)

/-- **The optimal action is monotone in the signal** (Topkis). A supermodular payoff over a compact,
nonempty feasible set with continuous objectives has an upper optimal-action selection that rises
weakly with the signal. -/
lemma optimalAction_monotone (h_sm : Supermodular u) (hA_ne : A.Nonempty) (hA_cpt : IsCompact A)
    (h_cont : ∀ x, ContinuousOn (u x) A) : Monotone (optimalAction u A) :=
  sSup_argmax_monotone_of_supermodular h_sm hA_ne hA_cpt h_cont

/-- The optimal action is feasible: It lies in `A` at every signal (the `sSup` of the nonempty
compact argmax set is attained, and maximizers are feasible). -/
lemma optimalAction_mem (hA_ne : A.Nonempty) (hA_cpt : IsCompact A)
    (h_cont : ∀ x, ContinuousOn (u x) A) (x : ℝ) : optimalAction u A x ∈ A :=
  ((argmax_compact hA_cpt (h_cont x)).sSup_mem
    (argmax_nonempty hA_cpt hA_ne (h_cont x))).1

/-- A bounded measurable statistic is integrable against the Gaussian density: The integrand is
dominated by `M · density` and the density is integrable. (Generalizes `gaussian_arctan_integrable`
from the explicit `π/2` bound of `arctan` to any uniform bound `M`.) -/
lemma gaussian_bdd_integrable (m : ℝ) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) :
    Integrable (fun x => (ContDist.gaussian m v hv).density x * g x) := by
  refine Integrable.mono' (g := fun x => M * (ContDist.gaussian m v hv).density x)
    ((ContDist.gaussian m v hv).integrable.const_mul _)
    ((ContDist.gaussian m v hv).integrable.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((ContDist.gaussian m v hv).nonneg x), mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM x) ((ContDist.gaussian m v hv).nonneg x)

/-- **Higher type ⇒ higher optimal action.** In a single-agent decision problem with a supermodular
payoff `u` over a compact feasible set `A`, the agent's expected optimal action under the
signal `X ~ N(θ, v)` is weakly increasing in the type `θ`. This is the decision-theoretic content
the prose of step 3 promises, now with an explicit action set, payoff, and optimal policy: A higher
type stochastically raises the signal (step 2), the supermodular structure makes the optimal action
rise with the signal (Topkis), and the two compose to raise the expected action. -/
theorem higher_type_higher_optimal_action
    (h_sm : Supermodular u) (hA_ne : A.Nonempty) (hA_cpt : IsCompact A)
    (h_cont : ∀ x, ContinuousOn (u x) A) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) :
    (ContDist.gaussian θ₁ v hv).expect (optimalAction u A)
      ≤ (ContDist.gaussian θ₂ v hv).expect (optimalAction u A) := by
  have hmono : Monotone (optimalAction u A) := optimalAction_monotone h_sm hA_ne hA_cpt h_cont
  -- The feasible set is compact, hence bounded: a uniform bound `M` on every feasible action.
  obtain ⟨M, hM⟩ := hA_cpt.isBounded.exists_norm_le
  have hbound : ∀ x, |optimalAction u A x| ≤ M := fun x => by
    simpa [Real.norm_eq_abs] using hM _ (optimalAction_mem hA_ne hA_cpt h_cont x)
  exact higher_type_higher_expectation_general v hv (optimalAction u A) hmono hθ
    (gaussian_bdd_integrable v hv θ₁ hmono.measurable hbound)
    (gaussian_bdd_integrable v hv θ₂ hmono.measurable hbound)

/-! ## Step 4: The Bayesian posterior — a higher signal shifts belief toward higher states

The previous steps are comparative statics in the type. Now we invert: Put a Gaussian prior
`θ ~ N(μ₀, v₀)` on the unknown state, observe a signal `x`, and form the posterior over `θ` by
Bayes' rule. The integrability and positivity side conditions are supplied by the upstream
normal-normal machinery: The prior-weighted likelihood is a constant multiple of a Gaussian density
(`ContDist.gaussian_likelihood_integrable`), and the evidence equals the prior-predictive density
`N(x; μ₀, v₀ + v)` (`ContDist.gaussian_evidence`), which is positive. The same MLRP as in steps 1–3
then makes the posterior **increasing in the observed signal**. -/

variable (μ₀ : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀)

/-- The Bayesian evidence (normalizing constant) is strictly positive at every signal: It equals
the prior-predictive density `N(x; μ₀, v₀ + v)`, and Gaussian densities are positive. -/
lemma posterior_denom_pos (x : ℝ) :
    0 < ∫ θ, (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x := by
  rw [ContDist.gaussian_evidence μ₀ x hv₀ hv]
  simp only [ContDist.gaussian_density]
  exact gaussianPDFReal_pos _ _ _ (gaussianVarianceNNReal_ne_zero _ (by positivity))

/-- **Higher signal ⇒ higher posterior odds on higher states.** With any Gaussian prior over the
state `θ` and the Gaussian signal likelihood, the posterior odds of a higher state `θ₂` over a
lower state `θ₁` are nondecreasing in the observed signal `x`. This is the Bayesian payoff
of MLRP: Observing a larger signal shifts posterior belief toward higher states. -/
theorem higher_signal_raises_posterior_odds {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    Monotone (fun x =>
      (ContDist.gaussianPosterior μ₀ x hv₀ hv).density θ₂ /
      (ContDist.gaussianPosterior μ₀ x hv₀ hv).density θ₁) :=
  HasMonotoneLikelihoodRatio.posteriorRatioMonotone (gaussianLocation_mlrp v hv)
    (ContDist.gaussian μ₀ v₀ hv₀) hθ
    (fun x θ => (ContDist.gaussian θ v hv).nonneg x)
    (fun x => gaussianPDFReal_pos θ₁ _ x (gaussianVarianceNNReal_ne_zero v hv))
    (gaussianPDFReal_pos μ₀ _ θ₁ (gaussianVarianceNNReal_ne_zero v₀ hv₀))
    (fun x => ContDist.gaussian_likelihood_integrable μ₀ x hv₀ hv)
    (posterior_denom_pos v hv μ₀ hv₀)

/-! ## Step 5: Conjugate updating — the posterior in closed form

The monotonicity in step 4 is qualitative and would hold for any prior with positive integrable
density. The Gaussian prior buys the quantitative closed form: The model is **conjugate**, so the
posterior is again Gaussian, with the textbook precision-weighted parameters. -/

/-- **Conjugacy: The posterior is Gaussian**, `θ ∣ x ~ N(μ⋆, v⋆)` with the precision-weighted mean
`μ⋆ = (v·μ₀ + v₀·x)/(v₀ + v)` (cf. `gaussianPosteriorMean_eq_precision`) and the summed-precision
variance `v⋆ = v₀·v/(v₀ + v) = (1/v₀ + 1/v)⁻¹` (cf. `gaussianPosteriorVariance_eq_precision`). -/
theorem posterior_is_gaussian (x : ℝ) :
    ContDist.gaussianPosterior μ₀ x hv₀ hv =
      ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
        (gaussianPosteriorVariance_pos hv₀ hv) :=
  ContDist.gaussianPosterior_eq μ₀ x hv₀ hv

/-- **The posterior mean in closed form**: The precision-weighted average of the prior mean and the
signal. -/
theorem posterior_mean_eq (x : ℝ) :
    (ContDist.gaussianPosterior μ₀ x hv₀ hv).expect id = (v * μ₀ + v₀ * x) / (v₀ + v) :=
  ContDist.gaussianPosterior_expect μ₀ x hv₀ hv

/-- **The posterior variance in closed form**: The inverse of the summed precisions — independent
of the observed signal. -/
theorem posterior_variance_eq (x : ℝ) :
    (ContDist.gaussianPosterior μ₀ x hv₀ hv).variance id = v₀ * v / (v₀ + v) :=
  ContDist.gaussianPosterior_variance μ₀ x hv₀ hv

/-- **A strictly higher signal strictly raises the posterior mean** — the strict, quantitative form
of "a higher signal shifts belief upward": The posterior mean responds to the signal with the
strictly positive weight `v₀/(v₀ + v)`. -/
theorem posterior_mean_strictMono_signal :
    StrictMono (fun x => (ContDist.gaussianPosterior μ₀ x hv₀ hv).expect id) := by
  intro x₁ x₂ hx
  dsimp only
  rw [posterior_mean_eq v hv μ₀ hv₀ x₁, posterior_mean_eq v hv μ₀ hv₀ x₂]
  have hsum_pos : 0 < v₀ + v := by positivity
  rw [div_lt_div_iff_of_pos_right hsum_pos]
  nlinarith [mul_pos hv₀ (sub_pos.2 hx)]

/-- **Learning reduces variance**: After observing any signal, the posterior variance is strictly
below the prior variance `v₀`. -/
theorem learning_reduces_variance (x : ℝ) :
    (ContDist.gaussianPosterior μ₀ x hv₀ hv).variance id < v₀ := by
  rw [ContDist.gaussianPosterior_variance μ₀ x hv₀ hv]
  exact gaussianPosteriorVariance_lt_left hv₀ hv

/-- **A more precise signal moves beliefs more.** For a signal above the prior mean, lowering the
noise variance (from `v₂` to `v₁ < v₂`) strictly raises the posterior mean toward the signal: The
precision weight on the signal grows. -/
theorem sharper_signal_moves_belief_more {x : ℝ} (hx : μ₀ < x)
    {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (h12 : v₁ < v₂) :
    (ContDist.gaussianPosterior μ₀ x hv₀ hv₂).expect id <
      (ContDist.gaussianPosterior μ₀ x hv₀ hv₁).expect id := by
  rw [ContDist.gaussianPosterior_expect μ₀ x hv₀ hv₂,
    ContDist.gaussianPosterior_expect μ₀ x hv₀ hv₁]
  exact gaussianPosteriorMean_strictAnti_var μ₀ x hv₀ hx
    (Set.mem_Ioi.mpr hv₁) (Set.mem_Ioi.mpr hv₂) h12

end EconlibExamples.Probability.GaussianSignal

end
