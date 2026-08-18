/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Correlated-Gaussian Cournot duopoly — a linear Bayes–Nash equilibrium

A worked example exercising the correlated disintegration path of the
measure-theoretic Bayesian-game framework (`Econlib.GameTheory.MeasBayesianGame`). Unlike the
first-price auction — which uses an independent product prior and the ex-ante / Fubini route — this
example builds a *correlated* Gaussian prior and verifies equilibrium through the **interim**
characterization `MeasBayesianGame.isBNE_of_ae_interim` (a.e. interim best response ⇒ BNE), passing
through the conditional law `condProfile` and the conjugate Gaussian conditional means.

## The model

Two firms `Fin 2` choose quantities `q i ∈ ℝ`. Inverse demand is `P = a − q₀ − q₁`; firm `i` has
constant marginal cost `θ i` (its private type), so its profit is the linear-quadratic Cournot
payoff

`πᵢ(q, θ) = qᵢ · (a − q₀ − q₁) − θᵢ · qᵢ`.

Costs are **correlated** via the noisy-signal Gaussian model
(`Econlib.Probability.gaussianNoisyLaw`): Firm 0's cost is `θ₀ ~ N(μ₀, v₀)` and firm 1's cost is a
noisy reading `θ₁ ∣ θ₀ ~ N(θ₀, v)`. The two conditional means are the conjugate Gaussian closed
forms `E[θ₁ ∣ θ₀] = θ₀` and `E[θ₀ ∣ θ₁] = μ⋆(θ₁) = (v·μ₀ + v₀·θ₁)/(v₀+v)`.

## The equilibrium

The linear equilibrium `qᵢ(θᵢ) = αᵢ + βᵢ·θᵢ` we construct has

`β₀ = −(v₀+v)/(3v₀+4v)`,  `β₁ = −(v₀+2v)/(3v₀+4v)`, `α₁ = a/3 + 2v·μ₀/(3(3v₀+4v))`,
`α₀ = (a − α₁)/2`,

derived from the two interim first-order conditions `qᵢ(θᵢ) = (a − θᵢ − E[q_j ∣ θᵢ])/2`. Because
each firm's interim objective is concave in its own quantity and, after fiber concentration,
**affine in the opponent's type**, the equilibrium needs only first conditional moments — no second
moments enter the interim comparison. These are also the *unique* coefficients for which a linear
schedule is a Bayes–Nash equilibrium, but uniqueness is established only within the linear class
(`linearBNE_coeffs_unique`); non-linear equilibria are not ruled out.

## Main statements

* `CorrelatedCournot.linearStrategy_isBNE`: The linear schedule is a Bayes–Nash equilibrium in the
  canonical `MeasBayesianGame.IsBNE` sense.
* `CorrelatedCournot.linearBNE_coeffs_unique`: Among **linear** strategies, the equilibrium is
  unique — any linear BNE has the displayed `coeffA`/`coeffB`. (Scope: Linear strategies only; this
  is the standard "unique linear equilibrium" claim, not uniqueness among all measurable
  strategies.)
* `CorrelatedCournot.linearStrategy_unique_of_isBNE`: The same statement at the level of strategy
  profiles — any linear BNE coincides with `linearStrategy`.

## Tags

cournot, bayesian game, correlated types, gaussian, bayes-nash equilibrium, interim, signal
-/

open MeasureTheory ProbabilityTheory Function Econlib.GameTheory Econlib.Probability

noncomputable section

namespace CorrelatedCournot

/-! ### Parameters and the game -/

variable (a μ₀ : ℝ) {v₀ v : ℝ}

/-- The correlated-cost prior on the type profile `Fin 2 → ℝ`: The noisy-signal Gaussian joint
`(θ₀, θ₁)` in profile form, `Econlib.Probability.gaussianNoisyLawVec`. -/
def prior (μ₀ : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) : Measure (Fin 2 → ℝ) :=
  gaussianNoisyLawVec μ₀ v₀ v hv₀ hv

instance (hv₀ : 0 < v₀) (hv : 0 < v) : IsProbabilityMeasure (prior μ₀ hv₀ hv) := by
  rw [prior]; infer_instance

/-- The **correlated-Gaussian Cournot duopoly** as a measure-theoretic Bayesian game: Players
`Fin 2`, type (cost) and action (quantity) spaces `ℝ`, the correlated noisy-signal prior, and the
linear-quadratic Cournot payoff `qᵢ·(a − q₀ − q₁) − θᵢ·qᵢ`. -/
@[reducible] def game (hv₀ : 0 < v₀) (hv : 0 < v) : MeasBayesianGame where
  Player := Fin 2
  Theta := fun _ => ℝ
  Action := fun _ => ℝ
  prior := prior μ₀ hv₀ hv
  payoff := fun i q θ => q i * (a - q 0 - q 1) - θ i * q i
  measurable_payoff := fun i => by
    have hq0 : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 0) :=
      (measurable_pi_apply 0).comp measurable_fst
    have hq1 : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 1) :=
      (measurable_pi_apply 1).comp measurable_fst
    have hqi : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hθi : Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact (hqi.mul ((measurable_const.sub hq0).sub hq1)).sub (hθi.mul hqi)

@[simp] lemma game_payoff (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2) (q θ : Fin 2 → ℝ) :
    (game a μ₀ hv₀ hv).payoff i q θ = q i * (a - q 0 - q 1) - θ i * q i := rfl

@[simp] lemma game_prior (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).prior = prior μ₀ hv₀ hv := rfl

/-! ### The equilibrium coefficients and strategy -/

/-- The equilibrium slope coefficients `β : Fin 2 → ℝ`, `β₀ = −(v₀+v)/(3v₀+4v)`,
`β₁ = −(v₀+2v)/(3v₀+4v)`. -/
def coeffB (v₀ v : ℝ) : Fin 2 → ℝ :=
  ![-(v₀ + v) / (3 * v₀ + 4 * v), -(v₀ + 2 * v) / (3 * v₀ + 4 * v)]

/-- The equilibrium intercept coefficients `α : Fin 2 → ℝ`, `α₁ = a/3 + 2v·μ₀/(3(3v₀+4v))`,
`α₀ = (a − α₁)/2`. -/
def coeffA (a μ₀ v₀ v : ℝ) : Fin 2 → ℝ :=
  ![(a - (a / 3 + 2 * v * μ₀ / (3 * (3 * v₀ + 4 * v)))) / 2,
    a / 3 + 2 * v * μ₀ / (3 * (3 * v₀ + 4 * v))]

/-- A general **linear schedule** `qᵢ(θᵢ) = αᵢ + βᵢ·θᵢ` with arbitrary coefficients, packaged as a
measurable strategy profile of the Cournot game. The equilibrium `linearStrategy` is the instance
with the closed-form coefficients; the uniqueness theorem ranges over all such schedules. -/
def linearStrategyOf (α β : Fin 2 → ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).Strategy :=
  fun i => ⟨fun t => α i + β i * t,
    (measurable_const.add (measurable_const.mul measurable_id))⟩

@[simp] lemma linearStrategyOf_apply (α β : Fin 2 → ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2)
    (t : ℝ) : (linearStrategyOf a μ₀ α β hv₀ hv i).1 t = α i + β i * t := rfl

/-- The linear equilibrium schedule `qᵢ(θᵢ) = αᵢ + βᵢ·θᵢ` with the closed-form coefficients
`coeffA`, `coeffB`. -/
def linearStrategy (hv₀ : 0 < v₀) (hv : 0 < v) : (game a μ₀ hv₀ hv).Strategy :=
  linearStrategyOf a μ₀ (coeffA a μ₀ v₀ v) (coeffB v₀ v) hv₀ hv

@[simp] lemma linearStrategy_apply (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2) (t : ℝ) :
    (linearStrategy a μ₀ hv₀ hv i).1 t = coeffA a μ₀ v₀ v i + coeffB v₀ v i * t := rfl

/-! ### Best-response (first-order condition) identities

The two interim first-order conditions `qᵢ(θᵢ) = (a − θᵢ − E[q_j ∣ θᵢ])/2`, with
`E[q₁ ∣ θ₀] = α₁ + β₁·θ₀` and `E[q₀ ∣ θ₁] = α₀ + β₀·μ⋆(θ₁)`. These are polynomial identities in the
type, verified from the closed-form coefficients. -/

/-- Firm 0's interim FOC: `q₀(θ₀) = (a − θ₀ − (α₁ + β₁θ₀))/2`, using `E[θ₁ ∣ θ₀] = θ₀`. -/
lemma foc_zero (hv₀ : 0 < v₀) (hv : 0 < v) (t : ℝ) :
    coeffA a μ₀ v₀ v 0 + coeffB v₀ v 0 * t =
      (a - t - (coeffA a μ₀ v₀ v 1 + coeffB v₀ v 1 * t)) / 2 := by
  have h1 : (3 * v₀ + 4 * v) ≠ 0 := by positivity
  simp only [coeffA, coeffB, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- Firm 1's interim FOC: `q₁(θ₁) = (a − θ₁ − (α₀ + β₀·μ⋆(θ₁)))/2`, using `E[θ₀ ∣ θ₁] = μ⋆(θ₁)`. -/
lemma foc_one (hv₀ : 0 < v₀) (hv : 0 < v) (t : ℝ) :
    coeffA a μ₀ v₀ v 1 + coeffB v₀ v 1 * t =
      (a - t - (coeffA a μ₀ v₀ v 0 +
        coeffB v₀ v 0 * gaussianPosteriorMean μ₀ v₀ v t)) / 2 := by
  have h1 : (3 * v₀ + 4 * v) ≠ 0 := by positivity
  have h2 : (v₀ + v) ≠ 0 := by positivity
  simp only [coeffA, coeffB, gaussianPosteriorMean, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-! ### The conditional-law bridge

The conditional law of the *opponent's* type given a firm's own type, pushed through the
`condProfile` of the framework. The single fact each interim computation needs is that
`(condProfile i θᵢ).map (eval j)` is the appropriate Gaussian conditional, from which both the
conditional mean and integrability of the opponent's quantity follow.

Because `prior` is `Econlib.Probability.gaussianNoisyLawVec`, its coordinate marginals and
conditional laws are the reusable profile-form accessors from `GaussianConditional`; the four named
lemmas below are one-line re-exports at the `prior` name. -/

/-- (H1) The first-coordinate marginal of the prior is the parameter prior `N(μ₀, v₀)`. -/
private lemma prior_map_eval0 (hv₀ : 0 < v₀) (hv : 0 < v) :
    (prior μ₀ hv₀ hv).map (fun θ : Fin 2 → ℝ => θ 0)
      = gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) :=
  gaussianNoisyLawVec_map_eval_zero μ₀ v₀ v hv₀ hv

/-- (H2) The second-coordinate marginal of the prior is the prior-predictive `N(μ₀, v₀+v)`. -/
private lemma prior_map_eval1 (hv₀ : 0 < v₀) (hv : 0 < v) :
    (prior μ₀ hv₀ hv).map (fun θ : Fin 2 → ℝ => θ 1)
      = gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) :=
  gaussianNoisyLawVec_map_eval_one μ₀ v₀ v hv₀ hv

/-- (C1) The conditional law of firm 1's type given firm 0's type is the location kernel
`N(θ₀, v)`, a.e. with respect to the firm-0 marginal `N(μ₀, v₀)`. -/
private lemma condDistrib_eval1_eval0 (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib (fun θ : Fin 2 → ℝ => θ 1) (fun θ => θ 0) (prior μ₀ hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀)] locationKernel v hv :=
  condDistrib_eval_one_eval_zero_gaussianNoisyLawVec μ₀ v₀ v hv₀ hv

/-- (C2) The conditional law of firm 0's type given firm 1's type is the posterior kernel
`N(μ⋆(θ₁), v⋆)`, a.e. with respect to the firm-1 marginal `N(μ₀, v₀+v)`. -/
private lemma condDistrib_eval0_eval1 (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib (fun θ : Fin 2 → ℝ => θ 0) (fun θ => θ 1) (prior μ₀ hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity))]
        posteriorKernel μ₀ v₀ v hv₀ hv :=
  condDistrib_eval_zero_eval_one_gaussianNoisyLawVec μ₀ v₀ v hv₀ hv

/-- The marginal type of firm 0 in the correlated-Gaussian Cournot game is the parameter prior
`N(μ₀, v₀)`. -/
private lemma marginalType_zero (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).marginalType 0
      = gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) := by
  rw [MeasBayesianGame.marginalType, game_prior, prior_map_eval0 μ₀ hv₀ hv]

/-- The marginal type of firm 1 in the correlated-Gaussian Cournot game is the prior-predictive
`N(μ₀, v₀+v)`. -/
private lemma marginalType_one (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).marginalType 1
      = gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) := by
  rw [MeasBayesianGame.marginalType, game_prior, prior_map_eval1 μ₀ hv₀ hv]

/-- **Firm 0's belief about firm 1's cost.** For almost every own cost `θ₀`, the conditional law of
firm 1's cost is `N(θ₀, v)` (the forward / likelihood conditional). -/
lemma condProfile_map_eval_zero (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ₀ ∂((game a μ₀ hv₀ hv).marginalType 0),
      ((game a μ₀ hv₀ hv).condProfile 0 θ₀).map (fun θ : Fin 2 → ℝ => θ 1)
        = gaussianReal θ₀ (gaussianVarianceNNReal v hv) := by
  -- The marginal type of firm 0 is the parameter prior `N(μ₀, v₀)`.
  rw [marginalType_zero a μ₀ hv₀ hv]
  -- `(condProfile 0).map (eval 1) =ᵐ condDistrib (eval 1) (eval 0) prior` (pushforward through the
  -- conditional law), and `condDistrib (eval 1) (eval 0) prior =ᵐ locationKernel v hv` (C1).
  have hidae : AEMeasurable (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (prior μ₀ hv₀ hv) :=
    aemeasurable_id
  have hcomp := condDistrib_comp (μ := prior μ₀ hv₀ hv) (mβ := (inferInstance : MeasurableSpace ℝ))
    (fun θ : Fin 2 → ℝ => θ 0) hidae (f := fun θ : Fin 2 → ℝ => θ 1) (measurable_pi_apply 1)
  rw [prior_map_eval0 μ₀ hv₀ hv] at hcomp
  filter_upwards [hcomp, condDistrib_eval1_eval0 μ₀ hv₀ hv] with θ₀ hθ_comp hθ_C1
  -- `condProfile 0 = condDistrib id (eval 0) prior`; push `eval 1` through it via
  -- `condDistrib_comp`, then identify the conditional with the location Gaussian (C1).
  change Measure.map (fun θ : Fin 2 → ℝ => θ 1)
    (condDistrib id (fun θ : Fin 2 → ℝ => θ 0) (prior μ₀ hv₀ hv) θ₀) = _
  rw [← Kernel.map_apply _ (measurable_pi_apply 1), ← hθ_comp]
  change (condDistrib (fun θ : Fin 2 → ℝ => θ 1) (fun θ => θ 0) (prior μ₀ hv₀ hv)) θ₀ = _
  rw [hθ_C1, locationKernel_apply]

/-- **Firm 1's belief about firm 0's cost.** For almost every own cost `θ₁`, the conditional law of
firm 0's cost is the conjugate posterior `N(μ⋆(θ₁), v⋆)`. -/
lemma condProfile_map_eval_one (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ₁ ∂((game a μ₀ hv₀ hv).marginalType 1),
      ((game a μ₀ hv₀ hv).condProfile 1 θ₁).map (fun θ : Fin 2 → ℝ => θ 0)
        = gaussianReal (gaussianPosteriorMean μ₀ v₀ v θ₁)
            (gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
              (gaussianPosteriorVariance_pos hv₀ hv)) := by
  -- The marginal type of firm 1 is the prior-predictive `N(μ₀, v₀+v)`.
  rw [marginalType_one a μ₀ hv₀ hv]
  have hidae : AEMeasurable (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (prior μ₀ hv₀ hv) :=
    aemeasurable_id
  have hcomp := condDistrib_comp (μ := prior μ₀ hv₀ hv) (mβ := (inferInstance : MeasurableSpace ℝ))
    (fun θ : Fin 2 → ℝ => θ 1) hidae (f := fun θ : Fin 2 → ℝ => θ 0) (measurable_pi_apply 0)
  rw [prior_map_eval1 μ₀ hv₀ hv] at hcomp
  filter_upwards [hcomp, condDistrib_eval0_eval1 μ₀ hv₀ hv] with θ₁ hθ_comp hθ_C2
  change Measure.map (fun θ : Fin 2 → ℝ => θ 0)
    (condDistrib id (fun θ : Fin 2 → ℝ => θ 1) (prior μ₀ hv₀ hv) θ₁) = _
  rw [← Kernel.map_apply _ (measurable_pi_apply 0), ← hθ_comp]
  change (condDistrib (fun θ : Fin 2 → ℝ => θ 0) (fun θ => θ 1) (prior μ₀ hv₀ hv)) θ₁ = _
  rw [hθ_C2, posteriorKernel_apply]

/-- Integrability of the opponent's coordinate `θ j` against any measure whose `eval j`-pushforward
is a real Gaussian — the conditional belief is Gaussian, so the opponent's cost has finite mean. -/
private lemma integrable_eval_of_map_gaussian {μ : Measure (Fin 2 → ℝ)} (j : Fin 2)
    {m : ℝ} {s : NNReal} (hmap : μ.map (fun θ : Fin 2 → ℝ => θ j) = gaussianReal m s) :
    Integrable (fun θ : Fin 2 → ℝ => θ j) μ := by
  have hid : Integrable (id : ℝ → ℝ) (μ.map (fun θ : Fin 2 → ℝ => θ j)) := by
    rw [hmap]; exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  have := (integrable_map_measure hid.aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).mp hid
  simpa [Function.comp] using this

/-- The conditional mean of the opponent's coordinate `θ j` equals the Gaussian mean `m` of the
`eval j`-pushforward belief. -/
private lemma integral_eval_of_map_gaussian {μ : Measure (Fin 2 → ℝ)} (j : Fin 2)
    {m : ℝ} {s : NNReal} (hmap : μ.map (fun θ : Fin 2 → ℝ => θ j) = gaussianReal m s) :
    ∫ θ, θ j ∂μ = m := by
  have hint : ∫ y, y ∂(μ.map (fun θ : Fin 2 → ℝ => θ j)) = ∫ θ : Fin 2 → ℝ, θ j ∂μ :=
    integral_map (measurable_pi_apply j).aemeasurable aestronglyMeasurable_id
  rw [← hint, hmap, integral_id_gaussianReal]

/-! ### Interim payoff closed forms

After fiber concentration (`θ i = θᵢ` a.e.) and integrating the opponent's quantity out, the
deviation interim payoff is the concave quadratic `b ↦ b·(Kᵢ(θᵢ) − b)`, where `Kᵢ(θᵢ)` is the
"effective intercept" net of the opponent's expected quantity and own cost. -/

/-- Firm 0's interim deviation payoff at quantity `b` against a general linear opponent
`q₁(θ₁) = α₁ + β₁θ₁`: `b·((a − α₁ − β₁θ₀ − θ₀) − b)`, using `E[θ₁ ∣ θ₀] = θ₀`. -/
lemma interimPayoffAction_zero_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) :
    ∀ᵐ θ₀ ∂((game a μ₀ hv₀ hv).marginalType 0), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoffAction 0 θ₀ b (linearStrategyOf a μ₀ α β hv₀ hv)
        = b * ((a - (α 1 + β 1 * θ₀) - θ₀) - b) := by
  filter_upwards [(game a μ₀ hv₀ hv).ae_condProfile_eval 0, condProfile_map_eval_zero a μ₀ hv₀ hv]
    with θ₀ hfiber hmap b
  -- Integrability of the opponent's coordinate `θ 1` against the conditional belief.
  have hinteg : Integrable (fun θ : Fin 2 → ℝ => θ 1) ((game a μ₀ hv₀ hv).condProfile 0 θ₀) :=
    integrable_eval_of_map_gaussian 1 hmap
  -- The conditional mean `∫ θ 1 = θ₀` (firm 0 expects firm 1's cost to equal its own).
  have hmean : ∫ θ : Fin 2 → ℝ, θ 1 ∂((game a μ₀ hv₀ hv).condProfile 0 θ₀) = θ₀ :=
    integral_eval_of_map_gaussian 1 hmap
  -- Rewrite the deviation integrand on the fiber `θ 0 = θ₀` to an affine function of `θ 1`.
  rw [MeasBayesianGame.interimPayoffAction]
  have hcongr : ∫ θ, (game a μ₀ hv₀ hv).payoff 0
        (Function.update
          ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) 0 b)
        θ ∂((game a μ₀ hv₀ hv).condProfile 0 θ₀)
      = ∫ θ : Fin 2 → ℝ,
          (b * (a - b - (α 1 + β 1 * θ 1)) - θ₀ * b)
          ∂((game a μ₀ hv₀ hv).condProfile 0 θ₀) := by
    refine integral_congr_ae ?_
    filter_upwards [hfiber] with θ hθ
    rw [hθ]
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
      MeasBayesianGame.actionProfile_apply, linearStrategyOf_apply]
  rw [hcongr]
  -- Split the affine integrand: constant part `b*(a-b) - θ₀*b - b*α 1` and the linear
  -- `-(b*β 1) * θ 1`, integrate the latter via the conditional mean.
  have hrw : ∀ θ : Fin 2 → ℝ,
      b * (a - b - (α 1 + β 1 * θ 1)) - θ₀ * b
        = (b * (a - b) - θ₀ * b - b * α 1) + (-(b * β 1)) * θ 1 := by
    intro θ; ring
  haveI : IsProbabilityMeasure ((game a μ₀ hv₀ hv).condProfile 0 θ₀) := by
    unfold MeasBayesianGame.condProfile; infer_instance
  simp only [hrw]
  rw [integral_add (integrable_const _) (hinteg.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul, hmean]
  ring

/-- Firm 0's interim deviation payoff against the equilibrium schedule, the `coeffA`/`coeffB`
instance of `interimPayoffAction_zero_lin`. -/
lemma interimPayoffAction_zero (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ₀ ∂((game a μ₀ hv₀ hv).marginalType 0), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoffAction 0 θ₀ b (linearStrategy a μ₀ hv₀ hv)
        = b * ((a - (coeffA a μ₀ v₀ v 1 + coeffB v₀ v 1 * θ₀) - θ₀) - b) :=
  interimPayoffAction_zero_lin a μ₀ hv₀ hv (coeffA a μ₀ v₀ v) (coeffB v₀ v)

/-- Firm 1's interim deviation payoff at quantity `b` against a general linear opponent
`q₀(θ₀) = α₀ + β₀θ₀`: `b·((a − α₀ − β₀·μ⋆(θ₁) − θ₁) − b)`, using `E[θ₀ ∣ θ₁] = μ⋆(θ₁)`. -/
lemma interimPayoffAction_one_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) :
    ∀ᵐ θ₁ ∂((game a μ₀ hv₀ hv).marginalType 1), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoffAction 1 θ₁ b (linearStrategyOf a μ₀ α β hv₀ hv)
        = b * ((a - (α 0 + β 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) - b) := by
  filter_upwards [(game a μ₀ hv₀ hv).ae_condProfile_eval 1, condProfile_map_eval_one a μ₀ hv₀ hv]
    with θ₁ hfiber hmap b
  -- Integrability and conditional mean of the opponent's coordinate `θ 0` — the conjugate posterior
  -- mean `μ⋆(θ₁)`.
  have hinteg : Integrable (fun θ : Fin 2 → ℝ => θ 0) ((game a μ₀ hv₀ hv).condProfile 1 θ₁) :=
    integrable_eval_of_map_gaussian 0 hmap
  have hmean : ∫ θ : Fin 2 → ℝ, θ 0 ∂((game a μ₀ hv₀ hv).condProfile 1 θ₁)
      = gaussianPosteriorMean μ₀ v₀ v θ₁ :=
    integral_eval_of_map_gaussian 0 hmap
  rw [MeasBayesianGame.interimPayoffAction]
  have hcongr : ∫ θ, (game a μ₀ hv₀ hv).payoff 1
        (Function.update
          ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) 1 b)
        θ ∂((game a μ₀ hv₀ hv).condProfile 1 θ₁)
      = ∫ θ : Fin 2 → ℝ,
          (b * (a - (α 0 + β 0 * θ 0) - b) - θ₁ * b)
          ∂((game a μ₀ hv₀ hv).condProfile 1 θ₁) := by
    refine integral_congr_ae ?_
    filter_upwards [hfiber] with θ hθ
    rw [hθ]
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      MeasBayesianGame.actionProfile_apply, linearStrategyOf_apply]
  rw [hcongr]
  haveI : IsProbabilityMeasure ((game a μ₀ hv₀ hv).condProfile 1 θ₁) := by
    unfold MeasBayesianGame.condProfile; infer_instance
  have hrw : ∀ θ : Fin 2 → ℝ,
      b * (a - (α 0 + β 0 * θ 0) - b) - θ₁ * b
        = (b * (a - b) - θ₁ * b - b * α 0) + (-(b * β 0)) * θ 0 := by
    intro θ; ring
  simp only [hrw]
  rw [integral_add (integrable_const _) (hinteg.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul, hmean]
  ring

/-- Firm 1's interim deviation payoff against the equilibrium schedule, the `coeffA`/`coeffB`
instance of `interimPayoffAction_one_lin`. -/
lemma interimPayoffAction_one (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ₁ ∂((game a μ₀ hv₀ hv).marginalType 1), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoffAction 1 θ₁ b (linearStrategy a μ₀ hv₀ hv)
        = b * ((a - (coeffA a μ₀ v₀ v 0 +
            coeffB v₀ v 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) - b) :=
  interimPayoffAction_one_lin a μ₀ hv₀ hv (coeffA a μ₀ v₀ v) (coeffB v₀ v)

/-! ### Integrability of the equilibrium payoff -/

/-- Each coordinate of a jointly-Gaussian type profile is square-integrable against the prior: Its
marginal is a real Gaussian, all of whose moments are finite (`memLp_id_gaussianReal`). -/
private lemma memLp_eval_two_prior (hv₀ : 0 < v₀) (hv : 0 < v) (j : Fin 2) :
    MemLp (fun θ : Fin 2 → ℝ => θ j) 2 (prior μ₀ hv₀ hv) := by
  have hmap : ∃ (m : ℝ) (s : NNReal),
      (prior μ₀ hv₀ hv).map (fun θ : Fin 2 → ℝ => θ j) = gaussianReal m s := by
    fin_cases j
    · exact ⟨μ₀, _, prior_map_eval0 μ₀ hv₀ hv⟩
    · exact ⟨μ₀, _, prior_map_eval1 μ₀ hv₀ hv⟩
  obtain ⟨m, s, hms⟩ := hmap
  have hid : MemLp (id : ℝ → ℝ) 2 ((prior μ₀ hv₀ hv).map (fun θ : Fin 2 → ℝ => θ j)) := by
    rw [hms]; exact memLp_id_gaussianReal 2
  have := (memLp_map_measure_iff hid.aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).mp hid
  simpa [Function.comp] using this

/-- An affine function of one coordinate is square-integrable against the prior. -/
private lemma memLp_affine_eval_two_prior (hv₀ : 0 < v₀) (hv : 0 < v) (j : Fin 2) (c₀ c₁ : ℝ) :
    MemLp (fun θ : Fin 2 → ℝ => c₀ + c₁ * θ j) 2 (prior μ₀ hv₀ hv) := by
  have hconst : MemLp (fun _ : Fin 2 → ℝ => c₀) 2 (prior μ₀ hv₀ hv) := memLp_const c₀
  have hlin : MemLp (fun θ : Fin 2 → ℝ => c₁ * θ j) 2 (prior μ₀ hv₀ hv) :=
    (memLp_eval_two_prior μ₀ hv₀ hv j).const_mul c₁
  exact hconst.add hlin

/-- The payoff integrand of any linear schedule is integrable against the prior: It is a quadratic
in jointly Gaussian types, which has all moments finite. -/
lemma integrable_payoff_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) (i : Fin 2) :
    Integrable (fun θ => (game a μ₀ hv₀ hv).payoff i
      ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) θ)
      (game a μ₀ hv₀ hv).prior := by
  -- `ENNReal.HolderTriple (2, 2, 1)` patches a likely Mathlib gap: no named instance for this
  -- exponent triple ships with Mathlib, so we provide it inline.
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  rw [game_prior]
  -- Each firm `j` plays the affine schedule `α j + β j · θ j`, which is in L².
  have hq0 : MemLp (fun θ : Fin 2 → ℝ => α 0 + β 0 * θ 0) 2
      (prior μ₀ hv₀ hv) := memLp_affine_eval_two_prior μ₀ hv₀ hv 0 _ _
  have hq1 : MemLp (fun θ : Fin 2 → ℝ => α 1 + β 1 * θ 1) 2
      (prior μ₀ hv₀ hv) := memLp_affine_eval_two_prior μ₀ hv₀ hv 1 _ _
  -- The own quantity `q i`, the inverse-demand factor `a - q 0 - q 1`, and the own cost `θ i` are
  -- all square-integrable, so the products entering the payoff are integrable (L²·L² ⊆ L¹).
  have hqi : MemLp (fun θ : Fin 2 → ℝ => α i + β i * θ i) 2
      (prior μ₀ hv₀ hv) := memLp_affine_eval_two_prior μ₀ hv₀ hv i _ _
  have hθi : MemLp (fun θ : Fin 2 → ℝ => θ i) 2 (prior μ₀ hv₀ hv) :=
    memLp_eval_two_prior μ₀ hv₀ hv i
  have hdemand : MemLp (fun θ : Fin 2 → ℝ =>
      a - (α 0 + β 0 * θ 0) - (α 1 + β 1 * θ 1)) 2 (prior μ₀ hv₀ hv) :=
    ((memLp_const a).sub hq0).sub hq1
  -- `q i · (a - q 0 - q 1)` and `θ i · q i` are each in L¹.
  have hrev : MemLp (fun θ : Fin 2 → ℝ =>
      (α i + β i * θ i)
        * (a - (α 0 + β 0 * θ 0) - (α 1 + β 1 * θ 1))) 1 (prior μ₀ hv₀ hv) :=
    hdemand.mul' hqi
  have hcost : MemLp (fun θ : Fin 2 → ℝ =>
      θ i * (α i + β i * θ i)) 1 (prior μ₀ hv₀ hv) :=
    hqi.mul' hθi
  have hmem : MemLp (fun θ : Fin 2 → ℝ =>
      (α i + β i * θ i)
        * (a - (α 0 + β 0 * θ 0) - (α 1 + β 1 * θ 1))
      - θ i * (α i + β i * θ i)) 1 (prior μ₀ hv₀ hv) :=
    hrev.sub hcost
  have hpayoff : (fun θ : Fin 2 → ℝ => (game a μ₀ hv₀ hv).payoff i
      ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) θ)
      = fun θ : Fin 2 → ℝ =>
        (α i + β i * θ i)
          * (a - (α 0 + β 0 * θ 0) - (α 1 + β 1 * θ 1))
        - θ i * (α i + β i * θ i) := by
    funext θ
    simp only [MeasBayesianGame.actionProfile_apply, linearStrategyOf_apply]
  rw [hpayoff]
  exact hmem.integrable le_rfl

/-- The equilibrium payoff integrand is integrable against the prior, the `coeffA`/`coeffB`
instance of `integrable_payoff_lin`. -/
lemma integrable_equilibrium_payoff (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2) :
    Integrable (fun θ => (game a μ₀ hv₀ hv).payoff i
      ((game a μ₀ hv₀ hv).actionProfile (linearStrategy a μ₀ hv₀ hv) θ) θ)
      (game a μ₀ hv₀ hv).prior :=
  integrable_payoff_lin a μ₀ hv₀ hv (coeffA a μ₀ v₀ v) (coeffB v₀ v) i

/-! ### The interim best response and the equilibrium theorem -/

/-- **Firm 0's a.e. interim best response.** Almost every type plays an interim best response: The
deviation payoff `b·(K₀ − b)` is maximized at `b = K₀/2 = q₀(θ₀)` by `foc_zero`, and concavity
gives `(K₀/2 − b)² ≥ 0`. -/
lemma ae_interim_best_response_zero (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType 0), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoff 0 θ_i (linearStrategy a μ₀ hv₀ hv) ≥
        (game a μ₀ hv₀ hv).interimPayoffAction 0 θ_i b (linearStrategy a μ₀ hv₀ hv) := by
  have hself := (game a μ₀ hv₀ hv).interimPayoff_ae_eq_interimPayoffAction 0
    (linearStrategy a μ₀ hv₀ hv) (linearStrategy a μ₀ hv₀ hv) (fun _ _ => rfl)
  filter_upwards [hself, interimPayoffAction_zero a μ₀ hv₀ hv] with θ₀ hself0 haction0
  intro b
  rw [hself0]
  simp only [haction0, linearStrategy_apply]
  have hfoc := foc_zero a μ₀ hv₀ hv θ₀
  nlinarith [sq_nonneg ((a - (coeffA a μ₀ v₀ v 1 + coeffB v₀ v 1 * θ₀) - θ₀) / 2 - b), hfoc]

/-- **Firm 1's a.e. interim best response.** Analogous to firm 0, with the posterior mean `μ⋆(θ₁)`
and `foc_one`. -/
lemma ae_interim_best_response_one (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType 1), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoff 1 θ_i (linearStrategy a μ₀ hv₀ hv) ≥
        (game a μ₀ hv₀ hv).interimPayoffAction 1 θ_i b (linearStrategy a μ₀ hv₀ hv) := by
  have hself := (game a μ₀ hv₀ hv).interimPayoff_ae_eq_interimPayoffAction 1
    (linearStrategy a μ₀ hv₀ hv) (linearStrategy a μ₀ hv₀ hv) (fun _ _ => rfl)
  filter_upwards [hself, interimPayoffAction_one a μ₀ hv₀ hv] with θ₁ hself1 haction1
  intro b
  rw [hself1]
  simp only [haction1, linearStrategy_apply]
  have hfoc := foc_one a μ₀ hv₀ hv θ₁
  nlinarith [sq_nonneg ((a - (coeffA a μ₀ v₀ v 0 +
    coeffB v₀ v 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) / 2 - b), hfoc]

/-- **Per-player a.e. interim best response**, assembled over the two firms. -/
lemma ae_interim_best_response (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType i), ∀ b : ℝ,
      (game a μ₀ hv₀ hv).interimPayoff i θ_i (linearStrategy a μ₀ hv₀ hv) ≥
        (game a μ₀ hv₀ hv).interimPayoffAction i θ_i b (linearStrategy a μ₀ hv₀ hv) := by
  fin_cases i
  · exact ae_interim_best_response_zero a μ₀ hv₀ hv
  · exact ae_interim_best_response_one a μ₀ hv₀ hv

/-- **The linear schedule is a Bayes–Nash equilibrium.** The correlated-Gaussian Cournot duopoly's
linear strategy `qᵢ(θᵢ) = αᵢ + βᵢ·θᵢ` is a Bayes–Nash equilibrium in the canonical
`MeasBayesianGame.IsBNE` sense, established through the interim characterization. -/
theorem linearStrategy_isBNE (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).IsBNE (linearStrategy a μ₀ hv₀ hv) :=
  (game a μ₀ hv₀ hv).isBNE_of_ae_interim (linearStrategy a μ₀ hv₀ hv)
    (integrable_equilibrium_payoff a μ₀ hv₀ hv)
    (ae_interim_best_response a μ₀ hv₀ hv)

/-! ### Uniqueness among linear strategies

We now show that the linear schedule we constructed is the *only* linear Bayes–Nash
equilibrium: Any strategy profile of the form `qᵢ(θᵢ) = αᵢ + βᵢθᵢ` that is a BNE must have the
closed-form coefficients `coeffA`, `coeffB`. This is **uniqueness within the linear class only** —
it says nothing about non-linear equilibria, whose conditional-expectation best-response operator
need not preserve affinity. The argument runs the existence proof in reverse: BNE ⇒ a.e. interim
best response (`MeasBayesianGame.ae_interim_of_isBNE`); strict concavity of the quadratic interim
objective forces each type onto the unique best response (the interim first-order condition);
matching the resulting affine identity coefficient-by-coefficient under the nondegenerate Gaussian
marginals (`affine_eq_of_ae_eq_gaussianReal`) yields a linear system whose unique solution is
`coeffA`, `coeffB`. -/

/-- Firm 0's deviation-payoff integrability against the Gaussian conditional belief at a general
linear profile: The deviation integrand is affine in the opponent's coordinate `θ 1`, hence
integrable. Supplies one firm of the `MeasBayesianGame.ae_interim_of_isBNE` guard. -/
lemma deviation_integrable_zero_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType 0), ∀ b : ℝ,
      Integrable (fun θ => (game a μ₀ hv₀ hv).payoff 0
        (Function.update
          ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) 0 b) θ)
        ((game a μ₀ hv₀ hv).condProfile 0 θ_i) := by
  -- On the fiber `θ 0 = θ₀` the integrand equals `b·(a − b − (α₁+β₁θ₁)) − θ₀·b`, affine in `θ 1`.
  filter_upwards [(game a μ₀ hv₀ hv).ae_condProfile_eval 0, condProfile_map_eval_zero a μ₀ hv₀ hv]
    with θ₀ hfiber hmap b
  haveI : IsProbabilityMeasure ((game a μ₀ hv₀ hv).condProfile 0 θ₀) := by
    unfold MeasBayesianGame.condProfile; infer_instance
  have hinteg : Integrable (fun θ : Fin 2 → ℝ => θ 1) ((game a μ₀ hv₀ hv).condProfile 0 θ₀) :=
    integrable_eval_of_map_gaussian 1 hmap
  have hbase : Integrable
      (fun θ : Fin 2 → ℝ => (b * (a - b) - θ₀ * b - b * α 1) + (-(b * β 1)) * θ 1)
      ((game a μ₀ hv₀ hv).condProfile 0 θ₀) :=
    (integrable_const _).add (hinteg.const_mul _)
  refine hbase.congr ?_
  filter_upwards [hfiber] with θ hθ
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    MeasBayesianGame.actionProfile_apply, linearStrategyOf_apply, hθ]
  ring

/-- Firm 1's deviation-payoff integrability against the Gaussian conditional belief at a general
linear profile: The deviation integrand is affine in the opponent's coordinate `θ 0`, hence
integrable. Supplies the other firm of the `MeasBayesianGame.ae_interim_of_isBNE` guard. -/
lemma deviation_integrable_one_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType 1), ∀ b : ℝ,
      Integrable (fun θ => (game a μ₀ hv₀ hv).payoff 1
        (Function.update
          ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) 1 b) θ)
        ((game a μ₀ hv₀ hv).condProfile 1 θ_i) := by
  -- On the fiber `θ 1 = θ₁` the integrand is affine in the opponent coordinate `θ 0`.
  filter_upwards [(game a μ₀ hv₀ hv).ae_condProfile_eval 1, condProfile_map_eval_one a μ₀ hv₀ hv]
    with θ₁ hfiber hmap b
  haveI : IsProbabilityMeasure ((game a μ₀ hv₀ hv).condProfile 1 θ₁) := by
    unfold MeasBayesianGame.condProfile; infer_instance
  have hinteg : Integrable (fun θ : Fin 2 → ℝ => θ 0) ((game a μ₀ hv₀ hv).condProfile 1 θ₁) :=
    integrable_eval_of_map_gaussian 0 hmap
  have hbase : Integrable
      (fun θ : Fin 2 → ℝ => (b * (a - b) - θ₁ * b - b * α 0) + (-(b * β 0)) * θ 0)
      ((game a μ₀ hv₀ hv).condProfile 1 θ₁) :=
    (integrable_const _).add (hinteg.const_mul _)
  refine hbase.congr ?_
  filter_upwards [hfiber] with θ hθ
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    MeasBayesianGame.actionProfile_apply, linearStrategyOf_apply, hθ]
  ring

/-- The deviation-payoff integrability guard for `MeasBayesianGame.ae_interim_of_isBNE` at a
general linear profile, assembled over the two firms from `deviation_integrable_zero_lin` and
`deviation_integrable_one_lin`. -/
lemma deviation_integrable_lin (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ) (i : Fin 2) :
    ∀ᵐ θ_i ∂((game a μ₀ hv₀ hv).marginalType i), ∀ b : ℝ,
      Integrable (fun θ => (game a μ₀ hv₀ hv).payoff i
        (Function.update
          ((game a μ₀ hv₀ hv).actionProfile (linearStrategyOf a μ₀ α β hv₀ hv) θ) i b) θ)
        ((game a μ₀ hv₀ hv).condProfile i θ_i) := by
  fin_cases i
  · exact deviation_integrable_zero_lin a μ₀ hv₀ hv α β
  · exact deviation_integrable_one_lin a μ₀ hv₀ hv α β

/-- **Uniqueness among linear strategies.** Any linear schedule `qᵢ(θᵢ) = αᵢ + βᵢθᵢ` that is a
Bayes–Nash equilibrium of the correlated-Gaussian Cournot game has the closed-form coefficients
`coeffA`, `coeffB`. (Scope: Linear strategies only.) -/
theorem linearBNE_coeffs_unique (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ)
    (hbne : (game a μ₀ hv₀ hv).IsBNE (linearStrategyOf a μ₀ α β hv₀ hv)) :
    α = coeffA a μ₀ v₀ v ∧ β = coeffB v₀ v := by
  have hS : (v₀ + v) ≠ 0 := by positivity
  have hD : (3 * v₀ + 4 * v) ≠ 0 := by positivity
  -- BNE ⇒ a.e. interim best response (necessity), discharging the deviation-integrability guard.
  have hbr := (game a μ₀ hv₀ hv).ae_interim_of_isBNE (linearStrategyOf a μ₀ α β hv₀ hv) hbne
    (deviation_integrable_lin a μ₀ hv₀ hv α β)
  -- The two marginal types are the Gaussian prior marginals `N(μ₀, v₀)` and `N(μ₀, v₀+v)`.
  have hmarg0 := marginalType_zero a μ₀ hv₀ hv
  have hmarg1 := marginalType_one a μ₀ hv₀ hv
  -- Firm 0's interim FOC, a.e.: the strategy plays the unique maximizer `K₀/2` of `b ↦ b(K₀−b)`.
  have hfoc0 : ∀ᵐ θ₀ ∂((game a μ₀ hv₀ hv).marginalType 0),
      α 0 + β 0 * θ₀ = (a - (α 1 + β 1 * θ₀) - θ₀) / 2 := by
    have hself := (game a μ₀ hv₀ hv).interimPayoff_ae_eq_interimPayoffAction 0
      (linearStrategyOf a μ₀ α β hv₀ hv) (linearStrategyOf a μ₀ α β hv₀ hv) (fun _ _ => rfl)
    filter_upwards [hbr 0, hself, interimPayoffAction_zero_lin a μ₀ hv₀ hv α β]
      with θ₀ hbrθ hselfθ hactθ
    have hmax := hbrθ ((a - (α 1 + β 1 * θ₀) - θ₀) / 2)
    rw [hselfθ] at hmax
    simp only [linearStrategyOf_apply, hactθ] at hmax
    have hle : (α 0 + β 0 * θ₀ - (a - (α 1 + β 1 * θ₀) - θ₀) / 2) ^ 2 ≤ 0 := by nlinarith [hmax]
    have hz := sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
    linarith
  -- Firm 1's interim FOC, a.e., with the conjugate posterior mean `μ⋆(θ₁)`.
  have hfoc1 : ∀ᵐ θ₁ ∂((game a μ₀ hv₀ hv).marginalType 1),
      α 1 + β 1 * θ₁ = (a - (α 0 + β 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) / 2 := by
    have hself := (game a μ₀ hv₀ hv).interimPayoff_ae_eq_interimPayoffAction 1
      (linearStrategyOf a μ₀ α β hv₀ hv) (linearStrategyOf a μ₀ α β hv₀ hv) (fun _ _ => rfl)
    filter_upwards [hbr 1, hself, interimPayoffAction_one_lin a μ₀ hv₀ hv α β]
      with θ₁ hbrθ hselfθ hactθ
    have hmax := hbrθ ((a - (α 0 + β 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) / 2)
    rw [hselfθ] at hmax
    simp only [linearStrategyOf_apply, hactθ] at hmax
    have hle : (α 1 + β 1 * θ₁
        - (a - (α 0 + β 0 * gaussianPosteriorMean μ₀ v₀ v θ₁) - θ₁) / 2) ^ 2 ≤ 0 := by
      nlinarith [hmax]
    have hz := sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
    linarith
  -- Identify the affine coefficients of each FOC under the nondegenerate Gaussian marginals.
  have hcoef0 : α 0 = (a - α 1) / 2 ∧ β 0 = (-1 - β 1) / 2 := by
    have hae : (fun t : ℝ => α 0 + β 0 * t)
        =ᵐ[(game a μ₀ hv₀ hv).marginalType 0]
        fun t : ℝ => (a - α 1) / 2 + ((-1 - β 1) / 2) * t := by
      filter_upwards [hfoc0] with θ₀ hθ
      show α 0 + β 0 * θ₀ = (a - α 1) / 2 + ((-1 - β 1) / 2) * θ₀
      rw [hθ]; ring
    rw [hmarg0] at hae
    exact affine_eq_of_ae_eq_gaussianReal (gaussianVarianceNNReal_ne_zero v₀ hv₀) hae
  have hcoef1 : α 1 = (a - α 0 - β 0 * (v * μ₀ / (v₀ + v))) / 2
      ∧ β 1 = (-(β 0 * (v₀ / (v₀ + v))) - 1) / 2 := by
    have hae : (fun t : ℝ => α 1 + β 1 * t)
        =ᵐ[(game a μ₀ hv₀ hv).marginalType 1]
        fun t : ℝ => ((a - α 0 - β 0 * (v * μ₀ / (v₀ + v))) / 2)
          + ((-(β 0 * (v₀ / (v₀ + v))) - 1) / 2) * t := by
      filter_upwards [hfoc1] with θ₁ hθ
      show α 1 + β 1 * θ₁ = _
      rw [hθ, gaussianPosteriorMean]
      field_simp
      ring
    rw [hmarg1] at hae
    exact affine_eq_of_ae_eq_gaussianReal
      (gaussianVarianceNNReal_ne_zero (v₀ + v) (by positivity)) hae
  obtain ⟨hα0, hβ0⟩ := hcoef0
  obtain ⟨hα1, hβ1eq⟩ := hcoef1
  -- Solve the 4×4 linear system. Slopes first (decoupled from intercepts), then intercepts.
  have hβ1 : β 1 = -(v₀ + 2 * v) / (3 * v₀ + 4 * v) := by
    rw [hβ0] at hβ1eq
    field_simp at hβ1eq
    field_simp
    nlinarith [hβ1eq]
  have hβ0' : β 0 = -(v₀ + v) / (3 * v₀ + 4 * v) := by
    rw [hβ0, hβ1]; field_simp; ring
  have hα1' : α 1 = a / 3 + 2 * v * μ₀ / (3 * (3 * v₀ + 4 * v)) := by
    rw [hα0, hβ0'] at hα1
    field_simp at hα1
    field_simp
    nlinarith [hα1]
  have hα0' : α 0 = (a - (a / 3 + 2 * v * μ₀ / (3 * (3 * v₀ + 4 * v)))) / 2 := by
    rw [hα0, hα1']
  -- Read off `α = coeffA`, `β = coeffB`.
  have ha0 : α 0 = coeffA a μ₀ v₀ v 0 := by
    simp only [coeffA, Matrix.cons_val_zero]; exact hα0'
  have ha1 : α 1 = coeffA a μ₀ v₀ v 1 := by
    simp only [coeffA, Matrix.cons_val_one]; exact hα1'
  have hb0 : β 0 = coeffB v₀ v 0 := by
    simp only [coeffB, Matrix.cons_val_zero]; exact hβ0'
  have hb1 : β 1 = coeffB v₀ v 1 := by
    simp only [coeffB, Matrix.cons_val_one]; exact hβ1
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · fin_cases i
    · exact ha0
    · exact ha1
  · fin_cases i
    · exact hb0
    · exact hb1

/-- **The constructed schedule is the unique linear equilibrium.** Any linear Bayes–Nash
equilibrium of the correlated-Gaussian Cournot game coincides with `linearStrategy`. (Scope: Linear
strategies only.) -/
theorem linearStrategy_unique_of_isBNE (hv₀ : 0 < v₀) (hv : 0 < v) (α β : Fin 2 → ℝ)
    (hbne : (game a μ₀ hv₀ hv).IsBNE (linearStrategyOf a μ₀ α β hv₀ hv)) :
    linearStrategyOf a μ₀ α β hv₀ hv = linearStrategy a μ₀ hv₀ hv := by
  obtain ⟨hα, hβ⟩ := linearBNE_coeffs_unique a μ₀ hv₀ hv α β hbne
  rw [linearStrategy, hα, hβ]

end CorrelatedCournot

end
