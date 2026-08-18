/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Conditioning
public import Econlib.Probability.Distributions.Gaussian

/-!
# Normal-normal conjugate updating

The Gaussian family is self-conjugate for the Gaussian location likelihood: With prior
`θ ~ N(μ₀, v₀)` and signal `x ∣ θ ~ N(θ, v)`, the posterior is again Gaussian,

`θ ∣ x ~ N(μ⋆, v⋆)`,  `μ⋆ = (v·μ₀ + v₀·x) / (v₀ + v)`,  `v⋆ = v₀·v / (v₀ + v)`,

i.e. in precision form: The posterior mean is the precision-weighted average of prior mean and
signal, `μ⋆ = (τ₀·μ₀ + τ·x) / (τ₀ + τ)`, and the posterior precision is the sum of the precisions,
`1/v⋆ = τ₀ + τ` (`τ₀ = 1/v₀`, `τ = 1/v`). This is the workhorse closed form of signal extraction in
information economics (Kalman filtering, reputation, global games).

Everything follows from one algebraic identity on Gaussian densities, the **factorization of the
joint** into prior-predictive and posterior,

`N(θ; μ₀, v₀) · N(x; θ, v) = N(x; μ₀, v₀ + v) · N(θ; μ⋆, v⋆)`.

Integrating over `θ` gives the evidence (the prior-predictive density `N(x; μ₀, v₀ + v)`), and
Bayes' rule (`ContDist.posterior`) then gives the posterior.

## Main definitions

* `gaussianPosteriorMean` — `μ⋆`, the precision-weighted average of prior mean and signal.
* `gaussianPosteriorVariance` — `v⋆`, the inverse of the summed precisions.

## Main statements

* `gaussianPDFReal_mul_factorization` — the joint factorizes as prior-predictive × posterior.
* `ContDist.gaussian_likelihood_integrable` — the prior-weighted likelihood is integrable.
* `ContDist.gaussian_evidence` — the evidence is the prior-predictive density `N(x; μ₀, v₀ + v)`.
* `ContDist.gaussian_posterior` — Bayes' rule maps Gaussian prior and likelihood to the Gaussian
  posterior `N(μ⋆, v⋆)`.
* `ContDist.gaussian_posterior_expect`, `ContDist.gaussian_posterior_variance` — the posterior
  moment closed forms.
* `ContDist.gaussianPosterior` — the bundled posterior: Sugar over `ContDist.posterior` with the
  Bayes side conditions discharged internally, with `gaussianPosterior_eq`, `_density`, `_expect`,
  `_variance` re-exposing the closed forms through the bundle.
* `gaussianPosteriorVariance_lt_left`, `gaussianPosteriorVariance_lt_right` — observing a signal
  strictly reduces variance below both the prior's and the signal's.
* `gaussianPosteriorMean_strictAnti_var` — a more precise signal (smaller `v`) moves the posterior
  mean strictly further toward the signal.

## Tags

gaussian, normal, conjugate prior, bayesian updating, posterior, signal extraction, precision
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.Probability

/-! ### The posterior parameters -/

/-- Posterior mean of normal-normal updating: The precision-weighted average
`(v·μ₀ + v₀·x) / (v₀ + v)` of the prior mean `μ₀` and the signal `x`. -/
noncomputable def gaussianPosteriorMean (μ₀ v₀ v x : ℝ) : ℝ :=
  (v * μ₀ + v₀ * x) / (v₀ + v)

/-- Posterior variance of normal-normal updating: `v₀·v / (v₀ + v)`, the inverse of the summed
precisions `1/v₀ + 1/v`. -/
noncomputable def gaussianPosteriorVariance (v₀ v : ℝ) : ℝ :=
  v₀ * v / (v₀ + v)

/-- The posterior variance `v₀·v / (v₀ + v)` is positive for positive prior and signal variances. -/
lemma gaussianPosteriorVariance_pos {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    0 < gaussianPosteriorVariance v₀ v := by
  unfold gaussianPosteriorVariance; positivity

/-- Precision form of the posterior mean: The precisions `1/v₀` and `1/v` weight the prior mean and
the signal. -/
lemma gaussianPosteriorMean_eq_precision (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosteriorMean μ₀ v₀ v x = ((1 / v₀) * μ₀ + (1 / v) * x) / (1 / v₀ + 1 / v) := by
  unfold gaussianPosteriorMean
  field_simp
  ring

/-- Precision form of the posterior variance: The posterior precision is the sum of the prior and
signal precisions. -/
lemma gaussianPosteriorVariance_eq_precision {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosteriorVariance v₀ v = (1 / v₀ + 1 / v)⁻¹ := by
  unfold gaussianPosteriorVariance
  field_simp
  ring

/-- Shrinkage form of the posterior mean: The prior mean moved toward the signal by the weight
`v₀ / (v₀ + v)`. -/
lemma gaussianPosteriorMean_eq_shrinkage (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosteriorMean μ₀ v₀ v x = μ₀ + (v₀ / (v₀ + v)) * (x - μ₀) := by
  unfold gaussianPosteriorMean
  field_simp
  ring

/-- **Learning reduces variance below the prior's:** `v⋆ < v₀`. -/
lemma gaussianPosteriorVariance_lt_left {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosteriorVariance v₀ v < v₀ := by
  -- `v₀·v/(v₀+v) < v₀ ⟺ v₀·v < v₀·(v₀+v) ⟺ 0 < v₀²`.
  unfold gaussianPosteriorVariance
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hv₀ hv₀]

/-- **The posterior is sharper than the signal:** `v⋆ < v`. -/
lemma gaussianPosteriorVariance_lt_right {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosteriorVariance v₀ v < v := by
  -- `v₀·v/(v₀+v) < v ⟺ v₀·v < v·(v₀+v) ⟺ 0 < v²`.
  unfold gaussianPosteriorVariance
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hv hv]

/-- **More precise signals move the posterior more.** When the signal exceeds the prior mean, the
posterior mean is strictly decreasing in the signal variance `v` — shrinking `v` (raising the
signal precision) pulls the posterior mean strictly closer to the signal. -/
lemma gaussianPosteriorMean_strictAnti_var (μ₀ x : ℝ) {v₀ : ℝ} (hv₀ : 0 < v₀) (hx : μ₀ < x) :
    StrictAntiOn (fun v => gaussianPosteriorMean μ₀ v₀ v x) (Set.Ioi 0) := by
  intro v₁ hv₁ v₂ hv₂ h12
  have hv₁_pos : 0 < v₁ := hv₁
  have hv₂_pos : 0 < v₂ := hv₂
  simp only [gaussianPosteriorMean]
  -- Cross-multiplied difference is `v₀·(x-μ₀)·(v₂-v₁) > 0`.
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (mul_pos hv₀ (sub_pos.mpr hx)) (sub_pos.mpr h12)]

/-! ### The factorization identity -/

/-- **The normal-normal joint factorizes as prior-predictive × posterior:**
`N(θ; μ₀, v₀) · N(x; θ, v) = N(x; μ₀, v₀ + v) · N(θ; μ⋆, v⋆)`. -/
lemma gaussianPDFReal_mul_factorization (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v)
    (θ : ℝ) :
    gaussianPDFReal μ₀ (gaussianVarianceNNReal v₀ hv₀) θ *
        gaussianPDFReal θ (gaussianVarianceNNReal v hv) x =
      gaussianPDFReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) x *
        gaussianPDFReal (gaussianPosteriorMean μ₀ v₀ v x)
          (gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
            (gaussianPosteriorVariance_pos hv₀ hv)) θ := by
  set vstar := gaussianPosteriorVariance v₀ v with hvstar_def
  set mustar := gaussianPosteriorMean μ₀ v₀ v x with hmustar_def
  have hsum_pos : 0 < v₀ + v := by positivity
  have hvstar_pos : 0 < vstar := gaussianPosteriorVariance_pos hv₀ hv
  -- Normalizing-constant identity: `v₀ · v = (v₀ + v) · vstar`.
  have h_radicand : v₀ * v = (v₀ + v) * vstar := by
    rw [hvstar_def]; unfold gaussianPosteriorVariance; field_simp
  -- The product of normalizing constants matches because the radicands agree.
  have h_const : (Real.sqrt (2 * Real.pi * v₀))⁻¹ * (Real.sqrt (2 * Real.pi * v))⁻¹ =
      (Real.sqrt (2 * Real.pi * (v₀ + v)))⁻¹ * (Real.sqrt (2 * Real.pi * vstar))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 2
    linear_combination (2 * Real.pi) ^ 2 * h_radicand
  -- Exponent identity by completing the square.
  have h_exp : -(θ - μ₀) ^ 2 / (2 * v₀) + -(x - θ) ^ 2 / (2 * v) =
      -(x - μ₀) ^ 2 / (2 * (v₀ + v)) + -(θ - mustar) ^ 2 / (2 * vstar) := by
    rw [hmustar_def, hvstar_def]
    unfold gaussianPosteriorMean gaussianPosteriorVariance
    field_simp
    ring
  unfold gaussianPDFReal
  rw [gaussianVarianceNNReal_coe, gaussianVarianceNNReal_coe, gaussianVarianceNNReal_coe,
    gaussianVarianceNNReal_coe]
  rw [mul_mul_mul_comm, ← Real.exp_add, h_const, h_exp, Real.exp_add, mul_mul_mul_comm]

/-! ### Bayes' rule for the Gaussian family -/

namespace ContDist

/-- The Gaussian prior-weighted likelihood is integrable in the state: By the factorization
identity it is a constant multiple of the posterior Gaussian density. -/
lemma gaussian_likelihood_integrable (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    Integrable (fun θ =>
      (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x) := by
  -- The factorization rewrites the integrand as `evidence · (posterior density)`.
  have h_eq : (fun θ => (ContDist.gaussian μ₀ v₀ hv₀).density θ *
        (ContDist.gaussian θ v hv).density x) =
      fun θ => gaussianPDFReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) x *
        (ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
          (gaussianPosteriorVariance_pos hv₀ hv)).density θ := by
    funext θ
    simp only [ContDist.gaussian_density]
    exact gaussianPDFReal_mul_factorization μ₀ x hv₀ hv θ
  rw [h_eq]
  exact (ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
    (gaussianPosteriorVariance_pos hv₀ hv)).integrable.const_mul _

/-- **The evidence is the prior-predictive density:** integrating the prior-weighted likelihood
over the state gives `N(x; μ₀, v₀ + v)` — the marginal (prior-predictive) law of the signal. -/
lemma gaussian_evidence (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    (∫ θ, (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x) =
      (ContDist.gaussian μ₀ (v₀ + v) (by positivity)).density x := by
  -- The factorization rewrites the integrand as `evidence · (posterior density)`; the posterior
  -- density integrates to one, leaving the evidence (the prior-predictive density).
  have h_eq : (fun θ => (ContDist.gaussian μ₀ v₀ hv₀).density θ *
        (ContDist.gaussian θ v hv).density x) =
      fun θ => (ContDist.gaussian μ₀ (v₀ + v) (by positivity)).density x *
        (ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
          (gaussianPosteriorVariance_pos hv₀ hv)).density θ := by
    funext θ
    simp only [ContDist.gaussian_density]
    exact gaussianPDFReal_mul_factorization μ₀ x hv₀ hv θ
  rw [h_eq, integral_const_mul,
    (ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
      (gaussianPosteriorVariance_pos hv₀ hv)).integral_one, mul_one]

/-- The Gaussian prior-predictive evidence is strictly positive, so the Bayesian
`ContDist.posterior` is always available for the normal-normal model. -/
theorem gaussian_evidence_pos (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    0 < ∫ θ', (ContDist.gaussian μ₀ v₀ hv₀).density θ' *
      (ContDist.gaussian θ' v hv).density x := by
  have h_evid : (∫ θ', (ContDist.gaussian μ₀ v₀ hv₀).density θ' *
        (ContDist.gaussian θ' v hv).density x) =
      gaussianPDFReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) x :=
    gaussian_evidence μ₀ x hv₀ hv
  rw [h_evid]
  exact gaussianPDFReal_pos _ _ _ (gaussianVarianceNNReal_ne_zero _ _)

/-- **Normal-normal conjugate updating.** Bayes' rule (`ContDist.posterior`) applied to the
Gaussian prior `N(μ₀, v₀)` and the Gaussian location likelihood `x ∣ θ ~ N(θ, v)` yields the
Gaussian posterior `N(μ⋆, v⋆)` with precision-weighted mean `μ⋆ = (v·μ₀ + v₀·x) / (v₀ + v)` and
summed-precision variance `v⋆ = v₀·v / (v₀ + v)`. -/
theorem gaussian_posterior (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v)
    (h_nn : ∀ θ, 0 ≤ (ContDist.gaussian θ v hv).density x)
    (h_int : Integrable (fun θ =>
      (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x)) :
    (ContDist.gaussian μ₀ v₀ hv₀).posterior
        (fun θ s => (ContDist.gaussian θ v hv).density s) x h_nn h_int
        (gaussian_evidence_pos μ₀ x hv₀ hv) =
      ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
        (gaussianPosteriorVariance_pos hv₀ hv) := by
  -- The evidence is the positive prior-predictive density, so Bayes' rule applies.
  have h_evid : (∫ θ', (ContDist.gaussian μ₀ v₀ hv₀).density θ' *
        (ContDist.gaussian θ' v hv).density x) =
      gaussianPDFReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) x :=
    gaussian_evidence μ₀ x hv₀ hv
  have h_evid_pos : 0 < gaussianPDFReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) x :=
    gaussianPDFReal_pos _ _ _ (gaussianVarianceNNReal_ne_zero _ _)
  have h_denom : 0 < ∫ θ', (ContDist.gaussian μ₀ v₀ hv₀).density θ' *
      (ContDist.gaussian θ' v hv).density x := gaussian_evidence_pos μ₀ x hv₀ hv
  -- Match densities pointwise: `(evidence · posterior θ) / evidence = posterior θ`.
  ext θ
  rw [ContDist.posterior_density _ _ _ _ h_nn h_int h_denom, h_evid,
    ContDist.gaussian_density, ContDist.gaussian_density, ContDist.gaussian_density,
    gaussianPDFReal_mul_factorization μ₀ x hv₀ hv θ, mul_div_cancel_left₀ _ h_evid_pos.ne']

/-- **Posterior mean closed form:** the precision-weighted average of prior mean and signal. -/
theorem gaussian_posterior_expect (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v)
    (h_nn : ∀ θ, 0 ≤ (ContDist.gaussian θ v hv).density x)
    (h_int : Integrable (fun θ =>
      (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x)) :
    ((ContDist.gaussian μ₀ v₀ hv₀).posterior
        (fun θ s => (ContDist.gaussian θ v hv).density s) x h_nn h_int
        (gaussian_evidence_pos μ₀ x hv₀ hv)).expect id =
      gaussianPosteriorMean μ₀ v₀ v x := by
  rw [gaussian_posterior μ₀ x hv₀ hv h_nn h_int, ContDist.gaussian_expect]

/-- **Posterior variance closed form:** the inverse of the summed precisions — independent of the
observed signal. -/
theorem gaussian_posterior_variance (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v)
    (h_nn : ∀ θ, 0 ≤ (ContDist.gaussian θ v hv).density x)
    (h_int : Integrable (fun θ =>
      (ContDist.gaussian μ₀ v₀ hv₀).density θ * (ContDist.gaussian θ v hv).density x)) :
    ((ContDist.gaussian μ₀ v₀ hv₀).posterior
        (fun θ s => (ContDist.gaussian θ v hv).density s) x h_nn h_int
        (gaussian_evidence_pos μ₀ x hv₀ hv)).variance id =
      gaussianPosteriorVariance v₀ v := by
  rw [gaussian_posterior μ₀ x hv₀ hv h_nn h_int, ContDist.gaussian_variance]

/-! ### Bundled posterior

`gaussianPosterior` packages the unbundled `gaussian_posterior` together with its two Bayes
side conditions (density nonnegativity, integrability of the prior-weighted likelihood), discharged
internally. The closed forms `gaussianPosterior_eq`, `_density`, `_expect`, and `_variance`
re-expose the unbundled results through the bundle. -/

/-- **Bundled normal-normal posterior.** Sugar over `ContDist.posterior` for the Gaussian prior
`N(μ₀, v₀)` and Gaussian location likelihood `x ∣ θ ~ N(θ, v)`, with the two Bayes side conditions
(density nonnegativity, prior-weighted-likelihood integrability) discharged internally. By
`gaussianPosterior_eq` it equals the Gaussian posterior `N(μ⋆, v⋆)`. -/
noncomputable def gaussianPosterior (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) : ContDist :=
  (ContDist.gaussian μ₀ v₀ hv₀).posterior
    (fun θ s => (ContDist.gaussian θ v hv).density s) x
    (fun θ => (ContDist.gaussian θ v hv).nonneg x)
    (ContDist.gaussian_likelihood_integrable μ₀ x hv₀ hv)
    (gaussian_evidence_pos μ₀ x hv₀ hv)

/-- **The bundled posterior is the Gaussian posterior** `N(μ⋆, v⋆)`, exposing `gaussian_posterior`
through the bundle. -/
@[simp] theorem gaussianPosterior_eq (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianPosterior μ₀ x hv₀ hv =
      ContDist.gaussian (gaussianPosteriorMean μ₀ v₀ v x) (gaussianPosteriorVariance v₀ v)
        (gaussianPosteriorVariance_pos hv₀ hv) :=
  gaussian_posterior μ₀ x hv₀ hv _ _

/-- **The bundled posterior density** is the posterior Gaussian density `N(θ; μ⋆, v⋆)`. -/
theorem gaussianPosterior_density (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) (θ : ℝ) :
    (gaussianPosterior μ₀ x hv₀ hv).density θ =
      gaussianPDFReal (gaussianPosteriorMean μ₀ v₀ v x)
        (gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
          (gaussianPosteriorVariance_pos hv₀ hv)) θ := by
  rw [gaussianPosterior_eq, ContDist.gaussian_density]

/-- **Bundled posterior mean closed form:** the precision-weighted average of prior mean and
signal. -/
theorem gaussianPosterior_expect (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianPosterior μ₀ x hv₀ hv).expect id = gaussianPosteriorMean μ₀ v₀ v x := by
  rw [gaussianPosterior_eq, ContDist.gaussian_expect]

/-- **Bundled posterior variance closed form:** the inverse of the summed precisions — independent
of the observed signal. -/
theorem gaussianPosterior_variance (μ₀ x : ℝ) {v₀ v : ℝ} (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianPosterior μ₀ x hv₀ hv).variance id = gaussianPosteriorVariance v₀ v := by
  rw [gaussianPosterior_eq, ContDist.gaussian_variance]

end ContDist

end Econlib.Probability
