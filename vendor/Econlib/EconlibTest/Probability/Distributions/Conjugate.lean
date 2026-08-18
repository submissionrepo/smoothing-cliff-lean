/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Gaussian Conjugate / Conditional Non-Vacuity Checks

These are compile-time semantic witnesses for normal-normal conjugate updating
(`GaussianConjugate.lean`) and the conditional laws of the noisy-signal joint
(`GaussianConditional.lean`). The concrete parameters are chosen asymmetric (`v₀ ≠ v`,
`μ₀ ≠ x`) so a witness would catch a precision-weighting swap, a prior/predictive variance flip,
or a conditional-direction reversal.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.Conjugate

open Econlib.Probability MeasureTheory ProbabilityTheory

section posteriorParameters

/-- Posterior mean is the precision-weighted average `(v·μ₀ + v₀·x)/(v₀+v)`. With `μ₀ = 1`,
`v₀ = 3`, `v = 1`, `x = 5` this is `(1·1 + 3·5)/4 = 4`. Swapping the precisions `v` and `v₀` would
give `(3·1 + 1·5)/4 = 2`; equal-weighting the two would give `(1 + 5)/2 = 3`. So the anchor `4`
discriminates both error modes. -/
theorem gaussianPosteriorMean_one_three_one_five :
    gaussianPosteriorMean 1 3 1 5 = 4 := by
  norm_num [gaussianPosteriorMean]

/-- Posterior variance is `v₀·v/(v₀+v)`. With `v₀ = 3`, `v = 1` this is `3/4`. -/
theorem gaussianPosteriorVariance_three_one :
    gaussianPosteriorVariance 3 1 = 3 / 4 := by
  norm_num [gaussianPosteriorVariance]

/-- **Shrinkage reading:** with prior mean below the signal (`μ₀ = 1 < 5 = x`), the posterior mean
lands strictly between the two. -/
theorem gaussianPosteriorMean_between_prior_and_signal :
    (1 : ℝ) < gaussianPosteriorMean 1 3 1 5 ∧ gaussianPosteriorMean 1 3 1 5 < 5 := by
  rw [gaussianPosteriorMean_one_three_one_five]; norm_num

/-- **Learning reduces variance below the prior's:** `v⋆ < v₀`. -/
theorem gaussianPosteriorVariance_lt_prior :
    gaussianPosteriorVariance 3 1 < 3 := by
  simpa using gaussianPosteriorVariance_lt_left (v₀ := 3) (v := 1) (by norm_num) (by norm_num)

/-- **The posterior is sharper than the signal:** `v⋆ < v`. -/
theorem gaussianPosteriorVariance_lt_signal :
    gaussianPosteriorVariance 3 1 < 1 := by
  simpa using gaussianPosteriorVariance_lt_right (v₀ := 3) (v := 1) (by norm_num) (by norm_num)

end posteriorParameters

section bundledPosterior

/-- **Bundled posterior mean closed form:** the precision-weighted average. With `μ₀ = 1`,
`v₀ = 3`, `v = 1`, `x = 5` the posterior expectation is `4`. -/
theorem gaussianPosterior_one_three_one_five_expect :
    (ContDist.gaussianPosterior 1 5 (v₀ := 3) (v := 1) (by norm_num) (by norm_num)).expect id =
      4 := by
  rw [ContDist.gaussianPosterior_expect, gaussianPosteriorMean_one_three_one_five]

/-- **Bundled posterior variance closed form:** the summed-precision inverse `v⋆ = 3/4`,
independent of the observed signal. -/
theorem gaussianPosterior_one_three_one_five_variance :
    (ContDist.gaussianPosterior 1 5 (v₀ := 3) (v := 1) (by norm_num) (by norm_num)).variance id =
      3 / 4 := by
  rw [ContDist.gaussianPosterior_variance, gaussianPosteriorVariance_three_one]

/-- **The bundled posterior is the Gaussian posterior** `N(μ⋆, v⋆) = N(4, 3/4)`. -/
theorem gaussianPosterior_one_three_one_five_eq :
    ContDist.gaussianPosterior 1 5 (v₀ := 3) (v := 1) (by norm_num) (by norm_num) =
      ContDist.gaussian 4 (3 / 4) (by norm_num) := by
  rw [ContDist.gaussianPosterior_eq]
  congr 1
  · exact gaussianPosteriorMean_one_three_one_five
  · exact gaussianPosteriorVariance_three_one

end bundledPosterior

section evidence

/-- **The evidence is the prior-predictive density** `N(x; μ₀, v₀ + v)`: with `μ₀ = 1`, `v₀ = 3`,
`v = 1` the marginal variance of the signal is `v₀ + v = 4`, not `v₀ = 3`. -/
theorem gaussian_evidence_one_three_one :
    (∫ θ, (ContDist.gaussian 1 3 (by norm_num)).density θ *
        (ContDist.gaussian θ 1 (by norm_num)).density 5) =
      (ContDist.gaussian 1 4 (by norm_num)).density 5 := by
  have h := ContDist.gaussian_evidence 1 5 (v₀ := 3) (v := 1) (by norm_num) (by norm_num)
  rw [h]; norm_num

end evidence

section conditionalLaws

/-- **First marginal of the noisy-signal joint** is the parameter prior `N(μ₀, v₀) = N(1, 3)` —
the prior variance `v₀ = 3`, not the prior-predictive `v₀ + v = 4`. -/
theorem gaussianNoisyLaw_one_three_one_map_fst :
    (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)).map Prod.fst =
      gaussianReal 1 (gaussianVarianceNNReal 3 (by norm_num)) :=
  gaussianNoisyLaw_map_fst 1 3 1 (by norm_num) (by norm_num)

/-- **Second marginal of the noisy-signal joint** is the prior-predictive `N(μ₀, v₀ + v) =
N(1, 4)` — the predictive variance `v₀ + v = 4`, picking up the signal noise. -/
theorem gaussianNoisyLaw_one_three_one_map_snd :
    (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)).map Prod.snd =
      gaussianReal 1 (gaussianVarianceNNReal 4 (by norm_num)) := by
  have h := gaussianNoisyLaw_map_snd 1 3 1 (by norm_num) (by norm_num)
  rw [h]; norm_num

/-- **The location kernel** `θ ↦ N(θ, v)` evaluates to the likelihood centered at the parameter:
at `θ = 7` it is `N(7, 1)`. -/
theorem locationKernel_one_at_seven :
    locationKernel 1 (by norm_num) 7 = gaussianReal 7 (gaussianVarianceNNReal 1 (by norm_num)) := by
  simp

/-- **The posterior kernel** `x ↦ N(μ⋆(x), v⋆)` centers at the posterior mean: at the signal
`x = 5` (with `μ₀ = 1`, `v₀ = 3`, `v = 1`) it is `N(4, 3/4)`. The RHS is restated with the explicit
numeric anchors `4` and `3/4` (rather than the parameter formulas) so a subtly wrong
`gaussianPosteriorMean`/`Variance` formula could not hide behind a shared definition on both
sides. -/
theorem posteriorKernel_one_three_one_at_five :
    posteriorKernel 1 3 1 (by norm_num) (by norm_num) 5 =
      gaussianReal 4 (gaussianVarianceNNReal (3 / 4) (by norm_num)) := by
  rw [posteriorKernel_apply]
  congr 1
  · exact gaussianPosteriorMean_one_three_one_five
  · congr 1
    exact gaussianPosteriorVariance_three_one

/-- **Forward conditional law `x ∣ θ` is the location kernel.** The conditional distribution of the
signal given the parameter is `θ ↦ N(θ, v) = locationKernel v`, a.e. under the parameter prior
`N(μ₀, v₀)`. With the asymmetric parameters `μ₀ = 1`, `v₀ = 3`, `v = 1`, this is the *forward*
direction; a `θ ∣ x` vs `x ∣ θ` reversal would instead land on the posterior kernel. This consumes
`condDistrib_snd_fst_gaussianNoisyLaw` — the load-bearing conditional-law content the rest of the
file (marginals, kernel application) does not touch. -/
theorem condDistrib_snd_fst_witness :
    condDistrib Prod.snd Prod.fst (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num))
      =ᵐ[gaussianReal 1 (gaussianVarianceNNReal 3 (by norm_num))]
        locationKernel 1 (by norm_num) :=
  condDistrib_snd_fst_gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)

/-- **Posterior conditional law `θ ∣ x` is the conjugate posterior kernel.** The conditional
distribution of the parameter given the signal is `x ↦ N(μ⋆(x), v⋆) = posteriorKernel`, a.e. under
the prior-predictive marginal `N(μ₀, v₀ + v) = N(1, 4)`. This is the *reverse* conditional, distinct
from the forward `locationKernel` above, so the pair pins the conditional direction. Consumes
`condDistrib_fst_snd_gaussianNoisyLaw`. -/
theorem condDistrib_fst_snd_witness :
    condDistrib Prod.fst Prod.snd (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num))
      =ᵐ[gaussianReal 1 (gaussianVarianceNNReal (3 + 1) (by norm_num))]
        posteriorKernel 1 3 1 (by norm_num) (by norm_num) :=
  condDistrib_fst_snd_gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)

/-- **Forward conditional mean `E[x ∣ θ] = θ`.** Given the parameter, the signal's conditional mean
is the parameter itself — a.e. under the parameter prior. Consumes the forward conditional-mean
lemma. -/
theorem condMean_snd_fst_witness :
    ∀ᵐ θ ∂(gaussianReal 1 (gaussianVarianceNNReal 3 (by norm_num))),
      ∫ y, y ∂(condDistrib Prod.snd Prod.fst (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)) θ)
        = θ :=
  gaussianNoisy_integral_id_condDistrib_snd_fst 1 3 1 (by norm_num) (by norm_num)

/-- **Posterior conditional mean `E[θ ∣ x] = μ⋆(x)`.** Given the signal, the parameter's conditional
mean is the conjugate posterior mean `(v·μ₀ + v₀·x)/(v₀+v)` — a.e. under the prior-predictive
marginal. Distinct from the forward `E[x ∣ θ] = θ` above, so the conditional-mean direction is
genuinely exercised. Consumes the posterior conditional-mean lemma. -/
theorem condMean_fst_snd_witness :
    ∀ᵐ x ∂(gaussianReal 1 (gaussianVarianceNNReal (3 + 1) (by norm_num))),
      ∫ y, y ∂(condDistrib Prod.fst Prod.snd (gaussianNoisyLaw 1 3 1 (by norm_num) (by norm_num)) x)
        = gaussianPosteriorMean 1 3 1 x :=
  gaussianNoisy_integral_id_condDistrib_fst_snd 1 3 1 (by norm_num) (by norm_num)

end conditionalLaws

end EconlibTest.Probability.Distributions.Conjugate

end
