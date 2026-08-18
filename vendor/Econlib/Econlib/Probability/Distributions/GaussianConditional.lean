/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.PiCompProd
public import Econlib.Probability.Distributions.GaussianConjugate
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.Posterior

/-!
# Conditional laws of the Gaussian noisy-signal joint

Mathlib has the normal-normal density factorization (`gaussianPDFReal_mul_factorization`) and the
bundled `ContDist` posterior, but no statement that the measure-theoretic **conditional
distribution** (`ProbabilityTheory.condDistrib`) of a bivariate Gaussian is Gaussian. This file
fills that gap for the noisy-signal model, an asymmetric correlated joint.

The model has a parameter `θ ~ N(μ₀, v₀)` and a signal `x ∣ θ ~ N(θ, v)`. The joint law on `ℝ × ℝ`
is the composition-product `gaussianReal μ₀ v₀ ⊗ₘ locationKernel v`, where the **location kernel**
`locationKernel v θ = N(θ, v)` is the likelihood. Its two coordinate conditional distributions are
the forward conditional `x ∣ θ`, equal to the location kernel `N(θ, v)`, and the **posterior**
`θ ∣ x`, equal to the conjugate Gaussian `N(μ⋆(x), v⋆)` with `μ⋆(x) = (v·μ₀ + v₀·x)/(v₀+v)`
(`gaussianPosteriorMean`) and `v⋆ = v₀·v/(v₀+v)` (`gaussianPosteriorVariance`).

## Main definitions

* `Econlib.Probability.locationKernel`: The Gaussian location likelihood kernel `θ ↦ N(θ, v)`.
* `Econlib.Probability.posteriorKernel`: The conjugate posterior kernel `x ↦ N(μ⋆(x), v⋆)`.
* `Econlib.Probability.gaussianNoisyLaw`: The noisy-signal joint law on `ℝ × ℝ`.
* `Econlib.Probability.gaussianNoisyLawVec`: The same joint in profile form on `Fin 2 → ℝ`, for
  two-player Bayesian games whose type profile is a function rather than a pair.

## Main statements

* `gaussianNoisyLaw_map_fst` / `gaussianNoisyLaw_map_snd`: The two marginals (`N(μ₀, v₀)` and the
  prior-predictive `N(μ₀, v₀+v)`).
* `gaussianNoisyLaw_map_swap`: The joint with coordinates swapped factorizes as
  `evidence ⊗ₘ posteriorKernel` (the conjugacy crux).
* `condDistrib_snd_fst_gaussianNoisyLaw` / `condDistrib_fst_snd_gaussianNoisyLaw`: The two
  coordinate conditionals equal the location / posterior kernels a.e.
* `gaussianNoisy_integral_id_condDistrib_snd_fst` /
  `gaussianNoisy_integral_id_condDistrib_fst_snd`: The conditional means `E[x ∣ θ] = θ` and
  `E[θ ∣ x] = μ⋆(x)`.
* `gaussianNoisyLawVec_map_eval_zero` / `_map_eval_one` and
  `condDistrib_eval_one_eval_zero_gaussianNoisyLawVec` /
  `condDistrib_eval_zero_eval_one_gaussianNoisyLawVec`: The coordinate marginals and conditional
  laws of the profile-form joint, read off the `ℝ × ℝ` results through
  `MeasurableEquiv.finTwoArrow`.

## Tags

gaussian, normal, conditional distribution, condDistrib, noisy signal, conjugate posterior,
disintegration
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.Probability

noncomputable section

/-! ### The location and posterior kernels -/

/-- The **Gaussian location likelihood kernel** `θ ↦ N(θ, v)`: The conditional law of a signal
given the parameter in the noisy-signal model. Built as the pushforward of `δ_θ ⊗ N(0, v)` under
addition, so that `locationKernel v hv θ = (N(0,v)).map (θ + ·) = N(θ, v)`. -/
def locationKernel (v : ℝ) (hv : 0 < v) : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 (gaussianVarianceNNReal v hv))).map
    (fun p : ℝ × ℝ => p.1 + p.2)

instance (v : ℝ) (hv : 0 < v) : IsMarkovKernel (locationKernel v hv) := by
  rw [locationKernel]
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The location kernel evaluates to the Gaussian `N(θ, v)`. -/
@[simp] lemma locationKernel_apply (v : ℝ) (hv : 0 < v) (θ : ℝ) :
    locationKernel v hv θ = gaussianReal θ (gaussianVarianceNNReal v hv) := by
  rw [locationKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  have : (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.mk θ = (θ + ·) := by
    funext b; simp
  rw [this, gaussianReal_map_const_add, zero_add]

/-- The conjugate posterior mean `μ⋆(x) = (v·μ₀ + v₀·x)/(v₀+v)` is measurable (indeed affine) in
the signal `x`. -/
lemma measurable_gaussianPosteriorMean (μ₀ v₀ v : ℝ) :
    Measurable (fun x : ℝ => gaussianPosteriorMean μ₀ v₀ v x) := by
  unfold gaussianPosteriorMean
  exact (measurable_const.add (measurable_const.mul measurable_id)).div_const _

/-- The **conjugate posterior kernel** `x ↦ N(μ⋆(x), v⋆)` of the normal-normal model, with
posterior mean `μ⋆(x) = (v·μ₀ + v₀·x)/(v₀+v)` and posterior variance `v⋆ = v₀·v/(v₀+v)`. Built as
the pushforward of `δ_{μ⋆(x)} ⊗ N(0, v⋆)` under addition. -/
def posteriorKernel (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) : Kernel ℝ ℝ :=
  (Kernel.deterministic (fun x : ℝ => gaussianPosteriorMean μ₀ v₀ v x)
        (measurable_gaussianPosteriorMean μ₀ v₀ v) ×ₖ
      Kernel.const ℝ (gaussianReal 0
        (gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
          (gaussianPosteriorVariance_pos hv₀ hv)))).map
    (fun p : ℝ × ℝ => p.1 + p.2)

instance (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    IsMarkovKernel (posteriorKernel μ₀ v₀ v hv₀ hv) := by
  rw [posteriorKernel]
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The posterior kernel evaluates to the conjugate Gaussian `N(μ⋆(x), v⋆)`. -/
@[simp] lemma posteriorKernel_apply (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) (x : ℝ) :
    posteriorKernel μ₀ v₀ v hv₀ hv x =
      gaussianReal (gaussianPosteriorMean μ₀ v₀ v x)
        (gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
          (gaussianPosteriorVariance_pos hv₀ hv)) := by
  rw [posteriorKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  have : (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.mk (gaussianPosteriorMean μ₀ v₀ v x)
      = (gaussianPosteriorMean μ₀ v₀ v x + ·) := by
    funext b; simp
  rw [this, gaussianReal_map_const_add, zero_add]

/-! ### The noisy-signal joint law -/

/-- The **noisy-signal joint law** on `ℝ × ℝ`: Parameter `θ ~ N(μ₀, v₀)` in the first coordinate,
signal `x ∣ θ ~ N(θ, v)` in the second. This is the composition-product of the Gaussian prior with
the location likelihood kernel. Correlated by construction: `Cov(θ, x) = v₀ > 0`. -/
def gaussianNoisyLaw (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) : Measure (ℝ × ℝ) :=
  gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) ⊗ₘ locationKernel v hv

instance (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    IsProbabilityMeasure (gaussianNoisyLaw μ₀ v₀ v hv₀ hv) := by
  rw [gaussianNoisyLaw]; infer_instance

/-- **First marginal** of the joint: The parameter prior `N(μ₀, v₀)`. -/
@[simp] lemma gaussianNoisyLaw_map_fst (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.fst
      = gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) := by
  rw [gaussianNoisyLaw, ← Measure.fst, Measure.fst_compProd]

/-- **Density representation of the joint.** The noisy-signal joint law is the volume-product
`withDensity` of the joint Gaussian density `N(θ; μ₀, v₀)·N(x; θ, v)` (parameter `θ` first, signal
`x` second). -/
lemma gaussianNoisyLaw_eq_withDensity (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    gaussianNoisyLaw μ₀ v₀ v hv₀ hv =
      (volume.prod volume).withDensity (fun p : ℝ × ℝ =>
        gaussianPDF μ₀ (gaussianVarianceNNReal v₀ hv₀) p.1 *
          gaussianPDF p.1 (gaussianVarianceNNReal v hv) p.2) := by
  set vdv := gaussianVarianceNNReal v hv with hvdv
  -- Joint measurability of the likelihood density `(θ, x) ↦ N(x; θ, v)`.
  have hg_meas : Measurable (Function.uncurry (fun θ x => gaussianPDF θ vdv x)) := by
    unfold Function.uncurry gaussianPDF gaussianPDFReal
    fun_prop
  -- Density representation of the likelihood kernel as a `withDensity` of the constant `volume`.
  have hker : locationKernel v hv
      = (Kernel.const ℝ (volume : Measure ℝ)).withDensity (fun θ x => gaussianPDF θ vdv x) := by
    ext θ s hs
    rw [Kernel.withDensity_apply _ hg_meas, Kernel.const_apply, locationKernel_apply,
      gaussianReal_of_var_ne_zero _ (gaussianVarianceNNReal_ne_zero v hv)]
  haveI : IsSFiniteKernel
      ((Kernel.const ℝ (volume : Measure ℝ)).withDensity (fun θ x => gaussianPDF θ vdv x)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => by simp [gaussianPDF])
  rw [gaussianNoisyLaw, hker, Measure.compProd_withDensity hg_meas, Measure.compProd_const,
    gaussianReal_of_var_ne_zero _ (gaussianVarianceNNReal_ne_zero v₀ hv₀),
    prod_withDensity_left (measurable_gaussianPDF _ _)]
  rw [← withDensity_mul (volume.prod volume)
    (f := fun z : ℝ × ℝ => gaussianPDF μ₀ (gaussianVarianceNNReal v₀ hv₀) z.1)
    (g := fun z : ℝ × ℝ => gaussianPDF z.1 vdv z.2)
    (by fun_prop) (hg_meas.comp (by fun_prop))]
  rfl

/-- **The conjugacy crux.** The joint law with coordinates swapped — i.e. the joint of
`(signal, parameter)` — factorizes as the prior-predictive (evidence) law of the signal composed
with the conjugate posterior kernel. Both sides are the `withDensity` of the same joint Gaussian
density read in `(x, θ)` order, with the equality of densities supplied by the normal-normal
factorization `gaussianPDFReal_mul_factorization`. -/
lemma gaussianNoisyLaw_map_swap (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.swap =
      gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) ⊗ₘ
        posteriorKernel μ₀ v₀ v hv₀ hv := by
  have hsum_pos : 0 < v₀ + v := by positivity
  set vd₀ := gaussianVarianceNNReal v₀ hv₀ with hvd₀
  set vdv := gaussianVarianceNNReal v hv with hvdv
  set vde := gaussianVarianceNNReal (v₀ + v) hsum_pos with hvde
  set vstar := gaussianVarianceNNReal (gaussianPosteriorVariance v₀ v)
    (gaussianPosteriorVariance_pos hv₀ hv) with hvstar
  -- The two joint densities, read in `(θ, x)` and `(x, θ)` order respectively.
  set D : ℝ × ℝ → ENNReal :=
    fun p => gaussianPDF μ₀ vd₀ p.1 * gaussianPDF p.1 vdv p.2 with hD
  set D' : ℝ × ℝ → ENNReal := fun q =>
    gaussianPDF μ₀ vde q.1 * gaussianPDF (gaussianPosteriorMean μ₀ v₀ v q.1) vstar q.2 with hD'
  have hD_meas : Measurable D := by
    rw [hD]; unfold gaussianPDF gaussianPDFReal; fun_prop
  -- Joint measurability of the posterior likelihood density `(x, θ) ↦ N(θ; μ⋆(x), v⋆)`.
  have hg'_meas : Measurable
      (Function.uncurry (fun x θ => gaussianPDF (gaussianPosteriorMean μ₀ v₀ v x) vstar θ)) := by
    have hμ : Measurable (fun a : ℝ × ℝ => gaussianPosteriorMean μ₀ v₀ v a.1) :=
      (measurable_gaussianPosteriorMean μ₀ v₀ v).comp measurable_fst
    unfold Function.uncurry gaussianPDF gaussianPDFReal
    fun_prop
  -- The swapped joint factorizes density-wise as the posterior decomposition `(x, θ)`.
  have hRHS : gaussianReal μ₀ vde ⊗ₘ posteriorKernel μ₀ v₀ v hv₀ hv
      = (volume.prod volume).withDensity D' := by
    have hker : posteriorKernel μ₀ v₀ v hv₀ hv
        = (Kernel.const ℝ (volume : Measure ℝ)).withDensity
            (fun x θ => gaussianPDF (gaussianPosteriorMean μ₀ v₀ v x) vstar θ) := by
      ext x s hs
      rw [Kernel.withDensity_apply _ hg'_meas, Kernel.const_apply, posteriorKernel_apply,
        gaussianReal_of_var_ne_zero _ (gaussianVarianceNNReal_ne_zero _ _)]
    haveI : IsSFiniteKernel ((Kernel.const ℝ (volume : Measure ℝ)).withDensity
        (fun x θ => gaussianPDF (gaussianPosteriorMean μ₀ v₀ v x) vstar θ)) :=
      Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => by simp [gaussianPDF])
    rw [hker, Measure.compProd_withDensity hg'_meas, Measure.compProd_const,
      gaussianReal_of_var_ne_zero _ (gaussianVarianceNNReal_ne_zero _ _),
      prod_withDensity_left (measurable_gaussianPDF _ _)]
    rw [← withDensity_mul (volume.prod volume)
      (f := fun q : ℝ × ℝ => gaussianPDF μ₀ vde q.1)
      (g := fun q : ℝ × ℝ => gaussianPDF (gaussianPosteriorMean μ₀ v₀ v q.1) vstar q.2)
      (by fun_prop) (hg'_meas.comp (by fun_prop))]
    rfl
  -- The pushforward of `withDensity D` by `swap` is `withDensity (D ∘ swap)` (volume is symmetric).
  have hswap : ((volume.prod volume).withDensity D).map Prod.swap
      = (volume.prod volume).withDensity (fun q => D q.swap) := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
      withDensity_apply _ hs]
    -- Change of variables along the swap-invariance of `volume.prod volume`.
    have hmp : (volume.prod volume).map Prod.swap = (volume.prod volume : Measure (ℝ × ℝ)) :=
      Measure.prod_swap
    calc ∫⁻ p in Prod.swap ⁻¹' s, D p ∂(volume.prod volume)
        = ∫⁻ p in Prod.swap ⁻¹' s, (fun q => D q.swap) (Prod.swap p) ∂(volume.prod volume) := by
          refine setLIntegral_congr_fun (measurable_swap hs) (fun p _ => ?_); simp
      _ = ∫⁻ q in s, (fun q => D q.swap) q ∂((volume.prod volume).map Prod.swap) :=
          (setLIntegral_map hs (hD_meas.comp measurable_swap) measurable_swap).symm
      _ = ∫⁻ q in s, D q.swap ∂(volume.prod volume) := by rw [hmp]
  -- Density equality `D (x.swap) = D' x` is the normal-normal factorization.
  have hDeq : (fun q : ℝ × ℝ => D q.swap) = D' := by
    funext q
    obtain ⟨x, θ⟩ := q
    simp only [hD, hD', Prod.swap_prod_mk]
    rw [hvd₀, hvdv, hvde, hvstar, gaussianPDF, gaussianPDF, gaussianPDF, gaussianPDF,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
      gaussianPDFReal_mul_factorization μ₀ x hv₀ hv θ]
  rw [gaussianNoisyLaw_eq_withDensity, hRHS, hswap, hDeq]

/-- **Second marginal** of the joint: The prior-predictive (evidence) law `N(μ₀, v₀+v)`. This is
the marginal law of the signal, obtained by integrating the parameter out of the joint Gaussian
density. -/
@[simp] lemma gaussianNoisyLaw_map_snd (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.snd =
      gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) := by
  -- The second marginal is the first marginal of the swapped joint, which factorizes as
  -- `evidence ⊗ₘ posteriorKernel` by `gaussianNoisyLaw_map_swap`.
  have hsnd : (Prod.snd : ℝ × ℝ → ℝ) = Prod.fst ∘ Prod.swap := rfl
  rw [hsnd, ← Measure.map_map measurable_fst measurable_swap, gaussianNoisyLaw_map_swap,
    ← Measure.fst, Measure.fst_compProd]

/-! ### The coordinate conditionals -/

/-- **Forward conditional.** The conditional law of the signal given the parameter is the location
kernel `N(θ, v)` — definitional from the `compProd` structure of the joint. -/
lemma condDistrib_snd_fst_gaussianNoisyLaw (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib Prod.snd Prod.fst (gaussianNoisyLaw μ₀ v₀ v hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀)] locationKernel v hv := by
  have hmap : (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.fst
      = gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) := gaussianNoisyLaw_map_fst _ _ _ _ _
  rw [← hmap]
  refine condDistrib_ae_eq_of_measure_eq_compProd Prod.fst measurable_snd.aemeasurable ?_
  -- The pair map `(fst, snd)` is the identity, and the joint is the defining `compProd`.
  rw [show (fun p : ℝ × ℝ => (Prod.fst p, Prod.snd p)) = id from rfl, Measure.map_id, hmap,
    gaussianNoisyLaw]

/-- **Posterior conditional.** The conditional law of the parameter given the signal is the
conjugate posterior kernel `N(μ⋆(x), v⋆)`, via the conjugacy crux `gaussianNoisyLaw_map_swap` and
the a.e. uniqueness of `condDistrib`. -/
lemma condDistrib_fst_snd_gaussianNoisyLaw (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib Prod.fst Prod.snd (gaussianNoisyLaw μ₀ v₀ v hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity))]
        posteriorKernel μ₀ v₀ v hv₀ hv := by
  have hmap : (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.snd
      = gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) :=
    gaussianNoisyLaw_map_snd _ _ _ _ _
  rw [← hmap]
  refine condDistrib_ae_eq_of_measure_eq_compProd Prod.snd measurable_fst.aemeasurable ?_
  -- The pair map `(snd, fst)` is `Prod.swap`; the swapped joint is `evidence ⊗ₘ posteriorKernel`.
  rw [show (fun p : ℝ × ℝ => (Prod.snd p, Prod.fst p)) = Prod.swap from rfl,
    gaussianNoisyLaw_map_swap, hmap]

/-! ### The conditional means -/

/-- **Forward conditional mean** `E[x ∣ θ] = θ`: The signal's conditional mean given the parameter
is the parameter itself. -/
lemma gaussianNoisy_integral_id_condDistrib_snd_fst (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ θ ∂(gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀)),
      ∫ y, y ∂(condDistrib Prod.snd Prod.fst (gaussianNoisyLaw μ₀ v₀ v hv₀ hv) θ) = θ := by
  filter_upwards [condDistrib_snd_fst_gaussianNoisyLaw μ₀ v₀ v hv₀ hv] with θ hθ
  rw [hθ, locationKernel_apply, integral_id_gaussianReal]

/-- **Posterior conditional mean** `E[θ ∣ x] = μ⋆(x)`: The parameter's conditional mean given the
signal is the conjugate posterior mean `(v·μ₀ + v₀·x)/(v₀+v)`. -/
lemma gaussianNoisy_integral_id_condDistrib_fst_snd (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    ∀ᵐ x ∂(gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity))),
      ∫ y, y ∂(condDistrib Prod.fst Prod.snd (gaussianNoisyLaw μ₀ v₀ v hv₀ hv) x) =
        gaussianPosteriorMean μ₀ v₀ v x := by
  filter_upwards [condDistrib_fst_snd_gaussianNoisyLaw μ₀ v₀ v hv₀ hv] with x hx
  rw [hx, posteriorKernel_apply, integral_id_gaussianReal]

/-! ### Profile form on `Fin 2 → ℝ`

A two-player measure-theoretic Bayesian game carries the type profile as a function
`Fin 2 → ℝ`, not a pair `ℝ × ℝ`. We transport the noisy-signal joint to that representation along
the measurable equivalence `MeasurableEquiv.finTwoArrow` and re-export the coordinate marginals and
conditional laws there, so such a game reads its conditional beliefs off directly instead of
re-proving the `Measure.map_map` transport at the use site. -/

/-- The measurable equivalence `(Fin 2 → ℝ) ≃ᵐ ℝ × ℝ`, `θ ↦ (θ 0, θ 1)`. -/
abbrev finTwoArrowEquiv : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow (α := ℝ)

/-- The noisy-signal joint law in profile form on `Fin 2 → ℝ`: The `ℝ × ℝ` joint `gaussianNoisyLaw`
transported along `θ ↦ (θ 0, θ 1)`. Coordinate `0` is the parameter `θ₀ ~ N(μ₀, v₀)`, coordinate
`1` the noisy signal `θ₁ ∣ θ₀ ~ N(θ₀, v)`. -/
def gaussianNoisyLawVec (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) : Measure (Fin 2 → ℝ) :=
  (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map finTwoArrowEquiv.symm

instance (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    IsProbabilityMeasure (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv) := by
  rw [gaussianNoisyLawVec]
  exact Measure.isProbabilityMeasure_map finTwoArrowEquiv.symm.measurable.aemeasurable

/-- Coordinate `0` marginal of the profile joint: The parameter prior `N(μ₀, v₀)`. -/
lemma gaussianNoisyLawVec_map_eval_zero (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv).map (fun θ : Fin 2 → ℝ => θ 0)
      = gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀) := by
  rw [gaussianNoisyLawVec,
    Measure.map_map (measurable_pi_apply 0) finTwoArrowEquiv.symm.measurable]
  have hcomp : (fun θ : Fin 2 → ℝ => θ 0) ∘ finTwoArrowEquiv.symm = Prod.fst := by funext p; rfl
  rw [hcomp, gaussianNoisyLaw_map_fst]

/-- Coordinate `1` marginal of the profile joint: The prior-predictive `N(μ₀, v₀+v)`. -/
lemma gaussianNoisyLawVec_map_eval_one (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv).map (fun θ : Fin 2 → ℝ => θ 1)
      = gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity)) := by
  rw [gaussianNoisyLawVec,
    Measure.map_map (measurable_pi_apply 1) finTwoArrowEquiv.symm.measurable]
  have hcomp : (fun θ : Fin 2 → ℝ => θ 1) ∘ finTwoArrowEquiv.symm = Prod.snd := by funext p; rfl
  rw [hcomp, gaussianNoisyLaw_map_snd]

/-- The `(θ 0, θ 1)` pushforward of the profile joint recovers the `ℝ × ℝ` noisy-signal joint. -/
lemma gaussianNoisyLawVec_map_pair01 (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv).map (fun θ : Fin 2 → ℝ => (θ 0, θ 1))
      = gaussianNoisyLaw μ₀ v₀ v hv₀ hv := by
  have hpair : Measurable (fun θ : Fin 2 → ℝ => (θ 0, θ 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  rw [gaussianNoisyLawVec, Measure.map_map hpair finTwoArrowEquiv.symm.measurable]
  have hcomp : (fun θ : Fin 2 → ℝ => (θ 0, θ 1)) ∘ finTwoArrowEquiv.symm = id := by funext p; rfl
  rw [hcomp, Measure.map_id]

/-- The `(θ 1, θ 0)` pushforward of the profile joint is the swapped `ℝ × ℝ` noisy-signal joint. -/
lemma gaussianNoisyLawVec_map_pair10 (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv).map (fun θ : Fin 2 → ℝ => (θ 1, θ 0))
      = (gaussianNoisyLaw μ₀ v₀ v hv₀ hv).map Prod.swap := by
  have hpair : Measurable (fun θ : Fin 2 → ℝ => (θ 1, θ 0)) :=
    (measurable_pi_apply 1).prodMk (measurable_pi_apply 0)
  rw [gaussianNoisyLawVec, Measure.map_map hpair finTwoArrowEquiv.symm.measurable]
  have hcomp : (fun θ : Fin 2 → ℝ => (θ 1, θ 0)) ∘ finTwoArrowEquiv.symm = Prod.swap := by
    funext p; rfl
  rw [hcomp]

/-- Forward conditional in profile form: The law of coordinate `1` given coordinate `0` is the
location kernel `N(θ₀, v)`, a.e. with respect to the coordinate-`0` marginal `N(μ₀, v₀)`. -/
lemma condDistrib_eval_one_eval_zero_gaussianNoisyLawVec (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib (fun θ : Fin 2 → ℝ => θ 1) (fun θ => θ 0) (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal v₀ hv₀)] locationKernel v hv := by
  have hkey := condDistrib_ae_eq_of_measure_eq_compProd
    (μ := gaussianNoisyLawVec μ₀ v₀ v hv₀ hv) (Y := fun θ : Fin 2 → ℝ => θ 1)
    (fun θ : Fin 2 → ℝ => θ 0) (measurable_pi_apply 1).aemeasurable
    (κ := locationKernel v hv) ?_
  · rwa [gaussianNoisyLawVec_map_eval_zero] at hkey
  · rw [gaussianNoisyLawVec_map_pair01, gaussianNoisyLawVec_map_eval_zero, ← gaussianNoisyLaw]

/-- Posterior conditional in profile form: The law of coordinate `0` given coordinate `1` is the
conjugate posterior kernel `N(μ⋆(θ₁), v⋆)`, a.e. with respect to the coordinate-`1` marginal
`N(μ₀, v₀+v)`. -/
lemma condDistrib_eval_zero_eval_one_gaussianNoisyLawVec (μ₀ v₀ v : ℝ) (hv₀ : 0 < v₀) (hv : 0 < v) :
    condDistrib (fun θ : Fin 2 → ℝ => θ 0) (fun θ => θ 1) (gaussianNoisyLawVec μ₀ v₀ v hv₀ hv)
      =ᵐ[gaussianReal μ₀ (gaussianVarianceNNReal (v₀ + v) (by positivity))]
        posteriorKernel μ₀ v₀ v hv₀ hv := by
  have hkey := condDistrib_ae_eq_of_measure_eq_compProd
    (μ := gaussianNoisyLawVec μ₀ v₀ v hv₀ hv) (Y := fun θ : Fin 2 → ℝ => θ 0)
    (fun θ : Fin 2 → ℝ => θ 1) (measurable_pi_apply 0).aemeasurable
    (κ := posteriorKernel μ₀ v₀ v hv₀ hv) ?_
  · rwa [gaussianNoisyLawVec_map_eval_one] at hkey
  · rw [gaussianNoisyLawVec_map_pair10, gaussianNoisyLawVec_map_eval_one,
      ← gaussianNoisyLaw_map_swap]

end

end Econlib.Probability
