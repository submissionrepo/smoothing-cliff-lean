/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.CauchySchwarz
public import Econlib.Math.MeasureTheory.IntegralReal
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# `ContDist` — continuous probability distribution on `ℝ` via a density

A `ContDist` is a continuous probability distribution over `ℝ` carried by a nonnegative Lebesgue
density integrating to one. This file collects the core API: The structure itself, the
density-builder `ofPDFReal`, the support and elementary density-integral lemmas, the measure bridge
`toMeasure` into Mathlib's measure API, and the expectation/variance operators.

## Main definitions

* `ContDist` — a density `ℝ → ℝ` that is nonnegative, integrable, and integrates to one.
* `ContDist.ofPDFReal` — build a `ContDist` from a nonnegative density with unit `lintegral`.
* `ContDist.support` — the set where the density is strictly positive.
* `ContDist.IsMode` — the density is maximized at a point.
* `ContDist.toMeasure` — the associated probability measure `volume.withDensity (ofReal ∘ density)`.
* `ContDist.expect`, `ContDist.variance` — expectation and variance of a function under the density.

## Main statements

* `ContDist.integral_toMeasure_eq` — the measure bridge `∫ f ∂d.toMeasure = ∫ density · f`.
* `ContDist.variance_nonneg` — variance is nonnegative (Cauchy–Schwarz).

## Tags

continuous distribution, density, expectation, variance
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

/-- A continuous probability distribution over `ℝ` via a density function. -/
structure ContDist where
  /-- Density with respect to Lebesgue measure. -/
  density : ℝ → ℝ
  /-- The density is nonnegative everywhere. -/
  nonneg : ∀ x, 0 ≤ density x
  /-- The density is Bochner integrable. -/
  integrable : Integrable density
  /-- The density integrates to one. -/
  integral_one : ∫ x, density x = 1

namespace ContDist

/-- Two continuous distributions with the same density are equal: All remaining fields are
propositional. -/
@[ext] lemma ext {d₁ d₂ : ContDist} (h : ∀ x, d₁.density x = d₂.density x) : d₁ = d₂ := by
  cases d₁; cases d₂
  simp only [ContDist.mk.injEq]
  exact funext h

/-- Build a `ContDist` from a nonnegative density whose `lintegral` is `1`. -/
noncomputable def ofPDFReal (density : ℝ → ℝ)
    (nonneg : ∀ x, 0 ≤ density x) (h_meas : StronglyMeasurable density)
    (h_lintegral : ∫⁻ x, ENNReal.ofReal (density x) = 1) : ContDist where
  density := density
  nonneg := nonneg
  integrable := integrable_of_lintegral_ofReal_eq_one nonneg h_meas h_lintegral
  integral_one := integral_eq_one_of_lintegral_ofReal_eq_one nonneg h_meas h_lintegral

/-- The reflection of the distribution across the origin, with density `x ↦ d.density (-x)`. -/
noncomputable def reflect (d : ContDist) : ContDist where
  density := fun x => d.density (-x)
  nonneg := fun x => d.nonneg (-x)
  integrable := d.integrable.comp_neg
  integral_one := by
    have h := MeasureTheory.Measure.integral_comp_mul_left d.density (-1)
    simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
    rw [h, d.integral_one]

/-! ### Support and elementary density-integral lemmas -/

/-- The support of a continuous distribution. -/
def support (d : ContDist) : Set ℝ :=
  {x : ℝ | 0 < d.density x}

/-- `c` is a mode of `d`: The density is maximized at `c`. A mode need not be unique — e.g. every
point of `[a, b]` is a mode of the uniform distribution on `[a, b]`. -/
def IsMode (d : ContDist) (c : ℝ) : Prop :=
  ∀ x, d.density x ≤ d.density c

/-- Density integral is strictly positive on a non-degenerate sub-interval where the density is
everywhere positive. -/
lemma density_integral_pos (d : ContDist) {a b : ℝ}
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    {p q : ℝ} (hpq : p < q) (hsub : Icc p q ⊆ Icc a b) :
    0 < ∫ x in Icc p q, d.density x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => d.nonneg x)) d.integrable.integrableOn]
  exact lt_of_lt_of_le (by simp [hpq]) (measure_mono
    (fun x hx => ⟨Function.mem_support.mpr
      (ne_of_gt (hd_pos x (hsub (Ioo_subset_Icc_self hx)))),
      Ioo_subset_Icc_self hx⟩))

/-- `density * g` is integrable on any compact sub-interval where both are continuous. -/
lemma density_mul_integrableOn (d : ContDist) {g : ℝ → ℝ} {a b : ℝ}
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hg_cont : ContinuousOn g (Icc a b))
    {p q : ℝ} (hsub : Icc p q ⊆ Icc a b) :
    IntegrableOn (fun x => d.density x * g x) (Icc p q) :=
  ((hd_cont.mono hsub).mul (hg_cont.mono hsub)).integrableOn_compact isCompact_Icc

/-- For a **compactly supported** density (vanishing off `[a, b]`), `density * g` is globally
integrable on `ℝ` whenever both factors are continuous on `[a, b]`. -/
lemma density_mul_integrable_of_supportsOn_Icc (d : ContDist) {g : ℝ → ℝ} {a b : ℝ}
    (h_supp : ∀ x, x ∉ Icc a b → d.density x = 0)
    (hd_cont : ContinuousOn d.density (Icc a b)) (hg_cont : ContinuousOn g (Icc a b)) :
    Integrable (fun x => d.density x * g x) := by
  -- off `[a, b]` the density vanishes, so the product is the indicator of its compact restriction
  have h_eq : (fun x => d.density x * g x)
      = (Icc a b).indicator (fun x => d.density x * g x) := by
    funext x
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h_supp x hx, zero_mul]
  rw [h_eq]
  exact ((hd_cont.mul hg_cont).integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_Icc

/-! ### Measure bridge -/

/-- Bridge to Mathlib measure (internal, not public API). -/
noncomputable def toMeasure (d : ContDist) : Measure ℝ :=
  Measure.withDensity volume (fun x => ENNReal.ofReal (d.density x))

/-- The density measure is a probability measure. -/
lemma toMeasure_isProbability (d : ContDist) : IsProbabilityMeasure d.toMeasure := by
  constructor
  change volume.withDensity (fun x => ENNReal.ofReal (d.density x)) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal d.integrable (ae_of_all _ d.nonneg)]
  rw [d.integral_one, ENNReal.ofReal_one]

/-- The density measure equals `volume.withDensity (ofReal ∘ density)`. Definitional. -/
@[simp] lemma toMeasure_eq (d : ContDist) :
    d.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (d.density x)) := rfl

/-- A `ContDist` is **atomless**: Every singleton has measure zero, inherited from Lebesgue measure
through `withDensity`. -/
instance instNoAtoms (d : ContDist) : NoAtoms d.toMeasure := by
  rw [toMeasure_eq]; exact noAtoms_withDensity _

/-- Integrating `f` against the density measure equals integrating `density * f` against Lebesgue
measure. This is the core bridge: `∫ f ∂d.toMeasure = ∫ density * f`. -/
lemma integral_toMeasure_eq (d : ContDist) (f : ℝ → ℝ) :
    ∫ x, f x ∂d.toMeasure = ∫ x, d.density x * f x := by
  rw [toMeasure_eq,
      integral_withDensity_eq_integral_toReal_smul₀
        d.integrable.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; ext x; simp [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x)]

/-- Set integral version of the measure bridge. -/
lemma setIntegral_toMeasure_eq (d : ContDist) (f : ℝ → ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    ∫ x in S, f x ∂d.toMeasure = ∫ x in S, d.density x * f x := by
  rw [toMeasure_eq,
      setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        d.integrable.aemeasurable.ennreal_ofReal.restrict
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ hS]
  congr 1; ext x; simp [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x)]

/-- Integrability against the density measure ↔ integrability of `density * f` against Lebesgue
measure. Wraps `withDensity` integrability machinery. -/
lemma integrable_toMeasure_iff (d : ContDist) {f : ℝ → ℝ} :
    Integrable f d.toMeasure ↔ Integrable (fun x => d.density x * f x) := by
  rw [toMeasure_eq,
      integrable_withDensity_iff_integrable_smul₀'
        d.integrable.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  -- the `toReal • f` integrand is pointwise the `density * f` integrand
  have h_integrand : (fun x => (ENNReal.ofReal (d.density x)).toReal • f x)
      = fun x => d.density x * f x :=
    funext fun x => by simp [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x)]
  rw [h_integrand]

/-! ### Expectation and variance -/

/-- Expected value for continuous distribution.

This is Mathlib's (Bochner) integral `∫ x, d.density x * f x`, hence **totalized**: It equals the
mathematical expectation `E_d[f]` exactly when `fun x => d.density x * f x` is `Integrable`, and
silently returns `0` when it is not (the convention of `MeasureTheory.integral`). The algebraic and
order laws that fail without integrability — `expect_add`, `expect_mono`, `variance_nonneg` — carry
the corresponding `Integrable` hypotheses, which is where the contract is discharged. -/
noncomputable def expect (d : ContDist) (f : ℝ → ℝ) : ℝ :=
  ∫ x, d.density x * f x

/-- Variance for continuous distribution. Inherits the totalization convention of `expect`: It is
the variance only when the relevant first and second moments are integrable (see
`variance_nonneg`). -/
noncomputable def variance (d : ContDist) (f : ℝ → ℝ) : ℝ :=
  d.expect (fun x => (f x)^2) - (d.expect f)^2

/-- `expect` unfolds to the density-weighted integral `∫ density · f`. -/
lemma expect_eq_integral (d : ContDist) (f : ℝ → ℝ) :
    d.expect f = ∫ x, d.density x * f x := rfl

/-- **Measure bridge for expectation**: `E_d[f] = ∫ f ∂d.toMeasure`. Rewrite with this to access
Mathlib's full integral API. -/
lemma expect_eq_measure_integral (d : ContDist) (f : ℝ → ℝ) :
    d.expect f = ∫ x, f x ∂d.toMeasure :=
  (d.integral_toMeasure_eq f).symm

/-- The expectation of a constant is that constant. -/
lemma expect_const (d : ContDist) (c : ℝ) :
    d.expect (fun _ => c) = c := by
  unfold expect
  simp only [mul_comm _ c]
  rw [integral_const_mul, d.integral_one, mul_one]

/-- Expectation is additive when both summands are integrable against the density. -/
lemma expect_add (d : ContDist) (f g : ℝ → ℝ)
    (hf : Integrable (fun x => d.density x * f x)) (hg : Integrable (fun x => d.density x * g x)) :
    d.expect (f + g) = d.expect f + d.expect g := by
  simp only [expect, Pi.add_apply, mul_add]
  exact integral_add hf hg

/-- Expectation commutes with scalar multiplication. -/
lemma expect_smul (d : ContDist) (c : ℝ) (f : ℝ → ℝ) :
    d.expect (c • f) = c * d.expect f := by
  unfold expect
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (d.density _) c]
  rw [integral_const_mul]

/-- The expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg (d : ContDist) (f : ℝ → ℝ) (h : ∀ x, 0 ≤ f x) :
    0 ≤ d.expect f :=
  integral_nonneg (fun x => mul_nonneg (d.nonneg x) (h x))

/-- Expectation is monotone in the integrand, given integrability of both sides. -/
lemma expect_mono (d : ContDist) (f g : ℝ → ℝ) (h : ∀ x, f x ≤ g x)
    (hf : Integrable (fun x => d.density x * f x)) (hg : Integrable (fun x => d.density x * g x)) :
    d.expect f ≤ d.expect g :=
  integral_mono hf hg (fun x => mul_le_mul_of_nonneg_left (h x) (d.nonneg x))

/-- Variance is nonnegative when the first and second moments are integrable (Cauchy–Schwarz). -/
lemma variance_nonneg (d : ContDist) (f : ℝ → ℝ)
    (hf : Integrable (fun x => d.density x * f x))
    (hf2 : Integrable (fun x => d.density x * (f x) ^ 2)) :
    0 ≤ d.variance f := by
  unfold ContDist.variance ContDist.expect
  set g := fun x => Real.sqrt (d.density x)
  set h := fun x => Real.sqrt (d.density x) * f x
  have g_sq : (fun x => g x ^ 2) = d.density := by
    ext x; simp [g, sq, Real.mul_self_sqrt (d.nonneg x)]
  have h_sq : ∀ x, h x ^ 2 = d.density x * (f x) ^ 2 := by
    intro x
    simp only [h, mul_pow]
    rw [sq (Real.sqrt _), Real.mul_self_sqrt (d.nonneg x)]
  have gh : ∀ x, g x * h x = d.density x * f x := by
    intro x; simp [g, h, ← mul_assoc, Real.mul_self_sqrt (d.nonneg x)]
  have hg2 : Integrable (fun x => g x ^ 2) := by rw [g_sq]; exact d.integrable
  have hh2 : Integrable (fun x => h x ^ 2) :=
    hf2.congr (Filter.Eventually.of_forall (fun x => (h_sq x).symm))
  have hgh : Integrable (fun x => g x * h x) :=
    hf.congr (Filter.Eventually.of_forall (fun x => (gh x).symm))
  have csz := integral_inner_mul_le_norm_sq_mul_norm_sq g h hg2 hh2 hgh
  have rw_g2 : ∫ x, g x ^ 2 = ∫ x, d.density x := by rw [g_sq]
  have rw_gh : ∫ x, g x * h x = ∫ x, d.density x * f x := by
    congr 1; ext x; exact gh x
  have rw_h2 : ∫ x, h x ^ 2 = ∫ x, d.density x * (f x) ^ 2 := by
    congr 1; ext x; exact h_sq x
  rw [rw_g2, rw_gh, rw_h2, d.integral_one] at csz
  linarith

end ContDist

end Econlib.Probability
