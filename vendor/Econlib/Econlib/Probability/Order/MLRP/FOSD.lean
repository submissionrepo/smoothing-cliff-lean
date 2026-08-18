/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.ProbDist
public import Econlib.Probability.Order.FOSD.Basic
public import Econlib.Probability.Order.FOSD.ExpectMono
public import Econlib.Probability.Order.MLRP.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# MLRP ⇒ FOSD and expectation orderings

The monotone likelihood ratio property is recast here as a pairwise relation on `ContDist`:
`d₁.MLRPLe d₂` says `d₂` is MLR-dominant over `d₁`. A parameterized family `d : ℝ → ContDist` has
MLRP (`HasMLRP d`) when its densities satisfy the cross inequality, equivalently
`∀ θ₁ < θ₂, (d θ₁).MLRPLe (d θ₂)`. MLR dominance implies first-order stochastic dominance, hence
the ordering of monotone expectations; strict MLRP implies the strict ordering (Milgrom 1981).

## Main definitions

* `ContDist.MLRPLe` — the pairwise MLR-dominance relation on `ContDist`.
* `HasMLRP`, `HasStrictMLRP` — the (strict) MLRP predicate for a parameterized family.

## Main statements

* `ContDist.MLRPLe.fosd` — MLR dominance implies first-order stochastic dominance.
* `ContDist.MLRPLe.expect_mono` — MLR dominance orders monotone expectations.
* `HasMLRP.fosd`, `HasMLRP.expectMonotone` — the family-level forms.
* `HasStrictMLRP.expectStrictMono` — strict MLRP strictly orders expectations of strictly monotone
  functions, with the full-support form `HasStrictMLRP.expectStrictMono_of_pos`.

## Notes

`HasMLRP` is definitionally the raw cross inequality on the family's densities; `HasMLRP.mlrpLe`
extracts the pairwise relation between any two ordered members.

## References

* Milgrom, Paul R. 1981. “Good News and Bad News: Representation Theorems and Applications.” *The
  Bell Journal of Economics* 12 (2): 380. [https://doi.org/10.2307/3003562](https://doi.org/10.2307/3003562).

## Tags

monotone likelihood ratio, mlrp, first-order stochastic dominance, fosd
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- `d₁.MLRPLe d₂`: `d₂` is MLR-dominant over `d₁` — the likelihood-ratio cross inequality. For
`x₁ ≤ x₂`, the "off-diagonal" product is dominated by the "diagonal" one. -/
def ContDist.MLRPLe (d₁ d₂ : ContDist) : Prop :=
  ∀ x₁ x₂, x₁ ≤ x₂ → d₂.density x₁ * d₁.density x₂ ≤ d₂.density x₂ * d₁.density x₁

/-- A parameterized family `d : ℝ → ContDist` has the **monotone likelihood ratio property**:
Definitionally the cross inequality on its densities, equivalently
`∀ θ₁ < θ₂, (d θ₁).MLRPLe (d θ₂)` (see `HasMLRP.mlrpLe`). -/
def HasMLRP (d : ℝ → ContDist) : Prop :=
  HasMonotoneLikelihoodRatio (fun x θ => (d θ).density x)

/-- Strict version of `HasMLRP`. -/
def HasStrictMLRP (d : ℝ → ContDist) : Prop :=
  HasStrictMonotoneLikelihoodRatio (fun x θ => (d θ).density x)

/-- A family with MLRP yields the pairwise relation between any two ordered members. -/
lemma HasMLRP.mlrpLe {d : ℝ → ContDist} (h : HasMLRP d) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    (d θ₁).MLRPLe (d θ₂) :=
  fun x₁ x₂ hx => h θ₁ θ₂ x₁ x₂ hθ hx

/-- Strict MLRP implies (weak) MLRP for a family. -/
lemma HasStrictMLRP.hasMLRP {d : ℝ → ContDist} (h : HasStrictMLRP d) : HasMLRP d :=
  HasStrictMonotoneLikelihoodRatio.hasMonotoneLikelihoodRatio h

/-- **CDF bridge.** The integral-defined CDF of a `ContDist` agrees with the canonical CDF of its
embedded probability law; both evaluate at `x` to the lower-tail integral
`∫ t in Iic x, density t`. -/
lemma ContDist.cdf_eq_ofProbDist (d : ContDist) : d.cdf = CDF.ofProbDist d.toProbDist := by
  haveI := d.toMeasure_isProbability
  apply CDF.ext
  intro x
  rw [CDF.ofProbDist_apply, ContDist.toProbDist_toMeasure,
    ProbabilityTheory.cdf_eq_real,
    ← MeasureTheory.setIntegral_one_eq_measureReal,
    d.setIntegral_toMeasure_eq (fun _ => (1 : ℝ)) measurableSet_Iic, cdf_eq_integral]
  simp

namespace ContDist.MLRPLe

/-- **MLR dominance ⇒ stochastic dominance (CDF form).** If `d₂` is MLR-dominant over `d₁` then its
CDF lies weakly below `d₁`'s, i.e. `IntegratedCDFTower 1 d₂.cdf d₁.cdf`. -/
lemma integratedCDFTower_one {d₁ d₂ : ContDist} (h : d₁.MLRPLe d₂) :
    IntegratedCDFTower 1 d₂.cdf d₁.cdf := by
  rw [IntegratedCDFTower.one_iff]
  intro x
  -- Upper-tail mass is `1 -` lower-tail mass, since the density integrates to one.
  have hCompl : ∀ d : ContDist, ∫ t in Ioi x, d.density t = 1 - ∫ t in Iic x, d.density t := by
    intro d
    have h := integral_add_compl (s := Iic x) measurableSet_Iic d.integrable
    rw [compl_Iic] at h
    linarith [d.integral_one]
  have hCompl₁ := hCompl d₁
  have hCompl₂ := hCompl d₂
  have hIneq := mlrp_integrated_cross (g₁ := d₁.density) (g₂ := d₂.density)
    (fun x₁ x₂ hx => h x₁ x₂ hx) d₁.integrable d₂.integrable
    (Iic x) (Ioi x) measurableSet_Iic measurableSet_Ioi
    (fun a ha b hb => le_trans ha (le_of_lt hb))
  rw [hCompl₁, hCompl₂] at hIneq
  have h_integral : ∫ t in Iic x, d₂.density t ≤ ∫ t in Iic x, d₁.density t := by
    nlinarith
  simpa [ContDist.cdf_eq_integral] using h_integral

/-- **MLR dominance ⇒ first-order stochastic dominance.** If `d₂` is MLR-dominant over `d₁`, then
`d₂.toProbDist` first-order stochastically dominates `d₁.toProbDist`, stated with the canonical
`FOSD` relation on `ProbDist`. -/
lemma fosd {d₁ d₂ : ContDist} (h : d₁.MLRPLe d₂) : FOSD d₂.toProbDist d₁.toProbDist := by
  rw [fosd_iff_integratedCDFTower_one, ← d₂.cdf_eq_ofProbDist, ← d₁.cdf_eq_ofProbDist]
  exact h.integratedCDFTower_one

/-- **MLR dominance orders monotone expectations.** If `d₂` is MLR-dominant over `d₁` and `g` is
monotone with integrable `density · g` against both, then `E_{d₁}[g] ≤ E_{d₂}[g]`. -/
lemma expect_mono {d₁ d₂ : ContDist} (h : d₁.MLRPLe d₂) (g : ℝ → ℝ) (hg : Monotone g)
    (hInt₁ : Integrable (fun x => d₁.density x * g x))
    (hInt₂ : Integrable (fun x => d₂.density x * g x)) :
    d₁.expect g ≤ d₂.expect g :=
  FOSD.expect_mono d₂ d₁ g hg h.integratedCDFTower_one hInt₂ hInt₁

end ContDist.MLRPLe

namespace HasMLRP

/-- **MLRP ⇒ FOSD (family form).** For `θ₁ ≤ θ₂`, the distribution at the higher parameter `θ₂`
first-order stochastically dominates the one at `θ₁`. -/
lemma fosd {d : ℝ → ContDist} (h : HasMLRP d) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂) :
    FOSD (d θ₂).toProbDist (d θ₁).toProbDist := by
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact FOSD.refl _
  · exact (h.mlrpLe hθ_lt).fosd

/-- **MLRP orders expectations of monotone functions (family form).** -/
lemma expectMonotone {d : ℝ → ContDist} (h : HasMLRP d) (g : ℝ → ℝ) (hg : Monotone g)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (hInt₁ : Integrable (fun x => (d θ₁).density x * g x))
    (hInt₂ : Integrable (fun x => (d θ₂).density x * g x)) :
    (d θ₁).expect g ≤ (d θ₂).expect g := by
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_rfl
  · exact (h.mlrpLe hθ_lt).expect_mono g hg hInt₁ hInt₂

end HasMLRP

namespace HasStrictMLRP

/-- **Strict MLRP implies strict monotonicity of expectations (family form).** For a strictly
monotone `g`, `θ₁ < θ₂`, integrable `density · g` against both members, and a positivity witness
for the lower density on some open interval, the expected value strictly increases. The positivity
witness rules out the degenerate case of a.e.-equal densities, which would make the strict cross
inequality collapse. -/
lemma expectStrictMono {d : ℝ → ContDist} (h : HasStrictMLRP d) (g : ℝ → ℝ) (hg : StrictMono g)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hInt₁ : Integrable (fun x => (d θ₁).density x * g x))
    (hInt₂ : Integrable (fun x => (d θ₂).density x * g x))
    (hPos : ∃ a b, a < b ∧ ∀ t ∈ Set.Ioo a b, 0 < (d θ₁).density t) :
    (d θ₁).expect g < (d θ₂).expect g := by
  obtain ⟨a, b, hab, hfPos⟩ := hPos
  have hFosd : IntegratedCDFTower 1 (d θ₂).cdf (d θ₁).cdf :=
    (h.hasMLRP.mlrpLe hθ).integratedCDFTower_one
  have hStrictCdf : ∃ x₀, (d θ₂).cdf x₀ < (d θ₁).cdf x₀ := by
    by_contra h_not_strict
    push Not at h_not_strict
    have hCdfEq : ∀ x, (d θ₁).cdf x = (d θ₂).cdf x :=
      fun x => le_antisymm (h_not_strict x)
        (by simpa [IntegratedCDFTower.one_iff] using hFosd x)
    have hSetIntegralEq : ∀ s : Set ℝ, MeasurableSet s → volume s < ⊤ →
        ∫ t in s, (d θ₁).density t = ∫ t in s, (d θ₂).density t := by
      intro s hs hfin
      have hEqMeas : (d θ₁).toMeasure = (d θ₂).toMeasure := by
        haveI := (d θ₁).toMeasure_isProbability
        apply Measure.ext_of_Iic
        intro x
        simp only [ContDist.toMeasure_eq]
        rw [withDensity_apply _ measurableSet_Iic, withDensity_apply _ measurableSet_Iic]
        -- Pull each `∫⁻ ofReal ∘ density` back to `ofReal ∘ ∫ density` (density ≥ 0, integrable).
        have hLint : ∀ d : ContDist, ∫⁻ t in Iic x, ENNReal.ofReal (d.density t) =
            ENNReal.ofReal (∫ t in Iic x, d.density t) :=
          fun d => (ofReal_integral_eq_lintegral_ofReal d.integrable.integrableOn
            (ae_of_all _ d.nonneg)).symm
        rw [hLint (d θ₁), hLint (d θ₂)]
        congr 1
        have := hCdfEq x
        simp only [ContDist.cdf_eq_integral] at this
        linarith
      calc ∫ t in s, (d θ₁).density t
          = ∫ t in s, (1 : ℝ) ∂(d θ₁).toMeasure := by
            rw [(d θ₁).setIntegral_toMeasure_eq _ hs]; congr 1; ext t; ring
        _ = ∫ t in s, (1 : ℝ) ∂(d θ₂).toMeasure := by rw [hEqMeas]
        _ = ∫ t in s, (d θ₂).density t := by
            rw [(d θ₂).setIntegral_toMeasure_eq _ hs]; congr 1; ext t; ring
    have hAeEq : (fun t => (d θ₁).density t) =ᵐ[volume] (fun t => (d θ₂).density t) :=
      MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq _ _
        (d θ₁).integrable (d θ₂).integrable hSetIntegralEq
    have hNull : volume {t | (d θ₁).density t ≠ (d θ₂).density t} = 0 := hAeEq
    have extractPoint : ∀ c e : ℝ, c < e →
        ∃ t ∈ Ioo c e, (d θ₁).density t = (d θ₂).density t := by
      intro c e hce
      by_contra h_all; push Not at h_all
      have hSub : Ioo c e ⊆ {t | (d θ₁).density t ≠ (d θ₂).density t} := fun t ht => h_all t ht
      have hLe : volume (Ioo c e) ≤ volume {t | (d θ₁).density t ≠ (d θ₂).density t} :=
        measure_mono hSub
      have hPos : (0 : ENNReal) < volume (Ioo c e) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
      exact absurd hPos (not_lt.mpr (hLe.trans (le_of_eq hNull)))
    obtain ⟨t₁, ht₁Mem, ht₁Eq⟩ := extractPoint a ((a + b) / 2) (by linarith)
    obtain ⟨t₂, ht₂Mem, ht₂Eq⟩ := extractPoint ((a + b) / 2) b (by linarith)
    have ht₁₂ : t₁ < t₂ := lt_trans ht₁Mem.2 ht₂Mem.1
    have hStrict := h θ₁ θ₂ t₁ t₂ hθ ht₁₂
    simp only at hStrict
    rw [ht₁Eq, ht₂Eq] at hStrict
    linarith [mul_comm ((d θ₂).density t₁) ((d θ₂).density t₂)]
  exact FOSD.expect_strict_mono (d θ₂) (d θ₁) g hg hFosd hStrictCdf hInt₂ hInt₁

/-- **Strict MLRP ⇒ strict expectation monotonicity, full-support form.** When the lower density is
positive everywhere — as for the Gaussian, exponential-family location models, the logistic family,
etc. — the caller supplies `∀ t, 0 < (d θ₁).density t` directly, in place of the non-degeneracy
interval required by `expectStrictMono`. -/
lemma expectStrictMono_of_pos {d : ℝ → ContDist} (h : HasStrictMLRP d) (g : ℝ → ℝ)
    (hg : StrictMono g) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hInt₁ : Integrable (fun x => (d θ₁).density x * g x))
    (hInt₂ : Integrable (fun x => (d θ₂).density x * g x))
    (hpos : ∀ t, 0 < (d θ₁).density t) :
    (d θ₁).expect g < (d θ₂).expect g :=
  h.expectStrictMono g hg hθ hInt₁ hInt₂ ⟨θ₁ - 1, θ₁ + 1, by linarith, fun t _ => hpos t⟩

end HasStrictMLRP

end Econlib.Probability
