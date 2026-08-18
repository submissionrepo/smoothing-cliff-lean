import SmoothingCliff.Frontier.MeanField
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The general-law large-market population program

This file formalizes part (ii) of Theorem `thm:meanfield` in
`Smoothing_the_Cliff_ITCS.tex` for a **general** Borel value law `F` on `ℝ`,
completing the finite-support development in
`SmoothingCliff.Frontier.MeanField`.

An allocation curve `ξ : ℝ → ℝ` is *admissible* when it takes values in
`[0, w₁]` and is `𝒮`-Lipschitz (`CurveShape`), and *feasible* when in addition
its ex-ante mass `∫ ξ dF` respects the per-capita cap (`CurveFeasible`).  Its
value is `∫ v · ξ v dF` (`curveWelfare`).  The main results are

* `postedRamp_solves_population_program`: a posted ramp
  `ξ*(v) = clip(𝒮 (v - t), 0, w₁)` with a nonnegative threshold whose mass
  equals `min {massCap, w₁}` dominates every feasible curve;
* `postedRamp_ae_eq_of_welfare_eq`: for atomless `F` the maximizer is unique up
  to `F`-null sets;
* `exists_postedRamp_mass` and `exists_threshold_of_mass_le`: existence of the
  calibrating threshold by the intermediate value theorem, the general-law
  analogues of `exists_postedRamp_of_smaller_mass`.

The argument is the paper's exchange argument in integral form.  Writing
`h := ξ - ξ*`, the gap is nonnegative below `t`, nonpositive above the cap
point `t + w₁/𝒮`, and antitone in between because the ramp rises at exactly
the maximal admissible slope there; hence `h` crosses zero once, at some
`c ≥ t`, and `(v - c) · h v ≤ 0` pointwise.  Integrating gives
`∫ v · h dF ≤ c ∫ h dF ≤ 0`, the second inequality because the mass constraint
and the pointwise cap force `∫ ξ dF ≤ min {massCap, w₁} = ∫ ξ* dF` while
`c ≥ t ≥ 0`.

Integrability is supplied by a finite first moment of `F`
(`Integrable id F`), which the paper's bounded value range `[r, b̄]` implies.
The paper's standing `𝒮 > 0` is used, since the cap point `t + w₁/𝒮` is where
the ramp stops rising.  Nothing here needs values to be nonnegative: only the
threshold has to satisfy `t ≥ 0`.

This file covers part (ii) only.  The finite-market reduction of part (i) and
the rationing bound of part (iii) live in `SmoothingCliff.Frontier.MeanField`
in their finite-support form; the bridges from a jointly measurable
finite-agent rule to interim curves and from inclusion probabilities to
lotteries with Myerson transfers remain outside the project.
-/

open MeasureTheory

open scoped BigOperators

namespace SmoothingCliff.Frontier

/-- Ex-ante allocation mass of a population curve under a general value law. -/
noncomputable def curveMass (F : Measure ℝ) (ξ : ℝ → ℝ) : ℝ :=
  ∫ v, ξ v ∂F

/-- Ex-ante value-weighted allocation of a population curve under a general
value law. -/
noncomputable def curveWelfare (F : Measure ℝ) (ξ : ℝ → ℝ) : ℝ :=
  ∫ v, v * ξ v ∂F

/-- The pointwise and Lipschitz restrictions in the population program. -/
structure CurveShape (weight sensitivity : NNReal) (ξ : ℝ → ℝ) : Prop where
  nonneg : ∀ v, 0 ≤ ξ v
  le_weight : ∀ v, ξ v ≤ weight
  lipschitz : LipschitzWith sensitivity ξ

/-- Feasibility for the general-law population program. -/
structure CurveFeasible (F : Measure ℝ) (weight sensitivity : NNReal)
    (massCap : ℝ) (ξ : ℝ → ℝ) : Prop extends CurveShape weight sensitivity ξ where
  mass_le : curveMass F ξ ≤ massCap

namespace CurveShape

variable {weight sensitivity : NNReal} {ξ : ℝ → ℝ}

theorem continuous (h : CurveShape weight sensitivity ξ) : Continuous ξ :=
  h.lipschitz.continuous

theorem measurable (h : CurveShape weight sensitivity ξ) : Measurable ξ :=
  h.continuous.measurable

theorem abs_le (h : CurveShape weight sensitivity ξ) (v : ℝ) :
    |ξ v| ≤ (weight : ℝ) := by
  rw [abs_of_nonneg (h.nonneg v)]
  exact h.le_weight v

/-- A curve bounded by the slot weight is integrable under any finite law. -/
theorem integrable (F : Measure ℝ) [IsFiniteMeasure F]
    (h : CurveShape weight sensitivity ξ) : Integrable ξ F := by
  refine (integrable_const (weight : ℝ)).mono'
    h.measurable.aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact h.abs_le v

/-- The value-weighted integrand is integrable as soon as the law has a finite
first moment. -/
theorem integrable_value_mul (F : Measure ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (h : CurveShape weight sensitivity ξ) :
    Integrable (fun v => v * ξ v) F := by
  refine (hFirstMoment.abs.const_mul (weight : ℝ)).mono'
    (measurable_id.mul h.measurable).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_mul]
  have hbound := mul_le_mul_of_nonneg_left (h.abs_le v) (abs_nonneg v)
  linarith [hbound]

end CurveShape

/-- The posted ramp is an admissible curve. -/
theorem postedRamp_curveShape (weight sensitivity : NNReal) (threshold : ℝ) :
    CurveShape weight sensitivity (postedRamp weight sensitivity threshold) :=
  { nonneg := postedRamp_nonneg weight sensitivity threshold
    le_weight := postedRamp_le weight sensitivity threshold
    lipschitz := postedRamp_lipschitz weight sensitivity threshold }

/-! ### Single crossing -/

/-- A gap function that is nonnegative below `lo`, nonpositive above `hi`, and
antitone on `[lo, hi]` crosses zero at a single point of `[lo, hi]`. -/
theorem exists_single_crossing {g : ℝ → ℝ} {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hlow : ∀ v, v ≤ lo → 0 ≤ g v)
    (hhigh : ∀ v, hi ≤ v → g v ≤ 0)
    (hanti : ∀ v v', lo ≤ v → v ≤ v' → v' ≤ hi → g v' ≤ g v) :
    ∃ c ∈ Set.Icc lo hi, ∀ v, (v - c) * g v ≤ 0 := by
  classical
  by_cases hpos : ∀ v, lo ≤ v → v ≤ hi → 0 ≤ g v
  · refine ⟨hi, ⟨hlohi, le_refl hi⟩, ?_⟩
    intro v
    rcases le_or_gt v hi with hv | hv
    · have hg : 0 ≤ g v := by
        rcases le_or_gt v lo with hv' | hv'
        · exact hlow v hv'
        · exact hpos v hv'.le hv
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hg
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hhigh v hv.le)
  · push Not at hpos
    obtain ⟨v₀, hv₀lo, hv₀hi, hv₀⟩ := hpos
    set T : Set ℝ := {v | lo ≤ v ∧ v ≤ hi ∧ g v ≤ 0} with hT
    have hv₀mem : v₀ ∈ T := ⟨hv₀lo, hv₀hi, hv₀.le⟩
    have hTne : T.Nonempty := ⟨v₀, hv₀mem⟩
    have hTbdd : BddBelow T := ⟨lo, fun x hx => hx.1⟩
    have hclo : lo ≤ sInf T := le_csInf hTne fun x hx => hx.1
    have hchi : sInf T ≤ hi := le_trans (csInf_le hTbdd hv₀mem) hv₀hi
    refine ⟨sInf T, ⟨hclo, hchi⟩, ?_⟩
    intro v
    rcases lt_trichotomy v (sInf T) with hv | hv | hv
    · have hg : 0 ≤ g v := by
        rcases le_or_gt v lo with hv' | hv'
        · exact hlow v hv'
        · by_contra hneg
          push Not at hneg
          have hmem : v ∈ T := ⟨hv'.le, le_trans hv.le hchi, hneg.le⟩
          exact absurd (csInf_le hTbdd hmem) (not_le.mpr hv)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hg
    · rw [hv]
      simp
    · have hg : g v ≤ 0 := by
        rcases le_or_gt hi v with hv' | hv'
        · exact hhigh v hv'
        · obtain ⟨x, hxT, hxv⟩ := exists_lt_of_csInf_lt hTne hv
          obtain ⟨hx1, hx2, hx3⟩ := hxT
          exact le_trans (hanti x v hx1 hxv.le hv'.le) hx3
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hg

/-- The exchange direction of the paper's argument: the gap between an
admissible curve and the posted ramp changes sign exactly once, at a point at
or above the ramp threshold. -/
theorem exists_crossing_point (weight sensitivity : NNReal)
    (hSensitivity : 0 < sensitivity) (threshold : ℝ)
    {ξ : ℝ → ℝ} (hξ : CurveShape weight sensitivity ξ) :
    ∃ c, threshold ≤ c ∧ ∀ v,
      (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ≤ 0 := by
  have hSpos : (0 : ℝ) < (sensitivity : ℝ) := by exact_mod_cast hSensitivity
  have hwnonneg : (0 : ℝ) ≤ (weight : ℝ) := weight.coe_nonneg
  have hquot : 0 ≤ (weight : ℝ) / (sensitivity : ℝ) :=
    div_nonneg hwnonneg hSpos.le
  have hid : (sensitivity : ℝ) * ((weight : ℝ) / (sensitivity : ℝ))
      = (weight : ℝ) := by
    field_simp
  have hlohi : threshold ≤ threshold + (weight : ℝ) / (sensitivity : ℝ) := by
    linarith
  have hlow : ∀ v, v ≤ threshold →
      0 ≤ ξ v - postedRamp weight sensitivity threshold v := by
    intro v hv
    rw [postedRamp_zero_of_value_le_threshold weight sensitivity hv]
    simpa using hξ.nonneg v
  have hhigh : ∀ v, threshold + (weight : ℝ) / (sensitivity : ℝ) ≤ v →
      ξ v - postedRamp weight sensitivity threshold v ≤ 0 := by
    intro v hv
    have hstep : (weight : ℝ) / (sensitivity : ℝ) ≤ v - threshold := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstep hSpos.le
    have hz : (weight : ℝ) ≤ (sensitivity : ℝ) * (v - threshold) := by
      rw [hid] at hmul
      exact hmul
    rw [postedRamp, clampWeight_eq_weight_of_le weight hz]
    linarith [hξ.le_weight v]
  have hmidramp : ∀ v, threshold ≤ v →
      v ≤ threshold + (weight : ℝ) / (sensitivity : ℝ) →
      postedRamp weight sensitivity threshold v
        = (sensitivity : ℝ) * (v - threshold) := by
    intro v hv1 hv2
    rw [postedRamp]
    refine clampWeight_eq_of_mem weight (mul_nonneg hSpos.le (by linarith)) ?_
    have hstep : v - threshold ≤ (weight : ℝ) / (sensitivity : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstep hSpos.le
    rw [hid] at hmul
    exact hmul
  have hanti : ∀ v v', threshold ≤ v → v ≤ v' →
      v' ≤ threshold + (weight : ℝ) / (sensitivity : ℝ) →
      ξ v' - postedRamp weight sensitivity threshold v'
        ≤ ξ v - postedRamp weight sensitivity threshold v := by
    intro v v' h1 h2 h3
    have hlip : |ξ v' - ξ v| ≤ (sensitivity : ℝ) * |v' - v| := by
      simpa [Real.dist_eq] using hξ.lipschitz.dist_le_mul v' v
    have hslope : ξ v' - ξ v ≤ (sensitivity : ℝ) * (v' - v) := by
      have habs := (abs_le.mp hlip).2
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ v' - v)] at habs
    rw [hmidramp v h1 (by linarith), hmidramp v' (by linarith) h3]
    have hring : (sensitivity : ℝ) * (v' - threshold)
        - (sensitivity : ℝ) * (v - threshold)
        = (sensitivity : ℝ) * (v' - v) := by ring
    linarith
  obtain ⟨c, hcmem, hcross⟩ :=
    exists_single_crossing (g := fun v =>
      ξ v - postedRamp weight sensitivity threshold v) hlohi hlow hhigh hanti
  exact ⟨c, hcmem.1, hcross⟩

/-! ### The ramp solves the program -/

/-- The mass of a feasible curve never exceeds the calibrating level
`min {massCap, w₁}`: the cap bounds it directly and the pointwise ceiling
bounds it under a probability law. -/
theorem curveMass_le_min (F : Measure ℝ) [IsProbabilityMeasure F]
    {weight sensitivity : NNReal} {massCap : ℝ} {ξ : ℝ → ℝ}
    (hξ : CurveFeasible F weight sensitivity massCap ξ) :
    curveMass F ξ ≤ min massCap (weight : ℝ) := by
  refine le_min hξ.mass_le ?_
  have hmono := integral_mono (hξ.toCurveShape.integrable F)
    (integrable_const (weight : ℝ)) (fun v => hξ.le_weight v)
  simpa [curveMass] using hmono

/-- Part (ii) of Theorem `thm:meanfield`: for a general value law with a finite
first moment, a posted ramp with a nonnegative threshold calibrated to the
per-capita cap weakly dominates every feasible curve. -/
theorem postedRamp_solves_population_program
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hSensitivity : 0 < sensitivity)
    (massCap threshold : ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hThreshold : 0 ≤ threshold)
    (hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min massCap (weight : ℝ))
    {ξ : ℝ → ℝ} (hξ : CurveFeasible F weight sensitivity massCap ξ) :
    curveWelfare F ξ
      ≤ curveWelfare F (postedRamp weight sensitivity threshold) := by
  obtain ⟨c, hc, hcross⟩ := exists_crossing_point weight sensitivity
    hSensitivity threshold hξ.toCurveShape
  have hrampShape := postedRamp_curveShape weight sensitivity threshold
  have hξint : Integrable ξ F := hξ.toCurveShape.integrable F
  have hrint : Integrable (postedRamp weight sensitivity threshold) F :=
    hrampShape.integrable F
  have hξvint : Integrable (fun v => v * ξ v) F :=
    hξ.toCurveShape.integrable_value_mul F hFirstMoment
  have hrvint :
      Integrable (fun v => v * postedRamp weight sensitivity threshold v) F :=
    hrampShape.integrable_value_mul F hFirstMoment
  have hcnonneg : 0 ≤ c := le_trans hThreshold hc
  have hmassGap :
      curveMass F ξ - curveMass F (postedRamp weight sensitivity threshold)
        ≤ 0 := by
    have hmin := curveMass_le_min F hξ
    rw [hRampMass]
    linarith
  have hfun :
      (fun v => (v - c) * (ξ v - postedRamp weight sensitivity threshold v))
        = fun v => (v * ξ v - v * postedRamp weight sensitivity threshold v)
          - c * (ξ v - postedRamp weight sensitivity threshold v) := by
    funext v
    ring
  have hsplit :
      (∫ v, (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = (curveWelfare F ξ
            - curveWelfare F (postedRamp weight sensitivity threshold))
          - c * (curveMass F ξ
            - curveMass F (postedRamp weight sensitivity threshold)) := by
    have hvgint : Integrable (fun v =>
        v * ξ v - v * postedRamp weight sensitivity threshold v) F :=
      hξvint.sub hrvint
    have hgint : Integrable (fun v =>
        ξ v - postedRamp weight sensitivity threshold v) F := hξint.sub hrint
    have hcgint : Integrable (fun v =>
        c * (ξ v - postedRamp weight sensitivity threshold v)) F :=
      hgint.const_mul c
    have hA : (∫ v, (v * ξ v
          - v * postedRamp weight sensitivity threshold v) ∂F)
        = (∫ v, v * ξ v ∂F)
          - ∫ v, v * postedRamp weight sensitivity threshold v ∂F :=
      integral_sub hξvint hrvint
    have hB : (∫ v, (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = (∫ v, ξ v ∂F)
          - ∫ v, postedRamp weight sensitivity threshold v ∂F :=
      integral_sub hξint hrint
    have hC : (∫ v, c * (ξ v
          - postedRamp weight sensitivity threshold v) ∂F)
        = c * ∫ v, (ξ v - postedRamp weight sensitivity threshold v) ∂F :=
      integral_const_mul c _
    have hD : (∫ v, (v * ξ v
          - v * postedRamp weight sensitivity threshold v
          - c * (ξ v - postedRamp weight sensitivity threshold v)) ∂F)
        = (∫ v, (v * ξ v
            - v * postedRamp weight sensitivity threshold v) ∂F)
          - ∫ v, c * (ξ v
            - postedRamp weight sensitivity threshold v) ∂F :=
      integral_sub hvgint hcgint
    have hE : (∫ v, (v - c)
          * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = ∫ v, (v * ξ v
            - v * postedRamp weight sensitivity threshold v
            - c * (ξ v - postedRamp weight sensitivity threshold v)) ∂F := by
      apply integral_congr_ae
      filter_upwards with v
      ring
    rw [hB] at hC
    simp only [curveWelfare, curveMass]
    linarith [hA, hC, hD, hE]
  have hcrossint :
      (∫ v, (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        ≤ 0 := integral_nonpos hcross
  have hcmass : c * (curveMass F ξ
      - curveMass F (postedRamp weight sensitivity threshold)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcnonneg hmassGap
  linarith

/-- Uniqueness up to `F`-null sets: for an atomless law, any feasible curve
attaining the ramp's value agrees with the ramp almost everywhere. -/
theorem postedRamp_ae_eq_of_welfare_eq
    (F : Measure ℝ) [IsProbabilityMeasure F] [NoAtoms F]
    (weight sensitivity : NNReal) (hSensitivity : 0 < sensitivity)
    (massCap threshold : ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hThreshold : 0 ≤ threshold)
    (hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min massCap (weight : ℝ))
    {ξ : ℝ → ℝ} (hξ : CurveFeasible F weight sensitivity massCap ξ)
    (hEq : curveWelfare F ξ
      = curveWelfare F (postedRamp weight sensitivity threshold)) :
    ξ =ᵐ[F] postedRamp weight sensitivity threshold := by
  obtain ⟨c, hc, hcross⟩ := exists_crossing_point weight sensitivity
    hSensitivity threshold hξ.toCurveShape
  have hrampShape := postedRamp_curveShape weight sensitivity threshold
  have hξint : Integrable ξ F := hξ.toCurveShape.integrable F
  have hrint : Integrable (postedRamp weight sensitivity threshold) F :=
    hrampShape.integrable F
  have hξvint : Integrable (fun v => v * ξ v) F :=
    hξ.toCurveShape.integrable_value_mul F hFirstMoment
  have hrvint :
      Integrable (fun v => v * postedRamp weight sensitivity threshold v) F :=
    hrampShape.integrable_value_mul F hFirstMoment
  have hcnonneg : 0 ≤ c := le_trans hThreshold hc
  have hmassGap :
      curveMass F ξ - curveMass F (postedRamp weight sensitivity threshold)
        ≤ 0 := by
    have hmin := curveMass_le_min F hξ
    rw [hRampMass]
    linarith
  have hfun :
      (fun v => (v - c) * (ξ v - postedRamp weight sensitivity threshold v))
        = fun v => (v * ξ v - v * postedRamp weight sensitivity threshold v)
          - c * (ξ v - postedRamp weight sensitivity threshold v) := by
    funext v
    ring
  have hcrossIntegrable :
      Integrable
        (fun v => (v - c) * (ξ v - postedRamp weight sensitivity threshold v))
        F := by
    rw [hfun]
    exact (hξvint.sub hrvint).sub ((hξint.sub hrint).const_mul c)
  have hsplit :
      (∫ v, (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = (curveWelfare F ξ
            - curveWelfare F (postedRamp weight sensitivity threshold))
          - c * (curveMass F ξ
            - curveMass F (postedRamp weight sensitivity threshold)) := by
    have hvgint : Integrable (fun v =>
        v * ξ v - v * postedRamp weight sensitivity threshold v) F :=
      hξvint.sub hrvint
    have hgint : Integrable (fun v =>
        ξ v - postedRamp weight sensitivity threshold v) F := hξint.sub hrint
    have hcgint : Integrable (fun v =>
        c * (ξ v - postedRamp weight sensitivity threshold v)) F :=
      hgint.const_mul c
    have hA : (∫ v, (v * ξ v
          - v * postedRamp weight sensitivity threshold v) ∂F)
        = (∫ v, v * ξ v ∂F)
          - ∫ v, v * postedRamp weight sensitivity threshold v ∂F :=
      integral_sub hξvint hrvint
    have hB : (∫ v, (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = (∫ v, ξ v ∂F)
          - ∫ v, postedRamp weight sensitivity threshold v ∂F :=
      integral_sub hξint hrint
    have hC : (∫ v, c * (ξ v
          - postedRamp weight sensitivity threshold v) ∂F)
        = c * ∫ v, (ξ v - postedRamp weight sensitivity threshold v) ∂F :=
      integral_const_mul c _
    have hD : (∫ v, (v * ξ v
          - v * postedRamp weight sensitivity threshold v
          - c * (ξ v - postedRamp weight sensitivity threshold v)) ∂F)
        = (∫ v, (v * ξ v
            - v * postedRamp weight sensitivity threshold v) ∂F)
          - ∫ v, c * (ξ v
            - postedRamp weight sensitivity threshold v) ∂F :=
      integral_sub hvgint hcgint
    have hE : (∫ v, (v - c)
          * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = ∫ v, (v * ξ v
            - v * postedRamp weight sensitivity threshold v
            - c * (ξ v - postedRamp weight sensitivity threshold v)) ∂F := by
      apply integral_congr_ae
      filter_upwards with v
      ring
    rw [hB] at hC
    simp only [curveWelfare, curveMass]
    linarith [hA, hC, hD, hE]
  have hcrossint :
      (∫ v, (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        ≤ 0 := integral_nonpos hcross
  have hcmass : c * (curveMass F ξ
      - curveMass F (postedRamp weight sensitivity threshold)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcnonneg hmassGap
  have hcrosszero :
      (∫ v, (v - c) * (ξ v - postedRamp weight sensitivity threshold v) ∂F)
        = 0 := by
    rw [hsplit, hEq]
    linarith
  have hnegzero :
      (∫ v, -((v - c) * (ξ v - postedRamp weight sensitivity threshold v)) ∂F)
        = 0 := by
    rw [integral_neg, hcrosszero, neg_zero]
  have hnegnonneg :
      (0 : ℝ → ℝ) ≤ fun v =>
        -((v - c) * (ξ v - postedRamp weight sensitivity threshold v)) := by
    intro v
    exact neg_nonneg.mpr (hcross v)
  have hae := (integral_eq_zero_iff_of_nonneg hnegnonneg
    hcrossIntegrable.neg).mp hnegzero
  have hne : ∀ᵐ v ∂F, v ≠ c := by
    rw [ae_iff]
    simp
  filter_upwards [hae, hne] with v hv hvne
  have hvzero : -((v - c) * (ξ v - postedRamp weight sensitivity threshold v))
      = 0 := hv
  have hzero : (v - c) * (ξ v - postedRamp weight sensitivity threshold v)
      = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hvne
  · exact sub_eq_zero.mp h

/-! ### Existence of the calibrating threshold -/

/-- Ex-ante mass posted by the ramp at a given threshold. -/
noncomputable def rampMass (F : Measure ℝ) (weight sensitivity : NNReal)
    (threshold : ℝ) : ℝ :=
  curveMass F (postedRamp weight sensitivity threshold)

theorem rampMass_antitone (F : Measure ℝ) [IsFiniteMeasure F]
    (weight sensitivity : NNReal) :
    Antitone (rampMass F weight sensitivity) := by
  intro s t hst
  refine integral_mono
    ((postedRamp_curveShape weight sensitivity t).integrable F)
    ((postedRamp_curveShape weight sensitivity s).integrable F) ?_
  intro v
  exact postedRamp_antitone_threshold weight sensitivity v hst

/-- The posted mass moves by at most `𝒮` per unit of threshold, so it is a
Lipschitz, hence continuous, function of the threshold. -/
theorem rampMass_lipschitz (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) :
    LipschitzWith sensitivity (rampMass F weight sensitivity) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hs := (postedRamp_curveShape weight sensitivity s).integrable F
  have ht := (postedRamp_curveShape weight sensitivity t).integrable F
  have hpoint : ∀ v, |postedRamp weight sensitivity s v
      - postedRamp weight sensitivity t v| ≤ (sensitivity : ℝ) * dist s t := by
    intro v
    have hclamp : |clampWeight weight ((sensitivity : ℝ) * (v - s))
        - clampWeight weight ((sensitivity : ℝ) * (v - t))|
        ≤ |(sensitivity : ℝ) * (v - s) - (sensitivity : ℝ) * (v - t)| := by
      simpa [Real.dist_eq] using (clampWeight_lipschitz weight).dist_le_mul
        ((sensitivity : ℝ) * (v - s)) ((sensitivity : ℝ) * (v - t))
    have hring : (sensitivity : ℝ) * (v - s) - (sensitivity : ℝ) * (v - t)
        = (sensitivity : ℝ) * (t - s) := by ring
    rw [hring, abs_mul, abs_of_nonneg sensitivity.coe_nonneg] at hclamp
    have hdist : |t - s| = dist s t := by
      rw [Real.dist_eq, abs_sub_comm]
    rw [hdist] at hclamp
    simpa [postedRamp] using hclamp
  have hbound : (∫ v, |postedRamp weight sensitivity s v
      - postedRamp weight sensitivity t v| ∂F)
      ≤ (sensitivity : ℝ) * dist s t := by
    have hmono := integral_mono (hs.sub ht).abs
      (integrable_const ((sensitivity : ℝ) * dist s t)) hpoint
    simpa using hmono
  calc dist (rampMass F weight sensitivity s) (rampMass F weight sensitivity t)
      = |(∫ v, postedRamp weight sensitivity s v ∂F)
          - ∫ v, postedRamp weight sensitivity t v ∂F| := by
        rw [Real.dist_eq]
        rfl
    _ = |∫ v, (postedRamp weight sensitivity s v
          - postedRamp weight sensitivity t v) ∂F| := by
        rw [integral_sub hs ht]
    _ ≤ ∫ v, |postedRamp weight sensitivity s v
          - postedRamp weight sensitivity t v| ∂F :=
        abs_integral_le_integral_abs
    _ ≤ (sensitivity : ℝ) * dist s t := hbound

theorem rampMass_continuous (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) :
    Continuous (rampMass F weight sensitivity) :=
  (rampMass_lipschitz F weight sensitivity).continuous

/-- A threshold at the top of the support posts no mass. -/
theorem rampMass_eq_zero_of_support_le (F : Measure ℝ)
    (weight sensitivity : NNReal) {upper : ℝ}
    (hSupport : F (Set.Ioi upper) = 0) :
    rampMass F weight sensitivity upper = 0 := by
  have hle : ∀ᵐ v ∂F, v ≤ upper := by
    rw [ae_iff]
    simpa using hSupport
  have hae : (fun v => postedRamp weight sensitivity upper v)
      =ᵐ[F] fun _ => 0 := by
    filter_upwards [hle] with v hv
    exact postedRamp_zero_of_value_le_threshold weight sensitivity hv
  simpa [rampMass, curveMass] using integral_congr_ae hae

/-- General-law analogue of `exists_postedRamp_of_smaller_mass`: every mass
between zero and the mass posted at a starting threshold is posted by some
threshold weakly above it, by the intermediate value theorem. -/
theorem exists_postedRamp_mass (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) {lower upper mass : ℝ}
    (hlower : lower ≤ upper) (hSupport : F (Set.Ioi upper) = 0)
    (hMassNonneg : 0 ≤ mass)
    (hMassLe : mass ≤ rampMass F weight sensitivity lower) :
    ∃ t ∈ Set.Icc lower upper, rampMass F weight sensitivity t = mass := by
  have hzero : rampMass F weight sensitivity upper = 0 :=
    rampMass_eq_zero_of_support_le F weight sensitivity hSupport
  have hmem : mass ∈ Set.Icc (rampMass F weight sensitivity upper)
      (rampMass F weight sensitivity lower) := by
    simpa [hzero] using ⟨hMassNonneg, hMassLe⟩
  obtain ⟨t, ht, hEq⟩ := intermediate_value_Icc' hlower
    (rampMass_continuous F weight sensitivity).continuousOn hmem
  exact ⟨t, ht, hEq⟩

/-- Existence of the calibrating threshold `t* ≥ 0` of Theorem
`thm:meanfield`(ii): whenever the target level `min {massCap, w₁}` is within
reach at threshold zero and the law is supported below `upper`, some
nonnegative threshold posts exactly that mass. -/
theorem exists_threshold_of_mass_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) {massCap upper : ℝ}
    (hUpper : 0 ≤ upper) (hSupport : F (Set.Ioi upper) = 0)
    (hMassCap : 0 ≤ massCap)
    (hReach : min massCap (weight : ℝ) ≤ rampMass F weight sensitivity 0) :
    ∃ t, 0 ≤ t ∧ curveMass F (postedRamp weight sensitivity t)
      = min massCap (weight : ℝ) := by
  obtain ⟨t, ht, hEq⟩ := exists_postedRamp_mass F weight sensitivity hUpper
    hSupport (le_min hMassCap weight.coe_nonneg) hReach
  exact ⟨t, ht.1, hEq⟩

/-! ### The program hypotheses are jointly satisfiable -/

/-- A witness that `postedRamp_solves_population_program` is not vacuous: the
Dirac law at `1`, unit weight and sensitivity, per-capita cap `1/2` and
threshold `1/2` satisfy every hypothesis at once, with the zero curve as a
feasible comparison. -/
example : curveWelfare (Measure.dirac (1 : ℝ)) (fun _ => 0)
    ≤ curveWelfare (Measure.dirac (1 : ℝ)) (postedRamp 1 1 (1 / 2)) :=
  postedRamp_solves_population_program (Measure.dirac (1 : ℝ)) 1 1 (by norm_num)
    (1 / 2) (1 / 2) (integrable_dirac (by simp)) (by norm_num)
    (by
      unfold curveMass
      rw [integral_dirac, postedRamp, clampWeight_eq_of_mem] <;> norm_num)
    ⟨⟨fun _ => le_refl 0, fun _ => by norm_num,
        (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)⟩,
      by
        unfold curveMass
        simp⟩

end SmoothingCliff.Frontier
