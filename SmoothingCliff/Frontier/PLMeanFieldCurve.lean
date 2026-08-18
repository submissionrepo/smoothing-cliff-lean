import SmoothingCliff.Frontier.InterimBridgeMeanField
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The PL rule's large-market allocation curve

This file formalizes the second half of Remark `rem:plmeanfield` in
`Smoothing_the_Cliff_ITCS.tex`.  For the Plackett-Luce rule run at temperature
`τ` with the matched certificate `𝒮 = w₁/(e τ)`, the paper's large-market
inclusion curve is

```
  ξ_PL(v) = w₁ (1 - exp (-θ α v)),        α v = exp ((v - r) / τ),
```

with the market-clearing clock `θ` pinned down by
`∫ (1 - exp (-θ α v)) dF v = γ`.  Three statements are proved.

* **Clock.** `existsUnique_plClock`: for `γ ∈ (0,1)` there is exactly one
  `θ > 0` solving the clearing equation.  `plMass` is continuous on `[0,∞)` by
  dominated convergence (`continuousOn_plMass`), vanishes at `θ = 0`
  (`plMass_zero`), is strictly increasing (`plMass_lt_plMass`), and tends to
  `1` along `θ = n → ∞` (`tendsto_plMass_atTop`), again by dominated
  convergence; the intermediate value theorem supplies the root and strict
  monotonicity its uniqueness.  *No support hypothesis on `F` is needed.*  The
  reason is that `α v > 0` at every real `v`, so `θ ↦ 1 - exp (-θ α v)` is
  strictly increasing and converges to `1` pointwise on all of `ℝ`; the
  paper's bounded value range `[r, b̄]` would give the cruder lower bound
  `1 - exp (-θ)` but is not needed.  Only `IsProbabilityMeasure F` and
  `τ > 0` are used.

* **Feasibility.** `plCurve_curveFeasible`: `ξ_PL` satisfies
  `CurveShape w₁ 𝒮` at exactly `𝒮 = w₁/(e τ)`, and `curveMass F ξ_PL = w₁ γ`,
  so it is feasible for the program of `thm:meanfield` at `massCap = w₁ γ`.
  Nonnegativity and the `w₁` ceiling are immediate.  The Lipschitz bound is
  the step that fixes the constant:
  `ξ_PL' v = (w₁ / τ) · x · exp (-x)` with `x = θ α v ≥ 0`
  (`hasDerivAt_plCurve`), and `sup_x x exp (-x) = exp (-1)`
  (`mul_exp_neg_le_exp_neg_one`), attained at `x = 1`
  (`mul_exp_neg_eq_at_one`).  So the Lipschitz constant of `ξ_PL` is
  `w₁ · exp (-1) / τ = w₁/(e τ) = 𝒮`, and `hasDerivAt_plCurve_eq_plSensitivity`
  shows the derivative equals `𝒮` exactly, at `v* = r + τ log (1/θ)`, where
  `θ α v* = 1`.  This coincidence between the published cap and the steepest
  slope the PL curve ever attains is what the paper means by calling
  `𝒮 = w₁/(e τ)` the *matched* certificate: the PL rule is certified by `𝒮` and
  by nothing smaller.

* **Strictly inside the frontier.** `plCurve_welfare_lt_postedRamp` and
  `plCurve_welfare_lt_populationValue`: for atomless `F`, `ξ_PL` is feasible
  but its value is strictly below the calibrated ramp's, hence strictly below
  the program value.  The route is the uniqueness clause
  `postedRamp_ae_eq_of_welfare_eq` of
  `SmoothingCliff.Frontier.PopulationProgram`: equal welfare would force
  `ξ_PL = ξ*` `F`-almost everywhere, while `ξ_PL` is strictly positive at every
  real value (`plCurve_pos`) and the ramp vanishes weakly below its threshold,
  so the two differ on all of `Set.Iio t`.  The hypothesis that makes this
  bite is `F (Set.Iio t) ≠ 0`: the law must put positive mass strictly below
  the ramp threshold.  Plainly: this is what "atomless `F`" plus a
  nondegenerate ramp delivers.  A ramp calibrated to `massCap = w₁ γ < w₁`
  cannot sit at the bottom of an atomless law's support and still clear only a
  `γ` fraction of the mass, so its threshold lands in the interior of the
  support and `F (Set.Iio t) > 0`.  The hypothesis is kept explicit rather than
  derived because "interior of the support" is not implied by `NoAtoms F`
  alone: a law concentrated on `[t, t + ε]` is atomless and calibrates a ramp
  at exactly `t`.  Deriving it would need a support-position assumption the
  paper leaves implicit.  The `Set.Iio` form matches the paper's "below the
  threshold"; under `NoAtoms F` it is equivalent to the `Set.Iic` form.

## Not formalized

The **first** half of the remark is not formalized here: the derivation of
`ξ_PL` as the `n → ∞` limit of the PL race's `K_n`-th order statistic along a
sequence with `K_n / n → γ ∈ (0,1)`, by concentration of the exponential
race's order statistics (the paper's Glivenko-Cantelli argument).  Closing it
would need the exponential-race representation of the finite-`n` PL rule as a
family of independent clocks with rates `α (v_i)`, a uniform law of large
numbers for the empirical distribution of ring times under a triangular array,
and a continuity argument transferring convergence of the empirical
`K_n / n`-quantile to convergence of the interim inclusion probabilities.
None of that is present in this project.  The limit is **not** assumed as a
hypothesis of any theorem below: `plCurve` is *defined* by the closed form and
everything proved here is proved about that definition.
-/

open MeasureTheory Filter Topology

namespace SmoothingCliff.Frontier

/-! ### The elementary bound `sup_{x ≥ 0} x e^{-x} = 1/e` -/

/-- `x e^{-x} ≤ 1/e` for every real `x`.  Equivalent to `x ≤ e^{x-1}`, which is
`Real.add_one_le_exp` at `x - 1`. -/
theorem mul_exp_neg_le_exp_neg_one (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have hx : x ≤ Real.exp (x - 1) := by
    have h := Real.add_one_le_exp (x - 1)
    linarith
  calc x * Real.exp (-x)
      ≤ Real.exp (x - 1) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- The bound `sup_{x ≥ 0} x e^{-x} = 1/e` is *attained*, at `x = 1`.  This is
why the paper calls `𝒮 = w₁/(e τ)` a matched certificate: the PL curve's slope
reaches exactly `𝒮` at the value where `θ α v = 1`. -/
theorem mul_exp_neg_eq_at_one : (1 : ℝ) * Real.exp (-1) = Real.exp (-1) := one_mul _

/-! ### The curve -/

/-- The PL rule's exponential-race intensity `α(v) = e^{(v-r)/τ}`. -/
noncomputable def plAlpha (reserve temperature v : ℝ) : ℝ :=
  Real.exp ((v - reserve) / temperature)

theorem plAlpha_pos (reserve temperature v : ℝ) : 0 < plAlpha reserve temperature v :=
  Real.exp_pos _

/-- Inclusion probability of a value-`v` agent when the market-clearing clock
reads `θ`: her exponential clock of rate `α v` has rung by time `θ`. -/
noncomputable def plInclusion (reserve temperature clock v : ℝ) : ℝ :=
  1 - Real.exp (-(clock * plAlpha reserve temperature v))

/-- The PL rule's large-market allocation curve
`ξ_PL(v) = w₁ (1 - e^{-θ α(v)})`. -/
noncomputable def plCurve (weight : NNReal) (reserve temperature clock v : ℝ) : ℝ :=
  (weight : ℝ) * plInclusion reserve temperature clock v

/-- The matched certificate `𝒮 = w₁ / (e τ)` of the remark. -/
noncomputable def plSensitivity (weight : NNReal) (temperature : ℝ) : NNReal :=
  Real.toNNReal ((weight : ℝ) / (Real.exp 1 * temperature))

theorem coe_plSensitivity (weight : NNReal) {temperature : ℝ} (hτ : 0 < temperature) :
    (plSensitivity weight temperature : ℝ)
      = (weight : ℝ) / (Real.exp 1 * temperature) :=
  Real.coe_toNNReal _ (div_nonneg weight.coe_nonneg (by positivity))

theorem plSensitivity_pos (weight : NNReal) (hweight : 0 < weight)
    {temperature : ℝ} (hτ : 0 < temperature) :
    0 < plSensitivity weight temperature := by
  have hw : (0 : ℝ) < (weight : ℝ) := NNReal.coe_pos.mpr hweight
  rw [plSensitivity, Real.toNNReal_pos]
  positivity

/-! ### Pointwise shape -/

theorem plInclusion_nonneg (reserve temperature : ℝ) {clock : ℝ}
    (hclock : 0 ≤ clock) (v : ℝ) : 0 ≤ plInclusion reserve temperature clock v := by
  have h : Real.exp (-(clock * plAlpha reserve temperature v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hclock (plAlpha_pos reserve temperature v).le))
  simp only [plInclusion]
  linarith

theorem plInclusion_le_one (reserve temperature clock v : ℝ) :
    plInclusion reserve temperature clock v ≤ 1 := by
  have h := (Real.exp_pos (-(clock * plAlpha reserve temperature v))).le
  simp only [plInclusion]
  linarith

theorem plInclusion_pos (reserve temperature : ℝ) {clock : ℝ}
    (hclock : 0 < clock) (v : ℝ) : 0 < plInclusion reserve temperature clock v := by
  have h : Real.exp (-(clock * plAlpha reserve temperature v)) < 1 :=
    Real.exp_lt_one_iff.mpr
      (neg_lt_zero.mpr (mul_pos hclock (plAlpha_pos reserve temperature v)))
  simp only [plInclusion]
  linarith

theorem continuous_plInclusion (reserve temperature clock : ℝ) :
    Continuous (plInclusion reserve temperature clock) := by
  unfold plInclusion plAlpha
  fun_prop

theorem continuous_plInclusion_clock (reserve temperature v : ℝ) :
    Continuous (fun clock : ℝ => plInclusion reserve temperature clock v) := by
  unfold plInclusion plAlpha
  fun_prop

/-- `ξ_PL` is strictly positive at every value: the PL rule randomizes over the
whole line, which is exactly why it cannot be the ramp. -/
theorem plCurve_pos (weight : NNReal) (hweight : 0 < weight) (reserve temperature : ℝ)
    {clock : ℝ} (hclock : 0 < clock) (v : ℝ) :
    0 < plCurve weight reserve temperature clock v :=
  mul_pos (NNReal.coe_pos.mpr hweight) (plInclusion_pos reserve temperature hclock v)

/-! ### The derivative and the matched Lipschitz constant -/

/-- `ξ_PL' v = (w₁ / τ) · (θ α v) · e^{-θ α v}`. -/
theorem hasDerivAt_plCurve (weight : NNReal) (reserve : ℝ) {temperature : ℝ}
    (hτ : 0 < temperature) (clock v : ℝ) :
    HasDerivAt (plCurve weight reserve temperature clock)
      ((weight : ℝ) / temperature * ((clock * plAlpha reserve temperature v)
        * Real.exp (-(clock * plAlpha reserve temperature v)))) v := by
  have hτ' : temperature ≠ 0 := ne_of_gt hτ
  have h1 : HasDerivAt (fun z : ℝ => (z - reserve) / temperature)
      (1 / temperature) v := by
    simpa using ((hasDerivAt_id v).sub_const reserve).div_const temperature
  have h2 : HasDerivAt (fun z : ℝ => plAlpha reserve temperature z)
      (plAlpha reserve temperature v * (1 / temperature)) v := h1.exp
  have h3 : HasDerivAt
      (fun z : ℝ => -(clock * plAlpha reserve temperature z))
      (-(clock * (plAlpha reserve temperature v * (1 / temperature)))) v :=
    (h2.const_mul clock).neg
  have h4 : HasDerivAt
      (fun z : ℝ => Real.exp (-(clock * plAlpha reserve temperature z)))
      (Real.exp (-(clock * plAlpha reserve temperature v))
        * -(clock * (plAlpha reserve temperature v * (1 / temperature)))) v := h3.exp
  have h5 := (h4.const_sub (1 : ℝ)).const_mul (weight : ℝ)
  convert h5 using 1
  field_simp

theorem differentiable_plCurve (weight : NNReal) (reserve : ℝ) {temperature : ℝ}
    (hτ : 0 < temperature) (clock : ℝ) :
    Differentiable ℝ (plCurve weight reserve temperature clock) :=
  fun v => (hasDerivAt_plCurve weight reserve hτ clock v).differentiableAt

/-- The Lipschitz step of the remark.  The derivative of `ξ_PL` is
`(w₁/τ) x e^{-x}` at `x = θ α v ≥ 0`, and `sup_x x e^{-x} = 1/e`, so `ξ_PL` is
Lipschitz with constant exactly `w₁ / (e τ) = 𝒮`. -/
theorem plCurve_lipschitz (weight : NNReal) (reserve : ℝ) {temperature clock : ℝ}
    (hτ : 0 < temperature) (hclock : 0 ≤ clock) :
    LipschitzWith (plSensitivity weight temperature)
      (plCurve weight reserve temperature clock) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (differentiable_plCurve weight reserve hτ clock) ?_
  intro v
  rw [(hasDerivAt_plCurve weight reserve hτ clock v).deriv,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    coe_plSensitivity weight hτ]
  set x : ℝ := clock * plAlpha reserve temperature v with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hclock (plAlpha_pos reserve temperature v).le
  have hw : (0 : ℝ) ≤ (weight : ℝ) / temperature :=
    div_nonneg weight.coe_nonneg hτ.le
  have hxe : 0 ≤ x * Real.exp (-x) := mul_nonneg hx0 (Real.exp_pos _).le
  rw [abs_of_nonneg (mul_nonneg hw hxe)]
  calc (weight : ℝ) / temperature * (x * Real.exp (-x))
      ≤ (weight : ℝ) / temperature * Real.exp (-1) :=
        mul_le_mul_of_nonneg_left (mul_exp_neg_le_exp_neg_one x) hw
    _ = (weight : ℝ) / (Real.exp 1 * temperature) := by
        rw [Real.exp_neg]
        field_simp

/-- The certificate is *matched*, not merely valid: the slope `𝒮 = w₁/(e τ)` is
attained.  At `v* = r + τ log (1/θ)` the race intensity satisfies
`θ α v* = 1`, where `x e^{-x}` peaks, so `ξ_PL' v* = w₁/(e τ) = 𝒮` exactly.
Together with `plCurve_lipschitz` this says `𝒮` is the least Lipschitz constant
of `ξ_PL`: the PL rule is certified by `w₁/(e τ)` and by nothing smaller. -/
theorem hasDerivAt_plCurve_eq_plSensitivity (weight : NNReal) (reserve : ℝ)
    {temperature clock : ℝ} (hτ : 0 < temperature) (hclock : 0 < clock) :
    HasDerivAt (plCurve weight reserve temperature clock)
      (plSensitivity weight temperature : ℝ)
      (reserve + temperature * Real.log (1 / clock)) := by
  have hτ' : temperature ≠ 0 := ne_of_gt hτ
  set v : ℝ := reserve + temperature * Real.log (1 / clock) with hv
  have hα : plAlpha reserve temperature v = 1 / clock := by
    have hsub : v - reserve = temperature * Real.log (1 / clock) := by
      rw [hv]
      ring
    have hstep : (v - reserve) / temperature = Real.log (1 / clock) := by
      rw [hsub, mul_comm, mul_div_assoc, div_self hτ', mul_one]
    rw [plAlpha, hstep, Real.exp_log (by positivity)]
  have hx : clock * plAlpha reserve temperature v = 1 := by
    rw [hα]
    field_simp
  have h := hasDerivAt_plCurve weight reserve hτ clock v
  rw [hx] at h
  rw [coe_plSensitivity weight hτ]
  convert h using 1
  rw [Real.exp_neg]
  field_simp

theorem plCurve_curveShape (weight : NNReal) (reserve : ℝ) {temperature clock : ℝ}
    (hτ : 0 < temperature) (hclock : 0 ≤ clock) :
    CurveShape weight (plSensitivity weight temperature)
      (plCurve weight reserve temperature clock) where
  nonneg v := mul_nonneg weight.coe_nonneg (plInclusion_nonneg reserve temperature hclock v)
  le_weight v :=
    mul_le_of_le_one_right weight.coe_nonneg (plInclusion_le_one reserve temperature clock v)
  lipschitz := plCurve_lipschitz weight reserve hτ hclock

/-! ### The clearing clock -/

/-- Ex-ante inclusion mass posted by the PL curve at clock `θ`, normalized by
the slot weight: the left-hand side of the paper's clearing equation. -/
noncomputable def plMass (F : Measure ℝ) (reserve temperature clock : ℝ) : ℝ :=
  ∫ v, plInclusion reserve temperature clock v ∂F

theorem plInclusion_integrable (F : Measure ℝ) [IsFiniteMeasure F]
    (reserve temperature : ℝ) {clock : ℝ} (hclock : 0 ≤ clock) :
    Integrable (plInclusion reserve temperature clock) F := by
  refine (integrable_const (1 : ℝ)).mono'
    (continuous_plInclusion reserve temperature clock).measurable.aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_of_nonneg (plInclusion_nonneg reserve temperature hclock v)]
  exact plInclusion_le_one reserve temperature clock v

theorem plMass_zero (F : Measure ℝ) [IsProbabilityMeasure F] (reserve temperature : ℝ) :
    plMass F reserve temperature 0 = 0 := by
  simp [plMass, plInclusion]

/-- Continuity of the clearing map on `[0,∞)`, by dominated convergence with
the constant bound `1`.  Only the nonnegative clocks are covered because that
is where the integrand is bounded by `1`. -/
theorem continuousOn_plMass (F : Measure ℝ) [IsProbabilityMeasure F]
    (reserve temperature : ℝ) :
    ContinuousOn (plMass F reserve temperature) (Set.Ici 0) := by
  intro θ₀ _
  refine continuousWithinAt_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const 1) ?_
  · filter_upwards with θ
    exact (continuous_plInclusion reserve temperature θ).measurable.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (plInclusion_nonneg reserve temperature hθ v)]
    exact plInclusion_le_one reserve temperature θ v
  · filter_upwards with v
    exact (continuous_plInclusion_clock reserve temperature v).continuousWithinAt

/-- The clearing map is strictly increasing on `[0,∞)`.  Strictness needs no
support hypothesis: `α v > 0` at every real `v`, so the integrand rises
strictly everywhere and `F` is a probability measure. -/
theorem plMass_lt_plMass (F : Measure ℝ) [IsProbabilityMeasure F]
    (reserve temperature : ℝ) {clock clock' : ℝ} (hclock : 0 ≤ clock)
    (hlt : clock < clock') :
    plMass F reserve temperature clock < plMass F reserve temperature clock' := by
  set g : ℝ → ℝ := fun v =>
    plInclusion reserve temperature clock' v - plInclusion reserve temperature clock v with hg
  have hpos : ∀ v, 0 < g v := by
    intro v
    have hα := plAlpha_pos reserve temperature v
    have hmul : clock * plAlpha reserve temperature v
        < clock' * plAlpha reserve temperature v := mul_lt_mul_of_pos_right hlt hα
    have hexp : Real.exp (-(clock' * plAlpha reserve temperature v))
        < Real.exp (-(clock * plAlpha reserve temperature v)) :=
      Real.exp_lt_exp.mpr (by linarith)
    simp only [hg, plInclusion]
    linarith
  have hintU : Integrable (plInclusion reserve temperature clock') F :=
    plInclusion_integrable F reserve temperature (hclock.trans hlt.le)
  have hintL : Integrable (plInclusion reserve temperature clock) F :=
    plInclusion_integrable F reserve temperature hclock
  have hint : Integrable g F := hintU.sub hintL
  have hsupp : Function.support g = Set.univ := by
    ext v
    simp [Function.mem_support, (hpos v).ne']
  have hmeas : 0 < F (Function.support g) := by
    rw [hsupp, measure_univ]
    exact zero_lt_one
  have hzero : (0 : ℝ → ℝ) ≤ g := fun v => (hpos v).le
  have hgpos : 0 < ∫ v, g v ∂F :=
    (integral_pos_iff_support_of_nonneg hzero hint).mpr hmeas
  rw [hg] at hgpos
  rw [integral_sub hintU hintL] at hgpos
  simp only [plMass]
  linarith

/-- The clearing map tends to `1` as the clock runs off to infinity, again by
dominated convergence with the constant bound `1`. -/
theorem tendsto_plMass_atTop (F : Measure ℝ) [IsProbabilityMeasure F]
    (reserve temperature : ℝ) :
    Tendsto (fun n : ℕ => plMass F reserve temperature n) atTop (𝓝 1) := by
  have hlim : Tendsto
      (fun n : ℕ => ∫ v, plInclusion reserve temperature (n : ℝ) v ∂F) atTop
      (𝓝 (∫ _v : ℝ, (1 : ℝ) ∂F)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (continuous_plInclusion reserve temperature
        (n : ℝ)).measurable.aestronglyMeasurable) (integrable_const 1) ?_ ?_
    · intro n
      filter_upwards with v
      rw [Real.norm_eq_abs,
        abs_of_nonneg (plInclusion_nonneg reserve temperature (Nat.cast_nonneg n) v)]
      exact plInclusion_le_one reserve temperature (n : ℝ) v
    · filter_upwards with v
      have hα := plAlpha_pos reserve temperature v
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) * plAlpha reserve temperature v)
          atTop atTop :=
        Filter.Tendsto.atTop_mul_const hα tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => -((n : ℝ) * plAlpha reserve temperature v))
          atTop atBot := Filter.tendsto_neg_atTop_atBot.comp h1
      have h3 : Tendsto
          (fun n : ℕ => Real.exp (-((n : ℝ) * plAlpha reserve temperature v)))
          atTop (𝓝 0) := Real.tendsto_exp_atBot.comp h2
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa [plInclusion] using hone.sub h3
  simpa [plMass] using hlim

/-- Existence of the market-clearing clock: for `γ ∈ (0,1)` some `θ > 0`
solves `∫ (1 - e^{-θ α v}) dF v = γ`, by the intermediate value theorem on
`[0, N]` for `N` large. -/
theorem exists_plClock (F : Measure ℝ) [IsProbabilityMeasure F]
    (reserve temperature : ℝ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ clock, 0 < clock ∧ plMass F reserve temperature clock = γ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, γ < plMass F reserve temperature N :=
    ((tendsto_plMass_atTop F reserve temperature).eventually
      (eventually_gt_nhds hγ1)).exists
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hcont : ContinuousOn (plMass F reserve temperature) (Set.Icc 0 (N : ℝ)) :=
    (continuousOn_plMass F reserve temperature).mono fun x hx => hx.1
  have hmem : γ ∈ Set.Icc (plMass F reserve temperature 0)
      (plMass F reserve temperature (N : ℝ)) := by
    rw [plMass_zero]
    exact ⟨hγ0.le, hN.le⟩
  obtain ⟨θ, hθmem, hθ⟩ := intermediate_value_Icc hNnonneg hcont hmem
  refine ⟨θ, ?_, hθ⟩
  rcases eq_or_lt_of_le hθmem.1 with h | h
  · rw [← h, plMass_zero] at hθ
    exact absurd hθ.symm (ne_of_gt hγ0)
  · exact h

/-- **Existence and uniqueness of the clearing clock `θ`.**  The first clause
of the remark. -/
theorem existsUnique_plClock (F : Measure ℝ) [IsProbabilityMeasure F]
    (reserve temperature : ℝ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃! clock : ℝ, 0 < clock ∧ plMass F reserve temperature clock = γ := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_plClock F reserve temperature hγ0 hγ1
  refine ⟨θ, ⟨hθ0, hθ⟩, ?_⟩
  rintro θ' ⟨hθ'0, hθ'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hstrict := plMass_lt_plMass F reserve temperature hθ'0.le h
    rw [hθ', hθ] at hstrict
    exact lt_irrefl γ hstrict
  · have hstrict := plMass_lt_plMass F reserve temperature hθ0.le h
    rw [hθ, hθ'] at hstrict
    exact lt_irrefl γ hstrict

/-! ### Feasibility for the population program -/

theorem curveMass_plCurve (F : Measure ℝ) (weight : NNReal)
    (reserve temperature clock : ℝ) :
    curveMass F (plCurve weight reserve temperature clock)
      = (weight : ℝ) * plMass F reserve temperature clock := by
  simp only [curveMass, plCurve, plMass, integral_const_mul]

/-- At the clearing clock the PL curve posts exactly the per-capita mass
`w₁ γ`. -/
theorem curveMass_plCurve_eq (F : Measure ℝ) (weight : NNReal)
    (reserve : ℝ) {temperature clock γ : ℝ}
    (hCalib : plMass F reserve temperature clock = γ) :
    curveMass F (plCurve weight reserve temperature clock) = (weight : ℝ) * γ := by
  rw [curveMass_plCurve, hCalib]

/-- **Feasibility.**  `ξ_PL` is admissible for the matched certificate
`𝒮 = w₁/(e τ)` and posts exactly the per-capita mass `w₁ γ`, so it is feasible
for the program of `thm:meanfield` at `massCap = w₁ γ`. -/
theorem plCurve_curveFeasible (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight : NNReal) (reserve : ℝ) {temperature clock γ : ℝ}
    (hτ : 0 < temperature) (hclock : 0 ≤ clock)
    (hCalib : plMass F reserve temperature clock = γ) :
    CurveFeasible F weight (plSensitivity weight temperature) ((weight : ℝ) * γ)
      (plCurve weight reserve temperature clock) where
  toCurveShape := plCurve_curveShape weight reserve hτ hclock
  mass_le := le_of_eq (curveMass_plCurve_eq F weight reserve hCalib)

/-! ### Strictly inside the frontier -/

/-- Weakly below the ramp threshold the two curves differ: the ramp is zero
there and `ξ_PL` is strictly positive everywhere. -/
theorem postedRamp_lt_plCurve_of_le_threshold (weight : NNReal) (hweight : 0 < weight)
    (reserve temperature : ℝ) {clock : ℝ} (hclock : 0 < clock)
    (sensitivity : NNReal) {threshold v : ℝ} (hv : v ≤ threshold) :
    postedRamp weight sensitivity threshold v
      < plCurve weight reserve temperature clock v := by
  rw [postedRamp_zero_of_value_le_threshold weight sensitivity hv]
  exact plCurve_pos weight hweight reserve temperature hclock v

/-- **Strictly inside the frontier.**  For an atomless law that puts positive
mass strictly below the calibrated ramp threshold, the PL curve is feasible but
its value is strictly below the ramp's.

The mass hypothesis `hBelow` is what "atomless `F` plus a nondegenerate ramp"
delivers: a ramp calibrated to `w₁ γ < w₁` has its threshold in the interior of
the support, so positive mass sits below it. -/
theorem plCurve_welfare_lt_postedRamp (F : Measure ℝ) [IsProbabilityMeasure F] [NoAtoms F]
    (weight : NNReal) (hweight : 0 < weight) (reserve : ℝ)
    {temperature clock γ threshold : ℝ}
    (hτ : 0 < temperature) (hclock : 0 < clock)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hCalib : plMass F reserve temperature clock = γ)
    (hThreshold : 0 ≤ threshold)
    (hRampMass :
      curveMass F (postedRamp weight (plSensitivity weight temperature) threshold)
        = min ((weight : ℝ) * γ) (weight : ℝ))
    (hBelow : F (Set.Iio threshold) ≠ 0) :
    curveWelfare F (plCurve weight reserve temperature clock)
      < curveWelfare F
          (postedRamp weight (plSensitivity weight temperature) threshold) := by
  have hS : 0 < plSensitivity weight temperature := plSensitivity_pos weight hweight hτ
  have hfeas := plCurve_curveFeasible F weight reserve hτ hclock.le hCalib
  have hle := postedRamp_solves_population_program F weight
    (plSensitivity weight temperature) hS ((weight : ℝ) * γ) threshold hFirstMoment
    hThreshold hRampMass hfeas
  refine lt_of_le_of_ne hle ?_
  intro hEq
  have hae := postedRamp_ae_eq_of_welfare_eq F weight (plSensitivity weight temperature)
    hS ((weight : ℝ) * γ) threshold hFirstMoment hThreshold hRampMass hfeas hEq
  have hnull : F {v | ¬ plCurve weight reserve temperature clock v
      = postedRamp weight (plSensitivity weight temperature) threshold v} = 0 :=
    ae_iff.mp hae
  refine hBelow (measure_mono_null ?_ hnull)
  intro v hv
  have hlt := postedRamp_lt_plCurve_of_le_threshold weight hweight reserve temperature
    hclock (plSensitivity weight temperature) (le_of_lt hv)
  exact fun hcontra => absurd hcontra (ne_of_gt hlt)

/-- The same statement against the program value itself: the PL curve is
feasible, so its value is at most the program value, and by the previous
theorem it is strictly less. -/
theorem plCurve_welfare_lt_populationValue (F : Measure ℝ) [IsProbabilityMeasure F]
    [NoAtoms F] (weight : NNReal) (hweight : 0 < weight) (reserve : ℝ)
    {temperature clock γ threshold : ℝ}
    (hτ : 0 < temperature) (hclock : 0 < clock)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hCalib : plMass F reserve temperature clock = γ)
    (hThreshold : 0 ≤ threshold)
    (hRampMass :
      curveMass F (postedRamp weight (plSensitivity weight temperature) threshold)
        = min ((weight : ℝ) * γ) (weight : ℝ))
    (hBelow : F (Set.Iio threshold) ≠ 0) :
    curveWelfare F (plCurve weight reserve temperature clock)
      < populationValue F weight (plSensitivity weight temperature)
          ((weight : ℝ) * γ) := by
  have hstrict := plCurve_welfare_lt_postedRamp F weight hweight reserve hτ hclock
    hFirstMoment hCalib hThreshold hRampMass hBelow
  have hrampFeasible :
      CurveFeasible F weight (plSensitivity weight temperature) ((weight : ℝ) * γ)
        (postedRamp weight (plSensitivity weight temperature) threshold) :=
    { toCurveShape :=
        postedRamp_curveShape weight (plSensitivity weight temperature) threshold
      mass_le := by
        rw [hRampMass]
        exact min_le_left _ _ }
  have hmem := le_csSup
    (populationValues_bddAbove F hFirstMoment weight (plSensitivity weight temperature)
      ((weight : ℝ) * γ))
    (Set.mem_setOf.mpr ⟨postedRamp weight (plSensitivity weight temperature) threshold,
      hrampFeasible, rfl⟩)
  exact lt_of_lt_of_le hstrict hmem

/-! ### The hypotheses are jointly satisfiable

Witnesses for the first two clauses.  The third clause additionally needs a
calibrated ramp threshold with positive mass below it, whose witness requires
evaluating a ramp integral under an atomless law; that computation is not
carried out here. -/

/-- The clock clause is not vacuous. -/
example : ∃! clock : ℝ, 0 < clock ∧ plMass (Measure.dirac (0 : ℝ)) 0 1 clock = 1 / 2 :=
  existsUnique_plClock (Measure.dirac (0 : ℝ)) 0 1 (by norm_num) (by norm_num)

/-- The feasibility clause is not vacuous. -/
example (clock : ℝ) (hclock : 0 ≤ clock) :
    CurveFeasible (Measure.dirac (0 : ℝ)) 1 (plSensitivity 1 1)
      (((1 : NNReal) : ℝ) * plMass (Measure.dirac (0 : ℝ)) 0 1 clock)
      (plCurve 1 0 1 clock) :=
  plCurve_curveFeasible (Measure.dirac (0 : ℝ)) 1 0 (by norm_num) hclock rfl

end SmoothingCliff.Frontier
