/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexBddDerivApprox
public import Econlib.Math.MeasureTheory.ConvexIntegralRepr
public import Econlib.Probability.ContDist.ProbDist
public import Econlib.Probability.Distributions.Beta.SingleCrossing
public import Econlib.Probability.Order.Convex.Basic
public import Econlib.Probability.Order.SOSD.Equivalence

/-!
# Convex order for `betaWithMean` via SOSD and equal means

For distributions on `[0, 1]` with equal means, second-order stochastic dominance (SOSD) implies
the **convex order** `E[φ(X)] ≤ E[φ(Y)]` for every `φ` convex and continuous on `[0, 1]`.
Specializing to the `betaWithMean pi κ` family gives `betaWithMean_convexOrder`: A lower
concentration parameter `κ` yields a higher expectation of every continuous convex function, so the
fixed-mean Beta family increases in convex order as concentration falls. The comparison holds for
the full continuous-convex test class, with no derivative bound and no integrability hypotheses.

## Main definitions

* `callPayoff` — the call payoff function `callPayoff s t = max(t - s, 0)`.

## Main statements

* `callPayoff_eq_sub_negPut` — call payoff decomposes as `(t - s) - negPut s t`.
* `expect_callPayoff_le_of_sosd_of_mean_eq` — under SOSD and equal means, call payoffs are ordered:
  `E_F[callPayoff s] ≤ E_G[callPayoff s]`.
* `ContDist.expect_callPayoff_integrableOn` — the map `s ↦ E_d[callPayoff s]` is integrable on
  `(0, 1]` with respect to any locally finite measure.
* `ContDist.expect_setIntegral_callPayoff_comm` — Fubini exchange for the call payoff integral.
* `expect_le_of_sosd_of_mean_eq_of_convexOn` — SOSD and equal means imply the convex-order
  inequality for convex test functions with bounded right-derivative image.
* `expect_le_of_sosd_of_mean_eq_of_convexOn_cont` — the same for the full continuous-convex test
  class, with no derivative bound and no integrability hypotheses.
* `betaWithMean_convexOrder` — lower-concentration Beta distributions dominate in convex order, for
  every continuous convex test function.
* `betaWithMean_convexOrderOnIcc` — the `ConvexOrderOnIcc` packaging of the above.

## References

* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

beta distribution, convex order, second-order stochastic dominance, rothschild-stiglitz
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

open Monotone

variable {pi : ℝ} (hpi_pos : 0 < pi) (hpi_lt : pi < 1)

/-- The call payoff function at strike `s`: `callPayoff s t = max(t - s, 0)`. -/
noncomputable def callPayoff (s : ℝ) : ℝ → ℝ := fun t => max (t - s) 0

/-- The call payoff decomposes as `callPayoff s t = (t - s) - negPut s t`. -/
lemma callPayoff_eq_sub_negPut (s t : ℝ) :
    callPayoff s t = (t - s) - negPut s t := by
  simp only [callPayoff, negPut]
  rcases le_or_gt t s with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), min_eq_right (sub_nonpos.mpr h)]; ring
  · rw [max_eq_left (le_of_lt (sub_pos.mpr h)), min_eq_left (le_of_lt (sub_pos.mpr h))]; ring

/-- Under SOSD and equal means, call payoffs are ordered: `E_F[callPayoff s] ≤ E_G[callPayoff s]`
for every strike `s`. -/
lemma expect_callPayoff_le_of_sosd_of_mean_eq (dF dG : ContDist) (s : ℝ)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_mean : dF.expect id = dG.expect id)
    (h_intF_x : Integrable (fun x => dF.density x * x))
    (h_intG_x : Integrable (fun x => dG.density x * x))
    (h_intF_abs : Integrable (fun x => dF.density x * |x|))
    (h_intG_abs : Integrable (fun x => dG.density x * |x|)) :
    dF.expect (callPayoff s) ≤ dG.expect (callPayoff s) := by
  -- Shared helpers for both distributions: decompose call via negPut, then extract the linear part.
  have expect_call_eq : ∀ d : ContDist, Integrable (fun x => d.density x * x) →
      d.expect (callPayoff s) = d.expect (fun t => t - s) - d.expect (negPut s) := by
    intro d h_int_x
    unfold ContDist.expect
    have h_call_eq : (fun x => d.density x * callPayoff s x) =
        (fun x => d.density x * (x - s) - d.density x * negPut s x) :=
      funext fun x => by rw [callPayoff_eq_sub_negPut]; ring
    rw [h_call_eq]
    have h_lin_int : Integrable (fun x => d.density x * (x - s)) := by
      have heq : (fun x => d.density x * (x - s)) =
          (fun x => d.density x * x - d.density x * s) := funext fun x => by ring
      rw [heq]; exact h_int_x.sub (d.integrable.mul_const s)
    rw [integral_sub h_lin_int (integrable_negPut d s h_int_x)]
  have expect_lin : ∀ d : ContDist, Integrable (fun x => d.density x * x) →
      d.expect (fun t => t - s) = d.expect id - s := by
    intro d h_int_x
    have h_id : d.expect id = ∫ x, d.density x * x := by
      change ∫ x, d.density x * id x = ∫ x, d.density x * x
      simp only [id]
    have h_const_s : ∫ a, d.density a * s = s := by
      rw [integral_mul_const, d.integral_one, one_mul]
    change ∫ x, d.density x * (x - s) = d.expect id - s
    have heq : (fun x => d.density x * (x - s)) =
        (fun x => d.density x * x - d.density x * s) :=
      funext fun x => by ring
    rw [heq, integral_sub h_int_x (d.integrable.mul_const s), h_const_s, h_id]
  have hF_eq := expect_call_eq dF h_intF_x
  have hG_eq := expect_call_eq dG h_intG_x
  have hF_lin := expect_lin dF h_intF_x
  have hG_lin := expect_lin dG h_intG_x
  have h_negPut : dG.expect (negPut s) ≤ dF.expect (negPut s) := by
    exact CDF.SOSD.expect_concave_mono dF dG (negPut s) h_sosd
      (negPut_concave s) (negPut_monotone s)
      ⟨1 + |s|, by positivity, fun t => by
        simp only [negPut]
        rcases le_or_gt t s with h | h
        · rw [min_eq_right (sub_nonpos.mpr h)]
          have hts : |t - s| = s - t := by rw [abs_of_nonpos (sub_nonpos.mpr h)]; ring
          rw [hts]
          -- s - t ≤ (1 + |s|)(1 + |t|)
          -- Expand: (1+|s|)(1+|t|) = 1 + |s| + |t| + |s||t| ≥ s - t
          -- since s ≤ |s|, -t ≤ |t|, and 1 + |s||t| ≥ 0
          have hs : s ≤ |s| := le_abs_self s
          have ht : -t ≤ |t| := neg_le_abs t
          nlinarith [abs_nonneg s, abs_nonneg t, mul_nonneg (abs_nonneg s) (abs_nonneg t)]
        · rw [min_eq_left (le_of_lt (sub_pos.mpr h)), abs_zero]; positivity⟩
      (integrable_negPut dF s h_intF_x)
      (integrable_negPut dG s h_intG_x)
      h_intF_abs h_intG_abs
  rw [hF_eq, hG_eq, hF_lin, hG_lin, h_mean]
  linarith

/-- The map `s ↦ E_d[callPayoff s]` is integrable on `(0, 1]` with respect to any locally finite
measure `μ`, provided `x ↦ d.density x * |x|` is integrable. -/
lemma ContDist.expect_callPayoff_integrableOn (d : ContDist) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ]
    (h_int_abs : Integrable (fun x => d.density x * |x|)) :
    IntegrableOn (fun s => d.expect (callPayoff s)) (Set.Ioc 0 1) μ := by
  have hμ_fin : μ (Set.Ioc 0 1) ≠ ⊤ := (measure_Ioc_lt_top (μ := μ)).ne
  -- Uniform bound on ‖d.expect (callPayoff s)‖ for s ∈ (0, 1]
  set M := (∫ x, d.density x * |x|) + 1
  -- callPayoff s t ≤ |t| + 1 for s ∈ [0, 1]
  have h_call_le : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ t : ℝ,
      d.density t * callPayoff s t ≤ d.density t * (|t| + 1) := by
    intro s hs t
    apply mul_le_mul_of_nonneg_left _ (d.nonneg t)
    simp only [callPayoff]
    calc max (t - s) 0 ≤ max (|t| + |s|) 0 := by
          apply max_le_max_right
          linarith [le_abs_self t, neg_le_abs s]
      _ = |t| + |s| := max_eq_left (by positivity)
      _ ≤ |t| + 1 := by
          have : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
          linarith
  have hint_dom : Integrable (fun x => d.density x * (|x| + 1)) := by
    have : (fun x => d.density x * (|x| + 1)) = (fun x => d.density x * |x| + d.density x) := by
      ext x; ring
    rw [this]; exact h_int_abs.add d.integrable
  have hint_call : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      Integrable (fun x => d.density x * callPayoff s x) := by
    intro s hs
    apply hint_dom.mono
    · exact d.integrable.aestronglyMeasurable.mul
        ((measurable_sub_const s).max measurable_const).aestronglyMeasurable
    · apply ae_of_all; intro x
      simp only [callPayoff, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (d.nonneg x) (le_max_right _ _)),
          abs_of_nonneg (mul_nonneg (d.nonneg x) (by positivity))]
      exact h_call_le s hs x
  have h_expect_le : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖d.expect (callPayoff s)‖ ≤ M := by
    intro s hs
    have h_nonneg : 0 ≤ d.expect (callPayoff s) := by
      apply integral_nonneg
      intro x; apply mul_nonneg (d.nonneg x)
      simp only [callPayoff]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    change d.expect (callPayoff s) ≤ M
    calc d.expect (callPayoff s)
        = ∫ x, d.density x * callPayoff s x := rfl
      _ ≤ ∫ x, d.density x * (|x| + 1) :=
          integral_mono (hint_call s hs) hint_dom (fun x => h_call_le s hs x)
      _ = M := by
          change ∫ x, d.density x * (|x| + 1) = (∫ x, d.density x * |x|) + 1
          have hrw :
              (fun x => d.density x * (|x| + 1)) =
                (fun x => d.density x * |x| + d.density x) :=
            funext fun x => by ring
          rw [hrw, integral_add h_int_abs d.integrable, d.integral_one]
  have hint_call_all : ∀ s : ℝ,
      Integrable (fun x => d.density x * callPayoff s x) := by
    intro s
    have hint_s : Integrable (fun x => d.density x * (|x| + |s|)) := by
      have :
          (fun x => d.density x * (|x| + |s|)) =
            (fun x => d.density x * |x| + d.density x * |s|) :=
        funext fun x => by ring
      rw [this]
      exact h_int_abs.add
        (d.integrable.const_mul |s| |>.congr (ae_of_all _ fun x => by ring))
    apply hint_s.mono
    · exact d.integrable.aestronglyMeasurable.mul
        ((measurable_sub_const s).max measurable_const).aestronglyMeasurable
    · apply ae_of_all; intro x
      simp only [callPayoff, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (d.nonneg x) (le_max_right _ _)),
          abs_of_nonneg (mul_nonneg (d.nonneg x) (by positivity))]
      apply mul_le_mul_of_nonneg_left _ (d.nonneg x)
      exact max_le (by linarith [le_abs_self x, neg_le_abs s]) (by positivity)
  have h_anti : Antitone (fun s => d.expect (callPayoff s)) := by
    intro s₁ s₂ h12
    change d.expect (callPayoff s₂) ≤ d.expect (callPayoff s₁)
    apply integral_mono (hint_call_all s₂) (hint_call_all s₁)
    intro x
    apply mul_le_mul_of_nonneg_left _ (d.nonneg x)
    simp only [callPayoff]
    exact max_le_max_right 0 (sub_le_sub_left h12 x)
  have h_meas : AEStronglyMeasurable (fun s => d.expect (callPayoff s)) μ :=
    h_anti.measurable.aestronglyMeasurable
  exact Measure.integrableOn_of_bounded hμ_fin h_meas
    (by rw [ae_restrict_iff' measurableSet_Ioc]
        exact ae_of_all _ fun s hs => h_expect_le s hs)

/-- Fubini exchange for call payoffs: `E_d[∫ max(·-s, 0) dμ(s)] = ∫ E_d[callPayoff s] dμ(s)`, where
integration in `s` is over `(0, 1]`. -/
lemma ContDist.expect_setIntegral_callPayoff_comm (d : ContDist) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ]
    (h_int_h : Integrable (fun x => d.density x * ∫ s in Set.Ioc 0 1, max (x - s) 0 ∂μ))
    -- Kept for API symmetry with `expect_callPayoff_integrableOn`; not needed in this proof body.
    (_h_int_abs : Integrable (fun x => d.density x * |x|)) :
    d.expect (fun t => ∫ s in Set.Ioc 0 1, max (t - s) 0 ∂μ) =
    ∫ s in Set.Ioc 0 1, d.expect (callPayoff s) ∂μ := by
  set ν := μ.restrict (Set.Ioc 0 1) with hν_def
  haveI : IsFiniteMeasure ν :=
    ⟨by
      simpa [ν] using (measure_Ioc_lt_top (μ := μ) (a := (0 : ℝ)) (b := 1))⟩
  have h_pull : ∀ x, d.density x * ∫ s, max (x - s) 0 ∂ν =
      ∫ s, d.density x * max (x - s) 0 ∂ν := by
    intro x; rw [← MeasureTheory.integral_const_mul]
  have h_meas_joint : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun x s => d.density x * max (x - s) 0))
      (MeasureTheory.volume.prod ν) := by
    apply AEStronglyMeasurable.mul
    · exact (d.integrable.aestronglyMeasurable.comp_fst)
    · exact ((measurable_fst.sub measurable_snd).max measurable_const).aestronglyMeasurable
  -- Joint integrability via Tonelli: each fiber is bounded on the finite measure ν,
  -- and the x-integral of fiber norms is dominated by h_int_h.
  have h_joint : MeasureTheory.Integrable
      (Function.uncurry (fun x s => d.density x * max (x - s) 0))
      (MeasureTheory.volume.prod ν) := by
    rw [MeasureTheory.integrable_prod_iff h_meas_joint]
    refine ⟨ae_of_all _ fun x => ?_, ?_⟩
    · change Integrable (fun s => d.density x * max (x - s) 0) ν
      have h_max_intOn : IntegrableOn (fun s => max (x - s) 0) (Set.Ioc 0 1) μ :=
        Measure.integrableOn_of_bounded (M := |x| + 1) (measure_Ioc_lt_top.ne)
          ((measurable_const.sub measurable_id).max measurable_const).aestronglyMeasurable
          ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            exact max_le (by linarith [le_abs_self x, hs.1]) (by positivity)))
      simpa [ν] using h_max_intOn.const_mul (d.density x) |>.congr (ae_of_all _ fun s => by ring)
    · change Integrable (fun x => ∫ s, ‖d.density x * max (x - s) 0‖ ∂ν) volume
      refine h_int_h.congr (ae_of_all _ fun x => ?_)
      change d.density x * ∫ s, max (x - s) 0 ∂ν = ∫ s, ‖d.density x * max (x - s) 0‖ ∂ν
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (d.nonneg x) (le_max_right _ _))]
      exact (MeasureTheory.integral_const_mul _ _).symm
  change (∫ x, d.density x * ∫ s, max (x - s) 0 ∂ν) =
    ∫ s, (∫ x, d.density x * callPayoff s x) ∂ν
  rw [show (∫ x, d.density x * ∫ s, max (x - s) 0 ∂ν) =
    ∫ x, ∫ s, d.density x * max (x - s) 0 ∂ν from
    integral_congr_ae (ae_of_all _ h_pull)]
  exact MeasureTheory.integral_integral_swap h_joint

/-- **Bounded-derivative case.** For continuous distributions on `[0, 1]` with equal means, SOSD
implies the convex-order inequality for convex test functions whose right-derivative image on
`(0, 1)` is bounded: If `dF` SOSD-dominates `dG` and `E_F[id] = E_G[id]`, then `E_F[φ] ≤ E_G[φ]`.
The full continuous-convex test class, with no derivative bound and no integrability hypotheses, is
`expect_le_of_sosd_of_mean_eq_of_convexOn_cont`. -/
lemma expect_le_of_sosd_of_mean_eq_of_convexOn (dF dG : ContDist)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_mean : dF.expect id = dG.expect id)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (hbb : BddBelow ((fun x => derivWithin φ (Set.Ioi x) x) '' Set.Ioo 0 1))
    (hba : BddAbove ((fun x => derivWithin φ (Set.Ioi x) x) '' Set.Ioo 0 1))
    (hint_F : Integrable (fun x => dF.density x * φ x))
    (hint_G : Integrable (fun x => dG.density x * φ x))
    -- Finite first moments needed for the call-payoff decomposition
    (h_intF_x : Integrable (fun x => dF.density x * x))
    (h_intG_x : Integrable (fun x => dG.density x * x))
    (h_intF_abs : Integrable (fun x => dF.density x * |x|))
    (h_intG_abs : Integrable (fun x => dG.density x * |x|))
    -- Support on [0, 1]: density vanishes outside [0, 1]
    (h_supp_F : ∀ x, x ∉ Set.Icc 0 1 → dF.density x = 0)
    (h_supp_G : ∀ x, x ∉ Set.Icc 0 1 → dG.density x = 0) :
    dF.expect φ ≤ dG.expect φ := by
  set μ := MeasureTheory.convexSecondDerivMeasure hφ (by norm_num : (0 : ℝ) < 1) hbb hba
  -- μ is a Stieltjes measure, hence locally finite
  haveI : IsLocallyFiniteMeasure μ := by
    simp only [μ, MeasureTheory.convexSecondDerivMeasure, stieltjesMeasure]
    infer_instance
  set c := sInf ((fun x => derivWithin φ (Set.Ioi x) x) '' Set.Ioo 0 1)
  -- h(t) = ∫ s in (0,1], max(t-s, 0) dμ(s) is the nonlinear part of the integral representation
  set h : ℝ → ℝ := fun t => ∫ s in Set.Ioc 0 1, max (t - s) 0 ∂μ with hh_def
  -- Integral representation: φ(t) = φ(0) + c·t + h(t) on [0,1]
  have repr : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t = φ 0 + c * t + h t := by
    intro t ht
    have :=
      MeasureTheory.convex_integral_repr_max hφ (by norm_num : (0 : ℝ) < 1) hφ_cont
        hbb hba ht.1 ht.2
    simp only [sub_zero] at this
    exact this
  -- Decomposition E_d[φ] = φ(0) + c·E_d[id] + E_d[h]: pointwise
  -- density(x)*φ(x) = density(x)*(φ(0)+c·x+h(x)) since density vanishes outside [0,1].
  have decomp : ∀ d : ContDist, Integrable (fun x => d.density x * φ x) →
      Integrable (fun x => d.density x * x) → (∀ x, x ∉ Set.Icc 0 1 → d.density x = 0) →
      Integrable (fun x => d.density x * h x) ∧
        d.expect φ = φ 0 + c * d.expect id + d.expect h := by
    intro d hint_d h_int_x h_supp
    have h_pw : ∀ x, d.density x * φ x =
        d.density x * φ 0 + d.density x * (c * x) + d.density x * h x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · rw [repr x hx]; ring
      · rw [h_supp x hx]; ring
    have hint_const : Integrable (fun x => d.density x * φ 0) :=
      (d.integrable.const_mul (φ 0)).congr (ae_of_all _ fun x => by ring)
    have hint_cx : Integrable (fun x => d.density x * (c * x)) :=
      (h_int_x.const_mul c).congr (ae_of_all _ fun x => by ring)
    have hint_h : Integrable (fun x => d.density x * h x) := by
      have hint_sum : Integrable
          (fun x => d.density x * φ 0 + d.density x * (c * x) + d.density x * h x) :=
        hint_d.congr (ae_of_all _ h_pw)
      exact (hint_sum.sub (hint_const.add hint_cx)).congr
        (ae_of_all _ fun x => by simp [Pi.sub_apply])
    refine ⟨hint_h, ?_⟩
    change ∫ x, d.density x * φ x =
      φ 0 + c * (∫ x, d.density x * x) + ∫ x, d.density x * h x
    have I1 : ∫ x, d.density x * φ 0 = φ 0 := by
      rw [show (fun x => d.density x * φ 0) = (fun x => φ 0 * d.density x)
        from funext fun x => by ring, integral_const_mul, d.integral_one, mul_one]
    have I2 : ∫ x, d.density x * (c * x) = c * ∫ x, d.density x * x := by
      rw [show (fun x => d.density x * (c * x)) = (fun x => c * (d.density x * x))
        from funext fun x => by ring, integral_const_mul]
    have key1 : ∫ x, (d.density x * φ 0 + d.density x * (c * x) + d.density x * h x) =
        (∫ x, (d.density x * φ 0 + d.density x * (c * x))) + ∫ x, d.density x * h x :=
      integral_add (hint_const.add hint_cx) hint_h
    have key2 : ∫ x, (d.density x * φ 0 + d.density x * (c * x)) =
        (∫ x, d.density x * φ 0) + ∫ x, d.density x * (c * x) :=
      integral_add hint_const hint_cx
    have hrw : ∫ x, d.density x * φ x =
        ∫ x, (d.density x * φ 0 + d.density x * (c * x) + d.density x * h x) :=
      integral_congr_ae (ae_of_all _ h_pw)
    linarith
  obtain ⟨hint_Fh, decomp_F⟩ := decomp dF hint_F h_intF_x h_supp_F
  obtain ⟨hint_Gh, decomp_G⟩ := decomp dG hint_G h_intG_x h_supp_G
  -- Fubini: E_d[h] = ∫ E_d[callPayoff s] dμ(s)
  have fubini_F : dF.expect h =
      ∫ s in Set.Ioc 0 1, dF.expect (callPayoff s) ∂μ :=
    dF.expect_setIntegral_callPayoff_comm μ hint_Fh h_intF_abs
  have fubini_G : dG.expect h =
      ∫ s in Set.Ioc 0 1, dG.expect (callPayoff s) ∂μ :=
    dG.expect_setIntegral_callPayoff_comm μ hint_Gh h_intG_abs
  have call_le : ∀ s : ℝ, dF.expect (callPayoff s) ≤ dG.expect (callPayoff s) := fun s =>
    expect_callPayoff_le_of_sosd_of_mean_eq dF dG s h_sosd h_mean h_intF_x h_intG_x h_intF_abs
      h_intG_abs
  have hint_call_F : IntegrableOn (fun s => dF.expect (callPayoff s))
      (Set.Ioc 0 1) μ :=
    dF.expect_callPayoff_integrableOn μ h_intF_abs
  have hint_call_G : IntegrableOn (fun s => dG.expect (callPayoff s))
      (Set.Ioc 0 1) μ :=
    dG.expect_callPayoff_integrableOn μ h_intG_abs
  have integral_le : ∫ s in Set.Ioc 0 1, dF.expect (callPayoff s) ∂μ ≤
                     ∫ s in Set.Ioc 0 1, dG.expect (callPayoff s) ∂μ :=
    setIntegral_mono hint_call_F hint_call_G (fun s => call_le s)
  -- Affine parts cancel by equal means; nonlinear parts are ordered by call_le.
  rw [decomp_F, decomp_G, fubini_F, fubini_G, h_mean]
  linarith

/-- For a `ContDist` whose density vanishes outside `[0, 1]`, the product of the density with any
function continuous on `[0, 1]` is integrable: The integrand is supported on `[0, 1]`, where the
continuous factor is bounded, so it is dominated by a scalar multiple of the density. -/
lemma ContDist.integrable_density_mul_of_supportsOn_Icc (d : ContDist) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc 0 1))
    (h_supp : ∀ x, x ∉ Set.Icc 0 1 → d.density x = 0) :
    Integrable (fun x => d.density x * g x) := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  -- Replace g with its [0,1]-indicator; density vanishes off [0,1] so the integrand is unchanged.
  have hgi : (fun x => d.density x * g x) =
      (fun x => d.density x * (Set.Icc 0 1).indicator g x) := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
    · rw [h_supp x hx, zero_mul, zero_mul]
  rw [hgi]
  have hmeas_ind : AEStronglyMeasurable ((Set.Icc 0 1).indicator g) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
      (hg.aestronglyMeasurable measurableSet_Icc)
  have hind_bound : ∀ x, ‖(Set.Icc 0 1).indicator g x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx]; exact hC x hx
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact hC0
  refine (d.integrable.const_mul C).mono'
    (d.integrable.aestronglyMeasurable.mul hmeas_ind) (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (d.nonneg x)]
  calc d.density x * ‖(Set.Icc 0 1).indicator g x‖
      ≤ d.density x * C := mul_le_mul_of_nonneg_left (hind_bound x) (d.nonneg x)
    _ = C * d.density x := mul_comm _ _

/-- For continuous distributions on `[0, 1]` with equal means, SOSD implies the convex order for
the **full continuous-convex test class**: If `dF` SOSD-dominates `dG` and `E_F[id] = E_G[id]`,
then `E_F[φ] ≤ E_G[φ]` for every `φ` convex and continuous on `[0, 1]`. Unlike
`expect_le_of_sosd_of_mean_eq_of_convexOn`, this requires neither a bounded right-derivative image
nor integrability hypotheses, since a convex function continuous on the compact `[0, 1]` is
bounded. -/
lemma expect_le_of_sosd_of_mean_eq_of_convexOn_cont (dF dG : ContDist)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_mean : dF.expect id = dG.expect id)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (h_supp_F : ∀ x, x ∉ Set.Icc 0 1 → dF.density x = 0)
    (h_supp_G : ∀ x, x ∉ Set.Icc 0 1 → dG.density x = 0) :
    dF.expect φ ≤ dG.expect φ := by
  obtain ⟨φn, M, hconv, hcont, hbb, hba, hbd, htend⟩ :=
    ConvexOn.exists_seq_bddRightDeriv_tendsto hφ (by norm_num : (0 : ℝ) < 1) hφ_cont
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbd 0 0 ⟨le_refl 0, zero_le_one⟩)
  have key : ∀ n, dF.expect (φn n) ≤ dG.expect (φn n) := fun n =>
    expect_le_of_sosd_of_mean_eq_of_convexOn dF dG h_sosd h_mean (φn n) (hconv n) (hcont n)
      (hbb n) (hba n)
      (dF.integrable_density_mul_of_supportsOn_Icc (hcont n) h_supp_F)
      (dG.integrable_density_mul_of_supportsOn_Icc (hcont n) h_supp_G)
      (dF.integrable_density_mul_of_supportsOn_Icc continuous_id.continuousOn h_supp_F)
      (dG.integrable_density_mul_of_supportsOn_Icc continuous_id.continuousOn h_supp_G)
      (dF.integrable_density_mul_of_supportsOn_Icc continuous_abs.continuousOn h_supp_F)
      (dG.integrable_density_mul_of_supportsOn_Icc continuous_abs.continuousOn h_supp_G)
      h_supp_F h_supp_G
  -- |density x * φn n x| ≤ M * density x since |φn n x| ≤ M on [0,1] and density vanishes off it.
  have tend : ∀ d : ContDist, (∀ x, x ∉ Set.Icc 0 1 → d.density x = 0) →
      Filter.Tendsto (fun n => d.expect (φn n)) Filter.atTop (nhds (d.expect φ)) := by
    intro d h_supp
    change Filter.Tendsto (fun n => ∫ x, d.density x * φn n x) Filter.atTop
      (nhds (∫ x, d.density x * φ x))
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => M * d.density x)
      (fun n => (d.integrable_density_mul_of_supportsOn_Icc (hcont n) h_supp).aestronglyMeasurable)
      (d.integrable.const_mul M) (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [norm_mul, Real.norm_of_nonneg (d.nonneg x)]
      by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · calc d.density x * ‖φn n x‖
            ≤ d.density x * M := mul_le_mul_of_nonneg_left
              (by rw [Real.norm_eq_abs]; exact hbd n x hx) (d.nonneg x)
          _ = M * d.density x := mul_comm _ _
      · simp [h_supp x hx]
    · by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
      · exact (htend x hx).const_mul (d.density x)
      · simp [h_supp x hx]
  exact le_of_tendsto_of_tendsto' (tend dF h_supp_F) (tend dG h_supp_G) key

/-- A `ContDist` whose density vanishes outside `[a, b]` is supported on `[a, b]` (as a
`ProbDist`): The associated measure puts zero mass on the complement. -/
lemma ContDist.toProbDist_supportsOn_Icc (d : ContDist) {a b : ℝ}
    (h_supp : ∀ x, x ∉ Set.Icc a b → d.density x = 0) :
    d.toProbDist.supportsOn (Set.Icc a b) := by
  refine ProbDist.supportsOn_of_ae_mem measurableSet_Icc ?_
  rw [MeasureTheory.ae_iff]
  have hset : {x | ¬ x ∈ Set.Icc a b} = (Set.Icc a b)ᶜ := rfl
  rw [hset, ContDist.toProbDist_toMeasure, ContDist.toMeasure,
    MeasureTheory.withDensity_apply _ measurableSet_Icc.compl]
  refine MeasureTheory.setLIntegral_eq_zero measurableSet_Icc.compl ?_
  intro x hx
  change ENNReal.ofReal (d.density x) = 0
  rw [h_supp x hx, ENNReal.ofReal_zero]

/-- **Beta convex order:** For `κ₁ < κ₂` and every `φ` convex and continuous on `[0, 1]`,
`E[φ(X₂)] ≤ E[φ(X₁)]` where `Xᵢ ~ betaWithMean pi κᵢ`.

In other words, a lower concentration parameter yields a more spread distribution in the convex
order: `betaWithMean pi κ₁` convex-order dominates `betaWithMean pi κ₂`. This holds for the **full
continuous-convex test class** — no bounded right-derivative image and no integrability hypotheses
are needed. -/
theorem betaWithMean_convexOrder {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc 0 1) φ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1)) :
    (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).expect φ ≤
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).expect φ := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  have h_sosd : CDF.SOSD d₂.cdf d₁.cdf := betaWithMean_sosd hpi_pos hpi_lt hk1 hk2 hlt
  have h_mean : d₂.expect id = d₁.expect id := by
    rw [betaWithMean_expect hpi_pos hpi_lt hk2, betaWithMean_expect hpi_pos hpi_lt hk1]
  have h_supp₂ : ∀ x, x ∉ Set.Icc 0 1 → d₂.density x = 0 := fun x hx =>
    ContDist.beta_density_eq_zero_of_not_mem (κ₂ * pi) (κ₂ * (1 - pi))
      (mul_pos hk2 hpi_pos) (mul_pos hk2 (by linarith)) hx
  have h_supp₁ : ∀ x, x ∉ Set.Icc 0 1 → d₁.density x = 0 := fun x hx =>
    ContDist.beta_density_eq_zero_of_not_mem (κ₁ * pi) (κ₁ * (1 - pi))
      (mul_pos hk1 hpi_pos) (mul_pos hk1 (by linarith)) hx
  exact expect_le_of_sosd_of_mean_eq_of_convexOn_cont d₂ d₁ h_sosd h_mean φ hφ hφ_cont
    h_supp₂ h_supp₁

/-- **Beta convex order, canonical form.** For `κ₁ < κ₂`, `betaWithMean pi κ₂` lies below
`betaWithMean pi κ₁` in the library's convex order on `[0, 1]` (`ConvexOrderOnIcc`). This packages
`betaWithMean_convexOrder` for direct use by the general convex-order API (Strassen, duality). -/
theorem betaWithMean_convexOrderOnIcc {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂) :
    ConvexOrderOnIcc 0 1 (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).toProbDist
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).toProbDist := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  have h_supp₂ : ∀ x, x ∉ Set.Icc 0 1 → d₂.density x = 0 := fun x hx =>
    ContDist.beta_density_eq_zero_of_not_mem (κ₂ * pi) (κ₂ * (1 - pi))
      (mul_pos hk2 hpi_pos) (mul_pos hk2 (by linarith)) hx
  have h_supp₁ : ∀ x, x ∉ Set.Icc 0 1 → d₁.density x = 0 := fun x hx =>
    ContDist.beta_density_eq_zero_of_not_mem (κ₁ * pi) (κ₁ * (1 - pi))
      (mul_pos hk1 hpi_pos) (mul_pos hk1 (by linarith)) hx
  refine ⟨d₂.toProbDist_supportsOn_Icc h_supp₂, d₁.toProbDist_supportsOn_Icc h_supp₁, ?_, ?_⟩
  · rw [← ContDist.expect_eq_probDist_expect, ← ContDist.expect_eq_probDist_expect,
      betaWithMean_expect hpi_pos hpi_lt hk2, betaWithMean_expect hpi_pos hpi_lt hk1]
  · intro φ hφ hφ_cont
    rw [← ContDist.expect_eq_probDist_expect, ← ContDist.expect_eq_probDist_expect]
    exact betaWithMean_convexOrder hpi_pos hpi_lt hk1 hk2 hlt φ hφ hφ_cont

end Econlib.Probability

end -- noncomputable section
