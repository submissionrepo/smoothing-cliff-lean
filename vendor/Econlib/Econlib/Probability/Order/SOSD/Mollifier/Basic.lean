/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Convolution.Preservation
public import Econlib.Probability.Order.Core.IntegratedCDF
public import Econlib.Probability.Order.SOSD.DoubleIBP
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convolution

/-!
# SOSD expectation ordering for smooth concave test functions

The smooth-step reduction for second-order stochastic dominance. For a `C²` monotone concave test
function `v` with linear growth, second-order stochastic dominance of `dF` over `dG` forces the
expectation ordering `E_G[v] ≤ E_F[v]`. This is the regularized core of the mollifier bridge: The
general (merely continuous) case in `Mollifier/ExpectConcave.lean` mollifies the test function and
reduces to this lemma.

## Main definitions

This file introduces no new definitions.

## Main statements

* `sosd_smooth_step` — second-order stochastic dominance implies `E_G[v] ≤ E_F[v]` for `C²`
  monotone concave `v` of linear growth, assembling the boundary-decay and integrability conditions
  required by the double integration-by-parts identity.

## Notes

The boundary-decay tail lemmas `tail_Ioi_tendsto_zero_real` and `tail_Iic_tendsto_zero_real` are
stated for nonnegative integrable functions on `ℝ` and reused throughout the survival-weighted
estimates.

## Tags

second-order stochastic dominance, concave, expectation ordering, integration by parts
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology ENNReal Real Convolution

namespace Econlib.Probability

open Monotone

/-- Tail integral of a nonneg integrable function on `Ioi x` tends to 0 as `x → +∞` (ℝ-indexed). -/
lemma tail_Ioi_tendsto_zero_real (g : ℝ → ℝ) (hg : Integrable g) (hg_nn : ∀ x, 0 ≤ g x) :
    Tendsto (fun x : ℝ => ∫ t in Ioi x, g t) atTop (𝓝 0) := by
  have hanti : Antitone (fun x : ℝ => ∫ t in Ioi x, g t) := by
    intro x y hxy
    exact setIntegral_mono_set hg.integrableOn (ae_of_all _ hg_nn)
      (Eventually.of_forall (fun t (ht : y < t) => lt_of_le_of_lt hxy ht))
  have h_nat_iInter : ⋂ n : ℕ, Ioi (n : ℝ) = ∅ := by
    ext x; simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⌈x⌉₊ + 1, by push_cast; linarith [Nat.le_ceil x]⟩
  have h_nat : Tendsto (fun n : ℕ => ∫ t in Ioi (n : ℝ), g t) atTop (𝓝 0) := by
    have := Antitone.tendsto_setIntegral (fun n => measurableSet_Ioi)
      (fun n m (hnm : n ≤ m) => Ioi_subset_Ioi (Nat.cast_le.mpr hnm))
      hg.integrableOn
    rwa [h_nat_iInter, setIntegral_empty] at this
  exact squeeze_zero_norm' (h' := h_nat.comp tendsto_nat_floor_atTop)
    (eventually_of_mem (Ici_mem_atTop 0) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (setIntegral_nonneg measurableSet_Ioi (fun t _ => hg_nn t))]
      exact hanti (Nat.floor_le hx))

/-- Tail integral of a nonneg integrable function on `Iic x` tends to 0 as `x → -∞` (ℝ-indexed). -/
lemma tail_Iic_tendsto_zero_real (g : ℝ → ℝ) (hg : Integrable g) (hg_nn : ∀ x, 0 ≤ g x) :
    Tendsto (fun x : ℝ => ∫ t in Iic x, g t) atBot (𝓝 0) := by
  have hmono : Monotone (fun x : ℝ => ∫ t in Iic x, g t) := by
    intro x y hxy
    exact setIntegral_mono_set hg.integrableOn (ae_of_all _ hg_nn)
      (Iic_subset_Iic.mpr hxy).eventuallyLE
  have hnn : ∀ x, 0 ≤ ∫ t in Iic x, g t :=
    fun x => setIntegral_nonneg measurableSet_Iic (fun t _ => hg_nn t)
  have h_nat_iInter : ⋂ n : ℕ, Iic (-(n : ℝ)) = ∅ := by
    ext x; simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⌈-x⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (-x)]⟩
  have h_nat : Tendsto (fun n : ℕ => ∫ t in Iic (-(n : ℝ)), g t) atTop (𝓝 0) := by
    have := Antitone.tendsto_setIntegral (fun n => measurableSet_Iic)
      (fun n m (hnm : n ≤ m) => Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr hnm)))
      hg.integrableOn
    rwa [h_nat_iInter, setIntegral_empty] at this
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := ((NormedAddGroup.tendsto_nhds_zero.mp h_nat) ε hε).exists_forall_of_atTop
  filter_upwards [eventually_le_atBot (-(N : ℝ))] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
  calc ∫ t in Iic x, g t ≤ ∫ t in Iic (-(N : ℝ)), g t := hmono hx
    _ = ‖∫ t in Iic (-(N : ℝ)), g t‖ := (Real.norm_eq_abs _ ▸ (abs_of_nonneg (hnn _)).symm)
    _ < ε := hN N le_rfl

variable {dF dG : ContDist}

/-- Helper: `density * (1 + |t|)` is integrable given a finite first absolute moment. -/
private lemma density_mul_one_add_abs_integrable (d : ContDist)
    (h_absm : Integrable (fun t => d.density t * |t|)) :
    Integrable (fun t => d.density t * (1 + |t|)) := by
  have h1 : Integrable (fun t => d.density t * 1) := by simpa using d.integrable
  have heq : (fun t => d.density t * (1 + |t|)) =
      fun t => d.density t * 1 + d.density t * |t| := by ext t; ring
  rw [heq]; exact h1.add h_absm

/-- Helper: `density * t` is integrable given a finite first absolute moment. -/
private lemma density_mul_id_integrable (d : ContDist)
    (h_absm : Integrable (fun t => d.density t * |t|)) :
    Integrable (fun t => d.density t * t) :=
  Integrable.mono' h_absm
    (d.integrable.aestronglyMeasurable.mul measurable_id.aestronglyMeasurable)
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (d.nonneg t)])

/-- For `v` with linear growth `|v x| ≤ Cb(1+|x|)`, the survival-weighted value `(1-F(x))·v(x)`
tends to `0` as `x → +∞`, dominated by the tail of `density·(1+|t|)`. -/
private lemma one_sub_cdf_mul_tendsto_atTop_zero (d : ContDist)
    (v : ℝ → ℝ) (Cb : ℝ) (hCb : 0 < Cb) (hv_bound : ∀ x, |v x| ≤ Cb * (1 + |x|))
    (h_absm : Integrable (fun t => d.density t * |t|)) :
    Tendsto (fun x => (1 - d.cdf x) * v x) atTop (𝓝 0) := by
  have h_dom_int := density_mul_one_add_abs_integrable d h_absm
  -- `1 - F(x) = ∫_{Ioi x} density` is a nonneg tail
  have h_one_sub : ∀ x, 1 - d.cdf x = ∫ t in Ioi x, d.density t := by
    intro x; rw [ContDist.cdf_eq_integral]
    have := integral_add_compl (s := Iic x) measurableSet_Iic d.integrable
    rw [compl_Iic, d.integral_one] at this; linarith
  have h_one_sub_nn : ∀ x, 0 ≤ 1 - d.cdf x := fun x => by linarith [(d.cdf.range x).2]
  -- Squeeze: `|(1-F(x))·v(x)| ≤ Cb · ∫_{Ioi x} density·(1+|t|) → 0`
  have h_tail := (tail_Ioi_tendsto_zero_real (fun t => d.density t * (1 + |t|))
    h_dom_int (fun t => mul_nonneg (d.nonneg t) (by linarith [abs_nonneg t]))).const_mul Cb
  rw [mul_zero] at h_tail
  apply squeeze_zero_norm' (h' := h_tail)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs]
  calc |((1 : ℝ) - d.cdf x) * v x|
      = (1 - d.cdf x) * |v x| := by rw [abs_mul, abs_of_nonneg (h_one_sub_nn x)]
    _ ≤ (1 - d.cdf x) * (Cb * (1 + |x|)) :=
        mul_le_mul_of_nonneg_left (hv_bound x) (h_one_sub_nn x)
    _ = Cb * ((1 - d.cdf x) * (1 + |x|)) := by ring
    _ = Cb * ((∫ t in Ioi x, d.density t) * (1 + x)) := by rw [h_one_sub, abs_of_nonneg hx]
    _ ≤ Cb * (∫ t in Ioi x, d.density t * (1 + |t|)) := by
        apply mul_le_mul_of_nonneg_left _ hCb.le
        rw [← integral_mul_const]
        apply setIntegral_mono_on (d.integrable.mul_const _).integrableOn
          h_dom_int.integrableOn measurableSet_Ioi
        intro t (ht : x < t)
        apply mul_le_mul_of_nonneg_left _ (d.nonneg t)
        have : |t| = t := abs_of_nonneg (le_of_lt (lt_of_le_of_lt hx ht))
        linarith

/-- For `v` with linear growth `|v x| ≤ Cb(1+|x|)`, the value-weighted CDF `F(x)·v(x)` tends to `0`
as `x → -∞`, dominated by the tail of `density·(1+|t|)`. -/
private lemma cdf_mul_tendsto_atBot_zero (d : ContDist)
    (v : ℝ → ℝ) (Cb : ℝ) (hCb : 0 < Cb) (hv_bound : ∀ x, |v x| ≤ Cb * (1 + |x|))
    (h_absm : Integrable (fun t => d.density t * |t|)) :
    Tendsto (fun x => d.cdf x * v x) atBot (𝓝 0) := by
  have h_dom_int := density_mul_one_add_abs_integrable d h_absm
  have h_cdf_eq : ∀ x, d.cdf x = ∫ t in Iic x, d.density t := ContDist.cdf_eq_integral d
  have h_cdf_nn : ∀ x, 0 ≤ d.cdf x := fun x => (d.cdf.range x).1
  -- Squeeze: `|F(x)·v(x)| ≤ Cb · ∫_{Iic x} density·(1+|t|) → 0`
  have h_tail := (tail_Iic_tendsto_zero_real (fun t => d.density t * (1 + |t|))
    h_dom_int (fun t => mul_nonneg (d.nonneg t) (by linarith [abs_nonneg t]))).const_mul Cb
  rw [mul_zero] at h_tail
  apply squeeze_zero_norm' (h' := h_tail)
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs]
  calc |d.cdf x * v x|
      = d.cdf x * |v x| := by rw [abs_mul, abs_of_nonneg (h_cdf_nn x)]
    _ ≤ d.cdf x * (Cb * (1 + |x|)) := mul_le_mul_of_nonneg_left (hv_bound x) (h_cdf_nn x)
    _ = Cb * (d.cdf x * (1 + |x|)) := by ring
    _ = Cb * ((∫ t in Iic x, d.density t) * (1 + (-x))) := by rw [h_cdf_eq, abs_of_nonpos hx]
    _ ≤ Cb * (∫ t in Iic x, d.density t * (1 + |t|)) := by
        apply mul_le_mul_of_nonneg_left _ hCb.le
        rw [← integral_mul_const]
        apply setIntegral_mono_on (d.integrable.mul_const _).integrableOn
          h_dom_int.integrableOn measurableSet_Iic
        intro t (ht : t ≤ x)
        apply mul_le_mul_of_nonneg_left _ (d.nonneg t)
        have : |t| = -t := abs_of_nonpos (le_trans ht hx)
        linarith

/-- For a `C²` monotone concave `v` with linear growth, second-order stochastic dominance of `dF`
over `dG` forces the expectation ordering `dG.expect v ≤ dF.expect v`. -/
lemma sosd_smooth_step
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (v : ℝ → ℝ) (hv_smooth : ContDiff ℝ 2 v) (hv_mono : Monotone v)
    (hv_conc : ConcaveOn ℝ univ v)
    (Cb : ℝ) (hCb : 0 < Cb) (hv_bound : ∀ x, |v x| ≤ Cb * (1 + |x|))
    (hv_intF : Integrable (fun x => dF.density x * v x))
    (hv_intG : Integrable (fun x => dG.density x * v x))
    (h_meanF : Integrable (fun x => dF.density x * |x|))
    (h_meanG : Integrable (fun x => dG.density x * |x|)) :
    dG.expect v ≤ dF.expect v := by
  -- Extract derivatives
  set v' := deriv v with hv'_def
  set v'' := deriv v' with hv''_def
  -- Smoothness: ContDiff ℝ 2 v gives Differentiable, HasDerivAt, Continuous for v' and v''
  have hv_diff : Differentiable ℝ v := hv_smooth.differentiable (by norm_num)
  have hv'_cont : Continuous v' := hv_smooth.continuous_deriv (by norm_num)
  have hv'_smooth : ContDiff ℝ 1 v' := by
    have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h2, contDiff_succ_iff_deriv] at hv_smooth
    exact hv_smooth.2.2
  have hv'_diff : Differentiable ℝ v' := hv'_smooth.differentiable (by norm_num)
  have hv''_cont : Continuous v'' := hv'_smooth.continuous_deriv le_rfl
  have h_deriv_v : ∀ x, HasDerivAt v (v' x) x := fun x => (hv_diff x).hasDerivAt
  have h_deriv_v' : ∀ x, HasDerivAt v' (v'' x) x := fun x => (hv'_diff x).hasDerivAt
  -- v' ≥ 0 (monotone), v'' ≤ 0 (concave → v' antitone)
  have hv'_nonneg : ∀ x, 0 ≤ v' x := fun x => hv_mono.deriv_nonneg
  have hv'_anti : Antitone v' := by
    have h_antiOn := hv_conc.antitoneOn_deriv (fun x _ => hv_diff x)
    exact fun a b hab => h_antiOn (mem_univ a) (mem_univ b) hab
  have hv''_nonpos : ∀ x, v'' x ≤ 0 := fun _ => hv'_anti.deriv_nonpos
  -- CDF integrability
  have h_meanF_t : Integrable (fun t => dF.density t * t) := density_mul_id_integrable dF h_meanF
  have h_meanG_t : Integrable (fun t => dG.density t * t) := density_mul_id_integrable dG h_meanG
  have h_cdf_int : ∀ x, IntegrableOn dF.cdf (Iic x) ∧ IntegrableOn dG.cdf (Iic x) :=
    fun x => ⟨cdf_integrableOn_Iic dF x h_meanF_t, cdf_integrableOn_Iic dG x h_meanG_t⟩
  -- Boundary decay and integrability conditions (each derivable from v' bounded + CDF properties)
  -- v' bounded above by Cb (from linear growth + FTC + antitone v')
  have hv'_le_Cb : ∀ x₀ : ℝ, v' x₀ ≤ Cb := by
    intro x₀
    by_contra h_neg; push Not at h_neg
    -- v'(x₀) > Cb. Pick a far enough below x₀ and use FTC + antitone.
    set ε := v' x₀ - Cb with hε_def
    have hε_pos : 0 < ε := by linarith
    set R₀ := (|v x₀| + Cb + Cb * |x₀| + 1) / ε
    have hR₀_pos : 0 < R₀ := by positivity
    set a := x₀ - (R₀ + 1) with ha_def
    have ha_lt : a < x₀ := by linarith
    have hftc : ∫ t in a..x₀, v' t = v x₀ - v a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => h_deriv_v t) (hv'_cont.intervalIntegrable _ _)
    -- ∫_a^{x₀} v' ≥ v'(x₀)*(x₀-a) since v' antitone ⟹ v'(t) ≥ v'(x₀) for t ≤ x₀
    have h_lower : v' x₀ * (x₀ - a) ≤ ∫ t in a..x₀, v' t := by
      rw [intervalIntegral.integral_of_le ha_lt.le]
      -- v'(x₀) * (x₀-a) = ∫_{Ioc a x₀} v'(x₀) ≤ ∫_{Ioc a x₀} v'(t)
      have h_const_eq : v' x₀ * (x₀ - a) = ∫ _ in Ioc a x₀, v' x₀ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
            ENNReal.toReal_ofReal (show 0 ≤ x₀ - a by linarith), mul_comm]
      rw [h_const_eq]
      apply setIntegral_mono_on
      · exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      · exact hv'_cont.integrableOn_Ioc
      · exact measurableSet_Ioc
      · intro t ⟨_, htx⟩; exact hv'_anti htx
    have h_dist : x₀ - a = R₀ + 1 := by simp [ha_def]
    have h_abs_a : |a| ≤ |x₀| + R₀ + 1 := by
      simp only [ha_def]
      have := abs_sub x₀ (R₀ + 1)
      have := abs_of_pos (show 0 < R₀ + 1 by linarith)
      linarith
    -- v(x₀) - v(a) ≤ |v(x₀)| + Cb*(1+|a|) ≤ |v(x₀)| + Cb*(1+|x₀|+R₀+1)
    have h_combined : v' x₀ * (R₀ + 1) ≤ |v x₀| + Cb * (1 + |x₀| + R₀ + 1) := by
      calc v' x₀ * (R₀ + 1) = v' x₀ * (x₀ - a) := by rw [h_dist]
        _ ≤ v x₀ - v a := by linarith
        _ ≤ |v x₀| + Cb * (1 + |a|) := by
            linarith [le_abs_self (v x₀), neg_abs_le (v a), hv_bound a]
        _ ≤ |v x₀| + Cb * (1 + |x₀| + R₀ + 1) := by
            have : 1 + |a| ≤ 1 + |x₀| + R₀ + 1 := by linarith
            nlinarith
    -- Expand: (Cb+ε)*(R₀+1) ≤ |v x₀| + Cb*(2+|x₀|+R₀), cancel Cb*(R₀+1)
    have : ε * (R₀ + 1) ≤ |v x₀| + Cb + Cb * |x₀| := by nlinarith [hε_def]
    -- But ε*R₀ = |v x₀| + Cb + Cb*|x₀| + 1 by definition
    have h_ε_R₀ : ε * R₀ = |v x₀| + Cb + Cb * |x₀| + 1 := by
      simp only [R₀]; field_simp
    linarith [mul_pos hε_pos (show (0 : ℝ) < 1 from one_pos)]
  -- Continuity of CDFs
  have hF_cont : Continuous dF.cdf := contdist_cdf_continuous dF
  have hG_cont : Continuous dG.cdf := contdist_cdf_continuous dG
  -- Stieltjes regularizations of the (right-continuous) CDFs and of `v` are the identity
  have hv_cont : Continuous v := hv_conc.locallyLipschitz.continuous
  have hF_eq : ∀ x, (stieltjes dF.cdf.mono) x = dF.cdf x :=
    stieltjes_eq_of_rightCts dF.cdf.mono dF.cdf.right_continuous
  have hG_eq : ∀ x, (stieltjes dG.cdf.mono) x = dG.cdf x :=
    stieltjes_eq_of_rightCts dG.cdf.mono dG.cdf.right_continuous
  have hv_eq : ∀ x, (stieltjes hv_mono) x = v x :=
    fun x => stieltjes_eq_of_rightCts hv_mono
      (fun _ => hv_cont.continuousAt.continuousWithinAt) x
  -- F - G is integrable on Iic 0 (from h_cdf_int at 0)
  have h_FG_intOn_Iic0 : IntegrableOn (fun x => dF.cdf x - dG.cdf x) (Iic 0) :=
    (h_cdf_int 0).1.sub (h_cdf_int 0).2
  -- F - G is integrable on Ioi 0 using integrableOn_Ioi_of_intervalIntegral_norm_bounded
  -- with uniform bound ∫_0^n ‖F-G‖ ≤ 2*(E_F[|X|]+E_G[|X|]) from the IBP identity
  -- ∫_{Ioc 0 n}(1-F) = n*(1-F(n)) + ∫_{Ioc 0 n} density*t ≤ 2*E_F[|X|].
  -- Helper: 1 - CDF is integrable on Ioi 0 given finite first absolute moment
  have h_one_sub_cdf_intOn_Ioi : ∀ (d : ContDist),
      Integrable (fun t => d.density t * |t|) →
      Integrable (fun t => d.density t * t) →
      IntegrableOn (fun x => 1 - d.cdf x) (Ioi 0) := by
    intro d h_absm h_mt
    -- Use integrableOn_Ioi_of_intervalIntegral_norm_bounded with bound 2*∫density*|t|
    set B := 2 * ∫ t, d.density t * |t| with hB_def
    exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded B 0
      (fun (n : ℕ) => (continuous_const.sub (contdist_cdf_continuous d)).integrableOn_Ioc)
      tendsto_natCast_atTop_atTop
      (Eventually.of_forall fun (n : ℕ) => by
      -- 1 - F(x) ∈ [0,1] for all x, so ‖1-F(x)‖ = 1-F(x)
      have h_nn : ∀ x, 0 ≤ 1 - d.cdf x := fun x => by linarith [d.cdf_le_one x]
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
      calc ∫ x in Ioc 0 (↑n : ℝ), ‖1 - d.cdf x‖
          = ∫ x in Ioc 0 (↑n : ℝ), (1 - d.cdf x) := by
            congr 1; ext x; rw [Real.norm_eq_abs, abs_of_nonneg (h_nn x)]
        _ = ↑n * (1 - d.cdf ↑n) + ∫ t in Ioc 0 (↑n : ℝ), d.density t * t := by
            -- From integral_cdf_Iic_eq: ∫_{Iic x} F = x*F(x) - ∫_{Iic x} density*t
            have h_ibp_n := integral_cdf_Iic_eq d (↑n : ℝ) h_mt
            have h_ibp_0 := integral_cdf_Iic_eq d 0 h_mt
            -- ∫_{Ioc 0 n} (1-F) = n - ∫_{Ioc 0 n} F
            have h_one_sub_int : ∫ x in Ioc 0 (↑n : ℝ), (1 - d.cdf x) =
                ↑n - ∫ s in Ioc 0 (↑n : ℝ), d.cdf s := by
              have h_const_int : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0:ℝ) (↑n:ℝ)) :=
                integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
              rw [integral_sub h_const_int
                (cdf_integrableOn_Iic d (↑n : ℝ) h_mt |>.mono_set Ioc_subset_Iic_self)]
              rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
                  ENNReal.toReal_ofReal (by simp [Nat.cast_nonneg] : 0 ≤ (↑n : ℝ) - 0)]
              ring
            -- ∫_{Ioc 0 n} F = ∫_{Iic n} F - ∫_{Iic 0} F (splitting the Iic integral)
            -- Split Iic n = Iic 0 ∪ Ioc 0 n
            have h_F_Iic_split :
                ∫ s in Iic 0 ∪ Ioc 0 (↑n : ℝ), d.cdf s =
                (∫ s in Iic 0, d.cdf s) + ∫ s in Ioc 0 (↑n : ℝ), d.cdf s :=
              setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
                (cdf_integrableOn_Iic d 0 h_mt)
                (cdf_integrableOn_Iic d (↑n : ℝ) h_mt |>.mono_set Ioc_subset_Iic_self)
            have h_Iic_eq : Iic (0 : ℝ) ∪ Ioc 0 (↑n : ℝ) = Iic (↑n : ℝ) :=
              Iic_union_Ioc_eq_Iic (Nat.cast_nonneg n)
            rw [h_Iic_eq] at h_F_Iic_split
            have h_dt_Iic_split :
                ∫ t in Iic 0 ∪ Ioc 0 (↑n : ℝ), d.density t * t =
                (∫ t in Iic 0, d.density t * t) + ∫ t in Ioc 0 (↑n : ℝ), d.density t * t :=
              setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
                h_mt.integrableOn h_mt.integrableOn
            rw [h_Iic_eq] at h_dt_Iic_split
            -- Now combine using the two IBP identities and the splits
            simp only [zero_mul, zero_sub] at h_ibp_0
            rw [h_one_sub_int]
            have : ↑n * (1 - d.cdf ↑n) = ↑n - ↑n * d.cdf ↑n := by ring
            linarith
        _ ≤ (∫ t, d.density t * |t|) + ∫ t, d.density t * |t| := by
            -- First bound: ↑n * (1 - F(n)) ≤ ∫ density*|t|
            have ha : ↑n * (1 - d.cdf ↑n) ≤ ∫ t, d.density t * |t| := by
              have h_one_sub_eq : 1 - d.cdf ↑n = ∫ t in Ioi (↑n : ℝ), d.density t := by
                rw [ContDist.cdf_eq_integral]
                have := integral_add_compl (s := Iic (↑n : ℝ)) measurableSet_Iic d.integrable
                rw [compl_Iic, d.integral_one] at this; linarith
              have h_mul_eq : ↑n * (∫ t in Ioi (↑n : ℝ), d.density t) =
                  ∫ t in Ioi (↑n : ℝ), d.density t * ↑n := by
                rw [mul_comm, integral_mul_const]
              rw [h_one_sub_eq, h_mul_eq]
              calc ∫ t in Ioi (↑n : ℝ), d.density t * ↑n
                  ≤ ∫ t in Ioi (↑n : ℝ), d.density t * |t| := by
                    apply setIntegral_mono_on
                    · exact (d.integrable.mul_const _).integrableOn
                    · exact h_absm.integrableOn
                    · exact measurableSet_Ioi
                    · intro t (ht : (↑n : ℝ) < t)
                      apply mul_le_mul_of_nonneg_left _ (d.nonneg t)
                      rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith
                _ ≤ ∫ t, d.density t * |t| :=
                    setIntegral_le_integral h_absm (ae_of_all _ fun t =>
                      mul_nonneg (d.nonneg t) (abs_nonneg t))
            -- Second bound: ∫_{Ioc 0 n} density*t ≤ ∫ density*|t|
            have hb : ∫ t in Ioc 0 (↑n : ℝ), d.density t * t ≤ ∫ t, d.density t * |t| :=
              calc ∫ t in Ioc 0 (↑n : ℝ), d.density t * t
                  ≤ ∫ t in Ioc 0 (↑n : ℝ), d.density t * |t| := by
                    apply setIntegral_mono_on h_mt.integrableOn h_absm.integrableOn
                      measurableSet_Ioc
                    intro t _; exact mul_le_mul_of_nonneg_left (le_abs_self t) (d.nonneg t)
                _ ≤ ∫ t, d.density t * |t| :=
                    setIntegral_le_integral h_absm (ae_of_all _ fun t =>
                      mul_nonneg (d.nonneg t) (abs_nonneg t))
            exact add_le_add ha hb
        _ = B := by rw [hB_def]; ring)
  have h_FG_intOn_Ioi0 : IntegrableOn (fun x => dF.cdf x - dG.cdf x) (Ioi 0) := by
    -- F - G = (1-G) - (1-F), both integrable on Ioi 0
    have h_eq : (fun x => dF.cdf x - dG.cdf x) =
        fun x => (1 - dG.cdf x) - (1 - dF.cdf x) := by ext x; ring
    rw [h_eq]
    exact (h_one_sub_cdf_intOn_Ioi dG h_meanG h_meanG_t).sub
      (h_one_sub_cdf_intOn_Ioi dF h_meanF h_meanF_t)
  -- Combine: F-G is globally integrable
  have h_FG_int : Integrable (fun x => dF.cdf x - dG.cdf x) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact h_FG_intOn_Iic0.union h_FG_intOn_Ioi0
  -- |H(x)| = |∫_{Iic x}(F-G)| ≤ ∫_{Iic x}|F-G|  (triangle inequality for the integral)
  have h_H_bound : ∀ x, |integratedCDFDiff dF dG x| ≤
      ∫ t in Iic x, |dF.cdf t - dG.cdf t| := by
    intro x
    have h := norm_integral_le_integral_norm
      (μ := volume.restrict (Iic x)) (fun t => dF.cdf t - dG.cdf t)
    simp only [Real.norm_eq_abs] at h; exact h
  -- h_bdy_left: v' * H → 0 at -∞, since |H(x)| → 0 and |v'*H| ≤ Cb*|H|.
  have h_bdy_left : Tendsto (fun x : ℝ => v' x * integratedCDFDiff dF dG x) atBot (𝓝 0) := by
    -- |H(x)| → 0 at -∞ via tail of integrable |F-G|
    have h_abs_FG_tail : Tendsto (fun x : ℝ => ∫ t in Iic x, |dF.cdf t - dG.cdf t|)
        atBot (𝓝 0) :=
      tail_Iic_tendsto_zero_real _ h_FG_int.norm (fun _ => abs_nonneg _)
    -- Squeeze: |v'*H| ≤ Cb * ∫_{Iic x} |F-G| → 0
    have h_tail_mul : Tendsto (fun x => Cb * ∫ t in Iic x, |dF.cdf t - dG.cdf t|)
        atBot (𝓝 0) := by
      rw [show (0 : ℝ) = Cb * 0 from (mul_zero _).symm]
      exact h_abs_FG_tail.const_mul Cb
    apply squeeze_zero_norm' (h' := h_tail_mul)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    calc |v' x| * |integratedCDFDiff dF dG x|
        ≤ Cb * |integratedCDFDiff dF dG x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [abs_of_nonneg (hv'_nonneg x)]; exact hv'_le_Cb x
      _ ≤ Cb * (∫ t in Iic x, |dF.cdf t - dG.cdf t|) :=
          mul_le_mul_of_nonneg_left (h_H_bound x) hCb.le
  have h_bdy_top_ibp1 : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hv_mono) x)
      atTop (𝓝 0) := by
    -- Step 1: rewrite stieltjes to CDF/v values
    simp_rw [hF_eq, hG_eq, hv_eq]
    -- Step 2: Decompose (G-F)*v = (1-F)*v - (1-G)*v
    have h_decomp : ∀ x, (dG.cdf x - dF.cdf x) * v x =
        (1 - dF.cdf x) * v x - (1 - dG.cdf x) * v x := by intro x; ring
    simp_rw [h_decomp]
    rw [show (0 : ℝ) = 0 - 0 from (sub_self 0).symm]
    -- Step 3: each survival-weighted value `(1-F)*v`, `(1-G)*v → 0` at +∞ (helper lemma)
    exact (one_sub_cdf_mul_tendsto_atTop_zero dF v Cb hCb hv_bound h_meanF).sub
      (one_sub_cdf_mul_tendsto_atTop_zero dG v Cb hCb hv_bound h_meanG)
  have h_bdy_bot_ibp1 : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hv_mono) x)
      atBot (𝓝 0) := by
    -- Step 1: rewrite stieltjes to CDF/v values
    simp_rw [hF_eq, hG_eq, hv_eq]
    -- Step 2: Decompose (G-F)*v = G*v - F*v (at -∞ both → 0)
    have h_decomp : ∀ x, (dG.cdf x - dF.cdf x) * v x =
        dG.cdf x * v x - dF.cdf x * v x := by intro x; ring
    simp_rw [h_decomp]
    rw [show (0 : ℝ) = 0 - 0 from (sub_self 0).symm]
    -- Step 3: each value-weighted CDF `G*v`, `F*v → 0` at -∞ (helper lemma)
    exact (cdf_mul_tendsto_atBot_zero dG v Cb hCb hv_bound h_meanG).sub
      (cdf_mul_tendsto_atBot_zero dF v Cb hCb hv_bound h_meanF)
  have h_int_GF_v' : Integrable (fun x => (dF.cdf x - dG.cdf x) * v' x) := by
    -- |(F-G)*v'| ≤ Cb * |F-G| since 0 ≤ v' ≤ Cb. And Cb*|F-G| is integrable.
    apply Integrable.mono' (h_FG_int.norm.const_mul Cb)
      ((hF_cont.sub hG_cont).aestronglyMeasurable.mul hv'_cont.aestronglyMeasurable)
    apply ae_of_all; intro x
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    calc |dF.cdf x - dG.cdf x| * |v' x|
        ≤ |dF.cdf x - dG.cdf x| * Cb := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonneg (hv'_nonneg x)]; exact hv'_le_Cb x
      _ = Cb * ‖dF.cdf x - dG.cdf x‖ := by rw [Real.norm_eq_abs]; ring
  have h_int_H_v'' : Integrable (fun x => integratedCDFDiff dF dG x * v'' x) := by
    -- |H(x)| ≤ ∫_ℝ |F-G| =: C_H (H bounded by total L¹ norm of F-G).
    -- |v''| integrable (total variation of v' bounded by Cb).
    -- Product: |H*v''| ≤ C_H * |v''|.
    -- Step 1: H is bounded
    set C_H := ∫ t, |dF.cdf t - dG.cdf t| with hCH_def
    have h_H_bdd : ∀ x, |integratedCDFDiff dF dG x| ≤ C_H := fun x =>
      (h_H_bound x).trans
        (setIntegral_le_integral h_FG_int.norm (ae_of_all _ fun t => abs_nonneg _))
    -- Step 2: v'' is integrable (total variation of v' is bounded by Cb via FTC)
    -- ∫_{-n}^n |v''| = ∫_{-n}^n (-v'') = v'(-n) - v'(n) ≤ Cb
    -- Use integrableOn_Ioi/Iic_of_intervalIntegral_norm_bounded
    have hv''_int : Integrable v'' := by
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      apply IntegrableOn.union
      · -- On Iic 0: use integrableOn_Iic_of_intervalIntegral_norm_bounded
        exact MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_bounded Cb 0
          (fun n => hv''_cont.integrableOn_Ioc)
          (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
          (Eventually.of_forall fun n => by
            simp only [Function.comp_apply]
            rw [intervalIntegral.integral_of_le
              (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(↑n : ℝ) ≤ 0)]
            calc ∫ t in Ioc (-(↑n : ℝ)) 0, ‖v'' t‖
                = ∫ t in Ioc (-(↑n : ℝ)) 0, (-v'' t) := by
                  congr 1; ext t; rw [Real.norm_eq_abs, abs_of_nonpos (hv''_nonpos t)]
              _ = ∫ t in (-(↑n : ℝ))..0, (-v'' t) := by
                  rw [intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n])]
              _ = v' (-(↑n : ℝ)) - v' 0 := by
                  have hftc : ∫ t in (-(↑n : ℝ))..(0 : ℝ), -v'' t = -(v' 0) - -(v' (-(↑n : ℝ))) :=
                    intervalIntegral.integral_eq_sub_of_hasDerivAt
                      (fun t _ => (h_deriv_v' t).neg)
                      (hv''_cont.neg.intervalIntegrable (-(↑n : ℝ)) 0)
                  linarith
              _ ≤ Cb := by linarith [hv'_le_Cb (-(↑n : ℝ)), hv'_nonneg 0])
      · -- On Ioi 0: similar
        exact MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded Cb 0
          (fun n => hv''_cont.integrableOn_Ioc)
          tendsto_natCast_atTop_atTop
          (Eventually.of_forall fun n => by
            rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
            calc ∫ t in Ioc 0 (↑n : ℝ), ‖v'' t‖
                = ∫ t in Ioc 0 (↑n : ℝ), (-v'' t) := by
                  congr 1; ext t; rw [Real.norm_eq_abs, abs_of_nonpos (hv''_nonpos t)]
              _ = ∫ t in (0 : ℝ)..(↑n : ℝ), (-v'' t) := by
                  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
              _ = v' 0 - v' (↑n : ℝ) := by
                  have hftc : ∫ t in (0 : ℝ)..↑n, -v'' t = -(v' ↑n) - -(v' 0) :=
                    intervalIntegral.integral_eq_sub_of_hasDerivAt
                      (fun t _ => (h_deriv_v' t).neg)
                      (hv''_cont.neg.intervalIntegrable 0 ↑n)
                  linarith
              _ ≤ Cb := by linarith [hv'_le_Cb 0, hv'_nonneg (↑n : ℝ)])
    -- Step 3: |H*v''| ≤ C_H * |v''|, and C_H * |v''| is integrable
    -- H is continuous (differentiable everywhere from integratedCDFDiff_hasDerivAt)
    have hH_cont : Continuous (integratedCDFDiff dF dG) :=
      (show Differentiable ℝ (integratedCDFDiff dF dG) from
        fun x => (integratedCDFDiff_hasDerivAt dF dG x
          (fun y => (h_cdf_int y).1) (fun y => (h_cdf_int y).2)).differentiableAt).continuous
    exact Integrable.mono' (hv''_int.norm.const_mul C_H)
      (hH_cont.mul hv''_cont).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |integratedCDFDiff dF dG x| * |v'' x|
            ≤ C_H * |v'' x| := mul_le_mul_of_nonneg_right (h_H_bdd x) (abs_nonneg _)
          _ = C_H * ‖v'' x‖ := by rw [Real.norm_eq_abs])
  have h_stieltjes_int : Integrable
      (fun y => (stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y)
      (stieltjesMeasure hv_mono) := by
    -- stieltjesMeasure hv_mono = withDensity volume (ENNReal.ofReal ∘ v')
    rw [Monotone.stieltjes_measure_eq_withDensity hv_mono h_deriv_v hv'_nonneg hv'_cont]
    -- Integrable g (withDensity f) ↔ Integrable (g * f.toReal) volume
    rw [MeasureTheory.integrable_withDensity_iff
      (hv'_cont.measurable.ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    -- Goal: Integrable (fun x => (G_sf x - F_sf x) * (ENNReal.ofReal (v' x)).toReal)
    -- Simplify: toReal (ofReal (v' x)) = v' x (since v' x ≥ 0)
    have h_eq : (fun x => ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) *
        (ENNReal.ofReal (v' x)).toReal) =
        fun x => (dG.cdf x - dF.cdf x) * v' x := by
      ext x
      rw [ENNReal.toReal_ofReal (hv'_nonneg x), hG_eq x, hF_eq x]
    rw [h_eq]
    -- (G-F)*v' = -((F-G)*v'), which is integrable iff (F-G)*v' is
    have h_neg : (fun x => (dG.cdf x - dF.cdf x) * v' x) =
        fun x => -((dF.cdf x - dG.cdf x) * v' x) := by ext x; ring
    rw [h_neg]; exact h_int_GF_v'.neg
  exact sosd_expect_concave_mono_smooth_assembled
    h_sosd hv_mono hv'_nonneg hv''_nonpos
    h_deriv_v h_deriv_v' hv'_cont hv''_cont
    hv_intF hv_intG
    h_bdy_left h_bdy_top_ibp1 h_bdy_bot_ibp1
    h_int_GF_v' h_int_H_v'' h_stieltjes_int

end Econlib.Probability
