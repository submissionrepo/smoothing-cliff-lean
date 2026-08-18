/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.StieltjesAbsCont
public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Econlib.Math.Probability.Quantile
public import Econlib.Probability.ProbDist.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Chain rule for Stieltjes integration against `F^k`

For an atomless probability distribution `F` on `ℝ`, the Stieltjes measure induced by `F(·)^k`
admits a density `k · F^{k-1}` against the Stieltjes measure of `F` itself (which, for `F` the CDF
of a probability measure, is just the underlying probability measure). Concretely,

`∫_{(a, b]} φ d(μ_{F^k}) = k · ∫_{(a, b]} φ · F^{k-1} dF`,

and an integration-by-parts corollary against a `C¹` function. Atomlessness — `∀ x, F {x} = 0` — is
the only regularity assumed: It makes the CDF continuous (no jumps), so the quantile transform
`map_quantile_volume_Ioo` realizes `F` as the pushforward of Lebesgue on `(0,1)` and `F^k` becomes
the pushforward of `u ↦ u^k`.

## Main definitions

* `cdfReal F` — the CDF as a plain real-valued function `x ↦ ((F : Measure ℝ) (Iic x)).toReal`. It
  equals `ProbabilityTheory.cdf` as a function but stays an `ℝ → ℝ`, so it can be raised to a power
  and fed to `stieltjesMeasure`.

## Main statements

* `cdfReal_monotone`, `cdfReal_pow_monotone` — monotonicity of `cdfReal F` and of `(cdfReal F)^k`.
* `cdfReal_continuous_of_noAtoms` — under atomlessness `cdfReal F` is continuous.
* `cdfReal_quantile_eq_self` — under atomlessness `cdfReal F` inverts the quantile on `(0,1)`.
* `stieltjes_pow_cdf_eq_pow_smul_F` — the chain rule on `(a, b]`.
* `integral_deriv_mul_cdf_pow` — the integration-by-parts corollary against a `C¹` function.

## Notes

This fills the gap between Mathlib's absolutely-continuous Stieltjes integration-by-parts (which
assumes the integrator is absolutely continuous) and Econlib's `stieltjes_ibp_local` (which handles
two monotone integrators but does not turn one integrator into a power of another).

## Tags

stieltjes measure, chain rule, integration by parts, quantile, atomless
-/

@[expose] public section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Real

namespace Econlib.Probability

open Monotone

variable {F : ProbDist ℝ}

/-- The CDF of a `ProbDist ℝ` as a plain real-valued function (so we can take powers and feed it to
`stieltjesMeasure`, which expects `ℝ → ℝ`). -/
noncomputable def cdfReal (F : ProbDist ℝ) (x : ℝ) : ℝ :=
  ((F : Measure ℝ) (Iic x)).toReal

lemma cdfReal_nonneg (F : ProbDist ℝ) (x : ℝ) : 0 ≤ cdfReal F x :=
  ENNReal.toReal_nonneg

lemma cdfReal_monotone (F : ProbDist ℝ) : Monotone (cdfReal F) :=
  Measure.monotone_toReal_measure_Iic (μ := (F : Measure ℝ))

lemma cdfReal_pow_monotone (F : ProbDist ℝ) (k : ℕ) :
    Monotone (fun x => (cdfReal F x) ^ k) := fun _ _ hxy =>
  pow_le_pow_left₀ (cdfReal_nonneg F _) (cdfReal_monotone F hxy) k

/-- Under atomlessness, `cdfReal F` agrees pointwise with the Stieltjes function
`ProbabilityTheory.cdf (F : Measure ℝ)`. Both are right-continuous monotone representations of the
CDF; atomlessness kills any jump, and the right-continuous representation simply equals the value
of the CDF. -/
lemma cdfReal_eq_cdf (x : ℝ) :
    cdfReal F x = (ProbabilityTheory.cdf (F : Measure ℝ)) x := by
  rw [cdfReal, Measure.cdf_eq_toReal_measure_Iic]

/-- Under atomlessness (`F {x} = 0` for all `x`), the CDF function `cdfReal F` is continuous. The
CDF is always right-continuous; atomlessness kills any jump, so the left limit also agrees with the
value. -/
lemma cdfReal_continuous_of_noAtoms (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0) :
    Continuous (cdfReal F) := by
  haveI : NoAtoms (F : Measure ℝ) := ⟨hF_atomless⟩
  -- Continuous = continuous at every point.
  refine continuous_iff_continuousAt.mpr fun x => ?_
  -- By `Monotone.continuousAt_iff_leftLim_eq_rightLim`, it suffices to show
  -- `leftLim = rightLim` at `x`.
  rw [(cdfReal_monotone F).continuousAt_iff_leftLim_eq_rightLim]
  -- `rightLim = cdfReal F x` by right-continuity (the CDF is right-continuous).
  have h_rc : Function.rightLim (cdfReal F) x = cdfReal F x :=
    (Measure.rightContinuous_toReal_measure_Iic (μ := (F : Measure ℝ)) x).rightLim_eq
  -- For left-continuity, use the Stieltjes-measure formula: the size of the jump at `x` is
  -- `ofReal (cdfReal F x - leftLim (cdfReal F) x)`, and equals the measure of `{x}`,
  -- which is `0` by atomlessness.
  -- Equivalent formulation via `ProbabilityTheory.cdf`:
  have h_cdf_eq : (⇑(ProbabilityTheory.cdf (F : Measure ℝ))) = cdfReal F := by
    funext y; exact (cdfReal_eq_cdf (F := F) y).symm
  have h_measure : (ProbabilityTheory.cdf (F : Measure ℝ)).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf]
    exact hF_atomless x
  -- StieltjesFunction.measure_singleton gives the jump size.
  rw [StieltjesFunction.measure_singleton] at h_measure
  -- ENNReal.ofReal vanishes iff the real number is ≤ 0.
  have h_jump_zero : (ProbabilityTheory.cdf (F : Measure ℝ)) x
      - Function.leftLim (⇑(ProbabilityTheory.cdf (F : Measure ℝ))) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp h_measure
  -- Combined with monotonicity, this gives leftLim ≥ value.
  have h_mono_le : Function.leftLim (⇑(ProbabilityTheory.cdf (F : Measure ℝ))) x ≤
      (ProbabilityTheory.cdf (F : Measure ℝ)) x :=
    Monotone.leftLim_le (ProbabilityTheory.monotone_cdf _) (le_refl x)
  have h_eq : Function.leftLim (⇑(ProbabilityTheory.cdf (F : Measure ℝ))) x =
      (ProbabilityTheory.cdf (F : Measure ℝ)) x := le_antisymm h_mono_le (by linarith)
  -- Transport back to cdfReal F.
  rw [show Function.leftLim (cdfReal F) x
        = Function.leftLim (⇑(ProbabilityTheory.cdf (F : Measure ℝ))) x by rw [h_cdf_eq],
      h_eq, h_cdf_eq, h_rc]

/-- Under atomlessness, the CDF inverts the quantile function on `Ioo 0 1`:
`cdfReal F (quantile F u) = u`. -/
lemma cdfReal_quantile_eq_self (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    cdfReal F (Measure.quantile (F : Measure ℝ) u) = u := by
  -- The set `S := {x | u ≤ (F (Iic x)).toReal}` is closed under continuity of `cdfReal F`,
  -- and bounded below for `u > 0`. So `sInf S ∈ S`, giving `u ≤ cdfReal F (quantile F u)`.
  -- Conversely, by continuity, if `cdfReal F (quantile F u) > u`, then for some `δ > 0`,
  -- `cdfReal F y > u` for all `y > quantile F u - δ`, contradicting `quantile F u` being
  -- the infimum.
  have h_cont := cdfReal_continuous_of_noAtoms (F := F) hF_atomless
  set c := Measure.quantile (F : Measure ℝ) u with hc_def
  -- Forward (`u ≤ cdfReal F c`): from quantile_le_iff applied at x := c (the trivial inequality
  -- c ≤ c).
  have h_ge : u ≤ cdfReal F c := (Measure.quantile_le_iff hu).mp (le_refl c)
  -- Reverse (`cdfReal F c ≤ u`): if not, by continuity of cdfReal F we'd find `y < c` with
  -- `cdfReal F y > u`, contradicting `c = sInf {x | u ≤ cdfReal F x}`.
  refine le_antisymm ?_ h_ge
  by_contra hlt
  push Not at hlt
  -- hlt : u < cdfReal F c. By continuity, ∃ δ > 0, ∀ y, |y - c| < δ → cdfReal F y > u.
  have h_cont_at_c : ContinuousAt (cdfReal F) c := h_cont.continuousAt
  rw [Metric.continuousAt_iff] at h_cont_at_c
  obtain ⟨δ, hδ_pos, hδ⟩ := h_cont_at_c (cdfReal F c - u) (by linarith)
  -- Pick y := c - δ/2 < c. Then |y - c| = δ/2 < δ, giving |F y - F c| < F c - u.
  set y := c - δ / 2 with hy_def
  have hy_lt : y < c := by rw [hy_def]; linarith
  have hy_dist : dist y c < δ := by
    rw [Real.dist_eq, hy_def, abs_of_nonpos (by linarith)]
    linarith
  have h_close := hδ hy_dist
  rw [Real.dist_eq, abs_lt] at h_close
  -- From h_close.1: -(cdfReal F c - u) < cdfReal F y - cdfReal F c, so u < cdfReal F y.
  have hy_in_set : u ≤ cdfReal F y := by linarith [h_close.1]
  -- Then y ∈ {x | u ≤ cdfReal F x}, but y < c = sInf of that set: contradiction.
  have hy_ge_inf : c ≤ y := csInf_le (Measure.Quantile.set_bddBelow hu.1) hy_in_set
  linarith

/-- The Stieltjes-function form of `(cdfReal F)^k` under no-atoms coincides with the function
itself, since continuity makes the right limit equal to the value. -/
private lemma cdfReal_pow_stieltjes_eq (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    (k : ℕ) (x : ℝ) :
    ((cdfReal_pow_monotone F k).stieltjesFunction) x = (cdfReal F x) ^ k := by
  rw [Monotone.stieltjesFunction_eq]
  -- rightLim of a continuous function equals the function itself.
  have h_cont_pow : Continuous (fun y => (cdfReal F y) ^ k) :=
    (cdfReal_continuous_of_noAtoms hF_atomless).pow k
  exact h_cont_pow.continuousAt.continuousWithinAt.rightLim_eq

/-- Stieltjes-measure of `(cdfReal F)^k` evaluated on `Ioc c d` under atomlessness. -/
private lemma stieltjesMeasure_cdfReal_pow_Ioc
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0) (k : ℕ) (c d : ℝ) :
    stieltjesMeasure (cdfReal_pow_monotone F k) (Ioc c d) =
      ENNReal.ofReal ((cdfReal F d) ^ k - (cdfReal F c) ^ k) := by
  -- Unfold to the Mathlib Stieltjes function and apply `measure_Ioc`.
  change ((cdfReal_pow_monotone F k).stieltjesFunction).measure (Ioc c d) = _
  rw [StieltjesFunction.measure_Ioc, cdfReal_pow_stieltjes_eq hF_atomless,
      cdfReal_pow_stieltjes_eq hF_atomless]

/-- For atomless `F` and `c ≤ d`, the F-integral `∫_{Ioc c d} k * F(x)^(k-1) dF` equals
`F(d)^k - F(c)^k`. The key chain-rule identity, proved by pushforward via the quantile function and
then FTC for `u ↦ u^k`. -/
private lemma integral_cdfReal_pow_sub_one_eq
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    (k : ℕ) {c d : ℝ} (hcd : c ≤ d) :
    ∫ x in Ioc c d, (k : ℝ) * (cdfReal F x) ^ (k - 1) ∂(F : Measure ℝ) =
      (cdfReal F d) ^ k - (cdfReal F c) ^ k := by
  -- Push forward via quantile to a Lebesgue integral on (0,1) ∩ Ioc (F c) (F d),
  -- then apply FTC to ∫ k*u^(k-1) du.
  set μ := (F : Measure ℝ)
  set q := Measure.quantile μ
  have hcont : Continuous (cdfReal F) := cdfReal_continuous_of_noAtoms hF_atomless
  -- Bounds on cdfReal F.
  have h_Fc_mem : cdfReal F c ∈ Icc (0 : ℝ) 1 :=
    ⟨cdfReal_nonneg F c, Measure.toReal_measure_Iic_le_one c⟩
  have h_Fd_mem : cdfReal F d ∈ Icc (0 : ℝ) 1 :=
    ⟨cdfReal_nonneg F d, Measure.toReal_measure_Iic_le_one d⟩
  have h_Fcd : cdfReal F c ≤ cdfReal F d := cdfReal_monotone F hcd
  -- Step 1: Express as a full integral with indicator.
  rw [show (∫ x in Ioc c d, (k : ℝ) * (cdfReal F x) ^ (k - 1) ∂μ) =
        ∫ x, (Ioc c d).indicator (fun x => (k : ℝ) * (cdfReal F x) ^ (k - 1)) x ∂μ by
        rw [integral_indicator measurableSet_Ioc]]
  -- Step 2: Apply integral_eq_integral_quantile.
  have h_aemeas : AEStronglyMeasurable
      ((Ioc c d).indicator (fun x => (k : ℝ) * (cdfReal F x) ^ (k - 1))) μ := by
    refine (AEStronglyMeasurable.indicator ?_ measurableSet_Ioc)
    exact (continuous_const.mul (hcont.pow (k - 1))).aestronglyMeasurable
  rw [Measure.integral_eq_integral_quantile (μ := μ)
    ((Ioc c d).indicator (fun x => (k : ℝ) * (cdfReal F x) ^ (k - 1))) h_aemeas]
  -- Step 3: Identify the integrand on Ioo 0 1.
  have h_inner : ∀ᵐ u, u ∈ Ioo (0 : ℝ) 1 →
      (Ioc c d).indicator (fun x => (k : ℝ) * (cdfReal F x) ^ (k - 1)) (q u) =
        (Ioc (cdfReal F c) (cdfReal F d)).indicator (fun u => (k : ℝ) * u ^ (k - 1)) u := by
    refine ae_of_all _ ?_
    intro u hu
    -- Split on whether q u ∈ Ioc c d. By quantile_le_iff, this is `F c < u ≤ F d`.
    by_cases h_qu_in : q u ∈ Ioc c d
    · -- q u ∈ Ioc c d ⟺ c < q u ∧ q u ≤ d ⟺ F c < u ∧ u ≤ F d.
      have hu_gt : cdfReal F c < u := by
        by_contra h_neg
        push Not at h_neg  -- u ≤ cdfReal F c
        -- u ≤ F c ⟺ q u ≤ c (by quantile_le_iff); contradicts c < q u
        have : q u ≤ c := (Measure.quantile_le_iff hu).mpr h_neg
        linarith [h_qu_in.1]
      have hu_le : u ≤ cdfReal F d := (Measure.quantile_le_iff hu).mp h_qu_in.2
      have h_u_in_Ioc : u ∈ Ioc (cdfReal F c) (cdfReal F d) := ⟨hu_gt, hu_le⟩
      rw [Set.indicator_of_mem h_qu_in, Set.indicator_of_mem h_u_in_Ioc]
      -- We need: k * (cdfReal F (q u))^(k-1) = k * u^(k-1)
      rw [cdfReal_quantile_eq_self hF_atomless hu]
    · -- q u ∉ Ioc c d.
      have h_u_not_in : u ∉ Ioc (cdfReal F c) (cdfReal F d) := by
        intro h_u_in
        apply h_qu_in
        -- We need q u ∈ Ioc c d, i.e., c < q u ∧ q u ≤ d.
        refine ⟨?_, ?_⟩
        · -- c < q u: equivalent to ¬(q u ≤ c) ⟺ ¬(u ≤ F c) ⟺ F c < u.
          by_contra h_neg
          push Not at h_neg
          have : u ≤ cdfReal F c := (Measure.quantile_le_iff hu).mp h_neg
          linarith [h_u_in.1]
        · exact (Measure.quantile_le_iff hu).mpr h_u_in.2
      rw [Set.indicator_of_notMem h_qu_in, Set.indicator_of_notMem h_u_not_in]
  -- Step 4: Rewrite the integral via h_inner.
  rw [setIntegral_congr_ae measurableSet_Ioo h_inner]
  -- Step 5: Evaluate the resulting Lebesgue integral on Ioo 0 1.
  -- It's k * ∫_{(0,1) ∩ Ioc (Fc) (Fd)} u^(k-1) du.
  rw [setIntegral_indicator measurableSet_Ioc]
  -- Step 6: Identify (Ioo 0 1) ∩ Ioc (F c) (F d) with Ioc (F c) (F d) modulo a null set.
  set Sint : Set ℝ := Ioo (0 : ℝ) 1 ∩ Ioc (cdfReal F c) (cdfReal F d) with hSint_def
  set Sfull : Set ℝ := Ioc (cdfReal F c) (cdfReal F d) with hSfull_def
  have h_set_eq : Sint =ᵐ[volume] Sfull := by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · -- Sint \ Sfull = ∅.
      have hempty : Sint \ Sfull = ∅ := by
        ext u; simp [Sint, Sfull, mem_diff, mem_inter_iff, mem_Ioo, mem_Ioc]
      rw [hempty]; exact measure_empty
    · -- Sfull \ Sint ⊆ {1}, measure zero.
      refine measure_mono_null (t := ({1} : Set ℝ)) ?_ (measure_singleton 1)
      intro u hu
      simp only [Sint, Sfull, mem_diff, mem_inter_iff, mem_Ioo, mem_Ioc, not_and] at hu
      simp only [mem_singleton_iff]
      obtain ⟨⟨hu_gt_Fc, hu_le_Fd⟩, hu_not⟩ := hu
      have hu_pos : 0 < u := lt_of_le_of_lt h_Fc_mem.1 hu_gt_Fc
      have hu_le_one : u ≤ 1 := le_trans hu_le_Fd h_Fd_mem.2
      -- hu_not has shape: (0 < u ∧ u < 1) → cdfReal F c < u → ¬ u ≤ cdfReal F d.
      by_contra hne
      have hu_lt_one : u < 1 := lt_of_le_of_ne hu_le_one hne
      exact hu_not ⟨hu_pos, hu_lt_one⟩ hu_gt_Fc hu_le_Fd
  rw [show ((∫ u in (Ioo (0 : ℝ) 1) ∩ Ioc (cdfReal F c) (cdfReal F d), (k : ℝ) * u ^ (k-1))
        = ∫ u in Sint, (k : ℝ) * u ^ (k-1)) from rfl,
      setIntegral_congr_set h_set_eq]
  -- Step 7: Evaluate via FTC for u ↦ u^k.
  -- ∫_{Ioc (Fc) (Fd)} k * u^(k-1) du = ∫_{Fc..Fd} k * u^(k-1) du = (Fd)^k - (Fc)^k.
  rw [show ∫ u in Ioc (cdfReal F c) (cdfReal F d), (k : ℝ) * u ^ (k - 1)
        = ∫ u in (cdfReal F c)..(cdfReal F d), (k : ℝ) * u ^ (k - 1) from
      (intervalIntegral.integral_of_le h_Fcd).symm]
  -- Apply FTC: d/du(u^k) = k * u^(k-1)
  have h_deriv : ∀ u, HasDerivAt (fun u : ℝ => u ^ k) ((k : ℝ) * u ^ (k - 1)) u := fun u =>
    hasDerivAt_pow k u
  have h_int : IntervalIntegrable (fun u => (k : ℝ) * u ^ (k - 1)) volume
      (cdfReal F c) (cdfReal F d) :=
    (continuous_const.mul (continuous_pow (k - 1))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h_deriv u) h_int]

/-- The density `k * (cdfReal F)^(k-1)` is bounded by `k`, hence finite. -/
private lemma cdfReal_pow_density_lt_top
    (k : ℕ) (x : ℝ) :
    ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1)) < ⊤ := ENNReal.ofReal_lt_top

/-- The density `k * (cdfReal F)^(k-1)` is bounded above by `k` (since `0 ≤ cdfReal F ≤ 1`). -/
private lemma cdfReal_pow_density_le (k : ℕ) (x : ℝ) :
    (k : ℝ) * (cdfReal F x) ^ (k - 1) ≤ (k : ℝ) := by
  have h_pow_le : (cdfReal F x) ^ (k - 1) ≤ 1 :=
    pow_le_one₀ (cdfReal_nonneg F _) (Measure.toReal_measure_Iic_le_one x)
  calc (k : ℝ) * (cdfReal F x) ^ (k - 1) ≤ (k : ℝ) * 1 := by gcongr
    _ = (k : ℝ) := by ring

/-- The withDensity measure on `Ioc c d` equals `ofReal((F d)^k - (F c)^k)`, the same as the
Stieltjes measure of `(cdfReal F)^k`. -/
private lemma withDensity_cdfReal_pow_Ioc
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    (k : ℕ) {c d : ℝ} (hcd : c ≤ d) :
    ((F : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1)))) (Ioc c d) =
      ENNReal.ofReal ((cdfReal F d) ^ k - (cdfReal F c) ^ k) := by
  rw [withDensity_apply _ measurableSet_Ioc]
  -- Convert lintegral of ofReal to ofReal of integral.
  have hcont : Continuous (cdfReal F) := cdfReal_continuous_of_noAtoms hF_atomless
  have h_nn : ∀ᵐ x ∂((F : Measure ℝ).restrict (Ioc c d)),
      0 ≤ (k : ℝ) * (cdfReal F x) ^ (k - 1) :=
    ae_of_all _ fun x => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (cdfReal_nonneg F _) _)
  have h_int : IntegrableOn (fun x => (k : ℝ) * (cdfReal F x) ^ (k - 1)) (Ioc c d)
      (F : Measure ℝ) := by
    refine Integrable.mono' (g := fun _ => (k : ℝ)) ?_ ?_ ?_
    · exact integrable_const _
    · exact (continuous_const.mul (hcont.pow (k - 1))).aestronglyMeasurable.restrict
    · refine ae_of_all _ fun x => ?_
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (cdfReal_nonneg F _) _))]
      exact cdfReal_pow_density_le k x
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  rw [integral_cdfReal_pow_sub_one_eq hF_atomless k hcd]

/-- **Measure equality**: The Stieltjes measure of `(cdfReal F)^k` is the F-measure weighted by
`k * (cdfReal F)^(k-1)`. -/
private lemma stieltjesMeasure_cdfReal_pow_eq_withDensity
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0) (k : ℕ) :
    stieltjesMeasure (cdfReal_pow_monotone F k) =
      (F : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1))) := by
  -- Both measures are locally finite; we verify equality on Ioc c d for c < d.
  -- For the withDensity side to be locally finite, we use that the density is bounded.
  haveI : IsFiniteMeasure
      ((F : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1)))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ]
    -- The integral of a bounded density against a finite measure is finite.
    refine lt_of_le_of_lt
      (setLIntegral_mono_ae' MeasurableSet.univ
        (g := fun _ => ENNReal.ofReal (k : ℝ)) (ae_of_all _ ?_)) ?_
    · intro x _hx
      -- pointwise: ofReal (k * F(x)^(k-1)) ≤ ofReal k
      exact ENNReal.ofReal_le_ofReal (cdfReal_pow_density_le k x)
    · -- ∫⁻ x, ofReal k ∂F = ofReal k * F(univ) = ofReal k < ⊤
      rw [setLIntegral_const, measure_univ]
      simp
  refine MeasureTheory.Measure.ext_of_Ioc _ _ ?_
  intro a b hab
  rw [stieltjesMeasure_cdfReal_pow_Ioc hF_atomless k,
      withDensity_cdfReal_pow_Ioc hF_atomless k hab.le]

/-- **Chain rule for `F^k` as a Stieltjes measure.** For `F : ProbDist ℝ` atomless and `φ`
continuous on `[a, b]`, integrating `φ` against the Stieltjes measure of `(cdfReal F)^k` on
`(a, b]` equals `k` times the `F`-integral of `φ · (cdfReal F)^{k-1}`. -/
theorem stieltjes_pow_cdf_eq_pow_smul_F
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    (k : ℕ) {a b : ℝ} (_hab : a ≤ b) {φ : ℝ → ℝ}
    (_hφ_cont : ContinuousOn φ (Icc a b)) :
    ∫ x in Ioc a b, φ x ∂(stieltjesMeasure (cdfReal_pow_monotone F k))
      = (k : ℝ) * ∫ x in Ioc a b, φ x * (cdfReal F x) ^ (k - 1) ∂(F : Measure ℝ) := by
  -- Step 1: Use the measure equality.
  rw [stieltjesMeasure_cdfReal_pow_eq_withDensity hF_atomless]
  -- Step 2: Convert the F-restricted integral via withDensity.
  -- ∫ in Ioc a b, φ ∂(F.withDensity g) = ∫ in Ioc a b, g.toReal • φ ∂F
  have hcont : Continuous (cdfReal F) := cdfReal_continuous_of_noAtoms hF_atomless
  have h_meas : AEMeasurable
      (fun x => ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1))) ((F : Measure ℝ)) :=
    (continuous_const.mul (hcont.pow (k - 1))).measurable.ennreal_ofReal.aemeasurable
  have h_density_fin : ∀ᵐ x ∂((F : Measure ℝ)),
      ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1)) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  -- For setIntegral with withDensity, we restrict the measure first then apply the lemma.
  rw [MeasureTheory.restrict_withDensity measurableSet_Ioc]
  rw [integral_withDensity_eq_integral_toReal_smul₀ h_meas.restrict
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x _ => ENNReal.ofReal_lt_top))]
  -- Step 3: Simplify (ENNReal.ofReal (k * ...)).toReal = k * ... (since k * ... ≥ 0)
  -- and rewrite • as * ; pull out the k.
  have h_simplify : ∫ x in Ioc a b,
        (ENNReal.ofReal ((k : ℝ) * (cdfReal F x) ^ (k - 1))).toReal • φ x ∂(F : Measure ℝ) =
      ∫ x in Ioc a b, (k : ℝ) * (cdfReal F x) ^ (k - 1) * φ x ∂(F : Measure ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    rw [smul_eq_mul, ENNReal.toReal_ofReal
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (cdfReal_nonneg F _) _))]
  rw [h_simplify]
  -- Step 4: Pull k out of the integral.
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
  ring

/-- **Integration by parts against `F^k`.** For `ψ : ℝ → ℝ` of class `C¹` and `F : ProbDist ℝ`
atomless, the Lebesgue integral of `ψ' · F^k` on `(a, b]` equals the boundary term
`ψ b · F(b)^k - ψ a · F(a)^k` minus the Stieltjes correction `k · ∫ ψ · F^{k-1} dF`. -/
theorem integral_deriv_mul_cdf_pow
    (hF_atomless : ∀ x, (F : Measure ℝ) {x} = 0)
    {ψ : ℝ → ℝ} (hψ_C1 : ContDiff ℝ 1 ψ)
    (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioc a b, deriv ψ x * (cdfReal F x) ^ k
      = ψ b * (cdfReal F b) ^ k - ψ a * (cdfReal F a) ^ k
        - (k : ℝ) * ∫ x in Ioc a b, ψ x * (cdfReal F x) ^ (k - 1) ∂(F : Measure ℝ) := by
  -- Handle the degenerate case a = b separately (both sides vanish).
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp
  -- Now assume a < b.
  set g := fun x => (cdfReal F x) ^ k
  set hg_mono : Monotone g := cdfReal_pow_monotone F k
  set μ_g := stieltjesMeasure hg_mono
  -- Step 1: g is continuous (continuity of cdfReal under no-atoms).
  have h_g_cont : Continuous g :=
    (cdfReal_continuous_of_noAtoms hF_atomless).pow k
  -- Step 2: μ_g (Ioc a x) = ofReal (g(x) - g(a)) under no-atoms.
  have h_μg_Ioc : ∀ x, μ_g (Ioc a x) = ENNReal.ofReal (g x - g a) := fun x => by
    change stieltjesMeasure (cdfReal_pow_monotone F k) (Ioc a x) = _
    rw [stieltjesMeasure_cdfReal_pow_Ioc hF_atomless]
  -- Step 3: extract ψ' as a continuous function via C¹.
  have h_ψ_diff : ∀ x, HasDerivAt ψ (deriv ψ x) x := fun x =>
    (hψ_C1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have h_ψ'_cont : Continuous (deriv ψ) := hψ_C1.continuous_deriv le_rfl
  have h_ψ_cont : Continuous ψ := hψ_C1.continuous
  -- Step 4: FTC for ψ on (a, x) with a ≤ x.
  have h_FTC : ∀ x, a ≤ x → ψ x - ψ a = ∫ t in Ioc a x, deriv ψ t := fun x hax => by
    rw [show (∫ t in Ioc a x, deriv ψ t) = ∫ t in (a : ℝ)..x, deriv ψ t from
      (intervalIntegral.integral_of_le hax).symm]
    linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := x)
      (fun y _ => h_ψ_diff y) (h_ψ'_cont.intervalIntegrable a x)]
  -- Step 5: Decompose the LHS integral.
  -- ∫_{Ioc a b} ψ'(x) g(x) dx = ∫_{Ioc a b} ψ'(x) (g(a) + (g(x) - g(a))) dx
  --                           = g(a) (ψ(b) - ψ(a)) + ∫_{Ioc a b} ψ'(x) (g(x) - g(a)) dx
  have h_int_ψ'g_split :
      ∫ x in Ioc a b, deriv ψ x * g x =
        g a * (ψ b - ψ a) + ∫ x in Ioc a b, deriv ψ x * (g x - g a) := by
    have h_const_int : ∫ x in Ioc a b, deriv ψ x * g a =
        g a * (ψ b - ψ a) := by
      rw [show (fun x => deriv ψ x * g a) = (fun x => g a * deriv ψ x) by
        funext x; ring]
      rw [integral_const_mul, h_FTC b hab]
    rw [show (fun x => deriv ψ x * g x) =
        fun x => deriv ψ x * g a + deriv ψ x * (g x - g a) by
      funext x; ring]
    rw [integral_add ?_ ?_]
    · rw [h_const_int]
    · -- integrability of deriv ψ x * g a
      exact (h_ψ'_cont.mul continuous_const).integrableOn_Ioc.mono_set Subset.rfl
    · -- integrability of deriv ψ x * (g x - g a)
      exact ((h_ψ'_cont.mul (h_g_cont.sub continuous_const))).integrableOn_Ioc.mono_set Subset.rfl
  -- Step 6: Compute the cross term ∫_{Ioc a b} ψ'(x) (g(x) - g(a)) dx via Fubini.
  -- Express g(x) - g(a) as μ_g (Ioc a x).toReal, then Fubini on the triangle.
  have h_cross : ∫ x in Ioc a b, deriv ψ x * (g x - g a) =
      ψ b * (g b - g a) - ∫ t in Ioc a b, ψ t ∂μ_g := by
    -- Setup the triangle T = {(t,x) | a < t ≤ x ≤ b} and Fubini against volume × μ_g.
    set T : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
    have hT_meas : MeasurableSet T :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const))
    -- The integrand on T: deriv ψ (snd).
    -- Compute the two iterated integrals:
    -- Order (x outer, t inner):
    --   ∫_{x ∈ Ioc a b} deriv ψ x * μ_g(Ioc a x).toReal dx
    -- Order (t outer, x inner):
    --   ∫_{t ∈ Ioc a b} (ψ b - ψ t) dμ_g(t)
    -- Sections of T.
    have sect_x : ∀ x, Prod.mk x ⁻¹' (Prod.swap ⁻¹' T) =
        if x ∈ Ioc a b then Ioc a x else ∅ := by
      intro x; ext t; simp only [T, mem_preimage, Prod.swap, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨hat, htx, _⟩ => ⟨hat, htx⟩, fun ⟨hat, htx⟩ => ⟨hat, htx, h.2⟩⟩
      · next h => exact ⟨fun ⟨hat, htx, hxb⟩ =>
          absurd ⟨lt_of_lt_of_le hat htx, hxb⟩ h, False.elim⟩
    have sect_t : ∀ t, Prod.mk t ⁻¹' T =
        if t ∈ Ioc a b then Icc t b else ∅ := by
      intro t; ext x; simp only [T, mem_preimage, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨_, htx, hxb⟩ => ⟨htx, hxb⟩, fun ⟨htx, hxb⟩ => ⟨h.1, htx, hxb⟩⟩
      · next h => exact ⟨fun ⟨hat, htx, hxb⟩ =>
          absurd ⟨hat, le_trans htx hxb⟩ h, False.elim⟩
    -- Bound |deriv ψ| on [a, b].
    obtain ⟨M, hM⟩ := ((isCompact_Icc).image h_ψ'_cont.norm).bddAbove
    have h_ψ'_bdd : ∀ x ∈ Icc a b, ‖deriv ψ x‖ ≤ M := fun x hx =>
      hM (Set.mem_image_of_mem _ hx)
    -- Bound |ψ| on [a, b].
    obtain ⟨Nψ, hNψ⟩ := ((isCompact_Icc).image h_ψ_cont.norm).bddAbove
    have h_ψ_bdd : ∀ x ∈ Icc a b, ‖ψ x‖ ≤ Nψ := fun x hx =>
      hNψ (Set.mem_image_of_mem _ hx)
    -- Finite measure of Ioc a b under both measures.
    have h_volIoc_lt_top : volume (Ioc a b) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have h_μgIoc_lt_top : μ_g (Ioc a b) < ⊤ := by
      rw [h_μg_Ioc]; exact ENNReal.ofReal_lt_top
    -- Define the indicator integrand f t x = 𝟙[T](t, x) * deriv ψ x.
    let f : ℝ → ℝ → ℝ := fun t x => T.indicator (fun p : ℝ × ℝ => deriv ψ p.2) (t, x)
    have h_uncurry_f : Function.uncurry f = T.indicator (fun p : ℝ × ℝ => deriv ψ p.2) := by
      funext p; cases p with | mk t x => simp [f, Function.uncurry]
    -- Restrictions: we work with μ_g ⊗ volume both restricted to Ioc a b.
    -- For integrability we need IsFiniteMeasure of these restrictions.
    haveI : IsFiniteMeasure (μ_g.restrict (Ioc a b)) := by
      refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact h_μgIoc_lt_top
    haveI : IsFiniteMeasure (volume.restrict (Ioc a b) : Measure ℝ) := by
      refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact h_volIoc_lt_top
    have h_f_int : Integrable (Function.uncurry f)
        ((μ_g.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
      rw [h_uncurry_f]
      refine Integrable.mono' (g := fun _ => M) (integrable_const _) ?_ ?_
      · refine (Measurable.indicator ?_ hT_meas).aestronglyMeasurable
        exact h_ψ'_cont.measurable.comp measurable_snd
      · refine ae_of_all _ fun p => ?_
        by_cases h_in : p ∈ T
        · rw [Set.indicator_of_mem h_in]
          exact h_ψ'_bdd p.2 ⟨le_trans (le_of_lt h_in.1) h_in.2.1, h_in.2.2⟩
        · rw [Set.indicator_of_notMem h_in]
          have h_a_in : a ∈ Icc a b := ⟨le_refl _, hab⟩
          simpa using le_trans (norm_nonneg _) (h_ψ'_bdd a h_a_in)
    -- Apply Fubini.
    have h_swap := MeasureTheory.integral_integral_swap (f := f) h_f_int
    -- Compute the two iterated integrals.
    -- For ∫ x ∂vol, ∫ t ∂μ_g: f(t, x) restricted to t ∈ Ioc a x gives deriv ψ x.
    -- For ∫ t ∂μ_g, ∫ x ∂vol: f(t, x) restricted to x ∈ Icc t b gives deriv ψ x.
    have h_LHS_inner : ∀ t ∈ Ioc a b,
        (∫ x in Ioc a b, f t x) = ψ b - ψ t := by
      intro t ht
      -- f t x = T.indicator (deriv ψ ∘ snd) (t, x)
      -- (t, x) ∈ T iff (since a < t already) t ≤ x ≤ b. So for t ∈ Ioc a b, the integrand
      -- f t x = deriv ψ x * 𝟙[Icc t b](x).
      have h_int_decomp : (fun x => f t x) =
          (Icc t b).indicator (fun x => deriv ψ x) := by
        funext x
        simp only [f, Set.indicator]
        by_cases h_in : (t, x) ∈ T
        · have : x ∈ Icc t b := ⟨h_in.2.1, h_in.2.2⟩
          simp [this, h_in]
        · have : x ∉ Icc t b := by
            simp only [mem_Icc, not_and] at *
            -- if x < t this is vacuous; if x ≥ t and x ≤ b, then (t,x) ∈ T (since a < t).
            intro htx hxb
            exact absurd ⟨ht.1, htx, hxb⟩ h_in
          simp [this, h_in]
      rw [h_int_decomp, setIntegral_indicator measurableSet_Icc]
      rw [show Ioc a b ∩ Icc t b = Icc t b by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Icc]
        refine ⟨fun h => h.2, fun h => ⟨⟨lt_of_lt_of_le ht.1 h.1, h.2⟩, h⟩⟩]
      rw [setIntegral_congr_set Ioc_ae_eq_Icc.symm]
      rw [show (∫ x in Ioc t b, deriv ψ x) = ∫ x in t..b, deriv ψ x from
        (intervalIntegral.integral_of_le ht.2).symm]
      linarith [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := t) (b := b)
        (fun y _ => h_ψ_diff y) (h_ψ'_cont.intervalIntegrable t b)]
    have h_RHS_inner : ∀ x ∈ Ioc a b,
        (∫ t in Ioc a b, f t x ∂μ_g) = deriv ψ x * (g x - g a) := by
      intro x hx
      have h_int_decomp : (fun t => f t x) =
          (Ioc a x).indicator (fun _ => deriv ψ x) := by
        funext t
        simp only [f, Set.indicator]
        by_cases h_in : (t, x) ∈ T
        · have : t ∈ Ioc a x := ⟨h_in.1, h_in.2.1⟩
          simp [this, h_in]
        · have : t ∉ Ioc a x := by
            simp only [mem_Ioc, not_and] at *
            intro hat htx
            exact absurd ⟨hat, htx, hx.2⟩ h_in
          simp [this, h_in]
      rw [h_int_decomp, setIntegral_indicator measurableSet_Ioc]
      rw [show Ioc a b ∩ Ioc a x = Ioc a x by
        ext y; simp only [mem_inter_iff, mem_Ioc]
        refine ⟨fun h => h.2, fun h => ⟨⟨h.1, le_trans h.2 hx.2⟩, h⟩⟩]
      rw [setIntegral_const, smul_eq_mul, measureReal_def, h_μg_Ioc x,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hg_mono hx.1.le))]
      ring
    -- Apply Fubini and conclude.
    have h_LHS_swap_eq :
        (∫ t in Ioc a b, (∫ x in Ioc a b, f t x) ∂μ_g) =
        ∫ t in Ioc a b, (ψ b - ψ t) ∂μ_g :=
      setIntegral_congr_fun measurableSet_Ioc h_LHS_inner
    have h_RHS_swap_eq :
        (∫ x in Ioc a b, (∫ t in Ioc a b, f t x ∂μ_g)) =
        ∫ x in Ioc a b, deriv ψ x * (g x - g a) :=
      setIntegral_congr_fun measurableSet_Ioc h_RHS_inner
    -- ∫ (ψb - ψt) dμ_g = ψb * μ_g(Ioc a b).toReal - ∫ ψ dμ_g
    have h_int_const : IntegrableOn (fun _ : ℝ => ψ b) (Ioc a b) μ_g :=
      integrableOn_const h_μgIoc_lt_top.ne
    have h_int_ψ : IntegrableOn ψ (Ioc a b) μ_g := by
      refine Measure.integrableOn_of_bounded (M := Nψ) h_μgIoc_lt_top.ne
        h_ψ_cont.measurable.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
      exact h_ψ_bdd x ⟨hx.1.le, hx.2⟩
    have h_const_sub : ∫ t in Ioc a b, (ψ b - ψ t) ∂μ_g =
        ψ b * (g b - g a) - ∫ t in Ioc a b, ψ t ∂μ_g := by
      rw [integral_sub h_int_const h_int_ψ]
      rw [setIntegral_const, smul_eq_mul, measureReal_def, h_μg_Ioc b,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (hg_mono hab))]
      ring
    -- Conclude.
    rw [← h_RHS_swap_eq, ← h_swap, h_LHS_swap_eq, h_const_sub]
  -- Step 7: Combine.
  rw [h_int_ψ'g_split, h_cross]
  -- Now: g a * (ψ b - ψ a) + (ψ b * (g b - g a) - ∫ ψ dμ_g)
  --     = ψ b * g b - ψ a * g a - ∫ ψ dμ_g
  --     = ψ b * g b - ψ a * g a - k * ∫ ψ * F^(k-1) dF
  -- Apply Layer 1 to ∫ ψ dμ_g.
  have h_Layer1 : ∫ t in Ioc a b, ψ t ∂μ_g =
      (k : ℝ) * ∫ x in Ioc a b, ψ x * (cdfReal F x) ^ (k - 1) ∂(F : Measure ℝ) :=
    stieltjes_pow_cdf_eq_pow_smul_F hF_atomless k hab h_ψ_cont.continuousOn
  rw [h_Layer1]
  ring

end Econlib.Probability
