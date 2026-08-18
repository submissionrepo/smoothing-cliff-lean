/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.FTC
public import Econlib.Math.MeasureTheory.IntegralAsymp
public import Econlib.Math.Order.Intervals
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ProbDist.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.CDF

/-!
# `CDF` — a probability cumulative distribution function on `ℝ`

A `CDF` is a `StieltjesFunction` (monotone, right-continuous) that additionally tends to `0` at
`-∞` and `1` at `+∞`. It is a thin extension of Mathlib's `StieltjesFunction`, so it inherits the
`FunLike` coercion and the `.measure` API, and bridges to `ProbabilityTheory.cdf` via
`CDF.ofMeasure`/`ofProbDist` and `cdf_measure`.

This file also relates a `ContDist` to its CDF: `ContDist.cdf` integrates the density, `CDF.toDist`
differentiates a CDF back into a density, and `ContDist.prob_interval` computes interval
probabilities `P(a ≤ X ≤ b)`.

## Main definitions

* `CDF` — a Stieltjes function tending to `0` at `-∞` and `1` at `+∞`.
* `CDF.ofMeasure`, `CDF.ofProbDist` — the CDF of a probability measure / real law.
* `CDF.toDist` — build a `ContDist` from a differentiable CDF using its derivative as density.
* `ContDist.cdf` — the CDF `F(x) = ∫_{-∞}^x density` of a continuous distribution.
* `ContDist.prob_interval` — closed-interval probability `P(a ≤ X ≤ b) = ∫ x in Icc a b, density x`
  (a probability in `[0,1]`; equals `cdf b - cdf a` when `a ≤ b`).

## Main statements

* `ContDist.cdf_continuous` — the CDF of a continuous distribution is continuous.
* `ContDist.deriv_cdf_eq_density` — the CDF differentiates back to the density.
* `ContDist.cdf_strictMono` — the CDF is strictly increasing where the density is positive.

## Tags

cumulative distribution function, cdf, stieltjes, interval probability
-/

@[expose] public section

open Filter Topology Set MeasureTheory ProbabilityTheory

namespace Econlib.Probability

/-- A cumulative distribution function: A Stieltjes function tending to `0` at `-∞` and `1` at
`+∞`. -/
structure CDF extends StieltjesFunction ℝ where
  /-- The CDF tends to zero at `-∞`. -/
  tendsto_bot : Tendsto toFun atBot (𝓝 0)
  /-- The CDF tends to one at `+∞`. -/
  tendsto_top : Tendsto toFun atTop (𝓝 1)

namespace CDF

instance instFunLike : FunLike CDF ℝ ℝ where
  coe F := F.toStieltjesFunction
  coe_injective' F G h := by
    cases F; cases G
    simp only [mk.injEq]
    exact StieltjesFunction.ext (fun x => congrFun h x)

@[simp] lemma coe_toStieltjesFunction (F : CDF) : ⇑F.toStieltjesFunction = ⇑F := rfl

/-- A CDF is monotone. -/
lemma mono (F : CDF) : Monotone ⇑F := F.toStieltjesFunction.mono'

/-- A CDF is right-continuous. -/
lemma right_continuous (F : CDF) (x : ℝ) : ContinuousWithinAt (⇑F) (Ici x) x :=
  F.toStieltjesFunction.right_continuous' x

@[ext] lemma ext {F G : CDF} (h : ∀ x, F x = G x) : F = G := DFunLike.coe_injective (funext h)

/-- A CDF takes values in `[0, 1]`. -/
lemma range (F : CDF) (x : ℝ) : 0 ≤ F x ∧ F x ≤ 1 :=
  ⟨F.mono.le_of_tendsto F.tendsto_bot x, F.mono.ge_of_tendsto F.tendsto_top x⟩

/-- The probability measure associated to a CDF. -/
noncomputable def measure (F : CDF) : Measure ℝ := F.toStieltjesFunction.measure

instance instIsProbabilityMeasure (F : CDF) : IsProbabilityMeasure F.measure := by
  refine ⟨?_⟩
  rw [measure, StieltjesFunction.measure_univ _ F.tendsto_bot F.tendsto_top]
  simp

/-- The CDF of a probability measure. -/
noncomputable def ofMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] : CDF where
  toStieltjesFunction := cdf μ
  tendsto_bot := tendsto_cdf_atBot μ
  tendsto_top := tendsto_cdf_atTop μ

/-- The CDF of a real probability law. -/
noncomputable def ofProbDist (d : ProbDist ℝ) : CDF := ofMeasure d.toMeasure

@[simp] lemma ofProbDist_apply (d : ProbDist ℝ) (x : ℝ) :
    ofProbDist d x = cdf d.toMeasure x := rfl

/-- `ProbabilityTheory.cdf` of a `CDF`'s measure recovers the underlying Stieltjes function. -/
lemma cdf_measure (F : CDF) : cdf F.measure = F.toStieltjesFunction :=
  cdf_measure_stieltjesFunction _ F.tendsto_bot F.tendsto_top

/-- Construct `ContDist` from a differentiable CDF. -/
noncomputable def toDist (F : CDF) (deriv : ℝ → ℝ)
  (h_deriv : ∀ x, HasDerivAt (⇑F) (deriv x) x) : ContDist where
  density := deriv
  nonneg := fun x => (h_deriv x).nonneg_of_monotone F.mono
  integrable := by
    -- Split ℝ = Iic 0 ∪ Ioi 0 and show integrability on each half via FTC
    have h_nn : ∀ x, 0 ≤ deriv x := fun x => (h_deriv x).nonneg_of_monotone F.mono
    have h_Ioi : IntegrableOn deriv (Ioi 0) := integrableOn_Ioi_deriv_of_nonneg'
      (fun x _ => h_deriv x) (fun x _ => h_nn x) F.tendsto_top
    have h_Iic : IntegrableOn deriv (Iic 0) := integrableOn_Iic_deriv_of_nonneg'
      (fun x _ => h_deriv x) (fun x _ => h_nn x) F.tendsto_bot
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact h_Iic.union h_Ioi
  integral_one := by
    -- ∫ deriv = ∫_{Iic 0} deriv + ∫_{Ioi 0} deriv = (F(0) - 0) + (1 - F(0)) = 1
    have h_nn : ∀ x, 0 ≤ deriv x := fun x => (h_deriv x).nonneg_of_monotone F.mono
    have h_Iic : IntegrableOn deriv (Iic 0) := integrableOn_Iic_deriv_of_nonneg'
      (fun x _ => h_deriv x) (fun x _ => h_nn x) F.tendsto_bot
    have h_int : Integrable deriv := by
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
      exact h_Iic.union (integrableOn_Ioi_deriv_of_nonneg'
        (fun x _ => h_deriv x) (fun x _ => h_nn x) F.tendsto_top)
    have h_split := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic h_int
    rw [compl_Iic] at h_split
    have h_val_Iic := integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun x _ => h_deriv x) h_Iic F.tendsto_bot
    have h_val_Ioi := integral_Ioi_of_hasDerivAt_of_nonneg' (a := (0 : ℝ))
      (fun x _ => h_deriv x) (fun x _ => h_nn x) F.tendsto_top
    linarith

end CDF

namespace ContDist

/-- The integral-of-density primitive `x ↦ ∫_{Iic x} density` is monotone: Enlarging the
integration set integrates a nonnegative function over a larger region. -/
lemma cdf_primitive_mono (d : ContDist) :
    Monotone (fun x : ℝ => ∫ t in Iic x, d.density t) := fun _ _ hxy =>
  setIntegral_mono_set d.integrable.integrableOn
    (ae_of_all _ d.nonneg) (Iic_subset_Iic.mpr hxy).eventuallyLE

/-- CDF derived from density by integration. -/
noncomputable def cdf (d : ContDist) : CDF where
  toStieltjesFunction :=
    { toFun := fun x => ∫ t in Iic x, d.density t
      mono' := cdf_primitive_mono d
      right_continuous' := fun x => tendsto_setIntegral_Iic_right d.integrable x }
  tendsto_bot := by
    set F := fun x : ℝ => ∫ t in Iic x, d.density t
    have hF_mono : Monotone F := cdf_primitive_mono d
    have hF_nonneg : ∀ x, 0 ≤ F x :=
      fun x => setIntegral_nonneg measurableSet_Iic (fun t _ => d.nonneg t)
    have h_nat : Tendsto (fun n : ℕ => F (-(n : ℝ))) atTop (𝓝 0) := by
      have := Antitone.tendsto_setIntegral (fun n => measurableSet_Iic)
        (fun n m (hnm : n ≤ m) => Iic_subset_Iic.mpr (neg_le_neg_iff.mpr (Nat.cast_le.mpr hnm)))
        d.integrable.integrableOn
      rwa [iInter_Iic_neg_nat_eq_empty, setIntegral_empty] at this
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    rw [NormedAddGroup.tendsto_nhds_zero] at h_nat
    obtain ⟨N, hN⟩ := (h_nat ε hε).exists_forall_of_atTop
    filter_upwards [eventually_le_atBot (-(N : ℝ))] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg x)]
    calc F x ≤ F (-(N : ℝ)) := hF_mono hx
      _ = ‖F (-(N : ℝ))‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg _)]
      _ < ε := hN N le_rfl
  tendsto_top := by
    set F := fun x : ℝ => ∫ t in Iic x, d.density t
    have hF_mono : Monotone F := cdf_primitive_mono d
    rw [tendsto_iff_tendsto_subseq_of_monotone hF_mono tendsto_natCast_atTop_atTop]
    rw [← d.integral_one, ← setIntegral_univ]
    have h_union : ⋃ n : ℕ, Iic (n : ℝ) = univ := by ext x; simp [exists_nat_ge x]
    rw [← h_union]
    apply tendsto_setIntegral_of_monotone
    · intro n; exact measurableSet_Iic
    · intro n m hnm; exact Iic_subset_Iic.mpr (Nat.cast_le.mpr hnm)
    · rw [h_union]; exact d.integrable.integrableOn

/-- The CDF unfolds to the integral of the density over `Iic x`. -/
lemma cdf_eq_integral (d : ContDist) (x : ℝ) :
    d.cdf x = ∫ t in Iic x, d.density t := rfl

/-- The CDF splits as the constant tail `∫_{Iic 0}` plus the interval primitive `∫_0^x`:
`F(x) = F(0) + ∫_0^x density`. -/
lemma cdf_eq_const_add_intervalIntegral (d : ContDist) (x : ℝ) :
    d.cdf x = (∫ t in Iic (0 : ℝ), d.density t) + ∫ t in (0 : ℝ)..x, d.density t := by
  simp only [cdf_eq_integral]
  linarith [intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := x)
    d.integrable.integrableOn d.integrable.integrableOn]

/-- The CDF of a continuous distribution is nonnegative. -/
lemma cdf_nonneg (d : ContDist) (x : ℝ) : 0 ≤ d.cdf x :=
  (d.cdf.range x).1

/-- The CDF of a continuous distribution is at most one. -/
lemma cdf_le_one (d : ContDist) (x : ℝ) : d.cdf x ≤ 1 :=
  (d.cdf.range x).2

/-- The CDF of a continuous distribution is continuous, not just right-continuous. -/
lemma cdf_continuous (d : ContDist) : Continuous (⇑d.cdf) := by
  simp_rw [funext (d.cdf_eq_const_add_intervalIntegral)]
  exact continuous_const.add (d.integrable.continuous_primitive 0)

/-- Where the density is continuous, the CDF differentiates back to the density (FTC). -/
lemma deriv_cdf_eq_density (d : ContDist) (x : ℝ) (h_cont : ContinuousAt d.density x) :
    HasDerivAt (⇑d.cdf) (d.density x) x := by
  -- CDF = C + ∫_0^x density, so CDF'(x) = density(x) by FTC
  rw [funext (d.cdf_eq_const_add_intervalIntegral)]
  -- FTC: d/dx ∫_0^x density = density(x)
  exact (intervalIntegral.integral_hasDerivAt_right
    d.integrable.intervalIntegrable
    d.integrable.aestronglyMeasurable.stronglyMeasurableAtFilter
    h_cont).const_add _

/-- If the density vanishes on `(-∞, x]`, then `CDF(x) = 0`. -/
lemma cdf_eq_zero_of_density_zero_left (d : ContDist) {x : ℝ}
    (h : ∀ t, t ≤ x → d.density t = 0) : d.cdf x = 0 := by
  simp only [cdf_eq_integral]
  exact setIntegral_eq_zero_of_forall_eq_zero (fun t ht => h t (mem_Iic.mp ht))

/-- If the density vanishes on `(x, ∞)`, then `CDF(x) = 1`. -/
lemma cdf_eq_one_of_density_zero_right (d : ContDist) {x : ℝ}
    (h : ∀ t, x < t → d.density t = 0) : d.cdf x = 1 := by
  have h_split := integral_add_compl (s := Iic x) measurableSet_Iic d.integrable
  rw [compl_Iic] at h_split
  have h_tail : ∫ t in Ioi x, d.density t = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht => h t (mem_Ioi.mp ht))
  simp only [cdf_eq_integral]
  linarith [d.integral_one]

/-- If the density vanishes outside `[a, b]` and `x < a`, then `CDF(x) = 0`. -/
lemma cdf_eq_zero_of_supportsOn_Icc_left (d : ContDist) {a b : ℝ}
    (h_zero : ∀ t, t ∉ Icc a b → d.density t = 0) {x : ℝ} (hx : x < a) :
    d.cdf x = 0 :=
  d.cdf_eq_zero_of_density_zero_left (fun t ht =>
    h_zero t (fun hmem => by linarith [hmem.1]))

/-- If the density vanishes outside `[a, b]` and `b ≤ x`, then `CDF(x) = 1`. -/
lemma cdf_eq_one_of_supportsOn_Icc_right (d : ContDist) {a b : ℝ}
    (h_zero : ∀ t, t ∉ Icc a b → d.density t = 0) {x : ℝ} (hx : b ≤ x) :
    d.cdf x = 1 :=
  d.cdf_eq_one_of_density_zero_right (fun t ht =>
    h_zero t (fun hmem => by linarith [hmem.2]))

/-- The probability the variable lands in the closed interval `[a, b]`:
`P(a ≤ X ≤ b) = ∫ x in Icc a b, d.density x`. This is a probability in `[0, 1]` for all `a, b`
(`prob_interval_nonneg`, `prob_interval_le_one`); when `a > b` the event `{a ≤ X ≤ b}` is empty and
the value is `0`. It equals the signed CDF increment `d.cdf b - d.cdf a` exactly when `a ≤ b`
(`prob_interval_eq_of_le`); for `a > b` that increment is negative and is not the interval
probability, so the oriented integral `∫ x in a..b` must not be conflated with this quantity. -/
noncomputable def prob_interval (d : ContDist) (a b : ℝ) : ℝ :=
  ∫ x in Set.Icc a b, d.density x

/-- On `a ≤ b` the interval probability is the CDF increment `d.cdf b - d.cdf a`. (For `a > b` the
event `{a ≤ X ≤ b}` is empty, so `prob_interval = 0`, which differs from the negative increment.) -/
lemma prob_interval_eq_of_le (d : ContDist) {a b : ℝ} (h : a ≤ b) :
    d.prob_interval a b = d.cdf b - d.cdf a := by
  rw [prob_interval, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
  simp only [cdf_eq_integral]
  rw [← intervalIntegral.integral_Iic_sub_Iic d.integrable.integrableOn d.integrable.integrableOn]

/-- A degenerate interval carries no probability: `P(a ≤ X ≤ a) = 0` (the density is atomless). -/
@[simp] lemma prob_interval_self (d : ContDist) (a : ℝ) : d.prob_interval a a = 0 := by
  rw [d.prob_interval_eq_of_le le_rfl, sub_self]

/-- The interval probability is nonnegative. -/
lemma prob_interval_nonneg (d : ContDist) (a b : ℝ) :
    0 ≤ d.prob_interval a b :=
  setIntegral_nonneg measurableSet_Icc (fun x _ => d.nonneg x)

/-- The interval probability is at most one. -/
lemma prob_interval_le_one (d : ContDist) (a b : ℝ) :
    d.prob_interval a b ≤ 1 := by
  rw [prob_interval, ← d.integral_one]
  exact setIntegral_le_integral d.integrable (ae_of_all _ d.nonneg)

/-- The CDF is strictly monotone on an interval where the density is continuous and positive: If
`a < b` and `density > 0` on `[a, b]`, then `F(a) < F(b)`. -/
lemma cdf_strictMono (d : ContDist) {a b : ℝ} (hab : a < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (_hd_cont : ContinuousOn d.density (Icc a b)) :
    d.cdf a < d.cdf b := by
  have h_pos : 0 < d.prob_interval a b := by
    rw [prob_interval, integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_ae (ae_of_all _ d.nonneg)) d.integrable.integrableOn]
    calc 0 < volume (Ioo a b) := by
          rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (by linarith)
      _ ≤ volume (Function.support d.density ∩ Ioo a b) :=
          measure_mono (fun x hx => ⟨Function.mem_support.mpr
            (ne_of_gt (hd_pos x (Ioo_subset_Icc_self hx))), hx⟩)
  linarith [d.prob_interval_eq_of_le hab.le]

/-- If the density is strictly positive on the open support interval `Ioo a b` and continuous on
the closed support interval `Icc a b`, then the CDF is strictly positive at every interior point. -/
lemma cdf_pos_of_mem_Ioo_support (d : ContDist) {a b x : ℝ}
    (hx : x ∈ Ioo a b)
    (hd_pos : ∀ y ∈ Ioo a b, 0 < d.density y)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    0 < d.cdf x := by
  set m : ℝ := (a + x) / 2 with hm_def
  have ham : a < m := by simp only [hm_def]; linarith [hx.1]
  have hmx : m < x := by simp only [hm_def]; linarith [hx.1]
  have hsub_Ioo : Icc m x ⊆ Ioo a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le ham hy.1, lt_of_le_of_lt hy.2 hx.2⟩
  have hsub_Icc : Icc m x ⊆ Icc a b := by
    intro y hy
    exact ⟨le_of_lt (lt_of_lt_of_le ham hy.1), le_of_lt (lt_of_le_of_lt hy.2 hx.2)⟩
  have hd_pos_local : ∀ y ∈ Icc m x, 0 < d.density y :=
    fun y hy => hd_pos y (hsub_Ioo hy)
  have hd_cont_local : ContinuousOn d.density (Icc m x) := hd_cont.mono hsub_Icc
  have hstrict : d.cdf m < d.cdf x := d.cdf_strictMono hmx hd_pos_local hd_cont_local
  exact lt_of_le_of_lt (d.cdf_nonneg m) hstrict

/-- The interval probability is strictly positive when the density is continuous and positive on
`[a, b]` with `a < b`. -/
lemma prob_interval_pos_of_pos_density (d : ContDist) {a b : ℝ} (hab : a < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    0 < d.prob_interval a b := by
  rw [d.prob_interval_eq_of_le hab.le]
  have hcdf : d.cdf a < d.cdf b := d.cdf_strictMono hab hd_pos hd_cont
  linarith

end ContDist

end Econlib.Probability
