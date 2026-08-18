/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Myerson ironing on an irregular environment (worked example)

A concrete **irregular** single-parameter screening environment where Myerson's ironing is *active*:
The raw virtual value `ψ` is non-monotone, the convex-envelope step changes the virtual
value (`ψ̄ ≠ ψ` on an ironed region), and the cumulative ironing gap is nonzero — the foil to the
regular uniform benchmark of `MyersonReserveUniform`, where `ψ̄ = ψ` and every ironing identity is
vacuous.

## The environment

Types are drawn on `[0, 3]` from the **decreasing** density

  `f(θ) = (1 + 8θ)^{-1/2}`,    `∫₀³ f = ¼(√25 − √1) = 1`.

Its CDF and quantile are closed-form rationals-under-a-root:

  `F(θ) = (√(1 + 8θ) − 1) / 4`,    `F⁻¹(q) = 2q² + q`     (since `1 + 8(2q² + q) = (4q + 1)²`).

Pulling the virtual value back to quantile space gives a **parabola**

  `h(q) = ψ(F⁻¹ q) = 6q² − 2q − 1`,

which *decreases* on `[0, 1/6]`: the environment is irregular (`¬ Regular`). Its primitive is the
cubic `H(q) = ∫₀^q h = 2q³ − q² − q`, and the algebraic identity

  `H(q) + 9q/8 = 2q (q − 1/4)²  ≥ 0  on [0, 1]`

exhibits the line `ℓ(q) = −9q/8` as a global affine **minorant** of `H` touching it exactly at
`q = 0` and `q = 1/4` (a double root). Hence on the **ironed interval** `[0, 1/4]` the convex hull
`Ĥ` coincides with `ℓ`, so the ironed virtual value is the constant

  `ĥ(q) = Ĥ'₊(q) = −9/8`    for `q ∈ (0, 1/4)`,

the low types are *bunched*. Away from the chord (`q > 1/4`) `H` is convex and `Ĥ = H`, so `ĥ = h`.

## What this catches (the ironing gap is real, not vacuous)

* `irrScreening_not_regular` — `ψ` is **non-monotone**: ironing is needed.
* `ironedVVQuantile_eq_ironed` / `ironedVVQuantile_ne_vvQuantile_witness` — on the ironed region
  `ψ̄_q = −9/8 ≠ h(q)`: the convex envelope **changes** the virtual value (`ψ̄ ≠ ψ`), unlike the
  uniform case where both sides agree.
* `integral_ironedVVQuantile_sub_vvQuantile_nonzero` — the cumulative gap
  `∫₀^{1/8} (ĥ − h) = Ĥ(1/8) − H(1/8) = −1/256 ≠ 0`: a sign/order error in the gap is now visible
  (on the uniform environment both sides vanish).
* `expected_rawSurplus_eq_ironedSurplus_ironedAlloc` (re-anchored) — the complementary-slackness
  identity `𝔼[ψ·x̄] = 𝔼[ψ̄·x̄]` for the ironed allocation is a contact-set cancellation
  here, not the pointwise `ψ̄ = ψ` collapse of the regular case.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.MyersonIroning

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.Probability
open Set MeasureTheory

/-! ## Block 1: The irregular distribution `f(θ) = (1 + 8θ)^{-1/2}` on `[0, 3]` -/

/-- The density `(1 + 8x)^{-1/2}` on `[0, 3]`, zero outside. -/
private def irrDensityFun (x : ℝ) : ℝ := if x ∈ Icc (0 : ℝ) 3 then (Real.sqrt (1 + 8 * x))⁻¹ else 0

/-- On `[0, 3]` the radicand `1 + 8x` is at least `1`, hence positive. -/
private lemma irr_radicand_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 3) : 0 < 1 + 8 * x := by
  have := hx.1; linarith

/-- The density as an indicator, for measure manipulations. -/
private lemma irrDensityFun_indicator :
    irrDensityFun = (Icc (0 : ℝ) 3).indicator (fun x => (Real.sqrt (1 + 8 * x))⁻¹) := by
  ext x; simp [irrDensityFun, Set.indicator_apply]

/-- The density is continuous on the support interval `[0, 3]`. -/
private lemma irr_density_continuousOn :
    ContinuousOn (fun x => (Real.sqrt (1 + 8 * x))⁻¹) (Icc (0 : ℝ) 3) := by
  refine ContinuousOn.inv₀ ?_ (fun x hx => ?_)
  · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).sqrt
  · exact ne_of_gt (Real.sqrt_pos.mpr (irr_radicand_pos hx))

/-- The density function is interval-integrable on any `[0, x] ⊆ [0, 3]`. -/
private lemma irr_density_intervalIntegrable {x : ℝ} (hx0 : 0 ≤ x) (hx3 : x ≤ 3) :
    IntervalIntegrable (fun t => (Real.sqrt (1 + 8 * t))⁻¹) volume 0 x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx0]
  exact irr_density_continuousOn.mono (Icc_subset_Icc le_rfl hx3)

/-- The antiderivative `√(1 + 8t)/4` differentiates back to the density wherever `1 + 8t > 0`. -/
private lemma irr_primitive_hasDerivAt {t : ℝ} (ht : 0 < 1 + 8 * t) :
    HasDerivAt (fun y => Real.sqrt (1 + 8 * y) / 4) ((Real.sqrt (1 + 8 * t))⁻¹) t := by
  have hlin : HasDerivAt (fun y : ℝ => 1 + 8 * y) 8 t := by
    simpa using ((hasDerivAt_id t).const_mul (8 : ℝ)).const_add (1 : ℝ)
  have hsqrt : HasDerivAt (fun y => Real.sqrt (1 + 8 * y)) (8 / (2 * Real.sqrt (1 + 8 * t))) t :=
    hlin.sqrt (ne_of_gt ht)
  have hsqrt_pos : 0 < Real.sqrt (1 + 8 * t) := Real.sqrt_pos.mpr ht
  convert hsqrt.div_const 4 using 1
  field_simp
  ring

/-- The **irregular type distribution**: density `(1 + 8x)^{-1/2}` on `[0, 3]`. -/
def irrDist : ContDist where
  density := irrDensityFun
  nonneg x := by
    rw [irrDensityFun]; split
    · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    · exact le_refl 0
  integrable := by
    rw [irrDensityFun_indicator]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (irr_density_continuousOn.integrableOn_compact isCompact_Icc)
  integral_one := by
    rw [irrDensityFun_indicator, integral_indicator measurableSet_Icc]
    rw [show (∫ x in Icc (0 : ℝ) 3, (Real.sqrt (1 + 8 * x))⁻¹)
        = ∫ x in (0 : ℝ)..3, (Real.sqrt (1 + 8 * x))⁻¹ from by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3)]
      exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => irr_primitive_hasDerivAt (by
        rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 3)] at ht; linarith [ht.1]))
      (irr_density_intervalIntegrable (by norm_num) (le_refl 3))]
    rw [show (1 : ℝ) + 8 * 3 = 25 by norm_num, show (1 : ℝ) + 8 * 0 = 1 by norm_num,
      show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_one]
    norm_num

@[simp] private lemma irr_density_eq (x : ℝ) :
    irrDist.density x = if x ∈ Icc (0 : ℝ) 3 then (Real.sqrt (1 + 8 * x))⁻¹ else 0 := rfl

/-- The density at a point of `[0, 3]`. -/
private lemma irr_density_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 3) :
    irrDist.density x = (Real.sqrt (1 + 8 * x))⁻¹ := by rw [irr_density_eq, if_pos hx]

private lemma irr_density_pos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 3) : 0 < irrDist.density x := by
  rw [irr_density_of_mem hx]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (irr_radicand_pos hx))

/-- `irrDist.density` (the `if`-guarded function) is continuous on `[0, 3]`. -/
private lemma irr_dist_density_continuousOn :
    ContinuousOn irrDist.density (Icc (0 : ℝ) 3) :=
  irr_density_continuousOn.congr (fun _ hx => irr_density_of_mem hx)

/-! ## Block 2: The CDF `F(θ) = (√(1 + 8θ) − 1)/4` and strict monotonicity -/

/-- The left tail `∫_{Iic 0} f` vanishes: the density is supported on `[0, 3]`. -/
private lemma irr_cdf_tail_zero : (∫ t in Iic (0 : ℝ), irrDist.density t) = 0 := by
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
    rw [ae_iff]; simp only [not_not]; exact measure_singleton 0
  refine integral_eq_zero_of_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
  filter_upwards [hne] with t htne ht
  simp only [Pi.zero_apply, irr_density_eq]
  rw [if_neg]; rintro ⟨h0, _⟩; exact htne (le_antisymm ht h0)

/-- **Closed-form CDF.** On `[0, 3]`, `F(θ) = (√(1 + 8θ) − 1)/4`. -/
lemma irr_cdf {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 3) :
    irrDist.cdf x = (Real.sqrt (1 + 8 * x) - 1) / 4 := by
  rw [irrDist.cdf_eq_const_add_intervalIntegral, irr_cdf_tail_zero, zero_add]
  rw [show (∫ t in (0 : ℝ)..x, irrDist.density t) = ∫ t in (0 : ℝ)..x, (Real.sqrt (1 + 8 * t))⁻¹
      from intervalIntegral.integral_congr (fun t ht => by
        rw [uIcc_of_le hx.1] at ht
        exact irr_density_of_mem ⟨ht.1, le_trans ht.2 hx.2⟩)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => irr_primitive_hasDerivAt (by rw [uIcc_of_le hx.1] at ht; linarith [ht.1]))
    (irr_density_intervalIntegrable hx.1 hx.2)]
  rw [show (1 : ℝ) + 8 * 0 = 1 by norm_num, Real.sqrt_one]; ring

/-- The CDF is strictly monotone on `[0, 3]` (the density is positive and continuous there). -/
private lemma irr_cdf_strictMonoOn : StrictMonoOn irrDist.cdf (Icc (0 : ℝ) 3) := by
  intro a ha b hb hab
  exact irrDist.cdf_strictMono hab
    (fun x hx => irr_density_pos ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩)
    (irr_dist_density_continuousOn.mono (Icc_subset_Icc ha.1 hb.2))

/-! ## Block 3: The screening environment -/

/-- The irregular screening environment on `[0, 3]`. -/
def irrScreening : ScreeningEnv where
  θlo := 0
  θhi := 3
  hθ := by norm_num
  dist := irrDist
  supp_subset x hx := by
    by_contra hmem
    rw [irr_density_eq, if_neg hmem] at hx
    exact lt_irrefl 0 hx
  density_pos x hx := irr_density_pos hx
  density_cont := irr_dist_density_continuousOn

@[simp] lemma irrScreening_θlo : irrScreening.θlo = 0 := rfl
@[simp] lemma irrScreening_θhi : irrScreening.θhi = 3 := rfl
@[simp] lemma irrScreening_dist : irrScreening.dist = irrDist := rfl

/-! ## Block 4: The quantile `F⁻¹(q) = 2q² + q` -/

/-- `2q² + q ∈ [0, 3]` for `q ∈ [0, 1]`. -/
private lemma quad_mem {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 2 * q ^ 2 + q ∈ Icc (0 : ℝ) 3 := by
  constructor
  · nlinarith [hq.1, sq_nonneg q]
  · nlinarith [hq.1, hq.2, sq_nonneg q]

/-- `F(2q² + q) = q`: the closed-form CDF inverts the quadratic quantile (since
`1 + 8(2q² + q) = (4q + 1)²`). -/
private lemma irr_cdf_quad {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    irrDist.cdf (2 * q ^ 2 + q) = q := by
  rw [irr_cdf (quad_mem hq)]
  rw [show 1 + 8 * (2 * q ^ 2 + q) = (4 * q + 1) ^ 2 by ring,
    Real.sqrt_sq (by linarith [hq.1] : (0 : ℝ) ≤ 4 * q + 1)]
  ring

/-- **The quantile function is `F⁻¹(q) = 2q² + q`** on `(0, 1)`. -/
lemma irr_quantileInv {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    irrScreening.quantileInv q = 2 * q ^ 2 + q := by
  have hmem : irrScreening.quantileInv q ∈ Icc (0 : ℝ) 3 := irrScreening.quantileInv_mem hq
  have hcdf : irrDist.cdf (irrScreening.quantileInv q) = q := irrScreening.dist.cdf_quantile hq
  have hcdf' : irrDist.cdf (2 * q ^ 2 + q) = q := irr_cdf_quad ⟨hq.1.le, hq.2.le⟩
  exact irr_cdf_strictMonoOn.injOn hmem (quad_mem ⟨hq.1.le, hq.2.le⟩) (hcdf.trans hcdf'.symm)

/-! ## Block 5: The pulled-back virtual value `h(q) = 6q² − 2q − 1`, primitive `H = 2q³ − q² − q` -/

/-- The density at the quadratic quantile: `f(2q² + q) = 1/(4q + 1)`. -/
private lemma irr_density_quad {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    irrDist.density (2 * q ^ 2 + q) = (4 * q + 1)⁻¹ := by
  rw [irr_density_of_mem (quad_mem ⟨hq.1.le, hq.2.le⟩),
    show 1 + 8 * (2 * q ^ 2 + q) = (4 * q + 1) ^ 2 by ring,
    Real.sqrt_sq (by linarith [hq.1] : (0 : ℝ) ≤ 4 * q + 1)]

/-- **The virtual value in quantile space is the parabola `h(q) = 6q² − 2q − 1`.** -/
lemma irr_vvQuantile {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    irrScreening.vvQuantile q = 6 * q ^ 2 - 2 * q - 1 := by
  rw [ScreeningEnv.vvQuantile_def, irr_quantileInv hq, ScreeningEnv.virtualValue_def,
    show irrScreening.dist = irrDist from rfl, irr_cdf_quad ⟨hq.1.le, hq.2.le⟩, irr_density_quad hq,
    div_eq_mul_inv, inv_inv]
  ring

/-- **The virtual value is non-monotone**, so the environment is irregular: `h` decreases on
`[0, 1/6]`. Concretely `h(1/12) = −9/8 > −7/6 = h(1/6)` at `1/12 < 1/6`. -/
theorem irr_vvQuantile_non_monotone :
    irrScreening.vvQuantile (1 / 12) = -(9 / 8) ∧ irrScreening.vvQuantile (1 / 6) = -(7 / 6) ∧
      irrScreening.vvQuantile (1 / 6) < irrScreening.vvQuantile (1 / 12) := by
  rw [irr_vvQuantile (by norm_num), irr_vvQuantile (by norm_num)]
  norm_num

/-- **The environment is irregular**: the virtual value is not monotone on the type interval.
`F⁻¹` is monotone and `ψ ∘ F⁻¹ = h` is non-monotone, so `ψ` itself reverses order. -/
theorem irrScreening_not_regular : ¬ irrScreening.Regular := by
  intro hreg
  -- `ψ(F⁻¹(1/12)) = h(1/12) = −9/8` and `ψ(F⁻¹(1/6)) = h(1/6) = −7/6`, with `F⁻¹(1/12) < F⁻¹(1/6)`.
  have hlt : irrScreening.quantileInv (1 / 12) < irrScreening.quantileInv (1 / 6) := by
    rw [irr_quantileInv (by norm_num), irr_quantileInv (by norm_num)]; norm_num
  have hmem1 : irrScreening.quantileInv (1 / 12) ∈ irrScreening.types :=
    irrScreening.quantileInv_mem (by norm_num)
  have hmem2 : irrScreening.quantileInv (1 / 6) ∈ irrScreening.types :=
    irrScreening.quantileInv_mem (by norm_num)
  have hmono := hreg hmem1 hmem2 hlt.le
  rw [← ScreeningEnv.vvQuantile_def, ← ScreeningEnv.vvQuantile_def,
    irr_vvQuantile (by norm_num), irr_vvQuantile (by norm_num)] at hmono
  norm_num at hmono

/-- **The primitive of the pulled-back virtual value is the cubic `H(q) = 2q³ − q² − q`** on
`[0, 1]`. -/
lemma irr_vvPrimitive {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    irrScreening.vvPrimitive q = 2 * q ^ 3 - q ^ 2 - q := by
  rw [ScreeningEnv.vvPrimitive_def]
  -- The integrand equals `6u² − 2u − 1` a.e. on `[0, q]` (interior of `(0, 1)`).
  have hcong : (∫ u in (0 : ℝ)..q, irrScreening.vvQuantile u)
      = ∫ u in (0 : ℝ)..q, (6 * u ^ 2 - 2 * u - 1) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hone : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (1 : ℝ) := by
      rw [ae_iff]; simp only [not_not]; exact measure_singleton 1
    filter_upwards [hone] with u hu1 huI
    rw [uIoc_of_le hq.1] at huI
    exact irr_vvQuantile ⟨huI.1, lt_of_le_of_ne (le_trans huI.2 hq.2) hu1⟩
  rw [hcong]
  have hderiv : ∀ u : ℝ, HasDerivAt (fun y => 2 * y ^ 3 - y ^ 2 - y) (6 * u ^ 2 - 2 * u - 1) u := by
    intro u
    have h1 : HasDerivAt (fun y : ℝ => 2 * y ^ 3) (2 * (3 * u ^ 2)) u :=
      (hasDerivAt_pow 3 u).const_mul 2
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u ^ 1) u := hasDerivAt_pow 2 u
    have h3 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) u := hasDerivAt_id u
    have h := (h1.sub h2).sub h3
    convert h using 1; ring
  have hcont' : Continuous (fun u : ℝ => 6 * u ^ 2 - 2 * u - 1) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont'.intervalIntegrable 0 q)]
  norm_num

/-! ## Block 6: The convex-envelope ironing — `Ĥ = −9q/8` on `[0, 1/4]`

The line `ℓ(q) = −9q/8` is a global affine minorant of `H`, since
`H(q) + 9q/8 = 2q³ − q² + q/8 = 2q (q − 1/4)² ≥ 0` on `[0, 1]`, touching `H` exactly at `q = 0` and
`q = 1/4`. Hence the convex hull `Ĥ` coincides with the chord `ℓ` on the ironed interval `[0, 1/4]`,
where the low types are bunched. -/

/-- `ℓ(q) = (−9/8)·q + 0` is an affine minorant of `H` on `[0, 1]` (double-root certificate). -/
private lemma irr_chord_minorant :
    IsAffineMinorant 0 1 irrScreening.vvPrimitive (-(9 / 8)) 0 := by
  intro t ht
  rw [irr_vvPrimitive ht]
  -- `2t³ − t² − t − ((−9/8)·t + 0) = 2t(t − 1/4)² ≥ 0`.
  nlinarith [mul_nonneg ht.1 (sq_nonneg (t - 1 / 4)), ht.1]

/-- The convex envelope at the chord endpoints: `Ĥ(0) = 0` and `Ĥ(1/4) = −9/32`. -/
private lemma irr_ironedPrimitive_zero : irrScreening.ironedPrimitive 0 = 0 := by
  refine le_antisymm ?_ ?_
  · have h := convexEnvelope_le_self (by norm_num) irrScreening.vvPrimitive_continuousOn
      (Set.left_mem_Icc.mpr (by norm_num) : (0 : ℝ) ∈ Icc (0:ℝ) 1)
    rw [ScreeningEnv.ironedPrimitive_def] at *
    rw [irr_vvPrimitive (Set.left_mem_Icc.mpr (by norm_num))] at h; simpa using h
  · have h := convexEnvelope_ge_affineMinorant irr_chord_minorant
      (Set.left_mem_Icc.mpr (by norm_num) : (0 : ℝ) ∈ Icc (0:ℝ) 1)
    rw [ScreeningEnv.ironedPrimitive_def]; simpa using h

private lemma irr_ironedPrimitive_quarter : irrScreening.ironedPrimitive (1 / 4) = -(9 / 32) := by
  have hmem : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  refine le_antisymm ?_ ?_
  · have h := convexEnvelope_le_self (by norm_num) irrScreening.vvPrimitive_continuousOn hmem
    rw [ScreeningEnv.ironedPrimitive_def]
    rw [irr_vvPrimitive hmem] at h; norm_num at h ⊢; linarith
  · have h := convexEnvelope_ge_affineMinorant irr_chord_minorant hmem
    rw [ScreeningEnv.ironedPrimitive_def]; norm_num at h ⊢; linarith

/-- **The ironed primitive is the chord `Ĥ(q) = −9q/8` on `[0, 1/4]`.** Convexity of `Ĥ` puts it
below the chord of its endpoints `(0, 0)` and `(1/4, −9/32)`; the minorant puts it above the same
line. -/
lemma irr_ironedPrimitive_affine {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 4)) :
    irrScreening.ironedPrimitive q = -(9 / 8) * q := by
  refine le_antisymm ?_ ?_
  · -- `Ĥ` convex on `[0,1]`, endpoints `0` and `1/4`: `Ĥ q ≤ chord q = −9q/8`.
    have hconv := irrScreening.ironedPrimitive_convexOn
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h4mem : (1 / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have key := hconv.2 h0mem h4mem
      (show (0 : ℝ) ≤ 1 - 4 * q by linarith [hq.2])
      (show (0 : ℝ) ≤ 4 * q by linarith [hq.1])
      (show (1 - 4 * q) + 4 * q = 1 by ring)
    rw [irr_ironedPrimitive_zero, irr_ironedPrimitive_quarter] at key
    simp only [smul_eq_mul] at key
    have harg : (1 - 4 * q) * 0 + 4 * q * (1 / 4) = q := by ring
    rw [harg] at key
    linarith [key]
  · have h := convexEnvelope_ge_affineMinorant irr_chord_minorant
      (⟨hq.1, le_trans hq.2 (by norm_num)⟩ : q ∈ Icc (0 : ℝ) 1)
    rw [ScreeningEnv.ironedPrimitive_def]; simpa using h

/-- **The ironed virtual value is the constant `ψ̄_q = −9/8` on the ironed interval `(0, 1/4)`** —
the low types are bunched. (Compare the regular uniform case, where `ψ̄_q = ψ_q` throughout.) -/
lemma irr_ironedVVQuantile_eq_ironed {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 4)) :
    irrScreening.ironedVVQuantile t = -(9 / 8) := by
  refine irrScreening.ironedVVQuantile_eq_of_affineOn (p := 0) (r := 1 / 4) (m := -(9 / 8)) (c := 0)
    (by norm_num) (by norm_num) (fun x hx => ?_) ht
  rw [irr_ironedPrimitive_affine ⟨hx.1.le, hx.2.le⟩]; ring

/-! ## Block 7: Headline witnesses — the ironing gap is real -/

/-- **`ψ̄_q ≠ ψ_q` on the ironed region** (nonzero ironing gap): at `q = 1/8 ∈ (0, 1/4)` the ironed
value is `−9/8 = −36/32` while the raw value is `h(1/8) = −37/32`, a gap of `1/32`. On the regular
uniform environment these two always coincide. -/
theorem ironedVVQuantile_ne_vvQuantile_witness :
    irrScreening.ironedVVQuantile (1 / 8) = -(9 / 8) ∧
      irrScreening.vvQuantile (1 / 8) = -(37 / 32) ∧
      irrScreening.ironedVVQuantile (1 / 8) ≠ irrScreening.vvQuantile (1 / 8) := by
  refine ⟨irr_ironedVVQuantile_eq_ironed (by norm_num), ?_, ?_⟩
  · rw [irr_vvQuantile (by norm_num)]; norm_num
  · rw [irr_ironedVVQuantile_eq_ironed (by norm_num), irr_vvQuantile (by norm_num)]; norm_num

/-- **The cumulative ironing gap is nonzero.** The library identity
`∫₀ˢ (ψ̄_q − ψ_q) = Ĥ(s) − H(s)` evaluated at `s = 1/8` gives `Ĥ(1/8) − H(1/8) = −9/64 − (−35/256) =
−1/256 ≠ 0`. On the regular uniform environment both sides vanish, so a sign/order error in the
gap is invisible there — here it is caught. -/
theorem integral_ironedVVQuantile_sub_vvQuantile_nonzero :
    (∫ t in (0 : ℝ)..(1 / 8), irrScreening.ironedVVQuantile t - irrScreening.vvQuantile t)
      = -(1 / 256) := by
  rw [irrScreening.integral_ironedVVQuantile_sub_vvQuantile (by norm_num),
    irr_ironedPrimitive_affine (by norm_num), irr_vvPrimitive (by norm_num)]
  norm_num

/-! ## Block 8: The auction layer — the complementary-slackness identity is now nontrivial -/

/-- The symmetric `n`-bidder auction over the irregular environment. -/
def irrAuction (n : ℕ) (hn : 0 < n) : AuctionEnv where
  n := n
  hn := hn
  base := irrScreening

@[simp] lemma irrAuction_base (n : ℕ) (hn : 0 < n) : (irrAuction n hn).base = irrScreening := rfl

/-- **Complementary slackness, now nontrivial.** For the highest-ironed-value allocation the raw and
ironed expected virtual surpluses coincide per bidder. Unlike the regular uniform environment —
where `ψ̄ = ψ` makes this the pointwise identity — here `ψ̄ ≠ ψ` on the ironed region
(`ironedVVQuantile_ne_vvQuantile_witness`), so the equality is a contact-set cancellation:
the ironed allocation is flat exactly where `ψ̄ ≠ ψ`. -/
theorem expected_rawSurplus_eq_ironedSurplus_ironedAlloc_witness
    (i : Fin (irrAuction 2 (by norm_num)).n) :
    ((irrAuction 2 (by norm_num)).base.dist.expect
        (fun t => (irrAuction 2 (by norm_num)).base.virtualValue t
          * (irrAuction 2 (by norm_num)).ironedAlloc.interimAlloc i t))
      = (irrAuction 2 (by norm_num)).base.dist.expect
        (fun t => (irrAuction 2 (by norm_num)).base.ironedVirtualValue t
          * (irrAuction 2 (by norm_num)).ironedAlloc.interimAlloc i t) :=
  (irrAuction 2 (by norm_num)).expected_rawSurplus_eq_ironedSurplus_ironedAlloc
    i

/-- **Ironing weakly raises virtual surplus** (`𝔼[ψ·x] ≤ 𝔼[ψ̄·x]`), surfaced on the irregular
environment where the bound is not an equality-by-degeneration. Anchored on the always-allocate rule
`x ≡ 1`. -/
theorem expected_virtualSurplus_le_ironed_witness :
    irrScreening.dist.expect (fun θ => irrScreening.virtualValue θ * 1)
      ≤ irrScreening.dist.expect (fun θ => irrScreening.ironedVirtualValue θ * 1) :=
  irrScreening.expected_virtualSurplus_le_ironed
    { alloc := { x := fun _ => 1, nonneg := fun _ => by norm_num, le_one := fun _ => le_rfl }
      p := fun _ => 0 }
    (fun _ _ _ _ _ => le_rfl)

end EconlibExamples.MechanismDesign.MyersonIroning

end
