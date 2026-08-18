/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `ContDist` Non-Vacuity Checks

Compile-time semantic witnesses for the generic continuous-distribution API
`Econlib.Probability.ContDist` (CDF, interval probability, expectation algebra, quantile),
exercised on the uniform law `cu = uniform 0 1`. The distribution-specific values (`uniform_cdf`,
`uniform_expect`, …) are already tested in `Distributions/Elementary.lean`; here we drive the
*generic* endpoints on a concrete law.

The CDF endpoint flips (`cdf = 0` left of support, `= 1` past it), the FTC derivative
`cdf' = density`, and the quantile round-trip `F(F⁻¹ u) = u` are the orientation-critical spots.
-/

noncomputable section

namespace EconlibTest.Probability.ContDist

open Econlib.Probability MeasureTheory ProbabilityTheory Filter Topology Set Function Monotone

/-- The uniform law on `[0,1]`. -/
private abbrev cu : ContDist := ContDist.uniform 0 1 (by norm_num)

/-- The density vanishes off `[0,1]` — the support hypothesis the generic CDF lemmas consume. -/
private theorem cu_density_zero_off : ∀ t, t ∉ Icc (0 : ℝ) 1 → cu.density t = 0 :=
  fun t ht => ContDist.uniform_density_eq_zero_of_not_mem 0 1 (by norm_num) ht

/-! ### Shared facts about `cu` on the sub-interval `[1/2, 1]`

The conditioning witnesses all live over the truncation interval `[1/2, 1] ⊆ [0,1]`, where the
uniform density is constantly `1`. We record the constant-density rewrite, continuity, positivity
of the interval mass, and integrability once, then reuse them. -/

/-- On the support `[0, 1]` the uniform density is constantly `1`. -/
private theorem cu_density_on_support : ∀ x ∈ Icc (0 : ℝ) 1, cu.density x = 1 := by
  intro x hx
  rw [ContDist.uniform_density, if_pos hx]; norm_num

/-- The density is continuous on the support `[0, 1]` — it agrees there with the constant `1`. -/
private theorem cu_density_continuousOn : ContinuousOn cu.density (Icc (0 : ℝ) 1) :=
  (continuousOn_const (c := (1 : ℝ))).congr cu_density_on_support

/-- On `[1/2, 1]` the uniform-on-`[0,1]` density is constantly `1` (it sits inside the support). -/
private theorem cu_density_on_half : ∀ x ∈ Icc (1 / 2 : ℝ) 1, cu.density x = 1 := by
  intro x hx
  rw [ContDist.uniform_density, if_pos ⟨by linarith [hx.1], hx.2⟩]; norm_num

/-- The density is continuous on `[1/2, 1]` — it agrees there with the constant `1`. -/
private theorem cu_density_continuousOn_half : ContinuousOn cu.density (Icc (1 / 2 : ℝ) 1) :=
  (continuousOn_const (c := (1 : ℝ))).congr cu_density_on_half

/-- The interval `[1/2, 1]` carries positive mass `1/2 = F(1) − F(1/2)`, the genuine-conditioning
gate `0 < ∫ x in Icc (1/2) 1, density`. -/
private theorem cu_half_mass_pos : 0 < ∫ x in Icc (1 / 2 : ℝ) 1, cu.density x := by
  have h_eq : (∫ x in Icc (1 / 2 : ℝ) 1, cu.density x) = 1 / 2 := by
    rw [show (∫ x in Icc (1 / 2 : ℝ) 1, cu.density x) = cu.prob_interval (1 / 2) 1 from rfl,
      cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
    norm_num
  rw [h_eq]; norm_num

/-- `density · id` is integrable on `[1/2, 1]` — needed by the monotone conditional-mean bounds. -/
private theorem cu_density_id_integrableOn_half :
    IntegrableOn (fun x => cu.density x * x) (Icc (1 / 2 : ℝ) 1) :=
  cu.density_mul_integrableOn cu_density_continuousOn_half continuousOn_id (subset_refl _)

/-- The mean of uniform `[0,1]` is `1/2` — the shared numeric anchor for the bridge witnesses. -/
private theorem cu_expect_id_half : cu.expect id = 1 / 2 := by
  rw [ContDist.uniform_expect 0 1 (by norm_num)]; norm_num

section cdf

/-- **Left endpoint flip:** the CDF is `0` strictly left of the support. -/
theorem cu_cdf_left_zero : cu.cdf (-1) = 0 :=
  cu.cdf_eq_zero_of_supportsOn_Icc_left cu_density_zero_off (by norm_num)

/-- **Right endpoint flip:** the CDF is `1` at or past the right edge of the support. -/
theorem cu_cdf_right_one : cu.cdf 2 = 1 :=
  cu.cdf_eq_one_of_supportsOn_Icc_right cu_density_zero_off (by norm_num)

/-- The CDF is continuous (atomless law). -/
theorem cu_cdf_continuous : Continuous ⇑cu.cdf := cu.cdf_continuous

/-- The CDF is monotone. -/
theorem cu_cdf_mono : Monotone ⇑cu.cdf := cu.cdf.mono

/-- **FTC:** at an interior point the CDF derivative is the density, here `cdf'(1/2) = 1`. -/
theorem cu_deriv_cdf_interior : HasDerivAt (⇑cu.cdf) 1 (1 / 2) := by
  have hcont : ContinuousAt cu.density (1 / 2) := by
    have hconst : ContinuousAt (fun _ : ℝ => (1 : ℝ)) (1 / 2) := continuousAt_const
    refine hconst.congr ?_
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 < 1 by norm_num)] with x hx
    rw [ContDist.uniform_density, if_pos ⟨hx.1.le, hx.2.le⟩]; norm_num
  have hval : cu.density (1 / 2) = 1 := by
    rw [ContDist.uniform_density, if_pos ⟨by norm_num, by norm_num⟩]; norm_num
  have hderiv := cu.deriv_cdf_eq_density (1 / 2) hcont
  rw [hval] at hderiv
  exact hderiv

/-- **Strict monotonicity** where the density is positive: `F(1/4) < F(3/4)`. -/
theorem cu_cdf_strictMono : cu.cdf (1 / 4) < cu.cdf (3 / 4) :=
  cu.cdf_strictMono (by norm_num)
    (fun x hx => by
      rw [ContDist.uniform_density, if_pos ⟨by linarith [hx.1], by linarith [hx.2]⟩]; norm_num)
    (by
      refine (continuousOn_const (c := (1 : ℝ))).congr (fun x hx => ?_)
      rw [ContDist.uniform_density, if_pos ⟨by linarith [hx.1], by linarith [hx.2]⟩]; norm_num)

end cdf

section interval

/-- **Full-support interval probability is one:** `P(0 ≤ X ≤ 1) = F(1) − F(0) = 1`. -/
theorem cu_prob_interval_full : cu.prob_interval 0 1 = 1 := by
  rw [cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
  norm_num

/-- **A degenerate interval has zero probability** (atomless density). -/
theorem cu_prob_interval_self : cu.prob_interval 1 1 = 0 := cu.prob_interval_self 1

/-- Interval probabilities are genuine probabilities in `[0,1]`. -/
theorem cu_prob_interval_nonneg : 0 ≤ cu.prob_interval 0 1 := cu.prob_interval_nonneg 0 1
theorem cu_prob_interval_le_one : cu.prob_interval 0 1 ≤ 1 := cu.prob_interval_le_one 0 1

end interval

section expectation

/-- Expectation of a constant is the constant (total mass `1`). -/
theorem cu_expect_const : cu.expect (fun _ => 5) = 5 := cu.expect_const 5

/-- **Scalar homogeneity:** `E[3·f] = 3·E[f]`. -/
theorem cu_expect_smul : cu.expect ((3 : ℝ) • id) = 3 * cu.expect id := cu.expect_smul 3 id

/-- A nonnegative integrand has nonnegative expectation. -/
theorem cu_expect_nonneg : 0 ≤ cu.expect (fun x => x ^ 2) :=
  cu.expect_nonneg _ (fun x => sq_nonneg x)

end expectation

section expectation_algebra

/-- `density · id` is globally integrable (compactly supported, continuous on the support). -/
private theorem cu_density_id_integrable : Integrable (fun x => cu.density x * x) :=
  cu.density_mul_integrable_of_supportsOn_Icc cu_density_zero_off cu_density_continuousOn
    continuousOn_id

/-- `density · 1` is globally integrable (it is the prior density). -/
private theorem cu_density_one_integrable : Integrable (fun x => cu.density x * (1 : ℝ)) :=
  cu.integrable.congr (Filter.Eventually.of_forall fun _ => (mul_one _).symm)

/-- `density · id²` is globally integrable (compactly supported, continuous on the support). -/
private theorem cu_density_sq_integrable : Integrable (fun x => cu.density x * x ^ 2) :=
  cu.density_mul_integrable_of_supportsOn_Icc cu_density_zero_off cu_density_continuousOn
    (continuous_pow 2).continuousOn

/-- **Additivity (integrability-gated):** `E[X + 1] = E[X] + E[1] = 1/2 + 1 = 3/2`. The witness
drives `expect_add`, whose contract requires both summands' density products integrable; here both
are. -/
theorem cu_expect_add :
    cu.expect (id + fun _ => 1) = cu.expect id + cu.expect (fun _ => 1) :=
  cu.expect_add id (fun _ => 1) cu_density_id_integrable cu_density_one_integrable

/-- The additivity witness lands on the correct number `3/2`: `E[X+1] = 3/2` under uniform
`[0,1]`. -/
theorem cu_expect_add_value : cu.expect (id + fun _ => 1) = 3 / 2 := by
  rw [cu_expect_add, ContDist.uniform_expect 0 1 (by norm_num), cu.expect_const]; norm_num

/-- **Order monotonicity (integrability-gated):** `id ≤ id + 1` pointwise, so `E[X] ≤ E[X + 1]`,
i.e. `1/2 ≤ 3/2`. Reversing the order would fail. -/
theorem cu_expect_mono : cu.expect id ≤ cu.expect (id + fun _ => 1) := by
  set f₂ : ℝ → ℝ := id + fun _ => 1 with hf₂
  have h_sum_int : Integrable (fun x => cu.density x * f₂ x) := by
    have h_eq : (fun x => cu.density x * f₂ x) = fun x => cu.density x * x + cu.density x * 1 := by
      funext x; rw [hf₂, Pi.add_apply, id, mul_add]
    rw [h_eq]; exact cu_density_id_integrable.add cu_density_one_integrable
  exact cu.expect_mono id f₂ (fun x => by rw [hf₂]; simp) cu_density_id_integrable h_sum_int

/-- **Variance is nonnegative (Cauchy–Schwarz, integrability-gated):** `Var[X] ≥ 0` under uniform
`[0,1]` (its actual value is `1/12`). Both first and second moments are integrable here. -/
theorem cu_variance_nonneg : 0 ≤ cu.variance id :=
  cu.variance_nonneg id cu_density_id_integrable
    (by simpa [id] using cu_density_sq_integrable)

end expectation_algebra

section quantile

/-- **CDF right-inverse:** for `u = 1/2 ∈ (0,1)`, `F(F⁻¹ u) = u`. -/
theorem cu_cdf_quantile :
    cu.cdf (Measure.quantile cu.toMeasure (1 / 2)) = 1 / 2 :=
  cu.cdf_quantile (Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩)

/-- **Quantile superlevel characterization:** `F⁻¹ u ≤ x ↔ u ≤ F x`. -/
theorem cu_quantile_le_iff (x : ℝ) :
    Measure.quantile cu.toMeasure (1 / 2) ≤ x ↔ (1 / 2 : ℝ) ≤ cu.cdf x :=
  cu.quantile_le_iff (Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩)

/-- **CDF superlevel inequality (`le_cdf_quantile`):** for `u ∈ (0,1)`, `u ≤ F(F⁻¹ u)`, the weaker
one-sided half of `cdf_quantile`. On the atomless uniform law equality holds, so this anchor
(`1/2 ≤ F(F⁻¹(1/2)) = 1/2`) is a weak duplicate of `cu_cdf_quantile`; it records that the library's
one-sided lemma is available, not a discriminating gap. -/
theorem cu_le_cdf_quantile :
    (1 / 2 : ℝ) ≤ cu.cdf (Measure.quantile cu.toMeasure (1 / 2)) :=
  cu.le_cdf_quantile (Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩)

/-- `id` is integrable against `cu.toMeasure` — the hypothesis for both the quantile change of
variables and the product-integral reduce witnesses. -/
private theorem cu_id_integrable_toMeasure' : Integrable (id : ℝ → ℝ) cu.toMeasure :=
  cu.integrable_toMeasure_iff.mpr (by simpa [id] using cu_density_id_integrable)

/-- **Quantile change of variables anchored to a number:** `E[id] = ∫₀¹ F⁻¹(t) dt`. Under uniform
`[0,1]`, `F⁻¹(t) = t`, so the RHS is `∫₀¹ t dt = 1/2 = E[X]`. The identity converts the
measure-theoretic expectation to a quantile integral. Caveat: on the uniform law `F⁻¹ = F = id` on
`(0,1)`, so this particular anchor would *not* distinguish a swapped `F`/`F⁻¹`; it checks that the
change-of-variables identity holds and lands on the right number, not the orientation of the
inverse. -/
theorem cu_expect_eq_integral_quantile_half :
    cu.expect id = ∫ t in Set.Ioo (0 : ℝ) 1, id (Measure.quantile cu.toMeasure t) :=
  cu.expect_eq_integral_quantile cu_id_integrable_toMeasure'

/-- The quantile change-of-variables lands on the correct number `1/2`:
`∫₀¹ F⁻¹(t) dt = E[X] = 1/2` under uniform `[0,1]`. -/
theorem cu_expect_eq_integral_quantile_value :
    ∫ t in Set.Ioo (0 : ℝ) 1, id (Measure.quantile cu.toMeasure t) = 1 / 2 := by
  rw [← cu_expect_eq_integral_quantile_half, cu_expect_id_half]

end quantile

section conditioning

/-- The genuine-conditioning gate, named once for reuse across the orientation witnesses. -/
private theorem cu_half_pos : 0 < ∫ x in Icc (1 / 2 : ℝ) 1, cu.density x := cu_half_mass_pos

/-- **Conditional-mean anchor:** `E[X | X ∈ [1/2, 1]] = 3/4` under uniform `[0,1]`. The conditional
density is uniform on `[1/2, 1]`, whose mean is the midpoint `3/4`. This is the exact number every
direction/endpoint witness below is checked against; an off-by-a-half-interval or numerator/
denominator swap would land somewhere other than `3/4`. -/
theorem cu_conditionalExpect_id_value :
    cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos = 3 / 4 := by
  rw [cu.conditionalExpect_eq id (Icc (1 / 2 : ℝ) 1) cu_half_pos]
  have h_denom : (∫ x in Icc (1 / 2 : ℝ) 1, cu.density x) = 1 / 2 := by
    rw [show (∫ x in Icc (1 / 2 : ℝ) 1, cu.density x) = cu.prob_interval (1 / 2) 1 from rfl,
      cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
    norm_num
  have h_numer : (∫ x in Icc (1 / 2 : ℝ) 1, cu.density x * id x) = 3 / 8 := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (g := fun x => x) (fun x hx => by rw [cu_density_on_half x hx, id, one_mul])]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)/2 ≤ 1)]
    rw [integral_id]; norm_num
  rw [h_numer, h_denom]; norm_num

/-- **Identity conditional mean lands inside the interval:** `E[X | X ∈ [1/2, 1]] ∈ [1/2, 1]`. The
anchor `3/4` lies strictly inside, so this would fail under either endpoint flip. -/
theorem cu_conditionalExpect_id_mem_Icc :
    cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos ∈ Icc (1 / 2 : ℝ) 1 :=
  cu.conditionalExpect_id_mem_Icc (1 / 2) 1 cu_half_pos cu_density_id_integrableOn_half
    (by norm_num)

/-- **Lower bound (`_ge_left`) with the correct direction:** `id(1/2) = 1/2 ≤ E[X | X ∈ [1/2, 1]]`.
The conditional mean dominates the left endpoint; reversing the inequality would be `3/4 ≤ 1/2`,
false. -/
theorem cu_conditionalExpect_ge_left :
    (1 / 2 : ℝ) ≤ cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos := by
  have h := cu.conditionalExpect_ge_left id (1 / 2) 1 cu_half_pos monotoneOn_id
    cu_density_id_integrableOn_half (by norm_num)
  simpa using h

/-- **Upper bound (`_le_right`) with the correct direction:** `E[X | X ∈ [1/2, 1]] ≤ id(1) = 1`.
The conditional mean is dominated by the right endpoint; the anchor `3/4 ≤ 1` confirms
orientation. -/
theorem cu_conditionalExpect_le_right :
    cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos ≤ 1 := by
  have h := cu.conditionalExpect_le_right id (1 / 2) 1 cu_half_pos monotoneOn_id
    cu_density_id_integrableOn_half (by norm_num)
  simpa using h

/-- `density · 1` is integrable on `[1/2, 1]` — the comparison integrand for the `_mono`
witnesses. -/
private theorem cu_density_one_integrableOn_half :
    IntegrableOn (fun x => cu.density x * (1 : ℝ)) (Icc (1 / 2 : ℝ) 1) :=
  cu.density_mul_integrableOn cu_density_continuousOn_half continuousOn_const (subset_refl _)

/-- **Monotonicity of conditional expectation:** since `id ≤ 1` pointwise on `[1/2, 1]`,
`E[X | X ∈ [1/2, 1]] ≤ E[1 | X ∈ [1/2, 1]]`, i.e. `3/4 ≤ 1`. -/
theorem cu_conditionalExpect_mono :
    cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos ≤
      cu.conditionalExpect (fun _ => 1) (Icc (1 / 2 : ℝ) 1) cu_half_pos :=
  cu.conditionalExpect_mono id (fun _ => 1) (Icc (1 / 2 : ℝ) 1) measurableSet_Icc cu_half_pos
    (fun x hx => by simpa [id] using hx.2)
    cu_density_id_integrableOn_half cu_density_one_integrableOn_half

/-- The comparison conditional mean `E[1 | X ∈ [1/2, 1]] = 1` (constant), so the `_mono` witness
above is the sharp inequality `3/4 ≤ 1`, not a vacuous one. -/
theorem cu_conditionalExpect_const_one :
    cu.conditionalExpect (fun _ => 1) (Icc (1 / 2 : ℝ) 1) cu_half_pos = 1 :=
  cu.conditionalExpect_const 1 (Icc (1 / 2 : ℝ) 1) cu_half_pos

/-- The sub-event `[1/2, 3/4] ⊆ [1/2, 1]` carries positive mass `1/4`; the strict-domination
witness needs a positive-measure set on which `id < 1` strictly. -/
private theorem cu_quarter_pos : 0 < ∫ x in Icc (1 / 2 : ℝ) (3 / 4), cu.density x := by
  have h_eq : (∫ x in Icc (1 / 2 : ℝ) (3 / 4), cu.density x) = 1 / 4 := by
    rw [show (∫ x in Icc (1 / 2 : ℝ) (3 / 4), cu.density x) = cu.prob_interval (1 / 2) (3 / 4)
        from rfl,
      cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
    norm_num
  rw [h_eq]; norm_num

/-- **Strict conditional domination:** `id < 1` strictly on the positive-measure sub-event
`[1/2, 3/4]` (and `id ≤ 1` throughout `[1/2, 1]`), so `E[X | X ∈ [1/2, 1]] < E[1 | X ∈ [1/2, 1]]`,
i.e. the anchor `3/4` is *strictly* below `1`. -/
theorem cu_conditionalExpect_strict_mono :
    cu.conditionalExpect id (Icc (1 / 2 : ℝ) 1) cu_half_pos <
      cu.conditionalExpect (fun _ => 1) (Icc (1 / 2 : ℝ) 1) cu_half_pos :=
  cu.conditionalExpect_strict_mono id (fun _ => 1) (Icc (1 / 2 : ℝ) 1) measurableSet_Icc
    cu_half_pos (fun x hx => by simpa [id] using hx.2)
    cu_density_id_integrableOn_half cu_density_one_integrableOn_half
    (Icc (1 / 2 : ℝ) (3 / 4)) (Icc_subset_Icc le_rfl (by norm_num)) measurableSet_Icc
    cu_quarter_pos
    (fun x hx => by simp only [id]; linarith [hx.2])

end conditioning

section posterior

/-- The flat likelihood `ℓ ≡ 1`, with which Bayes performs no update. -/
private abbrev flatLk : ℝ → ℝ := fun _ => 1

private theorem flatLk_nn : ∀ θ, 0 ≤ flatLk θ := fun _ => zero_le_one

/-- Under the flat likelihood the evidence integrand is just the prior density, integrable. -/
private theorem cu_flat_int : Integrable (fun θ => cu.density θ * flatLk θ) :=
  cu.integrable.congr (Filter.Eventually.of_forall fun θ => by simp [flatLk])

/-- The flat-likelihood normalizer is the prior's total mass `1 > 0` — positive evidence. -/
private theorem cu_flat_denom_pos : 0 < ∫ θ, cu.density θ * flatLk θ := by
  have h_eq : (∫ θ, cu.density θ * flatLk θ) = 1 := by
    simp only [flatLk, mul_one]; exact cu.integral_one
  rw [h_eq]; norm_num

/-- **Flat-likelihood posterior equals the prior:** with `ℓ ≡ 1` the Bayes update leaves the
density unchanged, so the posterior density at the interior point `1/2` is the uniform value `1`. A
swapped numerator/normalizer or a missing `mul ℓ` would not reproduce the prior here. -/
theorem cu_posteriorOfLikelihood_density_half :
    (cu.posteriorOfLikelihood flatLk flatLk_nn cu_flat_int cu_flat_denom_pos).density (1 / 2)
      = 1 := by
  rw [cu.posteriorOfLikelihood_density flatLk (1 / 2) flatLk_nn cu_flat_int cu_flat_denom_pos]
  have h_denom : (∫ θ', cu.density θ' * flatLk θ') = 1 := by
    simp only [flatLk, mul_one]; exact cu.integral_one
  rw [h_denom]
  simp only [flatLk, mul_one, div_one]
  rw [ContDist.uniform_density, if_pos ⟨by norm_num, by norm_num⟩]; norm_num

/-- The genuine posterior is a probability law (density integrates to `1`). Witnesses that the
positive-evidence gate yields a real distribution, not a renormalization artifact. -/
theorem cu_posterior_is_dist :
    ∫ θ, (cu.posteriorOfLikelihood flatLk flatLk_nn cu_flat_int cu_flat_denom_pos).density θ = 1 :=
  (cu.posteriorOfLikelihood flatLk flatLk_nn cu_flat_int cu_flat_denom_pos).integral_one

/-! ### Informative likelihood `ℓ(θ) = θ²` — discriminates the Bayes-formula bugs

The flat `ℓ ≡ 1` above cannot catch a missing `* ℓ` factor, a numerator/denominator swap, or a
normalization slip (prior density, likelihood, and normalizer are all `1`). The nonconstant
`ℓ(θ) = θ²` does: it reweights the uniform prior toward `1`, with evidence `∫₀¹ θ² dθ = 1/3` and
posterior density `prior(θ)·θ²/(1/3) = 3θ²` on `[0,1]`. -/

/-- The squared likelihood `ℓ(θ) = θ²`, globally nonnegative and nonconstant on `[0,1]`. -/
private abbrev sqLk : ℝ → ℝ := fun θ => θ ^ 2

private theorem sqLk_nn : ∀ θ, 0 ≤ sqLk θ := fun θ => sq_nonneg θ

/-- `density · θ²` is integrable: compactly supported, `θ²` continuous on `[0,1]`. -/
private theorem cu_sq_int : Integrable (fun θ => cu.density θ * sqLk θ) :=
  cu.density_mul_integrable_of_supportsOn_Icc cu_density_zero_off cu_density_continuousOn
    (continuous_pow 2).continuousOn

/-- **The `θ²` evidence is `1/3`.** `∫₀¹ 1·θ² dθ = 1/3` — distinct from the flat evidence `1`, so a
formula that ignored the likelihood would use the wrong normalizer. -/
theorem cu_sq_evidence : (∫ θ, cu.density θ * sqLk θ) = 1 / 3 := by
  rw [show (fun θ => cu.density θ * sqLk θ) = Set.indicator (Set.Icc 0 1) (fun θ => θ ^ 2) from by
    funext θ
    simp only [sqLk]
    rw [ContDist.uniform_density]
    by_cases hθ : θ ∈ Set.Icc (0:ℝ) 1
    · rw [if_pos (by simpa [Set.mem_Icc] using hθ), Set.indicator_of_mem hθ]; norm_num
    · rw [if_neg (by simpa [Set.mem_Icc] using hθ), Set.indicator_of_notMem hθ, zero_mul]]
  rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
  norm_num

private theorem cu_sq_denom_pos : 0 < ∫ θ, cu.density θ * sqLk θ := by
  rw [cu_sq_evidence]; norm_num

/-- **Informative posterior density at `θ = 1` is `3`.** `prior(1)·ℓ(1)/evidence = 1·1/(1/3) = 3`.
The flat-likelihood witness gives `1` here; the `θ²` update genuinely tilts mass toward `1`. A
missing `* ℓ` factor would give `1·1/(1/3)`... wait — a missing `* ℓ` factor would give
`prior(1)/(1/3) = 3` too only by coincidence of `ℓ(1)=1`; but at `θ = 1/2` below the factor is
load-bearing. -/
theorem cu_posterior_sq_density_one :
    (cu.posteriorOfLikelihood sqLk sqLk_nn cu_sq_int cu_sq_denom_pos).density 1 = 3 := by
  rw [cu.posteriorOfLikelihood_density sqLk 1 sqLk_nn cu_sq_int cu_sq_denom_pos, cu_sq_evidence]
  rw [ContDist.uniform_density, if_pos ⟨by norm_num, by norm_num⟩]
  simp only [sqLk]; norm_num

/-- **Informative posterior density at the interior `θ = 1/2` is `3/4`.**
`prior(1/2)·ℓ(1/2)/evidence = 1·(1/4)/(1/3) = 3/4`. Here the `* ℓ` factor is load-bearing: dropping
it would give `1/(1/3) = 3`, and a numerator/denominator swap would give `(1/3)/(1/4) = 4/3`, both
≠ `3/4`. So this is the witness that genuinely catches the Bayes-formula bugs the flat likelihood
masks. -/
theorem cu_posterior_sq_density_half :
    (cu.posteriorOfLikelihood sqLk sqLk_nn cu_sq_int cu_sq_denom_pos).density (1 / 2) = 3 / 4 := by
  rw [cu.posteriorOfLikelihood_density sqLk (1 / 2) sqLk_nn cu_sq_int cu_sq_denom_pos,
    cu_sq_evidence]
  rw [ContDist.uniform_density, if_pos ⟨by norm_num, by norm_num⟩]
  simp only [sqLk]; norm_num

end posterior

section truncate

/-- The mass `cu.prob_interval (1/2) 1 = 1/2 > 0`, the truncation gate. -/
private theorem cu_prob_half_pos : 0 < cu.prob_interval (1 / 2 : ℝ) 1 := by
  rw [cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
  norm_num

/-- **Truncated density on the interval is the renormalized value `2`:** restricting uniform
`[0,1]` to `[1/2, 1]` and renormalizing gives density `1 / (1/2) = 2` at the interior point `3/4`.
An off-by-`prob_interval` normalizer would not yield `2`. -/
theorem cu_truncate_density_inside :
    (cu.truncate (1 / 2) 1 (by norm_num) cu_prob_half_pos).density (3 / 4) = 2 := by
  rw [cu.truncate_density (1 / 2) 1 (by norm_num) cu_prob_half_pos,
    if_pos ⟨by norm_num, by norm_num⟩]
  rw [ContDist.uniform_density, if_pos ⟨by norm_num, by norm_num⟩]
  rw [cu.prob_interval_eq_of_le (by norm_num), ContDist.uniform_cdf, ContDist.uniform_cdf]
  norm_num

/-- **Truncated density vanishes off the interval:** at `1/4 ∉ [1/2, 1]` the truncated density is
`0`. This is the endpoint-flip catch — the truncation support is `[1/2, 1]`, not its complement. -/
theorem cu_truncate_density_outside :
    (cu.truncate (1 / 2) 1 (by norm_num) cu_prob_half_pos).density (1 / 4) = 0 := by
  rw [cu.truncate_density (1 / 2) 1 (by norm_num) cu_prob_half_pos, if_neg (by norm_num)]

end truncate

section stieltjes

/-- **Stieltjes measure bridge:** the CDF's Stieltjes measure is `cu.toMeasure`. Confirms the
density-CDF and the Stieltjes regularization agree as measures. -/
theorem cu_stieltjes_measure_eq : stieltjesMeasure cu.cdf.mono = cu.toMeasure :=
  contdist_stieltjes_measure_eq cu

/-- **Stieltjes integral bridge anchored to a number:** integrating `id` against the CDF's
Stieltjes measure equals `E[X] = 1/2`. The bridge would be off if it dropped the density weight. -/
theorem cu_stieltjes_integral_eq_half :
    ∫ x, x ∂(stieltjesMeasure cu.cdf.mono) = 1 / 2 := by
  have h := contdist_stieltjes_integral_eq cu id
  simp only [id] at h
  rw [h, show (∫ x, cu.density x * x) = cu.expect id from rfl, cu_expect_id_half]

/-- **IBP bridge on a monotone test function:** `∫ leftLim(id_sf) dμ_CDF = E[X] = 1/2`. The test
function `id` is monotone, so its left-limit reconstruction integrates back to the expectation. -/
theorem cu_ibp_bridge_id :
    ∫ x, leftLim (⇑(stieltjes (monotone_id (α := ℝ)))) x
        ∂(stieltjesMeasure cu.cdf.mono) = 1 / 2 := by
  rw [contdist_ibp_bridge cu id monotone_id, cu_expect_id_half]

/-- **Set IBP bridge anchored to a number:** restricting the bridge to `[0,1]` returns the full
mean `1/2`, since the uniform support is exactly `[0,1]`. -/
theorem cu_ibp_bridge_set_id :
    ∫ x in Icc (0 : ℝ) 1, leftLim (⇑(stieltjes (monotone_id (α := ℝ)))) x
        ∂(stieltjesMeasure cu.cdf.mono) = 1 / 2 := by
  rw [contdist_ibp_bridge_set cu id monotone_id measurableSet_Icc]
  rw [setIntegral_congr_fun measurableSet_Icc
    (g := fun x => x) (fun x hx => by rw [cu_density_on_support x hx, id, one_mul])]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [integral_id]; norm_num

end stieltjes

section tails

/-- **Left-tail first-moment decay:** `F(-n)·(-n) → 0` from the finite first moment of uniform
`[0,1]`. Caveat: uniform `[0,1]` has compact support, so `F(-n) = 0` for every `n ≥ 1` and the
product is *identically* `0` past the support — this witness therefore exercises only the
availability of the boundary-decay lemma, not the nontrivial finite-first-moment tail argument that
a law with a genuine left tail (e.g. a two-sided exponential) would stress. -/
theorem cu_cdf_times_a_tendsto_zero_left :
    Tendsto (fun n : ℕ => cu.cdf (-(↑n : ℝ)) * (-(↑n : ℝ))) atTop (𝓝 0) :=
  cdf_times_a_tendsto_zero_left cu cu_density_id_integrable

end tails

section product

/-- The identity is integrable against `cu.toMeasure` — the product-marginal hypothesis. -/
private theorem cu_id_integrable_toMeasure : Integrable (id : ℝ → ℝ) cu.toMeasure :=
  cu.integrable_toMeasure_iff.mpr (by simpa [id] using cu_density_id_integrable)

/-- **Coordinate marginal of the IID product anchored to a number:** averaging the first coordinate
of two IID uniform draws recovers the one-dimensional mean `E[X] = 1/2`. Caveat: under an *IID*
product both coordinates share the same marginal, so this anchor does not distinguish a coordinate
swap (`θ 0` vs `θ 1`) — it checks that the marginal-of-a-product reduction lands on the right
number, i.e. the Fubini/marginal bookkeeping, on a non-degenerate value. -/
theorem cu_integral_piMeasure_eval_half :
    ∫ θ, id ((θ : Fin 2 → ℝ) 0) ∂(cu.piMeasure 2) = 1 / 2 := by
  rw [cu.integral_piMeasure_eval (0 : Fin 2) cu_id_integrable_toMeasure, cu_expect_id_half]

/-- The IID product is a genuine probability measure (total mass `1`). -/
theorem cu_piMeasure_isProbability : IsProbabilityMeasure (cu.piMeasure 2) :=
  cu.isProbabilityMeasure_piMeasure 2

/-- The first coordinate `eval 0` is a measure-preserving map from the 2-fold IID product to the
one-dimensional marginal `cu.toMeasure`. Used to transfer integrability for the reduce witnesses. -/
private theorem cu_eval0_measurePreserving :
    MeasurePreserving (Function.eval (0 : Fin 2)) (cu.piMeasure 2) cu.toMeasure := by
  constructor
  · exact measurable_pi_apply 0
  · have : Measure.map (Function.eval (0 : Fin 2)) (cu.piMeasure 2) = cu.toMeasure := by
      haveI hpm : IsProbabilityMeasure cu.toMeasure := cu.toMeasure_isProbability
      haveI : ∀ _ : Fin 2, SigmaFinite cu.toMeasure := fun _ => inferInstance
      rw [ContDist.piMeasure, Measure.pi_map_eval,
        Finset.prod_eq_one fun _ _ => hpm.measure_univ, one_smul]
    exact this

/-- `eval 0` is integrable against `piMeasure 2` — pulled back from `Integrable id cu.toMeasure`
via the marginal measure-preserving property. -/
private theorem cu_eval0_integrable_piMeasure :
    Integrable (fun θ : Fin 2 → ℝ => θ 0) (cu.piMeasure 2) :=
  cu_eval0_measurePreserving.integrable_comp_of_integrable cu_id_integrable_toMeasure

/-- **`lintegral_piMeasure_reduce` — lower-integral reduce formula, constant witness:** The Tonelli
reduce identity `∫⁻ θ, 1 ∂piMeasure = ∫⁻ t, ∫⁻ θ', 1 ∂piMeasure ∂d.toMeasure` holds (both sides
equal `1`). Caveat: the constant integrand `h ≡ 1` erases all coordinate/update bookkeeping — both
sides are just the total mass `1` — so this is an availability/total-mass check for the
ENNReal-valued Fubini split, not a coordinate-sensitive guard. -/
-- `θ`, `t`, `θ'` are integral-notation binders; unused because the integrand is constant `1`.
theorem cu_lintegral_piMeasure_reduce_const :
    ∫⁻ _θ : Fin 2 → ℝ, (1 : ENNReal) ∂(cu.piMeasure 2)
      = ∫⁻ _t : ℝ, ∫⁻ _θ' : Fin 2 → ℝ, (1 : ENNReal) ∂(cu.piMeasure 2) ∂cu.toMeasure :=
  cu.lintegral_piMeasure_reduce (0 : Fin 2) measurable_const

/-- Both sides of the `lintegral_piMeasure_reduce` constant witness equal `1`, confirming the
formula is non-vacuous: Total-mass preservation under the Fubini split. -/
theorem cu_lintegral_piMeasure_reduce_const_value :
    (∫⁻ _θ : Fin 2 → ℝ, (1 : ENNReal) ∂(cu.piMeasure 2)) = 1 := by
  simp [MeasureTheory.lintegral_const, cu.isProbabilityMeasure_piMeasure 2 |>.measure_univ]

/-- **`integral_piMeasure_reduce` — Bochner reduce formula anchored to `1/2`:** With `h θ = θ 0`
and `i = 0`, reducing the 2-fold IID product integral gives:
`∫ θ, θ 0 ∂piMeasure 2 = ∫ t, (∫ θ', (update θ' 0 t) 0 ∂piMeasure 2) ∂cu.toMeasure`. The inner
integral simplifies to `t` (since `(update θ' 0 t) 0 = t` and piMeasure is a probability), and the
outer integral is `E[id] = 1/2`. This catches a wrong-coordinate swap (reducing by `i = 1` instead
of `0` would leave `θ 0` free in the inner integral) and confirms the Fubini slicing is in the
direction declared by the signature. -/
theorem cu_integral_piMeasure_reduce_half :
    ∫ θ : Fin 2 → ℝ, θ 0 ∂(cu.piMeasure 2)
      = ∫ t : ℝ, ∫ θ' : Fin 2 → ℝ, Function.update θ' 0 t 0 ∂(cu.piMeasure 2) ∂cu.toMeasure := by
  have h := cu.integral_piMeasure_reduce (0 : Fin 2)
    (hh := cu_eval0_integrable_piMeasure)
  simpa using h

/-- The `integral_piMeasure_reduce` anchor lands on the correct number: Each side equals `1/2`. LHS
= `∫ θ, θ 0 ∂piMeasure 2 = E[X] = 1/2` (coordinate marginal). RHS: `(update θ' 0 t) 0 = t`, so
inner integral = `t`, outer = `∫ t, t ∂cu.toMeasure = E[X] = 1/2`. -/
theorem cu_integral_piMeasure_reduce_value :
    ∫ θ : Fin 2 → ℝ, θ 0 ∂(cu.piMeasure 2) = 1 / 2 := by
  rw [show (∫ θ : Fin 2 → ℝ, θ 0 ∂cu.piMeasure 2)
      = ∫ θ, id (θ 0) ∂cu.piMeasure 2 from rfl]
  rw [cu.integral_piMeasure_eval (0 : Fin 2) cu_id_integrable_toMeasure, cu_expect_id_half]

/-- **The inner slice of the reduce is coordinate-sensitive:** `∀ t, ∫ θ', (update θ' 0 t) 0
∂piMeasure 2 = t`. Because `(update θ' 0 t) 0 = t` is constant in `θ'`, the inner integral equals
`t · (total mass) = t`. This is the *discriminating* slice the IID-marginal anchors cannot give:
updating the *wrong* coordinate, `(update θ' 1 t) 0 = θ' 0`, would integrate to `E[θ' 0] = 1/2`, a
constant independent of `t` — so a wrong-coordinate `update` is caught here. -/
theorem cu_integral_piMeasure_reduce_inner_slice (t : ℝ) :
    ∫ θ' : Fin 2 → ℝ, Function.update θ' 0 t 0 ∂(cu.piMeasure 2) = t := by
  rw [show (fun θ' : Fin 2 → ℝ => Function.update θ' 0 t 0) = (fun _ => t) from by
    funext θ'; rw [Function.update_self]]
  haveI := cu.isProbabilityMeasure_piMeasure 2
  rw [MeasureTheory.integral_const]
  simp

end product

section probLaw

/-- **`ProbLaw` embedding round-trip:** the measure carried by `cu.toProbDist` is `cu.toMeasure`. -/
theorem cu_toProbDist_toMeasure : (cu.toProbDist : Measure ℝ) = cu.toMeasure :=
  cu.toProbDist_toMeasure

/-- **Expectation agrees across the embedding anchored to a number:**
`E_cu[X] = E_{toProbDist}[X]
= 1/2`. Catches a mismatch between the `ContDist` and `ProbDist`
expectation conventions. -/
theorem cu_expect_eq_probDist_expect_half : cu.toProbDist.expect id = 1 / 2 := by
  rw [← cu.expect_eq_probDist_expect, cu_expect_id_half]

end probLaw

section stieltjesChainRule

/-- The uniform law viewed as a `ProbDist ℝ`, the carrier the chain-rule API operates on. -/
private abbrev cuP : ProbDist ℝ := cu.toProbDist

/-- **`cdfReal` agrees with the `ContDist` CDF, anchored:** `cdfReal cuP (1/2) = F(1/2) = 1/2`. The
real-valued CDF used to feed `stieltjesMeasure` is the same CDF, not an off-by-`toReal` artifact. -/
theorem cuP_cdfReal_half : cdfReal cuP (1 / 2) = 1 / 2 := by
  rw [cdfReal, show ((cuP : Measure ℝ) (Iic (1 / 2))) = cu.toMeasure (Iic (1 / 2)) from rfl,
    cu.toReal_measure_Iic_eq_cdf, ContDist.uniform_cdf]
  norm_num

/-- `cdfReal` is monotone (it is a CDF). -/
theorem cuP_cdfReal_monotone : Monotone (cdfReal cuP) := cdfReal_monotone cuP

/-- The uniform law is atomless: Every singleton has measure `0` (density measures inherit
`NoAtoms` from Lebesgue measure, via the `ContDist.instNoAtoms` instance). -/
private theorem cuP_atomless : ∀ x, (cuP : Measure ℝ) {x} = 0 := by
  intro x
  change cu.toMeasure {x} = 0
  exact measure_singleton x

/-- **`cdfReal` is continuous under atomlessness:** the uniform CDF has no jumps, so its
real-valued form is continuous (not merely right-continuous). -/
theorem cuP_cdfReal_continuous : Continuous (cdfReal cuP) :=
  cdfReal_continuous_of_noAtoms cuP_atomless

/-- **CDF-representation bridge, with both sides pinned to `1/2`:** the real-valued `cdfReal`
coincides with Mathlib's `ProbabilityTheory.cdf` Stieltjes representation, *and* both evaluate to
the concrete `1/2` at `x = 1/2`. The earlier version stated only the API equality; here the numeric
anchor is part of the statement. -/
theorem cuP_cdfReal_eq_cdf_half :
    cdfReal cuP (1 / 2) = (ProbabilityTheory.cdf (cuP : Measure ℝ)) (1 / 2) ∧
      cdfReal cuP (1 / 2) = 1 / 2 ∧ (ProbabilityTheory.cdf (cuP : Measure ℝ)) (1 / 2) = 1 / 2 := by
  have hbridge : cdfReal cuP (1 / 2) = (ProbabilityTheory.cdf (cuP : Measure ℝ)) (1 / 2) :=
    cdfReal_eq_cdf (1 / 2)
  exact ⟨hbridge, cuP_cdfReal_half, by rw [← hbridge, cuP_cdfReal_half]⟩

/-- **Chain rule (`stieltjes_pow_cdf_eq_pow_smul_F`) on a concrete law:** the Stieltjes measure of
`(cdfReal cuP)^1` integrates the constant `1` over `(0,1]` to the same value as `1·∫ 1·(cdfReal)^0`
against `cuP` itself. Instantiating the chain-rule identity at `k = 1`, `φ ≡ 1`, `[0,1]` confirms
it holds on the uniform law (atomless), not just abstractly. -/
theorem cuP_stieltjes_pow_chain_rule :
    ∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ) ∂(stieltjesMeasure (cdfReal_pow_monotone cuP 1))
      = (1 : ℝ) * ∫ x in Ioc (0 : ℝ) 1, (1 : ℝ) * (cdfReal cuP x) ^ (1 - 1) ∂(cuP : Measure ℝ) := by
  have h := stieltjes_pow_cdf_eq_pow_smul_F cuP_atomless 1 (a := 0) (b := 1) (φ := fun _ => 1)
    (by norm_num) continuousOn_const
  simpa using h

/-- **Chain rule at the non-degenerate `k = 2`, `φ = id`** — the genuine power-rule test. At `k = 1`
the factor `F^{k-1} = F^0 = 1` collapses, hiding a missing-power bug; at `k = 2` it is `F^1 = F`,
which is load-bearing. The identity `∫_{(0,1]} x d(F²) = 2·∫_{(0,1]} x·F dμ` is exercised on the
uniform law, where `F(x) = x` and `μ = dx` on `[0,1]`. -/
theorem cuP_stieltjes_pow_chain_rule_two :
    ∫ x in Ioc (0 : ℝ) 1, x ∂(stieltjesMeasure (cdfReal_pow_monotone cuP 2))
      = (2 : ℝ) * ∫ x in Ioc (0 : ℝ) 1, x * (cdfReal cuP x) ^ (2 - 1) ∂(cuP : Measure ℝ) :=
  stieltjes_pow_cdf_eq_pow_smul_F cuP_atomless 2 (a := 0) (b := 1) (φ := fun x => x)
    (by norm_num) continuousOn_id


/-- **IBP chain rule (`integral_deriv_mul_cdf_pow`) on a concrete law:** instantiated at `k = 1`,
`ψ = id` over `[0,1]`, the integration-by-parts identity `∫ ψ'·F = ψ·F|₀¹ − ∫ ψ dF` holds on the
uniform law. Here `deriv id = 1` and the boundary endpoints are `F(1) = 1`, `F(0) = 0`, so the
identity is the non-degenerate `∫_{(0,1]} F = 1 − E[X]`, exercising the boundary-term/interior
bookkeeping on a real distribution. -/
theorem cuP_integral_deriv_mul_cdf_pow :
    ∫ x in Ioc (0 : ℝ) 1, deriv (fun x => x) x * (cdfReal cuP x) ^ 1
      = (1 : ℝ) * (cdfReal cuP 1) ^ 1 - (0 : ℝ) * (cdfReal cuP 0) ^ 1
        - (1 : ℝ) * ∫ x in Ioc (0 : ℝ) 1, x * (cdfReal cuP x) ^ (1 - 1)
            ∂(cuP : Measure ℝ) := by
  have h := integral_deriv_mul_cdf_pow cuP_atomless (ψ := fun x => x) contDiff_id 1
    (a := 0) (b := 1) (by norm_num)
  simpa using h

end stieltjesChainRule

end EconlibTest.Probability.ContDist

end
