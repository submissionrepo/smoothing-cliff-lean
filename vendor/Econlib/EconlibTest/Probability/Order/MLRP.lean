/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# MLRP / measure-theoretic FOSD Non-Vacuity Checks

Compile-time semantic witnesses for the monotone-likelihood-ratio stack
(`Econlib.Probability.Order.MLRP`), the `ContDist` FOSD expectation engine
(`Econlib.Probability.Order.FOSD.ExpectMono`), and the `FinDist` FOSD lattice
(`Econlib.Probability.Order.FOSD.FinDistLattice`). The combinatorial `FinDist.FOSD` slice is
covered separately in `FOSD.lean`; this file exercises the *measure-theoretic* and *MLRP* layers
those tests leave open.

The continuum anchor is the pair of exponentials

* `eHi = Exp(1)` — rate `1`, mean `1`;
* `eLo = Exp(2)` — rate `2`, mean `1/2`.

The smaller rate has the smaller CDF (`1 - e^{-x} ≤ 1 - e^{-2x}`), so `Exp(1)` first-order
stochastically dominates `Exp(2)`. Equivalently `Exp(1)` is MLR-dominant over `Exp(2)`: The
likelihood ratio `e^{-x}/(2e^{-2x}) = e^{x}/2` is increasing. The orientation-critical anchor is
the **mean comparison** `mean(eHi) = 1 > 1/2 = mean(eLo)` — a reversed MLRP, a swapped pair, or a
sign error in the dominance direction breaks it. Every monotone-expectation witness routes through
this single `MLRPLe`/`FOSD` fact.

The MLRP single-crossing slice uses the Gaussian location family `θ ↦ N(θ, 1)` (the textbook strict
MLRP family) against the supermodular primitive `u t x = arctan t · x`.

The finite slice rebuilds the `Fin 3` pair from `FOSD.lean` (`dHi`/`dLo`) to drive the FOSD partial
order, the CDF-recovery constructors (`ofCdf`/`ofCdfVec`), and the complete-lattice supremum.
-/

noncomputable section

namespace EconlibTest.Probability.Order.MLRP

open Econlib.Probability MeasureTheory Set ProbabilityTheory Finset
open scoped Real BigOperators

/-! ## The continuum anchor: Two exponentials -/

/-- The FOSD-dominant law `Exp(1)` (lower rate, mean `1`). -/
private abbrev eHi : ContDist := ContDist.exponential 1 one_pos

/-- The FOSD-dominated law `Exp(2)` (higher rate, mean `1/2`). -/
private abbrev eLo : ContDist := ContDist.exponential 2 two_pos

/-- Density of `Exp(1)` on the support: `e^{-x}`. -/
private theorem eHi_density (x : ℝ) (hx : 0 ≤ x) : eHi.density x = Real.exp (-x) := by
  rw [eHi, ContDist.exponential_density, exponentialPDFReal, gammaPDFReal]; simp [hx]

/-- Density of `Exp(2)` on the support: `2 e^{-2x}`. -/
private theorem eLo_density (x : ℝ) (hx : 0 ≤ x) : eLo.density x = 2 * Real.exp (-(2 * x)) := by
  rw [eLo, ContDist.exponential_density, exponentialPDFReal, gammaPDFReal]; simp [hx]

private theorem eHi_density_neg (x : ℝ) (hx : x < 0) : eHi.density x = 0 := by
  rw [eHi, ContDist.exponential_density, exponentialPDFReal, gammaPDFReal]; simp [not_le.mpr hx]

private theorem eLo_density_neg (x : ℝ) (hx : x < 0) : eLo.density x = 0 := by
  rw [eLo, ContDist.exponential_density, exponentialPDFReal, gammaPDFReal]; simp [not_le.mpr hx]

section means

/-- **Mean of the dominant law:** `mean(Exp(1)) = 1`. -/
theorem eHi_mean : eHi.expect id = 1 := by rw [eHi, ContDist.exponential_expect]; norm_num

/-- **Mean of the dominated law:** `mean(Exp(2)) = 1/2`. The dominant mean is strictly higher,
`1 > 1/2`: The orientation anchor for the whole file. -/
theorem eLo_mean : eLo.expect id = 1 / 2 := by rw [eLo, ContDist.exponential_expect]

end means

section mlrp

/-- **The pairwise MLR dominance.** `Exp(1)` is MLR-dominant over `Exp(2)`: For `x₁ ≤ x₂`,
`eHi(x₁)·eLo(x₂) ≤ eHi(x₂)·eLo(x₁)`. After cancelling the rate constants this is `e^{x₁ - x₂} ≤ 1`.
A reversed pair flips the exponent sign. -/
theorem mlrpLe_witness : eLo.MLRPLe eHi := by
  intro x₁ x₂ hx
  rcases le_or_gt 0 x₁ with h1 | h1
  · have h2 : 0 ≤ x₂ := le_trans h1 hx
    rw [eHi_density x₁ h1, eLo_density x₂ h2, eHi_density x₂ h2, eLo_density x₁ h1,
      show Real.exp (-x₁) * (2 * Real.exp (-(2 * x₂)))
          = 2 * Real.exp (-x₁ + -(2 * x₂)) by rw [Real.exp_add]; ring,
      show Real.exp (-x₂) * (2 * Real.exp (-(2 * x₁)))
          = 2 * Real.exp (-x₂ + -(2 * x₁)) by rw [Real.exp_add]; ring]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  · -- Below the support both densities vanish, so the off-diagonal factor is zero.
    rw [eHi_density_neg x₁ h1, eLo_density_neg x₁ h1]; simp

/-- **MLR dominance ⇒ FOSD.** `Exp(1)` first-order stochastically dominates `Exp(2)`. -/
theorem eHi_fosd : FOSD eHi.toProbDist eLo.toProbDist := mlrpLe_witness.fosd

/-- **MLR dominance ⇒ CDF tower** (`IntegratedCDFTower 1`): The dominant CDF lies weakly below. -/
theorem mlrpLe_tower : IntegratedCDFTower 1 eHi.cdf eLo.cdf :=
  mlrpLe_witness.integratedCDFTower_one

/-- The strict CDF gap at `x = 1`: `cdf_hi 1 = 1 - e^{-1} < 1 - e^{-2} = cdf_lo 1`. Drives the
strict expectation engine. -/
theorem cdf_gap : eHi.cdf 1 < eLo.cdf 1 := by
  rw [eHi, eLo, ContDist.exponential_cdf, ContDist.exponential_cdf]
  simp only [if_neg (by norm_num : ¬(1:ℝ) < 0)]
  linarith [Real.exp_lt_exp.mpr (show (-(2:ℝ) * 1) < (-(1:ℝ) * 1) by norm_num)]

end mlrp

section expectations

/-- `density · arctan` is integrable: `arctan` is bounded by `π/2`, the density is integrable. -/
private theorem arctan_integrable (d : ContDist) :
    Integrable (fun x => d.density x * Real.arctan x) := by
  refine Integrable.mono' (g := fun x => Real.pi / 2 * d.density x)
    (d.integrable.const_mul _)
    (d.integrable.aestronglyMeasurable.mul
      Real.continuous_arctan.measurable.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (d.nonneg x), mul_comm (Real.pi / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (d.nonneg x)
  rw [abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩

/-- **MLR dominance orders monotone expectations** (pairwise form). A monotone statistic is worth
weakly more under the dominant law: `E_{Exp(2)}[arctan] ≤ E_{Exp(1)}[arctan]`. The same direction
as the mean anchor `1/2 < 1`. -/
theorem mlrpLe_expect_mono : eLo.expect Real.arctan ≤ eHi.expect Real.arctan :=
  mlrpLe_witness.expect_mono Real.arctan Real.arctan_strictMono.monotone
    (arctan_integrable eLo) (arctan_integrable eHi)

/-- **FOSD orders monotone expectations** (the `ContDist` engine, fed the CDF tower directly). -/
theorem fosd_expect_mono : eLo.expect Real.arctan ≤ eHi.expect Real.arctan :=
  FOSD.expect_mono eHi eLo Real.arctan Real.arctan_strictMono.monotone
    mlrpLe_tower (arctan_integrable eHi) (arctan_integrable eLo)

/-- **Strict FOSD orders strictly monotone expectations strictly.** The strict CDF gap at `1` plus
strict monotonicity of `arctan` gives `E_{Exp(2)}[arctan] < E_{Exp(1)}[arctan]`. -/
theorem fosd_expect_strict_mono : eLo.expect Real.arctan < eHi.expect Real.arctan :=
  FOSD.expect_strict_mono eHi eLo Real.arctan Real.arctan_strictMono
    mlrpLe_tower ⟨1, cdf_gap⟩ (arctan_integrable eHi) (arctan_integrable eLo)

/-- **The characterization.** The CDF tower holds exactly when every monotone decision maker
prefers the dominant law. -/
theorem fosd_iff_witness :
    IntegratedCDFTower 1 eHi.cdf eLo.cdf ↔
    (∀ u : ℝ → ℝ, Monotone u → Integrable (fun x => eHi.density x * u x) →
      Integrable (fun x => eLo.density x * u x) → eLo.expect u ≤ eHi.expect u) :=
  FOSD.iff_expect_mono eHi eLo

end expectations

section measureTheoreticFOSD

/-- **Measure-theoretic FOSD reflexivity.** -/
theorem fosd_refl : FOSD eHi.toProbDist eHi.toProbDist := FOSD.refl _

/-- **Measure-theoretic FOSD transitivity** (through reflexivity). -/
theorem fosd_trans : FOSD eHi.toProbDist eLo.toProbDist := FOSD.trans eHi_fosd (FOSD.refl _)

/-- **Measure-theoretic FOSD antisymmetry** on a self-pair: Mutual dominance forces equality. -/
theorem fosd_antisymm : eHi.toProbDist = eHi.toProbDist :=
  FOSD.antisymm (FOSD.refl _) (FOSD.refl _)

/-- **The FOSD ⇔ `IntegratedCDFTower 1` bridge on `ProbDist ℝ`.** -/
theorem fosd_iff_tower :
    FOSD eHi.toProbDist eLo.toProbDist ↔
    IntegratedCDFTower 1 (CDF.ofProbDist eHi.toProbDist) (CDF.ofProbDist eLo.toProbDist) :=
  fosd_iff_integratedCDFTower_one _ _

/-- **The CDF bridge:** a `ContDist`'s integral CDF is the canonical CDF of its embedded law. -/
theorem cdf_eq_ofProbDist_witness : eHi.cdf = CDF.ofProbDist eHi.toProbDist :=
  eHi.cdf_eq_ofProbDist

end measureTheoreticFOSD

section ratioMonotone

/-- The exponential-family kernel `f x θ = exp(θ x)` — a positive density family with MLRP. -/
private abbrev expFam : ℝ → ℝ → ℝ := fun x θ => Real.exp (θ * x)

/-- **The kernel has the monotone likelihood ratio property.** After taking logs the cross
inequality is `θ₂x₁ + θ₁x₂ ≤ θ₂x₂ + θ₁x₁`, i.e. `0 ≤ (θ₂-θ₁)(x₂-x₁)`. -/
theorem expFam_mlrp : HasMonotoneLikelihoodRatio expFam := by
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [expFam]
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.2 hθ.le) (sub_nonneg.2 hx)])

/-- **The likelihood ratio is monotone.** For `θ₁ < θ₂`, `x ↦ exp(θ₂ x)/exp(θ₁ x) = exp((θ₂-θ₁)x)`
is increasing — the qualitative content of MLRP. -/
theorem expFam_ratioMonotone {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    Monotone (fun x => expFam x θ₂ / expFam x θ₁) :=
  expFam_mlrp.ratioMonotone hθ (fun _ => Real.exp_pos _)

/-- **The integrated cross inequality** (Fubini engine) on separated sets `Iic 1 ≤ Ioi 1`, driven by
the exponential `MLRPLe` cross inequality. The cutoff is the **positive** value `1`, not `0`: at the
zero cutoff both exponential densities vanish on `Iic 0` (a null lower tail), so the inequality
would degenerate to the tautology `0 ≤ 0` and catch no sign/orientation bug. At cutoff `1` the
masses are
all strictly positive — `∫_{Iic 1} eHi = 1 - e⁻¹`, `∫_{Ioi 1} eLo = e⁻²`, etc. — so the witness
reads `(1 - e⁻¹)·e⁻² ≤ e⁻¹·(1 - e⁻²)` with both sides nonzero. -/
theorem integrated_cross_witness :
    (∫ x in Iic (1:ℝ), eHi.density x) * (∫ x in Ioi (1:ℝ), eLo.density x) ≤
    (∫ x in Ioi (1:ℝ), eHi.density x) * (∫ x in Iic (1:ℝ), eLo.density x) :=
  mlrp_integrated_cross (g₁ := eLo.density) (g₂ := eHi.density)
    (fun x₁ x₂ hx => mlrpLe_witness x₁ x₂ hx) eLo.integrable eHi.integrable
    (Iic 1) (Ioi 1) measurableSet_Iic measurableSet_Ioi
    -- `_a` and `_b` are the set-membership witnesses; the values are only used through `ha`/`hb`
    (fun _a ha _b hb => le_trans ha (le_of_lt hb))

end ratioMonotone

section singleCrossing

/-- The Gaussian location family with unit variance: The textbook strict MLRP family. -/
private abbrev gLoc : ℝ → ContDist := fun θ => ContDist.gaussian θ 1 one_pos

/-- **The Gaussian location family is strictly MLRP.** The exponent gap `2(θ₂-θ₁)(x₂-x₁)/(2v) > 0`
is strictly positive, `exp` is strictly monotone, and the common constant `C² > 0` preserves the
strict inequality. -/
theorem gLoc_strict_mlrp : HasStrictMLRP gLoc := by
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [gLoc, ContDist.gaussian_density, gaussianPDFReal]
  set V : ℝ := (gaussianVarianceNNReal 1 one_pos : ℝ) with hV
  have hVpos : 0 < V := by rw [hV, gaussianVarianceNNReal_coe]; norm_num
  have h2V : (0 : ℝ) < 2 * V := by linarith
  set C : ℝ := (Real.sqrt (2 * Real.pi * V))⁻¹ with hC
  have hexp : -(x₁ - θ₂) ^ 2 / (2 * V) + -(x₂ - θ₁) ^ 2 / (2 * V)
            < -(x₂ - θ₂) ^ 2 / (2 * V) + -(x₁ - θ₁) ^ 2 / (2 * V) := by
    simp_rw [← add_div, div_lt_div_iff_of_pos_right h2V]
    nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hθ)]
  have hprod : Real.exp (-(x₁ - θ₂) ^ 2 / (2 * V)) * Real.exp (-(x₂ - θ₁) ^ 2 / (2 * V))
             < Real.exp (-(x₂ - θ₂) ^ 2 / (2 * V)) * Real.exp (-(x₁ - θ₁) ^ 2 / (2 * V)) := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_lt_exp.mpr hexp
  calc C * Real.exp (-(x₁ - θ₂) ^ 2 / (2 * V)) * (C * Real.exp (-(x₂ - θ₁) ^ 2 / (2 * V)))
      = C ^ 2 * (Real.exp (-(x₁ - θ₂) ^ 2 / (2 * V)) * Real.exp (-(x₂ - θ₁) ^ 2 / (2 * V))) := by
        ring
    _ < C ^ 2 * (Real.exp (-(x₂ - θ₂) ^ 2 / (2 * V)) * Real.exp (-(x₁ - θ₁) ^ 2 / (2 * V))) :=
        mul_lt_mul_of_pos_left hprod (by rw [hC]; positivity)
    _ = C * Real.exp (-(x₂ - θ₂) ^ 2 / (2 * V)) * (C * Real.exp (-(x₁ - θ₁) ^ 2 / (2 * V))) := by
        ring

/-- The supermodular primitive `u t x = arctan t · x`, with strict increasing differences:
`u θ₂ x₂ - u θ₂ x₁ - (u θ₁ x₂ - u θ₁ x₁) = (arctan θ₂ - arctan θ₁)(x₂ - x₁) > 0`. -/
private abbrev uPrim : ℝ → ℝ → ℝ := fun t x => Real.arctan t * x

theorem uPrim_strictIncrDiff : Econlib.Preferences.StrictIncreasingDifferences uPrim where
  strict_incr_diff θ₁ θ₂ x₁ x₂ hθ hx := by
    simp only [uPrim]
    nlinarith [Real.arctan_strictMono hθ, sub_pos.2 hx]

private theorem gLoc_int (θ x : ℝ) :
    Integrable (fun t => (gLoc θ).density t * uPrim t x) := by
  simpa [uPrim, mul_comm, mul_left_comm, mul_assoc] using (arctan_integrable (gLoc θ)).mul_const x

/-- **Strict MLRP ⇒ single crossing of interim payoffs.** With the strictly MLRP Gaussian family
and the supermodular primitive `arctan t · x`, the induced expected-payoff preferences
`θ ↦ ∫ density · u` satisfy ordinal single crossing — the Milgrom comparative-statics bridge. -/
theorem singleCrossingRel_witness :
    Econlib.Preferences.SingleCrossingRel
      (fun θ => Econlib.Preferences.preferenceOfRealUtility
        (fun x => ∫ t, (gLoc θ).density t * uPrim t x)) :=
  gLoc_strict_mlrp.singleCrossingRel gLoc gLoc_int uPrim_strictIncrDiff
    (fun θ => ⟨θ - 1, θ + 1, by linarith, fun t _ =>
      gaussianPDFReal_pos θ _ t (gaussianVarianceNNReal_ne_zero 1 one_pos)⟩)

end singleCrossing

/-! ## The finite slice: The FOSD complete lattice on `FinDist (Fin 3)` -/

section finLattice

/-- The dominant finite law (mass on high outcomes); CDF `(1/6, 1/2, 1)`. -/
private abbrev dHi : FinDist (Fin 3) := finDist% ![1 / 6, 1 / 3, 1 / 2]

/-- The dominated finite law (mass on low outcomes); CDF `(1/2, 5/6, 1)`. -/
private abbrev dLo : FinDist (Fin 3) := finDist% ![1 / 2, 1 / 3, 1 / 6]

/-- The CDF vector of `dHi`. -/
private abbrev cHi : Fin 3 → ℝ := ![1 / 6, 1 / 2, 1]

private theorem cHi_mono : Monotone cHi := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> (simp_all [cHi, Fin.le_def]; try norm_num)

private theorem cHi_nn : ∀ k, 0 ≤ cHi k := by intro k; fin_cases k <;> simp [cHi]

private theorem cHi_max : cHi (univ.max' univ_nonempty) = 1 := by
  rw [show (univ.max' univ_nonempty : Fin 3) = 2 by decide]; rfl

private theorem cHi_last : cHi ⟨3 - 1, by norm_num⟩ = 1 := by norm_num [cHi]

/-- **`ofCdfVec` recovers the PMF by differencing the CDF.** From the CDF vector `cHi = (1/6,1/2,1)`
the recovered masses are `pmf 0 = cHi 0 = 1/6`, `pmf 1 = cHi 1 - cHi 0 = 1/2 - 1/6 = 1/3`,
`pmf 2 = cHi 2 - cHi 1 = 1 - 1/2 = 1/2` — i.e. exactly `dHi`'s masses. These concrete values are the
load-bearing recovery facts (a broken differencing or an off-by-one in the predecessor index would
change them); the previous witness only proved `True`. -/
theorem ofCdfVec_pmf_zero : (FinDist.ofCdfVec cHi cHi_mono cHi_nn cHi_last).pmf 0 = 1 / 6 := by
  simp only [FinDist.ofCdfVec, cHi, Matrix.cons_val_zero]; norm_num

theorem ofCdfVec_pmf_one : (FinDist.ofCdfVec cHi cHi_mono cHi_nn cHi_last).pmf 1 = 1 / 3 := by
  simp only [FinDist.ofCdfVec, cHi, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num

theorem ofCdfVec_pmf_two : (FinDist.ofCdfVec cHi cHi_mono cHi_nn cHi_last).pmf 2 = 1 / 2 := by
  simp only [FinDist.ofCdfVec, cHi, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]; norm_num

/-- The distribution recovered from `cHi` via the order-isomorphism transport. -/
private abbrev recovered : FinDist (Fin 3) := FinDist.ofCdf cHi cHi_mono cHi_nn cHi_max

/-- **`ofCdf` recovers the CDF:** the recovered distribution's CDF is exactly `cHi`. -/
theorem recovered_cdf : recovered.cdf = cHi := FinDist.ofCdf_cdf cHi cHi_mono cHi_nn cHi_max

private theorem dHi_cdf_eq : dHi.cdf = cHi := by
  funext k; fin_cases k <;>
    simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dHi, FinDist.ofVec_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.le_def, cHi] <;> norm_num

/-- **CDF injectivity:** `dHi` is the unique distribution with CDF `cHi` — the recovered one equals
it. -/
theorem recovered_eq_dHi : recovered = dHi :=
  FinDist.cdf_injective (fun _ => by rw [recovered_cdf, ← dHi_cdf_eq])

/-- The canonical order isomorphism `Fin (card (Fin 3)) ≃o Fin 3`. -/
private abbrev e3 : Fin (Fintype.card (Fin 3)) ≃o Fin 3 := Fintype.orderIsoFinOfCardEq (Fin 3) rfl

/-- **The pullback's CDF transports** along the order iso:
`(pullback e dHi).cdf k = dHi.cdf (e k)`. -/
theorem pullback_cdf_witness (k : Fin (Fintype.card (Fin 3))) :
    (FinDist.pullback e3 dHi).cdf k = dHi.cdf (e3 k) :=
  FinDist.pullback_cdf e3 dHi k

/-- `dHi` FOSD-dominates `dLo`: Lower CDF at every cutoff. -/
private theorem dHi_fosd_dLo : FinDist.FOSD dHi dLo := by
  rw [FinDist.FOSD_iff]; intro a
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three]
  fin_cases a <;>
    simp only [dHi, dLo, FinDist.ofVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.le_def] <;> norm_num

/-- **FOSD reflexivity** (lattice form). -/
theorem fosd_refl_fin : FinDist.FOSD dHi dHi := FinDist.FOSD_refl dHi

/-- **FOSD transitivity** (lattice form, through reflexivity). -/
theorem fosd_trans_fin : FinDist.FOSD dHi dLo :=
  FinDist.FOSD_trans dHi_fosd_dLo (FinDist.FOSD_refl dLo)

/-- **FOSD antisymmetry forces equality of distinct presentations.** `recovered` (built from `cHi`
via `ofCdf`) and `dHi` (built from its mass vector) are *syntactically distinct* `FinDist (Fin 3)`
objects with the same law. Mutual FOSD between them — which holds because they are equal,
transported through `recovered_eq_dHi` — forces `recovered = dHi` by antisymmetry. Unlike a
reflexive self-pair,
this exercises antisymmetry on objects that are not definitionally the same term. -/
theorem fosd_antisymm_fin : recovered = dHi := by
  have h1 : FinDist.FOSD recovered dHi := recovered_eq_dHi ▸ FinDist.FOSD_refl dHi
  have h2 : FinDist.FOSD dHi recovered := recovered_eq_dHi ▸ FinDist.FOSD_refl dHi
  exact FinDist.FOSD_antisymm h1 h2

/-- **The FOSD partial order.** `dLo ≤ dHi` (the FOSD-dominant law is the larger element); a
reversed convention would put `dHi ≤ dLo`. -/
theorem dLo_le_dHi : dLo ≤ dHi := (FinDist.le_iff_fosd dLo dHi).mpr dHi_fosd_dLo

/-- **`≤` is CDF-reversal:** `dLo ≤ dHi` iff `dHi`'s CDF lies below `dLo`'s everywhere. -/
theorem le_iff_cdf_witness : dLo ≤ dHi ↔ ∀ k, dHi.cdf k ≤ dLo.cdf k :=
  FinDist.le_iff_cdf_ge dLo dHi

/-- **The complete-lattice supremum.** `fosdsSup {dHi, dLo}` is the least FOSD-upper bound of the
pair — the pointwise infimum of their CDFs. -/
theorem sup_pair_isLUB :
    IsLUB ({dHi, dLo} : Set (FinDist (Fin 3))) (FinDist.fosdsSup {dHi, dLo}) :=
  FinDist.isLUB_fosdsSup {dHi, dLo}

/-- **The concrete supremum value.** Since `dLo ≤ dHi` in the FOSD order, the FOSD-dominant `dHi` is
itself the least upper bound of the comparable pair: `fosdsSup {dHi, dLo} = dHi`. This computes the
sup (the semantic anchor) rather than merely restating the abstract `isLUB` property. -/
theorem sup_pair_eq_dHi : FinDist.fosdsSup ({dHi, dLo} : Set (FinDist (Fin 3))) = dHi := by
  -- `dHi` is an upper bound of `{dHi, dLo}` (it dominates `dLo`) and lies in the set, hence is the
  -- LUB; uniqueness of LUB then identifies it with `fosdsSup`.
  have hdHi_lub : IsLUB ({dHi, dLo} : Set (FinDist (Fin 3))) dHi := by
    constructor
    · intro d hd
      rcases hd with hd | hd
      · exact hd ▸ le_refl dHi
      · exact hd ▸ dLo_le_dHi
    · intro d hd
      exact hd (Set.mem_insert dHi {dLo})
  exact (FinDist.isLUB_fosdsSup {dHi, dLo}).unique hdHi_lub

end finLattice

end EconlibTest.Probability.Order.MLRP

end
