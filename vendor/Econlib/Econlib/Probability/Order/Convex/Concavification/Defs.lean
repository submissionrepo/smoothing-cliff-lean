/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.Defs
public import Econlib.Probability.ContDist.ProbDist
public import Econlib.Probability.Distributions.Bernoulli
public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.Order.Convex.Basic
public import Econlib.Probability.Order.Convex.Duality

/-!
# Two-point laws and affine-majorant expectation bounds

Probability layer over the pure affine/contact-set core
(`Econlib.Math.Analysis.Concavification1D.Defs`). Introduces the **two-point law** with right-atom
weight `q` and atoms `xL, xR`, and the expectation bounds against affine majorants that drive the
1D concavification argument behind Bayesian persuasion (Kamenica and Gentzkow 2011).

## Main definitions

* `twoPointLaw q xL xR hq0 hq1` — the Bernoulli mixture of `dirac xL`, `dirac xR`.

## Main statements

* `twoPointLaw_expect`, `twoPointLaw_expect_id`, `twoPointLaw_supportsOn_Icc` — the two-point law's
  expectations and support.
* `expect_le_affineFun_of_supportsOn_Icc`, `expect_le_affineFun_of_convexOrderOnIcc` — affine
  majorants bound expectations.
* `expect_le_twoPointLaw_of_affineMajorant` — a supported distribution is dominated by the
  barycentric two-point law on a contact-touching majorant.
* `supportsOn_contactSet_of_expect_eq_affineFun`,
  `supportsOn_contactSet_of_convexOrder_eq_affineFun` — equality forces support on the contact set.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

two-point law, affine majorant, contact set, concavification, convex order, bayesian persuasion
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- Two-point law with right-atom weight `q`. -/
noncomputable def twoPointLaw (q xL xR : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ProbDist ℝ :=
  ProbDist.finMixture (FinDist.bernoulli q hq0 hq1)
    (fun i : Fin 2 => ProbDist.dirac (if i = 0 then xL else xR))

lemma ProbDist.expect_affineFun_eq_of_supportsOn_Icc {d : ProbDist ℝ} {a b m c : ℝ}
    (hsupp : d.supportsOn (Icc a b)) :
    d.expect (affineFun m c) = affineFun m c (d.expect id) := by
  have hid : Integrable id d.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc hsupp
  calc
    d.expect (affineFun m c) = ∫ x, (m * x + c) ∂d.toMeasure := by rfl
    _ = ∫ x, (m * x) ∂d.toMeasure + ∫ x, c ∂d.toMeasure := by
          rw [integral_add]
          · exact hid.const_mul m
          · simp
    _ = m * ∫ x, x ∂d.toMeasure + ∫ x, c ∂d.toMeasure := by
          rw [integral_const_mul]
    _ = m * d.expect id + c := by
          simp [ProbDist.expect]

lemma twoPointLaw_expect (q xL xR : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (φ : ℝ → ℝ) :
    (twoPointLaw q xL xR hq0 hq1).expect φ = (1 - q) * φ xL + q * φ xR := by
  rw [twoPointLaw, ProbDist.expect_finMixture]
  · simp only [ProbDist.expect_dirac]
    rw [Fin.sum_univ_two]
    simp [FinDist.bernoulli]
  · intro i
    fin_cases i
    · simpa [ProbDist.dirac] using
        (MeasureTheory.integrable_dirac (a := xL) (f := φ) (by simp : ‖φ xL‖ₑ < ⊤))
    · simpa [ProbDist.dirac] using
        (MeasureTheory.integrable_dirac (a := xR) (f := φ) (by simp : ‖φ xR‖ₑ < ⊤))

lemma twoPointLaw_expect_id (q xL xR : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoPointLaw q xL xR hq0 hq1).expect id = (1 - q) * xL + q * xR := by
  simpa using twoPointLaw_expect q xL xR hq0 hq1 id

lemma twoPointLaw_supportsOn_Icc (q xL xR a b : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hxL : xL ∈ Icc a b) (hxR : xR ∈ Icc a b) :
    (twoPointLaw q xL xR hq0 hq1).supportsOn (Icc a b) := by
  unfold ProbDist.supportsOn twoPointLaw ProbDist.finMixture ProbDist.dirac
  simp only [Fin.isValue, ProbabilityMeasure.coe_mk, Fin.sum_univ_two, ↓reduceIte, one_ne_zero,
    Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measurableSet_Icc,
    Measure.dirac_apply', smul_eq_mul, FinDist.bernoulli]
  rw [Set.indicator_of_mem hxL, Set.indicator_of_mem hxR]
  norm_num
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hq1) hq0]
  norm_num

lemma expect_le_affineFun_of_supportsOn_Icc {d : ProbDist ℝ} {a b m c : ℝ} {φ : ℝ → ℝ}
    (hsupp : d.supportsOn (Icc a b))
    (hmajor : ∀ x ∈ Icc a b, φ x ≤ affineFun m c x)
    (hφ : Continuous φ) :
    d.expect φ ≤ affineFun m c (d.expect id) := by
  have hφ_int : Integrable φ d.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hsupp hφ.continuousOn
  have haff_int : Integrable (affineFun m c) d.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hsupp (affineFun_continuous m c).continuousOn
  have hae : ∀ᵐ x ∂d.toMeasure, φ x ≤ affineFun m c x := by
    filter_upwards [ProbDist.ae_mem_of_supportsOn measurableSet_Icc hsupp] with x hx
    exact hmajor x hx
  calc
    d.expect φ ≤ d.expect (affineFun m c) := integral_mono_ae hφ_int haff_int hae
    _ = affineFun m c (d.expect id) :=
      ProbDist.expect_affineFun_eq_of_supportsOn_Icc hsupp

lemma expect_le_affineFun_of_convexOrderOnIcc {a b m c : ℝ} {ν μ : ProbDist ℝ} {φ : ℝ → ℝ}
    (hcx : ConvexOrderOnIcc a b ν μ)
    (hmajor : ∀ x ∈ Icc a b, φ x ≤ affineFun m c x)
    (hφ : Continuous φ) :
    ν.expect φ ≤ affineFun m c (μ.expect id) := by
  calc
    ν.expect φ ≤ affineFun m c (ν.expect id) :=
      expect_le_affineFun_of_supportsOn_Icc hcx.support_left hmajor hφ
    _ = affineFun m c (μ.expect id) := by rw [hcx.mean_eq]

lemma twoPointLaw_expect_affineFun (q xL xR m c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoPointLaw q xL xR hq0 hq1).expect (affineFun m c) =
      affineFun m c ((1 - q) * xL + q * xR) := by
  calc
    (twoPointLaw q xL xR hq0 hq1).expect (affineFun m c)
      = (1 - q) * affineFun m c xL + q * affineFun m c xR := by
          simpa using twoPointLaw_expect q xL xR hq0 hq1 (affineFun m c)
    _ = affineFun m c ((1 - q) * xL + q * xR) := by
          unfold affineFun
          ring

lemma twoPointLaw_expect_eq_affineFun_of_contact
    (q xL xR m c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {φ : ℝ → ℝ}
    (hxL : φ xL = affineFun m c xL) (hxR : φ xR = affineFun m c xR) :
    (twoPointLaw q xL xR hq0 hq1).expect φ =
      affineFun m c ((1 - q) * xL + q * xR) := by
  calc
    (twoPointLaw q xL xR hq0 hq1).expect φ
      = (1 - q) * φ xL + q * φ xR := by
          simpa using twoPointLaw_expect q xL xR hq0 hq1 φ
    _ = (1 - q) * affineFun m c xL + q * affineFun m c xR := by rw [hxL, hxR]
    _ = affineFun m c ((1 - q) * xL + q * xR) := by
          unfold affineFun
          ring

lemma twoPointLaw_expect_eq_of_barycentric_contact
    {xL xR μ m c : ℝ} (hx : xL < xR) {φ : ℝ → ℝ}
    (hμ : μ ∈ Icc xL xR)
    (hxL_contact : φ xL = affineFun m c xL)
    (hxR_contact : φ xR = affineFun m c xR) :
    let q := (μ - xL) / (xR - xL)
    (twoPointLaw q xL xR
      (by
        dsimp [q]
        have hden : 0 < xR - xL := sub_pos.mpr hx
        exact div_nonneg (sub_nonneg.mpr hμ.1) (le_of_lt hden))
      (by
        dsimp [q]
        have hden : 0 < xR - xL := sub_pos.mpr hx
        have hnum : μ - xL ≤ xR - xL := sub_le_sub_right hμ.2 xL
        exact (div_le_one hden).2 hnum)).expect φ = affineFun m c μ := by
  dsimp
  have hden : 0 < xR - xL := sub_pos.mpr hx
  have hq0 : 0 ≤ (μ - xL) / (xR - xL) :=
    div_nonneg (sub_nonneg.mpr hμ.1) (le_of_lt hden)
  have hq1 : (μ - xL) / (xR - xL) ≤ 1 := by
    have hnum : μ - xL ≤ xR - xL := sub_le_sub_right hμ.2 xL
    exact (div_le_one hden).2 hnum
  rw [twoPointLaw_expect_eq_affineFun_of_contact _ _ _ _ _ hq0 hq1 hxL_contact hxR_contact]
  unfold affineFun
  field_simp [ne_of_gt hden]
  ring

theorem expect_le_twoPointLaw_of_affineMajorant
    {d : ProbDist ℝ} {a b xL xR m c : ℝ} {φ : ℝ → ℝ}
    (hsupp : d.supportsOn (Icc a b))
    (hmajor : ∀ x ∈ Icc a b, φ x ≤ affineFun m c x)
    (hφ : Continuous φ) (hx : xL < xR)
    -- kept to specify that xL, xR lie in the support interval, matching hmajor's domain
    (_hxL : xL ∈ Icc a b) (_hxR : xR ∈ Icc a b)
    (hcontactL : φ xL = affineFun m c xL)
    (hcontactR : φ xR = affineFun m c xR)
    (hmean : d.expect id ∈ Icc xL xR) :
    let q := (d.expect id - xL) / (xR - xL)
    d.expect φ ≤ (twoPointLaw q xL xR
      (by
        dsimp [q]
        have hden : 0 < xR - xL := sub_pos.mpr hx
        exact div_nonneg (sub_nonneg.mpr hmean.1) (le_of_lt hden))
      (by
        dsimp [q]
        have hden : 0 < xR - xL := sub_pos.mpr hx
        have hnum : d.expect id - xL ≤ xR - xL := sub_le_sub_right hmean.2 xL
        exact (div_le_one hden).2 hnum)).expect φ := by
  dsimp
  have hbound := expect_le_affineFun_of_supportsOn_Icc hsupp hmajor hφ
  have htpeq := twoPointLaw_expect_eq_of_barycentric_contact hx hmean hcontactL hcontactR
  exact hbound.trans (by simpa using htpeq.symm.le)

theorem supportsOn_contactSet_of_expect_eq_affineFun
    {d : ProbDist ℝ} {a b m c : ℝ} {φ : ℝ → ℝ}
    (hsupp : d.supportsOn (Icc a b))
    (hmajor : ∀ x ∈ Icc a b, φ x ≤ affineFun m c x)
    (hφ : Continuous φ)
    (heq : d.expect φ = affineFun m c (d.expect id)) :
    d.supportsOn (contactSet a b φ m c) := by
  -- Route through the general convex-order contact certificate, taking the dominating prior to be
  -- `d` itself (reflexive convex order). The affine price is a convex majorant, and its prior
  -- expectation collapses to `affineFun m c (d.expect id)` by the affine-expectation lemma, so the
  -- equality hypothesis is exactly the dual certificate.
  let vPay : Order.Convex.Duality.PayoffOnIcc a b := ⟨φ, hφ.continuousOn⟩
  let pPay : Order.Convex.Duality.PayoffOnIcc a b :=
    ⟨affineFun m c, (affineFun_continuous m c).continuousOn⟩
  have hp : Order.Convex.Duality.IsConvexMajorantOnIcc a b vPay pPay :=
    ⟨convexOn_affineFun a b m c, hmajor⟩
  have heq' : d.expect vPay = Order.Convex.Duality.dualObjectiveConvexOrder d pPay := by
    change d.expect φ = d.expect (affineFun m c)
    rw [ProbDist.expect_affineFun_eq_of_supportsOn_Icc hsupp]
    exact heq
  exact Order.Convex.Duality.supportsOn_contactSet_of_eq_dualCertificate
    (ConvexOrderOnIcc.refl hsupp) hp heq'

theorem supportsOn_contactSet_of_convexOrder_eq_affineFun
    {a b m c : ℝ} {ν μ : ProbDist ℝ} {φ : ℝ → ℝ}
    (hcx : ConvexOrderOnIcc a b ν μ)
    (hmajor : ∀ x ∈ Icc a b, φ x ≤ affineFun m c x)
    (hφ : Continuous φ)
    (heq : ν.expect φ = affineFun m c (μ.expect id)) :
    ν.supportsOn (contactSet a b φ m c) := by
  have heq' : ν.expect φ = affineFun m c (ν.expect id) := by simpa [hcx.mean_eq] using heq
  exact supportsOn_contactSet_of_expect_eq_affineFun hcx.support_left hmajor hφ heq'

end Econlib.Probability
