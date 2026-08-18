/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexRightDeriv
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.MyersonLemma
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.PaymentFormula

/-!
# Single-parameter screening: The envelope (payment) formula

The **envelope theorem** for single-parameter screening: Under incentive compatibility, the interim
utility is determined by the allocation up to its value at the lowest type,

`U(θ) = U(θlo) + ∫_{θlo}^θ x(s) ds`.

## Main statements

* `DirectMechanism.sub_mul_le_interimUtil_sub`: Lower incentive sandwich
  `(t − r)·x(r) ≤ U(t) − U(r)`.
* `DirectMechanism.interimUtil_sub_le_sub_mul`: Upper incentive sandwich
  `U(t) − U(r) ≤ (t − r)·x(t)`.
* `DirectMechanism.interimUtil_eq_integral`: The envelope formula
  `U(θ) = U(θlo) + ∫_{θlo}^θ x(s) ds`.

## References

* Mussa, Michael, and Sherwin Rosen. 1978. “Monopoly and Product Quality.” *Journal of Economic
  Theory* 18 (2): 301–17. [https://doi.org/10.1016/0022-0531(78)90085-6](https://doi.org/10.1016/0022-0531(78)90085-6).
* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

screening, envelope theorem, incentive compatibility, interim utility
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace DirectMechanism

variable {E : ScreeningEnv} (M : DirectMechanism E)

/-- **Incentive sandwich, lower bound.** From `IsBIC`, for any types `r, t`:
`(t − r)·x(r) ≤ U(t) − U(r)`. -/
lemma sub_mul_le_interimUtil_sub (hbic : IsBIC M) {r t : ℝ} (hr : r ∈ E.types)
    (ht : t ∈ E.types) : (t - r) * M.x r ≤ M.interimUtil t - M.interimUtil r := by
  have h := hbic t ht r hr
  simp only [reportUtil_def, interimUtil_def] at h ⊢
  nlinarith [h]

/-- **Incentive sandwich, upper bound.** From `IsBIC`, for any types `r, t`:
`U(t) − U(r) ≤ (t − r)·x(t)`. -/
lemma interimUtil_sub_le_sub_mul (hbic : IsBIC M) {r t : ℝ} (hr : r ∈ E.types)
    (ht : t ∈ E.types) : M.interimUtil t - M.interimUtil r ≤ (t - r) * M.x t := by
  have h := hbic r hr t ht
  simp only [reportUtil_def, interimUtil_def] at h ⊢
  nlinarith [h]

/-- **Envelope formula** (Myerson 1981). Under `IsBIC`, the on-path interim utility is determined
by the allocation up to its value at the lowest type: `U(θ) = U(θlo) + ∫_{θlo}^θ x(s) ds`. -/
theorem interimUtil_eq_integral (hbic : IsBIC M) {θ : ℝ} (hθ : θ ∈ E.types) :
    M.interimUtil θ = M.interimUtil E.θlo + ∫ s in E.θlo..θ, M.x s := by
  set a := E.θlo with ha_def
  set b := E.θhi with hb_def
  have hab : a < b := E.hθ
  set U := M.interimUtil with hU_def
  set x := M.x with hx_def
  have hconv : ConvexOn ℝ (Icc a b) U := M.interimUtil_convexOn hbic
  have hmono : MonotoneAlloc M.alloc := M.isBIC_implies_monotone hbic
  have hxmono : MonotoneOn x (Icc a b) := hmono
  have hUmono : MonotoneOn U (Icc a b) := by
    intro θ₁ hθ₁ θ₂ hθ₂ hle
    have hsand := M.sub_mul_le_interimUtil_sub hbic hθ₁ hθ₂
    have hxnn : 0 ≤ x θ₁ := M.x_nonneg θ₁
    nlinarith [hsand, hxnn, sub_nonneg.mpr hle]
  have hcont : ContinuousOn U (Icc a b) := by
    have hlip : LipschitzOnWith 1 U (Icc a b) := by
      have hdist : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b, dist (U p) (U q) ≤ (1 : ℝ) * dist p q := by
        intro p hp q hq
        rw [Real.dist_eq, Real.dist_eq, one_mul, abs_le]
        rcases le_total p q with hpq | hpq
        · rw [abs_of_nonpos (by linarith)]
          have hlo : (q - p) * x p ≤ U q - U p := M.sub_mul_le_interimUtil_sub hbic hp hq
          have hhi : U q - U p ≤ (q - p) * x q := M.interimUtil_sub_le_sub_mul hbic hp hq
          have hx0 : 0 ≤ x p := M.x_nonneg p
          have hx1 : x q ≤ 1 := M.x_le_one q
          constructor <;> nlinarith [hlo, hhi, sub_nonneg.mpr hpq]
        · rw [abs_of_nonneg (by linarith)]
          have hlo : (p - q) * x q ≤ U p - U q := M.sub_mul_le_interimUtil_sub hbic hq hp
          have hhi : U p - U q ≤ (p - q) * x p := M.interimUtil_sub_le_sub_mul hbic hq hp
          have hx0 : 0 ≤ x q := M.x_nonneg q
          have hx1 : x p ≤ 1 := M.x_le_one p
          constructor <;> nlinarith [hlo, hhi, sub_nonneg.mpr hpq]
      simpa using LipschitzOnWith.of_dist_le' hdist
    exact hlip.continuousOn
  -- `x s ≤ D⁺U(s)`: the right derivative dominates the allocation, from the lower sandwich.
  -- Shared by the `BddBelow` bound and the pointwise identity at right-continuity points.
  have hderiv_lo : ∀ s ∈ Ioo a b, x s ≤ derivWithin U (Ioi s) s := by
    intro s hs
    have hsint : s ∈ interior (Icc a b) := by rw [interior_Icc]; exact hs
    rw [hconv.rightDeriv_eq_sInf_slope_of_mem_interior hsint]
    refine le_csInf ⟨slope U s b, ⟨b, ⟨⟨hab.le, le_refl b⟩, hs.2⟩, rfl⟩⟩ ?_
    rintro d ⟨y, ⟨hy, hsy⟩, rfl⟩
    rw [slope_def_field, le_div_iff₀ (by linarith)]
    have := M.sub_mul_le_interimUtil_sub hbic ⟨hs.1.le, hs.2.le⟩ hy
    nlinarith [this]
  have hbb : BddBelow ((fun s => derivWithin U (Ioi s) s) '' Ioo a b) := by
    refine ⟨0, ?_⟩
    rintro c ⟨s, hs, rfl⟩
    linarith [M.x_nonneg s, hderiv_lo s hs]
  have hba : BddAbove ((fun s => derivWithin U (Ioi s) s) '' Ioo a b) := by
    refine ⟨1, ?_⟩
    rintro c ⟨s, hs, rfl⟩
    have hsint : s ∈ interior (Icc a b) := by rw [interior_Icc]; exact hs
    have hslope : derivWithin U (Ioi s) s ≤ slope U s b :=
      hconv.rightDeriv_le_slope_of_mem_interior hsint ⟨hab.le, le_refl b⟩ hs.2
    have hsand := M.interimUtil_sub_le_sub_mul hbic ⟨hs.1.le, hs.2.le⟩
      ⟨hab.le, le_refl b⟩
    have hsb : slope U s b ≤ x b := by
      rw [slope_def_field, div_le_iff₀ (by linarith [hs.2])]
      nlinarith [hsand]
    linarith [hslope, hsb, M.x_le_one b]
  -- `D⁺U(s) = x s` at right-continuity points of `x`; used below to establish the a.e. identity.
  have hpoint : ∀ s ∈ Ioo a b, ContinuousWithinAt x (Icc a b ∩ Ioi s) s →
      derivWithin U (Ioi s) s = x s := by
    intro s hs hrc
    have hsint : s ∈ interior (Icc a b) := by rw [interior_Icc]; exact hs
    have hslope_hi : ∀ y ∈ Icc a b, s < y → slope U s y ≤ x y := by
      intro y hy hsy
      have hsand := M.interimUtil_sub_le_sub_mul hbic ⟨hs.1.le, hs.2.le⟩ hy
      rw [slope_def_field, div_le_iff₀ (by linarith)]
      nlinarith [hsand]
    have hlo : x s ≤ derivWithin U (Ioi s) s := hderiv_lo s hs
    have hhi : derivWithin U (Ioi s) s ≤ x s := by
      have htend : Filter.Tendsto x (nhdsWithin s (Icc a b ∩ Ioi s)) (nhds (x s)) := hrc
      have hsub : Ioo s b ⊆ Icc a b ∩ Ioi s := by
        rintro y ⟨hsy, hyb⟩
        exact ⟨⟨le_of_lt (lt_trans hs.1 hsy), hyb.le⟩, hsy⟩
      have hne : (nhdsWithin s (Icc a b ∩ Ioi s)).NeBot :=
        (left_nhdsWithin_Ioo_neBot hs.2).mono (nhdsWithin_mono s hsub)
      refine ge_of_tendsto htend ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hys : s < y := hy.2
      have hyb : y ∈ Icc a b := hy.1
      calc derivWithin U (Ioi s) s
          ≤ slope U s y := hconv.rightDeriv_le_slope_of_mem_interior hsint hyb hys
        _ ≤ x y := hslope_hi y hyb hys
    linarith
  have hae : ∀ᵐ s : ℝ, s ∈ uIoc a θ → derivWithin U (Ioi s) s = x s := by
    -- A monotone function is right-continuous off a countable set, so the exceptional set is null.
    have hbad : {s : ℝ | s ∈ Icc a b ∧ ¬ContinuousWithinAt x (Icc a b ∩ Ioi s) s}.Countable :=
      hxmono.countable_not_continuousWithinAt_Ioi
    have hcount : ({s : ℝ | s ∈ Icc a b ∧ ¬ContinuousWithinAt x (Icc a b ∩ Ioi s) s} ∪
        {b}).Countable := hbad.union (Set.countable_singleton b)
    filter_upwards [hcount.ae_notMem volume] with s hs_notbad hs_mem
    have hθb : θ ≤ b := hθ.2
    have hθa : a ≤ θ := hθ.1
    rw [Set.uIoc_of_le hθa] at hs_mem
    have hsa : a < s := hs_mem.1
    have hsb : s ≤ b := le_trans hs_mem.2 hθb
    have hsne_b : s ≠ b := fun h => hs_notbad (Or.inr (by simp [h]))
    have hs_lt_b : s < b := lt_of_le_of_ne hsb hsne_b
    have hsoo : s ∈ Ioo a b := ⟨hsa, hs_lt_b⟩
    have hrc : ContinuousWithinAt x (Icc a b ∩ Ioi s) s := by
      by_contra hc
      exact hs_notbad (Or.inl ⟨⟨hsa.le, hsb⟩, hc⟩)
    exact hpoint s hsoo hrc
  have hcongr : (∫ s in a..θ, derivWithin U (Ioi s) s) = ∫ s in a..θ, x s :=
    intervalIntegral.integral_congr_ae hae
  have hftc : (∫ s in a..θ, derivWithin U (Ioi s) s) = U θ - U a :=
    hconv.ftc_rightDeriv hab hcont hbb hba hθ.1 hθ.2
  rw [hcongr] at hftc
  linarith [hftc]

end DirectMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
