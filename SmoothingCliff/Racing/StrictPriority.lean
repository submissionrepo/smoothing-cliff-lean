import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic

/-!
# The two-bidder strict-priority race

This file formalizes the pure-strategy part of Proposition `prop:sp_race` in
*Smoothing the Cliff*.  An action is a nonnegative real latency investment.
The contested band is `gap = v - r`, and the payoff below is exactly

`w₁ min ((aᵢ-aⱼ)⁺) (v-r) - κ aᵢ`.

Best responses quantify over every nonnegative real deviation; Nash
equilibrium is therefore not assumed as an input to any classification result.
-/

namespace SmoothingCliff.Racing

/-- The amount of the contested band captured by an investment lead. -/
def strictPriorityCapturedGap (gap own rival : ℝ) : ℝ :=
  min (max (own - rival) 0) gap

/-- Utility in the common-value two-bidder strict-priority race. -/
def strictPriorityPayoff
    (slotWeight gap marginalCost own rival : ℝ) : ℝ :=
  slotWeight * strictPriorityCapturedGap gap own rival - marginalCost * own

/-- `own` is a best response to `rival` among all nonnegative investments. -/
def StrictPriorityBestResponse
    (slotWeight gap marginalCost own rival : ℝ) : Prop :=
  0 ≤ own ∧
    ∀ deviation : ℝ, 0 ≤ deviation →
      strictPriorityPayoff slotWeight gap marginalCost deviation rival ≤
        strictPriorityPayoff slotWeight gap marginalCost own rival

/-- Pure Nash equilibrium of the two-bidder strict-priority race. -/
def StrictPriorityPureNash
    (slotWeight gap marginalCost first second : ℝ) : Prop :=
  StrictPriorityBestResponse slotWeight gap marginalCost first second ∧
    StrictPriorityBestResponse slotWeight gap marginalCost second first

/-- Total resources burned by a pure action profile. -/
def strictPriorityDissipation (marginalCost first second : ℝ) : ℝ :=
  marginalCost * (first + second)

/-- Against a nonnegative rival, the captured gap never exceeds one's action. -/
theorem strictPriorityCapturedGap_le_own
    {gap own rival : ℝ} (hown : 0 ≤ own)
    (hrival : 0 ≤ rival) :
    strictPriorityCapturedGap gap own rival ≤ own := by
  unfold strictPriorityCapturedGap
  apply min_le_of_left_le
  exact max_le (by linarith) hown

theorem strictPriorityCapturedGap_nonneg
    {gap own rival : ℝ} (hgap : 0 ≤ gap) :
    0 ≤ strictPriorityCapturedGap gap own rival := by
  exact le_min (le_max_right _ _) hgap

@[simp] theorem strictPriorityPayoff_zero
    (slotWeight gap marginalCost rival : ℝ) (hgap : 0 ≤ gap)
    (hrival : 0 ≤ rival) :
    strictPriorityPayoff slotWeight gap marginalCost 0 rival = 0 := by
  simp [strictPriorityPayoff, strictPriorityCapturedGap, hgap, hrival]

@[simp] theorem strictPriorityCapturedGap_at_band
    (gap rival : ℝ) (hgap : 0 ≤ gap) :
    strictPriorityCapturedGap gap (rival + gap) rival = gap := by
  simp [strictPriorityCapturedGap, hgap]

theorem strictPriorityPayoff_at_band
    (slotWeight gap marginalCost rival : ℝ) (hgap : 0 ≤ gap) :
    strictPriorityPayoff slotWeight gap marginalCost (rival + gap) rival =
      (slotWeight - marginalCost) * gap - marginalCost * rival := by
  rw [strictPriorityPayoff, strictPriorityCapturedGap_at_band gap rival hgap]
  ring

/-- On the part of the action space strictly above the rival, the peak occurs
at a lead of exactly one contested band. -/
theorem strictPriorityPayoff_le_payoff_at_band
    {slotWeight gap marginalCost own rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight)
    (hlead : rival < own) :
    strictPriorityPayoff slotWeight gap marginalCost own rival ≤
      strictPriorityPayoff slotWeight gap marginalCost (rival + gap) rival := by
  by_cases hwithin : own - rival ≤ gap
  · have hpositive : 0 ≤ own - rival := le_of_lt (sub_pos.mpr hlead)
    rw [strictPriorityPayoff, strictPriorityPayoff,
      strictPriorityCapturedGap, strictPriorityCapturedGap]
    rw [max_eq_left hpositive, min_eq_left hwithin]
    have hband : rival + gap - rival = gap := by ring
    rw [hband, max_eq_left (le_of_lt hgap), min_self]
    nlinarith
  · have hbeyond : gap ≤ own - rival := le_of_not_ge hwithin
    rw [strictPriorityPayoff, strictPriorityPayoff,
      strictPriorityCapturedGap, strictPriorityCapturedGap]
    rw [max_eq_left (le_of_lt (sub_pos.mpr hlead)), min_eq_right hbeyond]
    have hband : rival + gap - rival = gap := by ring
    rw [hband, max_eq_left (le_of_lt hgap), min_self]
    nlinarith

/-- Equality in the preceding peak inequality, for a positive leader, pins
the lead down to exactly the contested band. -/
theorem eq_band_of_payoff_at_band_le
    {slotWeight gap marginalCost own rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight)
    (hlead : rival < own)
    (hpeak :
      strictPriorityPayoff slotWeight gap marginalCost (rival + gap) rival ≤
        strictPriorityPayoff slotWeight gap marginalCost own rival) :
    own = rival + gap := by
  by_cases hwithin : own - rival ≤ gap
  · have hpositive : 0 ≤ own - rival := le_of_lt (sub_pos.mpr hlead)
    rw [strictPriorityPayoff, strictPriorityPayoff,
      strictPriorityCapturedGap, strictPriorityCapturedGap] at hpeak
    rw [max_eq_left hpositive, min_eq_left hwithin] at hpeak
    have hband : rival + gap - rival = gap := by ring
    rw [hband, max_eq_left (le_of_lt hgap), min_self] at hpeak
    nlinarith
  · have hbeyond : gap ≤ own - rival := le_of_not_ge hwithin
    rw [strictPriorityPayoff, strictPriorityPayoff,
      strictPriorityCapturedGap, strictPriorityCapturedGap] at hpeak
    rw [max_eq_left (le_of_lt (sub_pos.mpr hlead)), min_eq_right hbeyond] at hpeak
    have hband : rival + gap - rival = gap := by ring
    rw [hband, max_eq_left (le_of_lt hgap), min_self] at hpeak
    nlinarith

/-- With marginal cost strictly between zero and the prize weight, a positive
best response leads the rival by exactly `gap`. -/
theorem positive_bestResponse_eq_rival_add_gap
    {slotWeight gap marginalCost own rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) (hrival : 0 ≤ rival)
    (hbest : StrictPriorityBestResponse
      slotWeight gap marginalCost own rival) (hown : 0 < own) :
    own = rival + gap := by
  have hzero := hbest.2 0 (le_refl 0)
  rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival] at hzero
  have hlead : rival < own := by
    by_contra hnot
    have hbelow : own - rival ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    rw [strictPriorityPayoff, strictPriorityCapturedGap,
      max_eq_right hbelow, min_eq_left hgap.le] at hzero
    nlinarith
  apply eq_band_of_payoff_at_band_le hgap hcost hcostWeight hlead
  exact hbest.2 (rival + gap) (add_nonneg hrival hgap.le)

/-- A zero action is optimal exactly when the payoff at the unique positive
peak is nonpositive. -/
theorem zero_bestResponse_iff
    {slotWeight gap marginalCost rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) (hrival : 0 ≤ rival) :
    StrictPriorityBestResponse slotWeight gap marginalCost 0 rival ↔
      (slotWeight - marginalCost) * gap ≤ marginalCost * rival := by
  constructor
  · intro hbest
    have h := hbest.2 (rival + gap) (add_nonneg hrival hgap.le)
    rw [strictPriorityPayoff_at_band slotWeight gap marginalCost rival hgap.le,
      strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival] at h
    linarith
  · intro hpeak
    refine ⟨le_refl 0, ?_⟩
    intro deviation hdeviation
    rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival]
    by_cases hzero : deviation = 0
    · subst deviation
      rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival]
    · have hpositive : 0 < deviation := lt_of_le_of_ne hdeviation (Ne.symm hzero)
      by_cases hlead : rival < deviation
      · calc
          strictPriorityPayoff slotWeight gap marginalCost deviation rival ≤
              strictPriorityPayoff slotWeight gap marginalCost (rival + gap) rival :=
            strictPriorityPayoff_le_payoff_at_band
              hgap hcost hcostWeight hlead
          _ = (slotWeight - marginalCost) * gap - marginalCost * rival :=
            strictPriorityPayoff_at_band slotWeight gap marginalCost rival hgap.le
          _ ≤ 0 := by linarith
      · have hbelow : deviation - rival ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hlead)
        rw [strictPriorityPayoff, strictPriorityCapturedGap,
          max_eq_right hbelow, min_eq_left hgap.le]
        nlinarith

/-- The action one full band above the rival is optimal exactly when its peak
payoff is nonnegative. -/
theorem band_bestResponse_iff
    {slotWeight gap marginalCost rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) (hrival : 0 ≤ rival) :
    StrictPriorityBestResponse slotWeight gap marginalCost (rival + gap) rival ↔
      marginalCost * rival ≤ (slotWeight - marginalCost) * gap := by
  constructor
  · intro hbest
    have h := hbest.2 0 (le_refl 0)
    rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival,
      strictPriorityPayoff_at_band slotWeight gap marginalCost rival hgap.le] at h
    linarith
  · intro hpeak
    refine ⟨add_nonneg hrival hgap.le, ?_⟩
    intro deviation hdeviation
    by_cases hzero : deviation = 0
    · subst deviation
      rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival,
        strictPriorityPayoff_at_band slotWeight gap marginalCost rival hgap.le]
      linarith
    · have hpositive : 0 < deviation := lt_of_le_of_ne hdeviation (Ne.symm hzero)
      by_cases hlead : rival < deviation
      · exact strictPriorityPayoff_le_payoff_at_band
          hgap hcost hcostWeight hlead
      · have hbelow : deviation - rival ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hlead)
        rw [strictPriorityPayoff, strictPriorityCapturedGap,
          max_eq_right hbelow, min_eq_left hgap.le,
          strictPriorityPayoff_at_band slotWeight gap marginalCost rival hgap.le]
        nlinarith

/-- Complete best-response correspondence for `0 < κ < w₁`. -/
theorem bestResponse_iff_of_cost_lt_weight
    {slotWeight gap marginalCost own rival : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) (hrival : 0 ≤ rival) :
    StrictPriorityBestResponse slotWeight gap marginalCost own rival ↔
      (own = 0 ∧
          (slotWeight - marginalCost) * gap ≤ marginalCost * rival) ∨
        (own = rival + gap ∧
          marginalCost * rival ≤ (slotWeight - marginalCost) * gap) := by
  constructor
  · intro hbest
    rcases eq_or_lt_of_le hbest.1 with hzero | hpositive
    · left
      refine ⟨hzero.symm, ?_⟩
      subst own
      exact (zero_bestResponse_iff hgap hcost hcostWeight hrival).mp hbest
    · right
      have heq := positive_bestResponse_eq_rival_add_gap
        hgap hcost hcostWeight hrival hbest hpositive
      refine ⟨heq, ?_⟩
      subst own
      exact (band_bestResponse_iff hgap hcost hcostWeight hrival).mp hbest
  · rintro (⟨rfl, hpeak⟩ | ⟨rfl, hpeak⟩)
    · exact (zero_bestResponse_iff hgap hcost hcostWeight hrival).mpr hpeak
    · exact (band_bestResponse_iff hgap hcost hcostWeight hrival).mpr hpeak

/-- If latency is more expensive at the margin than the prize weight, zero is
the unique best response against every feasible rival action. -/
theorem bestResponse_iff_of_weight_lt_cost
    {slotWeight gap marginalCost own rival : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (hweightCost : slotWeight < marginalCost) (hrival : 0 ≤ rival) :
    StrictPriorityBestResponse slotWeight gap marginalCost own rival ↔
      own = 0 := by
  constructor
  · intro hbest
    have hown := hbest.1
    apply le_antisymm _ hown
    by_contra hnot
    have hpositive : 0 < own := lt_of_not_ge hnot
    have hcaptured :=
      strictPriorityCapturedGap_le_own (gap := gap) hown hrival
    have hweighted := mul_le_mul_of_nonneg_left hcaptured hweight.le
    have hzero := hbest.2 0 (le_refl 0)
    rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival]
      at hzero
    unfold strictPriorityPayoff at hzero
    nlinarith
  · rintro rfl
    refine ⟨le_refl 0, ?_⟩
    intro deviation hdeviation
    rw [strictPriorityPayoff_zero slotWeight gap marginalCost rival hgap.le hrival]
    have hcaptured :=
      strictPriorityCapturedGap_le_own (gap := gap) hdeviation hrival
    have hweighted := mul_le_mul_of_nonneg_left hcaptured hweight.le
    unfold strictPriorityPayoff
    nlinarith

/-- At `κ = w₁`, every feasible payoff is nonpositive. -/
theorem strictPriorityPayoff_nonpos_of_cost_eq_weight
    {slotWeight gap own rival : ℝ}
    (hweight : 0 < slotWeight) (hown : 0 ≤ own) (hrival : 0 ≤ rival) :
    strictPriorityPayoff slotWeight gap slotWeight own rival ≤ 0 := by
  have hcaptured := strictPriorityCapturedGap_le_own (gap := gap) hown hrival
  have hweighted := mul_le_mul_of_nonneg_left hcaptured hweight.le
  unfold strictPriorityPayoff
  nlinarith

/-- Complete best-response correspondence at the boundary `κ = w₁`. -/
theorem bestResponse_iff_of_cost_eq_weight
    {slotWeight gap own rival : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight) (hrival : 0 ≤ rival) :
    StrictPriorityBestResponse slotWeight gap slotWeight own rival ↔
      own = 0 ∨ (rival = 0 ∧ 0 ≤ own ∧ own ≤ gap) := by
  constructor
  · intro hbest
    by_cases hzero : own = 0
    · exact Or.inl hzero
    · right
      have hown : 0 < own := lt_of_le_of_ne hbest.1 (Ne.symm hzero)
      have hzeroPayoff := hbest.2 0 (le_refl 0)
      rw [strictPriorityPayoff_zero slotWeight gap slotWeight rival hgap.le hrival]
        at hzeroPayoff
      have hlead : rival < own := by
        by_contra hnot
        have hbelow : own - rival ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hnot)
        rw [strictPriorityPayoff, strictPriorityCapturedGap,
          max_eq_right hbelow, min_eq_left hgap.le] at hzeroPayoff
        nlinarith
      have hwithin : own - rival ≤ gap := by
        by_contra hnot
        have hbeyond : gap < own - rival := lt_of_not_ge hnot
        rw [strictPriorityPayoff, strictPriorityCapturedGap,
          max_eq_left (le_of_lt (sub_pos.mpr hlead)),
          min_eq_right (le_of_lt hbeyond)] at hzeroPayoff
        nlinarith
      rw [strictPriorityPayoff, strictPriorityCapturedGap,
        max_eq_left (le_of_lt (sub_pos.mpr hlead)), min_eq_left hwithin]
        at hzeroPayoff
      have hrivalZero : rival = 0 := by nlinarith
      exact ⟨hrivalZero, hbest.1, by linarith⟩
  · rintro (rfl | ⟨rfl, hown, hownGap⟩)
    · refine ⟨le_refl 0, ?_⟩
      intro deviation hdeviation
      rw [strictPriorityPayoff_zero slotWeight gap slotWeight rival hgap.le hrival]
      exact strictPriorityPayoff_nonpos_of_cost_eq_weight
        hweight hdeviation hrival
    · refine ⟨hown, ?_⟩
      intro deviation hdeviation
      have hownPayoff :
          strictPriorityPayoff slotWeight gap slotWeight own 0 = 0 := by
        rw [strictPriorityPayoff, strictPriorityCapturedGap,
          sub_zero, max_eq_left hown, min_eq_left hownGap]
        ring
      rw [hownPayoff]
      exact strictPriorityPayoff_nonpos_of_cost_eq_weight
        hweight hdeviation (le_refl 0)

/-- Pure equilibria when `0 < κ < w₁`.  The two asymmetric band profiles
exist exactly when `w₁ ≤ 2κ`; if the inequality fails, no pure equilibrium
exists. -/
theorem pureNash_iff_of_cost_lt_weight
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) :
    StrictPriorityPureNash slotWeight gap marginalCost first second ↔
      slotWeight ≤ 2 * marginalCost ∧
        ((first = gap ∧ second = 0) ∨ (first = 0 ∧ second = gap)) := by
  constructor
  · intro hnash
    have hfirstNonneg := hnash.1.1
    have hsecondNonneg := hnash.2.1
    have hfirst := (bestResponse_iff_of_cost_lt_weight
      hgap hcost hcostWeight hsecondNonneg).mp hnash.1
    have hsecond := (bestResponse_iff_of_cost_lt_weight
      hgap hcost hcostWeight hfirstNonneg).mp hnash.2
    rcases hfirst with ⟨hfirstZero, hfirstPeak⟩ | ⟨hfirstBand, hfirstPeak⟩
    · rcases hsecond with ⟨hsecondZero, hsecondPeak⟩ | ⟨hsecondBand, hsecondPeak⟩
      · subst first
        subst second
        have hpositive : 0 < (slotWeight - marginalCost) * gap :=
          mul_pos (sub_pos.mpr hcostWeight) hgap
        norm_num at hfirstPeak
        linarith
      · subst first
        simp only [zero_add] at hsecondBand
        subst second
        have hcoeff : slotWeight - marginalCost ≤ marginalCost := by
          nlinarith [hfirstPeak]
        exact ⟨by linarith, Or.inr ⟨rfl, rfl⟩⟩
    · rcases hsecond with ⟨hsecondZero, hsecondPeak⟩ | ⟨hsecondBand, hsecondPeak⟩
      · subst second
        simp only [zero_add] at hfirstBand
        subst first
        have hcoeff : slotWeight - marginalCost ≤ marginalCost := by
          nlinarith [hsecondPeak]
        exact ⟨by linarith, Or.inl ⟨rfl, rfl⟩⟩
      · nlinarith [hfirstBand, hsecondBand]
  · rintro ⟨hhalf, hprofiles⟩
    rcases hprofiles with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · subst first
      subst second
      constructor
      · apply (bestResponse_iff_of_cost_lt_weight
          hgap hcost hcostWeight (le_refl 0)).mpr
        right
        constructor
        · ring
        · have hpositive : 0 ≤ (slotWeight - marginalCost) * gap :=
            mul_nonneg (sub_nonneg.mpr hcostWeight.le) hgap.le
          simpa using hpositive
      · apply (bestResponse_iff_of_cost_lt_weight
          hgap hcost hcostWeight hgap.le).mpr
        left
        refine ⟨rfl, ?_⟩
        have hcoeff : slotWeight - marginalCost ≤ marginalCost := by linarith
        exact mul_le_mul_of_nonneg_right hcoeff hgap.le
    · subst first
      subst second
      constructor
      · apply (bestResponse_iff_of_cost_lt_weight
          hgap hcost hcostWeight hgap.le).mpr
        left
        refine ⟨rfl, ?_⟩
        have hcoeff : slotWeight - marginalCost ≤ marginalCost := by linarith
        exact mul_le_mul_of_nonneg_right hcoeff hgap.le
      · apply (bestResponse_iff_of_cost_lt_weight
          hgap hcost hcostWeight (le_refl 0)).mpr
        right
        constructor
        · ring
        · have hpositive : 0 ≤ (slotWeight - marginalCost) * gap :=
            mul_nonneg (sub_nonneg.mpr hcostWeight.le) hgap.le
          simpa using hpositive

/-- Proposition `prop:sp_race` (i): the expensive-technology equilibrium. -/
theorem pureNash_iff_of_weight_lt_cost
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (hweightCost : slotWeight < marginalCost) :
    StrictPriorityPureNash slotWeight gap marginalCost first second ↔
      first = 0 ∧ second = 0 := by
  unfold StrictPriorityPureNash
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hsecondNonneg := hsecond.1
    have hfirstZero := (bestResponse_iff_of_weight_lt_cost
      hgap hweight hweightCost hsecondNonneg).mp hfirst
    subst first
    have hsecondZero := (bestResponse_iff_of_weight_lt_cost
      hgap hweight hweightCost (le_refl 0)).mp hsecond
    exact ⟨rfl, hsecondZero⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨
      (bestResponse_iff_of_weight_lt_cost
        hgap hweight hweightCost (le_refl 0)).mpr rfl,
      (bestResponse_iff_of_weight_lt_cost
        hgap hweight hweightCost (le_refl 0)).mpr rfl⟩

/-- Proposition `prop:sp_race` (ii): all pure equilibria at `κ = w₁`. -/
theorem pureNash_iff_of_cost_eq_weight
    {slotWeight gap first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight) :
    StrictPriorityPureNash slotWeight gap slotWeight first second ↔
      (second = 0 ∧ 0 ≤ first ∧ first ≤ gap) ∨
        (first = 0 ∧ 0 ≤ second ∧ second ≤ gap) := by
  constructor
  · intro hnash
    have hfirst := (bestResponse_iff_of_cost_eq_weight
      hgap hweight hnash.2.1).mp hnash.1
    have hsecond := (bestResponse_iff_of_cost_eq_weight
      hgap hweight hnash.1.1).mp hnash.2
    rcases hfirst with hfirstZero | ⟨hsecondZero, hfirstNonneg, hfirstGap⟩
    · right
      subst first
      rcases hsecond with hsecondZero | ⟨_, hsecondNonneg, hsecondGap⟩
      · subst second
        exact ⟨rfl, le_refl 0, hgap.le⟩
      · exact ⟨rfl, hsecondNonneg, hsecondGap⟩
    · left
      exact ⟨hsecondZero, hfirstNonneg, hfirstGap⟩
  · rintro (⟨rfl, hfirstNonneg, hfirstGap⟩ |
      ⟨rfl, hsecondNonneg, hsecondGap⟩)
    · constructor
      · apply (bestResponse_iff_of_cost_eq_weight
          hgap hweight (le_refl 0)).mpr
        exact Or.inr ⟨rfl, hfirstNonneg, hfirstGap⟩
      · apply (bestResponse_iff_of_cost_eq_weight
          hgap hweight hfirstNonneg).mpr
        exact Or.inl rfl
    · constructor
      · apply (bestResponse_iff_of_cost_eq_weight
          hgap hweight hsecondNonneg).mpr
        exact Or.inl rfl
      · apply (bestResponse_iff_of_cost_eq_weight
          hgap hweight (le_refl 0)).mpr
        exact Or.inr ⟨rfl, hsecondNonneg, hsecondGap⟩

/-- Proposition `prop:sp_race` (iii): the moderately costly region. -/
theorem pureNash_iff_of_half_weight_lt_cost
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap)
    (hhalfCost : slotWeight / 2 < marginalCost)
    (hcostWeight : marginalCost < slotWeight) :
    StrictPriorityPureNash slotWeight gap marginalCost first second ↔
      (first = gap ∧ second = 0) ∨ (first = 0 ∧ second = gap) := by
  have hcost : 0 < marginalCost := by nlinarith
  rw [pureNash_iff_of_cost_lt_weight hgap hcost hcostWeight]
  constructor
  · exact And.right
  · intro hprofiles
    exact ⟨by linarith, hprofiles⟩

/-- Proposition `prop:sp_race` (iv): the half-price boundary. -/
theorem pureNash_iff_of_cost_eq_half_weight
    {slotWeight gap first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight) :
    StrictPriorityPureNash slotWeight gap (slotWeight / 2) first second ↔
      (first = gap ∧ second = 0) ∨ (first = 0 ∧ second = gap) := by
  rw [pureNash_iff_of_cost_lt_weight hgap (by linarith) (by linarith)]
  constructor
  · exact And.right
  · intro hprofiles
    exact ⟨by linarith, hprofiles⟩

/-- Proposition `prop:sp_race` (v), pure part: cheap technology admits no
pure-strategy Nash equilibrium. -/
theorem no_pureNash_of_cost_lt_half_weight
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap) (hcost : 0 < marginalCost)
    (hcostHalf : marginalCost < slotWeight / 2) :
    ¬ StrictPriorityPureNash slotWeight gap marginalCost first second := by
  rw [pureNash_iff_of_cost_lt_weight hgap hcost (by linarith)]
  intro hnash
  linarith [hnash.1]

/-- In the expensive-technology region the unique equilibrium burns nothing. -/
theorem dissipation_eq_zero_of_weight_lt_cost
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (hweightCost : slotWeight < marginalCost)
    (hnash : StrictPriorityPureNash
      slotWeight gap marginalCost first second) :
    strictPriorityDissipation marginalCost first second = 0 := by
  rcases (pureNash_iff_of_weight_lt_cost
    hgap hweight hweightCost).mp hnash with ⟨rfl, rfl⟩
  simp [strictPriorityDissipation]

/-- At `κ = w₁`, every action `a ∈ [0,G]` paired with zero is an
equilibrium and burns exactly `w₁ a`.  This realizes both endpoints of the
paper's stated dissipation range. -/
theorem cost_eq_weight_equilibrium_with_dissipation
    {slotWeight gap action : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (haction : 0 ≤ action) (hactionGap : action ≤ gap) :
    StrictPriorityPureNash slotWeight gap slotWeight action 0 ∧
      strictPriorityDissipation slotWeight action 0 = slotWeight * action := by
  constructor
  · apply (pureNash_iff_of_cost_eq_weight hgap hweight).mpr
    exact Or.inl ⟨rfl, haction, hactionGap⟩
  · simp [strictPriorityDissipation]

/-- Every equilibrium at `κ = w₁` burns an amount between zero and the full
contested surplus `w₁ G`. -/
theorem dissipation_bounds_of_cost_eq_weight
    {slotWeight gap first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (hnash : StrictPriorityPureNash
      slotWeight gap slotWeight first second) :
    0 ≤ strictPriorityDissipation slotWeight first second ∧
      strictPriorityDissipation slotWeight first second ≤ slotWeight * gap := by
  rcases (pureNash_iff_of_cost_eq_weight hgap hweight).mp hnash with
    ⟨rfl, hfirstNonneg, hfirstGap⟩ | ⟨rfl, hsecondNonneg, hsecondGap⟩
  · simp only [strictPriorityDissipation, add_zero]
    exact ⟨mul_nonneg hweight.le hfirstNonneg,
      mul_le_mul_of_nonneg_left hfirstGap hweight.le⟩
  · simp only [strictPriorityDissipation, zero_add]
    exact ⟨mul_nonneg hweight.le hsecondNonneg,
      mul_le_mul_of_nonneg_left hsecondGap hweight.le⟩

/-- In the moderately costly region both pure equilibria burn `κG`. -/
theorem dissipation_eq_of_half_weight_lt_cost
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap)
    (hhalfCost : slotWeight / 2 < marginalCost)
    (hcostWeight : marginalCost < slotWeight)
    (hnash : StrictPriorityPureNash
      slotWeight gap marginalCost first second) :
    strictPriorityDissipation marginalCost first second = marginalCost * gap := by
  rcases (pureNash_iff_of_half_weight_lt_cost
    hgap hhalfCost hcostWeight).mp hnash with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [strictPriorityDissipation]

/-- Consequently more than half of the contested surplus is dissipated
throughout `w₁/2 < κ < w₁`. -/
theorem half_contested_surplus_lt_dissipation
    {slotWeight gap marginalCost first second : ℝ}
    (hgap : 0 < gap)
    (hhalfCost : slotWeight / 2 < marginalCost)
    (hcostWeight : marginalCost < slotWeight)
    (hnash : StrictPriorityPureNash
      slotWeight gap marginalCost first second) :
    slotWeight * gap / 2 <
      strictPriorityDissipation marginalCost first second := by
  rw [dissipation_eq_of_half_weight_lt_cost
    hgap hhalfCost hcostWeight hnash]
  have hscaled := mul_lt_mul_of_pos_right hhalfCost hgap
  nlinarith

/-- At `κ = w₁/2`, both pure equilibria dissipate exactly half of the
contested surplus. -/
theorem dissipation_eq_half_contested_surplus
    {slotWeight gap first second : ℝ}
    (hgap : 0 < gap) (hweight : 0 < slotWeight)
    (hnash : StrictPriorityPureNash
      slotWeight gap (slotWeight / 2) first second) :
    strictPriorityDissipation (slotWeight / 2) first second =
      slotWeight * gap / 2 := by
  rcases (pureNash_iff_of_cost_eq_half_weight hgap hweight).mp hnash with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [strictPriorityDissipation] <;> ring

end SmoothingCliff.Racing
