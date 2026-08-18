/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Environment
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity

/-!
# Symmetric IID auctions: The first-price equilibrium bid

In the symmetric `n`-bidder **first-price auction** with values drawn from `F` on `[θlo, θhi]`, the
symmetric **Bayes–Nash equilibrium** has each bidder shade its bid to the expected highest rival
value conditional on winning (Vickrey 1961; Riley and Samuelson 1981):

`b(θ) = θ − (∫_{θlo}^θ F(s)^{n-1} ds) / F(θ)^{n-1}`.

Equivalently `b(θ) = 𝔼[ max_{j≠i} θⱼ ∣ all θⱼ ≤ θ ]`, the mean of the top rival order statistic
truncated at `θ`. This file defines the equilibrium bid, records its monotonicity and boundary
behavior, and proves the symmetric best-response property.

## Main definitions

* `ScreeningEnv.firstPriceBid` — the symmetric equilibrium bid function
  `b(θ) = θ − (∫_{θlo}^θ F(s)^{n-1} ds) / F(θ)^{n-1}`.
* `ScreeningEnv.firstPriceInterimUtil` — interim payoff for a type-`θ` bidder mimicking type `z`.

## Main statements

* `ScreeningEnv.firstPriceBid_θlo` / `ScreeningEnv.θlo_le_firstPriceBid` /
  `ScreeningEnv.firstPriceBid_le_self` — boundary value and bounds: `b(θlo) = θlo` and
  `θlo ≤ b(θ) ≤ θ` on the type interval.
* `ScreeningEnv.firstPriceBid_lt_self` — bids are shaded below value (`b(θ) < θ` for `θ > θlo`).
* `ScreeningEnv.firstPriceBid_strictMonoOn` — `b` is strictly increasing, so the unit goes to the
  highest-value bidder.
* `ScreeningEnv.firstPriceBid_isBestResponse` — the symmetric **Bayes–Nash equilibrium**
  best-response property: When every rival bids `b`, a type-`θ` bidder maximizes its interim payoff
  by bidding `b(θ)`.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).
* Riley, John G., and William F. Samuelson. 1981. “Optimal Auctions.” *The American Economic
  Review* 71 (3): 381–92.

## Tags

auction, first-price, bayes-nash equilibrium, bid shading, mechanism design
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-- The **symmetric first-price equilibrium bid** for `n` bidders: A type-`θ` bidder bids the
expected highest rival value conditional on winning,
`b(θ) = θ − (∫_{θlo}^θ F(s)^{n-1} ds) / F(θ)^{n-1}`. Well-defined for `θ > θlo`, where
`F(θ) > 0`. -/
def firstPriceBid (n : ℕ) (θ : ℝ) : ℝ :=
  θ - (∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1)) / (E.dist.cdf θ) ^ (n - 1)

/-- The CDF vanishes at the lowest type: No mass lies below `θlo`. -/
theorem cdf_θlo_eq_zero : E.dist.cdf E.θlo = 0 := by
  rw [E.cdf_eq_intervalIntegral E.θlo, intervalIntegral.integral_same]

/-- The CDF is strictly positive above the lowest type, since the density is positive throughout
the support. -/
theorem cdf_pos_of_mem_Ioc {s : ℝ} (hs : s ∈ Ioc E.θlo E.θhi) : 0 < E.dist.cdf s := by
  -- strict monotonicity from `θlo` plus `cdf θlo = 0`
  have hstrict : E.dist.cdf E.θlo < E.dist.cdf s :=
    E.dist.cdf_strictMono hs.1
      (fun x hx => E.density_pos x ⟨hx.1, le_trans hx.2 hs.2⟩)
      (E.density_cont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hs.2⟩))
  rwa [E.cdf_θlo_eq_zero] at hstrict

/-- The first-price bid is measurable in the bidder's type. -/
lemma firstPriceBid_measurable (n : ℕ) : Measurable (E.firstPriceBid n) := by
  have hGcont : Continuous (fun s => (E.dist.cdf s) ^ (n - 1)) := (E.dist.cdf_continuous).pow _
  have hN : Continuous (fun θ => ∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1)) :=
    intervalIntegral.continuous_primitive (fun _ _ => hGcont.intervalIntegrable _ _) _
  exact measurable_id.sub (hN.measurable.div hGcont.measurable)

/-- At the lowest type the bid is the type itself: There is nothing to shade against. -/
@[simp] lemma firstPriceBid_θlo (n : ℕ) : E.firstPriceBid n E.θlo = E.θlo := by
  rw [firstPriceBid, intervalIntegral.integral_same, zero_div, sub_zero]

/-- **The bid never falls below the lowest type.** The shading term is at most `θ − θlo`, since the
integrand `F(s)^{n-1}` is bounded by its value at the upper endpoint. -/
lemma θlo_le_firstPriceBid (n : ℕ) {θ : ℝ} (hθ : θ ∈ Icc E.θlo E.θhi) :
    E.θlo ≤ E.firstPriceBid n θ := by
  rcases eq_or_lt_of_le hθ.1 with hlo | hlo
  · rw [← hlo, firstPriceBid_θlo]
  · have hG_pos : 0 < E.dist.cdf θ ^ (n - 1) :=
      pow_pos (E.cdf_pos_of_mem_Ioc ⟨hlo, hθ.2⟩) _
    -- The integrand is dominated by its right-endpoint value, so the integral is at most
    -- `(θ − θlo) · F(θ)^{n-1}`.
    have hbound : (∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1))
        ≤ (θ - E.θlo) * E.dist.cdf θ ^ (n - 1) := by
      calc (∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1))
          ≤ ∫ _s in E.θlo..θ, E.dist.cdf θ ^ (n - 1) := by
            refine intervalIntegral.integral_mono_on hlo.le
              ((E.dist.cdf_continuous.pow _).intervalIntegrable _ _) intervalIntegrable_const
              (fun s hs => pow_le_pow_left₀ (E.dist.cdf_nonneg s) (E.dist.cdf.mono hs.2) _)
        _ = (θ - E.θlo) * E.dist.cdf θ ^ (n - 1) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [firstPriceBid, le_sub_comm, div_le_iff₀ hG_pos]
    linarith

/-- **The bid never exceeds the value** (weak version, on the closed interval and for every `n`;
the strict version above the lowest type is `firstPriceBid_lt_self`). -/
lemma firstPriceBid_le_self (n : ℕ) {θ : ℝ} (hθ : θ ∈ Icc E.θlo E.θhi) :
    E.firstPriceBid n θ ≤ θ := by
  rcases eq_or_lt_of_le hθ.1 with hlo | hlo
  · rw [← hlo, firstPriceBid_θlo]
  · have hG_pos : 0 < E.dist.cdf θ ^ (n - 1) :=
      pow_pos (E.cdf_pos_of_mem_Ioc ⟨hlo, hθ.2⟩) _
    have hN_nonneg : 0 ≤ ∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1) :=
      intervalIntegral.integral_nonneg hlo.le (fun s _ => pow_nonneg (E.dist.cdf_nonneg s) _)
    have hshade : 0 ≤ (∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1)) / E.dist.cdf θ ^ (n - 1) :=
      div_nonneg hN_nonneg hG_pos.le
    rw [firstPriceBid]
    linarith

/-- **Bids are shaded below value.** For a type above the lowest, the first-price bid is strictly
below the value. -/
-- `_hn` is intentionally unused; it is kept so the signature matches `firstPriceBid_strictMonoOn`.
theorem firstPriceBid_lt_self (n : ℕ) (_hn : 2 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Ioc E.θlo E.θhi) : E.firstPriceBid n θ < θ := by
  have hFθ : 0 < E.dist.cdf θ := E.cdf_pos_of_mem_Ioc hθ
  have hden : 0 < (E.dist.cdf θ) ^ (n - 1) := pow_pos hFθ _
  have hcont : Continuous (fun s => (E.dist.cdf s) ^ (n - 1)) :=
    (E.dist.cdf_continuous).pow _
  have hint : IntervalIntegrable (fun s => (E.dist.cdf s) ^ (n - 1)) volume E.θlo θ :=
    hcont.intervalIntegrable _ _
  have hnum : 0 < ∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun s hs => ?_) hθ.1
    exact pow_pos (E.cdf_pos_of_mem_Ioc ⟨hs.1, le_trans hs.2.le hθ.2⟩) _
  rw [firstPriceBid]
  have : 0 < (∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1)) / (E.dist.cdf θ) ^ (n - 1) :=
    div_pos hnum hden
  linarith

/-- **The first-price bid is strictly increasing.** Hence the bidder with the highest value submits
the highest bid and wins, so first-price implements the same monotone allocation as second-price. -/
theorem firstPriceBid_strictMonoOn (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (E.firstPriceBid n) (Ioc E.θlo E.θhi) := by
  set F := E.dist.cdf with hF_def
  set f := E.dist.density with hf_def
  have hcdf_pos : ∀ s ∈ Ioc E.θlo E.θhi, 0 < F s := fun s hs => E.cdf_pos_of_mem_Ioc hs
  have hGcont : Continuous (fun s => (F s) ^ (n - 1)) := (E.dist.cdf_continuous).pow _
  have hcont : ContinuousOn (E.firstPriceBid n) (Ioc E.θlo E.θhi) := by
    have hN : Continuous (fun θ => ∫ s in E.θlo..θ, (F s) ^ (n - 1)) :=
      intervalIntegral.continuous_primitive (fun _ _ => hGcont.intervalIntegrable _ _) _
    have hGne : ∀ θ ∈ Ioc E.θlo E.θhi, (F θ) ^ (n - 1) ≠ 0 :=
      fun θ hθ => ne_of_gt (pow_pos (hcdf_pos θ hθ) _)
    have hdiv : ContinuousOn
        (fun θ => (∫ s in E.θlo..θ, (F s) ^ (n - 1)) / (F θ) ^ (n - 1)) (Ioc E.θlo E.θhi) :=
      hN.continuousOn.div hGcont.continuousOn hGne
    exact (continuousOn_id.sub hdiv)
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) hcont (fun θ hθ => ?_)
  rw [interior_Ioc] at hθ
  have hθIoc : θ ∈ Ioc E.θlo E.θhi := ⟨hθ.1, hθ.2.le⟩
  have hFθ_pos : 0 < F θ := hcdf_pos θ hθIoc
  have hfθ_pos : 0 < f θ := E.density_pos θ ⟨hθ.1.le, hθ.2.le⟩
  have hf_contAt : ContinuousAt f θ :=
    (E.density_cont.continuousAt (Icc_mem_nhds hθ.1 hθ.2))
  have hF_deriv : HasDerivAt (⇑F) (f θ) θ := E.dist.deriv_cdf_eq_density θ hf_contAt
  have hG_deriv : HasDerivAt (fun s => (F s) ^ (n - 1))
      ((↑(n - 1)) * (F θ) ^ (n - 1 - 1) * f θ) θ := by
    have := hF_deriv.pow (n - 1)
    simpa using this
  have hGint : IntervalIntegrable (fun s => (F s) ^ (n - 1)) volume E.θlo θ :=
    hGcont.intervalIntegrable _ _
  have hN_deriv : HasDerivAt (fun u => ∫ s in E.θlo..u, (F s) ^ (n - 1))
      ((F θ) ^ (n - 1)) θ :=
    intervalIntegral.integral_hasDerivAt_right hGint
      hGcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      (hGcont.continuousAt)
  have hGθ_ne : (F θ) ^ (n - 1) ≠ 0 := ne_of_gt (pow_pos hFθ_pos _)
  set N : ℝ := ∫ s in E.θlo..θ, (F s) ^ (n - 1) with hN_def
  set Nd' : ℝ := (↑(n - 1)) * (F θ) ^ (n - 1 - 1) * f θ with hNd'_def
  have hquot : HasDerivAt (fun u => (∫ s in E.θlo..u, (F s) ^ (n - 1)) / (F u) ^ (n - 1))
      (((F θ) ^ (n - 1) * (F θ) ^ (n - 1) - N * Nd') / ((F θ) ^ (n - 1)) ^ 2) θ :=
    hN_deriv.div hG_deriv hGθ_ne
  have hbid : HasDerivAt (E.firstPriceBid n)
      (1 - ((F θ) ^ (n - 1) * (F θ) ^ (n - 1) - N * Nd') / ((F θ) ^ (n - 1)) ^ 2) θ :=
    (hasDerivAt_id θ).sub hquot
  rw [hbid.deriv]
  have hNpos : 0 < N := by
    rw [hN_def]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hGint (fun s hs => ?_) hθ.1
    exact pow_pos (hcdf_pos s ⟨hs.1, le_trans hs.2.le hθ.2.le⟩) _
  have hNd'_pos : 0 < Nd' := by
    rw [hNd'_def]
    have h1 : 0 < (↑(n - 1) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hn
    positivity
  have hG2_pos : 0 < ((F θ) ^ (n - 1)) ^ 2 := by positivity
  have hkey : 1 - ((F θ) ^ (n - 1) * (F θ) ^ (n - 1) - N * Nd') / ((F θ) ^ (n - 1)) ^ 2
      = N * Nd' / ((F θ) ^ (n - 1)) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- A type-`θ` bidder's **interim payoff from mimicking type `z`** in the symmetric first-price
auction, when every rival bids the equilibrium `b`: It wins (and pays its bid `b(z)`) exactly when
all `n−1` rivals' values fall below `z`, an event of probability `F(z)^{n-1}`. -/
def firstPriceInterimUtil (n : ℕ) (θ z : ℝ) : ℝ :=
  (θ - E.firstPriceBid n z) * E.dist.cdf z ^ (n - 1)

/-- **Truthful mimicking is the symmetric Bayes–Nash best response.** When all rivals bid the
equilibrium schedule `b`, a type-`θ` bidder (with `θ > θlo`) cannot do better than bidding its own
`b(θ)`: For every alternative type `z` it could mimic, `Π(θ, z) ≤ Π(θ, θ)`. This determines
`firstPriceBid` as the symmetric equilibrium, so first-price implements the same monotone
allocation `F^{n-1}` as the second-price auction. -/
theorem firstPriceBid_isBestResponse (n : ℕ) (hn : 2 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Ioc E.θlo E.θhi) {z : ℝ} (hz : z ∈ Icc E.θlo E.θhi) :
    E.firstPriceInterimUtil n θ z ≤ E.firstPriceInterimUtil n θ θ := by
  have hn1 : n - 1 ≠ 0 := by omega
  have hFlo : E.dist.cdf E.θlo = 0 := E.cdf_θlo_eq_zero
  have hFmono : Monotone (⇑E.dist.cdf) := E.dist.cdf.mono
  have hFnn : ∀ s, 0 ≤ E.dist.cdf s := fun s => E.dist.cdf_nonneg s
  have hGcont : Continuous (fun s => E.dist.cdf s ^ (n - 1)) := E.dist.cdf_continuous.pow _
  have hGint : ∀ a b : ℝ, IntervalIntegrable (fun s => E.dist.cdf s ^ (n - 1)) volume a b :=
    fun a b => hGcont.intervalIntegrable a b
  have hFpos : ∀ s ∈ Ioc E.θlo E.θhi, 0 < E.dist.cdf s := fun s hs => E.cdf_pos_of_mem_Ioc hs
  have hval : ∀ {w : ℝ}, w ∈ Ioc E.θlo E.θhi →
      E.firstPriceInterimUtil n θ w
        = (θ - w) * E.dist.cdf w ^ (n - 1) + ∫ s in E.θlo..w, E.dist.cdf s ^ (n - 1) := by
    intro w hw
    have hGw : E.dist.cdf w ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt (hFpos w hw))
    simp only [firstPriceInterimUtil, firstPriceBid]
    field_simp
    ring
  have hdiag : E.firstPriceInterimUtil n θ θ = ∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1) := by
    rw [hval hθ, sub_self, zero_mul, zero_add]
  rw [hdiag]
  rcases eq_or_lt_of_le hz.1 with hzlo | hzlo
  · have hz0 : E.firstPriceInterimUtil n θ z = 0 := by
      simp only [firstPriceInterimUtil, ← hzlo, hFlo, zero_pow hn1, mul_zero]
    rw [hz0]
    exact intervalIntegral.integral_nonneg hθ.1.le (fun s _ => pow_nonneg (hFnn s) _)
  · rw [hval ⟨hzlo, hz.2⟩]
    have e1 : (∫ s in E.θlo..θ, E.dist.cdf s ^ (n - 1))
        - ∫ s in E.θlo..z, E.dist.cdf s ^ (n - 1)
        = ∫ s in z..θ, E.dist.cdf s ^ (n - 1) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hGint E.θlo z) (hGint z θ)]; ring
    have hmargin : 0 ≤ ∫ s in z..θ, (E.dist.cdf s ^ (n - 1) - E.dist.cdf z ^ (n - 1)) := by
      rcases le_total z θ with hzθ | hθz
      · exact intervalIntegral.integral_nonneg hzθ (fun s hs => by
          have := pow_le_pow_left₀ (hFnn z) (hFmono hs.1) (n - 1); linarith)
      · rw [intervalIntegral.integral_symm θ z, ← intervalIntegral.integral_neg]
        simp only [neg_sub]
        exact intervalIntegral.integral_nonneg hθz (fun s hs => by
          have := pow_le_pow_left₀ (hFnn s) (hFmono hs.2) (n - 1); linarith)
    rw [intervalIntegral.integral_sub (hGint z θ) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at hmargin
    linarith [e1, hmargin]

/-- The CDF saturates at the top of the support: `F(θhi) = 1`. -/
theorem cdf_θhi_eq_one : E.dist.cdf E.θhi = 1 :=
  E.dist.cdf_eq_one_of_supportsOn_Icc_right (fun _t ht => E.density_eq_zero_of_notMem ht) le_rfl

/-- **The bid is continuous on the closed type interval** `[θlo, θhi]`. -/
lemma firstPriceBid_continuousOn (n : ℕ) :
    ContinuousOn (E.firstPriceBid n) (Icc E.θlo E.θhi) := by
  have hGcont : Continuous (fun s => (E.dist.cdf s) ^ (n - 1)) := (E.dist.cdf_continuous).pow _
  have hN : Continuous (fun θ => ∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1)) :=
    intervalIntegral.continuous_primitive (fun _ _ => hGcont.intervalIntegrable _ _) _
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxlo | hxlo
  · -- At the lowest type: squeeze `θlo ≤ b(θ) ≤ θ`, both bounds tending to `θlo` within `Icc`.
    rw [ContinuousWithinAt, ← hxlo, firstPriceBid_θlo]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto continuous_id E.θlo))
      (eventually_nhdsWithin_of_forall fun θ hθ => ?_)
      (eventually_nhdsWithin_of_forall fun θ hθ => ?_)
    · exact E.θlo_le_firstPriceBid n hθ
    · exact E.firstPriceBid_le_self n hθ
  · -- Above the lowest type: the ratio is continuous (denominator nonzero), hence so is the bid.
    have hxIoc : x ∈ Ioc E.θlo E.θhi := ⟨hxlo, hx.2⟩
    have hGne : (E.dist.cdf x) ^ (n - 1) ≠ 0 := ne_of_gt (pow_pos (E.cdf_pos_of_mem_Ioc hxIoc) _)
    have hdiv : ContinuousAt
        (fun θ => (∫ s in E.θlo..θ, (E.dist.cdf s) ^ (n - 1)) / (E.dist.cdf θ) ^ (n - 1)) x :=
      hN.continuousAt.div hGcont.continuousAt hGne
    exact ((continuous_id.continuousAt).sub hdiv).continuousWithinAt

/-- **Strict monotonicity on the closed interval**, the lowest type included: `b(θlo) = θlo` lies
strictly below every `b(z)` with `z > θlo`. The open-interval version is
`firstPriceBid_strictMonoOn`. -/
theorem firstPriceBid_strictMonoOn_Icc (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (E.firstPriceBid n) (Icc E.θlo E.θhi) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le ha.1 with hlo | hlo
  · -- `a = θlo`: bid at `a` is `θlo`; route through a midpoint `c ∈ (θlo, b)` to gain strictness.
    rw [← hlo, firstPriceBid_θlo]
    have hθlo_b : E.θlo < b := hlo ▸ hab
    set c := (E.θlo + b) / 2 with hc_def
    have hc_lo : E.θlo < c := by rw [hc_def]; linarith
    have hc_b : c < b := by rw [hc_def]; linarith
    have hc_hi : c ≤ E.θhi := le_trans hc_b.le hb.2
    have hc_Icc : c ∈ Icc E.θlo E.θhi := ⟨hc_lo.le, hc_hi⟩
    have hstep1 : E.θlo ≤ E.firstPriceBid n c := E.θlo_le_firstPriceBid n hc_Icc
    have hstep2 : E.firstPriceBid n c < E.firstPriceBid n b :=
      E.firstPriceBid_strictMonoOn n hn ⟨hc_lo, hc_hi⟩ ⟨lt_trans hc_lo hc_b, hb.2⟩ hc_b
    linarith
  · -- `θlo < a`: both endpoints sit in the open-left interval, so the open-interval result applies.
    exact E.firstPriceBid_strictMonoOn n hn ⟨hlo, ha.2⟩ ⟨lt_trans hlo hab, hb.2⟩ hab

/-- **Mimicking best response on the closed interval**, the lowest type included. For `θ = θlo` the
truthful payoff is `0` and every mimicry payoff `(θlo − b(z))·F(z)^{n-1}` is nonpositive (bids
never fall below `θlo`); above the lowest type this is `firstPriceBid_isBestResponse`. -/
theorem firstPriceBid_isBestResponse_Icc (n : ℕ) (hn : 2 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Icc E.θlo E.θhi) {z : ℝ} (hz : z ∈ Icc E.θlo E.θhi) :
    E.firstPriceInterimUtil n θ z ≤ E.firstPriceInterimUtil n θ θ := by
  rcases eq_or_lt_of_le hθ.1 with hlo | hlo
  · -- Lowest type: truthful payoff is `0`, every mimicry payoff is `≤ 0`.
    have hself : E.firstPriceInterimUtil n θ θ = 0 := by
      rw [← hlo]; simp [firstPriceInterimUtil]
    rw [hself, ← hlo]
    have hb := E.θlo_le_firstPriceBid n hz
    have hF : (0:ℝ) ≤ E.dist.cdf z ^ (n - 1) := pow_nonneg (E.dist.cdf_nonneg z) _
    exact mul_nonpos_iff.mpr (Or.inr ⟨by linarith, hF⟩)
  · exact E.firstPriceBid_isBestResponse n hn ⟨hlo, hθ.2⟩ hz

end ScreeningEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
