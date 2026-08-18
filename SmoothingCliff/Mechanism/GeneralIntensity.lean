import SmoothingCliff.Mechanism.GeneralStability
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The stability certificate for a general Luce intensity

Remark `rem:functionalform`.  The certificate never uses the exponential form of
the intensity.  What it uses is that the bid enters through an increasing score
whose derivative is bounded, and the score derivative is exactly the logarithmic
derivative of the intensity.  So the whole certificate carries over to any
log-Lipschitz sequential Luce family, with the reciprocal temperature replaced
by a bound on the score derivative.

The score layer of the development is already stated for an arbitrary real
score; only the bid layer hard-wires `(bid - r)/tau`.  This file supplies the
bid layer for a general score and reads off the two members the remark names:
the exponential family, which returns the reciprocal temperature, and the
Tullock family, whose score is a scaled logarithm and whose derivative is
largest at the reserve.
-/

namespace SmoothingCliff.Mechanism

open MeasureTheory

noncomputable section

/-- Conditional allocation as a function of the own bid through a general
score. -/
def scoreBidPriority (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ → ℝ) (bid : ℝ) : ℝ :=
  conditionalPriority slotWeight slots stats (score bid)

/-- The bid derivative is the score derivative of the allocation times the
derivative of the score. -/
def scoreBidDerivative (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score scoreDeriv : ℝ → ℝ)
    (bid : ℝ) : ℝ :=
  conditionalPriorityScoreDerivative slotWeight slots stats (score bid) *
    scoreDeriv bid

theorem scoreBidPriority_hasDerivAt
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) {score scoreDeriv : ℝ → ℝ}
    {bid : ℝ} (hscore : HasDerivAt score (scoreDeriv bid) bid) :
    HasDerivAt (scoreBidPriority slotWeight slots stats score)
      (scoreBidDerivative slotWeight slots stats score scoreDeriv bid) bid :=
  (conditionalPriority_hasDerivAt_score slotWeight slots stats
    (score bid)).comp bid hscore

/-- **The general derivative bound.**  A score derivative bounded by `bound`
gives a bid derivative bounded by the top weight over `e` times `bound`. -/
theorem scoreBidDerivative_bounds
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score scoreDeriv : ℝ → ℝ)
    (bid bound : ℝ)
    (hWeight : Antitone slotWeight) (hTerminal : slotWeight slots = 0)
    (hderivNonneg : 0 ≤ scoreDeriv bid) (hderivLe : scoreDeriv bid ≤ bound) :
    scoreBidDerivative slotWeight slots stats score scoreDeriv bid ∈
      Set.Icc 0 (slotWeight 0 * Real.exp (-1) * bound) := by
  obtain ⟨hlow, hhigh⟩ := conditionalPriorityScoreDerivative_bounds slotWeight
    slots stats (score bid) hWeight hTerminal
  have htopNonneg : 0 ≤ slotWeight 0 * Real.exp (-1) :=
    le_trans hlow hhigh
  refine ⟨mul_nonneg hlow hderivNonneg, ?_⟩
  exact mul_le_mul hhigh hderivLe hderivNonneg htopNonneg

/-- A mean-value bridge on a convex set: an explicit nonnegative bounded
derivative gives an absolute-difference bound there. -/
theorem lipschitzOn_of_hasDerivAt_bounds
    (f f' : ℝ → ℝ) (C : ℝ) {domain : Set ℝ} (hconvex : Convex ℝ domain)
    (hDeriv : ∀ x ∈ domain, HasDerivAt f (f' x) x)
    (hBounds : ∀ x ∈ domain, f' x ∈ Set.Icc 0 C) :
    ∀ a ∈ domain, ∀ b ∈ domain, |f b - f a| ≤ C * |b - a| := by
  intro a ha b hb
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := f) (s := domain) (x := a) (y := b) (C := C)
    (fun x hx => (hDeriv x hx).differentiableAt)
    (fun x hx => by
      rw [(hDeriv x hx).deriv, Real.norm_eq_abs,
        abs_of_nonneg (hBounds x hx).1]
      exact (hBounds x hx).2)
    hconvex ha hb
  simpa [Real.norm_eq_abs] using h

/-- **The certificate for a general intensity.**  On any convex set of bids
where the score is differentiable with derivative in `[0, bound]`, the
conditional allocation is Lipschitz with constant the top weight over `e` times
`bound`. -/
theorem scoreBidPriority_lipschitzOn
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score scoreDeriv : ℝ → ℝ)
    (bound : ℝ) {domain : Set ℝ} (hconvex : Convex ℝ domain)
    (hWeight : Antitone slotWeight) (hTerminal : slotWeight slots = 0)
    (hscore : ∀ bid ∈ domain, HasDerivAt score (scoreDeriv bid) bid)
    (hderivNonneg : ∀ bid ∈ domain, 0 ≤ scoreDeriv bid)
    (hderivLe : ∀ bid ∈ domain, scoreDeriv bid ≤ bound) :
    ∀ a ∈ domain, ∀ b ∈ domain,
      |scoreBidPriority slotWeight slots stats score b -
          scoreBidPriority slotWeight slots stats score a| ≤
        slotWeight 0 * Real.exp (-1) * bound * |b - a| :=
  lipschitzOn_of_hasDerivAt_bounds _ _ _ hconvex
    (fun bid hbid => scoreBidPriority_hasDerivAt slotWeight slots stats
      (hscore bid hbid))
    (fun bid hbid => scoreBidDerivative_bounds slotWeight slots stats score
      scoreDeriv bid bound hWeight hTerminal (hderivNonneg bid hbid)
      (hderivLe bid hbid))

/-- The conditional allocation is nondecreasing in the own bid whenever the
score is. -/
theorem scoreBidPriority_monotoneOn
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score scoreDeriv : ℝ → ℝ)
    {domain : Set ℝ} (hconvex : Convex ℝ domain)
    (hWeight : Antitone slotWeight) (hTerminal : slotWeight slots = 0)
    (hscore : ∀ bid ∈ domain, HasDerivAt score (scoreDeriv bid) bid)
    (hderivNonneg : ∀ bid ∈ domain, 0 ≤ scoreDeriv bid) :
    MonotoneOn (scoreBidPriority slotWeight slots stats score) domain := by
  refine monotoneOn_of_deriv_nonneg hconvex ?_ ?_ ?_
  · exact fun bid hbid => (scoreBidPriority_hasDerivAt slotWeight slots stats
      (hscore bid hbid)).continuousAt.continuousWithinAt
  · exact fun bid hbid => ((scoreBidPriority_hasDerivAt slotWeight slots stats
      (hscore bid (interior_subset hbid))).differentiableAt).differentiableWithinAt
  · intro bid hbid
    have hmem := interior_subset hbid
    rw [(scoreBidPriority_hasDerivAt slotWeight slots stats
      (hscore bid hmem)).deriv]
    exact (scoreBidDerivative_bounds slotWeight slots stats score scoreDeriv
      bid (scoreDeriv bid) hWeight hTerminal (hderivNonneg bid hmem)
      (le_refl _)).1

/-! ### The two members the remark names -/

/-- The exponential member: the score is the bid gap over the temperature. -/
def exponentialScore (reserve temperature bid : ℝ) : ℝ :=
  (bid - reserve) / temperature

theorem scoreBidPriority_exponential_eq
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (reserve temperature bid : ℝ) :
    scoreBidPriority slotWeight slots stats
        (exponentialScore reserve temperature) bid =
      conditionalBidPriority slotWeight slots stats reserve temperature bid :=
  rfl

theorem exponentialScore_hasDerivAt (reserve temperature bid : ℝ) :
    HasDerivAt (exponentialScore reserve temperature) temperature⁻¹ bid := by
  simpa [exponentialScore, div_eq_mul_inv] using
    ((hasDerivAt_id bid).sub_const reserve).div_const temperature

/-- **The exponential member returns the reciprocal temperature.**  Reading the
general certificate at the exponential score recovers the constant of
`conditionalBidPriority_lipschitz`. -/
theorem exponential_certificate
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) {reserve temperature : ℝ}
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight) (hTerminal : slotWeight slots = 0) :
    ∀ a b : ℝ,
      |conditionalBidPriority slotWeight slots stats reserve temperature b -
          conditionalBidPriority slotWeight slots stats reserve temperature a| ≤
        slotWeight 0 / (Real.exp 1 * temperature) * |b - a| := by
  intro a b
  have hgeneral := scoreBidPriority_lipschitzOn slotWeight slots stats
    (exponentialScore reserve temperature) (fun _ => temperature⁻¹)
    temperature⁻¹ (convex_univ) hWeight hTerminal
    (fun bid _ => exponentialScore_hasDerivAt reserve temperature bid)
    (fun _ _ => inv_nonneg.mpr hTemperature.le)
    (fun _ _ => le_refl _)
    a (Set.mem_univ a) b (Set.mem_univ b)
  rw [scoreBidPriority_exponential_eq, scoreBidPriority_exponential_eq]
    at hgeneral
  have hconstant : slotWeight 0 * Real.exp (-1) * temperature⁻¹ =
      slotWeight 0 / (Real.exp 1 * temperature) := by
    rw [Real.exp_neg]
    field_simp
  rwa [hconstant] at hgeneral

/-- The Tullock member: the intensity is a power of the bid relative to the
reserve, so the score is a scaled logarithm. -/
def tullockScore (reserve exponentTemperature bid : ℝ) : ℝ :=
  (Real.log bid - Real.log reserve) / exponentTemperature

/-- Its derivative is largest at the reserve. -/
def tullockScoreDeriv (exponentTemperature bid : ℝ) : ℝ :=
  bid⁻¹ / exponentTemperature

theorem tullockScore_hasDerivAt {reserve exponentTemperature bid : ℝ}
    (hbid : bid ≠ 0) :
    HasDerivAt (tullockScore reserve exponentTemperature)
      (tullockScoreDeriv exponentTemperature bid) bid :=
  ((Real.hasDerivAt_log hbid).sub_const (Real.log reserve)).div_const _

theorem tullockScoreDeriv_nonneg {exponentTemperature bid : ℝ}
    (hTemperature : 0 < exponentTemperature) (hbid : 0 < bid) :
    0 ≤ tullockScoreDeriv exponentTemperature bid :=
  div_nonneg (inv_nonneg.mpr hbid.le) hTemperature.le

theorem tullockScoreDeriv_le {reserve exponentTemperature bid : ℝ}
    (hreserve : 0 < reserve) (hTemperature : 0 < exponentTemperature)
    (hbid : reserve ≤ bid) :
    tullockScoreDeriv exponentTemperature bid ≤
      (exponentTemperature * reserve)⁻¹ := by
  have hinv : bid⁻¹ ≤ reserve⁻¹ := by gcongr
  calc tullockScoreDeriv exponentTemperature bid
      = bid⁻¹ / exponentTemperature := rfl
    _ ≤ reserve⁻¹ / exponentTemperature := by gcongr
    _ = (exponentTemperature * reserve)⁻¹ := by
        rw [mul_inv]
        ring

/-- **The Tullock member returns the top weight over `e` times the exponent
temperature times the reserve.**  This is the constant the remark names in bid
units. -/
theorem tullock_certificate
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) {reserve exponentTemperature : ℝ}
    (hreserve : 0 < reserve) (hTemperature : 0 < exponentTemperature)
    (hWeight : Antitone slotWeight) (hTerminal : slotWeight slots = 0) :
    ∀ a ∈ Set.Ici reserve, ∀ b ∈ Set.Ici reserve,
      |scoreBidPriority slotWeight slots stats
            (tullockScore reserve exponentTemperature) b -
          scoreBidPriority slotWeight slots stats
            (tullockScore reserve exponentTemperature) a| ≤
        slotWeight 0 * Real.exp (-1) * (exponentTemperature * reserve)⁻¹ *
          |b - a| :=
  scoreBidPriority_lipschitzOn slotWeight slots stats
    (tullockScore reserve exponentTemperature)
    (tullockScoreDeriv exponentTemperature) _ (convex_Ici reserve) hWeight
    hTerminal
    (fun _ hbid =>
      tullockScore_hasDerivAt
        (ne_of_gt (lt_of_lt_of_le hreserve (Set.mem_Ici.mp hbid))))
    (fun _ hbid =>
      tullockScoreDeriv_nonneg hTemperature
        (lt_of_lt_of_le hreserve (Set.mem_Ici.mp hbid)))
    (fun _ hbid =>
      tullockScoreDeriv_le hreserve hTemperature (Set.mem_Ici.mp hbid))

end

end SmoothingCliff.Mechanism
