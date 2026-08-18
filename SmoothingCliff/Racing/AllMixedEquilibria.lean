import SmoothingCliff.Racing.MixedRace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Monotone

/-!
# Arbitrary Borel mixed equilibria of the strict-priority race

This file supplies the measure-theoretic layer needed for Proposition
`prop:sp_allequilibria` and Proposition `prop:sp_floor` of *Smoothing the
Cliff*.  An action has type `NNReal`, so negative investments are excluded by
the type rather than by an almost-sure side condition.  A mixed strategy is a
genuine Borel probability measure with finite first moment.  The latter is
part of the strategy interface because the game's linear cost would otherwise
make the ordinary Bochner integral an unsuitable payoff convention.

Best response is stated against every pure `NNReal` deviation.  The theorem
`borelExpectedPayoff_eq_integral_pure` proves that the displayed mixed payoff
is the integral of those pure payoffs, so this is the usual mixed best-response
condition rather than an auxiliary relaxation.

The zero-payoff dissipation argument below is measure-theoretic and does not
assume the paper's CDF window inequality.  It derives the relevant inequalities
from the Nash deviation conditions at `G, 2G, ..., JG` and integrates a
pointwise truncated-gap summation inequality.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- A Borel probability law on nonnegative actions with finite first moment. -/
structure BorelMixedStrategy where
  law : ProbabilityMeasure NNReal
  integrable_action :
    Integrable (fun action : NNReal => (action : ℝ))
      (law : Measure NNReal)

namespace BorelMixedStrategy

/-- The ordinary real-valued first moment of a mixed strategy. -/
def meanAction (strategy : BorelMixedStrategy) : ℝ :=
  ∫ action : NNReal, (action : ℝ)
    ∂(strategy.law : Measure NNReal)

/-- The CDF, extended to real arguments.  It is automatically zero below zero. -/
def cdf (strategy : BorelMixedStrategy) (x : ℝ) : ENNReal :=
  (strategy.law : Measure NNReal) {action : NNReal | (action : ℝ) ≤ x}

/-- The topological support of the action law. -/
def support (strategy : BorelMixedStrategy) : Set NNReal :=
  (strategy.law : Measure NNReal).support

/-- The lower endpoint of the closed, nonempty support. -/
def lowerSupport (strategy : BorelMixedStrategy) : NNReal :=
  sInf strategy.support

theorem meanAction_nonneg (strategy : BorelMixedStrategy) :
    0 ≤ strategy.meanAction := by
  apply integral_nonneg
  exact fun _ => by positivity

theorem cdf_of_neg (strategy : BorelMixedStrategy) {x : ℝ} (hx : x < 0) :
    strategy.cdf x = 0 := by
  have hset : {action : NNReal | (action : ℝ) ≤ x} = ∅ := by
    ext action
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_le_of_gt (lt_of_lt_of_le hx NNReal.zero_le_coe)
  simp [cdf, hset]

theorem cdf_mono (strategy : BorelMixedStrategy) :
    Monotone strategy.cdf := by
  intro x y hxy
  unfold cdf
  exact measure_mono (fun _ ha => le_trans ha hxy)

theorem cdf_le_one (strategy : BorelMixedStrategy) (x : ℝ) :
    strategy.cdf x ≤ 1 := by
  calc
    strategy.cdf x ≤ (strategy.law : Measure NNReal) Set.univ :=
      measure_mono (subset_univ _)
    _ = 1 := by simp

theorem law_ne_zero (strategy : BorelMixedStrategy) :
    (strategy.law : Measure NNReal) ≠ 0 := by
  intro hzero
  have huniv := congrArg (fun μ : Measure NNReal => μ Set.univ) hzero
  simp at huniv

theorem support_nonempty (strategy : BorelMixedStrategy) :
    strategy.support.Nonempty := by
  exact Measure.nonempty_support strategy.law_ne_zero

theorem support_closed (strategy : BorelMixedStrategy) :
    IsClosed strategy.support := by
  exact Measure.isClosed_support

theorem support_bddBelow (strategy : BorelMixedStrategy) :
    BddBelow strategy.support := by
  exact ⟨0, fun _ _ => bot_le⟩

theorem lowerSupport_mem_support (strategy : BorelMixedStrategy) :
    strategy.lowerSupport ∈ strategy.support := by
  exact IsClosed.csInf_mem strategy.support_closed strategy.support_nonempty
    strategy.support_bddBelow

theorem lowerSupport_le_of_mem_support
    (strategy : BorelMixedStrategy) {action : NNReal}
    (haction : action ∈ strategy.support) :
    strategy.lowerSupport ≤ action := by
  exact csInf_le strategy.support_bddBelow haction

theorem ae_mem_support (strategy : BorelMixedStrategy) :
    ∀ᵐ action ∂(strategy.law : Measure NNReal),
      action ∈ strategy.support := by
  exact Measure.support_mem_ae

end BorelMixedStrategy

/-- Expected captured band from a pure action against a Borel opponent law. -/
def borelPureExpectedCapturedGap
    (gap : ℝ) (opponent : BorelMixedStrategy) (action : NNReal) : ℝ :=
  ∫ rival : NNReal,
    strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ)
      ∂(opponent.law : Measure NNReal)

/-- Expected captured band under independent draws from two Borel laws. -/
def borelExpectedCapturedGap
    (gap : ℝ) (own opponent : BorelMixedStrategy) : ℝ :=
  ∫ profile : NNReal × NNReal,
    strictPriorityCapturedGap gap (profile.1 : ℝ) (profile.2 : ℝ)
      ∂((own.law : Measure NNReal).prod
        (opponent.law : Measure NNReal))

/-- Expected payoff of a pure deviation against a Borel opponent law. -/
def borelPureExpectedPayoff
    (slotWeight gap marginalCost : ℝ)
    (opponent : BorelMixedStrategy) (action : NNReal) : ℝ :=
  slotWeight * borelPureExpectedCapturedGap gap opponent action -
    marginalCost * (action : ℝ)

/-- Expected payoff under independent mixed actions. -/
def borelExpectedPayoff
    (slotWeight gap marginalCost : ℝ)
    (own opponent : BorelMixedStrategy) : ℝ :=
  slotWeight * borelExpectedCapturedGap gap own opponent -
    marginalCost * own.meanAction

/-- Mixed best response, equivalently tested against all pure deviations. -/
def IsBorelMixedBestResponse
    (slotWeight gap marginalCost : ℝ)
    (own opponent : BorelMixedStrategy) : Prop :=
  ∀ action : NNReal,
    borelPureExpectedPayoff slotWeight gap marginalCost opponent action ≤
      borelExpectedPayoff slotWeight gap marginalCost own opponent

/-- Nash equilibrium of two independent Borel mixed strategies. -/
def IsBorelMixedNash
    (slotWeight gap marginalCost : ℝ)
    (first second : BorelMixedStrategy) : Prop :=
  IsBorelMixedBestResponse slotWeight gap marginalCost first second ∧
    IsBorelMixedBestResponse slotWeight gap marginalCost second first

/-- Expected total investment cost. -/
def borelExpectedDissipation
    (marginalCost : ℝ)
    (first second : BorelMixedStrategy) : ℝ :=
  marginalCost * (first.meanAction + second.meanAction)

theorem strictPriorityCapturedGap_le_gap
    {gap own rival : ℝ} :
    strictPriorityCapturedGap gap own rival ≤ gap := by
  simp [strictPriorityCapturedGap]

theorem strictPriorityCapturedGap_continuous (gap : ℝ) :
    Continuous (fun profile : ℝ × ℝ =>
      strictPriorityCapturedGap gap profile.1 profile.2) := by
  simp only [strictPriorityCapturedGap]
  fun_prop

theorem borelCapturedGap_integrable
    {gap : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy) :
    Integrable
      (fun profile : NNReal × NNReal =>
        strictPriorityCapturedGap gap (profile.1 : ℝ) (profile.2 : ℝ))
      ((own.law : Measure NNReal).prod
        (opponent.law : Measure NNReal)) := by
  refine Integrable.mono' (integrable_const gap) ?_ ?_
  · simp only [strictPriorityCapturedGap]
    fun_prop
  · filter_upwards with profile
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hgap)]
    exact strictPriorityCapturedGap_le_gap

theorem borelPureExpectedCapturedGap_integrable
    {gap : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy) :
    Integrable (fun action : NNReal =>
      borelPureExpectedCapturedGap gap opponent action)
      (own.law : Measure NNReal) := by
  exact (borelCapturedGap_integrable hgap own opponent).integral_prod_left

theorem borelPureExpectedPayoff_integrable
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy) :
    Integrable (fun action : NNReal =>
      borelPureExpectedPayoff slotWeight gap marginalCost opponent action)
      (own.law : Measure NNReal) := by
  exact
    ((borelPureExpectedCapturedGap_integrable hgap own opponent).const_mul
      slotWeight).sub
      (own.integrable_action.const_mul marginalCost)

/-- Fubini identifies the product-law payoff with the average of pure payoffs. -/
theorem borelExpectedCapturedGap_eq_integral_pure
    {gap : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy) :
    borelExpectedCapturedGap gap own opponent =
      ∫ action : NNReal,
        borelPureExpectedCapturedGap gap opponent action
          ∂(own.law : Measure NNReal) := by
  symm
  exact integral_integral (borelCapturedGap_integrable hgap own opponent)

/-- The mixed payoff is literally the expectation of pure-action payoffs. -/
theorem borelExpectedPayoff_eq_integral_pure
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy) :
    borelExpectedPayoff slotWeight gap marginalCost own opponent =
      ∫ action : NNReal,
        borelPureExpectedPayoff slotWeight gap marginalCost opponent action
          ∂(own.law : Measure NNReal) := by
  have hCaptured :=
    (borelPureExpectedCapturedGap_integrable hgap own opponent).const_mul
      slotWeight
  have hCost := own.integrable_action.const_mul marginalCost
  rw [borelExpectedPayoff, BorelMixedStrategy.meanAction]
  simp_rw [borelPureExpectedPayoff]
  rw [integral_sub hCaptured hCost,
    integral_const_mul, integral_const_mul,
    borelExpectedCapturedGap_eq_integral_pure hgap]

theorem borelPureExpectedCapturedGap_zero
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy) :
    borelPureExpectedCapturedGap gap opponent 0 = 0 := by
  simp [borelPureExpectedCapturedGap, strictPriorityCapturedGap, hgap]

theorem borelPureExpectedPayoff_zero
    (slotWeight marginalCost : ℝ) {gap : ℝ} (hgap : 0 ≤ gap)
    (opponent : BorelMixedStrategy) :
    borelPureExpectedPayoff slotWeight gap marginalCost opponent 0 = 0 := by
  simp [borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_zero hgap]

/-- Every player's equilibrium payoff is nonnegative because action zero pays zero. -/
theorem borelMixedBestResponse_payoff_nonneg
    {slotWeight gap marginalCost : ℝ}
    {own opponent : BorelMixedStrategy}
    (hgap : 0 ≤ gap)
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent) :
    0 ≤ borelExpectedPayoff slotWeight gap marginalCost own opponent := by
  simpa [borelPureExpectedPayoff_zero slotWeight marginalCost hgap] using hbest 0

/-- Pure expected captured surplus varies continuously with one's action. -/
theorem borelPureExpectedCapturedGap_continuous
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy) :
    Continuous (borelPureExpectedCapturedGap gap opponent) := by
  unfold borelPureExpectedCapturedGap
  apply continuous_of_dominated (bound := fun _ : NNReal => gap)
  · intro action
    simp only [strictPriorityCapturedGap]
    fun_prop
  · intro action
    filter_upwards with rival
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hgap)]
    exact strictPriorityCapturedGap_le_gap
  · exact integrable_const gap
  · filter_upwards with rival
    simp only [strictPriorityCapturedGap]
    fun_prop

theorem borelPureExpectedPayoff_continuous
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (opponent : BorelMixedStrategy) :
    Continuous
      (borelPureExpectedPayoff slotWeight gap marginalCost opponent) := by
  unfold borelPureExpectedPayoff
  exact
    (continuous_const.mul
      (borelPureExpectedCapturedGap_continuous hgap opponent)).sub
      (continuous_const.mul continuous_subtype_val)

/-- A continuous function that is almost everywhere constant equals that
constant at every point in the measure's topological support. -/
theorem eq_on_measureSupport_of_continuous_of_ae_eq
    {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X]
    {μ : Measure X} {f : X → ℝ} {constant : ℝ}
    (hcontinuous : Continuous f)
    (hae : f =ᵐ[μ] (fun _ => constant)) :
    ∀ x ∈ μ.support, f x = constant := by
  intro x hx
  by_contra hne
  have hClosed : IsClosed {y : X | f y = constant} := by
    change IsClosed (f ⁻¹' ({constant} : Set ℝ))
    exact (isClosed_singleton : IsClosed ({constant} : Set ℝ)).preimage
      hcontinuous
  have hOpen : IsOpen {y : X | f y ≠ constant} := by
    simpa only [compl_setOf] using hClosed.isOpen_compl
  have hMem : x ∈ {y : X | f y ≠ constant} := hne
  have hpos : 0 < μ {y : X | f y ≠ constant} :=
    (Measure.mem_support_iff_forall x).mp hx _ (hOpen.mem_nhds hMem)
  have hzero : μ {y : X | f y ≠ constant} = 0 := by
    rw [← compl_compl {y : X | f y ≠ constant}, ← mem_ae_iff]
    filter_upwards [hae] with y hy
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    exact hy
  exact (ne_of_gt hpos) hzero

/-- Because the strategy's payoff is the average of pure payoffs and no pure
deviation beats it, almost every action in a best-response law is indifferent. -/
theorem borelMixedBestResponse_payoff_ae_eq
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse
      slotWeight gap marginalCost own opponent) :
    (fun action : NNReal =>
      borelPureExpectedPayoff slotWeight gap marginalCost opponent action) =ᵐ[
        (own.law : Measure NNReal)]
      (fun _ => borelExpectedPayoff
        slotWeight gap marginalCost own opponent) := by
  have hintegrable :=
    borelPureExpectedPayoff_integrable
      (slotWeight := slotWeight) (marginalCost := marginalCost)
      hgap own opponent
  have hconstant : Integrable
      (fun _ : NNReal =>
        borelExpectedPayoff slotWeight gap marginalCost own opponent)
      (own.law : Measure NNReal) :=
    integrable_const _
  have hle :
      (fun action : NNReal =>
        borelPureExpectedPayoff slotWeight gap marginalCost opponent action) ≤ᵐ[
          (own.law : Measure NNReal)]
        (fun _ => borelExpectedPayoff
          slotWeight gap marginalCost own opponent) :=
    Filter.Eventually.of_forall hbest
  apply (integral_eq_iff_of_ae_le hintegrable hconstant hle).mp
  rw [← borelExpectedPayoff_eq_integral_pure hgap]
  simp

/-- Support indifference is derived from the genuine mixed best response. -/
theorem borelMixedBestResponse_payoff_eq_on_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse
      slotWeight gap marginalCost own opponent) :
    ∀ action ∈ own.support,
      borelPureExpectedPayoff slotWeight gap marginalCost opponent action =
        borelExpectedPayoff slotWeight gap marginalCost own opponent := by
  exact eq_on_measureSupport_of_continuous_of_ae_eq
    (borelPureExpectedPayoff_continuous hgap opponent)
    (borelMixedBestResponse_payoff_ae_eq hgap hbest)

theorem borelPureExpectedCapturedGap_lower_eq_zero
    {gap : ℝ} (hgap : 0 ≤ gap)
    (own opponent : BorelMixedStrategy)
    (hlower : own.lowerSupport ≤ opponent.lowerSupport) :
    borelPureExpectedCapturedGap gap opponent own.lowerSupport = 0 := by
  unfold borelPureExpectedCapturedGap
  apply integral_eq_zero_of_ae
  filter_upwards [opponent.ae_mem_support] with rival hrival
  have horder : own.lowerSupport ≤ rival :=
    hlower.trans (opponent.lowerSupport_le_of_mem_support hrival)
  have horderReal : (own.lowerSupport : ℝ) ≤ (rival : ℝ) := by
    exact_mod_cast horder
  simp [strictPriorityCapturedGap, sub_nonpos.mpr horderReal, hgap]

/-- Part (i), including the nontrivial assertion that at least one equilibrium
payoff is zero.  This follows from the two closed support minima and support
indifference; it is not included in the Nash premise. -/
theorem borelMixedNash_payoff_classification
    {slotWeight gap marginalCost : ℝ}
    (hgap : 0 ≤ gap) (hcost : 0 ≤ marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash
      slotWeight gap marginalCost first second) :
    (0 ≤ borelExpectedPayoff
        slotWeight gap marginalCost first second) ∧
      (0 ≤ borelExpectedPayoff
        slotWeight gap marginalCost second first) ∧
      (borelExpectedPayoff slotWeight gap marginalCost first second = 0 ∨
        borelExpectedPayoff slotWeight gap marginalCost second first = 0) := by
  have hfirstNonneg :=
    borelMixedBestResponse_payoff_nonneg hgap hnash.1
  have hsecondNonneg :=
    borelMixedBestResponse_payoff_nonneg hgap hnash.2
  refine ⟨hfirstNonneg, hsecondNonneg, ?_⟩
  by_cases hlower : first.lowerSupport ≤ second.lowerSupport
  · left
    have hsupport :=
      borelMixedBestResponse_payoff_eq_on_support hgap hnash.1
        first.lowerSupport first.lowerSupport_mem_support
    have hcaptured :=
      borelPureExpectedCapturedGap_lower_eq_zero hgap first second hlower
    have hpureNonpos :
        borelPureExpectedPayoff slotWeight gap marginalCost
          second first.lowerSupport ≤ 0 := by
      rw [borelPureExpectedPayoff, hcaptured]
      have haction : 0 ≤ (first.lowerSupport : ℝ) := by positivity
      nlinarith
    exact le_antisymm (by simpa [hsupport] using hpureNonpos) hfirstNonneg
  · right
    have hlower' : second.lowerSupport ≤ first.lowerSupport :=
      le_of_lt (lt_of_not_ge hlower)
    have hsupport :=
      borelMixedBestResponse_payoff_eq_on_support hgap hnash.2
        second.lowerSupport second.lowerSupport_mem_support
    have hcaptured :=
      borelPureExpectedCapturedGap_lower_eq_zero hgap second first hlower'
    have hpureNonpos :
        borelPureExpectedPayoff slotWeight gap marginalCost
          first second.lowerSupport ≤ 0 := by
      rw [borelPureExpectedPayoff, hcaptured]
      have haction : 0 ≤ (second.lowerSupport : ℝ) := by positivity
      nlinarith
    exact le_antisymm (by simpa [hsupport] using hpureNonpos) hsecondNonneg

theorem borelSymmetricMixedNash_payoff_eq_zero
    {slotWeight marginalCost : ℝ} {gap : NNReal}
    (hcost : 0 ≤ marginalCost) (strategy : BorelMixedStrategy)
    (hnash : IsBorelMixedNash slotWeight (gap : ℝ) marginalCost
      strategy strategy) :
    borelExpectedPayoff slotWeight (gap : ℝ) marginalCost
      strategy strategy = 0 := by
  have hclass := borelMixedNash_payoff_classification
    (show 0 ≤ (gap : ℝ) by positivity) hcost hnash
  exact hclass.2.2.elim id id

/-! ## The zero-payoff class -/

/-- The `(index+1)`-st pure deviation, namely one more contested band. -/
def borelRungAction (gap : NNReal) (index : ℕ) : NNReal :=
  (index + 1) * gap

/-- Sum of captured bands from deviations `G,2G,...,depth*G` against one
realized rival action. -/
def borelRungCapturedSum (gap : NNReal) (rival : ℝ) (depth : ℕ) : ℝ :=
  ∑ index ∈ Finset.range depth,
    strictPriorityCapturedGap (gap : ℝ)
      (borelRungAction gap index : ℝ) rival

theorem borelCapturedGapAgainst_integrable
    (gap : NNReal) (opponent : BorelMixedStrategy) (action : NNReal) :
    Integrable
      (fun rival : NNReal =>
        strictPriorityCapturedGap (gap : ℝ)
          (action : ℝ) (rival : ℝ))
      (opponent.law : Measure NNReal) := by
  refine Integrable.mono' (integrable_const (gap : ℝ)) ?_ ?_
  · simp only [strictPriorityCapturedGap]
    fun_prop
  · filter_upwards with rival
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg (by positivity))]
    exact strictPriorityCapturedGap_le_gap

/-- Pointwise telescoping inequality behind the paper's summed CDF windows:
the sum of the captured bands at deviations `G,...,depth*G` is at least
`depth*G-rival`. -/
theorem depth_mul_gap_sub_le_borelRungCapturedSum
    (gap : NNReal) (rival : NNReal) :
    ∀ depth : ℕ,
      (depth : ℝ) * (gap : ℝ) - (rival : ℝ) ≤
        borelRungCapturedSum gap rival depth
  | 0 => by simp [borelRungCapturedSum]
  | depth + 1 => by
      rw [borelRungCapturedSum, Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      have haction :
          (borelRungAction gap depth : ℝ) =
            ((depth : ℝ) + 1) * (gap : ℝ) := by
        simp [borelRungAction]
      by_cases hlower :
          (rival : ℝ) ≤ (depth : ℝ) * (gap : ℝ)
      · have hdiff :
            (gap : ℝ) ≤
              ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) := by
          nlinarith
        have hnonneg :
            0 ≤ ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) :=
          le_trans (by positivity) hdiff
        have hcaptured :
            strictPriorityCapturedGap (gap : ℝ)
                (borelRungAction gap depth : ℝ) (rival : ℝ) =
              (gap : ℝ) := by
          rw [haction, strictPriorityCapturedGap, max_eq_left hnonneg,
            min_eq_right hdiff]
        rw [hcaptured]
        have hinduction :=
          depth_mul_gap_sub_le_borelRungCapturedSum gap rival depth
        unfold borelRungCapturedSum at hinduction
        nlinarith
      · have hgreater :
            (depth : ℝ) * (gap : ℝ) < (rival : ℝ) :=
          lt_of_not_ge hlower
        have hdiffLe :
            ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) ≤
              (gap : ℝ) := by
          nlinarith
        have hsumNonneg :
            0 ≤ ∑ index ∈ Finset.range depth,
              strictPriorityCapturedGap (gap : ℝ)
                (borelRungAction gap index : ℝ) (rival : ℝ) := by
          exact Finset.sum_nonneg fun _ _ =>
            strictPriorityCapturedGap_nonneg (by positivity)
        by_cases hnext :
            (rival : ℝ) ≤ ((depth : ℝ) + 1) * (gap : ℝ)
        · have hnonneg :
              0 ≤ ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) :=
            sub_nonneg.mpr hnext
          have hcaptured :
              strictPriorityCapturedGap (gap : ℝ)
                  (borelRungAction gap depth : ℝ) (rival : ℝ) =
                ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) := by
            rw [haction, strictPriorityCapturedGap, max_eq_left hnonneg,
              min_eq_left hdiffLe]
          rw [hcaptured]
          nlinarith
        · have hdiff :
              ((depth : ℝ) + 1) * (gap : ℝ) - (rival : ℝ) ≤ 0 :=
            sub_nonpos.mpr (le_of_not_ge hnext)
          have hcaptured :
              strictPriorityCapturedGap (gap : ℝ)
                  (borelRungAction gap depth : ℝ) (rival : ℝ) = 0 := by
            rw [haction, strictPriorityCapturedGap, max_eq_right hdiff,
              min_eq_left (by positivity)]
          rw [hcaptured]
          nlinarith

/-- Integrating the pointwise rung inequality turns it into a first-moment
bound.  This is the measure-theoretic counterpart of
`E[a] >= integral_0^J (1-F)`. -/
theorem depth_mul_gap_sub_meanAction_le_sum_pureCaptured
    (gap : NNReal) (opponent : BorelMixedStrategy) (depth : ℕ) :
    (depth : ℝ) * (gap : ℝ) - opponent.meanAction ≤
      ∑ index ∈ Finset.range depth,
        borelPureExpectedCapturedGap (gap : ℝ) opponent
          (borelRungAction gap index) := by
  have hleft : Integrable
      (fun rival : NNReal =>
        (depth : ℝ) * (gap : ℝ) - (rival : ℝ))
      (opponent.law : Measure NNReal) :=
    (integrable_const _).sub opponent.integrable_action
  have hterm : ∀ index ∈ Finset.range depth,
      Integrable
        (fun rival : NNReal =>
          strictPriorityCapturedGap (gap : ℝ)
            (borelRungAction gap index : ℝ) (rival : ℝ))
        (opponent.law : Measure NNReal) :=
    fun index _ =>
      borelCapturedGapAgainst_integrable gap opponent
        (borelRungAction gap index)
  have hright : Integrable
      (fun rival : NNReal =>
        ∑ index ∈ Finset.range depth,
          strictPriorityCapturedGap (gap : ℝ)
            (borelRungAction gap index : ℝ) (rival : ℝ))
      (opponent.law : Measure NNReal) :=
    integrable_finsetSum _ hterm
  have hintegral := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall
      (fun rival =>
        depth_mul_gap_sub_le_borelRungCapturedSum gap rival depth))
  rw [integral_sub (integrable_const _) opponent.integrable_action,
    integral_const, probReal_univ, one_smul,
    integral_finsetSum _ hterm] at hintegral
  simpa [BorelMixedStrategy.meanAction,
    borelPureExpectedCapturedGap] using hintegral

theorem sum_range_succ_natCast_eq (depth : ℕ) :
    ∑ index ∈ Finset.range depth, ((index : ℝ) + 1) =
      (depth : ℝ) * ((depth : ℝ) + 1) / 2 := by
  rw [Finset.sum_add_distrib, sum_range_natCast_eq]
  simp
  ring

/-- A zero-payoff best response forces the opponent's first moment above the
paper's exact `J - q J(J+1)/2` bound.  The inequality is derived solely from
actual pure deviations in the mixed Nash definition. -/
theorem zeroPayoff_opponent_meanAction_lower_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (gap : NNReal) (depth : ℕ)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost own opponent)
    (hzero : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost own opponent = 0) :
    (depth : ℝ) * (gap : ℝ) -
        (marginalCost / slotWeight) * (gap : ℝ) *
          ((depth : ℝ) * ((depth : ℝ) + 1) / 2) ≤
      opponent.meanAction := by
  have hpure : ∀ index ∈ Finset.range depth,
      borelPureExpectedCapturedGap (gap : ℝ) opponent
          (borelRungAction gap index) ≤
        (marginalCost / slotWeight) *
          (borelRungAction gap index : ℝ) := by
    intro index _
    have hdeviation := hbest (borelRungAction gap index)
    rw [hzero, borelPureExpectedPayoff] at hdeviation
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hweight).2
    nlinarith
  have hsum :
      ∑ index ∈ Finset.range depth,
          borelPureExpectedCapturedGap (gap : ℝ) opponent
            (borelRungAction gap index) ≤
        ∑ index ∈ Finset.range depth,
          (marginalCost / slotWeight) *
            (borelRungAction gap index : ℝ) := by
    exact Finset.sum_le_sum hpure
  have hlower :=
    depth_mul_gap_sub_meanAction_le_sum_pureCaptured gap opponent depth
  have hsumFormula :
      ∑ index ∈ Finset.range depth,
          (marginalCost / slotWeight) *
            (borelRungAction gap index : ℝ) =
          (marginalCost / slotWeight) * (gap : ℝ) *
          ((depth : ℝ) * ((depth : ℝ) + 1) / 2) := by
    have hcoe : ∀ index : ℕ,
        (borelRungAction gap index : ℝ) =
          ((index : ℝ) + 1) * (gap : ℝ) := by
      intro index
      norm_num [borelRungAction]
    simp_rw [hcoe]
    rw [← Finset.mul_sum, ← Finset.sum_mul,
      sum_range_succ_natCast_eq]
    ring
  rw [hsumFormula] at hsum
  linarith

end

end SmoothingCliff.Racing
