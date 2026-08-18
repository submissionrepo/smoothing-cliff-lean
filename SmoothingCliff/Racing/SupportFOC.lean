import SmoothingCliff.Racing.CdfWindow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The first-order condition on the support

Support indifference makes every action in the support a global maximizer of
the pure-deviation payoff.  Written through the window form, that payoff is a
differentiable function of the action wherever the opponent's distribution
function is continuous at both ends of the window, so at an interior support
point the derivative vanishes.

The resulting equation is the recursion of `prop:sp_allequilibria` (iii): the
increment of the opponent's distribution function across one contested band is
the cost ratio, at every support point that is not blocked by an opponent atom.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The pure-deviation payoff extended to all real actions through the window
form.  It agrees with the payoff on admissible actions and is differentiable
where the opponent's distribution function is. -/
def realPureExpectedPayoff (slotWeight gap marginalCost : ℝ)
    (opponent : BorelMixedStrategy) (x : ℝ) : ℝ :=
  slotWeight * (∫ point in (x - gap)..x, opponent.cdfReal point) -
    marginalCost * x

theorem realPureExpectedPayoff_coe
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (opponent : BorelMixedStrategy) (action : NNReal) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent (action : ℝ) =
      borelPureExpectedPayoff slotWeight gap marginalCost opponent action := by
  rw [realPureExpectedPayoff, borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_eq_intervalIntegral hgap]

/-- The extended payoff differentiates to the marginal window increment net of
marginal cost. -/
theorem hasDerivAt_realPureExpectedPayoff
    {slotWeight gap marginalCost : ℝ} (opponent : BorelMixedStrategy) {x : ℝ}
    (hx : ContinuousAt opponent.cdfReal x)
    (hxgap : ContinuousAt opponent.cdfReal (x - gap)) :
    HasDerivAt (realPureExpectedPayoff slotWeight gap marginalCost opponent)
      (slotWeight * (opponent.cdfReal x - opponent.cdfReal (x - gap)) -
        marginalCost) x := by
  have hwindow := opponent.hasDerivAt_window (gap := gap) hx hxgap
  have hcost : HasDerivAt (fun y : ℝ => marginalCost * y) marginalCost x := by
    simpa using (hasDerivAt_id x).const_mul marginalCost
  exact (hwindow.const_mul slotWeight).sub hcost

/-- **Every support action is a global maximizer.**  Support indifference and
the deviation inequality together. -/
theorem borelMixedBestResponse_isMaxOn_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support)
    (deviation : NNReal) :
    borelPureExpectedPayoff slotWeight gap marginalCost opponent deviation ≤
      borelPureExpectedPayoff slotWeight gap marginalCost opponent action := by
  rw [borelMixedBestResponse_payoff_eq_on_support hgap hbest action hmem]
  exact hbest deviation

/-- The extended payoff has a local maximum at every interior support point:
positive actions have a neighbourhood of admissible actions. -/
theorem isLocalMax_realPureExpectedPayoff
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) (hpos : 0 < (action : ℝ)) :
    IsLocalMax (realPureExpectedPayoff slotWeight gap marginalCost opponent)
      (action : ℝ) := by
  have hnhds : Set.Ioi (0 : ℝ) ∈ nhds (action : ℝ) :=
    isOpen_Ioi.mem_nhds hpos
  filter_upwards [hnhds] with x hx
  have hxle : (0 : ℝ) ≤ x := le_of_lt hx
  have hcoe : ((x.toNNReal : NNReal) : ℝ) = x := Real.coe_toNNReal x hxle
  calc realPureExpectedPayoff slotWeight gap marginalCost opponent x
      = borelPureExpectedPayoff slotWeight gap marginalCost opponent
          x.toNNReal := by
        rw [← realPureExpectedPayoff_coe hgap opponent x.toNNReal, hcoe]
    _ ≤ borelPureExpectedPayoff slotWeight gap marginalCost opponent action :=
        borelMixedBestResponse_isMaxOn_support hgap hbest hmem _
    _ = realPureExpectedPayoff slotWeight gap marginalCost opponent
          (action : ℝ) := (realPureExpectedPayoff_coe hgap _ _).symm

/-- **The support recursion.**  At an interior support point where the
opponent's distribution function is continuous at both ends of the contested
window, the increment of that distribution function across the window is the
cost ratio. -/
theorem support_window_increment_eq
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) (hpos : 0 < (action : ℝ))
    (hcont : ContinuousAt opponent.cdfReal (action : ℝ))
    (hcontgap : ContinuousAt opponent.cdfReal ((action : ℝ) - gap)) :
    slotWeight *
        (opponent.cdfReal (action : ℝ) -
          opponent.cdfReal ((action : ℝ) - gap)) =
      marginalCost := by
  have hderiv :=
    hasDerivAt_realPureExpectedPayoff
      (slotWeight := slotWeight) (gap := gap) (marginalCost := marginalCost)
      opponent hcont hcontgap
  have hzero :=
    (isLocalMax_realPureExpectedPayoff hgap hbest hmem hpos).hasDerivAt_eq_zero
      hderiv
  linarith

/-- The recursion in the paper's normalized form: the distribution function
climbs by the cost ratio across each contested window. -/
theorem support_cdf_recursion
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : slotWeight ≠ 0)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) (hpos : 0 < (action : ℝ))
    (hcont : ContinuousAt opponent.cdfReal (action : ℝ))
    (hcontgap : ContinuousAt opponent.cdfReal ((action : ℝ) - gap)) :
    opponent.cdfReal (action : ℝ) =
      opponent.cdfReal ((action : ℝ) - gap) + marginalCost / slotWeight := by
  have hkey :=
    support_window_increment_eq hgap hbest hmem hpos hcont hcontgap
  field_simp
  linarith

end

end SmoothingCliff.Racing
