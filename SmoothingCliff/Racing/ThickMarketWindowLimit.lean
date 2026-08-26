import SmoothingCliff.Racing.HeterogeneousWindowFloor
import SmoothingCliff.Racing.DissipationFloor

/-!
# The heterogeneous window floor at a thick-market endpoint

This file records the deterministic limit calculation used on the
strict-priority side of the thick-market theorem.  If the runner-up premium
and the leading premium both converge to the public upper endpoint, then the
corrected heterogeneous window floor converges to its common-premium value.
The argument is separate from the order-statistic proof that supplies those
two convergences.
-/

namespace SmoothingCliff.Racing

open Filter Topology

noncomputable section

/-- The corrected heterogeneous bracket converges to its common-premium
value whenever both top premia converge to the same endpoint. -/
theorem heterogeneousShiftedWindowBracket_tendsto_endpoint
    {q varsigma endpoint : ℝ} {runner leader : ℕ → ℝ}
    (hrunner : Tendsto runner atTop (𝓝 endpoint))
    (hleader : Tendsto leader atTop (𝓝 endpoint)) :
    Tendsto
      (fun n => heterogeneousShiftedWindowBracket
        q varsigma (runner n) (leader n))
      atTop (𝓝 (endpoint * (2 - varsigma - q))) := by
  simpa [heterogeneousShiftedWindowBracket] using
    (hrunner.mul_const (2 - varsigma - q)).sub
      ((hleader.sub hrunner).const_mul (2 * q))

/-- Continuity of the positive part lifts the preceding bracket limit to the
displayed heterogeneous window floor. -/
theorem heterogeneousShiftedWindowFloor_tendsto_endpoint
    {slotWeight q varsigma endpoint : ℝ} {runner leader : ℕ → ℝ}
    (hrunner : Tendsto runner atTop (𝓝 endpoint))
    (hleader : Tendsto leader atTop (𝓝 endpoint)) :
    Tendsto
      (fun n => heterogeneousShiftedWindowFloor
        slotWeight q varsigma (runner n) (leader n))
      atTop
      (𝓝 (slotWeight * varsigma / 2 *
        max (endpoint * (2 - varsigma - q)) 0)) := by
  have hbracket := heterogeneousShiftedWindowBracket_tendsto_endpoint
    (q := q) (varsigma := varsigma) hrunner hleader
  unfold heterogeneousShiftedWindowFloor
  exact tendsto_const_nhds.mul (hbracket.max tendsto_const_nhds)

/-- In the paper's parameter range the limiting positive part is inactive,
so the endpoint floor has the displayed product form. -/
theorem heterogeneousShiftedWindowFloor_tendsto_endpoint_of_nonneg
    {slotWeight q varsigma endpoint : ℝ} {runner leader : ℕ → ℝ}
    (hendpoint : 0 ≤ endpoint)
    (hcoefficient : 0 ≤ 2 - varsigma - q)
    (hrunner : Tendsto runner atTop (𝓝 endpoint))
    (hleader : Tendsto leader atTop (𝓝 endpoint)) :
    Tendsto
      (fun n => heterogeneousShiftedWindowFloor
        slotWeight q varsigma (runner n) (leader n))
      atTop
      (𝓝 (slotWeight * endpoint / 2 *
        (varsigma * (2 - varsigma - q)))) := by
  have hlimit := heterogeneousShiftedWindowFloor_tendsto_endpoint
    (slotWeight := slotWeight) (q := q) (varsigma := varsigma)
    hrunner hleader
  convert hlimit using 1
  rw [max_eq_left (mul_nonneg hendpoint hcoefficient)]
  ring_nf

/-- The integer-window relation converts the exact endpoint constant into the
simpler prize-net-of-one-band lower bound. -/
theorem heterogeneousWindow_endpoint_ge_prizeNetCost
    {slotWeight endpoint q varsigma : ℝ}
    (hweight : 0 ≤ slotWeight) (hendpoint : 0 ≤ endpoint)
    (hq : 0 < q) (hvarsigma : varsigma ≤ 1)
    (hnext : 1 < varsigma + q) :
    slotWeight * endpoint / 2 * (1 - q) ≤
      slotWeight * endpoint / 2 *
        (varsigma * (2 - varsigma - q)) := by
  exact mul_le_mul_of_nonneg_left
    (lattice_floor_ge_prize_net_cost hq hvarsigma hnext)
    (by positivity)

end

end SmoothingCliff.Racing
