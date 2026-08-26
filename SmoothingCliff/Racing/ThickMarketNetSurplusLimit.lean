import Mathlib

/-!
# Asymptotic accounting for thick-market dominance

The probabilistic part of the thick-market theorem supplies a dissipation
floor converging to a positive constant and a water-filling loss converging to
zero.  This file records the filter-level accounting that turns those two
limits into eventual and asymptotic net-surplus dominance.
-/

namespace SmoothingCliff.Racing

open Filter Topology Set

/-- A convergent positive floor minus a vanishing loss is eventually
positive. -/
theorem eventually_floor_sub_loss_pos
    {floor loss : ℕ → ℝ} {limit : ℝ}
    (hfloor : Tendsto floor atTop (𝓝 limit))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hlimit : 0 < limit) :
    ∀ᶠ n in atTop, 0 < floor n - loss n := by
  have hmargin : Tendsto (fun n => floor n - loss n) atTop (𝓝 limit) := by
    simpa using hfloor.sub hloss
  exact hmargin (Ioi_mem_nhds hlimit)

/-- Any pointwise net-surplus gain above the floor-minus-loss margin is
eventually strictly positive. -/
theorem eventually_netSurplusGain_pos
    {floor loss gain : ℕ → ℝ} {limit : ℝ}
    (hfloor : Tendsto floor atTop (𝓝 limit))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hlimit : 0 < limit)
    (hgain : ∀ n, floor n - loss n ≤ gain n) :
    ∀ᶠ n in atTop, 0 < gain n := by
  filter_upwards [eventually_floor_sub_loss_pos hfloor hloss hlimit]
    with n hn
  exact hn.trans_le (hgain n)

/-- Epsilon form of the paper's lower-limit conclusion.  It avoids hiding
the content behind a particular `liminf` API: every strict level below the
limiting dissipation constant eventually lower-bounds the net-surplus gain. -/
theorem eventually_netSurplusGain_ge_limit_sub_epsilon
    {floor loss gain : ℕ → ℝ} {limit : ℝ}
    (hfloor : Tendsto floor atTop (𝓝 limit))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hgain : ∀ n, floor n - loss n ≤ gain n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, limit - epsilon ≤ gain n := by
  have hmargin : Tendsto (fun n => floor n - loss n) atTop (𝓝 limit) := by
    simpa using hfloor.sub hloss
  have hthreshold : limit - epsilon < limit := by linarith
  filter_upwards [hmargin (Ioi_mem_nhds hthreshold)] with n hn
  exact hn.le.trans (hgain n)

end SmoothingCliff.Racing
