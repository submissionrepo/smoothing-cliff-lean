/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `CountDist` Non-Vacuity Checks

Compile-time semantic witnesses for the countable-distribution carrier
`Econlib.Probability.CountDist`. The generic `ℕ`-side API (CDF recursion and limit, `expect`,
`map` functor laws) is exercised on the concrete `Poisson(2)` and `Geometric(1/2)` laws, and the
Bayes machinery is instantiated on a genuine two-state countable prior/likelihood built from
`FinDist` literals.

The CDF recursion (`cdf_zero`, `cdf_succ`) and the `+∞` limit are the orientation-critical spots —
an off-by-one in the partial-sum range or a missing top limit would break them.
-/

noncomputable section

namespace EconlibTest.Probability.CountDist

open Econlib.Probability Filter Topology

/-- A `Poisson(2)` law on `ℕ`. -/
private abbrev pois2 : CountDist ℕ := CountDist.poisson 2 (by norm_num)

/-- A `Geometric(1/2)` law on `ℕ`. -/
private abbrev geo : CountDist ℕ := CountDist.geometric (1 / 2) (by norm_num) (by norm_num)

/-- The integer outcome map `n ↦ (n : ℝ)`. -/
private abbrev natOutcome : ℕ → ℝ := fun n => (n : ℝ)

section cdf

/-- **CDF base case.** `F(0) = P(X = 0)` — the partial sum starts at the first mass. -/
theorem pois_cdf_zero : pois2.cdf 0 = pois2.pmf 0 := CountDist.cdf_zero pois2

/-- **CDF recursion.** `F(n+1) = F(n) + P(X = n+1)` — the discrete-derivative step. -/
theorem pois_cdf_succ : pois2.cdf 3 = pois2.cdf 2 + pois2.pmf 3 := CountDist.cdf_succ pois2 2

/-- The CDF at `n` is the partial sum of masses through `n` (no off-by-one in the range). -/
theorem pois_cdf_sum_range : pois2.cdf 2 = ∑ k ∈ Finset.range 3, pois2.pmf k :=
  CountDist.cdf_eq_sum_range pois2 2

/-- **The CDF exhausts the mass:** `F(n) → 1` as `n → ∞`. -/
theorem pois_cdf_tendsto : Tendsto pois2.cdf atTop (𝓝 1) := CountDist.tendsto_cdf_atTop pois2

/-- The CDF is monotone. -/
theorem pois_cdf_mono : Monotone pois2.cdf := pois2.cdf_mono

/-- **A concrete CDF value.** For `Geometric(1/2)`, `F(1) = 1/2 + 1/4 = 3/4`. -/
theorem geo_cdf_one : geo.cdf 1 = 3 / 4 := by
  rw [CountDist.cdf_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [geo, CountDist.geometric_apply]
  norm_num

end cdf

section basic

/-- The pmf is summable (a structural prerequisite for `tsum`-based facts). -/
theorem pois_summable : Summable pois2.pmf := pois2.summable_pmf

/-- **Expectation is the pmf-weighted `tsum`.** -/
theorem pois_expect_eq_tsum :
    pois2.expect natOutcome = ∑' n, pois2.pmf n * natOutcome n :=
  CountDist.expect_eq_tsum pois2 natOutcome

/-- **Concrete Poisson mean.** `E[N] = rate = 2` for `Poisson(2)` — the load-bearing semantic anchor
that a wrong weighted-series or summability bug would break (the `tsum` identity above only states
the definition). -/
theorem pois_expect_two : pois2.expect natOutcome = 2 :=
  CountDist.poisson_expect 2 (by norm_num)

/-- `ofPMF` is a right inverse of `toPMF` on the `PMF` side: `(ofPMF p).toPMF = p`. (The
`CountDist`-side round trip `ofPMF (d.toPMF) = d` is a separate identity, not tested here.) -/
theorem toPMF_ofPMF_witness : (CountDist.ofPMF pois2.toPMF).toPMF = pois2.toPMF :=
  CountDist.toPMF_ofPMF pois2.toPMF

end basic

section map

/-- **Functor identity:** `map id = id`. -/
theorem geo_map_id : geo.map id = geo := CountDist.map_id geo

/-- **Functor composition:** `map g ∘ map f = map (g ∘ f)`. -/
theorem geo_map_comp (f g : ℕ → ℕ) : (geo.map f).map g = geo.map (g ∘ f) :=
  CountDist.map_comp geo f g

/-- **Pushforward semantics.** Shifting up by one empties the mass at `0`: no source state maps to
`0` under `n ↦ n+1`. -/
theorem geo_map_shift_zero : (geo.map (fun n => n + 1)).pmf 0 = 0 := by
  rw [CountDist.map_apply]
  simp

end map

section bayes

/-- An **asymmetric** two-state countable prior `P(θ=0)=2/3`, `P(θ=1)=1/3`, built from a `FinDist`
literal. The nonuniform prior, paired with the asymmetric likelihood below, is what lets the
posterior anchors discriminate a state/signal transpose. -/
private abbrev cprior : CountDist (Fin 2) :=
  (finDist% ![2 / 3, 1 / 3] : FinDist (Fin 2)).toCountDist

/-- **Asymmetric** two-state countable likelihood with distinct rows:
`ℓ(·|θ=0) = (3/4, 1/4)` (informative), `ℓ(·|θ=1) = (1/2, 1/2)` (uninformative). Because the matrix
is not symmetric, the transposed read `(clk signal).pmf state` differs from
`(clk state).pmf signal`, so the concrete posterior values below catch a state↔signal swap. -/
private abbrev clk : Fin 2 → CountDist (Fin 2) :=
  fun i => FinDist.toCountDist
    ((![finDist% ![3 / 4, 1 / 4], finDist% ![1 / 2, 1 / 2]] : Fin 2 → FinDist (Fin 2)) i)

/-- The integer outcome map on the two states. -/
private abbrev finOutcome : Fin 2 → ℝ := fun i => (i.val : ℝ)

/-- **Signal-`0` marginal.** `P(s=0) = P(θ=0)·ℓ(0|0) + P(θ=1)·ℓ(0|1) = (2/3)(3/4) + (1/3)(1/2)
= 1/2 + 1/6 = 2/3 > 0`. The positive value licenses the *genuine* `posterior` (not just the
totalized fallback) and is the denominator in the Bayes anchors below. -/
theorem csignalMarginal_zero : CountDist.signalMarginal cprior clk 0 = 2 / 3 := by
  rw [CountDist.signalMarginal_eq_finsum]
  simp only [Fin.sum_univ_two, cprior, clk, FinDist.toCountDist, Matrix.cons_val_zero,
    Matrix.cons_val_one, FinDist.ofVec_pmf]
  norm_num

/-- **Signal-`1` marginal.** `P(s=1) = (2/3)(1/4) + (1/3)(1/2) = 1/6 + 1/6 = 1/3 > 0`. -/
theorem csignalMarginal_one : CountDist.signalMarginal cprior clk 1 = 1 / 3 := by
  rw [CountDist.signalMarginal_eq_finsum]
  simp only [Fin.sum_univ_two, cprior, clk, FinDist.toCountDist, Matrix.cons_val_zero,
    Matrix.cons_val_one, FinDist.ofVec_pmf]
  norm_num

/-- The signal-`0` marginal is positive, gating the genuine posterior. -/
private theorem csignalMarginal_zero_pos : 0 < CountDist.signalMarginal cprior clk 0 := by
  rw [csignalMarginal_zero]; norm_num

/-- The signal-`1` marginal is positive, gating the genuine posterior. -/
private theorem csignalMarginal_one_pos : 0 < CountDist.signalMarginal cprior clk 1 := by
  rw [csignalMarginal_one]; norm_num

/-- **Genuine posterior moves toward the matching state.** After signal `0`,
`P(θ=0|s=0) = P(θ=0)·ℓ(0|0)/P(s=0) = (2/3)(3/4)/(2/3) = 3/4` — the posterior on state `0` rises from
the prior `2/3` to `3/4`. A swapped `(clk s).pmf θ` read or a flipped Bayes ratio gives a different
number, so this is a discriminating witness, not a tautology. -/
theorem cposterior_zero_signal_zero :
    (CountDist.posterior cprior clk 0 csignalMarginal_zero_pos).pmf 0 = 3 / 4 := by
  rw [CountDist.posterior_apply, csignalMarginal_zero]
  simp only [cprior, clk, FinDist.toCountDist, Matrix.cons_val_zero, FinDist.ofVec_pmf]
  norm_num

/-- **Posterior on the off state after signal `0`.** `P(θ=1|s=0) = (1/3)(1/2)/(2/3) = 1/4`; with the
matching-state value `3/4` the two posterior masses sum to one. -/
theorem cposterior_one_signal_zero :
    (CountDist.posterior cprior clk 0 csignalMarginal_zero_pos).pmf 1 = 1 / 4 := by
  rw [CountDist.posterior_apply, csignalMarginal_zero]
  simp only [cprior, clk, FinDist.toCountDist, Matrix.cons_val_zero, Matrix.cons_val_one,
    FinDist.ofVec_pmf]
  norm_num

/-- **Posterior after the less-likely signal `1`.** `P(θ=0|s=1) = (2/3)(1/4)/(1/3) = 1/2`:
signal `1` is uninformative about the state under this likelihood, so the posterior on `0` falls
from the prior `2/3` to `1/2`. Distinct from the signal-`0` posterior `3/4`, so a
constant/ignore-signal implementation is refuted. -/
theorem cposterior_zero_signal_one :
    (CountDist.posterior cprior clk 1 csignalMarginal_one_pos).pmf 0 = 1 / 2 := by
  rw [CountDist.posterior_apply, csignalMarginal_one]
  simp only [cprior, clk, FinDist.toCountDist, Matrix.cons_val_zero, Matrix.cons_val_one,
    FinDist.ofVec_pmf]
  norm_num

/-- **The posterior is a genuine distribution:** its masses sum to one. Paired with the concrete
masses `3/4 + 1/4 = 1` above, this is the normalization closing the loop, not a standalone
tautology. -/
theorem cposterior_is_dist :
    ∑' θ, (CountDist.posteriorOrPrior cprior clk 0).pmf θ = 1 :=
  CountDist.posteriorOrPrior_is_dist cprior clk 0

/-- **Law of total probability** on a genuine two-state countable model: averaging the posterior on
state `0` over the signal marginals recovers the prior mass `P(θ=0)`. With asymmetric marginals
`(2/3, 1/3)` and posteriors `(3/4, 1/2)`, the identity reads `(2/3)(3/4) + (1/3)(1/2) = 2/3`, so it
genuinely averages two distinct posteriors rather than collapsing to the prior. -/
theorem ctotal_probability :
    ∑ s : Fin 2, CountDist.signalMarginal cprior clk s *
      (CountDist.posteriorOrPrior cprior clk s).pmf 0 = cprior.pmf 0 :=
  CountDist.total_probability_fintype cprior clk 0

/-- **Bayes consistency:** posterior expectations average back to the prior expectation. -/
theorem cbayes_consistent :
    ∑ s : Fin 2, CountDist.signalMarginal cprior clk s *
      (CountDist.posteriorOrPrior cprior clk s).expect finOutcome = cprior.expect finOutcome :=
  CountDist.bayes_consistent_fintype cprior clk finOutcome

end bayes

end EconlibTest.Probability.CountDist

end
