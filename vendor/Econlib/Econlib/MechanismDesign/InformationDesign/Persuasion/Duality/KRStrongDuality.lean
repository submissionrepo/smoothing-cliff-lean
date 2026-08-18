/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.ComplementarySlackness
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.DualAttainment
public import Econlib.Probability.ProbDist.Borel

/-!
# Strong duality from KR-Lipschitz objective

If the sender's value `V` is Lipschitz under the Kantorovich–Rubinstein distance, bounded, and
upper semicontinuous, then strong duality holds: The concave closure equals the concave envelope,
the primal supremum is attained, and the dual infimum is attained by a Lipschitz price function.

## Main statements

* `strongDuality_of_isKRLipschitz` — strong duality + primal + dual attainment under KR-Lipschitz
  `V`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Corollary 2.

## Tags

persuasion, duality, strong duality, Kantorovich-Rubinstein
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

section StrongDuality

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

/-- **Strong duality from a KR-Lipschitz objective.**

If `V` is Lipschitz on `Δ(Ω)` with respect to the Kantorovich–Rubinstein distance, bounded, and
upper semicontinuous, then strong duality holds: The concave closure equals the concave envelope,
the primal sup is attained, and the dual `inf` is attained by some Lipschitz price function. -/
theorem strongDuality_of_isKRLipschitz
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    -- measurability is implied by hV_usc/hV_lip below and unused in the proof; kept in the
    -- signature to document the standing assumption on V for readers of this result.
    (_hV_meas : Measurable V) (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (hV_lip : IsKRLipschitz V L)
    (μ₀ : ProbDist Ω) :
    concaveClosure V μ₀ = dualValue V μ₀ ∧
    (∃ τ ∈ feasiblePrimal μ₀, primalValue V τ = concaveClosure V μ₀) ∧
    (∃ p ∈ feasibleDual V, dualObjective μ₀ p = dualValue V μ₀) := by
  have hgap_primal := noDualityGap_and_primalAttainment hV_bdd hV_usc μ₀
  -- Dual attainment follows from superdifferentiability of the concave closure, which the
  -- KR-Lipschitz objective supplies via bounded steepness.
  have hsuper : IsSuperdifferentiable (concaveClosure V) μ₀ :=
    concaveClosure_isSuperdifferentiable_of_hasBoundedSteepness hL hV_bdd hV_usc μ₀
      (hasBoundedSteepness_of_isKRLipschitz
        (isKRLipschitz_concaveClosure_of_isKRLipschitz hV_bdd hV_usc hV_lip) μ₀)
  exact ⟨hgap_primal.1, hgap_primal.2,
    dualAttainment_of_superdifferentiable hV_bdd hV_usc hgap_primal.1 hsuper⟩

end StrongDuality

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
