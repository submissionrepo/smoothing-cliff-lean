/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Basic

/-!
# Weak duality

The primal value of the persuasion problem is bounded above by the dual value: For every
Bayes-plausible distribution of posteriors and every Lipschitz price majorizing the value function,
the primal expected payoff is at most the dual expected price.

## Main statements

* `primalValue_le_dualObjective_of_feasible` — pairwise weak duality.
* `weakDuality` — the global inequality `concaveClosure V μ₀ ≤ dualValue V μ₀`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 1.

## Tags

persuasion, duality, weak duality
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## Weak duality inequality -/

section WeakDuality

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  [CompactSpace Ω]

omit [OpensMeasurableSpace Ω] in
/-- For any Bayes-plausible `τ` and any dual-feasible Lipschitz `p`, the primal payoff is bounded
by the dual objective.

This is the core pairwise inequality underlying weak duality.  We require `V` and `μ ↦ μ.expect p`
to be `τ`-integrable; both follow automatically when `V` is bounded measurable (e.g. bounded USC)
and `Ω` is compact, because `μ ↦ μ.expect p` is then a bounded continuous function on
`ProbDist Ω`. -/
lemma primalValue_le_dualObjective_of_feasible
    {V : ProbDist Ω → ℝ} {μ₀ : ProbDist Ω} {τ : ProbDist (ProbDist Ω)}
    {p : Ω → ℝ}
    (hV_int : Integrable V τ.toMeasure)
    (hg_int : Integrable (fun μ : ProbDist Ω => ProbDist.expect μ p) τ.toMeasure)
    (hτ : IsBayesPlausible μ₀ τ)
    (hp : IsDualFeasible V p) :
    primalValue V τ ≤ dualObjective μ₀ p := by
  let pBCF : Ω →ᵇ ℝ := lipschitzToBounded hp.lipschitz
  have step2 : ∫ μ, ProbDist.expect μ p ∂τ.toMeasure = ProbDist.expect μ₀ p := hτ pBCF
  have step1 : ∫ μ, V μ ∂τ.toMeasure
      ≤ ∫ μ, ProbDist.expect μ p ∂τ.toMeasure :=
    integral_mono_ae hV_int hg_int (Filter.Eventually.of_forall hp.majorizes)
  exact step1.trans_eq step2

omit [OpensMeasurableSpace Ω] in
/-- **Weak duality.** The concave closure is bounded above by the dual value.

We require `τ`-integrability of `V` and of `μ ↦ μ.expect p` for every feasible pair `(τ, p)`. Both
follow automatically when `V` is bounded measurable (e.g. bounded USC) and `Ω` is compact, because
then `μ ↦ μ.expect p` is a bounded continuous function on `ProbDist Ω`. -/
theorem weakDuality
    {V : ProbDist Ω → ℝ} {μ₀ : ProbDist Ω}
    (hP_nonempty : (feasiblePrimal μ₀).Nonempty)
    (hD_nonempty : (feasibleDual V).Nonempty)
    (hV_int : ∀ τ ∈ feasiblePrimal μ₀, Integrable V τ.toMeasure)
    (hg_int : ∀ τ ∈ feasiblePrimal μ₀, ∀ p ∈ feasibleDual V,
        Integrable (fun μ : ProbDist Ω => ProbDist.expect μ p) τ.toMeasure) :
    concaveClosure V μ₀ ≤ dualValue V μ₀ := by
  unfold concaveClosure dualValue
  refine csSup_le ?_ ?_
  · obtain ⟨τ, hτ⟩ := hP_nonempty
    exact ⟨primalValue V τ, ⟨τ, hτ, rfl⟩⟩
  rintro x ⟨τ, hτ, rfl⟩
  refine le_csInf ?_ ?_
  · obtain ⟨p, hp⟩ := hD_nonempty
    exact ⟨dualObjective μ₀ p, ⟨p, hp, rfl⟩⟩
  rintro y ⟨p, hp, rfl⟩
  exact primalValue_le_dualObjective_of_feasible (hV_int τ hτ)
    (hg_int τ hτ p hp) hτ hp

end WeakDuality

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
