/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.StrongDuality
public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.ProbDist.Borel

/-!
# Discretization setup: Finite atomic priors and finite concave closure

This file links the abstract concave closure to its finite, atomic analog. Any prior on `Ω` can be
approximated by a finite atomic prior, and on such a prior the finite concave closure is bounded
above by the abstract concave closure of the original objective.

## Main statements

* `finConcaveClosure_le_concaveClosure_of_finiteLaw` — on an atomic prior `μ₀_δ` matching the
  finite coordinates `μ₀_coords`, the finite concave closure of `finiteObjective V atom` is bounded
  above by the abstract concave closure `concaveClosure V μ₀_δ`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 2.

## Tags

persuasion, duality, discretization, concave closure
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

section NoDualityGap

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

variable {n : ℕ}

/-- On an atomic prior `μ₀_δ` that matches the finite coordinates `μ₀_coords` through `finiteLaw`,
the finite concave closure of `finiteObjective V atom` is bounded above by the abstract concave
closure `concaveClosure V μ₀_δ`, for any bounded upper-semicontinuous objective `V`. -/
lemma finConcaveClosure_le_concaveClosure_of_finiteLaw
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    {V : ProbDist Ω → ℝ}
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (atom : Fin n → Ω)
    {μ₀_coords : Fin n → ℝ}
    (h_simplex : μ₀_coords ∈ stdSimplex ℝ (Fin n))
    {μ₀_δ : ProbDist Ω}
    (h_match : finiteLaw atom ⟨μ₀_coords, h_simplex⟩ = μ₀_δ) :
    finConcaveClosure (finiteObjective V atom) μ₀_coords ≤
      concaveClosure V μ₀_δ := by
  unfold finConcaveClosure concaveClosure
  refine csSup_le (finConcaveClosure_values_nonempty (finiteObjective V atom) h_simplex) ?_
  rintro v ⟨k, _hk, lam, ν, hlam_nonneg, hlam_sum, hν_simplex, hbayes, rfl⟩
  classical
  let lift_post : Fin k → ProbDist Ω := fun j => finiteLaw atom ⟨ν j, hν_simplex j⟩
  let lam_findist : FinDist (Fin k) :=
    { pmf := lam
      nonneg := hlam_nonneg
      sum_one := hlam_sum }
  let τ : ProbDist (ProbDist Ω) :=
    ProbDist.map lam_findist.toProbDist lift_post (measurable_of_finite _)
  have hτ_bayes : IsBayesPlausible μ₀_δ τ := by
    intro f
    change ProbDist.expect τ (fun μ => ProbDist.expect μ f) = ProbDist.expect μ₀_δ f
    have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
      simpa [ProbDist.expect] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f)
    rw [ProbDist.expect_map lam_findist.toProbDist lift_post
        (measurable_of_finite _) (fun μ => ProbDist.expect μ f)
        hcont.aestronglyMeasurable]
    rw [← FinDist.expect_eq_probDist_expect]
    change ∑ j, lam j * ProbDist.expect (finiteLaw atom ⟨ν j, hν_simplex j⟩) f =
        ProbDist.expect μ₀_δ f
    have hlift_f : ∀ j, ProbDist.expect (finiteLaw atom ⟨ν j, hν_simplex j⟩) f =
        ∑ i, ν j i * f (atom i) :=
      fun j => finiteLaw_expect_boundedContinuous atom ⟨ν j, hν_simplex j⟩ f
    simp_rw [hlift_f]
    rw [show
        (∑ j : Fin k, lam j * (∑ i : Fin n, ν j i * f (atom i)))
          = (∑ i : Fin n, (∑ j : Fin k, lam j * ν j i) * f (atom i)) from by
        simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]]
    have hcoord : ∀ i : Fin n, (∑ j : Fin k, lam j * ν j i) = μ₀_coords i := by
      intro i
      have h := congrFun hbayes i
      have hsmul : (∑ j, lam j • ν j) i = ∑ j, lam j * ν j i := by
        simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsmul] at h
      exact h
    simp_rw [hcoord]
    rw [show ProbDist.expect μ₀_δ f = ∑ i : Fin n, μ₀_coords i * f (atom i) from by
      rw [← h_match]
      exact finiteLaw_expect_boundedContinuous atom ⟨μ₀_coords, h_simplex⟩ f]
  have hτ_value :
      primalValue V τ =
        ∑ j : Fin k, lam j * finiteObjective V atom (ν j) := by
    unfold primalValue τ lift_post
    have hVmeas : Measurable V := hV_usc.measurable
    rw [ProbDist.map_toMeasure]
    rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
        hVmeas.aestronglyMeasurable]
    rw [show (fun j : Fin k => V (finiteLaw atom ⟨ν j, hν_simplex j⟩)) =
          (fun j : Fin k => finiteObjective V atom (ν j)) from by
      funext j
      exact (finiteObjective_of_mem (hν_simplex j)).symm]
    change ProbDist.expect lam_findist.toProbDist
        (fun j => finiteObjective V atom (ν j)) = _
    rw [← FinDist.expect_eq_probDist_expect]
    rfl
  have hτ_value_le : primalValue V τ ≤
      concaveClosure V μ₀_δ := by
    unfold concaveClosure
    refine le_csSup ?_ ?_
    · obtain ⟨M, hM⟩ := hV_bdd
      refine ⟨M, ?_⟩
      rintro w ⟨σ, _, rfl⟩
      unfold primalValue
      have hVle : ∀ μ : ProbDist Ω, V μ ≤ M := fun μ => (abs_le.mp (hM μ)).2
      have hV_int : Integrable V σ.toMeasure := by
        refine ⟨hV_usc.measurable.aestronglyMeasurable, ?_⟩
        refine (hasFiniteIntegral_const M).mono' ?_
        refine Filter.Eventually.of_forall fun μ => ?_
        simp only [Real.norm_eq_abs]
        exact hM μ
      calc ∫ μ, V μ ∂σ.toMeasure
          ≤ ∫ _, M ∂σ.toMeasure :=
            MeasureTheory.integral_mono hV_int (integrable_const _) hVle
        _ = M := by simp [MeasureTheory.probReal_univ]
    · exact ⟨τ, hτ_bayes, rfl⟩
  exact hτ_value ▸ hτ_value_le

end NoDualityGap

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
