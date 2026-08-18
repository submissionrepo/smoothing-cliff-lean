/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Basic
public import Econlib.Probability.ProbDist.Borel
public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Primal attainment

When the state space `Ω` is compact and the sender's value `V : ProbDist Ω → ℝ` is bounded upper
semicontinuous, the primal supremum `concaveClosure V μ₀` is attained: There exists a
Bayes-plausible distribution of posteriors realizing it.

## Main statements

* `feasiblePrimal_isCompact` — the Bayes-plausibility constraint set is weak-* compact.
* `primalAttainment` — the primal supremum is attained.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 2 (first conjunct).

## Tags

persuasion, duality, primal attainment, Prokhorov
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal ProbabilityMeasure
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## Compactness of the Bayes-plausibility constraint and primal attainment -/

section PrimalAttainment

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

omit [SecondCountableTopology Ω] [CompactSpace Ω] [T2Space Ω] in
/-- The posterior expectation `μ ↦ ProbDist.expect μ f` is weak-* continuous for any bounded
continuous integrand `f`. -/
private lemma continuous_expect_boundedContinuous (f : Ω →ᵇ ℝ) :
    Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
  simpa [ProbDist.expect] using
    (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := Ω) f)

/-- The Bayes-plausibility constraint set is weak-* compact when `Ω` is a compact T2 space with the
Borel σ-algebra. -/
theorem feasiblePrimal_isCompact (μ₀ : ProbDist Ω) :
    IsCompact (feasiblePrimal μ₀) := by
  haveI : CompactSpace (ProbDist Ω) :=
    instCompactSpaceProbabilityMeasure (E := Ω)
  have hclosed : IsClosed (feasiblePrimal μ₀) := by
    have hset_eq :
        feasiblePrimal μ₀ =
          ⋂ f : Ω →ᵇ ℝ, {τ : ProbDist (ProbDist Ω) |
            ∫ μ, ProbDist.expect μ f ∂τ.toMeasure = ProbDist.expect μ₀ f} := by
      ext τ
      simp only [feasiblePrimal, IsBayesPlausible, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hset_eq]
    refine isClosed_iInter (fun f => ?_)
    let gBCF : ProbDist Ω →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨_, continuous_expect_boundedContinuous f⟩
    have hint_cont : Continuous (fun τ : ProbDist (ProbDist Ω) =>
        ∫ μ, ProbDist.expect μ f ∂τ.toMeasure) := by
      simpa [gBCF] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := ProbDist Ω) gBCF)
    exact isClosed_eq hint_cont continuous_const
  exact hclosed.isCompact

/-- **Primal attainment.**

When the state space `Ω` is a compact metric space and `V` is bounded and upper semicontinuous, the
supremum defining `V̂(μ₀)` is attained by some Bayes-plausible distribution of posteriors. -/
theorem primalAttainment
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (μ₀ : ProbDist Ω) :
    ∃ τ ∈ feasiblePrimal μ₀, primalValue V τ = concaveClosure V μ₀ := by
  have hT_compact : IsCompact (feasiblePrimal μ₀) := feasiblePrimal_isCompact μ₀
  have hT_ne : (feasiblePrimal μ₀).Nonempty := by
    refine ⟨MeasureTheory.diracProba μ₀, ?_⟩
    intro f
    have hcont := continuous_expect_boundedContinuous f
    have hdirac_eq : (MeasureTheory.diracProba μ₀ :
        ProbDist (ProbDist Ω)).toMeasure = MeasureTheory.Measure.dirac μ₀ := by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]
    rw [hdirac_eq]
    exact MeasureTheory.integral_dirac' _ _ hcont.stronglyMeasurable
  have hV_uscOn : UpperSemicontinuousOn V Set.univ :=
    hV_usc.upperSemicontinuousOn _
  have hV_bdd_on : ∃ B : ℝ, ∀ μ ∈ (Set.univ : Set (ProbDist Ω)), |V μ| ≤ B := by
    obtain ⟨M, hM⟩ := hV_bdd
    exact ⟨M, fun μ _ => hM μ⟩
  have hK_compact : IsCompact (Set.univ : Set (ProbDist Ω)) := isCompact_univ
  have hUSC_on_univ :
      UpperSemicontinuousOn
        (fun τ : ProbDist (ProbDist Ω) => ∫ μ, V μ ∂(τ : Measure (ProbDist Ω)))
        {τ : ProbDist (ProbDist Ω) | (τ : Measure (ProbDist Ω)) Set.univ = 1} :=
    upperSemicontinuousOn_integral_of_bounded_upperSemicontinuousOn_compactSupport
      (X := ProbDist Ω) hK_compact hV_bdd_on hV_uscOn
  have hSet_univ :
      {τ : ProbDist (ProbDist Ω) | (τ : Measure (ProbDist Ω)) Set.univ = 1}
        = Set.univ := by
    ext τ
    simp [MeasureTheory.measure_univ]
  rw [hSet_univ] at hUSC_on_univ
  have hUSC_feas :
      UpperSemicontinuousOn (primalValue V) (feasiblePrimal μ₀) :=
    hUSC_on_univ.mono (Set.subset_univ _)
  obtain ⟨τstar, hτstar_mem, hτstar_max⟩ :=
    hUSC_feas.exists_isMaxOn hT_ne hT_compact
  refine ⟨τstar, hτstar_mem, ?_⟩
  unfold concaveClosure
  apply le_antisymm
  · refine le_csSup ?_ ⟨τstar, hτstar_mem, rfl⟩
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨τ, hτ, rfl⟩
    unfold primalValue
    have hV_le : ∀ μ, V μ ≤ M := fun μ => (abs_le.mp (hM μ)).2
    have hV_meas : AEStronglyMeasurable V τ.toMeasure :=
      hV_usc.measurable.aestronglyMeasurable
    -- `V` is `M`-bounded on the finite measure `τ`, hence integrable.
    have hV_int : Integrable V τ.toMeasure :=
      .of_bound hV_meas M <|
        Filter.Eventually.of_forall fun μ => (Real.norm_eq_abs _).le.trans (hM μ)
    calc ∫ μ, V μ ∂τ.toMeasure
        ≤ ∫ _, M ∂τ.toMeasure :=
          integral_mono hV_int (integrable_const _) hV_le
      _ = M := by simp
  · refine csSup_le ⟨_, ⟨τstar, hτstar_mem, rfl⟩⟩ ?_
    rintro y ⟨τ, hτ, rfl⟩
    exact hτstar_max hτ

end PrimalAttainment

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
