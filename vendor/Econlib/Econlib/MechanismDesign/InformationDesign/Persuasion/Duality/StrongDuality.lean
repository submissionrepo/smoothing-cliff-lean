/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Perturbation
public import Econlib.Probability.ProbDist.Borel

/-!
# KR-Lipschitz preservation of the concave closure

If the sender's value `V : ProbDist Ω → ℝ` is bounded, upper semicontinuous, and Lipschitz under
the Kantorovich–Rubinstein metric, then so is the concave closure `V̂`.

This identifies KR-Lipschitz continuity as a sufficient condition for bounded steepness of the
concave closure at every prior, which feeds into dual attainment. It is a regularity ingredient,
not the strong-duality theorem itself: The strong-duality statement (primal value equals dual
value, with dual attainment) is `strongDuality_of_isKRLipschitz` in
`Persuasion.Duality.KRStrongDuality`, which consumes the constant produced here.

## Main statements

* `isKRLipschitz_concaveClosure_of_isKRLipschitz` — `V̂` inherits `V`'s KR-Lipschitz constant.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 4.

## Tags

persuasion, duality, Kantorovich-Rubinstein, Lipschitz
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

/-- **KR-Lipschitz preservation under concavification.** If `V : Δ(Ω) → ℝ` is bounded, upper
semicontinuous, and `L`-Lipschitz with respect to the Kantorovich–Rubinstein distance, then so is
the concave closure `V̂`. -/
theorem isKRLipschitz_concaveClosure_of_isKRLipschitz
    {V : ProbDist Ω → ℝ} {L : ℝ}
    (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (hV : IsKRLipschitz V L) :
    IsKRLipschitz (concaveClosure V) L := by
  intro μ₀ η₀
  obtain ⟨M, hM⟩ := hV_bdd
  have hV_le : ∀ μ, V μ ≤ M := fun μ => (abs_le.mp (hM μ)).2
  have hV_meas : Measurable V := hV_usc.measurable
  -- Any `M`-bounded measurable function is integrable against a probability measure.
  have hint_of_bound : ∀ {g : ProbDist Ω → ℝ}, Measurable g → (∀ μ, |g μ| ≤ M) →
      ∀ (ν : Measure (ProbDist Ω)) [IsProbabilityMeasure ν], Integrable g ν := by
    intro g hg_meas hg_bd ν _
    refine ⟨hg_meas.aestronglyMeasurable, (hasFiniteIntegral_const M).mono' ?_⟩
    exact Filter.Eventually.of_forall fun μ => by simpa only [Real.norm_eq_abs] using hg_bd μ
  have hV_int : ∀ σ : ProbDist (ProbDist Ω), Integrable V σ.toMeasure :=
    fun σ => hint_of_bound hV_meas hM σ.toMeasure
  obtain ⟨τ, hτ_mem, hτ_eq⟩ := primalAttainment ⟨M, hM⟩ hV_usc μ₀
  obtain ⟨η, hη_meas, hη_avg, hη_KR_int, hη_KR⟩ :=
    exists_perturbation (μ₀ := μ₀) (η₀ := η₀) hτ_mem
  let τ' : ProbDist (ProbDist Ω) := MeasureTheory.ProbabilityMeasure.map τ hη_meas.aemeasurable
  have htoMeasure : (τ' : Measure (ProbDist Ω))
      = MeasureTheory.Measure.map η τ.toMeasure :=
    MeasureTheory.ProbabilityMeasure.toMeasure_map τ hη_meas.aemeasurable
  have hτ'_feas : IsBayesPlausible η₀ τ' := by
    intro f
    have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
      simpa [ProbDist.expect] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f)
    calc ∫ μ, ProbDist.expect μ f ∂τ'.toMeasure
        = ∫ μ, ProbDist.expect μ f
            ∂MeasureTheory.Measure.map η τ.toMeasure := by rw [htoMeasure]
      _ = ∫ μ, ProbDist.expect (η μ) f ∂τ.toMeasure :=
            MeasureTheory.integral_map hη_meas.aemeasurable
              hcont.aestronglyMeasurable
      _ = ProbDist.expect η₀ f := hη_avg f
  have hτ'_value_eq : primalValue V τ' = ∫ μ, V (η μ) ∂τ.toMeasure := by
    unfold primalValue
    rw [htoMeasure]
    exact MeasureTheory.integral_map hη_meas.aemeasurable
      hV_meas.aestronglyMeasurable
  have hτ'_value_le : primalValue V τ' ≤ concaveClosure V η₀ := by
    refine le_csSup ?_ ⟨τ', hτ'_feas, rfl⟩
    refine ⟨M, ?_⟩
    rintro y ⟨σ, _, rfl⟩
    unfold primalValue
    calc ∫ μ, V μ ∂σ.toMeasure
        ≤ ∫ _, M ∂σ.toMeasure :=
          integral_mono (hV_int σ) (integrable_const _) hV_le
      _ = M := by simp
  have hVη_int : Integrable (fun μ : ProbDist Ω => V (η μ)) τ.toMeasure :=
    hint_of_bound (hV_meas.comp hη_meas) (fun μ => hM (η μ)) τ.toMeasure
  have hLKR_int :
      Integrable (fun μ : ProbDist Ω => L * krDist μ (η μ))
        τ.toMeasure := hη_KR_int.const_mul L
  have hLip_pt : ∀ μ : ProbDist Ω,
      V μ - V (η μ) ≤ L * krDist μ (η μ) := fun μ => hV μ (η μ)
  have hint_bound :
      ∫ μ, (V μ - V (η μ)) ∂τ.toMeasure
        ≤ ∫ μ, L * krDist μ (η μ) ∂τ.toMeasure :=
    integral_mono_ae ((hV_int τ).sub hVη_int) hLKR_int
      (Filter.Eventually.of_forall hLip_pt)
  have hRHS_eq :
      ∫ μ, L * krDist μ (η μ) ∂τ.toMeasure
        = L * krDist μ₀ η₀ := by
    rw [integral_const_mul, hη_KR]
  have hLHS_eq :
      ∫ μ, (V μ - V (η μ)) ∂τ.toMeasure
        = primalValue V τ - primalValue V τ' := by
    rw [integral_sub (hV_int τ) hVη_int, hτ'_value_eq]; rfl
  have hkey :
      primalValue V τ - primalValue V τ' ≤ L * krDist μ₀ η₀ := by
    rw [← hLHS_eq, ← hRHS_eq]; exact hint_bound
  have h1 : concaveClosure V μ₀ - concaveClosure V η₀
      ≤ primalValue V τ - primalValue V τ' := by
    rw [← hτ_eq]
    linarith
  exact h1.trans hkey

end StrongDuality

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
