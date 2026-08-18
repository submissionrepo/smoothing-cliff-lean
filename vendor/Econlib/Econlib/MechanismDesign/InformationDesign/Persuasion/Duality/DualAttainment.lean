/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.NoDualityGap
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Supergradient
public import Econlib.Probability.ProbDist.Borel

/-!
# Dual attainment

A supergradient of the concave closure at the prior is exactly an attaining dual price for the
original objective, once no-duality-gap identifies primal and dual values.  The headline result is
a three-way TFAE: Superdifferentiability ⇔ bounded steepness ⇔ dual attainment.

## Main statements

* `dualAttainment_of_superdifferentiable` — supergradient ⇒ attaining dual price.
* `hasBoundedSteepness_of_isSuperdifferentiable` — supergradient ⇒ bounded steepness.
* `isSuperdifferentiable_of_dualAttainment` — attaining dual price ⇒ supergradient.
* `dualAttainment_TFAE` — three-way equivalence.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 3, Lemma 6.
* Gale, D. 1967. “A Geometric Duality Theorem with Economic Applications.” *The Review of Economic
  Studies* 34 (1): 19–24. [https://doi.org/10.2307/2296568](https://doi.org/10.2307/2296568).

## Tags

persuasion, duality, dual attainment, supergradient
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## Supergradients and dual attainment -/

section DualAttainment

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]

/-- The concave closure dominates the original objective. -/
lemma le_concaveClosure
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ : ProbDist Ω) :
    V μ ≤ concaveClosure V μ := by
  unfold concaveClosure
  -- The Dirac persuasion's underlying measure is the Dirac measure at `μ`; shared by both
  -- the feasibility and the value computation below.
  have hdirac_eq : (MeasureTheory.diracProba μ :
      ProbDist (ProbDist Ω)).toMeasure = MeasureTheory.Measure.dirac μ := by
    simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]
  have hdirac_feas : IsBayesPlausible μ (MeasureTheory.diracProba μ) := by
    intro f
    have hcont : Continuous (fun ν : ProbDist Ω => ProbDist.expect ν f) := by
      simpa [ProbDist.expect] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f)
    change ∫ ν, ProbDist.expect ν f
        ∂(MeasureTheory.diracProba μ : ProbDist (ProbDist Ω)).toMeasure
        = ProbDist.expect μ f
    rw [hdirac_eq]
    exact MeasureTheory.integral_dirac' _ _ hcont.stronglyMeasurable
  have hvalue_dirac :
      primalValue V (MeasureTheory.diracProba μ) = V μ := by
    unfold primalValue
    rw [hdirac_eq]
    exact MeasureTheory.integral_dirac' _ _ hV_usc.measurable.stronglyMeasurable
  have hbd : BddAbove {y : ℝ | ∃ τ ∈ feasiblePrimal μ, y = primalValue V τ} := by
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨τ, _, rfl⟩
    unfold primalValue
    have hV_int : Integrable V τ.toMeasure := by
      refine ⟨hV_usc.measurable.aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const M).mono' ?_
      refine Filter.Eventually.of_forall fun ν => ?_
      simp only [Real.norm_eq_abs]
      exact hM ν
    calc ∫ ν, V ν ∂τ.toMeasure
        ≤ ∫ _, M ∂τ.toMeasure :=
          integral_mono hV_int (integrable_const _)
            (fun ν => (abs_le.mp (hM ν)).2)
      _ = M := by simp
  have hmem : V μ ∈ {y : ℝ | ∃ τ ∈ feasiblePrimal μ, y = primalValue V τ} := by
    refine ⟨MeasureTheory.diracProba μ, hdirac_feas, ?_⟩
    exact hvalue_dirac.symm
  exact le_csSup hbd hmem

/-- **Supergradient ⇒ attaining dual price.**

A supergradient of the concave closure at `μ₀` is an attaining dual price for the original
objective. -/
theorem dualAttainment_of_superdifferentiable
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) {μ₀ : ProbDist Ω}
    (hgap : concaveClosure V μ₀ = dualValue V μ₀)
    (hsuper : IsSuperdifferentiable (concaveClosure V) μ₀) :
    ∃ p ∈ feasibleDual V, dualObjective μ₀ p = dualValue V μ₀ := by
  obtain ⟨p, hp⟩ := hsuper
  refine ⟨p, ?_, ?_⟩
  · refine ⟨hp.lipschitz, ?_⟩
    intro μ
    exact (le_concaveClosure hV_bdd hV_usc μ).trans (hp.majorizes μ)
  · unfold dualObjective
    rw [← hp.value_eq, hgap]

end DualAttainment

/-! ## Three-way TFAE for dual attainment -/

section Theorem3

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

omit [T2Space Ω] in
/-- A `K`-Lipschitz price function has KR-Lipschitz expectation with the same constant:
`∫p dμ − ∫p dν ≤ K · krDist μ ν`.  This is the easy direction of Kantorovich–Rubinstein duality
applied to a non-normalized Lipschitz constant. -/
lemma expect_sub_le_kr_lipschitz
    {p : Ω → ℝ} {K : NNReal} (hp_lip : LipschitzWith K p) (μ ν : ProbDist Ω) :
    ProbDist.expect μ p - ProbDist.expect ν p ≤ (K : ℝ) * krDist μ ν := by
  haveI hΩ : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure (μ : Measure Ω)
  by_cases hK : K = 0
  · subst hK
    obtain ⟨ω₀⟩ := hΩ
    have hp_const : ∀ x : Ω, p x = p ω₀ := fun x => by
      have h := hp_lip.dist_le_mul x ω₀
      simp only [NNReal.coe_zero, zero_mul] at h
      exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
    have hp_eq_const : p = fun _ => p ω₀ := funext hp_const
    rw [hp_eq_const]
    simp [ProbDist.expect]
  · have hK_pos : (0 : ℝ) < (K : ℝ) := by
      rcases (zero_lt_iff (a := K)).mpr hK with h
      exact_mod_cast h
    set q : Ω → ℝ := fun x => p x / (K : ℝ) with hq_def
    have hq_lip : LipschitzWith 1 q := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      -- `dist (q x) (q y) = dist (p x) (p y) / K`, and `dist (p x) (p y) ≤ K · dist x y`.
      have h_dist_q : dist (q x) (q y) = dist (p x) (p y) / (K : ℝ) := by
        simp only [hq_def, Real.dist_eq]
        rw [show p x / (K : ℝ) - p y / (K : ℝ) = (p x - p y) / (K : ℝ) from by ring,
            abs_div, abs_of_pos hK_pos]
      rw [h_dist_q, NNReal.coe_one, one_mul, div_le_iff₀ hK_pos]
      linarith [hp_lip.dist_le_mul x y, mul_comm (dist x y) (K : ℝ)]
    have hq_le : ProbDist.expect μ q - ProbDist.expect ν q ≤ krDist μ ν :=
      le_csSup (bddAbove_krDist_setOf μ ν) ⟨q, hq_lip, rfl⟩
    have hμq : ProbDist.expect μ q = ProbDist.expect μ p / (K : ℝ) := by
      simp [q, ProbDist.expect, integral_div]
    have hνq : ProbDist.expect ν q = ProbDist.expect ν p / (K : ℝ) := by
      simp [q, ProbDist.expect, integral_div]
    rw [hμq, hνq, div_sub_div_same, div_le_iff₀ hK_pos] at hq_le
    linarith [hq_le, mul_comm (krDist μ ν) (K : ℝ)]

/-- **Easy direction: Supergradient ⇒ bounded steepness.**

Existence of a Lipschitz supergradient implies bounded steepness with the supergradient's Lipschitz
constant. -/
theorem hasBoundedSteepness_of_isSuperdifferentiable
    {Vhat : ProbDist Ω → ℝ} {μ₀ : ProbDist Ω}
    (hsuper : IsSuperdifferentiable Vhat μ₀) :
    ∃ L : ℝ, HasBoundedSteepness Vhat μ₀ L := by
  obtain ⟨p, hsg⟩ := hsuper
  obtain ⟨K, hK_lip⟩ := hsg.lipschitz
  refine ⟨(K : ℝ), fun μ hμ_ne => ?_⟩
  have hdist_pos : 0 < krDist μ μ₀ := by
    refine lt_of_le_of_ne (krDist_nonneg μ μ₀) (Ne.symm ?_)
    intro h
    exact hμ_ne (krDist_eq_zero_iff.mp h)
  refine (div_le_iff₀ hdist_pos).mpr ?_
  calc Vhat μ - Vhat μ₀
      ≤ ProbDist.expect μ p - ProbDist.expect μ₀ p := by
        have hμ_le := hsg.majorizes μ
        have hμ₀_eq := hsg.value_eq
        linarith
    _ ≤ (K : ℝ) * krDist μ μ₀ :=
        expect_sub_le_kr_lipschitz hK_lip μ μ₀

/-- **Dual attainment ⇒ superdifferentiable.**

Under no-duality-gap, an attaining dual price is a supergradient of the concave closure. -/
theorem isSuperdifferentiable_of_dualAttainment
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) {μ₀ : ProbDist Ω}
    (hattain : ∃ p ∈ feasibleDual V, dualObjective μ₀ p = dualValue V μ₀) :
    IsSuperdifferentiable (concaveClosure V) μ₀ := by
  obtain ⟨p, hp_feas, hp_value⟩ := hattain
  have hgap : ∀ μ : ProbDist Ω, concaveClosure V μ = dualValue V μ :=
    fun μ => noDualityGap hV_bdd hV_usc μ
  refine ⟨p, hp_feas.lipschitz, ?_, ?_⟩
  · rw [hgap, ← hp_value]; rfl
  · intro μ
    rw [hgap]
    refine csInf_le ?_ ⟨p, hp_feas, rfl⟩
    refine ⟨V μ, ?_⟩
    rintro y ⟨q, hq_feas, rfl⟩
    exact hq_feas.majorizes μ

variable [Inhabited Ω]

/-- **Three-way TFAE for dual attainment.**

Under boundedness and upper-semicontinuity of `V`, the following three properties of the prior `μ₀`
are equivalent:

* the concave closure `V̂` is **superdifferentiable** at `μ₀`;
* `V̂` has **bounded steepness** at `μ₀`;
* the dual problem `(D)` **attains** its value at `μ₀`.

This is the persuasion analog of Gale's (1967) duality theorem: The Lipschitz dual price acts as
the supergradient and as the attaining dual solution simultaneously. -/
theorem dualAttainment_TFAE
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω) :
    List.TFAE [
      IsSuperdifferentiable (concaveClosure V) μ₀,
      ∃ L : ℝ, HasBoundedSteepness (concaveClosure V) μ₀ L,
      ∃ p ∈ feasibleDual V, dualObjective μ₀ p = dualValue V μ₀
    ] := by
  tfae_have h12 : 1 → 2 := hasBoundedSteepness_of_isSuperdifferentiable
  tfae_have h23 : 2 → 3 := by
    rintro ⟨L, hsteep⟩
    set L₀ : ℝ := max L 0 with hL₀_def
    have hL₀_nn : 0 ≤ L₀ := le_max_right _ _
    have hsteep' : HasBoundedSteepness (concaveClosure V) μ₀ L₀ := by
      intro μ hμ_ne
      exact (hsteep μ hμ_ne).trans (le_max_left _ _)
    have hsuper :=
      concaveClosure_isSuperdifferentiable_of_hasBoundedSteepness
        hL₀_nn hV_bdd hV_usc μ₀ hsteep'
    have hgap : concaveClosure V μ₀ = dualValue V μ₀ :=
      noDualityGap hV_bdd hV_usc μ₀
    exact dualAttainment_of_superdifferentiable hV_bdd hV_usc hgap hsuper
  tfae_have h31 : 3 → 1 := isSuperdifferentiable_of_dualAttainment hV_bdd hV_usc
  tfae_finish

end Theorem3

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
