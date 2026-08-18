/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Supergradient
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.NoDualityGap
public import Econlib.Optimization.OptimalTransport.LipschitzDual
public import Econlib.Probability.ProbDist.Borel

/-!
# Superdifferentiability from bounded steepness

Bounded KR-steepness of the concave closure at the prior implies the existence of a Lipschitz
supporting price (a supergradient), bridging the metric Lipschitz condition and the Hanin / KR
representation.

## Main statements

* `hasBoundedSteepness_of_isKRLipschitz` — a KR-Lipschitz value function has bounded steepness at
  every prior.
* `concaveClosure_jensen` — Jensen's inequality for the concave closure under Bayes-plausible
  mixtures.
* `exists_kr_lipschitz_majorant` — Gale separation: Bounded steepness yields a Lipschitz supporting
  price tight at the prior.
* `concaveClosure_isSuperdifferentiable_of_hasBoundedSteepness` — bounded steepness of the concave
  closure implies superdifferentiability.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 3, Lemma 6.
* Hanin, Leonid G. 1992. “Kantorovich-Rubinstein Norm and Its Application in the Theory of
  Lipschitz Spaces.” *Proceedings of the American Mathematical Society* 115 (2): 345–52.
  [https://doi.org/10.1090/s0002-9939-1992-1097344-5](https://doi.org/10.1090/s0002-9939-1992-1097344-5).

## Tags

persuasion, duality, supergradient, Kantorovich-Rubinstein, Hanin
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## Superdifferentiability and bounded steepness -/

section Supergradient

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]

/-- A KR-Lipschitz value function has bounded steepness at every prior. -/
theorem hasBoundedSteepness_of_isKRLipschitz
    {Vhat : ProbDist Ω → ℝ} {L : ℝ}
    (hVhat_lip : IsKRLipschitz Vhat L) (μ₀ : ProbDist Ω) :
    HasBoundedSteepness Vhat μ₀ L := by
  intro μ hμ_ne
  have hdist_ne : krDist μ μ₀ ≠ 0 := by
    intro hzero
    exact hμ_ne ((krDist_eq_zero_iff.mp hzero))
  have hdist_pos : 0 < krDist μ μ₀ :=
    lt_of_le_of_ne (krDist_nonneg μ μ₀) (Ne.symm hdist_ne)
  exact (div_le_iff₀ hdist_pos).mpr (hVhat_lip μ μ₀)

/-! ### Concavity of the concave closure -/

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- The concave closure of a bounded upper-semicontinuous function is upper-semicontinuous. -/
theorem upperSemicontinuous_concaveClosure
    (V : ProbDist Ω → ℝ) (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) :
    UpperSemicontinuous (concaveClosure V) := by
  classical
  have hgap : ∀ μ : ProbDist Ω, concaveClosure V μ = dualValue V μ :=
    fun μ => noDualityGap hV_bdd hV_usc μ
  have hD_nonempty : (feasibleDual V).Nonempty := by
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨fun _ : Ω => M, ?_⟩
    refine ⟨⟨0, (LipschitzWith.const M).weaken (by simp)⟩, ?_⟩
    intro μ
    have hVM : V μ ≤ M := (abs_le.mp (hM μ)).2
    simpa [ProbDist.expect] using hVM
  let D : Type _ := {p : Ω → ℝ // p ∈ feasibleDual V}
  have henv_eq_iInf :
      dualValue V = fun μ : ProbDist Ω => ⨅ p : D, dualObjective μ p.1 := by
    funext μ
    unfold dualValue
    let S : Set ℝ := {y : ℝ | ∃ p ∈ feasibleDual V, y = dualObjective μ p}
    have hS_range : S = Set.range (fun p : D => dualObjective μ p.1) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨p.1, p.2, rfl⟩
    rw [show sInf S = sInf (Set.range (fun p : D => dualObjective μ p.1)) by rw [hS_range]]
    rfl
  have henv_usc : UpperSemicontinuous (fun μ : ProbDist Ω =>
      ⨅ p : D, dualObjective μ p.1) := by
    refine upperSemicontinuous_ciInf ?_ ?_
    · intro μ
      refine ⟨V μ, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact p.2.majorizes μ
    intro p
    have hp_cont : Continuous (fun μ : ProbDist Ω => dualObjective μ p.1) := by
      let pBCF : Ω →ᵇ ℝ := lipschitzToBounded p.2.lipschitz
      simpa [dualObjective, ProbDist.expect] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) pBCF)
    exact hp_cont.upperSemicontinuous
  rw [funext hgap, henv_eq_iInf]
  exact henv_usc

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- **Jensen's inequality for the concave closure.**

For any Bayes-plausible meta-distribution `τ ∈ Δ(Δ(Ω))` averaging to `μ₀`, the integral of the
concave closure under `τ` is at most its value at the prior. Equivalently, `concaveClosure V` is
concave on `Δ(Ω)` under the natural mixing. -/
theorem concaveClosure_jensen
    (V : ProbDist Ω → ℝ) (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    {μ₀ : ProbDist Ω} {τ : ProbDist (ProbDist Ω)}
    (hτ : IsBayesPlausible μ₀ τ) :
    ∫ μ, concaveClosure V μ ∂τ.toMeasure ≤ concaveClosure V μ₀ := by
  classical
  have hgap : ∀ μ : ProbDist Ω, concaveClosure V μ = dualValue V μ :=
    fun μ => noDualityGap hV_bdd hV_usc μ
  have hD_nonempty : (feasibleDual V).Nonempty := by
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨fun _ : Ω => M, ?_⟩
    refine ⟨⟨0, (LipschitzWith.const M).weaken (by simp)⟩, ?_⟩
    intro μ
    have hVM : V μ ≤ M := (abs_le.mp (hM μ)).2
    simpa [ProbDist.expect] using hVM
  have hVhat_usc : UpperSemicontinuous (concaveClosure V) :=
    upperSemicontinuous_concaveClosure V hV_bdd hV_usc
  obtain ⟨M, hM⟩ := hV_bdd
  have hVhat_le : ∀ μ : ProbDist Ω, concaveClosure V μ ≤ M := by
    intro μ
    unfold concaveClosure
    refine csSup_le ?_ ?_
    · refine ⟨V μ, ?_⟩
      have hdirac_eq : (MeasureTheory.diracProba μ :
          ProbDist (ProbDist Ω)).toMeasure = MeasureTheory.Measure.dirac μ := by
        simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]
      refine ⟨MeasureTheory.diracProba μ, ?_, ?_⟩
      · intro f
        have hcont : Continuous (fun ν : ProbDist Ω => ProbDist.expect ν f) := by
          simpa [ProbDist.expect] using
            (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
              (X := Ω) f)
        rw [hdirac_eq]
        exact MeasureTheory.integral_dirac' _ _ hcont.stronglyMeasurable
      · unfold primalValue
        rw [hdirac_eq]
        exact (MeasureTheory.integral_dirac' _ _
          hV_usc.measurable.stronglyMeasurable).symm
    · rintro y ⟨σ, _, rfl⟩
      unfold primalValue
      have hV_int : Integrable V σ.toMeasure := by
        refine ⟨hV_usc.measurable.aestronglyMeasurable, ?_⟩
        refine (hasFiniteIntegral_const M).mono' ?_
        refine Filter.Eventually.of_forall fun ν => ?_
        simp only [Real.norm_eq_abs]
        exact hM ν
      calc ∫ ν, V ν ∂σ.toMeasure
          ≤ ∫ _, M ∂σ.toMeasure :=
            integral_mono hV_int (integrable_const _)
              (fun ν => (abs_le.mp (hM ν)).2)
        _ = M := by simp
  have hVhat_abs : ∀ μ : ProbDist Ω, |concaveClosure V μ| ≤ M := by
    intro μ
    rw [abs_le]
    have hV_le_closure : V μ ≤ concaveClosure V μ := by
      rw [hgap μ]
      unfold dualValue
      refine le_csInf ?_ ?_
      · obtain ⟨p, hp⟩ := hD_nonempty
        exact ⟨dualObjective μ p, p, hp, rfl⟩
      rintro y ⟨p, hp, rfl⟩
      exact hp.majorizes μ
    exact ⟨(abs_le.mp (hM μ)).1.trans hV_le_closure, hVhat_le μ⟩
  have hVhat_int : Integrable (concaveClosure V) τ.toMeasure := by
    refine ⟨hVhat_usc.measurable.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const M).mono' ?_
    refine Filter.Eventually.of_forall fun μ => ?_
    simp only [Real.norm_eq_abs]
    exact hVhat_abs μ
  rw [hgap μ₀]
  refine le_csInf ?_ ?_
  · obtain ⟨p, hp⟩ := hD_nonempty
    exact ⟨dualObjective μ₀ p, p, hp, rfl⟩
  rintro y ⟨p, hp, rfl⟩
  let pBCF : Ω →ᵇ ℝ := lipschitzToBounded hp.lipschitz
  have hp_expect_cont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ p) := by
    simpa [ProbDist.expect] using
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (X := Ω) pBCF)
  have hp_expect_int : Integrable (fun μ : ProbDist Ω => ProbDist.expect μ p) τ.toMeasure := by
    let gBCF : ProbDist Ω →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨_, hp_expect_cont⟩
    exact gBCF.integrable τ.toMeasure
  have hpoint : ∀ μ : ProbDist Ω, concaveClosure V μ ≤ ProbDist.expect μ p := by
    intro μ
    rw [hgap μ]
    unfold dualValue
    refine csInf_le ?_ ⟨p, hp, rfl⟩
    refine ⟨V μ, ?_⟩
    rintro z ⟨q, hq, rfl⟩
    exact hq.majorizes μ
  calc ∫ μ, concaveClosure V μ ∂τ.toMeasure
      ≤ ∫ μ, ProbDist.expect μ p ∂τ.toMeasure :=
        integral_mono hVhat_int hp_expect_int hpoint
    _ = ProbDist.expect μ₀ p := hτ pBCF

/-! ### Gale's separation theorem -/

variable [Inhabited Ω]

/-- **Gale separation in the Kantorovich–Rubinstein normed space.**

Given a Jensen-concave function `Vhat : ProbDist Ω → ℝ` with bounded steepness `L` at `μ₀`, there
exists a continuous linear majorant `H : ProbDist Ω → ℝ` that is `L`-KR-Lipschitz, tight at `μ₀`,
dominates `Vhat`, and preserves Bayes-plausible mixtures.

Bounded steepness alone suffices — global Lipschitz continuity of `Vhat` is not required. -/
theorem exists_kr_lipschitz_majorant
    {Vhat : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L) (μ₀ : ProbDist Ω)
    (hVhat_jensen : ∀ {μ_pr : ProbDist Ω} {τ : ProbDist (ProbDist Ω)},
      IsBayesPlausible μ_pr τ → ∫ μ, Vhat μ ∂τ.toMeasure ≤ Vhat μ_pr)
    (hVhat_usc : UpperSemicontinuous Vhat)
    (hsteep : HasBoundedSteepness Vhat μ₀ L) :
    ∃ (p : Ω → ℝ) (_ : ∃ K : NNReal, LipschitzWith K p) (H : ProbDist Ω → ℝ),
      (∀ μ : ProbDist Ω, H μ = ProbDist.expect μ p) ∧
      (∀ μ ν : ProbDist Ω, H μ - H ν ≤ L * krDist μ ν) ∧
      (∀ {τ : ProbDist (ProbDist Ω)}, IsBayesPlausible μ₀ τ →
        H μ₀ = ∫ μ, H μ ∂τ.toMeasure) ∧
      H μ₀ = Vhat μ₀ ∧
      (∀ μ : ProbDist Ω, Vhat μ ≤ H μ) := by
  classical
  set liftedVhat : KRSignedMeasure Ω → ℝ :=
    Function.extend KRSignedMeasure.ofProbDist Vhat (fun _ => 0) with hlift_def
  have hlift_eq : ∀ μ : ProbDist Ω, liftedVhat (KRSignedMeasure.ofProbDist μ) = Vhat μ := by
    intro μ
    exact (Function.Injective.extend_apply KRSignedMeasure.injective_ofProbDist Vhat _ μ)
  set K : Set (KRSignedMeasure Ω) := Set.range (KRSignedMeasure.ofProbDist (Ω := Ω)) with hK_def
  have hK_conv : Convex ℝ K := KRSignedMeasure.convex_range_ofProbDist
  have hK_closed : IsClosed K := KRSignedMeasure.isClosed_range_ofProbDist
  have hμ₀_mem : KRSignedMeasure.ofProbDist μ₀ ∈ K := ⟨μ₀, rfl⟩
  have hlift_conc : ConcaveOn ℝ K liftedVhat := by
    refine ⟨hK_conv, ?_⟩
    rintro _ ⟨μ₁, rfl⟩ _ ⟨μ₂, rfl⟩ a b ha hb hab
    set aN : NNReal := a.toNNReal with haN_def
    set bN : NNReal := b.toNNReal with hbN_def
    have haN_coe : (aN : ℝ) = a := Real.coe_toNNReal a ha
    have hbN_coe : (bN : ℝ) = b := Real.coe_toNNReal b hb
    have hsumNN : aN + bN = 1 := by
      apply NNReal.eq
      rw [NNReal.coe_add, haN_coe, hbN_coe, NNReal.coe_one, hab]
    set mbar : MeasureTheory.Measure Ω :=
      aN • (μ₁ : MeasureTheory.Measure Ω) + bN • (μ₂ : MeasureTheory.Measure Ω) with hmbar_def
    have hmbar_prob : MeasureTheory.IsProbabilityMeasure mbar := by
      refine ⟨?_⟩
      rw [hmbar_def, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ,
        MeasureTheory.measure_univ]
      change (aN : ENNReal) • (1 : ENNReal) + (bN : ENNReal) • (1 : ENNReal) = 1
      rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add, hsumNN, ENNReal.coe_one]
    set mubar : ProbDist Ω := ⟨mbar, hmbar_prob⟩ with hmubar_def
    -- The embedding `ofProbDist` is affine: the convex combination in `KRSignedMeasure` agrees
    -- with the one constructed in `ProbDist`.
    have hmubar_eq :
        KRSignedMeasure.ofProbDist mubar = a • KRSignedMeasure.ofProbDist μ₁
            + b • KRSignedMeasure.ofProbDist μ₂ := by
      apply KRSignedMeasure.ext
      change mbar.toSignedMeasure = a • (μ₁ : MeasureTheory.Measure Ω).toSignedMeasure
          + b • (μ₂ : MeasureTheory.Measure Ω).toSignedMeasure
      have hmsm : mbar.toSignedMeasure
          = (aN • (μ₁ : MeasureTheory.Measure Ω)).toSignedMeasure
            + (bN • (μ₂ : MeasureTheory.Measure Ω)).toSignedMeasure :=
        MeasureTheory.Measure.toSignedMeasure_add _ _
      rw [hmsm, MeasureTheory.Measure.toSignedMeasure_smul _ aN,
        MeasureTheory.Measure.toSignedMeasure_smul _ bN]
      rw [show (aN • (μ₁ : MeasureTheory.Measure Ω).toSignedMeasure
              : MeasureTheory.SignedMeasure Ω)
            = (aN : ℝ) • (μ₁ : MeasureTheory.Measure Ω).toSignedMeasure from
          NNReal.smul_def aN _,
        show (bN • (μ₂ : MeasureTheory.Measure Ω).toSignedMeasure
              : MeasureTheory.SignedMeasure Ω)
            = (bN : ℝ) • (μ₂ : MeasureTheory.Measure Ω).toSignedMeasure from
          NNReal.smul_def bN _,
        haN_coe, hbN_coe]
    set mdbar : MeasureTheory.Measure (ProbDist Ω) :=
      aN • MeasureTheory.Measure.dirac μ₁ + bN • MeasureTheory.Measure.dirac μ₂ with hmdbar_def
    have hmdbar_prob : MeasureTheory.IsProbabilityMeasure mdbar := by
      refine ⟨?_⟩
      rw [hmdbar_def, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ,
        MeasureTheory.measure_univ]
      change (aN : ENNReal) • (1 : ENNReal) + (bN : ENNReal) • (1 : ENNReal) = 1
      rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add, hsumNN, ENNReal.coe_one]
    set τ : ProbDist (ProbDist Ω) := ⟨mdbar, hmdbar_prob⟩ with hτ_def
    have hτ_BP : IsBayesPlausible mubar τ := by
      intro f
      change ∫ ν, ProbDist.expect ν f ∂(τ : MeasureTheory.Measure (ProbDist Ω))
        = ProbDist.expect mubar f
      have hcont : Continuous (fun ν : ProbDist Ω => ProbDist.expect ν f) :=
        MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f
      have hSM : MeasureTheory.StronglyMeasurable (fun ν : ProbDist Ω => ProbDist.expect ν f) :=
        hcont.stronglyMeasurable
      have hint_d1 : MeasureTheory.Integrable (fun ν : ProbDist Ω => ProbDist.expect ν f)
          (MeasureTheory.Measure.dirac μ₁) := MeasureTheory.integrable_dirac' hSM (by simp)
      have hint_d2 : MeasureTheory.Integrable (fun ν : ProbDist Ω => ProbDist.expect ν f)
          (MeasureTheory.Measure.dirac μ₂) := MeasureTheory.integrable_dirac' hSM (by simp)
      change ∫ ν, ProbDist.expect ν f ∂mdbar = _
      change ∫ ν, ProbDist.expect ν f ∂(aN • MeasureTheory.Measure.dirac μ₁
            + bN • MeasureTheory.Measure.dirac μ₂) = _
      rw [MeasureTheory.integral_add_measure
        hint_d1.smul_measure_nnreal hint_d2.smul_measure_nnreal]
      rw [MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_dirac' _ μ₁ hSM,
        MeasureTheory.integral_dirac' _ μ₂ hSM]
      change (aN : ℝ) • ProbDist.expect μ₁ f + (bN : ℝ) • ProbDist.expect μ₂ f
        = ProbDist.expect mubar f
      change _ = ∫ ω, f ω ∂(mubar : MeasureTheory.Measure Ω)
      change _ = ∫ ω, f ω ∂mbar
      change (aN : ℝ) • ProbDist.expect μ₁ f + (bN : ℝ) • ProbDist.expect μ₂ f
        = ∫ ω, f ω ∂(aN • (μ₁ : MeasureTheory.Measure Ω)
              + bN • (μ₂ : MeasureTheory.Measure Ω))
      have hf_int_μ₁ : MeasureTheory.Integrable (⇑f) ((μ₁ : MeasureTheory.Measure Ω)) :=
        BoundedContinuousFunction.integrable _ f
      have hf_int_μ₂ : MeasureTheory.Integrable (⇑f) ((μ₂ : MeasureTheory.Measure Ω)) :=
        BoundedContinuousFunction.integrable _ f
      rw [MeasureTheory.integral_add_measure
        hf_int_μ₁.smul_measure_nnreal hf_int_μ₂.smul_measure_nnreal]
      rw [MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_smul_nnreal_measure]
      rfl
    have hVhat_meas : Measurable Vhat := hVhat_usc.measurable
    have hVhat_int : ∫ ν, Vhat ν ∂(τ : MeasureTheory.Measure (ProbDist Ω))
        = a * Vhat μ₁ + b * Vhat μ₂ := by
      change ∫ ν, Vhat ν ∂mdbar = _
      change ∫ ν, Vhat ν ∂(aN • MeasureTheory.Measure.dirac μ₁
              + bN • MeasureTheory.Measure.dirac μ₂)
            = _
      have hVhat_SM : MeasureTheory.StronglyMeasurable Vhat := hVhat_meas.stronglyMeasurable
      have hint_dirac : ∀ ν : ProbDist Ω,
          MeasureTheory.Integrable Vhat (MeasureTheory.Measure.dirac ν) := fun ν =>
        MeasureTheory.integrable_dirac' hVhat_SM (by simp)
      rw [MeasureTheory.integral_add_measure
          (hint_dirac μ₁).smul_measure_nnreal (hint_dirac μ₂).smul_measure_nnreal]
      rw [MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_dirac' _ μ₁ hVhat_SM,
        MeasureTheory.integral_dirac' _ μ₂ hVhat_SM]
      change (aN : ℝ) • Vhat μ₁ + (bN : ℝ) • Vhat μ₂ = _
      rw [haN_coe, hbN_coe]
      simp [smul_eq_mul]
    have hJensen := hVhat_jensen hτ_BP
    rw [hVhat_int] at hJensen
    rw [← hmubar_eq, hlift_eq mubar, hlift_eq μ₁, hlift_eq μ₂]
    exact hJensen
  have hlift_steep : ∀ x ∈ K, liftedVhat x - liftedVhat (KRSignedMeasure.ofProbDist μ₀)
      ≤ L * ‖x - KRSignedMeasure.ofProbDist μ₀‖ := by
    rintro _ ⟨μ, rfl⟩
    rw [hlift_eq μ, hlift_eq μ₀, KRSignedMeasure.norm_ofProbDist_sub]
    rcases eq_or_ne μ μ₀ with hμ | hne
    · subst hμ; simp [krDist_self]
    · have hsteep_μ := hsteep μ hne
      have hzero : krDist μ μ₀ ≠ 0 := fun h => hne (krDist_eq_zero_iff.mp h)
      have hpos : 0 < krDist μ μ₀ :=
        lt_of_le_of_ne (krDist_nonneg μ μ₀) (Ne.symm hzero)
      exact (div_le_iff₀ hpos).mp hsteep_μ
  obtain ⟨Hₐ, hHₐ_norm, hHₐ_supgrad⟩ :=
    ConcaveOn.exists_supergradient_of_boundedSteepness
      hK_conv hlift_conc hμ₀_mem hL hlift_steep
  obtain ⟨q, hq_lip, hq0, hq_repr⟩ := KRSignedMeasure.hanin_representation Hₐ
  have hq_lip_L : LipschitzWith ⟨L, hL⟩ q := hq_lip.weaken hHₐ_norm
  set boff : ℝ := Vhat μ₀ - ProbDist.expect μ₀ q with hboff_def
  set qBCF : Ω →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨q, hq_lip_L.continuous⟩ with hqBCF_def
  have hSI : ∀ μ : ProbDist Ω,
      KRSignedMeasure.signedIntegral q (KRSignedMeasure.ofProbDist μ) = ProbDist.expect μ q :=
    fun μ => KRSignedMeasure.signedIntegral_ofProbDist q μ
  have hq_kr : ∀ μ ν : ProbDist Ω,
      ProbDist.expect μ q - ProbDist.expect ν q ≤ L * krDist μ ν := by
    intro μ ν
    rcases (show 0 ≤ L from hL).lt_or_eq with hLpos | hLzero
    · have hLpos' : (0 : ℝ) < L := hLpos
      set r : Ω → ℝ := fun ω => q ω / L with hr_def
      have hr_lip : LipschitzWith 1 r := by
        rw [hr_def]
        exact KRSignedMeasure.lipschitzWith_one_div_lipConst hq_lip_L
          (by simpa [NNReal.coe_mk] using hLpos')
      have hr_bound :
          ProbDist.expect μ r - ProbDist.expect ν r ≤ krDist μ ν := by
        refine le_csSup (bddAbove_krDist_setOf μ ν) ?_
        exact ⟨r, hr_lip, rfl⟩
      have hexpect_scale :
          ∀ (η : ProbDist Ω), ProbDist.expect η r = ProbDist.expect η q / L := by
        intro η
        have hq_int : MeasureTheory.Integrable q (η : MeasureTheory.Measure Ω) :=
          qBCF.integrable _
        change ∫ ω, q ω / L ∂(η : MeasureTheory.Measure Ω)
            = (∫ ω, q ω ∂(η : MeasureTheory.Measure Ω)) / L
        rw [show (fun ω => q ω / L) = fun ω => L⁻¹ * q ω by funext ω; rw [div_eq_inv_mul],
          MeasureTheory.integral_const_mul]
        ring
      rw [hexpect_scale μ, hexpect_scale ν] at hr_bound
      have hsub : ProbDist.expect μ q / L - ProbDist.expect ν q / L
          = (ProbDist.expect μ q - ProbDist.expect ν q) / L := by ring
      rw [hsub] at hr_bound
      rw [div_le_iff₀ hLpos'] at hr_bound
      linarith
    · subst hLzero
      have hq_const : ∀ a b : Ω, q a = q b := by
        intro a b
        have h0 : dist (q a) (q b) ≤ 0 := by
          have hdist : dist (q a) (q b) ≤ ((⟨0, hL⟩ : NNReal) : ℝ) * dist a b :=
            hq_lip_L.dist_le_mul a b
          simpa using hdist
        have : dist (q a) (q b) = 0 := le_antisymm h0 dist_nonneg
        rw [Real.dist_eq] at this
        linarith [abs_eq_zero.mp this]
      have hq_eq_const : ∀ η : ProbDist Ω, ProbDist.expect η q = q (default : Ω) := by
        intro η
        change ∫ ω, q ω ∂(η : MeasureTheory.Measure Ω) = q default
        have hfun : (fun ω => q ω) = (fun _ => q (default : Ω)) := by
          funext ω; exact hq_const ω default
        rw [hfun]
        simp [MeasureTheory.measureReal_def]
      rw [hq_eq_const μ, hq_eq_const ν]
      simp
  set p : Ω → ℝ := fun ω => q ω + boff with hp_def
  have hp_lip_L : LipschitzWith ⟨L, hL⟩ p := by
    rw [hp_def]
    simpa [sub_neg_eq_add] using KRSignedMeasure.lipschitzWith_sub_const hq_lip_L (-boff)
  have hp_lip : ∃ K : NNReal, LipschitzWith K p := ⟨⟨L, hL⟩, hp_lip_L⟩
  have hH_eq_form : ∀ μ : ProbDist Ω,
      ProbDist.expect μ p = ProbDist.expect μ q + boff := by
    intro μ
    change ∫ ω, q ω + boff ∂(μ : MeasureTheory.Measure Ω)
        = ∫ ω, q ω ∂(μ : MeasureTheory.Measure Ω) + boff
    have hq_int : MeasureTheory.Integrable q (μ : MeasureTheory.Measure Ω) :=
      qBCF.integrable _
    rw [MeasureTheory.integral_add hq_int (MeasureTheory.integrable_const _)]
    simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def]
  refine ⟨p, hp_lip, fun μ => ProbDist.expect μ p, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro μ ν
    change ProbDist.expect μ p - ProbDist.expect ν p ≤ L * krDist μ ν
    rw [hH_eq_form μ, hH_eq_form ν]
    linarith [hq_kr μ ν]
  · intro τ hτ
    have hp_cont : Continuous p := (hq_lip_L.continuous).add continuous_const
    set pBCF : Ω →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨p, hp_cont⟩ with hpBCF_def
    have hp_coe : ∀ μ : ProbDist Ω, ProbDist.expect μ p = ProbDist.expect μ pBCF := by
      intro μ; rfl
    change ProbDist.expect μ₀ p
        = ∫ μ, (fun μ => ProbDist.expect μ p) μ ∂(τ : MeasureTheory.Measure (ProbDist Ω))
    simp_rw [hp_coe]
    exact (hτ pBCF).symm
  · change ProbDist.expect μ₀ p = Vhat μ₀
    rw [hH_eq_form μ₀]
    simp [hboff_def]
  · intro μ
    change Vhat μ ≤ ProbDist.expect μ p
    rw [hH_eq_form μ]
    have hsuper := hHₐ_supgrad (KRSignedMeasure.ofProbDist μ) ⟨μ, rfl⟩
    rw [hlift_eq μ, hlift_eq μ₀] at hsuper
    have hH_diff := hq_repr (KRSignedMeasure.ofProbDist μ - KRSignedMeasure.ofProbDist μ₀)
    -- The difference `ofProbDist μ - ofProbDist μ₀` has total signed mass 0, so the constant
    -- term in the Hanin representation cancels.
    have h_univ :
        (((KRSignedMeasure.ofProbDist μ - KRSignedMeasure.ofProbDist μ₀).toSignedMeasure
            Set.univ : ℝ)) = 0 := by
      change ((KRSignedMeasure.ofProbDist μ).toSignedMeasure Set.univ
          - (KRSignedMeasure.ofProbDist μ₀).toSignedMeasure Set.univ : ℝ) = 0
      rw [KRSignedMeasure.toSignedMeasure_ofProbDist_univ μ,
        KRSignedMeasure.toSignedMeasure_ofProbDist_univ μ₀, sub_self]
    have h_diff_si : KRSignedMeasure.signedIntegral q
        (KRSignedMeasure.ofProbDist μ - KRSignedMeasure.ofProbDist μ₀)
        = ProbDist.expect μ q
          - ProbDist.expect μ₀ q := by
      rw [KRSignedMeasure.signedIntegral_sub_lipschitz hq_lip_L]
      rw [KRSignedMeasure.signedIntegral_ofProbDist q μ,
        KRSignedMeasure.signedIntegral_ofProbDist q μ₀]
    rw [h_univ, mul_zero, zero_add, h_diff_si] at hH_diff
    rw [hH_diff] at hsuper
    change Vhat μ ≤ ProbDist.expect μ q + boff
    rw [hboff_def]
    linarith [hsuper]

/-! ### Main theorem -/

/-- **Hard direction: Bounded steepness ⟹ superdifferentiable.**

Bounded steepness of the concave closure at `μ₀` implies superdifferentiability: There exists a
Lipschitz supporting price `p` such that `concaveClosure V μ₀ = ∫ p dμ₀` and
`concaveClosure V μ ≤ ∫ p dμ` for all `μ`. -/
theorem concaveClosure_isSuperdifferentiable_of_hasBoundedSteepness
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω)
    (hsteep : HasBoundedSteepness (concaveClosure V) μ₀ L) :
    IsSuperdifferentiable (concaveClosure V) μ₀ := by
  have hjensen : ∀ {μ_pr : ProbDist Ω} {τ : ProbDist (ProbDist Ω)},
      IsBayesPlausible μ_pr τ →
      ∫ μ, concaveClosure V μ ∂τ.toMeasure ≤ concaveClosure V μ_pr :=
    fun hτ => concaveClosure_jensen V hV_bdd hV_usc hτ
  have hVhat_usc : UpperSemicontinuous (concaveClosure V) :=
    upperSemicontinuous_concaveClosure V hV_bdd hV_usc
  obtain ⟨p, hp_lip, _H, _hH_def, _hH_lip, _hH_aff, hH_eq, hH_maj⟩ :=
    exists_kr_lipschitz_majorant hL μ₀ hjensen hVhat_usc hsteep
  refine ⟨p, hp_lip, ?_, ?_⟩
  · rw [← _hH_def μ₀, hH_eq]
  · intro μ
    rw [← _hH_def μ]
    exact hH_maj μ

end Supergradient

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
