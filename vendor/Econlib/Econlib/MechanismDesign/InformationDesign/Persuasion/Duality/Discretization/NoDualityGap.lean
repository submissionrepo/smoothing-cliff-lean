/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.DualApproximation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.WeakDuality
public import Econlib.Probability.ProbDist.Borel

/-!
# No duality gap

For a compact metric state space `Ω` and a bounded upper-semicontinuous objective `V`, the
persuasion duality has no gap: `concaveClosure V μ₀ = dualValue V μ₀`. Combined with primal
attainment this yields the strong-duality theorem.

## Main statements

* `noDualityGap_isKRLipschitz` — no gap for bounded upper-semicontinuous objectives that are
  KR-Lipschitz with a fixed constant `L`.
* `noDualityGap` — for bounded upper-semicontinuous `V`, `concaveClosure V μ₀ = dualValue V μ₀`.
* `noDualityGap_and_primalAttainment` — the gap is closed and the primal supremum defining
  `concaveClosure V μ₀` is attained.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 2.

## Tags

persuasion, duality, no duality gap, primal attainment
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal ProbabilityMeasure
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

section NoDualityGap

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

variable {n : ℕ}

/-- No duality gap for bounded USC objectives that are KR-Lipschitz. -/
theorem noDualityGap_isKRLipschitz
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    {V : ProbDist Ω → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (hV_lip : Econlib.Optimization.OptimalTransport.IsKRLipschitz V L)
    (μ₀ : ProbDist Ω) :
    concaveClosure V μ₀ =
      dualValue V μ₀ := by
  apply le_antisymm
  · have hP_nonempty : (feasiblePrimal μ₀).Nonempty := by
      obtain ⟨τ, hτ, _hτ_val⟩ := primalAttainment hV_bdd hV_usc μ₀
      exact ⟨τ, hτ⟩
    have hD_nonempty : (feasibleDual V).Nonempty := by
      obtain ⟨M, hM⟩ := hV_bdd
      refine ⟨fun _ : Ω => M, ?_⟩
      constructor
      · exact ⟨0, (LipschitzWith.const M).weaken (by simp)⟩
      · intro μ
        have hVM : V μ ≤ M := (abs_le.mp (hM μ)).2
        simpa [ProbDist.expect] using hVM
    have hV_int : ∀ τ ∈ feasiblePrimal μ₀,
        Integrable V τ.toMeasure := by
      intro τ _hτ
      obtain ⟨M, hM⟩ := hV_bdd
      exact MeasureTheory.Integrable.of_bound hV_usc.measurable.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
    have hg_int : ∀ τ ∈ feasiblePrimal μ₀,
        ∀ p ∈ feasibleDual V,
          Integrable (fun μ : ProbDist Ω => ProbDist.expect μ p) τ.toMeasure := by
      intro τ _hτ p hp
      let pBCF : BoundedContinuousFunction Ω ℝ :=
        lipschitzToBounded hp.lipschitz
      have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ p) := by
        simpa [ProbDist.expect] using
          (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
            (X := Ω) pBCF)
      let gBCF : BoundedContinuousFunction (ProbDist Ω) ℝ :=
        BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩
      exact gBCF.integrable τ.toMeasure
    exact weakDuality hP_nonempty hD_nonempty hV_int hg_int
  · refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨p, hp, hp_le⟩ :=
      exists_dual_feasible_value_le_concaveClosure_add
        hL_nonneg hV_bdd hV_usc hV_lip μ₀ ε hε
    unfold dualValue
    have hbd : BddBelow {y : ℝ | ∃ p ∈ feasibleDual V,
        y = dualObjective μ₀ p} := by
      refine ⟨V μ₀, ?_⟩
      rintro y ⟨p, hp, rfl⟩
      exact hp.majorizes μ₀
    have hmem : dualObjective μ₀ p ∈
        {y : ℝ | ∃ p ∈ feasibleDual V,
          y = dualObjective μ₀ p} :=
      ⟨p, hp, rfl⟩
    exact le_trans (csInf_le hbd hmem) hp_le
omit [T2Space Ω] in
/-- The upper Lipschitz envelope of a bounded function `V` satisfies the same bound `M`, because
the penalty `L · krDist` is nonneg. -/
private lemma upperLipschitzEnvelope_abs_le_of_bdd
    {V : ProbDist Ω → ℝ} {L M : ℝ} (hL_nonneg : 0 ≤ L)
    (hM : ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (μ : ProbDist Ω) :
    |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V L μ| ≤ M := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hV_lower : -M ≤ V μ := (abs_le.mp (hM μ)).1
    have hV_le_env : V μ ≤
        Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V L μ :=
      Econlib.Optimization.OptimalTransport.le_upperLipschitzEnvelope_of_bdd
        ⟨M, hM⟩ hL_nonneg μ
    linarith
  · unfold Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
    have hne :=
      Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_values_nonempty
        V L μ
    refine csSup_le hne ?_
    rintro y ⟨ν, rfl⟩
    have hVν : V ν ≤ M := (abs_le.mp (hM ν)).2
    have hpenalty_nn : 0 ≤ L * Econlib.Optimization.OptimalTransport.krDist μ ν :=
      mul_nonneg hL_nonneg (Econlib.Optimization.OptimalTransport.krDist_nonneg μ ν)
    linarith

/-- For each natural `L`, the concave closure of the upper Lipschitz envelope of `V` with penalty
parameter `L` equals its dual value. -/
private lemma concaveClosure_upperLipschitzEnvelope_eq
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω) (L : ℕ) :
    concaveClosure
        (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) μ₀
      = dualValue
        (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ))
        μ₀ := by
  obtain ⟨M, hM⟩ := hV_bdd
  have hVL_bdd : ∃ M' : ℝ, ∀ μ : ProbDist Ω,
      |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ) μ|
        ≤ M' :=
    ⟨M, upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L) hM⟩
  have hVL_usc : UpperSemicontinuous
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) :=
    Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_usc
      (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M, hM⟩)
      (Nat.cast_nonneg L) hV_usc
  have hVL_lip : Econlib.Optimization.OptimalTransport.IsKRLipschitz
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ))
      (L : ℝ) :=
    Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_isKRLipschitz_of_bdd
      ⟨M, hM⟩ (Nat.cast_nonneg L)
  exact noDualityGap_isKRLipschitz
    (Nat.cast_nonneg L) hVL_bdd hVL_usc hVL_lip μ₀

/-- Monotonicity in `V`: If `V ≤ V'` pointwise (and both bounded measurable), then
`concaveClosure V μ₀ ≤ concaveClosure V' μ₀`. -/
private lemma concaveClosure_mono_of_bdd
    {V V' : ProbDist Ω → ℝ}
    (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M) (hV_meas : Measurable V)
    (hV'_bdd : ∃ M, ∀ μ, |V' μ| ≤ M) (hV'_meas : Measurable V')
    (hle : ∀ μ, V μ ≤ V' μ) (μ₀ : ProbDist Ω) :
    concaveClosure V μ₀ ≤ concaveClosure V' μ₀ := by
  obtain ⟨M', hM'⟩ := hV'_bdd
  obtain ⟨M, hM⟩ := hV_bdd
  unfold concaveClosure
  refine csSup_le ?_ ?_
  · refine ⟨primalValue V (MeasureTheory.diracProba μ₀),
      MeasureTheory.diracProba μ₀, ?_, rfl⟩
    intro f
    have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
      simpa [ProbDist.expect] using
        (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) f)
    change ∫ μ, ProbDist.expect μ f
        ∂(MeasureTheory.diracProba μ₀ : ProbDist (ProbDist Ω)).toMeasure
        = ProbDist.expect μ₀ f
    have hdirac_eq : (MeasureTheory.diracProba μ₀ :
        ProbDist (ProbDist Ω)).toMeasure = MeasureTheory.Measure.dirac μ₀ := by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]
    rw [hdirac_eq]
    exact MeasureTheory.integral_dirac' _ _ hcont.stronglyMeasurable
  · rintro y ⟨τ, hτ, rfl⟩
    have hbd' : BddAbove {y : ℝ | ∃ τ' ∈ feasiblePrimal μ₀, y = primalValue V' τ'} := by
      refine ⟨M', ?_⟩
      rintro y ⟨τ', _, rfl⟩
      unfold primalValue
      have hV'_int : Integrable V' τ'.toMeasure :=
        MeasureTheory.Integrable.of_bound hV'_meas.aestronglyMeasurable M'
          (Filter.Eventually.of_forall fun μ => by simpa using hM' μ)
      calc ∫ μ, V' μ ∂τ'.toMeasure
          ≤ ∫ _, M' ∂τ'.toMeasure :=
            integral_mono hV'_int (integrable_const _)
              (fun μ => (abs_le.mp (hM' μ)).2)
        _ = M' := by simp
    have hmem' : primalValue V' τ ∈
        {y : ℝ | ∃ τ' ∈ feasiblePrimal μ₀, y = primalValue V' τ'} :=
      ⟨τ, hτ, rfl⟩
    have h_pv_le : primalValue V τ ≤ primalValue V' τ := by
      unfold primalValue
      have hV_int : Integrable V τ.toMeasure :=
        MeasureTheory.Integrable.of_bound hV_meas.aestronglyMeasurable M
          (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
      have hV'_int : Integrable V' τ.toMeasure :=
        MeasureTheory.Integrable.of_bound hV'_meas.aestronglyMeasurable M'
          (Filter.Eventually.of_forall fun μ => by simpa using hM' μ)
      exact integral_mono_ae hV_int hV'_int (Filter.Eventually.of_forall hle)
    exact h_pv_le.trans (le_csSup hbd' hmem')

/-- The sequence `L ↦ concaveClosure V_L μ₀` is antitone in `L : ℕ`, where `V_L` denotes the upper
Lipschitz envelope of `V` with penalty parameter `L`. -/
private lemma concaveClosure_upperLipschitzEnvelope_antitone
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω) :
    Antitone (fun L : ℕ => concaveClosure
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) μ₀) := by
  intro L₁ L₂ hL
  obtain ⟨M, hM⟩ := hV_bdd
  have hVL₁_bdd : ∃ M', ∀ μ : ProbDist Ω,
      |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₁ : ℝ) μ| ≤ M' :=
    ⟨M, upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L₁) hM⟩
  have hVL₂_bdd : ∃ M', ∀ μ : ProbDist Ω,
      |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₂ : ℝ) μ| ≤ M' :=
    ⟨M, upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L₂) hM⟩
  have hVL₁_usc : UpperSemicontinuous
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₁ : ℝ)) :=
    Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_usc
      (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M, hM⟩)
      (Nat.cast_nonneg L₁) hV_usc
  have hVL₂_usc : UpperSemicontinuous
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₂ : ℝ)) :=
    Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_usc
      (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M, hM⟩)
      (Nat.cast_nonneg L₂) hV_usc
  have hle : ∀ μ,
      Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₂ : ℝ) μ ≤
        Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L₁ : ℝ) μ :=
    fun μ =>
      Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_anti_mono
        (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M, hM⟩)
        (Nat.cast_nonneg L₁) (Nat.cast_le.mpr hL) μ
  exact concaveClosure_mono_of_bdd hVL₂_bdd hVL₂_usc.measurable hVL₁_bdd
    hVL₁_usc.measurable hle μ₀

/-- The sequence `L ↦ concaveClosure V_L μ₀` is bounded below by `concaveClosure V μ₀`, since
`V ≤ V_L` pointwise. -/
private lemma concaveClosure_upperLipschitzEnvelope_lower_bound
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω) (L : ℕ) :
    concaveClosure V μ₀ ≤ concaveClosure
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) μ₀ := by
  obtain ⟨M, hM⟩ := hV_bdd
  have hVL_bdd : ∃ M', ∀ μ : ProbDist Ω,
      |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ) μ| ≤ M' :=
    ⟨M, upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L) hM⟩
  have hVL_usc : UpperSemicontinuous
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) :=
    Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_usc
      (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M, hM⟩)
      (Nat.cast_nonneg L) hV_usc
  exact concaveClosure_mono_of_bdd ⟨M, hM⟩ hV_usc.measurable hVL_bdd
    hVL_usc.measurable
    (fun μ =>
      Econlib.Optimization.OptimalTransport.le_upperLipschitzEnvelope_of_bdd
        ⟨M, hM⟩ (Nat.cast_nonneg L) μ) μ₀

/-- **No duality gap.**

For a compact metric state space `Ω` and a bounded upper-semicontinuous objective `V`, the concave
closure equals the dual value: `concaveClosure V μ₀ = dualValue V μ₀`. -/
theorem noDualityGap
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (μ₀ : ProbDist Ω) :
    concaveClosure V μ₀ = dualValue V μ₀ := by
  refine le_antisymm ?_ ?_
  · have hP_nonempty : (feasiblePrimal μ₀).Nonempty := by
      obtain ⟨τ, hτ, _hτ_val⟩ := primalAttainment hV_bdd hV_usc μ₀
      exact ⟨τ, hτ⟩
    have hD_nonempty : (feasibleDual V).Nonempty := by
      obtain ⟨M, hM⟩ := hV_bdd
      refine ⟨fun _ : Ω => M, ?_⟩
      refine ⟨⟨0, (LipschitzWith.const M).weaken (by simp)⟩, ?_⟩
      intro μ
      have hVM : V μ ≤ M := (abs_le.mp (hM μ)).2
      simpa [ProbDist.expect] using hVM
    have hV_int : ∀ τ ∈ feasiblePrimal μ₀, Integrable V τ.toMeasure := by
      intro τ _hτ
      obtain ⟨M, hM⟩ := hV_bdd
      exact MeasureTheory.Integrable.of_bound hV_usc.measurable.aestronglyMeasurable M
        (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
    have hg_int : ∀ τ ∈ feasiblePrimal μ₀, ∀ p ∈ feasibleDual V,
        Integrable (fun μ : ProbDist Ω => ProbDist.expect μ p) τ.toMeasure := by
      intro τ _hτ p hp
      let pBCF : Ω →ᵇ ℝ := lipschitzToBounded hp.lipschitz
      have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ p) := by
        simpa [ProbDist.expect] using
          (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
            (X := Ω) pBCF)
      let gBCF : ProbDist Ω →ᵇ ℝ :=
        BoundedContinuousFunction.mkOfCompact ⟨_, hcont⟩
      exact gBCF.integrable τ.toMeasure
    exact weakDuality hP_nonempty hD_nonempty hV_int hg_int
  · set f : ℕ → ℝ := fun L => concaveClosure
      (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) μ₀
      with hf_def
    have hf_anti : Antitone f :=
      concaveClosure_upperLipschitzEnvelope_antitone hV_bdd hV_usc μ₀
    have hf_lb : ∀ L : ℕ, concaveClosure V μ₀ ≤ f L := fun L =>
      concaveClosure_upperLipschitzEnvelope_lower_bound hV_bdd hV_usc μ₀ L
    have hf_bddBelow : BddBelow (Set.range f) := by
      refine ⟨concaveClosure V μ₀, ?_⟩
      rintro y ⟨L, rfl⟩; exact hf_lb L
    have hf_tendsto : Filter.Tendsto f Filter.atTop (𝓝 (⨅ L, f L)) :=
      tendsto_atTop_ciInf hf_anti hf_bddBelow
    have hbound : ∀ L : ℕ, dualValue V μ₀ ≤ f L := by
      intro L
      have hEq : f L = dualValue
          (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) μ₀ :=
        concaveClosure_upperLipschitzEnvelope_eq hV_bdd hV_usc μ₀ L
      rw [hEq]
      unfold dualValue
      refine le_csInf ?_ ?_
      · obtain ⟨M, hM⟩ := hV_bdd
        have hVL_bdd : ∀ μ : ProbDist Ω,
            |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ) μ|
              ≤ M :=
          upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L) hM
        refine ⟨dualObjective μ₀ (fun _ : Ω => M),
          ⟨fun _ : Ω => M, ?_, rfl⟩⟩
        refine ⟨⟨0, (LipschitzWith.const M).weaken (by simp)⟩, ?_⟩
        intro μ
        have hVL_le : Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
            V (L : ℝ) μ ≤ M := (abs_le.mp (hVL_bdd μ)).2
        simpa [ProbDist.expect] using hVL_le
      · rintro y ⟨p, hp_VL, rfl⟩
        obtain ⟨M, hM⟩ := hV_bdd
        have hp_V : IsDualFeasible V p := by
          refine ⟨hp_VL.lipschitz, ?_⟩
          intro μ
          have h1 : V μ ≤ Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
              V (L : ℝ) μ :=
            Econlib.Optimization.OptimalTransport.le_upperLipschitzEnvelope_of_bdd
              ⟨M, hM⟩ (Nat.cast_nonneg L) μ
          exact h1.trans (hp_VL.majorizes μ)
        refine csInf_le ?_ ⟨p, hp_V, rfl⟩
        refine ⟨V μ₀, ?_⟩
        rintro z ⟨q, hq, rfl⟩
        exact hq.majorizes μ₀
    have hle₁ : dualValue V μ₀ ≤ ⨅ L, f L :=
      ge_of_tendsto' hf_tendsto hbound
    obtain ⟨M_V, hM_V⟩ := hV_bdd
    have hVL_bdd : ∀ L : ℕ, ∃ M', ∀ μ : ProbDist Ω,
        |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ) μ| ≤ M' :=
      fun L => ⟨M_V, upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg L) hM_V⟩
    have hVL_usc : ∀ L : ℕ, UpperSemicontinuous
        (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (L : ℝ)) :=
      fun L => Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_usc
        (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M_V, hM_V⟩)
        (Nat.cast_nonneg L) hV_usc
    choose τ hτ_mem hτ_attain using
      fun L : ℕ => primalAttainment (hVL_bdd L) (hVL_usc L) μ₀
    -- `ProbDist (ProbDist Ω)` is a metric space (Lévy–Prokhorov), hence first-countable,
    -- which is needed to extract a convergent subsequence from the compact set.
    haveI : TopologicalSpace.PseudoMetrizableSpace (ProbDist Ω) :=
      (TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace
        (X := ProbDist Ω))
    haveI : TopologicalSpace.MetrizableSpace (ProbDist (ProbDist Ω)) :=
      MeasureTheory.instMetrizableSpaceProbabilityMeasure (ProbDist Ω)
    haveI : TopologicalSpace.PseudoMetrizableSpace (ProbDist (ProbDist Ω)) :=
      TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace
    haveI : FirstCountableTopology (ProbDist (ProbDist Ω)) :=
      TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology
    obtain ⟨τStar, hτStar_mem, φ, hφ_mono, hτ_subseq⟩ :=
      (feasiblePrimal_isCompact (μ₀ := μ₀)).tendsto_subseq hτ_mem
    have hUSC_int : ∀ M : ℕ, UpperSemicontinuous
        (fun τ : ProbDist (ProbDist Ω) =>
          ∫ μ, Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
            V (M : ℝ) μ ∂(τ : Measure (ProbDist Ω))) := by
      intro M
      have hVM_bdd_on : ∃ B : ℝ, ∀ μ ∈ (Set.univ : Set (ProbDist Ω)),
          |Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (M : ℝ) μ|
            ≤ B := by
        refine ⟨M_V, fun μ _ => ?_⟩
        exact upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg M) hM_V μ
      have hUSC_on_univ :
          UpperSemicontinuousOn
            (fun τ : ProbDist (ProbDist Ω) =>
              ∫ μ, Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
                V (M : ℝ) μ ∂(τ : Measure (ProbDist Ω)))
            {τ : ProbDist (ProbDist Ω) | (τ : Measure (ProbDist Ω)) Set.univ = 1} :=
        upperSemicontinuousOn_integral_of_bounded_upperSemicontinuousOn_compactSupport
          (X := ProbDist Ω) isCompact_univ hVM_bdd_on
          ((hVL_usc M).upperSemicontinuousOn _)
      have hSet_univ :
          {τ : ProbDist (ProbDist Ω) | (τ : Measure (ProbDist Ω)) Set.univ = 1}
            = Set.univ := by
        ext τ
        simp [MeasureTheory.measure_univ]
      rw [hSet_univ] at hUSC_on_univ
      exact upperSemicontinuousOn_univ_iff.mp hUSC_on_univ
    have hVM_int : ∀ M : ℕ, ∀ τ : ProbDist (ProbDist Ω),
        Integrable
          (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (M : ℝ))
          τ.toMeasure := by
      intro M τ
      exact MeasureTheory.Integrable.of_bound (hVL_usc M).measurable.aestronglyMeasurable M_V
        (Filter.Eventually.of_forall fun μ => by
          simpa using upperLipschitzEnvelope_abs_le_of_bdd (Nat.cast_nonneg M) hM_V μ)
    set g : ℕ → ProbDist (ProbDist Ω) → ℝ := fun M τ =>
      ∫ μ, Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
        V (M : ℝ) μ ∂(τ : Measure (ProbDist Ω)) with hg_def
    have hf_subseq : Filter.Tendsto (f ∘ φ) Filter.atTop (𝓝 (⨅ L, f L)) :=
      hf_tendsto.comp hφ_mono.tendsto_atTop
    have hLimitVsM : ∀ M : ℕ, (⨅ L, f L) ≤ g M τStar := by
      intro M
      have hφ_ge : ∀ᶠ k in Filter.atTop, M ≤ φ k :=
        Filter.tendsto_atTop.mp hφ_mono.tendsto_atTop M
      have hbound_ev : ∀ᶠ k in Filter.atTop,
          (f ∘ φ) k ≤ g M (τ (φ k)) := by
        filter_upwards [hφ_ge] with k hkM
        have heq_f : (f ∘ φ) k = primalValue
            (Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
              V ((φ k) : ℝ)) (τ (φ k)) := by
          rw [hf_def]
          exact (hτ_attain (φ k)).symm
        rw [heq_f]
        unfold primalValue
        change ∫ μ, Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope
              V ((φ k) : ℝ) μ ∂(τ (φ k)).toMeasure ≤ g M (τ (φ k))
        rw [hg_def]
        refine integral_mono_ae (hVM_int (φ k) (τ (φ k)))
          (hVM_int M (τ (φ k))) ?_
        refine Filter.Eventually.of_forall fun μ => ?_
        exact Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_anti_mono
          (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M_V, hM_V⟩)
          (Nat.cast_nonneg M) (Nat.cast_le.mpr hkM) μ
      have hg_subseq_tendsto :
          Filter.Tendsto (fun k => τ (φ k)) Filter.atTop (𝓝 τStar) := hτ_subseq
      have hg_USC_at : UpperSemicontinuousAt (g M) τStar := (hUSC_int M).upperSemicontinuousAt _
      by_contra hcontra
      push Not at hcontra
      set fInf : ℝ := ⨅ L, f L with hfInf_def
      set y : ℝ := (fInf + g M τStar) / 2 with hy_def
      have hy_lt_inf : g M τStar < y := by
        rw [hy_def]; linarith
      have hy_lt : y < fInf := by
        rw [hy_def]; linarith
      have h_ev_g_lt : ∀ᶠ k in Filter.atTop, g M (τ (φ k)) < y := by
        have h_ev_nhds : ∀ᶠ τ' in 𝓝 τStar, g M τ' < y :=
          (upperSemicontinuousAt_iff.mp hg_USC_at) y hy_lt_inf
        exact hg_subseq_tendsto.eventually h_ev_nhds
      have h_ev_f_lt : ∀ᶠ k in Filter.atTop, (f ∘ φ) k < y := by
        filter_upwards [hbound_ev, h_ev_g_lt] with k hb hg
        exact lt_of_le_of_lt hb hg
      have hf_subseq' : Filter.Tendsto (f ∘ φ) Filter.atTop (𝓝 fInf) := hf_subseq
      have h_ev_f_ge : ∀ᶠ k in Filter.atTop, y ≤ (f ∘ φ) k := by
        have : ∀ᶠ k in Filter.atTop, (f ∘ φ) k ∈ Set.Ioi y := by
          exact hf_subseq' (isOpen_Ioi.mem_nhds hy_lt)
        filter_upwards [this] with k hk
        exact le_of_lt hk
      have hF : ∀ᶠ k in (Filter.atTop : Filter ℕ), False := by
        filter_upwards [h_ev_f_lt, h_ev_f_ge] with k h1 h2
        linarith
      exact (hF.exists).elim fun _ h => h
    have hV_int_at_τStar : Integrable V τStar.toMeasure :=
      MeasureTheory.Integrable.of_bound hV_usc.measurable.aestronglyMeasurable M_V
        (Filter.Eventually.of_forall fun μ => by simpa using hM_V μ)
    have hVM_anti_pointwise : ∀ μ : ProbDist Ω,
        Antitone (fun M : ℕ =>
          Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (M : ℝ) μ) := by
      intro μ M₁ M₂ hM
      exact Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_anti_mono
        (Econlib.Optimization.OptimalTransport.bddAbove_range_of_abs_le ⟨M_V, hM_V⟩)
        (Nat.cast_nonneg M₁) (Nat.cast_le.mpr hM) μ
    have hVM_tendsto_pointwise : ∀ μ : ProbDist Ω,
        Filter.Tendsto
          (fun M : ℕ =>
            Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope V (M : ℝ) μ)
          Filter.atTop (𝓝 (V μ)) := fun μ =>
      Econlib.Optimization.OptimalTransport.upperLipschitzEnvelope_tendsto
        ⟨M_V, hM_V⟩ hV_usc μ
    have hgM_tendsto_at_τStar :
        Filter.Tendsto (fun M : ℕ => g M τStar) Filter.atTop
          (𝓝 (∫ μ, V μ ∂τStar.toMeasure)) := by
      rw [hg_def]
      exact MeasureTheory.integral_tendsto_of_tendsto_of_antitone
        (fun M => hVM_int M τStar) hV_int_at_τStar
        (Filter.Eventually.of_forall hVM_anti_pointwise)
        (Filter.Eventually.of_forall hVM_tendsto_pointwise)
    have hle₂ : (⨅ L, f L) ≤ ∫ μ, V μ ∂τStar.toMeasure :=
      ge_of_tendsto' hgM_tendsto_at_τStar hLimitVsM
    have hPrimalLe : primalValue V τStar ≤ concaveClosure V μ₀ := by
      unfold concaveClosure
      have hbd : BddAbove {y : ℝ | ∃ τ ∈ feasiblePrimal μ₀,
          y = primalValue V τ} := by
        refine ⟨M_V, ?_⟩
        rintro y ⟨τ, _, rfl⟩
        unfold primalValue
        have hV_int : Integrable V τ.toMeasure :=
          MeasureTheory.Integrable.of_bound hV_usc.measurable.aestronglyMeasurable M_V
            (Filter.Eventually.of_forall fun μ => by simpa using hM_V μ)
        calc ∫ μ, V μ ∂τ.toMeasure
            ≤ ∫ _, M_V ∂τ.toMeasure :=
              integral_mono hV_int (integrable_const _)
                (fun μ => (abs_le.mp (hM_V μ)).2)
          _ = M_V := by simp
      exact le_csSup hbd ⟨τStar, hτStar_mem, rfl⟩
    have hle₃ : (⨅ L, f L) ≤ concaveClosure V μ₀ := hle₂.trans hPrimalLe
    exact hle₁.trans hle₃

/-- **No duality gap and primal attainment.**

For a compact metric state space `Ω` and a bounded upper-semicontinuous objective `V`, the concave
closure equals the dual value, and the supremum defining `concaveClosure V μ₀` is attained by some
Bayes-plausible `τ`. -/
theorem noDualityGap_and_primalAttainment
    {V : ProbDist Ω → ℝ} (hV_bdd : ∃ M, ∀ μ, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (μ₀ : ProbDist Ω) :
    concaveClosure V μ₀ = dualValue V μ₀ ∧
    ∃ τ ∈ feasiblePrimal μ₀, primalValue V τ = concaveClosure V μ₀ :=
  ⟨noDualityGap hV_bdd hV_usc μ₀, primalAttainment hV_bdd hV_usc μ₀⟩

end NoDualityGap

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
