/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Semicontinuous
public import Econlib.Optimization.OptimalTransport.Duality
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Upper Lipschitz envelopes on `ProbabilityMeasure`

The **upper `L`-Lipschitz envelope** of a functional `V : ProbabilityMeasure Ω → ℝ` is the
Moreau-type upper envelope obtained by sup-convolving `V` with the Kantorovich–Rubinstein distance:

`V_L μ = sup_ν (V ν - L * krDist μ ν)`.

This is the largest `L`-KR-Lipschitz majorant of `V`: Penalizing each value `V ν` by the cost
`L * krDist μ ν` and taking the supremum over `ν` produces a functional that is upper
semicontinuous and `L`-Lipschitz with respect to `krDist`, while dominating `V`. As the penalty `L`
grows, the envelope decreases pointwise back down to `V` at any law where `V` is upper
semicontinuous.

## Main definitions

* `upperLipschitzEnvelope` — the upper `L`-Lipschitz envelope of `V`.

## Main statements

* `le_upperLipschitzEnvelope` — the envelope dominates `V`.
* `upperLipschitzEnvelope_anti_mono` — the envelope decreases in the penalty parameter.
* `upperLipschitzEnvelope_isKRLipschitz` — the envelope is `L`-Lipschitz in KR distance.
* `upperLipschitzEnvelope_usc` — the envelope is upper semicontinuous.
* `upperLipschitzEnvelope_tendsto` — the envelopes converge pointwise to a bounded USC objective.
* `krDist_eq_zero_iff` — KR distance separates probability laws on a compact metrizable Hausdorff
  state space.

## Notes

The basic facts are stated with the bounded-above hypothesis needed to take `sSup` over `ℝ`, rather
than building global boundedness or compactness into the definition.

## Tags

upper lipschitz envelope, moreau envelope, kantorovich-rubinstein, upper semicontinuous,
probability measure
-/

@[expose] public section

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist
open scoped Topology

namespace Econlib.Optimization.OptimalTransport

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [T2Space Ω] [CompactSpace Ω]

/-- The upper `L`-Lipschitz envelope of an objective on probability laws. -/
noncomputable def upperLipschitzEnvelope (V : ProbabilityMeasure Ω → ℝ) (L : ℝ)
    (μ : ProbabilityMeasure Ω) : ℝ :=
  sSup {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L * krDist μ ν}

omit [BorelSpace Ω] [SecondCountableTopology Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [T2Space Ω] [CompactSpace Ω] in
/-- The value set defining the envelope is nonempty, witnessed by `ν = μ`. -/
lemma upperLipschitzEnvelope_values_nonempty
    (V : ProbabilityMeasure Ω → ℝ) (L : ℝ) (μ : ProbabilityMeasure Ω) :
    {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L * krDist μ ν}.Nonempty :=
  ⟨V μ - L * krDist μ μ, μ, rfl⟩

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- For a nonnegative penalty and a bounded-above objective, the envelope value set is bounded
above. -/
lemma upperLipschitzEnvelope_values_bddAbove
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) (hL_nonneg : 0 ≤ L)
    (μ : ProbabilityMeasure Ω) :
    BddAbove {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L * krDist μ ν} := by
  obtain ⟨C, hC⟩ := hV_bddAbove
  refine ⟨C, ?_⟩
  rintro y ⟨ν, rfl⟩
  have hV_le : V ν ≤ C := hC ⟨ν, rfl⟩
  have hpenalty_nonneg : 0 ≤ L * krDist μ ν :=
    mul_nonneg hL_nonneg (krDist_nonneg μ ν)
  linarith

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] [CompactSpace Ω] in
/-- A uniform bound on `|V|` makes the range of `V` bounded above. -/
lemma bddAbove_range_of_abs_le {V : ProbabilityMeasure Ω → ℝ}
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M) :
    BddAbove (Set.range V) := by
  obtain ⟨M, hM⟩ := hV_bdd
  refine ⟨M, ?_⟩
  rintro y ⟨μ, rfl⟩
  exact (abs_le.mp (hM μ)).2

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- The envelope lies above the original objective at the same law. -/
lemma le_upperLipschitzEnvelope
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ} (hV_bddAbove : BddAbove (Set.range V))
    (hL_nonneg : 0 ≤ L) (μ : ProbabilityMeasure Ω) :
    V μ ≤ upperLipschitzEnvelope V L μ := by
  unfold upperLipschitzEnvelope
  have hbd := upperLipschitzEnvelope_values_bddAbove
    (Ω := Ω) hV_bddAbove hL_nonneg μ
  have hmem :
      V μ ∈ {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L * krDist μ ν} := by
    refine ⟨μ, ?_⟩
    rw [krDist_self]
    ring
  exact le_csSup hbd hmem

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- Bounded-objective version of `le_upperLipschitzEnvelope`. -/
lemma le_upperLipschitzEnvelope_of_bdd
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ}
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M)
    (hL_nonneg : 0 ≤ L) (μ : ProbabilityMeasure Ω) :
    V μ ≤ upperLipschitzEnvelope V L μ :=
  le_upperLipschitzEnvelope (bddAbove_range_of_abs_le hV_bdd) hL_nonneg μ

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- Increasing the penalty parameter lowers the upper Lipschitz envelope. -/
lemma upperLipschitzEnvelope_anti_mono
    {V : ProbabilityMeasure Ω → ℝ} {L₁ L₂ : ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) (hL₁_nonneg : 0 ≤ L₁)
    (hL_le : L₁ ≤ L₂) (μ : ProbabilityMeasure Ω) :
    upperLipschitzEnvelope V L₂ μ ≤ upperLipschitzEnvelope V L₁ μ := by
  unfold upperLipschitzEnvelope
  have hne := upperLipschitzEnvelope_values_nonempty V L₂ μ
  refine csSup_le hne ?_
  rintro y ⟨ν, rfl⟩
  have hL₂_nonneg : 0 ≤ L₂ := hL₁_nonneg.trans hL_le
  have hbd := upperLipschitzEnvelope_values_bddAbove
    (Ω := Ω) hV_bddAbove hL₁_nonneg μ
  have hdist_nonneg : 0 ≤ krDist μ ν := krDist_nonneg μ ν
  have hpenalty_le : L₁ * krDist μ ν ≤ L₂ * krDist μ ν :=
    mul_le_mul_of_nonneg_right hL_le hdist_nonneg
  have hcandidate :
      V ν - L₁ * krDist μ ν
        ≤ sSup {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L₁ * krDist μ ν} :=
    le_csSup hbd ⟨ν, rfl⟩
  linarith

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- The upper envelope is `L`-Lipschitz in KR distance. -/
theorem upperLipschitzEnvelope_isKRLipschitz
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) (hL_nonneg : 0 ≤ L) :
    IsKRLipschitz (upperLipschitzEnvelope V L) L := by
  intro μ η
  unfold upperLipschitzEnvelope
  have hne := upperLipschitzEnvelope_values_nonempty V L μ
  rw [sub_le_iff_le_add]
  refine csSup_le hne ?_
  rintro y ⟨ν, rfl⟩
  have hbd_η := upperLipschitzEnvelope_values_bddAbove
    (Ω := Ω) hV_bddAbove hL_nonneg η
  have hcandidate_η :
      V ν - L * krDist η ν
        ≤ sSup {y : ℝ | ∃ ν : ProbabilityMeasure Ω, y = V ν - L * krDist η ν} :=
    le_csSup hbd_η ⟨ν, rfl⟩
  have htriangle : krDist η ν ≤ krDist μ ν + krDist μ η := by
    have h := krDist_triangle η ν μ
    rw [krDist_comm η μ] at h
    linarith
  have hdist_linear : L * krDist η ν ≤ L * krDist μ ν + L * krDist μ η := by
    calc
      L * krDist η ν ≤ L * (krDist μ ν + krDist μ η) :=
        mul_le_mul_of_nonneg_left htriangle hL_nonneg
      _ = L * krDist μ ν + L * krDist μ η := by ring
  linarith

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- Bounded-objective version of `upperLipschitzEnvelope_isKRLipschitz`. -/
theorem upperLipschitzEnvelope_isKRLipschitz_of_bdd
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ}
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M) (hL_nonneg : 0 ≤ L) :
    IsKRLipschitz (upperLipschitzEnvelope V L) L :=
  upperLipschitzEnvelope_isKRLipschitz
    (bddAbove_range_of_abs_le hV_bdd) hL_nonneg

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- Boundedness of the upper Lipschitz envelope under a global KR-diameter bound. -/
theorem upperLipschitzEnvelope_bdd
    {V : ProbabilityMeasure Ω → ℝ} {L M D : ℝ}
    (hL_nonneg : 0 ≤ L) (hD_nonneg : 0 ≤ D)
    (hV_bdd : ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M)
    (hkr_le_D : ∀ μ ν : ProbabilityMeasure Ω, krDist μ ν ≤ D)
    (μ : ProbabilityMeasure Ω) :
    |upperLipschitzEnvelope V L μ| ≤ M + L * D := by
  rw [abs_le]
  constructor
  · have hLD_nonneg : 0 ≤ L * D := mul_nonneg hL_nonneg hD_nonneg
    have hV_lower : -M ≤ V μ := (abs_le.mp (hV_bdd μ)).1
    have hV_le_env : V μ ≤ upperLipschitzEnvelope V L μ := by
      refine le_upperLipschitzEnvelope ?_ hL_nonneg μ
      refine ⟨M, ?_⟩
      rintro y ⟨ν, rfl⟩
      exact (abs_le.mp (hV_bdd ν)).2
    linarith
  · unfold upperLipschitzEnvelope
    have hne := upperLipschitzEnvelope_values_nonempty V L μ
    refine csSup_le hne ?_
    rintro y ⟨ν, rfl⟩
    have hV_upper : V ν ≤ M := (abs_le.mp (hV_bdd ν)).2
    have hpenalty_nonneg : 0 ≤ L * krDist μ ν :=
      mul_nonneg hL_nonneg (krDist_nonneg μ ν)
    have hpenalty_le : L * krDist μ ν ≤ L * D :=
      mul_le_mul_of_nonneg_left (hkr_le_D μ ν) hL_nonneg
    linarith

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] in
/-- The KR distance is lower semicontinuous as a function of the pair of probability laws. -/
lemma krDist_lowerSemicontinuous :
    LowerSemicontinuous
      (fun q : ProbabilityMeasure Ω × ProbabilityMeasure Ω => krDist q.1 q.2) := by
  let Lip1 : Type _ := {p : Ω → ℝ // LipschitzWith 1 p}
  haveI : Nonempty Lip1 :=
    ⟨⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp)⟩⟩
  have hcomp_cont : ∀ p : Lip1, Continuous
      (fun q : ProbabilityMeasure Ω × ProbabilityMeasure Ω =>
        expect q.1 (p : Ω → ℝ) - expect q.2 (p : Ω → ℝ)) := by
    intro p
    have hp_cont : Continuous (p : Ω → ℝ) := p.2.continuous
    let pBCF : BoundedContinuousFunction Ω ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨_, hp_cont⟩
    have hexpect_cont : Continuous
        (fun μ : ProbabilityMeasure Ω => expect μ (p : Ω → ℝ)) := by
      simpa [expect] using
        MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
          (X := Ω) pBCF
    exact (hexpect_cont.comp continuous_fst).sub (hexpect_cont.comp continuous_snd)
  have hbddAbove : ∀ q : ProbabilityMeasure Ω × ProbabilityMeasure Ω,
      BddAbove (Set.range fun p : Lip1 =>
        expect q.1 (p : Ω → ℝ) - expect q.2 (p : Ω → ℝ)) := by
    intro q
    refine ⟨krTransportCost q.1 q.2, ?_⟩
    rintro y ⟨p, rfl⟩
    exact lipschitz_expect_sub_le_krTransportCost q.1 q.2 p.2
  have hkr_iSup : ∀ q : ProbabilityMeasure Ω × ProbabilityMeasure Ω,
      (⨆ p : Lip1, expect q.1 (p : Ω → ℝ) -
          expect q.2 (p : Ω → ℝ)) = krDist q.1 q.2 := by
    intro q
    unfold krDist
    apply le_antisymm
    · refine ciSup_le ?_
      intro p
      refine le_csSup (bddAbove_krDist_setOf q.1 q.2) ?_
      exact ⟨p.1, p.2, rfl⟩
    · refine csSup_le ?_ ?_
      · refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
        simp [expect]
      rintro x ⟨p, hp_lip, rfl⟩
      exact le_ciSup_of_le (hbddAbove q) ⟨p, hp_lip⟩ le_rfl
  have h := lowerSemicontinuous_ciSup
    (f := fun (p : Lip1) (q : ProbabilityMeasure Ω × ProbabilityMeasure Ω) =>
      expect q.1 (p : Ω → ℝ) - expect q.2 (p : Ω → ℝ))
    hbddAbove
    (fun p => (hcomp_cont p).lowerSemicontinuous)
  simpa only [hkr_iSup] using h

/-- KR distance separates probability laws on a compact metrizable Hausdorff state space. -/
lemma krDist_eq_zero_iff {μ ν : ProbabilityMeasure Ω} :
    krDist μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hzero
    obtain ⟨π, hπ, hπ_opt⟩ := exists_optimal_kr_coupling μ ν
    let dBC : BoundedContinuousFunction (Ω × Ω) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩
    have hd_int : Integrable (fun z : Ω × Ω => dist z.1 z.2) π.toMeasure :=
      dBC.integrable π.toMeasure
    have hd_integral_zero :
        ∫ z, dist z.1 z.2 ∂π.toMeasure = 0 := by
      rw [← hπ_opt]
      exact hzero
    have hdist_ae_zero :
        (fun z : Ω × Ω => dist z.1 z.2) =ᵐ[π.toMeasure] 0 := by
      exact (integral_eq_zero_iff_of_nonneg (fun z => dist_nonneg) hd_int).mp
        hd_integral_zero
    letI : MetricSpace Ω := MetricSpace.ofT0PseudoMetricSpace Ω
    have hfst_snd_ae : Prod.fst =ᵐ[π.toMeasure] (Prod.snd : Ω × Ω → Ω) := by
      filter_upwards [hdist_ae_zero] with z hz
      exact eq_of_dist_eq_zero hz
    apply ProbabilityMeasure.toMeasure_injective
    calc (μ : Measure Ω)
        = ((map π Prod.fst measurable_fst : ProbabilityMeasure Ω) : Measure Ω) := by
            rw [hπ.fst_marginal]
      _ = Measure.map Prod.fst π.toMeasure := by
            rw [map_toMeasure]
      _ = Measure.map Prod.snd π.toMeasure := Measure.map_congr hfst_snd_ae
      _ = ((map π Prod.snd measurable_snd : ProbabilityMeasure Ω) : Measure Ω) := by
            rw [map_toMeasure]
      _ = (ν : Measure Ω) := by
            rw [hπ.snd_marginal]
  · rintro rfl
    exact krDist_self μ

/-- KR distance between distinct probability laws is strictly positive. -/
lemma krDist_pos_of_ne {μ ν : ProbabilityMeasure Ω} (hμν : μ ≠ ν) :
    0 < krDist μ ν := by
  exact lt_of_le_of_ne (krDist_nonneg μ ν) (by
    intro hzero
    exact hμν (krDist_eq_zero_iff.mp hzero.symm))

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- Upper semicontinuity of the upper Lipschitz envelope. -/
theorem upperLipschitzEnvelope_usc
    {V : ProbabilityMeasure Ω → ℝ} {L : ℝ}
    -- kept for symmetry with the boundedness hypotheses of the surrounding envelope API,
    -- even though this proof's compact-space sSup argument doesn't need it
    (_hV_bddAbove : BddAbove (Set.range V)) (hL_nonneg : 0 ≤ L)
    (hV_usc : UpperSemicontinuous V) :
    UpperSemicontinuous (upperLipschitzEnvelope V L) := by
  have hV_prod_usc :
      UpperSemicontinuous (fun q : ProbabilityMeasure Ω × ProbabilityMeasure Ω => V q.2) :=
    hV_usc.comp continuous_snd
  have hscale_cont : Continuous (fun x : ℝ => -L * x) :=
    continuous_const_mul (-L)
  have hscale_antitone : Antitone (fun x : ℝ => -L * x) := by
    intro x y hxy
    exact mul_le_mul_of_nonpos_left hxy (by linarith)
  have hpenalty_usc :
      UpperSemicontinuous
        (fun q : ProbabilityMeasure Ω × ProbabilityMeasure Ω => -L * krDist q.1 q.2) := by
    simpa [Function.comp] using
      (hscale_cont.comp_lowerSemicontinuous_antitone
        krDist_lowerSemicontinuous hscale_antitone)
  have hF : UpperSemicontinuous
      (fun q : ProbabilityMeasure Ω × ProbabilityMeasure Ω => V q.2 - L * krDist q.1 q.2) := by
    simpa [sub_eq_add_neg, neg_mul] using hV_prod_usc.add hpenalty_usc
  by_cases hne : Nonempty (ProbabilityMeasure Ω)
  · letI := hne
    have hsup := upperSemicontinuous_sSup_compact
      (α := ProbabilityMeasure Ω) (β := ProbabilityMeasure Ω) hF
    simpa [upperLipschitzEnvelope] using hsup
  · rw [upperSemicontinuous_iff_isClosed_preimage]
    intro c
    have hpre :
        upperLipschitzEnvelope V L ⁻¹' Set.Ici c =
          (∅ : Set (ProbabilityMeasure Ω)) := by
      ext μ
      constructor
      · intro _
        exact False.elim (hne ⟨μ⟩)
      · intro hμ
        simp at hμ
    rw [hpre]
    exact isClosed_empty

/-- As the penalty grows, the upper Lipschitz envelopes converge pointwise back down to the bounded
upper-semicontinuous objective. -/
theorem upperLipschitzEnvelope_tendsto
    {V : ProbabilityMeasure Ω → ℝ}
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ : ProbabilityMeasure Ω) :
    Filter.Tendsto (fun L : ℕ => upperLipschitzEnvelope V (L : ℝ) μ)
      Filter.atTop (𝓝 (V μ)) := by
  obtain ⟨M, hM⟩ := hV_bdd
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha
      (le_upperLipschitzEnvelope_of_bdd ⟨M, hM⟩ (Nat.cast_nonneg n) μ)
  · intro a ha
    set η : ℝ := (a - V μ) / 2 with hη_def
    have hη_pos : 0 < η := by
      rw [hη_def]
      linarith
    have hμ_add_η_lt : V μ + η < a := by
      rw [hη_def]
      linarith
    let A : Set (ProbabilityMeasure Ω) := {ν | V μ + η ≤ V ν}
    have hA_closed : IsClosed A := by
      exact hV_usc.isClosed_preimage (V μ + η)
    by_cases hA_nonempty : A.Nonempty
    · have hA_compact : IsCompact A := hA_closed.isCompact
      have hkr_lsc : LowerSemicontinuous (fun ν : ProbabilityMeasure Ω => krDist μ ν) := by
        simpa [Function.comp] using
          (krDist_lowerSemicontinuous.comp (Continuous.prodMk_right μ))
      obtain ⟨ν₀, hν₀A, hν₀_min⟩ :=
        (hkr_lsc.lowerSemicontinuousOn A).exists_isMinOn hA_nonempty hA_compact
      set δ : ℝ := krDist μ ν₀ with hδ_def
      have hδ_pos : 0 < δ := by
        rw [hδ_def]
        refine krDist_pos_of_ne ?_
        intro hμν₀
        have hbad : V μ + η ≤ V μ := by
          subst ν₀
          exact hν₀A
        linarith
      obtain ⟨N, hN⟩ := exists_nat_gt ((M - a) / δ)
      have hN_bound : M - (N : ℝ) * δ < a := by
        have hmul := mul_lt_mul_of_pos_right hN hδ_pos
        have hdiv_mul : (M - a) / δ * δ = M - a := by
          field_simp [ne_of_gt hδ_pos]
        linarith
      rw [Filter.eventually_atTop]
      refine ⟨N, ?_⟩
      intro n hn
      have hn_bound : M - (n : ℝ) * δ < a := by
        have hn_real : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
        have hmul_le : (N : ℝ) * δ ≤ (n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right hn_real (le_of_lt hδ_pos)
        linarith
      unfold upperLipschitzEnvelope
      have hne := upperLipschitzEnvelope_values_nonempty V (n : ℝ) μ
      refine lt_of_le_of_lt
        (b := max (V μ + η) (M - (n : ℝ) * δ)) (csSup_le hne ?_) ?_
      · rintro y ⟨ν, rfl⟩
        by_cases hνA : ν ∈ A
        · have hδ_le : δ ≤ krDist μ ν := by
            simpa [hδ_def] using hν₀_min hνA
          have hpenalty_le :
              (n : ℝ) * δ ≤ (n : ℝ) * krDist μ ν :=
            mul_le_mul_of_nonneg_left hδ_le (Nat.cast_nonneg n)
          have hV_upper : V ν ≤ M := (abs_le.mp (hM ν)).2
          exact le_max_of_le_right (by linarith)
        · have hV_lt : V ν < V μ + η := lt_of_not_ge hνA
          have hpenalty_nonneg : 0 ≤ (n : ℝ) * krDist μ ν :=
            mul_nonneg (Nat.cast_nonneg n) (krDist_nonneg μ ν)
          exact le_max_of_le_left (by linarith)
      · exact max_lt hμ_add_η_lt hn_bound
    · rw [Filter.eventually_atTop]
      refine ⟨0, ?_⟩
      intro n hn
      unfold upperLipschitzEnvelope
      have hne := upperLipschitzEnvelope_values_nonempty V (n : ℝ) μ
      refine lt_of_le_of_lt (csSup_le hne ?_) hμ_add_η_lt
      rintro y ⟨ν, rfl⟩
      have hν_notA : ν ∉ A := fun hνA => hA_nonempty ⟨ν, hνA⟩
      have hV_lt : V ν < V μ + η := lt_of_not_ge hν_notA
      have hpenalty_nonneg : 0 ≤ (n : ℝ) * krDist μ ν :=
        mul_nonneg (Nat.cast_nonneg n) (krDist_nonneg μ ν)
      linarith

end Econlib.Optimization.OptimalTransport
