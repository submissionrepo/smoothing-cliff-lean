/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Basic
public import Econlib.Optimization.OptimalTransport.KantorovichRubinstein

/-!
# Composition of Lipschitz value and moment map is `L√N`-KR-Lipschitz

If `v : X → ℝ` is `L`-Lipschitz on a compact convex `X ⊆ ℝⁿ` and each coordinate `m_j : Ω → ℝ` of
the moment map is `1`-Lipschitz on `Ω`, then the composed value `V(μ) := v(∫ ω, m(ω) dμ(ω))` is
`L√N`-Lipschitz under the Kantorovich–Rubinstein metric on `ProbDist Ω`.

## Main definitions

* `MomentSetup.IsCoordLipschitz` — each scalar moment `m_j` is `1`-Lipschitz.

## Main statements

* `composedValue_isKRLipschitz_of_lipschitz` — the composed sender value is `L√N`-KR-Lipschitz on
  `ProbDist Ω`.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Lemma 1.

## Tags

persuasion, moment persuasion, Lipschitz, Kantorovich-Rubinstein
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.Optimization.OptimalTransport
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [SecondCountableTopology Ω]

/-! ## Coordinate Lipschitz hypothesis -/

variable {n : ℕ}

/-- Each moment coordinate is `1`-Lipschitz. -/
def MomentSetup.IsCoordLipschitz (s : MomentSetup Ω n) : Prop :=
  ∀ i : Fin n, LipschitzWith 1 (fun ω => s.m ω i)

/-! ## Coordinate-wise Lipschitz bound on moment expectations -/

lemma MomentSetup.coord_expect_sub_le_krDist
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    (μ ν : ProbDist Ω) (i : Fin n) :
    ProbDist.expect μ (fun ω => s.m ω i) - ProbDist.expect ν (fun ω => s.m ω i)
      ≤ krDist μ ν := by
  refine le_csSup (Econlib.Optimization.OptimalTransport.bddAbove_krDist_setOf μ ν) ?_
  refine ⟨fun ω => s.m ω i, hm_lip i, ?_⟩
  rfl

/-! ## Composed value is `L√N`-KR-Lipschitz -/

omit [SecondCountableTopology Ω] in
/-- Each moment coordinate `m_i` is integrable under any probability law on `Ω`. -/
lemma MomentSetup.coord_integrable
    (s : MomentSetup Ω n) (μ : ProbDist Ω) (i : Fin n) :
    MeasureTheory.Integrable (fun ω => (s.m ω).ofLp i) μ.toMeasure := by
  have h_cont : Continuous (fun ω => (s.m ω).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp s.m_continuous)
  exact h_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [SecondCountableTopology Ω] in
/-- The vector-valued moment map `m` is integrable under any probability law on `Ω`. -/
lemma MomentSetup.m_integrable
    (s : MomentSetup Ω n) (μ : ProbDist Ω) :
    MeasureTheory.Integrable s.m μ.toMeasure := by
  have h_supp : HasCompactSupport s.m := HasCompactSupport.of_compactSpace _
  exact s.m_continuous.integrable_of_hasCompactSupport h_supp

omit [SecondCountableTopology Ω] in
/-- Coordinate of the posterior moment equals the scalar expectation of the corresponding moment
coordinate. -/
lemma MomentSetup.posteriorMoment_ofLp
    (s : MomentSetup Ω n) (μ : ProbDist Ω) (i : Fin n) :
    (s.posteriorMoment μ).ofLp i = ProbDist.expect μ (fun ω => (s.m ω).ofLp i) := by
  unfold MomentSetup.posteriorMoment ProbDist.expect
  have h_int : MeasureTheory.Integrable s.m μ.toMeasure := s.m_integrable μ
  have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm h_int
  simp only [EuclideanSpace.coe_proj] at this
  exact this.symm

/-- Each coordinate of the posterior moment vector satisfies
`|(s.posteriorMoment μ).ofLp i - (s.posteriorMoment ν).ofLp i| ≤ krDist μ ν`. -/
lemma MomentSetup.abs_posteriorMoment_coord_sub_le
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    (μ ν : ProbDist Ω) (i : Fin n) :
    |(s.posteriorMoment μ).ofLp i - (s.posteriorMoment ν).ofLp i|
      ≤ krDist μ ν := by
  rw [s.posteriorMoment_ofLp μ i, s.posteriorMoment_ofLp ν i]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := s.coord_expect_sub_le_krDist hm_lip ν μ i
    rw [Econlib.Optimization.OptimalTransport.krDist_comm] at h
    linarith
  · exact s.coord_expect_sub_le_krDist hm_lip μ ν i

/-- The posterior-moment map is `√n`-Lipschitz under the KR distance. -/
lemma MomentSetup.dist_posteriorMoment_le
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    (μ ν : ProbDist Ω) :
    dist (s.posteriorMoment μ) (s.posteriorMoment ν)
      ≤ Real.sqrt n * krDist μ ν := by
  set d : ℝ := krDist μ ν with hd_def
  have hd_nn : 0 ≤ d := Econlib.Optimization.OptimalTransport.krDist_nonneg μ ν
  set pμ : Fin n → ℝ := (s.posteriorMoment μ).ofLp with hpμ
  set pν : Fin n → ℝ := (s.posteriorMoment ν).ofLp with hpν
  -- Each squared coordinate gap is at most `d²`, so `dist² = ∑ ≤ n·d²`.
  have h_dist_sq_le : dist (s.posteriorMoment μ) (s.posteriorMoment ν) ^ 2 ≤ (n : ℝ) * d ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have h_each : ∀ i : Fin n, dist (pμ i) (pν i) ^ 2 ≤ d ^ 2 := fun i => by
      rw [Real.dist_eq, hpμ, hpν, hd_def]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (s.abs_posteriorMoment_coord_sub_le hm_lip μ ν i) 2
    calc ∑ i : Fin n, dist (pμ i) (pν i) ^ 2
        ≤ ∑ _i : Fin n, d ^ 2 := Finset.sum_le_sum (fun i _ => h_each i)
      _ = (n : ℝ) * d ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `dist ≤ √(n·d²) = √n · d` since `d ≥ 0`.
  rw [← Real.sqrt_sq hd_nn (x := d), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le h_dist_sq_le

theorem composedValue_isKRLipschitz_of_lipschitz
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x)) :
    IsKRLipschitz (s.composedValue v) (L * Real.sqrt n) := by
  intro μ ν
  set aμ := s.posteriorMoment μ
  set aν := s.posteriorMoment ν
  have h_lip := hv.dist_le_mul aμ aν
  rw [Real.dist_eq] at h_lip
  have h_v_sub : v aμ - v aν ≤ (L : ℝ) * dist aμ aν := (abs_le.mp h_lip).2
  have h_dist :=
    s.dist_posteriorMoment_le hm_lip μ ν
  have hL_nn : (0 : ℝ) ≤ L := L.coe_nonneg
  calc v aμ - v aν
      ≤ (L : ℝ) * dist aμ aν := h_v_sub
    _ ≤ (L : ℝ) * (Real.sqrt n * krDist μ ν) :=
        mul_le_mul_of_nonneg_left h_dist hL_nn
    _ = (L : ℝ) * Real.sqrt n * krDist μ ν := by ring

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
