/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.SubgradientSelection
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.KRStrongDuality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.CompositionLipschitz
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ConvexRoof
public import Econlib.Probability.ProbDist.Borel

/-!
# Prices for moments

Given a moment-persuasion problem with prior `μ₀` and an objective `v : X → ℝ` on a compact convex
`X ⊆ ℝⁿ`, the dual problem admits a **structured price**.  Specifically there exists

* a convex Lipschitz `p̄ : X → ℝ` with `p̄ ≥ v` on `X`;
* a measurable `q : X → ℝⁿ` with bounded norm (a measurable selection of subgradients of the convex
  roof);
* the envelope identity `p̄(y) = sup_{x ∈ X} { v(x) + q(x) · (y − x) }`, so `p̄` is the upper
  envelope of affine minorants whose slope is `q`,

and the lifted price `ω ↦ p̄(m(ω))` is dual-feasible for `V(μ) := v(E_μ[m])` with dual objective
equal to the dual value `dualValue V μ₀`.

The existence result `MomentSetup.exists_hasMomentPrices` assumes more than Lipschitzness of `v`:
Lipschitzness of the moment coordinates (`hm_lip`); measurability, boundedness, and upper
semicontinuity of `v`; measurability and upper semicontinuity of the composed value; membership of
every posterior moment in `X` (`h_post_mem`); and Lipschitzness of the posterior check (convex
roof) of every Lipschitz price on `X` (`h_pcheck_lip`). It does not assume the open-positive prior
or moment-image density that the differentiable-case results add. The `MomentSetup` surjectivity
field `moment_surjOn_X` — every point of `X` is achievable as a posterior moment — is in force
throughout.

## Main definitions

* `HasMomentPrices` — bundles the structured-price package above.

## Main statements

* `MomentSetup.exists_hasMomentPrices` — existence of `p̄` and `q` witnessing `HasMomentPrices`,
  together with dual feasibility of `ω ↦ p̄(m(ω))` and the dual-value identity.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 5.

## Tags

persuasion, moment persuasion, duality, structured price
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

variable {n : ℕ}

/-! ## Prices for moments: Structured-prices package -/

/-- The structured-prices conclusion bundle: A convex Lipschitz envelope `p̄ ≥ v`, a measurable
slope selector `q`, and the affine-minorant envelope identity. -/
structure HasMomentPrices (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal)
    (pbar : EuclideanSpace ℝ (Fin n) → ℝ)
    (q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop where
  /-- `p̄` is convex on `X`. -/
  pbar_convex : ConvexOn ℝ s.X pbar
  /-- `p̄` is Lipschitz with some finite constant. -/
  pbar_lipschitz : ∃ K : NNReal, LipschitzWith K pbar
  /-- `p̄ ≥ v` on `X`. -/
  pbar_ge_v : ∀ x ∈ s.X, v x ≤ pbar x
  /-- `q` is a measurable selection. -/
  q_measurable : Measurable q
  /-- `q` has a uniform norm bound. -/
  q_norm_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖q x‖ ≤ K
  /-- `p̄` realized as the affine-minorant envelope:
  `p̄(y) = sup_{x ∈ X} { v(x) + q(x) · (y − x) }`. -/
  pbar_envelope : ∀ y ∈ s.X,
    pbar y = sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
      v x + inner ℝ (q x) (y - x)) '' s.X)

/-- **Prices for moments.**

Given an `L`-Lipschitz objective `v` on `X ⊆ ℝⁿ` and a moment-persuasion problem with prior
`μ₀ = s.prior`, there exist `p̄ : X → ℝ` convex Lipschitz and `q : X → ℝⁿ` measurable such that
`p̄ ≥ v` on `X` and `(λω, p̄(m(ω)))` is dual-feasible for the lifted objective `V(μ) := v(E_μ[m])`
with dual value equal to `dualValue V μ₀`.

Beyond `L`-Lipschitzness of `v`, the hypotheses (all explicit below) are: Lipschitzness of the
moment coordinates (`hm_lip`); measurability, boundedness, and upper semicontinuity of `v`;
measurability and upper semicontinuity of the composed value; membership of every posterior moment
in `X` (`h_post_mem`); and Lipschitzness of the posterior check on `X` (`h_pcheck_lip`). The
`MomentSetup` surjectivity field `moment_surjOn_X` is in force as part of `s`. -/
theorem MomentSetup.exists_hasMomentPrices
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    -- kept for the docstring's spec (measurability of `v`); the proof only needs `hv_bdd`
    (_hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    -- kept for the docstring's spec (upper semicontinuity of `v`); superseded by `hV_usc`
    (_hv_usc : UpperSemicontinuous v)
    (hV_meas : Measurable (s.composedValue v))
    (hV_usc : UpperSemicontinuous (s.composedValue v))
    (h_post_mem : ∀ μ : ProbDist Ω, s.posteriorMoment μ ∈ s.X)
    (h_pcheck_lip : ∀ {p : Ω → ℝ} {K : NNReal},
      LipschitzWith K p →
        LipschitzOnWith K (convexRoof s p) s.X) :
    ∃ (pbar : EuclideanSpace ℝ (Fin n) → ℝ)
      (q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasMomentPrices s v L pbar q ∧
      IsDualFeasible (s.composedValue v) (fun ω => pbar (s.m ω)) ∧
      dualObjective s.prior (fun ω => pbar (s.m ω))
        = dualValue (s.composedValue v) s.prior := by
  set Ln : NNReal := L * Real.toNNReal (Real.sqrt n) with hLn_def
  have hsqrt_n_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hLn_eq : (Ln : ℝ) = (L : ℝ) * Real.sqrt n := by
    simp [hLn_def, Real.coe_toNNReal _ hsqrt_n_nn]
  have hLn_nn : (0 : ℝ) ≤ (L : ℝ) * Real.sqrt n := mul_nonneg hL_nn hsqrt_n_nn
  have hV_lip : Econlib.Optimization.OptimalTransport.IsKRLipschitz
      (s.composedValue v) ((L : ℝ) * Real.sqrt n) :=
    composedValue_isKRLipschitz_of_lipschitz s hm_lip hv
  have hV_bdd : ∃ M, ∀ μ, |s.composedValue v μ| ≤ M := by
    obtain ⟨M, hM⟩ := hv_bdd
    exact ⟨M, fun μ => hM _⟩
  obtain ⟨_, _, p_star, hp_star_feas, hp_star_eq⟩ :=
    strongDuality_of_isKRLipschitz hLn_nn hV_meas hV_bdd hV_usc hV_lip s.prior
  obtain ⟨Kp_star, hp_star_lip⟩ := hp_star_feas.lipschitz
  have hp_star_majorizes : ∀ μ : ProbDist Ω,
      s.composedValue v μ ≤ ProbDist.expect μ p_star := hp_star_feas.majorizes
  set p_check : EuclideanSpace ℝ (Fin n) → ℝ := convexRoof s p_star with hpc_def
  have hp_star_cont : Continuous p_star := hp_star_lip.continuous
  -- `p_star` is continuous on a compact space, hence integrable against any measure.
  have hp_star_int : ∀ ν : ProbDist Ω, MeasureTheory.Integrable p_star ν.toMeasure :=
    fun ν => hp_star_cont.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hpc_convex : ConvexOn ℝ s.X p_check :=
    convexRoof_convexOn s hp_star_lip
  have hpc_lip : LipschitzOnWith Kp_star p_check s.X := h_pcheck_lip hp_star_lip
  have hKp_star_nn : (0 : ℝ) ≤ (Kp_star : ℝ) := Kp_star.coe_nonneg
  have hpc_lip' : LipschitzOnWith ((Kp_star : ℝ)).toNNReal p_check s.X := by
    rw [Real.toNNReal_coe]; exact hpc_lip
  obtain ⟨q, hq_meas, hq_norm, hq_subg⟩ :=
    ConvexOn.exists_measurable_subgradient_selection
      (K := s.X) (f := p_check) (L := (Kp_star : ℝ)) hKp_star_nn
      s.X_compact s.X_convex s.X_interior hpc_convex hpc_lip'
  set pbar : EuclideanSpace ℝ (Fin n) → ℝ := upperEnvelope s v q with hpbar_def
  have hv_cont : Continuous v := hv.continuous
  have hq_subg_set : ∀ x ∈ s.X,
      q x ∈ SubderivWithinAt p_check s.X x := by
    intro x hx y hy
    exact hq_subg x hx y hy
  have h_v_le_pcheck : ∀ x ∈ s.X, v x ≤ p_check x := by
    intro x hx
    obtain ⟨μ, hμ_x⟩ := s.feasible x hx
    have h_vx : v x = s.composedValue v μ := by
      unfold MomentSetup.composedValue; rw [hμ_x]
    rw [h_vx]
    -- p_check x = inf { ∫ p_star dν | posteriorMoment ν = x }; since
    -- composedValue v μ ≤ ∫ p_star dν for every such ν (by dual feasibility),
    -- composedValue v μ ≤ p_check x.
    set S : Set ℝ := { z : ℝ | ∃ ν : ProbDist Ω,
        s.posteriorMoment ν = x ∧ z = ProbDist.expect ν p_star } with hS_def
    have h_lb : ∀ z ∈ S, s.composedValue v μ ≤ z := by
      rintro z ⟨ν, hν_x, rfl⟩
      have h_eq : s.composedValue v μ = s.composedValue v ν := by
        unfold MomentSetup.composedValue; rw [hμ_x, hν_x]
      rw [h_eq]
      exact hp_star_majorizes ν
    have hp_star_bdd : ∃ M, ∀ ω, |p_star ω| ≤ M := by
      have hbdd : Bornology.IsBounded (Set.range p_star) :=
        (isCompact_range hp_star_cont).isBounded
      obtain ⟨M, hM⟩ := hbdd.exists_norm_le
      exact ⟨M, fun ω => by
        have := hM (p_star ω) ⟨ω, rfl⟩
        simpa [Real.norm_eq_abs] using this⟩
    obtain ⟨M, hM_abs⟩ := hp_star_bdd
    have hM_lb : ∀ ω, -M ≤ p_star ω := fun ω => (abs_le.mp (hM_abs ω)).1
    have hS_bdd : BddBelow S := by
      refine ⟨-M, ?_⟩
      rintro z ⟨ν, _, rfl⟩
      show -M ≤ ProbDist.expect ν p_star
      have h_const : (-M : ℝ) = ∫ x, (-M : ℝ) ∂ν.toMeasure := by simp
      rw [h_const]
      exact MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const _)
        (hp_star_int ν) (ae_of_all _ hM_lb)
    exact le_csInf ⟨ProbDist.expect μ p_star, μ, hμ_x, rfl⟩ h_lb
  have h_envelope_le_check : ∀ y ∈ s.X, pbar y ≤ p_check y :=
    upperEnvelope_le_convexRoof_on_X s hq_subg_set h_v_le_pcheck
  have hpbar_lip : LipschitzWith Kp_star pbar :=
    upperEnvelope_lipschitzWith s hv_cont hq_norm
  have hpbar_convex_univ : ConvexOn ℝ Set.univ pbar :=
    upperEnvelope_convexOn s hv_cont hq_norm
  have hpbar_convex_X : ConvexOn ℝ s.X pbar :=
    hpbar_convex_univ.subset (Set.subset_univ _) s.X_convex
  have hpbar_ge_v : ∀ y ∈ s.X, v y ≤ pbar y :=
    upperEnvelope_ge_v_on_X s hv_cont hq_norm
  have hpbar_envelope : ∀ y ∈ s.X,
      pbar y = sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
        v x + inner ℝ (q x) (y - x)) '' s.X) := by
    intro y _; rfl
  have hpbar_cont : Continuous pbar := hpbar_lip.continuous
  set pbar_m : Ω → ℝ := fun ω => pbar (s.m ω) with hpbar_m_def
  have hpbar_m_cont : Continuous pbar_m := hpbar_cont.comp s.m_continuous
  -- `pbar_m` is continuous on a compact space, hence integrable against any measure.
  have hpbar_m_int : ∀ μ : ProbDist Ω, MeasureTheory.Integrable pbar_m μ.toMeasure :=
    fun μ => hpbar_m_cont.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hpbar_m_lip : LipschitzWith (Kp_star * Real.toNNReal (Real.sqrt n)) pbar_m := by
    -- Each coordinate of `s.m` is 1-Lipschitz, so the vector map is √n-Lipschitz
    -- by Cauchy-Schwarz; composing with the Kp_star-Lipschitz `pbar` gives the bound.
    have hm_lip_vec : LipschitzWith (Real.toNNReal (Real.sqrt n)) s.m := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro ω₁ ω₂
      rw [dist_eq_norm, EuclideanSpace.norm_eq]
      have h_each : ∀ i : Fin n,
          ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2 ≤ dist ω₁ ω₂ ^ 2 := by
        intro i
        rw [PiLp.sub_apply]
        simp only [Real.norm_eq_abs, sq_abs]
        -- Each coordinate of `s.m` is 1-Lipschitz, so |Δᵢ| ≤ dist; square both sides.
        have h_abs_le : |s.m ω₁ i - s.m ω₂ i| ≤ dist ω₁ ω₂ := by
          have h_lipi := (hm_lip i).dist_le_mul ω₁ ω₂
          rw [Real.dist_eq] at h_lipi; simpa using h_lipi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs_le 2
      have h_sum_le : ∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2
                    ≤ (n : ℝ) * dist ω₁ ω₂ ^ 2 := by
        calc ∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2
            ≤ ∑ _i : Fin n, dist ω₁ ω₂ ^ 2 :=
              Finset.sum_le_sum (fun i _ => h_each i)
          _ = (n : ℝ) * dist ω₁ ω₂ ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h_dist_nn : 0 ≤ Real.sqrt (∑ i : Fin n,
          ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2) := Real.sqrt_nonneg _
      have h_sqrt_le : Real.sqrt (∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2)
            ≤ Real.sqrt ((n : ℝ) * dist ω₁ ω₂ ^ 2) :=
        Real.sqrt_le_sqrt h_sum_le
      have h_sqrt_eq : Real.sqrt ((n : ℝ) * dist ω₁ ω₂ ^ 2)
            = Real.sqrt n * dist ω₁ ω₂ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq dist_nonneg]
      rw [h_sqrt_eq] at h_sqrt_le
      have hcoe : ((Real.toNNReal (Real.sqrt n) : NNReal) : ℝ) = Real.sqrt n :=
        Real.coe_toNNReal _ hsqrt_n_nn
      rw [hcoe]
      exact h_sqrt_le
    exact hpbar_lip.comp hm_lip_vec
  have hpbar_m_lip' : ∃ K : NNReal, LipschitzWith K pbar_m :=
    ⟨Kp_star * Real.toNNReal (Real.sqrt n), hpbar_m_lip⟩
  have h_majorizes : ∀ μ : ProbDist Ω,
      s.composedValue v μ ≤ ProbDist.expect μ pbar_m := by
    intro μ
    have h_post_X : s.posteriorMoment μ ∈ s.X := h_post_mem μ
    have h_v_le : v (s.posteriorMoment μ) ≤ pbar (s.posteriorMoment μ) :=
      hpbar_ge_v _ h_post_X
    have h_jensen : pbar (s.posteriorMoment μ) ≤ ProbDist.expect μ pbar_m := by
      have h_pbar_int : MeasureTheory.Integrable pbar_m μ.toMeasure := hpbar_m_int μ
      have h_m_int : MeasureTheory.Integrable s.m μ.toMeasure := s.m_integrable μ
      have h_ae : ∀ᵐ ω ∂μ.toMeasure, s.m ω ∈ s.X :=
        ae_of_all _ s.m_mem_X
      have h_X_closed : IsClosed s.X := s.X_compact.isClosed
      have h_pbar_contOn : ContinuousOn pbar s.X := hpbar_cont.continuousOn
      have := hpbar_convex_X.map_integral_le h_pbar_contOn h_X_closed
        h_ae h_m_int h_pbar_int
      simpa [MomentSetup.posteriorMoment, ProbDist.expect, pbar_m, Function.comp]
        using this
    unfold MomentSetup.composedValue
    linarith
  have h_dual_feas : IsDualFeasible (s.composedValue v) pbar_m :=
    ⟨hpbar_m_lip', h_majorizes⟩
  have hp_star_int_prior : MeasureTheory.Integrable p_star s.prior.toMeasure :=
    hp_star_int s.prior
  have hpbar_m_int_prior : MeasureTheory.Integrable pbar_m s.prior.toMeasure :=
    hpbar_m_int s.prior
  have h_pbar_m_le : ∀ ω, pbar_m ω ≤ p_star ω := by
    intro ω
    have h₁ : pbar (s.m ω) ≤ p_check (s.m ω) := h_envelope_le_check _ (s.m_mem_X ω)
    have h₂ : p_check (s.m ω) ≤ p_star ω := convexRoof_le_lifted_p s hp_star_cont ω
    exact h₁.trans h₂
  have h_dualObj_le : dualObjective s.prior pbar_m ≤ dualObjective s.prior p_star := by
    unfold dualObjective ProbDist.expect
    exact MeasureTheory.integral_mono_ae hpbar_m_int_prior hp_star_int_prior
      (ae_of_all _ h_pbar_m_le)
  have h_dualObj_eq_env : dualObjective s.prior pbar_m
      = dualValue (s.composedValue v) s.prior := by
    apply le_antisymm
    · rw [← hp_star_eq]; exact h_dualObj_le
    · unfold dualValue
      refine csInf_le ?_ ⟨pbar_m, h_dual_feas, rfl⟩
      obtain ⟨M, hM⟩ := hV_bdd
      refine ⟨-M, ?_⟩
      rintro z ⟨p, hp_feas, rfl⟩
      have hpV : s.composedValue v s.prior ≤ ProbDist.expect s.prior p :=
        hp_feas.majorizes s.prior
      have hVlb : -M ≤ s.composedValue v s.prior := (abs_le.mp (hM s.prior)).1
      change -M ≤ ProbDist.expect s.prior p
      linarith
  refine ⟨pbar, q, ?_, h_dual_feas, h_dualObj_eq_env⟩
  refine
    { pbar_convex := hpbar_convex_X
      pbar_lipschitz := ⟨Kp_star, hpbar_lip⟩
      pbar_ge_v := hpbar_ge_v
      q_measurable := hq_meas
      q_norm_bound := ⟨(Kp_star : ℝ), Kp_star.coe_nonneg, hq_norm⟩
      pbar_envelope := hpbar_envelope }

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
