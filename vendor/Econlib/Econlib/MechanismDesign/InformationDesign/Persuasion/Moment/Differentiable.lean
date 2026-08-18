/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceCanonical
public import Econlib.Probability.ProbDist.Borel

/-!
# Differentiable moment persuasion: Optimality and condition (M)

When the moment value `v : X → ℝ` is `C¹`, the dual price becomes the upper envelope of tangent
hyperplanes to `v` at the active set `S ⊆ X`. This file establishes the differentiable-case
optimality characterization: A feasible joint is optimal if and only if condition (M) holds for
some candidate active set `S`.

The characterization carries more than `C¹`-smoothness of `v`. Beyond differentiability,
`optimality_iff_M` requires Lipschitzness of the moment coordinates, Lipschitzness/measurability/
boundedness/upper semicontinuity of `v`, measurability and upper semicontinuity of the composed
value, Lipschitzness of the posterior check on `X`, an open-positive prior measure, and density of
the moment image in `X` (`s.X ⊆ closure (range m)`). The `MomentSetup` surjectivity field
`moment_surjOn_X` — every point of `X` is achievable as a posterior moment — is also in force.

## Main statements

* `optimality_iff_M` — under the conditioning above, a feasible joint is optimal if and only if
  condition (M) holds at some `S`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 6.

## Tags

persuasion, moment persuasion, differentiable, condition M
-/

@[expose] public section

open MeasureTheory Set Real Filter
open scoped NNReal Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

variable {n : ℕ}

/-! ## Optimality and condition (M) -/

/-- For a `C¹`, Lipschitz value function `v` and a feasible joint `pi ∈ Π(μ₀)`, optimality of `pi`
for the moment-persuasion problem is equivalent to the existence of a candidate active set `S` such
that condition (M) holds.

Beyond `C¹`-smoothness and Lipschitzness of `v`, the equivalence assumes (all explicit below):
Lipschitzness of the moment coordinates (`hm_lip`); measurability, boundedness, and upper
semicontinuity of `v`; measurability and upper semicontinuity of the composed value; Lipschitzness
of the posterior check on `X` (`h_pcheck_lip`); an open-positive prior measure
(`IsOpenPosMeasure`); and density of the moment image in `X` (`h_dense`). The `MomentSetup`
surjectivity field `moment_surjOn_X` is in force as part of `s`. -/
theorem optimality_iff_M
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    (hv_usc : UpperSemicontinuous v)
    (hV_meas : Measurable (s.composedValue v))
    (hV_usc : UpperSemicontinuous (s.composedValue v))
    (h_pcheck_lip : ∀ {p : Ω → ℝ} {K : NNReal},
      LipschitzWith K p →
        LipschitzOnWith K (convexRoof s p) s.X)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (hpi : pi ∈ feasibleJoint s)
    [s.prior.toMeasure.IsOpenPosMeasure]
    (h_dense : s.X ⊆ closure (Set.range s.m)) :
    (∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v) ↔
      ∃ S : Set (EuclideanSpace ℝ (Fin n)), ConditionM s v pi S := by
  refine ⟨?_, ?_⟩
  · intro h_opt
    obtain ⟨pbar, q, h_struct, h_dual, h_value, h_slack⟩ :=
      prices_for_moments_with_slackness s hm_lip hv_lip hv_meas hv_bdd hv_usc
        hV_meas hV_usc h_pcheck_lip
    have h_slack_pi := h_slack pi hpi h_opt
    exact ⟨Prod.fst '' pi.toMeasure.support, hpi,
      optimality_implies_pStar_majorizes s hm_lip hv_lip hv_diff hv_meas hv_bdd hpi h_opt
        h_struct h_dual h_value h_slack_pi h_dense,
      optimality_implies_active_ae s hv_lip hv_diff hv_meas hv_bdd hpi
        h_struct h_slack_pi,
      rfl⟩
  · rintro ⟨S, hM⟩
    have hS_subX : S ⊆ s.X := by
      rw [hM.S_eq_support]
      -- support of π is contained in the closed set `Prod.fst ⁻¹' s.X`.
      have h_X_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
        s.X_compact.isClosed
      have h_pre_closed : IsClosed
          ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
        h_X_closed.preimage continuous_fst
      have h_pre_ae : (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
          ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
        rw [MeasureTheory.mem_ae_iff]
        exact (MeasureTheory.prob_compl_eq_zero_iff
          (h_X_closed.measurableSet.preimage measurable_fst)).mpr hpi.fst_supportsOn
      have h_supp_sub :
          pi.toMeasure.support ⊆ (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω →
            EuclideanSpace ℝ (Fin n)) ⁻¹' s.X :=
        MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed h_pre_ae
      rintro x ⟨p, hp_supp, rfl⟩
      exact h_supp_sub hp_supp
    have h_obj_eq :=
      objective_eq_pStar_integral_of_conditionM s hv_lip hv_diff hS_subX hM
    have h_pStar_convexOn : ConvexOn ℝ s.X (pStar v S) := pStar_convexOn s hv_diff hS_subX
    have h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) :=
      fun x _ => norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_pStar_lipWith : LipschitzWith L (pStar v S) :=
      pStar_lipschitzWith s hv_diff hS_subX h_slope
    have h_pStar_lipOn : LipschitzOnWith L (pStar v S) s.X := h_pStar_lipWith.lipschitzOnWith
    have h_pStar_cont : Continuous (pStar v S) := h_pStar_lipWith.continuous
    obtain ⟨M_v, hM_v⟩ := hv_bdd
    have h_ae_p1_of : ∀ {π' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)},
        π' ∈ feasibleJoint s → ∀ᵐ p ∂π'.toMeasure, p.1 ∈ s.X := by
      intro π' hπ'
      rw [MeasureTheory.ae_iff]
      have h_pre_meas : MeasurableSet
          ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
        s.X_compact.isClosed.measurableSet.preimage measurable_fst
      -- `{p | ¬ p.1 ∈ s.X}` is definitionally the complement of the fst-preimage of `s.X`.
      change π'.toMeasure ((Prod.fst ⁻¹' s.X)ᶜ) = 0
      rw [MeasureTheory.prob_compl_eq_zero_iff h_pre_meas]
      exact hπ'.fst_supportsOn
    have h_pStarm_compact : IsCompact (pStar v S '' s.X) := s.X_compact.image h_pStar_cont
    obtain ⟨M_pStar, hM_pStar⟩ := h_pStarm_compact.isBounded.exists_norm_le
    have h_v_int_of : ∀ {π' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)},
        π' ∈ feasibleJoint s →
          MeasureTheory.Integrable (fun p => v p.1) π'.toMeasure := by
      intro π' hπ'
      refine MeasureTheory.Integrable.of_bound (hv_meas.comp measurable_fst).aestronglyMeasurable
        M_v ?_
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Real.norm_eq_abs]; exact hM_v _
    have h_pStarm_p_cont : Continuous
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S (s.m p.2)) :=
      (h_pStar_cont.comp s.m_continuous).comp continuous_snd
    have h_pStarm_int_of : ∀ {π' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)},
        MeasureTheory.Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S (s.m p.2)) π'.toMeasure := by
      intro π'
      refine MeasureTheory.Integrable.of_bound h_pStarm_p_cont.aestronglyMeasurable M_pStar ?_
      refine Filter.Eventually.of_forall (fun p => ?_)
      have := hM_pStar (pStar v S (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
      simpa using this
    have h_uniform_ub : ∀ π' ∈ feasibleJoint s,
        ∫ p, v p.1 ∂π'.toMeasure
          ≤ ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure := by
      intro π' hπ'
      have h_jensen :=
        MomentSetup.integral_fst_le_integral_m_of_convexOn s hπ' h_pStar_convexOn h_pStar_lipOn
      have h_marg : ∫ p, pStar v S (s.m p.2) ∂π'.toMeasure
          = ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure := by
        have h_aem_pStar : AEStronglyMeasurable (fun ω => pStar v S (s.m ω))
            ((ProbDist.map π' Prod.snd measurable_snd).toMeasure) :=
          (h_pStar_cont.comp s.m_continuous).aestronglyMeasurable
        have hexp := ProbDist.expect_map π' Prod.snd measurable_snd
          (fun ω => pStar v S (s.m ω)) h_aem_pStar
        rw [hπ'.marginal] at hexp
        exact hexp.symm
      have h_v_le_pStar_ae : ∀ᵐ p ∂π'.toMeasure, v p.1 ≤ pStar v S p.1 := by
        filter_upwards [h_ae_p1_of hπ'] with p hp1
        exact hM.pStar_majorizes p.1 hp1
      have h_pStar_p1_int : MeasureTheory.Integrable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S p.1) π'.toMeasure := by
        refine MeasureTheory.Integrable.of_bound
          ((h_pStar_cont.comp continuous_fst).aestronglyMeasurable) M_pStar ?_
        filter_upwards [h_ae_p1_of hπ'] with p hp1
        have := hM_pStar (pStar v S p.1) ⟨p.1, hp1, rfl⟩
        simpa using this
      have h_v_le_int : ∫ p, v p.1 ∂π'.toMeasure ≤ ∫ p, pStar v S p.1 ∂π'.toMeasure :=
        MeasureTheory.integral_mono_ae (h_v_int_of hπ') h_pStar_p1_int h_v_le_pStar_ae
      linarith [h_v_le_int, h_jensen, h_marg.symm.le, h_marg.le]
    change ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v
    unfold momentPrimal
    refine le_antisymm ?_ ?_
    · refine le_csSup ?_ ⟨pi, hpi, rfl⟩
      refine ⟨∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure, ?_⟩
      rintro y ⟨π', hπ', rfl⟩
      exact h_uniform_ub π' hπ'
    · refine csSup_le ⟨∫ p, v p.1 ∂pi.toMeasure, pi, hpi, rfl⟩ ?_
      rintro y ⟨π', hπ', rfl⟩
      calc ∫ p, v p.1 ∂π'.toMeasure
          ≤ ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure := h_uniform_ub π' hπ'
        _ = ∫ p, v p.1 ∂pi.toMeasure := h_obj_eq.symm

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
