/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Differentiable
public import Econlib.Probability.ProbDist.Borel

/-!
# Canonical active set `S_star`

The active-set selector for the formula-S optimality characterization. `S_star v S` is the
canonical refinement of a candidate active set `S ⊆ X` — the subset on which the formula-S envelope
is already tight against `v`.

## Main definitions

* `S_star` — the canonical active set selected within a candidate `S`.

## Main statements

* `optimality_iff_M_with_Sstar` — strengthens `optimality_iff_M` with the explicit `S ⊆ S_star v S`
  selector witness.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 6.

## Tags

persuasion, moment persuasion, active set
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

/-! ## The canonical active set `S_star` -/

/-- **Candidate-relative active set.**  Given a candidate active set `S ⊆ s.X`, the *active-tangent
points within `S`* are those `x ∈ S` where `v(x)` is already on the formula-`S` upper envelope:

`S_star v S = { x ∈ S : v x = pStar v S x }`.

Under `ConditionM s v pi S` and optimality of `pi`, we always have `S ⊆ S_star v S` — the
active-tangent identity holds at every point of the projection support.

Note that the global active set `{x ∈ s.X : v x = pStar v s.X x}` is not in general a superset of
`supp(pi_X)` for optimal `pi`: For concave `v`, `pStar v s.X y > v y` everywhere, so the global
`S_star` is empty even when `supp(pi_X)` is nonempty.  The candidate-relative version (using
`pStar v S`, not `pStar v s.X`) avoids this. -/
-- `s` is unused in the body but kept so call sites can write `S_star s v S`,
-- matching the `S ⊆ S_star s v S` API used throughout this module's consumers.
noncomputable def S_star (_s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x ∈ S | v x = pStar v S x}

/-- Optimality is equivalent to condition (M) holding at some `S` whose every point is an
active-tangent point in `S` itself: `S ⊆ S_star v S`. -/
theorem optimality_iff_M_with_Sstar
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
      ∃ S, ConditionM s v pi S ∧ S ⊆ S_star s v S := by
  rw [optimality_iff_M s hm_lip hv_lip hv_diff hv_meas hv_bdd hv_usc hV_meas hV_usc
        h_pcheck_lip pi hpi h_dense]
  refine ⟨?_, ?_⟩
  · rintro ⟨S, hM⟩
    refine ⟨S, hM, ?_⟩
    intro x hxS
    -- Two-sided bound: pStar v S x ≥ v x (from majorization) and pStar v S x ≤ v x (from
    -- structured prices on the support).
    have hS_subX : S ⊆ s.X := by
      rw [hM.S_eq_support]
      have h_X_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
        s.X_compact.isClosed
      have h_pre_closed : IsClosed
          ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
        h_X_closed.preimage continuous_fst
      have h_pre_ae : (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
          ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
        rw [MeasureTheory.mem_ae_iff]
        exact (MeasureTheory.prob_compl_eq_zero_iff
          (h_pre_closed.measurableSet)).mpr hpi.fst_supportsOn
      have h_supp_sub : pi.toMeasure.support ⊆
          (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X :=
        MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed h_pre_ae
      rintro y ⟨p, hp_supp, rfl⟩
      exact h_supp_sub hp_supp
    have hx_in_X : x ∈ s.X := hS_subX hxS
    have h_pStar_ge : v x ≤ pStar v S x := hM.pStar_majorizes x hx_in_X
    have h_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v := by
      rw [optimality_iff_M s hm_lip hv_lip hv_diff hv_meas hv_bdd hv_usc hV_meas hV_usc
        h_pcheck_lip pi hpi h_dense]
      exact ⟨S, hM⟩
    obtain ⟨pbar, q, h_struct, -, -, h_slack⟩ :=
      prices_for_moments_with_slackness s hm_lip hv_lip hv_meas hv_bdd hv_usc
        hV_meas hV_usc h_pcheck_lip
    have h_slack_pi := h_slack pi hpi h_opt
    -- `pbar = v` pointwise on `S = Prod.fst '' supp(pi)`, by the canonical-active identification.
    have hS_active : ∀ y ∈ S, pbar y = v y := by
      rw [hM.S_eq_support]
      exact pbar_eq_v_on_active_support s hv_lip hv_meas hv_bdd hpi h_struct h_slack_pi
    have h_pStar_le : pStar v S x ≤ v x := by
      unfold pStar
      apply csSup_le
      · exact ⟨v x + (fderiv ℝ v x) (x - x), x, hxS, rfl⟩
      rintro _ ⟨z, hzS, rfl⟩
      have hz_X : z ∈ s.X := hS_subX hzS
      have hz_active : v z = pbar z := (hS_active z hzS).symm
      have hx_active : v x = pbar x := (hS_active x hxS).symm
      have h_subg := HasMomentPrices.fderiv_isSubgradient_of_active s hv_diff h_struct z hz_X
        hz_active x (hS_subX hxS)
      linarith
    exact ⟨hxS, le_antisymm h_pStar_ge h_pStar_le⟩
  · rintro ⟨S, hM, _⟩
    exact ⟨S, hM⟩

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
