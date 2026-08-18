/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceStructural

/-!
# Formula-S optimality: Forward direction

The forward direction of the formula-S optimality characterization: Optimality at a feasible joint
implies the formula-S envelope majorizes `v` on the active support and the active-tangent identity
holds prior-a.e.

## Main statements

* `MomentSetup.inner_q_eq_fderiv_ae_of_optimal` — at an optimal joint, `⟨q(x), m ω − x⟩` equals
  `(∇v(x))(m ω − x)` prior-a.e.
* `MomentSetup.pbar_le_pStar_on_X` — at an optimal joint, `pbar` is bounded by `pStar v S` on `s.X`.
* `optimality_implies_pStar_majorizes` — optimality at a feasible joint implies `pStar v S`
  dominates `v` on the projected support.
* `optimality_implies_active_ae` — optimality implies the active-tangent identity holds prior-a.e.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 6.

## Tags

persuasion, moment persuasion, formula S, optimality
-/

@[expose] public section

open MeasureTheory Set Real Filter
open scoped NNReal Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
  [T2Space Ω] [SecondCountableTopology Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

variable {n : ℕ}

/-! ### Forward-direction structural lemmas

The forward implication is packaged as measurable tangent identities, envelope bounds, and
active-tangent statements. -/

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For optimal `π` with structured prices `(pbar, q)`, the slope `q(x)` and the gradient `∇v(x)`
produce the same inner product against the martingale difference `m ω − x` for `π`-a.e. `(x, ω)`:

`⟨q(x), m ω − x⟩ = (fderiv ℝ v x)(m ω − x)`. -/
lemma MomentSetup.inner_q_eq_fderiv_ae_of_optimal
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    -- kept to match the "optimal π" hypothesis package used by callers of this lemma; the
    -- tangent identity itself follows from `h_slack_pi` alone.
    (_h_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) :
    ∀ᵐ p ∂pi.toMeasure,
      inner ℝ (q p.1) (s.m p.2 - p.1) = (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
  obtain ⟨K_pbar, h_pbar_lip⟩ := h_struct.pbar_lipschitz
  obtain ⟨K_q, h_K_q_nn, h_q_norm⟩ := h_struct.q_norm_bound
  have h_pbar_cont : Continuous pbar := h_pbar_lip.continuous
  -- Confinement: π-ae, p.1 ∈ s.X.
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_fst_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    h_X_meas.preimage measurable_fst
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    have h_set_eq :
        {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
          = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
              ⁻¹' s.X)ᶜ := rfl
    rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_fst_meas]
    exact hpi.fst_supportsOn
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  obtain ⟨M_v, hM_v⟩ := hv_bdd
  have h_pbar_compact : IsCompact (pbar '' s.X) := s.X_compact.image h_pbar_cont
  obtain ⟨M_pbar, hM_pbar⟩ := h_pbar_compact.isBounded.exists_norm_le
  have h_pbar_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure :=
    (h_pbar_cont.comp continuous_fst).aestronglyMeasurable
  have h_v_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure :=
    (hv_meas.comp measurable_fst).aestronglyMeasurable
  have h_pbar_m_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure :=
    (h_pbar_cont.comp (s.m_continuous.comp continuous_snd)).aestronglyMeasurable
  have h_pbar_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_fst_aem M_pbar ?_
    filter_upwards [h_ae_p1] with p hp1
    have := hM_pbar (pbar p.1) ⟨p.1, hp1, rfl⟩
    simpa using this
  have h_v_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_v_fst_aem M_v ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]; exact hM_v _
  have h_pbar_m_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_m_aem M_pbar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hM_pbar (pbar (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  have h_inner_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        inner ℝ (q p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_q_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => q p.1) :=
      h_struct.q_measurable.comp measurable_fst
    have h_m_meas : Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
      (s.m_continuous.comp continuous_snd).measurable.sub measurable_fst
    exact (continuous_inner.measurable.comp (h_q_meas.prodMk h_m_meas)).aestronglyMeasurable
  have h_inner_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (q p.1) (s.m p.2 - p.1))
      pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_inner_aem (K_q * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_cs : ‖inner ℝ (q p.1) (s.m p.2 - p.1)‖
        ≤ ‖q p.1‖ * ‖s.m p.2 - p.1‖ := norm_inner_le_norm _ _
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    have h_diff_nn : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
    exact h_cs.trans (mul_le_mul (h_q_norm p.1) h_diff_norm h_diff_nn h_K_q_nn)
  have h_pbar_lip_on : LipschitzOnWith K_pbar pbar s.X :=
    h_pbar_lip.lipschitzOnWith
  have h_jensen_pbar : ∫ p, pbar p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure :=
    MomentSetup.integral_fst_le_integral_m_of_convexOn s hpi h_struct.pbar_convex h_pbar_lip_on
  have h_cross_zero : ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 :=
    hpi.martingale_inner_measurable h_struct.q_measurable ⟨K_q, h_q_norm⟩
  have h_slack_integ : ∫ p, pbar (s.m p.2) ∂pi.toMeasure
      = ∫ p, v p.1 ∂pi.toMeasure
        + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := by
    have h_eq_ae : (fun p => pbar (s.m p.2))
        =ᵐ[pi.toMeasure]
          (fun p => v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) := by
      filter_upwards [h_slack_pi] with p hp using hp
    rw [MeasureTheory.integral_congr_ae h_eq_ae,
      MeasureTheory.integral_add h_v_fst_int h_inner_int]
  have h_pbar_ge_v_ae : ∀ᵐ p ∂pi.toMeasure, v p.1 ≤ pbar p.1 := by
    filter_upwards [h_ae_p1] with p hp1 using h_struct.pbar_ge_v _ hp1
  have h_int_v_le_int_pbar : ∫ p, v p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar p.1 ∂pi.toMeasure :=
    MeasureTheory.integral_mono_ae h_v_fst_int h_pbar_fst_int h_pbar_ge_v_ae
  have h_int_pbar_eq_v : ∫ p, pbar p.1 ∂pi.toMeasure = ∫ p, v p.1 ∂pi.toMeasure := by
    have h_chain : ∫ p, pbar p.1 ∂pi.toMeasure ≤ ∫ p, v p.1 ∂pi.toMeasure := by
      calc ∫ p, pbar p.1 ∂pi.toMeasure
          ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure := h_jensen_pbar
        _ = ∫ p, v p.1 ∂pi.toMeasure
            + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := h_slack_integ
        _ = ∫ p, v p.1 ∂pi.toMeasure := by rw [h_cross_zero, add_zero]
    linarith
  have h_diff_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1) pi.toMeasure :=
    h_pbar_fst_int.sub h_v_fst_int
  have h_diff_nonneg : ∀ᵐ p ∂pi.toMeasure, 0 ≤ pbar p.1 - v p.1 := by
    filter_upwards [h_pbar_ge_v_ae] with p hp using by linarith
  have h_diff_int_zero : ∫ p, (pbar p.1 - v p.1) ∂pi.toMeasure = 0 := by
    rw [MeasureTheory.integral_sub h_pbar_fst_int h_v_fst_int, h_int_pbar_eq_v, sub_self]
  have h_active_ae_pbar : ∀ᵐ p ∂pi.toMeasure, pbar p.1 = v p.1 := by
    have h_diff_zero_ae : (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1)
        =ᵐ[pi.toMeasure] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_diff_int).mp
        h_diff_int_zero
    filter_upwards [h_diff_zero_ae] with p hp
    exact sub_eq_zero.mp hp
  have h_subgrad_ae :
      ∀ᵐ p ∂pi.toMeasure,
        (fderiv ℝ v p.1) (s.m p.2 - p.1) ≤ inner ℝ (q p.1) (s.m p.2 - p.1) := by
    filter_upwards [h_ae_p1, h_active_ae_pbar, h_slack_pi] with p hp1 hp_active hp_slack
    have h_subgrad : v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1)
        ≤ pbar (s.m p.2) :=
      HasMomentPrices.fderiv_isSubgradient_of_active s hv_diff h_struct
        p.1 hp1 hp_active.symm (s.m p.2) (s.m_mem_X p.2)
    rw [hp_slack] at h_subgrad
    linarith
  have h_fderiv_cross_zero :=
    feasibleJoint_fderiv_cross_zero s hpi hv_lip hv_diff
  have h_fd_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_joint :
        Continuous fun q : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
          (fderiv ℝ v q.1) q.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    have h_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) := by
      refine h_joint.comp (Continuous.prodMk continuous_fst ?_)
      exact (s.m_continuous.comp continuous_snd).sub continuous_fst
    exact h_cont.aestronglyMeasurable
  have h_fd_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_fd_aem ((L : ℝ) * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_op : ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := ContinuousLinearMap.le_opNorm _ _
    have h_fd_norm : ‖fderiv ℝ v p.1‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    calc ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := h_op
      _ ≤ (L : ℝ) * (R + R) :=
          mul_le_mul h_fd_norm h_diff_norm (norm_nonneg _) L.coe_nonneg
  -- δ = inner - fderiv is ae nonneg with zero integral, hence ae zero.
  set δ : EuclideanSpace ℝ (Fin n) × Ω → ℝ := fun p =>
    inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1) with hδ_def
  have h_δ_int : MeasureTheory.Integrable δ pi.toMeasure := h_inner_int.sub h_fd_int
  have h_δ_nonneg : ∀ᵐ p ∂pi.toMeasure, 0 ≤ δ p := by
    filter_upwards [h_subgrad_ae] with p hp
    change 0 ≤ inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1)
    linarith
  have h_δ_int_zero : ∫ p, δ p ∂pi.toMeasure = 0 := by
    simp only [hδ_def]
    rw [MeasureTheory.integral_sub h_inner_int h_fd_int, h_cross_zero, h_fderiv_cross_zero,
      sub_zero]
  have h_δ_zero_ae : δ =ᵐ[pi.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_δ_nonneg h_δ_int).mp h_δ_int_zero
  filter_upwards [h_δ_zero_ae] with p hp
  have hδp : inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1) = 0 := hp
  linarith

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For optimal `π` with structured prices `(pbar, q)`, the upper-envelope sup defining `pbar(y)`
(over `s.X`) is bounded by the formula-S envelope `pStar v S(y)` (over the projection support
`S = Prod.fst '' pi.toMeasure.support`):

`∀ y ∈ s.X,  pbar(y) ≤ pStar v S(y)`. -/
lemma MomentSetup.pbar_le_pStar_on_X
    -- kept to match the "structured dual optimum" hypothesis package used by callers; the
    -- envelope bound proved here only needs `h_opt`, `h_struct`, and `h_slack_pi`.
    (s : MomentSetup Ω n) (_hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    (h_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    -- kept to match the caller's hypothesis package; not needed by this proof.
    (_h_dual : IsDualFeasible (s.composedValue v) (fun ω => pbar (s.m ω)))
    -- kept to match the caller's hypothesis package; not needed by this proof.
    (_h_value : dualObjective s.prior (fun ω => pbar (s.m ω))
        = dualValue (s.composedValue v) s.prior)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1))
    [h_prior_full : s.prior.toMeasure.IsOpenPosMeasure]
    (h_dense : s.X ⊆ closure (Set.range s.m)) :
    ∀ y ∈ s.X, pbar y ≤ pStar v (Prod.fst '' pi.toMeasure.support) y := by
  set S : Set (EuclideanSpace ℝ (Fin n)) := Prod.fst '' pi.toMeasure.support with hS_def
  have hA := MomentSetup.inner_q_eq_fderiv_ae_of_optimal s hv_lip hv_diff hv_meas hv_bdd hpi h_opt
    h_struct h_slack_pi
  have h_pre_X_closed : IsClosed
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    s.X_compact.isClosed.preimage continuous_fst
  have h_pre_X_ae : (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
      ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff
      (h_pre_X_closed.measurableSet)).mpr hpi.fst_supportsOn
  have h_supp_sub_X : pi.toMeasure.support ⊆
      (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_X_closed h_pre_X_ae
  have hS_subX : S ⊆ s.X := by
    rintro x ⟨p, hp_supp, rfl⟩
    exact h_supp_sub_X hp_supp
  obtain ⟨K_pbar, h_pbar_lip⟩ := h_struct.pbar_lipschitz
  have h_pbar_cont : Continuous pbar := h_pbar_lip.continuous
  have h_v_cont : Continuous v := hv_lip.continuous
  have h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) :=
    fun x _ => norm_fderiv_le_of_lipschitz ℝ hv_lip
  have h_pStar_lip : LipschitzWith L (pStar v S) :=
    pStar_lipschitzWith s hv_diff hS_subX h_slope
  have h_pStar_cont : Continuous (pStar v S) := h_pStar_lip.continuous
  have h_supp_ae : ∀ᵐ p ∂pi.toMeasure, p ∈ pi.toMeasure.support :=
    MeasureTheory.Measure.support_mem_ae
  have h_ae_at_m : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) ≤ pStar v S (s.m p.2) := by
    filter_upwards [hA, h_slack_pi, h_supp_ae] with p hp_A hp_slack hp_supp
    have hp1_in_S : p.1 ∈ S := ⟨p, hp_supp, rfl⟩
    have h_pbar_eq : pbar (s.m p.2) = v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
      rw [hp_slack, hp_A]
    have h_pStar_ge : v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1)
        ≤ pStar v S (s.m p.2) := by
      unfold pStar
      apply le_csSup (pStar_image_bddAbove s hv_diff hS_subX (s.m p.2))
      exact ⟨p.1, hp1_in_S, rfl⟩
    rw [h_pbar_eq]; exact h_pStar_ge
  have hmarg : ProbDist.map pi Prod.snd measurable_snd = s.prior := hpi.marginal
  have h_meas_set : MeasurableSet
      {ω : Ω | pbar (s.m ω) ≤ pStar v S (s.m ω)} := by
    refine measurableSet_le ?_ ?_
    · exact (h_pbar_cont.comp s.m_continuous).measurable
    · exact (h_pStar_cont.comp s.m_continuous).measurable
  have h_ae_at_m_prior : ∀ᵐ ω ∂s.prior.toMeasure,
      pbar (s.m ω) ≤ pStar v S (s.m ω) := by
    rw [← hmarg]
    show ∀ᵐ ω ∂(ProbDist.map pi Prod.snd measurable_snd).toMeasure,
        pbar (s.m ω) ≤ pStar v S (s.m ω)
    rw [ProbDist.map_toMeasure]
    rw [MeasureTheory.ae_map_iff measurable_snd.aemeasurable h_meas_set]
    exact h_ae_at_m
  -- `{ω : pStar v S(m ω) < pbar(m ω)}` is open and has zero prior measure, so empty.
  have h_pbar_le_on_omega : ∀ ω : Ω, pbar (s.m ω) ≤ pStar v S (s.m ω) := by
    intro ω
    by_contra h_neg
    push Not at h_neg
    set U : Set Ω := {ω' : Ω | pStar v S (s.m ω') < pbar (s.m ω')} with hU_def
    have hU_open : IsOpen U :=
      isOpen_lt (h_pStar_cont.comp s.m_continuous) (h_pbar_cont.comp s.m_continuous)
    have hU_mem : ω ∈ U := h_neg
    have hU_ne : U.Nonempty := ⟨ω, hU_mem⟩
    have hU_pos : s.prior.toMeasure U ≠ 0 :=
      h_prior_full.open_pos U hU_open hU_ne
    have hU_zero : s.prior.toMeasure U = 0 := by
      have h_subset : U ⊆ {ω' | ¬ pbar (s.m ω') ≤ pStar v S (s.m ω')} :=
        fun ω' hω' => not_le.mpr hω'
      have h_ae_zero : s.prior.toMeasure
          {ω' | ¬ pbar (s.m ω') ≤ pStar v S (s.m ω')} = 0 :=
        MeasureTheory.ae_iff.mp h_ae_at_m_prior
      exact MeasureTheory.measure_mono_null h_subset h_ae_zero
    exact hU_pos hU_zero
  intro y hy
  have hy_closure : y ∈ closure (Set.range s.m) := h_dense hy
  rw [mem_closure_iff_seq_limit] at hy_closure
  obtain ⟨z, hz_mem, hz_lim⟩ := hy_closure
  choose ω hω using hz_mem
  have h_z_eq_m : ∀ k, z k = s.m (ω k) := fun k => (hω k).symm
  have h_at_z : ∀ k, pbar (z k) ≤ pStar v S (z k) := by
    intro k
    rw [h_z_eq_m k]
    exact h_pbar_le_on_omega (ω k)
  have h_pbar_tendsto : Filter.Tendsto (fun k => pbar (z k)) Filter.atTop
      (𝓝 (pbar y)) :=
    (h_pbar_cont.tendsto y).comp hz_lim
  have h_pStar_tendsto : Filter.Tendsto (fun k => pStar v S (z k)) Filter.atTop
      (𝓝 (pStar v S y)) :=
    (h_pStar_cont.tendsto y).comp hz_lim
  exact le_of_tendsto_of_tendsto' h_pbar_tendsto h_pStar_tendsto h_at_z

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The formula-S envelope majorizes `v` for an optimal feasible joint.

For optimal `pi` with the structured prices `(pbar, q)` from `prices_for_moments_with_slackness`,
the formula-S envelope `pStar v S` (over `S = supp(π_X)`) majorizes `v` on `s.X`. -/
lemma optimality_implies_pStar_majorizes
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    (h_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    (h_dual : IsDualFeasible (s.composedValue v) (fun ω => pbar (s.m ω)))
    (h_value : dualObjective s.prior (fun ω => pbar (s.m ω))
        = dualValue (s.composedValue v) s.prior)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1))
    [h_prior_full : s.prior.toMeasure.IsOpenPosMeasure]
    (h_dense : s.X ⊆ closure (Set.range s.m)) :
    ∀ y ∈ s.X, v y ≤ pStar v (Prod.fst '' pi.toMeasure.support) y := by
  intro y hy
  have h_pbar_le_pStar : pbar y ≤ pStar v (Prod.fst '' pi.toMeasure.support) y :=
    MomentSetup.pbar_le_pStar_on_X s hm_lip hv_lip hv_diff hv_meas hv_bdd hpi h_opt h_struct
      h_dual h_value h_slack_pi h_dense y hy
  have h_v_le_pbar : v y ≤ pbar y := h_struct.pbar_ge_v y hy
  linarith

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The formula-S envelope realizes the active tangent for an optimal feasible joint.

For optimal `pi` with the structured prices `(pbar, q)` from `prices_for_moments_with_slackness`,
the formula-S envelope `pStar v S` (over `S = supp(π_X)`) realizes the active tangent at `pi`-a.e.
`(x, ω)`:

`pStar v S (m ω) = v x + (fderiv v x)(m ω − x)`   π-a.e. -/
lemma optimality_implies_active_ae
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) :
    ∀ᵐ p ∂pi.toMeasure,
      pStar v (Prod.fst '' pi.toMeasure.support) (s.m p.2)
        = v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
  set S : Set (EuclideanSpace ℝ (Fin n)) := Prod.fst '' pi.toMeasure.support with hS_def
  obtain ⟨K_pbar, h_pbar_lip⟩ := h_struct.pbar_lipschitz
  obtain ⟨K_q, h_K_q_nn, h_q_norm⟩ := h_struct.q_norm_bound
  have h_pbar_cont : Continuous pbar := h_pbar_lip.continuous
  have h_v_cont : Continuous v := hv_lip.continuous
  -- Confinement: π-ae, p.1 ∈ s.X.
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_fst_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    h_X_meas.preimage measurable_fst
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    have h_set_eq :
        {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
          = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
              ⁻¹' s.X)ᶜ := rfl
    rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_fst_meas]
    exact hpi.fst_supportsOn
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  obtain ⟨M_v, hM_v⟩ := hv_bdd
  have h_pbar_compact : IsCompact (pbar '' s.X) := s.X_compact.image h_pbar_cont
  obtain ⟨M_pbar, hM_pbar⟩ := h_pbar_compact.isBounded.exists_norm_le
  have h_pbar_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure :=
    (h_pbar_cont.comp continuous_fst).aestronglyMeasurable
  have h_v_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure :=
    (hv_meas.comp measurable_fst).aestronglyMeasurable
  have h_pbar_m_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure :=
    (h_pbar_cont.comp (s.m_continuous.comp continuous_snd)).aestronglyMeasurable
  have h_pbar_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_fst_aem M_pbar ?_
    filter_upwards [h_ae_p1] with p hp1
    have := hM_pbar (pbar p.1) ⟨p.1, hp1, rfl⟩
    simpa using this
  have h_v_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_v_fst_aem M_v ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]; exact hM_v _
  have h_pbar_m_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_m_aem M_pbar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hM_pbar (pbar (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  have h_inner_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        inner ℝ (q p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_q_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => q p.1) :=
      h_struct.q_measurable.comp measurable_fst
    have h_m_meas : Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
      (s.m_continuous.comp continuous_snd).measurable.sub measurable_fst
    exact (continuous_inner.measurable.comp (h_q_meas.prodMk h_m_meas)).aestronglyMeasurable
  have h_inner_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (q p.1) (s.m p.2 - p.1))
      pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_inner_aem (K_q * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_cs : ‖inner ℝ (q p.1) (s.m p.2 - p.1)‖
        ≤ ‖q p.1‖ * ‖s.m p.2 - p.1‖ := norm_inner_le_norm _ _
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    have h_diff_nn : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
    exact h_cs.trans (mul_le_mul (h_q_norm p.1) h_diff_norm h_diff_nn h_K_q_nn)
  -- Jensen along `m` for the convex envelope `pbar`.
  have h_pbar_lip_on : LipschitzOnWith K_pbar pbar s.X :=
    h_pbar_lip.lipschitzOnWith
  have h_jensen_pbar : ∫ p, pbar p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure :=
    MomentSetup.integral_fst_le_integral_m_of_convexOn s hpi h_struct.pbar_convex h_pbar_lip_on
  -- The martingale cross term vanishes.
  have h_cross_zero : ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 :=
    hpi.martingale_inner_measurable h_struct.q_measurable ⟨K_q, h_q_norm⟩
  have h_slack_integ : ∫ p, pbar (s.m p.2) ∂pi.toMeasure
      = ∫ p, v p.1 ∂pi.toMeasure
        + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := by
    have h_eq_ae : (fun p => pbar (s.m p.2))
        =ᵐ[pi.toMeasure]
          (fun p => v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) := by
      filter_upwards [h_slack_pi] with p hp using hp
    rw [MeasureTheory.integral_congr_ae h_eq_ae,
      MeasureTheory.integral_add h_v_fst_int h_inner_int]
  have h_pbar_ge_v_ae : ∀ᵐ p ∂pi.toMeasure, v p.1 ≤ pbar p.1 := by
    filter_upwards [h_ae_p1] with p hp1 using h_struct.pbar_ge_v _ hp1
  have h_int_v_le_int_pbar : ∫ p, v p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar p.1 ∂pi.toMeasure :=
    MeasureTheory.integral_mono_ae h_v_fst_int h_pbar_fst_int h_pbar_ge_v_ae
  have h_int_pbar_eq_v : ∫ p, pbar p.1 ∂pi.toMeasure = ∫ p, v p.1 ∂pi.toMeasure := by
    -- ∫ v ≤ ∫ pbar(p.1) ≤ ∫ pbar(m p.2) = ∫ v + 0 = ∫ v.
    have h_chain : ∫ p, pbar p.1 ∂pi.toMeasure ≤ ∫ p, v p.1 ∂pi.toMeasure := by
      calc ∫ p, pbar p.1 ∂pi.toMeasure
          ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure := h_jensen_pbar
        _ = ∫ p, v p.1 ∂pi.toMeasure
            + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := h_slack_integ
        _ = ∫ p, v p.1 ∂pi.toMeasure := by rw [h_cross_zero, add_zero]
    linarith
  have h_diff_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1) pi.toMeasure :=
    h_pbar_fst_int.sub h_v_fst_int
  have h_diff_nonneg : ∀ᵐ p ∂pi.toMeasure, 0 ≤ pbar p.1 - v p.1 := by
    filter_upwards [h_pbar_ge_v_ae] with p hp using by linarith
  have h_diff_int_zero : ∫ p, (pbar p.1 - v p.1) ∂pi.toMeasure = 0 := by
    rw [MeasureTheory.integral_sub h_pbar_fst_int h_v_fst_int, h_int_pbar_eq_v, sub_self]
  have h_active_ae_pbar : ∀ᵐ p ∂pi.toMeasure, pbar p.1 = v p.1 := by
    have h_diff_zero_ae : (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1)
        =ᵐ[pi.toMeasure] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_diff_int).mp
        h_diff_int_zero
    filter_upwards [h_diff_zero_ae] with p hp
    exact sub_eq_zero.mp hp
  have h_subgrad_ae :
      ∀ᵐ p ∂pi.toMeasure,
        (fderiv ℝ v p.1) (s.m p.2 - p.1) ≤ inner ℝ (q p.1) (s.m p.2 - p.1) := by
    filter_upwards [h_ae_p1, h_active_ae_pbar, h_slack_pi] with p hp1 hp_active hp_slack
    have h_subgrad : v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1)
        ≤ pbar (s.m p.2) :=
      HasMomentPrices.fderiv_isSubgradient_of_active s hv_diff h_struct
        p.1 hp1 hp_active.symm (s.m p.2) (s.m_mem_X p.2)
    rw [hp_slack] at h_subgrad
    linarith
  -- The `fderiv` cross term has zero integral.
  have h_fderiv_cross_zero :=
    feasibleJoint_fderiv_cross_zero s hpi hv_lip hv_diff
  have h_fd_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_joint :
        Continuous fun q : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
          (fderiv ℝ v q.1) q.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    have h_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) := by
      refine h_joint.comp (Continuous.prodMk continuous_fst ?_)
      exact (s.m_continuous.comp continuous_snd).sub continuous_fst
    exact h_cont.aestronglyMeasurable
  have h_fd_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_fd_aem ((L : ℝ) * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_op : ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := ContinuousLinearMap.le_opNorm _ _
    have h_fd_norm : ‖fderiv ℝ v p.1‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    calc ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := h_op
      _ ≤ (L : ℝ) * (R + R) :=
          mul_le_mul h_fd_norm h_diff_norm (norm_nonneg _) L.coe_nonneg
  -- The difference `δ = ⟨q, m−x⟩ − fderiv(m−x)` is a.e. nonneg with zero integral, hence a.e. zero.
  set δ : EuclideanSpace ℝ (Fin n) × Ω → ℝ := fun p =>
    inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1) with hδ_def
  have h_δ_int : MeasureTheory.Integrable δ pi.toMeasure := h_inner_int.sub h_fd_int
  have h_δ_nonneg : ∀ᵐ p ∂pi.toMeasure, 0 ≤ δ p := by
    filter_upwards [h_subgrad_ae] with p hp
    change 0 ≤ inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1)
    linarith
  have h_δ_int_zero : ∫ p, δ p ∂pi.toMeasure = 0 := by
    simp only [hδ_def]
    rw [MeasureTheory.integral_sub h_inner_int h_fd_int, h_cross_zero, h_fderiv_cross_zero,
      sub_zero]
  have h_δ_zero_ae : δ =ᵐ[pi.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_δ_nonneg h_δ_int).mp h_δ_int_zero
  have h_pbar_m_eq : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
    filter_upwards [h_slack_pi, h_δ_zero_ae] with p hp_slack hp_δ
    have hδp : inner ℝ (q p.1) (s.m p.2 - p.1) - (fderiv ℝ v p.1) (s.m p.2 - p.1) = 0 := hp_δ
    rw [hp_slack]
    linarith
  have h_pre_X_closed : IsClosed
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    s.X_compact.isClosed.preimage continuous_fst
  have h_pre_X_ae : (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
      ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff
      (h_pre_X_closed.measurableSet)).mpr hpi.fst_supportsOn
  have h_supp_sub_X :
      pi.toMeasure.support ⊆ (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω →
        EuclideanSpace ℝ (Fin n)) ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_X_closed h_pre_X_ae
  have hS_subX : S ⊆ s.X := by
    rintro x ⟨p, hp_supp, rfl⟩
    exact h_supp_sub_X hp_supp
  -- Every `x ∈ S` is active: `pbar x = v x`.
  -- The set `{p | pbar p.1 = v p.1}` is closed (continuity of `pbar - v`) and has full π-measure,
  -- so the support is contained in it, giving the activation of all `x ∈ S`.
  have h_active_set_closed : IsClosed
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0} := by
    have h_cont : Continuous
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1) :=
      (h_pbar_cont.comp continuous_fst).sub (h_v_cont.comp continuous_fst)
    exact isClosed_eq h_cont continuous_const
  have h_active_set_ae :
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0}
        ∈ MeasureTheory.ae pi.toMeasure := by
    filter_upwards [h_active_ae_pbar] with p hp
    linarith
  have h_supp_sub_active : pi.toMeasure.support ⊆
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0} :=
    MeasureTheory.Measure.support_subset_of_isClosed h_active_set_closed h_active_set_ae
  have hS_active : ∀ x ∈ S, pbar x = v x := by
    rintro x ⟨p, hp_supp, rfl⟩
    have : pbar p.1 - v p.1 = 0 := h_supp_sub_active hp_supp
    linarith
  -- The empty-S case is impossible: π is a probability measure, so supp π is
  -- nonempty, hence S = Prod.fst '' supp π is nonempty.
  have hS_nonempty : S.Nonempty := by
    obtain ⟨p, hp⟩ :=
      MeasureTheory.Measure.nonempty_support (μ := pi.toMeasure)
        (MeasureTheory.IsProbabilityMeasure.ne_zero pi.toMeasure)
    exact ⟨p.1, p, hp, rfl⟩
  have h_pStar_le_pbar : ∀ y ∈ s.X, pStar v S y ≤ pbar y := by
    intro y hy
    unfold pStar
    refine csSup_le (hS_nonempty.image _) ?_
    rintro _ ⟨x, hxS, rfl⟩
    have hx_in_X : x ∈ s.X := hS_subX hxS
    have hx_active : v x = pbar x := (hS_active x hxS).symm
    exact HasMomentPrices.fderiv_isSubgradient_of_active s hv_diff h_struct x hx_in_X hx_active y hy
  have h_supp_ae : ∀ᵐ p ∂pi.toMeasure, p ∈ pi.toMeasure.support :=
    MeasureTheory.Measure.support_mem_ae
  filter_upwards [h_supp_ae, h_pbar_m_eq, h_ae_p1] with p hp_supp hp_eq hp1
  -- Lower bound: pStar ≥ v(p.1) + (fderiv v p.1)(m p.2 - p.1) since p.1 ∈ S.
  have hp1_in_S : p.1 ∈ S := ⟨p, hp_supp, rfl⟩
  have h_image_ne :
      ((fun x : EuclideanSpace ℝ (Fin n) =>
          v x + (fderiv ℝ v x) (s.m p.2 - x)) '' S).Nonempty :=
    ⟨_, ⟨p.1, hp1_in_S, rfl⟩⟩
  have h_image_bdd : BddAbove
      ((fun x : EuclideanSpace ℝ (Fin n) =>
          v x + (fderiv ℝ v x) (s.m p.2 - x)) '' S) :=
    pStar_image_bddAbove s hv_diff hS_subX (s.m p.2)
  have h_pStar_ge : v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) ≤ pStar v S (s.m p.2) := by
    unfold pStar
    exact le_csSup h_image_bdd ⟨p.1, hp1_in_S, rfl⟩
  -- Upper bound: pStar (m p.2) ≤ pbar (m p.2) = v p.1 + (fderiv v p.1)(m p.2 - p.1).
  have h_pStar_le : pStar v S (s.m p.2) ≤ pbar (s.m p.2) :=
    h_pStar_le_pbar (s.m p.2) (s.m_mem_X p.2)
  have h_le_eq : pStar v S (s.m p.2) ≤ v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
    rw [hp_eq] at h_pStar_le; exact h_pStar_le
  linarith

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
