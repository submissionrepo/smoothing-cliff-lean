/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.JointPosteriorBridge
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.PricesForMoments
public import Econlib.Probability.ProbDist.Borel
public import Mathlib.MeasureTheory.Measure.Support

/-!
# The formula-S envelope, condition (M), and slackness

This file defines the formula-S envelope `pStar v S` and **condition (M)** for differentiable
moment persuasion, then augments the canonical dual price `pbar` with the active-hyperplane
equality holding at any optimal feasible joint, the complementary-slackness identity.

The formula-S envelope is `pStar v S y := sSup { v(x) + ⟨∇v(x), y - x⟩ : x ∈ S }`, the supremum of
the tangent hyperplanes to `v` over a set `S`. Condition (M) packages a feasible joint together
with a candidate active set on which `pStar v S` majorizes `v` and the active-tangent identity
holds prior-a.e. The structural follow-ups live in `OptimalDualPriceStructural`,
`OptimalDualPriceForward`, and `OptimalDualPriceCanonical`.

## Main definitions

* `pStar` — the formula-S envelope.
* `ConditionM` — the active-tangent identity along an active set.

## Main statements

* `ConditionM.activeSet_nonempty` — the active set of a condition (M) quadruple is non-empty.
* `prices_for_moments_with_slackness` — the canonical dual price together with the
  active-hyperplane equality at any optimal joint.
* `HasMomentPrices.fderiv_isSubgradient_of_active` — at an active point, `∇v` is a subgradient of
  `pbar` relative to `s.X`.
* `MomentSetup.integral_fst_le_integral_m_of_convexOn` — Jensen-style inequality along the moment
  map for a feasible joint.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorems 5–7.

## Tags

persuasion, moment persuasion, dual price, envelope
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

/-! ## Formula (S): The differentiable upper envelope -/

/-- Low-level upper-envelope helper: The supremum of the tangent hyperplanes to `v` over a set `S`,
as a function of the moment vector `y`.

`pStar v S y = sSup { v(x) + ⟨∇v(x), y − x⟩ : x ∈ S }`.

This is the raw convex-analysis primitive, deliberately total over all `S`: For `S = ∅` it returns
`sSup ∅ = 0`, which is what makes `pStar_convexOn`/`pStar_lipschitzWith` hold unconditionally. The
semantic formula-S object is `ConditionM`, whose active set is always non-empty
(`ConditionM.activeSet_nonempty`); reach for that rather than feeding a bare `S` here. -/
noncomputable def pStar
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => v x + (fderiv ℝ v x) (y - x)) '' S)

/-! ## Condition (M) -/

/-- Condition (M). Given a `C¹` value function `v`, a joint `pi`, and a candidate active set
`S ⊆ X`, the quadruple `(pi, v, S)` satisfies condition (M) when:

* `pi` is a feasible joint, `pi ∈ Π(μ₀)` (its `Ω`-marginal is the prior, its `X`-marginal lives in
  `X`, and it satisfies the martingale/mean-preserving constraint, all packaged by
  `feasibleJoint`);
* `pStar v S` majorizes `v` on `X` (the global affine-minorant property);
* the supremum in `pStar v S (m ω)` is attained at the joint's `x`-coordinate for `pi`-a.e.
  `(x, ω)`;
* `S` equals the projection of the support of `pi` onto the `X`-coordinate.

These pieces together say "(`pi`, `S`) tile `Ω` by tangent hyperplanes to `v`" along a feasible
joint. The feasibility field makes the documented `pi ∈ Π(μ₀)` precondition part of the type, so a
holder of `ConditionM` never has to carry feasibility as a separate hypothesis. -/
structure ConditionM (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (S : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  /-- `pi` is a feasible joint: Its `Ω`-marginal is the prior, its `X`-marginal lives in `X`, and
  it satisfies the martingale (mean-preserving) constraint. -/
  feasible : pi ∈ feasibleJoint s
  /-- `pStar v S` is a global majorant of `v` on `X`. -/
  pStar_majorizes : ∀ y ∈ s.X, v y ≤ pStar v S y
  /-- For `pi`-a.e. `(x, ω)`, the active tangent in `pStar v S` is at `x`. -/
  active_ae : ∀ᵐ p ∂pi.toMeasure,
    pStar v S (s.m p.2) = v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1)
  /-- `S` equals the projection support of `pi` onto `X`. -/
  S_eq_support : S = Prod.fst '' pi.toMeasure.support

variable {s : MomentSetup Ω n} {v : EuclideanSpace ℝ (Fin n) → ℝ}
  {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
  {S : Set (EuclideanSpace ℝ (Fin n))}

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] [CompactSpace Ω] in
/-- The active set of a `ConditionM` quadruple is non-empty. This is the semantic guarantee the
documented Formula-S precondition needs: `S` is the `X`-projection of the support of the
probability measure `pi`, which is non-empty because `pi` is a probability measure (hence
non-zero). Consumers should use this instead of re-deriving non-emptiness from `S_eq_support`
inline. -/
theorem ConditionM.activeSet_nonempty (hM : ConditionM s v pi S) : S.Nonempty := by
  rw [hM.S_eq_support]
  exact (MeasureTheory.Measure.nonempty_support
    (MeasureTheory.IsProbabilityMeasure.ne_zero pi.toMeasure)).image _

/-! ## Slackness for structured moment prices

The results in this section package the canonical dual prices together with active-hyperplane
equalities for optimal feasible joints.  Like `MomentSetup.exists_hasMomentPrices`, they assume
Lipschitzness of the moment coordinates, Lipschitzness/measurability/boundedness/upper
semicontinuity of `v`, measurability and upper semicontinuity of the composed value, and
Lipschitzness of the posterior check on `X`, with the `MomentSetup` surjectivity field
`moment_surjOn_X` in force; they do not require the open-positive prior or moment-image density of
the differentiable-case results. -/

/-- Structured moment prices satisfy complementary slackness.

For an `L`-Lipschitz USC `v`, the structured prices `(p̄, q)` from
`MomentSetup.exists_hasMomentPrices` are `HasMomentPrices`, dual-feasible, and dual-optimal
(`dualObjective = dualValue`), and additionally satisfy: For any optimal joint `π`, the active
hyperplane equality

`p̄(m(ω)) = v(x) + ⟨q(x), m(ω) − x⟩`

holds for `π`-a.e. `(x, ω)`.

The full hypothesis list (all explicit below): Lipschitzness of the moment coordinates (`hm_lip`);
Lipschitzness, measurability, boundedness, and upper semicontinuity of `v`; measurability and upper
semicontinuity of the composed value; and Lipschitzness of the posterior check on `X`
(`h_pcheck_lip`). The `MomentSetup` surjectivity field `moment_surjOn_X` is in force as part of
`s`. -/
theorem prices_for_moments_with_slackness
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    (hv_usc : UpperSemicontinuous v)
    (hV_meas : Measurable (s.composedValue v))
    (hV_usc : UpperSemicontinuous (s.composedValue v))
    (h_pcheck_lip : ∀ {p : Ω → ℝ} {K : NNReal},
      LipschitzWith K p →
        LipschitzOnWith K (convexRoof s p) s.X) :
    ∃ (pbar : EuclideanSpace ℝ (Fin n) → ℝ)
      (q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      HasMomentPrices s v L pbar q ∧
      IsDualFeasible (s.composedValue v) (fun ω => pbar (s.m ω)) ∧
      dualObjective s.prior (fun ω => pbar (s.m ω))
        = dualValue (s.composedValue v) s.prior ∧
      (∀ pi ∈ feasibleJoint s,
        (∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v) →
        ∀ᵐ p ∂pi.toMeasure,
          pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) := by
  have h_post_mem : ∀ μ : ProbDist Ω, s.posteriorMoment μ ∈ s.X := by
    intro μ
    unfold MomentSetup.posteriorMoment
    refine Convex.integral_mem s.X_convex s.X_compact.isClosed ?_ (s.m_integrable μ)
    exact ae_of_all _ s.m_mem_X
  obtain ⟨pbar, q, h_struct, h_dual, h_value⟩ :=
    MomentSetup.exists_hasMomentPrices s hm_lip hv hv_meas hv_bdd hv_usc hV_meas hV_usc
      h_post_mem h_pcheck_lip
  refine ⟨pbar, q, h_struct, h_dual, h_value, ?_⟩
  intro pi hpi h_opt
  obtain ⟨K_pbar, h_pbar_lip⟩ := h_struct.pbar_lipschitz
  obtain ⟨K_q, h_K_q_nn, h_q_norm⟩ := h_struct.q_norm_bound
  have h_pbar_cont : Continuous pbar := h_pbar_lip.continuous
  set Δ : EuclideanSpace ℝ (Fin n) × Ω → ℝ :=
    fun p => pbar (s.m p.2) - v p.1 - inner ℝ (q p.1) (s.m p.2 - p.1) with hΔ_def
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
      s.X_compact.isClosed.measurableSet
    have h_meas : MeasurableSet
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
      h_X_meas.preimage measurable_fst
    have h_set_eq :
        {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
          = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
              ⁻¹' s.X)ᶜ := rfl
    rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_meas]
    exact hpi.fst_supportsOn
  have h_Δ_nonneg_ae : ∀ᵐ p ∂pi.toMeasure, 0 ≤ Δ p := by
    filter_upwards [h_ae_p1] with p hp1
    have h_envelope : pbar (s.m p.2) =
        sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
          v x + inner ℝ (q x) (s.m p.2 - x)) '' s.X) :=
      h_struct.pbar_envelope (s.m p.2) (s.m_mem_X p.2)
    have h_image_ne : ((fun x : EuclideanSpace ℝ (Fin n) =>
        v x + inner ℝ (q x) (s.m p.2 - x)) '' s.X).Nonempty :=
      ⟨_, ⟨p.1, hp1, rfl⟩⟩
    have h_image_bdd : BddAbove ((fun x : EuclideanSpace ℝ (Fin n) =>
        v x + inner ℝ (q x) (s.m p.2 - x)) '' s.X) := by
      obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
      obtain ⟨M_v, hM_v⟩ := hv_bdd
      refine ⟨M_v + K_q * (R + R), ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have h_v : v x ≤ M_v := (abs_le.mp (hM_v x)).2
      have h_inner_bdd : inner ℝ (q x) (s.m p.2 - x) ≤ K_q * (R + R) := by
        have h_cs : ‖inner ℝ (q x) (s.m p.2 - x)‖ ≤ ‖q x‖ * ‖s.m p.2 - x‖ :=
          norm_inner_le_norm _ _
        have h_q_norm : ‖q x‖ ≤ K_q := h_q_norm x
        have h_diff_norm : ‖s.m p.2 - x‖ ≤ R + R := by
          calc ‖s.m p.2 - x‖
              ≤ ‖s.m p.2‖ + ‖x‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hx)
        have h_diff_nn : 0 ≤ ‖s.m p.2 - x‖ := norm_nonneg _
        have h_le_prod : ‖q x‖ * ‖s.m p.2 - x‖ ≤ K_q * (R + R) :=
          mul_le_mul h_q_norm h_diff_norm h_diff_nn h_K_q_nn
        rw [Real.norm_eq_abs] at h_cs
        exact (abs_le.mp (h_cs.trans h_le_prod)).2
      linarith
    have h_le : v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1) ≤ pbar (s.m p.2) := by
      rw [h_envelope]
      exact le_csSup h_image_bdd ⟨p.1, hp1, rfl⟩
    linarith
  have h_pbar_m_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure :=
    (h_pbar_cont.comp (s.m_continuous.comp continuous_snd)).aestronglyMeasurable
  have h_v_p_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure := by
    exact (hv_meas.comp measurable_fst).aestronglyMeasurable
  have h_inner_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        inner ℝ (q p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_q_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => q p.1) :=
      h_struct.q_measurable.comp measurable_fst
    have h_m_meas : Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
      (s.m_continuous.comp continuous_snd).measurable.sub measurable_fst
    exact (continuous_inner.measurable.comp (h_q_meas.prodMk h_m_meas)).aestronglyMeasurable
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have h_pbar_compact : IsCompact (pbar '' s.X) := s.X_compact.image h_pbar_cont
  obtain ⟨M_pbar, hM_pbar⟩ := h_pbar_compact.isBounded.exists_norm_le
  have ⟨M_v, hM_v⟩ : ∃ M, ∀ x, |v x| ≤ M := hv_bdd
  have h_pbar_m_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_m_aem M_pbar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hM_pbar (pbar (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  have h_v_p_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_v_p_aem M_v ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have h := hM_v p.1
    rwa [Real.norm_eq_abs]
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
  -- `Δ = pbar∘m - v∘fst - ⟨q, m - fst⟩` is integrable as a difference of the three pieces.
  have h_Δ_int : MeasureTheory.Integrable Δ pi.toMeasure :=
    (h_pbar_m_int.sub h_v_p_int).sub h_inner_int
  have h_int_eq_zero : ∫ p, Δ p ∂pi.toMeasure = 0 := by
    have h_split : ∫ p, Δ p ∂pi.toMeasure
        = ∫ p, pbar (s.m p.2) ∂pi.toMeasure - ∫ p, v p.1 ∂pi.toMeasure
          - ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := by
      have h₁ : ∫ p, pbar (s.m p.2) - v p.1 - inner ℝ (q p.1) (s.m p.2 - p.1)
            ∂pi.toMeasure
          = ∫ p, (pbar (s.m p.2) - v p.1) ∂pi.toMeasure
            - ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure :=
        MeasureTheory.integral_sub (h_pbar_m_int.sub h_v_p_int) h_inner_int
      have h₂ : ∫ p, (pbar (s.m p.2) - v p.1) ∂pi.toMeasure
          = ∫ p, pbar (s.m p.2) ∂pi.toMeasure - ∫ p, v p.1 ∂pi.toMeasure :=
        MeasureTheory.integral_sub h_pbar_m_int h_v_p_int
      simp only [hΔ_def]
      rw [h₁, h₂]
    have h_marg : ∫ p, pbar (s.m p.2) ∂pi.toMeasure
        = ∫ ω, pbar (s.m ω) ∂s.prior.toMeasure := by
      have hmarg := hpi.marginal
      have h_aem : AEStronglyMeasurable (fun ω => pbar (s.m ω))
          ((ProbDist.map pi Prod.snd measurable_snd).toMeasure) :=
        (h_pbar_cont.comp s.m_continuous).aestronglyMeasurable
      have hexp := ProbDist.expect_map pi Prod.snd measurable_snd
        (fun ω => pbar (s.m ω)) h_aem
      rw [hmarg] at hexp
      exact hexp.symm
    have h_pbar_eq_env : ∫ ω, pbar (s.m ω) ∂s.prior.toMeasure
        = dualValue (s.composedValue v) s.prior := by
      have := h_value
      unfold dualObjective ProbDist.expect at this
      exact this
    have h_bridge : momentPrimal s v
        = concaveClosure (s.composedValue v) s.prior :=
      momentPrimal_eq_concaveClosure_composedValue s hm_lip hv hv_bdd hv_usc
    have hL_nn : (0 : ℝ) ≤ (L : ℝ) * Real.sqrt n :=
      mul_nonneg L.coe_nonneg (Real.sqrt_nonneg _)
    have hV_lip : Econlib.Optimization.OptimalTransport.IsKRLipschitz (s.composedValue v)
        ((L : ℝ) * Real.sqrt n) :=
      composedValue_isKRLipschitz_of_lipschitz s hm_lip hv
    have hV_bdd' : ∃ M, ∀ μ, |s.composedValue v μ| ≤ M := by
      obtain ⟨M, hM⟩ := hv_bdd; exact ⟨M, fun μ => hM _⟩
    have h_no_gap : concaveClosure (s.composedValue v) s.prior
        = dualValue (s.composedValue v) s.prior :=
      (strongDuality_of_isKRLipschitz hL_nn hV_meas hV_bdd' hV_usc hV_lip s.prior).1
    have h_inner_cross : ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 :=
      hpi.martingale_inner_measurable h_struct.q_measurable ⟨K_q, h_q_norm⟩
    rw [h_split, h_marg, h_pbar_eq_env, h_opt, h_bridge, h_no_gap, h_inner_cross]
    ring
  have h_Δ_ae_zero : Δ =ᵐ[pi.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_Δ_nonneg_ae h_Δ_int).mp
      h_int_eq_zero
  filter_upwards [h_Δ_ae_zero] with p hΔ_p
  show pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)
  have : pbar (s.m p.2) - v p.1 - inner ℝ (q p.1) (s.m p.2 - p.1) = 0 := hΔ_p
  linarith

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- **Gradient subgradient inequality.**

When `v` is `C¹` and `pbar` is convex on the convex compact `s.X` with `pbar ≥ v`, then at every
active `x ∈ s.X` (where `v(x) = pbar(x)`), the Fréchet derivative `fderiv ℝ v x` is a subgradient
of `pbar` at `x` relative to `s.X`:

`v(x) + (fderiv ℝ v x) (y − x) ≤ pbar(y)` for every `y ∈ s.X`.

This is weaker than a pointwise identity `q x = fderiv ℝ v x`; the subdifferential of `pbar` can
have multiple elements. -/
lemma HasMomentPrices.fderiv_isSubgradient_of_active
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv_C1 : ContDiff ℝ 1 v)
    (h_struct : HasMomentPrices s v L pbar q) :
    ∀ x ∈ s.X, v x = pbar x →
      ∀ y ∈ s.X, v x + (fderiv ℝ v x) (y - x) ≤ pbar y := by
  intro x hx hx_active y hy
  have hv_diff : Differentiable ℝ v := hv_C1.differentiable one_ne_zero
  have hv_fderiv : HasFDerivAt v (fderiv ℝ v x) x := (hv_diff x).hasFDerivAt
  have hpbar_convex : ConvexOn ℝ s.X pbar := h_struct.pbar_convex
  have hpbar_ge_v : ∀ z ∈ s.X, v z ≤ pbar z := h_struct.pbar_ge_v
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • (y - x) with hγ_def
  have hγ0 : γ 0 = x := by simp [hγ_def]
  have hγ_deriv : HasDerivAt γ (y - x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • (y - x)) (y - x) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - x)
    simpa using (hasDerivAt_const (0 : ℝ) x).add h1
  have h_comp_deriv : HasDerivAt (v ∘ γ) ((fderiv ℝ v x) (y - x)) 0 := by
    have h_v_fd : HasFDerivAt v (fderiv ℝ v x) (γ 0) := hγ0 ▸ hv_fderiv
    exact h_v_fd.comp_hasDerivAt 0 hγ_deriv
  have h_slope_right :
      Filter.Tendsto (fun t : ℝ => t⁻¹ • ((v ∘ γ) (0 + t) - (v ∘ γ) 0)) (𝓝[Ioi 0] 0)
        (𝓝 ((fderiv ℝ v x) (y - x))) :=
    h_comp_deriv.tendsto_slope_zero_right
  have h_slope_right' : Filter.Tendsto (fun t : ℝ => (v (γ t) - v x) / t) (𝓝[Ioi 0] 0)
      (𝓝 ((fderiv ℝ v x) (y - x))) := by
    refine h_slope_right.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t _
    simp [Function.comp_apply, hγ0, smul_eq_mul, div_eq_inv_mul, zero_add]
  have h_eventually : ∀ᶠ t in 𝓝[Ioi 0] 0,
      (v (γ t) - v x) / t ≤ pbar y - v x := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (zero_lt_one : (0:ℝ) < 1)] with t ht_lt_1 ht_pos
    have ht_pos' : (0:ℝ) < t := ht_pos
    have ht_lt_1' : t < 1 := ht_lt_1
    have hγt_eq : γ t = (1 - t) • x + t • y := by
      simp only [hγ_def, smul_sub, sub_smul, one_smul]
      abel
    have hγt_in : γ t ∈ s.X := by
      rw [hγt_eq]
      exact s.X_convex hx hy (by linarith) ht_pos'.le (by ring)
    have h_conv : pbar (γ t) ≤ (1 - t) * pbar x + t * pbar y := by
      rw [hγt_eq]
      have h1 : (0:ℝ) ≤ 1 - t := by linarith
      have h_sum : (1 - t) + t = 1 := by ring
      have h_step := hpbar_convex.2 hx hy h1 ht_pos'.le h_sum
      simpa [smul_eq_mul] using h_step
    have hv_le : v (γ t) ≤ pbar (γ t) := hpbar_ge_v _ hγt_in
    have h_chain : v (γ t) - v x ≤ t * (pbar y - v x) := by
      have h_step1 : v (γ t) ≤ (1 - t) * pbar x + t * pbar y := le_trans hv_le h_conv
      have h_step2 : pbar x = v x := hx_active.symm
      nlinarith [h_step1, h_step2]
    rw [div_le_iff₀ ht_pos']
    linarith
  haveI : (𝓝[Ioi (0:ℝ)] (0:ℝ)).NeBot := nhdsGT_neBot 0
  have h_limit_le : (fderiv ℝ v x) (y - x) ≤ pbar y - v x :=
    le_of_tendsto h_slope_right' h_eventually
  linarith

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- **Jensen-style inequality on feasible joints.**

For any convex function `φ : ℝⁿ → ℝ` Lipschitz on `X`, and any feasible joint `π ∈ Π(μ₀)`, the
marginal-on-`X` integral of `φ` is dominated by the integral of `φ(m(ω))`:

`∫ φ(x) dπ(x, ω) ≤ ∫ φ(m(ω)) dπ(x, ω)`.

This is Jensen's inequality applied conditionally on `x`: The disintegration of `π` over its
`X`-marginal yields the conditional law `π(· | x)` whose `m`-mean equals `x` by the martingale
condition, and convexity of `φ` gives the bound. The inequality runs in the direction
`expect ≤ apply` rather than the usual `apply ≤ expect`, because the martingale condition forces
`E[m | x] = x` and hence `φ(x) = φ(E[m | x]) ≤ E[φ(m) | x]`. -/
lemma MomentSetup.integral_fst_le_integral_m_of_convexOn
    (s : MomentSetup Ω n)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)} (hpi : pi ∈ feasibleJoint s)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ_conv : ConvexOn ℝ s.X φ)
    {Lφ : NNReal} (hφ_lip : LipschitzOnWith Lφ φ s.X) :
    ∫ p, φ p.1 ∂pi.toMeasure ≤ ∫ p, φ (s.m p.2) ∂pi.toMeasure := by
  have hLφ_nn : 0 ≤ (Lφ : ℝ) := Lφ.coe_nonneg
  have h_lip_real : LipschitzOnWith ((Lφ : ℝ).toNNReal) φ s.X := by
    rw [Real.toNNReal_coe]; exact hφ_lip
  obtain ⟨g, hg_meas, hg_bound, hg_sub⟩ :=
    ConvexOn.exists_measurable_subgradient_selection
      hLφ_nn s.X_compact s.X_convex s.X_interior hφ_conv h_lip_real
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
  have h_subgrad_ae : ∀ᵐ p ∂pi.toMeasure,
      φ p.1 + inner ℝ (g p.1) (s.m p.2 - p.1) ≤ φ (s.m p.2) := by
    filter_upwards [h_ae_p1] with p hp1
    exact hg_sub p.1 hp1 (s.m p.2) (s.m_mem_X p.2)
  have h_cross : ∫ p, inner ℝ (g p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 :=
    hpi.martingale_inner_measurable hg_meas ⟨(Lφ : ℝ), hg_bound⟩
  have h_φ_p1_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1) pi.toMeasure := by
    have h_compact_set : IsCompact
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) := by
      have h_eq : ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
          ⁻¹' s.X) = s.X ×ˢ (Set.univ : Set Ω) := by ext; simp
      rw [h_eq]
      exact s.X_compact.prod isCompact_univ
    have h_cont_on : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1)
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
      hφ_lip.continuousOn.comp continuous_fst.continuousOn (fun _ hp => hp)
    have h_aem_restrict :
        AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1)
          (pi.toMeasure.restrict
            ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X)) :=
      h_cont_on.aestronglyMeasurable_of_isCompact h_compact_set h_fst_meas
    have h_restrict_eq :
        pi.toMeasure.restrict
            ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X)
          = pi.toMeasure :=
      MeasureTheory.Measure.restrict_eq_self_of_ae_mem h_ae_p1
    rw [← h_restrict_eq]
    exact h_aem_restrict
  have h_φm_cont : Continuous (fun ω : Ω => φ (s.m ω)) :=
    hφ_lip.continuousOn.comp_continuous s.m_continuous s.m_mem_X
  have h_φ_m_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ (s.m p.2)) pi.toMeasure :=
    (h_φm_cont.comp continuous_snd).aestronglyMeasurable
  have hφ_compact : IsCompact (φ '' s.X) :=
    s.X_compact.image_of_continuousOn hφ_lip.continuousOn
  obtain ⟨Mφ, hMφ⟩ := hφ_compact.isBounded.exists_norm_le
  have h_φ_p1_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_φ_p1_aem Mφ ?_
    filter_upwards [h_ae_p1] with p hp1
    have := hMφ (φ p.1) ⟨p.1, hp1, rfl⟩
    simpa using this
  have h_φ_m_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_φ_m_aem Mφ ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hMφ (φ (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have h_cross_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (g p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_aem : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (g p.1) (s.m p.2 - p.1))
        pi.toMeasure := by
      have h_q_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => g p.1) :=
        hg_meas.comp measurable_fst
      have h_diff_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
        (s.m_continuous.measurable.comp measurable_snd).sub measurable_fst
      exact (continuous_inner.measurable.comp
        (h_q_meas.prodMk h_diff_meas)).aestronglyMeasurable
    refine MeasureTheory.Integrable.of_bound h_aem ((Lφ : ℝ) * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_cs : ‖inner ℝ (g p.1) (s.m p.2 - p.1)‖ ≤ ‖g p.1‖ * ‖s.m p.2 - p.1‖ :=
      norm_inner_le_norm _ _
    have h_g_norm : ‖g p.1‖ ≤ (Lφ : ℝ) := hg_bound p.1
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    have h_diff_nn : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
    exact h_cs.trans (mul_le_mul h_g_norm h_diff_norm h_diff_nn Lφ.coe_nonneg)
  have h_int_le : ∫ p, φ p.1 + inner ℝ (g p.1) (s.m p.2 - p.1) ∂pi.toMeasure
      ≤ ∫ p, φ (s.m p.2) ∂pi.toMeasure :=
    MeasureTheory.integral_mono_ae (h_φ_p1_int.add h_cross_int) h_φ_m_int h_subgrad_ae
  have h_split : ∫ p, φ p.1 + inner ℝ (g p.1) (s.m p.2 - p.1) ∂pi.toMeasure
      = ∫ p, φ p.1 ∂pi.toMeasure
        + ∫ p, inner ℝ (g p.1) (s.m p.2 - p.1) ∂pi.toMeasure :=
    MeasureTheory.integral_add h_φ_p1_int h_cross_int
  rw [h_split, h_cross, add_zero] at h_int_le
  exact h_int_le

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
