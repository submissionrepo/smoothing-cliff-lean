/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.KernelReshuffle
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.MeasurableChoquet
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.SupportCell
public import Econlib.Probability.ProbDist.Borel

/-!
# Auxiliary minimizers and cell-conditional data

This file establishes the existence of auxiliary-minimal feasible joints for the moment-persuasion
problem, and provides the structures (`SameCellCompetitor`, `CellConditionalData`) that package
cell-conditional data for the extreme-point structure theorem.

## Main definitions

* `IsAuxiliaryMinimizer`: A primal-optimal feasible joint that minimizes the average squared norm
  of the posterior moment among all primal-optimal feasible joints.
* `SameCellCompetitor`: A probability measure competing with a cell-conditional measure, matching
  its Ω-marginal and satisfying the local martingale identity within the contact graph.
* `CellConditionalData`: The conditional measure on a contact cell together with its support,
  martingale, auxiliary minimality, and barycentric decomposability properties.

## Main statements

* `pos_cell_fst_ball_of_mem_Sx`: Positive cell-conditional first-marginal mass in any open ball
  around a point of `Sx`.
* `exists_auxiliary_minimizer`: Existence of a primal-optimal, auxiliary-minimal feasible joint
  together with an active-set witnessing `ConditionM`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900).

## Tags

persuasion, moment persuasion, extreme points, auxiliary minimization
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}
variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

/-- `pi` is auxiliary-minimal if, among all primal-optimal feasible joints, it minimizes the
average squared norm of the posterior moment. -/
def IsAuxiliaryMinimizer (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) : Prop :=
  pi ∈ feasibleJoint s ∧
  (∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v) ∧
  ∀ pi' ∈ feasibleJoint s,
    (∫ p, v p.1 ∂pi'.toMeasure = momentPrimal s v) →
    ∫ p, ‖p.1‖^2 ∂pi.toMeasure ≤ ∫ p, ‖p.1‖^2 ∂pi'.toMeasure

/-! ### Cell-conditional interfaces -/

/-- A same-cell competitor to a cell-conditional measure `rho`: A probability measure `rho'` whose
Ω-marginal matches `rho`, whose first marginal is X-supported, that satisfies the local martingale
identity, and whose support is contained in the contact graph `{(x, ω) : s.m ω ∈ Γ_x}`. -/
structure SameCellCompetitor
    (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (rho rho' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) : Prop where
  /-- Ω-marginal preserved. -/
  same_snd_marginal :
    (ProbDist.map rho' Prod.snd measurable_snd).toMeasure =
      (ProbDist.map rho Prod.snd measurable_snd).toMeasure
  /-- First marginal supported on `s.X`. -/
  fst_supportsOn_X :
    rho'.toMeasure ((Prod.fst ⁻¹' s.X)ᶜ) = 0
  /-- Local martingale identity (vector form). -/
  local_martingale :
    ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂rho'.toMeasure = 0
  /-- Support lies in the contact graph: `s.m ω ∈ Γ_x` for `rho'`-a.e. `(x, ω)`. -/
  contact_support :
    ∀ᵐ p ∂rho'.toMeasure, s.m p.2 ∈ Gamma_x s v S p.1

/-- Cell-conditional data at a moment `x₀`: The conditional measure `rho := π(· | relint(Γ_{x₀}))`
on `ℝⁿ × Ω` together with its support, martingale, auxiliary minimality, and barycentric
decomposability properties. -/
structure CellConditionalData
    (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x₀ : EuclideanSpace ℝ (Fin n)) where
  /-- The cell-conditional probability measure `π(· | relint(Γ_{x₀}))`. -/
  rho : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)
  /-- State-side support in `Γ_{x₀}`. -/
  m_state_mem_cell :
    ∀ᵐ p ∂rho.toMeasure,
      s.m p.2 ∈ Gamma_x s v S x₀
  /-- First-marginal support inside `Sx_{x₀}`. -/
  fst_support_subset_Sx :
    (ProbDist.map rho Prod.fst measurable_fst).toMeasure.support ⊆
      Sx s v S pi x₀
  /-- Pointwise neighborhood positivity on `Sx_{x₀}`. -/
  fst_marginal_pos_on_Sx :
    ∀ {y : EuclideanSpace ℝ (Fin n)}, y ∈ Sx s v S pi x₀ →
      ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, U ∈ nhds y →
        0 < (ProbDist.map rho Prod.fst measurable_fst).toMeasure U
  /-- Local martingale identity in vector form. -/
  local_martingale :
    ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂rho.toMeasure = 0
  /-- Cell-local auxiliary minimality. -/
  local_aux_min :
    ∀ rho' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
      SameCellCompetitor s v S x₀ rho rho' →
        ∫ p, ‖p.1‖ ^ 2 ∂rho.toMeasure ≤
          ∫ p, ‖p.1‖ ^ 2 ∂rho'.toMeasure
  /-- Conditional barycentric decomposability.

  For every non-extreme point `x' ∈ Sx_{x₀} \ ext(closure(conv(Sx_{x₀})))`, there exists a nonzero
  finite sub-measure `α` of the cell-conditional first marginal
  `ν_{cell} := (rho.map Prod.fst).toMeasure` satisfying

  * `α ≤ ν_{cell}` (sub-measure of the cell-conditional first marginal),
  * `α (Sx_{x₀})ᶜ = 0` (concentrated on `Sx_{x₀}`),
  * `α {x'} = 0` (no atom at the bad point itself),
  * `∫ z dα(z) = α(univ).toReal • x'` (the barycenter of `α / α(univ)` is `x'`). -/
  barycentric_decomposability :
    ∀ x' ∈ Sx s v S pi x₀,
      x' ∉ Set.extremePoints ℝ (closure (convexHull ℝ (Sx s v S pi x₀))) →
        ∃ α : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
          α ≠ 0 ∧
          α ≤ (ProbDist.map rho Prod.fst measurable_fst).toMeasure ∧
          α ((Sx s v S pi x₀)ᶜ) = 0 ∧
          α {x'} = 0 ∧
          ∫ z, z ∂α = (α Set.univ).toReal • x'

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The cell-conditional first-marginal measure has positive mass on every open ball around a point
of `Sx`. Per-cell analog of `pos_piX_ball_of_mem_Sx`. -/
lemma pos_cell_fst_ball_of_mem_Sx
    {s : MomentSetup Ω n}
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (cell : CellConditionalData s v S pi x₀)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Sx s v S pi x₀)
    {δ : ℝ} (hδ : 0 < δ) :
    0 < (ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure
          (Metric.ball y δ) :=
  cell.fst_marginal_pos_on_Sx hy (Metric.ball_mem_nhds y hδ)

/-- For a `C¹` value function `v` and a suitable prior, there exists a primal-optimal feasible
joint `π_aux` that is auxiliary-minimal (`IsAuxiliaryMinimizer`) and an active set
`S ⊆ S_star s v S` witnessing `ConditionM s v π_aux S`. -/
lemma exists_auxiliary_minimizer
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L v)
    (hv_C1 : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    (hv_usc : UpperSemicontinuous v)
    (hV_meas : Measurable (s.composedValue v))
    (hV_usc : UpperSemicontinuous (s.composedValue v))
    (h_pcheck_lip : ∀ {p : Ω → ℝ} {K : NNReal},
      LipschitzWith K p → LipschitzOnWith K (convexRoof s p) s.X)
    [s.prior.toMeasure.IsOpenPosMeasure]
    (h_dense : s.X ⊆ closure (Set.range s.m))
    (_h_density :
      ∃ lambdaref : ProbDist Ω,
        lambdaref.toMeasure.support = (Set.univ : Set Ω) ∧
        s.prior.toMeasure.AbsolutelyContinuous lambdaref.toMeasure) :
    ∃ pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
    ∃ S : Set (EuclideanSpace ℝ (Fin n)),
      IsAuxiliaryMinimizer s v pi ∧
      ConditionM s v pi S ∧
      S ⊆ S_star s v S := by
  have hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |s.composedValue v μ| ≤ M := by
    obtain ⟨M, hM⟩ := hv_bdd
    exact ⟨M, fun μ => hM (s.posteriorMoment μ)⟩
  obtain ⟨pi_star, hpi_feas, hpi_val⟩ :=
    exists_optimal_joint s hm_lip hv_lip hv_meas hv_bdd hv_usc hV_bdd hV_usc
  obtain ⟨pi_aux, hpi_aux_feas, hpi_aux_val, hpi_aux_min⟩ :
      ∃ pi_aux : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
        pi_aux ∈ feasibleJoint s ∧
        (∫ p, v p.1 ∂pi_aux.toMeasure = momentPrimal s v) ∧
        ∀ pi' ∈ feasibleJoint s,
          (∫ p, v p.1 ∂pi'.toMeasure = momentPrimal s v) →
          ∫ p, ‖p.1‖^2 ∂pi_aux.toMeasure ≤ ∫ p, ‖p.1‖^2 ∂pi'.toMeasure := by
    classical
    set K : Set (ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :=
      {μ | μ ∈ feasibleJoint s ∧ ∫ p, v p.1 ∂μ.toMeasure = momentPrimal s v}
      with hK_def
    set J : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) → ℝ :=
      fun μ => ∫ p, ‖p.1‖^2 ∂μ.toMeasure with hJ_def
    have hK_nonempty : K.Nonempty := ⟨pi_star, hpi_feas, hpi_val⟩
    have hK_compact : IsCompact K := by
      set B : Set (EuclideanSpace ℝ (Fin n) × Ω) :=
        s.X ×ˢ (Set.univ : Set Ω) with hB_def
      have hB_compact : IsCompact B := s.X_compact.prod isCompact_univ
      have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
      have hT_compact :
          IsCompact
            {μ : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              ∀ _ : ℕ, μ (Bᶜ) ≤ (0 : NNReal)} :=
        isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
          (u := fun _ : ℕ => (0 : NNReal))
          (K := fun _ : ℕ => B)
          tendsto_const_nhds
          (fun _ => hB_compact)
          (Or.inr (fun _ _ _ => le_refl _))
      have hK_sub_T : K ⊆
          {μ : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
            ∀ _ : ℕ, μ (Bᶜ) ≤ (0 : NNReal)} := by
        intro μ hμ _
        have hμ_feas : μ ∈ feasibleJoint s := hμ.1
        have h_supp_one :
            μ.toMeasure (Prod.fst ⁻¹' s.X) = 1 := hμ_feas.fst_supportsOn
        have h_set_eq : ((Prod.fst ⁻¹' s.X) : Set (EuclideanSpace ℝ (Fin n) × Ω))
            = B := by ext p; simp [hB_def]
        haveI : MeasureTheory.IsProbabilityMeasure μ.toMeasure := inferInstance
        have h_supp_one' : μ.toMeasure B = 1 := by rw [← h_set_eq]; exact h_supp_one
        have h_compl_zero : μ.toMeasure Bᶜ = 0 :=
          (MeasureTheory.prob_compl_eq_zero_iff hB_meas).mpr h_supp_one'
        have h_apply_zero : ((μ (Bᶜ) : NNReal) : ENNReal) = 0 := by
          rw [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ (Bᶜ)]
          exact h_compl_zero
        exact (ENNReal.coe_eq_zero.mp h_apply_zero).le
      have hK_closed : IsClosed K := by
        set Phi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) → ProbDist Ω :=
          fun ν => MeasureTheory.ProbabilityMeasure.map ν
            (continuous_snd
              (X := EuclideanSpace ℝ (Fin n)) (Y := Ω)).measurable.aemeasurable
          with hPhi_def
        have h_map_cont : Continuous Phi :=
          MeasureTheory.ProbabilityMeasure.continuous_map continuous_snd
        have hK_marg_closed :
            IsClosed {ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              Phi ν = s.prior} := by
          have h_singleton_closed : IsClosed ({s.prior} : Set (ProbDist Ω)) :=
            isClosed_singleton
          exact h_singleton_closed.preimage h_map_cont
        have hX_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
          s.X_compact.isClosed
        have hC_closed :
            IsClosed (Prod.fst ⁻¹' s.X : Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
          hX_closed.preimage continuous_fst
        have hK_supp_closed :
            IsClosed {ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              ν.toMeasure (Prod.fst ⁻¹' s.X) = 1} := by
          rw [isClosed_iff_clusterPt]
          intro ν hν_cluster
          set F : Filter (ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :=
            nhds ν ⊓ Filter.principal
              {ν' | ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1} with hF_def
          haveI hFNeBot : F.NeBot := hν_cluster
          have h_upper : ν.toMeasure (Prod.fst ⁻¹' s.X) ≤ 1 :=
            MeasureTheory.prob_le_one
          have h_limsup :
              Filter.limsup
                (fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                  (ν'.toMeasure (Prod.fst ⁻¹' s.X) : ENNReal)) F
                ≤ ν.toMeasure (Prod.fst ⁻¹' s.X) := by
            have htends :
                Filter.Tendsto (id : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) →
                    ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) F (nhds ν) :=
              Filter.tendsto_id.mono_left inf_le_left
            exact MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
              htends hC_closed
          have h_one_le :
              (1 : ENNReal) ≤ Filter.limsup
                (fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                  (ν'.toMeasure (Prod.fst ⁻¹' s.X) : ENNReal)) F := by
            have h_eventually :
                ∀ᶠ ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) in F,
                  (ν'.toMeasure (Prod.fst ⁻¹' s.X) : ENNReal) = 1 := by
              apply Filter.eventually_inf_principal.mpr
              filter_upwards with ν' hν'
              rw [hν']
            have h_eq :
                Filter.limsup
                  (fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                    (ν'.toMeasure (Prod.fst ⁻¹' s.X) : ENNReal)) F
                  = (1 : ENNReal) := by
              rw [Filter.limsup_congr h_eventually, Filter.limsup_const]
            exact h_eq.ge
          have h_one_le_ν : (1 : ENNReal) ≤ ν.toMeasure (Prod.fst ⁻¹' s.X) :=
            h_one_le.trans h_limsup
          exact le_antisymm h_upper h_one_le_ν
        obtain ⟨χcut, hχ_one, _hχ_zero, hχ_compactSupport, hχ_mem⟩ :=
          exists_continuous_one_zero_of_isCompact
            (s := (s.X : Set (EuclideanSpace ℝ (Fin n))))
            (t := (∅ : Set (EuclideanSpace ℝ (Fin n))))
            s.X_compact isClosed_empty (Set.disjoint_empty s.X)
        have hχ_le_one : ∀ x, χcut x ≤ 1 := fun x => (hχ_mem x).2
        have hχ_nn : ∀ x, 0 ≤ χcut x := fun x => (hχ_mem x).1
        have hχ_cont : Continuous (χcut : EuclideanSpace ℝ (Fin n) → ℝ) :=
          χcut.continuous
        have hΩ_compact : IsCompact (Set.univ : Set Ω) := isCompact_univ
        obtain ⟨Rm, hRm_nn, hRm_bd⟩ : ∃ Rm : ℝ, 0 ≤ Rm ∧ ∀ ω : Ω, ‖s.m ω‖ ≤ Rm := by
          obtain ⟨Rraw, hRraw⟩ :=
            (hΩ_compact.image s.m_continuous).isBounded.exists_norm_le
          refine ⟨max Rraw 0, le_max_right _ _, fun ω => ?_⟩
          exact (hRraw _ ⟨ω, trivial, rfl⟩).trans (le_max_left _ _)
        obtain ⟨RX, hRX_nn, hRX_bd⟩ : ∃ RX : ℝ, 0 ≤ RX ∧ ∀ x ∈ s.X, ‖x‖ ≤ RX := by
          obtain ⟨Rraw, hRraw⟩ := s.X_compact.isBounded.exists_norm_le
          refine ⟨max Rraw 0, le_max_right _ _, fun x hx => ?_⟩
          exact (hRraw x hx).trans (le_max_left _ _)
        obtain ⟨Rχ, hRχ_nn, hRχ_bd⟩ : ∃ Rχ : ℝ, 0 ≤ Rχ ∧
            ∀ x, x ∈ tsupport (χcut : _ → ℝ) → ‖x‖ ≤ Rχ := by
          obtain ⟨Rraw, hRraw⟩ := hχ_compactSupport.isBounded.exists_norm_le
          refine ⟨max Rraw 0, le_max_right _ _, fun x hx => ?_⟩
          exact (hRraw x hx).trans (le_max_left _ _)
        have hK_mart_closed :
            IsClosed {ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              ν.toMeasure (Prod.fst ⁻¹' s.X) = 1 ∧
              ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
                Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
                  ∀ i : Fin n,
                    ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂ν.toMeasure = 0} := by
          rw [isClosed_iff_clusterPt]
          intro ν hν_cluster
          set F : Filter (ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :=
            nhds ν ⊓ Filter.principal _ with hF_def
          haveI hF_NeBot : F.NeBot := hν_cluster
          have h_tend_id :
              Filter.Tendsto (id : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) →
                  ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) F (nhds ν) :=
            Filter.tendsto_id.mono_left inf_le_left
          have h_supp : ν.toMeasure (Prod.fst ⁻¹' s.X) = 1 := by
            have hclosed := hK_supp_closed
            rw [isClosed_iff_clusterPt] at hclosed
            apply hclosed ν
            have h_sub : {ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
                ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1 ∧
                ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
                  Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
                    ∀ i : Fin n,
                      ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂ν'.toMeasure = 0} ⊆
                {ν' | ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1} := by
              intro ν' hν'; exact hν'.1
            have hsubprinc :
                Filter.principal {ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
                  ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1 ∧
                  ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
                    Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
                      ∀ i : Fin n,
                        ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂ν'.toMeasure = 0} ≤
                  Filter.principal
                    {ν' | ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1} :=
              Filter.principal_mono.mpr h_sub
            refine ⟨?_⟩
            have h_le_supp : F ≤ nhds ν ⊓ Filter.principal
                {ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
                  ν'.toMeasure (Prod.fst ⁻¹' s.X) = 1} := by
              rw [hF_def]
              exact inf_le_inf_left _ hsubprinc
            exact (Filter.NeBot.mono hF_NeBot h_le_supp).ne'
          refine ⟨h_supp, ?_⟩
          intro φ hφ_cont hφ_bdd i
          obtain ⟨Mφ, hMφ⟩ := hφ_bdd
          have hMφ_nn : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ 0)
          have h_integrand_bound :
              ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
                |χcut p.1 * φ p.1 * (s.m p.2 i - p.1 i)|
                  ≤ Mφ * (Rm + Rχ) := by
            intro p
            by_cases hsupp : p.1 ∈ tsupport (χcut : _ → ℝ)
            · -- p.1 is in tsupport χcut, so ‖p.1‖ ≤ Rχ.
              have hp1_norm : ‖p.1‖ ≤ Rχ := hRχ_bd p.1 hsupp
              have hp1_i : |p.1 i| ≤ Rχ := by
                refine (?_ : |p.1 i| ≤ ‖p.1‖).trans hp1_norm
                have hbd := PiLp.norm_apply_le (p.1) i
                rw [Real.norm_eq_abs] at hbd
                exact hbd
              have hm_i : |s.m p.2 i| ≤ Rm := by
                refine (?_ : |s.m p.2 i| ≤ ‖s.m p.2‖).trans (hRm_bd p.2)
                have hbd := PiLp.norm_apply_le (s.m p.2) i
                rw [Real.norm_eq_abs] at hbd
                exact hbd
              have h_diff_bd : |s.m p.2 i - p.1 i| ≤ Rm + Rχ := by
                calc |s.m p.2 i - p.1 i|
                    ≤ |s.m p.2 i| + |p.1 i| := abs_sub _ _
                  _ ≤ Rm + Rχ := add_le_add hm_i hp1_i
              have hχ_abs : |χcut p.1| ≤ 1 := by
                rw [abs_of_nonneg (hχ_nn p.1)]; exact hχ_le_one p.1
              calc |χcut p.1 * φ p.1 * (s.m p.2 i - p.1 i)|
                  = |χcut p.1| * |φ p.1| * |s.m p.2 i - p.1 i| := by
                    rw [abs_mul, abs_mul]
                _ ≤ 1 * Mφ * (Rm + Rχ) := by
                    refine mul_le_mul (mul_le_mul hχ_abs (hMφ p.1) (abs_nonneg _) ?_) h_diff_bd
                      (abs_nonneg _) ?_
                    · exact zero_le_one
                    · exact mul_nonneg zero_le_one hMφ_nn
                _ = Mφ * (Rm + Rχ) := by ring
            · -- p.1 ∉ tsupport χcut ⇒ χcut p.1 = 0.
              have h_zero : χcut p.1 = 0 :=
                image_eq_zero_of_notMem_tsupport hsupp
              rw [h_zero, zero_mul, zero_mul, abs_zero]
              exact mul_nonneg hMφ_nn (add_nonneg hRm_nn hRχ_nn)
          have h_integrand_cont :
              Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                χcut p.1 * φ p.1 * (s.m p.2 i - p.1 i) := by
            have h1 : Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                χcut p.1 := hχ_cont.comp continuous_fst
            have h2 : Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                φ p.1 := hφ_cont.comp continuous_fst
            have hproj : Continuous fun x : EuclideanSpace ℝ (Fin n) => x i := by
              fun_prop
            have h3 : Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                s.m p.2 i := hproj.comp (s.m_continuous.comp continuous_snd)
            have h4 : Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                p.1 i := hproj.comp continuous_fst
            exact ((h1.mul h2).mul (h3.sub h4))
          let gφi : BoundedContinuousFunction
              (EuclideanSpace ℝ (Fin n) × Ω) ℝ :=
            BoundedContinuousFunction.ofNormedAddCommGroup
              (fun p => χcut p.1 * φ p.1 * (s.m p.2 i - p.1 i))
              h_integrand_cont
              (Mφ * (Rm + Rχ))
              (fun p => by
                rw [Real.norm_eq_abs]
                exact h_integrand_bound p)
          have h_gφi_cont :
              Continuous fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                ∫ p, gφi p ∂ν'.toMeasure :=
            MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction gφi
          have h_eventually_zero :
              ∀ᶠ ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) in F,
                ∫ p, gφi p ∂ν'.toMeasure = 0 := by
            apply Filter.eventually_inf_principal.mpr
            filter_upwards with ν' hν'
            obtain ⟨_hν'_supp, hν'_mart⟩ := hν'
            have hχφ_cont : Continuous (fun x => χcut x * φ x) :=
              hχ_cont.mul hφ_cont
            have hχφ_bdd : ∃ M, ∀ x, |χcut x * φ x| ≤ M := by
              refine ⟨Mφ, fun x => ?_⟩
              calc |χcut x * φ x|
                  = |χcut x| * |φ x| := abs_mul _ _
                _ ≤ 1 * Mφ := by
                    refine mul_le_mul ?_ (hMφ x) (abs_nonneg _) zero_le_one
                    rw [abs_of_nonneg (hχ_nn x)]
                    exact hχ_le_one x
                _ = Mφ := one_mul _
            exact hν'_mart (fun x => χcut x * φ x) hχφ_cont hχφ_bdd i
          have h_lim : Filter.Tendsto
              (fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                ∫ p, gφi p ∂ν'.toMeasure) F
              (nhds (∫ p, gφi p ∂ν.toMeasure)) :=
            (h_gφi_cont.tendsto ν).comp h_tend_id
          have h_zero_int_gφi : ∫ p, gφi p ∂ν.toMeasure = 0 := by
            have h_zero_tendsto :
                Filter.Tendsto (fun _ : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                  (0 : ℝ)) F (nhds 0) := tendsto_const_nhds
            have h_lim_zero : Filter.Tendsto
                (fun ν' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                  ∫ p, gφi p ∂ν'.toMeasure) F (nhds 0) := by
              apply h_zero_tendsto.congr'
              filter_upwards [h_eventually_zero] with ν' hν'
              exact hν'.symm
            exact tendsto_nhds_unique h_lim h_lim_zero
          have hX_meas : MeasurableSet s.X := s.X_compact.isClosed.measurableSet
          have h_supp_meas : MeasurableSet
              (Prod.fst ⁻¹' s.X : Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
            measurable_fst hX_meas
          haveI : MeasureTheory.IsProbabilityMeasure ν.toMeasure := inferInstance
          have h_compl_zero :
              ν.toMeasure (Prod.fst ⁻¹' s.X)ᶜ = 0 :=
            (MeasureTheory.prob_compl_eq_zero_iff h_supp_meas).mpr h_supp
          have h_ae_X : ∀ᵐ p ∂ν.toMeasure, p.1 ∈ s.X := by
            rw [MeasureTheory.ae_iff]
            convert h_compl_zero using 1
          have h_int_eq :
              ∫ p, χcut p.1 * φ p.1 * (s.m p.2 i - p.1 i) ∂ν.toMeasure
                = ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂ν.toMeasure := by
            apply integral_congr_ae
            filter_upwards [h_ae_X] with p hp
            have hχp : χcut p.1 = 1 := hχ_one hp
            rw [hχp, one_mul]
          rw [← h_int_eq]
          exact h_zero_int_gφi
        have hv_cont : Continuous v := hv_lip.continuous
        obtain ⟨Mv, hMv⟩ := hv_bdd
        let gv : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n) × Ω) ℝ :=
          BoundedContinuousFunction.ofNormedAddCommGroup
            (fun p => v p.1)
            (hv_cont.comp continuous_fst)
            Mv
            (fun p => by
              rw [Real.norm_eq_abs]
              exact hMv p.1)
        have h_gv_cont :
            Continuous fun ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
              ∫ p, gv p ∂ν.toMeasure :=
          MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction gv
        have hK_lvl_closed :
            IsClosed {ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              ∫ p, v p.1 ∂ν.toMeasure = momentPrimal s v} := by
          have h_const_closed : IsClosed ({momentPrimal s v} : Set ℝ) :=
            isClosed_singleton
          have h_eq : {ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) |
              ∫ p, v p.1 ∂ν.toMeasure = momentPrimal s v}
              = (fun ν : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
                  ∫ p, gv p ∂ν.toMeasure) ⁻¹' {momentPrimal s v} := by
            ext ν
            simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
            rfl
          rw [h_eq]
          exact h_const_closed.preimage h_gv_cont
        have h_eq_K :
            K = ({ν | Phi ν = s.prior}
                ∩ {ν | ν.toMeasure (Prod.fst ⁻¹' s.X) = 1 ∧
                    ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
                      Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
                        ∀ i : Fin n,
                          ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂ν.toMeasure = 0}
                ∩ {ν | ∫ p, v p.1 ∂ν.toMeasure = momentPrimal s v}) := by
          ext ν
          simp only [hK_def, Set.mem_setOf_eq, Set.mem_inter_iff, feasibleJoint]
          constructor
          · rintro ⟨⟨hmarg, hsupp, hmart⟩, hlvl⟩
            refine ⟨⟨?_, hsupp, hmart⟩, hlvl⟩
            show Phi ν = s.prior
            exact hmarg
          · rintro ⟨⟨hmarg, hsupp, hmart⟩, hlvl⟩
            refine ⟨⟨?_, hsupp, hmart⟩, hlvl⟩
            show ProbDist.map ν Prod.snd measurable_snd = s.prior
            exact hmarg
        rw [h_eq_K]
        exact (hK_marg_closed.inter hK_mart_closed).inter hK_lvl_closed
      exact hT_compact.of_isClosed_subset hK_closed hK_sub_T
    have hJ_cont : ContinuousOn J K := by
      obtain ⟨R, hR_nn, hR_bd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ s.X, ‖x‖ ≤ R := by
        obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
        refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
        exact (hR x hx).trans (le_max_left _ _)
      let g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n) × Ω) ℝ :=
        BoundedContinuousFunction.ofNormedAddCommGroup
          (fun p => min (‖p.1‖ ^ 2) (R ^ 2))
          (by
            have h1 : Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                ‖p.1‖ ^ 2 := by fun_prop
            exact h1.min continuous_const)
          (R ^ 2)
          (fun p => by
            rw [Real.norm_eq_abs]
            have h_nn : 0 ≤ min (‖p.1‖ ^ 2) (R ^ 2) :=
              le_min (sq_nonneg _) (sq_nonneg _)
            rw [abs_of_nonneg h_nn]
            exact min_le_right _ _)
      have hg_cont : Continuous fun μ : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) =>
          ∫ p, g p ∂μ.toMeasure :=
        MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction g
      have hJ_eq_on_K : ∀ μ ∈ K, ∫ p, g p ∂μ.toMeasure = J μ := by
        intro μ hμ
        have hμ_feas : μ ∈ feasibleJoint s := hμ.1
        have h_supp_one :
            μ.toMeasure (Prod.fst ⁻¹' s.X) = 1 := hμ_feas.fst_supportsOn
        have hX_meas : MeasurableSet s.X := s.X_compact.isClosed.measurableSet
        have h_supp_meas : MeasurableSet
            (Prod.fst ⁻¹' s.X : Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
          measurable_fst hX_meas
        haveI : MeasureTheory.IsProbabilityMeasure μ.toMeasure := inferInstance
        have h_compl_zero :
            μ.toMeasure (Prod.fst ⁻¹' s.X)ᶜ = 0 :=
          (MeasureTheory.prob_compl_eq_zero_iff h_supp_meas).mpr h_supp_one
        have h_ae : ∀ᵐ p ∂μ.toMeasure, p.1 ∈ s.X := by
          rw [MeasureTheory.ae_iff]
          convert h_compl_zero using 1
        refine integral_congr_ae ?_
        filter_upwards [h_ae] with p hp
        refine min_eq_left ?_
        have h_norm_nn : 0 ≤ ‖p.1‖ := norm_nonneg _
        exact pow_le_pow_left₀ h_norm_nn (hR_bd p.1 hp) 2
      refine ContinuousOn.congr (hg_cont.continuousOn (s := K)) ?_
      intro μ hμ
      exact (hJ_eq_on_K μ hμ).symm
    obtain ⟨pi_aux, hpi_aux_K, hpi_aux_min⟩ :=
      hK_compact.exists_isMinOn hK_nonempty hJ_cont
    refine ⟨pi_aux, hpi_aux_K.1, hpi_aux_K.2, fun pi' hpi'_feas hpi'_val => ?_⟩
    exact hpi_aux_min ⟨hpi'_feas, hpi'_val⟩
  obtain ⟨S, hM, hS_sub⟩ :=
    (optimality_iff_M_with_Sstar s hm_lip hv_lip hv_C1 hv_meas hv_bdd hv_usc
        hV_meas hV_usc h_pcheck_lip pi_aux hpi_aux_feas h_dense).mp hpi_aux_val
  refine ⟨pi_aux, S, ⟨hpi_aux_feas, hpi_aux_val, hpi_aux_min⟩, hM, hS_sub⟩

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
