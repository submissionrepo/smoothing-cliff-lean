/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.WeakConvergence.PortmanteauIntegral
public import Econlib.Probability.Order.Convex.ConditionalMeanPartition
public import Econlib.Probability.Order.Convex.Topology

/-!
# Topological continuity of conditional-mean partition laws

Continuity properties of the map `c ↦ conditionalMeanPartitionLaw d P_c` as the cutoff vector `c`
varies in the η-spaced domain over `[0, 1]`. Cell mass and cell mean vary continuously with the
cutoffs, so the partition law varies weakly-continuously in `ProbabilityMeasure ℝ`, which in turn
transports upper semicontinuity of a value functional to the cutoff domain.

## Main definitions

* `EtaSpacedDomain K η` — the η-spaced cutoff domain over `[0, 1]`, as a subtype.
* `hpos_of_etaSpaced` — the positive-mass hypothesis attached to each η-spaced cutoff.

## Main statements

* `continuous_cellMass` — cell mass is continuous in the cutoff vector.
* `continuous_cellMean` — cell mean is continuous in the cutoff vector.
* `tendsto_conditionalMeanPartitionLaw`, `continuous_conditionalMeanPartitionLaw` — the partition
  law converges weakly when cutoffs converge.
* `upperSemicontinuous_value_of_continuousOn_functional`,
  `upperSemicontinuous_restrictedValue_of_kernel_regular` — upper semicontinuity of a value
  functional composed with the partition-law map.

## Tags

conditional mean, partition law, weak convergence, upper semicontinuity, prokhorov
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace Econlib.Probability

variable {K : ℕ} (η : ℝ) (d : ContDist)
variable (hd_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < d.density x)
variable (hd_cont : ContinuousOn d.density (Icc 0 1))

/-- The eta-spaced domain over the unit interval, as a subtype. The topology layer is fixed to
`[0, 1]` (posterior-mean space); the underlying partition machinery is general in `[a, b]`. -/
abbrev EtaSpacedDomain (K : ℕ) (η : ℝ) :=
  {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K 0 1 η c}

/-- For each cutoff in the eta-spaced domain, the associated positive mass hypothesis. -/
noncomputable def hpos_of_etaSpaced (hηpos : 0 < η)
    (c : EtaSpacedDomain K η) (j : Fin K) :
    0 < cellMass d (partitionOfCutoffs η c) j :=
  cellMass_pos_of_density_pos d (partitionOfCutoffs η c) j hd_pos hd_cont
    (partitionOfCutoffs_etaSpaced η c) hηpos

/-! ### Shared scaffolding for the continuity proofs -/

/-- The left cutoff coordinate is nonnegative on the eta-spaced domain. -/
private lemma castSucc_nonneg (c : EtaSpacedDomain K η) (j : Fin K) :
    0 ≤ c.val j.castSucc := by
  have hcc : (partitionOfCutoffs η c).cutoff = c.val := partitionOfCutoffs_cutoff η c
  have := (partitionOfCutoffs η c).le_leftEndpoint j
  simpa [OrderedCutoffPartition.leftEndpoint, hcc] using this

/-- The left cutoff coordinate is below the right one on the eta-spaced domain. -/
private lemma castSucc_le_succ (c : EtaSpacedDomain K η) (j : Fin K) :
    c.val j.castSucc ≤ c.val j.succ := by
  have hcc : (partitionOfCutoffs η c).cutoff = c.val := partitionOfCutoffs_cutoff η c
  have := (partitionOfCutoffs η c).leftEndpoint_le_rightEndpoint j
  simpa [OrderedCutoffPartition.leftEndpoint, OrderedCutoffPartition.rightEndpoint, hcc] using this

/-- The difference of the primitives `x ↦ ∫ t in Icc 0 x, g t` at the two cutoff coordinates equals
the integral of `g` over the closed cell `j`. This is the common Ioc-decomposition step shared by
`continuous_cellMass`, `continuous_cellMean`, and the denominator-positivity argument. -/
private lemma primitive_diff_eq_cellIntegral {g : ℝ → ℝ} (c : EtaSpacedDomain K η) (j : Fin K)
    (hg : IntegrableOn g (Set.Ioc (0 : ℝ) (c.val j.succ))) :
    (∫ t in Set.Icc (0 : ℝ) (c.val j.succ), g t) -
        (∫ t in Set.Icc (0 : ℝ) (c.val j.castSucc), g t) =
      ∫ x in (partitionOfCutoffs η c).cellClosed j, g x := by
  have hcc : (partitionOfCutoffs η c).cutoff = c.val := partitionOfCutoffs_cutoff η c
  have hL_nonneg : 0 ≤ c.val j.castSucc := castSucc_nonneg η c j
  have hLR : c.val j.castSucc ≤ c.val j.succ := castSucc_le_succ η c j
  -- (0, R] = (0, L] ∪ (L, R], with the pieces disjoint, so the integral splits additively.
  have hUnion : Set.Ioc (0 : ℝ) (c.val j.succ) =
      Set.Ioc (0 : ℝ) (c.val j.castSucc) ∪ Set.Ioc (c.val j.castSucc) (c.val j.succ) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc hL_nonneg hLR]
  have hint_left : IntegrableOn g (Set.Ioc (0 : ℝ) (c.val j.castSucc)) :=
    hg.mono_set (Set.Ioc_subset_Ioc_right hLR)
  have hint_cell : IntegrableOn g (Set.Ioc (c.val j.castSucc) (c.val j.succ)) :=
    hg.mono_set (Set.Ioc_subset_Ioc_left hL_nonneg)
  have hsplit : ∫ x in Set.Ioc (0 : ℝ) (c.val j.succ), g x =
      (∫ x in Set.Ioc (0 : ℝ) (c.val j.castSucc), g x) +
      ∫ x in Set.Ioc (c.val j.castSucc) (c.val j.succ), g x := by
    rw [hUnion]
    exact MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hint_left hint_cell
  -- Convert each Icc-primitive to an Ioc integral (the left endpoint is null), then cancel.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    hsplit]
  unfold OrderedCutoffPartition.cellClosed
    OrderedCutoffPartition.leftEndpoint OrderedCutoffPartition.rightEndpoint
  rw [hcc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  ring

/-! ## Continuity of cell mass and mean -/

/-- Cell mass is continuous as a function of the cutoff vector. -/
lemma continuous_cellMass (j : Fin K) :
    ContinuousOn (fun c : EtaSpacedDomain K η =>
      cellMass d (partitionOfCutoffs η c) j)
    (Set.univ) := by
  -- The primitive `F(x) = ∫ t in Icc 0 x, d.density t`.
  set F : ℝ → ℝ := fun x => ∫ t in Set.Icc (0 : ℝ) x, d.density t with hF_def
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_Icc d.integrable.integrableOn
  -- Coordinate projections are continuous.
  have hL_cts : Continuous
      (fun c : EtaSpacedDomain K η => c.val j.castSucc) :=
    (continuous_apply j.castSucc).comp continuous_subtype_val
  have hR_cts : Continuous
      (fun c : EtaSpacedDomain K η => c.val j.succ) :=
    (continuous_apply j.succ).comp continuous_subtype_val
  -- Endpoints lie in `[0, 1]` for `c ∈ EtaSpacedDomain`.
  have hL_mem : ∀ c : EtaSpacedDomain K η, c.val j.castSucc ∈ Set.Icc (0 : ℝ) 1 := by
    intro c
    have hcc : (partitionOfCutoffs η c).cutoff = c.val :=
      partitionOfCutoffs_cutoff η c
    refine ⟨?_, ?_⟩
    · have := (partitionOfCutoffs η c).le_leftEndpoint j
      simpa [OrderedCutoffPartition.leftEndpoint, hcc] using this
    · have hlr := (partitionOfCutoffs η c).leftEndpoint_le_rightEndpoint j
      have hr := (partitionOfCutoffs η c).rightEndpoint_le j
      have hL_le_one : (partitionOfCutoffs η c).leftEndpoint j ≤ 1 := hlr.trans hr
      simpa [OrderedCutoffPartition.leftEndpoint, hcc] using hL_le_one
  have hR_mem : ∀ c : EtaSpacedDomain K η, c.val j.succ ∈ Set.Icc (0 : ℝ) 1 := by
    intro c
    have hcc : (partitionOfCutoffs η c).cutoff = c.val :=
      partitionOfCutoffs_cutoff η c
    refine ⟨?_, ?_⟩
    · have hlr := (partitionOfCutoffs η c).leftEndpoint_le_rightEndpoint j
      have hl0 := (partitionOfCutoffs η c).le_leftEndpoint j
      have : 0 ≤ (partitionOfCutoffs η c).rightEndpoint j := hl0.trans hlr
      simpa [OrderedCutoffPartition.rightEndpoint, hcc] using this
    · have := (partitionOfCutoffs η c).rightEndpoint_le j
      simpa [OrderedCutoffPartition.rightEndpoint, hcc] using this
  -- F ∘ R and F ∘ L are continuous.
  have hFR : Continuous (fun c : EtaSpacedDomain K η => F (c.val j.succ)) :=
    hF_cont.comp_continuous hR_cts hR_mem
  have hFL : Continuous (fun c : EtaSpacedDomain K η => F (c.val j.castSucc)) :=
    hF_cont.comp_continuous hL_cts hL_mem
  -- The cell mass equals F(R) - F(L), by the shared Ioc-decomposition helper.
  have hcellMass_eq : ∀ c : EtaSpacedDomain K η,
      cellMass d (partitionOfCutoffs η c) j = F (c.val j.succ) - F (c.val j.castSucc) := fun c =>
    (primitive_diff_eq_cellIntegral η c j d.integrable.integrableOn).symm
  -- Continuity follows.
  have hcellMass_cts :
      Continuous (fun c : EtaSpacedDomain K η => cellMass d (partitionOfCutoffs η c) j) := by
    have heq : (fun c : EtaSpacedDomain K η => cellMass d (partitionOfCutoffs η c) j) =
        (fun c => F (c.val j.succ) - F (c.val j.castSucc)) := by
      funext c; exact hcellMass_eq c
    rw [heq]
    exact hFR.sub hFL
  exact hcellMass_cts.continuousOn

/-- Cell mean is continuous as a function of the cutoff vector. The cell-mean ratio has denominator
the cell mass, which is positive on the eta-spaced domain. -/
lemma continuous_cellMean
    (hd_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc 0 1))
    (hηpos : 0 < η) (j : Fin K) :
    ContinuousOn (fun c : EtaSpacedDomain K η =>
      cellMean d (partitionOfCutoffs η c) j)
    Set.univ := by
  -- Numerator primitive `G(x) = ∫ t in Icc 0 x, d.density t * t`.
  set G : ℝ → ℝ := fun x => ∫ t in Set.Icc (0 : ℝ) x, d.density t * t with hG_def
  -- The integrand `t ↦ d.density t * t` is integrable on `[0,1]` (bounded factor).
  have hG_int : IntegrableOn (fun t => d.density t * t) (Set.Icc (0 : ℝ) 1) := by
    have hbdd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖t‖ ≤ 1 := by
      intro t ht; rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have h_meas : AEStronglyMeasurable (fun t : ℝ => t) (volume.restrict (Set.Icc 0 1)) :=
      (continuous_id.aestronglyMeasurable).restrict
    have hbdd' : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ‖t‖ ≤ 1 := by
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards with t ht using hbdd t ht
    have h_dens_int : Integrable d.density (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      d.integrable.integrableOn
    have h_mul : Integrable (fun t => t * d.density t) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      MeasureTheory.Integrable.bdd_mul h_dens_int h_meas hbdd'
    -- Reorder factors.
    have hcomm : (fun t : ℝ => d.density t * t) = (fun t => t * d.density t) := by
      funext t; ring
    rw [show (fun t => d.density t * t) = (fun t => t * d.density t) from hcomm]
    exact h_mul
  have hG_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_Icc hG_int
  -- Denominator primitive (cell mass), via the same argument as `continuous_cellMass`.
  set F : ℝ → ℝ := fun x => ∫ t in Set.Icc (0 : ℝ) x, d.density t with hF_def
  have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_Icc d.integrable.integrableOn
  -- Coordinate projections are continuous.
  have hL_cts : Continuous
      (fun c : EtaSpacedDomain K η => c.val j.castSucc) :=
    (continuous_apply j.castSucc).comp continuous_subtype_val
  have hR_cts : Continuous
      (fun c : EtaSpacedDomain K η => c.val j.succ) :=
    (continuous_apply j.succ).comp continuous_subtype_val
  -- Endpoint membership.
  have hL_mem : ∀ c : EtaSpacedDomain K η, c.val j.castSucc ∈ Set.Icc (0 : ℝ) 1 := by
    intro c
    have hcc : (partitionOfCutoffs η c).cutoff = c.val := partitionOfCutoffs_cutoff η c
    refine ⟨?_, ?_⟩
    · have := (partitionOfCutoffs η c).le_leftEndpoint j
      simpa [OrderedCutoffPartition.leftEndpoint, hcc] using this
    · have hlr := (partitionOfCutoffs η c).leftEndpoint_le_rightEndpoint j
      have hr := (partitionOfCutoffs η c).rightEndpoint_le j
      have : (partitionOfCutoffs η c).leftEndpoint j ≤ 1 := hlr.trans hr
      simpa [OrderedCutoffPartition.leftEndpoint, hcc] using this
  have hR_mem : ∀ c : EtaSpacedDomain K η, c.val j.succ ∈ Set.Icc (0 : ℝ) 1 := by
    intro c
    have hcc : (partitionOfCutoffs η c).cutoff = c.val := partitionOfCutoffs_cutoff η c
    refine ⟨?_, ?_⟩
    · have hlr := (partitionOfCutoffs η c).leftEndpoint_le_rightEndpoint j
      have hl0 := (partitionOfCutoffs η c).le_leftEndpoint j
      have : 0 ≤ (partitionOfCutoffs η c).rightEndpoint j := hl0.trans hlr
      simpa [OrderedCutoffPartition.rightEndpoint, hcc] using this
    · have := (partitionOfCutoffs η c).rightEndpoint_le j
      simpa [OrderedCutoffPartition.rightEndpoint, hcc] using this
  -- Continuity of N(c) and D(c).
  have hN_cts : Continuous (fun c : EtaSpacedDomain K η =>
      G (c.val j.succ) - G (c.val j.castSucc)) :=
    (hG_cont.comp_continuous hR_cts hR_mem).sub (hG_cont.comp_continuous hL_cts hL_mem)
  have hD_cts : Continuous (fun c : EtaSpacedDomain K η =>
      F (c.val j.succ) - F (c.val j.castSucc)) :=
    (hF_cont.comp_continuous hR_cts hR_mem).sub (hF_cont.comp_continuous hL_cts hL_mem)
  -- The denominator (cell mass) is everywhere positive on the eta-spaced domain.
  -- By the shared helper, `F(R) - F(L) = ∫_{cellClosed} density`, which is `cellMass`.
  have hD_pos : ∀ c : EtaSpacedDomain K η,
      F (c.val j.succ) - F (c.val j.castSucc) > 0 := by
    intro c
    rw [primitive_diff_eq_cellIntegral η c j d.integrable.integrableOn]
    exact hpos_of_etaSpaced η d hd_pos hd_cont hηpos c j
  -- Express cellMean as N/D.
  have hcellMean_eq : ∀ c : EtaSpacedDomain K η,
      cellMean d (partitionOfCutoffs η c) j =
        (G (c.val j.succ) - G (c.val j.castSucc)) /
        (F (c.val j.succ) - F (c.val j.castSucc)) := by
    intro c
    -- Numerator and denominator differences as cell integrals, via the shared helper.
    have hint_num : IntegrableOn (fun t => d.density t * t)
        (Set.Ioc (0 : ℝ) (c.val j.succ)) :=
      hG_int.mono_set fun x hx => ⟨le_of_lt hx.1, hx.2.trans (hR_mem c).2⟩
    have hG_diff_eq :
        G (c.val j.succ) - G (c.val j.castSucc) =
          ∫ x in (partitionOfCutoffs η c).cellClosed j, d.density x * x :=
      primitive_diff_eq_cellIntegral η c j hint_num
    have hF_diff_eq :
        F (c.val j.succ) - F (c.val j.castSucc) =
          ∫ x in (partitionOfCutoffs η c).cellClosed j, d.density x :=
      primitive_diff_eq_cellIntegral η c j d.integrable.integrableOn
    -- Cell mean equals N/D: unfold the conditional expectation, then match numerator/denominator.
    have h_cellMass_pos : 0 < ∫ x in (partitionOfCutoffs η c).cellClosed j, d.density x :=
      hpos_of_etaSpaced η d hd_pos hd_cont hηpos c j
    unfold cellMean
    rw [ContDist.conditionalExpectOrZero_eq_of_pos _ _ _ h_cellMass_pos, hG_diff_eq, hF_diff_eq]
    rfl
  -- Combine.
  have hcellMean_cts :
      Continuous (fun c : EtaSpacedDomain K η => cellMean d (partitionOfCutoffs η c) j) := by
    have heq : (fun c : EtaSpacedDomain K η => cellMean d (partitionOfCutoffs η c) j) =
        (fun c => (G (c.val j.succ) - G (c.val j.castSucc)) /
                  (F (c.val j.succ) - F (c.val j.castSucc))) := by
      funext c; exact hcellMean_eq c
    rw [heq]
    exact hN_cts.div hD_cts (fun c => ne_of_gt (hD_pos c))
  exact hcellMean_cts.continuousOn

/-! ## Weak convergence of partition laws -/

/-- The conditional-mean partition law converges weakly when the cutoff vector converges. -/
lemma tendsto_conditionalMeanPartitionLaw (hηpos : 0 < η)
    {ι : Type*} {l : Filter ι}
    {c : ι → EtaSpacedDomain K η} {c₀ : EtaSpacedDomain K η}
    (hc : Tendsto c l (nhds c₀)) :
    Tendsto
      (fun i => (conditionalMeanPartitionLaw d (partitionOfCutoffs η (c i))
                  (hpos_of_etaSpaced η d hd_pos hd_cont hηpos (c i)) : ProbabilityMeasure ℝ))
      l
      (nhds (conditionalMeanPartitionLaw d (partitionOfCutoffs η c₀)
               (hpos_of_etaSpaced η d hd_pos hd_cont hηpos c₀) : ProbabilityMeasure ℝ)) := by
  -- Abbreviation: `lawAt cv` is the partition law at cutoff `cv`.
  let lawAt : EtaSpacedDomain K η → ProbDist ℝ := fun cv =>
    conditionalMeanPartitionLaw d (partitionOfCutoffs η cv)
      (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)
  -- Reduce to: ∀ f : BCF ℝ ℝ, ∫ ω, f ω ∂(lawAt (c i) : Measure) → ∫ ω, f ω ∂(lawAt c₀ : Measure).
  change Tendsto (fun i => (lawAt (c i) : ProbabilityMeasure ℝ)) l
        (nhds (lawAt c₀ : ProbabilityMeasure ℝ))
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  -- Express each integral as a Finset sum: ∫ f d(law c) = ∑_j w_j(c) · f(μ_j(c)).
  have hint_dirac : ∀ (cv : EtaSpacedDomain K η) (j : Fin K),
      Integrable (⇑f)
        (ProbDist.dirac (cellMean d (partitionOfCutoffs η cv) j)).toMeasure := by
    intro cv j
    -- ProbDist.dirac unfolds to Measure.dirac for the underlying Measure.
    have h_le_top : ‖f (cellMean d (partitionOfCutoffs η cv) j)‖ₑ < ⊤ := by simp
    have hint : Integrable (⇑f)
        (Measure.dirac (cellMean d (partitionOfCutoffs η cv) j)) :=
      MeasureTheory.integrable_dirac h_le_top
    -- (ProbDist.dirac a).toMeasure = Measure.dirac a definitionally.
    simpa [ProbDist.dirac] using hint
  have hexpect_eq : ∀ cv : EtaSpacedDomain K η,
      ∫ ω, f ω ∂(lawAt cv : Measure ℝ) =
        ∑ j : Fin K,
          (conditionalMeanWeights d (partitionOfCutoffs η cv)
              (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).pmf j *
            f (cellMean d (partitionOfCutoffs η cv) j) := by
    intro cv
    -- ∫ f d(lawAt cv).toMeasure = (lawAt cv).expect (⇑f)
    change (lawAt cv).expect (⇑f) = _
    change (conditionalMeanPartitionLaw d (partitionOfCutoffs η cv)
            (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).expect (⇑f) = _
    rw [conditionalMeanPartitionLaw, ProbDist.expect_finMixture _ _ _ (fun j => hint_dirac cv j)]
    simp [ProbDist.expect_dirac]
  -- The Finset-sum form: φ(cv) = ∑_j w_j(cv) · f(μ_j(cv)).
  set φ : EtaSpacedDomain K η → ℝ := fun cv =>
    ∑ j : Fin K,
      (conditionalMeanWeights d (partitionOfCutoffs η cv)
          (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).pmf j *
        f (cellMean d (partitionOfCutoffs η cv) j) with hφ_def
  -- Rewrite both sides in terms of φ.
  have hLHS : (fun i => ∫ ω, f ω ∂(lawAt (c i) : Measure ℝ)) = φ ∘ c := by
    funext i
    change ∫ ω, f ω ∂(lawAt (c i) : Measure ℝ) = φ (c i)
    rw [hexpect_eq (c i)]
  have hRHS : ∫ ω, f ω ∂(lawAt c₀ : Measure ℝ) = φ c₀ := hexpect_eq c₀
  rw [hLHS, hRHS]
  -- It suffices to show φ is continuous.
  -- Each piece: w_j is continuous (cell mass / total cell mass), μ_j = cellMean is continuous,
  -- f is continuous, so f ∘ μ_j is continuous, and the product/sum is continuous.
  have hCellMass_cts : ∀ j : Fin K, Continuous
      (fun cv : EtaSpacedDomain K η => cellMass d (partitionOfCutoffs η cv) j) := by
    intro j
    exact continuousOn_univ.mp (continuous_cellMass (η := η) (d := d) (j := j))
  have hCellMean_cts : ∀ j : Fin K, Continuous
      (fun cv : EtaSpacedDomain K η => cellMean d (partitionOfCutoffs η cv) j) := by
    intro j
    exact continuousOn_univ.mp (continuous_cellMean (η := η) (d := d) hd_pos hd_cont hηpos j)
  -- Total cell mass, denominator of the weights.
  have hTotal_cts : Continuous
      (fun cv : EtaSpacedDomain K η =>
        ∑ k : Fin K, cellMass d (partitionOfCutoffs η cv) k) := by
    apply continuous_finset_sum
    intro k _; exact hCellMass_cts k
  -- Total cell mass is everywhere positive on the eta-spaced domain.
  -- (Strictly, this needs K ≥ 1; otherwise the empty sum is 0 — but `hpos_of_etaSpaced`
  -- forces K ≥ 1 because if K = 0 we'd have a contradictory partition.)
  have hTotal_pos : ∀ cv : EtaSpacedDomain K η,
      0 < ∑ k : Fin K, cellMass d (partitionOfCutoffs η cv) k := by
    intro cv
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · -- K = 0: derive contradiction from the partition's left=0 / right=1 endpoints.
      subst hK0
      have hP := partitionOfCutoffs η cv
      have h01 : (0 : ℝ) = 1 := by
        have hl := hP.left_eq
        have hr := hP.right_eq
        have heq : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = (0 : Fin 1) := rfl
        rw [heq, hl] at hr; exact hr
      exact absurd h01 (by norm_num)
    · haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
      exact Finset.sum_pos
        (fun k _ => hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv k) Finset.univ_nonempty
  -- Each weight pmf is continuous (cellMass / total).
  have hWeight_cts : ∀ j : Fin K, Continuous
      (fun cv : EtaSpacedDomain K η =>
        (conditionalMeanWeights d (partitionOfCutoffs η cv)
            (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).pmf j) := by
    intro j
    -- Unfold the pmf.
    have heq : (fun cv : EtaSpacedDomain K η =>
        (conditionalMeanWeights d (partitionOfCutoffs η cv)
            (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).pmf j) =
        (fun cv => cellMass d (partitionOfCutoffs η cv) j /
            ∑ k : Fin K, cellMass d (partitionOfCutoffs η cv) k) := by
      funext cv; rfl
    rw [heq]
    exact (hCellMass_cts j).div hTotal_cts (fun cv => ne_of_gt (hTotal_pos cv))
  -- f is continuous.
  have hf_cts : Continuous (⇑f : ℝ → ℝ) := f.continuous
  -- Each summand is continuous.
  have hSummand_cts : ∀ j : Fin K, Continuous
      (fun cv : EtaSpacedDomain K η =>
        (conditionalMeanWeights d (partitionOfCutoffs η cv)
            (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv)).pmf j *
          f (cellMean d (partitionOfCutoffs η cv) j)) := by
    intro j
    exact (hWeight_cts j).mul (hf_cts.comp (hCellMean_cts j))
  -- φ is continuous.
  have hφ_cts : Continuous φ := by
    apply continuous_finset_sum
    intro j _; exact hSummand_cts j
  -- Conclude.
  exact hφ_cts.tendsto c₀ |>.comp hc

/-- The partition-law map `c ↦ conditionalMeanPartitionLaw d P_c` is continuous as a map into
`ProbabilityMeasure ℝ`. Pointwise convergence at each `c₀` is `tendsto_conditionalMeanPartitionLaw`
applied to the identity net. -/
lemma continuous_conditionalMeanPartitionLaw (hηpos : 0 < η) :
    Continuous (fun c : EtaSpacedDomain K η =>
      (conditionalMeanPartitionLaw d (partitionOfCutoffs η c)
        (hpos_of_etaSpaced η d hd_pos hd_cont hηpos c) : ProbabilityMeasure ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro c₀
  exact tendsto_conditionalMeanPartitionLaw (η := η) (d := d) hd_pos hd_cont hηpos
    (ι := EtaSpacedDomain K η) (l := nhds c₀) (c := id) (c₀ := c₀) tendsto_id

/-! ## Upper semicontinuity of value functionals -/

/-- If a value functional `V : ProbDist ℝ → ℝ` is upper-semicontinuous on the set of laws supported
on `[0,1]` (in the weak topology), then the composite `c ↦ V (conditionalMeanPartitionLaw d P_c)`
is upper-semicontinuous on the eta-spaced domain. -/
lemma upperSemicontinuous_value_of_continuousOn_functional (hηpos : 0 < η)
    (V : ProbDist ℝ → ℝ)
    (hV : UpperSemicontinuousOn (fun μ : ProbabilityMeasure ℝ => V μ)
            {μ : ProbabilityMeasure ℝ | ProbDist.supportsOn μ (Icc 0 1)}) :
    UpperSemicontinuousOn
      (fun c : EtaSpacedDomain K η =>
        V (conditionalMeanPartitionLaw d (partitionOfCutoffs η c)
             (hpos_of_etaSpaced η d hd_pos hd_cont hηpos c)))
      Set.univ := by
  -- The map `c ↦ law(c)` from `EtaSpacedDomain K η` into `ProbabilityMeasure ℝ`.
  set lawAt : EtaSpacedDomain K η → ProbabilityMeasure ℝ := fun cv =>
    conditionalMeanPartitionLaw d (partitionOfCutoffs η cv)
      (hpos_of_etaSpaced η d hd_pos hd_cont hηpos cv) with hlawAt_def
  -- Continuity of `lawAt` is the shared `continuous_conditionalMeanPartitionLaw`.
  have hlawAt_cts : Continuous lawAt :=
    continuous_conditionalMeanPartitionLaw η d hd_pos hd_cont hηpos
  -- Each `lawAt c` is supported on `Icc 0 1` (by `conditionalMeanPartitionLaw_supportsOn`).
  have hMaps : Set.MapsTo lawAt Set.univ
      {μ : ProbabilityMeasure ℝ | ProbDist.supportsOn μ (Icc 0 1)} := by
    intro cv _
    exact conditionalMeanPartitionLaw_supportsOn d (partitionOfCutoffs η cv) _ hd_cont
  -- Apply USC composition.
  have hcomp := hV.comp hlawAt_cts.continuousOn hMaps
  exact hcomp

/-- Specialization: Upper semicontinuity of a bounded upper-semicontinuous welfare function `W`
composed with a weakly-continuous posterior kernel and the partition-law map. -/
lemma upperSemicontinuous_restrictedValue_of_kernel_regular (hηpos : 0 < η)
    (posteriorKernel : ProbDist ℝ → ProbDist ℝ)
    (hkernel_cts : Continuous (fun μ : ProbabilityMeasure ℝ =>
        (posteriorKernel μ : ProbabilityMeasure ℝ)))
    (hkernel_support : ∀ μ : ProbDist ℝ, (posteriorKernel μ : Measure ℝ) (Icc 0 1) = 1)
    (W : ℝ → ℝ)
    (hW_bdd : ∃ C, ∀ x ∈ Icc (0:ℝ) 1, |W x| ≤ C)
    (hW_usc : UpperSemicontinuousOn W (Icc 0 1)) :
    UpperSemicontinuousOn
      (fun c : EtaSpacedDomain K η =>
        (posteriorKernel
          (conditionalMeanPartitionLaw d (partitionOfCutoffs η c)
            (hpos_of_etaSpaced η d hd_pos hd_cont hηpos c))).expect W)
      Set.univ := by
  -- Let lawAt abbreviate the partition law.
  set lawAt : EtaSpacedDomain K η → ProbabilityMeasure ℝ := fun c =>
    conditionalMeanPartitionLaw d (partitionOfCutoffs η c)
      (hpos_of_etaSpaced η d hd_pos hd_cont hηpos c) with hlawAt_def
  -- lawAt is continuous (shared `continuous_conditionalMeanPartitionLaw`).
  have hlawAt_cts : Continuous lawAt :=
    continuous_conditionalMeanPartitionLaw η d hd_pos hd_cont hηpos
  -- The full map c ↦ posteriorKernel(lawAt c) is continuous.
  have hfullMap_cts : ContinuousOn
      (fun c : EtaSpacedDomain K η => (posteriorKernel (lawAt c) : ProbabilityMeasure ℝ))
      Set.univ :=
    (hkernel_cts.comp hlawAt_cts).continuousOn
  -- Unfold expect to a Bochner integral.
  simp_rw [ProbDist.expect]
  -- Apply Portmanteau bounded-USC integral theorem (composition form).
  open ProbabilityMeasure in
  exact
    upperSemicontinuousOn_integral_comp_of_bounded_upperSemicontinuousOn_compactSupport
      hfullMap_cts
      (fun θ _ => hkernel_support (lawAt θ))
      isCompact_Icc
      hW_bdd
      hW_usc

end Econlib.Probability

end
