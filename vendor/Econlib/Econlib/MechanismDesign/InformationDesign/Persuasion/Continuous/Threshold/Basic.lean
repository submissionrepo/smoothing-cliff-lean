/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.ConvexOrder
public import Econlib.Probability.ContDist.Conditioning
public import Econlib.Probability.ContDist.ProbDist
public import Econlib.Probability.Distributions.Bernoulli
public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.Order.Convex.ConditionalMeanPartition
public import Econlib.Probability.Order.Core.IntegratedCDF
public import Econlib.Probability.Order.Core.NegPut
public import Econlib.Probability.Order.FOSD.Basic
public import Econlib.Probability.Order.FOSD.ExpectMono
public import Econlib.Probability.Order.SOSD.Basic

/-!
# Threshold persuasion: Two-point laws and cutoff signals

In *threshold persuasion* on `ℝ`, the sender's payoff depends only on whether the state lies above
a cutoff, and an optimal signal collapses to a two-point distribution. This file develops the
supporting lemmas on truncated densities and provides the two-point construction; the optimality
statement itself is `thresholdTwoPointLaw_isOptimal_excessOverThreshold` in
`Persuasion.Continuous.Threshold.Optimality` (built on the convex-price certificate
`isOptimalSignal_of_convexMajorant` of `Persuasion.Continuous.Optimality`).

## Main definitions

* `thresholdTwoPointLaw` — two-point law derived from a continuous distribution and a cutoff.

## Main statements

* `thresholdTwoPointLaw_eq_finMixture_dirac` — the two-point law equals a finite mixture of Dirac
  masses at the conditional expectations below and above the cutoff.
* `thresholdTwoPointLaw_expect` — explicit formula for expectations under the two-point law.
* `thresholdTwoPointLaw_supportsOn_Icc` — the two-point law is supported on `[a, b]`.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, threshold persuasion, cutoff, two-point distribution
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

/-- A continuous distribution whose density vanishes outside `[a, b]` has its induced probability
law supported on `[a, b]`. -/
lemma contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside
    (d : Econlib.Probability.ContDist) {a b : ℝ}
    (hzero : ∀ x, x ∉ Icc a b → d.density x = 0) :
    d.toProbDist.supportsOn (Icc a b) := by
  unfold Econlib.Probability.ProbDist.supportsOn
  rw [Econlib.Probability.ContDist.toProbDist_toMeasure]
  have hcomp : d.toMeasure (Icc a b)ᶜ = 0 := by
    rw [d.toMeasure_eq, withDensity_apply _ measurableSet_Icc.compl]
    have hzero_ae :
        (fun x => ENNReal.ofReal (d.density x)) =ᵐ[volume.restrict (Icc a b)ᶜ] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      simp [hzero x (by simpa using hx)]
    rw [lintegral_congr_ae hzero_ae]
    simp
  calc
    d.toMeasure (Icc a b) = d.toMeasure univ := measure_of_measure_compl_eq_zero hcomp
    _ = 1 := by simpa using (Econlib.Probability.ContDist.toMeasure_isProbability d).measure_univ

/-- The expectation under the distribution truncated to `[a, b]` equals the conditional expectation
of `d` given `[a, b]`. -/
lemma truncate_expect_eq_conditionalExpect (d : Econlib.Probability.ContDist)
    (a b : ℝ) (h_ab : a < b) (h_pos : 0 < d.prob_interval a b)
    -- integrability of `d.density * f` on `[a, b]` is not needed: the proof rewrites the
    -- truncated-density integral to a division rather than invoking integrability directly.
    (f : ℝ → ℝ) (_hf_int : IntegrableOn (fun x => d.density x * f x) (Icc a b)) :
    (d.truncate a b h_ab h_pos).expect f = d.conditionalExpect f (Icc a b)
      (by simpa [Econlib.Probability.ContDist.prob_interval,
            integral_Icc_eq_integral_Ioc] using h_pos) := by
  have hpos_set : 0 < ∫ x in Icc a b, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval,
      integral_Icc_eq_integral_Ioc] using h_pos
  rw [Econlib.Probability.ContDist.expect, d.conditionalExpect_eq f (Icc a b) hpos_set]
  have hmass : ∫ x in Icc a b, d.density x = d.prob_interval a b := rfl
  have hprob_ne : d.prob_interval a b ≠ 0 := ne_of_gt h_pos
  rw [show (fun x => (d.truncate a b h_ab h_pos).density x * f x) =
      (Icc a b).indicator (fun x => (d.density x * f x) / d.prob_interval a b) by
      funext x
      by_cases hx : x ∈ Icc a b
      · simp [Econlib.Probability.ContDist.truncate_density, hx]
        field_simp [hprob_ne]
      · simp [Econlib.Probability.ContDist.truncate_density, hx]]
  rw [integral_indicator measurableSet_Icc, hmass]
  simpa using
    (MeasureTheory.integral_div (μ := volume.restrict (Icc a b)) (d.prob_interval a b)
      (fun x => d.density x * f x))

/-- When the density vanishes outside `[a, b]`, the conditional mean of `d` given `[a, b]` equals
the unconditional mean of the induced probability law. -/
lemma conditionalExpect_id_eq_expect_of_density_eq_zero_outside
    (d : Econlib.Probability.ContDist) {a b : ℝ}
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    d.conditionalExpectOrZero id (Icc a b) = d.toProbDist.expect id := by
  have hsupp : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  have hmass_measure : d.toMeasure (Icc a b) = 1 := by
    unfold Econlib.Probability.ProbDist.supportsOn at hsupp
    simpa [Econlib.Probability.ContDist.toProbDist_toMeasure] using hsupp
  have hmass : ∫ x in Icc a b, d.density x = 1 := by
    calc
      ∫ x in Icc a b, d.density x = ∫ x in Icc a b, (1 : ℝ) ∂d.toMeasure := by
        symm
        simpa [one_mul] using d.setIntegral_toMeasure_eq (fun _ => (1 : ℝ)) measurableSet_Icc
      _ = (d.toMeasure (Icc a b)).toReal := by
        simp [MeasureTheory.Measure.real_def]
      _ = 1 := by rw [hmass_measure]; norm_num
  have hnum : ∫ x in Icc a b, d.density x * x = d.toProbDist.expect id := by
    calc
      ∫ x in Icc a b, d.density x * x = ∫ x in Icc a b, id x ∂d.toMeasure := by
        symm
        simpa using d.setIntegral_toMeasure_eq id measurableSet_Icc
      _ = ∫ x, id x ∂d.toMeasure := by
        rw [← integral_indicator measurableSet_Icc]
        have hae : (Icc a b).indicator id =ᵐ[d.toMeasure] id := by
          filter_upwards
            [Econlib.Probability.ProbDist.ae_mem_of_supportsOn measurableSet_Icc hsupp] with x hx
          simp [hx]
        exact integral_congr_ae hae
      _ = d.toProbDist.expect id := by
        simp [Econlib.Probability.ProbDist.expect,
          Econlib.Probability.ContDist.toProbDist_toMeasure]
  have hpos : 0 < ∫ x in Icc a b, d.density x := by
    linarith [hmass]
  have hnum' : ∫ x in Icc a b, d.density x * id x = d.toProbDist.expect id := by
    simpa using hnum
  rw [d.conditionalExpectOrZero_eq_of_pos id (Icc a b) hpos, hnum', hmass, div_one]

-- `_hub` (`u ≤ b`) places the cutoff inside the support `[a, b]`; the two-point masses
-- `prob_interval u b` / its complement are valid probabilities regardless, so it is unused here.
/-- The two-point law of a continuous distribution `d` at cutoff `u`: A Bernoulli mixture placing
mass `1 - d.prob_interval u b` on the conditional mean of `d` over `[a, u]` and mass
`d.prob_interval u b` on the conditional mean over `[u, b]`. -/
noncomputable def thresholdTwoPointLaw (d : Econlib.Probability.ContDist)
    (a u b : ℝ) (_hub : u ≤ b) : Econlib.Probability.ProbDist ℝ := by
  let p := d.prob_interval u b
  let w : Econlib.Probability.FinDist (Fin 2) :=
    Econlib.Probability.FinDist.bernoulli p
      (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b)
  exact
    Econlib.Probability.ProbDist.map w.toProbDist
      (fun i : Fin 2 =>
        if i = 0 then d.conditionalExpectOrZero id (Icc a u)
        else d.conditionalExpectOrZero id (Icc u b))
      (measurable_of_finite _)

/-- The two-point law equals a finite Bernoulli mixture of Dirac masses at the conditional means
below and above the cutoff. -/
theorem thresholdTwoPointLaw_eq_finMixture_dirac (d : Econlib.Probability.ContDist)
    (a u b : ℝ) (hub : u ≤ b) :
    thresholdTwoPointLaw d a u b hub =
      Econlib.Probability.ProbDist.finMixture
        (Econlib.Probability.FinDist.bernoulli (d.prob_interval u b)
          (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b))
        (fun i : Fin 2 =>
          Econlib.Probability.ProbDist.dirac
            (if i = 0 then d.conditionalExpectOrZero id (Icc a u)
             else d.conditionalExpectOrZero id (Icc u b))) := by
  let p := d.prob_interval u b
  let w : Econlib.Probability.FinDist (Fin 2) :=
    Econlib.Probability.FinDist.bernoulli p
      (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b)
  let stat : Fin 2 → ℝ :=
    fun i => if i = 0 then d.conditionalExpectOrZero id (Icc a u)
      else d.conditionalExpectOrZero id (Icc u b)
  have hstat : Measurable stat := measurable_of_finite _
  ext s hs
  simp only [thresholdTwoPointLaw]
  rw [Econlib.Probability.ProbDist.map_toMeasure]
  rw [Measure.map_apply hstat hs]
  rw [Econlib.Probability.FinDist.toProbDist_toMeasure]
  rw [PMF.toMeasure_apply_fintype]
  change
    (∑ x : Fin 2, (stat ⁻¹' s).indicator (⇑w.toPMF) x) =
      ∑ i : Fin 2, ENNReal.ofReal (w.pmf i) * Measure.dirac (stat i) s
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  -- `toPMF` of the Bernoulli weight, evaluated at each point.
  have hw0 : w.toPMF 0 = ENNReal.ofReal (1 - d.prob_interval u b) := by
    change ENNReal.ofReal (w.pmf 0) = ENNReal.ofReal (1 - d.prob_interval u b)
    simp [w, p, Econlib.Probability.FinDist.bernoulli]
  have hw1 : w.toPMF 1 = ENNReal.ofReal (d.prob_interval u b) := by
    change ENNReal.ofReal (w.pmf 1) = ENNReal.ofReal (d.prob_interval u b)
    simp [w, p, Econlib.Probability.FinDist.bernoulli]
  by_cases h0 : d.conditionalExpectOrZero id (Icc a u) ∈ s
  · by_cases h1 : d.conditionalExpectOrZero id (Icc u b) ∈ s
    · rw [show (stat ⁻¹' s).indicator (⇑w.toPMF) 0 = w.toPMF 0 by simp [stat, h0],
          show (stat ⁻¹' s).indicator (⇑w.toPMF) 1 = w.toPMF 1 by simp [stat, h1],
          hw0, hw1]
      simp [hs, stat, p, w, Econlib.Probability.FinDist.bernoulli, h0, h1]
    · rw [show (stat ⁻¹' s).indicator (⇑w.toPMF) 0 = w.toPMF 0 by simp [stat, h0],
          show (stat ⁻¹' s).indicator (⇑w.toPMF) 1 = 0 by simp [stat, h1],
          hw0]
      simp [hs, stat, p, w, Econlib.Probability.FinDist.bernoulli, h0, h1]
  · by_cases h1 : d.conditionalExpectOrZero id (Icc u b) ∈ s
    · rw [show (stat ⁻¹' s).indicator (⇑w.toPMF) 0 = 0 by simp [stat, h0],
          show (stat ⁻¹' s).indicator (⇑w.toPMF) 1 = w.toPMF 1 by simp [stat, h1],
          hw1]
      simp [hs, stat, p, w, Econlib.Probability.FinDist.bernoulli, h0, h1]
    · rw [show (stat ⁻¹' s).indicator (⇑w.toPMF) 0 = 0 by simp [stat, h0],
          show (stat ⁻¹' s).indicator (⇑w.toPMF) 1 = 0 by simp [stat, h1]]
      simp [hs, stat, p, w, Econlib.Probability.FinDist.bernoulli, h0, h1]

/-- Explicit formula for the expectation of `φ` under the two-point law: The Bernoulli-weighted
average of `φ` at the two conditional means. -/
lemma thresholdTwoPointLaw_expect (d : Econlib.Probability.ContDist)
    (a u b : ℝ) (hub : u ≤ b) (φ : ℝ → ℝ)
    (hφ : AEStronglyMeasurable φ (thresholdTwoPointLaw d a u b hub).toMeasure) :
    (thresholdTwoPointLaw d a u b hub).expect φ =
      (1 - d.prob_interval u b) * φ (d.conditionalExpectOrZero id (Icc a u)) +
        d.prob_interval u b * φ (d.conditionalExpectOrZero id (Icc u b)) := by
  let p := d.prob_interval u b
  let w : Econlib.Probability.FinDist (Fin 2) :=
    Econlib.Probability.FinDist.bernoulli p
      (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b)
  let stat : Fin 2 → ℝ :=
    fun i => if i = 0 then d.conditionalExpectOrZero id (Icc a u)
             else d.conditionalExpectOrZero id (Icc u b)
  have hstat : Measurable stat := measurable_of_finite _
  calc
    (thresholdTwoPointLaw d a u b hub).expect φ
      = (Econlib.Probability.ProbDist.map w.toProbDist stat hstat).expect φ := by
          simp [thresholdTwoPointLaw, p, w, stat]
    _ = w.toProbDist.expect (fun i => φ (stat i)) := by
          exact Econlib.Probability.ProbDist.expect_map w.toProbDist stat hstat φ hφ
    _ = w.expect (fun i => φ (stat i)) := by
          rw [← Econlib.Probability.FinDist.expect_eq_probDist_expect w (fun i => φ (stat i))]
    _ = (1 - p) * φ (d.conditionalExpectOrZero id (Icc a u)) +
          p * φ (d.conditionalExpectOrZero id (Icc u b)) := by
          rw [Econlib.Probability.FinDist.bernoulli_expect_eq]
          simp [stat, p]

/-! ### The two-point law as a `K = 2` conditional-mean partition law

`thresholdTwoPointLaw` is the `K = 2` instance of the general conditional-mean partition law
(`Econlib.Probability.conditionalMeanPartitionLaw`) for the partition `a ≤ u ≤ b`. The bridge
`thresholdTwoPointLaw_eq_conditionalMeanPartitionLaw` derives the support and convex-order
properties of the two-point law from the general `K`-cell machinery. -/

/-- The two-cell ordered cutoff partition of `[a, b]` with the single interior cutoff `u`. -/
noncomputable def thresholdPartition {a u b : ℝ} (hau : a < u) (hub : u < b) :
    OrderedCutoffPartition 2 a b where
  cutoff := ![a, u, b]
  lt := hau.trans hub
  left_eq := rfl
  right_eq := rfl
  monotone := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i <;> simp [hau.le, hub.le]

@[simp] lemma thresholdPartition_cellClosed_zero {a u b : ℝ} (hau : a < u) (hub : u < b) :
    (thresholdPartition hau hub).cellClosed 0 = Icc a u := rfl

@[simp] lemma thresholdPartition_cellClosed_one {a u b : ℝ} (hau : a < u) (hub : u < b) :
    (thresholdPartition hau hub).cellClosed 1 = Icc u b := rfl

/-- The mass of the lower cell of the threshold partition is `d.prob_interval a u`. -/
lemma thresholdPartition_cellMass_zero (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b) :
    Econlib.Probability.cellMass d (thresholdPartition hau hub) 0 = d.prob_interval a u := by
  simp [Econlib.Probability.cellMass, Econlib.Probability.ContDist.prob_interval,
    integral_Icc_eq_integral_Ioc]

/-- The mass of the upper cell of the threshold partition is `d.prob_interval u b`. -/
lemma thresholdPartition_cellMass_one (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b) :
    Econlib.Probability.cellMass d (thresholdPartition hau hub) 1 = d.prob_interval u b := by
  simp [Econlib.Probability.cellMass, Econlib.Probability.ContDist.prob_interval,
    integral_Icc_eq_integral_Ioc]

/-- Both cells of the threshold partition carry positive mass when the density is positive on
`[a, b]`. -/
lemma thresholdPartition_cellMass_pos (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    ∀ j, 0 < Econlib.Probability.cellMass d (thresholdPartition hau hub) j := by
  intro j
  fin_cases j
  · rw [show (⟨0, by omega⟩ : Fin 2) = 0 from rfl, thresholdPartition_cellMass_zero d hau hub]
    exact d.prob_interval_pos_of_pos_density hau
      (fun x hx => hd_pos x (Icc_subset_Icc le_rfl hub.le hx))
      (hd_cont.mono (Icc_subset_Icc le_rfl hub.le))
  · rw [show (⟨1, by omega⟩ : Fin 2) = 1 from rfl, thresholdPartition_cellMass_one d hau hub]
    exact d.prob_interval_pos_of_pos_density hub
      (fun x hx => hd_pos x (Icc_subset_Icc hau.le le_rfl hx))
      (hd_cont.mono (Icc_subset_Icc hau.le le_rfl))

/-- The interval probabilities below and above the threshold sum to one. `K = 2` instance of
`Econlib.Probability.cellMass_sum_eq_one`. -/
theorem threshold_prob_intervals_sum_one (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    d.prob_interval a u + d.prob_interval u b = 1 := by
  have hd_support : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  have h := Econlib.Probability.cellMass_sum_eq_one d (thresholdPartition hau hub) hd_support
  rwa [Fin.sum_univ_two, thresholdPartition_cellMass_zero d hau hub,
    thresholdPartition_cellMass_one d hau hub] at h

/-- **Bridge to the partition law.** The two-point law equals the `K = 2` conditional-mean
partition law: The Bernoulli weight `(1 - p, p)` matches the normalized cell masses (using that the
two cell masses sum to one), and the two atoms are the cell conditional means. -/
theorem thresholdTwoPointLaw_eq_conditionalMeanPartitionLaw (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    thresholdTwoPointLaw d a u b hub.le
      = Econlib.Probability.conditionalMeanPartitionLaw d (thresholdPartition hau hub)
          (thresholdPartition_cellMass_pos d hau hub hd_pos hd_cont) := by
  rw [thresholdTwoPointLaw_eq_finMixture_dirac]
  unfold Econlib.Probability.conditionalMeanPartitionLaw
  have hsum : d.prob_interval a u + d.prob_interval u b = 1 :=
    threshold_prob_intervals_sum_one d hau hub hsupport
  congr 1
  · -- Weights: Bernoulli `(1 - p, p)` = normalized cell masses.
    ext j
    fin_cases j <;>
      simp [Econlib.Probability.FinDist.bernoulli, Econlib.Probability.conditionalMeanWeights,
        Fin.sum_univ_two, thresholdPartition_cellMass_zero d hau hub,
        thresholdPartition_cellMass_one d hau hub, hsum]
    -- Remaining (left-cell) weight identity: `1 - p = p_left` from the masses summing to one.
    linarith
  · -- Atoms: the two conditional means are the cell means.
    funext j
    fin_cases j <;> rfl

/-- Each conditional mean of the two-point law lies in its own subinterval: The lower mean in
`[a, u]` and the upper mean in `[u, b]`. -/
lemma threshold_conditionalExpect_id_mem_subintervals (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    d.conditionalExpectOrZero id (Icc a u) ∈ Icc a u ∧
      d.conditionalExpectOrZero id (Icc u b) ∈ Icc u b := by
  -- Both statements are `cellMean_mem_cell` for the two cells of the threshold partition.
  have hpos := thresholdPartition_cellMass_pos d hau hub hd_pos hd_cont
  refine ⟨?_, ?_⟩
  · simpa [Econlib.Probability.cellMean] using
      Econlib.Probability.cellMean_mem_cell d (thresholdPartition hau hub) 0 (hpos 0) hd_cont
  · simpa [Econlib.Probability.cellMean] using
      Econlib.Probability.cellMean_mem_cell d (thresholdPartition hau hub) 1 (hpos 1) hd_cont

/-- The two-point law is supported on `[a, b]` when the density is positive and continuous there
and vanishes outside. -/
lemma thresholdTwoPointLaw_supportsOn_Icc (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    (thresholdTwoPointLaw d a u b hub.le).supportsOn (Icc a b) := by
  rw [thresholdTwoPointLaw_eq_conditionalMeanPartitionLaw d hau hub hsupport hd_pos hd_cont]
  exact Econlib.Probability.conditionalMeanPartitionLaw_supportsOn d
    (thresholdPartition hau hub) _ hd_cont

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
