/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.ConvexOrder

/-!
# Threshold persuasion: Existence of cutoffs realizing a target posterior mean

Under continuity and positive-density assumptions, the cumulative probability is strictly monotone
in the cutoff, so the sender can choose a precise cutoff to match any target probability mass. The
intermediate-value theorem then yields existence, and strict monotonicity uniqueness, of threshold
cutoffs realizing any prescribed left or right posterior mean.

## Main statements

* `probInterval_left_strictMonoOn` — strict monotonicity of `u ↦ P(a ≤ X ≤ u)` in the cutoff.
* `exists_cutoff_of_probInterval` — for any target mass in `[0, P(a ≤ X ≤ b)]` there exists a
  cutoff `u ∈ [a, b]` achieving it.
* `exists_cutoff_of_probInterval_open` — open-interval refinement of the above for masses in
  `(0, P(a ≤ X ≤ b))`.
* `existsUnique_cutoff_of_leftPosteriorMean` — unique cutoff `u ∈ (a, b)` with
  `𝔼[X | X ∈ [a, u]] = mL` whenever `mL ∈ (a, 𝔼[X])`.
* `existsUnique_thresholdSplit_of_leftPosteriorMean` — strengthening that also determines the right
  posterior mean and the mean-preservation identity.
* `exists_thresholdLaw_convexOrder_of_leftPosteriorMean` — the threshold two-point law is a
  mean-preserving spread of `d` for any admissible left posterior mean.
* Symmetric right-posterior-mean variants of each of the above three results.
* `exists_twoPointFinMixture_of_leftPosteriorMean` /
  `exists_twoPointFinMixture_of_rightPosteriorMean` — restate the two-point law as an explicit
  Bernoulli mixture of Dirac masses at the posterior means.

## Notes

That the cutoff signal is optimal for the sender (for the excess-over-threshold objective) is
`thresholdTwoPointLaw_isOptimal_excessOverThreshold` in
`Persuasion.Continuous.Threshold.Optimality`.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, threshold persuasion, cutoff, cdf, posterior mean, convex order
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

/-- The map `u ↦ P(a ≤ X ≤ u)` is strictly increasing on `[a, b]` when the density is continuous
and positive on `[a, b]`. -/
theorem probInterval_left_strictMonoOn (d : Econlib.Probability.ContDist)
    -- kept so the statement is non-vacuous: without `a < b`, `Icc a b` is a subsingleton.
    {a b : ℝ} (_hab : a < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    StrictMonoOn (fun u => d.prob_interval a u) (Icc a b) := by
  intro u₁ hu₁ u₂ hu₂ hu₁₂
  have hd_pos_sub : ∀ x ∈ Icc u₁ u₂, 0 < d.density x := fun x hx =>
    hd_pos x (Icc_subset_Icc hu₁.1 hu₂.2 hx)
  have hd_cont_sub : ContinuousOn d.density (Icc u₁ u₂) :=
    hd_cont.mono (Icc_subset_Icc hu₁.1 hu₂.2)
  have hcdf : d.cdf u₁ < d.cdf u₂ :=
    d.cdf_strictMono hu₁₂ hd_pos_sub hd_cont_sub
  change d.prob_interval a u₁ < d.prob_interval a u₂
  rw [d.prob_interval_eq_of_le hu₁.1, d.prob_interval_eq_of_le hu₂.1]
  linarith

/-- For any target mass `q ∈ [0, P(a ≤ X ≤ b)]` there exists a cutoff `u ∈ [a, b]` with
`P(a ≤ X ≤ u) = q`. -/
theorem exists_cutoff_of_probInterval
    (d : Econlib.Probability.ContDist) {a b : ℝ} (hab : a < b)
    (q : ℝ) (hq : q ∈ Icc 0 (d.prob_interval a b)) :
    ∃ u ∈ Icc a b, d.prob_interval a u = q := by
  -- On `[a, b]` the cutoff mass agrees with the continuous map `u ↦ cdf u - cdf a` (the identity
  -- only holds for `a ≤ u`, so we transfer continuity via `EqOn` rather than a global rewrite).
  have hcont :
      ContinuousOn (fun u => d.prob_interval a u) (Icc a b) :=
    (((Econlib.Probability.contdist_cdf_continuous d).sub continuous_const).continuousOn).congr
      (fun u hu => d.prob_interval_eq_of_le hu.1)
  have hsurj :
      Set.SurjOn (fun u => d.prob_interval a u) (Icc a b)
        (Icc ((fun u => d.prob_interval a u) a) ((fun u => d.prob_interval a u) b)) :=
    hcont.surjOn_Icc (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le)
  have hq' : q ∈ Icc ((fun u => d.prob_interval a u) a) ((fun u => d.prob_interval a u) b) := by
    simpa [Econlib.Probability.ContDist.prob_interval_self] using hq
  exact hsurj hq'

/-- For any target mass `q ∈ (0, P(a ≤ X ≤ b))` there exists an interior cutoff `u ∈ (a, b)` with
`P(a ≤ X ≤ u) = q`. -/
theorem exists_cutoff_of_probInterval_open
    (d : Econlib.Probability.ContDist) {a b : ℝ} (hab : a < b)
    (q : ℝ) (hq : q ∈ Ioo 0 (d.prob_interval a b)) :
    ∃ u ∈ Ioo a b, d.prob_interval a u = q := by
  obtain ⟨u, hu, huq⟩ := exists_cutoff_of_probInterval d hab q ⟨hq.1.le, hq.2.le⟩
  have hu_ne_a : u ≠ a := by
    intro h_eq
    subst h_eq
    have : q = 0 := by
      simpa [Econlib.Probability.ContDist.prob_interval_self] using huq.symm
    exact (lt_irrefl 0) (by simpa [this] using hq.1)
  have hu_ne_b : u ≠ b := by
    intro h_eq
    subst h_eq
    exact (lt_irrefl q) (by simpa [huq] using hq.2)
  refine ⟨u, ⟨lt_of_le_of_ne hu.1 hu_ne_a.symm, lt_of_le_of_ne hu.2 hu_ne_b⟩, huq⟩

/-- The left conditional mean `u ↦ 𝔼[X | X ∈ [a, u]]` is continuous on `(a, b]` when the density
vanishes outside `[a, b]` and is continuous and positive on `[a, b]`. -/
theorem continuousOn_leftPosteriorMean_of_compactSupport
    -- kept so the statement is non-vacuous: without `a < b`, `Ioc a b` is empty.
    (d : Econlib.Probability.ContDist) {a b : ℝ} (_hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    ContinuousOn (fun u => d.conditionalExpectOrZero id (Icc a u)) (Ioc a b) := by
  let num : ℝ → ℝ := fun u => ∫ x in a..u, d.density x * x
  let den : ℝ → ℝ := fun u => ∫ x in a..u, d.density x
  have hsupp : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  have hid_measure : Integrable id d.toMeasure := by
    simpa [Econlib.Probability.ContDist.toProbDist_toMeasure] using
      (Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc hsupp)
  have hweighted_int : Integrable (fun x => d.density x * x) := by
    simpa using (d.integrable_toMeasure_iff (f := id)).mp hid_measure
  have hnum_cont : Continuous num := by
    unfold num
    simpa using hweighted_int.continuous_primitive a
  have hden_cont : Continuous den := by
    unfold den
    simpa using d.integrable.continuous_primitive a
  have hquot_cont : ContinuousOn (fun u => num u / den u) (Ioc a b) := by
    apply hnum_cont.continuousOn.div hden_cont.continuousOn
    intro u hu hzero
    have hd_pos_left : ∀ x ∈ Icc a u, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc le_rfl hu.2 hx)
    have hd_cont_left : ContinuousOn d.density (Icc a u) :=
      hd_cont.mono (Icc_subset_Icc le_rfl hu.2)
    have hprob : 0 < d.prob_interval a u :=
      d.prob_interval_pos_of_pos_density hu.1 hd_pos_left hd_cont_left
    exact (ne_of_gt hprob) (by
      simpa [den, Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hu.1.le] using hzero)
  refine hquot_cont.congr ?_
  intro u hu
  have hd_pos_left : ∀ x ∈ Icc a u, 0 < d.density x := fun x hx =>
    hd_pos x (Icc_subset_Icc le_rfl hu.2 hx)
  have hd_cont_left : ContinuousOn d.density (Icc a u) :=
    hd_cont.mono (Icc_subset_Icc le_rfl hu.2)
  have hpos_prob : 0 < d.prob_interval a u :=
    d.prob_interval_pos_of_pos_density hu.1 hd_pos_left hd_cont_left
  have hpos_set : 0 < ∫ x in Icc a u, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu.1.le] using hpos_prob
  change d.conditionalExpectOrZero id (Icc a u) = num u / den u
  rw [d.conditionalExpectOrZero_eq_of_pos id (Icc a u) hpos_set]
  simp [num, den, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hu.1.le]

/-- The right conditional mean `u ↦ 𝔼[X | X ∈ [u, b]]` is continuous on `[a, b)` when the density
vanishes outside `[a, b]` and is continuous and positive on `[a, b]`. -/
theorem continuousOn_rightPosteriorMean_of_compactSupport
    -- kept so the statement is non-vacuous: without `a < b`, `Ico a b` is empty.
    (d : Econlib.Probability.ContDist) {a b : ℝ} (_hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    ContinuousOn (fun u => d.conditionalExpectOrZero id (Icc u b)) (Ico a b) := by
  let numL : ℝ → ℝ := fun u => ∫ x in a..u, d.density x * x
  let denL : ℝ → ℝ := fun u => ∫ x in a..u, d.density x
  let numR : ℝ → ℝ := fun u => ∫ x in u..b, d.density x * x
  let denR : ℝ → ℝ := fun u => ∫ x in u..b, d.density x
  have hsupp : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  have hid_measure : Integrable id d.toMeasure := by
    simpa [Econlib.Probability.ContDist.toProbDist_toMeasure] using
      (Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc hsupp)
  have hweighted_int : Integrable (fun x => d.density x * x) := by
    simpa using (d.integrable_toMeasure_iff (f := id)).mp hid_measure
  have hnumL_cont : Continuous numL := by
    unfold numL
    simpa using hweighted_int.continuous_primitive a
  have hdenL_cont : Continuous denL := by
    unfold denL
    simpa using d.integrable.continuous_primitive a
  have hnumR_base : ContinuousOn (fun u => numL b - numL u) (Ico a b) :=
    (continuous_const.sub hnumL_cont).continuousOn
  have hdenR_base : ContinuousOn (fun u => denL b - denL u) (Ico a b) :=
    (continuous_const.sub hdenL_cont).continuousOn
  have hnumR_cont : ContinuousOn numR (Ico a b) := by
    refine hnumR_base.congr ?_
    intro u hu
    unfold numR numL
    have key : ∫ x in u..b, d.density x * x =
        (∫ x in a..b, d.density x * x) - ∫ x in a..u, d.density x * x :=
      (intervalIntegral.integral_interval_sub_left
        hweighted_int.intervalIntegrable hweighted_int.intervalIntegrable).symm
    simp only [key]
  have hdenR_cont : ContinuousOn denR (Ico a b) := by
    refine hdenR_base.congr ?_
    intro u hu
    unfold denR denL
    have key : ∫ x in u..b, d.density x =
        (∫ x in a..b, d.density x) - ∫ x in a..u, d.density x :=
      (intervalIntegral.integral_interval_sub_left
        d.integrable.intervalIntegrable d.integrable.intervalIntegrable).symm
    simp only [key]
  have hquot_cont : ContinuousOn (fun u => numR u / denR u) (Ico a b) := by
    apply hnumR_cont.div hdenR_cont
    intro u hu hzero
    have hd_pos_right : ∀ x ∈ Icc u b, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc hu.1 le_rfl hx)
    have hd_cont_right : ContinuousOn d.density (Icc u b) :=
      hd_cont.mono (Icc_subset_Icc hu.1 le_rfl)
    have hprob : 0 < d.prob_interval u b :=
      d.prob_interval_pos_of_pos_density hu.2 hd_pos_right hd_cont_right
    exact (ne_of_gt hprob) (by
      simpa [denR, Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hu.2.le] using hzero)
  refine hquot_cont.congr ?_
  intro u hu
  have hd_pos_right : ∀ x ∈ Icc u b, 0 < d.density x := fun x hx =>
    hd_pos x (Icc_subset_Icc hu.1 le_rfl hx)
  have hd_cont_right : ContinuousOn d.density (Icc u b) :=
    hd_cont.mono (Icc_subset_Icc hu.1 le_rfl)
  have hpos_prob : 0 < d.prob_interval u b :=
    d.prob_interval_pos_of_pos_density hu.2 hd_pos_right hd_cont_right
  have hpos_set : 0 < ∫ x in Icc u b, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hu.2.le] using hpos_prob
  change d.conditionalExpectOrZero id (Icc u b) = numR u / denR u
  rw [d.conditionalExpectOrZero_eq_of_pos id (Icc u b) hpos_set]
  simp [numR, denR, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hu.2.le]

/-- For any left posterior mean `mL ∈ (a, 𝔼[X])` there is a unique cutoff `u ∈ (a, b)` with
`𝔼[X | X ∈ [a, u]] = mL`. -/
theorem existsUnique_cutoff_of_leftPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mL : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmL : mL ∈ Ioo a (d.toProbDist.expect id)) :
    ∃! u ∈ Ioo a b, d.conditionalExpectOrZero id (Icc a u) = mL := by
  let f : ℝ → ℝ := fun u => d.conditionalExpectOrZero id (Icc a u)
  have hf_cont : ContinuousOn f (Ioc a b) := by
    simpa [f] using continuousOn_leftPosteriorMean_of_compactSupport
      d hab hsupport hd_pos hd_cont
  have hf_left :
      Filter.Tendsto f (nhdsWithin a (Ioc a b)) (nhds a) := by
    simpa [f] using
      Econlib.Probability.tendsto_conditionalExpect_id_left_boundary d a b hd_pos hd_cont hab
  have hbval : f b = d.toProbDist.expect id := by
    simpa [f] using conditionalExpect_id_eq_expect_of_density_eq_zero_outside d hsupport
  have hf_right :
      Filter.Tendsto f (pure b) (nhds (d.toProbDist.expect id)) := by
    simpa [hbval] using tendsto_pure_nhds f b
  letI : (nhdsWithin a (Ioc a b)).NeBot := left_nhdsWithin_Ioc_neBot hab
  have himage : mL ∈ f '' Ioc a b := by
    exact (isPreconnected_Ioc.intermediate_value_Ioo
      (l₁ := nhdsWithin a (Ioc a b)) (l₂ := pure b)
      (show nhdsWithin a (Ioc a b) ≤ Filter.principal (Ioc a b) from inf_le_right) (by
        simpa [Filter.principal_singleton] using
          (Filter.principal_mono.mpr (singleton_subset_iff.mpr (right_mem_Ioc.mpr hab))))
      hf_cont hf_left hf_right) hmL
  obtain ⟨u, huIoc, huval⟩ := himage
  have hu_ne_b : u ≠ b := by
    intro h_eq
    subst h_eq
    have hEq : mL = d.toProbDist.expect id := huval.symm.trans hbval
    exact (lt_irrefl (d.toProbDist.expect id)) (hEq ▸ hmL.2)
  have huIoo : u ∈ Ioo a b := ⟨huIoc.1, lt_of_le_of_ne huIoc.2 hu_ne_b⟩
  refine ⟨u, ⟨huIoo, by simpa [f] using huval⟩, ?_⟩
  intro v hv
  rcases hv with ⟨hvIoo, hvval⟩
  have hstrict : StrictMonoOn f (Ioc a b) := by
    simpa [f] using
      Econlib.Probability.conditionalExpect_strictMono_left d id a b strictMonoOn_id
        hd_pos continuousOn_id hd_cont hab
  have huIoc' : u ∈ Ioc a b := ⟨huIoo.1, huIoo.2.le⟩
  have hvIoc' : v ∈ Ioc a b := ⟨hvIoo.1, hvIoo.2.le⟩
  exact ((hstrict.eq_iff_eq huIoc' hvIoc').mp
    (huval.trans (by simpa [f] using hvval.symm))).symm

/-- For any left posterior mean `mL ∈ (a, 𝔼[X])` there is a unique cutoff `u ∈ (a, b)` such that
`𝔼[X | X ∈ [a, u]] = mL`, the right posterior mean `𝔼[X | X ∈ [u, b]]` lies in `(𝔼[X], b)`, and the
weighted average of the two posterior means equals `𝔼[X]`. -/
theorem existsUnique_thresholdSplit_of_leftPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mL : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmL : mL ∈ Ioo a (d.toProbDist.expect id)) :
    ∃! u ∈ Ioo a b,
      d.conditionalExpectOrZero id (Icc a u) = mL ∧
      d.conditionalExpectOrZero id (Icc u b) ∈ Ioo (d.toProbDist.expect id) b ∧
      d.prob_interval a u * mL +
        d.prob_interval u b * d.conditionalExpectOrZero id (Icc u b) = d.toProbDist.expect id := by
  obtain ⟨u, hu, hu_unique⟩ :=
    existsUnique_cutoff_of_leftPosteriorMean d hab hsupport hd_pos hd_cont hmL
  rcases hu with ⟨huIoo, huval⟩
  have hleft_prob : 0 < d.prob_interval a u := by
    have hd_pos_left : ∀ x ∈ Icc a u, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc le_rfl huIoo.2.le hx)
    have hd_cont_left : ContinuousOn d.density (Icc a u) :=
      hd_cont.mono (Icc_subset_Icc le_rfl huIoo.2.le)
    exact d.prob_interval_pos_of_pos_density huIoo.1 hd_pos_left hd_cont_left
  have hright_prob : 0 < d.prob_interval u b := by
    have hd_pos_right : ∀ x ∈ Icc u b, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc huIoo.1.le le_rfl hx)
    have hd_cont_right : ContinuousOn d.density (Icc u b) :=
      hd_cont.mono (Icc_subset_Icc huIoo.1.le le_rfl)
    exact d.prob_interval_pos_of_pos_density huIoo.2 hd_pos_right hd_cont_right
  have hmean :
      d.prob_interval a u * mL +
        d.prob_interval u b * d.conditionalExpectOrZero id (Icc u b) = d.toProbDist.expect id := by
    simpa [huval] using
      threshold_two_point_mean_identity d huIoo.1 huIoo.2 hsupport hd_cont
  have hsum : d.prob_interval a u + d.prob_interval u b = 1 :=
    threshold_prob_intervals_sum_one d huIoo.1 huIoo.2 hsupport
  have hright_gt_mean : d.toProbDist.expect id < d.conditionalExpectOrZero id (Icc u b) := by
    by_contra hnot
    have hright_le : d.conditionalExpectOrZero id (Icc u b) ≤ d.toProbDist.expect id :=
      not_lt.mp hnot
    have hleft_lt :
        d.prob_interval a u * mL < d.prob_interval a u * d.toProbDist.expect id :=
      mul_lt_mul_of_pos_left hmL.2 hleft_prob
    have hright_le' :
        d.prob_interval u b * d.conditionalExpectOrZero id (Icc u b) ≤
          d.prob_interval u b * d.toProbDist.expect id :=
      mul_le_mul_of_nonneg_left hright_le (le_of_lt hright_prob)
    -- the two probability-weighted `expect` terms recombine to `expect` via `hsum`
    have hcombine :
        d.prob_interval a u * d.toProbDist.expect id +
          d.prob_interval u b * d.toProbDist.expect id = d.toProbDist.expect id := by
      rw [← add_mul, hsum, one_mul]
    -- weighted sum is strictly below `expect`, contradicting the mean identity `hmean`
    linarith [hmean, hcombine, hleft_lt, hright_le']
  have hright_lt_b : d.conditionalExpectOrZero id (Icc u b) < b := by
    let v : ℝ := (u + b) / 2
    have hvIoo : v ∈ Ioo u b := by
      constructor
      · dsimp [v]
        nlinarith [huIoo.2]
      · dsimp [v]
        nlinarith [huIoo.2]
    have hvIco : v ∈ Ico a b := ⟨le_of_lt (lt_trans huIoo.1 hvIoo.1), hvIoo.2⟩
    have huIco : u ∈ Ico a b := ⟨huIoo.1.le, huIoo.2⟩
    have hstrict : StrictMonoOn (fun t => d.conditionalExpectOrZero id (Icc t b)) (Ico a b) := by
      simpa using
        Econlib.Probability.conditionalExpect_strictMono_right d id a b strictMonoOn_id
          hd_pos continuousOn_id hd_cont hab
    have huv_lt :
        d.conditionalExpectOrZero id (Icc u b) < d.conditionalExpectOrZero id (Icc v b) :=
      hstrict huIco hvIco hvIoo.1
    have hv_mem :
        d.conditionalExpectOrZero id (Icc v b) ∈ Icc v b := by
      exact (threshold_conditionalExpect_id_mem_subintervals d
        (lt_trans huIoo.1 hvIoo.1) hvIoo.2 hd_pos hd_cont).2
    exact lt_of_lt_of_le huv_lt hv_mem.2
  refine ⟨u, ⟨huIoo, huval, ⟨⟨hright_gt_mean, hright_lt_b⟩, hmean⟩⟩, ?_⟩
  intro v hv
  rcases hv with ⟨hvIoo, hvval, -, -⟩
  exact hu_unique v ⟨hvIoo, hvval⟩

/-- For any admissible left posterior mean `mL ∈ (a, 𝔼[X])`, the threshold two-point law with
cutoff at the unique `u` achieving `mL` is a mean-preserving spread of `d` on `[a, b]`. -/
theorem exists_thresholdLaw_convexOrder_of_leftPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mL : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmL : mL ∈ Ioo a (d.toProbDist.expect id)) :
    ∃ u, ∃ hu : u ∈ Ioo a b,
      d.conditionalExpectOrZero id (Icc a u) = mL ∧
      Econlib.Probability.ConvexOrderOnIcc a b
        (thresholdTwoPointLaw d a u b hu.2.le) d.toProbDist := by
  obtain ⟨u, hu, _⟩ :=
    existsUnique_thresholdSplit_of_leftPosteriorMean d hab hsupport hd_pos hd_cont hmL
  rcases hu with ⟨huIoo, huval, -, -⟩
  exact ⟨u, huIoo, huval,
    thresholdTwoPointLaw_convexOrderOnIcc d huIoo.1 huIoo.2 hsupport hd_pos hd_cont⟩

/-- For any right posterior mean `mR ∈ (𝔼[X], b)` there is a unique cutoff `u ∈ (a, b)` with
`𝔼[X | X ∈ [u, b]] = mR`. -/
theorem existsUnique_cutoff_of_rightPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mR : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmR : mR ∈ Ioo (d.toProbDist.expect id) b) :
    ∃! u ∈ Ioo a b, d.conditionalExpectOrZero id (Icc u b) = mR := by
  let f : ℝ → ℝ := fun u => d.conditionalExpectOrZero id (Icc u b)
  have hf_cont : ContinuousOn f (Ico a b) := by
    simpa [f] using continuousOn_rightPosteriorMean_of_compactSupport
      d hab hsupport hd_pos hd_cont
  have ha_val : f a = d.toProbDist.expect id := by
    simpa [f] using conditionalExpect_id_eq_expect_of_density_eq_zero_outside d hsupport
  have hf_left :
      Filter.Tendsto f (pure a) (nhds (d.toProbDist.expect id)) := by
    simpa [ha_val] using tendsto_pure_nhds f a
  have hf_right :
      Filter.Tendsto f (nhdsWithin b (Ico a b)) (nhds b) := by
    simpa [f] using
      Econlib.Probability.tendsto_conditionalExpect_id_right_boundary d a b hd_pos hd_cont hab
  letI : (nhdsWithin b (Ico a b)).NeBot := right_nhdsWithin_Ico_neBot hab
  have himage : mR ∈ f '' Ico a b := by
    exact (isPreconnected_Ico.intermediate_value_Ioo
      (l₁ := pure a) (l₂ := nhdsWithin b (Ico a b))
      (by
        simpa [Filter.principal_singleton] using
          (Filter.principal_mono.mpr (singleton_subset_iff.mpr (left_mem_Ico.mpr hab))))
      (show nhdsWithin b (Ico a b) ≤ Filter.principal (Ico a b) from inf_le_right)
      hf_cont hf_left hf_right) hmR
  obtain ⟨u, huIco, huval⟩ := himage
  have hu_ne_a : u ≠ a := by
    intro h_eq
    subst h_eq
    have hEq : mR = d.toProbDist.expect id := huval.symm.trans ha_val
    exact (lt_irrefl (d.toProbDist.expect id)) (hmR.1.trans_eq hEq)
  have huIoo : u ∈ Ioo a b := ⟨lt_of_le_of_ne huIco.1 hu_ne_a.symm, huIco.2⟩
  refine ⟨u, ⟨huIoo, by simpa [f] using huval⟩, ?_⟩
  intro v hv
  rcases hv with ⟨hvIoo, hvval⟩
  have hstrict : StrictMonoOn f (Ico a b) := by
    simpa [f] using
      Econlib.Probability.conditionalExpect_strictMono_right d id a b strictMonoOn_id
        hd_pos continuousOn_id hd_cont hab
  have huIco' : u ∈ Ico a b := ⟨huIoo.1.le, huIoo.2⟩
  have hvIco' : v ∈ Ico a b := ⟨hvIoo.1.le, hvIoo.2⟩
  exact ((hstrict.eq_iff_eq huIco' hvIco').mp
    (huval.trans (by simpa [f] using hvval.symm))).symm

/-- For any right posterior mean `mR ∈ (𝔼[X], b)` there is a unique cutoff `u ∈ (a, b)` such that
`𝔼[X | X ∈ [u, b]] = mR`, the left posterior mean `𝔼[X | X ∈ [a, u]]` lies in `(a, 𝔼[X])`, and the
weighted average of the two posterior means equals `𝔼[X]`. -/
theorem existsUnique_thresholdSplit_of_rightPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mR : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmR : mR ∈ Ioo (d.toProbDist.expect id) b) :
    ∃! u ∈ Ioo a b,
      d.conditionalExpectOrZero id (Icc u b) = mR ∧
      d.conditionalExpectOrZero id (Icc a u) ∈ Ioo a (d.toProbDist.expect id) ∧
      d.prob_interval a u * d.conditionalExpectOrZero id (Icc a u) +
        d.prob_interval u b * mR = d.toProbDist.expect id := by
  obtain ⟨u, hu, hu_unique⟩ :=
    existsUnique_cutoff_of_rightPosteriorMean d hab hsupport hd_pos hd_cont hmR
  rcases hu with ⟨huIoo, huval⟩
  have hleft_prob : 0 < d.prob_interval a u := by
    have hd_pos_left : ∀ x ∈ Icc a u, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc le_rfl huIoo.2.le hx)
    have hd_cont_left : ContinuousOn d.density (Icc a u) :=
      hd_cont.mono (Icc_subset_Icc le_rfl huIoo.2.le)
    exact d.prob_interval_pos_of_pos_density huIoo.1 hd_pos_left hd_cont_left
  have hright_prob : 0 < d.prob_interval u b := by
    have hd_pos_right : ∀ x ∈ Icc u b, 0 < d.density x := fun x hx =>
      hd_pos x (Icc_subset_Icc huIoo.1.le le_rfl hx)
    have hd_cont_right : ContinuousOn d.density (Icc u b) :=
      hd_cont.mono (Icc_subset_Icc huIoo.1.le le_rfl)
    exact d.prob_interval_pos_of_pos_density huIoo.2 hd_pos_right hd_cont_right
  have hmean :
      d.prob_interval a u * d.conditionalExpectOrZero id (Icc a u) +
        d.prob_interval u b * mR = d.toProbDist.expect id := by
    simpa [huval] using
      threshold_two_point_mean_identity d huIoo.1 huIoo.2 hsupport hd_cont
  have hsum : d.prob_interval a u + d.prob_interval u b = 1 :=
    threshold_prob_intervals_sum_one d huIoo.1 huIoo.2 hsupport
  have hleft_lt_mean : d.conditionalExpectOrZero id (Icc a u) < d.toProbDist.expect id := by
    by_contra hnot
    have hleft_ge : d.toProbDist.expect id ≤ d.conditionalExpectOrZero id (Icc a u) :=
      not_lt.mp hnot
    have hleft_ge' :
        d.prob_interval a u * d.toProbDist.expect id ≤
          d.prob_interval a u * d.conditionalExpectOrZero id (Icc a u) :=
      mul_le_mul_of_nonneg_left hleft_ge (le_of_lt hleft_prob)
    have hright_lt' :
        d.prob_interval u b * d.toProbDist.expect id <
          d.prob_interval u b * mR :=
      mul_lt_mul_of_pos_left hmR.1 hright_prob
    -- the two probability-weighted `expect` terms recombine to `expect` via `hsum`
    have hcombine :
        d.prob_interval a u * d.toProbDist.expect id +
          d.prob_interval u b * d.toProbDist.expect id = d.toProbDist.expect id := by
      rw [← add_mul, hsum, one_mul]
    -- weighted sum is strictly above `expect`, contradicting the mean identity `hmean`
    linarith [hmean, hcombine, hleft_ge', hright_lt']
  have hleft_gt_a : a < d.conditionalExpectOrZero id (Icc a u) := by
    let v : ℝ := (a + u) / 2
    have hvIoo : v ∈ Ioo a u := by
      constructor
      · dsimp [v]
        nlinarith [huIoo.1]
      · dsimp [v]
        nlinarith [huIoo.1]
    have hvIoc : v ∈ Ioc a b := ⟨hvIoo.1, le_of_lt (lt_trans hvIoo.2 huIoo.2)⟩
    have huIoc : u ∈ Ioc a b := ⟨huIoo.1, huIoo.2.le⟩
    have hstrict : StrictMonoOn (fun t => d.conditionalExpectOrZero id (Icc a t)) (Ioc a b) := by
      simpa using
        Econlib.Probability.conditionalExpect_strictMono_left d id a b strictMonoOn_id
          hd_pos continuousOn_id hd_cont hab
    have hvu_lt :
        d.conditionalExpectOrZero id (Icc a v) < d.conditionalExpectOrZero id (Icc a u) :=
      hstrict hvIoc huIoc hvIoo.2
    have hv_mem :
        d.conditionalExpectOrZero id (Icc a v) ∈ Icc a v := by
      exact (threshold_conditionalExpect_id_mem_subintervals d hvIoo.1
        (lt_trans hvIoo.2 huIoo.2) hd_pos hd_cont).1
    exact lt_of_le_of_lt hv_mem.1 hvu_lt
  refine ⟨u, ⟨huIoo, huval, ⟨⟨hleft_gt_a, hleft_lt_mean⟩, hmean⟩⟩, ?_⟩
  intro v hv
  rcases hv with ⟨hvIoo, hvval, -, -⟩
  exact hu_unique v ⟨hvIoo, hvval⟩

/-- For any admissible right posterior mean `mR ∈ (𝔼[X], b)`, the threshold two-point law with
cutoff at the unique `u` achieving `mR` is a mean-preserving spread of `d` on `[a, b]`. -/
theorem exists_thresholdLaw_convexOrder_of_rightPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mR : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmR : mR ∈ Ioo (d.toProbDist.expect id) b) :
    ∃ u, ∃ hu : u ∈ Ioo a b,
      d.conditionalExpectOrZero id (Icc u b) = mR ∧
      Econlib.Probability.ConvexOrderOnIcc a b
        (thresholdTwoPointLaw d a u b hu.2.le) d.toProbDist := by
  obtain ⟨u, hu, _⟩ :=
    existsUnique_thresholdSplit_of_rightPosteriorMean d hab hsupport hd_pos hd_cont hmR
  rcases hu with ⟨huIoo, huval, -, -⟩
  exact ⟨u, huIoo, huval,
    thresholdTwoPointLaw_convexOrderOnIcc d huIoo.1 huIoo.2 hsupport hd_pos hd_cont⟩

/-- For any admissible left posterior mean `mL ∈ (a, 𝔼[X])`, the threshold two-point law is equal
to a Bernoulli mixture of Dirac masses at `mL` and the corresponding right posterior mean. -/
theorem exists_twoPointFinMixture_of_leftPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mL : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmL : mL ∈ Ioo a (d.toProbDist.expect id)) :
    ∃ u, ∃ hu : u ∈ Ioo a b, ∃ mR ∈ Ioo (d.toProbDist.expect id) b,
      d.prob_interval a u * mL + d.prob_interval u b * mR = d.toProbDist.expect id ∧
      thresholdTwoPointLaw d a u b hu.2.le =
        Econlib.Probability.ProbDist.finMixture
          (Econlib.Probability.FinDist.bernoulli (d.prob_interval u b)
            (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b))
          (fun i : Fin 2 =>
            Econlib.Probability.ProbDist.dirac (if i = 0 then mL else mR)) := by
  obtain ⟨u, hu, _⟩ :=
    existsUnique_thresholdSplit_of_leftPosteriorMean d hab hsupport hd_pos hd_cont hmL
  rcases hu with ⟨huIoo, huval, hmR, hmean⟩
  refine ⟨u, huIoo, d.conditionalExpectOrZero id (Icc u b), hmR, hmean, ?_⟩
  simpa [huval] using thresholdTwoPointLaw_eq_finMixture_dirac d a u b huIoo.2.le

/-- For any admissible right posterior mean `mR ∈ (𝔼[X], b)`, the threshold two-point law is equal
to a Bernoulli mixture of Dirac masses at the corresponding left posterior mean and `mR`. -/
theorem exists_twoPointFinMixture_of_rightPosteriorMean
    (d : Econlib.Probability.ContDist) {a b mR : ℝ} (hab : a < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hmR : mR ∈ Ioo (d.toProbDist.expect id) b) :
    ∃ u, ∃ hu : u ∈ Ioo a b, ∃ mL ∈ Ioo a (d.toProbDist.expect id),
      d.prob_interval a u * mL + d.prob_interval u b * mR = d.toProbDist.expect id ∧
      thresholdTwoPointLaw d a u b hu.2.le =
        Econlib.Probability.ProbDist.finMixture
          (Econlib.Probability.FinDist.bernoulli (d.prob_interval u b)
            (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b))
          (fun i : Fin 2 =>
            Econlib.Probability.ProbDist.dirac (if i = 0 then mL else mR)) := by
  obtain ⟨u, hu, _⟩ :=
    existsUnique_thresholdSplit_of_rightPosteriorMean d hab hsupport hd_pos hd_cont hmR
  rcases hu with ⟨huIoo, huval, hmL, hmean⟩
  refine ⟨u, huIoo, d.conditionalExpectOrZero id (Icc a u), hmL, hmean, ?_⟩
  simpa [huval] using thresholdTwoPointLaw_eq_finMixture_dirac d a u b huIoo.2.le

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
