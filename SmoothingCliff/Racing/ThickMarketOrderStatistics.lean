import SmoothingCliff.Frontier.InterimBridgeMeanField
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Order.Lattice

/-!
# Top-two order statistics in bounded i.i.d. markets

This file isolates the order-statistic step used in the thick-market theorem.
For a finite profile, the runner-up is the maximum of the minima over all
distinct pairs.  Under an i.i.d. product law supported on `[0, dbar]`, a fixed
upper-tail mass forces this runner-up to approach `dbar` in `L1`; the gap
between the largest and second-largest draws then vanishes in `L1` as well.

The probability argument is deliberately finite.  If the runner-up lies below
`dbar - epsilon`, then after deleting a suitable coordinate every remaining
coordinate lies below that threshold.  A union bound and the exact product
measure of these coordinate rectangles give a geometric bound.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace SmoothingCliff.Racing

noncomputable section

variable {ι : Type*}

/-- Ordered pairs of distinct agents. -/
def distinctPairs [Fintype ι] [DecidableEq ι] : Finset (ι × ι) :=
  (Finset.univ.product Finset.univ).filter fun p => p.1 ≠ p.2

theorem distinctPairs_nonempty [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) : (distinctPairs (ι := ι)).Nonempty := by
  have hone : 1 < Fintype.card ι := by omega
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp hone
  exact ⟨(i, j), by simp [distinctPairs, hij]⟩

/-- The second-largest coordinate, represented without choosing a sorting
permutation: maximize the smaller coordinate over all distinct pairs. -/
def runnerUp [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) : (ι → ℝ) → ℝ :=
  (distinctPairs (ι := ι)).sup' (distinctPairs_nonempty hcard)
    fun p profile => min (profile p.1) (profile p.2)

/-- The largest coordinate. -/
def profileTop [Fintype ι] [Nonempty ι] : (ι → ℝ) → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i profile => profile i

theorem measurable_runnerUp [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) :
    Measurable (runnerUp (ι := ι) hcard) := by
  unfold runnerUp
  apply Finset.measurable_sup'
  intro p hp
  fun_prop

theorem measurable_profileTop [Fintype ι] [Nonempty ι] :
    Measurable (profileTop (ι := ι)) := by
  unfold profileTop
  apply Finset.measurable_sup'
  intro i hi
  fun_prop

theorem runnerUp_le_of_forall_le [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) {bound : ℝ}
    (hbound : ∀ i, profile i ≤ bound) :
    runnerUp hcard profile ≤ bound := by
  simp only [runnerUp, Finset.sup'_apply]
  apply Finset.sup'_le
  intro p hp
  exact min_le_iff.mpr (Or.inl (hbound p.1))

theorem runnerUp_nonneg [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ profile i) :
    0 ≤ runnerUp hcard profile := by
  obtain ⟨p, hp⟩ := distinctPairs_nonempty (ι := ι) hcard
  have hmin : 0 ≤ min (profile p.1) (profile p.2) :=
    le_min (hnonneg p.1) (hnonneg p.2)
  exact hmin.trans (by
    simpa only [runnerUp, Finset.sup'_apply] using
      (Finset.le_sup'
        (f := fun q : ι × ι => min (profile q.1) (profile q.2)) hp))

theorem runnerUp_le_profileTop [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) :
    runnerUp hcard profile ≤ profileTop profile := by
  apply runnerUp_le_of_forall_le hcard profile
  intro i
  simpa only [profileTop, Finset.sup'_apply] using
    (Finset.le_sup' (f := profile) (Finset.mem_univ i))

theorem profileTop_le_of_forall_le [Fintype ι] [Nonempty ι]
    (profile : ι → ℝ) {bound : ℝ} (hbound : ∀ i, profile i ≤ bound) :
    profileTop profile ≤ bound := by
  simp only [profileTop, Finset.sup'_apply]
  apply Finset.sup'_le
  intro i hi
  exact hbound i

theorem profileTop_nonneg [Fintype ι] [Nonempty ι]
    (profile : ι → ℝ) (hnonneg : ∀ i, 0 ≤ profile i) :
    0 ≤ profileTop profile := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  exact (hnonneg i).trans (by
    simpa only [profileTop, Finset.sup'_apply] using
      (Finset.le_sup' (f := profile) (Finset.mem_univ i)))

theorem endpoint_runnerUp_bounds [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) {endpoint : ℝ}
    (hnonneg : ∀ i, 0 ≤ profile i) (hupper : ∀ i, profile i ≤ endpoint) :
    0 ≤ endpoint - runnerUp hcard profile ∧
      endpoint - runnerUp hcard profile ≤ endpoint := by
  constructor
  · linarith [runnerUp_le_of_forall_le hcard profile hupper]
  · linarith [runnerUp_nonneg hcard profile hnonneg]

theorem top_runnerUp_gap_bounds [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) {endpoint : ℝ}
    (hupper : ∀ i, profile i ≤ endpoint) :
    0 ≤ profileTop profile - runnerUp hcard profile ∧
      profileTop profile - runnerUp hcard profile ≤
        endpoint - runnerUp hcard profile := by
  constructor
  · linarith [runnerUp_le_profileTop hcard profile]
  · linarith [profileTop_le_of_forall_le profile hupper]

/-! ## A finite upper-tail event bound -/

/-- The cylinder on which every coordinate except `i` lies below
`threshold`.  The distinguished coordinate is unrestricted. -/
def allButBelow [Fintype ι] [DecidableEq ι]
    (i : ι) (threshold : ℝ) : Set (ι → ℝ) :=
  ((Finset.univ.erase i : Finset ι) : Set ι).pi
    fun _ => Set.Iio threshold

theorem measurableSet_allButBelow [Fintype ι] [DecidableEq ι]
    (i : ι) (threshold : ℝ) :
    MeasurableSet (allButBelow i threshold) := by
  apply MeasurableSet.pi (Finset.countable_toSet (Finset.univ.erase i))
  intro j hj
  exact measurableSet_Iio

theorem profileLaw_allButBelow [Fintype ι] [DecidableEq ι]
    (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι) (threshold : ℝ) :
    SmoothingCliff.Frontier.profileLaw (ι := ι) F
        (allButBelow i threshold) =
      (F (Set.Iio threshold)) ^ (Fintype.card ι - 1) := by
  unfold SmoothingCliff.Frontier.profileLaw allButBelow
  rw [Measure.pi_pi_finset]
  simp [Finset.card_erase_of_mem]

/-- A profile whose runner-up is below `threshold` has all but at most one
coordinate below `threshold`. -/
theorem runnerUp_lt_subset_iUnion_allButBelow
    [Fintype ι] [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι)
    (threshold : ℝ) :
    {profile : ι → ℝ | runnerUp hcard profile < threshold} ⊆
      ⋃ i : ι, allButBelow i threshold := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro profile hbad
  by_cases hhigh : ∃ i, threshold ≤ profile i
  · obtain ⟨i, hi⟩ := hhigh
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    by_contra hjbelow
    have hjhigh : threshold ≤ profile j := le_of_not_gt hjbelow
    have hp : (i, j) ∈ distinctPairs (ι := ι) := by
      simp [distinctPairs, hji.symm]
    have hpair : min (profile i) (profile j) ≤ runnerUp hcard profile := by
      simpa only [runnerUp, Finset.sup'_apply] using
        (Finset.le_sup'
          (f := fun q : ι × ι => min (profile q.1) (profile q.2)) hp)
    exact (not_lt_of_ge ((le_min hi hjhigh).trans hpair)) hbad
  · let i : ι := Classical.choice (inferInstance : Nonempty ι)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    intro j hj
    exact lt_of_not_ge (fun hjhigh => hhigh ⟨j, hjhigh⟩)

theorem measurableSet_runnerUp_lt [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (threshold : ℝ) :
    MeasurableSet {profile : ι → ℝ | runnerUp hcard profile < threshold} :=
  measurableSet_lt (measurable_runnerUp hcard) measurable_const

/-- Union-bound form of the probability that the runner-up misses a fixed
upper interval. -/
theorem profileLaw_runnerUp_lt_le
    [Fintype ι] [DecidableEq ι] (hcard : 2 ≤ Fintype.card ι)
    (F : Measure ℝ) [IsProbabilityMeasure F] (threshold : ℝ) :
    SmoothingCliff.Frontier.profileLaw (ι := ι) F
        {profile | runnerUp hcard profile < threshold} ≤
      ∑ i : ι,
        SmoothingCliff.Frontier.profileLaw (ι := ι) F
          (allButBelow i threshold) := by
  calc
    _ ≤ SmoothingCliff.Frontier.profileLaw (ι := ι) F
          (⋃ i : ι, allButBelow i threshold) :=
      measure_mono (runnerUp_lt_subset_iUnion_allButBelow hcard threshold)
    _ ≤ _ := measure_iUnion_fintype_le _ _

/-- For `n+2` bidders, the failure probability is bounded by the geometric
quantity `(n+2) q^(n+1)`, where `q` is the probability of lying below the
fixed threshold. -/
theorem profileLaw_runnerUp_lt_le_geometric
    (F : Measure ℝ) [IsProbabilityMeasure F] (threshold : ℝ) (n : ℕ) :
    SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F
        {profile | runnerUp (ι := Fin (n + 2)) (by simp) profile < threshold} ≤
      (n + 2) * (F (Set.Iio threshold)) ^ (n + 1) := by
  calc
    _ ≤ ∑ i : Fin (n + 2),
          SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F
            (allButBelow i threshold) :=
      profileLaw_runnerUp_lt_le (by simp) F threshold
    _ = _ := by
      simp [profileLaw_allButBelow]

theorem profileLaw_runnerUp_lt_real_le_geometric
    (F : Measure ℝ) [IsProbabilityMeasure F] (threshold : ℝ) (n : ℕ) :
    (SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F).real
        {profile | runnerUp (ι := Fin (n + 2)) (by simp) profile < threshold} ≤
      (n + 2 : ℝ) * (F.real (Set.Iio threshold)) ^ (n + 1) := by
  have h := ENNReal.toReal_mono (by finiteness)
    (profileLaw_runnerUp_lt_le_geometric F threshold n)
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, Nat.cast_add, Nat.cast_ofNat] using h

theorem geometric_runnerUp_bound_tendsto_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (n + 2 : ℝ) * q ^ (n + 1))
      atTop (𝓝 0) := by
  have hn := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hsum : Tendsto
      (fun n : ℕ => (n : ℝ) * q ^ n + 2 * q ^ n) atTop (𝓝 0) := by
    simpa using hn.add (hp.const_mul 2)
  have hmul : Tendsto
      (fun n : ℕ => q * ((n : ℝ) * q ^ n + 2 * q ^ n))
      atTop (𝓝 0) := by
    simpa using hsum.const_mul q
  convert hmul using 1
  · funext n
    rw [pow_succ]
    ring

/-- Positive mass in a fixed upper interval makes the probability that the
runner-up misses that interval vanish as the population grows. -/
theorem profileLaw_runnerUp_failure_tendsto_zero
    (F : Measure ℝ) [IsProbabilityMeasure F] (threshold : ℝ)
    (hupperMass : 0 < F.real (Set.Ici threshold)) :
    Tendsto
      (fun n : ℕ =>
        (SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F).real
          {profile |
            runnerUp (ι := Fin (n + 2)) (by simp) profile < threshold})
      atTop (𝓝 0) := by
  have hcompl := probReal_compl_eq_one_sub (μ := F)
    (s := Set.Iio threshold) measurableSet_Iio
  have hq1 : F.real (Set.Iio threshold) < 1 := by
    rw [Set.compl_Iio] at hcompl
    linarith
  apply squeeze_zero
  · intro n
    exact measureReal_nonneg
  · intro n
    exact profileLaw_runnerUp_lt_real_le_geometric F threshold n
  · exact geometric_runnerUp_bound_tendsto_zero measureReal_nonneg hq1

/-! ## Bounded support and `L1` convergence -/

theorem ae_profile_mem_Icc [Fintype ι]
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    ∀ᵐ profile ∂SmoothingCliff.Frontier.profileLaw (ι := ι) F,
      ∀ i, profile i ∈ Set.Icc 0 endpoint := by
  rw [ae_all_iff]
  intro i
  have hqmp := (measurePreserving_eval (fun _ : ι => F) i).quasiMeasurePreserving
  exact hqmp.ae hSupport

/-- The endpoint shortfall of the runner-up. -/
def runnerUpShortfall [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (endpoint : ℝ) (profile : ι → ℝ) : ℝ :=
  endpoint - runnerUp hcard profile

theorem measurable_runnerUpShortfall [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (endpoint : ℝ) :
    Measurable (runnerUpShortfall hcard endpoint) :=
  measurable_const.sub (measurable_runnerUp hcard)

theorem integrable_runnerUpShortfall [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (F : Measure ℝ)
    [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    Integrable (runnerUpShortfall hcard endpoint)
      (SmoothingCliff.Frontier.profileLaw (ι := ι) F) := by
  refine (integrable_const endpoint).mono'
    (measurable_runnerUpShortfall hcard endpoint).aestronglyMeasurable ?_
  filter_upwards [ae_profile_mem_Icc F hSupport] with profile hprofile
  have hb := endpoint_runnerUp_bounds hcard profile
    (fun i => (hprofile i).1) (fun i => (hprofile i).2)
  unfold runnerUpShortfall
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

theorem runnerUpShortfall_nonneg_ae [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (F : Measure ℝ)
    [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    ∀ᵐ profile ∂SmoothingCliff.Frontier.profileLaw (ι := ι) F,
      0 ≤ runnerUpShortfall hcard endpoint profile := by
  filter_upwards [ae_profile_mem_Icc F hSupport] with profile hprofile
  exact (endpoint_runnerUp_bounds hcard profile
    (fun i => (hprofile i).1) (fun i => (hprofile i).2)).1

/-- Splitting according to whether the runner-up is within `epsilon` of the
endpoint bounds expected shortfall by `epsilon` plus the bounded-support loss
on the failure event. -/
theorem integral_runnerUpShortfall_le
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint epsilon : ℝ}
    (hEpsilon : 0 ≤ epsilon)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    (∫ profile,
        runnerUpShortfall (ι := Fin (n + 2)) (by simp) endpoint profile
        ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F) ≤
      epsilon + endpoint *
        (SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F).real
          {profile |
            runnerUp (ι := Fin (n + 2)) (by simp) profile < endpoint - epsilon} := by
  let μ := SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F
  let bad : Set (Fin (n + 2) → ℝ) :=
    {profile | runnerUp (ι := Fin (n + 2)) (by simp) profile < endpoint - epsilon}
  have hBadMeas : MeasurableSet bad := measurableSet_runnerUp_lt (by simp) _
  have hGapInt : Integrable
      (runnerUpShortfall (ι := Fin (n + 2)) (by simp) endpoint) μ :=
    integrable_runnerUpShortfall (by simp) F hSupport
  have hRhsInt : Integrable
      (fun profile : Fin (n + 2) → ℝ =>
        epsilon + endpoint * bad.indicator (fun _ => (1 : ℝ)) profile) μ := by
    fun_prop
  have hpoint : ∀ᵐ profile ∂μ,
      runnerUpShortfall (ι := Fin (n + 2)) (by simp) endpoint profile ≤
        epsilon + endpoint * bad.indicator (fun _ => (1 : ℝ)) profile := by
    filter_upwards [ae_profile_mem_Icc F hSupport] with profile hprofile
    have hb := endpoint_runnerUp_bounds (ι := Fin (n + 2)) (by simp) profile
      (fun i => (hprofile i).1) (fun i => (hprofile i).2)
    by_cases hbad : profile ∈ bad
    · simp [hbad]
      unfold runnerUpShortfall
      linarith
    · have hnear : endpoint - epsilon ≤
          runnerUp (ι := Fin (n + 2)) (by simp) profile := by
        exact le_of_not_gt hbad
      simp [hbad]
      unfold runnerUpShortfall
      linarith
  calc
    _ ≤ ∫ profile, (epsilon + endpoint *
          bad.indicator (fun _ => (1 : ℝ)) profile) ∂μ :=
      integral_mono_ae hGapInt hRhsInt hpoint
    _ = epsilon + endpoint * μ.real bad := by
      have hind : (∫ profile : Fin (n + 2) → ℝ,
          bad.indicator (fun _ => (1 : ℝ)) profile ∂μ) = μ.real bad := by
        simpa only [Pi.one_apply] using
          (integral_indicator_one (μ := μ) hBadMeas)
      have hepsInt : Integrable
          (fun _ : Fin (n + 2) → ℝ => epsilon) μ := integrable_const _
      have hscaledInt : Integrable
          (fun profile : Fin (n + 2) → ℝ =>
            endpoint * bad.indicator (fun _ => (1 : ℝ)) profile) μ :=
        ((integrable_const (1 : ℝ)).indicator hBadMeas).const_mul endpoint
      rw [integral_add hepsInt hscaledInt, integral_const,
        integral_const_mul, hind]
      simp [μ]
    _ = _ := rfl

/-- The `L1` distance between the runner-up and the upper endpoint. -/
def expectedAbsRunnerUpShortfall
    (F : Measure ℝ) (endpoint : ℝ) (n : ℕ) : ℝ :=
  ∫ profile,
    |runnerUpShortfall (ι := Fin (n + 2)) (by simp) endpoint profile|
    ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F

theorem expectedAbsRunnerUpShortfall_eq
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    expectedAbsRunnerUpShortfall F endpoint n =
      ∫ profile,
        runnerUpShortfall (ι := Fin (n + 2)) (by simp) endpoint profile
        ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F := by
  unfold expectedAbsRunnerUpShortfall
  apply integral_congr_ae
  filter_upwards [runnerUpShortfall_nonneg_ae (ι := Fin (n + 2))
    (by simp) F hSupport] with profile hnonneg
  exact abs_of_nonneg hnonneg

/-- A local linear lower bound on upper-tail mass is enough for the
runner-up to converge to the endpoint in `L1`. -/
theorem expectedAbsRunnerUpShortfall_tendsto_zero
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius : ℝ}
    (hTailConstant : 0 < tailConstant)
    (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto (expectedAbsRunnerUpShortfall F endpoint) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    filter_upwards with n
    exact hlower.trans_le (integral_nonneg fun _ => abs_nonneg _)
  · intro upper hupper
    let epsilon := min (tailRadius / 2) (upper / 2)
    have hEpsilon : 0 < epsilon := by
      dsimp [epsilon]
      exact lt_min (half_pos hTailRadius) (half_pos hupper)
    have hEpsilonTail : epsilon ≤ tailRadius := by
      calc
        epsilon ≤ tailRadius / 2 := min_le_left _ _
        _ ≤ tailRadius := by linarith
    have hEpsilonUpper : epsilon ≤ upper / 2 := min_le_right _ _
    have hUpperMargin : 0 < upper - epsilon := by linarith
    have hUpperMass : 0 < F.real (Set.Ici (endpoint - epsilon)) := by
      exact (mul_pos hTailConstant hEpsilon).trans_le
        (hTail epsilon hEpsilon hEpsilonTail)
    have hFailure := profileLaw_runnerUp_failure_tendsto_zero F
      (endpoint - epsilon) hUpperMass
    have hScaled : Tendsto
        (fun n : ℕ => endpoint *
          (SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F).real
            {profile |
              runnerUp (ι := Fin (n + 2)) (by simp) profile <
                endpoint - epsilon}) atTop (𝓝 0) := by
      simpa using hFailure.const_mul endpoint
    have hEventually := (tendsto_order.mp hScaled).2
      (upper - epsilon) hUpperMargin
    filter_upwards [hEventually] with n hn
    rw [expectedAbsRunnerUpShortfall_eq F hSupport n]
    calc
      _ ≤ epsilon + endpoint *
          (SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F).real
            {profile |
              runnerUp (ι := Fin (n + 2)) (by simp) profile <
                endpoint - epsilon} :=
        integral_runnerUpShortfall_le F hEpsilon.le hSupport n
      _ < upper := by linarith

/-! ## Expectation and top--runner-up interfaces -/

/-- Expected runner-up under the `n+2`-fold product law. -/
def expectedRunnerUp (F : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ profile,
    runnerUp (ι := Fin (n + 2)) (by simp) profile
    ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F

/-- The top-minus-runner-up spacing of a finite profile. -/
def topRunnerUpGap [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) : ℝ :=
  profileTop profile - runnerUp hcard profile

theorem measurable_topRunnerUpGap [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) :
    Measurable (topRunnerUpGap hcard) :=
  measurable_profileTop.sub (measurable_runnerUp hcard)

theorem topRunnerUpGap_nonneg [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (profile : ι → ℝ) :
    0 ≤ topRunnerUpGap hcard profile := by
  unfold topRunnerUpGap
  linarith [runnerUp_le_profileTop hcard profile]

theorem integrable_runnerUp [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (F : Measure ℝ)
    [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    Integrable (runnerUp hcard)
      (SmoothingCliff.Frontier.profileLaw (ι := ι) F) := by
  have hshort := integrable_runnerUpShortfall hcard F hSupport
  have hdiff := (integrable_const endpoint).sub hshort
  convert hdiff using 1
  ext profile
  simp [runnerUpShortfall]

theorem integrable_profileTop [Fintype ι] [Nonempty ι]
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    Integrable (profileTop (ι := ι))
      (SmoothingCliff.Frontier.profileLaw (ι := ι) F) := by
  refine (integrable_const endpoint).mono'
    measurable_profileTop.aestronglyMeasurable ?_
  filter_upwards [ae_profile_mem_Icc F hSupport] with profile hprofile
  have hnonneg : 0 ≤ profileTop profile :=
    profileTop_nonneg profile (fun i => (hprofile i).1)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact profileTop_le_of_forall_le profile (fun i => (hprofile i).2)

theorem integrable_topRunnerUpGap [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hcard : 2 ≤ Fintype.card ι) (F : Measure ℝ)
    [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) :
    Integrable (topRunnerUpGap hcard)
      (SmoothingCliff.Frontier.profileLaw (ι := ι) F) := by
  exact (integrable_profileTop F hSupport).sub
    (integrable_runnerUp hcard F hSupport)

/-- Expected top-minus-runner-up spacing under the `n+2`-fold product law. -/
def expectedTopRunnerUpGap (F : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ profile,
    topRunnerUpGap (ι := Fin (n + 2)) (by simp) profile
    ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F

/-- Expected largest coordinate under the `n+2`-fold product law. -/
def expectedProfileTop (F : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ profile,
    profileTop (ι := Fin (n + 2)) profile
    ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F

/-- The expected absolute top--runner-up spacing.  The absolute value is
redundant mathematically, but this definition exposes the exact `L1` quantity
used by downstream limit arguments. -/
def expectedAbsTopRunnerUpGap (F : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ profile,
    |topRunnerUpGap (ι := Fin (n + 2)) (by simp) profile|
    ∂SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F

theorem expectedAbsTopRunnerUpGap_eq
    (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    expectedAbsTopRunnerUpGap F n = expectedTopRunnerUpGap F n := by
  unfold expectedAbsTopRunnerUpGap expectedTopRunnerUpGap
  apply integral_congr_ae
  filter_upwards with profile
  exact abs_of_nonneg
    (topRunnerUpGap_nonneg (ι := Fin (n + 2)) (by simp) profile)

theorem expectedRunnerUp_eq_endpoint_sub_shortfall
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    expectedRunnerUp F n =
      endpoint - expectedAbsRunnerUpShortfall F endpoint n := by
  have hrunner := integrable_runnerUp (ι := Fin (n + 2)) (by simp) F hSupport
  have hshort :
      expectedAbsRunnerUpShortfall F endpoint n =
        endpoint - expectedRunnerUp F n := by
    rw [expectedAbsRunnerUpShortfall_eq F hSupport n]
    unfold runnerUpShortfall expectedRunnerUp
    rw [integral_sub (integrable_const endpoint) hrunner, integral_const]
    simp
  linarith

/-- The expected runner-up converges to the upper endpoint. -/
theorem expectedRunnerUp_tendsto_endpoint
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius : ℝ}
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto (expectedRunnerUp F) atTop (𝓝 endpoint) := by
  have hshort := expectedAbsRunnerUpShortfall_tendsto_zero F
    hTailConstant hTailRadius hSupport hTail
  have hrepr : expectedRunnerUp F =
      fun n => endpoint - expectedAbsRunnerUpShortfall F endpoint n := by
    funext n
    exact expectedRunnerUp_eq_endpoint_sub_shortfall F hSupport n
  rw [hrepr]
  simpa using tendsto_const_nhds.sub hshort

theorem expectedTopRunnerUpGap_nonneg
    (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    0 ≤ expectedTopRunnerUpGap F n := by
  unfold expectedTopRunnerUpGap
  exact integral_nonneg fun profile =>
    topRunnerUpGap_nonneg (ι := Fin (n + 2)) (by simp) profile

/-- The expected top--runner-up spacing is dominated by the runner-up's
endpoint shortfall. -/
theorem expectedTopRunnerUpGap_le_expectedAbsRunnerUpShortfall
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    expectedTopRunnerUpGap F n ≤
      expectedAbsRunnerUpShortfall F endpoint n := by
  let μ := SmoothingCliff.Frontier.profileLaw (ι := Fin (n + 2)) F
  have hgap := integrable_topRunnerUpGap (ι := Fin (n + 2))
    (by simp) F hSupport
  have hshort := integrable_runnerUpShortfall (ι := Fin (n + 2))
    (by simp) F hSupport
  rw [expectedAbsRunnerUpShortfall_eq F hSupport n]
  unfold expectedTopRunnerUpGap
  apply integral_mono_ae hgap hshort
  filter_upwards [ae_profile_mem_Icc F hSupport] with profile hprofile
  exact (top_runnerUp_gap_bounds (ι := Fin (n + 2)) (by simp) profile
    (fun i => (hprofile i).2)).2

/-- The largest and second-largest draws coalesce in expected absolute
distance. -/
theorem expectedTopRunnerUpGap_tendsto_zero
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius : ℝ}
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto (expectedTopRunnerUpGap F) atTop (𝓝 0) := by
  apply squeeze_zero
  · exact expectedTopRunnerUpGap_nonneg F
  · exact expectedTopRunnerUpGap_le_expectedAbsRunnerUpShortfall F hSupport
  · exact expectedAbsRunnerUpShortfall_tendsto_zero F
      hTailConstant hTailRadius hSupport hTail

theorem expectedAbsTopRunnerUpGap_tendsto_zero
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius : ℝ}
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto (expectedAbsTopRunnerUpGap F) atTop (𝓝 0) := by
  have hrepr : expectedAbsTopRunnerUpGap F = expectedTopRunnerUpGap F := by
    funext n
    exact expectedAbsTopRunnerUpGap_eq F n
  rw [hrepr]
  exact expectedTopRunnerUpGap_tendsto_zero F
    hTailConstant hTailRadius hSupport hTail

theorem expectedProfileTop_eq_runnerUp_add_gap
    (F : Measure ℝ) [IsProbabilityMeasure F] {endpoint : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    expectedProfileTop F n =
      expectedRunnerUp F n + expectedTopRunnerUpGap F n := by
  have hrunner := integrable_runnerUp (ι := Fin (n + 2)) (by simp) F hSupport
  have hgap := integrable_topRunnerUpGap (ι := Fin (n + 2))
    (by simp) F hSupport
  unfold expectedProfileTop expectedRunnerUp expectedTopRunnerUpGap
  rw [← integral_add hrunner hgap]
  apply integral_congr_ae
  filter_upwards with profile
  unfold topRunnerUpGap
  ring

/-- The expected largest draw converges to the same upper endpoint as the
runner-up. -/
theorem expectedProfileTop_tendsto_endpoint
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius : ℝ}
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto (expectedProfileTop F) atTop (𝓝 endpoint) := by
  have hrunner := expectedRunnerUp_tendsto_endpoint F
    hTailConstant hTailRadius hSupport hTail
  have hgap := expectedTopRunnerUpGap_tendsto_zero F
    hTailConstant hTailRadius hSupport hTail
  have hrepr : expectedProfileTop F =
      fun n => expectedRunnerUp F n + expectedTopRunnerUpGap F n := by
    funext n
    exact expectedProfileTop_eq_runnerUp_add_gap F hSupport n
  rw [hrepr]
  simpa using hrunner.add hgap

end

end SmoothingCliff.Racing
