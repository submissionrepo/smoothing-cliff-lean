import SmoothingCliff.Racing.AllMixedEquilibria
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Independent heterogeneous mixed profiles

This file builds the product-measure interface needed by the heterogeneous
strict-priority race.  It does not assume identical laws: each bidder has an
arbitrary `BorelMixedStrategy`, and replacing one sampled coordinate by an
independent draw from that bidder's own law preserves the full product law.

The replacement lemma is the measure-theoretic bridge from pure-deviation
best-response inequalities to deviations randomized according to the bidder's
equilibrium law.  Keeping it separate prevents the later racing proof from
silently assuming the independence that it needs.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- The independent product law of a finite heterogeneous mixed profile. -/
def heterogeneousProfileLaw [Fintype ι]
    (strategy : ι → BorelMixedStrategy) : ProbabilityMeasure (ι → NNReal) :=
  ProbabilityMeasure.pi fun i => (strategy i).law

/-- Replacing one coordinate by a fresh draw from that coordinate's own law
preserves a finite, not necessarily identically distributed, product law. -/
theorem measurePreserving_updateHeterogeneousCoordinate
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy) (i : ι) :
    MeasurePreserving
      (fun p : NNReal × (ι → NNReal) => Function.update p.2 i p.1)
      (((strategy i).law : Measure NNReal).prod
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal)))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have hmeas : Measurable
      (fun p : NNReal × (ι → NNReal) => Function.update p.2 i p.1) :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  refine ⟨hmeas, ?_⟩
  change Measure.map
      (fun p : NNReal × (ι → NNReal) => Function.update p.2 i p.1)
      (((strategy i).law : Measure NNReal).prod
        (Measure.pi fun j : ι => ((strategy j).law : Measure NNReal))) =
    Measure.pi fun j : ι => ((strategy j).law : Measure NNReal)
  refine (Measure.pi_eq ?_).symm
  intro s hs
  have hpre :
      (fun p : NNReal × (ι → NNReal) => Function.update p.2 i p.1) ⁻¹'
          Set.pi Set.univ s =
        s i ×ˢ Set.pi Set.univ
          (Function.update s i (Set.univ : Set NNReal)) := by
    ext p
    constructor
    · intro hp
      have hp' : ∀ j, Function.update p.2 i p.1 j ∈ s j := by
        simpa [Set.mem_preimage, Set.mem_univ_pi] using hp
      refine ⟨?_, ?_⟩
      · simpa using hp' i
      · intro j _
        by_cases hj : j = i
        · subst hj
          simp
        · simpa [Function.update_of_ne hj] using hp' j
    · rintro ⟨hown, hrest⟩
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using hown
      · have hjrest := hrest j (Set.mem_univ j)
        rw [Function.update_of_ne hj] at hjrest
        simpa [Function.update_of_ne hj] using hjrest
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre,
    Measure.prod_prod, Measure.pi_pi]
  have hrest : ∀ j ∈ Finset.univ.erase i,
      ((strategy j).law : Measure NNReal)
          (Function.update s i (Set.univ : Set NNReal) j) =
        ((strategy j).law : Measure NNReal) (s j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hproduct :
      (∏ j,
          ((strategy j).law : Measure NNReal)
            (Function.update s i (Set.univ : Set NNReal) j)) =
        ∏ j ∈ Finset.univ.erase i,
          ((strategy j).law : Measure NNReal) (s j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => ((strategy j).law : Measure NNReal)
        (Function.update s i (Set.univ : Set NNReal) j))
      (Finset.mem_univ i)]
    rw [Function.update_self, measure_univ, one_mul]
    exact Finset.prod_congr rfl hrest
  rw [hproduct, Finset.mul_prod_erase Finset.univ
    (fun j => ((strategy j).law : Measure NNReal) (s j))
    (Finset.mem_univ i)]

/-- Fubini form of coordinate replacement.  It is the heterogeneous analogue
of averaging a pure deviation against the bidder's own equilibrium law. -/
theorem integral_updateHeterogeneousCoordinate
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy) (i : ι)
    (f : (ι → NNReal) → ℝ)
    (hf : Integrable f
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) :
    (∫ profile, f profile
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))) =
      ∫ action : NNReal,
        (∫ profile, f (Function.update profile i action)
          ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)))
        ∂((strategy i).law : Measure NNReal) := by
  let replace : NNReal × (ι → NNReal) → (ι → NNReal) :=
    fun p => Function.update p.2 i p.1
  have hpreserving :=
    measurePreserving_updateHeterogeneousCoordinate strategy i
  have hcomp : Integrable (f ∘ replace)
      (((strategy i).law : Measure NNReal).prod
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) :=
    hpreserving.integrable_comp_of_integrable hf
  have hmap :
      (∫ profile, f profile
          ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))) =
        ∫ p, f (replace p)
          ∂(((strategy i).law : Measure NNReal).prod
            (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
    have hfmap : AEStronglyMeasurable f
        (Measure.map replace
          (((strategy i).law : Measure NNReal).prod
            (heterogeneousProfileLaw strategy : Measure (ι → NNReal)))) := by
      rw [hpreserving.map_eq]
      exact hf.aestronglyMeasurable
    conv_lhs => rw [← hpreserving.map_eq]
    exact integral_map hpreserving.measurable.aemeasurable
      hfmap
  rw [hmap]
  simpa [replace, Function.uncurry] using
    (integral_integral (f := fun (action : NNReal)
      (profile : ι → NNReal) =>
        f (Function.update profile i action)) hcomp).symm

/-- Every coordinate of the product profile has the stated marginal first
moment. -/
theorem integral_coordinate_eq_meanAction
    [Fintype ι] (strategy : ι → BorelMixedStrategy) (i : ι) :
    (∫ profile : ι → NNReal, (profile i : ℝ)
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))) =
      (strategy i).meanAction := by
  have heval : MeasurePreserving (Function.eval i)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal))
      ((strategy i).law : Measure NNReal) := by
    change MeasurePreserving (Function.eval i)
      (Measure.pi fun j : ι => ((strategy j).law : Measure NNReal))
      ((strategy i).law : Measure NNReal)
    exact measurePreserving_eval _ i
  have hfmap : AEStronglyMeasurable (fun action : NNReal => (action : ℝ))
      (Measure.map (Function.eval i)
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
    rw [heval.map_eq]
    exact (strategy i).integrable_action.aestronglyMeasurable
  unfold BorelMixedStrategy.meanAction
  rw [← heval.map_eq]
  simpa [Function.comp_def] using
    (integral_map heval.measurable.aemeasurable hfmap).symm

/-- Coordinate actions are integrable under the heterogeneous product law. -/
theorem integrable_coordinate
    [Fintype ι] (strategy : ι → BorelMixedStrategy) (i : ι) :
    Integrable (fun profile : ι → NNReal => (profile i : ℝ))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have heval : MeasurePreserving (Function.eval i)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal))
      ((strategy i).law : Measure NNReal) := by
    change MeasurePreserving (Function.eval i)
      (Measure.pi fun j : ι => ((strategy j).law : Measure NNReal))
      ((strategy i).law : Measure NNReal)
    exact measurePreserving_eval _ i
  simpa [Function.comp_def] using
    heval.integrable_comp_of_integrable (strategy i).integrable_action

/-- With at least two bidders, deleting one bidder from the finite population
leaves a nonempty opponent set. -/
theorem univ_erase_nonempty_of_two [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    (Finset.univ.erase i).Nonempty := by
  apply Finset.Nontrivial.erase_nonempty
  rw [← Finset.one_lt_card_iff_nontrivial, Finset.card_univ]
  omega

/-- Maximum effective score among the opponents of `i`. -/
def opponentMaxEffectiveScore [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : ι → NNReal) : ℝ :=
  (Finset.univ.erase i).sup' (univ_erase_nonempty_of_two hcard i)
    (fun j => premium j + (action j : ℝ))

theorem opponent_effectiveScore_le_max [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i j : ι) (hji : j ≠ i) (action : ι → NNReal) :
    premium j + (action j : ℝ) ≤
      opponentMaxEffectiveScore hcard premium i action := by
  exact Finset.le_sup' (fun k => premium k + (action k : ℝ))
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

/-- The maximum effective opponent score is bounded by any common pointwise
upper bound on all opponents. -/
theorem opponentMaxEffectiveScore_le [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : ι → NNReal) {bound : ℝ}
    (hbound : ∀ j, j ≠ i → premium j + (action j : ℝ) ≤ bound) :
    opponentMaxEffectiveScore hcard premium i action ≤ bound := by
  apply Finset.sup'_le
  intro j hj
  exact hbound j (Finset.ne_of_mem_erase hj)

theorem measurable_opponentMaxEffectiveScore
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) :
    Measurable (opponentMaxEffectiveScore hcard premium i) := by
  unfold opponentMaxEffectiveScore
  let opponents := Finset.univ.erase i
  let hopponents : opponents.Nonempty := univ_erase_nonempty_of_two hcard i
  have hmeas : Measurable
      (opponents.sup' hopponents
        (fun j (action : ι → NNReal) => premium j + (action j : ℝ))) :=
    Finset.measurable_sup' hopponents (fun j _ =>
      measurable_const.add
        (measurable_coe_nnreal_real.comp (measurable_pi_apply j)))
  have heq :
      opponents.sup' hopponents
          (fun j (action : ι → NNReal) => premium j + (action j : ℝ)) =
        (fun action : ι → NNReal =>
          opponents.sup' hopponents
            (fun j => premium j + (action j : ℝ))) := by
    funext action
    exact Finset.sup'_apply hopponents
      (fun j (profile : ι → NNReal) => premium j + (profile j : ℝ)) action
  rw [← heq]
  exact hmeas

theorem opponentMaxEffectiveScore_update_self
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (profile : ι → NNReal) (action : NNReal) :
    opponentMaxEffectiveScore hcard premium i
        (Function.update profile i action) =
      opponentMaxEffectiveScore hcard premium i profile := by
  unfold opponentMaxEffectiveScore
  apply Finset.sup'_congr (univ_erase_nonempty_of_two hcard i) rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Maximum opponent action, before adding heterogeneous value premia. -/
def opponentMaxAction [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : ι → NNReal) : NNReal :=
  (Finset.univ.erase i).sup' (univ_erase_nonempty_of_two hcard i)
    (fun j => action j)

theorem measurable_opponentMaxAction [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    Measurable (opponentMaxAction hcard i) := by
  unfold opponentMaxAction
  let opponents := Finset.univ.erase i
  let hopponents : opponents.Nonempty := univ_erase_nonempty_of_two hcard i
  have hmeas : Measurable
      (opponents.sup' hopponents
        (fun j (action : ι → NNReal) => action j)) :=
    Finset.measurable_sup' hopponents
      (fun j _ => measurable_pi_apply j)
  have heq :
      opponents.sup' hopponents
          (fun j (action : ι → NNReal) => action j) =
        (fun action : ι → NNReal =>
          opponents.sup' hopponents (fun j => action j)) := by
    funext action
    exact Finset.sup'_apply hopponents
      (fun j (profile : ι → NNReal) => profile j) action
  rw [← heq]
  exact hmeas

theorem opponentMaxAction_le_sum [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : ι → NNReal) :
    opponentMaxAction hcard i action ≤
      ∑ j ∈ Finset.univ.erase i, action j := by
  unfold opponentMaxAction
  apply Finset.sup'_le
  intro j hj
  exact Finset.single_le_sum (fun k hk => bot_le) hj

theorem integrable_opponentMaxAction
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    Integrable
      (fun profile : ι → NNReal =>
        (opponentMaxAction hcard i profile : ℝ))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have hsum : Integrable
      (fun profile : ι → NNReal =>
        ∑ j ∈ Finset.univ.erase i, (profile j : ℝ))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_coordinate strategy j
  refine hsum.mono'
    (measurable_coe_nnreal_real.comp
      (measurable_opponentMaxAction hcard i)).aestronglyMeasurable ?_
  filter_upwards with profile
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast opponentMaxAction_le_sum hcard i profile

/-- The pushforward law of the opponents' maximum action. -/
def opponentMaxActionStrategy [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) : BorelMixedStrategy where
  law := (heterogeneousProfileLaw strategy).map
    (measurable_opponentMaxAction hcard i).aemeasurable
  integrable_action := by
    have hmeas := measurable_opponentMaxAction hcard i
    have hstrong : AEStronglyMeasurable
        (fun action : NNReal => (action : ℝ))
        (Measure.map (opponentMaxAction hcard i)
          (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) :=
      measurable_coe_nnreal_real.aestronglyMeasurable
    exact (integrable_map_measure hstrong hmeas.aemeasurable).mpr
      (by simpa [Function.comp_def] using
        integrable_opponentMaxAction strategy hcard i)

/-- The first moment of the pushforward maximum law is the expected maximum
computed on the original product profile. -/
theorem opponentMaxActionStrategy_meanAction
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    (opponentMaxActionStrategy strategy hcard i).meanAction =
      ∫ profile : ι → NNReal,
        (opponentMaxAction hcard i profile : ℝ)
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  unfold BorelMixedStrategy.meanAction opponentMaxActionStrategy
  have hmeas := measurable_opponentMaxAction hcard i
  have hstrong : AEStronglyMeasurable
      (fun action : NNReal => (action : ℝ))
      (Measure.map (opponentMaxAction hcard i)
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) :=
    measurable_coe_nnreal_real.aestronglyMeasurable
  exact integral_map hmeas.aemeasurable hstrong

/-- Total expected latency expenditure of a finite independent profile. -/
def heterogeneousExpectedDissipation [Fintype ι]
    (marginalCost : ℝ) (strategy : ι → BorelMixedStrategy) : ℝ :=
  marginalCost * ∑ i, (strategy i).meanAction

/-- The mean of any opponents' maximum action is bounded by the sum of all
agents' mean actions.  This is the probabilistic inequality used after (H7). -/
theorem opponentMaxActionStrategy_meanAction_le_sum
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    (opponentMaxActionStrategy strategy hcard i).meanAction ≤
      ∑ j, (strategy j).meanAction := by
  have hmaxInt := integrable_opponentMaxAction strategy hcard i
  have hsumInt : Integrable
      (fun profile : ι → NNReal => ∑ j, (profile j : ℝ))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_coordinate strategy j
  have hpoint : ∀ profile : ι → NNReal,
      (opponentMaxAction hcard i profile : ℝ) ≤
        ∑ j, (profile j : ℝ) := by
    intro profile
    have hOpp := opponentMaxAction_le_sum hcard i profile
    have hSubset :
        ∑ j ∈ Finset.univ.erase i, profile j ≤ ∑ j, profile j := by
      exact Finset.sum_le_sum_of_subset (Finset.erase_subset i Finset.univ)
    exact_mod_cast hOpp.trans hSubset
  rw [opponentMaxActionStrategy_meanAction strategy hcard i]
  calc
    (∫ profile : ι → NNReal,
        (opponentMaxAction hcard i profile : ℝ)
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))) ≤
        ∫ profile : ι → NNReal, (∑ j, (profile j : ℝ))
          ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)) :=
      integral_mono hmaxInt hsumInt hpoint
    _ = ∑ j, (∫ profile : ι → NNReal, (profile j : ℝ)
          ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
      rw [integral_finsetSum]
      intro j hj
      exact integrable_coordinate strategy j
    _ = ∑ j, (strategy j).meanAction := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_coordinate_eq_meanAction strategy j

/-- Total dissipation dominates marginal cost times any opponents' maximum
mean action. -/
theorem marginalCost_mul_opponentMaxMean_le_dissipation
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    {marginalCost : ℝ} (hcost : 0 ≤ marginalCost) :
    marginalCost *
        (opponentMaxActionStrategy strategy hcard i).meanAction ≤
      heterogeneousExpectedDissipation marginalCost strategy := by
  unfold heterogeneousExpectedDissipation
  exact mul_le_mul_of_nonneg_left
    (opponentMaxActionStrategy_meanAction_le_sum strategy hcard i) hcost

/-! ## The heterogeneous mixed race -/

/-- Captured premium of bidder `i` after a pure action against one realized
opponent profile. -/
def heterogeneousPureCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) (profile : ι → NNReal) : ℝ :=
  strictPriorityCapturedGap (premium i)
    (premium i + (action : ℝ))
    (opponentMaxEffectiveScore hcard premium i profile)

/-- Expected captured premium of a pure deviation. -/
def heterogeneousPureExpectedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) : ℝ :=
  ∫ profile : ι → NNReal,
    heterogeneousPureCapturedPremium hcard premium i action profile
      ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))

/-- Expected captured premium when every bidder follows the mixed profile. -/
def heterogeneousExpectedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) : ℝ :=
  ∫ profile : ι → NNReal,
    heterogeneousPureCapturedPremium hcard premium i (profile i) profile
      ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))

/-- Expected payoff of a pure deviation in the heterogeneous race. -/
def heterogeneousPureExpectedPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) : ℝ :=
  slotWeight *
      heterogeneousPureExpectedCapturedPremium strategy hcard premium i action -
    marginalCost * (action : ℝ)

/-- Expected equilibrium payoff of one bidder. -/
def heterogeneousExpectedPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) : ℝ :=
  slotWeight * heterogeneousExpectedCapturedPremium strategy hcard premium i -
    marginalCost * (strategy i).meanAction

/-- A bidder's mixed law is a best response when no pure nonnegative action
beats its expected payoff. -/
def IsHeterogeneousBorelMixedBestResponse
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) : Prop :=
  ∀ action : NNReal,
    heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
        premium i action ≤
      heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i

/-- Independent Borel mixed Nash equilibrium of the heterogeneous race. -/
def IsHeterogeneousBorelMixedNash
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) : Prop :=
  ∀ i, IsHeterogeneousBorelMixedBestResponse slotWeight marginalCost
    strategy hcard premium i

theorem measurable_heterogeneousPureCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) :
    Measurable
      (heterogeneousPureCapturedPremium hcard premium i action) := by
  unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
  have hmax := measurable_opponentMaxEffectiveScore hcard premium i
  exact ((measurable_const.add measurable_const).sub hmax).max
    measurable_const |>.min measurable_const

theorem measurable_heterogeneousCapturedPremium_profile
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) :
    Measurable (fun profile : ι → NNReal =>
      heterogeneousPureCapturedPremium hcard premium i (profile i) profile) := by
  unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
  have hown : Measurable (fun profile : ι → NNReal =>
      premium i + (profile i : ℝ)) :=
    measurable_const.add
      (measurable_coe_nnreal_real.comp (measurable_pi_apply i))
  have hmax := measurable_opponentMaxEffectiveScore hcard premium i
  exact (hown.sub hmax).max measurable_const |>.min measurable_const

theorem integrable_heterogeneousPureCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) (action : NNReal) :
    Integrable
      (heterogeneousPureCapturedPremium hcard premium i action)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have hmeas :=
    measurable_heterogeneousPureCapturedPremium hcard premium i action
  refine Integrable.mono' (integrable_const (premium i))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with profile
  unfold heterogeneousPureCapturedPremium
  rw [Real.norm_eq_abs,
    abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
  exact strictPriorityCapturedGap_le_gap

theorem integrable_heterogeneousCapturedPremium_profile
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    Integrable
      (fun profile : ι → NNReal =>
        heterogeneousPureCapturedPremium hcard premium i (profile i) profile)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have hmeas :=
    measurable_heterogeneousCapturedPremium_profile hcard premium i
  refine Integrable.mono' (integrable_const (premium i))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with profile
  unfold heterogeneousPureCapturedPremium
  rw [Real.norm_eq_abs,
    abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
  exact strictPriorityCapturedGap_le_gap

/-- Independent coordinate replacement identifies the mixed captured premium
with the own-law average of pure captured premia. -/
theorem heterogeneousExpectedCapturedPremium_eq_integral_pure
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    heterogeneousExpectedCapturedPremium strategy hcard premium i =
      ∫ action : NNReal,
        heterogeneousPureExpectedCapturedPremium strategy hcard premium i action
        ∂((strategy i).law : Measure NNReal) := by
  let f : (ι → NNReal) → ℝ := fun profile =>
    heterogeneousPureCapturedPremium hcard premium i (profile i) profile
  have hf : Integrable f
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) :=
    integrable_heterogeneousCapturedPremium_profile strategy hcard premium
      i hpremium
  rw [heterogeneousExpectedCapturedPremium]
  have hreplace := integral_updateHeterogeneousCoordinate strategy i f hf
  rw [hreplace]
  apply integral_congr_ae
  filter_upwards with action
  unfold heterogeneousPureExpectedCapturedPremium f
  apply integral_congr_ae
  filter_upwards with profile
  unfold heterogeneousPureCapturedPremium
  rw [Function.update_self,
    opponentMaxEffectiveScore_update_self hcard premium i profile action]

/-- Expected equilibrium payoff is the own-law average of pure-deviation
payoffs. -/
theorem heterogeneousExpectedPayoff_eq_integral_pure
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i =
      ∫ action : NNReal,
        heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i action
        ∂((strategy i).law : Measure NNReal) := by
  have hcaptured : Integrable (fun action : NNReal =>
      heterogeneousPureExpectedCapturedPremium strategy hcard premium i action)
      ((strategy i).law : Measure NNReal) := by
    have hprofile := integrable_heterogeneousCapturedPremium_profile strategy
      hcard premium i hpremium
    have hreplace := measurePreserving_updateHeterogeneousCoordinate strategy i
    have hcomp : Integrable
        (fun p : NNReal × (ι → NNReal) =>
          heterogeneousPureCapturedPremium hcard premium i p.1 p.2)
        (((strategy i).law : Measure NNReal).prod
          (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
      refine Integrable.mono' (integrable_const (premium i)) ?_ ?_
      · have hown : Measurable (fun p : NNReal × (ι → NNReal) =>
            premium i + (p.1 : ℝ)) :=
          measurable_const.add
            (measurable_coe_nnreal_real.comp measurable_fst)
        have hmax : Measurable (fun p : NNReal × (ι → NNReal) =>
            opponentMaxEffectiveScore hcard premium i p.2) :=
          (measurable_opponentMaxEffectiveScore hcard premium i).comp
            measurable_snd
        have hmeas : Measurable (fun p : NNReal × (ι → NNReal) =>
            heterogeneousPureCapturedPremium hcard premium i p.1 p.2) := by
          unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
          exact (hown.sub hmax).max measurable_const |>.min measurable_const
        exact hmeas.aestronglyMeasurable
      · filter_upwards with p
        unfold heterogeneousPureCapturedPremium
        rw [Real.norm_eq_abs,
          abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
        exact strictPriorityCapturedGap_le_gap
    simpa [heterogeneousPureExpectedCapturedPremium] using
      hcomp.integral_prod_left
  have hcost := (strategy i).integrable_action.const_mul marginalCost
  rw [heterogeneousExpectedPayoff,
    heterogeneousExpectedCapturedPremium_eq_integral_pure strategy hcard
      premium i hpremium,
    BorelMixedStrategy.meanAction]
  unfold heterogeneousPureExpectedPayoff
  rw [integral_sub (hcaptured.const_mul slotWeight) hcost,
    integral_const_mul, integral_const_mul]

end

end SmoothingCliff.Racing
