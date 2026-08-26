import SmoothingCliff.Racing.HeterogeneousMixedProfile
import Econlib.GameTheory.Strategic.Bayesian.Measurable.MixedExtension

/-!
# Existence for the heterogeneous strict-priority race

This file supplies the compactification step behind existence of an
independent Borel mixed equilibrium.  Bidder `i` never needs an action above
`w₁ dᵢ / κ`: the captured premium is at most `dᵢ`, while action zero gives a
nonnegative payoff.  The resulting product of compact intervals is a
continuous game, so Econlib's measurable mixed-extension existence theorem
applies.  The final part maps the compact lotteries back to the paper's
`BorelMixedStrategy` interface and restores deviations on the whole
nonnegative half-line.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open Econlib.GameTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- The compactification bound `w₁ dᵢ / κ`, represented in `NNReal`. -/
def heterogeneousActionBound
    (slotWeight marginalCost premium : ℝ) : NNReal :=
  Real.toNNReal (slotWeight * premium / marginalCost)

@[simp] theorem coe_heterogeneousActionBound
    {slotWeight marginalCost premium : ℝ}
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    (hpremium : 0 ≤ premium) :
    (heterogeneousActionBound slotWeight marginalCost premium : ℝ) =
      slotWeight * premium / marginalCost := by
  unfold heterogeneousActionBound
  rw [Real.coe_toNNReal]
  exact div_nonneg (mul_nonneg hweight hpremium) hcost.le

/-- Bidder `i`'s compact action interval. -/
abbrev HeterogeneousCompactAction
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι) :=
  Set.Icc (0 : NNReal)
    (heterogeneousActionBound slotWeight marginalCost (premium i))

instance instNonemptyHeterogeneousCompactAction
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι) :
    Nonempty (HeterogeneousCompactAction slotWeight marginalCost premium i) :=
  ⟨⟨0, bot_le, bot_le⟩⟩

/-- Forget the compact upper-bound proof coordinatewise. -/
def compactActionProfileToNNReal
    [Fintype ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (action : ∀ i, HeterogeneousCompactAction slotWeight marginalCost premium i) :
    ι → NNReal :=
  fun i => action i

theorem continuous_compactActionProfileToNNReal
    [Fintype ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) :
    Continuous (compactActionProfileToNNReal slotWeight marginalCost premium) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)

/-- The opponents' maximum effective score is continuous in their action
profile.  The measurable counterpart is in `HeterogeneousMixedProfile`. -/
theorem continuous_opponentMaxEffectiveScore
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) :
    Continuous (opponentMaxEffectiveScore hcard premium i) := by
  unfold opponentMaxEffectiveScore
  exact Continuous.finset_sup'_apply
    (univ_erase_nonempty_of_two hcard i)
    (fun j _ => continuous_const.add
      (NNReal.continuous_coe.comp (continuous_apply j)))

/-- Pure payoff on the compact action product. -/
def heterogeneousCompactPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : ∀ j, HeterogeneousCompactAction slotWeight marginalCost premium j) : ℝ :=
  slotWeight * heterogeneousPureCapturedPremium hcard premium i
      (action i) (compactActionProfileToNNReal slotWeight marginalCost premium action) -
    marginalCost * (action i : NNReal)

theorem continuous_heterogeneousCompactPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    Continuous (heterogeneousCompactPayoff slotWeight marginalCost premium hcard i) := by
  unfold heterogeneousCompactPayoff heterogeneousPureCapturedPremium
  have hprofile := continuous_compactActionProfileToNNReal
    slotWeight marginalCost premium
  have hown : Continuous
      (fun action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j =>
        premium i + ((action i : NNReal) : ℝ)) :=
    continuous_const.add
      (NNReal.continuous_coe.comp
        (continuous_subtype_val.comp (continuous_apply i)))
  have hmax : Continuous
      (fun action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j =>
        opponentMaxEffectiveScore hcard premium i
          (compactActionProfileToNNReal slotWeight marginalCost premium action)) :=
    (continuous_opponentMaxEffectiveScore hcard premium i).comp hprofile
  have hcaptured : Continuous
      (fun action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j =>
        strictPriorityCapturedGap (premium i)
          (premium i + ((action i : NNReal) : ℝ))
          (opponentMaxEffectiveScore hcard premium i
            (compactActionProfileToNNReal slotWeight marginalCost premium action))) :=
    (strictPriorityCapturedGap_continuous (premium i)).comp
      (hown.prodMk hmax)
  exact (continuous_const.mul hcaptured).sub
    (continuous_const.mul
      (NNReal.continuous_coe.comp
        (continuous_subtype_val.comp (continuous_apply i))))

/-- A pure action above `w₁ dᵢ / κ` earns a strictly negative payoff against
every opponent profile. -/
theorem heterogeneousPurePayoff_neg_above_bound
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 < marginalCost) (premium : ι → ℝ)
    (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : NNReal) (haction :
      heterogeneousActionBound slotWeight marginalCost (premium i) < action)
    (profile : ι → NNReal) :
    slotWeight * heterogeneousPureCapturedPremium hcard premium i action profile -
        marginalCost * (action : ℝ) < 0 := by
  have hcap := strictPriorityCapturedGap_le_gap
    (gap := premium i)
    (own := premium i + (action : ℝ))
    (rival := opponentMaxEffectiveScore hcard premium i profile)
  have hbound : slotWeight * premium i / marginalCost < (action : ℝ) := by
    have hbound' :
        (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) <
          (action : ℝ) := by
      exact_mod_cast haction
    simpa [coe_heterogeneousActionBound hweight.le hcost (hpremium i)] using hbound'
  have hmul : slotWeight * premium i < marginalCost * (action : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hcost).mp hbound
  have hweightNonneg : 0 ≤ slotWeight := hweight.le
  unfold heterogeneousPureCapturedPremium
  nlinarith [mul_le_mul_of_nonneg_left hcap hweightNonneg]

/-- Action zero always gives a nonnegative pure payoff. -/
theorem heterogeneousPurePayoff_zero_nonneg
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ} (hweight : 0 ≤ slotWeight)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (profile : ι → NNReal) :
    0 ≤ slotWeight *
        heterogeneousPureCapturedPremium hcard premium i 0 profile -
      marginalCost * (0 : ℝ) := by
  simp only [mul_zero, sub_zero]
  exact mul_nonneg hweight
    (strictPriorityCapturedGap_nonneg (hpremium i))

/-! ## The compact complete-information game -/

instance instCompactSpaceHeterogeneousCompactAction
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι) :
    CompactSpace
      (HeterogeneousCompactAction slotWeight marginalCost premium i) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

instance instStandardBorelSpaceHeterogeneousCompactAction
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι) :
    StandardBorelSpace
      (HeterogeneousCompactAction slotWeight marginalCost premium i) :=
  measurableSet_Icc.standardBorel

/-- The truncated strict-priority race as a measurable Bayesian game with a
singleton type for every bidder.  Its mixed extension is therefore the
ordinary independent mixed extension of the compact complete-information
game. -/
def heterogeneousCompactGame
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) : MeasBayesianGame where
  Player := ι
  Theta := fun _ => PUnit.{1}
  Action := fun i =>
    HeterogeneousCompactAction slotWeight marginalCost premium i
  prior := Measure.dirac (fun _ => (PUnit.unit : PUnit.{1}))
  payoff := fun i action _ =>
    heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
  measurable_payoff := fun i =>
    (continuous_heterogeneousCompactPayoff
      slotWeight marginalCost premium hcard i).measurable.comp measurable_fst

instance instStandardBorelSpaceHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    StandardBorelSpace
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change StandardBorelSpace
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

instance instTopologicalSpaceHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    TopologicalSpace
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change TopologicalSpace
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

instance instCompactSpaceHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    CompactSpace
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change CompactSpace
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

instance instMetrizableSpaceHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    TopologicalSpace.MetrizableSpace
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change TopologicalSpace.MetrizableSpace
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

instance instBorelSpaceHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    BorelSpace
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change BorelSpace
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

instance instNonemptyHeterogeneousCompactGameAction
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (i : (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).Player) :
    Nonempty
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change Nonempty
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  infer_instance

@[simp] theorem heterogeneousCompactGame_payoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : ∀ j,
      HeterogeneousCompactAction slotWeight marginalCost premium j)
    (theta : ∀ _ : ι, PUnit.{1}) :
    (heterogeneousCompactGame slotWeight marginalCost premium hcard).payoff
        i action theta =
      heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action :=
  rfl

theorem heterogeneousCompactGame_payoff_bounded
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι) :
    ∀ i, ∃ C,
      ∀ (action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j)
        (theta : ∀ _ : ι, PUnit.{1}),
      |(heterogeneousCompactGame slotWeight marginalCost premium hcard).payoff
        i action theta| ≤ C := by
  intro i
  refine ⟨slotWeight * premium i + marginalCost *
    (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ), ?_⟩
  intro action theta
  rw [heterogeneousCompactGame_payoff]
  unfold heterogeneousCompactPayoff heterogeneousPureCapturedPremium
  have hcapturedNonneg : 0 ≤ strictPriorityCapturedGap (premium i)
      (premium i + ((action i : NNReal) : ℝ))
      (opponentMaxEffectiveScore hcard premium i
        (compactActionProfileToNNReal slotWeight marginalCost premium action)) :=
    strictPriorityCapturedGap_nonneg (hpremium i)
  have hcapturedLe : strictPriorityCapturedGap (premium i)
      (premium i + ((action i : NNReal) : ℝ))
      (opponentMaxEffectiveScore hcard premium i
        (compactActionProfileToNNReal slotWeight marginalCost premium action)) ≤
      premium i := strictPriorityCapturedGap_le_gap
  have hactionNonneg : 0 ≤ (((action i : NNReal) : ℝ)) :=
    NNReal.coe_nonneg _
  have hactionLe : (((action i : NNReal) : ℝ)) ≤
      (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) := by
    exact_mod_cast (action i).property.2
  calc
    |slotWeight * strictPriorityCapturedGap (premium i)
          (premium i + ((action i : NNReal) : ℝ))
          (opponentMaxEffectiveScore hcard premium i
            (compactActionProfileToNNReal slotWeight marginalCost premium action)) -
        marginalCost * ((action i : NNReal) : ℝ)| ≤
        |slotWeight * strictPriorityCapturedGap (premium i)
          (premium i + ((action i : NNReal) : ℝ))
          (opponentMaxEffectiveScore hcard premium i
            (compactActionProfileToNNReal slotWeight marginalCost premium action))| +
        |marginalCost * ((action i : NNReal) : ℝ)| := abs_sub _ _
    _ = slotWeight * strictPriorityCapturedGap (premium i)
          (premium i + ((action i : NNReal) : ℝ))
          (opponentMaxEffectiveScore hcard premium i
            (compactActionProfileToNNReal slotWeight marginalCost premium action)) +
        marginalCost * ((action i : NNReal) : ℝ) := by
      rw [abs_of_nonneg (mul_nonneg hweight hcapturedNonneg),
        abs_of_nonneg (mul_nonneg hcost.le hactionNonneg)]
    _ ≤ slotWeight * premium i +
        marginalCost *
          (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcapturedLe hweight)
        (mul_le_mul_of_nonneg_left hactionLe hcost.le)

/-- The singleton common prior equals the product of its singleton
marginals, so the absolute-continuity premise of the Econlib existence theorem
is automatic. -/
theorem heterogeneousCompactGame_prior_ac_product_marginals
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) :
    (heterogeneousCompactGame slotWeight marginalCost premium hcard).prior ≪
      Measure.pi fun i =>
        (heterogeneousCompactGame slotWeight marginalCost premium hcard).marginalType i := by
  have hmarginal : ∀ i,
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).marginalType i =
        Measure.dirac (PUnit.unit : PUnit.{1}) := by
    intro i
    unfold MeasBayesianGame.marginalType heterogeneousCompactGame
    rw [Measure.map_dirac]
  change Measure.dirac (fun _ : ι => (PUnit.unit : PUnit.{1})) ≪ _
  rw [show (Measure.pi fun i =>
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).marginalType i) =
      Measure.pi (fun _ : ι => Measure.dirac (PUnit.unit : PUnit.{1})) by
    congr 1
    funext i
    exact hmarginal i]
  rw [Measure.pi_dirac]

/-- Existence of a behavioral equilibrium of the compactified race, before
mapping the compact lotteries back to laws on all nonnegative actions. -/
theorem exists_heterogeneousCompactMixedBNE
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι) :
    let G := heterogeneousCompactGame slotWeight marginalCost premium hcard
    ∃ s : G.mixedExtension.Strategy, G.mixedExtension.IsBNE s := by
  dsimp only
  refine MeasBayesianGame.exists_mixedExtension_isBNE
    (G := heterogeneousCompactGame slotWeight marginalCost premium hcard) ?_ ?_ ?_
  · exact heterogeneousCompactGame_payoff_bounded
      hweight.le hcost premium hpremium hcard
  · intro i theta
    exact continuous_heterogeneousCompactPayoff
      slotWeight marginalCost premium hcard i
  · exact heterogeneousCompactGame_prior_ac_product_marginals
      slotWeight marginalCost premium hcard

/-! ## Mapping compact lotteries to the paper's Borel laws -/

/-- Forget the compact action bound in a probability law and retain the
finite first moment needed by `BorelMixedStrategy`. -/
def compactLotteryToBorelMixedStrategy
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι)
    (law : ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i)) :
    BorelMixedStrategy where
  law := law.map continuous_subtype_val.measurable.aemeasurable
  integrable_action := by
    have hval : Measurable
        (fun action : HeterogeneousCompactAction
            slotWeight marginalCost premium i => (action : NNReal)) :=
      continuous_subtype_val.measurable
    have hstrong : AEStronglyMeasurable
        (fun action : NNReal => (action : ℝ))
        (Measure.map
          (fun action : HeterogeneousCompactAction
            slotWeight marginalCost premium i => (action : NNReal))
          (law : Measure
            (HeterogeneousCompactAction slotWeight marginalCost premium i))) :=
      measurable_coe_nnreal_real.aestronglyMeasurable
    apply (integrable_map_measure hstrong hval.aemeasurable).mpr
    refine Integrable.of_bound
      (measurable_coe_nnreal_real.comp hval).aestronglyMeasurable
      (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) ?_
    filter_upwards with action
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast action.property.2

/-- The independent law of the mapped Borel profile is the pushforward of
the independent compact-lottery product. -/
theorem heterogeneousProfileLaw_compactLotteryToBorel
    [Fintype ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (law : ∀ i, ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i)) :
    (heterogeneousProfileLaw (fun i =>
        compactLotteryToBorelMixedStrategy
          slotWeight marginalCost premium i (law i)) :
        Measure (ι → NNReal)) =
      (Measure.pi fun i =>
        (law i : Measure
          (HeterogeneousCompactAction slotWeight marginalCost premium i))).map
        (fun action i => (action i : NNReal)) := by
  change (Measure.pi fun i =>
      Measure.map
        (fun action : HeterogeneousCompactAction
          slotWeight marginalCost premium i => (action : NNReal))
        (law i : Measure
          (HeterogeneousCompactAction slotWeight marginalCost premium i))) = _
  have hfinite := FiniteMeasure.pi_map_pi
    (μ := fun i => (law i).toFiniteMeasure)
    (f := fun i action => (action : NNReal))
    (fun i => continuous_subtype_val.measurable.aemeasurable)
  exact congrArg FiniteMeasure.toMeasure hfinite.symm

end

end SmoothingCliff.Racing
