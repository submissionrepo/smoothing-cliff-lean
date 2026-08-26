import SmoothingCliff.Racing.HeterogeneousExistence
import SmoothingCliff.Racing.HeterogeneousExceptionalRent

/-!
# Returning the compact equilibrium to nonnegative actions

The existence theorem first truncates each action at `w₁ dᵢ / κ`.  This file
pushes the resulting compact lotteries into `NNReal`, identifies their product
law and payoffs with the paper's heterogeneous mixed-race interface, and then
restores deviations on the whole nonnegative half-line.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open Econlib.GameTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- The compact action lottery selected by bidder `i` at a singleton type. -/
def compactMixedStrategyLawAt
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (i : ι) (theta : PUnit.{1}) : ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i) := by
  change ProbabilityMeasure
    ((heterogeneousCompactGame slotWeight marginalCost premium hcard).Action i)
  exact (s i).1 theta

/-- The action lottery selected at the unique type of bidder `i`. -/
def compactMixedStrategyLaw
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (i : ι) : ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i) :=
  compactMixedStrategyLawAt slotWeight marginalCost premium hcard s i
    (PUnit.unit : PUnit.{1})

/-- The Borel profile obtained by forgetting the compact support proofs in a
behavioral strategy of the compact game's mixed extension. -/
def compactMixedStrategyToBorelProfile
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension) :
    ι → BorelMixedStrategy :=
  fun i => compactLotteryToBorelMixedStrategy slotWeight marginalCost premium i
    (compactMixedStrategyLaw slotWeight marginalCost premium hcard s i)

theorem compactLotteryToBorelMixedStrategy_meanAction
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι)
    (law : ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i)) :
    (compactLotteryToBorelMixedStrategy
        slotWeight marginalCost premium i law).meanAction =
      ∫ action : HeterogeneousCompactAction
          slotWeight marginalCost premium i,
        (((action : NNReal) : ℝ)) ∂(law : Measure _) := by
  unfold BorelMixedStrategy.meanAction compactLotteryToBorelMixedStrategy
  have hmap : AEMeasurable
      (fun action : HeterogeneousCompactAction
        slotWeight marginalCost premium i => (action : NNReal))
      (law : Measure _) :=
    continuous_subtype_val.measurable.aemeasurable
  have hstrong : AEStronglyMeasurable
      (fun action : NNReal => (action : ℝ))
      (Measure.map
        (fun action : HeterogeneousCompactAction
          slotWeight marginalCost premium i => (action : NNReal))
        (law : Measure _)) :=
    measurable_coe_nnreal_real.aestronglyMeasurable
  exact integral_map hmap hstrong

theorem measurable_compactActionProfileToNNReal
    [Fintype ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) :
    Measurable (compactActionProfileToNNReal
      slotWeight marginalCost premium) :=
  (continuous_compactActionProfileToNNReal
    slotWeight marginalCost premium).measurable

/-- Captured premium under the pushed-forward Borel profile equals captured
premium integrated directly over the compact product law. -/
theorem heterogeneousExpectedCapturedPremium_compact
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (law : ∀ i, ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i))
    (i : ι) :
    heterogeneousExpectedCapturedPremium
        (fun j => compactLotteryToBorelMixedStrategy
          slotWeight marginalCost premium j (law j))
        hcard premium i =
      ∫ action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j,
        heterogeneousPureCapturedPremium hcard premium i (action i)
          (compactActionProfileToNNReal
            slotWeight marginalCost premium action)
        ∂(Measure.pi fun j => (law j : Measure _)) := by
  unfold heterogeneousExpectedCapturedPremium
  rw [heterogeneousProfileLaw_compactLotteryToBorel]
  have hmap := measurable_compactActionProfileToNNReal
    slotWeight marginalCost premium
  have hstrong : AEStronglyMeasurable
      (fun profile : ι → NNReal =>
        heterogeneousPureCapturedPremium hcard premium i (profile i) profile)
      (Measure.map
        (compactActionProfileToNNReal slotWeight marginalCost premium)
        (Measure.pi fun j => (law j : Measure _))) :=
    (measurable_heterogeneousCapturedPremium_profile
      hcard premium i).aestronglyMeasurable
  change (∫ profile : ι → NNReal,
      heterogeneousPureCapturedPremium hcard premium i (profile i) profile
      ∂Measure.map
        (compactActionProfileToNNReal slotWeight marginalCost premium)
        (Measure.pi fun j => (law j : Measure _))) = _
  rw [integral_map hmap.aemeasurable hstrong]
  rfl

/-- The paper's expected-payoff functional agrees with the compact mixed
extension's one-profile integral. -/
theorem heterogeneousExpectedPayoff_compact
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (law : ∀ i, ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium i))
    (i : ι) (hpremium : 0 ≤ premium i) :
    heterogeneousExpectedPayoff slotWeight marginalCost
        (fun j => compactLotteryToBorelMixedStrategy
          slotWeight marginalCost premium j (law j))
        hcard premium i =
      ∫ action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j,
        heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
        ∂(Measure.pi fun j => (law j : Measure _)) := by
  let compactLaw : Measure (∀ j,
      HeterogeneousCompactAction slotWeight marginalCost premium j) :=
    Measure.pi fun j => (law j : Measure _)
  have heval : MeasurePreserving (Function.eval i) compactLaw
      (law i : Measure _) := by
    dsimp [compactLaw]
    exact measurePreserving_eval _ i
  have hcoordinate :
      (∫ action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j,
        (((action i : NNReal) : ℝ)) ∂compactLaw) =
        ∫ action : HeterogeneousCompactAction
            slotWeight marginalCost premium i,
          (((action : NNReal) : ℝ)) ∂(law i : Measure _) := by
    have hstrong : AEStronglyMeasurable
        (fun action : HeterogeneousCompactAction
          slotWeight marginalCost premium i => (((action : NNReal) : ℝ)))
        (Measure.map (Function.eval i) compactLaw) := by
      rw [heval.map_eq]
      exact (measurable_coe_nnreal_real.comp
        continuous_subtype_val.measurable).aestronglyMeasurable
    have hmap := integral_map heval.measurable.aemeasurable hstrong
    rw [heval.map_eq] at hmap
    exact hmap.symm
  have hcapturedInt : Integrable
      (fun action : ∀ j,
        HeterogeneousCompactAction slotWeight marginalCost premium j =>
        heterogeneousPureCapturedPremium hcard premium i (action i)
          (compactActionProfileToNNReal
            slotWeight marginalCost premium action)) compactLaw := by
    refine Integrable.of_bound
      (((measurable_heterogeneousCapturedPremium_profile hcard premium i).comp
        (measurable_compactActionProfileToNNReal
          slotWeight marginalCost premium)).aestronglyMeasurable)
      (premium i) ?_
    filter_upwards with action
    unfold heterogeneousPureCapturedPremium
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
    exact strictPriorityCapturedGap_le_gap
  have hcoordinateInt : Integrable
      (fun action : ∀ j,
        HeterogeneousCompactAction slotWeight marginalCost premium j =>
        (((action i : NNReal) : ℝ))) compactLaw := by
    refine Integrable.of_bound
      ((measurable_coe_nnreal_real.comp continuous_subtype_val.measurable |>.comp
        (measurable_pi_apply i)).aestronglyMeasurable)
      (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) ?_
    filter_upwards with action
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast (action i).property.2
  rw [heterogeneousExpectedPayoff,
    heterogeneousExpectedCapturedPremium_compact]
  rw [compactLotteryToBorelMixedStrategy_meanAction]
  unfold heterogeneousCompactPayoff
  change _ = ∫ action, _ ∂compactLaw
  rw [integral_sub (hcapturedInt.const_mul slotWeight)
      (hcoordinateInt.const_mul marginalCost),
    integral_const_mul, integral_const_mul, hcoordinate]

/-! ## Degenerate deviations -/

/-- The point mass at a nonnegative action, packaged with its finite first
moment. -/
def diracBorelMixedStrategy (action : NNReal) : BorelMixedStrategy where
  law := ⟨Measure.dirac action, inferInstance⟩
  integrable_action := integrable_dirac (by simp)

@[simp] theorem diracBorelMixedStrategy_meanAction (action : NNReal) :
    (diracBorelMixedStrategy action).meanAction = (action : ℝ) := by
  simp [diracBorelMixedStrategy, BorelMixedStrategy.meanAction]

/-- Setting one coordinate of a product draw to `action` replaces precisely
that marginal by a point mass. -/
theorem map_setCoordinate_heterogeneousProfileLaw
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy) (i : ι) (action : NNReal) :
    Measure.map (fun profile : ι → NNReal =>
        Function.update profile i action)
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) =
      (heterogeneousProfileLaw
        (Function.update strategy i (diracBorelMixedStrategy action)) :
          Measure (ι → NNReal)) := by
  let coordinateMap : ι → NNReal → NNReal := fun j x =>
    if h : j = i then action else x
  have hmeas : ∀ j, AEMeasurable (coordinateMap j)
      ((strategy j).law : Measure NNReal) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [coordinateMap, ↓reduceDIte]
      exact measurable_const.aemeasurable
    · simp only [coordinateMap, hji, ↓reduceDIte]
      exact measurable_id.aemeasurable
  have hpi := Measure.pi_map_pi
    (μ := fun j => ((strategy j).law : Measure NNReal))
    (f := coordinateMap) hmeas
  rw [show (fun profile : ι → NNReal => Function.update profile i action) =
      (fun profile j => coordinateMap j (profile j)) by
    funext profile j
    by_cases hji : j = i
    · subst j
      simp [coordinateMap]
    · simp [coordinateMap, hji]]
  change Measure.map (fun profile j => coordinateMap j (profile j))
      (Measure.pi fun j => ((strategy j).law : Measure NNReal)) =
    Measure.pi fun j =>
      (((Function.update strategy i (diracBorelMixedStrategy action)) j).law :
        Measure NNReal)
  rw [hpi]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateMap, diracBorelMixedStrategy]
  · simp [coordinateMap, hji]

/-- Forgetting the support proof in a compact point mass gives the same
point mass on `NNReal`. -/
theorem compactLotteryToBorelMixedStrategy_dirac
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ) (i : ι)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    compactLotteryToBorelMixedStrategy slotWeight marginalCost premium i
        ⟨Measure.dirac action, inferInstance⟩ =
      diracBorelMixedStrategy (action : NNReal) := by
  unfold compactLotteryToBorelMixedStrategy diracBorelMixedStrategy
  congr 1
  apply ProbabilityMeasure.toMeasure_injective
  simp

/-- Replacing bidder `i` by a point mass converts expected payoff into the
corresponding pure-deviation payoff against the original opponents. -/
theorem heterogeneousExpectedPayoff_update_dirac_eq_pure
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) :
    heterogeneousExpectedPayoff slotWeight marginalCost
        (Function.update strategy i (diracBorelMixedStrategy action))
        hcard premium i =
      heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
        premium i action := by
  have hmap : Measurable (fun profile : ι → NNReal =>
      Function.update profile i action) :=
    measurable_update'.comp (measurable_id.prodMk measurable_const)
  have hstrong : AEStronglyMeasurable
      (fun profile : ι → NNReal =>
        heterogeneousPureCapturedPremium hcard premium i (profile i) profile)
      (Measure.map (fun profile : ι → NNReal =>
        Function.update profile i action)
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) :=
    (measurable_heterogeneousCapturedPremium_profile
      hcard premium i).aestronglyMeasurable
  have hcaptured :
      heterogeneousExpectedCapturedPremium
          (Function.update strategy i (diracBorelMixedStrategy action))
          hcard premium i =
        heterogeneousPureExpectedCapturedPremium strategy hcard premium i action := by
    unfold heterogeneousExpectedCapturedPremium
      heterogeneousPureExpectedCapturedPremium
    rw [← map_setCoordinate_heterogeneousProfileLaw strategy i action,
      integral_map hmap.aemeasurable hstrong]
    apply integral_congr_ae
    filter_upwards with profile
    unfold heterogeneousPureCapturedPremium
    rw [Function.update_self,
      opponentMaxEffectiveScore_update_self hcard premium i profile action]
  rw [heterogeneousExpectedPayoff, heterogeneousPureExpectedPayoff,
    hcaptured, Function.update_self, diracBorelMixedStrategy_meanAction]

/-! ## Compact mixed equilibrium implies Borel mixed equilibrium -/

/-- With singleton types, ex-ante payoff in the compact mixed extension is
just the product-law integral of compact pure payoffs. -/
theorem heterogeneousCompactMixedExtension_exAntePayoff_eq
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (i : ι) :
    (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.exAntePayoff
        i s =
      ∫ action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j,
        heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
        ∂(Measure.pi fun j =>
          (compactMixedStrategyLaw
            slotWeight marginalCost premium hcard s j : Measure _)) := by
  unfold MeasBayesianGame.exAntePayoff
  change (∫ theta : ∀ _ : ι, PUnit.{1},
      (∫ action : ∀ j,
          HeterogeneousCompactAction slotWeight marginalCost premium j,
        heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
        ∂(Measure.pi fun j =>
          (compactMixedStrategyLawAt
            slotWeight marginalCost premium hcard s j (theta j) : Measure _)))
      ∂Measure.dirac (fun _ : ι => (PUnit.unit : PUnit.{1}))) = _
  rw [integral_dirac]
  rfl

/-- A compact point mass, viewed as an action of the mixed extension. -/
def compactDiracLottery
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    ProbabilityMeasure
      ((heterogeneousCompactGame
        slotWeight marginalCost premium hcard).Action i) := by
  change ProbabilityMeasure
    (HeterogeneousCompactAction slotWeight marginalCost premium i)
  exact ⟨Measure.dirac action, inferInstance⟩

/-- The measurable constant strategy choosing a compact point mass. -/
def compactPureDeviation
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    {f : PUnit.{1} → ProbabilityMeasure
        ((heterogeneousCompactGame
          slotWeight marginalCost premium hcard).Action i) // Measurable f} :=
  ⟨fun _ => by
      change ProbabilityMeasure
        (HeterogeneousCompactAction slotWeight marginalCost premium i)
      exact ⟨Measure.dirac action, inferInstance⟩,
    measurable_const⟩

@[simp] theorem compactMixedStrategyLaw_replace_pure_self
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (i : ι)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    compactMixedStrategyLaw slotWeight marginalCost premium hcard
        ((heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.replace
          s i (compactPureDeviation
            slotWeight marginalCost premium hcard i action)) i =
      ⟨Measure.dirac action, inferInstance⟩ := by
  unfold compactMixedStrategyLaw compactMixedStrategyLawAt
    compactPureDeviation
  rw [MeasBayesianGame.replace_self]
  rfl

theorem compactMixedStrategyLaw_replace_pure_of_ne
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ) (premium : ι → ℝ)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (i j : ι) (hji : j ≠ i)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    compactMixedStrategyLaw slotWeight marginalCost premium hcard
        ((heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.replace
          s i (compactPureDeviation
            slotWeight marginalCost premium hcard i action)) j =
      compactMixedStrategyLaw slotWeight marginalCost premium hcard s j := by
  unfold compactMixedStrategyLaw compactMixedStrategyLawAt
  rw [(heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.replace_of_ne
    s i
      (compactPureDeviation slotWeight marginalCost premium hcard i action) hji]

/-- A compact mixed BNE satisfies every pure best-response inequality after
its lotteries are pushed into `NNReal`. -/
theorem compactMixedBNE_boundedBestResponse
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (hnash : (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.IsBNE
      s)
    (i : ι)
    (action : HeterogeneousCompactAction
      slotWeight marginalCost premium i) :
    heterogeneousPureExpectedPayoff slotWeight marginalCost
        (compactMixedStrategyToBorelProfile
          slotWeight marginalCost premium hcard s)
        hcard premium i (action : NNReal) ≤
      heterogeneousExpectedPayoff slotWeight marginalCost
        (compactMixedStrategyToBorelProfile
          slotWeight marginalCost premium hcard s)
        hcard premium i := by
  let s' : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension :=
    (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.replace
      s i (compactPureDeviation
        slotWeight marginalCost premium hcard i action)
  have hagree : ∀ j, j ≠ i → s' j = s j := by
    intro j hji
    exact (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).mixedExtension.replace_of_ne
        s i (compactPureDeviation
          slotWeight marginalCost premium hcard i action) hji
  obtain ⟨C, hC⟩ :=
    heterogeneousCompactGame_payoff_bounded
      hweight.le hcost premium hpremium hcard i
  have hdevInt : Integrable
      (fun theta =>
        (heterogeneousCompactGame
          slotWeight marginalCost premium hcard).mixedExtension.payoff i
          ((heterogeneousCompactGame
            slotWeight marginalCost premium hcard).mixedExtension.actionProfile s' theta)
          theta)
      (heterogeneousCompactGame
        slotWeight marginalCost premium hcard).mixedExtension.prior := by
    exact (heterogeneousCompactGame
      slotWeight marginalCost premium hcard).mixedExtension.integrable_exAntePayoff_of_bdd i s'
      (fun theta => (heterogeneousCompactGame
        slotWeight marginalCost premium hcard).abs_mixedExtension_payoff_le
          i hC _ theta)
  have hbest := (((heterogeneousCompactGame
    slotWeight marginalCost premium hcard).mixedExtension.isBNE_iff s).1 hnash).1
    i s' hagree hdevInt
  rw [heterogeneousCompactMixedExtension_exAntePayoff_eq,
    heterogeneousCompactMixedExtension_exAntePayoff_eq] at hbest
  let law : ∀ j, ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium j) :=
    fun j => compactMixedStrategyLaw
      slotWeight marginalCost premium hcard s j
  let law' : ∀ j, ProbabilityMeasure
      (HeterogeneousCompactAction slotWeight marginalCost premium j) :=
    fun j => compactMixedStrategyLaw
      slotWeight marginalCost premium hcard s' j
  have horiginal := heterogeneousExpectedPayoff_compact
    slotWeight marginalCost premium hcard law i (hpremium i)
  have hdeviation := heterogeneousExpectedPayoff_compact
    slotWeight marginalCost premium hcard law' i (hpremium i)
  change (∫ action : ∀ j,
      HeterogeneousCompactAction slotWeight marginalCost premium j,
      heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
      ∂(Measure.pi fun j => (law j : Measure _))) ≥
    ∫ action : ∀ j,
      HeterogeneousCompactAction slotWeight marginalCost premium j,
      heterogeneousCompactPayoff slotWeight marginalCost premium hcard i action
      ∂(Measure.pi fun j => (law' j : Measure _)) at hbest
  rw [← horiginal, ← hdeviation] at hbest
  have hprofile :
      (fun j => compactLotteryToBorelMixedStrategy
        slotWeight marginalCost premium j (law' j)) =
        Function.update
          (fun j => compactLotteryToBorelMixedStrategy
            slotWeight marginalCost premium j (law j))
          i (diracBorelMixedStrategy (action : NNReal)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rw [show law' i = ⟨Measure.dirac action, inferInstance⟩ from by
        exact compactMixedStrategyLaw_replace_pure_self
          slotWeight marginalCost premium hcard s i action]
      exact compactLotteryToBorelMixedStrategy_dirac
        slotWeight marginalCost premium i action
    · rw [Function.update_of_ne hji]
      rw [show law' j = law j from by
        exact compactMixedStrategyLaw_replace_pure_of_ne
          slotWeight marginalCost premium hcard s i j hji action]
  rw [hprofile,
    heterogeneousExpectedPayoff_update_dirac_eq_pure] at hbest
  exact hbest

/-- The compact mixed equilibrium remains a best response against every
nonnegative action.  Actions above `w₁ dᵢ / κ` have negative payoff, whereas
action zero guarantees a nonnegative equilibrium payoff. -/
theorem compactMixedBNE_isHeterogeneousBorelMixedNash
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι)
    (s : MeasBayesianGame.Strategy
      (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension)
    (hnash : (heterogeneousCompactGame slotWeight marginalCost premium hcard).mixedExtension.IsBNE
      s) :
    IsHeterogeneousBorelMixedNash slotWeight marginalCost
      (compactMixedStrategyToBorelProfile
        slotWeight marginalCost premium hcard s) hcard premium := by
  intro i action
  by_cases hbounded : action ≤
      heterogeneousActionBound slotWeight marginalCost (premium i)
  · let compactAction : HeterogeneousCompactAction
        slotWeight marginalCost premium i := ⟨action, bot_le, hbounded⟩
    exact compactMixedBNE_boundedBestResponse hweight hcost premium hpremium
      hcard s hnash i compactAction
  · have hzeroBR := compactMixedBNE_boundedBestResponse hweight hcost
      premium hpremium hcard s hnash i
      (⟨0, bot_le, bot_le⟩ : HeterogeneousCompactAction
        slotWeight marginalCost premium i)
    have hzeroPayoff := heterogeneousPureExpectedPayoff_zero_nonneg
      (marginalCost := marginalCost)
      hweight.le
      (compactMixedStrategyToBorelProfile
        slotWeight marginalCost premium hcard s)
      hcard premium i (hpremium i)
    have hzeroBR' :
        heterogeneousPureExpectedPayoff slotWeight marginalCost
            (compactMixedStrategyToBorelProfile
              slotWeight marginalCost premium hcard s)
            hcard premium i 0 ≤
          heterogeneousExpectedPayoff slotWeight marginalCost
            (compactMixedStrategyToBorelProfile
              slotWeight marginalCost premium hcard s)
            hcard premium i := by
      simpa using hzeroBR
    have hequilibriumNonneg : 0 ≤
        heterogeneousExpectedPayoff slotWeight marginalCost
          (compactMixedStrategyToBorelProfile
            slotWeight marginalCost premium hcard s)
          hcard premium i := hzeroPayoff.trans hzeroBR'
    have hcaptured := heterogeneousPureExpectedCapturedPremium_le_premium
      (compactMixedStrategyToBorelProfile
        slotWeight marginalCost premium hcard s)
      hcard premium i (hpremium i) action
    have habove : slotWeight * premium i / marginalCost < (action : ℝ) := by
      have habove' :
          heterogeneousActionBound slotWeight marginalCost (premium i) < action :=
        lt_of_not_ge hbounded
      have haboveCoe :
          (heterogeneousActionBound slotWeight marginalCost (premium i) : ℝ) <
            (action : ℝ) := by
        exact_mod_cast habove'
      simpa [coe_heterogeneousActionBound hweight.le hcost (hpremium i)]
        using haboveCoe
    have hcostExceeds : slotWeight * premium i <
        marginalCost * (action : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hcost).mp habove
    unfold heterogeneousPureExpectedPayoff
    nlinarith

/-- Existence of an independent Borel mixed equilibrium in the heterogeneous
strict-priority margin race. -/
theorem exists_heterogeneousBorelMixedNash
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι) :
    ∃ strategy : ι → BorelMixedStrategy,
      IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
        hcard premium := by
  obtain ⟨s, hnash⟩ := exists_heterogeneousCompactMixedBNE
    hweight hcost premium hpremium hcard
  exact ⟨compactMixedStrategyToBorelProfile
      slotWeight marginalCost premium hcard s,
    compactMixedBNE_isHeterogeneousBorelMixedNash
      hweight hcost premium hpremium hcard s hnash⟩

end

end SmoothingCliff.Racing
