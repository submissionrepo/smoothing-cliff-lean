import SmoothingCliff.Mechanism.Monotonicity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# General top-K stability of the PL allocation rule

This file formalizes the calculus argument in `thm:stability` from
*Smoothing the Cliff*.  We condition on the opponents' exponential-race
arrival order statistics.  A finite threshold is represented by `some t`;
`none` is the paper's `+∞` padding when fewer opponents than slots remain.

For own score `s` and intensity `λ = exp s`, the probability of zero-based
rank `p` is

`exp (-λ O_(p-1)) - exp (-λ O_p)`,

where the first survival probability is one.  We prove the finite
summation-by-parts identity, differentiate its Abel form, derive the sharp
kernel estimate `u exp (-u) ≤ exp (-1)`, and telescope the nonnegative slot
weight decrements.  The resulting pathwise bid derivative lies in
`[0, w₁ / (e τ)]` and the same constant is a global Lipschitz modulus.

The last section carries the result through an arbitrary probability law on
the conditioned opponent order statistics.  The differentiation-under-the-
integral step uses mathlib's dominated parametric Bochner-integral theorem;
the only extra hypotheses are almost-everywhere measurability of the
conditional priority and its explicitly derived derivative.
-/

open scoped BigOperators

namespace SmoothingCliff.Mechanism

/-- A conditioned sequence of opponent exponential-race order statistics.
`none` represents `+∞`.  The `padding` field makes this convention persistent
after the last finite opponent arrival. -/
structure ConditionedOpponentOrderStats where
  threshold : ℕ → Option ℝ
  nonnegative : ∀ p t, threshold p = some t → 0 ≤ t
  ordered : ∀ p t u,
    threshold p = some t → threshold (p + 1) = some u → t ≤ u
  padding : ∀ p, threshold p = none → threshold (p + 1) = none
  finite : ∃ p, threshold p = none

/-- Survival probability of an exponential clock of rate `exp score` at a
conditioned threshold.  Survival at the `+∞` padding value is zero. -/
noncomputable def conditionedSurvival (score : ℝ) : Option ℝ → ℝ
  | none => 0
  | some t => Real.exp (-(Real.exp score * t))

/-- The survival probability at the preceding order statistic.  For the
first rank the preceding time is `O_(0) = 0`, hence survival is one. -/
noncomputable def previousConditionedSurvival
    (stats : ConditionedOpponentOrderStats) (score : ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 1
  else conditionedSurvival score (stats.threshold (p - 1))

/-- Conditional probability that the own exponential clock has zero-based
rank `p`. -/
noncomputable def conditionedRankMass
    (stats : ConditionedOpponentOrderStats) (score : ℝ) (p : ℕ) : ℝ :=
  previousConditionedSurvival stats score p -
    conditionedSurvival score (stats.threshold p)

/-- The survival expression uses exactly the PL intensity from the common
exponential-race model in `Monotonicity.lean`. -/
theorem conditionedSurvival_at_bid
    (reserve temperature bid t : ℝ) :
    conditionedSurvival ((bid - reserve) / temperature) (some t) =
      Real.exp (-(luceIntensity reserve temperature bid * t)) := by
  rfl

theorem conditionedSurvival_mem_Icc
    (stats : ConditionedOpponentOrderStats) (score : ℝ) (p : ℕ) :
    conditionedSurvival score (stats.threshold p) ∈ Set.Icc 0 1 := by
  cases h : stats.threshold p with
  | none => simp [conditionedSurvival]
  | some t =>
      have ht := stats.nonnegative p t h
      simp only [conditionedSurvival]
      constructor
      · exact (Real.exp_pos _).le
      · rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr <| by
          have hRateTime : 0 ≤ Real.exp score * t :=
            mul_nonneg (Real.exp_pos _).le ht
          linarith

/-- Sorted nonnegative opponent arrivals make every displayed rank mass a
genuine nonnegative probability, including the `+∞` padding cases. -/
theorem conditionedRankMass_nonneg
    (stats : ConditionedOpponentOrderStats) (score : ℝ) (p : ℕ) :
    0 ≤ conditionedRankMass stats score p := by
  cases p with
  | zero =>
      simp only [conditionedRankMass, previousConditionedSurvival, if_pos]
      exact sub_nonneg.mpr (conditionedSurvival_mem_Icc stats score 0).2
  | succ p =>
      simp only [conditionedRankMass, previousConditionedSurvival,
        Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      cases hp : stats.threshold p with
      | none =>
          have hnext := stats.padding p hp
          simp [hnext, conditionedSurvival]
      | some t =>
          cases hn : stats.threshold (p + 1) with
          | none =>
              simp only [conditionedSurvival, sub_zero]
              exact (Real.exp_pos _).le
          | some u =>
              have htu := stats.ordered p t u hp hn
              simp only [conditionedSurvival]
              exact sub_nonneg.mpr <| Real.exp_le_exp.mpr <| by
                have hRate : 0 ≤ Real.exp score := (Real.exp_pos _).le
                have hProduct := mul_le_mul_of_nonneg_left htu hRate
                linarith

/-- Conditional expected priority written as the sum over realized ranks. -/
noncomputable def conditionalIntervalPriority
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ) : ℝ :=
  ∑ p ∈ Finset.range slots,
    slotWeight p * conditionedRankMass stats score p

/-- Generic finite Abel identity with the terminal boundary term retained. -/
theorem weighted_interval_sum_eq_abel_with_terminal
    (weight survival : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.range n,
      weight p *
        ((if p = 0 then 1 else survival (p - 1)) - survival p)) =
      weight 0 -
        (∑ p ∈ Finset.range n,
          (weight p - weight (p + 1)) * survival p) -
        weight n * (if n = 0 then 1 else survival (n - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      ring

/-- Abel/summation-by-parts form of conditional priority.  Zero-based
`slotWeight 0` is the paper's `w₁`, and `slotWeight slots = 0` is its
`w_(K+1) = 0` convention. -/
noncomputable def conditionalPriority
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ) : ℝ :=
  slotWeight 0 - ∑ p ∈ Finset.range slots,
    (slotWeight p - slotWeight (p + 1)) *
      conditionedSurvival score (stats.threshold p)

theorem conditionalIntervalPriority_eq_abel
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ)
    (hTerminal : slotWeight slots = 0) :
    conditionalIntervalPriority slotWeight slots stats score =
      conditionalPriority slotWeight slots stats score := by
  have h := weighted_interval_sum_eq_abel_with_terminal slotWeight
    (fun p => conditionedSurvival score (stats.threshold p)) slots
  rw [hTerminal, zero_mul, sub_zero] at h
  simpa [conditionalIntervalPriority, conditionalPriority,
    conditionedRankMass, previousConditionedSurvival] using h

/-- The derivative kernel produced by differentiating a survival term with
respect to the own score. -/
noncomputable def conditionedMarginal (score : ℝ) : Option ℝ → ℝ
  | none => 0
  | some t =>
      (Real.exp score * t) * Real.exp (-(Real.exp score * t))

theorem conditionedSurvival_hasDerivAt
    (threshold : Option ℝ) (score : ℝ) :
    HasDerivAt (fun s => conditionedSurvival s threshold)
      (-conditionedMarginal score threshold) score := by
  cases threshold with
  | none =>
      simpa [conditionedSurvival, conditionedMarginal] using
        (hasDerivAt_const score (0 : ℝ))
  | some t =>
      simpa [conditionedSurvival, conditionedMarginal, mul_comm,
        mul_left_comm, mul_assoc] using
        (((Real.hasDerivAt_exp score).mul_const t).neg.exp)

/-- Differentiation commutes with a finite sum whose coefficients are
constant in the differentiation variable. -/
theorem hasDerivAt_finset_sum_const_mul
    (s : Finset ℕ) (coefficient : ℕ → ℝ)
    (f f' : ℕ → ℝ → ℝ) (x : ℝ)
    (hDeriv : ∀ i, HasDerivAt (f i) (f' i x) x) :
    HasDerivAt (fun y => ∑ i ∈ s, coefficient i * f i y)
      (∑ i ∈ s, coefficient i * f' i x) x := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasDerivAt_const x (0 : ℝ))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((hDeriv i).const_mul (coefficient i)).add ih

/-- Explicit derivative of the conditional priority with respect to score. -/
noncomputable def conditionalPriorityScoreDerivative
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ) : ℝ :=
  ∑ p ∈ Finset.range slots,
    (slotWeight p - slotWeight (p + 1)) *
      conditionedMarginal score (stats.threshold p)

theorem conditionalPriority_hasDerivAt_score
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ) :
    HasDerivAt (conditionalPriority slotWeight slots stats)
      (conditionalPriorityScoreDerivative slotWeight slots stats score)
      score := by
  have hsum :
      HasDerivAt
        (fun s => ∑ p ∈ Finset.range slots,
          (slotWeight p - slotWeight (p + 1)) *
            conditionedSurvival s (stats.threshold p))
        (∑ p ∈ Finset.range slots,
          (slotWeight p - slotWeight (p + 1)) *
            (-conditionedMarginal score (stats.threshold p))) score := by
    exact hasDerivAt_finset_sum_const_mul (Finset.range slots)
      (fun p => slotWeight p - slotWeight (p + 1))
      (fun p s => conditionedSurvival s (stats.threshold p))
      (fun p _ => -conditionedMarginal score (stats.threshold p)) score
      (fun p => conditionedSurvival_hasDerivAt (stats.threshold p) score)
  simpa [conditionalPriority, conditionalPriorityScoreDerivative] using
    (hasDerivAt_const score (slotWeight 0)).sub hsum

/-- Tangency of `exp` at `u - 1` yields the sharp elementary maximum
`u exp (-u) ≤ 1/e` for `u ≥ 0`. -/
theorem exp_marginal_le_inv_e (u : ℝ) :
    u * Real.exp (-u) ≤ Real.exp (-1) := by
  have htangent : u ≤ Real.exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  calc
    u * Real.exp (-u) ≤ Real.exp (u - 1) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right htangent (Real.exp_pos _).le
    _ = Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem conditionedMarginal_mem_Icc
    (stats : ConditionedOpponentOrderStats) (score : ℝ) (p : ℕ) :
    conditionedMarginal score (stats.threshold p) ∈
      Set.Icc 0 (Real.exp (-1)) := by
  cases h : stats.threshold p with
  | none => exact ⟨le_rfl, (Real.exp_pos _).le⟩
  | some t =>
      have ht := stats.nonnegative p t h
      have hu : 0 ≤ Real.exp score * t :=
        mul_nonneg (Real.exp_pos _).le ht
      simp only [conditionedMarginal]
      exact ⟨mul_nonneg hu (Real.exp_pos _).le,
        exp_marginal_le_inv_e _⟩

/-- Slot-weight decrements telescope to the top weight minus the terminal
weight. -/
theorem sum_weight_decrements (slotWeight : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.range n,
      (slotWeight p - slotWeight (p + 1))) =
      slotWeight 0 - slotWeight n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Score derivative bound after summing the sharp kernel estimate with the
nonnegative slot-weight decrements. -/
theorem conditionalPriorityScoreDerivative_bounds
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0) :
    conditionalPriorityScoreDerivative slotWeight slots stats score ∈
      Set.Icc 0 (slotWeight 0 * Real.exp (-1)) := by
  have hDecrement : ∀ p, 0 ≤ slotWeight p - slotWeight (p + 1) :=
    fun p => sub_nonneg.mpr (hWeight (Nat.le_succ p))
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hDecrement p)
      (conditionedMarginal_mem_Icc stats score p).1
  · calc
      conditionalPriorityScoreDerivative slotWeight slots stats score
          ≤ ∑ p ∈ Finset.range slots,
              (slotWeight p - slotWeight (p + 1)) * Real.exp (-1) := by
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_left
              (conditionedMarginal_mem_Icc stats score p).2
              (hDecrement p)
      _ = (slotWeight 0 - slotWeight slots) * Real.exp (-1) := by
            rw [← Finset.sum_mul, sum_weight_decrements]
      _ = slotWeight 0 * Real.exp (-1) := by
            rw [hTerminal, sub_zero]

/-- Conditional priority is itself a bounded allocation in `[0, w₁]`. -/
theorem conditionalPriority_bounds
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats) (score : ℝ)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0) :
    conditionalPriority slotWeight slots stats score ∈
      Set.Icc 0 (slotWeight 0) := by
  have hDecrement : ∀ p, 0 ≤ slotWeight p - slotWeight (p + 1) :=
    fun p => sub_nonneg.mpr (hWeight (Nat.le_succ p))
  have hSumNonneg :
      0 ≤ ∑ p ∈ Finset.range slots,
        (slotWeight p - slotWeight (p + 1)) *
          conditionedSurvival score (stats.threshold p) := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (hDecrement p)
      (conditionedSurvival_mem_Icc stats score p).1
  have hSumUpper :
      (∑ p ∈ Finset.range slots,
        (slotWeight p - slotWeight (p + 1)) *
          conditionedSurvival score (stats.threshold p)) ≤ slotWeight 0 := by
    calc
      _ ≤ ∑ p ∈ Finset.range slots,
          (slotWeight p - slotWeight (p + 1)) * 1 := by
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_left
              (conditionedSurvival_mem_Icc stats score p).2
              (hDecrement p)
      _ = slotWeight 0 := by
            simp only [mul_one, sum_weight_decrements, hTerminal, sub_zero]
  exact ⟨by
      simpa [conditionalPriority] using sub_nonneg.mpr hSumUpper,
    by
      simpa [conditionalPriority] using
        sub_le_self (slotWeight 0) hSumNonneg⟩

/-- Conditional priority as a function of the own bid. -/
noncomputable def conditionalBidPriority
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) : ℝ :=
  conditionalPriority slotWeight slots stats
    ((bid - reserve) / temperature)

/-- Explicit bid derivative; the score derivative is divided by `τ`. -/
noncomputable def conditionalBidDerivative
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) : ℝ :=
  conditionalPriorityScoreDerivative slotWeight slots stats
    ((bid - reserve) / temperature) / temperature

theorem conditionalBidPriority_hasDerivAt
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) :
    HasDerivAt
      (conditionalBidPriority slotWeight slots stats reserve temperature)
      (conditionalBidDerivative slotWeight slots stats reserve temperature bid)
      bid := by
  simpa [conditionalBidPriority, conditionalBidDerivative, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
    (conditionalPriority_hasDerivAt_score slotWeight slots stats
      ((bid - reserve) / temperature)).comp bid
      (((hasDerivAt_id bid).sub_const reserve).div_const temperature)

/-- Pathwise version of the theorem's bid derivative bound. -/
theorem conditionalBidDerivative_bounds
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0) :
    conditionalBidDerivative slotWeight slots stats reserve temperature bid ∈
      Set.Icc 0 (slotWeight 0 / (Real.exp 1 * temperature)) := by
  have hScore := conditionalPriorityScoreDerivative_bounds slotWeight slots
    stats ((bid - reserve) / temperature) hWeight hTerminal
  constructor
  · exact div_nonneg hScore.1 hTemperature.le
  · calc
      conditionalBidDerivative slotWeight slots stats reserve temperature bid
          ≤ (slotWeight 0 * Real.exp (-1)) / temperature :=
            (div_le_div_iff_of_pos_right hTemperature).2 hScore.2
      _ = slotWeight 0 / (Real.exp 1 * temperature) := by
            rw [Real.exp_neg]
            field_simp [ne_of_gt (Real.exp_pos (1 : ℝ)),
              ne_of_gt hTemperature]

/-- A reusable mean-value bridge from an explicit nonnegative bounded
derivative to a global absolute-difference bound. -/
theorem global_lipschitz_of_hasDerivAt_Icc
    (f f' : ℝ → ℝ) (C : ℝ)
    (hDeriv : ∀ x, HasDerivAt f (f' x) x)
    (hBounds : ∀ x, f' x ∈ Set.Icc 0 C) :
    ∀ a b, |f b - f a| ≤ C * |b - a| := by
  intro a b
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := f) (s := (Set.univ : Set ℝ)) (x := a) (y := b) (C := C)
    (fun x _ => (hDeriv x).differentiableAt)
    (fun x _ => by
      rw [(hDeriv x).deriv, Real.norm_eq_abs,
        abs_of_nonneg (hBounds x).1]
      exact (hBounds x).2)
    convex_univ (Set.mem_univ a) (Set.mem_univ b)
  simpa [Real.norm_eq_abs] using h

/-- Conditional allocation is nondecreasing in the own bid. -/
theorem conditionalBidPriority_monotone
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0) :
    Monotone
      (conditionalBidPriority slotWeight slots stats reserve temperature) := by
  apply monotone_of_hasDerivAt_nonneg
    (fun bid => conditionalBidPriority_hasDerivAt slotWeight slots stats
      reserve temperature bid)
  intro bid
  exact (conditionalBidDerivative_bounds slotWeight slots stats reserve
    temperature bid hTemperature hWeight hTerminal).1

/-- Conditional, pathwise global stability. -/
theorem conditionalBidPriority_lipschitz
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0) :
    ∀ a b,
      |conditionalBidPriority slotWeight slots stats reserve temperature b -
          conditionalBidPriority slotWeight slots stats reserve temperature a| ≤
        (slotWeight 0 / (Real.exp 1 * temperature)) * |b - a| := by
  apply global_lipschitz_of_hasDerivAt_Icc
    (conditionalBidPriority slotWeight slots stats reserve temperature)
    (conditionalBidDerivative slotWeight slots stats reserve temperature)
    (slotWeight 0 / (Real.exp 1 * temperature))
  · exact fun bid => conditionalBidPriority_hasDerivAt slotWeight slots stats
      reserve temperature bid
  · exact fun bid => conditionalBidDerivative_bounds slotWeight slots stats
      reserve temperature bid hTemperature hWeight hTerminal

/-! ## Probability and Bochner-integral bridge -/

/-- Interim priority after averaging over the conditioned opponent order
statistics. -/
noncomputable def conditionedInterimPriority
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) : ℝ :=
  ∫ ω, conditionalBidPriority slotWeight slots (stats ω)
    reserve temperature bid ∂μ

/-- Expected value of the explicitly derived conditional bid derivative. -/
noncomputable def conditionedInterimDerivative
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) : ℝ :=
  ∫ ω, conditionalBidDerivative slotWeight slots (stats ω)
    reserve temperature bid ∂μ

theorem conditionalBidPriority_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hMeasurable : AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    MeasureTheory.Integrable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature bid) μ := by
  apply MeasureTheory.Integrable.of_mem_Icc 0 (slotWeight 0) hMeasurable
  filter_upwards with ω
  simpa [conditionalBidPriority] using
    conditionalPriority_bounds slotWeight slots (stats ω)
      ((bid - reserve) / temperature) hWeight hTerminal

theorem conditionalBidDerivative_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hMeasurable : AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    MeasureTheory.Integrable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature bid) μ := by
  apply MeasureTheory.Integrable.of_mem_Icc 0
    (slotWeight 0 / (Real.exp 1 * temperature)) hMeasurable
  filter_upwards with ω
  exact conditionalBidDerivative_bounds slotWeight slots (stats ω) reserve
    temperature bid hTemperature hWeight hTerminal

/-- Integrating a uniform pathwise Lipschitz estimate under a probability
measure preserves the same constant. -/
theorem integral_lipschitz_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (F : ℝ → Ω → ℝ) (C : ℝ)
    (hIntegrable : ∀ x, MeasureTheory.Integrable (F x) μ)
    (hPath : ∀ ω a b, |F b ω - F a ω| ≤ C * |b - a|) :
    ∀ a b,
      |(∫ ω, F b ω ∂μ) - ∫ ω, F a ω ∂μ| ≤ C * |b - a| := by
  intro a b
  calc
    |(∫ ω, F b ω ∂μ) - ∫ ω, F a ω ∂μ| =
        ‖∫ ω, (F b ω - F a ω) ∂μ‖ := by
          rw [MeasureTheory.integral_sub (hIntegrable b) (hIntegrable a)]
          rfl
    _ ≤ (C * |b - a|) * μ.real Set.univ := by
          apply MeasureTheory.norm_integral_le_of_norm_le_const
          filter_upwards with ω
          simpa [Real.norm_eq_abs] using hPath ω a b
    _ = C * |b - a| := by simp

/-- Global eligible-formula Lipschitz bound after averaging.  This proof does
not require differentiating under the integral sign. -/
theorem conditionedInterimPriority_lipschitz
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ bid, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    ∀ a b,
      |conditionedInterimPriority μ slotWeight slots stats reserve temperature b -
          conditionedInterimPriority μ slotWeight slots stats reserve temperature a| ≤
        (slotWeight 0 / (Real.exp 1 * temperature)) * |b - a| := by
  apply integral_lipschitz_of_pointwise μ
    (fun bid ω => conditionalBidPriority slotWeight slots (stats ω)
      reserve temperature bid)
    (slotWeight 0 / (Real.exp 1 * temperature))
  · intro bid
    exact conditionalBidPriority_integrable μ slotWeight slots stats reserve
      temperature bid hWeight hTerminal (hPriorityMeasurable bid)
  · intro ω
    exact conditionalBidPriority_lipschitz slotWeight slots (stats ω)
      reserve temperature hTemperature hWeight hTerminal

theorem conditionedInterimPriority_monotone
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ bid, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    Monotone
      (conditionedInterimPriority μ slotWeight slots stats reserve temperature) := by
  intro a b hab
  apply MeasureTheory.integral_mono
    (conditionalBidPriority_integrable μ slotWeight slots stats reserve
      temperature a hWeight hTerminal (hPriorityMeasurable a))
    (conditionalBidPriority_integrable μ slotWeight slots stats reserve
      temperature b hWeight hTerminal (hPriorityMeasurable b))
  intro ω
  exact conditionalBidPriority_monotone slotWeight slots (stats ω) reserve
    temperature hTemperature hWeight hTerminal hab

/-- Rademacher consequence requiring only measurable conditional priorities:
the interim eligible formula is differentiable almost everywhere and its
derivative lies in the claimed interval. -/
theorem conditionedInterimPriority_ae_derivative_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ bid, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    ∀ᵐ bid : ℝ,
      DifferentiableAt ℝ
          (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
          bid ∧
        deriv
          (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
          bid ∈ Set.Icc 0
            (slotWeight 0 / (Real.exp 1 * temperature)) := by
  let C := slotWeight 0 / (Real.exp 1 * temperature)
  have hTop : 0 ≤ slotWeight 0 := by
    rw [← hTerminal]
    exact hWeight (Nat.zero_le slots)
  have hC : 0 ≤ C :=
    div_nonneg hTop (mul_pos (Real.exp_pos 1) hTemperature).le
  have hLip := conditionedInterimPriority_lipschitz μ slotWeight slots stats
    reserve temperature hTemperature hWeight hTerminal hPriorityMeasurable
  have hLipWith : LipschitzWith ⟨C, hC⟩
      (conditionedInterimPriority μ slotWeight slots stats reserve temperature) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa [C, Real.dist_eq, abs_sub_comm] using hLip a b
  filter_upwards [hLipWith.ae_differentiableAt_real] with bid hDiff
  have hMono := conditionedInterimPriority_monotone μ slotWeight slots stats
    reserve temperature hTemperature hWeight hTerminal hPriorityMeasurable
  have hLower : 0 ≤ deriv
      (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
      bid := hMono.deriv_nonneg
  have hUpperNorm :
      ‖deriv
        (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
        bid‖ ≤ C := hDiff.hasDerivAt.le_of_lipschitz hLipWith
  rw [Real.norm_eq_abs, abs_of_nonneg hLower] at hUpperNorm
  exact ⟨hDiff, hLower, hUpperNorm⟩

/-- A general dominated differentiation bridge specialized to real-valued
Bochner expectations and a uniform nonnegative derivative bound. -/
theorem integral_hasDerivAt_of_uniform_deriv_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (F F' : ℝ → Ω → ℝ) (C : ℝ) (x₀ : ℝ)
    (hFMeasurable : ∀ x, AEMeasurable (F x) μ)
    (hFIntegrable : ∀ x, MeasureTheory.Integrable (F x) μ)
    (hF'Measurable : ∀ x, AEMeasurable (F' x) μ)
    (hBound : ∀ ω x, F' x ω ∈ Set.Icc 0 C)
    (hDeriv : ∀ ω x, HasDerivAt (fun y => F y ω) (F' x ω) x) :
    HasDerivAt (fun x => ∫ ω, F x ω ∂μ) (∫ ω, F' x₀ ω ∂μ) x₀ := by
  have hResult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := x₀)
    (s := Set.univ) (bound := fun _ : Ω => C)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      (hFMeasurable x).aestronglyMeasurable)
    (hFIntegrable x₀)
    ((hF'Measurable x₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBound ω x).1]
      exact (hBound ω x).2)
    (MeasureTheory.integrable_const C)
    (Filter.Eventually.of_forall fun ω x _ => hDeriv ω x)
  exact hResult.2

/-- Dominated differentiation of the actual conditional top-K expression. -/
theorem conditionedInterimPriority_hasDerivAt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature z) μ)
    (hDerivativeMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature z) μ) :
    HasDerivAt
      (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
      (conditionedInterimDerivative μ slotWeight slots stats reserve temperature bid)
      bid := by
  have h := integral_hasDerivAt_of_uniform_deriv_bound μ
    (fun z ω => conditionalBidPriority slotWeight slots (stats ω)
      reserve temperature z)
    (fun z ω => conditionalBidDerivative slotWeight slots (stats ω)
      reserve temperature z)
    (slotWeight 0 / (Real.exp 1 * temperature)) bid
    hPriorityMeasurable
    (fun z => conditionalBidPriority_integrable μ slotWeight slots stats reserve
      temperature z hWeight hTerminal (hPriorityMeasurable z))
    hDerivativeMeasurable
    (fun ω z => conditionalBidDerivative_bounds slotWeight slots (stats ω)
      reserve temperature z hTemperature hWeight hTerminal)
    (fun ω z => conditionalBidPriority_hasDerivAt slotWeight slots (stats ω)
      reserve temperature z)
  simpa [conditionedInterimPriority, conditionedInterimDerivative] using h

theorem conditionedInterimDerivative_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hDerivativeMeasurable : AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature bid) μ) :
    conditionedInterimDerivative μ slotWeight slots stats reserve temperature bid ∈
      Set.Icc 0 (slotWeight 0 / (Real.exp 1 * temperature)) := by
  have hIntegrable := conditionalBidDerivative_integrable μ slotWeight slots
    stats reserve temperature bid hTemperature hWeight hTerminal
    hDerivativeMeasurable
  constructor
  · exact MeasureTheory.integral_nonneg fun ω =>
      (conditionalBidDerivative_bounds slotWeight slots (stats ω) reserve
        temperature bid hTemperature hWeight hTerminal).1
  · calc
      conditionedInterimDerivative μ slotWeight slots stats reserve temperature bid
          ≤ ∫ _ : Ω, slotWeight 0 / (Real.exp 1 * temperature) ∂μ := by
            apply MeasureTheory.integral_mono hIntegrable
              (MeasureTheory.integrable_const _)
            intro ω
            exact (conditionalBidDerivative_bounds slotWeight slots (stats ω)
              reserve temperature bid hTemperature hWeight hTerminal).2
      _ = slotWeight 0 / (Real.exp 1 * temperature) := by simp

theorem conditionedInterimPriority_deriv_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature z) μ)
    (hDerivativeMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature z) μ) :
    deriv
      (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
      bid ∈ Set.Icc 0 (slotWeight 0 / (Real.exp 1 * temperature)) := by
  rw [(conditionedInterimPriority_hasDerivAt μ slotWeight slots stats reserve
    temperature bid hTemperature hWeight hTerminal hPriorityMeasurable
    hDerivativeMeasurable).deriv]
  exact conditionedInterimDerivative_bounds μ slotWeight slots stats reserve
    temperature bid hTemperature hWeight hTerminal
    (hDerivativeMeasurable bid)

/-! ## Reserve screening and the final stability theorem -/

/-- Reserve-screened version of the conditioned interim allocation. -/
noncomputable def conditionedReserveInterimPriority
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) : ℝ :=
  if reserve ≤ bid then
    conditionedInterimPriority μ slotWeight slots stats reserve temperature bid
  else 0

theorem conditionedReserveInterimPriority_of_lt_reserve
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) (hBid : bid < reserve) :
    conditionedReserveInterimPriority μ slotWeight slots stats reserve
      temperature bid = 0 := by
  simp [conditionedReserveInterimPriority, not_le.mpr hBid]

theorem conditionedReserveInterimPriority_hasRightDerivAt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature z) μ)
    (hDerivativeMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature z) μ) :
    HasDerivWithinAt
      (conditionedReserveInterimPriority μ slotWeight slots stats reserve
        temperature)
      (conditionedInterimDerivative μ slotWeight slots stats reserve temperature
        reserve)
      (Set.Ici reserve) reserve := by
  apply (conditionedInterimPriority_hasDerivAt μ slotWeight slots stats reserve
    temperature reserve hTemperature hWeight hTerminal hPriorityMeasurable
    hDerivativeMeasurable).hasDerivWithinAt.congr_of_mem
  · intro bid hBid
    change reserve ≤ bid at hBid
    simp [conditionedReserveInterimPriority, hBid]
  · exact Set.mem_Ici.mpr le_rfl

theorem conditionedReserveInterimPriority_hasDerivAt_of_reserve_lt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature bid : ℝ) (hBid : reserve < bid)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature z) μ)
    (hDerivativeMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature z) μ) :
    HasDerivAt
      (conditionedReserveInterimPriority μ slotWeight slots stats reserve
        temperature)
      (conditionedInterimDerivative μ slotWeight slots stats reserve temperature bid)
      bid := by
  apply (conditionedInterimPriority_hasDerivAt μ slotWeight slots stats reserve
    temperature bid hTemperature hWeight hTerminal hPriorityMeasurable
    hDerivativeMeasurable).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hBid] with z hz
  change reserve < z at hz
  simp [conditionedReserveInterimPriority, hz.le]

/-- Formal counterpart of `thm:stability` for general top-K nonincreasing
slot weights.  It packages differentiability and the sharp derivative bound,
global eligible-region Lipschitz stability, the right derivative at the
reserve, and ordinary differentiability strictly above the reserve. -/
theorem generalTopKStability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (stats : Ω → ConditionedOpponentOrderStats)
    (reserve temperature : ℝ)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hTerminal : slotWeight slots = 0)
    (hPriorityMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidPriority slotWeight slots (stats ω)
        reserve temperature z) μ)
    (hDerivativeMeasurable : ∀ z, AEMeasurable
      (fun ω => conditionalBidDerivative slotWeight slots (stats ω)
        reserve temperature z) μ) :
    (∀ bid,
        HasDerivAt
          (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
          (conditionedInterimDerivative μ slotWeight slots stats reserve
            temperature bid) bid ∧
        deriv
          (conditionedInterimPriority μ slotWeight slots stats reserve temperature)
          bid ∈ Set.Icc 0
            (slotWeight 0 / (Real.exp 1 * temperature))) ∧
      (∀ a b, reserve ≤ a → reserve ≤ b →
        |conditionedReserveInterimPriority μ slotWeight slots stats reserve
              temperature b -
            conditionedReserveInterimPriority μ slotWeight slots stats reserve
              temperature a| ≤
          (slotWeight 0 / (Real.exp 1 * temperature)) * |b - a|) ∧
      HasDerivWithinAt
        (conditionedReserveInterimPriority μ slotWeight slots stats reserve
          temperature)
        (conditionedInterimDerivative μ slotWeight slots stats reserve temperature
          reserve)
        (Set.Ici reserve) reserve ∧
      ∀ bid, reserve < bid →
        HasDerivAt
          (conditionedReserveInterimPriority μ slotWeight slots stats reserve
            temperature)
          (conditionedInterimDerivative μ slotWeight slots stats reserve
            temperature bid) bid := by
  constructor
  · intro bid
    exact ⟨conditionedInterimPriority_hasDerivAt μ slotWeight slots stats reserve
        temperature bid hTemperature hWeight hTerminal hPriorityMeasurable
        hDerivativeMeasurable,
      conditionedInterimPriority_deriv_bounds μ slotWeight slots stats reserve
        temperature bid hTemperature hWeight hTerminal hPriorityMeasurable
        hDerivativeMeasurable⟩
  constructor
  · intro a b ha hb
    simp only [conditionedReserveInterimPriority, if_pos ha, if_pos hb]
    exact conditionedInterimPriority_lipschitz μ slotWeight slots stats reserve
      temperature hTemperature hWeight hTerminal hPriorityMeasurable a b
  constructor
  · exact conditionedReserveInterimPriority_hasRightDerivAt μ slotWeight slots
      stats reserve temperature hTemperature hWeight hTerminal
      hPriorityMeasurable hDerivativeMeasurable
  · intro bid hBid
    exact conditionedReserveInterimPriority_hasDerivAt_of_reserve_lt μ
      slotWeight slots stats reserve temperature bid hBid hTemperature hWeight
      hTerminal hPriorityMeasurable hDerivativeMeasurable

end SmoothingCliff.Mechanism
