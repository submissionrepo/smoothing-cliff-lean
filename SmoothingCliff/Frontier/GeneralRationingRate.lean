import SmoothingCliff.Frontier.InterimBridgeMeanField
import SmoothingCliff.Frontier.RationedRamp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-!
# The rationing rate at a general value law

This file closes the last finite-support gap in Theorem `thm:meanfield` of
`Smoothing_the_Cliff_ITCS.tex`.  Parts (i) and (ii) already hold for a general
Borel law `F` (`SmoothingCliff.Frontier.InterimBridgeMeanField` and
`SmoothingCliff.Frontier.PopulationProgram`), and so does every structural
claim in part (iii) (`SmoothingCliff.Frontier.RationedRamp`,
`SmoothingCliff.Frontier.SlotLottery`,
`SmoothingCliff.Frontier.RationedRampPayments`).  Only the achievability bound

`V_n(x^RR) ≥ V*(W̄_n) - b̄ w₁ / (4 √n)`

was restricted to finitely supported laws
(`rationedRampRule_finiteLaw_achievability`, and
`rationedRampRule_iid_achievability`, which discharges its second-moment
premise from independence).  Here the bound is proved in the measure-theoretic
setting of `InterimBridgeMeanField`, where the profile law is
`profileLaw F = Measure.pi fun _ => F`.

## The benchmark is the one from part (i)

The benchmark is `curveWelfare F (postedRamp weight sensitivity threshold)`,
the population-programme value of the calibrated ramp.  That is exactly the
object bounding every certified rule from above in part (i)
(`certifiedRule_le_postedRamp`), and by part (ii)
(`postedRamp_solves_population_program`) it is the programme value
`V*(W̄_n)`.  Nothing is restated around a missing step: the closing theorem
`rationedRampMap_frontier_sandwich` puts the same expression on both sides of
the frontier, and `rationedRampMap_certifiedRule` shows the rationed ramp is a
member of the very class part (i) quantifies over.

## Hypotheses assumed, and why each is needed

* `[IsProbabilityMeasure F]`.  The profile law is a product of probability
  measures; the marginal identity `MeasureTheory.integral_comp_eval` and the
  variance decomposition `ProbabilityTheory.variance_sum_pi` both need it.
* `hFirstMoment : Integrable (fun v : ℝ => v) F`, a finite first moment.  This
  is the standing convention of `SmoothingCliff.Frontier.PopulationProgram`.
  It is what makes the value-weighted integrands `b ↦ b i * x b i` integrable.
  The paper's bounded value range `[r, b̄]` implies it, and
  `rationedRampMap_achievability_of_bounded_support` derives it from support in
  `Set.Icc reserve upperValue`; so nothing stronger than the paper is assumed.
* `hValueLe : ∀ᵐ v ∂F, v ≤ upperValue` with `hUpper : 0 ≤ upperValue`, the
  paper's `v ≤ b̄` and `b̄ ≥ 0`.  They enter only through the pointwise
  rationing-loss inequality `rationedResponse_welfare_loss_le`, which prices the
  mass rationing removes at the value cap.  No lower bound on the support is
  used in the main theorem; values may be negative provided the first moment is
  finite.
* `hSlots : 0 ≤ slots`, so the capacity `w₁ K` is nonnegative.
* `hClears : n * curveMass F (postedRamp weight sensitivity threshold)
  = weight * slots`.  The paper's calibration `E Σ = c := w₁ K_n`, equivalently
  `∫ ξ* dF = W̄_n`.  `exists_threshold_of_mass_le` produces such a threshold.

## The chain

1. `rationedResponse_welfare_loss_le`, already stated for an arbitrary agent
   index, caps the statewise loss by `b̄ (Σ - c)⁺`.
2. `integral_positivePart_eq_half_abs`: `E[(Σ - c)⁺] = ½ E|Σ - c|` when
   `c = E Σ`.
3. `integral_abs_le_of_integral_sq_le`: `E|Y| ≤ B` from `E[Y²] ≤ B²`, obtained
   by expanding `E[(|Y| - E|Y|)²] ≥ 0`.
4. `integral_sq_sub_total_le`: `E[(Σ - E Σ)²] = Var Σ = n Var r₁ ≤ n w₁²/4`,
   from `ProbabilityTheory.variance_sum_pi` (independence of the coordinates of
   a `Measure.pi`) and `ProbabilityTheory.variance_le_sq_of_bounded`
   (Popoviciu).
5. `rationedRampMap_achievability` assembles the four and divides by `n`.

Following the warning recorded in `SmoothingCliff.Frontier.RationingVariance`,
no step unfolds the product structure: the coordinates are reached only through
`MeasureTheory.integral_comp_eval`, `MeasureTheory.integrable_comp_eval`,
`MeasureTheory.measurePreserving_eval` and
`ProbabilityTheory.variance_sum_pi`.
-/

open MeasureTheory

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff

noncomputable section

variable {ι : Type*}

/-! ### Two scalar facts about integrals under a probability law -/

section Scalar

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- Measure-theoretic form of `finite_expected_positivePart_eq_half_abs`: a
centered variable has expected positive part equal to half its mean absolute
deviation. -/
theorem integral_positivePart_eq_half_abs {Y : α → ℝ} (hY : Integrable Y μ)
    (hCenter : ∫ a, Y a ∂μ = 0) :
    ∫ a, max (Y a) 0 ∂μ = (∫ a, |Y a| ∂μ) / 2 := by
  have hfun : (fun a => max (Y a) 0) = fun a => (|Y a| + Y a) / 2 := by
    funext a
    exact positivePart_eq_half_abs_add (Y a)
  rw [hfun, integral_div, integral_add hY.abs hY, hCenter, add_zero]

/-- Measure-theoretic form of `finite_expected_abs_le_of_secondMoment`: the
Cauchy--Schwarz bound of the mean absolute deviation by the square root of the
second moment, in the shape the rationing bound consumes.  It is proved from
`0 ≤ E[(|Y| - E|Y|)²] = E[Y²] - (E|Y|)²`. -/
theorem integral_abs_le_of_integral_sq_le [IsProbabilityMeasure μ] {Y : α → ℝ}
    (hY : Integrable Y μ) (hY2 : Integrable (fun a => Y a ^ 2) μ)
    {bound : ℝ} (hBound : 0 ≤ bound)
    (hSecond : ∫ a, Y a ^ 2 ∂μ ≤ bound ^ 2) :
    ∫ a, |Y a| ∂μ ≤ bound := by
  set m : ℝ := ∫ a, |Y a| ∂μ with hm
  have habs : Integrable (fun a => |Y a|) μ := hY.abs
  have hm0 : 0 ≤ m := integral_nonneg fun a => abs_nonneg _
  have hfun : (fun a => (|Y a| - m) ^ 2)
      = fun a => (Y a ^ 2 - 2 * m * |Y a|) + m ^ 2 := by
    funext a
    rw [sub_sq, sq_abs]
    ring
  have hint1 : Integrable (fun a => Y a ^ 2 - 2 * m * |Y a|) μ :=
    hY2.sub (habs.const_mul (2 * m))
  have hexp : ∫ a, (|Y a| - m) ^ 2 ∂μ = (∫ a, Y a ^ 2 ∂μ) - m ^ 2 := by
    rw [hfun, integral_add hint1 (integrable_const _),
      integral_sub hY2 (habs.const_mul (2 * m)), integral_const_mul, integral_const,
      probReal_univ]
    simp only [smul_eq_mul, one_mul]
    rw [← hm]
    ring
  have hnonneg : 0 ≤ ∫ a, (|Y a| - m) ^ 2 ∂μ :=
    integral_nonneg fun a => sq_nonneg _
  rw [hexp] at hnonneg
  nlinarith [hnonneg, hSecond, hm0, hBound]

end Scalar

/-! ### The rationed ramp as a map on raw profiles -/

variable [Fintype ι]

/-- The rationed-ramp rule of Theorem `thm:meanfield` (iii), read as a map on
raw bid profiles `ι → ℝ` rather than on the eligible subtype.  This is the form
the measure-theoretic setting of `InterimBridgeMeanField` consumes; the two
agree coordinatewise on eligible profiles
(`rationedRampMap_eq_rationedRampRule`). -/
noncomputable def rationedRampMap (weight sensitivity : NNReal)
    (capacity threshold : ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  rationedResponse capacity
    (fun j => postedRamp weight sensitivity threshold (b j)) i

/-- On eligible profiles the raw map is the rule of
`SmoothingCliff.Frontier.RationedRamp`, so the class properties proved there
(anonymity, own and cross monotonicity, own and cross Lipschitz continuity,
lottery implementability and Myerson transfers) transfer verbatim. -/
theorem rationedRampMap_eq_rationedRampRule {reserve : ℝ}
    (weight sensitivity : NNReal) (capacity threshold : ℝ)
    (b : EligibleProfile ι reserve) (i : ι) :
    rationedRampMap weight sensitivity capacity threshold
        (fun j => ((b j : EligibleBid reserve) : ℝ)) i
      = rationedRampRule weight sensitivity capacity threshold b i := rfl

theorem rationedRampMap_apply (weight sensitivity : NNReal)
    (capacity threshold : ℝ) (b : ι → ℝ) (i : ι) :
    rationedRampMap weight sensitivity capacity threshold b i
      = rationShare capacity (postedRamp weight sensitivity threshold (b i))
          (∑ j, postedRamp weight sensitivity threshold (b j)) := rfl

theorem rationedRampMap_nonneg (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) (b : ι → ℝ) (i : ι) :
    0 ≤ rationedRampMap weight sensitivity capacity threshold b i :=
  rationShare_nonneg hCapacity (postedRamp_nonneg _ _ _ _)

theorem rationedRampMap_le_weight (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) (b : ι → ℝ) (i : ι) :
    rationedRampMap weight sensitivity capacity threshold b i ≤ (weight : ℝ) :=
  (rationShare_le_self hCapacity (postedRamp_nonneg _ _ _ _)).trans
    (postedRamp_le _ _ _ _)

theorem rationedRampMap_total_le (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) (b : ι → ℝ) :
    ∑ i, rationedRampMap weight sensitivity capacity threshold b i ≤ capacity :=
  rationedResponse_total_le capacity _ hCapacity

/-- The paper's multiplier form, used here to read off measurability. -/
theorem rationedRampMap_eq_mul_min (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) (b : ι → ℝ) (i : ι) :
    rationedRampMap weight sensitivity capacity threshold b i
      = postedRamp weight sensitivity threshold (b i)
        * min 1 (capacity / ∑ j, postedRamp weight sensitivity threshold (b j)) :=
  rationShare_eq_mul_min hCapacity (postedRamp_nonneg _ _ _ _)
    (Finset.single_le_sum
      (f := fun k => postedRamp weight sensitivity threshold (b k))
      (fun _ _ => postedRamp_nonneg _ _ _ _) (Finset.mem_univ i))

theorem measurable_sum_postedRamp (weight sensitivity : NNReal) (threshold : ℝ) :
    Measurable fun b : ι → ℝ => ∑ j, postedRamp weight sensitivity threshold (b j) :=
  Finset.measurable_sum _ fun j _ =>
    ((postedRamp_lipschitz weight sensitivity threshold).continuous.measurable).comp
      (measurable_pi_apply j)

theorem rationedRampMap_measurable (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) (i : ι) :
    Measurable fun b : ι → ℝ =>
      rationedRampMap weight sensitivity capacity threshold b i := by
  have hg : Measurable (postedRamp weight sensitivity threshold) :=
    (postedRamp_lipschitz weight sensitivity threshold).continuous.measurable
  have hsum := measurable_sum_postedRamp (ι := ι) weight sensitivity threshold
  have hfun : (fun b : ι → ℝ =>
        rationedRampMap weight sensitivity capacity threshold b i)
      = fun b : ι → ℝ => postedRamp weight sensitivity threshold (b i)
        * min 1 (capacity / ∑ j, postedRamp weight sensitivity threshold (b j)) :=
    funext fun b =>
      rationedRampMap_eq_mul_min weight sensitivity threshold hCapacity b i
  rw [hfun]
  exact (hg.comp (measurable_pi_apply i)).mul
    (measurable_const.min (measurable_const.div hsum))

section Update

variable [DecidableEq ι]

theorem sum_postedRamp_update_raw (weight sensitivity : NNReal) (threshold : ℝ)
    (b : ι → ℝ) (i : ι) (v : ℝ) :
    ∑ j, postedRamp weight sensitivity threshold (Function.update b i v j)
      = postedRamp weight sensitivity threshold v
        + ∑ j ∈ Finset.univ.erase i,
            postedRamp weight sensitivity threshold (b j) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · rw [Function.update_self]
  · exact Finset.sum_congr rfl fun k hk => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

theorem rationedRampMap_update_self (weight sensitivity : NNReal)
    (capacity threshold : ℝ) (b : ι → ℝ) (i : ι) (v : ℝ) :
    rationedRampMap weight sensitivity capacity threshold
        (Function.update b i v) i
      = rationShare capacity (postedRamp weight sensitivity threshold v)
          (postedRamp weight sensitivity threshold v
            + ∑ j ∈ Finset.univ.erase i,
                postedRamp weight sensitivity threshold (b j)) := by
  rw [rationedRampMap_apply, sum_postedRamp_update_raw, Function.update_self]

theorem rationedRampMap_ownLipschitz (weight sensitivity : NNReal)
    {capacity : ℝ} (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (i : ι) (b : ι → ℝ) :
    LipschitzWith sensitivity fun v =>
      rationedRampMap weight sensitivity capacity threshold
        (Function.update b i v) i := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, Real.dist_eq, rationedRampMap_update_self,
    rationedRampMap_update_self]
  refine (rationShare_own_dist_le hCapacity (postedRamp_nonneg _ _ _ _)
    (postedRamp_nonneg _ _ _ _)
    (Finset.sum_nonneg fun _ _ => postedRamp_nonneg _ _ _ _)).trans ?_
  exact postedRamp_dist_le weight sensitivity threshold v w

/-- The rationed ramp belongs to the paper's certified class `C^n_S`, so part
(i) of `thm:meanfield` applies to it and both sides of the frontier are
measured against the same benchmark. -/
theorem rationedRampMap_certifiedRule (weight sensitivity : NNReal)
    {slots : ℝ} (threshold : ℝ) (hSlots : 0 ≤ slots) :
    CertifiedRule (ι := ι) weight sensitivity slots
      (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold) := by
  have hCapacity : (0 : ℝ) ≤ (weight : ℝ) * slots :=
    mul_nonneg weight.coe_nonneg hSlots
  exact
    { measurable := fun i =>
        rationedRampMap_measurable weight sensitivity threshold hCapacity i
      nonneg := fun b i =>
        rationedRampMap_nonneg weight sensitivity threshold hCapacity b i
      le_weight := fun b i =>
        rationedRampMap_le_weight weight sensitivity threshold hCapacity b i
      ownLipschitz := fun i b =>
        rationedRampMap_ownLipschitz weight sensitivity threshold hCapacity i b
      capacity := fun b =>
        rationedRampMap_total_le weight sensitivity threshold hCapacity b }

end Update

/-! ### Marginal identities under the profile law -/

theorem integral_coord_comp (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι)
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g F) :
    ∫ b, g (b i) ∂profileLaw (ι := ι) F = ∫ v, g v ∂F := by
  unfold profileLaw
  exact integral_comp_eval hg

theorem integrable_coord_comp (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι)
    {g : ℝ → ℝ} (hg : Integrable g F) :
    Integrable (fun b : ι → ℝ => g (b i)) (profileLaw (ι := ι) F) := by
  unfold profileLaw
  exact integrable_comp_eval hg

/-- Expected total posted response: `E Σ = n ∫ ξ* dF`. -/
theorem integral_sum_postedRamp (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (threshold : ℝ) :
    ∫ b, (∑ j, postedRamp weight sensitivity threshold (b j))
        ∂profileLaw (ι := ι) F
      = (Fintype.card ι : ℝ)
        * curveMass F (postedRamp weight sensitivity threshold) := by
  have hshape := postedRamp_curveShape weight sensitivity threshold
  rw [integral_finsetSum _ fun j _ =>
    integrable_coord_comp F j (hshape.integrable F)]
  rw [Finset.sum_congr rfl fun j _ =>
    integral_coord_comp F j hshape.measurable.aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- Expected value-weighted posted response:
`E[Σ_i v_i ξ*(v_i)] = n ∫ v ξ* dF`. -/
theorem integral_sum_value_postedRamp (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (weight sensitivity : NNReal) (threshold : ℝ) :
    ∫ b, (∑ i, b i * postedRamp weight sensitivity threshold (b i))
        ∂profileLaw (ι := ι) F
      = (Fintype.card ι : ℝ)
        * curveWelfare F (postedRamp weight sensitivity threshold) := by
  have hshape := postedRamp_curveShape weight sensitivity threshold
  have hvalue : Integrable
      (fun v : ℝ => v * postedRamp weight sensitivity threshold v) F :=
    hshape.integrable_value_mul F hFirstMoment
  rw [integral_finsetSum _ fun i _ => integrable_coord_comp F i hvalue]
  rw [Finset.sum_congr rfl fun i _ =>
    integral_coord_comp F i (g := fun v => v * postedRamp weight sensitivity threshold v)
      hvalue.aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-! ### The variance of the total response -/

/-- **Independence and Popoviciu at a general law.**  The total posted response
deviates from its mean by at most `n w₁² / 4` in mean square.  The two inputs
are `ProbabilityTheory.variance_sum_pi`, which turns the variance of a sum of
coordinatewise functions of a `Measure.pi` into a sum of coordinate variances,
and `ProbabilityTheory.variance_le_sq_of_bounded`, Popoviciu's inequality for a
variable in `[0, w₁]`. -/
theorem integral_sq_sub_total_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (threshold : ℝ) :
    ∫ b, ((∑ j, postedRamp weight sensitivity threshold (b j))
          - (Fintype.card ι : ℝ)
            * curveMass F (postedRamp weight sensitivity threshold)) ^ 2
        ∂profileLaw (ι := ι) F
      ≤ (Fintype.card ι : ℝ) * (weight : ℝ) ^ 2 / 4 := by
  classical
  have hshape := postedRamp_curveShape weight sensitivity threshold
  have hEsum := integral_sum_postedRamp (ι := ι) F weight sensitivity threshold
  set g : ℝ → ℝ := postedRamp weight sensitivity threshold with hgdef
  set Y : (ι → ℝ) → ℝ := ∑ _i : ι, fun b : ι → ℝ => g (b _i) with hYdef
  have hYapply : ∀ b : ι → ℝ, Y b = ∑ i, g (b i) := by
    intro b
    rw [hYdef]
    simp
  have hIcc : ∀ᵐ v ∂F, g v ∈ Set.Icc (0 : ℝ) (weight : ℝ) :=
    Filter.Eventually.of_forall fun v =>
      Set.mem_Icc.mpr ⟨hshape.nonneg v, hshape.le_weight v⟩
  have hMemLp : MemLp g 2 F :=
    memLp_of_bounded hIcc hshape.measurable.aestronglyMeasurable 2
  have hYfun : Y = fun b : ι → ℝ => ∑ i, g (b i) := funext hYapply
  have hYmeas : AEMeasurable Y (profileLaw (ι := ι) F) := by
    refine Measurable.aemeasurable ?_
    rw [hYfun]
    exact Finset.measurable_sum _ fun i _ =>
      hshape.measurable.comp (measurable_pi_apply i)
  have hEY : ∫ b, Y b ∂profileLaw (ι := ι) F
      = (Fintype.card ι : ℝ) * curveMass F g := by
    rw [hYfun]
    exact hEsum
  have hvar : ProbabilityTheory.variance Y (profileLaw (ι := ι) F)
      = ∑ _i : ι, ProbabilityTheory.variance g F := by
    rw [hYdef]
    exact ProbabilityTheory.variance_sum_pi (μ := fun _ : ι => F)
      (X := fun _ : ι => g) fun _ => hMemLp
  have hpop : ProbabilityTheory.variance g F ≤ (weight : ℝ) ^ 2 / 4 := by
    have h := ProbabilityTheory.variance_le_sq_of_bounded
      (μ := F) (a := (0 : ℝ)) (b := (weight : ℝ)) (X := g) hIcc
      hshape.measurable.aemeasurable
    calc ProbabilityTheory.variance g F ≤ (((weight : ℝ) - 0) / 2) ^ 2 := h
      _ = (weight : ℝ) ^ 2 / 4 := by ring
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hvarLe : ProbabilityTheory.variance Y (profileLaw (ι := ι) F)
      ≤ (Fintype.card ι : ℝ) * (weight : ℝ) ^ 2 / 4 := by
    rw [hvar, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc (Fintype.card ι : ℝ) * ProbabilityTheory.variance g F
        ≤ (Fintype.card ι : ℝ) * ((weight : ℝ) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hpop hn
      _ = (Fintype.card ι : ℝ) * (weight : ℝ) ^ 2 / 4 := by ring
  rw [ProbabilityTheory.variance_eq_integral hYmeas, hEY] at hvarLe
  calc ∫ b, ((∑ j, g (b j)) - (Fintype.card ι : ℝ) * curveMass F g) ^ 2
        ∂profileLaw (ι := ι) F
      = ∫ b, (Y b - (Fintype.card ι : ℝ) * curveMass F g) ^ 2
        ∂profileLaw (ι := ι) F := by
        refine integral_congr_ae ?_
        filter_upwards with b
        rw [hYapply b]
    _ ≤ (Fintype.card ι : ℝ) * (weight : ℝ) ^ 2 / 4 := hvarLe

/-! ### The expected excess over the capacity -/

theorem sum_postedRamp_nonneg (weight sensitivity : NNReal) (threshold : ℝ)
    (b : ι → ℝ) : 0 ≤ ∑ j, postedRamp weight sensitivity threshold (b j) :=
  Finset.sum_nonneg fun _ _ => postedRamp_nonneg _ _ _ _

theorem sum_postedRamp_le (weight sensitivity : NNReal) (threshold : ℝ)
    (b : ι → ℝ) :
    (∑ j, postedRamp weight sensitivity threshold (b j))
      ≤ (Fintype.card ι : ℝ) * (weight : ℝ) := by
  calc (∑ j, postedRamp weight sensitivity threshold (b j))
      ≤ ∑ _j : ι, (weight : ℝ) :=
        Finset.sum_le_sum fun j _ => postedRamp_le _ _ _ _
    _ = (Fintype.card ι : ℝ) * (weight : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integrable_sum_postedRamp (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (threshold : ℝ) :
    Integrable (fun b : ι → ℝ => ∑ j, postedRamp weight sensitivity threshold (b j))
      (profileLaw (ι := ι) F) := by
  refine (integrable_const ((Fintype.card ι : ℝ) * (weight : ℝ))).mono'
    (measurable_sum_postedRamp weight sensitivity threshold).aestronglyMeasurable ?_
  filter_upwards with b
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sum_postedRamp_nonneg weight sensitivity threshold b)]
  exact sum_postedRamp_le weight sensitivity threshold b

/-- The expected excess of the total posted response over the capacity is at
most `w₁ √n / 4`: the general-law analogue of
`finite_expected_excess_le_quarter_sqrt`. -/
theorem integral_excess_le_quarter_sqrt (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (threshold capacity : ℝ)
    (hClears : (Fintype.card ι : ℝ)
      * curveMass F (postedRamp weight sensitivity threshold) = capacity) :
    ∫ b, max ((∑ j, postedRamp weight sensitivity threshold (b j)) - capacity) 0
        ∂profileLaw (ι := ι) F
      ≤ (weight : ℝ) * Real.sqrt (Fintype.card ι) / 4 := by
  classical
  have hSumInt := integrable_sum_postedRamp (ι := ι) F weight sensitivity threshold
  have hY : Integrable
      (fun b : ι → ℝ =>
        (∑ j, postedRamp weight sensitivity threshold (b j)) - capacity)
      (profileLaw (ι := ι) F) := hSumInt.sub (integrable_const capacity)
  have hSumMeas := measurable_sum_postedRamp (ι := ι) weight sensitivity threshold
  have hbound : ∀ b : ι → ℝ,
      |(∑ j, postedRamp weight sensitivity threshold (b j)) - capacity|
        ≤ (Fintype.card ι : ℝ) * (weight : ℝ) + |capacity| := by
    intro b
    have h1 := sum_postedRamp_nonneg (ι := ι) weight sensitivity threshold b
    have h2 := sum_postedRamp_le (ι := ι) weight sensitivity threshold b
    have h3 : -|capacity| ≤ capacity := neg_abs_le capacity
    have h4 : capacity ≤ |capacity| := le_abs_self capacity
    rw [abs_le]
    constructor <;> linarith
  have hY2 : Integrable
      (fun b : ι → ℝ =>
        ((∑ j, postedRamp weight sensitivity threshold (b j)) - capacity) ^ 2)
      (profileLaw (ι := ι) F) := by
    refine (integrable_const
      (((Fintype.card ι : ℝ) * (weight : ℝ) + |capacity|) ^ 2)).mono'
      (((hSumMeas.sub measurable_const).pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound b) 2
  have hCenter : ∫ b,
      ((∑ j, postedRamp weight sensitivity threshold (b j)) - capacity)
        ∂profileLaw (ι := ι) F = 0 := by
    rw [integral_sub hSumInt (integrable_const capacity), integral_const,
      probReal_univ, integral_sum_postedRamp F weight sensitivity threshold,
      hClears]
    simp
  have hhalf := integral_positivePart_eq_half_abs
    (μ := profileLaw (ι := ι) F) hY hCenter
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (Fintype.card ι) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsq : ∫ b,
      ((∑ j, postedRamp weight sensitivity threshold (b j)) - capacity) ^ 2
        ∂profileLaw (ι := ι) F
      ≤ ((weight : ℝ) * Real.sqrt (Fintype.card ι) / 2) ^ 2 := by
    have h := integral_sq_sub_total_le (ι := ι) F weight sensitivity threshold
    rw [hClears] at h
    refine h.trans (le_of_eq ?_)
    rw [div_pow, mul_pow, hsqrtSq]
    ring
  have habs := integral_abs_le_of_integral_sq_le
    (μ := profileLaw (ι := ι) F) hY hY2
    (bound := (weight : ℝ) * Real.sqrt (Fintype.card ι) / 2)
    (by positivity) hsq
  rw [hhalf]
  linarith

/-! ### Achievability at a general value law -/

/-- **Theorem `thm:meanfield` (iii), achievability, at a general value law.**
With values i.i.d. from `F` and the threshold calibrated so that the expected
total posted response equals the capacity `w₁ K`, the rationed-ramp rule loses
at most `b̄ w₁ / (4 √n)` per capita against the population-programme value of
the calibrated ramp. -/
theorem rationedRampMap_achievability [Nonempty ι] [DecidableEq ι]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (slots threshold upperValue : ℝ)
    (hSlots : 0 ≤ slots) (hUpper : 0 ≤ upperValue)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hValueLe : ∀ᵐ v ∂F, v ≤ upperValue)
    (hClears : (Fintype.card ι : ℝ)
        * curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots) :
    curveWelfare F (postedRamp weight sensitivity threshold)
        - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
      ≤ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold) := by
  classical
  have hCapacity : (0 : ℝ) ≤ (weight : ℝ) * slots :=
    mul_nonneg weight.coe_nonneg hSlots
  have hCert := rationedRampMap_certifiedRule (ι := ι) weight sensitivity
    (slots := slots) threshold hSlots
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsqrtPos : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.2 hnpos
  -- every coordinate is capped by `b̄` almost surely
  have hcoordAe : ∀ᵐ b ∂(profileLaw (ι := ι) F), ∀ i : ι, b i ≤ upperValue := by
    rw [ae_all_iff]
    intro i
    have hqmp := (measurePreserving_eval (fun _ : ι => F) i).quasiMeasurePreserving
    have := hqmp.ae hValueLe
    exact this
  -- pointwise rationing loss
  have hpoint : ∀ᵐ b ∂(profileLaw (ι := ι) F),
      (∑ i, b i * postedRamp weight sensitivity threshold (b i))
        - (∑ i, b i * rationedRampMap weight sensitivity
            ((weight : ℝ) * slots) threshold b i)
      ≤ upperValue * max ((∑ j, postedRamp weight sensitivity threshold (b j))
            - (weight : ℝ) * slots) 0 := by
    filter_upwards [hcoordAe] with b hb
    exact rationedResponse_welfare_loss_le ((weight : ℝ) * slots) upperValue
      (fun i => b i) (fun j => postedRamp weight sensitivity threshold (b j))
      hCapacity hUpper hb (fun j => postedRamp_nonneg _ _ _ _)
  -- integrability of the three integrands
  have hRampInt : Integrable
      (fun b : ι → ℝ =>
        ∑ i, b i * postedRamp weight sensitivity threshold (b i))
      (profileLaw (ι := ι) F) := by
    refine integrable_finsetSum _ fun i _ => ?_
    exact integrable_coord_comp F i
      ((postedRamp_curveShape weight sensitivity threshold).integrable_value_mul
        F hFirstMoment)
  have hcoordValue : ∀ i : ι, Integrable (fun b : ι → ℝ => b i)
      (profileLaw (ι := ι) F) := fun i => integrable_coord_comp F i hFirstMoment
  have hRuleInt : Integrable
      (fun b : ι → ℝ =>
        ∑ i, b i * rationedRampMap weight sensitivity
          ((weight : ℝ) * slots) threshold b i)
      (profileLaw (ι := ι) F) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hb : Integrable (fun b : ι → ℝ => |b i| * (weight : ℝ))
        (profileLaw (ι := ι) F) := (hcoordValue i).abs.mul_const _
    refine hb.mono' (((measurable_pi_apply i).mul
      (hCert.measurable i)).aestronglyMeasurable) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (hCert.nonneg b i)]
    exact hCert.le_weight b i
  have hExcessInt : Integrable
      (fun b : ι → ℝ => upperValue
        * max ((∑ j, postedRamp weight sensitivity threshold (b j))
            - (weight : ℝ) * slots) 0)
      (profileLaw (ι := ι) F) := by
    have hmeas : Measurable fun b : ι → ℝ =>
        max ((∑ j, postedRamp weight sensitivity threshold (b j))
          - (weight : ℝ) * slots) 0 :=
      ((measurable_sum_postedRamp weight sensitivity threshold).sub
        measurable_const).max measurable_const
    have hb : Integrable (fun b : ι → ℝ =>
        max ((∑ j, postedRamp weight sensitivity threshold (b j))
          - (weight : ℝ) * slots) 0) (profileLaw (ι := ι) F) := by
      refine (integrable_const ((Fintype.card ι : ℝ) * (weight : ℝ)
        + |(weight : ℝ) * slots|)).mono' hmeas.aestronglyMeasurable ?_
      filter_upwards with b
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have h1 := sum_postedRamp_le (ι := ι) weight sensitivity threshold b
      have h2 : -((weight : ℝ) * slots) ≤ |(weight : ℝ) * slots| := neg_le_abs _
      have h3 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * (weight : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) weight.coe_nonneg
      have h4 : (0 : ℝ) ≤ |(weight : ℝ) * slots| := abs_nonneg _
      exact max_le (by linarith) (by linarith)
    exact hb.const_mul upperValue
  -- integrate the pointwise bound
  have hint : (∫ b, ((∑ i, b i * postedRamp weight sensitivity threshold (b i))
        - (∑ i, b i * rationedRampMap weight sensitivity
            ((weight : ℝ) * slots) threshold b i)) ∂profileLaw (ι := ι) F)
      ≤ upperValue * ((weight : ℝ) * Real.sqrt (Fintype.card ι) / 4) := by
    calc (∫ b, ((∑ i, b i * postedRamp weight sensitivity threshold (b i))
          - (∑ i, b i * rationedRampMap weight sensitivity
              ((weight : ℝ) * slots) threshold b i)) ∂profileLaw (ι := ι) F)
        ≤ ∫ b, upperValue
            * max ((∑ j, postedRamp weight sensitivity threshold (b j))
                - (weight : ℝ) * slots) 0 ∂profileLaw (ι := ι) F :=
          integral_mono_ae (hRampInt.sub hRuleInt) hExcessInt hpoint
      _ = upperValue * ∫ b,
            max ((∑ j, postedRamp weight sensitivity threshold (b j))
              - (weight : ℝ) * slots) 0 ∂profileLaw (ι := ι) F :=
          integral_const_mul _ _
      _ ≤ upperValue * ((weight : ℝ) * Real.sqrt (Fintype.card ι) / 4) :=
          mul_le_mul_of_nonneg_left
            (integral_excess_le_quarter_sqrt (ι := ι) F weight sensitivity
              threshold ((weight : ℝ) * slots) hClears) hUpper
  rw [integral_sub hRampInt hRuleInt,
    integral_sum_value_postedRamp F hFirstMoment weight sensitivity threshold] at hint
  -- the rule's side is `n` times per-capita value
  have hPC := perCapitaValue_eq_expectedWelfare F hFirstMoment hCert
  have hRule : (∫ b, ∑ i, b i * rationedRampMap weight sensitivity
        ((weight : ℝ) * slots) threshold b i ∂profileLaw (ι := ι) F)
      = (Fintype.card ι : ℝ)
        * perCapitaValue (ι := ι) F
            (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold) := by
    rw [hPC]
    field_simp
  rw [hRule] at hint
  -- divide by `n`
  have hdiv : curveWelfare F (postedRamp weight sensitivity threshold)
      - perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold)
      ≤ upperValue * ((weight : ℝ) * Real.sqrt (Fintype.card ι) / 4)
        / (Fintype.card ι : ℝ) := by
    rw [le_div_iff₀ hnpos]
    nlinarith [hint]
  have hrate : upperValue * ((weight : ℝ) * Real.sqrt (Fintype.card ι) / 4)
        / (Fintype.card ι : ℝ)
      = upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι)) := by
    field_simp
    rw [Real.sq_sqrt hnpos.le]
  rw [hrate] at hdiv
  linarith

/-- Achievability under the paper's own support assumption: values live in
`[r, b̄]`, which supplies the finite first moment and the value cap. -/
theorem rationedRampMap_achievability_of_bounded_support [Nonempty ι]
    [DecidableEq ι] (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (slots threshold reserve upperValue : ℝ)
    (hSlots : 0 ≤ slots) (hUpper : 0 ≤ upperValue)
    (hSupport : ∀ᵐ v ∂F, v ∈ Set.Icc reserve upperValue)
    (hClears : (Fintype.card ι : ℝ)
        * curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots) :
    curveWelfare F (postedRamp weight sensitivity threshold)
        - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
      ≤ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold) := by
  have hFirstMoment : Integrable (fun v : ℝ => v) F :=
    memLp_one_iff_integrable.mp
      (memLp_of_bounded hSupport measurable_id.aestronglyMeasurable 1)
  exact rationedRampMap_achievability F weight sensitivity slots threshold
    upperValue hSlots hUpper hFirstMoment (hSupport.mono fun v hv => hv.2) hClears

/-- **The frontier at a general value law.**  Per-capita welfare of the
rationed-ramp rule is squeezed between the population-programme value of the
calibrated ramp and that value minus `b̄ w₁ / (4 √n)`.  The upper half is part
(i) (`certifiedRule_le_postedRamp`), the lower half is
`rationedRampMap_achievability`; both are stated against the same benchmark. -/
theorem rationedRampMap_frontier_sandwich [Nonempty ι] [DecidableEq ι]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hSensitivity : 0 < sensitivity)
    (slots threshold upperValue : ℝ)
    (hSlots : 0 ≤ slots) (hUpper : 0 ≤ upperValue) (hThreshold : 0 ≤ threshold)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hValueLe : ∀ᵐ v ∂F, v ≤ upperValue)
    (hClears : (Fintype.card ι : ℝ)
        * curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots) :
    curveWelfare F (postedRamp weight sensitivity threshold)
        - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
      ≤ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold)
    ∧ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold)
      ≤ curveWelfare F (postedRamp weight sensitivity threshold) := by
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hshape := postedRamp_curveShape weight sensitivity threshold
  have hmassLe : curveMass F (postedRamp weight sensitivity threshold)
      ≤ (weight : ℝ) := by
    have hmono := integral_mono (hshape.integrable F)
      (integrable_const (weight : ℝ)) hshape.le_weight
    simpa [curveMass] using hmono
  have hmassEq : curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots / (Fintype.card ι : ℝ) := by
    rw [eq_div_iff (ne_of_gt hnpos), mul_comm]
    exact hClears
  have hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min ((weight : ℝ) * slots / (Fintype.card ι : ℝ)) (weight : ℝ) := by
    rw [min_eq_left (hmassEq ▸ hmassLe), hmassEq]
  refine ⟨rationedRampMap_achievability F weight sensitivity slots threshold
    upperValue hSlots hUpper hFirstMoment hValueLe hClears, ?_⟩
  exact certifiedRule_le_postedRamp F weight sensitivity hSensitivity slots
    threshold hFirstMoment hThreshold hRampMass
    (rationedRampMap_certifiedRule (ι := ι) weight sensitivity
      (slots := slots) threshold hSlots)

/-! ### The benchmark is the population-programme value -/

/-- The value of the calibrated ramp *is* the population-programme value
`V*(massCap)`: the supremum defining `populationValue` is attained at the ramp.
This is what makes the benchmark of part (iii) the same object as the bound of
part (i) rather than a restatement of it. -/
theorem curveWelfare_postedRamp_eq_populationValue
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hSensitivity : 0 < sensitivity)
    (massCap threshold : ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hThreshold : 0 ≤ threshold)
    (hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min massCap (weight : ℝ)) :
    curveWelfare F (postedRamp weight sensitivity threshold)
      = populationValue F weight sensitivity massCap := by
  have hfeas : CurveFeasible F weight sensitivity massCap
      (postedRamp weight sensitivity threshold) :=
    { toCurveShape := postedRamp_curveShape weight sensitivity threshold
      mass_le := by rw [hRampMass]; exact min_le_left _ _ }
  refine le_antisymm ?_ ?_
  · exact le_csSup
      (populationValues_bddAbove F hFirstMoment weight sensitivity massCap)
      ⟨postedRamp weight sensitivity threshold, hfeas, rfl⟩
  · refine csSup_le ⟨curveWelfare F (postedRamp weight sensitivity threshold),
      ⟨postedRamp weight sensitivity threshold, hfeas, rfl⟩⟩ ?_
    rintro z ⟨ξ, hξ, rfl⟩
    exact postedRamp_solves_population_program F weight sensitivity hSensitivity
      massCap threshold hFirstMoment hThreshold hRampMass hξ

/-- **Theorem `thm:meanfield` at a general value law.**  Per-capita welfare of
the rationed-ramp rule is sandwiched between `V*(W̄_n)` and
`V*(W̄_n) - b̄ w₁ / (4 √n)`, with `V*` the population-programme value at
per-capita priority mass `W̄_n = w₁ K / n` -- the same `V*` that bounds every
certified rule from above in part (i). -/
theorem rationedRampMap_frontier_populationValue [Nonempty ι] [DecidableEq ι]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hSensitivity : 0 < sensitivity)
    (slots threshold upperValue : ℝ)
    (hSlots : 0 ≤ slots) (hUpper : 0 ≤ upperValue) (hThreshold : 0 ≤ threshold)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hValueLe : ∀ᵐ v ∂F, v ≤ upperValue)
    (hClears : (Fintype.card ι : ℝ)
        * curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots) :
    populationValue F weight sensitivity
          ((weight : ℝ) * slots / (Fintype.card ι : ℝ))
        - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
      ≤ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold)
    ∧ perCapitaValue (ι := ι) F
          (rationedRampMap weight sensitivity ((weight : ℝ) * slots) threshold)
      ≤ populationValue F weight sensitivity
          ((weight : ℝ) * slots / (Fintype.card ι : ℝ)) := by
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hshape := postedRamp_curveShape weight sensitivity threshold
  have hmassLe : curveMass F (postedRamp weight sensitivity threshold)
      ≤ (weight : ℝ) := by
    have hmono := integral_mono (hshape.integrable F)
      (integrable_const (weight : ℝ)) hshape.le_weight
    simpa [curveMass] using hmono
  have hmassEq : curveMass F (postedRamp weight sensitivity threshold)
      = (weight : ℝ) * slots / (Fintype.card ι : ℝ) := by
    rw [eq_div_iff (ne_of_gt hnpos), mul_comm]
    exact hClears
  have hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min ((weight : ℝ) * slots / (Fintype.card ι : ℝ)) (weight : ℝ) := by
    rw [min_eq_left (hmassEq ▸ hmassLe), hmassEq]
  rw [← curveWelfare_postedRamp_eq_populationValue F weight sensitivity
    hSensitivity ((weight : ℝ) * slots / (Fintype.card ι : ℝ)) threshold
    hFirstMoment hThreshold hRampMass]
  exact rationedRampMap_frontier_sandwich F weight sensitivity hSensitivity
    slots threshold upperValue hSlots hUpper hThreshold hFirstMoment hValueLe
    hClears

/-! ### The hypotheses are jointly satisfiable -/

/-- A witness that `rationedRampMap_frontier_populationValue` is not vacuous:
one agent, the Dirac law at `1`, unit weight and sensitivity, half a slot,
threshold `1/2` and value cap `1` satisfy every hypothesis at once. -/
example :
    populationValue (Measure.dirac (1 : ℝ)) 1 1
          (((1 : NNReal) : ℝ) * (1 / 2) / (Fintype.card (Fin 1) : ℝ))
        - 1 * ((1 : NNReal) : ℝ) / (4 * Real.sqrt (Fintype.card (Fin 1)))
      ≤ perCapitaValue (ι := Fin 1) (Measure.dirac (1 : ℝ))
          (rationedRampMap 1 1 (((1 : NNReal) : ℝ) * (1 / 2)) (1 / 2))
    ∧ perCapitaValue (ι := Fin 1) (Measure.dirac (1 : ℝ))
          (rationedRampMap 1 1 (((1 : NNReal) : ℝ) * (1 / 2)) (1 / 2))
      ≤ populationValue (Measure.dirac (1 : ℝ)) 1 1
          (((1 : NNReal) : ℝ) * (1 / 2) / (Fintype.card (Fin 1) : ℝ)) := by
  refine rationedRampMap_frontier_populationValue (ι := Fin 1)
    (Measure.dirac (1 : ℝ)) 1 1 (by norm_num) (1 / 2) (1 / 2) 1 (by norm_num)
    (by norm_num) (by norm_num) (integrable_dirac (by simp)) (by simp) ?_
  have hmass : curveMass (Measure.dirac (1 : ℝ)) (postedRamp 1 1 (1 / 2))
      = 1 / 2 := by
    unfold curveMass
    rw [integral_dirac, postedRamp, clampWeight_eq_of_mem] <;> norm_num
  rw [hmass]
  norm_num

end

end SmoothingCliff.Frontier
