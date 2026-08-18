import SmoothingCliff.Frontier.WaterFilling
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Sqrt

/-!
# The finite-support large-market frontier

This file formalizes the self-contained core of Theorem `thm:meanfield` in
`Smoothing_the_Cliff_ITCS.tex`.  It proves the finite-support population
program, including the capped-linear optimizer, the exact reduction from a
family of interim curves to their population average, and the deterministic
and probabilistic inequalities behind the `O(n^{-1/2})` rationing term.

The paper's remaining bridges from a jointly measurable finite-agent rule to
these interim curves, and from inclusion probabilities to lotteries and
Myerson transfers, require measure/disintegration and assignment-decomposition
interfaces not yet present in this project.  They are deliberately not encoded
as assumptions of a theorem claiming the whole paper statement.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

/-- A probability law on a finite support. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  probability : α → ℝ
  probability_nonneg : ∀ a, 0 ≤ probability a
  probability_sum : ∑ a, probability a = 1

/-- Expectation under a finite law. -/
def finiteExpectation {α : Type*} [Fintype α]
    (law : FiniteLaw α) (f : α → ℝ) : ℝ :=
  ∑ a, law.probability a * f a

/-- Ex-ante allocation mass of a population curve. -/
def finiteCurveMass {α : Type*} [Fintype α]
    (law : FiniteLaw α) (ξ : α → ℝ) : ℝ :=
  finiteExpectation law ξ

/-- Ex-ante value-weighted allocation of a population curve. -/
def finiteCurveWelfare {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value ξ : α → ℝ) : ℝ :=
  finiteExpectation law (fun a => value a * ξ a)

/-- The pointwise and Lipschitz restrictions in the population program. -/
structure FiniteCurveShape {α : Type*} [Fintype α]
    (value : α → ℝ) (weight sensitivity : NNReal) (ξ : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ ξ a
  le_weight : ∀ a, ξ a ≤ weight
  lipschitz : ∀ a b,
    |ξ a - ξ b| ≤ (sensitivity : ℝ) * |value a - value b|

/-- Feasibility for the finite-support population program. -/
structure FiniteCurveFeasible {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap : ℝ) (ξ : α → ℝ) : Prop extends
    FiniteCurveShape value weight sensitivity ξ where
  mass_le : finiteCurveMass law ξ ≤ massCap

/-- Average of the agent-specific interim curves used in the finite-market
upper-bound reduction. -/
noncomputable def averageCurve {ι α : Type*} [Fintype ι] [Nonempty ι]
    [Fintype α] (x : ι → α → ℝ) (a : α) : ℝ :=
  (∑ i, x i a) / Fintype.card ι

theorem averageCurve_shape {ι α : Type*} [Fintype ι] [Nonempty ι]
    [Fintype α] (value : α → ℝ) (weight sensitivity : NNReal)
    (x : ι → α → ℝ)
    (hx : ∀ i, FiniteCurveShape value weight sensitivity (x i)) :
    FiniteCurveShape value weight sensitivity (averageCurve x) := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro a
    exact div_nonneg (Finset.sum_nonneg fun i _ => (hx i).nonneg a) hn.le
  · intro a
    apply (div_le_iff₀ hn).2
    calc
      (∑ i, x i a) ≤ ∑ _i : ι, (weight : ℝ) :=
        Finset.sum_le_sum fun i _ => (hx i).le_weight a
      _ = Fintype.card ι * (weight : ℝ) := by simp
      _ = (weight : ℝ) * Fintype.card ι := by ring
  · intro a b
    have hsum :
        |∑ i, (x i a - x i b)| ≤
          ∑ i, |x i a - x i b| :=
      Finset.abs_sum_le_sum_abs (fun i => x i a - x i b) Finset.univ
    have hterm :
        (∑ i, |x i a - x i b|) ≤
          ∑ _i : ι, (sensitivity : ℝ) * |value a - value b| :=
      Finset.sum_le_sum fun i _ => (hx i).lipschitz a b
    have hnum :
        |∑ i, (x i a - x i b)| ≤
          (Fintype.card ι : ℝ) *
            ((sensitivity : ℝ) * |value a - value b|) := by
      calc
        |∑ i, (x i a - x i b)| ≤
            ∑ i, |x i a - x i b| := hsum
        _ ≤ ∑ _i : ι, (sensitivity : ℝ) * |value a - value b| := hterm
        _ = (Fintype.card ι : ℝ) *
            ((sensitivity : ℝ) * |value a - value b|) := by simp
    rw [averageCurve, averageCurve]
    rw [div_sub_div_same, abs_div]
    rw [abs_of_pos hn]
    apply (div_le_iff₀ hn).2
    rw [mul_comm]
    simpa [Finset.sum_sub_distrib] using hnum

theorem averageCurve_mass {ι α : Type*} [Fintype ι] [Nonempty ι]
    [Fintype α] (law : FiniteLaw α) (x : ι → α → ℝ) :
    finiteCurveMass law (averageCurve x) =
      (∑ i, finiteCurveMass law (x i)) / Fintype.card ι := by
  unfold finiteCurveMass finiteExpectation averageCurve
  calc
    (∑ a, law.probability a * ((∑ i, x i a) / Fintype.card ι)) =
        (∑ a, law.probability a * ∑ i, x i a) / Fintype.card ι := by
          calc
            (∑ a, law.probability a *
                ((∑ i, x i a) / Fintype.card ι)) =
                ∑ a, (law.probability a * ∑ i, x i a) /
                  Fintype.card ι := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
            _ = (∑ a, law.probability a * ∑ i, x i a) /
                Fintype.card ι := by rw [Finset.sum_div]
    _ = (∑ i, ∑ a, law.probability a * x i a) / Fintype.card ι := by
      congr 1
      calc
        (∑ a, law.probability a * ∑ i, x i a) =
            ∑ a, ∑ i, law.probability a * x i a := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
        _ = ∑ i, ∑ a, law.probability a * x i a := Finset.sum_comm

theorem averageCurve_welfare {ι α : Type*} [Fintype ι] [Nonempty ι]
    [Fintype α] (law : FiniteLaw α) (value : α → ℝ)
    (x : ι → α → ℝ) :
    finiteCurveWelfare law value (averageCurve x) =
      (∑ i, finiteCurveWelfare law value (x i)) / Fintype.card ι := by
  unfold finiteCurveWelfare finiteExpectation averageCurve
  calc
    (∑ a, law.probability a * (value a *
        ((∑ i, x i a) / Fintype.card ι))) =
        (∑ a, law.probability a * (value a * ∑ i, x i a)) /
          Fintype.card ι := by
      calc
        (∑ a, law.probability a * (value a *
            ((∑ i, x i a) / Fintype.card ι))) =
            ∑ a, (law.probability a * (value a * ∑ i, x i a)) /
              Fintype.card ι := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a, law.probability a * (value a * ∑ i, x i a)) /
            Fintype.card ι := by rw [Finset.sum_div]
    _ = (∑ i, ∑ a, law.probability a * (value a * x i a)) /
        Fintype.card ι := by
      congr 1
      calc
        (∑ a, law.probability a * (value a * ∑ i, x i a)) =
            ∑ a, ∑ i, law.probability a * (value a * x i a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum, Finset.mul_sum]
        _ = ∑ i, ∑ a, law.probability a * (value a * x i a) := Finset.sum_comm

/-- The one-dimensional population-program value on a finite support. -/
noncomputable def finitePopulationValue {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ ξ : α → ℝ,
    FiniteCurveFeasible law value weight sensitivity massCap ξ ∧
      z = finiteCurveWelfare law value ξ}

theorem finitePopulationValues_bddAbove {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap upperValue : ℝ)
    (hValueLe : ∀ a, value a ≤ upperValue) (hUpper : 0 ≤ upperValue) :
    BddAbove {z : ℝ | ∃ ξ : α → ℝ,
      FiniteCurveFeasible law value weight sensitivity massCap ξ ∧
        z = finiteCurveWelfare law value ξ} := by
  refine ⟨upperValue * (weight : ℝ), ?_⟩
  rintro z ⟨ξ, hξ, rfl⟩
  unfold finiteCurveWelfare finiteExpectation
  calc
    (∑ a, law.probability a * (value a * ξ a)) ≤
        ∑ a, law.probability a * (upperValue * (weight : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (law.probability_nonneg a)
      have h₁ : 0 ≤ (upperValue - value a) * ξ a :=
        mul_nonneg (sub_nonneg.mpr (hValueLe a)) (hξ.nonneg a)
      have h₂ : 0 ≤ upperValue * ((weight : ℝ) - ξ a) :=
        mul_nonneg hUpper (sub_nonneg.mpr (hξ.le_weight a))
      nlinarith
    _ = upperValue * (weight : ℝ) := by
      rw [← Finset.sum_mul]
      rw [law.probability_sum]
      ring

/-- Exact finite-market upper-bound reduction after opponents have been
integrated out: averaging preserves the cap and mass feasibility, so average
welfare is bounded by the population program. -/
theorem finiteMarket_average_upper_bound
    {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap upperValue : ℝ) (x : ι → α → ℝ)
    (hValueLe : ∀ a, value a ≤ upperValue) (hUpper : 0 ≤ upperValue)
    (hx : ∀ i, FiniteCurveShape value weight sensitivity (x i))
    (hMass : ∑ i, finiteCurveMass law (x i) ≤
      Fintype.card ι * massCap) :
    (∑ i, finiteCurveWelfare law value (x i)) / Fintype.card ι ≤
      finitePopulationValue law value weight sensitivity massCap := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have havgMass : finiteCurveMass law (averageCurve x) ≤ massCap := by
    rw [averageCurve_mass]
    exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hMass)
  have havg : FiniteCurveFeasible law value weight sensitivity massCap
      (averageCurve x) :=
    ⟨averageCurve_shape value weight sensitivity x hx, havgMass⟩
  rw [← averageCurve_welfare law value x]
  exact le_csSup
    (finitePopulationValues_bddAbove law value weight sensitivity massCap
      upperValue hValueLe hUpper)
    ⟨averageCurve x, havg, rfl⟩

/-- The posted capped-linear allocation curve. -/
noncomputable def postedRamp (weight sensitivity : NNReal)
    (threshold value : ℝ) : ℝ :=
  clampWeight weight ((sensitivity : ℝ) * (value - threshold))

theorem postedRamp_nonneg (weight sensitivity : NNReal) (threshold value : ℝ) :
    0 ≤ postedRamp weight sensitivity threshold value :=
  clampWeight_nonneg weight _

theorem postedRamp_le (weight sensitivity : NNReal) (threshold value : ℝ) :
    postedRamp weight sensitivity threshold value ≤ weight :=
  clampWeight_le weight _

theorem postedRamp_lipschitz (weight sensitivity : NNReal) (threshold : ℝ) :
    LipschitzWith sensitivity (postedRamp weight sensitivity threshold) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  calc
    dist (postedRamp weight sensitivity threshold a)
        (postedRamp weight sensitivity threshold b) ≤
      dist ((sensitivity : ℝ) * (a - threshold))
        ((sensitivity : ℝ) * (b - threshold)) := by
          simpa only [NNReal.coe_one, one_mul, postedRamp] using
            (clampWeight_lipschitz weight).dist_le_mul
              ((sensitivity : ℝ) * (a - threshold))
              ((sensitivity : ℝ) * (b - threshold))
    _ = (sensitivity : ℝ) * dist a b := by
      rw [Real.dist_eq, Real.dist_eq]
      have h :
          (sensitivity : ℝ) * (a - threshold) -
              (sensitivity : ℝ) * (b - threshold) =
            (sensitivity : ℝ) * (a - b) := by ring
      rw [h, abs_mul, abs_of_nonneg sensitivity.coe_nonneg]

theorem postedRamp_shape {α : Type*} [Fintype α]
    (value : α → ℝ) (weight sensitivity : NNReal) (threshold : ℝ) :
    FiniteCurveShape value weight sensitivity
      (fun a => postedRamp weight sensitivity threshold (value a)) := by
  constructor
  · exact fun a => postedRamp_nonneg weight sensitivity threshold (value a)
  · exact fun a => postedRamp_le weight sensitivity threshold (value a)
  · intro a b
    simpa [Real.dist_eq] using
      (postedRamp_lipschitz weight sensitivity threshold).dist_le_mul
        (value a) (value b)

theorem postedRamp_antitone_threshold (weight sensitivity : NNReal)
    (value : ℝ) :
    Antitone (fun threshold => postedRamp weight sensitivity threshold value) := by
  intro s t hst
  apply clampWeight_monotone
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hst value)
    sensitivity.coe_nonneg

theorem finiteRampMass_continuous {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal) :
    Continuous (fun threshold => finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a))) := by
  unfold finiteCurveMass finiteExpectation
  apply continuous_finsetSum
  intro a ha
  apply continuous_const.mul
  unfold postedRamp
  apply (clampWeight_continuous weight).comp
  exact continuous_const.mul (continuous_const.sub continuous_id)

theorem finiteRampMass_antitone {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal) :
    Antitone (fun threshold => finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a))) := by
  intro s t hst
  unfold finiteCurveMass finiteExpectation
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left
    (postedRamp_antitone_threshold weight sensitivity (value a) hst)
    (law.probability_nonneg a)

theorem postedRamp_zero_of_value_le_threshold
    (weight sensitivity : NNReal) {threshold value : ℝ}
    (h : value ≤ threshold) :
    postedRamp weight sensitivity threshold value = 0 := by
  apply clampWeight_eq_zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos sensitivity.coe_nonneg
    (sub_nonpos.mpr h)

theorem finiteRampMass_eq_zero_at_upper {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    {upper : ℝ} (hUpper : ∀ a, value a ≤ upper) :
    finiteCurveMass law
      (fun a => postedRamp weight sensitivity upper (value a)) = 0 := by
  unfold finiteCurveMass finiteExpectation
  apply Finset.sum_eq_zero
  intro a ha
  change law.probability a *
    postedRamp weight sensitivity upper (value a) = 0
  rw [postedRamp_zero_of_value_le_threshold weight sensitivity (hUpper a), mul_zero]

/-- Every mass between zero and the mass of a posted ramp can be obtained by
moving its threshold weakly upward to a common upper endpoint. -/
theorem exists_postedRamp_of_smaller_mass {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    {threshold upper mass : ℝ} (hThreshold : threshold ≤ upper)
    (hUpper : ∀ a, value a ≤ upper) (hMassNonneg : 0 ≤ mass)
    (hMassLe : mass ≤ finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a))) :
    ∃ newThreshold ∈ Set.Icc threshold upper,
      finiteCurveMass law
        (fun a => postedRamp weight sensitivity newThreshold (value a)) = mass := by
  let f : ℝ → ℝ := fun t => finiteCurveMass law
    (fun a => postedRamp weight sensitivity t (value a))
  have hzero : f upper = 0 :=
    finiteRampMass_eq_zero_at_upper law value weight sensitivity hUpper
  have hmem : mass ∈ Set.Icc (f upper) (f threshold) := by
    simpa [hzero] using ⟨hMassNonneg, hMassLe⟩
  have himage := intermediate_value_Icc' hThreshold
    (finiteRampMass_continuous law value weight sensitivity).continuousOn hmem
  rcases himage with ⟨newThreshold, hnew, hEq⟩
  exact ⟨newThreshold, hnew, hEq⟩

/-- Below any point where the ramp is not capped, it falls at exactly the
published slope until it reaches zero. -/
theorem postedRamp_lower_formula (weight sensitivity : NNReal)
    (threshold : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hb : postedRamp weight sensitivity threshold b < weight) :
    postedRamp weight sensitivity threshold a =
      max 0 (postedRamp weight sensitivity threshold b -
        (sensitivity : ℝ) * (b - a)) := by
  have hrawb : (sensitivity : ℝ) * (b - threshold) < (weight : ℝ) := by
    by_contra hnot
    have hle : (weight : ℝ) ≤ (sensitivity : ℝ) * (b - threshold) :=
      le_of_not_gt hnot
    have heq := clampWeight_eq_weight_of_le weight hle
    exact (ne_of_lt hb) (by simpa [postedRamp] using heq)
  have hrawa : (sensitivity : ℝ) * (a - threshold) < (weight : ℝ) := by
    have hmono : (sensitivity : ℝ) * (a - threshold) ≤
        (sensitivity : ℝ) * (b - threshold) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hab threshold)
        sensitivity.coe_nonneg
    exact hmono.trans_lt hrawb
  simp only [postedRamp, clampWeight, Set.coe_projIcc]
  rw [min_eq_right hrawa.le, min_eq_right hrawb.le]
  have halg :
      (sensitivity : ℝ) * (a - threshold) =
        (sensitivity : ℝ) * (b - threshold) -
          (sensitivity : ℝ) * (b - a) := by ring
  rw [halg]
  by_cases hraw : (sensitivity : ℝ) * (b - threshold) ≤ 0
  · rw [max_eq_left hraw]
    have hsub :
        (sensitivity : ℝ) * (b - threshold) -
            (sensitivity : ℝ) * (b - a) ≤ 0 := by
      have hnonneg : 0 ≤ (sensitivity : ℝ) * (b - a) :=
        mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hab)
      linarith
    rw [max_eq_left hsub]
    have hnonneg : 0 ≤ (sensitivity : ℝ) * (b - a) :=
      mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hab)
    rw [max_eq_left (by linarith)]
  · rw [max_eq_right (le_of_not_ge hraw)]

/-- If an admissible curve exceeds the ramp at one value, then it weakly
exceeds the ramp at every lower value.  This is the single-crossing engine in
the paper's exchange proof. -/
theorem curve_ge_postedRamp_below_excess {α : Type*} [Fintype α]
    (value : α → ℝ) (weight sensitivity : NNReal) (threshold : ℝ)
    (ξ : α → ℝ) (hξ : FiniteCurveShape value weight sensitivity ξ)
    {a b : α} (hab : value a ≤ value b)
    (hb : postedRamp weight sensitivity threshold (value b) < ξ b) :
    postedRamp weight sensitivity threshold (value a) ≤ ξ a := by
  have hrampb : postedRamp weight sensitivity threshold (value b) < weight :=
    hb.trans_le (hξ.le_weight b)
  rw [postedRamp_lower_formula weight sensitivity threshold hab hrampb]
  apply max_le
  · exact hξ.nonneg a
  · have hlip := hξ.lipschitz a b
    rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hlip
    have habs : ξ b - ξ a ≤ |ξ a - ξ b| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith

/-- Equal-mass exchange: on a finite support, the posted ramp weakly maximizes
value-weighted allocation among all curves with the same mass. -/
theorem postedRamp_optimal_at_equal_mass {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (threshold : ℝ) (ξ : α → ℝ)
    (hValueNonneg : ∀ a, 0 ≤ value a)
    (hξ : FiniteCurveShape value weight sensitivity ξ)
    (hMass : finiteCurveMass law ξ = finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a))) :
    finiteCurveWelfare law value ξ ≤
      finiteCurveWelfare law value
        (fun a => postedRamp weight sensitivity threshold (value a)) := by
  classical
  let bad : Finset α := Finset.univ.filter fun a =>
    postedRamp weight sensitivity threshold (value a) < ξ a
  by_cases hbad : bad.Nonempty
  · obtain ⟨pivot, hpivot, hpivotMax⟩ :=
      Finset.exists_max_image bad value hbad
    have hpivotExcess :
        postedRamp weight sensitivity threshold (value pivot) < ξ pivot := by
      exact (Finset.mem_filter.mp hpivot).2
    have hpoint : ∀ a,
        0 ≤ law.probability a * (value a - value pivot) *
          (postedRamp weight sensitivity threshold (value a) - ξ a) := by
      intro a
      by_cases hlow : value a ≤ value pivot
      · have hcurve := curve_ge_postedRamp_below_excess value weight sensitivity
          threshold ξ hξ hlow hpivotExcess
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonneg_of_nonpos
            (law.probability_nonneg a) (sub_nonpos.mpr hlow))
          (sub_nonpos.mpr hcurve)
      · have hhigh : value pivot < value a := lt_of_not_ge hlow
        have hnotBad : a ∉ bad := by
          intro ha
          exact (not_le_of_gt hhigh) (hpivotMax a ha)
        have hcurve : ξ a ≤ postedRamp weight sensitivity threshold (value a) := by
          simpa [bad] using hnotBad
        exact mul_nonneg
          (mul_nonneg (law.probability_nonneg a) (sub_nonneg.mpr hhigh.le))
          (sub_nonneg.mpr hcurve)
    have hsum :
        0 ≤ ∑ a, law.probability a * (value a - value pivot) *
          (postedRamp weight sensitivity threshold (value a) - ξ a) :=
      Finset.sum_nonneg fun a _ => hpoint a
    have hmassZero :
        ∑ a, law.probability a *
          (postedRamp weight sensitivity threshold (value a) - ξ a) = 0 := by
      unfold finiteCurveMass finiteExpectation at hMass
      calc
        (∑ a, law.probability a *
            (postedRamp weight sensitivity threshold (value a) - ξ a)) =
            (∑ a, law.probability a *
              postedRamp weight sensitivity threshold (value a)) -
              ∑ a, law.probability a * ξ a := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro a ha
                ring
        _ = 0 := by linarith
    unfold finiteCurveWelfare finiteExpectation
    have hrewrite :
        (∑ a, law.probability a *
            (value a * postedRamp weight sensitivity threshold (value a))) -
          ∑ a, law.probability a * (value a * ξ a) =
        ∑ a, law.probability a * (value a - value pivot) *
          (postedRamp weight sensitivity threshold (value a) - ξ a) := by
      calc
        (∑ a, law.probability a *
            (value a * postedRamp weight sensitivity threshold (value a))) -
          ∑ a, law.probability a * (value a * ξ a) =
            ∑ a, law.probability a * value a *
              (postedRamp weight sensitivity threshold (value a) - ξ a) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro a ha
                ring
        _ = ∑ a, law.probability a * (value a - value pivot) *
              (postedRamp weight sensitivity threshold (value a) - ξ a) +
            value pivot * (∑ a, law.probability a *
              (postedRamp weight sensitivity threshold (value a) - ξ a)) := by
                rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro a ha
                ring
        _ = ∑ a, law.probability a * (value a - value pivot) *
              (postedRamp weight sensitivity threshold (value a) - ξ a) := by
                rw [hmassZero, mul_zero, add_zero]
    linarith
  · have hcurve : ∀ a, ξ a ≤
        postedRamp weight sensitivity threshold (value a) := by
      intro a
      have ha : a ∉ bad := fun ha => hbad ⟨a, ha⟩
      simpa [bad] using ha
    unfold finiteCurveWelfare finiteExpectation
    apply Finset.sum_le_sum
    intro a ha
    apply mul_le_mul_of_nonneg_left _ (law.probability_nonneg a)
    exact mul_le_mul_of_nonneg_left (hcurve a) (hValueNonneg a)

/-- Finite-support version of the population-program optimizer.  A ramp whose
mass equals the cap dominates every feasible curve. -/
theorem postedRamp_solves_finite_population_program
    {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap threshold upper : ℝ)
    (hValueNonneg : ∀ a, 0 ≤ value a)
    (hUpper : ∀ a, value a ≤ upper) (hThreshold : threshold ≤ upper)
    (hRampMass : finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a)) = massCap)
    (ξ : α → ℝ)
    (hξ : FiniteCurveFeasible law value weight sensitivity massCap ξ) :
    finiteCurveWelfare law value ξ ≤
      finiteCurveWelfare law value
        (fun a => postedRamp weight sensitivity threshold (value a)) := by
  have hMassNonneg : 0 ≤ finiteCurveMass law ξ := by
    unfold finiteCurveMass finiteExpectation
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (law.probability_nonneg a) (hξ.nonneg a)
  have hMassLe : finiteCurveMass law ξ ≤ finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a)) := by
    rw [hRampMass]
    exact hξ.mass_le
  obtain ⟨newThreshold, hnew, hnewMass⟩ :=
    exists_postedRamp_of_smaller_mass law value weight sensitivity hThreshold
      hUpper hMassNonneg hMassLe
  have hequal := postedRamp_optimal_at_equal_mass law value weight sensitivity
    newThreshold ξ hValueNonneg hξ.toFiniteCurveShape hnewMass.symm
  calc
    finiteCurveWelfare law value ξ ≤
        finiteCurveWelfare law value
          (fun a => postedRamp weight sensitivity newThreshold (value a)) := hequal
    _ ≤ finiteCurveWelfare law value
          (fun a => postedRamp weight sensitivity threshold (value a)) := by
      unfold finiteCurveWelfare finiteExpectation
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (law.probability_nonneg a)
      apply mul_le_mul_of_nonneg_left _ (hValueNonneg a)
      exact postedRamp_antitone_threshold weight sensitivity (value a) hnew.1

/-- Convenient statement that the ramp actually attains the `sSup` defining
the finite population program. -/
theorem finitePopulationValue_eq_postedRamp
    {α : Type*} [Fintype α]
    (law : FiniteLaw α) (value : α → ℝ) (weight sensitivity : NNReal)
    (massCap threshold upperValue : ℝ)
    (hValueNonneg : ∀ a, 0 ≤ value a)
    (hValueLe : ∀ a, value a ≤ upperValue) (hUpper : 0 ≤ upperValue)
    (hThreshold : threshold ≤ upperValue)
    (hRampMass : finiteCurveMass law
      (fun a => postedRamp weight sensitivity threshold (value a)) = massCap) :
    finitePopulationValue law value weight sensitivity massCap =
      finiteCurveWelfare law value
        (fun a => postedRamp weight sensitivity threshold (value a)) := by
  let ramp : α → ℝ :=
    fun a => postedRamp weight sensitivity threshold (value a)
  have hramp : FiniteCurveFeasible law value weight sensitivity massCap ramp := by
    refine ⟨postedRamp_shape value weight sensitivity threshold, ?_⟩
    simpa [ramp] using hRampMass.le
  apply le_antisymm
  · apply csSup_le
    · exact ⟨finiteCurveWelfare law value ramp, ramp, hramp, rfl⟩
    · rintro z ⟨ξ, hξ, rfl⟩
      simpa [ramp] using postedRamp_solves_finite_population_program law value
        weight sensitivity massCap threshold upperValue hValueNonneg hValueLe
        hThreshold hRampMass ξ hξ
  · exact le_csSup
      (finitePopulationValues_bddAbove law value weight sensitivity massCap
        upperValue hValueLe hUpper)
      ⟨ramp, hramp, rfl⟩

/-- Ration an unconstrained response vector to a common capacity.  This is the
paper's multiplier formula with its zero-denominator convention written as an
equivalent branch. -/
noncomputable def rationedResponse {ι : Type*} [Fintype ι]
    (capacity : ℝ) (response : ι → ℝ) (i : ι) : ℝ :=
  if (∑ j, response j) ≤ capacity then response i
  else capacity * response i / ∑ j, response j

theorem rationedResponse_nonneg {ι : Type*} [Fintype ι]
    (capacity : ℝ) (response : ι → ℝ)
    (hCapacity : 0 ≤ capacity) (hResponse : ∀ i, 0 ≤ response i) (i : ι) :
    0 ≤ rationedResponse capacity response i := by
  unfold rationedResponse
  split_ifs with h
  · exact hResponse i
  · have htotal : 0 < ∑ j, response j := by
      exact hCapacity.trans_lt (lt_of_not_ge h)
    exact div_nonneg (mul_nonneg hCapacity (hResponse i)) htotal.le

theorem rationedResponse_total_le {ι : Type*} [Fintype ι]
    (capacity : ℝ) (response : ι → ℝ)
    (hCapacity : 0 ≤ capacity) :
    ∑ i, rationedResponse capacity response i ≤ capacity := by
  unfold rationedResponse
  split_ifs with h
  · exact h
  · have htotal : 0 < ∑ i, response i := by
      have := lt_of_not_ge h
      exact hCapacity.trans_lt this
    calc
      (∑ i, capacity * response i / ∑ j, response j) = capacity := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        field_simp
      _ ≤ capacity := le_rfl

/-- Statewise welfare loss from rationing is at most the value cap times the
excess un-rationed mass. -/
theorem rationedResponse_welfare_loss_le {ι : Type*} [Fintype ι]
    (capacity upperValue : ℝ) (value response : ι → ℝ)
    (hCapacity : 0 ≤ capacity) (hUpper : 0 ≤ upperValue)
    (hValueLe : ∀ i, value i ≤ upperValue)
    (hResponse : ∀ i, 0 ≤ response i) :
    (∑ i, value i * response i) -
        ∑ i, value i * rationedResponse capacity response i ≤
      upperValue * max ((∑ i, response i) - capacity) 0 := by
  let total : ℝ := ∑ i, response i
  have hTotalNonneg : 0 ≤ total :=
    Finset.sum_nonneg fun i _ => hResponse i
  by_cases hle : total ≤ capacity
  · have hresp : ∀ i, rationedResponse capacity response i = response i := by
      intro i
      simp [rationedResponse, total, hle]
    simp_rw [hresp]
    rw [sub_self]
    exact mul_nonneg hUpper (le_max_right _ _)
  · have hlt : capacity < total := lt_of_not_ge hle
    have hTotalPos : 0 < total := hCapacity.trans_lt hlt
    have hraw : (∑ i, value i * response i) ≤ upperValue * total := by
      calc
        (∑ i, value i * response i) ≤
            ∑ i, upperValue * response i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hValueLe i) (hResponse i)
        _ = upperValue * total := by rw [Finset.mul_sum]
    have hfactor : 0 ≤ 1 - capacity / total := by
      rw [sub_nonneg]
      exact (div_le_one hTotalPos).2 hlt.le
    have hscaled :
        (1 - capacity / total) * (∑ i, value i * response i) ≤
          (1 - capacity / total) * (upperValue * total) :=
      mul_le_mul_of_nonneg_left hraw hfactor
    have hratio : ∀ i,
        rationedResponse capacity response i =
          capacity * response i / total := by
      intro i
      simp [rationedResponse, total, hle]
    simp_rw [hratio]
    have hsum :
        (∑ i, value i * (capacity * response i / total)) =
          (capacity / total) * ∑ i, value i * response i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    rw [hsum]
    rw [max_eq_left (sub_nonneg.mpr hlt.le)]
    have halg :
        (1 - capacity / total) * (upperValue * total) =
          upperValue * (total - capacity) := by
      field_simp
    rw [halg] at hscaled
    nlinarith

theorem positivePart_eq_half_abs_add (x : ℝ) :
    max x 0 = (|x| + x) / 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', abs_of_nonpos hx']
    ring

/-- A centered random variable has expected positive part equal to half its
mean absolute deviation. -/
theorem finite_expected_positivePart_eq_half_abs
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (random : Ω → ℝ) (center : ℝ)
    (hCenter : finiteExpectation law random = center) :
    finiteExpectation law (fun ω => max (random ω - center) 0) =
      finiteExpectation law (fun ω => |random ω - center|) / 2 := by
  unfold finiteExpectation at hCenter ⊢
  simp_rw [positivePart_eq_half_abs_add]
  calc
    (∑ a, law.probability a *
        ((|random a - center| + (random a - center)) / 2)) =
        (∑ a, law.probability a *
          (|random a - center| + (random a - center))) / 2 := by
      calc
        (∑ a, law.probability a *
            ((|random a - center| + (random a - center)) / 2)) =
            ∑ a, (law.probability a *
              (|random a - center| + (random a - center))) / 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a, law.probability a *
            (|random a - center| + (random a - center))) / 2 :=
          by rw [Finset.sum_div]
    _ = ((∑ a, law.probability a * |random a - center|) +
          (∑ a, law.probability a * (random a - center))) / 2 := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a, law.probability a * |random a - center|) / 2 := by
      have hzero : ∑ a, law.probability a * (random a - center) = 0 := by
        calc
          (∑ a, law.probability a * (random a - center)) =
              (∑ a, law.probability a * random a) -
                center * ∑ a, law.probability a := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = 0 := by rw [law.probability_sum, hCenter]; ring
      rw [hzero, add_zero]

/-- Weighted Cauchy--Schwarz turns a second-moment certificate into a bound on
mean absolute deviation. -/
theorem finite_expected_abs_le_of_secondMoment
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (random : Ω → ℝ) (bound : ℝ) (hBound : 0 ≤ bound)
    (hSecond : finiteExpectation law (fun ω => random ω ^ 2) ≤ bound ^ 2) :
    finiteExpectation law (fun ω => |random ω|) ≤ bound := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset Ω))
    (r := fun ω => law.probability ω * |random ω|)
    (f := fun ω => law.probability ω)
    (g := fun ω => law.probability ω * random ω ^ 2)
    (fun ω _ => law.probability_nonneg ω)
    (fun ω _ => mul_nonneg (law.probability_nonneg ω) (sq_nonneg _))
    (by
      intro ω hω
      apply le_of_eq
      change (law.probability ω * |random ω|) ^ 2 =
        law.probability ω * (law.probability ω * random ω ^ 2)
      rw [mul_pow, sq_abs]
      ring)
  unfold finiteExpectation at hSecond ⊢
  rw [law.probability_sum, one_mul] at hcs
  have hnonneg : 0 ≤ ∑ ω, law.probability ω * |random ω| :=
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (law.probability_nonneg ω) (abs_nonneg _)
  nlinarith

/-- The exact `w₁ sqrt(n) / 4` bound used in the paper, isolated from the
i.i.d. variance calculation. -/
theorem finite_expected_excess_le_quarter_sqrt
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (total : Ω → ℝ) (center weight : ℝ) (n : ℕ)
    (hWeight : 0 ≤ weight)
    (hCenter : finiteExpectation law total = center)
    (hSecond : finiteExpectation law (fun ω => (total ω - center) ^ 2) ≤
      (n : ℝ) * weight ^ 2 / 4) :
    finiteExpectation law (fun ω => max (total ω - center) 0) ≤
      weight * Real.sqrt n / 4 := by
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hmad := finite_expected_abs_le_of_secondMoment law
    (fun ω => total ω - center) (weight * Real.sqrt n / 2)
    (by positivity) (by
      apply hSecond.trans_eq
      rw [div_pow]
      norm_num
      rw [mul_pow, hsqrtSq]
      ring)
  rw [finite_expected_positivePart_eq_half_abs law total center hCenter]
  linarith

/-- Finite-law version of the paper's per-capita `n^{-1/2}` rationing error.
The moment premise is subsequently discharged by independence and the
`[0,w₁]` variance bound in a product-measure layer. -/
theorem finite_rationing_perCapita_rate
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (law : FiniteLaw Ω) (value response : Ω → ι → ℝ)
    (capacity upperValue weight : ℝ) (n : ℕ)
    (hn : 0 < n) (hCapacity : 0 ≤ capacity)
    (hUpper : 0 ≤ upperValue) (hWeight : 0 ≤ weight)
    (hValueLe : ∀ ω i, value ω i ≤ upperValue)
    (hResponse : ∀ ω i, 0 ≤ response ω i)
    (hCenter : finiteExpectation law (fun ω => ∑ i, response ω i) = capacity)
    (hSecond : finiteExpectation law
      (fun ω => ((∑ i, response ω i) - capacity) ^ 2) ≤
        (n : ℝ) * weight ^ 2 / 4) :
    finiteExpectation law (fun ω =>
        (∑ i, value ω i * response ω i) -
          ∑ i, value ω i * rationedResponse capacity (response ω) i) /
        (n : ℝ) ≤
      upperValue * weight / (4 * Real.sqrt n) := by
  have hstate : ∀ ω,
      (∑ i, value ω i * response ω i) -
          ∑ i, value ω i * rationedResponse capacity (response ω) i ≤
        upperValue * max ((∑ i, response ω i) - capacity) 0 := by
    intro ω
    exact rationedResponse_welfare_loss_le capacity upperValue (value ω)
      (response ω) hCapacity hUpper (hValueLe ω)
      (hResponse ω)
  have hexcess := finite_expected_excess_le_quarter_sqrt law
    (fun ω => ∑ i, response ω i) capacity weight n hWeight hCenter hSecond
  have htotal : finiteExpectation law (fun ω =>
      (∑ i, value ω i * response ω i) -
        ∑ i, value ω i * rationedResponse capacity (response ω) i) ≤
      upperValue * (weight * Real.sqrt n / 4) := by
    unfold finiteExpectation
    calc
      (∑ ω, law.probability ω *
          ((∑ i, value ω i * response ω i) -
            ∑ i, value ω i * rationedResponse capacity (response ω) i)) ≤
          ∑ ω, law.probability ω *
            (upperValue * max ((∑ i, response ω i) - capacity) 0) := by
        apply Finset.sum_le_sum
        intro ω hω
        exact mul_le_mul_of_nonneg_left (hstate ω)
          (law.probability_nonneg ω)
      _ = upperValue * finiteExpectation law
          (fun ω => max ((∑ i, response ω i) - capacity) 0) := by
        unfold finiteExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ ≤ upperValue * (weight * Real.sqrt n / 4) :=
        mul_le_mul_of_nonneg_left hexcess hUpper
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  calc
    finiteExpectation law (fun ω =>
        (∑ i, value ω i * response ω i) -
          ∑ i, value ω i * rationedResponse capacity (response ω) i) /
        (n : ℝ) ≤
        (upperValue * (weight * Real.sqrt n / 4)) / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnReal).2 htotal
    _ = upperValue * weight / (4 * Real.sqrt n) := by
      field_simp
      rw [Real.sq_sqrt hnReal.le]

end SmoothingCliff.Frontier
