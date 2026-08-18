import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# The analytic core of the optimal-cap certificate

This file formalizes the finite-dimensional objective in Proposition
`prop:optcert` of *Smoothing the Cliff*.  It deliberately does not assert the
economic claim that the expression below bounds every rationalizable outcome;
that claim also needs the mechanism-specific spread and dominance arguments.

For agent `i`, `premium i` is `v_i - r`, `entryCost i` is `χ_i`, and
`capacity i` is `γ_i`.  The definitions below are the paper's formulas

`a_i^S = γ_i ((v_i-r)S-χ_i)^+` and
`R(S) = ∑ᵢ [c_i(a_i^S) + w₁ a_i^S]`.
-/

open scoped BigOperators

namespace SmoothingCliff.Racing

noncomputable section

/-- Linear-quadratic latency cost `χ a + a²/(2γ)`. -/
def linearQuadraticCost (entryCost capacity investment : ℝ) : ℝ :=
  entryCost * investment + investment ^ 2 / (2 * capacity)

/-- The published upper bound `γ ((v-r)S-χ)^+` on one agent's investment. -/
def investmentUpperBound
    (premium entryCost capacity cap : ℝ) : ℝ :=
  capacity * max (premium * cap - entryCost) 0

/-- One agent's contribution `c_i(a_i^S) + w₁ a_i^S` to the racing burden. -/
def agentRacingBurden
    (slotWeight premium entryCost capacity cap : ℝ) : ℝ :=
  let a := investmentUpperBound premium entryCost capacity cap
  linearQuadraticCost entryCost capacity a + slotWeight * a

/-- The finite-agent racing burden `R(S)`. -/
def racingBurden {ι : Type*} [Fintype ι]
    (slotWeight : ℝ) (premium entryCost capacity : ι → ℝ) (cap : ℝ) : ℝ :=
  ∑ i, agentRacingBurden slotWeight (premium i) (entryCost i) (capacity i) cap

/-- The worst-case smoothing concession, written as a positive multiple of the
reciprocal to expose its strict convexity. -/
def smoothingConcession (slotWeight cap : ℝ) : ℝ :=
  (slotWeight ^ 2 / 4) * cap⁻¹

theorem smoothingConcession_eq (slotWeight cap : ℝ) :
    smoothingConcession slotWeight cap = slotWeight ^ 2 / (4 * cap) := by
  simp [smoothingConcession, div_eq_mul_inv]
  ring

/-- The paper's certified lower objective
`W_SP - w₁²/(4S) - R(S)`. -/
def certifiedNetSurplus {ι : Type*} [Fintype ι]
    (strictPriorityWelfare slotWeight : ℝ)
    (premium entryCost capacity : ι → ℝ) (cap : ℝ) : ℝ :=
  strictPriorityWelfare - smoothingConcession slotWeight cap -
    racingBurden slotWeight premium entryCost capacity cap

/-- All published investment upper bounds vanish at this cap. -/
def NoRaceAt {ι : Type*}
    (premium entryCost : ι → ℝ) (cap : ℝ) : Prop :=
  ∀ i, premium i * cap ≤ entryCost i

/-- The certified objective is continuous on the economically relevant domain
of strictly positive caps. -/
theorem certifiedNetSurplus_continuousOn_pos
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight : ℝ}
    {premium entryCost capacity : ι → ℝ} :
    ContinuousOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) := by
  intro cap hCap
  have hRacing :
      Continuous (racingBurden slotWeight premium entryCost capacity) := by
    unfold racingBurden agentRacingBurden investmentUpperBound
      linearQuadraticCost
    fun_prop
  have hConcession : ContinuousWithinAt
      (smoothingConcession slotWeight) (Set.Ioi 0) cap := by
    apply ContinuousAt.continuousWithinAt
    unfold smoothingConcession
    exact continuousAt_const.mul (continuousAt_inv₀ (ne_of_gt hCap))
  unfold certifiedNetSurplus
  exact (continuousWithinAt_const.sub hConcession).sub
    hRacing.continuousAt.continuousWithinAt

theorem investmentUpperBound_nonneg
    {premium entryCost capacity cap : ℝ} (hCapacity : 0 ≤ capacity) :
    0 ≤ investmentUpperBound premium entryCost capacity cap := by
  exact mul_nonneg hCapacity (le_max_right _ _)

theorem investmentUpperBound_eq_zero
    {premium entryCost capacity cap : ℝ}
    (h : premium * cap ≤ entryCost) :
    investmentUpperBound premium entryCost capacity cap = 0 := by
  unfold investmentUpperBound
  rw [max_eq_right]
  · ring
  · linarith

theorem investmentUpperBound_eq_active
    {premium entryCost capacity cap : ℝ}
    (h : entryCost ≤ premium * cap) :
    investmentUpperBound premium entryCost capacity cap =
      capacity * (premium * cap - entryCost) := by
  unfold investmentUpperBound
  rw [max_eq_left]
  linarith

theorem agentRacingBurden_eq_zero
    {slotWeight premium entryCost capacity cap : ℝ}
    (h : premium * cap ≤ entryCost) :
    agentRacingBurden slotWeight premium entryCost capacity cap = 0 := by
  simp [agentRacingBurden, investmentUpperBound_eq_zero h,
    linearQuadraticCost]

theorem agentRacingBurden_nonneg
    {slotWeight premium entryCost capacity cap : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : 0 ≤ entryCost)
    (hCapacity : 0 < capacity) :
    0 ≤ agentRacingBurden slotWeight premium entryCost capacity cap := by
  have hInvestment :
      0 ≤ investmentUpperBound premium entryCost capacity cap :=
    investmentUpperBound_nonneg (le_of_lt hCapacity)
  have hDenominator : 0 ≤ 2 * capacity :=
    le_of_lt (mul_pos (by norm_num) hCapacity)
  unfold agentRacingBurden linearQuadraticCost
  dsimp only
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hEntryCost hInvestment)
      (div_nonneg (sq_nonneg _) hDenominator))
    (mul_nonneg hWeight hInvestment)

/-- The latency-cost component is nonnegative, so an agent's burden dominates
the direct slot-weight charge on its investment upper bound. -/
theorem slotWeight_mul_investmentUpperBound_le_agentRacingBurden
    {slotWeight premium entryCost capacity cap : ℝ}
    (hEntryCost : 0 ≤ entryCost) (hCapacity : 0 < capacity) :
    slotWeight * investmentUpperBound premium entryCost capacity cap ≤
      agentRacingBurden slotWeight premium entryCost capacity cap := by
  have hInvestment :
      0 ≤ investmentUpperBound premium entryCost capacity cap :=
    investmentUpperBound_nonneg (le_of_lt hCapacity)
  have hLinear :
      0 ≤ entryCost * investmentUpperBound premium entryCost capacity cap :=
    mul_nonneg hEntryCost hInvestment
  have hQuadratic :
      0 ≤ investmentUpperBound premium entryCost capacity cap ^ 2 /
        (2 * capacity) :=
    div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (le_of_lt hCapacity))
  unfold agentRacingBurden linearQuadraticCost
  dsimp only
  linarith

theorem racingBurden_eq_zero {ι : Type*} [Fintype ι]
    {slotWeight cap : ℝ} {premium entryCost capacity : ι → ℝ}
    (hNoRace : NoRaceAt premium entryCost cap) :
    racingBurden slotWeight premium entryCost capacity cap = 0 := by
  simp [racingBurden, agentRacingBurden_eq_zero (hNoRace _)]

theorem noRaceAt_anti {ι : Type*}
    {premium entryCost : ι → ℝ} {smaller larger : ℝ}
    (hPremium : ∀ i, 0 ≤ premium i)
    (hCaps : smaller ≤ larger)
    (hLarger : NoRaceAt premium entryCost larger) :
    NoRaceAt premium entryCost smaller := by
  intro i
  calc
    premium i * smaller ≤ premium i * larger :=
      mul_le_mul_of_nonneg_left hCaps (hPremium i)
    _ ≤ entryCost i := hLarger i

/-- The positive part of an affine premium is convex. -/
theorem positivePartAffine_convex (premium entryCost : ℝ) :
    ConvexOn ℝ Set.univ (fun cap => max (premium * cap - entryCost) 0) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hAffine :
      premium * (a * x + b * y) - entryCost =
        a * (premium * x - entryCost) +
          b * (premium * y - entryCost) := by
    calc
      premium * (a * x + b * y) - entryCost =
          a * (premium * x - entryCost) +
            b * (premium * y - entryCost) +
              (a + b - 1) * entryCost := by ring
      _ = a * (premium * x - entryCost) +
          b * (premium * y - entryCost) := by rw [hab]; ring
  apply max_le
  · calc
      premium * (a * x + b * y) - entryCost =
          a * (premium * x - entryCost) +
            b * (premium * y - entryCost) := hAffine
      _ ≤ a * max (premium * x - entryCost) 0 +
          b * max (premium * y - entryCost) 0 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · exact add_nonneg
      (mul_nonneg ha (le_max_right _ _))
      (mul_nonneg hb (le_max_right _ _))

/-- Algebraic expansion of an active or inactive agent's burden. -/
theorem agentRacingBurden_eq_expanded
    {slotWeight premium entryCost capacity cap : ℝ}
    (hCapacity : capacity ≠ 0) :
    agentRacingBurden slotWeight premium entryCost capacity cap =
      capacity * (entryCost + slotWeight) *
          max (premium * cap - entryCost) 0 +
        capacity / 2 * max (premium * cap - entryCost) 0 ^ 2 := by
  unfold agentRacingBurden linearQuadraticCost investmentUpperBound
  field_simp [hCapacity]
  ring

/-- Each agent's racing-burden term is convex in the published cap. -/
theorem agentRacingBurden_convex
    {slotWeight premium entryCost capacity : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : 0 ≤ entryCost)
    (hCapacity : 0 < capacity) :
    ConvexOn ℝ Set.univ
      (agentRacingBurden slotWeight premium entryCost capacity) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  let z : ℝ → ℝ := fun cap => max (premium * cap - entryCost) 0
  let q : ℝ → ℝ := fun t =>
    capacity * (entryCost + slotWeight) * t + capacity / 2 * t ^ 2
  have hzConvex : z (a * x + b * y) ≤ a * z x + b * z y := by
    simpa [z, smul_eq_mul] using
      (positivePartAffine_convex premium entryCost).2
        (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hzx : 0 ≤ z x := by simp [z]
  have hzy : 0 ≤ z y := by simp [z]
  have hzm : 0 ≤ z (a * x + b * y) := by simp [z]
  have hzbar : 0 ≤ a * z x + b * z y :=
    add_nonneg (mul_nonneg ha hzx) (mul_nonneg hb hzy)
  have hLinearCoeff : 0 ≤ capacity * (entryCost + slotWeight) :=
    mul_nonneg (le_of_lt hCapacity) (add_nonneg hEntryCost hWeight)
  have hQuadraticCoeff : 0 ≤ capacity / 2 :=
    div_nonneg (le_of_lt hCapacity) (by norm_num)
  have hLinearGrowth :
      0 ≤ capacity * (entryCost + slotWeight) *
        ((a * z x + b * z y) - z (a * x + b * y)) :=
    mul_nonneg hLinearCoeff (sub_nonneg.mpr hzConvex)
  have hQuadraticGrowth :
      0 ≤ capacity / 2 *
        (((a * z x + b * z y) - z (a * x + b * y)) *
          ((a * z x + b * z y) + z (a * x + b * y))) :=
    mul_nonneg hQuadraticCoeff
      (mul_nonneg (sub_nonneg.mpr hzConvex) (add_nonneg hzbar hzm))
  have hMonotoneStep :
      q (z (a * x + b * y)) ≤ q (a * z x + b * z y) := by
    dsimp [q]
    nlinarith
  have hJensenRemainder :
      0 ≤ capacity / 2 * a * b * (z x - z y) ^ 2 :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hQuadraticCoeff ha) hb)
      (sq_nonneg _)
  have hQuadraticJensen :
      q (a * z x + b * z y) ≤ a * q (z x) + b * q (z y) := by
    have hbEq : b = 1 - a := by linarith
    have hIdentity :
        a * q (z x) + b * q (z y) - q (a * z x + b * z y) =
          capacity / 2 * a * b * (z x - z y) ^ 2 := by
      dsimp [q]
      rw [hbEq]
      ring
    linarith
  rw [agentRacingBurden_eq_expanded (ne_of_gt hCapacity),
    agentRacingBurden_eq_expanded (ne_of_gt hCapacity),
    agentRacingBurden_eq_expanded (ne_of_gt hCapacity)]
  change q (z (a * x + b * y)) ≤ a * q (z x) + b * q (z y)
  exact le_trans hMonotoneStep hQuadraticJensen

/-- Finite sums preserve convexity.  Kept local to this project to avoid
depending on a stronger auxiliary sum API. -/
theorem convexOn_finset_sum {ι : Type*}
    (agents : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ agents, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun cap => ∑ i ∈ agents, f i cap) := by
  classical
  induction agents using Finset.induction_on with
  | empty =>
      simpa using (convexOn_const (s := Set.univ) (0 : ℝ) convex_univ)
  | @insert i agents hi ih =>
      have hHead : ConvexOn ℝ Set.univ (f i) := h i (Finset.mem_insert_self i agents)
      have hTail : ConvexOn ℝ Set.univ (fun cap => ∑ j ∈ agents, f j cap) :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert, hi, Pi.add_apply] using hHead.add hTail

/-- The complete racing burden is convex in the cap. -/
theorem racingBurden_convex {ι : Type*} [Fintype ι]
    {slotWeight : ℝ} {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i) :
    ConvexOn ℝ Set.univ
      (racingBurden slotWeight premium entryCost capacity) := by
  classical
  unfold racingBurden
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
    convexOn_finset_sum Finset.univ
      (fun i => agentRacingBurden slotWeight
        (premium i) (entryCost i) (capacity i))
      (fun i _ => agentRacingBurden_convex hWeight (hEntryCost i) (hCapacity i))

/-- The reciprocal smoothing concession is strictly convex on positive caps. -/
theorem smoothingConcession_strictConvex
    {slotWeight : ℝ} (hWeight : 0 < slotWeight) :
    StrictConvexOn ℝ (Set.Ioi 0) (smoothingConcession slotWeight) := by
  have hCoefficient : 0 < slotWeight ^ 2 / 4 :=
    div_pos (sq_pos_of_pos hWeight) (by norm_num)
  have hReciprocal :=
    strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hStrict := hReciprocal.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul, zpow_neg_one] at hStrict ⊢
  have hScaled := mul_lt_mul_of_pos_left hStrict hCoefficient
  dsimp [smoothingConcession]
  convert hScaled using 1
  ring

/-- Under the paper's sign restrictions, the certified objective is strictly
concave on all positive caps.  This is stronger than checking strict concavity
separately between activation thresholds: the positive-part kinks preserve
convexity of `R`, while the reciprocal concession supplies strictness. -/
theorem certifiedNetSurplus_strictConcave
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i) :
    StrictConcaveOn ℝ (Set.Ioi 0)
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) := by
  have hRacing : ConvexOn ℝ (Set.Ioi 0)
      (racingBurden slotWeight premium entryCost capacity) :=
    (racingBurden_convex (le_of_lt hWeight) hEntryCost hCapacity).subset
      (Set.subset_univ _) (convex_Ioi 0)
  have hCost : StrictConvexOn ℝ (Set.Ioi 0)
      (smoothingConcession slotWeight +
        racingBurden slotWeight premium entryCost capacity) :=
    (smoothingConcession_strictConvex hWeight).add_convexOn hRacing
  have hNegative : StrictConcaveOn ℝ (Set.Ioi 0)
      (-(smoothingConcession slotWeight +
        racingBurden slotWeight premium entryCost capacity)) := hCost.neg
  have hShifted := hNegative.add_const strictPriorityWelfare
  refine hShifted.congr ?_
  intro cap _
  simp [certifiedNetSurplus]
  ring

/-- Strict concavity makes a positive global maximizer unique, conditional on
existence.  Existence is a separate coercivity/continuity question. -/
theorem certifiedNetSurplus_unique_maximizer
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight first second : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hFirstMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) first)
    (hSecondMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) second) :
    first = second := by
  exact (certifiedNetSurplus_strictConcave hWeight hEntryCost hCapacity).eq_of_isMaxOn
    hFirstMax hSecondMax hFirst hSecond

/-- The paper's right derivative of `R` at a no-race boundary.  Only agents
whose investment upper bound activates exactly at the boundary contribute. -/
def rightRacingSlope {ι : Type*} [Fintype ι]
    (slotWeight : ℝ) (premium entryCost capacity : ι → ℝ)
    (boundary : ℝ) : ℝ :=
  ∑ i, if entryCost i = premium i * boundary then
    capacity i * premium i * (slotWeight + entryCost i) else 0

/-- One agent's right derivative at a no-race boundary.  At a strict slack
constraint the term is locally zero; at an activation kink the derivative is
the active-side slope from the paper. -/
theorem agentRacingBurden_hasDerivWithinAt_noRaceBoundary
    {slotWeight premium entryCost capacity boundary : ℝ}
    (hPremium : 0 ≤ premium)
    (hNoRace : premium * boundary ≤ entryCost)
    (hCapacity : capacity ≠ 0) :
    HasDerivWithinAt
      (agentRacingBurden slotWeight premium entryCost capacity)
      (if entryCost = premium * boundary then
        capacity * premium * (slotWeight + entryCost) else 0)
      (Set.Ici boundary) boundary := by
  by_cases hBoundaryAgent : entryCost = premium * boundary
  · rw [if_pos hBoundaryAgent]
    subst entryCost
    let poly : ℝ → ℝ := fun cap =>
      capacity * (premium * boundary + slotWeight) * (premium * (cap - boundary)) +
        capacity / 2 * (premium * (cap - boundary)) ^ 2
    have hLinear :=
      ((hasDerivAt_id boundary).sub_const boundary).const_mul premium
    have hFirst :=
      hLinear.const_mul (capacity * (premium * boundary + slotWeight))
    have hSecond := (hLinear.pow 2).const_mul (capacity / 2)
    have hPoly : HasDerivAt poly
        (capacity * premium * (slotWeight + premium * boundary)) boundary := by
      dsimp only [poly]
      convert hFirst.add hSecond using 1
      all_goals simp [id]
      all_goals ring
    refine hPoly.hasDerivWithinAt.congr ?_ ?_
    · intro cap hCap
      have hActive : premium * boundary ≤ premium * cap :=
        mul_le_mul_of_nonneg_left hCap hPremium
      rw [agentRacingBurden_eq_expanded hCapacity]
      rw [max_eq_left (sub_nonneg.mpr hActive)]
      dsimp only [poly]
      ring
    · rw [agentRacingBurden_eq_zero hNoRace]
      dsimp only [poly]
      ring
  · rw [if_neg hBoundaryAgent]
    have hStrict : premium * boundary < entryCost := by
      exact lt_of_le_of_ne hNoRace (Ne.symm hBoundaryAgent)
    have hLeft : ContinuousAt (fun cap : ℝ => premium * cap) boundary :=
      continuousAt_const.mul continuousAt_id
    have hRight : ContinuousAt (fun _ : ℝ => entryCost) boundary :=
      continuousAt_const
    have hEventually : ∀ᶠ cap in nhds boundary, premium * cap < entryCost :=
      hLeft.eventually_lt hRight hStrict
    have hEventuallyWithin :
        ∀ᶠ cap in nhdsWithin boundary (Set.Ici boundary),
          premium * cap < entryCost :=
      hEventually.filter_mono inf_le_left
    refine (hasDerivWithinAt_const boundary (Set.Ici boundary) (0 : ℝ)).congr_of_eventuallyEq
      ?_ (agentRacingBurden_eq_zero hNoRace)
    filter_upwards [hEventuallyWithin] with cap hCap
    exact agentRacingBurden_eq_zero (le_of_lt hCap)

/-- Summing the agentwise one-sided derivatives gives exactly the paper's
boundary-agent slope. -/
theorem racingBurden_hasDerivWithinAt_noRaceBoundary
    {ι : Type*} [Fintype ι]
    {slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hPremium : ∀ i, 0 ≤ premium i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hCapacity : ∀ i, capacity i ≠ 0) :
    HasDerivWithinAt
      (racingBurden slotWeight premium entryCost capacity)
      (rightRacingSlope slotWeight premium entryCost capacity boundary)
      (Set.Ici boundary) boundary := by
  classical
  unfold racingBurden rightRacingSlope
  convert HasDerivWithinAt.sum (u := Finset.univ)
      (fun i _ => agentRacingBurden_hasDerivWithinAt_noRaceBoundary
        (slotWeight := slotWeight)
        (hPremium i) (hNoRace i) (hCapacity i)) using 1
  funext cap
  simp only [Finset.sum_apply]

/-- Derivative of the reciprocal smoothing concession away from zero. -/
theorem smoothingConcession_hasDerivAt
    {slotWeight cap : ℝ} (hCap : cap ≠ 0) :
    HasDerivAt (smoothingConcession slotWeight)
      (-slotWeight ^ 2 / (4 * cap ^ 2)) cap := by
  have hInv := hasDerivAt_inv hCap
  have hScaled := hInv.const_mul (slotWeight ^ 2 / 4)
  unfold smoothingConcession
  convert hScaled using 1
  ring

/-- At a no-race boundary, the right derivative of the certified objective is
the marginal smoothing gain minus the boundary agents' racing slope. -/
theorem certifiedNetSurplus_hasDerivWithinAt_noRaceBoundary
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hCapacity : ∀ i, capacity i ≠ 0) :
    HasDerivWithinAt
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity)
      (slotWeight ^ 2 / (4 * boundary ^ 2) -
        rightRacingSlope slotWeight premium entryCost capacity boundary)
      (Set.Ici boundary) boundary := by
  have hConcession : HasDerivWithinAt (smoothingConcession slotWeight)
      (-slotWeight ^ 2 / (4 * boundary ^ 2))
      (Set.Ici boundary) boundary :=
    (smoothingConcession_hasDerivAt (slotWeight := slotWeight)
      (ne_of_gt hBoundary)).hasDerivWithinAt
  have hRacing := racingBurden_hasDerivWithinAt_noRaceBoundary
    (slotWeight := slotWeight)
    hPremium hNoRace hCapacity
  have hObjective :=
    (hConcession.const_sub strictPriorityWelfare).sub hRacing
  unfold certifiedNetSurplus
  convert hObjective using 1
  ring

/-- A right derivative at a constrained local maximum is nonpositive. -/
theorem rightDerivative_nonpos_of_localMax
    {f : ℝ → ℝ} {boundary slope : ℝ}
    (hMax : IsLocalMaxOn f (Set.Ici boundary) boundary)
    (hDerivative : HasDerivWithinAt f slope (Set.Ici boundary) boundary) :
    slope ≤ 0 := by
  have hDirection : (1 : ℝ) ∈ posTangentConeAt (Set.Ici boundary) boundary := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    rw [show Set.Ioi boundary ∩ Set.Ici boundary = Set.Ioi boundary by
      ext x
      constructor
      · exact fun hx => hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        change boundary ≤ x
        exact le_of_lt hx]
    rw [closure_Ioi]
    show boundary ≤ boundary
    exact le_rfl
  have hNonpos := hMax.hasFDerivWithinAt_nonpos
    hDerivative.hasFDerivWithinAt hDirection
  simpa using hNonpos

/-- The boundary agents alone give a linear lower bound on all subsequent
racing burden.  This is the finite-sum inequality behind the one-sided
derivative criterion. -/
theorem boundarySlope_mul_le_racingBurden
    {ι : Type*} [Fintype ι]
    {slotWeight boundary cap : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hCaps : boundary ≤ cap) :
    (cap - boundary) *
        rightRacingSlope slotWeight premium entryCost capacity boundary ≤
      racingBurden slotWeight premium entryCost capacity cap := by
  classical
  rw [rightRacingSlope, Finset.mul_sum]
  unfold racingBurden
  apply Finset.sum_le_sum
  intro i _
  by_cases hBoundaryAgent : entryCost i = premium i * boundary
  · rw [if_pos hBoundaryAgent]
    have hActive : entryCost i ≤ premium i * cap := by
      calc
        entryCost i = premium i * boundary := hBoundaryAgent
        _ ≤ premium i * cap :=
          mul_le_mul_of_nonneg_left hCaps (hPremium i)
    have hPositivePart :
        max (premium i * cap - entryCost i) 0 =
          premium i * (cap - boundary) := by
      rw [max_eq_left]
      · rw [hBoundaryAgent]
        ring
      · linarith
    rw [agentRacingBurden_eq_expanded (ne_of_gt (hCapacity i)), hPositivePart]
    have hQuadratic :
        0 ≤ capacity i / 2 * (premium i * (cap - boundary)) ^ 2 :=
      mul_nonneg
        (div_nonneg (le_of_lt (hCapacity i)) (by norm_num))
        (sq_nonneg _)
    nlinarith [hQuadratic]
  · rw [if_neg hBoundaryAgent]
    simp only [mul_zero]
    exact agentRacingBurden_nonneg hWeight (hEntryCost i) (hCapacity i)

/-- Nonnegative right slope of the convex loss makes the certified no-race
boundary globally optimal.  Written in the paper's form, the hypothesis is
`w₁²/(4S₀²) ≤ ∑_{i∈M} γᵢ(vᵢ-r)(w₁+χᵢ)`. -/
theorem boundary_maximizes_of_slope_condition
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hSlope : slotWeight ^ 2 / (4 * boundary ^ 2) ≤
      rightRacingSlope slotWeight premium entryCost capacity boundary) :
    IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) boundary := by
  intro cap hCapPositive
  change certifiedNetSurplus strictPriorityWelfare slotWeight
      premium entryCost capacity cap ≤
    certifiedNetSurplus strictPriorityWelfare slotWeight
      premium entryCost capacity boundary
  by_cases hCapOrder : boundary ≤ cap
  · have hDelta : 0 ≤ cap - boundary := sub_nonneg.mpr hCapOrder
    have hCapPos : 0 < cap := hCapPositive
    have hRacingLower := boundarySlope_mul_le_racingBurden
      (le_of_lt hWeight) hPremium hEntryCost hCapacity hCapOrder
    have hNumerator : 0 ≤ slotWeight ^ 2 := sq_nonneg _
    have hDenLeft : 0 < 4 * (boundary * cap) :=
      mul_pos (by norm_num) (mul_pos hBoundary hCapPos)
    have hDenRight : 0 < 4 * boundary ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hBoundary)
    have hFractionOrder :
        slotWeight ^ 2 / (4 * (boundary * cap)) ≤
          slotWeight ^ 2 / (4 * boundary ^ 2) := by
      apply (div_le_div_iff₀ hDenLeft hDenRight).2
      have hSquareOrder : boundary ^ 2 ≤ boundary * cap := by
        nlinarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSquareOrder (by norm_num)) hNumerator
    have hScaledFraction := mul_le_mul_of_nonneg_left hFractionOrder hDelta
    have hScaledSlope := mul_le_mul_of_nonneg_left hSlope hDelta
    have hConcessionDifference :
        smoothingConcession slotWeight boundary -
            smoothingConcession slotWeight cap =
          (cap - boundary) *
            (slotWeight ^ 2 / (4 * (boundary * cap))) := by
      rw [smoothingConcession_eq, smoothingConcession_eq]
      field_simp [ne_of_gt hBoundary, ne_of_gt hCapPos]
    have hLossCovered :
        smoothingConcession slotWeight boundary -
            smoothingConcession slotWeight cap ≤
          racingBurden slotWeight premium entryCost capacity cap := by
      rw [hConcessionDifference]
      exact le_trans hScaledFraction (le_trans hScaledSlope hRacingLower)
    simp only [certifiedNetSurplus]
    rw [racingBurden_eq_zero hNoRace]
    linarith
  · have hCapBelow : cap < boundary := lt_of_not_ge hCapOrder
    have hNoRaceCap : NoRaceAt premium entryCost cap :=
      noRaceAt_anti hPremium (le_of_lt hCapBelow) hNoRace
    have hDenCap : 0 < 4 * cap := mul_pos (by norm_num) hCapPositive
    have hDenBoundary : 0 < 4 * boundary :=
      mul_pos (by norm_num) hBoundary
    have hConcession :
        smoothingConcession slotWeight boundary <
          smoothingConcession slotWeight cap := by
      rw [smoothingConcession_eq, smoothingConcession_eq]
      apply (div_lt_div_iff₀ hDenBoundary hDenCap).2
      nlinarith [sq_pos_of_pos hWeight]
    simp only [certifiedNetSurplus]
    rw [racingBurden_eq_zero hNoRaceCap, racingBurden_eq_zero hNoRace]
    linarith

/-- Necessity of the paper's boundary derivative condition.  A global maximum
at the positive no-race boundary is in particular a right-local maximum, so
its right derivative cannot be positive. -/
theorem slope_condition_of_boundary_maximizes
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) boundary) :
    slotWeight ^ 2 / (4 * boundary ^ 2) ≤
      rightRacingSlope slotWeight premium entryCost capacity boundary := by
  have hSubset : Set.Ici boundary ⊆ Set.Ioi (0 : ℝ) := by
    intro cap hCap
    change 0 < cap
    exact lt_of_lt_of_le hBoundary hCap
  have hLocal : IsLocalMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ici boundary) boundary :=
    (hMax.on_subset hSubset).localize
  have hDerivative :=
    certifiedNetSurplus_hasDerivWithinAt_noRaceBoundary
      (strictPriorityWelfare := strictPriorityWelfare)
      (slotWeight := slotWeight) hBoundary hPremium hNoRace
      (fun i => ne_of_gt (hCapacity i))
  have hNonpos := rightDerivative_nonpos_of_localMax hLocal hDerivative
  linarith

/-- Exact analytic version of Proposition `prop:optcert` (iii): the positive
no-race boundary maximizes the certified objective exactly when the marginal
smoothing gain is no larger than the boundary agents' racing slope. -/
theorem boundary_maximizer_iff_slope_condition
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary) :
    IsMaxOn
        (certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity) (Set.Ioi 0) boundary ↔
      slotWeight ^ 2 / (4 * boundary ^ 2) ≤
        rightRacingSlope slotWeight premium entryCost capacity boundary := by
  constructor
  · exact slope_condition_of_boundary_maximizes
      hBoundary hPremium hCapacity hNoRace
  · exact boundary_maximizes_of_slope_condition
      hWeight hBoundary hPremium hEntryCost hCapacity hNoRace

/-- Under the boundary slope condition, `S₀` is not merely a maximizer but the
unique positive maximizer. -/
theorem boundary_unique_maximizer_of_slope_condition
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary other : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hOther : 0 < other)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hSlope : slotWeight ^ 2 / (4 * boundary ^ 2) ≤
      rightRacingSlope slotWeight premium entryCost capacity boundary)
    (hOtherMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) other) :
    other = boundary := by
  exact certifiedNetSurplus_unique_maximizer
    hWeight hEntryCost hCapacity hOther hBoundary hOtherMax
    (boundary_maximizes_of_slope_condition hWeight hBoundary hPremium
      hEntryCost hCapacity hNoRace hSlope)

/-- On a no-race interval the objective rises strictly with the cap: racing
burden stays zero while the smoothing concession `w₁²/(4S)` falls. -/
theorem certifiedNetSurplus_strict_increase_of_noRace
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight smaller larger : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hSmaller : 0 < smaller)
    (hLarger : smaller < larger)
    (hNoRaceSmaller : NoRaceAt premium entryCost smaller)
    (hNoRaceLarger : NoRaceAt premium entryCost larger) :
    certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity smaller <
      certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity larger := by
  have hLargerPos : 0 < larger := lt_trans hSmaller hLarger
  have hDenSmaller : 0 < 4 * smaller := mul_pos (by norm_num) hSmaller
  have hDenLarger : 0 < 4 * larger := mul_pos (by norm_num) hLargerPos
  have hWeightSq : 0 < slotWeight ^ 2 := sq_pos_of_pos hWeight
  have hConcession :
      slotWeight ^ 2 / (4 * larger) <
        slotWeight ^ 2 / (4 * smaller) := by
    apply (div_lt_div_iff₀ hDenLarger hDenSmaller).2
    nlinarith
  simp only [certifiedNetSurplus,
    racingBurden_eq_zero hNoRaceSmaller,
    racingBurden_eq_zero hNoRaceLarger, sub_zero]
  rw [smoothingConcession_eq slotWeight smaller,
    smoothingConcession_eq slotWeight larger]
  linarith

/-- Any global maximizer over positive caps is weakly above a positive
no-race boundary.  This is the exact analytic content of the sentence that
caps tighter than `S₀` are dominated. -/
theorem maximizer_not_below_noRaceBoundary
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary maximizer : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hBoundary : 0 < boundary)
    (hMaximizer : 0 < maximizer)
    (hNoRaceBoundary : NoRaceAt premium entryCost boundary)
    (hMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) maximizer) :
    boundary ≤ maximizer := by
  by_contra hNot
  have hBelow : maximizer < boundary := lt_of_not_ge hNot
  have hNoRaceMaximizer : NoRaceAt premium entryCost maximizer :=
    noRaceAt_anti hPremium (le_of_lt hBelow) hNoRaceBoundary
  have hStrict :
      certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity maximizer <
        certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity boundary :=
    certifiedNetSurplus_strict_increase_of_noRace
      (strictPriorityWelfare := strictPriorityWelfare)
      (capacity := capacity)
      hWeight hMaximizer hBelow hNoRaceMaximizer hNoRaceBoundary
  have hOptimal :
      certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity boundary ≤
        certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity maximizer := hMax hBoundary
  exact (not_lt_of_ge hOptimal) hStrict

/-- Once one positive-premium agent's direct slot-weight charge covers the
smoothing concession at the no-race boundary, the certified objective cannot
exceed its boundary value.  This supplies an explicit finite upper cutoff for
the existence proof below. -/
theorem certifiedNetSurplus_le_boundary_of_cap_ge_activationTarget
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary cap : ℝ}
    {premium entryCost capacity : ι → ℝ} (agent : ι)
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hCapPositive : 0 < cap)
    (hPremium : 0 < premium agent)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary)
    (hCap : (entryCost agent +
        smoothingConcession slotWeight boundary /
          (slotWeight * capacity agent)) / premium agent ≤ cap) :
    certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity cap ≤
      certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity boundary := by
  classical
  let target :=
    smoothingConcession slotWeight boundary /
      (slotWeight * capacity agent)
  have hTargetNonneg : 0 ≤ target := by
    dsimp [target]
    exact div_nonneg
      (by
        rw [smoothingConcession_eq]
        exact div_nonneg (sq_nonneg _)
          (mul_nonneg (by norm_num) (le_of_lt hBoundary)))
      (mul_nonneg (le_of_lt hWeight) (le_of_lt (hCapacity agent)))
  change (entryCost agent + target) / premium agent ≤ cap at hCap
  have hScaled :=
    mul_le_mul_of_nonneg_left hCap (le_of_lt hPremium)
  have hQuotient :
      premium agent * ((entryCost agent + target) / premium agent) =
        entryCost agent + target := by
    field_simp [ne_of_gt hPremium]
  rw [hQuotient] at hScaled
  have hActive : entryCost agent ≤ premium agent * cap := by
    linarith
  have hGap : target ≤ premium agent * cap - entryCost agent := by
    linarith
  have hInvestment :
      capacity agent * target ≤
        investmentUpperBound (premium agent) (entryCost agent)
          (capacity agent) cap := by
    rw [investmentUpperBound_eq_active hActive]
    exact mul_le_mul_of_nonneg_left hGap
      (le_of_lt (hCapacity agent))
  have hWeightedInvestment :=
    mul_le_mul_of_nonneg_left hInvestment (le_of_lt hWeight)
  have hTargetIdentity :
      slotWeight * (capacity agent * target) =
        smoothingConcession slotWeight boundary := by
    dsimp [target]
    field_simp [ne_of_gt hWeight, ne_of_gt (hCapacity agent)]
  have hAgentLower :
      smoothingConcession slotWeight boundary ≤
        agentRacingBurden slotWeight (premium agent) (entryCost agent)
          (capacity agent) cap := by
    rw [← hTargetIdentity]
    exact le_trans hWeightedInvestment
      (slotWeight_mul_investmentUpperBound_le_agentRacingBurden
        (slotWeight := slotWeight) (premium := premium agent)
        (entryCost := entryCost agent) (capacity := capacity agent)
        (cap := cap) (hEntryCost agent) (hCapacity agent))
  have hAgentLeRacing :
      agentRacingBurden slotWeight (premium agent) (entryCost agent)
          (capacity agent) cap ≤
        racingBurden slotWeight premium entryCost capacity cap := by
    unfold racingBurden
    exact Finset.single_le_sum
      (fun i _ => agentRacingBurden_nonneg (le_of_lt hWeight)
        (hEntryCost i) (hCapacity i))
      (Finset.mem_univ agent)
  have hRacingLower :
      smoothingConcession slotWeight boundary ≤
        racingBurden slotWeight premium entryCost capacity cap :=
    le_trans hAgentLower hAgentLeRacing
  have hConcessionCap : 0 ≤ smoothingConcession slotWeight cap := by
    rw [smoothingConcession_eq]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (by norm_num) (le_of_lt hCapPositive))
  simp only [certifiedNetSurplus]
  rw [racingBurden_eq_zero hNoRace]
  linarith

/-- With at least one strictly positive premium, the certified objective has a
unique positive global maximizer.  The proof constructs an explicit upper
cutoff from that agent, maximizes continuously on the resulting compact
interval, and uses strict concavity for uniqueness. -/
theorem certifiedNetSurplus_existsUnique_maximizer
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hSomePremium : ∃ i, 0 < premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary) :
    ∃! maximizer : ℝ,
      0 < maximizer ∧
        IsMaxOn
          (certifiedNetSurplus strictPriorityWelfare slotWeight
            premium entryCost capacity) (Set.Ioi 0) maximizer := by
  classical
  obtain ⟨agent, hAgentPremium⟩ := hSomePremium
  let target :=
    smoothingConcession slotWeight boundary /
      (slotWeight * capacity agent)
  let upper := (entryCost agent + target) / premium agent
  have hTargetNonneg : 0 ≤ target := by
    dsimp [target]
    exact div_nonneg
      (by
        rw [smoothingConcession_eq]
        exact div_nonneg (sq_nonneg _)
          (mul_nonneg (by norm_num) (le_of_lt hBoundary)))
      (mul_nonneg (le_of_lt hWeight) (le_of_lt (hCapacity agent)))
  have hBoundaryUpper : boundary ≤ upper := by
    dsimp [upper]
    apply (le_div_iff₀ hAgentPremium).2
    calc
      boundary * premium agent = premium agent * boundary := mul_comm _ _
      _ ≤ entryCost agent := hNoRace agent
      _ ≤ entryCost agent + target := le_add_of_nonneg_right hTargetNonneg
  have hUpperPositive : 0 < upper := lt_of_lt_of_le hBoundary hBoundaryUpper
  have hIntervalSubset : Set.Icc boundary upper ⊆ Set.Ioi (0 : ℝ) := by
    intro cap hCap
    change 0 < cap
    exact lt_of_lt_of_le hBoundary hCap.1
  have hContinuous : ContinuousOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Icc boundary upper) :=
    certifiedNetSurplus_continuousOn_pos.mono hIntervalSubset
  obtain ⟨maximizer, hMaximizerMem, hMaxInterval⟩ :=
    isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr hBoundaryUpper) hContinuous
  have hBoundaryMem : boundary ∈ Set.Icc boundary upper :=
    ⟨le_rfl, hBoundaryUpper⟩
  have hBoundaryLeMax :
      certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity boundary ≤
        certifiedNetSurplus strictPriorityWelfare slotWeight
          premium entryCost capacity maximizer :=
    hMaxInterval hBoundaryMem
  have hMaximizerPositive : 0 < maximizer :=
    lt_of_lt_of_le hBoundary hMaximizerMem.1
  have hMaxGlobal : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        premium entryCost capacity) (Set.Ioi 0) maximizer := by
    intro cap hCapPositive
    by_cases hBelow : cap < boundary
    · have hNoRaceCap : NoRaceAt premium entryCost cap :=
        noRaceAt_anti hPremium (le_of_lt hBelow) hNoRace
      have hStrict :
          certifiedNetSurplus strictPriorityWelfare slotWeight
              premium entryCost capacity cap <
            certifiedNetSurplus strictPriorityWelfare slotWeight
              premium entryCost capacity boundary :=
        certifiedNetSurplus_strict_increase_of_noRace
          (strictPriorityWelfare := strictPriorityWelfare)
          (capacity := capacity) hWeight hCapPositive hBelow
          hNoRaceCap hNoRace
      exact le_trans (le_of_lt hStrict) hBoundaryLeMax
    · by_cases hAbove : upper < cap
      · have hThreshold :
            (entryCost agent +
                smoothingConcession slotWeight boundary /
                  (slotWeight * capacity agent)) /
                premium agent ≤ cap := by
          change upper ≤ cap
          exact le_of_lt hAbove
        have hAtMostBoundary :=
          certifiedNetSurplus_le_boundary_of_cap_ge_activationTarget
            (strictPriorityWelfare := strictPriorityWelfare)
            (premium := premium) (entryCost := entryCost)
            (capacity := capacity) agent hWeight hBoundary hCapPositive
            hAgentPremium hEntryCost hCapacity hNoRace hThreshold
        exact le_trans hAtMostBoundary hBoundaryLeMax
      · exact hMaxInterval
          ⟨le_of_not_gt hBelow, le_of_not_gt hAbove⟩
  refine ⟨maximizer, ⟨hMaximizerPositive, hMaxGlobal⟩, ?_⟩
  intro other hOther
  exact certifiedNetSurplus_unique_maximizer
    hWeight hEntryCost hCapacity hOther.1 hMaximizerPositive
    hOther.2 hMaxGlobal

/-- Proposition `prop:optcert` (ii), at the level of the analytic objective:
under the displayed sign, no-race, and positive-premium assumptions, there is
a unique positive global maximizer and it is weakly above the no-race
boundary. -/
theorem certifiedNetSurplus_existsUnique_maximizer_above_noRaceBoundary
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight boundary : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hBoundary : 0 < boundary)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hSomePremium : ∃ i, 0 < premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hNoRace : NoRaceAt premium entryCost boundary) :
    ∃! maximizer : ℝ,
      0 < maximizer ∧ boundary ≤ maximizer ∧
        IsMaxOn
          (certifiedNetSurplus strictPriorityWelfare slotWeight
            premium entryCost capacity) (Set.Ioi 0) maximizer := by
  obtain ⟨maximizer, hMaximizer, hUnique⟩ :=
    certifiedNetSurplus_existsUnique_maximizer
      hWeight hBoundary hPremium hSomePremium hEntryCost hCapacity hNoRace
  have hAbove : boundary ≤ maximizer :=
    maximizer_not_below_noRaceBoundary
      (strictPriorityWelfare := strictPriorityWelfare)
      (capacity := capacity) hWeight hPremium hBoundary hMaximizer.1
      hNoRace hMaximizer.2
  refine ⟨maximizer, ⟨hMaximizer.1, hAbove, hMaximizer.2⟩, ?_⟩
  intro other hOther
  exact hUnique other ⟨hOther.1, hOther.2.2⟩

end

end SmoothingCliff.Racing
