import SmoothingCliff.Racing.StrictPriority
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Order.Basic

/-!
# The symmetric lattice equilibrium of the strict-priority race

This file formalizes Proposition `prop:sp_mixed` of *Smoothing the Cliff*.
Write `q = κ / w₁`, `G = v-r`, and let `depth = ⌊1/q⌋`.  Instead of hiding
the floor operation in a definition, its exact characterization is carried as

`depth * q ≤ 1 < (depth + 1) * q`.

The strategy assigns mass `q` to `0,G,...,(depth-1)G` and the residual mass
`1-depth*q` to `depth*G`.  Expected payoffs below quantify over every
nonnegative real deviation, not merely over lattice deviations.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Probability mass at the integer lattice index.  It is zero outside the
displayed finite support. -/
def latticeMass (depth : ℕ) (q : ℝ) (index : ℕ) : ℝ :=
  if index < depth then q
  else if index = depth then 1 - (depth : ℝ) * q
  else 0

/-- The elementary conditions saying that the displayed finite mass function
is a probability law. -/
def LatticeProbabilityLaw (depth : ℕ) (q : ℝ) : Prop :=
  (∀ index : ℕ, 0 ≤ latticeMass depth q index) ∧
    ∑ index ∈ Finset.range (depth + 1), latticeMass depth q index = 1

/-- Expected captured contested band against the lattice strategy. -/
def latticeExpectedCapturedGap
    (gap : ℝ) (depth : ℕ) (q action : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (depth + 1),
    latticeMass depth q index *
      strictPriorityCapturedGap gap action ((index : ℝ) * gap)

/-- Expected payoff from a pure action against the lattice strategy.  The
literal finite-expectation identity is proved below once mass one is known. -/
def latticeExpectedPayoff
    (slotWeight gap : ℝ) (depth : ℕ) (q action : ℝ) : ℝ :=
  slotWeight * latticeExpectedCapturedGap gap depth q action -
    slotWeight * q * action

/-- Expected payoff when the focal player also draws from the lattice law. -/
def latticeStrategyExpectedPayoff
    (slotWeight gap : ℝ) (depth : ℕ) (q : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (depth + 1),
    latticeMass depth q index *
      latticeExpectedPayoff slotWeight gap depth q ((index : ℝ) * gap)

/-- A symmetric mixed-Nash certificate: the displayed masses form a
probability law and no nonnegative pure deviation beats the strategy's own
expected payoff.  Linearity then also excludes every finite mixed deviation. -/
def SymmetricLatticeMixedNash
    (slotWeight gap : ℝ) (depth : ℕ) (q : ℝ) : Prop :=
  LatticeProbabilityLaw depth q ∧
    ∀ action : ℝ, 0 ≤ action →
      latticeExpectedPayoff slotWeight gap depth q action ≤
        latticeStrategyExpectedPayoff slotWeight gap depth q

/-- Expected action under the lattice law. -/
def latticeExpectedAction (gap : ℝ) (depth : ℕ) (q : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (depth + 1),
    latticeMass depth q index * ((index : ℝ) * gap)

/-- Total expected resource dissipation of two independent symmetric draws,
with marginal cost `κ = w₁ q`. -/
def latticeExpectedDissipation
    (slotWeight gap : ℝ) (depth : ℕ) (q : ℝ) : ℝ :=
  2 * (slotWeight * q) * latticeExpectedAction gap depth q

/-- The same dissipation written in the paper's original marginal-cost
primitive `κ`. -/
def latticeExpectedDissipationAtCost
    (slotWeight gap marginalCost : ℝ) (depth : ℕ) : ℝ :=
  2 * marginalCost *
    latticeExpectedAction gap depth (marginalCost / slotWeight)

/-- Total expected contested surplus allocated across the two players. -/
def latticeExpectedAllocatedContestedSurplus
    (slotWeight gap : ℝ) (depth : ℕ) (q : ℝ) : ℝ :=
  2 * slotWeight *
    (∑ index ∈ Finset.range (depth + 1),
      latticeMass depth q index *
        latticeExpectedCapturedGap gap depth q ((index : ℝ) * gap))

/-- The dimensionless dissipation factor from the paper. -/
def normalizedLatticeDissipation (depth : ℕ) (q : ℝ) : ℝ :=
  ((depth : ℝ) * q) * (2 - (depth : ℝ) * q - q)

/-- The paper's displayed lattice depth `⌊1/q⌋`. -/
def floorLatticeDepth (q : ℝ) : ℕ := ⌊1 / q⌋₊

/-- Literal finite expectation of the imported strict-priority payoff at
marginal cost `κ`. -/
def latticeExpectedStrictPriorityPayoff
    (slotWeight gap marginalCost : ℝ) (depth : ℕ) (action : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (depth + 1),
    latticeMass depth (marginalCost / slotWeight) index *
      strictPriorityPayoff slotWeight gap marginalCost action
        ((index : ℝ) * gap)

/-- Payoff of the lattice mixture against itself, in the original game. -/
def latticeStrategyExpectedStrictPriorityPayoff
    (slotWeight gap marginalCost : ℝ) (depth : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (depth + 1),
    latticeMass depth (marginalCost / slotWeight) index *
      latticeExpectedStrictPriorityPayoff slotWeight gap marginalCost depth
        ((index : ℝ) * gap)

/-- Original-cost interface: `q` is the normalized marginal cost `κ/w₁`. -/
def SymmetricLatticeMixedNashAtCost
    (slotWeight gap marginalCost : ℝ) (depth : ℕ) : Prop :=
  LatticeProbabilityLaw depth (marginalCost / slotWeight) ∧
    ∀ action : ℝ, 0 ≤ action →
      latticeExpectedStrictPriorityPayoff
          slotWeight gap marginalCost depth action ≤
        latticeStrategyExpectedStrictPriorityPayoff
          slotWeight gap marginalCost depth

@[simp] theorem latticeMass_of_lt
    {depth index : ℕ} {q : ℝ} (hindex : index < depth) :
    latticeMass depth q index = q := by
  simp [latticeMass, hindex]

@[simp] theorem latticeMass_at_depth (depth : ℕ) (q : ℝ) :
    latticeMass depth q depth = 1 - (depth : ℝ) * q := by
  simp [latticeMass]

@[simp] theorem latticeMass_of_depth_lt
    {depth index : ℕ} {q : ℝ} (hindex : depth < index) :
    latticeMass depth q index = 0 := by
  simp [latticeMass, Ne.symm hindex.ne, Nat.not_lt.mpr hindex.le]

theorem latticeMass_nonneg
    {depth index : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (hLower : (depth : ℝ) * q ≤ 1) :
    0 ≤ latticeMass depth q index := by
  by_cases hlt : index < depth
  · simp [latticeMass, hlt, hq]
  · by_cases heq : index = depth
    · subst index
      simp [latticeMass]
      linarith
    · simp [latticeMass, hlt, heq]

theorem latticeMass_le_q
    {depth index : ℕ} {q : ℝ}
    (hq : 0 ≤ q)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    latticeMass depth q index ≤ q := by
  by_cases hlt : index < depth
  · simp [latticeMass, hlt]
  · by_cases heq : index = depth
    · subst index
      simp [latticeMass]
      nlinarith
    · simp [latticeMass, hlt, heq, hq]

theorem sum_latticeMass_eq_one (depth : ℕ) (q : ℝ) :
    ∑ index ∈ Finset.range (depth + 1), latticeMass depth q index = 1 := by
  rw [Finset.sum_range_succ]
  have hFirst :
      ∑ index ∈ Finset.range depth, latticeMass depth q index =
        (depth : ℝ) * q := by
    calc
      ∑ index ∈ Finset.range depth, latticeMass depth q index =
          ∑ _index ∈ Finset.range depth, q := by
            apply Finset.sum_congr rfl
            intro index hindex
            exact latticeMass_of_lt (Finset.mem_range.mp hindex)
      _ = (depth : ℝ) * q := by simp
  rw [hFirst, latticeMass_at_depth]
  ring

theorem lattice_probabilityLaw
    {depth : ℕ} {q : ℝ}
    (hq : 0 ≤ q) (hLower : (depth : ℝ) * q ≤ 1) :
    LatticeProbabilityLaw depth q := by
  exact ⟨fun index => latticeMass_nonneg hq hLower,
    sum_latticeMass_eq_one depth q⟩

/-- Each lattice cell contributes a telescoping truncated interval length. -/
theorem strictPriorityCapturedGap_eq_min_sub_min
    {gap action : ℝ} (hgap : 0 ≤ gap) (index : ℕ) :
    strictPriorityCapturedGap gap action ((index : ℝ) * gap) =
      min action (((index : ℝ) + 1) * gap) -
        min action ((index : ℝ) * gap) := by
  have hindexNonneg : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
  have hbaseNonneg : 0 ≤ (index : ℝ) * gap :=
    mul_nonneg hindexNonneg hgap
  by_cases hBelow : action ≤ (index : ℝ) * gap
  · have hLead : action - (index : ℝ) * gap ≤ 0 := sub_nonpos.mpr hBelow
    have hBelowNext : action ≤ ((index : ℝ) + 1) * gap := by nlinarith
    rw [strictPriorityCapturedGap, max_eq_right hLead,
      min_eq_left hgap, min_eq_left hBelowNext, min_eq_left hBelow]
    ring
  · have hAboveBase : (index : ℝ) * gap ≤ action := le_of_not_ge hBelow
    by_cases hWithin : action ≤ ((index : ℝ) + 1) * gap
    · have hLead : 0 ≤ action - (index : ℝ) * gap := sub_nonneg.mpr hAboveBase
      have hLeadGap : action - (index : ℝ) * gap ≤ gap := by nlinarith
      rw [strictPriorityCapturedGap, max_eq_left hLead,
        min_eq_left hLeadGap, min_eq_left hWithin,
        min_eq_right hAboveBase]
    · have hBeyond : ((index : ℝ) + 1) * gap ≤ action := le_of_not_ge hWithin
      have hLead : 0 ≤ action - (index : ℝ) * gap := sub_nonneg.mpr hAboveBase
      have hGapLead : gap ≤ action - (index : ℝ) * gap := by nlinarith
      rw [strictPriorityCapturedGap, max_eq_left hLead,
        min_eq_right hGapLead, min_eq_right hBeyond,
        min_eq_right hAboveBase]
      ring

/-- The truncated-gap cells partition `[0,min(action,nG)]`. -/
theorem sum_strictPriorityCapturedGap_eq_min
    {gap action : ℝ} (hgap : 0 ≤ gap) (haction : 0 ≤ action) :
    ∀ cells : ℕ,
      ∑ index ∈ Finset.range cells,
          strictPriorityCapturedGap gap action ((index : ℝ) * gap) =
        min action ((cells : ℝ) * gap)
  | 0 => by simp [haction]
  | cells + 1 => by
      rw [Finset.sum_range_succ,
        sum_strictPriorityCapturedGap_eq_min hgap haction cells,
        strictPriorityCapturedGap_eq_min_sub_min hgap]
      norm_num

/-- Against the displayed lattice law, expected captured band is at most
`q * action` for every nonnegative real action. -/
theorem latticeExpectedCapturedGap_le
    {gap q action : ℝ} {depth : ℕ}
    (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (hUpper : 1 < ((depth : ℝ) + 1) * q)
    (haction : 0 ≤ action) :
    latticeExpectedCapturedGap gap depth q action ≤ q * action := by
  have hTerm (index : ℕ) (hindex : index ∈ Finset.range (depth + 1)) :
      latticeMass depth q index *
          strictPriorityCapturedGap gap action ((index : ℝ) * gap) ≤
        q * strictPriorityCapturedGap gap action ((index : ℝ) * gap) := by
    exact mul_le_mul_of_nonneg_right
      (latticeMass_le_q hq hUpper)
      (strictPriorityCapturedGap_nonneg hgap)
  unfold latticeExpectedCapturedGap
  calc
    ∑ index ∈ Finset.range (depth + 1),
        latticeMass depth q index *
          strictPriorityCapturedGap gap action ((index : ℝ) * gap) ≤
      ∑ index ∈ Finset.range (depth + 1),
        q * strictPriorityCapturedGap gap action ((index : ℝ) * gap) := by
          exact Finset.sum_le_sum hTerm
    _ = q * (∑ index ∈ Finset.range (depth + 1),
        strictPriorityCapturedGap gap action ((index : ℝ) * gap)) := by
          rw [Finset.mul_sum]
    _ = q * min action (((depth + 1 : ℕ) : ℝ) * gap) := by
          rw [sum_strictPriorityCapturedGap_eq_min hgap haction]
    _ ≤ q * action :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hq

/-- At every support point `kG`, expected captured band is exactly `q kG`. -/
theorem latticeExpectedCapturedGap_at_lattice
    {gap q : ℝ} {depth index : ℕ}
    (hgap : 0 ≤ gap) (hindex : index ≤ depth) :
    latticeExpectedCapturedGap gap depth q ((index : ℝ) * gap) =
      q * ((index : ℝ) * gap) := by
  have hTerm (opponent : ℕ)
      (hopponent : opponent ∈ Finset.range (depth + 1)) :
      latticeMass depth q opponent *
          strictPriorityCapturedGap gap ((index : ℝ) * gap)
            ((opponent : ℝ) * gap) =
        q * strictPriorityCapturedGap gap ((index : ℝ) * gap)
          ((opponent : ℝ) * gap) := by
    by_cases hBefore : opponent < index
    · rw [latticeMass_of_lt (lt_of_lt_of_le hBefore hindex)]
    · have hAfter : index ≤ opponent := Nat.le_of_not_gt hBefore
      have hScaled : (index : ℝ) * gap ≤ (opponent : ℝ) * gap :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hAfter) hgap
      have hCaptured :
          strictPriorityCapturedGap gap ((index : ℝ) * gap)
              ((opponent : ℝ) * gap) = 0 := by
        unfold strictPriorityCapturedGap
        rw [max_eq_right (sub_nonpos.mpr hScaled), min_eq_left hgap]
      rw [hCaptured]
      ring
  have hIndexNext : index ≤ depth + 1 :=
    le_trans hindex (Nat.le_add_right depth 1)
  have hScaledNext :
      (index : ℝ) * gap ≤ (((depth + 1 : ℕ) : ℝ) * gap) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hIndexNext) hgap
  unfold latticeExpectedCapturedGap
  calc
    ∑ opponent ∈ Finset.range (depth + 1),
        latticeMass depth q opponent *
          strictPriorityCapturedGap gap ((index : ℝ) * gap)
            ((opponent : ℝ) * gap) =
      ∑ opponent ∈ Finset.range (depth + 1),
        q * strictPriorityCapturedGap gap ((index : ℝ) * gap)
          ((opponent : ℝ) * gap) := by
            exact Finset.sum_congr rfl hTerm
    _ = q * (∑ opponent ∈ Finset.range (depth + 1),
        strictPriorityCapturedGap gap ((index : ℝ) * gap)
          ((opponent : ℝ) * gap)) := by
            rw [Finset.mul_sum]
    _ = q * min ((index : ℝ) * gap)
        (((depth + 1 : ℕ) : ℝ) * gap) := by
          rw [sum_strictPriorityCapturedGap_eq_min hgap
            (mul_nonneg (Nat.cast_nonneg index) hgap)]
    _ = q * ((index : ℝ) * gap) := by
      rw [min_eq_left hScaledNext]

/-- `latticeExpectedPayoff` is the literal expectation of the imported
strict-priority payoff against the finite probability mass function. -/
theorem latticeExpectedPayoff_eq_sum_strictPriorityPayoff
    (slotWeight gap q action : ℝ) (depth : ℕ) :
    latticeExpectedPayoff slotWeight gap depth q action =
      ∑ index ∈ Finset.range (depth + 1),
        latticeMass depth q index *
          strictPriorityPayoff slotWeight gap (slotWeight * q) action
            ((index : ℝ) * gap) := by
  symm
  calc
    ∑ index ∈ Finset.range (depth + 1),
        latticeMass depth q index *
          strictPriorityPayoff slotWeight gap (slotWeight * q) action
            ((index : ℝ) * gap) =
      ∑ index ∈ Finset.range (depth + 1),
        (slotWeight *
            (latticeMass depth q index *
              strictPriorityCapturedGap gap action ((index : ℝ) * gap)) -
          (slotWeight * q * action) * latticeMass depth q index) := by
            apply Finset.sum_congr rfl
            intro index _hindex
            unfold strictPriorityPayoff
            ring
    _ = slotWeight *
          (∑ index ∈ Finset.range (depth + 1),
            latticeMass depth q index *
              strictPriorityCapturedGap gap action ((index : ℝ) * gap)) -
        (slotWeight * q * action) *
          (∑ index ∈ Finset.range (depth + 1), latticeMass depth q index) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = latticeExpectedPayoff slotWeight gap depth q action := by
      rw [sum_latticeMass_eq_one]
      unfold latticeExpectedPayoff latticeExpectedCapturedGap
      ring

/-- The normalized payoff is exactly the expected payoff in the imported
strict-priority game with marginal cost `κ`. -/
theorem latticeExpectedPayoff_at_cost_eq_sum_strictPriorityPayoff
    {slotWeight : ℝ} (hWeight : 0 < slotWeight)
    (gap marginalCost action : ℝ) (depth : ℕ) :
    latticeExpectedPayoff slotWeight gap depth
        (marginalCost / slotWeight) action =
      ∑ index ∈ Finset.range (depth + 1),
        latticeMass depth (marginalCost / slotWeight) index *
          strictPriorityPayoff slotWeight gap marginalCost action
            ((index : ℝ) * gap) := by
  have hCostEq : slotWeight * (marginalCost / slotWeight) = marginalCost := by
    field_simp
  simpa only [hCostEq] using
    latticeExpectedPayoff_eq_sum_strictPriorityPayoff
      slotWeight gap (marginalCost / slotWeight) action depth

theorem latticeExpectedStrictPriorityPayoff_eq_normalized
    {slotWeight : ℝ} (hWeight : 0 < slotWeight)
    (gap marginalCost : ℝ) (depth : ℕ) (action : ℝ) :
    latticeExpectedStrictPriorityPayoff
        slotWeight gap marginalCost depth action =
      latticeExpectedPayoff slotWeight gap depth
        (marginalCost / slotWeight) action := by
  symm
  exact latticeExpectedPayoff_at_cost_eq_sum_strictPriorityPayoff
    hWeight gap marginalCost action depth

theorem latticeStrategyExpectedStrictPriorityPayoff_eq_normalized
    {slotWeight : ℝ} (hWeight : 0 < slotWeight)
    (gap marginalCost : ℝ) (depth : ℕ) :
    latticeStrategyExpectedStrictPriorityPayoff
        slotWeight gap marginalCost depth =
      latticeStrategyExpectedPayoff slotWeight gap depth
        (marginalCost / slotWeight) := by
  unfold latticeStrategyExpectedStrictPriorityPayoff
  unfold latticeStrategyExpectedPayoff
  apply Finset.sum_congr rfl
  intro index _hindex
  rw [latticeExpectedStrictPriorityPayoff_eq_normalized
    hWeight gap marginalCost depth]

theorem symmetricLatticeMixedNashAtCost_iff_normalized
    {slotWeight : ℝ} (hWeight : 0 < slotWeight)
    (gap marginalCost : ℝ) (depth : ℕ) :
    SymmetricLatticeMixedNashAtCost
        slotWeight gap marginalCost depth ↔
      SymmetricLatticeMixedNash slotWeight gap depth
        (marginalCost / slotWeight) := by
  unfold SymmetricLatticeMixedNashAtCost SymmetricLatticeMixedNash
  constructor
  · rintro ⟨hLaw, hBest⟩
    refine ⟨hLaw, ?_⟩
    intro action haction
    rw [← latticeExpectedStrictPriorityPayoff_eq_normalized
      hWeight gap marginalCost depth action,
      ← latticeStrategyExpectedStrictPriorityPayoff_eq_normalized
        hWeight gap marginalCost depth]
    exact hBest action haction
  · rintro ⟨hLaw, hBest⟩
    refine ⟨hLaw, ?_⟩
    intro action haction
    rw [latticeExpectedStrictPriorityPayoff_eq_normalized
      hWeight gap marginalCost depth action,
      latticeStrategyExpectedStrictPriorityPayoff_eq_normalized
        hWeight gap marginalCost depth]
    exact hBest action haction

/-- Every nonnegative real deviation earns at most zero. -/
theorem latticeExpectedPayoff_nonpos
    {slotWeight gap q action : ℝ} {depth : ℕ}
    (hWeight : 0 ≤ slotWeight) (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (hUpper : 1 < ((depth : ℝ) + 1) * q)
    (haction : 0 ≤ action) :
    latticeExpectedPayoff slotWeight gap depth q action ≤ 0 := by
  have hCaptured := latticeExpectedCapturedGap_le
    hgap hq hUpper haction
  have hWeighted := mul_le_mul_of_nonneg_left hCaptured hWeight
  unfold latticeExpectedPayoff
  nlinarith

/-- Every displayed support action is indifferent with payoff exactly zero. -/
theorem latticeExpectedPayoff_at_lattice
    {slotWeight gap q : ℝ} {depth index : ℕ}
    (hgap : 0 ≤ gap) (hindex : index ≤ depth) :
    latticeExpectedPayoff slotWeight gap depth q ((index : ℝ) * gap) = 0 := by
  rw [latticeExpectedPayoff]
  rw [latticeExpectedCapturedGap_at_lattice hgap hindex]
  ring

/-- The lattice strategy itself earns expected payoff zero. -/
theorem latticeStrategyExpectedPayoff_eq_zero
    {slotWeight gap q : ℝ} {depth : ℕ} (hgap : 0 ≤ gap) :
    latticeStrategyExpectedPayoff slotWeight gap depth q = 0 := by
  unfold latticeStrategyExpectedPayoff
  apply Finset.sum_eq_zero
  intro index hindex
  rw [latticeExpectedPayoff_at_lattice hgap
    (Nat.le_of_lt_succ (Finset.mem_range.mp hindex))]
  ring

/-- Literal expected payoff in the original `κ`-cost game is nonpositive for
every nonnegative real deviation. -/
theorem latticeExpectedStrictPriorityPayoff_nonpos
    {slotWeight gap marginalCost action : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap)
    (hCost : 0 ≤ marginalCost)
    (hUpper :
      1 < ((depth : ℝ) + 1) * (marginalCost / slotWeight))
    (haction : 0 ≤ action) :
    latticeExpectedStrictPriorityPayoff
      slotWeight gap marginalCost depth action ≤ 0 := by
  rw [latticeExpectedStrictPriorityPayoff_eq_normalized
    hWeight gap marginalCost depth action]
  exact latticeExpectedPayoff_nonpos hWeight.le hgap
    (div_nonneg hCost hWeight.le) hUpper haction

/-- Every support point of the original-cost lattice law earns exactly zero. -/
theorem latticeExpectedStrictPriorityPayoff_at_lattice
    {slotWeight gap marginalCost : ℝ} {depth index : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap)
    (hindex : index ≤ depth) :
    latticeExpectedStrictPriorityPayoff slotWeight gap marginalCost depth
        ((index : ℝ) * gap) = 0 := by
  rw [latticeExpectedStrictPriorityPayoff_eq_normalized
    hWeight gap marginalCost depth]
  exact latticeExpectedPayoff_at_lattice hgap hindex

/-- Consequently the original-cost lattice mixture has payoff zero against
itself. -/
theorem latticeStrategyExpectedStrictPriorityPayoff_eq_zero
    {slotWeight gap marginalCost : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap) :
    latticeStrategyExpectedStrictPriorityPayoff
      slotWeight gap marginalCost depth = 0 := by
  rw [latticeStrategyExpectedStrictPriorityPayoff_eq_normalized
    hWeight gap marginalCost depth]
  exact latticeStrategyExpectedPayoff_eq_zero hgap

/-- Pure-deviation optimality extends immediately to every finite mixed
deviation with nonnegative weights. -/
theorem lattice_finiteMixedDeviation_nonpos
    {ι : Type*} (deviations : Finset ι) (weight action : ι → ℝ)
    {slotWeight gap q : ℝ} {depth : ℕ}
    (hWeight : 0 ≤ slotWeight) (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (hUpper : 1 < ((depth : ℝ) + 1) * q)
    (hMass : ∀ i ∈ deviations, 0 ≤ weight i)
    (hAction : ∀ i ∈ deviations, 0 ≤ action i) :
    ∑ i ∈ deviations,
        weight i * latticeExpectedPayoff slotWeight gap depth q (action i) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (hMass i hi)
    (latticeExpectedPayoff_nonpos hWeight hgap hq hUpper (hAction i hi))

/-- Finite mixed deviations in the original-cost game cannot improve on the
zero equilibrium payoff. -/
theorem lattice_finiteMixedDeviationAtCost_nonpos
    {ι : Type*} (deviations : Finset ι) (weight action : ι → ℝ)
    {slotWeight gap marginalCost : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap)
    (hCost : 0 ≤ marginalCost)
    (hUpper :
      1 < ((depth : ℝ) + 1) * (marginalCost / slotWeight))
    (hMass : ∀ i ∈ deviations, 0 ≤ weight i)
    (hAction : ∀ i ∈ deviations, 0 ≤ action i) :
    ∑ i ∈ deviations,
        weight i * latticeExpectedStrictPriorityPayoff
          slotWeight gap marginalCost depth (action i) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (hMass i hi)
    (latticeExpectedStrictPriorityPayoff_nonpos hWeight hgap hCost hUpper
      (hAction i hi))

/-- Proposition `prop:sp_mixed`, equilibrium part.  The floor inequalities
are exactly `depth = floor (1/q)`, with `q = κ/w₁`. -/
theorem lattice_symmetric_mixedNash
    {slotWeight gap q : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hq : 0 < q)
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    SymmetricLatticeMixedNash slotWeight gap depth q := by
  have hLaw := lattice_probabilityLaw hq.le hLower
  have hOwn := latticeStrategyExpectedPayoff_eq_zero
    (slotWeight := slotWeight) (q := q) (depth := depth) hgap.le
  refine ⟨hLaw, ?_⟩
  intro action haction
  rw [hOwn]
  exact latticeExpectedPayoff_nonpos hWeight.le hgap.le hq.le hUpper haction

/-- The exact floor choice satisfies the two arithmetic bounds used by the
equilibrium proof. -/
theorem floorLatticeDepth_bounds
    {q : ℝ} (hq : 0 < q) :
    ((floorLatticeDepth q : ℕ) : ℝ) * q ≤ 1 ∧
      1 < (((floorLatticeDepth q : ℕ) : ℝ) + 1) * q := by
  have hInvNonneg : 0 ≤ 1 / q := by positivity
  have hFloor : ((floorLatticeDepth q : ℕ) : ℝ) ≤ 1 / q := by
    exact Nat.floor_le hInvNonneg
  have hNext : 1 / q < ((floorLatticeDepth q : ℕ) : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (1 / q)
  exact ⟨(le_div_iff₀ hq).mp hFloor, (div_lt_iff₀ hq).mp hNext⟩

theorem floorLatticeDepth_pos
    {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    0 < floorLatticeDepth q := by
  have hUpper := (floorLatticeDepth_bounds hq).2
  by_contra hNot
  have hZero : floorLatticeDepth q = 0 := Nat.eq_zero_of_not_pos hNot
  rw [hZero] at hUpper
  norm_num at hUpper
  linarith

/-- Proposition `prop:sp_mixed` with the literal floor depth and normalized
cost `q∈(0,1)`. -/
theorem floorLattice_symmetric_mixedNash
    {slotWeight gap q : ℝ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hq : 0 < q) (hqOne : q < 1) :
    0 < floorLatticeDepth q ∧
      SymmetricLatticeMixedNash slotWeight gap (floorLatticeDepth q) q := by
  exact ⟨floorLatticeDepth_pos hq hqOne,
    lattice_symmetric_mixedNash hWeight hgap hq
      (floorLatticeDepth_bounds hq).1 (floorLatticeDepth_bounds hq).2⟩

/-- Proposition `prop:sp_mixed` in the paper's original primitives
`0 < κ < w₁`. -/
theorem floorLattice_symmetric_mixedNash_at_cost
    {slotWeight gap marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight) :
    0 < floorLatticeDepth (marginalCost / slotWeight) ∧
      SymmetricLatticeMixedNashAtCost slotWeight gap marginalCost
        (floorLatticeDepth (marginalCost / slotWeight)) := by
  have hNormalized := floorLattice_symmetric_mixedNash hWeight hgap
    (div_pos hCost hWeight) ((div_lt_one hWeight).mpr hCostWeight)
  exact ⟨hNormalized.1,
    (symmetricLatticeMixedNashAtCost_iff_normalized hWeight gap marginalCost
      (floorLatticeDepth (marginalCost / slotWeight))).mpr hNormalized.2⟩

/-- Sum of the first `n` natural numbers, cast to `ℝ`, in a subtraction-free
real form convenient for the moment computation. -/
theorem sum_range_natCast_eq (n : ℕ) :
    ∑ index ∈ Finset.range n, (index : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Exact first moment of the displayed lattice law. -/
theorem latticeExpectedAction_eq
    (gap q : ℝ) (depth : ℕ) :
    latticeExpectedAction gap depth q =
      gap * (depth : ℝ) * (1 - q * ((depth : ℝ) + 1) / 2) := by
  unfold latticeExpectedAction
  rw [Finset.sum_range_succ]
  have hFirst :
      ∑ index ∈ Finset.range depth,
          latticeMass depth q index * ((index : ℝ) * gap) =
        q * gap * ((depth : ℝ) * ((depth : ℝ) - 1) / 2) := by
    calc
      ∑ index ∈ Finset.range depth,
          latticeMass depth q index * ((index : ℝ) * gap) =
        ∑ index ∈ Finset.range depth, q * ((index : ℝ) * gap) := by
          apply Finset.sum_congr rfl
          intro index hindex
          rw [latticeMass_of_lt (Finset.mem_range.mp hindex)]
      _ = q * gap *
          (∑ index ∈ Finset.range depth, (index : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _hindex
        ring
      _ = q * gap * ((depth : ℝ) * ((depth : ℝ) - 1) / 2) := by
        rw [sum_range_natCast_eq]
  rw [hFirst, latticeMass_at_depth]
  ring

/-- Proposition `prop:sp_mixed`, exact dissipation formula. -/
theorem latticeExpectedDissipation_eq
    (slotWeight gap q : ℝ) (depth : ℕ) :
    latticeExpectedDissipation slotWeight gap depth q =
      slotWeight * gap * normalizedLatticeDissipation depth q := by
  rw [latticeExpectedDissipation, latticeExpectedAction_eq]
  unfold normalizedLatticeDissipation
  ring

/-- Exact dissipation formula in the paper's original primitives. -/
theorem latticeExpectedDissipationAtCost_eq
    {slotWeight : ℝ} (hWeight : 0 < slotWeight)
    (gap marginalCost : ℝ) (depth : ℕ) :
    latticeExpectedDissipationAtCost slotWeight gap marginalCost depth =
      slotWeight * gap *
        normalizedLatticeDissipation depth (marginalCost / slotWeight) := by
  have hCostEq : slotWeight * (marginalCost / slotWeight) = marginalCost := by
    field_simp
  rw [← latticeExpectedDissipation_eq slotWeight gap
    (marginalCost / slotWeight) depth]
  unfold latticeExpectedDissipationAtCost latticeExpectedDissipation
  rw [hCostEq]

/-- Zero equilibrium payoffs mean that allocated contested surplus equals
resources burned. -/
theorem latticeAllocatedContestedSurplus_eq_dissipation
    {slotWeight gap q : ℝ} {depth : ℕ} (hgap : 0 ≤ gap) :
    latticeExpectedAllocatedContestedSurplus slotWeight gap depth q =
      latticeExpectedDissipation slotWeight gap depth q := by
  have hGross :
      ∑ index ∈ Finset.range (depth + 1),
          latticeMass depth q index *
            latticeExpectedCapturedGap gap depth q ((index : ℝ) * gap) =
        q * latticeExpectedAction gap depth q := by
    calc
      ∑ index ∈ Finset.range (depth + 1),
          latticeMass depth q index *
            latticeExpectedCapturedGap gap depth q ((index : ℝ) * gap) =
        ∑ index ∈ Finset.range (depth + 1),
          latticeMass depth q index * (q * ((index : ℝ) * gap)) := by
            apply Finset.sum_congr rfl
            intro index hindex
            rw [latticeExpectedCapturedGap_at_lattice hgap
              (Nat.le_of_lt_succ (Finset.mem_range.mp hindex))]
      _ = q * (∑ index ∈ Finset.range (depth + 1),
          latticeMass depth q index * ((index : ℝ) * gap)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro index _hindex
            ring
      _ = q * latticeExpectedAction gap depth q := by
        rfl
  unfold latticeExpectedAllocatedContestedSurplus
  rw [hGross]
  unfold latticeExpectedDissipation
  ring

/-- The floor characterization implies `1-q < depth*q ≤ 1`. -/
theorem scaledDepth_mem_interval
    {q : ℝ} {depth : ℕ}
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    1 - q < (depth : ℝ) * q ∧ (depth : ℝ) * q ≤ 1 := by
  constructor
  · nlinarith
  · exact hLower

/-- The dimensionless dissipation is bounded below by `1-q`. -/
theorem one_sub_q_le_normalizedLatticeDissipation
    {q : ℝ} {depth : ℕ}
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    1 - q ≤ normalizedLatticeDissipation depth q := by
  have hx := scaledDepth_mem_interval hLower hUpper
  have hProduct :
      0 ≤ (1 - (depth : ℝ) * q) *
        ((depth : ℝ) * q - (1 - q)) :=
    mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1.le)
  unfold normalizedLatticeDissipation
  nlinarith

/-- The concave quadratic is at most its vertex value. -/
theorem normalizedLatticeDissipation_le_vertex
    (q : ℝ) (depth : ℕ) :
    normalizedLatticeDissipation depth q ≤ (1 - q / 2) ^ 2 := by
  have hSquare : 0 ≤ ((depth : ℝ) * q - (1 - q / 2)) ^ 2 := sq_nonneg _
  unfold normalizedLatticeDissipation
  nlinarith

theorem normalizedLatticeDissipation_le_one
    {q : ℝ} {depth : ℕ} (hq : 0 ≤ q) :
    normalizedLatticeDissipation depth q ≤ 1 := by
  have hx : 0 ≤ (depth : ℝ) * q :=
    mul_nonneg (Nat.cast_nonneg depth) hq
  have hSquare : 0 ≤ (1 - (depth : ℝ) * q) ^ 2 := sq_nonneg _
  have hProduct : 0 ≤ q * ((depth : ℝ) * q) := mul_nonneg hq hx
  unfold normalizedLatticeDissipation
  nlinarith

/-- Proposition `prop:sp_mixed`, the two displayed dissipation bounds. -/
theorem latticeExpectedDissipation_bounds
    {slotWeight gap q : ℝ} {depth : ℕ}
    (hWeight : 0 ≤ slotWeight) (hgap : 0 ≤ gap)
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    (slotWeight - slotWeight * q) * gap ≤
        latticeExpectedDissipation slotWeight gap depth q ∧
      latticeExpectedDissipation slotWeight gap depth q ≤
        (1 - q / 2) ^ 2 * slotWeight * gap := by
  rw [latticeExpectedDissipation_eq]
  have hScale : 0 ≤ slotWeight * gap := mul_nonneg hWeight hgap
  constructor
  · calc
      (slotWeight - slotWeight * q) * gap =
          (slotWeight * gap) * (1 - q) := by ring
      _ ≤ (slotWeight * gap) * normalizedLatticeDissipation depth q :=
        mul_le_mul_of_nonneg_left
          (one_sub_q_le_normalizedLatticeDissipation hLower hUpper) hScale
      _ = slotWeight * gap * normalizedLatticeDissipation depth q := rfl
  · calc
      slotWeight * gap * normalizedLatticeDissipation depth q ≤
          (slotWeight * gap) * (1 - q / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (normalizedLatticeDissipation_le_vertex q depth) hScale
      _ = (1 - q / 2) ^ 2 * slotWeight * gap := by ring

/-- The displayed bounds with `q=κ/w₁`, including the paper's literal lower
bound `(w₁-κ)G`. -/
theorem latticeExpectedDissipationAtCost_bounds
    {slotWeight gap marginalCost : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap)
    (hLower : (depth : ℝ) * (marginalCost / slotWeight) ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * (marginalCost / slotWeight)) :
    (slotWeight - marginalCost) * gap ≤
        latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ∧
      latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ≤
        (1 - marginalCost / (2 * slotWeight)) ^ 2 * slotWeight * gap := by
  have hCostEq : slotWeight * (marginalCost / slotWeight) = marginalCost := by
    field_simp
  have hBounds := latticeExpectedDissipation_bounds
    hWeight.le hgap hLower hUpper
  have hDissipationEq :
      latticeExpectedDissipationAtCost slotWeight gap marginalCost depth =
        latticeExpectedDissipation slotWeight gap depth
          (marginalCost / slotWeight) := by
    unfold latticeExpectedDissipationAtCost latticeExpectedDissipation
    rw [hCostEq]
  have hHalfRatio :
      (marginalCost / slotWeight) / 2 =
        marginalCost / (2 * slotWeight) := by
    field_simp
  rw [hDissipationEq]
  simpa only [hCostEq, hHalfRatio] using hBounds

/-- The formula and bounds at the paper's literal choice
`J=⌊w₁/κ⌋=⌊1/(κ/w₁)⌋`. -/
theorem floorLatticeExpectedDissipationAtCost_formula_and_bounds
    {slotWeight gap marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hgap : 0 ≤ gap)
    (hCost : 0 < marginalCost) :
    let q := marginalCost / slotWeight
    let depth := floorLatticeDepth q
    latticeExpectedDissipationAtCost slotWeight gap marginalCost depth =
        slotWeight * gap * normalizedLatticeDissipation depth q ∧
      (slotWeight - marginalCost) * gap ≤
          latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ∧
        latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ≤
          (1 - q / 2) ^ 2 * slotWeight * gap := by
  dsimp only
  have hFloor := floorLatticeDepth_bounds (div_pos hCost hWeight)
  have hHalfRatio :
      (marginalCost / slotWeight) / 2 =
        marginalCost / (2 * slotWeight) := by
    field_simp
  refine ⟨latticeExpectedDissipationAtCost_eq hWeight gap marginalCost _, ?_⟩
  simpa only [hHalfRatio] using
    (latticeExpectedDissipationAtCost_bounds hWeight hgap hFloor.1 hFloor.2)

/-- When `depth*q=1` (equivalently `w₁/κ` is the integer `depth`), the lower
bound is attained. -/
theorem latticeExpectedDissipation_eq_lower_of_scaledDepth_eq_one
    {slotWeight gap q : ℝ} {depth : ℕ}
    (hInteger : (depth : ℝ) * q = 1) :
    latticeExpectedDissipation slotWeight gap depth q =
      (slotWeight - slotWeight * q) * gap := by
  rw [latticeExpectedDissipation_eq]
  unfold normalizedLatticeDissipation
  rw [hInteger]
  ring

theorem latticeExpectedDissipationAtCost_eq_lower_of_integer_ratio
    {slotWeight gap marginalCost : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight)
    (hInteger : (depth : ℝ) * marginalCost = slotWeight) :
    latticeExpectedDissipationAtCost slotWeight gap marginalCost depth =
      (slotWeight - marginalCost) * gap := by
  have hRatio : (depth : ℝ) * (marginalCost / slotWeight) = 1 := by
    field_simp
    exact hInteger
  have hCostEq : slotWeight * (marginalCost / slotWeight) = marginalCost := by
    field_simp
  have hNormalized :=
    latticeExpectedDissipation_eq_lower_of_scaledDepth_eq_one
      (slotWeight := slotWeight) (gap := gap) hRatio
  unfold latticeExpectedDissipationAtCost latticeExpectedDissipation at *
  rw [hCostEq] at hNormalized
  exact hNormalized

theorem floorLatticeDepth_eq_of_integer_cost_ratio
    {slotWeight marginalCost : ℝ} {depth : ℕ}
    (hCost : 0 < marginalCost)
    (hInteger : (depth : ℝ) * marginalCost = slotWeight) :
    floorLatticeDepth (marginalCost / slotWeight) = depth := by
  have hRatioInv :
      1 / (marginalCost / slotWeight) = (depth : ℝ) := by
    field_simp
    nlinarith
  unfold floorLatticeDepth
  rw [hRatioInv]
  exact Nat.floor_natCast depth

/-- Literal floor version of the paper's equality claim: if `w₁/κ` is the
natural number `depth`, the lower dissipation bound is attained. -/
theorem floorLatticeExpectedDissipationAtCost_eq_lower_of_integer_ratio
    {slotWeight gap marginalCost : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hCost : 0 < marginalCost)
    (hInteger : (depth : ℝ) * marginalCost = slotWeight) :
    latticeExpectedDissipationAtCost slotWeight gap marginalCost
        (floorLatticeDepth (marginalCost / slotWeight)) =
      (slotWeight - marginalCost) * gap := by
  rw [floorLatticeDepth_eq_of_integer_cost_ratio hCost hInteger]
  exact latticeExpectedDissipationAtCost_eq_lower_of_integer_ratio
    hWeight hInteger

/-- In the no-pure-equilibrium region `q<1/2`, the lattice equilibrium burns
strictly more than half the contested prize. -/
theorem half_contestedPrize_lt_latticeExpectedDissipation
    {slotWeight gap q : ℝ} {depth : ℕ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hqHalf : q < 1 / 2)
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    slotWeight * gap / 2 <
      latticeExpectedDissipation slotWeight gap depth q := by
  have hBounds := latticeExpectedDissipation_bounds
    hWeight.le hgap.le hLower hUpper
  have hScale : 0 < slotWeight * gap := mul_pos hWeight hgap
  have hScaled := mul_lt_mul_of_pos_left hqHalf hScale
  calc
    slotWeight * gap / 2 < (slotWeight - slotWeight * q) * gap := by
      nlinarith
    _ ≤ latticeExpectedDissipation slotWeight gap depth q := hBounds.1

/-- Original-cost, literal-floor form of the strict half-prize result. -/
theorem half_contestedPrize_lt_floorLatticeExpectedDissipationAtCost
    {slotWeight gap marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hCost : 0 < marginalCost)
    (hCostHalf : marginalCost < slotWeight / 2) :
    slotWeight * gap / 2 <
      latticeExpectedDissipationAtCost slotWeight gap marginalCost
        (floorLatticeDepth (marginalCost / slotWeight)) := by
  have hRatio : 0 < marginalCost / slotWeight := div_pos hCost hWeight
  have hRatioHalf : marginalCost / slotWeight < 1 / 2 := by
    apply (div_lt_iff₀ hWeight).2
    nlinarith
  have hFloor := floorLatticeDepth_bounds hRatio
  have hNormalized := half_contestedPrize_lt_latticeExpectedDissipation
    hWeight hgap hRatioHalf hFloor.1 hFloor.2
  have hCostEq : slotWeight * (marginalCost / slotWeight) = marginalCost := by
    field_simp
  unfold latticeExpectedDissipationAtCost latticeExpectedDissipation at *
  rw [hCostEq] at hNormalized
  exact hNormalized

/-- Quantitative cheap-technology estimate: normalized dissipation lies
within `q` of the full contested prize. -/
theorem normalizedLatticeDissipation_cheap_bound
    {q : ℝ} {depth : ℕ}
    (hq : 0 ≤ q)
    (hLower : (depth : ℝ) * q ≤ 1)
    (hUpper : 1 < ((depth : ℝ) + 1) * q) :
    0 ≤ 1 - normalizedLatticeDissipation depth q ∧
      1 - normalizedLatticeDissipation depth q ≤ q := by
  constructor
  · exact sub_nonneg.mpr (normalizedLatticeDissipation_le_one hq)
  · have hBound := one_sub_q_le_normalizedLatticeDissipation hLower hUpper
    linarith

/-- Sequence form of the paper's cheap-technology limit. -/
theorem normalizedLatticeDissipation_tendsto_one
    {q : ℕ → ℝ} {depth : ℕ → ℕ}
    (hq : ∀ n, 0 ≤ q n)
    (hLower : ∀ n, ((depth n : ℕ) : ℝ) * q n ≤ 1)
    (hUpper : ∀ n, 1 < (((depth n : ℕ) : ℝ) + 1) * q n)
    (hqZero : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => normalizedLatticeDissipation (depth n) (q n))
      Filter.atTop (nhds 1) := by
  have hLowerLimit :
      Filter.Tendsto (fun n => 1 - q n) Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hqZero using 1
    all_goals norm_num
  apply Filter.Tendsto.squeeze hLowerLimit tendsto_const_nhds
  · intro n
    exact one_sub_q_le_normalizedLatticeDissipation (hLower n) (hUpper n)
  · intro n
    exact normalizedLatticeDissipation_le_one (hq n)

/-- The unnormalized expected dissipation converges to the full contested
prize `w₁G` as `q=κ/w₁ → 0`. -/
theorem latticeExpectedDissipation_tendsto_fullPrize
    (slotWeight gap : ℝ) {q : ℕ → ℝ} {depth : ℕ → ℕ}
    (hq : ∀ n, 0 ≤ q n)
    (hLower : ∀ n, ((depth n : ℕ) : ℝ) * q n ≤ 1)
    (hUpper : ∀ n, 1 < (((depth n : ℕ) : ℝ) + 1) * q n)
    (hqZero : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => latticeExpectedDissipation slotWeight gap (depth n) (q n))
      Filter.atTop (nhds (slotWeight * gap)) := by
  have hNormalized := normalizedLatticeDissipation_tendsto_one
    hq hLower hUpper hqZero
  have hScaled :
      Filter.Tendsto
        (fun n => (slotWeight * gap) *
          normalizedLatticeDissipation (depth n) (q n))
        Filter.atTop (nhds ((slotWeight * gap) * 1)) :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _n : ℕ => slotWeight * gap) Filter.atTop
      (nhds (slotWeight * gap))).mul hNormalized
  simpa only [latticeExpectedDissipation_eq, mul_one] using hScaled

/-- Literal `κ→0` version of the cheap-technology limit for fixed `w₁>0`. -/
theorem latticeExpectedDissipationAtCost_tendsto_fullPrize
    {slotWeight : ℝ} (hWeight : 0 < slotWeight) (gap : ℝ)
    {marginalCost : ℕ → ℝ} {depth : ℕ → ℕ}
    (hCost : ∀ n, 0 ≤ marginalCost n)
    (hLower : ∀ n,
      ((depth n : ℕ) : ℝ) * (marginalCost n / slotWeight) ≤ 1)
    (hUpper : ∀ n,
      1 < (((depth n : ℕ) : ℝ) + 1) * (marginalCost n / slotWeight))
    (hCostZero : Filter.Tendsto marginalCost Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => latticeExpectedDissipationAtCost
        slotWeight gap (marginalCost n) (depth n))
      Filter.atTop (nhds (slotWeight * gap)) := by
  have hRatioNonneg : ∀ n, 0 ≤ marginalCost n / slotWeight :=
    fun n => div_nonneg (hCost n) hWeight.le
  have hRatioZero :
      Filter.Tendsto (fun n => marginalCost n / slotWeight)
        Filter.atTop (nhds 0) := by
    convert hCostZero.div_const slotWeight using 1
    norm_num
  have hNormalized := latticeExpectedDissipation_tendsto_fullPrize
    slotWeight gap hRatioNonneg hLower hUpper hRatioZero
  have hEventuallyEq :
      (fun n => latticeExpectedDissipationAtCost
          slotWeight gap (marginalCost n) (depth n)) =ᶠ[Filter.atTop]
        (fun n => latticeExpectedDissipation slotWeight gap (depth n)
          (marginalCost n / slotWeight)) := by
    filter_upwards [] with n
    unfold latticeExpectedDissipationAtCost latticeExpectedDissipation
    have hCostEq :
        slotWeight * (marginalCost n / slotWeight) = marginalCost n := by
      field_simp
    rw [hCostEq]
  exact hNormalized.congr' hEventuallyEq.symm

/-- Proposition `prop:sp_mixed`, cheap-technology limit with the literal
floor lattice chosen at every positive cost. -/
theorem floorLatticeExpectedDissipationAtCost_tendsto_fullPrize
    {slotWeight : ℝ} (hWeight : 0 < slotWeight) (gap : ℝ)
    {marginalCost : ℕ → ℝ}
    (hCost : ∀ n, 0 < marginalCost n)
    (hCostZero : Filter.Tendsto marginalCost Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => latticeExpectedDissipationAtCost slotWeight gap
        (marginalCost n)
        (floorLatticeDepth (marginalCost n / slotWeight)))
      Filter.atTop (nhds (slotWeight * gap)) := by
  apply latticeExpectedDissipationAtCost_tendsto_fullPrize hWeight gap
    (fun n => (hCost n).le)
  · intro n
    exact (floorLatticeDepth_bounds (div_pos (hCost n) hWeight)).1
  · intro n
    exact (floorLatticeDepth_bounds (div_pos (hCost n) hWeight)).2
  · exact hCostZero

/-- A single kernel-facing package for the finite-cost claims of Proposition
`prop:sp_mixed`. -/
theorem floorLattice_equilibrium_and_dissipation_package
    {slotWeight gap marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hgap : 0 < gap)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight) :
    let q := marginalCost / slotWeight
    let depth := floorLatticeDepth q
    LatticeProbabilityLaw depth q ∧
      (∀ action : ℝ, 0 ≤ action →
        latticeExpectedStrictPriorityPayoff
          slotWeight gap marginalCost depth action ≤ 0) ∧
      (∀ index : ℕ, index ≤ depth →
        latticeExpectedStrictPriorityPayoff slotWeight gap marginalCost depth
          ((index : ℝ) * gap) = 0) ∧
      latticeStrategyExpectedStrictPriorityPayoff
          slotWeight gap marginalCost depth = 0 ∧
      SymmetricLatticeMixedNashAtCost
          slotWeight gap marginalCost depth ∧
      latticeExpectedAction gap depth q =
        gap * (depth : ℝ) * (1 - q * ((depth : ℝ) + 1) / 2) ∧
      latticeExpectedDissipationAtCost slotWeight gap marginalCost depth =
        slotWeight * gap * normalizedLatticeDissipation depth q ∧
      (slotWeight - marginalCost) * gap ≤
        latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ∧
      latticeExpectedDissipationAtCost slotWeight gap marginalCost depth ≤
        (1 - q / 2) ^ 2 * slotWeight * gap ∧
      latticeExpectedAllocatedContestedSurplus slotWeight gap depth q =
        latticeExpectedDissipationAtCost slotWeight gap marginalCost depth := by
  dsimp only
  let q := marginalCost / slotWeight
  let depth := floorLatticeDepth q
  have hRatio : 0 < q := by
    dsimp [q]
    exact div_pos hCost hWeight
  have hFloor := floorLatticeDepth_bounds hRatio
  have hNash := (floorLattice_symmetric_mixedNash_at_cost
    hWeight hgap hCost hCostWeight).2
  have hFormulaBounds :=
    floorLatticeExpectedDissipationAtCost_formula_and_bounds
      hWeight hgap.le hCost
  have hCostEq : slotWeight * q = marginalCost := by
    dsimp [q]
    field_simp
  have hAllocated :
      latticeExpectedAllocatedContestedSurplus slotWeight gap depth q =
        latticeExpectedDissipationAtCost
          slotWeight gap marginalCost depth := by
    calc
      latticeExpectedAllocatedContestedSurplus slotWeight gap depth q =
          latticeExpectedDissipation slotWeight gap depth q :=
        latticeAllocatedContestedSurplus_eq_dissipation hgap.le
      _ = latticeExpectedDissipationAtCost
          slotWeight gap marginalCost depth := by
        unfold latticeExpectedDissipation latticeExpectedDissipationAtCost
        rw [hCostEq]
  refine ⟨hNash.1, ?_, ?_, ?_, hNash, ?_, ?_, ?_, ?_, hAllocated⟩
  · intro action haction
    exact latticeExpectedStrictPriorityPayoff_nonpos hWeight hgap.le hCost.le
      hFloor.2 haction
  · intro index hindex
    exact latticeExpectedStrictPriorityPayoff_at_lattice
      hWeight hgap.le hindex
  · exact latticeStrategyExpectedStrictPriorityPayoff_eq_zero
      hWeight hgap.le
  · exact latticeExpectedAction_eq gap q depth
  · exact hFormulaBounds.1
  · exact hFormulaBounds.2.1
  · exact hFormulaBounds.2.2

end

end SmoothingCliff.Racing
