import SmoothingCliff.Racing.OptimalCapEntryCost

/-!
# The optimal cap diverges as the racing burden vanishes

Formal target: the limit clause of clause (iv) of Proposition `prop:optcert` in
`Smoothing_the_Cliff_ITCS.tex`: with the prize fixed, the optimal published cap
diverges when both the linear and the quadratic racing burdens vanish, so the
principal publishes no finite cap and strict priority is optimal.

The paper argues through the right derivative of the racing burden.  The route
below needs no derivative.  A strictly concave function whose value at `2M`
exceeds its value at `M` has its maximizer above `M`, and the certified
objective satisfies that comparison as soon as the racing burden at `2M` is
below an explicit multiple of the prize.  The burden itself is bounded by
`w * cap * sum gamma p + (3/2) * cap^2 * sum gamma p^2`, which is exactly the
pair of aggregates the paper sends to zero.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- A strictly concave function that rises from `M` to `2M` has its maximizer
above `M`. -/
theorem lt_isMaxOn_of_lt_double
    {f : ℝ → ℝ} {maximizer bound : ℝ}
    (hConcave : StrictConcaveOn ℝ (Set.Ioi 0) f)
    (hBound : 0 < bound)
    (hMaximizer : 0 < maximizer)
    (hMax : IsMaxOn f (Set.Ioi 0) maximizer)
    (hRise : f bound < f (2 * bound)) :
    bound < maximizer := by
  by_contra hNot
  have hle : maximizer ≤ bound := le_of_not_gt hNot
  have hboundMem : bound ∈ Set.Ioi (0 : ℝ) := hBound
  have hdoubleMem : 2 * bound ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    linarith
  have hmaxMem : maximizer ∈ Set.Ioi (0 : ℝ) := hMaximizer
  have hfmax : f (2 * bound) ≤ f maximizer := hMax hdoubleMem
  have hfbound : f bound ≤ f maximizer := hMax hboundMem
  have hstrict : maximizer < bound := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      rw [heq] at hfmax
      linarith
    · exact hlt
  have hdenomPos : 0 < 2 * bound - maximizer := by linarith
  have hdne : (2 * bound - maximizer) ≠ 0 := ne_of_gt hdenomPos
  have hapos : 0 < bound / (2 * bound - maximizer) := div_pos hBound hdenomPos
  have hbpos : 0 < (bound - maximizer) / (2 * bound - maximizer) :=
    div_pos (by linarith) hdenomPos
  have hab : bound / (2 * bound - maximizer) +
      (bound - maximizer) / (2 * bound - maximizer) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hdne]
    ring
  have hcombo : bound / (2 * bound - maximizer) * maximizer +
      (bound - maximizer) / (2 * bound - maximizer) * (2 * bound) = bound := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hdne]
    ring
  have hne : maximizer ≠ 2 * bound := by linarith
  have hconv := hConcave.2 hmaxMem hdoubleMem hne hapos hbpos hab
  simp only [smul_eq_mul, hcombo] at hconv
  have hsum : bound / (2 * bound - maximizer) * f bound +
      (bound - maximizer) / (2 * bound - maximizer) * f bound = f bound := by
    rw [← add_mul, hab, one_mul]
  have hleft := mul_le_mul_of_nonneg_left hfbound hapos.le
  have hright := mul_lt_mul_of_pos_left hRise hbpos
  linarith [hconv, hsum, hleft, hright]

/-- One agent's racing burden is bounded by the linear and quadratic
aggregates. -/
theorem agentRacingBurden_le_aggregates
    {slotWeight premium entryCost capacity cap : ℝ}
    (hWeight : 0 ≤ slotWeight) (hPremium : 0 ≤ premium)
    (hEntryCost : 0 ≤ entryCost) (hCapacity : 0 < capacity)
    (hCap : 0 ≤ cap) :
    agentRacingBurden slotWeight premium entryCost capacity cap ≤
      slotWeight * (capacity * premium) * cap +
        3 / 2 * (capacity * premium ^ 2) * cap ^ 2 := by
  have hCapNe : capacity ≠ 0 := ne_of_gt hCapacity
  rw [agentRacingBurden_factored hCapNe]
  set m := max (premium * cap - entryCost) 0 with hm
  have hmNonneg : 0 ≤ m := le_max_right _ _
  have hmLe : m ≤ premium * cap := by
    refine max_le ?_ (by positivity)
    linarith
  rcases eq_or_lt_of_le hmNonneg with hzero | hpos
  · rw [← hzero]
    have : (0 : ℝ) ≤ slotWeight * (capacity * premium) * cap +
        3 / 2 * (capacity * premium ^ 2) * cap ^ 2 := by positivity
    simpa using this
  · have hactive : entryCost ≤ premium * cap := by
      by_contra hcontra
      have : m = 0 := max_eq_right (by linarith [not_le.mp hcontra])
      linarith [hpos, this.le]
    have hbracket : entryCost + slotWeight + m / 2 ≤
        slotWeight + 3 / 2 * (premium * cap) := by linarith
    have hstep : m * (entryCost + slotWeight + m / 2) ≤
        (premium * cap) * (slotWeight + 3 / 2 * (premium * cap)) := by
      apply mul_le_mul hmLe hbracket (by linarith) (by positivity)
    nlinarith [hstep, hCapacity]

/-- The racing burden is bounded by the two aggregates the paper sends to
zero. -/
theorem racingBurden_le_aggregates
    {ι : Type*} [Fintype ι]
    {slotWeight cap : ℝ} {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 ≤ slotWeight) (hPremium : ∀ i, 0 ≤ premium i)
    (hEntryCost : ∀ i, 0 ≤ entryCost i) (hCapacity : ∀ i, 0 < capacity i)
    (hCap : 0 ≤ cap) :
    racingBurden slotWeight premium entryCost capacity cap ≤
      slotWeight * (∑ i, capacity i * premium i) * cap +
        3 / 2 * (∑ i, capacity i * premium i ^ 2) * cap ^ 2 := by
  have hterm : ∀ i,
      agentRacingBurden slotWeight (premium i) (entryCost i) (capacity i)
          cap ≤
        slotWeight * (capacity i * premium i) * cap +
          3 / 2 * (capacity i * premium i ^ 2) * cap ^ 2 := fun i =>
    agentRacingBurden_le_aggregates hWeight (hPremium i) (hEntryCost i)
      (hCapacity i) hCap
  calc
    racingBurden slotWeight premium entryCost capacity cap ≤
        ∑ i, (slotWeight * (capacity i * premium i) * cap +
          3 / 2 * (capacity i * premium i ^ 2) * cap ^ 2) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = slotWeight * (∑ i, capacity i * premium i) * cap +
          3 / 2 * (∑ i, capacity i * premium i ^ 2) * cap ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The divergence clause of `prop:optcert` (iv).**  Fix the prize and a
target cap level.  Once the linear and quadratic racing aggregates are small
enough that the burden at twice the target falls below an eighth of the prize
over the target, the optimal published cap exceeds the target. -/
theorem maximizer_gt_of_racingBurden_small
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight bound maximizer : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (hWeight : 0 < slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hBound : 0 < bound) (hMaximizer : 0 < maximizer)
    (hMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premium entryCost
        capacity) (Set.Ioi 0) maximizer)
    (hSmall : racingBurden slotWeight premium entryCost capacity (2 * bound) <
      slotWeight ^ 2 / (8 * bound)) :
    bound < maximizer := by
  refine lt_isMaxOn_of_lt_double
    (certifiedNetSurplus_strictConcave hWeight hEntryCost hCapacity) hBound
    hMaximizer hMax ?_
  have hburdenNonneg :
      0 ≤ racingBurden slotWeight premium entryCost capacity bound :=
    Finset.sum_nonneg fun i _ =>
      agentRacingBurden_nonneg hWeight.le (hEntryCost i) (hCapacity i)
  have hgap : smoothingConcession slotWeight bound -
      smoothingConcession slotWeight (2 * bound) =
        slotWeight ^ 2 / (8 * bound) := by
    rw [smoothingConcession, smoothingConcession]
    field_simp
    norm_num
  simp only [certifiedNetSurplus]
  linarith [hgap, hSmall, hburdenNonneg]

end

end SmoothingCliff.Racing
