import SmoothingCliff.Racing.OptimalCap
import SmoothingCliff.Racing.RentDissipation

/-!
# The guarantee clause and a comparative static for the published cap

Formal targets: clauses (i) and (iv) of Proposition `prop:optcert` in
`Smoothing_the_Cliff_ITCS.tex`.  `OptimalCap.lean` carries the analytic core,
clauses (ii) and (iii); this file adds the two clauses that connect the
objective to the race.

Clause (i) has two steps.  Under linear-quadratic costs the spread cap bounds
every best response by the paper's `a_i^S`, and net surplus at any such profile
is at least the certified objective.  Both steps are stated over an arbitrary
monotone `S`-Lipschitz response function, so they apply to the water-filling
rule of `thm:pos` (ii).

Clause (iv) is an ordinal comparative static: the certified objective changes
by a monotone amount in the cap when racing capacity rises, so its maximizer
falls.  The argument is the standard single-crossing one and needs no
derivative.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-! ### Clause (i): the published investment bound and the guarantee -/

theorem linearQuadraticCost_hasDerivAt
    {entryCost capacity : ℝ} (hCapacity : 0 < capacity) (investment : ℝ) :
    HasDerivAt (linearQuadraticCost entryCost capacity)
      (entryCost + investment / capacity) investment := by
  have hsq : HasDerivAt (fun a : ℝ => a ^ 2 / (2 * capacity))
      (2 * investment / (2 * capacity)) investment := by
    simpa using ((hasDerivAt_pow 2 investment).div_const (2 * capacity))
  have hlin : HasDerivAt (fun a : ℝ => entryCost * a) entryCost investment := by
    simpa using (hasDerivAt_id investment).const_mul entryCost
  have := hlin.add hsq
  convert this using 1
  field_simp

/-- Every nonnegative best response under linear-quadratic costs is bounded by
the paper's published investment bound `a_i^S = γ ((v-r) S - χ)^+`. -/
theorem linearQuadratic_bestResponse_le_investmentUpperBound
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value entryCost capacity action : ℝ}
    (hValue : reserve ≤ value) (hCapacity : 0 < capacity)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation (linearQuadraticCost entryCost capacity)
        reserve value) action) :
    action ≤ investmentUpperBound (value - reserve) entryCost capacity
      (sensitivity : ℝ) := by
  rcases eq_or_lt_of_le hBest.1 with hZero | hPositive
  · rw [← hZero]
    exact mul_nonneg hCapacity.le (le_max_right _ _)
  · have hMarginalCost := positive_bestResponse_marginalCost_le
      allocation (linearQuadraticCost entryCost capacity) weight sensitivity
      hMono hRange hLip hValue hPositive
      (linearQuadraticCost_hasDerivAt hCapacity action).differentiableAt hBest
    rw [(linearQuadraticCost_hasDerivAt hCapacity action).deriv]
      at hMarginalCost
    have hSlack : action / capacity ≤
        (value - reserve) * (sensitivity : ℝ) - entryCost := by linarith
    have hScaled : action ≤
        capacity * ((value - reserve) * (sensitivity : ℝ) - entryCost) := by
      rw [div_le_iff₀ hCapacity] at hSlack
      linarith
    refine hScaled.trans ?_
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hCapacity.le

/-- Clause (i) of `prop:optcert`.  At any investment profile whose per-agent
burden is bounded by the published one, net surplus is at least the certified
objective.  The water-filling worst-case bound of `thm:pos` (ii) enters as
`hWaterFilling` and the effective-input welfare comparison as `hWelfare`. -/
theorem certifiedNetSurplus_guarantee
    {ι : Type*} [Fintype ι]
    {slotWeight cap welfareAtValues welfareAtInputs : ℝ}
    {premium entryCost capacity : ι → ℝ}
    (value action exposure : ι → ℝ) (cost : ι → ℝ → ℝ)
    (hWelfare : welfareAtValues ≤ welfareAtInputs)
    (hWaterFilling :
      welfareAtInputs - ∑ i, (value i + action i) * exposure i ≤
        smoothingConcession slotWeight cap)
    (hExposureLe : ∀ i, exposure i ≤ slotWeight)
    (hActionNonneg : ∀ i, 0 ≤ action i)
    (hBurden : ∑ i, (slotWeight * action i + cost i (action i)) ≤
      racingBurden slotWeight premium entryCost capacity cap) :
    certifiedNetSurplus welfareAtValues slotWeight premium entryCost capacity
        cap ≤
      (∑ i, value i * exposure i) - ∑ i, cost i (action i) := by
  have hTilt : ∑ i, action i * exposure i ≤ ∑ i, slotWeight * action i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hExposureLe i) (hActionNonneg i)
    linarith [this]
  have hsplit : ∑ i, (value i + action i) * exposure i =
      (∑ i, value i * exposure i) + ∑ i, action i * exposure i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcombine : ∑ i, (slotWeight * action i + cost i (action i)) =
      (∑ i, slotWeight * action i) + ∑ i, cost i (action i) := by
    rw [← Finset.sum_add_distrib]
  rw [certifiedNetSurplus]
  rw [hsplit] at hWaterFilling
  rw [hcombine] at hBurden
  linarith

/-! ### Clause (iv): the maximizer falls as racing capacity rises -/

/-- Single crossing: if the second objective exceeds the first by an amount
that is antitone in the argument, its maximizer is no larger.  Uniqueness of
the first maximizer is what rules out the tie. -/
theorem isMaxOn_le_of_antitone_difference
    {f g : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}
    (hx : IsMaxOn f s x) (hy : IsMaxOn g s y) (hxs : x ∈ s) (hys : y ∈ s)
    (hDifference : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → g b - f b ≤ g a - f a)
    (hUnique : ∀ z ∈ s, IsMaxOn f s z → z = x) :
    y ≤ x := by
  by_contra hNot
  have hlt : x < y := lt_of_not_ge hNot
  have hfx : f y ≤ f x := hx hys
  have hgy : g x ≤ g y := hy hxs
  have hdiff := hDifference x hxs y hys hlt.le
  have hEqual : f y = f x := by linarith
  have hyMax : IsMaxOn f s y := by
    intro z hz
    have := hx hz
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [hEqual]
    exact this
  exact absurd (hUnique y hys hyMax) (ne_of_gt hlt)

/-- Factored form of one agent's racing burden: `γ m (χ + w + m/2)` with
`m = ((v-r) S - χ)^+`. -/
theorem agentRacingBurden_factored
    {slotWeight premium entryCost capacity cap : ℝ} (hCapacity : capacity ≠ 0) :
    agentRacingBurden slotWeight premium entryCost capacity cap =
      capacity * (max (premium * cap - entryCost) 0 *
        (entryCost + slotWeight + max (premium * cap - entryCost) 0 / 2)) := by
  rw [agentRacingBurden, linearQuadraticCost, investmentUpperBound]
  field_simp
  ring

/-- The bracket `m (χ + w + m/2)` is monotone in `m` on the nonnegatives. -/
theorem burdenBracket_mono
    {entryCost slotWeight m m' : ℝ}
    (hEntryCost : 0 ≤ entryCost) (hWeight : 0 ≤ slotWeight)
    (hm : 0 ≤ m) (hmm : m ≤ m') :
    m * (entryCost + slotWeight + m / 2) ≤
      m' * (entryCost + slotWeight + m' / 2) := by
  nlinarith

/-- Raising one agent's racing capacity changes the burden by an amount that is
monotone in the cap. -/
theorem agentRacingBurden_difference_monotone_in_capacity
    {slotWeight premium entryCost capacityLow capacityHigh : ℝ}
    (hWeight : 0 ≤ slotWeight) (hEntryCost : 0 ≤ entryCost)
    (hPremium : 0 ≤ premium)
    (hLow : 0 < capacityLow) (hHigh : capacityLow ≤ capacityHigh) :
    Monotone fun cap =>
      agentRacingBurden slotWeight premium entryCost capacityHigh cap -
        agentRacingBurden slotWeight premium entryCost capacityLow cap := by
  intro cap cap' hcap
  have hHighNe : capacityHigh ≠ 0 := by
    have : 0 < capacityHigh := lt_of_lt_of_le hLow hHigh
    exact ne_of_gt this
  have hLowNe : capacityLow ≠ 0 := ne_of_gt hLow
  simp only [agentRacingBurden_factored hHighNe,
    agentRacingBurden_factored hLowNe]
  set m := max (premium * cap - entryCost) 0 with hm
  set m' := max (premium * cap' - entryCost) 0 with hm'
  have hmNonneg : 0 ≤ m := le_max_right _ _
  have hmle : m ≤ m' := by
    refine max_le_max ?_ le_rfl
    have := mul_le_mul_of_nonneg_left hcap hPremium
    linarith
  have hbracket := burdenBracket_mono (entryCost := entryCost)
    (slotWeight := slotWeight) hEntryCost hWeight hmNonneg hmle
  have hgap : 0 ≤ capacityHigh - capacityLow := by linarith
  nlinarith [hbracket, hgap]

/-- Clause (iv) of `prop:optcert`, capacity direction.  Raising every agent's
racing capacity moves the certified objective by an amount monotone in the cap,
hence weakly lowers the optimal published cap. -/
theorem certifiedNetSurplus_maximizer_antitone_in_capacity
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight : ℝ}
    {premium entryCost capacityLow capacityHigh : ι → ℝ}
    {capLow capHigh : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hLow : ∀ i, 0 < capacityLow i)
    (hOrder : ∀ i, capacityLow i ≤ capacityHigh i)
    (hLowMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premium entryCost
        capacityLow) (Set.Ioi 0) capLow)
    (hHighMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premium entryCost
        capacityHigh) (Set.Ioi 0) capHigh)
    (hLowMem : capLow ∈ Set.Ioi (0 : ℝ)) (hHighMem : capHigh ∈ Set.Ioi (0 : ℝ))
    (hLowUnique : ∀ z ∈ Set.Ioi (0 : ℝ),
      IsMaxOn (certifiedNetSurplus strictPriorityWelfare slotWeight premium
        entryCost capacityLow) (Set.Ioi 0) z → z = capLow) :
    capHigh ≤ capLow := by
  refine isMaxOn_le_of_antitone_difference hLowMax hHighMax hLowMem hHighMem
    ?_ hLowUnique
  intro a _ b _ hab
  set term : ι → ℝ → ℝ := fun i cap =>
    agentRacingBurden slotWeight (premium i) (entryCost i) (capacityHigh i)
        cap -
      agentRacingBurden slotWeight (premium i) (entryCost i) (capacityLow i)
        cap with hterm
  have hburden : ∀ i, term i a ≤ term i b := fun i =>
    agentRacingBurden_difference_monotone_in_capacity hWeight (hEntryCost i)
      (hPremium i) (hLow i) (hOrder i) hab
  have hsum : ∑ i, term i a ≤ ∑ i, term i b :=
    Finset.sum_le_sum fun i _ => hburden i
  simp only [hterm] at hsum
  simp only [certifiedNetSurplus, racingBurden]
  have hexpand : ∀ cap : ℝ,
      (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premium i) (entryCost i)
            (capacityHigh i) cap) -
        (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premium i) (entryCost i)
            (capacityLow i) cap) =
      -∑ i, (agentRacingBurden slotWeight (premium i) (entryCost i)
          (capacityHigh i) cap -
        agentRacingBurden slotWeight (premium i) (entryCost i)
          (capacityLow i) cap) := by
    intro cap
    rw [Finset.sum_sub_distrib]
    ring
  rw [hexpand a, hexpand b]
  linarith

end

end SmoothingCliff.Racing
