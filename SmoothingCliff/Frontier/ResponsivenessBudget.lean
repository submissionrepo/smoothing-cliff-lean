import SmoothingCliff.Frontier.WaterFilling
import SmoothingCliff.Racing.RentDissipation
import SmoothingCliff.Racing.OptimalCap

/-!
# The no-race responsiveness budget

This file formalizes Proposition `prop:responsiveness-budget`.  The proof has
two logically separate parts.  A zero action at the boundary of the investment
set makes the marginal allocation spread no larger than marginal cost.  Then
cross-monotonicity lowers every opponent to the reserve, anonymity identifies
the equal-share allocation at that profile, and feasibility gives the cap
`w₁ / n + κ`.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff
open SmoothingCliff.Racing

noncomputable section

/-- A profile in which bidder `i` remains at the reserve and precisely the
opponents in `S` are raised to their bids in `b`. -/
def opponentsRaisedProfile
    {ι : Type*} [DecidableEq ι] {reserve : ℝ}
    (b : EligibleProfile ι reserve) (i : ι) (S : Finset ι) :
    EligibleProfile ι reserve :=
  fun j => if j = i then
    ⟨reserve, Set.mem_Ici.mpr le_rfl⟩
  else if j ∈ S then b j else ⟨reserve, Set.mem_Ici.mpr le_rfl⟩

@[simp] theorem opponentsRaisedProfile_empty
    {ι : Type*} [DecidableEq ι] {reserve : ℝ}
    (b : EligibleProfile ι reserve) (i : ι) :
    opponentsRaisedProfile b i ∅ = tiedEligibleProfile reserve := by
  funext j
  apply Subtype.ext
  simp [opponentsRaisedProfile, tiedEligibleProfile]

@[simp] theorem opponentsRaisedProfile_univ_erase
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (b : EligibleProfile ι reserve) (i : ι) :
    opponentsRaisedProfile b i ((Finset.univ : Finset ι).erase i) =
      updateBid b i ⟨reserve, Set.mem_Ici.mpr le_rfl⟩ := by
  funext j
  apply Subtype.ext
  by_cases hji : j = i
  · subst j
    simp [opponentsRaisedProfile, updateBid]
  · simp [opponentsRaisedProfile, updateBid, hji]

/-- Raising any finite collection of opponents from the reserve can only
lower bidder `i`'s allocation under cross-monotonicity. -/
theorem opponentsRaisedProfile_allocation_le_tie
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve) (hCross : CrossMonotone x)
    (b : EligibleProfile ι reserve) (i : ι) (S : Finset ι)
    (hiS : i ∉ S) :
    x (opponentsRaisedProfile b i S) i ≤
      x (tiedEligibleProfile reserve) i := by
  induction S using Finset.induction_on with
  | empty =>
      rw [opponentsRaisedProfile_empty]
  | @insert j S hjS ih =>
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hiS (Finset.mem_insert_self i S)
      have hji : j ≠ i := Ne.symm hij
      have hiS' : i ∉ S := by
        intro hi
        exact hiS (Finset.mem_insert_of_mem hi)
      have hstep := hCross (opponentsRaisedProfile b i S) i j hij
        (show (⟨reserve, Set.mem_Ici.mpr le_rfl⟩ : EligibleBid reserve) ≤ b j
          from (b j).2)
      have hRaised :
          updateBid (opponentsRaisedProfile b i S) j (b j) =
            opponentsRaisedProfile b i (insert j S) := by
        funext k
        apply Subtype.ext
        by_cases hki : k = i
        · subst k
          simp [opponentsRaisedProfile, updateBid, hij]
        · by_cases hkj : k = j
          · subst k
            simp [opponentsRaisedProfile, updateBid, hji]
          · simp [opponentsRaisedProfile, updateBid, hki, hkj]
      have hBase :
          updateBid (opponentsRaisedProfile b i S) j
              (⟨reserve, Set.mem_Ici.mpr le_rfl⟩ : EligibleBid reserve) =
            opponentsRaisedProfile b i S := by
        funext k
        apply Subtype.ext
        by_cases hkj : k = j
        · subst k
          simp [opponentsRaisedProfile, updateBid, hji, hjS]
        · simp [updateBid, hkj]
      change
        x (updateBid (opponentsRaisedProfile b i S) j (b j)) i ≤
          x (updateBid (opponentsRaisedProfile b i S) j
            (⟨reserve, Set.mem_Ici.mpr le_rfl⟩ : EligibleBid reserve)) i
        at hstep
      rw [hRaised, hBase] at hstep
      exact hstep.trans (ih hiS')

/-- At an anonymous all-reserve profile, feasibility caps every bidder by the
equal share of the slot. -/
theorem anonymous_tie_allocation_le_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reserve weight : ℝ}
    (x : InterimRule ι reserve) (hAnon : Anonymous x)
    (hFeasible : OneSlotFeasible weight x) (i : ι) :
    x (tiedEligibleProfile reserve) i ≤
      weight / (Fintype.card ι : ℝ) := by
  let b : EligibleProfile ι reserve := tiedEligibleProfile reserve
  have hall : ∀ j, x b j = x b i := by
    intro j
    apply allocation_eq_of_bid_eq x hAnon b j i
    rfl
  have hsum : ∑ j, x b j ≤ weight := hFeasible.2 b
  have hsumEq : ∑ j, x b j = (Fintype.card ι : ℝ) * x b i := by
    calc
      (∑ j, x b j) = ∑ _j : ι, x b i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hall j
      _ = (Fintype.card ι : ℝ) * x b i := by simp
  rw [hsumEq] at hsum
  have hcard : (0 : ℝ) < Fintype.card ι := by positivity
  apply (le_div_iff₀ hcard).2
  simpa [mul_comm] using hsum

/-- The boundary first-order condition.  If zero is a best response and the
latency cost is `κa`, then the gross allocation gain from the truthful value
over the reserve is at most `κ`. -/
theorem zeroBestResponse_allocationSpread_le
    (allocation : ℝ → ℝ) (hAllocation : Continuous allocation)
    {reserve value kappa : ℝ}
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation (fun a => kappa * a) reserve value) 0) :
    allocation value - allocation reserve ≤ kappa := by
  have hCost : HasDerivAt (fun a : ℝ => kappa * a) kappa 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul kappa
  have hDerivative := advantageUtility_hasDerivAt allocation
    (fun a => kappa * a) hAllocation (reserve := reserve) (value := value)
      (advantage := 0) (marginalCost := kappa) hCost
  have hNonpos := rightDerivative_nonpos_of_localMax
    hBest.2.localize hDerivative.hasDerivWithinAt
  simpa using hNonpos

/-- Proposition `prop:responsiveness-budget`.  The family `slice b i`
represents bidder `i`'s allocation as her effective input varies while the
opponents in `b` are fixed. -/
theorem noRace_responsiveness_budget
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reserve weight kappa : ℝ}
    (x : InterimRule ι reserve)
    (slice : EligibleProfile ι reserve → ι → ℝ → ℝ)
    (hSliceContinuous : ∀ b i, Continuous (slice b i))
    (hSliceValue : ∀ b i, slice b i (b i) = x b i)
    (hSliceReserve : ∀ b i,
      slice b i reserve =
        x (updateBid b i ⟨reserve, Set.mem_Ici.mpr le_rfl⟩) i)
    (hZeroBest : ∀ b i, NonnegativeBestResponse
      (advantageUtility (slice b i) (fun a => kappa * a)
        reserve (b i)) 0)
    (hAnon : Anonymous x) (hCross : CrossMonotone x)
    (hFeasible : OneSlotFeasible weight x) :
    ∀ b i,
      x b i -
          x (updateBid b i ⟨reserve, Set.mem_Ici.mpr le_rfl⟩) i ≤ kappa ∧
      x b i ≤ weight / (Fintype.card ι : ℝ) + kappa := by
  intro b i
  have hSpread := zeroBestResponse_allocationSpread_le
    (slice b i) (hSliceContinuous b i) (hZeroBest b i)
  rw [hSliceValue b i, hSliceReserve b i] at hSpread
  have hCrossBase :
      x (updateBid b i ⟨reserve, Set.mem_Ici.mpr le_rfl⟩) i ≤
        x (tiedEligibleProfile reserve) i := by
    rw [← opponentsRaisedProfile_univ_erase b i]
    exact opponentsRaisedProfile_allocation_le_tie x hCross b i
      ((Finset.univ : Finset ι).erase i) (by simp)
  have hTie := anonymous_tie_allocation_le_card x hAnon hFeasible i
  constructor
  · exact hSpread
  · linarith

end

end SmoothingCliff.Frontier
