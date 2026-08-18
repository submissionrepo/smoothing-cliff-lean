import SmoothingCliff.Mechanism.CrossAgent
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Revenue identity and bounded-convergence bridge

This file formalizes the exact finite-sum revenue identity in Proposition
`prop:revenue` and the bounded-convergence step used by both temperature
limits.  The remaining model-specific task is to instantiate the convergence
hypotheses with the low- and high-temperature limits of the full top-`K`
Plackett--Luce allocation.
-/

open scoped BigOperators

namespace SmoothingCliff.Mechanism

open Filter MeasureTheory

noncomputable section

/-- Total truthful revenue induced by the reserve-normalized Myerson payment. -/
def totalMyersonRevenue
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve) : ℝ :=
  ∑ i, myersonPayment x b i

/-- Proposition `prop:revenue(i)`: total revenue is the sum of the displayed
bid-times-interim-allocation minus allocation-integral terms. -/
theorem totalMyersonRevenue_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve) :
    totalMyersonRevenue x b =
      ∑ i, ((b i : ℝ) * x b i -
        ∫ z in reserve..(b i : ℝ), allocationCurve x b i z) := by
  unfold totalMyersonRevenue
  apply Finset.sum_congr rfl
  intro i _
  exact myersonPayment_eq_integral x b i

/-- Bounded convergence of an allocation curve passes through the
reserve-normalized Myerson operator.  Endpoint convergence is stated
separately because an almost-everywhere hypothesis on the integration
interval does not control the reported bid itself. -/
theorem myersonCurvePayment_tendsto_of_dominated
    {κ : Type*} {l : Filter κ} [l.IsCountablyGenerated]
    (allocation : κ → ℝ → ℝ) (limit bound : ℝ → ℝ)
    {reserve bid : ℝ}
    (hMeasurable : ∀ᶠ k in l,
      AEStronglyMeasurable (allocation k)
        (volume.restrict (Set.uIoc reserve bid)))
    (hBound : ∀ᶠ k in l, ∀ᵐ z ∂volume,
      z ∈ Set.uIoc reserve bid → ‖allocation k z‖ ≤ bound z)
    (hBoundIntegrable : IntervalIntegrable bound volume reserve bid)
    (hPointwise : ∀ᵐ z ∂volume, z ∈ Set.uIoc reserve bid →
      Tendsto (fun k => allocation k z) l (nhds (limit z)))
    (hEndpoint : Tendsto (fun k => allocation k bid) l
      (nhds (limit bid))) :
    Tendsto
      (fun k => myersonCurvePayment reserve (allocation k) bid) l
      (nhds (myersonCurvePayment reserve limit bid)) := by
  have hIntegral :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      bound hMeasurable hBound hBoundIntegrable hPointwise
  unfold myersonCurvePayment
  exact (hEndpoint.const_mul bid).sub hIntegral

/-- A constant eligible allocation curve charges exactly the reserve times
the allocated priority, independently of the report. -/
theorem myersonCurvePayment_const (reserve bid allocation : ℝ) :
    myersonCurvePayment reserve (fun _ => allocation) bid =
      reserve * allocation := by
  simp [myersonCurvePayment]
  ring

/-- High-temperature endpoint of the bounded-convergence bridge: if an
allocation curve converges to a constant, its payment converges to the reserve
times that constant. -/
theorem myersonCurvePayment_tendsto_const_of_dominated
    {κ : Type*} {l : Filter κ} [l.IsCountablyGenerated]
    (allocation : κ → ℝ → ℝ) (bound : ℝ → ℝ)
    {reserve bid constant : ℝ}
    (hMeasurable : ∀ᶠ k in l,
      AEStronglyMeasurable (allocation k)
        (volume.restrict (Set.uIoc reserve bid)))
    (hBound : ∀ᶠ k in l, ∀ᵐ z ∂volume,
      z ∈ Set.uIoc reserve bid → ‖allocation k z‖ ≤ bound z)
    (hBoundIntegrable : IntervalIntegrable bound volume reserve bid)
    (hPointwise : ∀ᵐ z ∂volume, z ∈ Set.uIoc reserve bid →
      Tendsto (fun k => allocation k z) l (nhds constant))
    (hEndpoint : Tendsto (fun k => allocation k bid) l
      (nhds constant)) :
    Tendsto
      (fun k => myersonCurvePayment reserve (allocation k) bid) l
      (nhds (reserve * constant)) := by
  have h := myersonCurvePayment_tendsto_of_dominated allocation
    (fun _ => constant) bound hMeasurable hBound hBoundIntegrable
      hPointwise hEndpoint
  simpa [myersonCurvePayment_const] using h

/-- Finite-agent aggregation of payment limits.  This is the exact step from
per-agent uniform-lottery limits to `reserve * allocatedMass`. -/
theorem totalPayment_tendsto_reserve_mul_mass
    {ι κ : Type*} [Fintype ι]
    {l : Filter κ} (payment : ι → κ → ℝ)
    (reserve : ℝ) (limitAllocation : ι → ℝ) (allocatedMass : ℝ)
    (hPayment : ∀ i,
      Tendsto (payment i) l (nhds (reserve * limitAllocation i)))
    (hMass : ∑ i, limitAllocation i = allocatedMass) :
    Tendsto (fun k => ∑ i, payment i k) l
      (nhds (reserve * allocatedMass)) := by
  have hSum := tendsto_finsetSum Finset.univ
    (fun i _ => hPayment i)
  have hLimit : ∑ i, reserve * limitAllocation i =
      reserve * allocatedMass := by
    rw [← Finset.mul_sum, hMass]
  simpa [hLimit] using hSum

/-- At the exact uniform-allocation endpoint, total Myerson revenue is the
reserve times total allocated priority mass. -/
theorem uniformAllocation_totalRevenue_eq
    {ι : Type*} [Fintype ι]
    (reserve : ℝ) (bid allocation : ι → ℝ) (allocatedMass : ℝ)
    (hMass : ∑ i, allocation i = allocatedMass) :
    ∑ i, myersonCurvePayment reserve (fun _ => allocation i) (bid i) =
      reserve * allocatedMass := by
  calc
    ∑ i, myersonCurvePayment reserve (fun _ => allocation i) (bid i) =
        ∑ i, reserve * allocation i := by
      apply Finset.sum_congr rfl
      intro i _
      exact myersonCurvePayment_const reserve (bid i) (allocation i)
    _ = reserve * ∑ i, allocation i := by rw [Finset.mul_sum]
    _ = reserve * allocatedMass := by rw [hMass]

end

end SmoothingCliff.Mechanism
