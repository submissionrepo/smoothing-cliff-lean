import SmoothingCliff.Mechanism.LuceOptimality
import SmoothingCliff.Racing.PLLogPremium

/-!
# The logarithmic premium binds the whole capped Luce class (`cor:luceclass`)

Composition of Proposition `prop:luceopt` (`exponential_oneSlot_welfare_optimal`)
with the matched lower-bound witness of Theorem `thm:pos(iii)`
(`matched_tiedLogTrailers_PLWelfare_premium_eq`): every sequential Luce rule
whose intensity satisfies the log-derivative cap `(log α)' ≤ 1/τ` at the
matched one-slot certificate `τ = w₁/(4𝒮)` loses at least
`w₁² log(n-1)/(8𝒮)` at the one-leader log-trailer profile, so the `Θ(log n)`
premium is the price of the Luce class, not of exponential scores.

The equivalence half of `cor:luceclass`, cap `𝒮` iff `(log α)' ≤ 4𝒮/w₁`,
is the derivative computation recorded in
`SmoothingCliff.Mechanism.OneSlotStability` (`hasDerivAt_oneSlotLuceProbability`
with `oneSlotLuceProbability_balanced` and `quadratic_variance_le_quarter`);
this file certifies the premium half.
-/

open scoped BigOperators

namespace SmoothingCliff.LuceOptimality

open SmoothingCliff Racing

/-- Reserve-normalized exponential Luce welfare equals the PL welfare with
scores `value / τ`: the reserve factor cancels from every choice ratio. -/
theorem oneSlotLuceWelfare_exponential_eq_PL
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reserve τ weight : ℝ) (v : ι → ℝ) :
    oneSlotLuceWelfare weight v
        (fun i => exponentialIntensity reserve τ (v i)) =
      oneSlotPLWelfare (Finset.univ : Finset ι) v τ weight := by
  have hc : Real.exp (-(reserve / τ)) ≠ 0 := Real.exp_ne_zero _
  unfold oneSlotLuceWelfare oneSlotPLWelfare oneSlotPLProbability
    exponentialIntensity
  have hexp : ∀ i : ι, Real.exp ((v i - reserve) / τ) =
      Real.exp (v i / τ) * Real.exp (-(reserve / τ)) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hexp]
  congr 1
  have hnum : (∑ i : ι,
        Real.exp (v i / τ) * Real.exp (-(reserve / τ)) * v i) =
      (∑ i : ι, v i * Real.exp (v i / τ)) * Real.exp (-(reserve / τ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hden : (∑ i : ι, Real.exp (v i / τ) * Real.exp (-(reserve / τ))) =
      (∑ i : ι, Real.exp (v i / τ)) * Real.exp (-(reserve / τ)) := by
    rw [Finset.sum_mul]
  rw [hnum, hden, mul_div_mul_right _ _ hc]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]

/-- `cor:luceclass`, premium half: at the matched certificate, every
`EligibleC1Intensity` sequential Luce rule loses at least
`w₁² log(n-1)/(8𝒮)` at the one-leader log-trailer witness profile. -/
theorem luceClass_matched_log_premium
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reserve base weight sensitivity : ℝ) (α dα : ℝ → ℝ)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hI : EligibleC1Intensity reserve
      (matchedPLTemperature weight sensitivity) α dα)
    (helig : ∀ o : Option ι, reserve ≤
      oneLeaderPLValue base (matchedPLTemperature weight sensitivity)
        (fun _ : ι => Real.log (Fintype.card ι : ℝ)) o) :
    weight ^ 2 * Real.log (Fintype.card ι : ℝ) / (8 * sensitivity) ≤
      weight * base -
        oneSlotLuceWelfare weight
          (oneLeaderPLValue base (matchedPLTemperature weight sensitivity)
            (fun _ : ι => Real.log (Fintype.card ι : ℝ)))
          (fun o => α (oneLeaderPLValue base
            (matchedPLTemperature weight sensitivity)
            (fun _ : ι => Real.log (Fintype.card ι : ℝ)) o)) := by
  have htau : 0 < matchedPLTemperature weight sensitivity := by
    unfold matchedPLTemperature
    positivity
  set τ := matchedPLTemperature weight sensitivity with hτ
  set v : Option ι → ℝ :=
    oneLeaderPLValue base τ (fun _ : ι => Real.log (Fintype.card ι : ℝ))
    with hv
  have hopt :
      oneSlotLuceWelfare weight v (fun o => α (v o)) ≤
        oneSlotLuceWelfare weight v
          (fun o => exponentialIntensity reserve τ (v o)) :=
    exponential_oneSlot_welfare_optimal reserve τ weight v α dα htau
      hweight.le helig hI
  have hbridge :
      oneSlotLuceWelfare weight v
          (fun o => exponentialIntensity reserve τ (v o)) =
        oneSlotPLWelfare (Finset.univ : Finset (Option ι)) v τ weight :=
    oneSlotLuceWelfare_exponential_eq_PL reserve τ weight v
  have hprem :
      weight * base -
          oneLeaderPLWelfare base τ weight
            (fun _ : ι => Real.log (Fintype.card ι : ℝ)) =
        weight ^ 2 * Real.log (Fintype.card ι : ℝ) / (8 * sensitivity) := by
    simpa [hτ] using
      matched_tiedLogTrailers_PLWelfare_premium_eq (ι := ι)
        base weight sensitivity hweight hsens
  have hPLdef :
      oneLeaderPLWelfare base τ weight
          (fun _ : ι => Real.log (Fintype.card ι : ℝ)) =
        oneSlotPLWelfare (Finset.univ : Finset (Option ι)) v τ weight := rfl
  linarith [hopt, hbridge.ge, hbridge.le]

end SmoothingCliff.LuceOptimality
