import SmoothingCliff.Racing.RaceEquilibrium

/-!
# The racing game with a genuine profile argument

The racing development of `Spread.lean` and `RentDissipation.lean` holds the
opponents fixed inside a response function `allocation : ℝ → ℝ`, which is what
makes every best-response statement uniform over opponents.  The existence
result of `RaceEquilibrium.lean` instead takes a payoff defined on a genuine
profile.  This file connects the two, completing clause (ii) of Proposition
`prop:rentdissipation`.

The response family is indexed by the whole action profile and required to
ignore the own coordinate, which is what makes the payoff concave in the own
action: changing `a_i` moves the argument of the allocation but not the
allocation itself.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

variable {ι : Type} [Fintype ι] [Inhabited ι] [DecidableEq ι]

/-- The racing payoff as a function of the whole action profile. -/
def raceProfilePayoff
    (response : ι → ((j : ι) → ℝ) → ℝ → ℝ) (cost : ι → ℝ → ℝ)
    (reserve : ℝ) (value upper : ι → ℝ)
    (i : ι) (σ : (j : ι) → ↑(raceSlice (upper j))) : ℝ :=
  advantageUtility (response i fun j => (σ j : ℝ)) (cost i) reserve (value i)
    (σ i)

/-- A response family that ignores the own coordinate. -/
def OwnBlind (response : ι → ((j : ι) → ℝ) → ℝ → ℝ) : Prop :=
  ∀ (i : ι) (first second : (j : ι) → ℝ),
    (∀ j, j ≠ i → first j = second j) → response i first = response i second

omit [Fintype ι] [Inhabited ι] in
/-- Under the certificate and the curvature condition the racing payoff is
concave in the own action, with the ambient representative required by the
existence result. -/
theorem raceProfilePayoff_concave_in_own
    {response : ι → ((j : ι) → ℝ) → ℝ → ℝ} {cost : ι → ℝ → ℝ}
    {reserve : ℝ} {value upper : ι → ℝ} {sensitivity : NNReal} {curvature : ℝ}
    (hBlind : OwnBlind response)
    (hMono : ∀ i a, Monotone (response i a))
    (hLip : ∀ i a, LipschitzWith sensitivity (response i a))
    (hCostDiff : ∀ i a, DifferentiableAt ℝ (cost i) a)
    (hCurvature : (sensitivity : ℝ) < curvature)
    (hCost : ∀ (i : ι) (first second : ℝ), first ≤ second →
      curvature * (second - first) ≤
        deriv (cost i) second - deriv (cost i) first)
    (i : ι) (σ : (j : ι) → ↑(raceSlice (upper j))) :
    ∃ g : ℝ → ℝ, ConcaveOn ℝ (raceSlice (upper i)) g ∧
      ∀ y : ↑(raceSlice (upper i)),
        g y.1 =
          raceProfilePayoff response cost reserve value upper i
            (Function.update σ i y) := by
  classical
  set allocation := response i fun j => (σ j : ℝ) with hallocation
  refine ⟨advantageUtility allocation (cost i) reserve (value i), ?_, ?_⟩
  · have hderiv : ∀ a : ℝ,
        HasDerivAt (advantageUtility allocation (cost i) reserve (value i))
          (allocation (value i + a) - allocation (reserve + a) -
            deriv (cost i) a) a := fun a =>
      advantageUtility_hasDerivAt allocation (cost i)
        (hLip i _).continuous (hCostDiff i a).hasDerivAt
    have hderivEq :
        deriv (advantageUtility allocation (cost i) reserve (value i)) =
          fun a => allocation (value i + a) - allocation (reserve + a) -
            deriv (cost i) a := by
      funext a
      exact (hderiv a).deriv
    have hcont : Continuous
        (advantageUtility allocation (cost i) reserve (value i)) :=
      continuous_iff_continuousAt.mpr fun a =>
        (hderiv a).differentiableAt.continuousAt
    have hanti : StrictAnti
        (deriv (advantageUtility allocation (cost i) reserve (value i))) := by
      rw [hderivEq]
      exact advantageUtility_marginal_strictAnti allocation (cost i) sensitivity
        (hMono i _) (hLip i _) hCurvature (hCost i) reserve (value i)
    exact ((hanti.strictConcaveOn_univ_of_deriv hcont).concaveOn).subset
      (Set.subset_univ _) (raceSlice_convex (upper i))
  · intro y
    have hsame : (response i fun j => ((Function.update σ i y) j : ℝ)) =
        allocation := by
      rw [hallocation]
      refine hBlind i _ _ ?_
      intro j hj
      simp [Function.update_of_ne hj]
    rw [raceProfilePayoff, hsame]
    simp [Function.update_self]

/-- **Proposition `prop:rentdissipation` (ii).**  Under the certificate and the
curvature condition, the race on a compact action box has a pure-strategy Nash
equilibrium. -/
theorem exists_raceProfile_equilibrium
    {response : ι → ((j : ι) → ℝ) → ℝ → ℝ} {cost : ι → ℝ → ℝ}
    {reserve : ℝ} {value upper : ι → ℝ} {sensitivity : NNReal} {curvature : ℝ}
    (hUpper : ∀ i, 0 ≤ upper i)
    (hBlind : OwnBlind response)
    (hMono : ∀ i a, Monotone (response i a))
    (hLip : ∀ i a, LipschitzWith sensitivity (response i a))
    (hCostDiff : ∀ i a, DifferentiableAt ℝ (cost i) a)
    (hCurvature : (sensitivity : ℝ) < curvature)
    (hCost : ∀ (i : ι) (first second : ℝ), first ≤ second →
      curvature * (second - first) ≤
        deriv (cost i) second - deriv (cost i) first)
    (hCont : ∀ i,
      Continuous (raceProfilePayoff response cost reserve value upper i)) :
    ∃ σ : (raceGameData upper hUpper
        (raceProfilePayoff response cost reserve value upper) hCont
        (raceProfilePayoff_concave_in_own hBlind hMono hLip hCostDiff
          hCurvature hCost)).Profile,
      (raceGameData upper hUpper
        (raceProfilePayoff response cost reserve value upper) hCont
        (raceProfilePayoff_concave_in_own hBlind hMono hLip hCostDiff
          hCurvature hCost)).toEquilibriumProblem.IsEquilibrium σ :=
  exists_race_equilibrium upper hUpper _ hCont _

end

end SmoothingCliff.Racing
