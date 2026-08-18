import SmoothingCliff.Racing.RentDissipation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A coercivity counterexample for the generic dissipation bound

The paper defines a real action bound as the supremum of a marginal-cost
sublevel set under assumptions of strict increase, strict convexity, and
differentiability.  Those assumptions do not imply that the sublevel set is
bounded.  This file gives an explicit smooth counterexample.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- A normalized, strictly increasing and strictly convex cost whose marginal
cost converges upward to one. -/
def asymptoticallyLinearCost (a : ℝ) : ℝ :=
  a + Real.exp (-a) - 1

def asymptoticallyLinearMarginalCost (a : ℝ) : ℝ :=
  1 - Real.exp (-a)

theorem asymptoticallyLinearCost_hasDerivAt (a : ℝ) :
    HasDerivAt asymptoticallyLinearCost
      (asymptoticallyLinearMarginalCost a) a := by
  change HasDerivAt (fun x : ℝ => x + Real.exp (-x) - 1)
    (1 - Real.exp (-a)) a
  convert (((hasDerivAt_id a).add (hasDerivAt_neg a).exp).sub_const 1) using 1
  ring

theorem asymptoticallyLinearMarginalCost_strictMono :
    StrictMono asymptoticallyLinearMarginalCost := by
  intro a b hab
  have hexp : Real.exp (-b) < Real.exp (-a) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hab)
  dsimp [asymptoticallyLinearMarginalCost]
  linarith

theorem asymptoticallyLinearCost_continuous :
    Continuous asymptoticallyLinearCost := by
  change Continuous (fun a : ℝ => a + Real.exp (-a) - 1)
  fun_prop

theorem asymptoticallyLinearCost_strictConvex :
    StrictConvexOn ℝ (Set.Ici 0) asymptoticallyLinearCost := by
  have hderiv :
      deriv asymptoticallyLinearCost =
        asymptoticallyLinearMarginalCost := by
    funext a
    exact (asymptoticallyLinearCost_hasDerivAt a).deriv
  have hall : StrictConvexOn ℝ Set.univ asymptoticallyLinearCost := by
    apply StrictMono.strictConvexOn_univ_of_deriv
      asymptoticallyLinearCost_continuous
    simpa [hderiv] using asymptoticallyLinearMarginalCost_strictMono
  exact hall.subset (Set.subset_univ _) (convex_Ici 0)

theorem asymptoticallyLinearCost_strictMonoOn :
    StrictMonoOn asymptoticallyLinearCost (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    asymptoticallyLinearCost_continuous.continuousOn
  intro a ha
  have ha_pos : 0 < a := by
    simpa only [interior_Ici, Set.mem_Ioi] using ha
  rw [(asymptoticallyLinearCost_hasDerivAt a).deriv]
  dsimp [asymptoticallyLinearMarginalCost]
  have hexp : Real.exp (-a) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha_pos)
  linarith

theorem asymptoticallyLinear_marginal_le_one (a : ℝ) :
    deriv asymptoticallyLinearCost a ≤ 1 := by
  rw [(asymptoticallyLinearCost_hasDerivAt a).deriv]
  dsimp [asymptoticallyLinearMarginalCost]
  linarith [Real.exp_pos (-a)]

theorem asymptoticallyLinear_derivative_sublevel_not_bddAbove :
    ¬ BddAbove {a : ℝ |
      0 ≤ a ∧ deriv asymptoticallyLinearCost a ≤ 1} := by
  rw [not_bddAbove_iff]
  intro x
  refine ⟨max 0 x + 1, ?_, ?_⟩
  · constructor
    · have hx : 0 ≤ max 0 x := le_max_left _ _
      linarith
    · exact asymptoticallyLinear_marginal_le_one _
  · have hx : x ≤ max 0 x := le_max_right _ _
    linarith

/-- The exact counterexample package: all of the paper's stated regularity
properties hold, while the marginal-cost sublevel at threshold one is
unbounded above. -/
theorem rentDissipation_finite_supremum_counterexample :
    asymptoticallyLinearCost 0 = 0 ∧
    StrictMonoOn asymptoticallyLinearCost (Set.Ici 0) ∧
    StrictConvexOn ℝ (Set.Ici 0) asymptoticallyLinearCost ∧
    (∀ a, DifferentiableAt ℝ asymptoticallyLinearCost a) ∧
    ¬ BddAbove {a : ℝ |
      0 ≤ a ∧ deriv asymptoticallyLinearCost a ≤ 1} := by
  refine ⟨?_, asymptoticallyLinearCost_strictMonoOn,
    asymptoticallyLinearCost_strictConvex, ?_,
    asymptoticallyLinear_derivative_sublevel_not_bddAbove⟩
  · simp [asymptoticallyLinearCost]
  · intro a
    exact (asymptoticallyLinearCost_hasDerivAt a).differentiableAt

end

end SmoothingCliff.Racing
