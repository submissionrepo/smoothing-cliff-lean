import SmoothingCliff.Racing.ConcaveGameExistence
import SmoothingCliff.Racing.SpreadDecay

/-!
# Existence of a pure-strategy equilibrium of the race

Formal target: Proposition `prop:rentdissipation` (ii) in
`Smoothing_the_Cliff_ITCS.tex`.

Two steps.  First, a game whose action sets are compact intervals of the line
and whose payoffs are continuous and concave in the own action has a
pure-strategy equilibrium: this specializes the Debreu--Glicksberg--Fan result
of `ConcaveGameExistence.lean` to the racing shape.  Second, the racing payoff
is strictly concave in the own action under the paper's curvature condition.

The curvature condition is stated one derivative lower than in the paper.  The
paper assumes the cost twice differentiable with `inf c'' > S`; what the proof
actually needs is that marginal cost grows at least at rate `S`, and that is
what is assumed here.  Every twice-differentiable cost with `inf c'' >= eps`
satisfies it, and no differentiability of the allocation is required at all:
the allocation spread grows at most at rate `S` because the rule is monotone
and `S`-Lipschitz.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-! ### The racing payoff is strictly concave in the own action -/

/-- The allocation spread grows at most at the certified rate.  Monotonicity
supplies the lower endpoint and the Lipschitz certificate the upper one. -/
theorem spread_growth_le
    (allocation : ℝ → ℝ) (sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value first second : ℝ} (hab : first ≤ second) :
    (allocation (value + second) - allocation (reserve + second)) -
        (allocation (value + first) - allocation (reserve + first)) ≤
      (sensitivity : ℝ) * (second - first) := by
  have hvalue : allocation (value + second) - allocation (value + first) ≤
      (sensitivity : ℝ) * (second - first) := by
    have hd := hLip.dist_le_mul (value + second) (value + first)
    rw [Real.dist_eq, Real.dist_eq] at hd
    have habs : allocation (value + second) - allocation (value + first) ≤
        |allocation (value + second) - allocation (value + first)| :=
      le_abs_self _
    have hxy : |value + second - (value + first)| = second - first := by
      rw [abs_of_nonneg (by linarith)]
      ring
    calc
      allocation (value + second) - allocation (value + first) ≤
          |allocation (value + second) - allocation (value + first)| := habs
      _ ≤ (sensitivity : ℝ) * |value + second - (value + first)| := hd
      _ = (sensitivity : ℝ) * (second - first) := by rw [hxy]
  have hreserve : allocation (reserve + first) ≤ allocation (reserve + second) :=
    hMono (by linarith)
  linarith

/-- Under the curvature condition, the marginal utility of advantage is
strictly decreasing, which is strict concavity of the payoff in the own
action. -/
theorem advantageUtility_marginal_strictAnti
    (allocation cost : ℝ → ℝ) (sensitivity : NNReal) {curvature : ℝ}
    (hMono : Monotone allocation)
    (hLip : LipschitzWith sensitivity allocation)
    (hCurvature : (sensitivity : ℝ) < curvature)
    (hCost : ∀ first second : ℝ, first ≤ second →
      curvature * (second - first) ≤ deriv cost second - deriv cost first)
    (reserve value : ℝ) :
    StrictAnti fun advantage : ℝ =>
      allocation (value + advantage) - allocation (reserve + advantage) -
        deriv cost advantage := by
  intro first second hlt
  have hspread := spread_growth_le allocation sensitivity hMono hLip
    (reserve := reserve) (value := value) hlt.le
  have hcost := hCost first second hlt.le
  have hgap : 0 < second - first := by linarith
  nlinarith [hspread, hcost, hgap, hCurvature]

/-! ### Existence on a compact action box -/

/-- The racing shape: every action set is a compact interval of the line. -/
def raceSlice (upper : ℝ) : Set ℝ := Set.Icc 0 upper

theorem raceSlice_convex (upper : ℝ) : Convex ℝ (raceSlice upper) :=
  convex_Icc 0 upper

theorem raceSlice_compact (upper : ℝ) : IsCompact (raceSlice upper) :=
  isCompact_Icc

theorem raceSlice_nonempty {upper : ℝ} (hUpper : 0 ≤ upper) :
    (raceSlice upper).Nonempty :=
  Set.nonempty_Icc.mpr hUpper

/-- The racing game packaged as concave-game data. -/
def raceGameData
    {ι : Type} [Fintype ι] [Inhabited ι] [DecidableEq ι]
    (upper : ι → ℝ) (hUpper : ∀ i, 0 ≤ upper i)
    (payoff : (i : ι) → ((j : ι) → ↑(raceSlice (upper j))) → ℝ)
    (hCont : ∀ i, Continuous (payoff i))
    (hConcave : ∀ (i : ι) (σ : (j : ι) → ↑(raceSlice (upper j))),
      ∃ g : ℝ → ℝ, ConcaveOn ℝ (raceSlice (upper i)) g ∧
        ∀ y : ↑(raceSlice (upper i)),
          g y.1 = payoff i (Function.update σ i y)) :
    ConcaveNashExistenceData where
  Player := ι
  V := fun _ => ℝ
  Slice := fun i => raceSlice (upper i)
  hSlice_convex := fun i => raceSlice_convex (upper i)
  hSlice_compact := fun i => raceSlice_compact (upper i)
  hSlice_nonempty := fun i => raceSlice_nonempty (hUpper i)
  payoff := payoff
  payoff_continuous := hCont
  payoff_quasiconcave_in_own := fun i σ => by
    obtain ⟨g, hg, hmatch⟩ := hConcave i σ
    exact ⟨g, hg.quasiconcaveOn, hmatch⟩

/-- **Proposition `prop:rentdissipation` (ii), existence.**  A game on compact
action intervals with continuous payoffs that are concave in the own action has
a pure-strategy Nash equilibrium. -/
theorem exists_race_equilibrium
    {ι : Type} [Fintype ι] [Inhabited ι] [DecidableEq ι]
    (upper : ι → ℝ) (hUpper : ∀ i, 0 ≤ upper i)
    (payoff : (i : ι) → ((j : ι) → ↑(raceSlice (upper j))) → ℝ)
    (hCont : ∀ i, Continuous (payoff i))
    (hConcave : ∀ (i : ι) (σ : (j : ι) → ↑(raceSlice (upper j))),
      ∃ g : ℝ → ℝ, ConcaveOn ℝ (raceSlice (upper i)) g ∧
        ∀ y : ↑(raceSlice (upper i)),
          g y.1 = payoff i (Function.update σ i y)) :
    ∃ σ : (raceGameData upper hUpper payoff hCont hConcave).Profile,
      (raceGameData upper hUpper payoff hCont
        hConcave).toEquilibriumProblem.IsEquilibrium σ :=
  ConcaveNashExistenceData.exists_equilibrium _

end

end SmoothingCliff.Racing
