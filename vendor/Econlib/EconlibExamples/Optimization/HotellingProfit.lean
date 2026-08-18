/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Hotelling's Lemma: Supply as the Gradient of Profit for a Concrete Firm

**Hotelling's lemma** is the supply-side envelope result of producer theory: The profit-maximizing
supply of a competitive firm equals the gradient of its (maximized) profit function in prices,
`∇_p Π(p) = y*(p)`. It is the production analog of Shephard's lemma and a special case of the
envelope/Danskin theorem — when the profit-maximizing plan is unique, the indirect (value) function
inherits the differentiability of the direct objective and its derivative "reads off" the optimal
choice.

## The model

A single-output price-taking firm. Prices live on the line, `E := ℝ` (which carries
`NormedAddCommGroup`, the real `InnerProductSpace ℝ ℝ` with `⟪x, y⟫ = x * y`, and `CompleteSpace`).
The output level lives in a compact, nonempty technology set `Y := ↥(Set.Icc 0 ymax)` for a fixed
capacity `ymax > 0`; the embedding `Y_embed y = (y : ℝ)` records the produced quantity and the cost
function is the strictly convex `cost y = (y : ℝ)² / 2`. The resulting profit objective is

`π(p, y) = p · y − y² / 2`.

For an interior price `p ∈ (0, ymax)` the firm's problem `max_{y ∈ [0, ymax]} (p · y − y²/2)` has a
unique solution, the interior point `y* = p`, with maximized profit `Π(p) = p²/2`. Hotelling's
lemma then gives `∇_p Π(p) = y* = p`.

## The mathematics

The objective is strictly concave in `y`, and completing the square exposes the optimum directly:

`p · y − y² / 2 = p²/2 − (p − y)²/2 ≤ p²/2`,

with equality iff `y = p`. Hence over `y ∈ [0, ymax]` the supremum (value function) is `p²/2`,
attained *only* at the interior point `y* = ⟨p, _⟩`. We prove `valueFunction π p = p²/2` by
`le_antisymm` — `ciSup_le` with the square identity for `≤`, and `le_ciSup` evaluated at `y*` for
`≥` (using boundedness of the range from compactness) — and then characterize the optimizer set:
`π(p, y) = p²/2 ↔ (p − y)² = 0 ↔ y = p ↔ y = y*`. This yields the singleton-argmax hypothesis
`argmax_iSup π p = {y*}` that `hasGradientAt_profitFunction` consumes.

The instances needed for the subtype `Y` are standard: `CompactSpace ↥(Set.Icc 0 ymax)` comes from
`compactSpace_Icc`, and `Nonempty` from the interior point. Continuity of `cost` and `Y_embed`
(both restrictions of polynomials in the coordinate) and openness of the price set `(0, ymax)`
(`isOpen_Ioo`) complete the hypotheses.

## Main definitions and theorems

* `Y ymax` — the technology set `↥(Set.Icc 0 ymax)` of feasible outputs.
* `Y_embed`, `cost` — the output embedding `y ↦ (y : ℝ)` and quadratic cost `y ↦ (y : ℝ)²/2`.
* `profitObjective_apply` — the profit objective equals `p · y − y²/2`.
* `valueFunction_eq` — the maximized profit (value function) at `p ∈ (0, ymax)` is `p²/2`.
* `argmax_eq_singleton` — the profit-maximizing output is the unique interior point `y* = p`.
* `hotelling` — Hotelling's lemma on this firm: `∇_p Π(p) = y* = p` at every `p ∈ (0, ymax)`.
* `hotelling_hasDerivAt` / `deriv_profitFunction` — the scalar punchline `Π′(p) = y*(p) = p` (via
  `Y_embed_y_star`): Differentiating the profit function traces out the supply curve.
-/

noncomputable section

namespace EconlibExamples.Optimization.HotellingProfit

open Econlib.Optimization Econlib.Optimization.Envelope
open Set Danskin

variable {ymax : ℝ}

/-- The firm's technology set: Feasible outputs form the compact interval `[0, ymax]`. -/
abbrev Y (ymax : ℝ) : Type := ↥(Set.Icc (0 : ℝ) ymax)

/-- The output embedding: A feasible plan `y` produces the quantity `(y : ℝ)`. -/
def Y_embed : Y ymax → ℝ := fun y => (y : ℝ)

/-- The (strictly convex) cost of producing output `y`: `c(y) = y² / 2`. -/
def cost : Y ymax → ℝ := fun y => (y : ℝ) ^ 2 / 2

/-- The profit objective in this model is `π(p, y) = p · y − y²/2`. The upstream
`profitObjective_real` already collapses the abstract `⟪p, y⟫` on the line to `p * y`; here we just
substitute the concrete `Y_embed` and `cost`. -/
@[simp] lemma profitObjective_apply (p : ℝ) (y : Y ymax) :
    profitObjective Y_embed cost p y = p * (y : ℝ) - (y : ℝ) ^ 2 / 2 := by
  simp only [profitObjective_real, Y_embed, cost]

/-- The lower endpoint `0` is feasible, so `Y ymax` is nonempty whenever `ymax ≥ 0`. -/
instance instNonemptyY (ymax : ℝ) [Fact (0 ≤ ymax)] : Nonempty (Y ymax) :=
  ⟨⟨0, ⟨le_refl _, Fact.out⟩⟩⟩

/-- The output embedding `y ↦ (y : ℝ)` is continuous (it is the subtype coercion). -/
lemma continuous_Y_embed : Continuous (Y_embed (ymax := ymax)) :=
  continuous_subtype_val

/-- The quadratic cost `y ↦ (y : ℝ)²/2` is continuous (a polynomial in the coordinate). -/
lemma continuous_cost : Continuous (cost (ymax := ymax)) := by
  unfold cost
  exact (continuous_subtype_val.pow 2).div_const 2

/-! ### The crux: Computing the value function and the optimizer set

Completing the square `p · y − y²/2 = p²/2 − (p − y)²/2` makes the maximizer transparent: The
objective never exceeds `p²/2`, and equals it exactly when `y = p`. For an interior price the point
`y = p` is feasible, so it is the *unique* profit-maximizing output. -/

section InteriorPrice

/-- The profit objective on this firm, with `ymax` fixed explicitly so that the dependent type
`Y ymax` is fixed in the statements below (it is otherwise only constrained through `Y_embed`'s
domain, which the elaborator will not infer). -/
local notation3 "π" => profitObjective (Y_embed (ymax := ymax)) (cost (ymax := ymax))

variable [Fact (0 ≤ ymax)] {p : ℝ}

/-- For an interior price the optimal output `y* = p` is itself a feasible plan. -/
def y_star (hp : p ∈ Set.Ioo (0 : ℝ) ymax) : Y ymax :=
  ⟨p, Set.mem_Icc.mpr ⟨le_of_lt hp.1, le_of_lt hp.2⟩⟩

omit [Fact (0 ≤ ymax)] in
/-- The profit objective is bounded above on the (compact) technology set, so its supremum is a
least upper bound rather than the junk value of an unbounded `iSup`. -/
lemma bddAbove_profit (p : ℝ) : BddAbove (Set.range (fun y : Y ymax => π p y)) := by
  -- `y ↦ π p y` is continuous on the compact technology set, so its range is compact and bounded.
  have hcont : Continuous (fun y : Y ymax => π p y) :=
    profitObjective_continuous_right Y_embed cost continuous_cost continuous_Y_embed p
  exact (isCompact_range hcont).bddAbove

/-- **The maximized profit (value function) at an interior price is `p²/2`.** The `≤` direction is
the completed-square bound `π(p, y) = p²/2 − (p − y)²/2 ≤ p²/2`; the `≥` direction evaluates the
objective at the feasible point `y* = p`, where it attains `p²/2`. -/
lemma valueFunction_eq (hp : p ∈ Set.Ioo (0 : ℝ) ymax) :
    valueFunction π p = p ^ 2 / 2 := by
  apply le_antisymm
  · -- Square identity: every objective value is ≤ p²/2.
    apply ciSup_le
    intro y
    rw [profitObjective_apply]
    nlinarith [sq_nonneg (p - (y : ℝ))]
  · -- Evaluated at the feasible interior point y* = p, the objective hits p²/2.
    have hval : π p (y_star hp) = p ^ 2 / 2 := by
      rw [profitObjective_apply]; simp only [y_star]; ring
    rw [← hval]
    exact le_ciSup (bddAbove_profit p) (y_star hp)

omit [Fact (0 ≤ ymax)] in
/-- **The profit-maximizing output is unique.** The objective equals the value `p²/2` exactly at
the interior point `y* = p`: Completing the square turns the equality into `(p − y)² = 0`, then
`Subtype.ext` lifts `(y : ℝ) = p` to `y = y*`. -/
lemma profit_eq_value_iff (hp : p ∈ Set.Ioo (0 : ℝ) ymax) (y : Y ymax) :
    π p y = p ^ 2 / 2 ↔ y = y_star hp := by
  rw [profitObjective_apply]
  constructor
  · intro h
    -- p·y − y²/2 = p²/2 ⟺ (p − y)² = 0 ⟺ (y : ℝ) = p.
    have hsq : (p - (y : ℝ)) ^ 2 = 0 := by nlinarith [h]
    have hyp : (y : ℝ) = p := by
      have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq
      linarith
    exact Subtype.ext hyp
  · intro h
    subst h
    simp only [y_star]; ring

/-- **The optimizer set is the singleton `{y*}`.** This is the hypothesis consumed by Hotelling's
lemma: Combining `valueFunction_eq` with `profit_eq_value_iff` says a feasible plan is optimal iff
it is the interior point `y* = p`. -/
lemma argmax_eq_singleton (hp : p ∈ Set.Ioo (0 : ℝ) ymax) :
    argmax_iSup π p = {y_star hp} := by
  ext y
  rw [Danskin.argmax_iSup, Set.mem_setOf_eq, valueFunction_eq hp, Set.mem_singleton_iff]
  exact profit_eq_value_iff hp y

/-! ### Hotelling's Lemma on this firm -/

/-- **Hotelling's lemma.** At every interior price `p ∈ (0, ymax)` the profit function `Π(p)` is
differentiable with gradient equal to the optimal supply `y* = p`. This is a direct instantiation
of the upstream envelope theorem `hasGradientAt_profitFunction`: We supply openness of the price
set (`isOpen_Ioo`), continuity of cost and the output embedding, and the singleton-argmax fact
`argmax_eq_singleton`. -/
theorem hotelling (hp : p ∈ Set.Ioo (0 : ℝ) ymax) :
    HasGradientAt (profitFunction (Y_embed (ymax := ymax)) (cost (ymax := ymax)))
      (Y_embed (y_star hp)) p :=
  hasGradientAt_profitFunction Y_embed cost isOpen_Ioo continuous_cost continuous_Y_embed
    p hp (y_star hp) (argmax_eq_singleton hp)

omit [Fact (0 ≤ ymax)] in
/-- The quantity supplied at an interior price is the price itself: `y*(p) = p`. This is the
identification that turns the abstract gradient statement of `hotelling` into the scalar supply
curve. -/
@[simp] lemma Y_embed_y_star (hp : p ∈ Set.Ioo (0 : ℝ) ymax) : Y_embed (y_star hp) = p := rfl

/-- **Hotelling's lemma, scalar form.** On the line the gradient is the ordinary derivative, so
Hotelling's lemma reads `Π′(p) = y*(p) = p`: Differentiating the profit function in the price
traces out the firm's supply curve. -/
theorem hotelling_hasDerivAt (hp : p ∈ Set.Ioo (0 : ℝ) ymax) :
    HasDerivAt (profitFunction (Y_embed (ymax := ymax)) (cost (ymax := ymax))) p p :=
  (hotelling hp).hasDerivAt'

/-- The derivative of the profit function at an interior price is the optimal supply:
`Π′(p) = p`. Together with the closed form `Π(p) = p²/2` (`valueFunction_eq`) this closes the
envelope loop explicitly: `(p²/2)′ = p = y*(p)`. -/
theorem deriv_profitFunction (hp : p ∈ Set.Ioo (0 : ℝ) ymax) :
    deriv (profitFunction (Y_embed (ymax := ymax)) (cost (ymax := ymax))) p = p :=
  (hotelling_hasDerivAt hp).deriv

end InteriorPrice

end EconlibExamples.Optimization.HotellingProfit
