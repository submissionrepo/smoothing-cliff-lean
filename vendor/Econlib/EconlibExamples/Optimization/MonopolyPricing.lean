/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Monopoly Pricing: First- and Second-Order Conditions

This file formalizes the textbook monopoly-pricing calculation with linear demand. A monopolist
faces demand `D(p) = a − b·p` with slope `−b` (the demand coefficient `b > 0`, so demand slopes
down), has constant marginal cost `c`, and chooses the price `p` that maximizes profit

`π(p) = (p − c)·(a − b·p)`.

Because profit is a downward parabola, the optimal price is the familiar midpoint between marginal
cost and the choke price:

`p* = (a + b·c) / (2·b) = (c + a/b) / 2`.

The Lean development treats this as a worked example of global optimality first and local
first-order conditions second. We prove directly that `p*` is the global maximizer, then use the
general unconstrained-optimization API to recover the first- and second-order conditions at the
optimum.

## The story

The monopolist trades off margin against volume. Raising price increases the markup `p − c`, but
lowers quantity sold through the linear demand curve. The optimum splits the difference: It lies
halfway between the cost floor `c` and the choke price `a/b`, where demand would fall to zero.

The economic story is cleanest when demand is viable at marginal cost, `b·c < a`. In that regime
the optimal price is strictly above cost, strictly below the choke price, sells a positive
quantity, and earns strictly positive profit.

## The mathematics

The central algebraic identity is the exact profit gap

`π(p*) − π(p) = b·(p* − p)²`.

When `b > 0`, the right-hand side is nonnegative for every price `p`, so `p*` globally maximizes
profit. This proof of optimality is purely algebraic.

After global optimality is established, the local calculus conditions become consequences of the
general theory: `IsMaxOn.deriv_eq_zero` gives `π′(p*) = 0`, and `IsMaxOn.deriv_deriv_nonpos` gives
`π″(p*) ≤ 0`. The file also computes the closed forms `π′(p) = a + b·c − 2·b·p` and `π″(p) = −2b`,
making the usual marginal-revenue-equals-marginal-cost calculation visible.

## What this file proves

We construct the profit function `profit a b c`, define the candidate optimal price `pStar a b c`,
and prove that it globally maximizes profit over all real prices whenever `b > 0`.

The file then connects the global result to the textbook calculus story:

* `profit_foc` derives the first-order condition at the optimum from global maximality.
* `profit_soc` derives the weak second-order condition from the same optimality fact.
* `profit_soc_neg` records the strict second-order condition `π″ = −2b < 0`.
* In the viable-demand regime `b·c < a`, the optimum has positive markup, positive demand, and
  positive profit.

## Main definitions and theorems

* `profit a b c` — the monopolist's profit function `p ↦ (p − c)·(a − b·p)`.
* `pStar a b c` — the optimal price `(a + b·c)/(2·b)`, the cost/choke midpoint
  (`pStar_eq_midpoint`).
* `profit_eq_sq` — the exact profit gap `π(p*) − π(p) = b·(p* − p)²`.
* `profit_isMaxOn` — `p*` globally maximizes profit over all prices.
* `profit_foc` / `profit_soc` — first- and second-order conditions at `p*`, both via the general
  `IsMaxOn` interior-optimum lemmas.
* `deriv_profit` / `deriv_deriv_profit` / `profit_soc_neg` — the closed forms
  `π′(p) = a + b·c − 2·b·p` and `π″ ≡ −2b < 0`.
* `cost_lt_pStar`, `pStar_lt_choke`, `demand_pos`, `profit_pos` — the textbook regime `b·c < a`.
-/

noncomputable section

namespace EconlibExamples.Optimization.MonopolyPricing

open Econlib.Optimization

variable (a b c : ℝ)

/-- The monopolist's profit `π(p) = (p − c)·(a − b·p)` under linear demand `D(p) = a − b·p`. -/
def profit (p : ℝ) : ℝ := (p - c) * (a - b * p)

/-- The profit-maximizing price `p* = (a + b·c)/(2·b)`. -/
def pStar : ℝ := (a + b * c) / (2 * b)

/-- The exact profit gap is a perfect square scaled by `b`: `π(p*) − π(p) = b·(p* − p)²`. This
single identity drives the global-maximum claim. -/
lemma profit_eq_sq (hb : 0 < b) (p : ℝ) :
    profit a b c (pStar a b c) - profit a b c p = b * (pStar a b c - p) ^ 2 := by
  simp only [profit, pStar]
  field_simp
  ring

/-- **The optimal price globally maximizes profit.** Over all prices `p`, profit never exceeds
`π(p*)`, because the gap `b·(p* − p)²` is nonnegative. -/
theorem profit_isMaxOn (hb : 0 < b) : IsMaxOn (profit a b c) Set.univ (pStar a b c) := by
  intro p _
  simp only [Set.mem_setOf_eq]
  have := profit_eq_sq a b c hb p
  nlinarith [mul_nonneg hb.le (sq_nonneg (pStar a b c - p)), this]

/-- **First-order condition.** At the optimum the marginal profit vanishes, `π′(p*) = 0`. We obtain
it from the global maximum via the interior-optimum lemma `IsMaxOn.deriv_eq_zero`;
differentiability of the polynomial profit is discharged by `fun_prop`. -/
theorem profit_foc (hb : 0 < b) : deriv (profit a b c) (pStar a b c) = 0 :=
  (profit_isMaxOn a b c hb).deriv_eq_zero (by simp) (by unfold profit; fun_prop)

/-- Marginal profit in closed form: `π′(p) = a + b·c − 2·b·p`, the demand `a − b·p` plus the markup
term `−b·(p − c)`. Setting it to zero is the price-space **"marginal revenue = marginal cost"**
condition. -/
lemma deriv_profit : deriv (profit a b c) = fun p => a + b * c - 2 * b * p := by
  funext p
  have h₁ : HasDerivAt (fun p : ℝ => p - c) 1 p := (hasDerivAt_id p).sub_const c
  have h₂ : HasDerivAt (fun p : ℝ => a - b * p) (-b) p := by
    simpa using (hasDerivAt_const p a).sub ((hasDerivAt_id p).const_mul b)
  have hd : HasDerivAt (profit a b c) (1 * (a - b * p) + (p - c) * -b) p := h₁.mul h₂
  rw [hd.deriv]
  ring

/-- `π″ ≡ −2b`: Profit is a downward parabola with constant second derivative. -/
lemma deriv_deriv_profit (p : ℝ) : deriv (deriv (profit a b c)) p = -(2 * b) := by
  rw [deriv_profit]
  have : HasDerivAt (fun p : ℝ => a + b * c - 2 * b * p) (-(2 * b)) p := by
    simpa using (hasDerivAt_const p (a + b * c)).sub ((hasDerivAt_id p).const_mul (2 * b))
  exact this.deriv

/-- **Second-order condition.** Marginal profit is (weakly) decreasing at the optimum, `π″(p*) ≤ 0`
— the necessary condition delivered by the general interior-maximum lemma
`IsMaxOn.deriv_deriv_nonpos` from optimality plus twice-differentiability alone. (The exact value
is `π″ ≡ −2b`: See `deriv_deriv_profit` and the strict form `profit_soc_neg`.) -/
theorem profit_soc (hb : 0 < b) : deriv (deriv (profit a b c)) (pStar a b c) ≤ 0 :=
  (profit_isMaxOn a b c hb).deriv_deriv_nonpos (by simp)
    (by unfold profit; fun_prop)
    (by rw [deriv_profit]; fun_prop)

/-- **Strict second-order condition**: `π″(p*) = −2b < 0`. The maximum is nondegenerate. -/
theorem profit_soc_neg (hb : 0 < b) : deriv (deriv (profit a b c)) (pStar a b c) < 0 := by
  rw [deriv_deriv_profit]; linarith

/-! ## The textbook regime `b·c < a`

Everything above holds for arbitrary `a`, `c`: Those are facts about a downward parabola. The
textbook monopoly narrative — positive markup, positive sales, positive profit, optimal price
between cost and choke price — additionally requires demand to be viable at marginal cost,
`D(c) = a − b·c > 0`. -/

/-- `p*` is literally the midpoint of marginal cost `c` and the choke price `a/b` — the "average of
cost and choke price" rule. -/
lemma pStar_eq_midpoint (hb : 0 < b) : pStar a b c = (c + a / b) / 2 := by
  rw [pStar]
  field_simp
  ring

/-- **Positive markup**: In the textbook regime the optimal price strictly exceeds marginal cost. -/
theorem cost_lt_pStar (hb : 0 < b) (hac : b * c < a) : c < pStar a b c := by
  rw [pStar, lt_div_iff₀ (by positivity)]
  nlinarith

/-- The optimal price sits strictly below the **choke price** `a/b` at which demand vanishes: The
monopolist restricts supply but never chokes the market entirely. -/
theorem pStar_lt_choke (hb : 0 < b) (hac : b * c < a) : pStar a b c < a / b := by
  rw [pStar, div_lt_div_iff₀ (by positivity) hb]
  nlinarith [mul_pos hb (sub_pos.mpr hac)]

/-- **Positive sales at the optimum**: `D(p*) = (a − b·c)/2 > 0`. -/
theorem demand_pos (hb : 0 < b) (hac : b * c < a) : 0 < a - b * pStar a b c := by
  have hD : a - b * pStar a b c = (a - b * c) / 2 := by rw [pStar]; field_simp; ring
  rw [hD]
  linarith

/-- **Positive profit at the optimum**: The monopolist operates. -/
theorem profit_pos (hb : 0 < b) (hac : b * c < a) : 0 < profit a b c (pStar a b c) := by
  unfold profit
  exact mul_pos (sub_pos.mpr (cost_lt_pStar a b c hb hac)) (demand_pos a b c hb hac)

end EconlibExamples.Optimization.MonopolyPricing
