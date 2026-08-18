/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Production.Economy
public import Econlib.Preferences.Pareto

/-!
# First welfare theorem with production

The first welfare theorem for the Arrow–Debreu private-ownership economy: Every Walrasian
equilibrium with production is Pareto optimal, assuming only local nonsatiation and profit
maximization.

## Main definitions

* `ProductionEconomy.Feasible` — nonnegative consumption, attainable plans, free-disposal clearing.
* `ProductionEconomy.ParetoDominates` / `ParetoOptimal` — welfare comparison over consumption.

## Main statements

* `WalrasianEquilibriumWithProduction.paretoOptimal` — every equilibrium allocation is Pareto
  optimal.

## References

* Arrow, Kenneth J. 1951. “An Extension of the Basic Theorems of Classical Welfare Economics.” In
  *Proceedings of the Second Berkeley Symposium on Mathematical Statistics and Probability*, edited
  by Jerzy Neyman. University of California Press.
* Debreu, Gerard. 1951. “The Coefficient of Resource Utilization.” *Econometrica* 19 (3): 273.
  [https://doi.org/10.2307/1906814](https://doi.org/10.2307/1906814).

## Tags

welfare theorem, production economy, pareto optimality, arrow-debreu
-/

@[expose] public section

open Matrix Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

namespace ProductionEconomy

variable (E : ProductionEconomy L)

/-! ## Feasibility and Pareto optimality with production -/

/-- A feasible production allocation: Nonnegative consumption, attainable production plans
(`yⱼ ∈ Yⱼ`), and aggregate excess demand nonpositive in every good (free disposal). -/
structure Feasible (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)) : Prop where
  /-- Every consumption bundle is nonnegative in every good. -/
  nonneg : ∀ a l, 0 ≤ x a l
  /-- Every firm's plan is attainable (`yⱼ ∈ Yⱼ`). -/
  plans_feasible : ∀ j, y j ∈ (E.tech j).Y
  /-- Aggregate excess demand is nonpositive in every good (free disposal). -/
  excess_nonpos : ∀ l, E.aggregateExcess x y l ≤ 0

/-- Consumption allocation `x` Pareto dominates `x'`: Every agent weakly prefers `x` and at least
one strictly prefers it. Production plans enter welfare only through feasibility. -/
def ParetoDominates (x x' : E.Agents → (Fin L → ℝ)) : Prop :=
  Econlib.Preferences.ParetoDominates E.pref x x'

/-- A feasible production allocation is Pareto optimal if no feasible allocation's consumption
Pareto dominates it. -/
structure ParetoOptimal (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)) : Prop where
  /-- The allocation is feasible. -/
  feasible : E.Feasible x y
  /-- No feasible allocation's consumption Pareto dominates `x`. -/
  undominated : ¬ ∃ x' y', E.Feasible x' y' ∧ E.ParetoDominates x' x

variable {E}

/-! ## First welfare theorem with production -/

/-- **First welfare theorem with production** (Arrow 1951; Debreu 1951). Every Walrasian
equilibrium with production is Pareto optimal. Requires only local nonsatiation and profit
maximization — no convexity or closedness of any technology is assumed. -/
theorem _root_.Econlib.Equilibrium.WalrasianEquilibriumWithProduction.paretoOptimal
    (hlns : ∀ a, LocallyNonsatiated (nonnegOrthant L) (E.pref a))
    (W : WalrasianEquilibriumWithProduction E) :
    E.ParetoOptimal W.alloc W.plan := by
  refine ⟨⟨fun a l => (W.isOptimal a).1.1 l, fun j => (W.profit_max j).1, W.clears.1⟩, ?_⟩
  rintro ⟨x', y', ⟨hx'_nn, hy'_mem, hy'_feas⟩, hyle, a₀, hya₀⟩
  -- Net spending `W.price ⬝ᵥ x' a - E.wealth W.price a` is ≥ 0 for all agents, > 0 at `a₀`.
  have hg_nonneg : ∀ a, 0 ≤ W.price ⬝ᵥ x' a - E.wealth W.price a := fun a => by
    linarith [budgetSetAt_preferred_costly (hlns a) (W.isOptimal a) (hx'_nn a) (hyle a)]
  have hg_pos : 0 < W.price ⬝ᵥ x' a₀ - E.wealth W.price a₀ := by
    linarith [budgetSetAt_strictlyPreferred_costly (W.isOptimal a₀) (hx'_nn a₀) hya₀]
  have hplan_le : W.price ⬝ᵥ (fun l => ∑ j, y' j l) ≤ ∑ j, (E.tech j).profit W.price := by
    have hsum : W.price ⬝ᵥ (fun l => ∑ j, y' j l) = ∑ j, W.price ⬝ᵥ y' j := by
      simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hsum]
    exact Finset.sum_le_sum fun j _ =>
      (E.tech j).dotProduct_le_profit_of_mem_supply (hy'_mem j) (W.profit_max j)
  -- Free disposal at nonneg prices: `W.price ⬝ᵥ aggregateExcess ≤ 0`.
  have hexcess_le : W.price ⬝ᵥ E.aggregateExcess x' y' ≤ 0 := by
    simp only [dotProduct]
    exact Finset.sum_nonpos fun l _ =>
      mul_nonpos_of_nonneg_of_nonpos (W.price_cone l) (hy'_feas l)
  -- Split `toEconomy.aggregateExcess x' = aggregateExcess x' y' + ∑ j, y' j`.
  have hagg_excess_le :
      W.price ⬝ᵥ E.toEconomy.aggregateExcess x' ≤ ∑ j, (E.tech j).profit W.price := by
    have hrw : E.toEconomy.aggregateExcess x'
        = E.aggregateExcess x' y' + (fun l => ∑ j, y' j l) := by
      rw [E.aggregateExcess_eq x' y']; abel
    rw [hrw, dotProduct_add]
    linarith [hexcess_le, hplan_le]
  have hagg_le : (∑ a, (W.price ⬝ᵥ x' a - E.wealth W.price a)) ≤ 0 := by
    rw [E.aggregate_net_spending W.price x']
    linarith [hagg_excess_le]
  have hagg_zero : (∑ a, (W.price ⬝ᵥ x' a - E.wealth W.price a)) = 0 :=
    le_antisymm hagg_le (Finset.sum_nonneg fun a _ => hg_nonneg a)
  have hgainer_zero := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hg_nonneg a).mp hagg_zero a₀
    (Finset.mem_univ a₀)
  linarith

end ProductionEconomy

end Econlib.Equilibrium
