/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy

/-!
# General equilibrium: The First Welfare Theorem

The first welfare theorem for the preference-carried exchange `Economy`. Every Walrasian
equilibrium allocation is Pareto optimal and lies in the core. Both follow from the cost lemmas
`Economy.preferred_costly` / `Economy.strictlyPreferred_costly` (in `Econlib.Equilibrium.Economy`):
Under local nonsatiation a weakly-preferred bundle costs at least, and a strictly-preferred bundle
strictly more than, the agent's wealth, so no feasible reallocation can make everyone weakly and
someone strictly better off.

## Main statements

* `Economy.WalrasianEquilibrium.paretoOptimal`: **First Welfare Theorem**: Every Walrasian
  equilibrium allocation is Pareto optimal.
* `Economy.WalrasianEquilibrium.mem_core`: Every Walrasian equilibrium allocation lies in the core.

## References

* Arrow, Kenneth J. 1951. “An Extension of the Basic Theorems of Classical Welfare Economics.” In
  *Proceedings of the Second Berkeley Symposium on Mathematical Statistics and Probability*, edited
  by Jerzy Neyman. University of California Press.
* Debreu, Gerard. 1951. “The Coefficient of Resource Utilization.” *Econometrica* 19 (3): 273.
  [https://doi.org/10.2307/1906814](https://doi.org/10.2307/1906814).

## Tags

first welfare theorem, walrasian equilibrium, pareto optimal, core
-/

@[expose] public section

open Finset BigOperators Matrix Econlib.Preferences

namespace Econlib.Equilibrium

namespace Economy

variable {L : ℕ} {E : Economy L}

/-! ## First welfare theorem -/

/-- **First welfare theorem.** Every Walrasian equilibrium allocation is Pareto optimal. -/
theorem WalrasianEquilibrium.paretoOptimal (hreg : RegularEconomy E) (W : WalrasianEquilibrium E) :
    E.ParetoOptimal W.alloc :=
  -- Reuse the abstract optimum. Its `FeasibleOver`/`ParetoDominatesOver` components are defeq to
  -- the finite economy's `Feasible`/`ParetoDominates` (aggregation is the counting sum), so we only
  -- repackage the `And`s as the `Feasible` and `ParetoOptimal` structures.
  have := ParetoOptimalOver.of_preferred_costly (Z := E.Agents) (endow := E.endow) (pref := E.pref)
    (alloc := W.alloc) (price := W.price) W.price_cone (fun a l => (W.isOptimal a).1.1 l)
    W.clears.excess_nonpos
    (fun a _ hz hle => E.preferred_costly hreg (W.isOptimal a) hz hle)
    (fun a _ hz hlt => E.strictlyPreferred_costly (W.isOptimal a) hz hlt)
  { feasible := ⟨this.1.1, this.1.2⟩
    undominated := fun ⟨y, hy, hdom⟩ => this.2 ⟨y, ⟨hy.nonneg, hy.excess_nonpos⟩, hdom⟩ }

/-! ## Core -/

/-- Every Walrasian equilibrium allocation lies in the core. -/
theorem WalrasianEquilibrium.mem_core (W : WalrasianEquilibrium E) : E.Core W.alloc := by
  refine ⟨⟨fun a l => (W.isOptimal a).1.1 l, W.clears.excess_nonpos⟩, ?_⟩
  rintro ⟨S, y, hS_ne, hy_nn, hy_feas, hy_better⟩
  have h_expensive : ∀ i ∈ S, W.price ⬝ᵥ E.endow i < W.price ⬝ᵥ y i := fun i hi =>
    E.strictlyPreferred_costly (W.isOptimal i) (hy_nn i hi) (hy_better i hi)
  have h_sum : ∑ i ∈ S, W.price ⬝ᵥ E.endow i < ∑ i ∈ S, W.price ⬝ᵥ y i :=
    Finset.sum_lt_sum_of_nonempty hS_ne h_expensive
  -- Coalitional feasibility at nonneg prices bounds aggregate spending the other way.
  have h_le : ∑ i ∈ S, W.price ⬝ᵥ y i ≤ ∑ i ∈ S, W.price ⬝ᵥ E.endow i := by
    simp only [dotProduct]
    rw [Finset.sum_comm (s := S) (t := Finset.univ) (f := fun i l => W.price l * y i l),
        Finset.sum_comm (s := S) (t := Finset.univ) (f := fun i l => W.price l * E.endow i l)]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hy_feas l) (W.price_cone l)
  linarith

end Economy

end Econlib.Equilibrium
