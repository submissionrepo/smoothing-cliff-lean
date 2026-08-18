/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A stationary Walrasian equilibrium of an induced Markov economy

The macro / heterogeneous-agent face of the equilibrium API. A `MarkovExchangeEconomy` packages an
exogenous shock process and state-contingent preferences and endowments; a **stationary
functional** `π` (a unital, kernel-invariant aggregator — a measure-free stationary distribution)
collapses it to an ordinary static `Economy`, and a **stationary Walrasian equilibrium** is a
Walrasian equilibrium of that static economy. This is the market-clearing / accounting component a
stationary recursive competitive equilibrium must satisfy; the household dynamic program (policy
optimality) and the law of motion (`π` as the policy-induced invariant law) are inputs, not solved
here.

The one new object to build is the `StationaryFunctional`. We make it trivial by choosing
an **i.i.d.-uniform** transition: the next state is the drawn shock, drawn uniformly and
independently of the current state (`next z e = e`, `shock z = uniform`). We work at the level of
the one-step kernel — the transition law each period is uniform and history-independent, the
defining feature of an i.i.d. process — not the path-space measure. Then the one-step
expectation `P f` is a constant (independent of the state), the stationary distribution is uniform,
and the Koopman invariance `∫ Pf dπ = ∫ f dπ` collapses to `ring`.

## The model

* One good (`Fin 1`); two states and two shocks (`Bool`).
* Kernel: `shock z = uniform`, `next z e = e` — i.i.d. uniform transitions.
* Preferences `u x = x₀`, endowment `(1)` in every state (a unit of the good).
* Stationary functional: The uniform average `π f = f false / 2 + f true / 2`.
* Equilibrium: Price `(1)`, autarkic allocation `(1)` in every state (consume the endowment).

## Main definitions and theorems

* `markovKernel`, `markovEcon` — the i.i.d. kernel and the Markov exchange economy.
* `stationaryπ` — the uniform stationary functional (the crux; invariance is `ring`).
* `markov_alloc_mem_demand`, `markov_clears` — consumer optimality and market clearing.
* `markovEquilibrium` — a **stationary Walrasian equilibrium**.
* `markov_accounting_clears` — the same clearing re-derived from the steady-state **accounting
  identity** `aggregate income = aggregate consumption + δ·aggregate capital` (here `δ = 0`).
-/

noncomputable section

namespace EconlibExamples.Equilibrium.MarkovStationary

open Econlib.Equilibrium Econlib.Preferences Econlib.Probability Matrix

/-! ## The kernel and the economy -/

/-- The i.i.d.-uniform two-state kernel: The next state is the freshly drawn uniform shock,
independent of the current state. -/
def markovKernel : FiniteSupportKernel Bool Bool where
  shock _ := FinDist.uniform
  next _ e := e

/-- The single-good, two-state Markov exchange economy with linear preferences. -/
def markovEcon : MarkovExchangeEconomy 1 where
  State := Bool
  Shock := Bool
  kernel := markovKernel
  pref := fun _ => preferenceOfRealUtility (fun x => x 0)
  endow := fun _ => ![1]
  endow_mem := fun _ l => by fin_cases l; simp

/-! ## The stationary functional

The uniform average. The only non-bookkeeping field is `invariant`: Because the kernel is
i.i.d.-uniform, `P f` is the state-independent constant `(f false + f true) / 2`, so both sides of
the Koopman identity equal it. -/

/-- The uniform stationary functional `π f = f false / 2 + f true / 2`. -/
def stationaryπ : markovKernel.StationaryFunctional where
  aggregate f := f false / 2 + f true / 2
  positive f hf := by have := hf false; have := hf true; linarith
  aggregate_add f g := by dsimp only; ring
  aggregate_smul c f := by dsimp only; ring
  aggregate_one := by norm_num
  invariant f := by
    simp only [markovKernel, FiniteSupportKernel.expect, FinDist.expect_eq_sum,
      FinDist.uniform_apply, Fintype.card_bool, Fintype.sum_bool, Nat.cast_ofNat]
    ring

/-! ## The candidate equilibrium -/

/-- Equilibrium price for the single good. -/
def markovPrice : Fin 1 → ℝ := ![1]

/-- Autarkic allocation: Every state consumes its endowment. -/
def markovAlloc : Bool → (Fin 1 → ℝ) := fun _ => ![1]

/-! ## Consumer optimality, clearing, and the equilibrium -/

/-- Each state's autarkic consumption maximizes utility on its budget set: Any affordable `y` has
`u y = y₀ = price ⬝ᵥ y ≤ 1 = u (1)`. -/
theorem markov_alloc_mem_demand (s : (markovEcon.stationaryEconomy stationaryπ).Agents) :
    markovAlloc s ∈ (markovEcon.stationaryEconomy stationaryπ).demand markovPrice s := by
  have hendow : markovPrice ⬝ᵥ (markovEcon.stationaryEconomy stationaryπ).endow s = 1 := by
    change markovPrice ⬝ᵥ markovEcon.endow s = 1
    simp [markovPrice, markovEcon, dotProduct]
  change markovAlloc s ∈ Econlib.Optimization.argmaxRel
      (preferenceOfRealUtility (fun x => x 0))
      ((markovEcon.stationaryEconomy stationaryπ).budgetSet markovPrice s)
  rw [mem_argmaxRel_preferenceOfUtilityIn_iff]
  refine ⟨?_, isMaxOn_iff.mpr fun y hy => ?_⟩
  · -- budget feasibility
    simp only [MeasureEconomy.budgetSet, mem_budgetSetAt]
    exact ⟨fun l => by fin_cases l; simp [markovAlloc],
      by rw [hendow]; simp [markovPrice, markovAlloc, dotProduct]⟩
  · -- utility maximality: u y = y 0 ≤ 1 = u (markovAlloc s)
    simp only [MeasureEconomy.budgetSet, mem_budgetSetAt] at hy
    obtain ⟨_, hyw⟩ := hy
    rw [hendow] at hyw; simp [markovPrice, dotProduct] at hyw
    simp [markovAlloc]
    linarith

/-- Markets clear: The autarkic allocation aggregates to the endowment in the single good. -/
theorem markov_clears :
    (markovEcon.stationaryEconomy stationaryπ).MarketClears markovPrice markovAlloc :=
  stationaryEconomy_marketClears markovEcon stationaryπ markovAlloc markovPrice (fun _ => rfl)

/-- A **stationary Walrasian equilibrium**: A Walrasian equilibrium of the static economy induced by
the uniform stationary functional. (This constructs one such equilibrium; we do not claim it is the
unique one.) -/
def markovEquilibrium : markovEcon.StationaryWalrasianEquilibrium stationaryπ where
  price := markovPrice
  alloc := markovAlloc
  price_cone := fun l => by fin_cases l; simp [markovPrice]
  price_ne := ⟨0, by simp [markovPrice]⟩
  isOptimal := markov_alloc_mem_demand
  clears := markov_clears

/-! ## Steady-state accounting -/

/-- **Accounting recast of clearing.** The same market clearing follows from the steady-state
resource identity `aggregate income = aggregate consumption + δ · aggregate capital`. Here there is
no capital and no depreciation (`δ = 0`), so the identity reads
`aggregate income = aggregate
consumption`, and
`MarkovExchangeEconomy.stationaryEconomy_marketClears_of_transition`
turns it into `MarketClears`. -/
theorem markov_accounting_clears :
    (markovEcon.stationaryEconomy stationaryπ).MarketClears markovPrice (fun _ => ![1]) :=
  MarkovExchangeEconomy.stationaryEconomy_marketClears_of_transition markovEcon stationaryπ
    (wealth := fun _ => 1) (consumption := fun _ => 1) (capital := fun _ => 0)
    (expectedIncome := fun _ => 1) (delta := 0) (p := markovPrice)
    (fun _ => by ring)
    (fun s => by simp [markovEcon, markovKernel, FiniteSupportKernel.expect, FinDist.expect_const])
    (fun _ => by simp [markovEcon])

end EconlibExamples.Equilibrium.MarkovStationary

end
