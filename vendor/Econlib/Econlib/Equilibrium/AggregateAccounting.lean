/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Equilibrium.MarketClearing
public import Econlib.Probability.Markov.Endogenous

/-!
# Aggregate accounting

This file provides aggregate accounting identities for stationary Markov economies and packages
them as market-clearing statements for the static economy induced by a stationary distribution.

The accounting results relate aggregate wealth, consumption, capital, and expected income. The
basic identity starts from pointwise equations for current wealth and next-period resources. The
stationary version replaces next-period wealth with a finite-support kernel expectation. The
collateral version adds Arrow-claim demand and collateral supply, with claim-market clearing giving
the same aggregate resource identity.

The file also defines `MarkovExchangeEconomy`, whose agents are states of a finite-support Markov
kernel, and `MarkovExchangeEconomy.stationaryEconomy`, the static `MeasureEconomy` obtained from a
stationary functional. In the one-good special cases, the resource identities imply `MarketClears`
for the induced stationary economy at the consumption allocation.

## Main definitions

* `MarkovExchangeEconomy`: A finite-support Markov kernel economy whose agents are states, each
  carrying a preference and a nonnegative endowment.
* `MarkovExchangeEconomy.stationaryEconomy`: The static `MeasureEconomy` induced at a stationary
  functional `π`.
* `MarkovExchangeEconomy.StationaryWalrasianEquilibrium`: A `WalrasianEquilibrium` of the induced
  static economy — the market-clearing component of a stationary recursive competitive equilibrium,
  with the household dynamic program and law of motion supplied as inputs.

## Main statements

* `aggregate_accounting_of_pointwise`: Aggregate resource identities from pointwise current-wealth
  and next-resource equations.
* `aggregate_accounting_of_stationary_transition`: Aggregate resource identities when next-period
  wealth is a stationary kernel expectation.
* `aggregate_accounting_of_stationarity_marketClearing`: Levered Arrow-claim version with
  collateral supply and claim-market clearing.
* `stationaryEconomy_marketClears`: Per-coordinate aggregate clearing implies `MarketClears` for
  the induced stationary economy.
* `MarkovExchangeEconomy.stationaryEconomy_marketClears_of_transition`,
  `MarkovExchangeEconomy.stationaryEconomy_marketClears_of_collateral`: Market-clearing statements
  for one-good stationary economies with transition or collateral accounting.

## Tags

equilibrium, aggregate accounting, Markov economy, market clearing, stationarity
-/

@[expose] public section

namespace Econlib.Probability

namespace FiniteSupportKernel.StationaryFunctional

variable {Z Shock : Type*} [Fintype Shock] [DecidableEq Shock]
variable {K : FiniteSupportKernel Z Shock}

/-- The aggregate of `π.toAggregateFunctional` agrees with `π.aggregate`. -/
@[simp] lemma toAggregateFunctional_aggregate (π : K.StationaryFunctional)
    (f : Z → ℝ) :
    π.toAggregateFunctional.aggregate f = π.aggregate f :=
  rfl

end FiniteSupportKernel.StationaryFunctional

end Econlib.Probability

namespace Econlib.Equilibrium

open Econlib.Probability

variable {Z : Type*}

/-! ## Layer 1 — algebraic accounting identities -/

/-- Aggregate resource identities from pointwise budget equations: If
`wealth = consumption + capital` and `wealth = expectedIncome + (1 - δ)·capital` hold pointwise,
linearity of the aggregation functional gives `𝔼[wealth] = 𝔼[consumption] + 𝔼[capital]` and
`𝔼[expectedIncome] = 𝔼[consumption] + δ·𝔼[capital]`. -/
theorem aggregate_accounting_of_pointwise
    (A : AggregateFunctional Z)
    (wealth consumption capital expectedIncome : Z → ℝ) (delta : ℝ)
    (h_current : ∀ z, wealth z = consumption z + capital z)
    (h_next : ∀ z, wealth z = expectedIncome z + (1 - delta) * capital z) :
    A.aggregate wealth = A.aggregate consumption + A.aggregate capital ∧
      A.aggregate wealth =
        A.aggregate expectedIncome + (1 - delta) * A.aggregate capital ∧
      A.aggregate expectedIncome =
        A.aggregate consumption + delta * A.aggregate capital := by
  have h_current_agg :
      A.aggregate wealth = A.aggregate consumption + A.aggregate capital := by
    calc
      A.aggregate wealth
          = A.aggregate (fun z => consumption z + capital z) :=
              A.aggregate_congr h_current
      _ = A.aggregate consumption + A.aggregate capital :=
              A.aggregate_add consumption capital
  have h_next_agg :
      A.aggregate wealth =
        A.aggregate expectedIncome + (1 - delta) * A.aggregate capital := by
    calc
      A.aggregate wealth
          = A.aggregate (fun z => expectedIncome z + (1 - delta) * capital z) :=
              A.aggregate_congr h_next
      _ = A.aggregate expectedIncome + A.aggregate (fun z => (1 - delta) * capital z) :=
              A.aggregate_add expectedIncome (fun z => (1 - delta) * capital z)
      _ = A.aggregate expectedIncome + (1 - delta) * A.aggregate capital := by
              rw [A.aggregate_smul]
  refine ⟨h_current_agg, h_next_agg, ?_⟩
  linarith

variable {Shock : Type*} [Fintype Shock] [DecidableEq Shock]

/-- Stationary-kernel version of `aggregate_accounting_of_pointwise`: Stationarity of `π` converts
`𝔼_π[K.expect z wealth]` to `π.aggregate wealth`, and linearity gives the resource identities. -/
theorem aggregate_accounting_of_stationary_transition
    (K : FiniteSupportKernel Z Shock) (π : K.StationaryFunctional)
    (wealth consumption capital expectedIncome : Z → ℝ) (delta : ℝ)
    (h_current : ∀ z, wealth z = consumption z + capital z)
    (h_next :
      ∀ z, K.expect z wealth = expectedIncome z + (1 - delta) * capital z) :
    π.aggregate wealth = π.aggregate consumption + π.aggregate capital ∧
      π.aggregate wealth =
        π.aggregate expectedIncome + (1 - delta) * π.aggregate capital ∧
      π.aggregate expectedIncome =
        π.aggregate consumption + delta * π.aggregate capital := by
  have h_current_agg :
      π.aggregate wealth = π.aggregate consumption + π.aggregate capital := by
    calc
      π.aggregate wealth
          = π.aggregate (fun z => consumption z + capital z) :=
              π.aggregate_congr h_current
      _ = π.aggregate consumption + π.aggregate capital :=
              π.aggregate_add consumption capital
  have h_stationary : π.aggregate (fun z => K.expect z wealth) = π.aggregate wealth :=
    π.invariant wealth
  have h_next_congr :
      π.aggregate (fun z => K.expect z wealth) =
        π.aggregate (fun z => expectedIncome z + (1 - delta) * capital z) :=
    π.aggregate_congr h_next
  have h_next_linear :
      π.aggregate (fun z => expectedIncome z + (1 - delta) * capital z) =
        π.aggregate expectedIncome + (1 - delta) * π.aggregate capital := by
    calc
      π.aggregate (fun z => expectedIncome z + (1 - delta) * capital z)
          = π.aggregate expectedIncome + π.aggregate (fun z => (1 - delta) * capital z) :=
              π.aggregate_add expectedIncome (fun z => (1 - delta) * capital z)
      _ = π.aggregate expectedIncome + (1 - delta) * π.aggregate capital := by
              rw [π.aggregate_smul]
  have h_next_agg :
      π.aggregate wealth =
        π.aggregate expectedIncome + (1 - delta) * π.aggregate capital := by
    rw [← h_stationary, h_next_congr, h_next_linear]
  refine ⟨h_current_agg, h_next_agg, ?_⟩
  linarith

/-- Levered version of `aggregate_accounting_of_stationary_transition` with Arrow-claim market
clearing. The household retains `(1 - θ)(1 - δ)` of the durable and pledges `θ(1 - δ)` as
collateral; Arrow-claim clearing collapses both contributions to `(1 - δ)` on the aggregate. -/
theorem aggregate_accounting_of_stationarity_marketClearing
    (K : FiniteSupportKernel Z Shock) (π : K.StationaryFunctional)
    (wealth consumption capital expectedIncome
        claimDemand collateralSupply : Z → ℝ)
    (theta delta : ℝ)
    (h_current : ∀ z, wealth z = consumption z + capital z)
    (h_next :
      ∀ z, K.expect z wealth =
        expectedIncome z + (1 - theta) * (1 - delta) * capital z + claimDemand z)
    (h_collateral :
      ∀ z, collateralSupply z = theta * (1 - delta) * capital z)
    (h_market :
      ClearsMarket π.toAggregateFunctional claimDemand collateralSupply) :
    π.aggregate wealth = π.aggregate consumption + π.aggregate capital ∧
      π.aggregate wealth =
        π.aggregate expectedIncome + (1 - delta) * π.aggregate capital ∧
      π.aggregate expectedIncome =
        π.aggregate consumption + delta * π.aggregate capital := by
  have h_current_agg :
      π.aggregate wealth = π.aggregate consumption + π.aggregate capital := by
    calc
      π.aggregate wealth
          = π.aggregate (fun z => consumption z + capital z) :=
              π.aggregate_congr h_current
      _ = π.aggregate consumption + π.aggregate capital :=
              π.aggregate_add consumption capital
  have h_stationary :
      π.aggregate (fun z => K.expect z wealth) = π.aggregate wealth :=
    π.invariant wealth
  have h_next_linear :
      π.aggregate (fun z => K.expect z wealth) =
        π.aggregate expectedIncome
          + (1 - theta) * (1 - delta) * π.aggregate capital
          + π.aggregate claimDemand := by
    calc
      π.aggregate (fun z => K.expect z wealth)
          = π.aggregate (fun z =>
              expectedIncome z + (1 - theta) * (1 - delta) * capital z
                + claimDemand z) :=
              π.aggregate_congr h_next
      _ = π.aggregate (fun z =>
              expectedIncome z + (1 - theta) * (1 - delta) * capital z)
            + π.aggregate claimDemand :=
              π.aggregate_add
                (fun z => expectedIncome z + (1 - theta) * (1 - delta) * capital z)
                claimDemand
      _ = (π.aggregate expectedIncome
              + π.aggregate (fun z => (1 - theta) * (1 - delta) * capital z))
            + π.aggregate claimDemand := by
              rw [π.aggregate_add expectedIncome
                    (fun z => (1 - theta) * (1 - delta) * capital z)]
      _ = π.aggregate expectedIncome
            + (1 - theta) * (1 - delta) * π.aggregate capital
            + π.aggregate claimDemand := by
              rw [π.aggregate_smul]
  have h_market_eq : π.aggregate claimDemand = π.aggregate collateralSupply := by
    simpa [ClearsMarket, aggregateDemand, aggregateSupply] using h_market
  have h_collateral_agg :
      π.aggregate collateralSupply = theta * (1 - delta) * π.aggregate capital := by
    calc
      π.aggregate collateralSupply
          = π.aggregate (fun z => theta * (1 - delta) * capital z) :=
              π.aggregate_congr h_collateral
      _ = theta * (1 - delta) * π.aggregate capital :=
              π.aggregate_smul (theta * (1 - delta)) capital
  have h_next_agg :
      π.aggregate wealth =
        π.aggregate expectedIncome + (1 - delta) * π.aggregate capital := by
    have h := h_stationary.symm.trans h_next_linear
    rw [h_market_eq, h_collateral_agg] at h
    linarith
  refine ⟨h_current_agg, h_next_agg, ?_⟩
  linarith

/-! ## Layer 2 — the induced static economy -/

open Econlib.Preferences

variable {L : ℕ}

/-- A finite-support Markov kernel economy whose agents are states. Each state carries a preference
over commodity bundles and a nonnegative endowment. The shock space is finite; the state space may
be a continuum (Aiyagari/Bewley). At a stationary functional this induces a static `MeasureEconomy`
via `stationaryEconomy`. -/
structure MarkovExchangeEconomy (L : ℕ) where
  /-- The (possibly continuum) endogenous state space. -/
  State : Type*
  /-- The finite exogenous shock space. -/
  Shock : Type*
  /-- The shock space is finite. -/
  [shockFintype : Fintype Shock]
  /-- The shock space has decidable equality. -/
  [shockDecEq : DecidableEq Shock]
  /-- The policy-induced transition kernel on states. -/
  kernel : FiniteSupportKernel State Shock
  /-- Each state's preference over commodity bundles. -/
  pref : State → PreferenceRel (Fin L → ℝ)
  /-- Each state's endowment (income net of steady-state replacement investment). -/
  endow : State → (Fin L → ℝ)
  /-- Endowments are nonnegative. -/
  endow_mem : ∀ s, endow s ∈ nonnegOrthant L

attribute [instance] MarkovExchangeEconomy.shockFintype MarkovExchangeEconomy.shockDecEq

/-- The static `MeasureEconomy` induced by `M` at the stationary functional `π`. Aggregation is the
stationary law `π`, coerced to a `PositiveLinearFunctional`. -/
def MarkovExchangeEconomy.stationaryEconomy (M : MarkovExchangeEconomy L)
    (π : M.kernel.StationaryFunctional) : MeasureEconomy L where
  Agents := M.State
  agg := ⟨π.toAggregateFunctional.toPositiveLinearFunctional⟩
  pref := M.pref
  endow := M.endow
  endow_mem := M.endow_mem

/-- The induced static economy aggregates by the stationary functional `π`. -/
@[simp] lemma stationaryEconomy_agg_aggregate (M : MarkovExchangeEconomy L)
    (π : M.kernel.StationaryFunctional) (f : M.State → ℝ) :
    (M.stationaryEconomy π).agg.toPLF.aggregate f = π.aggregate f :=
  rfl

/-- A **stationary Walrasian equilibrium**: A `WalrasianEquilibrium` of the static economy induced
by the stationary functional `π`. This is the market-clearing component that a stationary recursive
competitive equilibrium must satisfy. Household dynamic-program optimality (policy functions
solving the Bellman problem) and consistency of the law of motion (`π` as the invariant law
generated by the optimal policy) are inputs here, not derived — so this is the static projection of
a recursive equilibrium, not the recursive equilibrium itself. -/
abbrev MarkovExchangeEconomy.StationaryWalrasianEquilibrium (M : MarkovExchangeEconomy L)
    (π : M.kernel.StationaryFunctional) : Type _ :=
  (M.stationaryEconomy π).WalrasianEquilibrium

/-! ## Layer 3 — accounting recast as market clearing -/

open scoped Matrix

/-- Per-coordinate aggregate clearing (`∀ l, 𝔼[alloc · l] = 𝔼[endow · l]`) implies `MarketClears`
for the induced stationary economy at any price. -/
theorem stationaryEconomy_marketClears (M : MarkovExchangeEconomy L)
    (π : M.kernel.StationaryFunctional) (alloc : M.State → (Fin L → ℝ)) (p : Fin L → ℝ)
    (h_clear : ∀ l, π.aggregate (fun s => alloc s l) = π.aggregate (fun s => M.endow s l)) :
    (M.stationaryEconomy π).MarketClears p alloc := by
  have hzero : (M.stationaryEconomy π).aggregateExcess alloc = 0 := by
    funext l
    change π.aggregate (fun s => alloc s l) - π.aggregate (fun s => M.endow s l) = 0
    rw [h_clear l]; ring
  refine ⟨fun l => ?_, ?_⟩
  · rw [hzero]; simp
  · rw [hzero, dotProduct_zero]

/-- If `endow s 0 = expectedIncome s - δ·capital s` pointwise and the aggregate resource identity
`𝔼[expectedIncome] = 𝔼[consumption] + δ·𝔼[capital]` holds, the single-good stationary economy
market-clears at the consumption allocation. -/
private lemma stationaryEconomy_marketClears_of_resource (M : MarkovExchangeEconomy 1)
    (π : M.kernel.StationaryFunctional)
    (consumption capital expectedIncome : M.State → ℝ) (delta : ℝ) (p : Fin 1 → ℝ)
    (h_endow : ∀ s, M.endow s 0 = expectedIncome s - delta * capital s)
    (h_resource :
      π.aggregate expectedIncome = π.aggregate consumption + delta * π.aggregate capital) :
    (M.stationaryEconomy π).MarketClears p (fun s => ![consumption s]) := by
  refine stationaryEconomy_marketClears M π (fun s => ![consumption s]) p (fun l => ?_)
  fin_cases l
  have hendow_agg : π.aggregate (fun s => M.endow s 0) = π.aggregate consumption := by
    rw [π.aggregate_congr h_endow, π.aggregate_sub, π.aggregate_smul]
    linarith
  simpa using hendow_agg.symm

/-- A single-good stationary Markov economy whose endowment is income net of replacement investment
(`expectedIncome - δ·capital`) market-clears at the stationary consumption allocation. -/
theorem MarkovExchangeEconomy.stationaryEconomy_marketClears_of_transition
    (M : MarkovExchangeEconomy 1) (π : M.kernel.StationaryFunctional)
    (wealth consumption capital expectedIncome : M.State → ℝ) (delta : ℝ) (p : Fin 1 → ℝ)
    (h_current : ∀ s, wealth s = consumption s + capital s)
    (h_next : ∀ s, M.kernel.expect s wealth = expectedIncome s + (1 - delta) * capital s)
    (h_endow : ∀ s, M.endow s 0 = expectedIncome s - delta * capital s) :
    (M.stationaryEconomy π).MarketClears p (fun s => ![consumption s]) := by
  obtain ⟨_, _, h_resource⟩ :=
    aggregate_accounting_of_stationary_transition M.kernel π
      wealth consumption capital expectedIncome delta h_current h_next
  exact stationaryEconomy_marketClears_of_resource M π consumption capital expectedIncome
    delta p h_endow h_resource

/-- The levered collateral economy (Arrow-claim market clearing built in) market-clears at the
stationary consumption allocation. -/
theorem MarkovExchangeEconomy.stationaryEconomy_marketClears_of_collateral
    (M : MarkovExchangeEconomy 1) (π : M.kernel.StationaryFunctional)
    (wealth consumption capital expectedIncome claimDemand collateralSupply : M.State → ℝ)
    (theta delta : ℝ) (p : Fin 1 → ℝ)
    (h_current : ∀ s, wealth s = consumption s + capital s)
    (h_next : ∀ s, M.kernel.expect s wealth =
      expectedIncome s + (1 - theta) * (1 - delta) * capital s + claimDemand s)
    (h_collateral : ∀ s, collateralSupply s = theta * (1 - delta) * capital s)
    (h_market : ClearsMarket π.toAggregateFunctional claimDemand collateralSupply)
    (h_endow : ∀ s, M.endow s 0 = expectedIncome s - delta * capital s) :
    (M.stationaryEconomy π).MarketClears p (fun s => ![consumption s]) := by
  obtain ⟨_, _, h_resource⟩ :=
    aggregate_accounting_of_stationarity_marketClearing M.kernel π
      wealth consumption capital expectedIncome claimDemand collateralSupply
      theta delta h_current h_next h_collateral h_market
  exact stationaryEconomy_marketClears_of_resource M π consumption capital expectedIncome
    delta p h_endow h_resource

end Econlib.Equilibrium
