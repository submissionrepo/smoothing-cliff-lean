/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Equilibrium.MarkovStationary
import Mathlib

/-!
# Aggregation / recursive-equilibrium non-vacuity witnesses

Compile-time semantic witnesses for the macro / heterogeneous-agent face of `Econlib.Equilibrium`:
`AgentAggregation`, `AggregateAccounting`, and `LimitedEnforcement`. The aggregate-accounting and
recursive-equilibrium witnesses are anchored on the concrete single-good, two-state i.i.d.-uniform
Markov exchange economy of `EconlibExamples.Equilibrium.MarkovStationary` (state space `Bool`,
uniform stationary functional `π f = f false / 2 + f true / 2`, unit endowment in every state). The
limited-enforcement witness is anchored on an explicit two-state finite Markov chain with a
*constant* payoff stream, where the present value is the geometric sum `c / (1 - β)`.

## The hand-computation that anchors every numeric claim

The stationary functional is the uniform average over `Bool`:

* `π.aggregate (fun _ => 1) = 1/2 + 1/2 = 1` — the stationary distribution is uniform with total
  mass `1`.
* Aggregate endowment in the good: `π (s ↦ endow s 0) = 1/2·1 + 1/2·1 = 1`.
* Aggregate (autarkic) demand in the good: `π (s ↦ alloc s 0) = 1/2·1 + 1/2·1 = 1`.
* Aggregate supply equals aggregate demand equals `1`: Markets clear *exactly*.

For limited enforcement, with discount `β = 1/2` and a constant payoff `c = 1` at every history,
the present value is the geometric sum

`PV = ∑_{τ} β^τ · c = 1 + 1/2 + 1/4 + ⋯ = c / (1 - β) = 1 / (1 - 1/2) = 2`,

and the constant continuation value `V ≡ 2` is the unique bounded Bellman fixed point:
`V = X + β · 𝔼[V] = 1 + (1/2)·2 = 2`. (A discounting off-by-one — e.g. `c / (1 + β) = 2/3`, or a
shift `c·β / (1 - β) = 1` — would break the equality `V = PV = 2`.)

## What each block catches

* **Aggregate accounting** (`aggregate_accounting_of_pointwise`,
  `stationaryEconomy_marketClears_of_transition`, `..._of_collateral`,
  `stationaryEconomy_agg_aggregate`, `toAggregateFunctional_aggregate`) — a measure/weight mismatch
  in the cross-agent aggregation: The uniform `1/2` weights, not unweighted counting, must collapse
  the per-state identities to the aggregate ones, and the induced static economy's aggregator must
  *be* `π`, not the default `Fintype` counting sum.
* **Stationary Walrasian equilibrium** (`StationaryWalrasianEquilibrium`) — a vacuous
  equilibrium abbreviation: The abbreviation is shown inhabited by a concrete object.
* **Limited enforcement** (`participates_iff`, `V_eq_presentValue`) — a present-value discounting /
  off-by-one error: The continuation value `2` equals the geometric present value `1 / (1 - 1/2)`.
* **Fintype aggregation instances** (`AgentAggregation.instFintype`,
  `FaithfulAggregation.instFintype`) — a wrong default aggregator on a finite agent space: The
  counting sum over `Bool` of `![3, 5]` must reduce to `8`, and the instance must be faithful.
-/

noncomputable section

namespace EconlibTest.Equilibrium.Aggregation

open Econlib.Equilibrium Econlib.Probability Matrix
open EconlibExamples.Equilibrium.MarkovStationary
  (markovKernel markovEcon stationaryπ markovPrice markovAlloc markovEquilibrium)

/-! ## Block 1: Aggregate market clearing at the stationary distribution

The stationary functional `π` is the uniform average over `Bool`. We first anchor the aggregate
numerically, then exercise the accounting → clearing pipeline. -/

/-- **The stationary mass is `1`** (`π.aggregate 1 = 1/2 + 1/2`): The uniform stationary functional
is a probability functional. This is `aggregate_one` re-anchored numerically; a weight mismatch
(e.g. unweighted counting, giving `2`) would break it. -/
theorem stationary_mass_one : stationaryπ.aggregate (fun _ => 1) = 1 := by
  simp [stationaryπ]; norm_num

/-- **Aggregate endowment in the single good is `1`**: `π (s ↦ endow s 0) = 1/2·1 + 1/2·1 = 1`.
This is the aggregate *supply* the market must clear. -/
theorem aggregate_endow_eq_one :
    stationaryπ.aggregate (fun s => markovEcon.endow s 0) = 1 := by
  simp [stationaryπ, markovEcon]; norm_num

/-- **Aggregate (autarkic) demand in the single good is `1`**: `π (s ↦ alloc s 0) = 1/2 + 1/2 = 1`,
equal to aggregate supply — markets clear *exactly* on the aggregate. -/
theorem aggregate_alloc_eq_one :
    stationaryπ.aggregate (fun s => markovAlloc s 0) = 1 := by
  simp [stationaryπ, markovAlloc]; norm_num

/-- **`stationaryEconomy_agg_aggregate`**: The induced static economy's aggregator *is* the
stationary functional `π`, not the default `Fintype` counting sum. Anchored: The aggregate of the
endowment statistic is `1` (uniform `1/2`-weights), not `2` (counting). -/
theorem stationaryEconomy_agg_aggregate_witness :
    (markovEcon.stationaryEconomy stationaryπ).agg.toPLF.aggregate
        (fun s => markovEcon.endow s 0) = 1 := by
  rw [stationaryEconomy_agg_aggregate]
  exact aggregate_endow_eq_one

/-- **`toAggregateFunctional_aggregate` bridge**: The coerced `AggregateFunctional` agrees with the
stationary functional's own aggregate. Anchored at the endowment statistic, giving `1`. -/
theorem toAggregateFunctional_aggregate_witness :
    stationaryπ.toAggregateFunctional.aggregate (fun s => markovEcon.endow s 0) = 1 := by
  rw [FiniteSupportKernel.StationaryFunctional.toAggregateFunctional_aggregate]
  exact aggregate_endow_eq_one

/-! ### Aggregate accounting on genuinely nonconstant data

The constant-`1` data of an earlier revision could not discriminate counting from averaging (both
collapse `1 = 1 + 0`), nor could `δ = 0` reveal a depreciation-term sign error. We anchor the
accounting on **nonconstant** capital and a **nonzero** depreciation `δ = 1/4`, with every aggregate
hand-computed to an exact rational, so a counting-vs-averaging mismatch (which would, e.g., report
aggregate wealth `10` instead of `5`) is caught.

The data (state space `Bool`, uniform `1/2`-weights):

* `capital = (false ↦ 0, true ↦ 2)`, aggregate `0/2 + 2/2 = 1`;
* `consumption = (false ↦ 3, true ↦ 5)`, aggregate `3/2 + 5/2 = 4`;
* `wealth = consumption + capital = (false ↦ 3, true ↦ 7)`, aggregate `3/2 + 7/2 = 5`;
* `δ = 1/4`, so `expectedIncome = wealth − (3/4)·capital = (false ↦ 3, true ↦ 11/2)`,
  aggregate `3/2 + 11/4 = 17/4`.

The three aggregate identities then read `5 = 4 + 1`, `5 = 17/4 + (3/4)·1`, `17/4 = 4 + (1/4)·1`. -/

/-- Nonconstant capital `false ↦ 0`, `true ↦ 2` (aggregate `1`). -/
def accCapital : Bool → ℝ := fun b => if b then 2 else 0

/-- Nonconstant consumption `false ↦ 3`, `true ↦ 5` (aggregate `4`). -/
def accConsumption : Bool → ℝ := fun b => if b then 5 else 3

/-- Wealth `= consumption + capital`: `false ↦ 3`, `true ↦ 7` (aggregate `5`). -/
def accWealth : Bool → ℝ := fun b => if b then 7 else 3

/-- Expected income `= wealth − (3/4)·capital`: `false ↦ 3`, `true ↦ 11/2` (aggregate `17/4`). -/
def accExpectedIncome : Bool → ℝ := fun b => if b then 11 / 2 else 3

private def accAgg (f : Bool → ℝ) : ℝ :=
  stationaryπ.toAggregateFunctional.toPositiveLinearFunctional.aggregate f

/-- **`aggregate_accounting_of_pointwise`** (the measure/weight-mismatch catcher) on nonconstant
data with nonzero depreciation `δ = 1/4`: pointwise budget balance aggregates to the three resource
identities. The uniform `1/2`-weights (not counting) collapse the per-state identities; each
aggregate is the exact rational hand-computed above, so a counting aggregator (reporting `10` for
aggregate wealth) or a depreciation-sign error would fail. -/
theorem aggregate_accounting_of_pointwise_witness :
    (accAgg accWealth = accAgg accConsumption + accAgg accCapital) ∧
      (accAgg accWealth = accAgg accExpectedIncome + (1 - (1 / 4 : ℝ)) * accAgg accCapital) ∧
      (accAgg accExpectedIncome = accAgg accConsumption + (1 / 4 : ℝ) * accAgg accCapital) :=
  aggregate_accounting_of_pointwise
    (A := stationaryπ.toAggregateFunctional)
    (wealth := accWealth) (consumption := accConsumption) (capital := accCapital)
    (expectedIncome := accExpectedIncome) (delta := 1 / 4)
    (fun b => by cases b <;> norm_num [accWealth, accConsumption, accCapital])
    (fun b => by cases b <;> norm_num [accWealth, accExpectedIncome, accCapital])

/-- **Exact aggregate anchors** for the accounting data: `𝔼[wealth] = 5`, `𝔼[consumption] = 4`,
`𝔼[capital] = 1`, `𝔼[expectedIncome] = 17/4`. These pin the *numbers*, so the identities of
`aggregate_accounting_of_pointwise_witness` are `5 = 4 + 1`, `5 = 17/4 + (3/4)·1`, `17/4 = 4 +
(1/4)·1`, all of which a counting aggregator would violate. -/
theorem aggregate_accounting_anchors :
    accAgg accWealth = 5 ∧ accAgg accConsumption = 4 ∧
      accAgg accCapital = 1 ∧ accAgg accExpectedIncome = 17 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · change stationaryπ.aggregate _ = _
      simp only [stationaryπ, accWealth, accConsumption, accCapital, accExpectedIncome]
      norm_num

/-- **`stationaryEconomy_marketClears_of_transition`** (aggregate demand = aggregate supply): The
single-good stationary economy clears at the autarkic consumption allocation, with **nonzero capital
`k = 2` and nonzero depreciation `δ = 1/4`**. The steady-state resource chain is
`wealth ≡ consumption + capital = 1 + 2 = 3`, `expect[wealth] = expectedIncome + (1−δ)·capital`
(`3 = 3/2 + (3/4)·2`), and `endow = expectedIncome − δ·capital` (`1 = 3/2 − (1/4)·2`). The
depreciation and capital terms are genuinely load-bearing — a δ-sign error in `h_endow` or `h_next`
(which the `δ = 0` data could not catch) makes these equalities fail. Clearing then says aggregate
demand `1` equals aggregate supply `1`. -/
theorem stationaryEconomy_marketClears_of_transition_witness :
    (markovEcon.stationaryEconomy stationaryπ).MarketClears markovPrice (fun _ => ![1]) :=
  MarkovExchangeEconomy.stationaryEconomy_marketClears_of_transition markovEcon stationaryπ
    (wealth := fun _ => 3) (consumption := fun _ => 1) (capital := fun _ => 2)
    (expectedIncome := fun _ => 3 / 2) (delta := 1 / 4) (p := markovPrice)
    (fun _ => by norm_num)
    (fun s => by
      simp only [markovEcon, markovKernel, FiniteSupportKernel.expect, FinDist.expect_const]
      norm_num)
    (fun _ => by simp only [markovEcon]; norm_num)

/-- **`stationaryEconomy_marketClears_of_collateral`** (Arrow-claim variant) on a **genuinely
levered** economy: collateralization rate `θ = 1/2`, capital `k = 2`, depreciation `δ = 1/4`, with a
**nonzero** Arrow-claim market `claimDemand ≡ collateralSupply ≡ 3/4`. The collateral identity
`collateralSupply = θ·(1−δ)·capital` reads `3/4 = (1/2)·(3/4)·2`, the claim market clears at the
nonzero level `3/4 = 3/4`, and the resource chain `expect[wealth] = expectedIncome + (1−θ)(1−δ)·k +
claimDemand` reads `3 = 3/2 + (1/2)(3/4)·2 + 3/4`. A swapped `θ ↔ 1−θ` or a dropped claim term would
break these — invisible at the earlier all-zero collateral data. Clearing is still at the autarkic
`(fun _ => ![1])`. -/
theorem stationaryEconomy_marketClears_of_collateral_witness :
    (markovEcon.stationaryEconomy stationaryπ).MarketClears markovPrice (fun _ => ![1]) :=
  MarkovExchangeEconomy.stationaryEconomy_marketClears_of_collateral markovEcon stationaryπ
    (wealth := fun _ => 3) (consumption := fun _ => 1) (capital := fun _ => 2)
    (expectedIncome := fun _ => 3 / 2) (claimDemand := fun _ => 3 / 4)
    (collateralSupply := fun _ => 3 / 4)
    (theta := 1 / 2) (delta := 1 / 4) (p := markovPrice)
    (fun _ => by norm_num)
    (fun s => by
      simp only [markovEcon, markovKernel, FiniteSupportKernel.expect, FinDist.expect_const]
      norm_num)
    (fun _ => by norm_num)
    (by simp only [ClearsMarket, aggregateDemand, aggregateSupply])
    (fun _ => by simp only [markovEcon]; norm_num)

/-! ## Block 2: Stationary Walrasian equilibrium is inhabited

`MarkovExchangeEconomy.StationaryWalrasianEquilibrium` is an abbreviation for a Walrasian
equilibrium of the induced static economy. The example file builds one (`markovEquilibrium`); here
we certify the type is inhabited, so the definition is not vacuous. -/

/-- **`StationaryWalrasianEquilibrium` is inhabited**: The concrete economy admits a stationary
Walrasian equilibrium (the autarkic one). The definition is shown inhabited, not just defined. -/
theorem stationaryWalrasianEquilibrium_nonempty :
    Nonempty (markovEcon.StationaryWalrasianEquilibrium stationaryπ) :=
  ⟨markovEquilibrium⟩

/-- The equilibrium's price is the single-good unit price (a constructor-spelling sanity anchor). -/
theorem markovEquilibrium_price : markovEquilibrium.price = markovPrice := rfl

/-- The equilibrium's allocation is autarkic (each state consumes its endowment; a constructor
sanity anchor). -/
theorem markovEquilibrium_alloc : markovEquilibrium.alloc = markovAlloc := rfl

/-- **Semantic equilibrium check** (not a mere field projection): the constructed
`markovEquilibrium` actually *clears* markets — its `clears` field gives weak excess supply
everywhere together with zero excess value `p ⬝ᵥ aggregateExcess = 0`. This consumes the genuine
equilibrium content, so it would fail for an object that merely had the right `price`/`alloc`
spelling but did not clear. -/
theorem markovEquilibrium_clears :
    (∀ l, (markovEcon.stationaryEconomy stationaryπ).aggregateExcess markovEquilibrium.alloc l ≤ 0)
      ∧ markovEquilibrium.price ⬝ᵥ
          (markovEcon.stationaryEconomy stationaryπ).aggregateExcess markovEquilibrium.alloc = 0 :=
  ⟨markovEquilibrium.clears.excess_nonpos, markovEquilibrium.clears.value_zero⟩

/-- **Semantic optimality check**: in `markovEquilibrium` every (representative) agent's allocation
is demand-optimal in its budget set — the `isOptimal` field, consumed directly. -/
theorem markovEquilibrium_isOptimal :
    ∀ s, markovEquilibrium.alloc s ∈
      (markovEcon.stationaryEconomy stationaryπ).demand markovEquilibrium.price s :=
  markovEquilibrium.isOptimal

/-! ## Block 3: Limited enforcement — present value of a constant stream

We instantiate `LimitedEnforcementFeasible` on an explicit two-state Markov chain with a
*constant* payoff `X ≡ 1`, discount `β = 1/2`, default `D ≡ 0`, and continuation value `V ≡ 2`. The
geometric present value is `1 / (1 - 1/2) = 2`, so `V_eq_presentValue` forces `2 = PV`, catching a
discounting off-by-one. -/

/-- A concrete two-state finite Markov chain on `Bool`: The i.i.d.-uniform chain (every state
transitions to the uniform distribution). The transition law is immaterial to the constant-stream
present value, but a genuine `FiniteMarkovChain` is needed to form the histories. -/
def boolChain : Econlib.Probability.FiniteMarkovChain Bool where
  transition _ := FinDist.uniform

/-- The constant payoff stream `X ≡ 1`. -/
def constPayoff : Econlib.Probability.AdaptedProcess Bool :=
  Econlib.Probability.AdaptedProcess.const 1

/-- The default (outside-option) value `D ≡ 0`. -/
def zeroDefault : DefaultValue Bool :=
  Econlib.Probability.AdaptedProcess.const 0

/-- The candidate continuation value `V ≡ 2 = 1 / (1 - 1/2)`, the present value of the constant
unit stream at discount `1/2`. -/
def constValue : Econlib.Probability.AdaptedProcess Bool :=
  Econlib.Probability.AdaptedProcess.const 2

/-- The constant payoff stream is bounded by `1`. -/
theorem constPayoff_bounded : constPayoff.Bounded 1 := by
  intro t h
  simp [constPayoff, Econlib.Probability.AdaptedProcess.const]

/-- **`participates_iff`**: The constant value `V ≡ 2` participates against the default `D ≡ 0`
exactly because `0 ≤ 2` at every history. This unfolds the participation predicate to its pointwise
form; a reversed orientation (`V ≤ D`) would fail. -/
theorem participates_iff_witness :
    Participates constValue zeroDefault ↔
      ∀ t (h : Econlib.Probability.History Bool t),
        zeroDefault.val t h ≤ constValue.val t h :=
  participates_iff constValue zeroDefault

/-- The constant value participates: `0 ≤ 2` at every history. -/
theorem constValue_participates : Participates constValue zeroDefault := by
  rw [participates_iff_witness]
  intro t h
  simp [constValue, zeroDefault, Econlib.Probability.AdaptedProcess.const]

/-- The constant value `V ≡ 2` satisfies the Bellman recursion against payoff `X ≡ 1` at discount
`β = 1/2`: `2 = 1 + (1/2)·∑ s', P(s')·2 = 1 + (1/2)·2 = 2`. The transition probabilities sum to
`1`, so the conditional expectation of the constant `2` is `2`. -/
theorem constValue_bellman :
    ∀ t (h : Econlib.Probability.History Bool t),
      constValue.val t h = constPayoff.val t h
        + (1/2 : ℝ) * ∑ s' : Bool, (boolChain.transition h.lastNode) s' *
            constValue.val (t + 1) (h.extend s') := by
  intro t h
  have hsum : ∑ s' : Bool, (boolChain.transition h.lastNode) s' *
      constValue.val (t + 1) (h.extend s') = 2 := by
    simp only [constValue, Econlib.Probability.AdaptedProcess.const, ← Finset.sum_mul,
      (boolChain.transition h.lastNode).sum_one, one_mul]
  rw [hsum]
  simp [constValue, constPayoff, Econlib.Probability.AdaptedProcess.const]
  ring

/-- A **`LimitedEnforcementFeasible`** contract on the concrete chain: Payoff `X ≡ 1`, discount
`1/2`, default `D ≡ 0`, continuation value `V ≡ 2`. The Bellman recursion and participation are the
two computed facts above. -/
def constFeasible :
    LimitedEnforcementFeasible boolChain (1/2 : ℝ) constPayoff zeroDefault where
  V := constValue
  bellman := constValue_bellman
  participates := constValue_participates

/-- **`LimitedEnforcementFeasible.V_eq_presentValue`** (the discounting / off-by-one catcher): The
bounded continuation value of the feasible contract equals the canonical present value of the
payoff stream at every history. -/
theorem V_eq_presentValue_witness :
    ∀ t (h : Econlib.Probability.History Bool t),
      constFeasible.V.val t h
        = Econlib.Probability.presentValue boolChain (1/2 : ℝ) constPayoff t h :=
  constFeasible.V_eq_presentValue boolChain (1/2 : ℝ) (by norm_num) (by norm_num)
    constPayoff zeroDefault constPayoff_bounded ⟨2, fun t h => by
      simp [constFeasible, constValue, Econlib.Probability.AdaptedProcess.const]⟩

/-- The iterated conditional expectation of the constant unit stream is `1` at every horizon — the
conditional expectation of a constant is that constant (the transition probabilities sum to `1` at
each step). Proved directly by induction on the horizon `τ`, *independently* of the Bellman /
present-value machinery under test. -/
theorem iterCondExp_constPayoff (τ : ℕ) :
    ∀ t (h : Econlib.Probability.History Bool t),
      Econlib.Probability.iterCondExp boolChain constPayoff τ t h = 1 := by
  induction τ with
  | zero =>
    intro t h
    simp [Econlib.Probability.iterCondExp, constPayoff, Econlib.Probability.AdaptedProcess.const]
  | succ k ih =>
    intro t h
    rw [Econlib.Probability.iterCondExp_succ]
    simp_rw [ih (t + 1)]
    rw [← Finset.sum_mul, (boolChain.transition h.lastNode).sum_one, one_mul]

/-- **The present value of the constant unit stream is exactly `2 = 1 / (1 - 1/2)`** — the
**geometric sum, evaluated directly** from the definition `presentValue = ∑' τ, β^τ · iterCondExp`.
Each `iterCondExp` term is `1` (above), so `PV = ∑' τ, (1/2)^τ = 1 / (1 - 1/2) = 2` by
`tsum_geometric_of_lt_one`. This does *not* route through `V_eq_presentValue_witness`
(the uniqueness
theorem under test), so it is an independent off-by-one anchor: a shift (`c·β / (1 - β) = 1`) or a
wrong denominator (`c / (1 + β) = 2/3`) would break it. -/
theorem presentValue_const_eq_two :
    ∀ t (h : Econlib.Probability.History Bool t),
      Econlib.Probability.presentValue boolChain (1/2 : ℝ) constPayoff t h = 2 := by
  intro t h
  unfold Econlib.Probability.presentValue
  -- each summand is `(1/2)^τ · 1 = (1/2)^τ`; the geometric tsum is `1/(1-1/2) = 2`.
  simp_rw [iterCondExp_constPayoff, mul_one]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-! ## Block 4: Fintype aggregation instances over a concrete model

The default `AgentAggregation` on a `Fintype` agent space is the counting sum, and it is
faithful. We exercise both `instFintype` instances by a `Finset.univ` sum over the two aggregated
agents that reduces to a hand-computed number. -/

/-- A concrete statistic over the two-agent space `Bool`: `false ↦ 3`, `true ↦ 5`. -/
def boolStat : Bool → ℝ := fun b => if b then 5 else 3

/-- **`AgentAggregation.instFintype` over a `Finset.univ` sum** (`agg_fintype`): The default
aggregation of `boolStat` over `Bool` is the counting sum `∑ i, boolStat i = 3 + 5 = 8`. The
instance must resolve to counting (not, say, an average), so the sum reduces to `8`, not `4`. -/
theorem agentAggregation_fintype_sum :
    AgentAggregation.agg Bool boolStat = 8 := by
  rw [AgentAggregation.agg_fintype]
  simp [boolStat]; norm_num

/-- The aggregation map literally *is* the `Finset.univ` counting sum. -/
theorem agentAggregation_eq_univ_sum (f : Bool → ℝ) :
    AgentAggregation.agg Bool f = ∑ i : Bool, f i :=
  AgentAggregation.agg_fintype Bool f

/-- **`FaithfulAggregation.instFintype`, exact value**: The counting aggregation over `Bool` of the
indicator `1_{false}` is **exactly `1`** — `(if false = false then 1 else 0) + (if true = false then
1 else 0) = 1 + 0`. This is the *counting* mass; an averaging aggregator would instead give
`1/2`, so
the exact equality (not just positivity) discriminates counting from averaging. -/
theorem faithfulAggregation_indicator_eq_one :
    (AgentAggregation.toPLF (Z := Bool)).aggregate
        (fun z : Bool => if z = false then (1 : ℝ) else 0) = 1 := by
  change AgentAggregation.agg Bool (fun z : Bool => if z = false then (1 : ℝ) else 0) = 1
  rw [AgentAggregation.agg_fintype]
  simp

/-- **`FaithfulAggregation.instFintype`**: The counting aggregation over `Bool` is faithful, so the
indicator aggregate is strictly positive. Here it is the exact `1 > 0` (via
`faithfulAggregation_indicator_eq_one`), confirming the faithfulness witness lands on the counting
mass `1`, not an averaging `1/2`. -/
theorem faithfulAggregation_indicator_pos :
    0 < (AgentAggregation.toPLF (Z := Bool)).aggregate
        (fun z : Bool => if z = false then (1 : ℝ) else 0) := by
  rw [faithfulAggregation_indicator_eq_one]; norm_num

end EconlibTest.Equilibrium.Aggregation

end
