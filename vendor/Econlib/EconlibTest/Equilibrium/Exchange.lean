/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Equilibrium.CobbDouglasEdgeworth
import EconlibExamples.Equilibrium.FiniteExistence
import Mathlib

/-!
# Exchange-economy core non-vacuity witnesses

Compile-time semantic witnesses for the `Econlib.Equilibrium` exchange-economy core (`Basic`,
`Economy`, `CobbDouglasDemand`, `LinearEconomy`, `MarketClearing`, `Existence`). The witnesses are
anchored on the concrete two-good / two-agent **Cobb–Douglas Edgeworth box** of
`EconlibExamples.Equilibrium.CobbDouglasEdgeworth` (and the three-agent linear economy of
`...FiniteExistence`), so every abstract budget-set / demand / Walras-law / equilibrium statement
is forced through real numbers rather than only an abstract hypothesis.

The hand-computation that anchors every numeric claim (symmetric tastes `α = (1/2, 1/2)`,
endowments `e₀ = (2,1)`, `e₁ = (1,2)`, equilibrium price `(1,1)`):

* Wealth of each agent at `(1,1)`: `p ⬝ᵥ eₐ = 3`.
* Cobb–Douglas demand at price `p`, wealth `w`: `xₗ = (αₗ / ∑α) · w / pₗ = (1/2) · w / pₗ`; at
  `p = (1,1)`, `w = 3`, this is `(3/2, 3/2)` for both agents.
* Aggregate demand `(3,3)` equals the aggregate endowment `(3,3)`: Markets clear *exactly*.

## What each block catches

* **Budget set** — a wealth/price-orientation error (e.g. comparing `p ⬝ᵥ x` against `w` with the
  inequality reversed, or scaling prices the wrong way). `budgetSetAt_scale` is checked at the
  *true* scaling convention `budgetSetAt (t • p) (t * w) = budgetSetAt p w`.
* **Demand** — a price-homogeneity-degree mistake (`demand` is degree `0`, so
  `demand (2•p) = demand p`, not degree `1`), and a Cobb–Douglas closed-form sign/share error: The
  share bundle is exactly `(3/2, 3/2)`, not its reciprocal.
* **Walras's law** — a sign error in `p ⬝ᵥ excess = 0`; checked on the concrete equilibrium where
  excess is *identically* zero, and the abstract `walras_law_over` is exercised on real
  budget-binding data.
* **Existence** — a vacuous existence claim: `exists_equilibrium_data` / `exists_quasi_equilibrium`
  / `quasi_to_walrasian` are invoked with every hypothesis discharged from the concrete economy's
  actual regularity and irreducibility instances, so the chain (and its truncated-simplex
  scaffolding, consumed transitively) runs on real data.

The internal `truncatedSimplex_*` / `maxDotTruncated_*` lemmas of `Existence.lean` are scaffolding
for the Kakutani fixed point; their honest consumer is the headline `exists_equilibrium`, which we
exercise here. They are genuinely reached (verified by source audit), so no per-helper test is
written.
-/

noncomputable section

namespace EconlibTest.Equilibrium.Exchange

open Econlib.Equilibrium Econlib.Preferences Econlib.Optimization Matrix
open EconlibExamples.Equilibrium.CobbDouglasEdgeworth (economy economy_regular cdU edgeEndow
  edgePrice edgeAlloc edgeworthEquilibrium edgeworth_demand_optimal edge_wealth
  edgeEndow_pos edgeworth_aggregateExcess_zero edgeworth_gains_from_trade)

/-! ## Block 1: Budget set at strictly positive prices

The Edgeworth equilibrium price `(1,1)` is strictly positive, agent `0` has wealth `3`. We
check the budget-set API directly against `budgetSetAt (1,1) 3`. -/

/-- The equilibrium price is strictly positive in every good. -/
theorem edgePrice_pos : ∀ l, 0 < edgePrice l := fun l => by fin_cases l <;> norm_num [edgePrice]

/-- Agent `0`'s wealth at the equilibrium price is `3` (the price-bundle pairing, anchored). -/
theorem agent0_wealth : edgePrice ⬝ᵥ economy.endow (0 : Fin 2) = 3 := edge_wealth 0

/-- **`mem_budgetSetAt` unfolds correctly, on the budget boundary** (`3 ≤ 3`): The equilibrium
bundle
`(3/2, 3/2)` is in `budgetSetAt (1,1) 3`. (Boundary membership alone does *not* discriminate the
wealth/price orientation — see `mem_budgetSetAt_strict_affordable` / `mem_budgetSetAt_unaffordable`
below, which do.) -/
theorem mem_budgetSetAt_witness :
    (![3/2, 3/2] : Fin 2 → ℝ) ∈ budgetSetAt edgePrice 3 := by
  rw [mem_budgetSetAt]
  refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
  simp [edgePrice, dotProduct, Fin.sum_univ_two]

/-- **Orientation guard, positive side** (`mem_budgetSetAt`): The *strictly affordable* bundle
`(1, 1)` has value `1·1 + 1·1 = 2 < 3 = w`, so it lies strictly inside `budgetSetAt (1,1) 3`. A
reversed orientation (`w ≤ p ⬝ᵥ x`) would *exclude* it, so this witness catches the flip. -/
theorem mem_budgetSetAt_strict_affordable :
    (![1, 1] : Fin 2 → ℝ) ∈ budgetSetAt edgePrice 3 := by
  rw [mem_budgetSetAt]
  refine ⟨fun l => by fin_cases l <;> norm_num, ?_⟩
  rw [edgePrice, dotProduct]; norm_num

/-- **Orientation guard, negative side** (`mem_budgetSetAt`): The *strictly unaffordable* bundle
`(2, 2)` has value `2·1 + 2·1 = 4 > 3 = w`, so it is **not** in `budgetSetAt (1,1) 3`. A reversed
orientation would wrongly *include* it, so this negative witness pins the orientation from the other
side. -/
theorem mem_budgetSetAt_unaffordable :
    (![2, 2] : Fin 2 → ℝ) ∉ budgetSetAt edgePrice 3 := by
  rw [mem_budgetSetAt]
  rintro ⟨-, hle⟩
  rw [edgePrice, dotProduct] at hle
  norm_num at hle

/-- **The endowment is affordable** (`mem_budgetSetAt` / `endow_mem_budgetSet`): Every agent's
endowment lies in its budget set. This is a reflexive API witness (`p ⬝ᵥ e ≤ p ⬝ᵥ e` holds by
`le_refl`), so it does *not* by itself discriminate the wealth/price orientation; the strict
positive/negative pair `mem_budgetSetAt_strict_affordable` / `mem_budgetSetAt_unaffordable` does. -/
theorem endow_mem_budgetSet_witness (a : economy.Agents) :
    economy.endow a ∈ economy.budgetSet edgePrice a :=
  Economy.endow_mem_budgetSet edgePrice a

/-- The `(1,1)`-budget at wealth `3` is convex. -/
theorem budgetSetAt_convex_witness : Convex ℝ (budgetSetAt edgePrice (3 : ℝ)) :=
  budgetSetAt_convex edgePrice 3

/-- The `(1,1)`-budget at wealth `3` is closed. -/
theorem budgetSetAt_closed_witness : IsClosed (budgetSetAt edgePrice (3 : ℝ)) :=
  budgetSetAt_closed edgePrice 3

/-- **Price-scaling invariance** (`budgetSetAt_scale`): Scaling *both* the price `(1,1)` and the
wealth `3` by `2` leaves the budget set unchanged —
`budgetSetAt (2•(1,1)) (2·3) = budgetSetAt (1,1) 3`. A wrong scaling convention (e.g. scaling price
but not wealth) breaks this. -/
theorem budgetSetAt_scale_witness :
    budgetSetAt ((2 : ℝ) • edgePrice) (2 * 3) = budgetSetAt edgePrice 3 :=
  budgetSetAt_scale (by norm_num) edgePrice 3

/-- **Coordinate bound** (`budgetSetAt_coord_bound`): At strictly positive prices, every affordable
bundle's coordinate is bounded by `w / pₗ`. Anchored: At `(1,1)`, wealth `3`, every affordable
bundle has each coordinate `≤ 3`. -/
theorem budgetSetAt_coord_bound_witness (x : Fin 2 → ℝ) (hx : x ∈ budgetSetAt edgePrice 3)
    (l : Fin 2) : x l ≤ 3 := by
  have h := budgetSetAt_coord_bound edgePrice_pos x hx l
  fin_cases l <;> · simp only [edgePrice] at h ⊢; norm_num at h ⊢; linarith

/-- **Box containment** (`budgetSetAt_subset_Icc`): At strictly positive prices the budget set sits
inside `∏ₗ [0, w/pₗ]`. -/
theorem budgetSetAt_subset_Icc_witness :
    budgetSetAt edgePrice 3 ⊆ Set.pi Set.univ (fun l => Set.Icc 0 (3 / edgePrice l)) :=
  budgetSetAt_subset_Icc edgePrice_pos 3

/-- **Compactness** (`isCompact_budgetSetAt_of_pos_prices`): At strictly positive prices the budget
set is compact (the Berge-maximum-theorem input). -/
theorem isCompact_budgetSetAt_witness : IsCompact (budgetSetAt edgePrice (3 : ℝ)) :=
  isCompact_budgetSetAt_of_pos_prices edgePrice_pos 3

/-- The economy budget set is compact at the strictly positive equilibrium price. -/
theorem isCompact_budgetSet_witness (a : economy.Agents) :
    IsCompact (economy.budgetSet edgePrice a) :=
  economy.isCompact_budgetSet_of_pos_prices edgePrice_pos a

/-- The economy budget set is convex. -/
theorem budgetSet_convex_witness (a : economy.Agents) :
    Convex ℝ (economy.budgetSet edgePrice a) :=
  economy.budgetSet_convex edgePrice a

/-- Scaling the economy price by `2 > 0` leaves the budget set unchanged. -/
theorem budgetSet_scale_witness (a : economy.Agents) :
    economy.budgetSet ((2 : ℝ) • edgePrice) a = economy.budgetSet edgePrice a :=
  economy.budgetSet_scale (by norm_num) edgePrice a

/-! ## Block 2: Demand

The Cobb–Douglas closed form is anchored exactly at the Edgeworth numbers: At `(1,1)`, wealth
`3`, the share bundle is `(3/2, 3/2)`. -/

/-- **Cobb–Douglas closed-form demand** (`demand_eq_singleton_of_cobbDouglas`): At the equilibrium
price, each agent's demand is the singleton expenditure-share bundle
`l ↦ (αₗ / ∑α) · (p ⬝ᵥ eₐ) / pₗ`. -/
theorem demand_eq_singleton_witness (a : economy.Agents) :
    economy.demand edgePrice a
      = {fun l => (cdU.α l / ∑ i, cdU.α i) * (edgePrice ⬝ᵥ economy.endow a) / edgePrice l} := by
  have hw : (0 : ℝ) < edgePrice ⬝ᵥ economy.endow a := by
    change (0 : ℝ) < edgePrice ⬝ᵥ edgeEndow a
    rw [edge_wealth a]; norm_num
  exact economy.demand_eq_singleton_of_cobbDouglas (by norm_num) a cdU rfl edgePrice_pos hw

/-- **The share bundle is `(3/2, 3/2)`** — the closed form, evaluated. This pins the *numbers*: The
consumer spends half of wealth `3` on each unit-priced good, getting `3/2` of each (catches a
reciprocal/share inversion). -/
theorem share_bundle_eq (a : economy.Agents) :
    (fun l => (cdU.α l / ∑ i, cdU.α i) * (edgePrice ⬝ᵥ economy.endow a) / edgePrice l)
      = ![3/2, 3/2] := by
  have hα_sum : ∑ i, cdU.α i = 1 := by rw [Fin.sum_univ_two]; norm_num [cdU]
  have hw : edgePrice ⬝ᵥ economy.endow a = 3 := edge_wealth a
  funext l
  rw [hα_sum, hw]
  fin_cases l <;> · norm_num [cdU, edgePrice]

/-- Consequently the demand *is* the singleton `(3/2, 3/2)`, matching `edgeAlloc`. -/
theorem demand_eq_edgeAlloc (a : economy.Agents) :
    economy.demand edgePrice a = {edgeAlloc a} := by
  rw [demand_eq_singleton_witness a, share_bundle_eq a]
  rfl

/-- **Demand is contained in the budget set** (`demand_subset_budgetSet`). -/
theorem demand_subset_budgetSet_witness (a : economy.Agents) :
    economy.demand edgePrice a ⊆ economy.budgetSet edgePrice a :=
  economy.demand_subset_budgetSet edgePrice a

/-- **Demand is homogeneous of degree zero in prices** (`demand_homogeneous`): Demand at `2 • p`
equals demand at `p`. A degree-`1` (or any nonzero-degree) mistake fails here. -/
theorem demand_homogeneous_witness (a : economy.Agents) :
    economy.demand ((2 : ℝ) • edgePrice) a = economy.demand edgePrice a :=
  economy.demand_homogeneous (by norm_num) edgePrice a

/-- **Demand is convex** (`demand_convex`), from convexity of Cobb–Douglas preferences. -/
theorem demand_convex_witness (a : economy.Agents) :
    Convex ℝ (economy.demand edgePrice a) :=
  economy.demand_convex a (economy_regular.convex a) edgePrice

/-- **Demand is a subsingleton** here — even stronger, it is the singleton `(3/2, 3/2)`. -/
theorem demand_subsingleton_witness (a : economy.Agents) :
    (economy.demand edgePrice a).Subsingleton := by
  rw [demand_eq_edgeAlloc a]; exact Set.subsingleton_singleton

/-- **Demand is nonempty** at the strictly positive equilibrium price (`demand_nonempty`). -/
theorem demand_nonempty_witness (a : economy.Agents) :
    (economy.demand edgePrice a).Nonempty :=
  economy.demand_nonempty economy_regular edgePrice_pos a

/-- The strictly-positive price domain on which demand upper hemicontinuity is honest: every
coordinate of the price is `> 0`. The equilibrium price `(1,1)` lives here (see
`edgePrice_mem_positivePrices`), so the witness below is genuinely non-vacuous. -/
def positivePrices : Set (Fin 2 → ℝ) := {p | ∀ l, 0 < p l}

/-- The equilibrium price `(1,1)` is in the strictly-positive price domain — the domain is nonempty,
so the upper-hemicontinuity witness is not vacuous. -/
theorem edgePrice_mem_positivePrices : edgePrice ∈ positivePrices := edgePrice_pos

/-- **Demand is upper hemicontinuous on strictly positive prices** (`demand_upperHemicontinuousOn`,
Berge's maximum theorem). This is the honest, *dischargeable* form: on `positivePrices` the budget
set is compact and the cheaper-point (Slater) condition holds (the origin is cheaper than the
nonzero endowment), so every hypothesis is supplied from the concrete economy's regularity instance
— unlike a statement over the full price space, which is vacuous at `p = 0` (non-compact budget set,
no cheaper point). See `backlog/eq-demand-uhc-global-prices.md`. -/
theorem demand_upperHemicontinuousOn_witness (a : economy.Agents) :
    UpperHemicontinuousOn (fun p => economy.demand p a) positivePrices :=
  economy.demand_upperHemicontinuousOn economy_regular a (fun _ hp => hp)

/-- **Demand equals an argmax of a continuous utility** (`exists_demand_eq_argmax`): In a regular
economy each agent's demand is the argmax of a continuous Debreu representation, uniformly in
price. -/
theorem exists_demand_eq_argmax_witness (a : economy.Agents) :
    ∃ u : (Fin 2 → ℝ) → ℝ, Continuous u ∧
      ∀ p : Fin 2 → ℝ, economy.demand p a = argmax u (economy.budgetSet p a) :=
  economy.exists_demand_eq_argmax economy_regular a

/-! ## Block 3: Walras's law and equilibrium endpoints -/

/-- **Walras's law** (`walras_law`): If every agent demands its bundle, the value of aggregate
excess demand is zero. Anchored on the Edgeworth allocation `(3/2, 3/2)`. -/
theorem walras_law_witness :
    edgePrice ⬝ᵥ economy.aggregateExcess edgeAlloc = 0 :=
  economy.walras_law economy_regular edgeworth_demand_optimal

/-- **Abstract Walras's law** (`walras_law_over`) exercised on real budget-binding data over the
`Fin 2` counting aggregation: The equilibrium allocation binds every agent's budget at `(1,1)`. -/
theorem walras_law_over_witness :
    edgePrice ⬝ᵥ aggregateExcessOver economy.endow edgeAlloc = 0 := by
  refine walras_law_over (Z := economy.Agents) (fun a => ?_)
  -- `p ⬝ᵥ (3/2,3/2) = 3 = p ⬝ᵥ eₐ`.
  change edgePrice ⬝ᵥ edgeAlloc a = edgePrice ⬝ᵥ edgeEndow a
  rw [edge_wealth a]; simp [edgePrice, dotProduct, Fin.sum_univ_two, edgeAlloc]

/-- A **non-equilibrium budget-binding** allocation: agent `0` takes `(4, −1)` and agent `1` takes
`(0, 3)`, both with value `3 = wealth` at `(1,1)`. Its aggregate excess vector is `(4+0, −1+3) −
(3,3) = (1, −1)` — *nonzero* — yet `p ⬝ᵥ excess = 1 − 1 = 0`. This is the data that makes the Walras
witnesses discriminating: the excess does not vanish, only its *value* does. -/
def bindingAlloc : Fin 2 → (Fin 2 → ℝ) := ![![4, -1], ![0, 3]]

/-- Each agent's budget binds at the off-equilibrium allocation: `p ⬝ᵥ (bindingAlloc a) = 3 = p ⬝ᵥ
eₐ`. -/
theorem bindingAlloc_binds (a : Fin 2) :
    edgePrice ⬝ᵥ bindingAlloc a = edgePrice ⬝ᵥ economy.endow a := by
  change edgePrice ⬝ᵥ bindingAlloc a = edgePrice ⬝ᵥ edgeEndow a
  rw [edge_wealth a, edgePrice, dotProduct]
  fin_cases a <;> · simp only [bindingAlloc]; norm_num

/-- **Walras's law on nonzero excess** (`walras_law_over`): At the off-equilibrium binding
allocation the aggregate excess vector is the *nonzero* `(1, −1)`, yet its value is `0`. A sign
error that turned the value-aggregation into `p ⬝ᵥ demand + p ⬝ᵥ endow` (`= 12 ≠ 0`) would be
caught here, unlike at the equilibrium where the excess vanishes identically. -/
theorem walras_law_over_nonzero_excess :
    edgePrice ⬝ᵥ aggregateExcessOver economy.endow bindingAlloc = 0 :=
  walras_law_over (Z := economy.Agents) bindingAlloc_binds

/-- The aggregate **excess vector** at the off-equilibrium binding allocation is exactly `(1, −1)`
(orientation: `demand − endow`, not its negation). A swapped `endow − demand` in
`aggregateExcessOver`
would give `(−1, 1)`; this anchors the orientation of the vector, not just its value. -/
theorem bindingAlloc_aggregateExcessOver_anchor :
    aggregateExcessOver economy.endow bindingAlloc = ![1, -1] := by
  funext l
  simp only [aggregateExcessOver, AgentAggregation.agg_fintype]
  change (∑ a : Fin 2, bindingAlloc a l) - (∑ a : Fin 2, economy.endow a l) =
    (![1, -1] : Fin 2 → ℝ) l
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change (bindingAlloc 0 l + bindingAlloc 1 l) - (edgeEndow 0 l + edgeEndow 1 l)
    = (![1, -1] : Fin 2 → ℝ) l
  fin_cases l <;> · simp only [bindingAlloc, edgeEndow]; norm_num

/-- The **doubled allocation** `a ↦ (3, 3)`: aggregate demand `(6, 6)` exceeds the aggregate
endowment `(3, 3)`, so the aggregate excess vector is the *nonzero* `(3, 3)` with value `6 ≠ 0`.
This
is the non-clearing data on which the spending-decomposition is genuinely exercised. -/
def doubledAlloc : Fin 2 → (Fin 2 → ℝ) := fun _ => ![3, 3]

/-- `dotProduct_aggregateExcess` decomposes `p ⬝ᵥ excess` as the sum over agents of net spending,
exercised on the **non-clearing** doubled allocation where the value is `6 ≠ 0`: the per-agent terms
are `p ⬝ᵥ (3,3) − 3 = 3` each, summing to `6`. A sign flip in the decomposition would be caught,
unlike at the equilibrium where every term and the sum are `0`. -/
theorem dotProduct_aggregateExcess_witness :
    edgePrice ⬝ᵥ economy.aggregateExcess doubledAlloc
      = ∑ a, (edgePrice ⬝ᵥ (doubledAlloc a) - edgePrice ⬝ᵥ economy.endow a) :=
  economy.dotProduct_aggregateExcess edgePrice doubledAlloc

/-- The doubled allocation's net-spending sum is exactly `6` (both sides of the decomposition equal
`6`, the nonzero anchor that makes the previous witness non-tautological). -/
theorem doubledAlloc_dotProduct_excess_anchor :
    edgePrice ⬝ᵥ economy.aggregateExcess doubledAlloc = 6 := by
  rw [economy.dotProduct_aggregateExcess edgePrice doubledAlloc]
  change ∑ a : Fin 2, (edgePrice ⬝ᵥ doubledAlloc a - edgePrice ⬝ᵥ edgeEndow a) = 6
  rw [Fin.sum_univ_two, edge_wealth 0, edge_wealth 1, edgePrice, dotProduct, dotProduct]
  simp only [doubledAlloc]; norm_num

/-- `aggregateExcessOver` over the `Fin 2` counting sum coincides with the coordinatewise net
excess, identically zero on the equilibrium and the **nonzero** `(3, 3)` on the doubled allocation
(orientation: `demand − endow`, so a swapped orientation would give `(−3, −3)`). -/
theorem aggregateExcessOver_zero_witness :
    aggregateExcessOver economy.endow edgeAlloc = 0 := by
  funext l
  simp only [aggregateExcessOver, AgentAggregation.agg_fintype]
  change (∑ a : Fin 2, edgeAlloc a l) - (∑ a : Fin 2, economy.endow a l) = (0 : Fin 2 → ℝ) l
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change (edgeAlloc 0 l + edgeAlloc 1 l) - (edgeEndow 0 l + edgeEndow 1 l) = 0
  fin_cases l <;> norm_num [edgeAlloc, edgeEndow]

/-- **Orientation anchor for `aggregateExcessOver`**: on the doubled allocation the excess vector is
the nonzero `(3, 3)` (so the convention is `demand − endow`; a swapped `endow − demand` would give
`(−3, −3)`, caught here). -/
theorem aggregateExcessOver_doubled_anchor :
    aggregateExcessOver economy.endow doubledAlloc = ![3, 3] := by
  funext l
  simp only [aggregateExcessOver, AgentAggregation.agg_fintype]
  change (∑ a : Fin 2, doubledAlloc a l) - (∑ a : Fin 2, economy.endow a l) =
    (![3, 3] : Fin 2 → ℝ) l
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change (doubledAlloc 0 l + doubledAlloc 1 l) - (edgeEndow 0 l + edgeEndow 1 l)
    = (![3, 3] : Fin 2 → ℝ) l
  fin_cases l <;> · simp only [doubledAlloc, edgeEndow]; norm_num

/-- **Positive equilibrium prices** (`WalrasianEquilibrium.price_pos`): The Edgeworth equilibrium
has strictly positive prices, since agent `0` has strictly positive wealth `3`. -/
theorem price_pos_witness : ∀ l, 0 < edgeworthEquilibrium.price l :=
  edgeworthEquilibrium.price_pos economy_regular
    ⟨(0 : Fin 2), by change (0 : ℝ) < edgePrice ⬝ᵥ edgeEndow 0; rw [edge_wealth]; norm_num⟩

/-- **First welfare theorem** (`WalrasianEquilibrium.paretoOptimal`): The equilibrium allocation is
Pareto optimal. -/
theorem paretoOptimal_witness : economy.ParetoOptimal edgeworthEquilibrium.alloc :=
  edgeworthEquilibrium.paretoOptimal economy_regular

/-- **Core** (`WalrasianEquilibrium.mem_core`): The equilibrium allocation lies in the core. -/
theorem mem_core_witness : economy.Core edgeworthEquilibrium.alloc :=
  edgeworthEquilibrium.mem_core

/-! ## Block 4: Feasibility / Pareto — positive AND negative instances -/

/-- The endowment allocation `a ↦ eₐ` is feasible: Aggregate consumption equals aggregate
endowment, so excess is `0 ≤ 0` in every good. -/
theorem endowAlloc_feasible : economy.Feasible economy.endow := by
  refine ⟨fun a l => economy.endow_mem a l, fun l => ?_⟩
  change (∑ a : Fin 2, economy.endow a l) - (∑ a : Fin 2, economy.endow a l) ≤ 0
  simp

/-- The equilibrium allocation `(3/2,3/2)` is feasible (excess identically zero). -/
theorem edgeAlloc_feasible : economy.Feasible edgeAlloc := by
  refine ⟨fun a l => by fin_cases a <;> fin_cases l <;> norm_num [edgeAlloc], fun l => ?_⟩
  rw [edgeworth_aggregateExcess_zero]; simp

/-- **Positive Pareto-dominance instance**: The equilibrium split `(3/2,3/2)` Pareto dominates the
endowment allocation — both agents *strictly* prefer it (genuine gains from trade). -/
theorem edgeAlloc_paretoDominates_endow :
    economy.ParetoDominates edgeAlloc economy.endow := by
  refine ⟨fun a => (edgeworth_gains_from_trade a).1, ?_⟩
  exact ⟨(⟨0, by norm_num⟩ : Fin 2), edgeworth_gains_from_trade ⟨0, by norm_num⟩⟩

/-- **Negative Pareto-optimality instance**: The endowment allocation is **not** Pareto optimal —
it is feasible but the equilibrium allocation (also feasible) Pareto dominates it. Catches an
optimality predicate that accepts dominated allocations. -/
theorem endow_not_paretoOptimal : ¬ economy.ParetoOptimal economy.endow := by
  rintro ⟨_, hno⟩
  exact hno ⟨edgeAlloc, edgeAlloc_feasible, edgeAlloc_paretoDominates_endow⟩

/-- **Negative feasibility instance**: The doubled allocation `a ↦ (3,3)` is **not** feasible —
aggregate consumption `(6,6)` strictly exceeds the aggregate endowment `(3,3)`, so excess is
`3 > 0`. Catches a feasibility predicate with the inequality reversed. -/
theorem doubled_not_feasible :
    ¬ economy.Feasible (fun _ : economy.Agents => ![3, 3]) := by
  rintro ⟨_, hexc⟩
  have h0 := hexc 0
  change (∑ a : Fin 2, (![3, 3] : Fin 2 → ℝ) 0) - (∑ a : Fin 2, economy.endow a 0) ≤ 0 at h0
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h0
  change ((3 : ℝ) + 3) - (edgeEndow 0 0 + edgeEndow 1 0) ≤ 0 at h0
  norm_num [edgeEndow] at h0

/-- **`ParetoOptimalOver`** (abstract, over the `Fin 2` counting aggregation): The equilibrium
allocation is Pareto optimal in the aggregation-generic sense. Built from the first welfare theorem
on the concrete economy. -/
theorem paretoOptimalOver_witness :
    ParetoOptimalOver economy.endow economy.pref edgeAlloc := by
  refine ParetoOptimalOver.of_preferred_costly (Z := economy.Agents) edgeworthEquilibrium.price_cone
    (fun a l => (edgeworthEquilibrium.isOptimal a).1.1 l) edgeworthEquilibrium.clears.1
    (fun a z hz hle => ?_) (fun a z hz hlt => ?_)
  · exact economy.preferred_costly economy_regular (edgeworthEquilibrium.isOptimal a) hz hle
  · exact economy.strictlyPreferred_costly (edgeworthEquilibrium.isOptimal a) hz hlt

/-! ## Block 5: Transfers and the nonnegative orthant -/

/-- The equilibrium allocation is nonnegative (needed to form `transferEndow`). -/
theorem edgeAlloc_mem_nonnegOrthant : ∀ a, edgeAlloc a ∈ nonnegOrthant 2 :=
  fun a l => by fin_cases l <;> norm_num [edgeAlloc]

/-- **`transferEndow`** relabel: Replacing endowments by the (nonnegative) equilibrium allocation
sets `endow := edgeAlloc` while **keeping the agent type and the preference profile** untouched
(`Agents` and `pref` are inherited verbatim). All three fields are checked, specialized to the
concrete nonnegativity witness `edgeAlloc_mem_nonnegOrthant`. -/
theorem transferEndow_relabels :
    (economy.transferEndow edgeAlloc_mem_nonnegOrthant).endow = edgeAlloc ∧
      (economy.transferEndow edgeAlloc_mem_nonnegOrthant).pref = economy.pref ∧
      (economy.transferEndow edgeAlloc_mem_nonnegOrthant).Agents = economy.Agents :=
  ⟨rfl, rfl, rfl⟩

/-- **`WalrasianEquilibriumWithTransfers`, zero-transfer instance**: The Edgeworth equilibrium is a
Walrasian equilibrium with the trivial (everywhere-zero) balanced transfer scheme. With zero
transfers the transfer-adjusted budget `budgetSetAt p (p ⬝ᵥ eₐ + 0)` is the ordinary budget, so
optimality transports from `edgeworthEquilibrium.isOptimal`. -/
def edgeworthEquilibriumWithTransfers : economy.WalrasianEquilibriumWithTransfers where
  price := edgePrice
  alloc := edgeAlloc
  transfer := fun _ => 0
  price_cone := edgeworthEquilibrium.price_cone
  price_ne := edgeworthEquilibrium.price_ne
  transfers_balance := by simp
  isOptimal := fun a => by
    have h := edgeworthEquilibrium.isOptimal a
    change edgeAlloc a ∈ argmaxRel (economy.pref a)
      (budgetSetAt edgePrice (edgePrice ⬝ᵥ economy.endow a + 0))
    rw [add_zero]
    exact h
  clears := edgeworthEquilibrium.clears

/-- The nonnegative orthant equals the up-set of `0` (`nonnegOrthant_eq_Ici`). -/
theorem nonnegOrthant_eq_Ici_witness :
    nonnegOrthant 2 = Set.Ici (0 : Fin 2 → ℝ) :=
  nonnegOrthant_eq_Ici

/-- The nonnegative orthant is convex (`nonnegOrthant_convex`). -/
theorem nonnegOrthant_convex_witness : Convex ℝ (nonnegOrthant 2) :=
  nonnegOrthant_convex

/-- The nonnegative orthant is closed (`nonnegOrthant_closed`). -/
theorem nonnegOrthant_closed_witness : IsClosed (nonnegOrthant 2) :=
  nonnegOrthant_closed

/-! ## Block 6: The existence chain on real data

We exercise `exists_quasi_equilibrium`, `quasi_to_walrasian`, and `exists_equilibrium_data` on
the concrete economies, discharging every hypothesis from the economies' actual instances — so the
Kakutani/truncated-simplex machinery runs, certifying non-vacuity. We use the **three-agent linear
economy** (`...FiniteExistence.economy`), which is irreducible from strictly positive endowments. -/

open EconlibExamples.Equilibrium.FiniteExistence renaming economy → linEconomy,
  economy_regular → linEconomy_regular
open EconlibExamples.Equilibrium.FiniteExistence (coef endow coef_pos endow_pos)

/-- Linear utility `c ⬝ᵥ x` is continuous (`LinearUtility.continuous_u`), checked on agent `0`'s
coefficient `(2,1)`. -/
theorem continuous_linearUtil_witness :
    Continuous (fun x : Fin 2 → ℝ => coef 0 ⬝ᵥ x) :=
  (LinearUtility.mk (coef 0)).continuous_u

/-- Linear utility is quasiconcave (`LinearUtility.quasiconcaveOn_u`). -/
theorem quasiconcaveOn_linearUtil_witness :
    QuasiconcaveOn ℝ Set.univ (fun x : Fin 2 → ℝ => coef 0 ⬝ᵥ x) :=
  (LinearUtility.mk (coef 0)).quasiconcaveOn_u

/-- Linear utility with strictly positive coefficients is strictly monotone
(`LinearUtility.strictMono_u`), checked on `(2,1) ≫ 0`. -/
theorem strictMono_linearUtil_witness {x y : Fin 2 → ℝ} (hxy : x ≤ y) (hne : x ≠ y) :
    coef 0 ⬝ᵥ x < coef 0 ⬝ᵥ y :=
  (LinearUtility.mk (coef 0)).strictMono_u (coef_pos 0) hxy hne

/-- The linear economy's agent type is finite (an instance the existence chain consumes). -/
instance : Finite linEconomy.Agents := inferInstanceAs (Finite (Fin 3))

/-- The linear economy is McKenzie-irreducible from strictly positive endowments. -/
theorem linEconomy_irreducible : Irreducible linEconomy :=
  Irreducible.of_pos_endow linEconomy (by norm_num) endow_pos linEconomy_regular.mono

/-- **The full existence chain on real data** (`exists_equilibrium_data`): For the concrete
three-agent linear economy there exist nonnegative (some positive) prices and a market-clearing
allocation at which every consumer optimizes. Every hypothesis is discharged from the economy's
actual regularity / irreducibility / ownership data — so the Kakutani argument and its
truncated-simplex scaffolding run, certifying the claim is not vacuous. -/
theorem exists_equilibrium_data_witness :
    ∃ (p : Fin 2 → ℝ) (x : linEconomy.Agents → Fin 2 → ℝ),
      (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a, x a ∈ linEconomy.demand p a) ∧ linEconomy.MarketClears p x :=
  linEconomy.exists_equilibrium_data (inferInstanceAs (Nonempty (Fin 3))) linEconomy_regular
    linEconomy_irreducible (by norm_num) (fun l => ⟨(0 : Fin 3), endow_pos 0 l⟩)

/-- **Quasi-equilibrium existence** (`exists_quasi_equilibrium`) on the concrete linear economy:
Simplex prices and a market-clearing, budget-binding, individually-rational, quasi-optimal
allocation. -/
theorem exists_quasi_equilibrium_witness :
    ∃ (p : Fin 2 → ℝ) (x : linEconomy.Agents → Fin 2 → ℝ),
      p ∈ priceSimplex 2 ∧
      (∀ a, x a ∈ linEconomy.budgetSet p a) ∧
      (∀ a, p ⬝ᵥ x a = p ⬝ᵥ linEconomy.endow a) ∧
      (∀ a, x a ≽[linEconomy.pref a] linEconomy.endow a) ∧
      (∀ a y, (∀ l, 0 ≤ y l) → p ⬝ᵥ y < p ⬝ᵥ linEconomy.endow a → ¬ (y ≻[linEconomy.pref a] x a)) ∧
      linEconomy.MarketClears p x :=
  linEconomy.exists_quasi_equilibrium (inferInstanceAs (Nonempty (Fin 3))) linEconomy_regular
    (by norm_num)

/-- **Excess demand is homogeneous of degree zero** (`excessDemand_homogeneous`). -/
theorem excessDemand_homogeneous_witness (p : Fin 2 → ℝ) :
    linEconomy.excessDemand ((2 : ℝ) • p) = linEconomy.excessDemand p :=
  linEconomy.excessDemand_homogeneous (by norm_num) p

/-- **Aggregate excess demand is continuous in the allocation** (`continuous_aggregateExcess`). -/
theorem continuous_aggregateExcess_witness :
    Continuous (fun x : linEconomy.Agents → Fin 2 → ℝ => linEconomy.aggregateExcess x) :=
  linEconomy.continuous_aggregateExcess

/-- **A Walrasian equilibrium exists** for the concrete linear economy (`exists_equilibrium`), the
non-vacuity endpoint of the whole chain. -/
theorem finite_economy_has_equilibrium_witness : Nonempty linEconomy.WalrasianEquilibrium :=
  linEconomy.exists_equilibrium (inferInstanceAs (Nonempty (Fin 3))) linEconomy_regular
    linEconomy_irreducible (by norm_num) (fun l => ⟨(0 : Fin 3), endow_pos 0 l⟩)

/-! ## Block 7: Scalar market clearing (`MarketClearing.lean`)

The scalar market-clearing helpers operate over a unital `AggregateFunctional` and a *single*
good. We exercise them on a concrete single-agent (`Fin 1`) unital aggregator with concrete
demand/supply, where market clearing reduces to numeric equality. -/

/-- A concrete unital aggregator over a single agent: `f ↦ f 0` (the `Fin 1` counting sum, which
*is* unital since `∑ i : Fin 1, 1 = 1`). -/
def oneAgg : AggregateFunctional (Fin 1) where
  toPositiveLinearFunctional := Fintype.countingFunctional (Fin 1)
  aggregate_one := by simp

/-- **Market clearing iff aggregate demand equals aggregate supply** (`clearsMarket_iff`), checked
on a single agent demanding `1` and supplying `1`: The market clears. -/
theorem clearsMarket_iff_witness :
    ClearsMarket oneAgg (fun _ => 1) (fun _ => 1) ↔
      aggregateDemand oneAgg (fun _ => 1) = aggregateSupply oneAgg (fun _ => 1) :=
  clearsMarket_iff oneAgg _ _

/-- A clearing market: Demand `1`, supply `1` — aggregate demand `1` equals aggregate supply `1`. -/
theorem clears_balanced : ClearsMarket oneAgg (fun _ => 1) (fun _ => 1) := by
  unfold ClearsMarket aggregateDemand aggregateSupply oneAgg
  simp

/-- **Market clearing iff zero excess demand** (`clearsMarket_iff_excessDemand_eq_zero`). -/
theorem clearsMarket_iff_excessDemand_eq_zero_witness :
    ClearsMarket oneAgg (fun _ => 1) (fun _ => 1) ↔
      scalarExcessDemand oneAgg (fun _ => 1) (fun _ => 1) = 0 :=
  clearsMarket_iff_excessDemand_eq_zero oneAgg _ _

/-- **Negative clearing instance**: Demand `2`, supply `1` does **not** clear — excess demand
`1 ≠ 0`. Catches a clearing predicate that ignores the demand–supply gap. -/
theorem unbalanced_not_clears :
    ¬ ClearsMarket oneAgg (fun _ => 2) (fun _ => 1) := by
  unfold ClearsMarket aggregateDemand aggregateSupply oneAgg
  simp

/-- **Nonnegative aggregate demand** (`aggregateDemand_nonneg`) from nonnegative individual
demand. -/
theorem aggregateDemand_nonneg_witness :
    0 ≤ aggregateDemand oneAgg (fun _ => 1) :=
  aggregateDemand_nonneg oneAgg (fun _ => by norm_num)

/-- **Nonnegative aggregate supply** (`aggregateSupply_nonneg`). -/
theorem aggregateSupply_nonneg_witness :
    0 ≤ aggregateSupply oneAgg (fun _ => 1) :=
  aggregateSupply_nonneg oneAgg (fun _ => by norm_num)

/-- **IVT market clearing** (`exists_clearing_parameter_of_continuous_excessDemand`): A continuous
scalar excess-demand function changing sign over `[0,1]` has a market-clearing parameter. Anchored
on `excess R = 1 - 2R`, which is `+1` at `R = 0` and `-1` at `R = 1`, clearing at `R = 1/2`. -/
theorem exists_clearing_parameter_witness :
    ∃ R ∈ Set.Icc (0 : ℝ) 1,
      ClearsMarket oneAgg (fun _ => 1 - R) (fun _ => R) := by
  refine exists_clearing_parameter_of_continuous_excessDemand (by norm_num) (fun _ => oneAgg)
    (fun R _ => 1 - R) (fun R _ => R) ?_ ?_ ?_
  · -- continuity of `R ↦ (1 - R) - R = 1 - 2R`; `oneAgg`'s aggregate of a constant is that constant
    have hexc : (fun R : ℝ => scalarExcessDemand oneAgg (fun _ => 1 - R) (fun _ => R))
        = fun R : ℝ => (1 - R) - R := by
      funext R
      simp only [scalarExcessDemand, aggregateDemand, aggregateSupply, oneAgg,
        Fintype.countingFunctional_aggregate, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, one_smul]
    rw [hexc]; fun_prop
  · -- at `R = 0`: excess `= 1 ≥ 0`
    simp only [scalarExcessDemand, aggregateDemand, aggregateSupply, oneAgg,
      Fintype.countingFunctional_aggregate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      one_smul]
    norm_num
  · -- at `R = 1`: excess `= -1 ≤ 0`
    simp only [scalarExcessDemand, aggregateDemand, aggregateSupply, oneAgg,
      Fintype.countingFunctional_aggregate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      one_smul]
    norm_num

/-- **The IVT clearing parameter, evaluated** (`ClearsMarket`): the existential of
`exists_clearing_parameter_witness` is realized at the hand-computed `R = 1/2`, where demand
`1 − 1/2 = 1/2` equals supply `1/2` and excess `1 − 2·(1/2) = 0`. This anchors the numeric value the
docstring above advertises, which the bare `∃ R` does not formalize. -/
theorem clears_at_half : ClearsMarket oneAgg (fun _ => 1 - (1 / 2)) (fun _ => 1 / 2) := by
  unfold ClearsMarket aggregateDemand aggregateSupply oneAgg
  simp only [Fintype.countingFunctional_aggregate, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_smul]
  norm_num

end EconlibTest.Equilibrium.Exchange

end
