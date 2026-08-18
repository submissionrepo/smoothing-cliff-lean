/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Equilibrium.Production.Technology

/-!
# The private-ownership production economy

The Arrow–Debreu private-ownership extension of the exchange `Economy`, adding firms (each a
`Technology`) and ownership shares.

## Main definitions

* `ProductionEconomy` — `Economy` plus finite firms, tech, and unit ownership shares summing to one.
* `ProductionEconomy.wealth` — augmented wealth: Endowment value plus the agent's share of profits.
* `ProductionEconomy.consumerDemand` — greatest preference elements over the augmented budget set.
* `ProductionEconomy.aggregateExcess` — consumption minus endowment minus aggregate net output.
* `WalrasianEquilibriumWithProduction` — competitive equilibrium with profit-maximizing firms.

## Main statements

* `ProductionEconomy.walras_law_prod` — at a profit-maximizing, budget-binding allocation the value
  of aggregate excess demand is zero.

## References

* Debreu, Gérard. 1959. *Theory of Value: An Axiomatic Analysis of Economic Equilibrium*. Wiley.
* McKenzie, Lionel W. 1959. “On the Existence of General Equilibrium for a Competitive Market.”
  *Econometrica* 27 (1): 54. [https://doi.org/10.2307/1907777](https://doi.org/10.2307/1907777).

## Tags

walrasian equilibrium, production economy, arrow-debreu, private ownership
-/

@[expose] public section

namespace Econlib.Equilibrium

open Matrix Econlib.Preferences

variable {L : ℕ}

/-! ## The production economy -/

/-- A **private-ownership production economy** (Debreu 1959). Extends the exchange `Economy` with a
finite set of `Firms`, a `Technology` per firm, and ownership shares `θ_aj ≥ 0` totalling one over
the (finite) agents (`share_sum`). The exchange economy is the special case `Firms := Empty`. -/
structure ProductionEconomy (L : ℕ) extends Economy L where
  /-- The (finite) set of firms. -/
  Firms : Type*
  /-- Firms are finite — the aggregate net output is an ordinary `Finset` sum. -/
  [firmsFin : Fintype Firms]
  /-- Each firm's production technology. -/
  tech : Firms → Technology L
  /-- Ownership shares: Agent `a` owns fraction `share a j` of firm `j`'s profit. -/
  share : Agents → Firms → ℝ
  /-- Ownership shares are nonnegative. -/
  share_nonneg : ∀ a j, 0 ≤ share a j
  /-- Ownership of each firm totals one across the (finite) agents. -/
  share_sum : ∀ j, ∑ a, share a j = 1

attribute [instance] ProductionEconomy.firmsFin

namespace ProductionEconomy

variable (E : ProductionEconomy L)

/-- **Augmented wealth.** Agent `a`'s spending power at prices `p`: Endowment value plus the
agent's share of each firm's profit.

The profit term is the totalized `Technology.profit`: At prices where some firm's revenue is
unbounded above on its `T.Y`, that firm's `sSup` returns the junk value `0` rather than a finite
optimum, so its dividend silently collapses to zero. Augmented wealth is therefore meaningful only
where every firm's revenue is bounded above — guaranteed at equilibrium prices, where each firm's
plan lies in a nonempty `Technology.supply`, but not at arbitrary `p`. See `Technology.profit`. -/
noncomputable def wealth (p : Fin L → ℝ) (a : E.Agents) : ℝ :=
  p ⬝ᵥ E.endow a + ∑ j, E.share a j * (E.tech j).profit p

/-- The **production budget set**: Nonnegative bundles affordable at augmented wealth. Inherits the
boundedness caveat on `wealth`: Meaningful only where each firm's revenue is bounded above. -/
noncomputable def budgetSet (p : Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  budgetSetAt p (E.wealth p a)

/-- The **consumer demand correspondence with production**: Greatest elements of the preference
over the augmented budget set (endowment value plus profit dividends). Like `wealth` and
`budgetSet`, this is meaningful only at prices where every firm's revenue is bounded above; at
other prices the junk-`0` profit term distorts the budget. -/
noncomputable def consumerDemand (p : Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  Optimization.argmaxRel (E.pref a) (E.budgetSet p a)

/-- **Aggregate excess demand with production**: Total consumption minus total endowment minus
aggregate net output `∑ⱼ y j`. -/
noncomputable def aggregateExcess (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)) :
    Fin L → ℝ :=
  fun l => (∑ a, x a l) - (∑ a, E.endow a l) - ∑ j, y j l

/-- The production excess equals the exchange excess minus aggregate net output. -/
lemma aggregateExcess_eq (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)) :
    E.aggregateExcess x y = E.toEconomy.aggregateExcess x - (fun l => ∑ j, y j l) := by
  funext l
  simp only [aggregateExcess, Economy.aggregateExcess, Pi.sub_apply]

/-- The sum of `(p ⬝ᵥ x a - wealth p a)` over agents equals `p ⬝ᵥ aggregateExcess x` minus total
profit. -/
lemma aggregate_net_spending (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)) :
    (∑ a, (p ⬝ᵥ x a - E.wealth p a))
      = p ⬝ᵥ E.toEconomy.aggregateExcess x - ∑ j, (E.tech j).profit p := by
  classical
  have hwealth_split : ∀ a, p ⬝ᵥ x a - E.wealth p a
      = (p ⬝ᵥ x a - p ⬝ᵥ E.endow a) - ∑ j, E.share a j * (E.tech j).profit p := by
    intro a; simp only [wealth]; ring
  rw [Finset.sum_congr rfl (fun a _ => hwealth_split a), Finset.sum_sub_distrib,
    ← E.toEconomy.dotProduct_aggregateExcess]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, E.share_sum j, one_mul]

/-! ## Regularity -/

/-- Regularity hypotheses for the production economy: Consumer-side `RegularEconomy`, a
`RegularTechnology` per firm, and no mutually-cancelling unbounded activities. -/
structure _root_.Econlib.Equilibrium.RegularProductionEconomy (E : ProductionEconomy L) where
  /-- Consumer-side regularity (continuous, convex, strictly monotone toward interior bundles via
  `StrictMonoToInterior`, locally nonsatiated). Interior strict monotonicity is weaker than global
  strong monotonicity and admits Cobb–Douglas / CES preferences. -/
  toRegularEconomy : RegularEconomy E.toEconomy
  /-- Each firm's technology is regular (closed, convex, inaction, free disposal, no free lunch,
  irreversible). -/
  techReg : ∀ j, RegularTechnology (E.tech j)
  /-- **No mutually-cancelling unbounded activities** (aggregate Arrow–Debreu boundedness). The
  only profile of recession directions with nonnegative aggregate is the zero profile. Per-firm
  irreversibility is insufficient: Two firms can run opposite unbounded rays that cancel; this
  rules that out. -/
  no_aggregate_recession : ∀ d : E.Firms → Fin L → ℝ,
    (∀ j, ∀ t : ℝ, 0 ≤ t → t • d j ∈ (E.tech j).Y) → (∀ l, 0 ≤ ∑ j, d j l) → ∀ j, d j = 0

/-! ## Walrasian equilibrium with production -/

/-- A **Walrasian equilibrium with production**: Nonnegative nonzero prices, a consumption
allocation, and a production plan, at which every firm maximizes profit, every agent optimizes over
its augmented budget set, and markets clear (free-goods form). -/
structure _root_.Econlib.Equilibrium.WalrasianEquilibriumWithProduction
    (E : ProductionEconomy L) where
  /-- Equilibrium prices. -/
  price : Fin L → ℝ
  /-- Equilibrium consumption allocation. -/
  alloc : E.Agents → (Fin L → ℝ)
  /-- Equilibrium production plan. -/
  plan : E.Firms → (Fin L → ℝ)
  /-- Prices are nonnegative. -/
  price_cone : ∀ l, 0 ≤ price l
  /-- Some good has a positive price. -/
  price_ne : ∃ l, 0 < price l
  /-- Each firm's plan maximizes profit. -/
  profit_max : ∀ j, plan j ∈ (E.tech j).supply price
  /-- Each agent's allocation is optimal in its augmented budget set. -/
  isOptimal : ∀ a, alloc a ∈ E.consumerDemand price a
  /-- Markets clear (free-goods form). -/
  clears : (∀ l, E.aggregateExcess alloc plan l ≤ 0)
    ∧ price ⬝ᵥ (E.aggregateExcess alloc plan) = 0

/-- A **Walrasian equilibrium with production and lump-sum transfers**: Nonnegative nonzero prices,
a consumption allocation, a production plan, and a balanced transfer scheme `transfer` (`∑ = 0`),
at which every firm maximizes profit, every agent optimizes over its transfer-adjusted augmented
budget set `budgetSetAt price (wealth price a + transfer a)`, and markets clear. The transfers
redistribute the profit/endowment wealth `wealth price a` so that each agent can afford exactly its
equilibrium bundle; the balance condition is a structure field. This is the object delivered by the
second welfare theorem with production. -/
structure _root_.Econlib.Equilibrium.WalrasianEquilibriumWithProductionAndTransfers
    (E : ProductionEconomy L) where
  /-- Equilibrium prices. -/
  price : Fin L → ℝ
  /-- Equilibrium consumption allocation. -/
  alloc : E.Agents → (Fin L → ℝ)
  /-- Equilibrium production plan. -/
  plan : E.Firms → (Fin L → ℝ)
  /-- The lump-sum transfer to each agent (signed). -/
  transfer : E.Agents → ℝ
  /-- Prices are nonnegative. -/
  price_cone : ∀ l, 0 ≤ price l
  /-- Some good has a positive price. -/
  price_ne : ∃ l, 0 < price l
  /-- Transfers balance: They redistribute wealth without aggregate injection. -/
  transfers_balance : ∑ a, transfer a = 0
  /-- Each firm's plan maximizes profit. -/
  profit_max : ∀ j, plan j ∈ (E.tech j).supply price
  /-- Each agent's allocation is optimal in its transfer-adjusted augmented budget set. -/
  isOptimal : ∀ a, alloc a ∈
    Optimization.argmaxRel (E.pref a) (budgetSetAt price (E.wealth price a + transfer a))
  /-- Markets clear (free-goods form). -/
  clears : (∀ l, E.aggregateExcess alloc plan l ≤ 0)
    ∧ price ⬝ᵥ (E.aggregateExcess alloc plan) = 0

/-- `W` **decentralizes** the allocation–plan pair `(x, y)`: Its equilibrium consumption is exactly
`x`, its production plan exactly `y`, supported by the canonical balanced lump-sum transfers
`transfer a = price ⬝ᵥ x a − wealth price a`. `W` is already a full equilibrium with production
(every field of `WalrasianEquilibriumWithProductionAndTransfers`); `Decentralizes` adds nothing to
equilibrium-hood — it only records that `W` implements the *given* optimum `(x, y)` with the
supporting transfer scheme. This is the property the second welfare theorem with production
establishes (see `ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers`). -/
structure _root_.Econlib.Equilibrium.WalrasianEquilibriumWithProductionAndTransfers.Decentralizes
    {L : ℕ} {E : ProductionEconomy L} (W : WalrasianEquilibriumWithProductionAndTransfers E)
    (x : E.Agents → Fin L → ℝ) (y : E.Firms → Fin L → ℝ) : Prop where
  /-- The equilibrium consumption is exactly the target allocation `x`. -/
  alloc_eq : W.alloc = x
  /-- The equilibrium production plan is exactly `y`. -/
  plan_eq : W.plan = y
  /-- The transfers are the canonical balanced supporting scheme. -/
  transfer_eq : ∀ a, W.transfer a = W.price ⬝ᵥ x a - E.wealth W.price a

/-! ## Walras's law with profits -/

/-- **Walras's law with profits.** If every agent optimizes over its augmented budget set and every
firm maximizes profit, the value of aggregate excess demand is zero. No price-sign condition is
needed. -/
theorem walras_law_prod (hreg : RegularProductionEconomy E) {p : Fin L → ℝ}
    {x : E.Agents → (Fin L → ℝ)} {y : E.Firms → (Fin L → ℝ)}
    (hx : ∀ a, x a ∈ E.consumerDemand p a) (hy : ∀ j, y j ∈ (E.tech j).supply p) :
    p ⬝ᵥ E.aggregateExcess x y = 0 := by
  classical
  have hbind : ∀ a, p ⬝ᵥ x a = E.wealth p a :=
    fun a => budgetSetAt_binds (hreg.toRegularEconomy.locallyNonsatiated a) (hx a)
  have hprofit : ∀ j, (E.tech j).profit p = p ⬝ᵥ y j :=
    fun j => (E.tech j).profit_eq_dotProduct_of_mem_supply (hy j)
  have hAggExcessVal : p ⬝ᵥ E.toEconomy.aggregateExcess x = ∑ j, (E.tech j).profit p := by
    have hNetSpending := E.aggregate_net_spending p x
    simp only [hbind, sub_self, Finset.sum_const_zero] at hNetSpending
    linarith
  have hNetOutputVal : p ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, (E.tech j).profit p := by
    have hDotSum : p ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, p ⬝ᵥ y j := by
      simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hDotSum]; exact Finset.sum_congr rfl fun j _ => (hprofit j).symm
  rw [E.aggregateExcess_eq, dotProduct_sub, hAggExcessVal, hNetOutputVal, sub_self]

/-! ## Production irreducibility -/

/-- **McKenzie irreducibility, with firms** (McKenzie 1959). For every individually-rational
consumption `x` and every feasible current production profile `y`, any split into a nonempty
improving coalition `S` and nonempty donor coalition `T` can be made strictly better off using
`S`'s consumption, the donors' endowments, and `S`'s owned share of the change in production
`yf - y`. A firm can thus convert one agent's resources into a good another agent wants — the
mechanism that makes a multi-agent production economy connected, invisible to exchange
`Irreducible` alone.

Crediting the production **increment** `yf - y` (rather than the gross plan `yf`) keeps the
predicate faithful at any returns to scale: Dotted with equilibrium prices the increment has
nonpositive value, since the current `y` already maximizes profit, so the McKenzie zero-wealth
elimination closes without a constant-returns assumption. Crediting the gross plan would
double-count the profit already inside `p ⬝ᵥ x = wealth`. With `yf := y` the increment vanishes and
this reduces to `Irreducible E.toEconomy` (`Irreducible.toIrreducibleProd`). -/
structure _root_.Econlib.Equilibrium.IrreducibleProd (E : ProductionEconomy L) : Prop where
  improve : ∀ (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)),
    (∀ i l, 0 ≤ x i l) → (∀ i, x i ≽[E.pref i] E.endow i) →
    (∀ f, y f ∈ (E.tech f).Y) →
    ∀ S T : Finset E.Agents, S.Nonempty → T.Nonempty → Disjoint S T →
      ∃ (y' : E.Agents → (Fin L → ℝ)) (yf : E.Firms → (Fin L → ℝ)),
        (∀ f, yf f ∈ (E.tech f).Y) ∧
        (∀ i ∈ S, (∀ l, 0 ≤ y' i l) ∧ y' i ≻[E.pref i] x i) ∧
        (∀ l, ∑ i ∈ S, y' i l ≤
          ∑ i ∈ S, x i l + ∑ j ∈ T, E.endow j l
            + ∑ f, (∑ i ∈ S, E.share i f) * (yf f l - y f l))

/-- **Exchange irreducibility implies production irreducibility.** Taking the proposed production
`yf := y` (feasible by hypothesis) makes the increment `yf - y` vanish, so the production resource
inequality collapses to the exchange one supplied by `Irreducible E.toEconomy`. Hence the
firm-aware existence theorem subsumes the consumption-only one. -/
theorem _root_.Econlib.Equilibrium.Irreducible.toIrreducibleProd (h : Irreducible E.toEconomy) :
    IrreducibleProd E := by
  refine ⟨fun x y hx_nn hIR hy_mem S T hS hT hdisj => ?_⟩
  obtain ⟨y', hy'_improve, hy'_resource⟩ := h.improve x hx_nn hIR S T hS hT hdisj
  refine ⟨y', y, hy_mem, hy'_improve, fun l => ?_⟩
  have hfirm : (∑ f, (∑ i ∈ S, E.share i f) * (y f l - y f l)) = 0 := by
    simp
  rw [hfirm, add_zero]
  exact hy'_resource l

end ProductionEconomy

end Econlib.Equilibrium
