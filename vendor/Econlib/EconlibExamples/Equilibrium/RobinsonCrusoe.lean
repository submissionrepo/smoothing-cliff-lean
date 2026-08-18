/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Robinson Crusoe: A one-consumer, one-firm production economy

The textbook production economy. A single agent (Robinson Crusoe) is endowed with one unit of
**labor** (good `0`) and owns the single **firm**. The firm runs a constant-returns technology that
turns labor into **output** (good `1`). In equilibrium Crusoe sells his labor, the firm produces,
and Crusoe consumes the output — the firm's profit (here zero, by constant returns) is returned to
him as the owner.

We exhibit the equilibrium **by hand** and verify it, then apply the **first welfare theorem with
production** (`WalrasianEquilibriumWithProduction.paretoOptimal`) to conclude the equilibrium
allocation is Pareto optimal. We also invoke the **general existence theorem**
`exists_equilibrium_prod` to obtain an equilibrium abstractly: This economy is the friction test
for the weakened positive-wealth hypothesis `hendow_valued`. Crusoe's output good `1` is
produced-only (his endowment `(1,0)` has no output), so the old "every good owned by some agent"
condition fails — but the producer-side free-input lemma
(`Technology.supply_eq_empty_of_free_input`) rules out the one collapsing price `(0,1)`, so
`hendow_valued` holds and existence applies.

## The model

* Goods: `0` = labor (an input, so firm net output in coordinate `0` is `≤ 0`), `1` = output.
* `Agents = Unit`, `Firms = Unit`, counting aggregation.
* Endowment `(1, 0)`: One unit of labor, no output. Crusoe owns the whole firm (`share = 1`).
* Technology `Y = {y | y₀ ≤ 0 ∧ y₁ + y₀ ≤ 0}`: A labor-only activity cone — output is bounded by
  labor used. The `y₀ ≤ 0` truncation makes it **irreversible** (a plain half-space
  `{y₀ + y₁ ≤ 0}` is not — its frontier line lies in `Y ∩ -Y`).
* Preferences `u x = x₀ + x₁` (linear; Crusoe values leisure and output equally).
* Equilibrium: Price `(1, 1)`, consumption `(0, 1)`, plan `(-1, 1)` (use 1 labor, make 1 output).

## Main definitions and theorems

* `crusoeTech`, `crusoe` — the technology and the production economy.
* `crusoeTech_regular` — the technology satisfies `RegularTechnology` (all six Arrow–Debreu fields).
* `crusoe_plan_mem_supply`, `crusoe_profit_eq_zero` — the plan is profit-maximizing; profit is `0`.
* `crusoe_alloc_mem_demand`, `crusoe_excess_eq_zero`, `crusoe_clears` — consumer optimality and
  market clearing (exact, and the free-goods form the equilibrium consumes).
* `crusoeEquilibrium` — the assembled Walrasian equilibrium with production.
* `crusoe_pareto_optimal` — **first welfare theorem**: The equilibrium allocation is Pareto optimal.
* `crusoe_regular_prod`, `crusoe_irreducible`, `crusoe_endow_valued` — the hypotheses of the
  general existence theorem (`crusoe_endow_valued` is the free-input discharge of the
  positive-wealth seed).
* `crusoe_equilibrium_exists` — **existence theorem**: An equilibrium exists via
  `exists_equilibrium_prod`, with no good-by-good ownership assumption.
-/

noncomputable section

namespace EconlibExamples.Equilibrium.RobinsonCrusoe

open Econlib.Equilibrium Econlib.Preferences Matrix

/-! ## The technology and the economy -/

/-- The labor-only activity cone: Labor (good `0`) is an input, and output (good `1`) is bounded by
the labor used. This is the upstream `laborConeTech`. -/
abbrev crusoeTech : Technology 2 := laborConeTech

/-- Crusoe's preference coefficients (values both goods equally). -/
def crusoeCoef : Fin 2 → ℝ := ![1, 1]

/-- The Robinson Crusoe production economy. -/
def crusoe : ProductionEconomy 2 where
  Agents := Unit
  pref := fun _ => preferenceOfRealUtility (fun x => crusoeCoef ⬝ᵥ x)
  endow := fun _ => ![1, 0]
  endow_mem := fun _ l => by fin_cases l <;> simp
  Firms := Unit
  tech := fun _ => crusoeTech
  share := fun _ _ => 1
  share_nonneg := fun _ _ => zero_le_one
  share_sum := fun _ => by simp

/-! ## The candidate equilibrium -/

/-- Equilibrium price: Labor and output both priced at `1`. -/
def crusoePrice : Fin 2 → ℝ := ![1, 1]

/-- Equilibrium consumption: Crusoe consumes one unit of output and no leisure. -/
def crusoeAlloc : Unit → (Fin 2 → ℝ) := fun _ => ![0, 1]

/-- Equilibrium production plan: Use one unit of labor to make one unit of output. -/
def crusoePlan : Unit → (Fin 2 → ℝ) := fun _ => ![-1, 1]

/-! ## The technology is regular -/

/-- The labor-only activity cone satisfies every `RegularTechnology` field, including
irreversibility (which the `y₀ ≤ 0` truncation supplies). This is the upstream
`laborConeTech_regular`. -/
theorem crusoeTech_regular : RegularTechnology crusoeTech := laborConeTech_regular

/-! ## Profit maximization -/

/-- The plan `(-1, 1)` maximizes profit at the price `(1, 1)`: It lies in `Y` and earns the maximal
revenue `0` (every feasible plan has nonpositive value `z₀ + z₁ ≤ 0`). -/
theorem crusoe_plan_mem_supply : crusoePlan () ∈ crusoeTech.supply crusoePrice := by
  refine ⟨⟨by norm_num [crusoePlan], by norm_num [crusoePlan]⟩, isMaxOn_iff.mpr fun z hz => ?_⟩
  obtain ⟨_, hz2⟩ := hz
  simp [crusoePrice, dotProduct, Fin.sum_univ_two, crusoePlan]
  linarith

/-- The firm's profit at the equilibrium price is `0`. -/
theorem crusoe_profit_eq_zero : crusoeTech.profit crusoePrice = 0 := by
  rw [crusoeTech.profit_eq_dotProduct_of_mem_supply crusoe_plan_mem_supply, crusoePrice]
  simp [dotProduct, Fin.sum_univ_two, crusoePlan]

/-! ## Consumer optimality and market clearing -/

/-- Crusoe's augmented wealth at the equilibrium price is `1` (endowment value `1` plus zero
profit). -/
theorem crusoe_wealth : crusoe.wealth crusoePrice () = 1 := by
  haveI : Unique crusoe.Firms := inferInstanceAs (Unique Unit)
  simp only [ProductionEconomy.wealth, Fintype.sum_unique]
  rw [show (crusoe.tech default).profit crusoePrice = 0 from crusoe_profit_eq_zero]
  change crusoePrice ⬝ᵥ ![1, 0] + crusoe.share () default * 0 = 1
  rw [mul_zero, add_zero, crusoePrice]; simp [dotProduct, Fin.sum_univ_two]

/-- Crusoe's consumption `(0, 1)` maximizes utility on his augmented budget set: Any affordable
bundle `y` has `u y = y₀ + y₁ = price ⬝ᵥ y ≤ 1 = u (0,1)`. -/
theorem crusoe_alloc_mem_demand : crusoeAlloc () ∈ crusoe.consumerDemand crusoePrice () := by
  change crusoeAlloc () ∈ Econlib.Optimization.argmaxRel
      (preferenceOfRealUtility (fun x => crusoeCoef ⬝ᵥ x)) (crusoe.budgetSet crusoePrice ())
  rw [mem_argmaxRel_preferenceOfUtilityIn_iff]
  refine ⟨?_, isMaxOn_iff.mpr fun y hy => ?_⟩
  · -- budget feasibility: crusoeAlloc () ∈ crusoe.budgetSet crusoePrice ()
    simp only [ProductionEconomy.budgetSet, mem_budgetSetAt, crusoe_wealth]
    exact ⟨fun l => by fin_cases l <;> simp [crusoeAlloc],
      by rw [crusoePrice]; simp [dotProduct, Fin.sum_univ_two, crusoeAlloc]⟩
  · -- utility maximality: crusoeCoef ⬝ᵥ y ≤ crusoeCoef ⬝ᵥ crusoeAlloc ()
    simp only [ProductionEconomy.budgetSet, mem_budgetSetAt, crusoe_wealth] at hy
    obtain ⟨_, hyw⟩ := hy
    rw [crusoePrice] at hyw; simp [dotProduct, Fin.sum_univ_two] at hyw
    simp [crusoeCoef, dotProduct, Fin.sum_univ_two, crusoeAlloc]
    linarith

/-- Aggregate excess demand is identically zero: with one consumer and one firm, consumption `(0,1)`
plus net production `(-1,1)` exactly offsets the endowment `(1,0)` in both goods. -/
theorem crusoe_excess_eq_zero : crusoe.aggregateExcess crusoeAlloc crusoePlan = 0 := by
  haveI : Unique crusoe.Agents := inferInstanceAs (Unique Unit)
  haveI : Unique crusoe.Firms := inferInstanceAs (Unique Unit)
  funext l
  fin_cases l <;>
    simp [ProductionEconomy.aggregateExcess, crusoe, crusoeAlloc, crusoePlan]

/-- Markets clear (free-goods form): the value of aggregate excess demand is zero and every good is
in weak excess supply. This is the form the equilibrium structure consumes; the underlying excess is
in fact identically zero (`crusoe_excess_eq_zero`). -/
theorem crusoe_clears :
    (∀ l, crusoe.aggregateExcess crusoeAlloc crusoePlan l ≤ 0) ∧
      crusoePrice ⬝ᵥ crusoe.aggregateExcess crusoeAlloc crusoePlan = 0 := by
  rw [crusoe_excess_eq_zero]
  exact ⟨fun l => by simp, by simp⟩

/-! ## The equilibrium and the first welfare theorem -/

/-- The assembled Walrasian equilibrium with production. -/
def crusoeEquilibrium : WalrasianEquilibriumWithProduction crusoe where
  price := crusoePrice
  alloc := crusoeAlloc
  plan := crusoePlan
  price_cone := fun l => by fin_cases l <;> simp [crusoePrice]
  price_ne := ⟨0, by simp [crusoePrice]⟩
  profit_max := fun _ => crusoe_plan_mem_supply
  isOptimal := fun _ => crusoe_alloc_mem_demand
  clears := crusoe_clears

/-- Crusoe's preference is locally nonsatiated on the orthant (linear utility with positive
coefficients is strictly monotone toward the interior). -/
theorem crusoe_lns (a : crusoe.Agents) :
    LocallyNonsatiated (nonnegOrthant 2) (crusoe.pref a) := by
  have hc : ∀ l, 0 < crusoeCoef l := fun l => by fin_cases l <;> simp [crusoeCoef]
  exact locallyNonsatiated_nonnegOrthant_of_strictMonoToInterior
    ((LinearUtility.mk crusoeCoef).strictMonotonePreference hc).toStrictMonoToInterior

/-- **First welfare theorem with production.** Crusoe's equilibrium allocation is Pareto optimal.
The counting functional is faithful and preferences are locally nonsatiated, which is all
`WalrasianEquilibriumWithProduction.paretoOptimal` needs (no technology regularity required). -/
theorem crusoe_pareto_optimal :
    crusoe.ParetoOptimal crusoeEquilibrium.alloc crusoeEquilibrium.plan :=
  crusoeEquilibrium.paretoOptimal crusoe_lns

/-! ## Existence via the general theorem -/

/-- Crusoe's preference coefficients are strictly positive (linear utility is strongly monotone). -/
lemma crusoeCoef_pos : ∀ l, 0 < crusoeCoef l := fun l => by fin_cases l <;> simp [crusoeCoef]

/-- The consumption side is regular: Linear preferences with a nonzero endowment. The endowment
`(1,0)` is not strictly positive (good `1` is produced-only), but `RegularEconomy` only needs it
nonzero — exactly what the weakened `ofLinearPrefs` now exploits. -/
theorem crusoe_regular : RegularEconomy crusoe.toEconomy :=
  RegularEconomy.ofLinearPrefs crusoe.toEconomy (fun _ => ⟨crusoeCoef⟩)
    (fun _ => crusoeCoef_pos) (fun _ => rfl)
    (fun _ hz => by simpa [crusoe] using congr_fun hz 0)

/-- The single firm's technology admits no aggregate recession: A nonnegative recession ray lies in
`Y`, so `no_free_lunch` forces it to zero. (With one firm, aggregate nonnegativity is the single
plan's nonnegativity — there is no cancelation to rule out.) -/
theorem crusoe_no_aggregate_recession : ∀ d : crusoe.Firms → Fin 2 → ℝ,
    (∀ j, ∀ t : ℝ, 0 ≤ t → t • d j ∈ (crusoe.tech j).Y) → (∀ l, 0 ≤ ∑ j, d j l) → ∀ j, d j = 0 := by
  haveI : Unique crusoe.Firms := inferInstanceAs (Unique Unit)
  intro d hray hagg j
  -- The ray at `t = 1` is feasible, and aggregate nonnegativity over `Unit` is `d default ≥ 0`.
  have hmem : d default ∈ crusoeTech.Y := by simpa using hray default 1 zero_le_one
  have hnn : ∀ l, 0 ≤ d default l := fun l => by
    have h := hagg l; rwa [Fintype.sum_unique] at h
  have hzero : d default = 0 := crusoeTech_regular.no_free_lunch _ hmem hnn
  rw [Unique.eq_default j]; exact hzero

/-- Crusoe's production economy satisfies the full Arrow–Debreu regularity bundle. -/
theorem crusoe_regular_prod : RegularProductionEconomy crusoe where
  toRegularEconomy := crusoe_regular
  techReg := fun _ => crusoeTech_regular
  no_aggregate_recession := crusoe_no_aggregate_recession

/-- Consumption-side irreducibility holds **vacuously**: `Unit` has no two nonempty disjoint
coalitions, so the improving-coalition hypothesis is never triggered. -/
theorem crusoe_irreducible : Irreducible crusoe.toEconomy := by
  haveI : Subsingleton crusoe.toEconomy.Agents := inferInstanceAs (Subsingleton Unit)
  refine ⟨fun _ _ _ S T hS hT hdisj => ?_⟩
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  -- `s = t` in `Unit`, so `s ∈ T` as well, contradicting `Disjoint S T`.
  exact absurd (Subsingleton.elim t s ▸ ht) (Finset.disjoint_left.mp hdisj hs)

/-- **The positive-wealth seed for Robinson Crusoe.** At any simplex price `p` at which the firm has
a profit-maximizing plan (`supply p` nonempty), Crusoe's endowment `(1,0)` is valued positively,
i.e. `0 < p 0`. The only price that would zero it is `(0,1)`; there the technology is still
nonempty (`0 ∈ Y`), but the free-input ray `(-1,1)` of the labor technology is priced strictly
positively, so profit is unbounded above and `supply_eq_empty_of_free_input` makes supply empty —
contradicting the assumption. (Note the gap this exploits: feasibility of some plan, `Y ≠ ∅`, is
weaker than existence of a profit-*maximizing* plan, `supply p ≠ ∅`.) This is the hypothesis the old
"every good owned" condition over-supplied. -/
theorem crusoe_endow_valued (p : Fin 2 → ℝ) (hp : p ∈ priceSimplex 2)
    (hsupp : ∀ j, ((crusoe.tech j).supply p).Nonempty) :
    ∃ a, 0 < p ⬝ᵥ crusoe.endow a := by
  refine ⟨(), ?_⟩
  have hp_nn : ∀ l, 0 ≤ p l := fun l => hp.1 l
  -- `p ⬝ᵥ (1,0) = p 0`.
  have hval : p ⬝ᵥ crusoe.endow () = p 0 := by
    change (∑ i, p i * (![1, 0] : Fin 2 → ℝ) i) = p 0
    rw [Fin.sum_univ_two]; simp
  rw [hval]
  rcases (hp_nn 0).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hp0 : p 0 = 0 := hzero.symm
    have hp1 : p 1 = 1 := by
      have hs := hp.2
      rw [Fin.sum_univ_two, hp0] at hs; linarith
    -- The labor recession ray `(-1,1)`: feasible for every `t ≥ 0`, and priced `1 > 0` at `(0,1)`.
    have hray : ∀ t : ℝ, 0 ≤ t → t • (![-1, 1] : Fin 2 → ℝ) ∈ crusoeTech.Y :=
      fun _ ht => laborConeRay_smul_mem ht
    have hposd : 0 < p ⬝ᵥ (![-1, 1] : Fin 2 → ℝ) := by
      have hd : p ⬝ᵥ (![-1, 1] : Fin 2 → ℝ) = -p 0 + p 1 := by
        change (∑ i, p i * (![-1, 1] : Fin 2 → ℝ) i) = -p 0 + p 1
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      rw [hd, hp0, hp1]; norm_num
    have hempty : crusoeTech.supply p = ∅ :=
      crusoeTech.supply_eq_empty_of_free_input hray hposd
    obtain ⟨x, hx⟩ := hsupp ()
    have hx' : x ∈ crusoeTech.supply p := hx
    rw [hempty] at hx'
    exact Set.notMem_empty x hx'

/-- **Existence of a Walrasian equilibrium with production**, obtained from the general theorem
`exists_equilibrium_prod` — no good-by-good ownership assumption, only the free-input-discharged
positive-wealth seed `crusoe_endow_valued`. -/
theorem crusoe_equilibrium_exists : Nonempty (WalrasianEquilibriumWithProduction crusoe) :=
  crusoe.exists_equilibrium_prod (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod
    crusoe_irreducible.toIrreducibleProd (by norm_num) crusoe_endow_valued

end EconlibExamples.Equilibrium.RobinsonCrusoe

end
