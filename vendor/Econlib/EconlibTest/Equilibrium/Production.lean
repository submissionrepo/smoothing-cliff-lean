/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Equilibrium.FirmConnected
import EconlibExamples.Equilibrium.RobinsonCrusoe
import Mathlib

/-!
# Production-economy core non-vacuity witnesses

Compile-time semantic witnesses for the `Econlib.Equilibrium` private-ownership production core
(`Production/Technology.lean`, `Production/Economy.lean`, `Production/Existence.lean`). The
witnesses are anchored on the concrete one-consumer/one-firm **Robinson Crusoe** economy and the
two-agent **firm-connected Cobb–Douglas** economy of `EconlibExamples.Equilibrium`, plus a fresh
**positive-profit** decreasing-returns technology built here so the profit-income term is forced to
be genuinely nonzero (the Crusoe/firm-connected technologies are constant-returns cones with profit
identically `0`, which cannot exhibit a *dropped* profit term).

## The positive-profit hand computation

`posProfitTech` is the decreasing-returns production set `{y | y 0 ≤ -(max (y 1) 0)^2}` (it is *not*
a cone — e.g. `(-1/4, 1/2)` is feasible but `2 • (-1/4, 1/2) = (-1/2, 1)` is not): Producing `q ≥ 0`
units of output (good `1`) costs `q^2` units of input (good `0`). At price `(1,1)` profit is

`max_q (-q^2 + q) = 1/4` at `q = 1/2`,

achieved by the plan `(-1/4, 1/2)`. A constant-returns cone would give profit `0` or `+∞`; here it
is finite and **strictly positive (`1/4`)**, exactly the non-vacuity property the profit-income
term needs. In the one-firm `posProfitEconomy` the single owner's augmented wealth at `(1,1)` is
therefore

`wealth = p ⬝ᵥ endowment + share · profit = 1 + 1 · (1/4) = 5/4`,

so the `+ 1/4` profit dividend is visibly present in `wealth` and in `aggregate_net_spending`. A
formalization that dropped the profit term would report wealth `1`, not `5/4`.

## What each block catches

* **Technology** — `RegularTechnology.isCompact_attainable` / `isCompact_attainable`: The
  attainable set is compact (the fixed-point input). Checked on both the Crusoe cone and
  `posProfitTech`. The supply/profit closed forms are anchored at the *positive* number `1/4`,
  catching a degenerate (always-zero) profit function.
* **Walras's law with production** — `walras_law_prod` / `aggregate_net_spending` /
  `aggregateExcess_eq`: At a profit-maximizing budget-binding allocation, aggregate excess demand
  has zero value, and the net-spending identity carries `∑ⱼ profit` explicitly. Anchored on Crusoe
  (the equilibrium) and on `posProfitEconomy` (the profit term equals `1/4`, not `0`).
* **Existence** — `exists_equilibrium_data_prod` / `exists_quasi_equilibrium_prod` /
  `quasi_to_walrasian_prod` / `exists_attainable_profile_bound` /
  `mem_supply_of_mem_truncSupply_of_interior`: The production existence chain runs on the concrete
  Crusoe and firm-connected economies with every hypothesis discharged from their actual instances,
  so the Kakutani / truncated-technology scaffolding (`truncTech_*`, `truncDemand_*`,
  `truncWealth_*`, `walras_law_trunc`, `aggregate_net_spending_trunc`) is exercised transitively.
  Those helpers are internal scaffolding for the fixed point; their honest consumer is the headline
  `exists_equilibrium_prod`, which we exercise here. They are genuinely reached (verified by source
  audit of `Existence.lean`: Every `truncTech_*`/`truncDemand_*`/`truncWealth_*` lemma has ≥ 1
  in-file usage), so no per-helper test is written.
-/

noncomputable section

namespace EconlibTest.Equilibrium.Production

open Econlib.Equilibrium Econlib.Preferences Econlib.Optimization Matrix

/-! ## A positive-profit decreasing-returns technology

The Crusoe and firm-connected technologies are constant-returns labor cones with profit
identically `0` — a poor witness for a *dropped* profit term. We build a decreasing-returns
technology with a hand-computed strictly positive profit so the profit-income term is forced to
carry a nonzero value downstream. -/

/-- A concrete decreasing-returns one-input/one-output technology. Good `0` is the input (net
output negative), good `1` is the output (net output positive). The frontier
`y 0 ≤ -(max (y 1) 0)^2` says producing `q ≥ 0` units of output requires `q^2` units of input. Free
disposal is built in (the set is downward closed). -/
def posProfitTech : Technology 2 :=
  ⟨{y : Fin 2 → ℝ | y 0 ≤ -(max (y 1) 0) ^ 2}⟩

/-- Membership in `posProfitTech.Y` is the frontier inequality, definitionally. -/
theorem mem_posProfitTech {y : Fin 2 → ℝ} :
    y ∈ posProfitTech.Y ↔ y 0 ≤ -(max (y 1) 0) ^ 2 := Iff.rfl

/-- The decreasing-returns technology satisfies every `RegularTechnology` field. The frontier set
is the `0`-sublevel set of the convex function `y ↦ y 0 + (max (y 1) 0)^2`, which gives convexity;
the remaining fields are elementary `max`/square arithmetic. -/
theorem posProfitTech_regular : RegularTechnology posProfitTech where
  closed := by
    have hf : Continuous (fun y : Fin 2 → ℝ => y 0) := by fun_prop
    have hg : Continuous (fun y : Fin 2 → ℝ => -(max (y 1) 0) ^ 2) := by fun_prop
    exact isClosed_le hf hg
  convex := by
    have hproj0 : ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun y => y 0) :=
      (LinearMap.proj (0 : Fin 2)).convexOn convex_univ
    have hproj1 : ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun y => y 1) :=
      (LinearMap.proj (1 : Fin 2)).convexOn convex_univ
    have hconst : ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun _ => (0 : ℝ)) :=
      convexOn_const 0 convex_univ
    have hmax : ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun y => max (y 1) 0) :=
      hproj1.sup hconst
    have hmax_nonneg :
        ∀ ⦃y : Fin 2 → ℝ⦄, y ∈ (Set.univ : Set (Fin 2 → ℝ)) → 0 ≤ max (y 1) 0 :=
      fun y _ => le_max_right _ _
    have hsq : ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun y => (max (y 1) 0) ^ 2) :=
      hmax.pow hmax_nonneg 2
    have hsum :
        ConvexOn ℝ (Set.univ : Set (Fin 2 → ℝ)) (fun y => y 0 + (max (y 1) 0) ^ 2) :=
      hproj0.add hsq
    have hset := hsum.convex_le 0
    change Convex ℝ {y : Fin 2 → ℝ | y 0 ≤ -(max (y 1) 0) ^ 2}
    convert hset using 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
    constructor
    · intro h; linarith
    · intro h; linarith
  inaction := by
    change (0 : Fin 2 → ℝ) 0 ≤ -(max ((0 : Fin 2 → ℝ) 1) 0) ^ 2
    simp only [Pi.zero_apply]
    norm_num
  free_disposal := by
    intro y hy y' hy'
    simp only [mem_posProfitTech] at hy ⊢
    have h0 := hy' 0
    have h1 := hy' 1
    have hmax_mono : max (y' 1) 0 ≤ max (y 1) 0 := max_le_max h1 (le_refl 0)
    have hm0 : (0 : ℝ) ≤ max (y' 1) 0 := le_max_right _ _
    nlinarith [hy, h0, hmax_mono, hm0]
  no_free_lunch := by
    intro y hy hynn
    simp only [mem_posProfitTech] at hy
    have h0 := hynn 0
    have h1 := hynn 1
    have hmax_eq : max (y 1) 0 = y 1 := max_eq_left h1
    have hy0 : y 0 = 0 := by nlinarith [sq_nonneg (y 1), hy, h0, hmax_eq]
    have hy1 : y 1 = 0 := by nlinarith [sq_nonneg (y 1), hy, h0, hmax_eq, hy0]
    funext l
    fin_cases l
    · simpa using hy0
    · simpa using hy1
  irreversible := by
    intro y hy hny
    simp only [mem_posProfitTech] at hy
    simp only [mem_posProfitTech, Pi.neg_apply] at hny
    have hm0y : (0 : ℝ) ≤ max (y 1) 0 := le_max_right _ _
    have hm0ny : (0 : ℝ) ≤ max (-(y 1)) 0 := le_max_right _ _
    have hsq1 : (0 : ℝ) ≤ (max (y 1) 0) ^ 2 := sq_nonneg _
    have hsq2 : (0 : ℝ) ≤ (max (-(y 1)) 0) ^ 2 := sq_nonneg _
    have hy0 : y 0 = 0 := by nlinarith [hy, hny, hsq1, hsq2]
    have hmax1 : max (y 1) 0 = 0 := by nlinarith [hy, hy0, hsq1, hm0y]
    have hmax2 : max (-(y 1)) 0 = 0 := by nlinarith [hny, hy0, hsq2, hm0ny]
    have h1le : y 1 ≤ 0 := by
      have := le_max_left (y 1) 0; rw [hmax1] at this; exact this
    have h1ge : 0 ≤ y 1 := by
      have := le_max_left (-(y 1)) 0; rw [hmax2] at this; linarith
    have hy1 : y 1 = 0 := le_antisymm h1le h1ge
    funext l
    fin_cases l
    · simpa using hy0
    · simpa using hy1

/-- Equilibrium-style price for the positive-profit technology: Both goods priced `1`. -/
def posProfitPrice : Fin 2 → ℝ := ![1, 1]

/-- The profit-maximizing plan at `(1,1)`: Use `1/4` unit of input to make `1/2` unit of output. -/
def posProfitPlan : Fin 2 → ℝ := ![-1 / 4, 1 / 2]

/-- **The plan `(-1/4, 1/2)` maximizes profit at `(1,1)`** (`Technology.supply`). It lies in `Y`
(frontier binds: `-1/4 = -(1/2)^2`) and earns `1/4 = p ⬝ᵥ (-1/4,1/2)`, which is maximal because
`z 0 + z 1 ≤ -(max (z 1) 0)^2 + max (z 1) 0 ≤ 1/4` for every feasible `z` (the quadratic
`(m - 1/2)^2 ≥ 0`). -/
theorem posProfitPlan_mem_supply :
    posProfitPlan ∈ posProfitTech.supply posProfitPrice := by
  refine ⟨?_, ?_⟩
  · change posProfitPlan 0 ≤ -(max (posProfitPlan 1) 0) ^ 2
    simp only [posProfitPlan]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro z hz
    change posProfitPrice ⬝ᵥ z ≤ posProfitPrice ⬝ᵥ posProfitPlan
    have hzY : z 0 ≤ -(max (z 1) 0) ^ 2 := hz
    have hdot_z : posProfitPrice ⬝ᵥ z = z 0 + z 1 := by
      simp [posProfitPrice, dotProduct, Fin.sum_univ_two]
    have hdot_plan : posProfitPrice ⬝ᵥ posProfitPlan = 1 / 4 := by
      simp [posProfitPrice, posProfitPlan, dotProduct, Fin.sum_univ_two]; norm_num
    rw [hdot_z, hdot_plan]
    have hm1 : z 1 ≤ max (z 1) 0 := le_max_left _ _
    have hm0 : (0 : ℝ) ≤ max (z 1) 0 := le_max_right _ _
    set m := max (z 1) 0 with hm
    nlinarith [sq_nonneg (m - 1 / 2), hzY, hm1, hm0]

/-- **The hand-computed profit is `1/4`** (`Technology.profit`), strictly positive and finite — the
defining non-vacuity property a constant-returns cone (profit `0` or `+∞`) cannot supply. -/
theorem posProfitTech_profit_eq : posProfitTech.profit posProfitPrice = 1 / 4 := by
  rw [posProfitTech.profit_eq_dotProduct_of_mem_supply posProfitPlan_mem_supply]
  simp [posProfitPrice, posProfitPlan, dotProduct, Fin.sum_univ_two]
  norm_num

/-! ## Block 1: Attainable-set compactness (`Technology.lean`)

`RegularTechnology.isCompact_attainable` and the underlying `isCompact_attainable` are the
fixed-point inputs. We exercise them on the positive-profit technology (regular, with positive
profit) and on the Crusoe labor cone. -/

open EconlibExamples.Equilibrium.RobinsonCrusoe (crusoeTech crusoeTech_regular crusoePrice
  crusoePlan crusoe_plan_mem_supply crusoe_profit_eq_zero)

/-- **`RegularTechnology.isCompact_attainable`** on the positive-profit technology: At resource
bound `e = (1,1)` the attainable set `Y ∩ {y | -e ≤ y}` is compact. -/
theorem posProfit_isCompact_attainable :
    IsCompact (posProfitTech.Y ∩ {y : Fin 2 → ℝ | ∀ l, -(![1, 1] : Fin 2 → ℝ) l ≤ y l}) :=
  posProfitTech_regular.isCompact_attainable ![1, 1]

/-- **`RegularTechnology.isCompact_attainable`** on the Crusoe labor cone (constant returns), at
resource bound `(1,0)` (Crusoe's endowment). -/
theorem crusoe_isCompact_attainable :
    IsCompact (crusoeTech.Y ∩ {y : Fin 2 → ℝ | ∀ l, -(![1, 0] : Fin 2 → ℝ) l ≤ y l}) :=
  crusoeTech_regular.isCompact_attainable ![1, 0]

/-- **`isCompact_attainable`** (the underlying set-level theorem) directly, fed the positive-profit
technology's regularity facts: Closedness, convexity, `0 ∈ Y`, and no-free-lunch. -/
theorem posProfit_isCompact_attainable_setForm :
    IsCompact (posProfitTech.Y ∩ {y : Fin 2 → ℝ | ∀ l, -(![1, 1] : Fin 2 → ℝ) l ≤ y l}) :=
  isCompact_attainable posProfitTech.Y ![1, 1] posProfitTech_regular.closed
    posProfitTech_regular.convex posProfitTech_regular.inaction posProfitTech_regular.no_free_lunch

/-- **`Technology.supply_convex`**: The supply correspondence of the positive-profit technology is
convex-valued. (It is in fact the singleton `{(-1/4, 1/2)}` — see
`posProfit_supply_eq_singleton`.) -/
theorem posProfit_supply_convex :
    Convex ℝ (posProfitTech.supply posProfitPrice) :=
  posProfitTech.supply_convex posProfitTech_regular.convex posProfitPrice

/-- **The supply correspondence is exactly the singleton `{(-1/4, 1/2)}`.** The profit maximizer is
*unique*: any feasible `z` with `z 0 + z 1 = 1/4` and `z 0 ≤ -(max (z 1) 0)^2` is forced to `(-1/4,
1/2)` (the quadratic `(m - 1/2)^2 ≥ 0` binds, so `max (z 1) 0 = 1/2`, `z 0 = -1/4`, `z 1 = 1/2`). A
broken supply correspondence admitting extra maximizers would fail this exact equality, which the
bare convexity witness above cannot catch. -/
theorem posProfit_supply_eq_singleton :
    posProfitTech.supply posProfitPrice = {posProfitPlan} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨posProfitPlan_mem_supply, fun z hz => ?_⟩
  -- `z` is feasible and maximal, so `p ⬝ᵥ z = 1/4`.
  have hzY : z 0 ≤ -(max (z 1) 0) ^ 2 := hz.1
  have hz_val : posProfitPrice ⬝ᵥ z = 1 / 4 := by
    rw [← posProfitTech_profit_eq, eq_comm]
    exact posProfitTech.profit_eq_dotProduct_of_mem_supply hz
  have hdot_z : posProfitPrice ⬝ᵥ z = z 0 + z 1 := by
    simp [posProfitPrice, dotProduct, Fin.sum_univ_two]
  rw [hdot_z] at hz_val
  -- `m := max (z 1) 0 ≥ z 1`, `m ≥ 0`; the binding quadratic forces `m = 1/2`.
  have hm1 : z 1 ≤ max (z 1) 0 := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ max (z 1) 0 := le_max_right _ _
  set m := max (z 1) 0 with hm
  have hm_half : m = 1 / 2 := by nlinarith [sq_nonneg (m - 1 / 2), hzY, hm1, hm0, hz_val]
  -- with `m = 1/2`: `z 1 ≤ 1/2` and `z 0 ≤ -1/4`, but `z 0 + z 1 = 1/4` pins both.
  have hz0 : z 0 = -1 / 4 := by nlinarith [hzY, hm_half, hz_val, hm1]
  have hz1 : z 1 = 1 / 2 := by linarith [hz_val, hz0]
  funext l
  fin_cases l
  · simpa [posProfitPlan] using hz0
  · simpa [posProfitPlan] using hz1

/-- **`Technology.dotProduct_le_profit_of_mem_supply`**: **Every** feasible plan earns at most the
profit `1/4` — the universal bound, anchored numerically (`profit = 1/4`). This is the genuine
content the inaction-only check could not deliver. -/
theorem posProfit_dotProduct_le_profit :
    ∀ z ∈ posProfitTech.Y, posProfitPrice ⬝ᵥ z ≤ posProfitTech.profit posProfitPrice :=
  fun _z hz => posProfitTech.dotProduct_le_profit_of_mem_supply hz posProfitPlan_mem_supply

/-- The profit bound's value is exactly `1/4`, so the universal inequality above reads
`p ⬝ᵥ z ≤ 1/4` for every feasible `z`. -/
theorem posProfit_dotProduct_le_quarter :
    ∀ z ∈ posProfitTech.Y, posProfitPrice ⬝ᵥ z ≤ 1 / 4 := by
  intro z hz
  rw [← posProfitTech_profit_eq]
  exact posProfit_dotProduct_le_profit z hz

/-! ## Block 2: A positive-profit one-firm economy — the profit-income term is nonzero

The Crusoe / firm-connected economies have profit identically `0`, so they cannot reveal a
*dropped* profit term. We assemble a minimal one-consumer/one-firm economy around `posProfitTech`,
in which the single owner's augmented wealth at `(1,1)` is

`wealth = p ⬝ᵥ (1,0) + 1 · profit = 1 + 1/4 = 5/4`,

making the `+ 1/4` profit dividend visibly load-bearing. -/

/-- The single agent's preference coefficients (values both goods equally). -/
def posCoef : Fin 2 → ℝ := ![1, 1]

/-- A one-consumer/one-firm production economy on the positive-profit technology. The agent holds
one unit of the input good and owns the whole firm. -/
def posProfitEconomy : ProductionEconomy 2 where
  Agents := Unit
  pref := fun _ => preferenceOfRealUtility (fun x => posCoef ⬝ᵥ x)
  endow := fun _ => ![1, 0]
  endow_mem := fun _ l => by fin_cases l <;> simp
  Firms := Unit
  tech := fun _ => posProfitTech
  share := fun _ _ => 1
  share_nonneg := fun _ _ => zero_le_one
  share_sum := fun _ => by simp

/-- The firm's profit in `posProfitEconomy` at `(1,1)` is the hand-computed `1/4`. -/
theorem posProfitEconomy_profit_eq :
    (posProfitEconomy.tech ()).profit posProfitPrice = 1 / 4 :=
  posProfitTech_profit_eq

/-- **The profit dividend is present in `wealth`.** The single owner's augmented wealth at `(1,1)`
is `5/4 = 1 (endowment value) + 1/4 (profit)`, **not** `1`. A formalization that dropped the profit
share term would report `1`. This is the canonical dropped-profit-term check, anchored
numerically. -/
theorem posProfitEconomy_wealth_eq :
    posProfitEconomy.wealth posProfitPrice () = 5 / 4 := by
  haveI : Unique posProfitEconomy.Firms := inferInstanceAs (Unique Unit)
  -- `wealth = p ⬝ᵥ endow + ∑ⱼ share · profit`; the firm sum collapses to `1 · (1/4)`.
  simp only [ProductionEconomy.wealth, Fintype.sum_unique]
  rw [show (posProfitEconomy.tech default).profit posProfitPrice = 1 / 4 from
    posProfitEconomy_profit_eq]
  have hshare : posProfitEconomy.share () default = 1 := rfl
  rw [hshare]
  change posProfitPrice ⬝ᵥ ![1, 0] + 1 * (1 / 4) = 5 / 4
  simp only [posProfitPrice, dotProduct, Fin.sum_univ_two]
  norm_num

/-- **Negative check: A dropped profit term is detectable.** Endowment value alone is `1`, strictly
less than the true wealth `5/4`. So the wealth formula does **not** coincide with bare endowment
value — the profit dividend genuinely shifts wealth. -/
theorem posProfitEconomy_wealth_ne_endowValue :
    posProfitEconomy.wealth posProfitPrice () ≠ posProfitPrice ⬝ᵥ posProfitEconomy.endow () := by
  rw [posProfitEconomy_wealth_eq]
  have hendow : posProfitPrice ⬝ᵥ posProfitEconomy.endow () = 1 := by
    change posProfitPrice ⬝ᵥ ![1, 0] = 1
    simp only [posProfitPrice, dotProduct, Fin.sum_univ_two]
    norm_num [posProfitEconomy]
  rw [hendow]; norm_num

/-- **`aggregate_net_spending` carries the profit term.** For any consumption `x`, the net-spending
identity `∑ₐ (p ⬝ᵥ x a - wealth p a) = p ⬝ᵥ aggregateExcess x - ∑ⱼ profit` holds, and on
`posProfitEconomy` the right-hand profit sum is the nonzero `1/4`. We exercise the identity at the
consumption `x() = (1, 0)` (the agent consuming its own endowment), where it reads
`(1 - 5/4) = (p ⬝ᵥ excess) - 1/4`, i.e. both sides equal `-1/4` since the exchange excess value is
`0`. -/
theorem posProfitEconomy_aggregate_net_spending :
    (∑ a, (posProfitPrice ⬝ᵥ (fun _ => ![1, 0] : Unit → Fin 2 → ℝ) a -
        posProfitEconomy.wealth posProfitPrice a))
      = posProfitPrice ⬝ᵥ posProfitEconomy.toEconomy.aggregateExcess (fun _ => ![1, 0])
        - ∑ j, (posProfitEconomy.tech j).profit posProfitPrice :=
  posProfitEconomy.aggregate_net_spending posProfitPrice (fun _ => ![1, 0])

/-- The profit sum on the right of `aggregate_net_spending` is exactly `1/4` (one firm, profit
`1/4`). This is the term that a dropped-profit bug would omit. -/
theorem posProfitEconomy_profit_sum_eq :
    (∑ j, (posProfitEconomy.tech j).profit posProfitPrice) = 1 / 4 := by
  haveI : Unique posProfitEconomy.Firms := inferInstanceAs (Unique Unit)
  rw [Fintype.sum_unique]
  exact posProfitEconomy_profit_eq

/-! ## Block 3: Walras's law with production (`Economy.lean`)

`walras_law_prod`, `aggregate_net_spending`, and `aggregateExcess_eq` on the concrete Robinson
Crusoe equilibrium (constant returns, so the profit term is present but `0`) and on the
positive-profit economy (where the profit term is the nonzero `1/4`). -/

open EconlibExamples.Equilibrium.RobinsonCrusoe (crusoe crusoeAlloc crusoe_alloc_mem_demand
  crusoe_regular_prod crusoe_wealth crusoeEquilibrium crusoe_excess_eq_zero)

/-- **Walras's law with production** (`walras_law_prod`): At the Crusoe equilibrium — every firm
profit-maximizing, every agent optimizing over its augmented budget — the value of aggregate excess
demand is zero. The profit term is genuinely consumed inside the proof (via the augmented-wealth
binding), even though it evaluates to `0` here. (For the *nonzero*-profit version, where the profit
term `1/4` is load-bearing in the cancellation, see `posProfit_walras_law_prod` below.) -/
theorem crusoe_walras_law_prod :
    crusoePrice ⬝ᵥ crusoe.aggregateExcess crusoeAlloc crusoePlan = 0 :=
  crusoe.walras_law_prod crusoe_regular_prod (fun _ => crusoe_alloc_mem_demand)
    (fun _ => crusoe_plan_mem_supply)

/-- The single owner's budget-binding consumption in `posProfitEconomy`: value `3/4 + 1/2 = 5/4` at
`(1,1)`, exactly the augmented wealth `5/4 = endowment 1 + profit 1/4`. -/
def posAlloc : Unit → Fin 2 → ℝ := fun _ => ![3 / 4, 1 / 2]

/-- The consumption `posAlloc` binds the augmented budget: `p ⬝ᵥ (3/4, 1/2) = 5/4 = wealth`. The
right-hand side carries the profit dividend, so this binding equation is itself a profit-term
witness. -/
theorem posAlloc_binds (a : Unit) :
    posProfitPrice ⬝ᵥ posAlloc a = posProfitEconomy.wealth posProfitPrice a := by
  obtain rfl : a = () := rfl
  rw [posProfitEconomy_wealth_eq]
  change posProfitPrice ⬝ᵥ ![3 / 4, 1 / 2] = 5 / 4
  simp only [posProfitPrice, dotProduct, Fin.sum_univ_two]
  norm_num

/-- **Walras's law with production on the positive-profit economy.** At the profit-maximizing plan
`(-1/4, 1/2)` (profit `1/4 ≠ 0`) and the budget-binding consumption `(3/4, 1/2)`, the value of
aggregate excess demand is zero — and here the cancellation genuinely *consumes* the nonzero profit
term: `p ⬝ᵥ exchangeExcess = ∑ⱼ profit = 1/4` is set against `p ⬝ᵥ (∑ⱼ planⱼ) = 1/4`. A
dropped-profit
bug (which the zero-profit Crusoe witness cannot detect) would break this equality. The aggregate
excess vector is itself `(3/4,1/2) − (1,0) − (-1/4,1/2) = (0,0)`. -/
theorem posProfit_walras_law_prod :
    posProfitPrice ⬝ᵥ
      posProfitEconomy.aggregateExcess posAlloc (fun _ : posProfitEconomy.Firms => posProfitPlan)
      = 0 := by
  haveI : Unique posProfitEconomy.Agents := inferInstanceAs (Unique Unit)
  set y : posProfitEconomy.Firms → Fin 2 → ℝ := fun _ => posProfitPlan with hy
  -- exchange-excess value equals total profit `1/4` (via `aggregate_net_spending` + binding) ...
  have hAggExcessVal :
      posProfitPrice ⬝ᵥ posProfitEconomy.toEconomy.aggregateExcess posAlloc
        = ∑ j, (posProfitEconomy.tech j).profit posProfitPrice := by
    have hNet := posProfitEconomy.aggregate_net_spending posProfitPrice posAlloc
    rw [Fintype.sum_unique, posAlloc_binds, sub_self] at hNet
    -- `hNet : 0 = p ⬝ᵥ exchangeExcess - ∑ profit`
    linarith
  -- ... and so does the aggregate net-output value `p ⬝ᵥ (∑ⱼ planⱼ)`.
  have hNetOutputVal :
      posProfitPrice ⬝ᵥ (fun l => ∑ j, y j l)
        = ∑ j, (posProfitEconomy.tech j).profit posProfitPrice := by
    have hDotSum : posProfitPrice ⬝ᵥ (fun l => ∑ j, y j l)
        = ∑ j, posProfitPrice ⬝ᵥ y j := by
      simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hDotSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact ((posProfitEconomy.tech j).profit_eq_dotProduct_of_mem_supply
      posProfitPlan_mem_supply).symm
  rw [posProfitEconomy.aggregateExcess_eq, dotProduct_sub, hAggExcessVal, hNetOutputVal, sub_self]

/-- **`aggregateExcess_eq`**: The production excess equals the exchange excess minus aggregate net
output. Checked structurally on the Crusoe allocation/plan. -/
theorem crusoe_aggregateExcess_eq :
    crusoe.aggregateExcess crusoeAlloc crusoePlan
      = crusoe.toEconomy.aggregateExcess crusoeAlloc - (fun l => ∑ j, crusoePlan j l) :=
  crusoe.aggregateExcess_eq crusoeAlloc crusoePlan

/-- **`aggregate_net_spending` on Crusoe**: The net-spending identity holds at the equilibrium
consumption. The right-hand profit sum is `0` here (constant returns), in contrast to the `1/4` of
`posProfitEconomy` — together they witness that the profit term tracks the actual profit value. -/
theorem crusoe_aggregate_net_spending :
    (∑ a, (crusoePrice ⬝ᵥ crusoeAlloc a - crusoe.wealth crusoePrice a))
      = crusoePrice ⬝ᵥ crusoe.toEconomy.aggregateExcess crusoeAlloc
        - ∑ j, (crusoe.tech j).profit crusoePrice :=
  crusoe.aggregate_net_spending crusoePrice crusoeAlloc

/-- The Crusoe profit sum in `aggregate_net_spending` is `0` (constant-returns cone). The contrast
with `posProfitEconomy_profit_sum_eq` (`= 1/4`) is the non-vacuity point: The profit term is not a
hard-wired constant; it equals the technology's actual profit. -/
theorem crusoe_profit_sum_eq :
    (∑ j, (crusoe.tech j).profit crusoePrice) = 0 := by
  haveI : Unique crusoe.Firms := inferInstanceAs (Unique Unit)
  rw [Fintype.sum_unique]
  exact crusoe_profit_eq_zero

/-- **`walras_law_prod` on the firm-connected economy**, with the equilibrium `W` genuinely
*obtained* (not assumed): `firmConnected_equilibrium_exists` produces a Walrasian equilibrium with
production, and at it the value of aggregate excess demand is zero with profit-maximizing firms.
This
discharges every hypothesis from the economy's own existence theorem, so the witness is
unconditional. -/
theorem firmConnected_walras_law_prod :
    ∃ W : WalrasianEquilibriumWithProduction
      EconlibExamples.Equilibrium.FirmConnected.firmConnected,
      W.price ⬝ᵥ EconlibExamples.Equilibrium.FirmConnected.firmConnected.aggregateExcess
        W.alloc W.plan = 0 := by
  obtain ⟨W⟩ := EconlibExamples.Equilibrium.FirmConnected.firmConnected_equilibrium_exists
  exact ⟨W, EconlibExamples.Equilibrium.FirmConnected.firmConnected.walras_law_prod
    EconlibExamples.Equilibrium.FirmConnected.firmConnected_regular_prod W.isOptimal W.profit_max⟩

/-! ## Block 4: The production existence chain on real data (`Existence.lean`)

We exercise `exists_equilibrium_data_prod`, `exists_quasi_equilibrium_prod`,
`quasi_to_walrasian_prod`, `exists_attainable_profile_bound`, and
`mem_supply_of_mem_truncSupply_of_interior` on the concrete Robinson Crusoe (and firm-connected)
economies, discharging every hypothesis from their actual regularity / irreducibility / positive-
wealth instances. This runs the Kakutani fixed point and its truncated-technology scaffolding
(`truncTech_*`, `truncDemand_*`, `truncWealth_*`, `walras_law_trunc`,
`aggregate_net_spending_trunc`) transitively — certifying the chain is not vacuous. -/

open EconlibExamples.Equilibrium.RobinsonCrusoe (crusoe_irreducible crusoe_endow_valued)

/-- The Crusoe agent type is finite (an instance the existence chain consumes). -/
instance : Finite crusoe.Agents := inferInstanceAs (Finite Unit)

/-- **`exists_attainable_profile_bound`**: Attainable production profiles for the Crusoe economy
are uniformly norm-bounded — the radius that the truncated fixed point is run at. -/
theorem crusoe_exists_attainable_profile_bound :
    ∃ R : ℝ, 0 < R ∧ ∀ y : crusoe.Firms → Fin 2 → ℝ,
      (∀ j, y j ∈ (crusoe.tech j).Y) →
        (∀ l, -∑ a : crusoe.Agents, crusoe.endow a l ≤ ∑ j : crusoe.Firms, y j l) →
          ∀ j, ‖y j‖ ≤ R :=
  crusoe.exists_attainable_profile_bound crusoe_regular_prod

/-- **`exists_equilibrium_data_prod`**: For the concrete Crusoe economy there exist nonnegative
(some positive) prices, a profit-maximizing plan, a consumer-optimal allocation, and market
clearing. Every hypothesis is discharged from the economy's actual data, so the
truncated-technology Kakutani argument runs, certifying non-vacuity. -/
theorem crusoe_exists_equilibrium_data_prod :
    ∃ (p : Fin 2 → ℝ) (x : crusoe.Agents → Fin 2 → ℝ) (y : crusoe.Firms → Fin 2 → ℝ),
      (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ j, y j ∈ (crusoe.tech j).supply p) ∧
      (∀ a, x a ∈ crusoe.consumerDemand p a) ∧
      (∀ l, crusoe.aggregateExcess x y l ≤ 0) ∧ p ⬝ᵥ crusoe.aggregateExcess x y = 0 :=
  crusoe.exists_equilibrium_data_prod (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod
    crusoe_irreducible.toIrreducibleProd (by norm_num) crusoe_endow_valued

/-- **`exists_quasi_equilibrium_prod`**: Simplex prices and a budget-binding,
individually-rational, quasi-optimal, market-clearing allocation with a profit-maximizing plan for
the Crusoe economy. This is the pre-`quasi_to_walrasian_prod` object. -/
theorem crusoe_exists_quasi_equilibrium_prod :
    ∃ (p : Fin 2 → ℝ) (x : crusoe.Agents → Fin 2 → ℝ) (y : crusoe.Firms → Fin 2 → ℝ),
      p ∈ priceSimplex 2 ∧
      (∀ a, x a ∈ crusoe.budgetSet p a) ∧
      (∀ a, p ⬝ᵥ x a = crusoe.wealth p a) ∧
      (∀ a, (crusoe.pref a).le (x a) (crusoe.endow a)) ∧
      (∀ j, y j ∈ (crusoe.tech j).supply p) ∧
      (∀ a z, (∀ l, 0 ≤ z l) → p ⬝ᵥ z < crusoe.wealth p a → ¬ (crusoe.pref a).lt z (x a)) ∧
      (∀ l, crusoe.aggregateExcess x y l ≤ 0) ∧ p ⬝ᵥ crusoe.aggregateExcess x y = 0 :=
  crusoe.exists_quasi_equilibrium_prod (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod
    (by norm_num)

/-- **`quasi_to_walrasian_prod`**: The quasi-to-Walrasian upgrade for the Crusoe economy. Fed the
quasi-equilibrium data produced above (every hypothesis genuinely discharged from it), it yields
strictly positive prices and genuine consumer optimality. -/
theorem crusoe_quasi_to_walrasian_prod :
    ∃ (p : Fin 2 → ℝ) (x : crusoe.Agents → Fin 2 → ℝ),
      (∀ l, 0 < p l) ∧ ∀ a, x a ∈ crusoe.consumerDemand p a := by
  obtain ⟨p, x, y, hp_mem, hbud, hbind, hIR, hsupply, hquasi, _hclear_le, _hclear_val⟩ :=
    crusoe_exists_quasi_equilibrium_prod
  -- `quasi_to_walrasian_prod` needs a positive-wealth agent. Crusoe's endowment is valued
  -- positively because the firm supplies (`crusoe_endow_valued`), and wealth ≥ endowment value.
  have hagg : ∃ a, 0 < crusoe.wealth p a := by
    obtain ⟨a, ha⟩ := crusoe_endow_valued p hp_mem (fun j => ⟨y j, hsupply j⟩)
    refine ⟨a, ?_⟩
    have hprofit_nn : 0 ≤ ∑ j, crusoe.share a j * (crusoe.tech j).profit p := by
      refine Finset.sum_nonneg fun j _ => mul_nonneg (crusoe.share_nonneg a j) ?_
      have h0 : p ⬝ᵥ (0 : Fin 2 → ℝ) ≤ (crusoe.tech j).profit p :=
        (crusoe.tech j).dotProduct_le_profit_of_mem_supply
          (crusoe_regular_prod.techReg j).inaction (hsupply j)
      simpa using h0
    have : crusoe.wealth p a = p ⬝ᵥ crusoe.endow a +
        ∑ j, crusoe.share a j * (crusoe.tech j).profit p := rfl
    rw [this]; linarith
  obtain ⟨hpos, hopt⟩ :=
    crusoe.quasi_to_walrasian_prod (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod
      crusoe_irreducible.toIrreducibleProd hp_mem hbud hbind hIR hsupply hquasi hagg
  exact ⟨p, x, hpos, hopt⟩

/-! ### `mem_supply_of_mem_truncSupply_of_interior` on the positive-profit technology

The interesting non-vacuity instance: At radius `M = 1` the truncated supply of `posProfitTech`
still contains the global optimum `(-1/4, 1/2)` (its sup-norm `1/2 < 1`), so the lemma recovers the
*untruncated* optimum. This is exactly the step the existence proof uses to escape the
truncation. -/

/-- The sup norm of the optimal plan `(-1/4, 1/2)` is `1/2`. -/
theorem posProfitPlan_norm_eq : ‖posProfitPlan‖ = 1 / 2 := by
  have h0 : ‖posProfitPlan 0‖ = 1 / 4 := by simp [posProfitPlan]
  have h1 : ‖posProfitPlan 1‖ = 1 / 2 := by simp [posProfitPlan]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun l => ?_) ?_
  · fin_cases l
    · simpa [h0] using (by norm_num : (1 : ℝ) / 4 ≤ 1 / 2)
    · simp [h1]
  · exact (norm_le_pi_norm posProfitPlan 1).trans' h1.ge

/-- The optimal plan lies in the truncated technology at radius `1`: It is in `Y` and in
`closedBall 0 1` (sup norm `1/2 ≤ 1`). -/
theorem posProfitPlan_mem_truncTech :
    posProfitPlan ∈ (ProductionEconomy.truncTech posProfitTech 1).Y := by
  refine ⟨posProfitPlan_mem_supply.1, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, posProfitPlan_norm_eq]
  norm_num

/-- The optimal plan maximizes profit over the *truncated* technology — proved **directly** from the
quadratic bound `(m - 1/2)^2 ≥ 0` (not by invoking the untruncated `posProfitPlan_mem_supply.2`), so
that the recovery `posProfit_mem_supply_of_mem_truncSupply` below is not circular: the truncated
optimality is established on its own footing and the lemma then lifts it to genuine supply. -/
theorem posProfitPlan_mem_truncSupply :
    posProfitPlan ∈ (ProductionEconomy.truncTech posProfitTech 1).supply posProfitPrice := by
  refine ⟨posProfitPlan_mem_truncTech, fun z hz => ?_⟩
  -- `z ∈ truncTech.Y ⊆ Y`, so `z 0 ≤ -(max (z 1) 0)^2`; the quadratic argument runs in place.
  rw [ProductionEconomy.truncTech_Y] at hz
  have hzY : z 0 ≤ -(max (z 1) 0) ^ 2 := hz.1
  change posProfitPrice ⬝ᵥ z ≤ posProfitPrice ⬝ᵥ posProfitPlan
  have hdot_z : posProfitPrice ⬝ᵥ z = z 0 + z 1 := by
    simp [posProfitPrice, dotProduct, Fin.sum_univ_two]
  have hdot_plan : posProfitPrice ⬝ᵥ posProfitPlan = 1 / 4 := by
    simp [posProfitPrice, posProfitPlan, dotProduct, Fin.sum_univ_two]; norm_num
  rw [hdot_z, hdot_plan]
  have hm1 : z 1 ≤ max (z 1) 0 := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ max (z 1) 0 := le_max_right _ _
  set m := max (z 1) 0 with hm
  nlinarith [sq_nonneg (m - 1 / 2), hzY, hm1, hm0]

/-- **`mem_supply_of_mem_truncSupply_of_interior`**: Since the truncated optimum `(-1/4, 1/2)` lies
strictly inside the truncation ball (`‖·‖ = 1/2 < 1`), it is an *untruncated* profit maximizer. The
truncation does not bind, recovering the genuine supply. -/
theorem posProfit_mem_supply_of_mem_truncSupply :
    posProfitPlan ∈ posProfitTech.supply posProfitPrice :=
  ProductionEconomy.mem_supply_of_mem_truncSupply_of_interior posProfitTech_regular.convex
    posProfitPlan_mem_truncSupply (by rw [posProfitPlan_norm_eq]; norm_num)

/-! ### The existence chain on the firm-connected economy

The firm-connected economy is the strictly harder non-vacuity case: Exchange `Irreducible`
**fails** (`firmConnected_not_irreducible`), so this data is genuinely beyond the consumption-only
existence theorem; only the firm-aware `IrreducibleProd` reaches it. -/

open EconlibExamples.Equilibrium.FirmConnected (firmConnected firmConnected_regular_prod
  firmConnected_irreducibleProd firmConnected_endow_valued)

/-- **`exists_equilibrium_data_prod` on the firm-connected economy** — the production existence
chain run on data the consumption-only theorem cannot reach. -/
theorem firmConnected_exists_equilibrium_data_prod :
    ∃ (p : Fin 2 → ℝ) (x : firmConnected.Agents → Fin 2 → ℝ) (y : firmConnected.Firms → Fin 2 → ℝ),
      (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ j, y j ∈ (firmConnected.tech j).supply p) ∧
      (∀ a, x a ∈ firmConnected.consumerDemand p a) ∧
      (∀ l, firmConnected.aggregateExcess x y l ≤ 0) ∧
        p ⬝ᵥ firmConnected.aggregateExcess x y = 0 :=
  firmConnected.exists_equilibrium_data_prod (inferInstanceAs (Nonempty (Fin 2)))
    firmConnected_regular_prod firmConnected_irreducibleProd (by norm_num)
    firmConnected_endow_valued

/-- **`exists_quasi_equilibrium_prod` on the firm-connected economy.** -/
theorem firmConnected_exists_quasi_equilibrium_prod :
    ∃ (p : Fin 2 → ℝ) (x : firmConnected.Agents → Fin 2 → ℝ) (y : firmConnected.Firms → Fin 2 → ℝ),
      p ∈ priceSimplex 2 ∧
      (∀ a, x a ∈ firmConnected.budgetSet p a) ∧
      (∀ a, p ⬝ᵥ x a = firmConnected.wealth p a) ∧
      (∀ a, (firmConnected.pref a).le (x a) (firmConnected.endow a)) ∧
      (∀ j, y j ∈ (firmConnected.tech j).supply p) ∧
      (∀ a z, (∀ l, 0 ≤ z l) → p ⬝ᵥ z < firmConnected.wealth p a →
        ¬ (firmConnected.pref a).lt z (x a)) ∧
      (∀ l, firmConnected.aggregateExcess x y l ≤ 0) ∧
        p ⬝ᵥ firmConnected.aggregateExcess x y = 0 :=
  firmConnected.exists_quasi_equilibrium_prod (inferInstanceAs (Nonempty (Fin 2)))
    firmConnected_regular_prod (by norm_num)

end EconlibTest.Equilibrium.Production

end
