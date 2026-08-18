/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Equilibrium.CobbDouglasEdgeworth
import EconlibExamples.Equilibrium.RobinsonCrusoe
import Mathlib

/-!
# Welfare-theorem non-vacuity witnesses

Compile-time semantic witnesses for the two Second Welfare Theorems of `Econlib.Equilibrium`
(`SecondWelfare.lean`, exchange; `Production/SecondWelfare.lean`, production). The first welfare
direction is already exercised through `WalrasianEquilibrium.paretoOptimal` on the concrete
Edgeworth box; the hard content here is the **second** welfare theorem *with lump-sum transfers*,
instantiated at a Pareto optimum that is **not** the no-transfer equilibrium — the failure mode the
audit flagged.

## The off-equilibrium Pareto optimum (exchange)

The symmetric Cobb–Douglas Edgeworth box (`EconlibExamples...CobbDouglasEdgeworth`) has endowments
`e₀ = (2,1)`, `e₁ = (1,2)`, aggregate `(3,3)`, and a *unique* no-transfer equilibrium at the equal
split `(3/2, 3/2)` for both agents (`edgeworth_unique`). We pick a **different** point on the
contract curve:

* `offAlloc 0 = (1,1)`, `offAlloc 1 = (2,2)` — aggregate `(3,3)` (feasible), but agent `0` consumes
  `(1,1) ≠ (3/2,3/2)`, so this is *not* the no-transfer equilibrium (`offAlloc_ne_edgeAlloc`).

Both bundles lie on the diagonal `x₀ = x₁`, where the symmetric geometric-mean utility has marginal
rate of substitution `MRS = x₁/x₀ = 1`. Equal `MRS` across agents is exactly the contract-curve /
Pareto-optimality first-order condition (`offAlloc_equal_mrs`), and the common direction `(1,1)` is
the supporting price. We *prove* Pareto optimality by exhibiting `offAlloc` as the no-transfer
Walrasian equilibrium of the **re-endowed** economy `transferEndow offAlloc` (each agent endowed
with its own bundle, CD-demand-optimal at `(1,1)`) and applying the first welfare theorem there;
feasibility/dominance depend only on the aggregate endowment `(3,3)`, which is unchanged, so the
optimum transports back to the original box (`offAlloc_paretoOptimal`).

Feeding this off-equilibrium optimum to `ParetoOptimal.exists_walrasianEquilibriumWithTransfers`
(with the strictly-positive endowment `offAlloc` discharging McKenzie irreducibility) produces a
genuine `WalrasianEquilibriumWithTransfers` object — supporting prices *and* balanced transfers —
at an allocation the no-transfer theorem can never reach.

## The off-equilibrium Pareto optimum (production)

Robinson Crusoe (`EconlibExamples...RobinsonCrusoe`) has one agent, one firm, endowment `(1,0)`,
linear utility `u x = x₀ + x₁`, and a constant-returns labor technology. Its equilibrium
consumption `(0,1)` leaves good `0` (leisure) unconsumed, so the "every good consumed" hypothesis
`hcons` of `exists_walrasianEquilibriumWithProductionAndTransfers` *fails* there. We therefore pick
a different welfare optimum that consumes both goods:

* `crusoeAlloc2 () = (1/2, 1/2)`, `crusoePlan2 () = (-1/2, 1/2)` — keep half the labor as leisure,
  turn the other half into output. Utility `1`, identical to the equilibrium's, and feasible with
  exact clearing, so it is Pareto optimal (`crusoeAlloc2_paretoOptimal`), yet consumes good `0`
  positively (`crusoe_hcons`).

This feeds `exists_consumer_supporting_price`, `exists_quasiEquilibrium_price`, and
`exists_walrasianEquilibriumWithProductionAndTransfers` (irreducibility holding vacuously on the
`Unit` agent space).

CAVEAT (production side): unlike the exchange off-equilibrium optimum, `crusoeAlloc2` is *itself* a
no-transfer Walrasian equilibrium with production (`crusoeEquilibrium2`) — with linear utility,
wealth `1`, profit `0`, and zero aggregate excess, zero transfers suffice. So the production witness
certifies the SWT at an *alternative no-transfer equilibrium satisfying `hcons`*, not at a point
requiring nontrivial transfers (which this economy does not admit among both-goods optima). The
exchange side is where the genuinely-off-equilibrium, transfer-`(-1,+1)` decentralization lives.
-/

noncomputable section

namespace EconlibTest.Equilibrium.Welfare

open Econlib.Equilibrium Econlib.Preferences Econlib.Optimization Matrix

/-! ## Part 1: Exchange — the separating-hyperplane inputs and first welfare -/

open EconlibExamples.Equilibrium.CobbDouglasEdgeworth (economy economy_regular cdU edgeEndow
  edgePrice edgeAlloc edgeworthEquilibrium edge_wealth edgeworth_unique)

/-- **First welfare theorem** witnessed on the concrete box: The Edgeworth equilibrium allocation
is Pareto optimal (consuming `WalrasianEquilibrium.paretoOptimal`). -/
theorem edge_first_welfare : economy.ParetoOptimal edgeworthEquilibrium.alloc :=
  edgeworthEquilibrium.paretoOptimal economy_regular

/-- **`strictlyPreferredPos_isOpen`** on the concrete economy at the equilibrium allocation. -/
theorem strictlyPreferredPos_isOpen_witness (a : economy.Agents) :
    IsOpen (economy.strictlyPreferredPos edgeAlloc a) :=
  Economy.strictlyPreferredPos_isOpen economy_regular edgeAlloc a

/-- **`strictlyPreferredPos_convex`** on the concrete economy at the equilibrium allocation. -/
theorem strictlyPreferredPos_convex_witness (a : economy.Agents) :
    Convex ℝ (economy.strictlyPreferredPos edgeAlloc a) :=
  Economy.strictlyPreferredPos_convex economy_regular edgeAlloc a

/-- **`strictlyPreferredPos_nonempty`** on the concrete economy: The equilibrium allocation is
nonnegative, so each agent's strictly-preferred-positive set is inhabited. -/
theorem strictlyPreferredPos_nonempty_witness (a : economy.Agents) :
    (economy.strictlyPreferredPos edgeAlloc a).Nonempty :=
  Economy.strictlyPreferredPos_nonempty economy_regular (by norm_num)
    (fun a l => by fin_cases a <;> fin_cases l <;> norm_num [edgeAlloc]) a

/-! ## Part 2: Exchange — the off-equilibrium Pareto optimum -/

/-- The off-equilibrium allocation: Agent `0` consumes `(1,1)`, agent `1` consumes `(2,2)`. Its
aggregate is `(3,3)`, matching the box's aggregate endowment, so it is feasible — but it is *not*
the equal-split equilibrium. -/
def offAlloc : Fin 2 → (Fin 2 → ℝ) := ![![1, 1], ![2, 2]]

/-- The off-equilibrium allocation is nonnegative. -/
theorem offAlloc_mem_nonnegOrthant : ∀ a, offAlloc a ∈ nonnegOrthant 2 :=
  fun a l => by fin_cases a <;> fin_cases l <;> norm_num [offAlloc]

/-- The off-equilibrium allocation differs from the no-transfer equilibrium split `(3/2,3/2)`:
Agent `0` consumes `(1,1) ≠ (3/2,3/2)`. -/
theorem offAlloc_ne_edgeAlloc : offAlloc ≠ edgeAlloc := by
  intro heq
  have h := congr_fun (congr_fun heq 0) 0
  simp only [offAlloc, edgeAlloc, Matrix.cons_val_zero] at h
  norm_num at h

/-- **No no-transfer Walrasian equilibrium reaches `offAlloc`** (consuming `edgeworth_unique`):
every
no-transfer equilibrium of the box has allocation `edgeAlloc` (the unique equal split), so since
`offAlloc ≠ edgeAlloc`, none has allocation `offAlloc`. This is the genuine content the prose
advertised — that the off-equilibrium optimum is unreachable *without* transfers — and a broken or
missing uniqueness theorem would be caught here. -/
theorem offAlloc_not_walrasian (W : economy.WalrasianEquilibrium) : W.alloc ≠ offAlloc := by
  rw [(edgeworth_unique W).2]
  exact fun h => offAlloc_ne_edgeAlloc h.symm

/-- **Diagonal coordinate-ratio check.** Both `offAlloc 0 = (1,1)` and `offAlloc 1 = (2,2)` lie on
the diagonal `x₀ = x₁`, so their coordinate ratios `x₁/x₀` agree (both `1`). For the symmetric
geometric-mean Cobb–Douglas utility this ratio is the marginal rate of substitution, and equal MRS
across agents is the contract-curve first-order condition; but this theorem proves only the bare
arithmetic identity `1/1 = 2/2` on `offAlloc`, *not* the differential MRS statement nor Pareto
optimality. The genuine Pareto-optimality content is `offAlloc_paretoOptimal` (first welfare theorem
on the re-endowed economy); this is merely an orienting sanity anchor for the diagonal. -/
theorem offAlloc_diagonal_ratio :
    offAlloc 0 1 / offAlloc 0 0 = offAlloc 1 1 / offAlloc 1 0 := by
  norm_num [offAlloc]

/-- The re-endowed economy whose endowments are `offAlloc` (each agent endowed with its own
off-equilibrium bundle). Same agents and CD preferences as the box; aggregate endowment still
`(3,3)`. -/
def offEconomy : Economy 2 := economy.transferEndow offAlloc_mem_nonnegOrthant

/-- `offEconomy` is regular: CD preferences with the strictly positive endowment `offAlloc`. -/
theorem offEconomy_regular : RegularEconomy offEconomy :=
  RegularEconomy.ofCobbDouglas (by norm_num) offEconomy (fun _ => cdU) (fun _ => rfl)
    (fun a l => by
      change (0 : ℝ) < offAlloc a l
      fin_cases a <;> fin_cases l <;> norm_num [offAlloc])

/-- Each agent's wealth in `offEconomy` at the price `(1,1)` is its bundle's coordinate sum: Agent
`0` has `2`, agent `1` has `4`. -/
theorem off_wealth (a : economy.Agents) :
    edgePrice ⬝ᵥ offEconomy.endow a = (offAlloc a 0 + offAlloc a 1) := by
  change edgePrice ⬝ᵥ offAlloc a = offAlloc a 0 + offAlloc a 1
  simp [edgePrice, dotProduct, Fin.sum_univ_two]

/-- **Each agent's own bundle is its CD demand in the re-endowed economy** at price `(1,1)`: Agent
`0` endowed `(1,1)` with wealth `2` demands `(1,1)`; agent `1` endowed `(2,2)` with wealth `4`
demands `(2,2)`. -/
theorem offAlloc_demand_optimal (a : economy.Agents) :
    offAlloc a ∈ offEconomy.demand edgePrice a := by
  -- Strictly positive price and wealth feed the CD closed form.
  have hpos : ∀ l, 0 < edgePrice l := fun l => by fin_cases l <;> norm_num [edgePrice]
  have hw : (0 : ℝ) < edgePrice ⬝ᵥ offEconomy.endow a := by
    rw [off_wealth a]; fin_cases a <;> norm_num [offAlloc]
  -- `offEconomy.pref a = preferenceOfRealUtility cdU.uTotal` definitionally.
  have hsingle := offEconomy.demand_eq_singleton_of_cobbDouglas (by norm_num) a cdU rfl hpos hw
  rw [hsingle]
  -- The share bundle evaluates to `offAlloc a`.
  have hα_sum : ∑ i, cdU.α i = 1 := by rw [Fin.sum_univ_two]; norm_num [cdU]
  have hbundle : (fun l => (cdU.α l / ∑ i, cdU.α i) * (edgePrice ⬝ᵥ offEconomy.endow a)
      / edgePrice l) = offAlloc a := by
    funext l
    rw [hα_sum, off_wealth a]
    fin_cases a <;> fin_cases l <;> norm_num [cdU, edgePrice, offAlloc]
  rw [hbundle]
  exact Set.mem_singleton _

/-- Markets clear in `offEconomy` at price `(1,1)`: Each agent consuming its own endowment makes
aggregate excess identically zero. -/
theorem off_market_clears : offEconomy.MarketClears edgePrice offAlloc := by
  -- In `offEconomy` the endowment IS `offAlloc`, so aggregate excess is identically zero.
  have hexc : offEconomy.aggregateExcess offAlloc = 0 := by
    funext l
    change (∑ a, offAlloc a l) - (∑ a, offAlloc a l) = (0 : Fin 2 → ℝ) l
    simp
  refine ⟨fun l => ?_, ?_⟩ <;> rw [hexc] <;> simp

/-- **Exact clearing of `offAlloc` in the *original* box** (not just self-endowment clearing in the
re-endowed economy): the aggregate of `offAlloc` is `(1,1) + (2,2) = (3,3)`, matching the box's
aggregate endowment `(3,3)`, so `economy.aggregateExcess offAlloc = 0` exactly. A sign reversal in
`aggregateExcess` would be caught (the per-coordinate excess is genuinely `3 − 3`, not `0 − 0`). -/
theorem offAlloc_box_clears : economy.aggregateExcess offAlloc = 0 := by
  funext l
  change (∑ a : Fin 2, offAlloc a l) - (∑ a : Fin 2, edgeEndow a l) = (0 : Fin 2 → ℝ) l
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  change (offAlloc 0 l + offAlloc 1 l) - (edgeEndow 0 l + edgeEndow 1 l) = 0
  fin_cases l <;> norm_num [offAlloc, edgeEndow]

/-- The assembled no-transfer Walrasian equilibrium of the **re-endowed** economy. -/
def offEquilibrium : offEconomy.WalrasianEquilibrium where
  price := edgePrice
  alloc := offAlloc
  price_cone := fun l => by fin_cases l <;> simp [edgePrice]
  price_ne := ⟨0, by simp [edgePrice]⟩
  isOptimal := offAlloc_demand_optimal
  clears := off_market_clears

/-- Feasibility in the box and in the re-endowed economy coincide: Both have aggregate endowment
`(3,3)`, so the aggregate-excess (hence feasibility) constraints are identical. -/
theorem offEconomy_feasible_iff (g : economy.Agents → Fin 2 → ℝ) :
    offEconomy.Feasible g ↔ economy.Feasible g := by
  -- The two economies share the aggregate endowment `(3,3)`, so the aggregate-excess (hence
  -- feasibility) constraints coincide; the nonnegativity conjunct is identical.
  have hagg_eq : ∀ l, (∑ a, offEconomy.endow a l) = (∑ a, economy.endow a l) := by
    intro l
    change (∑ a : Fin 2, offAlloc a l) = (∑ a : Fin 2, edgeEndow a l)
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases l <;> norm_num [offAlloc, edgeEndow]
  have hexc_eq : ∀ l, offEconomy.aggregateExcess g l = economy.aggregateExcess g l := by
    intro l
    change (∑ a, g a l) - (∑ a, offEconomy.endow a l) = (∑ a, g a l) - (∑ a, economy.endow a l)
    rw [hagg_eq l]
  constructor
  · rintro ⟨hnn, hexc⟩
    exact ⟨hnn, fun l => (hexc_eq l) ▸ hexc l⟩
  · rintro ⟨hnn, hexc⟩
    exact ⟨hnn, fun l => (hexc_eq l).symm ▸ hexc l⟩

/-- **Pareto optimality of the off-equilibrium allocation.** `offAlloc` is the no-transfer
equilibrium of the re-endowed economy, hence Pareto optimal *there* (first welfare theorem); since
feasibility and dominance depend only on the (unchanged) aggregate endowment and the (identical)
preferences, the optimum transports back to the original box. -/
theorem offAlloc_paretoOptimal : economy.ParetoOptimal offAlloc := by
  -- First welfare theorem on the re-endowed economy: `offAlloc` is its no-transfer equilibrium.
  have hpo' : offEconomy.ParetoOptimal offAlloc := offEquilibrium.paretoOptimal offEconomy_regular
  obtain ⟨hfeas', hnodom'⟩ := hpo'
  -- Transport feasibility and (preference-only) dominance back to the original box.
  refine ⟨(offEconomy_feasible_iff offAlloc).mp hfeas', ?_⟩
  rintro ⟨y, hy_feas, hy_dom⟩
  -- `ParetoDominates` depends only on preferences, which `offEconomy` shares with `economy`.
  exact hnodom' ⟨y, (offEconomy_feasible_iff y).mpr hy_feas, hy_dom⟩

/-! ## Part 3: Exchange — the Second Welfare Theorem with transfers -/

/-- Every good is consumed in `offAlloc` (`(1,1)` and `(2,2)` are both strictly positive). -/
theorem off_hcons : ∀ l, ∃ a, 0 < offAlloc a l :=
  fun l => ⟨0, by fin_cases l <;> norm_num [offAlloc]⟩

/-- The re-endowed economy is McKenzie-irreducible: `offAlloc` is strictly positive and CD
preferences are strictly monotone toward the interior. -/
theorem offEconomy_irreducible :
    Irreducible (economy.transferEndow (fun a => offAlloc_paretoOptimal.1.1 a)) :=
  Irreducible.of_pos_endow _ (by norm_num)
    (fun a l => by
      change (0 : ℝ) < offAlloc a l
      fin_cases a <;> fin_cases l <;> norm_num [offAlloc])
    (fun a => economy_regular.mono a)

/-- **Second Welfare Theorem with lump-sum transfers**, instantiated at the *non-trivial* Pareto
optimum `offAlloc` (≠ the no-transfer equilibrium). The library theorem produces a genuine
`WalrasianEquilibriumWithTransfers` object — supporting prices *and* a balanced transfer scheme —
whose allocation is bound to `offAlloc` and whose transfers are the supported scheme
`t a = price ⬝ᵥ offAlloc a − price ⬝ᵥ endow a`, at an allocation the no-transfer existence theorem
cannot reach (`offAlloc_not_walrasian`). The allocation binding `W.alloc = offAlloc` is what
discriminates this from the zero-transfer Edgeworth equilibrium; the *concrete* price `(1,1)` and
hand-computed numeric transfers `(-1, +1)` — which the abstract supporting price does not fix — are
supplied separately by `off_second_welfare_binds` below. -/
theorem off_second_welfare :
    ∃ W : economy.WalrasianEquilibriumWithTransfers, W.Decentralizes offAlloc :=
  offAlloc_paretoOptimal.exists_walrasianEquilibriumWithTransfers
    (inferInstanceAs (Nonempty (Fin 2))) economy_regular (by norm_num) off_hcons
    offEconomy_irreducible

/-- The lump-sum transfers that decentralize `offAlloc` at price `(1,1)`: `t a = p ⬝ᵥ offAlloc a −
p ⬝ᵥ endow a`, i.e. `t 0 = 2 − 3 = −1` and `t 1 = 4 − 3 = +1`. They balance (`∑ t = 0`). -/
def offTransfer : economy.Agents → ℝ :=
  fun a => edgePrice ⬝ᵥ offAlloc a - edgePrice ⬝ᵥ economy.endow a

/-- The transfers are exactly `(-1, +1)` — the hand-computed values. -/
theorem offTransfer_anchor : offTransfer (0 : Fin 2) = -1 ∧ offTransfer (1 : Fin 2) = 1 := by
  constructor
  · change edgePrice ⬝ᵥ offAlloc (0 : Fin 2) - edgePrice ⬝ᵥ edgeEndow (0 : Fin 2) = -1
    rw [edge_wealth]; simp [edgePrice, dotProduct, Fin.sum_univ_two, offAlloc]; norm_num
  · change edgePrice ⬝ᵥ offAlloc (1 : Fin 2) - edgePrice ⬝ᵥ edgeEndow (1 : Fin 2) = 1
    rw [edge_wealth]; simp [edgePrice, dotProduct, Fin.sum_univ_two, offAlloc]; norm_num

/-- **The decentralizing equilibrium with transfers, built explicitly** with `alloc = offAlloc`.
Each
agent's bundle is its CD demand at the transfer-adjusted wealth `p ⬝ᵥ offAlloc a` (transported from
`offAlloc_demand_optimal`, since the re-endowed economy's budget at `a` is `budgetSetAt p (p ⬝ᵥ
offAlloc a)` and shares `economy`'s preferences), and markets clear because the aggregate of
`offAlloc` matches the aggregate endowment `(3,3)`. -/
def offEquilibriumWithTransfers : economy.WalrasianEquilibriumWithTransfers where
  price := edgePrice
  alloc := offAlloc
  transfer := offTransfer
  price_cone := fun l => by fin_cases l <;> simp [edgePrice]
  price_ne := ⟨0, by simp [edgePrice]⟩
  transfers_balance := by
    change ∑ a : Fin 2, offTransfer a = 0
    rw [Fin.sum_univ_two]
    change (edgePrice ⬝ᵥ offAlloc 0 - edgePrice ⬝ᵥ edgeEndow 0)
      + (edgePrice ⬝ᵥ offAlloc 1 - edgePrice ⬝ᵥ edgeEndow 1) = 0
    rw [edge_wealth 0, edge_wealth 1]
    simp [edgePrice, dotProduct, Fin.sum_univ_two, offAlloc]; norm_num
  isOptimal := fun a => by
    -- transfer-adjusted wealth `p ⬝ᵥ endow a + (p ⬝ᵥ offAlloc a − p ⬝ᵥ endow a) = p ⬝ᵥ offAlloc a`.
    have hw : edgePrice ⬝ᵥ economy.endow a + offTransfer a = edgePrice ⬝ᵥ offAlloc a := by
      simp only [offTransfer]; ring
    rw [hw]
    -- this budget IS `offEconomy.budgetSet edgePrice a` (endow there is `offAlloc`),
    -- and prefs match.
    have hmem := offAlloc_demand_optimal a
    rw [Economy.demand, Economy.budgetSet] at hmem
    change offAlloc a ∈ argmaxRel (offEconomy.pref a)
      (budgetSetAt edgePrice (edgePrice ⬝ᵥ offEconomy.endow a)) at hmem
    have hendow : edgePrice ⬝ᵥ offEconomy.endow a = edgePrice ⬝ᵥ offAlloc a := rfl
    rw [hendow] at hmem
    exact hmem
  clears := by
    refine ⟨fun l => ?_, ?_⟩ <;> rw [offAlloc_box_clears] <;> simp

/-- **Allocation/transfer-binding SWT witness** (the discriminating strengthening of
`off_second_welfare`): there is a Walrasian-equilibrium-with-transfers whose allocation is *exactly*
`offAlloc` and whose transfers are the hand-computed `(-1, +1)`. This pins the decentralized object
to the off-equilibrium optimum — a witness the original zero-transfer Edgeworth equilibrium cannot
satisfy. -/
theorem off_second_welfare_binds :
    ∃ W : economy.WalrasianEquilibriumWithTransfers,
      W.alloc = offAlloc ∧ W.transfer (0 : Fin 2) = -1 ∧ W.transfer (1 : Fin 2) = 1 :=
  ⟨offEquilibriumWithTransfers, rfl, offTransfer_anchor.1, offTransfer_anchor.2⟩

/-! ## Part 4: Production — Robinson Crusoe Second Welfare Theorem -/

open EconlibExamples.Equilibrium.RobinsonCrusoe (crusoe crusoe_regular_prod crusoeTech
  crusoeCoef crusoePrice crusoe_lns crusoe_wealth crusoeAlloc)

/-- Off-equilibrium consumption: Crusoe keeps half his labor as leisure and consumes half a unit of
output. Both goods are consumed positively (unlike the equilibrium `(0,1)`). -/
def crusoeAlloc2 : Unit → (Fin 2 → ℝ) := fun _ => ![1/2, 1/2]

/-- Off-equilibrium production plan: Use half a unit of labor to make half a unit of output. -/
def crusoePlan2 : Unit → (Fin 2 → ℝ) := fun _ => ![-1/2, 1/2]

/-- The off-equilibrium plan maximizes profit at `(1,1)`: It lies in `Y` and earns the maximal
revenue `0`. -/
theorem crusoePlan2_mem_supply : crusoePlan2 () ∈ crusoeTech.supply crusoePrice := by
  refine ⟨⟨by norm_num [crusoePlan2], by norm_num [crusoePlan2]⟩, isMaxOn_iff.mpr fun z hz => ?_⟩
  obtain ⟨_, hz2⟩ := hz
  simp only [crusoePrice, dotProduct, Fin.sum_univ_two]
  norm_num [crusoePlan2]
  linarith

/-- Crusoe's off-equilibrium consumption `(1/2,1/2)` is demand-optimal: Wealth is `1`, and linear
utility `x₀ + x₁ = price ⬝ᵥ x ≤ 1`. -/
theorem crusoeAlloc2_mem_demand : crusoeAlloc2 () ∈ crusoe.consumerDemand crusoePrice () := by
  refine ⟨⟨fun l => by fin_cases l <;> norm_num [crusoeAlloc2], ?_⟩, fun y hy => ?_⟩
  · -- affordable: `price ⬝ᵥ (1/2,1/2) = 1 = wealth`
    show crusoePrice ⬝ᵥ crusoeAlloc2 () ≤ crusoe.wealth crusoePrice ()
    rw [crusoe_wealth]; simp [crusoePrice, dotProduct, Fin.sum_univ_two, crusoeAlloc2]; norm_num
  · -- utility-maximal: `u y = price ⬝ᵥ y ≤ wealth = u alloc`
    obtain ⟨_, hyw⟩ := hy
    change crusoeCoef ⬝ᵥ y ≤ crusoeCoef ⬝ᵥ crusoeAlloc2 ()
    rw [crusoe_wealth] at hyw
    simp only [crusoePrice, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul] at hyw
    simp only [crusoeCoef, dotProduct, Fin.sum_univ_two, crusoeAlloc2,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    norm_num
    linarith

/-- Aggregate excess is identically zero: Consumption `(1/2,1/2)` plus net production `(-1/2,1/2)`
exactly offsets the endowment `(1,0)`. -/
theorem crusoe2_excess_eq_zero : crusoe.aggregateExcess crusoeAlloc2 crusoePlan2 = 0 := by
  haveI : Unique crusoe.Agents := inferInstanceAs (Unique Unit)
  haveI : Unique crusoe.Firms := inferInstanceAs (Unique Unit)
  funext l
  fin_cases l <;>
    · simp only [ProductionEconomy.aggregateExcess, crusoe, crusoeAlloc2, crusoePlan2,
        Fintype.sum_unique, Pi.zero_apply]
      norm_num

/-- The assembled off-equilibrium Walrasian equilibrium with production. -/
def crusoeEquilibrium2 : WalrasianEquilibriumWithProduction crusoe where
  price := crusoePrice
  alloc := crusoeAlloc2
  plan := crusoePlan2
  price_cone := fun l => by fin_cases l <;> simp [crusoePrice]
  price_ne := ⟨0, by simp [crusoePrice]⟩
  profit_max := fun _ => crusoePlan2_mem_supply
  isOptimal := fun _ => crusoeAlloc2_mem_demand
  clears := by
    rw [crusoe2_excess_eq_zero]; exact ⟨fun l => by simp, by simp⟩

/-- **Pareto optimality of the off-equilibrium production allocation** (first welfare theorem with
production): `(1/2,1/2)` consumption with plan `(-1/2,1/2)` is a Walrasian equilibrium with
production, hence Pareto optimal. -/
theorem crusoeAlloc2_paretoOptimal :
    crusoe.ParetoOptimal crusoeAlloc2 crusoePlan2 :=
  crusoeEquilibrium2.paretoOptimal crusoe_lns

/-- The off-equilibrium production allocation differs from the equilibrium consumption `(0,1)`:
Crusoe keeps `1/2` of leisure (`crusoeAlloc2 () 0 = 1/2 ≠ 0`). -/
theorem crusoeAlloc2_ne_crusoeAlloc : crusoeAlloc2 ≠ crusoeAlloc := by
  intro heq
  have h := congr_fun (congr_fun heq ()) 0
  simp only [crusoeAlloc2, crusoeAlloc, Matrix.cons_val_zero] at h
  norm_num at h

/-- **The equilibrium allocation `(0,1)` fails the "every good consumed" hypothesis `hcons`** that
`exists_walrasianEquilibriumWithProductionAndTransfers` requires: Good `0` (leisure) is consumed at
level `0`. This is exactly why a *different*, both-goods-positive optimum (`crusoeAlloc2`) is
needed to exercise the production SWT non-trivially. -/
theorem crusoeAlloc_not_hcons : ¬ (∀ l, ∃ a, 0 < crusoeAlloc a l) := by
  intro hcons
  obtain ⟨a, ha⟩ := hcons 0
  have : crusoeAlloc a 0 = 0 := by fin_cases a; norm_num [crusoeAlloc]
  rw [this] at ha
  exact lt_irrefl 0 ha

/-- **Production SWT — consumer support.** A nonnegative nonzero supporting price exists at the
off-equilibrium production optimum. -/
theorem crusoe_consumer_supporting_price :
    ∃ p : Fin 2 → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      ∀ a z, z ∈ nonnegOrthant 2 → (z ≻[crusoe.pref a] crusoeAlloc2 a) →
        p ⬝ᵥ crusoeAlloc2 a ≤ p ⬝ᵥ z :=
  crusoeAlloc2_paretoOptimal.exists_consumer_supporting_price
    (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod (by norm_num)

/-- **Production SWT — quasi-equilibrium at positive wealth.** The supporting price additionally
gives budget-optimality for positive-wealth agents and profit maximization for firms. -/
theorem crusoe_quasiEquilibrium_price :
    ∃ p : Fin 2 → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a z, z ∈ nonnegOrthant 2 → (z ≻[crusoe.pref a] crusoeAlloc2 a) →
        p ⬝ᵥ crusoeAlloc2 a ≤ p ⬝ᵥ z) ∧
      (∀ a, 0 < p ⬝ᵥ crusoeAlloc2 a →
        crusoeAlloc2 a ∈ argmaxRel (crusoe.pref a) (budgetSetAt p (p ⬝ᵥ crusoeAlloc2 a))) ∧
      (∀ j, ∀ z ∈ (crusoe.tech j).Y, p ⬝ᵥ z ≤ p ⬝ᵥ crusoePlan2 j) :=
  crusoeAlloc2_paretoOptimal.exists_quasiEquilibrium_price
    (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod (by norm_num)

/-- Every good is consumed in the off-equilibrium production allocation. -/
theorem crusoe_hcons : ∀ l, ∃ a, 0 < crusoeAlloc2 a l :=
  fun l => ⟨(), by fin_cases l <;> norm_num [crusoeAlloc2]⟩

/-- Consumption-side irreducibility of the relabeled economy holds **vacuously**: `Unit` has no two
nonempty disjoint coalitions. -/
theorem crusoe2_irreducible :
    Irreducible (crusoe.toEconomy.transferEndow (fun a => crusoeAlloc2_paretoOptimal.1.1 a)) := by
  -- The relabeled economy keeps `Agents = Unit`: no two nonempty disjoint coalitions exist.
  haveI : Subsingleton (crusoe.toEconomy.transferEndow
      (fun a => crusoeAlloc2_paretoOptimal.1.1 a)).Agents :=
    inferInstanceAs (Subsingleton Unit)
  refine ⟨fun _ _ _ S T hS hT hdisj => ?_⟩
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  exact absurd (Subsingleton.elim t s ▸ ht) (Finset.disjoint_left.mp hdisj hs)

/-- **Production SWT — decentralization with transfers**, at the welfare optimum `crusoeAlloc2`
that consumes *both* goods (so the "every good consumed" hypothesis `hcons` — which the equilibrium
consumption `(0,1)` fails — holds here). Produces a genuine
`WalrasianEquilibriumWithProductionAndTransfers`.

The library theorem binds the produced object's allocation and plan to `(crusoeAlloc2, crusoePlan2)`
and its transfers to the supported scheme `t a = price ⬝ᵥ crusoeAlloc2 a − wealth price a`.

HONEST SCOPE NOTE: for this linear-utility one-agent Crusoe economy the chosen optimum
`crusoeAlloc2 = (1/2,1/2)` with plan `crusoePlan2 = (-1/2,1/2)` is *itself* a **no-transfer**
Walrasian equilibrium with production (`crusoeEquilibrium2`): wealth `1`, profit `0`, aggregate
excess `0`, so zero transfers suffice. This witness therefore does **not** exhibit *nontrivial*
transfers; it certifies the production SWT at an alternative no-transfer equilibrium satisfying
`hcons`. (Genuinely nonzero transfers are impossible here: with linear utility every both-goods
budget-binding feasible plan is already a no-transfer equilibrium.) The *concrete* zero-transfer
binding is made explicit by `crusoe_second_welfare_binds` below. -/
theorem crusoe_second_welfare :
    ∃ W : WalrasianEquilibriumWithProductionAndTransfers crusoe,
      W.Decentralizes crusoeAlloc2 crusoePlan2 :=
  crusoeAlloc2_paretoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers
    (inferInstanceAs (Nonempty Unit)) crusoe_regular_prod (by norm_num) crusoe_hcons
    crusoe2_irreducible

/-- The explicit decentralization of `crusoeAlloc2` with production and **zero** (balanced)
transfers: it reuses `crusoeEquilibrium2`'s profit-maximization, demand-optimality, and clearing,
with the transfer-adjusted budget `wealth + 0 = wealth` coinciding with the ordinary budget. -/
def crusoeEquilibriumWithTransfers : WalrasianEquilibriumWithProductionAndTransfers crusoe where
  price := crusoePrice
  alloc := crusoeAlloc2
  plan := crusoePlan2
  transfer := fun _ => 0
  price_cone := fun l => by fin_cases l <;> simp [crusoePrice]
  price_ne := ⟨0, by simp [crusoePrice]⟩
  transfers_balance := by simp
  profit_max := fun _ => crusoePlan2_mem_supply
  isOptimal := fun a => by
    -- transfer-adjusted wealth `wealth + 0 = wealth`, so the budget is the ordinary one.
    have hmem := crusoeAlloc2_mem_demand
    rw [ProductionEconomy.consumerDemand, ProductionEconomy.budgetSet] at hmem
    obtain rfl : a = () := rfl
    rw [add_zero]
    exact hmem
  clears := by
    rw [crusoe2_excess_eq_zero]; exact ⟨fun l => by simp, by simp⟩

/-- **Allocation/plan-binding production SWT witness** (the discriminating strengthening of
`crusoe_second_welfare`): there is a Walrasian-equilibrium-with-production-and-transfers whose
allocation is *exactly* `crusoeAlloc2` and whose plan is *exactly* `crusoePlan2`, with balanced
transfers (here zero). This pins the decentralized object to the chosen both-goods optimum, which
the `Nonempty`-only conclusion does not. -/
theorem crusoe_second_welfare_binds :
    ∃ W : WalrasianEquilibriumWithProductionAndTransfers crusoe,
      W.alloc = crusoeAlloc2 ∧ W.plan = crusoePlan2 ∧ W.transfer = fun _ => 0 :=
  ⟨crusoeEquilibriumWithTransfers, rfl, rfl, rfl⟩

end EconlibTest.Equilibrium.Welfare

end
