/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.AgentAggregation
public import Econlib.Equilibrium.Basic
public import Econlib.Math.LinearAlgebra.AggregateFunctional
public import Econlib.Optimization.ComparativeStatics.MonotoneSelection
public import Econlib.Optimization.MaximumTheorem
public import Econlib.Preferences.Geometry.Nonsatiation
public import Econlib.Preferences.Pareto
public import Econlib.Preferences.Representation.Debreu

/-!
# General equilibrium: The preference-carried economy

This file defines the exchange-economy objects used by the general equilibrium module. An `Economy`
has finitely many agents, agent-indexed preferences over commodity bundles, and nonnegative
endowments. Demand is the set of greatest elements of an agent's preference over their budget set,
represented by `Optimization.argmaxRel`.

The budget API is stated first at an abstract wealth level in `budgetSetAt`. It includes convexity,
closedness, compactness at strictly positive prices, homogeneity under common rescaling of prices
and wealth, hemicontinuity lemmas for budget correspondences, budget binding under local
nonsatiation, and revealed-preference cost bounds for weakly or strictly preferred bundles.

The file then gives aggregation-generic notions over `[AgentAggregation Z]`: Aggregate excess
demand, feasibility, Pareto dominance, Pareto optimality, Walras's law, and the abstract
first-welfare statement used by both finite and measure-agent economies. The finite `Economy`
specializes aggregation to the counting sum; `MeasureEconomy` carries its aggregation instance as
data for continuum or stationary-law applications.

The finite economy section also defines `RegularEconomy`, McKenzie irreducibility (`Irreducible`),
market clearing, the core, Walrasian equilibrium, and Walrasian equilibrium with balanced lump-sum
transfers.

## Main definitions

* `budgetSetAt`, `Economy.budgetSet`, `Economy.demand` — wealth-parameterized and endowment-wealth
  budget and demand correspondences.
* `aggregateExcessOver`, `FeasibleOver`, `ParetoDominatesOver`, `ParetoOptimalOver` — the
  aggregation-generic equilibrium layer shared by `Economy` and `MeasureEconomy`.
* `Economy` — the finite preference-carried economy; `MeasureEconomy` — the same primitives with
  aggregation carried as data.
* `RegularEconomy` — the `Prop`-valued regularity bundle for continuous, convex, monotone,
  desirable preferences with nonzero endowments.
* `Irreducible` — McKenzie irreducibility of an economy.
* `Economy.aggregateExcess`, `Economy.MarketClears`, `Economy.Feasible`, `Economy.ParetoOptimal`,
  `Economy.Core`.
* `Economy.WalrasianEquilibrium`, `Economy.WalrasianEquilibriumWithTransfers` — competitive
  equilibrium, with and without lump-sum transfers.
* `Economy.WalrasianEquilibriumWithTransfers.Decentralizes` — the relation "this equilibrium
  implements the given optimum `x` with the supporting balanced transfer scheme"; the conclusion of
  the second welfare theorem (`Econlib.Equilibrium.SecondWelfare`).

## Main statements

* `budgetSetAt_scale`, `Economy.demand_homogeneous` — common rescaling of prices and wealth leaves
  budgets and demand unchanged.
* `budgetSetAt_upperHemicontinuous`, `budgetSetAt_lowerHemicontinuous`, `Economy.demand_nonempty`,
  `Economy.demand_compact` — structural budget and demand properties.
* `budgetSetAt_binds`, `Economy.demand_budget_binds` — local nonsatiation makes demanded bundles
  exhaust the budget.
* `walras_law_over`, `Economy.walras_law` — Walras's law: Budget-binding demand has zero aggregate
  excess value.
* `ParetoOptimalOver.of_preferred_costly`, `Economy.preferred_costly`,
  `Economy.strictlyPreferred_costly` — the cost lemmas underlying the first welfare theorem (the
  packaged theorem `WalrasianEquilibrium.paretoOptimal` lives in `Econlib.Equilibrium.Welfare`).
* `Economy.MarketClears.aggregateExcess_eq_zero` — strictly positive prices turn free-goods
  clearing into exact clearing.
* `Economy.WalrasianEquilibrium.price_pos` — positive wealth forces strictly positive prices.

## Equilibrium convention

The library fixes one Walrasian convention (Debreu 1959), shared by the exchange economy here and
the production economy in `Econlib.Equilibrium.Production`:

* **Prices** are nonnegative (`WalrasianEquilibrium.price_cone`) and not all zero
  (`WalrasianEquilibrium.price_ne`). Nonnegativity plus one strictly positive coordinate is the
  cone normalization; it rules out the degenerate `p = 0`, at which every allocation clears
  vacuously.
* **Market clearing** is the free-disposal (free-goods) form `MarketClears`: Aggregate excess
  demand is nonpositive in every good, and its value at `p` is zero (`p ⬝ᵥ excess = 0`). This is
  weak Walras' law with disposal of goods in excess supply. At strictly positive prices it
  collapses to exact clearing in every good (`MarketClears.aggregateExcess_eq_zero`); a good
  carried in strict excess supply must have price zero (complementary slackness). With positive
  wealth the prices are in turn forced strictly positive (`WalrasianEquilibrium.price_pos`), so for
  an interior economy the free-disposal form and exact-clearing form coincide.
* **Existence** (`Economy.exists_equilibrium`) is stated under explicit regularity: A
  `RegularEconomy` (continuous, convex, monotone, desirable preferences with nonzero endowments),
  McKenzie irreducibility (`Irreducible`), and the ownership condition that every good is owned by
  some agent. These are the Arrow–Debreu / McKenzie hypotheses; strict concavity and single-valued
  demand are not assumed.

## References

* Debreu, Gérard. 1959. *Theory of Value: An Axiomatic Analysis of Economic Equilibrium*. Wiley.
* McKenzie, Lionel W. 1959. “On the Existence of General Equilibrium for a Competitive Market.”
  *Econometrica* 27 (1): 54. [https://doi.org/10.2307/1907777](https://doi.org/10.2307/1907777).

## Tags

general equilibrium, walrasian equilibrium, competitive equilibrium, walras's law, pareto optimal
-/

@[expose] public section

open Finset BigOperators Matrix Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

/-! ## Wealth-parameterized budget set

Defining the budget set against an abstract wealth level `w` (rather than `p ⬝ᵥ endowment`)
lets the exchange economy (`w := p ⬝ᵥ endow a`) and the production economy
(`w := p ⬝ᵥ endow a + dividends`) share one object and its convexity lemma. -/

/-- Nonnegative bundles affordable at wealth `w` and prices `p`. -/
def budgetSetAt (p : Fin L → ℝ) (w : ℝ) : Set (Fin L → ℝ) :=
  {x ∈ nonnegOrthant L | p ⬝ᵥ x ≤ w}

/-- Membership in `budgetSetAt`. -/
@[simp] lemma mem_budgetSetAt {p x : Fin L → ℝ} {w : ℝ} :
    x ∈ budgetSetAt p w ↔ (∀ l, 0 ≤ x l) ∧ p ⬝ᵥ x ≤ w := Iff.rfl

/-- The wealth-parameterized budget set is convex. -/
lemma budgetSetAt_convex (p : Fin L → ℝ) (w : ℝ) : Convex ℝ (budgetSetAt p w) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxpos, hxw⟩ := hx
  obtain ⟨hypos, hyw⟩ := hy
  refine ⟨fun l => ?_, ?_⟩
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha (hxpos l)) (mul_nonneg hb (hypos l))
  · calc p ⬝ᵥ (a • x + b • y)
        = a * (p ⬝ᵥ x) + b * (p ⬝ᵥ y) := by
          rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      _ ≤ a * w + b * w := by gcongr
      _ = w := by rw [← add_mul, hab, one_mul]

/-- **Scaling prices and wealth by the same positive factor leaves the budget set unchanged.** -/
lemma budgetSetAt_scale {t : ℝ} (ht : 0 < t) (p : Fin L → ℝ) (w : ℝ) :
    budgetSetAt (t • p) (t * w) = budgetSetAt p w := by
  ext x
  simp only [mem_budgetSetAt, smul_dotProduct, smul_eq_mul]
  constructor
  · rintro ⟨hnn, hbud⟩
    exact ⟨hnn, le_of_mul_le_mul_left hbud ht⟩
  · rintro ⟨hnn, hbud⟩
    exact ⟨hnn, mul_le_mul_of_nonneg_left hbud ht.le⟩

/-- The wealth-parameterized budget set is closed. -/
lemma budgetSetAt_closed (p : Fin L → ℝ) (w : ℝ) : IsClosed (budgetSetAt p w) := by
  have h_halfspace_closed : IsClosed {x : Fin L → ℝ | p ⬝ᵥ x ≤ w} :=
    isClosed_le (by fun_prop) continuous_const
  have heq : budgetSetAt p w = nonnegOrthant L ∩ {x | p ⬝ᵥ x ≤ w} := by
    ext x; simp [budgetSetAt, nonnegOrthant, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [heq]; exact nonnegOrthant_closed.inter h_halfspace_closed

/-- With strictly positive prices, each coordinate of an affordable bundle is bounded above. -/
lemma budgetSetAt_coord_bound {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ}
    (x : Fin L → ℝ) (hx : x ∈ budgetSetAt p w) (l : Fin L) : x l ≤ w / p l := by
  have h_single_le : p l * x l ≤ p ⬝ᵥ x :=
    Finset.single_le_sum (fun l' _ => mul_nonneg (hp l').le (hx.1 l')) (Finset.mem_univ l)
  rw [le_div_iff₀ (hp l)]
  linarith [hx.2]

/-- With strictly positive prices, the budget set sits inside a product of closed intervals. -/
lemma budgetSetAt_subset_Icc {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) (w : ℝ) :
    budgetSetAt p w ⊆ Set.pi Set.univ (fun l => Set.Icc 0 (w / p l)) :=
  fun _ hx l _ => ⟨hx.1 l, budgetSetAt_coord_bound hp _ hx l⟩

/-- The budget set is compact when all prices are strictly positive. -/
lemma isCompact_budgetSetAt_of_pos_prices {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) (w : ℝ) :
    IsCompact (budgetSetAt p w) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
    (budgetSetAt_closed p w) (budgetSetAt_subset_Icc hp w)

/-! ## Budget-correspondence hemicontinuity

Upper and lower hemicontinuity of `p ↦ budgetSetAt p (w p)` for a continuous wealth function
`w`. These are the constraint-correspondence inputs to Berge's maximum theorem. Stated generically
in `w` so both the exchange economy (`w p := p ⬝ᵥ endow a`) and the production economy (wealth
augmented with profits) specialize them. -/

/-- If `‖u‖ ≤ R < ‖v‖`, the segment from `u` to `v` passes through the sphere of radius `R`. -/
lemma segment_crosses_sphere {u v : Fin L → ℝ} {R : ℝ}
    (hu : ‖u‖ ≤ R) (hv : R < ‖v‖) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ ‖(1 - t) • u + t • v‖ = R := by
  set f : ℝ → ℝ := fun t => ‖(1 - t) • u + t • v‖
  have hf_cont : Continuous f :=
    (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)).norm
  have hf0 : f 0 = ‖u‖ := by simp [f]
  have hf1 : f 1 = ‖v‖ := by simp [f]
  have hR_mem : R ∈ Set.uIcc (f 0) (f 1) := by
    rw [hf0, hf1, Set.mem_uIcc]; left; exact ⟨hu, le_of_lt hv⟩
  obtain ⟨t, ht, htR⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := 1)
    hf_cont.continuousOn hR_mem
  rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 1)] at ht
  exact ⟨t, ht, htR⟩

/-- The graph `{(p, x) | x ∈ budgetSetAt p (w p)}` is closed in the product topology, for any
continuous wealth function `w`. -/
lemma isClosed_budgetSetAt_graph (w : (Fin L → ℝ) → ℝ) (hw : Continuous w) :
    IsClosed {px : (Fin L → ℝ) × (Fin L → ℝ) | px.2 ∈ budgetSetAt px.1 (w px.1)} := by
  have h_orth : IsClosed {px : (Fin L → ℝ) × (Fin L → ℝ) | ∀ l, 0 ≤ px.2 l} := by
    simp_rw [Set.setOf_forall]
    exact isClosed_iInter fun l =>
      isClosed_le continuous_const ((continuous_apply l).comp continuous_snd)
  have h_ineq : IsClosed
      {px : (Fin L → ℝ) × (Fin L → ℝ) | px.1 ⬝ᵥ px.2 ≤ w px.1} :=
    isClosed_le
      (continuous_finset_sum _ fun l _ =>
        ((continuous_apply l).comp continuous_fst).mul
          ((continuous_apply l).comp continuous_snd))
      (hw.comp continuous_fst)
  have h_eq : {px : (Fin L → ℝ) × (Fin L → ℝ) | px.2 ∈ budgetSetAt px.1 (w px.1)} =
      {px : (Fin L → ℝ) × (Fin L → ℝ) | ∀ l, 0 ≤ px.2 l} ∩
      {px : (Fin L → ℝ) × (Fin L → ℝ) | px.1 ⬝ᵥ px.2 ≤ w px.1} := by
    ext ⟨p, x⟩; simp [budgetSetAt, nonnegOrthant]
  rw [h_eq]; exact h_orth.inter h_ineq

/-- **The budget correspondence is upper hemicontinuous** wherever its values are compact. -/
theorem budgetSetAt_upperHemicontinuous (w : (Fin L → ℝ) → ℝ) (hw : Continuous w)
    (x₀ : Fin L → ℝ) (hx₀ : ∀ p, x₀ ∈ budgetSetAt p (w p))
    (hK : ∀ p, IsCompact (budgetSetAt p (w p))) :
    UpperHemicontinuous (fun p : Fin L → ℝ => budgetSetAt p (w p)) := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  intro p₀ U hU hBU
  obtain ⟨R, hR_pos, hK₀R⟩ :
      ∃ R : ℝ, 0 < R ∧ budgetSetAt p₀ (w p₀) ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := (hK p₀).isBounded.subset_closedBall 0
    exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right R 1),
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))⟩
  have he_R : ‖x₀‖ ≤ R := by
    have h := hK₀R (hx₀ p₀)
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hΓcl : IsClosed
      {px : (Fin L → ℝ) × (Fin L → ℝ) | px.2 ∈ budgetSetAt px.1 (w px.1)} :=
    isClosed_budgetSetAt_graph w hw
  have h_sphere_sub : {p₀} ×ˢ Metric.sphere (0 : Fin L → ℝ) (R + 1) ⊆
      {px : (Fin L → ℝ) × (Fin L → ℝ) | px.2 ∈ budgetSetAt px.1 (w px.1)}ᶜ := by
    intro ⟨q, x⟩ ⟨hq, hx⟩
    simp only [Set.mem_singleton_iff] at hq
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]; rw [hq]
    intro hmem
    have h_le : ‖x‖ ≤ R := by
      have := hK₀R hmem; rwa [Metric.mem_closedBall, dist_zero_right] at this
    have h_eq : ‖x‖ = R + 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hx
    linarith
  obtain ⟨N₂, W₂, hN₂_open, _, hp₀N₂, hSW₂, hNW₂⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere 0 (R + 1))
      hΓcl.isOpen_compl h_sphere_sub
  -- For `p ∈ N₂`, the budget set stays in `closedBall(0, R+1)`: any point past the sphere would
  -- produce a convex combination with `x₀` that crosses the sphere, contradicting `h_sphere_sub`.
  have h_bound : ∀ p ∈ N₂, budgetSetAt p (w p) ⊆ Metric.closedBall 0 (R + 1) := by
    intro p hp x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h_big; push Not at h_big
    obtain ⟨t, ht, ht_norm⟩ := segment_crosses_sphere (by linarith : ‖x₀‖ ≤ R + 1) h_big
    have hy_bset : (1 - t) • x₀ + t • x ∈ budgetSetAt p (w p) :=
      budgetSetAt_convex p (w p) (hx₀ p) hx
        (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    have hy_sphere : (1 - t) • x₀ + t • x ∈ Metric.sphere (0 : Fin L → ℝ) (R + 1) := by
      rw [Metric.mem_sphere, dist_zero_right]; exact ht_norm
    exact hNW₂ (Set.mk_mem_prod hp (hSW₂ hy_sphere)) hy_bset
  have h_ball_sub : {p₀} ×ˢ Metric.closedBall (0 : Fin L → ℝ) (R + 1) ⊆
      (Set.univ ×ˢ U) ∪
      {px : (Fin L → ℝ) × (Fin L → ℝ) | px.2 ∈ budgetSetAt px.1 (w px.1)}ᶜ := by
    intro ⟨q, x⟩ ⟨hq, hx⟩
    simp only [Set.mem_singleton_iff] at hq
    by_cases hmem : x ∈ budgetSetAt p₀ (w p₀)
    · exact Or.inl ⟨Set.mem_univ _, hBU hmem⟩
    · right; simp only [Set.mem_compl_iff, Set.mem_setOf_eq]; rwa [hq]
  obtain ⟨N₁, W₁, hN₁_open, _, hp₀N₁, hBW₁, hNW₁⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_closedBall 0 (R + 1))
      ((isOpen_univ.prod hU).union hΓcl.isOpen_compl) h_ball_sub
  filter_upwards [hN₁_open.mem_nhds (hp₀N₁ (Set.mem_singleton _)),
      hN₂_open.mem_nhds (hp₀N₂ (Set.mem_singleton _))] with p hp₁ hp₂ x hx
  rcases hNW₁ (Set.mk_mem_prod hp₁ (hBW₁ (h_bound p hp₂ hx))) with ⟨_, hxU⟩ | hxΓc
  · exact hxU
  · exact absurd hx hxΓc

/-- **The budget correspondence is lower hemicontinuous at `p₀`** when a **cheaper point** exists:
Some nonnegative `z` with `p₀ ⬝ᵥ z < w p₀` (the `IsParametricSlater` / survival witness). -/
theorem budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint (w : (Fin L → ℝ) → ℝ)
    (hw : Continuous w) {p₀ : Fin L → ℝ} (hz : ∃ z ∈ nonnegOrthant L, p₀ ⬝ᵥ z < w p₀) :
    LowerHemicontinuousAt (fun p : Fin L → ℝ => budgetSetAt p (w p)) p₀ := by
  rw [lowerHemicontinuousAt_iff]
  intro U hU ⟨x, hx_mem, hx_U⟩
  obtain ⟨z, hz_orth, hz_cheap⟩ := hz
  have hx_orth : x ∈ nonnegOrthant L := hx_mem.1
  have hx_bud : p₀ ⬝ᵥ x ≤ w p₀ := hx_mem.2
  have h_cont_dot : ∀ v : Fin L → ℝ, Continuous (fun p : Fin L → ℝ => p ⬝ᵥ v) :=
    fun _ => continuous_id.dotProduct continuous_const
  have h_cont_gap : Continuous (fun p : Fin L → ℝ => p ⬝ᵥ x - w p) :=
    (h_cont_dot x).sub hw
  by_cases h_strict : p₀ ⬝ᵥ x < w p₀
  · have h_neg : p₀ ⬝ᵥ x - w p₀ < 0 := sub_neg.mpr h_strict
    have h_open : IsOpen {p | p ⬝ᵥ x - w p < 0} := isOpen_lt h_cont_gap continuous_const
    filter_upwards [h_open.mem_nhds (show p₀ ∈ _ from h_neg)] with p hp
    exact ⟨x, ⟨hx_orth, le_of_lt (sub_neg.mp hp)⟩, hx_U⟩
  · -- Boundary case: `p₀ ⬝ᵥ x = w p₀`. Nudge `x` toward the cheaper point `z`.
    push Not at h_strict
    have h_eq : p₀ ⬝ᵥ x = w p₀ := le_antisymm hx_bud h_strict
    rw [Metric.isOpen_iff] at hU
    obtain ⟨ε, hε_pos, hε_ball⟩ := hU x hx_U
    by_cases hzx : z = x
    · rw [hzx, h_eq] at hz_cheap
      exact absurd hz_cheap (lt_irrefl _)
    · have hdist_pos : 0 < dist z x := dist_pos.mpr hzx
      set δ := min (1 / 2) (ε / (2 * dist z x)) with hδ_def
      have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
      have hδ_lt_one : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have h1mδ_pos : 0 < 1 - δ := by linarith
      set y := (1 - δ) • x + δ • z with hy_def
      have hy_orth : y ∈ nonnegOrthant L := by
        intro l
        simp only [hy_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg (le_of_lt h1mδ_pos) (hx_orth l))
          (mul_nonneg (le_of_lt hδ_pos) (hz_orth l))
      have hdot_y : p₀ ⬝ᵥ y = (1 - δ) * (w p₀) + δ * (p₀ ⬝ᵥ z) := by
        rw [hy_def, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
          smul_eq_mul, h_eq]
      have hy_cheap : p₀ ⬝ᵥ y < w p₀ := by
        have h_δz_lt : δ * (p₀ ⬝ᵥ z) < δ * (w p₀) := mul_lt_mul_of_pos_left hz_cheap hδ_pos
        have h_sum_one : (1 - δ) * (w p₀) + δ * (w p₀) = w p₀ := by ring
        linarith
      have hy_dist : dist y x < ε := by
        have hyz : y - x = δ • (z - x) := by
          ext l
          simp only [hy_def, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [dist_eq_norm, hyz, norm_smul, Real.norm_of_nonneg (le_of_lt hδ_pos), ← dist_eq_norm]
        calc δ * dist z x
            ≤ (ε / (2 * dist z x)) * dist z x := by gcongr; exact min_le_right _ _
          _ = ε / 2 := by field_simp
          _ < ε := by linarith
      have hy_U : y ∈ U := hε_ball (Metric.mem_ball.mpr hy_dist)
      have h_cont_gap_y : Continuous (fun p : Fin L → ℝ => p ⬝ᵥ y - w p) :=
        (h_cont_dot y).sub hw
      have h_open_y : IsOpen {p | p ⬝ᵥ y - w p < 0} :=
        isOpen_lt h_cont_gap_y continuous_const
      filter_upwards [h_open_y.mem_nhds (show p₀ ∈ _ from sub_neg.mpr hy_cheap)] with p hp
      exact ⟨y, ⟨hy_orth, le_of_lt (sub_neg.mp hp)⟩, hy_U⟩

/-- **The budget correspondence is lower hemicontinuous** when a cheaper point exists at every
price (global Slater / survival condition). -/
theorem budgetSetAt_lowerHemicontinuous (w : (Fin L → ℝ) → ℝ) (hw : Continuous w)
    (hcheap : ∀ p, ∃ z ∈ nonnegOrthant L, p ⬝ᵥ z < w p) :
    LowerHemicontinuous (fun p : Fin L → ℝ => budgetSetAt p (w p)) :=
  fun p => budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint w hw (hcheap p)

/-- Under local nonsatiation, a bundle maximizing a preference over `budgetSetAt p w` satisfies
`p ⬝ᵥ x = w`. -/
theorem budgetSetAt_binds {pref : PreferenceRel (Fin L → ℝ)}
    (hlns : Econlib.Preferences.LocallyNonsatiated (nonnegOrthant L) pref)
    {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ}
    (hx : x ∈ Optimization.argmaxRel pref (budgetSetAt p w)) :
    p ⬝ᵥ x = w := by
  obtain ⟨hxbud, hxmax⟩ := hx
  refine le_antisymm hxbud.2 ?_
  by_contra hlt
  push Not at hlt
  have hcont : Continuous fun y : Fin L → ℝ => p ⬝ᵥ y :=
    continuous_const.dotProduct continuous_id
  have hUopen : IsOpen {y : Fin L → ℝ | p ⬝ᵥ y < w} := isOpen_lt hcont continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUopen x hlt
  obtain ⟨y, hyC, hyclose, hybetter⟩ := hlns.exists_better_nearby x hxbud.1 ε hε
  have hyaff : p ⬝ᵥ y < w := hball (by rwa [Metric.mem_ball, dist_eq_norm])
  have hybud : y ∈ budgetSetAt p w := ⟨hyC, le_of_lt hyaff⟩
  exact hybetter.2 (hxmax y hybud)

/-- If `x` maximizes over `budgetSetAt p w` and a feasible `z` is strictly preferred, then
`w < p ⬝ᵥ z`. -/
theorem budgetSetAt_strictlyPreferred_costly {pref : PreferenceRel (Fin L → ℝ)} {p : Fin L → ℝ}
    {w : ℝ} {x z : Fin L → ℝ} (hx : x ∈ Optimization.argmaxRel pref (budgetSetAt p w))
    (hz : z ∈ nonnegOrthant L) (hlt : z ≻[pref] x) : w < p ⬝ᵥ z := by
  obtain ⟨_, hxmax⟩ := hx
  by_contra hle
  push Not at hle
  exact hlt.2 (hxmax z ⟨hz, hle⟩)

/-- Under local nonsatiation, if `x` maximizes over `budgetSetAt p w` and a feasible `z` is weakly
preferred, then `w ≤ p ⬝ᵥ z`. -/
theorem budgetSetAt_preferred_costly {pref : PreferenceRel (Fin L → ℝ)}
    (hlns : Econlib.Preferences.LocallyNonsatiated (nonnegOrthant L) pref)
    {p : Fin L → ℝ} {w : ℝ} {x z : Fin L → ℝ}
    (hx : x ∈ Optimization.argmaxRel pref (budgetSetAt p w))
    (hz : z ∈ nonnegOrthant L) (hle : z ≽[pref] x) : w ≤ p ⬝ᵥ z := by
  obtain ⟨_, hxmax⟩ := hx
  by_contra hlt
  push Not at hlt
  have hcont : Continuous fun y : Fin L → ℝ => p ⬝ᵥ y :=
    continuous_const.dotProduct continuous_id
  have hUopen : IsOpen {y : Fin L → ℝ | p ⬝ᵥ y < w} := isOpen_lt hcont continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUopen z hlt
  obtain ⟨z', hz'C, hz'close, hz'better⟩ := hlns.exists_better_nearby z hz ε hε
  have hz'aff : p ⬝ᵥ z' < w := hball (by rwa [Metric.mem_ball, dist_eq_norm])
  exact (pref.lt_of_lt_of_le hz'better hle).2 (hxmax z' ⟨hz'C, le_of_lt hz'aff⟩)

/-! ## Aggregation-generic equilibrium notions

Walras's law and the first welfare theorem are stated once over an abstract
`[AgentAggregation Z]`. The finite `Economy` instantiates this with its `Fintype` counting sum; a
continuum `MeasureEconomy` reuses the same proofs via its integration instance. -/

section Aggregation

variable {Z : Type*} [inst : AgentAggregation Z]

/-- Aggregate excess demand over an abstract agent aggregation. -/
noncomputable def aggregateExcessOver (endow x : Z → (Fin L → ℝ)) : Fin L → ℝ :=
  fun l => AgentAggregation.agg Z (fun a => x a l) - AgentAggregation.agg Z (fun a => endow a l)

/-- A **feasible allocation** (abstract): Nonnegative bundles whose aggregate consumption does not
exceed aggregate endowment in any good. -/
def FeasibleOver (endow x : Z → (Fin L → ℝ)) : Prop :=
  (∀ a l, 0 ≤ x a l) ∧ ∀ l, aggregateExcessOver endow x l ≤ 0

/-- Allocation `x` **Pareto dominates** `y` (aggregation-free). -/
def ParetoDominatesOver (pref : Z → PreferenceRel (Fin L → ℝ)) (x y : Z → (Fin L → ℝ)) : Prop :=
  Econlib.Preferences.ParetoDominates pref x y

/-- A feasible allocation is **Pareto optimal** (abstract): No feasible allocation dominates it. -/
def ParetoOptimalOver (endow : Z → (Fin L → ℝ)) (pref : Z → PreferenceRel (Fin L → ℝ))
    (x : Z → (Fin L → ℝ)) : Prop :=
  FeasibleOver endow x ∧ ¬ ∃ y, FeasibleOver endow y ∧ ParetoDominatesOver pref y x

/-- `p ⬝ᵥ aggregateExcessOver endow x = agg (a ↦ p ⬝ᵥ x a - p ⬝ᵥ endow a)`. -/
lemma dotProduct_aggregateExcessOver (p : Fin L → ℝ) (endow x : Z → (Fin L → ℝ)) :
    p ⬝ᵥ aggregateExcessOver endow x
      = AgentAggregation.agg Z (fun a => p ⬝ᵥ (x a) - p ⬝ᵥ endow a) := by
  have hpt : ∀ a, p ⬝ᵥ (x a) - p ⬝ᵥ endow a = ∑ l, p l * (x a l - endow a l) := fun a => by
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
  simp only [AgentAggregation.agg]
  rw [inst.toPLF.aggregate_congr hpt,
    inst.toPLF.aggregate_finset_sum Finset.univ (fun l a => p l * (x a l - endow a l))]
  simp only [dotProduct, aggregateExcessOver, AgentAggregation.agg]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← inst.toPLF.aggregate_sub, ← inst.toPLF.aggregate_smul]

/-- **Walras's law (abstract).** If every agent's budget binds, the value of aggregate excess
demand is zero. -/
theorem walras_law_over {p : Fin L → ℝ} {endow x : Z → (Fin L → ℝ)}
    (hbind : ∀ a, p ⬝ᵥ (x a) = p ⬝ᵥ endow a) :
    p ⬝ᵥ aggregateExcessOver endow x = 0 := by
  rw [dotProduct_aggregateExcessOver]
  have hzero : (fun a => p ⬝ᵥ (x a) - p ⬝ᵥ endow a) = fun _ : Z => (0 : ℝ) := by
    funext a; rw [hbind a, sub_self]
  rw [hzero]; exact inst.toPLF.aggregate_zero

/-- **First welfare theorem (abstract).** Over a faithful aggregation, a nonnegative
market-clearing allocation satisfying the revealed-preference cost bounds `hweak`/`hstrict` is
Pareto optimal. -/
theorem ParetoOptimalOver.of_preferred_costly [FaithfulAggregation Z]
    {pref : Z → PreferenceRel (Fin L → ℝ)} {endow alloc : Z → (Fin L → ℝ)} {price : Fin L → ℝ}
    (hprice_nn : ∀ l, 0 ≤ price l) (halloc_nn : ∀ a l, 0 ≤ alloc a l)
    (hclears_le : ∀ l, aggregateExcessOver endow alloc l ≤ 0)
    (hweak : ∀ (a : Z) (z : Fin L → ℝ), z ∈ nonnegOrthant L → (z ≽[pref a] alloc a) →
      price ⬝ᵥ endow a ≤ price ⬝ᵥ z)
    (hstrict : ∀ (a : Z) (z : Fin L → ℝ), z ∈ nonnegOrthant L → (z ≻[pref a] alloc a) →
      price ⬝ᵥ endow a < price ⬝ᵥ z) :
    ParetoOptimalOver endow pref alloc := by
  refine ⟨⟨halloc_nn, hclears_le⟩, ?_⟩
  rintro ⟨y, hyfeas, hyle, a₀, hya₀⟩
  have hg_nonneg : ∀ a, 0 ≤ price ⬝ᵥ (y a) - price ⬝ᵥ endow a := fun a => by
    have := hweak a (y a) (hyfeas.1 a) (hyle a); linarith
  have hg_pos : 0 < price ⬝ᵥ (y a₀) - price ⬝ᵥ endow a₀ := by
    have := hstrict a₀ (y a₀) (hyfeas.1 a₀) hya₀; linarith
  have hagg_le : AgentAggregation.agg Z (fun a => price ⬝ᵥ (y a) - price ⬝ᵥ endow a) ≤ 0 := by
    rw [← dotProduct_aggregateExcessOver]
    simp only [dotProduct]
    exact Finset.sum_nonpos fun l _ =>
      mul_nonpos_of_nonneg_of_nonpos (hprice_nn l) (hyfeas.2 l)
  have hagg_zero : AgentAggregation.agg Z (fun a => price ⬝ᵥ (y a) - price ⬝ᵥ endow a) = 0 :=
    le_antisymm hagg_le (inst.toPLF.aggregate_nonneg _ hg_nonneg)
  -- Faithfulness forces the strict gainer's net spending to zero, contradicting `hg_pos`.
  have hzero := FaithfulAggregation.faithful (Z := Z) _ hg_nonneg hagg_zero a₀
  linarith

end Aggregation

/-! ## The economy -/

/-- A **preference-carried finite economy**. Aggregation is the counting sum `∑`; `pref` and
`endow` are the agent-indexed primitives. -/
structure Economy (L : ℕ) where
  /-- The agent space. -/
  Agents : Type*
  /-- Agents are finite — aggregation is the counting `∑`. -/
  [agentsFin : Fintype Agents]
  /-- Each agent's preference over commodity bundles. -/
  pref : Agents → PreferenceRel (Fin L → ℝ)
  /-- Each agent's endowment. -/
  endow : Agents → (Fin L → ℝ)
  /-- Endowments are nonnegative. -/
  endow_mem : ∀ a, endow a ∈ nonnegOrthant L

attribute [instance] Economy.agentsFin

/-- The `Prop`-valued regularity bundle for the convex existence case: Continuity (closed weak
contour sets), convexity, strict monotonicity toward the interior, desirability (the free-good
exclusion behind positive prices), and nonzero endowments. -/
structure RegularEconomy (E : Economy L) : Prop where
  /-- Each agent's preference is continuous (closed weak upper/lower contour sets). -/
  contPref : ∀ a, Econlib.Preferences.ContinuousPref (E.pref a)
  /-- Preferences are convex (not necessarily strict; see the strict corollary). -/
  convex : ∀ a, ConvexPreference (E.pref a)
  /-- Preferences are strictly monotone toward interior bundles. Weaker than global strong
  monotonicity (admits Cobb–Douglas / CES); `StrictMonotonePreference` implies it via
  `StrictMonotonePreference.toStrictMonoToInterior`. -/
  mono : ∀ a, StrictMonoToInterior (E.pref a)
  /-- **No free goods.** Each agent's preference is `Desirable`: Monotone improvement at any bundle
  weakly preferred to an interior bundle. This drives the free-good exclusion behind positive
  equilibrium prices. Strong monotonicity (e.g. linear preferences) furnishes it via
  `StrictMonotonePreference.toDesirable`; boundary-flat preferences (Cobb–Douglas / CES) via
  `BoundaryAvoiding.toDesirable`. -/
  desirable : ∀ a, Desirable (E.pref a)
  /-- Every agent owns a nonzero endowment. Required for budget lower-hemicontinuity: At strictly
  positive prices, `z = 0` is a cheaper point iff `endow a ≠ 0`. Weaker than `e ≫ 0`. -/
  endow_ne : ∀ a, E.endow a ≠ 0

/-- **McKenzie irreducibility** (McKenzie 1959). For every individually-rational allocation `x` and
every split into a nonempty improving coalition `S` and nonempty donor coalition `T`, the donors'
endowments augment `S`'s resources enough to make every member of `S` strictly better off:
`∑_{i∈S} y i ≤ ∑_{i∈S} x i + ∑_{j∈T} e j` in every good.

Drives the quasi→Walrasian upgrade: Take `S` to be strictly-positive-wealth agents and `T` the
zero-wealth agents; improved `S`-bundles cost strictly more than `S`'s wealth, while the resource
inequality bounds it — a contradiction. Strictly positive endowments imply it
(`Irreducible.of_pos_endow`); labor economies with boundary endowments also qualify. -/
structure Irreducible (E : Economy L) : Prop where
  improve : ∀ x : E.Agents → (Fin L → ℝ), (∀ i l, 0 ≤ x i l) →
    (∀ i, x i ≽[E.pref i] E.endow i) →
    ∀ S T : Finset E.Agents, S.Nonempty → T.Nonempty → Disjoint S T →
      ∃ y : E.Agents → (Fin L → ℝ),
        (∀ i ∈ S, (∀ l, 0 ≤ y i l) ∧ y i ≻[E.pref i] x i) ∧
        (∀ l, ∑ i ∈ S, y i l ≤ ∑ i ∈ S, x i l + ∑ j ∈ T, E.endow j l)

/-- Local nonsatiation follows from `mono` in a regular economy. -/
lemma RegularEconomy.locallyNonsatiated {E : Economy L} (hreg : RegularEconomy E) (a : E.Agents) :
    Econlib.Preferences.LocallyNonsatiated (nonnegOrthant L) (E.pref a) := by
  haveI : Nonempty (Fin L) := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    exact hreg.endow_ne a (funext fun l => (hemp.false l).elim)
  exact locallyNonsatiated_nonnegOrthant_of_strictMonoToInterior (hreg.mono a)

/-- Strictly positive endowments imply McKenzie irreducibility when preferences are
`StrictMonoToInterior`. -/
lemma Irreducible.of_pos_endow (E : Economy L) (hL : 0 < L) (hpos : ∀ a l, 0 < E.endow a l)
    (hmono : ∀ a, StrictMonoToInterior (E.pref a)) : Irreducible E := by
  classical
  refine ⟨fun x hx_nn _hIR S T hS hT _hdisj => ?_⟩
  set r : Fin L → ℝ := fun l => ∑ j ∈ T, E.endow j l with hr_def
  have hScard_pos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hr_pos : ∀ l, 0 < r l := by
    intro l
    obtain ⟨j₀, hj₀⟩ := hT
    exact Finset.sum_pos' (fun j _ => (hpos j l).le) ⟨j₀, hj₀, hpos j₀ l⟩
  have hbump_pos : ∀ l, 0 < r l / (S.card : ℝ) := fun l => div_pos (hr_pos l) hScard_pos
  refine ⟨fun i l => x i l + r l / (S.card : ℝ), fun i _hi => ⟨fun l => ?_, ?_⟩, fun l => ?_⟩
  · linarith [hx_nn i l, hbump_pos l]
  · set y : Fin L → ℝ := fun l => x i l + r l / (S.card : ℝ) with hy_def
    have hle : x i ≤ y := fun l => by simp only [hy_def]; linarith [hbump_pos l]
    have hypos : ∀ l, 0 < y l := fun l => by simp only [hy_def]; linarith [hx_nn i l, hbump_pos l]
    have hne : x i ≠ y := by
      intro heq
      have := congr_fun heq ⟨0, hL⟩
      simp only [hy_def] at this
      linarith [hbump_pos ⟨0, hL⟩]
    exact (hmono i).strictMono hle hne hypos
  · have hsum : ∑ i ∈ S, (x i l + r l / (S.card : ℝ)) =
        (∑ i ∈ S, x i l) + r l := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have : (S.card : ℝ) * (r l / (S.card : ℝ)) = r l := by
        field_simp
      rw [this]
    rw [hsum, hr_def]

/-- **Irreducibility at singleton coalitions.** Instantiates `Irreducible.improve` at the singleton
improving coalition `S = {i}` and singleton donor coalition `T = {j}` for two distinct agents, with
the three `Finset.sum_singleton`s pre-discharged. The donor's whole endowment augments `i`'s
resources, so the improved bundle `y i` satisfies `y i l ≤ x i l + E.endow j l` per good while
strictly bettering `i`. This is the two-agent form behind every "irreducibility fails" witness in a
finite economy, sparing consumers the opaque-`E.Agents` `Finset.sum_singleton` plumbing. -/
lemma Irreducible.improve_singletons (h : Irreducible E)
    (x : E.Agents → (Fin L → ℝ)) (hx_nn : ∀ i l, 0 ≤ x i l)
    (hIR : ∀ i, x i ≽[E.pref i] E.endow i) (i j : E.Agents) (hij : i ≠ j) :
    ∃ y : E.Agents → (Fin L → ℝ),
      ((∀ l, 0 ≤ y i l) ∧ y i ≻[E.pref i] x i) ∧
      (∀ l, y i l ≤ x i l + E.endow j l) := by
  obtain ⟨y, hy_imp, hy_res⟩ :=
    h.improve x hx_nn hIR {i} {j}
      (Finset.singleton_nonempty _) (Finset.singleton_nonempty _)
      (Finset.disjoint_singleton.mpr hij)
  refine ⟨y, hy_imp i (Finset.mem_singleton_self _), fun l => ?_⟩
  have := hy_res l
  rwa [Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton] at this

namespace Economy

variable (E : Economy L)

/-- Agent `a`'s budget set at prices `p`: Nonnegative bundles affordable at endowment wealth. -/
def budgetSet (p : Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  budgetSetAt p (p ⬝ᵥ E.endow a)

/-- The **demand correspondence** is the greatest-element set of the preference over the budget set
(`Optimization.argmaxRel`). -/
noncomputable def demand (p : Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  Optimization.argmaxRel (E.pref a) (E.budgetSet p a)

/-- Aggregate excess demand: Total consumption minus total endowment, coordinatewise. Aggregation
for a finite economy is the counting sum `∑ a`. -/
noncomputable def aggregateExcess (x : E.Agents → (Fin L → ℝ)) : Fin L → ℝ :=
  fun l => (∑ a, x a l) - (∑ a, E.endow a l)

/-- **Market clearing, free-goods form**: Weak excess supply everywhere, with equality on priced
goods (`p ⬝ᵥ excess = 0`). -/
structure MarketClears (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)) : Prop where
  /-- Aggregate excess demand is nonpositive in every good (free disposal). -/
  excess_nonpos : ∀ l, E.aggregateExcess x l ≤ 0
  /-- The value of aggregate excess demand at prices `p` is zero. -/
  value_zero : p ⬝ᵥ (E.aggregateExcess x) = 0

variable {E} in
/-- **At strictly positive prices, free-goods clearing is exact**: Weak excess supply plus zero
excess value force zero excess demand in every good. -/
lemma MarketClears.aggregateExcess_eq_zero {p : Fin L → ℝ} {x : E.Agents → (Fin L → ℝ)}
    (hclear : E.MarketClears p x) (hp : ∀ l, 0 < p l) : E.aggregateExcess x = 0 := by
  funext l
  change E.aggregateExcess x l = 0
  -- Each value term `p k * excess k` is nonpositive and they sum to zero, so each vanishes.
  have hterm_nonpos : ∀ k ∈ Finset.univ, p k * E.aggregateExcess x k ≤ 0 :=
    fun k _ => mul_nonpos_of_nonneg_of_nonpos (hp k).le (hclear.excess_nonpos k)
  have hsum_zero : ∑ k, p k * E.aggregateExcess x k = 0 := hclear.value_zero
  have hterm_zero : p l * E.aggregateExcess x l = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm_nonpos).mp hsum_zero l (Finset.mem_univ l)
  exact (mul_eq_zero.mp hterm_zero).resolve_left (hp l).ne'

/-! ### Feasibility and Pareto optimality -/

/-- A **feasible allocation**: Nonnegative bundles whose aggregate consumption does not exceed
aggregate endowment in any good (free disposal). -/
structure Feasible (x : E.Agents → (Fin L → ℝ)) : Prop where
  /-- Every bundle is nonnegative in every good. -/
  nonneg : ∀ a l, 0 ≤ x a l
  /-- Aggregate consumption does not exceed aggregate endowment in any good (free disposal). -/
  excess_nonpos : ∀ l, E.aggregateExcess x l ≤ 0

/-- Allocation `x` **Pareto dominates** `y` if every agent weakly prefers `x` and at least one
strictly prefers it. -/
def ParetoDominates (x y : E.Agents → (Fin L → ℝ)) : Prop :=
  Econlib.Preferences.ParetoDominates E.pref x y

/-- A feasible allocation is **Pareto optimal** if no feasible allocation Pareto dominates it. -/
structure ParetoOptimal (x : E.Agents → (Fin L → ℝ)) : Prop where
  /-- The allocation is feasible. -/
  feasible : E.Feasible x
  /-- No feasible allocation Pareto dominates `x`. -/
  undominated : ¬ ∃ y, E.Feasible y ∧ E.ParetoDominates y x

/-- An allocation is in the **core** if it is feasible and no nonempty coalition `S` has a
reallocation `y` within its own endowments (`∑_{i∈S} y i ≤ ∑_{i∈S} endow i`) that every member
strictly prefers. -/
structure Core (x : E.Agents → (Fin L → ℝ)) : Prop where
  /-- The allocation is feasible. -/
  feasible : E.Feasible x
  /-- No nonempty coalition can improve on `x` within its own endowments. -/
  unblocked : ¬ ∃ (S : Finset E.Agents) (y : E.Agents → (Fin L → ℝ)),
      S.Nonempty ∧
      (∀ i ∈ S, ∀ l, 0 ≤ y i l) ∧
      (∀ l, ∑ i ∈ S, y i l ≤ ∑ i ∈ S, E.endow i l) ∧
      ∀ i ∈ S, y i ≻[E.pref i] x i

/-- A **Walrasian (competitive) equilibrium** (Debreu 1959): Nonnegative, nonzero prices at which
every agent is optimizing and markets clear. -/
structure WalrasianEquilibrium (E : Economy L) where
  /-- Equilibrium prices. -/
  price : Fin L → ℝ
  /-- Equilibrium allocation. -/
  alloc : E.Agents → (Fin L → ℝ)
  /-- Prices are nonnegative. -/
  price_cone : ∀ l, 0 ≤ price l
  /-- Some good has a positive price. -/
  price_ne : ∃ l, 0 < price l
  /-- Each agent's allocation is optimal in its budget set. -/
  isOptimal : ∀ a, alloc a ∈ E.demand price a
  /-- Markets clear (free-goods form). -/
  clears : E.MarketClears price alloc

/-- The **relabeled economy** whose endowments are replaced by the (nonnegative) allocation `x`,
keeping the same agents and preferences. In `E.transferEndow hx`, agent `a`'s wealth at price `p`
is `p ⬝ᵥ x a` — the transfer-adjusted wealth of the second welfare theorem — so a Pareto optimum of
`E` supported by `p` is exactly a quasi-equilibrium of `E.transferEndow hx`. This is the bridge
that lets the existence-side McKenzie upgrade (`quasi_to_walrasian`) deliver full budget-optimality
for every agent, including zero-wealth ones, from supporting prices alone. -/
def transferEndow {x : E.Agents → (Fin L → ℝ)} (hx : ∀ a, x a ∈ nonnegOrthant L) : Economy L where
  Agents := E.Agents
  agentsFin := E.agentsFin
  pref := E.pref
  endow := x
  endow_mem := hx

/-- A **Walrasian (competitive) equilibrium with lump-sum transfers**: Nonnegative, nonzero prices
together with a balanced transfer scheme `transfer` (`∑ transfer = 0`, so transfers redistribute
without creating or destroying value), at which every agent is optimizing within its
transfer-adjusted budget set `budgetSetAt price (price ⬝ᵥ endow a + transfer a)` and markets clear.
The balance condition is a structure field — a transfer scheme that fails to balance cannot be
packaged as an equilibrium. -/
structure WalrasianEquilibriumWithTransfers (E : Economy L) where
  /-- Equilibrium prices. -/
  price : Fin L → ℝ
  /-- Equilibrium allocation. -/
  alloc : E.Agents → (Fin L → ℝ)
  /-- The lump-sum transfer to each agent (signed). -/
  transfer : E.Agents → ℝ
  /-- Prices are nonnegative. -/
  price_cone : ∀ l, 0 ≤ price l
  /-- Some good has a positive price. -/
  price_ne : ∃ l, 0 < price l
  /-- Transfers balance: They redistribute wealth without aggregate injection. -/
  transfers_balance : ∑ a, transfer a = 0
  /-- Each agent's allocation is optimal in its transfer-adjusted budget set. -/
  isOptimal : ∀ a, alloc a ∈
    Optimization.argmaxRel (E.pref a) (budgetSetAt price (price ⬝ᵥ E.endow a + transfer a))
  /-- Markets clear (free-goods form). -/
  clears : E.MarketClears price alloc

/-! ## Structural demand lemmas -/

variable {E}

/-- `W` **decentralizes** the allocation `x`: Its equilibrium allocation is exactly `x`, supported
by the canonical balanced lump-sum transfers `transfer a = price ⬝ᵥ x a − price ⬝ᵥ endow a`. `W` is
already a full equilibrium (every field of `WalrasianEquilibriumWithTransfers`); `Decentralizes`
adds nothing to equilibrium-hood — it only records that `W` implements the *given* optimum `x` with
the supporting transfer scheme. This is the property the second welfare theorem establishes (see
`Econlib.Equilibrium.Economy.ParetoOptimal.exists_walrasianEquilibriumWithTransfers`). -/
structure WalrasianEquilibriumWithTransfers.Decentralizes (W : E.WalrasianEquilibriumWithTransfers)
    (x : E.Agents → Fin L → ℝ) : Prop where
  /-- The equilibrium allocation is exactly the target allocation `x`. -/
  alloc_eq : W.alloc = x
  /-- The transfers are the canonical balanced supporting scheme. -/
  transfer_eq : ∀ a, W.transfer a = W.price ⬝ᵥ x a - W.price ⬝ᵥ E.endow a

/-- Membership in `Economy.budgetSet`. -/
@[simp] lemma mem_budgetSet {p : Fin L → ℝ} {a : E.Agents} {x : Fin L → ℝ} :
    x ∈ E.budgetSet p a ↔ (∀ l, 0 ≤ x l) ∧ p ⬝ᵥ x ≤ p ⬝ᵥ E.endow a := Iff.rfl

/-- The budget set is convex. -/
lemma budgetSet_convex (p : Fin L → ℝ) (a : E.Agents) : Convex ℝ (E.budgetSet p a) :=
  budgetSetAt_convex p _

/-- The endowment is always affordable. -/
lemma endow_mem_budgetSet (p : Fin L → ℝ) (a : E.Agents) :
    E.endow a ∈ E.budgetSet p a :=
  ⟨E.endow_mem a, le_refl _⟩

/-- Demand is contained in the budget set. -/
lemma demand_subset_budgetSet (p : Fin L → ℝ) (a : E.Agents) :
    E.demand p a ⊆ E.budgetSet p a :=
  fun _ hx => hx.1

/-- Scaling prices by `t > 0` leaves the budget set unchanged. -/
lemma budgetSet_scale {t : ℝ} (ht : 0 < t) (p : Fin L → ℝ) (a : E.Agents) :
    E.budgetSet (t • p) a = E.budgetSet p a := by
  unfold budgetSet
  rw [smul_dotProduct, smul_eq_mul, budgetSetAt_scale ht]

/-- Demand is homogeneous of degree zero in prices. -/
lemma demand_homogeneous {t : ℝ} (ht : 0 < t) (p : Fin L → ℝ) (a : E.Agents) :
    E.demand (t • p) a = E.demand p a := by
  unfold demand
  rw [E.budgetSet_scale ht]

/-- Convex preferences imply convex demand. -/
lemma demand_convex (a : E.Agents) (hconv : ConvexPreference (E.pref a)) (p : Fin L → ℝ) :
    Convex ℝ (E.demand p a) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hxS, hxmax⟩ := hx
  obtain ⟨hyS, hymax⟩ := hy
  have hcombS : s • x + t • y ∈ E.budgetSet p a :=
    E.budgetSet_convex p a hxS hyS hs ht hst
  refine ⟨hcombS, fun z hz => ?_⟩
  have hx_upper : x ∈ (E.pref a).upperContour x := (E.pref a).le_refl x
  have hy_upper : y ∈ (E.pref a).upperContour x := hymax x hxS
  have hcomb_le_x : (E.pref a).le (s • x + t • y) x :=
    hconv.convex_upper x hx_upper hy_upper hs ht hst
  exact (E.pref a).le_trans _ _ _ hcomb_le_x (hxmax z hz)

/-- Strictly convex preferences imply single-valued demand. -/
lemma demand_subsingleton (a : E.Agents) (hstrict : StrictConvexPreference (E.pref a))
    (p : Fin L → ℝ) : (E.demand p a).Subsingleton :=
  Optimization.argmaxRel_subsingleton_of_strictConvex hstrict (E.budgetSet_convex p a)

/-- The budget set is compact at strictly positive prices. -/
lemma isCompact_budgetSet_of_pos_prices {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) (a : E.Agents) :
    IsCompact (E.budgetSet p a) :=
  isCompact_budgetSetAt_of_pos_prices hp _

/-- The budget set is nonempty (it contains the endowment). -/
lemma budgetSet_nonempty (p : Fin L → ℝ) (a : E.Agents) : (E.budgetSet p a).Nonempty :=
  ⟨E.endow a, endow_mem_budgetSet p a⟩

/-- In a regular economy, each agent's demand equals the `argmax` of a continuous Debreu utility
over the budget set. The representation is price-independent. -/
lemma exists_demand_eq_argmax (hreg : RegularEconomy E) (a : E.Agents) :
    ∃ u : (Fin L → ℝ) → ℝ, Continuous u ∧
      ∀ p : Fin L → ℝ, E.demand p a = Optimization.argmax u (E.budgetSet p a) := by
  obtain ⟨C, hCval⟩ :=
    (Econlib.Preferences.continuousPref_iff_exists (E.pref a)).mp (hreg.contPref a)
  obtain ⟨u, hrep, hcont⟩ := C.exists_continuous_utility_representation
  rw [hCval] at hrep
  refine ⟨u, hcont, fun p => ?_⟩
  rw [show E.demand p a = Optimization.argmaxRel (E.pref a) (E.budgetSet p a) from rfl,
    ← Optimization.argmax_eq_argmaxRel_of_represents hrep]

/-- Demand is nonempty at strictly positive prices. -/
theorem demand_nonempty (hreg : RegularEconomy E) {p : Fin L → ℝ} (hp : ∀ l, 0 < p l)
    (a : E.Agents) : (E.demand p a).Nonempty := by
  obtain ⟨u, hcont, hda⟩ := E.exists_demand_eq_argmax hreg a
  rw [hda p]
  exact Optimization.argmax_nonempty (E.isCompact_budgetSet_of_pos_prices hp a)
    (E.budgetSet_nonempty p a) hcont.continuousOn

/-- Demand is compact at strictly positive prices. -/
theorem demand_compact (hreg : RegularEconomy E) {p : Fin L → ℝ} (hp : ∀ l, 0 < p l)
    (a : E.Agents) : IsCompact (E.demand p a) := by
  obtain ⟨u, hcont, hda⟩ := E.exists_demand_eq_argmax hreg a
  rw [hda p]
  exact Optimization.argmax_compact (E.isCompact_budgetSet_of_pos_prices hp a) hcont.continuousOn

-- Upper hemicontinuity of demand in prices (Berge's maximum theorem) is stated as
-- `Economy.demand_upperHemicontinuousOn` in `Equilibrium/Existence.lean`, restricted to a set of
-- strictly positive prices: only there are the budget set compact and the cheaper-point (Slater)
-- condition satisfiable. A statement over the full price space is vacuous — at `p = 0` the budget
-- set is the whole non-compact nonnegative orthant and no nonnegative bundle is cheaper than the
-- endowment — so no economy could instantiate it. (That restricted
-- version needs the *pointwise* `budgetSetAt_upperHemicontinuousAt`, which lives in
-- `Existence.lean`.)

/-! ## Budget-binding (individual Walras's law) -/

/-- **Budget-binding.** Under local nonsatiation, a demanded bundle exhausts the budget:
`p ⬝ᵥ x = p ⬝ᵥ endow a`. No sign condition on prices is needed. -/
theorem demand_budget_binds (hreg : RegularEconomy E) {p : Fin L → ℝ} (a : E.Agents)
    {x : Fin L → ℝ} (hx : x ∈ E.demand p a) : p ⬝ᵥ x = p ⬝ᵥ E.endow a :=
  budgetSetAt_binds (hreg.locallyNonsatiated a) hx

/-- `p ⬝ᵥ aggregateExcess x = ∑ a, (p ⬝ᵥ x a - p ⬝ᵥ endow a)`. -/
lemma dotProduct_aggregateExcess (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)) :
    p ⬝ᵥ E.aggregateExcess x
      = ∑ a, (p ⬝ᵥ (x a) - p ⬝ᵥ E.endow a) := by
  simp only [dotProduct, aggregateExcess, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_comm

/-- **Walras's law.** If every agent demands its bundle then `p ⬝ᵥ aggregateExcess x = 0`. -/
theorem walras_law (hreg : RegularEconomy E) {p : Fin L → ℝ}
    {x : E.Agents → (Fin L → ℝ)} (hx : ∀ a, x a ∈ E.demand p a) :
    p ⬝ᵥ E.aggregateExcess x = 0 :=
  walras_law_over (fun a => E.demand_budget_binds hreg a (hx a))

/-! ## Positive equilibrium prices -/

/-- **Positive equilibrium prices.** In a regular economy, a Walrasian equilibrium in which some
agent has strictly positive wealth has strictly positive prices: A zero-priced good is free, so the
positive-wealth agent's demanded bundle — which weakly beats an affordable interior bundle — could
be strictly improved by consuming more of the free good (`Desirable`), contradicting optimality. -/
theorem WalrasianEquilibrium.price_pos (hreg : RegularEconomy E) (W : WalrasianEquilibrium E)
    (hwealth : ∃ a, 0 < W.price ⬝ᵥ E.endow a) : ∀ l, 0 < W.price l := by
  intro l₀
  by_contra hl₀
  obtain ⟨a, ha⟩ := hwealth
  have hl₀_eq : W.price l₀ = 0 := le_antisymm (not_lt.mp hl₀) (W.price_cone l₀)
  obtain ⟨hx_bud, hx_max⟩ := W.isOptimal a
  -- A small constant interior bundle `z = ε·𝟙` is affordable at the agent's positive wealth.
  have hsum_nonneg : 0 ≤ ∑ l, W.price l := Finset.sum_nonneg fun l _ => W.price_cone l
  have hsum1_pos : 0 < ∑ l, W.price l + 1 := by linarith
  set ε : ℝ := (W.price ⬝ᵥ E.endow a) / (∑ l, W.price l + 1) with hε_def
  have hε_pos : 0 < ε := div_pos ha hsum1_pos
  have hz_dot : W.price ⬝ᵥ (fun _ : Fin L => ε) = (∑ l, W.price l) * ε := by
    simp only [dotProduct]
    rw [← Finset.sum_mul]
  have hz_afford : W.price ⬝ᵥ (fun _ : Fin L => ε) ≤ W.price ⬝ᵥ E.endow a := by
    rw [hz_dot]
    have hfrac_le_one : (∑ l, W.price l) / (∑ l, W.price l + 1) ≤ 1 := by
      rw [div_le_one hsum1_pos]; linarith
    calc (∑ l, W.price l) * ε
        = (W.price ⬝ᵥ E.endow a) * ((∑ l, W.price l) / (∑ l, W.price l + 1)) := by
          rw [hε_def]; ring
      _ ≤ (W.price ⬝ᵥ E.endow a) * 1 := mul_le_mul_of_nonneg_left hfrac_le_one ha.le
      _ = W.price ⬝ᵥ E.endow a := mul_one _
  have hx_ge_z : W.alloc a ≽[E.pref a] (fun _ : Fin L => ε) :=
    hx_max _ ⟨fun _ => hε_pos.le, hz_afford⟩
  -- Adding one unit of the free good `l₀` stays affordable but strictly improves.
  set y : Fin L → ℝ := fun l => W.alloc a l + (if l = l₀ then 1 else 0) with hy_def
  have h_le : W.alloc a ≤ y := fun l => by simp only [hy_def]; split <;> linarith
  have h_ne : W.alloc a ≠ y := fun heq => by
    have hcontra := congr_fun heq.symm l₀
    simp only [hy_def, if_true] at hcontra; linarith
  have hy_dot : W.price ⬝ᵥ y = W.price ⬝ᵥ W.alloc a := by
    simp only [dotProduct, hy_def, mul_add]
    rw [Finset.sum_add_distrib]
    have hzero : ∑ l, W.price l * (if l = l₀ then (1 : ℝ) else 0) = 0 := by
      rw [Finset.sum_eq_single l₀]
      · rw [if_pos rfl, hl₀_eq]; ring
      · intro l _ hl; rw [if_neg hl]; ring
      · intro h; exact absurd (Finset.mem_univ l₀) h
    rw [hzero, add_zero]
  have hy_bud : y ∈ E.budgetSet W.price a := by
    refine ⟨fun l => by simp only [hy_def]; split <;> linarith [hx_bud.1 l], ?_⟩
    rw [hy_dot]; exact hx_bud.2
  have hy_pref : y ≻[E.pref a] W.alloc a :=
    (hreg.desirable a).improve (fun _ => hε_pos) hx_ge_z h_le h_ne
  exact hy_pref.2 (hx_max y hy_bud)

/-! ## Revealed-preference cost bounds (first-welfare building blocks) -/

/-- **Strictly-preferred bundles are strictly costly.** If `x` is demanded and a nonnegative bundle
`z` is strictly preferred to it, then `p ⬝ᵥ endow a < p ⬝ᵥ z`. No local nonsatiation needed. -/
theorem strictlyPreferred_costly {p : Fin L → ℝ} {a : E.Agents} {x z : Fin L → ℝ}
    (hx : x ∈ E.demand p a) (hz : z ∈ nonnegOrthant L) (hlt : z ≻[E.pref a] x) :
    p ⬝ᵥ E.endow a < p ⬝ᵥ z :=
  budgetSetAt_strictlyPreferred_costly hx hz hlt

/-- **Weakly-preferred bundles are at least as costly.** Under local nonsatiation, if `x` is
demanded and a nonnegative bundle `z` is weakly preferred to it, then `p ⬝ᵥ endow a ≤ p ⬝ᵥ z`. -/
theorem preferred_costly (hreg : RegularEconomy E) {p : Fin L → ℝ} {a : E.Agents}
    {x z : Fin L → ℝ} (hx : x ∈ E.demand p a) (hz : z ∈ nonnegOrthant L)
    (hle : z ≽[E.pref a] x) : p ⬝ᵥ E.endow a ≤ p ⬝ᵥ z :=
  budgetSetAt_preferred_costly (hreg.locallyNonsatiated a) hx hz hle

end Economy

/-! ## The continuum (measure) economy

A `MeasureEconomy` carries its aggregation as data (a measure / stationary law). Unlike
`Economy`, where the `Fintype` counting instance is canonical, the continuum agent space has no
competing instance, so the data `[agg]` is unambiguous and the equilibrium notions reuse the
`*Over` layer. -/
structure MeasureEconomy (L : ℕ) where
  /-- The (possibly continuum) agent space. -/
  Agents : Type*
  /-- The aggregation functional over agents, carried as data (a measure / stationary law). -/
  [agg : AgentAggregation Agents]
  /-- Each agent's preference over commodity bundles. -/
  pref : Agents → PreferenceRel (Fin L → ℝ)
  /-- Each agent's endowment. -/
  endow : Agents → (Fin L → ℝ)
  /-- Endowments are nonnegative. -/
  endow_mem : ∀ a, endow a ∈ nonnegOrthant L

attribute [instance] MeasureEconomy.agg

namespace MeasureEconomy

variable (M : MeasureEconomy L)

/-- Agent `a`'s budget set at prices `p` (aggregation-free). -/
def budgetSet (p : Fin L → ℝ) (a : M.Agents) : Set (Fin L → ℝ) :=
  budgetSetAt p (p ⬝ᵥ M.endow a)

/-- The demand correspondence: Greatest elements of the preference over the budget set. -/
noncomputable def demand (p : Fin L → ℝ) (a : M.Agents) : Set (Fin L → ℝ) :=
  Optimization.argmaxRel (M.pref a) (M.budgetSet p a)

/-- Aggregate excess demand, through the carried aggregation functional. -/
noncomputable def aggregateExcess (x : M.Agents → (Fin L → ℝ)) : Fin L → ℝ :=
  aggregateExcessOver M.endow x

/-- Market clearing (free-goods form). -/
structure MarketClears (p : Fin L → ℝ) (x : M.Agents → (Fin L → ℝ)) : Prop where
  /-- Aggregate excess demand is nonpositive in every good (free disposal). -/
  excess_nonpos : ∀ l, M.aggregateExcess x l ≤ 0
  /-- The value of aggregate excess demand at prices `p` is zero. -/
  value_zero : p ⬝ᵥ (M.aggregateExcess x) = 0

/-- A **Walrasian equilibrium** of a measure economy: Nonnegative nonzero prices at which every
agent optimizes and markets clear. -/
structure WalrasianEquilibrium (M : MeasureEconomy L) where
  /-- Equilibrium prices. -/
  price : Fin L → ℝ
  /-- Equilibrium allocation. -/
  alloc : M.Agents → (Fin L → ℝ)
  /-- Prices are nonnegative. -/
  price_cone : ∀ l, 0 ≤ price l
  /-- Some good has a positive price. -/
  price_ne : ∃ l, 0 < price l
  /-- Each agent's allocation is optimal in its budget set. -/
  isOptimal : ∀ a, alloc a ∈ M.demand price a
  /-- Markets clear (free-goods form). -/
  clears : M.MarketClears price alloc

end MeasureEconomy

end Econlib.Equilibrium
