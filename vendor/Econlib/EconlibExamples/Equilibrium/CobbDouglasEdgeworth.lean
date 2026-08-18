import Mathlib
import Econlib

/-!
# The Edgeworth box: a Cobb–Douglas exchange equilibrium

The canonical two-agent, two-good exchange economy, with **Cobb–Douglas** preferences. This is the
textbook Edgeworth box — the geometric-mean tastes give the familiar smooth, strictly convex
indifference curves (descriptive framing; not separately formalized here) — with a unique interior
equilibrium, and the uniqueness is a theorem here (`edgeworth_unique`), not just folklore. It
also serves as the **regression-guard witness** that the (weakened) `RegularEconomy` bundle admits
Cobb–Douglas — we certify the economy regular through `RegularEconomy.ofCobbDouglas`, which routes
through `BoundaryAvoiding.toDesirable` (Cobb–Douglas is `0` on the orthant boundary, so it is not
globally strongly monotone).

## The model

* Two agents (`Fin 2`), two goods (`Fin 2`), counting aggregation.
* Both agents have symmetric Cobb–Douglas tastes `u x = x₀^{1/2} x₁^{1/2}` (the geometric mean).
* Endowments `e₀ = (2, 1)`, `e₁ = (1, 2)`: the agents hold mirror-image bundles.
* Equilibrium: price `(1, 1)`; each agent has wealth `3` and demands `(3/2, 3/2)`, spending half its
  wealth on each good. The allocation moves both agents to the symmetric split — gains from
  trade — and aggregate demand `(3, 3)` equals the aggregate endowment, so markets clear.

On the consumer side, `edgeworth_demand_optimal` does not re-derive optimality by hand: it
instantiates the library's closed-form Cobb–Douglas demand
(`Economy.demand_eq_singleton_of_cobbDouglas`), whose unique optimizer is the expenditure-share
bundle — at price `(1,1)` and wealth `3`, exactly the symmetric split `(3/2, 3/2)`.

## Main definitions and theorems

* `economy`, `economy_regular` — the Cobb–Douglas exchange economy and its `RegularEconomy` witness.
* `edgeworth_demand_optimal` — each agent's `(3/2, 3/2)` is demand-optimal, read off the library's
  closed-form Cobb–Douglas demand singleton.
* `edgeworth_aggregateExcess_zero`, `edgeworth_market_clears`, `edgeworthEquilibrium` — exact
  clearing and the assembled equilibrium.
* `edgeworth_gains_from_trade` — each agent **strictly** prefers `(3/2, 3/2)` to its endowment.
* `edgeworth_walras_law` — Walras's law holds at the equilibrium.
* `edgeworth_pareto_optimal` — **first welfare theorem**: the equilibrium is Pareto optimal.
* `edgeworth_supporting_prices` — **second welfare theorem** (supporting-price / quasi-equilibrium
  form): the Pareto-optimal allocation is supported by prices.
* `edgeworth_unique`, `edgeworth_price_ray_isEquilibrium` — **uniqueness up to price scale**: the
  equilibrium set is exactly the ray `{t • (1,1) : t > 0}`, each with allocation `(3/2, 3/2)`.
-/

noncomputable section

namespace EconlibExamples.Equilibrium.CobbDouglasEdgeworth

open Econlib.Equilibrium Econlib.Preferences Matrix

/-! ## The economy -/

/-- Symmetric Cobb–Douglas tastes: equal weights `1/2` on each good (the geometric mean). -/
def cdU : CobbDouglasUtility 2 := ⟨![1/2, 1/2], by intro i; fin_cases i <;> norm_num⟩

/-- Mirror-image endowments: agent `0` holds `(2,1)`, agent `1` holds `(1,2)`. -/
def edgeEndow : Fin 2 → (Fin 2 → ℝ) := ![![2, 1], ![1, 2]]

/-- Equilibrium price: both goods priced at `1`. -/
def edgePrice : Fin 2 → ℝ := ![1, 1]

/-- Equilibrium allocation: each agent consumes the symmetric bundle `(3/2, 3/2)`. -/
def edgeAlloc : Fin 2 → (Fin 2 → ℝ) := fun _ => ![3/2, 3/2]

/-- Every endowment coordinate is strictly positive (the survival/cheaper-point condition). -/
lemma edgeEndow_pos : ∀ (a : Fin 2) (l : Fin 2), 0 < edgeEndow a l := by
  intro a l; fin_cases a <;> fin_cases l <;> norm_num [edgeEndow]

/-- Each agent's wealth at the equilibrium price is `3`. -/
lemma edge_wealth (a : Fin 2) : edgePrice ⬝ᵥ edgeEndow a = 3 := by
  fin_cases a <;> norm_num [edgePrice, edgeEndow, dotProduct, Fin.sum_univ_two]

/-- The two-agent, two-good Cobb–Douglas exchange economy. -/
def economy : Economy 2 where
  Agents := Fin 2
  pref := fun _ => preferenceOfRealUtility cdU.uTotal
  endow := edgeEndow
  endow_mem := fun a l => (edgeEndow_pos a l).le

/-- The economy is regular: Cobb–Douglas preferences with strictly positive endowments. This is the
total-Cobb–Douglas `RegularEconomy` witness. -/
lemma economy_regular : RegularEconomy economy :=
  RegularEconomy.ofCobbDouglas (by norm_num) economy (fun _ => cdU) (fun _ => rfl) edgeEndow_pos

/-- The total Cobb–Douglas utility for these symmetric tastes is the (truncated) geometric mean. -/
lemma cdU_uTotal_eq (y : Fin 2 → ℝ) :
    cdU.uTotal y = (max (y 0) 0) ^ (1/2 : ℝ) * (max (y 1) 0) ^ (1/2 : ℝ) := by
  rw [CobbDouglasUtility.uTotal_def, Fin.prod_univ_two]
  norm_num [cdU]

/-- The equilibrium bundle has utility `3/2`: `(3/2)^{1/2} (3/2)^{1/2} = 3/2`. -/
lemma uTotal_edgeAlloc : cdU.uTotal ![3/2, 3/2] = 3/2 := by
  rw [cdU_uTotal_eq]
  rw [show (![3/2, 3/2] : Fin 2 → ℝ) 0 = 3/2 from rfl,
    show (![3/2, 3/2] : Fin 2 → ℝ) 1 = 3/2 from rfl, max_eq_left (by norm_num : (0:ℝ) ≤ 3/2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3/2), show (1/2 : ℝ) + 1/2 = 1 by norm_num,
    Real.rpow_one]

/-! ## Consumer optimality -/

/-- **Each agent's `(3/2, 3/2)` is demand-optimal.** Read off the library's closed-form Cobb–Douglas
demand (`Economy.demand_eq_singleton_of_cobbDouglas`): the unique optimizer is the expenditure-share
bundle, which at price `(1,1)` and wealth `3` is exactly `(½·3, ½·3) = (3/2, 3/2)`. -/
theorem edgeworth_demand_optimal (a : economy.Agents) :
    edgeAlloc a ∈ economy.demand edgePrice a := by
  have hpos : ∀ l, 0 < edgePrice l := fun l => by fin_cases l <;> norm_num [edgePrice]
  have hw : (0 : ℝ) < edgePrice ⬝ᵥ economy.endow a := by
    change (0 : ℝ) < edgePrice ⬝ᵥ edgeEndow a; rw [edge_wealth]; norm_num
  -- The demand set is the singleton expenditure-share bundle; evaluate it at this price and wealth.
  rw [economy.demand_eq_singleton_of_cobbDouglas (by norm_num) a cdU rfl hpos hw,
    Set.mem_singleton_iff]
  funext l
  rw [show edgePrice ⬝ᵥ economy.endow a = 3 from edge_wealth a]
  fin_cases l <;> norm_num [edgeAlloc, cdU, edgePrice, Fin.sum_univ_two]

/-! ## Market clearing and the equilibrium -/

/-- Aggregate excess demand is identically zero: aggregate demand `(3,3)` equals the aggregate
endowment exactly (not merely free-goods clearing). -/
theorem edgeworth_aggregateExcess_zero : economy.aggregateExcess edgeAlloc = 0 := by
  funext l
  change (∑ a : Fin 2, edgeAlloc a l) - (∑ a : Fin 2, edgeEndow a l) = (0 : Fin 2 → ℝ) l
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases l <;> norm_num [edgeAlloc, edgeEndow]

/-- Markets clear: aggregate demand `(3,3)` equals the aggregate endowment. -/
theorem edgeworth_market_clears : economy.MarketClears edgePrice edgeAlloc := by
  refine ⟨fun l => ?_, ?_⟩ <;> rw [edgeworth_aggregateExcess_zero] <;> simp

/-- The assembled Walrasian equilibrium. -/
def edgeworthEquilibrium : economy.WalrasianEquilibrium where
  price := edgePrice
  alloc := edgeAlloc
  price_cone := fun l => by fin_cases l <;> simp [edgePrice]
  price_ne := ⟨0, by simp [edgePrice]⟩
  isOptimal := edgeworth_demand_optimal
  clears := edgeworth_market_clears

/-! ## Welfare theorems -/

/-- **Walras's law** holds at the equilibrium: the value of aggregate excess demand is zero. -/
theorem edgeworth_walras_law :
    edgePrice ⬝ᵥ economy.aggregateExcess edgeAlloc = 0 :=
  economy.walras_law economy_regular edgeworth_demand_optimal

/-- **Gains from trade.** Each agent strictly prefers its equilibrium bundle `(3/2, 3/2)`
to its endowment: the mirror-image endowment `(2,1)` / `(1,2)` has geometric-mean utility
`√2 ≈ 1.414`, strictly below the symmetric split's `3/2`. (Here `(pref a).lt x y` reads `x ≻ y`.) -/
theorem edgeworth_gains_from_trade (a : economy.Agents) :
    (economy.pref a).lt (edgeAlloc a) (edgeEndow a) := by
  -- `√2 < 3/2`, since `(√2)² = 2 < 9/4 = (3/2)²`.
  have hsqrt2 : (2 : ℝ) ^ (1/2 : ℝ) < 3/2 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
  -- A bundle holding `2` of one good and `1` of the other has utility `√2 · 1 = √2 < 3/2`.
  have key : ∀ y : Fin 2 → ℝ, ((y 0 = 2 ∧ y 1 = 1) ∨ (y 0 = 1 ∧ y 1 = 2)) →
      cdU.uTotal y < 3/2 := by
    rintro y (⟨h0, h1⟩ | ⟨h0, h1⟩) <;>
      · rw [cdU_uTotal_eq, h0, h1, max_eq_left (by norm_num : (0:ℝ) ≤ 2),
          max_eq_left (by norm_num : (0:ℝ) ≤ 1), Real.one_rpow]
        first
          | (rw [mul_one]; exact hsqrt2)
          | (rw [one_mul]; exact hsqrt2)
  -- `(pref a).lt x y` unfolds through the `preferenceOfRealUtility` abbrev to `u y < u x`;
  -- `preferenceOfUtilityIn_lt_iff` is `@[simp]`, so it lands directly on the utility comparison.
  simp only [economy, edgeAlloc, preferenceOfUtilityIn_lt_iff, uTotal_edgeAlloc]
  -- Goal: `cdU.uTotal (edgeEndow a) < 3/2`.
  fin_cases a
  · exact key _ (Or.inl ⟨rfl, rfl⟩)
  · exact key _ (Or.inr ⟨rfl, rfl⟩)

/-- **First welfare theorem.** The Cobb–Douglas equilibrium allocation is Pareto optimal. -/
theorem edgeworth_pareto_optimal : economy.ParetoOptimal edgeAlloc :=
  edgeworthEquilibrium.paretoOptimal economy_regular

/-- **Second welfare theorem** (supporting-price / quasi-equilibrium form). The Pareto-optimal
equilibrium allocation is supported by prices: there is a nonzero nonnegative price vector at which
every bundle an agent strictly prefers to its allocation costs at least as much. -/
theorem edgeworth_supporting_prices :
    ∃ p : Fin 2 → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      ∀ a, ∀ z ∈ nonnegOrthant 2, (economy.pref a).lt z (edgeAlloc a) →
        p ⬝ᵥ edgeAlloc a ≤ p ⬝ᵥ z := by
  obtain ⟨p, hnn, hpos, hsupp, _⟩ :=
    edgeworth_pareto_optimal.exists_quasiEquilibrium_price (inferInstanceAs (Nonempty (Fin 2)))
      economy_regular (by norm_num)
  exact ⟨p, hnn, hpos, hsupp⟩

/-! ## Uniqueness -/

/-- **Uniqueness of the Edgeworth equilibrium.** Every Walrasian equilibrium of the symmetric
Cobb–Douglas exchange economy has equal prices and the symmetric allocation: prices are a positive
scalar multiple of `(1,1)` and each agent consumes `(3/2, 3/2)`. Together with
`edgeworthEquilibrium` this determines the equilibrium of the box, up to price normalization. The
scalar is free — every `t • (1,1)` with `t > 0` is also an equilibrium, proved in the
converse `edgeworth_price_ray_isEquilibrium` (demand is homogeneous of degree zero in prices). -/
theorem edgeworth_unique (W : economy.WalrasianEquilibrium) :
    (∃ t : ℝ, 0 < t ∧ W.price = t • edgePrice) ∧ W.alloc = edgeAlloc := by
  -- Every agent's wealth is positive at the (nonzero, nonnegative) equilibrium price.
  have hwealth : ∀ a : Fin 2, 0 < W.price ⬝ᵥ economy.endow a := by
    intro a
    obtain ⟨l', hl'⟩ := W.price_ne
    exact Finset.sum_pos' (fun l _ => mul_nonneg (W.price_cone l) (edgeEndow_pos a l).le)
      ⟨l', Finset.mem_univ l', mul_pos hl' (edgeEndow_pos a l')⟩
  -- Hence prices are strictly positive (a zero price would let demand grab a free good).
  have hpos : ∀ l, 0 < W.price l := W.price_pos economy_regular ⟨(0 : Fin 2), hwealth 0⟩
  -- Cobb–Douglas demand fixes each agent's bundle to the expenditure-share formula.
  have hα_sum : ∑ i, cdU.α i = 1 := by
    rw [Fin.sum_univ_two]; norm_num [cdU]
  have hα_val : ∀ l, cdU.α l = 1 / 2 := fun l => by fin_cases l <;> norm_num [cdU]
  have hdemand : ∀ a : Fin 2, W.alloc a
      = fun l => (cdU.α l / ∑ i, cdU.α i) * (W.price ⬝ᵥ economy.endow a) / W.price l := by
    intro a
    have hsingle :=
      economy.demand_eq_singleton_of_cobbDouglas (by norm_num) a cdU rfl hpos (hwealth a)
    have hmem := W.isOptimal a
    rw [hsingle] at hmem
    exact hmem
  have halloc : ∀ a l : Fin 2, W.alloc a l
      = 1 / 2 * (W.price ⬝ᵥ economy.endow a) / W.price l := by
    intro a l
    rw [congr_fun (hdemand a) l, hα_val l, hα_sum]
    norm_num
  -- Wealths in coordinates.
  have hwealth_coord : ∀ a : Fin 2, W.price ⬝ᵥ economy.endow a
      = W.price 0 * edgeEndow a 0 + W.price 1 * edgeEndow a 1 := by
    intro a
    change ∑ l, W.price l * edgeEndow a l = _
    rw [Fin.sum_univ_two]
  -- Exact clearing in good 0 (prices are positive, so the free-goods slack vanishes).
  have hexc : economy.aggregateExcess W.alloc = 0 := W.clears.aggregateExcess_eq_zero hpos
  have hclear0 : W.alloc (0 : Fin 2) 0 + W.alloc (1 : Fin 2) 0 = 3 := by
    have h := congr_fun hexc 0
    change (∑ a : Fin 2, W.alloc a 0) - (∑ a : Fin 2, edgeEndow a 0) = 0 at h
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
    norm_num [edgeEndow] at h
    linarith
  -- Demand formulas + clearing in good 0 force equal prices.
  have hprice_eq : W.price 1 = W.price 0 := by
    have h0 := halloc 0 0
    have h1 := halloc 1 0
    rw [hwealth_coord 0] at h0
    rw [hwealth_coord 1] at h1
    norm_num [edgeEndow] at h0 h1
    rw [h0, h1] at hclear0
    field_simp [(hpos 0).ne'] at hclear0
    linarith
  refine ⟨⟨W.price 0, hpos 0, ?_⟩, ?_⟩
  · -- The price vector is `q₀ • (1,1)`.
    funext l
    fin_cases l <;> simp [edgePrice, hprice_eq]
  · -- Equal prices give wealth `3q₀` and the symmetric `(3/2, 3/2)` split.
    have hwa : ∀ a : Fin 2, W.price ⬝ᵥ economy.endow a = 3 * W.price 0 := by
      intro a
      rw [hwealth_coord a]
      fin_cases a <;> · norm_num [edgeEndow]; linarith
    have hql : ∀ l : Fin 2, W.price l = W.price 0 := by
      intro l
      fin_cases l
      · rfl
      · exact hprice_eq
    funext a l
    have h := halloc a l
    rw [hwa a, hql l] at h
    have hval : edgeAlloc a l = 3 / 2 := by
      fin_cases l <;> norm_num [edgeAlloc]
    rw [h, hval]
    field_simp [(hpos 0).ne']

/-- **The price scalar is free** (converse to `edgeworth_unique`). For every positive
scalar `t`, the rescaled price `t • (1,1)` together with the symmetric allocation `(3/2, 3/2)` is
itself a Walrasian equilibrium of the box. Demand is homogeneous of degree zero in prices
(`Economy.demand_homogeneous`), so consumer optimality transports from the `t = 1` equilibrium, and
clearing is exact (`edgeworth_aggregateExcess_zero`) hence price-independent. Combined with
`edgeworth_unique`, the equilibrium set is exactly the ray `{t • (1,1) : t > 0}`. -/
theorem edgeworth_price_ray_isEquilibrium {t : ℝ} (ht : 0 < t) :
    ∃ W : economy.WalrasianEquilibrium, W.price = t • edgePrice ∧ W.alloc = edgeAlloc :=
  ⟨{ price := t • edgePrice
     alloc := edgeAlloc
     price_cone := fun l => by
       simp only [Pi.smul_apply, smul_eq_mul]
       exact mul_nonneg ht.le (by fin_cases l <;> simp [edgePrice])
     price_ne := ⟨0, by simp only [Pi.smul_apply, smul_eq_mul, edgePrice]; norm_num; exact ht⟩
     isOptimal := fun a => by
       rw [economy.demand_homogeneous ht]; exact edgeworth_demand_optimal a
     clears := by
       refine ⟨fun l => ?_, ?_⟩ <;> rw [edgeworth_aggregateExcess_zero] <;> simp }, rfl, rfl⟩

end EconlibExamples.Equilibrium.CobbDouglasEdgeworth

end
