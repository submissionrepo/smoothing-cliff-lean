/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Existence
public import Econlib.Equilibrium.Production.Economy

/-!
# Existence of Walrasian equilibrium with production

This file contains existence results for Arrow–Debreu private-ownership production economies. A
`ProductionEconomy` extends an exchange economy with finitely many firms, a production technology
for each firm, and nonnegative ownership shares that distribute firm profits to consumers.

The main theorem, `exists_equilibrium_prod`, gives a `WalrasianEquilibriumWithProduction`: Prices
are nonnegative and nonzero, firms choose profit-maximizing production plans, consumers choose
optimal bundles from their augmented budget sets, and markets clear with aggregate production
netted out. Its hypotheses are regular consumer preferences and firm technologies
(`RegularProductionEconomy`), production irreducibility (`IrreducibleProd`), a nonempty finite
agent set, at least one commodity, and the endowment-value condition `hendow_valued`.

The condition `hendow_valued` says that at every simplex price where all firms have nonempty
supply, some agent owns an endowment with strictly positive value. It is weaker than requiring
every good to be initially owned and covers labor economies where output goods may have zero
aggregate endowment.

The file also exposes quasi-equilibrium and raw equilibrium-data versions of the result, together
with the bounded and truncated correspondences used to state those intermediate objects.

## Main definitions

* `truncTech`: A `Technology` truncated to `closedBall 0 M`.
* `truncWealth`: Truncated wealth — endowment value plus owned shares of truncated firm profits.
* `truncDemand`: Truncated demand — argmax of preference over the truncated budget set.
* `truncWealthBound`: Uniform upper bound on truncated wealth over the price simplex.

## Main statements

* `mem_supply_of_mem_truncSupply_of_interior`: A truncated interior supply maximizer is a supply
  maximizer for the original technology.
* `exists_attainable_profile_bound`: Feasible production profiles compatible with aggregate
  resources are uniformly bounded in norm.
* `exists_truncated_fixed_point_prod`: Bounded equilibrium data for strictly positive price floors.
* `quasi_to_walrasian_prod`: Quasi-equilibrium data gives Walrasian consumer optimality under
  production irreducibility.
* `exists_quasi_equilibrium_prod`: Quasi-equilibrium with production exists under regularity.
* `exists_equilibrium_data_prod`: Raw equilibrium prices, allocation, plans, and market-clearing
  inequalities exist under the final equilibrium hypotheses.
* `exists_equilibrium_prod`: **Main result.** A `WalrasianEquilibriumWithProduction` exists.

## References

* Arrow, Kenneth J., and Gerard Debreu. 1954. “Existence of an Equilibrium for a Competitive
  Economy.” *Econometrica* 22 (3): 265. [https://doi.org/10.2307/1907353](https://doi.org/10.2307/1907353).
* McKenzie, Lionel W. 1959. “On the Existence of General Equilibrium for a Competitive Market.”
  *Econometrica* 27 (1): 54. [https://doi.org/10.2307/1907777](https://doi.org/10.2307/1907777).

## Tags

walrasian equilibrium, production economy, arrow-debreu, kakutani, existence
-/

@[expose] public section

open Finset BigOperators Matrix Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

namespace ProductionEconomy

/-! ## Truncated technology -/

/-- A technology truncated to `closedBall 0 M`. -/
def truncTech (T : Technology L) (M : ℝ) : Technology L :=
  ⟨T.Y ∩ Metric.closedBall 0 M⟩

@[simp] lemma truncTech_Y (T : Technology L) (M : ℝ) :
    (truncTech T M).Y = T.Y ∩ Metric.closedBall 0 M := rfl

lemma truncTech_closed {T : Technology L} (hT : RegularTechnology T) (M : ℝ) :
    IsClosed (truncTech T M).Y :=
  hT.closed.inter Metric.isClosed_closedBall

lemma truncTech_compact {T : Technology L} (hT : RegularTechnology T) (M : ℝ) :
    IsCompact (truncTech T M).Y :=
  (isCompact_closedBall (0 : Fin L → ℝ) M).of_isClosed_subset
    (truncTech_closed hT M) Set.inter_subset_right

lemma truncTech_convex {T : Technology L} (hT : RegularTechnology T) (M : ℝ) :
    Convex ℝ (truncTech T M).Y :=
  hT.convex.inter (convex_closedBall 0 M)

lemma truncTech_zero_mem {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M) :
    (0 : Fin L → ℝ) ∈ (truncTech T M).Y :=
  ⟨hT.inaction, by simp [Metric.mem_closedBall, hM]⟩

lemma truncTech_nonempty {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M) :
    (truncTech T M).Y.Nonempty :=
  ⟨0, truncTech_zero_mem hT hM⟩

/-- The bilinear pairing `(p, y) ↦ p ⬝ᵥ y` is jointly continuous. -/
lemma dotProduct_continuous_prod :
    Continuous (fun py : (Fin L → ℝ) × (Fin L → ℝ) => py.1 ⬝ᵥ py.2) :=
  continuous_fst.dotProduct continuous_snd

/-- The truncated supply correspondence is upper hemicontinuous in prices (Berge, constant compact
constraint). -/
lemma truncTech_supply_uhc {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M) :
    UpperHemicontinuous (fun p : Fin L → ℝ => (truncTech T M).supply p) :=
  Optimization.argmax_upperHemicontinuous dotProduct_continuous_prod
    UpperHemicontinuous.const LowerHemicontinuous.const
    (fun _ => truncTech_compact hT M) (fun _ => truncTech_nonempty hT hM)

/-- The truncated profit is continuous in prices (Berge value function, constant compact
correspondence). -/
lemma truncTech_profit_continuous {T : Technology L} (hT : RegularTechnology T) {M : ℝ}
    (hM : 0 ≤ M) : Continuous (fun p : Fin L → ℝ => (truncTech T M).profit p) :=
  Optimization.valueFunction_continuous dotProduct_continuous_prod
    UpperHemicontinuous.const LowerHemicontinuous.const
    (fun _ => truncTech_compact hT M) (fun _ => truncTech_nonempty hT hM)

/-- Truncated supply is convex-valued. -/
lemma truncTech_supply_convex {T : Technology L} (hT : RegularTechnology T) (M : ℝ)
    (p : Fin L → ℝ) : Convex ℝ ((truncTech T M).supply p) :=
  (truncTech T M).supply_convex (truncTech_convex hT M) p

/-- Truncated supply is nonempty at any price. -/
lemma truncTech_supply_nonempty {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M)
    (p : Fin L → ℝ) : ((truncTech T M).supply p).Nonempty :=
  Optimization.argmax_nonempty (truncTech_compact hT M) (truncTech_nonempty hT hM)
    ((continuous_const.dotProduct continuous_id).continuousOn)

/-- Truncated supply is compact. -/
lemma truncTech_supply_compact {T : Technology L} (hT : RegularTechnology T) (M : ℝ)
    (p : Fin L → ℝ) : IsCompact ((truncTech T M).supply p) :=
  Optimization.argmax_compact (truncTech_compact hT M)
    ((continuous_const.dotProduct continuous_id).continuousOn)

/-! ## Truncated wealth and demand -/

variable (E : ProductionEconomy L)

/-- **Truncated wealth.** Endowment value plus owned shares of each firm's truncated profit. -/
noncomputable def truncWealth (M : ℝ) (p : Fin L → ℝ) (a : E.Agents) : ℝ :=
  p ⬝ᵥ E.endow a + ∑ j, E.share a j * (truncTech (E.tech j) M).profit p

/-- Truncated wealth is continuous in prices (truncated profit is continuous). -/
lemma truncWealth_continuous (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M)
    (a : E.Agents) : Continuous (fun p => E.truncWealth M p a) := by
  refine (continuous_id.dotProduct continuous_const).add (continuous_finset_sum _ fun j _ => ?_)
  exact continuous_const.mul (truncTech_profit_continuous (hreg.techReg j) hM)

/-- Truncated profit is nonnegative at any price (`0 ∈ truncTech.Y` gives `profit ≥ p ⬝ᵥ 0 = 0`). -/
lemma truncTech_profit_nonneg {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M)
    (p : Fin L → ℝ) : 0 ≤ (truncTech T M).profit p := by
  obtain ⟨y, hy⟩ := truncTech_supply_nonempty hT hM p
  have h0le : p ⬝ᵥ (0 : Fin L → ℝ) ≤ (truncTech T M).profit p :=
    (truncTech T M).dotProduct_le_profit_of_mem_supply (truncTech_zero_mem hT hM) hy
  simpa using h0le

/-- Truncated wealth is nonnegative at nonnegative prices. -/
lemma truncWealth_nonneg (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M) {p : Fin L → ℝ}
    (hp : ∀ l, 0 ≤ p l) (a : E.Agents) : 0 ≤ E.truncWealth M p a := by
  have hendow : 0 ≤ p ⬝ᵥ E.endow a :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hp l) (E.endow_mem a l)
  have hsum : 0 ≤ ∑ j, E.share a j * (truncTech (E.tech j) M).profit p :=
    Finset.sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a j)
      (truncTech_profit_nonneg (hreg.techReg j) hM p)
  exact add_nonneg hendow hsum

/-- `0` lies in the truncated budget set at any nonnegative price. -/
lemma zero_mem_budgetK (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M) {p : Fin L → ℝ}
    (hp : ∀ l, 0 ≤ p l) (a : E.Agents) :
    (0 : Fin L → ℝ) ∈ budgetSetAt p (E.truncWealth M p a) :=
  ⟨fun _ => le_refl 0, by simpa using E.truncWealth_nonneg hreg hM hp a⟩

/-- The endowment is affordable at truncated wealth at any price: Truncated profits are nonneg, so
`truncWealth M p a ≥ p ⬝ᵥ endow a`. -/
lemma endow_mem_budgetK (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M) (p : Fin L → ℝ)
    (a : E.Agents) : E.endow a ∈ budgetSetAt p (E.truncWealth M p a) := by
  refine ⟨E.endow_mem a, ?_⟩
  have hsum : 0 ≤ ∑ j, E.share a j * (truncTech (E.tech j) M).profit p :=
    Finset.sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a j)
      (truncTech_profit_nonneg (hreg.techReg j) hM p)
  simp only [truncWealth]; linarith

/-- **Truncated demand:** preference-maximal bundles in the truncated budget set. -/
noncomputable def truncDemand (M : ℝ) (p : Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  Optimization.argmaxRel (E.pref a) (budgetSetAt p (E.truncWealth M p a))

/-- Truncated demand is contained in the truncated budget set. -/
lemma truncDemand_subset_budget {M : ℝ} {p : Fin L → ℝ} {a : E.Agents} {x : Fin L → ℝ}
    (hx : x ∈ E.truncDemand M p a) : x ∈ budgetSetAt p (E.truncWealth M p a) := hx.1

/-- Truncated demand is convex (convex preference over a convex budget set). -/
lemma truncDemand_convex (hreg : RegularProductionEconomy E) (M : ℝ) (p : Fin L → ℝ)
    (a : E.Agents) : Convex ℝ (E.truncDemand M p a) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hxS, hxmax⟩ := hx
  obtain ⟨hyS, hymax⟩ := hy
  have hcombS : s • x + t • y ∈ budgetSetAt p (E.truncWealth M p a) :=
    budgetSetAt_convex p _ hxS hyS hs ht hst
  refine ⟨hcombS, fun z hz => ?_⟩
  have hx_upper : x ∈ (E.pref a).upperContour x := (E.pref a).le_refl x
  have hy_upper : y ∈ (E.pref a).upperContour x := hymax x hxS
  have hcomb_le_x : (E.pref a).le (s • x + t • y) x :=
    (hreg.toRegularEconomy.convex a).convex_upper x hx_upper hy_upper hs ht hst
  exact (E.pref a).le_trans _ _ _ hcomb_le_x (hxmax z hz)

/-- Truncated demand is nonempty at strictly positive prices. -/
lemma truncDemand_nonempty (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) (a : E.Agents) : (E.truncDemand M p a).Nonempty := by
  obtain ⟨C, hCval⟩ := (Econlib.Preferences.continuousPref_iff_exists (E.pref a)).mp
    (hreg.toRegularEconomy.contPref a)
  obtain ⟨u, hrep, hcont⟩ := C.exists_continuous_utility_representation
  rw [hCval] at hrep
  have hcompact : IsCompact (budgetSetAt p (E.truncWealth M p a)) :=
    isCompact_budgetSetAt_of_pos_prices hp _
  have hne : (budgetSetAt p (E.truncWealth M p a)).Nonempty :=
    ⟨0, E.zero_mem_budgetK hreg hM (fun l => (hp l).le) a⟩
  rw [show E.truncDemand M p a
        = Optimization.argmaxRel (E.pref a) (budgetSetAt p (E.truncWealth M p a)) from rfl,
      ← Optimization.argmax_eq_argmaxRel_of_represents hrep]
  exact Optimization.argmax_nonempty hcompact hne hcont.continuousOn

/-- Truncated demand has a closed graph over the ε-truncated simplex (Berge + compact values). -/
lemma truncDemand_closedGraph_subtype (hreg : RegularProductionEconomy E) {ε : ℝ} (hε_pos : 0 < ε)
    {M : ℝ} (hM : 0 ≤ M) (a : E.Agents) :
    IsClosedGraph (fun pp : ↥(truncatedSimplex ε L) => E.truncDemand M pp.1 a) := by
  obtain ⟨C, hCval⟩ := (Econlib.Preferences.continuousPref_iff_exists (E.pref a)).mp
    (hreg.toRegularEconomy.contPref a)
  obtain ⟨u, hrep, hu_cont⟩ := C.exists_continuous_utility_representation
  rw [hCval] at hrep
  have hpos : ∀ pp : ↥(truncatedSimplex ε L), ∀ l, 0 < pp.1 l :=
    fun pp l => truncatedSimplex_pos_prices pp.2 hε_pos l
  set Φ : ↥(truncatedSimplex ε L) → Set (Fin L → ℝ) :=
    fun pp => budgetSetAt pp.1 (E.truncWealth M pp.1 a) with hΦ_def
  have hΦ_compact : ∀ pp, IsCompact (Φ pp) :=
    fun pp => isCompact_budgetSetAt_of_pos_prices (hpos pp) _
  have hwcont : Continuous (fun p => E.truncWealth M p a) := E.truncWealth_continuous hreg hM a
  have hΦ_uhc : UpperHemicontinuous Φ := by
    rw [upperHemicontinuous_iff]
    intro pp
    have hAt : UpperHemicontinuousAt
        (fun p : Fin L → ℝ => budgetSetAt p (E.truncWealth M p a)) pp.1 :=
      budgetSetAt_upperHemicontinuousAt (fun p => E.truncWealth M p a) hwcont (E.endow a)
        (fun p => E.endow_mem_budgetK hreg hM p a) (hΦ_compact pp)
    exact hAt.comp (continuous_subtype_val.continuousAt)
  -- LHC witness: `0 < pp.1 ⬝ᵥ endow a ≤ truncWealth M pp.1 a`, so `0` is strictly cheaper.
  have he_nn : ∀ l, 0 ≤ E.endow a l := fun l => E.endow_mem a l
  have he_ne : E.endow a ≠ 0 := hreg.toRegularEconomy.endow_ne a
  obtain ⟨l₀, hl₀⟩ : ∃ l, 0 < E.endow a l := by
    by_contra h; push Not at h
    exact he_ne (funext fun l => le_antisymm (h l) (he_nn l))
  have hΦ_lhc : LowerHemicontinuous Φ := by
    intro pp
    have hwealth_pos : 0 < pp.1 ⬝ᵥ E.endow a := by
      have hterm : ∀ l ∈ Finset.univ, 0 ≤ pp.1 l * E.endow a l :=
        fun l _ => mul_nonneg (hpos pp l).le (he_nn l)
      calc (0 : ℝ) < pp.1 l₀ * E.endow a l₀ := mul_pos (hpos pp l₀) hl₀
        _ ≤ ∑ l, pp.1 l * E.endow a l := Finset.single_le_sum hterm (Finset.mem_univ l₀)
        _ = pp.1 ⬝ᵥ E.endow a := rfl
    have hcheap : pp.1 ⬝ᵥ (0 : Fin L → ℝ) < E.truncWealth M pp.1 a := by
      have hendow_le_wealth : pp.1 ⬝ᵥ E.endow a ≤ E.truncWealth M pp.1 a :=
        (E.endow_mem_budgetK hreg hM pp.1 a).2
      simpa using lt_of_lt_of_le hwealth_pos hendow_le_wealth
    have hAt : LowerHemicontinuousAt
        (fun p : Fin L → ℝ => budgetSetAt p (E.truncWealth M p a)) pp.1 :=
      budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint (fun p => E.truncWealth M p a) hwcont
        ⟨0, fun l => le_refl 0, hcheap⟩
    exact hAt.comp continuous_subtype_val.continuousAt
  have hΦ_nonempty : ∀ pp, (Φ pp).Nonempty :=
    fun pp => ⟨E.endow a, E.endow_mem_budgetK hreg hM pp.1 a⟩
  have hf_cont : Continuous (fun q : ↥(truncatedSimplex ε L) × (Fin L → ℝ) => u q.2) :=
    hu_cont.comp continuous_snd
  have huhc :
      UpperHemicontinuous (fun pp : ↥(truncatedSimplex ε L) =>
        Optimization.argmax u (Φ pp)) :=
    Optimization.argmax_upperHemicontinuous hf_cont hΦ_uhc hΦ_lhc hΦ_compact hΦ_nonempty
  have hdemand_eq : (fun pp : ↥(truncatedSimplex ε L) => E.truncDemand M pp.1 a) =
      fun pp => Optimization.argmax u (Φ pp) := by
    funext pp
    rw [show E.truncDemand M pp.1 a
          = Optimization.argmaxRel (E.pref a) (budgetSetAt pp.1 (E.truncWealth M pp.1 a)) from rfl,
      ← Optimization.argmax_eq_argmaxRel_of_represents hrep]
  rw [hdemand_eq]
  refine huhc.isClosedGraph (fun pp => ?_)
  exact (Optimization.argmax_compact (hΦ_compact pp) hu_cont.continuousOn).isClosed

/-! ## Continuity and bounds for the fixed point -/

/-- Aggregate excess demand with production is jointly continuous in `(consumption, plan)`. -/
lemma continuous_aggregateExcess_prod [Finite E.Agents] :
    Continuous (fun xy : (E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ) =>
      E.aggregateExcess xy.1 xy.2) := by
  have heq : (fun xy : (E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ) =>
      E.aggregateExcess xy.1 xy.2)
      = fun xy => E.toEconomy.aggregateExcess xy.1 - (fun l => ∑ j, xy.2 j l) := by
    funext xy; rw [E.aggregateExcess_eq]
  rw [heq]
  refine Continuous.sub (E.toEconomy.continuous_aggregateExcess.comp continuous_fst) ?_
  refine continuous_pi fun l => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_apply l).comp ((continuous_apply j).comp continuous_snd)

/-- On the price simplex, truncated profit is at most `M`. -/
lemma truncTech_profit_le_radius {T : Technology L} (hT : RegularTechnology T) {M : ℝ} (hM : 0 ≤ M)
    {p : Fin L → ℝ} (hp : p ∈ priceSimplex L) : (truncTech T M).profit p ≤ M := by
  obtain ⟨y, hy⟩ := truncTech_supply_nonempty hT hM p
  rw [(truncTech T M).profit_eq_dotProduct_of_mem_supply hy]
  have hyM : ‖y‖ ≤ M := by
    have := hy.1.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hcoord : ∀ l, y l ≤ M := fun l =>
    le_trans (le_trans (le_abs_self (y l)) (Real.norm_eq_abs (y l) ▸ norm_le_pi_norm y l)) hyM
  have hsum := hp.2
  have hnn := fun l => hp.1 l
  calc p ⬝ᵥ y = ∑ l, p l * y l := by simp [dotProduct]
    _ ≤ ∑ l, p l * M := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hcoord l) (hnn l)
    _ = (∑ l, p l) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hsum, one_mul]

/-- Uniform upper bound on truncated wealth over the price simplex:
`truncWealth M p a ≤ ⨆ endow a + (∑ⱼ share)·M`. -/
noncomputable def truncWealthBound (M : ℝ) (a : E.Agents) : ℝ :=
  (⨆ l, E.endow a l) + (∑ j, E.share a j) * M

/-- Truncated wealth at a truncated-simplex price is bounded by `truncWealthBound`. -/
lemma truncWealth_le_bound (hreg : RegularProductionEconomy E) {M : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    {p : Fin L → ℝ} (hp : p ∈ truncatedSimplex ε L) (a : E.Agents) :
    E.truncWealth M p a ≤ E.truncWealthBound M a := by
  have hendow : p ⬝ᵥ E.endow a ≤ ⨆ l, E.endow a l := E.toEconomy.wealth_le_iSup_endow hL hp a
  have hprofit : ∀ j, (truncTech (E.tech j) M).profit p ≤ M :=
    fun j => truncTech_profit_le_radius (hreg.techReg j) hM (truncatedSimplex_subset hp)
  have hsum_le : ∑ j, E.share a j * (truncTech (E.tech j) M).profit p ≤ (∑ j, E.share a j) * M := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hprofit j) (E.share_nonneg a j)
  simp only [truncWealth, truncWealthBound]; linarith

/-- `truncWealthBound` is nonneg when `M ≥ 0`. -/
lemma truncWealthBound_nonneg {M : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (a : E.Agents) : 0 ≤ E.truncWealthBound M a := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hbdd : BddAbove (Set.range fun l => E.endow a l) := Finite.bddAbove_range _
  have hendow_nn : 0 ≤ ⨆ l, E.endow a l :=
    le_trans (E.endow_mem a ⟨0, hL⟩) (le_ciSup hbdd ⟨0, hL⟩)
  have hshare_nn : 0 ≤ (∑ j, E.share a j) * M :=
    mul_nonneg (Finset.sum_nonneg fun j _ => E.share_nonneg a j) hM
  simp only [truncWealthBound]; linarith

/-- Every truncated-demand bundle at a truncated-simplex price lies in
`[0, truncWealthBound/ε]^L`. -/
lemma truncDemand_subset_box [Finite E.Agents] (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {M : ℝ} (hM : 0 ≤ M) {p : Fin L → ℝ} (hp : p ∈ truncatedSimplex ε L) (hε_pos : 0 < ε)
    (a : E.Agents) :
    E.truncDemand M p a ⊆
      Set.pi Set.univ (fun _ : Fin L => Set.Icc (0 : ℝ) (E.truncWealthBound M a / ε)) := by
  have hp_pos : ∀ l, 0 < p l := fun l => truncatedSimplex_pos_prices hp hε_pos l
  intro x hx l _
  have hx_bud : x ∈ budgetSetAt p (E.truncWealth M p a) := E.truncDemand_subset_budget hx
  refine ⟨hx_bud.1 l, ?_⟩
  have hcoord : x l ≤ (E.truncWealth M p a) / p l := budgetSetAt_coord_bound hp_pos x hx_bud l
  have hw : E.truncWealth M p a ≤ E.truncWealthBound M a := E.truncWealth_le_bound hreg hM hL hp a
  have hwb_nn : 0 ≤ E.truncWealthBound M a := E.truncWealthBound_nonneg hM hL a
  calc x l ≤ (E.truncWealth M p a) / p l := hcoord
    _ ≤ (E.truncWealthBound M a) / p l := by gcongr; exact (hp_pos l).le
    _ ≤ (E.truncWealthBound M a) / ε := div_le_div_of_nonneg_left hwb_nn hε_pos (hp.2 l)

/-! ## Truncated Walras's law -/

/-- The aggregate of each agent's spending net of truncated wealth equals the value of aggregate
excess consumption minus total truncated profit (truncated analog of `aggregate_net_spending`). -/
lemma aggregate_net_spending_trunc (M : ℝ) (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)) :
    (∑ a, (p ⬝ᵥ x a - E.truncWealth M p a))
      = p ⬝ᵥ E.toEconomy.aggregateExcess x - ∑ j, (truncTech (E.tech j) M).profit p := by
  classical
  have hsplit : ∀ a, p ⬝ᵥ x a - E.truncWealth M p a
      = (p ⬝ᵥ x a - p ⬝ᵥ E.endow a)
        - ∑ j, E.share a j * (truncTech (E.tech j) M).profit p := by
    intro a; simp only [truncWealth]; ring
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_sub_distrib,
    ← E.toEconomy.dotProduct_aggregateExcess]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, E.share_sum j, one_mul]

/-- **Truncated Walras's law.** If every agent optimizes over its truncated budget set and every
firm supplies against the truncated technology, then `p ⬝ᵥ aggregateExcess x y = 0`. -/
lemma walras_law_trunc (hreg : RegularProductionEconomy E) {M : ℝ} {p : Fin L → ℝ}
    {x : E.Agents → (Fin L → ℝ)} {y : E.Firms → (Fin L → ℝ)}
    (hx : ∀ a, x a ∈ E.truncDemand M p a) (hy : ∀ j, y j ∈ (truncTech (E.tech j) M).supply p) :
    p ⬝ᵥ E.aggregateExcess x y = 0 := by
  classical
  have hbind : ∀ a, p ⬝ᵥ x a = E.truncWealth M p a :=
    fun a => budgetSetAt_binds (hreg.toRegularEconomy.locallyNonsatiated a) (hx a)
  have hprofit : ∀ j, (truncTech (E.tech j) M).profit p = p ⬝ᵥ y j :=
    fun j => (truncTech (E.tech j) M).profit_eq_dotProduct_of_mem_supply (hy j)
  have hAgg : p ⬝ᵥ E.toEconomy.aggregateExcess x = ∑ j, (truncTech (E.tech j) M).profit p := by
    have hzero : (∑ a, (p ⬝ᵥ x a - E.truncWealth M p a)) = 0 := by
      simp_rw [hbind, sub_self, Finset.sum_const_zero]
    have hns := E.aggregate_net_spending_trunc M p x
    rw [hzero] at hns; linarith
  have hPlan : p ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, (truncTech (E.tech j) M).profit p := by
    have hsum : p ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, p ⬝ᵥ y j := by
      simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hsum]; exact Finset.sum_congr rfl fun j _ => (hprofit j).symm
  rw [E.aggregateExcess_eq, dotProduct_sub, hAgg, hPlan, sub_self]

/-! ## Truncation-not-binding recovery -/

/-- **Interior maximizers recover true supply.** If `y` maximizes `p ⬝ᵥ ·` over `Yⱼ ∩ ball M` and
`‖y‖ < M`, then `y` maximizes over all of `Yⱼ`: Any `z ∈ Yⱼ` with `p ⬝ᵥ z > p ⬝ᵥ y` yields, by
convexity, a nearby interior point with strictly higher value, contradicting truncated
optimality. -/
lemma mem_supply_of_mem_truncSupply_of_interior {T : Technology L} (hconv : Convex ℝ T.Y) {M : ℝ}
    {p y : Fin L → ℝ} (hy : y ∈ (truncTech T M).supply p) (hyint : ‖y‖ < M) :
    y ∈ T.supply p := by
  obtain ⟨⟨hyY, hyball⟩, hymax⟩ := hy
  refine ⟨hyY, fun z hz => ?_⟩
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_le] at hlt
  set f : ℝ → Fin L → ℝ := fun t => (1 - t) • y + t • z with hf_def
  have hf_cont : Continuous f :=
    (continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const)
  have hf0 : f 0 = y := by simp [hf_def]
  have hfY : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → f t ∈ T.Y := fun t ht0 ht1 =>
    hconv hyY hz (by linarith) ht0 (by ring)
  have hval : ∀ t : ℝ, p ⬝ᵥ f t = (1 - t) * (p ⬝ᵥ y) + t * (p ⬝ᵥ z) := fun t => by
    simp only [hf_def, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hnorm_ev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), ‖f t‖ < M ∧ t ≤ 1 := by
    have hnball : ∀ᶠ t in nhds (0:ℝ), ‖f t‖ < M := by
      have hc : Continuous (fun t => ‖f t‖) := continuous_norm.comp hf_cont
      have : ‖f 0‖ < M := by rw [hf0]; exact hyint
      exact (hc.tendsto 0).eventually (isOpen_Iio.mem_nhds this)
    have hle1 : ∀ᶠ t in nhds (0:ℝ), t ≤ 1 := eventually_le_nhds (by norm_num)
    exact ((hnball.and hle1).filter_mono nhdsWithin_le_nhds)
  obtain ⟨t, ⟨htnorm, ht1⟩, htpos⟩ :=
    ((hnorm_ev.and self_mem_nhdsWithin).exists)
  have hft_mem : f t ∈ (truncTech T M).Y :=
    ⟨hfY t htpos.le ht1, by rw [Metric.mem_closedBall, dist_zero_right]; exact htnorm.le⟩
  have hft_val : p ⬝ᵥ y < p ⬝ᵥ f t := by
    rw [hval]; nlinarith [hlt, htpos]
  exact absurd (hymax hft_mem) (not_le.mpr hft_val)

/-- **A-priori bound on attainable production profiles** (Arrow and Debreu 1954). There exists `R`
such that every attainable profile (each `y j ∈ Yⱼ`, aggregate net output `≥ -ē`) satisfies
`‖y j‖ ≤ R` for all `j`. -/
lemma exists_attainable_profile_bound [Finite E.Agents] (hreg : RegularProductionEconomy E) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : E.Firms → (Fin L → ℝ), (∀ j, y j ∈ (E.tech j).Y) →
      (∀ l, -(∑ a, E.endow a l) ≤ ∑ j, y j l) →
      ∀ j, ‖y j‖ ≤ R := by
  classical
  set ē : Fin L → ℝ := fun l => ∑ a, E.endow a l with hē_def
  by_contra hcon
  push Not at hcon
  have hstep : ∀ n : ℕ, ∃ y : E.Firms → (Fin L → ℝ), (∀ j, y j ∈ (E.tech j).Y) ∧
      (∀ l, -(ē l) ≤ ∑ j, y j l) ∧ (n : ℝ) < ‖y‖ := by
    intro n
    obtain ⟨y, hyY, hyfloor, j, hj⟩ := hcon ((n : ℝ) + 1) (by positivity)
    have : (n : ℝ) + 1 < ‖y‖ := lt_of_lt_of_le hj (norm_le_pi_norm y j)
    exact ⟨y, hyY, hyfloor, by linarith⟩
  choose Y hYmem hYfloor hYgt using hstep
  have hY_pos : ∀ n, 0 < ‖Y n‖ := fun n => lt_of_le_of_lt (Nat.cast_nonneg n) (hYgt n)
  have hnorm_top : Filter.Tendsto (fun n => ‖Y n‖) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => (hYgt n).le) tendsto_natCast_atTop_atTop
  set d := fun n => (‖Y n‖)⁻¹ • Y n with hddef
  have hd_norm : ∀ n, ‖d n‖ = 1 := by
    intro n
    simp only [hddef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hY_pos n))]
    exact inv_mul_cancel₀ (ne_of_gt (hY_pos n))
  have hd_ball : ∀ n, d n ∈ Metric.closedBall (0 : E.Firms → Fin L → ℝ) 1 := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right, hd_norm n]
  obtain ⟨dstar, -, φ, hφ_mono, hφ_lim⟩ :=
    (isCompact_closedBall (0 : E.Firms → Fin L → ℝ) 1).tendsto_subseq hd_ball
  have hdstar_norm : ‖dstar‖ = 1 := by
    have hlim : Filter.Tendsto (fun n => ‖d (φ n)‖) Filter.atTop (nhds ‖dstar‖) :=
      (continuous_norm.tendsto dstar).comp hφ_lim
    simp only [hd_norm] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hsub_top : Filter.Tendsto (fun n => ‖Y (φ n)‖) Filter.atTop Filter.atTop :=
    hnorm_top.comp hφ_mono.tendsto_atTop
  have hdstar_firm : ∀ j, Filter.Tendsto (fun n => d (φ n) j) Filter.atTop (nhds (dstar j)) :=
    fun j => ((continuous_apply j).tendsto dstar).comp hφ_lim
  -- Each `dstar j` is a recession direction: `t • dstar j ∈ Yⱼ` for all `t ≥ 0`.
  have hray : ∀ j, ∀ t : ℝ, 0 ≤ t → t • dstar j ∈ (E.tech j).Y := by
    intro j t ht
    refine (hreg.techReg j).closed.mem_of_tendsto
      (((continuous_apply j).tendsto dstar).comp hφ_lim |>.const_smul t) ?_
    filter_upwards [hsub_top.eventually_ge_atTop t] with n hn
    simp only [Function.comp_apply]
    have hsmul_eq : t • d (φ n) j = (t / ‖Y (φ n)‖) • Y (φ n) j := by
      simp only [hddef, Pi.smul_apply, smul_smul]; rw [← div_eq_mul_inv]
    rw [hsmul_eq]
    refine (hreg.techReg j).convex.smul_mem_of_zero_mem (hreg.techReg j).inaction
      (hYmem (φ n) j) ⟨by positivity, ?_⟩
    rw [div_le_one (hY_pos (φ n))]; exact hn
  -- Aggregate `∑ⱼ dstar j ≥ 0`: the floor `-ē` washes out as `‖Y‖ → ∞`.
  have hdstar_agg_nonneg : ∀ l, 0 ≤ ∑ j, dstar j l := by
    intro l
    have hagg_lim : Filter.Tendsto (fun n => ∑ j, d (φ n) j l) Filter.atTop
        (nhds (∑ j, dstar j l)) := by
      refine tendsto_finset_sum _ fun j _ => ?_
      exact ((continuous_apply l).tendsto (dstar j)).comp (hdstar_firm j)
    have hlow : Filter.Tendsto (fun n => (‖Y (φ n)‖)⁻¹ * (-(ē l))) Filter.atTop (nhds 0) := by
      simpa using hsub_top.inv_tendsto_atTop.mul_const (-(ē l))
    refine le_of_tendsto_of_tendsto hlow hagg_lim ?_
    filter_upwards with n
    have hsum_eq : ∑ j, d (φ n) j l = (‖Y (φ n)‖)⁻¹ * ∑ j, Y (φ n) j l := by
      simp only [hddef, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [hsum_eq]
    exact mul_le_mul_of_nonneg_left
      (by linarith [hYfloor (φ n) l]) (le_of_lt (inv_pos.mpr (hY_pos (φ n))))
  have hdstar_zero : ∀ j, dstar j = 0 := hreg.no_aggregate_recession dstar hray hdstar_agg_nonneg
  have : dstar = 0 := funext hdstar_zero
  rw [this, norm_zero] at hdstar_norm
  norm_num at hdstar_norm

/-! ## The three existence theorems -/

/-- **Per-ε, per-radius fixed point with production.** For `0 < ε ≤ 1/L` and `0 ≤ M`, there exist
`p ∈ Δ_ε`, an allocation `x`, and plans `y` such that each consumer optimizes against truncated
wealth, each firm supplies against `truncTech M`, and `p` maximizes `q ↦ q ⬝ᵥ aggregateExcess x y`
over `Δ_ε`. -/
lemma exists_truncated_fixed_point_prod [Finite E.Agents]
    (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / (L : ℝ)) {M : ℝ} (hM : 0 ≤ M) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)) (y : E.Firms → (Fin L → ℝ)),
      p ∈ truncatedSimplex ε L ∧ (∀ a, x a ∈ E.truncDemand M p a) ∧
        (∀ j, y j ∈ (truncTech (E.tech j) M).supply p) ∧
        IsMaxOn (fun q => q ⬝ᵥ E.aggregateExcess x y) (truncatedSimplex ε L) p := by
  classical
  letI : Fintype E.Agents := Fintype.ofFinite E.Agents
  set consBox : Set (E.Agents → Fin L → ℝ) :=
    Set.pi Set.univ (fun a => Set.pi Set.univ
      (fun _ : Fin L => Set.Icc (0 : ℝ) (E.truncWealthBound M a / ε))) with hconsBox_def
  set prodBox : Set (E.Firms → Fin L → ℝ) :=
    Set.pi Set.univ (fun j => (truncTech (E.tech j) M).Y) with hprodBox_def
  have hconsBox_convex : Convex ℝ consBox :=
    convex_pi fun _ _ => convex_pi fun _ _ => convex_Icc _ _
  have hconsBox_compact : IsCompact consBox :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hconsBox_nonempty : consBox.Nonempty := by
    refine ⟨fun _ _ => 0, fun a _ => Set.mem_univ_pi.mpr fun _ => ⟨le_refl _, ?_⟩⟩
    exact div_nonneg (E.truncWealthBound_nonneg hM hL a) hε_pos.le
  have hprodBox_convex : Convex ℝ prodBox :=
    convex_pi fun j _ => truncTech_convex (hreg.techReg j) M
  have hprodBox_compact : IsCompact prodBox :=
    isCompact_univ_pi fun j => truncTech_compact (hreg.techReg j) M
  have hprodBox_nonempty : prodBox.Nonempty :=
    ⟨fun _ => 0, fun j _ => truncTech_zero_mem (hreg.techReg j) hM⟩
  set S : Set ((Fin L → ℝ) × ((E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ))) :=
    truncatedSimplex ε L ×ˢ (consBox ×ˢ prodBox) with hS_def
  have hS_convex : Convex ℝ S :=
    truncatedSimplex_convex.prod (hconsBox_convex.prod hprodBox_convex)
  have hS_compact : IsCompact S :=
    truncatedSimplex_compact.prod (hconsBox_compact.prod hprodBox_compact)
  have hS_nonempty : S.Nonempty :=
    (truncatedSimplex_nonempty hL hε_le).prod (hconsBox_nonempty.prod hprodBox_nonempty)
  have hdemand_box : ∀ p ∈ truncatedSimplex ε L, ∀ (x : E.Agents → Fin L → ℝ),
      (∀ a, x a ∈ E.truncDemand M p a) → x ∈ consBox := by
    intro p hp x hx
    exact Set.mem_univ_pi.mpr fun a => E.truncDemand_subset_box hreg hL hM hp hε_pos a (hx a)
  have hsupply_box : ∀ p (y : E.Firms → Fin L → ℝ),
      (∀ j, y j ∈ (truncTech (E.tech j) M).supply p) → y ∈ prodBox := by
    intro p y hy
    exact Set.mem_univ_pi.mpr fun j => (hy j).1
  set Ψ : ↥S → Set ((Fin L → ℝ) × ((E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ))) :=
    fun z => maxDotTruncated ε (E.aggregateExcess z.1.2.1 z.1.2.2) ×ˢ
      (Set.pi Set.univ (fun a => E.truncDemand M z.1.1 a) ×ˢ
        Set.pi Set.univ (fun j => (truncTech (E.tech j) M).supply z.1.1)) with hΨ_def
  have hz_price : ∀ z : ↥S, z.1.1 ∈ truncatedSimplex ε L := fun z => z.2.1
  set Θ := ↥(truncatedSimplex ε L)
  have hToΘ_cont : Continuous (fun z : ↥S => (⟨z.1.1, hz_price z⟩ : Θ)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hpos_price : ∀ z : ↥S, ∀ l, 0 < z.1.1 l :=
    fun z l => truncatedSimplex_pos_prices (hz_price z) hε_pos l
  have hΨ_sub : ∀ z, Ψ z ⊆ S := by
    rintro z ⟨q, x, y⟩ ⟨hq, hx, hy⟩
    refine ⟨maxDotTruncated_subset hq, ?_, ?_⟩
    · exact hdemand_box z.1.1 (hz_price z) x (fun a => (Set.mem_univ_pi.mp hx) a)
    · exact hsupply_box z.1.1 y (fun j => (Set.mem_univ_pi.mp hy) j)
  have hΨ_convex : ∀ z, Convex ℝ (Ψ z) := fun z =>
    (maxDotTruncated_convex _).prod
      ((convex_pi fun a _ => E.truncDemand_convex hreg M z.1.1 a).prod
        (convex_pi fun j _ => truncTech_supply_convex (hreg.techReg j) M z.1.1))
  have hΨ_nonempty : ∀ z, (Ψ z).Nonempty := fun z =>
    (maxDotTruncated_nonempty hL hε_le _).prod
      ((Set.univ_pi_nonempty_iff.mpr fun a => E.truncDemand_nonempty hreg hM (hpos_price z) a).prod
        (Set.univ_pi_nonempty_iff.mpr fun j =>
          truncTech_supply_nonempty (hreg.techReg j) hM z.1.1))
  have hΨ_cg : IsClosedGraph Ψ := by
    set W := ↥S × ((Fin L → ℝ) × ((E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ))) with hW_def
    have cont_q : Continuous (fun w : W => w.2.1) := continuous_fst.comp continuous_snd
    have cont_excess : Continuous (fun w : W =>
        E.aggregateExcess w.1.1.2.1 w.1.1.2.2) := by
      have hcons : Continuous (fun w : W => w.1.1.2.1) :=
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).comp continuous_fst
      have hplan : Continuous (fun w : W => w.1.1.2.2) :=
        (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).comp continuous_fst
      exact E.continuous_aggregateExcess_prod.comp (hcons.prodMk hplan)
    have hA1 : IsClosed {w : W | w.2.1 ∈ truncatedSimplex ε L} :=
      truncatedSimplex_closed.preimage cont_q
    have hA2 : IsClosed {w : W |
        IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2.1 w.1.1.2.2)
          (truncatedSimplex ε L) w.2.1} := by
      have heq : {w : W |
          IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2.1 w.1.1.2.2)
            (truncatedSimplex ε L) w.2.1} =
          ⋂ r ∈ truncatedSimplex ε L,
            {w : W | r ⬝ᵥ E.aggregateExcess w.1.1.2.1 w.1.1.2.2 ≤
              w.2.1 ⬝ᵥ E.aggregateExcess w.1.1.2.1 w.1.1.2.2} := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_iInter, isMaxOn_iff]
      rw [heq]
      refine isClosed_biInter fun r _ => isClosed_le ?_ ?_
      · exact (continuous_const.dotProduct cont_excess)
      · exact cont_q.dotProduct cont_excess
    have hBset : IsClosed {w : W | ∀ a, w.2.2.1 a ∈ E.truncDemand M w.1.1.1 a} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun a => ?_
      have hcg := E.truncDemand_closedGraph_subtype hreg hε_pos hM a
      have hg : Continuous (fun w : W =>
          ((⟨w.1.1.1, hz_price w.1⟩ : Θ), w.2.2.1 a)) :=
        ((hToΘ_cont.comp continuous_fst).prodMk
          (((continuous_apply a).comp (continuous_fst.comp continuous_snd)).comp continuous_snd))
      exact hcg.preimage hg
    have hCset : IsClosed {w : W | ∀ j, w.2.2.2 j ∈ (truncTech (E.tech j) M).supply w.1.1.1} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun j => ?_
      have hcg : IsClosedGraph (fun p : Fin L → ℝ => (truncTech (E.tech j) M).supply p) :=
        (truncTech_supply_uhc (hreg.techReg j) hM).isClosedGraph
          (fun p => (truncTech_supply_compact (hreg.techReg j) M p).isClosed)
      have hg : Continuous (fun w : W =>
          (w.1.1.1, w.2.2.2 j)) :=
        (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          (((continuous_apply j).comp
            (continuous_snd.comp continuous_snd)).comp continuous_snd)
      exact hcg.preimage hg
    have hgraph_eq :
        {w : ↥S × ((Fin L → ℝ) × ((E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ))) |
          w.2 ∈ Ψ w.1} =
        ({w | w.2.1 ∈ truncatedSimplex ε L} ∩
          {w | IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2.1 w.1.1.2.2)
            (truncatedSimplex ε L) w.2.1}) ∩
        ({w | ∀ a, w.2.2.1 a ∈ E.truncDemand M w.1.1.1 a} ∩
          {w | ∀ j, w.2.2.2 j ∈ (truncTech (E.tech j) M).supply w.1.1.1}) := by
      ext w
      simp only [hΨ_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, maxDotTruncated,
        Set.mem_univ_pi, and_assoc]
    rw [show IsClosedGraph Ψ =
        IsClosed {w : ↥S × ((Fin L → ℝ) × ((E.Agents → Fin L → ℝ) × (E.Firms → Fin L → ℝ))) |
          w.2 ∈ Ψ w.1} from rfl,
      hgraph_eq]
    exact ((hA1.inter hA2).inter (hBset.inter hCset))
  obtain ⟨z, hz⟩ := kakutaniFixedPoint S hS_convex hS_compact hS_nonempty Ψ hΨ_cg
    (fun z => ⟨hΨ_sub z, hΨ_convex z, hΨ_nonempty z⟩)
  obtain ⟨hz_max, hz_dem, hz_sup⟩ := hz
  refine ⟨z.1.1, z.1.2.1, z.1.2.2, hz_price z, fun a => ?_, fun j => ?_, hz_max.2⟩
  · exact (Set.mem_univ_pi.mp hz_dem) a
  · exact (Set.mem_univ_pi.mp hz_sup) j

/-- **Quasi-equilibrium ⇒ Walrasian, under production irreducibility** (McKenzie 1959).
`IrreducibleProd E` rules out any zero-augmented-wealth agent, giving `0 < E.wealth p a` for all
`a`, after which quasi-optimality upgrades to full demand optimality via the cheaper-point `z = 0`.
The improving coalition is credited its share of the production change `yf - y` against the current
profit-maximizing plan `y`; that change is valued nonpositively at `p`, so the zero-wealth
contradiction closes at any returns to scale. -/
lemma quasi_to_walrasian_prod [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hirr : IrreducibleProd E)
    {p : Fin L → ℝ} {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ}
    (hp_mem : p ∈ priceSimplex L)
    (hbud : ∀ a, x a ∈ E.budgetSet p a)
    (hbind : ∀ a, p ⬝ᵥ x a = E.wealth p a)
    (hIR : ∀ a, x a ≽[E.pref a] E.endow a)
    (hsupply : ∀ j, y j ∈ (E.tech j).supply p)
    (hquasi : ∀ a z, (∀ l, 0 ≤ z l) → p ⬝ᵥ z < E.wealth p a → ¬ (z ≻[E.pref a] x a))
    (hagg : ∃ a, 0 < E.wealth p a) :
    (∀ l, 0 < p l) ∧ (∀ a, x a ∈ E.consumerDemand p a) := by
  classical
  letI : Fintype E.Agents := Fintype.ofFinite _
  have hp_nn : ∀ l, 0 ≤ p l := fun l => hp_mem.1 l
  have hx_nn : ∀ a l, 0 ≤ x a l := fun a => (hbud a).1
  have hendow_nn : ∀ a, 0 ≤ p ⬝ᵥ E.endow a := fun a =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hp_nn l) (E.endow_mem a l)
  have hprofit_nn : ∀ j, 0 ≤ (E.tech j).profit p := fun j => by
    have hinaction : p ⬝ᵥ (0 : Fin L → ℝ) ≤ (E.tech j).profit p :=
      (E.tech j).dotProduct_le_profit_of_mem_supply (hreg.techReg j).inaction (hsupply j)
    simpa using hinaction
  have hshareprofit_nn : ∀ a, 0 ≤ ∑ j, E.share a j * (E.tech j).profit p := fun a =>
    Finset.sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a j) (hprofit_nn j)
  have hw_nn : ∀ a, 0 ≤ E.wealth p a := fun a => by
    simp only [wealth]; exact add_nonneg (hendow_nn a) (hshareprofit_nn a)
  -- Any strictly preferred nonneg bundle costs more than wealth (mix toward 0 on equal cost).
  have strict_exp : ∀ (a : E.Agents) (z : Fin L → ℝ), 0 < E.wealth p a → (∀ l, 0 ≤ z l) →
      (z ≻[E.pref a] (x a)) → E.wealth p a < p ⬝ᵥ z := by
    intro a z hwa hz_nn hz_pref
    by_contra hge; push Not at hge
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact hquasi a z hz_nn hlt hz_pref
    · set g : ℝ → Fin L → ℝ := fun s l => (1 - s) * z l with hg_def
      have hg_cont : Continuous g := by
        refine continuous_pi fun l => ?_
        simp only [hg_def]
        exact (continuous_const.sub continuous_id).mul continuous_const
      have hg0 : g 0 = z := by funext l; simp only [hg_def]; ring
      have h_open : IsOpen {w | w ≻[E.pref a] x a} :=
        (hreg.toRegularEconomy.contPref a).isOpen_strictUpperContour (x a)
      have h_mem0 : g 0 ∈ {w | w ≻[E.pref a] x a} := by rw [hg0]; exact hz_pref
      have h_pref_ev : ∀ᶠ s in nhds (0:ℝ), g s ∈ {w | w ≻[E.pref a] x a} :=
        (hg_cont.tendsto 0).eventually (h_open.mem_nhds h_mem0)
      have h_nn_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ l, 0 ≤ g s l := by
        have hs1 : ∀ᶠ s in nhds (0:ℝ), s ≤ 1 := eventually_le_nhds (by norm_num)
        refine ((hs1.filter_mono nhdsWithin_le_nhds).and
          (eventually_nhdsWithin_of_forall (fun s hs => hs))).mono ?_
        intro s ⟨hs_le1, _hs_pos⟩ l
        simp only [hg_def]
        exact mul_nonneg (by linarith) (hz_nn l)
      have h_cheap_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), p ⬝ᵥ g s < E.wealth p a := by
        refine eventually_nhdsWithin_of_forall fun s hs_pos => ?_
        have hs_pos' : 0 < s := hs_pos
        have hdot : p ⬝ᵥ g s = (1 - s) * (p ⬝ᵥ z) := by
          simp only [hg_def, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hdot, ← heq]
        nlinarith [hs_pos', hwa, heq]
      obtain ⟨s, hs_pref, hs_nn, hs_cheap⟩ :
          ∃ s, g s ∈ {w | w ≻[E.pref a] x a} ∧ (∀ l, 0 ≤ g s l) ∧ p ⬝ᵥ g s < E.wealth p a := by
        have hev := ((h_pref_ev.filter_mono nhdsWithin_le_nhds).and (h_nn_ev.and h_cheap_ev))
        obtain ⟨s, hs⟩ := hev.exists
        exact ⟨s, hs.1, hs.2.1, hs.2.2⟩
      exact hquasi a (g s) hs_nn hs_cheap hs_pref
  have wealth_pos : ∀ a, 0 < E.wealth p a := by
    by_contra h
    push Not at h
    obtain ⟨a_zero, ha_zero_le⟩ := h
    have ha_zero : E.wealth p a_zero = 0 := le_antisymm ha_zero_le (hw_nn a_zero)
    set T : Finset E.Agents := Finset.univ.filter (fun a => E.wealth p a = 0) with hT_def
    set S : Finset E.Agents := Finset.univ.filter (fun a => E.wealth p a ≠ 0) with hS_def
    have hT_ne : T.Nonempty := ⟨a_zero, by simp [hT_def, ha_zero]⟩
    have hS_ne : S.Nonempty := by
      obtain ⟨a_pos, ha_pos⟩ := hagg
      exact ⟨a_pos, by simp [hS_def, ne_of_gt ha_pos]⟩
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro a haS haT
      simp only [hS_def, Finset.mem_filter] at haS
      simp only [hT_def, Finset.mem_filter] at haT
      exact haS.2 haT.2
    -- Production irreducibility, applied to the current profit-maximizing plan `y`, hands `S` an
    -- improving consumption `yimp` together with a deviating production `yf`, crediting `S`'s share
    -- of the *increment* `yf - y`.
    obtain ⟨yimp, yf, hyf_mem, hy_improve, hy_resource⟩ :=
      hirr.improve x y hx_nn hIR (fun f => (hsupply f).1) S T hS_ne hT_ne hdisj
    have hS_wealth : ∀ i ∈ S, 0 < E.wealth p i := by
      intro i hi
      simp only [hS_def, Finset.mem_filter] at hi
      exact lt_of_le_of_ne (hw_nn i) (Ne.symm hi.2)
    have hexp : ∀ i ∈ S, E.wealth p i < p ⬝ᵥ yimp i := fun i hi =>
      strict_exp i (yimp i) (hS_wealth i hi) (hy_improve i hi).1 (hy_improve i hi).2
    have hsum_strict : (∑ i ∈ S, E.wealth p i) < ∑ i ∈ S, p ⬝ᵥ yimp i :=
      Finset.sum_lt_sum_of_nonempty hS_ne hexp
    -- The value of `S`'s share of the production change is nonpositive: each `yf f ∈ Y` earns no
    -- more than the profit-maximizing `y f` at prices `p`.
    have hΦ_nonpos :
        (∑ f, (∑ i ∈ S, E.share i f) * (p ⬝ᵥ yf f - p ⬝ᵥ y f)) ≤ 0 := by
      refine Finset.sum_nonpos fun f _ => ?_
      have hshare_nn : 0 ≤ ∑ i ∈ S, E.share i f :=
        Finset.sum_nonneg fun i _ => E.share_nonneg i f
      have hdev : p ⬝ᵥ yf f - p ⬝ᵥ y f ≤ 0 := by
        have hle : p ⬝ᵥ yf f ≤ (E.tech f).profit p :=
          (E.tech f).dotProduct_le_profit_of_mem_supply (hyf_mem f) (hsupply f)
        have heq : (E.tech f).profit p = p ⬝ᵥ y f :=
          (E.tech f).profit_eq_dotProduct_of_mem_supply (hsupply f)
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hshare_nn hdev
    -- Dotting the production resource inequality with `p`: the firm term collapses to the (signed)
    -- value of the production change.
    have hΦ_coord :
        (∑ l, p l * (∑ f, (∑ i ∈ S, E.share i f) * (yf f l - y f l)))
          = ∑ f, (∑ i ∈ S, E.share i f) * (p ⬝ᵥ yf f - p ⬝ᵥ y f) := by
      have hdot_diff : ∀ f, (∑ l, p l * (yf f l - y f l)) = p ⬝ᵥ yf f - p ⬝ᵥ y f :=
        fun f => by simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
      calc ∑ l, p l * (∑ f, (∑ i ∈ S, E.share i f) * (yf f l - y f l))
          = ∑ l, ∑ f, p l * ((∑ i ∈ S, E.share i f) * (yf f l - y f l)) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ f, ∑ l, p l * ((∑ i ∈ S, E.share i f) * (yf f l - y f l)) := Finset.sum_comm
        _ = ∑ f, (∑ i ∈ S, E.share i f) * (∑ l, p l * (yf f l - y f l)) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        _ = ∑ f, (∑ i ∈ S, E.share i f) * (p ⬝ᵥ yf f - p ⬝ᵥ y f) := by
            exact Finset.sum_congr rfl fun f _ => by rw [hdot_diff f]
    have h_dot_resource : (∑ i ∈ S, p ⬝ᵥ yimp i) ≤
        (∑ i ∈ S, p ⬝ᵥ x i) + (∑ j ∈ T, p ⬝ᵥ E.endow j)
          + ∑ f, (∑ i ∈ S, E.share i f) * (p ⬝ᵥ yf f - p ⬝ᵥ y f) := by
      have hLHS : (∑ i ∈ S, p ⬝ᵥ yimp i) = ∑ l, p l * (∑ i ∈ S, yimp i l) := by
        simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
      have hRHS : (∑ i ∈ S, p ⬝ᵥ x i) + (∑ j ∈ T, p ⬝ᵥ E.endow j)
            + ∑ f, (∑ i ∈ S, E.share i f) * (p ⬝ᵥ yf f - p ⬝ᵥ y f) =
          ∑ l, p l * ((∑ i ∈ S, x i l) + ∑ j ∈ T, E.endow j l
            + ∑ f, (∑ i ∈ S, E.share i f) * (yf f l - y f l)) := by
        have hx_comm : (∑ i ∈ S, p ⬝ᵥ x i) = ∑ l, p l * (∑ i ∈ S, x i l) := by
          simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
        have he_comm : (∑ j ∈ T, p ⬝ᵥ E.endow j) = ∑ l, p l * (∑ j ∈ T, E.endow j l) := by
          simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
        rw [hx_comm, he_comm, ← hΦ_coord, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      rw [hLHS, hRHS]
      refine Finset.sum_le_sum fun l _ => ?_
      exact mul_le_mul_of_nonneg_left (hy_resource l) (hp_nn l)
    have h_xS : (∑ i ∈ S, p ⬝ᵥ x i) = ∑ i ∈ S, E.wealth p i :=
      Finset.sum_congr rfl fun i _ => hbind i
    -- Donors in `T` have zero augmented wealth, hence zero endowment value.
    have h_eT : (∑ j ∈ T, p ⬝ᵥ E.endow j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [hT_def, Finset.mem_filter] at hj
      have hwj : p ⬝ᵥ E.endow j + ∑ k, E.share j k * (E.tech k).profit p = 0 := by
        have := hj.2; simpa only [wealth] using this
      linarith [hendow_nn j, hshareprofit_nn j]
    rw [h_xS, h_eT] at h_dot_resource
    linarith
  have hp_pos : ∀ l, 0 < p l := by
    by_contra h_neg; push Not at h_neg
    obtain ⟨l₀, hl₀⟩ := h_neg
    have hl₀_eq : p l₀ = 0 := le_antisymm hl₀ (hp_nn l₀)
    obtain ⟨a₀⟩ := hne
    have h_wealth_pos : 0 < E.wealth p a₀ := wealth_pos a₀
    have h_xstar_dot_pos : 0 < p ⬝ᵥ x a₀ := by rw [hbind a₀]; exact h_wealth_pos
    obtain ⟨l', hl'_price, hl'_alloc⟩ : ∃ l', 0 < p l' ∧ 0 < x a₀ l' := by
      by_contra h_none; push Not at h_none
      have h_dot_zero : p ⬝ᵥ x a₀ = 0 := by
        simp only [dotProduct]
        apply Finset.sum_eq_zero; intro l _
        rcases eq_or_lt_of_le (hp_nn l) with hp0 | hpl
        · rw [show p l = 0 from hp0.symm]; ring
        · rw [show x a₀ l = 0 from le_antisymm (h_none l hpl) (hx_nn a₀ l)]; ring
      linarith
    have hl₀_ne : l₀ ≠ l' := fun h => by rw [h] at hl₀_eq; linarith
    set y₀ : Fin L → ℝ := fun l => x a₀ l + (if l = l₀ then 1 else 0) with hy₀_def
    have hy₀_nn : ∀ l, 0 ≤ y₀ l := fun l => by
      simp only [hy₀_def]; split <;> linarith [hx_nn a₀ l]
    have h_le : x a₀ ≤ y₀ := fun l => by simp only [hy₀_def]; split <;> linarith
    have h_ne : x a₀ ≠ y₀ := fun heq => by
      have hcontra := congr_fun heq.symm l₀
      simp only [hy₀_def, if_true] at hcontra; linarith
    have h_y₀_pref : y₀ ≻[E.pref a₀] x a₀ := by
      -- The constant interior bundle `δ·𝟙` is cheaper than the (positive) augmented wealth, so the
      -- quasi-optimal `x a₀` weakly beats it; desirability then improves along `y₀`.
      set δ : ℝ := E.wealth p a₀ / 2 with hδ_def
      have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
      have hz_pos : ∀ l, 0 < (fun _ : Fin L => δ) l := fun _ => hδ_pos
      have hz_cheap : p ⬝ᵥ (fun _ : Fin L => δ) < E.wealth p a₀ := by
        have hsum : p ⬝ᵥ (fun _ : Fin L => δ) = δ := by
          simp only [dotProduct]
          rw [← Finset.sum_mul, hp_mem.2, one_mul]
        rw [hsum, hδ_def]; linarith
      have hx_ge_z : x a₀ ≽[E.pref a₀] (fun _ : Fin L => δ) := by
        by_contra hge
        have hle' : (fun _ : Fin L => δ) ≽[E.pref a₀] x a₀ :=
          ((E.pref a₀).le_total (fun _ : Fin L => δ) (x a₀)).resolve_right hge
        exact hquasi a₀ (fun _ : Fin L => δ) (fun _ => hδ_pos.le) hz_cheap ⟨hle', hge⟩
      exact (hreg.toRegularEconomy.desirable a₀).improve hz_pos hx_ge_z h_le h_ne
    have h_dot_y₀ : p ⬝ᵥ y₀ = p ⬝ᵥ x a₀ := by
      simp only [dotProduct, hy₀_def, mul_add]
      rw [Finset.sum_add_distrib]
      have hzero : ∑ l, p l * (if l = l₀ then (1:ℝ) else 0) = 0 := by
        rw [Finset.sum_eq_single l₀]
        · rw [if_pos rfl, hl₀_eq]; ring
        · intro l _ hl; rw [if_neg hl]; ring
        · intro h; exact absurd (Finset.mem_univ l₀) h
      rw [hzero, add_zero]
    set f : ℝ → Fin L → ℝ := fun t l => y₀ l - t * (if l = l' then 1 else 0) with hf_def
    have hf_cont : Continuous f := by
      refine continuous_pi fun l => ?_
      simp only [hf_def]
      exact continuous_const.sub (continuous_id.mul continuous_const)
    have hf0 : f 0 = y₀ := by funext l; simp only [hf_def]; ring
    have h_open : IsOpen {w | w ≻[E.pref a₀] x a₀} :=
      (hreg.toRegularEconomy.contPref a₀).isOpen_strictUpperContour (x a₀)
    have h_mem0 : f 0 ∈ {w | w ≻[E.pref a₀] x a₀} := by rw [hf0]; exact h_y₀_pref
    have h_pref_ev : ∀ᶠ t in nhds (0:ℝ), f t ∈ {w | w ≻[E.pref a₀] x a₀} :=
      (hf_cont.tendsto 0).eventually (h_open.mem_nhds h_mem0)
    have h_nn_ev : ∀ᶠ t in nhds (0:ℝ), ∀ l, 0 ≤ f t l := by
      have hy₀l' : 0 < y₀ l' := by
        simp only [hy₀_def]; rw [if_neg (Ne.symm hl₀_ne)]; simpa using hl'_alloc
      have h_l'_pos : ∀ᶠ t in nhds (0:ℝ), 0 < f t l' := by
        have hcont_l' : Continuous (fun t => f t l') := (continuous_apply l').comp hf_cont
        have : f 0 l' = y₀ l' := by rw [hf0]
        exact (hcont_l'.tendsto 0).eventually (by rw [this] at *; exact Ioi_mem_nhds hy₀l')
      filter_upwards [h_l'_pos] with t ht l
      by_cases hl : l = l'
      · subst hl; exact ht.le
      · simp only [hf_def, if_neg hl, mul_zero, sub_zero]; exact hy₀_nn l
    have h_cheap_ev : ∀ᶠ t in nhds (0:ℝ),
        p ⬝ᵥ f t = p ⬝ᵥ x a₀ - t * p l' := by
      filter_upwards with t
      simp only [hf_def, dotProduct]
      have hsplit : ∀ l, p l * (y₀ l - t * (if l = l' then (1:ℝ) else 0)) =
          p l * y₀ l - t * (if l = l' then p l else 0) := by
        intro l; split <;> ring
      simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [Finset.sum_ite_eq' Finset.univ l' (fun l => p l)]
      simp only [Finset.mem_univ, if_true]
      have hy₀dot : (∑ l, p l * y₀ l) = p ⬝ᵥ x a₀ := by
        rw [show (∑ l, p l * y₀ l) = p ⬝ᵥ y₀ from rfl, h_dot_y₀]
      rw [hy₀dot]; rfl
    obtain ⟨t, ht_pref, ht_nn, ht_cheap, ht_pos⟩ :
        ∃ t, f t ∈ {w | w ≻[E.pref a₀] x a₀} ∧ (∀ l, 0 ≤ f t l) ∧
          p ⬝ᵥ f t = p ⬝ᵥ x a₀ - t * p l' ∧ 0 < t := by
      have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
          (f t ∈ {w | w ≻[E.pref a₀] x a₀} ∧ (∀ l, 0 ≤ f t l) ∧
            p ⬝ᵥ f t = p ⬝ᵥ x a₀ - t * p l') ∧ t ∈ Set.Ioi (0:ℝ) := by
        refine (((h_pref_ev.and (h_nn_ev.and h_cheap_ev)).filter_mono
          nhdsWithin_le_nhds).and self_mem_nhdsWithin).mono ?_
        intro t ht; exact ⟨ht.1, ht.2⟩
      obtain ⟨t, ht⟩ := (hev.exists)
      exact ⟨t, ht.1.1, ht.1.2.1, ht.1.2.2, ht.2⟩
    have h_ft_cheap : p ⬝ᵥ f t < E.wealth p a₀ := by
      rw [ht_cheap, ← hbind a₀]
      linarith [mul_pos ht_pos hl'_price]
    exact hquasi a₀ (f t) ht_nn h_ft_cheap ht_pref
  have hquasi_ge : ∀ (a : E.Agents) (z : Fin L → ℝ), (∀ l, 0 ≤ z l) →
      p ⬝ᵥ z < E.wealth p a → (x a ≽[E.pref a] z) := by
    intro a z hz_nn hz_strict
    by_contra hge
    have hle : z ≽[E.pref a] x a := ((E.pref a).le_total z (x a)).resolve_right hge
    exact hquasi a z hz_nn hz_strict ⟨hle, hge⟩
  refine ⟨hp_pos, fun a => ?_⟩
  have hx_bud : x a ∈ E.budgetSet p a := ⟨fun l => hx_nn a l, le_of_eq (hbind a)⟩
  refine ⟨hx_bud, fun z hz => ?_⟩
  have hz_nn : ∀ l, 0 ≤ z l := hz.1
  have hz_le : p ⬝ᵥ z ≤ E.wealth p a := hz.2
  rcases lt_or_eq_of_le hz_le with hlt | heq_cost
  · exact hquasi_ge a z hz_nn hlt
  · -- `p ⬝ᵥ z = wealth`: approximate by `(1-s)z`, strictly cheaper for `s > 0`.
    have hwealth_lt : (0 : ℝ) < E.wealth p a := wealth_pos a
    set g : ℝ → Fin L → ℝ := fun s l => (1 - s) * z l with hg_def
    have hg_cont : Continuous g := by
      refine continuous_pi fun l => ?_
      simp only [hg_def]
      exact (continuous_const.sub continuous_id).mul continuous_const
    have hg0 : g 0 = z := by funext l; simp only [hg_def]; ring
    have h_upper_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0),
        g s ∈ {w : Fin L → ℝ | x a ≽[E.pref a] w} := by
      have h_nn_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ l, 0 ≤ g s l := by
        have hs1 : ∀ᶠ s in nhds (0:ℝ), s ≤ 1 := eventually_le_nhds (by norm_num)
        refine ((hs1.filter_mono nhdsWithin_le_nhds).and
          (eventually_nhdsWithin_of_forall (fun s hs => hs))).mono ?_
        intro s ⟨hs_le1, _hs_pos⟩ l
        simp only [hg_def]
        exact mul_nonneg (by linarith) (hz_nn l)
      have h_cheap_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), p ⬝ᵥ g s < E.wealth p a := by
        refine eventually_nhdsWithin_of_forall fun s hs_pos => ?_
        have hs_pos' : 0 < s := hs_pos
        have hdot : p ⬝ᵥ g s = (1 - s) * (p ⬝ᵥ z) := by
          simp only [hg_def, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hdot, heq_cost]
        nlinarith [hs_pos', hwealth_lt]
      filter_upwards [h_nn_ev, h_cheap_ev] with s hs_nn hs_cheap
      exact hquasi_ge a (g s) hs_nn hs_cheap
    have hg_tendsto : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds z) := by
      rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    have h_closed_lower : IsClosed {w : Fin L → ℝ | x a ≽[E.pref a] w} :=
      (hreg.toRegularEconomy.contPref a).closed_lower (x a)
    exact h_closed_lower.mem_of_tendsto hg_tendsto h_upper_ev

/-- **Existence of a quasi-equilibrium with production.** Under regularity and `0 < L`, there exist
simplex prices `p`, an individually-rational budget-binding allocation `x`, and profit-maximizing
plans `y` such that no nonneg bundle strictly cheaper than `wealth p a` is strictly preferred to
`x a`, and markets clear. -/
-- `_hne` kept for API symmetry with `exists_quasi_equilibrium`; not used in the proof body.
lemma exists_quasi_equilibrium_prod [Finite E.Agents] (_hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hL : 0 < L) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → Fin L → ℝ) (y : E.Firms → Fin L → ℝ),
      p ∈ priceSimplex L ∧
      (∀ a, x a ∈ E.budgetSet p a) ∧
      (∀ a, p ⬝ᵥ x a = E.wealth p a) ∧
      (∀ a, x a ≽[E.pref a] E.endow a) ∧
      (∀ j, y j ∈ (E.tech j).supply p) ∧
      (∀ a z, (∀ l, 0 ≤ z l) → p ⬝ᵥ z < E.wealth p a → ¬ (z ≻[E.pref a] x a)) ∧
      (∀ l, E.aggregateExcess x y l ≤ 0) ∧ p ⬝ᵥ E.aggregateExcess x y = 0 := by
  classical
  letI : DecidableEq E.Agents := Classical.decEq _
  obtain ⟨R, hR_pos, hR_bound⟩ := E.exists_attainable_profile_bound hreg
  set M : ℝ := R + 1 with hM_def
  have hM_nonneg : 0 ≤ M := by positivity
  have hM_pos : 0 < M := by positivity
  have hLR : (0:ℝ) < ↑L := Nat.cast_pos.mpr hL
  set εseq : ℕ → ℝ := fun k => 1 / ((↑(k + 2) : ℝ) * ↑L) with hεseq_def
  have hεk_pos : ∀ k : ℕ, 0 < εseq k := fun k => by simp only [hεseq_def]; positivity
  have hεk_le : ∀ k : ℕ, εseq k ≤ 1 / ↑L := by
    intro k
    simp only [hεseq_def]
    apply div_le_div_of_nonneg_left (by positivity) hLR
    exact le_mul_of_one_le_left hLR.le (by exact_mod_cast (show 1 ≤ k + 2 by omega))
  have hp_data : ∀ k, ∃ (pk : Fin L → ℝ) (xk : E.Agents → Fin L → ℝ) (yk : E.Firms → Fin L → ℝ),
      pk ∈ truncatedSimplex (εseq k) L ∧ (∀ a, xk a ∈ E.truncDemand M pk a) ∧
        (∀ j, yk j ∈ (truncTech (E.tech j) M).supply pk) ∧
        IsMaxOn (fun q => q ⬝ᵥ E.aggregateExcess xk yk) (truncatedSimplex (εseq k) L) pk :=
    fun (k : ℕ) =>
      E.exists_truncated_fixed_point_prod hreg hL (hεk_pos k) (hεk_le k) hM_nonneg
  choose p xall yall hp_trunc hxall_dem hyall_sup hpall_max using hp_data
  have hp_simplex : ∀ k, p k ∈ priceSimplex L := fun k => truncatedSimplex_subset (hp_trunc k)
  set zall : ℕ → Fin L → ℝ := fun k => E.aggregateExcess (xall k) (yall k) with hzall_def
  obtain ⟨pstar, hp_mem, φ, hφ_mono, hp_tendsto⟩ :=
    (isCompact_stdSimplex ℝ (ι := Fin L)).tendsto_subseq hp_simplex
  have hwalras : ∀ k, p k ⬝ᵥ zall k = 0 :=
    fun k => E.walras_law_trunc hreg (hxall_dem k) (hyall_sup k)
  have h_dot_le : ∀ (q : Fin L → ℝ), q ∈ priceSimplex L → (∀ l, 0 < q l) →
      ∀ᶠ k in Filter.atTop, q ⬝ᵥ zall (φ k) ≤ 0 := by
    intro q hq hq_pos
    obtain ⟨N, hN⟩ := interior_price_eventually_in_truncated hq hq_pos hL
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun k hk => hk⟩] with k hk
    have hφk_ge : N ≤ φ k := le_trans hk (hφ_mono.id_le k)
    have hq_trunc : q ∈ truncatedSimplex (εseq (φ k)) L := hN (φ k) hφk_ge
    have h_maxdot : q ⬝ᵥ zall (φ k) ≤ p (φ k) ⬝ᵥ zall (φ k) := (hpall_max (φ k)) hq_trunc
    have h_walras : p (φ k) ⬝ᵥ zall (φ k) = 0 := hwalras (φ k)
    linarith
  have hplan_bd : ∀ k j l, |yall k j l| ≤ M := by
    intro k j l
    have hball : yall k j ∈ Metric.closedBall (0 : Fin L → ℝ) M := (hyall_sup k j).1.2
    rw [Metric.mem_closedBall, dist_zero_right] at hball
    exact le_trans (Real.norm_eq_abs (yall k j l) ▸ norm_le_pi_norm (yall k j) l) hball
  set Etot : ℝ := ∑ l : Fin L, ∑ a, E.endow a l with hEtot_def
  have hagg_endow_nonneg : ∀ l, 0 ≤ ∑ a, E.endow a l :=
    fun l => Finset.sum_nonneg fun a _ => E.endow_mem a l
  have hEtot_nonneg : 0 ≤ Etot := Finset.sum_nonneg fun l _ => hagg_endow_nonneg l
  set PM : ℝ := (Fintype.card E.Firms : ℝ) * M with hPM_def
  have hPM_nonneg : 0 ≤ PM := by positivity
  have hplansum_bd : ∀ k l, |∑ j, yall k j l| ≤ PM := by
    intro k l
    calc |∑ j, yall k j l| ≤ ∑ j, |yall k j l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : E.Firms, M := Finset.sum_le_sum fun j _ => hplan_bd k j l
      _ = PM := by rw [Finset.sum_const, hPM_def]; simp [nsmul_eq_mul]
  set Cbound : ℝ := 2 * Etot + (↑L + 1) * PM with hCbound_def
  have hagg_alloc_le : ∀ᶠ k in Filter.atTop, ∀ l,
      ∑ a, xall (φ k) a l ≤ Cbound := by
    set q : Fin L → ℝ := fun _ => 1 / (↑L : ℝ) with hq_def
    have hq_pos : ∀ l, 0 < q l := fun _ => by simp only [hq_def]; positivity
    have hq_simplex : q ∈ priceSimplex L := by
      exact ⟨fun l => (hq_pos l).le, by simp [hq_def, Fintype.card_fin, ne_of_gt hLR]⟩
    filter_upwards [h_dot_le q hq_simplex hq_pos] with k hk l
    have h_sum_le : ∑ l', zall (φ k) l' ≤ 0 := by
      have hdot : q ⬝ᵥ zall (φ k) = (1 / ↑L) * ∑ l', zall (φ k) l' := by
        simp only [dotProduct, hq_def]; rw [Finset.mul_sum]
      nlinarith [div_pos one_pos hLR]
    have hz_lower : ∀ l', -((∑ a, E.endow a l') + PM)
        ≤ zall (φ k) l' := by
      intro l'
      have hagg_x_nonneg : 0 ≤ ∑ a, xall (φ k) a l' :=
        Finset.sum_nonneg fun a _ =>
          (E.truncDemand_subset_budget (hxall_dem (φ k) a)).1 l'
      have hplan_le : ∑ j, yall (φ k) j l' ≤ PM :=
        le_trans (le_abs_self _) (hplansum_bd (φ k) l')
      simp only [hzall_def, aggregateExcess]
      linarith
    have hz_l_le : zall (φ k) l ≤ Etot + (↑L) * PM := by
      have h_tail_ge :
          -(∑ l' ∈ Finset.univ.erase l,
              ((∑ a, E.endow a l') + PM)) ≤
            ∑ l' ∈ Finset.univ.erase l, zall (φ k) l' := by
        rw [neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
        exact Finset.sum_nonneg fun l' _ => by linarith [hz_lower l']
      have h_sub_le :
          ∑ l' ∈ Finset.univ.erase l,
              ((∑ a, E.endow a l') + PM) ≤ Etot + (↑L) * PM := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ l),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hsum_endow_le : ∑ l' ∈ Finset.univ.erase l,
            (∑ a, E.endow a l') ≤ Etot :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l Finset.univ)
            (fun l' _ _ => hagg_endow_nonneg l')
        have hPM_factor_le : ((L - 1 : ℕ) : ℝ) * PM ≤ (↑L) * PM :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le L 1) hPM_nonneg
        linarith
      have h_split := (Finset.add_sum_erase (f := zall (φ k)) _ (Finset.mem_univ l)).symm
      linarith
    have h_agg_eq : ∑ a, xall (φ k) a l =
        zall (φ k) l + (∑ a, E.endow a l)
          + ∑ j, yall (φ k) j l := by
      simp only [hzall_def, aggregateExcess]; ring
    have h_endow_l_le : (∑ a, E.endow a l) ≤ Etot :=
      Finset.single_le_sum (fun l' _ => hagg_endow_nonneg l') (Finset.mem_univ l)
    have h_plan_l_le : ∑ j, yall (φ k) j l ≤ PM :=
      le_trans (le_abs_self _) (hplansum_bd (φ k) l)
    rw [h_agg_eq, hCbound_def]; linarith
  have hCbound_nonneg : 0 ≤ Cbound := by rw [hCbound_def]; positivity
  set B : E.Agents → ℝ := fun _ => Cbound with hB_def
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hagg_alloc_le
  set consbox : Set (E.Agents → Fin L → ℝ) :=
    Set.pi Set.univ (fun a => Set.pi Set.univ (fun _ : Fin L => Set.Icc (0 : ℝ) (B a)))
    with hconsbox_def
  have hconsbox_compact : IsCompact consbox :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set xseq : ℕ → E.Agents → Fin L → ℝ := fun n => xall (φ (n + K₀)) with hxseq_def
  have hxseq_box : ∀ n, xseq n ∈ consbox := by
    intro n
    simp only [hconsbox_def, hxseq_def, Set.mem_univ_pi, Set.mem_Icc]
    intro a l
    refine ⟨(E.truncDemand_subset_budget (hxall_dem (φ (n + K₀)) a)).1 l, ?_⟩
    have hsingle_le : xall (φ (n + K₀)) a l ≤ ∑ a', xall (φ (n + K₀)) a' l :=
      Finset.single_le_sum
        (fun a' _ => (E.truncDemand_subset_budget (hxall_dem (φ (n + K₀)) a')).1 l)
        (Finset.mem_univ a)
    have hagg_le := hK₀ (n + K₀) (by omega) l
    rw [hB_def]; linarith
  obtain ⟨xstar, hxstar_mem, ψ, hψ_mono, hx_conv⟩ := hconsbox_compact.tendsto_subseq hxseq_box
  set prodbox : Set (E.Firms → Fin L → ℝ) :=
    Set.pi Set.univ (fun j => (truncTech (E.tech j) M).Y) with hprodbox_def
  have hprodbox_compact : IsCompact prodbox :=
    isCompact_univ_pi fun j => truncTech_compact (hreg.techReg j) M
  set yseq : ℕ → E.Firms → Fin L → ℝ := fun n => yall (φ (ψ n + K₀)) with hyseq_def
  have hyseq_box : ∀ n, yseq n ∈ prodbox := by
    intro n
    exact Set.mem_univ_pi.mpr fun j => (hyall_sup (φ (ψ n + K₀)) j).1
  obtain ⟨ystar, hystar_mem, ρ, hρ_mono, hy_conv⟩ := hprodbox_compact.tendsto_subseq hyseq_box
  set χ : ℕ → ℕ := fun n => φ (ψ (ρ n) + K₀) with hχ_def
  have hχ_mono : StrictMono χ := fun a b hab =>
    hφ_mono (Nat.add_lt_add_right (hψ_mono (hρ_mono hab)) K₀)
  have hpχ_tendsto : Filter.Tendsto (fun n => p (χ n)) Filter.atTop (nhds pstar) := by
    have hshift : Filter.Tendsto (fun n => ψ (ρ n) + K₀) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨b, fun n hn => le_trans hn (le_trans (le_trans (hρ_mono.id_le n) (hψ_mono.id_le (ρ n)))
          (Nat.le_add_right _ K₀))⟩
    exact hp_tendsto.comp hshift
  have hxχ_tendsto : Filter.Tendsto (fun n => xall (χ n)) Filter.atTop (nhds xstar) :=
    hx_conv.comp hρ_mono.tendsto_atTop
  have hyχ_tendsto : Filter.Tendsto (fun n => yall (χ n)) Filter.atTop (nhds ystar) := hy_conv
  have hxχ_agent : ∀ a, Filter.Tendsto (fun n => xall (χ n) a) Filter.atTop (nhds (xstar a)) :=
    fun a => ((continuous_apply a).tendsto _).comp hxχ_tendsto
  have hyχ_firm : ∀ j, Filter.Tendsto (fun n => yall (χ n) j) Filter.atTop (nhds (ystar j)) :=
    fun j => ((continuous_apply j).tendsto _).comp hyχ_tendsto
  have hxstar_nn : ∀ a l, 0 ≤ xstar a l := by
    intro a l
    have := (Set.mem_univ_pi.mp hxstar_mem) a
    exact ((Set.mem_univ_pi.mp this) l).1
  have hystar_truncY : ∀ j, ystar j ∈ (truncTech (E.tech j) M).Y :=
    fun j => (Set.mem_univ_pi.mp hystar_mem) j
  have hpstar_nn0 : ∀ l, 0 ≤ pstar l := fun l => hp_mem.1 l
  set zstar : Fin L → ℝ := E.aggregateExcess xstar ystar with hzstar_def
  have hz_tendsto : Filter.Tendsto (fun n => zall (χ n)) Filter.atTop (nhds zstar) := by
    have hxy : Filter.Tendsto (fun n => (xall (χ n), yall (χ n))) Filter.atTop
        (nhds (xstar, ystar)) := hxχ_tendsto.prodMk_nhds hyχ_tendsto
    exact (E.continuous_aggregateExcess_prod.tendsto _).comp hxy
  have h_walras_star : pstar ⬝ᵥ zstar = 0 := by
    have h_lhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ zall (χ n)) Filter.atTop
        (nhds (pstar ⬝ᵥ zstar)) :=
      ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
        (hpχ_tendsto.prodMk_nhds hz_tendsto)
    have h_eq : ∀ n, p (χ n) ⬝ᵥ zall (χ n) = 0 := fun n => hwalras (χ n)
    exact tendsto_nhds_unique (h_lhs.congr h_eq) tendsto_const_nhds
  have h_dot_star_le : ∀ q : Fin L → ℝ, q ∈ priceSimplex L → (∀ l, 0 < q l) →
      q ⬝ᵥ zstar ≤ 0 := by
    intro q hq hq_pos
    have h_dot_χ_tendsto : Filter.Tendsto (fun n => q ⬝ᵥ zall (χ n)) Filter.atTop
        (nhds (q ⬝ᵥ zstar)) :=
      ((continuous_const.dotProduct continuous_id).tendsto _).comp hz_tendsto
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_dot_le q hq hq_pos)
    have h_ev_nonpos : ∀ᶠ n in Filter.atTop, q ⬝ᵥ zall (χ n) ≤ 0 := by
      have hχshift : Filter.Tendsto (fun n => ψ (ρ n) + K₀) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun b =>
          ⟨b, fun n hn => le_trans hn (le_trans (le_trans (hρ_mono.id_le n)
            (hψ_mono.id_le (ρ n))) (Nat.le_add_right _ K₀))⟩
      filter_upwards [hχshift.eventually (Filter.eventually_atTop.mpr ⟨N, fun m hm => hm⟩)]
        with n hn
      exact hN (ψ (ρ n) + K₀) hn
    exact le_of_tendsto h_dot_χ_tendsto h_ev_nonpos
  have hz_nonpos : ∀ l, zstar l ≤ 0 :=
    coord_nonpos_of_interior_dotProduct_nonpos hL h_dot_star_le
  have hystar_inY : ∀ j, ystar j ∈ (E.tech j).Y := fun j => (hystar_truncY j).1
  have hplan_lower : ∀ l, -(∑ a, E.endow a l) ≤ ∑ j, ystar j l := by
    intro l
    have hxnn : 0 ≤ ∑ a, xstar a l :=
      Finset.sum_nonneg fun a _ => hxstar_nn a l
    have hzl := hz_nonpos l
    simp only [hzstar_def, aggregateExcess] at hzl
    linarith
  have hystar_normR : ∀ j, ‖ystar j‖ ≤ R := hR_bound ystar hystar_inY hplan_lower
  have hystar_int : ∀ j, ‖ystar j‖ < M :=
    fun j => lt_of_le_of_lt (hystar_normR j) (by simp [hM_def])
  have hystar_truncSupply : ∀ j, ystar j ∈ (truncTech (E.tech j) M).supply pstar := by
    intro j
    have hcg : IsClosedGraph (fun p : Fin L → ℝ => (truncTech (E.tech j) M).supply p) :=
      (truncTech_supply_uhc (hreg.techReg j) hM_nonneg).isClosedGraph
        (fun p => (truncTech_supply_compact (hreg.techReg j) M p).isClosed)
    have hmem : ∀ n, ((p (χ n)), yall (χ n) j) ∈
        {pq : (Fin L → ℝ) × (Fin L → ℝ) | pq.2 ∈ (truncTech (E.tech j) M).supply pq.1} :=
      fun n => hyall_sup (χ n) j
    have htend : Filter.Tendsto (fun n => (p (χ n), yall (χ n) j)) Filter.atTop
        (nhds (pstar, ystar j)) := hpχ_tendsto.prodMk_nhds (hyχ_firm j)
    exact hcg.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  have hystar_supply : ∀ j, ystar j ∈ (E.tech j).supply pstar := fun j =>
    mem_supply_of_mem_truncSupply_of_interior (hreg.techReg j).convex
      (hystar_truncSupply j) (hystar_int j)
  -- Truncated and true profit agree at p* (both equal p* ⬝ᵥ y*j); hence truncated = true wealth.
  have hprofit_eq : ∀ j, (truncTech (E.tech j) M).profit pstar = (E.tech j).profit pstar := by
    intro j
    rw [(truncTech (E.tech j) M).profit_eq_dotProduct_of_mem_supply (hystar_truncSupply j),
      (E.tech j).profit_eq_dotProduct_of_mem_supply (hystar_supply j)]
  have hwealth_eq : ∀ a, E.truncWealth M pstar a = E.wealth pstar a := by
    intro a
    simp only [truncWealth, wealth]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hprofit_eq j]
  have hwK_cont : ∀ a, Continuous (fun p => E.truncWealth M p a) :=
    fun a => E.truncWealth_continuous hreg hM_nonneg a
  have hbudget_bind : ∀ a, pstar ⬝ᵥ xstar a = E.wealth pstar a := by
    intro a
    have h_eq_ev : ∀ n, p (χ n) ⬝ᵥ xall (χ n) a = E.truncWealth M (p (χ n)) a :=
      fun n => budgetSetAt_binds (hreg.toRegularEconomy.locallyNonsatiated a) (hxall_dem (χ n) a)
    have h_lhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ xall (χ n) a) Filter.atTop
        (nhds (pstar ⬝ᵥ xstar a)) :=
      ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
        (hpχ_tendsto.prodMk_nhds (hxχ_agent a))
    have h_rhs : Filter.Tendsto (fun n => E.truncWealth M (p (χ n)) a) Filter.atTop
        (nhds (E.truncWealth M pstar a)) :=
      ((hwK_cont a).tendsto _).comp hpχ_tendsto
    rw [← hwealth_eq a]
    exact tendsto_nhds_unique (h_lhs.congr h_eq_ev) h_rhs
  have hquasi : ∀ (a : E.Agents) (y : Fin L → ℝ), (∀ l, 0 ≤ y l) →
      pstar ⬝ᵥ y < E.wealth pstar a → ¬ (y ≻[E.pref a] xstar a) := by
    intro a y hy_nn hy_strict
    suffices hge : xstar a ∈ (E.pref a).upperContour y by
      intro hlt; exact hlt.2 hge
    have h_ev_feasible : ∀ᶠ n in Filter.atTop,
        y ∈ budgetSetAt (p (χ n)) (E.truncWealth M (p (χ n)) a) := by
      have h_lhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ y) Filter.atTop (nhds (pstar ⬝ᵥ y)) :=
        ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
          (hpχ_tendsto.prodMk_nhds tendsto_const_nhds)
      have h_rhs : Filter.Tendsto (fun n => E.truncWealth M (p (χ n)) a) Filter.atTop
          (nhds (E.truncWealth M pstar a)) := ((hwK_cont a).tendsto _).comp hpχ_tendsto
      have hstrict : pstar ⬝ᵥ y < E.truncWealth M pstar a := by rw [hwealth_eq a]; exact hy_strict
      have h_lt := h_lhs.eventually_lt h_rhs hstrict
      filter_upwards [h_lt] with n hn
      exact ⟨hy_nn, hn.le⟩
    have h_upper_ev : ∀ᶠ n in Filter.atTop, xall (χ n) a ∈ (E.pref a).upperContour y := by
      filter_upwards [h_ev_feasible] with n hn
      exact (hxall_dem (χ n) a).2 y hn
    have h_closed : IsClosed ((E.pref a).upperContour y) :=
      (hreg.toRegularEconomy.contPref a).closed_upper y
    exact h_closed.mem_of_tendsto (hxχ_agent a) h_upper_ev
  have hIR : ∀ a, xstar a ≽[E.pref a] E.endow a := by
    intro a
    have h_endow_feasible : ∀ n, E.endow a ∈ budgetSetAt (p (χ n)) (E.truncWealth M (p (χ n)) a) :=
      fun n => E.endow_mem_budgetK hreg hM_nonneg (p (χ n)) a
    have h_upper_ev : ∀ᶠ n in Filter.atTop,
        xall (χ n) a ∈ (E.pref a).upperContour (E.endow a) := by
      filter_upwards with n
      exact (hxall_dem (χ n) a).2 (E.endow a) (h_endow_feasible n)
    have h_closed : IsClosed ((E.pref a).upperContour (E.endow a)) :=
      (hreg.toRegularEconomy.contPref a).closed_upper (E.endow a)
    exact h_closed.mem_of_tendsto (hxχ_agent a) h_upper_ev
  have hxstar_bud : ∀ a, xstar a ∈ E.budgetSet pstar a :=
    fun a => ⟨fun l => hxstar_nn a l, le_of_eq (hbudget_bind a)⟩
  exact ⟨pstar, xstar, ystar, hp_mem, hxstar_bud, hbudget_bind, hIR, hystar_supply, hquasi,
    hz_nonpos, h_walras_star⟩

/-- **Equilibrium data for a private-ownership production economy.** Under regularity, production
irreducibility, and `hendow_valued` (at every feasible-supply simplex price some agent's endowment
is valued positively), there exist `p ≥ 0` (nonzero), profit-maximizing plans `y`, consumer optima
`x`, and market clearing.

`hendow_valued` is weaker than every-good-ownership: In labor economies, free-input prices are
ruled out by `Technology.supply_eq_empty_of_free_input`, so `hendow_valued` holds even if no agent
owns the output good. -/
lemma exists_equilibrium_data_prod [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hirr : IrreducibleProd E) (hL : 0 < L)
    (hendow_valued : ∀ p : Fin L → ℝ, p ∈ priceSimplex L →
      (∀ j, ((E.tech j).supply p).Nonempty) → ∃ a, 0 < p ⬝ᵥ E.endow a) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → Fin L → ℝ) (y : E.Firms → Fin L → ℝ),
      (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ j, y j ∈ (E.tech j).supply p) ∧
      (∀ a, x a ∈ E.consumerDemand p a) ∧
      (∀ l, E.aggregateExcess x y l ≤ 0) ∧ p ⬝ᵥ E.aggregateExcess x y = 0 := by
  obtain ⟨p, x, y, hp_mem, hbud, hbind, hIR, hsupply, hquasi, hclears_le, hclears_eq⟩ :=
    E.exists_quasi_equilibrium_prod hne hreg hL
  obtain ⟨l₀, hl₀⟩ := priceSimplex_exists_pos hp_mem
  obtain ⟨a₀, hendow_pos⟩ := hendow_valued p hp_mem (fun j => ⟨y j, hsupply j⟩)
  have hagg : ∃ a, 0 < E.wealth p a := by
    refine ⟨a₀, ?_⟩
    have hprofit_nn : ∀ j, 0 ≤ (E.tech j).profit p := fun j => by
      have hinaction : p ⬝ᵥ (0 : Fin L → ℝ) ≤ (E.tech j).profit p :=
        (E.tech j).dotProduct_le_profit_of_mem_supply (hreg.techReg j).inaction (hsupply j)
      simpa using hinaction
    have hshare_nn : 0 ≤ ∑ j, E.share a₀ j * (E.tech j).profit p :=
      Finset.sum_nonneg fun j _ => mul_nonneg (E.share_nonneg a₀ j) (hprofit_nn j)
    simp only [wealth]; linarith
  obtain ⟨hp_pos, hopt⟩ :=
    E.quasi_to_walrasian_prod hne hreg hirr hp_mem hbud hbind hIR hsupply hquasi hagg
  exact ⟨p, x, y, fun l => (hp_pos l).le, ⟨l₀, hl₀⟩, hsupply, hopt, hclears_le, hclears_eq⟩

/-- **Existence of a Walrasian equilibrium with production** (Arrow and Debreu 1954; McKenzie
1959). Under `RegularProductionEconomy`, production irreducibility (`IrreducibleProd`), `0 < L`,
and `hendow_valued`, a `WalrasianEquilibriumWithProduction` exists. Generalizes the
consumption-only hypothesis (`Irreducible.toIrreducibleProd`) to firm-connected economies.

`RegularProductionEconomy` requires each firm's technology to be a `RegularTechnology`, so every
production set is convex (the no-increasing-returns condition). This is the convex
general-equilibrium case; the theorem does not cover increasing returns to scale. -/
theorem exists_equilibrium_prod [Finite E.Agents]
    (hne : Nonempty E.Agents) (hreg : RegularProductionEconomy E) (hirr : IrreducibleProd E)
    (hL : 0 < L) (hendow_valued : ∀ p : Fin L → ℝ, p ∈ priceSimplex L →
      (∀ j, ((E.tech j).supply p).Nonempty) → ∃ a, 0 < p ⬝ᵥ E.endow a) :
    Nonempty (WalrasianEquilibriumWithProduction E) := by
  obtain ⟨p, x, y, hp_nn, hp_ne, hprofit, hopt, hclears_le, hclears_eq⟩ :=
    E.exists_equilibrium_data_prod hne hreg hirr hL hendow_valued
  exact ⟨⟨p, x, y, hp_nn, hp_ne, hprofit, hopt, hclears_le, hclears_eq⟩⟩

end ProductionEconomy

end Econlib.Equilibrium
