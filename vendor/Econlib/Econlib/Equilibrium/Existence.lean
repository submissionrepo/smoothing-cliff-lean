/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Math.Topology.Kakutani

/-!
# General equilibrium: Existence of competitive equilibrium

This file contains existence results for Walrasian equilibria in finite, preference-carried
exchange economies. The main theorem, `Economy.exists_equilibrium`, returns a
`WalrasianEquilibrium` under `RegularEconomy`, McKenzie irreducibility (`Irreducible`), at least
one commodity, a nonempty finite agent set, and the ownership condition that every good is held in
strictly positive amount by some agent.

The result is stated for the general convex case: Demands may be set-valued, and no strict
concavity or single-valued demand selection is required. The file also exposes the price-simplex
objects, bounded demand correspondences, quasi-equilibrium data, and raw equilibrium-data statement
used by downstream developments.

## Main definitions

* `priceSimplex`: The standard price simplex of nonnegative vectors summing to one.
* `truncatedSimplex`: Prices in the simplex with every component `≥ ε`.
* `Economy.excessDemand`: The set-valued aggregate excess-demand correspondence.
* `Economy.demandBound`: A uniform box bound on demanded bundles over the ε-truncated simplex.

## Main statements

* `Economy.exists_quasi_equilibrium`: Market-clearing quasi-equilibrium with simplex prices,
  budget-binding, individual rationality, and quasi-optimality.
* `Economy.quasi_to_walrasian`: A quasi-equilibrium gives Walrasian consumer optimality under
  irreducibility and positive aggregate endowment value.
* `Economy.exists_equilibrium_data`: Raw equilibrium data (prices and allocation) under regularity,
  irreducibility, and the ownership condition.
* `Economy.exists_equilibrium`: A Walrasian equilibrium exists for any regular, irreducible economy
  in which every good is owned by some agent.

## References

* Arrow, Kenneth J., and Gerard Debreu. 1954. “Existence of an Equilibrium for a Competitive
  Economy.” *Econometrica* 22 (3): 265. [https://doi.org/10.2307/1907353](https://doi.org/10.2307/1907353).
* McKenzie, Lionel W. 1959. “On the Existence of General Equilibrium for a Competitive Market.”
  *Econometrica* 27 (1): 54. [https://doi.org/10.2307/1907777](https://doi.org/10.2307/1907777).

## Tags

general equilibrium, walrasian equilibrium, quasi-equilibrium, excess demand, price simplex
-/

@[expose] public section

open Finset BigOperators Matrix Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

/-! ## The price simplex -/

/-- The price simplex: Nonnegative price vectors summing to one. Abbreviates
`stdSimplex ℝ (Fin L)`; membership unfolds to `(∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1`. -/
abbrev priceSimplex (L : ℕ) : Set (Fin L → ℝ) := stdSimplex ℝ (Fin L)

/-- The price simplex is nonempty when `L > 0`. -/
lemma priceSimplex_nonempty (hL : 0 < L) : (priceSimplex L).Nonempty :=
  ⟨Pi.single ⟨0, hL⟩ 1, single_mem_stdSimplex ℝ _⟩

/-- Every simplex price has at least one strictly positive coordinate. -/
lemma priceSimplex_exists_pos {p : Fin L → ℝ} (hp : p ∈ priceSimplex L) :
    ∃ l, 0 < p l := by
  by_contra h; push Not at h
  have h_sum := hp.2
  have h_le : ∑ l, p l ≤ 0 := Finset.sum_nonpos fun l _ => h l
  linarith

/-! ## The ε-truncated simplex -/

variable {ε : ℝ}

/-- The ε-truncated simplex: Prices in the simplex with every component `≥ ε`. -/
def truncatedSimplex (ε : ℝ) (L : ℕ) : Set (Fin L → ℝ) :=
  {p ∈ priceSimplex L | ∀ l, ε ≤ p l}

/-- The ε-truncated simplex is contained in the price simplex. -/
lemma truncatedSimplex_subset : truncatedSimplex ε L ⊆ priceSimplex L :=
  fun _ hp => hp.1

/-- The ε-truncated simplex is closed. -/
lemma truncatedSimplex_closed : IsClosed (truncatedSimplex ε L) := by
  have h1 : IsClosed (priceSimplex L) := (isCompact_stdSimplex ℝ (ι := Fin L)).isClosed
  have h2 : IsClosed {p : Fin L → ℝ | ∀ l, ε ≤ p l} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have : truncatedSimplex ε L = priceSimplex L ∩ {p | ∀ l, ε ≤ p l} := by
    ext p; simp [truncatedSimplex]
  rw [this]; exact h1.inter h2

/-- The ε-truncated simplex is compact. -/
lemma truncatedSimplex_compact : IsCompact (truncatedSimplex ε L) :=
  (isCompact_stdSimplex ℝ (ι := Fin L)).of_isClosed_subset truncatedSimplex_closed
    truncatedSimplex_subset

/-- The ε-truncated simplex is convex. -/
lemma truncatedSimplex_convex : Convex ℝ (truncatedSimplex ε L) := by
  intro p ⟨hp, hpl⟩ q ⟨hq, hql⟩ a b ha hb hab
  refine ⟨convex_stdSimplex ℝ (Fin L) hp hq ha hb hab, fun l => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc ε = a * ε + b * ε := by rw [← add_mul, hab, one_mul]
    _ ≤ a * p l + b * q l := add_le_add
        (mul_le_mul_of_nonneg_left (hpl l) ha) (mul_le_mul_of_nonneg_left (hql l) hb)

/-- The ε-truncated simplex is nonempty when `ε ≤ 1/L`. -/
lemma truncatedSimplex_nonempty (hL : 0 < L) (hε : ε ≤ 1 / (L : ℝ)) :
    (truncatedSimplex ε L).Nonempty := by
  have hLR : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  refine ⟨fun _ => 1 / (L : ℝ), ?_, fun _ => hε⟩
  exact ⟨fun _ => by positivity, by simp [Fintype.card_fin, ne_of_gt hLR]⟩

/-- All price coordinates are strictly positive on the ε-truncated simplex when `ε > 0`. -/
lemma truncatedSimplex_pos_prices {p : Fin L → ℝ} (hp : p ∈ truncatedSimplex ε L)
    (hε : 0 < ε) (l : Fin L) : 0 < p l :=
  lt_of_lt_of_le hε (hp.2 l)

/-- Any strictly interior simplex price eventually lies in `truncatedSimplex (1/((n+2)L))`. -/
lemma interior_price_eventually_in_truncated {q : Fin L → ℝ}
    (hq_simplex : q ∈ priceSimplex L) (hq_pos : ∀ l, 0 < q l) (hL : 0 < L) :
    ∃ N : ℕ, ∀ n, N ≤ n → q ∈ truncatedSimplex (1 / (↑(n + 2) * ↑L)) L := by
  have hLR : (0 : ℝ) < ↑L := Nat.cast_pos.mpr hL
  suffices h : ∀ l, ∃ N : ℕ, ∀ n, N ≤ n → 1 / (↑(n + 2) * ↑L) ≤ q l by
    choose N_l hN_l using h
    refine ⟨Finset.univ.sup N_l, fun n hn => ⟨hq_simplex, fun l => ?_⟩⟩
    exact hN_l l n (le_trans (Finset.le_sup (f := N_l) (Finset.mem_univ l)) hn)
  intro l
  have hql_pos := hq_pos l
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (q l * ↑L))
  refine ⟨M, fun n hn => ?_⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑(n + 2) * ↑L)]
  have hM_le : 1 / (q l * ↑L) < ↑(n + 2) := by
    calc 1 / (q l * ↑L) < ↑M := hM
      _ ≤ ↑n := Nat.cast_le.mpr hn
      _ ≤ ↑(n + 2) := by exact_mod_cast (show n ≤ n + 2 by omega)
  have hql_L_pos : 0 < q l * ↑L := mul_pos hql_pos hLR
  have h1 : q l * (↑(n + 2) * ↑L) = (q l * ↑L) * ↑(n + 2) := by ring
  rw [h1]
  calc 1 = q l * ↑L * (1 / (q l * ↑L)) := by field_simp
    _ ≤ q l * ↑L * ↑(n + 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hM_le) (le_of_lt hql_L_pos)

/-- If `q ⬝ᵥ zstar ≤ 0` for every strictly interior simplex price `q`, then `zstar l ≤ 0` for all
`l`. -/
lemma coord_nonpos_of_interior_dotProduct_nonpos {zstar : Fin L → ℝ} (hL : 0 < L)
    (h_dot_star_le : ∀ q : Fin L → ℝ, q ∈ priceSimplex L → (∀ l', 0 < q l') → q ⬝ᵥ zstar ≤ 0) :
    ∀ l, zstar l ≤ 0 := by
  intro l; by_contra h_pos; push Not at h_pos
  set C := (∑ l' ∈ Finset.univ.erase l, zstar l') - (↑(L - 1 : ℕ) : ℝ) * zstar l with hC_def
  obtain ⟨δ, hδ_pos, hδ_small, hδ_val⟩ : ∃ δ : ℝ, 0 < δ ∧
      δ < 1 / (↑L : ℝ) ∧ 0 < zstar l + δ * C := by
    by_cases hC : 0 ≤ C
    · have hLR : (0:ℝ) < ↑L := Nat.cast_pos.mpr hL
      exact ⟨1 / (2 * ↑L), by positivity,
        div_lt_div_of_pos_left one_pos hLR (by linarith),
        add_pos_of_pos_of_nonneg h_pos (mul_nonneg (by positivity) hC)⟩
    · push Not at hC
      have hnC_pos : 0 < -C := neg_pos.mpr hC
      set δ₁ := min (1 / (2 * (↑L : ℝ))) (zstar l / (2 * (-C)))
      have hδ₁_pos : 0 < δ₁ := lt_min (by positivity) (div_pos h_pos (by positivity))
      have hLR : (0:ℝ) < ↑L := Nat.cast_pos.mpr hL
      refine ⟨δ₁, hδ₁_pos, lt_of_le_of_lt (min_le_left _ _)
        (div_lt_div_of_pos_left one_pos hLR (by linarith)), ?_⟩
      have hδ₁_le : δ₁ ≤ zstar l / (2 * (-C)) := min_le_right _ _
      have h_bound : δ₁ * (-C) ≤ zstar l / 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hδ₁_le (le_of_lt hnC_pos),
          div_mul_cancel₀ (zstar l) (show (2 : ℝ) * (-C) ≠ 0 by positivity)]
      linarith [show δ₁ * C = -(δ₁ * (-C)) from by ring]
  set q : Fin L → ℝ := fun l' => if l' = l then 1 - (↑(L - 1 : ℕ) : ℝ) * δ else δ with hq_def
  have hq_pos : ∀ l', 0 < q l' := by
    intro l'; simp only [hq_def]; split_ifs
    · have : (↑(L - 1 : ℕ) : ℝ) * δ < 1 := by
        have hle : (↑(L - 1 : ℕ) : ℝ) ≤ ↑L := by exact_mod_cast Nat.sub_le L 1
        calc (↑(L - 1 : ℕ) : ℝ) * δ ≤ ↑L * δ :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hδ_pos)
          _ < ↑L * (1 / ↑L) := mul_lt_mul_of_pos_left hδ_small (Nat.cast_pos.mpr hL)
          _ = 1 := by field_simp
      linarith
    · exact hδ_pos
  have hq_simplex : q ∈ priceSimplex L := by
    refine ⟨fun l' => le_of_lt (hq_pos l'), ?_⟩
    calc ∑ l', q l'
        = q l + ∑ l' ∈ Finset.univ.erase l, q l' :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ l)).symm
      _ = (1 - (↑(L - 1 : ℕ) : ℝ) * δ) +
          ∑ _l' ∈ Finset.univ.erase l, δ := by
          simp only [hq_def, if_pos rfl]
          congr 1
          exact Finset.sum_congr rfl fun l' hl' => if_neg (Finset.mem_erase.mp hl').1
      _ = (1 - (↑(L - 1 : ℕ) : ℝ) * δ) + ↑(L - 1 : ℕ) * δ := by
          congr 1
          rw [Finset.sum_const, nsmul_eq_mul,
              show (Finset.univ.erase l).card = L - 1 from by
                rw [Finset.card_erase_of_mem (Finset.mem_univ l)]; simp]
      _ = 1 := by ring
  have h_dot_pos : 0 < q ⬝ᵥ zstar := by
    simp only [dotProduct]
    have h_split : ∑ l', q l' * zstar l' =
        q l * zstar l + ∑ l' ∈ Finset.univ.erase l, q l' * zstar l' :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ l)).symm
    have hql : q l = 1 - (↑(L - 1 : ℕ) : ℝ) * δ := if_pos rfl
    have h_tail : ∑ l' ∈ Finset.univ.erase l, q l' * zstar l' =
        δ * ∑ l' ∈ Finset.univ.erase l, zstar l' := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l' hl' => by
        rw [show q l' = δ from if_neg (Finset.mem_erase.mp hl').1]
    rw [h_split, hql, h_tail]
    linarith [show (1 - (↑(L - 1 : ℕ) : ℝ) * δ) * zstar l +
        δ * ∑ l' ∈ Finset.univ.erase l, zstar l' = zstar l + δ * C from by
      simp only [hC_def]; ring]
  linarith [h_dot_star_le q hq_simplex hq_pos]

/-! ## The price player: Maximizers of `q ⬝ᵥ z` on the truncated simplex -/

/-- Prices in `Δ_ε` maximizing `q ⬝ᵥ z` (the price player's best response to excess demand `z`). -/
def maxDotTruncated (ε : ℝ) (z : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {q ∈ truncatedSimplex ε L | IsMaxOn (fun q' => q' ⬝ᵥ z) (truncatedSimplex ε L) q}

/-- Maximizers of `q ⬝ᵥ z` on `Δ_ε` lie in `Δ_ε`. -/
lemma maxDotTruncated_subset {z : Fin L → ℝ} : maxDotTruncated ε z ⊆ truncatedSimplex ε L :=
  fun _ hq => hq.1

/-- The set of dot-product maximizers on `Δ_ε` is nonempty. -/
lemma maxDotTruncated_nonempty (hL : 0 < L) (hε_le : ε ≤ 1 / (L : ℝ))
    (z : Fin L → ℝ) : (maxDotTruncated ε z).Nonempty := by
  have h_cont : Continuous (fun q => q ⬝ᵥ z) :=
    continuous_finset_sum _ fun l _ => (continuous_apply l).mul continuous_const
  obtain ⟨q, hq, hmax⟩ :=
    truncatedSimplex_compact.exists_isMaxOn (truncatedSimplex_nonempty hL hε_le) h_cont.continuousOn
  exact ⟨q, hq, hmax⟩

/-- The set of dot-product maximizers on `Δ_ε` is convex. -/
lemma maxDotTruncated_convex (z : Fin L → ℝ) : Convex ℝ (maxDotTruncated ε z) := by
  intro p ⟨hp, hp_max⟩ q ⟨hq, hq_max⟩ a b ha hb hab
  refine ⟨truncatedSimplex_convex hp hq ha hb hab, ?_⟩
  intro r hr
  change r ⬝ᵥ z ≤ (a • p + b • q) ⬝ᵥ z
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (hp_max hr) ha
  have h2 := mul_le_mul_of_nonneg_left (hq_max hr) hb
  linarith [show a * r ⬝ᵥ z + b * r ⬝ᵥ z = r ⬝ᵥ z from by rw [← add_mul, hab, one_mul]]

/-- The budget correspondence `p ↦ budgetSetAt p (w p)` is upper hemicontinuous at any price `p₀`
where the budget set is compact, provided a feasible interior point exists. -/
lemma budgetSetAt_upperHemicontinuousAt (w : (Fin L → ℝ) → ℝ) (hw : Continuous w)
    (x₀ : Fin L → ℝ) (hx₀ : ∀ p, x₀ ∈ budgetSetAt p (w p))
    {p₀ : Fin L → ℝ} (hK : IsCompact (budgetSetAt p₀ (w p₀))) :
    UpperHemicontinuousAt (fun p : Fin L → ℝ => budgetSetAt p (w p)) p₀ := by
  have hmem_self : ∀ p : Fin L → ℝ, x₀ ∈ budgetSetAt p (w p) := hx₀
  rw [upperHemicontinuousAt_iff_forall_isOpen]
  intro U hU hBU
  obtain ⟨R, hR_pos, hK₀R⟩ :
      ∃ R : ℝ, 0 < R ∧ budgetSetAt p₀ (w p₀) ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    exact ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right R 1),
      hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))⟩
  have he_R : ‖x₀‖ ≤ R := by
    have h := hK₀R (hmem_self p₀)
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
  -- For `p ∈ N₂`, any point outside `closedBall(0, R+1)` would be connected to `x₀` by a segment
  -- crossing the sphere, contradicting the tube argument above.
  have h_bound : ∀ p ∈ N₂, budgetSetAt p (w p) ⊆ Metric.closedBall 0 (R + 1) := by
    intro p hp x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h_big; push Not at h_big
    obtain ⟨t, ht, ht_norm⟩ := segment_crosses_sphere (by linarith : ‖x₀‖ ≤ R + 1) h_big
    have hy_bset : (1 - t) • x₀ + t • x ∈ budgetSetAt p (w p) :=
      budgetSetAt_convex p (w p) (hmem_self p) hx
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

namespace Economy

/-- The **excess demand correspondence**: Aggregate excess vectors achievable by some demand
selection. For general (not necessarily strictly) convex preferences this is set-valued. -/
noncomputable def excessDemand (E : Economy L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  {z | ∃ x : E.Agents → (Fin L → ℝ), (∀ a, x a ∈ E.demand p a) ∧ z = E.aggregateExcess x}

/-- Excess demand is homogeneous of degree zero: Scaling prices by `t > 0` leaves the excess-demand
set unchanged. -/
lemma excessDemand_homogeneous (E : Economy L) {t : ℝ} (ht : 0 < t) (p : Fin L → ℝ) :
    E.excessDemand (t • p) = E.excessDemand p := by
  simp only [excessDemand, E.demand_homogeneous ht]

/-! ## Per-ε existence via Kakutani -/

/-- The summation functional `f ↦ ∑ a, f a` as a linear map `(E.Agents → ℝ) →ₗ[ℝ] ℝ`. -/
noncomputable def aggregationLinearMap (E : Economy L) : (E.Agents → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun f => ∑ a, f a
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The summation functional over `E.Agents` is continuous. -/
lemma continuous_aggregate (E : Economy L) [Finite E.Agents] :
    Continuous (fun f : E.Agents → ℝ => ∑ a, f a) := by
  letI : Fintype E.Agents := Fintype.ofFinite E.Agents
  exact E.aggregationLinearMap.continuous_of_finiteDimensional

/-- Aggregate excess demand is continuous in the allocation. -/
lemma continuous_aggregateExcess (E : Economy L) [Finite E.Agents] :
    Continuous (fun x : E.Agents → Fin L → ℝ => E.aggregateExcess x) := by
  refine continuous_pi fun l => ?_
  simp only [aggregateExcess]
  refine (E.continuous_aggregate.comp ?_).sub continuous_const
  exact continuous_pi fun a => (continuous_apply l).comp (continuous_apply a)

/-- On the truncated simplex, `p ⬝ᵥ E.endow a ≤ ⨆ l, E.endow a l`. -/
lemma wealth_le_iSup_endow (E : Economy L) (hL : 0 < L) {p : Fin L → ℝ}
    (hp : p ∈ truncatedSimplex ε L) (a : E.Agents) :
    p ⬝ᵥ E.endow a ≤ ⨆ l, E.endow a l := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  have hbdd : BddAbove (Set.range fun l => E.endow a l) := Finite.bddAbove_range _
  have hsum_one := (truncatedSimplex_subset hp).2
  have hnonneg := fun l => (truncatedSimplex_subset hp).1 l
  calc p ⬝ᵥ E.endow a = ∑ l, p l * E.endow a l := by simp only [dotProduct]
    _ ≤ ∑ l, p l * (⨆ l', E.endow a l') := by
        refine Finset.sum_le_sum fun l _ => ?_
        exact mul_le_mul_of_nonneg_left (le_ciSup hbdd l) (hnonneg l)
    _ = (∑ l, p l) * (⨆ l', E.endow a l') := by rw [← Finset.sum_mul]
    _ = ⨆ l, E.endow a l := by rw [hsum_one, one_mul]

/-- Uniform bound on demanded bundle coordinates over the ε-truncated simplex:
`(⨆ a l, E.endow a l) / ε`. -/
noncomputable def demandBound (E : Economy L) (ε : ℝ) : ℝ :=
  (⨆ a, ⨆ l, E.endow a l) / ε

/-- Every demanded bundle lies in the box `[0, demandBound ε]^L` at any truncated-simplex price. -/
lemma demand_subset_box (E : Economy L) [Finite E.Agents] (hL : 0 < L) {p : Fin L → ℝ}
    (hp : p ∈ truncatedSimplex ε L) (hε_pos : 0 < ε) (a : E.Agents) :
    E.demand p a ⊆ Set.pi Set.univ (fun _ : Fin L => Set.Icc (0 : ℝ) (E.demandBound ε)) := by
  have hp_pos : ∀ l, 0 < p l := fun l => truncatedSimplex_pos_prices hp hε_pos l
  intro x hx l _
  have hx_bud : x ∈ E.budgetSet p a := E.demand_subset_budgetSet p a hx
  refine ⟨hx_bud.1 l, ?_⟩
  have hcoord : x l ≤ (p ⬝ᵥ E.endow a) / p l :=
    budgetSetAt_coord_bound hp_pos x hx_bud l
  have hw : p ⬝ᵥ E.endow a ≤ ⨆ l', E.endow a l' := E.wealth_le_iSup_endow hL hp a
  have hbdd_l : BddAbove (Set.range fun l' => E.endow a l') := Finite.bddAbove_range _
  have hbdd_a : BddAbove (Set.range fun a' => ⨆ l', E.endow a' l') := Finite.bddAbove_range _
  have hsup_a : (⨆ l', E.endow a l') ≤ ⨆ a', ⨆ l', E.endow a' l' := le_ciSup hbdd_a a
  have hw' : p ⬝ᵥ E.endow a ≤ ⨆ a', ⨆ l', E.endow a' l' := le_trans hw hsup_a
  have hsup_nonneg : 0 ≤ ⨆ a', ⨆ l', E.endow a' l' :=
    le_trans (le_trans (E.endow_mem a l) (le_ciSup hbdd_l l)) hsup_a
  calc x l ≤ (p ⬝ᵥ E.endow a) / p l := hcoord
    _ ≤ (⨆ a', ⨆ l', E.endow a' l') / p l := by gcongr; exact (hp_pos l).le
    _ ≤ (⨆ a', ⨆ l', E.endow a' l') / ε :=
        div_le_div_of_nonneg_left hsup_nonneg hε_pos (hp.2 l)
    _ = E.demandBound ε := rfl

/-- **Demand is upper hemicontinuous in prices** (Berge's maximum theorem), restricted to a set `P`
of strictly positive prices. On such a set the hypotheses of the maximum theorem are dischargeable:
The budget set is compact (`isCompact_budgetSet_of_pos_prices`), and the cheaper-point (Slater)
condition holds automatically, since the origin `z = 0` is strictly cheaper than the regular
economy's nonzero, nonnegative endowment when `p ⬝ᵥ e > 0` at strictly positive `p`.

The restriction to positive prices is essential: At `p = 0` the budget set is the whole non-compact
nonnegative orthant and no nonnegative bundle is cheaper than the endowment, so the maximum-theorem
inputs are unsatisfiable there. -/
theorem demand_upperHemicontinuousOn (E : Economy L) (hreg : RegularEconomy E) (a : E.Agents)
    {P : Set (Fin L → ℝ)} (hP_pos : ∀ p ∈ P, ∀ l, 0 < p l) :
    UpperHemicontinuousOn (fun p => E.demand p a) P := by
  rw [← upperHemicontinuousOn_iff_restrict]
  obtain ⟨u, hu_cont, hu_eq⟩ := E.exists_demand_eq_argmax hreg a
  set e := E.endow a with he_def
  have hpos : ∀ pp : ↥P, ∀ l, 0 < pp.1 l := fun pp l => hP_pos pp.1 pp.2 l
  set Φ : ↥P → Set (Fin L → ℝ) := fun pp => E.budgetSet pp.1 a with hΦ_def
  have hΦ_eq : ∀ pp, Φ pp = budgetSetAt pp.1 (pp.1 ⬝ᵥ e) := fun pp => rfl
  have hΦ_compact : ∀ pp, IsCompact (Φ pp) :=
    fun pp => E.isCompact_budgetSet_of_pos_prices (hpos pp) a
  have hΦ_nonempty : ∀ pp, (Φ pp).Nonempty := fun pp => E.budgetSet_nonempty pp.1 a
  have hΦ_uhc : UpperHemicontinuous Φ := by
    rw [upperHemicontinuous_iff]
    intro pp
    have hAt : UpperHemicontinuousAt (fun p : Fin L → ℝ => budgetSetAt p (p ⬝ᵥ e)) pp.1 :=
      budgetSetAt_upperHemicontinuousAt (fun p => p ⬝ᵥ e)
        (continuous_id.dotProduct continuous_const) e (fun p => ⟨E.endow_mem a, le_refl _⟩)
        (by simpa [hΦ_eq pp] using hΦ_compact pp)
    exact hAt.comp (continuous_subtype_val.continuousAt)
  have he_nn : ∀ l, 0 ≤ e l := fun l => E.endow_mem a l
  have he_ne : e ≠ 0 := hreg.endow_ne a
  obtain ⟨l₀, hl₀⟩ : ∃ l, 0 < e l := by
    by_contra h; push Not at h
    exact he_ne (funext fun l => le_antisymm (h l) (he_nn l))
  have hΦ_lhc : LowerHemicontinuous Φ := by
    intro pp
    have hwealth_pos : 0 < pp.1 ⬝ᵥ e := by
      have hterm : ∀ l ∈ Finset.univ, 0 ≤ pp.1 l * e l :=
        fun l _ => mul_nonneg (hpos pp l).le (he_nn l)
      calc (0 : ℝ) < pp.1 l₀ * e l₀ := mul_pos (hpos pp l₀) hl₀
        _ ≤ ∑ l, pp.1 l * e l := Finset.single_le_sum hterm (Finset.mem_univ l₀)
        _ = pp.1 ⬝ᵥ e := rfl
    have hAt : LowerHemicontinuousAt (fun p : Fin L → ℝ => budgetSetAt p (p ⬝ᵥ e)) pp.1 :=
      budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint (fun p => p ⬝ᵥ e)
        (continuous_id.dotProduct continuous_const)
        ⟨0, fun l => le_refl 0, by simpa using hwealth_pos⟩
    exact hAt.comp continuous_subtype_val.continuousAt
  have hf_cont : Continuous (fun q : ↥P × (Fin L → ℝ) => u q.2) :=
    hu_cont.comp continuous_snd
  have huhc : UpperHemicontinuous (fun pp : ↥P => Optimization.argmax u (Φ pp)) :=
    Optimization.argmax_upperHemicontinuous hf_cont hΦ_uhc hΦ_lhc hΦ_compact hΦ_nonempty
  have hdemand_eq : (P.restrict fun p => E.demand p a) =
      fun pp => Optimization.argmax u (Φ pp) := by
    funext pp; exact hu_eq pp.1
  rw [hdemand_eq]
  exact huhc

/-- The demand correspondence `pp ↦ E.demand pp.1 a` has a closed graph over
`↥(truncatedSimplex ε L)`. The upper hemicontinuity is supplied by the strictly-positive-price
`demand_upperHemicontinuousOn`; the truncated simplex consists of strictly positive prices. -/
lemma demand_closedGraph_subtype (E : Economy L) (hreg : RegularEconomy E)
    (hε_pos : 0 < ε) (a : E.Agents) :
    IsClosedGraph (fun pp : ↥(truncatedSimplex ε L) => E.demand pp.1 a) := by
  have hpos : ∀ p ∈ truncatedSimplex ε L, ∀ l, 0 < p l :=
    fun p hp l => truncatedSimplex_pos_prices hp hε_pos l
  have huhc : UpperHemicontinuous (fun pp : ↥(truncatedSimplex ε L) => E.demand pp.1 a) :=
    upperHemicontinuousOn_iff_restrict.mpr (E.demand_upperHemicontinuousOn hreg a hpos)
  refine huhc.isClosedGraph (fun pp => ?_)
  exact (E.demand_compact hreg (hpos pp.1 pp.2) a).isClosed

/-- For `0 < ε ≤ 1/L`, there exists a price `p ∈ Δ_ε` and allocation `x` such that every consumer
optimizes and `p` maximizes aggregate excess demand value over `Δ_ε`. -/
lemma exists_truncated_fixed_point (E : Economy L) [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hL : 0 < L)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / (L : ℝ)) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → (Fin L → ℝ)),
      p ∈ truncatedSimplex ε L ∧ (∀ a, x a ∈ E.demand p a) ∧
        IsMaxOn (fun q => q ⬝ᵥ E.aggregateExcess x) (truncatedSimplex ε L) p := by
  classical
  letI : Fintype E.Agents := Fintype.ofFinite E.Agents
  set B := E.demandBound ε with hB_def
  have hB_nonneg : 0 ≤ B := by
    have hbdd_l : ∀ a, BddAbove (Set.range fun l => E.endow a l) := fun a => Finite.bddAbove_range _
    have hbdd_a : BddAbove (Set.range fun a => ⨆ l, E.endow a l) := Finite.bddAbove_range _
    have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
    have hsup_nonneg : 0 ≤ ⨆ a, ⨆ l, E.endow a l := by
      obtain ⟨a₀⟩ := hne
      exact le_trans (le_trans (E.endow_mem a₀ ⟨0, hL⟩) (le_ciSup (hbdd_l a₀) ⟨0, hL⟩))
        (le_ciSup hbdd_a a₀)
    exact div_nonneg hsup_nonneg hε_pos.le
  set box : Set (E.Agents → Fin L → ℝ) :=
    Set.pi Set.univ (fun _ : E.Agents => Set.pi Set.univ (fun _ : Fin L => Set.Icc (0 : ℝ) B))
    with hbox_def
  set S : Set ((Fin L → ℝ) × (E.Agents → Fin L → ℝ)) := truncatedSimplex ε L ×ˢ box with hS_def
  have hbox_convex : Convex ℝ box :=
    convex_pi fun _ _ => convex_pi fun _ _ => convex_Icc _ _
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hbox_nonempty : box.Nonempty :=
    ⟨fun _ _ => 0, fun _ _ => Set.mem_univ_pi.mpr fun _ => ⟨le_refl _, hB_nonneg⟩⟩
  have hS_convex : Convex ℝ S := truncatedSimplex_convex.prod hbox_convex
  have hS_compact : IsCompact S := truncatedSimplex_compact.prod hbox_compact
  have hS_nonempty : S.Nonempty :=
    (truncatedSimplex_nonempty hL hε_le).prod hbox_nonempty
  have hdemand_box : ∀ p ∈ truncatedSimplex ε L, ∀ (x : E.Agents → Fin L → ℝ),
      (∀ a, x a ∈ E.demand p a) → x ∈ box := by
    intro p hp x hx
    exact Set.mem_univ_pi.mpr fun a => E.demand_subset_box hL hp hε_pos a (hx a)
  set Ψ : ↥S → Set ((Fin L → ℝ) × (E.Agents → Fin L → ℝ)) :=
    fun z => maxDotTruncated ε (E.aggregateExcess z.1.2) ×ˢ
      Set.pi Set.univ (fun a => E.demand z.1.1 a) with hΨ_def
  have hz_price : ∀ z : ↥S, z.1.1 ∈ truncatedSimplex ε L := fun z => z.2.1
  set Θ := ↥(truncatedSimplex ε L)
  have hToΘ_cont : Continuous (fun z : ↥S => (⟨z.1.1, hz_price z⟩ : Θ)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hpos_price : ∀ z : ↥S, ∀ l, 0 < z.1.1 l :=
    fun z l => truncatedSimplex_pos_prices (hz_price z) hε_pos l
  have hΨ_sub : ∀ z, Ψ z ⊆ S := by
    rintro z ⟨q, y⟩ ⟨hq, hy⟩
    refine ⟨maxDotTruncated_subset hq, ?_⟩
    refine hdemand_box z.1.1 (hz_price z) y (fun a => ?_)
    exact (Set.mem_univ_pi.mp hy) a
  have hΨ_convex : ∀ z, Convex ℝ (Ψ z) := fun z =>
    (maxDotTruncated_convex _).prod
      (convex_pi fun a _ => E.demand_convex a (hreg.convex a) z.1.1)
  have hΨ_nonempty : ∀ z, (Ψ z).Nonempty := fun z =>
    (maxDotTruncated_nonempty hL hε_le _).prod
      (Set.univ_pi_nonempty_iff.mpr fun a => E.demand_nonempty hreg (hpos_price z) a)
  have hΨ_cg : IsClosedGraph Ψ := by
    set W := ↥S × ((Fin L → ℝ) × (E.Agents → Fin L → ℝ)) with hW_def
    have cont_q : Continuous (fun w : W => w.2.1) := continuous_fst.comp continuous_snd
    have cont_excess :
        Continuous (fun w : W => E.aggregateExcess w.1.1.2) :=
      E.continuous_aggregateExcess.comp
        ((continuous_snd.comp continuous_subtype_val).comp continuous_fst)
    have hA1 : IsClosed {w : W | w.2.1 ∈ truncatedSimplex ε L} :=
      truncatedSimplex_closed.preimage cont_q
    have hA2 : IsClosed {w : W |
        IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2) (truncatedSimplex ε L) w.2.1} := by
      have heq : {w : W |
          IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2) (truncatedSimplex ε L) w.2.1} =
          ⋂ r ∈ truncatedSimplex ε L,
            {w : W | r ⬝ᵥ E.aggregateExcess w.1.1.2 ≤ w.2.1 ⬝ᵥ E.aggregateExcess w.1.1.2} := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_iInter, isMaxOn_iff]
      rw [heq]
      refine isClosed_biInter fun r _ => isClosed_le ?_ ?_
      · exact (continuous_const.dotProduct cont_excess)
      · exact cont_q.dotProduct cont_excess
    have hBset : IsClosed {w : W | ∀ a, w.2.2 a ∈ E.demand w.1.1.1 a} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun a => ?_
      have hcg := E.demand_closedGraph_subtype hreg hε_pos a
      have hg : Continuous (fun w : W =>
          ((⟨w.1.1.1, hz_price w.1⟩ : Θ), w.2.2 a)) :=
        ((hToΘ_cont.comp continuous_fst).prodMk
          (((continuous_apply a).comp continuous_snd).comp continuous_snd))
      exact hcg.preimage hg
    have hgraph_eq : {w : ↥S × ((Fin L → ℝ) × (E.Agents → Fin L → ℝ)) | w.2 ∈ Ψ w.1} =
        {w | w.2.1 ∈ truncatedSimplex ε L} ∩
        {w | IsMaxOn (fun q' => q' ⬝ᵥ E.aggregateExcess w.1.1.2) (truncatedSimplex ε L) w.2.1} ∩
        {w | ∀ a, w.2.2 a ∈ E.demand w.1.1.1 a} := by
      ext w
      simp only [hΨ_def, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, maxDotTruncated,
        Set.mem_univ_pi, and_assoc]
    rw [show IsClosedGraph Ψ =
        IsClosed {w : ↥S × ((Fin L → ℝ) × (E.Agents → Fin L → ℝ)) | w.2 ∈ Ψ w.1} from rfl,
      hgraph_eq]
    exact (hA1.inter hA2).inter hBset
  obtain ⟨z, hz⟩ := kakutaniFixedPoint S hS_convex hS_compact hS_nonempty Ψ hΨ_cg
    (fun z => ⟨hΨ_sub z, hΨ_convex z, hΨ_nonempty z⟩)
  obtain ⟨hz_max, hz_dem⟩ := hz
  refine ⟨z.1.1, z.1.2, hz_price z, fun a => ?_, ?_⟩
  · exact (Set.mem_univ_pi.mp hz_dem) a
  · exact hz_max.2

/-! ## The `ε → 0` limit -/

/-- **Existence of a quasi-equilibrium.** For a regular economy, there exist prices `p` in the
simplex and a market-clearing allocation `x` that is budget-binding, individually rational, and
quasi-optimal (no strictly-cheaper nonnegative bundle is strictly preferred to `x a`). -/
lemma exists_quasi_equilibrium (E : Economy L) [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hL : 0 < L) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → Fin L → ℝ),
      p ∈ priceSimplex L ∧
      (∀ a, x a ∈ E.budgetSet p a) ∧
      (∀ a, p ⬝ᵥ x a = p ⬝ᵥ E.endow a) ∧
      (∀ a, x a ≽[E.pref a] E.endow a) ∧
      (∀ a y, (∀ l, 0 ≤ y l) → p ⬝ᵥ y < p ⬝ᵥ E.endow a → ¬ (y ≻[E.pref a] x a)) ∧
      E.MarketClears p x := by
  classical
  letI : DecidableEq E.Agents := Classical.decEq _
  have hLR : (0:ℝ) < ↑L := Nat.cast_pos.mpr hL
  set εseq : ℕ → ℝ := fun k => 1 / ((↑(k + 2) : ℝ) * ↑L) with hεseq_def
  have hεk_pos : ∀ k : ℕ, 0 < εseq k := fun k => by simp only [hεseq_def]; positivity
  have hεk_le : ∀ k : ℕ, εseq k ≤ 1 / ↑L := by
    intro k
    simp only [hεseq_def]
    apply div_le_div_of_nonneg_left (by positivity) hLR
    exact le_mul_of_one_le_left hLR.le (by exact_mod_cast (show 1 ≤ k + 2 by omega))
  have hp_data : ∀ k, ∃ (pk : Fin L → ℝ) (xk : E.Agents → Fin L → ℝ),
      pk ∈ truncatedSimplex (εseq k) L ∧ (∀ a, xk a ∈ E.demand pk a) ∧
        IsMaxOn (fun q => q ⬝ᵥ E.aggregateExcess xk) (truncatedSimplex (εseq k) L)
          pk := fun (k : ℕ) =>
    E.exists_truncated_fixed_point hne hreg hL (hεk_pos k) (hεk_le k)
  choose p xall hp_trunc hxall_dem hpall_max using hp_data
  have hp_simplex : ∀ k, p k ∈ priceSimplex L := fun k => truncatedSimplex_subset (hp_trunc k)
  set zall : ℕ → Fin L → ℝ := fun k => E.aggregateExcess (xall k) with hzall_def
  obtain ⟨pstar, hp_mem, φ, hφ_mono, hp_tendsto⟩ :=
    (isCompact_stdSimplex ℝ (ι := Fin L)).tendsto_subseq hp_simplex
  have h_dot_le : ∀ (q : Fin L → ℝ), q ∈ priceSimplex L → (∀ l, 0 < q l) →
      ∀ᶠ k in Filter.atTop, q ⬝ᵥ zall (φ k) ≤ 0 := by
    intro q hq hq_pos
    obtain ⟨N, hN⟩ := interior_price_eventually_in_truncated hq hq_pos hL
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, fun k hk => hk⟩] with k hk
    have hφk_ge : N ≤ φ k := le_trans hk (hφ_mono.id_le k)
    have hq_trunc : q ∈ truncatedSimplex (εseq (φ k)) L := hN (φ k) hφk_ge
    have h_maxdot : q ⬝ᵥ zall (φ k) ≤ p (φ k) ⬝ᵥ zall (φ k) := (hpall_max (φ k)) hq_trunc
    have h_walras : p (φ k) ⬝ᵥ zall (φ k) = 0 :=
      E.walras_law hreg (hxall_dem (φ k))
    linarith
  set Etot : ℝ := ∑ l : Fin L, ∑ a, E.endow a l with hEtot_def
  have hagg_endow_nonneg : ∀ l, 0 ≤ ∑ a, E.endow a l :=
    fun l => Finset.sum_nonneg fun a _ => E.endow_mem a l
  have hEtot_nonneg : 0 ≤ Etot :=
    Finset.sum_nonneg fun l _ => hagg_endow_nonneg l
  have hagg_alloc_le : ∀ᶠ k in Filter.atTop, ∀ l,
      ∑ a, xall (φ k) a l ≤ 2 * Etot := by
    set q : Fin L → ℝ := fun _ => 1 / (↑L : ℝ) with hq_def
    have hq_pos : ∀ l, 0 < q l := fun _ => by simp only [hq_def]; positivity
    have hq_simplex : q ∈ priceSimplex L := by
      exact ⟨fun l => (hq_pos l).le, by simp [hq_def, Fintype.card_fin, ne_of_gt hLR]⟩
    filter_upwards [h_dot_le q hq_simplex hq_pos] with k hk l
    have h_sum_le : ∑ l', zall (φ k) l' ≤ 0 := by
      have hdot : q ⬝ᵥ zall (φ k) = (1 / ↑L) * ∑ l', zall (φ k) l' := by
        simp only [dotProduct, hq_def]; rw [Finset.mul_sum]
      nlinarith [div_pos one_pos hLR]
    have hz_lower : ∀ l', -(∑ a, E.endow a l') ≤ zall (φ k) l' := by
      intro l'
      have hagg_x_nonneg : 0 ≤ ∑ a, xall (φ k) a l' :=
        Finset.sum_nonneg fun a _ =>
          (E.demand_subset_budgetSet (p (φ k)) a (hxall_dem (φ k) a)).1 l'
      simp only [hzall_def, aggregateExcess]
      linarith
    have hz_l_le : zall (φ k) l ≤ Etot := by
      have h_split := (Finset.add_sum_erase (f := zall (φ k)) _ (Finset.mem_univ l)).symm
      have h_tail_ge : -(∑ l' ∈ Finset.univ.erase l, ∑ a, E.endow a l') ≤
          ∑ l' ∈ Finset.univ.erase l, zall (φ k) l' := by
        rw [neg_le_iff_add_nonneg, ← Finset.sum_add_distrib]
        exact Finset.sum_nonneg fun l' _ => by linarith [hz_lower l']
      have h_sub_le : ∑ l' ∈ Finset.univ.erase l, ∑ a, E.endow a l' ≤ Etot :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset l Finset.univ)
          (fun l' _ _ => hagg_endow_nonneg l')
      linarith
    have h_agg_eq : ∑ a, xall (φ k) a l =
        zall (φ k) l + ∑ a, E.endow a l := by
      simp only [hzall_def, aggregateExcess]; ring
    have h_endow_l_le : ∑ a, E.endow a l ≤ Etot :=
      Finset.single_le_sum (fun l' _ => hagg_endow_nonneg l') (Finset.mem_univ l)
    rw [h_agg_eq]; linarith
  set B : E.Agents → ℝ := fun _ => 2 * Etot with hB_def
  have hB_nonneg : ∀ a, 0 ≤ B a := fun a => by
    simp only [hB_def]; linarith [hEtot_nonneg]
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hagg_alloc_le
  set box : Set (E.Agents → Fin L → ℝ) :=
    Set.pi Set.univ (fun a => Set.pi Set.univ (fun _ : Fin L => Set.Icc (0 : ℝ) (B a)))
    with hbox_def
  have hbox_compact : IsCompact box :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  set xseq : ℕ → E.Agents → Fin L → ℝ := fun n => xall (φ (n + K₀)) with hxseq_def
  have hxseq_box : ∀ n, xseq n ∈ box := by
    intro n
    simp only [hbox_def, hxseq_def, Set.mem_univ_pi, Set.mem_Icc]
    intro a l
    refine ⟨(E.demand_subset_budgetSet (p (φ (n + K₀))) a (hxall_dem (φ (n + K₀)) a)).1 l, ?_⟩
    have hsingle_le : xall (φ (n + K₀)) a l ≤ ∑ a', xall (φ (n + K₀)) a' l :=
      Finset.single_le_sum
        (fun a' _ => (E.demand_subset_budgetSet (p (φ (n + K₀))) a'
          (hxall_dem (φ (n + K₀)) a')).1 l) (Finset.mem_univ a)
    have hagg_le := hK₀ (n + K₀) (by omega) l
    rw [hB_def]
    linarith
  obtain ⟨xstar, hxstar_mem, ψ, hψ_mono, hx_conv⟩ := hbox_compact.tendsto_subseq hxseq_box
  set χ : ℕ → ℕ := fun n => φ (ψ n + K₀) with hχ_def
  have hχ_mono : StrictMono χ := fun a b hab =>
    hφ_mono (Nat.add_lt_add_right (hψ_mono hab) K₀)
  have hpχ_tendsto : Filter.Tendsto (fun n => p (χ n)) Filter.atTop (nhds pstar) := by
    have : Filter.Tendsto (fun n => ψ n + K₀) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b =>
        ⟨b, fun n hn => le_trans hn (le_trans (hψ_mono.id_le n) (Nat.le_add_right (ψ n) K₀))⟩
    exact (hp_tendsto.comp this)
  have hxχ_tendsto : Filter.Tendsto (fun n => xall (χ n)) Filter.atTop (nhds xstar) := hx_conv
  have hxχ_agent : ∀ a, Filter.Tendsto (fun n => xall (χ n) a) Filter.atTop (nhds (xstar a)) :=
    fun a => ((continuous_apply a).tendsto _).comp hxχ_tendsto
  have hdot_tendsto : ∀ (s : ℕ → Fin L → ℝ) (sstar : Fin L → ℝ),
      Filter.Tendsto s Filter.atTop (nhds sstar) →
      Filter.Tendsto (fun n => p (χ n) ⬝ᵥ s n) Filter.atTop (nhds (pstar ⬝ᵥ sstar)) :=
    fun s sstar hs => ((continuous_fst.dotProduct continuous_snd).tendsto _).comp
      (hpχ_tendsto.prodMk_nhds hs)
  have hxstar_nn : ∀ a l, 0 ≤ xstar a l := by
    intro a l
    have := (Set.mem_univ_pi.mp hxstar_mem) a
    exact ((Set.mem_univ_pi.mp this) l).1
  have hbudget_bind : ∀ a, pstar ⬝ᵥ xstar a = pstar ⬝ᵥ E.endow a := by
    intro a
    have h_le_ev : ∀ n, p (χ n) ⬝ᵥ xall (χ n) a = p (χ n) ⬝ᵥ E.endow a :=
      fun n => E.demand_budget_binds hreg a (hxall_dem (χ n) a)
    have h_lhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ xall (χ n) a) Filter.atTop
        (nhds (pstar ⬝ᵥ xstar a)) :=
      hdot_tendsto _ _ (hxχ_agent a)
    have h_rhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ E.endow a) Filter.atTop
        (nhds (pstar ⬝ᵥ E.endow a)) :=
      hdot_tendsto _ _ tendsto_const_nhds
    exact tendsto_nhds_unique (h_lhs.congr h_le_ev) h_rhs
  have hquasi : ∀ (a : E.Agents) (y : Fin L → ℝ), (∀ l, 0 ≤ y l) →
      pstar ⬝ᵥ y < pstar ⬝ᵥ E.endow a → ¬ (y ≻[E.pref a] xstar a) := by
    intro a y hy_nn hy_strict
    suffices hge : xstar a ∈ (E.pref a).upperContour y by
      intro hlt; exact hlt.2 hge
    have h_ev_feasible : ∀ᶠ n in Filter.atTop, y ∈ E.budgetSet (p (χ n)) a := by
      have h_lhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ y) Filter.atTop (nhds (pstar ⬝ᵥ y)) :=
        hdot_tendsto _ _ tendsto_const_nhds
      have h_rhs : Filter.Tendsto (fun n => p (χ n) ⬝ᵥ E.endow a) Filter.atTop
          (nhds (pstar ⬝ᵥ E.endow a)) :=
        hdot_tendsto _ _ tendsto_const_nhds
      have h_lt := h_lhs.eventually_lt h_rhs hy_strict
      filter_upwards [h_lt] with n hn
      exact ⟨hy_nn, hn.le⟩
    have h_upper_ev : ∀ᶠ n in Filter.atTop, xall (χ n) a ∈ (E.pref a).upperContour y := by
      filter_upwards [h_ev_feasible] with n hn
      exact (hxall_dem (χ n) a).2 y hn
    have h_closed : IsClosed ((E.pref a).upperContour y) :=
      (hreg.contPref a).closed_upper y
    exact h_closed.mem_of_tendsto (hxχ_agent a) h_upper_ev
  have hIR : ∀ a, xstar a ≽[E.pref a] E.endow a := by
    intro a
    have h_endow_feasible : ∀ n, E.endow a ∈ E.budgetSet (p (χ n)) a :=
      fun n => E.endow_mem_budgetSet (p (χ n)) a
    have h_upper_ev : ∀ᶠ n in Filter.atTop,
        xall (χ n) a ∈ (E.pref a).upperContour (E.endow a) := by
      filter_upwards with n
      exact (hxall_dem (χ n) a).2 (E.endow a) (h_endow_feasible n)
    have h_closed : IsClosed ((E.pref a).upperContour (E.endow a)) :=
      (hreg.contPref a).closed_upper (E.endow a)
    exact h_closed.mem_of_tendsto (hxχ_agent a) h_upper_ev
  have hxstar_bud : ∀ a, xstar a ∈ E.budgetSet pstar a :=
    fun a => ⟨fun l => hxstar_nn a l, le_of_eq (hbudget_bind a)⟩
  have hmc : E.MarketClears pstar xstar := by
    set zstar : Fin L → ℝ := E.aggregateExcess xstar with hzstar_def
    have h_walras : pstar ⬝ᵥ zstar = 0 := by
      rw [hzstar_def, E.dotProduct_aggregateExcess]
      have hbind' : (fun a => pstar ⬝ᵥ (xstar a) - pstar ⬝ᵥ E.endow a)
          = fun _ : E.Agents => (0 : ℝ) := by
        funext a; rw [hbudget_bind a, sub_self]
      rw [hbind', Finset.sum_const_zero]
    have hz_tendsto : Filter.Tendsto (fun n => zall (χ n)) Filter.atTop (nhds zstar) :=
      (E.continuous_aggregateExcess.tendsto _).comp hxχ_tendsto
    have h_dot_star_le : ∀ q : Fin L → ℝ, q ∈ priceSimplex L → (∀ l, 0 < q l) →
        q ⬝ᵥ zstar ≤ 0 := by
      intro q hq hq_pos
      have h_dot_χ_tendsto : Filter.Tendsto (fun n => q ⬝ᵥ zall (χ n)) Filter.atTop
          (nhds (q ⬝ᵥ zstar)) :=
        ((continuous_const.dotProduct continuous_id).tendsto _).comp hz_tendsto
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_dot_le q hq hq_pos)
      have h_ev_nonpos : ∀ᶠ n in Filter.atTop, q ⬝ᵥ zall (χ n) ≤ 0 := by
        have hψshift : Filter.Tendsto (fun n => ψ n + K₀) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_atTop.mpr fun b =>
            ⟨b, fun n hn => le_trans hn (le_trans (hψ_mono.id_le n) (Nat.le_add_right _ K₀))⟩
        filter_upwards [hψshift.eventually (Filter.eventually_atTop.mpr ⟨N, fun m hm => hm⟩)]
          with n hn
        exact hN (ψ n + K₀) hn
      exact le_of_tendsto h_dot_χ_tendsto h_ev_nonpos
    have hz_nonpos : ∀ l, zstar l ≤ 0 :=
      coord_nonpos_of_interior_dotProduct_nonpos hL h_dot_star_le
    exact ⟨hz_nonpos, h_walras⟩
  exact ⟨pstar, xstar, hp_mem, hxstar_bud, hbudget_bind, hIR, hquasi, hmc⟩

/-- **McKenzie's upgrade** (McKenzie 1959). A quasi-equilibrium is a Walrasian equilibrium under
irreducibility: Irreducibility forces all prices and all agent wealths to be strictly positive,
giving full demand-optimality. Returns `(∀ l, 0 < p l)` and `(∀ a, x a ∈ E.demand p a)`. -/
lemma quasi_to_walrasian (E : Economy L) [Finite E.Agents] (hne : Nonempty E.Agents)
    (hcont : ∀ a, Econlib.Preferences.ContinuousPref (E.pref a))
    (hdes : ∀ a, Econlib.Preferences.Desirable (E.pref a)) (hirr : Irreducible E)
    {p : Fin L → ℝ} {x : E.Agents → Fin L → ℝ}
    (hp_mem : p ∈ priceSimplex L)
    (hbud : ∀ a, x a ∈ E.budgetSet p a)
    (hbind : ∀ a, p ⬝ᵥ x a = p ⬝ᵥ E.endow a)
    (hIR : ∀ a, x a ≽[E.pref a] E.endow a)
    (hquasi : ∀ a y, (∀ l, 0 ≤ y l) → p ⬝ᵥ y < p ⬝ᵥ E.endow a → ¬ (y ≻[E.pref a] x a))
    (hagg : ∃ a, 0 < p ⬝ᵥ E.endow a) :
    (∀ l, 0 < p l) ∧ (∀ a, x a ∈ E.demand p a) := by
  classical
  letI : Fintype E.Agents := Fintype.ofFinite _
  have hp_nn : ∀ l, 0 ≤ p l := fun l => hp_mem.1 l
  have hx_nn : ∀ a l, 0 ≤ x a l := fun a => (hbud a).1
  have hw_nn : ∀ a, 0 ≤ p ⬝ᵥ E.endow a := fun a =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hp_nn l) (E.endow_mem a l)
  -- Any bundle strictly preferred to `x a` by a positive-wealth agent costs strictly more than
  -- wealth; a cheaper approximate would contradict `hquasi` via a ray toward 0.
  have strict_exp : ∀ (a : E.Agents) (z : Fin L → ℝ), 0 < p ⬝ᵥ E.endow a → (∀ l, 0 ≤ z l) →
      (z ≻[E.pref a] (x a)) → p ⬝ᵥ E.endow a < p ⬝ᵥ z := by
    intro a z hwa hz_nn hz_pref
    by_contra hge; push Not at hge
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact hquasi a z hz_nn hlt hz_pref
    · -- Equal cost: `g s = (1-s)·z` is strictly cheaper for `s > 0`, still preferred.
      set g : ℝ → Fin L → ℝ := fun s l => (1 - s) * z l with hg_def
      have hg_cont : Continuous g := by
        refine continuous_pi fun l => ?_
        simp only [hg_def]
        exact (continuous_const.sub continuous_id).mul continuous_const
      have hg0 : g 0 = z := by funext l; simp only [hg_def]; ring
      have h_open : IsOpen {w | w ≻[E.pref a] x a} :=
        (hcont a).isOpen_strictUpperContour (x a)
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
      have h_cheap_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0),
          p ⬝ᵥ g s < p ⬝ᵥ E.endow a := by
        refine eventually_nhdsWithin_of_forall fun s hs_pos => ?_
        have hs_pos' : 0 < s := hs_pos
        have hdot : p ⬝ᵥ g s = (1 - s) * (p ⬝ᵥ z) := by
          simp only [hg_def, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hdot, ← heq]
        nlinarith [hs_pos', hwa, heq]
      obtain ⟨s, hs_pref, hs_nn, hs_cheap⟩ :
          ∃ s, g s ∈ {w | w ≻[E.pref a] x a} ∧ (∀ l, 0 ≤ g s l) ∧
            p ⬝ᵥ g s < p ⬝ᵥ E.endow a := by
        have hev := ((h_pref_ev.filter_mono nhdsWithin_le_nhds).and (h_nn_ev.and h_cheap_ev))
        obtain ⟨s, hs⟩ := hev.exists
        exact ⟨s, hs.1, hs.2.1, hs.2.2⟩
      exact hquasi a (g s) hs_nn hs_cheap hs_pref
  have wealth_pos : ∀ a, 0 < p ⬝ᵥ E.endow a := by
    by_contra h
    push Not at h
    obtain ⟨a_zero, ha_zero_le⟩ := h
    have ha_zero : p ⬝ᵥ E.endow a_zero = 0 := le_antisymm ha_zero_le (hw_nn a_zero)
    -- `T` = zero-wealth agents; `S` = positive-wealth agents.
    set T : Finset E.Agents := Finset.univ.filter (fun a => p ⬝ᵥ E.endow a = 0) with hT_def
    set S : Finset E.Agents := Finset.univ.filter (fun a => p ⬝ᵥ E.endow a ≠ 0) with hS_def
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
    obtain ⟨y, hy_improve, hy_resource⟩ :=
      hirr.improve x hx_nn hIR S T hS_ne hT_ne hdisj
    have hS_wealth : ∀ i ∈ S, 0 < p ⬝ᵥ E.endow i := by
      intro i hi
      simp only [hS_def, Finset.mem_filter] at hi
      exact lt_of_le_of_ne (hw_nn i) (Ne.symm hi.2)
    have hexp : ∀ i ∈ S, p ⬝ᵥ E.endow i < p ⬝ᵥ y i := by
      intro i hi
      exact strict_exp i (y i) (hS_wealth i hi) (hy_improve i hi).1 (hy_improve i hi).2
    have hsum_strict : (∑ i ∈ S, p ⬝ᵥ E.endow i) < ∑ i ∈ S, p ⬝ᵥ y i :=
      Finset.sum_lt_sum_of_nonempty hS_ne hexp
    have h_dot_resource : (∑ i ∈ S, p ⬝ᵥ y i) ≤
        (∑ i ∈ S, p ⬝ᵥ x i) + ∑ j ∈ T, p ⬝ᵥ E.endow j := by
      have hdotsum : ∀ (X : E.Agents → Fin L → ℝ) (U : Finset E.Agents),
          (∑ i ∈ U, p ⬝ᵥ X i) = ∑ l, p l * (∑ i ∈ U, X i l) := fun X U => by
        simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
      have hLHS : (∑ i ∈ S, p ⬝ᵥ y i) = ∑ l, p l * (∑ i ∈ S, y i l) := hdotsum y S
      have hRHS : (∑ i ∈ S, p ⬝ᵥ x i) + ∑ j ∈ T, p ⬝ᵥ E.endow j =
          ∑ l, p l * ((∑ i ∈ S, x i l) + ∑ j ∈ T, E.endow j l) := by
        rw [hdotsum x S, hdotsum E.endow T, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      rw [hLHS, hRHS]
      refine Finset.sum_le_sum fun l _ => ?_
      exact mul_le_mul_of_nonneg_left (hy_resource l) (hp_nn l)
    have h_xS : (∑ i ∈ S, p ⬝ᵥ x i) = ∑ i ∈ S, p ⬝ᵥ E.endow i :=
      Finset.sum_congr rfl fun i _ => hbind i
    have h_eT : (∑ j ∈ T, p ⬝ᵥ E.endow j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [hT_def, Finset.mem_filter] at hj
      exact hj.2
    rw [h_xS, h_eT, add_zero] at h_dot_resource
    linarith
  have hp_pos : ∀ l, 0 < p l := by
    by_contra h_neg; push Not at h_neg
    obtain ⟨l₀, hl₀⟩ := h_neg
    have hl₀_eq : p l₀ = 0 := le_antisymm hl₀ (hp_nn l₀)
    obtain ⟨a₀⟩ := hne
    have h_endow_pos : 0 < p ⬝ᵥ E.endow a₀ := wealth_pos a₀
    have h_xstar_dot_pos : 0 < p ⬝ᵥ x a₀ := by
      rw [hbind a₀]; exact h_endow_pos
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
    -- `y₀ = x a₀ + e_{l₀}` costs the same as `x a₀` (since `p l₀ = 0`) but is weakly larger.
    set y₀ : Fin L → ℝ := fun l => x a₀ l + (if l = l₀ then 1 else 0) with hy₀_def
    have hy₀_nn : ∀ l, 0 ≤ y₀ l := fun l => by
      simp only [hy₀_def]; split <;> linarith [hx_nn a₀ l]
    have h_le : x a₀ ≤ y₀ := fun l => by simp only [hy₀_def]; split <;> linarith
    have h_ne : x a₀ ≠ y₀ := fun heq => by
      have hcontra := congr_fun heq.symm l₀
      simp only [hy₀_def, if_true] at hcontra; linarith
    have h_y₀_pref : y₀ ≻[E.pref a₀] x a₀ := by
      -- The constant interior bundle `δ·𝟙` is cheaper than the (positive) wealth, so the
      -- quasi-optimal `x a₀` weakly beats it; desirability then improves along `y₀`.
      set δ : ℝ := p ⬝ᵥ E.endow a₀ / 2 with hδ_def
      have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
      have hz_pos : ∀ l, 0 < (fun _ : Fin L => δ) l := fun _ => hδ_pos
      have hz_cheap : p ⬝ᵥ (fun _ : Fin L => δ) < p ⬝ᵥ E.endow a₀ := by
        have hsum : p ⬝ᵥ (fun _ : Fin L => δ) = δ := by
          simp only [dotProduct]
          rw [← Finset.sum_mul, hp_mem.2, one_mul]
        rw [hsum, hδ_def]; linarith
      have hx_ge_z : x a₀ ≽[E.pref a₀] (fun _ : Fin L => δ) := by
        by_contra hge
        have hle' : (fun _ : Fin L => δ) ≽[E.pref a₀] x a₀ :=
          ((E.pref a₀).le_total (fun _ : Fin L => δ) (x a₀)).resolve_right hge
        exact hquasi a₀ (fun _ : Fin L => δ) (fun _ => hδ_pos.le) hz_cheap ⟨hle', hge⟩
      exact (hdes a₀).improve hz_pos hx_ge_z h_le h_ne
    have h_dot_y₀ : p ⬝ᵥ y₀ = p ⬝ᵥ x a₀ := by
      simp only [dotProduct, hy₀_def, mul_add]
      rw [Finset.sum_add_distrib]
      have hzero : ∑ l, p l * (if l = l₀ then (1:ℝ) else 0) = 0 := by
        rw [Finset.sum_eq_single l₀]
        · rw [if_pos rfl, hl₀_eq]; ring
        · intro l _ hl; rw [if_neg hl]; ring
        · intro h; exact absurd (Finset.mem_univ l₀) h
      rw [hzero, add_zero]
    -- Perturb: `f t = y₀ - t·e_{l'}` is cheaper than `y₀` for `t > 0`, still preferred.
    set f : ℝ → Fin L → ℝ := fun t l => y₀ l - t * (if l = l' then 1 else 0) with hf_def
    have hf_cont : Continuous f := by
      refine continuous_pi fun l => ?_
      simp only [hf_def]
      exact continuous_const.sub (continuous_id.mul continuous_const)
    have hf0 : f 0 = y₀ := by funext l; simp only [hf_def]; ring
    have h_open : IsOpen {w | w ≻[E.pref a₀] x a₀} :=
      (hcont a₀).isOpen_strictUpperContour (x a₀)
    have h_mem0 : f 0 ∈ {w | w ≻[E.pref a₀] x a₀} := by rw [hf0]; exact h_y₀_pref
    have h_pref_ev : ∀ᶠ t in nhds (0:ℝ), f t ∈ {w | w ≻[E.pref a₀] x a₀} :=
      (hf_cont.tendsto 0).eventually (h_open.mem_nhds h_mem0)
    have h_nn_ev : ∀ᶠ t in nhds (0:ℝ), ∀ l, 0 ≤ f t l := by
      have hy₀l' : 0 < y₀ l' := by
        simp only [hy₀_def]; rw [if_neg (Ne.symm hl₀_ne)]; simpa using hl'_alloc
      have h_l'_pos : ∀ᶠ t in nhds (0:ℝ), 0 < f t l' := by
        have hcont_l' : Continuous (fun t => f t l') :=
          (continuous_apply l').comp hf_cont
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
    have h_ft_cheap : p ⬝ᵥ f t < p ⬝ᵥ E.endow a₀ := by
      rw [ht_cheap, hbind a₀]
      linarith [mul_pos ht_pos hl'_price]
    exact hquasi a₀ (f t) ht_nn h_ft_cheap ht_pref
  refine ⟨hp_pos, fun a => ?_⟩
  have hquasi_ge : ∀ (a : E.Agents) (y : Fin L → ℝ), (∀ l, 0 ≤ y l) →
      p ⬝ᵥ y < p ⬝ᵥ E.endow a → (x a ≽[E.pref a] y) := by
    intro a y hy_nn hy_strict
    by_contra hge
    have hle : y ≽[E.pref a] x a := ((E.pref a).le_total y (x a)).resolve_right hge
    exact hquasi a y hy_nn hy_strict ⟨hle, hge⟩
  have hx_bud : x a ∈ E.budgetSet p a :=
    ⟨fun l => hx_nn a l, le_of_eq (hbind a)⟩
  refine ⟨hx_bud, fun y hy => ?_⟩
  have hy_nn : ∀ l, 0 ≤ y l := hy.1
  have hy_le : p ⬝ᵥ y ≤ p ⬝ᵥ E.endow a := hy.2
  rcases lt_or_eq_of_le hy_le with hlt | heq_cost
  · exact hquasi_ge a y hy_nn hlt
  · -- Equal cost: approximate `y` by `g s = (1-s)·y`, strictly cheaper for `s > 0`.
    have hwealth_lt : (0 : ℝ) < p ⬝ᵥ E.endow a := wealth_pos a
    set g : ℝ → Fin L → ℝ := fun s l => (1 - s) * y l with hg_def
    have hg_cont : Continuous g := by
      refine continuous_pi fun l => ?_
      simp only [hg_def]
      exact (continuous_const.sub continuous_id).mul continuous_const
    have hg0 : g 0 = y := by funext l; simp only [hg_def]; ring
    have h_upper_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0),
        g s ∈ {w : Fin L → ℝ | x a ≽[E.pref a] w} := by
      have h_nn_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ l, 0 ≤ g s l := by
        have hs1 : ∀ᶠ s in nhds (0:ℝ), s ≤ 1 :=
          eventually_le_nhds (by norm_num)
        refine ((hs1.filter_mono nhdsWithin_le_nhds).and
          (eventually_nhdsWithin_of_forall (fun s hs => hs))).mono ?_
        intro s ⟨hs_le1, _hs_pos⟩ l
        simp only [hg_def]
        exact mul_nonneg (by linarith) (hy_nn l)
      have h_cheap_ev : ∀ᶠ s in nhdsWithin (0:ℝ) (Set.Ioi 0),
          p ⬝ᵥ g s < p ⬝ᵥ E.endow a := by
        refine eventually_nhdsWithin_of_forall fun s hs_pos => ?_
        have hs_pos' : 0 < s := hs_pos
        have hdot : p ⬝ᵥ g s = (1 - s) * (p ⬝ᵥ y) := by
          simp only [hg_def, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hdot, heq_cost]
        nlinarith [hs_pos', hwealth_lt]
      filter_upwards [h_nn_ev, h_cheap_ev] with s hs_nn hs_cheap
      exact hquasi_ge a (g s) hs_nn hs_cheap
    have hg_tendsto : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds y) := by
      rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    have h_closed_lower : IsClosed {w : Fin L → ℝ | x a ≽[E.pref a] w} :=
      (hcont a).closed_lower (x a)
    exact h_closed_lower.mem_of_tendsto hg_tendsto h_upper_ev

/-- For a regular, irreducible economy in which every good is owned by some agent, there exist
nonnegative prices (with at least one strictly positive) and a market-clearing allocation at which
every consumer optimizes. -/
lemma exists_equilibrium_data (E : Economy L) [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hirr : Irreducible E) (hL : 0 < L)
    (hagg_endow : ∀ l, ∃ a, 0 < E.endow a l) :
    ∃ (p : Fin L → ℝ) (x : E.Agents → Fin L → ℝ),
      (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a, x a ∈ E.demand p a) ∧ E.MarketClears p x := by
  obtain ⟨p, x, hp_mem, hbud, hbind, hIR, hquasi, hclears⟩ :=
    E.exists_quasi_equilibrium hne hreg hL
  obtain ⟨l₀, hl₀⟩ := priceSimplex_exists_pos hp_mem
  obtain ⟨a₀, ha₀⟩ := hagg_endow l₀
  have hagg : ∃ a, 0 < p ⬝ᵥ E.endow a := by
    refine ⟨a₀, ?_⟩
    have hterm : ∀ l ∈ Finset.univ, 0 ≤ p l * E.endow a₀ l :=
      fun l _ => mul_nonneg (hp_mem.1 l) (E.endow_mem a₀ l)
    calc (0 : ℝ) < p l₀ * E.endow a₀ l₀ := mul_pos hl₀ ha₀
      _ ≤ ∑ l, p l * E.endow a₀ l := Finset.single_le_sum hterm (Finset.mem_univ l₀)
      _ = p ⬝ᵥ E.endow a₀ := rfl
  obtain ⟨hp_pos, hopt⟩ :=
    E.quasi_to_walrasian hne hreg.contPref hreg.desirable hirr hp_mem hbud hbind hIR hquasi hagg
  exact ⟨p, x, fun l => (hp_pos l).le, ⟨l₀, hl₀⟩, hopt, hclears⟩

/-- **Existence of a Walrasian equilibrium (general convex case)** (Arrow and Debreu 1954; McKenzie
1959). Under `RegularEconomy`, McKenzie irreducibility, and the ownership condition (every good is
owned by some agent), a Walrasian equilibrium exists without requiring strict concavity or
single-valued demand. -/
theorem exists_equilibrium (E : Economy L) [Finite E.Agents] (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hirr : Irreducible E) (hL : 0 < L)
    (hagg_endow : ∀ l, ∃ a, 0 < E.endow a l) :
    Nonempty E.WalrasianEquilibrium := by
  obtain ⟨p, x, hp_nn, hp_ne, hopt, hclears⟩ :=
    E.exists_equilibrium_data hne hreg hirr hL hagg_endow
  exact ⟨⟨p, x, hp_nn, hp_ne, hopt, hclears⟩⟩

end Economy

end Econlib.Equilibrium
