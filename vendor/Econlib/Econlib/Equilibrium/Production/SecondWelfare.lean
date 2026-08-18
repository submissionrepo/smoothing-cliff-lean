/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Production.Welfare
public import Econlib.Equilibrium.SecondWelfare
public import Econlib.Math.LinearAlgebra.ContinuousLinearMap
public import Econlib.Math.Order.AffineInequalities
public import Econlib.Math.Topology.MinkowskiSum

/-!
# Second Welfare Theorem with production

This file contains Second Welfare Theorem results for Arrow–Debreu private-ownership production
economies. The results start from a Pareto optimal feasible allocation `(x, y)`, where `x` is the
consumer allocation and `y` is the firm production plan.

The supporting-price theorems produce a nonnegative nonzero price vector. Consumers are supported
in the sense that every nonnegative bundle strictly preferred to `x a` costs at least `x a`; firms
are supported in the sense that each `y j` maximizes profit over its technology. The
quasi-equilibrium theorem adds budget maximality for agents whose transfer budget `p ⬝ᵥ x a` is
strictly positive.

The strongest result,
`ProductionEconomy.ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers`,
decentralizes the given Pareto optimum as a `WalrasianEquilibriumWithProductionAndTransfers`. It
assumes every good is consumed and that the exchange economy whose endowments are relabeled to the
allocation `x` is McKenzie-irreducible. The returned equilibrium keeps exactly the allocation `x`
and production plan `y`, uses balanced lump-sum transfers, and gives every agent a budget-maximal
bundle.

## Main statements

* `ProductionEconomy.ParetoOptimal.exists_consumer_supporting_price`: A Pareto optimum admits
  nonnegative nonzero prices supporting each consumer's assigned bundle.
* `ProductionEconomy.ParetoOptimal.exists_supporting_price`: The same prices also support each
  firm's assigned production plan as profit-maximizing.
* `ProductionEconomy.ParetoOptimal.exists_quasiEquilibrium_price`: Positive-wealth agents are
  budget-maximal in their transfer budget sets, and firms maximize profit.
* `ProductionEconomy.ParetoOptimal.aggregateExcess_value_zero_prod`: Aggregate excess demand is
  zero-valued at a supported optimum with a positive-wealth agent, giving balanced transfers.
* `ProductionEconomy.ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers`: **Full
  decentralization.** Under every-good-consumed (`hcons`) and relabeled-economy irreducibility
  (`hirr`), `(x, y)` is implemented by a `WalrasianEquilibriumWithProductionAndTransfers`.

## References

* Arrow, Kenneth J. 1951. “An Extension of the Basic Theorems of Classical Welfare Economics.” In
  *Proceedings of the Second Berkeley Symposium on Mathematical Statistics and Probability*, edited
  by Jerzy Neyman. University of California Press.
* Debreu, Gerard. 1951. “The Coefficient of Resource Utilization.” *Econometrica* 19 (3): 273.
  [https://doi.org/10.2307/1906814](https://doi.org/10.2307/1906814).
* McKenzie, Lionel W. 1959. “On the Existence of General Equilibrium for a Competitive Market.”
  *Econometrica* 27 (1): 54. [https://doi.org/10.2307/1907777](https://doi.org/10.2307/1907777).

## Tags

welfare theorem, production economy, pareto optimality, decentralization, transfers
-/

@[expose] public section

open Finset BigOperators Matrix Pointwise Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

namespace ProductionEconomy

variable (E : ProductionEconomy L)

/-! ### Functional-analytic helpers -/

/-- For a regular economy and nonneg `x j`, `c`, any `δ > 0` puts `x j + c + δ • 𝟙` in
`strictlyPreferredPos x j`. -/
private lemma perturb_mem_strictlyPreferredPos {E' : Economy L} (hreg' : RegularEconomy E')
    (hL : 0 < L) {x : E'.Agents → Fin L → ℝ} (hx_nn : ∀ a l, 0 ≤ x a l)
    (j : E'.Agents) (c : Fin L → ℝ) (hc : ∀ l, 0 ≤ c l) (δ : ℝ) (hδ : 0 < δ) :
    x j + c + δ • (fun _ => (1 : ℝ)) ∈ E'.strictlyPreferredPos x j := by
  refine ⟨?_, fun l => ?_⟩
  · refine (hreg'.mono j).strictMono (fun l => ?_) (fun heq => ?_) (fun l => ?_)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]; linarith [hc l]
    · have := congr_fun heq ⟨0, hL⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one] at this
      linarith [hc ⟨0, hL⟩]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      linarith [hx_nn j l, hc l]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    linarith [hx_nn j l, hc l]

variable {E}

/-! ### Consumer support -/

/-- **Second Welfare Theorem with production — consumer support** (Arrow 1951; Debreu 1951). For a
regular production economy, every Pareto optimal allocation `(x, y)` admits a nonnegative nonzero
price `p` supporting consumers: Any nonneg bundle strictly preferred to `x a` costs at least
`p ⬝ᵥ x a`. -/
theorem ParetoOptimal.exists_consumer_supporting_price (hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ}
    (hpo : E.ParetoOptimal x y) :
    ∃ p : Fin L → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      ∀ a z, z ∈ nonnegOrthant L → (z ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ z := by
  classical
  have hregE : RegularEconomy E.toEconomy := hreg.toRegularEconomy
  have hx_nn : ∀ a l, 0 ≤ x a l := hpo.feasible.nonneg
  set one : Fin L → ℝ := fun _ => (1 : ℝ) with hone
  set S : E.Agents → Set (Fin L → ℝ) := fun a => E.toEconomy.strictlyPreferredPos x a with hS
  set P : Set (Fin L → ℝ) := ∑ a : E.Agents, S a with hP
  set w : Fin L → ℝ := fun l => ∑ a, x a l with hw
  set I : ℕ := Fintype.card E.Agents with hI
  have hS_open : ∀ a, IsOpen (S a) := fun a => Economy.strictlyPreferredPos_isOpen hregE x a
  have hS_convex : ∀ a, Convex ℝ (S a) := fun a => Economy.strictlyPreferredPos_convex hregE x a
  have hS_ne : ∀ a, (S a).Nonempty :=
    fun a => Economy.strictlyPreferredPos_nonempty hregE hL hx_nn a
  have hP_open : IsOpen P :=
    isOpen_finset_sum_of_nonempty Finset.univ_nonempty (fun a _ => hS_open a)
  have hP_convex : Convex ℝ P := convex_sum _ (fun a _ => hS_convex a)
  have hP_ne : P.Nonempty :=
    ⟨∑ a, (hS_ne a).some,
      Set.finset_sum_mem_finset_sum _ _ _ (fun a _ => (hS_ne a).some_mem)⟩
  have hS_mem : ∀ {a : E.Agents} {z : Fin L → ℝ},
      z ∈ S a ↔ (z ≻[E.pref a] x a) ∧ ∀ l, 0 < z l := fun {a z} => Iff.rfl
  have hperturb_mem : ∀ (j : E.Agents) (c : Fin L → ℝ) (_hc : ∀ l, 0 ≤ c l) (δ : ℝ), 0 < δ →
      x j + c + δ • one ∈ S j :=
    fun j c hc δ hδ => perturb_mem_strictlyPreferredPos hregE hL hx_nn j c hc δ hδ
  -- `w ∉ P`: any decomposition of `w` into strictly-preferred bundles yields a feasible
  -- Pareto-dominating allocation paired with the same plan `y`.
  have hw_notin : w ∉ P := by
    rw [hP]
    intro hmem
    rw [Set.mem_finset_sum] at hmem
    obtain ⟨g, hg_mem, hg_sum⟩ := hmem
    have hg_mem' : ∀ a, g a ∈ S a := fun a => hg_mem (Finset.mem_univ a)
    have hsum_eq : ∀ l, (∑ a, g a l) = w l := by
      intro l
      have := congr_fun hg_sum l
      simpa [Finset.sum_apply, hw] using this
    have h_feas : E.Feasible g y := by
      refine ⟨fun a l => ((hS_mem.mp (hg_mem' a)).2 l).le, hpo.feasible.plans_feasible, fun l => ?_⟩
      simp only [ProductionEconomy.aggregateExcess, hsum_eq l, hw]
      exact hpo.feasible.excess_nonpos l
    have h_dom : E.ParetoDominates g x := by
      refine ⟨fun a => ((hS_mem.mp (hg_mem' a)).1).1, ?_⟩
      exact ⟨hne.some, (hS_mem.mp (hg_mem' hne.some)).1⟩
    exact hpo.undominated ⟨g, y, h_feas, h_dom⟩
  obtain ⟨f, hf_sep⟩ := geometric_hahn_banach_open_point hP_convex hP_open hw_notin
  have hf_ne : f ≠ 0 := by
    intro hf0
    obtain ⟨z, hz⟩ := hP_ne
    have := hf_sep z hz
    simp [hf0] at this
  have hIR : (0 : ℝ) < I := by
    rw [hI]; exact_mod_cast Fintype.card_pos
  have hsingle_nn : ∀ (l₀ l : Fin L), 0 ≤ (Pi.single l₀ (1 : ℝ) : Fin L → ℝ) l := by
    intro l₀ l
    rw [Pi.single_apply]
    split <;> norm_num
  have h_basis_nonpos : ∀ l₀ : Fin L, f (Pi.single l₀ 1) ≤ 0 := by
    intro l₀
    have hstep : ∀ δ : ℝ, 0 < δ →
        (I : ℝ) * f one * δ + (I : ℝ) * f (Pi.single l₀ 1) ≤ 0 := by
      intro δ hδ
      have h_in_P : ∑ j, (x j + Pi.single l₀ (1 : ℝ) + δ • one) ∈ P :=
        hP ▸ Set.finset_sum_mem_finset_sum _ _ _
          (fun j _ => hperturb_mem j (Pi.single l₀ 1) (fun l => hsingle_nn l₀ l) δ hδ)
      have h_sep := hf_sep _ h_in_P
      have hsum : (∑ j, (x j + (Pi.single l₀ (1 : ℝ) : Fin L → ℝ) + δ • one))
          = w + (I : ℝ) • (Pi.single l₀ (1 : ℝ) : Fin L → ℝ) + (I : ℝ) • (δ • one) := by
        ext l
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw, hI]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ]
      rw [hsum, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul] at h_sep
      nlinarith [h_sep]
    nlinarith [affine_const_nonpos_of_forall_pos hstep, hIR]
  refine ⟨fun l => -(f (Pi.single l 1)), fun l => by linarith [h_basis_nonpos l], ?_, ?_⟩
  · by_contra h_all
    push Not at h_all
    apply hf_ne
    ext v
    rw [ContinuousLinearMap.pi_eq_dotProduct_single f v, ContinuousLinearMap.zero_apply]
    simp only [dotProduct]
    refine Finset.sum_eq_zero (fun l₀ _ => ?_)
    have h_ge : 0 ≤ f (Pi.single l₀ 1) := by linarith [h_all l₀]
    rw [le_antisymm (h_basis_nonpos l₀) h_ge, zero_mul]
  · intro a z hz_orth hz_lt
    rw [show (fun l => -(f (Pi.single l 1))) ⬝ᵥ x a = -(f (x a)) from
          ContinuousLinearMap.neg_dotProduct_single f (x a),
        show (fun l => -(f (Pi.single l 1))) ⬝ᵥ z = -(f z) from
          ContinuousLinearMap.neg_dotProduct_single f z]
    have hfw : f w = ∑ b, f (x b) := by
      have hweq : w = ∑ b, x b := by ext l; simp [hw, Finset.sum_apply]
      rw [hweq, map_sum]
    have h_weak_on_S : ∀ z ∈ S a, f z ≤ f (x a) := by
      intro z hz
      have hstep : ∀ δ : ℝ, 0 < δ →
          (∑ b ∈ Finset.univ.erase a, f one) * δ + (f z - f (x a)) ≤ 0 := by
        intro δ hδ
        set elem : E.Agents → Fin L → ℝ :=
          fun j => if j = a then z else x j + (0 : Fin L → ℝ) + δ • one with helem
        have h_elem_mem : ∀ j, elem j ∈ S j := by
          intro j
          simp only [helem]
          split_ifs with hj
          · subst hj; exact hz
          · exact hperturb_mem j 0 (fun l => le_refl 0) δ hδ
        have h_in_P : ∑ j, elem j ∈ P :=
          hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => h_elem_mem j)
        have h_sep := hf_sep _ h_in_P
        have h_fsum : f (∑ j, elem j) =
            f z + ∑ j ∈ Finset.univ.erase a, (f (x j) + δ * f one) := by
          rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [helem]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [helem, (Finset.mem_erase.mp hj).1, if_false, add_zero, map_add, map_smul,
              smul_eq_mul]
        have h_fw_split : f w = f (x a) + ∑ j ∈ Finset.univ.erase a, f (x j) := by
          rw [hfw, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
        rw [h_fsum, h_fw_split] at h_sep
        have hδsum : ∑ j ∈ Finset.univ.erase a, (f (x j) + δ * f one) =
            (∑ j ∈ Finset.univ.erase a, f (x j)) + (∑ b ∈ Finset.univ.erase a, f one) * δ := by
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_const, Finset.sum_const]
          ring
        rw [hδsum] at h_sep
        linarith
      linarith [affine_const_nonpos_of_forall_pos hstep]
    have hz_step : ∀ ε : ℝ, 0 < ε → f one * ε + (f z - f (x a)) ≤ 0 := by
      intro ε hε
      have hmem : z + ε • one ∈ S a := by
        rw [hS_mem]
        refine ⟨?_, fun l => ?_⟩
        · have hge : (z + ε • one) ≽[E.pref a] z :=
            ((hregE.mono a).strictMono
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
                linarith)
              (fun heq => by
                have := congr_fun heq ⟨0, hL⟩
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one] at this
                linarith)
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
                linarith [hz_orth l])).1
          exact (E.pref a).lt_of_le_of_lt hge hz_lt
        · simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
          linarith [hz_orth l]
      have hweak := h_weak_on_S _ hmem
      rw [map_add, map_smul, smul_eq_mul] at hweak
      linarith
    linarith [affine_const_nonpos_of_forall_pos hz_step]

/-- **Second Welfare Theorem with production — supporting prices.** For a regular production
economy, every Pareto optimal allocation `(x, y)` admits a nonnegative nonzero price `p` such that
any nonnegative bundle strictly preferred to `x a` is at least as expensive as `x a`, and every
firm's plan maximizes profit. This is the support half: It does not by itself assert that `x a` is
budget-maximal. `exists_quasiEquilibrium_price` upgrades the consumer side to budget-maximality at
positive-wealth agents (a price quasi-equilibrium with lump-sum transfers). -/
theorem ParetoOptimal.exists_supporting_price (hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ}
    (hpo : E.ParetoOptimal x y) :
    ∃ p : Fin L → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a z, z ∈ nonnegOrthant L → (z ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ z) ∧
      (∀ j, ∀ z ∈ (E.tech j).Y, p ⬝ᵥ z ≤ p ⬝ᵥ y j) := by
  classical
  have hregE : RegularEconomy E.toEconomy := hreg.toRegularEconomy
  have hx_nn : ∀ a l, 0 ≤ x a l := hpo.feasible.nonneg
  have hy_mem : ∀ j, y j ∈ (E.tech j).Y := hpo.feasible.plans_feasible
  set one : Fin L → ℝ := fun _ => (1 : ℝ) with hone
  set S : E.Agents → Set (Fin L → ℝ) := fun a => E.toEconomy.strictlyPreferredPos x a with hS
  set P : Set (Fin L → ℝ) := ∑ a : E.Agents, S a with hP
  set w : Fin L → ℝ := fun l => ∑ a, x a l with hw
  set eagg : Fin L → ℝ := fun l => ∑ a, E.endow a l with heagg
  -- `gy = eagg + ∑_j y j` is the optimal aggregate supply point.
  set gy : Fin L → ℝ := fun l => eagg l + ∑ j, y j l with hgy
  set I : ℕ := Fintype.card E.Agents with hI
  -- `G = eagg + ∑_j Y_j` is the aggregate feasible production set.
  set G : Set (Fin L → ℝ) :=
    {g | ∃ yy : E.Firms → Fin L → ℝ, (∀ j, yy j ∈ (E.tech j).Y) ∧
      g = fun l => eagg l + ∑ j, yy j l} with hG
  have hS_open : ∀ a, IsOpen (S a) := fun a => Economy.strictlyPreferredPos_isOpen hregE x a
  have hS_convex : ∀ a, Convex ℝ (S a) := fun a => Economy.strictlyPreferredPos_convex hregE x a
  have hS_ne : ∀ a, (S a).Nonempty :=
    fun a => Economy.strictlyPreferredPos_nonempty hregE hL hx_nn a
  have hP_open : IsOpen P :=
    isOpen_finset_sum_of_nonempty Finset.univ_nonempty (fun a _ => hS_open a)
  have hP_convex : Convex ℝ P := convex_sum _ (fun a _ => hS_convex a)
  have hP_ne : P.Nonempty :=
    ⟨∑ a, (hS_ne a).some,
      Set.finset_sum_mem_finset_sum _ _ _ (fun a _ => (hS_ne a).some_mem)⟩
  have hS_mem : ∀ {a : E.Agents} {z : Fin L → ℝ},
      z ∈ S a ↔ (z ≻[E.pref a] x a) ∧ ∀ l, 0 < z l := fun {a z} => Iff.rfl
  have hsingle_nn : ∀ (l₀ l : Fin L), 0 ≤ (Pi.single l₀ (1 : ℝ) : Fin L → ℝ) l := by
    intro l₀ l; rw [Pi.single_apply]; split <;> norm_num
  -- `G` is convex: a convex combination of plans is a plan (each `Y_j` convex).
  have hG_convex : Convex ℝ G := by
    rintro g₁ ⟨yy₁, hyy₁, rfl⟩ g₂ ⟨yy₂, hyy₂, rfl⟩ a b ha hb hab
    refine ⟨fun j => a • yy₁ j + b • yy₂ j,
      fun j => (hreg.techReg j).convex (hyy₁ j) (hyy₂ j) ha hb hab, ?_⟩
    ext l
    have hab' : a * eagg l + b * eagg l = eagg l := by rw [← add_mul, hab, one_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib]
    linarith [hab']
  have hgy_mem : gy ∈ G := ⟨y, hy_mem, rfl⟩
  -- `P` and `G` are disjoint, else a point in both is a feasible Pareto-dominating allocation.
  have hPG_disjoint : Disjoint P G := by
    rw [Set.disjoint_left]
    intro q hqP hqG
    rw [hP, Set.mem_finset_sum] at hqP
    obtain ⟨g, hg_mem, hg_sum⟩ := hqP
    have hg_mem' : ∀ a, g a ∈ S a := fun a => hg_mem (Finset.mem_univ a)
    have hq_cons : ∀ l, (∑ a, g a l) = q l := by
      intro l; have := congr_fun hg_sum l; simpa [Finset.sum_apply] using this
    obtain ⟨yy, hyy_mem, hq_prod⟩ := hqG
    have hq_prod' : ∀ l, q l = eagg l + ∑ j, yy j l := fun l => congr_fun hq_prod l
    have h_feas : E.Feasible g yy := by
      refine ⟨fun a l => ((hS_mem.mp (hg_mem' a)).2 l).le, hyy_mem, fun l => ?_⟩
      simp only [ProductionEconomy.aggregateExcess]
      simp only [heagg] at hq_prod'
      have := hq_cons l
      have := hq_prod' l
      linarith
    have h_dom : E.ParetoDominates g x := by
      refine ⟨fun a => ((hS_mem.mp (hg_mem' a)).1).1, ?_⟩
      exact ⟨hne.some, (hS_mem.mp (hg_mem' hne.some)).1⟩
    exact hpo.undominated ⟨g, yy, h_feas, h_dom⟩
  obtain ⟨f, u, hfP, hfG⟩ := geometric_hahn_banach_open hP_convex hP_open hG_convex hPG_disjoint
  have hperturb_mem : ∀ (j : E.Agents) (c : Fin L → ℝ) (_hc : ∀ l, 0 ≤ c l) (δ : ℝ), 0 < δ →
      x j + c + δ • one ∈ S j :=
    fun j c hc δ hδ => perturb_mem_strictlyPreferredPos hregE hL hx_nn j c hc δ hδ
  have hfw : f w = ∑ b, f (x b) := by
    have hweq : w = ∑ b, x b := by ext l; simp [hw, Finset.sum_apply]
    rw [hweq, map_sum]
  -- `w ≤ gy` pointwise from the market-clearing inequality.
  have hw_le_gy : ∀ l, w l ≤ gy l := by
    intro l
    have hfeas := hpo.feasible.excess_nonpos l
    simp only [ProductionEconomy.aggregateExcess] at hfeas
    simp only [hw, hgy, heagg]; linarith
  have hIR : (0 : ℝ) < I := by rw [hI]; exact_mod_cast Fintype.card_pos
  have h_basis_nonpos : ∀ l₀ : Fin L, f (Pi.single l₀ 1) ≤ 0 := by
    intro l₀
    set e₀ : Fin L → ℝ := Pi.single l₀ (1 : ℝ) with he₀
    have he₀_nn : ∀ l, 0 ≤ e₀ l := fun l => hsingle_nn l₀ l
    have hstep : ∀ t : ℝ, 0 < t →
        (I : ℝ) * f e₀ * t + (f w + (I : ℝ) * f one - u) ≤ 0 := by
      intro t ht
      have hmem : ∀ j, x j + (t • e₀) + (1 : ℝ) • one ∈ S j :=
        fun j => hperturb_mem j (t • e₀)
          (fun l => by
            simp only [Pi.smul_apply, smul_eq_mul]
            exact mul_nonneg ht.le (he₀_nn l)) 1 (by norm_num)
      have h_in_P : ∑ j, (x j + (t • e₀) + (1 : ℝ) • one) ∈ P :=
        hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => hmem j)
      have h_sep := hfP _ h_in_P
      have hsum : (∑ j, (x j + (t • e₀) + (1 : ℝ) • one))
          = w + (I : ℝ) • (t • e₀) + (I : ℝ) • ((1 : ℝ) • one) := by
        ext l
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw, hI]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ]
      rw [hsum, map_add, map_add, map_smul, map_smul, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, one_mul] at h_sep
      nlinarith [h_sep]
    nlinarith [affine_slope_nonpos_of_forall_pos hstep, hIR]
  have hfw_le_u : f w ≤ u := by
    have hstep : ∀ δ : ℝ, 0 < δ → (I : ℝ) * f one * δ + (f w - u) ≤ 0 := by
      intro δ hδ
      have hmem : ∀ j, x j + (0 : Fin L → ℝ) + δ • one ∈ S j :=
        fun j => hperturb_mem j 0 (fun l => le_refl 0) δ hδ
      have h_in_P : ∑ j, (x j + (0 : Fin L → ℝ) + δ • one) ∈ P :=
        hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => hmem j)
      have h_sep := hfP _ h_in_P
      have hsum : (∑ j, (x j + (0 : Fin L → ℝ) + δ • one)) = w + (I : ℝ) • (δ • one) := by
        ext l
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw, hI, add_zero]
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ]
      rw [hsum, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h_sep
      nlinarith [h_sep]
    linarith [affine_const_nonpos_of_forall_pos hstep]
  have hf_nonpos_of_nonneg : ∀ v : Fin L → ℝ, (∀ l, 0 ≤ v l) → f v ≤ 0 := by
    intro v hv
    rw [ContinuousLinearMap.pi_eq_dotProduct_single f v]
    simp only [dotProduct]
    refine Finset.sum_nonpos (fun l₀ _ => ?_)
    exact mul_nonpos_of_nonpos_of_nonneg (h_basis_nonpos l₀) (hv l₀)
  -- `f` is order-reversing on the nonneg orthant, so `w ≤ gy` gives `f gy ≤ f w ≤ u ≤ f gy`.
  have hfgy_le_fw : f gy ≤ f w := by
    have hdiff : f gy - f w = f (gy - w) := by rw [← map_sub]
    have : f (gy - w) ≤ 0 :=
      hf_nonpos_of_nonneg _ (fun l => by simp only [Pi.sub_apply]; linarith [hw_le_gy l])
    linarith
  have hu_le_fgy : u ≤ f gy := hfG gy hgy_mem
  have hfw_eq_u : f w = u := le_antisymm hfw_le_u (by linarith [hfgy_le_fw, hu_le_fgy])
  have hfgy_eq_u : f gy = u := le_antisymm (by linarith [hfgy_le_fw, hfw_le_u]) hu_le_fgy
  have hf_ne : f ≠ 0 := by
    intro hf0
    obtain ⟨z, hz⟩ := hP_ne
    have h1 := hfP z hz
    have h2 := hfG gy hgy_mem
    rw [hf0] at h1 h2
    simp only [ContinuousLinearMap.zero_apply] at h1 h2
    linarith
  refine ⟨fun l => -(f (Pi.single l 1)), fun l => by linarith [h_basis_nonpos l], ?_, ?_, ?_⟩
  · by_contra h_all
    push Not at h_all
    apply hf_ne
    ext v
    rw [ContinuousLinearMap.pi_eq_dotProduct_single f v, ContinuousLinearMap.zero_apply]
    simp only [dotProduct]
    refine Finset.sum_eq_zero (fun l₀ _ => ?_)
    have h_ge : 0 ≤ f (Pi.single l₀ 1) := by linarith [h_all l₀]
    rw [le_antisymm (h_basis_nonpos l₀) h_ge, zero_mul]
  · intro a z hz_orth hz_lt
    rw [show (fun l => -(f (Pi.single l 1))) ⬝ᵥ x a = -(f (x a)) from
          ContinuousLinearMap.neg_dotProduct_single f (x a),
        show (fun l => -(f (Pi.single l 1))) ⬝ᵥ z = -(f z) from
          ContinuousLinearMap.neg_dotProduct_single f z]
    have h_weak_on_S : ∀ z' ∈ S a, f z' ≤ f (x a) := by
      intro z' hz'
      have hstep : ∀ δ : ℝ, 0 < δ →
          (∑ b ∈ Finset.univ.erase a, f one) * δ + (f z' - f (x a)) ≤ 0 := by
        intro δ hδ
        set elem : E.Agents → Fin L → ℝ :=
          fun j => if j = a then z' else x j + (0 : Fin L → ℝ) + δ • one with helem
        have h_elem_mem : ∀ j, elem j ∈ S j := by
          intro j
          simp only [helem]
          split_ifs with hj
          · subst hj; exact hz'
          · exact hperturb_mem j 0 (fun l => le_refl 0) δ hδ
        have h_in_P : ∑ j, elem j ∈ P :=
          hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => h_elem_mem j)
        have h_sep := hfP _ h_in_P
        have h_fsum : f (∑ j, elem j) =
            f z' + ∑ j ∈ Finset.univ.erase a, (f (x j) + δ * f one) := by
          rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [helem]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [helem, (Finset.mem_erase.mp hj).1, if_false, add_zero, map_add, map_smul,
              smul_eq_mul]
        have h_fw_split : f w = f (x a) + ∑ j ∈ Finset.univ.erase a, f (x j) := by
          rw [hfw, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
        rw [h_fsum] at h_sep
        have hδsum : ∑ j ∈ Finset.univ.erase a, (f (x j) + δ * f one) =
            (∑ j ∈ Finset.univ.erase a, f (x j)) + (∑ b ∈ Finset.univ.erase a, f one) * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const]; ring
        rw [hδsum] at h_sep
        rw [← hfw_eq_u] at h_sep
        rw [h_fw_split] at h_sep
        linarith
      linarith [affine_const_nonpos_of_forall_pos hstep]
    have hz_step : ∀ ε : ℝ, 0 < ε → f one * ε + (f z - f (x a)) ≤ 0 := by
      intro ε hε
      have hmem : z + ε • one ∈ S a := by
        rw [hS_mem]
        refine ⟨?_, fun l => ?_⟩
        · have hge : (z + ε • one) ≽[E.pref a] z :=
            ((hregE.mono a).strictMono
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
                linarith)
              (fun heq => by
                have := congr_fun heq ⟨0, hL⟩
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one] at this
                linarith)
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
                linarith [hz_orth l])).1
          exact (E.pref a).lt_of_le_of_lt hge hz_lt
        · simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
          linarith [hz_orth l]
      have hweak := h_weak_on_S _ hmem
      rw [map_add, map_smul, smul_eq_mul] at hweak
      linarith
    linarith [affine_const_nonpos_of_forall_pos hz_step]
  · intro j z hz
    rw [show (fun l => -(f (Pi.single l 1))) ⬝ᵥ z = -(f z) from
          ContinuousLinearMap.neg_dotProduct_single f z,
        show (fun l => -(f (Pi.single l 1))) ⬝ᵥ y j = -(f (y j)) from
          ContinuousLinearMap.neg_dotProduct_single f (y j)]
    -- Swap firm `j`'s plan to `z`; the resulting aggregate point stays in `G`.
    set y' : E.Firms → Fin L → ℝ := fun k => if k = j then z else y k with hy'
    have hy'_mem : ∀ k, y' k ∈ (E.tech k).Y := by
      intro k; simp only [hy']; split_ifs with hk
      · subst hk; exact hz
      · exact hy_mem k
    set gz : Fin L → ℝ := fun l => eagg l + ∑ k, y' k l with hgz
    have hgz_mem : gz ∈ G := ⟨y', hy'_mem, rfl⟩
    have hfgz : u ≤ f gz := hfG gz hgz_mem
    have hdiff : gz - gy = z - y j := by
      ext l
      simp only [hgz, hgy, Pi.sub_apply, hy', apply_ite (fun (v : Fin L → ℝ) => v l)]
      have hsumdiff : (∑ k, (if k = j then z l else y k l)) - ∑ k, y k l = z l - y j l := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
        · simp
        · intro k _ hk; rw [if_neg hk]; ring
        · intro hj; exact absurd (Finset.mem_univ j) hj
      linarith [hsumdiff]
    have hfdiff : f z - f (y j) = f gz - f gy := by
      rw [← map_sub, ← map_sub, hdiff]
    linarith [hfgz, hfgy_eq_u]

/-- **Second Welfare Theorem with production — quasi-equilibrium at positive wealth.** The
supporting price from `ParetoOptimal.exists_supporting_price` gives a price quasi-equilibrium with
production: Every firm maximizes profit, and every agent with positive wealth `0 < p ⬝ᵥ x a` holds
a `≽`-maximal bundle in its transfer budget set `budgetSetAt p (p ⬝ᵥ x a)`. The positive-wealth
guard is the minimum-wealth caveat separating quasi-equilibrium from full equilibrium; zero-wealth
agents are not covered and no equilibrium object is built here. For the full **Walrasian
equilibrium with production and transfers** — budget-optimality for every agent, profit-maximizing
firms, and a balanced transfer scheme, packaged as a
`WalrasianEquilibriumWithProductionAndTransfers` — see
`ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers`, which closes the zero-wealth
gap under (consumption-side) McKenzie irreducibility. -/
theorem ParetoOptimal.exists_quasiEquilibrium_price (hne : Nonempty E.Agents)
    (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ}
    (hpo : E.ParetoOptimal x y) :
    ∃ p : Fin L → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a z, z ∈ nonnegOrthant L → (z ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ z) ∧
      (∀ a, 0 < p ⬝ᵥ x a →
        x a ∈ Optimization.argmaxRel (E.pref a) (budgetSetAt p (p ⬝ᵥ x a))) ∧
      (∀ j, ∀ z ∈ (E.tech j).Y, p ⬝ᵥ z ≤ p ⬝ᵥ y j) := by
  obtain ⟨p, hp_nn, hp_ne, hsupp_cons, hsupp_firm⟩ :=
    hpo.exists_supporting_price hne hreg hL
  have hregE : RegularEconomy E.toEconomy := hreg.toRegularEconomy
  have hx_nn : ∀ a l, 0 ≤ x a l := hpo.feasible.nonneg
  refine ⟨p, hp_nn, hp_ne, hsupp_cons, ?_, hsupp_firm⟩
  intro a hwealth
  refine ⟨⟨hx_nn a, le_refl _⟩, ?_⟩
  intro z hz
  rw [mem_budgetSetAt] at hz
  obtain ⟨hz_nn, hz_budget⟩ := hz
  rcases (E.pref a).le_total (x a) z with hle | hge
  · exact hle
  · by_cases hxa_ge : x a ≽[E.pref a] z
    · exact hxa_ge
    · exfalso
      have hz_lt : z ≻[E.pref a] x a := ⟨hge, hxa_ge⟩
      have hsup := hsupp_cons a z hz_nn hz_lt
      have hpz_eq : p ⬝ᵥ z = p ⬝ᵥ x a := le_antisymm hz_budget hsup
      have hz_ne : z ≠ 0 := by
        rintro rfl
        simp only [dotProduct_zero] at hpz_eq
        linarith [hpz_eq ▸ hwealth]
      have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
      have hopen : IsOpen ((E.pref a).strictUpperContour (x a)) :=
        (hregE.contPref a).isOpen_strictUpperContour (x a)
      have hz_in : z ∈ (E.pref a).strictUpperContour (x a) := hz_lt
      obtain ⟨r, hr_pos, hr⟩ := Metric.isOpen_iff.mp hopen z hz_in
      set s : ℝ := min (1 / 2) (r / (2 * ‖z‖)) with hs
      have hs_pos : 0 < s := lt_min (by norm_num) (by positivity)
      -- `s < 1` is not used below; retained to document that `(1 - s) > 0`.
      have _hs_lt_one : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hs_small : s * ‖z‖ < r := by
        have h_half : (r / (2 * ‖z‖)) * ‖z‖ = r / 2 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (r / (2 * ‖z‖)))
          hz_norm_pos.le, hr_pos]
      have hperturb_in : (1 - s) • z ∈ (E.pref a).strictUpperContour (x a) := by
        apply hr
        rw [Metric.mem_ball, dist_eq_norm]
        have : (1 - s) • z - z = (-s) • z := by module
        rw [this, norm_smul]
        simp only [norm_neg, Real.norm_eq_abs, abs_of_pos hs_pos]
        exact hs_small
      have hperturb_lt : ((1 - s) • z) ≻[E.pref a] x a := hperturb_in
      have hperturb_nn : (1 - s) • z ∈ nonnegOrthant L := by
        intro l
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hz_nn l)
      -- `p ⬝ᵥ x a ≤ p ⬝ᵥ ((1 - s) • z) = (1 - s) * (p ⬝ᵥ x a) < p ⬝ᵥ x a`.
      have hsup2 := hsupp_cons a ((1 - s) • z) hperturb_nn hperturb_lt
      have hval : p ⬝ᵥ ((1 - s) • z) = (1 - s) * (p ⬝ᵥ x a) := by
        rw [dotProduct_smul, smul_eq_mul, hpz_eq]
      rw [hval] at hsup2
      nlinarith [hwealth, hs_pos]

/-- **Market value-clearing at a supported Pareto optimum (production).** If `(x, y)` is Pareto
optimal, supported by a nonnegative price `p`, and some agent has positive wealth, then aggregate
excess demand is worthless: `p ⬝ᵥ aggregateExcess x y = 0`. Feasibility gives `≤ 0`; the reverse is
non-wastefulness — positively-valued slack could be handed (keeping the production plan fixed) to
the positive-wealth agent and would strictly improve them (`Desirable`), contradicting Pareto
optimality. This is what makes the lump-sum transfers `p ⬝ᵥ x a − wealth p a` balance. -/
lemma ParetoOptimal.aggregateExcess_value_zero_prod (hreg : RegularProductionEconomy E)
    {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ} (hpo : E.ParetoOptimal x y)
    {p : Fin L → ℝ} (hp_nn : ∀ l, 0 ≤ p l)
    (hsupp : ∀ a z, z ∈ nonnegOrthant L → (z ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ z)
    (hwealth : ∃ a, 0 < p ⬝ᵥ x a) :
    p ⬝ᵥ E.aggregateExcess x y = 0 := by
  classical
  have hx_nn : ∀ a l, 0 ≤ x a l := hpo.feasible.nonneg
  set z : Fin L → ℝ := E.aggregateExcess x y with hz
  -- Feasibility: every coordinate of aggregate excess is nonpositive.
  have hz_nonpos : ∀ l, z l ≤ 0 := fun l => hpo.feasible.excess_nonpos l
  -- Each priced coordinate contributes nonpositively, so the value of excess is `≤ 0`.
  have hval_le : p ⬝ᵥ z ≤ 0 := by
    rw [dotProduct]
    refine Finset.sum_nonpos fun l _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (hp_nn l) (hz_nonpos l)
  -- The reverse inequality is non-wastefulness: a strictly negative excess value would let us
  -- hand the slack at some priced, oversupplied good to a positive-wealth agent and improve them.
  refine le_antisymm hval_le ?_
  by_contra h_neg
  push Not at h_neg
  have h_sum_lt : (∑ l, p l * z l) < ∑ _l : Fin L, (0 : ℝ) := by
    rw [Finset.sum_const_zero, ← dotProduct]; exact h_neg
  obtain ⟨l₀, _, hl₀_neg⟩ := Finset.exists_lt_of_sum_lt h_sum_lt
  have hp_l₀_pos : 0 < p l₀ := by
    rcases lt_or_eq_of_le (hp_nn l₀) with hpos | hzero
    · exact hpos
    · exfalso; rw [← hzero, zero_mul] at hl₀_neg; exact lt_irrefl 0 hl₀_neg
  have hz_l₀_neg : z l₀ < 0 :=
    lt_of_not_ge fun hge => absurd hl₀_neg (not_lt.mpr (mul_nonneg hp_l₀_pos.le hge))
  set slack : ℝ := -z l₀ with hslack
  have hslack_pos : 0 < slack := by rw [hslack]; linarith
  obtain ⟨a₀, ha₀_wealth⟩ := hwealth
  set x' : E.Agents → Fin L → ℝ :=
    fun a l => x a l + (if a = a₀ ∧ l = l₀ then slack else 0) with hx'
  have hx'_nn : ∀ a l, 0 ≤ x' a l := by
    intro a l
    simp only [hx']
    split
    · linarith [hx_nn a l]
    · linarith [hx_nn a l]
  -- The aggregate excess of `x'` (same plan `y`) matches `x` away from `l₀`, exactly `0` at `l₀`.
  have hagg_x' : ∀ l, E.aggregateExcess x' y l = z l + (if l = l₀ then slack else 0) := by
    intro l
    have hsum_x' : (∑ a, x' a l) = (∑ a, x a l) + (if l = l₀ then slack else 0) := by
      simp only [hx']
      rw [Finset.sum_add_distrib]
      congr 1
      by_cases hl : l = l₀
      · subst hl
        simp only [and_true]
        rw [Finset.sum_ite_eq' Finset.univ a₀ (fun _ => slack)]
        simp only [Finset.mem_univ, if_true]
      · simp only [hl, and_false, if_false, Finset.sum_const_zero]
    change (∑ a, x' a l) - (∑ a, E.endow a l) - (∑ j, y j l)
      = z l + (if l = l₀ then slack else 0)
    rw [hsum_x', hz]
    change (∑ a, x a l) + (if l = l₀ then slack else 0) - (∑ a, E.endow a l) - (∑ j, y j l)
      = ((∑ a, x a l) - (∑ a, E.endow a l) - (∑ j, y j l)) + (if l = l₀ then slack else 0)
    ring
  -- `(x', y)` is feasible: plans `y` are still attainable, and excess stays nonpositive (zero at
  -- `l₀`, where the slack exactly cancels the oversupply).
  have hx'_feas : E.Feasible x' y := by
    refine ⟨hx'_nn, hpo.feasible.plans_feasible, fun l => ?_⟩
    rw [hagg_x' l]
    by_cases hl : l = l₀
    · subst hl; simp only [if_true, hslack]; linarith
    · simp only [hl, if_false, add_zero]; exact hz_nonpos l
  -- `a₀` strictly improves: `x a₀ ≤ x' a₀`, they differ at `l₀`, and `x a₀` is weakly preferred to
  -- a strictly cheaper interior bundle, so `Desirable.improve` upgrades the bump to a strict gain.
  have hsum_p_pos : 0 < ∑ l, p l := by
    by_contra h_le
    push Not at h_le
    have hsum_zero : ∀ l, p l = 0 := by
      have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => hp_nn l)
      have hsum_eq : (∑ l, p l) = 0 := le_antisymm h_le this
      intro l
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hp_nn l)).mp hsum_eq l (Finset.mem_univ l)
    have : p ⬝ᵥ x a₀ = 0 := by
      rw [dotProduct]
      exact Finset.sum_eq_zero fun l _ => by rw [hsum_zero l, zero_mul]
    linarith [this ▸ ha₀_wealth]
  set δ : ℝ := (p ⬝ᵥ x a₀) / (2 * ∑ l, p l) with hδ
  have hδ_pos : 0 < δ := by rw [hδ]; positivity
  set w : Fin L → ℝ := fun _ => δ with hw_def
  have hw_pos : ∀ l, 0 < w l := fun _ => hδ_pos
  have hpw : p ⬝ᵥ w = δ * ∑ l, p l := by
    rw [dotProduct]
    simp only [hw_def, mul_comm]
    rw [← Finset.sum_mul]
  have hpw_half : p ⬝ᵥ w = (p ⬝ᵥ x a₀) / 2 := by
    rw [hpw, hδ]; field_simp
  have hpw_lt : p ⬝ᵥ w < p ⬝ᵥ x a₀ := by rw [hpw_half]; linarith
  have hxa_ge_w : x a₀ ≽[E.pref a₀] w := by
    by_contra hge
    have hle' : w ≽[E.pref a₀] x a₀ :=
      ((E.pref a₀).le_total w (x a₀)).resolve_right hge
    have hw_orth : w ∈ nonnegOrthant L := fun l => (hw_pos l).le
    have hsup := hsupp a₀ w hw_orth ⟨hle', hge⟩
    linarith
  have hxa_le_x'a : x a₀ ≤ x' a₀ := by
    intro l
    simp only [hx']
    split
    · linarith [hslack_pos]
    · linarith
  have hxa_ne_x'a : x a₀ ≠ x' a₀ := by
    intro heq
    have hcontra := congr_fun heq l₀
    simp only [hx', and_true, if_true] at hcontra
    linarith [hslack_pos]
  have hx'a_pref : x' a₀ ≻[E.pref a₀] x a₀ :=
    (hreg.toRegularEconomy.desirable a₀).improve hw_pos hxa_ge_w hxa_le_x'a hxa_ne_x'a
  -- `(x', y)` Pareto-dominates `x`: untouched agents are unchanged, and `a₀` strictly gains.
  have hx'_dom : E.ParetoDominates x' x := by
    refine ⟨fun a => ?_, ⟨a₀, hx'a_pref⟩⟩
    by_cases ha : a = a₀
    · subst ha; exact hx'a_pref.1
    · have : x' a = x a := by
        funext l
        simp only [hx', ha, false_and, if_false, add_zero]
      rw [this]; exact (E.pref a).le_refl (x a)
  exact hpo.undominated ⟨x', y, hx'_feas, hx'_dom⟩

/-- **Second Welfare Theorem with production — full decentralization with lump-sum transfers**
(Arrow 1951; Debreu 1951; McKenzie 1959). Every Pareto optimal allocation `(x, y)` of a regular,
consumption-side McKenzie-irreducible production economy in which every good is consumed (`hcons`)
is a **Walrasian equilibrium with production and lump-sum transfers**: There is a nonnegative
nonzero price `p`, profit-maximizing firm plans, a balanced transfer scheme
`t a = p ⬝ᵥ x a − wealth p a` (`∑ t = 0`), at which every agent — including zero-wealth ones —
holds a `≽`-maximal bundle in its transfer-adjusted budget `budgetSetAt p (wealth p a + t a)`, and
markets clear. The consumption side reduces to the exchange upgrade on
`E.toEconomy.transferEndow x`; irreducibility closes the minimum-wealth gap that
`exists_quasiEquilibrium_price` leaves open. The returned `W` is a complete equilibrium with
production on its own (every field of `WalrasianEquilibriumWithProductionAndTransfers`); the
conclusion `W.Decentralizes x y` records only that it implements the *given* optimum `(x, y)` with
the supporting balanced transfer scheme `t a = price ⬝ᵥ x a − wealth p a`. -/
theorem ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers
    (hne : Nonempty E.Agents) (hreg : RegularProductionEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} {y : E.Firms → Fin L → ℝ} (hpo : E.ParetoOptimal x y)
    (hcons : ∀ l, ∃ a, 0 < x a l)
    (hirr : Irreducible (E.toEconomy.transferEndow (fun a => hpo.feasible.nonneg a))) :
    ∃ W : WalrasianEquilibriumWithProductionAndTransfers E, W.Decentralizes x y := by
  classical
  haveI : Finite E.Agents := Finite.of_fintype _
  have hregE : RegularEconomy E.toEconomy := hreg.toRegularEconomy
  -- The relabeled *exchange* economy whose endowments are `x`: its wealth at `p` is `p ⬝ᵥ x a`,
  -- which is exactly the transfer-adjusted budget level. The consumer upgrade is purely exchange.
  set E' : Economy L := E.toEconomy.transferEndow (fun a => hpo.feasible.nonneg a) with hE'
  -- 1. Supporting (quasi-equilibrium) price: consumer support + firm profit maximization.
  obtain ⟨p₀, hp₀_nn, hp₀_ne, hsupp_cons₀, hsupp_firm₀⟩ :=
    hpo.exists_supporting_price hne hreg hL
  -- 2. Normalize to the price simplex (scale-invariant).
  obtain ⟨q, hq_simplex, hq_ne, t, ht_pos, hqt⟩ :
      ∃ q : Fin L → ℝ, q ∈ priceSimplex L ∧ (∃ l, 0 < q l) ∧
        ∃ t : ℝ, 0 < t ∧ q = t • p₀ := by
    obtain ⟨l_pos, hl_pos⟩ := hp₀_ne
    set S : ℝ := ∑ l, p₀ l with hS
    have hS_pos : 0 < S :=
      Finset.sum_pos' (fun l _ => hp₀_nn l) ⟨l_pos, Finset.mem_univ l_pos, hl_pos⟩
    set s : ℝ := S⁻¹ with hs
    have hs_pos : 0 < s := by rw [hs]; positivity
    refine ⟨s • p₀, ⟨fun l => ?_, ?_⟩, ⟨l_pos, ?_⟩, s, hs_pos, rfl⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hs_pos.le (hp₀_nn l)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, ← hS, hs, inv_mul_cancel₀ (ne_of_gt hS_pos)]
    · simp only [Pi.smul_apply, smul_eq_mul]; positivity
  have hq_nn : ∀ l, 0 ≤ q l := fun l => hq_simplex.1 l
  have hscale_dot : ∀ v : Fin L → ℝ, q ⬝ᵥ v = t * (p₀ ⬝ᵥ v) := fun v => by
    rw [hqt, smul_dotProduct, smul_eq_mul]
  have hsupp_cons : ∀ a z, z ∈ nonnegOrthant L → (z ≻[E.pref a] x a) → q ⬝ᵥ x a ≤ q ⬝ᵥ z := by
    intro a z hz hlt
    rw [hscale_dot, hscale_dot]
    exact mul_le_mul_of_nonneg_left (hsupp_cons₀ a z hz hlt) ht_pos.le
  have hsupp_firm : ∀ j, ∀ z ∈ (E.tech j).Y, q ⬝ᵥ z ≤ q ⬝ᵥ y j := by
    intro j z hz
    rw [hscale_dot, hscale_dot]
    exact mul_le_mul_of_nonneg_left (hsupp_firm₀ j z hz) ht_pos.le
  -- 3. Positive-wealth witness: some positively-priced good is consumed.
  have hwealth : ∃ a, 0 < q ⬝ᵥ x a := by
    obtain ⟨l₀, hl₀_pos⟩ := hq_ne
    obtain ⟨a, ha_pos⟩ := hcons l₀
    refine ⟨a, lt_of_lt_of_le (mul_pos hl₀_pos ha_pos) ?_⟩
    rw [dotProduct]
    exact Finset.single_le_sum
      (fun l _ => mul_nonneg (hq_nn l) (hpo.feasible.nonneg a l)) (Finset.mem_univ l₀)
  -- 4. Consumer upgrade via the exchange McKenzie machinery on `E'` (endow = x).
  have hbud' : ∀ a, x a ∈ E'.budgetSet q a := fun a => ⟨hpo.feasible.nonneg a, le_refl _⟩
  have hbind' : ∀ a, q ⬝ᵥ x a = q ⬝ᵥ E'.endow a := fun _ => rfl
  have hIR' : ∀ a, x a ≽[E'.pref a] E'.endow a := fun a => (E.pref a).le_refl (x a)
  have hquasi' : ∀ a z, (∀ l, 0 ≤ z l) → q ⬝ᵥ z < q ⬝ᵥ E'.endow a →
      ¬ (z ≻[E'.pref a] x a) := by
    intro a z hz_nn hz_cheap hz_lt
    exact absurd (hsupp_cons a z hz_nn hz_lt) (not_le.mpr hz_cheap)
  obtain ⟨hq_pos, hopt'⟩ :=
    E'.quasi_to_walrasian hne (fun a => hregE.contPref a) (fun a => hregE.desirable a) hirr
      hq_simplex hbud' hbind' hIR' hquasi' hwealth
  -- 5. Firm side: the supported plans maximize profit.
  have hsupply : ∀ j, y j ∈ (E.tech j).supply q :=
    fun j => ⟨hpo.feasible.plans_feasible j, hsupp_firm j⟩
  -- 6. Market value-clearing, and from it the balance of the transfers.
  have hval : q ⬝ᵥ E.aggregateExcess x y = 0 :=
    hpo.aggregateExcess_value_zero_prod hreg hq_nn hsupp_cons hwealth
  have hprofit : ∀ j, (E.tech j).profit q = q ⬝ᵥ y j :=
    fun j => (E.tech j).profit_eq_dotProduct_of_mem_supply (hsupply j)
  have hnet : q ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, (E.tech j).profit q := by
    have hdot : q ⬝ᵥ (fun l => ∑ j, y j l) = ∑ j, q ⬝ᵥ y j := by
      simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hdot]; exact Finset.sum_congr rfl fun j _ => (hprofit j).symm
  have htb : ∑ a, (q ⬝ᵥ x a - E.wealth q a) = 0 := by
    rw [E.aggregate_net_spending, ← hnet, ← dotProduct_sub, ← E.aggregateExcess_eq]
    exact hval
  refine ⟨{
    price := q
    alloc := x
    plan := y
    transfer := fun a => q ⬝ᵥ x a - E.wealth q a
    price_cone := hq_nn
    price_ne := hq_ne
    transfers_balance := htb
    profit_max := hsupply
    isOptimal := ?_
    clears := ⟨hpo.feasible.excess_nonpos, hval⟩ }, ⟨rfl, rfl, fun a => rfl⟩⟩
  intro a
  have hbudget_eq : E.wealth q a + (q ⬝ᵥ x a - E.wealth q a) = q ⬝ᵥ x a := by ring
  rw [hbudget_eq]
  exact hopt' a

end ProductionEconomy

end Econlib.Equilibrium
