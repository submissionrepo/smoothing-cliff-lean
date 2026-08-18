/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Equilibrium.Existence
public import Econlib.Math.LinearAlgebra.ContinuousLinearMap
public import Econlib.Math.Order.AffineInequalities
public import Econlib.Math.Topology.MinkowskiSum
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# General equilibrium: The Second Welfare Theorem

This file contains Second Welfare Theorem results for the preference-carried `Economy`. The results
start from a Pareto optimal feasible allocation `x` in a regular economy.

The supporting-price theorem gives a nonnegative nonzero price vector supporting each assigned
bundle: Every nonnegative bundle strictly preferred to `x a` costs at least `x a`. The
quasi-equilibrium theorem adds budget maximality for agents whose transfer budget `p ⬝ᵥ x a` is
strictly positive.

The strongest result, `Economy.ParetoOptimal.exists_walrasianEquilibriumWithTransfers`,
decentralizes the given Pareto optimum as a `WalrasianEquilibriumWithTransfers`. It assumes every
good is consumed and that the exchange economy whose endowments are relabeled to the allocation `x`
is McKenzie-irreducible. The returned equilibrium keeps exactly the allocation `x`, uses balanced
lump-sum transfers, and gives every agent a budget-maximal bundle.

## Main definitions

* `Economy.strictlyPreferredPos`: The strictly-preferred, strictly-positive set for agent `a` at
  allocation `x`; open and convex by continuous, convex preferences.

## Main statements

* `Economy.ParetoOptimal.exists_supporting_price`: A Pareto optimum admits nonnegative nonzero
  prices supporting each agent's assigned bundle.
* `Economy.ParetoOptimal.exists_quasiEquilibrium_price`: Positive-wealth agents are budget-maximal
  in their transfer budget sets.
* `Economy.ParetoOptimal.aggregateExcess_value_zero`: At a supported Pareto optimum with some
  positive-wealth agent, aggregate excess demand is worthless (`p ⬝ᵥ aggregateExcess x = 0`) — the
  non-wastefulness that makes the lump-sum transfers balance.
* `Economy.ParetoOptimal.exists_walrasianEquilibriumWithTransfers`: **Full decentralization.**
  Under every-good-consumed (`hcons`) and relabeled-economy irreducibility (`hirr`), `x` is
  implemented by a `WalrasianEquilibriumWithTransfers` `W` with `W.Decentralizes x`.

## References

* Arrow (1951)
* Debreu (1951)

## Tags

second welfare theorem, pareto optimality, walrasian equilibrium, supporting prices, transfers
-/

@[expose] public section

open Finset BigOperators Matrix Pointwise Econlib.Preferences

namespace Econlib.Equilibrium

variable {L : ℕ}

namespace Economy

variable (E : Economy L)

/-- The **strictly-preferred, strictly-positive** set for agent `a` at allocation `x`: Strictly
positive bundles (in the open orthant interior) that are strictly preferred to `x a`. -/
def strictlyPreferredPos (x : E.Agents → Fin L → ℝ) (a : E.Agents) : Set (Fin L → ℝ) :=
  {y | (y ≻[E.pref a] x a) ∧ ∀ l, 0 < y l}

variable {E}

/-- If `b` dominates `x` everywhere, is strictly positive, and strictly exceeds `x` at coordinate
`⟨0, hL⟩`, then `b ≻ x`. -/
private lemma lt_of_dom_pos {R : Preferences.PreferenceRel (Fin L → ℝ)}
    (hmono : Preferences.StrictMonoToInterior R) (hL : 0 < L) {x b : Fin L → ℝ}
    (hle : ∀ l, x l ≤ b l) (h0 : x ⟨0, hL⟩ < b ⟨0, hL⟩) (hpos : ∀ l, 0 < b l) : R.lt b x :=
  hmono.strictMono hle (fun heq => absurd (congr_fun heq ⟨0, hL⟩) h0.ne) hpos

/-- `strictlyPreferredPos` is open for any regular economy. -/
lemma strictlyPreferredPos_isOpen (hreg : RegularEconomy E) (x : E.Agents → Fin L → ℝ)
    (a : E.Agents) : IsOpen (E.strictlyPreferredPos x a) := by
  change IsOpen ((E.pref a).strictUpperContour (x a) ∩ {y : Fin L → ℝ | ∀ l, 0 < y l})
  refine IsOpen.inter ?_ ?_
  · exact (hreg.contPref a).isOpen_strictUpperContour (x a)
  · have : {y : Fin L → ℝ | ∀ l, 0 < y l} = ⋂ l, {y | 0 < y l} := by ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun l => isOpen_lt continuous_const (continuous_apply l)

/-- `strictlyPreferredPos` is convex for any regular economy. -/
lemma strictlyPreferredPos_convex (hreg : RegularEconomy E) (x : E.Agents → Fin L → ℝ)
    (a : E.Agents) : Convex ℝ (E.strictlyPreferredPos x a) := by
  change Convex ℝ ((E.pref a).strictUpperContour (x a) ∩ {y : Fin L → ℝ | ∀ l, 0 < y l})
  refine Convex.inter (ConvexPreference.strictUpperContour_convex (hreg.convex a) (x a)) ?_
  have : {y : Fin L → ℝ | ∀ l, 0 < y l} = ⋂ l, {y | 0 < y l} := by ext y; simp
  rw [this]
  refine convex_iInter fun l => ?_
  exact convex_halfSpace_gt (LinearMap.proj l).isLinear 0

/-- `strictlyPreferredPos` is nonempty whenever `x a` is nonnegative. -/
lemma strictlyPreferredPos_nonempty (hreg : RegularEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} (hx_nn : ∀ a l, 0 ≤ x a l) (a : E.Agents) :
    (E.strictlyPreferredPos x a).Nonempty := by
  refine ⟨x a + fun _ => (1 : ℝ), ?_, fun l => ?_⟩
  · refine lt_of_dom_pos (hreg.mono a) hL (fun l => ?_) ?_ (fun l => ?_) <;>
      simp only [Pi.add_apply]
    · linarith
    · linarith
    · linarith [hx_nn a l]
  · simp only [Pi.add_apply]
    linarith [hx_nn a l]

/-- **Second Welfare Theorem — supporting prices.** For a regular economy, every Pareto optimal
allocation `x` is supported by a nonnegative nonzero price vector: Any nonnegative bundle strictly
preferred to `x a` is at least as expensive as `x a`. -/
theorem ParetoOptimal.exists_supporting_price (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} (hpareto : E.ParetoOptimal x) :
    ∃ p : Fin L → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      ∀ a y, y ∈ nonnegOrthant L → (y ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ y := by
  classical
  have hx_nn : ∀ a l, 0 ≤ x a l := hpareto.feasible.nonneg
  set one : Fin L → ℝ := fun _ => (1 : ℝ) with hone
  set S : E.Agents → Set (Fin L → ℝ) := fun a => E.strictlyPreferredPos x a with hS
  set P : Set (Fin L → ℝ) := ∑ a : E.Agents, S a with hP
  set w : Fin L → ℝ := fun l => ∑ a, x a l with hw
  set I : ℕ := Fintype.card E.Agents with hI
  have hS_open : ∀ a, IsOpen (S a) := fun a => strictlyPreferredPos_isOpen hreg x a
  have hS_convex : ∀ a, Convex ℝ (S a) := fun a => strictlyPreferredPos_convex hreg x a
  have hS_ne : ∀ a, (S a).Nonempty :=
    fun a => strictlyPreferredPos_nonempty hreg hL hx_nn a
  have hP_open : IsOpen P :=
    isOpen_finset_sum_of_nonempty Finset.univ_nonempty (fun a _ => hS_open a)
  have hP_convex : Convex ℝ P := convex_sum _ (fun a _ => hS_convex a)
  have hP_ne : P.Nonempty :=
    ⟨∑ a, (hS_ne a).some,
      Set.finset_sum_mem_finset_sum _ _ _ (fun a _ => (hS_ne a).some_mem)⟩
  have hS_mem : ∀ {a : E.Agents} {y : Fin L → ℝ},
      y ∈ S a ↔ (y ≻[E.pref a] x a) ∧ ∀ l, 0 < y l := fun {a y} => Iff.rfl
  have hperturb_mem : ∀ (j : E.Agents) (δ : ℝ), 0 < δ → x j + δ • one ∈ S j := by
    intro j δ hδ
    rw [hS_mem]
    refine ⟨?_, fun l => ?_⟩
    · refine lt_of_dom_pos (hreg.mono j) hL (fun l => ?_) ?_ (fun l => ?_) <;>
        simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
      · linarith
      · linarith
      · linarith [hx_nn j l]
    · simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
      linarith [hx_nn j l]
  have hagg_excess : ∀ (g : E.Agents → Fin L → ℝ) (l : Fin L),
      E.aggregateExcess g l = (∑ a, g a l) - ∑ a, E.endow a l := fun _ _ => rfl
  -- `w` is not in `P`: otherwise we get a feasible Pareto-dominating allocation.
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
    have h_feas : E.Feasible g := by
      refine ⟨fun a l => ((hS_mem.mp (hg_mem' a)).2 l).le, fun l => ?_⟩
      rw [hagg_excess g l, hsum_eq l, hw]
      have hxfeas := hpareto.feasible.excess_nonpos l
      rw [hagg_excess x l] at hxfeas
      simpa [hw] using hxfeas
    have h_dom : E.ParetoDominates g x := by
      refine ⟨fun a => ((hS_mem.mp (hg_mem' a)).1).1, ?_⟩
      exact ⟨hne.some, (hS_mem.mp (hg_mem' hne.some)).1⟩
    exact hpareto.undominated ⟨g, h_feas, h_dom⟩
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
    have hmem : ∀ (j : E.Agents) (δ : ℝ), 0 < δ →
        x j + δ • one + Pi.single l₀ (1 : ℝ) ∈ S j := by
      intro j δ hδ
      rw [hS_mem]
      refine ⟨?_, fun l => ?_⟩
      · refine lt_of_dom_pos (hreg.mono j) hL (fun l => ?_) ?_ (fun l => ?_) <;>
          simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
        · linarith [hsingle_nn l₀ l]
        · linarith [hsingle_nn l₀ (⟨0, hL⟩ : Fin L)]
        · linarith [hx_nn j l, hsingle_nn l₀ l]
      · simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
        linarith [hx_nn j l, hsingle_nn l₀ l]
    have hstep : ∀ δ : ℝ, 0 < δ →
        (I : ℝ) * f one * δ + (I : ℝ) * f (Pi.single l₀ 1) ≤ 0 := by
      intro δ hδ
      have h_in_P : ∑ j, (x j + δ • one + Pi.single l₀ (1 : ℝ)) ∈ P :=
        hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => hmem j δ hδ)
      have h_sep := hf_sep _ h_in_P
      have hsum : (∑ j, (x j + δ • one + (Pi.single l₀ (1 : ℝ) : Fin L → ℝ)))
          = w + (I : ℝ) • (δ • one) + (I : ℝ) • (Pi.single l₀ (1 : ℝ) : Fin L → ℝ) := by
        ext l
        simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw, hI]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ]
      rw [hsum, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
        smul_eq_mul] at h_sep
      nlinarith [h_sep]
    have hB : (I : ℝ) * f (Pi.single l₀ 1) ≤ 0 :=
      affine_const_nonpos_of_forall_pos hstep
    nlinarith [hB]
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
  · intro a y hy_orth hy_lt
    rw [show (fun l => -(f (Pi.single l 1))) ⬝ᵥ x a = -(f (x a)) from
          ContinuousLinearMap.neg_dotProduct_single f (x a),
        show (fun l => -(f (Pi.single l 1))) ⬝ᵥ y = -(f y) from
          ContinuousLinearMap.neg_dotProduct_single f y]
    have hfw : f w = ∑ b, f (x b) := by
      have hweq : w = ∑ b, x b := by ext l; simp [hw, Finset.sum_apply]
      rw [hweq, map_sum]
    -- Any strictly-preferred-positive bundle has `f`-value at most `f (x a)`,
    -- by perturbing the other agents and sending `δ → 0`.
    have h_weak_on_S : ∀ z ∈ S a, f z ≤ f (x a) := by
      intro z hz
      have hstep : ∀ δ : ℝ, 0 < δ →
          (∑ b ∈ Finset.univ.erase a, f one) * δ + (f z - f (x a)) ≤ 0 := by
        intro δ hδ
        set elem : E.Agents → Fin L → ℝ :=
          fun j => if j = a then z else x j + δ • one with helem
        have h_elem_mem : ∀ j, elem j ∈ S j := by
          intro j
          simp only [helem]
          split_ifs with hj
          · subst hj; exact hz
          · exact hperturb_mem j δ hδ
        have h_in_P : ∑ j, elem j ∈ P :=
          hP ▸ Set.finset_sum_mem_finset_sum _ _ _ (fun j _ => h_elem_mem j)
        have h_sep := hf_sep _ h_in_P
        have h_fsum : f (∑ j, elem j) =
            f z + ∑ j ∈ Finset.univ.erase a, (f (x j) + δ * f one) := by
          rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          congr 1
          · simp [helem]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [helem, (Finset.mem_erase.mp hj).1, if_false, map_add, map_smul,
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
      have := affine_const_nonpos_of_forall_pos hstep
      linarith
    have hy_step : ∀ ε : ℝ, 0 < ε → f one * ε + (f y - f (x a)) ≤ 0 := by
      intro ε hε
      have hmem : y + ε • one ∈ S a := by
        rw [hS_mem]
        refine ⟨?_, fun l => ?_⟩
        · have hge : (y + ε • one) ≽[E.pref a] y :=
            (lt_of_dom_pos (hreg.mono a) hL
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]; linarith)
              (by simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]; linarith)
              (fun l => by
                simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
                linarith [hy_orth l])).1
          exact (E.pref a).lt_of_le_of_lt hge hy_lt
        · simp only [Pi.add_apply, Pi.smul_apply, hone, smul_eq_mul, mul_one]
          linarith [hy_orth l]
      have hweak := h_weak_on_S _ hmem
      rw [map_add, map_smul, smul_eq_mul] at hweak
      linarith
    have := affine_const_nonpos_of_forall_pos hy_step
    linarith

/-- **Second Welfare Theorem — quasi-equilibrium at positive wealth.** The supporting price from
`ParetoOptimal.exists_supporting_price` additionally gives budget-optimality for positive-wealth
agents: For every agent with `0 < p ⬝ᵥ x a`, the bundle `x a` is `≽`-maximal in its transfer budget
set `budgetSetAt p (p ⬝ᵥ x a)`.

This is a price quasi-equilibrium with transfers: The zero-wealth agents (the minimum-wealth
exceptional case) are not covered, and no equilibrium object is built. For the full **Walrasian
equilibrium with transfers** — budget-optimality for every agent and a balanced transfer scheme,
packaged as a `WalrasianEquilibriumWithTransfers` — see
`ParetoOptimal.exists_walrasianEquilibriumWithTransfers`, which closes the zero-wealth gap under
McKenzie irreducibility. -/
theorem ParetoOptimal.exists_quasiEquilibrium_price (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} (hpareto : E.ParetoOptimal x) :
    ∃ p : Fin L → ℝ, (∀ l, 0 ≤ p l) ∧ (∃ l, 0 < p l) ∧
      (∀ a y, y ∈ nonnegOrthant L → (y ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ y) ∧
      (∀ a, 0 < p ⬝ᵥ x a →
        x a ∈ Optimization.argmaxRel (E.pref a) (budgetSetAt p (p ⬝ᵥ x a))) := by
  obtain ⟨p, hp_nn, hp_ne, hsupp⟩ :=
    hpareto.exists_supporting_price hne hreg hL
  have hx_nn : ∀ a l, 0 ≤ x a l := hpareto.feasible.nonneg
  refine ⟨p, hp_nn, hp_ne, hsupp, ?_⟩
  intro a hwealth
  refine ⟨⟨hx_nn a, le_refl _⟩, ?_⟩
  intro y hy
  rw [mem_budgetSetAt] at hy
  obtain ⟨hy_nn, hy_budget⟩ := hy
  rcases (E.pref a).le_total (x a) y with hle | hge
  · exact hle
  · by_cases hxa_ge : x a ≽[E.pref a] y
    · exact hxa_ge
    · exfalso
      have hy_lt : y ≻[E.pref a] x a := ⟨hge, hxa_ge⟩
      have hsup := hsupp a y hy_nn hy_lt
      have hpy_eq : p ⬝ᵥ y = p ⬝ᵥ x a := le_antisymm hy_budget hsup
      have hy_ne : y ≠ 0 := by
        rintro rfl
        simp only [dotProduct_zero] at hpy_eq
        linarith [hpy_eq ▸ hwealth]
      have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
      have hopen : IsOpen ((E.pref a).strictUpperContour (x a)) :=
        (hreg.contPref a).isOpen_strictUpperContour (x a)
      have hy_in : y ∈ (E.pref a).strictUpperContour (x a) := hy_lt
      obtain ⟨r, hr_pos, hr⟩ := Metric.isOpen_iff.mp hopen y hy_in
      set s : ℝ := min (1 / 2) (r / (2 * ‖y‖)) with hs
      have hs_pos : 0 < s := lt_min (by norm_num) (by positivity)
      -- `s < 1` is not used below; retained to document that `(1 - s) > 0`.
      have _hs_lt_one : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hs_small : s * ‖y‖ < r := by
        have h_half : (r / (2 * ‖y‖)) * ‖y‖ = r / 2 := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (r / (2 * ‖y‖)))
          hy_norm_pos.le, hr_pos]
      have hperturb_in : (1 - s) • y ∈ (E.pref a).strictUpperContour (x a) := by
        apply hr
        rw [Metric.mem_ball, dist_eq_norm]
        have : (1 - s) • y - y = (-s) • y := by module
        rw [this, norm_smul]
        simp only [norm_neg, Real.norm_eq_abs, abs_of_pos hs_pos]
        exact hs_small
      have hperturb_lt : ((1 - s) • y) ≻[E.pref a] x a := hperturb_in
      have hperturb_nn : (1 - s) • y ∈ nonnegOrthant L := by
        intro l
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (by linarith) (hy_nn l)
      -- `p ⬝ᵥ x a ≤ p ⬝ᵥ ((1 - s) • y) = (1 - s) * (p ⬝ᵥ x a) < p ⬝ᵥ x a`.
      have hsup2 := hsupp a ((1 - s) • y) hperturb_nn hperturb_lt
      have hval : p ⬝ᵥ ((1 - s) • y) = (1 - s) * (p ⬝ᵥ x a) := by
        rw [dotProduct_smul, smul_eq_mul, hpy_eq]
      rw [hval] at hsup2
      nlinarith [hwealth, hs_pos]

/-- **Market value-clearing at a supported Pareto optimum.** If `x` is Pareto optimal, supported by
a nonnegative price `p`, and some agent has positive wealth, then aggregate excess demand is
worthless: `p ⬝ᵥ aggregateExcess x = 0`. This non-wastefulness is what makes the lump-sum transfers
`p ⬝ᵥ x a − p ⬝ᵥ endow a` balance. -/
lemma ParetoOptimal.aggregateExcess_value_zero (hreg : RegularEconomy E)
    {x : E.Agents → Fin L → ℝ} (hpareto : E.ParetoOptimal x)
    {p : Fin L → ℝ} (hp_nn : ∀ l, 0 ≤ p l)
    (hsupp : ∀ a y, y ∈ nonnegOrthant L → (y ≻[E.pref a] x a) → p ⬝ᵥ x a ≤ p ⬝ᵥ y)
    (hwealth : ∃ a, 0 < p ⬝ᵥ x a) :
    p ⬝ᵥ E.aggregateExcess x = 0 := by
  classical
  have hx_nn : ∀ a l, 0 ≤ x a l := hpareto.feasible.nonneg
  set z : Fin L → ℝ := E.aggregateExcess x with hz
  have hz_nonpos : ∀ l, z l ≤ 0 := fun l => hpareto.feasible.excess_nonpos l
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
  -- The dominating allocation: bump only `a₀`'s coordinate `l₀` by the slack.
  set y : E.Agents → Fin L → ℝ :=
    fun a l => x a l + (if a = a₀ ∧ l = l₀ then slack else 0) with hy
  have hy_nn : ∀ a l, 0 ≤ y a l := by
    intro a l
    simp only [hy]
    split
    · linarith [hx_nn a l]
    · linarith [hx_nn a l]
  -- The aggregate excess of `y` matches `x` away from `l₀`, and is exactly `0` at `l₀`.
  have hagg_y : ∀ l, E.aggregateExcess y l = z l + (if l = l₀ then slack else 0) := by
    intro l
    have hsum_y : (∑ a, y a l) = (∑ a, x a l) + (if l = l₀ then slack else 0) := by
      simp only [hy]
      rw [Finset.sum_add_distrib]
      congr 1
      by_cases hl : l = l₀
      · subst hl
        simp only [and_true]
        rw [Finset.sum_ite_eq' Finset.univ a₀ (fun _ => slack)]
        simp only [Finset.mem_univ, if_true]
      · simp only [hl, and_false, if_false, Finset.sum_const_zero]
    -- `aggregateExcess` is definitionally total consumption minus total endowment.
    change (∑ a, y a l) - (∑ a, E.endow a l) = z l + (if l = l₀ then slack else 0)
    rw [hsum_y, hz]
    change (∑ a, x a l) + (if l = l₀ then slack else 0) - (∑ a, E.endow a l) =
      ((∑ a, x a l) - (∑ a, E.endow a l)) + (if l = l₀ then slack else 0)
    ring
  -- `y` is feasible: nonpositive excess everywhere, with the slack exactly cancelling at `l₀`.
  have hy_feas : E.Feasible y := by
    refine ⟨hy_nn, fun l => ?_⟩
    rw [hagg_y l]
    by_cases hl : l = l₀
    · subst hl; simp only [if_true, hslack]; linarith
    · simp only [hl, if_false, add_zero]; exact hz_nonpos l
  -- `a₀` strictly improves: `x a₀ ≤ y a₀`, they differ at `l₀`, and `x a₀` is weakly preferred to
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
  -- `x a₀ ≽ w`: otherwise `le_total` makes `w ≻ x a₀`, but then the support inequality says
  -- `p ⬝ᵥ x a₀ ≤ p ⬝ᵥ w`, contradicting that `w` is strictly cheaper.
  have hxa_ge_w : x a₀ ≽[E.pref a₀] w := by
    by_contra hge
    have hle' : w ≽[E.pref a₀] x a₀ :=
      ((E.pref a₀).le_total w (x a₀)).resolve_right hge
    have hw_orth : w ∈ nonnegOrthant L := fun l => (hw_pos l).le
    have hsup := hsupp a₀ w hw_orth ⟨hle', hge⟩
    linarith
  have hxa_le_ya : x a₀ ≤ y a₀ := by
    intro l
    simp only [hy]
    split
    · linarith [hslack_pos]
    · linarith
  have hxa_ne_ya : x a₀ ≠ y a₀ := by
    intro heq
    have hcontra := congr_fun heq l₀
    simp only [hy, and_true, if_true] at hcontra
    linarith [hslack_pos]
  have hya_pref : y a₀ ≻[E.pref a₀] x a₀ :=
    (hreg.desirable a₀).improve hw_pos hxa_ge_w hxa_le_ya hxa_ne_ya
  -- `y` Pareto-dominates `x`: untouched agents are unchanged, and `a₀` strictly gains.
  have hy_dom : E.ParetoDominates y x := by
    refine ⟨fun a => ?_, ⟨a₀, hya_pref⟩⟩
    by_cases ha : a = a₀
    · subst ha; exact hya_pref.1
    · have : y a = x a := by
        funext l
        simp only [hy, ha, false_and, if_false, add_zero]
      rw [this]; exact (E.pref a).le_refl (x a)
  exact hpareto.undominated ⟨y, hy_feas, hy_dom⟩

/-- **Second Welfare Theorem — full decentralization with lump-sum transfers.** Every Pareto
optimal allocation `x` of a regular, McKenzie-irreducible exchange economy in which every good is
consumed (`hcons`) is a **Walrasian equilibrium with lump-sum transfers**: There is a nonnegative
nonzero price `p`, a balanced transfer scheme `t a = p ⬝ᵥ x a − p ⬝ᵥ endow a` (`∑ t = 0`), at which
every agent — including zero-wealth ones — holds a `≽`-maximal bundle in its transfer-adjusted
budget `budgetSetAt p (p ⬝ᵥ endow a + t a)`, and markets clear. Irreducibility (of the allocation
viewed as an endowment profile, `E.transferEndow`) closes the minimum-wealth gap that
`exists_quasiEquilibrium_price` leaves open. The returned `W` is a complete equilibrium on its own
(every field of `WalrasianEquilibriumWithTransfers`); the conclusion `W.Decentralizes x` records
only that it implements the *given* optimum `x` with the supporting balanced transfer scheme. -/
theorem ParetoOptimal.exists_walrasianEquilibriumWithTransfers (hne : Nonempty E.Agents)
    (hreg : RegularEconomy E) (hL : 0 < L)
    {x : E.Agents → Fin L → ℝ} (hpareto : E.ParetoOptimal x)
    (hcons : ∀ l, ∃ a, 0 < x a l)
    (hirr : Irreducible (E.transferEndow (fun a => hpareto.feasible.nonneg a))) :
    ∃ W : E.WalrasianEquilibriumWithTransfers, W.Decentralizes x := by
  classical
  haveI : Finite E.Agents := Finite.of_fintype _
  -- The relabeled economy whose endowments are `x`: its wealth at `p` is `p ⬝ᵥ x a`.
  set E' : Economy L := E.transferEndow (fun a => hpareto.feasible.nonneg a) with hE'
  -- Supporting (quasi-equilibrium) price for the Pareto optimum.
  obtain ⟨p₀, hp₀_nn, hp₀_ne, hsupp₀⟩ := hpareto.exists_supporting_price hne hreg hL
  -- Normalize to the price simplex (scale-invariant; budgets and demand are homogeneous deg 0).
  obtain ⟨q, hq_simplex, hq_ne, hsupp, hscale⟩ :
      ∃ q : Fin L → ℝ, q ∈ priceSimplex L ∧ (∃ l, 0 < q l) ∧
        (∀ a y, y ∈ nonnegOrthant L → (y ≻[E.pref a] x a) → q ⬝ᵥ x a ≤ q ⬝ᵥ y) ∧
        ∃ t : ℝ, 0 < t ∧ q = t • p₀ := by
    obtain ⟨l_pos, hl_pos⟩ := hp₀_ne
    set S : ℝ := ∑ l, p₀ l with hS
    have hS_pos : 0 < S :=
      Finset.sum_pos' (fun l _ => hp₀_nn l) ⟨l_pos, Finset.mem_univ l_pos, hl_pos⟩
    set t : ℝ := S⁻¹ with ht
    have ht_pos : 0 < t := by rw [ht]; positivity
    refine ⟨t • p₀, ?_, ?_, ?_, ⟨t, ht_pos, rfl⟩⟩
    · refine ⟨fun l => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg ht_pos.le (hp₀_nn l)
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum, ← hS, ht, inv_mul_cancel₀ (ne_of_gt hS_pos)]
    · exact ⟨l_pos, by simp only [Pi.smul_apply, smul_eq_mul]; positivity⟩
    · intro a y hy_orth hy_lt
      rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hsupp₀ a y hy_orth hy_lt) ht_pos.le
  have hq_nn : ∀ l, 0 ≤ q l := fun l => hq_simplex.1 l
  -- Positive-wealth witness: some positively-priced good is consumed.
  have hwealth : ∃ a, 0 < q ⬝ᵥ x a := by
    -- A positively-priced good `l₀` that is consumed by some agent `a` gives that agent positive
    -- wealth: its single `l₀`-term `q l₀ * x a l₀ > 0` bounds the (nonnegative-termed) dot product.
    obtain ⟨l₀, hl₀_pos⟩ := hq_ne
    obtain ⟨a, ha_pos⟩ := hcons l₀
    refine ⟨a, ?_⟩
    have hterm_pos : 0 < q l₀ * x a l₀ := mul_pos hl₀_pos ha_pos
    have hsingle_le : q l₀ * x a l₀ ≤ q ⬝ᵥ x a := by
      rw [dotProduct]
      exact Finset.single_le_sum
        (fun l _ => mul_nonneg (hq_nn l) (hpareto.feasible.nonneg a l)) (Finset.mem_univ l₀)
    exact lt_of_lt_of_le hterm_pos hsingle_le
  -- Feed the supporting price into the McKenzie upgrade on the relabeled economy `E'`.
  -- There the allocation `x` is the endowment, so budgets bind trivially and the supporting
  -- inequality is the quasi-equilibrium condition.
  have hbud' : ∀ a, x a ∈ E'.budgetSet q a := fun a => ⟨hpareto.feasible.nonneg a, le_refl _⟩
  have hbind' : ∀ a, q ⬝ᵥ x a = q ⬝ᵥ E'.endow a := fun _ => rfl
  have hIR' : ∀ a, x a ≽[E'.pref a] E'.endow a := fun a => (E.pref a).le_refl (x a)
  have hquasi' : ∀ a y, (∀ l, 0 ≤ y l) → q ⬝ᵥ y < q ⬝ᵥ E'.endow a →
      ¬ (y ≻[E'.pref a] x a) := by
    intro a y hy_nn hy_cheap hy_lt
    exact absurd (hsupp a y hy_nn hy_lt) (not_le.mpr hy_cheap)
  have hagg' : ∃ a, 0 < q ⬝ᵥ E'.endow a := hwealth
  obtain ⟨hq_pos, hopt'⟩ :=
    E'.quasi_to_walrasian hne (fun a => hreg.contPref a) (fun a => hreg.desirable a) hirr
      hq_simplex hbud' hbind' hIR' hquasi' hagg'
  -- Market clearing in value (transfers balance) from non-wastefulness.
  have hval_zero : q ⬝ᵥ E.aggregateExcess x = 0 :=
    hpareto.aggregateExcess_value_zero hreg hq_nn hsupp hwealth
  have hclears : E.MarketClears q x := ⟨hpareto.feasible.excess_nonpos, hval_zero⟩
  refine ⟨{
    price := q
    alloc := x
    transfer := fun a => q ⬝ᵥ x a - q ⬝ᵥ E.endow a
    price_cone := hq_nn
    price_ne := hq_ne
    transfers_balance := ?_
    isOptimal := ?_
    clears := hclears }, ⟨rfl, fun a => rfl⟩⟩
  · rw [← E.dotProduct_aggregateExcess q x]
    exact hval_zero
  · intro a
    have hbudget_eq : q ⬝ᵥ E.endow a + (q ⬝ᵥ x a - q ⬝ᵥ E.endow a) = q ⬝ᵥ x a := by ring
    rw [hbudget_eq]
    exact hopt' a

end Economy

end Econlib.Equilibrium
