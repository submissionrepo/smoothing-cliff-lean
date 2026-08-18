/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Production technology and attainable sets

This file defines the firm-side technology objects used by production economies. A `Technology L`
is a production-possibility set `Y ⊆ Fin L → ℝ` of net-output vectors, with negative coordinates
representing inputs and positive coordinates representing outputs.

The regularity structure `RegularTechnology` collects the production-set assumptions used in the
convex general-equilibrium existence files: Closedness, convexity, feasible inaction, free
disposal, no free lunch, and irreversibility.

The file also defines the profit function `Technology.profit` and the supply correspondence
`Technology.supply`. Profit is the value of linear revenue over the production set, while supply is
the set of profit-maximizing production plans at a price vector.

The main compactness result is `isCompact_attainable`: If a production set is closed, convex,
contains inaction, and satisfies no free lunch, then the part compatible with a finite resource
lower bound, `Y ∩ {y | ∀ l, -e l ≤ y l}`, is compact. The lemma
`RegularTechnology.isCompact_attainable` packages this statement for regular technologies.

## Main definitions

* `Technology`: A production-possibility set of net-output vectors.
* `RegularTechnology`: The regularity bundle (closed, convex, inaction feasible, free disposal, no
  free lunch, irreversibility) for the convex existence case.
* `Technology.profit`: The profit function (support function of `T.Y`).
* `Technology.supply`: The supply correspondence (profit-maximizing face of `T.Y`).

## Main statements

* `isCompact_attainable`: The resource-bounded attainable set is compact under closedness,
  convexity, inaction, and no free lunch.
* `Technology.supply_convex`: The supply correspondence is convex-valued.
* `Technology.profit_eq_dotProduct_of_mem_supply`: A supply plan realizes profit.
* `Technology.dotProduct_le_profit_of_mem_supply`: Feasible plans earn at most profit.
* `Technology.supply_eq_empty_of_free_input`: A positively valued scalable production ray rules out
  a profit-maximizing supply plan.
* `RegularTechnology.isCompact_attainable`: Compact attainable set for regular technologies.

## References

* Debreu, Gérard. 1959. *Theory of Value: An Axiomatic Analysis of Economic Equilibrium*. Wiley.

## Tags

production, technology, attainable set, profit, supply correspondence, arrow-debreu
-/

@[expose] public section

namespace Econlib.Equilibrium

open Matrix

variable {L : ℕ}

/-! ## Technologies -/

/-- A **firm technology** is a production-possibility set of net-output vectors (inputs negative,
outputs positive). -/
structure Technology (L : ℕ) where
  /-- The production-possibility set. -/
  Y : Set (Fin L → ℝ)

/-- The regularity bundle for the convex existence case (parallels `RegularEconomy`), collecting
the Arrow–Debreu production-set axioms (Debreu 1959). `no_free_lunch` and `irreversible`, together
with the resource bound, make the attainable set compact. -/
structure RegularTechnology (T : Technology L) where
  /-- The production set is closed. -/
  closed : IsClosed T.Y
  /-- The production set is convex (no increasing returns). -/
  convex : Convex ℝ T.Y
  /-- Inaction (shutdown) is feasible. -/
  inaction : (0 : Fin L → ℝ) ∈ T.Y
  /-- Free disposal: Any pointwise-smaller net-output vector is also feasible. -/
  free_disposal : ∀ y ∈ T.Y, ∀ y', (∀ l, y' l ≤ y l) → y' ∈ T.Y
  /-- No free lunch: The only nonnegative net-output plan is inaction (`Y ∩ ℝ^L_+ = {0}`). -/
  no_free_lunch : ∀ y ∈ T.Y, (∀ l, 0 ≤ y l) → y = 0
  /-- Irreversibility: No nonzero plan can be reversed (`Y ∩ -Y = {0}`). -/
  irreversible : ∀ y ∈ T.Y, -y ∈ T.Y → y = 0

/-- The **profit** of technology `T` at prices `p`: `sup_{y ∈ T.Y} p ⬝ᵥ y` (the support function of
`T.Y`).

This is a totalized real-valued supremum (`Optimization.valueFunction`, defined via `sSup`): When
revenue is unbounded above on `T.Y` the value is the junk value `0` of an unbounded `sSup` rather
than a finite optimum, so `profit` is meaningful only when revenue is bounded above. The unbounded
case is handled through supply, not through this value: `Technology.supply_eq_empty_of_free_input`
shows that a positively valued recession ray forces an empty supply correspondence, so no
equilibrium plan attains the spurious value. -/
noncomputable def Technology.profit (T : Technology L) (p : Fin L → ℝ) : ℝ :=
  Optimization.valueFunction (fun y => p ⬝ᵥ y) T.Y

/-- The **supply correspondence** of technology `T` at prices `p`: The profit-maximizing face of
`T.Y`. -/
noncomputable def Technology.supply (T : Technology L) (p : Fin L → ℝ) : Set (Fin L → ℝ) :=
  Optimization.argmax (fun y => p ⬝ᵥ y) T.Y

/-- **Attainable-set compactness.** If `Y` is closed and convex, contains the origin, satisfies no
free lunch (`Y ∩ ℝ^L_+ = {0}`), and `e` is a resource bound, then `Y ∩ {y | ∀ l, -e l ≤ y l}` is
compact. -/
theorem isCompact_attainable (Y : Set (Fin L → ℝ)) (e : Fin L → ℝ)
    (hYclosed : IsClosed Y) (hYconv : Convex ℝ Y) (hY0 : (0 : Fin L → ℝ) ∈ Y)
    (hnfl : ∀ y ∈ Y, (∀ l, 0 ≤ y l) → y = 0) :
    IsCompact (Y ∩ {y : Fin L → ℝ | ∀ l, -e l ≤ y l}) := by
  have hbox_closed : IsClosed {y : Fin L → ℝ | ∀ l, -e l ≤ y l} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
  have hAclosed : IsClosed (Y ∩ {y : Fin L → ℝ | ∀ l, -e l ≤ y l}) := hYclosed.inter hbox_closed
  -- Boundedness via a recession argument: if unbounded, normalize to find a nonneg unit vector in
  -- `Y`, contradicting no free lunch.
  have hAbdd : Bornology.IsBounded (Y ∩ {y : Fin L → ℝ | ∀ l, -e l ≤ y l}) := by
    by_contra hub
    have hstep : ∀ n : ℕ, ∃ z, z ∈ Y ∩ {y : Fin L → ℝ | ∀ l, -e l ≤ y l} ∧ (n : ℝ) < ‖z‖ := by
      intro n
      by_contra hcon
      push Not at hcon
      exact hub ((Metric.isBounded_iff_subset_closedBall 0).mpr
        ⟨n, fun z hz => by simpa [Metric.mem_closedBall, dist_zero_right] using hcon z hz⟩)
    choose y hy_memA hy_gt using hstep
    have hy_mem : ∀ n, y n ∈ Y := fun n => (hy_memA n).1
    have hy_box : ∀ n, ∀ l, -e l ≤ y n l := fun n => (hy_memA n).2
    have hy_pos : ∀ n, 0 < ‖y n‖ := fun n => lt_of_le_of_lt (Nat.cast_nonneg n) (hy_gt n)
    have hnorm_top : Filter.Tendsto (fun n => ‖y n‖) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => (hy_gt n).le) tendsto_natCast_atTop_atTop
    set d := fun n => (‖y n‖)⁻¹ • y n with hddef
    have hd_norm : ∀ n, ‖d n‖ = 1 := by
      intro n
      simp only [hddef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hy_pos n))]
      exact inv_mul_cancel₀ (ne_of_gt (hy_pos n))
    have hd_ball : ∀ n, d n ∈ Metric.closedBall (0 : Fin L → ℝ) 1 := fun n => by
      rw [Metric.mem_closedBall, dist_zero_right, hd_norm n]
    obtain ⟨dstar, -, φ, hφ_mono, hφ_lim⟩ :=
      (isCompact_closedBall (0 : Fin L → ℝ) 1).tendsto_subseq hd_ball
    have hdstar_norm : ‖dstar‖ = 1 := by
      have hlim : Filter.Tendsto (fun n => ‖d (φ n)‖) Filter.atTop (nhds ‖dstar‖) :=
        (continuous_norm.tendsto dstar).comp hφ_lim
      simp only [hd_norm] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    have hsub_top : Filter.Tendsto (fun n => ‖y (φ n)‖) Filter.atTop Filter.atTop :=
      hnorm_top.comp hφ_mono.tendsto_atTop
    -- The ray `{t • dstar | t ≥ 0}` lies in `Y`: each `t • d (φ n)` is a convex combination of `0`
    -- and `y (φ n)` in `Y`, and the limit is in the closed set.
    have hray : ∀ t : ℝ, 0 ≤ t → t • dstar ∈ Y := by
      intro t ht
      refine hYclosed.mem_of_tendsto (hφ_lim.const_smul t) ?_
      filter_upwards [hsub_top.eventually_ge_atTop t] with n hn
      simp only [Function.comp_apply]
      have hsmul_eq : t • d (φ n) = (t / ‖y (φ n)‖) • y (φ n) := by
        simp only [hddef, smul_smul]; rw [← div_eq_mul_inv]
      rw [hsmul_eq]
      refine hYconv.smul_mem_of_zero_mem hY0 (hy_mem (φ n)) ⟨by positivity, ?_⟩
      rw [div_le_one (hy_pos (φ n))]; exact hn
    -- `dstar ≥ 0` componentwise: the lower bound `-e l` is washed out after normalization.
    have hdstar_nonneg : ∀ l, 0 ≤ dstar l := by
      intro l
      have hcomp_lim : Filter.Tendsto (fun n => d (φ n) l) Filter.atTop (nhds (dstar l)) :=
        ((continuous_apply l).tendsto dstar).comp hφ_lim
      have hlow : Filter.Tendsto (fun n => (‖y (φ n)‖)⁻¹ * (-e l)) Filter.atTop (nhds 0) := by
        simpa using hsub_top.inv_tendsto_atTop.mul_const (-e l)
      refine le_of_tendsto_of_tendsto hlow hcomp_lim ?_
      filter_upwards with n
      simp only [hddef, Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hy_box (φ n) l) (le_of_lt (inv_pos.mpr (hy_pos (φ n))))
    have hdstar_inY : dstar ∈ Y := by simpa using hray 1 (by norm_num)
    rw [hnfl dstar hdstar_inY hdstar_nonneg, norm_zero] at hdstar_norm
    norm_num at hdstar_norm
  exact Metric.isCompact_of_isClosed_isBounded hAclosed hAbdd

/-- **Supply is convex-valued.** The profit-maximizing face of a convex set is convex. -/
lemma Technology.supply_convex (T : Technology L) (hconv : Convex ℝ T.Y) (p : Fin L → ℝ) :
    Convex ℝ (T.supply p) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  obtain ⟨hy₁S, hy₁max⟩ := hy₁
  obtain ⟨hy₂S, hy₂max⟩ := hy₂
  refine ⟨hconv hy₁S hy₂S ha hb hab, ?_⟩
  intro w hw
  have hval : p ⬝ᵥ (a • y₁ + b • y₂) = a * (p ⬝ᵥ y₁) + b * (p ⬝ᵥ y₂) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  change p ⬝ᵥ w ≤ p ⬝ᵥ (a • y₁ + b • y₂)
  rw [hval]
  have h1 : p ⬝ᵥ w ≤ p ⬝ᵥ y₁ := hy₁max hw
  have h2 : p ⬝ᵥ w ≤ p ⬝ᵥ y₂ := hy₂max hw
  have hsum : a * (p ⬝ᵥ w) + b * (p ⬝ᵥ w) = p ⬝ᵥ w := by rw [← add_mul, hab, one_mul]
  exact hsum ▸ add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **A supply plan realizes profit.** If `y ∈ T.supply p` then `T.profit p = p ⬝ᵥ y`. -/
lemma Technology.profit_eq_dotProduct_of_mem_supply (T : Technology L) {p y : Fin L → ℝ}
    (hy : y ∈ T.supply p) : T.profit p = p ⬝ᵥ y := by
  obtain ⟨hyY, hymax⟩ := hy
  have hbdd : BddAbove ((fun z => p ⬝ᵥ z) '' T.Y) :=
    ⟨p ⬝ᵥ y, by rintro _ ⟨z, hz, rfl⟩; exact hymax hz⟩
  refine le_antisymm (csSup_le ⟨p ⬝ᵥ y, y, hyY, rfl⟩ ?_) (le_csSup hbdd ⟨y, hyY, rfl⟩)
  rintro _ ⟨z, hz, rfl⟩; exact hymax hz

/-- **Feasible plans earn at most profit.** If `y ∈ T.supply p` and `z ∈ T.Y`, then
`p ⬝ᵥ z ≤ T.profit p`. -/
lemma Technology.dotProduct_le_profit_of_mem_supply (T : Technology L) {p z y : Fin L → ℝ}
    (hz : z ∈ T.Y) (hy : y ∈ T.supply p) : p ⬝ᵥ z ≤ T.profit p := by
  rw [T.profit_eq_dotProduct_of_mem_supply hy]; exact hy.2 hz

/-- **Free input ⇒ empty supply.** If `d` is a nonnegative-scaling recession ray of `T.Y` and
`p ⬝ᵥ d > 0`, then profit is unbounded and `T.supply p = ∅`. -/
theorem Technology.supply_eq_empty_of_free_input (T : Technology L) {p d : Fin L → ℝ}
    (hray : ∀ t : ℝ, 0 ≤ t → t • d ∈ T.Y) (hpos : 0 < p ⬝ᵥ d) :
    T.supply p = ∅ := by
  refine Set.eq_empty_of_forall_notMem (fun x hx => ?_)
  obtain ⟨_hxY, hxmax⟩ := hx
  set t : ℝ := max (p ⬝ᵥ x) 0 / (p ⬝ᵥ d) + 1 with ht_def
  have ht0 : 0 ≤ t := by
    have hdiv : 0 ≤ max (p ⬝ᵥ x) 0 / (p ⬝ᵥ d) := div_nonneg (le_max_right _ _) hpos.le
    rw [ht_def]; linarith
  have hle : p ⬝ᵥ (t • d) ≤ p ⬝ᵥ x := hxmax (hray t ht0)
  rw [dotProduct_smul, smul_eq_mul] at hle
  have htc : t * (p ⬝ᵥ d) = max (p ⬝ᵥ x) 0 + (p ⬝ᵥ d) := by
    rw [ht_def, add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
  have hxle : p ⬝ᵥ x ≤ max (p ⬝ᵥ x) 0 := le_max_left _ _
  linarith

/-- A regular technology has a compact attainable set at any resource bound `e`. -/
lemma RegularTechnology.isCompact_attainable {T : Technology L} (hT : RegularTechnology T)
    (e : Fin L → ℝ) :
    IsCompact (T.Y ∩ {y : Fin L → ℝ | ∀ l, -e l ≤ y l}) :=
  Econlib.Equilibrium.isCompact_attainable T.Y e hT.closed hT.convex hT.inaction hT.no_free_lunch

/-! ## The one-input/one-output labor activity cone -/

/-- The **labor activity cone** in two goods: Labor (good `0`) is an input (`y₀ ≤ 0`) and output
(good `1`) is bounded by the labor used (`y₁ + y₀ ≤ 0`). This is the canonical constant-returns
firm that turns labor into output. The `y₀ ≤ 0` truncation makes it genuinely **irreversible** — a
plain half-space `{y₀ + y₁ ≤ 0}` is not, since its frontier line lies in `Y ∩ -Y`. -/
def laborConeTech : Technology 2 := ⟨{ y | y 0 ≤ 0 ∧ y 1 + y 0 ≤ 0 }⟩

@[simp] lemma laborConeTech_Y :
    laborConeTech.Y = { y : Fin 2 → ℝ | y 0 ≤ 0 ∧ y 1 + y 0 ≤ 0 } := rfl

/-- The labor cone satisfies every `RegularTechnology` field, including irreversibility (which the
`y₀ ≤ 0` truncation supplies). -/
theorem laborConeTech_regular : RegularTechnology laborConeTech where
  closed := by
    rw [laborConeTech, Set.setOf_and]
    exact (isClosed_le (continuous_apply 0) continuous_const).inter
      (isClosed_le ((continuous_apply 1).add (continuous_apply 0)) continuous_const)
  convex := by
    rintro x ⟨hx0, hx2⟩ y ⟨hy0, hy2⟩ a b ha hb _
    refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx0, mul_nonpos_of_nonneg_of_nonpos hb hy0]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx2, mul_nonpos_of_nonneg_of_nonpos hb hy2]
  inaction := by constructor <;> simp
  free_disposal := by
    rintro y ⟨hy0, hy2⟩ y' hy'
    exact ⟨le_trans (hy' 0) hy0, by have := hy' 0; have := hy' 1; linarith⟩
  no_free_lunch := by
    rintro y ⟨hy0, hy2⟩ hpos
    have h0 : y 0 = 0 := le_antisymm hy0 (hpos 0)
    have h1 : y 1 = 0 := le_antisymm (by linarith [hpos 0]) (hpos 1)
    funext l; fin_cases l
    · exact h0
    · exact h1
  irreversible := by
    rintro y ⟨hy0, hy2⟩ hny
    simp only [laborConeTech, Set.mem_setOf_eq, Pi.neg_apply] at hny
    have h0 : y 0 = 0 := le_antisymm hy0 (by linarith [hny.1])
    have h1 : y 1 = 0 := le_antisymm (by linarith [hny.1]) (by linarith [hny.2, hy0])
    funext l; fin_cases l
    · exact h0
    · exact h1

/-- The labor cone is closed under addition (the two half-space inequalities add). Used to feasibly
*increment* a current production plan by the labor ray `(-1, 1)`. -/
theorem laborConeTech_add_mem {a b : Fin 2 → ℝ} (ha : a ∈ laborConeTech.Y)
    (hb : b ∈ laborConeTech.Y) : a + b ∈ laborConeTech.Y := by
  obtain ⟨ha0, ha2⟩ := ha
  obtain ⟨hb0, hb2⟩ := hb
  exact ⟨by simp only [Pi.add_apply]; linarith, by simp only [Pi.add_apply]; linarith⟩

/-- The labor recession ray `(-1, 1)` lies in the cone. -/
theorem laborConeRay_mem : (![-1, 1] : Fin 2 → ℝ) ∈ laborConeTech.Y :=
  ⟨by norm_num, by norm_num⟩

/-- Every nonnegative scaling `t • (-1, 1)` of the labor ray is feasible: The cone is a genuine
recession cone of `laborConeTech`, so the ray is a *free input* witness for
`Technology.supply_eq_empty_of_free_input`. -/
theorem laborConeRay_smul_mem {t : ℝ} (ht : 0 ≤ t) :
    t • (![-1, 1] : Fin 2 → ℝ) ∈ laborConeTech.Y := by
  refine ⟨?_, ?_⟩
  · simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]; nlinarith
  · simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]; nlinarith

end Econlib.Equilibrium
