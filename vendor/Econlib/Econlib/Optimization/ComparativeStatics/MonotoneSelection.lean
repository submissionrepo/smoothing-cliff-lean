/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.StrongSetOrder
public import Econlib.Optimization.Basic
public import Econlib.Preferences.Geometry.Basic
public import Econlib.Preferences.Geometry.SingleCrossing

/-!
# Milgrom–Shannon Monotone Selection

Argmax sets are monotone in the strong set order under the single-crossing property (Milgrom and
Shannon 1994, Theorem 4), specialized to a linearly ordered action space. The Topkis theorems
(Topkis 1978) are recovered as corollaries via
`StrictIncreasingDifferences.toCardinalSingleCrossing`, and their flat-top (supermodular) analogs
via `Supermodular.toWeakCardinalSingleCrossing`.

## Main definitions

* `argmaxRel`: The set of maximal elements under a preference relation (ordinal argmax).

## Main statements

* `argmaxRel_le_of_singleCrossing`: Ordinal single crossing implies every maximizer at `θ₁` is
  weakly below every maximizer at `θ₂ > θ₁`.
* `argmax_le_of_singleCrossing`: Cardinal single crossing analog over `ℝ`.
* `argmax_strongSetOrder_of_singleCrossing`: Argmax sets are monotone in the strong set order.
* `argmax_strongSetOrder_of_weakSingleCrossing`: Milgrom–Shannon Theorem 4 proper — the strong set
  order from the *weak* single-crossing property, covering flat-top objectives whose argmax sets
  overlap.
* `sSup_argmax_monotone_of_singleCrossing`, `sInf_argmax_monotone_of_singleCrossing`: Monotonicity
  of the upper and lower selections.
* `sSup_argmax_monotone_of_weakSingleCrossing`, `sInf_argmax_monotone_of_weakSingleCrossing`:
  Monotonicity of the upper and lower selections under the *weak* single-crossing property,
  covering flat-top objectives — derived from the strong set order alone.
* `sSup_argmax_monotone_of_strictIncreasingDifferences` and its `sInf` analog: Topkis corollaries
  under `StrictIncreasingDifferences`.
* `sSup_argmax_monotone_of_supermodular` and its `sInf` analog: Weak (flat-top) Topkis corollaries
  under `Supermodular`.

## References

* Milgrom, Paul, and Chris Shannon. 1994. “Monotone Comparative Statics.” *Econometrica* 62 (1):
  157. [https://doi.org/10.2307/2951479](https://doi.org/10.2307/2951479).
* Topkis, Donald M. 1978. “Minimizing a Submodular Function on a Lattice.” *Operations Research* 26
  (2): 305–21. [https://doi.org/10.1287/opre.26.2.305](https://doi.org/10.1287/opre.26.2.305).

## Tags

monotone selection, milgrom-shannon, single crossing, topkis, comparative statics, strong set order
-/

@[expose] public section

namespace Econlib.Optimization

open Econlib.Preferences

variable {Θ : Type*} [LinearOrder Θ]

/-! ## Relation-level Milgrom–Shannon -/

/-- The set of maximal elements of `S` under a preference relation. This is the ordinal analog of
`argmax`, which is specialized to real-valued objectives. Nonemptiness on finite alternative spaces
is `Preferences.PreferenceRel.exists_greatest_on`; on compact sets it comes from Berge. -/
def argmaxRel {X : Type*} (R : PreferenceRel X) (S : Set X) : Set X :=
  {x | x ∈ S ∧ ∀ y ∈ S, PreferenceRel.le R x y}

/-- **The real-objective `argmax` is the preference `argmaxRel`** whenever the objective represents
the preference. This bridges Berge's `argmax`-based maximum theorem to the greatest-element (demand
or best-response) reading. -/
theorem argmax_eq_argmaxRel_of_represents {X : Type*} [TopologicalSpace X]
    {R : PreferenceRel X} {u : X → ℝ} (hu : RepresentsRealPreference R u) (S : Set X) :
    argmax u S = argmaxRel R S := by
  ext x
  simp only [argmax, argmaxRel, Set.mem_setOf_eq, isMaxOn_iff]
  refine and_congr_right fun _ => ⟨fun hmax y hy => (hu x y).mpr (hmax y hy),
    fun hle y hy => (hu x y).mp (hle y hy)⟩

/-- **Strict convexity of preferences ⇒ single-valued demand.** On a convex feasible set, a
strictly convex preference has at most one maximal element. The midpoint of two distinct maximizers
would be strictly preferred to one of them, contradicting maximality. -/
theorem argmaxRel_subsingleton_of_strictConvex {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {R : PreferenceRel E} (hconv : StrictConvexPreference R) {S : Set E} (hS : Convex ℝ S) :
    (argmaxRel R S).Subsingleton := by
  intro x hx y hy
  by_contra hne
  -- Both are maximal, so each is at least as good as the other; the midpoint lies in `S`.
  obtain ⟨hxS, hxmax⟩ := hx
  obtain ⟨hyS, hymax⟩ := hy
  have hmid : ((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • y ∈ S :=
    hS hxS hyS (by norm_num) (by norm_num) (by norm_num)
  -- Strict convexity (with `z := x`, using `x ≽ x` and `y ≽ x`) makes the midpoint strictly better
  -- than `x`; but `x` is maximal, so `x ≽ midpoint`, a contradiction.
  have hbetter : (((1 : ℝ) / 2) • x + ((1 : ℝ) / 2) • y) ≻[R] x :=
    hconv.strict_convex hne (R.le_refl x) (hymax x hxS) (by norm_num) (by norm_num) (by norm_num)
  exact hbetter.2 (hxmax _ hmid)

section RelationLevel

variable {X : Type*} [LinearOrder X]

/-- **Milgrom–Shannon monotone selection, relation-level version.**

If an ordered family of preferences satisfies ordinal single crossing, then every maximizer for a
lower type is weakly below every maximizer for a higher type. -/
theorem argmaxRel_le_of_singleCrossing {R : Θ → PreferenceRel X} {S : Set X}
    (hsc : SingleCrossingRel R)
    (θ₁ θ₂ : Θ) (hθ : θ₁ < θ₂)
    {x₁ x₂ : X}
    (hx₁ : x₁ ∈ argmaxRel (R θ₁) S)
    (hx₂ : x₂ ∈ argmaxRel (R θ₂) S) :
    x₁ ≤ x₂ := by
  by_contra h_not_le
  push Not at h_not_le
  have h_opt₁ : PreferenceRel.le (R θ₁) x₁ x₂ := hx₁.2 x₂ hx₂.1
  have h_scp := hsc.weak_crossing θ₁ θ₂ x₂ x₁ hθ h_not_le h_opt₁
  have h_opt₂ : PreferenceRel.le (R θ₂) x₂ x₁ := hx₂.2 x₁ hx₁.1
  exact h_scp.2 h_opt₂

/-- Relation-level Milgrom–Shannon implies argmax sets are monotone in the strong set order on a
linear order. -/
theorem argmaxRel_strongSetOrder_of_singleCrossing {R : Θ → PreferenceRel X} {S : Set X}
    (hsc : SingleCrossingRel R)
    (θ₁ θ₂ : Θ) (hθ : θ₁ < θ₂) :
    StrongSetOrder (argmaxRel (R θ₁) S) (argmaxRel (R θ₂) S) :=
  strongSetOrder_of_forall_le fun _ ha _ hb => argmaxRel_le_of_singleCrossing hsc θ₁ θ₂ hθ ha hb

/-- If each type has a selected maximal action, ordinal single crossing makes the selection
monotone. -/
theorem argmaxRel_monotone_of_singleCrossing {R : Θ → PreferenceRel X} {S : Set X}
    (hsc : SingleCrossingRel R)
    (x_star : Θ → X)
    (h_mem : ∀ θ, x_star θ ∈ S)
    (h_opt : ∀ θ, ∀ x ∈ S, PreferenceRel.le (R θ) (x_star θ) x) :
    Monotone x_star := by
  intro θ₁ θ₂ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_refl _
  exact argmaxRel_le_of_singleCrossing hsc θ₁ θ₂ hθ_lt
    ⟨h_mem θ₁, h_opt θ₁⟩ ⟨h_mem θ₂, h_opt θ₂⟩

end RelationLevel

/-! ## Real-valued Milgrom–Shannon -/

/-- **Milgrom–Shannon Monotone Selection Theorem** (linear order case).

If `u : Θ → ℝ → ℝ` satisfies the single-crossing property, then for `θ₁ < θ₂`, every maximizer at
`θ₁` is weakly below every maximizer at `θ₂`. This is monotonicity of the argmax correspondence in
the strong set order.

This is the principal MCS result of the file; `sSup_argmax_monotone_of_strictIncreasingDifferences`
and its `sInf` analog below are corollaries under the strictly stronger
`StrictIncreasingDifferences` hypothesis. -/
theorem argmax_le_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u)
    (θ₁ θ₂ : Θ) (hθ : θ₁ < θ₂)
    {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ argmax (u θ₁) S)
    (hx₂ : x₂ ∈ argmax (u θ₂) S) :
    x₁ ≤ x₂ := by
  by_contra h_not_le
  push Not at h_not_le
  have h_opt₁ : u θ₁ x₂ ≤ u θ₁ x₁ := isMaxOn_iff.mp hx₁.2 x₂ hx₂.1
  have h_scp := hsc.weak_crossing θ₁ θ₂ x₂ x₁ hθ h_not_le (by linarith)
  have h_opt₂ : u θ₂ x₁ ≤ u θ₂ x₂ := isMaxOn_iff.mp hx₂.2 x₁ hx₁.1
  linarith

/-- Milgrom–Shannon implies argmax sets are monotone in the strong set order. -/
theorem argmax_strongSetOrder_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u)
    (θ₁ θ₂ : Θ) (hθ : θ₁ < θ₂) :
    StrongSetOrder (argmax (u θ₁) S) (argmax (u θ₂) S) :=
  strongSetOrder_of_forall_le fun _ ha _ hb => argmax_le_of_singleCrossing hsc θ₁ θ₂ hθ ha hb

/-- **Milgrom–Shannon Theorem 4** (linearly ordered action space): Under the *weak* single-crossing
property, argmax sets are monotone in the strong set order.

This is the set-valued comparative-statics theorem. Unlike
`argmax_strongSetOrder_of_singleCrossing`, which derives the strong set order from the full
dominance conclusion of strict single crossing (every low-type maximizer below every high-type
maximizer), this version covers objectives with flat tops, where argmax sets are non-degenerate
intervals that overlap and dominance fails: The strong set order — swap a low-type maximizer for a
lower one, a high-type maximizer for a higher one — is all that survives, and all that the weak
hypothesis delivers. -/
theorem argmax_strongSetOrder_of_weakSingleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : WeakCardinalSingleCrossing u)
    (θ₁ θ₂ : Θ) (hθ : θ₁ < θ₂) :
    StrongSetOrder (argmax (u θ₁) S) (argmax (u θ₂) S) := by
  intro a ha b hb
  rcases le_total a b with hab | hba
  · -- Ordered as expected: `a ⊓ b = a` and `a ⊔ b = b` are the maximizers we started with.
    rw [inf_eq_left.mpr hab, sup_eq_right.mpr hab]
    exact ⟨ha, hb⟩
  · -- Crossed maximizers `b ≤ a`: swap them across the argmax sets.
    rw [inf_eq_right.mpr hba, sup_eq_left.mpr hba]
    rcases eq_or_lt_of_le hba with rfl | hba_lt
    · exact ⟨ha, hb⟩
    obtain ⟨haS, hamax⟩ := ha
    obtain ⟨hbS, hbmax⟩ := hb
    -- The low type cannot strictly prefer `a` to `b`: strict preference would cross upward and
    -- contradict `b`'s optimality for the high type.
    have h_lo_pref_b : u θ₁ a ≤ u θ₁ b := by
      by_contra hlt
      push Not at hlt
      exact absurd (isMaxOn_iff.mp hbmax a haS)
        (not_le.mpr (hsc.lt_crossing θ₁ θ₂ b a hθ hba_lt hlt))
    -- So `b` matches `a`'s value for the low type and inherits its optimality.
    have hb_argmax₁ : b ∈ argmax (u θ₁) S :=
      ⟨hbS, isMaxOn_iff.mpr fun y hy => (isMaxOn_iff.mp hamax y hy).trans h_lo_pref_b⟩
    -- The low type weakly prefers `a` to `b` (by `a`'s optimality), and weak preference crosses
    -- upward, so the high type does too — `a` inherits `b`'s optimality.
    have h_hi_pref_a : u θ₂ b ≤ u θ₂ a :=
      hsc.le_crossing θ₁ θ₂ b a hθ hba_lt (isMaxOn_iff.mp hamax b hbS)
    have ha_argmax₂ : a ∈ argmax (u θ₂) S :=
      ⟨haS, isMaxOn_iff.mpr fun y hy => (isMaxOn_iff.mp hbmax y hy).trans h_hi_pref_a⟩
    exact ⟨hb_argmax₁, ha_argmax₂⟩

/-! ## sSup / sInf corollaries -/

/-- Shared engine for the `sSup`/`sInf` selection corollaries: Any selector `sel` that lands in
each argmax set inherits monotonicity from Milgrom–Shannon. The two corollaries below instantiate
`sel` with `sSup` (via `IsCompact.sSup_mem`) and `sInf` (via `IsCompact.sInf_mem`). -/
private theorem argmax_selection_monotone_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u) {sel : Set ℝ → ℝ}
    (h_sel : ∀ θ, sel (argmax (u θ) S) ∈ argmax (u θ) S) :
    Monotone (fun θ ↦ sel (argmax (u θ) S)) := by
  intro θ₁ θ₂ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_refl _
  exact argmax_le_of_singleCrossing hsc θ₁ θ₂ hθ_lt (h_sel θ₁) (h_sel θ₂)

/-- Corollary: `sSup` of the argmax set is monotone under SCP. -/
theorem sSup_argmax_monotone_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u)
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sSup (argmax (u θ) S)) :=
  argmax_selection_monotone_of_singleCrossing hsc
    fun θ => (argmax_compact h_compact (h_cont θ)).sSup_mem
      (argmax_nonempty h_compact h_nonempty (h_cont θ))

/-- Corollary: `sInf` of the argmax set is monotone under SCP. -/
theorem sInf_argmax_monotone_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u)
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sInf (argmax (u θ) S)) :=
  argmax_selection_monotone_of_singleCrossing hsc
    fun θ => (argmax_compact h_compact (h_cont θ)).sInf_mem
      (argmax_nonempty h_compact h_nonempty (h_cont θ))

/-! ## sSup / sInf corollaries under weak single crossing

Under the *weak* single-crossing property only the strong set order
(`argmax_strongSetOrder_of_weakSingleCrossing`) survives — pointwise dominance fails on flat-top
objectives whose argmax sets overlap. But the strong set order on a chain already determines both
extreme selections: It forces `a ⊔ b` into the higher argmax set and `a ⊓ b` into the lower one, so
the upper selection `sSup` and the lower selection `sInf` are each monotone. These corollaries
deliver exactly the flat-top comparative statics an applied user wants, with no strict
hypothesis. -/

/-- **Upper selection is monotone under weak single crossing.** On a compact, nonempty feasible set
with continuous objectives, the `sSup` of the argmax set is monotone in the type under the *weak*
single-crossing property. The strong set order forces `sSup A₁ ⊔ sSup A₂` into the higher argmax
set `A₂`, and `sSup A₂` is an upper bound of `A₂`, so `sSup A₁ ≤ sSup A₁ ⊔ sSup A₂ ≤ sSup A₂`. -/
theorem sSup_argmax_monotone_of_weakSingleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : WeakCardinalSingleCrossing u)
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sSup (argmax (u θ) S)) := by
  intro θ₁ θ₂ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_refl _
  -- Both argmax sets are compact and nonempty, so their suprema are attained members.
  have h_ne₁ : (argmax (u θ₁) S).Nonempty := argmax_nonempty h_compact h_nonempty (h_cont θ₁)
  have h_ne₂ : (argmax (u θ₂) S).Nonempty := argmax_nonempty h_compact h_nonempty (h_cont θ₂)
  have h_cpt₂ : IsCompact (argmax (u θ₂) S) := argmax_compact h_compact (h_cont θ₂)
  have h_bdd₂ : BddAbove (argmax (u θ₂) S) := h_cpt₂.bddAbove
  have h_mem₁ : sSup (argmax (u θ₁) S) ∈ argmax (u θ₁) S :=
    (argmax_compact h_compact (h_cont θ₁)).sSup_mem h_ne₁
  have h_mem₂ : sSup (argmax (u θ₂) S) ∈ argmax (u θ₂) S := h_cpt₂.sSup_mem h_ne₂
  -- The strong set order pushes the join of the two suprema into the higher argmax set.
  have h_join_mem : sSup (argmax (u θ₁) S) ⊔ sSup (argmax (u θ₂) S) ∈ argmax (u θ₂) S :=
    (argmax_strongSetOrder_of_weakSingleCrossing hsc θ₁ θ₂ hθ_lt _ h_mem₁ _ h_mem₂).2
  -- `sSup A₂` bounds that join, and `sSup A₁ ≤` the join, so `sSup A₁ ≤ sSup A₂`.
  exact le_sup_left.trans (le_csSup h_bdd₂ h_join_mem)

/-- **Lower selection is monotone under weak single crossing.** On a compact, nonempty feasible set
with continuous objectives, the `sInf` of the argmax set is monotone in the type under the *weak*
single-crossing property. The strong set order forces `sInf A₁ ⊓ sInf A₂` into the lower argmax set
`A₁`, and `sInf A₁` is a lower bound of `A₁`, so `sInf A₁ ≤ sInf A₁ ⊓ sInf A₂ ≤ sInf A₂`. -/
theorem sInf_argmax_monotone_of_weakSingleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : WeakCardinalSingleCrossing u)
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sInf (argmax (u θ) S)) := by
  intro θ₁ θ₂ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_refl _
  -- Both argmax sets are compact and nonempty, so their infima are attained members.
  have h_ne₁ : (argmax (u θ₁) S).Nonempty := argmax_nonempty h_compact h_nonempty (h_cont θ₁)
  have h_ne₂ : (argmax (u θ₂) S).Nonempty := argmax_nonempty h_compact h_nonempty (h_cont θ₂)
  have h_cpt₁ : IsCompact (argmax (u θ₁) S) := argmax_compact h_compact (h_cont θ₁)
  have h_bdd₁ : BddBelow (argmax (u θ₁) S) := h_cpt₁.bddBelow
  have h_mem₁ : sInf (argmax (u θ₁) S) ∈ argmax (u θ₁) S := h_cpt₁.sInf_mem h_ne₁
  have h_mem₂ : sInf (argmax (u θ₂) S) ∈ argmax (u θ₂) S :=
    (argmax_compact h_compact (h_cont θ₂)).sInf_mem h_ne₂
  -- The strong set order pushes the meet of the two infima into the lower argmax set.
  have h_meet_mem : sInf (argmax (u θ₁) S) ⊓ sInf (argmax (u θ₂) S) ∈ argmax (u θ₁) S :=
    (argmax_strongSetOrder_of_weakSingleCrossing hsc θ₁ θ₂ hθ_lt _ h_mem₁ _ h_mem₂).1
  -- `sInf A₁` bounds that meet from below, and the meet `≤ sInf A₂`, so `sInf A₁ ≤ sInf A₂`.
  exact (csInf_le h_bdd₁ h_meet_mem).trans inf_le_right

/-! ## Supermodular (weak Topkis) corollaries

Supermodularity (weak increasing differences) implies the weak single-crossing property
(`Supermodular.toWeakCardinalSingleCrossing`), so a supermodular flat-top objective gets one-line
selection monotonicity for both extreme selections. -/

/-- Set-valued Topkis upper-selection monotonicity for a *supermodular* objective. The flat-top
analog of `sSup_argmax_monotone_of_strictIncreasingDifferences`: A corollary of
`sSup_argmax_monotone_of_weakSingleCrossing` via `Supermodular.toWeakCardinalSingleCrossing`. -/
lemma sSup_argmax_monotone_of_supermodular {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (h_sm : Supermodular u)
    (h_nonempty : S.Nonempty)
    (h_compact : IsCompact S)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sSup (argmax (u θ) S)) :=
  sSup_argmax_monotone_of_weakSingleCrossing h_sm.toWeakCardinalSingleCrossing h_compact
    h_nonempty h_cont

/-- Set-valued Topkis lower-selection monotonicity for a *supermodular* objective. The flat-top
analog of `sInf_argmax_monotone_of_strictIncreasingDifferences`: A corollary of
`sInf_argmax_monotone_of_weakSingleCrossing` via `Supermodular.toWeakCardinalSingleCrossing`. -/
lemma sInf_argmax_monotone_of_supermodular {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (h_sm : Supermodular u)
    (h_nonempty : S.Nonempty)
    (h_compact : IsCompact S)
    (h_cont : ∀ θ, ContinuousOn (u θ) S) :
    Monotone (fun θ ↦ sInf (argmax (u θ) S)) :=
  sInf_argmax_monotone_of_weakSingleCrossing h_sm.toWeakCardinalSingleCrossing h_compact
    h_nonempty h_cont

/-- Corollary: A pointwise maximizing selection `x_star` over a fixed set `S` is monotone under
cardinal single crossing. -/
theorem argmax_monotone_of_singleCrossing {u : Θ → ℝ → ℝ} {S : Set ℝ}
    (hsc : CardinalSingleCrossing u)
    (x_star : Θ → ℝ)
    (h_mem : ∀ θ, x_star θ ∈ S)
    (h_opt : ∀ θ, IsMaxOn (u θ) S (x_star θ)) :
    Monotone x_star := by
  intro θ₁ θ₂ hθ
  rcases eq_or_lt_of_le hθ with rfl | hθ_lt
  · exact le_refl _
  exact argmax_le_of_singleCrossing hsc θ₁ θ₂ hθ_lt ⟨h_mem θ₁, h_opt θ₁⟩ ⟨h_mem θ₂, h_opt θ₂⟩

/-! ## Topkis corollaries

Recovered as thin specializations of Milgrom–Shannon via
`StrictIncreasingDifferences.toCardinalSingleCrossing`. -/

/-- Set-valued Topkis's theorem for upper-selections under the (strictly stronger)
`StrictIncreasingDifferences` hypothesis. A corollary of
`sSup_argmax_monotone_of_singleCrossing`. -/
lemma sSup_argmax_monotone_of_strictIncreasingDifferences {u : Θ → ℝ → ℝ} {X : Set ℝ}
    (h_id : StrictIncreasingDifferences u)
    (h_X_nonempty : X.Nonempty)
    (h_X_compact : IsCompact X)
    (h_u_cont : ∀ θ, ContinuousOn (u θ) X) :
    Monotone (fun θ ↦ sSup (argmax (u θ) X)) :=
  sSup_argmax_monotone_of_singleCrossing h_id.toCardinalSingleCrossing h_X_compact h_X_nonempty
    h_u_cont

/-- Set-valued Topkis's theorem for lower-selections under `StrictIncreasingDifferences`. A
corollary of `sInf_argmax_monotone_of_singleCrossing`. -/
lemma sInf_argmax_monotone_of_strictIncreasingDifferences {u : Θ → ℝ → ℝ} {X : Set ℝ}
    (h_id : StrictIncreasingDifferences u)
    (h_X_nonempty : X.Nonempty)
    (h_X_compact : IsCompact X)
    (h_u_cont : ∀ θ, ContinuousOn (u θ) X) :
    Monotone (fun θ ↦ sInf (argmax (u θ) X)) :=
  sInf_argmax_monotone_of_singleCrossing h_id.toCardinalSingleCrossing h_X_compact h_X_nonempty
    h_u_cont

end Econlib.Optimization
