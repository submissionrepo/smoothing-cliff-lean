/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Monotone Comparative Statics: Higher Types Choose Higher Actions

The Milgrom–Shannon monotone-selection theorem says that when a family of objectives
`u : Θ → X → ℝ` satisfies the single-crossing property in `(x; θ)`, the argmax correspondence is
monotone in `θ`. How monotone depends on how strong the crossing is, and this file works both
regimes on concrete models:

1. **Strict single crossing — full dominance.** The quadratic complementarity payoff
   `u(θ, x) = θ·x − x²/2` on `S = [0, 1]` has strictly increasing differences (cross-partial
   `∂²u/∂θ∂x = 1 > 0`), hence strict single crossing. Every maximizer of a lower type lies weakly
   below every maximizer of a higher type (`maximizers_ordered`), the `sSup`/`sInf` selections are
   monotone (Topkis, `highest_action_monotone` / `lowest_action_monotone`), and the argmax sets are
   ordered in the strong set order (`maximizers_strongSetOrder`). Because the objective is strictly
   concave in `x`, each argmax is the singleton `{θ}` for `θ ∈ [0, 1]` (`argmax_eq_singleton`) —
   dominance and the strong set order coincide.
2. **Weak single crossing with a flat top — the strong set order earns its keep.** The
   capacity-constrained payoff `v(θ, x) = min(x, θ)` on `T = [0, 2]` — output is throttled by
   capacity `θ` — is supermodular (`v_supermodular`), but only *weakly* single crossing: It
   fails the strict property (`v_not_strict_singleCrossing`). Its argmax is the whole
   flat top `[θ, 2]` (`flat_argmax_eq`) — for every `θ < 2` a fat interval
   (`flat_argmax_nontrivial`: it holds two distinct optima), not a point, that moves with `θ` and
   overlaps its neighbors. Dominance fails (`flat_dominance_fails`: The low type's maximizer `2`
   does not sit below the high type's maximizer `1`), yet the argmax correspondence is still
   monotone in the strong set order (`flat_argmax_strongSetOrder`, via Milgrom–Shannon Theorem 4,
   `argmax_strongSetOrder_of_weakSingleCrossing`). This is exactly the content the strong set order
   was invented for: Swap any low-type maximizer for a lower one, any high-type maximizer for a
   higher one.

## The mathematics

Model 1's cross-partial is `∂²u/∂θ∂x = 1 > 0`, so `u` has strictly increasing differences
(`strict_increasing_differences_of_cross_partial_pos`), hence cardinal single crossing. The action
set `[0, 1]` is compact and nonempty and each `u(θ, ·)` is continuous, so the argmax is nonempty
and compact and the `sSup`/`sInf` selections are well defined and monotone.

Model 2's `min(x, θ)` is the canonical supermodular function: Its incremental return to raising `x`
jumps from `0` to positive as capacity `θ` rises past `x`. Supermodularity gives the weak
Milgrom–Shannon single-crossing property (`Supermodular.toWeakCardinalSingleCrossing`), which is
all that Theorem 4 needs — and all that is true: On the flat top the strict property's `≥ 0 → > 0`
clause fails, as `v_not_strict_singleCrossing` certifies.

## Main definitions and theorems

* `u`, `S` — the strict model: Quadratic complementarity payoff on `[0, 1]`.
* `incr_diff` / `single_crossing` — strictly increasing differences, hence strict single crossing.
* `highest_action_monotone` / `lowest_action_monotone` — Topkis: The top/bottom optimal action is
  nondecreasing in `θ`.
* `maximizers_ordered` — full dominance: Any low-type maximizer `≤` any high-type maximizer.
* `maximizers_strongSetOrder` — the argmax correspondence is monotone in the strong set order.
* `argmax_eq_singleton` — for `θ ∈ [0, 1]` the argmax is the single point `{θ}` (strict concavity).
* `v`, `T` — the flat-top model: Capacity-constrained payoff `min(x, θ)` on `[0, 2]`.
* `v_supermodular` / `v_single_crossing` — supermodularity, hence *weak* single crossing.
* `v_not_strict_singleCrossing` — the strict single-crossing property fails.
* `flat_argmax_eq` — the argmax is the interval `[θ, 2]`.
* `flat_argmax_nontrivial` — for `θ < 2` that interval is fat (two distinct optima), not a
  point; it collapses to `{2}` only at `θ = 2`.
* `flat_dominance_fails` — full dominance is false for the flat-top model.
* `flat_argmax_strongSetOrder` — yet the argmax correspondence is monotone in the strong set order
  (Milgrom–Shannon Theorem 4).
* `flat_highest_action_monotone` / `flat_lowest_action_monotone` — and the upper/lower selections
  are each monotone, via the *weak* (supermodular) Topkis selection corollaries — the strict ones do
  not apply, yet the strong set order alone delivers selection monotonicity.
* `flat_upper_selection_eq` / `flat_lower_selection_eq` — concretely, `sSup [θ, 2] = 2` (constant)
  and `sInf [θ, 2] = θ` (identity) on the capacity range.
-/

noncomputable section

namespace EconlibExamples.Preferences.MonotoneComparativeStatics

open Econlib.Preferences Econlib.Optimization

/-! ## Model 1: Strict complementarity, singleton argmax, full dominance -/

/-- The quadratic complementarity payoff `u(θ, x) = θ·x − x²/2`. -/
def u (θ x : ℝ) : ℝ := θ * x - x ^ 2 / 2

/-- The compact action set `[0, 1]`. -/
def S : Set ℝ := Set.Icc 0 1

theorem S_nonempty : S.Nonempty := Set.nonempty_Icc.mpr (by norm_num)

theorem S_compact : IsCompact S := isCompact_Icc

/-- Each section `u(θ, ·)` is continuous. -/
theorem u_continuous (θ : ℝ) : Continuous (u θ) := by unfold u; fun_prop

/-- `u` has strictly increasing differences, established from the strictly positive cross-partial
`∂²u/∂θ∂x = 1`: The `θ`-marginal is `∂u/∂θ = x`, whose `x`-derivative is the constant `1`. -/
theorem incr_diff : StrictIncreasingDifferences u :=
  strict_increasing_differences_of_cross_partial_pos u
    -- ∂u/∂θ = x
    (fun _ x => x)
    (fun θ x => by
      have h : HasDerivAt (fun θ' => θ' * x - x ^ 2 / 2) (1 * x) θ :=
        ((hasDerivAt_id θ).mul_const x).sub_const (x ^ 2 / 2)
      simpa [u] using h)
    -- ∂²u/∂θ∂x = 1
    (fun _ _ => 1)
    (fun _ x => by simpa using hasDerivAt_id x)
    (fun _ _ => one_pos)

/-- Strictly increasing differences imply cardinal single crossing (Spence–Mirrlees). -/
theorem single_crossing : CardinalSingleCrossing u := incr_diff.toCardinalSingleCrossing

/-- **Topkis (upper selection).** The highest optimal action is nondecreasing in the type. -/
theorem highest_action_monotone :
    Monotone (fun θ => sSup (argmax (u θ) S)) :=
  sSup_argmax_monotone_of_strictIncreasingDifferences incr_diff S_nonempty S_compact
    (fun θ => (u_continuous θ).continuousOn)

/-- **Topkis (lower selection).** The lowest optimal action is also nondecreasing in the type. -/
theorem lowest_action_monotone :
    Monotone (fun θ => sInf (argmax (u θ) S)) :=
  sInf_argmax_monotone_of_strictIncreasingDifferences incr_diff S_nonempty S_compact
    (fun θ => (u_continuous θ).continuousOn)

/-- **Milgrom–Shannon (pairwise dominance).** For `θ₁ < θ₂`, any action optimal for the lower type
lies weakly below any action optimal for the higher type. Strict single crossing delivers this full
dominance — strictly more than the strong set order. -/
theorem maximizers_ordered {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ argmax (u θ₁) S) (hx₂ : x₂ ∈ argmax (u θ₂) S) :
    x₁ ≤ x₂ :=
  argmax_le_of_singleCrossing single_crossing θ₁ θ₂ hθ hx₁ hx₂

/-- **Milgrom–Shannon (strong set order).** The argmax correspondence is monotone in the strong set
order. In this strictly concave model each argmax is a singleton (`argmax_eq_singleton`), so this
adds nothing beyond `maximizers_ordered` — see the flat-top model below for the case where it
does. -/
theorem maximizers_strongSetOrder {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    StrongSetOrder (argmax (u θ₁) S) (argmax (u θ₂) S) :=
  argmax_strongSetOrder_of_singleCrossing single_crossing θ₁ θ₂ hθ

/-- **The argmax is a singleton.** For every interior type `θ ∈ S = [0, 1]` the constrained optimum
is the single point `θ`: the unconstrained optimum `x = θ` of `θ·x − x²/2` already lies in `[0, 1]`,
and strict concavity makes it the unique maximizer. Concretely
`u(θ, θ) − u(θ, x) = (θ − x)²/2 ≥ 0` with equality only at `x = θ`. This is the precise sense in
which dominance and the strong set order coincide here: each argmax set is a point. -/
theorem argmax_eq_singleton {θ : ℝ} (hθ : θ ∈ S) :
    argmax (u θ) S = {θ} := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  ext x
  simp only [argmax, Set.mem_setOf_eq, isMaxOn_iff, S, Set.mem_Icc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hmax⟩
    -- Optimality at the feasible point `θ` gives `u θ θ ≤ u θ x`, i.e. `(θ − x)²/2 ≤ 0`.
    have htest : u θ θ ≤ u θ x := hmax θ ⟨hθ0, hθ1⟩
    simp only [u] at htest
    nlinarith [sq_nonneg (x - θ)]
  · rintro rfl
    -- `x` is feasible and beats every action: `u x x − u x y = (x − y)²/2 ≥ 0`.
    refine ⟨⟨hθ0, hθ1⟩, fun y _ => ?_⟩
    simp only [u]
    nlinarith [sq_nonneg (x - y)]

/-! ## Model 2: A flat top — where the strong set order is the whole story

Output `min(x, θ)` is throttled by capacity `θ`: Effort beyond capacity is free but useless, so
every `x ∈ [θ, 2]` is optimal and the argmax is a fat interval. Consecutive types' argmax sets
overlap, dominance fails, and only the strong set order survives. -/

/-- The capacity-constrained payoff `v(θ, x) = min(x, θ)`: Effort `x` produces output up to
capacity `θ`, with no cost of effort. -/
def v (θ x : ℝ) : ℝ := min x θ

/-- The compact action set `[0, 2]`. -/
def T : Set ℝ := Set.Icc 0 2

/-- `min(x, θ)` is the canonical supermodular function: Raising capacity raises the incremental
return to effort. -/
theorem v_supermodular : Supermodular v := by
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [v, min_def]
  split_ifs <;> linarith

/-- Supermodularity hands us the *weak* Milgrom–Shannon single-crossing property. -/
theorem v_single_crossing : WeakCardinalSingleCrossing v :=
  v_supermodular.toWeakCardinalSingleCrossing

/-- The flat-top model fails *strict* single crossing: With `x₁ = 1 < x₂ = 2` both above
the capacities `θ₁ = 0 < θ₂ = 1/2`, the low type is exactly indifferent (`0 − 0 ≥ 0`) but the high
type is indifferent too (`1/2 − 1/2 ≯ 0`). The strict-crossing API of Model 1 cannot see this
model; the weak Theorem 4 below is not a luxury. -/
theorem v_not_strict_singleCrossing : ¬ CardinalSingleCrossing v := by
  intro h
  have hcross := h.weak_crossing 0 (1 / 2) 1 2 (by norm_num) (by norm_num) (by norm_num [v])
  norm_num [v] at hcross

/-- **The argmax is the flat top `[θ, 2]`.** Every action at or above capacity attains the maximal
output `θ`; every action below it falls short. For `θ < 2` this interval is fat — see
`flat_argmax_nontrivial` — collapsing to a point only at the very top `θ = 2`. -/
theorem flat_argmax_eq {θ : ℝ} (hθ : θ ∈ T) :
    argmax (v θ) T = Set.Icc θ 2 := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  ext x
  simp only [argmax, Set.mem_setOf_eq, isMaxOn_iff, T, v, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hx2⟩, hmax⟩
    refine ⟨?_, hx2⟩
    -- Test optimality against the action `θ` itself: `θ = min θ θ ≤ min x θ` forces `θ ≤ x`.
    have htest := hmax θ ⟨hθ0, hθ2⟩
    simp only [min_self] at htest
    exact (le_min_iff.mp htest).1
  · rintro ⟨hθx, hx2⟩
    refine ⟨⟨hθ0.trans hθx, hx2⟩, fun y hy => ?_⟩
    -- At or above capacity the payoff is the cap `θ`, which no action exceeds.
    calc min y θ ≤ θ := min_le_right y θ
      _ = min x θ := (min_eq_right hθx).symm

/-- **The flat top is fat below capacity `2`.** For any `θ < 2` the argmax `[θ, 2]`
contains two distinct optimal actions (`θ` and `2`), so it is not a singleton — this is the
non-degeneracy that distinguishes the flat-top model from the strictly concave Model 1, where every
argmax is a point (`argmax_eq_singleton`). Only at the very top `θ = 2` does `[θ, 2]` collapse to
the point `{2}`. -/
theorem flat_argmax_nontrivial {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2) :
    ∃ x ∈ argmax (v θ) T, ∃ y ∈ argmax (v θ) T, x ≠ y := by
  have hmem : θ ∈ T := Set.mem_Icc.mpr ⟨hθ0, hθ2.le⟩
  refine ⟨θ, ?_, 2, ?_, ne_of_lt hθ2⟩
  · rw [flat_argmax_eq hmem]; exact Set.mem_Icc.mpr ⟨le_refl _, hθ2.le⟩
  · rw [flat_argmax_eq hmem]; exact Set.mem_Icc.mpr ⟨hθ2.le, le_refl _⟩

/-- **Dominance fails on the flat top.** The low type `θ = 1/2` is happy at the action `2`, the
high type `θ = 1` is happy at the action `1`, and `2 ≤ 1` is false: Maximizers of consecutive types
interleave, so the full-dominance conclusion of strict single crossing (`maximizers_ordered`) is
simply not available here. -/
theorem flat_dominance_fails :
    ¬ ∀ x₁ ∈ argmax (v (1 / 2)) T, ∀ x₂ ∈ argmax (v 1) T, x₁ ≤ x₂ := by
  intro h
  have h_two : (2 : ℝ) ∈ argmax (v (1 / 2)) T := by
    rw [flat_argmax_eq (Set.mem_Icc.mpr (by norm_num))]
    exact Set.mem_Icc.mpr (by norm_num)
  have h_one : (1 : ℝ) ∈ argmax (v 1) T := by
    rw [flat_argmax_eq (Set.mem_Icc.mpr (by norm_num))]
    exact Set.mem_Icc.mpr (by norm_num)
  linarith [h 2 h_two 1 h_one]

/-- **Milgrom–Shannon Theorem 4 on the flat-top model.** Although dominance fails
(`flat_dominance_fails`), the argmax correspondence `θ ↦ [θ, 2]` is monotone in the strong set
order: The min of a low-type and a high-type maximizer is optimal for the low type, their max for
the high type. Weak single crossing is exactly enough. -/
theorem flat_argmax_strongSetOrder {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    StrongSetOrder (argmax (v θ₁) T) (argmax (v θ₂) T) :=
  argmax_strongSetOrder_of_weakSingleCrossing v_single_crossing θ₁ θ₂ hθ

/-! ### Flat-top selection monotonicity — the strong set order delivers both extreme selections

Dominance fails on the flat top, so the *strict* Topkis corollaries of Model 1
(`highest_action_monotone` / `lowest_action_monotone`) do not apply here. But the strong set order
on the chain already determines both extreme selections, so the *weak* corollaries
(`sSup_argmax_monotone_of_weakSingleCrossing` / `sInf_…`, and their supermodular specializations)
still make the upper and lower selections monotone. For the argmax `[θ, 2]` this is concrete: the
upper selection `sSup [θ, 2] = 2` is constant and the lower selection `sInf [θ, 2] = θ` is the
identity — both monotone. -/

theorem T_nonempty : T.Nonempty := Set.nonempty_Icc.mpr (by norm_num)

theorem T_compact : IsCompact T := isCompact_Icc

/-- Each capacity section `v(θ, ·) = min(·, θ)` is continuous. -/
theorem v_continuous (θ : ℝ) : Continuous (v θ) := by unfold v; fun_prop

/-- **Weak Topkis (upper selection), flat top.** The highest optimal action `sSup (argmax (v θ) T)`
is nondecreasing in capacity `θ` — even though dominance fails. Supermodularity routes through the
*weak* single-crossing selection corollary, the strict Topkis corollary being unavailable here. -/
theorem flat_highest_action_monotone :
    Monotone (fun θ => sSup (argmax (v θ) T)) :=
  sSup_argmax_monotone_of_supermodular v_supermodular T_nonempty T_compact
    (fun θ => (v_continuous θ).continuousOn)

/-- **Weak Topkis (lower selection), flat top.** The lowest optimal action `sInf (argmax (v θ) T)`
is likewise nondecreasing in capacity `θ`. -/
theorem flat_lowest_action_monotone :
    Monotone (fun θ => sInf (argmax (v θ) T)) :=
  sInf_argmax_monotone_of_supermodular v_supermodular T_nonempty T_compact
    (fun θ => (v_continuous θ).continuousOn)

/-- The lower selection is concretely the identity on the capacity range `[0, 2]`:
`sInf (argmax (v θ) T) = sInf [θ, 2] = θ`. Its monotonicity is `flat_lowest_action_monotone`
specialized. -/
theorem flat_lower_selection_eq {θ : ℝ} (hθ : θ ∈ T) :
    sInf (argmax (v θ) T) = θ := by
  rw [flat_argmax_eq hθ, csInf_Icc (Set.mem_Icc.mp hθ).2]

/-- The upper selection is concretely the constant `2` on the capacity range `[0, 2]`:
`sSup (argmax (v θ) T) = sSup [θ, 2] = 2`. -/
theorem flat_upper_selection_eq {θ : ℝ} (hθ : θ ∈ T) :
    sSup (argmax (v θ) T) = 2 := by
  rw [flat_argmax_eq hθ, csSup_Icc (Set.mem_Icc.mp hθ).2]

end EconlibExamples.Preferences.MonotoneComparativeStatics
