/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Optimization
import Mathlib

/-!
# Comparative Statics Non-Vacuity Checks

Compile-time semantic witnesses for the monotone comparative statics stack in
`Econlib.Optimization.ComparativeStatics`. These tests catch canonical failure modes:

* **Argmax moves DOWN**: If the increasing-differences direction is reversed, the argmax moves
  antitone (lowest action chosen as the parameter rises), not monotone.
* **sSup/sInf selection flip**: `sSup` and `sInf` could be swapped — the largest optimizer might be
  taken as sInf, or the smallest as sSup — reversing the inequality direction.
* **Value-function direction reversal**: If the objective is decreasing in `θ`, so is the value
  function; the witness here confirms the increasing direction.
* **Binding threshold in the wrong direction**: Under domination the binding point could be
  confused with the dominated one.

## The objective

All argmax witnesses use `u : ℝ → ℝ → ℝ := fun t x => t * x` on `S = Set.Icc 0 1`.

Hand-computed anchors (parameter `t`, action space `[0,1]`):

* At `t = 0`:  `u 0 x = 0` for all `x`, so every `x ∈ [0,1]` is optimal.

  * `argmax (u 0) S = S = Set.Icc 0 1`
  * `sInf (argmax (u 0) S) = 0`,  `sSup (argmax (u 0) S) = 1`
* At `t = 1/2`:  `u (1/2) x = x/2`, strictly increasing, so `x = 1` uniquely maximizes.

  * `argmax (u (1/2)) S = {1}`
  * `sInf (argmax (u (1/2)) S) = 1`,  `sSup (argmax (u (1/2)) S) = 1`

Both selections rise as `t` goes from `0` to `1/2`: `sInf` from `0` to `1` (strict move up), `sSup`
from `1` to `1` (stays at top). To make the *upper* selection move strictly we also use the negative
type `t = -1/2`, where `f (-1/2) x = -x/2` is decreasing so `argmax = {0}` and `sSup = 0`: across
`t = -1/2 ↦ 0` the upper selection rises strictly `0 → 1` (`sSup_argmax_rises_strict`). A reversed
objective `u t x = -t * x` would move both selections *down*, catching an antitone reversal.

## Coverage

1. `sSup_argmax_monotone_of_supermodular` — upper selection monotone under supermodularity
2. `sInf_argmax_monotone_of_supermodular` — lower selection monotone under supermodularity
3. `sSup_argmax_monotone_of_strictIncreasingDifferences` — Topkis corollary (strict case)
4. `sInf_argmax_monotone_of_strictIncreasingDifferences` — Topkis corollary (strict case)
5. `argmaxRel_le_of_singleCrossing` — ordinal single-crossing cross-maximizer ordering (discharged
   on concrete optimizers `0 ∈ argmaxRel (f 0) S`, `1 ∈ argmaxRel (f (1/2)) S`)
6. `argmaxRel_strongSetOrder_of_singleCrossing` — strong set order under ordinal SCP (with the
   `argmaxRel` set shapes computed: `[0,1]` and `{1}`, so non-vacuous)
7. `argmaxRel_monotone_of_singleCrossing` — monotone selection under ordinal SCP, on the **moving**
   selection `xSel` (`0` at `t = 0`, `1` at `t > 0`), not a constant policy
8. `argmax_monotone_of_singleCrossing` — monotone cardinal selection, likewise on `xSel`
9. `valueFunction_monotone_of_monotone` — value rises in `t`; anchor `v(t) = t` at `t ∈ [0,1]`
10. `valueFunction_supermodular` — value supermodular in two parameters; the value is the
    *truncated* `max (θ + ψ) 0` (`g_valueFunction_pos = 1` at `θ+ψ = 1`,
    `g_valueFunction_neg = 0` at `θ+ψ = -1`)
11. `binding_threshold_lt_of_domination` — binding threshold of dominated function is strictly
    higher
12. `strictAntiOn_apply_lt_of_binding_lt` — strictly antitone cost rises at lower threshold
-/

noncomputable section

namespace EconlibTest.Optimization.ComparativeStatics

open Econlib.Optimization Econlib.Preferences Set

/-! ## Objective and feasible set -/

/-- The bilinear (product) objective: `f t x = t * x`. Supermodular and has strictly increasing
differences on `ℝ`; the unique maximizer over `[0,1]` at any `t > 0` is `x = 1`. -/
private abbrev f : ℝ → ℝ → ℝ := fun t x => t * x

/-- The action space: The unit interval `[0, 1]`. -/
private abbrev S : Set ℝ := Set.Icc 0 1

/-! ## Basic feasibility lemmas -/

private lemma S_nonempty : S.Nonempty := ⟨0, le_refl _, zero_le_one⟩

private lemma S_compact : IsCompact S := isCompact_Icc

private lemma f_cont (t : ℝ) : ContinuousOn (f t) S :=
  (continuous_const.mul continuous_id).continuousOn

/-! ## Supermodularity of `f` -/

/-- `f t x = t * x` is supermodular: For `t₁ ≤ t₂` and `x₁ ≤ x₂`,
`f t₂ x₂ + f t₁ x₁ ≥ f t₂ x₁ + f t₁ x₂`, i.e. `t₂ x₂ + t₁ x₁ ≥ t₂ x₁ + t₁ x₂`. This is equivalent
to `(t₂ - t₁)(x₂ - x₁) ≥ 0`. -/
private lemma f_supermodular : Supermodular f := by
  intro t₁ t₂ x₁ x₂ ht hx
  simp only [f]
  nlinarith

/-- `f t x = t * x` has strictly increasing differences: For `t₁ < t₂` and `x₁ < x₂`,
`f t₂ x₂ - f t₂ x₁ > f t₁ x₂ - f t₁ x₁`, i.e. `(t₂ - t₁)(x₂ - x₁) > 0`. -/
private lemma f_strictIncDiff : StrictIncreasingDifferences f where
  strict_incr_diff := by
    intro t₁ t₂ x₁ x₂ ht hx
    simp only [f]
    nlinarith

/-- `f t x = t * x` satisfies cardinal single crossing: At `t₁ < t₂`, `x₁ < x₂`, if the lower type
weakly prefers `x₂` (`f t₁ x₂ - f t₁ x₁ ≥ 0`, i.e. `t₁(x₂ - x₁) ≥ 0`), then the higher type
strictly prefers it (`f t₂ x₂ - f t₂ x₁ > 0`). -/
private lemma f_cardinalSCP : CardinalSingleCrossing f :=
  f_strictIncDiff.toCardinalSingleCrossing

/-- The ordinal single-crossing induced by `f` through `preferenceOfRealUtility`. -/
private lemma f_singleCrossingRel :
    SingleCrossingRel (fun t => preferenceOfRealUtility (f t)) :=
  f_cardinalSCP.toSingleCrossingRel

/-- `f` restricted to nonneg parameter type satisfies cardinal single crossing. -/
private lemma f_nn_cardinalSCP :
    CardinalSingleCrossing (fun (t : {t : ℝ // 0 ≤ t}) (x : ℝ) => f t.val x) :=
  ⟨fun t₁ t₂ x₁ x₂ ht hx hge => by
    simp only [f] at *
    have ht2pos : 0 < t₂.val := lt_of_le_of_lt t₁.2 ht
    nlinarith⟩

/-- Ordinal single crossing for nonneg parameters. -/
private lemma f_nn_singleCrossingRel :
    SingleCrossingRel (fun t : {t : ℝ // 0 ≤ t} => preferenceOfRealUtility (f t.val)) :=
  f_nn_cardinalSCP.toSingleCrossingRel

/-! ## Argmax set at the key parameter values -/

/-- At `t = 0`, every action in `[0,1]` achieves the same objective value `0`, so the entire
interval is the argmax set. -/
private lemma argmax_f_zero : argmax (f 0) S = S := by
  ext x
  simp only [argmax, f, zero_mul, Set.mem_setOf_eq, Set.mem_Icc, isMaxOn_iff]
  constructor
  · exact fun ⟨hx, _⟩ => hx
  · exact fun hx => ⟨hx, fun _ _ => le_refl _⟩

/-- At `t = 1/2`, `f (1/2) x = x/2` is strictly increasing, so the argmax is `{1}`. -/
private lemma argmax_f_half : argmax (f (1 / 2)) S = {1} := by
  ext x
  simp only [argmax, Set.mem_setOf_eq, Set.mem_Icc, isMaxOn_iff, Set.mem_singleton_iff, f]
  constructor
  · intro ⟨⟨hx0, hx1⟩, hmax⟩
    -- hmax : ∀ y ∈ S, f (1/2) y ≤ f (1/2) x, i.e. (1/2)*y ≤ (1/2)*x for all y ∈ [0,1]
    have h1 : 1 / 2 * 1 ≤ 1 / 2 * x := hmax 1 ⟨zero_le_one, le_refl 1⟩
    linarith
  · intro heq
    subst heq
    exact ⟨⟨zero_le_one, le_refl 1⟩, fun y hy => by
      have hyS := Set.mem_Icc.mp hy
      linarith⟩

/-- At `t = -1/2`, `f (-1/2) x = -x/2` is strictly *decreasing*, so the argmax is `{0}` (the lowest
action). This is the negative-parameter anchor that makes the *upper* selection move strictly. -/
private lemma argmax_f_neg_half : argmax (f (-1 / 2)) S = {0} := by
  ext x
  simp only [argmax, Set.mem_setOf_eq, Set.mem_Icc, isMaxOn_iff, Set.mem_singleton_iff, f]
  constructor
  · intro ⟨⟨hx0, hx1⟩, hmax⟩
    -- `hmax 0 : -1/2 * 0 ≤ -1/2 * x`, i.e. `0 ≤ -x/2`, so `x ≤ 0`;
    -- with `x ≥ 0` this forces `x = 0`.
    have h0 : -1 / 2 * 0 ≤ -1 / 2 * x := hmax 0 ⟨le_refl 0, zero_le_one⟩
    linarith
  · intro heq
    subst heq
    exact ⟨⟨le_refl 0, zero_le_one⟩, fun y hy => by
      have hyS := Set.mem_Icc.mp hy
      linarith [hyS.1]⟩

/-! ## Anchor computations: SInf and sSup at t = 0 and t = 1/2 -/

/-- At `t = 0` the infimum of the argmax (which is all of `[0,1]`) equals `0`. This is the starting
point of the semantic check: `sInf` rises from `0` (at `t = 0`) to `1` (at `t ≥` any positive
value). -/
theorem sInf_argmax_f_zero : sInf (argmax (f 0) S) = 0 := by
  rw [argmax_f_zero]
  exact csInf_Icc zero_le_one

/-- At `t = 1/2` the infimum of the argmax (`{1}`) equals `1`. Together with
`sInf_argmax_f_zero = 0`, this confirms `sInf` rises by `1` as `t` increases from `0` to `1/2`. A
direction-reversed theorem would give `1 ≤ 0`, which is false and would fail. -/
theorem sInf_argmax_f_half : sInf (argmax (f (1 / 2)) S) = 1 := by
  rw [argmax_f_half]
  simp

/-- At `t = 0` the supremum of the argmax (which is all of `[0,1]`) equals `1`. The `sSup` starts
at the top and stays there; a selection-flip bug would confuse it with `sInf`. -/
theorem sSup_argmax_f_zero : sSup (argmax (f 0) S) = 1 := by
  rw [argmax_f_zero]
  exact csSup_Icc zero_le_one

/-- At `t = 1/2` the supremum of the argmax (`{1}`) equals `1`. -/
theorem sSup_argmax_f_half : sSup (argmax (f (1 / 2)) S) = 1 := by
  rw [argmax_f_half]
  simp

/-- At `t = -1/2` the supremum of the argmax (`{0}`) equals `0`. Together with
`sSup_argmax_f_zero = 1` this gives a *strict* upward move of the **upper** selection across the
pair
`t = -1/2 ↦ t = 0`, where the symmetric pair `t = 0 ↦ t = 1/2` (both `sSup = 1`) cannot. -/
theorem sSup_argmax_f_neg_half : sSup (argmax (f (-1 / 2)) S) = 0 := by
  rw [argmax_f_neg_half]
  simp

/-! ## Section 1: Argmax monotone in the parameter -/

section ArgmaxMonotone

/-- **`sSup` argmax monotone (supermodular).** The largest optimizer of `f t x = t * x` over
`[0,1]` weakly rises as `t` increases. Anchored: `sSup` is `1` at both `t = 0` and `t = 1/2` (it
starts at the top and stays there). A reversed objective `-t·x` would give an antitone selection,
catching the direction-reversal failure mode. -/
theorem sSup_argmax_monotone :
    Monotone (fun t => sSup (argmax (f t) S)) :=
  sSup_argmax_monotone_of_supermodular f_supermodular S_nonempty S_compact f_cont

/-- **`sInf` argmax monotone (supermodular).** The smallest optimizer of `f t x = t * x` over
`[0,1]` weakly rises as `t` increases. The key semantic content: At `t = 0` the infimum is `0`, at
any `t > 0` the unique maximizer is `1` (so `sInf = 1`). Monotonicity requires `0 ≤ 1`. A wrong
direction gives `1 ≤ 0`, which is false and would fail. -/
theorem sInf_argmax_monotone :
    Monotone (fun t => sInf (argmax (f t) S)) :=
  sInf_argmax_monotone_of_supermodular f_supermodular S_nonempty S_compact f_cont

/-- **Semantic direction check for `sInf`.** The lower selection rises as the parameter rises from
`0` to `1/2`. The inequality `sInf(argmax at 0) ≤ sInf(argmax at 1/2)` is produced by *applying* the
library monotonicity `sInf_argmax_monotone` to `0 ≤ 1/2`; it is load-bearing in the proof (the
statement is about the actual `sInf`s, not a pre-evaluated `0 ≤ 1`). The anchor equalities
`sInf_argmax_f_zero`/`_half` independently certify the endpoints are `0` and `1`. -/
theorem sInf_argmax_rises : sInf (argmax (f 0) S) ≤ sInf (argmax (f (1 / 2)) S) :=
  sInf_argmax_monotone (show (0 : ℝ) ≤ 1 / 2 by norm_num)

/-- **Strict upper-selection move.** Across `t = -1/2 ↦ t = 0` the *upper* selection rises strictly,
from `sSup = 0` to `sSup = 1`. The weak inequality is produced by applying the library monotonicity
`sSup_argmax_monotone` to `-1/2 ≤ 0`; combined with the anchor equalities it becomes the *strict*
move `sSup(argmax at -1/2) < sSup(argmax at 0)` — unlike the symmetric `t = 0 ↦ t = 1/2` pair (both
sups `1`), this pair separates monotone from antitone behavior. A reversed (antitone) selection
would
give `1 ≤ 0`, which is false. -/
theorem sSup_argmax_rises_strict :
    sSup (argmax (f (-1 / 2)) S) < sSup (argmax (f 0) S) := by
  have hmono := sSup_argmax_monotone (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  simp only at hmono
  rw [sSup_argmax_f_neg_half, sSup_argmax_f_zero]
  rw [sSup_argmax_f_neg_half, sSup_argmax_f_zero] at hmono
  exact lt_of_le_of_ne hmono (by norm_num)

/-- **`sSup` argmax monotone (strict increasing differences).** Topkis corollary: The largest
optimizer rises under the strictly stronger hypothesis. Same objective and set. -/
theorem sSup_argmax_monotone_strictID :
    Monotone (fun t => sSup (argmax (f t) S)) :=
  sSup_argmax_monotone_of_strictIncreasingDifferences f_strictIncDiff S_nonempty S_compact f_cont

/-- **`sInf` argmax monotone (strict increasing differences).** Topkis corollary for the lower
selection. -/
theorem sInf_argmax_monotone_strictID :
    Monotone (fun t => sInf (argmax (f t) S)) :=
  sInf_argmax_monotone_of_strictIncreasingDifferences f_strictIncDiff S_nonempty S_compact f_cont

end ArgmaxMonotone

/-! ## Section 2: Strong set order / ordinal single-crossing selection -/

section SingleCrossingSelection

/-- **Cross-maximizer ordering (cardinal SCP).** At parameter `t₁ = 0` and `t₂ = 1/2`, every
optimizer at `t₁` is ≤ every optimizer at `t₂`. Concretely: Every `x ∈ [0,1]` (argmax at `0`) is ≤
`1` (the argmax at `1/2`). A direction-reversed single-crossing predicate would try to prove
maximizers at the *lower* type are weakly *above* those at the higher type, which fails since
`[0,1]` contains points below `1`. -/
theorem argmax_le_at_concrete_params {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ argmax (f 0) S) (hx₂ : x₂ ∈ argmax (f (1 / 2)) S) :
    x₁ ≤ x₂ :=
  argmax_le_of_singleCrossing f_cardinalSCP 0 (1 / 2) (by norm_num) hx₁ hx₂

/-- **Cross-maximizer ordering, discharged on concrete optimizers.** Not the conditional form above:
here we *exhibit* the actual low/high maximizers `x₁ = 0 ∈ argmax (f 0) S`
(since `argmax (f 0) S = S`
contains `0`) and `x₂ = 1 ∈ argmax (f (1/2)) S = {1}`, and feed them to the single-crossing ordering
to conclude `0 ≤ 1`. So the guard is non-vacuous: it produces a genuine pair of optimizers, not just
a conditional on assumed memberships. -/
theorem argmax_le_at_concrete_optimizers : (0 : ℝ) ≤ 1 :=
  argmax_le_of_singleCrossing f_cardinalSCP 0 (1 / 2) (by norm_num)
    (by rw [argmax_f_zero]; exact ⟨le_refl 0, zero_le_one⟩)
    (by rw [argmax_f_half]; exact rfl)

/-- **Strong set order (cardinal SCP).** The argmax at `t = 0` and `t = 1/2` are ordered in the
strong set order: For any `a` in the lower argmax and `b` in the higher argmax, `a ⊓ b` lands in
the lower set and `a ⊔ b` in the higher set. -/
theorem argmax_strongSetOrder_at_concrete :
    StrongSetOrder (argmax (f 0) S) (argmax (f (1 / 2)) S) :=
  argmax_strongSetOrder_of_singleCrossing f_cardinalSCP 0 (1 / 2) (by norm_num)

/-- **The ordinal `argmaxRel` of `f t` coincides with the cardinal `argmax`** (the objective `f t`
represents `preferenceOfRealUtility (f t)`). This bridge lets us read the ordinal argmax sets off
the
hand-computed cardinal ones: `argmaxRel (·) S = argmax (f t) S`. -/
private lemma argmaxRel_f_eq (t : ℝ) :
    argmaxRel (preferenceOfRealUtility (f t)) S = argmax (f t) S :=
  (argmax_eq_argmaxRel_of_represents (preferenceOfUtilityIn_represents (f t)) S).symm

/-- The ordinal argmax at `t = 0` is the **whole interval** `S = [0,1]` (every action is
indifferent), and at `t = 1/2` it is the **singleton** `{1}`. Computed via the
represents-bridge from
the cardinal anchors, so the relation-level sets have the intended nonempty shapes (a strong-set or
cross-maximizer guard would be vacuous if either were empty). -/
theorem argmaxRel_shapes :
    argmaxRel (preferenceOfRealUtility (f 0)) S = S ∧
      argmaxRel (preferenceOfRealUtility (f (1 / 2))) S = {1} := by
  rw [argmaxRel_f_eq, argmaxRel_f_eq, argmax_f_zero, argmax_f_half]
  exact ⟨rfl, rfl⟩

/-- **Ordinal cross-maximizer ordering.** The `SingleCrossingRel` (relation-level) version: At
`θ₁ = 0 < θ₂ = 1/2`, every ordinal maximizer at `θ₁` is ≤ every ordinal maximizer at `θ₂`. -/
theorem argmaxRel_le_at_concrete_params {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ argmaxRel (preferenceOfRealUtility (f 0)) S)
    (hx₂ : x₂ ∈ argmaxRel (preferenceOfRealUtility (f (1 / 2))) S) :
    x₁ ≤ x₂ :=
  argmaxRel_le_of_singleCrossing f_singleCrossingRel 0 (1 / 2) (by norm_num) hx₁ hx₂

/-- **Ordinal cross-maximizer ordering, discharged on concrete optimizers.** We exhibit the actual
ordinal maximizers `0 ∈ argmaxRel (f 0) S = S` (the low type is indifferent on all of `[0,1]`) and
`1 ∈ argmaxRel (f (1/2)) S = {1}`, and conclude `0 ≤ 1` — a non-vacuous instance of the
ordering, not
just a conditional on assumed memberships. -/
theorem argmaxRel_le_at_concrete_optimizers : (0 : ℝ) ≤ 1 :=
  argmaxRel_le_of_singleCrossing f_singleCrossingRel 0 (1 / 2) (by norm_num)
    (by rw [argmaxRel_shapes.1]; exact ⟨le_refl 0, zero_le_one⟩)
    (by rw [argmaxRel_shapes.2]; exact rfl)

/-- **Ordinal strong set order.** At `θ₁ = 0 < θ₂ = 1/2`, the `argmaxRel` sets are in the strong
set order. By `argmaxRel_shapes` the lower set is the *nonempty* interval `[0,1]` and the upper set
is `{1}`, so the strong-set-order conclusion is non-vacuous (it would be trivially true if either
set
were empty). Exercises the relation-level `argmaxRel_strongSetOrder_of_singleCrossing`. -/
theorem argmaxRel_strongSetOrder_at_concrete :
    StrongSetOrder
      (argmaxRel (preferenceOfRealUtility (f 0)) S)
      (argmaxRel (preferenceOfRealUtility (f (1 / 2))) S) :=
  argmaxRel_strongSetOrder_of_singleCrossing f_singleCrossingRel 0 (1 / 2) (by norm_num)

/-- A **non-constant** optimal selection on the nonnegative-parameter subtype: choose the lowest
action `0` at the indifferent type `t = 0`, and the unique maximizer `1` at every strictly positive
type. Both are genuine maximizers of `f t x = t·x` over `[0,1]` (at `t = 0` everything is
optimal, so
`0` qualifies; at `t > 0` the strict monotonicity forces `1`), and the selection actually *moves*
(`0 ↦ 1`), so the monotone-selection theorems are exercised on a moving selection rather than a
constant one. -/
private def xSel : {t : ℝ // 0 ≤ t} → ℝ := fun t => if t.val = 0 then 0 else 1

/-- The selection lands in `[0,1]` (it is `0` or `1`). -/
private lemma xSel_mem (t : {t : ℝ // 0 ≤ t}) : xSel t ∈ S := by
  simp only [xSel]
  split <;> exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩

/-- The selection is genuinely **non-constant**: value `0` at `t = 0`, value `1` at `t = 1`. -/
theorem xSel_not_constant : xSel ⟨0, le_refl 0⟩ ≠ xSel ⟨1, zero_le_one⟩ := by
  simp only [xSel]; norm_num

/-- The selection is pointwise optimal: at `t = 0` it is `0` (everything is indifferent), and at
`t > 0` it is `1` (the strict maximizer). -/
private lemma xSel_opt (t : {t : ℝ // 0 ≤ t}) (x : ℝ) (hx : x ∈ S) :
    f t.val x ≤ f t.val (xSel t) := by
  simp only [Set.mem_Icc] at hx
  simp only [xSel, f]
  split
  · -- `t.val = 0`: `0 * x = 0 ≤ 0 = 0 * 0`.
    rename_i h0; rw [h0]; simp
  · -- `t.val > 0` (and `≥ 0`): `t * x ≤ t * 1` since `x ≤ 1`.
    exact mul_le_mul_of_nonneg_left hx.2 t.2

/-- **Monotone ordinal selection on a *moving* selection.** The non-constant selection `xSel`
(value `0` at `t = 0`, `1` at `t > 0`) is ordinal-optimal for `f t` over `S` at every nonneg type;
`argmaxRel_monotone_of_singleCrossing` then derives that this genuinely moving selection is
monotone.
A direction-reversed single crossing would force an antitone selection and fail here. -/
theorem argmaxRel_monotone_xSel : Monotone xSel :=
  argmaxRel_monotone_of_singleCrossing f_nn_singleCrossingRel xSel xSel_mem
    (fun θ x hx => by simpa only [preferenceOfUtilityIn_le_iff] using xSel_opt θ x hx)

/-- **Monotone cardinal selection on a *moving* selection.** The non-constant selection `xSel` is a
valid maximizer of `f t x = t·x` over `[0,1]` at every nonneg type, and single crossing makes it
monotone — a genuine comparative-statics move (`0 ↦ 1`), not a constant-policy tautology. -/
theorem argmax_monotone_xSel : Monotone xSel :=
  argmax_monotone_of_singleCrossing f_nn_cardinalSCP xSel xSel_mem
    (fun t => isMaxOn_iff.mpr (fun x hx => xSel_opt t x hx))

end SingleCrossingSelection

/-! ## Section 3: Value function inheritance -/

section ValueFunction

/-- **Value function monotone.** `V(t) = valueFunction (f t) S` is monotone in `t`. Since
`f t x = t * x` is monotone in `t` for each fixed `x ≥ 0`, the value function inherits
monotonicity. Anchor: `V(0) = 0 ≤ 1 = V(1)`, confirming the increasing direction. -/
theorem valueFunction_monotone :
    Monotone (fun t => valueFunction (f t) S) :=
  valueFunction_monotone_of_monotone
    S_nonempty
    (fun x hx t₁ t₂ ht => by
      simp only [Set.mem_Icc] at hx
      simp only [f]
      exact mul_le_mul_of_nonneg_right ht hx.1)
    (fun t => by
      apply (S_compact.image_of_continuousOn (f_cont t)).bddAbove)

/-- **Anchor: Value at `t = 0` is `0`.** `f 0 x = 0` for all `x`, so the value function is `0`. -/
theorem valueFunction_zero : valueFunction (f 0) S = 0 := by
  apply valueFunction_eq_of_isGreatest
  constructor
  · exact ⟨0, left_mem_Icc.mpr zero_le_one, by simp [f]⟩
  · rintro r ⟨x, _, rfl⟩
    simp [f]

/-- **Anchor: Value at `t = 1` is `1`.** `f 1 x = x`, maximized at `x = 1`. -/
theorem valueFunction_one : valueFunction (f 1) S = 1 := by
  apply valueFunction_eq_of_isGreatest
  constructor
  · exact ⟨1, right_mem_Icc.mpr zero_le_one, by simp [f]⟩
  · rintro r ⟨x, hx, rfl⟩
    simp only [f, one_mul]
    exact (mem_Icc.mp hx).2

/-- **Value rises from `0` to `1`.** The inequality `V(0) ≤ V(1)` is produced by *applying* the
library monotonicity `valueFunction_monotone` to `0 ≤ 1`; it is load-bearing (the statement is about
the actual value functions, not the pre-evaluated `0 ≤ 1`). The anchors `valueFunction_zero`/`_one`
independently certify the endpoints are `0` and `1`, so the direction is genuinely increasing. -/
theorem valueFunction_zero_le_one :
    valueFunction (f 0) S ≤ valueFunction (f 1) S :=
  valueFunction_monotone (show (0 : ℝ) ≤ 1 by norm_num)

/-- **Value function supermodular in two parameters.** Use `g θ ψ x = (θ + ψ) * x` over `S = [0,1]`.
The maximized value is `V(θ, ψ) = max (θ + ψ) 0`: when `θ + ψ ≥ 0` the maximizer is the upper corner
`x = 1` (value `θ + ψ`); when `θ + ψ < 0` it is the lower corner `x = 0` (value `0`). This
truncated-affine value function is supermodular in `(θ, ψ)`. -/
private abbrev g : ℝ → ℝ → ℝ → ℝ := fun θ ψ x => (θ + ψ) * x

/-- `g` satisfies the product supermodularity hypothesis of `valueFunction_supermodular`. The key
inequality `g (θ⊔θ') (ψ⊔ψ') (x⊔x') + g (θ⊓θ') (ψ⊓ψ') (x⊓x') ≥ g θ ψ x + g θ' ψ' x'` reduces to
`(max θ θ' + max ψ ψ') * max x x' + (min θ θ' + min ψ ψ') * min x x' ≥ (θ+ψ)*x + (θ'+ψ')*x'`, which
holds because each component pair satisfies `max·max + min·min ≥ a·b + a'·b'`. -/
-- Helper: bilinear supermodularity `a₂ * b₂ + a₁ * b₁ ≥ a₁ * b₂ + a₂ * b₁` when `a₁ ≤ a₂, b₁ ≤ b₂`
private lemma bilinear_super {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ + a₁ * b₁ ≥ a₁ * b₂ + a₂ * b₁ := by nlinarith

private lemma g_prod_supermodular :
    ∀ (θ θ' ψ ψ' x x' : ℝ),
      g (θ ⊔ θ') (ψ ⊔ ψ') (x ⊔ x') + g (θ ⊓ θ') (ψ ⊓ ψ') (x ⊓ x') ≥
      g θ ψ x + g θ' ψ' x' := by
  intro θ θ' ψ ψ' x x'
  simp only [g]
  -- Split on the ordering of each coordinate pair. After each `simp` all `⊔`/`⊓` reduce.
  -- Then the 8 goals follow from `nlinarith` using the bilinear helper on the sub-terms.
  rcases le_total θ θ' with hθ | hθ <;>
    rcases le_total ψ ψ' with hψ | hψ <;>
      rcases le_total x x' with hx | hx <;>
        simp only [sup_of_le_right hθ, sup_of_le_left hθ, sup_of_le_right hψ,
                   sup_of_le_left hψ, sup_of_le_right hx, sup_of_le_left hx,
                   inf_of_le_left hθ, inf_of_le_right hθ, inf_of_le_left hψ, inf_of_le_right hψ,
                   inf_of_le_left hx, inf_of_le_right hx, *] <;>
          nlinarith [bilinear_super hθ hx, bilinear_super hψ hx,
                     bilinear_super (le_refl x) (le_refl x)]

/-- `S` is a sublattice of `ℝ`: `[0,1]` is closed under `max` and `min`. -/
private lemma S_sublattice : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ⊔ x₂ ∈ S ∧ x₁ ⊓ x₂ ∈ S := by
  intro x₁ hx₁ x₂ hx₂
  simp only [S, mem_Icc] at hx₁ hx₂ ⊢
  exact ⟨⟨le_sup_of_le_left hx₁.1, sup_le hx₁.2 hx₂.2⟩,
         ⟨le_inf hx₁.1 hx₂.1, inf_le_of_left_le hx₁.2⟩⟩

/-- **Value function is supermodular** in `(θ, ψ)` for objective `g θ ψ x = (θ + ψ) · x`. -/
theorem g_valueFunction_supermodular :
    Supermodular (fun θ ψ => valueFunction (g θ ψ) S) :=
  valueFunction_supermodular g_prod_supermodular S_sublattice S_nonempty
    (fun θ ψ => by
      apply (S_compact.image_of_continuousOn ?_).bddAbove
      exact (continuous_const.mul continuous_id).continuousOn)

/-- **Positive-parameter anchor:** at `θ + ψ = 1 ≥ 0` the value is `V(1, 0) = 1`, attained at the
upper corner `x = 1`. -/
theorem g_valueFunction_pos : valueFunction (g 1 0) S = 1 := by
  apply valueFunction_eq_of_isGreatest
  constructor
  · exact ⟨1, right_mem_Icc.mpr zero_le_one, by simp [g]⟩
  · rintro r ⟨x, hx, rfl⟩
    simp only [g, add_zero, one_mul]
    exact (mem_Icc.mp hx).2

/-- **Negative-parameter anchor:** at `θ + ψ = -1 < 0` the value is `V(-1, 0) = 0`, attained at the
*lower* corner `x = 0` — *not* `θ + ψ = -1`. This is the case the naive `V = θ + ψ` reading gets
wrong: the truncated value is `max (θ + ψ) 0 = 0` here. -/
theorem g_valueFunction_neg : valueFunction (g (-1) 0) S = 0 := by
  apply valueFunction_eq_of_isGreatest
  constructor
  · exact ⟨0, left_mem_Icc.mpr zero_le_one, by simp [g]⟩
  · rintro r ⟨x, hx, rfl⟩
    simp only [g, add_zero]
    have hx0 := (mem_Icc.mp hx).1
    nlinarith [hx0]

end ValueFunction

/-! ## Section 4: Binding threshold comparative statics -/

section BindingThreshold

/-- **Concrete binding-threshold setup.**

`F x = 2 * x` and `G x = x` on `[0, 1)`. Both are strictly increasing. `F` strictly dominates `G`
pointwise: `G x = x < 2 * x = F x` for all `x > 0`.

Both bind at `t = 1/2`:

* `F u_F = 1/2`  ↔  `2 * u_F = 1/2`  ↔  `u_F = 1/4`
* `G u_G = 1/2`  ↔  `u_G = 1/2`

So `u_F = 1/4 < 1/2 = u_G`: The dominant function `F` binds at a strictly lower threshold. This is
`binding_threshold_lt_of_domination`. -/
private abbrev bigF : ℝ → ℝ := fun x => 2 * x
private abbrev bigG : ℝ → ℝ := fun x => x

/-- We use the domain `Ico (1/8) 1` to ensure strict domination `F x > G x` holds everywhere (at
`x ≥ 1/8 > 0`, `2*x > x`). Both binding points `1/4` and `1/2` lie in this domain. -/
private abbrev bindingDomain : Set ℝ := Set.Ico (1 / 8 : ℝ) 1

private lemma bigF_strictMono : StrictMonoOn bigF bindingDomain :=
  fun _ _ _ _ hlt => by simp only [bigF]; linarith

private lemma bigG_strictMono : StrictMonoOn bigG bindingDomain :=
  fun _ _ _ _ hlt => by simp only [bigG]; exact hlt

private lemma bigF_dominates_bigG :
    ∀ x ∈ bindingDomain, bigG x < bigF x := by
  intro x hx
  simp only [bigF, bigG, bindingDomain, Set.mem_Ico] at hx ⊢
  linarith

/-- `F` binds at `u_F = 1/4` for target `t = 1/2`. -/
private lemma bigF_binds : bigF (1 / 4 : ℝ) = 1 / 2 := by norm_num [bigF]

/-- `G` binds at `u_G = 1/2` for target `t = 1/2`. -/
private lemma bigG_binds : bigG (1 / 2 : ℝ) = 1 / 2 := by norm_num [bigG]

/-- **Binding threshold: `F`'s threshold is strictly below `G`'s.** Since `F` dominates `G`
pointwise on `[1/8, 1)`, and both bind at `t = 1/2`, the dominant function `F` hits the target at
`u_F = 1/4 < 1/2 = u_G`. -/
theorem bigF_threshold_lt_bigG_threshold :
    (1 / 4 : ℝ) < 1 / 2 :=
  binding_threshold_lt_of_domination
    bigF_strictMono bigG_strictMono
    (by norm_num : (1 / 4 : ℝ) ∈ bindingDomain)
    (by norm_num : (1 / 2 : ℝ) ∈ bindingDomain)
    bigF_binds bigG_binds bigF_dominates_bigG

/-- **Anti-monotone cost rises at the lower threshold.** The cost function `h x = 1 - x` is
strictly antitone on `[0,1)`. At the lower threshold `u_F = 1/4`, the cost is higher than at
`u_G = 1/2`: `h(1/2) = 1/2 < 3/4 = h(1/4)`. This exercises `strictAntiOn_apply_lt_of_binding_lt`
with the concrete threshold ordering from `bigF_threshold_lt_bigG_threshold`. -/
private abbrev costFn : ℝ → ℝ := fun x => 1 - x

private lemma costFn_strictAnti : StrictAntiOn costFn bindingDomain :=
  fun _ _ _ _ hlt => by simp only [costFn]; linarith

/-- **Cost at the lower threshold is strictly higher.** -/
theorem cost_at_lower_threshold_higher :
    costFn (1 / 2 : ℝ) < costFn (1 / 4 : ℝ) :=
  strictAntiOn_apply_lt_of_binding_lt costFn_strictAnti
    (by norm_num : (1 / 4 : ℝ) ∈ bindingDomain)
    (by norm_num : (1 / 2 : ℝ) ∈ bindingDomain)
    bigF_threshold_lt_bigG_threshold

end BindingThreshold

end EconlibTest.Optimization.ComparativeStatics

end
