/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Mathlib

/-!
# Preferences Geometry Non-Vacuity Checks

Compile-time semantic witnesses for `Econlib.Preferences.Geometry`: `SinglePeaked`,
`SinglePeakedRel`, `SinglePeakedFinite`, `Supermodular.iff_increasing_differences`,
`monotonePreference_of_monotoneUtility`, `StrictMonotonePreference.toMonotonePreference`, and
`LatticePreference`.

## Anchor utility functions

**Section 1 — Single-peaked (quadratic loss, peak = 1/2).** `u₁(x) = -(x - 1/2)^2` constructed via
`SinglePeaked.quadraticLoss (1/2 : ℝ)`.

Hand-computed values:

| x   | u₁(x) |
| --- | ----- |
| 1/2 | 0     |
| 1/4 | -1/16 |
| 3/4 | -1/16 |
| 0   | -1/4  |
| 1   | -1/4  |

These witnesses catch:

* A left/right orientation flip in `closer_preferred` or `between_preferred`: The four explicit
  concrete comparisons (left-side pair 1/4 vs 0 and right-side pair 3/4 vs 1) each test one
  orientation; reversing the inequality sign breaks the corresponding positive check.
* A sign error in `peak_is_max`: U(1/2) = 0 and all other values are negative.
* `upper_contour_convex` concretely at level c = -1/4: The set {x | -(x-1/2)² ≥ -1/4} = [0, 1] is
  an interval, so any convex combination of 0 and 1 lies in it.

**Section 2 — Supermodular (complementary utility u₂(θ, x) = θ * x).**

Concrete check at (θ₁, θ₂, x₁, x₂) = (1, 2, 1, 3):
`u₂(2,3) - u₂(2,1) = 6 - 2 = 4 ≥ u₂(1,3) - u₂(1,1) = 3 - 1 = 2`. ✓ The orientation test: The
higher-type marginal gain (4) exceeds the lower-type marginal gain (2), which is exactly the
comparative-statics direction. Reversing θ or x would flip the inequality.

**Section 3 — Monotone-preference bridges (sum utility u₃(x, y) = x + y on ℝ²).**

`u₃` is monotone in the pointwise order. Dominance pair: X = (0, 0), y = (1, 2), so u₃(x) = 0 ≤ 3 =
u₃(y). For strict monotonicity we use `u₄(x) = x` on `ℝ` with the standard order. For
`LatticePreference` we use `u₅(t) = t` on `ℝ`: `x ≽ z ∧ y ≽ z` means `x ≥ z` and `y ≥ z`, so
`x ⊔ y = max(x,y) ≥ x ≥ z` and `x ⊓ y = min(x,y) ≥ z` (since both ≥ z). Concrete: Z = 1, x = 2, y =
3.
-/

noncomputable section

namespace EconlibTest.Preferences.Geometry

open Econlib.Preferences

/-! ## Section 1. Single-peaked preferences (quadratic loss, peak = 1/2)

Every API lemma of `SinglePeaked` is checked on `u₁ x = -(x - 1/2)^2`. `closer_preferred` and
`between_preferred` each have both a left-side check (x ≤ 1/2) and a right-side check (x ≥ 1/2), to
catch orientation bugs in either direction. -/

section single_peaked

/-- The quadratic-loss single-peaked preference at peak 1/2. -/
private abbrev sp : SinglePeaked (fun x : ℝ => -(x - 1 / 2) ^ 2) :=
  SinglePeaked.quadraticLoss (1 / 2)

/-- **`SinglePeaked.peak_is_max` at x = 3/4.** Peak 1/2 weakly dominates 3/4: u₁(3/4) = -(1/4)² =
-1/16 ≤ 0 = u₁(1/2). Proved by *applying* the API lemma `sp.peak_is_max (3/4)` (not bare
arithmetic), with the RHS stated as the honest peak value `-(1/2 - 1/2)^2 = 0` (no zero-hiding
`* (-1)`). -/
theorem peak_is_max_three_quarters :
    -(3 / 4 - 1 / 2 : ℝ) ^ 2 ≤ -(1 / 2 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  have h := sp.peak_is_max (3 / 4 : ℝ)
  simp only [hsp] at h
  exact h

/-- **`SinglePeaked.peak_is_max` API directly.** Peak 1/2 weakly dominates 0. u₁(0) = -(0-1/2)² =
-1/4 ≤ 0 = u₁(1/2). -/
theorem sp_peak_is_max_zero : -(0 - 1 / 2 : ℝ) ^ 2 ≤ -(1 / 2 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  have h := sp.peak_is_max (0 : ℝ)
  simp only [hsp] at h
  exact h

/-- **`SinglePeaked.peak_is_max` at x = 1.** u₁(1) = -(1/2)² = -1/4 ≤ 0 = u₁(1/2). -/
theorem sp_peak_is_max_one : -(1 - 1 / 2 : ℝ) ^ 2 ≤ -(1 / 2 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  have := sp.peak_is_max (1 : ℝ)
  simpa [hsp] using this

/-- **`SinglePeaked.peak_unique_max`.** Only x = 1/2 attains u₁(x) = 0. -/
theorem sp_peak_unique_max : ∀ x : ℝ, -(x - 1 / 2) ^ 2 = 0 → x = 1 / 2 := by
  intro x h
  have hsp : sp.peak = 1 / 2 := rfl
  apply sp.peak_unique_max
  rw [hsp]
  simp
  nlinarith [sq_nonneg (x - 1 / 2)]

/-- **`closer_preferred`, left side (x = 1/4 closer to peak than y = 0).** Both x = 1/4 and y = 0
are ≤ 1/2. |1/4 - 1/2| = 1/4 < 1/2 = |0 - 1/2|. So u₁(0) < u₁(1/4): -1/4 < -1/16. ✓ -/
theorem sp_closer_preferred_left :
    -(0 - 1 / 2 : ℝ) ^ 2 < -(1 / 4 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  have := sp.closer_preferred
    (x := 1 / 4) (y := 0)
    (h_side := Or.inl ⟨by rw [hsp]; norm_num, by rw [hsp]; norm_num⟩)
    (h_dist := by rw [hsp]; norm_num)
  simpa [hsp] using this

/-- **`closer_preferred`, right side (x = 3/4 closer to peak than y = 1).** Both x = 3/4 and y = 1
are ≥ 1/2. |3/4 - 1/2| = 1/4 < 1/2 = |1 - 1/2|. So u₁(1) < u₁(3/4): -1/4 < -1/16. ✓ -/
theorem sp_closer_preferred_right :
    -(1 - 1 / 2 : ℝ) ^ 2 < -(3 / 4 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  have := sp.closer_preferred
    (x := 3 / 4) (y := 1)
    (h_side := Or.inr ⟨by rw [hsp]; norm_num, by rw [hsp]; norm_num⟩)
    (h_dist := by rw [hsp]; norm_num)
  simpa [hsp] using this

/-- **`between_preferred`, left side.** x = 0 ≤ y = 1/4 ≤ 1/2 → u₁(0) ≤ u₁(1/4): -1/4 ≤ -1/16. ✓ -/
theorem sp_between_preferred_left :
    -(0 - 1 / 2 : ℝ) ^ 2 ≤ -(1 / 4 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  exact sp.between_preferred (x := 0) (y := 1 / 4)
    (h := Or.inl ⟨by norm_num, by rw [hsp]; norm_num⟩)

/-- **`between_preferred`, right side.** 1/2 ≤ y = 3/4 ≤ x = 1 → u₁(1) ≤ u₁(3/4): -1/4 ≤ -1/16. ✓ -/
theorem sp_between_preferred_right :
    -(1 - 1 / 2 : ℝ) ^ 2 ≤ -(3 / 4 - 1 / 2 : ℝ) ^ 2 := by
  have hsp : sp.peak = 1 / 2 := rfl
  exact sp.between_preferred (x := 1) (y := 3 / 4)
    (h := Or.inr ⟨by rw [hsp]; norm_num, by norm_num⟩)

/-- **Negative check: X = 1 is NOT closer to peak 1/2 than x = 3/4.** Stated as an actual
distance-from-peak comparison: `|1 - 1/2| = 1/2` is *not* `< 1/4 = |3/4 - 1/2|`. This is the
`h_dist` hypothesis of `closer_preferred` failing in the reverse orientation, so the lemma cannot
conclude `1 ≻ 3/4`. -/
theorem sp_closer_preferred_neg : ¬ |(1 : ℝ) - 1 / 2| < |(3 / 4 : ℝ) - 1 / 2| := by
  rw [show |(1:ℝ) - 1/2| = 1/2 by rw [abs_of_nonneg] <;> norm_num,
      show |(3/4:ℝ) - 1/2| = 1/4 by rw [abs_of_nonneg] <;> norm_num]
  norm_num

/-- **`SinglePeaked.upper_contour_convex`.** At level c = -1/4, the upper contour set {x |
-(x-1/2)² ≥ -1/4} is convex (it equals [0,1]). We apply the API directly: Any convex combination of
two points in the upper contour set is also in it. -/
theorem sp_upper_contour_convex : Convex ℝ {x : ℝ | -(x - 1 / 2) ^ 2 ≥ -1 / 4} :=
  sp.upper_contour_convex (-1 / 4)

/-- Concrete membership check: X = 0 is in the -1/4 upper contour set. -/
theorem sp_zero_in_contour : (0 : ℝ) ∈ {x : ℝ | -(x - 1 / 2) ^ 2 ≥ -1 / 4} := by
  simp; norm_num

/-- Concrete membership check: X = 1 is in the -1/4 upper contour set. -/
theorem sp_one_in_contour : (1 : ℝ) ∈ {x : ℝ | -(x - 1 / 2) ^ 2 ≥ -1 / 4} := by
  simp; norm_num

/-- **Convex-combination is in contour set, via the convexity API.** The midpoint `1/2` of `0` and
`1` is in the `-1/4` contour set — derived by *applying* `sp.upper_contour_convex (-1/4)` to the two
endpoint memberships `sp_zero_in_contour`, `sp_one_in_contour` with weights `1/2, 1/2`, then
identifying `(1/2)•0 + (1/2)•1 = 1/2`. This genuinely exercises the convex-combination API rather
than recomputing the membership by hand. -/
theorem sp_midpoint_in_contour : (1 / 2 : ℝ) ∈ {x : ℝ | -(x - 1 / 2) ^ 2 ≥ -1 / 4} := by
  have h := sp.upper_contour_convex (-1 / 4) sp_zero_in_contour sp_one_in_contour
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have he : (1/2 : ℝ) • (0:ℝ) + (1/2 : ℝ) • (1:ℝ) = 1/2 := by norm_num
  rwa [he] at h

end single_peaked

/-! ## Section 2. `SinglePeakedRel` — the ordinal layer

We convert our concrete `SinglePeaked sp` to a `SinglePeakedRel` and check its API. -/

section single_peaked_rel

/-- The relational single-peaked structure at peak 1/2, derived from the cardinal `sp`. -/
private abbrev spRel : SinglePeakedRel (preferenceOfRealUtility (fun x : ℝ => -(x - 1 / 2) ^ 2)) :=
  sp.toRel

/-- **The ordinal conversion preserves the peak.** `spRel.peak = (1/2 : ℝ)` independently of the
relational max lemmas: the `toRel` construction carries the cardinal peak `1/2` through unchanged. A
conversion that dropped or shifted the peak would falsify this. -/
theorem spRel_peak_eq : spRel.peak = (1 / 2 : ℝ) := rfl

/-- **`SinglePeakedRel.peak_is_max`, stated at the literal anchor `1/2`.** The peak `1/2` weakly
dominates `0` in the induced preference: `le` holds iff `u(1/2) ≥ u(0)`, i.e. `0 ≥ -1/4`. Stated
with the concrete `(1/2 : ℝ)` (via `spRel_peak_eq`) rather than the opaque `spRel.peak`, so the
docstring's "peak 1/2" claim is independently guarded. -/
theorem spRel_peak_is_max_zero :
    (preferenceOfRealUtility (fun x : ℝ => -(x - 1 / 2) ^ 2)).le (1 / 2 : ℝ) 0 := by
  rw [← spRel_peak_eq]; exact spRel.peak_is_max 0

/-- **`SinglePeakedRel.peak_is_max` at x = 1, literal anchor.** `u(1) = -1/4 ≤ 0 = u(1/2)`. -/
theorem spRel_peak_is_max_one :
    (preferenceOfRealUtility (fun x : ℝ => -(x - 1 / 2) ^ 2)).le (1 / 2 : ℝ) 1 := by
  rw [← spRel_peak_eq]; exact spRel.peak_is_max 1

end single_peaked_rel

/-! ## Section 3. `SinglePeakedFinite` on a Fin 5 grid

Policy grid: Positions [0, 1/4, 1/2, 3/4, 1], peak at index 2 (= 1/2). Utility values: [-1/4,
-1/16, 0, -1/16, -1/4] (quadratic loss at peak 1/2). -/

section single_peaked_finite

/-- Position map for a 5-point policy grid. -/
private abbrev pos5 : Fin 5 → ℝ := ![0, 1 / 4, 1 / 2, 3 / 4, 1]

/-- Utility values on the grid (quadratic loss). -/
private abbrev util5 : Fin 5 → ℝ := ![-1 / 4, -1 / 16, 0, -1 / 16, -1 / 4]

/-- The strictly monotone position map for the 5-point grid. -/
private lemma pos5_strictMono : StrictMono pos5 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pos5] <;> norm_num

/-- **`SinglePeakedFinite` instance on a Fin 5 grid.** Peak at index 2 (position 1/2). Left/right
fields discharge by `fin_cases` + `norm_num`. -/
def spFin : SinglePeakedFinite 5 pos5 util5 where
  strictMono_pos := pos5_strictMono
  peakIdx := ⟨2, by norm_num⟩
  left_of_peak := by
    intro i j hij hjp
    fin_cases i <;> fin_cases j <;> simp_all [pos5, util5] <;> norm_num at *
  right_of_peak := by
    intro i j hpi hij
    fin_cases i <;> fin_cases j <;> simp_all [pos5, util5] <;> norm_num at *

/-- **Non-vacuity check: Left side.** Index 0 (pos 0) vs index 1 (pos 1/4), both left of peak 1/2.
`left_of_peak`: Util5 0 < util5 1, i.e., -1/4 < -1/16. ✓ -/
theorem spFin_left_check : util5 ⟨0, by norm_num⟩ < util5 ⟨1, by norm_num⟩ := by
  have hpeak : spFin.peakIdx = ⟨2, by norm_num⟩ := rfl
  apply spFin.left_of_peak ⟨0, by norm_num⟩ ⟨1, by norm_num⟩
  · simp [pos5]
  · rw [hpeak]; simp [pos5]; norm_num

/-- **Non-vacuity check: Right side.** Index 3 (pos 3/4) vs index 4 (pos 1), both right of peak.
`right_of_peak`: Util5 4 < util5 3, i.e., -1/4 < -1/16. ✓ -/
theorem spFin_right_check : util5 ⟨4, by norm_num⟩ < util5 ⟨3, by norm_num⟩ := by
  have hpeak : spFin.peakIdx = ⟨2, by norm_num⟩ := rfl
  apply spFin.right_of_peak ⟨3, by norm_num⟩ ⟨4, by norm_num⟩
  · rw [hpeak]; simp [pos5]; norm_num
  · simp [pos5]; norm_num

end single_peaked_finite

/-! ## Section 4. Supermodularity ⟺ increasing differences

Anchor: `u₂(θ, x) = θ * x` on `ℝ` — the canonical complementary goods / cross-elasticity
example.

Supermodularity criterion: U₂(θ₂, x₂) + u₂(θ₁, x₁) ≥ u₂(θ₂, x₁) + u₂(θ₁, x₂) iff θ₂*x₂ + θ₁*x₁ ≥
θ₂*x₁ + θ₁*x₂ iff (θ₂ - θ₁)*(x₂ - x₁) ≥ 0, which holds for θ₁ ≤ θ₂, x₁ ≤ x₂. ✓

Increasing-differences form (the iff direction): U₂(θ₂, x₂) - u₂(θ₂, x₁) ≥ u₂(θ₁, x₂) - u₂(θ₁, x₁)
i.e., θ₂*(x₂-x₁) ≥ θ₁*(x₂-x₁), which follows from θ₁ ≤ θ₂ and x₁ ≤ x₂. ✓

Concrete anchor: (θ₁, θ₂, x₁, x₂) = (1, 2, 1, 3). u₂(2,3) - u₂(2,1) = 6 - 2 = 4. u₂(1,3) - u₂(1,1)
= 3 - 1 = 2. 4 ≥ 2. ✓  (comparative statics: Higher type θ gains more from increasing action) -/

section supermodular

/-- The complementary utility function u₂(θ, x) = θ * x. -/
private abbrev u₂ : ℝ → ℝ → ℝ := fun θ x => θ * x

/-- **`u₂` is supermodular.** For θ₁ ≤ θ₂ and x₁ ≤ x₂, u₂(θ₂,x₂) + u₂(θ₁,x₁) ≥ u₂(θ₂,x₁) +
u₂(θ₁,x₂). -/
theorem u₂_supermodular : Supermodular u₂ := fun θ₁ θ₂ x₁ x₂ hθ hx => by
  simp only [u₂]
  nlinarith

/-- **Forward direction of `Supermodular.iff_increasing_differences`, genuinely applied.** The
concrete increasing-differences inequality at `(θ₁,θ₂,x₁,x₂) = (1,2,1,3)` — `4 ≥ 2` — is obtained by
*feeding* `u₂_supermodular` through the `.mp` direction of the library iff, not by re-deriving the
arithmetic. A broken forward direction would fail to produce this. -/
theorem u₂_increasing_differences_concrete :
    u₂ 2 3 - u₂ 2 1 ≥ u₂ 1 3 - u₂ 1 1 :=
  (Supermodular.iff_increasing_differences u₂).mp u₂_supermodular 1 2 1 3
    (by norm_num) (by norm_num)

/-- **The iff in both directions at (1,2,1,3):** reading off the abstract equivalence
`Supermodular.iff_increasing_differences` and instantiating it at `u₂`. -/
theorem u₂_iff_instantiated :
    Supermodular u₂ ↔ ∀ (θ₁ θ₂ : ℝ) (x₁ x₂ : ℝ), θ₁ ≤ θ₂ → x₁ ≤ x₂ →
      u₂ θ₂ x₂ - u₂ θ₂ x₁ ≥ u₂ θ₁ x₂ - u₂ θ₁ x₁ :=
  Supermodular.iff_increasing_differences u₂

/-- **Backward direction of the iff.** From the increasing-differences property, reconstruct
supermodularity. We use `Supermodular.iff_increasing_differences` in the ← direction and
verify it holds for `u₂`. -/
theorem u₂_supermodular_of_incr_diff : Supermodular u₂ := by
  rw [Supermodular.iff_increasing_differences]
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [u₂]
  nlinarith

/-- **Orientation check (negative).** The increasing-differences inequality is NOT symmetric:
Reversing the sign of one variable breaks it. Concretely, at (θ₁=2, θ₂=1, x₁=1, x₂=3) (θ-order
reversed), u₂(1,3)-u₂(1,1) = 2 is NOT ≥ u₂(2,3)-u₂(2,1) = 4. -/
theorem u₂_incr_diff_not_reversed : ¬ (u₂ 1 3 - u₂ 1 1 ≥ u₂ 2 3 - u₂ 2 1) := by
  simp [u₂]; norm_num

end supermodular

/-! ## Section 5. Monotone-preference bridges

### `monotonePreference_of_monotoneUtility`

Anchor: `u₃(a, b) = a + b` on `Fin 2 → ℝ` with the pointwise order. `u₃` is monotone: If a ≤ a'
and b ≤ b', then a + b ≤ a' + b'. Dominance pair: X = ![0, 0], y = ![1, 2]: U₃(x) = 0 ≤ 3 =
u₃(y).

### `StrictMonotonePreference.toMonotonePreference`

Anchor: `u₄ : ℝ → ℝ`, `u₄ t = t`. Strictly monotone: S ≤ t → s ≠ t → s < t. Then
`strictMonotonePreference_of_strictMono` gives a `StrictMonotonePreference`, and
`.toMonotonePreference` gives a `MonotonePreference`.

### `LatticePreference`

Anchor: `u₅ : ℝ → ℝ`, `u₅ t = t`, on `ℝ` with its natural lattice (⊔ = max, ⊓ = min). `R₅.le x z`
means `u₅(z) ≤ u₅(x)`, i.e., `z ≤ x` (standard order). For `x ≽ z` and `y ≽ z` (x ≥ z, y ≥ z): X ⊔
y = max(x,y) ≥ x ≥ z  ✓ x ⊓ y = min(x,y) ≥ z because both x ≥ z and y ≥ z  ✓ -/

section monotone_bridges

/-- Sum utility on `Fin 2 → ℝ`: U₃ x = x 0 + x 1. -/
private abbrev u₃ : (Fin 2 → ℝ) → ℝ := fun v => v 0 + v 1

/-- `u₃` is monotone in the pointwise order. -/
private lemma u₃_monotone : Monotone u₃ := fun x y hxy => by
  simp only [u₃]
  linarith [hxy 0, hxy 1]

/-- **`monotonePreference_of_monotoneUtility`.**  Derive the preference from the utility. -/
def monoPref₃ : MonotonePreference (preferenceOfRealUtility u₃) :=
  monotonePreference_of_monotoneUtility u₃ u₃_monotone

/-- **Non-vacuity check via the `monoPref₃` field on *distinct* bundles.** `y = ![1,2]` dominates
`x = ![0,0]` pointwise (`0 ≤ 1`, `0 ≤ 2`), so `monoPref₃.monotone` (the monotone-preference field,
not bare utility arithmetic) yields `![1,2] ≽ ![0,0]`. This consumes
`monotonePreference_of_monotoneUtility` on a non-degenerate pair, so a broken monotonicity bridge
would be caught. -/
theorem monoPref₃_dominance :
    (preferenceOfRealUtility u₃).le (![1, 2] : Fin 2 → ℝ) ![0, 0] :=
  monoPref₃.monotone (by intro i; fin_cases i <;> norm_num)

/-- Identity utility on ℝ, strictly monotone. -/
private abbrev u₄ : ℝ → ℝ := id

/-- **`strictMonotonePreference_of_strictMono`.**  Derive a strict monotone preference. -/
def strictMonoPref₄ : StrictMonotonePreference (preferenceOfRealUtility u₄) :=
  strictMonotonePreference_of_strictMono u₄ (fun hxy hne => lt_of_le_of_ne hxy fun h => hne h)

/-- **`StrictMonotonePreference.toMonotonePreference`.**  Chain to weak monotonicity. -/
def monoPref₄ : MonotonePreference (preferenceOfRealUtility u₄) :=
  strictMonoPref₄.toMonotonePreference

/-- **Strict implies weak, through the strict field.** At `(1, 2)`: `strictMonoPref₄.strictMono`
gives the *strict* preference `2 ≻ 1` (`u₄ 1 = 1 < 2 = u₄ 2`), and its `.1` component is the weak
preference `2 ≽ 1`. This genuinely traverses the strict→weak path (the content of
`StrictMonotonePreference.toMonotonePreference`) rather than recomputing `1 ≤ 2` from the utility
definition. -/
theorem monoPref₄_weak_at_one_two :
    (preferenceOfRealUtility u₄).le 2 1 :=
  (strictMonoPref₄.strictMono (by norm_num : (1:ℝ) ≤ 2) (by norm_num)).1

/-- Verify the structure field is non-trivial: 2 weakly dominates 1 via `monoPref₄.monotone`. -/
theorem monoPref₄_monotone_field :
    (preferenceOfRealUtility u₄).le (2 : ℝ) 1 :=
  monoPref₄.monotone (by norm_num)

/-- Linear utility on ℝ. -/
private abbrev u₅ : ℝ → ℝ := id

/-- **`LatticePreference` instance.**  `ℝ` with its natural lattice (⊔ = max, ⊓ = min), utility u₅
= id. R₅.le x z ↔ z ≤ x (standard order). If x ≥ z and y ≥ z then: Max(x,y) ≥ x ≥ z and min(x,y) ≥
z (since both ≥ z). -/
def latticePref₅ : LatticePreference (preferenceOfRealUtility u₅) where
  upper_closed_sup_inf x y z hxz hyz := by
    simp only [preferenceOfUtilityIn_le_iff, u₅, id] at *
    constructor
    · -- z ≤ max(x, y): since z ≤ x.
      exact le_trans hxz (le_sup_left)
    · -- z ≤ min(x, y): since z ≤ x and z ≤ y.
      exact le_inf hxz hyz

/-- **Non-vacuity check for `LatticePreference`, premises discharged.** With `z = 1, x = 2, y = 3`
(both `≥ 1` under `u₅ = id`), the `upper_closed_sup_inf` field yields both `2 ⊔ 3 ≽ 1` and
`2 ⊓ 3 ≽ 1`. The two numeric premises `2 ≽ 1`, `3 ≽ 1` are discharged here, so this is an
*unconditional* witness — not a conditional wrapper around the field. -/
theorem latticePref₅_concrete :
    let R := preferenceOfRealUtility u₅
    R.le ((2 : ℝ) ⊔ 3) 1 ∧ R.le ((2 : ℝ) ⊓ 3) 1 := by
  apply latticePref₅.upper_closed_sup_inf
  · simp [preferenceOfUtilityIn_le_iff, u₅]
  · simp [preferenceOfUtilityIn_le_iff, u₅]

/-- The sup/inf in the lattice check are the genuine `max`/`min`: `2 ⊔ 3 = 3` and `2 ⊓ 3 = 2`, so
the contour membership above is about the *distinct* combined bundles, not a degenerate
self-bound. -/
theorem latticePref₅_sup_inf_values : ((2 : ℝ) ⊔ 3 = 3) ∧ ((2 : ℝ) ⊓ 3 = 2) := by
  constructor <;> norm_num

end monotone_bridges

end EconlibTest.Preferences.Geometry

end
