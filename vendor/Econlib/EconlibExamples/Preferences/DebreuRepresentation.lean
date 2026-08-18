/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Debreu's Continuous Representation Theorem on the Policy Line

Debreu's theorem is the cornerstone of ordinal utility theory: A *continuous* preference relation
on a well-behaved space can be represented by a *continuous* real-valued utility function. The
adjective "continuous" appears on both sides — the hypothesis is a topological condition on the
order (closed contour sets), and the conclusion is a topological condition on the representing
scale. The content of the theorem is that the second follows from the first using nothing but the
order and the topology; one does not need to be handed a utility to begin with.

This file exhibits both halves of that story:

1. **The theorem, on an order-theoretic seed.** A decision maker on the policy line `X := ℝ` has
   the Euclidean ideal-point preference with bliss point `1`: Policy `x` is weakly preferred to `y`
   exactly when `x` is at least as close to the ideal point, `|x - 1| ≤ |y - 1|`. The preference is
   defined by this order — no utility function is handed to the construction. Its continuity is
   verified directly from the topology of `ℝ`: The weak upper contour sets are closed balls around
   the ideal point, and the weak lower contour sets are complements of open balls. Debreu's theorem
   then produces a continuous utility from the order and topology alone, via the separable Debreu
   order construction (countable basis → geometric raw utility → gap-collapsing rescale). (For
   preferences that do come packaged with a continuous utility, the bridge
   `ContinuousPreferenceRel.ofContinuousUtility` discharges the continuity hypothesis instead.)
2. **The counterexample, showing continuity is not decoration.** The lexicographic preference on
   `ℝ × ℝ` is complete and transitive — every axiom of rationality holds — yet it admits no
   real-valued utility representation, continuous or otherwise (`lexicographic_not_representable`).
   Rationality alone does not buy a utility function; the topological hypothesis is doing real
   work. (The preference is ordinally representable when the codomain may be the lexicographic
   order `ℝ ×ₗ ℝ` itself, `lexPref_represents_in_lex`; the obstruction is specific to `ℝ`.)

The ideal-point seed is the Euclidean single-peaked preference familiar from the median-voter
example (`EconlibExamples.Preferences.MedianVoter`); here it is built order-first rather than from
a quadratic-loss utility.

## Main definitions

* `idealPref` — the ideal-point preference on the policy line, defined order-theoretically:
  `x ≽ y ↔ |x - 1| ≤ |y - 1|`.
* `R` — the bundled continuous preference, via the no-utility-needed constructor
  `ContinuousPreferenceRel.ofContinuousPref`.
* `lexPref` — the lexicographic preference on `ℝ × ℝ`: First coordinate decides; the second breaks
  ties.

## Main statements

* `idealPref_continuous` — continuity of the preference, proved topologically: Upper contours are
  closed balls, lower contours are complements of open balls.
* `debreu_representation` — Debreu's theorem on `ℝ`: There exists a continuous utility representing
  `R.val`.
* `strictUpperContour_open` / `strictLowerContour_open` — strict upper/lower contour sets are open.
* `lexicographic_not_representable` — the lexicographic preference on `ℝ × ℝ` is rational but has
  no real-valued utility representation: Debreu's continuity hypothesis cannot be dropped.

## Tags

Debreu representation theorem, ideal-point preference, continuous utility, lexicographic preference
-/

noncomputable section

namespace EconlibExamples.Preferences.DebreuRepresentation

open Econlib.Preferences

/-! ## The order-theoretic seed: An ideal-point preference on the policy line -/

/-- The ideal-point preference on the policy line: Policy `x` is weakly preferred to `y` exactly
when `x` is at least as close to the bliss point `1`, i.e. `|x - 1| ≤ |y - 1|`. The preference is
defined directly by this order — there is no utility function in the construction. Reflexivity,
transitivity, and completeness are inherited from `≤` on distances. -/
def idealPref : PreferenceRel ℝ where
  le x y := |x - 1| ≤ |y - 1|
  le_refl _ := le_refl _
  le_trans _ _ _ hxy hyz := hxy.trans hyz
  le_total _ _ := le_total _ _

/-- The defining order, restated as a simp lemma: `x ≽ y ↔ |x - 1| ≤ |y - 1|`. -/
@[simp] lemma idealPref_le_iff (x y : ℝ) : (x ≽[idealPref] y) ↔ |x - 1| ≤ |y - 1| := Iff.rfl

/-- **Continuity of the ideal-point preference, from the topology alone.** The weak upper contour
set of `x` is the closed ball of radius `|x - 1|` around the ideal point, and the weak lower
contour set is the complement of the corresponding open ball — closed sets both, with no appeal to
any utility function. This is exactly the closed-contour-sets hypothesis of Debreu's theorem. -/
theorem idealPref_continuous : ContinuousPref idealPref := by
  constructor
  · -- Upper contours are closed balls: `{y | |y - 1| ≤ |x - 1|} = closedBall 1 |x - 1|`.
    intro x
    have hball : idealPref.upperContour x = Metric.closedBall 1 |x - 1| := by
      ext z
      simp [PreferenceRel.upperContour, Real.dist_eq]
    rw [hball]
    exact Metric.isClosed_closedBall
  · -- Lower contours are complements of open balls: `{y | |x - 1| ≤ |y - 1|} = (ball 1 |x - 1|)ᶜ`.
    intro x
    have hball : idealPref.lowerContour x = (Metric.ball 1 |x - 1|)ᶜ := by
      ext z
      simp [PreferenceRel.lowerContour, Real.dist_eq, not_lt]
    rw [hball]
    exact Metric.isOpen_ball.isClosed_compl

/-- The bundled continuous preference on the policy line, assembled by the order-first constructor
`ofContinuousPref`: The inputs are the preference relation and the topological continuity proof —
no generating utility. -/
def R : ContinuousPreferenceRel ℝ :=
  ContinuousPreferenceRel.ofContinuousPref idealPref idealPref_continuous

/-- The bundled relation is the seeded order, definitionally. -/
lemma R_val_eq : R.val = idealPref :=
  ContinuousPreferenceRel.ofContinuousPref_val idealPref idealPref_continuous

/-! ## Debreu's continuous representation theorem on `ℝ` -/

/-- **Debreu's theorem on the policy line.** There exists a continuous utility function `u`
representing the continuous preference `R.val`. The witness is produced by the Debreu separable-
order construction from the order and topology of `ℝ` alone — nothing in the hypotheses supplies a
utility. The application typechecks directly because `ℝ` is `Nonempty` and
`SecondCountableTopology`. -/
theorem debreu_representation :
    ∃ u : ℝ → ℝ, RepresentsRealPreference R.val u ∧ Continuous u :=
  R.exists_continuous_utility_representation

/-! ## The topological hallmark: Open strict contour sets -/

/-- **Strict upper contour sets are open.** The set of policies strictly preferred to `x` is open —
one of the two topological signatures of a continuous preference relation. -/
lemma strictUpperContour_open (x : ℝ) : IsOpen (R.val.strictUpperContour x) :=
  R.isOpen_strictUpperContour x

/-- **Strict lower contour sets are open.** The set of policies strictly worse than `x` is open —
the companion topological signature of continuity of preferences. -/
lemma strictLowerContour_open (x : ℝ) : IsOpen (R.val.strictLowerContour x) :=
  R.isOpen_strictLowerContour x

/-! ## The counterexample: Rationality without continuity buys nothing

The lexicographic preference on `ℝ × ℝ` ranks bundles by the first coordinate and breaks ties
with the second. It is complete and transitive — as rational as a preference can be — yet no
function `u : ℝ × ℝ → ℝ` represents it. The classical argument (Debreu 1954): Each vertical pair
`(x, 0) ≺ (x, 1)` would open a nonempty interval `(u (x, 0), u (x, 1))` in `ℝ`, and for `x < x'`
these intervals would be pairwise disjoint because `(x, 1) ≺ (x', 0)`. Picking a rational from each
gap yields a strictly monotone — hence injective — map `ℝ → ℚ`, contradicting the uncountability of
`ℝ`. The continuity hypothesis of Debreu's theorem is exactly what rules this order structure out:
The lexicographic order has uncountably many jumps, and `ℝ` has no room for them. -/

/-- The lexicographic preference on `ℝ × ℝ`: A bundle is weakly preferred when its first coordinate
is strictly larger, or the first coordinates tie and its second coordinate is weakly larger.
Constructed as the preference induced by the ordinal utility `toLex` valued in the lexicographic
linear order `ℝ ×ₗ ℝ`. -/
def lexPref : PreferenceRel (ℝ × ℝ) :=
  preferenceOfUtilityIn (toLex : ℝ × ℝ → ℝ ×ₗ ℝ)

/-- Weak lexicographic preference, unfolded: `x ≽ y` iff `y.1 < x.1`, or the first coordinates tie
and `y.2 ≤ x.2`. -/
@[simp] lemma lexPref_le_iff (x y : ℝ × ℝ) :
    (x ≽[lexPref] y) ↔ y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2) := by
  simp [lexPref, Prod.Lex.le_iff]

/-- The lexicographic preference is ordinally representable — by `toLex`, valued in the
lexicographic linear order `ℝ ×ₗ ℝ`. The obstruction in `lexicographic_not_representable` is
specific to the codomain `ℝ`. -/
lemma lexPref_represents_in_lex :
    RepresentsPreferenceIn lexPref (toLex : ℝ × ℝ → ℝ ×ₗ ℝ) :=
  preferenceOfUtilityIn_represents _

/-- **Lexicographic preferences admit no real-valued utility representation** (Debreu 1954).

The lexicographic preference on `ℝ × ℝ` is complete and transitive, but any representing
`u : ℝ × ℝ → ℝ` would put a nonempty open interval `(u (x, 0), u (x, 1))` above each `x : ℝ`, with
the intervals pairwise disjoint across distinct `x`. A rational chosen from each interval defines a
strictly monotone — hence injective — map `ℝ → ℚ`, which cannot exist since `ℝ` is uncountable.
This is the companion to `debreu_representation`: Dropping the continuity hypothesis costs the
conclusion, so rationality alone does not buy a utility function. -/
theorem lexicographic_not_representable :
    ¬ ∃ u : ℝ × ℝ → ℝ, RepresentsRealPreference lexPref u := by
  rintro ⟨u, hu⟩
  have hgap : ∀ x : ℝ, u (x, 0) < u (x, 1) := by
    intro x
    by_contra hle
    push Not at hle
    have h01 : (x, (0 : ℝ)) ≽[lexPref] (x, 1) := (hu (x, 0) (x, 1)).mpr hle
    norm_num at h01
  have hq : ∀ x : ℝ, ∃ q : ℚ, u (x, 0) < q ∧ (q : ℝ) < u (x, 1) :=
    fun x => exists_rat_btwn (hgap x)
  choose q hq₀ hq₁ using hq
  -- For `x < y`, the gaps are ordered: `q x < u (x, 1) ≤ u (y, 0) < q y`.
  have hq_strictMono : StrictMono q := by
    intro x y hxy
    have h_between : u (x, 1) ≤ u (y, 0) := (hu (y, 0) (x, 1)).mp (by simp [hxy])
    have hcast : (q x : ℝ) < (q y : ℝ) := ((hq₁ x).trans_le h_between).trans (hq₀ y)
    exact_mod_cast hcast
  exact not_injective_uncountable_countable q hq_strictMono.injective

end EconlibExamples.Preferences.DebreuRepresentation
