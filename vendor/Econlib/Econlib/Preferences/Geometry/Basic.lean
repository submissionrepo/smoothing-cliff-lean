/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.StrongSetOrder
public import Econlib.Preferences.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Order.Lattice

/-!
# Geometric preference predicates

This file collects domain-geometry predicates for preferences. They keep `PreferenceRel`
outcome-generic, adding exactly the order, lattice, product, or convex structure needed for
monotonicity, convexity, welfare, and comparative-statics statements, and supply bridges from the
corresponding real-valued utility conditions.

## Main definitions

* `ConvexPreference`, `StrictConvexPreference` — convex (resp. strictly convex) upper contour sets
  on a real vector domain, the relation-level analogs of quasiconcavity.
* `MonotonePreference`, `StrictMonotonePreference` — monotone and strong monotonicity of preference
  on an ordered domain.
* `StrictMonoToInterior`, `BoundaryAvoiding`, `Desirable` — the weakenings of strong monotonicity
  on a commodity space `ι → ℝ` appearing in welfare and equilibrium-existence theorems.
* `LatticePreference` — lattice-domain preference interface for Topkis–Veinott arguments.

## Main statements

* `QuasiconcaveOn.toConvexPreference`, `monotonePreference_of_monotoneUtility`,
  `strictMonotonePreference_of_strictMono` — utility-to-preference bridges.
* `ConvexPreference.strictUpperContour_convex` — strict upper contour sets of a convex preference
  are convex.
* `StrictMonotonePreference.toDesirable`, `BoundaryAvoiding.toDesirable` — both routes to
  `Desirable`.

## Notes

For an ordinal theorem, state it for `PreferenceRel` plus a geometry predicate such as
`MonotonePreference`, `ConvexPreference`, or `LatticePreference`; for one needing real arithmetic,
integration, derivatives, or expected utility, use the corresponding real-valued utility predicate
together with a bridge to preferences. Broader generalizations of comparative-statics theorems from
linearly ordered real actions to these predicates belong with the corresponding optimization
results.

## Tags

preferences, convexity, monotonicity, quasiconcavity, lattice, comparative statics
-/

@[expose] public section

namespace Econlib.Preferences

/-- A preference relation has convex upper contour sets on a real vector domain.

This is the relation-level analog of quasiconcavity of a utility representation. It should be used
when convexity of choice sets is needed but the actual utility scale is irrelevant. -/
structure ConvexPreference {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (R : PreferenceRel E) : Prop where
  convex_upper : ∀ x : E, Convex ℝ (PreferenceRel.upperContour R x)

/-- **Strict convexity of preferences.** Any nontrivial convex combination of two distinct points,
each at least as good as `z`, is strictly better than `z`. This is the relation-level analog of
strict quasiconcavity; combined with a convex feasible set it forces single-valued demand
(`Econlib.Optimization.argmaxRel_subsingleton_of_strictConvex`). -/
structure StrictConvexPreference {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    (R : PreferenceRel E) : Prop where
  strict_convex :
    ∀ ⦃x y z : E⦄, x ≠ y → (x ≽[R] z) → (y ≽[R] z) →
      ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 → ((a • x + b • y) ≻[R] z)

/-- A quasiconcave real utility induces convex preferences.

Quasiconcavity of a utility (convex superlevel sets) is Mathlib's `QuasiconcaveOn ℝ Set.univ u`;
build it with `Convex.quasiconcaveOn_of_convex_ge convex_univ`. -/
lemma _root_.QuasiconcaveOn.toConvexPreference {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {u : E → ℝ} (hu : QuasiconcaveOn ℝ Set.univ u) :
    ConvexPreference (preferenceOfRealUtility u) where
  convex_upper x := by
    simpa [PreferenceRel.upperContour, preferenceOfRealUtility, preferenceOfUtilityIn,
      Set.sep_univ] using hu (u x)

/-- The strict upper contour set of a convex preference is convex: Any nontrivial convex
combination of two bundles each strictly preferred to `x` is again strictly preferred to `x`. -/
theorem ConvexPreference.strictUpperContour_convex {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {R : PreferenceRel E} (hconv : ConvexPreference R) (x : E) :
    Convex ℝ (R.strictUpperContour x) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  simp only [PreferenceRel.strictUpperContour, Set.mem_setOf_eq] at hy₁ hy₂ ⊢
  rcases R.le_total y₁ y₂ with h12 | h21
  · -- Convexity of the upper contour at `y₂` gives `a • y₁ + b • y₂ ≽ y₂ ≻ x`.
    have hge : (a • y₁ + b • y₂) ≽[R] y₂ :=
      hconv.convex_upper y₂ h12 (R.le_refl y₂) ha hb hab
    exact R.lt_of_le_of_lt hge hy₂
  · -- Convexity of the upper contour at `y₁` gives `a • y₁ + b • y₂ ≽ y₁ ≻ x`.
    have hge : (a • y₁ + b • y₂) ≽[R] y₁ :=
      hconv.convex_upper y₁ (R.le_refl y₁) h21 ha hb hab
    exact R.lt_of_le_of_lt hge hy₁

/-- Preference monotonicity on an ordered domain: A weakly larger bundle is at least as good.

For concrete commodity bundles, instantiate `X` as `ι → ℝ` with the pointwise order. -/
structure MonotonePreference {X : Type*} [Preorder X] (R : PreferenceRel X) : Prop where
  monotone : ∀ {x y : X}, y ≤ x → x ≽[R] y

/-- A monotone real utility induces a monotone preference. -/
lemma monotonePreference_of_monotoneUtility {X : Type*} [Preorder X]
    (u : X → ℝ) (hu : Monotone u) :
    MonotonePreference (preferenceOfRealUtility u) where
  monotone hxy := hu hxy

/-- **Strong monotonicity** of preference: Weakly more of every good and strictly more of some good
is strictly better. For commodity bundles `X = Fin L → ℝ` with the pointwise order, `x ≤ y` with
`x ≠ y` means `y` dominates `x` weakly everywhere and strictly somewhere. This is the "more is
strictly better" hypothesis behind positive equilibrium prices, strictly stronger than
`MonotonePreference`. -/
structure StrictMonotonePreference {X : Type*} [Preorder X] (R : PreferenceRel X) : Prop where
  strictMono : ∀ {x y : X}, x ≤ y → x ≠ y → y ≻[R] x

/-- Strict monotonicity implies (weak) monotonicity. -/
lemma StrictMonotonePreference.toMonotonePreference {X : Type*} [Preorder X] {R : PreferenceRel X}
    (h : StrictMonotonePreference R) : MonotonePreference R where
  monotone {x y} hyx := by
    rcases eq_or_ne y x with rfl | hne
    · exact R.le_refl _
    · exact (h.strictMono hyx hne).1

/-- A strictly monotone real utility induces a strictly monotone preference. -/
lemma strictMonotonePreference_of_strictMono {X : Type*} [Preorder X]
    (u : X → ℝ) (hu : ∀ {x y : X}, x ≤ y → x ≠ y → u x < u y) :
    StrictMonotonePreference (preferenceOfRealUtility u) where
  strictMono hxy hne := by
    refine ⟨(hu hxy hne).le, fun hge => ?_⟩
    exact absurd (hge : u _ ≤ u _) (not_le.mpr (hu hxy hne))

/-- **Strict monotonicity toward interior bundles.** On a commodity space `ι → ℝ`: If `y` dominates
`x` coordinatewise (`x ≤ y`, `x ≠ y`) and `y` is strictly positive in every coordinate, then
`y ≻ x`. This is the weakening of strong monotonicity (`StrictMonotonePreference`) that admits
boundary-flat utilities such as Cobb–Douglas (`∏ xᵢ^αᵢ`, which is `0` whenever any coordinate
vanishes): The dominating bundle is required to lie in the interior of the orthant, where such
utilities are strictly increasing. Strong monotonicity implies it
(`StrictMonotonePreference.toStrictMonoToInterior`). -/
structure StrictMonoToInterior {ι : Type*} (R : PreferenceRel (ι → ℝ)) : Prop where
  strictMono : ∀ {x y : ι → ℝ}, x ≤ y → x ≠ y → (∀ l, 0 < y l) → y ≻[R] x

/-- Strong monotonicity implies strict monotonicity toward interior bundles. -/
lemma StrictMonotonePreference.toStrictMonoToInterior {ι : Type*} {R : PreferenceRel (ι → ℝ)}
    (h : StrictMonotonePreference R) : StrictMonoToInterior R where
  -- The strict-positivity hypothesis on `y` is unused: strong monotonicity improves everywhere.
  strictMono hle hne _ := h.strictMono hle hne

/-- **Boundary avoidance** (interior-valued upper contours). On a commodity space `ι → ℝ`: Any
bundle at least as good as a strictly-positive bundle is itself strictly positive, so the upper
contour set of an interior point avoids the boundary of the orthant. Cobb–Douglas and CES satisfy
it (a bundle with a zero coordinate has utility `0`, strictly below any interior bundle's positive
utility). Combined with strictly positive wealth it forces the demanded bundle into the interior. -/
structure BoundaryAvoiding {ι : Type*} (R : PreferenceRel (ι → ℝ)) : Prop where
  pos_of_ge_pos : ∀ {x z : ι → ℝ}, (∀ l, 0 < z l) → (x ≽[R] z) → ∀ l, 0 < x l

/-- **Desirability of goods.** Monotone improvement holds at any bundle weakly preferred to some
strictly-positive bundle: If `x ≽ z` with `z ≫ 0` and `y` dominates `x` (`x ≤ y`, `x ≠ y`), then
`y ≻ x`. This is the free-good-exclusion interface behind positive equilibrium prices. Both strong
monotonicity (`StrictMonotonePreference.toDesirable`) and boundary avoidance with interior
monotonicity (`BoundaryAvoiding.toDesirable`) furnish it. -/
structure Desirable {ι : Type*} (R : PreferenceRel (ι → ℝ)) : Prop where
  improve : ∀ {x y z : ι → ℝ}, (∀ l, 0 < z l) → (x ≽[R] z) → x ≤ y → x ≠ y → y ≻[R] x

/-- Strong monotonicity gives desirability. -/
lemma StrictMonotonePreference.toDesirable {ι : Type*} {R : PreferenceRel (ι → ℝ)}
    (h : StrictMonotonePreference R) : Desirable R where
  -- The interior witness `z ≫ 0` and `x ≽ z` are unused: strong monotonicity improves everywhere.
  improve _ _ hle hne := h.strictMono hle hne

/-- Boundary avoidance plus interior monotonicity gives desirability. -/
lemma BoundaryAvoiding.toDesirable {ι : Type*} {R : PreferenceRel (ι → ℝ)}
    (hba : BoundaryAvoiding R) (hmono : StrictMonoToInterior R) : Desirable R where
  improve hz hxz hle hne :=
    hmono.strictMono hle hne (fun l => lt_of_lt_of_le (hba.pos_of_ge_pos hz hxz l) (hle l))

/-- Lattice-domain preference interface, used by Topkis–Veinott style arguments: If both `x` and
`y` are at least as good as `z`, then so are `x ⊔ y` and `x ⊓ y`. -/
structure LatticePreference {X : Type*} [Lattice X] (R : PreferenceRel X) : Prop where
  upper_closed_sup_inf :
    ∀ x y z : X, PreferenceRel.le R x z → PreferenceRel.le R y z →
      PreferenceRel.le R (x ⊔ y) z ∧ PreferenceRel.le R (x ⊓ y) z

end Econlib.Preferences
