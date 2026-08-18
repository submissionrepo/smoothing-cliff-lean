/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic
public import Econlib.Preferences.Geometry.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Local nonsatiation

`LocallyNonsatiated C R` says that arbitrarily close to any bundle of the consumption set `C` there
is a strictly preferred bundle that is itself in `C`. It is the preference-regularity hypothesis
behind budget-binding and the first welfare theorem.

## Main definitions

* `LocallyNonsatiated` — local nonsatiation of a preference relative to a consumption set.

## Main statements

* `locallyNonsatiated_nonnegOrthant_of_strictMonoToInterior` — strict monotonicity toward interior
  bundles makes a preference locally nonsatiated on the nonnegative orthant.

## Notes

The consumption-set parameter `C` is essential: Budget-binding needs a nearby strictly better
feasible bundle (e.g. in the nonnegative orthant), not merely a point of the ambient space. This is
the Mas-Colell, Whinston, and Green formulation (Definition 3.B.3), relative to the consumption
set. The predicate is stated on a single `PreferenceRel` over a seminormed space rather than on a
whole economy, so that every consumer shares one definition and the continuum and finite economies
inherit the same lemmas.

## Tags

local nonsatiation, preferences, consumption set, first welfare theorem
-/

@[expose] public section

namespace Econlib.Preferences

/-- **Local nonsatiation** on a consumption set `C`: Within every neighborhood of every bundle of
`C` there is a strictly preferred bundle that is itself in `C`. -/
structure LocallyNonsatiated {E : Type*} [SeminormedAddCommGroup E] (C : Set E)
    (R : PreferenceRel E) : Prop where
  /-- For every `x ∈ C` and radius `ε > 0` there is a strictly preferred `y ∈ C` within `ε`. -/
  exists_better_nearby :
    ∀ x ∈ C, ∀ ε : ℝ, 0 < ε → ∃ y ∈ C, ‖y - x‖ < ε ∧ (y ≻[R] x)

/-- **Local nonsatiation from strict monotonicity toward interior bundles.** On a finite-good
commodity space `ι → ℝ`, a preference satisfying `StrictMonoToInterior` is locally nonsatiated on
the nonnegative orthant. This covers both strongly-monotone (linear) and boundary-flat
(Cobb–Douglas) consumers. -/
theorem locallyNonsatiated_nonnegOrthant_of_strictMonoToInterior
    {ι : Type*} [Fintype ι] [Nonempty ι] {R : PreferenceRel (ι → ℝ)}
    (hmono : StrictMonoToInterior R) :
    LocallyNonsatiated {x : ι → ℝ | ∀ l, 0 ≤ x l} R where
  exists_better_nearby x hx ε hε := by
    refine ⟨fun l => x l + ε / 2, fun l => by have := hx l; linarith, ?_, ?_⟩
    · have hsub : (fun l => x l + ε / 2) - x = fun _ : ι => ε / 2 := by funext l; simp
      rw [hsub, pi_norm_const, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · refine hmono.strictMono (fun l => by simp; linarith) ?_ (fun l => by have := hx l; linarith)
      intro heq
      have := congrFun heq (Classical.arbitrary ι)
      linarith

end Econlib.Preferences
