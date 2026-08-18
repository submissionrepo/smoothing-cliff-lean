/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Preferences.Utility.CobbDouglas
public import Econlib.Preferences.Utility.Linear

/-!
# Regular economies from explicit utility families

This file provides `RegularEconomy` constructors for economies whose preferences are represented by
common utility families. The constructors turn explicit utility data into the regularity bundle
needed by the general-equilibrium existence and welfare results.

For linear, perfect-substitutes utility (`Preferences.LinearUtility`, `x ↦ c ⬝ᵥ x`), strictly
positive coefficients give continuity, convex preferences, strict monotonicity toward the interior,
and desirability; the economy constructor additionally requires nonzero endowments. For
Cobb-Douglas utility, total utility supplies the same preference-side regularity when there is at
least one commodity; the economy constructor requires strictly positive endowments.

The preference-level regularity facts for the utility families themselves live with the family
definitions in `Econlib.Preferences.Utility` (`LinearUtility`, `CobbDouglasUtility`); this file
only assembles them into `RegularEconomy` bundles.

## Main statements

* `RegularEconomy.ofLinearPrefs`: Regularity for linear-utility economies.
* `RegularEconomy.ofCobbDouglas`: Regularity for Cobb–Douglas economies.

## Tags

equilibrium, regular economy, linear utility, Cobb-Douglas, explicit utility
-/

@[expose] public section

namespace Econlib.Equilibrium

open Matrix Econlib.Preferences

variable {L : ℕ}

/-! ## Linear / perfect-substitutes preferences -/

/-- **Regular economy from linear preferences.** An economy whose agents have linear utility
`lin a` (`Preferences.LinearUtility`, `x ↦ c_a ⬝ᵥ x`) with strictly positive coefficients and
nonzero endowments is regular. -/
theorem RegularEconomy.ofLinearPrefs (E : Economy L)
    (lin : E.Agents → LinearUtility L) (hcoef : ∀ a l, 0 < (lin a).c l)
    (hpref : ∀ a, E.pref a = preferenceOfRealUtility (lin a).u)
    (hendow_ne : ∀ a, E.endow a ≠ 0) : RegularEconomy E := by
  refine
    { contPref := fun a => by
        rw [hpref a]; exact continuousPref_preferenceOfRealUtility (lin a).continuous_u
      convex := fun a => by
        rw [hpref a]; exact (lin a).quasiconcaveOn_u.toConvexPreference
      mono := fun a => by
        rw [hpref a]; exact ((lin a).strictMonotonePreference (hcoef a)).toStrictMonoToInterior
      desirable := fun a => by
        rw [hpref a]; exact ((lin a).strictMonotonePreference (hcoef a)).toDesirable
      endow_ne := hendow_ne }

/-! ## Cobb–Douglas preferences -/

/-- **Regular economy from Cobb–Douglas preferences.** An economy whose agents have total
Cobb–Douglas utility and strictly positive endowments is regular. -/
theorem RegularEconomy.ofCobbDouglas (hL : 0 < L) (E : Economy L)
    (cd : E.Agents → CobbDouglasUtility L)
    (hpref : ∀ a, E.pref a = preferenceOfRealUtility (cd a).uTotal)
    (hendow : ∀ a l, 0 < E.endow a l) : RegularEconomy E := by
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  refine
    { contPref := fun a => by
        rw [hpref a]; exact continuousPref_preferenceOfRealUtility (cd a).uTotal_continuous
      convex := fun a => by rw [hpref a]; exact (cd a).uTotal_quasiconcave.toConvexPreference
      mono := fun a => by rw [hpref a]; exact (cd a).uTotal_strictMonoToInterior
      desirable := fun a => by
        rw [hpref a]
        exact (cd a).uTotal_boundaryAvoiding.toDesirable (cd a).uTotal_strictMonoToInterior
      endow_ne := fun a hzero =>
        (hendow a ⟨0, hL⟩).ne' (congr_fun hzero ⟨0, hL⟩) }

end Econlib.Equilibrium
