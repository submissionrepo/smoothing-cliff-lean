import Mathlib
import Econlib

/-!
# Existence of competitive equilibrium in a finite exchange economy

Unlike the Edgeworth box (where we exhibit the equilibrium and verify it), this example invokes
the library's general **existence theorem** `Economy.exists_equilibrium` on a concrete finite
economy. The theorem's proof is non-constructive — a Kakutani fixed point on the ε-truncated price
simplex, followed by an `ε → 0` limit — so it certifies that an equilibrium exists without naming
a price or allocation.

## The model

Three agents (`Fin 3`), two goods (`Fin 2`), aggregated by the counting sum (`∑ a` — what the
finite `Economy` hard-codes). Each agent `a` has linear / perfect-substitutes preferences
`u_a x = c_a ⬝ᵥ x` with strictly positive coefficients, and owns the strictly positive bundle
`(1, 1)`. Strictly positive coefficients give global strong monotonicity, and strictly positive
endowments give the survival (cheaper-point) condition and McKenzie irreducibility, so the economy
is `RegularEconomy` via `RegularEconomy.ofLinearPrefs` and `exists_equilibrium` applies.

## Main definitions and theorems

* `economy` — the concrete three-agent, two-good exchange economy.
* `economy_regular` — its `RegularEconomy` certificate.
* `finite_economy_has_equilibrium` — **a Walrasian equilibrium exists** (`exists_equilibrium`).
-/

noncomputable section

namespace EconlibExamples.Equilibrium.FiniteExistence

open Econlib.Equilibrium Econlib.Preferences Matrix

/-! ## The economy -/

/-- Per-agent linear preference coefficients (all strictly positive, pairwise distinct tastes). -/
def coef : Fin 3 → Fin 2 → ℝ := ![![2, 1], ![1, 2], ![1, 1]]

/-- Every agent owns one unit of each good (a strictly positive endowment). -/
def endow : Fin 3 → Fin 2 → ℝ := fun _ => ![1, 1]

/-- Every coefficient is strictly positive (linear utilities are strongly monotone). -/
lemma coef_pos : ∀ (a : Fin 3) (l : Fin 2), 0 < coef a l := by
  intro a l; fin_cases a <;> fin_cases l <;> norm_num [coef]

/-- Every endowment coordinate is strictly positive (the survival/cheaper-point condition). -/
lemma endow_pos : ∀ (a : Fin 3) (l : Fin 2), 0 < endow a l := by
  -- The endowment is constant across agents, so `a` is not needed.
  intro _ l; fin_cases l <;> norm_num [endow]

/-- The three-agent, two-good exchange economy with linear preferences and counting aggregation. -/
def economy : Economy 2 where
  Agents := Fin 3
  pref := fun a => preferenceOfRealUtility (fun x => coef a ⬝ᵥ x)
  endow := endow
  endow_mem := fun a l => (endow_pos a l).le

/-! ## Regularity and existence -/

/-- The economy satisfies the convex-existence regularity bundle. -/
lemma economy_regular : RegularEconomy economy :=
  RegularEconomy.ofLinearPrefs economy (fun a => ⟨coef a⟩) coef_pos (fun _ => rfl)
    (fun a hz => by simpa [economy, endow] using congr_fun hz 0)

/-- **A Walrasian equilibrium exists.** Every hypothesis of `Economy.exists_equilibrium` is
discharged: the agent type is nonempty (and finite), the economy is regular (`economy_regular`), it
is McKenzie-irreducible (from the strictly positive endowments, `Irreducible.of_pos_endow`), there
are two goods (`0 < L`), and every good is owned by some agent (`endow_pos`). -/
theorem finite_economy_has_equilibrium : Nonempty economy.WalrasianEquilibrium := by
  haveI : Finite economy.Agents := inferInstanceAs (Finite (Fin 3))
  exact economy.exists_equilibrium (inferInstanceAs (Nonempty (Fin 3))) economy_regular
    (Irreducible.of_pos_endow economy (by norm_num) endow_pos economy_regular.mono) (by norm_num)
    (fun l => ⟨(0 : Fin 3), endow_pos 0 l⟩)

end EconlibExamples.Equilibrium.FiniteExistence

end
