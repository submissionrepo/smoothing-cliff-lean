/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith

/-!
# Quasilinear utility

The standard **quasilinear** utility `u(x, m) = v(x) + m` over a non-monetary outcome `x` and a
monetary transfer `m`. This is a cardinal utility object: Transfers enter linearly with constant
unit marginal utility, so the API is useful for mechanism design and models with monetary transfers.

The non-monetary good ranges over an arbitrary type `X`, so the same primitive serves both the
single-good `X = ℝ` form and the abstract-outcome form used in mechanism design (where `X` is a
finite outcome space and the valuation `v` is the agent's type-conditional value of an outcome).

## Main definitions

* `QuasilinearUtility X` — a quasilinear utility, carrying the valuation function `v : X → ℝ` over
  the non-monetary good.
* `QuasilinearUtility.u` — the full utility `u(x, m) = v(x) + m`.

## Main statements

* `QuasilinearUtility.transfer_utility_increment` — a money transfer `Δ` changes utility by exactly
  `Δ`, independent of the non-monetary level.

## Tags

quasilinear, transferable utility, numeraire, mechanism design
-/

@[expose] public section

namespace Econlib.Preferences

/-- **Quasilinear utility** over a non-monetary outcome `x : X` and a monetary transfer `m : ℝ`.
The utility is `v(x) + m`, where `v : X → ℝ` is the valuation function over the non-monetary good.
The single-good case is `X = ℝ`. -/
structure QuasilinearUtility (X : Type*) where
  /-- The valuation function over the non-monetary good. -/
  v : X → ℝ

namespace QuasilinearUtility

variable {X : Type*}

/-- The full utility function: `u(x, m) = v(x) + m`. -/
def u (q : QuasilinearUtility X) (x : X) (m : ℝ) : ℝ := q.v x + m

variable (q : QuasilinearUtility X)

@[simp] lemma u_def (x : X) (m : ℝ) : q.u x m = q.v x + m := rfl

/-- Two outcome–transfer pairs are utility-indifferent exactly when the valuation gap is offset by
the transfer gap: `u(x₁, m₁) = u(x₂, m₂) ↔ v(x₁) - v(x₂) = m₂ - m₁`. -/
lemma transfer_equiv (x₁ x₂ : X) (m₁ m₂ : ℝ) :
    q.u x₁ m₁ = q.u x₂ m₂ ↔ q.v x₁ - q.v x₂ = m₂ - m₁ := by
  dsimp [u]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- The utility increment from a money transfer `Δ` equals `Δ`, independent of the non-monetary
level `x`: Transfers enter `u` linearly with unit marginal utility (constant marginal utility of
the numeraire). -/
lemma transfer_utility_increment (x : X) (m Δ : ℝ) :
    q.u x (m + Δ) - q.u x m = Δ := by
  dsimp [u]
  ring

end QuasilinearUtility

end Econlib.Preferences
