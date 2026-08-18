/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Econlib.Preferences.Geometry.SingleCrossing

/-!
# Monotone-policy certificate for dynamic programing

This module provides `OrderedPolicyCertificate`: A selected policy carrying an ordered-argmax
comparison field, from which `choice_monotone` reads off monotone comparative statics. Unlike a
bare property bundle, it ships a constructor `ofStrictIncreasingDifferences` that *derives* the
ordered-argmax field from supermodularity primitives (Topkis), so instantiating the certificate
costs less than proving monotonicity of the policy directly.

For the bare statement "this policy is optimal," use `argmax` / `IsMaxOn`
(`Econlib.Optimization.Basic`) directly. For a constructive optimal policy with continuous
selection, see `EndogenousPolicyProblem` in
`Econlib.Optimization.DynamicProgramming.Core.EndogenousChain`.

## Main definitions

* `OrderedPolicyCertificate` — a selected policy with an ordered-argmax comparison field.
* `OrderedPolicyCertificate.ofStrictIncreasingDifferences` — builds the certificate from strict
  increasing differences plus pointwise uniqueness of the argmax.

## Main statements

* `OrderedPolicyCertificate.choice_monotone` — the selected policy is monotone in the ordered
  parameter (recombines the stored `ordered_argmax` field).

## Tags

dynamic programing, monotone policy, comparative statics, topkis, milgrom-shannon
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Econlib.Optimization Set

universe u v

/-- A generic selected-policy certificate whose monotonicity follows from an ordered argmax theorem
supplied separately, for example from Topkis or Milgrom-Shannon. -/
structure OrderedPolicyCertificate (Θ : Type u) (Action : Type v)
    [Preorder Θ] [Preorder Action] where
  /-- Feasible action set. -/
  feasible : Θ → Set Action
  /-- Objective indexed by the ordered parameter. -/
  objective : Θ → Action → ℝ
  /-- Selected action. -/
  choice : Θ → Action
  /-- Selected action is feasible. -/
  choice_mem : ∀ θ, choice θ ∈ feasible θ
  /-- Selected action is optimal. -/
  choice_optimal : ∀ θ, IsMaxOn (objective θ) (feasible θ) (choice θ)
  /-- Ordered argmax comparison. -/
  ordered_argmax :
    ∀ ⦃θ₁ θ₂ : Θ⦄, θ₁ ≤ θ₂ →
      ∀ ⦃a₁ a₂ : Action⦄,
        a₁ ∈ argmax (objective θ₁) (feasible θ₁) →
        a₂ ∈ argmax (objective θ₂) (feasible θ₂) →
        a₁ ≤ a₂

namespace OrderedPolicyCertificate

variable {Θ : Type u} {Action : Type v} [Preorder Θ] [Preorder Action]
variable (C : OrderedPolicyCertificate Θ Action)

/-- The selected policy is monotone in the ordered parameter. This recombines the stored
`ordered_argmax`, `choice_mem`, and `choice_optimal` fields; the monotone-comparative-statics
content (e.g. Topkis or Milgrom-Shannon) is supplied when the certificate is built. -/
theorem choice_monotone : Monotone C.choice := by
  intro θ₁ θ₂ hθ
  exact C.ordered_argmax hθ
    ⟨C.choice_mem θ₁, C.choice_optimal θ₁⟩
    ⟨C.choice_mem θ₂, C.choice_optimal θ₂⟩

end OrderedPolicyCertificate

/-! ## Constructor from Topkis primitives

When the objective satisfies `StrictIncreasingDifferences` and the action space `X` is a
nonempty compact subset of `ℝ`, with the additional uniqueness hypothesis that each parameter `θ`
admits a singleton argmax (e.g. delivered by strict concavity of `u θ` in the action), Topkis's
theorem produces an `OrderedPolicyCertificate` directly, with the `ordered_argmax` field
established from the supermodularity hypotheses rather than supplied by the consumer. -/

namespace OrderedPolicyCertificate

open Econlib.Preferences

/-- Build an `OrderedPolicyCertificate` from Topkis-style strict increasing differences plus
pointwise uniqueness of the argmax (the latter is automatic under, e.g., strict concavity of the
objective in the action). -/
noncomputable def ofStrictIncreasingDifferences {Θ : Type u} [LinearOrder Θ]
    {u : Θ → ℝ → ℝ} {X : Set ℝ}
    (h_id : StrictIncreasingDifferences u)
    (h_X_nonempty : X.Nonempty)
    (h_X_compact : IsCompact X)
    (h_u_cont : ∀ θ, ContinuousOn (u θ) X)
    (h_unique : ∀ θ a₁ a₂,
        a₁ ∈ argmax (u θ) X → a₂ ∈ argmax (u θ) X → a₁ = a₂) :
    OrderedPolicyCertificate Θ ℝ where
  feasible := fun _ => X
  objective := u
  choice := fun θ => sSup (argmax (u θ) X)
  choice_mem θ :=
    have hne := argmax_nonempty h_X_compact h_X_nonempty (h_u_cont θ)
    have hcomp := argmax_compact h_X_compact (h_u_cont θ)
    (hcomp.sSup_mem hne).1
  choice_optimal θ :=
    have hne := argmax_nonempty h_X_compact h_X_nonempty (h_u_cont θ)
    have hcomp := argmax_compact h_X_compact (h_u_cont θ)
    (hcomp.sSup_mem hne).2
  ordered_argmax := by
    intro θ₁ θ₂ hθ a₁ a₂ ha₁ ha₂
    rcases eq_or_lt_of_le hθ with heq | hlt
    · -- Same parameter: uniqueness collapses both argmaxes to a single point.
      subst heq
      exact (h_unique θ₁ a₁ a₂ ha₁ ha₂).le
    · -- Strict parameter inequality: standard Topkis monotone-comparison argument.
      by_contra h_not_le
      push Not at h_not_le
      have h_opt₁ : u θ₁ a₂ ≤ u θ₁ a₁ := isMaxOn_iff.mp ha₁.2 a₂ ha₂.1
      have h_opt₂ : u θ₂ a₁ ≤ u θ₂ a₂ := isMaxOn_iff.mp ha₂.2 a₁ ha₁.1
      have h_incr := h_id.strict_incr_diff θ₁ θ₂ a₂ a₁ hlt h_not_le
      linarith

end OrderedPolicyCertificate

end Econlib.Optimization.DynamicProgramming
