/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Monotone comparative statics of optimal effort (Topkis)

This worked example instantiates `OrderedPolicyCertificate.ofStrictIncreasingDifferences`
(`Econlib.Optimization.DynamicProgramming`) on a concrete monotone-comparative-statics problem, and
runs it to its payoff: **the optimal action is monotone in the parameter.**

It is the acceptance test for the ordered-policy certificate. Unlike a bare property bundle, that
certificate ships a constructor that *derives* its monotone-argmax field from Topkis supermodularity
primitives, so instantiating it is cheaper than proving policy monotonicity directly — this file
exercises exactly that constructor and the `choice_monotone` it unlocks.

## The model

An agent with productivity `θ ∈ ℝ` chooses effort `a` from the unit interval `[0, 1]` to maximize

`payoff(θ, a) = θ · a − a²`,

a linear benefit scaled by productivity against a quadratic effort cost. The cross-partial is
`∂²payoff/∂θ∂a = 1 > 0`, so the payoff has strictly increasing differences: a more productive agent
gains strictly more from raising effort. Topkis's theorem then forces the optimal effort to rise in
productivity.

The constructor needs three facts about the model — all easier than the conclusion:

* `payoff` has strictly increasing differences (the supermodularity primitive — a one-line
  `nlinarith` on the cross-difference `(θ₂−θ₁)(a₂−a₁) > 0`);
* the action set `[0, 1]` is nonempty and compact, and `payoff θ` is continuous on it;
* `payoff θ` is strictly concave, so each productivity admits a unique optimal effort.

From these the certificate *derives* the monotone-argmax comparison; `choice_monotone` then reads
off that the selected effort policy is monotone in `θ`.

## Results

* `optimalEffort_monotone` — the selected optimal effort is monotone in productivity (the payoff,
  obtained from the certificate's `choice_monotone`, not assumed);
* `choice_zero` / `choice_two` — the optimal effort is `0` at `θ = 0` and `1` at `θ = 2`, the
  closed forms determined from the unique maximizer (so the policy is not a disguised constant);
* `optimalEffort_strictMono_witness` — and strictly increasing between those parameters,
  certifying the comparative static is non-vacuous.
-/

namespace EconlibExamples.Optimization.MonotoneComparativeStatics

open Set Econlib.Optimization Econlib.Optimization.DynamicProgramming Econlib.Preferences

/-- The productivity–effort payoff: a linear benefit `θ · a` scaled by productivity, net of a
quadratic effort cost `a²`. -/
def payoff (θ a : ℝ) : ℝ := θ * a - a ^ 2

/-- `payoff θ` is strictly concave in effort on the unit interval: the linear benefit `θ · a` is
concave and the quadratic cost `−a²` is strictly concave, so their sum is strictly concave. This
gives a unique optimal effort at each productivity. -/
lemma payoff_strictConcaveOn (θ : ℝ) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (payoff θ) := by
  have hsq : StrictConvexOn ℝ (univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
    Even.strictConvexOn_pow (by norm_num) (by norm_num)
  have hneg : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => -(x ^ 2)) :=
    (hsq.subset (subset_univ _) (convex_Icc 0 1)).neg
  have hlin : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => θ * x) :=
    (LinearMap.lsmul ℝ ℝ θ).concaveOn (convex_Icc 0 1)
  have hsum := hneg.add_concaveOn hlin
  have hfun : payoff θ = (fun x : ℝ => -(x ^ 2)) + (fun x : ℝ => θ * x) := by
    funext a; simp only [payoff, Pi.add_apply]; ring
  rw [hfun]; exact hsum

/-- The ordered-policy certificate for the effort problem, built by the Topkis constructor. The
strictly-increasing-differences field is discharged from the supermodularity primitive
`(θ₂ − θ₁)(a₂ − a₁) > 0`; uniqueness of the maximizer comes from strict concavity. -/
noncomputable def effortCert : OrderedPolicyCertificate ℝ ℝ :=
  OrderedPolicyCertificate.ofStrictIncreasingDifferences
    (u := payoff) (X := Icc (0 : ℝ) 1)
    { strict_incr_diff := fun θ₁ θ₂ x₁ x₂ hθ hx => by
        simp only [payoff]
        nlinarith [mul_pos (sub_pos.mpr hθ) (sub_pos.mpr hx)] }
    (nonempty_Icc.mpr (by norm_num))
    isCompact_Icc
    (fun θ => (by fun_prop : Continuous (fun a : ℝ => θ * a - a ^ 2)).continuousOn)
    (fun θ _ _ ha₁ ha₂ =>
      argmax_subsingleton_of_strictConcaveOn (payoff_strictConcaveOn θ) ha₁ ha₂)

/-- The certificate's selected effort is `sSup` of the (single-valued) argmax. -/
lemma choice_eq (θ : ℝ) :
    effortCert.choice θ = sSup (argmax (payoff θ) (Icc (0 : ℝ) 1)) := rfl

/-- **The optimal effort is monotone in productivity.** This is the certificate's payoff
`choice_monotone`, whose monotone-comparative-statics content was established by the Topkis
constructor — we *derive* it, not assume it. -/
theorem optimalEffort_monotone : Monotone effortCert.choice :=
  effortCert.choice_monotone

/-- The optimal effort at productivity `θ = 0` is `0`: with no benefit, any effort only incurs the
quadratic cost, so the corner `a = 0` is the unique maximizer. -/
theorem choice_zero : effortCert.choice 0 = 0 := by
  have hmax : IsMaxOn (payoff 0) (Icc (0 : ℝ) 1) 0 :=
    isMaxOn_iff.mpr fun a _ => by simp only [payoff]; nlinarith [sq_nonneg a]
  rw [choice_eq, argmax_eq_singleton (payoff_strictConcaveOn 0) (by norm_num [Set.mem_Icc]) hmax,
    csSup_singleton]

/-- The optimal effort at productivity `θ = 2` is `1`: the unconstrained optimum `a = θ/2 = 1` lies
on the boundary of `[0, 1]`, where `2a − a² = 1 − (1 − a)²` is maximized. -/
theorem choice_two : effortCert.choice 2 = 1 := by
  have hmax : IsMaxOn (payoff 2) (Icc (0 : ℝ) 1) 1 :=
    isMaxOn_iff.mpr fun a _ => by simp only [payoff]; nlinarith [sq_nonneg (1 - a)]
  rw [choice_eq, argmax_eq_singleton (payoff_strictConcaveOn 2) (by norm_num [Set.mem_Icc]) hmax,
    csSup_singleton]

/-- **The comparative static is non-vacuous**: optimal effort strictly increases from `θ = 0` to
`θ = 2` (value `0` to `1`), so the monotone policy is state-dependent, not constant. -/
theorem optimalEffort_strictMono_witness : effortCert.choice 0 < effortCert.choice 2 := by
  rw [choice_zero, choice_two]; norm_num

end EconlibExamples.Optimization.MonotoneComparativeStatics
