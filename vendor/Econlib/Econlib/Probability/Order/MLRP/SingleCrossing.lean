/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Geometry.SingleCrossing
public import Econlib.Probability.Order.MLRP.FOSD

/-!
# Strict MLRP ⇒ single-crossing of interim payoffs

Strict MLRP of a signal family, combined with strict increasing differences of the underlying
payoff `u`, transports strict increasing differences — and hence the **single-crossing** property —
to the interim objective `θ ↦ ∫ (d θ).density t * u t x`. This is the Milgrom-style bridge used in
mechanism-design arguments (Milgrom 1981).

## Main statements

* `HasStrictMLRP.strictIncreasingDifferences` — strict MLRP transports strict increasing
  differences through expectation.
* `HasStrictMLRP.singleCrossing` — the cardinal single-crossing form of the interim objective.
* `HasStrictMLRP.singleCrossingRel` — the ordinal, relation-level single-crossing form.

## References

* Milgrom, Paul R. 1981. “Good News and Bad News: Representation Theorems and Applications.” *The
  Bell Journal of Economics* 12 (2): 380. [https://doi.org/10.2307/3003562](https://doi.org/10.2307/3003562).

## Tags

monotone likelihood ratio, mlrp, single-crossing, increasing differences
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

namespace HasStrictMLRP

/-- Strict MLRP transports strict increasing differences through expectation.

If `u` has strict increasing differences in `(t, x)`, then the expected payoff
`θ ↦ ∫ (d θ).density t * u t x` has strict increasing differences in `(θ, x)`. -/
theorem strictIncreasingDifferences
    (d : ℝ → ContDist) {u : ℝ → ℝ → ℝ}
    (hMlrp : HasStrictMLRP d)
    (hInt : ∀ θ x, Integrable (fun t => (d θ).density t * u t x))
    (hIncr : Econlib.Preferences.StrictIncreasingDifferences u)
    (hPos : ∀ θ, ∃ a b, a < b ∧ ∀ t ∈ Set.Ioo a b, 0 < (d θ).density t) :
    Econlib.Preferences.StrictIncreasingDifferences
      (fun θ x => ∫ t, (d θ).density t * u t x) where
  strict_incr_diff θ₁ θ₂ x₁ x₂ hθ hx := by
    let g : ℝ → ℝ := fun t => u t x₂ - u t x₁
    have hG : StrictMono g := fun t₁ t₂ ht => hIncr.strict_incr_diff t₁ t₂ x₁ x₂ ht hx
    have hIntDiff : ∀ θ, Integrable (fun t => (d θ).density t * g t) := by
      intro θ
      simpa [g, mul_sub] using (hInt θ x₂).sub (hInt θ x₁)
    have hDiff :
        ∀ θ, (∫ t, (d θ).density t * u t x₂) - (∫ t, (d θ).density t * u t x₁) =
          (d θ).expect g := by
      intro θ
      simp only [ContDist.expect]
      rw [← integral_sub (hInt θ x₂) (hInt θ x₁)]
      simp only [g, mul_sub]
    linarith [hDiff θ₁, hDiff θ₂,
      hMlrp.expectStrictMono g hG hθ (hIntDiff θ₁) (hIntDiff θ₂) (hPos θ₁)]

/-- Strict MLRP and strict increasing differences imply single-crossing of expected payoffs.

This is the Milgrom-style bridge used in mechanism-design arguments: MLRP of signals plus
increasing differences of primitives yields single-crossing of the interim objective. -/
theorem singleCrossing
    (d : ℝ → ContDist) {u : ℝ → ℝ → ℝ}
    (hMlrp : HasStrictMLRP d)
    (hInt : ∀ θ x, Integrable (fun t => (d θ).density t * u t x))
    (hIncr : Econlib.Preferences.StrictIncreasingDifferences u)
    (hPos : ∀ θ, ∃ a b, a < b ∧ ∀ t ∈ Set.Ioo a b, 0 < (d θ).density t) :
    Econlib.Preferences.CardinalSingleCrossing
      (fun θ x => ∫ t, (d θ).density t * u t x) :=
  (hMlrp.strictIncreasingDifferences d hInt hIncr hPos).toCardinalSingleCrossing

/-- Strict MLRP and increasing differences also imply ordinal relation-level single crossing for
the induced expected-payoff preferences. -/
theorem singleCrossingRel
    (d : ℝ → ContDist) {u : ℝ → ℝ → ℝ}
    (hMlrp : HasStrictMLRP d)
    (hInt : ∀ θ x, Integrable (fun t => (d θ).density t * u t x))
    (hIncr : Econlib.Preferences.StrictIncreasingDifferences u)
    (hPos : ∀ θ, ∃ a b, a < b ∧ ∀ t ∈ Set.Ioo a b, 0 < (d θ).density t) :
    Econlib.Preferences.SingleCrossingRel
      (fun θ => Econlib.Preferences.preferenceOfRealUtility
        (fun x => ∫ t, (d θ).density t * u t x)) :=
  (hMlrp.singleCrossing d hInt hIncr hPos).toSingleCrossingRel

end HasStrictMLRP

end Econlib.Probability
