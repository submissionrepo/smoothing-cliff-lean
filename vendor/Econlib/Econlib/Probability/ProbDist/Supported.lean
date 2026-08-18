/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Support
public import Econlib.Probability.ProbLaw

/-!
# `SupportedProbDist s` — a probability law bundled with its support

`SupportedProbDist s` bundles a real probability law together with the invariant that it is
supported on `s` (`d.toMeasure s = 1`), so that support-sensitive APIs (convex order, Strassen,
compact-support persuasion) obtain the integrability and mean helpers with no side condition, and a
law unsupported on `s` is inexpressible at the type level.

The support set is a parameter `s : Set ℝ`, so the bundle is uniform across compact intervals,
half-lines, and finite supports. The bare `ProbDist.supportsOn` predicate remains the underlying
definition for support-generic statements.

## Main definitions

* `SupportedProbDist s` — a real probability law together with a proof it is supported on `s`.
* `SupportedProbDist.expect` — expectation under the bundled law.
* `SupportedProbDist.widen` — widen the recorded support along `s ⊆ t`.
* `SupportedProbDist.dirac` — point mass at a point of `s`.

## Main statements

* `SupportedProbDist.integrable_of_continuousOn`, `SupportedProbDist.integrable_id` — integrability
  on a compact-interval support without a side hypothesis.
* `SupportedProbDist.expect_id_mem_Icc` — the mean of a law supported on `[a, b]` lies in `[a, b]`.

## Tags

probability distribution, support, probability measure, expectation
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- A real probability law together with the fact that it is supported on `s`. -/
structure SupportedProbDist (s : Set ℝ) where
  /-- The underlying probability law. -/
  law : ProbDist ℝ
  /-- The law is supported on `s`. -/
  supported : law.supportsOn s

namespace SupportedProbDist

variable {s t : Set ℝ}

instance : ProbLaw (SupportedProbDist s) ℝ where
  toProbDist d := d.law

@[simp] lemma toProbDist_eq (d : SupportedProbDist s) : ProbLaw.toProbDist d = d.law := rfl

/-- Expectation of `f` under the bundled law. -/
noncomputable def expect (d : SupportedProbDist s) (f : ℝ → ℝ) : ℝ := d.law.expect f

@[simp] lemma expect_eq (d : SupportedProbDist s) (f : ℝ → ℝ) : d.expect f = d.law.expect f := rfl

/-- Widen the recorded support: A law supported on `s` is supported on any `t ⊇ s`. -/
def widen (hst : s ⊆ t) (d : SupportedProbDist s) : SupportedProbDist t :=
  ⟨d.law, d.law.supportsOn_mono hst d.supported⟩

@[simp] lemma widen_law (hst : s ⊆ t) (d : SupportedProbDist s) : (d.widen hst).law = d.law := rfl

/-- A continuous statistic is integrable on a compact-interval support — no side hypothesis. -/
lemma integrable_of_continuousOn {a b : ℝ} (d : SupportedProbDist (Icc a b)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : Integrable f d.law.toMeasure :=
  ProbDist.integrable_of_supportsOn_Icc d.supported hf

lemma integrable_id {a b : ℝ} (d : SupportedProbDist (Icc a b)) :
    Integrable id d.law.toMeasure :=
  ProbDist.integrable_id_of_supportsOn_Icc d.supported

/-- The mean of a law supported on `[a, b]` lies in `[a, b]` — no side hypothesis. -/
lemma expect_id_mem_Icc {a b : ℝ} (d : SupportedProbDist (Icc a b)) :
    d.expect id ∈ Icc a b :=
  ProbDist.expect_mem_Icc d.supported

/-- Point mass at a point of the support. -/
noncomputable def dirac {s : Set ℝ} (hs : MeasurableSet s) {x : ℝ} (hx : x ∈ s) :
    SupportedProbDist s :=
  ⟨ProbDist.dirac x, ProbDist.supportsOn_dirac hs hx⟩

end SupportedProbDist

end Econlib.Probability
