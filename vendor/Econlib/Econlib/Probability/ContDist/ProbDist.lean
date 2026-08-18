/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbLaw

/-!
# Bridge: `ContDist` → `ProbDist`

Embeds a continuous distribution into the universal measure-theoretic carrier `ProbDist ℝ` via its
density measure, registers the `ProbLaw` instance, and records the coherence lemma identifying
`ContDist.expect` with `ProbDist.expect`.

## Main definitions

* `ContDist.toProbDist` — the density-measure embedding into `ProbDist ℝ`.
* `ContDist.instProbLaw` — the `ProbLaw` instance.

## Main statements

* `ContDist.expect_eq_probDist_expect` — `ContDist.expect` agrees with `ProbDist.expect`.

## Tags

continuous distribution, probability measure, problaw
-/

@[expose] public section

open MeasureTheory

namespace Econlib.Probability

namespace ContDist

/-- Embed `ContDist` into `ProbDist ℝ` via the density measure. -/
noncomputable def toProbDist (d : ContDist) : ProbDist ℝ :=
  ⟨d.toMeasure, d.toMeasure_isProbability⟩

/-- The measure underlying `d.toProbDist` is `d.toMeasure`. -/
@[simp] lemma toProbDist_toMeasure (d : ContDist) :
    (d.toProbDist : Measure ℝ) = d.toMeasure := rfl

/-- `ContDist.expect` agrees with `ProbDist.expect` under embedding. -/
lemma expect_eq_probDist_expect (d : ContDist) (f : ℝ → ℝ) :
    d.expect f = d.toProbDist.expect f := by
  simp only [ProbDist.expect, toProbDist_toMeasure, expect_eq_measure_integral]

/-- `ContDist` is a probability law via its `toProbDist` embedding. -/
noncomputable instance instProbLaw : ProbLaw ContDist ℝ where
  toProbDist := ContDist.toProbDist

end ContDist

end Econlib.Probability
