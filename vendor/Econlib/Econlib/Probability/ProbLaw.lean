/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Basic

/-!
# `ProbLaw` — the semantic spine for probability carriers

`ProbLaw D α` records that a type `D` represents a probability law over the measurable space `α`,
via a canonical embedding `toProbDist : D → ProbDist α`. It is the unifying interface across the
concrete carriers (`FinDist`, `CountDist`, `ContDist`, `MixedDist`, `SupportedProbDist`): Semantic
results — stochastic orders, support, weak-* topology, anything stated about the measure — are
proved once on `ProbDist` and transferred to every carrier through `toProbDist`.

## Main definitions

* `ProbLaw`: A type carrying a canonical embedding into `ProbDist α`.
* `ProbLaw.expect`: Expectation taken via the canonical law.

## Notes

The class deliberately does not rehome the computational operations (`expect`, `map`, `bind`).
Those stay native to each carrier (finite sums, tsums, density integrals) so the lightweight
discrete carriers need not depend on the measure-theoretic stack; each carrier instead supplies
coherence lemmas identifying its native operation with the measure-theoretic one in its bridge
module.

## Tags

probability, probability law, expectation
-/

@[expose] public section

open MeasureTheory

namespace Econlib.Probability

/-- A type `D` is a probability law over a measurable space `α` when it has a canonical embedding
into `ProbDist α`. The semantic spine of the probability API. -/
class ProbLaw (D : Type*) (α : outParam Type*) [MeasurableSpace α] where
  /-- The canonical probability measure represented by an element of `D`. -/
  toProbDist : D → ProbDist α

namespace ProbLaw

variable {D : Type*} {α : Type*} [MeasurableSpace α] [ProbLaw D α]

/-- Semantic expectation of `f` under `d`, taken via its canonical law. Each carrier supplies its
own computational `expect` together with a coherence lemma identifying it with this one. -/
noncomputable def expect (d : D) (f : α → ℝ) : ℝ :=
  (toProbDist d).expect f

/-- The expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg (d : D) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ProbLaw.expect d f :=
  ProbDist.expect_nonneg _ _ hf

end ProbLaw

/-- `ProbDist` is its own law: The spine instance. -/
instance (α : Type*) [MeasurableSpace α] : ProbLaw (ProbDist α) α where
  toProbDist := id

end Econlib.Probability
