/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbLaw
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# `CountDist α` — probability distribution over a countable type

`CountDist α` is a probability mass function over an `[Encodable α]` whose masses are nonnegative
and sum (as a `tsum`) to one. This file collects the core structure, the bridges to Mathlib's `PMF`
and Econlib's measure-theoretic `ProbDist`, and the expectation/variance operators.

## Main definitions

* `CountDist` — a pmf `α → ℝ` that is nonnegative with `∑' a, pmf a = 1`.
* `CountDist.toPMF`, `CountDist.ofPMF` — conversions to/from Mathlib's `PMF`.
* `CountDist.toProbDist` — embedding as a probability measure.
* `CountDist.IsMode` — the probability mass is maximized at an outcome.
* `CountDist.expect`, `CountDist.variance` — expectation and variance.

## Main statements

* `CountDist.summable_pmf` — the pmf is summable.
* `CountDist.expect_eq_probDist_expect` — compatibility with `ProbDist.expect`.

## Tags

probability, countable distributions, pmf, expectation
-/

@[expose] public section

open BigOperators MeasureTheory

namespace Econlib.Probability

/-- A probability distribution over a countable type. -/
structure CountDist (α : Type*) [Encodable α] where
  /-- Probability mass assigned to each outcome. -/
  pmf : α → ℝ
  /-- Probability masses are nonnegative. -/
  nonneg : ∀ a, 0 ≤ pmf a
  /-- Total probability mass is one. -/
  tsum_one : ∑' a, pmf a = 1

namespace CountDist

variable {α : Type*} [Encodable α]

/-- Coercion allowing `d a` syntax for probability evaluation. -/
instance : CoeFun (CountDist α) (fun _ => α → ℝ) where
  coe d := d.pmf

/-- Two countable distributions are equal when their probability masses agree pointwise. -/
@[ext]
lemma ext (d₁ d₂ : CountDist α)
    (h : ∀ a, d₁.pmf a = d₂.pmf a) : d₁ = d₂ := by
  cases d₁
  cases d₂
  congr
  exact funext h

/-- The probability mass function of a `CountDist` is summable. -/
lemma summable_pmf (d : CountDist α) : Summable d.pmf := by
  by_contra h
  have hone := d.tsum_one
  simp [tsum_eq_zero_of_not_summable h] at hone

/-! ### Bridges to `PMF` and `ProbDist` -/

/-- Bridge to Mathlib's `PMF`. -/
noncomputable def toPMF (d : CountDist α) : PMF α where
  val a := ENNReal.ofReal (d.pmf a)
  property := by
    have htsum : ∑' a, ENNReal.ofReal (d.pmf a) = 1 := by
      rw [← ENNReal.ofReal_one, ← d.tsum_one,
        ENNReal.ofReal_tsum_of_nonneg d.nonneg d.summable_pmf]
    rw [← htsum]
    exact ENNReal.summable.hasSum

/-- Bridge from Mathlib's `PMF`. -/
noncomputable def ofPMF (p : PMF α) : CountDist α where
  pmf a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  tsum_one := by
    have hne : ∀ a, p a ≠ ⊤ := fun a => PMF.apply_ne_top p a
    rw [← ENNReal.tsum_toReal_eq hne, PMF.tsum_coe]
    simp

/-- Converting a `PMF` to a `CountDist` and back recovers the original `PMF`. -/
lemma toPMF_ofPMF (p : PMF α) :
    (ofPMF p).toPMF = p := by
  ext a
  simp only [toPMF, ofPMF]
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a))

/-- Embed `CountDist α` into `ProbDist α` via the PMF bridge. -/
noncomputable def toProbDist [MeasurableSpace α]
    (d : CountDist α) : ProbDist α :=
  ⟨d.toPMF.toMeasure, PMF.toMeasure.isProbabilityMeasure d.toPMF⟩

@[simp] lemma toProbDist_toMeasure [MeasurableSpace α]
    (d : CountDist α) : (d.toProbDist : Measure α) = d.toPMF.toMeasure := rfl

/-- `CountDist` is a probability law via its `toProbDist` embedding. -/
noncomputable instance instProbLaw [MeasurableSpace α] :
    ProbLaw (CountDist α) α where
  toProbDist := CountDist.toProbDist

/-- `a` is a mode of `d`: The probability mass is maximized at `a`. A mode need not be unique. -/
def IsMode (d : CountDist α) (a : α) : Prop :=
  ∀ b, d.pmf b ≤ d.pmf a

/-! ### Expectation and variance -/

/-- Expected value for a countable distribution, the `tsum` `∑' a, d.pmf a * f a`.

This equals the mathematical expectation `E_d[f]` exactly when `fun a => d.pmf a * f a` is
`Summable`, and silently returns `0` when it is not (the convention of `tsum`). Lemmas whose
conclusions fail without summability carry the corresponding `Summable`/`Integrable` hypotheses;
`expect_eq_probDist_expect` identifies this with `ProbDist.expect` under `Integrable`. -/
noncomputable def expect (d : CountDist α) (f : α → ℝ) : ℝ :=
  ∑' a, d.pmf a * f a

/-- Variance for a countable distribution. Inherits the `tsum` convention of `expect`: It equals
the mathematical variance when the relevant first and second moments are summable. -/
noncomputable def variance (d : CountDist α) (f : α → ℝ) : ℝ :=
  d.expect (fun a => (f a)^2) - (d.expect f)^2

/-- `expect` unfolds to the `tsum` of mass times value. -/
lemma expect_eq_tsum (d : CountDist α) (f : α → ℝ) :
    d.expect f = ∑' a, d.pmf a * f a := rfl

/-- `CountDist.expect` agrees with `ProbDist.expect` under embedding. -/
lemma expect_eq_probDist_expect [MeasurableSpace α]
    [MeasurableSingletonClass α] (d : CountDist α) (f : α → ℝ)
    (hf : Integrable f d.toProbDist.toMeasure) :
    d.expect f = d.toProbDist.expect f := by
  simp only [CountDist.expect, ProbDist.expect, toProbDist_toMeasure]
  rw [PMF.integral_eq_tsum _ _ hf]
  congr 1
  ext a
  rw [smul_eq_mul, show (d.toPMF a).toReal = d.pmf a from ENNReal.toReal_ofReal (d.nonneg a)]

end CountDist

end Econlib.Probability
