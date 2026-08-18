/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Econlib.Probability.FinDist.Expect
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbLaw
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite distributions as probability measures

This file bridges `FinDist` with Mathlib's `PMF`, countable distributions, and Econlib's
measure-theoretic `ProbDist`.

## Main definitions

* `FinDist.toPMF` — convert a finite distribution to a `PMF`.
* `FinDist.ofPMF` — convert a `PMF` on a finite type to a `FinDist`.
* `FinDist.toCountDist` — embed a finite distribution as a countable distribution.
* `FinDist.toProbDist` — embed a finite distribution as a probability measure.
* `ProbDist.toFinDist` — extract a finite distribution from a probability measure on a finite
  measurable space.

## Main statements

* `FinDist.toPMF_ofPMF` — `toPMF` is a left inverse of `ofPMF`.
* `FinDist.expect_eq_probDist_expect` — `FinDist.expect` agrees with `ProbDist.expect` under the
  embedding.

## Notes

`FinDist α` is registered as a `ProbLaw` via its `toProbDist` embedding.

## Tags

probability, finite distributions, probability measures
-/

@[expose] public section

open BigOperators MeasureTheory Finset

namespace Econlib.Probability
namespace FinDist

/-- Bridge to Mathlib's `PMF`. -/
noncomputable def toPMF {α : Type*} [Fintype α] [DecidableEq α] (d : FinDist α) : PMF α where
  val a := ENNReal.ofReal (d.pmf a)
  property := by
    have : HasSum (fun a => ENNReal.ofReal (d.pmf a)) (∑ a, ENNReal.ofReal (d.pmf a)) :=
      hasSum_fintype _
    convert this using 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => d.nonneg a), d.sum_one]; simp

/-- Bridge from Mathlib's `PMF`. -/
noncomputable def ofPMF {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) : FinDist α where
  pmf a := (p a).toReal
  nonneg a := ENNReal.toReal_nonneg
  sum_one := by
    have h1 : ∀ a : α, (p a) ≠ ⊤ :=
      fun a => ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a)
    rw [← ENNReal.toReal_sum (fun a _ => h1 a)]
    have hsum : (∑ a : α, p a) = 1 := by have := p.tsum_coe; rwa [tsum_fintype] at this
    rw [hsum]; simp

/-- Bridge from finite distributions to countable distributions. -/
noncomputable def toCountDist {α : Type*} [Fintype α] [DecidableEq α] [Encodable α]
    (d : FinDist α) : CountDist α where
  pmf := d.pmf
  nonneg := d.nonneg
  tsum_one := by simpa [tsum_fintype] using d.sum_one

/-- `toPMF` is a left inverse of `ofPMF`. -/
lemma toPMF_ofPMF {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) :
    FinDist.toPMF (FinDist.ofPMF p) = p := by
  ext a
  simp only [toPMF, ofPMF]
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a))

/-- Embed `FinDist α` into `ProbDist α` via the PMF bridge. -/
noncomputable def toProbDist {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    (d : FinDist α) : ProbDist α :=
  ⟨d.toPMF.toMeasure, PMF.toMeasure.isProbabilityMeasure d.toPMF⟩

/-- The measure underlying `toProbDist` is the `PMF`-induced measure. -/
@[simp] lemma toProbDist_toMeasure {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    (d : FinDist α) :
    (d.toProbDist : Measure α) = d.toPMF.toMeasure := rfl

/-- `FinDist.expect` agrees with `ProbDist.expect` under embedding. -/
lemma expect_eq_probDist_expect {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (d : FinDist α) (f : α → ℝ) :
    d.expect f = d.toProbDist.expect f := by
  simp only [FinDist.expect, ProbDist.expect, toProbDist_toMeasure]
  rw [PMF.integral_eq_sum]
  congr 1; ext a; rw [smul_eq_mul]
  congr 1
  exact (ENNReal.toReal_ofReal (d.nonneg a)).symm

/-- `FinDist` is a probability law via its `toProbDist` embedding. -/
noncomputable instance instProbLaw {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] :
    ProbLaw (FinDist α) α where
  toProbDist := FinDist.toProbDist

end FinDist

/-- Extract a `FinDist α` from a `ProbDist α` on a finite measurable space. -/
noncomputable def ProbDist.toFinDist {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (d : ProbDist α) : FinDist α where
  pmf a := (d.toMeasure {a}).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := by
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top d.toMeasure {a})]
    have : ∑ a : α, d.toMeasure {a} = d.toMeasure Set.univ := by
      rw [← measure_biUnion_finset]
      · congr 1; ext x; simp
      · intro i _ j _ hij; exact Set.disjoint_singleton.mpr hij
      · intro i _; exact measurableSet_singleton i
    rw [this, measure_univ]; simp

end Econlib.Probability
