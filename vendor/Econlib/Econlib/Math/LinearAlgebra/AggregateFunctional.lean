/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# Linear aggregation functionals

A measure-free interface for aggregate integration of real-valued functions. The base object is a
positive, additive, homogeneous linear functional `(Z → ℝ) → ℝ` (`PositiveLinearFunctional`); the
unital refinement that also sends the constant `1` to `1` is `AggregateFunctional`. The counting
functional `f ↦ ∑ i, f i` is positive-linear but not unital (`∑ i : Fin I, 1 = I`), while an
averaging functional is unital. Results needing only positivity, additivity and homogeneity are
proved at the `PositiveLinearFunctional` layer and inherited by both; normalization statements
consume unitality.

## Main definitions

* `PositiveLinearFunctional` — a positive linear functional on real-valued statistics.
* `AggregateFunctional` — its unital refinement (`aggregate (fun _ => 1) = 1`).
* `Fintype.countingFunctional` — the non-unital counting functional `f ↦ ∑ i, f i`.
* `PositiveLinearFunctional.eventMass` — the mass of an event via its indicator.
* `PositiveLinearFunctional.Faithful` — no nonzero nonnegative statistic has zero aggregate.

## Main statements

* `PositiveLinearFunctional.aggregate_mono` — aggregation is monotone in the pointwise order.
* `PositiveLinearFunctional.aggregate_finset_sum` — aggregation commutes with finite sums.
* `PositiveLinearFunctional.aggregate_single_pos` — a faithful functional gives every point
  strictly positive mass.
* `Fintype.countingFunctional_faithful` — the counting functional is faithful.

## Notes

`Econlib.Equilibrium.AgentAggregation` packages a `PositiveLinearFunctional` as a typeclass on the
index type.

## Tags

linear functional, aggregation, expectation
-/

@[expose] public section

/-- A positive linear functional on real-valued functions: Positive, additive and homogeneous. It
is not assumed unital, so the finite counting sum is an instance. -/
structure PositiveLinearFunctional (Z : Type*) where
  /-- Aggregate/integrate a real-valued statistic. -/
  aggregate : (Z → ℝ) → ℝ
  /-- Positivity of aggregation. -/
  positive : ∀ f : Z → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ aggregate f
  /-- Additivity. -/
  aggregate_add :
    ∀ f g : Z → ℝ, aggregate (fun z => f z + g z) = aggregate f + aggregate g
  /-- Homogeneity. -/
  aggregate_smul :
    ∀ (c : ℝ) (f : Z → ℝ), aggregate (fun z => c * f z) = c * aggregate f

namespace PositiveLinearFunctional

variable {Z : Type*} (A : PositiveLinearFunctional Z)

/-- Aggregating the zero statistic gives zero. -/
@[simp] theorem aggregate_zero : A.aggregate (fun _ : Z => 0) = 0 := by
  have h := A.aggregate_smul (0 : ℝ) (fun _ : Z => 1)
  simpa using h

/-- Aggregation commutes with negation. -/
@[simp] theorem aggregate_neg (f : Z → ℝ) :
    A.aggregate (fun z => -f z) = -A.aggregate f := by
  have h := A.aggregate_smul (-1 : ℝ) f
  simpa using h

/-- Aggregation commutes with subtraction. -/
theorem aggregate_sub (f g : Z → ℝ) :
    A.aggregate (fun z => f z - g z) = A.aggregate f - A.aggregate g := by
  simp only [sub_eq_add_neg, A.aggregate_add f (fun z => -g z), A.aggregate_neg]

/-- Aggregation commutes with finite sums. -/
theorem aggregate_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Z → ℝ) :
    A.aggregate (fun z => s.sum fun i => f i z) =
      s.sum fun i => A.aggregate (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    calc
      A.aggregate (fun z => (insert a s).sum fun i => f i z)
          = A.aggregate (fun z => f a z + s.sum fun i => f i z) := by
            congr 1
            funext z
            simp [ha]
      _ = A.aggregate (f a) + A.aggregate (fun z => s.sum fun i => f i z) :=
            A.aggregate_add (f a) (fun z => s.sum fun i => f i z)
      _ = (insert a s).sum fun i => A.aggregate (f i) := by
            simp [ha, ih]

/-- Pointwise equal statistics have equal aggregates. -/
theorem aggregate_congr {f g : Z → ℝ} (h : ∀ z, f z = g z) :
    A.aggregate f = A.aggregate g :=
  congrArg A.aggregate (funext h)

/-- A nonnegative statistic has nonnegative aggregate. -/
theorem aggregate_nonneg (f : Z → ℝ) (hf : ∀ z, 0 ≤ f z) :
    0 ≤ A.aggregate f :=
  A.positive f hf

/-- Aggregation is monotone for the pointwise order. -/
theorem aggregate_mono {f g : Z → ℝ} (hfg : ∀ z, f z ≤ g z) :
    A.aggregate f ≤ A.aggregate g := by
  have hnonneg : 0 ≤ A.aggregate (fun z => g z - f z) :=
    A.aggregate_nonneg (fun z => g z - f z) fun z => sub_nonneg.mpr (hfg z)
  have hsub := A.aggregate_sub g f
  linarith

/-- A positive linear functional is **faithful** if every nonnegative statistic with zero aggregate
is identically zero. The finite counting functional is faithful; an atomless continuum average is
not, since a single point has measure zero. -/
def Faithful : Prop :=
  ∀ f : Z → ℝ, (∀ z, 0 ≤ f z) → A.aggregate f = 0 → ∀ z, f z = 0

/-- A faithful functional gives every point strictly positive mass: The aggregate of a unit mass at
`a` is `> 0`. -/
theorem aggregate_single_pos [DecidableEq Z] (hfaith : A.Faithful) (a : Z) :
    0 < A.aggregate (fun z => if z = a then (1 : ℝ) else 0) := by
  have hnn : ∀ z, 0 ≤ (if z = a then (1 : ℝ) else 0) := fun z => by
    by_cases h : z = a <;> simp [h]
  refine lt_of_le_of_ne (A.aggregate_nonneg _ hnn) (fun hz => ?_)
  have hval := hfaith _ hnn hz.symm a
  simp at hval

/-- **Individual-vs-aggregate bound.** For a nonnegative statistic, the value at `a` scaled by
`a`'s unit mass is at most the whole aggregate: `aggregate (𝟙{a}) * f a ≤ aggregate f`. -/
theorem single_mul_le_aggregate [DecidableEq Z] (f : Z → ℝ) (hf : ∀ z, 0 ≤ f z) (a : Z) :
    A.aggregate (fun z => if z = a then (1 : ℝ) else 0) * f a ≤ A.aggregate f := by
  have hsmul : A.aggregate (fun z => f a * (if z = a then (1 : ℝ) else 0))
      = f a * A.aggregate (fun z => if z = a then (1 : ℝ) else 0) := A.aggregate_smul (f a) _
  have hdiff : 0 ≤ A.aggregate (fun z => f z - f a * (if z = a then (1 : ℝ) else 0)) := by
    refine A.aggregate_nonneg _ (fun z => ?_)
    by_cases h : z = a
    · subst h; simp
    · simp [h, hf z]
  rw [A.aggregate_sub, hsmul] at hdiff
  nlinarith [hdiff]

/-- Mass of an event represented by aggregation of its indicator. -/
noncomputable def eventMass (E : Set Z) : ℝ := by
  classical
  exact A.aggregate (fun z => if z ∈ E then 1 else 0)

/-- Event masses are nonnegative. -/
theorem eventMass_nonneg (E : Set Z) : 0 ≤ A.eventMass E := by
  classical
  apply A.aggregate_nonneg
  intro z
  by_cases hz : z ∈ E <;> simp [hz]

end PositiveLinearFunctional

/-- A positive normalized (unital) linear functional: A `PositiveLinearFunctional` that sends the
constant `1` statistic to `1`, i.e. an average or probability functional. -/
structure AggregateFunctional (Z : Type*) extends PositiveLinearFunctional Z where
  /-- Normalization. -/
  aggregate_one : aggregate (fun _ => 1) = 1

namespace AggregateFunctional

variable {Z : Type*} (A : AggregateFunctional Z)

/-- Aggregating a constant statistic returns that constant. -/
@[simp] theorem aggregate_const (c : ℝ) : A.aggregate (fun _ : Z => c) = c := by
  have h := A.aggregate_smul c (fun _ : Z => 1)
  simpa [A.aggregate_one] using h

/-- The whole space has aggregate mass one. -/
@[simp] theorem eventMass_univ : A.eventMass Set.univ = 1 := by
  classical
  simp [PositiveLinearFunctional.eventMass, A.aggregate_one]

end AggregateFunctional

/-- The finite **counting** functional `f ↦ ∑ i, f i`. It is positive-linear but not unital
(`∑ i : Fin I, 1 = I`), so it lives at the `PositiveLinearFunctional` layer. -/
def Fintype.countingFunctional (I : Type*) [Fintype I] : PositiveLinearFunctional I where
  aggregate f := ∑ i, f i
  positive _ hf := Finset.sum_nonneg fun i _ => hf i
  aggregate_add f g := by simp [Finset.sum_add_distrib]
  aggregate_smul c f := by simp [Finset.mul_sum]

/-- The counting functional aggregates a statistic by summing it over the index type. -/
@[simp] theorem Fintype.countingFunctional_aggregate (I : Type*) [Fintype I] (f : I → ℝ) :
    (Fintype.countingFunctional I).aggregate f = ∑ i, f i := rfl

/-- The finite counting functional is faithful: A nonnegative statistic summing to zero is zero
everywhere. -/
theorem Fintype.countingFunctional_faithful (I : Type*) [Fintype I] :
    (Fintype.countingFunctional I).Faithful := by
  intro f hf hsum z
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hf i).1 hsum z (Finset.mem_univ z)
