/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.LinearAlgebra.AggregateFunctional
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Market-clearing helpers

This file defines scalar aggregate demand, aggregate supply, scalar excess demand, and market
clearing for a single claim or good aggregated by an `AggregateFunctional`. Market clearing is the
equality of aggregate demand and aggregate supply, equivalently zero scalar excess demand.

The file also provides one-dimensional existence statements for continuous excess-demand functions:
A continuous function with opposite endpoint signs has a zero and a parameterized aggregate
excess-demand function with those signs has a clearing parameter.

## Main definitions

* `aggregateDemand`: Aggregate demand for a scalar good via `AggregateFunctional`.
* `aggregateSupply`: Aggregate supply for a scalar good via `AggregateFunctional`.
* `scalarExcessDemand`: Scalar excess demand (demand minus supply).
* `ClearsMarket`: Market-clearing predicate (aggregate demand equals aggregate supply).

## Main statements

* `clearsMarket_iff`, `clearsMarket_iff_excessDemand_eq_zero`: Characterizations of scalar market
  clearing.
* `aggregateDemand_nonneg`, `aggregateSupply_nonneg`: Nonnegative individual quantities have
  nonnegative aggregates.
* `exists_zero_of_continuousOn_excessDemand`: A continuous excess-demand function with a sign
  change has a zero.
* `exists_clearing_parameter_of_continuous_excessDemand`: A continuous aggregate excess-demand
  function with a sign change has a market-clearing parameter.

## Tags

market clearing, excess demand, equilibrium, scalar aggregate
-/

@[expose] public section

open Set

namespace Econlib.Equilibrium

variable {Z : Type*}

/-- Aggregate demand for a scalar claim or good. -/
noncomputable def aggregateDemand (A : AggregateFunctional Z) (demand : Z → ℝ) : ℝ :=
  A.aggregate demand

/-- Aggregate supply for a scalar claim or good. -/
noncomputable def aggregateSupply (A : AggregateFunctional Z) (supply : Z → ℝ) : ℝ :=
  A.aggregate supply

/-- Scalar excess demand. -/
noncomputable def scalarExcessDemand (A : AggregateFunctional Z) (demand supply : Z → ℝ) : ℝ :=
  aggregateDemand A demand - aggregateSupply A supply

/-- Market clearing for a scalar claim or good. -/
def ClearsMarket (A : AggregateFunctional Z) (demand supply : Z → ℝ) : Prop :=
  aggregateDemand A demand = aggregateSupply A supply

/-- Market clearing holds iff aggregate demand equals aggregate supply. -/
lemma clearsMarket_iff
    (A : AggregateFunctional Z) (demand supply : Z → ℝ) :
    ClearsMarket A demand supply ↔ aggregateDemand A demand = aggregateSupply A supply :=
  Iff.rfl

/-- Market clearing is equivalent to zero scalar excess demand. -/
lemma clearsMarket_iff_excessDemand_eq_zero
    (A : AggregateFunctional Z) (demand supply : Z → ℝ) :
    ClearsMarket A demand supply ↔ scalarExcessDemand A demand supply = 0 := by
  unfold ClearsMarket scalarExcessDemand aggregateDemand aggregateSupply
  constructor <;> intro h <;> linarith

/-- Nonnegative individual demand has nonnegative aggregate demand. -/
lemma aggregateDemand_nonneg (A : AggregateFunctional Z) {demand : Z → ℝ}
    (hdemand : ∀ z, 0 ≤ demand z) :
    0 ≤ aggregateDemand A demand :=
  A.aggregate_nonneg demand hdemand

/-- Nonnegative individual supply has nonnegative aggregate supply. -/
lemma aggregateSupply_nonneg (A : AggregateFunctional Z) {supply : Z → ℝ}
    (hsupply : ∀ z, 0 ≤ supply z) :
    0 ≤ aggregateSupply A supply :=
  A.aggregate_nonneg supply hsupply

/-- A continuous scalar excess-demand function with a sign change has a zero. -/
theorem exists_zero_of_continuousOn_excessDemand {a b : ℝ} (hab : a ≤ b)
    {z : ℝ → ℝ} (hz : ContinuousOn z (Icc a b))
    (ha : 0 ≤ z a) (hb : z b ≤ 0) :
    ∃ R ∈ Icc a b, z R = 0 :=
  intermediate_value_Icc' hab hz ⟨hb, ha⟩

/-- A continuous aggregate excess-demand function with endpoint signs has a market-clearing
parameter. -/
theorem exists_clearing_parameter_of_continuous_excessDemand {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → AggregateFunctional Z) (demand supply : ℝ → Z → ℝ)
    (hz : ContinuousOn (fun R => scalarExcessDemand (A R) (demand R) (supply R)) (Icc a b))
    (ha : 0 ≤ scalarExcessDemand (A a) (demand a) (supply a))
    (hb : scalarExcessDemand (A b) (demand b) (supply b) ≤ 0) :
    ∃ R ∈ Icc a b, ClearsMarket (A R) (demand R) (supply R) := by
  obtain ⟨R, hR, hzero⟩ :=
    exists_zero_of_continuousOn_excessDemand hab hz ha hb
  exact ⟨R, hR,
    (clearsMarket_iff_excessDemand_eq_zero (A R) (demand R) (supply R)).mpr hzero⟩

end Econlib.Equilibrium
