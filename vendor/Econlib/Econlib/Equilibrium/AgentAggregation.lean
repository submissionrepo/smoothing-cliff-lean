/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.LinearAlgebra.AggregateFunctional

/-!
# Aggregation as a typeclass on the agent space

This file packages aggregation of real-valued statistics over an agent or index type as typeclass
data. An `AgentAggregation Z` supplies a `PositiveLinearFunctional Z`, so consumers can aggregate
functions `Z → ℝ` using only the type `Z` and its available instances.

Finite agent spaces use counting aggregation by default: `AgentAggregation.agg Z f` is the sum
`∑ i, f i` whenever `Z` is a `Fintype`. The separate class `FaithfulAggregation Z` records the
stronger property that a nonnegative statistic with zero aggregate is zero at every point. Results
that need pointwise conclusions from aggregate equalities can require this stronger class.

## Main definitions

* `AgentAggregation` — aggregation of real-valued statistics over the agent space.
* `AgentAggregation.agg` — the aggregation map supplied by the typeclass instance.
* `FaithfulAggregation` — the aggregation functional is faithful.
* `AgentAggregation.instFintype` — finite agent spaces aggregate by counting sum.
* `FaithfulAggregation.instFintype` — finite counting aggregation is faithful.

## Tags

aggregation, agent space, general equilibrium
-/

@[expose] public section

namespace Econlib.Equilibrium

/-- Aggregation of real-valued statistics over the agent space `Z`, via a
`PositiveLinearFunctional` determined by `Z`'s structure. -/
class AgentAggregation (Z : Type*) where
  /-- The underlying positive linear functional. -/
  toPLF : PositiveLinearFunctional Z

/-- The aggregation map of `Z`'s `AgentAggregation` instance. -/
abbrev AgentAggregation.agg (Z : Type*) [inst : AgentAggregation Z] : (Z → ℝ) → ℝ :=
  inst.toPLF.aggregate

/-- An agent aggregation is **faithful** when no nonnegative statistic with zero aggregate is
positive anywhere. Separate from `AgentAggregation` to mark exactly which results need
finiteness/atomicity; the `Fintype` counting instance satisfies this, an atomless-measure instance
does not. -/
class FaithfulAggregation (Z : Type*) [inst : AgentAggregation Z] : Prop where
  /-- The functional is faithful. -/
  faithful : inst.toPLF.Faithful

/-- The finite counting aggregation `f ↦ ∑ i, f i`. High priority so a `Fintype` agent space
resolves to counting by default. -/
instance (priority := high) AgentAggregation.instFintype (Z : Type*) [Fintype Z] :
    AgentAggregation Z := ⟨Fintype.countingFunctional Z⟩

/-- The aggregation map on a `Fintype` agent space is the counting sum `∑ i, f i`. -/
@[simp] lemma AgentAggregation.agg_fintype (Z : Type*) [Fintype Z] (f : Z → ℝ) :
    AgentAggregation.agg Z f = ∑ i, f i := rfl

/-- The finite counting aggregation is faithful. -/
instance FaithfulAggregation.instFintype (Z : Type*) [Fintype Z] : FaithfulAggregation Z :=
  ⟨Fintype.countingFunctional_faithful Z⟩

end Econlib.Equilibrium
