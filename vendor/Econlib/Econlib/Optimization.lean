/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Econlib.Optimization.ComparativeStatics.MonotoneSelection
public import Econlib.Optimization.ComparativeStatics.Value
public import Econlib.Optimization.Constrained.Duality
public import Econlib.Optimization.Constrained.KKT
public import Econlib.Optimization.Constrained.KKTFirstOrder
public import Econlib.Optimization.Constrained.Problem
public import Econlib.Optimization.Constrained.Sensitivity
public import Econlib.Optimization.Constrained.Slater
public import Econlib.Optimization.DynamicProgramming.Budget.ConsumptionSavingsDP
public import Econlib.Optimization.DynamicProgramming.Budget.OptionValueDP
public import Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetDP
public import Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetWeighted
public import Econlib.Optimization.DynamicProgramming.Concavity.BenvenisteScheinkman
public import Econlib.Optimization.DynamicProgramming.Concavity.ClosedInvariantSet
public import Econlib.Optimization.DynamicProgramming.Concavity.ConcavityPreservation
public import Econlib.Optimization.DynamicProgramming.Core.Bellman
public import Econlib.Optimization.DynamicProgramming.Core.BellmanOperator
public import Econlib.Optimization.DynamicProgramming.Core.EndogenousChain
public import Econlib.Optimization.DynamicProgramming.Core.MDP
public import Econlib.Optimization.DynamicProgramming.Core.Optimality
public import Econlib.Optimization.DynamicProgramming.Core.ParametricDP
public import Econlib.Optimization.DynamicProgramming.Core.Regularity
public import Econlib.Optimization.DynamicProgramming.Core.Stochastic
public import Econlib.Optimization.DynamicProgramming.Core.UnboundedOptimality
public import Econlib.Optimization.DynamicProgramming.Core.Weighted
public import Econlib.Optimization.Envelope
public import Econlib.Optimization.FirstOrder
public import Econlib.Optimization.MaximumTheorem
public import Econlib.Optimization.OptimalTransport.AtomicDense
public import Econlib.Optimization.OptimalTransport.Atomization
public import Econlib.Optimization.OptimalTransport.CTransform
public import Econlib.Optimization.OptimalTransport.Coupling
public import Econlib.Optimization.OptimalTransport.Discretization
public import Econlib.Optimization.OptimalTransport.Duality
public import Econlib.Optimization.OptimalTransport.DualityFinite
public import Econlib.Optimization.OptimalTransport.KRSignedMeasure
public import Econlib.Optimization.OptimalTransport.KantorovichRubinstein
public import Econlib.Optimization.OptimalTransport.LipschitzDual
public import Econlib.Optimization.OptimalTransport.TransportCost
public import Econlib.Optimization.OptimalTransport.UpperLipschitzEnvelope

/-!
# Optimization library

This module collects Econlib's optimization API. It exposes unconstrained and constrained
optimization primitives, maximum and envelope theorems, monotone comparative statics, dynamic
programing, and optimal-transport duality tools used throughout the economic applications.

## Main topics

* Core optimization: Argmax sets, first-order conditions, maximum theorem, and envelope/Danskin
  consequences.
* Constrained optimization: KKT conditions, Slater condition, strong duality, sensitivity, and
  first-order sufficient conditions.
* Dynamic programing: Bellman operators, value iteration, weighted and unbounded fixed points,
  concavity preservation, parametric and stochastic-budget formulations, the canonical
  consumption–savings layer (`DynamicProgramming/Budget/ConsumptionSavingsDP`), and endogenous
  Markov chains. Named economic models built on this layer (collateral, insurance) live in
  `Applications.Models`.
* Optimal transport: Couplings, cost, Kantorovich-Rubinstein duality, signed-measure functionals,
  atomization, discretization, and finite duality.

## Tags

optimization, kkt, envelope theorem, dynamic programing, optimal transport
-/
