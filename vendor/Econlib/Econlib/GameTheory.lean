/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.BalancedCore
public import Econlib.GameTheory.Cooperative.Balancedness
public import Econlib.GameTheory.Cooperative.Core
public import Econlib.GameTheory.Cooperative.Game
public import Econlib.GameTheory.Cooperative.Mobius
public import Econlib.GameTheory.Cooperative.Operations
public import Econlib.GameTheory.Cooperative.Shapley
public import Econlib.GameTheory.Cooperative.StrategicBridge
public import Econlib.GameTheory.Cooperative.StrongEquilibrium
public import Econlib.GameTheory.Cooperative.ValueRule
public import Econlib.GameTheory.Equilibrium.Existence
public import Econlib.GameTheory.Equilibrium.Problem
public import Econlib.GameTheory.Equilibrium.Refinement
-- ExtensiveForm/Core: the extensive-form object, strategies, and strategic normalization
public import Econlib.GameTheory.ExtensiveForm.Core.Node
public import Econlib.GameTheory.ExtensiveForm.Core.Tree
public import Econlib.GameTheory.ExtensiveForm.Core.Strategy
public import Econlib.GameTheory.ExtensiveForm.Core.Game
public import Econlib.GameTheory.ExtensiveForm.Core.Reachable
public import Econlib.GameTheory.ExtensiveForm.Core.PureStrategy
public import Econlib.GameTheory.ExtensiveForm.Core.StrategicForm
-- ExtensiveForm/Kuhn: recall predicates and Kuhn's realization-equivalence theorem
public import Econlib.GameTheory.ExtensiveForm.Kuhn.Recall
public import Econlib.GameTheory.ExtensiveForm.Kuhn.PathConsistency
public import Econlib.GameTheory.ExtensiveForm.Kuhn.Maps
public import Econlib.GameTheory.ExtensiveForm.Kuhn.PerfectRecall
public import Econlib.GameTheory.ExtensiveForm.Kuhn.Forward
public import Econlib.GameTheory.ExtensiveForm.Kuhn.Converse
-- ExtensiveForm/Refinements: belief systems, PBE, sequential equilibrium, OSDP
public import Econlib.GameTheory.ExtensiveForm.Refinements.BeliefSystem
public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE
public import Econlib.GameTheory.ExtensiveForm.Refinements.SequentialEquilibrium
public import Econlib.GameTheory.ExtensiveForm.Refinements.ReachInvariance
public import Econlib.GameTheory.ExtensiveForm.Refinements.ReachCoherent
public import Econlib.GameTheory.ExtensiveForm.Refinements.BeliefTower
public import Econlib.GameTheory.ExtensiveForm.Refinements.OneShotSurgery
public import Econlib.GameTheory.ExtensiveForm.Refinements.NextStopFrontier
public import Econlib.GameTheory.ExtensiveForm.Refinements.OneShotDeviation
public import Econlib.GameTheory.ExtensiveForm.Refinements.ConsistentBeliefs
-- ExtensiveForm/PerfectInfoTree: perfect-information backward induction
public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.Tree
public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.BackwardInduction
public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.OneShot
public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.SPE
public import Econlib.GameTheory.Repeated.Basic
public import Econlib.GameTheory.Repeated.GrimTrigger
public import Econlib.GameTheory.Repeated.OneShotDeviation
public import Econlib.GameTheory.Signaling.Basic
public import Econlib.GameTheory.Signaling.Bridge.Assessment
public import Econlib.GameTheory.Signaling.Bridge.Existence
public import Econlib.GameTheory.Signaling.Bridge.GameTree
public import Econlib.GameTheory.Signaling.Bridge.Morphism
public import Econlib.GameTheory.Signaling.Bridge.SequentialEquilibrium
public import Econlib.GameTheory.Signaling.Bridge.StrategicBNE
public import Econlib.GameTheory.Signaling.IntuitiveCriterion
public import Econlib.GameTheory.Signaling.PBE
public import Econlib.GameTheory.Signaling.Perturbation
public import Econlib.GameTheory.Signaling.Pooling
public import Econlib.GameTheory.Signaling.Separating
public import Econlib.GameTheory.Strategic.Basic
public import Econlib.GameTheory.Strategic.Bayesian.Dominant
public import Econlib.GameTheory.Strategic.Bayesian.Game
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Distributional
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.DistributionalRepr
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Existence
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Game
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Interim
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.MixedExtension
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Econlib.GameTheory.Strategic.Bayesian.MixedBNE
public import Econlib.GameTheory.Strategic.Bayesian.PureBNE
public import Econlib.GameTheory.Strategic.Bayesian.TypeDist
public import Econlib.GameTheory.Strategic.Coordination
public import Econlib.GameTheory.Strategic.CorrelatedEquilibrium
public import Econlib.GameTheory.Strategic.Refinements
public import Econlib.GameTheory.Strategic.Symmetric

/-!
# Game theory library

This module collects Econlib's game-theory API. It exposes strategic-form and Bayesian games,
abstract equilibrium problems and existence theorems, cooperative transferable-utility games,
repeated games, signaling games, and finite extensive forms with behavioral strategies,
perfect-recall maps, and refinement concepts.

## Main topics

* Strategic games: Nash equilibrium, correlated equilibrium, refinements, symmetric games, and
  finite or measurable Bayesian games.
* Extensive forms: Game trees, information structures, behavioral and pure strategies, Kuhn
  realization equivalence, perfect-information backward induction, PBE, and sequential equilibrium.
* Signaling games: Assessments, Bayes consistency, PBE, pooling and separating assessments,
  perturbations, the intuitive criterion, and extensive-form embeddings.
* Cooperative games: Core, balancedness, Shapley value, value rules, Mobius inversion, and bridges
  from strategic-form games.

## Tags

game theory, equilibrium, extensive form, signaling game, cooperative game
-/
