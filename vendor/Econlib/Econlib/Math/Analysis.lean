/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ArctanConcave
public import Econlib.Math.Analysis.BetaIntegral
public import Econlib.Math.Analysis.Blackwell
public import Econlib.Math.Analysis.CauchyMVT
public import Econlib.Math.Analysis.ConcaveHingeInterpolation
public import Econlib.Math.Analysis.Concavification1D.ConvexEnvelope
public import Econlib.Math.Analysis.Concavification1D.Defs
public import Econlib.Math.Analysis.Concavification1D.Envelope
public import Econlib.Math.Analysis.Concavification1D.EnvelopeDuality
public import Econlib.Math.Analysis.Concavification1D.OneGapBoundary
public import Econlib.Math.Analysis.Concavification1D.OneGapChord
public import Econlib.Math.Analysis.Convex.ConcaveOn
public import Econlib.Math.Analysis.Convex.FunctionSum
public import Econlib.Math.Analysis.Convex.PerturbedSimplex
public import Econlib.Math.Analysis.Convex.StdSimplex
public import Econlib.Math.Analysis.ConvexBddDerivApprox
public import Econlib.Math.Analysis.ConvexFaces
public import Econlib.Math.Analysis.ConvexRademacher
public import Econlib.Math.Analysis.ConvexReduction
public import Econlib.Math.Analysis.ConvexRightDeriv
public import Econlib.Math.Analysis.Convolution.Preservation
public import Econlib.Math.Analysis.Danskin
public import Econlib.Math.Analysis.EvenPowerConcave
public import Econlib.Math.Analysis.ExtremePointsGDelta
public import Econlib.Math.Analysis.FiniteFenchelMoreau
public import Econlib.Math.Analysis.HingeConvex
public import Econlib.Math.Analysis.ImplicitFunction
public import Econlib.Math.Analysis.IntegralIdentities
public import Econlib.Math.Analysis.IntervalOrderIso
public import Econlib.Math.Analysis.MeasurableCaratheodory
public import Econlib.Math.Analysis.MinkowskiCaratheodory
public import Econlib.Math.Analysis.ParametricIntegral
public import Econlib.Math.Analysis.RademacherACBridge
public import Econlib.Math.Analysis.SmoothParametricIntegral
public import Econlib.Math.Analysis.SpecialFunctions.Pochhammer
public import Econlib.Math.Analysis.SpecialFunctions.Rpow
public import Econlib.Math.Analysis.StrictJensenNormSq
public import Econlib.Math.Analysis.SubgradientSelection
public import Econlib.Math.Analysis.Supergradient

/-!
# Analysis support library

This module collects analysis results for Econlib's optimization, probability, and mechanism design
developments. It exposes convex-analysis tools, envelope and differentiability results,
finite-dimensional separation and Caratheodory lemmas, concavification on the line, parametric
integral differentiability, and special-function identities.

## Main topics

* Convex analysis: Hinge representations, Fenchel-Moreau, faces, subgradients, Jensen-style
  strictness, convex reductions, and bounded-derivative approximations.
* Concavification: One-dimensional envelopes, convex envelopes, one-gap chords, and duality.
* Differentiability and calculus: Danskin, implicit functions, Cauchy mean-value packaging,
  Rademacher bridges, smooth parametric integrals, and closed-form integral identities.
* Auxiliary geometry: Minkowski-Caratheodory, measurable Caratheodory selections, interval-order
  isomorphisms, and convolution preservation.

## Tags

analysis, convexity, concavity, differentiability, concavification
-/
