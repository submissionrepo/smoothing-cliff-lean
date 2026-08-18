/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.AbstractDisintegration
public import Econlib.Math.MeasureTheory.AnalyticNullMeasurable
public import Econlib.Math.MeasureTheory.AnalyticUniformization
public import Econlib.Math.MeasureTheory.CauchySchwarz
public import Econlib.Math.MeasureTheory.Chebyshev
public import Econlib.Math.MeasureTheory.CompProdProjections
public import Econlib.Math.MeasureTheory.ConvexIntegralRepr
public import Econlib.Math.MeasureTheory.DiracSum
public import Econlib.Math.MeasureTheory.FTC
public import Econlib.Math.MeasureTheory.GradientDisintegration
public import Econlib.Math.MeasureTheory.IntegralAsymp
public import Econlib.Math.MeasureTheory.IntegralBridge
public import Econlib.Math.MeasureTheory.IntegralReal
public import Econlib.Math.MeasureTheory.IntegralTails
public import Econlib.Math.MeasureTheory.IntervalIntegral
public import Econlib.Math.MeasureTheory.LusinContinuity
public import Econlib.Math.MeasureTheory.MeasurableSelection
public import Econlib.Math.MeasureTheory.PiCompProd
public import Econlib.Math.MeasureTheory.PiProdCongr
public import Econlib.Math.MeasureTheory.PiUpdate
public import Econlib.Math.MeasureTheory.PolishRefinement
public import Econlib.Math.MeasureTheory.SimplexIntegral
public import Econlib.Math.MeasureTheory.StieltjesAbsCont
public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Econlib.Math.MeasureTheory.StieltjesRegularization
public import Econlib.Math.MeasureTheory.TriangleFubini
public import Econlib.Math.MeasureTheory.VonNeumannSelection
public import Econlib.Math.MeasureTheory.WeakConvergence.FixedMarginal
public import Econlib.Math.MeasureTheory.WeakConvergence.FixedMarginalContinuity
public import Econlib.Math.MeasureTheory.WeakConvergence.PortmanteauIntegral
public import Econlib.Math.MeasureTheory.WeakConvergence.ProbabilityMeasureWeakDual

/-!
# Measure-theory support library

This module collects measure-theoretic tools for Econlib's probability and economic applications.
It exposes disintegration and measurable-selection results, product-measure and simplex-integration
identities, Stieltjes and fundamental-theorem-of-calculus bridges, integral inequalities,
weak-convergence results, and finite sums of Dirac measures.

## Main topics

* Disintegration and selection: Abstract disintegration, analytic uniformization, von Neumann and
  measurable-selection tools, Lusin continuity, and Polish refinements.
* Product and simplex integration: Product-coordinate rewrites, triangle and simplex Fubini
  formulas, pair/product congruences, and gradient disintegration.
* Stieltjes and integral calculus: Stieltjes integration by parts, absolute continuity,
  regularization, FTC bridges, integral tails, Chebyshev and Cauchy-Schwarz inequalities.
* Weak convergence: Fixed-marginal compactness and continuity, portmanteau integral statements, and
  weak-dual probability-measure results.

## Tags

measure theory, disintegration, measurable selection, stieltjes, weak convergence
-/
