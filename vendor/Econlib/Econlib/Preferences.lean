/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic
public import Econlib.Preferences.Geometry.Basic
public import Econlib.Preferences.Geometry.Nonsatiation
public import Econlib.Preferences.Geometry.SingleCrossing
public import Econlib.Preferences.Geometry.SinglePeaked
public import Econlib.Preferences.Pareto
public import Econlib.Preferences.Representation.Debreu
public import Econlib.Preferences.Representation.Finite
public import Econlib.Preferences.Risk.ArrowPratt
public import Econlib.Preferences.Risk.Basic
public import Econlib.Preferences.Risk.CertaintyEquivalent
public import Econlib.Preferences.Risk.ComparativeRiskAversion
public import Econlib.Preferences.Utility.CobbDouglas
public import Econlib.Preferences.Utility.Differentiable
public import Econlib.Preferences.Utility.Inada
public import Econlib.Preferences.Utility.Linear
public import Econlib.Preferences.Utility.Positive
public import Econlib.Preferences.Utility.Prudence
public import Econlib.Preferences.Utility.Quasilinear
public import Econlib.Preferences.Utility.RiskFamilies
public import Econlib.Preferences.Utility.Separable
public import Econlib.Preferences.Utility.Sqrt

/-!
# Preferences library

This module collects Econlib's preference API. It exposes total-preorder preferences, utility
representation predicates, geometric restrictions on preferences, Pareto dominance, risk-attitude
notions, and reusable utility families for consumer and uncertainty applications.

## Main topics

* Core preferences: `PreferenceRel`, strict preference, indifference, contour sets, and ordinal or
  real-valued utility representation.
* Geometry: Convex preferences, monotonicity and nonsatiation, single crossing, and single-peaked
  preferences.
* Risk: Certainty equivalents, risk premia, Arrow-Pratt measures, prudence, and comparative risk
  aversion.
* Utility families: Positive-domain primitives, differentiable utilities, Inada conditions,
  Cobb-Douglas, quasilinear, separable, square-root, and closed-form risk families.

## Tags

preferences, utility, risk aversion, pareto, single crossing
-/
