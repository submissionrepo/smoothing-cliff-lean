/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.AgentAggregation
public import Econlib.Equilibrium.AggregateAccounting
public import Econlib.Equilibrium.Basic
public import Econlib.Equilibrium.CobbDouglasDemand
public import Econlib.Equilibrium.Economy
public import Econlib.Equilibrium.Existence
public import Econlib.Equilibrium.IndirectUtility
public import Econlib.Equilibrium.LimitedEnforcement
public import Econlib.Equilibrium.LinearEconomy
public import Econlib.Equilibrium.MarketClearing
public import Econlib.Equilibrium.Production.Economy
public import Econlib.Equilibrium.Production.Existence
public import Econlib.Equilibrium.Production.SecondWelfare
public import Econlib.Equilibrium.Production.Technology
public import Econlib.Equilibrium.Production.Welfare
public import Econlib.Equilibrium.RoyIdentity
public import Econlib.Equilibrium.SecondWelfare
public import Econlib.Equilibrium.Welfare

/-!
# General equilibrium library

This module collects Econlib's general-equilibrium API. It exposes the commodity-space conventions,
preference-carried exchange economies, market-clearing and welfare statements, existence theorems,
explicit regular-economy constructors, consumer duality facts, stationary aggregate-accounting
results, and the private-ownership production-economy extension.

## Main topics

* Exchange economies: `Economy`, `RegularEconomy`, Walrasian equilibrium, core membership, and
  finite or measure-agent aggregation.
* Welfare and existence: First and second welfare theorems, supporting-price theorems, and
  Arrow-Debreu-McKenzie existence results.
* Explicit demand and duality: Cobb-Douglas demand, indirect utility, Roy's identity, and
  limited-enforcement participation constraints.
* Production economies: Technologies, profit maximization, production equilibrium, and welfare
  theorems with production.

## Tags

general equilibrium, walrasian equilibrium, welfare theorem, production economy
-/
