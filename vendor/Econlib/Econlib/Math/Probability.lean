/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Probability.Doeblin
public import Econlib.Math.Probability.KernelPi
public import Econlib.Math.Probability.Quantile
public import Econlib.Math.Probability.QuantileIntegral
public import Econlib.Math.Probability.QuantileStopLoss
public import Econlib.Math.Probability.StopLoss

/-!
# Probability support library

This module collects measure-level probability tools for Econlib before specializing to `FinDist`,
`CountDist`, `ContDist`, or `ProbDist`. It exposes quantile functions and their integral
identities, stop-loss transforms, finite products of Markov kernels, and Doeblin contraction facts.

## Tags

probability, quantile, stop-loss, markov kernel, doeblin
-/
