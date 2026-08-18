/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.AffineInequalities
public import Econlib.Math.Order.CountableLinearOrderEmbedding
public import Econlib.Math.Order.CsSup
public import Econlib.Math.Order.GapFilling
public import Econlib.Math.Order.ISupFinTwo
public import Econlib.Math.Order.Intervals
public import Econlib.Math.Order.OrderedCutoffPartition
public import Econlib.Math.Order.StrongSetOrder
public import Econlib.Math.Order.Supermodular

/-!
# Order support library

This module collects order-theoretic tools for Econlib. It exposes countable embeddings into
bounded real intervals, open-gap filling, finite suprema over `Fin 2`, ordered cutoff partitions,
the strong set order, and supermodular real-valued functions.

## Tags

order theory, supermodularity, strong set order, cutoff partition
-/
