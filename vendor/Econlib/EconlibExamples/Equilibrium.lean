/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import EconlibExamples.Equilibrium.CobbDouglasEdgeworth
import EconlibExamples.Equilibrium.CobbDouglasRoy
import EconlibExamples.Equilibrium.FiniteExistence
import EconlibExamples.Equilibrium.FirmConnected
import EconlibExamples.Equilibrium.MarkovStationary
import EconlibExamples.Equilibrium.RobinsonCrusoe

/-!
# EconlibExamples.Equilibrium

Worked examples of general-equilibrium theory, formalized against the `Econlib.Equilibrium` API.
Each example file is a self-contained tutorial: It constructs a textbook economy, names the claim,
and proves it.

Per-file index:

* `CobbDouglasEdgeworth` — the 2×2 Edgeworth box with Cobb–Douglas preferences: The interior
  competitive equilibrium, both welfare theorems, and the total-Cobb–Douglas `RegularEconomy`
  witness (demand optimality via weighted AM–GM).
* `CobbDouglasRoy` — Roy's identity for the closed-form Cobb–Douglas Marshallian demand: The
  acceptance instance certifying that `roy_identity_of_isMaxOn` is non-vacuous (Cobb–Douglas
  gradient on the interior, demand smoothness, positive budget multiplier).
* `FiniteExistence` — existence of a Walrasian equilibrium in a concrete three-agent economy, via
  the library's Kakutani-based `exists_equilibrium`.
* `FirmConnected` — a firm-connected two-agent production economy: The regression guard for
  production irreducibility (`IrreducibleProd`). The pure-exchange `Irreducible` predicate *fails*
  (labor-only endowments, Cobb–Douglas tastes), but the shared labor→output firm restores
  irreducibility, so the general existence theorem still delivers an equilibrium.
* `RobinsonCrusoe` — a one-consumer, one-firm production economy: Profit maximization, market
  clearing, and the first welfare theorem with production.
* `MarkovStationary` — a stationary recursive competitive equilibrium of a Markov exchange economy,
  with a steady-state accounting identity.
-/
