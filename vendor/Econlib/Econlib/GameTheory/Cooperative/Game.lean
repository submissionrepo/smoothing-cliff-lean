/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Real.Basic

/-!
# Transferable-utility cooperative games

This file defines the core data of a transferable-utility cooperative game on a fixed finite player
type: A characteristic function `value : Finset Player → ℝ` normalized so that the empty coalition
receives `0`.

The structure `TUGameOn Player` is the carrier for all cooperative-game theory in `Econlib`:
Value-rule axioms, the Shapley value, the core, balancedness, and convexity all take it as input,
with the player type carrying `[Fintype]` and `[DecidableEq]` brackets.

## Main definitions

* `TUGameOn`: A transferable-utility game on a fixed finite player type.
* `TUGameOn.PayoffVector`: Payoff vectors for a fixed game.

## Tags

cooperative game, transferable utility, characteristic function
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

/-- A transferable-utility game on a fixed finite player type.

This is the carrier for value-rule axioms, which compare a rule across games with the same player
set. -/
structure TUGameOn (Player : Type*) [Fintype Player] [DecidableEq Player] where
  /-- Characteristic function. -/
  value : Finset Player → ℝ
  /-- The empty coalition has value zero. -/
  value_empty : value ∅ = 0

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Two fixed-player TU games are equal when their characteristic functions agree on every
coalition. -/
@[ext] lemma ext {G H : TUGameOn Player} (h : ∀ S, G.value S = H.value S) :
    G = H := by
  cases G; cases H
  congr 1
  exact funext h

/-- Payoff vector for a fixed-player cooperative game. -/
abbrev PayoffVector (_G : TUGameOn Player) := Player → ℝ

end TUGameOn

end Econlib.GameTheory
