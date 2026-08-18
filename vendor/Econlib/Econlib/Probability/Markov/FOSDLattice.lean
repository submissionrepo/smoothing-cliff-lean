/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.StochasticMonotone
public import Econlib.Probability.Order.FOSD.FinDistLattice
public import Mathlib.Order.FixedPoints

/-!
# Knaster–Tarski stationary distributions for stochastically monotone chains

The FOSD complete lattice on `FinDist α` (from `Order.FOSD.FinDistLattice`) combined with
stochastic monotonicity of the step operator lets the Knaster–Tarski fixed-point theorem yield
existence of stationary distributions. The least fixed point is FOSD-minimal among stationary
distributions and the greatest fixed point is FOSD-maximal.

## Main definitions

* `StochMonotoneFiniteMarkovChain.stepOrderHom` — the step operator as a monotone self-map of the
  FOSD lattice.

## Main statements

* `StochMonotoneFiniteMarkovChain.exists_stationary_lfp` / `exists_stationary_gfp` — existence of a
  stationary distribution via the least / greatest fixed point.
* `StochMonotoneFiniteMarkovChain.lfp_le_stationary` — the lfp is FOSD-minimal.
* `StochMonotoneFiniteMarkovChain.stationary_le_gfp` — the gfp is FOSD-maximal.

## Tags

markov chain, stationary distribution, knaster-tarski, fosd, fixed point
-/

@[expose] public noncomputable section

namespace Econlib.Probability

open Finset BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- The step operator of a stochastically monotone chain is FOSD-monotone. -/
lemma StochMonotoneFiniteMarkovChain.step_fosd_mono (P : StochMonotoneFiniteMarkovChain α) :
    Monotone P.toFiniteMarkovChain.step :=
  fun _ _ hd => P.step_preserves_FOSD hd

/-- The step operator as a monotone self-map of the FOSD lattice. -/
def StochMonotoneFiniteMarkovChain.stepOrderHom (P : StochMonotoneFiniteMarkovChain α) :
    FinDist α →o FinDist α where
  toFun := P.toFiniteMarkovChain.step
  monotone' := P.step_fosd_mono

variable [Nonempty α]

/-- **Existence of stationary distribution via Knaster-Tarski.** The least fixed point of the step
operator (in the FOSD lattice) is a stationary distribution for any stochastically monotone
chain. -/
theorem StochMonotoneFiniteMarkovChain.exists_stationary_lfp
    (P : StochMonotoneFiniteMarkovChain α) :
    ∃ μ : FinDist α, P.toFiniteMarkovChain.step μ = μ :=
  ⟨OrderHom.lfp P.stepOrderHom, OrderHom.isFixedPt_lfp P.stepOrderHom⟩

/-- The least fixed point is FOSD-minimal among stationary distributions. -/
theorem StochMonotoneFiniteMarkovChain.lfp_le_stationary
    (P : StochMonotoneFiniteMarkovChain α)
    (μ : FinDist α) (hμ : P.toFiniteMarkovChain.step μ = μ) :
    OrderHom.lfp P.stepOrderHom ≤ μ :=
  OrderHom.lfp_le_fixed P.stepOrderHom hμ

/-- **Existence of stationary distribution via the greatest fixed point.** -/
theorem StochMonotoneFiniteMarkovChain.exists_stationary_gfp
    (P : StochMonotoneFiniteMarkovChain α) :
    ∃ μ : FinDist α, P.toFiniteMarkovChain.step μ = μ :=
  ⟨OrderHom.gfp P.stepOrderHom, OrderHom.isFixedPt_gfp P.stepOrderHom⟩

/-- The greatest fixed point is FOSD-maximal among stationary distributions. -/
theorem StochMonotoneFiniteMarkovChain.stationary_le_gfp
    (P : StochMonotoneFiniteMarkovChain α)
    (μ : FinDist α) (hμ : P.toFiniteMarkovChain.step μ = μ) :
    μ ≤ OrderHom.gfp P.stepOrderHom :=
  (OrderHom.isGreatest_gfp P.stepOrderHom).2 hμ

end Econlib.Probability

end
