/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.Bellman

/-!
# Closed Invariant Set Principle for the Bellman Operator

If `C` is a nonempty closed subset of `BddFun` that is invariant under the lifted Bellman operator,
then the value function lies in `C`.

This is the mechanism by which shape properties (concavity, monotonicity, etc.) are transferred
from the Bellman operator to the value function: Define `C = {v ∈ BddFun | v has property P}`, show
`T(C) ⊆ C`, and conclude `v* ∈ C`.

This file specializes the closed-invariant-set fixed-point principle to the deterministic Bellman
operator.

## Main statements

* `DetMDP.isFixedPt_mem_closedInvariant`: Any bounded solution of the Bellman equation lies in
  every nonempty closed invariant set.
* `DetMDP.valueFunction_mem_closedInvariant`: In particular, the value function does.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76). Corollary 1 to Theorem
  3.2.

## Tags

dynamic programing, contraction mapping, fixed point, invariant set, Bellman operator
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell

universe u_S
variable {S : Type u_S} {A : Type*} [Nonempty S]

/-- **Closed invariant set principle for the Bellman operator.** If `C ⊆ BddFun` is nonempty,
closed, and invariant under the lifted Bellman operator, then every bounded solution of the Bellman
equation lies in `C` (as its `toBddFun` embedding). -/
theorem DetMDP.isFixedPt_mem_closedInvariant (M : DetMDP S A)
    {C : Set (@BddFun S)} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo (bellmanOperatorBddFun M) C C)
    {v : S → ℝ} (hv_bdd : UniformBounded v)
    (hv_fp : ∀ s, v s = M.bellmanOperator v s) :
    toBddFun v hv_bdd ∈ C :=
  Blackwell.isFixedPt_mem_of_isClosed M.contractingWith_bellmanOperatorBddFun
    hC_nonempty hC_closed hC_inv hv_bdd hv_fp

/-- The value function lies in every nonempty closed set invariant under the lifted Bellman
operator. -/
theorem DetMDP.valueFunction_mem_closedInvariant (M : DetMDP S A)
    {C : Set (@BddFun S)} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo (bellmanOperatorBddFun M) C C) :
    toBddFun M.valueFunction M.valueFunction_bounded ∈ C :=
  M.isFixedPt_mem_closedInvariant hC_nonempty hC_closed hC_inv
    M.valueFunction_bounded M.valueFunction_isFixedPt

end Econlib.Optimization.DynamicProgramming
