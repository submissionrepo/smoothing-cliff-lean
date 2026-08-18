/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Incentive

/-!
# Single-parameter screening: Monotone allocations

`MonotoneAlloc X` asserts that an allocation rule is nondecreasing on the type interval. Myerson's
lemma (`MyersonLemma`) characterizes implementability: An allocation rule is implementable by some
incentive-compatible payment schedule if and only if it is monotone.

## Main definitions

* `MonotoneAlloc`: An allocation rule is nondecreasing on the type interval.

## Main statements

* `MonotoneAlloc.le`: Monotonicity unpacked at a specific comparable pair of types.

## References

* Mussa, Michael, and Sherwin Rosen. 1978. “Monopoly and Product Quality.” *Journal of Economic
  Theory* 18 (2): 301–17. [https://doi.org/10.1016/0022-0531(78)90085-6](https://doi.org/10.1016/0022-0531(78)90085-6).
* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

screening, monotone allocation, myerson's lemma, implementability
-/

@[expose] public noncomputable section

open Set

namespace Econlib.MechanismDesign.Transfers.SingleParameter

/-- An allocation rule is **monotone** when it is nondecreasing on the type interval. -/
def MonotoneAlloc {E : ScreeningEnv} (X : AllocationRule E) : Prop :=
  MonotoneOn X.x E.types

namespace MonotoneAlloc

variable {E : ScreeningEnv} {X : AllocationRule E}

/-- Unpack monotonicity at a specific comparable pair. -/
lemma le (h : MonotoneAlloc X) {θ θ' : ℝ} (hθ : θ ∈ E.types) (hθ' : θ' ∈ E.types)
    (hle : θ ≤ θ') : X.x θ ≤ X.x θ' := h hθ hθ' hle

end MonotoneAlloc

end Econlib.MechanismDesign.Transfers.SingleParameter
