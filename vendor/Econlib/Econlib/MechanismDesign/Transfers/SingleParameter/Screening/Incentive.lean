/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Environment

/-!
# Single-parameter screening: Incentive compatibility and participation

Incentive compatibility and individual rationality conditions for direct mechanisms in the
single-parameter screening model.

## Main definitions

* `DirectMechanism.reportUtil`: The utility a type-`θ` agent obtains by reporting `r`, equal to
  `θ · x(r) − p(r)`. For each fixed `r` this is affine in `θ`.
* `IsBIC`: Bayesian incentive compatibility — truthful reporting is weakly optimal for every type.
* `IsBIR`: Interim individual rationality — every type's on-path utility is nonnegative.

## Main statements

* `DirectMechanism.reportUtil_self`: Reporting truthfully realizes the on-path interim utility.
* `IsBIC.reportUtil_le`: Under `IsBIC`, any misreport `r` yields at most the on-path utility at `θ`.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

incentive compatibility, individual rationality, screening, mechanism design
-/

@[expose] public section

open Set

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace DirectMechanism

variable {E : ScreeningEnv} (M : DirectMechanism E)

/-- The utility a type-`θ` agent obtains by reporting `r`: `θ · x(r) − p(r)`. For each fixed report
`r` this is affine in the true type `θ`. -/
def reportUtil (θ r : ℝ) : ℝ := θ * M.x r - M.p r

@[simp] lemma reportUtil_def (θ r : ℝ) : M.reportUtil θ r = θ * M.x r - M.p r := rfl

/-- Reporting truthfully realizes the on-path interim utility. -/
@[simp] lemma reportUtil_self (θ : ℝ) : M.reportUtil θ θ = M.interimUtil θ := rfl

end DirectMechanism

/-- **Incentive compatibility.** For every true type `θ` and every feasible report `r`, truthful
reporting is (weakly) optimal: `θ · x(θ) − p(θ) ≥ θ · x(r) − p(r)`. -/
def IsBIC {E : ScreeningEnv} (M : DirectMechanism E) : Prop :=
  ∀ θ ∈ E.types, ∀ r ∈ E.types, M.reportUtil θ r ≤ M.interimUtil θ

/-- **Interim individual rationality.** Every type's on-path utility is nonnegative — the agent
weakly prefers participating to the outside option `0`. -/
def IsBIR {E : ScreeningEnv} (M : DirectMechanism E) : Prop :=
  ∀ θ ∈ E.types, 0 ≤ M.interimUtil θ

namespace IsBIC

variable {E : ScreeningEnv} {M : DirectMechanism E}

/-- The utility from any misreport `r` is at most the on-path utility at `θ`. -/
lemma reportUtil_le (h : IsBIC M) {θ r : ℝ} (hθ : θ ∈ E.types) (hr : r ∈ E.types) :
    M.reportUtil θ r ≤ M.interimUtil θ := h θ hθ r hr

end IsBIC

end Econlib.MechanismDesign.Transfers.SingleParameter
