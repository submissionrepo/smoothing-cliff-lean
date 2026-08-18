/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Envelope

/-!
# The Revenue Equivalence Theorem (single parameter)

Two incentive-compatible mechanisms with the same allocation rule and the same interim utility at
the lowest type charge the same payments, hence raise the same expected revenue (Myerson 1981;
Riley and Samuelson 1981).

## Main statements

* `revenue_equivalence`: If `M₁` and `M₂` are BIC, share the same allocation on the type interval,
  and give the lowest type the same interim utility, then they charge identical payments.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).
* Riley, John G., and William F. Samuelson. 1981. “Optimal Auctions.” *The American Economic
  Review* 71 (3): 381–92.

## Tags

revenue equivalence, screening, incentive compatibility, single parameter
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

variable {E : ScreeningEnv}

/-- **Revenue equivalence.** If `M₁` and `M₂` are incentive compatible, share the same allocation
on the type interval, and give the lowest type the same interim utility, then they charge identical
payments throughout the interval. -/
theorem revenue_equivalence {M₁ M₂ : DirectMechanism E} (h₁ : IsBIC M₁) (h₂ : IsBIC M₂)
    (hx : ∀ θ ∈ E.types, M₁.x θ = M₂.x θ)
    (hU0 : M₁.interimUtil E.θlo = M₂.interimUtil E.θlo)
    {θ : ℝ} (hθ : θ ∈ E.types) : M₁.p θ = M₂.p θ := by
  have hUθ : M₁.interimUtil θ = M₂.interimUtil θ := by
    rw [M₁.interimUtil_eq_integral h₁ hθ, M₂.interimUtil_eq_integral h₂ hθ, hU0]
    congr 1
    exact intervalIntegral.integral_congr
      (fun s hs => hx s (uIcc_subset_Icc E.θlo_mem_types hθ hs))
  have e₁ : M₁.p θ = θ * M₁.x θ - M₁.interimUtil θ := by rw [DirectMechanism.interimUtil_def]; ring
  have e₂ : M₂.p θ = θ * M₂.x θ - M₂.interimUtil θ := by rw [DirectMechanism.interimUtil_def]; ring
  rw [e₁, e₂, hUθ, hx θ hθ]

end Econlib.MechanismDesign.Transfers.SingleParameter
