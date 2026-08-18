/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Monotone

/-!
# Single-parameter screening: Convexity and monotonicity under incentive compatibility

Two structural consequences of Bayesian incentive compatibility in the single-parameter screening
model: The interim utility function is convex on the type interval, and the allocation rule is
monotone (Mussa and Rosen 1978; Myerson 1981).

## Main statements

* `DirectMechanism.interimUtil_convexOn`: Under `IsBIC`, the interim utility `U(θ) = θ·x(θ) − p(θ)`
  is convex on the type interval.
* `DirectMechanism.isBIC_implies_monotone`: Under `IsBIC`, the allocation rule is monotone.

## References

* Mussa, Michael, and Sherwin Rosen. 1978. “Monopoly and Product Quality.” *Journal of Economic
  Theory* 18 (2): 301–17. [https://doi.org/10.1016/0022-0531(78)90085-6](https://doi.org/10.1016/0022-0531(78)90085-6).
* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, screening, incentive compatibility, convexity, monotone allocation
-/

@[expose] public section

open Set

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace DirectMechanism

variable {E : ScreeningEnv} (M : DirectMechanism E)

/-- **Under incentive compatibility, the interim utility is convex** on the type interval. -/
theorem interimUtil_convexOn (hbic : IsBIC M) : ConvexOn ℝ E.types M.interimUtil := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro θ₀ hθ₀ θ₁ hθ₁ a b ha hb hab
  simp only [smul_eq_mul]
  have hmem : a * θ₀ + b * θ₁ ∈ E.types := by
    simpa [smul_eq_mul] using (convex_Icc E.θlo E.θhi) hθ₀ hθ₁ ha hb hab
  -- U(θ_t) = a · reportUtil(θ₀, θ_t) + b · reportUtil(θ₁, θ_t): the payment cancels linearly.
  have hsplit : M.interimUtil (a * θ₀ + b * θ₁)
      = a * M.reportUtil θ₀ (a * θ₀ + b * θ₁) + b * M.reportUtil θ₁ (a * θ₀ + b * θ₁) := by
    simp only [interimUtil_def, reportUtil_def]
    linear_combination (M.p (a * θ₀ + b * θ₁)) * hab
  rw [hsplit]
  have h0 := hbic θ₀ hθ₀ (a * θ₀ + b * θ₁) hmem
  have h1 := hbic θ₁ hθ₁ (a * θ₀ + b * θ₁) hmem
  exact add_le_add (mul_le_mul_of_nonneg_left h0 ha) (mul_le_mul_of_nonneg_left h1 hb)

/-- **Under incentive compatibility, the allocation is monotone.** -/
theorem isBIC_implies_monotone (hbic : IsBIC M) : MonotoneAlloc M.alloc := by
  intro θ hθ θ' hθ' hle
  have h1 := hbic θ hθ θ' hθ'      -- θ·x θ' − p θ' ≤ θ·x θ − p θ
  have h2 := hbic θ' hθ' θ hθ      -- θ'·x θ − p θ ≤ θ'·x θ' − p θ'
  simp only [reportUtil_def, interimUtil_def, x_def] at h1 h2
  have key : 0 ≤ (θ' - θ) * (M.alloc.x θ' - M.alloc.x θ) := by nlinarith [h1, h2]
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact le_rfl
  · nlinarith [key, sub_pos.mpr hlt]

end DirectMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
