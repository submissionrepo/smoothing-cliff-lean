/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.PaymentFormula

/-!
# Myerson's lemma: Implementability ⟺ monotonicity

An allocation rule `X` is *implementable* — there exists a payment schedule making the mechanism
incentive compatible — iff `X` is monotone.

The **Myerson payment** `p(θ) = θ·x(θ) − ∫_{θlo}^θ x`, normalized so the lowest type has zero
interim utility, implements any monotone `X`.

## Main statements

* `AllocationRule.monotone_implies_isBIC`: The Myerson payment implements any monotone allocation.
* `AllocationRule.myersonMechanism_isBIR`: The Myerson mechanism is individually rational.
* `myerson_lemma`: An allocation rule is implementable iff it is monotone.

## References

* Mussa, Michael, and Sherwin Rosen. 1978. “Monopoly and Product Quality.” *Journal of Economic
  Theory* 18 (2): 301–17. [https://doi.org/10.1016/0022-0531(78)90085-6](https://doi.org/10.1016/0022-0531(78)90085-6).
* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, screening, myerson lemma, implementability, monotonicity
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AllocationRule

variable {E : ScreeningEnv} (X : AllocationRule E)

/-- The **Myerson payment** with the `interimUtil(θlo) = 0` normalization:
`p(θ) = θ·x(θ) − ∫_{θlo}^θ x(s) ds`. -/
def myersonPayment (θ : ℝ) : ℝ := θ * X.x θ - ∫ s in E.θlo..θ, X.x s

/-- The direct mechanism implementing `X` via the Myerson payment. -/
def myersonMechanism : DirectMechanism E := ⟨X, X.myersonPayment⟩

@[simp] lemma myersonMechanism_alloc : (X.myersonMechanism).alloc = X := rfl

@[simp] lemma myersonMechanism_p : (X.myersonMechanism).p = X.myersonPayment := rfl

/-- A monotone allocation is interval-integrable on any sub-pair of the type interval. -/
lemma intervalIntegrable_x (hmono : MonotoneAlloc X) {a b : ℝ}
    (ha : a ∈ E.types) (hb : b ∈ E.types) : IntervalIntegrable X.x volume a b :=
  MonotoneOn.intervalIntegrable (hmono.mono (uIcc_subset_Icc ha hb))

/-- The core incentive inequality: `(θ − r)·x(r) ≤ ∫_r^θ x`. -/
lemma sub_mul_le_integral (hmono : MonotoneAlloc X) {r θ : ℝ}
    (hr : r ∈ E.types) (hθ : θ ∈ E.types) :
    (θ - r) * X.x r ≤ ∫ s in r..θ, X.x s := by
  -- `(b - a)·x(r)` is the integral of the constant `x(r)` over `a..b`
  have hconst : ∀ a b : ℝ, (∫ _ in a..b, X.x r) = (b - a) * X.x r := fun a b => by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rcases le_total r θ with hle | hle
  · -- on `[r, θ]` the integrand dominates the constant `x(r)` by monotonicity
    rw [← hconst r θ]
    refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
      (X.intervalIntegrable_x hmono hr hθ) (fun s hs => ?_)
    exact hmono.le hr ⟨le_trans hr.1 hs.1, le_trans hs.2 hθ.2⟩ hs.1
  · -- on `[θ, r]` the constant `x(r)` dominates; flip the oriented integral
    rw [intervalIntegral.integral_symm]
    have hcmp : (∫ s in θ..r, X.x s) ≤ (r - θ) * X.x r := by
      rw [← hconst θ r]
      refine intervalIntegral.integral_mono_on hle (X.intervalIntegrable_x hmono hθ hr)
        intervalIntegrable_const (fun s hs => ?_)
      exact hmono.le ⟨le_trans hθ.1 hs.1, le_trans hs.2 hr.2⟩ hr hs.2
    linarith

/-- The on-path interim utility under the Myerson payment is the integral of the allocation. -/
@[simp] lemma interimUtil_myersonMechanism (θ : ℝ) :
    (X.myersonMechanism).interimUtil θ = ∫ s in E.θlo..θ, X.x s := by
  simp only [DirectMechanism.interimUtil_def, DirectMechanism.x_def, myersonMechanism_alloc,
    myersonMechanism_p, myersonPayment]
  ring

/-- **Constructive direction of Myerson's lemma.** The Myerson payment implements any monotone
allocation: The resulting mechanism is incentive compatible. -/
theorem monotone_implies_isBIC (hmono : MonotoneAlloc X) : IsBIC X.myersonMechanism := by
  intro θ hθ r hr
  simp only [DirectMechanism.reportUtil_def, DirectMechanism.x_def, myersonMechanism_alloc,
    myersonMechanism_p, myersonPayment, interimUtil_myersonMechanism]
  have hadj : (∫ s in E.θlo..r, X.x s) + (∫ s in r..θ, X.x s) = ∫ s in E.θlo..θ, X.x s :=
    intervalIntegral.integral_add_adjacent_intervals
      (X.intervalIntegrable_x hmono E.θlo_mem_types hr) (X.intervalIntegrable_x hmono hr hθ)
  have hkey := X.sub_mul_le_integral hmono hr hθ
  nlinarith [hadj, hkey]

/-- The Myerson mechanism is individually rational. On the type interval its on-path interim
utility is `∫_{θlo}^θ x` with `x ≥ 0` and `θlo ≤ θ`, hence nonnegative. No monotonicity is needed:
Individual rationality follows from the zero-rent normalization at `θlo` plus a nonnegative
allocation. -/
theorem myersonMechanism_isBIR : IsBIR X.myersonMechanism := by
  intro θ hθ
  rw [interimUtil_myersonMechanism]
  exact intervalIntegral.integral_nonneg_of_forall hθ.1 X.nonneg

end AllocationRule

/-- **Myerson's lemma** (Myerson 1981). An allocation rule is implementable iff it is monotone. -/
theorem myerson_lemma {E : ScreeningEnv} (X : AllocationRule E) :
    (∃ p : ℝ → ℝ, IsBIC (DirectMechanism.mk X p)) ↔ MonotoneAlloc X := by
  constructor
  · rintro ⟨p, hbic⟩
    exact (DirectMechanism.mk X p).isBIC_implies_monotone hbic
  · intro hmono
    exact ⟨X.myersonPayment, X.monotone_implies_isBIC hmono⟩

end Econlib.MechanismDesign.Transfers.SingleParameter
