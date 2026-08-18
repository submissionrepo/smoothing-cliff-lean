/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueEquivalence

/-!
# Virtual values and regularity

Myerson's **virtual value** `ψ(θ) = θ − (1 − F(θ)) / f(θ)` (Myerson 1981), where `F` is the type
CDF and `f` the density, converts revenue maximization into pointwise virtual-surplus maximization.
The term `(1 − F)/f` is the informational rent conceded to types above `θ`.

A `ScreeningEnv` is **regular** (Myerson 1981) if `ψ` is monotone on the type interval. Under
regularity, the revenue-optimal allocation serves exactly the types with nonnegative virtual value
and no ironing is needed.

## Main definitions

* `ScreeningEnv.virtualValue` — the virtual value function `ψ`.
* `ScreeningEnv.Regular` — Myerson regularity: `ψ` is monotone on the type interval.

## Main statements

* `ScreeningEnv.virtualValue_measurable` — the virtual value function is measurable.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

virtual value, regularity, myerson, screening, mechanism design
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-- The **virtual value** `ψ(θ) = θ − (1 − F(θ)) / f(θ)`. -/
def virtualValue (θ : ℝ) : ℝ := θ - (1 - E.dist.cdf θ) / E.dist.density θ

@[simp] lemma virtualValue_def (θ : ℝ) :
    E.virtualValue θ = θ - (1 - E.dist.cdf θ) / E.dist.density θ := rfl

/-- **Regularity** (Myerson 1981): The virtual value is monotone on the type interval. Under
regularity the revenue-optimal allocation serves exactly the types with nonnegative virtual value,
and no ironing is needed. -/
def Regular : Prop := MonotoneOn E.virtualValue E.types

/-- The density vanishes off the support. -/
private lemma density_eq_zero_of_notMem_types {θ : ℝ} (hθ : θ ∉ E.types) :
    E.dist.density θ = 0 := by
  by_contra h
  exact hθ (E.supp_subset θ (lt_of_le_of_ne (E.dist.nonneg θ) (Ne.symm h)))

/-- The virtual value function is measurable. -/
lemma virtualValue_measurable : Measurable E.virtualValue := by
  classical
  have hcont : ContinuousOn E.virtualValue E.types :=
    continuousOn_id.sub ((continuousOn_const.sub E.dist.cdf_continuous.continuousOn).div
      E.density_cont (fun x hx => ne_of_gt (E.density_pos x hx)))
  -- Off the support the density vanishes, so `ψ = id` there and `ψ = Icc.piecewise ψ id`.
  have hpiece : E.virtualValue = (E.types).piecewise E.virtualValue id := by
    ext θ
    by_cases hθ : θ ∈ E.types
    · rw [Set.piecewise_eq_of_mem _ _ _ hθ]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hθ, id_eq, ScreeningEnv.virtualValue_def,
        E.density_eq_zero_of_notMem_types hθ, div_zero, sub_zero]
  rw [hpiece]
  exact ContinuousOn.measurable_piecewise hcont continuous_id.continuousOn measurableSet_Icc

end ScreeningEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
