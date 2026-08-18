/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.TriangleFubini
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.VirtualValue

/-!
# Single-parameter screening: The Myerson revenue identity

The **Myerson revenue identity**: Under incentive compatibility and a normalized lowest-type rent
(`U(θlo) = 0`), expected payment equals expected *virtual surplus*,

`𝔼[p(θ)] = 𝔼[ψ(θ) · x(θ)]`,

where `ψ(θ) = θ − (1 − F(θ)) / f(θ)` is the virtual value. This identity collapses the seller's
revenue-maximization to pointwise virtual-surplus maximization (Myerson 1981).

## Main statements

* `DirectMechanism.expected_revenue_eq_virtual_surplus_sub_rent` — the general identity
  `𝔼[p] = 𝔼[ψ·x] − U(θlo)`, with no normalization.
* `DirectMechanism.expected_revenue_eq_virtual_surplus` — the normalized identity (`U(θlo) = 0`).
* `DirectMechanism.expected_revenue_le_virtual_surplus` — the revenue bound `𝔼[p] ≤ 𝔼[ψ·x]` for any
  individually rational BIC mechanism.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

screening, revenue identity, virtual value, myerson
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-- **`expect`→interval-integral reduction.** Since the density vanishes off `[θlo, θhi]`, the
expectation `𝔼[h] = ∫ density·h` over `ℝ` collapses to the interval integral on the support. -/
lemma expect_eq_intervalIntegral (h : ℝ → ℝ) :
    E.dist.expect h = ∫ θ in E.θlo..E.θhi, E.dist.density θ * h θ := by
  rw [E.dist.expect_eq_integral]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc E.θlo E.θhi) (fun θ hθ => by rw [E.density_eq_zero_of_notMem hθ, zero_mul])]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le E.hθ.le]

/-- The total density mass on the support is `1`. -/
lemma density_mass_eq_one : (∫ θ in E.θlo..E.θhi, E.dist.density θ) = 1 := by
  have h := E.expect_eq_intervalIntegral (fun _ => 1)
  rw [E.dist.expect_const] at h
  simpa using h.symm

/-- The CDF is the cumulative density on the support: For `θ ∈ [θlo, θhi]`,
`F(θ) = ∫_{θlo}^θ density`. -/
lemma cdf_eq_intervalIntegral (θ : ℝ) :
    E.dist.cdf θ = ∫ s in E.θlo..θ, E.dist.density s := by
  -- `cdf θlo = 0` since the density vanishes a.e. on `Iic θlo` (only `{θlo}` carries mass `0`).
  have hcdf_lo : (∫ t in Iic E.θlo, E.dist.density t) = 0 := by
    rw [← MeasureTheory.setIntegral_congr_set (Iio_ae_eq_Iic (a := E.θlo))]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    exact E.density_eq_zero_of_notMem (fun hmem => absurd (mem_Iio.mp ht) (not_lt.mpr hmem.1))
  have hsub := intervalIntegral.integral_Iic_sub_Iic (a := E.θlo) (b := θ)
    E.dist.integrable.integrableOn E.dist.integrable.integrableOn
  rw [E.dist.cdf_eq_integral]
  linarith [hsub]

end ScreeningEnv

namespace DirectMechanism

variable {E : ScreeningEnv} (M : DirectMechanism E)

/-- **Payment from the envelope formula (general).** On the type interval the payment is
`p(θ) = θ·x(θ) − U(θlo) − ∫_{θlo}^θ x`, where `U(θlo) = M.interimUtil E.θlo` is the lowest type's
rent. No normalization is assumed. -/
lemma payment_eq_sub_rent (hbic : IsBIC M) {θ : ℝ} (hθ : θ ∈ E.types) :
    M.p θ = θ * M.x θ - M.interimUtil E.θlo - ∫ s in E.θlo..θ, M.x s := by
  have henv := M.interimUtil_eq_integral hbic hθ
  rw [interimUtil_def] at henv
  linarith [henv]

/-- **Payment from the envelope formula.** With the lowest type's rent normalized to `0`, the
payment on the type interval is `p(θ) = θ·x(θ) − ∫_{θlo}^θ x`. -/
lemma payment_eq (hbic : IsBIC M) (hU0 : M.interimUtil E.θlo = 0) {θ : ℝ} (hθ : θ ∈ E.types) :
    M.p θ = θ * M.x θ - ∫ s in E.θlo..θ, M.x s := by
  rw [M.payment_eq_sub_rent hbic hθ, hU0, sub_zero]

/-- **Myerson revenue identity (general).** Under incentive compatibility, expected payment equals
expected virtual surplus minus the lowest type's rent: `𝔼[p(θ)] = 𝔼[ψ(θ)·x(θ)] − U(θlo)`. No
normalization is assumed; the rent `U(θlo) = M.interimUtil E.θlo` is the only slack between revenue
and virtual surplus. -/
theorem expected_revenue_eq_virtual_surplus_sub_rent (hbic : IsBIC M) :
    E.dist.expect M.p
      = E.dist.expect (fun θ => E.virtualValue θ * M.x θ) - M.interimUtil E.θlo := by
  set a := E.θlo
  set b := E.θhi
  have hab : a ≤ b := E.hθ.le
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hmono : MonotoneAlloc M.alloc := M.isBIC_implies_monotone hbic
  have hxii : IntervalIntegrable M.x volume a b :=
    M.alloc.intervalIntegrable_x hmono E.θlo_mem_types E.θhi_mem_types
  have hfcont : ContinuousOn E.dist.density (uIcc a b) := huIcc ▸ E.density_cont
  have hθfcont : ContinuousOn (fun θ => θ * E.dist.density θ) (uIcc a b) :=
    (continuousOn_id.mul hfcont)
  have hXprim_cont : ContinuousOn (fun θ => ∫ s in a..θ, M.x s) (uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval' hxii (left_mem_uIcc)
  have hA : IntervalIntegrable (fun θ => (θ * E.dist.density θ) * M.x θ) volume a b :=
    hxii.continuousOn_mul hθfcont
  have hB : IntervalIntegrable (fun θ => (∫ s in a..θ, M.x s) * E.dist.density θ) volume a b :=
    (hXprim_cont.intervalIntegrable).mul_continuousOn hfcont
  -- The rent contributes the constant `U(θlo) · density`, integrating to `U(θlo)` (total mass `1`).
  have hRent : IntervalIntegrable (fun θ => M.interimUtil a * E.dist.density θ) volume a b :=
    (hfcont.intervalIntegrable).const_mul _
  have hswap := MeasureTheory.integral_triangle_swap_survival hab hxii
    (hfcont.intervalIntegrable) (F := fun θ => E.dist.cdf θ)
    (fun t => E.cdf_eq_intervalIntegral t) (E.density_mass_eq_one)
  have hLHS : (∫ θ in a..b, E.dist.density θ * M.p θ)
      = (∫ θ in a..b, (θ * E.dist.density θ) * M.x θ)
        - (∫ s in a..b, M.x s * (1 - E.dist.cdf s))
        - M.interimUtil a := by
    rw [intervalIntegral.integral_of_le hab]
    have hpay : EqOn (fun θ => E.dist.density θ * M.p θ)
        (fun θ => ((θ * E.dist.density θ) * M.x θ
          - (∫ s in a..θ, M.x s) * E.dist.density θ)
          - M.interimUtil a * E.dist.density θ) (Ioc a b) := by
      intro θ hθ
      simp only
      rw [M.payment_eq_sub_rent hbic ⟨le_of_lt hθ.1, hθ.2⟩]; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpay,
      ← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_sub (hA.sub hB) hRent,
      intervalIntegral.integral_sub hA hB, hswap,
      intervalIntegral.integral_const_mul, E.density_mass_eq_one, mul_one]
  have hSurv : IntervalIntegrable (fun s => M.x s * (1 - E.dist.cdf s)) volume a b :=
    hxii.mul_continuousOn ((continuousOn_const.sub
      ((E.dist.cdf_continuous).continuousOn)))
  have hRHS : (∫ θ in a..b, E.dist.density θ * (E.virtualValue θ * M.x θ))
      = (∫ θ in a..b, (θ * E.dist.density θ) * M.x θ)
        - ∫ s in a..b, M.x s * (1 - E.dist.cdf s) := by
    rw [intervalIntegral.integral_of_le hab]
    have hfold : EqOn (fun θ => E.dist.density θ * (E.virtualValue θ * M.x θ))
        (fun θ => (θ * E.dist.density θ) * M.x θ - M.x θ * (1 - E.dist.cdf θ)) (Ioc a b) := by
      intro θ hθ
      have hpos : E.dist.density θ ≠ 0 :=
        ne_of_gt (E.density_pos θ ⟨le_of_lt hθ.1, hθ.2⟩)
      simp only [ScreeningEnv.virtualValue_def]
      field_simp
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hfold,
      ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_sub hA hSurv]
  rw [E.expect_eq_intervalIntegral M.p,
    E.expect_eq_intervalIntegral (fun θ => E.virtualValue θ * M.x θ), hLHS, hRHS]

/-- **Myerson revenue identity.** Under incentive compatibility with the lowest type's rent
normalized to zero, expected payment equals expected virtual surplus: `𝔼[p(θ)] = 𝔼[ψ(θ)·x(θ)]`. -/
theorem expected_revenue_eq_virtual_surplus (hbic : IsBIC M) (hU0 : M.interimUtil E.θlo = 0) :
    E.dist.expect M.p = E.dist.expect (fun θ => E.virtualValue θ * M.x θ) := by
  rw [M.expected_revenue_eq_virtual_surplus_sub_rent hbic, hU0, sub_zero]

/-- **Myerson revenue bound.** For any incentive-compatible, individually rational mechanism,
expected payment is at most expected virtual surplus: `𝔼[p(θ)] ≤ 𝔼[ψ(θ)·x(θ)]`. Individual
rationality forces the lowest type's rent `U(θlo) ≥ 0`, which is the only slack in the revenue
identity. This is the per-bidder engine of the optimal-auction upper bound over all admissible
mechanisms, not only the zero-rent-normalized ones. -/
theorem expected_revenue_le_virtual_surplus (hbic : IsBIC M) (hbir : IsBIR M) :
    E.dist.expect M.p ≤ E.dist.expect (fun θ => E.virtualValue θ * M.x θ) := by
  rw [M.expected_revenue_eq_virtual_surplus_sub_rent hbic]
  have hrent : 0 ≤ M.interimUtil E.θlo := hbir E.θlo E.θlo_mem_types
  linarith

end DirectMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
