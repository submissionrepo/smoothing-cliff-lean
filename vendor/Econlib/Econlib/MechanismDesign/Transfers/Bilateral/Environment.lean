/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Environment

/-!
# Bilateral trade: Environment, mechanisms, and solution concepts

The **Myerson–Satterthwaite** bilateral-trade model. A single buyer with private value `θ_b ~ F_b`
and a single seller with private cost `θ_s ~ F_s` may trade one unit. A direct mechanism specifies
a trade probability `trade θ_b θ_s ∈ [0,1]` and (interim) transfers — `payBuyer` out of the buyer,
`paySeller` into the seller — and each agent's **reduced form** integrates out the other's type
against its distribution. Each agent then faces a single-parameter screening problem.

The two private types are drawn independently, so the **joint law** is the product
`jointLaw = F_b ⊗ F_s` on `ℝ × ℝ`. The transfers are required to be jointly measurable and jointly
integrable against this product law (`payBuyer_jointMeasurable`/`payBuyer_jointIntegrable` and
their seller analogs), in addition to the one-dimensional reduced-form integrability that makes
each interim payment a per-report expectation. The joint fields let Fubini read budget balance as a
single ex-ante product-measure expectation rather than an iterated reduced-form inequality.

The supports overlap (`hlo`, `hhi`): Sometimes the buyer's value exceeds the seller's cost (trade
is efficient) and sometimes not.

## Main definitions

* `BilateralEnv` — buyer and seller `ScreeningEnv`s with overlapping supports.
* `BilateralEnv.jointLaw` — the product law `F_b ⊗ F_s` of the two independent private types.
* `BilateralMechanism` — trade rule and the two transfer schedules (bounded/measurable, with both
  reduced-form one-dimensional integrability and joint measurability/integrability under
  `jointLaw`).
* reduced forms `buyerInterimTrade`/`buyerInterimPay`/`sellerInterimTrade`/`sellerInterimRecv` and
  interim utilities `buyerUtil`/`sellerUtil`.
* `BuyerBIC`/`SellerBIC`, `BuyerIR`/`SellerIR`, `Efficient`, `WeaklyBudgetBalanced` — the four
  desiderata of the impossibility theorem.
* `BudgetBalancedExAnte` — weak budget balance as the ex-ante product-measure expectation
  `0 ≤ ∫ (payBuyer − paySeller) ∂jointLaw`, shown equivalent to `WeaklyBudgetBalanced` via Fubini.

## Main statements

* `weaklyBudgetBalanced_iff_budgetBalancedExAnte` — the Fubini equivalence: The iterated
  reduced-form budget condition equals the single product-measure expectation of
  `payBuyer − paySeller`.

## References

* Myerson, Roger B., and Mark A. Satterthwaite. 1983. “Efficient Mechanisms for Bilateral Trading.”
  *Journal of Economic Theory* 29 (2): 265–81. [https://doi.org/10.1016/0022-0531(83)90048-0](https://doi.org/10.1016/0022-0531(83)90048-0).

## Tags

bilateral trade, myerson-satterthwaite, screening, budget balance, incentive compatibility
-/

@[expose] public section

open Set MeasureTheory Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.Bilateral

open Econlib.MechanismDesign.Transfers.SingleParameter

/-- A **bilateral-trade environment**: A buyer and a seller, each a single-parameter screening
environment, with overlapping type supports so that efficient trade is sometimes profitable and
sometimes not. -/
structure BilateralEnv where
  /-- The buyer's value environment. -/
  buyer : ScreeningEnv
  /-- The seller's cost environment. -/
  seller : ScreeningEnv
  /-- The seller's lowest cost is below the buyer's highest value: Efficient trade can occur. -/
  hlo : seller.θlo < buyer.θhi
  /-- The buyer's lowest value is below the seller's highest cost: Efficient no-trade can occur. -/
  hhi : buyer.θlo < seller.θhi

namespace BilateralEnv

variable (Γ : BilateralEnv)

/-- The **joint law** of the two independent private types: The product `F_b ⊗ F_s` of the buyer's
and the seller's type laws on `ℝ × ℝ`. The transfers' ex-ante (double-integral) expectations are
taken against this measure. -/
def jointLaw : Measure (ℝ × ℝ) := Γ.buyer.dist.toMeasure.prod Γ.seller.dist.toMeasure

@[simp] lemma jointLaw_def :
    Γ.jointLaw = Γ.buyer.dist.toMeasure.prod Γ.seller.dist.toMeasure := rfl

instance : IsProbabilityMeasure Γ.jointLaw := by
  haveI := Γ.buyer.dist.toMeasure_isProbability
  haveI := Γ.seller.dist.toMeasure_isProbability
  rw [jointLaw_def]; infer_instance

/-- A **direct bilateral mechanism**: A trade probability and two transfer schedules. The trade
rule is bounded in `[0,1]` and (separately) measurable in each argument. The transfers carry both
one-dimensional reduced-form integrability (`payBuyer_integrable`/`paySeller_integrable`, against
the other agent's density, so each interim payment is a per-report expectation at every report) and
joint measurability/integrability under the product law
(`payBuyer_jointMeasurable`/`payBuyer_jointIntegrable` and seller analogs). The joint fields give
the ex-ante (double-integral) expectations of the transfers a well-defined value, so weak budget
balance is a product-measure expectation whose Fubini swap between the buyer-first and seller-first
iterated integrals is justified. -/
structure Mechanism where
  /-- Probability of trade at the reported `(value, cost)` pair. -/
  trade : ℝ → ℝ → ℝ
  /-- Trade probabilities are nonnegative. -/
  trade_nonneg : ∀ θb θs, 0 ≤ trade θb θs
  /-- Trade probabilities are at most one. -/
  trade_le_one : ∀ θb θs, trade θb θs ≤ 1
  /-- The trade rule is measurable in the buyer's value (for the seller's reduced form). -/
  trade_measurable_buyer : ∀ θs, Measurable (fun θb => trade θb θs)
  /-- The trade rule is measurable in the seller's cost (for the buyer's reduced form). -/
  trade_measurable_seller : ∀ θb, Measurable (fun θs => trade θb θs)
  /-- The buyer's payment schedule (money out of the buyer). -/
  payBuyer : ℝ → ℝ → ℝ
  /-- The seller's receipt schedule (money into the seller). -/
  paySeller : ℝ → ℝ → ℝ
  /-- The buyer's payment is integrable against the seller's density, for each buyer value. -/
  payBuyer_integrable : ∀ θb, Integrable (fun θs => Γ.seller.dist.density θs * payBuyer θb θs)
  /-- The seller's receipt is integrable against the buyer's density, for each seller cost. -/
  paySeller_integrable : ∀ θs, Integrable (fun θb => Γ.buyer.dist.density θb * paySeller θb θs)
  /-- The buyer's payment is **jointly measurable** in the `(value, cost)` pair. -/
  payBuyer_jointMeasurable : Measurable (fun θ : ℝ × ℝ => payBuyer θ.1 θ.2)
  /-- The seller's receipt is **jointly measurable** in the `(value, cost)` pair. -/
  paySeller_jointMeasurable : Measurable (fun θ : ℝ × ℝ => paySeller θ.1 θ.2)
  /-- The buyer's payment is **jointly integrable** under the product law `F_b ⊗ F_s`, so its
  ex-ante (double-integral) expectation exists and Fubini applies. -/
  payBuyer_jointIntegrable : Integrable (fun θ : ℝ × ℝ => payBuyer θ.1 θ.2) Γ.jointLaw
  /-- The seller's receipt is **jointly integrable** under the product law `F_b ⊗ F_s`, so its
  ex-ante (double-integral) expectation exists and Fubini applies. -/
  paySeller_jointIntegrable : Integrable (fun θ : ℝ × ℝ => paySeller θ.1 θ.2) Γ.jointLaw

namespace Mechanism

variable {Γ} (M : Γ.Mechanism)

/-- Buyer's **interim trade probability** `Q_b(θ_b) = 𝔼_{θ_s}[trade θ_b θ_s]`. -/
def buyerInterimTrade (θb : ℝ) : ℝ := Γ.seller.dist.expect (fun θs => M.trade θb θs)

/-- Buyer's **interim expected payment** `P_b(θ_b) = 𝔼_{θ_s}[payBuyer θ_b θ_s]`. -/
def buyerInterimPay (θb : ℝ) : ℝ := Γ.seller.dist.expect (fun θs => M.payBuyer θb θs)

/-- Seller's **interim trade probability** `Q_s(θ_s) = 𝔼_{θ_b}[trade θ_b θ_s]`. -/
def sellerInterimTrade (θs : ℝ) : ℝ := Γ.buyer.dist.expect (fun θb => M.trade θb θs)

/-- Seller's **interim expected receipt** `P_s(θ_s) = 𝔼_{θ_b}[paySeller θ_b θ_s]`. -/
def sellerInterimRecv (θs : ℝ) : ℝ := Γ.buyer.dist.expect (fun θb => M.paySeller θb θs)

/-- Buyer's interim utility `U_b(θ_b) = θ_b · Q_b(θ_b) − P_b(θ_b)`. -/
def buyerUtil (θb : ℝ) : ℝ := θb * M.buyerInterimTrade θb - M.buyerInterimPay θb

/-- Seller's interim utility `U_s(θ_s) = P_s(θ_s) − θ_s · Q_s(θ_s)`. -/
def sellerUtil (θs : ℝ) : ℝ := M.sellerInterimRecv θs - θs * M.sellerInterimTrade θs

/-- **Buyer incentive compatibility**: Truthful reporting is interim-optimal for the buyer. -/
def BuyerBIC : Prop :=
  ∀ θb ∈ Γ.buyer.types, ∀ θb' ∈ Γ.buyer.types,
    θb * M.buyerInterimTrade θb' - M.buyerInterimPay θb' ≤ M.buyerUtil θb

/-- **Seller incentive compatibility**: Truthful reporting is interim-optimal for the seller. -/
def SellerBIC : Prop :=
  ∀ θs ∈ Γ.seller.types, ∀ θs' ∈ Γ.seller.types,
    M.sellerInterimRecv θs' - θs * M.sellerInterimTrade θs' ≤ M.sellerUtil θs

/-- **Buyer individual rationality**: Every buyer type's interim utility is nonnegative. -/
def BuyerIR : Prop := ∀ θb ∈ Γ.buyer.types, 0 ≤ M.buyerUtil θb

/-- **Seller individual rationality**: Every seller type's interim utility is nonnegative. -/
def SellerIR : Prop := ∀ θs ∈ Γ.seller.types, 0 ≤ M.sellerUtil θs

/-- **Ex-post efficiency**: Trade occurs exactly when the buyer's value covers the seller's cost. -/
def Efficient : Prop :=
  ∀ θb ∈ Γ.buyer.types, ∀ θs ∈ Γ.seller.types, M.trade θb θs = if θs ≤ θb then 1 else 0

/-- **Weak budget balance**: The buyer's expected payment covers the seller's expected receipt —
the mechanism needs no outside subsidy. Stated as the iterated reduced-form inequality; under the
joint-integrability fields it is equivalent to the ex-ante product-measure expectation
`BudgetBalancedExAnte` via Fubini (`weaklyBudgetBalanced_iff_budgetBalancedExAnte`). -/
def WeaklyBudgetBalanced : Prop :=
  Γ.seller.dist.expect M.sellerInterimRecv ≤ Γ.buyer.dist.expect M.buyerInterimPay

/-- **Buyer's ex-ante expected payment as a single product integral.** The aggregate buyer payment
`𝔼_{θ_b}[𝔼_{θ_s}[payBuyer]]` equals the double integral of `payBuyer` against the joint law, by
Fubini (`integral_prod`) using `payBuyer_jointIntegrable`. -/
lemma buyerPay_total_eq :
    Γ.buyer.dist.expect M.buyerInterimPay = ∫ θ, M.payBuyer θ.1 θ.2 ∂Γ.jointLaw := by
  haveI := Γ.buyer.dist.toMeasure_isProbability
  haveI := Γ.seller.dist.toMeasure_isProbability
  rw [jointLaw_def, integral_prod _ M.payBuyer_jointIntegrable,
    Γ.buyer.dist.expect_eq_measure_integral]
  refine integral_congr_ae (ae_of_all _ fun θb => ?_)
  exact Γ.seller.dist.expect_eq_measure_integral (fun θs => M.payBuyer θb θs)

/-- **Seller's ex-ante expected receipt as a single product integral.** The aggregate seller
receipt `𝔼_{θ_s}[𝔼_{θ_b}[paySeller]]` equals the double integral of `paySeller` against the joint
law, by Fubini in the seller-first order (`integral_prod_symm`) using
`paySeller_jointIntegrable`. -/
lemma sellerRecv_total_eq :
    Γ.seller.dist.expect M.sellerInterimRecv = ∫ θ, M.paySeller θ.1 θ.2 ∂Γ.jointLaw := by
  haveI := Γ.buyer.dist.toMeasure_isProbability
  haveI := Γ.seller.dist.toMeasure_isProbability
  rw [jointLaw_def, integral_prod_symm _ M.paySeller_jointIntegrable,
    Γ.seller.dist.expect_eq_measure_integral]
  refine integral_congr_ae (ae_of_all _ fun θs => ?_)
  exact Γ.buyer.dist.expect_eq_measure_integral (fun θb => M.paySeller θb θs)

/-- **Ex-ante weak budget balance**: The ex-ante (double-integral) net transfer is nonnegative —
the buyer's payment covers the seller's receipt as a single expectation against the product law
`F_b ⊗ F_s`, not merely as an iterated reduced-form inequality.
`weaklyBudgetBalanced_iff_budgetBalancedExAnte` shows it agrees with `WeaklyBudgetBalanced`. -/
def BudgetBalancedExAnte : Prop :=
  0 ≤ ∫ θ, (M.payBuyer θ.1 θ.2 - M.paySeller θ.1 θ.2) ∂Γ.jointLaw

/-- **Fubini bridge for budget balance.** The iterated reduced-form budget condition
`WeaklyBudgetBalanced` (seller's expected receipt ≤ buyer's expected payment) is equivalent to the
ex-ante product-measure expectation `BudgetBalancedExAnte`
(`0 ≤ ∫ (payBuyer − paySeller) ∂jointLaw`). -/
lemma weaklyBudgetBalanced_iff_budgetBalancedExAnte :
    M.WeaklyBudgetBalanced ↔ M.BudgetBalancedExAnte := by
  rw [WeaklyBudgetBalanced, BudgetBalancedExAnte, M.buyerPay_total_eq, M.sellerRecv_total_eq,
    integral_sub M.payBuyer_jointIntegrable M.paySeller_jointIntegrable, sub_nonneg]

end Mechanism

end BilateralEnv

end Econlib.MechanismDesign.Transfers.Bilateral
