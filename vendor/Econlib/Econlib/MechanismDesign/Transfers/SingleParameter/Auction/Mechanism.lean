/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.ReducedForm
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Incentive

/-!
# Auction mechanisms and incentive compatibility

A **direct auction mechanism** adds a per-bidder payment schedule to an ex-post allocation. Each
bidder's interim problem — its winning probability and expected payment as a function of its own
report — is a single-agent screening mechanism (`reducedMechanism`). Incentive compatibility
(`IsBIC`) holds when every bidder's reduced mechanism is single-agent BIC (the Myerson 1981 interim
reduction).

## Main definitions

* `AuctionMechanism` — an `ExPostAlloc` plus a measurable, integrable payment schedule. The payment
  schedule additionally carries reportwise measurability and integrability of the report-spliced
  integrand, so the interim payment is a well-defined expectation at every report, not merely
  almost everywhere.
* `AuctionMechanism.interimPay` — bidder `i`'s expected payment as a function of its own type.
* `AuctionMechanism.reducedMechanism` — bidder `i`'s interim problem as a screening mechanism.
* `AuctionMechanism.IsBIC` — Bayesian incentive compatibility.
* `AuctionMechanism.IsBIR` — Bayesian individual rationality.

## Main statements

* `AuctionMechanism.interimPay_measurable` — the interim payment is measurable as a function of the
  own report.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, mechanism design, incentive compatibility, interim reduction
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

/-- A **direct auction mechanism**: An ex-post allocation together with a per-bidder payment
schedule. The payment carries both profilewise regularity (`pay_measurable`/`pay_integrable`, so
the unconditional expected payment exists) and reportwise regularity
(`pay_measurable_update`/`pay_integrable_update`, so the report-spliced integrand defining
`interimPay i t` is integrable at every own report `t`, not just almost everywhere). Without the
latter, the Bochner integral defining `interimPay i t` would silently return `0` at reports where
the spliced integrand fails to be integrable, yet downstream `reducedMechanism`/`IsBIC` read
`interimPay` as a per-report payment schedule for every `t`. -/
structure AuctionMechanism (A : AuctionEnv) where
  /-- The ex-post allocation rule. -/
  alloc : ExPostAlloc A
  /-- `pay θ i` is the payment made by bidder `i` at profile `θ`. -/
  pay : A.Profile → Fin A.n → ℝ
  /-- Each bidder's payment is measurable in the profile. -/
  pay_measurable : ∀ i, Measurable (fun θ => pay θ i)
  /-- Each bidder's payment is integrable against the joint law (its expected payment exists). -/
  pay_integrable : ∀ i, Integrable (fun θ => pay θ i) A.jointLaw
  /-- Each bidder's report-spliced payment is measurable in the others' profile, for every own
  report `t`. -/
  pay_measurable_update : ∀ (i : Fin A.n) (t : ℝ), Measurable (fun θ => pay (update θ i t) i)
  /-- Each bidder's report-spliced payment is integrable against the joint law, for every own
  report `t` (so `interimPay i t` is a well-defined expectation at every report, not only a.e.). -/
  pay_integrable_update : ∀ (i : Fin A.n) (t : ℝ),
    Integrable (fun θ => pay (update θ i t) i) A.jointLaw

namespace AuctionMechanism

variable {A : AuctionEnv} (M : AuctionMechanism A)

/-- **Reduced-form interim payment** of bidder `i`: Its expected payment as a function of its own
reported type, averaging over the other bidders' types. -/
def interimPay (i : Fin A.n) (t : ℝ) : ℝ :=
  ∫ θ, M.pay (update θ i t) i ∂A.jointLaw

lemma interimPay_def (i : Fin A.n) (t : ℝ) :
    M.interimPay i t = ∫ θ, M.pay (update θ i t) i ∂A.jointLaw := rfl

/-- The interim-payment integrand is measurable at every own report. The reportwise field
`pay_measurable_update` exposed at the `interimPay` level: It certifies the integrand
`θ ↦ pay (update θ i t) i` averaged by `interimPay i t` is measurable. -/
lemma interimPay_integrand_measurable (i : Fin A.n) (t : ℝ) :
    Measurable (fun θ => M.pay (update θ i t) i) :=
  M.pay_measurable_update i t

/-- The interim-payment integrand is integrable at every own report, so `interimPay i t` is a
well-defined expectation — not a silent `0` returned by the Bochner integral of a non-integrable
integrand — for every report `t`. This is the reportwise contract `pay_integrable_update` that
supports the pointwise per-report reading of `interimPay`, consumed by `reducedMechanism` and
`IsBIC` at every `t`, not merely a.e. -/
lemma interimPay_integrand_integrable (i : Fin A.n) (t : ℝ) :
    Integrable (fun θ => M.pay (update θ i t) i) A.jointLaw :=
  M.pay_integrable_update i t

/-- The interim payment is measurable as a function of the own report. The reduced-form payment
`interimPay i` integrates the report-spliced payment against the others' joint law; jointly in
`(t, θ)` the spliced map `θ ↦ pay (update θ i t) i` is measurable, so its partial integral in the
own report is measurable. This makes the own-type expectation `𝔼_t[interimPay i t]` (the
reduced-form revenue, `RevenueIdentity`) a well-defined integral over the own-type marginal rather
than a silent `0`. -/
lemma interimPay_measurable (i : Fin A.n) : Measurable (M.interimPay i) := by
  -- Joint measurability of `(t, θ) ↦ pay (update θ i t) i`, from the profilewise field, splices the
  -- own report into coordinate `i` and reads off coordinate `i` of `pay`.
  have hupd : Measurable (fun p : ℝ × A.Profile => Function.update p.2 i p.1) :=
    measurable_update'.comp measurable_swap
  have hjoint : Measurable (fun p : ℝ × A.Profile => M.pay (Function.update p.2 i p.1) i) :=
    (M.pay_measurable i).comp hupd
  exact (hjoint.stronglyMeasurable.integral_prod_right' (ν := A.jointLaw)).measurable

/-- Bidder `i`'s **reduced (interim) mechanism**: A single-agent screening mechanism on the shared
environment, with the reduced-form allocation and the reduced-form payment. -/
def reducedMechanism (i : Fin A.n) : DirectMechanism A.base where
  alloc := M.alloc.reducedAlloc i
  p := M.interimPay i

@[simp] lemma reducedMechanism_x (i : Fin A.n) (t : ℝ) :
    (M.reducedMechanism i).x t = M.alloc.interimAlloc i t := rfl

@[simp] lemma reducedMechanism_p (i : Fin A.n) :
    (M.reducedMechanism i).p = M.interimPay i := rfl

/-- **Bayesian incentive compatibility**: Truthful reporting is optimal for every bidder. -/
def IsBIC : Prop := ∀ i, SingleParameter.IsBIC (M.reducedMechanism i)

/-- **Bayesian individual rationality**: Every bidder's reduced mechanism is IR. -/
def IsBIR : Prop := ∀ i, SingleParameter.IsBIR (M.reducedMechanism i)

end AuctionMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
