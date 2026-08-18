import Mathlib
import Econlib

/-!
# Symmetric uniform IPV: order statistics, the first-price equilibrium, and revenue equivalence

The textbook symmetric independent-private-values benchmark: `n ≥ 2` bidders each draw a value
**uniformly on `[0, 1]`**. This file instantiates the Revenue Equivalence Theorem on the two
classic auction formats:

* `uniformSecondPrice` — the **second-price (Vickrey) auction**, an `AuctionMechanism` with
  its actual ex-post payment rule: highest value wins and pays the highest rival value (the
  second-highest value overall);
* `uniformFirstPrice` — the **direct reduced representation** of the first-price auction: highest
  value wins and pays the equilibrium bid `b(θ) = θ − θ/n` *of its reported value*. This is NOT the
  indirect first-price auction itself — in the indirect game messages are arbitrary bids `b' ∈ ℝ`
  and the winner pays its *submitted* bid. The indirect game and its symmetric Bayes–Nash
  equilibrium live in `FirstPriceGame.lean`; here they are surfaced as
  `uniformFirstPrice_isEquilibriumBid`, and the bridge
  `AuctionEnv.firstPriceMechanism_eq_equilibriumPayoff` (instantiated below as
  `uniformFirstPrice_eq_equilibriumPayoff`) shows this direct reduced mechanism is the indirect
  game played through the equilibrium schedule, so the revenue-equivalence comparison on the reduced
  object is faithful to the actual auction.

The ingredients:

* `highestValue_interimAlloc` — the shared highest-value allocation gives each bidder the interim
  winning probability `t ^ (n-1)`: conditional on value `t`, a bidder wins iff all `n − 1` rivals
  draw below `t` (the top order statistic, with `F(t) = t`).
* `firstPriceBid_eq` — the symmetric **first-price bid schedule** in closed form,
  `b(θ) = θ − θ / n = (n − 1)/n · θ`: shade your value by the factor `(n−1)/n` (the equilibrium
  property, for `n ≥ 2`, is `uniformFirstPrice_isEquilibriumBid`).
* `uniformFirstPrice_isEquilibriumBid` — the **Bayes–Nash equilibrium** of the indirect
  first-price auction: against rivals bidding `b`, a type-`θ` bidder weakly prefers its own bid
  `b(θ)` to *every* bid `b' ∈ ℝ` — on-path mimicry bids, underbids, and overbids alike (the general
  statement and the underbid/overbid analysis live in `FirstPriceGame.lean`).
* `uniformFirstPrice_isBIC` / `uniformSecondPrice_isBIC` — both formats are Bayesian incentive
  compatible *as direct mechanisms* (the second-price side by ex-post Vickrey dominance), and both
  leave the lowest type zero rent.

The conclusions:

* `firstPrice_secondPrice_payment_equivalence` — **Revenue Equivalence, instantiated**: the two
  formats charge identical interim payments throughout `[0, 1]`.
* `uniformFirstPrice_interimPay_eq` / `uniformSecondPrice_interimPay_eq` — the common interim
  payment in closed form: `t^n − t^n/n`. For the first-price auction this is `b(t) · t^{n-1}`; for
  the second-price auction it is the expected second-highest value on the winning event.
* `firstPrice_secondPrice_expectedRevenue_eq` — integrating the equal interim payments against
  the common type law: the two formats raise the **same expected revenue**.

The generic wrapper `revenueEquivalence` (any two BIC auctions implementing `t ^ (n-1)` with the
same lowest-type rent charge equal interim payments) is kept as the abstract statement that the
instantiation above feeds.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.UniformRevenueEquivalence

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.Probability
open Set MeasureTheory

/-- The uniform-`[0, 1]` per-bidder screening environment. -/
def uniformBase : ScreeningEnv := ScreeningEnv.uniform 0 1 (by norm_num)

@[simp] lemma uniformBase_θlo : uniformBase.θlo = 0 := rfl
@[simp] lemma uniformBase_θhi : uniformBase.θhi = 1 := rfl

/-- On `[0, 1]` the uniform CDF is the identity: `F(x) = x`. -/
lemma uniformBase_cdf {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : uniformBase.dist.cdf x = x := by
  rw [uniformBase, ScreeningEnv.uniform_dist, ContDist.uniform_cdf_of_mem 0 1 (by norm_num) hx]
  ring

/-- The symmetric `n`-bidder uniform-`[0, 1]` IPV auction. -/
def uniformAuction (n : ℕ) (hn : 0 < n) : AuctionEnv where
  n := n
  hn := hn
  base := uniformBase

@[simp] lemma uniformAuction_base (n : ℕ) (hn : 0 < n) : (uniformAuction n hn).base = uniformBase :=
  rfl

@[simp] lemma uniformAuction_n (n : ℕ) (hn : 0 < n) : (uniformAuction n hn).n = n := rfl

/-! ## The order-statistic interim allocation -/

/-- **The highest-value allocation's interim form is the top order statistic `t ^ (n-1)`.**
Awarding the unit to the highest value, bidder `i` wins with probability
`F(t) ^ (n-1) = t ^ (n-1)` conditional on its own value `t ∈ [0, 1]`. This is a statement about
the *allocation* only — it is shared by every efficient format (second-price, first-price,
all-pay, …); the payment rules differ. -/
theorem highestValue_interimAlloc (n : ℕ) (hn : 0 < n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformAuction n hn).highestValueAlloc.interimAlloc i t = t ^ (n - 1) := by
  rw [AuctionEnv.highestValueAlloc_interimAlloc, uniformAuction_base, uniformAuction_n,
    uniformBase_cdf ht]

/-! ## The first-price equilibrium bid -/

/-- **The symmetric first-price bid schedule for the uniform type**, in closed form:
`b(θ) = θ − θ / n = (n − 1)/n · θ`. This is the schedule `ScreeningEnv.firstPriceBid`; it is the
*equilibrium* bid for `n ≥ 2` — that property is `uniformFirstPrice_isEquilibriumBid`, not this
closed-form computation (which holds already for `1 ≤ n`). -/
theorem firstPriceBid_eq (n : ℕ) (hn : 1 ≤ n) {θ : ℝ} (hθ : θ ∈ Ioc (0 : ℝ) 1) :
    uniformBase.firstPriceBid n θ = θ - θ / n := by
  have hθ0 : 0 < θ := hθ.1
  have hcdfθ : uniformBase.dist.cdf θ = θ := uniformBase_cdf ⟨hθ0.le, hθ.2⟩
  have hexp : n - 1 + 1 = n := by omega
  -- The numerator integral is `∫_0^θ s^{n-1} = θ^n / n` (the CDF is the identity on `[0, θ]`).
  have hint : (∫ s in (0 : ℝ)..θ, uniformBase.dist.cdf s ^ (n - 1)) = θ ^ n / n := by
    have hcong : (∫ s in (0 : ℝ)..θ, uniformBase.dist.cdf s ^ (n - 1))
        = ∫ s in (0 : ℝ)..θ, s ^ (n - 1) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le hθ0.le] at hs
      rw [uniformBase_cdf ⟨hs.1, le_trans hs.2 hθ.2⟩]
    rw [hcong, integral_pow, hexp, zero_pow (show n ≠ 0 by omega), sub_zero]
    congr 1
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [ScreeningEnv.firstPriceBid, uniformBase_θlo, hcdfθ, hint]
  have hθn : (θ : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hθ0)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show θ ^ n = θ ^ (n - 1) * θ by rw [← pow_succ, hexp]]
  field_simp

/-- **`b(θ)` is a Bayes–Nash equilibrium bid** of the indirect uniform first-price auction: against
rivals bidding the symmetric schedule `b`, a type-`θ` bidder weakly prefers its own bid `b(θ)` to
*every* bid `b' ∈ ℝ` — not merely the on-path mimicry bids `b(z)`, but also underbids (which never
win) and overbids above `b(1)` (which only overpay). This is the equilibrium statement,
`firstPriceBid_isEquilibriumBid` instantiated on the uniform environment; the underbid/overbid
analysis is carried out once and for all in `FirstPriceGame.lean`. -/
theorem uniformFirstPrice_isEquilibriumBid (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    (uniformAuction n hn).IsBestBid i θ (uniformBase.firstPriceBid n θ) :=
  (uniformAuction n hn).firstPriceBid_isEquilibriumBid hn2 i hθ

/-! ## The two formats as auction mechanisms -/

/-- The **direct reduced representation** of the first-price auction on the uniform environment:
highest value wins and pays the equilibrium bid `b(θ)` *of its reported value*. This is the
reduced/direct object (a `DirectMechanism`-style `AuctionMechanism`), not the indirect first-price
auction whose messages are arbitrary bids and whose winner pays its submitted bid; the indirect game
and its equilibrium are in `FirstPriceGame.lean` (see `uniformFirstPrice_isEquilibriumBid` and the
`uniformFirstPrice_eq_equilibriumPayoff` bridge below). -/
abbrev uniformFirstPrice (n : ℕ) (hn : 0 < n) : AuctionMechanism (uniformAuction n hn) :=
  (uniformAuction n hn).firstPriceMechanism

/-- **The reduced first-price mechanism is the indirect game played through the equilibrium.** A
type-`θ` bidder's truthful interim utility in `uniformFirstPrice` equals its equilibrium interim
payoff in the indirect uniform first-price game — the `firstPriceMechanism = Γ ∘ σ` bridge
(`AuctionEnv.firstPriceMechanism_eq_equilibriumPayoff`) on the uniform environment. This is what
makes the revenue-equivalence comparison on the direct reduced object faithful to the actual
indirect auction (arbitrary bids, pay-your-bid). -/
theorem uniformFirstPrice_eq_equilibriumPayoff (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ((uniformFirstPrice n hn).reducedMechanism i).reportUtil θ θ
      = (uniformAuction n hn).firstPriceDevPayoff i θ (uniformBase.firstPriceBid n θ) :=
  (uniformAuction n hn).firstPriceMechanism_eq_equilibriumPayoff hn2 i hθ

/-- The **second-price (Vickrey) auction** on the uniform environment: highest value wins, pays
the highest rival value. -/
abbrev uniformSecondPrice (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) :
    AuctionMechanism (uniformAuction n hn) :=
  (uniformAuction n hn).secondPriceMechanism hn2

/-- The first-price auction's interim allocation is the top order statistic `t ^ (n-1)`. -/
theorem uniformFirstPrice_interimAlloc (n : ℕ) (hn : 0 < n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformFirstPrice n hn).alloc.interimAlloc i t = t ^ (n - 1) := by
  rw [AuctionEnv.firstPriceMechanism_alloc]
  exact highestValue_interimAlloc n hn i ht

/-- The second-price auction's interim allocation is the same top order statistic `t ^ (n-1)`. -/
theorem uniformSecondPrice_interimAlloc (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformSecondPrice n hn hn2).alloc.interimAlloc i t = t ^ (n - 1) := by
  rw [AuctionEnv.secondPriceMechanism_alloc]
  exact highestValue_interimAlloc n hn i ht

/-- **The first-price auction is Bayesian incentive compatible** (the equilibrium bid is a best
response; `firstPriceMechanism_isBIC` instantiated). -/
theorem uniformFirstPrice_isBIC (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) :
    (uniformFirstPrice n hn).IsBIC :=
  (uniformAuction n hn).firstPriceMechanism_isBIC hn2

/-- **The second-price auction is Bayesian incentive compatible** — by the ex-post Vickrey
dominance argument (`secondPriceMechanism_isBIC` instantiated). -/
theorem uniformSecondPrice_isBIC (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) :
    (uniformSecondPrice n hn hn2).IsBIC :=
  (uniformAuction n hn).secondPriceMechanism_isBIC hn2

/-! ## Revenue equivalence, instantiated -/

/-- **Revenue Equivalence Theorem, instantiated on the two classic formats.** The first-price and
second-price auctions charge identical interim payments to every bidder throughout `[0, 1]`: both
are BIC, both award the unit through the same highest-value allocation (so both implement the
order-statistic interim allocation `t ^ (n-1)`), and both leave the lowest type zero rent. -/
theorem firstPrice_secondPrice_payment_equivalence (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformFirstPrice n hn).interimPay i t = (uniformSecondPrice n hn hn2).interimPay i t := by
  refine AuctionMechanism.revenue_equivalence (uniformFirstPrice_isBIC n hn hn2)
    (uniformSecondPrice_isBIC n hn hn2)
    -- Both mechanisms carry literally the same ex-post allocation.
    (fun _j _s _hs => rfl) (fun j => ?_) i ht
  rw [AuctionEnv.firstPriceMechanism_interimUtil_θlo,
    AuctionEnv.secondPriceMechanism_interimUtil_θlo hn2]

/-- **The first-price interim payment in closed form**: `b(t) · t^{n-1} = t^n − t^n/n`. -/
theorem uniformFirstPrice_interimPay_eq (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformFirstPrice n hn).interimPay i t = t ^ n - t ^ n / n := by
  rw [AuctionEnv.firstPriceMechanism_interimPay, uniformAuction_base, uniformAuction_n,
    uniformBase_cdf ht]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · -- At `t = 0` both sides vanish: the lowest type never wins.
    rw [← h0, zero_pow (show n - 1 ≠ 0 by omega), mul_zero,
      zero_pow (show n ≠ 0 by omega), zero_div, sub_zero]
  · rw [firstPriceBid_eq n (by omega) ⟨h0, ht.2⟩]
    have ht_pow : t * t ^ (n - 1) = t ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    rw [sub_mul, ht_pow, div_mul_eq_mul_div, ht_pow]

/-- **The second-price interim payment in closed form**: the expected second-highest value on the
winning event is also `t^n − t^n/n` — for the uniform, `𝔼[max rival ∣ win] · P(win)
= ((n−1)/n · t) · t^{n-1}`. Immediate from payment equivalence and the first-price closed form. -/
theorem uniformSecondPrice_interimPay_eq (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (uniformSecondPrice n hn hn2).interimPay i t = t ^ n - t ^ n / n := by
  rw [← firstPrice_secondPrice_payment_equivalence n hn hn2 i ht]
  exact uniformFirstPrice_interimPay_eq n hn hn2 i ht

/-- **Equal expected revenue.** Integrating the equal interim payments against the common type law
and summing over bidders: the first-price and second-price auctions raise the same expected
revenue. -/
theorem firstPrice_secondPrice_expectedRevenue_eq (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) :
    (∫ θ, ∑ i, (uniformFirstPrice n hn).pay θ i ∂(uniformAuction n hn).jointLaw)
      = ∫ θ, ∑ i, (uniformSecondPrice n hn hn2).pay θ i ∂(uniformAuction n hn).jointLaw := by
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => (uniformFirstPrice n hn).pay_integrable i),
    MeasureTheory.integral_finset_sum _
      (fun i _ => (uniformSecondPrice n hn hn2).pay_integrable i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AuctionMechanism.expected_interimPay_eq, AuctionMechanism.expected_interimPay_eq,
    ScreeningEnv.expect_eq_intervalIntegral, ScreeningEnv.expect_eq_intervalIntegral]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le (uniformAuction n hn).base.hθ.le] at hs
  dsimp only
  rw [firstPrice_secondPrice_payment_equivalence n hn hn2 i hs]

/-! ## The abstract wrapper -/

/-- **Revenue Equivalence Theorem (uniform IPV), abstract form.** Two incentive-compatible
auctions that both implement the order-statistic interim allocation `t ^ (n-1)` and give the
lowest type the same rent charge identical interim payments. The instantiated version above
feeds `uniformFirstPrice` and `uniformSecondPrice` (both zero-rent) through this statement. -/
theorem revenueEquivalence (n : ℕ) (hn : 0 < n)
    {M₁ M₂ : AuctionMechanism (uniformAuction n hn)} (h₁ : M₁.IsBIC) (h₂ : M₂.IsBIC)
    (hx₁ : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, M₁.alloc.interimAlloc i t = t ^ (n - 1))
    (hx₂ : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, M₂.alloc.interimAlloc i t = t ^ (n - 1))
    (hU0 : ∀ i, (M₁.reducedMechanism i).interimUtil (uniformAuction n hn).base.θlo
            = (M₂.reducedMechanism i).interimUtil (uniformAuction n hn).base.θlo)
    (i : Fin (uniformAuction n hn).n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    M₁.interimPay i t = M₂.interimPay i t := by
  refine AuctionMechanism.revenue_equivalence h₁ h₂ (fun j s hs => ?_) hU0 i ht
  rw [hx₁ j s hs, hx₂ j s hs]

end EconlibExamples.MechanismDesign.UniformRevenueEquivalence
