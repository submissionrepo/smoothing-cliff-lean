/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Achievable
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.RevenueEquivalence

/-!
# Symmetric IID auctions: The second-price (Vickrey) auction mechanism

The **second-price auction** (Vickrey 1961) as an `AuctionMechanism` with ex-post Vickrey payments:
The unit goes to the highest-value bidder (the shared `highestValueAlloc`), and the winner pays the
**highest rival value** `rivalMax` — the second-highest value overall.

Incentive compatibility comes from the pointwise Vickrey dominance argument: For every fixed
profile of rival values, truthful reporting maximizes the ex-post payoff `(θ − rivalMax) · 𝟙{win}`
— winning is desirable exactly when the value clears the price, and the price does not depend on
the own report. Integrating the pointwise dominance over the rivals' law yields `IsBIC` directly,
with no order-statistic computation.

The interim payment identity then follows from revenue equivalence: The second-price auction and
the Myerson mechanism of the same allocation are both BIC with zero rent at the lowest type and
share the allocation, so their interim payments coincide — i.e.
`𝔼[top rival value · 𝟙{win} ∣ θᵢ = t] = t·F(t)^{n-1} − ∫_{θlo}^t F(s)^{n-1} ds`, the
expected-second-order-statistic identity, obtained without integrating the order statistic.

## Main definitions

* `AuctionEnv.rivalMax` — the highest rival value (requires `2 ≤ n`).
* `AuctionEnv.secondPriceMechanism` — `highestValueAlloc` paired with pay-the-second-price.

## Main statements

* `secondPrice_pointwise_dominance` — ex-post Vickrey dominance of truthful reporting;
* `secondPriceMechanism_isBIC` — the second-price auction is Bayesian incentive compatible;
* `secondPriceMechanism_interimUtil_θlo` — the lowest type earns no rent;
* `secondPriceMechanism_interimPay_eq_myersonPayment` — the Vickrey interim payment is the Myerson
  payment of the highest-value allocation.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).

## Tags

auction, second-price, vickrey, mechanism, incentive compatibility, revenue equivalence
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionEnv

variable (A : AuctionEnv)

/-- With at least two bidders, every bidder has a rival. -/
lemma erase_nonempty (hn : 2 ≤ A.n) (i : Fin A.n) : (Finset.univ.erase i).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The **highest rival value**: The maximum of the other bidders' values — with the winner being
the top value, the second-highest value overall. -/
def rivalMax (hn : 2 ≤ A.n) (θ : A.Profile) (i : Fin A.n) : ℝ :=
  (Finset.univ.erase i).sup' (A.erase_nonempty hn i) θ

variable {A}

/-- The rival max does not depend on the bidder's own slot. -/
lemma rivalMax_update_self (hn : 2 ≤ A.n) (θ : A.Profile) (i : Fin A.n) (t : ℝ) :
    A.rivalMax hn (update θ i t) i = A.rivalMax hn θ i := by
  unfold rivalMax
  exact Finset.sup'_congr _ rfl fun j hj => update_of_ne (Finset.ne_of_mem_erase hj) t θ

/-- The rival max is measurable in the profile. -/
lemma rivalMax_measurable (hn : 2 ≤ A.n) (i : Fin A.n) :
    Measurable (fun θ : A.Profile => A.rivalMax hn θ i) := by
  have heq : (fun θ : A.Profile => A.rivalMax hn θ i)
      = (Finset.univ.erase i).sup' (A.erase_nonempty hn i) (fun j (θ : A.Profile) => θ j) := by
    funext θ
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  exact Finset.measurable_sup' _ fun j _ => measurable_pi_apply j

/-- On a profile inside the type box, the rival max lies in the type interval. -/
lemma rivalMax_mem_Icc (hn : 2 ≤ A.n) {θ : A.Profile}
    (hθ : ∀ j, θ j ∈ Icc A.base.θlo A.base.θhi) (i : Fin A.n) :
    A.rivalMax hn θ i ∈ Icc A.base.θlo A.base.θhi := by
  obtain ⟨j₀, hj₀⟩ := A.erase_nonempty hn i
  exact ⟨le_trans (hθ j₀).1 (Finset.le_sup' θ hj₀),
    Finset.sup'_le _ _ fun j _ => (hθ j).2⟩

/-- A report strictly above every rival wins. -/
lemma isTopBidder_update_of_rivalMax_lt (hn : 2 ≤ A.n) {θ : A.Profile} {i : Fin A.n} {t : ℝ}
    (h : A.rivalMax hn θ i < t) : A.IsTopBidder Real.exp (update θ i t) i := by
  have hrival : ∀ j, j ≠ i → θ j < t :=
    fun j hj => lt_of_le_of_lt (Finset.le_sup' θ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)) h
  refine ⟨?_, fun j => ?_, fun j hji => ?_⟩
  · rw [update_self]; exact (Real.exp_pos t).le
  · rw [update_self]
    by_cases hj : j = i
    · subst hj; rw [update_self]
    · rw [update_of_ne hj]
      exact (Real.exp_le_exp.mpr (hrival j hj).le)
  · rw [update_self]
    have hjne : j ≠ i := ne_of_lt hji
    rw [update_of_ne hjne]
    exact Real.exp_lt_exp.mpr (hrival j hjne)

/-- A winning report weakly clears every rival, so the rival max is at most the report. -/
lemma rivalMax_le_of_isTopBidder (hn : 2 ≤ A.n) {θ : A.Profile} {i : Fin A.n} {t : ℝ}
    (h : A.IsTopBidder Real.exp (update θ i t) i) : A.rivalMax hn θ i ≤ t := by
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hje := h.is_max j
  rw [update_self, update_of_ne (Finset.ne_of_mem_erase hj)] at hje
  exact Real.exp_le_exp.mp hje

variable (A)

/-- The **second-price (Vickrey) auction mechanism**: The highest-value bidder wins and pays the
highest rival value — the second-highest value overall; losers pay nothing. -/
def secondPriceMechanism (hn : 2 ≤ A.n) : AuctionMechanism A where
  alloc := A.highestValueAlloc
  pay θ i := A.rivalMax hn θ i * A.highestValueAlloc.x θ i
  pay_measurable i := (rivalMax_measurable hn i).mul (A.highestValueAlloc.measurable i)
  pay_integrable i := by
    refine ⟨((rivalMax_measurable hn i).mul
      (A.highestValueAlloc.measurable i)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := max |A.base.θlo| |A.base.θhi|) ?_⟩
    filter_upwards [A.ae_forall_mem_Icc] with θ hθ
    have hm := rivalMax_mem_Icc hn hθ i
    have hm_abs : |A.rivalMax hn θ i| ≤ max |A.base.θlo| |A.base.θhi| := by
      rw [abs_le]
      constructor
      · calc -(max |A.base.θlo| |A.base.θhi|)
            ≤ -|A.base.θlo| := neg_le_neg (le_max_left _ _)
          _ ≤ A.base.θlo := neg_abs_le _
          _ ≤ A.rivalMax hn θ i := hm.1
      · calc A.rivalMax hn θ i
            ≤ A.base.θhi := hm.2
          _ ≤ |A.base.θhi| := le_abs_self _
          _ ≤ max |A.base.θlo| |A.base.θhi| := le_max_right _ _
    calc ‖A.rivalMax hn θ i * A.highestValueAlloc.x θ i‖
        = |A.rivalMax hn θ i| * |A.highestValueAlloc.x θ i| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |A.rivalMax hn θ i| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_le]
          exact ⟨by linarith [A.highestValueAlloc.nonneg θ i], A.highestValueAlloc.le_one θ i⟩
      _ = |A.rivalMax hn θ i| := mul_one _
      _ ≤ max |A.base.θlo| |A.base.θhi| := hm_abs
  pay_measurable_update i t := by
    -- The rival max ignores coordinate `i`, so splicing leaves it unchanged; the spliced
    -- allocation is measurable via the reduced-form integrand helper.
    have heq : (fun θ : A.Profile =>
          A.rivalMax hn (update θ i t) i * A.highestValueAlloc.x (update θ i t) i)
        = fun θ : A.Profile =>
          A.rivalMax hn θ i * A.highestValueAlloc.x (update θ i t) i := by
      funext θ; rw [rivalMax_update_self]
    rw [heq]
    exact (rivalMax_measurable hn i).mul (A.highestValueAlloc.measurable_interim_integrand i t)
  pay_integrable_update i t := by
    -- The rival max ignores coordinate `i`, so the spliced price is still bounded by
    -- `max |θlo| |θhi|` a.e.; the spliced allocation is bounded in `[0, 1]`. Mirror the
    -- profilewise integrability bound.
    have heq : (fun θ : A.Profile =>
          A.rivalMax hn (update θ i t) i * A.highestValueAlloc.x (update θ i t) i)
        = fun θ : A.Profile =>
          A.rivalMax hn θ i * A.highestValueAlloc.x (update θ i t) i := by
      funext θ; rw [rivalMax_update_self]
    rw [heq]
    refine ⟨((rivalMax_measurable hn i).mul
      (A.highestValueAlloc.measurable_interim_integrand i t)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := max |A.base.θlo| |A.base.θhi|) ?_⟩
    filter_upwards [A.ae_forall_mem_Icc] with θ hθ
    have hm := rivalMax_mem_Icc hn hθ i
    have hm_abs : |A.rivalMax hn θ i| ≤ max |A.base.θlo| |A.base.θhi| := by
      rw [abs_le]
      constructor
      · calc -(max |A.base.θlo| |A.base.θhi|)
            ≤ -|A.base.θlo| := neg_le_neg (le_max_left _ _)
          _ ≤ A.base.θlo := neg_abs_le _
          _ ≤ A.rivalMax hn θ i := hm.1
      · calc A.rivalMax hn θ i
            ≤ A.base.θhi := hm.2
          _ ≤ |A.base.θhi| := le_abs_self _
          _ ≤ max |A.base.θlo| |A.base.θhi| := le_max_right _ _
    calc ‖A.rivalMax hn θ i * A.highestValueAlloc.x (update θ i t) i‖
        = |A.rivalMax hn θ i| * |A.highestValueAlloc.x (update θ i t) i| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |A.rivalMax hn θ i| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_le]
          exact ⟨by linarith [A.highestValueAlloc.nonneg (update θ i t) i],
            A.highestValueAlloc.le_one (update θ i t) i⟩
      _ = |A.rivalMax hn θ i| := mul_one _
      _ ≤ max |A.base.θlo| |A.base.θhi| := hm_abs

variable {A}

@[simp] lemma secondPriceMechanism_alloc (hn : 2 ≤ A.n) :
    (A.secondPriceMechanism hn).alloc = A.highestValueAlloc := rfl

@[simp] lemma secondPriceMechanism_pay (hn : 2 ≤ A.n) (θ : A.Profile) (i : Fin A.n) :
    (A.secondPriceMechanism hn).pay θ i
      = A.rivalMax hn θ i * A.highestValueAlloc.x θ i := rfl

/-- **The winner pays the second-highest value.** -/
lemma secondPriceMechanism_pay_of_top (hn : 2 ≤ A.n) {θ : A.Profile} {i : Fin A.n}
    (h : A.IsTopBidder Real.exp θ i) :
    (A.secondPriceMechanism hn).pay θ i = A.rivalMax hn θ i := by
  rw [secondPriceMechanism_pay, highestValueAlloc_x_of_top h, mul_one]

/-- **A losing bidder pays nothing.** -/
lemma secondPriceMechanism_pay_of_not_top (hn : 2 ≤ A.n) {θ : A.Profile} {i : Fin A.n}
    (h : ¬ A.IsTopBidder Real.exp θ i) :
    (A.secondPriceMechanism hn).pay θ i = 0 := by
  rw [secondPriceMechanism_pay, highestValueAlloc_x_of_not_top h, mul_zero]

/-- The ex-post payoff integrand `(θ − rivalMax) · 𝟙{win at report s}` is integrable against the
joint law. -/
lemma secondPrice_expost_integrable (hn : 2 ≤ A.n) (i : Fin A.n) (θ s : ℝ) :
    Integrable
      (fun θ' : A.Profile =>
        (θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i s) i)
      A.jointLaw := by
  refine ⟨((measurable_const.sub (rivalMax_measurable hn i)).mul
    (A.highestValueAlloc.measurable_interim_integrand i s)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := |θ| + max |A.base.θlo| |A.base.θhi|) ?_⟩
  filter_upwards [A.ae_forall_mem_Icc] with θ' hθ'
  have hm := rivalMax_mem_Icc hn hθ' i
  have hm_abs : |A.rivalMax hn θ' i| ≤ max |A.base.θlo| |A.base.θhi| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le A.base.θlo, hm.1,
        neg_le_neg (le_max_left |A.base.θlo| |A.base.θhi|)]
    · linarith [le_abs_self A.base.θhi, hm.2,
        le_max_right |A.base.θlo| |A.base.θhi|]
  have hx_abs : |A.highestValueAlloc.x (update θ' i s) i| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [A.highestValueAlloc.nonneg (update θ' i s) i],
      A.highestValueAlloc.le_one (update θ' i s) i⟩
  calc ‖(θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i s) i‖
      = |θ - A.rivalMax hn θ' i| * |A.highestValueAlloc.x (update θ' i s) i| := by
        rw [Real.norm_eq_abs, abs_mul]
    _ ≤ |θ - A.rivalMax hn θ' i| * 1 := mul_le_mul_of_nonneg_left hx_abs (abs_nonneg _)
    _ = |θ - A.rivalMax hn θ' i| := mul_one _
    _ ≤ |θ| + |A.rivalMax hn θ' i| := abs_sub _ _
    _ ≤ |θ| + max |A.base.θlo| |A.base.θhi| := by linarith [hm_abs]

/-- **The reduced report-utility is the integrated ex-post Vickrey payoff**: A type-`θ` bidder
reporting `r` gets `∫ (θ − rivalMax) · 𝟙{win at report r}` over the rivals' law. -/
lemma secondPriceMechanism_reportUtil (hn : 2 ≤ A.n) (i : Fin A.n) (θ r : ℝ) :
    ((A.secondPriceMechanism hn).reducedMechanism i).reportUtil θ r
      = ∫ θ', (θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i r) i
          ∂A.jointLaw := by
  have hx_int : Integrable
      (fun θ' : A.Profile => θ * A.highestValueAlloc.x (update θ' i r) i) A.jointLaw :=
    (A.highestValueAlloc.integrable_interim_integrand i r).const_mul θ
  have hpay_int : Integrable
      (fun θ' : A.Profile =>
        A.rivalMax hn θ' i * A.highestValueAlloc.x (update θ' i r) i) A.jointLaw := by
    have h := secondPrice_expost_integrable hn i 0 r
    simpa using h.neg
  rw [DirectMechanism.reportUtil_def, AuctionMechanism.reducedMechanism_x,
    AuctionMechanism.reducedMechanism_p, secondPriceMechanism_alloc,
    ExPostAlloc.interimAlloc_def, AuctionMechanism.interimPay_def]
  have hpay_pt : ∀ θ' : A.Profile,
      (A.secondPriceMechanism hn).pay (update θ' i r) i
        = A.rivalMax hn θ' i * A.highestValueAlloc.x (update θ' i r) i := by
    intro θ'
    rw [secondPriceMechanism_pay, rivalMax_update_self]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpay_pt), ← integral_const_mul,
    ← integral_sub hx_int hpay_int]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ' => ?_)
  dsimp only
  ring

/-- **Pointwise Vickrey dominance.** For every fixed rival profile, truthful reporting maximizes
the ex-post payoff: Winning pays `θ − rivalMax`, the price does not depend on the own report, and
the truthful report wins exactly when winning is (weakly) profitable. -/
lemma secondPrice_pointwise_dominance (hn : 2 ≤ A.n) (i : Fin A.n) (θ r : ℝ)
    (θ' : A.Profile) :
    (θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i r) i
      ≤ (θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i θ) i := by
  -- The truthful payoff is never negative: winning truthfully implies the value clears the price.
  have hRHS : 0 ≤ (θ - A.rivalMax hn θ' i) * A.highestValueAlloc.x (update θ' i θ) i := by
    by_cases hw : A.IsTopBidder Real.exp (update θ' i θ) i
    · rw [highestValueAlloc_x_of_top hw, mul_one, sub_nonneg]
      exact rivalMax_le_of_isTopBidder hn hw
    · rw [highestValueAlloc_x_of_not_top hw, mul_zero]
  by_cases hwr : A.IsTopBidder Real.exp (update θ' i r) i
  · rw [highestValueAlloc_x_of_top hwr, mul_one]
    rcases lt_trichotomy (A.rivalMax hn θ' i) θ with hlt | heq | hgt
    · -- Value strictly clears the price: the truthful report also wins, same payoff.
      rw [highestValueAlloc_x_of_top (isTopBidder_update_of_rivalMax_lt hn hlt), mul_one]
    · -- Tie: the deviating payoff is zero, and the truthful payoff is nonnegative.
      rw [← heq] at hRHS ⊢
      linarith
    · -- Value below the price: the deviation wins at a loss.
      linarith
  · rw [highestValueAlloc_x_of_not_top hwr, mul_zero]
    exact hRHS

/-- **The second-price auction is Bayesian incentive compatible.** Truthful reporting dominates
every misreport ex post (`secondPrice_pointwise_dominance`); integrating over the rivals' law gives
the interim statement. -/
theorem secondPriceMechanism_isBIC (hn : 2 ≤ A.n) : (A.secondPriceMechanism hn).IsBIC := by
  -- The type-interval hypotheses are not needed: ex-post dominance holds for every real type and
  -- report; they are kept (underscored) because `IsBIC` quantifies over the interval.
  intro i θ _hθ r _hr
  rw [← DirectMechanism.reportUtil_self, secondPriceMechanism_reportUtil,
    secondPriceMechanism_reportUtil]
  exact integral_mono (secondPrice_expost_integrable hn i θ r)
    (secondPrice_expost_integrable hn i θ θ)
    (secondPrice_pointwise_dominance hn i θ r)

/-- **The lowest type earns no rent.** Almost surely all rivals' values are at least `θlo`, so the
lowest type either loses (payoff `0`) or wins in a tie at price exactly `θlo` (payoff `0`). -/
lemma secondPriceMechanism_interimUtil_θlo (hn : 2 ≤ A.n) (i : Fin A.n) :
    ((A.secondPriceMechanism hn).reducedMechanism i).interimUtil A.base.θlo = 0 := by
  rw [← DirectMechanism.reportUtil_self, secondPriceMechanism_reportUtil]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [A.ae_forall_mem_Icc] with θ' hθ'
  rw [Pi.zero_apply]
  by_cases hw : A.IsTopBidder Real.exp (update θ' i A.base.θlo) i
  · have hm_eq : A.rivalMax hn θ' i = A.base.θlo :=
      le_antisymm (rivalMax_le_of_isTopBidder hn hw) (rivalMax_mem_Icc hn hθ' i).1
    rw [hm_eq, sub_self, zero_mul]
  · rw [highestValueAlloc_x_of_not_top hw, mul_zero]

/-- **The Vickrey interim payment is the Myerson payment** of the highest-value allocation:
`𝔼[top rival value · 𝟙{win} ∣ θᵢ = t] = t·F(t)^{n-1} − ∫_{θlo}^t F(s)^{n-1} ds`. Obtained from
revenue equivalence against the Myerson mechanism of the same allocation — both are BIC with zero
lowest-type rent — with no order-statistic integration. -/
theorem secondPriceMechanism_interimPay_eq_myersonPayment (hn : 2 ≤ A.n) (i : Fin A.n)
    {t : ℝ} (ht : t ∈ Icc A.base.θlo A.base.θhi) :
    (A.secondPriceMechanism hn).interimPay i t
      = (A.highestValueAlloc.reducedAlloc i).myersonPayment t := by
  have h := AuctionMechanism.revenue_equivalence
    (M₁ := A.secondPriceMechanism hn) (M₂ := A.highestValueAlloc.myersonMechanism)
    (A.secondPriceMechanism_isBIC hn)
    (A.highestValueAlloc.myersonMechanism_isBIC A.highestValueAlloc_reducedAlloc_monotone)
    (fun _j _s _hs => rfl)
    (fun j => by
      rw [secondPriceMechanism_interimUtil_θlo hn,
        ExPostAlloc.myersonMechanism_interimUtil_zero])
    i ht
  rw [h, ExPostAlloc.myersonMechanism_interimPay]

end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
