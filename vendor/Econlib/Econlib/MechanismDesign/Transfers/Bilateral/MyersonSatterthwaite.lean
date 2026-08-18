/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.IntervalIntegral
public import Econlib.MechanismDesign.Transfers.Bilateral.Environment
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity

/-!
# The Myerson–Satterthwaite impossibility theorem

The **Myerson–Satterthwaite** impossibility theorem (Myerson and Satterthwaite 1983): No
bilateral-trade mechanism is simultaneously incentive compatible, individually rational, ex-post
efficient, and weakly budget balanced. Even with one buyer and one seller, private information
makes efficient voluntary trade incompatible with budget balance.

The transfer schedules are not literally arbitrary: Each `BilateralEnv.Mechanism` requires its
buyer and seller payment fields to be reduced-form integrable (against the other agent's density)
and jointly measurable and integrable under the product law `F_b ⊗ F_s`, so that the interim
expectations and the ex-ante budget integral are well defined and Fubini applies. The impossibility
holds across all transfers meeting these regularity conditions; see `BilateralEnv.Mechanism` for
the exact fields.

## Main definitions

* `ScreeningEnv.reflect`: The reflection of a screening environment across the origin, used to
  translate the seller's decreasing-allocation problem into a standard buyer-style problem.
* `BilateralEnv.Mechanism.buyerMech`: The buyer's reduced-form direct screening mechanism.
* `BilateralEnv.Mechanism.sellerMech`: The seller's reduced-form direct screening mechanism on the
  reflected environment.

## Main statements

* `myerson_satterthwaite`: No bilateral-trade mechanism can simultaneously satisfy buyer and seller
  incentive compatibility, individual rationality, ex-post efficiency, and weak budget balance.
* `gains_eq_integral`: The expected gains from trade equal the integral of `(1 − Fb)·Fs` over the
  joint type span (layer-cake identity).
* `budget_collapse`: The budget surplus identity relating virtual gains to the overlap integral of
  `(1 − Fb)·Fs`.

## References

* Myerson, Roger B., and Mark A. Satterthwaite. 1983. “Efficient Mechanisms for Bilateral Trading.”
  *Journal of Economic Theory* 29 (2): 265–81. [https://doi.org/10.1016/0022-0531(83)90048-0](https://doi.org/10.1016/0022-0531(83)90048-0).

## Tags

mechanism design, bilateral trade, myerson-satterthwaite, incentive compatibility, budget balance
-/

@[expose] public section

open Set MeasureTheory Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

open Econlib.Probability

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-- The **reflected screening environment** `[−θhi, −θlo]` carrying the reflected distribution. The
seller's problem on `E` maps to a standard increasing-allocation problem on `E.reflect` via the
change of variable `σ = −θ`. -/
noncomputable def reflect : ScreeningEnv where
  θlo := -E.θhi
  θhi := -E.θlo
  hθ := by simpa using E.hθ
  dist := E.dist.reflect
  supp_subset := by
    intro x hx
    have := E.supp_subset (-x) hx
    rw [mem_Icc] at this ⊢
    constructor <;> [linarith [this.2]; linarith [this.1]]
  density_pos := by
    intro x hx
    rw [mem_Icc] at hx
    exact E.density_pos (-x) (by rw [mem_Icc]; constructor <;> linarith [hx.1, hx.2])
  density_cont := by
    have hcomp : ContinuousOn (fun x => E.dist.density (-x)) (Icc (-E.θhi) (-E.θlo)) := by
      apply E.density_cont.comp continuousOn_neg
      intro x hx
      rw [mem_Icc] at hx ⊢
      constructor <;> linarith [hx.1, hx.2]
    exact hcomp

end ScreeningEnv

end Econlib.MechanismDesign.Transfers.SingleParameter

namespace Econlib.MechanismDesign.Transfers.Bilateral

open Econlib.MechanismDesign.Transfers.SingleParameter

namespace BilateralEnv.Mechanism

variable {Γ : BilateralEnv} (M : Γ.Mechanism)

/-- The buyer's interim-trade integrand `θs ↦ trade θb θs` is integrable against the seller's
density (bounded measurable on a finite measure). -/
lemma buyer_trade_integrable (θb : ℝ) :
    Integrable (fun θs => Γ.seller.dist.density θs * M.trade θb θs) :=
  (Γ.seller.dist.integrable.bdd_mul (M.trade_measurable_seller θb).aestronglyMeasurable
    (ae_of_all _ fun θs => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [M.trade_nonneg θb θs], M.trade_le_one θb θs⟩)).congr
    (ae_of_all _ fun θs => mul_comm _ _)

/-- The seller's interim-trade integrand `θb ↦ trade θb θs` is integrable against the buyer's
density. -/
lemma seller_trade_integrable (θs : ℝ) :
    Integrable (fun θb => Γ.buyer.dist.density θb * M.trade θb θs) :=
  (Γ.buyer.dist.integrable.bdd_mul (M.trade_measurable_buyer θs).aestronglyMeasurable
    (ae_of_all _ fun θb => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [M.trade_nonneg θb θs], M.trade_le_one θb θs⟩)).congr
    (ae_of_all _ fun θb => mul_comm _ _)

/-- The buyer's interim trade probability is nonnegative. -/
lemma buyerInterimTrade_nonneg (θb : ℝ) : 0 ≤ M.buyerInterimTrade θb :=
  Γ.seller.dist.expect_nonneg _ (fun θs => M.trade_nonneg θb θs)

/-- The buyer's interim trade probability is at most one. -/
lemma buyerInterimTrade_le_one (θb : ℝ) : M.buyerInterimTrade θb ≤ 1 := by
  calc M.buyerInterimTrade θb
      ≤ Γ.seller.dist.expect (fun _ => 1) :=
        Γ.seller.dist.expect_mono _ _ (fun θs => M.trade_le_one θb θs)
          (M.buyer_trade_integrable θb) (by simpa using Γ.seller.dist.integrable)
    _ = 1 := Γ.seller.dist.expect_const 1

/-- The seller's interim trade probability is nonnegative. -/
lemma sellerInterimTrade_nonneg (θs : ℝ) : 0 ≤ M.sellerInterimTrade θs :=
  Γ.buyer.dist.expect_nonneg _ (fun θb => M.trade_nonneg θb θs)

/-- The seller's interim trade probability is at most one. -/
lemma sellerInterimTrade_le_one (θs : ℝ) : M.sellerInterimTrade θs ≤ 1 := by
  calc M.sellerInterimTrade θs
      ≤ Γ.buyer.dist.expect (fun _ => 1) :=
        Γ.buyer.dist.expect_mono _ _ (fun θb => M.trade_le_one θb θs)
          (M.seller_trade_integrable θs) (by simpa using Γ.buyer.dist.integrable)
    _ = 1 := Γ.buyer.dist.expect_const 1

/-- The buyer's reduced-form **screening allocation** on `Γ.buyer`. -/
def buyerAlloc : AllocationRule Γ.buyer where
  x := M.buyerInterimTrade
  nonneg := M.buyerInterimTrade_nonneg
  le_one := M.buyerInterimTrade_le_one

/-- The buyer's reduced-form **direct screening mechanism** on `Γ.buyer`: Allocation `Q_b`, payment
`P_b`. Its `IsBIC` is exactly `BuyerBIC`, and its `interimUtil` is exactly `buyerUtil`. -/
def buyerMech : DirectMechanism Γ.buyer where
  alloc := M.buyerAlloc
  p := M.buyerInterimPay

@[simp] lemma buyerMech_x (θb : ℝ) : M.buyerMech.x θb = M.buyerInterimTrade θb := rfl

@[simp] lemma buyerMech_p (θb : ℝ) : M.buyerMech.p θb = M.buyerInterimPay θb := rfl

@[simp] lemma buyerMech_interimUtil (θb : ℝ) :
    M.buyerMech.interimUtil θb = M.buyerUtil θb := rfl

/-- `BuyerBIC` is exactly the screening `IsBIC` of the buyer's reduced mechanism. -/
lemma buyerMech_isBIC (h : M.BuyerBIC) : IsBIC M.buyerMech := h

/-- The seller's reduced-form **screening allocation** on the reflected environment
`Γ.seller.reflect`: At the reflected type `σ`, the allocation is `Q_s(−σ)`. -/
def sellerAlloc : AllocationRule Γ.seller.reflect where
  x := fun σ => M.sellerInterimTrade (-σ)
  nonneg := fun σ => M.sellerInterimTrade_nonneg (-σ)
  le_one := fun σ => M.sellerInterimTrade_le_one (-σ)

/-- The seller's reduced-form **direct screening mechanism** on the reflected environment: At
reflected type `σ = −θs`, allocation `Q_s(−σ)` and payment `−P_s(−σ)`. Its `interimUtil σ` equals
`sellerUtil (−σ)`, and its `IsBIC` is `SellerBIC`. -/
def sellerMech : DirectMechanism Γ.seller.reflect where
  alloc := M.sellerAlloc
  p := fun σ => -M.sellerInterimRecv (-σ)

@[simp] lemma sellerMech_x (σ : ℝ) : M.sellerMech.x σ = M.sellerInterimTrade (-σ) := rfl

@[simp] lemma sellerMech_p (σ : ℝ) : M.sellerMech.p σ = -M.sellerInterimRecv (-σ) := rfl

lemma sellerMech_interimUtil (σ : ℝ) :
    M.sellerMech.interimUtil σ = M.sellerUtil (-σ) := by
  simp only [DirectMechanism.interimUtil_def, sellerMech_x, sellerMech_p,
    Mechanism.sellerUtil]
  ring

/-- `SellerBIC` is exactly the screening `IsBIC` of the seller's reflected reduced mechanism. -/
lemma sellerMech_isBIC (h : M.SellerBIC) : IsBIC M.sellerMech := by
  intro σ hσ ρ hρ
  rw [ScreeningEnv.mem_types, ScreeningEnv.reflect, mem_Icc] at hσ hρ
  have hθs : -σ ∈ Γ.seller.types := by rw [ScreeningEnv.mem_types, mem_Icc]; constructor <;>
    linarith [hσ.1, hσ.2]
  have hθs' : -ρ ∈ Γ.seller.types := by rw [ScreeningEnv.mem_types, mem_Icc]; constructor <;>
    linarith [hρ.1, hρ.2]
  have hsb := h (-σ) hθs (-ρ) hθs'
  rw [Mechanism.sellerUtil] at hsb
  rw [DirectMechanism.reportUtil_def, sellerMech_interimUtil, sellerMech_x, sellerMech_p,
    Mechanism.sellerUtil]
  linarith [hsb]

/-- **Buyer envelope payment formula.** Under `BuyerBIC`, on the buyer's type interval:
`P_b(θb) = θb·Q_b(θb) − U_b(b.θlo) − ∫_{b.θlo}^{θb} Q_b`. -/
lemma buyerPay_eq (hbic : M.BuyerBIC) {θb : ℝ} (hθb : θb ∈ Γ.buyer.types) :
    M.buyerInterimPay θb = θb * M.buyerInterimTrade θb - M.buyerUtil Γ.buyer.θlo
      - ∫ s in Γ.buyer.θlo..θb, M.buyerInterimTrade s := by
  have henv := M.buyerMech.interimUtil_eq_integral (M.buyerMech_isBIC hbic) hθb
  rw [buyerMech_interimUtil, buyerMech_interimUtil] at henv
  simp only [buyerMech_x] at henv
  rw [Mechanism.buyerUtil] at henv
  linarith [henv]

/-- **Seller envelope payment formula.** Under `SellerBIC`, on the seller's type interval:
`P_s(θs) = θs·Q_s(θs) + U_s(s.θhi) + ∫_{θs}^{s.θhi} Q_s`. -/
lemma sellerRecv_eq (hbic : M.SellerBIC) {θs : ℝ} (hθs : θs ∈ Γ.seller.types) :
    M.sellerInterimRecv θs = θs * M.sellerInterimTrade θs + M.sellerUtil Γ.seller.θhi
      + ∫ u in θs..Γ.seller.θhi, M.sellerInterimTrade u := by
  have hlo_eq : (Γ.seller.reflect).θlo = -Γ.seller.θhi := rfl
  have hhi_eq : (Γ.seller.reflect).θhi = -Γ.seller.θlo := rfl
  have hσ : -θs ∈ Γ.seller.reflect.types := by
    rw [ScreeningEnv.mem_types, mem_Icc] at hθs
    rw [ScreeningEnv.mem_types, hlo_eq, hhi_eq, mem_Icc]
    constructor <;> linarith [hθs.1, hθs.2]
  have henv := M.sellerMech.interimUtil_eq_integral (M.sellerMech_isBIC hbic) hσ
  rw [sellerMech_interimUtil, sellerMech_interimUtil] at henv
  have hcv : (∫ u in (Γ.seller.reflect).θlo..(-θs), M.sellerMech.x u)
      = ∫ v in θs..Γ.seller.θhi, M.sellerInterimTrade v := by
    simp only [sellerMech_x, hlo_eq]
    rw [intervalIntegral.integral_comp_neg (fun u => M.sellerInterimTrade u)]
    simp only [neg_neg]
  rw [hcv, hlo_eq] at henv
  simp only [neg_neg] at henv
  rw [Mechanism.sellerUtil] at henv
  linarith [henv]

/-- **Efficiency determines the buyer's reduced trade probability.** For `θb ∈ b.types`,
`Q_b(θb) = F_s(θb)`. -/
lemma buyerInterimTrade_eq_cdf (hEff : M.Efficient) {θb : ℝ} (hθb : θb ∈ Γ.buyer.types) :
    M.buyerInterimTrade θb = Γ.seller.dist.cdf θb := by
  rw [Mechanism.buyerInterimTrade, ContDist.expect_eq_integral, ContDist.cdf_eq_integral]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  apply ae_of_all
  intro θs
  dsimp only
  by_cases hmem : θs ∈ Γ.seller.types
  · rw [hEff θb hθb θs hmem]
    by_cases hle : θs ≤ θb
    · simp [hle, Set.indicator_of_mem]
    · simp [hle, Set.indicator_of_notMem]
  · have hz := Γ.seller.density_eq_zero_of_notMem (by rwa [ScreeningEnv.mem_types] at hmem)
    rw [hz, zero_mul, Set.indicator_apply, hz, ite_self]

/-- **Efficiency determines the seller's reduced trade probability.** For `θs ∈ s.types`,
`Q_s(θs) = 1 − F_b(θs)`. -/
lemma sellerInterimTrade_eq_survival (hEff : M.Efficient) {θs : ℝ}
    (hθs : θs ∈ Γ.seller.types) :
    M.sellerInterimTrade θs = 1 - Γ.buyer.dist.cdf θs := by
  rw [Mechanism.sellerInterimTrade, ContDist.expect_eq_integral]
  have hsurv : (∫ θb, Γ.buyer.dist.density θb * M.trade θb θs)
      = ∫ θb in Ici θs, Γ.buyer.dist.density θb := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    apply ae_of_all
    intro θb
    dsimp only
    by_cases hmem : θb ∈ Γ.buyer.types
    · rw [hEff θb hmem θs hθs]
      by_cases hle : θs ≤ θb
      · simp [hle, Set.indicator_of_mem, Set.mem_Ici]
      · simp [hle, Set.indicator_of_notMem, Set.mem_Ici]
    · have hz := Γ.buyer.density_eq_zero_of_notMem (by rwa [ScreeningEnv.mem_types] at hmem)
      rw [hz, zero_mul, Set.indicator_apply, hz, ite_self]
  rw [hsurv]
  rw [ContDist.cdf_eq_integral]
  have hsplit := integral_add_compl (s := Iic θs) measurableSet_Iic Γ.buyer.dist.integrable
  rw [compl_Iic, Γ.buyer.dist.integral_one] at hsplit
  have hIci : (∫ θb in Ici θs, Γ.buyer.dist.density θb)
      = ∫ θb in Ioi θs, Γ.buyer.dist.density θb := by
    rw [← integral_Ici_eq_integral_Ioi]
  rw [hIci]; linarith [hsplit]

end BilateralEnv.Mechanism

open Econlib.Probability

/-- The product density `f_b ⊗ f_s` is integrable on `volume.prod volume`. -/
private lemma density_prod_integrable (b s : ScreeningEnv) :
    Integrable (fun p : ℝ × ℝ => b.dist.density p.1 * s.dist.density p.2)
      (volume.prod volume) :=
  b.dist.integrable.mul_prod s.dist.integrable

/-- `(1 − Fb)·Fs` vanishes outside `[s.θlo, b.θhi]`: `Fs = 0` below `s.θlo` and `Fb = 1` above
`b.θhi`. -/
private lemma survival_cdf_eq_zero_off (b s : ScreeningEnv) {t : ℝ}
    (ht : t ∉ Icc s.θlo b.θhi) : (1 - b.dist.cdf t) * s.dist.cdf t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with hlt | hgt
  · rw [s.dist.cdf_eq_zero_of_supportsOn_Icc_left
      (fun u hu => s.density_eq_zero_of_notMem hu) hlt, mul_zero]
  · rw [b.dist.cdf_eq_one_of_supportsOn_Icc_right
      (fun u hu => b.density_eq_zero_of_notMem hu) hgt.le, sub_self, zero_mul]

/-- `θ ↦ |θ| · f(θ)` is integrable for a `ScreeningEnv` density `f`. -/
private lemma abs_id_mul_density_integrable (E : ScreeningEnv) :
    Integrable (fun θ => |θ| * E.dist.density θ) := by
  set C := max |E.θlo| |E.θhi| with hC
  have hbound : ∀ θ, |(|θ| * E.dist.density θ)| ≤ C * E.dist.density θ := by
    intro θ
    rw [abs_mul, abs_abs, abs_of_nonneg (E.dist.nonneg θ)]
    rcases le_or_gt (E.dist.density θ) 0 with hd | hd
    · have : E.dist.density θ = 0 := le_antisymm hd (E.dist.nonneg θ)
      simp [this]
    · have hmem := E.supp_subset θ hd
      rw [mem_Icc] at hmem
      apply mul_le_mul_of_nonneg_right _ (E.dist.nonneg θ)
      rw [hC]
      rcases le_total 0 θ with hθ | hθ
      · rw [abs_of_nonneg hθ]
        exact le_trans (le_trans hmem.2 (le_abs_self _)) (le_max_right _ _)
      · rw [abs_of_nonpos hθ]
        exact le_trans (by linarith [hmem.1, neg_le_neg hmem.1])
          (le_trans (neg_le_abs _) (le_max_left _ _))
  refine Integrable.mono' (E.dist.integrable.const_mul C) ?_ (ae_of_all _ hbound)
  exact (continuous_abs.aestronglyMeasurable.mul E.dist.integrable.aestronglyMeasurable)

/-- `Fs(θ) = ∫ f_s(σ) · 1{σ ≤ θ} dσ` as a full-line integral against an indicator. -/
private lemma cdf_eq_indicator_integral (s : ScreeningEnv) (θ : ℝ) :
    s.dist.cdf θ = ∫ σ, (Iic θ).indicator s.dist.density σ := by
  rw [s.dist.cdf_eq_integral, integral_indicator measurableSet_Iic]

/-- `1 − Fb(θ) = ∫ f_b(τ) · 1{θ ≤ τ} dτ` as a full-line integral against an indicator. -/
private lemma survival_eq_indicator_integral (b : ScreeningEnv) (θ : ℝ) :
    1 - b.dist.cdf θ = ∫ τ, (Ici θ).indicator b.dist.density τ := by
  rw [b.dist.cdf_eq_integral, integral_indicator measurableSet_Ici]
  have hsplit := integral_add_compl (s := Iic θ) measurableSet_Iic b.dist.integrable
  rw [compl_Iic, b.dist.integral_one] at hsplit
  rw [← integral_Ici_eq_integral_Ioi] at hsplit
  linarith [hsplit]

/-- **Expected gains from trade as a CDF integral.** For two screening environments, the
density-weighted virtual gains `𝔼_b[θ·Fs(θ)] − 𝔼_s[θ·(1−Fb(θ))]` equal the integral of
`(1 − Fb)·Fs` over the joint type span `[min θlo, max θhi]`. -/
lemma gains_eq_integral (b s : ScreeningEnv) :
    (∫ θ in b.θlo..b.θhi, b.dist.density θ * (θ * s.dist.cdf θ))
      - (∫ θ in s.θlo..s.θhi, s.dist.density θ * (θ * (1 - b.dist.cdf θ)))
      = ∫ t in (min b.θlo s.θlo)..(max b.θhi s.θhi),
          (1 - b.dist.cdf t) * s.dist.cdf t := by
  classical
  have hA_full : (∫ θ in b.θlo..b.θhi, b.dist.density θ * (θ * s.dist.cdf θ))
      = ∫ θ, b.dist.density θ * (θ * s.dist.cdf θ) := by
    rw [intervalIntegral.integral_of_le b.hθ.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun θ hθ => by rw [b.density_eq_zero_of_notMem hθ, zero_mul])]
  have hB_full : (∫ θ in s.θlo..s.θhi, s.dist.density θ * (θ * (1 - b.dist.cdf θ)))
      = ∫ θ, s.dist.density θ * (θ * (1 - b.dist.cdf θ)) := by
    rw [intervalIntegral.integral_of_le s.hθ.le,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun θ hθ => by rw [s.density_eq_zero_of_notMem hθ, zero_mul])]
  have hspan : min b.θlo s.θlo ≤ max b.θhi s.θhi :=
    le_trans (min_le_right _ _) (le_trans s.hθ.le (le_max_right _ _))
  have hR_full : (∫ t in (min b.θlo s.θlo)..(max b.θhi s.θhi),
        (1 - b.dist.cdf t) * s.dist.cdf t)
      = ∫ t, (1 - b.dist.cdf t) * s.dist.cdf t := by
    rw [intervalIntegral.integral_of_le hspan,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => survival_cdf_eq_zero_off b s (fun hmem => ht (by
          rw [mem_Icc] at hmem ⊢
          exact ⟨le_trans (min_le_right _ _) hmem.1, le_trans hmem.2 (le_max_left _ _)⟩)))]
  rw [hA_full, hB_full, hR_full]
  set K : ℝ × ℝ → ℝ := fun p =>
    (if p.2 ≤ p.1 then (p.1 - p.2) else 0) * (b.dist.density p.1 * s.dist.density p.2) with hK
  have hdens_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => b.dist.density p.1 * s.dist.density p.2) (volume.prod volume) :=
    (b.dist.integrable.aestronglyMeasurable.comp_fst).mul
      (s.dist.integrable.aestronglyMeasurable.comp_snd)
  have hcutA : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then p.1 else (0 : ℝ))
      (volume.prod volume) :=
    (Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_fst
      measurable_const).aestronglyMeasurable
  have hcutB : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then p.2 else (0 : ℝ))
      (volume.prod volume) :=
    (Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_snd
      measurable_const).aestronglyMeasurable
  have hcutK : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then p.1 - p.2 else (0 : ℝ))
      (volume.prod volume) :=
    (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (measurable_fst.sub measurable_snd) measurable_const).aestronglyMeasurable
  have hdomA : Integrable (fun p : ℝ × ℝ => |p.1| * b.dist.density p.1 * s.dist.density p.2)
      (volume.prod volume) := (abs_id_mul_density_integrable b).mul_prod s.dist.integrable
  have hdomB : Integrable (fun p : ℝ × ℝ => b.dist.density p.1 * (|p.2| * s.dist.density p.2))
      (volume.prod volume) := b.dist.integrable.mul_prod (abs_id_mul_density_integrable s)
  have hbnn : ∀ p : ℝ × ℝ, 0 ≤ b.dist.density p.1 * s.dist.density p.2 :=
    fun p => mul_nonneg (b.dist.nonneg _) (s.dist.nonneg _)
  have hKA_int : Integrable (fun p : ℝ × ℝ => (if p.2 ≤ p.1 then p.1 else 0)
      * (b.dist.density p.1 * s.dist.density p.2)) (volume.prod volume) := by
    refine Integrable.mono' hdomA (hcutA.mul hdens_meas) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbnn p), mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (hbnn p)
    by_cases h : p.2 ≤ p.1 <;> simp [h, abs_nonneg]
  have hKB_int : Integrable (fun p : ℝ × ℝ => (if p.2 ≤ p.1 then p.2 else 0)
      * (b.dist.density p.1 * s.dist.density p.2)) (volume.prod volume) := by
    refine Integrable.mono' hdomB (hcutB.mul hdens_meas) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbnn p),
      show b.dist.density p.1 * (|p.2| * s.dist.density p.2)
        = |p.2| * (b.dist.density p.1 * s.dist.density p.2) by ring]
    apply mul_le_mul_of_nonneg_right _ (hbnn p)
    by_cases h : p.2 ≤ p.1 <;> simp [h, abs_nonneg]
  have hKint : Integrable K (volume.prod volume) := by
    rw [hK]
    refine Integrable.mono' (hdomA.add hdomB) (hcutK.mul hdens_meas) (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hbnn p),
      show |p.1| * b.dist.density p.1 * s.dist.density p.2
          + b.dist.density p.1 * (|p.2| * s.dist.density p.2)
        = (|p.1| + |p.2|) * (b.dist.density p.1 * s.dist.density p.2) by ring]
    apply mul_le_mul_of_nonneg_right _ (hbnn p)
    by_cases h : p.2 ≤ p.1
    · simp only [h, if_true]; exact abs_sub _ _
    · simp only [h, if_false, abs_zero]; positivity
  have hIA : (∫ θ, b.dist.density θ * (θ * s.dist.cdf θ))
      = ∫ p : ℝ × ℝ, (if p.2 ≤ p.1 then p.1 else 0)
          * (b.dist.density p.1 * s.dist.density p.2) ∂(volume.prod volume) := by
    rw [MeasureTheory.integral_prod _ hKA_int]
    apply integral_congr_ae; apply ae_of_all; intro θ
    dsimp only
    have hinner : (∫ y : ℝ, (if y ≤ θ then θ else 0) * (b.dist.density θ * s.dist.density y))
        = b.dist.density θ * (θ * s.dist.cdf θ) := by
      rw [cdf_eq_indicator_integral s θ]
      rw [show b.dist.density θ * (θ * ∫ σ, (Iic θ).indicator s.dist.density σ)
        = ∫ σ, b.dist.density θ * (θ * (Iic θ).indicator s.dist.density σ) by
          rw [integral_const_mul, integral_const_mul]]
      apply integral_congr_ae; apply ae_of_all; intro σ
      by_cases h : σ ≤ θ
      · simp only [h, if_true, Set.indicator_of_mem, Set.mem_Iic]; ring
      · simp only [h, if_false, Set.indicator_of_notMem, Set.mem_Iic, not_false_iff,
          zero_mul, mul_zero]
    rw [hinner]
  have hIB : (∫ θ, s.dist.density θ * (θ * (1 - b.dist.cdf θ)))
      = ∫ p : ℝ × ℝ, (if p.2 ≤ p.1 then p.2 else 0)
          * (b.dist.density p.1 * s.dist.density p.2) ∂(volume.prod volume) := by
    rw [MeasureTheory.integral_prod_symm _ hKB_int]
    apply integral_congr_ae; apply ae_of_all; intro σ
    dsimp only
    have hinner : (∫ τ : ℝ, (if σ ≤ τ then σ else 0) * (b.dist.density τ * s.dist.density σ))
        = s.dist.density σ * (σ * (1 - b.dist.cdf σ)) := by
      rw [survival_eq_indicator_integral b σ]
      rw [show s.dist.density σ * (σ * ∫ τ, (Ici σ).indicator b.dist.density τ)
        = ∫ τ, s.dist.density σ * (σ * (Ici σ).indicator b.dist.density τ) by
          rw [integral_const_mul, integral_const_mul]]
      apply integral_congr_ae; apply ae_of_all; intro τ
      by_cases h : σ ≤ τ
      · simp only [h, if_true, Set.indicator_of_mem, Set.mem_Ici]; ring
      · simp only [h, if_false, Set.indicator_of_notMem, Set.mem_Ici, not_false_iff,
          zero_mul, mul_zero]
    rw [hinner]
  have hRHS : (∫ t, (1 - b.dist.cdf t) * s.dist.cdf t)
      = ∫ p : ℝ × ℝ, K p ∂(volume.prod volume) := by
    set F3 : ℝ → ℝ × ℝ → ℝ := fun t p =>
      (Ici t).indicator b.dist.density p.1 * (Iic t).indicator s.dist.density p.2 with hF3
    have hslice : ∀ t, (∫ p : ℝ × ℝ, F3 t p ∂(volume.prod volume))
        = (1 - b.dist.cdf t) * s.dist.cdf t := by
      intro t
      rw [hF3, MeasureTheory.integral_prod_mul, survival_eq_indicator_integral b t,
        cdf_eq_indicator_integral s t]
    have hslice' : ∀ p : ℝ × ℝ, (∫ t, F3 t p) = K p := by
      intro p
      rw [hK]
      simp only [hF3, Set.indicator_apply, Set.mem_Ici, Set.mem_Iic]
      have hpull : (∫ t, (if t ≤ p.1 then b.dist.density p.1 else 0)
            * (if p.2 ≤ t then s.dist.density p.2 else 0))
          = (b.dist.density p.1 * s.dist.density p.2)
            * ∫ t, (if p.2 ≤ t ∧ t ≤ p.1 then (1 : ℝ) else 0) := by
        rw [← integral_const_mul]
        apply integral_congr_ae; apply ae_of_all; intro t
        by_cases h1 : t ≤ p.1 <;> by_cases h2 : p.2 ≤ t <;> simp [h1, h2]
      rw [hpull]
      have hlen : (∫ t, (if p.2 ≤ t ∧ t ≤ p.1 then (1 : ℝ) else 0))
          = if p.2 ≤ p.1 then p.1 - p.2 else 0 := by
        have hset : (fun t => if p.2 ≤ t ∧ t ≤ p.1 then (1 : ℝ) else 0)
            = (Icc p.2 p.1).indicator (fun _ => 1) := by
          funext t; simp [Set.indicator_apply, Set.mem_Icc]
        rw [hset, MeasureTheory.integral_indicator_const _ measurableSet_Icc, smul_eq_mul,
          mul_one, Real.volume_real_Icc]
        by_cases h : p.2 ≤ p.1
        · rw [if_pos h, max_eq_left (by linarith)]
        · rw [if_neg h, max_eq_right (by linarith [not_le.mp h])]
      rw [hlen]
      by_cases h : p.2 ≤ p.1
      · simp only [h, if_true]; ring
      · simp only [h, if_false]; ring
    calc (∫ t, (1 - b.dist.cdf t) * s.dist.cdf t)
        = ∫ t, ∫ p : ℝ × ℝ, F3 t p ∂(volume.prod volume) := by
          apply integral_congr_ae; apply ae_of_all; intro t; dsimp only; rw [hslice t]
      _ = ∫ p : ℝ × ℝ, ∫ t, F3 t p ∂volume ∂(volume.prod volume) := by
          rw [MeasureTheory.integral_integral_swap]
          set G : ℝ × ℝ × ℝ → ℝ := fun q => (Icc s.θlo b.θhi).indicator (fun _ => (1 : ℝ)) q.1
            * (b.dist.density q.2.1 * s.dist.density q.2.2) with hG
          have hGint : Integrable G (volume.prod (volume.prod volume)) := by
            have hind : Integrable ((Icc s.θlo b.θhi).indicator (fun _ => (1 : ℝ))) volume := by
              rw [integrable_indicator_iff measurableSet_Icc]
              exact integrableOn_const (measure_Icc_lt_top).ne
            exact hind.mul_prod (density_prod_integrable b s)
          have hF3eq : Function.uncurry F3 = fun q : ℝ × ℝ × ℝ =>
              (if q.1 ≤ q.2.1 then b.dist.density q.2.1 else 0)
                * (if q.2.2 ≤ q.1 then s.dist.density q.2.2 else 0) := by
            funext q; simp only [Function.uncurry, hF3, Set.indicator_apply, Set.mem_Ici,
              Set.mem_Iic]
          rw [hF3eq]
          refine Integrable.mono' hGint ?_ (ae_of_all _ fun q => ?_)
          · have hm1 : AEStronglyMeasurable
                (fun q : ℝ × ℝ × ℝ => if q.1 ≤ q.2.1 then b.dist.density q.2.1 else 0)
                (volume.prod (volume.prod volume)) := by
              rw [show (fun q : ℝ × ℝ × ℝ => if q.1 ≤ q.2.1 then b.dist.density q.2.1 else 0)
                = {q : ℝ × ℝ × ℝ | q.1 ≤ q.2.1}.indicator
                  (fun q => b.dist.density q.2.1) by funext q; simp [Set.indicator_apply]]
              exact (b.dist.integrable.aestronglyMeasurable.comp_fst.comp_snd).indicator
                (measurableSet_le measurable_fst measurable_snd.fst)
            have hm2 : AEStronglyMeasurable
                (fun q : ℝ × ℝ × ℝ => if q.2.2 ≤ q.1 then s.dist.density q.2.2 else 0)
                (volume.prod (volume.prod volume)) := by
              rw [show (fun q : ℝ × ℝ × ℝ => if q.2.2 ≤ q.1 then s.dist.density q.2.2 else 0)
                = {q : ℝ × ℝ × ℝ | q.2.2 ≤ q.1}.indicator
                  (fun q => s.dist.density q.2.2) by funext q; simp [Set.indicator_apply]]
              exact (s.dist.integrable.aestronglyMeasurable.comp_snd.comp_snd).indicator
                (measurableSet_le measurable_snd.snd measurable_fst)
            exact hm1.mul hm2
          · simp only [hG, Real.norm_eq_abs, abs_mul]
            have hbnn1 : 0 ≤ b.dist.density q.2.1 := b.dist.nonneg _
            have hbnn2 : 0 ≤ s.dist.density q.2.2 := s.dist.nonneg _
            by_cases h1 : q.1 ≤ q.2.1 <;> by_cases h2 : q.2.2 ≤ q.1
            · by_cases hb1 : 0 < b.dist.density q.2.1
              · by_cases hs1 : 0 < s.dist.density q.2.2
                · have hmemb := b.supp_subset q.2.1 hb1
                  have hmems := s.supp_subset q.2.2 hs1
                  rw [mem_Icc] at hmemb hmems
                  rw [Set.indicator_of_mem (a := q.1) (by rw [mem_Icc]; constructor <;>
                    [linarith [hmems.1, h2]; linarith [hmemb.2, h1]])]
                  simp only [if_pos h1, if_pos h2, abs_of_nonneg hbnn1, abs_of_nonneg hbnn2,
                    one_mul, le_refl]
                · have : s.dist.density q.2.2 = 0 := le_antisymm (not_lt.mp hs1) hbnn2
                  simp [this]
              · have : b.dist.density q.2.1 = 0 := le_antisymm (not_lt.mp hb1) hbnn1
                simp [this]
            · simp only [if_pos h1, if_neg h2, abs_zero, mul_zero]
              exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
                (mul_nonneg hbnn1 hbnn2)
            · simp only [if_neg h1, if_pos h2, abs_zero, zero_mul]
              exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
                (mul_nonneg hbnn1 hbnn2)
            · simp only [if_neg h1, if_neg h2, abs_zero, zero_mul]
              exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
                (mul_nonneg hbnn1 hbnn2)
      _ = ∫ p : ℝ × ℝ, K p ∂(volume.prod volume) := by
          apply integral_congr_ae; apply ae_of_all; intro p; dsimp only; rw [hslice' p]
  rw [hIA, hIB, hRHS, hK, ← integral_sub hKA_int hKB_int]
  apply integral_congr_ae; apply ae_of_all; intro p
  by_cases h : p.2 ≤ p.1
  · simp only [h, if_true]; ring
  · simp only [h, if_false]; ring

/-- **Budget collapse identity.** For two screening environments with overlapping supports
(`s.θlo < b.θhi`, `b.θlo < s.θhi`), the buyer/seller virtual gains minus the two cumulative
survival integrals equal the negative of the overlap integral of `(1 − Fb)·Fs`. -/
lemma budget_collapse (b s : ScreeningEnv) (hlo : s.θlo < b.θhi) (hhi : b.θlo < s.θhi) :
    (∫ θ in b.θlo..b.θhi, b.dist.density θ * (θ * s.dist.cdf θ))
      - (∫ θ in s.θlo..s.θhi, s.dist.density θ * (θ * (1 - b.dist.cdf θ)))
      - (∫ θ in b.θlo..b.θhi, s.dist.cdf θ * (1 - b.dist.cdf θ))
      - (∫ θ in s.θlo..s.θhi, s.dist.cdf θ * (1 - b.dist.cdf θ))
      = - ∫ t in (max b.θlo s.θlo)..(min b.θhi s.θhi),
          (1 - b.dist.cdf t) * s.dist.cdf t := by
  have hHcont : Continuous (fun t => s.dist.cdf t * (1 - b.dist.cdf t)) :=
    s.dist.cdf_continuous.mul (continuous_const.sub b.dist.cdf_continuous)
  have hgains := gains_eq_integral b s
  have hcumul : (∫ θ in b.θlo..b.θhi, s.dist.cdf θ * (1 - b.dist.cdf θ))
      + (∫ θ in s.θlo..s.θhi, s.dist.cdf θ * (1 - b.dist.cdf θ))
      = (∫ t in (min b.θlo s.θlo)..(max b.θhi s.θhi), s.dist.cdf t * (1 - b.dist.cdf t))
        + ∫ t in (max b.θlo s.θlo)..(min b.θhi s.θhi), s.dist.cdf t * (1 - b.dist.cdf t) := by
    refine intervalIntegral.add_eq_union_add_inter b.hθ.le s.hθ.le ?_
      (hHcont.intervalIntegrable _ _)
    rw [max_le_iff, le_min_iff, le_min_iff]
    exact ⟨⟨b.hθ.le, hhi.le⟩, ⟨hlo.le, s.hθ.le⟩⟩
  have hcomm : ∀ p q : ℝ, (∫ t in p..q, s.dist.cdf t * (1 - b.dist.cdf t))
      = ∫ t in p..q, (1 - b.dist.cdf t) * s.dist.cdf t := fun p q => by
      apply intervalIntegral.integral_congr; intro _ _; exact mul_comm _ _
  rw [hcomm (max b.θlo s.θlo) (min b.θhi s.θhi),
      hcomm (min b.θlo s.θlo) (max b.θhi s.θhi)] at hcumul
  linarith [hgains, hcumul]

/-- **The Myerson–Satterthwaite impossibility theorem** (Myerson and Satterthwaite 1983). No
bilateral-trade mechanism can be simultaneously buyer- and seller-incentive-compatible,
individually rational for both, ex-post efficient, and weakly budget balanced. Private information
precludes efficient voluntary trade without an outside subsidy. -/
theorem myerson_satterthwaite (Γ : BilateralEnv) :
    ¬ ∃ M : Γ.Mechanism, M.BuyerBIC ∧ M.SellerBIC ∧ M.BuyerIR ∧ M.SellerIR ∧
      M.Efficient ∧ M.WeaklyBudgetBalanced := by
  rintro ⟨M, hBIC_b, hBIC_s, hIR_b, hIR_s, hEff, hWBB⟩
  set b := Γ.buyer with hb_def
  set s := Γ.seller with hs_def
  set Fb := b.dist.cdf with hFb_def
  set Fs := s.dist.cdf with hFs_def
  set rentB := M.buyerUtil b.θlo with hrentB
  set rentS := M.sellerUtil s.θhi with hrentS
  set L := max b.θlo s.θlo with hL_def
  set R := min b.θhi s.θhi with hR_def
  set G := ∫ t in L..R, (1 - Fb t) * Fs t with hG_def
  set Qb := M.buyerInterimTrade with hQb_def
  set Qs := M.sellerInterimTrade with hQs_def
  have hQb_mono : MonotoneAlloc M.buyerAlloc :=
    M.buyerMech.isBIC_implies_monotone (M.buyerMech_isBIC hBIC_b)
  have hQb_ii : IntervalIntegrable Qb volume b.θlo b.θhi :=
    M.buyerAlloc.intervalIntegrable_x hQb_mono b.θlo_mem_types b.θhi_mem_types
  have hQs'_mono : MonotoneAlloc M.sellerAlloc := M.sellerMech.isBIC_implies_monotone
    (M.sellerMech_isBIC hBIC_s)
  have hQs_ii : IntervalIntegrable Qs volume s.θlo s.θhi := by
    have h' : IntervalIntegrable (fun σ => M.sellerAlloc.x σ) volume
        (Γ.seller.reflect).θlo (Γ.seller.reflect).θhi :=
      M.sellerAlloc.intervalIntegrable_x hQs'_mono
        (Γ.seller.reflect).θlo_mem_types (Γ.seller.reflect).θhi_mem_types
    have hlo_eq : (Γ.seller.reflect).θlo = -s.θhi := rfl
    have hhi_eq : (Γ.seller.reflect).θhi = -s.θlo := rfl
    rw [hlo_eq, hhi_eq] at h'
    have h'' : IntervalIntegrable (fun σ => Qs (-σ)) volume (-s.θhi) (-s.θlo) := h'
    rw [← IntervalIntegrable.iff_comp_neg] at h''
    exact h''.symm
  have hFb_cont : Continuous (⇑Fb) := Γ.buyer.dist.cdf_continuous
  have hFs_cont : Continuous (⇑Fs) := Γ.seller.dist.cdf_continuous
  have hEb : b.dist.expect M.buyerInterimPay
      = (∫ θ in b.θlo..b.θhi, b.dist.density θ * (θ * Fs θ)) - rentB
        - (∫ θ in b.θlo..b.θhi, Fs θ * (1 - Fb θ)) := by
    have hab : b.θlo ≤ b.θhi := b.hθ.le
    have hcum_eq : ∀ θ ∈ Ioc b.θlo b.θhi, (∫ u in b.θlo..θ, Qb u) = ∫ u in b.θlo..θ, Fs u := by
      intro θ hθ
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le (le_of_lt hθ.1)]
      apply ae_of_all
      intro u hu
      exact M.buyerInterimTrade_eq_cdf hEff ⟨le_of_lt hu.1, le_trans hu.2 hθ.2⟩
    have hpay : EqOn (fun θ => b.dist.density θ * M.buyerInterimPay θ)
        (fun θ => b.dist.density θ * (θ * Fs θ) - rentB * b.dist.density θ
          - (∫ u in b.θlo..θ, Fs u) * b.dist.density θ) (Ioc b.θlo b.θhi) := by
      intro θ hθ
      have hmem : θ ∈ b.types := ⟨le_of_lt hθ.1, hθ.2⟩
      simp only
      rw [M.buyerPay_eq hBIC_b hmem, M.buyerInterimTrade_eq_cdf hEff hmem, hcum_eq θ hθ]
      ring
    have hFs_ii : IntervalIntegrable Fs volume b.θlo b.θhi := hFs_cont.intervalIntegrable _ _
    have hfb_cont : ContinuousOn b.dist.density (Icc b.θlo b.θhi) := b.density_cont
    have hA : IntervalIntegrable (fun θ => b.dist.density θ * (θ * Fs θ)) volume b.θlo b.θhi := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact hfb_cont.mul ((continuousOn_id.mul hFs_cont.continuousOn))
    have hrentpiece : IntervalIntegrable (fun θ => rentB * b.dist.density θ) volume b.θlo b.θhi :=
      (b.dist.integrable.intervalIntegrable).const_mul rentB
    have hXprim_cont : ContinuousOn (fun θ => ∫ u in b.θlo..θ, Fs u) (uIcc b.θlo b.θhi) :=
      intervalIntegral.continuousOn_primitive_interval' hFs_ii left_mem_uIcc
    have hCb : IntervalIntegrable (fun θ => (∫ u in b.θlo..θ, Fs u) * b.dist.density θ)
        volume b.θlo b.θhi :=
      (hXprim_cont.intervalIntegrable).mul_continuousOn ((uIcc_of_le hab) ▸ hfb_cont)
    have hswap := MeasureTheory.integral_triangle_swap_survival hab hFs_ii
      (b.dist.integrable.intervalIntegrable) (F := fun θ => Fb θ)
      (fun t => Γ.buyer.cdf_eq_intervalIntegral t) (Γ.buyer.density_mass_eq_one)
    rw [Γ.buyer.expect_eq_intervalIntegral, intervalIntegral.integral_of_le hab,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpay,
      ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_sub (hA.sub hrentpiece) hCb,
      intervalIntegral.integral_sub hA hrentpiece, hswap]
    rw [intervalIntegral.integral_const_mul, Γ.buyer.density_mass_eq_one, mul_one]
  have hEs : s.dist.expect M.sellerInterimRecv
      = (∫ θ in s.θlo..s.θhi, s.dist.density θ * (θ * (1 - Fb θ))) + rentS
        + (∫ θ in s.θlo..s.θhi, Fs θ * (1 - Fb θ)) := by
    have has : s.θlo ≤ s.θhi := s.hθ.le
    set surv := fun θ => 1 - Fb θ with hsurv_def
    have hsurv_cont : Continuous surv := continuous_const.sub hFb_cont
    have htail_eq : ∀ θ ∈ Ioc s.θlo s.θhi,
        (∫ u in θ..s.θhi, Qs u) = ∫ u in θ..s.θhi, surv u := by
      intro θ hθ
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le hθ.2]
      apply ae_of_all
      intro u hu
      exact M.sellerInterimTrade_eq_survival hEff ⟨le_trans (le_of_lt hθ.1) (le_of_lt hu.1),
        hu.2⟩
    have hpay : EqOn (fun θ => s.dist.density θ * M.sellerInterimRecv θ)
        (fun θ => s.dist.density θ * (θ * surv θ) + rentS * s.dist.density θ
          + (∫ u in θ..s.θhi, surv u) * s.dist.density θ) (Ioc s.θlo s.θhi) := by
      intro θ hθ
      have hmem : θ ∈ s.types := ⟨le_of_lt hθ.1, hθ.2⟩
      simp only [hsurv_def]
      rw [M.sellerRecv_eq hBIC_s hmem, M.sellerInterimTrade_eq_survival hEff hmem,
        htail_eq θ hθ]
      simp only [hsurv_def]; ring
    have hfs_cont : ContinuousOn s.dist.density (Icc s.θlo s.θhi) := s.density_cont
    have hfs_ii : IntervalIntegrable s.dist.density volume s.θlo s.θhi :=
      s.dist.integrable.intervalIntegrable
    have hB : IntervalIntegrable (fun θ => s.dist.density θ * (θ * surv θ)) volume
        s.θlo s.θhi := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le has]
      exact hfs_cont.mul ((continuousOn_id.mul hsurv_cont.continuousOn))
    have hrentpiece : IntervalIntegrable (fun θ => rentS * s.dist.density θ) volume
        s.θlo s.θhi := hfs_ii.const_mul rentS
    have hTprim_cont : ContinuousOn (fun θ => ∫ u in θ..s.θhi, surv u) (uIcc s.θlo s.θhi) :=
      intervalIntegral.continuousOn_primitive_interval_left
        (hsurv_cont.continuousOn.integrableOn_compact isCompact_uIcc)
    have hCs : IntervalIntegrable (fun θ => (∫ u in θ..s.θhi, surv u) * s.dist.density θ)
        volume s.θlo s.θhi :=
      (hTprim_cont.intervalIntegrable).mul_continuousOn ((uIcc_of_le has) ▸ hfs_cont)
    have hswap := MeasureTheory.integral_triangle_swap has hfs_ii
      (hsurv_cont.intervalIntegrable _ _)
    have hCsval : (∫ θ in s.θlo..s.θhi, (∫ u in θ..s.θhi, surv u) * s.dist.density θ)
        = ∫ θ in s.θlo..s.θhi, Fs θ * surv θ := by
      have hcomm : (∫ θ in s.θlo..s.θhi, (∫ u in θ..s.θhi, surv u) * s.dist.density θ)
          = ∫ θ in s.θlo..s.θhi, s.dist.density θ * ∫ u in θ..s.θhi, surv u := by
        apply intervalIntegral.integral_congr; intro θ _; exact mul_comm _ _
      rw [hcomm, ← hswap]
      rw [intervalIntegral.integral_of_le has, intervalIntegral.integral_of_le has]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro θ _
      simp only
      rw [← Γ.seller.cdf_eq_intervalIntegral θ]
    rw [Γ.seller.expect_eq_intervalIntegral, intervalIntegral.integral_of_le has,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpay,
      ← intervalIntegral.integral_of_le has,
      intervalIntegral.integral_add (hB.add hrentpiece) hCs,
      intervalIntegral.integral_add hB hrentpiece, hCsval,
      intervalIntegral.integral_const_mul, Γ.seller.density_mass_eq_one, mul_one]
  have hbudget : b.dist.expect M.buyerInterimPay - s.dist.expect M.sellerInterimRecv
      = - G - rentB - rentS := by
    rw [hEb, hEs, hG_def, hFb_def, hFs_def]
    have hcollapse := budget_collapse b s Γ.hlo Γ.hhi
    rw [hb_def, hs_def] at *
    linarith [hcollapse]
  have hrentB_nn : 0 ≤ rentB := hIR_b b.θlo b.θlo_mem_types
  have hrentS_nn : 0 ≤ rentS := hIR_s s.θhi s.θhi_mem_types
  have hbz : ∀ t, t ∉ Icc b.θlo b.θhi → b.dist.density t = 0 :=
    fun t ht => Γ.buyer.density_eq_zero_of_notMem ht
  have hsz : ∀ t, t ∉ Icc s.θlo s.θhi → s.dist.density t = 0 :=
    fun t ht => Γ.seller.density_eq_zero_of_notMem ht
  have hG_pos : 0 < G := by
    rw [hG_def]
    have hLR : L < R := by
      rw [hL_def, hR_def]
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨b.hθ, Γ.hhi⟩, ⟨Γ.hlo, s.hθ⟩⟩
    apply intervalIntegral.integral_pos hLR
    · exact ((continuous_const.sub hFb_cont).mul hFs_cont).continuousOn
    · intro t _
      exact mul_nonneg (by linarith [Γ.buyer.dist.cdf_le_one t]) (Γ.seller.dist.cdf_nonneg t)
    · set c := (L + R) / 2 with hc_def
      have hcL : L < c := by rw [hc_def]; linarith [hLR]
      have hcR : c < R := by rw [hc_def]; linarith [hLR]
      have hcs : s.θlo < c := lt_of_le_of_lt (le_max_right _ _) (hL_def ▸ hcL)
      have hcb : c < b.θhi := lt_of_lt_of_le (hR_def ▸ hcR) (min_le_left _ _)
      refine ⟨c, ⟨hcL.le, hcR.le⟩, ?_⟩
      have hFsc : 0 < Fs c := by
        rcases lt_or_ge c s.θhi with hlt | hge
        · exact Γ.seller.dist.cdf_pos_of_mem_Ioo_support ⟨hcs, hlt⟩
            (fun y hy => Γ.seller.density_pos y ⟨hy.1.le, hy.2.le⟩) Γ.seller.density_cont
        · rw [hFs_def]
          rw [Γ.seller.dist.cdf_eq_one_of_supportsOn_Icc_right hsz hge]; norm_num
      have hFbc : Fb c < 1 := by
        rcases lt_or_ge b.θlo c with hgt | hle
        · have := Γ.buyer.dist.cdf_strictMono hcb
            (fun y hy => Γ.buyer.density_pos y ⟨le_trans hgt.le hy.1, hy.2⟩)
            (Γ.buyer.density_cont.mono (Icc_subset_Icc hgt.le le_rfl))
          linarith [Γ.buyer.dist.cdf_le_one b.θhi, this]
        · have hFlo : Fb b.θlo = 0 := by
            rw [hFb_def, Γ.buyer.cdf_eq_intervalIntegral, intervalIntegral.integral_same]
          have := Γ.buyer.dist.cdf.mono hle
          rw [hFb_def] at hFlo ⊢
          linarith [this, hFlo]
      exact mul_pos (by linarith [hFbc]) hFsc
  have hWBB' : 0 ≤ b.dist.expect M.buyerInterimPay - s.dist.expect M.sellerInterimRecv := by
    have h := hWBB
    rw [BilateralEnv.Mechanism.WeaklyBudgetBalanced] at h
    linarith
  rw [hbudget] at hWBB'
  linarith

end Econlib.MechanismDesign.Transfers.Bilateral
