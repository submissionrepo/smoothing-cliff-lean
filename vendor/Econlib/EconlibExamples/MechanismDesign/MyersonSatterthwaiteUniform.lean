import Mathlib
import Econlib

/-!
# Myerson–Satterthwaite for uniform traders (worked example)

The canonical Myerson–Satterthwaite instance: a buyer and a seller each draw a private
value/cost **uniformly on `[0, 1]`**, with fully overlapping supports. We build the corresponding
`BilateralEnv`, quantify what is at stake, and read off the impossibility.

Efficient trade here means trade exactly when `θ_b ≥ θ_s`, and the stakes are computed exactly:

* `uniformBilateral_efficient_trade_prob` — efficient trade occurs with probability `1/2`: the
  event `{θ_s ≤ θ_b}` has mass `1/2` under the joint density;
* `uniformBilateral_gains_integral` — efficient trade generates expected gains
  `∫₀¹ ∫₀^{θ_b} (θ_b − θ_s) dθ_s dθ_b = 1/6`;
* `uniformBilateral_survival_integral` — the overlap integral `∫₀¹ (1 − F_b) F_s = 1/6`. This is
  the quantity `G` whose strict positivity drives `myerson_satterthwaite`, so on this instance the
  impossibility is non-vacuous by the margin `1/6`;
* `uniformBilateral_gains` — the density-weighted virtual-gains expression from the library's
  layer-cake identity `gains_eq_integral` also equals `1/6`, tying the raw computation to the
  expression the impossibility proof manipulates.

Yet none of those gains are realizable by a voluntary, self-financing mechanism:

* `uniformBilateral_impossible` — no bilateral-trade mechanism on this environment is simultaneously
  incentive compatible (both sides), individually rational (both sides), ex-post efficient, and
  weakly budget balanced.

This file doubles as a regression test of the `Transfers.Bilateral` impossibility API on concrete
numbers.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.MechanismDesign.Transfers.Bilateral
open Econlib.Probability
open Set MeasureTheory

/-- The uniform-`[0,1]` single-parameter environment (shared by buyer and seller). -/
def uniformEnv : ScreeningEnv := ScreeningEnv.uniform 0 1 (by norm_num)

/-- The **bilateral environment** with a uniform-`[0,1]` buyer and a uniform-`[0,1]` seller. The
supports coincide, so they overlap: efficient trade is sometimes profitable (`θ_b > θ_s`) and
sometimes not (`θ_b < θ_s`). -/
def uniformBilateral : BilateralEnv where
  buyer := uniformEnv
  seller := uniformEnv
  hlo := uniformEnv.hθ
  hhi := uniformEnv.hθ

/-- The buyer of the uniform bilateral environment is the uniform environment (definitional). -/
@[simp] lemma uniformBilateral_buyer : uniformBilateral.buyer = uniformEnv := rfl

/-- The seller of the uniform bilateral environment is the uniform environment (definitional). -/
@[simp] lemma uniformBilateral_seller : uniformBilateral.seller = uniformEnv := rfl

/-- The distribution of `uniformEnv` is the uniform distribution on `[0, 1]` (definitional). -/
lemma uniformEnv_dist : uniformEnv.dist = ContDist.uniform 0 1 one_pos := rfl

/-- On the support `[0, 1]`, the uniform density is `1`. -/
lemma uniformEnv_density {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    uniformEnv.dist.density t = 1 := by
  rw [uniformEnv_dist, ContDist.uniform_density_of_mem 0 1 one_pos ht]
  norm_num

/-- On the support `[0, 1]`, the uniform CDF is the identity: `F(t) = t`. -/
lemma uniformEnv_cdf {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    uniformEnv.dist.cdf t = t := by
  rw [uniformEnv_dist, ContDist.uniform_cdf_of_mem 0 1 one_pos ht]
  ring

/-! ### The headline numbers

Before the impossibility, quantify what is on the table: trade is efficient on the event
`{θ_s ≤ θ_b}`, which has probability `1/2`, and realizing it would generate expected gains `1/6`.
-/

/-- **Efficient trade has probability `1/2`.** Under the joint density of the uniform buyer and
seller, the event `{θ_s ≤ θ_b}` on which trade is (weakly) profitable has probability `1/2`. -/
theorem uniformBilateral_efficient_trade_prob :
    ∫ p : ℝ × ℝ in {p : ℝ × ℝ | p.2 ≤ p.1},
        uniformBilateral.buyer.dist.density p.1 * uniformBilateral.seller.dist.density p.2
      = 1 / 2 := by
  simp only [uniformBilateral_buyer, uniformBilateral_seller]
  have hE : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  -- Write the event probability as a full-plane integral of an indicator, then slice by Fubini.
  rw [← integral_indicator hE, MeasureTheory.Measure.volume_eq_prod]
  have hint : Integrable
      ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        fun p => uniformEnv.dist.density p.1 * uniformEnv.dist.density p.2)
      (volume.prod volume) :=
    (uniformEnv.dist.integrable.mul_prod uniformEnv.dist.integrable).indicator hE
  rw [MeasureTheory.integral_prod _ hint]
  -- For fixed buyer type, the inner integral is the seller CDF at the buyer's type.
  have hinner : ∀ θb : ℝ,
      (∫ θs, ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        (fun p => uniformEnv.dist.density p.1 * uniformEnv.dist.density p.2)) (θb, θs))
      = uniformEnv.dist.density θb * uniformEnv.dist.cdf θb := by
    intro θb
    have hslice : (fun θs => ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        (fun p => uniformEnv.dist.density p.1 * uniformEnv.dist.density p.2)) (θb, θs))
        = (Iic θb).indicator
            (fun θs => uniformEnv.dist.density θb * uniformEnv.dist.density θs) := by
      funext θs
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iic]
    rw [hslice, integral_indicator measurableSet_Iic, integral_const_mul,
      ← uniformEnv.dist.cdf_eq_integral]
  simp only [hinner]
  -- The density vanishes off `[0, 1]`; on `[0, 1]` the integrand is the identity.
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc (0 : ℝ) 1)
      (fun θb hθb => by rw [uniformEnv.density_eq_zero_of_notMem hθb, zero_mul]),
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θb hθb => by rw [uniformEnv_density hθb, uniformEnv_cdf hθb, one_mul]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
  norm_num

/-- **Expected gains from efficient trade are `1/6`.** Integrating the trade surplus `θ_b − θ_s`
over the region of profitable trade: `∫₀¹ ∫₀^{θ_b} (θ_b − θ_s) dθ_s dθ_b = 1/6`. -/
theorem uniformBilateral_gains_integral :
    ∫ θb in (0 : ℝ)..1, (∫ θs in (0 : ℝ)..θb, (θb - θs)) = 1 / 6 := by
  have hinner : ∀ θb : ℝ, (∫ θs in (0 : ℝ)..θb, (θb - θs)) = θb ^ 2 / 2 := by
    intro θb
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable 0 θb)
        intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  simp only [hinner]
  rw [show (fun θb : ℝ => θb ^ 2 / 2) = fun θb : ℝ => (1 / 2 : ℝ) * θb ^ 2 from
      funext fun θb => by ring,
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- **The overlap integral `G` equals `1/6`.** `∫₀¹ (1 − F_b(t)) · F_s(t) dt = 1/6` on the uniform
instance. This is the quantity whose strict positivity drives `myerson_satterthwaite`: inside that
proof, the expected budget deficit of an incentive-compatible, individually rational, efficient
mechanism is `G` plus the two participation rents, so it is at least `G = 1/6` here. -/
theorem uniformBilateral_survival_integral :
    ∫ t in (0 : ℝ)..1,
        (1 - uniformBilateral.buyer.dist.cdf t) * uniformBilateral.seller.dist.cdf t
      = 1 / 6 := by
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => (1 - t) * t) (fun t ht => by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [uniformBilateral_buyer, uniformBilateral_seller]
    rw [uniformEnv_cdf ht])]
  rw [show (fun t : ℝ => (1 - t) * t) = fun t : ℝ => t - t ^ 2 from funext fun t => by ring,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      ((continuous_pow 2).intervalIntegrable _ _),
    integral_id, integral_pow]
  norm_num

/-- **The library's virtual-gains expression equals `1/6`.** The density-weighted gains
`𝔼_b[θ·F_s(θ)] − 𝔼_s[θ·(1 − F_b(θ))]` — the form manipulated by the impossibility proof — equal
`1/6`, via the layer-cake identity `gains_eq_integral` and `uniformBilateral_survival_integral`. -/
theorem uniformBilateral_gains :
    (∫ θ in (0 : ℝ)..1,
        uniformBilateral.buyer.dist.density θ * (θ * uniformBilateral.seller.dist.cdf θ))
      - (∫ θ in (0 : ℝ)..1,
        uniformBilateral.seller.dist.density θ * (θ * (1 - uniformBilateral.buyer.dist.cdf θ)))
      = 1 / 6 := by
  have h := gains_eq_integral uniformEnv uniformEnv
  rw [show uniformEnv.θlo = (0 : ℝ) from rfl, show uniformEnv.θhi = (1 : ℝ) from rfl,
    min_self, max_self] at h
  have hs := uniformBilateral_survival_integral
  simp only [uniformBilateral_buyer, uniformBilateral_seller] at hs
  simp only [uniformBilateral_buyer, uniformBilateral_seller]
  rw [h]
  exact hs

/-- **Myerson–Satterthwaite for uniform traders.** No mechanism for the uniform-`[0,1]` bilateral
environment is at once buyer- and seller-incentive-compatible, individually rational for both,
ex-post efficient, and weakly budget balanced — even though efficient trade would generate strictly
positive expected gains. -/
theorem uniformBilateral_impossible :
    ¬ ∃ M : uniformBilateral.Mechanism, M.BuyerBIC ∧ M.SellerBIC ∧ M.BuyerIR ∧ M.SellerIR ∧
      M.Efficient ∧ M.WeaklyBudgetBalanced :=
  myerson_satterthwaite uniformBilateral

end EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform
