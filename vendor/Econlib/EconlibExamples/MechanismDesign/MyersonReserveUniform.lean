/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Myerson virtual value and optimal reserve for the uniform type (worked example)

The textbook single-parameter screening benchmark: Values are **uniform on `[0, 1]`**. We build the
corresponding `ScreeningEnv` and derive Myerson's virtual value and optimal reserve:

* `myersonUniform_virtualValue` — `ψ(θ) = 2θ − 1` on `[0, 1]` (since `F(θ) = θ`, `f ≡ 1`);
* `myersonUniform_regular` / `myersonUniform_virtualValue_strictMonoOn` — `ψ` is (strictly)
  monotone, so the environment is **regular**;
* `myersonUniform_reservePrice` / `_unique` / `myersonUniform_virtualValue_nonneg_iff` — `ψ`
  vanishes at `1/2` *only*, and its sign switches there: `0 ≤ ψ(θ) ↔ 1/2 ≤ θ` on `[0, 1]`.

"No ironing needed" is demonstrated, not just asserted:

* `myersonUniform_ironedVirtualValue` — the ironed virtual value `ψ̄` of the `Screening.Ironing`
  layer **equals** `ψ` on `[0, 1]`: The quantile-space primitive `H(q) = q² − q` is already convex,
  so the convex envelope (and its right derivative) is idle.

What makes `1/2` the *optimal reserve*, via the `Auction` layer over this environment:

* `myersonOptimalAuction` — Myerson's optimal auction (highest-`ψ` allocation + Myerson payments);
  it is BIC (`myersonOptimalAuction_isBIC`), leaves the lowest type zero rent (`_zero_rent`), serves
  only types `≥ 1/2` (`_winner_above_reserve`), and withholds the unit exactly when every bidder is
  below `1/2` (`_withholds_iff`);
* `myersonOptimalAuction_optimal` — it revenue-dominates **every** individually rational, BIC
  auction (`revenue_le_optimalVirtualSurplus` + attainment `myersonOptimalAuction_revenue_eq`).

With a single buyer (`n = 1`) the optimal auction is the textbook **posted price**:

* `monopoly_pay_of_reserve_le` / `monopoly_pay_of_lt_reserve` — a served buyer pays exactly `1/2`,
  an excluded buyer pays nothing;
* `monopoly_revenue_eq` / `monopoly_revenue_le` — the optimal revenue is
  `p(1 − F(p)) = 1/2 · 1/2 = 1/4`, and no BIC, individually rational selling mechanism beats it.

It doubles as a regression test of the `Transfers.SingleParameter` screening, ironing, and
optimal-auction APIs.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.MyersonReserveUniform

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.Probability
open Set MeasureTheory

/-- The uniform-`[0,1]` screening environment. -/
def myersonUniform : ScreeningEnv := ScreeningEnv.uniform 0 1 (by norm_num)

@[simp] lemma myersonUniform_θlo : myersonUniform.θlo = 0 := rfl
@[simp] lemma myersonUniform_θhi : myersonUniform.θhi = 1 := rfl

/-- On `[0, 1]` the uniform CDF is the identity: `F(x) = x`. -/
lemma myersonUniform_cdf {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : myersonUniform.dist.cdf x = x := by
  rw [myersonUniform, ScreeningEnv.uniform_dist, ContDist.uniform_cdf_of_mem 0 1 (by norm_num) hx]
  ring

/-- On `[0, 1]` the uniform density is `1`. -/
lemma myersonUniform_density {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    myersonUniform.dist.density x = 1 := by
  rw [myersonUniform, ScreeningEnv.uniform_dist,
    ContDist.uniform_density_of_mem 0 1 (by norm_num) hx]
  norm_num

/-- On `[0, 1]` the virtual value of the uniform type is `ψ(θ) = 2θ − 1`. -/
theorem myersonUniform_virtualValue {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    myersonUniform.virtualValue θ = 2 * θ - 1 := by
  rw [ScreeningEnv.virtualValue_def, myersonUniform_cdf hθ, myersonUniform_density hθ]; ring

/-- The uniform environment is **regular**: The virtual value is monotone. -/
theorem myersonUniform_regular : myersonUniform.Regular := by
  intro θ hθ θ' hθ' hle
  have e := myersonUniform_virtualValue (θ := θ) (by simpa using hθ)
  have e' := myersonUniform_virtualValue (θ := θ') (by simpa using hθ')
  rw [e, e']; linarith

/-- The **optimal reserve price** for the uniform type — the type at which the virtual value
crosses zero — is `1/2`. -/
theorem myersonUniform_reservePrice : myersonUniform.virtualValue (1 / 2) = 0 := by
  rw [myersonUniform_virtualValue (by norm_num)]; norm_num

/-! ## Strictness and the sign of the virtual value

`Regular` is only weak monotonicity, so `ψ(1/2) = 0` alone would not identify `1/2` as the
crossing — a weakly monotone `ψ` may vanish on an interval. For the uniform type `ψ` is strictly
increasing, its sign switches exactly at `1/2`, and the zero is unique. -/

/-- The uniform virtual value is **strictly** monotone on the type interval. -/
theorem myersonUniform_virtualValue_strictMonoOn :
    StrictMonoOn myersonUniform.virtualValue (Icc (0 : ℝ) 1) := by
  intro θ hθ θ' hθ' hlt
  rw [myersonUniform_virtualValue hθ, myersonUniform_virtualValue hθ']
  linarith

/-- **Sign characterization, negative side**: On `[0, 1]`, `ψ(θ) < 0 ↔ θ < 1/2`. -/
theorem myersonUniform_virtualValue_neg_iff {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    myersonUniform.virtualValue θ < 0 ↔ θ < 1 / 2 := by
  rw [myersonUniform_virtualValue hθ]
  constructor <;> intro h <;> linarith

/-- **Sign characterization, nonnegative side**: On `[0, 1]`, `0 ≤ ψ(θ) ↔ 1/2 ≤ θ`. -/
theorem myersonUniform_virtualValue_nonneg_iff {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    0 ≤ myersonUniform.virtualValue θ ↔ 1 / 2 ≤ θ := by
  rw [← not_lt, myersonUniform_virtualValue_neg_iff hθ, not_lt]

/-- The zero of the virtual value is **unique**: `1/2` is the reserve type, not merely a type
where `ψ` vanishes. -/
theorem myersonUniform_reservePrice_unique {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (h : myersonUniform.virtualValue θ = 0) : θ = 1 / 2 := by
  have := myersonUniform_virtualValue hθ
  rw [h] at this
  linarith

/-! ## No ironing needed: `ψ̄ = ψ`

The docstring's aside — regularity means the Ironing layer is unnecessary — made demonstrable:
On the uniform environment the ironed virtual value *coincides* with the raw one. In quantile space
the pulled-back virtual value is `h(q) = 2q − 1`, its primitive `H(q) = q² − q` is already convex,
so the convex envelope (and hence its right derivative `ĥ`) changes nothing. -/

/-- The uniform quantile function is the identity on `(0, 1)`. -/
lemma myersonUniform_quantileInv {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    myersonUniform.quantileInv q = q := by
  -- `F(F⁻¹ q) = q` and `F = id` on the type interval, where `F⁻¹ q` lives.
  have hmem : myersonUniform.quantileInv q ∈ Icc (0 : ℝ) 1 := myersonUniform.quantileInv_mem hq
  have hcdf : myersonUniform.dist.cdf (myersonUniform.quantileInv q) = q :=
    myersonUniform.dist.cdf_quantile hq
  rwa [myersonUniform_cdf hmem] at hcdf

/-- The virtual value pulled back to quantile space: `h(q) = ψ(F⁻¹ q) = 2q − 1`. -/
lemma myersonUniform_vvQuantile {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    myersonUniform.vvQuantile q = 2 * q - 1 := by
  rw [ScreeningEnv.vvQuantile_def, myersonUniform_quantileInv hq,
    myersonUniform_virtualValue ⟨hq.1.le, hq.2.le⟩]

/-- The quantile-space primitive `H(q) = ∫₀^q h = q² − q` on `[0, 1]`. -/
lemma myersonUniform_vvPrimitive {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    myersonUniform.vvPrimitive q = q ^ 2 - q := by
  rw [ScreeningEnv.vvPrimitive_def]
  -- The integrand is `2u − 1` on the integration range, up to the null endpoint `u = 1`.
  have hcong : (∫ u in (0 : ℝ)..q, myersonUniform.vvQuantile u)
      = ∫ u in (0 : ℝ)..q, (2 * u - 1) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hone : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ (1 : ℝ) := by
      rw [ae_iff]; simp only [not_not]; exact measure_singleton 1
    filter_upwards [hone] with u hu1 huI
    rw [uIoc_of_le hq.1] at huI
    exact myersonUniform_vvQuantile ⟨huI.1, lt_of_le_of_ne (le_trans huI.2 hq.2) hu1⟩
  have h2u : IntervalIntegrable (fun u : ℝ => 2 * u) volume 0 q :=
    (by fun_prop : Continuous fun u : ℝ => 2 * u).intervalIntegrable 0 q
  rw [hcong, intervalIntegral.integral_sub h2u intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- `H(q) = q² − q` is already convex, so the convex envelope is `H` itself: The ironing step is
idle. Each point of `[0, 1]` is a contact point of the supporting line of `H` there. -/
lemma myersonUniform_ironedPrimitive {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    myersonUniform.ironedPrimitive q = myersonUniform.vvPrimitive q := by
  rw [ScreeningEnv.ironedPrimitive_def]
  -- The supporting line of `u ↦ u² − u` at `q` has slope `2q − 1` and intercept `−q²`.
  refine convexEnvelope_eq_of_affineMinorant_contact (by norm_num)
    myersonUniform.vvPrimitive_continuousOn hq (m := 2 * q - 1) (c := -q ^ 2) ?_ ?_
  · intro u hu
    rw [myersonUniform_vvPrimitive hu]
    nlinarith [sq_nonneg (u - q)]
  · rw [myersonUniform_vvPrimitive hq]; ring

/-- The right derivative of the (idle) envelope on `(0, 1)` is `2t − 1`. -/
lemma myersonUniform_ironedPrimitive_rightDeriv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin myersonUniform.ironedPrimitive (Ioi t) t = 2 * t - 1 := by
  -- Near `t` the envelope is the polynomial `u² − u`, so the derivative is `2t − 1`.
  have hpoly : HasDerivWithinAt (fun u : ℝ => u ^ 2 - u) (2 * t - 1) (Ioi t) t := by
    have h := (hasDerivAt_pow 2 t).sub (hasDerivAt_id t)
    norm_num at h
    exact h.hasDerivWithinAt
  have heq : myersonUniform.ironedPrimitive =ᶠ[nhds t] fun u => u ^ 2 - u := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [myersonUniform_ironedPrimitive ⟨hu.1.le, hu.2.le⟩,
      myersonUniform_vvPrimitive ⟨hu.1.le, hu.2.le⟩]
  exact (hpoly.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
    heq.eq_of_nhds).derivWithin (uniqueDiffWithinAt_Ioi t)

/-- The right derivatives of the envelope over `(0, 1)` form the open interval `(−1, 1)`. -/
private lemma myersonUniform_rightDeriv_image :
    (fun x => derivWithin myersonUniform.ironedPrimitive (Ioi x) x) '' Ioo (0 : ℝ) 1
      = Ioo (-1 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    dsimp only
    rw [myersonUniform_ironedPrimitive_rightDeriv hx]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rintro ⟨hy1, hy2⟩
    exact ⟨(y + 1) / 2, ⟨by linarith, by linarith⟩, by
      dsimp only
      rw [myersonUniform_ironedPrimitive_rightDeriv ⟨by linarith, by linarith⟩]; ring⟩

/-- The ironed quantile-space virtual value `ĥ = Ĥ'₊` is `2t − 1` throughout `[0, 1]` (interior by
differentiation, endpoints by the inf/sup extension of the right derivative). -/
lemma myersonUniform_ironedVVQuantile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    myersonUniform.ironedVVQuantile t = 2 * t - 1 := by
  unfold ScreeningEnv.ironedVVQuantile
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · -- `t = 0`: the extension takes the infimum of the interior right derivatives, `−1`.
    rw [myersonUniform.ironedPrimitive_convexOn.rightDerivExtend_of_le_left (by norm_num)
        (le_of_eq h0.symm),
      myersonUniform_rightDeriv_image, csInf_Ioo (by norm_num : (-1 : ℝ) < 1)]
    rw [← h0]; norm_num
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · -- `t = 1`: the extension takes the supremum of the interior right derivatives, `1`.
    rw [myersonUniform.ironedPrimitive_convexOn.rightDerivExtend_of_right_le (by norm_num)
        h1.ge,
      myersonUniform_rightDeriv_image, csSup_Ioo (by norm_num : (-1 : ℝ) < 1)]
    rw [h1]; norm_num
  · -- Interior: the extension is the right derivative itself.
    rw [myersonUniform.ironedPrimitive_convexOn.rightDerivExtend_eq_of_mem_Ioo (by norm_num)
        ⟨h0, h1⟩]
    exact myersonUniform_ironedPrimitive_rightDeriv ⟨h0, h1⟩

/-- **No ironing needed, demonstrated**: On the (regular) uniform environment the ironed virtual
value equals the raw virtual value throughout the type interval. -/
theorem myersonUniform_ironedVirtualValue {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    myersonUniform.ironedVirtualValue θ = myersonUniform.virtualValue θ := by
  rw [ScreeningEnv.ironedVirtualValue_def, myersonUniform_cdf hθ,
    myersonUniform_ironedVVQuantile hθ, myersonUniform_virtualValue hθ]

/-! ## The optimal auction: Reserve `1/2`

What makes `1/2` *the optimal reserve*: In the symmetric auction over this environment,
Myerson's optimal mechanism — highest virtual value wins if nonnegative, Myerson payments — awards
the unit only to types `≥ 1/2`, withholds it exactly when every bidder is below `1/2`, and
revenue-dominates every incentive-compatible auction that leaves the lowest type no rent. -/

/-- The symmetric `n`-bidder auction over the uniform-`[0, 1]` environment. -/
def myersonAuction (n : ℕ) (hn : 0 < n) : AuctionEnv where
  n := n
  hn := hn
  base := myersonUniform

@[simp] lemma myersonAuction_base (n : ℕ) (hn : 0 < n) :
    (myersonAuction n hn).base = myersonUniform := rfl

@[simp] lemma myersonAuction_n (n : ℕ) (hn : 0 < n) : (myersonAuction n hn).n = n := rfl

/-- **Myerson's optimal auction** for the uniform environment: Award the unit to the highest
virtual value if nonnegative (reserve `1/2`), charge the Myerson payments. -/
def myersonOptimalAuction (n : ℕ) (hn : 0 < n) : AuctionMechanism (myersonAuction n hn) :=
  (myersonAuction n hn).optimalAlloc.myersonMechanism

/-- Every reduced optimal allocation is monotone — regularity makes the highest-`ψ` rule
implementable. -/
lemma myersonAuction_optimalAlloc_monotone (n : ℕ) (hn : 0 < n)
    (i : Fin (myersonAuction n hn).n) :
    MonotoneAlloc ((myersonAuction n hn).optimalAlloc.reducedAlloc i) :=
  (myersonAuction n hn).highestAlloc_interimAlloc_monotoneOn
    (myersonAuction n hn).base.virtualValue_measurable myersonUniform_regular i

/-- **Only types above the reserve are ever served.** On the type box, a bidder receiving the unit
with positive probability has type at least `1/2`. -/
theorem myersonOptimalAuction_winner_above_reserve (n : ℕ) (hn : 0 < n)
    {θ : (myersonAuction n hn).Profile} (hθ : ∀ j, θ j ∈ Icc (0 : ℝ) 1)
    {i : Fin (myersonAuction n hn).n}
    (h : (myersonOptimalAuction n hn).alloc.x θ i ≠ 0) : 1 / 2 ≤ θ i := by
  -- A nonzero allocation forces top-bidder status, whose first conjunct is `0 ≤ ψ(θᵢ)`.
  have htop : (myersonAuction n hn).IsTopBidder
      (myersonAuction n hn).base.virtualValue θ i := by
    by_contra hnot
    exact h (AuctionEnv.highestAlloc_x_of_not_top
      (myersonAuction n hn).base.virtualValue_measurable hnot)
  exact (myersonUniform_virtualValue_nonneg_iff (hθ i)).mp htop.1

/-- **The unit is withheld exactly when every bidder is below the reserve.** -/
theorem myersonOptimalAuction_withholds_iff (n : ℕ) (hn : 0 < n)
    {θ : (myersonAuction n hn).Profile} (hθ : ∀ j, θ j ∈ Icc (0 : ℝ) 1) :
    (∀ i, (myersonOptimalAuction n hn).alloc.x θ i = 0) ↔ ∀ i, θ i < 1 / 2 := by
  constructor
  · -- Withheld → all below: a bidder at or above the reserve would put the top virtual value
    -- above zero, producing a winner.
    intro hall i
    by_contra hge
    rw [not_lt] at hge
    have hψ : 0 ≤ (myersonAuction n hn).base.virtualValue (θ i) :=
      (myersonUniform_virtualValue_nonneg_iff (hθ i)).mpr hge
    have hsup : 0 ≤ Finset.univ.sup' (myersonAuction n hn).univ_nonempty
        (fun j => (myersonAuction n hn).base.virtualValue (θ j)) :=
      le_trans hψ (Finset.le_sup'
        (fun j => (myersonAuction n hn).base.virtualValue (θ j)) (Finset.mem_univ i))
    obtain ⟨w, hw, -⟩ := AuctionEnv.exists_isTopBidder_of_sup'_nonneg hsup
    have hone : (myersonOptimalAuction n hn).alloc.x θ w = 1 :=
      AuctionEnv.highestAlloc_x_of_top
        (myersonAuction n hn).base.virtualValue_measurable hw
    rw [hall w] at hone
    norm_num at hone
  · -- All below → withheld: no bidder can satisfy the nonnegativity conjunct of top-bidder
    -- status, since `ψ(θᵢ) < 0` strictly below the reserve.
    intro hall i
    refine AuctionEnv.highestAlloc_x_of_not_top
      (myersonAuction n hn).base.virtualValue_measurable (fun htop => ?_)
    exact absurd ((myersonUniform_virtualValue_nonneg_iff (hθ i)).mp htop.1)
      (not_le.mpr (hall i))

/-- The optimal auction is Bayesian incentive compatible. -/
theorem myersonOptimalAuction_isBIC (n : ℕ) (hn : 0 < n) : (myersonOptimalAuction n hn).IsBIC :=
  (myersonAuction n hn).optimalAlloc.myersonMechanism_isBIC
    (myersonAuction_optimalAlloc_monotone n hn)

/-- The optimal auction leaves the lowest type zero rent. -/
theorem myersonOptimalAuction_zero_rent (n : ℕ) (hn : 0 < n)
    (i : Fin (myersonAuction n hn).n) :
    ((myersonOptimalAuction n hn).reducedMechanism i).interimUtil
      (myersonAuction n hn).base.θlo = 0 :=
  (myersonAuction n hn).optimalAlloc.myersonMechanism_interimUtil_zero i

/-- The optimal auction's expected revenue **attains** Myerson's bound: The integrated optimal
virtual surplus `∫ max(0, maxᵢ ψ(θᵢ))`. -/
theorem myersonOptimalAuction_revenue_eq (n : ℕ) (hn : 0 < n) :
    (∫ θ, ∑ i, (myersonOptimalAuction n hn).pay θ i ∂(myersonAuction n hn).jointLaw)
      = ∫ θ, (myersonAuction n hn).optimalVirtualSurplus θ ∂(myersonAuction n hn).jointLaw := by
  unfold myersonOptimalAuction
  rw [(myersonAuction n hn).optimalAlloc.myersonMechanism_revenue
      (myersonAuction_optimalAlloc_monotone n hn),
    (myersonAuction n hn).optimalAlloc.sum_expect_virtualSurplus_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact (myersonAuction n hn).highestAlloc_virtualSurplus_eq
    (myersonAuction n hn).base.virtualValue_measurable θ

/-- **Optimality.** No individually rational, incentive-compatible auction raises more expected
revenue than Myerson's optimal auction — the reserve-`1/2` mechanism is revenue-maximal over the
full admissible class on the uniform environment. -/
theorem myersonOptimalAuction_optimal (n : ℕ) (hn : 0 < n)
    (M : AuctionMechanism (myersonAuction n hn)) (hbic : M.IsBIC) (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂(myersonAuction n hn).jointLaw)
      ≤ ∫ θ, ∑ i, (myersonOptimalAuction n hn).pay θ i ∂(myersonAuction n hn).jointLaw :=
  le_trans (M.revenue_le_optimalVirtualSurplus hbic hbir)
    (myersonOptimalAuction_revenue_eq n hn).ge

/-! ## The monopoly case `n = 1`: A posted price of `1/2`, revenue `1/4`

With a single buyer the optimal auction is the textbook posted price: Serve the buyer iff
`θ ≥ 1/2`, charge exactly `1/2` when serving — and its expected revenue
`p · (1 − F(p)) = 1/2 · 1/2 = 1/4` is the most any incentive-compatible, individually rational
selling mechanism can raise. -/

/-- With one bidder the index set is a singleton. -/
private lemma monopoly_fin_eq (j i : Fin (myersonAuction 1 Nat.one_pos).n) : j = i :=
  Fin.ext (by
    have hj : j.val < 1 := j.isLt
    have hi : i.val < 1 := i.isLt
    omega)

/-- With one buyer, the optimal allocation's interim form is the threshold rule, "serve" side:
Above the reserve the buyer receives the unit surely. -/
lemma monopoly_interimAlloc_of_reserve_le (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : 1 / 2 ≤ t) :
    (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i t = 1 := by
  have hψ : 0 ≤ (myersonAuction 1 Nat.one_pos).base.virtualValue t :=
    (myersonUniform_virtualValue_nonneg_iff ht).mpr hres
  -- With no rivals, a nonnegative virtual value makes the buyer the top bidder at every profile.
  have hxθ : ∀ θ : (myersonAuction 1 Nat.one_pos).Profile,
      (myersonAuction 1 Nat.one_pos).optimalAlloc.x (Function.update θ i t) i = 1 := by
    intro θ
    refine AuctionEnv.highestAlloc_x_of_top
      (myersonAuction 1 Nat.one_pos).base.virtualValue_measurable ⟨?_, ?_, ?_⟩
    · rw [Function.update_self]; exact hψ
    · intro j
      have hj : j = i := monopoly_fin_eq j i
      subst hj
      exact le_rfl
    · intro j hj
      rw [monopoly_fin_eq j i] at hj
      exact absurd hj (lt_irrefl i)
  rw [ExPostAlloc.interimAlloc_def,
    integral_congr_ae (Filter.Eventually.of_forall fun θ => hxθ θ), integral_const]
  haveI : IsProbabilityMeasure (myersonUniform.dist.piMeasure 1) :=
    myersonUniform.dist.isProbabilityMeasure_piMeasure 1
  simp only [probReal_univ, one_smul]

/-- With one buyer, the optimal allocation's interim form is the threshold rule, "exclude" side:
Below the reserve the buyer never receives the unit. -/
lemma monopoly_interimAlloc_of_lt_reserve (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : t < 1 / 2) :
    (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i t = 0 := by
  have hψ : (myersonAuction 1 Nat.one_pos).base.virtualValue t < 0 :=
    (myersonUniform_virtualValue_neg_iff ht).mpr hres
  -- A negative virtual value fails the nonnegativity conjunct of top-bidder status.
  have hxθ : ∀ θ : (myersonAuction 1 Nat.one_pos).Profile,
      (myersonAuction 1 Nat.one_pos).optimalAlloc.x (Function.update θ i t) i = 0 := by
    intro θ
    refine AuctionEnv.highestAlloc_x_of_not_top
      (myersonAuction 1 Nat.one_pos).base.virtualValue_measurable (fun htop => ?_)
    have h0 := htop.1
    rw [Function.update_self] at h0
    exact absurd h0 (not_le.mpr hψ)
  rw [ExPostAlloc.interimAlloc_def,
    integral_congr_ae (Filter.Eventually.of_forall fun θ => hxθ θ), integral_zero]

/-- The cumulative interim allocation below the reserve vanishes: `∫₀ᵗ x̄ = 0` for `t < 1/2`. -/
private lemma monopoly_integral_interimAlloc_of_lt (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : t < 1 / 2) :
    (∫ s in (0 : ℝ)..t, (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i s) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => ?_),
    intervalIntegral.integral_zero]
  rw [uIcc_of_le ht.1] at hs
  exact monopoly_interimAlloc_of_lt_reserve i ⟨hs.1, le_trans hs.2 ht.2⟩
    (lt_of_le_of_lt hs.2 hres)

/-- The cumulative interim allocation above the reserve: `∫₀ᵗ x̄ = t − 1/2` for `t ≥ 1/2`. -/
private lemma monopoly_integral_interimAlloc_of_le (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : 1 / 2 ≤ t) :
    (∫ s in (0 : ℝ)..t, (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i s)
      = t - 1 / 2 := by
  -- Split at the reserve: zero below, surely-served above.
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((myersonAuction 1 Nat.one_pos).optimalAlloc.intervalIntegrable_interimAlloc i 0 (1 / 2))
    ((myersonAuction 1 Nat.one_pos).optimalAlloc.intervalIntegrable_interimAlloc i (1 / 2) t)
  have hlow : (∫ s in (0 : ℝ)..(1 / 2 : ℝ),
      (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i s) = 0 := by
    -- The integrand vanishes below the reserve; the boundary point `1/2` is null.
    have hcong : (∫ s in (0 : ℝ)..(1 / 2 : ℝ),
        (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i s)
        = ∫ s in (0 : ℝ)..(1 / 2 : ℝ), (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hhalf : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (1 / 2 : ℝ) := by
        rw [ae_iff]; simp only [not_not]; exact measure_singleton _
      filter_upwards [hhalf] with s hs hsI
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsI
      exact monopoly_interimAlloc_of_lt_reserve i ⟨hsI.1.le, by linarith [hsI.2]⟩
        (lt_of_le_of_ne hsI.2 hs)
    rw [hcong, intervalIntegral.integral_zero]
  have hhigh : (∫ s in (1 / 2 : ℝ)..t,
      (myersonAuction 1 Nat.one_pos).optimalAlloc.interimAlloc i s) = t - 1 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun s hs => ?_),
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    rw [uIcc_of_le hres] at hs
    exact monopoly_interimAlloc_of_reserve_le i ⟨by linarith [hs.1], le_trans hs.2 ht.2⟩ hs.1
  linarith [hsplit, hlow, hhigh]

/-- A served buyer's Myerson payment is the reserve: `t·1 − (t − 1/2) = 1/2`. -/
private lemma monopoly_myersonPayment_of_reserve_le (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : 1 / 2 ≤ t) :
    (((myersonAuction 1 Nat.one_pos).optimalAlloc.reducedAlloc i)).myersonPayment t = 1 / 2 := by
  simp only [AllocationRule.myersonPayment, ExPostAlloc.reducedAlloc_x]
  rw [myersonAuction_base, myersonUniform_θlo,
    monopoly_interimAlloc_of_reserve_le i ht hres,
    monopoly_integral_interimAlloc_of_le i ht hres]
  ring

/-- An excluded buyer's Myerson payment vanishes: `t·0 − 0 = 0`. -/
private lemma monopoly_myersonPayment_of_lt_reserve (i : Fin (myersonAuction 1 Nat.one_pos).n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hres : t < 1 / 2) :
    (((myersonAuction 1 Nat.one_pos).optimalAlloc.reducedAlloc i)).myersonPayment t = 0 := by
  simp only [AllocationRule.myersonPayment, ExPostAlloc.reducedAlloc_x]
  rw [myersonAuction_base, myersonUniform_θlo,
    monopoly_interimAlloc_of_lt_reserve i ht hres,
    monopoly_integral_interimAlloc_of_lt i ht hres]
  ring

/-- **The optimal selling mechanism is a posted price `1/2`, "buy" side**: A served buyer pays
exactly the reserve `1/2` — independent of its type. -/
theorem monopoly_pay_of_reserve_le {θ : (myersonAuction 1 Nat.one_pos).Profile}
    (i : Fin (myersonAuction 1 Nat.one_pos).n) (hθ : θ i ∈ Icc (0 : ℝ) 1)
    (hres : 1 / 2 ≤ θ i) : (myersonOptimalAuction 1 Nat.one_pos).pay θ i = 1 / 2 := by
  unfold myersonOptimalAuction
  rw [ExPostAlloc.myersonMechanism_pay]
  exact monopoly_myersonPayment_of_reserve_le i hθ hres

/-- **The optimal selling mechanism is a posted price `1/2`, "walk away" side**: An excluded buyer
pays nothing. -/
theorem monopoly_pay_of_lt_reserve {θ : (myersonAuction 1 Nat.one_pos).Profile}
    (i : Fin (myersonAuction 1 Nat.one_pos).n) (hθ : θ i ∈ Icc (0 : ℝ) 1)
    (hres : θ i < 1 / 2) : (myersonOptimalAuction 1 Nat.one_pos).pay θ i = 0 := by
  unfold myersonOptimalAuction
  rw [ExPostAlloc.myersonMechanism_pay]
  exact monopoly_myersonPayment_of_lt_reserve i hθ hres

/-- **The optimal monopoly revenue is `1/4`** — the posted price `1/2` is paid with probability
`P(θ ≥ 1/2) = 1/2`. -/
theorem monopoly_revenue_eq :
    (∫ θ, ∑ i, (myersonOptimalAuction 1 Nat.one_pos).pay θ i
      ∂(myersonAuction 1 Nat.one_pos).jointLaw) = 1 / 4 := by
  rw [MeasureTheory.integral_finset_sum _
    (fun i _ => (myersonOptimalAuction 1 Nat.one_pos).pay_integrable i)]
  -- The single buyer's expected interim payment is `1/2 · P(θ ≥ 1/2) = 1/4`.
  have hterm : ∀ i : Fin (myersonAuction 1 Nat.one_pos).n,
      (∫ θ, (myersonOptimalAuction 1 Nat.one_pos).pay θ i
        ∂(myersonAuction 1 Nat.one_pos).jointLaw) = 1 / 4 := by
    intro i
    unfold myersonOptimalAuction
    rw [AuctionMechanism.expected_interimPay_eq, ExPostAlloc.myersonMechanism_interimPay,
      ScreeningEnv.expect_eq_intervalIntegral,
      show (myersonAuction 1 Nat.one_pos).base.θlo = 0 from rfl,
      show (myersonAuction 1 Nat.one_pos).base.θhi = 1 from rfl,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    -- On `(0, 1]` the integrand is exactly the posted-price indicator `(1/2)·𝟙{s ≥ 1/2}`.
    rw [setIntegral_congr_fun (g := (Ici (1 / 2 : ℝ)).indicator (fun _ => (1 / 2 : ℝ)))
      measurableSet_Ioc (fun s hs => ?_)]
    · rw [integral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici,
        show Ici (1 / 2 : ℝ) ∩ Ioc 0 1 = Icc (1 / 2 : ℝ) 1 by
          ext s
          simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩,
        setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
      norm_num
    · have hden : (myersonAuction 1 Nat.one_pos).base.dist.density s = 1 :=
        myersonUniform_density ⟨hs.1.le, hs.2⟩
      by_cases hres : (1 / 2 : ℝ) ≤ s
      · rw [monopoly_myersonPayment_of_reserve_le i ⟨hs.1.le, hs.2⟩ hres, hden, one_mul,
          Set.indicator_of_mem (mem_Ici.mpr hres)]
      · rw [monopoly_myersonPayment_of_lt_reserve i ⟨hs.1.le, hs.2⟩ (not_le.mp hres),
          mul_zero, Set.indicator_of_notMem (show s ∉ Ici (1 / 2 : ℝ) from hres)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ]
  simp

/-- **The `1/4` bound.** No individually rational, incentive-compatible mechanism for selling to a
single uniform buyer raises expected revenue above `1/4`. -/
theorem monopoly_revenue_le (M : AuctionMechanism (myersonAuction 1 Nat.one_pos)) (hbic : M.IsBIC)
    (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂(myersonAuction 1 Nat.one_pos).jointLaw) ≤ 1 / 4 :=
  le_trans (myersonOptimalAuction_optimal 1 Nat.one_pos M hbic hbir)
    (le_of_eq monopoly_revenue_eq)

end EconlibExamples.MechanismDesign.MyersonReserveUniform
