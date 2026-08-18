/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.MechanismDesign.MyersonReserveUniform
import Mathlib

/-!
# Single-parameter screening and optimal-auction non-vacuity witnesses

Compile-time semantic witnesses for the `Transfers.SingleParameter` **screening** layer
(`myerson_lemma`, the envelope two-sided bounds, the Myerson payment / revenue identity, virtual
value) and the **optimal-auction / ironing** layer (`exists_optimal_auction_{regular,ironed}`,
`myersonMechanism_{bic,IsBIR,revenue}`, `revenue_le_ironedOptimalVirtualSurplus`, the ironing
machinery). Anchored on the uniform-`[0, 1]` screening environment `myersonUniform` of
`EconlibExamples.MechanismDesign.MyersonReserveUniform` (and its `n`-bidder auction
`myersonAuction`), so every abstract incentive / envelope / virtual-value statement is forced
through real numbers where `ψ(θ) = 2θ − 1`, the reserve is `1/2`, and the lowest type's rent is `0`.

The hand-computation anchoring the numeric claims (uniform `[0, 1]`, so `F(θ) = θ`, `f ≡ 1`):

* virtual value `ψ(θ) = θ − (1 − θ)/1 = 2θ − 1`; vanishes at `1/2`, the reserve type.
* For the **always-allocate** rule `x ≡ 1` (`alwaysAlloc`, trivially monotone), the Myerson payment
  is `p(θ) = θ·1 − ∫₀^θ 1 = θ − θ = 0`: A posted price of `0`, leaving every type its full surplus
  `θ` and the lowest type *zero* rent. The interim utility under the Myerson payment is
  `∫₀^θ 1 = θ`.

## What each block catches

* **Incentive compatibility direction** (`IsBIC.reportUtil_le`, `reportUtil_self`,
  `reportUtil_strict_loss_witness`): Truth-telling weakly dominates every misreport. On the
  *nonconstant* clipped-identity rule a type-`3/4` agent misreporting `1/4` earns `5/32 < 9/32`, a
  **strict** loss — so a flipped inequality exposing misreporting as optimal is caught (the constant
  rule tied every report).
* **Myerson's lemma** (`myerson_lemma`): Implementable ⟺ monotone — checked in *both* directions on
  `alwaysAlloc`, and on the auction-layer reduced allocation. Monotonicity is anchored *strictly*
  on the clipped-identity rule (`x(1/4) = 1/4 < 3/4 = x(3/4)`).
* **The envelope two-sided bound** (`sub_mul_le_interimUtil_sub`, `interimUtil_sub_le_sub_mul`,
  `envelope_distinct_anchors_witness`): `(t − r)·x(r) ≤ U(t) − U(r) ≤ (t − r)·x(t)`, with the three
  terms anchored to **distinct** values `1/8 ≤ 1/4 ≤ 3/8` on the clipped-identity rule, so an
  `x(r) ↔ x(t)` swap flips `1/8 ↔ 3/8` and breaks the sandwich.
* **Revenue identity sign** (`payment_eq_sub_rent`, `payment_eq`,
  `payment_eq_sub_rent_nonzero_rent_witness`): `p(θ) = θ·x(θ) − U(θlo) − ∫x` — the
  virtual-value-minus-rent decomposition with the correct sign. The rent term is made *active* by a
  subsidized BIC mechanism with `U(θlo) = 1/8 ≠ 0`, so a wrong rent sign is no longer silent.
* **The lowest type binds at zero rent** (`interimUtil_myersonMechanism` at `θlo`):
  `U(θlo) = ∫_{θlo}^{θlo} x = 0`, the IR-binding endpoint.
* **Individual rationality direction** (`myersonMechanism_BIR`, the auction-layer BIR): Interim
  utility `≥ 0`, *not* `< 0`.
* **Optimal-revenue attainment & universal upper bound** (`exists_optimal_auction_regular`,
  `exists_optimal_auction_ironed`, `revenue_le_ironedOptimalVirtualSurplus_witness`): The optimal
  revenue *equals* the (ironed) virtual surplus bound, and — for **every** BIC, BIR auction `M`
  (universally quantified, not just the optimum) — `revenue M ≤ ironedOptimalVirtualSurplus`. A `≥`
  reversal would falsely make the bound a lower bound for all auctions.
* **Ironing degeneration** (`ironedVVQuantile_monotone`, `ironedVVQuantile_eq_of_affineOn`,
  `ironedPrimitive_convexOn`, `integral_ironedVVQuantile_sub_vvQuantile`,
  `allocQuantile_monotoneOn`): On the *regular* uniform environment `ψ̄ = ψ`
  (`myersonUniform_ironedVVQuantile = 2t − 1`), the primitive `H(q) = q² − q` is convex, and the
  ironing gap vanishes — the regular-case degeneration of the ironing API. The complementary
  *irregular* instance, where `ψ̄ ≠ ψ` and the ironing gap is nonzero, is the worked example
  `EconlibExamples.MechanismDesign.MyersonIroning`.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.TransfersScreening

open Econlib.MechanismDesign.Transfers.SingleParameter
open Econlib.Probability
open Set MeasureTheory
open EconlibExamples.MechanismDesign.MyersonReserveUniform
  (myersonUniform myersonUniform_θlo myersonUniform_θhi myersonUniform_virtualValue
    myersonUniform_regular myersonUniform_reservePrice myersonUniform_ironedVVQuantile
    myersonUniform_ironedPrimitive myersonUniform_vvPrimitive myersonUniform_vvQuantile
    myersonAuction myersonAuction_base myersonAuction_n myersonOptimalAuction
    myersonOptimalAuction_isBIC myersonOptimalAuction_zero_rent
    myersonAuction_optimalAlloc_monotone)

/-! ## Block 1: The `ScreeningEnv` glue on the uniform environment

`myersonUniform` is the concrete `ScreeningEnv` with `θlo = 0`, `θhi = 1`, uniform density. We
check the support / type-membership / virtual-value glue directly on it. -/

/-- **`θlo_mem_types`**: The lowest type `0` lies in the type interval `[0, 1]`. -/
theorem θlo_mem_types_witness : myersonUniform.θlo ∈ myersonUniform.types :=
  myersonUniform.θlo_mem_types

/-- **`θhi_mem_types`**: The highest type `1` lies in the type interval `[0, 1]`. -/
theorem θhi_mem_types_witness : myersonUniform.θhi ∈ myersonUniform.types :=
  myersonUniform.θhi_mem_types

/-- **`density_eq_zero_of_notMem`**: Outside `[0, 1]` the uniform density vanishes — the support
glue. Anchored at `θ = 2 ∉ [0, 1]`. -/
theorem density_eq_zero_of_notMem_witness :
    myersonUniform.dist.density 2 = 0 :=
  myersonUniform.density_eq_zero_of_notMem (by norm_num)

/-- **`virtualValue_def`** unfolds to `ψ(θ) = θ − (1 − F(θ))/f(θ)`, evaluated at `1/2` where the
uniform CDF is `1/2` and the density is `1`, giving `ψ(1/2) = 1/2 − (1 − 1/2)/1 = 0` — the reserve.
A sign error in the rent term `(1 − F)/f` would move the reserve. -/
theorem virtualValue_def_witness :
    myersonUniform.virtualValue (1 / 2)
      = (1 / 2) - (1 - myersonUniform.dist.cdf (1 / 2)) / myersonUniform.dist.density (1 / 2) :=
  myersonUniform.virtualValue_def (1 / 2)

/-- **The uniform CDF and density anchors** `F(1/2) = 1/2` and `f(1/2) = 1`, computed independently
of `virtualValue`. These are the inputs whose values force the reserve. -/
theorem uniform_cdf_density_at_half :
    myersonUniform.dist.cdf (1 / 2) = 1 / 2 ∧ myersonUniform.dist.density (1 / 2) = 1 :=
  ⟨EconlibExamples.MechanismDesign.MyersonReserveUniform.myersonUniform_cdf (by norm_num),
   EconlibExamples.MechanismDesign.MyersonReserveUniform.myersonUniform_density (by norm_num)⟩

/-- **The reserve type's virtual value is exactly `0`**, derived *here* from the independently
checked `F(1/2) = 1/2`, `f(1/2) = 1`: `ψ(1/2) = 1/2 − (1 − 1/2)/1 = 0`. This re-derives the reserve
from the primitive uniform anchors rather than copying `myersonUniform_reservePrice`. -/
theorem virtualValue_reserve_eq_zero : myersonUniform.virtualValue (1 / 2) = 0 := by
  rw [virtualValue_def_witness, uniform_cdf_density_at_half.1, uniform_cdf_density_at_half.2]
  norm_num

/-- **`virtualValue_measurable`**: The virtual value of the uniform environment is measurable (the
input to the optimal-auction integrals). -/
theorem virtualValue_measurable_witness : Measurable myersonUniform.virtualValue :=
  myersonUniform.virtualValue_measurable

/-- **`expect_eq_intervalIntegral`**: The expectation `𝔼[h]` collapses to the support integral
`∫₀¹ density·h`. Checked on `h = id`: `𝔼[θ] = ∫₀¹ density(θ)·θ`. -/
theorem expect_eq_intervalIntegral_witness :
    myersonUniform.dist.expect (fun θ => θ)
      = ∫ θ in (myersonUniform.θlo)..(myersonUniform.θhi), myersonUniform.dist.density θ * θ :=
  myersonUniform.expect_eq_intervalIntegral (fun θ => θ)

/-- **`cdf_eq_intervalIntegral`**: The CDF is the cumulative density on the support,
`F(θ) = ∫_{θlo}^θ density`. Checked at `θ = 1/2`. -/
theorem cdf_eq_intervalIntegral_witness :
    myersonUniform.dist.cdf (1 / 2)
      = ∫ s in (myersonUniform.θlo)..(1 / 2), myersonUniform.dist.density s :=
  myersonUniform.cdf_eq_intervalIntegral (1 / 2)

/-! ## Block 2: A concrete monotone allocation and its Myerson mechanism

The **always-allocate** rule `x ≡ 1` is the simplest monotone allocation; its Myerson payment
is identically `0` (a posted price of `0`), so every type keeps its full surplus and the lowest
type's rent is exactly zero. We use it to exercise the screening API end-to-end. -/

/-- The always-allocate rule `x ≡ 1` on the uniform environment. -/
private def alwaysAlloc : AllocationRule myersonUniform where
  x := fun _ => 1
  nonneg := fun _ => by norm_num
  le_one := fun _ => le_rfl

/-- The always-allocate rule is monotone (it is constant). -/
private theorem alwaysAlloc_monotone : MonotoneAlloc alwaysAlloc :=
  fun _ _ _ _ _ => le_rfl

/-! ### A *nonconstant* monotone allocation: the clipped identity `x(θ) = clamp θ`

To exercise the direction-critical monotonicity, IC, and envelope checks (which a constant
allocation makes trivially-equal), we add the clipped-identity rule `x(θ) = max 0 (min 1 θ)`. On
`[0,1]` this is `θ`, so it is **strictly increasing** there: `x(1/4) = 1/4 < 3/4 = x(3/4)`. Its
Myerson payment is `p(θ) = θ·θ − ∫₀^θ s = θ² − θ²/2 = θ²/2` and interim utility `U(θ) = θ²/2`. -/

/-- The clamp `[0,1]` map. -/
private def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

private lemma clamp01_eq_self {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_right ht.2, max_eq_right ht.1]

/-- The clipped-identity allocation `x(θ) = clamp θ`, **nonconstant** monotone. -/
private def clipAlloc : AllocationRule myersonUniform where
  x := clamp01
  nonneg := fun _ => le_max_left _ _
  le_one := fun _ => by rw [clamp01, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩

/-- The clipped-identity rule is monotone on `[0,1]` (the clamp is monotone). -/
private theorem clipAlloc_monotone : MonotoneAlloc clipAlloc := by
  intro a _ b _ hab
  change clamp01 a ≤ clamp01 b
  exact max_le_max (le_refl 0) (min_le_min (le_refl 1) hab)

/-- `clipAlloc` is BIC via Myerson's monotone-implies-BIC direction. -/
private theorem clipAlloc_isBIC : IsBIC clipAlloc.myersonMechanism :=
  clipAlloc.monotone_implies_isBIC clipAlloc_monotone

/-- The interim utility of `clipAlloc`'s Myerson mechanism is `U(θ) = ∫₀^θ clamp = θ²/2` on
`[0,1]`. At `θ = 1/4`: `1/32`; at `θ = 3/4`: `9/32`. -/
private lemma clipAlloc_interimUtil {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    clipAlloc.myersonMechanism.interimUtil θ = θ ^ 2 / 2 := by
  rw [clipAlloc.interimUtil_myersonMechanism, myersonUniform_θlo]
  rw [show (∫ s in (0 : ℝ)..θ, clipAlloc.x s) = ∫ s in (0 : ℝ)..θ, s from
      intervalIntegral.integral_congr (fun s hs => clamp01_eq_self (by
        rw [Set.uIcc_of_le hθ.1] at hs; exact ⟨hs.1, hs.2.trans hθ.2⟩))]
  rw [integral_id]; ring

/-- **`x_nonneg`** / **`x_le_one`**: Every reported allocation lies in `[0, 1]` — the `[0,1]` bound
baked into the `AllocationRule` type, surfaced on the always-allocate mechanism (`x ≡ 1`). -/
theorem alwaysAlloc_x_mem_unitInterval (θ : ℝ) :
    0 ≤ alwaysAlloc.myersonMechanism.x θ ∧ alwaysAlloc.myersonMechanism.x θ ≤ 1 :=
  ⟨alwaysAlloc.myersonMechanism.x_nonneg θ, alwaysAlloc.myersonMechanism.x_le_one θ⟩

/-- **`MonotoneAlloc.le`** on the **nonconstant** clipped-identity rule: `x(1/4) = 1/4 < 3/4 =
x(3/4)` — a *strict* increase, so an endpoint swap (testing `x(3/4) ≤ x(1/4)`) genuinely fails. (The
constant always-allocate rule made both sides `1`, where the swap would have been invisible.) -/
theorem monotoneAlloc_le_strict_witness :
    clipAlloc.x (1 / 4) < clipAlloc.x (3 / 4) := by
  change clamp01 (1 / 4) < clamp01 (3 / 4)
  rw [clamp01_eq_self (by norm_num), clamp01_eq_self (by norm_num)]; norm_num

/-- The library `MonotoneAlloc.le` (`≤`) on the clipped-identity rule at the same pair. -/
theorem monotoneAlloc_le_witness :
    clipAlloc.x (1 / 4) ≤ clipAlloc.x (3 / 4) :=
  clipAlloc_monotone (by norm_num) (by norm_num) (by norm_num)

/-- **`myersonMechanism_alloc`**: The Myerson mechanism's allocation is the underlying rule. -/
theorem myersonMechanism_alloc_witness :
    alwaysAlloc.myersonMechanism.alloc = alwaysAlloc :=
  alwaysAlloc.myersonMechanism_alloc

/-- **`myersonMechanism_p`**: The Myerson mechanism's payment is the Myerson payment. -/
theorem myersonMechanism_p_witness :
    alwaysAlloc.myersonMechanism.p = alwaysAlloc.myersonPayment :=
  alwaysAlloc.myersonMechanism_p

/-- **`interimUtil_myersonMechanism`**: On-path interim utility under the Myerson payment is the
allocation integral `∫_{θlo}^θ x`. For `x ≡ 1` this is `∫₀^θ 1 = θ` — checked at `θ = 1/2`, giving
`1/2` (the type's full surplus, since the posted price is `0`). -/
theorem interimUtil_myersonMechanism_witness :
    alwaysAlloc.myersonMechanism.interimUtil (1 / 2) = 1 / 2 := by
  rw [alwaysAlloc.interimUtil_myersonMechanism, myersonUniform_θlo]
  simp [alwaysAlloc]

/-- **The lowest type gets ZERO rent** (`interimUtil_myersonMechanism` at `θlo`): The IR-binding
endpoint `U(0) = ∫₀⁰ x = 0`. An `interimUtil θlo ≠ 0` would mean the lowest type captures rent. -/
theorem interimUtil_θlo_eq_zero :
    alwaysAlloc.myersonMechanism.interimUtil myersonUniform.θlo = 0 := by
  rw [alwaysAlloc.interimUtil_myersonMechanism, intervalIntegral.integral_same]

/-- **The Myerson payment is a posted price of `0`** (`payment_eq` on the always-allocate rule):
`p(θ) = θ·1 − ∫₀^θ 1 = θ − θ = 0`. The mechanism gives the good away — a sign error in the rent
term `∫x` would make the payment `2θ` or `−2θ`, not `0`. Checked at `θ = 3/4`. -/
theorem payment_eq_witness :
    alwaysAlloc.myersonMechanism.p (3 / 4) = 0 := by
  rw [alwaysAlloc.myersonMechanism_p, AllocationRule.myersonPayment, myersonUniform_θlo]
  simp only [alwaysAlloc, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-! ## Block 3: Incentive compatibility on the Myerson mechanism

The always-allocate Myerson mechanism is BIC (Myerson's constructive direction). We surface the
direction-critical truth-telling inequality. -/

/-- The always-allocate Myerson mechanism is incentive compatible. -/
private theorem alwaysAlloc_isBIC : IsBIC alwaysAlloc.myersonMechanism :=
  alwaysAlloc.monotone_implies_isBIC alwaysAlloc_monotone

/-- **`reportUtil_self`**: Truthful reporting realizes the on-path interim utility,
`M.reportUtil θ θ = M.interimUtil θ`. Checked at `θ = 1/2`. -/
theorem reportUtil_self_witness :
    alwaysAlloc.myersonMechanism.reportUtil (1 / 2) (1 / 2)
      = alwaysAlloc.myersonMechanism.interimUtil (1 / 2) :=
  alwaysAlloc.myersonMechanism.reportUtil_self (1 / 2)

/-- **`IsBIC.reportUtil_le` — truth-telling weakly dominates** (THE direction-critical site): A
type-`1/2` agent reporting `1/4` gets *no more* than reporting truthfully. A flipped inequality
would make misreporting weakly optimal — a silent IC violation. -/
theorem reportUtil_le_witness :
    alwaysAlloc.myersonMechanism.reportUtil (1 / 2) (1 / 4)
      ≤ alwaysAlloc.myersonMechanism.interimUtil (1 / 2) :=
  alwaysAlloc_isBIC.reportUtil_le (by norm_num) (by norm_num)

/-- The Myerson payment of the clipped-identity rule is `p(θ) = θ²/2` on `[0,1]`. -/
private lemma clipAlloc_payment {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    clipAlloc.myersonMechanism.p θ = θ ^ 2 / 2 := by
  rw [clipAlloc.myersonMechanism_p, AllocationRule.myersonPayment, myersonUniform_θlo]
  rw [show (∫ s in (0 : ℝ)..θ, clipAlloc.x s) = ∫ s in (0 : ℝ)..θ, s from
      intervalIntegral.integral_congr (fun s hs => clamp01_eq_self (by
        rw [Set.uIcc_of_le hθ.1] at hs; exact ⟨hs.1, hs.2.trans hθ.2⟩))]
  rw [integral_id]
  change θ * clamp01 θ - (θ ^ 2 - 0 ^ 2) / 2 = θ ^ 2 / 2
  rw [clamp01_eq_self hθ]; ring

/-- **`IsBIC.reportUtil_le`, with a STRICT loss** on the *nonconstant* clipped-identity rule. A
type-`3/4` agent who misreports `1/4` earns `3/4·x(1/4) − p(1/4) = 3/4·(1/4) − 1/32 = 5/32`,
**strictly below** the truthful utility `U(3/4) = (3/4)²/2 = 9/32`. Misreporting genuinely hurts
(unlike the constant rule, where every report tied at the full surplus), so a flipped inequality
exposing misreporting as optimal is now caught. -/
theorem reportUtil_strict_loss_witness :
    clipAlloc.myersonMechanism.reportUtil (3 / 4) (1 / 4)
      < clipAlloc.myersonMechanism.interimUtil (3 / 4) := by
  rw [DirectMechanism.reportUtil_def, clipAlloc_interimUtil (by norm_num), clipAlloc_payment
    (by norm_num)]
  have hx : clipAlloc.myersonMechanism.x (1 / 4) = 1 / 4 := by
    change clamp01 (1 / 4) = 1 / 4; rw [clamp01_eq_self (by norm_num)]
  rw [hx]; norm_num

/-- The library `IsBIC.reportUtil_le` (`≤`) at the same misreport on `clipAlloc`. -/
theorem reportUtil_le_clipAlloc_witness :
    clipAlloc.myersonMechanism.reportUtil (3 / 4) (1 / 4)
      ≤ clipAlloc.myersonMechanism.interimUtil (3 / 4) :=
  clipAlloc_isBIC.reportUtil_le (by norm_num) (by norm_num)

/-! ## Block 4: Myerson's lemma — implementable ⟺ monotone

Both directions on the concrete always-allocate rule. -/

/-- **`myerson_lemma` (← direction)**: A monotone allocation is implementable — there exists a
payment making it BIC. -/
theorem myerson_lemma_mpr_witness :
    ∃ p : ℝ → ℝ, IsBIC (DirectMechanism.mk alwaysAlloc p) :=
  (myerson_lemma alwaysAlloc).mpr alwaysAlloc_monotone

/-- **`myerson_lemma` (→ direction)**: An implementable allocation is monotone. Fed the witness
from the `mpr` direction, recovering monotonicity. This closes the biconditional non-vacuously. -/
theorem myerson_lemma_mp_witness : MonotoneAlloc alwaysAlloc :=
  (myerson_lemma alwaysAlloc).mp myerson_lemma_mpr_witness

/-- **`sub_mul_le_integral`** — the core incentive inequality `(θ − r)·x(r) ≤ ∫_r^θ x`. For `x ≡ 1`
this is `(θ − r)·1 ≤ θ − r`, an equality. Checked at `r = 1/4`, `θ = 3/4`. -/
theorem sub_mul_le_integral_witness :
    ((3 : ℝ) / 4 - 1 / 4) * alwaysAlloc.x (1 / 4)
      ≤ ∫ s in (1 / 4 : ℝ)..(3 / 4), alwaysAlloc.x s :=
  alwaysAlloc.sub_mul_le_integral alwaysAlloc_monotone (by norm_num) (by norm_num)

/-! ## Block 5: The envelope two-sided bound

`(t − r)·x(r) ≤ U(t) − U(r) ≤ (t − r)·x(t)`, on the BIC always-allocate mechanism. A reversed
bound breaks the monotone comparative statics underlying the revenue identity. -/

/-- **`sub_mul_le_interimUtil_sub`** (lower envelope bound): `(t − r)·x(r) ≤ U(t) − U(r)`. Checked
at `r = 1/4`, `t = 3/4`. -/
theorem sub_mul_le_interimUtil_sub_witness :
    ((3 : ℝ) / 4 - 1 / 4) * alwaysAlloc.myersonMechanism.x (1 / 4)
      ≤ alwaysAlloc.myersonMechanism.interimUtil (3 / 4)
        - alwaysAlloc.myersonMechanism.interimUtil (1 / 4) :=
  alwaysAlloc.myersonMechanism.sub_mul_le_interimUtil_sub alwaysAlloc_isBIC (by norm_num)
    (by norm_num)

/-- **`interimUtil_sub_le_sub_mul`** (upper envelope bound): `U(t) − U(r) ≤ (t − r)·x(t)`. Together
with the previous block this two-sided bound forces the envelope identity. -/
theorem interimUtil_sub_le_sub_mul_witness :
    alwaysAlloc.myersonMechanism.interimUtil (3 / 4)
        - alwaysAlloc.myersonMechanism.interimUtil (1 / 4)
      ≤ ((3 : ℝ) / 4 - 1 / 4) * alwaysAlloc.myersonMechanism.x (3 / 4) :=
  alwaysAlloc.myersonMechanism.interimUtil_sub_le_sub_mul alwaysAlloc_isBIC (by norm_num)
    (by norm_num)

/-- **The envelope two-sided bound, with DISTINCT numeric anchors** on the nonconstant
clipped-identity rule: `1/8 ≤ 1/4 ≤ 3/8`. The lower bound `(t−r)·x(r) = (1/2)·(1/4) = 1/8`, the
utility gap `U(3/4) − U(1/4) = 9/32 − 1/32 = 1/4`, and the upper bound `(t−r)·x(t) = (1/2)·(3/4) =
3/8` are all *different*, so a swap of `x(r)` and `x(t)` flips `1/8 ↔ 3/8` and breaks the sandwich.
(The constant rule collapsed all three to equal values.) -/
theorem envelope_distinct_anchors_witness :
    ((3 : ℝ) / 4 - 1 / 4) * clipAlloc.myersonMechanism.x (1 / 4) = 1 / 8 ∧
    clipAlloc.myersonMechanism.interimUtil (3 / 4)
        - clipAlloc.myersonMechanism.interimUtil (1 / 4) = 1 / 4 ∧
    ((3 : ℝ) / 4 - 1 / 4) * clipAlloc.myersonMechanism.x (3 / 4) = 3 / 8 := by
  have hx14 : clipAlloc.myersonMechanism.x (1 / 4) = 1 / 4 := by
    change clamp01 (1 / 4) = 1 / 4; rw [clamp01_eq_self (by norm_num)]
  have hx34 : clipAlloc.myersonMechanism.x (3 / 4) = 3 / 4 := by
    change clamp01 (3 / 4) = 3 / 4; rw [clamp01_eq_self (by norm_num)]
  refine ⟨by rw [hx14]; norm_num, ?_, by rw [hx34]; norm_num⟩
  rw [clipAlloc_interimUtil (by norm_num), clipAlloc_interimUtil (by norm_num)]; norm_num

/-- The two library envelope bounds on `clipAlloc`, whose values `1/8 ≤ 1/4 ≤ 3/8` are pinned by
`envelope_distinct_anchors_witness`. -/
theorem envelope_two_sided_clipAlloc_witness :
    ((3 : ℝ) / 4 - 1 / 4) * clipAlloc.myersonMechanism.x (1 / 4)
        ≤ clipAlloc.myersonMechanism.interimUtil (3 / 4)
          - clipAlloc.myersonMechanism.interimUtil (1 / 4) ∧
    clipAlloc.myersonMechanism.interimUtil (3 / 4)
        - clipAlloc.myersonMechanism.interimUtil (1 / 4)
      ≤ ((3 : ℝ) / 4 - 1 / 4) * clipAlloc.myersonMechanism.x (3 / 4) :=
  ⟨clipAlloc.myersonMechanism.sub_mul_le_interimUtil_sub clipAlloc_isBIC
      (by norm_num) (by norm_num),
   clipAlloc.myersonMechanism.interimUtil_sub_le_sub_mul clipAlloc_isBIC
      (by norm_num) (by norm_num)⟩

/-! ## Block 6: The revenue identity (virtual value minus rent)

`payment_eq_sub_rent` decomposes the payment as `θ·x(θ) − U(θlo) − ∫x`, with the correct
virtual-value-minus-rent sign. On `alwaysAlloc` this evaluates to `0` (posted price). -/

/-- **`payment_eq_sub_rent`** — revenue = virtual value minus rent (correct sign):
`p(θ) = θ·x(θ) − U(θlo) − ∫_{θlo}^θ x`. Surfaced on `alwaysAlloc` at `θ = 3/4`, where `U(θlo) = 0`
and `∫₀^{3/4} 1 = 3/4`, so `p(3/4) = 3/4·1 − 0 − 3/4 = 0`. A wrong sign on either subtracted term
would break the identity. -/
theorem payment_eq_sub_rent_witness :
    alwaysAlloc.myersonMechanism.p (3 / 4)
      = (3 / 4) * alwaysAlloc.myersonMechanism.x (3 / 4)
        - alwaysAlloc.myersonMechanism.interimUtil myersonUniform.θlo
        - ∫ s in (myersonUniform.θlo)..(3 / 4), alwaysAlloc.myersonMechanism.x s :=
  alwaysAlloc.myersonMechanism.payment_eq_sub_rent alwaysAlloc_isBIC (by norm_num)

/-- **`payment_eq`** (normalized, `U(θlo) = 0`): `p(θ) = θ·x(θ) − ∫_{θlo}^θ x`. The always-allocate
Myerson mechanism is exactly zero-rent-normalized, so this fires. -/
theorem payment_eq_witness' :
    alwaysAlloc.myersonMechanism.p (3 / 4)
      = (3 / 4) * alwaysAlloc.myersonMechanism.x (3 / 4)
        - ∫ s in (myersonUniform.θlo)..(3 / 4), alwaysAlloc.myersonMechanism.x s :=
  alwaysAlloc.myersonMechanism.payment_eq alwaysAlloc_isBIC interimUtil_θlo_eq_zero (by norm_num)

/-! ### A BIC mechanism with NONZERO lowest-type rent

The Myerson mechanism always normalizes `U(θlo) = 0`, so the rent term in `payment_eq_sub_rent` is
numerically silent. We build `subsidyMech` = the clipped-identity Myerson mechanism **minus a
constant subsidy `1/8`**: `p'(θ) = p_M(θ) − 1/8`. Adding a constant to every utility preserves IC,
so it is BIC; and now `U'(θlo) = U_M(θlo) + 1/8 = 1/8 ≠ 0`, so the lowest-type rent term in the
payment identity is *active*. -/

/-- The subsidized mechanism: clipped-identity allocation, Myerson payment minus the constant
subsidy `1/8`. -/
private def subsidyMech : DirectMechanism myersonUniform where
  alloc := clipAlloc
  p := fun θ => clipAlloc.myersonMechanism.p θ - 1 / 8

/-- The subsidy shifts every interim/report utility by `+1/8`, preserving IC. -/
private theorem subsidyMech_isBIC : IsBIC subsidyMech := by
  intro θ hθ r hr
  have hbic := clipAlloc_isBIC θ hθ r hr
  rw [DirectMechanism.reportUtil_def, DirectMechanism.interimUtil_def] at hbic ⊢
  -- `subsidyMech.x = clipAlloc.myersonMechanism.x`, `subsidyMech.p = p_M - 1/8`.
  change θ * clipAlloc.myersonMechanism.x r - (clipAlloc.myersonMechanism.p r - 1 / 8)
    ≤ θ * clipAlloc.myersonMechanism.x θ - (clipAlloc.myersonMechanism.p θ - 1 / 8)
  linarith [hbic]

/-- **The lowest type captures NONZERO rent**: `U'(θlo) = U'(0) = 0·x(0) − (p_M(0) − 1/8) = 1/8`. -/
theorem subsidyMech_nonzero_rent : subsidyMech.interimUtil myersonUniform.θlo = 1 / 8 := by
  rw [DirectMechanism.interimUtil_def, myersonUniform_θlo]
  change (0 : ℝ) * subsidyMech.x 0 - (clipAlloc.myersonMechanism.p 0 - 1 / 8) = 1 / 8
  rw [clipAlloc_payment (by norm_num)]; norm_num

/-- **`payment_eq_sub_rent` with the NONZERO-rent term active**: on `subsidyMech` at `θ = 3/4`,
`p'(3/4) = 3/4·x(3/4) − U'(θlo) − ∫₀^{3/4} x` with `U'(θlo) = 1/8 ≠ 0`. The rent subtraction is now
numerically load-bearing — a wrong sign on it would change `p'(3/4)` by `±1/4` (twice the rent). The
constant always-allocate / zero-rent mechanisms could not exercise this term. -/
theorem payment_eq_sub_rent_nonzero_rent_witness :
    subsidyMech.p (3 / 4)
      = (3 / 4) * subsidyMech.x (3 / 4)
        - subsidyMech.interimUtil myersonUniform.θlo
        - ∫ s in (myersonUniform.θlo)..(3 / 4), subsidyMech.x s :=
  subsidyMech.payment_eq_sub_rent subsidyMech_isBIC (by norm_num)

/-- **`myersonMechanism_isBIR`** (screening layer) — the Myerson mechanism is individually rational:
Interim utility `≥ 0` for every type. An `interimUtil < 0` would mean a type prefers the outside
option. -/
theorem myersonMechanism_isBIR_witness : IsBIR alwaysAlloc.myersonMechanism :=
  alwaysAlloc.myersonMechanism_isBIR

/-! ## Block 7: The auction layer — optimal-revenue attainment and BIR

The `n`-bidder uniform auction `myersonAuction` (regular) and its optimal mechanism
`myersonOptimalAuction`. We surface the BIR direction and the optimal-revenue *attainment* /
*upper-bound* lemmas not already consumed by `MyersonReserveUniform`. -/

/-- The reduced allocation of the optimal mechanism is monotone (regularity makes the highest-`ψ`
rule implementable). -/
private theorem optimalAlloc_reducedAlloc_monotone (i : Fin (myersonAuction 2 (by norm_num)).n) :
    MonotoneAlloc ((myersonAuction 2 (by norm_num)).optimalAlloc.reducedAlloc i) :=
  myersonAuction_optimalAlloc_monotone 2 (by norm_num) i

/-- **`myersonMechanism_BIR`** (auction layer) — Myerson's optimal auction is individually
rational: Every reduced mechanism's interim utility is `≥ 0` (`IsBIR`, NOT `< 0`). The zero-rent
normalization at `θlo` plus a nonnegative allocation forces it. -/
theorem auction_myersonMechanism_BIR : (myersonOptimalAuction 2 (by norm_num)).IsBIR :=
  (myersonAuction 2 (by norm_num)).optimalAlloc.myersonMechanism_BIR

/-- **`myersonMechanism_isBIC`** (auction layer) — Myerson's optimal auction is incentive compatible
(truthful bidding is a best response). -/
theorem auction_myersonMechanism_isBIC : (myersonOptimalAuction 2 (by norm_num)).IsBIC :=
  myersonOptimalAuction_isBIC 2 (by norm_num)

/-- **`highestValueAlloc_interimAlloc`** — the efficient allocation's interim form is the top order
statistic `F(t)^(n-1)`, **anchored to the closed numeric value `1/2`** for the uniform `2`-bidder
auction at `t = 1/2`: `F(1/2)^(2−1) = (1/2)^1 = 1/2`. (The previous witness left the RHS as the
symbolic `cdf(1/2)^(n−1)`; we now discharge the uniform CDF and the `n = 2` exponent reduction.) -/
theorem highestValueAlloc_interimAlloc_witness (i : Fin (myersonAuction 2 (by norm_num)).n) :
    (myersonAuction 2 (by norm_num)).highestValueAlloc.interimAlloc i (1 / 2) = 1 / 2 := by
  rw [(myersonAuction 2 (by norm_num)).highestValueAlloc_interimAlloc i (1 / 2),
    myersonAuction_base, myersonAuction_n,
    EconlibExamples.MechanismDesign.MyersonReserveUniform.myersonUniform_cdf (by norm_num)]
  norm_num

/-- **`exists_optimal_auction_regular`** — under regularity there exists a BIC, BIR, zero-rent
auction whose expected revenue *equals* the optimal virtual surplus bound `∫ max(0, maxᵢ ψ(θᵢ))`.
Discharged from the uniform environment's actual regularity instance, so the achievability
construction runs on real data. This *attains* the bound; the `≤` for all admissible auctions is
`revenue_le_ironedOptimalVirtualSurplus`. -/
theorem exists_optimal_auction_regular_witness :
    ∃ M : AuctionMechanism (myersonAuction 2 (by norm_num)),
      M.IsBIC ∧ M.IsBIR ∧
      (∀ i, (M.reducedMechanism i).interimUtil (myersonAuction 2 (by norm_num)).base.θlo = 0) ∧
      (∫ θ, ∑ i, M.pay θ i ∂(myersonAuction 2 (by norm_num)).jointLaw)
        = ∫ θ, (myersonAuction 2 (by norm_num)).optimalVirtualSurplus θ
          ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  (myersonAuction 2 (by norm_num)).exists_optimal_auction_regular myersonUniform_regular

/-- **`exists_optimal_auction_ironed`** — *without any regularity assumption* there exists a BIC,
BIR, zero-rent auction whose expected revenue equals the *ironed* optimal virtual surplus bound
`∫ max(0, maxᵢ ψ̄(θᵢ))`. On the (regular) uniform environment `ψ̄ = ψ`, so this coincides with the
regular bound — the general-case construction, exercised on real data. -/
theorem exists_optimal_auction_ironed_witness :
    ∃ M : AuctionMechanism (myersonAuction 2 (by norm_num)),
      M.IsBIC ∧ M.IsBIR ∧
      (∀ i, (M.reducedMechanism i).interimUtil (myersonAuction 2 (by norm_num)).base.θlo = 0) ∧
      (∫ θ, ∑ i, M.pay θ i ∂(myersonAuction 2 (by norm_num)).jointLaw)
        = ∫ θ, (myersonAuction 2 (by norm_num)).ironedOptimalVirtualSurplus θ
          ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  (myersonAuction 2 (by norm_num)).exists_optimal_auction_ironed

/-- **`revenue_le_ironedOptimalVirtualSurplus`** (the `≤` direction, **universally quantified**) —
*every* BIC, BIR auction `M` over the uniform `2`-bidder environment has expected revenue *at most*
the ironed optimal virtual surplus. This is the genuine upper-bound direction over arbitrary
admissible auctions (the previous witness instantiated it only on `myersonOptimalAuction`, which
also *attains* the bound, so an attainment-only statement could not distinguish "upper bound for
all" from "value at the optimum"). A `≥` reversal would falsely claim the bound is a *lower* bound
for every auction. -/
theorem revenue_le_ironedOptimalVirtualSurplus_witness
    (M : AuctionMechanism (myersonAuction 2 (by norm_num))) (hbic : M.IsBIC) (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂(myersonAuction 2 (by norm_num)).jointLaw)
      ≤ ∫ θ, (myersonAuction 2 (by norm_num)).ironedOptimalVirtualSurplus θ
        ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  M.revenue_le_ironedOptimalVirtualSurplus hbic hbir

/-- The optimal mechanism, being BIC ∧ BIR, is one such admissible auction the universal bound
applies to (it also *attains* the bound — `exists_optimal_auction_ironed_witness`). -/
theorem revenue_le_ironedOptimalVirtualSurplus_optimal :
    (∫ θ, ∑ i, (myersonOptimalAuction 2 (by norm_num)).pay θ i
        ∂(myersonAuction 2 (by norm_num)).jointLaw)
      ≤ ∫ θ, (myersonAuction 2 (by norm_num)).ironedOptimalVirtualSurplus θ
        ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  revenue_le_ironedOptimalVirtualSurplus_witness (myersonOptimalAuction 2 (by norm_num))
    auction_myersonMechanism_isBIC auction_myersonMechanism_BIR

/-- **`myersonMechanism_revenue`** — the optimal mechanism's expected revenue equals the sum over
bidders of expected virtual surplus `∑ᵢ 𝔼[ψ(t)·x̄ᵢ(t)]`. The headline revenue identity at the
auction layer. -/
theorem auction_myersonMechanism_revenue_witness :
    (∫ θ, ∑ i, (myersonOptimalAuction 2 (by norm_num)).pay θ i
        ∂(myersonAuction 2 (by norm_num)).jointLaw)
      = ∑ i, (myersonAuction 2 (by norm_num)).base.dist.expect
        (fun t => (myersonAuction 2 (by norm_num)).base.virtualValue t
          * (myersonAuction 2 (by norm_num)).optimalAlloc.interimAlloc i t) :=
  (myersonAuction 2 (by norm_num)).optimalAlloc.myersonMechanism_revenue
    optimalAlloc_reducedAlloc_monotone

/-- **`sum_expect_virtualSurplus_eq`** — the per-bidder expected virtual surplus over the type law
equals the joint-profile virtual surplus `∫ ∑ᵢ ψ(θᵢ)·xᵢ(θ)`. The interim-to-ex-post bridge for the
raw virtual value. -/
theorem sum_expect_virtualSurplus_eq_witness :
    (∑ i, (myersonAuction 2 (by norm_num)).base.dist.expect
        (fun t => (myersonAuction 2 (by norm_num)).base.virtualValue t
          * (myersonAuction 2 (by norm_num)).optimalAlloc.interimAlloc i t))
      = ∫ θ, ∑ i, (myersonAuction 2 (by norm_num)).base.virtualValue (θ i)
        * (myersonAuction 2 (by norm_num)).optimalAlloc.x θ i
        ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  (myersonAuction 2 (by norm_num)).optimalAlloc.sum_expect_virtualSurplus_eq

/-- **`sum_expect_ironedVirtualSurplus_eq`** — the same interim-to-ex-post bridge for the *ironed*
virtual value `ψ̄`. On the regular uniform environment `ψ̄ = ψ`, so it coincides with the raw
bridge; the lemma itself holds unconditionally. -/
theorem sum_expect_ironedVirtualSurplus_eq_witness :
    (∑ i, (myersonAuction 2 (by norm_num)).base.dist.expect
        (fun t => (myersonAuction 2 (by norm_num)).base.ironedVirtualValue t
          * (myersonAuction 2 (by norm_num)).ironedAlloc.interimAlloc i t))
      = ∫ θ, ∑ i, (myersonAuction 2 (by norm_num)).base.ironedVirtualValue (θ i)
        * (myersonAuction 2 (by norm_num)).ironedAlloc.x θ i
        ∂(myersonAuction 2 (by norm_num)).jointLaw :=
  (myersonAuction 2 (by norm_num)).ironedAlloc.sum_expect_ironedVirtualSurplus_eq

/-- **`expected_rawSurplus_eq_ironedSurplus_ironedAlloc`** — complementary slackness: For the
highest-ironed-value allocation the raw and ironed expected virtual surpluses coincide per bidder.

**Scope (regular-degeneration smoke test).** On the *regular* uniform environment `ψ̄ = ψ`
pointwise, so this equality is trivially the pointwise one rather than a genuine contact-set /
complementary-slackness argument with a nonzero ironing gap. The concrete *irregular* environment
with a real ironing gap (where this equality is the nontrivial contact-set identity) is the worked
example `EconlibExamples.MechanismDesign.MyersonIroning` (see
`expected_rawSurplus_eq_ironedSurplus_ironedAlloc_witness` there). -/
theorem expected_rawSurplus_eq_ironedSurplus_ironedAlloc_witness
    (i : Fin (myersonAuction 2 (by norm_num)).n) :
    ((myersonAuction 2 (by norm_num)).base.dist.expect
        (fun t => (myersonAuction 2 (by norm_num)).base.virtualValue t
          * (myersonAuction 2 (by norm_num)).ironedAlloc.interimAlloc i t))
      = (myersonAuction 2 (by norm_num)).base.dist.expect
        (fun t => (myersonAuction 2 (by norm_num)).base.ironedVirtualValue t
          * (myersonAuction 2 (by norm_num)).ironedAlloc.interimAlloc i t) :=
  (myersonAuction 2 (by norm_num)).expected_rawSurplus_eq_ironedSurplus_ironedAlloc i

/-! ## Block 8: The ironing machinery (regular-case degeneration)

On the *regular* uniform environment the ironed virtual value equals the raw one (`ψ̄ = ψ`,
`myersonUniform_ironedVVQuantile = 2t − 1`), the quantile primitive `H(q) = q² − q` is convex, and
the ironing gap vanishes — the degenerate (idle) case of the ironing API. We exercise the lemmas
whose hypotheses are dischargeable on this regular instance: `ironedPrimitive_convexOn` (the
engine), `ironedVVQuantile_monotone`, `allocQuantile_monotoneOn`, and the cumulative-gap identity
`integral_ironedVVQuantile_sub_vvQuantile` (gap `= 0` here).

`ironedVVQuantile_eq_of_affineOn` (the ironed value is *flat* on any interval where the envelope is
affine) cannot be witnessed *faithfully* on the uniform instance: `H(q) = q² − q` is strictly
convex, hence affine on *no* nondegenerate subinterval, so the `haffine` hypothesis is
dischargeable only on a degenerate (empty) interval, which is not an informative witness. It *is*
exercised faithfully on the irregular worked example
`EconlibExamples.MechanismDesign.MyersonIroning`
(`irr_ironedVVQuantile_eq_ironed`: `ψ̄_q = −9/8` flat on the bunched region `(0, 1/4)`). Here only
its load-bearing input, `ironedPrimitive_convexOn`, is exercised below. -/

/-- **`ironedPrimitive_convexOn`** — the quantile-space ironed primitive is convex on `[0, 1]`. For
the uniform environment it is `H(q) = q² − q`, already convex. This is the engine of the whole
ironing layer (the convex envelope is `H` itself when `H` is convex). -/
theorem ironedPrimitive_convexOn_witness :
    ConvexOn ℝ (Icc (0 : ℝ) 1) myersonUniform.ironedPrimitive :=
  myersonUniform.ironedPrimitive_convexOn

/-- **`ironedVVQuantile_monotone`** — the ironed quantile-space virtual value is *monotone*
(unconditionally — that is the point of ironing). On the uniform environment it equals `2t − 1`. -/
theorem ironedVVQuantile_monotone_witness : Monotone myersonUniform.ironedVVQuantile :=
  myersonUniform.ironedVVQuantile_monotone

/-- **The ironed value equals the raw virtual value** (the regular-case degeneration): On the
uniform environment `ψ̄_q(t) = 2t − 1 = ψ_q(t)` throughout `[0, 1]`, so ironing is idle. Checked at
**three points** `1/4, 1/2, 3/4` with *distinct nonzero* slope-`(2q − 1)` values `−1/2, 0, 1/2` —
so the test exercises the slope `2q − 1`, not just the reserve crossing at `1/2` where both happen
to vanish. This is the *informative* substitute for `ironedVVQuantile_eq_of_affineOn`, which is not
faithfully witnessable here (see the block note). -/
theorem ironedVVQuantile_eq_vvQuantile_at_points :
    (myersonUniform.ironedVVQuantile (1 / 4) = myersonUniform.vvQuantile (1 / 4)
        ∧ myersonUniform.vvQuantile (1 / 4) = -(1 / 2)) ∧
    (myersonUniform.ironedVVQuantile (1 / 2) = myersonUniform.vvQuantile (1 / 2)
        ∧ myersonUniform.vvQuantile (1 / 2) = 0) ∧
    (myersonUniform.ironedVVQuantile (3 / 4) = myersonUniform.vvQuantile (3 / 4)
        ∧ myersonUniform.vvQuantile (3 / 4) = 1 / 2) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [myersonUniform_ironedVVQuantile (by norm_num), myersonUniform_vvQuantile (by norm_num)]
  · rw [myersonUniform_vvQuantile (by norm_num)]; norm_num
  · rw [myersonUniform_ironedVVQuantile (by norm_num), myersonUniform_vvQuantile (by norm_num)]
  · rw [myersonUniform_vvQuantile (by norm_num)]; norm_num
  · rw [myersonUniform_ironedVVQuantile (by norm_num), myersonUniform_vvQuantile (by norm_num)]
  · rw [myersonUniform_vvQuantile (by norm_num)]; norm_num

/-- **`allocQuantile_monotoneOn`** — the allocation pulled back to quantile space is monotone on
`(0, 1)`. Surfaced on the **nonconstant** clipped-identity mechanism: a reversed or malformed
quantile transport would have to *un-order* a genuinely increasing rule, so the monotonicity is
load-bearing (the constant always-allocate rule would pass even with a broken transport, since a
constant function is monotone under any reordering). -/
theorem allocQuantile_monotoneOn_witness :
    MonotoneOn (fun t => clipAlloc.myersonMechanism.x (myersonUniform.quantileInv t)) (Ioo 0 1) :=
  myersonUniform.allocQuantile_monotoneOn clipAlloc.myersonMechanism clipAlloc_monotone

/-- **`integral_ironedVVQuantile_sub_vvQuantile`** — the cumulative ironing gap equals the
primitive gap, `∫₀^s (ψ̄_q − ψ_q) = Ĥ(s) − H(s)`.

**Scope (regular-degeneration smoke test).** On the regular uniform environment `ψ̄_q = ψ_q` and
`Ĥ = H`, so *both* sides of this identity are identically `0` here — a sign/order mistake in the gap
would be invisible on this instance. The identity itself holds unconditionally; the non-regular
instance with a *nonzero* cumulative gap is the worked example
`EconlibExamples.MechanismDesign.MyersonIroning`
(`integral_ironedVVQuantile_sub_vvQuantile_nonzero`: `∫₀^{1/8} (ψ̄_q − ψ_q) = −1/256 ≠ 0`). Checked
at `s = 1/2`. -/
theorem integral_ironedVVQuantile_sub_vvQuantile_witness :
    (∫ t in (0 : ℝ)..(1 / 2), myersonUniform.ironedVVQuantile t - myersonUniform.vvQuantile t)
      = myersonUniform.ironedPrimitive (1 / 2) - myersonUniform.vvPrimitive (1 / 2) :=
  myersonUniform.integral_ironedVVQuantile_sub_vvQuantile (by norm_num)

end EconlibTest.MechanismDesign.TransfersScreening

end
