import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.MyersonLemma
import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity

/-!
# Single-parameter payment identity with a reserve

This file formalizes Proposition `prop:payment_identity` and Corollary `cor:ir`
from *Smoothing the Cliff*, after fixing one bidder and the opponents' bids.
Econlib's screening interface uses a compact interval of types and normalizes
allocation to `[0, 1]`; the distribution bundled into `ScreeningEnv` plays no
role in the statements below.  The paper's lower endpoint `0` is imposed
explicitly where its displayed formula is recovered.
-/

open Set MeasureTheory
open scoped Interval

namespace SmoothingCliff.Payments

open Econlib.MechanismDesign.Transfers.SingleParameter

noncomputable section

/-- A payment schedule obeys the envelope payment identity up to one constant.
After fixing opponents' bids, the paper's `C_i(b_{-i})` is exactly this `C`. -/
def PaymentIdentity {E : ScreeningEnv} (X : AllocationRule E) (p : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ θ ∈ E.types,
    p θ = θ * X.x θ - (∫ s in E.θlo..θ, X.x s) + C

/-- For a fixed monotone interim allocation, truthfulness in expectation is
equivalent to the payment identity, including both directions and the free
constant. -/
theorem isBIC_iff_paymentIdentity {E : ScreeningEnv} (X : AllocationRule E)
    (hmono : MonotoneAlloc X) (p : ℝ → ℝ) :
    IsBIC (DirectMechanism.mk X p) ↔ PaymentIdentity X p := by
  let M : DirectMechanism E := DirectMechanism.mk X p
  constructor
  · intro hbic
    refine ⟨-M.interimUtil E.θlo, ?_⟩
    intro θ hθ
    have hpay := M.payment_eq_sub_rent hbic hθ
    change p θ = θ * X.x θ - (∫ s in E.θlo..θ, X.x s) + -M.interimUtil E.θlo
    change p θ = θ * X.x θ - M.interimUtil E.θlo -
      ∫ s in E.θlo..θ, X.x s at hpay
    linarith
  · rintro ⟨C, hpay⟩
    have hbase : IsBIC X.myersonMechanism := X.monotone_implies_isBIC hmono
    intro θ hθ r hr
    have h := hbase θ hθ r hr
    have hpayθ := hpay θ hθ
    have hpayr := hpay r hr
    simp only [DirectMechanism.reportUtil_def, DirectMechanism.interimUtil_def,
      DirectMechanism.x_def, AllocationRule.myersonMechanism_alloc,
      AllocationRule.myersonMechanism_p, AllocationRule.myersonPayment] at h ⊢
    linarith

/-- The preceding characterization in the paper's zero-based notation. -/
theorem isBIC_iff_zeroBasedPaymentIdentity {E : ScreeningEnv} (X : AllocationRule E)
    (hmono : MonotoneAlloc X) (p : ℝ → ℝ) (hlo : E.θlo = 0) :
    IsBIC (DirectMechanism.mk X p) ↔
      ∃ C : ℝ, ∀ θ ∈ E.types,
        p θ = θ * X.x θ - (∫ s in (0 : ℝ)..θ, X.x s) + C := by
  simpa [PaymentIdentity, hlo] using isBIC_iff_paymentIdentity X hmono p

/-- Screening at the reserve: allocation is zero for every type strictly below
the weak eligibility threshold.  Allocation at the boundary may be positive. -/
def ScreensAtReserve {E : ScreeningEnv} (X : AllocationRule E) (reserve : ℝ) : Prop :=
  reserve ∈ E.types ∧ ∀ θ ∈ E.types, θ < reserve → X.x θ = 0

/-- The reserve-normalized piecewise payment displayed in the paper. -/
def reservePayment {E : ScreeningEnv} (X : AllocationRule E) (reserve θ : ℝ) : ℝ :=
  if θ < reserve then 0
  else θ * X.x θ - ∫ s in reserve..θ, X.x s

/-- A screened allocation has zero integral between the lowest type and the
reserve.  The possibly positive boundary allocation is harmless because a
singleton has Lebesgue measure zero. -/
lemma integral_to_reserve_eq_zero {E : ScreeningEnv} (X : AllocationRule E)
    {reserve : ℝ} (hscreen : ScreensAtReserve X reserve) :
    (∫ s in E.θlo..reserve, X.x s) = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [Measure.ae_ne volume reserve] with s hne hs
  rw [Set.uIoc_of_le hscreen.1.1] at hs
  apply hscreen.2 s ⟨hs.1.le, le_trans hs.2 hscreen.1.2⟩
  exact lt_of_le_of_ne hs.2 hne

/-- The normalized Myerson payment is exactly the paper's piecewise reserve
formula on the type interval. -/
theorem myersonPayment_eq_reservePayment {E : ScreeningEnv} (X : AllocationRule E)
    (hmono : MonotoneAlloc X) {reserve : ℝ} (hscreen : ScreensAtReserve X reserve)
    {θ : ℝ} (hθ : θ ∈ E.types) :
    X.myersonPayment θ = reservePayment X reserve θ := by
  by_cases hbelow : θ < reserve
  · rw [reservePayment, if_pos hbelow, AllocationRule.myersonPayment]
    have hxθ : X.x θ = 0 := hscreen.2 θ hθ hbelow
    have hint : (∫ s in E.θlo..θ, X.x s) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hθ.1] at hs
      exact hscreen.2 s ⟨hs.1.le, le_trans hs.2 hθ.2⟩ (lt_of_le_of_lt hs.2 hbelow)
    rw [hxθ, hint]
    ring
  · rw [reservePayment, if_neg hbelow, AllocationRule.myersonPayment]
    have hrθ : reserve ≤ θ := le_of_not_gt hbelow
    have hleft : IntervalIntegrable X.x volume E.θlo reserve :=
      X.intervalIntegrable_x hmono E.θlo_mem_types hscreen.1
    have hright : IntervalIntegrable X.x volume reserve θ :=
      X.intervalIntegrable_x hmono hscreen.1 hθ
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [integral_to_reserve_eq_zero X hscreen, zero_add] at hadd
    rw [← hadd]

/-- The reserve payment implements the monotone allocation in truthfulness in
expectation.  This is the constructive half of the paper's proposition. -/
theorem reservePayment_isBIC {E : ScreeningEnv} (X : AllocationRule E)
    (hmono : MonotoneAlloc X) {reserve : ℝ} (hscreen : ScreensAtReserve X reserve) :
    IsBIC (DirectMechanism.mk X (reservePayment X reserve)) := by
  rw [isBIC_iff_paymentIdentity X hmono]
  refine ⟨0, ?_⟩
  intro θ hθ
  rw [← myersonPayment_eq_reservePayment X hmono hscreen hθ]
  simp [AllocationRule.myersonPayment]

/-- Under weak eligibility, payment at the reserve is generally
`reserve * x(reserve)`, not zero. -/
theorem reservePayment_at_boundary {E : ScreeningEnv} (X : AllocationRule E)
    (reserve : ℝ) :
    reservePayment X reserve reserve = reserve * X.x reserve := by
  simp [reservePayment]

/-- Truthful utility under the reserve-normalized payment is zero below the
reserve and the allocation integral above it. -/
theorem truthfulUtility_reservePayment {E : ScreeningEnv} (X : AllocationRule E)
    {reserve : ℝ} (hscreen : ScreensAtReserve X reserve) {θ : ℝ}
    (hθ : θ ∈ E.types) :
    (DirectMechanism.mk X (reservePayment X reserve)).interimUtil θ =
      if θ < reserve then 0 else ∫ s in reserve..θ, X.x s := by
  by_cases hbelow : θ < reserve
  · rw [if_pos hbelow]
    simp [DirectMechanism.interimUtil_def, reservePayment, hbelow,
      hscreen.2 θ hθ hbelow]
  · rw [if_neg hbelow]
    simp only [DirectMechanism.interimUtil_def, DirectMechanism.x_def,
      reservePayment, hbelow, ↓reduceIte]
    ring

/-- Corollary `cor:ir`: truthful interim utility is nonnegative, with the exact
zero/integral formula from the paper. -/
theorem reservePayment_interimIR {E : ScreeningEnv} (X : AllocationRule E)
    {reserve : ℝ} (hscreen : ScreensAtReserve X reserve) :
    IsBIR (DirectMechanism.mk X (reservePayment X reserve)) := by
  intro θ hθ
  rw [truthfulUtility_reservePayment X hscreen hθ]
  split_ifs with hbelow
  · exact le_rfl
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_gt hbelow) X.nonneg

/-! ## Arbitrary priority-weight scale

Econlib normalizes allocation to `[0, 1]`.  The paper instead measures priority
in units of the top slot weight `w₁`, so its interim allocation lies in
`[0, w₁]`.  The following interface scales both allocation and utility while
leaving the Econlib allocation rule as the canonical normalized object.  It
also treats the degenerate scale `w₁ = 0` explicitly rather than dividing by
zero.
-/

/-- The paper-scale allocation obtained from Econlib's unit-normalized rule. -/
def scaledAllocation {E : ScreeningEnv} (scale : ℝ) (X : AllocationRule E)
    (θ : ℝ) : ℝ :=
  scale * X.x θ

/-- For a nonnegative scale, the scaled allocation has exactly the paper's
range `[0, scale]`. -/
theorem scaledAllocation_mem_Icc {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (hscale : 0 ≤ scale) (θ : ℝ) :
    scaledAllocation scale X θ ∈ Set.Icc 0 scale := by
  constructor
  · exact mul_nonneg hscale (X.nonneg θ)
  · simpa [scaledAllocation] using mul_le_mul_of_nonneg_left (X.le_one θ) hscale

/-- BIC written directly in paper-scale units.  Unlike `DirectMechanism`, this
definition does not require the scaled allocation itself to be at most one. -/
def ScaledIsBIC {E : ScreeningEnv} (scale : ℝ) (X : AllocationRule E)
    (p : ℝ → ℝ) : Prop :=
  ∀ θ ∈ E.types, ∀ report ∈ E.types,
    θ * scaledAllocation scale X report - p report ≤
      θ * scaledAllocation scale X θ - p θ

/-- Interim IR written directly in paper-scale units. -/
def ScaledIsBIR {E : ScreeningEnv} (scale : ℝ) (X : AllocationRule E)
    (p : ℝ → ℝ) : Prop :=
  ∀ θ ∈ E.types, 0 ≤ θ * scaledAllocation scale X θ - p θ

/-- The envelope payment identity for a priority scale that need not equal
one. -/
def ScaledPaymentIdentity {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (p : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ θ ∈ E.types,
    p θ = θ * scaledAllocation scale X θ -
      (∫ s in E.θlo..θ, scaledAllocation scale X s) + C

/-- At a positive scale, paper-scale BIC is precisely Econlib BIC after
dividing payments by the scale. -/
theorem scaledIsBIC_iff_normalized {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (p : ℝ → ℝ) (hscale : 0 < scale) :
    ScaledIsBIC scale X p ↔
      IsBIC (DirectMechanism.mk X (fun θ ↦ p θ / scale)) := by
  have hsne : scale ≠ 0 := ne_of_gt hscale
  constructor
  · intro h θ hθ report hreport
    have hs := h θ hθ report hreport
    simp only [scaledAllocation] at hs
    simp only [DirectMechanism.reportUtil_def, DirectMechanism.interimUtil_def,
      DirectMechanism.x_def]
    apply (mul_le_mul_iff_of_pos_left hscale).mp
    calc
      scale * (θ * X.x report - p report / scale) =
          θ * (scale * X.x report) - p report := by field_simp
      _ ≤ θ * (scale * X.x θ) - p θ := hs
      _ = scale * (θ * X.x θ - p θ / scale) := by field_simp
  · intro h θ hθ report hreport
    have hn := h θ hθ report hreport
    simp only [DirectMechanism.reportUtil_def, DirectMechanism.interimUtil_def,
      DirectMechanism.x_def] at hn
    have hm := (mul_le_mul_iff_of_pos_left hscale).2 hn
    simp only [scaledAllocation]
    calc
      θ * (scale * X.x report) - p report =
          scale * (θ * X.x report - p report / scale) := by field_simp
      _ ≤ scale * (θ * X.x θ - p θ / scale) := hm
      _ = θ * (scale * X.x θ) - p θ := by field_simp

/-- Scaling the payment identity is equivalent to scaling allocation and
payment together. -/
theorem paymentIdentity_normalized_iff_scaled {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (p : ℝ → ℝ) (hscale : 0 < scale) :
    PaymentIdentity X (fun θ ↦ p θ / scale) ↔
      ScaledPaymentIdentity scale X p := by
  have hsne : scale ≠ 0 := ne_of_gt hscale
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨scale * C, ?_⟩
    intro θ hθ
    have h := hC θ hθ
    change p θ / scale =
      θ * X.x θ - (∫ s in E.θlo..θ, X.x s) + C at h
    simp only [scaledAllocation, intervalIntegral.integral_const_mul]
    calc
      p θ = scale * (p θ / scale) := by field_simp
      _ = scale * (θ * X.x θ - (∫ s in E.θlo..θ, X.x s) + C) := by rw [h]
      _ = θ * (scale * X.x θ) -
          scale * (∫ s in E.θlo..θ, X.x s) + scale * C := by ring
  · rintro ⟨C, hC⟩
    refine ⟨C / scale, ?_⟩
    intro θ hθ
    have h := hC θ hθ
    simp only [scaledAllocation, intervalIntegral.integral_const_mul] at h
    change p θ / scale =
      θ * X.x θ - (∫ s in E.θlo..θ, X.x s) + C / scale
    rw [h]
    field_simp

/-- At zero priority scale, BIC says exactly that payment is constant on the
type interval. -/
theorem scaledIsBIC_zero_iff_constant {E : ScreeningEnv}
    (X : AllocationRule E) (p : ℝ → ℝ) :
    ScaledIsBIC 0 X p ↔ ∃ C : ℝ, ∀ θ ∈ E.types, p θ = C := by
  constructor
  · intro h
    refine ⟨p E.θlo, ?_⟩
    intro θ hθ
    have h₁ := h θ hθ E.θlo E.θlo_mem_types
    have h₂ := h E.θlo E.θlo_mem_types θ hθ
    simp [scaledAllocation] at h₁ h₂
    linarith
  · rintro ⟨C, hC⟩
    intro θ hθ report hreport
    rw [hC θ hθ, hC report hreport]
    simp [scaledAllocation]

/-- At zero priority scale, the payment identity has the same constant-payment
content as BIC. -/
theorem scaledPaymentIdentity_zero_iff_constant {E : ScreeningEnv}
    (X : AllocationRule E) (p : ℝ → ℝ) :
    ScaledPaymentIdentity 0 X p ↔
      ∃ C : ℝ, ∀ θ ∈ E.types, p θ = C := by
  simp [ScaledPaymentIdentity, scaledAllocation]

/-- Proposition `prop:payment_identity` at an arbitrary nonnegative priority
scale, including the degenerate case `scale = 0`. -/
theorem scaledIsBIC_iff_scaledPaymentIdentity {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (hmono : MonotoneAlloc X) (p : ℝ → ℝ)
    (hscale : 0 ≤ scale) :
    ScaledIsBIC scale X p ↔ ScaledPaymentIdentity scale X p := by
  by_cases hzero : scale = 0
  · subst scale
    rw [scaledIsBIC_zero_iff_constant, scaledPaymentIdentity_zero_iff_constant]
  · have hpos : 0 < scale := lt_of_le_of_ne hscale (Ne.symm hzero)
    calc
      ScaledIsBIC scale X p ↔
          IsBIC (DirectMechanism.mk X (fun θ ↦ p θ / scale)) :=
        scaledIsBIC_iff_normalized scale X p hpos
      _ ↔ PaymentIdentity X (fun θ ↦ p θ / scale) :=
        isBIC_iff_paymentIdentity X hmono _
      _ ↔ ScaledPaymentIdentity scale X p :=
        paymentIdentity_normalized_iff_scaled scale X p hpos

/-- The scaled characterization in the paper's zero-based notation. -/
theorem scaledIsBIC_iff_zeroBasedPaymentIdentity {E : ScreeningEnv}
    (scale : ℝ) (X : AllocationRule E) (hmono : MonotoneAlloc X)
    (p : ℝ → ℝ) (hscale : 0 ≤ scale) (hlo : E.θlo = 0) :
    ScaledIsBIC scale X p ↔
      ∃ C : ℝ, ∀ θ ∈ E.types,
        p θ = θ * scaledAllocation scale X θ -
          (∫ s in (0 : ℝ)..θ, scaledAllocation scale X s) + C := by
  simpa [ScaledPaymentIdentity, hlo] using
    scaledIsBIC_iff_scaledPaymentIdentity scale X hmono p hscale

/-- Screening at the reserve stated for the actual paper-scale allocation. -/
def ScaledScreensAtReserve {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (reserve : ℝ) : Prop :=
  reserve ∈ E.types ∧ ∀ θ ∈ E.types, θ < reserve → scaledAllocation scale X θ = 0

/-- Econlib-scale screening implies screening after every rescaling. -/
theorem screensAtReserve_scaled {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) {reserve : ℝ} (hscreen : ScreensAtReserve X reserve) :
    ScaledScreensAtReserve scale X reserve := by
  refine ⟨hscreen.1, ?_⟩
  intro θ hθ hbelow
  simp [scaledAllocation, hscreen.2 θ hθ hbelow]

/-- The reserve-normalized payment in paper-scale priority units. -/
def scaledReservePayment {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (reserve θ : ℝ) : ℝ :=
  if θ < reserve then 0
  else θ * scaledAllocation scale X θ -
    ∫ s in reserve..θ, scaledAllocation scale X s

/-- A scaled screened allocation has zero integral from the lowest type to the
reserve. -/
lemma scaledIntegral_to_reserve_eq_zero {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) {reserve : ℝ}
    (hscreen : ScaledScreensAtReserve scale X reserve) :
    (∫ s in E.θlo..reserve, scaledAllocation scale X s) = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [Measure.ae_ne volume reserve] with s hne hs
  rw [Set.uIoc_of_le hscreen.1.1] at hs
  apply hscreen.2 s ⟨hs.1.le, le_trans hs.2 hscreen.1.2⟩
  exact lt_of_le_of_ne hs.2 hne

/-- The piecewise scaled reserve payment has envelope constant zero. -/
theorem scaledReservePayment_paymentIdentity {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (hmono : MonotoneAlloc X) {reserve : ℝ}
    (hscreen : ScaledScreensAtReserve scale X reserve) :
    ScaledPaymentIdentity scale X (scaledReservePayment scale X reserve) := by
  refine ⟨0, ?_⟩
  intro θ hθ
  by_cases hbelow : θ < reserve
  · rw [scaledReservePayment, if_pos hbelow]
    have hxθ : scaledAllocation scale X θ = 0 := hscreen.2 θ hθ hbelow
    have hint : (∫ s in E.θlo..θ, scaledAllocation scale X s) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hθ.1] at hs
      exact hscreen.2 s ⟨hs.1.le, le_trans hs.2 hθ.2⟩
        (lt_of_le_of_lt hs.2 hbelow)
    rw [hxθ, hint]
    ring
  · rw [scaledReservePayment, if_neg hbelow]
    have hleft : IntervalIntegrable (scaledAllocation scale X) volume E.θlo reserve :=
      (X.intervalIntegrable_x hmono E.θlo_mem_types hscreen.1).const_mul scale
    have hright : IntervalIntegrable (scaledAllocation scale X) volume reserve θ :=
      (X.intervalIntegrable_x hmono hscreen.1 hθ).const_mul scale
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [scaledIntegral_to_reserve_eq_zero scale X hscreen, zero_add] at hadd
    rw [← hadd]
    ring

/-- The scaled reserve payment implements the scaled allocation in BIC for
every nonnegative priority scale. -/
theorem scaledReservePayment_isBIC {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (hmono : MonotoneAlloc X) (hscale : 0 ≤ scale)
    {reserve : ℝ} (hscreen : ScaledScreensAtReserve scale X reserve) :
    ScaledIsBIC scale X (scaledReservePayment scale X reserve) := by
  rw [scaledIsBIC_iff_scaledPaymentIdentity scale X hmono _ hscale]
  exact scaledReservePayment_paymentIdentity scale X hmono hscreen

/-- Weak reserve eligibility retains the paper's boundary payment
`reserve · x(reserve)` at every scale. -/
theorem scaledReservePayment_at_boundary {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (reserve : ℝ) :
    scaledReservePayment scale X reserve reserve =
      reserve * scaledAllocation scale X reserve := by
  simp [scaledReservePayment]

/-- Truthful paper-scale utility under the reserve-normalized payment is zero
below the reserve and the scaled allocation integral above it. -/
theorem scaledTruthfulUtility_reservePayment {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) {reserve : ℝ}
    (hscreen : ScaledScreensAtReserve scale X reserve) {θ : ℝ}
    (hθ : θ ∈ E.types) :
    θ * scaledAllocation scale X θ - scaledReservePayment scale X reserve θ =
      if θ < reserve then 0 else ∫ s in reserve..θ, scaledAllocation scale X s := by
  by_cases hbelow : θ < reserve
  · rw [if_pos hbelow]
    simp [scaledReservePayment, hbelow, hscreen.2 θ hθ hbelow]
  · rw [if_neg hbelow]
    simp only [scaledReservePayment, hbelow, ↓reduceIte]
    ring

/-- Corollary `cor:ir` for every nonnegative top-slot weight `w₁`. -/
theorem scaledReservePayment_interimIR {E : ScreeningEnv} (scale : ℝ)
    (X : AllocationRule E) (hscale : 0 ≤ scale) {reserve : ℝ}
    (hscreen : ScaledScreensAtReserve scale X reserve) :
    ScaledIsBIR scale X (scaledReservePayment scale X reserve) := by
  intro θ hθ
  rw [scaledTruthfulUtility_reservePayment scale X hscreen hθ]
  split_ifs with hbelow
  · exact le_rfl
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_gt hbelow)
      (fun s ↦ mul_nonneg hscale (X.nonneg s))

/-! ## Noncompact type domain

The paper permits all nonnegative reports, rather than fixing a highest type.
The compact environments below are internal proof devices only: every finite
pair of reports lies in one of them, while the public BIC and payment-identity
statements quantify over the whole half-line `[0, ∞)` and contain no upper
endpoint.
-/

/-- Uniform density on `[0, hi]`, used only to instantiate Econlib's compact
screening interface inside the proof of the global theorem. -/
def compactUniformDensity (hi : ℝ) (x : ℝ) : ℝ :=
  Set.indicator (Set.Icc 0 hi) (fun _ ↦ hi⁻¹) x

theorem compactUniformDensity_nonneg (hi : ℝ) (hhi : 0 < hi) (x : ℝ) :
    0 ≤ compactUniformDensity hi x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) hi
  · simp [compactUniformDensity, hx, hhi.le]
  · simp [compactUniformDensity, hx]

theorem compactUniformDensity_integrable (hi : ℝ) :
    Integrable (compactUniformDensity hi) volume := by
  change Integrable (Set.indicator (Set.Icc 0 hi) (fun _ : ℝ ↦ hi⁻¹)) volume
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (ne_of_lt measure_Icc_lt_top)

theorem compactUniformDensity_integral_one (hi : ℝ) (hhi : 0 < hi) :
    (∫ x : ℝ, compactUniformDensity hi x) = 1 := by
  change (∫ x : ℝ, Set.indicator (Set.Icc 0 hi) (fun _ : ℝ ↦ hi⁻¹) x) = 1
  rw [integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hhi.le)]
  norm_num
  field_simp

/-- A concrete continuous distribution with positive density on `[0, hi]`.
Its distributional content is immaterial to BIC; it supplies the fields of
Econlib's `ScreeningEnv`. -/
def compactUniformContDist (hi : ℝ) (hhi : 0 < hi) :
    Econlib.Probability.ContDist where
  density := compactUniformDensity hi
  nonneg := compactUniformDensity_nonneg hi hhi
  integrable := compactUniformDensity_integrable hi
  integral_one := compactUniformDensity_integral_one hi hhi

/-- The compact restriction `[0, hi]` used to localize a finite collection of
reports from the noncompact domain. -/
def compactScreeningEnv (hi : ℝ) (hhi : 0 < hi) : ScreeningEnv where
  θlo := 0
  θhi := hi
  hθ := hhi
  dist := compactUniformContDist hi hhi
  supp_subset := by
    intro x hx
    by_contra hmem
    simp [compactUniformContDist, compactUniformDensity, hmem] at hx
  density_pos := by
    intro x hx
    simp [compactUniformContDist, compactUniformDensity, hx, hhi]
  density_cont := by
    apply ContinuousOn.congr (f := fun _ : ℝ ↦ hi⁻¹) continuousOn_const
    intro x hx
    simp [compactUniformContDist, compactUniformDensity, hx]

/-- A paper-scale allocation on the whole real line.  Reports used by the
mechanism are nonnegative, but the global extension makes monotonicity and
local interval integration available without any compact-domain premise. -/
def GlobalAllocationAtMost (scale : ℝ) (x : ℝ → ℝ) : Prop :=
  Monotone x ∧ (∀ θ, 0 ≤ x θ) ∧ ∀ θ, x θ ≤ scale

/-- Normalize a globally bounded paper-scale allocation for use on any local
Econlib environment. -/
def normalizedGlobalRule {E : ScreeningEnv} (scale : ℝ) (x : ℝ → ℝ)
    (hscale : 0 < scale) (halloc : GlobalAllocationAtMost scale x) :
    AllocationRule E where
  x θ := x θ / scale
  nonneg θ := div_nonneg (halloc.2.1 θ) hscale.le
  le_one θ := (div_le_one hscale).2 (halloc.2.2 θ)

theorem normalizedGlobalRule_monotone {E : ScreeningEnv} (scale : ℝ)
    (x : ℝ → ℝ) (hscale : 0 < scale)
    (halloc : GlobalAllocationAtMost scale x) :
    MonotoneAlloc (normalizedGlobalRule (E := E) scale x hscale halloc) := by
  intro a ha b hb hab
  exact (div_le_div_iff_of_pos_right hscale).2 (halloc.1 hab)

theorem scaledAllocation_normalizedGlobalRule {E : ScreeningEnv}
    (scale : ℝ) (x : ℝ → ℝ) (hscale : 0 < scale)
    (halloc : GlobalAllocationAtMost scale x) (θ : ℝ) :
    scaledAllocation scale
      (normalizedGlobalRule (E := E) scale x hscale halloc) θ = x θ := by
  change scale * (x θ / scale) = x θ
  field_simp

/-- BIC on the paper's full nonnegative report domain. -/
def GlobalIsBIC (x p : ℝ → ℝ) : Prop :=
  ∀ θ, 0 ≤ θ → ∀ report, 0 ≤ report →
    θ * x report - p report ≤ θ * x θ - p θ

/-- The Myerson envelope identity on every finite type in `[0, ∞)`, with
one common payment constant and no highest-type parameter. -/
def GlobalPaymentIdentity (x p : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ θ, 0 ≤ θ →
    p θ = θ * x θ - (∫ s in (0 : ℝ)..θ, x s) + C

/-- Proposition `prop:payment_identity` on the full noncompact type domain.
The allocation is measured directly in `[0, scale]`, so there is no hidden
unit upper bound.  The proof localizes each finite report pair to a compact
Econlib environment; the conclusion has one constant valid for all types. -/
theorem globalIsBIC_iff_paymentIdentity (scale : ℝ) (x p : ℝ → ℝ)
    (hscale : 0 ≤ scale) (halloc : GlobalAllocationAtMost scale x) :
    GlobalIsBIC x p ↔ GlobalPaymentIdentity x p := by
  by_cases hzero : scale = 0
  · have hxzero : x = fun _ ↦ 0 := by
      funext θ
      apply le_antisymm
      · simpa [hzero] using halloc.2.2 θ
      · exact halloc.2.1 θ
    subst x
    constructor
    · intro hbic
      refine ⟨p 0, ?_⟩
      intro θ hθ
      have h₁ := hbic θ hθ 0 le_rfl
      have h₂ := hbic 0 le_rfl θ hθ
      simp at h₁ h₂ ⊢
      linarith
    · rintro ⟨C, hpay⟩
      intro θ hθ report hreport
      have hpθ := hpay θ hθ
      have hpr := hpay report hreport
      simp at hpθ hpr ⊢
      linarith
  · have hpos : 0 < scale := lt_of_le_of_ne hscale (Ne.symm hzero)
    constructor
    · intro hbic
      refine ⟨p 0, ?_⟩
      intro θ hθ
      by_cases hθzero : θ = 0
      · subst θ
        simp
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθzero)
        let E : ScreeningEnv := compactScreeningEnv θ hθpos
        let X : AllocationRule E := normalizedGlobalRule scale x hpos halloc
        have hmonoX : MonotoneAlloc X := by
          exact normalizedGlobalRule_monotone scale x hpos halloc
        have hscaled : ∀ s, scaledAllocation scale X s = x s := by
          intro s
          exact scaledAllocation_normalizedGlobalRule scale x hpos halloc s
        have hbicE : ScaledIsBIC scale X p := by
          intro a ha b hb
          rw [hscaled a, hscaled b]
          exact hbic a ha.1 b hb.1
        obtain ⟨C, hC⟩ :=
          (scaledIsBIC_iff_scaledPaymentIdentity scale X hmonoX p hscale).1 hbicE
        have hC0 := hC 0 (by
          simpa [E, compactScreeningEnv, ScreeningEnv.types] using hθ)
        have hCθ := hC θ (by
          simpa [E, compactScreeningEnv, ScreeningEnv.types] using hθ)
        simp_rw [hscaled] at hC0 hCθ
        have hCeq : C = p 0 := by
          simpa [E, compactScreeningEnv] using hC0.symm
        simpa [E, compactScreeningEnv, hCeq] using hCθ
    · rintro ⟨C, hpay⟩
      intro θ hθ report hreport
      let hi : ℝ := max θ report + 1
      have hhi : 0 < hi := by
        dsimp [hi]
        linarith [le_max_left θ report]
      let E : ScreeningEnv := compactScreeningEnv hi hhi
      let X : AllocationRule E := normalizedGlobalRule scale x hpos halloc
      have hmonoX : MonotoneAlloc X := by
        exact normalizedGlobalRule_monotone scale x hpos halloc
      have hscaled : ∀ s, scaledAllocation scale X s = x s := by
        intro s
        exact scaledAllocation_normalizedGlobalRule scale x hpos halloc s
      have hpayE : ScaledPaymentIdentity scale X p := by
        refine ⟨C, ?_⟩
        intro a ha
        have h := hpay a ha.1
        simp_rw [hscaled]
        simpa [E, compactScreeningEnv] using h
      have hbicE :=
        (scaledIsBIC_iff_scaledPaymentIdentity scale X hmonoX p hscale).2 hpayE
      have hθE : θ ∈ E.types := by
        simp [E, compactScreeningEnv, ScreeningEnv.types, hi, hθ]
        linarith [le_max_left θ report]
      have hrE : report ∈ E.types := by
        simp [E, compactScreeningEnv, ScreeningEnv.types, hi, hreport]
        linarith [le_max_right θ report]
      have h := hbicE θ hθE report hrE
      rw [hscaled θ, hscaled report] at h
      exact h

/-- Reserve screening on the full nonnegative type domain. -/
def GlobalScreensAtReserve (x : ℝ → ℝ) (reserve : ℝ) : Prop :=
  0 ≤ reserve ∧ ∀ θ, 0 ≤ θ → θ < reserve → x θ = 0

/-- Reserve-normalized payment on all nonnegative reports. -/
def globalReservePayment (x : ℝ → ℝ) (reserve θ : ℝ) : ℝ :=
  if θ < reserve then 0
  else θ * x θ - ∫ s in reserve..θ, x s

/-- Screening makes the allocation integral vanish from zero to the reserve;
the weakly eligible boundary is ignored only inside the integral. -/
lemma globalIntegral_to_reserve_eq_zero (x : ℝ → ℝ) {reserve : ℝ}
    (hscreen : GlobalScreensAtReserve x reserve) :
    (∫ s in (0 : ℝ)..reserve, x s) = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [Measure.ae_ne volume reserve] with s hne hs
  rw [Set.uIoc_of_le hscreen.1] at hs
  exact hscreen.2 s hs.1.le (lt_of_le_of_ne hs.2 hne)

/-- The global reserve payment has envelope constant zero. -/
theorem globalReservePayment_paymentIdentity (scale : ℝ) (x : ℝ → ℝ)
    (halloc : GlobalAllocationAtMost scale x) {reserve : ℝ}
    (hscreen : GlobalScreensAtReserve x reserve) :
    GlobalPaymentIdentity x (globalReservePayment x reserve) := by
  refine ⟨0, ?_⟩
  intro θ hθ
  by_cases hbelow : θ < reserve
  · rw [globalReservePayment, if_pos hbelow]
    have hxθ : x θ = 0 := hscreen.2 θ hθ hbelow
    have hint : (∫ s in (0 : ℝ)..θ, x s) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with s hs
      rw [Set.uIoc_of_le hθ] at hs
      exact hscreen.2 s hs.1.le (lt_of_le_of_lt hs.2 hbelow)
    rw [hxθ, hint]
    ring
  · rw [globalReservePayment, if_neg hbelow]
    have hleft : IntervalIntegrable x volume 0 reserve := halloc.1.intervalIntegrable
    have hright : IntervalIntegrable x volume reserve θ := halloc.1.intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    rw [globalIntegral_to_reserve_eq_zero x hscreen, zero_add] at hadd
    rw [← hadd]
    ring

/-- The reserve payment implements the global monotone allocation in BIC. -/
theorem globalReservePayment_isBIC (scale : ℝ) (x : ℝ → ℝ)
    (hscale : 0 ≤ scale) (halloc : GlobalAllocationAtMost scale x)
    {reserve : ℝ} (hscreen : GlobalScreensAtReserve x reserve) :
    GlobalIsBIC x (globalReservePayment x reserve) := by
  rw [globalIsBIC_iff_paymentIdentity scale x _ hscale halloc]
  exact globalReservePayment_paymentIdentity scale x halloc hscreen

/-- Weak eligibility gives the exact boundary payment `r x(r)` globally. -/
theorem globalReservePayment_at_boundary (x : ℝ → ℝ) (reserve : ℝ) :
    globalReservePayment x reserve reserve = reserve * x reserve := by
  simp [globalReservePayment]

/-- Truthful utility on `[0, ∞)` is zero below the reserve and equals the
allocation integral above it. -/
theorem globalTruthfulUtility_reservePayment (x : ℝ → ℝ) {reserve : ℝ}
    (hscreen : GlobalScreensAtReserve x reserve) {θ : ℝ} (hθ : 0 ≤ θ) :
    θ * x θ - globalReservePayment x reserve θ =
      if θ < reserve then 0 else ∫ s in reserve..θ, x s := by
  by_cases hbelow : θ < reserve
  · rw [if_pos hbelow]
    simp [globalReservePayment, hbelow, hscreen.2 θ hθ hbelow]
  · rw [if_neg hbelow]
    simp only [globalReservePayment, hbelow, ↓reduceIte]
    ring

/-- Corollary `cor:ir` on the full noncompact type domain. -/
theorem globalReservePayment_interimIR (scale : ℝ) (x : ℝ → ℝ)
    (halloc : GlobalAllocationAtMost scale x) {reserve : ℝ}
    (hscreen : GlobalScreensAtReserve x reserve) :
    ∀ θ, 0 ≤ θ → 0 ≤ θ * x θ - globalReservePayment x reserve θ := by
  intro θ hθ
  rw [globalTruthfulUtility_reservePayment x hscreen hθ]
  split_ifs with hbelow
  · exact le_rfl
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_gt hbelow)
      halloc.2.1

end

end SmoothingCliff.Payments
