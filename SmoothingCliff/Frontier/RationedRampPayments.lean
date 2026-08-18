import SmoothingCliff.Frontier.RationedRamp
import SmoothingCliff.Mechanism.Payments

/-!
# Truthful transfers for the rationed ramp

The last clause of Theorem `thm:meanfield` (iii) reads "implementable as a
lottery over feasible assignments with truthful Myerson transfers".  The
lottery half is `Frontier/SlotLottery.lean`; this file is the transfer half.

The paper's argument is one line -- "Monotonicity then delivers truthful
Myerson transfers as in Proposition `prop:payment_identity`" -- and that
proposition is already formalized in `Mechanism/Payments.lean` on Econlib's
screening interface.  So all that is needed is to present the rationed ramp's
own-bid section, with the opponents held fixed, as an Econlib allocation rule
and to transport `rationedRampRule_ownMonotone` to it.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff SmoothingCliff.Payments
open Econlib.MechanismDesign.Transfers.SingleParameter

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}

/-- The rationed ramp seen by one agent, with the opponents' bids fixed and the
allocation normalized by the slot weight, as an Econlib allocation rule.  Types
below the reserve are clamped, which is invisible on `E.types` once the lowest
type is the reserve. -/
def rationedRampAlloc (E : ScreeningEnv) (weight sensitivity : NNReal)
    (hweight : 0 < (weight : ℝ)) {capacity : ℝ} (hCapacity : 0 ≤ capacity)
    (threshold : ℝ) (b : EligibleProfile ι reserve) (i : ι) : AllocationRule E where
  x := fun θ => rationedRampRule weight sensitivity capacity threshold
      (updateBid b i ⟨max θ reserve, by simp⟩) i / (weight : ℝ)
  nonneg := fun _ =>
    div_nonneg (rationedRampRule_nonneg weight sensitivity threshold hCapacity _ _)
      hweight.le
  le_one := fun _ => by
    rw [div_le_one hweight]
    exact rationedRampRule_le_weight weight sensitivity threshold hCapacity _ _

@[simp] theorem rationedRampAlloc_apply (E : ScreeningEnv) (weight sensitivity : NNReal)
    (hweight : 0 < (weight : ℝ)) {capacity : ℝ} (hCapacity : 0 ≤ capacity)
    (threshold : ℝ) (b : EligibleProfile ι reserve) (i : ι) (θ : ℝ) :
    (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i).x θ
      = rationedRampRule weight sensitivity capacity threshold
          (updateBid b i ⟨max θ reserve, by simp⟩) i / (weight : ℝ) := rfl

/-- Own-bid monotonicity of the rule transports to the normalized curve. -/
theorem rationedRampAlloc_monotone (E : ScreeningEnv) (weight sensitivity : NNReal)
    (hweight : 0 < (weight : ℝ)) {capacity : ℝ} (hCapacity : 0 ≤ capacity)
    (threshold : ℝ) (b : EligibleProfile ι reserve) (i : ι) :
    MonotoneAlloc (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i) := by
  intro θ _ θ' _ hle
  rw [rationedRampAlloc_apply, rationedRampAlloc_apply]
  have hbid : (⟨max θ reserve, by simp⟩ : EligibleBid reserve)
      ≤ ⟨max θ' reserve, by simp⟩ := max_le_max hle le_rfl
  have hnum := rationedRampRule_ownMonotone weight sensitivity threshold hCapacity b i hbid
  gcongr

/-- With the reserve as the lowest type, the screening condition is automatic. -/
theorem rationedRampAlloc_screensAtReserve (E : ScreeningEnv) (hlo : E.θlo = reserve)
    (weight sensitivity : NNReal) (hweight : 0 < (weight : ℝ)) {capacity : ℝ}
    (hCapacity : 0 ≤ capacity) (threshold : ℝ) (b : EligibleProfile ι reserve)
    (i : ι) :
    ScreensAtReserve (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i) reserve := by
  constructor
  · rw [ScreeningEnv.mem_types, ← hlo]
    exact ⟨le_rfl, E.hθ.le⟩
  · intro θ hθ hbelow
    rw [ScreeningEnv.mem_types] at hθ
    rw [← hlo] at hbelow
    exact absurd hθ.1 (not_le.mpr hbelow)

/-- **The transfer clause of `thm:meanfield` (iii).**  The rationed ramp,
together with the reserve-anchored Myerson payment, is Bayesian incentive
compatible and interim individually rational for every agent at every profile
of opponents' bids. -/
theorem rationedRampRule_isBIC_and_isBIR (E : ScreeningEnv) (hlo : E.θlo = reserve)
    (weight sensitivity : NNReal) (hweight : 0 < (weight : ℝ)) {capacity : ℝ}
    (hCapacity : 0 ≤ capacity) (threshold : ℝ) (b : EligibleProfile ι reserve)
    (i : ι) :
    IsBIC (DirectMechanism.mk (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
        (reservePayment (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i) reserve)) ∧
    IsBIR (DirectMechanism.mk (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
        (reservePayment (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i) reserve)) := by
  have hmono := rationedRampAlloc_monotone E weight sensitivity hweight hCapacity threshold b i
  have hscreen := rationedRampAlloc_screensAtReserve E hlo weight sensitivity hweight hCapacity threshold b i
  exact ⟨reservePayment_isBIC _ hmono hscreen, reservePayment_interimIR _ hscreen⟩

/-! ### The same statement in the paper's units

Econlib normalizes an allocation to `[0,1]`, so `rationedRampAlloc` carries
`x^RR / w₁`.  The paper measures priority in units of `w₁`.  The scaled
interface of `Mechanism/Payments.lean` states incentive compatibility and
individual rationality directly at an arbitrary scale, so the paper-scale
statement is available without rescaling by hand: at scale `w₁` the allocation
appearing in the utilities is `x^RR` itself, which the first lemma records. -/

section PaperScale

/-- At scale `w₁` the Econlib rule carries the paper's own allocation. -/
theorem scaledAllocation_rationedRampAlloc (E : ScreeningEnv)
    (weight sensitivity : NNReal) (hweight : 0 < (weight : ℝ)) {capacity : ℝ}
    (hCapacity : 0 ≤ capacity) (threshold : ℝ) (b : EligibleProfile ι reserve)
    (i : ι) (θ : ℝ) :
    scaledAllocation (weight : ℝ)
        (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i) θ
      = rationedRampRule weight sensitivity capacity threshold
          (updateBid b i ⟨max θ reserve, by simp⟩) i := by
  rw [scaledAllocation, rationedRampAlloc_apply]
  field_simp

/-- **The transfer clause in paper units.**  The rationed ramp, in units of the
top slot weight, together with the reserve-anchored payment at that scale, is
Bayesian incentive compatible and interim individually rational. -/
theorem rationedRampRule_paperScale_isBIC_and_isBIR (E : ScreeningEnv)
    (hlo : E.θlo = reserve) (weight sensitivity : NNReal)
    (hweight : 0 < (weight : ℝ)) {capacity : ℝ} (hCapacity : 0 ≤ capacity)
    (threshold : ℝ) (b : EligibleProfile ι reserve) (i : ι) :
    ScaledIsBIC (weight : ℝ)
        (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
        (scaledReservePayment (weight : ℝ)
          (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
          reserve) ∧
      ScaledIsBIR (weight : ℝ)
        (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
        (scaledReservePayment (weight : ℝ)
          (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
          reserve) := by
  have hmono := rationedRampAlloc_monotone E weight sensitivity hweight hCapacity
    threshold b i
  have hscreen : ScaledScreensAtReserve (weight : ℝ)
      (rationedRampAlloc E weight sensitivity hweight hCapacity threshold b i)
      reserve := by
    obtain ⟨hmem, hbelow⟩ := rationedRampAlloc_screensAtReserve E hlo weight
      sensitivity hweight hCapacity threshold b i
    exact ⟨hmem, fun θ hθ hlt => by
      rw [scaledAllocation, hbelow θ hθ hlt, mul_zero]⟩
  exact ⟨scaledReservePayment_isBIC _ _ hmono hweight.le hscreen,
    scaledReservePayment_interimIR _ _ hweight.le hscreen⟩

end PaperScale

end

end SmoothingCliff.Frontier
