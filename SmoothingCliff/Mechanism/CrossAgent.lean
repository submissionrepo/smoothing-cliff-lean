import SmoothingCliff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Cross-agent and payment-vector sensitivity

This file formalizes Lemma `lem:crossagent` and Corollary
`cor:paymentvector` from *Smoothing the Cliff*.  The allocation result is
abstract: cross-monotonicity makes every spillover have the same sign, no waste
turns their sum into the own-coordinate change, and the own-coordinate
Lipschitz certificate bounds that change.

Payments are not postulated.  `myersonPayment` is the reserve-normalized
Myerson integral, and the payment-vector bound is derived from that definition.
-/

open scoped BigOperators

namespace SmoothingCliff.Mechanism

/-- Lemma `lem:crossagent`, abstracted from the particular Plackett--Luce
formula.  Raising coordinate `i` lowers every other coordinate, and each loss
is no larger than the own-coordinate Lipschitz budget.  The second conjunct is
the coordinatewise form of the full-vector sup-norm certificate. -/
theorem crossAgentSensitivity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    (∀ j, j ≠ i →
      0 ≤ x (updateBid b i z) j - x (updateBid b i z') j ∧
      x (updateBid b i z) j - x (updateBid b i z') j ≤
        (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ))) ∧
    ∀ j, |x (updateBid b i z) j - x (updateBid b i z') j| ≤
      (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
  let low := updateBid b i z
  let high := updateBid b i z'
  have hreal : (z : ℝ) ≤ (z' : ℝ) := hzz'
  have hOthers : ∀ j, j ≠ i → 0 ≤ x low j - x high j := by
    intro j hji
    exact sub_nonneg.mpr (hCross b j i hji hzz')
  have hOwnBound :
      |x low i - x high i| ≤
        (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
    have h := (hOwn b i).dist_le_mul z z'
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq] at h
    calc
      |x low i - x high i| ≤
          (sensitivity : ℝ) * |(z : ℝ) - (z' : ℝ)| := h
      _ = (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hreal)]
        ring
  have hConservation :
      Finset.sum (Finset.univ.erase i) (fun j => x low j - x high j) =
        x high i - x low i := by
    have hsum : (∑ j, (x low j - x high j)) = 0 := by
      rw [Finset.sum_sub_distrib, hMass low, hMass high, sub_self]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    linarith
  have hOtherBound : ∀ j, j ≠ i →
      x low j - x high j ≤
        (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
    intro j hji
    have hjmem : j ∈ Finset.univ.erase i := by simp [hji]
    calc
      x low j - x high j ≤
          Finset.sum (Finset.univ.erase i) (fun k => x low k - x high k) :=
        Finset.single_le_sum
          (fun k hk => hOthers k (by simpa using (Finset.ne_of_mem_erase hk)))
          hjmem
      _ = x high i - x low i := hConservation
      _ ≤ |x low i - x high i| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := hOwnBound
  constructor
  · intro j hji
    exact ⟨hOthers j hji, hOtherBound j hji⟩
  · intro j
    by_cases hji : j = i
    · subst j
      exact hOwnBound
    · rw [abs_of_nonneg (hOthers j hji)]
      exact hOtherBound j hji

/-- The literal sup-norm version of `crossAgentSensitivity`. -/
theorem crossAgent_supNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    ‖fun j => x (updateBid b i z) j - x (updateBid b i z') j‖ ≤
      (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
  have hpoint := (crossAgentSensitivity sensitivity x hOwn hCross hMass
    b i z z' hzz').2
  have hnonneg :
      0 ≤ (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) :=
    mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hzz')
  rw [Pi.norm_def]
  have hs :
      Finset.univ.sup
          (fun j => ‖x (updateBid b i z) j - x (updateBid b i z') j‖₊) ≤
        ⟨(sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)), hnonneg⟩ := by
    apply Finset.sup_le
    intro j hj
    exact_mod_cast hpoint j
  exact_mod_cast hs

/-- Symmetric full-vector certificate for two arbitrary eligible reports. -/
theorem fullAllocationVector_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) :
    ‖fun j => x (updateBid b i z) j - x (updateBid b i z') j‖ ≤
      (sensitivity : ℝ) * |(z : ℝ) - (z' : ℝ)| := by
  rcases le_total z z' with hzz' | hz'z
  · have h := crossAgent_supNorm sensitivity x hOwn hCross hMass b i z z' hzz'
    have hreal : (z : ℝ) ≤ (z' : ℝ) := hzz'
    simpa [abs_of_nonpos (sub_nonpos.mpr hreal)] using h
  · have h := crossAgent_supNorm sensitivity x hOwn hCross hMass b i z' z hz'z
    have hreal : (z' : ℝ) ≤ (z : ℝ) := hz'z
    have hfun :
        (fun j => x (updateBid b i z) j - x (updateBid b i z') j) =
          -(fun j => x (updateBid b i z') j - x (updateBid b i z) j) := by
      funext j
      simp
    rw [hfun, norm_neg]
    simpa [abs_of_nonneg (sub_nonneg.mpr hreal)] using h

/-- Project a real report to the eligible half-line.  The maximum is used only
to give the Myerson allocation curve a total real domain; on the integration
interval it is the identity. -/
def eligibleClamp (reserve z : ℝ) : EligibleBid reserve :=
  ⟨max reserve z, le_max_left reserve z⟩

theorem eligibleClamp_lipschitz (reserve : ℝ) :
    LipschitzWith 1 (eligibleClamp reserve) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Subtype.dist_eq]
  simpa [eligibleClamp] using
    (((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max reserve).dist_le_mul a b)

/-- The one-dimensional allocation curve used in the Myerson identity. -/
def allocationCurve {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) (z : ℝ) : ℝ :=
  x (updateBid b i (eligibleClamp reserve z)) i

theorem allocationCurve_lipschitz
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (sensitivity : NNReal) (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (b : EligibleProfile ι reserve) (i : ι) :
    LipschitzWith sensitivity (allocationCurve x b i) := by
  simpa [allocationCurve] using
    (hOwn b i).comp (eligibleClamp_lipschitz reserve)

theorem allocationCurve_at_bid
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) :
    allocationCurve x b i (b i : ℝ) = x b i := by
  have hclamp : eligibleClamp reserve (b i : ℝ) = b i := by
    apply Subtype.ext
    exact max_eq_right (show reserve ≤ (b i : ℝ) from (b i).property)
  simp [allocationCurve, hclamp, updateBid]

/-- Reserve-normalized Myerson payment for a one-dimensional allocation curve. -/
noncomputable def myersonCurvePayment
    (reserve : ℝ) (allocation : ℝ → ℝ) (bid : ℝ) : ℝ :=
  bid * allocation bid - ∫ z in reserve..bid, allocation z

/-- Expected payment obtained from the interim allocation by the Myerson
integral.  This is a definition, not a payment-stability premise. -/
noncomputable def myersonPayment
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) : ℝ :=
  myersonCurvePayment reserve (allocationCurve x b i) (b i : ℝ)

theorem myersonPayment_eq_integral
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) :
    myersonPayment x b i =
      (b i : ℝ) * x b i -
        ∫ z in reserve..(b i : ℝ), allocationCurve x b i z := by
  simp [myersonPayment, myersonCurvePayment, allocationCurve_at_bid]

theorem myersonCurvePayment_sub
    (reserve a b : ℝ) (allocation : ℝ → ℝ)
    (hAllocation : Continuous allocation) :
    myersonCurvePayment reserve allocation b -
        myersonCurvePayment reserve allocation a =
      b * (allocation b - allocation a) -
        ∫ t in a..b, (allocation t - allocation a) := by
  have h₁ := hAllocation.intervalIntegrable
    (μ := MeasureTheory.volume) reserve a
  have h₂ := hAllocation.intervalIntegrable
    (μ := MeasureTheory.volume) a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hconst :
      IntervalIntegrable (fun _ : ℝ => allocation a)
        MeasureTheory.volume a b :=
    continuous_const.intervalIntegrable (μ := MeasureTheory.volume) a b
  have hsub := intervalIntegral.integral_sub h₂ hconst
  unfold myersonCurvePayment
  rw [← hadd, hsub]
  simp only [intervalIntegral.integral_const]
  ring

/-- Moving an agent's own report changes her reserve-normalized Myerson payment
by at most the paper's relaxed `2 * upper * sensitivity` constant.  The proof
uses the cancellation inside the Myerson identity; it does not assume a bound
on allocation levels. -/
theorem myersonCurvePayment_lipschitz
    (reserve upper a b : ℝ) (allocation : ℝ → ℝ)
    (sensitivity : NNReal)
    (hLip : LipschitzWith sensitivity allocation)
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hbUpper : b ≤ upper) :
    |myersonCurvePayment reserve allocation b -
        myersonCurvePayment reserve allocation a| ≤
      2 * upper * (sensitivity : ℝ) * (b - a) := by
  let C : ℝ := (sensitivity : ℝ) * (b - a)
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab
  have hC : 0 ≤ C := mul_nonneg sensitivity.coe_nonneg hD
  have hb0 : 0 ≤ b := ha0.trans hab
  have hEndpoint : |allocation b - allocation a| ≤ C := by
    have h := hLip.dist_le_mul b a
    rw [Real.dist_eq, Real.dist_eq] at h
    simpa [C, abs_of_nonneg hD] using h
  have hpoint :
      ∀ t ∈ Set.uIoc a b, ‖allocation t - allocation a‖ ≤ C := by
    intro t ht
    have ht' : t ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have hta : 0 ≤ t - a := sub_nonneg.mpr ht'.1.le
    have htb : t - a ≤ b - a := by linarith [ht'.2]
    have h := hLip.dist_le_mul t a
    rw [Real.dist_eq, Real.dist_eq] at h
    calc
      ‖allocation t - allocation a‖ =
          |allocation t - allocation a| := Real.norm_eq_abs _
      _ ≤ (sensitivity : ℝ) * |t - a| := h
      _ = (sensitivity : ℝ) * (t - a) := by
        rw [abs_of_nonneg hta]
      _ ≤ (sensitivity : ℝ) * (b - a) :=
        mul_le_mul_of_nonneg_left htb sensitivity.coe_nonneg
      _ = C := rfl
  have hIntegral :
      |∫ t in a..b, (allocation t - allocation a)| ≤ C * (b - a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa [Real.norm_eq_abs, abs_of_nonneg hD] using h
  rw [myersonCurvePayment_sub reserve a b allocation hLip.continuous]
  calc
    |b * (allocation b - allocation a) -
        ∫ t in a..b, (allocation t - allocation a)| ≤
        |b * (allocation b - allocation a)| +
          |∫ t in a..b, (allocation t - allocation a)| :=
      abs_sub _ _
    _ ≤ b * C + C * (b - a) := by
      apply add_le_add
      · simpa [abs_mul, abs_of_nonneg hb0] using
          (mul_le_mul_of_nonneg_left hEndpoint hb0)
      · exact hIntegral
    _ = C * (b + (b - a)) := by ring
    _ ≤ C * (upper + upper) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = 2 * upper * (sensitivity : ℝ) * (b - a) := by
      simp [C]
      ring

/-- At a fixed bid, pointwise perturbation of the allocation curve propagates
through the Myerson integral with factor at most `2 * upper`. -/
theorem myersonCurvePayment_fixedBid_stability
    (reserve upper bid C : ℝ) (f g : ℝ → ℝ)
    (hReserve : 0 ≤ reserve) (hBid : reserve ≤ bid)
    (hUpper : bid ≤ upper) (hC : 0 ≤ C)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t ∈ Set.Icc reserve bid, ‖f t - g t‖ ≤ C) :
    |myersonCurvePayment reserve f bid -
        myersonCurvePayment reserve g bid| ≤
      2 * upper * C := by
  have hfInt := hf.intervalIntegrable
    (μ := MeasureTheory.volume) reserve bid
  have hgInt := hg.intervalIntegrable
    (μ := MeasureTheory.volume) reserve bid
  have hsub := intervalIntegral.integral_sub hfInt hgInt
  have hpoint : ∀ t ∈ Set.uIoc reserve bid, ‖f t - g t‖ ≤ C := by
    intro t ht
    have ht' : t ∈ Set.Ioc reserve bid := by
      simpa [Set.uIoc_of_le hBid] using ht
    exact hfg t ⟨ht'.1.le, ht'.2⟩
  have hIntegral :
      |∫ t in reserve..bid, (f t - g t)| ≤ C * (bid - reserve) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hBid)] using h
  have hBid0 : 0 ≤ bid := hReserve.trans hBid
  unfold myersonCurvePayment
  calc
    |bid * f bid - (∫ t in reserve..bid, f t) -
        (bid * g bid - ∫ t in reserve..bid, g t)| =
        |bid * (f bid - g bid) -
          ∫ t in reserve..bid, (f t - g t)| := by
            apply congrArg abs
            rw [hsub]
            ring
    _ ≤ |bid * (f bid - g bid)| +
          |∫ t in reserve..bid, (f t - g t)| := abs_sub _ _
    _ ≤ bid * C + C * (bid - reserve) := by
      apply add_le_add
      · simpa [abs_mul, abs_of_nonneg hBid0] using
          (mul_le_mul_of_nonneg_left (hfg bid ⟨hBid, le_rfl⟩) hBid0)
      · exact hIntegral
    _ = C * (bid + (bid - reserve)) := by ring
    _ ≤ C * (upper + upper) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = 2 * upper * C := by ring

theorem allocationCurve_update_self
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) (z : EligibleBid reserve) :
    allocationCurve x (updateBid b i z) i = allocationCurve x b i := by
  funext t
  simp [allocationCurve, updateBid]

theorem myersonPayment_update_self
    {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) (b : EligibleProfile ι reserve)
    (i : ι) (z : EligibleBid reserve) :
    myersonPayment x (updateBid b i z) i =
      myersonCurvePayment reserve (allocationCurve x b i) (z : ℝ) := by
  simp only [myersonPayment]
  rw [allocationCurve_update_self]
  simp [updateBid]

/-- Own-coordinate part of Corollary `cor:paymentvector`. -/
theorem myersonPayment_own_coordinate
    {ι : Type*} [DecidableEq ι]
    {reserve upper : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hReserve : 0 ≤ reserve)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z')
    (hz'Upper : (z' : ℝ) ≤ upper) :
    |myersonPayment x (updateBid b i z) i -
        myersonPayment x (updateBid b i z') i| ≤
      2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
  rw [myersonPayment_update_self, myersonPayment_update_self]
  rw [abs_sub_comm]
  have hz0 : 0 ≤ (z : ℝ) :=
    hReserve.trans (show reserve ≤ (z : ℝ) from z.property)
  exact myersonCurvePayment_lipschitz reserve upper (z : ℝ) (z' : ℝ)
    (allocationCurve x b i) sensitivity
    (allocationCurve_lipschitz sensitivity x hOwn b i)
    hz0 hzz' hz'Upper

/-- Cross-coordinate part of Corollary `cor:paymentvector`, obtained by
integrating `crossAgentSensitivity` along agent `j`'s Myerson curve. -/
theorem myersonPayment_cross_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight upper : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (hReserve : 0 ≤ reserve)
    (b : EligibleProfile ι reserve)
    (hUpper : ∀ k, (b k : ℝ) ≤ upper)
    (i j : ι) (hji : j ≠ i)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    |myersonPayment x (updateBid b i z) j -
        myersonPayment x (updateBid b i z') j| ≤
      2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
  let low := updateBid b i z
  let high := updateBid b i z'
  let C : ℝ := (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ))
  have hC : 0 ≤ C :=
    mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hzz')
  have hlowj : low j = b j := by simp [low, updateBid, hji]
  have hhighj : high j = b j := by simp [high, updateBid, hji]
  have hcurve :
      ∀ t ∈ Set.Icc reserve (b j : ℝ),
        ‖allocationCurve x low j t - allocationCurve x high j t‖ ≤ C := by
    intro t ht
    have hs := (crossAgentSensitivity sensitivity x hOwn hCross hMass
      (updateBid b j (eligibleClamp reserve t)) i z z' hzz').2 j
    have hij : i ≠ j := Ne.symm hji
    simpa [C, low, high, allocationCurve, updateBid,
      Function.update_comm hij] using hs
  change
    |myersonCurvePayment reserve (allocationCurve x low j) (low j : ℝ) -
        myersonCurvePayment reserve (allocationCurve x high j) (high j : ℝ)| ≤
      2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ))
  rw [hlowj, hhighj]
  simpa [C, mul_assoc] using
    (myersonCurvePayment_fixedBid_stability reserve upper (b j : ℝ) C
      (allocationCurve x low j) (allocationCurve x high j)
      hReserve (b j).property (hUpper j) hC
      (allocationCurve_lipschitz sensitivity x hOwn low j).continuous
      (allocationCurve_lipschitz sensitivity x hOwn high j).continuous hcurve)

/-- Ordered-coordinate, full-vector version of Corollary `cor:paymentvector`. -/
theorem myersonPaymentVector_coordinate_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight upper : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (hReserve : 0 ≤ reserve)
    (b : EligibleProfile ι reserve)
    (hUpper : ∀ k, (b k : ℝ) ≤ upper)
    (i : ι) (z z' : EligibleBid reserve) (hzz' : z ≤ z')
    (hz'Upper : (z' : ℝ) ≤ upper) :
    (∀ j,
      |myersonPayment x (updateBid b i z) j -
          myersonPayment x (updateBid b i z') j| ≤
        2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ))) ∧
    ‖fun j => myersonPayment x (updateBid b i z) j -
        myersonPayment x (updateBid b i z') j‖ ≤
      2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
  have hpoint : ∀ j,
      |myersonPayment x (updateBid b i z) j -
          myersonPayment x (updateBid b i z') j| ≤
        2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) := by
    intro j
    by_cases hji : j = i
    · subst j
      exact myersonPayment_own_coordinate sensitivity x hOwn hReserve
        b i z z' hzz' hz'Upper
    · exact myersonPayment_cross_coordinate sensitivity x hOwn hCross hMass
        hReserve b hUpper i j hji z z' hzz'
  constructor
  · exact hpoint
  · have hUpper0 : 0 ≤ upper :=
      hReserve.trans ((b i).property.trans (hUpper i))
    have hBound0 :
        0 ≤ 2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)) :=
      mul_nonneg
        (mul_nonneg (by positivity) sensitivity.coe_nonneg)
        (sub_nonneg.mpr hzz')
    rw [Pi.norm_def]
    have hs :
        Finset.univ.sup
            (fun j => ‖myersonPayment x (updateBid b i z) j -
              myersonPayment x (updateBid b i z') j‖₊) ≤
          ⟨2 * upper * (sensitivity : ℝ) * ((z' : ℝ) - (z : ℝ)),
            hBound0⟩ := by
      apply Finset.sup_le
      intro j hj
      exact_mod_cast hpoint j
    exact_mod_cast hs

/-- Symmetric sup-norm payment certificate, with the exact constant stated in
Corollary `cor:paymentvector`. -/
theorem fullPaymentVector_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve weight upper : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hOwn : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hMass : OneSlotNoWaste weight x)
    (hReserve : 0 ≤ reserve)
    (b : EligibleProfile ι reserve)
    (hUpper : ∀ k, (b k : ℝ) ≤ upper)
    (i : ι) (z z' : EligibleBid reserve)
    (hzUpper : (z : ℝ) ≤ upper) (hz'Upper : (z' : ℝ) ≤ upper) :
    ‖fun j => myersonPayment x (updateBid b i z) j -
        myersonPayment x (updateBid b i z') j‖ ≤
      2 * upper * (sensitivity : ℝ) * |(z : ℝ) - (z' : ℝ)| := by
  rcases le_total z z' with hzz' | hz'z
  · have h := (myersonPaymentVector_coordinate_lipschitz sensitivity x hOwn
      hCross hMass hReserve b hUpper i z z' hzz' hz'Upper).2
    have hreal : (z : ℝ) ≤ (z' : ℝ) := hzz'
    simpa [abs_of_nonpos (sub_nonpos.mpr hreal)] using h
  · have h := (myersonPaymentVector_coordinate_lipschitz sensitivity x hOwn
      hCross hMass hReserve b hUpper i z' z hz'z hzUpper).2
    have hreal : (z' : ℝ) ≤ (z : ℝ) := hz'z
    have hfun :
        (fun j => myersonPayment x (updateBid b i z) j -
          myersonPayment x (updateBid b i z') j) =
          -(fun j => myersonPayment x (updateBid b i z') j -
            myersonPayment x (updateBid b i z) j) := by
      funext j
      simp
    rw [hfun, norm_neg]
    simpa [abs_of_nonneg (sub_nonneg.mpr hreal)] using h

end SmoothingCliff.Mechanism
