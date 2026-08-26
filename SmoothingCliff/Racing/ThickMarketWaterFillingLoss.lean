import SmoothingCliff.Racing.ThickMarketCandidateMass
import SmoothingCliff.Racing.ThickMarketOrderStatistics
import SmoothingCliff.Frontier.FlatKMinimax

/-!
# The canonical water-filling loss in a thick market

The threshold used to define `waterFillingVector` is chosen nonconstructively.
Allocation-level uniqueness nevertheless gives a globally Lipschitz allocation
vector.  This file uses that fact to prove measurability of the canonical loss
directly, without asserting measurability of the chosen threshold.  It then
connects the candidate-mass event to the deterministic `weight * delta` loss
bound used in the thick-market argument.
-/

namespace SmoothingCliff.Racing

open MeasureTheory ProbabilityTheory Set Filter Topology
open SmoothingCliff.Frontier
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Canonical one-slot water-filling allocation is Lipschitz as a function of
the entire finite score profile, coordinate by coordinate. -/
theorem waterFillingVector_fullProfile_lipschitz
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity) (i : ι) :
    LipschitzWith (2 * sensitivity * (Fintype.card ι : NNReal))
      (fun profile : ι → ℝ =>
        waterFillingVector weight sensitivity hsensitivity profile i) := by
  let threshold : (ι → ℝ) → ℝ :=
    waterFillingThreshold weight sensitivity hsensitivity
  have hMass : ∀ profile,
      waterFillMass weight sensitivity profile (threshold profile) =
        (weight : ℝ) := by
    intro profile
    exact waterFillingThreshold_spec weight sensitivity hsensitivity profile
  apply LipschitzWith.of_dist_le_mul
  intro profile profile'
  have hFull := waterFillingSelection_fullVector_l1_le
    weight sensitivity threshold (weight : ℝ) hMass profile profile'
  have hFull' :
      finiteL1
          (waterFillingVector weight sensitivity hsensitivity profile')
          (waterFillingVector weight sensitivity hsensitivity profile) ≤
        (2 * (sensitivity : ℝ) *
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) *
          finiteL1 profile' profile := by
    simpa [threshold, waterFillingSelection, waterFillingVector] using hFull
  have hCoordinate :
      |waterFillingVector weight sensitivity hsensitivity profile' i -
          waterFillingVector weight sensitivity hsensitivity profile i| ≤
        finiteL1
          (waterFillingVector weight sensitivity hsensitivity profile')
          (waterFillingVector weight sensitivity hsensitivity profile) := by
    unfold finiteL1
    exact Finset.single_le_sum
      (fun j _ => abs_nonneg
        (waterFillingVector weight sensitivity hsensitivity profile' j -
          waterFillingVector weight sensitivity hsensitivity profile j))
      (Finset.mem_univ i)
  have hInput : finiteL1 profile' profile ≤
      (Fintype.card ι : ℝ) * dist profile' profile := by
    unfold finiteL1
    calc
      (∑ j, |profile' j - profile j|) ≤
          ∑ _j : ι, dist profile' profile := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [Real.dist_eq] using dist_le_pi_dist profile' profile j
      _ = (Fintype.card ι : ℝ) * dist profile' profile := by simp
  have hCardPos : (0 : ℝ) < Fintype.card ι := by positivity
  have hFraction :
      ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) ≤ 1 := by
    exact (div_le_one hCardPos).2 (by linarith)
  have hCoefficient :
      2 * (sensitivity : ℝ) *
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ≤
        2 * (sensitivity : ℝ) := by
    calc
      2 * (sensitivity : ℝ) *
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) =
          (2 * (sensitivity : ℝ)) *
            (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by ring
      _ ≤ (2 * (sensitivity : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hFraction
          (mul_nonneg (by norm_num) sensitivity.coe_nonneg)
      _ = 2 * (sensitivity : ℝ) := by ring
  have hL1Nonneg : 0 ≤ finiteL1 profile' profile := by
    unfold finiteL1
    positivity
  rw [Real.dist_eq]
  calc
    |waterFillingVector weight sensitivity hsensitivity profile i -
        waterFillingVector weight sensitivity hsensitivity profile' i| =
        |waterFillingVector weight sensitivity hsensitivity profile' i -
          waterFillingVector weight sensitivity hsensitivity profile i| :=
      abs_sub_comm _ _
    _ ≤ finiteL1
          (waterFillingVector weight sensitivity hsensitivity profile')
          (waterFillingVector weight sensitivity hsensitivity profile) :=
      hCoordinate
    _ ≤ (2 * (sensitivity : ℝ) *
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) *
          finiteL1 profile' profile := hFull'
    _ ≤ 2 * (sensitivity : ℝ) * finiteL1 profile' profile :=
      mul_le_mul_of_nonneg_right hCoefficient hL1Nonneg
    _ ≤ 2 * (sensitivity : ℝ) *
          ((Fintype.card ι : ℝ) * dist profile' profile) := by
      gcongr
    _ = ((2 * sensitivity * (Fintype.card ι : NNReal) : NNReal) : ℝ) *
          dist profile profile' := by
      rw [dist_comm profile' profile]
      norm_num
      ring

/-- Coordinate measurability of canonical water filling for a measurable
random finite profile. -/
theorem measurable_waterFillingVector_profile
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (i : ι) :
    Measurable (fun ω => waterFillingVector weight sensitivity hsensitivity
      (fun j => X j ω) i) := by
  have hProfile : Measurable (fun ω j => X j ω) :=
    measurable_pi_lambda _ hX
  exact (waterFillingVector_fullProfile_lipschitz
    weight sensitivity hsensitivity i).continuous.measurable.comp hProfile

/-- The canonical one-slot allocation-value loss relative to the highest
premium in the profile. -/
def canonicalOneSlotWaterFillingLoss
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) : ℝ :=
  (weight : ℝ) * profileTop premium -
    ∑ i, premium i *
      waterFillingVector weight sensitivity hsensitivity premium i

/-- The canonical loss is measurable for every measurable random profile. -/
theorem measurable_canonicalOneSlotWaterFillingLoss
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => canonicalOneSlotWaterFillingLoss
      weight sensitivity hsensitivity (fun i => X i ω)) := by
  have hProfile : Measurable (fun ω i => X i ω) :=
    measurable_pi_lambda _ hX
  have hTop : Measurable (fun ω => profileTop (fun i => X i ω)) :=
    measurable_profileTop.comp hProfile
  have hAllocation : ∀ i, Measurable (fun ω =>
      waterFillingVector weight sensitivity hsensitivity
        (fun j => X j ω) i) :=
    measurable_waterFillingVector_profile weight sensitivity hsensitivity hX
  unfold canonicalOneSlotWaterFillingLoss
  exact (measurable_const.mul hTop).sub
    (Finset.measurable_sum _ fun i _ => (hX i).mul (hAllocation i))

/-- Exact gap representation of the canonical allocation-value loss. -/
theorem canonicalOneSlotWaterFillingLoss_eq_sum_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) :
    canonicalOneSlotWaterFillingLoss weight sensitivity hsensitivity premium =
      ∑ i, waterFillingVector weight sensitivity hsensitivity premium i *
        (profileTop premium - premium i) := by
  unfold canonicalOneSlotWaterFillingLoss
  rw [← waterFillingVector_mass weight sensitivity hsensitivity premium,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Canonical water-filling loss is nonnegative when compared with the largest
premium in the profile. -/
theorem canonicalOneSlotWaterFillingLoss_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) :
    0 ≤ canonicalOneSlotWaterFillingLoss
      weight sensitivity hsensitivity premium := by
  rw [canonicalOneSlotWaterFillingLoss_eq_sum_gap]
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (waterFillingVector_nonneg weight sensitivity hsensitivity premium i)
    (sub_nonneg.mpr (by
      simpa only [profileTop, Finset.sup'_apply] using
        (Finset.le_sup' (f := premium) (Finset.mem_univ i))))

/-- On a profile contained in `[0, endpoint]`, loss is at most the full slot
weight times the endpoint. -/
theorem canonicalOneSlotWaterFillingLoss_le_endpoint
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) {endpoint : ℝ}
    (hnonneg : ∀ i, 0 ≤ premium i)
    (hupper : ∀ i, premium i ≤ endpoint) :
    canonicalOneSlotWaterFillingLoss weight sensitivity hsensitivity premium ≤
      (weight : ℝ) * endpoint := by
  rw [canonicalOneSlotWaterFillingLoss_eq_sum_gap]
  calc
    (∑ i, waterFillingVector weight sensitivity hsensitivity premium i *
        (profileTop premium - premium i)) ≤
        ∑ i, waterFillingVector weight sensitivity hsensitivity premium i *
          endpoint := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · linarith [profileTop_le_of_forall_le premium hupper, hnonneg i]
      · exact waterFillingVector_nonneg weight sensitivity hsensitivity premium i
    _ = (weight : ℝ) * endpoint := by
      rw [← Finset.sum_mul,
        waterFillingVector_mass weight sensitivity hsensitivity premium]

/-- Every overfull proposed threshold dominates the canonical allocation
coordinatewise.  This avoids choosing an ordered representative from a flat
interval of mass-solving thresholds. -/
theorem waterFillingVector_le_at_overfullThreshold
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) (proposed : ℝ)
    (hoverfull : (weight : ℝ) ≤
      waterFillMass weight sensitivity premium proposed) (i : ι) :
    waterFillingVector weight sensitivity hsensitivity premium i ≤
      waterFillAt weight sensitivity premium proposed i := by
  let actual := waterFillingThreshold weight sensitivity hsensitivity premium
  have hActual : IsWaterFillingThreshold weight sensitivity premium actual :=
    waterFillingThreshold_spec weight sensitivity hsensitivity premium
  rcases le_total proposed actual with hProposedActual | hActualProposed
  · change waterFillAt weight sensitivity premium actual i ≤
      waterFillAt weight sensitivity premium proposed i
    exact waterFillAt_antitone_threshold weight sensitivity premium
      hProposedActual i
  · have hMassLe : waterFillMass weight sensitivity premium proposed ≤
        waterFillMass weight sensitivity premium actual := by
      unfold waterFillMass
      exact Finset.sum_le_sum fun j _ =>
        waterFillAt_antitone_threshold weight sensitivity premium
          hActualProposed j
    have hProposedMass :
        waterFillMass weight sensitivity premium proposed = (weight : ℝ) := by
      exact le_antisymm (hMassLe.trans_eq hActual) hoverfull
    have hProposed :
        IsWaterFillingThreshold weight sensitivity premium proposed :=
      hProposedMass
    exact (waterFillingVector_eq_at_threshold weight sensitivity hsensitivity
      premium hProposed i).le

/-- At the candidate endpoint threshold, clipping is inactive whenever the
whole candidate band fits below one bidder's allocation cap. -/
theorem waterFillMass_endpoint_sub_delta_eq_candidateSlackSum
    {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (premium : ι → ℝ)
    {endpoint delta : ℝ}
    (hupper : ∀ i, premium i ≤ endpoint)
    (hband : (sensitivity : ℝ) * delta ≤ (weight : ℝ)) :
    waterFillMass weight sensitivity premium (endpoint - delta) =
      (sensitivity : ℝ) *
        ∑ i, max (delta - (endpoint - premium i)) 0 := by
  unfold waterFillMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hshortfall : 0 ≤ endpoint - premium i := sub_nonneg.mpr (hupper i)
  by_cases hslack : delta - (endpoint - premium i) ≤ 0
  · rw [max_eq_right hslack, mul_zero]
    apply clampWeight_eq_zero_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos sensitivity.coe_nonneg (by linarith)
  · have hslackNonneg : 0 ≤ delta - (endpoint - premium i) :=
      le_of_not_ge hslack
    rw [max_eq_left hslackNonneg]
    change clampWeight weight
        ((sensitivity : ℝ) * (premium i - (endpoint - delta))) =
      (sensitivity : ℝ) * (delta - (endpoint - premium i))
    rw [show premium i - (endpoint - delta) =
      delta - (endpoint - premium i) by ring]
    apply clampWeight_eq_of_mem
    · exact mul_nonneg sensitivity.coe_nonneg hslackNonneg
    · calc
        (sensitivity : ℝ) * (delta - (endpoint - premium i)) ≤
            (sensitivity : ℝ) * delta :=
          mul_le_mul_of_nonneg_left (by linarith) sensitivity.coe_nonneg
        _ ≤ (weight : ℝ) := hband

/-- Sufficient candidate mass in an endpoint band forces canonical
water-filling loss below `weight * delta`. -/
theorem canonicalOneSlotWaterFillingLoss_le_of_candidateSlackMass
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal)
    (hsensitivity : 0 < sensitivity)
    (premium : ι → ℝ) {endpoint delta : ℝ}
    (hupper : ∀ i, premium i ≤ endpoint)
    (hband : (sensitivity : ℝ) * delta ≤ (weight : ℝ))
    (hcandidate : (weight : ℝ) ≤
      (sensitivity : ℝ) *
        ∑ i, max (delta - (endpoint - premium i)) 0) :
    canonicalOneSlotWaterFillingLoss weight sensitivity hsensitivity premium ≤
      (weight : ℝ) * delta := by
  let proposed : ℝ := endpoint - delta
  have hoverfull : (weight : ℝ) ≤
      waterFillMass weight sensitivity premium proposed := by
    rw [waterFillMass_endpoint_sub_delta_eq_candidateSlackSum
      weight sensitivity premium hupper hband]
    exact hcandidate
  have hdom : ∀ i,
      waterFillingVector weight sensitivity hsensitivity premium i ≤
        waterFillAt weight sensitivity premium proposed i :=
    waterFillingVector_le_at_overfullThreshold
      weight sensitivity hsensitivity premium proposed hoverfull
  have hTop : profileTop premium ≤ endpoint :=
    profileTop_le_of_forall_le premium hupper
  have hSensitivityReal : (0 : ℝ) < (sensitivity : ℝ) := by
    exact_mod_cast hsensitivity
  rw [canonicalOneSlotWaterFillingLoss_eq_sum_gap]
  calc
    (∑ i, waterFillingVector weight sensitivity hsensitivity premium i *
        (profileTop premium - premium i)) ≤
        ∑ i, waterFillingVector weight sensitivity hsensitivity premium i *
          delta := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero :
          waterFillingVector weight sensitivity hsensitivity premium i = 0
      · simp [hzero]
      · have hAllocationPos : 0 <
            waterFillingVector weight sensitivity hsensitivity premium i :=
          lt_of_le_of_ne
            (waterFillingVector_nonneg weight sensitivity hsensitivity premium i)
            (Ne.symm hzero)
        have hProposedPos : 0 <
            waterFillAt weight sensitivity premium proposed i :=
          hAllocationPos.trans_le (hdom i)
        have hRawPos : 0 <
            (sensitivity : ℝ) * (premium i - proposed) := by
          apply lt_of_not_ge
          intro hRawNonpos
          have hzeroRaw := clampWeight_eq_zero_of_nonpos weight hRawNonpos
          unfold waterFillAt at hProposedPos
          rw [hzeroRaw] at hProposedPos
          linarith
        have hPremium : proposed < premium i := by
          nlinarith
        apply mul_le_mul_of_nonneg_left
        · dsimp [proposed] at hPremium
          linarith
        · exact waterFillingVector_nonneg
            weight sensitivity hsensitivity premium i
    _ = (weight : ℝ) * delta := by
      rw [← Finset.sum_mul,
        waterFillingVector_mass weight sensitivity hsensitivity premium]

/-- The canonical loss is integrable for every globally bounded measurable
random premium profile. -/
theorem integrable_canonicalOneSlotWaterFillingLoss
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    {X : ι → Ω → ℝ} {endpoint : ℝ}
    (hX : ∀ i, Measurable (X i))
    (hnonneg : ∀ i ω, 0 ≤ X i ω)
    (hupper : ∀ i ω, X i ω ≤ endpoint) :
    Integrable (fun ω => canonicalOneSlotWaterFillingLoss
      weight sensitivity hsensitivity (fun i => X i ω)) μ := by
  refine Integrable.of_bound
    (measurable_canonicalOneSlotWaterFillingLoss
      weight sensitivity hsensitivity hX).aestronglyMeasurable
    ((weight : ℝ) * endpoint) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg
    (canonicalOneSlotWaterFillingLoss_nonneg
      weight sensitivity hsensitivity (fun i => X i ω))]
  exact canonicalOneSlotWaterFillingLoss_le_endpoint
    weight sensitivity hsensitivity (fun i => X i ω)
      (fun i => hnonneg i ω) (fun i => hupper i ω)

/-! ## A globally bounded representative of the supported profile -/

/-- Clip a real premium to the public interval `[0, endpoint]`. -/
def clipPremium (endpoint value : ℝ) : ℝ := max 0 (min endpoint value)

theorem measurable_clipPremium (endpoint : ℝ) :
    Measurable (clipPremium endpoint) := by
  unfold clipPremium
  fun_prop

theorem clipPremium_nonneg (endpoint value : ℝ) :
    0 ≤ clipPremium endpoint value := by
  exact le_max_left _ _

theorem clipPremium_le_endpoint {endpoint value : ℝ}
    (hendpoint : 0 ≤ endpoint) :
    clipPremium endpoint value ≤ endpoint := by
  unfold clipPremium
  exact max_le hendpoint (min_le_left _ _)

theorem clipPremium_eq_of_mem_Icc {endpoint value : ℝ}
    (hvalue : value ∈ Set.Icc 0 endpoint) :
    clipPremium endpoint value = value := by
  unfold clipPremium
  rw [min_eq_right hvalue.2, max_eq_right hvalue.1]

/-- Coordinate marginal of the i.i.d. finite product law, in real-measure
notation. -/
theorem profileLaw_eval_preimage_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (profileLaw (ι := ι) F).real {profile | profile i ∈ s} = F.real s := by
  have hMeasure : profileLaw (ι := ι) F {profile | profile i ∈ s} = F s := by
    have hmap := (measurePreserving_eval (fun _ : ι => F) i).map_eq
    have hmap' : Measure.map (Function.eval i) (profileLaw (ι := ι) F) = F := by
      simpa [profileLaw] using hmap
    calc
      profileLaw (ι := ι) F {profile | profile i ∈ s} =
          (Measure.map (Function.eval i) (profileLaw (ι := ι) F)) s := by
        rw [Measure.map_apply (measurable_pi_apply i) hs]
        rfl
      _ = F s := by rw [hmap']
  simp only [measureReal_def]
  rw [hMeasure]

/-- Globally bounded profile representative used under the product law. -/
def clippedPremiumProfile
    {ι : Type*} (endpoint : ℝ) (profile : ι → ℝ) : ι → ℝ :=
  fun i => clipPremium endpoint (profile i)

/-- Endpoint shortfall of the clipped profile. -/
def clippedEndpointShortfall
    {ι : Type*} (endpoint : ℝ) (i : ι) : (ι → ℝ) → ℝ :=
  fun profile => endpoint - clipPremium endpoint (profile i)

theorem measurable_clippedEndpointShortfall
    {ι : Type*} (endpoint : ℝ) (i : ι) :
    Measurable (clippedEndpointShortfall endpoint i) := by
  unfold clippedEndpointShortfall
  exact measurable_const.sub ((measurable_clipPremium endpoint).comp
    (measurable_pi_apply i))

theorem clippedEndpointShortfall_nonneg
    {ι : Type*} {endpoint : ℝ} (hendpoint : 0 ≤ endpoint)
    (i : ι) (profile : ι → ℝ) :
    0 ≤ clippedEndpointShortfall endpoint i profile := by
  unfold clippedEndpointShortfall
  exact sub_nonneg.mpr (clipPremium_le_endpoint hendpoint)

/-- The paper's canonical water-filling loss, evaluated on the bounded
representative of a product-law profile. -/
def thickMarketWaterFillingLoss
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (endpoint : ℝ) (profile : ι → ℝ) : ℝ :=
  canonicalOneSlotWaterFillingLoss weight sensitivity hsensitivity
    (clippedPremiumProfile endpoint profile)

theorem measurable_thickMarketWaterFillingLoss
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (endpoint : ℝ) :
    Measurable (thickMarketWaterFillingLoss
      (ι := ι) weight sensitivity hsensitivity endpoint) := by
  apply measurable_canonicalOneSlotWaterFillingLoss
  intro i
  exact (measurable_clipPremium endpoint).comp (measurable_pi_apply i)

theorem integrable_thickMarketWaterFillingLoss
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    {endpoint : ℝ} (hendpoint : 0 ≤ endpoint) :
    Integrable (thickMarketWaterFillingLoss
      (ι := ι) weight sensitivity hsensitivity endpoint)
      (profileLaw (ι := ι) F) := by
  apply integrable_canonicalOneSlotWaterFillingLoss
  · intro i
    exact (measurable_clipPremium endpoint).comp (measurable_pi_apply i)
  · exact fun i profile => clipPremium_nonneg endpoint (profile i)
  · exact fun i profile => clipPremium_le_endpoint hendpoint

/-! ## The finite i.i.d. expected-loss estimate -/

/-- Candidate-mass concentration instantiated with the actual canonical
water-filling loss.  The profile is clipped only off the support; on a law
supported in `[0, endpoint]` this is literally the paper's loss. -/
theorem profileLaw_thickMarketWaterFillingLoss_integral_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    {endpoint delta c z q : ℝ}
    (hendpoint : 0 ≤ endpoint)
    (hdelta : 0 < delta) (hdeltaEndpoint : delta ≤ endpoint)
    (hz : 0 ≤ z)
    (hTail : ∀ x, 0 ≤ x → x ≤ delta →
      c * x ≤ F.real (Set.Ici (endpoint - x)))
    (hband : (sensitivity : ℝ) * delta ≤ (weight : ℝ))
    (hTarget : (weight : ℝ) ≤
      (sensitivity : ℝ) *
        (q * Fintype.card ι * c * delta ^ 2 / 2)) :
    (∫ profile, thickMarketWaterFillingLoss
        (ι := ι) weight sensitivity hsensitivity endpoint profile
      ∂profileLaw (ι := ι) F) ≤
      (weight : ℝ) * delta + (weight : ℝ) * endpoint *
        Real.exp (-(Fintype.card ι * c * delta / 2 *
          (1 - Real.exp (-z) - q * z))) := by
  let Y : ι → (ι → ℝ) → ℝ :=
    fun i => clippedEndpointShortfall endpoint i
  have hY : ∀ i, Measurable (Y i) := fun i =>
    measurable_clippedEndpointShortfall endpoint i
  have hYnonneg : ∀ i profile, 0 ≤ Y i profile := fun i profile =>
    clippedEndpointShortfall_nonneg hendpoint i profile
  have hTailProduct : ∀ i x, 0 ≤ x → x ≤ delta →
      c * x ≤ (profileLaw (ι := ι) F).real
        {profile | Y i profile ≤ x} := by
    intro i x hx0 hxdelta
    have hxEndpoint : x ≤ endpoint := hxdelta.trans hdeltaEndpoint
    have hsubset :
        {profile : ι → ℝ | profile i ∈ Set.Ici (endpoint - x)} ⊆
          {profile | Y i profile ≤ x} := by
      intro profile hprofile
      change endpoint - x ≤ profile i at hprofile
      have hthresholdNonneg : 0 ≤ endpoint - x := by linarith
      have hthresholdLeEndpoint : endpoint - x ≤ endpoint := by linarith
      have hthresholdLeMin : endpoint - x ≤
          min endpoint (profile i) :=
        le_min hthresholdLeEndpoint hprofile
      have hthresholdLeClip : endpoint - x ≤
          clipPremium endpoint (profile i) := by
        exact hthresholdLeMin.trans (le_max_right _ _)
      change Y i profile ≤ x
      dsimp [Y, clippedEndpointShortfall]
      linarith
    calc
      c * x ≤ F.real (Set.Ici (endpoint - x)) :=
        hTail x hx0 hxdelta
      _ = (profileLaw (ι := ι) F).real
          {profile : ι → ℝ | profile i ∈ Set.Ici (endpoint - x)} :=
        (profileLaw_eval_preimage_real F i _ measurableSet_Ici).symm
      _ ≤ (profileLaw (ι := ι) F).real {profile | Y i profile ≤ x} :=
        measureReal_mono hsubset
  have hIndep : iIndepFun Y (profileLaw (ι := ι) F) := by
    have hBase := iIndepFun_pi
      (μ := fun _ : ι => F)
      (X := fun _i : ι => fun value : ℝ =>
        endpoint - clipPremium endpoint value)
      (fun _i => (measurable_const.sub
        (measurable_clipPremium endpoint)).aemeasurable)
    simpa [Y, clippedEndpointShortfall, profileLaw] using hBase
  have hLossInt := integrable_thickMarketWaterFillingLoss
    (ι := ι) F weight sensitivity hsensitivity hendpoint
  have hLossGlobal : ∀ profile,
      thickMarketWaterFillingLoss
          (ι := ι) weight sensitivity hsensitivity endpoint profile ≤
        (weight : ℝ) * endpoint := by
    intro profile
    unfold thickMarketWaterFillingLoss
    exact canonicalOneSlotWaterFillingLoss_le_endpoint
      weight sensitivity hsensitivity (clippedPremiumProfile endpoint profile)
      (fun i => clipPremium_nonneg endpoint (profile i))
      (fun i => clipPremium_le_endpoint hendpoint)
  have hLossGood : ∀ profile,
      (weight : ℝ) ≤ candidateMass (sensitivity : ℝ)
          (fun i => candidateSlack delta (Y i)) profile →
        thickMarketWaterFillingLoss
            (ι := ι) weight sensitivity hsensitivity endpoint profile ≤
          (weight : ℝ) * delta := by
    intro profile hCandidate
    unfold thickMarketWaterFillingLoss
    apply canonicalOneSlotWaterFillingLoss_le_of_candidateSlackMass
      weight sensitivity hsensitivity (clippedPremiumProfile endpoint profile)
      (fun i => clipPremium_le_endpoint hendpoint) hband
    simpa [candidateMass, candidateSlack, Y, clippedEndpointShortfall,
      clippedPremiumProfile] using hCandidate
  exact independent_candidateSlackMass_integral_loss_le
    (μ := profileLaw (ι := ι) F)
    (Y := Y)
    (loss := thickMarketWaterFillingLoss
      (ι := ι) weight sensitivity hsensitivity endpoint)
    (delta := delta) (endpoint := endpoint) (weight := (weight : ℝ))
    (c := c) (z := z) (q := q) (scale := (sensitivity : ℝ))
    (target := (weight : ℝ))
    hdelta hendpoint weight.coe_nonneg hz
    (by exact_mod_cast hsensitivity) hY hYnonneg hTailProduct hIndep
    hTarget hLossInt hLossGlobal hLossGood

/-! ## Square-root scaling -/

/-- Every retained fraction `q < 1` admits a positive Chernoff parameter. -/
theorem exists_positive_candidateMass_chernoffParameter
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ z : ℝ, 0 < z ∧ 0 < 1 - Real.exp (-z) - q * z := by
  let z : ℝ := (1 - q) / (2 * q)
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have hOneAdd : 0 < 1 + z := by linarith
  have hExpInv : Real.exp (-z) < 1 / (1 + z) := by
    have hStrict := Real.add_one_lt_exp (ne_of_gt hz)
    have hStrict' : 1 + z < Real.exp z := by linarith
    have hInv := one_div_lt_one_div_of_lt hOneAdd hStrict'
    simpa [Real.exp_neg] using hInv
  have hqInv : q < 1 / (1 + z) := by
    apply (lt_div_iff₀ hOneAdd).2
    dsimp [z]
    field_simp [ne_of_gt hq0]
    linarith
  refine ⟨z, hz, ?_⟩
  have hqz : q * z < z / (1 + z) := by
    have := mul_lt_mul_of_pos_right hqInv hz
    field_simp [ne_of_gt hOneAdd] at this ⊢
    nlinarith
  have hidentity : 1 - 1 / (1 + z) = z / (1 + z) := by
    field_simp [ne_of_gt hOneAdd]
    ring
  rw [← hidentity] at hqz
  linarith

/-- Expected canonical water-filling loss in an `(n+2)`-bidder market. -/
def expectedThickMarketWaterFillingLoss
    (F : Measure ℝ) (weight sensitivity : NNReal)
    (hsensitivity : 0 < sensitivity) (endpoint : ℝ) (n : ℕ) : ℝ :=
  ∫ profile, thickMarketWaterFillingLoss
      (ι := Fin (n + 2)) weight sensitivity hsensitivity endpoint profile
    ∂profileLaw (ι := Fin (n + 2)) F

/-- The candidate endpoint-band width used in the square-root scaling. -/
def thickMarketBand (C : ℝ) (n : ℕ) : ℝ :=
  C / Real.sqrt ((n + 2 : ℕ) : ℝ)

theorem thickMarketSqrt_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))

theorem thickMarketBand_tendsto_zero (C : ℝ) :
    Tendsto (thickMarketBand C) atTop (𝓝 0) := by
  have hInv : Tendsto
      (fun n : ℕ => (Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp thickMarketSqrt_tendsto_atTop
  change Tendsto
    (fun n : ℕ => C / Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero] using hInv.const_mul C

/-- A fixed retained fraction gives an explicit square-root expected-loss
bound, up to an arbitrarily small remainder. -/
theorem eventually_sqrt_marketSize_mul_expectedWaterFillingLoss_le
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    {endpoint tailConstant tailRadius C q z : ℝ}
    (hendpoint : 0 < endpoint)
    (hTailConstant : 0 < tailConstant)
    (hTailRadius : 0 < tailRadius)
    (hC : 0 < C) (hz : 0 ≤ z)
    (hChernoff : 0 < 1 - Real.exp (-z) - q * z)
    (hTail : ∀ x, 0 ≤ x → x ≤ tailRadius →
      tailConstant * x ≤ F.real (Set.Ici (endpoint - x)))
    (hTarget : (weight : ℝ) ≤
      (sensitivity : ℝ) * (q * tailConstant * C ^ 2 / 2))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n + 2 : ℕ) : ℝ) *
          expectedThickMarketWaterFillingLoss
            F weight sensitivity hsensitivity endpoint n ≤
        (weight : ℝ) * C + epsilon := by
  let B : ℝ := 1 - Real.exp (-z) - q * z
  let rate : ℝ := tailConstant * C / 2 * B
  have hrate : 0 < rate := by
    dsimp [rate, B]
    positivity
  have hDelta := thickMarketBand_tendsto_zero C
  have hDeltaEndpoint := (tendsto_order.mp hDelta).2 endpoint hendpoint
  have hDeltaTail := (tendsto_order.mp hDelta).2 tailRadius hTailRadius
  have hSensitivityReal : (0 : ℝ) < (sensitivity : ℝ) := by
    exact_mod_cast hsensitivity
  have hWeightReal : (0 : ℝ) < (weight : ℝ) := by
    exact_mod_cast hweight
  have hCapPos : 0 < (weight : ℝ) / (sensitivity : ℝ) :=
    div_pos hWeightReal hSensitivityReal
  have hDeltaCap := (tendsto_order.mp hDelta).2
    ((weight : ℝ) / (sensitivity : ℝ)) hCapPos
  have hRemainder : Tendsto
      (fun n : ℕ => (weight : ℝ) * endpoint *
        (Real.sqrt ((n + 2 : ℕ) : ℝ) *
          Real.exp (-rate * Real.sqrt ((n + 2 : ℕ) : ℝ))))
      atTop (𝓝 0) := by
    have hBase := (sqrt_mul_exp_neg_sqrt_tendsto_zero hrate).comp
      (tendsto_add_atTop_nat 2)
    simpa only [mul_zero] using hBase.const_mul ((weight : ℝ) * endpoint)
  have hRemainderSmall := (tendsto_order.mp hRemainder).2 epsilon hepsilon
  filter_upwards [hDeltaEndpoint, hDeltaTail, hDeltaCap, hRemainderSmall]
      with n hEndpointN hTailN hCapN hRemainderN
  let marketSize : ℝ := ((n + 2 : ℕ) : ℝ)
  let rootSize : ℝ := Real.sqrt marketSize
  let delta : ℝ := thickMarketBand C n
  have hMarketSize : 0 < marketSize := by
    dsimp [marketSize]
    positivity
  have hRoot : 0 < rootSize := by
    exact Real.sqrt_pos.2 hMarketSize
  have hRootSquare : rootSize * rootSize = marketSize := by
    dsimp [rootSize]
    exact Real.mul_self_sqrt hMarketSize.le
  have hDeltaPos : 0 < delta := by
    dsimp [delta, thickMarketBand, rootSize, marketSize] at hRoot ⊢
    exact div_pos hC hRoot
  have hDeltaEndpointN : delta ≤ endpoint := hEndpointN.le
  have hDeltaTailN : delta ≤ tailRadius := hTailN.le
  have hBand : (sensitivity : ℝ) * delta ≤ (weight : ℝ) := by
    have := (lt_div_iff₀ hSensitivityReal).1 hCapN
    nlinarith
  have hScaledSquare : marketSize * delta ^ 2 = C ^ 2 := by
    dsimp [delta, thickMarketBand]
    change marketSize * (C / rootSize) ^ 2 = C ^ 2
    field_simp [ne_of_gt hRoot]
    nlinarith [hRootSquare]
  have hTargetN : (weight : ℝ) ≤
      (sensitivity : ℝ) *
        (q * (Fintype.card (Fin (n + 2)) : ℝ) * tailConstant *
          delta ^ 2 / 2) := by
    calc
      (weight : ℝ) ≤
          (sensitivity : ℝ) * (q * tailConstant * C ^ 2 / 2) := hTarget
      _ = (sensitivity : ℝ) *
          (q * (Fintype.card (Fin (n + 2)) : ℝ) * tailConstant *
            delta ^ 2 / 2) := by
        simp only [Fintype.card_fin]
        rw [show ((n + 2 : ℕ) : ℝ) = marketSize by rfl]
        rw [← hScaledSquare]
        ring
  have hFinite := profileLaw_thickMarketWaterFillingLoss_integral_le
    (ι := Fin (n + 2)) F weight sensitivity hsensitivity
    hendpoint.le hDeltaPos hDeltaEndpointN hz
    (fun x hx0 hxdelta => hTail x hx0 (hxdelta.trans hDeltaTailN))
    hBand hTargetN
  have hMarketQuotient : marketSize / rootSize = rootSize := by
    apply (div_eq_iff (ne_of_gt hRoot)).2
    nlinarith [hRootSquare]
  have hExponent :
      (Fintype.card (Fin (n + 2)) : ℝ) * tailConstant * delta / 2 * B =
        rate * rootSize := by
    simp only [Fintype.card_fin]
    rw [show ((n + 2 : ℕ) : ℝ) = marketSize by rfl]
    dsimp [delta, thickMarketBand]
    change marketSize * tailConstant * (C / rootSize) / 2 * B =
      rate * rootSize
    calc
      marketSize * tailConstant * (C / rootSize) / 2 * B =
          (tailConstant * C / 2 * B) * (marketSize / rootSize) := by ring
      _ = rate * rootSize := by rw [hMarketQuotient]
  have hFinite' :
      expectedThickMarketWaterFillingLoss
          F weight sensitivity hsensitivity endpoint n ≤
        (weight : ℝ) * delta + (weight : ℝ) * endpoint *
          Real.exp (-rate * rootSize) := by
    unfold expectedThickMarketWaterFillingLoss
    rw [show B = 1 - Real.exp (-z) - q * z by rfl] at hExponent
    rw [hExponent] at hFinite
    simpa only [neg_mul] using hFinite
  have hScaled := mul_le_mul_of_nonneg_left hFinite' hRoot.le
  calc
    Real.sqrt ((n + 2 : ℕ) : ℝ) *
        expectedThickMarketWaterFillingLoss
          F weight sensitivity hsensitivity endpoint n =
        rootSize * expectedThickMarketWaterFillingLoss
          F weight sensitivity hsensitivity endpoint n := by rfl
    _ ≤ rootSize * ((weight : ℝ) * delta + (weight : ℝ) * endpoint *
          Real.exp (-rate * rootSize)) := hScaled
    _ = (weight : ℝ) * C + (weight : ℝ) * endpoint *
          (rootSize * Real.exp (-rate * rootSize)) := by
      dsimp [delta, thickMarketBand]
      field_simp [ne_of_gt hRoot]
      ring
    _ ≤ (weight : ℝ) * C + epsilon := by
      have hRemainderN' : (weight : ℝ) * endpoint *
          (rootSize * Real.exp (-rate * rootSize)) < epsilon := by
        simpa only [rootSize, marketSize] using hRemainderN
      linarith

/-- Sharp epsilon form of the square-root loss constant.  The retained
fraction in the candidate-mass argument is allowed to approach one, and the
band constant approaches the threshold at which its expected candidate mass
equals the slot weight. -/
theorem eventually_sqrt_marketSize_mul_expectedWaterFillingLoss_le_sharp
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    {endpoint tailConstant tailRadius : ℝ}
    (hendpoint : 0 < endpoint)
    (hTailConstant : 0 < tailConstant)
    (hTailRadius : 0 < tailRadius)
    (hTail : ∀ x, 0 ≤ x → x ≤ tailRadius →
      tailConstant * x ≤ F.real (Set.Ici (endpoint - x)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n + 2 : ℕ) : ℝ) *
          expectedThickMarketWaterFillingLoss
            F weight sensitivity hsensitivity endpoint n ≤
        (weight : ℝ) * Real.sqrt
          (2 * (weight : ℝ) /
            ((sensitivity : ℝ) * tailConstant)) + epsilon := by
  have hWeightReal : (0 : ℝ) < (weight : ℝ) := by
    exact_mod_cast hweight
  have hSensitivityReal : (0 : ℝ) < (sensitivity : ℝ) := by
    exact_mod_cast hsensitivity
  let base : ℝ := Real.sqrt
    (2 * (weight : ℝ) / ((sensitivity : ℝ) * tailConstant))
  have hRadicand : 0 <
      2 * (weight : ℝ) / ((sensitivity : ℝ) * tailConstant) := by
    positivity
  have hBase : 0 < base := by
    dsimp [base]
    exact Real.sqrt_pos.2 hRadicand
  have hBaseSquare : base ^ 2 =
      2 * (weight : ℝ) / ((sensitivity : ℝ) * tailConstant) := by
    dsimp [base]
    exact Real.sq_sqrt hRadicand.le
  let C : ℝ := base + epsilon / (2 * (weight : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hBaseLtC : base < C := by
    dsimp [C]
    have hIncrement : 0 < epsilon / (2 * (weight : ℝ)) := by positivity
    linarith
  let q : ℝ := base ^ 2 / C ^ 2
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hBaseSquareLt : base ^ 2 < C ^ 2 := by
    nlinarith
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one (sq_pos_of_pos hC)).2 hBaseSquareLt
  obtain ⟨z, hz, hChernoff⟩ :=
    exists_positive_candidateMass_chernoffParameter hq0 hq1
  have hqC : q * C ^ 2 = base ^ 2 := by
    dsimp [q]
    field_simp [ne_of_gt hC]
  have hNormalization : (weight : ℝ) =
      (sensitivity : ℝ) * (base ^ 2 * tailConstant / 2) := by
    rw [hBaseSquare]
    field_simp [ne_of_gt hSensitivityReal, ne_of_gt hTailConstant]
  have hTarget : (weight : ℝ) ≤
      (sensitivity : ℝ) * (q * tailConstant * C ^ 2 / 2) := by
    rw [hNormalization]
    rw [show q * tailConstant * C ^ 2 = base ^ 2 * tailConstant by
      nlinarith [hqC]]
  have hGeneric :=
    eventually_sqrt_marketSize_mul_expectedWaterFillingLoss_le
      F weight sensitivity hweight hsensitivity hendpoint hTailConstant
      hTailRadius hC hz.le hChernoff hTail hTarget (half_pos hepsilon)
  filter_upwards [hGeneric] with n hn
  have hConstantIdentity :
      (weight : ℝ) * C + epsilon / 2 =
        (weight : ℝ) * base + epsilon := by
    dsimp [C]
    field_simp [ne_of_gt hWeightReal]
    ring
  rw [hConstantIdentity] at hn
  simpa [base] using hn

theorem expectedThickMarketWaterFillingLoss_nonneg
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal) (hsensitivity : 0 < sensitivity)
    (endpoint : ℝ) (n : ℕ) :
    0 ≤ expectedThickMarketWaterFillingLoss
      F weight sensitivity hsensitivity endpoint n := by
  unfold expectedThickMarketWaterFillingLoss
  apply integral_nonneg
  intro profile
  unfold thickMarketWaterFillingLoss
  exact canonicalOneSlotWaterFillingLoss_nonneg
    weight sensitivity hsensitivity _

/-- Under the bounded-support upper-tail condition, the expected canonical
water-filling loss vanishes. -/
theorem expectedThickMarketWaterFillingLoss_tendsto_zero
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    {endpoint tailConstant tailRadius : ℝ}
    (hendpoint : 0 < endpoint)
    (hTailConstant : 0 < tailConstant)
    (hTailRadius : 0 < tailRadius)
    (hTail : ∀ x, 0 ≤ x → x ≤ tailRadius →
      tailConstant * x ≤ F.real (Set.Ici (endpoint - x))) :
    Tendsto
      (expectedThickMarketWaterFillingLoss
        F weight sensitivity hsensitivity endpoint)
      atTop (𝓝 0) := by
  let bound : ℝ := (weight : ℝ) * Real.sqrt
    (2 * (weight : ℝ) / ((sensitivity : ℝ) * tailConstant)) + 1
  have hRate :=
    eventually_sqrt_marketSize_mul_expectedWaterFillingLoss_le_sharp
      F weight sensitivity hweight hsensitivity hendpoint hTailConstant
      hTailRadius hTail (epsilon := 1) one_pos
  rw [tendsto_order]
  constructor
  · intro lower hlower
    filter_upwards with n
    exact hlower.trans_le
      (expectedThickMarketWaterFillingLoss_nonneg
        F weight sensitivity hsensitivity endpoint n)
  · intro upper hupper
    have hRootLarge := thickMarketSqrt_tendsto_atTop
      (eventually_gt_atTop (bound / upper))
    filter_upwards [hRate, hRootLarge] with n hn hlarge
    have hRoot : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) := by positivity
    have hBoundLt : bound <
        upper * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
      have hscaled := mul_lt_mul_of_pos_left hlarge hupper
      field_simp [ne_of_gt hupper] at hscaled
      simpa [mul_comm] using hscaled
    have hproduct :
        Real.sqrt ((n + 2 : ℕ) : ℝ) *
            expectedThickMarketWaterFillingLoss
              F weight sensitivity hsensitivity endpoint n <
          Real.sqrt ((n + 2 : ℕ) : ℝ) * upper := by
      dsimp [bound] at hn hBoundLt
      nlinarith
    exact lt_of_mul_lt_mul_left hproduct hRoot.le

end

end SmoothingCliff.Racing
