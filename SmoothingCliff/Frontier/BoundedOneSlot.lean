import SmoothingCliff.Frontier.ResponsivenessBudget
import SmoothingCliff.Frontier.WaterFillingProfileLoss

/-!
# The exact bounded one-slot frontier

This file formalizes Proposition `prop:bounded-one-slot` and Corollary
`cor:cheap-latency-price`.  The analytic core is a finite active-set variance
bound: once one active coordinate is the leader, the other active coordinates
must carry the offsetting centered mass.  This turns the exact profile-loss
identity into a one-dimensional truncated quadratic.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff
open SmoothingCliff.Racing

noncomputable section

/-- A global Lipschitz allocation slice makes zero investment a best response
under linear latency cost whenever the value-window certificate is weakly
below marginal cost. -/
theorem linearCost_zero_bestResponse_of_certificate
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ z, 0 ≤ allocation z ∧ allocation z ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {value kappa : ℝ} (hValue : 0 ≤ value)
    (hThreshold : value * (sensitivity : ℝ) ≤ kappa) :
    NonnegativeBestResponse
      (advantageUtility allocation (fun a => kappa * a) 0 value) 0 := by
  let marginal : ℝ → ℝ := fun a =>
    allocation (value + a) - allocation a - kappa
  have hCost : ∀ a : ℝ, HasDerivAt (fun z : ℝ => kappa * z) kappa a := by
    intro a
    simpa using (hasDerivAt_id a).const_mul kappa
  have hHas : ∀ a : ℝ,
      HasDerivAt
        (advantageUtility allocation (fun z => kappa * z) 0 value)
        (marginal a) a := by
    intro a
    simpa [marginal] using advantageUtility_hasDerivAt allocation
      (fun z => kappa * z) hLip.continuous
      (reserve := (0 : ℝ)) (value := value) (advantage := a)
      (marginalCost := kappa) (hCost a)
  have hNonpos : ∀ a : ℝ, marginal a ≤ 0 := by
    intro a
    have hSpread := allocationSpread_bounds allocation weight sensitivity
      hMono hRange hLip (reserve := (0 : ℝ)) (value := value)
        (advantage := a) hValue
    have hUpper := hSpread.2.trans (min_le_right _ _)
    have hUpper' :
        allocation (value + a) - allocation a ≤ value * (sensitivity : ℝ) := by
      simpa using hUpper
    dsimp [marginal]
    linarith
  have hAnti := antitone_of_hasDerivAt_nonpos hHas hNonpos
  refine ⟨le_rfl, ?_⟩
  intro action hAction
  exact hAnti hAction

/-- With strict slack in the same certificate, every positive investment is
strictly worse than zero even for linear latency cost. -/
theorem linearCost_positive_action_strictly_worse
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ z, 0 ≤ allocation z ∧ allocation z ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {value kappa action : ℝ} (hValue : 0 ≤ value) (hAction : 0 < action)
    (hThreshold : value * (sensitivity : ℝ) < kappa) :
    advantageUtility allocation (fun a => kappa * a) 0 value action <
      advantageUtility allocation (fun a => kappa * a) 0 value 0 := by
  let marginal : ℝ → ℝ := fun a =>
    allocation (value + a) - allocation a - kappa
  have hCost : ∀ a : ℝ, HasDerivAt (fun z : ℝ => kappa * z) kappa a := by
    intro a
    simpa using (hasDerivAt_id a).const_mul kappa
  have hHas : ∀ a : ℝ,
      HasDerivAt
        (advantageUtility allocation (fun z => kappa * z) 0 value)
        (marginal a) a := by
    intro a
    simpa [marginal] using advantageUtility_hasDerivAt allocation
      (fun z => kappa * z) hLip.continuous
      (reserve := (0 : ℝ)) (value := value) (advantage := a)
      (marginalCost := kappa) (hCost a)
  have hNeg : ∀ a : ℝ, marginal a < 0 := by
    intro a
    have hSpread := allocationSpread_bounds allocation weight sensitivity
      hMono hRange hLip (reserve := (0 : ℝ)) (value := value)
        (advantage := a) hValue
    have hUpper := hSpread.2.trans (min_le_right _ _)
    have hUpper' :
        allocation (value + a) - allocation a ≤ value * (sensitivity : ℝ) := by
      simpa using hUpper
    dsimp [marginal]
    linarith
  exact (strictAnti_of_hasDerivAt_neg hHas hNeg) hAction

/-- If a nonempty active set contains a distinguished coordinate and has at
least two members, its centered sum of squares is bounded below by the square
of that coordinate times `m/(m-1)`. -/
theorem active_variance_ge_distinguished
    {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (leader : ι) (hLeader : leader ∈ A)
    (hCard : 2 ≤ A.card) (d : ι → ℝ) :
    (A.card : ℝ) / ((A.card : ℝ) - 1) *
        (d leader - activeMean A d) ^ 2 ≤
      ∑ i ∈ A, (d i - activeMean A d) ^ 2 := by
  let μ := activeMean A d
  have hA : A.Nonempty := ⟨leader, hLeader⟩
  have hCenter : ∑ i ∈ A, (d i - μ) = 0 :=
    sum_sub_activeMean_eq_zero A hA d
  have hSplit := Finset.sum_erase_add A (fun i => d i - μ) hLeader
  rw [hCenter] at hSplit
  have hRest : ∑ i ∈ A.erase leader, (d i - μ) = -(d leader - μ) := by
    linarith
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := A.erase leader) (f := fun i => d i - μ)
  rw [hRest] at hCS
  have hEraseCardNat : (A.erase leader).card = A.card - 1 := by
    rw [Finset.card_erase_of_mem hLeader]
  have hEraseCard : ((A.erase leader).card : ℝ) = (A.card : ℝ) - 1 := by
    rw [hEraseCardNat, Nat.cast_sub (by omega : 1 ≤ A.card)]
    norm_num
  rw [hEraseCard] at hCS
  have hCardReal : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hCard
  have hDen : (0 : ℝ) < (A.card : ℝ) - 1 := by linarith
  have hRestLower :
      (d leader - μ) ^ 2 / ((A.card : ℝ) - 1) ≤
        ∑ i ∈ A.erase leader, (d i - μ) ^ 2 := by
    apply (div_le_iff₀ hDen).2
    nlinarith
  have hSquareSplit := Finset.sum_erase_add A
    (fun i => (d i - μ) ^ 2) hLeader
  calc
    (A.card : ℝ) / ((A.card : ℝ) - 1) * (d leader - μ) ^ 2 =
        (d leader - μ) ^ 2 /
            ((A.card : ℝ) - 1) + (d leader - μ) ^ 2 := by
      field_simp [ne_of_gt hDen]
      ring
    _ ≤ (∑ i ∈ A.erase leader, (d i - μ) ^ 2) +
        (d leader - μ) ^ 2 := by linarith
    _ = ∑ i ∈ A, (d i - μ) ^ 2 := hSquareSplit

theorem clampWeight_pos_iff (weight : NNReal) (hweight : 0 < weight) (z : ℝ) :
    0 < clampWeight weight z ↔ 0 < z := by
  simp [clampWeight, Set.coe_projIcc, hweight]

theorem clampWeight_lt_weight_iff
    (weight : NNReal) (hweight : 0 < weight) (z : ℝ) :
    clampWeight weight z < (weight : ℝ) ↔ z < (weight : ℝ) := by
  simp [clampWeight, Set.coe_projIcc, hweight]

/-- The leader-to-trailer gap induced by an active set.  Removing the leader
makes the denominator `m-1` visible, which is the convenient normalization for
the one-dimensional loss bound. -/
def activeGap { ι : Type* } [DecidableEq ι]
    (A : Finset ι) (leader : ι) (d : ι → ℝ) : ℝ :=
  (∑ i ∈ A, (d leader - d i)) / ((A.card : ℝ) - 1)

theorem activeGap_nonneg_le
    {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (leader : ι) (hLeader : leader ∈ A)
    (hCard : 2 ≤ A.card) (d : ι → ℝ) (diameter : ℝ)
    (hLeaderMax : ∀ i ∈ A, d i ≤ d leader)
    (hDiameter : ∀ i ∈ A, d leader - d i ≤ diameter) :
    0 ≤ activeGap A leader d ∧ activeGap A leader d ≤ diameter := by
  have hDen : (0 : ℝ) < (A.card : ℝ) - 1 := by
    have hCardReal : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hCard
    linarith
  have hSumNonneg : 0 ≤ ∑ i ∈ A, (d leader - d i) := by
    exact Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hLeaderMax i hi)
  have hSplit := Finset.sum_erase_add A (fun i => d leader - d i) hLeader
  have hSumErase :
      ∑ i ∈ A, (d leader - d i) =
        ∑ i ∈ A.erase leader, (d leader - d i) := by
    simpa using hSplit.symm
  have hEraseCard : ((A.erase leader).card : ℝ) = (A.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hLeader, Nat.cast_sub (by omega : 1 ≤ A.card)]
    norm_num
  have hSumUpper :
      ∑ i ∈ A, (d leader - d i) ≤
        ((A.card : ℝ) - 1) * diameter := by
    rw [hSumErase, ← hEraseCard]
    calc
      ∑ i ∈ A.erase leader, (d leader - d i) ≤
          ∑ _i ∈ A.erase leader, diameter := by
        apply Finset.sum_le_sum
        intro i hi
        exact hDiameter i (Finset.mem_of_mem_erase hi)
      _ = ((A.erase leader).card : ℝ) * diameter := by
        rw [Finset.sum_const, nsmul_eq_mul]
  constructor
  · unfold activeGap
    exact div_nonneg hSumNonneg hDen.le
  · unfold activeGap
    exact (div_le_iff₀ hDen).2 (by simpa [mul_comm] using hSumUpper)

theorem leader_sub_activeMean_eq_activeGap
    {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (leader : ι) (hCard : 2 ≤ A.card) (d : ι → ℝ) :
    d leader - activeMean A d =
      (((A.card : ℝ) - 1) / (A.card : ℝ)) * activeGap A leader d := by
  have hCardPos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (show 0 < A.card by omega)
  have hDen : (0 : ℝ) < (A.card : ℝ) - 1 := by
    have hCardReal : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hCard
    linarith
  have hConst : ∑ _i ∈ A, d leader = (A.card : ℝ) * d leader := by
    rw [Finset.sum_const, nsmul_eq_mul]
  unfold activeMean activeGap
  rw [Finset.sum_sub_distrib, hConst]
  field_simp [ne_of_gt hCardPos, ne_of_gt hDen]

/-- Every one-slot water-filling loss is controlled by the same truncated
quadratic as a two-block profile.  The witness `delta` is the average
leader-to-trailer gap on the positive active set. -/
theorem waterFillAt_oneSlot_loss_controlled
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight slope : NNReal) (hweight : 0 < weight) (hslope : 0 < slope)
    (d : ι → ℝ) (diameter threshold : ℝ) (leader : ι)
    (hLeaderMax : ∀ i, d i ≤ d leader)
    (hDiameter : ∀ i, d leader - d i ≤ diameter)
    (hMass : ∑ i, waterFillAt weight slope d threshold i = (weight : ℝ)) :
    ∃ delta : ℝ, 0 ≤ delta ∧ delta ≤ diameter ∧
      (weight : ℝ) * d leader -
          ∑ i, d i * waterFillAt weight slope d threshold i ≤
        (1 - 1 / (Fintype.card ι : ℝ)) *
          ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) := by
  classical
  let p : ι → ℝ := waterFillAt weight slope d threshold
  have hp0 : ∀ i, 0 ≤ p i := fun i => clampWeight_nonneg weight _
  have hpw : ∀ i, p i ≤ (weight : ℝ) := fun i => clampWeight_le weight _
  have hWeightReal : (0 : ℝ) < (weight : ℝ) := by exact_mod_cast hweight
  have hSlopeReal : (0 : ℝ) < (slope : ℝ) := by exact_mod_cast hslope
  have hLossEq :
      (weight : ℝ) * d leader - ∑ i, d i * p i =
        ∑ i, p i * (d leader - d i) := by
    change ∑ i, p i = (weight : ℝ) at hMass
    rw [← hMass, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hLossNonneg :
      0 ≤ (weight : ℝ) * d leader - ∑ i, d i * p i := by
    rw [hLossEq]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hp0 i) (sub_nonneg.mpr (hLeaderMax i))
  by_cases hCapped : p leader = (weight : ℝ)
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · have hDiameter0 : 0 ≤ diameter := by
        exact (sub_nonneg.mpr (le_refl (d leader))).trans (hDiameter leader)
      exact hDiameter0
    · have hzero := waterFillAt_loss_eq_zero_of_capped
          weight slope d threshold leader hMass hCapped
      simpa [p] using hzero.le
  · have hpLeaderLt : p leader < (weight : ℝ) :=
      lt_of_le_of_ne (hpw leader) hCapped
    have hRawLeaderLt :
        (slope : ℝ) * (d leader - threshold) < (weight : ℝ) :=
      (clampWeight_lt_weight_iff weight hweight _).mp hpLeaderLt
    have hpLeaderPos : 0 < p leader := by
      by_contra hnot
      have hpLeaderZero : p leader = 0 :=
        le_antisymm (le_of_not_gt hnot) (hp0 leader)
      have hpAllZero : ∀ i, p i = 0 := by
        intro i
        have hRaw :
            (slope : ℝ) * (d i - threshold) ≤
              (slope : ℝ) * (d leader - threshold) := by
          exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hLeaderMax i) threshold)
            slope.coe_nonneg
        have hpLe : p i ≤ p leader := by
          exact clampWeight_monotone weight hRaw
        linarith [hp0 i]
      have hsumZero : ∑ i, p i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hpAllZero i
      change ∑ i, p i = (weight : ℝ) at hMass
      rw [hsumZero] at hMass
      linarith
    let A : Finset ι := Finset.univ.filter (fun i => 0 < p i)
    have hLeaderA : leader ∈ A := by
      simp [A, hpLeaderPos]
    have hInside : ∀ i ∈ A,
        0 < (slope : ℝ) * (d i - threshold) ∧
          (slope : ℝ) * (d i - threshold) < (weight : ℝ) := by
      intro i hi
      have hpPos : 0 < p i := (Finset.mem_filter.mp hi).2
      constructor
      · exact (clampWeight_pos_iff weight hweight _).mp hpPos
      · have hRawLe :
            (slope : ℝ) * (d i - threshold) ≤
              (slope : ℝ) * (d leader - threshold) := by
          exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hLeaderMax i) threshold)
            slope.coe_nonneg
        exact hRawLe.trans_lt hRawLeaderLt
    have hOutside : ∀ i ∉ A,
        (slope : ℝ) * (d i - threshold) ≤ 0 := by
      intro i hi
      have hpNot : ¬ 0 < p i := by simpa [A] using hi
      have hRawNot : ¬ 0 < (slope : ℝ) * (d i - threshold) := by
        intro hRaw
        exact hpNot ((clampWeight_pos_iff weight hweight _).2 hRaw)
      exact le_of_not_gt hRawNot
    have hpOutside : ∀ i ∉ A, p i = 0 := by
      intro i hi
      exact clampWeight_eq_zero_of_nonpos weight (hOutside i hi)
    have hMassA : ∑ i ∈ A, p i = (weight : ℝ) := by
      calc
        ∑ i ∈ A, p i = ∑ i, p i := by
          apply Finset.sum_subset (Finset.subset_univ A)
          intro i hiuniv hiA
          exact hpOutside i hiA
        _ = (weight : ℝ) := by simpa [p] using hMass
    have hActiveCard : 2 ≤ A.card := by
      have hPos : 0 < A.card := Finset.card_pos.mpr ⟨leader, hLeaderA⟩
      by_contra hnot
      have hOne : A.card = 1 := by omega
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hOne
      have hjLeader : j = leader := by
        have : leader ∈ ({j} : Finset ι) := by simpa [hj] using hLeaderA
        exact (by simpa using this : leader = j).symm
      subst j
      rw [hj] at hMassA
      simp only [Finset.sum_singleton] at hMassA
      exact hCapped hMassA
    let delta : ℝ := activeGap A leader d
    have hDeltaBounds : 0 ≤ delta ∧ delta ≤ diameter := by
      exact activeGap_nonneg_le A leader hLeaderA hActiveCard d diameter
        (fun i hi => hLeaderMax i) (fun i hi => hDiameter i)
    have hMean : d leader - activeMean A d =
        (((A.card : ℝ) - 1) / (A.card : ℝ)) * delta := by
      simpa [delta] using
        leader_sub_activeMean_eq_activeGap A leader hActiveCard d
    have hVariance := active_variance_ge_distinguished
      A leader hLeaderA hActiveCard d
    have hCardReal : (0 : ℝ) < (A.card : ℝ) := by
      exact_mod_cast (show 0 < A.card by omega)
    have hCardMinus : (0 : ℝ) < (A.card : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hActiveCard
      linarith
    have hVarianceDelta :
        (((A.card : ℝ) - 1) / (A.card : ℝ)) * delta ^ 2 ≤
          ∑ i ∈ A, (d i - activeMean A d) ^ 2 := by
      calc
        (((A.card : ℝ) - 1) / (A.card : ℝ)) * delta ^ 2 =
            (A.card : ℝ) / ((A.card : ℝ) - 1) *
              ((((A.card : ℝ) - 1) / (A.card : ℝ)) * delta) ^ 2 := by
          field_simp [ne_of_gt hCardReal, ne_of_gt hCardMinus]
        _ = (A.card : ℝ) / ((A.card : ℝ) - 1) *
              (d leader - activeMean A d) ^ 2 := by rw [hMean]
        _ ≤ ∑ i ∈ A, (d i - activeMean A d) ^ 2 := hVariance
    have hLossActive := waterFillAt_active_loss_identity
      A weight slope d threshold leader hLeaderA hInside hOutside hMass
    change
      (weight : ℝ) * d leader - ∑ i, d i * p i =
        (weight : ℝ) * (d leader - activeMean A d) -
          (slope : ℝ) * ∑ i ∈ A, (d i - activeMean A d) ^ 2
      at hLossActive
    have hLossSmall :
        (weight : ℝ) * d leader - ∑ i, d i * p i ≤
          (((A.card : ℝ) - 1) / (A.card : ℝ)) *
            ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) := by
      rw [hLossActive, hMean]
      have hScaled := mul_le_mul_of_nonneg_left hVarianceDelta slope.coe_nonneg
      nlinarith
    have hFactorPos :
        0 < ((A.card : ℝ) - 1) / (A.card : ℝ) :=
      div_pos hCardMinus hCardReal
    have hQuadraticNonneg :
        0 ≤ (weight : ℝ) * delta - (slope : ℝ) * delta ^ 2 := by
      nlinarith
    have hCardLe : A.card ≤ Fintype.card ι := by
      simpa [A] using A.card_le_univ
    have hTotalReal : (0 : ℝ) < (Fintype.card ι : ℝ) := by positivity
    have hFactorLe :
        ((A.card : ℝ) - 1) / (A.card : ℝ) ≤
          ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by
      apply (div_le_div_iff₀ hCardReal hTotalReal).2
      have hCardLeReal : (A.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast hCardLe
      nlinarith
    refine ⟨delta, hDeltaBounds.1, hDeltaBounds.2, hLossSmall.trans ?_⟩
    calc
      (((A.card : ℝ) - 1) / (A.card : ℝ)) *
          ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) ≤
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) *
          ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) :=
        mul_le_mul_of_nonneg_right hFactorLe hQuadraticNonneg
      _ = (1 - 1 / (Fintype.card ι : ℝ)) *
          ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) := by
        field_simp [ne_of_gt hTotalReal]

/-- The two branches of the exact bounded one-slot price. -/
noncomputable def boundedOneSlotPrice
    (n : ℕ) (weight sensitivity diameter : ℝ) : ℝ :=
  if 2 * sensitivity * diameter < weight * (1 - 1 / (n : ℝ)) then
    weight * diameter * (1 - 1 / (n : ℝ)) - sensitivity * diameter ^ 2
  else
    (1 - 1 / (n : ℝ)) ^ 2 * weight ^ 2 / (4 * sensitivity)

theorem boundedOneSlot_quadratic_le_price
    (n : ℕ) (hn : 2 ≤ n)
    (weight sensitivity diameter delta : ℝ)
    (hsensitivity : 0 < sensitivity) (hdelta : delta ≤ diameter) :
    weight * (1 - 1 / (n : ℝ)) * delta - sensitivity * delta ^ 2 ≤
      boundedOneSlotPrice n weight sensitivity diameter := by
  have hnReal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hnPos : (0 : ℝ) < (n : ℝ) := lt_trans (by norm_num) hnReal
  have hFactorPos : 0 < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnPos]
    exact hnReal
  by_cases hLinear :
      2 * sensitivity * diameter < weight * (1 - 1 / (n : ℝ))
  · rw [boundedOneSlotPrice, if_pos hLinear]
    have hGap0 : 0 ≤ diameter - delta := sub_nonneg.mpr hdelta
    have hSlopeGap :
        0 ≤ weight * (1 - 1 / (n : ℝ)) -
          sensitivity * (diameter + delta) := by
      nlinarith
    have hProduct := mul_nonneg hGap0 hSlopeGap
    nlinarith
  · rw [boundedOneSlotPrice, if_neg hLinear]
    have hSquare :=
      sq_nonneg (2 * sensitivity * delta - weight * (1 - 1 / (n : ℝ)))
    apply (le_div_iff₀ (mul_pos (by norm_num) hsensitivity)).2
    nlinarith

/-- Budget-spending water filling obeys the exact bounded two-branch loss
bound on every profile in the premium cube. -/
theorem budgetSpent_waterFillingVector_bounded_loss_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcertificate : 0 < certificate) (diameter : ℝ)
    (d : Fin n → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hdbar : ∀ i, d i ≤ diameter)
    (leader : Fin n) (hLeaderMax : ∀ i, d i ≤ d leader) :
    let slope := budgetSpentSensitivity n certificate
    (weight : ℝ) * d leader -
        ∑ i, d i * waterFillingVector weight slope
          (budgetSpentSensitivity_pos n hn certificate hcertificate) d i ≤
      boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter := by
  dsimp only
  let slope := budgetSpentSensitivity n certificate
  have hslope : 0 < slope := budgetSpentSensitivity_pos n hn certificate hcertificate
  let threshold := waterFillingThreshold weight slope hslope d
  have hMass :
      ∑ i, waterFillAt weight slope d threshold i = (weight : ℝ) := by
    exact waterFillingThreshold_spec weight slope hslope d
  have hDiameter : ∀ i, d leader - d i ≤ diameter := by
    intro i
    linarith [hd0 i, hdbar leader]
  obtain ⟨delta, hdelta0, hdeltaBar, hLoss⟩ :=
    waterFillAt_oneSlot_loss_controlled weight slope hweight hslope d diameter
      threshold leader hLeaderMax hDiameter hMass
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnMinus : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hCoefficient :
      (1 - 1 / (n : ℝ)) * (slope : ℝ) = (certificate : ℝ) := by
    rw [show 1 - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) by
      field_simp [ne_of_gt hnReal]]
    rw [show (slope : ℝ) = (n : ℝ) * (certificate : ℝ) /
        ((n : ℝ) - 1) by simp [slope, budgetSpentSensitivity_coe, hnSub]]
    field_simp [ne_of_gt hnReal, ne_of_gt hnMinus]
  have hRewrite :
      (1 - 1 / (n : ℝ)) *
          ((weight : ℝ) * delta - (slope : ℝ) * delta ^ 2) =
        (weight : ℝ) * (1 - 1 / (n : ℝ)) * delta -
          (certificate : ℝ) * delta ^ 2 := by
    rw [← hCoefficient]
    ring
  have hScalar := boundedOneSlot_quadratic_le_price n hn
    (weight : ℝ) (certificate : ℝ) diameter delta
    (by exact_mod_cast hcertificate) hdeltaBar
  simp only [Fintype.card_fin] at hLoss
  rw [hRewrite] at hLoss
  have hVector : ∀ i,
      waterFillingVector weight slope hslope d i =
        waterFillAt weight slope d threshold i := by
    intro i
    exact waterFillingVector_eq_at_threshold weight slope hslope d hMass i
  calc
    (weight : ℝ) * d leader -
        ∑ i, d i * waterFillingVector weight slope hslope d i =
      (weight : ℝ) * d leader -
        ∑ i, d i * waterFillAt weight slope d threshold i := by
          simp_rw [hVector]
    _ ≤ (weight : ℝ) * (1 - 1 / (n : ℝ)) * delta -
        (certificate : ℝ) * delta ^ 2 := hLoss
    _ ≤ boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter :=
      hScalar

/-- On `n` bidders, the internal slope `n/(n-1)` spends exactly the published
own-coordinate certificate. -/
theorem budgetSpent_waterFillingRule_ownLipschitz
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) {reserve : ℝ}
    (weight certificate : NNReal) (hcertificate : 0 < certificate) :
    OwnLipschitz certificate
      (waterFillingRule (ι := Fin n) (reserve := reserve) weight
        (budgetSpentSensitivity n certificate)
        (budgetSpentSensitivity_pos n hn certificate hcertificate)) := by
  let slope := budgetSpentSensitivity n certificate
  have hslope : 0 < slope := budgetSpentSensitivity_pos n hn certificate hcertificate
  intro b i
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  let br : Fin n → ℝ := fun j => (b j : ℝ)
  have hz : (fun j => ((updateBid b i z) j : ℝ)) =
      Function.update br i (z : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  have hz' : (fun j => ((updateBid b i z') j : ℝ)) =
      Function.update br i (z' : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  change dist (waterFillingVector weight slope hslope
      (fun j => ((updateBid b i z) j : ℝ)) i)
      (waterFillingVector weight slope hslope
        (fun j => ((updateBid b i z') j : ℝ)) i) ≤
    (certificate : ℝ) * dist z z'
  rw [hz, hz']
  have hExact := waterFillingVector_own_lipschitz_exact
    weight slope hslope br i (z : ℝ) (z' : ℝ)
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnMinus : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hCoefficient :
      (slope : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) =
        (certificate : ℝ) := by
    rw [show (slope : ℝ) = (n : ℝ) * (certificate : ℝ) /
        ((n : ℝ) - 1) by simp [slope, budgetSpentSensitivity_coe, hnSub]]
    field_simp [ne_of_gt hnReal, ne_of_gt hnMinus]
  simp only [Fintype.card_fin] at hExact
  rw [hCoefficient] at hExact
  simpa only [Real.dist_eq, Subtype.dist_eq, abs_sub_comm] using hExact

/-- The highest score is the one-selection benchmark. -/
theorem topOneScore_eq_of_isMax
    (n : ℕ) [NeZero n] (hn : 1 ≤ n) (u : Fin n → ℝ) (leader : Fin n)
    (hLeaderMax : ∀ i, u i ≤ u leader) :
    topKScore 1 (by simpa using hn) u = u leader := by
  classical
  obtain ⟨T, hTcard, hTscore⟩ := exists_subsetScore_eq_topKScore 1
    (by simpa using hn) u
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hTcard
  have hUpper : topKScore 1 (by simpa using hn) u ≤
      u leader := by
    rw [← hTscore, hj]
    simpa [subsetScore] using hLeaderMax j
  have hLower : u leader ≤
      topKScore 1 (by simpa using hn) u := by
    have h := subsetScore_le_topKScore 1
      (by simpa using hn) u ({leader} : Finset (Fin n))
      (by simp)
    simpa [subsetScore] using h
  exact le_antisymm hUpper hLower

/-- Premium profile with bidder `0` at `delta` and every other bidder at the
reserve, normalized to reserve zero. -/
def oneLeaderPremiumProfile
    (n : ℕ) [NeZero n] (delta : ℝ) (hdelta : 0 ≤ delta) :
    EligibleProfile (Fin n) 0 :=
  updateBid (tiedEligibleProfile 0) 0 ⟨delta, hdelta⟩

@[simp] theorem oneLeaderPremiumProfile_zero
    (n : ℕ) [NeZero n] (delta : ℝ) (hdelta : 0 ≤ delta) :
    ((oneLeaderPremiumProfile n delta hdelta 0 : EligibleBid 0) : ℝ) = delta := by
  simp [oneLeaderPremiumProfile, updateBid]

theorem oneLeaderPremiumProfile_ne_zero
    (n : ℕ) [NeZero n] (delta : ℝ) (hdelta : 0 ≤ delta)
    (i : Fin n) (hi : i ≠ 0) :
    ((oneLeaderPremiumProfile n delta hdelta i : EligibleBid 0) : ℝ) = 0 := by
  simp [oneLeaderPremiumProfile, updateBid, tiedEligibleProfile, hi]

/-- A one-leader profile gives the universal quadratic lower certificate at
every gap, not only at the unconstrained optimizer. -/
theorem oneLeader_certified_loss_lower
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal)
    (x : InterimRule (Fin n) 0)
    (hAnon : Anonymous x) (hLipschitz : OwnLipschitz certificate x)
    (hFeasible : OneSlotFeasible (weight : ℝ) x)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    delta * ((weight : ℝ) * (1 - 1 / (n : ℝ)) -
        (certificate : ℝ) * delta) ≤
      (weight : ℝ) * delta -
        welfare x (oneLeaderPremiumProfile n delta hdelta) := by
  let b0 : EligibleProfile (Fin n) 0 := tiedEligibleProfile 0
  let bDelta : EligibleProfile (Fin n) 0 := oneLeaderPremiumProfile n delta hdelta
  let high : EligibleBid 0 := ⟨delta, hdelta⟩
  have hTie : x b0 0 ≤ (weight : ℝ) / (n : ℝ) := by
    simpa [b0] using
      anonymous_tie_allocation_le_card x hAnon hFeasible (0 : Fin n)
  have hUpdateZero : updateBid b0 0 (b0 0) = b0 := by
    funext i
    apply Subtype.ext
    by_cases hi : i = 0 <;> simp [updateBid, Function.update, hi]
  have hUpdateHigh : updateBid b0 0 high = bDelta := by
    rfl
  have hLip := (hLipschitz b0 0).dist_le_mul (b0 0) high
  rw [hUpdateZero, hUpdateHigh] at hLip
  have hDist : dist (b0 0) high = delta := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |0 - delta| = delta
    rw [zero_sub, abs_neg, abs_of_nonneg hdelta]
  rw [hDist] at hLip
  have hDiff : x bDelta 0 - x b0 0 ≤ dist (x b0 0) (x bDelta 0) := by
    rw [Real.dist_eq, abs_sub_comm]
    exact le_abs_self _
  have hLeaderAllocation :
      x bDelta 0 ≤ (weight : ℝ) / (n : ℝ) +
        (certificate : ℝ) * delta := by
    linarith
  have hWelfare : welfare x bDelta = delta * x bDelta 0 := by
    unfold welfare
    have hPoint : ∀ i : Fin n,
        ((bDelta i : EligibleBid 0) : ℝ) * x bDelta i =
          if i = (0 : Fin n) then delta * x bDelta 0 else 0 := by
      intro i
      by_cases hi : i = (0 : Fin n)
      · subst i
        rw [show ((bDelta (0 : Fin n) : EligibleBid 0) : ℝ) = delta by
          change ((oneLeaderPremiumProfile n delta hdelta 0 : EligibleBid 0) : ℝ) = delta
          exact oneLeaderPremiumProfile_zero n delta hdelta]
        simp
      · rw [show ((bDelta i : EligibleBid 0) : ℝ) = 0 by
          change ((oneLeaderPremiumProfile n delta hdelta i : EligibleBid 0) : ℝ) = 0
          exact oneLeaderPremiumProfile_ne_zero n delta hdelta i hi]
        simp [hi]
    calc
      ∑ i, ((bDelta i : EligibleBid 0) : ℝ) * x bDelta i =
          ∑ i : Fin n, if i = (0 : Fin n) then delta * x bDelta 0 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hPoint i
      _ = delta * x bDelta 0 := by simp
  change delta * ((weight : ℝ) * (1 - 1 / (n : ℝ)) -
      (certificate : ℝ) * delta) ≤
    (weight : ℝ) * delta - welfare x bDelta
  rw [hWelfare]
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hScaled := mul_le_mul_of_nonneg_left hLeaderAllocation hdelta
  field_simp [ne_of_gt hnReal] at hScaled ⊢
  nlinarith

/-- The paper's certified one-slot class on the normalized premium domain. -/
def IsBoundedOneSlotCertifiedRule
    (n : ℕ) (weight : ℝ) (certificate : NNReal)
    (x : InterimRule (Fin n) 0) : Prop :=
  Anonymous x ∧ OwnMonotone x ∧ OwnLipschitz certificate x ∧
    OneSlotFeasible weight x

def InBoundedPremiumCube
    {n : ℕ} (diameter : ℝ) (b : EligibleProfile (Fin n) 0) : Prop :=
  ∀ i, (b i : ℝ) ≤ diameter

def HasBoundedOneSlotRegretBound
    (n : ℕ) (hn : 1 ≤ n) (weight diameter : ℝ)
    (x : InterimRule (Fin n) 0) (R : ℝ) : Prop :=
  ∀ b, InBoundedPremiumCube diameter b →
    weight * topKScore 1 (by simpa using hn) (fun i => (b i : ℝ)) -
      welfare x b ≤ R

/-- Literal infimum over all uniform regret bounds on `[0,diameter]^n`. -/
noncomputable def boundedOneSlotFrontier
    (n : ℕ) (hn : 1 ≤ n) (weight diameter : ℝ) (certificate : NNReal) : ℝ :=
  sInf {R : ℝ | ∃ x : InterimRule (Fin n) 0,
    IsBoundedOneSlotCertifiedRule n weight certificate x ∧
      HasBoundedOneSlotRegretBound n hn weight diameter x R}

noncomputable def budgetSpentOneSlotRule
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate) :
    InterimRule (Fin n) 0 :=
  waterFillingRule weight (budgetSpentSensitivity n certificate)
    (budgetSpentSensitivity_pos n hn certificate hcertificate)

theorem budgetSpentOneSlotRule_certificate
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcertificate : 0 < certificate) (diameter : ℝ) :
    IsBoundedOneSlotCertifiedRule n (weight : ℝ) certificate
        (budgetSpentOneSlotRule n hn weight certificate hcertificate) ∧
      HasBoundedOneSlotRegretBound n (by omega) (weight : ℝ) diameter
        (budgetSpentOneSlotRule n hn weight certificate hcertificate)
        (boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter) := by
  let slope := budgetSpentSensitivity n certificate
  have hslope : 0 < slope := budgetSpentSensitivity_pos n hn certificate hcertificate
  have hMembership := waterFillingRule_membership
    (ι := Fin n) (reserve := (0 : ℝ))
      (weight := weight) (sensitivity := slope) hslope
  constructor
  · exact ⟨hMembership.1, hMembership.2.1,
      budgetSpent_waterFillingRule_ownLipschitz n hn weight certificate hcertificate,
      hMembership.2.2.2.2.1⟩
  · intro b hb
    let d : Fin n → ℝ := fun i => (b i : ℝ)
    obtain ⟨leader, hLeader⟩ := Finite.exists_max d
    have hd0 : ∀ i, 0 ≤ d i := fun i => (b i).2
    have hdbar : ∀ i, d i ≤ diameter := hb
    have hLoss := budgetSpent_waterFillingVector_bounded_loss_le n hn
      weight certificate hweight hcertificate diameter d hd0 hdbar leader hLeader
    have hTop := topOneScore_eq_of_isMax n (by omega) d leader hLeader
    have hTop' :
        topKScore 1 (by simpa using (show 1 ≤ n by omega))
            (fun i => (b i : ℝ)) = d leader := by
      simpa [d] using hTop
    dsimp only at hLoss
    unfold budgetSpentOneSlotRule
    unfold welfare
    rw [hTop']
    simpa [d, slope] using hLoss

theorem oneLeaderPremiumProfile_mem_cube
    (n : ℕ) [NeZero n] (delta diameter : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ diameter) :
    InBoundedPremiumCube diameter (oneLeaderPremiumProfile n delta hdelta0) := by
  intro i
  by_cases hi : i = (0 : Fin n)
  · subst i
    rw [oneLeaderPremiumProfile_zero]
    exact hdelta
  · rw [oneLeaderPremiumProfile_ne_zero n delta hdelta0 i hi]
    exact hdelta0.trans hdelta

theorem oneLeaderPremiumProfile_topScore
    (n : ℕ) [NeZero n] (hn : 1 ≤ n) (delta : ℝ) (hdelta : 0 ≤ delta) :
    topKScore 1 (by simpa using hn)
        (fun i => ((oneLeaderPremiumProfile n delta hdelta i : EligibleBid 0) : ℝ)) =
      delta := by
  have hLeader : ∀ i : Fin n,
      ((oneLeaderPremiumProfile n delta hdelta i : EligibleBid 0) : ℝ) ≤
        ((oneLeaderPremiumProfile n delta hdelta 0 : EligibleBid 0) : ℝ) := by
    intro i
    by_cases hi : i = (0 : Fin n)
    · subst i
      exact le_rfl
    · rw [oneLeaderPremiumProfile_ne_zero n delta hdelta i hi,
          oneLeaderPremiumProfile_zero]
      exact hdelta
  rw [topOneScore_eq_of_isMax n hn _ 0 hLeader,
    oneLeaderPremiumProfile_zero]

/-- Every certified rule pays at least the displayed bounded price on one of
the two one-leader profiles. -/
theorem boundedOneSlot_uniform_lower
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcertificate : 0 < certificate) (diameter : ℝ) (hdiameter : 0 < diameter)
    (x : InterimRule (Fin n) 0)
    (hx : IsBoundedOneSlotCertifiedRule n (weight : ℝ) certificate x)
    (R : ℝ)
    (hR : HasBoundedOneSlotRegretBound n (by omega)
      (weight : ℝ) diameter x R) :
    boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter ≤ R := by
  have hWeightReal : (0 : ℝ) < (weight : ℝ) := by exact_mod_cast hweight
  have hCertificateReal : (0 : ℝ) < (certificate : ℝ) := by
    exact_mod_cast hcertificate
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hFactorPos : 0 < 1 - 1 / (n : ℝ) := by
    rw [sub_pos, div_lt_one hnReal]
    exact hnOne
  by_cases hLinear :
      2 * (certificate : ℝ) * diameter <
        (weight : ℝ) * (1 - 1 / (n : ℝ))
  · let b := oneLeaderPremiumProfile n diameter hdiameter.le
    have hb := oneLeaderPremiumProfile_mem_cube n diameter diameter
      hdiameter.le le_rfl
    have hRegret := hR b hb
    have hTop := oneLeaderPremiumProfile_topScore n (by omega)
      diameter hdiameter.le
    have hLower := oneLeader_certified_loss_lower n hn weight certificate x
      hx.1 hx.2.2.1 hx.2.2.2 diameter hdiameter.le
    rw [hTop] at hRegret
    have hRegret' :
        (weight : ℝ) * diameter - welfare x b ≤ R := by
      simpa [b] using hRegret
    rw [boundedOneSlotPrice, if_pos hLinear]
    calc
      (weight : ℝ) * diameter * (1 - 1 / (n : ℝ)) -
          (certificate : ℝ) * diameter ^ 2 =
        diameter * ((weight : ℝ) * (1 - 1 / (n : ℝ)) -
          (certificate : ℝ) * diameter) := by ring
      _ ≤ (weight : ℝ) * diameter - welfare x b := by simpa [b] using hLower
      _ ≤ R := hRegret'
  · let delta : ℝ :=
        (weight : ℝ) * (1 - 1 / (n : ℝ)) / (2 * (certificate : ℝ))
    have hdelta0 : 0 ≤ delta := by
      dsimp [delta]
      positivity
    have hdelta : delta ≤ diameter := by
      have hNumerator :
          (weight : ℝ) * (1 - 1 / (n : ℝ)) ≤
            2 * (certificate : ℝ) * diameter := le_of_not_gt hLinear
      dsimp [delta]
      exact (div_le_iff₀ (mul_pos (by norm_num) hCertificateReal)).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hNumerator)
    let b := oneLeaderPremiumProfile n delta hdelta0
    have hb := oneLeaderPremiumProfile_mem_cube n delta diameter hdelta0 hdelta
    have hRegret := hR b hb
    have hTop := oneLeaderPremiumProfile_topScore n (by omega) delta hdelta0
    have hLower := oneLeader_certified_loss_lower n hn weight certificate x
      hx.1 hx.2.2.1 hx.2.2.2 delta hdelta0
    rw [hTop] at hRegret
    have hRegret' :
        (weight : ℝ) * delta - welfare x b ≤ R := by
      simpa [b] using hRegret
    have hOptimizer :
        delta * ((weight : ℝ) * (1 - 1 / (n : ℝ)) -
            (certificate : ℝ) * delta) =
          (1 - 1 / (n : ℝ)) ^ 2 * (weight : ℝ) ^ 2 /
            (4 * (certificate : ℝ)) := by
      dsimp [delta]
      field_simp [ne_of_gt hCertificateReal]
      ring
    rw [boundedOneSlotPrice, if_neg hLinear, ← hOptimizer]
    exact hLower.trans (by simpa [b] using hRegret')

/-- Proposition `prop:bounded-one-slot`: literal minimax equality together
with an admissible water-filling rule attaining the uniform bound. -/
theorem boundedOneSlotFrontier_exact
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcertificate : 0 < certificate) (diameter : ℝ) (hdiameter : 0 < diameter) :
    boundedOneSlotFrontier n (by omega) (weight : ℝ) diameter certificate =
        boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter ∧
      IsBoundedOneSlotCertifiedRule n (weight : ℝ) certificate
        (budgetSpentOneSlotRule n hn weight certificate hcertificate) ∧
      HasBoundedOneSlotRegretBound n (by omega) (weight : ℝ) diameter
        (budgetSpentOneSlotRule n hn weight certificate hcertificate)
        (boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter) := by
  let price := boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) diameter
  let rule := budgetSpentOneSlotRule n hn weight certificate hcertificate
  let bounds : Set ℝ := {R : ℝ | ∃ x : InterimRule (Fin n) 0,
    IsBoundedOneSlotCertifiedRule n (weight : ℝ) certificate x ∧
      HasBoundedOneSlotRegretBound n (by omega) (weight : ℝ) diameter x R}
  have hRule := budgetSpentOneSlotRule_certificate n hn weight certificate
    hweight hcertificate diameter
  have hPriceMem : price ∈ bounds := by
    exact ⟨rule, hRule⟩
  have hNonempty : bounds.Nonempty := ⟨price, hPriceMem⟩
  have hLower : ∀ R ∈ bounds, price ≤ R := by
    intro R hR
    rcases hR with ⟨x, hx, hxR⟩
    exact boundedOneSlot_uniform_lower n hn weight certificate hweight
      hcertificate diameter hdiameter x hx R hxR
  have hEquality : sInf bounds = price := by
    apply le_antisymm
    · exact csInf_le ⟨price, hLower⟩ hPriceMem
    · exact le_csInf hNonempty hLower
  refine ⟨?_, hRule⟩
  change sInf bounds = price
  exact hEquality

/-! ## The incentive-defined cheap-latency frontier -/

/-- A boundary-regular implementation witness for zero investment on the
bounded premium cube. -/
def IsBoundedZeroInvestmentRule
    (n : ℕ) (weight kappa diameter : ℝ)
    (x : InterimRule (Fin n) 0) : Prop :=
  Anonymous x ∧ OwnMonotone x ∧ CrossMonotone x ∧
    OneSlotFeasible weight x ∧
    ∃ slice : EligibleProfile (Fin n) 0 → Fin n → ℝ → ℝ,
      (∀ b i, Continuous (slice b i)) ∧
      (∀ b i, slice b i (b i) = x b i) ∧
      (∀ b i, slice b i 0 =
        x (updateBid b i ⟨0, Set.mem_Ici.mpr le_rfl⟩) i) ∧
      ∀ b, InBoundedPremiumCube diameter b → ∀ i,
        NonnegativeBestResponse
          (advantageUtility (slice b i) (fun a => kappa * a) 0 (b i)) 0

/-- The responsiveness cap localized to the bounded cube used by the
incentive-defined class. -/
theorem boundedZeroInvestment_responsiveness
    (n : ℕ) [NeZero n]
    (weight kappa diameter : ℝ) (x : InterimRule (Fin n) 0)
    (hx : IsBoundedZeroInvestmentRule n weight kappa diameter x)
    (b : EligibleProfile (Fin n) 0) (hb : InBoundedPremiumCube diameter b)
    (i : Fin n) :
    x b i ≤ weight / (n : ℝ) + kappa := by
  rcases hx.2.2.2.2 with ⟨slice, hContinuous, hValue, hReserve, hBest⟩
  have hSpread := zeroBestResponse_allocationSpread_le
    (slice b i) (hContinuous b i) (hBest b hb i)
  rw [hValue b i, hReserve b i] at hSpread
  have hCrossBase :
      x (updateBid b i ⟨0, Set.mem_Ici.mpr le_rfl⟩) i ≤
        x (tiedEligibleProfile 0) i := by
    rw [← opponentsRaisedProfile_univ_erase b i]
    exact opponentsRaisedProfile_allocation_le_tie x hx.2.2.1 b i
      ((Finset.univ : Finset (Fin n)).erase i) (by simp)
  have hTie := anonymous_tie_allocation_le_card x hx.1 hx.2.2.2.1 i
  simp only [Fintype.card_fin] at hTie
  linarith

/-- Literal minimax price over the full incentive-defined class, without a
Lipschitz restriction in its definition. -/
noncomputable def zeroInvestmentFrontier
    (n : ℕ) (hn : 1 ≤ n) (weight kappa diameter : ℝ) : ℝ :=
  sInf {R : ℝ | ∃ x : InterimRule (Fin n) 0,
    IsBoundedZeroInvestmentRule n weight kappa diameter x ∧
      HasBoundedOneSlotRegretBound n hn weight diameter x R}

def cheapLatencyPrice (n : ℕ) (weight kappa diameter : ℝ) : ℝ :=
  weight * diameter * (1 - 1 / (n : ℝ)) - kappa * diameter

/-- The real-line own-bid slice of the budget-spending one-slot water-filling
rule.  Extending the slice to all real scores lets the latency utility be
treated by ordinary one-dimensional calculus. -/
noncomputable def budgetSpentOneSlotSlice
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) (z : ℝ) : ℝ :=
  waterFillingVector weight (budgetSpentSensitivity n certificate)
    (budgetSpentSensitivity_pos n hn certificate hcertificate)
    (Function.update (fun j => (b j : ℝ)) i z) i

theorem budgetSpentOneSlotSlice_monotone
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) :
    Monotone (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i) := by
  intro z z' hzz'
  let raw : Fin n → ℝ := fun j => (b j : ℝ)
  let slope := budgetSpentSensitivity n certificate
  have hslope : 0 < slope :=
    budgetSpentSensitivity_pos n hn certificate hcertificate
  have hMono := waterFillingVector_own_monotone weight slope hslope
    (Function.update raw i z) i (z := z') (by simpa using hzz')
  simpa [budgetSpentOneSlotSlice, raw, slope, Function.update] using hMono

/-- The real-line slice has exactly the published finite-population
certificate as a global Lipschitz bound. -/
theorem budgetSpentOneSlotSlice_lipschitz
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) :
    LipschitzWith certificate
      (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i) := by
  let raw : Fin n → ℝ := fun j => (b j : ℝ)
  let slope := budgetSpentSensitivity n certificate
  have hslope : 0 < slope :=
    budgetSpentSensitivity_pos n hn certificate hcertificate
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  have hExact := waterFillingVector_own_lipschitz_exact
    weight slope hslope raw i z z'
  have hnReal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hnMinus : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    linarith
  have hCoefficient :
      (slope : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) =
        (certificate : ℝ) := by
    rw [show (slope : ℝ) = (n : ℝ) * (certificate : ℝ) /
        ((n : ℝ) - 1) by simp [slope, budgetSpentSensitivity_coe, hnSub]]
    field_simp [ne_of_gt hnReal, ne_of_gt hnMinus]
  simp only [Fintype.card_fin] at hExact
  rw [hCoefficient] at hExact
  simpa only [budgetSpentOneSlotSlice, raw, slope, Real.dist_eq,
    abs_sub_comm] using hExact

theorem budgetSpentOneSlotSlice_range
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) (z : ℝ) :
    0 ≤ budgetSpentOneSlotSlice n hn weight certificate hcertificate b i z ∧
      budgetSpentOneSlotSlice n hn weight certificate hcertificate b i z ≤
        (weight : ℝ) := by
  exact ⟨waterFillingVector_nonneg _ _ _ _ _,
    waterFillingVector_le _ _ _ _ _⟩

theorem budgetSpentOneSlotSlice_self
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) :
    budgetSpentOneSlotSlice n hn weight certificate hcertificate b i (b i) =
      budgetSpentOneSlotRule n hn weight certificate hcertificate b i := by
  simp [budgetSpentOneSlotSlice, budgetSpentOneSlotRule, waterFillingRule]

theorem budgetSpentOneSlotSlice_reserve
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (b : EligibleProfile (Fin n) 0) (i : Fin n) :
    budgetSpentOneSlotSlice n hn weight certificate hcertificate b i 0 =
      budgetSpentOneSlotRule n hn weight certificate hcertificate
        (updateBid b i ⟨0, Set.mem_Ici.mpr le_rfl⟩) i := by
  unfold budgetSpentOneSlotSlice budgetSpentOneSlotRule waterFillingRule
  congr 1
  funext j
  by_cases hji : j = i <;> simp [updateBid, Function.update, hji]

/-- If the published responsiveness budget satisfies
`certificate * diameter ≤ kappa`, the budget-spending water-filling rule
implements zero latency investment throughout the bounded premium cube. -/
theorem budgetSpentOneSlotRule_zeroInvestment
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (kappa diameter : ℝ)
    (hBudget : (certificate : ℝ) * diameter ≤ kappa) :
    IsBoundedZeroInvestmentRule n (weight : ℝ) kappa diameter
      (budgetSpentOneSlotRule n hn weight certificate hcertificate) := by
  let rule := budgetSpentOneSlotRule n hn weight certificate hcertificate
  let slice : EligibleProfile (Fin n) 0 → Fin n → ℝ → ℝ :=
    budgetSpentOneSlotSlice n hn weight certificate hcertificate
  have hMembership := waterFillingRule_membership
    (ι := Fin n) (reserve := (0 : ℝ))
      (weight := weight) (sensitivity := budgetSpentSensitivity n certificate)
      (budgetSpentSensitivity_pos n hn certificate hcertificate)
  refine ⟨hMembership.1, hMembership.2.1, hMembership.2.2.2.1,
    hMembership.2.2.2.2.1, slice, ?_, ?_, ?_, ?_⟩
  · intro b i
    exact (budgetSpentOneSlotSlice_lipschitz n hn weight certificate
      hcertificate b i).continuous
  · intro b i
    exact budgetSpentOneSlotSlice_self n hn weight certificate hcertificate b i
  · intro b i
    exact budgetSpentOneSlotSlice_reserve n hn weight certificate
      hcertificate b i
  · intro b hb i
    apply linearCost_zero_bestResponse_of_certificate
      (slice b i) weight certificate
      (budgetSpentOneSlotSlice_monotone n hn weight certificate
        hcertificate b i)
      (budgetSpentOneSlotSlice_range n hn weight certificate
        hcertificate b i)
      (budgetSpentOneSlotSlice_lipschitz n hn weight certificate
        hcertificate b i)
      (b i).2
    have hScaled := mul_le_mul_of_nonneg_right (hb i) certificate.coe_nonneg
    calc
      (b i : ℝ) * (certificate : ℝ) ≤
          diameter * (certificate : ℝ) := hScaled
      _ = (certificate : ℝ) * diameter := by ring
      _ ≤ kappa := hBudget

/-- Strict slack in the responsiveness budget makes every positive latency
investment strictly worse than zero, uniformly over the bounded cube. -/
theorem budgetSpentOneSlotRule_strictNoRace
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight certificate : NNReal) (hcertificate : 0 < certificate)
    (kappa diameter : ℝ)
    (hBudget : (certificate : ℝ) * diameter < kappa)
    (b : EligibleProfile (Fin n) 0) (hb : InBoundedPremiumCube diameter b)
    (i : Fin n) (action : ℝ) (haction : 0 < action) :
    advantageUtility
        (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i)
        (fun a => kappa * a) 0 (b i) action <
      advantageUtility
        (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i)
        (fun a => kappa * a) 0 (b i) 0 := by
  apply linearCost_positive_action_strictly_worse
    (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i)
    weight certificate
    (budgetSpentOneSlotSlice_monotone n hn weight certificate
      hcertificate b i)
    (budgetSpentOneSlotSlice_range n hn weight certificate
      hcertificate b i)
    (budgetSpentOneSlotSlice_lipschitz n hn weight certificate
      hcertificate b i)
    (b i).2 haction
  have hScaled := mul_le_mul_of_nonneg_right (hb i) certificate.coe_nonneg
  calc
    (b i : ℝ) * (certificate : ℝ) ≤
        diameter * (certificate : ℝ) := hScaled
    _ = (certificate : ℝ) * diameter := by ring
    _ < kappa := hBudget

theorem oneLeaderPremiumProfile_welfare
    (n : ℕ) [NeZero n] (x : InterimRule (Fin n) 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    welfare x (oneLeaderPremiumProfile n delta hdelta) =
      delta * x (oneLeaderPremiumProfile n delta hdelta) 0 := by
  unfold welfare
  apply Finset.sum_eq_single 0
  · intro i hi hi0
    rw [show (((oneLeaderPremiumProfile n delta hdelta) i : EligibleBid 0) : ℝ) =
        0 by exact oneLeaderPremiumProfile_ne_zero n delta hdelta i hi0]
    simp
  · simp

/-- The one-leader endpoint converts the responsiveness budget into a
universal welfare lower bound for every zero-investment implementation. -/
theorem zeroInvestment_uniform_lower
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight kappa diameter : ℝ) (hdiameter : 0 ≤ diameter)
    (x : InterimRule (Fin n) 0)
    (hx : IsBoundedZeroInvestmentRule n weight kappa diameter x)
    (R : ℝ)
    (hR : HasBoundedOneSlotRegretBound n (by omega)
      weight diameter x R) :
    cheapLatencyPrice n weight kappa diameter ≤ R := by
  let b := oneLeaderPremiumProfile n diameter hdiameter
  have hb : InBoundedPremiumCube diameter b :=
    oneLeaderPremiumProfile_mem_cube n diameter diameter hdiameter le_rfl
  have hAllocation := boundedZeroInvestment_responsiveness n
    weight kappa diameter x hx b hb 0
  have hScaled := mul_le_mul_of_nonneg_left hAllocation hdiameter
  have hRegret := hR b hb
  have hTop := oneLeaderPremiumProfile_topScore n (by omega)
    diameter hdiameter
  have hWelfare := oneLeaderPremiumProfile_welfare n x diameter hdiameter
  rw [hTop] at hRegret
  have hRegret' :
      weight * diameter - diameter * x b 0 ≤ R := by
    simpa [b, hWelfare] using hRegret
  calc
    cheapLatencyPrice n weight kappa diameter =
        weight * diameter - diameter * (weight / (n : ℝ) + kappa) := by
          unfold cheapLatencyPrice
          ring
    _ ≤ weight * diameter - diameter * x b 0 :=
      sub_le_sub_left hScaled _
    _ ≤ R := hRegret'

/-- Corollary `cor:cheap-latency-price`: in the cheap-latency regime, the
literal minimax price over the full incentive-defined class equals the linear
responsiveness price.  No Lipschitz condition appears in the class defining
the infimum; budget-spending water-filling supplies an attaining rule. -/
theorem cheapLatencyFrontier_exact
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight kappa diameter : NNReal)
    (hweight : 0 < weight) (hkappa : 0 < kappa)
    (hdiameter : 0 < diameter)
    (hCheap : 2 * (kappa : ℝ) <
      (weight : ℝ) * (1 - 1 / (n : ℝ))) :
    let certificate : NNReal := kappa / diameter
    zeroInvestmentFrontier n (by omega) (weight : ℝ) (kappa : ℝ)
          (diameter : ℝ) =
        cheapLatencyPrice n (weight : ℝ) (kappa : ℝ) (diameter : ℝ) ∧
      IsBoundedZeroInvestmentRule n (weight : ℝ) (kappa : ℝ) (diameter : ℝ)
        (budgetSpentOneSlotRule n hn weight certificate (div_pos hkappa hdiameter)) ∧
      HasBoundedOneSlotRegretBound n (by omega) (weight : ℝ) (diameter : ℝ)
        (budgetSpentOneSlotRule n hn weight certificate (div_pos hkappa hdiameter))
        (cheapLatencyPrice n (weight : ℝ) (kappa : ℝ) (diameter : ℝ)) := by
  dsimp only
  let certificate : NNReal := kappa / diameter
  have hcertificate : 0 < certificate := div_pos hkappa hdiameter
  let rule := budgetSpentOneSlotRule n hn weight certificate hcertificate
  let price := cheapLatencyPrice n (weight : ℝ) (kappa : ℝ) (diameter : ℝ)
  let bounds : Set ℝ := {R : ℝ | ∃ x : InterimRule (Fin n) 0,
    IsBoundedZeroInvestmentRule n (weight : ℝ) (kappa : ℝ) (diameter : ℝ) x ∧
      HasBoundedOneSlotRegretBound n (by omega)
        (weight : ℝ) (diameter : ℝ) x R}
  have hCertificateDiameter :
      (certificate : ℝ) * (diameter : ℝ) = (kappa : ℝ) := by
    dsimp [certificate]
    field_simp [ne_of_gt (show (0 : ℝ) < (diameter : ℝ) by
      exact_mod_cast hdiameter)]
  have hZero : IsBoundedZeroInvestmentRule n (weight : ℝ) (kappa : ℝ)
      (diameter : ℝ) rule := by
    apply budgetSpentOneSlotRule_zeroInvestment n hn weight certificate
      hcertificate (kappa : ℝ) (diameter : ℝ)
    exact hCertificateDiameter.le
  have hBranch :
      2 * (certificate : ℝ) * (diameter : ℝ) <
        (weight : ℝ) * (1 - 1 / (n : ℝ)) := by
    rw [mul_assoc, hCertificateDiameter]
    exact hCheap
  have hPriceIdentity :
      boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) (diameter : ℝ) =
        price := by
    rw [boundedOneSlotPrice, if_pos hBranch]
    dsimp [price, cheapLatencyPrice]
    rw [← hCertificateDiameter]
    ring
  have hCertified := budgetSpentOneSlotRule_certificate n hn weight certificate
    hweight hcertificate (diameter : ℝ)
  have hRegret : HasBoundedOneSlotRegretBound n (by omega)
      (weight : ℝ) (diameter : ℝ) rule price := by
    simpa [rule, hPriceIdentity] using hCertified.2
  have hPriceMem : price ∈ bounds := ⟨rule, hZero, hRegret⟩
  have hNonempty : bounds.Nonempty := ⟨price, hPriceMem⟩
  have hLower : ∀ R ∈ bounds, price ≤ R := by
    intro R hR
    rcases hR with ⟨x, hx, hxR⟩
    exact zeroInvestment_uniform_lower n hn (weight : ℝ) (kappa : ℝ)
      (diameter : ℝ) hdiameter.le x hx R hxR
  have hEquality : sInf bounds = price := by
    apply le_antisymm
    · exact csInf_le ⟨price, hLower⟩ hPriceMem
    · exact le_csInf hNonempty hLower
  refine ⟨?_, hZero, hRegret⟩
  change sInf bounds = price
  exact hEquality

/-- The strict-slack clause of Corollary `cor:cheap-latency-price`.  A
retention factor in `(0,1)` multiplies the boundary certificate: every
positive latency action is then strictly worse than zero, and the same
one-leader endpoint proves that the displayed uniform loss of the rule is
exact rather than merely an upper bound. -/
theorem cheapLatency_strictSlack_rule
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight kappa diameter retention : NNReal)
    (hweight : 0 < weight) (hkappa : 0 < kappa)
    (hdiameter : 0 < diameter) (hretention0 : 0 < retention)
    (hretention1 : retention < 1)
    (hCheap : 2 * (kappa : ℝ) <
      (weight : ℝ) * (1 - 1 / (n : ℝ))) :
    let certificate : NNReal := retention * (kappa / diameter)
    let rule := budgetSpentOneSlotRule n hn weight certificate
      (mul_pos hretention0 (div_pos hkappa hdiameter))
    let price := (weight : ℝ) * (diameter : ℝ) *
        (1 - 1 / (n : ℝ)) -
      (retention : ℝ) * (kappa : ℝ) * (diameter : ℝ)
    IsBoundedZeroInvestmentRule n (weight : ℝ) (kappa : ℝ) (diameter : ℝ)
        rule ∧
      (∀ b, InBoundedPremiumCube (diameter : ℝ) b → ∀ i action,
        0 < action →
          advantageUtility
              (budgetSpentOneSlotSlice n hn weight certificate
                (mul_pos hretention0 (div_pos hkappa hdiameter)) b i)
              (fun a => (kappa : ℝ) * a) 0 (b i) action <
            advantageUtility
              (budgetSpentOneSlotSlice n hn weight certificate
                (mul_pos hretention0 (div_pos hkappa hdiameter)) b i)
              (fun a => (kappa : ℝ) * a) 0 (b i) 0) ∧
      HasBoundedOneSlotRegretBound n (by omega) (weight : ℝ) (diameter : ℝ)
        rule price ∧
      ∃ b, InBoundedPremiumCube (diameter : ℝ) b ∧
        (weight : ℝ) * topKScore 1
          (by simpa using (show 1 ≤ n by omega)) (fun i => (b i : ℝ)) -
          welfare rule b = price := by
  dsimp only
  let certificate : NNReal := retention * (kappa / diameter)
  have hcertificate : 0 < certificate :=
    mul_pos hretention0 (div_pos hkappa hdiameter)
  let rule := budgetSpentOneSlotRule n hn weight certificate hcertificate
  let price := (weight : ℝ) * (diameter : ℝ) *
      (1 - 1 / (n : ℝ)) -
    (retention : ℝ) * (kappa : ℝ) * (diameter : ℝ)
  have hCertificateDiameter :
      (certificate : ℝ) * (diameter : ℝ) =
        (retention : ℝ) * (kappa : ℝ) := by
    dsimp [certificate]
    field_simp [ne_of_gt (show (0 : ℝ) < (diameter : ℝ) by
      exact_mod_cast hdiameter)]
  have hRetentionReal : (retention : ℝ) < 1 := by exact_mod_cast hretention1
  have hKappaReal : (0 : ℝ) < (kappa : ℝ) := by exact_mod_cast hkappa
  have hBudgetStrict :
      (certificate : ℝ) * (diameter : ℝ) < (kappa : ℝ) := by
    rw [hCertificateDiameter]
    nlinarith
  have hBranch :
      2 * (certificate : ℝ) * (diameter : ℝ) <
        (weight : ℝ) * (1 - 1 / (n : ℝ)) := by
    rw [mul_assoc, hCertificateDiameter]
    nlinarith
  have hPriceIdentity :
      boundedOneSlotPrice n (weight : ℝ) (certificate : ℝ) (diameter : ℝ) =
        price := by
    rw [boundedOneSlotPrice, if_pos hBranch]
    dsimp [price]
    rw [← hCertificateDiameter]
    ring
  have hCertified := budgetSpentOneSlotRule_certificate n hn weight certificate
    hweight hcertificate (diameter : ℝ)
  have hZero : IsBoundedZeroInvestmentRule n (weight : ℝ) (kappa : ℝ)
      (diameter : ℝ) rule := by
    apply budgetSpentOneSlotRule_zeroInvestment n hn weight certificate
      hcertificate (kappa : ℝ) (diameter : ℝ)
    exact hBudgetStrict.le
  have hStrict : ∀ b, InBoundedPremiumCube (diameter : ℝ) b → ∀ i action,
      0 < action →
        advantageUtility
            (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i)
            (fun a => (kappa : ℝ) * a) 0 (b i) action <
          advantageUtility
            (budgetSpentOneSlotSlice n hn weight certificate hcertificate b i)
            (fun a => (kappa : ℝ) * a) 0 (b i) 0 := by
    intro b hb i action haction
    exact budgetSpentOneSlotRule_strictNoRace n hn weight certificate
      hcertificate (kappa : ℝ) (diameter : ℝ) hBudgetStrict
      b hb i action haction
  have hRegret : HasBoundedOneSlotRegretBound n (by omega)
      (weight : ℝ) (diameter : ℝ) rule price := by
    simpa [rule, hPriceIdentity] using hCertified.2
  let b := oneLeaderPremiumProfile n (diameter : ℝ) hdiameter.le
  have hb : InBoundedPremiumCube (diameter : ℝ) b :=
    oneLeaderPremiumProfile_mem_cube n (diameter : ℝ) (diameter : ℝ)
      hdiameter.le le_rfl
  have hLower := oneLeader_certified_loss_lower n hn weight certificate rule
    hCertified.1.1 hCertified.1.2.2.1 hCertified.1.2.2.2
    (diameter : ℝ) hdiameter.le
  have hTop := oneLeaderPremiumProfile_topScore n (by omega)
    (diameter : ℝ) hdiameter.le
  have hUpper := hRegret b hb
  rw [hTop] at hUpper
  have hEndpointPrice :
      (diameter : ℝ) * ((weight : ℝ) * (1 - 1 / (n : ℝ)) -
        (certificate : ℝ) * (diameter : ℝ)) = price := by
    dsimp [price]
    rw [hCertificateDiameter]
    ring
  rw [hEndpointPrice] at hLower
  have hAttains :
      (weight : ℝ) * topKScore 1
        (by simpa using (show 1 ≤ n by omega)) (fun i => (b i : ℝ)) -
          welfare rule b = price := by
    rw [hTop]
    exact le_antisymm hUpper hLower
  exact ⟨hZero, hStrict, hRegret, b, hb, hAttains⟩

end

end SmoothingCliff.Frontier
