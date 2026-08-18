import SmoothingCliff.Frontier.Squeeze
import SmoothingCliff.Frontier.TwoBidder
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Fintype.Lattice

/-!
# The one-slot water-filling frontier

This file formalizes the finite-population core of Theorem `thm:pos` in
`Smoothing_the_Cliff_ITCS.tex`: existence and allocation-level uniqueness of
the water-filling threshold, the induced winner lottery, its comparative
statics, the universal lower-bound certificate, and the pointwise worst-case
welfare bound.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff

/-- Allocation generated at a proposed water-filling threshold. -/
noncomputable def waterFillAt {ι : Type*} (weight sensitivity : NNReal)
    (b : ι → ℝ) (threshold : ℝ) (i : ι) : ℝ :=
  clampWeight weight ((sensitivity : ℝ) * (b i - threshold))

/-- Total priority mass generated at a proposed threshold. -/
noncomputable def waterFillMass {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i, waterFillAt weight sensitivity b threshold i

/-- The threshold equation in Theorem `thm:pos(ii)`. -/
def IsWaterFillingThreshold {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) (threshold : ℝ) : Prop :=
  waterFillMass weight sensitivity b threshold = weight

theorem clampWeight_continuous (weight : NNReal) :
    Continuous (clampWeight weight) := by
  simpa only [clampWeight, Set.coe_projIcc] using
    (continuous_const.max (continuous_const.min continuous_id) :
      Continuous (fun z : ℝ => max 0 (min (weight : ℝ) z)))

theorem clampWeight_eq_zero_of_nonpos (weight : NNReal) {z : ℝ} (hz : z ≤ 0) :
    clampWeight weight z = 0 := by
  simp only [clampWeight, Set.coe_projIcc]
  rw [min_eq_right (hz.trans weight.coe_nonneg), max_eq_left hz]

theorem clampWeight_eq_weight_of_le (weight : NNReal) {z : ℝ}
    (hz : (weight : ℝ) ≤ z) :
    clampWeight weight z = weight := by
  simp only [clampWeight, Set.coe_projIcc]
  rw [min_eq_left hz, max_eq_right weight.coe_nonneg]

theorem continuous_waterFillMass {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) :
    Continuous (waterFillMass weight sensitivity b) := by
  unfold waterFillMass
  apply continuous_finsetSum
  intro i hi
  unfold waterFillAt
  apply (clampWeight_continuous weight).comp
  exact continuous_const.mul (continuous_const.sub continuous_id)

/-- For a finite nonempty population and positive sensitivity, the threshold
equation has a solution. The proof brackets the target mass between the
highest bid and that bid minus `weight / sensitivity`, then applies the IVT. -/
theorem exists_waterFillingThreshold {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) :
    ∃ threshold, IsWaterFillingThreshold weight sensitivity b threshold := by
  obtain ⟨imax, himax⟩ := Finite.exists_max b
  have hzero : waterFillMass weight sensitivity b (b imax) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply clampWeight_eq_zero_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos sensitivity.coe_nonneg
      (sub_nonpos.mpr (himax i))
  let low : ℝ := b imax - (weight : ℝ) / (sensitivity : ℝ)
  have hs0 : (sensitivity : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hs
  have htop : waterFillAt weight sensitivity b low imax = weight := by
    apply clampWeight_eq_weight_of_le
    dsimp [low, waterFillAt]
    rw [show b imax - (b imax - (weight : ℝ) / (sensitivity : ℝ)) =
      (weight : ℝ) / (sensitivity : ℝ) by ring]
    rw [mul_div_cancel₀ _ hs0]
  have hlow : (weight : ℝ) ≤ waterFillMass weight sensitivity b low := by
    rw [← htop]
    unfold waterFillMass
    refine Finset.single_le_sum (s := Finset.univ)
      (f := fun i => waterFillAt weight sensitivity b low i) ?_ (Finset.mem_univ imax)
    intro i hi
    exact clampWeight_nonneg weight _
  have hrange : (weight : ℝ) ∈ Set.range (waterFillMass weight sensitivity b) := by
    apply mem_range_of_exists_le_of_exists_ge
    · exact continuous_waterFillMass weight sensitivity b
    · exact ⟨b imax, by rw [hzero]; exact weight.coe_nonneg⟩
    · exact ⟨low, hlow⟩
  rcases hrange with ⟨threshold, hthreshold⟩
  exact ⟨threshold, hthreshold⟩

theorem waterFillAt_antitone_threshold {ι : Type*}
    (weight sensitivity : NNReal) (b : ι → ℝ) :
    Antitone (fun threshold => waterFillAt weight sensitivity b threshold) := by
  intro s t hst i
  apply clampWeight_monotone
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hst (b i)) sensitivity.coe_nonneg

/-- The threshold itself may range over a flat interval, but every solution of
the threshold equation induces exactly the same allocation vector. -/
theorem waterFillAt_eq_of_thresholds {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) {s t : ℝ}
    (hs : IsWaterFillingThreshold weight sensitivity b s)
    (ht : IsWaterFillingThreshold weight sensitivity b t) (i : ι) :
    waterFillAt weight sensitivity b s i =
      waterFillAt weight sensitivity b t i := by
  rcases le_total s t with hst | hts
  · have hle : ∀ j ∈ Finset.univ,
        waterFillAt weight sensitivity b t j ≤
          waterFillAt weight sensitivity b s j := by
      intro j hj
      exact waterFillAt_antitone_threshold weight sensitivity b hst j
    have hsum :
        (∑ j, waterFillAt weight sensitivity b t j) =
          ∑ j, waterFillAt weight sensitivity b s j := by
      exact ht.trans hs.symm
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)).symm
  · have hle : ∀ j ∈ Finset.univ,
        waterFillAt weight sensitivity b s j ≤
          waterFillAt weight sensitivity b t j := by
      intro j hj
      exact waterFillAt_antitone_threshold weight sensitivity b hts j
    have hsum :
        (∑ j, waterFillAt weight sensitivity b s j) =
          ∑ j, waterFillAt weight sensitivity b t j := by
      exact hs.trans ht.symm
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)

/-- A canonical threshold, chosen only after existence has been proved. -/
noncomputable def waterFillingThreshold {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) : ℝ :=
  Classical.choose (exists_waterFillingThreshold weight sensitivity hs b)

theorem waterFillingThreshold_spec {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) :
    IsWaterFillingThreshold weight sensitivity b
      (waterFillingThreshold weight sensitivity hs b) :=
  Classical.choose_spec (exists_waterFillingThreshold weight sensitivity hs b)

/-- The allocation vector induced by the canonical threshold. Allocation-level
uniqueness makes this independent of the particular witness selected above. -/
noncomputable def waterFillingVector {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) (i : ι) : ℝ :=
  waterFillAt weight sensitivity b (waterFillingThreshold weight sensitivity hs b) i

theorem waterFillingVector_eq_at_threshold {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ)
    {threshold : ℝ} (ht : IsWaterFillingThreshold weight sensitivity b threshold)
    (i : ι) :
    waterFillingVector weight sensitivity hs b i =
      waterFillAt weight sensitivity b threshold i := by
  exact waterFillAt_eq_of_thresholds weight sensitivity b
    (waterFillingThreshold_spec weight sensitivity hs b) ht i

theorem waterFillingVector_mass {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) :
    ∑ i, waterFillingVector weight sensitivity hs b i = weight := by
  exact waterFillingThreshold_spec weight sensitivity hs b

theorem waterFillingVector_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) (i : ι) :
    0 ≤ waterFillingVector weight sensitivity hs b i :=
  clampWeight_nonneg weight _

theorem waterFillingVector_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hs : 0 < sensitivity) (b : ι → ℝ) (i : ι) :
    waterFillingVector weight sensitivity hs b i ≤ weight :=
  clampWeight_le weight _

/-- Raising coordinate `j` while weakly lowering the threshold weakly raises
every allocation coordinate. -/
theorem waterFillAt_le_update_of_threshold_le
    {ι : Type*} [DecidableEq ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) (j : ι) {z s t : ℝ}
    (hb : b j ≤ z) (ht : t ≤ s) (i : ι) :
    waterFillAt weight sensitivity b s i ≤
      waterFillAt weight sensitivity (Function.update b j z) t i := by
  apply clampWeight_monotone
  apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
  by_cases hij : i = j
  · subst i
    simp
    linarith
  · simp [Function.update, hij]
    linarith

/-- If the threshold rises after coordinate `j` rises, every other coordinate
weakly loses allocation. -/
theorem waterFillAt_update_le_of_threshold_le
    {ι : Type*} [DecidableEq ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) (j : ι) {z s t : ℝ}
    (hst : s ≤ t) {i : ι} (hij : i ≠ j) :
    waterFillAt weight sensitivity (Function.update b j z) t i ≤
      waterFillAt weight sensitivity b s i := by
  apply clampWeight_monotone
  apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
  simp [Function.update, hij]
  linarith

/-- After one bid rises, either a valid new threshold lies weakly above the old
one, or the two threshold solutions induce exactly the same allocations. This
formulation is robust to flat intervals of threshold solutions. -/
theorem threshold_le_or_update_allocations_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) (j : ι) {z s t : ℝ}
    (hb : b j ≤ z)
    (hs : IsWaterFillingThreshold weight sensitivity b s)
    (ht : IsWaterFillingThreshold weight sensitivity (Function.update b j z) t) :
    s ≤ t ∨ ∀ i,
      waterFillAt weight sensitivity b s i =
        waterFillAt weight sensitivity (Function.update b j z) t i := by
  rcases le_total s t with hst | hts
  · exact Or.inl hst
  · right
    have hle : ∀ i ∈ Finset.univ,
        waterFillAt weight sensitivity b s i ≤
          waterFillAt weight sensitivity (Function.update b j z) t i := by
      intro i hi
      exact waterFillAt_le_update_of_threshold_le weight sensitivity b j hb hts i
    have hsum :
        (∑ i, waterFillAt weight sensitivity b s i) =
          ∑ i, waterFillAt weight sensitivity (Function.update b j z) t i := by
      exact hs.trans ht.symm
    intro i
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)

theorem waterFillingVector_own_monotone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) {z : ℝ} (hb : b i ≤ z) :
    waterFillingVector weight sensitivity hsens b i ≤
      waterFillingVector weight sensitivity hsens (Function.update b i z) i := by
  let s := waterFillingThreshold weight sensitivity hsens b
  let t := waterFillingThreshold weight sensitivity hsens (Function.update b i z)
  have hs := waterFillingThreshold_spec weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens (Function.update b i z)
  rcases threshold_le_or_update_allocations_eq weight sensitivity b i hb hs ht with
      hst | heq
  · by_contra hnot
    have hstrict :
        waterFillAt weight sensitivity (Function.update b i z) t i <
          waterFillAt weight sensitivity b s i := lt_of_not_ge hnot
    have hle : ∀ k ∈ Finset.univ,
        waterFillAt weight sensitivity (Function.update b i z) t k ≤
          waterFillAt weight sensitivity b s k := by
      intro k hk
      by_cases hki : k = i
      · subst k
        exact hstrict.le
      · exact waterFillAt_update_le_of_threshold_le weight sensitivity b i hst hki
    have hsumlt := Finset.sum_lt_sum hle ⟨i, Finset.mem_univ i, hstrict⟩
    change (∑ k, waterFillAt weight sensitivity (Function.update b i z) t k) =
      weight at ht
    change (∑ k, waterFillAt weight sensitivity b s k) = weight at hs
    rw [ht, hs] at hsumlt
    exact (lt_irrefl (weight : ℝ)) hsumlt
  · exact (heq i).le

theorem waterFillingVector_cross_monotone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) {i j : ι} (hij : i ≠ j) {z : ℝ} (hb : b j ≤ z) :
    waterFillingVector weight sensitivity hsens (Function.update b j z) i ≤
      waterFillingVector weight sensitivity hsens b i := by
  let s := waterFillingThreshold weight sensitivity hsens b
  let t := waterFillingThreshold weight sensitivity hsens (Function.update b j z)
  have hs := waterFillingThreshold_spec weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens (Function.update b j z)
  rcases threshold_le_or_update_allocations_eq weight sensitivity b j hb hs ht with
      hst | heq
  · exact waterFillAt_update_le_of_threshold_le weight sensitivity b j hst hij
  · exact (heq i).ge

/-- The own-coordinate increase after raising a bid is at most sensitivity
times the bid increase. This is the one-sided form of the own Lipschitz bound. -/
theorem waterFillingVector_own_increment_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) {z : ℝ} (hb : b i ≤ z) :
    waterFillingVector weight sensitivity hsens (Function.update b i z) i -
        waterFillingVector weight sensitivity hsens b i ≤
      (sensitivity : ℝ) * (z - b i) := by
  let s := waterFillingThreshold weight sensitivity hsens b
  let t := waterFillingThreshold weight sensitivity hsens (Function.update b i z)
  have hs := waterFillingThreshold_spec weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens (Function.update b i z)
  have hown := waterFillingVector_own_monotone weight sensitivity hsens b i hb
  rcases threshold_le_or_update_allocations_eq weight sensitivity b i hb hs ht with
      hst | heq
  · let a : ℝ := (sensitivity : ℝ) * (b i - s)
    let c : ℝ := (sensitivity : ℝ) * (z - t)
    have hown' : clampWeight weight a ≤ clampWeight weight c := by
      change waterFillAt weight sensitivity b s i ≤
        waterFillAt weight sensitivity (Function.update b i z) t i at hown
      simp only [waterFillAt] at hown
      simp at hown
      change clampWeight weight a ≤ clampWeight weight c at hown
      exact hown
    by_cases hac : a ≤ c
    · have hlip :
          |clampWeight weight a - clampWeight weight c| ≤ |a - c| :=
        Set.abs_projIcc_sub_projIcc weight.coe_nonneg
      have hca : clampWeight weight a ≤ clampWeight weight c :=
        clampWeight_monotone weight hac
      have hlip' : clampWeight weight c - clampWeight weight a ≤ c - a := by
        rw [abs_of_nonpos (sub_nonpos.mpr hca), abs_of_nonpos (sub_nonpos.mpr hac)] at hlip
        linarith
      change waterFillAt weight sensitivity (Function.update b i z) t i -
          waterFillAt weight sensitivity b s i ≤
        (sensitivity : ℝ) * (z - b i)
      simp only [waterFillAt]
      simp
      change clampWeight weight c ≤
        (sensitivity : ℝ) * (z - b i) + clampWeight weight a
      have hraw : c - a ≤ (sensitivity : ℝ) * (z - b i) := by
        dsimp [a, c]
        nlinarith [sensitivity.coe_nonneg]
      linarith
    · have hca : clampWeight weight c ≤ clampWeight weight a :=
        clampWeight_monotone weight (le_of_not_ge hac)
      change waterFillAt weight sensitivity (Function.update b i z) t i -
          waterFillAt weight sensitivity b s i ≤
        (sensitivity : ℝ) * (z - b i)
      simp only [waterFillAt]
      simp
      change clampWeight weight c ≤
        (sensitivity : ℝ) * (z - b i) + clampWeight weight a
      have heqca : clampWeight weight c = clampWeight weight a := by
        apply le_antisymm hca
        exact hown'
      rw [heqca]
      have hnonneg : 0 ≤ (sensitivity : ℝ) * (z - b i) :=
        mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hb)
      linarith
  · change waterFillAt weight sensitivity (Function.update b i z) t i -
        waterFillAt weight sensitivity b s i ≤
      (sensitivity : ℝ) * (z - b i)
    rw [← heq i, sub_self]
    positivity

/-- The allocation of an agent is globally sensitivity-Lipschitz in that
agent's real-valued bid, with all other bids held fixed. -/
theorem waterFillingVector_own_lipschitz
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) :
    LipschitzWith sensitivity
      (fun z : ℝ => waterFillingVector weight sensitivity hsens
        (Function.update b i z) i) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  rcases le_total z z' with hzz | hzz
  · have hupdate : Function.update (Function.update b i z) i z' =
        Function.update b i z' := by
      funext k
      by_cases hki : k = i <;> simp [Function.update, hki]
    have hstep := waterFillingVector_own_increment_le weight sensitivity hsens
      (Function.update b i z) i (z := z') (by simpa using hzz)
    have hmono := waterFillingVector_own_monotone weight sensitivity hsens
      (Function.update b i z) i (z := z') (by simpa using hzz)
    rw [hupdate] at hstep hmono
    simp [Function.update] at hstep
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hzz)]
    linarith
  · have hupdate : Function.update (Function.update b i z') i z =
        Function.update b i z := by
      funext k
      by_cases hki : k = i <;> simp [Function.update, hki]
    have hstep := waterFillingVector_own_increment_le weight sensitivity hsens
      (Function.update b i z') i (z := z) (by simpa using hzz)
    have hmono := waterFillingVector_own_monotone weight sensitivity hsens
      (Function.update b i z') i (z := z) (by simpa using hzz)
    rw [hupdate] at hstep hmono
    simp [Function.update] at hstep
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hzz)]
    linarith

theorem waterFillingVector_coordinate_monotone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) :
    Monotone (fun z : ℝ => waterFillingVector weight sensitivity hsens
      (Function.update b i z) i) := by
  intro z z' hzz
  have hupdate : Function.update (Function.update b i z) i z' =
      Function.update b i z' := by
    funext k
    by_cases hki : k = i <;> simp [Function.update, hki]
  have h := waterFillingVector_own_monotone weight sensitivity hsens
    (Function.update b i z) i (z := z') (by simpa using hzz)
  rwa [hupdate] at h

theorem waterFillingVector_coordinate_antitone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    Antitone (fun z : ℝ => waterFillingVector weight sensitivity hsens
      (Function.update b j z) i) := by
  intro z z' hzz
  have hupdate : Function.update (Function.update b j z) j z' =
      Function.update b j z' := by
    funext k
    by_cases hkj : k = j <;> simp [Function.update, hkj]
  have h := waterFillingVector_cross_monotone weight sensitivity hsens
    (Function.update b j z) hij (z := z') (by simpa using hzz)
  rwa [hupdate] at h

/-- Water-filling commutes with relabeling the finite population. -/
theorem waterFillingVector_equivariant
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (π : Equiv.Perm ι) (b : ι → ℝ) (i : ι) :
    waterFillingVector weight sensitivity hsens (fun j => b (π.symm j)) (π i) =
      waterFillingVector weight sensitivity hsens b i := by
  let t := waterFillingThreshold weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens b
  have htRelabel :
      IsWaterFillingThreshold weight sensitivity (fun j => b (π.symm j)) t := by
    change (∑ j, waterFillAt weight sensitivity (fun k => b (π.symm k)) t j) = weight
    calc
      (∑ j, waterFillAt weight sensitivity (fun k => b (π.symm k)) t j) =
          ∑ j, waterFillAt weight sensitivity b t (π.symm j) := by rfl
      _ = ∑ j, waterFillAt weight sensitivity b t j :=
        Equiv.sum_comp π.symm (fun j => waterFillAt weight sensitivity b t j)
      _ = weight := ht
  calc
    waterFillingVector weight sensitivity hsens (fun j => b (π.symm j)) (π i) =
        waterFillAt weight sensitivity (fun j => b (π.symm j)) t (π i) :=
      waterFillingVector_eq_at_threshold weight sensitivity hsens _ htRelabel _
    _ = waterFillAt weight sensitivity b t i := by
      simp [waterFillAt]
    _ = waterFillingVector weight sensitivity hsens b i :=
      (waterFillingVector_eq_at_threshold weight sensitivity hsens b ht i).symm

/-- The water-filling interim rule on the paper's eligible-bid domain. -/
noncomputable def waterFillingRule
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    InterimRule ι reserve :=
  fun b i => waterFillingVector weight sensitivity hsens (fun j => (b j : ℝ)) i

theorem waterFillingRule_noWaste
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    OneSlotNoWaste (weight : ℝ)
      (waterFillingRule (ι := ι) (reserve := reserve) weight sensitivity hsens) := by
  intro b
  exact waterFillingVector_mass weight sensitivity hsens (fun j => (b j : ℝ))

theorem waterFillingRule_feasible
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    OneSlotFeasible (weight : ℝ)
      (waterFillingRule (ι := ι) (reserve := reserve) weight sensitivity hsens) := by
  constructor
  · intro b i
    exact waterFillingVector_nonneg weight sensitivity hsens _ i
  · intro b
    exact (waterFillingRule_noWaste (ι := ι) (reserve := reserve)
      weight sensitivity hsens b).le

theorem waterFillingRule_anonymous
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    Anonymous (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) := by
  intro π b i
  simpa [waterFillingRule, relabelProfile] using
    waterFillingVector_equivariant weight sensitivity hsens π
      (fun j => (b j : ℝ)) i

theorem waterFillingRule_ownMonotone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    OwnMonotone (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) := by
  intro b i z z' hzz
  let br : ι → ℝ := fun j => (b j : ℝ)
  have hz : (fun j => ((updateBid b i z) j : ℝ)) =
      Function.update br i (z : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  have hz' : (fun j => ((updateBid b i z') j : ℝ)) =
      Function.update br i (z' : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  change waterFillingVector weight sensitivity hsens
      (fun j => ((updateBid b i z) j : ℝ)) i ≤
    waterFillingVector weight sensitivity hsens
      (fun j => ((updateBid b i z') j : ℝ)) i
  rw [hz, hz']
  exact waterFillingVector_coordinate_monotone weight sensitivity hsens br i hzz

theorem waterFillingRule_crossMonotone
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    CrossMonotone (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) := by
  intro b i j hij z z' hzz
  let br : ι → ℝ := fun k => (b k : ℝ)
  have hz : (fun k => ((updateBid b j z) k : ℝ)) =
      Function.update br j (z : ℝ) := by
    funext k
    by_cases hkj : k = j <;> simp [updateBid, br, Function.update, hkj]
  have hz' : (fun k => ((updateBid b j z') k : ℝ)) =
      Function.update br j (z' : ℝ) := by
    funext k
    by_cases hkj : k = j <;> simp [updateBid, br, Function.update, hkj]
  change waterFillingVector weight sensitivity hsens
      (fun k => ((updateBid b j z') k : ℝ)) i ≤
    waterFillingVector weight sensitivity hsens
      (fun k => ((updateBid b j z) k : ℝ)) i
  rw [hz, hz']
  exact waterFillingVector_coordinate_antitone weight sensitivity hsens br hij hzz

theorem waterFillingRule_ownLipschitz
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    OwnLipschitz sensitivity (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) := by
  intro b i
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  let br : ι → ℝ := fun j => (b j : ℝ)
  have hz : (fun j => ((updateBid b i z) j : ℝ)) =
      Function.update br i (z : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  have hz' : (fun j => ((updateBid b i z') j : ℝ)) =
      Function.update br i (z' : ℝ) := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, br, Function.update, hji]
  change dist (waterFillingVector weight sensitivity hsens
      (fun j => ((updateBid b i z) j : ℝ)) i)
      (waterFillingVector weight sensitivity hsens
        (fun j => ((updateBid b i z') j : ℝ)) i) ≤
    (sensitivity : ℝ) * dist z z'
  rw [hz, hz']
  simpa only [Subtype.dist_eq] using
    (waterFillingVector_own_lipschitz weight sensitivity hsens br i).dist_le_mul
      (z : ℝ) (z' : ℝ)

/-- After normalization by a positive slot weight, the allocation is a
probability vector and hence is implementable as a winner lottery. -/
theorem waterFillingRule_winnerLottery
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) (b : EligibleProfile ι reserve) :
    (∀ i, 0 ≤ waterFillingRule weight sensitivity hsens b i / (weight : ℝ) ∧
        waterFillingRule weight sensitivity hsens b i / (weight : ℝ) ≤ 1) ∧
      ∑ i, waterFillingRule weight sensitivity hsens b i / (weight : ℝ) = 1 := by
  have hw : (0 : ℝ) < weight := by exact_mod_cast hweight
  constructor
  · intro i
    constructor
    · exact div_nonneg
        ((waterFillingRule_feasible (ι := ι) (reserve := reserve)
          weight sensitivity hsens).1 b i) hw.le
    · exact (div_le_one hw).mpr
        (waterFillingVector_le weight sensitivity hsens _ i)
  · rw [← Finset.sum_div]
    rw [waterFillingRule_noWaste (ι := ι) (reserve := reserve)
      weight sensitivity hsens b]
    exact div_self (ne_of_gt hw)

/-- The all-tied eligible profile used by the lower-bound certificate. -/
def tiedEligibleProfile {ι : Type*} (reserve : ℝ) : EligibleProfile ι reserve :=
  fun _ => ⟨reserve, by change reserve ≤ reserve; exact le_rfl⟩

/-- Raise agent zero by `delta` from an all-tied profile. -/
def oneLeaderEligibleProfile (n : ℕ) (reserve delta : ℝ) (hdelta : 0 ≤ delta) :
    EligibleProfile (Fin (n + 2)) reserve :=
  fun i => if i = 0 then
    ⟨reserve + delta, by change reserve ≤ reserve + delta; linarith⟩
  else ⟨reserve, by change reserve ≤ reserve; exact le_rfl⟩

theorem update_tiedProfile_zero (n : ℕ) (reserve delta : ℝ) (hdelta : 0 ≤ delta) :
    updateBid (tiedEligibleProfile reserve : EligibleProfile (Fin (n + 2)) reserve)
      0 ⟨reserve + delta, by change reserve ≤ reserve + delta; linarith⟩ =
        oneLeaderEligibleProfile n reserve delta hdelta := by
  funext i
  apply Subtype.ext
  by_cases hi : i = 0
  · subst i
    simp [updateBid, oneLeaderEligibleProfile]
  · simp [updateBid, tiedEligibleProfile, oneLeaderEligibleProfile, hi]

/-- At an anonymous `N`-way tie, feasibility caps each allocation at the
equal-share benchmark `weight / N`. -/
theorem anonymous_tie_allocation_le_average
    (n : ℕ) {reserve : ℝ} (weight : NNReal)
    (x : InterimRule (Fin (n + 2)) reserve)
    (hAnon : Anonymous x) (hFeasible : OneSlotFeasible (weight : ℝ) x)
    (b : EligibleProfile (Fin (n + 2)) reserve)
    (hTie : ∀ i j, (b i : ℝ) = (b j : ℝ)) :
    x b 0 ≤ (weight : ℝ) / ((n : ℝ) + 2) := by
  have hall : ∀ i, x b i = x b 0 := by
    intro i
    exact allocation_eq_of_bid_eq x hAnon b i 0 (hTie i 0)
  have hsum : ∑ i, x b i ≤ weight := hFeasible.2 b
  have hsumEq : ∑ i, x b i = (n + 2 : ℝ) * x b 0 := by
    calc
      (∑ i, x b i) = ∑ _i : Fin (n + 2), x b 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hall i
      _ = (n + 2 : ℝ) * x b 0 := by simp
  rw [hsumEq] at hsum
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 2)).2
  simpa [mul_comm] using hsum

/-- Bid increment optimizing the quadratic lower-bound certificate for a
population of size `n + 2`. -/
noncomputable def minimaxLowerDelta (n : ℕ) (weight sensitivity : NNReal) : ℝ :=
  (weight : ℝ) * (1 - 1 / ((n : ℝ) + 2)) / (2 * (sensitivity : ℝ))

theorem minimaxLowerDelta_nonneg (n : ℕ) (weight sensitivity : NNReal) :
    0 ≤ minimaxLowerDelta n weight sensitivity := by
  unfold minimaxLowerDelta
  have hNpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hNge : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdiv : 1 / ((n : ℝ) + 2) ≤ 1 := by
    apply (div_le_iff₀ hNpos).2
    simpa using hNge
  exact div_nonneg (mul_nonneg weight.coe_nonneg (sub_nonneg.mpr hdiv))
    (mul_nonneg (by norm_num) sensitivity.coe_nonneg)

/-- The lower-bound half of Theorem `thm:pos(i)`, as the exact adversarial
profile certificate used in the paper. For every admissible rule on `n + 2`
agents, the one-leader profile at the optimizing gap incurs at least
`(1 - 1/(n+2))² weight² / (4 sensitivity)` welfare loss. -/
theorem minimax_welfare_lower_bound_certificate
    (n : ℕ) {reserve : ℝ} (hreserve : 0 ≤ reserve)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (x : InterimRule (Fin (n + 2)) reserve)
    (hAnon : Anonymous x)
    (hLipschitz : OwnLipschitz sensitivity x)
    (hFeasible : OneSlotFeasible (weight : ℝ) x) :
    let delta := minimaxLowerDelta n weight sensitivity
    (reserve + delta) * (weight : ℝ) -
        welfare x (oneLeaderEligibleProfile n reserve delta
          (minimaxLowerDelta_nonneg n weight sensitivity)) ≥
      (1 - 1 / ((n : ℝ) + 2)) ^ 2 * (weight : ℝ) ^ 2 /
        (4 * (sensitivity : ℝ)) := by
  let delta := minimaxLowerDelta n weight sensitivity
  let b0 : EligibleProfile (Fin (n + 2)) reserve := tiedEligibleProfile reserve
  let bΔ : EligibleProfile (Fin (n + 2)) reserve :=
    oneLeaderEligibleProfile n reserve delta
      (minimaxLowerDelta_nonneg n weight sensitivity)
  change (reserve + delta) * (weight : ℝ) - welfare x bΔ ≥
    (1 - 1 / ((n : ℝ) + 2)) ^ 2 * (weight : ℝ) ^ 2 /
      (4 * (sensitivity : ℝ))
  let leaderBid : EligibleBid reserve :=
    ⟨reserve + delta, by
      change reserve ≤ reserve + delta
      exact le_add_of_nonneg_right (minimaxLowerDelta_nonneg n weight sensitivity)⟩
  have hdelta : 0 ≤ delta := minimaxLowerDelta_nonneg n weight sensitivity
  have hzeroUpdate : updateBid b0 0 (b0 0) = b0 := by
    funext i
    apply Subtype.ext
    by_cases hi : i = 0 <;> simp [updateBid, Function.update, hi]
  have hleaderUpdate : updateBid b0 0 leaderBid = bΔ := by
    change updateBid (tiedEligibleProfile reserve) 0
      ⟨reserve + delta, _⟩ =
        oneLeaderEligibleProfile n reserve delta _
    exact update_tiedProfile_zero n reserve delta hdelta
  have htie : x b0 0 ≤ (weight : ℝ) / ((n : ℝ) + 2) := by
    apply anonymous_tie_allocation_le_average n weight x hAnon hFeasible b0
    intro i j
    rfl
  have hlip := (hLipschitz b0 0).dist_le_mul (b0 0) leaderBid
  rw [hzeroUpdate, hleaderUpdate] at hlip
  have hdist : dist (b0 0) leaderBid = delta := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |reserve - (reserve + delta)| = delta
    rw [show reserve - (reserve + delta) = -delta by ring,
      abs_neg, abs_of_nonneg hdelta]
  rw [hdist] at hlip
  have hdiff : x bΔ 0 - x b0 0 ≤ dist (x b0 0) (x bΔ 0) := by
    rw [Real.dist_eq]
    rw [abs_sub_comm]
    exact le_abs_self (x bΔ 0 - x b0 0)
  have hleader :
      x bΔ 0 ≤ (weight : ℝ) / ((n : ℝ) + 2) +
        (sensitivity : ℝ) * delta := by
    linarith [hdiff]
  have hvalues : ∀ i, (bΔ i : ℝ) = reserve + if i = 0 then delta else 0 := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp [bΔ, oneLeaderEligibleProfile]
    · simp [bΔ, oneLeaderEligibleProfile, hi]
  have hwelfare :
      welfare x bΔ = reserve * (∑ i, x bΔ i) + delta * x bΔ 0 := by
    unfold welfare
    calc
      (∑ i, (bΔ i : ℝ) * x bΔ i) =
          ∑ i, (reserve * x bΔ i + if i = 0 then delta * x bΔ i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hvalues i]
        by_cases hi0 : i = 0
        · subst i
          simp
          ring
        · simp [hi0]
      _ = reserve * (∑ i, x bΔ i) + delta * x bΔ 0 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp
  have hsum : ∑ i, x bΔ i ≤ weight := hFeasible.2 bΔ
  have hwelfareUpper :
      welfare x bΔ ≤ reserve * (weight : ℝ) +
        delta * ((weight : ℝ) / ((n : ℝ) + 2) +
          (sensitivity : ℝ) * delta) := by
    rw [hwelfare]
    have hbase : reserve * (∑ i, x bΔ i) ≤ reserve * (weight : ℝ) :=
      mul_le_mul_of_nonneg_left hsum hreserve
    have hlead : delta * x bΔ 0 ≤
        delta * ((weight : ℝ) / ((n : ℝ) + 2) +
          (sensitivity : ℝ) * delta) :=
      mul_le_mul_of_nonneg_left hleader hdelta
    linarith
  have hs0 : (sensitivity : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsens
  have hn0 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hquadratic :
      delta * ((weight : ℝ) * (1 - 1 / ((n : ℝ) + 2)) -
          (sensitivity : ℝ) * delta) =
        (1 - 1 / ((n : ℝ) + 2)) ^ 2 * (weight : ℝ) ^ 2 /
          (4 * (sensitivity : ℝ)) := by
    dsimp [delta, minimaxLowerDelta]
    field_simp [hs0, hn0]
    ring
  rw [← hquadratic]
  calc
    delta * ((weight : ℝ) * (1 - 1 / ((n : ℝ) + 2)) -
        (sensitivity : ℝ) * delta) =
        (reserve + delta) * (weight : ℝ) -
          (reserve * (weight : ℝ) +
            delta * ((weight : ℝ) / ((n : ℝ) + 2) +
              (sensitivity : ℝ) * delta)) := by ring
    _ ≤ (reserve + delta) * (weight : ℝ) - welfare x bΔ :=
      sub_le_sub_left hwelfareUpper _

theorem clampWeight_eq_of_mem (weight : NNReal) {z : ℝ}
    (hz0 : 0 ≤ z) (hzw : z ≤ weight) :
    clampWeight weight z = z := by
  simp only [clampWeight, Set.coe_projIcc]
  rw [min_eq_right hzw, max_eq_right hz0]

/-- Sharp pointwise welfare bound for water-filling at any valid threshold.
This is the complete algebraic `Worst case` argument in Theorem `thm:pos(ii)`. -/
theorem waterFilling_welfare_loss_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) (b : ι → ℝ) (leader : ι)
    (hleader : ∀ i, b i ≤ b leader) {threshold : ℝ}
    (hthreshold : IsWaterFillingThreshold weight sensitivity b threshold) :
    (weight : ℝ) * b leader -
        ∑ i, b i * waterFillAt weight sensitivity b threshold i ≤
      (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  let a : ι → ℝ := waterFillAt weight sensitivity b threshold
  let D : ℝ := b leader - threshold
  have hwpos : (0 : ℝ) < weight := by exact_mod_cast hweight
  have hspos : (0 : ℝ) < sensitivity := by exact_mod_cast hsens
  have hmass : ∑ i, a i = weight := hthreshold
  have hanonneg : ∀ i, 0 ≤ a i := by
    intro i
    exact clampWeight_nonneg weight _
  have hD : 0 ≤ D := by
    by_contra hnot
    have hDneg : D < 0 := lt_of_not_ge hnot
    have hallzero : ∀ i, a i = 0 := by
      intro i
      apply clampWeight_eq_zero_of_nonpos
      apply mul_nonpos_of_nonneg_of_nonpos sensitivity.coe_nonneg
      dsimp [D] at hDneg
      linarith [hleader i]
    have : ∑ i, a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hallzero i
    rw [this] at hmass
    exact (ne_of_gt hwpos) hmass.symm
  have hgap :
      (weight : ℝ) * b leader - ∑ i, b i * a i =
        ∑ i, a i * (b leader - b i) := by
    rw [← hmass]
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  by_cases hsaturated : (weight : ℝ) ≤ (sensitivity : ℝ) * D
  · have hatop : a leader = weight := by
      apply clampWeight_eq_weight_of_le
      exact hsaturated
    let g : ι → ℝ := fun i => if i = leader then (weight : ℝ) else 0
    have hgle : ∀ i ∈ Finset.univ, g i ≤ a i := by
      intro i hi
      by_cases hil : i = leader
      · subst i
        simp [g, hatop]
      · simp [g, hil, hanonneg i]
    have hgsum : ∑ i, g i = weight := by
      simp [g]
    have hsumEq : ∑ i, g i = ∑ i, a i := hgsum.trans hmass.symm
    have hall := (Finset.sum_eq_sum_iff_of_le hgle).mp hsumEq
    rw [hgap]
    have hzero : ∑ i, a i * (b leader - b i) = 0 := by
      calc
        (∑ i, a i * (b leader - b i)) =
            ∑ i, g i * (b leader - b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hall i (Finset.mem_univ i)]
        _ = 0 := by simp [g]
    rw [hzero]
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) sensitivity.coe_nonneg)
  · have hunsat : (sensitivity : ℝ) * D < weight := lt_of_not_ge hsaturated
    have hatop : a leader = (sensitivity : ℝ) * D := by
      apply clampWeight_eq_of_mem
      · exact mul_nonneg sensitivity.coe_nonneg hD
      · exact hunsat.le
    have hterm (i : ι) :
        a i * (b leader - b i) ≤ a i * D := by
      by_cases hai : a i = 0
      · rw [hai, zero_mul, zero_mul]
      · have haipos : 0 < a i := lt_of_le_of_ne (hanonneg i) (Ne.symm hai)
        have hrawpos : 0 < (sensitivity : ℝ) * (b i - threshold) := by
          by_contra hnot
          have hzero := clampWeight_eq_zero_of_nonpos weight (le_of_not_gt hnot)
          exact hai hzero
        have hbit : threshold < b i := by
          nlinarith
        apply mul_le_mul_of_nonneg_left _ (hanonneg i)
        dsimp [D]
        linarith
    have herase :
        ∑ i ∈ Finset.univ.erase leader, a i * (b leader - b i) ≤
          ∑ i ∈ Finset.univ.erase leader, a i * D := by
      exact Finset.sum_le_sum fun i hi => hterm i
    have hsumErase : ∑ i ∈ Finset.univ.erase leader, a i =
        (weight : ℝ) - a leader := by
      have hdecomp := Finset.sum_erase_add (s := Finset.univ) (f := a)
        (Finset.mem_univ leader)
      linarith
    have hgapErase : ∑ i, a i * (b leader - b i) =
        ∑ i ∈ Finset.univ.erase leader, a i * (b leader - b i) := by
      have hdecomp := Finset.sum_erase_add (s := Finset.univ)
        (f := fun i => a i * (b leader - b i)) (Finset.mem_univ leader)
      simpa only [sub_self, mul_zero, add_zero] using hdecomp.symm
    rw [hgap, hgapErase]
    calc
      (∑ i ∈ Finset.univ.erase leader, a i * (b leader - b i)) ≤
          ∑ i ∈ Finset.univ.erase leader, a i * D := herase
      _ = D * ((weight : ℝ) - (sensitivity : ℝ) * D) := by
        rw [← Finset.sum_mul, hsumErase, hatop]
        ring
      _ ≤ (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hspos)).2
        nlinarith [sq_nonneg (2 * (sensitivity : ℝ) * D - (weight : ℝ))]

/-- The canonical water-filling vector therefore satisfies the paper's
pointwise `weight²/(4 sensitivity)` loss certificate. -/
theorem waterFillingVector_welfare_loss_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) (b : ι → ℝ) (leader : ι)
    (hleader : ∀ i, b i ≤ b leader) :
    (weight : ℝ) * b leader -
        ∑ i, b i * waterFillingVector weight sensitivity hsens b i ≤
      (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  let threshold := waterFillingThreshold weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens b
  have h := waterFilling_welfare_loss_le weight sensitivity hweight hsens b leader hleader ht
  simpa only [waterFillingVector, threshold] using h

/-- All reduced-form membership properties claimed for water-filling in
Theorem `thm:pos(ii)`, collected in one kernel-checked declaration. -/
theorem waterFillingRule_membership
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    Anonymous (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) ∧
    OwnMonotone (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) ∧
    OwnLipschitz sensitivity (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) ∧
    CrossMonotone (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) ∧
    OneSlotFeasible (weight : ℝ) (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) ∧
    OneSlotNoWaste (weight : ℝ) (waterFillingRule (ι := ι) (reserve := reserve)
      weight sensitivity hsens) := by
  exact ⟨waterFillingRule_anonymous weight sensitivity hsens,
    waterFillingRule_ownMonotone weight sensitivity hsens,
    waterFillingRule_ownLipschitz weight sensitivity hsens,
    waterFillingRule_crossMonotone weight sensitivity hsens,
    waterFillingRule_feasible weight sensitivity hsens,
    waterFillingRule_noWaste weight sensitivity hsens⟩

/-- Eligible-profile version of the sharp worst-case welfare certificate. -/
theorem waterFillingRule_welfare_loss_le
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) (b : EligibleProfile ι reserve) (leader : ι)
    (hleader : ∀ i, (b i : ℝ) ≤ (b leader : ℝ)) :
    (weight : ℝ) * (b leader : ℝ) -
        welfare (waterFillingRule weight sensitivity hsens) b ≤
      (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  simpa only [welfare, waterFillingRule] using
    waterFillingVector_welfare_loss_le weight sensitivity hweight hsens
      (fun i => (b i : ℝ)) leader hleader

end SmoothingCliff.Frontier
