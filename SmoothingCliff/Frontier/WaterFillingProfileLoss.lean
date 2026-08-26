import SmoothingCliff.Frontier.FlatKMinimax

/-!
# Exact profile loss for one-slot water filling

This file formalizes Lemma `lem:wf-profile-loss`.  On an interior active set,
the threshold disappears through the exact-mass equation and allocation value
is mean value plus a variance term.  If one bidder is capped at the full slot
weight, exact mass makes every other allocation zero.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

noncomputable section

/-- Arithmetic mean of a value vector on a nonempty finite set. -/
def activeMean {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (d : ι → ℝ) : ℝ :=
  (∑ i ∈ A, d i) / (A.card : ℝ)

theorem sum_sub_activeMean_eq_zero
    {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (hA : A.Nonempty) (d : ι → ℝ) :
    ∑ i ∈ A, (d i - activeMean A d) = 0 := by
  have hcardNat : 0 < A.card := Finset.card_pos.mpr hA
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcardNat)
  unfold activeMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- On a fixed interior active set, eliminating the water level gives the
mean-plus-variance decomposition of allocation value. -/
theorem waterFillAt_active_value_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (hA : A.Nonempty)
    (weight slope : NNReal) (d : ι → ℝ) (threshold : ℝ)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (d i - threshold) ∧
        (slope : ℝ) * (d i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A, (slope : ℝ) * (d i - threshold) ≤ 0)
    (hMass : ∑ i, waterFillAt weight slope d threshold i = (weight : ℝ)) :
    ∑ i, d i * waterFillAt weight slope d threshold i =
      (slope : ℝ) * ∑ i ∈ A, (d i - activeMean A d) ^ 2 +
        (weight : ℝ) * activeMean A d := by
  let p : ι → ℝ := waterFillAt weight slope d threshold
  let μ : ℝ := activeMean A d
  have hpInside : ∀ i ∈ A, p i = (slope : ℝ) * (d i - threshold) := by
    intro i hi
    unfold p waterFillAt
    exact clampWeight_eq_of_mem weight (hInside i hi).1.le (hInside i hi).2.le
  have hpOutside : ∀ i ∉ A, p i = 0 := by
    intro i hi
    unfold p waterFillAt
    exact clampWeight_eq_zero_of_nonpos weight (hOutside i hi)
  have hMassA :
      ∑ i ∈ A, (slope : ℝ) * (d i - threshold) = (weight : ℝ) := by
    calc
      ∑ i ∈ A, (slope : ℝ) * (d i - threshold) = ∑ i ∈ A, p i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpInside i hi]
      _ = ∑ i, p i := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro i hiuniv hiA
        exact hpOutside i hiA
      _ = (weight : ℝ) := hMass
  have hCenter : ∑ i ∈ A, (d i - μ) = 0 := by
    exact sum_sub_activeMean_eq_zero A hA d
  have hPoint : ∀ i,
      d i * ((slope : ℝ) * (d i - threshold)) =
        (slope : ℝ) * (d i - μ) ^ 2 +
          μ * ((slope : ℝ) * (d i - threshold)) +
          ((slope : ℝ) * (μ - threshold)) * (d i - μ) := by
    intro i
    ring
  have hActiveValue :
      ∑ i ∈ A, d i * ((slope : ℝ) * (d i - threshold)) =
        (slope : ℝ) * ∑ i ∈ A, (d i - μ) ^ 2 +
          μ * ∑ i ∈ A, ((slope : ℝ) * (d i - threshold)) := by
    calc
      ∑ i ∈ A, d i * ((slope : ℝ) * (d i - threshold)) =
          ∑ i ∈ A,
            ((slope : ℝ) * (d i - μ) ^ 2 +
              μ * ((slope : ℝ) * (d i - threshold)) +
              ((slope : ℝ) * (μ - threshold)) * (d i - μ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hPoint i
      _ = (slope : ℝ) * ∑ i ∈ A, (d i - μ) ^ 2 +
          μ * ∑ i ∈ A, ((slope : ℝ) * (d i - threshold)) +
          ((slope : ℝ) * (μ - threshold)) * ∑ i ∈ A, (d i - μ) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (slope : ℝ) * ∑ i ∈ A, (d i - μ) ^ 2 +
          μ * ∑ i ∈ A, ((slope : ℝ) * (d i - threshold)) := by
        rw [hCenter]
        ring
  have hRestrict : ∑ i, d i * p i = ∑ i ∈ A, d i * p i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro i hiuniv hiA
    rw [hpOutside i hiA, mul_zero]
  calc
    ∑ i, d i * waterFillAt weight slope d threshold i =
        ∑ i, d i * p i := rfl
    _ = ∑ i ∈ A, d i * p i := hRestrict
    _ = ∑ i ∈ A, d i * ((slope : ℝ) * (d i - threshold)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpInside i hi]
    _ = (slope : ℝ) * ∑ i ∈ A, (d i - μ) ^ 2 +
        μ * ∑ i ∈ A, ((slope : ℝ) * (d i - threshold)) := hActiveValue
    _ = (slope : ℝ) * ∑ i ∈ A, (d i - μ) ^ 2 +
        (weight : ℝ) * μ := by rw [hMassA]; ring
    _ = (slope : ℝ) * ∑ i ∈ A, (d i - activeMean A d) ^ 2 +
        (weight : ℝ) * activeMean A d := rfl

/-- Lemma `lem:wf-profile-loss`, interior-active-set branch. -/
theorem waterFillAt_active_loss_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (d : ι → ℝ) (threshold : ℝ) (leader : ι)
    (hLeader : leader ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (d i - threshold) ∧
        (slope : ℝ) * (d i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A, (slope : ℝ) * (d i - threshold) ≤ 0)
    (hMass : ∑ i, waterFillAt weight slope d threshold i = (weight : ℝ)) :
    (weight : ℝ) * d leader -
        ∑ i, d i * waterFillAt weight slope d threshold i =
      (weight : ℝ) * (d leader - activeMean A d) -
        (slope : ℝ) * ∑ i ∈ A, (d i - activeMean A d) ^ 2 := by
  have hValue := waterFillAt_active_value_identity A ⟨leader, hLeader⟩
    weight slope d threshold
    hInside hOutside hMass
  rw [hValue]
  ring

/-- If one bidder receives the full slot under exact-mass water filling, every
other allocation is zero and the highest-value bidder incurs no loss. -/
theorem waterFillAt_loss_eq_zero_of_capped
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (d : ι → ℝ) (threshold : ℝ) (leader : ι)
    (hMass : ∑ i, waterFillAt weight slope d threshold i = (weight : ℝ))
    (hCapped : waterFillAt weight slope d threshold leader = (weight : ℝ)) :
    (weight : ℝ) * d leader -
        ∑ i, d i * waterFillAt weight slope d threshold i = 0 := by
  let p : ι → ℝ := waterFillAt weight slope d threshold
  have hCappedP : p leader = (weight : ℝ) := hCapped
  have hp0 : ∀ i, 0 ≤ p i := fun i => clampWeight_nonneg weight _
  have hRest : ∑ i ∈ (Finset.univ : Finset ι).erase leader, p i = 0 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι) p
      (Finset.mem_univ leader)
    change ∑ i, p i = (weight : ℝ) at hMass
    rw [hMass, hCappedP] at hsplit
    linarith
  have hzero : ∀ i ∈ (Finset.univ : Finset ι).erase leader, p i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => hp0 i)).mp hRest
  have hValue : ∑ i, d i * p i = d leader * (weight : ℝ) := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => d i * p i) (Finset.mem_univ leader)
    have hrestValue :
        ∑ i ∈ (Finset.univ : Finset ι).erase leader, d i * p i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i hi, mul_zero]
    rw [hrestValue] at hsplit
    change 0 + d leader * p leader = ∑ i, d i * p i at hsplit
    rw [hCappedP] at hsplit
    simpa using hsplit.symm
  change (weight : ℝ) * d leader - ∑ i, d i * p i = 0
  rw [hValue]
  ring

end

end SmoothingCliff.Frontier
