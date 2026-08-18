import SmoothingCliff.Racing.InterimBridge
import SmoothingCliff.Racing.PLPermutationLaw
import SmoothingCliff.Racing.TemperatureMonotone

/-!
# The one-slot interim allocation of the Plackett--Luce law

This closes the last seam in Proposition `prop:netsurplus_n`.  The temperature
monotonicity of `TemperatureMonotone.lean` is proved over the softmax
representation, while everything else about the proposition is stated over the
interim allocations of `InterimBridge.lean`.  The two are identified here: the
first step of the Plackett--Luce recursion makes the probability of ranking
first equal to the rate share, so at a one-slot weight profile the interim
allocation is the top weight times that share, and interim welfare is the top
weight times the softmax mean.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- The probability that a given agent is ranked first under the recursive
Plackett--Luce mass is her rate share. -/
theorem plPermutationMass_first_eq
    {n : ℕ} (rate : Fin (n + 1) → ℝ) (hrate : ∀ i, 0 < rate i)
    (agent : Fin (n + 1)) :
    ∑ ranking : Equiv.Perm (Fin (n + 1)),
        plPermutationMass (n + 1) rate ranking *
          eventIndicator (ranking 0 = agent) =
      rate agent / ∑ i, rate i := by
  classical
  rw [← (Equiv.Perm.decomposeFin (n := n)).symm.sum_comp
    (fun ranking => plPermutationMass (n + 1) rate ranking *
      eventIndicator (ranking 0 = agent))]
  rw [Fintype.sum_prod_type]
  simp only [plPermutationMass, Equiv.apply_symm_apply,
    Equiv.Perm.decomposeFin_symm_apply_zero]
  have hstep : ∀ first : Fin (n + 1),
      (∑ tail : Equiv.Perm (Fin n),
          rate first / (∑ i, rate i) *
              plPermutationMass n (removeChosenRate rate first) tail *
            eventIndicator (first = agent)) =
        rate first / (∑ i, rate i) * eventIndicator (first = agent) := by
    intro first
    have hinner :
        (∑ tail : Equiv.Perm (Fin n),
            rate first / (∑ i, rate i) *
                plPermutationMass n (removeChosenRate rate first) tail *
              eventIndicator (first = agent)) =
          (rate first / (∑ i, rate i) * eventIndicator (first = agent)) *
            ∑ tail : Equiv.Perm (Fin n),
              plPermutationMass n (removeChosenRate rate first) tail := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun tail _ => by ring
    rw [hinner, plPermutationMass_sum_one n (removeChosenRate rate first)
      (fun i => hrate _), mul_one]
  rw [Finset.sum_congr rfl fun first _ => hstep first]
  simp [eventIndicator]

/-- A one-slot weight profile: the top weight at the first position and zero
afterwards. -/
def oneSlotWeight (topWeight : ℝ) : ℕ → ℝ :=
  fun position => if position = 0 then topWeight else 0

/-- At a one-slot weight profile the interim allocation is the top weight times
the probability of ranking first. -/
theorem rankingInterimPriority_oneSlot
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin (n + 1)))) (topWeight : ℝ)
    (agent : Fin (n + 1)) :
    rankingInterimPriority law (oneSlotWeight topWeight) agent =
      topWeight *
        finiteProbability law (fun ranking => ranking 0 = agent) := by
  classical
  simp only [rankingInterimPriority, finiteProbability, finiteExpectation,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ranking _ => ?_
  have hiff : ((ranking.symm agent : ℕ) = 0) ↔ (ranking 0 = agent) := by
    constructor
    · intro hzero
      have hfin : ranking.symm agent = 0 := Fin.val_eq_zero_iff.mp hzero
      rw [← hfin, Equiv.apply_symm_apply]
    · intro hfirst
      have hfin : ranking.symm agent = 0 := by
        rw [← hfirst, Equiv.symm_apply_apply]
      rw [hfin]
      rfl
  by_cases hfirst : ranking 0 = agent
  · simp only [oneSlotWeight, eventIndicator, if_pos (hiff.mpr hfirst),
      if_pos hfirst]
    ring
  · simp only [oneSlotWeight, eventIndicator,
      if_neg (fun hzero => hfirst (hiff.mp hzero)), if_neg hfirst]
    ring

/-- The one-slot interim allocation of the Plackett--Luce law is the top weight
times the agent's rate share. -/
theorem plLaw_rankingInterimPriority_oneSlot
    {n : ℕ} (value : Fin (n + 1) → ℝ) (reference tau topWeight : ℝ)
    (agent : Fin (n + 1)) :
    rankingInterimPriority
        (plPermutationLaw (n + 1) (shiftedExponentialRate value reference tau)
          (shiftedExponentialRate_positive value reference tau))
        (oneSlotWeight topWeight) agent =
      topWeight *
        (shiftedExponentialRate value reference tau agent /
          ∑ i, shiftedExponentialRate value reference tau i) := by
  classical
  rw [rankingInterimPriority_oneSlot]
  congr 1
  simpa [finiteProbability, finiteExpectation, plPermutationLaw] using
    plPermutationMass_first_eq (shiftedExponentialRate value reference tau)
      (shiftedExponentialRate_positive value reference tau) agent

/-- One-slot interim welfare under the Plackett--Luce law is the top weight
times the softmax mean.  This is the identification the temperature
monotonicity clause needed. -/
theorem plLaw_oneSlot_interimWelfare_eq
    {n : ℕ} (value : Fin (n + 1) → ℝ) (reference tau topWeight : ℝ)
    (hTau : tau ≠ 0) :
    ∑ agent : Fin (n + 1),
        value agent *
          rankingInterimPriority
            (plPermutationLaw (n + 1)
              (shiftedExponentialRate value reference tau)
              (shiftedExponentialRate_positive value reference tau))
            (oneSlotWeight topWeight) agent =
      topWeight * softmaxMean value (1 / tau) := by
  have hshare : ∀ agent : Fin (n + 1),
      shiftedExponentialRate value reference tau agent /
          ∑ i, shiftedExponentialRate value reference tau i =
        Real.exp ((1 / tau) * value agent) /
          softmaxPartition value (1 / tau) := by
    intro agent
    simpa [shiftedExponentialRate] using
      reserveAdjusted_share_eq_softmax_share value reference tau hTau agent
  have hterm : ∀ agent : Fin (n + 1),
      value agent *
          rankingInterimPriority
            (plPermutationLaw (n + 1)
              (shiftedExponentialRate value reference tau)
              (shiftedExponentialRate_positive value reference tau))
            (oneSlotWeight topWeight) agent =
        topWeight *
          (value agent * Real.exp ((1 / tau) * value agent) /
            softmaxPartition value (1 / tau)) := by
    intro agent
    rw [plLaw_rankingInterimPriority_oneSlot, hshare agent]
    ring
  rw [Finset.sum_congr rfl fun agent _ => hterm agent, ← Finset.mul_sum]
  congr 1
  rw [softmaxMean, softmaxFirstMoment, Finset.sum_div]

/-- **The one-slot monotonicity clause of `prop:netsurplus_n`, in interim
form.**  Expected one-slot welfare under the Plackett--Luce rule is
non-increasing in the temperature on the positive temperatures. -/
theorem plLaw_oneSlot_interimWelfare_antitoneOn
    {n : ℕ} (value : Fin (n + 1) → ℝ) (reference : ℝ) {topWeight : ℝ}
    (hTopWeight : 0 ≤ topWeight) :
    AntitoneOn
      (fun tau : ℝ =>
        ∑ agent : Fin (n + 1),
          value agent *
            rankingInterimPriority
              (plPermutationLaw (n + 1)
                (shiftedExponentialRate value reference tau)
                (shiftedExponentialRate_positive value reference tau))
              (oneSlotWeight topWeight) agent)
      (Set.Ioi 0) := by
  intro tau₁ h₁ tau₂ h₂ hle
  dsimp only
  rw [plLaw_oneSlot_interimWelfare_eq value reference tau₁ topWeight
      (ne_of_gt (Set.mem_Ioi.mp h₁)),
    plLaw_oneSlot_interimWelfare_eq value reference tau₂ topWeight
      (ne_of_gt (Set.mem_Ioi.mp h₂))]
  exact mul_le_mul_of_nonneg_left
    (softmaxMean_inverse_antitoneOn value h₁ h₂ hle) hTopWeight

end

end SmoothingCliff.Racing
