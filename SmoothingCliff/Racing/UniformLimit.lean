import SmoothingCliff.Racing.OneSlotInterim

/-!
# The uniform-lottery endpoint of the Plackett--Luce rule

Formal target: the high-temperature clause of Proposition `prop:revenue` in
`Smoothing_the_Cliff_ITCS.tex`.

As the temperature grows every reserve-adjusted intensity tends to one, and at
equal rates the Plackett--Luce law is exchangeable, so each agent's interim
allocation is the allocated priority mass divided by the number of eligible
agents.  Feeding that endpoint through the payment identity gives revenue equal
to the reserve times the allocated mass, which is the step
`Mechanism.totalPayment_tendsto_reserve_mul_mass` already provides.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Removing a chosen agent from a constant rate vector leaves it constant. -/
theorem removeChosenRate_const {n : ℕ} (c : ℝ) (first : Fin (n + 1)) :
    removeChosenRate (fun _ : Fin (n + 1) => c) first = fun _ : Fin n => c :=
  rfl

/-- At equal rates the recursive Plackett--Luce mass is uniform. -/
theorem plPermutationMass_const
    (n : ℕ) {c : ℝ} (hc : 0 < c) (ranking : Equiv.Perm (Fin n)) :
    plPermutationMass n (fun _ => c) ranking = (n.factorial : ℝ)⁻¹ := by
  induction n with
  | zero => simp [plPermutationMass]
  | succ m ih =>
    have hsum : ∑ _i : Fin (m + 1), c = (m + 1 : ℝ) * c := by
      simp [Finset.sum_const, nsmul_eq_mul]
    simp only [plPermutationMass, removeChosenRate_const]
    rw [ih _, hsum]
    have hne : ((m : ℝ) + 1) * c ≠ 0 := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp

/-- Exchangeability at equal rates: every agent has the same interim
allocation. -/
theorem rankingInterimPriority_const_congr
    {n : ℕ} (weight : ℕ → ℝ) {c : ℝ} (hc : ∀ _ : Fin n, 0 < c)
    (first second : Fin n) :
    rankingInterimPriority (plPermutationLaw n (fun _ => c) hc) weight first =
      rankingInterimPriority (plPermutationLaw n (fun _ => c) hc) weight
        second := by
  classical
  have hmass : ∀ ranking : Equiv.Perm (Fin n),
      (plPermutationLaw n (fun _ => c) hc).probability ranking =
        (n.factorial : ℝ)⁻¹ := by
    intro ranking
    exact plPermutationMass_const n (hc first) ranking
  simp only [rankingInterimPriority, finiteExpectation, hmass]
  refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap first second)) _ _ ?_
  intro ranking
  have hsymm :
      ((Equiv.mulLeft (Equiv.swap first second)) ranking).symm second =
        ranking.symm first := by
    have hmul : (Equiv.mulLeft (Equiv.swap first second)) ranking =
        (Equiv.swap first second) * ranking := rfl
    rw [hmul, Equiv.symm_apply_eq, Equiv.Perm.mul_apply,
      Equiv.apply_symm_apply, Equiv.swap_apply_left]
  rw [hsymm]

/-- **The uniform-lottery endpoint.**  At equal rates each agent's interim
allocation is the allocated priority mass divided by the number of agents. -/
theorem rankingInterimPriority_const_eq
    {n : ℕ} (weight : ℕ → ℝ) {c : ℝ} (hc : ∀ _ : Fin (n + 1), 0 < c)
    (agent : Fin (n + 1)) :
    rankingInterimPriority (plPermutationLaw (n + 1) (fun _ => c) hc) weight
        agent =
      (∑ position : Fin (n + 1), weight position) / (n + 1 : ℝ) := by
  have hsum := sum_rankingInterimPriority
    (plPermutationLaw (n + 1) (fun _ => c) hc) weight
  have hconst : ∀ other : Fin (n + 1),
      rankingInterimPriority (plPermutationLaw (n + 1) (fun _ => c) hc) weight
          other =
        rankingInterimPriority (plPermutationLaw (n + 1) (fun _ => c) hc)
          weight agent := fun other =>
    rankingInterimPriority_const_congr weight hc other agent
  rw [Finset.sum_congr rfl fun other _ => hconst other] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_succ] at hsum
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp at hsum ⊢
  linarith [hsum]

end

end SmoothingCliff.Racing
