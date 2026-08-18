import SmoothingCliff.Racing.GeneralWelfareLoss

/-!
# The shared interface between ranking laws and interim allocations

The welfare development of `GeneralWelfareLoss.lean` states everything over a
`FiniteLaw (Equiv.Perm (Fin n))` and the realized welfare of a ranking.  The
racing development states everything over an agent's interim expected priority
weight.  Nothing connected the two, so the analytic content of
`prop:netsurplus_n` could not be composed into the proposition.

This file supplies the connection.  Under any ranking law, the expected
realized welfare equals the sum over agents of value times expected slot
weight, where the expected slot weight of an agent is her interim allocation.
The proof is a finite Fubini exchange combined with the reindexing of positions
by the inverse permutation.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Realized welfare of a ranking listed by position. -/
theorem rankingWelfareFrom_ofFn {n : ℕ} (weight : ℕ → ℝ) (offset : ℕ)
    (entry : Fin n → ℝ) :
    rankingWelfareFrom weight offset (List.ofFn entry) =
      ∑ position : Fin n, weight (offset + position) * entry position := by
  induction n generalizing offset with
  | zero => simp [rankingWelfareFrom]
  | succ m ih =>
    rw [List.ofFn_succ, rankingWelfareFrom, ih (offset + 1)]
    rw [Fin.sum_univ_succ]
    have hshift : ∀ position : Fin m,
        weight (offset + 1 + position) * entry position.succ =
          weight (offset + position.succ) * entry position.succ := by
      intro position
      congr 2
      simp [Fin.val_succ]
      omega
    simp only [hshift, Fin.val_zero, Nat.add_zero]

/-- Realized welfare of a ranking as a sum over positions. -/
theorem rankingWelfare_ofFn {n : ℕ} (weight : ℕ → ℝ) (entry : Fin n → ℝ) :
    rankingWelfare weight (List.ofFn entry) =
      ∑ position : Fin n, weight position * entry position := by
  simpa [rankingWelfare] using rankingWelfareFrom_ofFn weight 0 entry

/-- Realized welfare of a permutation ranking, indexed by agents rather than by
positions: agent `i` sits at position `ranking.symm i`. -/
theorem rankingWelfare_permutation_eq_agentSum
    {n : ℕ} (weight : ℕ → ℝ) (value : Fin n → ℝ)
    (ranking : Equiv.Perm (Fin n)) :
    rankingWelfare weight (permutationRankingValues n value ranking) =
      ∑ agent : Fin n, weight (ranking.symm agent) * value agent := by
  rw [permutationRankingValues, rankingWelfare_ofFn]
  exact Fintype.sum_equiv ranking _ _ fun position => by
    simp [Equiv.symm_apply_apply]

/-- The interim expected priority weight of an agent under a ranking law: the
expected weight of the slot she occupies. -/
def rankingInterimPriority {n : ℕ}
    (law : FiniteLaw (Equiv.Perm (Fin n))) (weight : ℕ → ℝ) (agent : Fin n) :
    ℝ :=
  finiteExpectation law fun ranking => weight (ranking.symm agent)

/-- **The bridge.**  Expected realized welfare under any ranking law is the sum
over agents of value times interim expected priority weight.  This is what lets
the welfare bounds of `lem:welfareloss`, stated over ranking laws, be composed
with the racing results, stated over interim allocations. -/
theorem finiteExpectation_rankingWelfare_eq_interimWelfare
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n)))
    (weight : ℕ → ℝ) (value : Fin n → ℝ) :
    finiteExpectation law
        (fun ranking =>
          rankingWelfare weight (permutationRankingValues n value ranking)) =
      ∑ agent : Fin n, value agent * rankingInterimPriority law weight agent := by
  simp only [finiteExpectation, rankingInterimPriority,
    rankingWelfare_permutation_eq_agentSum]
  have hpush : ∀ ranking : Equiv.Perm (Fin n),
      law.probability ranking *
          ∑ agent : Fin n, weight (ranking.symm agent) * value agent =
        ∑ agent : Fin n,
          law.probability ranking * weight (ranking.symm agent) *
            value agent := by
    intro ranking
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun agent _ => by ring
  rw [Finset.sum_congr rfl fun ranking _ => hpush ranking, Finset.sum_comm]
  refine Finset.sum_congr rfl fun agent _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ranking _ => by ring

/-- The interim allocations of a ranking law are nonnegative when the weights
are. -/
theorem rankingInterimPriority_nonneg
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n))) {weight : ℕ → ℝ}
    (hWeight : ∀ position, 0 ≤ weight position) (agent : Fin n) :
    0 ≤ rankingInterimPriority law weight agent :=
  Finset.sum_nonneg fun ranking _ =>
    mul_nonneg (law.probability_nonnegative ranking) (hWeight _)

/-- The interim allocations of a ranking law never exceed the top weight. -/
theorem rankingInterimPriority_le
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n))) {weight : ℕ → ℝ}
    {topWeight : ℝ} (hWeight : ∀ position, weight position ≤ topWeight)
    (agent : Fin n) :
    rankingInterimPriority law weight agent ≤ topWeight := by
  have hbound : ∀ ranking : Equiv.Perm (Fin n),
      law.probability ranking * weight (ranking.symm agent) ≤
        law.probability ranking * topWeight := fun ranking =>
    mul_le_mul_of_nonneg_left (hWeight _) (law.probability_nonnegative ranking)
  calc
    rankingInterimPriority law weight agent ≤
        ∑ ranking, law.probability ranking * topWeight :=
      Finset.sum_le_sum fun ranking _ => hbound ranking
    _ = topWeight := by
      rw [← Finset.sum_mul, law.probability_sum_one, one_mul]

/-- Total allocated priority mass under a ranking law is the total slot weight
of the `n` positions, independent of the law. -/
theorem sum_rankingInterimPriority
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n))) (weight : ℕ → ℝ) :
    ∑ agent : Fin n, rankingInterimPriority law weight agent =
      ∑ position : Fin n, weight position := by
  simp only [rankingInterimPriority, finiteExpectation]
  rw [Finset.sum_comm]
  have hinner : ∀ ranking : Equiv.Perm (Fin n),
      ∑ agent : Fin n, law.probability ranking * weight (ranking.symm agent) =
        law.probability ranking * ∑ position : Fin n, weight position := by
    intro ranking
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv ranking.symm _ _ fun agent => rfl
  rw [Finset.sum_congr rfl fun ranking _ => hinner ranking,
    ← Finset.sum_mul, law.probability_sum_one, one_mul]

end

end SmoothingCliff.Racing
