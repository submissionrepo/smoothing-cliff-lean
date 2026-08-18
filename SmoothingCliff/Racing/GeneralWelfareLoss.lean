import SmoothingCliff.Racing.WelfareLoss
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Tuple.Sort

/-!
# General top-K Plackett--Luce welfare loss

This file formalizes the general-slot part of Lemma `lem:welfareloss` in
`Smoothing_the_Cliff_ITCS.tex`.  The deterministic core is stated for lists,
which makes the adjacent-transposition argument explicit: insertion sort moves
each inverted pair past one another exactly once.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Gap contributed by a later, strictly higher value. -/
def pairInversionGap (earlier later : ℝ) : ℝ := max (later - earlier) 0

/-- Sum of value gaps over all inverted pairs in a realized ranking. -/
def inversionGap : List ℝ → ℝ
  | [] => 0
  | value :: tail =>
      (tail.map (pairInversionGap value)).sum + inversionGap tail

/-- Welfare of a finite ranking, starting at position `position`.  The weight
function is defined on all natural positions, implementing the paper's
extension by zero after the last genuine slot. -/
def rankingWelfareFrom (weight : ℕ → ℝ) : ℕ → List ℝ → ℝ
  | _, [] => 0
  | position, value :: tail =>
      weight position * value + rankingWelfareFrom weight (position + 1) tail

def rankingWelfare (weight : ℕ → ℝ) (ranking : List ℝ) : ℝ :=
  rankingWelfareFrom weight 0 ranking

/-- Strict-priority welfare is welfare after sorting values in descending
order. This definition does not require choosing names for agents. -/
def strictPriorityWelfare (weight : ℕ → ℝ) (ranking : List ℝ) : ℝ :=
  rankingWelfare weight
    (List.insertionSort (fun a b : ℝ => b ≤ a) ranking)

/-- Paper-faithful assumptions on the zero-extended slot-weight sequence. -/
structure ExtendedSlotWeights (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ) : Prop where
  nonnegative : ∀ position, 0 ≤ weight position
  antitone : Antitone weight
  zero_after : ∀ position, slots ≤ position → weight position = 0
  adjacent_drop_le : ∀ position,
    weight position - weight (position + 1) ≤ barDrop
  barDrop_nonnegative : 0 ≤ barDrop

theorem pairInversionGap_nonnegative (earlier later : ℝ) :
    0 ≤ pairInversionGap earlier later := by
  simp [pairInversionGap]

theorem map_pairInversionGap_sum_nonnegative (value : ℝ) (tail : List ℝ) :
    0 ≤ (tail.map (pairInversionGap value)).sum := by
  apply List.sum_nonneg
  intro gap hgap
  rcases List.mem_map.mp hgap with ⟨later, hlater, rfl⟩
  exact pairInversionGap_nonnegative value later

/-- Reordering two adjacent elements leaves the sum of any elementwise
statistic unchanged. -/
theorem map_sum_adjacent_swap (f : ℝ → ℝ) (pre suffix : List ℝ) (x y : ℝ) :
    (List.map f (pre ++ x :: y :: suffix)).sum =
      (List.map f (pre ++ y :: x :: suffix)).sum := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  ring

/-- Correcting an adjacent inversion reduces `inversionGap` by exactly that
pair's value gap. -/
theorem inversionGap_adjacent_correction
    (pre suffix : List ℝ) (lower higher : ℝ) (h : lower ≤ higher) :
    inversionGap (pre ++ lower :: higher :: suffix) =
      (higher - lower) +
        inversionGap (pre ++ higher :: lower :: suffix) := by
  induction pre with
  | nil =>
      simp only [List.nil_append, inversionGap, List.map_cons, List.sum_cons]
      have hpos : max (higher - lower) 0 = higher - lower :=
        max_eq_left (sub_nonneg.mpr h)
      have hzero : max (lower - higher) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr h)
      simp only [pairInversionGap, hpos, hzero, zero_add]
      ring
  | cons value pre ih =>
      simp only [List.cons_append, inversionGap]
      rw [map_sum_adjacent_swap, ih]
      ring

/-- Inserting one value into a ranking is an adjacent-sort pass. Its welfare
gain is bounded by `barDrop` times precisely the inverted gaps crossed. -/
theorem orderedInsert_welfare_loss_le
    (weight : ℕ → ℝ) (barDrop : ℝ) (hbar : 0 ≤ barDrop)
    (hdrop : ∀ position,
      weight position - weight (position + 1) ≤ barDrop)
    (position : ℕ) (value : ℝ) (ranking : List ℝ) :
    rankingWelfareFrom weight position
        (List.orderedInsert (fun a b : ℝ => b ≤ a) value ranking) -
      rankingWelfareFrom weight position (value :: ranking) ≤
        barDrop * (ranking.map (pairInversionGap value)).sum := by
  induction ranking generalizing position with
  | nil =>
      simp [rankingWelfareFrom]
  | cons next ranking ih =>
      by_cases hnext : next ≤ value
      · rw [List.orderedInsert_cons, if_pos hnext]
        simp only [sub_self]
        exact mul_nonneg hbar
          (map_pairInversionGap_sum_nonnegative value (next :: ranking))
      · have hvalue : value < next := lt_of_not_ge hnext
        rw [List.orderedInsert_cons, if_neg hnext]
        have hlocal :
            (weight position - weight (position + 1)) * (next - value) ≤
              barDrop * (next - value) :=
          mul_le_mul_of_nonneg_right (hdrop position)
            (sub_nonneg.mpr hvalue.le)
        have htail := ih (position + 1)
        simp only [rankingWelfareFrom, List.map_cons, List.sum_cons,
          pairInversionGap, max_eq_left (sub_nonneg.mpr hvalue.le)]
        calc
          weight position * next +
                  rankingWelfareFrom weight (position + 1)
                    (List.orderedInsert (fun a b : ℝ => b ≤ a) value ranking) -
                (weight position * value +
                  (weight (position + 1) * next +
                    rankingWelfareFrom weight (position + 1 + 1) ranking)) =
              (weight position - weight (position + 1)) * (next - value) +
                (rankingWelfareFrom weight (position + 1)
                    (List.orderedInsert (fun a b : ℝ => b ≤ a) value ranking) -
                  rankingWelfareFrom weight (position + 1) (value :: ranking)) := by
            simp only [rankingWelfareFrom]
            ring
          _ ≤ barDrop * (next - value) +
                barDrop * (List.map (pairInversionGap value) ranking).sum :=
            add_le_add hlocal htail
          _ = barDrop *
                ((next - value) +
                  (List.map (pairInversionGap value) ranking).sum) := by ring

/-- An adjacent insertion-sort pass cannot reduce welfare when slot weights
are nonincreasing. -/
theorem orderedInsert_welfare_gain_nonnegative
    (weight : ℕ → ℝ) (hantitone : Antitone weight)
    (position : ℕ) (value : ℝ) (ranking : List ℝ) :
    0 ≤ rankingWelfareFrom weight position
          (List.orderedInsert (fun a b : ℝ => b ≤ a) value ranking) -
        rankingWelfareFrom weight position (value :: ranking) := by
  induction ranking generalizing position with
  | nil =>
      simp [rankingWelfareFrom]
  | cons next ranking ih =>
      by_cases hnext : next ≤ value
      · rw [List.orderedInsert_cons, if_pos hnext]
        simp
      · have hvalue : value < next := lt_of_not_ge hnext
        rw [List.orderedInsert_cons, if_neg hnext]
        have hlocal :
            0 ≤ (weight position - weight (position + 1)) *
              (next - value) :=
          mul_nonneg
            (sub_nonneg.mpr (hantitone (Nat.le_add_right position 1)))
            (sub_nonneg.mpr hvalue.le)
        have htail := ih (position + 1)
        calc
          0 ≤ (weight position - weight (position + 1)) *
                (next - value) +
              (rankingWelfareFrom weight (position + 1)
                  (List.orderedInsert (fun a b : ℝ => b ≤ a) value ranking) -
                rankingWelfareFrom weight (position + 1)
                  (value :: ranking)) :=
            add_nonneg hlocal htail
          _ = rankingWelfareFrom weight position
                  (next :: List.orderedInsert
                    (fun a b : ℝ => b ≤ a) value ranking) -
                rankingWelfareFrom weight position
                  (value :: next :: ranking) := by
            simp only [rankingWelfareFrom]
            ring

/-- Descending insertion sort maximizes welfare for an antitone weight
sequence, giving the lower half of the paper's welfare-loss inequality. -/
theorem deterministic_welfare_loss_nonnegative
    (weight : ℕ → ℝ) (hantitone : Antitone weight)
    (position : ℕ) (ranking : List ℝ) :
    0 ≤ rankingWelfareFrom weight position
          (List.insertionSort (fun a b : ℝ => b ≤ a) ranking) -
        rankingWelfareFrom weight position ranking := by
  induction ranking generalizing position with
  | nil =>
      simp [rankingWelfareFrom]
  | cons value tail ih =>
      rw [List.insertionSort_cons]
      have hinsert := orderedInsert_welfare_gain_nonnegative
        weight hantitone position value
          (List.insertionSort (fun a b : ℝ => b ≤ a) tail)
      have htail := ih (position + 1)
      calc
        0 ≤ (rankingWelfareFrom weight position
                (List.orderedInsert (fun a b : ℝ => b ≤ a) value
                  (List.insertionSort (fun a b : ℝ => b ≤ a) tail)) -
              rankingWelfareFrom weight position
                (value :: List.insertionSort
                  (fun a b : ℝ => b ≤ a) tail)) +
            (rankingWelfareFrom weight position
                (value :: List.insertionSort
                  (fun a b : ℝ => b ≤ a) tail) -
              rankingWelfareFrom weight position (value :: tail)) := by
          apply add_nonneg hinsert
          simpa only [rankingWelfareFrom, add_sub_add_left_eq_sub] using htail
        _ = rankingWelfareFrom weight position
                (List.orderedInsert (fun a b : ℝ => b ≤ a) value
                  (List.insertionSort (fun a b : ℝ => b ≤ a) tail)) -
              rankingWelfareFrom weight position (value :: tail) := by ring

/-- Deterministic adjacent-sort theorem behind Lemma `lem:welfareloss`:
strict-priority welfare minus realized-ranking welfare is at most the maximum
adjacent weight drop times the sum of inverted-pair value gaps. -/
theorem deterministic_inversion_welfare_loss_le
    (weight : ℕ → ℝ) (barDrop : ℝ) (hbar : 0 ≤ barDrop)
    (hdrop : ∀ position,
      weight position - weight (position + 1) ≤ barDrop)
    (position : ℕ) (ranking : List ℝ) :
    rankingWelfareFrom weight position
        (List.insertionSort (fun a b : ℝ => b ≤ a) ranking) -
      rankingWelfareFrom weight position ranking ≤
        barDrop * inversionGap ranking := by
  induction ranking generalizing position with
  | nil =>
      simp [rankingWelfareFrom, inversionGap]
  | cons value tail ih =>
      rw [List.insertionSort_cons]
      have hinsert := orderedInsert_welfare_loss_le weight barDrop hbar hdrop
        position value (List.insertionSort (fun a b : ℝ => b ≤ a) tail)
      have htail := ih (position + 1)
      have hperm := List.perm_insertionSort (fun a b : ℝ => b ≤ a) tail
      have hhead :
          ((List.insertionSort (fun a b : ℝ => b ≤ a) tail).map
              (pairInversionGap value)).sum =
            (tail.map (pairInversionGap value)).sum :=
        (hperm.map (pairInversionGap value)).sum_eq
      calc
        rankingWelfareFrom weight position
              (List.orderedInsert (fun a b : ℝ => b ≤ a) value
                (List.insertionSort (fun a b : ℝ => b ≤ a) tail)) -
            rankingWelfareFrom weight position (value :: tail) =
          (rankingWelfareFrom weight position
              (List.orderedInsert (fun a b : ℝ => b ≤ a) value
                (List.insertionSort (fun a b : ℝ => b ≤ a) tail)) -
            rankingWelfareFrom weight position
              (value :: List.insertionSort (fun a b : ℝ => b ≤ a) tail)) +
          (rankingWelfareFrom weight position
              (value :: List.insertionSort (fun a b : ℝ => b ≤ a) tail) -
            rankingWelfareFrom weight position (value :: tail)) := by ring
        _ ≤ barDrop *
              ((List.insertionSort (fun a b : ℝ => b ≤ a) tail).map
                (pairInversionGap value)).sum +
            barDrop * inversionGap tail := by
          apply add_le_add hinsert
          simpa only [rankingWelfareFrom, add_sub_add_left_eq_sub] using htail
        _ = barDrop * inversionGap (value :: tail) := by
          simp only [inversionGap, hhead]
          ring

/-- Zero-extended top-K wrapper of the deterministic theorem. -/
theorem generalTopK_deterministic_welfare_loss_le
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : List ℝ) :
    strictPriorityWelfare weight ranking - rankingWelfare weight ranking ≤
      barDrop * inversionGap ranking := by
  exact deterministic_inversion_welfare_loss_le weight barDrop
    hweight.barDrop_nonnegative hweight.adjacent_drop_le 0 ranking

theorem generalTopK_deterministic_welfare_loss_nonnegative
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : List ℝ) :
    0 ≤ strictPriorityWelfare weight ranking -
      rankingWelfare weight ranking := by
  exact deterministic_welfare_loss_nonnegative
    weight hweight.antitone 0 ranking

/-- Values in the order specified by a finite ranking permutation. -/
def permutationRankingValues (n : ℕ) (value : Fin n → ℝ)
    (ranking : Equiv.Perm (Fin n)) : List ℝ :=
  List.ofFn fun position => value (ranking position)

/-- A descending insertion sort depends only on the multiset of values. -/
theorem descending_insertionSort_eq_of_perm
    (left right : List ℝ) (hperm : left.Perm right) :
    List.insertionSort (fun a b : ℝ => b ≤ a) left =
      List.insertionSort (fun a b : ℝ => b ≤ a) right := by
  have hsortedLeft :
      (List.insertionSort (fun a b : ℝ => b ≤ a) left).SortedGE :=
    List.sortedGE_insertionSort
  have hsortedRight :
      (List.insertionSort (fun a b : ℝ => b ≤ a) right).SortedGE :=
    List.sortedGE_insertionSort
  have hsortedPerm :
      (List.insertionSort (fun a b : ℝ => b ≤ a) left).Perm
        (List.insertionSort (fun a b : ℝ => b ≤ a) right) :=
    (List.perm_insertionSort _ left).trans
      (hperm.trans (List.perm_insertionSort _ right).symm)
  have hsublist :
      (List.insertionSort (fun a b : ℝ => b ≤ a) left).Sublist
        (List.insertionSort (fun a b : ℝ => b ≤ a) right) :=
    List.sublist_of_subperm_of_sortedGE hsortedPerm.subperm
      hsortedLeft hsortedRight
  exact hsublist.eq_of_length hsortedPerm.length_eq

theorem permutationRankingValues_perm_profile
    (n : ℕ) (value : Fin n → ℝ) (ranking : Equiv.Perm (Fin n)) :
    (permutationRankingValues n value ranking).Perm (List.ofFn value) := by
  simpa [permutationRankingValues, Function.comp_def] using
    (ranking.ofFn_comp_perm value)

/-- Every permutation of a fixed value profile has the same strict-priority
welfare. -/
theorem strictPriorityWelfare_permutation_eq_profile
    (n : ℕ) (weight : ℕ → ℝ) (value : Fin n → ℝ)
    (ranking : Equiv.Perm (Fin n)) :
    strictPriorityWelfare weight (permutationRankingValues n value ranking) =
      strictPriorityWelfare weight (List.ofFn value) := by
  unfold strictPriorityWelfare
  rw [descending_insertionSort_eq_of_perm _ _
    (permutationRankingValues_perm_profile n value ranking)]

/-- The deterministic bound applies to every finite ranking/permutation. -/
theorem permutation_deterministic_welfare_loss_le
    (n : ℕ) (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (ranking : Equiv.Perm (Fin n)) :
    strictPriorityWelfare weight (permutationRankingValues n value ranking) -
        rankingWelfare weight (permutationRankingValues n value ranking) ≤
      barDrop * inversionGap (permutationRankingValues n value ranking) :=
  generalTopK_deterministic_welfare_loss_le weight slots barDrop hweight _

/-! ## Finite ranking laws and genuine finite expectations -/

/-- A finite probability law, represented by its probability mass function. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  probability : Ω → ℝ
  probability_nonnegative : ∀ outcome, 0 ≤ probability outcome
  probability_sum_one : ∑ outcome, probability outcome = 1

/-- Expectation with respect to a finite probability mass function. -/
def finiteExpectation {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (randomVariable : Ω → ℝ) : ℝ :=
  ∑ outcome, law.probability outcome * randomVariable outcome

/-- Indicator of an event, valued in the reals. -/
def eventIndicator (event : Prop) [Decidable event] : ℝ :=
  if event then 1 else 0

/-- Probability of an event under a finite probability law. -/
def finiteProbability {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (event : Ω → Prop) [DecidablePred event] : ℝ :=
  finiteExpectation law fun outcome => eventIndicator (event outcome)

theorem finiteExpectation_mono {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (x y : Ω → ℝ)
    (hxy : ∀ outcome, x outcome ≤ y outcome) :
    finiteExpectation law x ≤ finiteExpectation law y := by
  classical
  apply Finset.sum_le_sum
  intro outcome houtcome
  exact mul_le_mul_of_nonneg_left (hxy outcome)
    (law.probability_nonnegative outcome)

/-- Taking a finite expectation of the deterministic adjacent-sort theorem.
The expectation inequality is derived pointwise, rather than assumed. -/
theorem finiteRanking_expected_welfare_loss_le
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) :
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
      barDrop * finiteExpectation law (fun outcome =>
        inversionGap (ranking outcome)) := by
  calc
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
        finiteExpectation law (fun outcome =>
          barDrop * inversionGap (ranking outcome)) :=
      finiteExpectation_mono law _ _ fun outcome =>
        generalTopK_deterministic_welfare_loss_le
          weight slots barDrop hweight (ranking outcome)
    _ = barDrop * finiteExpectation law (fun outcome =>
          inversionGap (ranking outcome)) := by
      simp only [finiteExpectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outcome houtcome
      ring

theorem finiteRanking_expected_welfare_loss_nonnegative
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) :
    0 ≤ finiteExpectation law (fun outcome =>
      strictPriorityWelfare weight (ranking outcome) -
        rankingWelfare weight (ranking outcome)) := by
  have hmono := finiteExpectation_mono law
    (fun _outcome => 0)
    (fun outcome => strictPriorityWelfare weight (ranking outcome) -
      rankingWelfare weight (ranking outcome))
    (fun outcome =>
      generalTopK_deterministic_welfare_loss_nonnegative
        weight slots barDrop hweight (ranking outcome))
  simpa [finiteExpectation] using hmono

/-- Finite Fubini identity for a statistic decomposed into pair events. -/
theorem finiteExpectation_pair_decomposition
    {Ω Pair : Type*} [Fintype Ω] [Fintype Pair]
    (law : FiniteLaw Ω) (statistic : Ω → ℝ)
    (gap : Pair → ℝ) (inverted : Ω → Pair → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      statistic outcome =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair)) :
    finiteExpectation law statistic =
      ∑ pair, gap pair *
        finiteProbability law (fun outcome => inverted outcome pair) := by
  classical
  simp only [finiteExpectation, finiteProbability]
  calc
    (∑ outcome, law.probability outcome * statistic outcome) =
        ∑ outcome, ∑ pair,
          law.probability outcome *
            (gap pair * eventIndicator (inverted outcome pair)) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      rw [hdecomp outcome, Finset.mul_sum]
    _ = ∑ pair, ∑ outcome,
          law.probability outcome *
            (gap pair * eventIndicator (inverted outcome pair)) := by
      rw [Finset.sum_comm]
    _ = ∑ pair, gap pair *
          ∑ outcome, law.probability outcome *
            eventIndicator (inverted outcome pair) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outcome houtcome
      ring

/-- The general top-K pairwise bound for any actual finite ranking law whose
inversion events have the stated pair marginals. -/
theorem finiteRanking_expected_pairwise_welfare_loss_le
    {Ω Pair : Type*} [Fintype Ω] [Fintype Pair]
    (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) (gap : Pair → ℝ)
    (inverted : Ω → Pair → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      inversionGap (ranking outcome) =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair))
    (hmarginal : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        Real.sigmoid (-gap pair / tau)) :
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
      barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) := by
  have hdet := finiteRanking_expected_welfare_loss_le
    law weight slots barDrop hweight ranking
  have hpair := finiteExpectation_pair_decomposition
    law (fun outcome => inversionGap (ranking outcome)) gap inverted hdecomp
  calc
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
        barDrop * finiteExpectation law (fun outcome =>
          inversionGap (ranking outcome)) := hdet
    _ = barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) := by
      rw [hpair]
      congr 1
      apply Finset.sum_congr rfl
      intro pair hpair_mem
      rw [hmarginal pair]

/-! ## Exact two-clock exponential-race marginal -/

/-- Probability mass of the two possible orders of two exponential clocks.
`lowerFirst = true` denotes that the lower-valued agent's clock rings first.
The rates are `exp(value / tau)`, as in the paper. -/
def exponentialRacePairMass (highValue lowValue tau : ℝ)
    (lowerFirst : Bool) : ℝ :=
  if lowerFirst then
    Real.exp (lowValue / tau) /
      (Real.exp (highValue / tau) + Real.exp (lowValue / tau))
  else
    Real.exp (highValue / tau) /
      (Real.exp (highValue / tau) + Real.exp (lowValue / tau))

theorem exponentialRacePairMass_nonnegative
    (highValue lowValue tau : ℝ) (outcome : Bool) :
    0 ≤ exponentialRacePairMass highValue lowValue tau outcome := by
  cases outcome <;> simp [exponentialRacePairMass] <;> positivity

/-- The two exponential-clock orders form an actual finite probability law. -/
def exponentialRacePairLaw (highValue lowValue tau : ℝ) : FiniteLaw Bool where
  probability := exponentialRacePairMass highValue lowValue tau
  probability_nonnegative :=
    exponentialRacePairMass_nonnegative highValue lowValue tau
  probability_sum_one := by
    simp [exponentialRacePairMass]
    have hden :
        Real.exp (highValue / tau) + Real.exp (lowValue / tau) ≠ 0 :=
      ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
    field_simp
    ring

/-- The exponential-race rate ratio is exactly the negative-gap sigmoid. -/
theorem exponentialRace_rateRatio_eq_sigmoid
    (highValue lowValue tau : ℝ) :
    Real.exp (lowValue / tau) /
        (Real.exp (highValue / tau) + Real.exp (lowValue / tau)) =
      Real.sigmoid (-(highValue - lowValue) / tau) := by
  rw [Real.sigmoid_def]
  have hrewrite :
      -(-(highValue - lowValue) / tau) =
        highValue / tau - lowValue / tau := by ring
  rw [hrewrite, Real.exp_sub]
  have hhigh : Real.exp (highValue / tau) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hlow : Real.exp (lowValue / tau) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  field_simp
  ring

/-- Exact pair inversion probability in the finite order law induced by the
two exponential clocks. -/
theorem exponentialRace_pair_inversion_probability
    (highValue lowValue tau : ℝ) :
    finiteProbability (exponentialRacePairLaw highValue lowValue tau)
        (fun lowerFirst => lowerFirst = true) =
      Real.sigmoid (-(highValue - lowValue) / tau) := by
  rw [← exponentialRace_rateRatio_eq_sigmoid highValue lowValue tau]
  simp [finiteProbability, finiteExpectation, eventIndicator,
    exponentialRacePairLaw, exponentialRacePairMass]

/-- If every pair marginal of a finite ranking law is the finite order law of
its two exponential clocks, then its inversion probability is the paper's
sigmoid expression.  This isolates the probabilistic content from the
adjacent-sort and finite-Fubini arguments. -/
theorem exponentialRace_consistent_marginal_eq_sigmoid
    {Ω Pair : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (gap : Pair → ℝ) (tau : ℝ)
    (inverted : Ω → Pair → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hpairLaw : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true)) :
    ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        Real.sigmoid (-gap pair / tau) := by
  intro pair
  rw [hpairLaw pair]
  simpa using exponentialRace_pair_inversion_probability (gap pair) 0 tau

/-- Pairwise expected welfare bound specialized to exponential-race-consistent
finite ranking marginals; no sigmoid marginal is assumed. -/
theorem finiteRanking_exponentialRace_expected_pairwise_welfare_loss_le
    {Ω Pair : Type*} [Fintype Ω] [Fintype Pair]
    (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) (gap : Pair → ℝ)
    (inverted : Ω → Pair → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      inversionGap (ranking outcome) =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true)) :
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
      barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) := by
  apply finiteRanking_expected_pairwise_welfare_loss_le
    law weight slots barDrop tau hweight ranking gap inverted hdecomp
  exact exponentialRace_consistent_marginal_eq_sigmoid
    law gap tau inverted hpairLaw

/-! ## Pairwise and binomial welfare bounds -/

/-- Applying the paper's scalar sigmoid estimate to every member of a finite
pair index type. -/
theorem pairwise_gap_mul_sigmoid_sum_le_card
    {Pair : Type*} [Fintype Pair] (gap : Pair → ℝ) (tau : ℝ)
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    (∑ pair, gap pair * Real.sigmoid (-gap pair / tau)) ≤
      (Fintype.card Pair : ℝ) * (tau / Real.exp 1) := by
  calc
    (∑ pair, gap pair * Real.sigmoid (-gap pair / tau)) ≤
        ∑ _pair : Pair, tau / Real.exp 1 := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact gap_mul_sigmoid_le_tau_div_exp_one
        (gap pair) tau (hgap pair) htau
    _ = (Fintype.card Pair : ℝ) * (tau / Real.exp 1) := by simp

/-- There are exactly `n.choose 2` unordered pairs, encoded by a finite type
of that cardinality. -/
theorem pairwise_gap_mul_sigmoid_sum_le_choose_two
    (n : ℕ) (gap : Fin (n.choose 2) → ℝ) (tau : ℝ)
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    (∑ pair, gap pair * Real.sigmoid (-gap pair / tau)) ≤
      (n.choose 2 : ℝ) * (tau / Real.exp 1) := by
  simpa using
    (pairwise_gap_mul_sigmoid_sum_le_card gap tau hgap htau)

/-- The paper's general top-K expected welfare-loss bound, for a finite
ranking law with its `n.choose 2` pair events explicitly decomposed and with
the exact exponential-race sigmoid marginals. -/
theorem finiteRanking_expected_welfare_loss_le_choose_two
    {Ω : Type*} [Fintype Ω] (n : ℕ) (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Ω → Fin (n.choose 2) → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      inversionGap (ranking outcome) =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair))
    (hmarginal : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        Real.sigmoid (-gap pair / tau))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  have hpairwise := finiteRanking_expected_pairwise_welfare_loss_le
    law weight slots barDrop tau hweight ranking gap inverted hdecomp hmarginal
  have hbinomial :=
    pairwise_gap_mul_sigmoid_sum_le_choose_two n gap tau hgap htau
  calc
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
        barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) :=
      hpairwise
    _ ≤ barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) :=
      mul_le_mul_of_nonneg_left hbinomial hweight.barDrop_nonnegative

/-- Binomial general top-K bound with exponential-race pair laws as the
probabilistic premise, rather than the sigmoid formula itself. -/
theorem finiteRanking_exponentialRace_expected_welfare_loss_le_choose_two
    {Ω : Type*} [Fintype Ω] (n : ℕ) (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Ω → Fin (n.choose 2) → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      inversionGap (ranking outcome) =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  have hpairwise :=
    finiteRanking_exponentialRace_expected_pairwise_welfare_loss_le
      law weight slots barDrop tau hweight ranking gap inverted
        hdecomp hpairLaw
  have hbinomial :=
    pairwise_gap_mul_sigmoid_sum_le_choose_two n gap tau hgap htau
  calc
    finiteExpectation law (fun outcome =>
        strictPriorityWelfare weight (ranking outcome) -
          rankingWelfare weight (ranking outcome)) ≤
        barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) :=
      hpairwise
    _ ≤ barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) :=
      mul_le_mul_of_nonneg_left hbinomial hweight.barDrop_nonnegative

/-- Expectation of a constant minus a finite random variable. -/
theorem finiteExpectation_const_sub
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (constant : ℝ) (randomVariable : Ω → ℝ) :
    finiteExpectation law (fun outcome => constant - randomVariable outcome) =
      constant - finiteExpectation law randomVariable := by
  classical
  simp only [finiteExpectation]
  calc
    (∑ outcome,
        law.probability outcome * (constant - randomVariable outcome)) =
        ∑ outcome,
          (constant * law.probability outcome -
            law.probability outcome * randomVariable outcome) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      ring
    _ = (∑ outcome, constant * law.probability outcome) -
          ∑ outcome,
            law.probability outcome * randomVariable outcome := by
      rw [Finset.sum_sub_distrib]
    _ = constant * (∑ outcome, law.probability outcome) -
          ∑ outcome,
            law.probability outcome * randomVariable outcome := by
      rw [Finset.mul_sum]
    _ = constant -
          ∑ outcome,
            law.probability outcome * randomVariable outcome := by
      rw [law.probability_sum_one]
      ring

/-- Paper-form statement `W_SP - E[W]`: it follows from the expected-loss
form whenever every outcome is a ranking of the same value profile, hence has
the same strict-priority welfare. -/
theorem strictPriorityWelfare_sub_expected_le_choose_two
    {Ω : Type*} [Fintype Ω] (n : ℕ) (law : FiniteLaw Ω)
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau optimum : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (ranking : Ω → List ℝ)
    (hoptimum : ∀ outcome,
      strictPriorityWelfare weight (ranking outcome) = optimum)
    (gap : Fin (n.choose 2) → ℝ)
    (inverted : Ω → Fin (n.choose 2) → Prop)
    [∀ outcome pair, Decidable (inverted outcome pair)]
    (hdecomp : ∀ outcome,
      inversionGap (ranking outcome) =
        ∑ pair, gap pair * eventIndicator (inverted outcome pair))
    (hmarginal : ∀ pair,
      finiteProbability law (fun outcome => inverted outcome pair) =
        Real.sigmoid (-gap pair / tau))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    optimum - finiteExpectation law (fun outcome =>
        rankingWelfare weight (ranking outcome)) ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  have hexpected := finiteRanking_expected_welfare_loss_le_choose_two
    n law weight slots barDrop tau hweight ranking gap inverted
      hdecomp hmarginal hgap htau
  calc
    optimum - finiteExpectation law (fun outcome =>
        rankingWelfare weight (ranking outcome)) =
        finiteExpectation law (fun outcome =>
          optimum - rankingWelfare weight (ranking outcome)) := by
      symm
      exact finiteExpectation_const_sub law optimum _
    _ = finiteExpectation law (fun outcome =>
          strictPriorityWelfare weight (ranking outcome) -
            rankingWelfare weight (ranking outcome)) := by
      apply congrArg (finiteExpectation law)
      funext outcome
      rw [hoptimum outcome]
    _ ≤ barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) :=
      hexpected

/-- Fully specialized paper-form wrapper for an actual finite law on
permutations of one fixed finite value profile.  Strict-priority welfare is
now proved constant, rather than supplied as a premise. -/
theorem permutationLaw_strictPriorityWelfare_sub_expected_le_choose_two
    (n : ℕ) (law : FiniteLaw (Equiv.Perm (Fin n)))
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Equiv.Perm (Fin n) → Fin (n.choose 2) → Prop)
    [∀ ranking pair, Decidable (inverted ranking pair)]
    (hdecomp : ∀ ranking,
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair, gap pair * eventIndicator (inverted ranking pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun ranking => inverted ranking pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    strictPriorityWelfare weight (List.ofFn value) -
        finiteExpectation law (fun ranking =>
          rankingWelfare weight
            (permutationRankingValues n value ranking)) ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  exact strictPriorityWelfare_sub_expected_le_choose_two
    n law weight slots barDrop tau
      (strictPriorityWelfare weight (List.ofFn value)) hweight
      (fun ranking => permutationRankingValues n value ranking)
      (strictPriorityWelfare_permutation_eq_profile n weight value)
      gap inverted hdecomp
      (exponentialRace_consistent_marginal_eq_sigmoid
        law gap tau inverted hpairLaw)
      hgap htau

/-- The complete three-stage inequality from the general top-K part of
`lem:welfareloss`: nonnegative loss, the pairwise sigmoid bound, and the
uniform `n.choose 2` bound. -/
theorem permutationLaw_generalTopK_welfare_loss_bounds
    (n : ℕ) (law : FiniteLaw (Equiv.Perm (Fin n)))
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Equiv.Perm (Fin n) → Fin (n.choose 2) → Prop)
    [∀ ranking pair, Decidable (inverted ranking pair)]
    (hdecomp : ∀ ranking,
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair, gap pair * eventIndicator (inverted ranking pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun ranking => inverted ranking pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    let welfareLoss :=
      strictPriorityWelfare weight (List.ofFn value) -
        finiteExpectation law (fun ranking =>
          rankingWelfare weight
            (permutationRankingValues n value ranking))
    0 ≤ welfareLoss ∧
      welfareLoss ≤
        barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) ∧
      barDrop * ∑ pair, gap pair * Real.sigmoid (-gap pair / tau) ≤
        barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  dsimp only
  have hlossEq :
      strictPriorityWelfare weight (List.ofFn value) -
          finiteExpectation law (fun ranking =>
            rankingWelfare weight
              (permutationRankingValues n value ranking)) =
        finiteExpectation law (fun ranking =>
          strictPriorityWelfare weight
              (permutationRankingValues n value ranking) -
            rankingWelfare weight
              (permutationRankingValues n value ranking)) := by
    calc
      strictPriorityWelfare weight (List.ofFn value) -
          finiteExpectation law (fun ranking =>
            rankingWelfare weight
              (permutationRankingValues n value ranking)) =
          finiteExpectation law (fun ranking =>
            strictPriorityWelfare weight (List.ofFn value) -
              rankingWelfare weight
                (permutationRankingValues n value ranking)) := by
        symm
        exact finiteExpectation_const_sub law
          (strictPriorityWelfare weight (List.ofFn value)) _
      _ = finiteExpectation law (fun ranking =>
            strictPriorityWelfare weight
                (permutationRankingValues n value ranking) -
              rankingWelfare weight
                (permutationRankingValues n value ranking)) := by
        apply congrArg (finiteExpectation law)
        funext ranking
        rw [strictPriorityWelfare_permutation_eq_profile]
  have hnonnegative := finiteRanking_expected_welfare_loss_nonnegative
    law weight slots barDrop hweight
      (fun ranking => permutationRankingValues n value ranking)
  have hpairwise :=
    finiteRanking_exponentialRace_expected_pairwise_welfare_loss_le
      law weight slots barDrop tau hweight
        (fun ranking => permutationRankingValues n value ranking)
        gap inverted hdecomp hpairLaw
  have hbinomial :=
    pairwise_gap_mul_sigmoid_sum_le_choose_two n gap tau hgap htau
  constructor
  · rw [hlossEq]
    exact hnonnegative
  constructor
  · rw [hlossEq]
    exact hpairwise
  · exact mul_le_mul_of_nonneg_left hbinomial
      hweight.barDrop_nonnegative

end

end SmoothingCliff.Racing
