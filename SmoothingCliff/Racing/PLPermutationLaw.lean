import SmoothingCliff.Racing.GeneralWelfareLoss
import Mathlib.GroupTheory.Perm.Fin

/-!
# Finite Plackett--Luce laws on permutations

This file supplies the representation layer for the general top-slot welfare
bound.  A Plackett--Luce mass is constructed recursively by choosing the first
agent proportionally to its positive rate and recursing on the remaining
agents.  The recursion uses `Equiv.Perm.decomposeFin`, so every outcome is an
actual permutation and normalization is a finite sum identity.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Rates remaining after `first` is selected.  This is the relabelling used
by `Equiv.Perm.decomposeFin`: the tail label `i` represents
`swap 0 first i.succ`. -/
def removeChosenRate {n : ℕ} (rate : Fin (n + 1) → ℝ)
    (first : Fin (n + 1)) : Fin n → ℝ :=
  fun i => rate ((Equiv.swap 0 first) i.succ)

/-- Recursive Plackett--Luce probability mass on full permutations. -/
def plPermutationMass :
    (n : ℕ) → (Fin n → ℝ) → Equiv.Perm (Fin n) → ℝ
  | 0, _rate, _ranking => 1
  | n + 1, rate, ranking =>
      let decomposition := Equiv.Perm.decomposeFin ranking
      rate decomposition.1 / (∑ i, rate i) *
        plPermutationMass n
          (removeChosenRate rate decomposition.1) decomposition.2

theorem plPermutationMass_nonnegative :
    ∀ n (rate : Fin n → ℝ), (∀ i, 0 ≤ rate i) →
      ∀ ranking, 0 ≤ plPermutationMass n rate ranking := by
  intro n
  induction n with
  | zero =>
      intro rate hrate ranking
      simp [plPermutationMass]
  | succ n ih =>
      intro rate hrate ranking
      simp only [plPermutationMass]
      apply mul_nonneg
      · exact div_nonneg (hrate _)
          (Finset.sum_nonneg fun i hi => hrate i)
      · apply ih
        intro i
        exact hrate _

/-- The recursive masses sum to one for every strictly positive rate vector. -/
theorem plPermutationMass_sum_one :
    ∀ n (rate : Fin n → ℝ), (∀ i, 0 < rate i) →
      ∑ ranking : Equiv.Perm (Fin n),
        plPermutationMass n rate ranking = 1 := by
  intro n
  induction n with
  | zero =>
      intro rate hrate
      simp [plPermutationMass]
  | succ n ih =>
      intro rate hrate
      rw [← (Equiv.Perm.decomposeFin (n := n)).symm.sum_comp
        (fun ranking => plPermutationMass (n + 1) rate ranking)]
      simp only [plPermutationMass, Equiv.apply_symm_apply]
      rw [Fintype.sum_prod_type]
      calc
        (∑ first : Fin (n + 1),
            ∑ tail : Equiv.Perm (Fin n),
              rate first / (∑ i, rate i) *
                plPermutationMass n
                  (removeChosenRate rate first) tail) =
            ∑ first : Fin (n + 1),
              rate first / (∑ i, rate i) := by
          apply Finset.sum_congr rfl
          intro first hfirst
          rw [← Finset.mul_sum]
          rw [ih (removeChosenRate rate first)]
          · ring
          · intro i
            exact hrate _
        _ = 1 := by
          have hsum : (∑ i, rate i) ≠ 0 :=
            ne_of_gt (Finset.sum_pos (fun i hi => hrate i)
              Finset.univ_nonempty)
          rw [← Finset.sum_div Finset.univ rate (∑ i, rate i),
            div_self hsum]

/-- The normalized recursive mass as the finite-law interface used by the
welfare-loss development. -/
def plPermutationLaw (n : ℕ) (rate : Fin n → ℝ)
    (hrate : ∀ i, 0 < rate i) : FiniteLaw (Equiv.Perm (Fin n)) where
  probability := plPermutationMass n rate
  probability_nonnegative :=
    plPermutationMass_nonnegative n rate fun i => (hrate i).le
  probability_sum_one := plPermutationMass_sum_one n rate hrate

/-- Agent `left` occurs earlier than agent `right` in a ranking. -/
def permutationBefore {n : ℕ} (ranking : Equiv.Perm (Fin n))
    (left right : Fin n) : Prop :=
  ranking.symm left < ranking.symm right

instance {n : ℕ} (ranking : Equiv.Perm (Fin n)) (left right : Fin n) :
    Decidable (permutationBefore ranking left right) := by
  unfold permutationBefore
  infer_instance

/-- The tail labels used by `decomposeFin` are equivalent to the original
labels other than the selected first label. -/
def remainingEquivSwap {n : ℕ} (first : Fin (n + 1)) :
    Fin n ≃ {x : Fin (n + 1) // x ≠ first} :=
  (finSuccAboveEquiv (0 : Fin (n + 1))).trans
    ((Equiv.swap 0 first).subtypeEquiv fun x => by
      constructor
      · intro hx h
        apply hx
        apply (Equiv.swap 0 first).injective
        simpa using h
      · intro h hx
        apply h
        simp [hx])

def remainingIndex {n : ℕ} (first x : Fin (n + 1))
    (hx : x ≠ first) : Fin n :=
  (remainingEquivSwap first).symm ⟨x, hx⟩

theorem remainingIndex_spec {n : ℕ} (first x : Fin (n + 1))
    (hx : x ≠ first) :
    (Equiv.swap 0 first) (remainingIndex first x hx).succ = x := by
  have h := (remainingEquivSwap first).apply_symm_apply ⟨x, hx⟩
  exact congrArg Subtype.val h

theorem removeChosenRate_remainingIndex {n : ℕ}
    (rate : Fin (n + 1) → ℝ) (first x : Fin (n + 1))
    (hx : x ≠ first) :
    removeChosenRate rate first (remainingIndex first x hx) = rate x := by
  simp only [removeChosenRate]
  rw [remainingIndex_spec]

theorem decomposeFin_position_of_ne {n : ℕ}
    (first x : Fin (n + 1)) (tail : Equiv.Perm (Fin n))
    (hx : x ≠ first) :
    (Equiv.Perm.decomposeFin.symm (first, tail)).symm x =
      (tail.symm (remainingIndex first x hx)).succ := by
  apply (Equiv.Perm.decomposeFin.symm (first, tail)).injective
  rw [Equiv.apply_symm_apply]
  rw [Equiv.Perm.decomposeFin_symm_apply_succ]
  rw [Equiv.apply_symm_apply]
  exact (remainingIndex_spec first x hx).symm

theorem decomposeFin_position_first {n : ℕ}
    (first : Fin (n + 1)) (tail : Equiv.Perm (Fin n)) :
    (Equiv.Perm.decomposeFin.symm (first, tail)).symm first = 0 := by
  apply (Equiv.Perm.decomposeFin.symm (first, tail)).injective
  rw [Equiv.apply_symm_apply]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]

theorem permutationBefore_first_left {n : ℕ}
    (left right : Fin (n + 1)) (hne : left ≠ right)
    (tail : Equiv.Perm (Fin n)) :
    permutationBefore
      (Equiv.Perm.decomposeFin.symm (left, tail)) left right := by
  unfold permutationBefore
  rw [decomposeFin_position_first,
    decomposeFin_position_of_ne left right tail hne.symm]
  simp

theorem permutationBefore_first_right_false {n : ℕ}
    (left right : Fin (n + 1)) (hne : left ≠ right)
    (tail : Equiv.Perm (Fin n)) :
    ¬permutationBefore
      (Equiv.Perm.decomposeFin.symm (right, tail)) left right := by
  unfold permutationBefore
  rw [decomposeFin_position_first,
    decomposeFin_position_of_ne right left tail hne]
  simp

theorem permutationBefore_tail_iff {n : ℕ}
    (first left right : Fin (n + 1)) (tail : Equiv.Perm (Fin n))
    (hleft : left ≠ first) (hright : right ≠ first) :
    permutationBefore
        (Equiv.Perm.decomposeFin.symm (first, tail)) left right ↔
      permutationBefore tail
        (remainingIndex first left hleft)
        (remainingIndex first right hright) := by
  unfold permutationBefore
  rw [decomposeFin_position_of_ne first left tail hleft,
    decomposeFin_position_of_ne first right tail hright]
  simp

/-- Algebraic first-step identity behind the Plackett--Luce pair marginal. -/
theorem weightedFirstStep_pair_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (rate : α → ℝ) (left right : α) (hne : left ≠ right)
    (hsum : (∑ x, rate x) ≠ 0)
    (hpairsum : rate left + rate right ≠ 0) :
    (∑ first, rate first / (∑ x, rate x) *
      (if first = left then 1 else if first = right then 0
        else rate left / (rate left + rate right))) =
      rate left / (rate left + rate right) := by
  let summand : α → ℝ := fun first =>
    rate first / (∑ x, rate x) *
      (if first = left then 1 else if first = right then 0
        else rate left / (rate left + rate right))
  let rest : Finset α := (Finset.univ.erase left).erase right
  have hrightMem : right ∈ Finset.univ.erase left := by
    simp [hne.symm]
  have hsplitLeft :
      (∑ first, summand first) =
        summand left +
          ∑ first ∈ Finset.univ.erase left, summand first := by
    symm
    exact Finset.add_sum_erase Finset.univ summand
      (Finset.mem_univ left)
  have hsplitRight :
      (∑ first ∈ Finset.univ.erase left, summand first) =
        summand right + ∑ first ∈ rest, summand first := by
    symm
    exact Finset.add_sum_erase (Finset.univ.erase left) summand
      hrightMem
  change (∑ first, summand first) = _
  rw [hsplitLeft, hsplitRight]
  dsimp only [summand]
  simp only [if_pos, if_neg hne, if_neg hne.symm]
  have hrestRate :
      ∑ first ∈ rest, rate first =
        (∑ first, rate first) - rate left - rate right := by
    have hleftErase := Finset.add_sum_erase Finset.univ rate
      (Finset.mem_univ left)
    have hrightErase :=
      Finset.add_sum_erase (Finset.univ.erase left) rate hrightMem
    dsimp [rest]
    linarith
  have hrestSum :
      ∑ first ∈ rest,
          rate first / (∑ x, rate x) *
            (if first = left then 1 else if first = right then 0
              else rate left / (rate left + rate right)) =
        (rate left / (rate left + rate right)) *
          ((∑ first, rate first) - rate left - rate right) /
            (∑ x, rate x) := by
    calc
      _ = ∑ first ∈ rest,
          rate first / (∑ x, rate x) *
            (rate left / (rate left + rate right)) := by
        apply Finset.sum_congr rfl
        intro first hfirst
        have hleft : first ≠ left :=
          (Finset.mem_erase.mp (Finset.mem_of_mem_erase hfirst)).1
        have hright : first ≠ right := (Finset.mem_erase.mp hfirst).1
        rw [if_neg hleft, if_neg hright]
      _ = (rate left / (rate left + rate right)) *
          (∑ first ∈ rest, rate first) / (∑ x, rate x) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro first hfirst
        ring
      _ = _ := by rw [hrestRate]
  rw [hrestSum]
  field_simp
  ring

/-- The exact Plackett--Luce pair marginal.  The proof is a finite induction
on the recursive first-choice construction: if neither member of the pair is
chosen first, the induction hypothesis applies after relabelling the tail. -/
theorem plPermutationLaw_pair_before_probability :
    ∀ n (rate : Fin n → ℝ) (hrate : ∀ i, 0 < rate i),
      ∀ left right, left ≠ right →
        finiteProbability (plPermutationLaw n rate hrate)
            (fun ranking => permutationBefore ranking left right) =
          rate left / (rate left + rate right) := by
  intro n
  induction n with
  | zero =>
      intro rate hrate left
      exact Fin.elim0 left
  | succ n ih =>
      intro rate hrate left right hne
      let decomposition := Equiv.Perm.decomposeFin (n := n)
      simp only [finiteProbability, finiteExpectation, plPermutationLaw]
      rw [← decomposition.symm.sum_comp
        (fun ranking =>
          plPermutationMass (n + 1) rate ranking *
            eventIndicator (permutationBefore ranking left right))]
      simp only [plPermutationMass, decomposition, Equiv.apply_symm_apply]
      rw [Fintype.sum_prod_type]
      have hinner : ∀ first : Fin (n + 1),
          (∑ tail : Equiv.Perm (Fin n),
              plPermutationMass n (removeChosenRate rate first) tail *
                eventIndicator
                  (permutationBefore
                    (decomposition.symm (first, tail)) left right)) =
            if first = left then 1 else if first = right then 0
              else rate left / (rate left + rate right) := by
        intro first
        by_cases hfirstLeft : first = left
        · subst first
          rw [if_pos rfl]
          calc
            (∑ tail : Equiv.Perm (Fin n),
                plPermutationMass n (removeChosenRate rate left) tail *
                  eventIndicator
                    (permutationBefore
                      (decomposition.symm (left, tail)) left right)) =
                ∑ tail : Equiv.Perm (Fin n),
                  plPermutationMass n
                    (removeChosenRate rate left) tail := by
              apply Finset.sum_congr rfl
              intro tail htail
              rw [show eventIndicator
                    (permutationBefore
                      (decomposition.symm (left, tail)) left right) = 1 by
                simp [eventIndicator, decomposition,
                  permutationBefore_first_left left right hne tail]]
              ring
            _ = 1 := by
              apply plPermutationMass_sum_one
              intro i
              exact hrate _
        · by_cases hfirstRight : first = right
          · subst first
            rw [if_neg hne.symm, if_pos rfl]
            apply Finset.sum_eq_zero
            intro tail htail
            rw [show eventIndicator
                  (permutationBefore
                    (decomposition.symm (right, tail)) left right) = 0 by
              simp [eventIndicator, decomposition,
                permutationBefore_first_right_false left right hne tail]]
            ring
          · rw [if_neg hfirstLeft, if_neg hfirstRight]
            have hleft : left ≠ first := fun h => hfirstLeft h.symm
            have hright : right ≠ first := fun h => hfirstRight h.symm
            let leftTail := remainingIndex first left hleft
            let rightTail := remainingIndex first right hright
            have hneTail : leftTail ≠ rightTail := by
              intro h
              apply hne
              have hsubtype :
                  (⟨left, hleft⟩ : {x : Fin (n + 1) // x ≠ first}) =
                    ⟨right, hright⟩ := by
                apply (remainingEquivSwap first).symm.injective
                exact h
              exact congrArg Subtype.val hsubtype
            have htailRate : ∀ i,
                0 < removeChosenRate rate first i := by
              intro i
              exact hrate _
            calc
              (∑ tail : Equiv.Perm (Fin n),
                  plPermutationMass n (removeChosenRate rate first) tail *
                    eventIndicator
                      (permutationBefore
                        (decomposition.symm (first, tail)) left right)) =
                  ∑ tail : Equiv.Perm (Fin n),
                    plPermutationMass n
                        (removeChosenRate rate first) tail *
                      eventIndicator
                        (permutationBefore tail leftTail rightTail) := by
                apply Finset.sum_congr rfl
                intro tail htail
                congr 1
                by_cases htailBefore :
                    permutationBefore tail leftTail rightTail
                · have hglobal :
                      permutationBefore
                        (decomposition.symm (first, tail)) left right := by
                    simpa only [decomposition] using
                      (permutationBefore_tail_iff first left right tail
                        hleft hright).2 htailBefore
                  simp [eventIndicator, htailBefore, hglobal]
                · have hglobal :
                      ¬permutationBefore
                        (decomposition.symm (first, tail)) left right := by
                    intro hcontra
                    apply htailBefore
                    exact (permutationBefore_tail_iff first left right tail
                      hleft hright).1 (by simpa only [decomposition] using hcontra)
                  simp [eventIndicator, htailBefore, hglobal]
              _ = finiteProbability
                    (plPermutationLaw n
                      (removeChosenRate rate first) htailRate)
                    (fun tail =>
                      permutationBefore tail leftTail rightTail) := by
                rfl
              _ = removeChosenRate rate first leftTail /
                    (removeChosenRate rate first leftTail +
                      removeChosenRate rate first rightTail) := by
                exact ih (removeChosenRate rate first) htailRate
                  leftTail rightTail hneTail
              _ = rate left / (rate left + rate right) := by
                dsimp only [leftTail, rightTail]
                rw [removeChosenRate_remainingIndex,
                  removeChosenRate_remainingIndex]
      calc
        (∑ first : Fin (n + 1),
            ∑ tail : Equiv.Perm (Fin n),
              (rate first / (∑ i, rate i) *
                plPermutationMass n
                  (removeChosenRate rate first) tail) *
                eventIndicator
                  (permutationBefore
                    (decomposition.symm (first, tail)) left right)) =
            ∑ first : Fin (n + 1),
              rate first / (∑ i, rate i) *
                (∑ tail : Equiv.Perm (Fin n),
                  plPermutationMass n
                      (removeChosenRate rate first) tail *
                    eventIndicator
                      (permutationBefore
                        (decomposition.symm (first, tail)) left right)) := by
          apply Finset.sum_congr rfl
          intro first hfirst
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tail htail
          ring
        _ = ∑ first : Fin (n + 1),
              rate first / (∑ i, rate i) *
                (if first = left then 1 else if first = right then 0
                  else rate left / (rate left + rate right)) := by
          apply Finset.sum_congr rfl
          intro first hfirst
          rw [hinner first]
        _ = rate left / (rate left + rate right) := by
          apply weightedFirstStep_pair_probability rate left right hne
          · exact ne_of_gt (Finset.sum_pos (fun i hi => hrate i)
              Finset.univ_nonempty)
          · exact ne_of_gt (add_pos (hrate left) (hrate right))

/-! ## Exponential rates and the welfare-bound specialization -/

/-- Shift-invariant exponential rates used by the paper. -/
def shiftedExponentialRate {n : ℕ} (value : Fin n → ℝ)
    (reference tau : ℝ) : Fin n → ℝ :=
  fun agent => Real.exp ((value agent - reference) / tau)

theorem shiftedExponentialRate_positive {n : ℕ}
    (value : Fin n → ℝ) (reference tau : ℝ) :
    ∀ agent, 0 < shiftedExponentialRate value reference tau agent := by
  intro agent
  exact Real.exp_pos _

/-- The common reference shift cancels from every two-rate comparison. -/
theorem shiftedExponential_rateRatio_eq_sigmoid
    (highValue lowValue reference tau : ℝ) :
    Real.exp ((lowValue - reference) / tau) /
        (Real.exp ((highValue - reference) / tau) +
          Real.exp ((lowValue - reference) / tau)) =
      Real.sigmoid (-(highValue - lowValue) / tau) := by
  rw [Real.sigmoid_def]
  have hrewrite :
      -(-(highValue - lowValue) / tau) =
        (highValue - reference) / tau -
          (lowValue - reference) / tau := by ring
  rw [hrewrite, Real.exp_sub]
  have hhigh : Real.exp ((highValue - reference) / tau) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hlow : Real.exp ((lowValue - reference) / tau) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  field_simp
  ring

/-- Under the full global Plackett--Luce law, the lower-valued member of a
named pair precedes the higher-valued member with exactly the paper's sigmoid
probability.  No pair marginal is assumed. -/
theorem shiftedExponential_PL_pair_inversion_probability
    (n : ℕ) (value : Fin n → ℝ) (reference tau : ℝ)
    (low high : Fin n) (hne : low ≠ high) :
    finiteProbability
        (plPermutationLaw n
          (shiftedExponentialRate value reference tau)
          (shiftedExponentialRate_positive value reference tau))
        (fun ranking => permutationBefore ranking low high) =
      Real.sigmoid (-(value high - value low) / tau) := by
  rw [plPermutationLaw_pair_before_probability n
    (shiftedExponentialRate value reference tau)
    (shiftedExponentialRate_positive value reference tau) low high hne]
  simpa [shiftedExponentialRate, add_comm] using
    shiftedExponential_rateRatio_eq_sigmoid
      (value high) (value low) reference tau

/-- The pair marginal of the global Plackett--Luce law agrees with the
explicit two-clock order law constructed in `GeneralWelfareLoss`. -/
theorem shiftedExponential_PL_pairLaw_consistency
    (n : ℕ) (value : Fin n → ℝ) (reference tau : ℝ)
    (low high : Fin n) (hne : low ≠ high) :
    finiteProbability
        (plPermutationLaw n
          (shiftedExponentialRate value reference tau)
          (shiftedExponentialRate_positive value reference tau))
        (fun ranking => permutationBefore ranking low high) =
      finiteProbability
        (exponentialRacePairLaw (value high - value low) 0 tau)
        (fun lowerFirst => lowerFirst = true) := by
  rw [shiftedExponential_PL_pair_inversion_probability
    n value reference tau low high hne]
  symm
  simpa using exponentialRace_pair_inversion_probability
    (value high - value low) 0 tau

/-- General top-K welfare bounds under the actual globally normalized
Plackett--Luce law.  The only remaining input is the deterministic statement
that the chosen enumeration of unordered agent pairs decomposes
`inversionGap`; the global law, its normalization, and every pair marginal
are all discharged here. -/
theorem shiftedExponential_PL_generalTopK_welfare_loss_bounds
    (n : ℕ) (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau reference : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ)
    (low high : Fin (n.choose 2) → Fin n)
    (hdistinct : ∀ pair, low pair ≠ high pair)
    (hvalueOrder : ∀ pair, value (low pair) < value (high pair))
    (hdecomp : ∀ ranking : Equiv.Perm (Fin n),
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair,
          (value (high pair) - value (low pair)) *
            eventIndicator
              (permutationBefore ranking (low pair) (high pair)))
    (htau : 0 < tau) :
    let law := plPermutationLaw n
      (shiftedExponentialRate value reference tau)
      (shiftedExponentialRate_positive value reference tau)
    let welfareLoss :=
      strictPriorityWelfare weight (List.ofFn value) -
        finiteExpectation law (fun ranking =>
          rankingWelfare weight
            (permutationRankingValues n value ranking))
    0 ≤ welfareLoss ∧
      welfareLoss ≤
        barDrop * ∑ pair,
          (value (high pair) - value (low pair)) *
            Real.sigmoid
              (-(value (high pair) - value (low pair)) / tau) ∧
      barDrop * ∑ pair,
          (value (high pair) - value (low pair)) *
            Real.sigmoid
              (-(value (high pair) - value (low pair)) / tau) ≤
        barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  dsimp only
  apply permutationLaw_generalTopK_welfare_loss_bounds
    n
    (plPermutationLaw n
      (shiftedExponentialRate value reference tau)
      (shiftedExponentialRate_positive value reference tau))
    weight slots barDrop tau hweight value
    (fun pair => value (high pair) - value (low pair))
    (fun ranking pair =>
      permutationBefore ranking (low pair) (high pair))
    hdecomp
  · intro pair
    exact shiftedExponential_PL_pairLaw_consistency n value reference tau
      (low pair) (high pair) (hdistinct pair)
  · intro pair
    exact sub_nonneg.mpr (hvalueOrder pair).le
  · exact htau

end

end SmoothingCliff.Racing

namespace SmoothingCliff.Racing

/-- Canonical unordered pairs of Fin n, represented in decreasing index order. -/
abbrev CanonicalPair (n : ℕ) := ↥(Equiv.Perm.finPairsLT n)

theorem canonicalPair_card (n : ℕ) :
    Fintype.card (CanonicalPair n) = n.choose 2 := by
  rw [Fintype.card_coe]
  simp [Equiv.Perm.finPairsLT, Finset.card_sigma, Nat.choose_two_right]
  calc
    (∑ x : Fin n, (x : ℕ)) = ∑ i ∈ Finset.range n, i :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n
    _ = n * (n - 1) / 2 := Finset.sum_range_id n

def canonicalPairSuccMap (n : ℕ) :
    Fin n ⊕ CanonicalPair n → CanonicalPair (n + 1)
  | Sum.inl later =>
      ⟨⟨later.succ, (0 : Fin (n + 1))⟩,
        Equiv.Perm.mem_finPairsLT.2 (Fin.succ_pos later)⟩
  | Sum.inr pair =>
      ⟨⟨pair.1.1.succ, pair.1.2.succ⟩,
        Equiv.Perm.mem_finPairsLT.2
          (Fin.succ_lt_succ_iff.2 (Equiv.Perm.mem_finPairsLT.1 pair.2))⟩

theorem canonicalPairSuccMap_bijective (n : ℕ) :
    Function.Bijective (canonicalPairSuccMap n) := by
  constructor
  · rintro (later | pair) (later' | pair') h
    · simp [canonicalPairSuccMap] at h ⊢
      exact h
    · have hzero : (0 : Fin (n + 1)) = pair'.1.2.succ :=
        congrArg (fun p : CanonicalPair (n + 1) => p.1.2) h
      exact (Fin.succ_ne_zero _ hzero.symm).elim
    · have hzero : pair.1.2.succ = (0 : Fin (n + 1)) :=
        congrArg (fun p : CanonicalPair (n + 1) => p.1.2) h
      exact (Fin.succ_ne_zero _ hzero).elim
    · apply congrArg Sum.inr
      apply Subtype.ext
      have hfst : pair.1.1.succ = pair'.1.1.succ := by
        simpa [canonicalPairSuccMap] using
          congrArg (fun p : CanonicalPair (n + 1) => p.1.1) h
      have hsnd : pair.1.2.succ = pair'.1.2.succ := by
        simpa [canonicalPairSuccMap] using
          congrArg (fun p : CanonicalPair (n + 1) => p.1.2) h
      apply Sigma.ext
      · exact Fin.succ_inj.mp hfst
      · exact heq_of_eq (Fin.succ_inj.mp hsnd)
  · rintro ⟨⟨later, earlier⟩, hpair⟩
    have hlt : earlier < later := Equiv.Perm.mem_finPairsLT.1 hpair
    have hlater : later ≠ 0 := ne_of_gt (lt_of_le_of_lt earlier.zero_le hlt)
    obtain ⟨later', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hlater
    by_cases hearlier : earlier = 0
    · subst earlier
      exact ⟨Sum.inl later', rfl⟩
    · obtain ⟨earlier', heq⟩ := Fin.exists_succ_eq_of_ne_zero hearlier
      subst earlier
      have hlt' : earlier' < later' := Fin.succ_lt_succ_iff.1 hlt
      let pair : CanonicalPair n :=
        ⟨⟨later', earlier'⟩, Equiv.Perm.mem_finPairsLT.2 hlt'⟩
      exact ⟨Sum.inr pair, rfl⟩

noncomputable def canonicalPairSuccEquiv (n : ℕ) :
    (Fin n ⊕ CanonicalPair n) ≃ CanonicalPair (n + 1) :=
  Equiv.ofBijective (canonicalPairSuccMap n) (canonicalPairSuccMap_bijective n)

theorem inversionGap_ofFn_eq_canonicalPair_sum :
    ∀ (n : ℕ) (values : Fin n → ℝ),
      inversionGap (List.ofFn values) =
        ∑ pair : CanonicalPair n,
          pairInversionGap (values pair.1.2) (values pair.1.1) := by
  intro n
  induction n with
  | zero =>
      intro values
      simp [CanonicalPair, Equiv.Perm.finPairsLT, inversionGap]
  | succ n ih =>
      intro values
      rw [List.ofFn_succ]
      simp only [inversionGap, List.map_ofFn, List.sum_ofFn]
      rw [ih]
      rw [← (canonicalPairSuccEquiv n).sum_comp
        (fun pair : CanonicalPair (n + 1) =>
          pairInversionGap (values pair.1.2) (values pair.1.1))]
      rw [Fintype.sum_sum_type]
      rfl

def canonicalPairPermMap {n : ℕ} (ranking : Equiv.Perm (Fin n)) :
    CanonicalPair n → CanonicalPair n := fun pair =>
  ⟨Equiv.Perm.signBijAux ranking pair.1,
    Equiv.Perm.signBijAux_mem pair.1 pair.2⟩

theorem canonicalPairPermMap_bijective {n : ℕ}
    (ranking : Equiv.Perm (Fin n)) :
    Function.Bijective (canonicalPairPermMap ranking) := by
  constructor
  · intro left right h
    apply Subtype.ext
    apply Equiv.Perm.signBijAux_injOn left.2 right.2
    exact congrArg Subtype.val h
  · intro pair
    obtain ⟨source, hsource, hmap⟩ :=
      Equiv.Perm.signBijAux_surj pair.1 pair.2
    exact ⟨⟨source, hsource⟩, Subtype.ext hmap⟩

noncomputable def canonicalPairPermEquiv {n : ℕ}
    (ranking : Equiv.Perm (Fin n)) : CanonicalPair n ≃ CanonicalPair n :=
  Equiv.ofBijective (canonicalPairPermMap ranking)
    (canonicalPairPermMap_bijective ranking)

noncomputable def canonicalPairLow {n : ℕ} (value : Fin n → ℝ)
    (pair : CanonicalPair n) : Fin n :=
  if value pair.1.1 ≤ value pair.1.2 then pair.1.1 else pair.1.2

noncomputable def canonicalPairHigh {n : ℕ} (value : Fin n → ℝ)
    (pair : CanonicalPair n) : Fin n :=
  if value pair.1.1 ≤ value pair.1.2 then pair.1.2 else pair.1.1

noncomputable def canonicalPairGap {n : ℕ} (value : Fin n → ℝ)
    (pair : CanonicalPair n) : ℝ :=
  value (canonicalPairHigh value pair) - value (canonicalPairLow value pair)

theorem canonicalPair_low_ne_high {n : ℕ} (value : Fin n → ℝ)
    (pair : CanonicalPair n) :
    canonicalPairLow value pair ≠ canonicalPairHigh value pair := by
  have hne : pair.1.1 ≠ pair.1.2 :=
    (Equiv.Perm.mem_finPairsLT.1 pair.2).ne'
  have hne' : pair.1.2 ≠ pair.1.1 := hne.symm
  simp only [canonicalPairLow, canonicalPairHigh]
  split_ifs <;> assumption

theorem canonicalPairGap_nonnegative {n : ℕ} (value : Fin n → ℝ)
    (pair : CanonicalPair n) : 0 ≤ canonicalPairGap value pair := by
  simp only [canonicalPairGap, canonicalPairLow, canonicalPairHigh]
  split_ifs with h
  · linarith
  · exact sub_nonneg.mpr (le_of_not_ge h)

theorem inversionGap_permutation_eq_canonicalPair_sum {n : ℕ}
    (value : Fin n → ℝ) (ranking : Equiv.Perm (Fin n)) :
    inversionGap (permutationRankingValues n value ranking) =
      ∑ pair : CanonicalPair n,
        canonicalPairGap value pair *
          eventIndicator
            (permutationBefore ranking
              (canonicalPairLow value pair) (canonicalPairHigh value pair)) := by
  change inversionGap (List.ofFn (fun position => value (ranking position))) = _
  rw [inversionGap_ofFn_eq_canonicalPair_sum]
  rw [← (canonicalPairPermEquiv ranking).sum_comp
    (fun pair : CanonicalPair n =>
      canonicalPairGap value pair *
        eventIndicator
          (permutationBefore ranking
            (canonicalPairLow value pair) (canonicalPairHigh value pair)))]
  apply Fintype.sum_congr
  intro pair
  have hpos : pair.1.2 < pair.1.1 :=
    Equiv.Perm.mem_finPairsLT.1 pair.2
  have hnotpos : ¬pair.1.1 < pair.1.2 := not_lt_of_ge hpos.le
  by_cases hindex : ranking pair.1.2 < ranking pair.1.1
  · by_cases hvalue :
        value (ranking pair.1.1) ≤ value (ranking pair.1.2)
    · simp [canonicalPairPermEquiv, canonicalPairPermMap,
        canonicalPairGap, canonicalPairLow, canonicalPairHigh,
        Equiv.Perm.signBijAux, hindex, hvalue, permutationBefore,
        eventIndicator, pairInversionGap, hnotpos]
    · have hvalue' :
          value (ranking pair.1.2) ≤ value (ranking pair.1.1) :=
        le_of_not_ge hvalue
      simp [canonicalPairPermEquiv, canonicalPairPermMap,
        canonicalPairGap, canonicalPairLow, canonicalPairHigh,
        Equiv.Perm.signBijAux, hindex, hvalue, hvalue', permutationBefore,
        eventIndicator, pairInversionGap, hpos]
  · by_cases hvalue :
        value (ranking pair.1.2) ≤ value (ranking pair.1.1)
    · simp [canonicalPairPermEquiv, canonicalPairPermMap,
        canonicalPairGap, canonicalPairLow, canonicalPairHigh,
        Equiv.Perm.signBijAux, hindex, hvalue, permutationBefore,
        eventIndicator, pairInversionGap, hpos]
    · have hvalue' :
          value (ranking pair.1.1) ≤ value (ranking pair.1.2) :=
        le_of_not_ge hvalue
      simp [canonicalPairPermEquiv, canonicalPairPermMap,
        canonicalPairGap, canonicalPairLow, canonicalPairHigh,
        Equiv.Perm.signBijAux, hindex, hvalue, hvalue', permutationBefore,
        eventIndicator, pairInversionGap, hnotpos]

noncomputable def canonicalPairIndexEquiv (n : ℕ) :
    Fin (n.choose 2) ≃ CanonicalPair n :=
  Fintype.equivOfCardEq (by
    simpa using (canonicalPair_card n).symm)

/-- The general top-slot welfare-loss theorem under the globally normalized
shifted-exponential Plackett--Luce law, with the unordered-pair decomposition
proved internally.  In particular, this theorem has no pair-marginal or
bookkeeping premise. -/
theorem shiftedExponential_PL_generalTopK_welfare_loss_bounds_complete
    (n : ℕ) (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau reference : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (htau : 0 < tau) :
    let law := plPermutationLaw n
      (shiftedExponentialRate value reference tau)
      (shiftedExponentialRate_positive value reference tau)
    let welfareLoss :=
      strictPriorityWelfare weight (List.ofFn value) -
        finiteExpectation law (fun ranking =>
          rankingWelfare weight
            (permutationRankingValues n value ranking))
    0 ≤ welfareLoss ∧
      welfareLoss ≤
        barDrop * ∑ pair : CanonicalPair n,
          canonicalPairGap value pair *
            Real.sigmoid (-(canonicalPairGap value pair) / tau) ∧
      barDrop * ∑ pair : CanonicalPair n,
          canonicalPairGap value pair *
            Real.sigmoid (-(canonicalPairGap value pair) / tau) ≤
        barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  dsimp only
  let enumerate := canonicalPairIndexEquiv n
  have hbounds := permutationLaw_generalTopK_welfare_loss_bounds
    n
    (plPermutationLaw n
      (shiftedExponentialRate value reference tau)
      (shiftedExponentialRate_positive value reference tau))
    weight slots barDrop tau hweight value
    (fun pair => canonicalPairGap value (enumerate pair))
    (fun ranking pair =>
      permutationBefore ranking
        (canonicalPairLow value (enumerate pair))
        (canonicalPairHigh value (enumerate pair)))
    (by
      intro ranking
      rw [inversionGap_permutation_eq_canonicalPair_sum]
      rw [← enumerate.sum_comp
        (fun pair : CanonicalPair n =>
          canonicalPairGap value pair *
            eventIndicator
              (permutationBefore ranking
                (canonicalPairLow value pair)
                (canonicalPairHigh value pair)))])
    (by
      intro pair
      exact shiftedExponential_PL_pairLaw_consistency n value reference tau
        (canonicalPairLow value (enumerate pair))
        (canonicalPairHigh value (enumerate pair))
        (canonicalPair_low_ne_high value (enumerate pair)))
    (by
      intro pair
      exact canonicalPairGap_nonnegative value (enumerate pair))
    htau
  have hsum :
      (∑ pair : Fin (n.choose 2),
          canonicalPairGap value (enumerate pair) *
            Real.sigmoid (-(canonicalPairGap value (enumerate pair)) / tau)) =
        ∑ pair : CanonicalPair n,
          canonicalPairGap value pair *
            Real.sigmoid (-(canonicalPairGap value pair) / tau) :=
    enumerate.sum_comp (fun pair : CanonicalPair n =>
      canonicalPairGap value pair *
        Real.sigmoid (-(canonicalPairGap value pair) / tau))
  rw [hsum] at hbounds
  exact hbounds

end SmoothingCliff.Racing
