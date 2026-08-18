/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Econlib.Probability.CountDist.Map
public import Econlib.Probability.Distributions.Binomial.Moments
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial distribution

This file defines multinomial outcomes and the multinomial distribution over count vectors with a
fixed number of trials.

## Main definitions

* `MultinomialOutcome`: Count vectors summing to a fixed number of trials.
* `CountDist.multinomial`: Multinomial distribution for finite category probabilities.

## Main statements

* `CountDist.multinomial_apply`: Point-mass formula for the multinomial pmf.
* `CountDist.multinomial_apply_zero_trials`: Degenerate case with zero trials.
* `CountDist.multinomial_apply_single_category`: Degenerate case with a single category.
* `CountDist.multinomial_apply_one_trial_unit_vector`: One-trial point mass at a unit vector.
* `CountDist.multinomial_apply_two_categories`: Two-category specialization (binomial formula).
* `CountDist.multinomial_marginal`: The marginal of a coordinate is the corresponding binomial.
* `CountDist.multinomial_expect_count`: Expected count for coordinate `i` equals `trials * p i`.
* `CountDist.multinomial_variance_count`: Variance of coordinate `i` equals
  `trials * p i * (1 - p i)`.

## Tags

probability, discrete distributions, multinomial
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability

/-- Outcome space for a multinomial law with `m` categories and `trials` draws. -/
abbrev MultinomialOutcome (m trials : ℕ) := { counts : Fin m → ℕ // ∑ i, counts i = trials }

namespace MultinomialOutcome

variable {m trials : ℕ}

/-- The finite enumeration of multinomial outcomes agrees with Mathlib's tuple antidiagonal. -/
def finset (m trials : ℕ) : Finset (MultinomialOutcome m trials) :=
  (Finset.Nat.antidiagonalTuple m trials).attach.map
    ⟨fun x => ⟨x.1, Finset.Nat.mem_antidiagonalTuple.mp x.2⟩, by
      intro x y h
      cases x
      cases y
      cases h
      rfl⟩

/-- Every multinomial outcome belongs to `finset m trials`. -/
lemma mem_finset (x : MultinomialOutcome m trials) : x ∈ finset m trials := by
  refine Finset.mem_map.mpr ?_
  refine ⟨⟨x.1, Finset.Nat.mem_antidiagonalTuple.mpr x.2⟩, ?_, rfl⟩
  simp

/-- Equivalence between multinomial outcomes and antidiagonal tuples. -/
def equivAntidiagonal (m trials : ℕ) :
    MultinomialOutcome m trials ≃ { x // x ∈ Finset.Nat.antidiagonalTuple m trials } where
  toFun x := ⟨x.1, Finset.Nat.mem_antidiagonalTuple.mpr x.2⟩
  invFun x := ⟨x.1, Finset.Nat.mem_antidiagonalTuple.mp x.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- `MultinomialOutcome m trials` is a fintype, via the equivalence with antidiagonal tuples. -/
noncomputable instance instFintype (m trials : ℕ) : Fintype (MultinomialOutcome m trials) := by
  letI : Fintype { x // x ∈ Finset.Nat.antidiagonalTuple m trials } :=
    Fintype.ofFinset (Finset.Nat.antidiagonalTuple m trials) (fun _ => Iff.rfl)
  exact Fintype.ofEquiv { x // x ∈ Finset.Nat.antidiagonalTuple m trials }
    (equivAntidiagonal m trials).symm

end MultinomialOutcome

/-- Multinomial distribution with category probabilities `p` and `trials` draws. -/
noncomputable def CountDist.multinomial {m : ℕ} (p : FinDist (Fin m)) (trials : ℕ) :
    CountDist (MultinomialOutcome m trials) :=
  { pmf := fun counts =>
      (Nat.multinomial Finset.univ counts.1 : ℕ) * ∏ i, (p.pmf i) ^ counts.1 i
    nonneg := by
      intro counts
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (p.nonneg i) _)
    tsum_one := by
      rw [tsum_fintype]
      let e := MultinomialOutcome.equivAntidiagonal m trials
      have hsum_eq :
          ∑ counts : MultinomialOutcome m trials,
              ((Nat.multinomial Finset.univ counts.1 : ℕ) * ∏ i, (p.pmf i) ^ counts.1 i) =
            ∑ x : {x // x ∈ Finset.Nat.antidiagonalTuple m trials},
              ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ i, (p.pmf i) ^ x.1 i) :=
        Fintype.sum_equiv e
          (fun counts => (Nat.multinomial Finset.univ counts.1 : ℕ) * ∏ i, (p.pmf i) ^ counts.1 i)
          (fun x => (Nat.multinomial Finset.univ x.1 : ℕ) * ∏ i, (p.pmf i) ^ x.1 i)
          (fun _ => rfl)
      have hattach :
          (∑ x : {x // x ∈ Finset.Nat.antidiagonalTuple m trials},
            ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ i, (p.pmf i) ^ x.1 i)) =
          Finset.sum (Finset.Nat.antidiagonalTuple m trials)
            (fun x => ((Nat.multinomial Finset.univ x : ℕ) * ∏ i, (p.pmf i) ^ x i)) := by
        rw [← Finset.attach_eq_univ]
        exact Finset.sum_attach
          (s := Finset.Nat.antidiagonalTuple m trials)
          (f := fun x => ((Nat.multinomial Finset.univ x : ℕ) * ∏ i, (p.pmf i) ^ x i))
      rw [hsum_eq, hattach]
      have hpow :
          Finset.sum (Finset.Nat.antidiagonalTuple m trials)
            (fun x => ((Nat.multinomial Finset.univ x : ℕ) * ∏ i, (p.pmf i) ^ x i)) =
            (∑ i, p.pmf i) ^ trials := by
        simpa [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple] using
          (Finset.sum_pow_eq_sum_piAntidiag (s := Finset.univ) (f := p.pmf) trials).symm
      rw [hpow, p.sum_one]
      simp }

/-- The pmf of the multinomial distribution at a count vector `counts` is the multinomial
coefficient times the product of category probabilities raised to their respective counts. -/
@[simp] lemma CountDist.multinomial_apply {m trials : ℕ} (p : FinDist (Fin m))
    (counts : MultinomialOutcome m trials) :
    (CountDist.multinomial p trials).pmf counts =
      (Nat.multinomial Finset.univ counts.1 : ℕ) * ∏ i, (p.pmf i) ^ counts.1 i := by
  rfl

/-- With zero trials, the multinomial pmf is `1` at the all-zero count vector and `0` elsewhere. -/
lemma CountDist.multinomial_apply_zero_trials {m : ℕ} (p : FinDist (Fin m))
    (counts : MultinomialOutcome m 0) :
    (CountDist.multinomial p 0).pmf counts = if counts.1 = 0 then 1 else 0 := by
  have hzero : counts.1 = 0 := by
    funext i
    have hi : counts.1 i ≤ 0 := by
      have hsum_nonneg : counts.1 i ≤ ∑ j, counts.1 j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa [counts.2] using hsum_nonneg
    exact Nat.eq_zero_of_le_zero hi
  simp [CountDist.multinomial_apply, hzero, Nat.multinomial]

/-- With a single category, the multinomial pmf is identically `1` (the only outcome has
probability one). -/
lemma CountDist.multinomial_apply_single_category (p : FinDist (Fin 1)) (trials : ℕ)
    (counts : MultinomialOutcome 1 trials) :
    (CountDist.multinomial p trials).pmf counts = 1 := by
  have hcounts : counts.1 = ![trials] := by
    funext i
    fin_cases i
    simpa using counts.2
  have hp : p.pmf 0 = 1 := by simpa using p.sum_one
  simp [CountDist.multinomial_apply, hcounts, hp]

/-- With one trial, the multinomial pmf at the unit vector `eᵢ` equals the probability `p i`. -/
lemma CountDist.multinomial_apply_one_trial_unit_vector {m : ℕ} (p : FinDist (Fin m)) (i : Fin m) :
    (CountDist.multinomial p 1).pmf
      ⟨Pi.single i 1, by simp⟩ = p.pmf i := by
  rw [CountDist.multinomial_apply]
  let unit : Fin m → ℕ := Pi.single i 1
  have hprod :
      ∏ x, p.pmf x ^ unit x = p.pmf i := by
    calc
      ∏ x, p.pmf x ^ unit x = ∏ x, if x = i then p.pmf x else 1 := by
        refine Finset.prod_congr rfl fun x _ => ?_
        by_cases h : x = i <;> simp [unit, h]
      _ = p.pmf i := by simp
  have hmulti : Nat.multinomial Finset.univ unit = 1 := by
    rw [Nat.multinomial]
    have hsum : Finset.sum Finset.univ unit = 1 := by
      simp [unit]
    rw [hsum]
    have hfact :
        Finset.prod Finset.univ (fun x : Fin m => Nat.factorial (unit x)) = 1 := by
      calc
        Finset.prod Finset.univ (fun x : Fin m => Nat.factorial (unit x)) =
            Finset.prod Finset.univ
              (fun x : Fin m => if x = i then Nat.factorial 1 else Nat.factorial 0) := by
          refine Finset.prod_congr rfl fun x _ => ?_
          by_cases h : x = i <;> simp [unit, h]
        _ = 1 := by simp
    simp [hfact]
  simp [unit, hmulti, hprod]

/-- **Two-category specialization:** For two categories, the multinomial pmf reduces to the
binomial formula `C(trials, k) * p₀^k * p₁^(trials-k)`. -/
lemma CountDist.multinomial_apply_two_categories {trials : ℕ} (p : FinDist (Fin 2))
    (counts : MultinomialOutcome 2 trials) :
    (CountDist.multinomial p trials).pmf counts =
      (trials.choose (counts.1 0) : ℕ) *
        (p.pmf 0) ^ counts.1 0 * (p.pmf 1) ^ counts.1 1 := by
  have hsum : counts.1 0 + counts.1 1 = trials := by simpa using counts.2
  rw [CountDist.multinomial_apply]
  have hmulti :
      Nat.multinomial (Finset.univ : Finset (Fin 2)) counts.1 = trials.choose (counts.1 0) := by
    simpa [hsum] using
      (Nat.binomial_eq_choose (f := counts.1) (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide))
  rw [hmulti]
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- The coordinate count as a `Fin (trials + 1)`. -/
def multinomialCount {m trials : ℕ} (i : Fin m) (x : MultinomialOutcome m trials) :
    Fin (trials + 1) :=
  ⟨x.1 i, Nat.lt_succ_of_le <| by
    have hle : x.1 i ≤ ∑ j, x.1 j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [x.2] using hle⟩

/-- Summing the multinomial weights over all count vectors where coordinate `i` equals `k` recovers
the binomial pmf `Bin(trials, p i)` at `k`. -/
private lemma multinomial_fixed_coordinate_sum {m trials : ℕ} (p : FinDist (Fin m)) (i : Fin m)
    (k : Fin (trials + 1)) :
    Finset.sum (Finset.univ.piAntidiag trials) (fun counts =>
      if (k : ℕ) = counts i then
        ((Nat.multinomial Finset.univ counts : ℕ) * ∏ j, (p.pmf j) ^ counts j)
      else 0)
      = (FinDist.binomial (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials).pmf k := by
  let s : Finset (Fin m) := Finset.univ.erase i
  have hi : i ∉ s := by simp [s]
  have huniv : Finset.cons i s hi = Finset.univ := by
    ext j
    simp [s]
  rw [← huniv, Finset.piAntidiag_cons hi, Finset.sum_disjiUnion]
  simp only [Finset.sum_map, addRightEmbedding_apply]
  let pk : ℕ × ℕ := (k, trials - k)
  have hpk_mem : pk ∈ Finset.antidiagonal trials := by
    simp [pk, Finset.mem_antidiagonal, Nat.add_sub_of_le k.is_le]
  rw [Finset.sum_eq_single_of_mem pk hpk_mem]
  · simp only [pk] at *
    change (
      ∑ g ∈ s.piAntidiag (trials - k),
        if (k : ℕ) = (g + fun t ↦ if t = i then (k : ℕ) else 0) i then
          ↑(Nat.multinomial (Finset.cons i s hi) (g + fun t ↦ if t = i then (k : ℕ) else 0)) *
            ∏ x ∈ Finset.cons i s hi, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x
        else 0
      ) = (FinDist.binomial (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials).pmf k
    have hinner :
        (∑ g ∈ s.piAntidiag (trials - k),
          if (k : ℕ) = (g + fun t ↦ if t = i then (k : ℕ) else 0) i then
            ↑(Nat.multinomial (Finset.cons i s hi) (g + fun t ↦ if t = i then (k : ℕ) else 0)) *
              ∏ x ∈ Finset.cons i s hi, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x
          else 0
        ) =
        ((trials.choose k : ℕ) : ℝ) * (p.pmf i) ^ (k : ℕ) *
          (∑ g ∈ s.piAntidiag (trials - k),
            ((Nat.multinomial s g : ℕ) * ∏ x ∈ s, p.pmf x ^ g x)) := by
      let F : (Fin m → ℕ) → ℝ := fun g =>
        if (k : ℕ) = (g + fun t ↦ if t = i then (k : ℕ) else 0) i then
          ↑(Nat.multinomial (Finset.cons i s hi) (g + fun t ↦ if t = i then (k : ℕ) else 0)) *
            ∏ x ∈ Finset.cons i s hi, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x
        else 0
      let G : (Fin m → ℕ) → ℝ := fun g =>
        ((trials.choose k : ℕ) : ℝ) * (p.pmf i) ^ (k : ℕ) *
          ((Nat.multinomial s g : ℕ) * ∏ x ∈ s, p.pmf x ^ g x)
      suffices ∑ g ∈ s.piAntidiag (trials - k), F g = ∑ g ∈ s.piAntidiag (trials - k), G g by
        simpa [F, G, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro g hg
      rw [Finset.mem_piAntidiag] at hg
      have hgi0 : g i = 0 := by
        by_contra hgi
        exact hi (hg.2 i hgi)
      have hcons_sum : (k : ℕ) + ∑ x ∈ s, g x = trials := by
        simpa [hg.1, Nat.add_comm] using (Nat.add_sub_of_le k.is_le)
      have hmulti :
          Nat.multinomial (Finset.cons i s hi) (g + fun t ↦ if t = i then (k : ℕ) else 0) =
            trials.choose k * Nat.multinomial s g := by
        rw [Nat.multinomial_cons hi]
        have hsum_s :
            ∑ x ∈ s, (g + fun t ↦ if t = i then (k : ℕ) else 0) x = ∑ x ∈ s, g x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxi : x ≠ i := fun h => hi (h ▸ hx)
          simp [hxi]
        rw [show (g + fun t ↦ if t = i then (k : ℕ) else 0) i = k by simp [hgi0],
          hsum_s, hg.1]
        rw [Nat.add_sub_of_le k.is_le]
        congr 1
        exact Nat.multinomial_congr (fun x hx => by
          have hxi : x ≠ i := fun h => hi (h ▸ hx)
          simp [hxi])
      have hprod :
          ∏ x ∈ Finset.cons i s hi, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x =
            (p.pmf i) ^ (k : ℕ) * ∏ x ∈ s, p.pmf x ^ g x := by
        rw [Finset.prod_cons hi]
        have hprod_s :
            ∏ x ∈ s, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x =
              ∏ x ∈ s, p.pmf x ^ g x := by
          refine Finset.prod_congr rfl fun x hx => ?_
          have hxi : x ≠ i := fun h => hi (h ▸ hx)
          simp [hxi]
        rw [hprod_s]
        simp [hgi0]
      dsimp [F, G]
      rw [if_pos (by simp [hgi0]), hmulti]
      change
        ↑(trials.choose k * Nat.multinomial s g) *
            ∏ x ∈ Finset.cons i s hi, p.pmf x ^ (g + fun t ↦ if t = i then (k : ℕ) else 0) x =
          ((trials.choose k : ℕ) : ℝ) * (p.pmf i) ^ (k : ℕ) *
            ((Nat.multinomial s g : ℕ) * ∏ x ∈ s, p.pmf x ^ g x)
      rw [hprod]
      rw [Nat.cast_mul]
      ring
    rw [hinner]
    have hpow :
        ∑ g ∈ s.piAntidiag (trials - k), ((Nat.multinomial s g : ℕ) * ∏ x ∈ s, p.pmf x ^ g x) =
          (∑ x ∈ s, p.pmf x) ^ (trials - k) := by
      simpa using (Finset.sum_pow_eq_sum_piAntidiag (s := s) (f := p.pmf) (trials - k)).symm
    rw [hpow]
    have hs : ∑ x ∈ s, p.pmf x = 1 - p.pmf i := by
      dsimp [s]
      have hsum := Finset.sum_erase_add (s := Finset.univ) (f := p.pmf) (a := i) (by simp)
      rw [p.sum_one] at hsum
      linarith
    rw [hs, FinDist.binomial_apply]
    have hkrev : (k.rev : ℕ) = trials - k := by
      simp [Fin.val_rev]
    rw [hkrev]
    ring
  · intro p' hp' hpne
    have hp'ant : p'.1 + p'.2 = trials := Finset.mem_antidiagonal.mp hp'
    have hp1ne : p'.1 ≠ k := by
      intro hp1
      apply hpne
      apply Prod.ext
      · simpa [pk] using hp1
      · have hp2 : p'.2 = trials - p'.1 := Nat.eq_sub_of_add_eq' hp'ant
        simpa [pk, hp1] using hp2
    refine Finset.sum_eq_zero ?_
    intro g hg
    have hg_mem := (Finset.mem_piAntidiag.mp hg).2
    have hgi0 : g i = 0 := by
      by_contra hgi
      exact hi (hg_mem i hgi)
    have hneq : ¬ (k : ℕ) = (g + fun t ↦ if t = i then p'.1 else 0) i := by
      intro hk_eq
      apply hp1ne
      simpa [hgi0] using hk_eq.symm
    rw [if_neg hneq]

/-- **Marginal distribution:** The pushforward of the multinomial distribution along coordinate `i`
is the binomial distribution with success probability `p i` and `trials` draws. -/
lemma CountDist.multinomial_marginal {m trials : ℕ} (p : FinDist (Fin m)) (i : Fin m) :
    (CountDist.multinomial p trials).map (multinomialCount i) =
      (FinDist.binomial (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials).toCountDist := by
  ext k
  simp only [map_apply, multinomial_apply, tsum_fintype]
  have hsum_eq :
      (∑ counts : MultinomialOutcome m trials,
        if k = multinomialCount i counts then (CountDist.multinomial p trials).pmf counts else 0
        ) =
      (∑ x : {x // x ∈ Finset.Nat.antidiagonalTuple m trials},
        if (k : ℕ) = x.1 i then
          ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ j, (p.pmf j) ^ x.1 j) else 0) :=
    Fintype.sum_equiv (MultinomialOutcome.equivAntidiagonal m trials)
      (fun counts => if k = multinomialCount i counts
                     then (CountDist.multinomial p trials).pmf counts
                     else 0)
      (fun x => if (k : ℕ) = x.1 i then
        ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ j, (p.pmf j) ^ x.1 j) else 0)
      (by
        intro counts
        by_cases hk : (k : ℕ) = counts.1 i
        · have hkeq : k = multinomialCount i counts := by
            apply Fin.ext
            simpa [multinomialCount] using hk
          simp [hkeq, CountDist.multinomial_apply, multinomialCount,
            MultinomialOutcome.equivAntidiagonal]
        · have hkneq : k ≠ multinomialCount i counts := by
            intro h
            apply hk
            exact congrArg Fin.val h
          have hrhs :
              ¬ (k : ℕ) = ((MultinomialOutcome.equivAntidiagonal m trials) counts).1 i := by
            simpa [MultinomialOutcome.equivAntidiagonal] using hk
          dsimp
          rw [if_neg hkneq, if_neg hrhs])
  have hattach :
      (∑ x : {x // x ∈ Finset.Nat.antidiagonalTuple m trials},
        if (k : ℕ) = x.1 i then
          ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ j, (p.pmf j) ^ x.1 j) else 0) =
      Finset.sum (Finset.Nat.antidiagonalTuple m trials) (fun x =>
        if (k : ℕ) = x i then
          ((Nat.multinomial Finset.univ x : ℕ) * ∏ j, (p.pmf j) ^ x j) else 0) := by
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach
      (s := Finset.Nat.antidiagonalTuple m trials)
      (f := fun x => if (k : ℕ) = x i then
        ((Nat.multinomial Finset.univ x : ℕ) * ∏ j, (p.pmf j) ^ x j) else 0)
  calc
    (∑ a, if k = multinomialCount i a then
        ((Nat.multinomial Finset.univ a.1 : ℕ) * ∏ j, (p.pmf j) ^ a.1 j) else 0)
      =
        ∑ x : {x // x ∈ Finset.Nat.antidiagonalTuple m trials},
          if (k : ℕ) = x.1 i then
            ((Nat.multinomial Finset.univ x.1 : ℕ) * ∏ j, (p.pmf j) ^ x.1 j) else 0 := by
          simpa [CountDist.multinomial_apply] using hsum_eq
    _ =
        Finset.sum (Finset.Nat.antidiagonalTuple m trials) (fun x =>
          if (k : ℕ) = x i then
            ((Nat.multinomial Finset.univ x : ℕ) * ∏ j, (p.pmf j) ^ x j) else 0) := hattach
    _ =
        (FinDist.binomial (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials).pmf k := by
          simpa [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple] using
            multinomial_fixed_coordinate_sum p i k

/-- Expectation of a countable distribution over a fintype equals the finite sum. -/
lemma CountDist.expect_eq_finsum {α : Type*} [Encodable α] [Fintype α]
    (d : CountDist α) (f : α → ℝ) :
    d.expect f = ∑ a : α, d.pmf a * f a := by
  simp [CountDist.expect, tsum_fintype]

/-- Expectation commutes with `CountDist.map` for fintype domains. -/
lemma CountDist.expect_map_fintype {α β : Type*} [Encodable α] [Encodable β]
    [Finite α] [Finite β]
    (d : CountDist α) (g : α → β) (f : β → ℝ) :
    (d.map g).expect f = d.expect (f ∘ g) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  rw [CountDist.expect_eq_finsum, CountDist.expect_eq_finsum]
  simp only [CountDist.map_apply, Function.comp, tsum_fintype]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

/-- Expectation of `FinDist.toCountDist` equals `FinDist.expect`. -/
lemma FinDist.toCountDist_expect {n : ℕ} (d : FinDist (Fin n)) (f : Fin n → ℝ) :
    d.toCountDist.expect f = d.expect f := by
  simp [CountDist.expect, FinDist.expect, tsum_fintype, FinDist.toCountDist]

/-- If `d₂ = d₁.map g`, then `𝔼[f; d₂] = 𝔼[f ∘ g; d₁]`. -/
lemma CountDist.expect_congr_map {α β : Type*} [Encodable α] [Encodable β]
    [Finite α] [Finite β]
    (d₁ : CountDist α) (d₂ : CountDist β) (g : α → β) (f : β → ℝ)
    (hmarg : d₁.map g = d₂) :
    d₂.expect f = d₁.expect (f ∘ g) := by
  rw [← hmarg]
  exact CountDist.expect_map_fintype d₁ g f

/-- The expected count for category `i` under the multinomial distribution equals `trials * p i`. -/
lemma CountDist.multinomial_expect_count {m trials : ℕ} (p : FinDist (Fin m)) (i : Fin m) :
    (CountDist.multinomial p trials).expect (fun x => (x.1 i : ℝ)) = (trials : ℝ) * p.pmf i := by
  have hmarg := CountDist.multinomial_marginal (p := p) (trials := trials) i
  have hfun : (fun x : MultinomialOutcome m trials => (x.1 i : ℝ)) =
      (fun k : Fin (trials + 1) => (k : ℝ)) ∘ multinomialCount i := by
    ext x; simp [multinomialCount]
  rw [hfun, ← CountDist.expect_map_fintype _ (multinomialCount i) (fun k => (k : ℝ)), hmarg,
    FinDist.toCountDist_expect]
  exact FinDist.binomial_expect (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials

/-- The variance of coordinate `i` under the multinomial distribution equals
`trials * p i * (1 - p i)`. -/
lemma CountDist.multinomial_variance_count {m trials : ℕ} (p : FinDist (Fin m)) (i : Fin m) :
    (CountDist.multinomial p trials).variance (fun x => (x.1 i : ℝ)) =
      (trials : ℝ) * p.pmf i * (1 - p.pmf i) := by
  have hmarg := CountDist.multinomial_marginal (p := p) (trials := trials) i
  have hfun : (fun x : MultinomialOutcome m trials => (x.1 i : ℝ)) =
      (fun k : Fin (trials + 1) => (k : ℝ)) ∘ multinomialCount i := by
    ext x; simp [multinomialCount]
  have hfun2 : (fun a : MultinomialOutcome m trials => ((a.1 i : ℝ)) ^ 2) =
      (fun k : Fin (trials + 1) => ((k : ℝ)) ^ 2) ∘ multinomialCount i := by
    ext x; simp [multinomialCount]
  rw [CountDist.variance, hfun, hfun2,
    ← CountDist.expect_map_fintype _ (multinomialCount i) (fun k => ((k : ℝ)) ^ 2),
    ← CountDist.expect_map_fintype _ (multinomialCount i) (fun k => (k : ℝ)), hmarg,
    FinDist.toCountDist_expect, FinDist.toCountDist_expect]
  exact FinDist.binomial_variance (p.pmf i) (p.nonneg i) (p.prob_le_one i) trials

end Econlib.Probability
