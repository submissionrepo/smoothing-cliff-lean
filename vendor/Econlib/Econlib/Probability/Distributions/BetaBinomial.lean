/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.DirichletMultinomial.Pochhammer
public import Econlib.Probability.FinDist.CDF

/-!
# Beta-binomial distribution

This file defines the beta-binomial probability mass function, the corresponding finite
distribution on `Fin (n + 1)`, its first two moments, and the beta-density integral identities used
to analyze it.

## Main definitions

* `betaBinomialPMF`: Beta-binomial probability mass function.
* `FinDist.betaBinomial`: Beta-binomial distribution.

## Main statements

* `betaBinomialPMF_sum_one`: Normalization of the mass function.
* `FinDist.betaBinomial_apply`: Point-mass formula.
* `FinDist.betaBinomial_cdf`: The CDF at `k` is the partial sum of `betaBinomialPMF` up to `k`.
* `FinDist.betaBinomial_expect`: Expectation formula.
* `FinDist.betaBinomial_variance`: Variance formula.
* `beta_mixed_moment`: Beta mixed-moment identity.
* `beta_integral_binomial`: Binomial-weighted beta integral identity.

## Tags

probability, discrete distributions, beta-binomial
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BigOperators Finset Real

namespace Econlib.Probability

/-- The beta-binomial probability mass function on `{0, …, n}` with Beta prior parameters `α, β`,
defined as `C(n,k) · B(k+α, (n-k)+β) / B(α,β)`. -/
noncomputable def betaBinomialPMF (α β : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ProbabilityTheory.beta ((k : ℝ) + α) ((n - k : ℕ) + β) /
    ProbabilityTheory.beta α β

/-- The beta-binomial PMF is nonneg for positive shape parameters. -/
lemma betaBinomialPMF_nonneg (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n k : ℕ) :
    0 ≤ betaBinomialPMF α β n k := by
  have hkα : 0 < (k : ℝ) + α := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hα
  have hnkβ : 0 < ((n - k : ℕ) : ℝ) + β := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hβ
  unfold betaBinomialPMF
  apply div_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact le_of_lt (ProbabilityTheory.beta_pos hkα hnkβ)
  · exact le_of_lt (ProbabilityTheory.beta_pos hα hβ)

/-- The shifted Beta ratio `B(k+α, (n-k)+β) / B(α,β)` equals `(α)_k · (β)_{n-k} / (α+β)_n`, where
`(·)_m` denotes the ascending Pochhammer symbol. -/
lemma beta_ratio_eq_ascPochhammer (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n k : ℕ) (hk : k ≤ n) :
    ProbabilityTheory.beta (k + α) (n - k + β) / ProbabilityTheory.beta α β =
      (Polynomial.eval α (ascPochhammer ℝ k) *
        Polynomial.eval β (ascPochhammer ℝ (n - k))) /
          Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
  let x : MultinomialOutcome 2 n :=
    ⟨Fin.cons k (Fin.cons (n - k) (Fin.elim0)), by
      simp [hk]⟩
  have hα2 : ∀ i : Fin 2, 0 < (![α, β] i) := by
    intro i
    fin_cases i <;> simpa
  have hm : 0 < 2 := by decide
  have hratio :
      multivariateBeta 2 (fun i => ↑(x.1 i) + ![α, β] i) / multivariateBeta 2 ![α, β] =
        (∏ i, Polynomial.eval (![α, β] i) (ascPochhammer ℝ (x.1 i))) /
          Polynomial.eval (∑ i, ![α, β] i) (ascPochhammer ℝ n) :=
    multivariateBeta_ratio_eq (α := ![α, β]) hα2 hm x
  simpa [multivariateBeta_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, x,
    add_comm, add_left_comm, add_assoc, Nat.cast_sub hk] using hratio

/-- The beta-binomial PMF sums to one over `{0, …, n}`. -/
theorem betaBinomialPMF_sum_one (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k = 1 := by
  have hαβ_pos : 0 < α + β := add_pos hα hβ
  have hΓαβ_ne : Real.Gamma (α + β) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hαβ_pos)
  have hΓnαβ_ne : Real.Gamma (↑n + (α + β)) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGamma_sum_ratio :
      Real.Gamma (↑n + (α + β)) / Real.Gamma (α + β) =
        Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
    rw [add_comm]
    exact Gamma_ratio_eq_ascPochhammer (α + β) hαβ_pos n
  have hPoch_ne : Polynomial.eval (α + β) (ascPochhammer ℝ n) ≠ 0 := by
    rw [← hGamma_sum_ratio]
    exact div_ne_zero hΓnαβ_ne hΓαβ_ne
  have hterm : ∀ k ∈ Finset.range (n + 1),
      betaBinomialPMF α β n k =
        ((n.choose k : ℝ) *
          Polynomial.eval α (ascPochhammer ℝ k) *
          Polynomial.eval β (ascPochhammer ℝ (n - k))) /
            Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkcast : (((n - k : ℕ) : ℝ) + β) = (n : ℝ) - k + β := by
      rw [Nat.cast_sub hk']
    unfold betaBinomialPMF
    calc
      (↑(n.choose k) * ProbabilityTheory.beta ((k : ℝ) + α) (((n - k : ℕ) : ℝ) + β)) /
          ProbabilityTheory.beta α β
        = (n.choose k : ℝ) * (ProbabilityTheory.beta ((k : ℝ) + α)
            ((n : ℝ) - k + β) /  ProbabilityTheory.beta α β) := by
          rw [hkcast]
          ring
      _ = (n.choose k : ℝ) *
            ((Polynomial.eval α (ascPochhammer ℝ k) *
              Polynomial.eval β (ascPochhammer ℝ (n - k))) /
                Polynomial.eval (α + β) (ascPochhammer ℝ n)) := by
              rw [beta_ratio_eq_ascPochhammer α β hα hβ n k hk']
      _ = ((n.choose k : ℝ) *
            Polynomial.eval α (ascPochhammer ℝ k) *
            Polynomial.eval β (ascPochhammer ℝ (n - k))) /
              Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
              ring
  calc
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k
      = ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℝ) *
            Polynomial.eval α (ascPochhammer ℝ k) *
            Polynomial.eval β (ascPochhammer ℝ (n - k))) /
              Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hterm k hk]
    _ = ∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℝ) *
            Polynomial.eval α (ascPochhammer ℝ k) *
            Polynomial.eval β (ascPochhammer ℝ (n - k))) *
              (Polynomial.eval (α + β) (ascPochhammer ℝ n))⁻¹) := by
                simp_rw [div_eq_mul_inv]
    _ = (Polynomial.eval (α + β) (ascPochhammer ℝ n))⁻¹ *
          ∑ k ∈ Finset.range (n + 1),
            ((n.choose k : ℝ) *
              Polynomial.eval α (ascPochhammer ℝ k) *
              Polynomial.eval β (ascPochhammer ℝ (n - k))) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k hk
                ring
  have hcv := chu_vandermonde_two α β n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcv
  have hcv' :
      ∑ k ∈ Finset.range (n + 1),
        ↑(n.choose k) * Polynomial.eval α (ascPochhammer ℝ k) *
          Polynomial.eval β (ascPochhammer ℝ (n - k)) =
        Polynomial.eval (α + β) (ascPochhammer ℝ n) := by
    simpa using hcv
  rw [hcv']
  field_simp [hPoch_ne]

/-- The beta-binomial distribution on `Fin (n + 1)`, obtained by compounding a binomial
distribution `Binomial(n, p)` with a `Beta(α, β)` prior on `p`. -/
noncomputable def FinDist.betaBinomial (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    FinDist (Fin (n + 1)) where
  pmf i := betaBinomialPMF α β n i
  nonneg i := betaBinomialPMF_nonneg α β hα hβ n i
  sum_one := by
    rw [Fin.sum_univ_eq_sum_range]
    exact betaBinomialPMF_sum_one α β hα hβ n

/-- Point-mass formula for the beta-binomial distribution:
`pmf i = C(n,i) · B(i+α, (n-i)+β) / B(α,β)`. -/
lemma FinDist.betaBinomial_apply (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n : ℕ) (i : Fin (n + 1)) :
    (FinDist.betaBinomial α β hα hβ n).pmf i =
      (n.choose (i : ℕ) : ℝ) * ProbabilityTheory.beta ((i : ℕ) + α) ((i.rev : ℕ) + β) /
        ProbabilityTheory.beta α β := by
  simp [FinDist.betaBinomial, betaBinomialPMF, Fin.val_rev]

/-- Closed form for the beta-binomial CDF: The probability of at most `k` successes is the partial
sum of `betaBinomialPMF` up to `k`. -/
lemma FinDist.betaBinomial_cdf (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) (k : Fin (n + 1)) :
    (FinDist.betaBinomial α β hα hβ n).cdf k =
      ∑ i ∈ Finset.range ((k : ℕ) + 1), betaBinomialPMF α β n i :=
  FinDist.cdf_eq_sum_range _ (fun _ => rfl) k

/-- The mass at `0` of the beta-binomial distribution is `B(α, n+β) / B(α,β)`. -/
@[simp] lemma FinDist.betaBinomial_apply_zero (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (FinDist.betaBinomial α β hα hβ n).pmf 0 =
      ProbabilityTheory.beta α (n + β) / ProbabilityTheory.beta α β := by
  simp [FinDist.betaBinomial_apply]

/-- The mass at `Fin.last n` of the beta-binomial distribution is `B(n+α, β) / B(α,β)`. -/
@[simp] lemma FinDist.betaBinomial_apply_last (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (FinDist.betaBinomial α β hα hβ n).pmf (Fin.last n) =
      ProbabilityTheory.beta (n + α) β / ProbabilityTheory.beta α β := by
  simp [FinDist.betaBinomial_apply]

/-- The ratio `B(α+1,β) / B(α,β) = α / (α+β)`. -/
private lemma beta_ratio_add_one (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β = α / (α + β) := by
  simp only [ProbabilityTheory.beta]
  rw [Real.Gamma_add_one (ne_of_gt hα),
      show α + 1 + β = (α + β) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp

/-- The ratio `B(α+2,β) / B(α,β) = α(α+1) / ((α+β)(α+β+1))`. -/
private lemma beta_ratio_add_two (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β =
      α * (α + 1) / ((α + β) * (α + β + 1)) := by
  simp only [ProbabilityTheory.beta]
  rw [show α + 2 = (α + 1) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (by linarith : 0 < α + 1)),
      Real.Gamma_add_one (ne_of_gt hα),
      show α + 1 + 1 + β = ((α + β) + 1) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (by linarith : 0 < (α + β) + 1)),
      Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp

/-- Index-raising identity:
`betaBinomialPMF α β (n+1) (k+1) · (k+1) = (n+1) · α/(α+β) ·
betaBinomialPMF (α+1) β n k`, the
recurrence driving the expectation computation. -/
private lemma betaBinomialPMF_succ_mul_cast (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n k : ℕ) (hk : k ≤ n) :
    betaBinomialPMF α β (n + 1) (k + 1) * ((k + 1 : ℕ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (α / (α + β)) * betaBinomialPMF (α + 1) β n k := by
  have hchoose :
      ((Nat.choose (n + 1) (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  have hsub : n + 1 - (k + 1) = n - k := by omega
  have hshift : (((k + 1 : ℕ) : ℝ) + α) = (k : ℝ) + (α + 1) := by
    push_cast; ring
  have hB : ProbabilityTheory.beta α β ≠ 0 := (ProbabilityTheory.beta_pos hα hβ).ne'
  have hB1 : ProbabilityTheory.beta (α + 1) β ≠ 0 :=
    (ProbabilityTheory.beta_pos (by linarith : 0 < α + 1) hβ).ne'
  have hbeta := beta_ratio_add_one α β hα hβ
  unfold betaBinomialPMF
  rw [hsub, hshift, ← hbeta]
  field_simp [hB, hB1]
  linear_combination
    ProbabilityTheory.beta (↑k + (α + 1)) (↑(n - k) + β) * hchoose

/-- Second index-raising identity, relating `betaBinomialPMF α β (n+2) (k+2)` weighted by the
falling factorial `(k+2)(k+1)` to `betaBinomialPMF (α+2) β n k`; drives the second-moment
computation. -/
private lemma betaBinomialPMF_succ_succ_mul_cast (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n k : ℕ) (hk : k ≤ n) :
    betaBinomialPMF α β (n + 2) (k + 2) * ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
        (α * (α + 1) / ((α + β) * (α + β + 1))) *
          betaBinomialPMF (α + 2) β n k := by
  have hchoose₁ :
      ((Nat.choose (n + 2) (k + 2) : ℝ) * ((k + 2 : ℕ) : ℝ)) =
        ((n + 2 : ℕ) : ℝ) * (Nat.choose (n + 1) (k + 1) : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq (n + 1) (k + 1)).symm
  have hchoose₂ :
      ((Nat.choose (n + 1) (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  have hsub : n + 2 - (k + 2) = n - k := by omega
  have hshift : (((k + 2 : ℕ) : ℝ) + α) = (k : ℝ) + (α + 2) := by
    push_cast; ring
  have hB : ProbabilityTheory.beta α β ≠ 0 := (ProbabilityTheory.beta_pos hα hβ).ne'
  have hB2 : ProbabilityTheory.beta (α + 2) β ≠ 0 :=
    (ProbabilityTheory.beta_pos (by linarith : 0 < α + 2) hβ).ne'
  have hbeta := beta_ratio_add_two α β hα hβ
  unfold betaBinomialPMF
  rw [hsub, hshift, ← hbeta]
  field_simp [hB, hB2]
  linear_combination
    ProbabilityTheory.beta (↑k + (α + 2)) (↑(n - k) + β) * ((k + 1 : ℕ) : ℝ) * hchoose₁ +
      ProbabilityTheory.beta (↑k + (α + 2)) (↑(n - k) + β) * ((n + 2 : ℕ) : ℝ) * hchoose₂

/-- The first moment `∑ k, k · betaBinomialPMF α β n k = n · α/(α+β)`. -/
private lemma betaBinomialPMF_expect_sum (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) =
      (n : ℝ) * α / (α + β) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, add_zero]
      calc
        ∑ x ∈ Finset.range (n + 1),
            betaBinomialPMF α β (n + 1) (x + 1) * ↑(x + 1)
          = ∑ x ∈ Finset.range (n + 1),
              ((n + 1 : ℕ) : ℝ) * (α / (α + β)) *
                betaBinomialPMF (α + 1) β n x := by
              apply Finset.sum_congr rfl
              intro x hx
              exact betaBinomialPMF_succ_mul_cast α β hα hβ n x
                (Nat.le_of_lt_succ (Finset.mem_range.mp hx))
        _ = ((n + 1 : ℕ) : ℝ) * (α / (α + β)) *
            ∑ x ∈ Finset.range (n + 1), betaBinomialPMF (α + 1) β n x := by
              rw [Finset.mul_sum]
        _ = ((n + 1 : ℕ) : ℝ) * α / (α + β) := by
              rw [betaBinomialPMF_sum_one (α + 1) β (by linarith) hβ n]
              ring

/-- The second falling-factorial moment
`∑ k, k(k-1) · betaBinomialPMF α β n k =
n(n-1) · α(α+1) / ((α+β)(α+β+1))`. -/
private lemma betaBinomialPMF_second_factorial_sum (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) * ((k - 1 : ℕ) : ℝ) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * α * (α + 1) / ((α + β) * (α + β + 1)) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          norm_num [Finset.sum_range_succ, betaBinomialPMF]
      | succ n =>
          let f := fun k => betaBinomialPMF α β (n + 2) k * (k : ℝ) * ((k - 1 : ℕ) : ℝ)
          change ∑ k ∈ Finset.range (n + 2 + 1), f k =
            ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * α * (α + 1) /
              ((α + β) * (α + β + 1))
          calc
            ∑ k ∈ Finset.range (n + 2 + 1), f k
              = ∑ x ∈ Finset.range (n + 2), f (x + 1) := by
                  rw [Finset.sum_range_succ']
                  simp [f]
            _ = ∑ x ∈ Finset.range (n + 1), f (x + 1 + 1) := by
                  rw [Finset.sum_range_succ']
                  simp [f]
            _ = ∑ x ∈ Finset.range (n + 1),
                betaBinomialPMF α β (n + 2) (x + 2) * ↑(x + 2) * ↑(x + 1) := by
                  refine Finset.sum_congr rfl fun x _ => ?_
                  simp only [f, show x + 1 + 1 - 1 = x + 1 from by omega]
            _ = ∑ x ∈ Finset.range (n + 1),
                  ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
                    (α * (α + 1) / ((α + β) * (α + β + 1))) *
                      betaBinomialPMF (α + 2) β n x := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  have hxle : x ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
                  simpa [Nat.add_sub_cancel] using
                    betaBinomialPMF_succ_succ_mul_cast α β hα hβ n x hxle
            _ = ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
                (α * (α + 1) / ((α + β) * (α + β + 1))) *
                  ∑ x ∈ Finset.range (n + 1), betaBinomialPMF (α + 2) β n x := by
                  rw [Finset.mul_sum]
            _ = ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * α * (α + 1) /
                ((α + β) * (α + β + 1)) := by
                  rw [betaBinomialPMF_sum_one (α + 2) β (by linarith) hβ n]
                  ring

/-- The second moment `∑ k, k² · betaBinomialPMF α β n k`, obtained by adding the second
falling-factorial moment and the first moment. -/
private lemma betaBinomialPMF_expect_sq_sum (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * α * (α + 1) / ((α + β) * (α + β + 1)) +
        (n : ℝ) * α / (α + β) := by
  rw [← betaBinomialPMF_second_factorial_sum α β hα hβ n,
    ← betaBinomialPMF_expect_sum α β hα hβ n]
  calc
    ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) ^ 2
      = ∑ k ∈ Finset.range (n + 1),
          (betaBinomialPMF α β n k * (k : ℝ) * ((k - 1 : ℕ) : ℝ) +
            betaBinomialPMF α β n k * (k : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_sq : (k : ℝ) ^ 2 = (k : ℝ) * ((k - 1 : ℕ) : ℝ) + (k : ℝ) := by
              cases k <;> simp [pow_two]
              ring
            rw [hk_sq]
            ring
    _ = ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) * ((k - 1 : ℕ) : ℝ) +
        ∑ k ∈ Finset.range (n + 1), betaBinomialPMF α β n k * (k : ℝ) := by
          rw [Finset.sum_add_distrib]

/-- **Expectation of the beta-binomial:** the mean of `BetaBinomial(n, α, β)` is `n · α / (α+β)`. -/
theorem FinDist.betaBinomial_expect (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (FinDist.betaBinomial α β hα hβ n).expect (fun i => (i : ℝ)) =
      (n : ℝ) * α / (α + β) := by
  rw [FinDist.expect_eq_sum, Finset.sum_fin_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (n + 1),
        (if h : i < n + 1 then
          (FinDist.betaBinomial α β hα hβ n).pmf (Fin.mk i h) *
            (((Fin.mk i h : Fin (n + 1)) : ℝ))
         else 0)
      = ∑ i ∈ Finset.range (n + 1), betaBinomialPMF α β n i * (i : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n + 1 := Finset.mem_range.mp hi
          simp [hi', FinDist.betaBinomial]
    _ = (n : ℝ) * α / (α + β) := betaBinomialPMF_expect_sum α β hα hβ n

/-- **Variance of the beta-binomial:** the variance of `BetaBinomial(n, α, β)` is
`n · α · β · (α+β+n) / ((α+β)² · (α+β+1))`. -/
theorem FinDist.betaBinomial_variance (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    (FinDist.betaBinomial α β hα hβ n).variance (fun i => (i : ℝ)) =
      (n : ℝ) * α * β * (α + β + n) / ((α + β) ^ 2 * (α + β + 1)) := by
  rw [FinDist.variance, FinDist.betaBinomial_expect α β hα hβ n]
  rw [FinDist.expect_eq_sum, Finset.sum_fin_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (n + 1),
        (if h : i < n + 1 then
          (FinDist.betaBinomial α β hα hβ n).pmf (Fin.mk i h) *
            ((((Fin.mk i h : Fin (n + 1)) : ℝ)) ^ 2)
         else 0) - ((n : ℝ) * α / (α + β)) ^ 2
      = ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * α * (α + 1) / ((α + β) * (α + β + 1)) +
          (n : ℝ) * α / (α + β)) - ((n : ℝ) * α / (α + β)) ^ 2 := by
          congr 1
          calc
            ∑ i ∈ Finset.range (n + 1),
                (if h : i < n + 1 then
                  (FinDist.betaBinomial α β hα hβ n).pmf (Fin.mk i h) *
                    ((((Fin.mk i h : Fin (n + 1)) : ℝ)) ^ 2)
                 else 0)
              = ∑ i ∈ Finset.range (n + 1), betaBinomialPMF α β n i * (i : ℝ) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  have hi' : i < n + 1 := Finset.mem_range.mp hi
                  simp [hi', FinDist.betaBinomial]
            _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * α * (α + 1) /
                  ((α + β) * (α + β + 1)) +
                (n : ℝ) * α / (α + β) := betaBinomialPMF_expect_sq_sum α β hα hβ n
    _ = (n : ℝ) * α * β * (α + β + n) / ((α + β) ^ 2 * (α + β + 1)) := by
      have hαβ : α + β ≠ 0 := ne_of_gt (add_pos hα hβ)
      have hαβ1 : α + β + 1 ≠ 0 := by linarith [add_pos hα hβ]
      cases n with
      | zero =>
          ring
      | succ n =>
          rw [show n + 1 - 1 = n by omega]
          field_simp [hαβ, hαβ1]
          norm_num
          ring

/-- Pointwise identity relating the Beta density to a shifted Beta density:
`betaPDFReal α β x · x^j · (1-x)^k = (B(j+α, k+β) / B(α,β)) · betaPDFReal (j+α) (k+β) x`. -/
lemma betaPDFReal_mul_pow_pow (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (j k : ℕ) (x : ℝ) :
    betaPDFReal α β x * (x ^ j * (1 - x) ^ k) =
      (beta (↑j + α) (↑k + β) / beta α β) *
        betaPDFReal (↑j + α) (↑k + β) x := by
  simp only [betaPDFReal]
  split_ifs with h
  · have hx_pos : (0 : ℝ) < x := h.1
    have h1mx_pos : (0 : ℝ) < 1 - x := by linarith [h.2]
    have hB : beta α β ≠ 0 := (beta_pos hα hβ).ne'
    have hαj : 0 < ↑j + α := by positivity
    have hβk : 0 < ↑k + β := by positivity
    have hB' : beta (↑j + α) (↑k + β) ≠ 0 := (beta_pos hαj hβk).ne'
    have key_x : x ^ (α - 1) * (x ^ j : ℝ) = x ^ (↑j + α - 1) := by
      rw [← Real.rpow_natCast x j, ← Real.rpow_add hx_pos]
      congr 1
      ring
    have key_1mx : (1 - x) ^ (β - 1) * ((1 - x) ^ k : ℝ) = (1 - x) ^ (↑k + β - 1) := by
      rw [← Real.rpow_natCast (1 - x) k, ← Real.rpow_add h1mx_pos]
      congr 1
      ring
    have lhs_eq :
        1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1) * (x ^ j * (1 - x) ^ k) =
        1 / beta α β * (x ^ (α - 1) * (x ^ j : ℝ)) *
          ((1 - x) ^ (β - 1) * ((1 - x) ^ k : ℝ)) := by ring
    rw [lhs_eq, key_x, key_1mx]
    field_simp
  · simp

/-- **Mixed moments of the Beta distribution:**
`∫ betaPDFReal(α,β,x) · x^j · (1-x)^k dx = B(j+α, k+β) / B(α,β)`. -/
theorem beta_mixed_moment (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (j k : ℕ) :
    ∫ x, betaPDFReal α β x * (x ^ j * (1 - x) ^ k) =
      beta (↑j + α) (↑k + β) / beta α β := by
  have hαj : 0 < ↑j + α := by positivity
  have hβk : 0 < ↑k + β := by positivity
  have hfun : (fun x => betaPDFReal α β x * (x ^ j * (1 - x) ^ k)) =
      fun x => (beta (↑j + α) (↑k + β) / beta α β) * betaPDFReal (↑j + α) (↑k + β) x :=
    funext (betaPDFReal_mul_pow_pow α β hα hβ j k)
  rw [hfun, integral_const_mul, integral_betaPDFReal_eq_one _ _ hαj hβk, mul_one]

/-- **Beta-binomial integral identity:** integrating the binomial likelihood against the Beta prior
recovers the beta-binomial PMF, i.e.,
`∫ betaPDFReal(α,β,p) · C(n,j) · p^j · (1-p)^(n-j) dp = betaBinomialPMF α β n j`. -/
theorem beta_integral_binomial (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (n : ℕ) (j : Fin (n + 1)) :
    ∫ p, betaPDFReal α β p *
      ((n.choose (j : ℕ) : ℝ) * p ^ (j : ℕ) * (1 - p) ^ (n - j)) =
    betaBinomialPMF α β n j := by
  have hfactor : ∀ p, betaPDFReal α β p *
      ((n.choose (j : ℕ) : ℝ) * p ^ (j : ℕ) * (1 - p) ^ (n - ↑j)) =
    (n.choose (j : ℕ) : ℝ) * (betaPDFReal α β p * (p ^ (j : ℕ) * (1 - p) ^ (n - ↑j))) := by
    intro p; ring
  simp_rw [hfactor]
  rw [integral_const_mul, beta_mixed_moment α β hα hβ (j : ℕ) (n - j)]
  unfold betaBinomialPMF
  ring

end Econlib.Probability
