/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Compound Distribution Non-Vacuity Checks

These tests instantiate compound and multivariate distribution APIs at concrete legal parameters.
They are aimed at parameter-order, coordinate-indexing, and off-diagonal/diagonal semantic drift.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.Compound

open Econlib.Probability MeasureTheory ProbabilityTheory

section betaBinomial

theorem betaBinomial_one_one_two_mean :
    ((FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).expect
      fun i : Fin (2 + 1) => (i : ℝ)) = 1 := by
  calc
    ((FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).expect
        fun i : Fin (2 + 1) => (i : ℝ))
        = (2 : ℝ) * 1 / (1 + 1) := by
          simpa using FinDist.betaBinomial_expect 1 1 (by norm_num) (by norm_num) 2
    _ = 1 := by norm_num

theorem betaBinomial_one_one_two_variance :
    ((FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).variance
      fun i : Fin (2 + 1) => (i : ℝ)) = 2 / 3 := by
  calc
    ((FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).variance
        fun i : Fin (2 + 1) => (i : ℝ))
        = (2 : ℝ) * 1 * 1 * (1 + 1 + 2) / ((1 + 1) ^ 2 * (1 + 1 + 1)) := by
          simpa using FinDist.betaBinomial_variance 1 1 (by norm_num) (by norm_num) 2
    _ = 2 / 3 := by norm_num

theorem betaBinomial_two_six_one_mean_matches_bernoulli_quarter :
    ((FinDist.betaBinomial 2 6 (by norm_num) (by norm_num) 1).expect
      fun i : Fin (1 + 1) => (i : ℝ)) =
        (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).expect
          fun i : Fin 2 => (i : ℝ) := by
  calc
    ((FinDist.betaBinomial 2 6 (by norm_num) (by norm_num) 1).expect
        fun i : Fin (1 + 1) => (i : ℝ))
        = (1 : ℝ) * 2 / (2 + 6) := by
          simpa using FinDist.betaBinomial_expect 2 6 (by norm_num) (by norm_num) 1
    _ = 1 / 4 := by norm_num
    _ = (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).expect
          fun i : Fin 2 => (i : ℝ) := by
        symm
        simpa using FinDist.bernoulli_expect (1 / 4 : ℝ) (by norm_num) (by norm_num)

/-! The symmetric beta-binomial `BetaBin(1, 1, 2)` is the discrete uniform law on `{0, 1, 2}`:
every mass is `1/3`. These numeric witnesses go through the ascending-Pochhammer evaluation of the
beta ratio, exercising the PMF endpoints, the CDF, and the beta-mixture integral. -/

private theorem betaBinomialPMF_uniform_zero : betaBinomialPMF 1 1 2 0 = 1 / 3 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 1 1 (by norm_num) (by norm_num) 2 0 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [h]

private theorem betaBinomialPMF_uniform_one : betaBinomialPMF 1 1 2 1 = 1 / 3 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 1 1 (by norm_num) (by norm_num) 2 1 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [mul_div_assoc, h]; norm_num

private theorem betaBinomialPMF_uniform_two : betaBinomialPMF 1 1 2 2 = 1 / 3 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 1 1 (by norm_num) (by norm_num) 2 2 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [h]

/-- **PMF left endpoint:** `BetaBin(1, 1, 2)` mass at `0` is `1/3` (uniform). -/
theorem betaBinomial_uniform_mass_zero :
    (FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).pmf 0 = 1 / 3 :=
  betaBinomialPMF_uniform_zero

/-- **PMF right endpoint:** `BetaBin(1, 1, 2)` mass at the top `Fin.last 2` is `1/3`, equal to the
mass at `0` — the hallmark of the uniform beta-binomial. -/
theorem betaBinomial_uniform_mass_last :
    (FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).pmf (Fin.last 2) = 1 / 3 :=
  betaBinomialPMF_uniform_two

/-- **CDF reaches one at the top:** the partial sums of the beta-binomial PMF exhaust the unit
mass, `Pr(X ≤ 2) = 1`. -/
theorem betaBinomial_uniform_cdf_last :
    (FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).cdf (Fin.last 2) = 1 := by
  rw [FinDist.betaBinomial_cdf]
  simpa using betaBinomialPMF_sum_one 1 1 (by norm_num) (by norm_num) 2

/-- **CDF midpoint:** `Pr(X ≤ 1) = 2/3` for the uniform beta-binomial, accumulating the first two
of three equal masses. -/
theorem betaBinomial_uniform_cdf_one :
    (FinDist.betaBinomial 1 1 (by norm_num) (by norm_num) 2).cdf 1 = 2 / 3 := by
  rw [FinDist.betaBinomial_cdf]
  norm_num [Finset.sum_range_succ, betaBinomialPMF_uniform_zero, betaBinomialPMF_uniform_one]

/-- **Beta-mixture integral:** integrating the binomial likelihood against the uniform `Beta(1,1)`
prior recovers the (uniform) beta-binomial mass `1/3` — the compound-distribution identity. -/
theorem betaBinomial_mixture_integral :
    (∫ p, betaPDFReal 1 1 p *
        ((Nat.choose 2 ((0 : Fin 3) : ℕ) : ℝ) * p ^ ((0 : Fin 3) : ℕ) *
          (1 - p) ^ (2 - ((0 : Fin 3) : ℕ)))) = 1 / 3 := by
  rw [beta_integral_binomial 1 1 (by norm_num) (by norm_num) 2 0]
  exact betaBinomialPMF_uniform_zero

/-! ### Asymmetric anchors for `BetaBin(2, 6, 2)`

`BetaBin(1,1,2)` is the discrete uniform on `{0,1,2}` — too symmetric to discriminate k ↔ n-k
swaps. The following witnesses use `α = 2, β = 6, n = 2`, which gives a right-skewed distribution
with distinct endpoint masses:

  P(0) = C(2,0)·B(2+0, 2+6)/B(2,6) = B(2,8)/B(2,6).
  B(2,6) = 1!·5!/7! = 120/5040 = 1/42.
  B(2,8) = 1!·7!/9! = 5040/362880 = 1/72.
  P(0) = (1/72)/(1/42) = 42/72 = 7/12.

  P(2) = C(2,2)·B(4,6)/B(2,6) = B(4,6)/B(2,6).
  B(4,6) = 3!·5!/9! = 720/362880 = 1/504.
  P(2) = (1/504)/(1/42) = 42/504 = 1/12.

  P(1) = 1 − 7/12 − 1/12 = 4/12 = 1/3.
  CDF(1) = P(0) + P(1) = 7/12 + 4/12 = 11/12.
-/

private theorem betaBinomialPMF_asymm_zero : betaBinomialPMF 2 6 2 0 = 7 / 12 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 2 6 (by norm_num) (by norm_num) 2 0 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [h]

private theorem betaBinomialPMF_asymm_one : betaBinomialPMF 2 6 2 1 = 1 / 3 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 2 6 (by norm_num) (by norm_num) 2 1 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [mul_div_assoc, h]; norm_num

private theorem betaBinomialPMF_asymm_two : betaBinomialPMF 2 6 2 2 = 1 / 12 := by
  unfold betaBinomialPMF
  have h := beta_ratio_eq_ascPochhammer 2 6 (by norm_num) (by norm_num) 2 2 (by norm_num)
  norm_num [ascPochhammer_succ_right, ascPochhammer_zero] at h ⊢
  rw [h]

/-- **PMF left endpoint (asymmetric):** `BetaBin(2, 6, 2)` mass at `0` is `7/12`.
The endpoint masses `7/12` and `1/12` are distinct, discriminating any k ↔ n-k swap. -/
theorem betaBinomial_asymm_mass_zero :
    (FinDist.betaBinomial 2 6 (by norm_num) (by norm_num) 2).pmf 0 = 7 / 12 :=
  betaBinomialPMF_asymm_zero

/-- **PMF right endpoint (asymmetric):** `BetaBin(2, 6, 2)` mass at the top `Fin.last 2` is `1/12`,
less than the mass `7/12` at `0` — confirming the right-skewed shape. -/
theorem betaBinomial_asymm_mass_last :
    (FinDist.betaBinomial 2 6 (by norm_num) (by norm_num) 2).pmf (Fin.last 2) = 1 / 12 :=
  betaBinomialPMF_asymm_two

/-- **CDF midpoint (asymmetric):** `Pr(X ≤ 1) = 11/12` for `BetaBin(2, 6, 2)`.
P(1) = 1 − 7/12 − 1/12 = 1/3; CDF(1) = 7/12 + 1/3 = 7/12 + 4/12 = 11/12. -/
theorem betaBinomial_asymm_cdf_one :
    (FinDist.betaBinomial 2 6 (by norm_num) (by norm_num) 2).cdf 1 = 11 / 12 := by
  rw [FinDist.betaBinomial_cdf]
  norm_num [Finset.sum_range_succ, betaBinomialPMF_asymm_zero, betaBinomialPMF_asymm_one]

end betaBinomial

section multinomial

private abbrev oneEach : MultinomialOutcome 2 2 :=
  ⟨![1, 1], by norm_num [Fin.sum_univ_two]⟩

theorem multinomial_bernoulli_quarter_two_one_each :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 2).pmf
      oneEach = 3 / 8 := by
  rw [CountDist.multinomial_apply_two_categories]
  norm_num [FinDist.bernoulli, oneEach]

/-- **Asymmetric multinomial anchor — both in category 0:**
For two trials under `Bernoulli(1/4)`, category `0` is "failure" with `p₀ = 3/4` and category `1`
is "success" with `p₁ = 1/4`. The outcome `![2, 0]` (both trials in category 0) has mass
`C(2,2)·(3/4)²·(1/4)⁰ = 9/16`. By contrast the outcome `![0, 2]` has mass `(1/4)² = 1/16`.
The two masses `9/16 ≠ 1/16` discriminate a category-0 ↔ category-1 index swap. -/
theorem multinomial_bernoulli_quarter_two_both_zero :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 2).pmf
      ⟨![2, 0], by norm_num [Fin.sum_univ_two]⟩ = 9 / 16 := by
  rw [CountDist.multinomial_apply_two_categories]
  norm_num [FinDist.bernoulli]

/-- **Asymmetric multinomial anchor — both in category 1:**
For two trials under `Bernoulli(1/4)`, the outcome `![0, 2]` (both in the success category) has
mass `C(2,0)·(3/4)⁰·(1/4)² = 1/16`, distinct from the `9/16` mass at `![2,0]`. -/
theorem multinomial_bernoulli_quarter_two_both_one :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 2).pmf
      ⟨![0, 2], by norm_num [Fin.sum_univ_two]⟩ = 1 / 16 := by
  rw [CountDist.multinomial_apply_two_categories]
  norm_num [FinDist.bernoulli]

theorem multinomial_bernoulli_quarter_one_trial_success :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 1).pmf
      ⟨Pi.single (1 : Fin 2) 1, by simp⟩ = 1 / 4 := by
  calc
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 1).pmf
        ⟨Pi.single (1 : Fin 2) 1, by simp⟩
        = (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 1 := by
          simpa using
            CountDist.multinomial_apply_one_trial_unit_vector
              (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) (1 : Fin 2)
    _ = 1 / 4 := by
      simpa using FinDist.bernoulli_apply_one (1 / 4 : ℝ) (by norm_num) (by norm_num)

theorem multinomial_bernoulli_quarter_four_success_mean :
    ((CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 4).expect
      fun x : MultinomialOutcome 2 4 => (x.1 1 : ℝ)) = 1 := by
  calc
    ((CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 4).expect
        fun x : MultinomialOutcome 2 4 => (x.1 1 : ℝ))
        = (4 : ℝ) *
            (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 1 := by
          simpa using
            CountDist.multinomial_expect_count
              (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) (1 : Fin 2)
    _ = 1 := by
      norm_num [FinDist.bernoulli]

theorem multinomial_bernoulli_quarter_four_failure_mean :
    ((CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 4).expect
      fun x : MultinomialOutcome 2 4 => (x.1 0 : ℝ)) = 3 := by
  calc
    ((CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 4).expect
        fun x : MultinomialOutcome 2 4 => (x.1 0 : ℝ))
        = (4 : ℝ) *
            (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 0 := by
          simpa using
            CountDist.multinomial_expect_count
              (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) (0 : Fin 2)
    _ = 3 := by
      norm_num [FinDist.bernoulli]

theorem multinomial_bernoulli_quarter_four_success_marginal :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 4).map
        (multinomialCount (1 : Fin 2)) =
      (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 4).toCountDist := by
  simpa [FinDist.bernoulli] using
    CountDist.multinomial_marginal
      (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) (1 : Fin 2)

/-- **Zero-trials edge case:** with no trials the multinomial puts all mass on the empty count
vector, so its PMF there is `1`. -/
theorem multinomial_zero_trials_mass_one :
    (CountDist.multinomial (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)) 0).pmf
      ⟨0, by simp⟩ = 1 := by
  rw [CountDist.multinomial_apply_zero_trials]
  simp

/-- **Single-category edge case:** with only one category every multinomial outcome (all `trials`
in that category) has probability `1`. -/
theorem multinomial_single_category_mass_one :
    (CountDist.multinomial (finDist% ![(1 : ℝ)]) 3).pmf ⟨![3], by simp⟩ = 1 :=
  CountDist.multinomial_apply_single_category _ 3 _

end multinomial

section dirichlet

private abbrev dirichletOneTwoThree : DirichletDist 3 where
  alpha := ![1, 2, 3]
  alpha_pos := by
    intro i
    fin_cases i <;> norm_num

theorem dirichlet_one_two_three_alphaSum :
    dirichletOneTwoThree.alphaSum = 6 := by
  norm_num [DirichletDist.alphaSum, dirichletOneTwoThree, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem dirichlet_one_two_three_mean_zero :
    dirichletOneTwoThree.mean (by norm_num) 0 = 1 / 6 := by
  norm_num [DirichletDist.mean, DirichletDist.alphaSum, dirichletOneTwoThree, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem dirichlet_one_two_three_mean_two :
    dirichletOneTwoThree.mean (by norm_num) 2 = 1 / 2 := by
  norm_num [DirichletDist.mean, DirichletDist.alphaSum, dirichletOneTwoThree, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem dirichlet_one_two_three_mean_sum_one :
    ∑ i, dirichletOneTwoThree.mean (by norm_num) i = 1 := by
  simpa using dirichletOneTwoThree.mean_sum_one (by norm_num)

theorem dirichlet_one_two_three_variance_two :
    dirichletOneTwoThree.variance (by norm_num) 2 = 1 / 28 := by
  norm_num [DirichletDist.variance, DirichletDist.alphaSum, dirichletOneTwoThree,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem dirichlet_one_two_three_covariance_zero_one :
    dirichletOneTwoThree.covariance (by norm_num) 0 1 (by decide) = -(1 / 126 : ℝ) := by
  norm_num [DirichletDist.covariance, DirichletDist.alphaSum, dirichletOneTwoThree,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

theorem dirichlet_one_two_three_covariance_zero_one_neg :
    dirichletOneTwoThree.covariance (by norm_num) 0 1 (by decide) < 0 := by
  simpa using dirichletOneTwoThree.covariance_neg (by norm_num) 0 1 (by decide)

theorem dirichlet_uniform_four_mean_two :
    (DirichletDist.uniform 4).mean (by norm_num) (2 : Fin 4) = 1 / 4 := by
  simpa using DirichletDist.uniform_mean 4 (by norm_num) (2 : Fin 4)

/-- **Density positivity:** the Dirichlet density is strictly positive at an interior simplex
point (here the barycenter `(1/3, 1/3, 1/3)`). -/
theorem dirichlet_one_two_three_density_pos :
    0 < dirichletOneTwoThree.density ![1 / 3, 1 / 3, 1 / 3] := by
  apply dirichletOneTwoThree.density_pos (by norm_num)
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
  norm_num [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Normalization:** the Dirichlet density in reduced `(k-1)` coordinates integrates to `1`. -/
theorem dirichlet_one_two_three_normalization :
    ∫ y : Fin (3 - 1) → ℝ, dirichletOneTwoThree.densityReduced (by norm_num) y = 1 :=
  dirichletOneTwoThree.densityReduced_integral_one (by norm_num)

/-- **Marginal Beta:** the first marginal of `Dir(1, 2, 3)` is `Beta(1, 5)`, whose mean matches the
Dirichlet mean `α₀/∑α = 1/6`. -/
theorem dirichlet_one_two_three_marginalBeta_mean :
    (dirichletOneTwoThree.marginalBeta (by norm_num) 0).expect id = 1 / 6 := by
  rw [DirichletDist.marginalBeta_mean]
  norm_num [DirichletDist.mean, DirichletDist.alphaSum, dirichletOneTwoThree, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Genuine marginalization:** beyond moment-matching, the first coordinate of `Dir(1, 2, 3)`
pushes forward to its `Beta(1, 5)` marginal — for every continuous `g`, the Dirichlet coordinate
integral equals the Beta expectation (`marginalBeta_expect` on the concrete instance). -/
example {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ y : Fin (3 - 1) → ℝ, dirichletOneTwoThree.densityReduced (by norm_num) y *
      g (if h : (0 : Fin 3).val < 3 - 1 then y ⟨(0 : Fin 3).val, by omega⟩
         else 1 - ∑ j : Fin (3 - 1), y j)) =
    (dirichletOneTwoThree.marginalBeta (by norm_num) 0).expect g :=
  dirichletOneTwoThree.marginalBeta_expect (by norm_num) 0 hg

/-- **Jeffreys prior:** the symmetric `Dir(1/2, …, 1/2)` on `4` categories has each component mean
`(1/2)/(4·1/2) = 1/4`, equal to the uniform mean. -/
theorem dirichlet_jeffreys_four_mean :
    (DirichletDist.jeffreys 4).mean (by norm_num) 0 = 1 / 4 := by
  norm_num [DirichletDist.mean, DirichletDist.jeffreys, DirichletDist.alphaSum, Finset.sum_const]

/-- **Dirichlet-to-Beta reduction:** the two-category Dirichlet density on `(x, 1-x)` equals the
Beta density `Beta(α₀, α₁)` at `x` — the `Dir` on the `1`-simplex *is* the Beta. -/
theorem dirichlet_two_eq_beta :
    dirichletPDFReal 2 ![2, 3] ![1 / 2, 1 - 1 / 2] = betaPDFReal 2 3 (1 / 2) := by
  simpa using
    dirichletPDFReal_two_eq_betaPDFReal (![2, 3] : Fin 2 → ℝ) (x := 1 / 2) (by norm_num)
      (by norm_num)

/-- **Dirichlet-to-Beta reduction at an asymmetric point:** at `x = 1/3` the
`Dir(2, 3)` density on `(1/3, 2/3)` equals `Beta(2, 3)` density `16/9`, which differs from
the swapped `Beta(3, 2)` density `8/9` at the same point.

Computation: `B(2,3) = 1!·2!/4! = 1/12`, so density `= 12·x·(1-x)²`.
At `x = 1/3`: `12·(1/3)·(2/3)² = 12·(1/3)·(4/9) = 48/27 = 16/9`. -/
theorem dirichlet_two_eq_beta_one_third :
    dirichletPDFReal 2 ![2, 3] ![1 / 3, 1 - 1 / 3] = betaPDFReal 2 3 (1 / 3) := by
  simpa using
    dirichletPDFReal_two_eq_betaPDFReal (![2, 3] : Fin 2 → ℝ) (x := 1 / 3) (by norm_num)
      (by norm_num)

/-- **Value witness:** `Beta(2, 3)` density at `1/3` equals `16/9`. This discriminates a parameter
swap: `Beta(3, 2)` density at `1/3` is `12·(1/3)²·(2/3) = 8/9 ≠ 16/9`. -/
theorem betaPDFReal_two_three_one_third :
    betaPDFReal 2 3 (1 / 3 : ℝ) = 16 / 9 := by
  simp only [betaPDFReal]
  norm_num [ProbabilityTheory.beta, Real.Gamma_add_one, Real.Gamma_one]

end dirichlet

end EconlibTest.Probability.Distributions.Compound

end
