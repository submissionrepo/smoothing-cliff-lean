/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Dirichlet-Multinomial Non-Vacuity Checks

These are compile-time semantic witnesses for the Dirichlet-Multinomial API
(`DirichletMultinomial/Basic.lean`, `DirichletMultinomial/Pochhammer.lean`). They instantiate the
marginal, pair-correlation, conditional, mean/variance, posterior-update, normalization, and
marginal-to-Beta-Binomial facts at the concrete concentration vector `α = (1, 2, 3)` so that a
witness would catch a same-vs-different conditional swap, an `α₀ + 1` denominator slip, a
posterior-update direction flip, or a wrong Beta-Binomial complement parameter.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.DirichletMultinomial

open Econlib.Probability

/-- The concentration vector `α = (1, 2, 3)`, with `αsum = ∑ αᵢ = 6` and `α[0] = 1`. -/
private abbrev a123 : Fin 3 → ℝ := ![1, 2, 3]

private abbrev d123 : DirichletDist 3 where
  alpha := a123
  alpha_pos := by intro i; fin_cases i <;> norm_num

private theorem a123_pos : ∀ i, 0 < a123 i := by intro i; fin_cases i <;> norm_num

section marginalAndCorrelation

/-- The marginal probability of category `0` is `α₀/∑α = 1/6`. -/
theorem dm_marginal_zero :
    dirichletMultinomialMarginal a123 0 = 1 / 6 := by
  norm_num [dirichletMultinomialMarginal, a123, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The marginal probability equals the Dirichlet mean. -/
theorem dm_marginal_eq_mean :
    dirichletMultinomialMarginal d123.alpha 1 = d123.mean (by norm_num) 1 :=
  dirichletMultinomialMarginal_eq d123 (by norm_num) 1

/-- The pair-correlation parameter is `ρ = 1/(1 + ∑α) = 1/7`. -/
theorem dm_pairCorrelation :
    dirichletMultinomialPairCorrelation a123 = 1 / 7 := by
  norm_num [dirichletMultinomialPairCorrelation, a123, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

end marginalAndCorrelation

section conditionals

/-- **Same-category conditional** `Pr(θⱼ = 0 ∣ θᵢ = 0) = (α₀ + 1)/(∑α + 1) = 2/7`: observing a
draw in category `0` raises the count by one, so the conditional exceeds the marginal `1/6`. -/
theorem dm_conditionalSame_zero :
    dirichletMultinomialConditionalSame a123 0 = 2 / 7 := by
  norm_num [dirichletMultinomialConditionalSame, a123, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Different-category conditional** `Pr(θⱼ = 2 ∣ θᵢ = 0) = α₂/(∑α + 1) = 3/7` for `0 ≠ 2`: the
result depends only on the target category `2`, not the conditioning category `0`. -/
theorem dm_conditionalDiff_zero_two :
    dirichletMultinomialConditionalDiff a123 0 2 = 3 / 7 := by
  norm_num [dirichletMultinomialConditionalDiff, a123, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Independence of conditioning category:** `Pr(θⱼ = 2 ∣ θᵢ = 0) = Pr(θⱼ = 2 ∣ θᵢ = 1) = 3/7`.
The different-category conditional depends only on the *target* category `2` and the total `∑α`,
not on which conditioning category `0` or `1` is used. This catches a bug that makes the
conditional depend on `α[conditioning_category]` instead of being category-independent. -/
theorem dm_conditionalDiff_conditioning_independent :
    dirichletMultinomialConditionalDiff a123 0 2 =
      dirichletMultinomialConditionalDiff a123 1 2 := by
  norm_num [dirichletMultinomialConditionalDiff, a123, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Same-category decomposition bridge:** `Pr(θⱼ = 0 ∣ θᵢ = 0) = πₒ + ρ(1 - πₒ)`, the marginal
nudged upward by the correlation `ρ`. -/
theorem dm_conditionalSame_decomp :
    dirichletMultinomialConditionalSame a123 0 =
      dirichletMultinomialMarginal a123 0 +
        dirichletMultinomialPairCorrelation a123 * (1 - dirichletMultinomialMarginal a123 0) :=
  dirichletMultinomialConditionalSame_eq a123_pos (by norm_num) 0

/-- **Different-category decomposition bridge:** `Pr(θⱼ = 2 ∣ θᵢ = 0) = (1 - ρ)·π₂`, the marginal
shaded *down* by the correlation `ρ`. -/
theorem dm_conditionalDiff_decomp :
    dirichletMultinomialConditionalDiff a123 0 2 =
      (1 - dirichletMultinomialPairCorrelation a123) * dirichletMultinomialMarginal a123 2 :=
  dirichletMultinomialConditionalDiff_eq a123_pos (by norm_num) 0 2 (by decide)

end conditionals

section momentsAndUpdate

/-- The expected count of category `1` over `4` trials is `n·α₁/α₀ = 4·2/6 = 4/3`. -/
theorem dm_mean_four_one :
    DirichletDist.dirichletMultinomialMean d123 (by norm_num) 4 1 = 4 / 3 := by
  norm_num [DirichletDist.dirichletMultinomialMean, DirichletDist.alphaSum, a123, d123,
    Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- The count variance of category `1` over `4` trials is
`n·(α₁/α₀)(1 - α₁/α₀)·(α₀ + n)/(α₀ + 1) = 4·(1/3)(2/3)·(10/7) = 80/63`. -/
theorem dm_variance_four_one :
    DirichletDist.dirichletMultinomialVariance d123 (by norm_num) 4 1 = 80 / 63 := by
  norm_num [DirichletDist.dirichletMultinomialVariance, DirichletDist.alphaSum, a123, d123,
    Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- **Posterior update is additive in the observed counts:** after observing counts `x`, the
posterior concentration in category `1` is `α₁ + x₁`. With a unit observation in category `1`
this is `2 + 1 = 3`. -/
theorem dm_posteriorUpdate_alpha_one :
    (d123.posteriorUpdate (⟨![0, 1, 0], by decide⟩ : MultinomialOutcome 3 1)).alpha 1 = 3 := by
  rw [DirichletDist.posteriorUpdate_alpha]
  norm_num [a123, d123]

/-- **All-coordinates posterior update (asymmetric observation):** after observing 6 trials with
counts `![1, 2, 3]`, the posterior concentration vector is `(1+1, 2+2, 3+3) = (2, 4, 6)`. The
three distinct values catch a coordinate-permutation bug that a single-coordinate check cannot.

- `posteriorAlpha 0 = α[0] + x[0] = 1 + 1 = 2`
- `posteriorAlpha 1 = α[1] + x[1] = 2 + 2 = 4`
- `posteriorAlpha 2 = α[2] + x[2] = 3 + 3 = 6` -/
theorem dm_posteriorUpdate_all_coords :
    let obs : MultinomialOutcome 3 6 := ⟨![1, 2, 3], by decide⟩
    (d123.posteriorUpdate obs).alpha 0 = 2 ∧
    (d123.posteriorUpdate obs).alpha 1 = 4 ∧
    (d123.posteriorUpdate obs).alpha 2 = 6 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (rw [DirichletDist.posteriorUpdate_alpha];
     norm_num [a123, d123, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

end momentsAndUpdate

section normalizationAndMarginalLaw

/-- **The Dirichlet-Multinomial PMF normalizes:** over the `2`-trial outcomes it sums to `1`
(exercises the multivariate Chu–Vandermonde identity). -/
theorem dm_pmf_sum_one_two :
    ∑ x : MultinomialOutcome 3 2, dirichletMultinomialPMF a123 a123_pos x = 1 :=
  dirichletMultinomialPMF_sum_one a123_pos (by norm_num) 2

/-- **Zero trials puts all mass on the empty count vector:** the PMF at the unique `0`-trial
outcome is `1`. -/
theorem dm_zero_trials :
    (CountDist.dirichletMultinomial d123 (by norm_num) 0).pmf (⟨0, by simp⟩) = 1 :=
  CountDist.dirichletMultinomial_zero_trials d123 (by norm_num) _

/-- **The DM marginal is Beta-Binomial:** summing the joint PMF over outcomes with `x₀ = 1`
recovers `BetaBin(j = 1 ∣ α[0] = 1, αsum − α[0] = 5, n = 2)`. The complement parameter is
`αsum − α[0] = 5`, catching a wrong residual-concentration in the marginal. -/
theorem dm_marginal_eq_betaBinomial :
    ∑ x : MultinomialOutcome 3 2,
      (if x.1 0 = (1 : Fin 3) then dirichletMultinomialPMF a123 a123_pos x else 0) =
    betaBinomialPMF 1 5 2 1 := by
  have hβ : (∑ i, a123 i) - a123 0 = 5 := by
    norm_num [a123, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  rw [dirichletMultinomial_marginal_eq_betaBinomialPMF a123 a123_pos (by norm_num) 2 0 1, hβ]
  norm_num [a123, Matrix.cons_val_zero, Fin.val_one]

/-- **DM marginal at coordinate 1 is Beta-Binomial (nonzero-coordinate witness):** summing the
joint PMF over outcomes with `x₁ = 1` recovers `BetaBin(j = 1 ∣ α[1] = 2, αsum − α[1] = 4, n = 2)`.
This witnesses the marginal identity at a non-zero coordinate, catching a bug that confuses the
target coordinate's α with the residual complement. -/
theorem dm_marginal_eq_betaBinomial_coord_one :
    ∑ x : MultinomialOutcome 3 2,
      (if x.1 1 = (1 : Fin 3) then dirichletMultinomialPMF a123 a123_pos x else 0) =
    betaBinomialPMF 2 4 2 1 := by
  have hβ : (∑ i, a123 i) - a123 1 = 4 := by
    norm_num [a123, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  rw [dirichletMultinomial_marginal_eq_betaBinomialPMF a123 a123_pos (by norm_num) 2 1 1, hβ]
  norm_num [a123, Matrix.cons_val_one, Fin.val_one]

end normalizationAndMarginalLaw

end EconlibTest.Probability.Distributions.DirichletMultinomial

end
