/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Stochastic-Order Non-Vacuity Checks

These are compile-time semantic witnesses for the stochastic-order layer over the Beta and
Dirichlet-Multinomial families: the single-crossing and SOSD facts (`Beta/SingleCrossing.lean`),
the Beta convex order (`Beta/ConvexOrder.lean`), and the Dirichlet-Multinomial marginal convex
order (`DirichletMultinomial/ConvexOrder.lean`).

The Beta witnesses fix the mean frequency `π = 1/4` and the legal concentrations `κ₁ = 2 < κ₂ = 4`,
so they check the *direction* of the order: the **lower**-concentration `betaWithMean π 2` is the
more dispersed law — it is SOSD-dominated by `betaWithMean π 4`, sits above-then-below it in CDF
(single crossing), carries strictly more variance, and convex-order dominates it on convex test
functions. A direction reversal in any of these would flip a witness. The concrete mean anchor
`E[X] = π = 1/4` (`betaWithMean_mean_quarter`) is asymmetric (`π ≠ 1 - π`), so a `π ↦ 1 - π`
shape-swap bug — invisible to the variance/SOSD/convex-order direction alone — is also caught.

The Dirichlet-Multinomial witness uses the **asymmetric** marginal frequency profile
`π = (1/4, 3/4)` over two categories (matching the Beta `π = 1/4` for category `0`), with the same
concentration pair `κ₁ = 2 < κ₂ = 4`. Asymmetry is what makes the marginal-moment anchors below
discriminate a category swap (category `0` and category `1` carry *different* marginal laws) and
keeps the convex-order witness off the degenerate `0 ≤ 0`.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.Order

open Econlib.Probability MeasureTheory Set

section betaSosdAndCrossing

/-- **SOSD direction:** the higher-concentration (sharper) `betaWithMean (1/4) 4` second-order
stochastically dominates the lower-concentration (more dispersed) `betaWithMean (1/4) 2` of the
same mean. -/
theorem betaWithMean_sosd_four_dominates_two :
    CDF.SOSD (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).cdf
      (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).cdf :=
  betaWithMean_sosd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Single crossing of the CDFs:** there is an interior `x₀` where the more-dispersed
`betaWithMean (1/4) 2` CDF crosses from above to below the sharper `betaWithMean (1/4) 4` CDF —
the signature of a mean-preserving spread. -/
theorem beta_cdf_single_crossing_two_four :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ < 1 ∧
      (∀ x, x < x₀ →
        (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).cdf x ≥
        (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).cdf x) ∧
      (∀ x, x₀ < x →
        (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).cdf x ≤
        (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).cdf x) :=
  beta_cdf_single_crossing (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end betaSosdAndCrossing

section betaVariance

/-- **The mean is the asymmetric target frequency** `E[X] = π = 1/4`, for both concentrations. This
is the orientation anchor the variance/SOSD/convex-order witnesses miss: those are all invariant
under the shape swap `π ↦ 1 - π = 3/4` (which keeps the variance and the dispersion ordering), but
the concrete mean `1/4 ≠ 3/4` is not. -/
theorem betaWithMean_mean_quarter_two :
    (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).expect id = 1 / 4 :=
  betaWithMean_expect (by norm_num) (by norm_num) (by norm_num)

theorem betaWithMean_mean_quarter_four :
    (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).expect id = 1 / 4 :=
  betaWithMean_expect (by norm_num) (by norm_num) (by norm_num)

/-- The variance of `betaWithMean (1/4) 2` is `π(1-π)/(κ+1) = (3/16)/3 = 1/16`. -/
theorem betaWithMean_variance_two :
    (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).variance id = 1 / 16 := by
  rw [betaWithMean_variance (pi := (1 / 4 : ℝ)) (kappa := 2) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- The variance of `betaWithMean (1/4) 4` is `(3/16)/5 = 3/80`. -/
theorem betaWithMean_variance_four :
    (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).variance id = 3 / 80 := by
  rw [betaWithMean_variance (pi := (1 / 4 : ℝ)) (kappa := 4) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- **Lower concentration is more spread:** the dispersion ordering `Var(κ=4) < Var(κ=2)` that
underlies the convex order. -/
theorem betaWithMean_variance_decreasing :
    (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).variance id <
      (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).variance id := by
  rw [betaWithMean_variance_two, betaWithMean_variance_four]; norm_num

end betaVariance

section betaConvexOrder

/-- **Convex order direction:** for the convex test function `φ(x) = x²`, the sharper
`betaWithMean (1/4) 4` has the smaller expectation, `E₄[X²] ≤ E₂[X²]` — i.e. the more dispersed
`betaWithMean (1/4) 2` convex-order dominates. -/
theorem betaWithMean_convexOrder_sq :
    (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).expect (fun x => x ^ 2) ≤
      (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).expect
        (fun x => x ^ 2) :=
  betaWithMean_convexOrder (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun x => x ^ 2) (even_two.convexOn_pow.subset (Set.subset_univ _) (convex_Icc 0 1))
    ((continuous_pow 2).continuousOn)

/-- **Canonical convex-order packaging:** `betaWithMean (1/4) 4` lies below `betaWithMean (1/4) 2`
in the library `ConvexOrderOnIcc 0 1`. -/
theorem betaWithMean_convexOrderOnIcc_four_two :
    ConvexOrderOnIcc 0 1
      (betaWithMean (1 / 4) 4 (by norm_num) (by norm_num) (by norm_num)).toProbDist
      (betaWithMean (1 / 4) 2 (by norm_num) (by norm_num) (by norm_num)).toProbDist :=
  betaWithMean_convexOrderOnIcc (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end betaConvexOrder

section dirichletMultinomialConvexOrder

/-- **Asymmetric** two-category frequency profile `π = (1/4, 3/4)`. Asymmetry is essential: under a
symmetric `(1/2, 1/2)` profile category `0` and category `1` carry the *same* marginal law, so a
wrong-coordinate `marginalExpect` would be invisible; here they differ. -/
private abbrev piQ : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- Higher concentration `κ₂ = 4`: `α = (1, 3)`. -/
private abbrev dmHi : DirichletDist 2 where
  alpha := fun i => 4 * piQ i
  alpha_pos := fun i => by fin_cases i <;> norm_num

/-- Lower concentration `κ₁ = 2`: `α = (1/2, 3/2)`. -/
private abbrev dmLo : DirichletDist 2 where
  alpha := fun i => 2 * piQ i
  alpha_pos := fun i => by fin_cases i <;> norm_num

/-- The `binomialExpect` of `k²` over `n = 3` trials is the quadratic `3p + 6p²`:
`E_{Bin(3,p)}[K²] = Var + (E K)² = 3p(1-p) + 9p² = 3p + 6p²`. This is the inner expectation in the
Beta-Binomial mixture identity, evaluated by expanding the explicit Bernstein sum. -/
private theorem binomialExpect_sq_three (p : ℝ) :
    binomialExpect 3 ((fun x : ℝ => x ^ 2) ∘ Nat.cast) p = 3 * p + 6 * p ^ 2 := by
  rw [binomialExpect, Fin.sum_univ_four]
  norm_num [Function.comp_apply, Nat.choose, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((0 : Fin 4) : ℕ) = 0 from rfl]
  ring

/-- The DM marginal second moment `E[K₀²]` for an `α = κ·(1/4, 3/4)` profile over `n = 3` trials,
computed through the Beta-Binomial mixture identity:
`E[K₀²] = E_{Beta(mean 1/4, conc κ)}[3p + 6p²] = 3·(1/4) + 6·(Var + 1/16)`, where
`Var = (1/4·3/4)/(κ+1) = (3/16)/(κ+1)`. -/
private theorem dm_marginalExpect_sq (κ : ℝ) (hκ : 0 < κ)
    (hα_pos : ∀ i, 0 < κ * piQ i) :
    DirichletMultinomial.marginalExpect ⟨fun i => κ * piQ i, hα_pos⟩ (by norm_num) 3 0
        ((fun x : ℝ => x ^ 2) ∘ Nat.cast)
      = 3 * (1 / 4) + 6 * ((3 / 16) / (κ + 1) + (1 / 4) ^ 2) := by
  set d : DirichletDist 2 := ⟨fun i => κ * piQ i, hα_pos⟩ with hd
  have hαsum : d.alphaSum = κ := by
    simp only [hd, DirichletDist.alphaSum, piQ, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hαsum_pos : 0 < d.alphaSum := by rw [hαsum]; exact hκ
  have hmean : d.mean (by norm_num) 0 = 1 / 4 := by
    rw [DirichletDist.mean, hαsum]
    simp only [hd, piQ, Matrix.cons_val_zero]
    field_simp
  have hπ_lt : d.alpha 0 / d.alphaSum < 1 := by
    rw [hαsum]
    simp only [hd, piQ, Matrix.cons_val_zero]
    rw [show κ * (1 / 4) / κ = 1 / 4 by field_simp]
    norm_num
  rw [DirichletMultinomial.marginalExpect_eq_betaBinomial d (by norm_num) 3 0 _ hαsum_pos hπ_lt]
  -- Identify the mixture's `betaWithMean (d.mean .. 0) d.alphaSum` with `betaWithMean (1/4) κ`
  -- (the hypothesis arguments are Props, so only `pi` and `kappa` matter). Avoid `rw` inside the
  -- proof-carrying `betaWithMean` term — the motive would not typecheck — by unfolding both to
  -- `ContDist.beta` and matching the two real parameters.
  set bm := betaWithMean (1 / 4) κ (by norm_num) (by norm_num) hκ with hbm
  have hbm_eq : betaWithMean (d.mean (by norm_num) 0) d.alphaSum
      (div_pos (d.alpha_pos 0) hαsum_pos) (by rw [DirichletDist.mean]; exact hπ_lt) hαsum_pos
      = bm := by
    rw [hbm, betaWithMean, betaWithMean]
    congr 1 <;> rw [hmean, hαsum]
  rw [hbm_eq]
  -- Inner integrand reduces to 3p + 6p²; integrate against betaWithMean (1/4) κ.
  have hbe : (fun p => binomialExpect 3 ((fun x : ℝ => x ^ 2) ∘ Nat.cast) p)
      = fun p => 3 * p + 6 * p ^ 2 := by funext p; exact binomialExpect_sq_three p
  rw [hbe]
  -- E[3p + 6p²] = 3·E[p] + 6·E[p²]; E[p] = 1/4, E[p²] = Var + (1/4)².
  have hmean_p : bm.expect id = 1 / 4 := betaWithMean_expect (by norm_num) (by norm_num) hκ
  have hvar_p : bm.variance id = (3 / 16) / (κ + 1) := by
    rw [hbm, betaWithMean_variance (pi := (1 / 4 : ℝ)) (kappa := κ) (by norm_num) (by norm_num) hκ]
    norm_num
  have hsq_p : bm.expect (fun p => p ^ 2) = (3 / 16) / (κ + 1) + (1 / 4) ^ 2 := by
    -- `variance d f = E[f²] - (E f)²` by definition, with `f = id`.
    have hdef : bm.variance id = bm.expect (fun p => p ^ 2) - (bm.expect id) ^ 2 := rfl
    rw [hvar_p, hmean_p] at hdef
    linarith [hdef]
  have hfun : (fun p : ℝ => 3 * p + 6 * p ^ 2)
      = (fun p : ℝ => 3 * p) + (fun p : ℝ => 6 * p ^ 2) := rfl
  have hint1 : Integrable (fun x => bm.density x * (3 * x)) := by
    rw [hbm]
    exact betaWithMean_integrable_mul_continuous (pi := (1/4 : ℝ)) (kappa := κ)
      (by norm_num) (by norm_num) hκ (fun p => 3 * p) (by fun_prop)
  have hint2 : Integrable (fun x => bm.density x * (6 * x ^ 2)) := by
    rw [hbm]
    exact betaWithMean_integrable_mul_continuous (pi := (1/4 : ℝ)) (kappa := κ)
      (by norm_num) (by norm_num) hκ (fun p => 6 * p ^ 2) (by fun_prop)
  have hsmul1 : (fun p : ℝ => 3 * p) = (3 : ℝ) • (fun p : ℝ => p) := by
    funext p; simp [Pi.smul_apply]
  have hsmul2 : (fun p : ℝ => 6 * p ^ 2) = (6 : ℝ) • (fun p : ℝ => p ^ 2) := by
    funext p; simp [Pi.smul_apply]
  have hint_lin : bm.expect (fun p => 3 * p + 6 * p ^ 2)
      = 3 * bm.expect (fun p => p) + 6 * bm.expect (fun p => p ^ 2) := by
    rw [hfun, bm.expect_add (fun p => 3 * p) (fun p => 6 * p ^ 2) hint1 hint2]
    rw [hsmul1, bm.expect_smul, hsmul2, bm.expect_smul]
  rw [hint_lin]
  have hmean_p' : bm.expect (fun p => p) = 1 / 4 := hmean_p
  rw [hmean_p', hsq_p]

/-- **DM marginal `E[K₀²] = 27/20`** at the higher concentration `κ = 4` (`α = (1, 3)`, `n = 3`).
With `Var(p) = (3/16)/5 = 3/80`, `E[p²] = 3/80 + 1/16 = 1/10`, so `E[K²] = 3/4 + 6/10 = 27/20`. A
concrete, *nonzero* anchor — not the degenerate `0`. -/
theorem dmMarginal_sq_hi : DirichletMultinomial.marginalExpect dmHi (by norm_num) 3 0
    ((fun x : ℝ => x ^ 2) ∘ Nat.cast) = 27 / 20 := by
  rw [show (dmHi : DirichletDist 2) = ⟨fun i => 4 * piQ i, fun i => by fin_cases i <;> norm_num⟩
    from rfl]
  rw [dm_marginalExpect_sq 4 (by norm_num) _]
  norm_num

/-- **DM marginal `E[K₀²] = 3/2`** at the lower concentration `κ = 2` (`α = (1/2, 3/2)`, `n = 3`).
With `Var(p) = (3/16)/3 = 1/16`, `E[p²] = 1/16 + 1/16 = 1/8`, so `E[K²] = 3/4 + 6/8 = 3/2`. -/
theorem dmMarginal_sq_lo : DirichletMultinomial.marginalExpect dmLo (by norm_num) 3 0
    ((fun x : ℝ => x ^ 2) ∘ Nat.cast) = 3 / 2 := by
  rw [show (dmLo : DirichletDist 2) = ⟨fun i => 2 * piQ i, fun i => by fin_cases i <;> norm_num⟩
    from rfl]
  rw [dm_marginalExpect_sq 2 (by norm_num) _]
  norm_num

/-- **DM marginal convex order direction, with concrete strict gap.** For the convex payoff
`φ(k) = k²` over `n = 3` trials, the higher-concentration `DM(4·π)` has the strictly smaller
marginal second moment than the lower-concentration `DM(2·π)`: `27/20 < 3/2` — the lower
concentration produces the more dispersed marginal count. The strict, *nonzero* gap rules out a
tautological `0 ≤ 0` and a wrong-coordinate marginal. -/
theorem dmMarginal_convexOrder_sq :
    DirichletMultinomial.marginalExpect dmHi (by norm_num) 3 0 ((fun x : ℝ => x ^ 2) ∘ Nat.cast) <
      DirichletMultinomial.marginalExpect dmLo (by norm_num) 3 0
        ((fun x : ℝ => x ^ 2) ∘ Nat.cast) := by
  rw [dmMarginal_sq_hi, dmMarginal_sq_lo]; norm_num

end dirichletMultinomialConvexOrder

end EconlibTest.Probability.Distributions.Order

end
