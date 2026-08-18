/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.BetaBinomial

/-!
# Dirichlet-Multinomial distribution

The Dirichlet-Multinomial distribution arises by compounding: If `p ~ Dirichlet(α)` and
`X | p ~ Multinomial(n, p)`, then the marginal distribution of `X` is Dirichlet-Multinomial with
PMF `P(x) = multinomial(x) · B(x + α) / B(α)`, where `B` is the multivariate Beta function
`B(α) = ∏ Γ(αᵢ) / Γ(∑ αᵢ)`.

## Main definitions

* `dirichletMultinomialPMF`: The PMF of the Dirichlet-Multinomial distribution.
* `CountDist.dirichletMultinomial`: The Dirichlet-Multinomial as a `CountDist`.
* `DirichletDist.posteriorUpdate`: The posterior Dirichlet after observing multinomial counts.
* `dirichletMultinomialMarginal`, `dirichletMultinomialPairCorrelation`,
  `dirichletMultinomialConditionalSame`, `dirichletMultinomialConditionalDiff`: Marginal
  probability and correlation structure.

## Main statements

* `dirichletMultinomialPMF_sum_one`: The PMF sums to 1.
* `dirichletMultinomial_marginal_eq_betaBinomialPMF`: The marginal distribution of a single
  coordinate is Beta-Binomial.
* `dirichletMultinomial_expect_coord`: Expectation pushforward — any moment of the category-`k`
  count is the corresponding Beta-Binomial moment.
* `dirichletMultinomialMean_eq_expect`, `dirichletMultinomialVariance_eq_variance`: The closed-form
  mean and variance are the actual expectation and variance of the category count.
* `dirichletMultinomialConditionalSame_eq`, `dirichletMultinomialConditionalDiff_eq`: Conditional
  probabilities expressed via the marginal and pair-correlation parameter.

## Notes

Key distributional properties: `E[Xᵢ] = n · αᵢ / α₀`,
`Var[Xᵢ] = n · (αᵢ/α₀) · (1 - αᵢ/α₀) · (α₀ + n) / (α₀ + 1)`. The distribution reduces to
Multinomial as `α → ∞` (with `αᵢ/α₀` fixed) and has Beta-Binomial marginals.

## Tags

dirichlet-multinomial, compound distribution, beta-binomial, conjugate prior
-/

@[expose] public section

namespace Econlib.Probability

/-- The Dirichlet-Multinomial PMF: `P(x) = multinomial(x) · B(x + α) / B(α)`, where
`x : MultinomialOutcome m n` is a vector of counts summing to `n` and `α : Fin m → ℝ` are the
Dirichlet concentration parameters. Here `B` is the multivariate Beta function. -/
noncomputable def dirichletMultinomialPMF {m : ℕ} (α : Fin m → ℝ) (_hα : ∀ i, 0 < α i)
    {n : ℕ} (x : MultinomialOutcome m n) : ℝ :=
  (Nat.multinomial Finset.univ x.1 : ℝ) *
    multivariateBeta m (fun i => x.1 i + α i) / multivariateBeta m α

/-- The Dirichlet-Multinomial PMF is nonneg for all outcomes `x`. -/
lemma dirichletMultinomialPMF_nonneg {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (hm : 0 < m) {n : ℕ} (x : MultinomialOutcome m n) :
    0 ≤ dirichletMultinomialPMF α hα x := by
  unfold dirichletMultinomialPMF
  apply div_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact le_of_lt (multivariateBeta_pos hm (fun i => by positivity [hα i]))
  · exact le_of_lt (multivariateBeta_pos hm hα)

/-- The Dirichlet-Multinomial PMF sums to 1 over all outcomes `x : MultinomialOutcome m n`. -/
lemma dirichletMultinomialPMF_sum_one {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (hm : 0 < m) (n : ℕ) :
    ∑ x : MultinomialOutcome m n, dirichletMultinomialPMF α hα x = 1 := by
  have hα_sum_pos : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hPoch_ne : Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) ≠ 0 :=
    ne_of_gt (ascPochhammer_pos n _ hα_sum_pos)
  -- Rewrite each PMF term via multivariateBeta_ratio_eq, then apply vandermonde_multinomial.
  have hterm : ∀ x : MultinomialOutcome m n,
      dirichletMultinomialPMF α hα x =
        (↑(Nat.multinomial Finset.univ x.1) *
          ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) := by
    intro x
    unfold dirichletMultinomialPMF
    rw [mul_div_assoc, multivariateBeta_ratio_eq hα hm x, mul_div_assoc]
  simp_rw [hterm, ← Finset.sum_div]
  rw [vandermonde_multinomial, div_self hPoch_ne]

/-- The Dirichlet-Multinomial distribution as a `CountDist`. -/
noncomputable def CountDist.dirichletMultinomial {m : ℕ} (d : DirichletDist m)
    (hm : 0 < m) (n : ℕ) : CountDist (MultinomialOutcome m n) where
  pmf := dirichletMultinomialPMF d.alpha d.alpha_pos
  nonneg := fun x => dirichletMultinomialPMF_nonneg d.alpha_pos hm x
  tsum_one := by
    rw [tsum_fintype]
    exact dirichletMultinomialPMF_sum_one d.alpha_pos hm n

/-- The PMF of `CountDist.dirichletMultinomial` at `x` is `multinomial(x) · B(x + α) / B(α)`. -/
@[simp] lemma CountDist.dirichletMultinomial_apply {m : ℕ} (d : DirichletDist m)
    (hm : 0 < m) (n : ℕ) (x : MultinomialOutcome m n) :
    (CountDist.dirichletMultinomial d hm n).pmf x =
      (Nat.multinomial Finset.univ x.1 : ℝ) *
        multivariateBeta m (fun i => x.1 i + d.alpha i) / multivariateBeta m d.alpha := by
  rfl

/-- When `n = 0`, the only outcome is the zero vector, which has probability 1. -/
lemma CountDist.dirichletMultinomial_zero_trials {m : ℕ} (d : DirichletDist m)
    (hm : 0 < m) (x : MultinomialOutcome m 0) :
    (CountDist.dirichletMultinomial d hm 0).pmf x = 1 := by
  have hzero : x.1 = 0 := by
    funext i; simp only [Pi.zero_apply]
    have hle : x.1 i ≤ ∑ j, x.1 j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [x.2] at hle; omega
  unfold CountDist.dirichletMultinomial dirichletMultinomialPMF
  simp only [hzero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [show Nat.multinomial Finset.univ (0 : Fin m → ℕ) = 1 from by simp [Nat.multinomial]]
  simp [div_self (multivariateBeta_ne_zero hm d.alpha_pos)]

/-- The expected count of category `i` under `CountDist.dirichletMultinomial d hm n` is
`n · αᵢ / α₀`, where `α₀ = ∑ αᵢ`. This closed form is certified as the actual expectation by
`dirichletMultinomialMean_eq_expect`. -/
-- `_hm` is not used in the formula but is kept to parallel `dirichletMultinomialVariance`
-- and to record that `m > 0` is required for the distribution to be well-defined.
noncomputable def DirichletDist.dirichletMultinomialMean {m : ℕ} (d : DirichletDist m)
    (_hm : 0 < m) (n : ℕ) (i : Fin m) : ℝ :=
  n * d.alpha i / d.alphaSum

/-- The variance of the count of category `i` under `CountDist.dirichletMultinomial d hm n` is
`n · (αᵢ/α₀) · (1 - αᵢ/α₀) · (α₀ + n) / (α₀ + 1)`, where `α₀ = ∑ αᵢ`. This closed form is certified
as the actual variance by `dirichletMultinomialVariance_eq_variance`. -/
-- `_hm` is not used in the formula but is kept to record that `m > 0` is required for the
-- distribution to be well-defined.
noncomputable def DirichletDist.dirichletMultinomialVariance {m : ℕ} (d : DirichletDist m)
    (_hm : 0 < m) (n : ℕ) (i : Fin m) : ℝ :=
  n * (d.alpha i / d.alphaSum) * (1 - d.alpha i / d.alphaSum) *
    (d.alphaSum + n) / (d.alphaSum + 1)

/-- The marginal probability of category `k`: `π_k = α_k / ∑ α`. Certified as the first-draw
probability `Pr(θ₁ = k)` of the ordered-draw law by `dirichletMultinomialMarginal_eq_probEvent` (in
`DirichletMultinomial.OrderedDraws`). -/
noncomputable def dirichletMultinomialMarginal {m : ℕ} (α : Fin m → ℝ) (k : Fin m) : ℝ :=
  α k / ∑ i, α i

/-- The pair correlation parameter: `ρ = 1 / (1 + ∑ α)`. -/
noncomputable def dirichletMultinomialPairCorrelation {m : ℕ} (α : Fin m → ℝ) : ℝ :=
  1 / (1 + ∑ i, α i)

/-- The conditional probability `Pr(θ_j = k | θ_i = k)` (same category): `(α_k + 1) / (∑ α + 1)`.
Certified as the conditional probability `Pr(θ₂ = k ∣ θ₁ = k)` of the ordered-draw law by
`dirichletMultinomialConditionalSame_eq_cond` (in `DirichletMultinomial.OrderedDraws`). -/
noncomputable def dirichletMultinomialConditionalSame {m : ℕ} (α : Fin m → ℝ)
    (k : Fin m) : ℝ :=
  (α k + 1) / (∑ i, α i + 1)

/-- The conditional probability `Pr(θ_j = t | θ_i = k)` for `k ≠ t`: `α_t / (∑ α + 1)`. The result
does not depend on `k`; it is kept as an argument to match the interface of
`dirichletMultinomialConditionalSame`. Certified as the conditional probability
`Pr(θ₂ = t ∣ θ₁ = k)` of the ordered-draw law (for `k ≠ t`) by
`dirichletMultinomialConditionalDiff_eq_cond` (in `DirichletMultinomial.OrderedDraws`). -/
-- `_k` is intentionally unused: the formula is the same for all `k ≠ t`.
noncomputable def dirichletMultinomialConditionalDiff {m : ℕ} (α : Fin m → ℝ)
    (_k t : Fin m) : ℝ :=
  α t / (∑ i, α i + 1)

/-- The marginal probability equals the Dirichlet mean: `π_k = α_k / (∑ α)`. -/
lemma dirichletMultinomialMarginal_eq {m : ℕ} (d : DirichletDist m) (hm : 0 < m)
    (k : Fin m) :
    dirichletMultinomialMarginal d.alpha k = d.mean hm k := by
  simp [dirichletMultinomialMarginal, DirichletDist.mean, DirichletDist.alphaSum]

/-- The pair-correlation parameter equals `1 / (1 + ∑ αᵢ)`. -/
lemma dirichletMultinomialPairCorrelation_eq {m : ℕ} (α : Fin m → ℝ) :
    dirichletMultinomialPairCorrelation α = 1 / (1 + ∑ i, α i) := rfl

/-- Conditional same-category: `Pr(θ_j = k | θ_i = k) = π_k + ρ(1 - π_k)`. -/
lemma dirichletMultinomialConditionalSame_eq {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (hm : 0 < m) (k : Fin m) :
    dirichletMultinomialConditionalSame α k =
      dirichletMultinomialMarginal α k +
        dirichletMultinomialPairCorrelation α *
          (1 - dirichletMultinomialMarginal α k) := by
  simp only [dirichletMultinomialConditionalSame, dirichletMultinomialMarginal,
    dirichletMultinomialPairCorrelation]
  have hκ : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hκ1 : (1 + ∑ i, α i) ≠ 0 := by linarith
  have hκ_ne : (∑ i, α i) ≠ 0 := ne_of_gt hκ
  field_simp
  ring

/-- Conditional different-category: `Pr(θ_j = t | θ_i = k) = (1 - ρ) · π_t` for `k ≠ t`. -/
lemma dirichletMultinomialConditionalDiff_eq {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (hm : 0 < m) (k t : Fin m) (_hkt : k ≠ t) :
    dirichletMultinomialConditionalDiff α k t =
      (1 - dirichletMultinomialPairCorrelation α) * dirichletMultinomialMarginal α t := by
  simp only [dirichletMultinomialConditionalDiff, dirichletMultinomialMarginal,
    dirichletMultinomialPairCorrelation]
  have hκ : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hκ1 : (1 + ∑ i, α i) ≠ 0 := by linarith
  have hκ_ne : (∑ i, α i) ≠ 0 := ne_of_gt hκ
  field_simp
  ring

/-- The updated parameters `αᵢ + xᵢ` remain strictly positive after observing multinomial counts
`x`, given that the prior parameters `α` are strictly positive. -/
lemma DirichletDist.posteriorUpdate_alpha_pos {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (_hm : 0 < m) {n : ℕ} (x : MultinomialOutcome m n) :
    ∀ i, 0 < α i + ↑(x.1 i) :=
  fun i => add_pos_of_pos_of_nonneg (hα i) (Nat.cast_nonneg _)

/-- The posterior Dirichlet distribution after observing multinomial counts. -/
noncomputable def DirichletDist.posteriorUpdate {m : ℕ} (d : DirichletDist m)
    {n : ℕ} (x : MultinomialOutcome m n) : DirichletDist m where
  alpha := fun i => d.alpha i + ↑(x.1 i)
  alpha_pos := fun i => add_pos_of_pos_of_nonneg (d.alpha_pos i) (Nat.cast_nonneg _)

/-- The `i`-th parameter of the posterior `d.posteriorUpdate x` is `d.alpha i + x.1 i`. -/
@[simp] lemma DirichletDist.posteriorUpdate_alpha {m : ℕ} (d : DirichletDist m)
    {n : ℕ} (x : MultinomialOutcome m n) (i : Fin m) :
    (d.posteriorUpdate x).alpha i = d.alpha i + ↑(x.1 i) := rfl

/-- Extract coordinate `k` of a `MultinomialOutcome` as a bounded natural number
`x.1 k : Fin (n + 1)`. -/
def MultinomialOutcome.headAt {m n : ℕ} (k : Fin (m + 1))
    (x : MultinomialOutcome (m + 1) n) : Fin (n + 1) :=
  ⟨x.1 k, by
    have : x.1 k ≤ ∑ i, x.1 i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega⟩

/-- Remove coordinate `k` from a `MultinomialOutcome (m + 1) n`, yielding an outcome in
`MultinomialOutcome m (n - x.1 k)`. -/
def MultinomialOutcome.tailAt {m n : ℕ} (k : Fin (m + 1))
    (x : MultinomialOutcome (m + 1) n) :
    MultinomialOutcome m (n - x.1 k) :=
  ⟨fun i => x.1 (k.succAbove i), by
    have hsum := x.2
    rw [Fin.sum_univ_succAbove (f := x.1) k] at hsum
    have hle : x.1 k ≤ n := by
      have := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    have : ∑ i : Fin m, (fun i => x.1 (k.succAbove i)) i = ∑ i : Fin m, x.1 (k.succAbove i) :=
      Finset.sum_congr rfl (fun i _ => rfl)
    rw [this]; omega⟩

/-- Construct a `MultinomialOutcome (m + 1) n` by inserting count `j` at position `k`, with the
remaining counts given by `y : MultinomialOutcome m (n - j)`. -/
def MultinomialOutcome.consAt {m n : ℕ} (k : Fin (m + 1)) (j : Fin (n + 1))
    (y : MultinomialOutcome m (n - j)) : MultinomialOutcome (m + 1) n :=
  ⟨Fin.insertNth k (j : ℕ) y.1, by
    rw [Fin.sum_univ_succAbove (f := Fin.insertNth k (j : ℕ) y.1) k]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    omega⟩

/-- The value of `consAt k j y` at position `k` is `j`. -/
@[simp] lemma MultinomialOutcome.consAt_at {m n : ℕ} (k : Fin (m + 1))
    (j : Fin (n + 1)) (y : MultinomialOutcome m (n - j)) :
    (MultinomialOutcome.consAt k j y).1 k = j := by
  simp [consAt, Fin.insertNth_apply_same]

/-- The value of `consAt k j y` at position `k.succAbove i` is `y.1 i`. -/
@[simp] lemma MultinomialOutcome.consAt_succAbove {m n : ℕ} (k : Fin (m + 1))
    (j : Fin (n + 1)) (y : MultinomialOutcome m (n - j)) (i : Fin m) :
    (MultinomialOutcome.consAt k j y).1 (k.succAbove i) = y.1 i := by
  simp [consAt, Fin.insertNth_apply_succAbove]

/-- The canonical equivalence between `MultinomialOutcome (m + 1) n` and
`Σ j : Fin (n + 1), MultinomialOutcome m (n - j)`, decomposing an outcome at coordinate `k`. -/
def MultinomialOutcome.sigmaEquivAt (m n : ℕ) (k : Fin (m + 1)) :
    MultinomialOutcome (m + 1) n ≃
      Σ (j : Fin (n + 1)), MultinomialOutcome m (n - j) where
  toFun x := ⟨x.headAt k, x.tailAt k⟩
  invFun p := consAt k p.1 p.2
  left_inv x := by
    ext i
    change (consAt k (headAt k x) (tailAt k x)).1 i = x.1 i
    simp only [consAt, headAt, tailAt]
    exact congr_fun (Fin.insertNth_self_removeNth k x.1) i
  right_inv p := by
    ext
    · simp [consAt, headAt, Fin.insertNth_apply_same]
    · rename_i i
      simp [consAt, tailAt, Fin.insertNth_apply_succAbove]

/-- Multinomial coefficient factors when inserting at position `k`:
`multinomial(insertNth k j y) = C(n, j) * multinomial(y)`. -/
lemma MultinomialOutcome.multinomial_consAt {m n : ℕ} (k : Fin (m + 1))
    (j : Fin (n + 1)) (y : MultinomialOutcome m (n - j)) :
    Nat.multinomial Finset.univ (MultinomialOutcome.consAt k j y).1 =
      Nat.choose n j * Nat.multinomial Finset.univ y.1 := by
  have hj_le : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  -- From multinomial_spec: ∏ f(i)! * mult(f) = (∑ f)!
  have hsum_cons : ∑ i, (consAt k j y).1 i = n := (consAt k j y).2
  have spec1 := Nat.multinomial_spec Finset.univ (consAt k j y).1
  rw [hsum_cons] at spec1
  have spec2 := Nat.multinomial_spec Finset.univ y.1
  rw [y.2] at spec2
  -- ∏_{Fin(m+1)} (consAt k j y)(i)! = j! * ∏_{Fin m} y.1(i)!
  have hprod_split : ∏ i : Fin (m + 1),
      ((consAt k j y).1 i).factorial =
    (j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial := by
    rw [Fin.prod_univ_succAbove _ k]
    congr 1
    · simp [consAt_at]
    · exact Finset.prod_congr rfl (fun i _ => by simp [consAt_succAbove])
  rw [hprod_split] at spec1
  have hfact_pos : 0 < (j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos (fun i _ => Nat.factorial_pos _))
  apply Nat.eq_of_mul_eq_mul_left hfact_pos
  calc ((j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial) *
        Nat.multinomial Finset.univ (consAt k j y).1
      = n.factorial := spec1
    _ = Nat.choose n j * (j : ℕ).factorial * (n - j).factorial :=
        (Nat.choose_mul_factorial_mul_factorial hj_le).symm
    _ = Nat.choose n j * ((j : ℕ).factorial *
          ((∏ i : Fin m, (y.1 i).factorial) * Nat.multinomial Finset.univ y.1)) := by
        rw [spec2]; ring
    _ = ((j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial) *
        (Nat.choose n j * Nat.multinomial Finset.univ y.1) := by ring

/-- Product of Pochhammer factors decomposes when inserting at position `k`. -/
lemma MultinomialOutcome.prod_poch_consAt {m n : ℕ} (k : Fin (m + 1))
    (j : Fin (n + 1)) (y : MultinomialOutcome m (n - j)) (α : Fin (m + 1) → ℝ) :
    ∏ i, Polynomial.eval (α i)
        (ascPochhammer ℝ ((consAt k j y).1 i)) =
      Polynomial.eval (α k) (ascPochhammer ℝ j) *
        ∏ i : Fin m, Polynomial.eval (α (k.succAbove i))
          (ascPochhammer ℝ (y.1 i)) := by
  rw [Fin.prod_univ_succAbove _ k]
  congr 1
  · simp [consAt_at]
  · exact Finset.prod_congr rfl (fun i _ => by simp [consAt_succAbove])

/-- The Dirichlet-Multinomial marginal at coordinate `k` equals the Beta-Binomial PMF:
`∑_{x : x_k = j} DM(x | α) = BetaBin(j | α_k, α₀ - α_k, n)`. -/
lemma dirichletMultinomial_marginal_eq_betaBinomialPMF {m : ℕ} (α : Fin (m + 1) → ℝ)
    (hα : ∀ i, 0 < α i) (hm : 1 ≤ m) (n : ℕ) (k : Fin (m + 1)) (j : Fin (n + 1)) :
    ∑ x : MultinomialOutcome (m + 1) n,
      (if x.1 k = j then dirichletMultinomialPMF α hα x else 0) =
    betaBinomialPMF (α k) ((∑ i, α i) - α k) n j := by
  have hm : 0 < m + 1 := Nat.succ_pos m
  have hα_sum_pos : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hsum_rest : ∑ i : Fin m, α (k.succAbove i) = (∑ i, α i) - α k := by
    have := Fin.sum_univ_succAbove α k; linarith
  have hβ_pos : 0 < (∑ i, α i) - α k := by
    rw [← hsum_rest]
    exact Finset.sum_pos (fun i _ => hα (k.succAbove i)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hj_le : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  have hPoch_ne : Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) ≠ 0 :=
    ne_of_gt (ascPochhammer_pos n _ hα_sum_pos)
  -- Rewrite each PMF term in Pochhammer form via `multivariateBeta_ratio_eq`, decompose the sum
  -- over `MultinomialOutcome (m+1) n` using `sigmaEquivAt` to peel off coordinate `k`, isolate
  -- the `j' = j` term, then apply `vandermonde_multinomial` to the residual sum and
  -- `beta_ratio_eq_ascPochhammer` to match the Beta-Binomial PMF.
  have hterm : ∀ x : MultinomialOutcome (m + 1) n,
      dirichletMultinomialPMF α hα x =
        (↑(Nat.multinomial Finset.univ x.1) *
          ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) := by
    intro x
    unfold dirichletMultinomialPMF
    rw [mul_div_assoc, multivariateBeta_ratio_eq hα hm x, mul_div_assoc]
  have hterm_if : ∀ x : MultinomialOutcome (m + 1) n,
      (if x.1 k = j then dirichletMultinomialPMF α hα x else 0) =
      (if x.1 k = j then
        (↑(Nat.multinomial Finset.univ x.1) *
          ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
      else 0) := by
    intro x; split_ifs <;> simp_all
  simp_rw [hterm_if]
  rw [show ∑ x : MultinomialOutcome (m + 1) n,
      (if x.1 k = ↑j then
        (↑(Nat.multinomial Finset.univ x.1) *
          ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
      else 0) =
    ∑ j' : Fin (n + 1), ∑ y : MultinomialOutcome m (n - j'),
      (if (MultinomialOutcome.consAt k j' y).1 k = ↑j then
        (↑(Nat.multinomial Finset.univ (MultinomialOutcome.consAt k j' y).1) *
          ∏ i, Polynomial.eval (α i)
            (ascPochhammer ℝ ((MultinomialOutcome.consAt k j' y).1 i))) /
              Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
      else 0)
    from by
      rw [← Fintype.sum_sigma']
      refine Fintype.sum_equiv (MultinomialOutcome.sigmaEquivAt m n k) _ _ (fun x => ?_)
      simp only [MultinomialOutcome.sigmaEquivAt, Equiv.coe_fn_mk]
      have hinv : (MultinomialOutcome.consAt k (x.headAt k) (x.tailAt k)).1 = x.1 :=
        congrArg Subtype.val ((MultinomialOutcome.sigmaEquivAt m n k).left_inv x)
      simp only [hinv]]
  simp only [MultinomialOutcome.consAt_at]
  have hsum_eq : ∀ j' : Fin (n + 1), j' ≠ j →
      ∀ y : MultinomialOutcome m (n - j'),
        (if (j' : ℕ) = (j : ℕ) then
          (↑(Nat.multinomial Finset.univ (MultinomialOutcome.consAt k j' y).1) *
            ∏ i, Polynomial.eval (α i)
              (ascPochhammer ℝ ((MultinomialOutcome.consAt k j' y).1 i))) /
                Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
        else 0) = 0 := by
    intro j' hj' y
    simp [Fin.val_ne_of_ne hj']
  rw [show ∑ j' : Fin (n + 1), ∑ y : MultinomialOutcome m (n - j'),
      (if (j' : ℕ) = (j : ℕ) then _ else 0) =
    ∑ y : MultinomialOutcome m (n - j),
      (↑(Nat.multinomial Finset.univ (MultinomialOutcome.consAt k j y).1) *
        ∏ i, Polynomial.eval (α i)
          (ascPochhammer ℝ ((MultinomialOutcome.consAt k j y).1 i))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
    from by
      have : ∀ j' : Fin (n + 1), j' ≠ j →
          ∑ y : MultinomialOutcome m (n - j'),
            (if (j' : ℕ) = (j : ℕ) then
              (↑(Nat.multinomial Finset.univ (MultinomialOutcome.consAt k j' y).1) *
                ∏ i, Polynomial.eval (α i)
                  (ascPochhammer ℝ ((MultinomialOutcome.consAt k j' y).1 i))) /
                    Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)
            else 0) = 0 := by
        intro j' hj'
        exact Finset.sum_eq_zero (fun y _ => hsum_eq j' hj' y)
      rw [Fintype.sum_eq_single j (fun j' hj' => this j' hj')]
      simp]
  simp_rw [MultinomialOutcome.multinomial_consAt k j,
    MultinomialOutcome.prod_poch_consAt k j _ α]
  simp_rw [Nat.cast_mul]
  have hrearrange : ∀ y : MultinomialOutcome m (n - j),
      (↑(Nat.choose n ↑j) * ↑(Nat.multinomial Finset.univ y.1) *
        (Polynomial.eval (α k) (ascPochhammer ℝ ↑j) *
          ∏ i : Fin m, Polynomial.eval (α (k.succAbove i)) (ascPochhammer ℝ (y.1 i)))) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) =
      (↑(Nat.choose n ↑j) * Polynomial.eval (α k) (ascPochhammer ℝ ↑j)) /
        Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) *
        (↑(Nat.multinomial Finset.univ y.1) *
          ∏ i : Fin m, Polynomial.eval (α (k.succAbove i)) (ascPochhammer ℝ (y.1 i))) := by
    intro y; ring
  simp_rw [hrearrange, ← Finset.mul_sum]
  rw [vandermonde_multinomial (fun i => α (k.succAbove i)) (n - j)]
  rw [hsum_rest]
  unfold betaBinomialPMF
  have hαβ : α k + ((∑ i, α i) - α k) = ∑ i, α i := by ring
  have h_beta := beta_ratio_eq_ascPochhammer (α k) ((∑ i, α i) - α k) (hα k) hβ_pos n (↑j) hj_le
  rw [hαβ] at h_beta
  calc ↑(Nat.choose n ↑j) * Polynomial.eval (α k) (ascPochhammer ℝ ↑j) /
          Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) *
        Polynomial.eval (∑ i, α i - α k) (ascPochhammer ℝ (n - ↑j))
      = ↑(Nat.choose n ↑j) * (Polynomial.eval (α k) (ascPochhammer ℝ ↑j) *
          Polynomial.eval (∑ i, α i - α k) (ascPochhammer ℝ (n - ↑j)) /
            Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n)) := by ring
    _ = ↑(Nat.choose n ↑j) * (ProbabilityTheory.beta (↑↑j + α k) (↑(n - ↑j) + (∑ i, α i - α k)) /
          ProbabilityTheory.beta (α k) (∑ i, α i - α k)) := by
        congr 1
        have : (↑(n - ↑j) : ℝ) = ↑n - ↑↑j := by
          rw [Nat.cast_sub hj_le]
        rw [this]
        exact h_beta.symm
    _ = _ := by ring

/-- The "rest" mass `α₀ − α_k = ∑_{i ≠ k} αᵢ` is strictly positive when there are at least two
categories, so the Beta-Binomial marginal `BetaBinomial(α_k, α₀ − α_k, n)` is nondegenerate. -/
lemma DirichletDist.alphaSum_sub_alpha_pos {m : ℕ} (d : DirichletDist (m + 1)) (hm : 1 ≤ m)
    (k : Fin (m + 1)) : 0 < d.alphaSum - d.alpha k := by
  have hsum_rest : ∑ i : Fin m, d.alpha (k.succAbove i) = d.alphaSum - d.alpha k := by
    have := Fin.sum_univ_succAbove d.alpha k
    simp only [DirichletDist.alphaSum]; linarith
  rw [← hsum_rest]
  exact Finset.sum_pos (fun i _ => d.alpha_pos (k.succAbove i)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

/-- **Expectation pushforward to the Beta-Binomial marginal.** For any `g : ℕ → ℝ`, the
Dirichlet-Multinomial expectation of `g (X_k)` (with `X_k` the count of category `k`) equals the
Beta-Binomial expectation of `g`. This is the distribution-level upgrade of
`dirichletMultinomial_marginal_eq_betaBinomialPMF`: It transports every moment of the marginal
count `X_k ~ BetaBinomial(α_k, α₀ − α_k, n)` from the Beta-Binomial family, so the closed-form mean
and variance below are derived facts rather than definitions. -/
lemma dirichletMultinomial_expect_coord {m : ℕ} (d : DirichletDist (m + 1)) (hm : 1 ≤ m)
    (n : ℕ) (k : Fin (m + 1)) (g : ℕ → ℝ) :
    (CountDist.dirichletMultinomial d (Nat.succ_pos m) n).expect (fun x => g (x.1 k)) =
      (FinDist.betaBinomial (d.alpha k) (d.alphaSum - d.alpha k)
        (d.alpha_pos k) (d.alphaSum_sub_alpha_pos hm k) n).expect (fun j => g (j : ℕ)) := by
  -- Regroup `∑_x pmf(x)·g(x_k)` by the value `j = x_k ∈ Fin (n+1)` (fiberwise via `headAt k`);
  -- on the fiber `x_k = j` the factor `g(x_k) = g j` is constant, and the residual fiber mass
  -- `∑_{x : x_k = j} pmf(x)` is `betaBinomialPMF α_k (α₀ − α_k) n j` by the marginal theorem.
  rw [CountDist.expect_eq_tsum, tsum_fintype, FinDist.expect_eq_sum]
  -- Identify the unfolded DM pmf with `dirichletMultinomialPMF` and the BetaBinomial pmf with
  -- `betaBinomialPMF`, then reduce `α₀ - α k = (∑ i, α i) - α k`.
  have hpmf : ∀ x : MultinomialOutcome (m + 1) n,
      (CountDist.dirichletMultinomial d (Nat.succ_pos m) n).pmf x =
        dirichletMultinomialPMF d.alpha d.alpha_pos x := fun _ => rfl
  have hbb : ∀ j : Fin (n + 1),
      (FinDist.betaBinomial (d.alpha k) (d.alphaSum - d.alpha k)
          (d.alpha_pos k) (d.alphaSum_sub_alpha_pos hm k) n).pmf j =
        betaBinomialPMF (d.alpha k) (d.alphaSum - d.alpha k) n j := fun _ => rfl
  simp_rw [hpmf, hbb]
  -- The "rest" mass `(∑ i, α i) - α k` from the marginal theorem equals `α₀ - α k`.
  have hαsum : (∑ i, d.alpha i) - d.alpha k = d.alphaSum - d.alpha k := by
    simp only [DirichletDist.alphaSum]
  -- Fiberwise regroup the LHS by `MultinomialOutcome.headAt k`.
  have hm1 : 1 ≤ m := hm
  rw [← Finset.sum_fiberwise Finset.univ (fun x => MultinomialOutcome.headAt k x)
        (fun x => dirichletMultinomialPMF d.alpha d.alpha_pos x * g (x.1 k))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- On the fiber `headAt k x = j` we have `x.1 k = ↑j`, so `g (x.1 k) = g ↑j` is constant.
  have hfiber : ∀ x ∈ Finset.univ.filter (fun x => MultinomialOutcome.headAt k x = j),
      dirichletMultinomialPMF d.alpha d.alpha_pos x * g (x.1 k) =
        g (j : ℕ) * dirichletMultinomialPMF d.alpha d.alpha_pos x := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxk : x.1 k = (j : ℕ) := by
      have := hx.2
      rwa [MultinomialOutcome.headAt, Fin.ext_iff] at this
    rw [hxk]; ring
  rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum]
  -- Turn the filtered fiber mass into the marginal-theorem form and apply it.
  have hmass : ∑ x ∈ Finset.univ.filter (fun x => MultinomialOutcome.headAt k x = j),
      dirichletMultinomialPMF d.alpha d.alpha_pos x =
      betaBinomialPMF (d.alpha k) (d.alphaSum - d.alpha k) n j := by
    rw [Finset.sum_filter]
    have hbridge : ∀ x : MultinomialOutcome (m + 1) n,
        (if MultinomialOutcome.headAt k x = j then
            dirichletMultinomialPMF d.alpha d.alpha_pos x else 0) =
          (if x.1 k = (j : ℕ) then dirichletMultinomialPMF d.alpha d.alpha_pos x else 0) := by
      intro x
      congr 1
      rw [MultinomialOutcome.headAt, Fin.ext_iff]
    simp_rw [hbridge]
    rw [dirichletMultinomial_marginal_eq_betaBinomialPMF d.alpha d.alpha_pos hm1 n k j, hαsum]
  rw [hmass]; ring

/-- **The closed-form Dirichlet-Multinomial mean is the actual expected count.** The expectation of
the category-`k` count under `CountDist.dirichletMultinomial` equals `dirichletMultinomialMean`,
i.e. `n · α_k / α₀`. Derived from the Beta-Binomial marginal via
`dirichletMultinomial_expect_coord`. -/
theorem dirichletMultinomialMean_eq_expect {m : ℕ} (d : DirichletDist (m + 1)) (hm : 1 ≤ m)
    (n : ℕ) (k : Fin (m + 1)) :
    (CountDist.dirichletMultinomial d (Nat.succ_pos m) n).expect (fun x => (x.1 k : ℝ)) =
      d.dirichletMultinomialMean (Nat.succ_pos m) n k := by
  have h := dirichletMultinomial_expect_coord d hm n k (fun t => (t : ℝ))
  rw [h]
  -- The Beta-Binomial expectation of `fun j => ((↑j : ℕ) : ℝ)` is the standard `fun i => (i : ℝ)`.
  rw [FinDist.betaBinomial_expect (d.alpha k) (d.alphaSum - d.alpha k)
        (d.alpha_pos k) (d.alphaSum_sub_alpha_pos hm k) n]
  -- Reconcile the denominator `α_k + (α₀ − α_k) = α₀` and unfold `dirichletMultinomialMean`.
  have hdenom : d.alpha k + (d.alphaSum - d.alpha k) = d.alphaSum := by ring
  rw [hdenom]
  rfl

/-- **The closed-form Dirichlet-Multinomial variance is the actual variance of the count.** The
variance of the category-`k` count under `CountDist.dirichletMultinomial` equals
`dirichletMultinomialVariance`, i.e. `n · (α_k/α₀) · (1 − α_k/α₀) · (α₀ + n) / (α₀ + 1)`. Derived
from the Beta-Binomial marginal via `dirichletMultinomial_expect_coord`. -/
theorem dirichletMultinomialVariance_eq_variance {m : ℕ} (d : DirichletDist (m + 1)) (hm : 1 ≤ m)
    (n : ℕ) (k : Fin (m + 1)) :
    (CountDist.dirichletMultinomial d (Nat.succ_pos m) n).variance (fun x => (x.1 k : ℝ)) =
      d.dirichletMultinomialVariance (Nat.succ_pos m) n k := by
  -- Unfold DM variance into second-moment minus squared first-moment, push each through the
  -- Beta-Binomial marginal via `dirichletMultinomial_expect_coord`, fold back into
  -- `FinDist.variance`, and apply the Beta-Binomial variance formula.
  rw [CountDist.variance]
  have h2 := dirichletMultinomial_expect_coord d hm n k (fun t => (t : ℝ) ^ 2)
  have h1 := dirichletMultinomial_expect_coord d hm n k (fun t => (t : ℝ))
  rw [h2, h1, ← FinDist.variance]
  rw [FinDist.betaBinomial_variance (d.alpha k) (d.alphaSum - d.alpha k)
        (d.alpha_pos k) (d.alphaSum_sub_alpha_pos hm k) n]
  -- Identify `α + β = α₀` and clear denominators; uses `α₀ > 0` and `α₀ + 1 > 0`.
  have hα0_pos : 0 < d.alphaSum := d.alphaSum_pos (Nat.succ_pos m)
  have hαβ : d.alpha k + (d.alphaSum - d.alpha k) = d.alphaSum := by ring
  rw [DirichletDist.dirichletMultinomialVariance, hαβ]
  have hα0_ne : d.alphaSum ≠ 0 := ne_of_gt hα0_pos
  have hα01_ne : d.alphaSum + 1 ≠ 0 := by positivity
  field_simp

end Econlib.Probability
