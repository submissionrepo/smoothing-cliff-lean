/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.IntegralReal
public import Econlib.Probability.Distributions.Beta.ConvexOrder
public import Econlib.Probability.Distributions.BetaBinomial
public import Econlib.Probability.Distributions.Binomial.Tail.Convexity
public import Econlib.Probability.Distributions.DirichletMultinomial.Basic

/-!
# Dirichlet-Multinomial Marginal Convex Order

This file establishes the convex order property for marginals of the Dirichlet-Multinomial
distribution. The k-th marginal count `X_k` of a `DM(κπ, n)` distribution has a Beta-Binomial
mixture representation: `X_k | p_k ~ Bin(n, p_k)` where `p_k ~ Beta(κπ_k, κ(1 − π_k))`.

Combining the fact that lower κ produces a more dispersed Beta prior (`betaWithMean_convexOrder`)
with convexity of `E_{Bin(n,p)}[φ(X)]` in `p` for convex `φ` (`binomialExpect_convexOn`), the
iterated expectation `E[φ(X_k)] = E_Beta[E_Bin[φ]]` is larger under the lower-concentration
distribution.

## Main definitions

* `DirichletMultinomial.marginalExpect` — the expected value `E[f(X_k)]` for the k-th marginal of a
  DM distribution.

## Main statements

* `DirichletMultinomial.marginalExpect_eq_betaBinomial` — the Beta-Binomial mixture identity:
  `E_{DM(α,n)}[f(X_k)] = E_{Beta(α_k, α₀ − α_k)}[E_{Bin(n,p)}[f]]`.
* `dmMarginal_convexOrder` — for fixed type frequencies `π` and concentrations `κ₁ < κ₂`,
  `E_{DM(κ₂π,n)}[φ(X_k)] ≤ E_{DM(κ₁π,n)}[φ(X_k)]` for every convex `φ`.

## References

* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

dirichlet-multinomial, beta-binomial, convex order, marginal, concentration
-/

@[expose] public noncomputable section

open Finset BigOperators

namespace Econlib.Probability

/-- The expected value `E[f(X_k)]` of a function `f : ℕ → ℝ` applied to the k-th marginal count of
a Dirichlet-Multinomial distribution `DM(d, n)`, computed as a weighted sum over all multinomial
outcomes. -/
noncomputable def DirichletMultinomial.marginalExpect {m : ℕ} (d : DirichletDist m) (hm : 0 < m)
    (n : ℕ) (k : Fin m) (f : ℕ → ℝ) : ℝ :=
  ∑ x : MultinomialOutcome m n,
    (CountDist.dirichletMultinomial d hm n).pmf x * f (x.1 k)

/-- **Beta-Binomial mixture identity:** The DM marginal expectation equals an iterated expectation
over the Beta marginal prior and binomial likelihood:
`E_{DM(α,n)}[f(X_k)] = E_{Beta(α_k, α₀ − α_k)}[E_{Bin(n,p)}[f]]`. -/
lemma DirichletMultinomial.marginalExpect_eq_betaBinomial {m : ℕ} (d : DirichletDist m) (hm : 0 < m)
    (n : ℕ) (k : Fin m) (f : ℕ → ℝ)
    (hα_sum : 0 < d.alphaSum) (hπ_lt : d.alpha k / d.alphaSum < 1) :
    DirichletMultinomial.marginalExpect d hm n k f =
      (betaWithMean (d.mean hm k) d.alphaSum
        (div_pos (d.alpha_pos k) hα_sum)
        (by rw [DirichletDist.mean]; exact hπ_lt)
        hα_sum).expect
        (fun p => binomialExpect n f p) := by
  -- Both sides equal ∑ j : Fin (n+1), f j * betaBinomialPMF (α k) (α₀ - α k) n j.
  set α := d.alpha
  set α₀ := d.alphaSum
  set β := α₀ - α k with hβ_def
  -- hπ_lt implies m ≥ 2: when m = 1, α k / α₀ = 1, contradicting hπ_lt.
  have hm2 : 2 ≤ m := by
    by_contra h; push Not at h
    have hm1 : m = 1 := by omega
    subst hm1
    have : k = ⟨0, hm⟩ := Fin.eq_zero k
    subst this
    have : α₀ = α ⟨0, hm⟩ := by
      change d.alphaSum = d.alpha ⟨0, hm⟩
      simp [DirichletDist.alphaSum]
    rw [this, div_self (ne_of_gt (d.alpha_pos ⟨0, hm⟩))] at hπ_lt
    linarith
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  -- Fiber decomposition: ∑_x DM(x)*f(x_k) = ∑_j f(j) * BB(j)
  -- via dirichletMultinomial_marginal_eq_betaBinomialPMF.
  have hLHS : DirichletMultinomial.marginalExpect d hm n k f =
      ∑ j : Fin (n + 1), f j * betaBinomialPMF (α k) β n j := by
    unfold DirichletMultinomial.marginalExpect
    set g : MultinomialOutcome (m' + 1) n → Fin (n + 1) := fun x =>
      ⟨x.1 k, by
        have := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega⟩
    rw [← Finset.sum_fiberwise Finset.univ g]
    congr 1; ext j
    rw [show ∑ x ∈ Finset.univ.filter (fun x => g x = j),
          (CountDist.dirichletMultinomial d hm n).pmf x * f (x.1 k) =
        f j * ∑ x ∈ Finset.univ.filter (fun x => g x = j),
          (CountDist.dirichletMultinomial d hm n).pmf x from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx
      have hxk : x.1 k = ↑j := congrArg Fin.val (Finset.mem_filter.mp hx).2
      rw [hxk, mul_comm]]
    congr 1
    rw [Finset.sum_filter]
    simp only [g, CountDist.dirichletMultinomial_apply]
    have : ∀ x : MultinomialOutcome (m' + 1) n,
        (if (⟨x.1 k, by
            have :=
              Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ k)
            omega⟩ : Fin (n + 1)) = j then
          (↑(Nat.multinomial Finset.univ x.1) *
            multivariateBeta (m' + 1) (fun i => ↑(x.1 i) + d.alpha i)) /
            multivariateBeta (m' + 1) d.alpha
        else 0) =
        (if x.1 k = ↑j then dirichletMultinomialPMF α d.alpha_pos x else 0) := by
      intro x; congr 1; exact propext Fin.ext_iff
    simp_rw [this]
    exact dirichletMultinomial_marginal_eq_betaBinomialPMF α d.alpha_pos (by omega) n k j
  -- Beta-Binomial integral identity: ∑_j f(j) * BB(j) = E_Beta[E_Bin[f]].
  have hRHS : (betaWithMean (d.mean hm k) d.alphaSum
      (div_pos (d.alpha_pos k) hα_sum)
      (by rw [DirichletDist.mean]; exact hπ_lt)
      hα_sum).expect (fun p => binomialExpect n f p) =
    ∑ j : Fin (n + 1), f j * betaBinomialPMF (α k) β n j := by
    -- The density of betaWithMean (d.mean hm k) α₀ equals betaPDFReal (α k) β,
    -- since α₀ * (α k / α₀) = α k and α₀ * (1 - α k / α₀) = β.
    set bm := betaWithMean (d.mean hm k) d.alphaSum
      (div_pos (d.alpha_pos k) hα_sum) (by rw [DirichletDist.mean]; exact hπ_lt) hα_sum
    have hα_k_pos : 0 < α k := d.alpha_pos k
    have hβ_pos : 0 < β := by
      rw [hβ_def]
      have hαk_lt : α k < α₀ := (div_lt_one hα_sum).mp hπ_lt
      linarith
    have hmean_eq : d.alphaSum * d.mean hm k = α k := by
      simp only [DirichletDist.mean]
      exact mul_div_cancel₀ _ (ne_of_gt hα_sum)
    have hdens : bm.density = ProbabilityTheory.betaPDFReal (α k) β := by
      ext x
      change ProbabilityTheory.betaPDFReal (d.alphaSum * (d.mean hm k))
        (d.alphaSum * (1 - d.mean hm k)) x = ProbabilityTheory.betaPDFReal (α k) β x
      rw [hmean_eq]; congr 1; linarith [hmean_eq]
    simp only [ContDist.expect, hdens, binomialExpect]
    -- betaPDFReal (α k) β * (p^j * (1-p)^k') is integrable via betaPDFReal_mul_pow_pow.
    have hint_pow : ∀ (j' k' : ℕ), MeasureTheory.Integrable
        (fun p => ProbabilityTheory.betaPDFReal (α k) β p * (p ^ j' * (1 - p) ^ k')) := by
      intro j' k'
      rw [show (fun p => ProbabilityTheory.betaPDFReal (α k) β p * (p ^ j' * (1 - p) ^ k')) =
          fun p => (ProbabilityTheory.beta (↑j' + α k) (↑k' + β) /
            ProbabilityTheory.beta (α k) β) *
            ProbabilityTheory.betaPDFReal (↑j' + α k) (↑k' + β) p
        from funext (betaPDFReal_mul_pow_pow (α k) β hα_k_pos hβ_pos j' k')]
      exact (MeasureTheory.integrable_of_lintegral_ofReal_eq_one
        (betaPDFReal_nonneg (by positivity) (by positivity))
        (ProbabilityTheory.stronglyMeasurable_betaPDFReal _ _)
        (by rw [ofReal_betaPDFReal_eq_betaPDF,
            ProbabilityTheory.lintegral_betaPDF_eq_one
              (by positivity) (by positivity)])).const_mul _
    simp_rw [Finset.mul_sum]
    rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => by
      have heq : (fun x => ProbabilityTheory.betaPDFReal (α k) β x *
          (↑(n.choose ↑j) * x ^ (↑j : ℕ) * (1 - x) ^ (n - ↑j) * f ↑j)) =
        fun x => (↑(n.choose ↑j) * f ↑j) *
          (ProbabilityTheory.betaPDFReal (α k) β x * (x ^ (↑j : ℕ) * (1 - x) ^ (n - ↑j))) := by
        ext x; ring
      rw [heq]; exact (hint_pow ↑j (n - ↑j)).const_mul _)]
    congr 1; ext j
    have : (fun p => ProbabilityTheory.betaPDFReal (α k) β p *
        (↑(n.choose (j : ℕ)) * p ^ (j : ℕ) * (1 - p) ^ (n - (j : ℕ)) * f (j : ℕ))) =
      fun p => f (j : ℕ) * (ProbabilityTheory.betaPDFReal (α k) β p *
        (↑(n.choose (j : ℕ)) * p ^ (j : ℕ) * (1 - p) ^ (n - (j : ℕ)))) := by ext p; ring
    rw [this, MeasureTheory.integral_const_mul]
    congr 1
    exact beta_integral_binomial (α k) β hα_k_pos hβ_pos n j
  rw [hLHS, hRHS]

/-- **DM marginal convex order:** For two Dirichlet-Multinomial distributions with the same mean
type frequencies `π` but different concentrations `κ₁ < κ₂`, the lower-concentration distribution
dominates in convex order on every marginal: For all convex `φ`,
`E_{DM(κ₂π, n)}[φ(X_k)] ≤ E_{DM(κ₁π, n)}[φ(X_k)]`. -/
theorem dmMarginal_convexOrder {m : ℕ} (π : Fin m → ℝ) (κ₁ κ₂ : ℝ) (n : ℕ)
    (hm : 0 < m) (hπ : ∀ i, 0 < π i) (hπ_sum : ∑ i, π i = 1)
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂)
    (k : Fin m) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    DirichletMultinomial.marginalExpect
        ⟨fun i => κ₂ * π i, fun i => mul_pos hk2 (hπ i)⟩ hm n k (φ ∘ Nat.cast) ≤
    DirichletMultinomial.marginalExpect
        ⟨fun i => κ₁ * π i, fun i => mul_pos hk1 (hπ i)⟩ hm n k (φ ∘ Nat.cast) := by
  set d₂ : DirichletDist m := ⟨fun i => κ₂ * π i, fun i => mul_pos hk2 (hπ i)⟩ with hd₂_def
  set d₁ : DirichletDist m := ⟨fun i => κ₁ * π i, fun i => mul_pos hk1 (hπ i)⟩ with hd₁_def
  have hα₂_sum : d₂.alphaSum = κ₂ := by
    simp only [DirichletDist.alphaSum, hd₂_def, ← Finset.mul_sum]
    rw [hπ_sum, mul_one]
  have hα₁_sum : d₁.alphaSum = κ₁ := by
    simp only [DirichletDist.alphaSum, hd₁_def, ← Finset.mul_sum]
    rw [hπ_sum, mul_one]
  have hα₂_pos : 0 < d₂.alphaSum := hα₂_sum ▸ hk2
  have hα₁_pos : 0 < d₁.alphaSum := hα₁_sum ▸ hk1
  -- When m = 1, X_k = n deterministically, so both expectations equal φ(n).
  -- When m ≥ 2, there exists j ≠ k with π j > 0, so π k < 1 and the Beta-Binomial
  -- mixture identity applies; the conclusion then follows from betaWithMean_convexOrder.
  by_cases hm1 : m = 1
  · subst hm1
    have hk0 : k = ⟨0, hm⟩ := Fin.eq_zero k
    have hx_val : ∀ x : MultinomialOutcome 1 n, x.1 0 = n := by
      intro x
      simpa using x.2
    simp only [DirichletMultinomial.marginalExpect, hk0]
    have : ∀ (d' : DirichletDist 1) (x : MultinomialOutcome 1 n),
        (CountDist.dirichletMultinomial d' hm n).pmf x * (φ ∘ Nat.cast) (x.1 ⟨0, hm⟩) =
        (CountDist.dirichletMultinomial d' hm n).pmf x * (φ ∘ Nat.cast) n := by
      intro d' x; congr 1; simp [hx_val x]
    simp_rw [this]
    simp_rw [← Finset.sum_mul]
    have hsum : ∀ d' : DirichletDist 1, ∑ x : MultinomialOutcome 1 n,
        (CountDist.dirichletMultinomial d' hm n).pmf x = 1 := fun d' => by
      have := (CountDist.dirichletMultinomial d' hm n).tsum_one
      rwa [tsum_fintype] at this
    rw [hsum d₂, hsum d₁]
  · have hm2 : 2 ≤ m := by omega
    have hπk_lt : π k < 1 := by
      haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
      obtain ⟨j, hj⟩ := exists_ne k
      have hsum := Finset.add_sum_erase Finset.univ π (Finset.mem_univ k)
      have hj_mem : j ∈ Finset.univ.erase k :=
        Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      have hj_le : π j ≤ ∑ i ∈ Finset.univ.erase k, π i :=
        Finset.single_le_sum (fun i _ => le_of_lt (hπ i)) hj_mem
      linarith [hπ j, hπ_sum]
    have hπ₂_lt : d₂.alpha k / d₂.alphaSum < 1 := by
      rw [hα₂_sum]
      change κ₂ * π k / κ₂ < 1
      rw [mul_div_cancel_left₀ (π k) (ne_of_gt hk2)]
      exact hπk_lt
    have hπ₁_lt : d₁.alpha k / d₁.alphaSum < 1 := by
      rw [hα₁_sum]
      change κ₁ * π k / κ₁ < 1
      rw [mul_div_cancel_left₀ (π k) (ne_of_gt hk1)]
      exact hπk_lt
    have hmean₂ : d₂.mean hm k = π k := by
      simp only [DirichletDist.mean]
      rw [hα₂_sum]; exact mul_div_cancel_left₀ (π k) (ne_of_gt hk2)
    have hmean₁ : d₁.mean hm k = π k := by
      simp only [DirichletDist.mean]
      rw [hα₁_sum]; exact mul_div_cancel_left₀ (π k) (ne_of_gt hk1)
    rw [DirichletMultinomial.marginalExpect_eq_betaBinomial d₂ hm n k (φ ∘ Nat.cast) hα₂_pos hπ₂_lt,
        DirichletMultinomial.marginalExpect_eq_betaBinomial d₁ hm n k (φ ∘ Nat.cast) hα₁_pos hπ₁_lt]
    have hπk_pos : 0 < π k := hπ k
    have hconv : ConvexOn ℝ (Set.Icc 0 1) (fun p => binomialExpect n (φ ∘ Nat.cast) p) :=
      binomialExpect_convexOn n (φ ∘ Nat.cast) (ConvexOn.nondecreasing_differences φ hφ)
    simp only [hmean₂, hmean₁, hα₂_sum, hα₁_sum] at *
    -- ψ = E_Bin[φ] is a polynomial in p, so it is C^∞ and plugs
    -- directly into betaWithMean_convexOrder.
    set ψ := fun p => binomialExpect n (φ ∘ Nat.cast) p
    have hψ_cont : Continuous ψ := (binomialExpect_contDiff n (φ ∘ Nat.cast)).continuous
    exact betaWithMean_convexOrder hπk_pos hπk_lt hk1 hk2 hlt ψ hconv hψ_cont.continuousOn

end Econlib.Probability

end -- noncomputable section
