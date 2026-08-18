/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.SimplexIntegral
public import Econlib.Probability.Distributions.Beta.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Dirichlet distribution

This file develops the Dirichlet density on the `(k-1)`-dimensional simplex, including the
multivariate Beta normalizing constant, the bundled `DirichletDist` type, and basic results on
positivity, normalization, moments (mean, variance, covariance), marginals, and special cases
(uniform, Jeffreys prior).

## Main definitions

* `multivariateBeta`: The multivariate Beta function `B(α) = ∏ Γ(αᵢ) / Γ(∑ αᵢ)`, the normalizing
  constant for Dirichlet densities.
* `OnSimplex`: Membership in the open probability simplex (all coordinates positive, summing to 1).
* `dirichletPDFReal`: The real-valued Dirichlet density on the simplex.
* `DirichletDist`: Bundled Dirichlet distribution with concentration parameters `α : Fin k → ℝ`.
* `DirichletDist.densityReduced`: The density in reduced `(k-1)` coordinates for integration.
* `DirichletDist.marginalBeta`: The `i`-th marginal `Beta(αᵢ, α₀ - αᵢ)`.
* `DirichletDist.uniform`, `DirichletDist.jeffreys`: The symmetric Dirichlet (`αᵢ = 1`) and the
  Jeffreys prior (`αᵢ = 1/2`).

## Main statements

* `DirichletDist.densityReduced_integral_one`: The Dirichlet density integrates to 1.
* `DirichletDist.mean_eq`: Integral characterization of the component mean `αᵢ / α₀`.
* `DirichletDist.variance_eq`: Integral characterization of the component variance.
* `DirichletDist.covariance_eq`: Integral characterization of the component covariance.
* `DirichletDist.marginalBeta_mean`, `DirichletDist.marginalBeta_variance`: The marginal Beta
  moments match the Dirichlet component moments.
* `dirichletPDFReal_two_eq_betaPDFReal`: When `k = 2`, the Dirichlet PDF reduces to the Beta PDF.

## Tags

probability, continuous distributions, dirichlet, simplex, beta function
-/

@[expose] public section

open ProbabilityTheory

namespace Econlib.Probability

/-! ## Multivariate Beta function B(α) = ∏ Γ(αᵢ) / Γ(∑ αᵢ) -/

/-- The multivariate Beta function `B(α) = ∏ Γ(αᵢ) / Γ(∑ αᵢ)`, the normalizing constant of the
Dirichlet distribution. -/
noncomputable def multivariateBeta (k : ℕ) (α : Fin k → ℝ) : ℝ :=
  (∏ i, Real.Gamma (α i)) / Real.Gamma (∑ i, α i)

/-- The multivariate Beta function is positive when all concentration parameters are positive. -/
lemma multivariateBeta_pos {k : ℕ} (hk : 0 < k) {α : Fin k → ℝ}
    (hα : ∀ i, 0 < α i) : 0 < multivariateBeta k α := by
  unfold multivariateBeta
  apply div_pos
  · exact Finset.prod_pos (fun i _ => Real.Gamma_pos_of_pos (hα i))
  · apply Real.Gamma_pos_of_pos
    apply Finset.sum_pos (fun i _ => hα i)
    exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-- The multivariate Beta function is nonzero when all concentration parameters are positive. -/
lemma multivariateBeta_ne_zero {k : ℕ} (hk : 0 < k) {α : Fin k → ℝ}
    (hα : ∀ i, 0 < α i) : multivariateBeta k α ≠ 0 :=
  ne_of_gt (multivariateBeta_pos hk hα)

/-- Incrementing a positive parameter vector at one coordinate keeps it positive. -/
lemma update_add_one_pos {k : ℕ} {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) (i : Fin k) :
    ∀ j, 0 < Function.update α i (α i + 1) j := by
  intro j
  by_cases h : j = i
  · rw [h, Function.update_self]; linarith [hα i]
  · rw [Function.update_of_ne h]; exact hα j

/-- When `k = 2`, the multivariate Beta function equals the classical Beta function. -/
lemma multivariateBeta_two (α : Fin 2 → ℝ) :
    multivariateBeta 2 α = ProbabilityTheory.beta (α 0) (α 1) := by
  simp only [multivariateBeta, ProbabilityTheory.beta, Fin.prod_univ_two, Fin.sum_univ_two]

/-! ## Dirichlet PDF -/

/-- A point lies in the open simplex: All coordinates positive, summing to 1. -/
def OnSimplex (k : ℕ) (x : Fin k → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∑ i, x i = 1

open Classical in
/-- The Dirichlet PDF: `(1 / B(α)) ∏ xᵢ^(αᵢ - 1)` on the open simplex, 0 elsewhere. -/
noncomputable def dirichletPDFReal (k : ℕ) (α : Fin k → ℝ) (x : Fin k → ℝ) : ℝ :=
  if OnSimplex k x then
    (1 / multivariateBeta k α) * ∏ i, (x i) ^ (α i - 1)
  else 0

/-- The Dirichlet PDF is nonneg when all concentration parameters are positive. -/
lemma dirichletPDFReal_nonneg {k : ℕ} (hk : 0 < k) {α : Fin k → ℝ}
    (hα : ∀ i, 0 < α i) (x : Fin k → ℝ) : 0 ≤ dirichletPDFReal k α x := by
  unfold dirichletPDFReal
  split_ifs with h
  · apply mul_nonneg
    · apply div_nonneg one_pos.le
      exact le_of_lt (multivariateBeta_pos hk hα)
    · exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (le_of_lt (h.1 i)) _)
  · exact le_refl 0

/-- The Dirichlet PDF is strictly positive at interior simplex points when all concentration
parameters are positive. -/
lemma dirichletPDFReal_pos {k : ℕ} (hk : 0 < k) {α : Fin k → ℝ}
    (hα : ∀ i, 0 < α i) {x : Fin k → ℝ} (hx : OnSimplex k x) :
    0 < dirichletPDFReal k α x := by
  unfold dirichletPDFReal
  rw [if_pos hx]
  apply mul_pos
  · exact div_pos one_pos (multivariateBeta_pos hk hα)
  · exact Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx.1 i) _)

/-! ## DirichletDist structure -/

/-- The Dirichlet distribution with `k` components and concentration parameters `α`. This is a
multivariate distribution on the `(k-1)`-simplex. -/
structure DirichletDist (k : ℕ) where
/-- Concentration parameters, all positive. -/
  alpha : Fin k → ℝ
/-- All concentration parameters are positive. -/
  alpha_pos : ∀ i, 0 < alpha i

namespace DirichletDist

variable {k : ℕ} (d : DirichletDist k)

/-- The density function of the Dirichlet distribution. -/
noncomputable def density : (Fin k → ℝ) → ℝ :=
  dirichletPDFReal k d.alpha

/-- The sum of all concentration parameters, conventionally α₀. -/
noncomputable def alphaSum : ℝ := ∑ i, d.alpha i

/-- The concentration parameter sum `α₀ = ∑ αᵢ` is positive when `k > 0`. -/
lemma alphaSum_pos (hk : 0 < k) : 0 < d.alphaSum :=
  Finset.sum_pos (fun i _ => d.alpha_pos i) ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-- The concentration parameter sum `α₀` is nonzero when `k > 0`. -/
lemma alphaSum_ne_zero (hk : 0 < k) : d.alphaSum ≠ 0 := ne_of_gt (d.alphaSum_pos hk)

/-- The Dirichlet density is nonneg everywhere when `k > 0`. -/
lemma density_nonneg (hk : 0 < k) (x : Fin k → ℝ) : 0 ≤ d.density x :=
  dirichletPDFReal_nonneg hk d.alpha_pos x

/-- The Dirichlet density is strictly positive at interior simplex points when `k > 0`. -/
lemma density_pos (hk : 0 < k) {x : Fin k → ℝ} (hx : OnSimplex k x) :
    0 < d.density x :=
  dirichletPDFReal_pos hk d.alpha_pos hx

/-! ## Normalization -/

/-- The Dirichlet PDF in reduced `(k-1)` coordinates, where the last coordinate is `1 - ∑ᵢ yᵢ`.
This is the form suitable for integration over `ℝ^(k-1)`. -/
-- `_hk` is not used in the definition body but fixes the intended domain constraint `0 < k` for
-- callers of the reduced-coordinate API, matching the signature of `densityReduced_integral_one`.
noncomputable def densityReduced (_hk : 0 < k) (y : Fin (k - 1) → ℝ) : ℝ :=
  let x : Fin k → ℝ := fun i =>
    if h : i.val < k - 1 then y ⟨i.val, by omega⟩
    else 1 - ∑ j : Fin (k - 1), y j
  dirichletPDFReal k d.alpha x

/-- The reconstruction map `i ↦ if i < k-1 then y i else 1 - ∑ y` sums to 1. -/
private lemma reconstructed_sum_eq_one {k : ℕ} (hk : 0 < k) (y : Fin (k - 1) → ℝ) :
    ∑ i : Fin k, (fun i : Fin k =>
      if h : i.val < k - 1 then y ⟨i.val, by omega⟩
      else 1 - ∑ j : Fin (k - 1), y j) i = 1 := by
  simp only
  suffices h : (∑ i : Fin k, if h : i.val < k - 1 then y ⟨i.val, h⟩
      else 1 - ∑ j, y j) =
    ∑ i : Fin (k - 1), y i + (1 - ∑ j, y j) by linarith
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hi : (Fin.castSucc i).val < n + 1 - 1 := by simp [Fin.castSucc]
    simp only [hi, dite_true]
    congr 1
  · simp [Fin.last]

/-- The reconstruction map lies in `OnSimplex k` iff all `y i > 0` and `∑ y < 1`. -/
private lemma onSimplex_reconstructed_iff {k : ℕ} (hk : 1 < k) (y : Fin (k - 1) → ℝ) :
    OnSimplex k (fun i : Fin k =>
      if h : i.val < k - 1 then y ⟨i.val, by omega⟩
      else 1 - ∑ j : Fin (k - 1), y j) ↔
    (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 := by
  unfold OnSimplex
  constructor
  · rintro ⟨hpos, hsum⟩
    constructor
    · intro i
      have := hpos ⟨i.val, by omega⟩
      simp only [show i.val < k - 1 from i.isLt, ↓reduceDIte, Fin.eta] at this
      exact this
    · have hlast := hpos ⟨k - 1, by omega⟩
      simp only [lt_self_iff_false, ↓reduceDIte, sub_pos] at hlast
      linarith
  · rintro ⟨hpos, hsum_lt⟩
    constructor
    · intro i
      by_cases hi : i.val < k - 1
      · simp only [hi, ↓reduceDIte]; exact hpos ⟨i.val, hi⟩
      · simp only [hi, ↓reduceDIte, sub_pos]; linarith
    · exact reconstructed_sum_eq_one (by omega) y

/-- The product `∏ i, x i ^ (α i - 1)` for the reconstructed `x` factors into the simplex integrand
form `(∏ i < k-1, y i ^ (α i - 1)) * (1 - ∑ y) ^ (α (k-1) - 1)`. -/
private lemma prod_reconstructed_eq {k : ℕ} (hk : 1 < k) (α : Fin k → ℝ)
    (y : Fin (k - 1) → ℝ) (hy : (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1) :
    ∏ i : Fin k, ((fun i : Fin k =>
      if h : i.val < k - 1 then y ⟨i.val, by omega⟩
      else 1 - ∑ j : Fin (k - 1), y j) i) ^ (α i - 1) =
    (∏ i : Fin (k - 1), (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
      (1 - ∑ i, y i) ^ (α ⟨k - 1, by omega⟩ - 1) := by
  simp only
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hi : (Fin.castSucc i).val < n + 1 - 1 := by simp [Fin.castSucc]
    simp only [hi, dite_true]
    congr 1
  · simp [Fin.last]

/-- The Dirichlet density integrates to 1 over the simplex (in reduced coordinates), establishing
that `dirichletPDFReal` defines a probability density when `k ≥ 2`. -/
theorem densityReduced_integral_one (hk : 1 < k) :
    ∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y = 1 := by
  -- densityReduced y = (1/B(α)) * (simplex integrand) pointwise, so the integral equals
  -- (1/B(α)) * simplexIntegral k α = (1/B(α)) * B(α) = 1.
  have hpw : ∀ y : Fin (k - 1) → ℝ,
      d.densityReduced (by omega) y =
      1 / multivariateBeta k d.alpha *
        (if (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 then
          (∏ i : Fin (k - 1), (y i) ^ (d.alpha ⟨i.val, by omega⟩ - 1)) *
            (1 - ∑ i, y i) ^ (d.alpha ⟨k - 1, by omega⟩ - 1)
        else 0) := by
    intro y
    simp only [densityReduced, dirichletPDFReal]
    set x : Fin k → ℝ := fun i =>
      if h : i.val < k - 1 then y ⟨i.val, by omega⟩
      else 1 - ∑ j : Fin (k - 1), y j with hx_def
    have hiff : OnSimplex k x ↔ (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 :=
      onSimplex_reconstructed_iff hk y
    by_cases hy : (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1
    · rw [if_pos (hiff.mpr hy), if_pos hy]
      congr 1
      exact prod_reconstructed_eq hk d.alpha y hy
    · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy, mul_zero]
  simp_rw [hpw]
  rw [MeasureTheory.integral_const_mul]
  have hk2 : 2 ≤ k := hk
  have hint : ∫ y : Fin (k - 1) → ℝ,
      (if (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 then
        (∏ i : Fin (k - 1), (y i) ^ (d.alpha ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i, y i) ^ (d.alpha ⟨k - 1, by omega⟩ - 1)
      else 0) = MeasureTheory.simplexIntegral k d.alpha := by
    unfold MeasureTheory.simplexIntegral
    rw [dif_neg (by omega), dif_neg (by omega)]
  rw [hint, MeasureTheory.simplexIntegral_eq_multivariateBeta hk2 d.alpha_pos]
  rw [show (∏ i, Real.Gamma (d.alpha i)) / Real.Gamma (∑ i, d.alpha i) =
      multivariateBeta k d.alpha from rfl,
    one_div, inv_mul_cancel₀ (multivariateBeta_ne_zero (by omega) d.alpha_pos)]

/-! ## Shifted parameters and moment infrastructure -/

/-- Shift the `i`-th concentration parameter by `r`: `α' j = α j + r` if `j = i`, else `α j`. -/
noncomputable def shiftAlpha (i : Fin k) (r : ℝ) : Fin k → ℝ :=
  fun j => if j = i then d.alpha j + r else d.alpha j

/-- Shifting a positive parameter vector at one coordinate by a positive amount keeps all
parameters positive. -/
lemma shiftAlpha_pos (i : Fin k) {r : ℝ} (hr : 0 < r) : ∀ j, 0 < d.shiftAlpha i r j := by
  intro j; unfold shiftAlpha
  split_ifs <;> linarith [d.alpha_pos j]

/-- `shiftAlpha i r` is the single-coordinate `Function.update` of `α` at `i`. -/
lemma shiftAlpha_eq_update (i : Fin k) (r : ℝ) :
    d.shiftAlpha i r = Function.update d.alpha i (d.alpha i + r) := by
  ext j; simp only [shiftAlpha, Function.update]
  split_ifs with h <;> [subst h; rfl]; rfl

/-- The shifted parameter sum: `∑ (shiftAlpha i r) = α₀ + r`. -/
-- `_hk` is unused in the body; it records that `Fin k` is nonempty (implicit in `i : Fin k`).
lemma shiftAlpha_sum (_hk : 0 < k) (i : Fin k) (r : ℝ) :
    ∑ j, d.shiftAlpha i r j = d.alphaSum + r := by
  unfold shiftAlpha alphaSum
  have : (fun j => if j = i then d.alpha j + r else d.alpha j) =
      (fun j => d.alpha j + if j = i then r else 0) := by
    ext j; split_ifs <;> ring
  rw [this, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- Shifting the `i`-th concentration parameter by 1 scales the normalizing constant by `αᵢ / α₀`:
`B(shiftAlpha i 1) / B(α) = αᵢ / α₀`. -/
lemma multivariateBeta_shift_ratio (hk : 0 < k) (i : Fin k) :
    multivariateBeta k (d.shiftAlpha i 1) / multivariateBeta k d.alpha =
    d.alpha i / d.alphaSum := by
  unfold multivariateBeta shiftAlpha alphaSum
  have hα_ne : d.alpha i ≠ 0 := ne_of_gt (d.alpha_pos i)
  have hα₀_ne : (∑ j, d.alpha j) ≠ 0 := ne_of_gt (d.alphaSum_pos hk)
  -- Numerator: factor out αᵢ using Γ(αᵢ + 1) = αᵢ · Γ(αᵢ) at coordinate i.
  have h_num : ∏ j, Real.Gamma (if j = i then d.alpha j + 1 else d.alpha j) =
      d.alpha i * ∏ j, Real.Gamma (d.alpha j) := by
    have h_factor : ∀ j, Real.Gamma (if j = i then d.alpha j + 1 else d.alpha j) =
        (if j = i then d.alpha j else 1) * Real.Gamma (d.alpha j) := by
      intro j; split_ifs with h
      · subst h; rw [Real.Gamma_add_one hα_ne]
      · ring
    simp_rw [h_factor, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq']
    simp
  -- Denominator: Γ(α₀ + 1) = α₀ · Γ(α₀).
  have h_den : Real.Gamma (∑ j, (if j = i then d.alpha j + 1 else d.alpha j)) =
      (∑ j, d.alpha j) * Real.Gamma (∑ j, d.alpha j) := by
    have : ∑ j, (if j = i then d.alpha j + 1 else d.alpha j) = (∑ j, d.alpha j) + 1 := by
      have := d.shiftAlpha_sum hk i 1
      unfold shiftAlpha alphaSum at this; linarith
    rw [this, Real.Gamma_add_one hα₀_ne]
  rw [h_num, h_den]
  have hΓ_ne : Real.Gamma (∑ j, d.alpha j) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (d.alphaSum_pos hk))
  have h_prod_ne : (∏ j, Real.Gamma (d.alpha j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => ne_of_gt (Real.Gamma_pos_of_pos (d.alpha_pos j)))
  field_simp

/-- Multiplying the Dirichlet PDF at `x` by the `i`-th coordinate equals the ratio `B(α') / B(α)`
times the PDF with parameters `α' = Function.update α i (α i + 1)`:
`dirichletPDFReal k α x * x i = (B(α') / B(α)) * dirichletPDFReal k α' x`. -/
lemma dirichletPDFReal_mul_coord {α : Fin k → ℝ} (hα : ∀ j, 0 < α j) (hk : 0 < k)
    (i : Fin k) (x : Fin k → ℝ) :
    dirichletPDFReal k α x * x i =
    (multivariateBeta k (Function.update α i (α i + 1)) /
      multivariateBeta k α) *
    dirichletPDFReal k (Function.update α i (α i + 1)) x := by
  unfold dirichletPDFReal
  set α' := Function.update α i (α i + 1)
  by_cases hx : OnSimplex k x
  · simp only [if_pos hx]
    have hBα : multivariateBeta k α ≠ 0 := multivariateBeta_ne_zero hk hα
    have hα' : ∀ j, 0 < α' j := update_add_one_pos hα i
    have hBα' : multivariateBeta k α' ≠ 0 := multivariateBeta_ne_zero hk hα'
    -- Key product identity: xᵢ^(α'ᵢ - 1) = xᵢ^αᵢ = xᵢ^(αᵢ-1) · xᵢ, so ∏ x^(α'-1) = xᵢ · ∏ x^(α-1).
    have hprod : ∏ j : Fin k, (x j) ^ (α' j - 1) =
        x i * ∏ j : Fin k, (x j) ^ (α j - 1) := by
      have hxi_ne : x i ≠ 0 := ne_of_gt (hx.1 i)
      have hmem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
      rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
      have hα'i : α' i = α i + 1 := Function.update_self i (α i + 1) α
      have hprod_eq : ∏ j ∈ Finset.univ.erase i, (x j) ^ (α' j - 1) =
          ∏ j ∈ Finset.univ.erase i, (x j) ^ (α j - 1) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [show α' j = α j from Function.update_of_ne hji _ _]
      rw [hprod_eq, hα'i, show α i + 1 - 1 = α i from by ring]
      conv_lhs => rw [show α i = (α i - 1) + 1 from by ring, Real.rpow_add_one hxi_ne]
      ring
    rw [hprod]
    field_simp
  · simp only [if_neg hx, zero_mul, mul_zero]

/-! ## Moments -/

/-- The mean of the `i`-th component: `E[Xᵢ] = αᵢ / α₀`. -/
-- `_hk` is not used in the definition body but ensures `0 < k` is explicit at call sites,
-- parallel to `variance` and `covariance` which need it for `alphaSum_pos`.
noncomputable def mean (_hk : 0 < k) (i : Fin k) : ℝ := d.alpha i / d.alphaSum

/-- The means sum to 1. -/
lemma mean_sum_one (hk : 0 < k) : ∑ i, d.mean hk i = 1 := by
  simp only [mean, ← Finset.sum_div]
  exact div_self (d.alphaSum_ne_zero hk)

/-- The variance of the `i`-th component: `Var[Xᵢ] = αᵢ(α₀ - αᵢ) / (α₀²(α₀ + 1))`. -/
-- `_hk` is not used in the definition body but is required at call sites to discharge
-- `alphaSum_pos` when proving results about this quantity.
noncomputable def variance (_hk : 0 < k) (i : Fin k) : ℝ :=
  d.alpha i * (d.alphaSum - d.alpha i) / (d.alphaSum ^ 2 * (d.alphaSum + 1))

/-- The covariance of components `i` and `j`: `Cov[Xᵢ, Xⱼ] = -αᵢαⱼ / (α₀²(α₀ + 1))`. -/
-- `_hk` is not used in the definition body but is required at call sites to discharge
-- `alphaSum_pos` when proving results about this quantity.
noncomputable def covariance (_hk : 0 < k) (i j : Fin k)
    -- `_hij` is unused by the formula but enforces the off-diagonal restriction `i ≠ j`; the
    -- diagonal case is `variance`.
    (_hij : i ≠ j) : ℝ :=
  -(d.alpha i * d.alpha j) / (d.alphaSum ^ 2 * (d.alphaSum + 1))

/-- The covariance between two distinct components is strictly negative: `Cov[Xᵢ, Xⱼ] < 0`. -/
lemma covariance_neg (hk : 0 < k) (i j : Fin k) (hij : i ≠ j) :
    d.covariance hk i j hij < 0 := by
  unfold covariance
  have hα₀ := d.alphaSum_pos hk
  apply div_neg_of_neg_of_pos
  · linarith [mul_pos (d.alpha_pos i) (d.alpha_pos j)]
  · exact mul_pos (sq_pos_of_pos hα₀) (by linarith)

/-- The integral of `densityReduced * x i` over reduced coordinates equals the `i`-th mean
`d.alpha i / d.alphaSum`. -/
theorem mean_eq (hk : 1 < k) (i : Fin k) :
    ∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
      (if h : i.val < k - 1 then y ⟨i.val, by omega⟩
       else 1 - ∑ j : Fin (k - 1), y j) = d.mean (by omega) i := by
  have hk0 : 0 < k := by omega
  set α' := Function.update d.alpha i (d.alpha i + 1) with hα'_def
  have hα'_pos : ∀ j, 0 < α' j := update_add_one_pos d.alpha_pos i
  let d' : DirichletDist k := ⟨α', hα'_pos⟩
  have hshift_eq : d.shiftAlpha i 1 = α' := d.shiftAlpha_eq_update i 1
  have hpw : ∀ y : Fin (k - 1) → ℝ,
      d.densityReduced hk0 y *
        (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ j, y j) =
      (multivariateBeta k α' / multivariateBeta k d.alpha) *
        d'.densityReduced hk0 y := by
    intro y
    simp only [densityReduced]
    set x : Fin k → ℝ := fun j =>
      if h : j.val < k - 1 then y ⟨j.val, by omega⟩
      else 1 - ∑ l : Fin (k - 1), y l
    have hxi : (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ j, y j) = x i := by
      simp only [x]
    rw [hxi]
    exact dirichletPDFReal_mul_coord d.alpha_pos hk0 i x
  simp_rw [hpw]
  rw [MeasureTheory.integral_const_mul, d'.densityReduced_integral_one hk, mul_one]
  rw [show multivariateBeta k α' = multivariateBeta k (d.shiftAlpha i 1) from by rw [hshift_eq]]
  exact d.multivariateBeta_shift_ratio hk0 i

/-- The integral of `densityReduced * xᵢ²` minus `(E[Xᵢ])²` equals the `i`-th variance
`αᵢ(α₀ - αᵢ) / (α₀²(α₀ + 1))`. -/
theorem variance_eq (hk : 1 < k) (i : Fin k) :
    (∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
      (if h : i.val < k - 1 then y ⟨i.val, by omega⟩
       else 1 - ∑ j : Fin (k - 1), y j) ^ 2) -
    (d.mean (by omega) i) ^ 2 = d.variance (by omega) i := by
  have hk0 : 0 < k := by omega
  -- Two successive parameter shifts: α' = αᵢ + 1, α'' = αᵢ + 2.
  set α' := Function.update d.alpha i (d.alpha i + 1) with hα'_def
  have hα'_pos : ∀ j, 0 < α' j := update_add_one_pos d.alpha_pos i
  let d' : DirichletDist k := ⟨α', hα'_pos⟩
  set α'' := Function.update α' i (α' i + 1) with hα''_def
  have hα'_i : α' i = d.alpha i + 1 := Function.update_self i (d.alpha i + 1) d.alpha
  have hα''_pos : ∀ j, 0 < α'' j := update_add_one_pos hα'_pos i
  let d'' : DirichletDist k := ⟨α'', hα''_pos⟩
  have hshift1 : d.shiftAlpha i 1 = α' := d.shiftAlpha_eq_update i 1
  have hshift2 : d'.shiftAlpha i 1 = α'' := d'.shiftAlpha_eq_update i 1
  -- density * xᵢ² = ratio₁ · (ratio₂ · d''.densityReduced) by applying mul_coord twice.
  have hpw : ∀ y : Fin (k - 1) → ℝ,
      d.densityReduced hk0 y *
        (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ j, y j) ^ 2 =
      (multivariateBeta k α' / multivariateBeta k d.alpha) *
      ((multivariateBeta k α'' / multivariateBeta k α') *
        d''.densityReduced hk0 y) := by
    intro y
    simp only [densityReduced]
    set x : Fin k → ℝ := fun j =>
      if h : j.val < k - 1 then y ⟨j.val, by omega⟩
      else 1 - ∑ l : Fin (k - 1), y l
    have hxi : (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ j, y j) = x i := by
      simp only [x]
    rw [hxi, sq, ← mul_assoc]
    rw [dirichletPDFReal_mul_coord d.alpha_pos hk0 i x]
    rw [mul_assoc, dirichletPDFReal_mul_coord hα'_pos hk0 i x, ← mul_assoc]
  simp_rw [hpw]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      d''.densityReduced_integral_one hk, mul_one]
  -- ratio₁ = αᵢ/α₀, ratio₂ = (αᵢ+1)/(α₀+1).
  have hratio1 : multivariateBeta k α' / multivariateBeta k d.alpha =
      d.alpha i / d.alphaSum := by
    rw [show multivariateBeta k α' = multivariateBeta k (d.shiftAlpha i 1) from by rw [hshift1]]
    exact d.multivariateBeta_shift_ratio hk0 i
  have hratio2 : multivariateBeta k α'' / multivariateBeta k α' =
      (d.alpha i + 1) / (d.alphaSum + 1) := by
    rw [show multivariateBeta k α'' = multivariateBeta k (d'.shiftAlpha i 1) from by rw [hshift2]]
    rw [show multivariateBeta k α' = multivariateBeta k d'.alpha from rfl]
    have h := d'.multivariateBeta_shift_ratio hk0 i
    simp only [d'] at h
    rw [h, hα'_i]
    congr 1
    change ∑ j, α' j = d.alphaSum + 1
    rw [← hshift1]; exact d.shiftAlpha_sum hk0 i 1
  rw [hratio1, hratio2]
  simp only [mean, variance]
  have hα₀_pos := d.alphaSum_pos hk0
  field_simp
  ring

/-- The integral of `densityReduced * (xᵢ * xⱼ)` minus `E[Xᵢ] * E[Xⱼ]` equals the covariance
`-αᵢαⱼ / (α₀²(α₀ + 1))`, for `i ≠ j`. -/
theorem covariance_eq (hk : 1 < k) (i j : Fin k) (hij : i ≠ j) :
    (∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
      ((if h : i.val < k - 1 then y ⟨i.val, by omega⟩
        else 1 - ∑ l : Fin (k - 1), y l) *
       (if h : j.val < k - 1 then y ⟨j.val, by omega⟩
        else 1 - ∑ l : Fin (k - 1), y l))) -
    d.mean (by omega) i * d.mean (by omega) j =
    d.covariance (by omega) i j hij := by
  have hk0 : 0 < k := by omega
  -- Shift j first, then i: αj' = (αⱼ + 1), αij'' = (αᵢ + 1, αⱼ + 1).
  set αj' := Function.update d.alpha j (d.alpha j + 1) with hαj'_def
  have hαj'_pos : ∀ l, 0 < αj' l := update_add_one_pos d.alpha_pos j
  let dj' : DirichletDist k := ⟨αj', hαj'_pos⟩
  have hαj'_i : αj' i = d.alpha i := by
    simp only [αj', Function.update_of_ne hij]
  set αij'' := Function.update αj' i (αj' i + 1) with hαij''_def
  have hαij''_pos : ∀ l, 0 < αij'' l := update_add_one_pos hαj'_pos i
  let dij'' : DirichletDist k := ⟨αij'', hαij''_pos⟩
  have hshiftj : d.shiftAlpha j 1 = αj' := d.shiftAlpha_eq_update j 1
  have hshifti : dj'.shiftAlpha i 1 = αij'' := dj'.shiftAlpha_eq_update i 1
  have hpw : ∀ y : Fin (k - 1) → ℝ,
      d.densityReduced hk0 y *
        ((if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ l, y l) *
         (if h : j.val < k - 1 then y ⟨j.val, h⟩ else 1 - ∑ l, y l)) =
      (multivariateBeta k αj' / multivariateBeta k d.alpha) *
      ((multivariateBeta k αij'' / multivariateBeta k αj') *
        dij''.densityReduced hk0 y) := by
    intro y
    simp only [densityReduced]
    set x : Fin k → ℝ := fun l =>
      if h : l.val < k - 1 then y ⟨l.val, by omega⟩
      else 1 - ∑ m : Fin (k - 1), y m
    have hxi : (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ l, y l) = x i := by
      simp only [x]
    have hxj : (if h : j.val < k - 1 then y ⟨j.val, h⟩ else 1 - ∑ l, y l) = x j := by
      simp only [x]
    rw [hxi, hxj, mul_comm (x i) (x j), ← mul_assoc]
    rw [dirichletPDFReal_mul_coord d.alpha_pos hk0 j x]
    rw [mul_assoc, dirichletPDFReal_mul_coord hαj'_pos hk0 i x, ← mul_assoc]
  simp_rw [hpw]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      dij''.densityReduced_integral_one hk, mul_one]
  have hratio_j : multivariateBeta k αj' / multivariateBeta k d.alpha =
      d.alpha j / d.alphaSum := by
    rw [show multivariateBeta k αj' = multivariateBeta k (d.shiftAlpha j 1) from by rw [hshiftj]]
    exact d.multivariateBeta_shift_ratio hk0 j
  have hratio_i : multivariateBeta k αij'' / multivariateBeta k αj' =
      d.alpha i / (d.alphaSum + 1) := by
    rw [show multivariateBeta k αij'' =
        multivariateBeta k (dj'.shiftAlpha i 1) from by rw [hshifti]]
    rw [show multivariateBeta k αj' = multivariateBeta k dj'.alpha from rfl]
    have h := dj'.multivariateBeta_shift_ratio hk0 i
    simp only [dj'] at h
    rw [h, hαj'_i]
    congr 1
    change ∑ l, αj' l = d.alphaSum + 1
    rw [← hshiftj]; exact d.shiftAlpha_sum hk0 j 1
  rw [hratio_j, hratio_i]
  simp only [mean, covariance]
  have hα₀_pos := d.alphaSum_pos hk0
  field_simp
  ring

/-! ## Marginals and Beta connection -/

private lemma alpha_lt_alphaSum (d : DirichletDist k) (hk : 1 < k) (i : Fin k) :
    d.alpha i < d.alphaSum := by
  have ⟨j, hji⟩ : ∃ j : Fin k, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; exact hk) i
  unfold alphaSum
  calc d.alpha i = ∑ l ∈ ({i} : Finset (Fin k)), d.alpha l := by simp
    _ < ∑ l ∈ Finset.univ, d.alpha l := by
        apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _)
          (Finset.mem_univ j) (by simp [hji]) (d.alpha_pos j)
        intro l _ hl; exact le_of_lt (d.alpha_pos l)

/-- **Moment determinacy on `[0,1]`.** Two finite Borel measures on `ℝ`, each carried by the
interval `[0,1]` (their complement is null) and agreeing on every power moment `∫ xⁿ`, integrate
every continuous function `g` to the same value. The proof approximates `g` uniformly on `[0,1]` by
a polynomial (Weierstrass), matches the polynomial integrals via the moment hypothesis, and lets
the approximation error vanish. -/
private lemma integral_eq_of_moments_eq_on_Icc {μ ν : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (hμ : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0) (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν)
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  classical
  -- A continuous `f` is integrable against any finite measure carried by `[0,1]`: off `[0,1]` the
  -- measure is null, and on the compact `[0,1]` continuity bounds `f`.
  have hint : ∀ (ρ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure ρ],
      ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0 → ∀ {f : ℝ → ℝ}, Continuous f → MeasureTheory.Integrable f ρ := by
    intro ρ _ hρ f hf
    -- `f` agrees a.e. (off the null complement) with its truncation, which is bounded.
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hf.continuousOn
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const C) hf.aestronglyMeasurable
      ?_
    -- `‖f x‖ ≤ C` holds a.e. since the complement of `[0,1]` is null.
    refine MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl (Set.Icc (0 : ℝ) 1) ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hC x hx)
    · have hz : ρ.restrict (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
        MeasureTheory.Measure.restrict_eq_zero.mpr hρ
      rw [hz, MeasureTheory.ae_zero]; exact Filter.eventually_bot
  -- Polynomial moment match: integrals of `p.eval` against `μ` and `ν` agree.
  have hpoly : ∀ p : Polynomial ℝ, ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
    intro p
    have heval : ∀ x : ℝ, p.eval x = ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n * x ^ n :=
      fun x => Polynomial.eval_eq_sum_range x
    simp_rw [heval]
    rw [MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl (fun n _ => ?_)
      simp_rw [MeasureTheory.integral_const_mul, hmom n]
    · exact fun n _ => (hint ν hν (continuous_pow n)).const_mul _
    · exact fun n _ => (hint μ hμ (continuous_pow n)).const_mul _
  -- Approximate `g` uniformly on `[0,1]` and pass to the limit.
  have hgμ : MeasureTheory.Integrable g μ := hint μ hμ hg
  have hgν : MeasureTheory.Integrable g ν := hint ν hν hg
  -- It suffices to bound the gap by `ε · (μ univ + ν univ)` for every `ε > 0`.
  rw [← sub_eq_zero]
  by_contra hne
  set δ := |∫ x, g x ∂μ - ∫ x, g x ∂ν| with hδ
  have hδ_pos : 0 < δ := abs_pos.mpr hne
  set M := (μ Set.univ).toReal + (ν Set.univ).toReal + 1 with hM
  have hM_pos : 0 < M := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg.continuousOn (δ / M)
    (by positivity)
  -- `‖g - p.eval‖ ≤ δ/M` a.e. against each measure.
  have hbound : ∀ (ρ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure ρ],
      ρ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
      |∫ x, g x ∂ρ - ∫ x, p.eval x ∂ρ| ≤ δ / M * (ρ Set.univ).toReal := by
    intro ρ _ hρ
    rw [← MeasureTheory.integral_sub (hint ρ hρ hg) (hint ρ hρ (Polynomial.continuous p))]
    have hbd : ‖∫ x, (g x - p.eval x) ∂ρ‖ ≤ δ / M * ρ.real Set.univ := by
      refine MeasureTheory.norm_integral_le_of_norm_le_const ?_
      refine MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl (Set.Icc (0 : ℝ) 1) ?_ ?_
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_)
        simpa [abs_sub_comm] using (hp x hx).le
      · have hz : ρ.restrict (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
          MeasureTheory.Measure.restrict_eq_zero.mpr hρ
        rw [hz, MeasureTheory.ae_zero]; exact Filter.eventually_bot
    rwa [Real.norm_eq_abs, MeasureTheory.measureReal_def] at hbd
  have hbμ := hbound μ hμ
  have hbν := hbound ν hν
  rw [hpoly] at hbμ
  -- triangle inequality: δ = |∫g μ - ∫g ν| ≤ |∫g μ - ∫p ν| + |∫p ν - ∫g ν|
  have hkey : δ ≤ δ / M * ((μ Set.univ).toReal + (ν Set.univ).toReal) := by
    calc δ = |∫ x, g x ∂μ - ∫ x, g x ∂ν| := hδ
      _ ≤ |∫ x, g x ∂μ - ∫ x, p.eval x ∂ν| + |∫ x, p.eval x ∂ν - ∫ x, g x ∂ν| :=
          abs_sub_le _ _ _
      _ ≤ δ / M * (μ Set.univ).toReal + δ / M * (ν Set.univ).toReal := by
          have hbν' : |∫ x, p.eval x ∂ν - ∫ x, g x ∂ν| ≤ δ / M * (ν Set.univ).toReal := by
            rw [abs_sub_comm]; exact hbν
          exact add_le_add hbμ hbν'
      _ = δ / M * ((μ Set.univ).toReal + (ν Set.univ).toReal) := by ring
  -- but δ/M·(μ+ν) < δ since μ+ν < M, contradiction.
  have hlt : δ / M * ((μ Set.univ).toReal + (ν Set.univ).toReal) < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM_pos]
    have : (μ Set.univ).toReal + (ν Set.univ).toReal < M := by rw [hM]; linarith
    nlinarith [hδ_pos]
  linarith

/-- The beta-density recursion: `betaPDFReal α β x · x = (α/(α+β)) · betaPDFReal (α+1) β x`. This
is the pointwise identity underlying the rising-factorial moment recursion of the Beta law;
integrating it yields the `n`-th moment. -/
private lemma betaPDFReal_mul_coord {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    betaPDFReal α β x * x = (α / (α + β)) * betaPDFReal (α + 1) β x := by
  have hratio : ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β = α / (α + β) := by
    simp only [ProbabilityTheory.beta]
    rw [Real.Gamma_add_one (ne_of_gt hα),
        show α + 1 + β = (α + β) + 1 from by ring,
        Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
    field_simp
  rw [← hratio]
  simp only [betaPDFReal]
  split_ifs with h1
  · have hx_ne : x ≠ 0 := ne_of_gt h1.1
    have hB : ProbabilityTheory.beta α β ≠ 0 := (ProbabilityTheory.beta_pos hα hβ).ne'
    have hB1 : ProbabilityTheory.beta (α + 1) β ≠ 0 :=
      (ProbabilityTheory.beta_pos (by linarith) hβ).ne'
    have key : x ^ (α - 1) * x = x ^ α := by
      rw [← Real.rpow_add_one hx_ne, sub_add_cancel]
    rw [show (α + 1 - 1 : ℝ) = α from by ring,
        show (1 : ℝ) / ProbabilityTheory.beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1) * x =
            1 / ProbabilityTheory.beta α β * (x ^ (α - 1) * x) * (1 - x) ^ (β - 1) from by ring,
        key]
    field_simp
  · ring

/-- **The `n`-th moment of the Dirichlet coordinate `i` matches the `n`-th moment of
`Beta(αᵢ, α₀ − αᵢ)`.** Proven by induction on `n`: Each step strips one factor of the coordinate,
shifting `αᵢ ↦ αᵢ + 1` on both sides and contributing the common ratio `αᵢ / α₀`. -/
private lemma marginal_moment_eq (d : DirichletDist k) (hk : 1 < k) (i : Fin k) (n : ℕ) :
    ∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
      (if h : i.val < k - 1 then y ⟨i.val, by omega⟩
       else 1 - ∑ j : Fin (k - 1), y j) ^ n =
    ∫ x : ℝ, betaPDFReal (d.alpha i) (d.alphaSum - d.alpha i) x * x ^ n := by
  induction n generalizing d with
  | zero =>
    simp only [pow_zero, mul_one]
    rw [d.densityReduced_integral_one hk,
        integral_betaPDFReal_eq_one (d.alpha i) (d.alphaSum - d.alpha i) (d.alpha_pos i)
          (by linarith [d.alpha_lt_alphaSum hk i])]
  | succ n ih =>
    have hk0 : 0 < k := by omega
    set α' := Function.update d.alpha i (d.alpha i + 1) with hα'_def
    have hα'_pos : ∀ j, 0 < α' j := update_add_one_pos d.alpha_pos i
    let d' : DirichletDist k := ⟨α', hα'_pos⟩
    have hd'_alpha : d'.alpha = α' := rfl
    have hα'_i : α' i = d.alpha i + 1 := Function.update_self i (d.alpha i + 1) d.alpha
    have hd'_sum : d'.alphaSum = d.alphaSum + 1 := by
      have h := d.shiftAlpha_sum hk0 i 1
      rw [d.shiftAlpha_eq_update i 1] at h
      change ∑ j, α' j = d.alphaSum + 1
      rw [hα'_def]; exact h
    -- LHS: peel one coordinate factor, shift parameters, get ratio αᵢ/α₀ times the `d'` moment of
    -- order `n`.
    have hLHS : (∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
        (if h : i.val < k - 1 then y ⟨i.val, by omega⟩ else 1 - ∑ j, y j) ^ (n + 1)) =
        (d.alpha i / d.alphaSum) *
        ∫ y : Fin (k - 1) → ℝ, d'.densityReduced (by omega) y *
          (if h : i.val < k - 1 then y ⟨i.val, by omega⟩ else 1 - ∑ j, y j) ^ n := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext y
      simp only [densityReduced]
      set x : Fin k → ℝ := fun j =>
        if h : j.val < k - 1 then y ⟨j.val, by omega⟩ else 1 - ∑ l : Fin (k - 1), y l
      have hxi : (if h : i.val < k - 1 then y ⟨i.val, h⟩ else 1 - ∑ j, y j) = x i := by
        simp only [x]
      rw [hxi, pow_succ, ← mul_assoc, mul_right_comm,
          dirichletPDFReal_mul_coord d.alpha_pos hk0 i x]
      rw [show multivariateBeta k (Function.update d.alpha i (d.alpha i + 1)) =
            multivariateBeta k (d.shiftAlpha i 1) from by rw [d.shiftAlpha_eq_update i 1],
          d.multivariateBeta_shift_ratio hk0 i]
      ring
    -- RHS: same recursion on the Beta moment, same ratio αᵢ/α₀.
    have hβ_pos : 0 < d.alphaSum - d.alpha i := by linarith [d.alpha_lt_alphaSum hk i]
    have hRHS : (∫ x : ℝ, betaPDFReal (d.alpha i) (d.alphaSum - d.alpha i) x * x ^ (n + 1)) =
        (d.alpha i / d.alphaSum) *
        ∫ x : ℝ, betaPDFReal (d.alpha i + 1) (d.alphaSum - d.alpha i) x * x ^ n := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext x
      rw [pow_succ, ← mul_assoc, mul_right_comm,
          betaPDFReal_mul_coord (d.alpha_pos i) hβ_pos x]
      rw [show d.alpha i + (d.alphaSum - d.alpha i) = d.alphaSum from by ring]
      ring
    rw [hLHS, hRHS, ih d']
    -- after IH, the `d'` moment is `betaPDFReal (d'.alpha i) (d'.alphaSum - d'.alpha i)`; rewrite
    -- those into `(αᵢ+1, α₀-αᵢ)` to match the RHS Beta.
    congr 2
    ext x
    rw [hd'_alpha, hα'_i, hd'_sum]
    congr 2
    ring

/-- The `i`-th marginal is Beta(αᵢ, α₀ - αᵢ). Requires `k ≥ 2` so that `α₀ - αᵢ > 0`. That this is
the genuine marginal law — not just a moment-matched candidate — is `marginalBeta_expect`, which
shows the Dirichlet coordinate `i` pushes forward to it. -/
noncomputable def marginalBeta (hk : 1 < k) (i : Fin k) : ContDist :=
  ContDist.beta (d.alpha i) (d.alphaSum - d.alpha i) (d.alpha_pos i)
    (by linarith [d.alpha_lt_alphaSum hk i])

/-- The reduced Dirichlet density equals `(1/B(α))` times the simplex integrand, pointwise. This
exposes `densityReduced` as a constant multiple of the (integrable, measurable) simplex
integrand. -/
private lemma densityReduced_eq_const_mul_integrand (hk : 1 < k) (y : Fin (k - 1) → ℝ) :
    d.densityReduced (by omega) y =
    1 / multivariateBeta k d.alpha *
      (if (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 then
        (∏ i : Fin (k - 1), (y i) ^ (d.alpha ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i, y i) ^ (d.alpha ⟨k - 1, by omega⟩ - 1)
      else 0) := by
  simp only [densityReduced, dirichletPDFReal]
  set x : Fin k → ℝ := fun i =>
    if h : i.val < k - 1 then y ⟨i.val, by omega⟩ else 1 - ∑ j : Fin (k - 1), y j with hx_def
  have hiff : OnSimplex k x ↔ (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1 :=
    onSimplex_reconstructed_iff hk y
  by_cases hy : (∀ i : Fin (k - 1), 0 < y i) ∧ ∑ i, y i < 1
  · rw [if_pos (hiff.mpr hy), if_pos hy]
    congr 1; exact prod_reconstructed_eq hk d.alpha y hy
  · rw [if_neg (fun h => hy (hiff.mp h)), if_neg hy, mul_zero]

/-- The reduced Dirichlet density is integrable over `ℝ^(k-1)`. -/
private lemma densityReduced_integrable (hk : 1 < k) :
    MeasureTheory.Integrable (d.densityReduced (by omega)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hint := MeasureTheory.simplexIntegrand_integrable d.alpha d.alpha_pos
  have heq : d.densityReduced (by omega) =
      fun y => 1 / multivariateBeta (m + 2) d.alpha *
        (if (∀ i : Fin (m + 1), 0 < y i) ∧ ∑ i, y i < 1 then
          (∏ i : Fin (m + 1), (y i) ^ (d.alpha ⟨i.val, by omega⟩ - 1)) *
            (1 - ∑ i, y i) ^ (d.alpha ⟨m + 1, by omega⟩ - 1)
        else 0) := by
    funext y
    have := d.densityReduced_eq_const_mul_integrand (by omega) y
    simpa using this
  rw [heq]
  exact hint.const_mul _

/-- The reduced Dirichlet density is a.e.-strongly measurable. -/
private lemma densityReduced_aestronglyMeasurable (hk : 1 < k) :
    MeasureTheory.AEStronglyMeasurable (d.densityReduced (by omega)) :=
  (d.densityReduced_integrable hk).aestronglyMeasurable

/-- **Marginalization: The `i`-th coordinate of the Dirichlet is `Beta(αᵢ, α₀ - αᵢ)`.** For any
continuous test function `g`, integrating `g` against the `i`-th coordinate of the Dirichlet
density (in reduced coordinates) equals the expectation of `g` under the marginal Beta. This is the
genuine pushforward of the Dirichlet law along coordinate `i`, expressed via integrals since the
Dirichlet density is carried in reduced coordinates rather than as a packaged measure; testing
against all continuous `g` characterizes the marginal law. `marginalBeta_mean` and
`marginalBeta_variance` are the `g = id` / `g = (·)²` corollaries. -/
theorem marginalBeta_expect (hk : 1 < k) (i : Fin k) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y *
      g (if h : i.val < k - 1 then y ⟨i.val, by omega⟩
         else 1 - ∑ j : Fin (k - 1), y j) =
    (d.marginalBeta hk i).expect g := by
  classical
  have hk0 : 0 < k := by omega
  set D : (Fin (k - 1) → ℝ) → ℝ := d.densityReduced hk0 with hD_def
  -- The coordinate map `φ` reconstructing `xᵢ` from reduced coordinates.
  set φ : (Fin (k - 1) → ℝ) → ℝ := fun y =>
    if h : i.val < k - 1 then y ⟨i.val, by omega⟩ else 1 - ∑ j : Fin (k - 1), y j with hφ_def
  have hD_nonneg : ∀ y, 0 ≤ D y := fun y => d.density_nonneg hk0 _
  have hD_int : MeasureTheory.Integrable D := d.densityReduced_integrable hk
  have hφ_meas : Measurable φ := by
    rw [hφ_def]
    by_cases h : i.val < k - 1
    · simp only [h, dite_true]; exact measurable_pi_apply _
    · simp only [h, dite_false]
      exact measurable_const.sub (Finset.measurable_sum _ (fun j _ => measurable_pi_apply j))
  -- Base probability measure on `ℝ^(k-1)` carried by the reduced Dirichlet density.
  set νbase : MeasureTheory.Measure (Fin (k - 1) → ℝ) :=
    MeasureTheory.volume.withDensity (fun y => ENNReal.ofReal (D y)) with hνbase_def
  have hνbase_prob : MeasureTheory.IsProbabilityMeasure νbase := by
    constructor
    rw [hνbase_def, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
        MeasureTheory.Measure.restrict_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hD_int
          (Filter.Eventually.of_forall hD_nonneg)]
    rw [hD_def, d.densityReduced_integral_one hk, ENNReal.ofReal_one]
  -- The two measures on `ℝ`.
  set μ : MeasureTheory.Measure ℝ := νbase.map φ with hμ_def
  set ν : MeasureTheory.Measure ℝ := (d.marginalBeta hk i).toMeasure with hν_def
  have hμ_prob : MeasureTheory.IsProbabilityMeasure μ :=
    MeasureTheory.Measure.isProbabilityMeasure_map hφ_meas.aemeasurable
  have hν_prob : MeasureTheory.IsProbabilityMeasure ν :=
    (d.marginalBeta hk i).toMeasure_isProbability
  -- Bridge: `∫ y, D y · f(φ y) ∂volume = ∫ z, f z ∂μ` for any continuous (hence measurable) `f`.
  have hbridge : ∀ {f : ℝ → ℝ}, Continuous f →
      ∫ y, D y * f (φ y) = ∫ z, f z ∂μ := by
    intro f hf
    rw [hμ_def, MeasureTheory.integral_map hφ_meas.aemeasurable hf.aestronglyMeasurable,
        hνbase_def,
        integral_withDensity_eq_integral_toReal_smul₀
          hD_int.aemeasurable.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1; ext y
    simp [smul_eq_mul, ENNReal.toReal_ofReal (hD_nonneg y)]
  -- RHS as a measure integral.
  have hRHS_meas : (d.marginalBeta hk i).expect g = ∫ z, g z ∂ν :=
    (d.marginalBeta hk i).expect_eq_measure_integral g
  -- Both measures are carried by `[0,1]`.
  have hμ_supp : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    -- Where the density is nonzero the reconstructed point is on the open simplex, so `φ y` lies in
    -- `(0,1)`.
    have hsupp : ∀ y, D y ≠ 0 → φ y ∈ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      rw [hD_def, densityReduced, dirichletPDFReal] at hy
      set x : Fin k → ℝ := fun j =>
        if h : j.val < k - 1 then y ⟨j.val, by omega⟩ else 1 - ∑ l : Fin (k - 1), y l with hx_def
      by_contra hφ
      have hos : OnSimplex k x := by
        by_contra h; rw [if_neg h] at hy; exact hy rfl
      -- on the simplex, `φ y = x i ∈ (0,1)`.
      have hφx : φ y = x i := by simp only [hφ_def, hx_def]
      have hxi_pos : 0 < x i := hos.1 i
      have hxi_lt : x i < 1 := by
        obtain ⟨j, hji⟩ : ∃ j : Fin k, j ≠ i :=
          Fintype.exists_ne_of_one_lt_card (by simp only [Fintype.card_fin]; exact hk) i
        have hsum := hos.2
        have hmem : i ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ i
        have hother : 0 < ∑ l ∈ Finset.univ.erase i, x l :=
          Finset.sum_pos (fun l _ => hos.1 l)
            ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩⟩
        rw [← Finset.add_sum_erase _ x hmem] at hsum
        linarith
      exact hφ (hφx ▸ ⟨hxi_pos.le, hxi_lt.le⟩)
    rw [hμ_def, MeasureTheory.Measure.map_apply hφ_meas measurableSet_Icc.compl,
        hνbase_def, MeasureTheory.withDensity_apply _ (hφ_meas measurableSet_Icc.compl)]
    rw [MeasureTheory.setLIntegral_congr_fun (hφ_meas measurableSet_Icc.compl)
      (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
    intro y hy
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hy
    have hDy : D y = 0 := by
      by_contra hne; exact hy (hsupp y hne)
    simp [hDy]
  have hν_supp : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    rw [hν_def, ContDist.toMeasure_eq,
        MeasureTheory.withDensity_apply _ measurableSet_Icc.compl]
    rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Icc.compl
      (g := fun _ => 0) ?_, MeasureTheory.lintegral_zero]
    intro x hx
    rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, not_le] at hx
    simp only [marginalBeta, ContDist.beta_density]
    rw [betaPDFReal_eq_zero_of_not_mem _ _
      (by rintro ⟨h0, h1⟩; rcases hx with h | h <;> linarith), ENNReal.ofReal_zero]
  -- Equal moments.
  have hmom : ∀ n : ℕ, ∫ z, z ^ n ∂μ = ∫ z, z ^ n ∂ν := by
    intro n
    rw [← hbridge (continuous_pow n), hν_def, ← (d.marginalBeta hk i).expect_eq_measure_integral]
    -- LHS `∫ D · (φ ·)^n` is the Dirichlet `n`-th coordinate moment; RHS `expect (·^n)` is the
    -- Beta `n`-th moment. Both equal by `marginal_moment_eq`.
    rw [(d.marginalBeta hk i).expect_eq_integral]
    simp only [marginalBeta, ContDist.beta_density]
    exact d.marginal_moment_eq hk i n
  -- Determinacy closes the goal.
  rw [show (∫ y : Fin (k - 1) → ℝ, d.densityReduced (by omega) y * g (φ y)) =
        ∫ y, D y * g (φ y) from rfl, hbridge hg, hRHS_meas]
  exact integral_eq_of_moments_eq_on_Icc hμ_supp hν_supp hmom hg

/-- The mean of the `i`-th marginal Beta matches the Dirichlet mean. Corollary of
`marginalBeta_expect` at `g = id`, identifying the marginal expectation with the integral
characterization of the mean (`mean_eq`). -/
lemma marginalBeta_mean (hk : 1 < k) (i : Fin k) :
    (d.marginalBeta hk i).expect id = d.mean (by omega) i := by
  rw [← d.marginalBeta_expect hk i (g := id) continuous_id]
  simpa only [id_eq] using d.mean_eq hk i

/-- The variance of the `i`-th marginal Beta matches the Dirichlet variance. Corollary of
`marginalBeta_expect` at `g = id` (first moment) and `g = (·)²` (second moment), combined with the
integral characterization of the variance (`variance_eq`). -/
lemma marginalBeta_variance (hk : 1 < k) (i : Fin k) :
    (d.marginalBeta hk i).variance id = d.variance (by omega) i := by
  rw [ContDist.variance]
  simp only [id_eq]
  rw [← d.marginalBeta_expect hk i (g := fun x => x ^ 2) (by fun_prop),
      show (d.marginalBeta hk i).expect id = d.mean (by omega) i from d.marginalBeta_mean hk i]
  -- the second-moment integral minus the squared mean is exactly `variance_eq`.
  exact d.variance_eq hk i

/-- When `k = 2`, the Dirichlet PDF on `![x, 1-x]` equals the Beta PDF at `x`. -/
lemma _root_.Econlib.Probability.dirichletPDFReal_two_eq_betaPDFReal (α : Fin 2 → ℝ)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    dirichletPDFReal 2 α ![x, 1 - x] = betaPDFReal (α 0) (α 1) x := by
  have hsimp : OnSimplex 2 ![x, 1 - x] := by
    constructor
    · intro i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [dirichletPDFReal, if_pos hsimp, multivariateBeta_two]
  have hcond : (0 : ℝ) < x ∧ x < 1 := ⟨hx0, hx1⟩
  simp only [betaPDFReal, if_pos hcond]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## Special cases -/

/-- The symmetric Dirichlet with all `αᵢ = 1` — the uniform distribution on the simplex. -/
def uniform (k : ℕ) : DirichletDist k where
  alpha := fun _ => 1
  alpha_pos := fun _ => one_pos

/-- The Jeffreys prior: Symmetric Dirichlet with all `αᵢ = 1/2`. -/
noncomputable def jeffreys (k : ℕ) : DirichletDist k where
  alpha := fun _ => 1 / 2
  alpha_pos := fun _ => by positivity

/-- Each component mean of the uniform Dirichlet (`all αᵢ = 1`) equals `1 / k`. -/
lemma uniform_mean (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (uniform k).mean hk i = 1 / (k : ℝ) := by
  simp [mean, uniform, alphaSum, Finset.sum_const]

end DirichletDist

end Econlib.Probability
