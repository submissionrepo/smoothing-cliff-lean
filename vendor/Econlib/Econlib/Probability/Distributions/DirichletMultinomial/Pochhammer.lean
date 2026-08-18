/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.SpecialFunctions.Pochhammer
public import Econlib.Probability.Distributions.Dirichlet
public import Econlib.Probability.Distributions.Multinomial

/-!
# Pochhammer bridges for the Dirichlet-Multinomial distribution

This file establishes the algebraic bridges between the Dirichlet-Multinomial PMF and the
Pochhammer/Γ-function algebra developed in `Econlib.Math.Analysis.SpecialFunctions.Pochhammer`.
Specifically, it provides a decomposition of `MultinomialOutcome (m+1) n` along its first
coordinate, proves the multivariate Chu–Vandermonde identity, and computes the multivariate Beta
ratio `B(x+α)/B(α)` in terms of ascending Pochhammer symbols.

## Main definitions

* `MultinomialOutcome.head` — first coordinate of a `MultinomialOutcome (m+1) n`, as an element of
  `Fin (n+1)`.
* `MultinomialOutcome.tail` — remaining coordinates of a `MultinomialOutcome (m+1) n`, as a
  `MultinomialOutcome m (n - head)`.
* `MultinomialOutcome.cons` — constructor: Builds a `MultinomialOutcome (m+1) n` from a head value
  and a tail.
* `MultinomialOutcome.sigmaEquiv` — equivalence
  `MultinomialOutcome (m+1) n ≃ Σ j : Fin (n+1),
  MultinomialOutcome m (n - j)`.

## Main statements

* `vandermonde_multinomial` — multivariate Chu–Vandermonde identity: The weighted sum of Pochhammer
  products over all `MultinomialOutcome m n` equals the Pochhammer symbol of the sum of parameters.
* `multivariateBeta_ratio_eq` — `B(x+α)/B(α) = ∏ᵢ (αᵢ)↑^(xᵢ) / (∑ αᵢ)↑^n`.

## Tags

dirichlet multinomial, pochhammer, chu-vandermonde, multivariate beta
-/

@[expose] public section

namespace Econlib.Probability

/-! ## MultinomialOutcome Decomposition (coordinate 0) -/

/-- The first coordinate of `x : MultinomialOutcome (m + 1) n`, as an element of `Fin (n + 1)`. The
bound `x.1 0 ≤ n` follows from the multinomial constraint `∑ i, x.1 i = n`. -/
def MultinomialOutcome.head {m n : ℕ} (x : MultinomialOutcome (m + 1) n) : Fin (n + 1) :=
  ⟨x.1 0, by
    have : x.1 0 ≤ ∑ i, x.1 i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    omega⟩

/-- The tail of `x : MultinomialOutcome (m + 1) n`, obtained by dropping the first coordinate. The
result is a `MultinomialOutcome m (n - x.1 0)`, since the remaining coordinates sum to `n - x.1 0`
by the multinomial constraint. -/
def MultinomialOutcome.tail {m n : ℕ} (x : MultinomialOutcome (m + 1) n) :
    MultinomialOutcome m (n - x.1 0) :=
  ⟨Fin.tail x.1, by
    have hsum := x.2
    rw [Fin.sum_univ_succ] at hsum
    have : ∑ i : Fin m, Fin.tail x.1 i = ∑ i : Fin m, x.1 i.succ :=
      Finset.sum_congr rfl (fun i _ => rfl)
    omega⟩

/-- Build a `MultinomialOutcome (m + 1) n` from a head value `j : Fin (n + 1)` and a tail
`y : MultinomialOutcome m (n - j)`. This is the inverse of the `(head, tail)` decomposition. -/
def MultinomialOutcome.cons {m n : ℕ} (j : Fin (n + 1))
    (y : MultinomialOutcome m (n - j)) : MultinomialOutcome (m + 1) n :=
  ⟨Fin.cons j y.1, by
    rw [Fin.sum_cons, y.2]; omega⟩

/-- Equivalence between `MultinomialOutcome (m + 1) n` and
`Σ j : Fin (n + 1), MultinomialOutcome m (n - j)`, given by sending `x` to `(x.head, x.tail)` with
inverse `(j, y) ↦ cons j y`. -/
def MultinomialOutcome.sigmaEquiv (m n : ℕ) :
    MultinomialOutcome (m + 1) n ≃
      Σ (j : Fin (n + 1)), MultinomialOutcome m (n - j) where
  toFun x := ⟨x.head, x.tail⟩
  invFun p := cons p.1 p.2
  left_inv x := by
    ext i
    simp only [cons, head, tail]
    exact (Fin.cons_self_tail x.1 ▸ rfl)
  right_inv p := by
    ext
    · simp [cons, head]
    · rename_i i
      simp [cons, tail, Fin.tail_cons]

/-- The zeroth coordinate of `cons j y` is `j`. -/
@[simp] lemma MultinomialOutcome.cons_zero {m n : ℕ} (j : Fin (n + 1))
    (y : MultinomialOutcome m (n - j)) :
    (MultinomialOutcome.cons j y).1 0 = j := by
  simp [cons, Fin.cons_zero]

/-- The `i.succ`-th coordinate of `cons j y` equals `y.1 i`. -/
@[simp] lemma MultinomialOutcome.cons_succ {m n : ℕ} (j : Fin (n + 1))
    (y : MultinomialOutcome m (n - j)) (i : Fin m) :
    (MultinomialOutcome.cons j y).1 i.succ = y.1 i := by
  simp [cons, Fin.cons_succ]

/-! ## Multivariate Vandermonde Identity -/

/-- **Multivariate Chu–Vandermonde identity.** For `α : Fin m → ℝ` and `n : ℕ`, $$\sum_{x \in
\mathrm{MultinomialOutcome}(m, n)} \binom{n}{x} \prod_i (\alpha_i)^{\uparrow x_i} = \Bigl(\sum_i
\alpha_i\Bigr)^{\uparrow n},$$ where `(a)↑k` denotes the ascending Pochhammer symbol
`ascPochhammer ℝ k` evaluated at `a`. -/
theorem vandermonde_multinomial {m : ℕ} (α : Fin m → ℝ) (n : ℕ) :
    ∑ x : MultinomialOutcome m n,
      (Nat.multinomial Finset.univ x.1 : ℝ) *
        ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i)) =
      Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) := by
  induction m generalizing n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [ascPochhammer_eval_zero]
    rcases n with _ | n
    · simp only [ite_true]
      rw [Fintype.sum_eq_single ⟨Fin.elim0, by simp⟩ (fun b hb => by
        exfalso; apply hb; ext i; exact Fin.elim0 i)]
      simp [Nat.multinomial, Finset.prod_empty]
    · simp only [Nat.succ_ne_zero, ite_false]
      have hempty : (Finset.univ : Finset (MultinomialOutcome 0 (n + 1))) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro ⟨f, hf⟩ _
        have : ∑ i : Fin 0, f i = 0 := by simp
        omega
      rw [hempty, Finset.sum_empty]
  | succ m ih =>
    have hx_eq : ∀ x : MultinomialOutcome (m + 1) n,
        (MultinomialOutcome.cons x.head x.tail).1 = x.1 := by
      intro x
      simp [MultinomialOutcome.cons, MultinomialOutcome.head, MultinomialOutcome.tail]
    rw [show ∑ x : MultinomialOutcome (m + 1) n,
          (Nat.multinomial Finset.univ x.1 : ℝ) *
            ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i)) =
        ∑ j : Fin (n + 1), ∑ y : MultinomialOutcome m (n - j),
          (Nat.multinomial Finset.univ (MultinomialOutcome.cons j y).1 : ℝ) *
            ∏ i, Polynomial.eval (α i)
              (ascPochhammer ℝ ((MultinomialOutcome.cons j y).1 i))
      from by
        rw [← Fintype.sum_sigma']
        exact Fintype.sum_equiv (MultinomialOutcome.sigmaEquiv m n) _ _
          (fun x => by
            have := hx_eq x
            simp only [MultinomialOutcome.sigmaEquiv, Equiv.coe_fn_mk]
            rw [this])]
    have hsimp_summand : ∀ (j : Fin (n + 1)) (y : MultinomialOutcome m (n - j)),
        (Nat.multinomial Finset.univ (MultinomialOutcome.cons j y).1 : ℝ) *
          ∏ i, Polynomial.eval (α i) (ascPochhammer ℝ ((MultinomialOutcome.cons j y).1 i)) =
        (Nat.choose n j : ℝ) * (Nat.multinomial Finset.univ y.1 : ℝ) *
          Polynomial.eval (α 0) (ascPochhammer ℝ j) *
          ∏ i : Fin m, Polynomial.eval (α i.succ) (ascPochhammer ℝ (y.1 i)) := by
      intro j y
      have hmult : Nat.multinomial Finset.univ (MultinomialOutcome.cons j y).1 =
          Nat.choose n j * Nat.multinomial Finset.univ y.1 := by
        have hj_le : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
        have hsum_cons : ∑ i, (MultinomialOutcome.cons j y).1 i = n :=
          (MultinomialOutcome.cons j y).2
        have hprod_ne : ∏ i : Fin (m + 1),
            ((MultinomialOutcome.cons j y).1 i).factorial ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
        have hprod_ne' : ∏ i : Fin m, (y.1 i).factorial ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero _)
        have spec1 := Nat.multinomial_spec Finset.univ (MultinomialOutcome.cons j y).1
        rw [hsum_cons] at spec1
        have spec2 := Nat.multinomial_spec Finset.univ y.1
        rw [y.2] at spec2
        have hprod_split : ∏ i : Fin (m + 1),
            ((MultinomialOutcome.cons j y).1 i).factorial =
          (j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial := by
          rw [Fin.prod_univ_succ]
          congr 1
        rw [hprod_split] at spec1
        have := Nat.choose_mul_factorial_mul_factorial hj_le
        have hfact_pos : 0 < (j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial :=
          Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos (fun i _ => Nat.factorial_pos _))
        apply Nat.eq_of_mul_eq_mul_left hfact_pos
        calc ((j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial) *
              Nat.multinomial Finset.univ (MultinomialOutcome.cons j y).1
            = n.factorial := spec1
          _ = Nat.choose n j * (j : ℕ).factorial * (n - j).factorial := this.symm
          _ = Nat.choose n j * ((j : ℕ).factorial *
                ((∏ i : Fin m, (y.1 i).factorial) * Nat.multinomial Finset.univ y.1)) := by
              rw [spec2]; ring
          _ = ((j : ℕ).factorial * ∏ i : Fin m, (y.1 i).factorial) *
              (Nat.choose n j * Nat.multinomial Finset.univ y.1) := by ring
      have hprod : ∏ i : Fin (m + 1),
          Polynomial.eval (α i)
            (ascPochhammer ℝ ((MultinomialOutcome.cons j y).1 i)) =
        Polynomial.eval (α 0) (ascPochhammer ℝ j) *
          ∏ i : Fin m, Polynomial.eval (α i.succ) (ascPochhammer ℝ (y.1 i)) := by
        rw [Fin.prod_univ_succ]
        congr 1
      rw [hmult, hprod]; push_cast; ring
    simp_rw [hsimp_summand]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp_rw [mul_left_comm _ (Polynomial.eval (α 0) _)]
    simp_rw [← Finset.mul_sum]
    simp_rw [ih (fun i => α i.succ)]
    rw [show (∑ i, α i) = α 0 + ∑ i : Fin m, α i.succ from Fin.sum_univ_succ α]
    set a := α 0; set b := ∑ i : Fin m, α i.succ
    have hcv := chu_vandermonde_two a b n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcv
    rw [← hcv]
    rw [Finset.sum_range]
    congr 1; ext x; ring

/-! ## Multivariate Beta Ratio in Pochhammer Form -/

/-- The multivariate Beta ratio expressed in ascending Pochhammer symbols. For positive
concentration parameters `α : Fin m → ℝ` and `x : MultinomialOutcome m n`,
$$\frac{B(x+\alpha)}{B(\alpha)} = \frac{\prod_i (\alpha_i)^{\uparrow x_i}}{(\sum_i
\alpha_i)^{\uparrow n}},$$ where `B` denotes `multivariateBeta` and `(a)↑k = ascPochhammer ℝ k`
evaluated at `a`. -/
theorem multivariateBeta_ratio_eq {m : ℕ} {α : Fin m → ℝ} (hα : ∀ i, 0 < α i)
    (hm : 0 < m) {n : ℕ} (x : MultinomialOutcome m n) :
    multivariateBeta m (fun i => ↑(x.1 i) + α i) / multivariateBeta m α =
      (∏ i, Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i))) /
        Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) := by
  have hα_sum_pos : 0 < ∑ i, α i :=
    Finset.sum_pos (fun i _ => hα i) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hBα : multivariateBeta m α ≠ 0 := multivariateBeta_ne_zero hm hα
  have hxα_pos : ∀ i, 0 < (↑(x.1 i) : ℝ) + α i :=
    fun i => add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (hα i)
  have hBxα : multivariateBeta m (fun i => ↑(x.1 i) + α i) ≠ 0 :=
    multivariateBeta_ne_zero hm hxα_pos
  have hGamma_ratio : ∀ i : Fin m,
      Real.Gamma (↑(x.1 i) + α i) / Real.Gamma (α i) =
        Polynomial.eval (α i) (ascPochhammer ℝ (x.1 i)) := by
    intro i; rw [add_comm]; exact Real.Gamma_ratio_eq_ascPochhammer (α i) (hα i) (x.1 i)
  have hsum_shift : ∑ i, ((↑(x.1 i) : ℝ) + α i) = ↑n + ∑ i, α i := by
    rw [Finset.sum_add_distrib, ← Nat.cast_sum, x.2]
  have hGamma_sum_ratio :
      Real.Gamma (↑n + ∑ i, α i) / Real.Gamma (∑ i, α i) =
        Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) := by
    rw [add_comm]; exact Real.Gamma_ratio_eq_ascPochhammer _ hα_sum_pos n
  have hΓα_ne : ∀ i, Real.Gamma (α i) ≠ 0 :=
    fun i => ne_of_gt (Real.Gamma_pos_of_pos (hα i))
  have hΓαsum_ne : Real.Gamma (∑ i, α i) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hα_sum_pos)
  have hΓnαsum_ne : Real.Gamma (↑n + ∑ i, α i) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hprod_Γα_ne : ∏ i : Fin m, Real.Gamma (α i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hΓα_ne i)
  have hPoch_ne : Polynomial.eval (∑ i, α i) (ascPochhammer ℝ n) ≠ 0 := by
    rw [← hGamma_sum_ratio]; exact div_ne_zero hΓnαsum_ne hΓαsum_ne
  rw [div_eq_div_iff (ne_of_gt (multivariateBeta_pos hm hα)) hPoch_ne]
  unfold multivariateBeta
  simp only [hsum_shift]
  rw [← hGamma_sum_ratio]
  field_simp
  rw [← Finset.prod_mul_distrib]
  congr 1
  · ext i
    have := hGamma_ratio i
    rw [div_eq_iff (hΓα_ne i)] at this
    linarith

end Econlib.Probability
