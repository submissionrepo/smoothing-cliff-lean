/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Powerset sum identity for Bernoulli trials

This file proves the powerset-sum identity underlying the binomial distribution construction: A sum
over all subsets of `Fin n`, weighted by `p^|S| · (1-p)^{n-|S|}` and depending only on `|S|`,
collapses to a binomial-weighted sum over the cardinality.

## Main statements

* `Finset.powerset_bern_sum` — the powerset sum equals the binomial-weighted sum over cardinalities.

## Tags

combinatorics, powerset, binomial coefficient, bernoulli
-/

@[expose] public section

namespace Finset

/-- Summing a function of subset cardinality over all subsets of `Fin n`, weighted by
`p^|S| · (1-p)^{n-|S|}`, equals the binomial-weighted sum `∑_k C(n,k) p^k (1-p)^{n-k} · f(k)`. -/
theorem powerset_bern_sum (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      p ^ S.card * (1 - p) ^ (n - S.card) * f S.card =
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) * f k := by
  -- Decompose powerset sum by cardinality
  rw [Finset.sum_powerset, show (Finset.univ : Finset (Fin n)).card = n from by simp]
  apply Finset.sum_congr rfl; intro k hk
  -- Each S ∈ powersetCard k has card = k, so all summands are equal
  have : ∀ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
      p ^ S.card * (1 - p) ^ (n - S.card) * f S.card =
      p ^ k * (1 - p) ^ (n - k) * f k := by
    intro S hS; rw [(Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Finset
