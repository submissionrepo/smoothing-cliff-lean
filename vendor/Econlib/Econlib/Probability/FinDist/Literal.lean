/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Literal constructors for finite distributions

This file provides ergonomic constructors for finite distributions from probability-mass functions,
especially concrete vectors indexed by `Fin n`.

## Main definitions

* `FinDist.ofFn`: Construct a finite distribution from a finite pmf and its two probability
  obligations.
* `FinDist.ofVec`: The `Fin n`-specialized constructor used with vector notation.
* `finDist% ![...]`: Term syntax that constructs a `FinDist (Fin n)` and tries to discharge the
  nonnegativity and total-mass obligations by computation and arithmetic.

## Tags

probability, finite distributions, literals
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Construct a finite distribution from a pmf, pointwise nonnegativity, and total mass one. -/
def ofFn (p : α → ℝ) (h_nonneg : ∀ a, 0 ≤ p a) (h_sum : ∑ a, p a = 1) :
    FinDist α where
  pmf := p
  nonneg := h_nonneg
  sum_one := h_sum

/-- Construct a `FinDist (Fin n)` from a vector-shaped pmf. -/
def ofVec {n : ℕ} (p : Fin n → ℝ) (h_nonneg : ∀ i, 0 ≤ p i)
    (h_sum : ∑ i, p i = 1) : FinDist (Fin n) :=
  FinDist.ofFn p h_nonneg h_sum

/-- The pmf of `ofFn p _ _` is `p`. -/
@[simp] lemma ofFn_pmf (p : α → ℝ) (h_nonneg : ∀ a, 0 ≤ p a)
    (h_sum : ∑ a, p a = 1) :
    (FinDist.ofFn p h_nonneg h_sum).pmf = p :=
  rfl

/-- Evaluating `ofFn p _ _` at `a` gives `p a`. -/
@[simp] lemma ofFn_apply (p : α → ℝ) (h_nonneg : ∀ a, 0 ≤ p a)
    (h_sum : ∑ a, p a = 1) (a : α) :
    FinDist.ofFn p h_nonneg h_sum a = p a :=
  rfl

/-- The pmf of `ofVec p _ _` is `p`. -/
@[simp] lemma ofVec_pmf {n : ℕ} (p : Fin n → ℝ) (h_nonneg : ∀ i, 0 ≤ p i)
    (h_sum : ∑ i, p i = 1) :
    (FinDist.ofVec p h_nonneg h_sum).pmf = p :=
  rfl

/-- Evaluating `ofVec p _ _` at `i` gives `p i`. -/
@[simp] lemma ofVec_apply {n : ℕ} (p : Fin n → ℝ) (h_nonneg : ∀ i, 0 ≤ p i)
    (h_sum : ∑ i, p i = 1) (i : Fin n) :
    FinDist.ofVec p h_nonneg h_sum i = p i :=
  rfl

end FinDist
end Econlib.Probability

/-- Simplify concrete `Fin` vectors and finite sums over them. -/
syntax "fin_dist_simp" : tactic

macro_rules
  | `(tactic| fin_dist_simp) =>
      `(tactic|
        simp [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
          Matrix.head_cons, Matrix.tail_cons])

/-- Discharge routine probability-vector obligations for concrete `Fin` literals. -/
syntax "fin_dist_norm" : tactic

macro_rules
  | `(tactic| fin_dist_norm) =>
      `(tactic|
        (try fin_dist_simp) <;>
          solve
          | positivity
          | norm_num
          | linarith
          | nlinarith
          | ring_nf <;> solve | norm_num | linarith | nlinarith | positivity
          | ring_nf)

/-- Construct a `FinDist (Fin n)` from a concrete vector literal, discharging routine probability
obligations by `fin_dist_norm`.

Examples:

```lean
let d : FinDist (Fin 3) := finDist% ![(1 : ℝ) / 2, 1 / 3, 1 / 6]
``` -/
syntax "finDist% " term : term

macro_rules
  | `(finDist% $p:term) =>
      `(Econlib.Probability.FinDist.ofVec $p
          (by
            intro i
            fin_cases i <;> fin_dist_norm)
          (by
            fin_dist_norm))
