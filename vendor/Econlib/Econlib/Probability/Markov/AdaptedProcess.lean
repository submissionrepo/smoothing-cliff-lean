/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.History

/-!
# Adapted processes over a finite Markov chain

An **adapted process** `AdaptedProcess α` is a sequence `val t : History α t → ℝ` whose value at
time `t` depends only on the chain's path through time `t+1`. The `condExpStep` operator computes
the one-step conditional expectation along the natural filtration of the chain, and the
`iterCondExp` family iterates it `k` times. Both operators preserve uniform bounds, nonnegativity,
and monotonicity in the underlying payoff.

## Main definitions

* `AdaptedProcess α` — a real-valued process adapted to the natural filtration of a finite chain
* `AdaptedProcess.Bounded`, `AdaptedProcess.Nonneg`, `AdaptedProcess.const` — basic predicates and
  the constant process
* `AdaptedProcess.condExpStep` — one-step conditional expectation along a history
* `iterCondExp` — the `k`-fold iterated conditional expectation

## Main statements

* `AdaptedProcess.condExpStep_const`, `AdaptedProcess.condExpStep_mono`,
  `AdaptedProcess.condExpStep_bounded`, `AdaptedProcess.condExpStep_nonneg` — the one-step operator
  fixes constants and preserves monotonicity, uniform bounds, and nonnegativity
* `iterCondExp_bounded`, `iterCondExp_nonneg`, `iterCondExp_mono` — the iterated operator preserves
  uniform bounds, nonnegativity, and monotonicity

## Tags

markov chain, adapted process, filtration, conditional expectation
-/

@[expose] public section

open BigOperators Finset

namespace Econlib.Probability

/-- A real-valued process adapted to the natural filtration of a finite Markov chain on `α`. -/
structure AdaptedProcess (α : Type*) where
  /-- Value of the process at history `h` of length `t+1`. -/
  val : (t : ℕ) → History α t → ℝ

namespace AdaptedProcess

variable {α : Type*}

/-- The process is uniformly bounded by `M`. -/
def Bounded (X : AdaptedProcess α) (M : ℝ) : Prop :=
  ∀ (t : ℕ) (h : History α t), |X.val t h| ≤ M

/-- The process is everywhere nonnegative. -/
def Nonneg (X : AdaptedProcess α) : Prop :=
  ∀ (t : ℕ) (h : History α t), 0 ≤ X.val t h

/-- The constant adapted process at value `c`. -/
def const (c : ℝ) : AdaptedProcess α :=
  ⟨fun _ _ => c⟩

/-- The constant process takes the value `c` at every history. -/
@[simp] theorem const_val (c : ℝ) (t : ℕ) (h : History α t) :
    (const (α := α) c).val t h = c := rfl

end AdaptedProcess

/-! ## Conditional expectation along the chain -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One-step conditional expectation along a history.  Given the chain's path through time `t+1`,
integrate the next-period value of `X` against the transition out of `h.lastNode`. -/
noncomputable def AdaptedProcess.condExpStep
    (P : FiniteMarkovChain α) (X : AdaptedProcess α)
    (t : ℕ) (h : History α t) : ℝ :=
  ∑ s' : α, (P.transition h.lastNode) s' * X.val (t + 1) (h.extend s')

namespace AdaptedProcess

variable (P : FiniteMarkovChain α)

/-- The one-step conditional expectation of a constant process is that constant. -/
theorem condExpStep_const (c : ℝ) (t : ℕ) (h : History α t) :
    (AdaptedProcess.const (α := α) c).condExpStep P t h = c := by
  unfold AdaptedProcess.condExpStep
  simp_rw [const_val, ← Finset.sum_mul, (P.transition h.lastNode).sum_one, one_mul]

/-- One-step conditional expectation is monotone. -/
theorem condExpStep_mono {X Y : AdaptedProcess α}
    (hXY : ∀ t (h : History α t), X.val t h ≤ Y.val t h)
    (t : ℕ) (h : History α t) :
    X.condExpStep P t h ≤ Y.condExpStep P t h := by
  unfold AdaptedProcess.condExpStep
  refine Finset.sum_le_sum fun s' _ => ?_
  exact mul_le_mul_of_nonneg_left (hXY _ _) ((P.transition h.lastNode).nonneg s')

/-- A `FinDist`-weighted average of values each bounded by `M` in absolute value is itself bounded
by `M`. -/
private theorem _root_.Econlib.Probability.FinDist.abs_sum_mul_le
    {p : FinDist α} {f : α → ℝ} {M : ℝ} (hf : ∀ s', |f s'| ≤ M) :
    |∑ s' : α, p s' * f s'| ≤ M :=
  calc |∑ s' : α, p s' * f s'|
      ≤ ∑ s' : α, |p s' * f s'| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s' : α, p s' * |f s'| := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (p.nonneg s')]
    _ ≤ ∑ s' : α, p s' * M :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hf s') (p.nonneg s')
    _ = M := by rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- One-step conditional expectation preserves uniform bounds. -/
theorem condExpStep_bounded {X : AdaptedProcess α} {M : ℝ}
    (hX : X.Bounded M) (t : ℕ) (h : History α t) :
    |X.condExpStep P t h| ≤ M :=
  FinDist.abs_sum_mul_le fun _ => hX _ _

/-- One-step conditional expectation preserves nonnegativity. -/
theorem condExpStep_nonneg {X : AdaptedProcess α}
    (hX : X.Nonneg) (t : ℕ) (h : History α t) :
    0 ≤ X.condExpStep P t h := by
  unfold AdaptedProcess.condExpStep
  refine Finset.sum_nonneg fun s' _ => ?_
  exact mul_nonneg ((P.transition h.lastNode).nonneg s') (hX _ _)

end AdaptedProcess

/-- Iterated conditional expectation: `iterCondExp P X k t h` is the conditional expectation of
`X.val (t+k)` integrated over the next `k` shocks. -/
noncomputable def iterCondExp (P : FiniteMarkovChain α) (X : AdaptedProcess α) :
    ℕ → (t : ℕ) → History α t → ℝ
  | 0,     t, h => X.val t h
  | k+1,   t, h => ∑ s' : α, (P.transition h.lastNode) s' *
      iterCondExp P X k (t + 1) (h.extend s')

/-- Zero iterations return the underlying value. -/
@[simp] theorem iterCondExp_zero (P : FiniteMarkovChain α) (X : AdaptedProcess α)
    (t : ℕ) (h : History α t) :
    iterCondExp P X 0 t h = X.val t h := rfl

/-- One more iteration integrates the `k`-fold value against the transition out of `h.lastNode`. -/
theorem iterCondExp_succ (P : FiniteMarkovChain α) (X : AdaptedProcess α)
    (k t : ℕ) (h : History α t) :
    iterCondExp P X (k + 1) t h =
      ∑ s' : α, (P.transition h.lastNode) s' *
        iterCondExp P X k (t + 1) (h.extend s') := rfl

/-- Iterated conditional expectation of a bounded process is uniformly bounded by the same
constant. -/
theorem iterCondExp_bounded (P : FiniteMarkovChain α) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) (k t : ℕ) (h : History α t) :
    |iterCondExp P X k t h| ≤ M := by
  induction k generalizing t h with
  | zero => exact hX t h
  | succ k ih =>
    rw [iterCondExp_succ]
    exact FinDist.abs_sum_mul_le fun s' => ih (t + 1) (h.extend s')

/-- Iterated conditional expectation preserves nonnegativity. -/
theorem iterCondExp_nonneg (P : FiniteMarkovChain α) (X : AdaptedProcess α)
    (hX : X.Nonneg) (k t : ℕ) (h : History α t) :
    0 ≤ iterCondExp P X k t h := by
  induction k generalizing t h with
  | zero => exact hX t h
  | succ k ih =>
    rw [iterCondExp_succ]
    refine Finset.sum_nonneg fun s' _ => ?_
    exact mul_nonneg ((P.transition h.lastNode).nonneg s') (ih _ _)

/-- Iterated conditional expectation is monotone in the underlying payoff. -/
theorem iterCondExp_mono (P : FiniteMarkovChain α) {X Y : AdaptedProcess α}
    (hXY : ∀ t (h : History α t), X.val t h ≤ Y.val t h)
    (k t : ℕ) (h : History α t) :
    iterCondExp P X k t h ≤ iterCondExp P Y k t h := by
  induction k generalizing t h with
  | zero => exact hXY t h
  | succ k ih =>
    rw [iterCondExp_succ, iterCondExp_succ]
    refine Finset.sum_le_sum fun s' _ => ?_
    exact mul_le_mul_of_nonneg_left (ih _ _) ((P.transition h.lastNode).nonneg s')

end Econlib.Probability
