/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.Basic

/-!
# Finite Markov histories

A **history** of length `t+1` for a chain on `α` is a function `Fin (t + 1) → α` listing the
chain's path through `t+1` consecutive states. This module provides combinatorial navigation on
histories — `head`, `lastNode`, `tail`, `extend` — together with the **path probability** of a
history under a finite Markov chain and its factorization over extension.

## Main definitions

* `History α t` — a length-`t+1` history of states for a chain on `α`
* `History.head`, `History.lastNode`, `History.tail`, `History.extend` — navigation on histories
* `pathProb` — the Markov path probability of a history

## Main statements

* `pathProb_extend` — the path probability factors over a one-state extension
* `sum_pathProb_extend` — summing over the appended state recovers the prefix's path probability

## Tags

markov chain, history, path probability
-/

@[expose] public section

open BigOperators Finset

namespace Econlib.Probability

/-- A length-`t+1` history of states for a chain on `α`. -/
abbrev History (α : Type*) (t : ℕ) : Type _ := Fin (t + 1) → α

namespace History

variable {α : Type*}

/-- The first node of a history. -/
def head {t : ℕ} (h : History α t) : α := h 0

/-- The last node of a length-`t+1` history. -/
def lastNode {t : ℕ} (h : History α t) : α := h (Fin.last t)

/-- Drop the last node of a length-`t+2` history, producing a length-`t+1` prefix. -/
def tail {t : ℕ} (h : History α (t + 1)) : History α t :=
  fun i => h i.castSucc

/-- Extend a history by one additional state, producing a length-`t+2` history. -/
def extend {t : ℕ} (h : History α t) (s' : α) : History α (t + 1) :=
  Fin.snoc h s'

/-- The first node is preserved by extension. -/
@[simp] theorem head_extend {t : ℕ} (h : History α t) (s' : α) :
    (extend h s').head = h.head := by
  simp [extend, head]

/-- The last node of an extension is the new state. -/
@[simp] theorem lastNode_extend {t : ℕ} (h : History α t) (s' : α) :
    (extend h s').lastNode = s' := by
  unfold extend lastNode
  simp

/-- The prefix of an extension is the original history. -/
@[simp] theorem tail_extend {t : ℕ} (h : History α t) (s' : α) :
    (extend h s').tail = h := by
  funext i
  unfold extend tail
  simp

end History

/-! ## Path probabilities -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Markov path probability of a history of length `t+1`. The initial state's marginal weight
is `1` (treated as conditioning data); each transition contributes a factor `P(h k → h (k + 1))`. -/
noncomputable def pathProb (P : FiniteMarkovChain α) {t : ℕ}
    (h : History α t) : ℝ :=
  ∏ k : Fin t, (P.transition (h k.castSucc)) (h k.succ)

/-- Path probabilities are nonnegative. -/
theorem pathProb_nonneg (P : FiniteMarkovChain α) {t : ℕ} (h : History α t) :
    0 ≤ pathProb P h :=
  Finset.prod_nonneg fun _ _ => (P.transition _).nonneg _

/-- A length-1 history has unit path probability — only the initial state is named. -/
@[simp] theorem pathProb_zero (P : FiniteMarkovChain α) (h : History α 0) :
    pathProb P h = 1 := by
  unfold pathProb
  simp

/-- Path probability factors over an extension. -/
theorem pathProb_extend (P : FiniteMarkovChain α) {t : ℕ}
    (h : History α t) (s' : α) :
    pathProb P (h.extend s') =
      pathProb P h * (P.transition h.lastNode) s' := by
  unfold pathProb History.extend History.lastNode
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- Summing the path probability over the appended state recovers the prefix's path probability. -/
theorem sum_pathProb_extend (P : FiniteMarkovChain α) {t : ℕ}
    (h : History α t) :
    ∑ s' : α, pathProb P (h.extend s') = pathProb P h := by
  simp_rw [pathProb_extend, ← Finset.mul_sum, (P.transition h.lastNode).sum_one,
    mul_one]

end Econlib.Probability
