/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.FinCases

/-!
# Permutations and the complement on `Fin 2`

Elementary combinatorics of the two-element type `Fin 2`: The complement function `otherFin2`
(swapping `0` and `1`), the swap permutation `swapFin2 = Equiv.swap 0 1`, and the fact that the
only two permutations of `Fin 2` are the identity and `swapFin2`.

These are pure-combinatorial facts (no order/economic content). They support the two-alternative
social-choice development (May's theorem), where `otherFin2` names "the other alternative" and
`swapFin2` is the alternative-relabeling permutation in the neutrality axiom.

`otherFin2` agrees pointwise with `Fin.rev` on `Fin 2` (`Fin.rev 0 = 1`, `Fin.rev 1 = 0`), but is
kept as an explicit `if`-based definition for computational transparency.

## Main definitions

* `otherFin2` — the complement of an element of `Fin 2`.
* `swapFin2` — the permutation of `Fin 2` swapping the two elements.

## Main results

* `otherFin2_otherFin2` — `otherFin2` is an involution.
* `swapFin2_apply` — `swapFin2` agrees with `otherFin2`.
* `perm_fin2_eq` — every permutation of `Fin 2` is the identity or `swapFin2`.
* `sum_piFinTwo` — a sum over functions `Fin 2 → α` is the iterated sum over the two coordinate
  values, summing `f ![a, b]`.

## Tags

Fin 2, permutation, swap, complement
-/

@[expose] public section

/-- The "other" element on `Fin 2`. -/
def otherFin2 (a : Fin 2) : Fin 2 :=
  if a = 0 then 1 else 0

@[simp] lemma otherFin2_zero : otherFin2 0 = 1 := by simp [otherFin2]
@[simp] lemma otherFin2_one : otherFin2 1 = 0 := by simp [otherFin2]
@[simp] lemma otherFin2_otherFin2 (a : Fin 2) : otherFin2 (otherFin2 a) = a := by
  fin_cases a <;> simp [otherFin2]
@[simp] lemma otherFin2_ne (a : Fin 2) : otherFin2 a ≠ a := by
  fin_cases a <;> decide

/-- On `Fin 2`, the only off-diagonal ordered pairs are `(w, otherFin2 w)` and `(otherFin2 w, w)`,
so any pair excluded from both is reflexive. -/
lemma fin2_eq_of_not_cross {w o a b : Fin 2} (ho : o = otherFin2 w)
    (h1 : ¬ (a = w ∧ b = o)) (h2 : ¬ (a = o ∧ b = w)) : a = b := by
  subst ho; fin_cases w <;> fin_cases a <;> fin_cases b <;> simp_all [otherFin2]

/-- The permutation of `Fin 2` swapping the two elements. -/
def swapFin2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

lemma swapFin2_apply_zero : swapFin2 0 = 1 := by simp [swapFin2]
lemma swapFin2_apply_one : swapFin2 1 = 0 := by simp [swapFin2]

lemma swapFin2_apply (a : Fin 2) : swapFin2 a = otherFin2 a := by
  fin_cases a <;> simp [swapFin2, otherFin2]

lemma swapFin2_symm_apply (a : Fin 2) : swapFin2.symm a = otherFin2 a := by
  fin_cases a <;> simp [swapFin2, otherFin2]

/-- Every permutation of `Fin 2` is either the identity or `swapFin2`. -/
lemma perm_fin2_eq (τ : Equiv.Perm (Fin 2)) : τ = 1 ∨ τ = swapFin2 := by
  have hne01 : τ 1 ≠ τ 0 := fun h => by simpa using τ.injective h
  have fin2cases : ∀ z : Fin 2, z = 0 ∨ z = 1 := by decide
  have h0cases : τ 0 = 0 ∨ τ 0 = 1 := fin2cases _
  have h1cases : τ 1 = 0 ∨ τ 1 = 1 := fin2cases _
  rcases h0cases with h0 | h0
  · left
    have h1 : τ 1 = 1 := by rcases h1cases with h1 | h1 <;> simp_all
    ext a; fin_cases a <;> simp [Equiv.Perm.one_apply, h0, h1]
  · right
    have h1 : τ 1 = 0 := by rcases h1cases with h1 | h1 <;> simp_all
    ext a; fin_cases a <;> simp [swapFin2, h0, h1]

/-- A sum over functions `Fin 2 → α` decomposes as the iterated sum over the two coordinate values:
Transport the function-type sum along `piFinTwoEquiv : (Fin 2 → α) ≃ α × α`, split the product sum
with `Fintype.sum_prod_type`, and identify the transported point `(a, b)` with the vector literal
`![a, b]`. -/
lemma sum_piFinTwo {α M : Type*} [Fintype α] [AddCommMonoid M] (f : (Fin 2 → α) → M) :
    ∑ s : Fin 2 → α, f s = ∑ a, ∑ b, f ![a, b] := by
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => α)).symm.sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- `(piFinTwoEquiv α).symm (a, b)` is `Fin.cons a (Fin.cons b finZeroElim)`, defeq to `![a, b]`,
  -- so `congr 1` reduces to the (definitional) argument equality and closes the goal.
  congr 1
