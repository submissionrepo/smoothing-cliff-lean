/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexReduction
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Basic

open Econlib.Probability Finset

/-!
# Concavification and Finite Splitting

By Carathéodory's theorem, any point in the convex hull of a set in `ℝ^d` can be written as a
convex combination of at most `d + 1` points. Applied to Bayesian persuasion, any Bayes-plausible
splitting of a prior can be realized with at most `n + 1` signals, where `n` is the number of types.

## Main statements

* `caratheodory_simplex` — any Bayes-plausible splitting can be reduced to one with at most `n + 1`
  signals achieving the same expected payoff
* `concavification_finite` — the concave closure equals the sup over `(n+1)`-signal splittings

## Tags

persuasion, Carathéodory, splitting, concavification, Bayesian persuasion
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

variable {n : ℕ}

/-- Padding lemma: A sum over `Fin N` with `dite`-based zero padding for indices ≥ `k` equals the
corresponding sum over `Fin k`. -/
lemma sum_dite_pad {k N : ℕ} (hk : k ≤ N) (f : (j : Fin N) → j.val < k → ℝ) :
    ∑ j : Fin N, (if h : j.val < k then f j h else 0) =
    ∑ j : Fin k, f ⟨j.val, by omega⟩ j.isLt := by
  symm
  refine @Finset.sum_of_injOn (Fin k) (Fin N) ℝ _ univ univ
    (fun j => f ⟨j.val, by omega⟩ j.isLt)
    (fun j => if h : j.val < k then f j h else 0)
    (fun j : Fin k => (⟨j.val, by omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
  · intro _ _; simp
  · intro j _ hj
    have : ¬ (j.val < k) := by
      intro hlt; apply hj; exact ⟨⟨j.val, hlt⟩, by simp, Fin.ext rfl⟩
    exact dif_neg this
  · intro j _; simp only [dif_pos j.isLt]

/-- **Carathéodory's theorem for Bayes-plausible splittings.** Any Bayes-plausible splitting of a
prior `μ` into `m` beliefs can be reduced to a splitting with at most `n + 1` beliefs achieving the
same expected value of any function `v`. -/
theorem caratheodory_simplex (μ : FinDist (Fin n)) (v : FinDist (Fin n) → ℝ)
    (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) :
    ∃ (weights' : FinDist (Fin (n + 1))) (beliefs' : Fin (n + 1) → FinDist (Fin n)),
      (∀ i, ∑ s, weights'.pmf s * (beliefs' s).pmf i = μ.pmf i) ∧
      weights'.expect (fun s => v (beliefs' s)) =
        weights.expect (fun s => v (beliefs s)) := by
  -- `FinDist (Fin 0)` is uninhabited since probabilities must sum to 1 over an empty type.
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero => exact absurd μ.sum_one (by simp)
    | succ n' => exact ⟨n', rfl⟩
  -- Lift each belief to a vector in `ℝ^{n'+1}`: the first `n'` coordinates are the pmf values
  -- (dropping the last coordinate, which is determined by the sum-to-one constraint), and the
  -- final coordinate records `v(beliefs s)`. Carathéodory then gives at most `n'+2` points.
  set Y : Fin m → (Fin (n' + 1) → ℝ) :=
    fun s => Fin.snoc (fun i : Fin n' => (beliefs s).pmf (Fin.castSucc i)) (v (beliefs s))
    with hY_def
  obtain ⟨k, hk_le, idx, w', hw'_pos, hw'_sum, hw'_bary⟩ :=
    convex_combination_reduce weights.pmf Y (weights.nonneg) (weights.sum_one)
  have h_coord : ∀ (i : Fin (n' + 1)),
      ∑ j, w' j * Y (idx j) i = ∑ s, weights.pmf s * Y s i := fun i => by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congr_fun hw'_bary i
  have h_pmf_coord : ∀ (i : Fin n'),
      ∑ j, w' j * (beliefs (idx j)).pmf (Fin.castSucc i) =
      ∑ s, weights.pmf s * (beliefs s).pmf (Fin.castSucc i) := fun i => by
    simpa only [hY_def, Fin.snoc_castSucc] using h_coord (Fin.castSucc i)
  have h_val : ∑ j, w' j * v (beliefs (idx j)) =
      ∑ s, weights.pmf s * v (beliefs s) := by
    simpa only [hY_def, Fin.snoc_last] using h_coord (Fin.last n')
  have h_last_coord (d : FinDist (Fin (n' + 1))) :
      d.pmf (Fin.last n') = 1 - ∑ i : Fin n', d.pmf (Fin.castSucc i) := by
    have := d.sum_one; rw [Fin.sum_univ_castSucc] at this; linarith
  have h_bp_last :
      ∑ j, w' j * (beliefs (idx j)).pmf (Fin.last n') = μ.pmf (Fin.last n') := by
    simp_rw [h_last_coord]
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hw'_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [h_pmf_coord i, ← h_bp (Fin.castSucc i)]
  have h_bp_all : ∀ (i : Fin (n' + 1)),
      ∑ j, w' j * (beliefs (idx j)).pmf i = μ.pmf i := by
    intro i; refine Fin.lastCases ?_ ?_ i
    · exact h_bp_last
    · intro i'; rw [h_pmf_coord i', ← h_bp (Fin.castSucc i')]
  set w_pad : Fin (n' + 2) → ℝ :=
    fun j => if h : j.val < k then w' ⟨j.val, h⟩ else 0 with hw_pad_def
  set b_pad : Fin (n' + 2) → FinDist (Fin (n' + 1)) :=
    fun j => if h : j.val < k then beliefs (idx ⟨j.val, h⟩) else μ with hb_pad_def
  have hw_pad_nn : ∀ j, 0 ≤ w_pad j := by
    intro j; simp only [hw_pad_def]
    split_ifs with h
    · exact le_of_lt (hw'_pos ⟨j.val, h⟩)
    · exact le_refl 0
  have hw_pad_sum : ∑ j, w_pad j = 1 := by
    rw [sum_dite_pad hk_le]; exact hw'_sum
  set weights' : FinDist (Fin (n' + 2)) := ⟨w_pad, hw_pad_nn, hw_pad_sum⟩
  have h_bp_pad : ∀ i, ∑ s, weights'.pmf s * (b_pad s).pmf i = μ.pmf i := by
    intro i
    change ∑ s, w_pad s * (b_pad s).pmf i = μ.pmf i
    have h_term : ∀ s : Fin (n' + 2), w_pad s * (b_pad s).pmf i =
        if h : s.val < k then w' ⟨s.val, h⟩ * (beliefs (idx ⟨s.val, h⟩)).pmf i else 0 := by
      intro s
      simp only [hw_pad_def, hb_pad_def]
      split_ifs with h <;> simp [*]
    simp_rw [h_term]
    rw [sum_dite_pad hk_le]
    exact h_bp_all i
  have h_val_pad : weights'.expect (fun s => v (b_pad s)) =
      weights.expect (fun s => v (beliefs s)) := by
    change ∑ s, w_pad s * v (b_pad s) = ∑ s, weights.pmf s * v (beliefs s)
    have h_term : ∀ s : Fin (n' + 2), w_pad s * v (b_pad s) =
        if h : s.val < k then w' ⟨s.val, h⟩ * v (beliefs (idx ⟨s.val, h⟩)) else 0 := by
      intro s
      simp only [hw_pad_def, hb_pad_def]
      split_ifs with h <;> simp [*]
    simp_rw [h_term]
    rw [sum_dite_pad hk_le]
    exact h_val
  exact ⟨weights', b_pad, h_bp_pad, h_val_pad⟩

/-- The set of achievable expected payoffs with `n+1` signals is contained in the set of all
achievable payoffs. -/
lemma finite_splitting_subset (μ : FinDist (Fin n)) (v : FinDist (Fin n) → ℝ) :
    { E | ∃ (weights : FinDist (Fin (n + 1))) (beliefs : Fin (n + 1) → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) }
    ⊆ { E | ∃ (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) } := by
  intro E ⟨weights, beliefs, h_bp, h_E⟩
  exact ⟨n + 1, weights, beliefs, h_bp, h_E⟩

/-- Every achievable expected payoff with arbitrary signals is also achievable with at most `n + 1`
signals. -/
lemma general_splitting_subset_finite (μ : FinDist (Fin n)) (v : FinDist (Fin n) → ℝ) :
    { E | ∃ (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) }
    ⊆ { E | ∃ (weights : FinDist (Fin (n + 1))) (beliefs : Fin (n + 1) → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) } := by
  intro E ⟨m, weights, beliefs, h_bp, h_E⟩
  obtain ⟨w', b', h_bp', h_eq⟩ := caratheodory_simplex μ v m weights beliefs h_bp
  exact ⟨w', b', h_bp', by rw [h_E, h_eq]⟩

/-- **Concavification with finitely many signals.** The concave closure equals the supremum over
splittings with at most `n + 1` signals. This reduces the sender's optimization from an
infinite-dimensional problem to a finite one. -/
theorem concavification_finite (μ : FinDist (Fin n)) (v : FinDist (Fin n) → ℝ) :
    concaveClosure v μ = sSup { E |
      ∃ (weights : FinDist (Fin (n + 1))) (beliefs : Fin (n + 1) → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) } := by
  unfold concaveClosure
  congr 1
  exact Set.Subset.antisymm
    (general_splitting_subset_finite μ v)
    (finite_splitting_subset μ v)

/-- Any achievable expected payoff can also be achieved with `n+1` signals. -/
theorem achievable_with_bounded_signals (μ : FinDist (Fin n)) (v : FinDist (Fin n) → ℝ)
    (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) :
    ∃ (weights' : FinDist (Fin (n + 1))) (beliefs' : Fin (n + 1) → FinDist (Fin n)),
      (∀ i, ∑ s, weights'.pmf s * (beliefs' s).pmf i = μ.pmf i) ∧
      weights'.expect (fun s => v (beliefs' s)) =
        weights.expect (fun s => v (beliefs s)) :=
  caratheodory_simplex μ v m weights beliefs h_bp

end Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
