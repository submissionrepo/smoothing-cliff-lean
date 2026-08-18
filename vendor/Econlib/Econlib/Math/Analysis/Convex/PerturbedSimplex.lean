/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# ε-perturbed standard simplex slice

The slice of the standard simplex whose coordinates are all bounded below by `ε`:
`{x ∈ stdSimplex ℝ α | ∀ a, ε ≤ x a}`. This is the fully-mixed slice used in trembling-hand
constructions, but it is a purely geometric object.

## Main definitions

* `PerturbedSimplex` — the slice `stdSimplex ℝ α ∩ {x | ∀ a, ε ≤ x a}`.

## Main results

* `convex_PerturbedSimplex` — convexity of the slice.
* `isCompact_PerturbedSimplex` — compactness of the slice.
* `nonempty_PerturbedSimplex_of_le_inv` — nonemptiness for `ε ≤ 1 / |α|`, witnessed by the uniform
  distribution.

## Tags

standard simplex, perturbation, convex, compact
-/

@[expose] public section

variable {α : Type*} [Fintype α]

/-- The ε-perturbed simplex slice: Distributions in the standard simplex whose entries are all at
least `ε`. For `ε ≤ 1 / |α|` this is non-empty (uniform distribution). For `ε > 1 / |α|` it is
empty (no distribution has every entry above the average). -/
def PerturbedSimplex (ε : ℝ) : Set (α → ℝ) :=
  stdSimplex ℝ α ∩ {x | ∀ a, ε ≤ x a}

/-- The ε-perturbed simplex slice is convex. -/
lemma convex_PerturbedSimplex (ε : ℝ) : Convex ℝ (PerturbedSimplex (α := α) ε) := by
  refine (convex_stdSimplex ℝ α).inter ?_
  intro x hx y hy a b ha hb hab i
  have hxi : ε ≤ x i := hx i
  have hyi : ε ≤ y i := hy i
  -- ε = (a+b)ε ≤ a·x i + b·y i since the convex weights sum to one and each coordinate ≥ ε.
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hεab : ε = a * ε + b * ε := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hxi ha, mul_le_mul_of_nonneg_left hyi hb]

/-- The ε-perturbed simplex slice is compact. -/
lemma isCompact_PerturbedSimplex (ε : ℝ) : IsCompact (PerturbedSimplex (α := α) ε) := by
  refine (isCompact_stdSimplex ℝ α).inter_right ?_
  have h_eq : {x : α → ℝ | ∀ a, ε ≤ x a} = ⋂ a : α, {x : α → ℝ | ε ≤ x a} := by
    ext x; simp [Set.mem_iInter]
  rw [h_eq]
  refine isClosed_iInter (fun a => ?_)
  exact isClosed_le continuous_const (continuous_apply a)

/-- For `ε ≤ 1 / |α|` the ε-perturbed simplex slice is non-empty, witnessed by the uniform
distribution. -/
lemma nonempty_PerturbedSimplex_of_le_inv [Nonempty α]
    -- `_hε_nn` is unused in the proof but is part of the intended use contract: callers should
    -- only invoke this lemma for non-negative `ε`.
    {ε : ℝ} (_hε_nn : 0 ≤ ε) (hε : ε ≤ 1 / (Fintype.card α : ℝ)) :
    (PerturbedSimplex (α := α) ε).Nonempty := by
  refine ⟨fun _ => 1 / (Fintype.card α : ℝ), ?_, fun _ => hε⟩
  have hcard_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => div_nonneg (by norm_num) hcard_pos.le, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
