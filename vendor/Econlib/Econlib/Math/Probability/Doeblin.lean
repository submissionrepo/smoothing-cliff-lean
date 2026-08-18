/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.Analysis.RCLike.Basic

/-!
# Doeblin-type total-variation contraction

A row-stochastic matrix `P` on a finite index type `α` whose entries are all at least `ε > 0`
contracts the total variation (L¹) distance `½ Σᵢ |μᵢ - νᵢ|` between any two equal-mass signed
vectors `μ, ν : α → ℝ` by the factor `1 - card·ε` per step; iterating gives `(1 - card·ε)ᵏ`. This
is the quantitative analytic core behind the Doeblin contraction argument.

The contraction lemmas assume only that `μ` and `ν` have equal total mass (`∑ μ = ∑ ν`); they do
not require nonnegativity or normalization, so they hold for arbitrary equal-mass signed vectors
and not only for probability distributions. No stationary existence, uniqueness, or
geometric-convergence theorem is proved in this file; those consequences require the additional
probability-distribution structure and are not developed here.

Everything is stated over an arbitrary finite index type `α` (`[Fintype α]`), so it applies to a
chain on any finite state space, not just `Fin n`.

## Main definitions

* `tvDist` — the total variation distance `½ Σᵢ |μᵢ - νᵢ|` between two vectors `μ, ν : α → ℝ`.

## Main statements

* `tvDist_step_le` — one step contracts TV distance by `1 - card·ε`, where `ε` lower-bounds every
  entry of `P`, for any two equal-mass vectors.
* `tvDist_nStep_le` — `k` steps contract by `(1 - card·ε)ᵏ`.

## Tags

doeblin condition, total variation, contraction, stochastic matrix, equal mass
-/

@[expose] public section

open Finset BigOperators

namespace MeasureTheory

/-! ## Total Variation Distance -/

/-- Total variation distance between two vectors `μ ν : α → ℝ` on a finite type `α`:
`TV(μ, ν) = ½ Σᵢ |μᵢ - νᵢ|`.

When `μ` and `ν` are probability vectors this equals `sup_A |μ(A) - ν(A)|` and metrizes convergence
in distribution on finite spaces, but the definition itself is the scaled L¹ distance for arbitrary
real vectors. -/
noncomputable def tvDist {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |μ i - ν i|

/-- The total variation distance is nonnegative. -/
lemma tvDist_nonneg {α : Type*} [Fintype α] (μ ν : α → ℝ) :
    0 ≤ tvDist μ ν := by
  unfold tvDist
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- The total variation distance of a vector from itself is zero. -/
lemma tvDist_self {α : Type*} [Fintype α] (μ : α → ℝ) :
    tvDist μ μ = 0 := by
  simp [tvDist]

/-- The total variation distance is symmetric. -/
lemma tvDist_comm {α : Type*} [Fintype α] (μ ν : α → ℝ) :
    tvDist μ ν = tvDist ν μ := by
  simp [tvDist, abs_sub_comm]

/-- The total variation distance vanishes if and only if the two vectors are equal. -/
lemma tvDist_eq_zero_iff {α : Type*} [Fintype α] {μ ν : α → ℝ} :
    tvDist μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    unfold tvDist at h
    -- The half-sum of nonnegatives vanishes, so each `|μ i - ν i|` does.
    have hsum : ∑ i, |μ i - ν i| = 0 := by
      nlinarith [Finset.sum_nonneg
        (fun i (_ : i ∈ Finset.univ) => abs_nonneg (μ i - ν i))]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => abs_nonneg (μ i - ν i))).mp hsum
    ext i
    have := abs_eq_zero.mp (hzero i (Finset.mem_univ i))
    linarith
  · intro h; subst h; exact tvDist_self μ

/-! ## Doeblin Contraction -/

/-- **Doeblin contraction.** For a row-stochastic matrix `P` on a finite type `α` whose entries are
all at least `ε > 0`, and any two equal-mass vectors `μ ν : α → ℝ`, one push-forward step contracts
TV distance:

`TV(P μ, P ν) ≤ (1 - card·ε) · TV(μ, ν)`

where `(Pμ)(s') = Σ_s μ(s) P(s, s')`. Equal mass (`∑ μ = ∑ ν`) makes the shared `ε`-mass component
cancel, leaving the factor `1 - card·ε`. Nonnegativity and normalization of `μ`, `ν` are not
required. -/
theorem tvDist_step_le {α : Type*} [Fintype α]
    (P : α → α → ℝ)
    -- Part of "P is row-stochastic"; the proof only uses hP_min (ε ≤ P s s'), which subsumes it.
    (_hP_nn : ∀ s s', 0 ≤ P s s')
    (hP_sum : ∀ s, ∑ s', P s s' = 1)
    -- Part of the Doeblin-coefficient contract; the proof only uses hP_min, not ε > 0 itself.
    (ε : ℝ) (_hε : 0 < ε)
    (hP_min : ∀ s s', ε ≤ P s s')
    (μ ν : α → ℝ)
    (hμν : ∑ s, μ s = ∑ s, ν s) :
    tvDist (fun s' => ∑ s, μ s * P s s')
           (fun s' => ∑ s, ν s * P s s') ≤
      (1 - Fintype.card α * ε) * tvDist μ ν := by
  -- Decompose P(s,s') = ε + Q(s,s') where Q ≥ 0 and ∑ Q = 1 - card·ε.
  -- The ε component vanishes (∑(μ-ν) = 0), leaving exactly the factor (1 - card·ε).
  unfold tvDist
  rw [show (1 - Fintype.card α * ε) * ((1 / 2) * ∑ i, |μ i - ν i|) =
      (1 / 2) * ((1 - Fintype.card α * ε) * ∑ i, |μ i - ν i|) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- Combine sums in the difference
  have hdiff : ∀ s' : α, (∑ s, μ s * P s s') - (∑ s, ν s * P s s') =
      ∑ s, (μ s - ν s) * P s s' := by
    intro s'; rw [← Finset.sum_sub_distrib]; congr 1; ext s; ring
  simp_rw [hdiff]
  -- Key fact: ∑(μ - ν) = 0
  have h_zero : ∑ s : α, (μ s - ν s) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  -- Replace P s s' by (P s s' - ε) using the zero-sum property
  have hdecomp : ∀ s' : α, ∑ s, (μ s - ν s) * P s s' =
      ∑ s, (μ s - ν s) * (P s s' - ε) := by
    intro s'
    have : ∑ s, (μ s - ν s) * P s s' =
        (∑ s, (μ s - ν s) * (P s s' - ε)) + ε * ∑ s, (μ s - ν s) := by
      rw [Finset.mul_sum]; simp_rw [mul_comm ε]; rw [← Finset.sum_add_distrib]
      congr 1; ext s; ring
    rw [this, h_zero, mul_zero, add_zero]
  simp_rw [hdecomp]
  -- Residual sum: ∑_{s'} (P s s' - ε) = 1 - card·ε
  have hQ_sum : ∀ s : α, ∑ s', (P s s' - ε) = 1 - ↑(Fintype.card α) * ε := by
    intro s
    rw [Finset.sum_sub_distrib, hP_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Main calculation via triangle inequality
  calc ∑ s', |∑ s, (μ s - ν s) * (P s s' - ε)|
      ≤ ∑ s', ∑ s, |(μ s - ν s) * (P s s' - ε)| := by
        apply Finset.sum_le_sum; intro s' _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', ∑ s, |μ s - ν s| * (P s s' - ε) := by
        congr 1; ext s'; congr 1; ext s
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hP_min s s'))]
    _ = ∑ s, |μ s - ν s| * ∑ s', (P s s' - ε) := by
        rw [Finset.sum_comm]; congr 1; ext s; rw [← Finset.mul_sum]
    _ = ∑ s, |μ s - ν s| * (1 - ↑(Fintype.card α) * ε) := by
        congr 1; ext s; rw [hQ_sum]
    _ = (1 - Fintype.card α * ε) * ∑ s, |μ s - ν s| := by
        rw [Finset.mul_sum]; congr 1; ext s; ring

/-- The step operator of a stochastic matrix preserves total mass: `Σ_{s'} (P d)(s') = Σ_s d s`. -/
private lemma step_sum_eq {α : Type*} [Fintype α] (P : α → α → ℝ)
    (hP_sum : ∀ s, ∑ s', P s s' = 1) (d : α → ℝ) :
    ∑ s', (∑ s, d s * P s s') = ∑ s, d s := by
  rw [Finset.sum_comm]; congr 1; ext s
  rw [← Finset.mul_sum, hP_sum, mul_one]

/-- **Iterated Doeblin contraction.** `k` push-forward steps of a row-stochastic matrix whose
entries are all at least `ε > 0`, applied to two equal-mass vectors, contract TV distance by
`(1 - card·ε)ᵏ`. -/
theorem tvDist_nStep_le {α : Type*} [Fintype α]
    (P : α → α → ℝ)
    (hP_nn : ∀ s s', 0 ≤ P s s')
    (hP_sum : ∀ s, ∑ s', P s s' = 1)
    (ε : ℝ) (hε : 0 < ε)
    (hP_min : ∀ s s', ε ≤ P s s')
    (k : ℕ) (μ ν : α → ℝ)
    (hμν : ∑ s, μ s = ∑ s, ν s) :
    tvDist
      (Nat.iterate (fun d s' => ∑ s, d s * P s s') k μ)
      (Nat.iterate (fun d s' => ∑ s, d s * P s s') k ν) ≤
      (1 - Fintype.card α * ε) ^ k * tvDist μ ν := by
  -- Stochasticity forces `card·ε ≤ 1`, so the contraction factor lies in `[0,1]`.
  have hcard_le : (Fintype.card α : ℝ) * ε ≤ 1 := by
    rcases isEmpty_or_nonempty α with he | hne
    · haveI := he; simp [Fintype.card_eq_zero]
    · obtain ⟨s⟩ := hne
      calc (Fintype.card α : ℝ) * ε
          = ∑ _s' : α, ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ ∑ s', P s s' := Finset.sum_le_sum (fun s' _ => hP_min s s')
        _ = 1 := hP_sum s
  induction k with
  | zero => simp [tvDist]
  | succ k ih =>
    -- The step preserves equal sums
    have hiter_sum : ∀ m, ∑ s, Nat.iterate (fun d s' => ∑ s, d s * P s s') m μ s =
        ∑ s, Nat.iterate (fun d s' => ∑ s, d s * P s s') m ν s := by
      intro m; induction m with
      | zero => simp [hμν]
      | succ m ihm =>
        simp only [Function.iterate_succ', Function.comp_def]
        rw [step_sum_eq P hP_sum, step_sum_eq P hP_sum]; exact ihm
    simp only [Function.iterate_succ']
    calc tvDist _ _ ≤ (1 - Fintype.card α * ε) * tvDist
          (Nat.iterate _ k μ) (Nat.iterate _ k ν) :=
        tvDist_step_le P hP_nn hP_sum ε hε hP_min _ _ (hiter_sum k)
      _ ≤ (1 - Fintype.card α * ε) * ((1 - Fintype.card α * ε) ^ k * tvDist μ ν) := by
        apply mul_le_mul_of_nonneg_left ih
        linarith
      _ = (1 - Fintype.card α * ε) ^ (k + 1) * tvDist μ ν := by ring

end MeasureTheory
