/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexReduction
public import Mathlib.Analysis.Convex.Approximation
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Order.UpperLower
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Finite Fenchel–Moreau theorem on the standard simplex

For a bounded-above, upper-semicontinuous function `V` on the standard simplex, this file builds
two finite-dimensional envelopes and proves they coincide:

* the **finite concave closure**, the best value obtainable by a Carathéodory-sized finite convex
  splitting of a point `μ₀` into points of the simplex, and
* the **finite concave envelope**, the infimum of affine majorants of `V` evaluated at `μ₀`.

The main theorem `finFenchelMoreau` identifies the two, the finite-dimensional analog of the
Fenchel–Moreau biconjugation theorem. The hard direction is the affine-majorant (supporting
hyperplane) bound, supported here by concavity and upper-semicontinuity of the closure.

## Main definitions

* `finConcaveClosure`, `finConcaveEnvelope` — the two envelopes.

## Main statements

* `finConcaveClosure_concave`, `finConcaveClosure_usc` — concavity and upper semicontinuity of the
  closure.
* `finConcaveClosure_le_finConcaveEnvelope`, `finConcaveEnvelope_le_finConcaveClosure` — the two
  inequalities.
* `finFenchelMoreau` — the closure equals the envelope.

## Tags

fenchel–moreau, concave closure, concave envelope, affine majorant, simplex
-/

@[expose] public section

open Finset Set Topology

variable {n : ℕ}

/-- Finite concave closure: The best value obtainable by a Carathéodory-sized finite splitting of
`μ₀` into posteriors in the standard simplex. -/
noncomputable def finConcaveClosure (V : (Fin n → ℝ) → ℝ)
    (μ₀ : Fin n → ℝ) : ℝ :=
  sSup { y : ℝ |
    ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ : Fin k → Fin n → ℝ),
      (∀ i, 0 ≤ lam i) ∧
      (∑ i, lam i = 1) ∧
      (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
      (∑ i, lam i • μ i = μ₀) ∧
      y = ∑ i, lam i * V (μ i) }

/-- Finite concave envelope as the infimum over affine majorants of `V` on the standard simplex. -/
noncomputable def finConcaveEnvelope (V : (Fin n → ℝ) → ℝ)
    (μ₀ : Fin n → ℝ) : ℝ :=
  sInf { y : ℝ |
    ∃ (p : Fin n → ℝ) (c : ℝ),
      (∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p i * μ i + c) ∧
      y = ∑ i, p i * μ₀ i + c }

/-- The set of finite-splitting values at `μ₀` is nonempty: The trivial splitting placing all mass
on `μ₀` is feasible. -/
lemma finConcaveClosure_values_nonempty
    (V : (Fin n → ℝ) → ℝ) {μ₀ : Fin n → ℝ}
    (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin n)) :
    { y : ℝ |
      ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ : Fin k → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        (∑ i, lam i = 1) ∧
        (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
        (∑ i, lam i • μ i = μ₀) ∧
        y = ∑ i, lam i * V (μ i) }.Nonempty := by
  exact ⟨V μ₀, 1, by omega, fun _ => 1, fun _ => μ₀,
    fun _ => zero_le_one, by simp, fun _ => hμ₀, by ext j; simp, by simp⟩

/-- A bound on the range of `V` yields a uniform bound on `V` over the standard simplex. -/
lemma bddAbove_range_on_simplex_of_bddAbove_range
    {V : (Fin n → ℝ) → ℝ} (hV_bddAbove : BddAbove (Set.range V)) :
    ∃ M : ℝ, ∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ M := by
  obtain ⟨M, hM⟩ := hV_bddAbove
  refine ⟨M, ?_⟩
  intro μ _hμ
  exact hM ⟨μ, rfl⟩

/-- A convex combination of simplex values is bounded by any uniform bound `M` on `V` over the
simplex.  This is the common arithmetic core of the several `BddAbove` arguments below. -/
private lemma splitting_value_le_of_bound
    {V : (Fin n → ℝ) → ℝ} {M : ℝ} (hM : ∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ M)
    {κ : Type*} [Fintype κ] {lam : κ → ℝ} {μ : κ → Fin n → ℝ}
    (hlam_nn : ∀ i, 0 ≤ lam i) (hlam_sum : ∑ i, lam i = 1)
    (hμ_simplex : ∀ i, μ i ∈ stdSimplex ℝ (Fin n)) :
    ∑ i, lam i * V (μ i) ≤ M :=
  calc
    ∑ i, lam i * V (μ i) ≤ ∑ i, lam i * M :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM (μ i) (hμ_simplex i)) (hlam_nn i)
    _ = M := by rw [← sum_mul, hlam_sum, one_mul]

/-- The set of finite-splitting values at `μ₀` is bounded above whenever `V` has bounded range. -/
lemma finConcaveClosure_values_bddAbove
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) :
    BddAbove { y : ℝ |
      ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ : Fin k → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        (∑ i, lam i = 1) ∧
        (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
        (∑ i, lam i • μ i = μ₀) ∧
        y = ∑ i, lam i * V (μ i) } := by
  obtain ⟨M, hM⟩ := bddAbove_range_on_simplex_of_bddAbove_range hV_bddAbove
  refine ⟨M, ?_⟩
  rintro y ⟨k, _hk, lam, μ, hlam_nonneg, hlam_sum, hμ_simplex, _hbayes, rfl⟩
  exact splitting_value_le_of_bound hM hlam_nonneg hlam_sum hμ_simplex

/-- The finite concave closure majorizes `V` on the simplex. -/
lemma finConcaveClosure_majorizes
    {V : (Fin n → ℝ) → ℝ} {μ : Fin n → ℝ}
    (hV_bddAbove : BddAbove (Set.range V))
    (hμ : μ ∈ stdSimplex ℝ (Fin n)) :
    V μ ≤ finConcaveClosure V μ := by
  unfold finConcaveClosure
  have hbd := finConcaveClosure_values_bddAbove (V := V) (μ₀ := μ) hV_bddAbove
  have hmem :
      V μ ∈ { y : ℝ |
        ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ' : Fin k → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧
          (∑ i, lam i = 1) ∧
          (∀ i, μ' i ∈ stdSimplex ℝ (Fin n)) ∧
          (∑ i, lam i • μ' i = μ) ∧
          y = ∑ i, lam i * V (μ' i) } := by
    exact ⟨1, by omega, fun _ => 1, fun _ => μ,
      fun _ => zero_le_one, by simp, fun _ => hμ, by ext j; simp, by simp⟩
  exact le_csSup hbd hmem

/-- The set of affine-majorant values at `μ₀` is nonempty: A constant uniform bound on `V` is an
affine majorant. -/
lemma finConcaveEnvelope_values_nonempty
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) :
    { y : ℝ |
      ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀ i + c }.Nonempty := by
  obtain ⟨M, hM⟩ := bddAbove_range_on_simplex_of_bddAbove_range hV_bddAbove
  exact ⟨M, fun _ => 0, M, fun μ hμ => by simpa using hM μ hμ, by simp⟩

/-- A single splitting value is bounded by any affine majorant evaluated at the barycenter `μ₀`. -/
lemma finConcaveClosure_candidate_le_affine
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    {k : ℕ} {lam : Fin k → ℝ} {μ : Fin k → Fin n → ℝ}
    {p : Fin n → ℝ} {c : ℝ}
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hlam_sum : ∑ i, lam i = 1)
    (hμ_simplex : ∀ i, μ i ∈ stdSimplex ℝ (Fin n))
    (hbayes : ∑ i, lam i • μ i = μ₀)
    (haff : ∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ j, p j * μ j + c) :
    ∑ i, lam i * V (μ i) ≤ ∑ j, p j * μ₀ j + c := by
  have hpoint :
      ∀ i, lam i * V (μ i) ≤ lam i * ((∑ j, p j * μ i j) + c) := by
    intro i
    exact mul_le_mul_of_nonneg_left (haff (μ i) (hμ_simplex i)) (hlam_nonneg i)
  -- The barycenter constraint, read off coordinate-wise.
  have hcoord : ∀ j, ∑ i, lam i * μ i j = μ₀ j := fun j => by
    have := congrFun hbayes j
    simpa [Finset.sum_apply, Pi.smul_apply] using this
  calc
    ∑ i, lam i * V (μ i)
        ≤ ∑ i, lam i * ((∑ j, p j * μ i j) + c) := sum_le_sum fun i _hi => hpoint i
    _ = ∑ i, (lam i * (∑ j, p j * μ i j)) + ∑ i, lam i * c := by
          rw [← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring
    _ = ∑ j, p j * (∑ i, lam i * μ i j) + ∑ i, lam i * c := by
          congr 1
          rw [show (∑ i, lam i * (∑ j, p j * μ i j)) = ∑ i, ∑ j, lam i * (p j * μ i j) from
                sum_congr rfl fun i _ => mul_sum _ _ _, sum_comm]
          exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ = ∑ j, p j * μ₀ j + c := by
          rw [← sum_mul, hlam_sum, one_mul]
          exact congrArg (· + c) (sum_congr rfl fun j _ => by rw [hcoord j])

/-- Finite weak duality: Every splitting value is bounded by every affine majorant value, hence the
finite closure is below the finite envelope. -/
theorem finConcaveClosure_le_finConcaveEnvelope
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin n))
    (hV_bddAbove : BddAbove (Set.range V)) :
    finConcaveClosure V μ₀ ≤ finConcaveEnvelope V μ₀ := by
  unfold finConcaveClosure finConcaveEnvelope
  refine csSup_le (finConcaveClosure_values_nonempty V hμ₀) ?_
  rintro x ⟨k, _hk, lam, μ, hlam_nonneg, hlam_sum, hμ_simplex, hbayes, rfl⟩
  refine le_csInf (finConcaveEnvelope_values_nonempty (V := V) (μ₀ := μ₀) hV_bddAbove) ?_
  rintro y ⟨p, c, haff, rfl⟩
  exact finConcaveClosure_candidate_le_affine hlam_nonneg hlam_sum hμ_simplex hbayes haff

/-- Finite-dimensional linear functionals are dot products against a vector. -/
theorem exists_dot_of_continuousLinearMap
    (φ : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ p : Fin n → ℝ, ∀ x : Fin n → ℝ, φ x = ∑ i, p i * x i := by
  classical
  refine ⟨fun i => φ (Pi.single i 1), ?_⟩
  intro x
  have hx_decomp : x = ∑ i, (Pi.single i (x i) : Fin n → ℝ) := by
    ext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simpa using
        (Pi.single_eq_of_ne (M := fun _ : Fin n => ℝ) (Ne.symm hij) (x i))
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  calc
    φ x = φ (∑ i, (Pi.single i (x i) : Fin n → ℝ)) := by
      exact congrArg φ hx_decomp
    _ = ∑ i, φ (Pi.single i (x i) : Fin n → ℝ) := by
      rw [map_sum]
    _ = ∑ i, x i * φ (Pi.single i (1 : ℝ)) := by
      apply sum_congr rfl
      intro i _hi
      have hsingle :
          (Pi.single i (x i) : Fin n → ℝ)
            = x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · rw [Pi.single_eq_of_ne (M := fun _ : Fin n => ℝ) hji (x i),
            Pi.smul_apply,
            Pi.single_eq_of_ne (M := fun _ : Fin n => ℝ) hji (1 : ℝ)]
          simp
      rw [hsingle, map_smul]
      rfl
    _ = ∑ i, φ (Pi.single i (1 : ℝ)) * x i := by
      apply sum_congr rfl
      intro i _hi
      ring

/-- Concatenation of two feasible splittings at convex coefficients gives a feasible splitting at
the convex combination of priors, with value the convex combination of values.  After Carathéodory
reduction, the resulting splitting size is at most `n + 1`. -/
lemma finConcaveClosure_concat_value_mem
    {V : (Fin n → ℝ) → ℝ} {μa μb : Fin n → ℝ} {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1)
    {ka kb : ℕ}
    (lam_a : Fin ka → ℝ) (μ_a : Fin ka → Fin n → ℝ)
    (hlam_a_nn : ∀ i, 0 ≤ lam_a i) (hlam_a_sum : ∑ i, lam_a i = 1)
    (hμ_a_simplex : ∀ i, μ_a i ∈ stdSimplex ℝ (Fin n))
    (hbar_a : ∑ i, lam_a i • μ_a i = μa)
    (lam_b : Fin kb → ℝ) (μ_b : Fin kb → Fin n → ℝ)
    (hlam_b_nn : ∀ i, 0 ≤ lam_b i) (hlam_b_sum : ∑ i, lam_b i = 1)
    (hμ_b_simplex : ∀ i, μ_b i ∈ stdSimplex ℝ (Fin n))
    (hbar_b : ∑ i, lam_b i • μ_b i = μb) :
    (t * (∑ i, lam_a i * V (μ_a i)) + s * (∑ i, lam_b i * V (μ_b i)))
      ∈ { y : ℝ |
          ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ : Fin k → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
            (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
            (∑ i, lam i • μ i = t • μa + s • μb) ∧
            y = ∑ i, lam i * V (μ i) } := by
  classical
  -- Concatenate weights and points using Fin.append.
  set w : Fin (ka + kb) → ℝ :=
    Fin.append (fun j => t * lam_a j) (fun j => s * lam_b j) with hw_def
  set μ : Fin (ka + kb) → Fin n → ℝ := Fin.append μ_a μ_b with hμ_def
  have hw_nn : ∀ j, 0 ≤ w j := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, w]; exact mul_nonneg ht (hlam_a_nn j)
    · simp only [Fin.append_right, w]; exact mul_nonneg hs (hlam_b_nn j)
  have hw_sum : ∑ j, w j = 1 := by
    rw [Fin.sum_univ_add]
    have h1 : ∑ j : Fin ka, w (Fin.castAdd kb j) = t := by
      simp only [w, Fin.append_left, ← Finset.mul_sum, hlam_a_sum, mul_one]
    have h2 : ∑ j : Fin kb, w (Fin.natAdd ka j) = s := by
      simp only [w, Fin.append_right, ← Finset.mul_sum, hlam_b_sum, mul_one]
    rw [h1, h2]; linarith
  have hμ_simplex : ∀ j, μ j ∈ stdSimplex ℝ (Fin n) := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left, μ]; exact hμ_a_simplex j
    · simp only [Fin.append_right, μ]; exact hμ_b_simplex j
  have hbar : ∑ j, w j • μ j = t • μa + s • μb := by
    rw [Fin.sum_univ_add]
    have hL : ∑ j : Fin ka, w (Fin.castAdd kb j) • μ (Fin.castAdd kb j) = t • μa := by
      have : ∀ j : Fin ka,
          w (Fin.castAdd kb j) • μ (Fin.castAdd kb j) = t • (lam_a j • μ_a j) := by
        intro j
        simp [w, μ, Fin.append_left, smul_smul]
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.smul_sum, hbar_a]
    have hR : ∑ j : Fin kb, w (Fin.natAdd ka j) • μ (Fin.natAdd ka j) = s • μb := by
      have : ∀ j : Fin kb,
          w (Fin.natAdd ka j) • μ (Fin.natAdd ka j) = s • (lam_b j • μ_b j) := by
        intro j
        simp [w, μ, Fin.append_right, smul_smul]
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.smul_sum, hbar_b]
    rw [hL, hR]
  have hval : ∑ j, w j * V (μ j) =
      t * (∑ i, lam_a i * V (μ_a i)) + s * (∑ i, lam_b i * V (μ_b i)) := by
    rw [Fin.sum_univ_add]
    have hL : ∑ j : Fin ka, w (Fin.castAdd kb j) * V (μ (Fin.castAdd kb j))
        = t * (∑ i, lam_a i * V (μ_a i)) := by
      have : ∀ j : Fin ka,
          w (Fin.castAdd kb j) * V (μ (Fin.castAdd kb j))
            = t * (lam_a j * V (μ_a j)) := by
        intro j
        simp [w, μ, Fin.append_left, mul_assoc]
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum]
    have hR : ∑ j : Fin kb, w (Fin.natAdd ka j) * V (μ (Fin.natAdd ka j))
        = s * (∑ i, lam_b i * V (μ_b i)) := by
      have : ∀ j : Fin kb,
          w (Fin.natAdd ka j) * V (μ (Fin.natAdd ka j))
            = s * (lam_b j * V (μ_b j)) := by
        intro j
        simp [w, μ, Fin.append_right, mul_assoc]
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum]
    rw [hL, hR]
  -- Apply augmented Carathéodory.
  obtain ⟨k, hk_le, idx, w', hw'_pos, hw'_sum, hw'_bary, hw'_val⟩ :=
    convex_combination_reduce_simplex_augmented w μ (fun j => V (μ j))
      hw_nn hw_sum hμ_simplex
  refine ⟨k, hk_le, w', fun j => μ (idx j),
    fun j => le_of_lt (hw'_pos j), hw'_sum, fun j => hμ_simplex (idx j), ?_, ?_⟩
  · rw [hw'_bary, hbar]
  · rw [hw'_val, hval]

/-- Concavity of the finite concave closure on the simplex. -/
theorem finConcaveClosure_concave
    {V : (Fin n → ℝ) → ℝ}
    (hV_bddAbove : BddAbove (Set.range V)) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin n)) (finConcaveClosure V) := by
  classical
  refine ⟨convex_stdSimplex ℝ (Fin n), ?_⟩
  intro μa hμa μb hμb t s ht hs hts
  set μav := t • μa + s • μb with hμav_def
  have hμav : μav ∈ stdSimplex ℝ (Fin n) :=
    (convex_stdSimplex ℝ (Fin n)) hμa hμb ht hs hts
  have hbd_av := finConcaveClosure_values_bddAbove (V := V) (μ₀ := μav) hV_bddAbove
  have hbd_a := finConcaveClosure_values_bddAbove (V := V) (μ₀ := μa) hV_bddAbove
  have hbd_b := finConcaveClosure_values_bddAbove (V := V) (μ₀ := μb) hV_bddAbove
  have hne_a := finConcaveClosure_values_nonempty V hμa
  have hne_b := finConcaveClosure_values_nonempty V hμb
  -- Per-pair claim: t*va + s*vb ≤ finConcaveClosure V μav.
  have hpair :
      ∀ va ∈ { y : ℝ | ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ)
              (μ : Fin k → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
            (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
            (∑ i, lam i • μ i = μa) ∧ y = ∑ i, lam i * V (μ i) },
      ∀ vb ∈ { y : ℝ | ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ)
              (μ : Fin k → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
            (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
            (∑ i, lam i • μ i = μb) ∧ y = ∑ i, lam i * V (μ i) },
        t * va + s * vb ≤ finConcaveClosure V μav := by
    rintro va ⟨ka, _hka, lam_a, μ_a, hlam_a_nn, hlam_a_sum, hμ_a_simplex,
      hbar_a, rfl⟩
    rintro vb ⟨kb, _hkb, lam_b, μ_b, hlam_b_nn, hlam_b_sum, hμ_b_simplex,
      hbar_b, rfl⟩
    have hmem :=
      finConcaveClosure_concat_value_mem (V := V) (μa := μa) (μb := μb)
        (t := t) (s := s) ht hs hts
        lam_a μ_a hlam_a_nn hlam_a_sum hμ_a_simplex hbar_a
        lam_b μ_b hlam_b_nn hlam_b_sum hμ_b_simplex hbar_b
    unfold finConcaveClosure
    exact le_csSup hbd_av hmem
  -- Reduce: t * sSup A_a + s * sSup A_b ≤ sSup A_av
  -- via `le_of_forall_pos_le_add` and approximating each sSup by an element.
  change t • finConcaveClosure V μa + s • finConcaveClosure V μb
       ≤ finConcaveClosure V μav
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  -- Choose va and vb close enough to the suprema.
  -- We need t*va ≥ t * sSup A_a - ε/2 and s*vb ≥ s * sSup A_b - ε/2.
  -- Take va > sSup A_a - ε/(2 * (t + 1)), vb > sSup A_b - ε/(2 * (s + 1)).
  set δa : ℝ := ε / (2 * (t + 1)) with hδa_def
  set δb : ℝ := ε / (2 * (s + 1)) with hδb_def
  have ht1_pos : 0 < t + 1 := by linarith
  have hs1_pos : 0 < s + 1 := by linarith
  have hδa_pos : 0 < δa := by
    rw [hδa_def]; positivity
  have hδb_pos : 0 < δb := by
    rw [hδb_def]; positivity
  -- Set notation for the two splitting sets.
  set Aa : Set ℝ := { y : ℝ | ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ)
              (μ : Fin k → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
            (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
            (∑ i, lam i • μ i = μa) ∧ y = ∑ i, lam i * V (μ i) } with hAa_def
  set Ab : Set ℝ := { y : ℝ | ∃ (k : ℕ) (_hk : k ≤ n + 1) (lam : Fin k → ℝ)
              (μ : Fin k → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
            (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
            (∑ i, lam i • μ i = μb) ∧ y = ∑ i, lam i * V (μ i) } with hAb_def
  have hfCC_a_eq : finConcaveClosure V μa = sSup Aa := rfl
  have hfCC_b_eq : finConcaveClosure V μb = sSup Ab := rfl
  -- Approximate sSup A_a from below.
  obtain ⟨va, hva_mem, hva_close⟩ : ∃ va ∈ Aa, sSup Aa - δa < va := by
    refine exists_lt_of_lt_csSup hne_a ?_
    linarith
  obtain ⟨vb, hvb_mem, hvb_close⟩ : ∃ vb ∈ Ab, sSup Ab - δb < vb := by
    refine exists_lt_of_lt_csSup hne_b ?_
    linarith
  have hpair_va_vb := hpair va hva_mem vb hvb_mem
  -- t * va + s * vb ≤ finConcaveClosure V μav, and t*va > t*(fCC μa - δa),
  -- s*vb > s*(fCC μb - δb).
  -- So t*fCC μa + s*fCC μb < t*va + δa*t + s*vb + δb*s ≤ fCC μav + δa*t + δb*s
  -- δa*t = ε*t/(2(t+1)) ≤ ε/2 (since t/(t+1) ≤ 1).
  -- δb*s = ε*s/(2(s+1)) ≤ ε/2.
  have h_t_va : t * (finConcaveClosure V μa - δa) ≤ t * va :=
    mul_le_mul_of_nonneg_left hva_close.le ht
  have h_s_vb : s * (finConcaveClosure V μb - δb) ≤ s * vb :=
    mul_le_mul_of_nonneg_left hvb_close.le hs
  -- For any r ≥ 0, the slack `r * ε/(2(r+1))` is at most `ε/2`, since `r/(r+1) ≤ 1`.
  have hδ_bound : ∀ r : ℝ, 0 ≤ r → r * (ε / (2 * (r + 1))) ≤ ε / 2 := by
    intro r hr
    have hr1_pos : 0 < r + 1 := by linarith
    have hr_ratio : r / (r + 1) ≤ 1 := by rw [div_le_one hr1_pos]; linarith
    have hmul : r * (ε / (2 * (r + 1))) = ε / 2 * (r / (r + 1)) := by field_simp
    rw [hmul]; nlinarith [hε.le]
  have hδa_t : t * δa ≤ ε / 2 := hδ_bound t ht
  have hδb_s : s * δb ≤ ε / 2 := hδ_bound s hs
  linarith

/-- Helper: In an unpadded splitting of size `k ≤ n + 1`, padding zeroes onto the weight vector and
any default simplex point onto `μ` produces a size `n + 1` splitting with the same value and
barycenter.  This will be used to identify `finConcaveClosure V` with a supremum over a fixed-size,
compact parameter space. -/
lemma finConcaveClosure_padded_value_mem
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    {k : ℕ} (hk : k ≤ n + 1) (lam : Fin k → ℝ) (μ : Fin k → Fin n → ℝ)
    (hlam_nn : ∀ i, 0 ≤ lam i) (hlam_sum : ∑ i, lam i = 1)
    (hμ_simplex : ∀ i, μ i ∈ stdSimplex ℝ (Fin n))
    (hbar : ∑ i, lam i • μ i = μ₀)
    (default : Fin n → ℝ) (hdefault : default ∈ stdSimplex ℝ (Fin n)) :
    ∃ (lam' : Fin (n + 1) → ℝ) (μ' : Fin (n + 1) → Fin n → ℝ),
      (∀ i, 0 ≤ lam' i) ∧
      (∑ i, lam' i = 1) ∧
      (∀ i, μ' i ∈ stdSimplex ℝ (Fin n)) ∧
      (∑ i, lam' i • μ' i = μ₀) ∧
      (∑ i, lam' i * V (μ' i)) = ∑ i, lam i * V (μ i) := by
  classical
  -- Pad to size n + 1 by appending (n + 1 - k) copies of (0, default).
  obtain ⟨r, hr⟩ : ∃ r, n + 1 = k + r := ⟨n + 1 - k, by omega⟩
  -- Use Fin.append: lam' = Fin.append lam (fun _ : Fin r => 0),
  --                 μ' = Fin.append μ (fun _ : Fin r => default).
  let lam'_raw : Fin (k + r) → ℝ := Fin.append lam (fun _ : Fin r => 0)
  let μ'_raw : Fin (k + r) → Fin n → ℝ := Fin.append μ (fun _ : Fin r => default)
  -- Cast Fin (k + r) ≃ Fin (n + 1) via hr.
  let e : Fin (k + r) ≃ Fin (n + 1) := finCongr hr.symm
  refine ⟨lam'_raw ∘ e.symm, μ'_raw ∘ e.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [Function.comp_apply]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) (e.symm i)
    · simpa [lam'_raw, Fin.append_left] using hlam_nn j
    · simp [lam'_raw, Fin.append_right]
  · -- ∑ lam' i = 1.
    change (∑ i, lam'_raw (e.symm i)) = 1
    rw [Equiv.sum_comp e.symm lam'_raw, Fin.sum_univ_add]
    have h1 : (∑ j : Fin k, lam'_raw (Fin.castAdd r j)) = 1 := by
      simp [lam'_raw, Fin.append_left, hlam_sum]
    have h2 : (∑ j : Fin r, lam'_raw (Fin.natAdd k j)) = 0 := by
      simp [lam'_raw, Fin.append_right]
    rw [h1, h2]; ring
  · intro i
    simp only [Function.comp_apply]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) (e.symm i)
    · simpa [μ'_raw, Fin.append_left] using hμ_simplex j
    · simpa [μ'_raw, Fin.append_right] using hdefault
  · -- Barycenter.
    change (∑ i, lam'_raw (e.symm i) • μ'_raw (e.symm i)) = μ₀
    rw [Equiv.sum_comp e.symm (fun j => lam'_raw j • μ'_raw j), Fin.sum_univ_add]
    have h1 :
        (∑ j : Fin k, lam'_raw (Fin.castAdd r j) • μ'_raw (Fin.castAdd r j))
          = μ₀ := by
      have : ∀ j : Fin k,
          lam'_raw (Fin.castAdd r j) • μ'_raw (Fin.castAdd r j) = lam j • μ j := by
        intro j
        simp [lam'_raw, μ'_raw, Fin.append_left]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      exact hbar
    have h2 :
        (∑ j : Fin r, lam'_raw (Fin.natAdd k j) • μ'_raw (Fin.natAdd k j)) = 0 := by
      have : ∀ j : Fin r,
          lam'_raw (Fin.natAdd k j) • μ'_raw (Fin.natAdd k j) = (0 : Fin n → ℝ) := by
        intro j
        simp [lam'_raw, μ'_raw, Fin.append_right]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
    rw [h1, h2]; simp
  · -- Value sum.
    change (∑ i, lam'_raw (e.symm i) * V (μ'_raw (e.symm i))) = ∑ i, lam i * V (μ i)
    rw [Equiv.sum_comp e.symm (fun j => lam'_raw j * V (μ'_raw j)),
      Fin.sum_univ_add]
    have h1 :
        (∑ j : Fin k, lam'_raw (Fin.castAdd r j) * V (μ'_raw (Fin.castAdd r j)))
          = ∑ i, lam i * V (μ i) := by
      have : ∀ j : Fin k,
          lam'_raw (Fin.castAdd r j) * V (μ'_raw (Fin.castAdd r j))
            = lam j * V (μ j) := by
        intro j
        simp [lam'_raw, μ'_raw, Fin.append_left]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
    have h2 :
        (∑ j : Fin r, lam'_raw (Fin.natAdd k j) * V (μ'_raw (Fin.natAdd k j))) = 0 := by
      have : ∀ j : Fin r,
          lam'_raw (Fin.natAdd k j) * V (μ'_raw (Fin.natAdd k j)) = 0 := by
        intro j
        simp [lam'_raw, μ'_raw, Fin.append_right]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
    rw [h1, h2]; ring

/-- The trivial splitting that puts all mass on `ν` itself is a feasible size `n + 1` padded
splitting, witnessing that the padded value set at `ν` contains `V ν`.  Used to establish
nonemptiness of the padded sup in both `finConcaveClosure_eq_padded` and `finConcaveClosure_usc`. -/
private lemma padded_trivial_splitting_mem
    {V : (Fin n → ℝ) → ℝ} {ν : Fin n → ℝ} (hν : ν ∈ stdSimplex ℝ (Fin n)) :
    ∃ (lam : Fin (n + 1) → ℝ) (μ : Fin (n + 1) → Fin n → ℝ),
      (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
      (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
      (∑ i, lam i • μ i = ν) ∧
      V ν = ∑ i, lam i * V (μ i) := by
  refine ⟨fun i : Fin (n + 1) => if i = (0 : Fin (n + 1)) then 1 else 0,
    fun _ => ν, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change (0 : ℝ) ≤ if i = (0 : Fin (n + 1)) then 1 else 0
    split_ifs <;> simp
  · simp [Finset.sum_ite_eq']
  · intro _; exact hν
  · ext j
    rw [Finset.sum_apply]
    simp [Pi.smul_apply, Finset.sum_ite_eq']
  · simp [Finset.sum_ite_eq']

/-- The finite concave closure equals the supremum of values over the fixed-size parameter space
`stdSimplex ℝ (Fin (n + 1)) × ((Fin (n + 1)) → stdSimplex ℝ (Fin n))`, intersected with the
constraint `∑ λᵢ • μᵢ = μ₀`.  This rewriting is used to realize the closure as the image of a
closed set under a continuous map. -/
lemma finConcaveClosure_eq_padded
    {V : (Fin n → ℝ) → ℝ} (hn : 0 < n) {μ₀ : Fin n → ℝ}
    (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin n))
    (hV_bddAbove : BddAbove (Set.range V)) :
    finConcaveClosure V μ₀ =
      sSup { y : ℝ |
        ∃ (lam : Fin (n + 1) → ℝ) (μ : Fin (n + 1) → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧
          (∑ i, lam i = 1) ∧
          (∀ i, μ i ∈ stdSimplex ℝ (Fin n)) ∧
          (∑ i, lam i • μ i = μ₀) ∧
          y = ∑ i, lam i * V (μ i) } := by
  classical
  -- Default padded point.
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  let i0 : Fin n := ⟨0, hn⟩
  let v0 : Fin n → ℝ := Pi.single i0 1
  have hv0 : v0 ∈ stdSimplex ℝ (Fin n) := single_mem_stdSimplex ℝ i0
  apply le_antisymm
  · -- finConcaveClosure ≤ sSup_padded.
    unfold finConcaveClosure
    refine csSup_le_csSup ?_ (finConcaveClosure_values_nonempty V hμ₀) ?_
    · -- Padded set bounded above.
      obtain ⟨M, hM⟩ := bddAbove_range_on_simplex_of_bddAbove_range hV_bddAbove
      refine ⟨M, ?_⟩
      rintro y ⟨lam, μ, hlam_nn, hlam_sum, hμ_simplex, _hbar, rfl⟩
      exact splitting_value_le_of_bound hM hlam_nn hlam_sum hμ_simplex
    · -- Original ⊆ padded set.
      rintro y ⟨k, hk, lam, μ, hlam_nn, hlam_sum, hμ_simplex, hbar, rfl⟩
      obtain ⟨lam', μ', hlam'_nn, hlam'_sum, hμ'_simplex, hbar', hval'⟩ :=
        finConcaveClosure_padded_value_mem hk lam μ hlam_nn hlam_sum
          hμ_simplex hbar v0 hv0
      exact ⟨lam', μ', hlam'_nn, hlam'_sum, hμ'_simplex, hbar', hval'.symm⟩
  · -- sSup_padded ≤ finConcaveClosure: padded ⊆ original (k = n + 1).
    refine csSup_le ?_ ?_
    · -- Padded set is nonempty: take the trivial splitting all-mass-on-μ₀.
      obtain ⟨lam, μ, hlam_nn, hlam_sum, hμ_simplex, hbar, hval⟩ :=
        padded_trivial_splitting_mem (V := V) hμ₀
      exact ⟨V μ₀, lam, μ, hlam_nn, hlam_sum, hμ_simplex, hbar, hval⟩
    · rintro y ⟨lam, μ, hlam_nn, hlam_sum, hμ_simplex, hbar, rfl⟩
      unfold finConcaveClosure
      have hbd := finConcaveClosure_values_bddAbove (V := V) (μ₀ := μ₀) hV_bddAbove
      exact le_csSup hbd ⟨n + 1, le_refl _, lam, μ, hlam_nn, hlam_sum,
        hμ_simplex, hbar, rfl⟩

/-- Upper semicontinuity of the finite concave closure on the simplex. -/
theorem finConcaveClosure_usc
    {V : (Fin n → ℝ) → ℝ}
    (hV_bddAbove : BddAbove (Set.range V))
    (hV_usc : UpperSemicontinuousOn V (stdSimplex ℝ (Fin n))) :
    UpperSemicontinuousOn (finConcaveClosure V) (stdSimplex ℝ (Fin n)) := by
  classical
  -- Edge case: n = 0.  Then stdSimplex ℝ (Fin 0) = ∅, so USC is trivial.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    intro μ hμ
    have : (∑ i : Fin 0, μ i) = 1 := hμ.2
    simp at this
  -- Sequential characterization of upper semicontinuity via closed hypograph.
  rw [upperSemicontinuousOn_iff_isClosed_hypograph (isClosed_stdSimplex _ _),
      ← isSeqClosed_iff_isClosed]
  intro u p hu_mem hu_tend
  -- Coordinate sequences and their limits.
  set μ : ℕ → Fin n → ℝ := fun k => (u k).1 with hμ_def
  set y : ℕ → ℝ := fun k => (u k).2 with hy_def
  have hμ_simplex : ∀ k, μ k ∈ stdSimplex ℝ (Fin n) := fun k => (hu_mem k).1
  have hy_le : ∀ k, y k ≤ finConcaveClosure V (μ k) := fun k => (hu_mem k).2
  have hμ_tend : Filter.Tendsto μ Filter.atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hu_tend
  have hy_tend : Filter.Tendsto y Filter.atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hu_tend
  -- p.1 ∈ stdSimplex (closed under sequential limits).
  have hp1_simplex : p.1 ∈ stdSimplex ℝ (Fin n) :=
    (isClosed_stdSimplex _ _).mem_of_tendsto hμ_tend (Filter.Eventually.of_forall hμ_simplex)
  refine ⟨hp1_simplex, ?_⟩
  -- We will use the padded characterization throughout.
  -- For each k, pick a padded splitting at μ k achieving value > y k − 1/(k+1).
  -- Step 0: the padded sup is bounded above (by a uniform M from BddAbove (range V)).
  obtain ⟨M, hM⟩ := bddAbove_range_on_simplex_of_bddAbove_range hV_bddAbove
  -- Padded value set for an arbitrary prior in the simplex.
  let Spad : (Fin n → ℝ) → Set ℝ := fun ν =>
    { z : ℝ | ∃ (lam : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
        (∀ i, m i ∈ stdSimplex ℝ (Fin n)) ∧
        (∑ i, lam i • m i = ν) ∧
        z = ∑ i, lam i * V (m i) }
  -- Boundedness of `Spad ν` by `M` for any `ν` in the simplex.
  have hSpad_bdd : ∀ ν, BddAbove (Spad ν) := by
    intro ν
    refine ⟨M, ?_⟩
    rintro z ⟨lam, m, hlam_nn, hlam_sum, hm_simplex, _hbar, rfl⟩
    exact splitting_value_le_of_bound hM hlam_nn hlam_sum hm_simplex
  -- `finConcaveClosure V ν = sSup (Spad ν)` for ν ∈ stdSimplex (via finConcaveClosure_eq_padded).
  have hfCC_eq : ∀ ν ∈ stdSimplex ℝ (Fin n), finConcaveClosure V ν = sSup (Spad ν) := by
    intro ν hν
    exact finConcaveClosure_eq_padded hnpos hν hV_bddAbove
  -- For each k, get a near-maximizer (lam_k, m_k) at μ k with value > y k - 1/(k+1).
  have h_near_max : ∀ k : ℕ, ∃ (lam : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Fin n → ℝ),
      (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i = 1) ∧
      (∀ i, m i ∈ stdSimplex ℝ (Fin n)) ∧
      (∑ i, lam i • m i = μ k) ∧
      y k - 1 / (k + 1 : ℝ) < ∑ i, lam i * V (m i) := by
    intro k
    have hk1_pos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    have h_lt : y k - 1 / (k + 1 : ℝ) < finConcaveClosure V (μ k) := by
      have h1 : y k ≤ finConcaveClosure V (μ k) := hy_le k
      linarith
    rw [hfCC_eq (μ k) (hμ_simplex k)] at h_lt
    -- Padded set is nonempty: V (μ k) is a feasible value via the trivial all-mass-on-μ-k.
    have hSne : (Spad (μ k)).Nonempty := by
      obtain ⟨lam, m, hlam_nn, hlam_sum, hm_simplex, hbar, hval⟩ :=
        padded_trivial_splitting_mem (V := V) (hμ_simplex k)
      exact ⟨V (μ k), lam, m, hlam_nn, hlam_sum, hm_simplex, hbar, hval⟩
    obtain ⟨z, hz_mem, hz_lt⟩ := exists_lt_of_lt_csSup hSne h_lt
    obtain ⟨lam, m, hlam_nn, hlam_sum, hm_simplex, hbar, rfl⟩ := hz_mem
    exact ⟨lam, m, hlam_nn, hlam_sum, hm_simplex, hbar, hz_lt⟩
  choose lam m hlam_nn hlam_sum hm_simplex hbar hval using h_near_max
  -- The pair `(lam k, m k)` lies in a compact subset of
  -- `(Fin (n+1) → ℝ) × (Fin (n+1) → Fin n → ℝ)`.
  let K : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin n → ℝ)) :=
    { p | p.1 ∈ stdSimplex ℝ (Fin (n + 1)) ∧ ∀ i, p.2 i ∈ stdSimplex ℝ (Fin n) }
  have hK_compact : IsCompact K := by
    have h1 : IsCompact (stdSimplex ℝ (Fin (n + 1))) := isCompact_stdSimplex ℝ (Fin (n + 1))
    have h2 : IsCompact { f : Fin (n + 1) → Fin n → ℝ |
        ∀ i, f i ∈ stdSimplex ℝ (Fin n) } :=
      isCompact_pi_infinite (fun _ => isCompact_stdSimplex ℝ (Fin n))
    have hprod := h1.prod h2
    convert hprod using 1
  -- Pack the sequence into K.
  have h_in_K : ∀ k, (lam k, m k) ∈ K := fun k =>
    ⟨⟨hlam_nn k, hlam_sum k⟩, hm_simplex k⟩
  -- Extract a convergent subsequence.
  obtain ⟨q, hq_in_K, ψ, hψ_mono, hψ_tend⟩ :=
    hK_compact.tendsto_subseq h_in_K
  set lam_star : Fin (n + 1) → ℝ := q.1 with hlam_star_def
  set m_star : Fin (n + 1) → Fin n → ℝ := q.2 with hm_star_def
  have hlam_star_nn : ∀ i, 0 ≤ lam_star i := hq_in_K.1.1
  have hlam_star_sum : ∑ i, lam_star i = 1 := hq_in_K.1.2
  have hm_star_simplex : ∀ i, m_star i ∈ stdSimplex ℝ (Fin n) := hq_in_K.2
  -- Coordinate convergence.
  have hlam_tend : Filter.Tendsto (fun j => lam ∘ ψ <| j) Filter.atTop (𝓝 lam_star) := by
    have := (continuous_fst.tendsto q).comp hψ_tend
    simpa [Function.comp_def, hlam_star_def] using this
  have hm_tend : Filter.Tendsto (fun j => m ∘ ψ <| j) Filter.atTop (𝓝 m_star) := by
    have := (continuous_snd.tendsto q).comp hψ_tend
    simpa [Function.comp_def, hm_star_def] using this
  -- Coordinate-wise convergence (i.e. for each i ∈ Fin (n+1)).
  have hlam_i_tend : ∀ i, Filter.Tendsto (fun j => lam (ψ j) i) Filter.atTop
      (𝓝 (lam_star i)) := fun i =>
    (continuous_apply i).tendsto _ |>.comp hlam_tend
  have hm_i_tend : ∀ i, Filter.Tendsto (fun j => m (ψ j) i) Filter.atTop
      (𝓝 (m_star i)) := fun i =>
    (continuous_apply i).tendsto _ |>.comp hm_tend
  -- Pass the barycenter constraint to the limit.
  have hbar_star : ∑ i, lam_star i • m_star i = p.1 := by
    have hbar_lim : Filter.Tendsto
        (fun j => ∑ i, lam (ψ j) i • m (ψ j) i) Filter.atTop
        (𝓝 (∑ i, lam_star i • m_star i)) := by
      refine tendsto_finset_sum _ ?_
      intro i _
      exact (hlam_i_tend i).smul (hm_i_tend i)
    have hbar_const : Filter.Tendsto
        (fun j => ∑ i, lam (ψ j) i • m (ψ j) i) Filter.atTop
        (𝓝 p.1) := by
      have hμ_subseq := hμ_tend.comp hψ_mono.tendsto_atTop
      have hbar_eq : ∀ j, ∑ i, lam (ψ j) i • m (ψ j) i = μ (ψ j) := fun j => hbar (ψ j)
      simpa [hbar_eq] using hμ_subseq
    exact tendsto_nhds_unique hbar_lim hbar_const
  -- The pair (lam_star, m_star) defines a feasible padded splitting at p.1.
  have hp1_value_le : ∑ i, lam_star i * V (m_star i) ≤ finConcaveClosure V p.1 := by
    rw [hfCC_eq p.1 hp1_simplex]
    refine le_csSup (hSpad_bdd p.1) ?_
    exact ⟨lam_star, m_star, hlam_star_nn, hlam_star_sum, hm_star_simplex,
      hbar_star, rfl⟩
  -- Limsup argument: for any ε > 0, eventually
  -- `∑ i, lam (ψ j) i * V (m (ψ j) i) ≤ ∑ i, lam_star i * V (m_star i) + ε`.
  -- Combined with `y (ψ j) - 1/(ψ j + 1) < ∑ ... `, get y (ψ j) < ∑_star + ε + 1/(ψ j + 1).
  -- Pass j → ∞.
  -- Step: prove `p.2 ≤ ∑ i, lam_star i * V (m_star i)`.
  have hy_upper : p.2 ≤ ∑ i, lam_star i * V (m_star i) := by
    -- It suffices to show that for every ε > 0, p.2 ≤ ∑_star + ε.
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- Step A: USC of V at each m_star i gives a bound for j large.
    -- For each i, eventually V (m (ψ j) i) ≤ V (m_star i) + ε / (n + 1).
    have hε' : (0 : ℝ) < ε / (n + 1 : ℝ) := by positivity
    have hUSC_event : ∀ i, ∀ᶠ j in Filter.atTop,
        V (m (ψ j) i) ≤ V (m_star i) + ε / (n + 1 : ℝ) := by
      intro i
      have hm_star_i : m_star i ∈ stdSimplex ℝ (Fin n) := hm_star_simplex i
      have h_usc_at := hV_usc (m_star i) hm_star_i
      -- USC at m_star i within stdSimplex: V < V (m_star i) + ε/(n+1) on a 𝓝[stdSimplex] m_star i.
      have h_lt : V (m_star i) < V (m_star i) + ε / (n + 1 : ℝ) := by linarith
      have h_event_within : ∀ᶠ x in 𝓝[stdSimplex ℝ (Fin n)] (m_star i),
          V x < V (m_star i) + ε / (n + 1 : ℝ) :=
        h_usc_at _ h_lt
      -- Convergence m (ψ j) i → m_star i within stdSimplex.
      have hm_i_within : Filter.Tendsto (fun j => m (ψ j) i) Filter.atTop
          (𝓝[stdSimplex ℝ (Fin n)] (m_star i)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (hm_i_tend i)
          (Filter.Eventually.of_forall (fun j => hm_simplex (ψ j) i))
      filter_upwards [hm_i_within h_event_within] with j hj
      exact le_of_lt hj
    -- Step B: bundle over the finite set of i ∈ Fin (n+1).
    have hUSC_all : ∀ᶠ j in Filter.atTop,
        ∀ i, V (m (ψ j) i) ≤ V (m_star i) + ε / (n + 1 : ℝ) := by
      rw [Filter.eventually_all]
      exact hUSC_event
    -- Step C: bound the value sum eventually.
    have h_value_bound : ∀ᶠ j in Filter.atTop,
        ∑ i, lam (ψ j) i * V (m (ψ j) i) ≤
          ∑ i, lam (ψ j) i * (V (m_star i) + ε / (n + 1 : ℝ)) := by
      filter_upwards [hUSC_all] with j hj
      refine Finset.sum_le_sum (fun i _ => ?_)
      exact mul_le_mul_of_nonneg_left (hj i) (hlam_nn (ψ j) i)
    -- Step D: simplify the RHS = ∑ lam (ψ j) i * V (m_star i) + ε / (n + 1).
    have h_rhs_eq : ∀ j, ∑ i, lam (ψ j) i * (V (m_star i) + ε / (n + 1 : ℝ)) =
        (∑ i, lam (ψ j) i * V (m_star i)) + ε / (n + 1 : ℝ) := by
      intro j
      have h1 : ∑ i, lam (ψ j) i * (V (m_star i) + ε / (n + 1 : ℝ)) =
          (∑ i, lam (ψ j) i * V (m_star i)) +
            ∑ i, lam (ψ j) i * (ε / (n + 1 : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      have h2 : ∑ i, lam (ψ j) i * (ε / (n + 1 : ℝ)) = ε / (n + 1 : ℝ) := by
        rw [← Finset.sum_mul, hlam_sum (ψ j), one_mul]
      rw [h1, h2]
    -- Step E: convergence of ∑ lam (ψ j) i * V (m_star i) to ∑ lam_star i * V (m_star i).
    have h_lin_tend : Filter.Tendsto
        (fun j => ∑ i, lam (ψ j) i * V (m_star i)) Filter.atTop
        (𝓝 (∑ i, lam_star i * V (m_star i))) := by
      refine tendsto_finset_sum _ ?_
      intro i _
      exact (hlam_i_tend i).mul tendsto_const_nhds
    -- Step F: 1/(ψ j + 1) → 0.
    have h_inv_tend : Filter.Tendsto (fun j => 1 / (ψ j + 1 : ℝ)) Filter.atTop (𝓝 0) := by
      have hψ_atTop : Filter.Tendsto ψ Filter.atTop Filter.atTop := hψ_mono.tendsto_atTop
      have h1 : Filter.Tendsto (fun j => (ψ j + 1 : ℝ)) Filter.atTop Filter.atTop := by
        refine Filter.tendsto_atTop_add_const_right _ 1 ?_
        exact tendsto_natCast_atTop_atTop.comp hψ_atTop
      simpa using h1.inv_tendsto_atTop
    -- Step G: y (ψ j) tendsto p.2.
    have hy_subseq : Filter.Tendsto (fun j => y (ψ j)) Filter.atTop (𝓝 p.2) :=
      hy_tend.comp hψ_mono.tendsto_atTop
    -- Step H: combine.  Eventually y (ψ j) < ∑ + 1/(ψ j + 1) and value sum bound.
    have h_y_bound : ∀ᶠ j in Filter.atTop,
        y (ψ j) ≤
          (∑ i, lam (ψ j) i * V (m_star i)) + ε / (n + 1 : ℝ)
            + 1 / (ψ j + 1 : ℝ) := by
      filter_upwards [h_value_bound] with j hj
      have hval_j := hval (ψ j)
      have h_rhs := h_rhs_eq j
      linarith [hj, hval_j, h_rhs]
    -- Step I: pass to the limit using the eventual upper bound.
    have h_rhs_tend : Filter.Tendsto
        (fun j => (∑ i, lam (ψ j) i * V (m_star i)) + ε / (n + 1 : ℝ)
              + 1 / (ψ j + 1 : ℝ)) Filter.atTop
        (𝓝 ((∑ i, lam_star i * V (m_star i)) + ε / (n + 1 : ℝ) + 0)) :=
      (h_lin_tend.add tendsto_const_nhds).add h_inv_tend
    have h_le_lim : p.2 ≤
        (∑ i, lam_star i * V (m_star i)) + ε / (n + 1 : ℝ) + 0 :=
      le_of_tendsto_of_tendsto hy_subseq h_rhs_tend h_y_bound
    -- Combine with `ε / (n + 1) ≤ ε`.
    have h_eps_le : ε / (n + 1 : ℝ) ≤ ε := by
      have hn1_pos : (0 : ℝ) < n + 1 := by positivity
      rw [div_le_iff₀ hn1_pos]
      have h_one_le : (1 : ℝ) ≤ n + 1 := by
        have : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        linarith
      nlinarith [le_of_lt hε]
    linarith
  exact hy_upper.trans hp1_value_le

/-- Hard finite Fenchel–Moreau direction: The finite concave envelope is bounded above by the
finite concave closure, so affine majorants attain the closure value from above. -/
theorem finConcaveEnvelope_le_finConcaveClosure
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin n))
    (hV_bddAbove : BddAbove (Set.range V))
    (hV_usc : UpperSemicontinuousOn V (stdSimplex ℝ (Fin n))) :
    finConcaveEnvelope V μ₀ ≤ finConcaveClosure V μ₀ := by
  classical
  -- Set up the convex, LSC negative function.
  set φ : (Fin n → ℝ) → ℝ := fun μ => -finConcaveClosure V μ with hφ_def
  have hφ_convex : ConvexOn ℝ (stdSimplex ℝ (Fin n)) φ := by
    have := finConcaveClosure_concave (V := V) hV_bddAbove
    exact this.neg
  have hφ_lsc : LowerSemicontinuousOn φ (stdSimplex ℝ (Fin n)) := by
    have := finConcaveClosure_usc (V := V) hV_bddAbove hV_usc
    exact this.neg
  have hsc : IsClosed (stdSimplex ℝ (Fin n)) := isClosed_stdSimplex _ _
  -- Use le_of_forall_pos_le_add (we can also use exists_affine_le_real if we want to
  -- get a single affine majorant; here we proceed with arbitrarily small ε).
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  -- a := φ μ₀ - ε satisfies a < φ μ₀.
  set a : ℝ := φ μ₀ - ε with ha_def
  have ha_lt : a < φ μ₀ := by rw [ha_def]; linarith
  -- Apply `exists_affine_le_of_lt` over 𝕜 = ℝ to get an affine minorant of φ
  -- whose value at μ₀ equals a.
  obtain ⟨l, c, hlc_le, hlc_eq⟩ :=
    hφ_convex.exists_affine_le_of_lt (𝕜 := ℝ) hμ₀ ha_lt hsc hφ_lsc
  -- hlc_le : restrict (re ∘ l) + const c ≤ restrict φ on stdSimplex.
  -- For ℝ, re = id, so re ∘ l acts as l on points.  Convert l to a vector p.
  obtain ⟨p, hp_dot⟩ := exists_dot_of_continuousLinearMap (n := n) l
  -- For each μ ∈ stdSimplex, l μ + c ≤ φ μ = -finConcaveClosure V μ.
  -- So -l μ - c ≥ finConcaveClosure V μ ≥ V μ.  Thus (p' := -p, c' := -c) gives
  -- an affine majorant of V on stdSimplex; its value at μ₀ is -(l μ₀ + c) =
  -- -(a + ε - ε) = -a (using hlc_eq, since RCLike re of real l is l itself).
  -- More precisely: l μ₀ + c = a (from hlc_eq).
  set p' : Fin n → ℝ := fun i => -p i with hp'_def
  set c' : ℝ := -c with hc'_def
  -- The negated affine form `(p', c')` evaluates to `-(l x + c)` at every point.
  have h_affine_eq : ∀ x : Fin n → ℝ, ∑ i, p' i * x i + c' = -(l x + c) := by
    intro x
    have h1 : (∑ i, p' i * x i) = -(∑ i, p i * x i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp [p']
    rw [h1, hp_dot, hc'_def]; ring
  -- Affine majorant on stdSimplex: ∑ p'_i μ_i + c' ≥ V μ.
  have hmaj : ∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p' i * μ i + c' := by
    intro μ hμ
    have hμ_phi : V μ ≤ -φ μ := by
      have := finConcaveClosure_majorizes (V := V) hV_bddAbove hμ
      simp [hφ_def]; linarith
    -- l μ + c ≤ φ μ, so -φ μ ≤ -(l μ + c) = -l μ - c = ∑ -p_i μ_i - c.
    have hl_phi : l μ + c ≤ φ μ := by
      have := hlc_le ⟨μ, hμ⟩
      -- The restrict + const formulation.  Unfold.
      simpa [Set.restrict_apply] using this
    rw [h_affine_eq μ]
    linarith
  -- Value at μ₀: ∑ p'_i μ₀_i + c' = -(l μ₀ + c) = -a.
  have hval : (∑ i, p' i * μ₀ i + c') = -a := by
    rw [h_affine_eq μ₀]
    -- hlc_eq : RCLike.re (l μ₀) + c = a (since 𝕜 = ℝ, RCLike.re = id).
    have : (l μ₀ : ℝ) + c = a := hlc_eq
    linarith
  -- Now use this affine majorant to bound the envelope.
  unfold finConcaveEnvelope
  have hbd_below :
      BddBelow { y : ℝ | ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀ i + c } := by
    -- Bounded below by V μ₀ (or by finConcaveClosure V μ₀, which is ≥ V μ₀).
    refine ⟨V μ₀, ?_⟩
    rintro y ⟨p, c, haff, rfl⟩
    exact haff μ₀ hμ₀
  have hmem : (∑ i, p' i * μ₀ i + c') ∈ { y : ℝ |
      ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀ i + c } :=
    ⟨p', c', hmaj, rfl⟩
  -- sInf of envelope set ≤ this affine value = -a = -(φ μ₀ - ε) = finConcaveClosure V μ₀ + ε.
  have h_inf_le : sInf { y : ℝ | ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), V μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀ i + c } ≤ ∑ i, p' i * μ₀ i + c' :=
    csInf_le hbd_below hmem
  rw [hval] at h_inf_le
  have hneg_a : -a = finConcaveClosure V μ₀ + ε := by
    simp [a, φ]; ring
  linarith

/-- Finite Fenchel--Moreau equality on the standard simplex. -/
theorem finFenchelMoreau
    {V : (Fin n → ℝ) → ℝ} {μ₀ : Fin n → ℝ}
    (hμ₀ : μ₀ ∈ stdSimplex ℝ (Fin n))
    (hV_bddAbove : BddAbove (Set.range V))
    (hV_usc : UpperSemicontinuousOn V (stdSimplex ℝ (Fin n))) :
    finConcaveClosure V μ₀ = finConcaveEnvelope V μ₀ := by
  exact le_antisymm
    (finConcaveClosure_le_finConcaveEnvelope hμ₀ hV_bddAbove)
    (finConcaveEnvelope_le_finConcaveClosure hμ₀ hV_bddAbove hV_usc)
