/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Econlib.Math.Analysis.BetaIntegral

/-!
# The Dirichlet integral over the standard simplex

This file evaluates the unnormalized **Dirichlet integral** over the standard **simplex** in
reduced coordinates and shows it equals the multivariate beta function `(∏ i, Γ(αᵢ)) / Γ(∑ i, αᵢ)`
for parameters `αᵢ > 0`.

## Main definitions

* `MeasureTheory.simplexIntegral` — the unnormalized Dirichlet integrand integrated over the
  reduced-coordinate simplex.

## Main statements

* `MeasureTheory.indicator_beta_integral` — the one-dimensional indicator beta integral.
* `MeasureTheory.simplexIntegral_two` — the value at dimension `k = 2`.
* `MeasureTheory.simplexIntegrand_integrable` — integrability of the Dirichlet integrand.
* `MeasureTheory.simplexIntegral_fubini` — the recurrence relating dimension `k + 2` to dimension
  `k + 1` via the parameter merge `mergeLastTwo`.
* `MeasureTheory.simplexIntegral_eq_multivariateBeta` — the Dirichlet integral equals the
  multivariate beta function.

## Tags

dirichlet integral, simplex, beta function, gamma function, fubini
-/

@[expose] public section

open MeasureTheory Real

namespace MeasureTheory

/-- The unnormalized Dirichlet integral over the simplex in reduced coordinates. -/
noncomputable def simplexIntegral (k : ℕ) (α : Fin k → ℝ) : ℝ :=
  if hk : k = 0 then 1
  else if hk1 : k = 1 then 1
  else
    let n := k - 1
    ∫ y : Fin n → ℝ,
      if (∀ i, 0 < y i) ∧ ∑ i, y i < 1 then
        (∏ i : Fin n, (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i, y i) ^ (α ⟨n, by omega⟩ - 1)
      else 0

/-! ### The indicator beta integral -/

/-- The integral over `ℝ` of the indicator-restricted integrand `x^(s-1)·(1-x)^(t-1)` on `(0, 1)`
equals the beta function `beta s t`, for `s, t > 0`. -/
lemma indicator_beta_integral {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∫ x : ℝ, (if 0 < x ∧ x < 1 then x ^ (s - 1) * (1 - x) ^ (t - 1) else 0) =
    ProbabilityTheory.beta s t := by
  have h1 : ∫ x : ℝ, (if 0 < x ∧ x < 1 then x ^ (s - 1) * (1 - x) ^ (t - 1) else 0) =
      ∫ x in Set.Ioo 0 1, x ^ (s - 1) * (1 - x) ^ (t - 1) := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [Set.mem_Ioo] at hx
      simp [hx.1, hx.2]
    · intro x hx
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
      simp only [ite_eq_right_iff]
      intro ⟨hx1, hx2⟩
      exact absurd hx1 (by rcases hx with h | h <;> linarith)
  rw [h1]
  have h2 := betaIntegral_scaled_real hs ht (show (0 : ℝ) < 1 by linarith)
  simp only [one_rpow, one_mul] at h2
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
    Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by linarith)] at h2
  simp only [show (0 : ℝ) ≤ 1 from by linarith, if_true, one_smul] at h2
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact h2

/-! ### Dimension `k = 2` -/

/-- At dimension `k = 2` the Dirichlet simplex integral is the two-parameter beta function
`beta (α 0) (α 1)`, for positive parameters. -/
lemma simplexIntegral_two {α : Fin 2 → ℝ} (hα : ∀ i, 0 < α i) :
    simplexIntegral 2 α = ProbabilityTheory.beta (α 0) (α 1) := by
  change (∫ y : Fin 1 → ℝ,
    if (∀ i : Fin 1, 0 < y i) ∧ ∑ i : Fin 1, y i < 1 then
      (∏ i : Fin 1, (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
        (1 - ∑ i : Fin 1, y i) ^ (α ⟨1, by omega⟩ - 1)
    else 0) = _
  have key : ∀ y : Fin 1 → ℝ,
      (if (∀ i : Fin 1, 0 < y i) ∧ ∑ i : Fin 1, y i < 1 then
        (∏ i : Fin 1, (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i : Fin 1, y i) ^ (α ⟨1, by omega⟩ - 1)
      else 0) =
      (fun t : ℝ => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1) else 0)
        (y 0) := by
    intro y
    simp only [Fin.sum_univ_one, Fin.prod_univ_one, Fin.forall_fin_one, Fin.val_zero]
    rfl
  simp_rw [key]
  have := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp'
    (f := MeasurableEquiv.funUnique (Fin 1) ℝ)
    (fun t : ℝ => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1) else 0)
  simp only [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero] at this
  erw [this]
  exact indicator_beta_integral (hα 0) (hα 1)

/-! ### Decomposition helpers for `Fin.snoc` -/

/-- Sum of `Fin.snoc y' t` equals `∑ y' + t`. -/
private lemma snoc_sum {k : ℕ} (y' : Fin k → ℝ) (t : ℝ) :
    ∑ i : Fin (k + 1), Fin.snoc y' t i = (∑ j : Fin k, y' j) + t := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl; intro j _; exact Fin.snoc_castSucc _ _ _
  · exact Fin.snoc_last _ _

/-- Product of `(Fin.snoc y' t) i ^ (α i - 1)` decomposes via castSucc and last. -/
private lemma snoc_prod {k : ℕ} (y' : Fin k → ℝ) (t : ℝ)
    (α : Fin (k + 2) → ℝ) :
    ∏ i : Fin (k + 1), (Fin.snoc y' t i) ^ (α ⟨i.val, by omega⟩ - 1) =
    (∏ j : Fin k, (y' j) ^ (α ⟨j.val, by omega⟩ - 1)) *
      t ^ (α ⟨k, by omega⟩ - 1) := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl; intro j _
    rw [Fin.snoc_castSucc]
    congr 2
  · rw [Fin.snoc_last]; congr 2

/-- The simplex condition on `Fin.snoc y' t` is equivalent to
`(∀ j, 0 < y' j) ∧ 0 < t ∧ ∑ y' + t < 1`. -/
private lemma snoc_simplex_iff {k : ℕ} (y' : Fin k → ℝ) (t : ℝ) :
    ((∀ i : Fin (k + 1), 0 < @Fin.snoc k (fun _ => ℝ) y' t i) ∧
      ∑ i, @Fin.snoc k (fun _ => ℝ) y' t i < 1) ↔
    ((∀ j : Fin k, 0 < y' j) ∧ 0 < t ∧ (∑ j, y' j) + t < 1) := by
  constructor
  · intro ⟨hpos, hsum⟩
    refine ⟨fun j => ?_, ?_, ?_⟩
    · have := hpos (Fin.castSucc j); rwa [Fin.snoc_castSucc _ _ _] at this
    · have := hpos (Fin.last k); rwa [Fin.snoc_last _ _] at this
    · rwa [snoc_sum] at hsum
  · intro ⟨hpos, ht, hsum⟩
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = Fin.last k
      · subst h; rwa [Fin.snoc_last _ _]
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr h
        rw [Fin.snoc_castSucc _ _ _]; exact hpos j
    · rw [snoc_sum]; exact hsum

/-! ### Inner integral evaluation -/

/-- The inner integral `∫ t, if 0 < t ∧ S + t < 1 then C * t^(s-1) * (1-S-t)^(u-1) else 0` equals
`C * (1-S)^(s+u-1) * beta(s, u)` when `S < 1`, `s > 0`, `u > 0`. -/
private lemma inner_integral_eq {s u S C : ℝ} (hs : 0 < s) (hu : 0 < u) (hS : S < 1) :
    ∫ t : ℝ, (if 0 < t ∧ S + t < 1 then
      C * t ^ (s - 1) * (1 - S - t) ^ (u - 1) else 0) =
    C * (1 - S) ^ (s + u - 1) * ProbabilityTheory.beta s u := by
  -- Factor out C
  have h_factor : ∀ t : ℝ,
      (if 0 < t ∧ S + t < 1 then C * t ^ (s - 1) * (1 - S - t) ^ (u - 1) else 0) =
      C * (if 0 < t ∧ S + t < 1 then t ^ (s - 1) * (1 - S - t) ^ (u - 1) else 0) := by
    intro t; split_ifs <;> ring
  simp_rw [h_factor, integral_const_mul]
  rw [show C * (1 - S) ^ (s + u - 1) * ProbabilityTheory.beta s u =
    C * ((1 - S) ^ (s + u - 1) * ProbabilityTheory.beta s u) from by ring]
  congr 1
  -- Now need: ∫ t, if 0 < t ∧ S + t < 1 then t^(s-1)*(1-S-t)^(u-1) else 0
  --         = (1-S)^(s+u-1) * beta(s, u)
  -- The condition 0 < t ∧ S + t < 1 is equivalent to 0 < t ∧ t < 1 - S
  have h_cond : ∀ t : ℝ, (0 < t ∧ S + t < 1) ↔ (0 < t ∧ t < 1 - S) := by
    intro t; constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  simp_rw [show ∀ t, (if 0 < t ∧ S + t < 1 then t ^ (s - 1) * (1 - S - t) ^ (u - 1) else 0) =
    (if 0 < t ∧ t < 1 - S then t ^ (s - 1) * ((1 - S) - t) ^ (u - 1) else 0) from by
      intro t; rw [show 1 - S - t = (1 - S) - t from by ring]; congr 1; exact propext (h_cond t)]
  -- Convert indicator integral to set integral on Ioo
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioo 0 (1 - S)) (fun x hx => by
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hx
    split_ifs with h
    · exact absurd h.1 (by rcases hx with h' | h' <;> linarith)
    · rfl)]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => by
    simp only [Set.mem_Ioo] at hx; rw [if_pos ⟨hx.1, hx.2⟩])]
  -- Now: ∫ x in Ioo 0 (1-S), x^(s-1) * ((1-S)-x)^(u-1) = (1-S)^(s+u-1) * beta(s, u)
  rw [← integral_Ioc_eq_integral_Ioo]
  have ha : (0 : ℝ) < 1 - S := by linarith
  rw [show ∫ x in Set.Ioc 0 (1 - S), x ^ (s - 1) * ((1 - S) - x) ^ (u - 1) =
    ∫ x in (0 : ℝ)..(1 - S), x ^ (s - 1) * ((1 - S) - x) ^ (u - 1) from by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
          Set.uIoc_of_le ha.le]; simp [ha.le]]
  exact betaIntegral_scaled_real hs hu ha

/-! ### The Fubini decomposition lemma -/

/-- The Dirichlet integrand evaluated at `Fin.snoc y' t` decomposes into the lower-dimensional
product in `y'` times the boundary factors in `t`. -/
lemma fubini_integrand_eq {k : ℕ} (α : Fin (k + 2) → ℝ) (y' : Fin k → ℝ) (t : ℝ) :
    (if (∀ i : Fin (k + 1), 0 < @Fin.snoc k (fun _ => ℝ) y' t i) ∧
        ∑ i, @Fin.snoc k (fun _ => ℝ) y' t i < 1 then
      (∏ i : Fin (k + 1), (@Fin.snoc k (fun _ => ℝ) y' t i) ^ (α ⟨i.val, by omega⟩ - 1)) *
        (1 - ∑ i : Fin (k + 1), @Fin.snoc k (fun _ => ℝ) y' t i) ^ (α ⟨k + 1, by omega⟩ - 1)
    else 0) =
    if (∀ j : Fin k, 0 < y' j) ∧ 0 < t ∧ (∑ j, y' j) + t < 1 then
      (∏ j : Fin k, (y' j) ^ (α ⟨j.val, by omega⟩ - 1)) *
        t ^ (α ⟨k, by omega⟩ - 1) *
        (1 - (∑ j, y' j) - t) ^ (α ⟨k + 1, by omega⟩ - 1)
    else 0 := by
  split_ifs with h1 h2 h2
  · rw [snoc_sum, snoc_prod]; ring_nf
  · exact absurd ((snoc_simplex_iff y' t).mp h1) h2
  · exact absurd ((snoc_simplex_iff y' t).mpr h2) h1
  · rfl

/-- The Dirichlet simplex integrand on `Fin (k + 1) → ℝ` is integrable when all parameters
`αᵢ > 0`. -/
lemma simplexIntegrand_integrable {k : ℕ}
    (α : Fin (k + 2) → ℝ) (hα : ∀ i, 0 < α i) :
    Integrable (fun y : Fin (k + 1) → ℝ =>
      if (∀ i, 0 < y i) ∧ ∑ i, y i < 1 then
        (∏ i : Fin (k + 1), (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i, y i) ^ (α ⟨k + 1, by omega⟩ - 1)
      else 0) volume := by
  induction k with
  | zero =>
    -- Base case: 1D beta integrand on Fin 1 → ℝ
    -- Use indicator_beta_integral to compute ∫ f = beta(α0, α1) ≠ 0
    apply Integrable.of_integral_ne_zero
    -- Transfer from Fin 1 → ℝ to ℝ
    have hmp := volume_preserving_funUnique (Fin 1) ℝ
    have h_eq : ∀ y : Fin 1 → ℝ,
        (if (∀ i : Fin 1, 0 < y i) ∧ ∑ i : Fin 1, y i < 1 then
          (∏ i : Fin 1, (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
            (1 - ∑ i : Fin 1, y i) ^ (α ⟨1, by omega⟩ - 1)
        else 0) =
        (fun t : ℝ => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1)
          else 0) (y 0) := by
      intro y
      simp only [Fin.sum_univ_one, Fin.prod_univ_one, Fin.forall_fin_one, Fin.val_zero]
      rfl
    simp_rw [h_eq]
    rw [show (fun y : Fin 1 → ℝ =>
        (fun t => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1) else 0) (y 0)) =
      (fun t : ℝ => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1) else 0) ∘
        (MeasurableEquiv.funUnique (Fin 1) ℝ) from by
      ext y; simp [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero]]
    change (∫ y : Fin 1 → ℝ,
      if 0 < y 0 ∧ y 0 < 1 then (y 0) ^ (α 0 - 1) * (1 - y 0) ^ (α 1 - 1) else 0) ≠ 0
    have := hmp.integral_comp'
      (f := MeasurableEquiv.funUnique (Fin 1) ℝ)
      (fun t : ℝ => if 0 < t ∧ t < 1 then t ^ (α 0 - 1) * (1 - t) ^ (α 1 - 1) else 0)
    simp only [MeasurableEquiv.funUnique_apply, Fin.default_eq_zero] at this
    erw [this, indicator_beta_integral (hα 0) (hα 1)]
    exact ne_of_gt (ProbabilityTheory.beta_pos (hα 0) (hα 1))
  | succ n ih =>
    -- Inductive step: decompose Fin (n+2) → ℝ ≃ ℝ × (Fin (n+1) → ℝ) via piFinSuccAbove
    set F : (Fin (n + 2) → ℝ) → ℝ := fun y =>
      if (∀ i, 0 < y i) ∧ ∑ i, y i < 1 then
        (∏ i : Fin (n + 2), (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
          (1 - ∑ i, y i) ^ (α ⟨n + 2, by omega⟩ - 1)
      else 0
    -- F = original function
    change Integrable F volume
    -- Decompose via piFinSuccAbove at Fin.last (n+1)
    set equiv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))
    have hmp := (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))).symm equiv
    rw [show Integrable F volume ↔
      Integrable (F ∘ equiv.symm) volume from
      (hmp.integrable_comp_emb equiv.symm.measurableEmbedding).symm]
    -- F ∘ equiv.symm : ℝ × (Fin (n+1) → ℝ) → ℝ decomposes as the simplex integrand
    -- Using fubini_integrand_eq, F(snoc y' t) = product form
    have h_snoc : ∀ p : ℝ × (Fin (n + 1) → ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))).symm p =
        Fin.snoc p.2 p.1 := by
      intro ⟨t, y'⟩
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
    set g : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun p =>
      if (∀ j, 0 < p.2 j) ∧ 0 < p.1 ∧ ∑ j, p.2 j + p.1 < 1 then
        (∏ j, p.2 j ^ (α ⟨↑j, by omega⟩ - 1)) * p.1 ^ (α ⟨n + 1, by omega⟩ - 1) *
          (1 - ∑ j, p.2 j - p.1) ^ (α ⟨n + 2, by omega⟩ - 1)
      else 0
    have hFg : F ∘ equiv.symm = g := by
      ext p; simp only [Function.comp_apply, equiv, h_snoc]
      -- F (Fin.snoc p.2 p.1) = g p, using fubini_integrand_eq
      -- Need to handle Fin (n+1+1) = Fin (n+2) for the snoc
      convert fubini_integrand_eq α p.2 p.1 using 1
    rw [hFg]
    -- Now prove Integrable g volume
    -- g is nonneg
    have hg_nonneg : ∀ p, 0 ≤ g p := by
      intro p; simp only [g]
      split_ifs with h
      · exact mul_nonneg (mul_nonneg
          (Finset.prod_nonneg fun j _ => rpow_nonneg (le_of_lt (h.1 j)) _)
          (rpow_nonneg (le_of_lt h.2.1) _))
          (rpow_nonneg (by linarith [h.2.2]) _)
      · exact le_refl 0
    -- For `y'` on the simplex, `g(·, y')` collapses to a 1D beta-type indicator in `t`.
    have hg_inner : ∀ y' : Fin (n + 1) → ℝ, (∀ j, 0 < y' j) → ∀ t : ℝ, g (t, y') =
        if 0 < t ∧ (∑ j, y' j) + t < 1 then
          (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) * t ^ (α ⟨n + 1, by omega⟩ - 1) *
            (1 - ∑ j, y' j - t) ^ (α ⟨n + 2, by omega⟩ - 1)
        else 0 := by
      intro y' hy1 t; simp only [g]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1.2 h2
      · exact absurd ⟨hy1, h2.1, h2.2⟩ h1
      · rfl
    -- For `y'` off the simplex, `g(·, y')` vanishes identically.
    have hg_zero : ∀ y' : Fin (n + 1) → ℝ, ¬ ((∀ j, 0 < y' j) ∧ ∑ j, y' j < 1) →
        (fun t => g (t, y')) = 0 := by
      intro y' hy; ext t; simp only [g]
      split_ifs with h
      · exact absurd ⟨h.1, by linarith [h.2.1, h.2.2]⟩ hy
      · rfl
    -- Use integrable_prod_iff' : need AEStronglyMeasurable + two conditions
    rw [Measure.volume_eq_prod]
    -- AEStronglyMeasurable g on product
    have hg_meas : AEStronglyMeasurable g (volume.prod volume) := by
      apply Measurable.aestronglyMeasurable
      simp only [g]
      -- Helper: p.2 j is measurable
      have hm_yj : ∀ j : Fin (n + 1), Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => p.2 j) :=
        fun j => (measurable_pi_apply j).comp measurable_snd
      -- Helper: ∑ p.2 j + p.1 is measurable
      have hm_sum_t : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => ∑ j, p.2 j + p.1) :=
        (Finset.measurable_sum _ fun j _ => hm_yj j).add measurable_fst
      -- Helper: 1 - ∑ y' - t is measurable (rewrite as 1 - (∑ y' + t))
      have hm_remainder : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) => 1 - ∑ j, p.2 j - p.1) := by
        have : (fun p : ℝ × (Fin (n + 1) → ℝ) => 1 - ∑ j, p.2 j - p.1) =
          fun p => (1 : ℝ) - (∑ j, p.2 j + p.1) := by ext p; ring
        rw [this]
        exact measurable_const.sub hm_sum_t
      apply Measurable.ite
      · -- MeasurableSet of the condition {p | (∀ j, 0 < p.2 j) ∧ 0 < p.1 ∧ ∑ p.2 j + p.1 < 1}
        refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
        · -- {p | ∀ j, 0 < p.2 j} = ⋂ j, {p | 0 < p.2 j}
          change MeasurableSet {a : ℝ × (Fin (n + 1) → ℝ) | ∀ j, 0 < a.2 j}
          rw [show {a : ℝ × (Fin (n + 1) → ℝ) | ∀ j, 0 < a.2 j} =
              ⋂ j, {a | 0 < a.2 j} from by ext p; simp [Set.mem_iInter]]
          exact MeasurableSet.iInter fun j => (hm_yj j) measurableSet_Ioi
        · exact measurable_fst measurableSet_Ioi
        · exact hm_sum_t measurableSet_Iio
      · -- Measurable body
        exact ((Finset.measurable_prod _ fun j _ => (hm_yj j).pow_const _).mul
          (measurable_fst.pow_const _)).mul
          (hm_remainder.pow_const _)
      · exact measurable_const
    rw [integrable_prod_iff' hg_meas]
    constructor
    · -- ∀ᵐ y', Integrable (fun t => g(t, y'))
      filter_upwards with y'
      by_cases hy : (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1
      · -- y' on simplex: inner integral is beta-type
        -- g(t, y') = C * (if 0 < t ∧ S+t < 1 then t^... * (1-S-t)^... else 0) for constant C, S
        rw [funext (hg_inner y' hy.1)]
        -- This is C * beta-type integrand, integrable by inner_integral_eq computation
        -- Use of_integral_ne_zero: ∫ = C * (1-S)^... * beta ≠ 0
        apply Integrable.of_integral_ne_zero
        rw [inner_integral_eq (hα ⟨n + 1, by omega⟩) (hα ⟨n + 2, by omega⟩) hy.2]
        exact mul_ne_zero (mul_ne_zero
          (ne_of_gt (Finset.prod_pos fun j _ => rpow_pos_of_pos (hy.1 j) _))
          (ne_of_gt (rpow_pos_of_pos (by linarith [hy.2] : 0 < 1 - ∑ j, y' j) _)))
          (ne_of_gt (ProbabilityTheory.beta_pos
            (hα ⟨n + 1, by omega⟩) (hα ⟨n + 2, by omega⟩)))
      · -- y' not on simplex: g(t, y') = 0 for all t
        rw [hg_zero y' hy]; exact integrable_zero _ _ _
    · -- Integrable (fun y' => ∫ t, ‖g(t, y')‖)
      -- Since g ≥ 0, ‖g‖ = g, so ∫ t, ‖g(t,y')‖ = ∫ t, g(t,y')
      -- By inner_integral_eq, this equals the lower-dim integrand * beta
      have h_norm_eq : (fun y' => ∫ t, ‖g (t, y')‖) =
          fun y' => ∫ t, g (t, y') := by
        ext y'; congr 1; ext t
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg (t, y'))]
      rw [h_norm_eq]
      -- Compute inner integral using same logic as h_inner in simplexIntegral_fubini
      have h_inner_val : ∀ y' : Fin (n + 1) → ℝ,
          ∫ t, g (t, y') =
          if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
              (1 - ∑ j, y' j) ^ (α ⟨n + 1, by omega⟩ + α ⟨n + 2, by omega⟩ - 1) *
              ProbabilityTheory.beta (α ⟨n + 1, by omega⟩) (α ⟨n + 2, by omega⟩)
          else 0 := by
        intro y'
        by_cases hy : (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1
        · rw [if_pos hy]
          simp_rw [hg_inner y' hy.1]
          exact inner_integral_eq (hα ⟨n + 1, by omega⟩) (hα ⟨n + 2, by omega⟩) hy.2
        · rw [if_neg hy]; simp [hg_zero y' hy]
      simp_rw [h_inner_val]
      -- Factor out beta constant
      have h_factor : ∀ y' : Fin (n + 1) → ℝ,
          (if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
              (1 - ∑ j, y' j) ^ (α ⟨n + 1, by omega⟩ + α ⟨n + 2, by omega⟩ - 1) *
              ProbabilityTheory.beta (α ⟨n + 1, by omega⟩) (α ⟨n + 2, by omega⟩)
          else 0) =
          ProbabilityTheory.beta (α ⟨n + 1, by omega⟩) (α ⟨n + 2, by omega⟩) *
          (if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
              (1 - ∑ j, y' j) ^ (α ⟨n + 1, by omega⟩ + α ⟨n + 2, by omega⟩ - 1)
          else 0) := by
        intro y'; split_ifs <;> ring
      simp_rw [h_factor]
      apply Integrable.const_mul
      -- Need: Integrable (fun y' => if ... then ∏ * (1-∑)^(αn+1+αn+2-1) else 0)
      -- This is the (n+1)-dim integrand with merged last two params
      -- The IH gives integrability for any Fin (n+2) → ℝ params
      -- mergeLastTwo α has merged params: αj for j < n+1, α_{n+1}+α_{n+2} for j = n+1
      -- Need to match the integrand with IH applied to mergeLastTwo α
      have h_match : (fun y' : Fin (n + 1) → ℝ =>
          if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
              (1 - ∑ j, y' j) ^ (α ⟨n + 1, by omega⟩ + α ⟨n + 2, by omega⟩ - 1)
          else 0) =
        (fun y' : Fin (n + 1) → ℝ =>
          if (∀ i, 0 < y' i) ∧ ∑ i, y' i < 1 then
            (∏ i : Fin (n + 1), (y' i) ^ (mergeLastTwo α ⟨i.val, by omega⟩ - 1)) *
              (1 - ∑ i, y' i) ^ (mergeLastTwo α ⟨n + 1, by omega⟩ - 1)
          else 0) := by
        ext y'; split_ifs with h <;> [skip; rfl]
        congr 1
        · apply Finset.prod_congr rfl; intro j _
          congr 2
          simp [mergeLastTwo, j.isLt]
        · congr 1
          simp [mergeLastTwo]
      rw [h_match]
      exact ih (mergeLastTwo α) (mergeLastTwo_pos hα)

/-- The Dirichlet simplex integral in dimension `k + 2` reduces to dimension `k + 1` by peeling off
the last coordinate: It equals `beta (α k) (α (k+1))` times the integral in the merged parameters
`mergeLastTwo α`. -/
lemma simplexIntegral_fubini {k : ℕ} (hk : 1 ≤ k)
    (α : Fin (k + 2) → ℝ) (hα : ∀ i, 0 < α i) :
    simplexIntegral (k + 2) α =
    ProbabilityTheory.beta (α ⟨k, by omega⟩) (α ⟨k + 1, by omega⟩) *
      simplexIntegral (k + 1) (mergeLastTwo α) := by
  -- Unfold LHS to integral over Fin (k+1)
  change (∫ y : Fin (k + 1) → ℝ,
    if (∀ i, 0 < y i) ∧ ∑ i, y i < 1 then
      (∏ i : Fin (k + 1), (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
        (1 - ∑ i, y i) ^ (α ⟨k + 1, by omega⟩ - 1)
    else 0) = _
  -- Step 1: Change variables: Fin (k+1) → ℝ  ≃  ℝ × (Fin k → ℝ) via snoc
  -- piFinSuccAbove.symm at Fin.last k is snocEquiv
  set F : (Fin (k + 1) → ℝ) → ℝ := fun y =>
    if (∀ i, 0 < y i) ∧ ∑ i, y i < 1 then
      (∏ i : Fin (k + 1), (y i) ^ (α ⟨i.val, by omega⟩ - 1)) *
        (1 - ∑ i, y i) ^ (α ⟨k + 1, by omega⟩ - 1)
    else 0 with hF_def
  -- Use piFinSuccAbove to change variables
  have hmp_symm : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm
      volume volume :=
    (volume_preserving_piFinSuccAbove _ _).symm _
  rw [show ∫ y, F y = ∫ p : ℝ × (Fin k → ℝ),
      F ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k)).symm p) from
    (hmp_symm.integral_comp' _).symm]
  -- piFinSuccAbove.symm at last = snocEquiv, so equiv.symm (t, y') = Fin.snoc y' t
  have h_snoc : ∀ p : ℝ × (Fin k → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k)).symm p =
      Fin.snoc p.2 p.1 := by
    intro ⟨t, y'⟩
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
    rfl
  simp_rw [h_snoc]
  -- Step 2: Rewrite the integrand using fubini_integrand_eq
  simp_rw [hF_def, fubini_integrand_eq]
  -- Step 3: Swap product order to (Fin k → ℝ) × ℝ, then Fubini
  -- Write p = (t, y') and swap to integrate y' first (outer), t second (inner)
  -- Step 3: Fubini via integral_prod_symm
  -- The integrand g : ℝ × (Fin k → ℝ) → ℝ is nonneg and supported on the simplex (bounded).
  set g : ℝ × (Fin k → ℝ) → ℝ := fun p =>
    if (∀ j, 0 < p.2 j) ∧ 0 < p.1 ∧ ∑ j, p.2 j + p.1 < 1 then
      (∏ j, p.2 j ^ (α ⟨↑j, by omega⟩ - 1)) * p.1 ^ (α ⟨k, by omega⟩ - 1) *
        (1 - ∑ j, p.2 j - p.1) ^ (α ⟨k + 1, by omega⟩ - 1)
    else 0 with hg_def
  -- g is nonneg
  have hg_nonneg : ∀ p, 0 ≤ g p := by
    intro p; simp only [hg_def]
    split_ifs with h
    · apply mul_nonneg
      · apply mul_nonneg
        · exact Finset.prod_nonneg fun j _ => rpow_nonneg (le_of_lt (h.1 j)) _
        · exact rpow_nonneg (le_of_lt h.2.1) _
      · exact rpow_nonneg (by linarith [h.2.2]) _
    · exact le_refl 0
  -- Integrability of g on the product measure
  -- g = F ∘ equiv.symm, so integrability transfers via MeasurePreserving
  have hg_eq : g = F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k)).symm := by
    ext p; simp only [hg_def, hF_def, Function.comp_apply, h_snoc, fubini_integrand_eq]
  have hg_int : Integrable g (volume : Measure (ℝ × (Fin k → ℝ))) := by
    rw [hg_eq]
    rw [hmp_symm.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last k)).symm.measurableEmbedding]
    exact simplexIntegrand_integrable α hα
  rw [Measure.volume_eq_prod (α := ℝ) (β := Fin k → ℝ)] at hg_int ⊢
  rw [integral_prod_symm g hg_int]
  -- Goal: ∫ y, ∫ t, g(t, y) = beta * simplexIntegral(k+1, mergeLastTwo)
  -- Step 4a: Evaluate inner integral for each y' using inner_integral_eq
  have h_inner : ∀ y' : Fin k → ℝ,
      ∫ t : ℝ, g (t, y') =
      if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
        (∏ j : Fin k, (y' j) ^ (α ⟨j.val, by omega⟩ - 1)) *
          (1 - ∑ j, y' j) ^ (α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩ - 1) *
          ProbabilityTheory.beta (α ⟨k, by omega⟩) (α ⟨k + 1, by omega⟩)
      else 0 := by
    intro y'; simp only [hg_def]
    by_cases hy : (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1
    · rw [if_pos hy]
      -- Inner integral: ∫ t, if ... ∧ 0 < t ∧ S+t < 1 then C * t^... * ...^... else 0
      -- where C = ∏ y'j^... and S = ∑ y'j
      -- The condition ∀ j, 0 < y' j is already satisfied, so simplify
      have h_simp : ∀ t : ℝ,
          (if (∀ j, 0 < y' j) ∧ 0 < t ∧ ∑ j, y' j + t < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) * t ^ (α ⟨k, by omega⟩ - 1) *
              (1 - ∑ j, y' j - t) ^ (α ⟨k + 1, by omega⟩ - 1)
          else 0) =
          (if 0 < t ∧ (∑ j, y' j) + t < 1 then
            (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) * t ^ (α ⟨k, by omega⟩ - 1) *
              (1 - (∑ j, y' j) - t) ^ (α ⟨k + 1, by omega⟩ - 1)
          else 0) := by
        intro t; split_ifs with h1 h2 h2
        · rfl
        · exact absurd h1.2 h2
        · exact absurd ⟨hy.1, h2.1, h2.2⟩ h1
        · rfl
      simp_rw [h_simp]
      exact inner_integral_eq (hα ⟨k, by omega⟩) (hα ⟨k + 1, by omega⟩) hy.2
    · rw [if_neg hy]
      have : (fun t => (if (∀ j : Fin k, 0 < y' j) ∧ 0 < t ∧ ∑ j, y' j + t < 1 then
          (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) * t ^ (α ⟨k, by omega⟩ - 1) *
            (1 - ∑ j, y' j - t) ^ (α ⟨k + 1, by omega⟩ - 1) else 0)) = 0 := by
        ext t; split_ifs with h
        · exact absurd ⟨h.1, by linarith [h.2.1, h.2.2]⟩ hy
        · rfl
      simp [this]
  simp_rw [h_inner]
  -- Step 4b: Factor beta out of the integral
  have h_factor : ∀ y' : Fin k → ℝ,
      (if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
        (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
          (1 - ∑ j, y' j) ^ (α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩ - 1) *
          ProbabilityTheory.beta (α ⟨k, by omega⟩) (α ⟨k + 1, by omega⟩)
      else 0) =
      ProbabilityTheory.beta (α ⟨k, by omega⟩) (α ⟨k + 1, by omega⟩) *
      (if (∀ j, 0 < y' j) ∧ ∑ j, y' j < 1 then
        (∏ j, y' j ^ (α ⟨↑j, by omega⟩ - 1)) *
          (1 - ∑ j, y' j) ^ (α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩ - 1)
      else 0) := by
    intro y'; split_ifs <;> ring
  simp_rw [h_factor, integral_const_mul]
  congr 1
  -- Step 4c: Match with simplexIntegral (k+1) (mergeLastTwo α)
  -- Need: the integrand (∏ y'j^(αj-1)) * (1-S)^(αk+α_{k+1}-1) on simplex
  -- equals simplexIntegral (k+1) (mergeLastTwo α) integrand
  -- mergeLastTwo α ⟨j, _⟩ = α ⟨j, _⟩ for j < k, and = α_k + α_{k+1} for j = k
  show _ = simplexIntegral (k + 1) (mergeLastTwo α)
  simp only [simplexIntegral, show k + 1 ≠ 0 from by omega, dite_false,
    show k + 1 ≠ 1 from by omega, show k + 1 - 1 = k from by omega]
  apply integral_congr_ae
  filter_upwards with y'
  split_ifs with h1 h2 h2
  · -- Both on simplex: match products
    congr 1
    · apply Finset.prod_congr rfl; intro j _
      congr 2
      simp [mergeLastTwo, j.isLt]
    · congr 1
      simp [mergeLastTwo]
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-! ### The Dirichlet integral equals the multivariate beta function -/

/-- **Dirichlet integral:** for parameters `αᵢ > 0` and dimension `k ≥ 2`, the unnormalized
Dirichlet integral over the simplex equals the multivariate beta function
`(∏ i, Γ(αᵢ)) / Γ(∑ i, αᵢ)`. -/
theorem simplexIntegral_eq_multivariateBeta {k : ℕ} (hk : 2 ≤ k)
    {α : Fin k → ℝ} (hα : ∀ i, 0 < α i) :
    simplexIntegral k α =
    (∏ i, Real.Gamma (α i)) / Real.Gamma (∑ i, α i) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  induction m with
  | zero =>
    rw [simplexIntegral_two hα]
    unfold ProbabilityTheory.beta
    rw [Fin.prod_univ_two, Fin.sum_univ_two]
  | succ n ih =>
    rw [simplexIntegral_fubini (by omega : 1 ≤ n + 1) _ hα]
    rw [ih (by omega) (mergeLastTwo_pos hα)]
    rw [← multivariateBeta_merge _ hα]

end MeasureTheory
