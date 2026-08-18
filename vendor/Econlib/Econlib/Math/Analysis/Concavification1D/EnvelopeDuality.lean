/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.Envelope

open MeasureTheory Set

/-!
# Strong duality: Concave envelope equals two-point value

On `[a, b]`, for continuous `φ`, the concave envelope of `φ` at `μ` coincides with the optimal
mean-`μ` two-point splitting value (`twoPointValue`). This file also records that the concave
envelope is concave.

## Main statements

* `twoPointValue_le_concaveEnvelope` — the `≤` direction (each splitting is dominated by every
  affine majorant).
* `isAffineMajorant_secant_of_twoPointOptimum` — the secant of a non-degenerate two-point optimum
  is an affine majorant.
* `concaveEnvelope_eq_twoPointValue` — the strong-duality identity.
* `concaveEnvelope_concaveOn` — the concave envelope is concave.

## Tags

concave envelope, two-point value, strong duality, affine majorant, concavification
-/

@[expose] public section

/-- The two-point value is bounded above by the concave envelope: Each feasible two-point splitting
of the mean `μ` is dominated, value-wise, by every affine majorant evaluated at `μ`, and the
infimum over majorants is the concave envelope. -/
lemma twoPointValue_le_concaveEnvelope
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {μ : ℝ} (hμ : μ ∈ Icc a b) :
    twoPointValue a b φ μ ≤ concaveEnvelope a b φ μ := by
  -- It suffices to bound the two-point value by every affine majorant value `m * μ + c`, then
  -- take the infimum (which is `concaveEnvelope a b φ μ`).
  unfold concaveEnvelope
  refine le_csInf ?_ ?_
  · obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ.continuousOn
    exact ⟨m₀ * μ + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩
  rintro _ ⟨m, c, hmaj, rfl⟩
  -- Bound the supremum (`twoPointValue`) by `m * μ + c`.
  refine csSup_le ((twoPointFeasibleSet_nonempty hμ).image _) ?_
  rintro v ⟨⟨xL, xR, q⟩, ⟨hxL, hxR, hq_mem, hmean⟩, rfl⟩
  -- The objective at a feasible splitting is dominated by the affine majorant at `μ`.
  have hφxL : φ xL ≤ m * xL + c := hmaj xL hxL
  have hφxR : φ xR ≤ m * xR + c := hmaj xR hxR
  have hq0 : 0 ≤ q := hq_mem.1
  have h1q0 : 0 ≤ 1 - q := by linarith [hq_mem.2]
  have hbound :
      twoPointObjective φ (xL, xR, q) ≤ (1 - q) * (m * xL + c) + q * (m * xR + c) := by
    simp only [twoPointObjective]
    exact add_le_add (mul_le_mul_of_nonneg_left hφxL h1q0)
      (mul_le_mul_of_nonneg_left hφxR hq0)
  -- The dominating value collapses to `m * μ + c` by the barycentric identity.
  have hcollapse : (1 - q) * (m * xL + c) + q * (m * xR + c) = m * μ + c := by
    rw [← hmean]; ring
  rw [hcollapse] at hbound
  exact hbound

/-- **Secant line of an interior two-point optimum is an affine majorant.** If `(xL, xR, q)` is a
two-point optimum of `φ`-expectation at mean `μ` with `xL < xR`, then the line through `(xL, φ xL)`
and `(xR, φ xR)` majorizes `φ` on `[a, b]`. This is the non-degenerate building block for the
strong-duality identity `concaveEnvelope = twoPointValue`. -/
lemma isAffineMajorant_secant_of_twoPointOptimum
    -- Continuity matches the lemma's continuous setting; the algebraic argument doesn't use it.
    {a b xL xR q : ℝ} {φ : ℝ → ℝ} (_hφ : Continuous φ)
    (hxL : xL ∈ Icc a b) (hxR : xR ∈ Icc a b) (hxLR : xL < xR)
    (hq_pos : 0 < q) (hq_lt1 : q < 1)
    (hmean : (1 - q) * xL + q * xR ∈ Icc a b)
    (hopt : IsMaxOn (twoPointObjective φ) (twoPointFeasibleSet a b ((1 - q) * xL + q * xR))
              (xL, xR, q)) :
    IsAffineMajorant a b φ
      ((φ xR - φ xL) / (xR - xL)) (φ xL - (φ xR - φ xL) / (xR - xL) * xL) := by
  set μ := (1 - q) * xL + q * xR with hμ_def
  set m := (φ xR - φ xL) / (xR - xL) with hm_def
  set c := φ xL - m * xL with hc_def
  have hxR_sub_xL_pos : 0 < xR - xL := sub_pos.mpr hxLR
  have hxR_sub_xL_ne : xR - xL ≠ 0 := ne_of_gt hxR_sub_xL_pos
  have hline_xL : m * xL + c = φ xL := by simp [hc_def]
  have hline_xR : m * xR + c = φ xR := by
    rw [hc_def]
    have : m * xR + (φ xL - m * xL) = m * (xR - xL) + φ xL := by ring
    rw [this, hm_def, div_mul_cancel₀ _ hxR_sub_xL_ne]
    ring
  -- Barycentric identity: `L(μ) = (1-q) φ xL + q φ xR`.
  have hline_μ : m * μ + c = (1 - q) * φ xL + q * φ xR := by
    have hrw : m * ((1 - q) * xL + q * xR) + c
             = (1 - q) * (m * xL + c) + q * (m * xR + c) := by ring
    rw [hμ_def, hrw, hline_xL, hline_xR]
  -- Mean decomposition identities.
  have hxR_sub_μ : xR - μ = (1 - q) * (xR - xL) := by rw [hμ_def]; ring
  have hμ_sub_xL : μ - xL = q * (xR - xL) := by rw [hμ_def]; ring
  -- Optimality bound on any pair at μ.
  have hv_def : twoPointObjective φ (xL, xR, q) = (1 - q) * φ xL + q * φ xR := by
    simp [twoPointObjective]
  intro t ht
  by_contra hfail
  push Not at hfail
  -- `hfail : m * t + c < φ t`. Derive a contradiction with `hopt`.
  rcases eq_or_ne t xL with ht_eq_xL | ht_ne_xL
  · rw [ht_eq_xL, hline_xL] at hfail; exact absurd hfail (lt_irrefl _)
  rcases eq_or_ne t xR with ht_eq_xR | ht_ne_xR
  · rw [ht_eq_xR, hline_xR] at hfail; exact absurd hfail (lt_irrefl _)
  -- Split by position of t relative to μ.
  rcases lt_trichotomy t μ with ht_lt_μ | ht_eq_μ | ht_gt_μ
  · -- `t < μ < xR`: replace `xL` in the pair with `t`.
    have hμ_lt_xR : μ < xR := by
      have : 0 < (1 - q) * (xR - xL) := mul_pos (by linarith) hxR_sub_xL_pos
      linarith [hxR_sub_μ]
    have ht_lt_xR : t < xR := lt_trans ht_lt_μ hμ_lt_xR
    have hxR_sub_t_pos : 0 < xR - t := sub_pos.mpr ht_lt_xR
    set q_new := (μ - t) / (xR - t) with hq_new_def
    have hq_new_nn : 0 ≤ q_new :=
      div_nonneg (by linarith) (le_of_lt hxR_sub_t_pos)
    have hq_new_le1 : q_new ≤ 1 := by
      rw [hq_new_def, div_le_one hxR_sub_t_pos]; linarith
    have hmean_new : (1 - q_new) * t + q_new * xR = μ := by
      rw [hq_new_def]
      field_simp
      ring
    have hpair_mem : (t, xR, q_new) ∈ twoPointFeasibleSet a b μ :=
      ⟨ht, hxR, ⟨hq_new_nn, hq_new_le1⟩, hmean_new⟩
    have hopt_bound :
        twoPointObjective φ (t, xR, q_new) ≤ (1 - q) * φ xL + q * φ xR := by
      have := hopt hpair_mem
      simpa [hv_def] using this
    -- New value: `(1 - q_new) φ t + q_new φ xR`.
    -- Claim: this strictly exceeds `(1 - q) φ xL + q φ xR`, contradicting `hopt_bound`.
    have hobj_new_eq :
        twoPointObjective φ (t, xR, q_new) = (1 - q_new) * φ t + q_new * φ xR := by
      simp [twoPointObjective]
    -- Key algebraic identity:
    --   (1 - q_new) φ t + q_new φ xR - ((1 - q) φ xL + q φ xR)
    --     = ((xR - μ) / (xR - t)) * (φ t - (m t + c))
    have hdiff :
        (1 - q_new) * φ t + q_new * φ xR - ((1 - q) * φ xL + q * φ xR)
          = ((xR - μ) / (xR - t)) * (φ t - (m * t + c)) := by
      rw [hq_new_def]
      have h1 : m * t + c = ((xR - t) / (xR - xL)) * φ xL
                            + ((t - xL) / (xR - xL)) * φ xR := by
        rw [hc_def, hm_def]
        field_simp
        ring
      rw [h1, hμ_def]
      field_simp
      ring
    have hfactor_pos : 0 < (xR - μ) / (xR - t) := by
      apply div_pos _ hxR_sub_t_pos
      rw [hxR_sub_μ]
      exact mul_pos (by linarith) hxR_sub_xL_pos
    have hprod_pos :
        0 < ((xR - μ) / (xR - t)) * (φ t - (m * t + c)) :=
      mul_pos hfactor_pos (sub_pos.mpr hfail)
    have hstrict :
        (1 - q) * φ xL + q * φ xR < (1 - q_new) * φ t + q_new * φ xR := by linarith
    rw [hobj_new_eq] at hopt_bound
    linarith
  · -- `t = μ`: use the degenerate pair `(μ, μ, 0)`.
    have hdegen : (μ, μ, (0 : ℝ)) ∈ twoPointFeasibleSet a b μ :=
      ⟨hmean, hmean, ⟨le_refl 0, zero_le_one⟩, by simp⟩
    have hopt_bound :
        twoPointObjective φ (μ, μ, (0 : ℝ)) ≤ (1 - q) * φ xL + q * φ xR := by
      have := hopt hdegen
      simpa [hv_def] using this
    have hval : twoPointObjective φ (μ, μ, (0 : ℝ)) = φ μ := by
      simp [twoPointObjective]
    rw [hval] at hopt_bound
    -- `hfail` with `t = μ` gives `m * μ + c < φ μ`, but `m * μ + c = (1-q) φ xL + q φ xR`.
    rw [ht_eq_μ, hline_μ] at hfail
    linarith
  · -- `xL < μ < t`: replace `xR` in the pair with `t`.
    have hxL_lt_μ : xL < μ := by
      have : 0 < q * (xR - xL) := mul_pos hq_pos hxR_sub_xL_pos
      linarith [hμ_sub_xL]
    have hxL_lt_t : xL < t := lt_trans hxL_lt_μ ht_gt_μ
    have ht_sub_xL_pos : 0 < t - xL := sub_pos.mpr hxL_lt_t
    set q_new := (μ - xL) / (t - xL) with hq_new_def
    have hq_new_nn : 0 ≤ q_new :=
      div_nonneg (by linarith) (le_of_lt ht_sub_xL_pos)
    have hq_new_le1 : q_new ≤ 1 := by
      rw [hq_new_def, div_le_one ht_sub_xL_pos]; linarith
    have hmean_new : (1 - q_new) * xL + q_new * t = μ := by
      rw [hq_new_def]
      field_simp
      ring
    have hpair_mem : (xL, t, q_new) ∈ twoPointFeasibleSet a b μ :=
      ⟨hxL, ht, ⟨hq_new_nn, hq_new_le1⟩, hmean_new⟩
    have hopt_bound :
        twoPointObjective φ (xL, t, q_new) ≤ (1 - q) * φ xL + q * φ xR := by
      have := hopt hpair_mem
      simpa [hv_def] using this
    have hobj_new_eq :
        twoPointObjective φ (xL, t, q_new) = (1 - q_new) * φ xL + q_new * φ t := by
      simp [twoPointObjective]
    -- Key algebraic identity (symmetric to the left case):
    have hdiff :
        (1 - q_new) * φ xL + q_new * φ t - ((1 - q) * φ xL + q * φ xR)
          = ((μ - xL) / (t - xL)) * (φ t - (m * t + c)) := by
      rw [hq_new_def]
      have h1 : m * t + c = ((xR - t) / (xR - xL)) * φ xL
                            + ((t - xL) / (xR - xL)) * φ xR := by
        rw [hc_def, hm_def]
        field_simp
        ring
      rw [h1, hμ_def]
      field_simp
      ring
    have hfactor_pos : 0 < (μ - xL) / (t - xL) := by
      apply div_pos _ ht_sub_xL_pos
      rw [hμ_sub_xL]
      exact mul_pos hq_pos hxR_sub_xL_pos
    have hprod_pos :
        0 < ((μ - xL) / (t - xL)) * (φ t - (m * t + c)) :=
      mul_pos hfactor_pos (sub_pos.mpr hfail)
    have hstrict :
        (1 - q) * φ xL + q * φ xR < (1 - q_new) * φ xL + q_new * φ t := by linarith
    rw [hobj_new_eq] at hopt_bound
    linarith

/-- **Degenerate case of the strong-duality step.** If every two-point splitting of the mean `μ` on
`[a, b]` has `φ`-expectation at most `φ μ` — equivalently, the two-point optimum at `μ` is the
point mass — then `concaveEnvelope a b φ μ ≤ φ μ`. -/
private lemma concaveEnvelope_le_phi_of_degenerate_twoPointOptimum
    {a b μ : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hμ : μ ∈ Icc a b)
    (hchord : ∀ p ∈ twoPointFeasibleSet a b μ, twoPointObjective φ p ≤ φ μ) :
    concaveEnvelope a b φ μ ≤ φ μ := by
  -- **Chord inequality extraction.** For `t₁ ∈ [a, μ)` and `t₂ ∈ (μ, b]`, the pair
  --   `(t₁, t₂, (μ - t₁)/(t₂ - t₁))` is feasible at mean `μ`, giving
  --   `(t₂ - μ) φ t₁ + (μ - t₁) φ t₂ ≤ (t₂ - t₁) φ μ`.
  have hchord_ineq : ∀ t₁ t₂ : ℝ, t₁ ∈ Icc a μ → t₂ ∈ Icc μ b → t₁ < t₂ →
      (t₂ - μ) * φ t₁ + (μ - t₁) * φ t₂ ≤ (t₂ - t₁) * φ μ := by
    intro t₁ t₂ ht₁ ht₂ hlt
    have ht₁' : t₁ ∈ Icc a b := ⟨ht₁.1, le_trans ht₁.2 hμ.2⟩
    have ht₂' : t₂ ∈ Icc a b := ⟨le_trans hμ.1 ht₂.1, ht₂.2⟩
    have ht₂_sub_t₁_pos : 0 < t₂ - t₁ := sub_pos.mpr hlt
    set q' := (μ - t₁) / (t₂ - t₁) with hq'_def
    have hq'_nn : 0 ≤ q' :=
      div_nonneg (by linarith [ht₁.2]) (le_of_lt ht₂_sub_t₁_pos)
    have hq'_le1 : q' ≤ 1 := by
      rw [hq'_def, div_le_one ht₂_sub_t₁_pos]; linarith [ht₂.1]
    have hmean' : (1 - q') * t₁ + q' * t₂ = μ := by
      rw [hq'_def]; field_simp; ring
    have hpair_mem : (t₁, t₂, q') ∈ twoPointFeasibleSet a b μ :=
      ⟨ht₁', ht₂', ⟨hq'_nn, hq'_le1⟩, hmean'⟩
    have hobj_le := hchord (t₁, t₂, q') hpair_mem
    simp only [twoPointObjective] at hobj_le
    -- `(1 - q') φ t₁ + q' φ t₂ ≤ φ μ`. Multiply by `t₂ - t₁ > 0`.
    have hstep : ((1 - q') * φ t₁ + q' * φ t₂) * (t₂ - t₁) ≤ φ μ * (t₂ - t₁) :=
      mul_le_mul_of_nonneg_right hobj_le (le_of_lt ht₂_sub_t₁_pos)
    have hexpand : ((1 - q') * φ t₁ + q' * φ t₂) * (t₂ - t₁)
                  = (t₂ - μ) * φ t₁ + (μ - t₁) * φ t₂ := by
      rw [hq'_def]
      field_simp
      ring
    linarith [hexpand ▸ hstep]
  -- **Case split** on the position of `μ`.
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · -- `a = b`, so `μ = a = b` and `[a, b] = {a}`. Any majorant with `c = φ a` works.
    have hμ_eq : μ = a := by rw [← hab_eq] at hμ; exact le_antisymm hμ.2 hμ.1
    have hmaj0 : IsAffineMajorant a b φ 0 (φ a) := by
      intro t ht
      have ht_eq_a : t = a := by rw [← hab_eq] at ht; exact le_antisymm ht.2 ht.1
      rw [ht_eq_a]; simp
    have := concaveEnvelope_le_affineMajorant hmaj0 hμ
    simp [hμ_eq] at this ⊢
    linarith
  -- `a < b`. Case on position of `μ`.
  have hμ_a : a ≤ μ := hμ.1
  have hμ_b : μ ≤ b := hμ.2
  rcases eq_or_lt_of_le hμ_a with hμ_eq_a | ha_lt_μ
  · -- `μ = a`. ε-majorant limit argument.
    subst hμ_eq_a
    -- Need `concaveEnvelope a b φ a ≤ φ a`. Build ε-approximating majorants.
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- By continuity of `φ` at `a`, `∃ δ > 0, ∀ t ∈ [a, a+δ], |φ t - φ a| < ε/2`.
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousAt_iff.mp (hφ.continuousAt (x := a)) (ε / 2) (by linarith)
    -- `M := sSup (φ '' Icc a b) - φ a + 1` (upper bound on excess over `φ a`).
    obtain ⟨Mp, hMp_mem, hMp_max⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab_lt.le) hφ.continuousOn
    set M := φ Mp - φ a + 1 with hM_def
    have hφ_a_le_Mp : φ a ≤ φ Mp := hMp_max (Set.left_mem_Icc.mpr hab_lt.le)
    have hM_pos : 0 < M := by rw [hM_def]; linarith
    have hφ_bound : ∀ t ∈ Icc a b, φ t - φ a ≤ M := by
      intro t ht
      have : φ t ≤ φ Mp := hMp_max ht
      rw [hM_def]; linarith
    -- Choose `δ' := min (δ/2) ((b - a) / 2)` so `a + δ' ≤ b` and `δ' < δ` strictly.
    set δ' := min (δ / 2) ((b - a) / 2) with hδ'_def
    have hδ'_pos : 0 < δ' := lt_min (by linarith) (by linarith)
    have hδ'_lt_δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ'_le_half : δ' ≤ (b - a) / 2 := min_le_right _ _
    have ha_plus_δ'_le_b : a + δ' ≤ b := by linarith
    -- Choose `m := M / δ' + 1`.
    set m := M / δ' + 1 with hm_def
    have hm_pos : 0 < m := by
      have : 0 < M / δ' := div_pos hM_pos hδ'_pos
      linarith
    -- Build the majorant `L(t) := m * (t - a) + (φ a + ε)`, i.e., slope m, intercept.
    set c := φ a + ε - m * a with hc_def
    have hmaj : IsAffineMajorant a b φ m c := by
      intro t ht
      rw [hc_def]
      -- Goal: `φ t ≤ m * t + (φ a + ε - m * a) = m * (t - a) + φ a + ε`.
      have hrw : m * t + (φ a + ε - m * a) = m * (t - a) + (φ a + ε) := by ring
      rw [hrw]
      -- Two sub-cases: t ∈ [a, a + δ'] (use continuity) or t ∈ [a + δ', b] (use m large).
      by_cases ht_close : t ≤ a + δ'
      · -- Close to `a`: continuity gives `|φ t - φ a| < ε/2 < ε`.
        have ht_dist : dist t a < δ := by
          have ht_ge : a ≤ t := ht.1
          rw [Real.dist_eq]
          have h_abs : |t - a| = t - a := abs_of_nonneg (by linarith)
          rw [h_abs]
          linarith [hδ'_lt_δ]
        have := hδ ht_dist
        rw [Real.dist_eq] at this
        have hφ_close : φ t - φ a < ε / 2 := by
          linarith [abs_lt.mp this]
        have hmta_nn : 0 ≤ m * (t - a) := mul_nonneg (le_of_lt hm_pos) (by linarith [ht.1])
        linarith
      · -- Far from `a`: `t - a > δ'`, so `m * (t - a) > m * δ' ≥ M ≥ φ t - φ a`.
        push Not at ht_close
        have ht_ge : a + δ' < t := ht_close
        have ht_sub_a_ge : δ' < t - a := by linarith
        have hm_ta : m * δ' ≤ m * (t - a) :=
          mul_le_mul_of_nonneg_left (le_of_lt ht_sub_a_ge) (le_of_lt hm_pos)
        have hm_δ'_ge_M : M ≤ m * δ' := by
          rw [hm_def]
          have : M / δ' * δ' = M := div_mul_cancel₀ M (ne_of_gt hδ'_pos)
          nlinarith [this, hδ'_pos]
        have hM_ge_excess : φ t - φ a ≤ M := hφ_bound t ht
        linarith
    have hLμ : m * a + c = φ a + ε := by rw [hc_def]; ring
    have := concaveEnvelope_le_affineMajorant hmaj hμ
    linarith [hLμ]
  rcases eq_or_lt_of_le hμ_b with hμ_eq_b | hμ_lt_b
  · -- `μ = b`. Symmetric ε-argument: build majorant through `(b, φ b + ε)` with very
    -- negative slope using continuity at `b`.
    subst hμ_eq_b
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousAt_iff.mp (hφ.continuousAt (x := μ)) (ε / 2) (by linarith)
    obtain ⟨Mp, hMp_mem, hMp_max⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab_lt.le) hφ.continuousOn
    set M := φ Mp - φ μ + 1 with hM_def
    have hφ_μ_le_Mp : φ μ ≤ φ Mp := hMp_max (Set.right_mem_Icc.mpr hab_lt.le)
    have hM_pos : 0 < M := by rw [hM_def]; linarith
    have hφ_bound : ∀ t ∈ Icc a μ, φ t - φ μ ≤ M := by
      intro t ht
      have : φ t ≤ φ Mp := hMp_max ht
      rw [hM_def]; linarith
    set δ' := min (δ / 2) ((μ - a) / 2) with hδ'_def
    have hδ'_pos : 0 < δ' := lt_min (by linarith) (by linarith)
    have hδ'_lt_δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ'_le_half : δ' ≤ (μ - a) / 2 := min_le_right _ _
    have ha_le_μ_sub_δ' : a ≤ μ - δ' := by linarith
    -- Slope `m := -(M / δ' + 1)` (very negative).
    set m := -(M / δ' + 1) with hm_def
    have hm_neg : m < 0 := by
      have : 0 < M / δ' := div_pos hM_pos hδ'_pos
      rw [hm_def]; linarith
    set c := φ μ + ε - m * μ with hc_def
    have hmaj : IsAffineMajorant a μ φ m c := by
      intro t ht
      rw [hc_def]
      have hrw : m * t + (φ μ + ε - m * μ) = m * (t - μ) + (φ μ + ε) := by ring
      rw [hrw]
      by_cases ht_close : μ - δ' ≤ t
      · -- Close to `μ` (on the left): continuity gives `|φ t - φ μ| < ε/2`.
        have ht_dist : dist t μ < δ := by
          rw [Real.dist_eq]
          have ht_le_μ : t ≤ μ := ht.2
          have h_abs : |t - μ| = μ - t := by
            rw [abs_of_nonpos (sub_nonpos.mpr ht_le_μ)]; ring
          rw [h_abs]
          linarith [hδ'_lt_δ]
        have := hδ ht_dist
        rw [Real.dist_eq] at this
        have hφ_close : φ t - φ μ < ε / 2 := by
          linarith [abs_lt.mp this]
        -- `m*(t - μ) ≥ 0` since `m < 0` and `t - μ ≤ 0`.
        have hmta_nn : 0 ≤ m * (t - μ) :=
          mul_nonneg_of_nonpos_of_nonpos (le_of_lt hm_neg) (by linarith [ht.2])
        linarith
      · -- Far from `μ` (on the left): `μ - t > δ'`, so `m*(t - μ) = -m*(μ - t) ≥ M`.
        push Not at ht_close
        have ht_lt : t < μ - δ' := ht_close
        have ht_μ_gt_δ' : δ' < μ - t := by linarith
        have hm_ta : m * (t - μ) = -m * (μ - t) := by ring
        have hnm_ta_ge : -m * δ' ≤ -m * (μ - t) :=
          mul_le_mul_of_nonneg_left (le_of_lt ht_μ_gt_δ') (by linarith)
        have hnm_δ'_ge_M : M ≤ -m * δ' := by
          rw [hm_def]
          have : M / δ' * δ' = M := div_mul_cancel₀ M (ne_of_gt hδ'_pos)
          nlinarith [this, hδ'_pos]
        have hM_ge_excess : φ t - φ μ ≤ M := hφ_bound t ht
        linarith [hm_ta, hnm_ta_ge, hnm_δ'_ge_M]
    have hLμ : m * μ + c = φ μ + ε := by rw [hc_def]; ring
    have := concaveEnvelope_le_affineMajorant hmaj hμ
    linarith [hLμ]
  -- **Interior case** `a < μ < b`. Use `m := sSup {(φ t - φ μ)/(t - μ) | t ∈ (μ, b]}`;
  -- chord bounds this by any left difference quotient, giving a majorant line through
  -- `(μ, φ μ)` with slope `m`.
  have hμ_sub_a_pos : 0 < μ - a := sub_pos.mpr ha_lt_μ
  have hb_sub_μ_pos : 0 < b - μ := sub_pos.mpr hμ_lt_b
  set rSlopes : Set ℝ := (fun t => (φ t - φ μ) / (t - μ)) '' Set.Ioc μ b with hrSlopes_def
  have hrSlopes_nonempty : rSlopes.Nonempty :=
    ⟨(φ b - φ μ) / (b - μ), b, ⟨hμ_lt_b, le_refl b⟩, rfl⟩
  set leftBound := (φ μ - φ a) / (μ - a) with hleftBound_def
  have hrSlopes_bdd : ∀ x ∈ rSlopes, x ≤ leftBound := by
    rintro _ ⟨t, ⟨ht_gt, ht_le⟩, rfl⟩
    have ht_in_right : t ∈ Set.Icc μ b := ⟨le_of_lt ht_gt, ht_le⟩
    have ha_in_left : (a : ℝ) ∈ Set.Icc a μ := ⟨le_refl a, le_of_lt ha_lt_μ⟩
    have ha_lt_t : a < t := lt_trans ha_lt_μ ht_gt
    have hcineq := hchord_ineq a t ha_in_left ht_in_right ha_lt_t
    have ht_sub_μ_pos : 0 < t - μ := sub_pos.mpr ht_gt
    -- From `(t - μ) φ a + (μ - a) φ t ≤ (t - a) φ μ` deduce
    -- `(φ t - φ μ)(μ - a) ≤ (φ μ - φ a)(t - μ)`, then divide.
    have hcross : (φ t - φ μ) * (μ - a) ≤ (φ μ - φ a) * (t - μ) := by nlinarith [hcineq]
    rw [hleftBound_def]
    rw [div_le_div_iff₀ ht_sub_μ_pos hμ_sub_a_pos]
    linarith
  have hrSlopes_bddAbove : BddAbove rSlopes := ⟨leftBound, hrSlopes_bdd⟩
  set m := sSup rSlopes with hm_def
  have hm_upper : ∀ x ∈ rSlopes, x ≤ m := fun x hx => le_csSup hrSlopes_bddAbove hx
  have hm_le_leftSlope : ∀ t₁ ∈ Set.Ico a μ, m ≤ (φ μ - φ t₁) / (μ - t₁) := by
    intro t₁ ht₁
    have ht₁_lt_μ : t₁ < μ := ht₁.2
    have hμ_sub_t₁_pos : 0 < μ - t₁ := sub_pos.mpr ht₁_lt_μ
    have ht₁_in_left : t₁ ∈ Set.Icc a μ := ⟨ht₁.1, le_of_lt ht₁_lt_μ⟩
    refine csSup_le hrSlopes_nonempty ?_
    rintro _ ⟨t₂, ⟨ht₂_gt, ht₂_le⟩, rfl⟩
    have ht₂_in_right : t₂ ∈ Set.Icc μ b := ⟨le_of_lt ht₂_gt, ht₂_le⟩
    have ht₂_sub_μ_pos : 0 < t₂ - μ := sub_pos.mpr ht₂_gt
    have ht₁_lt_t₂ : t₁ < t₂ := lt_trans ht₁_lt_μ ht₂_gt
    have hcineq := hchord_ineq t₁ t₂ ht₁_in_left ht₂_in_right ht₁_lt_t₂
    rw [div_le_div_iff₀ ht₂_sub_μ_pos hμ_sub_t₁_pos]
    nlinarith [hcineq]
  set c := φ μ - m * μ with hc_def
  have hline_μ : m * μ + c = φ μ := by rw [hc_def]; ring
  have hmaj : IsAffineMajorant a b φ m c := by
    intro t ht
    rcases lt_trichotomy t μ with ht_lt | ht_eq | ht_gt
    · -- `t < μ`: use the cross-chord bound.
      have ht_in_Ico : t ∈ Set.Ico a μ := ⟨ht.1, ht_lt⟩
      have hslope := hm_le_leftSlope t ht_in_Ico
      have hμ_sub_t_pos : 0 < μ - t := sub_pos.mpr ht_lt
      -- `m ≤ (φ μ - φ t)/(μ - t)` ⟹ `m*(μ - t) ≤ φ μ - φ t`.
      have hineq : m * (μ - t) ≤ φ μ - φ t := by
        rw [le_div_iff₀ hμ_sub_t_pos] at hslope
        linarith
      have hL_eq : m * t + c = φ μ - m * (μ - t) := by rw [hc_def]; ring
      rw [hL_eq]
      linarith
    · rw [ht_eq, hline_μ]
    · -- `t > μ`: use the sup bound.
      have ht_in_Ioc : t ∈ Set.Ioc μ b := ⟨ht_gt, ht.2⟩
      have ht_in_rSlopes : (φ t - φ μ) / (t - μ) ∈ rSlopes := ⟨t, ht_in_Ioc, rfl⟩
      have hslope := hm_upper _ ht_in_rSlopes
      have ht_sub_μ_pos : 0 < t - μ := sub_pos.mpr ht_gt
      have hineq : φ t - φ μ ≤ m * (t - μ) := by
        rw [div_le_iff₀ ht_sub_μ_pos] at hslope
        linarith
      have hL_eq : m * t + c = m * (t - μ) + φ μ := by rw [hc_def]; ring
      rw [hL_eq]
      linarith
  have := concaveEnvelope_le_affineMajorant hmaj hμ
  linarith [hline_μ]

/-- **Concave envelope equals two-point value** on `[a, b]` for continuous `φ`. This is the
classical 1D concavification identity: The least concave majorant of `φ` at `μ` coincides with the
optimal mean-preserving two-point splitting value. -/
theorem concaveEnvelope_eq_twoPointValue
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {μ : ℝ} (hμ : μ ∈ Icc a b) :
    concaveEnvelope a b φ μ = twoPointValue a b φ μ := by
  refine le_antisymm ?_ (twoPointValue_le_concaveEnvelope hab hφ hμ)
  -- Grab an optimizer and specialize to `xL ≤ xR` via symmetry of the feasible set.
  obtain ⟨⟨xL₀, xR₀, q₀⟩, hmem₀, hmax₀⟩ := exists_twoPointOptimum hφ hμ
  -- Swap to ensure `xL ≤ xR`.
  have hsym_feasible :
      ∀ {xL xR q : ℝ}, (xL, xR, q) ∈ twoPointFeasibleSet a b μ →
        (xR, xL, 1 - q) ∈ twoPointFeasibleSet a b μ := by
    intro xL xR q ⟨hxL, hxR, hq_mem, hmean⟩
    refine ⟨hxR, hxL, ⟨?_, ?_⟩, ?_⟩
    · linarith [hq_mem.2]
    · linarith [hq_mem.1]
    · have : (1 - (1 - q)) * xR + (1 - q) * xL = q * xR + (1 - q) * xL := by ring
      rw [this]
      linarith [hmean]
  have hsym_obj : ∀ (xL xR q : ℝ),
      twoPointObjective φ (xR, xL, 1 - q) = twoPointObjective φ (xL, xR, q) := by
    intros; simp [twoPointObjective]; ring
  rcases le_total xL₀ xR₀ with hxLR_le | hxLR_ge
  · -- Case `xL₀ ≤ xR₀`.
    set xL := xL₀
    set xR := xR₀
    set q := q₀
    have hxL : xL ∈ Icc a b := hmem₀.1
    have hxR : xR ∈ Icc a b := hmem₀.2.1
    have hq_mem : q ∈ Icc (0 : ℝ) 1 := hmem₀.2.2.1
    have hmean : (1 - q) * xL + q * xR = μ := hmem₀.2.2.2
    have hval_eq : twoPointValue a b φ μ = (1 - q) * φ xL + q * φ xR := by
      unfold twoPointValue
      refine le_antisymm ?_ ?_
      · refine csSup_le ((twoPointFeasibleSet_nonempty hμ).image _) ?_
        rintro v ⟨p, hp, rfl⟩
        have := hmax₀ hp
        simpa [twoPointObjective] using this
      · refine le_csSup ?_ ⟨(xL, xR, q), hmem₀, ?_⟩
        · exact (twoPointFeasibleSet_isCompact a b μ).bddAbove_image
            (twoPointObjective_continuous hφ).continuousOn
        · simp [twoPointObjective]
    rw [hval_eq]
    -- Case split: proper non-degenerate `xL < xR ∧ 0 < q < 1` vs "effectively degenerate".
    by_cases hnondeg : xL < xR ∧ 0 < q ∧ q < 1
    · -- Non-degenerate: the secant line is an affine majorant.
      obtain ⟨hxLR_lt, hq_pos, hq_lt1⟩ := hnondeg
      have hmean' : (1 - q) * xL + q * xR ∈ Icc a b := hmean ▸ hμ
      have hopt' : IsMaxOn (twoPointObjective φ)
            (twoPointFeasibleSet a b ((1 - q) * xL + q * xR)) (xL, xR, q) := by
        rw [hmean]; exact hmax₀
      have hmaj := isAffineMajorant_secant_of_twoPointOptimum
        hφ hxL hxR hxLR_lt hq_pos hq_lt1 hmean' hopt'
      set m := (φ xR - φ xL) / (xR - xL) with hm_def
      set c := φ xL - m * xL with hc_def
      have hxR_sub_xL_ne : xR - xL ≠ 0 := sub_ne_zero.mpr hxLR_lt.ne'
      have h1 : m * xL + c = φ xL := by rw [hc_def]; ring
      have h2 : m * xR + c = φ xR := by
        rw [hc_def, hm_def]
        field_simp
        ring
      have hline_μ : m * μ + c = (1 - q) * φ xL + q * φ xR := by
        rw [← hmean]
        have hrw : m * ((1 - q) * xL + q * xR) + c
             = (1 - q) * (m * xL + c) + q * (m * xR + c) := by ring
        rw [hrw, h1, h2]
      have hbound := concaveEnvelope_le_affineMajorant hmaj hμ
      -- `hbound : concaveEnvelope a b φ μ ≤ m * μ + c`
      linarith [hline_μ]
    · -- Degenerate case: either `xL = xR`, or `q = 0`, or `q = 1`. In each sub-case the
      -- optimal value collapses to `φ μ` and we only need `concaveEnvelope μ ≤ φ μ`.
      have hval_eq_phi : (1 - q) * φ xL + q * φ xR = φ μ := by
        rcases not_and_or.mp hnondeg with hxLR_nlt | hq_not_in_Ioo
        · have hxLR_eq : xL = xR := le_antisymm hxLR_le (not_lt.mp hxLR_nlt)
          have hμ_eq : μ = xL := by
            have h := hmean
            rw [← hxLR_eq] at h
            linarith
          rw [← hxLR_eq, hμ_eq]; ring
        · rcases not_and_or.mp hq_not_in_Ioo with hq_not_pos | hq_not_lt1
          · have hq_zero : q = 0 := le_antisymm (not_lt.mp hq_not_pos) hq_mem.1
            have hμ_eq : μ = xL := by
              have := hmean
              rw [hq_zero] at this; linarith
            rw [hq_zero, hμ_eq]; ring
          · have hq_one : q = 1 := le_antisymm hq_mem.2 (not_lt.mp hq_not_lt1)
            have hμ_eq : μ = xR := by
              have := hmean
              rw [hq_one] at this; linarith
            rw [hq_one, hμ_eq]; ring
      rw [hval_eq_phi]
      -- The chord condition: every two-point value at `μ` is ≤ `φ μ`.
      have hchord : ∀ p ∈ twoPointFeasibleSet a b μ, twoPointObjective φ p ≤ φ μ := by
        intro p hp
        have hp_le : twoPointObjective φ p ≤ (1 - q) * φ xL + q * φ xR := hmax₀ hp
        linarith [hval_eq_phi]
      exact concaveEnvelope_le_phi_of_degenerate_twoPointOptimum hab hφ hμ hchord
  · -- Case `xR₀ ≤ xL₀`: swap to reduce to the first case.
    have hmem_sw : (xR₀, xL₀, 1 - q₀) ∈ twoPointFeasibleSet a b μ := hsym_feasible hmem₀
    have hmax_sw : IsMaxOn (twoPointObjective φ) (twoPointFeasibleSet a b μ)
        (xR₀, xL₀, 1 - q₀) := by
      intro p hp
      have h1 := hsym_feasible hp
      have h2 := hmax₀ h1
      -- `twoPointObjective φ (p.2.1, p.1, 1 - p.2.2) ≤ twoPointObjective φ (xL₀, xR₀, q₀)`
      -- Simplify both sides via `hsym_obj`.
      have hobj_swap := hsym_obj p.1 p.2.1 p.2.2
      have h3 := hsym_obj xL₀ xR₀ q₀
      calc twoPointObjective φ p
          = twoPointObjective φ (p.2.1, p.1, 1 - p.2.2) := hobj_swap.symm
        _ ≤ twoPointObjective φ (xL₀, xR₀, q₀) := h2
        _ = twoPointObjective φ (xR₀, xL₀, 1 - q₀) := h3.symm
    -- Now we have an optimizer with `xR₀ ≤ xL₀`, i.e., the "swapped" pair has `xL_sw ≤ xR_sw`.
    -- Recurse using the same body. We replicate the proof with `xL := xR₀`, `xR := xL₀`,
    -- `q := 1 - q₀`, so `xL ≤ xR`.
    set xL := xR₀
    set xR := xL₀
    set q := 1 - q₀
    have hxL : xL ∈ Icc a b := hmem_sw.1
    have hxR : xR ∈ Icc a b := hmem_sw.2.1
    have hq_mem : q ∈ Icc (0 : ℝ) 1 := hmem_sw.2.2.1
    have hmean : (1 - q) * xL + q * xR = μ := hmem_sw.2.2.2
    have hval_eq : twoPointValue a b φ μ = (1 - q) * φ xL + q * φ xR := by
      unfold twoPointValue
      refine le_antisymm ?_ ?_
      · refine csSup_le ((twoPointFeasibleSet_nonempty hμ).image _) ?_
        rintro v ⟨p, hp, rfl⟩
        have := hmax_sw hp
        simpa [twoPointObjective] using this
      · refine le_csSup ?_ ⟨(xL, xR, q), hmem_sw, ?_⟩
        · exact (twoPointFeasibleSet_isCompact a b μ).bddAbove_image
            (twoPointObjective_continuous hφ).continuousOn
        · simp [twoPointObjective]
    rw [hval_eq]
    have hxLR_le : xL ≤ xR := hxLR_ge
    by_cases hnondeg : xL < xR ∧ 0 < q ∧ q < 1
    · -- Non-degenerate.
      obtain ⟨hxLR_lt, hq_pos, hq_lt1⟩ := hnondeg
      have hmean' : (1 - q) * xL + q * xR ∈ Icc a b := hmean ▸ hμ
      have hopt' : IsMaxOn (twoPointObjective φ)
            (twoPointFeasibleSet a b ((1 - q) * xL + q * xR)) (xL, xR, q) := by
        rw [hmean]; exact hmax_sw
      have hmaj := isAffineMajorant_secant_of_twoPointOptimum
        hφ hxL hxR hxLR_lt hq_pos hq_lt1 hmean' hopt'
      set m := (φ xR - φ xL) / (xR - xL) with hm_def
      set c := φ xL - m * xL with hc_def
      have hxR_sub_xL_ne : xR - xL ≠ 0 := sub_ne_zero.mpr hxLR_lt.ne'
      have h1 : m * xL + c = φ xL := by rw [hc_def]; ring
      have h2 : m * xR + c = φ xR := by
        rw [hc_def, hm_def]
        field_simp
        ring
      have hline_μ : m * μ + c = (1 - q) * φ xL + q * φ xR := by
        rw [← hmean]
        have hrw : m * ((1 - q) * xL + q * xR) + c
             = (1 - q) * (m * xL + c) + q * (m * xR + c) := by ring
        rw [hrw, h1, h2]
      have hbound := concaveEnvelope_le_affineMajorant hmaj hμ
      linarith [hline_μ]
    · -- Degenerate (same as the non-swap branch).
      have hval_eq_phi : (1 - q) * φ xL + q * φ xR = φ μ := by
        rcases not_and_or.mp hnondeg with hxLR_nlt | hq_not_in_Ioo
        · have hxLR_eq : xL = xR := le_antisymm hxLR_le (not_lt.mp hxLR_nlt)
          have hμ_eq : μ = xL := by
            have h := hmean
            rw [← hxLR_eq] at h
            linarith
          rw [← hxLR_eq, hμ_eq]; ring
        · rcases not_and_or.mp hq_not_in_Ioo with hq_not_pos | hq_not_lt1
          · have hq_zero : q = 0 := le_antisymm (not_lt.mp hq_not_pos) hq_mem.1
            have hμ_eq : μ = xL := by
              have := hmean
              rw [hq_zero] at this; linarith
            rw [hq_zero, hμ_eq]; ring
          · have hq_one : q = 1 := le_antisymm hq_mem.2 (not_lt.mp hq_not_lt1)
            have hμ_eq : μ = xR := by
              have := hmean
              rw [hq_one] at this; linarith
            rw [hq_one, hμ_eq]; ring
      rw [hval_eq_phi]
      have hchord : ∀ p ∈ twoPointFeasibleSet a b μ, twoPointObjective φ p ≤ φ μ := by
        intro p hp
        have hp_le : twoPointObjective φ p ≤ (1 - q) * φ xL + q * φ xR := hmax_sw hp
        linarith [hval_eq_phi]
      exact concaveEnvelope_le_phi_of_degenerate_twoPointOptimum hab hφ hμ hchord

/-- The concave envelope is itself concave on `Icc a b`. This is automatic from its definition as a
pointwise infimum of affine functions. -/
lemma concaveEnvelope_concaveOn
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) :
    ConcaveOn ℝ (Icc a b) (concaveEnvelope a b φ) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  have hz : α • x + β • y ∈ Icc a b := convex_Icc a b hx hy hα hβ hαβ
  refine le_csInf ?_ ?_
  · obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ
    exact ⟨m₀ * (α • x + β • y) + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩
  rintro _ ⟨m, c, hm, rfl⟩
  have hxb : concaveEnvelope a b φ x ≤ m * x + c :=
    concaveEnvelope_le_affineMajorant hm hx
  have hyb : concaveEnvelope a b φ y ≤ m * y + c :=
    concaveEnvelope_le_affineMajorant hm hy
  have hαx : α * concaveEnvelope a b φ x ≤ α * (m * x + c) :=
    mul_le_mul_of_nonneg_left hxb hα
  have hβy : β * concaveEnvelope a b φ y ≤ β * (m * y + c) :=
    mul_le_mul_of_nonneg_left hyb hβ
  have hsum := add_le_add hαx hβy
  have hconv : α * (m * x + c) + β * (m * y + c) = m * (α • x + β • y) + c := by
    simp only [smul_eq_mul]
    linear_combination c * hαβ
  calc α • concaveEnvelope a b φ x + β • concaveEnvelope a b φ y
      = α * concaveEnvelope a b φ x + β * concaveEnvelope a b φ y := by
          simp [smul_eq_mul]
    _ ≤ α * (m * x + c) + β * (m * y + c) := hsum
    _ = m * (α • x + β • y) + c := hconv
