/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.EnvelopeDuality

open MeasureTheory Set

/-!
# Convex envelope as the supremum over affine minorants

The **convex envelope** of `φ` on `[a, b]` is the **greatest convex minorant** of `φ`, realized
concretely as the reflection `convexEnvelope a b φ := -concaveEnvelope a b (fun y => -φ y)`. The
file proves the sandwich, convexity, contact, and affine-gap properties of this envelope.

## Main definitions

* `IsAffineMinorant a b φ m c` — `(m, c)` is dominated by `φ` on `[a, b]`.
* `convexEnvelope a b φ` — the greatest convex minorant, realized as `-concaveEnvelope a b (-φ)`.

## Main statements

* `convexEnvelope_le_self`, `convexEnvelope_convexOn` — sandwich and convexity.
* `convexEnvelope_affineOn_of_lt` — the convex envelope is affine across each gap where it lies
  strictly below `φ`.

## Tags

convex envelope, greatest convex minorant, affine minorant, ironing, concavification
-/

@[expose] public section

/-- `(m, c)` is an affine minorant of `φ` on `[a, b]` if `m t + c ≤ φ t` throughout. -/
def IsAffineMinorant (a b : ℝ) (φ : ℝ → ℝ) (m c : ℝ) : Prop :=
  ∀ t ∈ Icc a b, m * t + c ≤ φ t

/-- The **convex envelope** of `φ` on `[a, b]`, the largest convex function below `φ`, realized as
the reflection `-concaveEnvelope a b (-φ)`. On `[a, b]` this is the largest convex minorant. -/
noncomputable def convexEnvelope (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -concaveEnvelope a b (fun y => -φ y) x

/-- `(m, c)` is an affine minorant of `φ` iff `(-m, -c)` is an affine majorant of `-φ`. -/
lemma isAffineMinorant_iff_neg {a b : ℝ} {φ : ℝ → ℝ} {m c : ℝ} :
    IsAffineMinorant a b φ m c ↔ IsAffineMajorant a b (fun y => -φ y) (-m) (-c) := by
  -- Both directions are the same termwise inequality `m*t+c ≤ φ t ↔ -φ t ≤ -m*t + -c`.
  constructor
  · intro h t ht; simp only; linarith [h t ht]
  · intro h t ht; have := h t ht; simp only at this; linarith

/-- The convex envelope lies below `φ` on `[a, b]`. -/
lemma convexEnvelope_le_self {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    convexEnvelope a b φ x ≤ φ x := by
  unfold convexEnvelope
  have hneg : ContinuousOn (fun y => -φ y) (Icc a b) := hφ.neg
  linarith [concaveEnvelope_ge_self hab hneg hx]

/-- Every affine minorant of `φ` is dominated by the convex envelope at each point of `[a, b]`. -/
lemma convexEnvelope_ge_affineMinorant {a b : ℝ} {φ : ℝ → ℝ} {m c : ℝ}
    (hm : IsAffineMinorant a b φ m c) {x : ℝ} (hx : x ∈ Icc a b) :
    m * x + c ≤ convexEnvelope a b φ x := by
  unfold convexEnvelope
  have hmaj : IsAffineMajorant a b (fun y => -φ y) (-m) (-c) := isAffineMinorant_iff_neg.mp hm
  -- `concaveEnvelope ≤ (-m) * x + (-c)`, so `-concaveEnvelope ≥ m * x + c`.
  nlinarith [concaveEnvelope_le_affineMajorant hmaj hx]

/-- The convex envelope is convex on `[a, b]`. -/
lemma convexEnvelope_convexOn {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) :
    ConvexOn ℝ (Icc a b) (convexEnvelope a b φ) := by
  have hneg : ContinuousOn (fun y => -φ y) (Icc a b) := hφ.neg
  -- `(concaveEnvelope a b (-φ)).neg` is `ConvexOn (-(concaveEnvelope a b (-φ)))`,
  -- which is defeq to `convexEnvelope a b φ`.
  exact (concaveEnvelope_concaveOn hab hneg).neg

/-- **Contact agreement.** Wherever `φ` has a supporting affine minorant — one that touches `φ` at
`x` — the convex envelope coincides with `φ` there. At the endpoints `a, b` a Lipschitz `φ` admits
such a supporting line, giving `convexEnvelope a b φ a = φ a` and `… b = φ b`. -/
lemma convexEnvelope_eq_of_affineMinorant_contact {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) {x m c : ℝ} (hx : x ∈ Icc a b)
    (hm : IsAffineMinorant a b φ m c) (hcontact : m * x + c = φ x) :
    convexEnvelope a b φ x = φ x := by
  refine le_antisymm (convexEnvelope_le_self hab hφ hx) ?_
  have h := convexEnvelope_ge_affineMinorant hm hx
  rwa [hcontact] at h

/-- **The concave envelope is affine across each gap.** If at an interior point `q` the concave
envelope of a continuous `ψ` strictly exceeds `ψ`, then `q` is straddled by two points
`xL < q < xR` on which the envelope coincides with the secant line through `(xL, ψ xL)` and
`(xR, ψ xR)`. Hence the envelope is affine on the closed interval `[xL, xR]` containing `q`. -/
lemma concaveEnvelope_affineOn_of_lt {a b : ℝ} (hab : a ≤ b) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) {q : ℝ} (hq : q ∈ Ioo a b) (hlt : ψ q < concaveEnvelope a b ψ q) :
    ∃ xL xR : ℝ, xL ∈ Icc a b ∧ xR ∈ Icc a b ∧ xL < q ∧ q < xR ∧
      ∀ x ∈ Icc xL xR,
        concaveEnvelope a b ψ x
          = (ψ xR - ψ xL) / (xR - xL) * x + (ψ xL - (ψ xR - ψ xL) / (xR - xL) * xL) := by
  have hqIcc : q ∈ Icc a b := ⟨hq.1.le, hq.2.le⟩
  obtain ⟨⟨xL₀, xR₀, w₀⟩, hmem₀, hmax₀⟩ := exists_twoPointOptimum hψ hqIcc
  -- Swap the two atoms (and the weight) to ensure `xL ≤ xR`; the secant is unchanged.
  set xL := if xL₀ ≤ xR₀ then xL₀ else xR₀ with hxL_set
  set xR := if xL₀ ≤ xR₀ then xR₀ else xL₀ with hxR_set
  set w := if xL₀ ≤ xR₀ then w₀ else 1 - w₀ with hw_set
  have hmem : (xL, xR, w) ∈ twoPointFeasibleSet a b q := by
    by_cases hle : xL₀ ≤ xR₀
    · simp only [hxL_set, hxR_set, hw_set, if_pos hle]; exact hmem₀
    · obtain ⟨hxL₀, hxR₀, hw₀mem, hmean₀⟩ := hmem₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [hxL_set, if_neg hle]; exact hxR₀
      · simp only [hxR_set, if_neg hle]; exact hxL₀
      · simp only [hw_set, if_neg hle]; exact ⟨by linarith [hw₀mem.2], by linarith [hw₀mem.1]⟩
      · simp only [hxL_set, hxR_set, hw_set, if_neg hle]; linarith [hmean₀]
  have hmax : IsMaxOn (twoPointObjective ψ) (twoPointFeasibleSet a b q) (xL, xR, w) := by
    by_cases hle : xL₀ ≤ xR₀
    · simp only [hxL_set, hxR_set, hw_set, if_pos hle]; exact hmax₀
    · intro p hp
      have hsym_obj : twoPointObjective ψ (xR₀, xL₀, 1 - w₀)
          = twoPointObjective ψ (xL₀, xR₀, w₀) := by simp [twoPointObjective]; ring
      have hval₀ : twoPointObjective ψ (xL, xR, w) = twoPointObjective ψ (xL₀, xR₀, w₀) := by
        simp only [hxL_set, hxR_set, hw_set, if_neg hle]; exact hsym_obj
      rw [hval₀]; exact hmax₀ hp
  have hxLR_le : xL ≤ xR := by
    by_cases hle : xL₀ ≤ xR₀
    · simp only [hxL_set, hxR_set, if_pos hle]; exact hle
    · simp only [hxL_set, hxR_set, if_neg hle]; linarith [le_of_not_ge hle]
  have hxL : xL ∈ Icc a b := hmem.1
  have hxR : xR ∈ Icc a b := hmem.2.1
  have hw_mem : w ∈ Icc (0 : ℝ) 1 := hmem.2.2.1
  have hmean : (1 - w) * xL + w * xR = q := hmem.2.2.2
  -- The optimum value equals the concave envelope at `q`.
  have hval : (1 - w) * ψ xL + w * ψ xR = concaveEnvelope a b ψ q := by
    rw [concaveEnvelope_eq_twoPointValue hab hψ hqIcc]
    unfold twoPointValue
    refine le_antisymm ?_ ?_
    · refine le_csSup ((twoPointFeasibleSet_isCompact a b q).bddAbove_image
        (twoPointObjective_continuous hψ).continuousOn) ⟨(xL, xR, w), hmem, ?_⟩
      simp [twoPointObjective]
    · refine csSup_le ((twoPointFeasibleSet_nonempty hqIcc).image _) ?_
      rintro v ⟨p, hp, rfl⟩
      have := hmax hp
      simpa [twoPointObjective] using this
  -- Strict gap rules out the degenerate optima: `xL < xR`, `0 < w < 1`.
  have hgap : (1 - w) * ψ xL + w * ψ xR > ψ q := by rw [hval]; exact hlt
  -- Strict gap rules out `xL = xR`, `w = 0`, `w = 1` (each collapses the value to `ψ q`).
  have hxL_ne_xR : xL ≠ xR := by
    intro heq
    have hval' : (1 - w) * ψ xL + w * ψ xR = ψ xL := by rw [heq]; ring
    have hq' : q = xL := by rw [← hmean, heq]; ring
    rw [hval', hq'] at hgap; exact lt_irrefl _ hgap
  have hw_pos : 0 < w := by
    rcases lt_or_eq_of_le hw_mem.1 with h | h
    · exact h
    · exfalso
      have hq' : q = xL := by rw [← hmean, ← h]; ring
      rw [← h, hq'] at hgap; simp only [sub_zero, one_mul, zero_mul, add_zero] at hgap
      exact lt_irrefl _ hgap
  have hw_lt1 : w < 1 := by
    rcases lt_or_eq_of_le hw_mem.2 with h | h
    · exact h
    · exfalso
      have hq' : q = xR := by rw [← hmean, h]; ring
      rw [h, hq'] at hgap; simp only [sub_self, zero_mul, one_mul, zero_add] at hgap
      exact lt_irrefl _ hgap
  -- With `xL ≤ xR` and `xL ≠ xR`, we get `xL < xR`.
  have hxLR : xL < xR := lt_of_le_of_ne hxLR_le hxL_ne_xR
  -- `xL < q < xR`: `q` is a strict interior barycenter.
  have hxL_lt_q : xL < q := by
    rw [← hmean]; nlinarith [hw_pos, sub_pos.mpr hxLR]
  have hq_lt_xR : q < xR := by
    rw [← hmean]; nlinarith [hw_lt1, sub_pos.mpr hxLR]
  -- The secant of `ψ` through `xL, xR` is an affine majorant of `ψ`.
  set m := (ψ xR - ψ xL) / (xR - xL) with hm_def
  set c := ψ xL - m * xL with hc_def
  have hmaj : IsAffineMajorant a b ψ m c := by
    have hmean_mem : (1 - w) * xL + w * xR ∈ Icc a b := by rw [hmean]; exact hqIcc
    have hopt' : IsMaxOn (twoPointObjective ψ)
        (twoPointFeasibleSet a b ((1 - w) * xL + w * xR)) (xL, xR, w) := by
      rw [hmean]; exact hmax
    exact isAffineMajorant_secant_of_twoPointOptimum hψ hxL hxR hxLR hw_pos hw_lt1 hmean_mem hopt'
  refine ⟨xL, xR, hxL, hxR, hxL_lt_q, hq_lt_xR, fun x hx => ?_⟩
  have hxIcc : x ∈ Icc a b := ⟨le_trans hxL.1 hx.1, le_trans hx.2 hxR.2⟩
  -- Endpoint contact values: at `xL, xR` the envelope equals the secant.
  have hxR_sub_ne : xR - xL ≠ 0 := sub_ne_zero.mpr hxLR.ne'
  have hsec_xL : m * xL + c = ψ xL := by rw [hc_def]; ring
  have hsec_xR : m * xR + c = ψ xR := by
    rw [hc_def]
    have : m * xR + (ψ xL - m * xL) = m * (xR - xL) + ψ xL := by ring
    rw [this, hm_def, div_mul_cancel₀ _ hxR_sub_ne]; ring
  -- At any contact point of the secant majorant, the envelope is squeezed to the secant value.
  have henv_contact : ∀ z ∈ Icc a b, m * z + c = ψ z → concaveEnvelope a b ψ z = m * z + c :=
    fun z hz hsec => le_antisymm (concaveEnvelope_le_affineMajorant hmaj hz)
      (hsec ▸ concaveEnvelope_ge_self hab hψ.continuousOn hz)
  have henv_xL : concaveEnvelope a b ψ xL = m * xL + c := henv_contact xL hxL hsec_xL
  have henv_xR : concaveEnvelope a b ψ xR = m * xR + c := henv_contact xR hxR hsec_xR
  -- Squeeze on `[xL, xR]`: envelope ≤ secant (majorant) and envelope ≥ chord (concavity).
  refine le_antisymm (concaveEnvelope_le_affineMajorant hmaj hxIcc) ?_
  have hconc : ConcaveOn ℝ (Icc a b) (concaveEnvelope a b ψ) :=
    concaveEnvelope_concaveOn hab hψ.continuousOn
  -- Write `x` as a barycenter of `xL, xR` and use concavity ≥ chord, with contact endpoints.
  rcases eq_or_lt_of_le hx.1 with hxxL | hxxL
  · rw [← hxxL, henv_xL]
  rcases eq_or_lt_of_le hx.2 with hxxR | hxxR
  · rw [hxxR, henv_xR]
  · set t := (x - xL) / (xR - xL) with ht_def
    have hxR_sub_pos : 0 < xR - xL := sub_pos.mpr hxLR
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hxR_sub_pos.le
    have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hxR_sub_pos]; linarith
    have hbary : (1 - t) • xL + t • xR = x := by
      rw [ht_def]; simp only [smul_eq_mul]; field_simp; ring
    have hconc_ineq := hconc.2 hxL hxR (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    rw [hbary] at hconc_ineq
    rw [henv_xL, henv_xR] at hconc_ineq
    have hsec_x : m * x + c = (1 - t) • (m * xL + c) + t • (m * xR + c) := by
      simp only [smul_eq_mul]
      rw [ht_def]; field_simp; ring
    rw [hsec_x]; exact hconc_ineq

/-- The convex envelope depends only on the values of `φ` on `[a, b]`. -/
lemma convexEnvelope_congr {a b : ℝ} {φ ψ : ℝ → ℝ} (h : Set.EqOn φ ψ (Icc a b)) (x : ℝ) :
    convexEnvelope a b φ x = convexEnvelope a b ψ x := by
  unfold convexEnvelope
  rw [concaveEnvelope_congr (φ := fun y => -φ y) (ψ := fun y => -ψ y)
    (fun t ht => by simp only [h ht]) x]

/-- **The convex envelope is affine across each gap.** If at an interior point `q` the convex
envelope of a `φ` continuous on `[a, b]` lies strictly below `φ`, then `q` is straddled by two
points `xL < q < xR` on which the envelope equals a single affine function. This is the reflection
of `concaveEnvelope_affineOn_of_lt`: The ironed primitive `convexEnvelope` is affine on a
neighborhood of every point of the open ironed region `{convexEnvelope < φ}`. -/
lemma convexEnvelope_affineOn_of_lt {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc a b)) {q : ℝ} (hq : q ∈ Ioo a b)
    (hlt : convexEnvelope a b φ q < φ q) :
    ∃ xL xR m c : ℝ, xL ∈ Icc a b ∧ xR ∈ Icc a b ∧ xL < q ∧ q < xR ∧
      ∀ x ∈ Icc xL xR, convexEnvelope a b φ x = m * x + c := by
  -- Extend `φ` to a globally continuous `φe = IccExtend hab (φ ∘ val)` agreeing on `[a, b]`.
  set φe : ℝ → ℝ := Set.IccExtend hab (fun p : Icc a b => φ p) with hφe_def
  have hcont : Continuous φe := by
    rw [hφe_def]
    exact continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hφ)
  have heqOn : Set.EqOn φe φ (Icc a b) := fun x hx => by
    rw [hφe_def, Set.IccExtend_of_mem hab _ hx]
  have hcongr : ∀ x, convexEnvelope a b φe x = convexEnvelope a b φ x :=
    fun x => convexEnvelope_congr heqOn x
  -- The negation `-φe` is globally continuous; apply the concave gap lemma.
  have hψ : Continuous (fun y => -φe y) := hcont.neg
  have henv_eq : ∀ x, concaveEnvelope a b (fun y => -φe y) x = -convexEnvelope a b φe x := by
    intro x; unfold convexEnvelope; rw [neg_neg]
  have hqIcc : q ∈ Icc a b := ⟨hq.1.le, hq.2.le⟩
  have hlt' : (fun y => -φe y) q < concaveEnvelope a b (fun y => -φe y) q := by
    rw [henv_eq q]; simp only [hcongr q, heqOn hqIcc]; linarith
  obtain ⟨xL, xR, hxL, hxR, hxLq, hqxR, haffine⟩ :=
    concaveEnvelope_affineOn_of_lt hab hψ hq hlt'
  set m := ((-φe xR) - (-φe xL)) / (xR - xL) with hm_def
  set c := (-φe xL) - m * xL with hc_def
  refine ⟨xL, xR, -m, -c, hxL, hxR, hxLq, hqxR, fun x hx => ?_⟩
  have h := haffine x hx
  rw [henv_eq x] at h
  -- `-Ĥ x = m * x + c`, so `Ĥ x = -(m * x + c)`; transfer from `φe` to `φ`.
  have hφe_env : convexEnvelope a b φe x = -(m * x + c) := by linarith [h]
  rw [← hcongr x, hφe_env]; ring
