/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.OneGapChord

/-!
# Concave envelope under a one-gap chord

Identification of the concave envelope on `[0, 1]` in the single-gap geometry: The glued function
`oneGapGlue` (chord on the middle, `v` on the tails) is the concave envelope, the envelope strictly
exceeds `v` exactly on the open middle, and the contact set is the union of the two tails.

## Main statements

* `concaveEnvelope_eq_oneGapGlue` — the envelope equals the glued chord/tail function.
* `concaveEnvelope_eq_of_oneGapChord` — piecewise description (tails and middle).
* `concaveEnvelope_strict_gt_on_oneGap`, `contactSet_of_oneGapChord` — strict gap and contact set.

## Tags

concave envelope, affine chord, contact set, concavification, ironing
-/

@[expose] public section

open MeasureTheory Set

/-- Continuity of `oneGapGlue v a b slope intercept`. -/
lemma oneGapGlue_continuous {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (hab : a ≤ b) (hv : Continuous v)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b) :
    Continuous (oneGapGlue v a b slope intercept) := by
  have heq : oneGapGlue v a b slope intercept
           = (Icc a b).piecewise (affineFun slope intercept) v := by
    funext x
    simp [oneGapGlue, Set.piecewise, mem_Icc]
  rw [heq]
  apply Continuous.piecewise
  · intro x hx
    rw [frontier_Icc hab] at hx
    rcases hx with hxa | hxb
    · rw [hxa, ← hva]
    · rw [hxb, ← hvb]
  · exact affineFun_continuous _ _
  · exact hv

/-- Endpoint value: The concave envelope equals the chord at `a`. -/
lemma concaveEnvelope_eq_chord_at_a {v : ℝ → ℝ} {a slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1)
    (hv : Continuous v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a) :
    concaveEnvelope 0 1 v a = affineFun slope intercept a := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hv_cont_on : ContinuousOn v (Icc (0 : ℝ) 1) := hv.continuousOn
  have hge : v a ≤ concaveEnvelope 0 1 v a :=
    concaveEnvelope_ge_self h01 hv_cont_on ha
  have hle : concaveEnvelope 0 1 v a ≤ slope * a + intercept :=
    concaveEnvelope_le_affineMajorant (isAffineMajorant_of_oneGap hmaj) ha
  have hgeq : v a = slope * a + intercept := hva
  linarith

/-- Endpoint value: The concave envelope equals the chord at `b`. -/
lemma concaveEnvelope_eq_chord_at_b {v : ℝ → ℝ} {b slope intercept : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1)
    (hv : Continuous v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hvb : v b = affineFun slope intercept b) :
    concaveEnvelope 0 1 v b = affineFun slope intercept b := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hv_cont_on : ContinuousOn v (Icc (0 : ℝ) 1) := hv.continuousOn
  have hge : v b ≤ concaveEnvelope 0 1 v b :=
    concaveEnvelope_ge_self h01 hv_cont_on hb
  have hle : concaveEnvelope 0 1 v b ≤ slope * b + intercept :=
    concaveEnvelope_le_affineMajorant (isAffineMajorant_of_oneGap hmaj) hb
  have hgeq : v b = slope * b + intercept := hvb
  linarith

/-- `concaveEnvelope ≥ oneGapGlue` on `Icc 0 1`. -/
lemma concaveEnvelope_ge_oneGapGlue {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hv : Continuous v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    oneGapGlue v a b slope intercept x ≤ concaveEnvelope 0 1 v x := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hv_cont_on : ContinuousOn v (Icc (0 : ℝ) 1) := hv.continuousOn
  have hCE_conc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (concaveEnvelope 0 1 v) :=
    concaveEnvelope_concaveOn h01 hv_cont_on
  have hCEa : concaveEnvelope 0 1 v a = affineFun slope intercept a :=
    concaveEnvelope_eq_chord_at_a ha hv hmaj hva
  have hCEb : concaveEnvelope 0 1 v b = affineFun slope intercept b :=
    concaveEnvelope_eq_chord_at_b hb hv hmaj hvb
  by_cases hxm : x ∈ Icc a b
  · -- On [a, b]: CE concave with CE(a) = g(a), CE(b) = g(b) gives CE ≥ g by chord.
    rw [oneGapGlue_of_mem_Icc hxm]
    set α := (b - x) / (b - a)
    set β := (x - a) / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hab
    have hα_nn : 0 ≤ α := by
      apply div_nonneg
      · linarith [hxm.2]
      · linarith
    have hβ_nn : 0 ≤ β := by
      apply div_nonneg
      · linarith [hxm.1]
      · linarith
    have hne : (b - a) ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hαβ : α + β = 1 := by
      change (b - x) / (b - a) + (x - a) / (b - a) = 1
      field_simp
      ring
    have hxeq : α • a + β • b = x := by
      simp only [smul_eq_mul, α, β]
      field_simp
      ring
    have hconc_ineq := hCE_conc.2 ha hb hα_nn hβ_nn hαβ
    rw [hxeq] at hconc_ineq
    have hga : concaveEnvelope 0 1 v a = slope * a + intercept := hCEa
    have hgb : concaveEnvelope 0 1 v b = slope * b + intercept := hCEb
    have : α * (slope * a + intercept) + β * (slope * b + intercept)
         = affineFun slope intercept x := by
      simp only [affineFun, α, β]
      field_simp
      ring
    calc affineFun slope intercept x
        = α * (slope * a + intercept) + β * (slope * b + intercept) := this.symm
      _ = α • concaveEnvelope 0 1 v a + β • concaveEnvelope 0 1 v b := by
          rw [hga, hgb]; simp [smul_eq_mul]
      _ ≤ concaveEnvelope 0 1 v x := hconc_ineq
  · -- On tails: CE ≥ v = glue.
    have hge : v x ≤ concaveEnvelope 0 1 v x :=
      concaveEnvelope_ge_self h01 hv_cont_on hx
    by_cases hxa : x ≤ a
    · rw [oneGapGlue_of_le_a hab hva hxa]
      exact hge
    · push Not at hxa
      have hbx : b ≤ x := by
        by_contra hbx_neg
        push Not at hbx_neg
        exact hxm ⟨hxa.le, hbx_neg.le⟩
      rw [oneGapGlue_of_ge_b hab hvb hbx]
      exact hge

/-- For `x₀ ∈ (0, 1)`, there exists an affine majorant of `v` on `Icc 0 1` whose value at `x₀`
equals `oneGapGlue v a b slope intercept x₀`. -/
lemma exists_affineMajorant_eq_oneGapGlue_of_mem_Ioo
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hvL : ConcaveOn ℝ (Icc (0 : ℝ) a) v)
    (hvR : ConcaveOn ℝ (Icc b 1) v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ m c, IsAffineMajorant 0 1 v m c ∧
      m * x₀ + c = oneGapGlue v a b slope intercept x₀ := by
  set G := oneGapGlue v a b slope intercept with hGdef
  have hG_conc : ConcaveOn ℝ (Icc (0 : ℝ) 1) G :=
    oneGapGlue_concaveOn ha hb hab hvL hvR hmaj hva hvb
  have hnegG_conv : ConvexOn ℝ (Icc (0 : ℝ) 1) (-G) := hG_conc.neg
  have hx₀_int : x₀ ∈ interior (Icc (0 : ℝ) 1) := by
    rw [interior_Icc]; exact hx₀
  -- σ_r : subgradient of -G at x₀ from the right.
  set σ_r : ℝ := derivWithin (-G) (Ioi x₀) x₀ with hσ_r_def
  set σ_l : ℝ := derivWithin (-G) (Iio x₀) x₀ with hσ_l_def
  have hle_lr : σ_l ≤ σ_r :=
    hnegG_conv.leftDeriv_le_rightDeriv_of_mem_interior hx₀_int
  -- Subgradient inequality: -G y ≥ -G x₀ + σ_r * (y - x₀) for y ∈ Icc 0 1.
  have hsubgrad : ∀ y ∈ Icc (0 : ℝ) 1,
      (-G) x₀ + σ_r * (y - x₀) ≤ (-G) y := by
    intro y hy
    rcases lt_trichotomy y x₀ with hyx | hyx | hyx
    · have hslope := hnegG_conv.slope_le_leftDeriv_of_mem_interior hy hx₀_int hyx
      -- hslope : slope (-G) y x₀ ≤ σ_l
      have hpos : 0 < x₀ - y := sub_pos.mpr hyx
      rw [slope_def_field, div_le_iff₀ hpos] at hslope
      linarith [mul_le_mul_of_nonneg_right hle_lr hpos.le]
    · subst hyx
      linarith
    · have hslope := hnegG_conv.rightDeriv_le_slope_of_mem_interior hx₀_int hy hyx
      have hpos : 0 < y - x₀ := sub_pos.mpr hyx
      rw [slope_def_field, le_div_iff₀ hpos] at hslope
      linarith
  -- Translate to: G y ≤ G x₀ + (-σ_r) * (y - x₀).
  have hsupgrad : ∀ y ∈ Icc (0 : ℝ) 1,
      G y ≤ G x₀ + (-σ_r) * (y - x₀) := by
    intro y hy
    have := hsubgrad y hy
    simp only [Pi.neg_apply] at this
    linarith
  -- Now construct m, c.
  refine ⟨-σ_r, G x₀ + σ_r * x₀, ?_, ?_⟩
  · intro t ht
    have hGt_ge : v t ≤ G t := by
      have hx₀_mem : x₀ ∈ Icc (0 : ℝ) 1 := ⟨hx₀.1.le, hx₀.2.le⟩
      rcases le_or_gt t a with hta | hta
      · rw [hGdef, oneGapGlue_of_le_a hab hva hta]
      · rcases le_or_gt b t with hbt | hbt
        · rw [hGdef, oneGapGlue_of_ge_b hab hvb hbt]
        · rw [hGdef, oneGapGlue_of_mem_Icc ⟨hta.le, hbt.le⟩]
          exact hmaj t ht
    have hGt_le : G t ≤ G x₀ + (-σ_r) * (t - x₀) := hsupgrad t ht
    have heq : G x₀ + (-σ_r) * (t - x₀) = -σ_r * t + (G x₀ + σ_r * x₀) := by ring
    linarith
  · ring

/-- `concaveEnvelope ≤ oneGapGlue` on `Ioo 0 1` (interior). -/
lemma concaveEnvelope_le_oneGapGlue_of_mem_Ioo
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hvL : ConcaveOn ℝ (Icc (0 : ℝ) a) v)
    (hvR : ConcaveOn ℝ (Icc b 1) v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    concaveEnvelope 0 1 v x ≤ oneGapGlue v a b slope intercept x := by
  obtain ⟨m, c, hmaj_aff, heq⟩ :=
    exists_affineMajorant_eq_oneGapGlue_of_mem_Ioo ha hb hab hvL hvR hmaj hva hvb hx
  have hxmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  calc concaveEnvelope 0 1 v x
      ≤ m * x + c := concaveEnvelope_le_affineMajorant hmaj_aff hxmem
    _ = oneGapGlue v a b slope intercept x := heq

/-- For concave `f` on `Icc 0 1`, `f 0 ≤ 2 * f ε - f (2 * ε)` for any `ε ∈ (0, 1/2]`. -/
private lemma concaveOn_bound_at_zero
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : 2 * ε ≤ 1) :
    f 0 ≤ 2 * f ε - f (2 * ε) := by
  have h2ε_mem : (2 * ε) ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hε_le⟩
  have h0_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hconc := hf.2 h0_mem h2ε_mem
    (by norm_num : (0:ℝ) ≤ (1:ℝ)/2) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  simp only [smul_eq_mul] at hconc
  have hmidpt : (1 : ℝ)/2 * 0 + 1/2 * (2 * ε) = ε := by ring
  rw [hmidpt] at hconc
  linarith

/-- For concave `f` on `Icc 0 1`, `f 1 ≤ 2 * f (1 - ε) - f (1 - 2 * ε)` for `ε ∈ (0, 1/2]`. -/
private lemma concaveOn_bound_at_one
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_le : 2 * ε ≤ 1) :
    f 1 ≤ 2 * f (1 - ε) - f (1 - 2 * ε) := by
  have h2ε_nn : 0 ≤ 1 - 2 * ε := by linarith
  have h1m2ε_mem : (1 - 2 * ε) ∈ Icc (0 : ℝ) 1 := ⟨h2ε_nn, by linarith⟩
  have h1_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have hconc := hf.2 h1_mem h1m2ε_mem
    (by norm_num : (0:ℝ) ≤ (1:ℝ)/2) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  simp only [smul_eq_mul] at hconc
  have hmidpt : (1 : ℝ)/2 * 1 + 1/2 * (1 - 2 * ε) = 1 - ε := by ring
  rw [hmidpt] at hconc
  linarith

/-- `concaveEnvelope ≤ oneGapGlue` on `Icc 0 1` (extended to boundary via concavity of the concave
envelope and continuity of `v`). -/
lemma concaveEnvelope_le_oneGapGlue
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hvL : ConcaveOn ℝ (Icc (0 : ℝ) a) v)
    (hvR : ConcaveOn ℝ (Icc b 1) v)
    (hv : Continuous v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    concaveEnvelope 0 1 v x ≤ oneGapGlue v a b slope intercept x := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hv_cont_on : ContinuousOn v (Icc (0 : ℝ) 1) := hv.continuousOn
  have hCE_conc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (concaveEnvelope 0 1 v) :=
    concaveEnvelope_concaveOn h01 hv_cont_on
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · -- x = 0 (from `hx0 : 0 = x`)
    rw [← hx0]
    -- Case split on whether a = 0 or a > 0.
    rcases eq_or_lt_of_le ha.1 with ha0 | ha0
    · -- a = 0: glue(0) = affineFun(0) = v(0). CE(0) ≤ g(0) via affine majorant.
      rw [oneGapGlue_of_mem_Icc ⟨ha0.symm.le, hb.1⟩]
      have hCE_le := concaveEnvelope_le_affineMajorant
        (isAffineMajorant_of_oneGap hmaj) ⟨le_refl _, by norm_num⟩
      simpa [affineFun] using hCE_le
    · -- a > 0. Use boundary-limit via concavity.
      have hglue0 : oneGapGlue v a b slope intercept 0 = v 0 :=
        oneGapGlue_of_le_a hab hva ha0.le
      rw [hglue0]
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hv_cont : ContinuousAt v 0 := hv.continuousAt
      rw [Metric.continuousAt_iff] at hv_cont
      obtain ⟨η, hη_pos, hη⟩ := hv_cont (δ / 3) (by positivity)
      -- Pick ε = min(η, a, 1) / 4 so that ε ∈ (0, min(η, a, 1)/4] and 2ε is also bounded.
      set ε : ℝ := min (η / 4) (min (a / 4) (1 / 4)) with hε_def
      have hε_pos : 0 < ε := by
        apply lt_min_iff.mpr ⟨by linarith, ?_⟩
        exact lt_min_iff.mpr ⟨by linarith, by norm_num⟩
      have hε_η : ε ≤ η / 4 := min_le_left _ _
      have hε_ah : ε ≤ a / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
      have hε_1h : ε ≤ 1 / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
      have h2ε_lt_1 : 2 * ε ≤ 1 := by linarith
      have h2ε_lt_a : 2 * ε < a := by linarith
      -- Bound 1: CE(0) ≤ 2 CE(ε) - CE(2ε) by concavity.
      have hbound1 := concaveOn_bound_at_zero hCE_conc hε_pos h2ε_lt_1
      -- Bound 2: CE(ε) = v(ε), CE(2ε) = v(2ε) via interior Ioo case.
      have hε_Ioo : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε_pos, by linarith⟩
      have h2ε_pos : 0 < 2 * ε := by linarith
      have h2ε_Ioo : 2 * ε ∈ Ioo (0 : ℝ) 1 := ⟨h2ε_pos, by linarith⟩
      have hCE_ε_le := concaveEnvelope_le_oneGapGlue_of_mem_Ioo
        ha hb hab hvL hvR hmaj hva hvb hε_Ioo
      have hCE_2ε_le := concaveEnvelope_le_oneGapGlue_of_mem_Ioo
        ha hb hab hvL hvR hmaj hva hvb h2ε_Ioo
      have hglue_ε : oneGapGlue v a b slope intercept ε = v ε :=
        oneGapGlue_of_le_a hab hva (by linarith : ε ≤ a)
      have hglue_2ε : oneGapGlue v a b slope intercept (2 * ε) = v (2 * ε) :=
        oneGapGlue_of_le_a hab hva h2ε_lt_a.le
      rw [hglue_ε] at hCE_ε_le
      rw [hglue_2ε] at hCE_2ε_le
      -- Get CE ε = v ε and CE (2ε) = v (2ε) from sandwich
      have hv_ε_le : v ε ≤ concaveEnvelope 0 1 v ε := by
        exact concaveEnvelope_ge_self h01 hv_cont_on ⟨hε_pos.le, by linarith⟩
      have hv_2ε_le : v (2 * ε) ≤ concaveEnvelope 0 1 v (2 * ε) := by
        exact concaveEnvelope_ge_self h01 hv_cont_on ⟨h2ε_pos.le, by linarith⟩
      have hCE_ε_eq : concaveEnvelope 0 1 v ε = v ε := le_antisymm hCE_ε_le hv_ε_le
      have hCE_2ε_eq : concaveEnvelope 0 1 v (2 * ε) = v (2 * ε) :=
        le_antisymm hCE_2ε_le hv_2ε_le
      rw [hCE_ε_eq, hCE_2ε_eq] at hbound1
      -- Bound 3: v(ε) and v(2ε) close to v(0) by continuity.
      have hε_abs : |ε - 0| < η := by
        rw [sub_zero, abs_of_pos hε_pos]; linarith
      have h2ε_abs : |2 * ε - 0| < η := by
        rw [sub_zero, abs_of_pos h2ε_pos]; linarith
      have h_v_ε : |v ε - v 0| < δ / 3 := by
        have := hη (x := ε) (by rw [Real.dist_eq]; exact hε_abs)
        rwa [Real.dist_eq] at this
      have h_v_2ε : |v (2 * ε) - v 0| < δ / 3 := by
        have := hη (x := 2 * ε) (by rw [Real.dist_eq]; exact h2ε_abs)
        rwa [Real.dist_eq] at this
      -- Conclude: CE 0 ≤ 2 v ε - v (2ε) ≤ 2 (v 0 + δ/3) - (v 0 - δ/3) = v 0 + δ.
      rw [abs_lt] at h_v_ε h_v_2ε
      linarith
  · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
    · -- x = 1 (hx1 : x = 1)
      rw [hx1]
      rcases eq_or_lt_of_le hb.2 with hb1 | hb1
      · -- b = 1: glue(1) = affineFun(1) = v(1). CE(1) ≤ g(1) via global majorant.
        rw [oneGapGlue_of_mem_Icc ⟨by linarith [hb1, hab], le_of_eq hb1.symm⟩]
        have hCE_le := concaveEnvelope_le_affineMajorant
          (isAffineMajorant_of_oneGap hmaj) ⟨by norm_num, le_refl _⟩
        simpa [affineFun] using hCE_le
      · -- b < 1. Use boundary-limit.
        have hglue1 : oneGapGlue v a b slope intercept 1 = v 1 :=
          oneGapGlue_of_ge_b hab hvb hb1.le
        rw [hglue1]
        apply le_of_forall_pos_le_add
        intro δ hδ
        have hv_cont : ContinuousAt v 1 := hv.continuousAt
        rw [Metric.continuousAt_iff] at hv_cont
        obtain ⟨η, hη_pos, hη⟩ := hv_cont (δ / 3) (by positivity)
        set ε : ℝ := min (η / 4) (min ((1 - b) / 4) (1 / 4)) with hε_def
        have h1mb : 0 < 1 - b := sub_pos.mpr hb1
        have hε_pos : 0 < ε := by
          apply lt_min_iff.mpr ⟨by linarith, ?_⟩
          exact lt_min_iff.mpr ⟨by linarith, by norm_num⟩
        have hε_η : ε ≤ η / 4 := min_le_left _ _
        have hε_1mbh : ε ≤ (1 - b) / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
        have hε_1h : ε ≤ 1 / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
        have h2ε_lt_1 : 2 * ε ≤ 1 := by linarith
        have h2ε_lt_1mb : 2 * ε < 1 - b := by linarith
        have hbound1 := concaveOn_bound_at_one hCE_conc hε_pos h2ε_lt_1
        have h1ε_Ioo : (1 - ε) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have h12ε_Ioo : (1 - 2 * ε) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have h1ε_ge_b : b ≤ 1 - ε := by linarith
        have h12ε_ge_b : b ≤ 1 - 2 * ε := by linarith
        have hglue_1ε : oneGapGlue v a b slope intercept (1 - ε) = v (1 - ε) :=
          oneGapGlue_of_ge_b hab hvb h1ε_ge_b
        have hglue_12ε : oneGapGlue v a b slope intercept (1 - 2 * ε) = v (1 - 2 * ε) :=
          oneGapGlue_of_ge_b hab hvb h12ε_ge_b
        have hCE_1ε_le := concaveEnvelope_le_oneGapGlue_of_mem_Ioo
          ha hb hab hvL hvR hmaj hva hvb h1ε_Ioo
        have hCE_12ε_le := concaveEnvelope_le_oneGapGlue_of_mem_Ioo
          ha hb hab hvL hvR hmaj hva hvb h12ε_Ioo
        rw [hglue_1ε] at hCE_1ε_le
        rw [hglue_12ε] at hCE_12ε_le
        have hv_1ε_le : v (1 - ε) ≤ concaveEnvelope 0 1 v (1 - ε) :=
          concaveEnvelope_ge_self h01 hv_cont_on ⟨h1ε_Ioo.1.le, h1ε_Ioo.2.le⟩
        have hv_12ε_le : v (1 - 2 * ε) ≤ concaveEnvelope 0 1 v (1 - 2 * ε) :=
          concaveEnvelope_ge_self h01 hv_cont_on ⟨h12ε_Ioo.1.le, h12ε_Ioo.2.le⟩
        have hCE_1ε_eq : concaveEnvelope 0 1 v (1 - ε) = v (1 - ε) :=
          le_antisymm hCE_1ε_le hv_1ε_le
        have hCE_12ε_eq : concaveEnvelope 0 1 v (1 - 2 * ε) = v (1 - 2 * ε) :=
          le_antisymm hCE_12ε_le hv_12ε_le
        rw [hCE_1ε_eq, hCE_12ε_eq] at hbound1
        have h1ε_abs : |(1 - ε) - 1| < η := by
          rw [show (1 - ε) - 1 = -ε from by ring, abs_neg, abs_of_pos hε_pos]
          linarith
        have h12ε_abs : |(1 - 2 * ε) - 1| < η := by
          rw [show (1 - 2 * ε) - 1 = -(2 * ε) from by ring, abs_neg,
            abs_of_pos (by linarith : 0 < 2 * ε)]
          linarith
        have h_v_1ε : |v (1 - ε) - v 1| < δ / 3 := by
          have := hη (x := 1 - ε) (by rw [Real.dist_eq]; exact h1ε_abs)
          rwa [Real.dist_eq] at this
        have h_v_12ε : |v (1 - 2 * ε) - v 1| < δ / 3 := by
          have := hη (x := 1 - 2 * ε) (by rw [Real.dist_eq]; exact h12ε_abs)
          rwa [Real.dist_eq] at this
        rw [abs_lt] at h_v_1ε h_v_12ε
        linarith
    · -- x ∈ Ioo 0 1
      exact concaveEnvelope_le_oneGapGlue_of_mem_Ioo ha hb hab hvL hvR hmaj hva hvb
        ⟨hx0, hx1⟩

/-- `concaveEnvelope 0 1 v = oneGapGlue v a b slope intercept` on `Icc 0 1`. -/
lemma concaveEnvelope_eq_oneGapGlue
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hvL : ConcaveOn ℝ (Icc (0 : ℝ) a) v)
    (hvR : ConcaveOn ℝ (Icc b 1) v)
    (hv : Continuous v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    concaveEnvelope 0 1 v x = oneGapGlue v a b slope intercept x :=
  le_antisymm
    (concaveEnvelope_le_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hx)
    (concaveEnvelope_ge_oneGapGlue ha hb hab hv hmaj hva hvb hx)

/-- **Main envelope theorem under a one-gap chord.** The concave envelope of a continuous `v` on
`[0,1]` with one-gap chord data coincides with `v` on each tail and with the chord on the middle
interval. -/
theorem concaveEnvelope_eq_of_oneGapChord
    {v : ℝ → ℝ} (hv : Continuous v) (hgap : HasOneGapChord v) :
    ∃ a b slope intercept,
      a ∈ Icc (0 : ℝ) 1 ∧
      b ∈ Icc (0 : ℝ) 1 ∧
      a < b ∧
      (∀ x ∈ Icc (0 : ℝ) a,
        concaveEnvelope (0 : ℝ) 1 v x = v x) ∧
      (∀ x ∈ Icc a b,
        concaveEnvelope (0 : ℝ) 1 v x = affineFun slope intercept x) ∧
      (∀ x ∈ Icc b 1,
        concaveEnvelope (0 : ℝ) 1 v x = v x) := by
  obtain ⟨a, b, slope, intercept, ha, hb, hab, hvL, hvR, hmaj, hva, hvb, _⟩ := hgap
  refine ⟨a, b, slope, intercept, ha, hb, hab, ?_, ?_, ?_⟩
  · -- On left tail [0, a]: CE = v.
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans ha.2⟩
    have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
    rw [hCE_eq]
    exact oneGapGlue_of_le_a hab hva hx.2
  · -- On middle [a, b]: CE = affineFun.
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
    rw [hCE_eq]
    exact oneGapGlue_of_mem_Icc hx
  · -- On right tail [b, 1]: CE = v.
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hb.1.trans hx.1, hx.2⟩
    have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
    rw [hCE_eq]
    exact oneGapGlue_of_ge_b hab hvb hx.1

/-- **Strict separation on the open middle.** Under a one-gap chord, the concave envelope strictly
exceeds `v` on `(a, b)`. -/
theorem concaveEnvelope_strict_gt_on_oneGap
    {v : ℝ → ℝ} (hv : Continuous v) (hgap : HasOneGapChord v) :
    ∃ a b,
      a ∈ Icc (0 : ℝ) 1 ∧
      b ∈ Icc (0 : ℝ) 1 ∧
      a < b ∧
      (∀ x ∈ Ioo a b, v x < concaveEnvelope (0 : ℝ) 1 v x) := by
  obtain ⟨a, b, slope, intercept, ha, hb, hab, hvL, hvR, hmaj, hva, hvb, hstrict⟩ := hgap
  refine ⟨a, b, ha, hb, hab, ?_⟩
  intro x hx
  have hxIcc_ab : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hxIcc_ab.1, hxIcc_ab.2.trans hb.2⟩
  have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
  rw [hCE_eq, oneGapGlue_of_mem_Icc hxIcc_ab]
  exact hstrict x hx

/-- **Contact-set formulation.** The set where the concave envelope agrees with `v` on `[0, 1]` is
exactly the union of the two closed tails. -/
theorem contactSet_of_oneGapChord
    {v : ℝ → ℝ} (hv : Continuous v) (hgap : HasOneGapChord v) :
    ∃ a b,
      a ∈ Icc (0 : ℝ) 1 ∧
      b ∈ Icc (0 : ℝ) 1 ∧
      a < b ∧
      {x | x ∈ Icc (0 : ℝ) 1 ∧ concaveEnvelope (0 : ℝ) 1 v x = v x}
        = Icc (0 : ℝ) a ∪ Icc b 1 := by
  obtain ⟨a, b, slope, intercept, ha, hb, hab, hvL, hvR, hmaj, hva, hvb, hstrict⟩ := hgap
  refine ⟨a, b, ha, hb, hab, ?_⟩
  ext x
  constructor
  · rintro ⟨hxIcc, heq⟩
    by_contra hnot
    rw [Set.mem_union] at hnot
    push Not at hnot
    have hxa : a < x := by
      by_contra hle
      push Not at hle
      exact hnot.1 ⟨hxIcc.1, hle⟩
    have hxb : x < b := by
      by_contra hle
      push Not at hle
      exact hnot.2 ⟨hle, hxIcc.2⟩
    have hx_ab : x ∈ Ioo a b := ⟨hxa, hxb⟩
    have hx_Icc : x ∈ Icc a b := ⟨hxa.le, hxb.le⟩
    have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
    rw [hCE_eq, oneGapGlue_of_mem_Icc hx_Icc] at heq
    have := hstrict x hx_ab
    linarith
  · rintro (hxL | hxR)
    · -- x ∈ [0, a]
      refine ⟨⟨hxL.1, hxL.2.trans ha.2⟩, ?_⟩
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hxL.1, hxL.2.trans ha.2⟩
      have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
      rw [hCE_eq]
      exact oneGapGlue_of_le_a hab hva hxL.2
    · -- x ∈ [b, 1]
      refine ⟨⟨hb.1.trans hxR.1, hxR.2⟩, ?_⟩
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hb.1.trans hxR.1, hxR.2⟩
      have hCE_eq := concaveEnvelope_eq_oneGapGlue ha hb hab hvL hvR hv hmaj hva hvb hxIcc
      rw [hCE_eq]
      exact oneGapGlue_of_ge_b hab hvb hxR.1
