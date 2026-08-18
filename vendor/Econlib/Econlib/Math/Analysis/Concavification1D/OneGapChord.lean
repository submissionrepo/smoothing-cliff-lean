/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.EnvelopeDuality

open MeasureTheory Set

/-!
# One-gap chord geometry

1D concavification geometry for payoffs with a single affine bridge: A continuous `v` on `[0, 1]`,
concave on a left tail `[0, a]` and right tail `[b, 1]`, with a chord `g x = slope * x + intercept`
that dominates `v` everywhere on `[0, 1]`, touches `v` at `a` and `b`, and strictly dominates `v`
on `(a, b)`. Under this geometry the concave envelope coincides with `v` on the tails, agrees with
the chord on `[a, b]`, and the non-contact region is exactly `(a, b)`.

## Main definitions

* `HasOneGapChord v` — the single-chord geometry predicate.
* `oneGapGlue v a b slope intercept` — the function equal to the chord on `[a, b]` and to `v`
  elsewhere.

## Main statements

* `oneGapGlue_concaveOn` — the glued function is concave on `[0, 1]`.

## Tags

concave envelope, affine chord, concavification, ironing
-/

@[expose] public section

/-- `HasOneGapChord v`: There exist `a, b ∈ [0, 1]` with `a < b` and an affine function
`g = affineFun slope intercept` such that

* `v` is concave on the left tail `[0, a]` and on the right tail `[b, 1]`;
* `g` weakly dominates `v` on the whole interval `[0, 1]`;
* `v` touches the chord `g` at the two endpoints `a` and `b`;
* `g` strictly dominates `v` on the open middle `(a, b)`.

This is the single-chord geometry that drives 1D concavification in applications.

The global-majorant clause `∀ x ∈ Icc 0 1, v x ≤ g x` is load-bearing: Without it, `v` could sit
above the chord's affine extension on a tail (the concave tail need not be tangent to the chord),
and then the concave envelope would strictly exceed `v` on parts of the tail. -/
def HasOneGapChord (v : ℝ → ℝ) : Prop :=
  ∃ a b slope intercept,
    a ∈ Icc (0 : ℝ) 1 ∧
    b ∈ Icc (0 : ℝ) 1 ∧
    a < b ∧
    ConcaveOn ℝ (Icc (0 : ℝ) a) v ∧
    ConcaveOn ℝ (Icc b 1) v ∧
    (∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x) ∧
    v a = affineFun slope intercept a ∧
    v b = affineFun slope intercept b ∧
    (∀ x ∈ Ioo a b, v x < affineFun slope intercept x)

/-- The glued function, equal to the chord `affineFun slope intercept` on `[a, b]` and to `v`
elsewhere. Under `HasOneGapChord v`, this is the concave envelope on `[0, 1]`. -/
noncomputable def oneGapGlue (v : ℝ → ℝ) (a b slope intercept : ℝ) (x : ℝ) : ℝ :=
  if a ≤ x ∧ x ≤ b then affineFun slope intercept x else v x

/-- On the middle `[a, b]`, the glued function equals the chord. -/
lemma oneGapGlue_of_mem_Icc {v : ℝ → ℝ} {a b slope intercept x : ℝ}
    (hx : x ∈ Icc a b) :
    oneGapGlue v a b slope intercept x = affineFun slope intercept x := by
  unfold oneGapGlue
  simp [hx.1, hx.2]

/-- Strictly left of `a`, the glued function equals `v`. -/
lemma oneGapGlue_of_lt {v : ℝ → ℝ} {a b slope intercept x : ℝ} (hx : x < a) :
    oneGapGlue v a b slope intercept x = v x := by
  unfold oneGapGlue
  have : ¬ (a ≤ x ∧ x ≤ b) := fun h => absurd h.1 (not_le.mpr hx)
  simp [this]

/-- Strictly right of `b`, the glued function equals `v`. -/
lemma oneGapGlue_of_gt {v : ℝ → ℝ} {a b slope intercept x : ℝ} (hx : b < x) :
    oneGapGlue v a b slope intercept x = v x := by
  unfold oneGapGlue
  have : ¬ (a ≤ x ∧ x ≤ b) := fun h => absurd h.2 (not_le.mpr hx)
  simp [this]

/-- On the closed left tail `x ≤ a`, the glued function equals `v` (using the contact `v a = g a`
at the endpoint). -/
lemma oneGapGlue_of_le_a {v : ℝ → ℝ} {a b slope intercept x : ℝ}
    (hab : a < b) (hva : v a = affineFun slope intercept a) (hx : x ≤ a) :
    oneGapGlue v a b slope intercept x = v x := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact oneGapGlue_of_lt hlt
  · subst heq
    rw [oneGapGlue_of_mem_Icc ⟨le_refl _, le_of_lt hab⟩, hva]

/-- On the closed right tail `b ≤ x`, the glued function equals `v` (using the contact `v b = g b`
at the endpoint). -/
lemma oneGapGlue_of_ge_b {v : ℝ → ℝ} {a b slope intercept x : ℝ}
    (hab : a < b) (hvb : v b = affineFun slope intercept b) (hx : b ≤ x) :
    oneGapGlue v a b slope intercept x = v x := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact oneGapGlue_of_gt hlt
  · subst heq
    rw [oneGapGlue_of_mem_Icc ⟨le_of_lt hab, le_refl _⟩, hvb]

/-- `v ≤ oneGapGlue v` on `[0, 1]` under the one-gap chord hypothesis. -/
lemma v_le_oneGapGlue {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (hab : a < b)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    v x ≤ oneGapGlue v a b slope intercept x := by
  by_cases hxa : x ≤ a
  · rw [oneGapGlue_of_le_a hab hva hxa]
  · by_cases hxb : b ≤ x
    · rw [oneGapGlue_of_ge_b hab hvb hxb]
    · push Not at hxa hxb
      have hxmem : x ∈ Icc a b := ⟨le_of_lt hxa, le_of_lt hxb⟩
      rw [oneGapGlue_of_mem_Icc hxmem]
      exact hmaj x hx

/-- From global majorant, `v ≤ g` on `[0, a]` together with `v(a) = g(a)` gives that every secant
slope from a point in `[0, a)` to `a` is at least `slope`. -/
lemma slope_to_a_ge_slope {v : ℝ → ℝ} {a slope intercept : ℝ}
    (hmaj : ∀ x ∈ Icc (0 : ℝ) a, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) a) :
    slope ≤ (v a - v x) / (a - x) := by
  have hlt : x < a := hx.2
  have hpos : 0 < a - x := sub_pos.mpr hlt
  have hvx : v x ≤ affineFun slope intercept x :=
    hmaj x ⟨hx.1, le_of_lt hlt⟩
  have h1 : affineFun slope intercept a - affineFun slope intercept x =
            slope * (a - x) := by
    simp [affineFun]; ring
  exact (le_div_iff₀ hpos).mpr (by linarith [hvx, hva])

/-- From global majorant on `[b, 1]` and `v(b) = g(b)`, every secant slope from `b` to a point in
`(b, 1]` is at most `slope`. -/
lemma slope_from_b_le_slope {v : ℝ → ℝ} {b slope intercept : ℝ}
    (hmaj : ∀ x ∈ Icc b (1 : ℝ), v x ≤ affineFun slope intercept x)
    (hvb : v b = affineFun slope intercept b)
    {y : ℝ} (hy : y ∈ Ioc b (1 : ℝ)) :
    (v y - v b) / (y - b) ≤ slope := by
  have hlt : b < y := hy.1
  have hpos : 0 < y - b := sub_pos.mpr hlt
  have hvy : v y ≤ affineFun slope intercept y :=
    hmaj y ⟨le_of_lt hlt, hy.2⟩
  have h1 : affineFun slope intercept y - affineFun slope intercept b =
            slope * (y - b) := by
    simp [affineFun]; ring
  exact (div_le_iff₀ hpos).mpr (by linarith [hvy, hvb])

/-- Global majorant specialized: `g` is an affine majorant of `v` on `Icc 0 1`. -/
lemma isAffineMajorant_of_oneGap {v : ℝ → ℝ} {slope intercept : ℝ}
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x) :
    IsAffineMajorant 0 1 v slope intercept := by
  intro t ht
  simpa [affineFun] using hmaj t ht

/-- `v ≤ g` on `[0, a]`, inherited from the global majorant and `Icc 0 a ⊆ Icc 0 1`. -/
lemma v_le_chord_on_left {v : ℝ → ℝ} {a slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x) :
    ∀ x ∈ Icc (0 : ℝ) a, v x ≤ affineFun slope intercept x := by
  intro x hx
  exact hmaj x ⟨hx.1, hx.2.trans ha.2⟩

/-- `v ≤ g` on `[b, 1]`, inherited from the global majorant and `Icc b 1 ⊆ Icc 0 1`. -/
lemma v_le_chord_on_right {v : ℝ → ℝ} {b slope intercept : ℝ}
    (hb : b ∈ Icc (0 : ℝ) 1)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x) :
    ∀ x ∈ Icc b (1 : ℝ), v x ≤ affineFun slope intercept x := by
  intro x hx
  exact hmaj x ⟨hb.1.trans hx.1, hx.2⟩

/-- For `y ∈ [0, a)` and `z ∈ (a, 1]`, the glue-slope from `y` to `z` is bounded by the `v`-secant
slope from `y` to `a`. The crossing-through-`a` inequality used to prove concavity of the glue. -/
lemma oneGapGlue_slope_crossing_a
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_ha : a ∈ Icc (0 : ℝ) 1) (_hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {y z : ℝ} (hyIcc : y ∈ Icc (0 : ℝ) 1) (hzIcc : z ∈ Icc (0 : ℝ) 1)
    (hya : y < a) (haz : a < z) :
    (oneGapGlue v a b slope intercept z
      - oneGapGlue v a b slope intercept y) / (z - y)
    ≤ (v a - v y) / (a - y) := by
  have hfy : oneGapGlue v a b slope intercept y = v y :=
    oneGapGlue_of_le_a hab hva (le_of_lt hya)
  have hfz_le : oneGapGlue v a b slope intercept z ≤ affineFun slope intercept z := by
    by_cases hzb : z ≤ b
    · rw [oneGapGlue_of_mem_Icc ⟨le_of_lt haz, hzb⟩]
    · push Not at hzb
      rw [oneGapGlue_of_ge_b hab hvb (le_of_lt hzb)]
      exact hmaj z hzIcc
  have hpos_zy : 0 < z - y := sub_pos.mpr (lt_trans hya haz)
  have hpos_ay : 0 < a - y := sub_pos.mpr hya
  have hvy_le_gy : v y ≤ affineFun slope intercept y := hmaj y hyIcc
  have step1 : (oneGapGlue v a b slope intercept z - v y) / (z - y)
             ≤ (affineFun slope intercept z - v y) / (z - y) := by
    exact div_le_div_of_nonneg_right (by linarith) hpos_zy.le
  have step2 : (affineFun slope intercept z - v y) / (z - y)
             ≤ (affineFun slope intercept a - v y) / (a - y) := by
    rw [div_le_div_iff₀ hpos_zy hpos_ay]
    have key : (affineFun slope intercept z - v y) * (a - y)
             - (affineFun slope intercept a - v y) * (z - y)
             = (a - z) * (affineFun slope intercept y - v y) := by
      simp only [affineFun]; ring
    nlinarith [sub_nonneg.mpr hvy_le_gy, sub_neg.mpr haz]
  calc (oneGapGlue v a b slope intercept z
          - oneGapGlue v a b slope intercept y) / (z - y)
      = (oneGapGlue v a b slope intercept z - v y) / (z - y) := by rw [hfy]
    _ ≤ (affineFun slope intercept z - v y) / (z - y) := step1
    _ ≤ (affineFun slope intercept a - v y) / (a - y) := step2
    _ = (v a - v y) / (a - y) := by rw [hva]

/-- For `x ∈ [0, b)` and `y ∈ (b, 1]`, the glue-slope from `x` to `y` is bounded below by the
`v`-secant slope from `b` to `y`. -/
lemma oneGapGlue_slope_crossing_b
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_ha : a ∈ Icc (0 : ℝ) 1) (_hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x y : ℝ} (hxIcc : x ∈ Icc (0 : ℝ) 1) (hyIcc : y ∈ Icc (0 : ℝ) 1)
    (hxb : x < b) (hby : b < y) :
    (v y - v b) / (y - b)
    ≤ (oneGapGlue v a b slope intercept y
        - oneGapGlue v a b slope intercept x) / (y - x) := by
  have hfy : oneGapGlue v a b slope intercept y = v y :=
    oneGapGlue_of_ge_b hab hvb (le_of_lt hby)
  have hfx_ge : affineFun slope intercept x ≥ oneGapGlue v a b slope intercept x := by
    by_cases hxa : a ≤ x
    · rw [oneGapGlue_of_mem_Icc ⟨hxa, le_of_lt hxb⟩]
    · push Not at hxa
      rw [oneGapGlue_of_le_a hab hva (le_of_lt hxa)]
      exact hmaj x hxIcc
  have hpos_yx : 0 < y - x := sub_pos.mpr (lt_trans hxb hby)
  have hpos_yb : 0 < y - b := sub_pos.mpr hby
  have hvx_le_gx : v x ≤ affineFun slope intercept x := hmaj x hxIcc
  have step1 : (v y - affineFun slope intercept x) / (y - x)
             ≤ (v y - oneGapGlue v a b slope intercept x) / (y - x) := by
    exact div_le_div_of_nonneg_right (by linarith) hpos_yx.le
  have step2 : (v y - affineFun slope intercept b) / (y - b)
             ≤ (v y - affineFun slope intercept x) / (y - x) := by
    rw [div_le_div_iff₀ hpos_yb hpos_yx]
    have key : (v y - affineFun slope intercept x) * (y - b)
             - (v y - affineFun slope intercept b) * (y - x)
             = (b - x) * (affineFun slope intercept y - v y) := by
      simp only [affineFun]; ring
    have hvy_le_gy : v y ≤ affineFun slope intercept y := hmaj y hyIcc
    nlinarith [sub_nonneg.mpr hvy_le_gy, sub_pos.mpr hxb]
  calc (v y - v b) / (y - b)
      = (v y - affineFun slope intercept b) / (y - b) := by rw [hvb]
    _ ≤ (v y - affineFun slope intercept x) / (y - x) := step2
    _ ≤ (v y - oneGapGlue v a b slope intercept x) / (y - x) := step1
    _ = (oneGapGlue v a b slope intercept y
          - oneGapGlue v a b slope intercept x) / (y - x) := by rw [hfy]

/-- For `x ∈ [0, 1]` with `x ≤ b`, and `y ∈ [a, b]` with `x < y`, the glue-slope from `x` to `y` is
at least the chord slope. -/
lemma oneGapGlue_slope_to_middle_ge_slope
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_ha : a ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hvb : v b = affineFun slope intercept b)
    {x y : ℝ} (hxIcc : x ∈ Icc (0 : ℝ) 1)
    (hxb : x ≤ b) (hay : a ≤ y) (hyb : y ≤ b) (hxy : x < y) :
    slope ≤ (oneGapGlue v a b slope intercept y
              - oneGapGlue v a b slope intercept x) / (y - x) := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have hfy : oneGapGlue v a b slope intercept y = affineFun slope intercept y :=
    oneGapGlue_of_mem_Icc ⟨hay, hyb⟩
  have h1 : affineFun slope intercept y - affineFun slope intercept x
          = slope * (y - x) := by simp only [affineFun]; ring
  rcases le_or_gt x a with hxa | hxa
  · have hfx : oneGapGlue v a b slope intercept x = v x :=
      oneGapGlue_of_le_a hab hva hxa
    have hvx_le : v x ≤ affineFun slope intercept x := hmaj x hxIcc
    rw [hfx, hfy, le_div_iff₀ hpos]
    linarith
  · have hfx : oneGapGlue v a b slope intercept x = affineFun slope intercept x :=
      oneGapGlue_of_mem_Icc ⟨hxa.le, hxb⟩
    rw [hfx, hfy, le_div_iff₀ hpos]
    linarith

/-- Symmetric to `oneGapGlue_slope_to_middle_ge_slope`: For `y ∈ [0, 1]` with `a ≤ y`, and
`x ∈ [a, b]` with `x < y`, the glue-slope from `x` to `y` is at most the chord slope. -/
lemma oneGapGlue_slope_from_middle_le_slope
    {v : ℝ → ℝ} {a b slope intercept : ℝ}
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {x y : ℝ} (hyIcc : y ∈ Icc (0 : ℝ) 1)
    (hax : a ≤ x) (hxb : x ≤ b) (hay : a ≤ y) (hxy : x < y) :
    (oneGapGlue v a b slope intercept y
      - oneGapGlue v a b slope intercept x) / (y - x) ≤ slope := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have hfx : oneGapGlue v a b slope intercept x = affineFun slope intercept x :=
    oneGapGlue_of_mem_Icc ⟨hax, hxb⟩
  have h1 : affineFun slope intercept y - affineFun slope intercept x
          = slope * (y - x) := by simp only [affineFun]; ring
  rcases le_or_gt y b with hyb | hyb
  · have hfy : oneGapGlue v a b slope intercept y = affineFun slope intercept y :=
      oneGapGlue_of_mem_Icc ⟨hay, hyb⟩
    rw [hfx, hfy, div_le_iff₀ hpos]
    linarith
  · have hfy : oneGapGlue v a b slope intercept y = v y :=
      oneGapGlue_of_ge_b hab hvb hyb.le
    have hvy_le : v y ≤ affineFun slope intercept y := hmaj y hyIcc
    rw [hfx, hfy, div_le_iff₀ hpos]
    linarith

/-- For `y > a` and `y ∈ [0, 1]`, the slope from `a` (in `oneGapGlue`) to `y` is at most the chord
slope. Handles both `y ≤ b` (slope = chord slope via `g`) and `y > b` (via the global majorant on
the right tail). -/
lemma oneGapGlue_slope_from_a_le_slope
    {v : ℝ → ℝ} {a b slope intercept : ℝ} (hab : a < b)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hb : b ∈ Icc (0 : ℝ) 1)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b)
    {y : ℝ} (hyIcc : y ∈ Icc (0 : ℝ) 1) (hay : a < y) :
    (oneGapGlue v a b slope intercept y
      - oneGapGlue v a b slope intercept a) / (y - a) ≤ slope := by
  have hfa : oneGapGlue v a b slope intercept a = affineFun slope intercept a :=
    oneGapGlue_of_mem_Icc ⟨le_refl _, hab.le⟩
  have hpos : 0 < y - a := sub_pos.mpr hay
  have heq : affineFun slope intercept y - affineFun slope intercept a
           = slope * (y - a) := by simp only [affineFun]; ring
  rcases le_or_gt y b with hyb | hyb
  · have hfy : oneGapGlue v a b slope intercept y = affineFun slope intercept y :=
      oneGapGlue_of_mem_Icc ⟨hay.le, hyb⟩
    rw [hfa, hfy, div_le_iff₀ hpos]
    linarith
  · have hfy : oneGapGlue v a b slope intercept y = v y :=
      oneGapGlue_of_ge_b hab hvb hyb.le
    rw [hfa, hfy, div_le_iff₀ hpos]
    have hvy_le : v y ≤ affineFun slope intercept y := hmaj y hyIcc
    linarith

/-- For `x < b` and `x ∈ [0, 1]`, the slope from `x` to `b` (in `oneGapGlue`) is at least the chord
slope. Handles both `x ≥ a` (slope = chord slope via `g`) and `x < a` (via the global majorant on
the left tail). -/
lemma oneGapGlue_slope_to_b_ge_slope
    {v : ℝ → ℝ} {a b slope intercept : ℝ} (hab : a < b)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_ha : a ∈ Icc (0 : ℝ) 1)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    -- Kept for signature uniformity with the other crossing/middle lemmas called alongside it.
    (_hvb : v b = affineFun slope intercept b)
    {x : ℝ} (hxIcc : x ∈ Icc (0 : ℝ) 1) (hxb : x < b) :
    slope ≤ (oneGapGlue v a b slope intercept b
      - oneGapGlue v a b slope intercept x) / (b - x) := by
  have hfb : oneGapGlue v a b slope intercept b = affineFun slope intercept b :=
    oneGapGlue_of_mem_Icc ⟨hab.le, le_refl _⟩
  have hpos : 0 < b - x := sub_pos.mpr hxb
  have heq : affineFun slope intercept b - affineFun slope intercept x
           = slope * (b - x) := by simp only [affineFun]; ring
  rcases le_or_gt x a with hxa | hxa
  · have hfx : oneGapGlue v a b slope intercept x = v x :=
      oneGapGlue_of_le_a hab hva hxa
    rw [hfb, hfx, le_div_iff₀ hpos]
    have hvx_le : v x ≤ affineFun slope intercept x := hmaj x hxIcc
    linarith
  · have hfx : oneGapGlue v a b slope intercept x = affineFun slope intercept x :=
      oneGapGlue_of_mem_Icc ⟨hxa.le, hxb.le⟩
    rw [hfb, hfx, le_div_iff₀ hpos]
    linarith

/-- Concavity of the glued function on `Icc 0 1`, via case analysis on the middle point `y`'s
position relative to `a` and `b`. -/
lemma oneGapGlue_concaveOn {v : ℝ → ℝ} {a b slope intercept : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b)
    (hvL : ConcaveOn ℝ (Icc (0 : ℝ) a) v)
    (hvR : ConcaveOn ℝ (Icc b 1) v)
    (hmaj : ∀ x ∈ Icc (0 : ℝ) 1, v x ≤ affineFun slope intercept x)
    (hva : v a = affineFun slope intercept a)
    (hvb : v b = affineFun slope intercept b) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (oneGapGlue v a b slope intercept) := by
  refine concaveOn_of_slope_anti_adjacent (convex_Icc _ _) ?_
  intro x y z hx hz hxy hyz
  have hxz : x < z := lt_trans hxy hyz
  have hyIcc : y ∈ Icc (0 : ℝ) 1 :=
    ⟨hx.1.trans hxy.le, hyz.le.trans hz.2⟩
  -- Case split on middle `y`.
  rcases lt_trichotomy y a with hya | hya | hya
  · -- y < a.
    have hxa : x < a := lt_trans hxy hya
    have hx' : x ∈ Icc (0 : ℝ) a := ⟨hx.1, hxa.le⟩
    have hy' : y ∈ Icc (0 : ℝ) a := ⟨hyIcc.1, hya.le⟩
    have ha' : a ∈ Icc (0 : ℝ) a := ⟨ha.1, le_refl _⟩
    have hfx : oneGapGlue v a b slope intercept x = v x :=
      oneGapGlue_of_le_a hab hva hxa.le
    have hfy : oneGapGlue v a b slope intercept y = v y :=
      oneGapGlue_of_le_a hab hva hya.le
    rcases le_or_gt z a with hza | haz
    · have hz' : z ∈ Icc (0 : ℝ) a := ⟨hx.1.trans hxz.le, hza⟩
      have hfz : oneGapGlue v a b slope intercept z = v z :=
        oneGapGlue_of_le_a hab hva hza
      rw [hfx, hfy, hfz]
      exact hvL.slope_anti_adjacent hx' hz' hxy hyz
    · have hcross : (oneGapGlue v a b slope intercept z
                    - oneGapGlue v a b slope intercept y) / (z - y)
                  ≤ (v a - v y) / (a - y) :=
        oneGapGlue_slope_crossing_a ha hb hab hmaj hva hvb hyIcc hz hya haz
      have hconc : (v a - v y) / (a - y) ≤ (v y - v x) / (y - x) :=
        hvL.slope_anti_adjacent hx' ha' hxy hya
      rw [hfx, hfy]
      rw [hfy] at hcross
      exact le_trans hcross hconc
  · -- y = a.
    have hxa : x < a := hya ▸ hxy
    have haz : a < z := hya ▸ hyz
    have hfx : oneGapGlue v a b slope intercept x = v x :=
      oneGapGlue_of_le_a hab hva hxa.le
    have hfa : oneGapGlue v a b slope intercept a = v a :=
      oneGapGlue_of_le_a hab hva (le_refl _)
    have hleft : slope ≤ (oneGapGlue v a b slope intercept a
                  - oneGapGlue v a b slope intercept x) / (a - x) := by
      rw [hfx, hfa]
      exact slope_to_a_ge_slope (v_le_chord_on_left ha hmaj) hva ⟨hx.1, hxa⟩
    have hright : (oneGapGlue v a b slope intercept z
                  - oneGapGlue v a b slope intercept a) / (z - a) ≤ slope :=
      oneGapGlue_slope_from_a_le_slope hab hb hmaj hva hvb hz haz
    rw [hya]
    linarith
  · -- y > a. Split on y vs b.
    rcases lt_trichotomy y b with hyb | hyb | hyb
    · -- a < y < b. y strictly in open middle.
      have hleft : slope ≤ (oneGapGlue v a b slope intercept y
                    - oneGapGlue v a b slope intercept x) / (y - x) :=
        oneGapGlue_slope_to_middle_ge_slope ha hab hmaj hva hvb hx
          (hxy.le.trans hyb.le) hya.le hyb.le hxy
      have hright : (oneGapGlue v a b slope intercept z
                    - oneGapGlue v a b slope intercept y) / (z - y) ≤ slope :=
        oneGapGlue_slope_from_middle_le_slope hb hab hmaj hva hvb hz
          hya.le hyb.le (hya.le.trans hyz.le) hyz
      linarith
    · -- y = b.
      have hxb : x < b := hyb ▸ hxy
      have hbz : b < z := hyb ▸ hyz
      have hleft : slope ≤ (oneGapGlue v a b slope intercept b
                    - oneGapGlue v a b slope intercept x) / (b - x) :=
        oneGapGlue_slope_to_b_ge_slope hab ha hmaj hva hvb hx hxb
      have hright : (oneGapGlue v a b slope intercept z
                    - oneGapGlue v a b slope intercept b) / (z - b) ≤ slope :=
        oneGapGlue_slope_from_middle_le_slope hb hab hmaj hva hvb hz
          hab.le (le_refl _) (hab.le.trans hbz.le) hbz
      rw [hyb]
      linarith
    · -- y > b. y, z ∈ (b, 1], x possibly in any of three regions.
      have hyb_le : b ≤ y := hyb.le
      have hz_gt_b : b < z := lt_trans hyb hyz
      have hfy : oneGapGlue v a b slope intercept y = v y :=
        oneGapGlue_of_ge_b hab hvb hyb_le
      have hfz : oneGapGlue v a b slope intercept z = v z :=
        oneGapGlue_of_ge_b hab hvb hz_gt_b.le
      have hy' : y ∈ Icc b (1 : ℝ) := ⟨hyb_le, hyIcc.2⟩
      have hz' : z ∈ Icc b (1 : ℝ) := ⟨hz_gt_b.le, hz.2⟩
      have hb' : b ∈ Icc b (1 : ℝ) := ⟨le_refl _, hb.2⟩
      rcases le_or_gt b x with hbx | hxb
      · have hx' : x ∈ Icc b (1 : ℝ) := ⟨hbx, hx.2⟩
        have hfx : oneGapGlue v a b slope intercept x = v x :=
          oneGapGlue_of_ge_b hab hvb hbx
        rw [hfx, hfy, hfz]
        exact hvR.slope_anti_adjacent hx' hz' hxy hyz
      · have hcross : (v y - v b) / (y - b)
                    ≤ (oneGapGlue v a b slope intercept y
                        - oneGapGlue v a b slope intercept x) / (y - x) :=
          oneGapGlue_slope_crossing_b ha hb hab hmaj hva hvb hx hyIcc hxb hyb
        have hconc : (v z - v y) / (z - y) ≤ (v y - v b) / (y - b) :=
          hvR.slope_anti_adjacent hb' hz' hyb hyz
        rw [hfy, hfz]
        rw [hfy] at hcross
        exact le_trans hconc hcross
