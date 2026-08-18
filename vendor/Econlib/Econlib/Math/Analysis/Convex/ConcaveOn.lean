/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Four-point inequalities for concave functions on `ℝ`

Two consequences of concavity for a real function on a convex set: A four-point Schur-type
inequality (more balanced pairs with equal sum have larger total value) and the
diminishing-increments property (the increment `f(x + h) - f(x)` is antitone in `x`).

## Main results

* `ConcaveOn.outer_add_le_inner_add` — the four-point Schur inequality.
* `ConcaveOn.antitone_increment` — diminishing increments.
-/

@[expose] public section

open Set

/-- **Four-point Schur inequality for concave functions.** If `a ≤ b ≤ c ≤ d` with `b + c = a + d`
(same sum, more balanced), then `f(a) + f(d) ≤ f(b) + f(c)`. -/
lemma ConcaveOn.outer_add_le_inner_add {f : ℝ → ℝ} {S : Set ℝ}
    (hf : ConcaveOn ℝ S f)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (ha : a ∈ S) (hd : d ∈ S) (hsum : b + c = a + d) :
    f a + f d ≤ f b + f c := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · have hcd' : c = d := by linarith
    rw [← hcd']
  rcases eq_or_lt_of_le hcd with hcd_eq | hcd_lt
  · -- c = d, contradicts a < b ≤ c = d with b + c = a + d
    linarith
  have had : a < d := lt_of_lt_of_le (lt_of_lt_of_le hab_lt hbc) (le_of_lt hcd_lt)
  have hda_pos : (0 : ℝ) < d - a := sub_pos.mpr had
  have hda_ne : d - a ≠ 0 := ne_of_gt hda_pos
  set t := (d - b) / (d - a)
  have ht_pos : 0 < t := div_pos (sub_pos.mpr (lt_of_le_of_lt hbc hcd_lt)) hda_pos
  have ht_lt : t < 1 := by rw [div_lt_one hda_pos]; linarith
  have h1t_nn : 0 ≤ 1 - t := by linarith
  have htda : t * (d - a) = d - b := by
    rw [show t = (d - b) / (d - a) from rfl, div_mul_cancel₀ _ hda_ne]
  have hb_eq : b = t * a + (1 - t) * d := by nlinarith
  have hc_eq : c = (1 - t) * a + t * d := by linarith
  have h1 : t * f a + (1 - t) * f d ≤ f b := by
    rw [hb_eq]; exact hf.2 ha hd (le_of_lt ht_pos) h1t_nn (by linarith)
  have h2 : (1 - t) * f a + t * f d ≤ f c := by
    rw [hc_eq]; exact hf.2 ha hd h1t_nn (le_of_lt ht_pos) (by linarith)
  linarith

/-- **Diminishing differences for concave functions.** The increment `f(x + h) − f(x)` is antitone
in `x`: Higher base values yield smaller increments. -/
lemma ConcaveOn.antitone_increment {f : ℝ → ℝ} {S : Set ℝ}
    (hf : ConcaveOn ℝ S f)
    {x₁ x₂ h : ℝ} (hx : x₁ ≤ x₂) (hh : 0 ≤ h)
    -- kept for symmetry of specification: membership of all four points x₁, x₁+h, x₂, x₂+h
    (hx₁ : x₁ ∈ S) (_hx₁h : x₁ + h ∈ S)
    (_hx₂ : x₂ ∈ S) (hx₂h : x₂ + h ∈ S) :
    f (x₂ + h) - f x₂ ≤ f (x₁ + h) - f x₁ := by
  suffices key : f x₁ + f (x₂ + h) ≤ f (x₁ + h) + f x₂ by linarith
  -- Four points: x₁, x₁+h, x₂, x₂+h. Sort middle two.
  by_cases hle : x₁ + h ≤ x₂
  · -- Order: x₁ ≤ x₁+h ≤ x₂ ≤ x₂+h
    have := ConcaveOn.outer_add_le_inner_add hf (show x₁ ≤ x₁ + h by linarith) hle
      (show x₂ ≤ x₂ + h by linarith) hx₁ hx₂h
      (show x₁ + h + x₂ = x₁ + (x₂ + h) by ring)
    linarith
  · -- Order: x₁ ≤ x₂ ≤ x₁+h ≤ x₂+h
    push Not at hle
    have := ConcaveOn.outer_add_le_inner_add hf hx (le_of_lt hle)
      (show x₁ + h ≤ x₂ + h by linarith) hx₁ hx₂h
      (show x₂ + (x₁ + h) = x₁ + (x₂ + h) by ring)
    linarith
