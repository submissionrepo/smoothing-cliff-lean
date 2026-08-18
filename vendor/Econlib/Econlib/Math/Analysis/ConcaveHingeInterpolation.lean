/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.HingeConvex
public import Mathlib.Analysis.Convex.Slope

/-!
# Concave functions are affine-minus-hinges on finite grids

On a strictly increasing finite grid `v 0 < v 1 < ⋯ < v k`, every concave `f : ℝ → ℝ` agrees at the
grid points with a function of the form `x ↦ A + B * x - ∑ j, c j * max (v j - x) 0` where all
hinge weights `c j` are nonnegative. The hinges are the *lower* hinges `x ↦ max (v j - x) 0`
(kinked at the grid points), so the representation exhibits the concave function — on the grid — as
an affine part plus a nonnegative combination of concave kinks.

This is the discrete dual-cone fact behind the Rothschild-Stiglitz characterization of
mean-preserving spreads: Testing an expectation inequality against all concave functions reduces,
on a finite outcome set, to testing it against affine functions (determined by equal means and
equal masses) and lower hinges (the integrated-CDF condition).

## Main statements

* `ConcaveOn.exists_affine_hinge_interpolation` — the grid representation described above.

## Tags

concave, hinge, interpolation, piecewise linear, majorization, mean-preserving spread
-/

@[expose] public section

open Finset

/-- The chord slopes of a concave function along a strictly increasing ℕ-indexed grid are antitone:
`sN (i + 1) ≤ sN i`. The grid is accessed through `vAt`, which is assumed strictly monotone on
`{0, …, k' + 1}`, and the slope function `sN` is the chord slope below `k'` and constant (equal to
the last slope `B`) above. -/
private lemma sN_antitone_of_concave {k' : ℕ} (vAt : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ k' + 1 → j ≤ k' + 1 → i < j → vAt i < vAt j)
    {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) (hmemAt : ∀ i, vAt i ∈ s)
    (B : ℝ) (hB : B = (f (vAt (k' + 1)) - f (vAt k')) / (vAt (k' + 1) - vAt k'))
    (sN : ℕ → ℝ)
    (hsN : ∀ i, sN i =
      if i < k' + 1 then (f (vAt (i + 1)) - f (vAt i)) / (vAt (i + 1) - vAt i) else B) :
    ∀ i, sN (i + 1) ≤ sN i := by
  intro i
  rcases lt_trichotomy i k' with hi | hi | hi
  · -- Adjacent chord slopes: decreasing by `slope_anti_adjacent`.
    have hlt₁ : vAt i < vAt (i + 1) := hmono i (i + 1) (by omega) (by omega) (by omega)
    have hlt₂ : vAt (i + 1) < vAt (i + 2) := hmono (i + 1) (i + 2) (by omega) (by omega) (by omega)
    have hslope := hf.slope_anti_adjacent (hmemAt i) (hmemAt (i + 2)) hlt₁ hlt₂
    rw [hsN i, hsN (i + 1), if_pos (by omega : i < k' + 1),
      if_pos (by omega : i + 1 < k' + 1)]
    exact hslope
  · -- `i = k'`: the last chord slope equals `B`.
    subst hi
    rw [hsN i, hsN (i + 1), if_neg (by omega : ¬ i + 1 < i + 1), if_pos (by omega : i < i + 1), hB]
  · -- Above the grid: both slopes are the constant `B`.
    rw [hsN i, hsN (i + 1), if_neg (by omega : ¬ i + 1 < k' + 1),
      if_neg (by omega : ¬ i < k' + 1)]

/-- **Concave grid interpolation by affine-minus-hinges.** On a strictly increasing grid
`v : Fin (k + 1) → ℝ`, a concave `f : ℝ → ℝ` agrees at every grid point with
`x ↦ A + B * x - ∑ j, c j * max (v j - x) 0` for some `A B : ℝ` and nonnegative hinge weights
`c : Fin (k + 1) → ℝ`.

Explicitly, with chord slopes `s j = (f (v (j+1)) - f (v j)) / (v (j+1) - v j)` (`j < k`): Take
`B = s (k - 1)` (the last slope), `c j = s (j - 1) - s j` for `0 < j < k` (nonnegative since
concave chord slopes are antitone) with `c 0 = c k = 0`, and `A = f (v k) - B * v k` fixes the
value at the top grid point. -/
theorem ConcaveOn.exists_affine_hinge_interpolation {k : ℕ} {v : Fin (k + 1) → ℝ}
    (hv : StrictMono v) {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    (hmem : ∀ m, v m ∈ s) :
    ∃ (A B : ℝ) (c : Fin (k + 1) → ℝ), (∀ j, 0 ≤ c j) ∧
      ∀ m, f (v m) = A + B * v m - ∑ j, c j * max (v j - v m) 0 := by
  -- Two cases: a single grid point (`k = 0`) is constant; `k ≥ 1` uses chord slopes.
  match k, v, hv with
  | 0, v, _ =>
    -- One grid point: the representation is the constant `f (v 0)`.
    refine ⟨f (v 0), 0, 0, fun _ => le_refl 0, fun m => ?_⟩
    have hm : m = 0 := by ext; omega
    subst hm
    simp
  | (k' + 1), v, hv =>
    -- `vAt` is the grid clamped to a total ℕ-indexed map; `sN` the chord slopes (constant `B`
    -- above the top segment); `c j = sN (j-1) - sN j` (ℕ subtraction makes `c 0 = c last = 0`).
    set vAt : ℕ → ℝ := fun i => v ⟨min i (k' + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩ with hvAt
    have hvAt_eq : ∀ i : Fin (k' + 1 + 1), vAt i.val = v i := by
      intro i
      simp only [hvAt, min_eq_left (Nat.lt_succ_iff.mp i.isLt)]
    have hvAt_mono : ∀ i j, i ≤ k' + 1 → j ≤ k' + 1 → i < j → vAt i < vAt j := by
      intro i j hi hj hij
      have hfin : (⟨min i (k' + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (k' + 1 + 1)) <
          ⟨min j (k' + 1), Nat.lt_succ_of_le (min_le_right _ _)⟩ := by
        simp only [Fin.mk_lt_mk, min_eq_left hi, min_eq_left hj]; exact hij
      exact hv hfin
    set B : ℝ := (f (vAt (k' + 1)) - f (vAt k')) / (vAt (k' + 1) - vAt k') with hB
    set sN : ℕ → ℝ := fun i =>
      if i < k' + 1 then (f (vAt (i + 1)) - f (vAt i)) / (vAt (i + 1) - vAt i) else B with hsN_def
    have hsN : ∀ i, sN i =
        if i < k' + 1 then (f (vAt (i + 1)) - f (vAt i)) / (vAt (i + 1) - vAt i) else B :=
      fun i => rfl
    set c : Fin (k' + 1 + 1) → ℝ := fun j => sN (j.val - 1) - sN j.val with hc
    have hmemAt : ∀ i, vAt i ∈ s := fun i => hmem _
    -- chord slopes decrease (concavity), so the `c j` are nonnegative.
    have hanti := sN_antitone_of_concave vAt hvAt_mono hf hmemAt B hB sN hsN
    refine ⟨f (vAt (k' + 1)) - B * vAt (k' + 1), B, c, ?_, ?_⟩
    · -- Nonnegativity of `c`: at `0` it is `sN 0 - sN 0 = 0`, elsewhere `sN (m-1) - sN m ≥ 0`.
      intro j
      simp only [hc]
      rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
      · rw [hj0]; simp
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
        rw [hm, Nat.succ_sub_one]
        exact sub_nonneg.mpr (hanti m)
    · -- The grid identity at every point, by downward (reverse) induction.
      -- Work with `vAt` everywhere, then transport back to `v` via `hvAt_eq`.
      -- Telescoping of the upper tail of `c`: `∑_{j > m} c j = sN m - B`.
      have htail : ∀ m : ℕ, m ≤ k' + 1 →
          ∑ p ∈ Finset.Ico (m + 1) (k' + 1 + 1), (sN (p - 1) - sN p) = sN m - B := by
        intro m hm
        -- Reindex `p = m + 1 + r`, then telescope `∑ (sN (m + r) - sN (m + r + 1))`.
        rw [Finset.sum_Ico_eq_sum_range]
        have hreindex : ∀ r ∈ Finset.range (k' + 1 + 1 - (m + 1)),
            sN (m + 1 + r - 1) - sN (m + 1 + r) =
              (fun r => sN (m + r)) r - (fun r => sN (m + r)) (r + 1) := by
          intro r _
          simp only []
          congr 2 <;> omega
        rw [Finset.sum_congr rfl hreindex, Finset.sum_range_sub' (fun r => sN (m + r))]
        rw [Nat.add_zero, show m + (k' + 1 + 1 - (m + 1)) = k' + 1 by omega]
        -- `sN (k' + 1) = B` since the top index falls in the constant branch.
        rw [hsN (k' + 1), if_neg (by omega : ¬ k' + 1 < k' + 1)]
      have key : ∀ m : Fin (k' + 1 + 1),
          f (vAt m.val) = f (vAt (k' + 1)) - B * vAt (k' + 1) + B * vAt m.val -
            ∑ j, c j * max (vAt j.val - vAt m.val) 0 := by
        refine Fin.reverseInduction ?_ ?_
        · -- Top grid point: all hinges vanish since `vAt j ≤ vAt (k' + 1)`.
          have hsum_zero : ∑ j, c j * max (vAt j.val - vAt (Fin.last (k' + 1)).val) 0 = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            have hle : vAt j.val ≤ vAt (k' + 1) := by
              rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp j.isLt) with hlt | heq
              · exact le_of_lt (hvAt_mono j.val (k' + 1) (by omega) (by omega) hlt)
              · rw [heq]
            simp only [Fin.val_last]
            rw [max_eq_right (by linarith), mul_zero]
          rw [hsum_zero, Fin.val_last]
          ring
        · -- Step down: relate consecutive grid points through one chord slope.
          intro i hi
          simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢
          set n := i.val with hn
          have hn_lt : n < k' + 1 := i.isLt
          have hvlt : vAt n < vAt (n + 1) :=
            hvAt_mono n (n + 1) (by omega) (by omega) (by omega)
          have hne : vAt (n + 1) - vAt n ≠ 0 := by linarith
          -- Per-grid-point hinge difference: nonzero (equal to one segment length) only above `n`.
          have hdiff : ∀ j : Fin (k' + 1 + 1),
              max (vAt j.val - vAt n) 0 - max (vAt j.val - vAt (n + 1)) 0 =
                if n + 1 ≤ j.val then vAt (n + 1) - vAt n else 0 := by
            intro j
            rcases Nat.lt_or_ge j.val (n + 1) with hlt | hge
            · -- At or below the cutoff: both hinges vanish.
              have h2 : vAt j.val ≤ vAt n := by
                rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
                · exact le_of_lt (hvAt_mono j.val n (by omega) (by omega) h)
                · rw [h]
              rw [if_neg (by omega), max_eq_right (by linarith), max_eq_right (by linarith)]; ring
            · -- Above the cutoff: both hinges are active.
              have h1 : vAt (n + 1) ≤ vAt j.val := by
                rcases lt_or_eq_of_le hge with h | h
                · exact le_of_lt (hvAt_mono (n + 1) j.val (by omega) (by omega) h)
                · rw [h]
              rw [if_pos hge, max_eq_left (by linarith), max_eq_left (by linarith)]; ring
          -- The hinge-sum difference contributes only above `n`, telescoping to `sN n - B`.
          have hrel : (∑ j, c j * max (vAt j.val - vAt n) 0) -
              (∑ j, c j * max (vAt j.val - vAt (n + 1)) 0) =
                (vAt (n + 1) - vAt n) * (sN n - B) := by
            rw [← Finset.sum_sub_distrib]
            have hterm : ∀ j ∈ Finset.univ,
                c j * max (vAt j.val - vAt n) 0 - c j * max (vAt j.val - vAt (n + 1)) 0 =
                  (vAt (n + 1) - vAt n) * (if n + 1 ≤ j.val then c j else 0) := by
              intro j _
              rw [← mul_sub, hdiff j]
              by_cases h : n + 1 ≤ j.val
              · rw [if_pos h, if_pos h, mul_comm]
              · rw [if_neg h, if_neg h, mul_zero, mul_zero]
            rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
            congr 1
            -- The tail sum of `c` telescopes via `htail`.
            rw [hc]
            rw [Fin.sum_univ_eq_sum_range (fun p => if n + 1 ≤ p then sN (p - 1) - sN p else 0)]
            rw [← Finset.sum_filter (n + 1 ≤ ·) (fun p => sN (p - 1) - sN p)]
            have hfilter : Finset.filter (fun p => n + 1 ≤ p) (Finset.range (k' + 1 + 1)) =
                Finset.Ico (n + 1) (k' + 1 + 1) := by
              ext p
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
              omega
            rw [hfilter, htail n (by omega)]
          -- Chord-slope cancellation at the chord slope `sN n`.
          have hslope : (vAt n - vAt (n + 1)) * sN n = f (vAt n) - f (vAt (n + 1)) := by
            rw [hsN n, if_pos hn_lt]
            field_simp
            ring
          linarith [hi, hrel, hslope]
      intro m
      have hm := key m
      simp only [hvAt_eq] at hm
      exact hm
