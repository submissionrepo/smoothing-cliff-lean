/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Geometry.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Cobb–Douglas utility

This file defines **Cobb–Douglas** utility `∏ i, (x i) ^ αᵢ` (Cobb and Douglas 1928) on finite
product domains, both the interior-only form `u` (defined for strictly positive bundles) and the
total form `uTotal` on all of `Fin n → ℝ` obtained by truncating each coordinate at `0`. It also
provides the standard log-form and homogeneity lemmas, and the preference-level regularity facts
(strict monotonicity toward interior bundles, boundary avoidance, quasiconcavity) needed for
general-equilibrium applications.

## Main definitions

* `CobbDouglasUtility` — a Cobb–Douglas utility, carrying strictly positive exponents `α`.
* `CobbDouglasUtility.u` — the interior-only utility `∏ i, (x i) ^ αᵢ`.
* `CobbDouglasUtility.uTotal` — the total utility `∏ i, (max (x i) 0) ^ αᵢ` on `Fin n → ℝ`.
* `NormalizedCobbDouglasUtility` — a Cobb–Douglas utility whose exponents sum to `1`.

## Main statements

* `CobbDouglasUtility.log_u_eq_sum_mul_log` — `log (u x) = ∑ i, αᵢ · log (x i)` on the interior.
* `CobbDouglasUtility.u_homogeneous` — `u` is homogeneous of degree `∑ i, αᵢ`.
* `CobbDouglasUtility.uTotal_strictMonoToInterior`, `CobbDouglasUtility.uTotal_boundaryAvoiding`,
  `CobbDouglasUtility.uTotal_quasiconcave` — preference-level regularity of `uTotal`.

## References

* Cobb, Charles W., and Paul H. Douglas. 1928. “A Theory of Production.” *American Economic Review*
  18 (1): 139–65.

## Tags

utility, cobb-douglas, quasiconcave, homogeneous
-/

@[expose] public section

open Finset

namespace Econlib.Preferences

/-- **Cobb–Douglas** utility over `n` goods. The utility function is `u(x₁, …, xₙ) = ∏ᵢ xᵢ^(αᵢ)`
where `αᵢ > 0` for all `i`. -/
structure CobbDouglasUtility (n : ℕ) where
  /-- The exponents, or preference weights, for each good. -/
  α : Fin n → ℝ
  /-- Each exponent is strictly positive. -/
  α_pos : ∀ i, 0 < α i

namespace CobbDouglasUtility

/-- The utility function, defined for strictly positive consumption bundles. -/
noncomputable def u {n : ℕ} (cd : CobbDouglasUtility n) (x : Fin n → ℝ)
    (_hx : ∀ i, 0 < x i) : ℝ :=
  ∏ i : Fin n, (x i) ^ (cd.α i)

variable {n : ℕ} (cd : CobbDouglasUtility n)

@[simp] lemma u_def (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    cd.u x hx = ∏ i : Fin n, (x i) ^ (cd.α i) := rfl

theorem log_u_eq_sum_mul_log (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    Real.log (cd.u x hx) = ∑ i, cd.α i * Real.log (x i) := by
  dsimp [u]
  rw [Real.log_prod]
  · apply sum_congr rfl
    intro i _
    exact Real.log_rpow (hx i) (cd.α i)
  · intro i _
    exact (Real.rpow_pos_of_pos (hx i) _).ne'

theorem u_homogeneous (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (t : ℝ)
    (ht : 0 < t) :
    cd.u (fun i => t * x i) (fun i => mul_pos ht (hx i)) =
      t ^ (∑ i, cd.α i) * cd.u x hx := by
  dsimp [u]
  have h1 : ∀ i ∈ Finset.univ, (t * x i) ^ cd.α i = t ^ cd.α i * (x i) ^ cd.α i := by
    intro i _
    exact Real.mul_rpow ht.le (le_of_lt (hx i))
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  congr 1
  exact (Real.rpow_sum_of_pos ht cd.α Finset.univ).symm

/-! ### Total Cobb–Douglas utility

The interior-only `u` is extended to a function on all of `Fin n → ℝ` by truncating each
coordinate at `0`. On the strictly positive orthant it agrees with `u`; on the boundary (any
coordinate `≤ 0`) it is `0`. This total form supplies a `PreferenceRel` over the whole commodity
space (`preferenceOfRealUtility uTotal`) together with quasiconcavity, strict monotonicity toward
the interior, and boundary avoidance. -/

/-- **Total Cobb–Douglas utility** `∏ i, (max (x i) 0) ^ αᵢ`, defined on all of `Fin n → ℝ`. -/
noncomputable def uTotal (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, (max (x i) 0) ^ (cd.α i)

@[simp] lemma uTotal_def (x : Fin n → ℝ) :
    cd.uTotal x = ∏ i : Fin n, (max (x i) 0) ^ (cd.α i) := rfl

lemma uTotal_nonneg (x : Fin n → ℝ) : 0 ≤ cd.uTotal x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (le_max_right _ _) _

/-- On the boundary — any coordinate `≤ 0` — the total utility vanishes. -/
lemma uTotal_eq_zero_of_nonpos {x : Fin n → ℝ} {i : Fin n} (hi : x i ≤ 0) :
    cd.uTotal x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) <| by
    rw [max_eq_right hi, Real.zero_rpow (cd.α_pos i).ne']

/-- On the strictly-positive orthant the total utility is the ordinary Cobb–Douglas product. -/
lemma uTotal_eq_prod_of_pos {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    cd.uTotal x = ∏ i : Fin n, (x i) ^ (cd.α i) :=
  Finset.prod_congr rfl fun i _ => by rw [max_eq_left (hx i).le]

lemma uTotal_eq_u_of_pos {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    cd.uTotal x = cd.u x hx :=
  cd.uTotal_eq_prod_of_pos hx

/-- The total utility is strictly positive exactly on the interior of the orthant. -/
lemma uTotal_pos_iff {x : Fin n → ℝ} : 0 < cd.uTotal x ↔ ∀ i, 0 < x i := by
  constructor
  · intro h i
    by_contra hi
    rw [not_lt] at hi
    rw [cd.uTotal_eq_zero_of_nonpos hi] at h
    exact lt_irrefl 0 h
  · intro hx
    exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (by rw [max_eq_left (hx i).le]; exact hx i) _

lemma uTotal_continuous : Continuous cd.uTotal :=
  continuous_finset_prod _ fun i _ =>
    ((continuous_apply i).max continuous_const).rpow_const fun _ => Or.inr (cd.α_pos i).le

/-- **Strict monotonicity toward interior bundles.** A coordinatewise-larger, strictly positive
bundle has strictly larger total Cobb–Douglas utility. -/
theorem uTotal_strictMonoToInterior :
    StrictMonoToInterior (preferenceOfRealUtility cd.uTotal) where
  strictMono {x y} hxy hne hypos := by
    have hyu : 0 < cd.uTotal y := cd.uTotal_pos_iff.mpr hypos
    have key : cd.uTotal x < cd.uTotal y := by
      by_cases hxpos : ∀ i, 0 < x i
      · rw [cd.uTotal_eq_prod_of_pos hxpos, cd.uTotal_eq_prod_of_pos hypos]
        obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
        refine Finset.prod_lt_prod (fun i _ => Real.rpow_pos_of_pos (hxpos i) _)
          (fun i _ => Real.rpow_le_rpow (hxpos i).le (hxy i) (cd.α_pos i).le)
          ⟨k, Finset.mem_univ k, Real.rpow_lt_rpow (hxpos k).le
            (lt_of_le_of_ne (hxy k) hk) (cd.α_pos k)⟩
      · rw [not_forall] at hxpos
        obtain ⟨i, hi⟩ := hxpos
        rw [not_lt] at hi
        rw [cd.uTotal_eq_zero_of_nonpos hi]
        exact hyu
    exact ⟨key.le, not_le.mpr key⟩

/-- **Boundary avoidance.** Any bundle at least as good as a strictly positive bundle is itself
strictly positive. -/
theorem uTotal_boundaryAvoiding :
    BoundaryAvoiding (preferenceOfRealUtility cd.uTotal) where
  pos_of_ge_pos {x z} hz hxz := by
    have hzu : 0 < cd.uTotal z := cd.uTotal_pos_iff.mpr hz
    have hxz' : cd.uTotal z ≤ cd.uTotal x := hxz
    exact cd.uTotal_pos_iff.mp (lt_of_lt_of_le hzu hxz')

/-- The log of the total utility on the interior is the additively-separable log form. -/
lemma log_uTotal_of_pos {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    Real.log (cd.uTotal x) = ∑ i, cd.α i * Real.log (x i) := by
  rw [cd.uTotal_eq_u_of_pos hx, cd.log_u_eq_sum_mul_log]

/-- **Quasiconcavity** of total Cobb–Douglas utility: Every upper contour set is convex. -/
theorem uTotal_quasiconcave : QuasiconcaveOn ℝ Set.univ cd.uTotal :=
  Convex.quasiconcaveOn_of_convex_ge convex_univ fun c => by
    by_cases hc : 0 < c
    · intro x hx y hy a b ha hb hab
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      have hxpos : ∀ i, 0 < x i := cd.uTotal_pos_iff.mp (lt_of_lt_of_le hc hx)
      have hypos : ∀ i, 0 < y i := cd.uTotal_pos_iff.mp (lt_of_lt_of_le hc hy)
      have hwval : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp
      have hwpos : ∀ i, 0 < (a • x + b • y) i := by
        intro i
        rw [hwval i]
        rcases eq_or_lt_of_le ha with ha0 | ha0
        · have hb1 : b = 1 := by linarith
          rw [← ha0, hb1]; simpa using hypos i
        · exact add_pos_of_pos_of_nonneg (mul_pos ha0 (hxpos i)) (mul_nonneg hb (hypos i).le)
      have hwu : 0 < cd.uTotal (a • x + b • y) := cd.uTotal_pos_iff.mpr hwpos
      have key : Real.log c ≤ Real.log (cd.uTotal (a • x + b • y)) := by
        rw [cd.log_uTotal_of_pos hwpos]
        have hsum : a * Real.log (cd.uTotal x) + b * Real.log (cd.uTotal y)
            ≤ ∑ i, cd.α i * Real.log ((a • x + b • y) i) := by
          rw [cd.log_uTotal_of_pos hxpos, cd.log_uTotal_of_pos hypos,
            Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun i _ => ?_
          have hconc : a * Real.log (x i) + b * Real.log (y i)
              ≤ Real.log ((a • x + b • y) i) := by
            have h := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr (hxpos i))
              (Set.mem_Ioi.mpr (hypos i)) ha hb hab
            simpa [hwval i] using h
          nlinarith [mul_le_mul_of_nonneg_left hconc (cd.α_pos i).le]
        have hcx : Real.log c ≤ Real.log (cd.uTotal x) := Real.log_le_log hc hx
        have hcy : Real.log c ≤ Real.log (cd.uTotal y) := Real.log_le_log hc hy
        have e1 : a * Real.log c ≤ a * Real.log (cd.uTotal x) :=
          mul_le_mul_of_nonneg_left hcx ha
        have e2 : b * Real.log c ≤ b * Real.log (cd.uTotal y) :=
          mul_le_mul_of_nonneg_left hcy hb
        have e3 : a * Real.log c + b * Real.log c = Real.log c := by
          rw [← add_mul, hab, one_mul]
        linarith [hsum, e1, e2, e3]
      calc c = Real.exp (Real.log c) := (Real.exp_log hc).symm
        _ ≤ Real.exp (Real.log (cd.uTotal (a • x + b • y))) := Real.exp_le_exp.mpr key
        _ = cd.uTotal (a • x + b • y) := Real.exp_log hwu
    · rw [not_lt] at hc
      have hset : {x : Fin n → ℝ | c ≤ cd.uTotal x} = Set.univ :=
        Set.eq_univ_of_forall fun x => le_trans hc (cd.uTotal_nonneg x)
      rw [hset]; exact convex_univ

end CobbDouglasUtility

/-- A **Cobb–Douglas** utility with exponents summing to one. -/
structure NormalizedCobbDouglasUtility (n : ℕ) extends CobbDouglasUtility n where
  /-- Constant-returns normalization. -/
  α_sum_one : ∑ i : Fin n, α i = 1

end Econlib.Preferences
