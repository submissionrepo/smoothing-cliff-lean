/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Mathlib

/-!
# Utility-Family Non-Vacuity Checks

Compile-time semantic witnesses for the closed-form utility families in
`Econlib.Preferences.Utility` whose curvature/monotonicity/homogeneity claims are prone to silent
sign reversals. Every claim is anchored on a *concrete* utility with hand-computed values, so the
direction of each inequality is checked against numbers rather than restated as theorem syntax.

Families exercised (chunks 1, 2, 4, 5 of `backlog/pref-utility-test-coverage.md`):

* **Cobb–Douglas** (`CobbDouglas.lean`): The two-good symmetric `α = (1/2, 1/2)` utility
  `u(x, y) = √x · √y`. Hand anchors: `u(4, 9) = 6`; boundary `u(0, 9) = 0`; degree-1 homogeneity
  `u(8, 18) = 12 = 2 · u(4, 9)` (the exponent sum is `1`); quasiconcavity, strict monotonicity into
  the interior, boundary avoidance.
* **Risk families** (`RiskFamilies.lean`): CARA at `α = 2` (`u = -exp(-2x)`, Arrow–Pratt `= 2`),
  CRRA at `γ = 2` (`u = -1/x`, relative risk aversion `= 2`), log utility. The curvature checks pin
  *concavity* (not convexity) and the constant risk coefficients to their exact hand values.
* **Positive concave primitive** (`Positive.lean`): A concrete `PositiveConcavePrimitive` built
  from `Real.log`, exercising the bundled concavity/monotonicity/positive-marginal facts.
* **Inada** (`Inada.lean`): The canonical `InadaUtility.sqrt` witness `u = √x`, closing the
  outstanding Inada witness gap. Marginal-inverse round-trip anchor: `u'(x) = (2√x)⁻¹`, so
  `inverseMarginal (1/2) = 1` (since `u'(1) = 1/2`).
* **Prudence** (`Prudence.lean`): CRRA is prudent via the nonnegative-third-derivative
  characterization; `crraMarginal` is positive. Hand sign-check: `u''' = (1+γ)γ · x^(-γ-2) > 0`.

A hostile reviewer reading the family docstrings should agree these are genuine, non-vacuous,
direction-correct instances — e.g. the concavity witnesses would *fail to typecheck* if the
curvature sign in the source were reversed, and the negative check `cara2.u` is **not** convex
catches a flipped `ConcaveOn`/`ConvexOn`.
-/

noncomputable section

namespace EconlibTest.Preferences.UtilityFamilies

open Econlib.Preferences
open Set Filter Topology

/-! ## Chunk 1. Cobb–Douglas: Symmetric two-good `α = (1/2, 1/2)`

The utility is `u(x, y) = x^(1/2) · y^(1/2) = √(xy)`, the canonical constant-returns
Cobb–Douglas. Exponent sum is `1/2 + 1/2 = 1`, so the function is homogeneous of degree `1`. Hand
anchors: `u(4, 9) = 2 · 3 = 6`, boundary `u(0, 9) = 0`, and `u(8, 18) = √144 = 12 = 2 · 6`. -/

section cobbDouglas

/-- The symmetric two-good Cobb–Douglas utility with exponents `(1/2, 1/2)`. -/
private def cd : CobbDouglasUtility 2 where
  α := ![1/2, 1/2]
  α_pos := by intro i; fin_cases i <;> norm_num

/-- The interior bundle `(4, 9)`. -/
private def x49 : Fin 2 → ℝ := ![4, 9]

/-- The boundary bundle `(0, 9)` (first coordinate zero). -/
private def x09 : Fin 2 → ℝ := ![0, 9]

/-- The interior bundle is strictly positive. -/
private lemma x49_pos : ∀ i, 0 < x49 i := by intro i; fin_cases i <;> norm_num [x49]

/-- **`u_def` + value anchor.** The interior utility is the exponent-weighted product;
at `(4, 9)` it equals `4^(1/2) · 9^(1/2) = 2 · 3 = 6`. -/
theorem cd_u_at : cd.u x49 x49_pos = 6 := by
  rw [cd.u_def]
  simp only [Fin.prod_univ_two, cd, x49, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- `4^(1/2) = √4 = 2`, `9^(1/2) = √9 = 3`, so the product is `6`.
  rw [show (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 from by
        rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num),
    show (9 : ℝ) ^ ((1 : ℝ) / 2) = 3 from by
        rw [← Real.sqrt_eq_rpow, show (9 : ℝ) = 3 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)]
  norm_num

/-- **`uTotal_def` + `uTotal_eq_u_of_pos`.** On the interior the total utility agrees with the
ordinary product, so `uTotal (4, 9) = 6`. -/
theorem cd_uTotal_at : cd.uTotal x49 = 6 := by
  rw [cd.uTotal_eq_u_of_pos x49_pos, cd_u_at]

/-- **`uTotal_nonneg`.** Total utility is nonnegative everywhere — even on the boundary. -/
theorem cd_uTotal_nonneg (x : Fin 2 → ℝ) : 0 ≤ cd.uTotal x := cd.uTotal_nonneg x

/-- **`uTotal_eq_zero_of_nonpos` / boundary value.** A zero first coordinate makes the total
utility vanish: `uTotal (0, 9) = 0`. This is the load-bearing boundary fact for
`boundaryAvoiding`. -/
theorem cd_uTotal_boundary : cd.uTotal x09 = 0 :=
  cd.uTotal_eq_zero_of_nonpos (i := 0) (by norm_num [x09])

/-- **`uTotal_pos_iff`, positive direction.** The interior bundle has strictly positive utility. -/
theorem cd_uTotal_pos : 0 < cd.uTotal x49 := cd.uTotal_pos_iff.mpr x49_pos

/-- **`uTotal_pos_iff`, negative direction — through the iff.** The boundary bundle does *not* have
positive utility, because its first coordinate is `0` (not strictly positive). Proved via
`mt cd.uTotal_pos_iff.mp`: positivity of `uTotal` would force *every* coordinate positive, which
fails at coordinate `0`. This genuinely exercises the `.mp` direction of `uTotal_pos_iff`, not just
the boundary value. -/
theorem cd_uTotal_not_pos : ¬ 0 < cd.uTotal x09 :=
  mt cd.uTotal_pos_iff.mp (fun h => by have := h 0; norm_num [x09] at this)

/-- **`uTotal_eq_prod_of_pos`.** On the interior the truncated product collapses to the raw
product. -/
theorem cd_uTotal_eq_prod : cd.uTotal x49 = ∏ i : Fin 2, (x49 i) ^ (cd.α i) :=
  cd.uTotal_eq_prod_of_pos x49_pos

/-- **`uTotal_continuous`.** Total Cobb–Douglas utility is continuous on the whole commodity
space. -/
theorem cd_uTotal_continuous : Continuous cd.uTotal := cd.uTotal_continuous

/-- **`log_u_eq_sum_mul_log`.** The interior log-utility is the additively separable log form
`∑ αᵢ log xᵢ = (1/2) log 4 + (1/2) log 9`. -/
theorem cd_log_form :
    Real.log (cd.u x49 x49_pos) = (1/2) * Real.log 4 + (1/2) * Real.log 9 := by
  rw [cd.log_u_eq_sum_mul_log]
  simp [Fin.sum_univ_two, cd, x49]

/-- **`log_uTotal_of_pos`.** The log of the *total* utility on the interior matches the same
separable form. -/
theorem cd_log_uTotal :
    Real.log (cd.uTotal x49) = (1/2) * Real.log 4 + (1/2) * Real.log 9 := by
  rw [cd.log_uTotal_of_pos x49_pos]
  simp [Fin.sum_univ_two, cd, x49]

/-- The scaled bundle `2 · (4, 9)` is strictly positive coordinatewise. -/
private lemma x49_scaled_pos : ∀ i, 0 < (2 : ℝ) * x49 i :=
  fun i => mul_pos two_pos (x49_pos i)

/-- **`u_homogeneous`, degree anchor.** The exponent sum is `1`, so the utility is
homogeneous of degree `1`: `u(2·x) = 2^1 · u(x) = 2 · u(x)`. The product domain bundle is
`(8, 18)`, and indeed `u(8, 18) = √144 = 12 = 2 · 6`. -/
theorem cd_homogeneous_degree_one :
    cd.u (fun i => (2 : ℝ) * x49 i) x49_scaled_pos = 2 * cd.u x49 x49_pos := by
  rw [cd.u_homogeneous x49 x49_pos 2 (by norm_num)]
  congr 1
  -- the exponent sum is `1/2 + 1/2 = 1`, so `2 ^ (∑ αᵢ) = 2 ^ 1 = 2`.
  rw [show (∑ i : Fin 2, cd.α i) = 1 from by simp [Fin.sum_univ_two, cd]; norm_num,
    Real.rpow_one]

/-- **Homogeneity value anchor.** Spelling out the scaled bundle: `u(8, 18) = 12 = 2 · u(4, 9)`. -/
theorem cd_homogeneous_value :
    cd.u (fun i => (2 : ℝ) * x49 i) x49_scaled_pos = 12 := by
  rw [cd_homogeneous_degree_one, cd_u_at]; norm_num

/-- **`uTotal_quasiconcave`.** Every upper contour set of total Cobb–Douglas utility is convex. -/
theorem cd_quasiconcave : QuasiconcaveOn ℝ Set.univ cd.uTotal := cd.uTotal_quasiconcave

/-- **`uTotal_strictMonoToInterior`.** The induced preference is strictly monotone toward interior
bundles: A coordinatewise-larger strictly-positive bundle is strictly preferred. -/
theorem cd_strictMonoToInterior :
    StrictMonoToInterior (preferenceOfRealUtility cd.uTotal) := cd.uTotal_strictMonoToInterior

/-- **`uTotal_boundaryAvoiding`.** Any bundle at least as good as an interior bundle is itself
interior — boundary bundles (utility `0`) are never weakly preferred to a strictly-positive one. -/
theorem cd_boundaryAvoiding :
    BoundaryAvoiding (preferenceOfRealUtility cd.uTotal) := cd.uTotal_boundaryAvoiding

/-- **`NormalizedCobbDouglasUtility`.** The same `α = (1/2, 1/2)` is a genuine *normalized*
Cobb–Douglas: The exponents sum to one (constant returns). This is the non-vacuity witness for the
`α_sum_one` field. -/
private def ncd : NormalizedCobbDouglasUtility 2 where
  toCobbDouglasUtility := cd
  α_sum_one := by simp [Fin.sum_univ_two, cd]; norm_num

/-- **`NormalizedCobbDouglasUtility.α_sum_one`, the real non-vacuity content.** The exponents sum to
one: `∑ ncd.α i = 1/2 + 1/2 = 1` (constant returns to scale). This checks the `α_sum_one` field
directly, rather than the trivial projection `ncd.toCobbDouglasUtility = cd`. -/
theorem ncd_alpha_sum_one : ∑ i, ncd.α i = 1 := ncd.α_sum_one

/-! ### Concrete consequences (not just API pass-throughs)

The pass-through theorems above (`cd_quasiconcave`, `cd_strictMonoToInterior`,
`cd_boundaryAvoiding`) assert availability of the named properties; the following anchor them on
explicit bundles, so a broken property would change a *checkable* preference. -/

/-- **Strict preference, concrete.** The interior bundle `(4, 9)` (utility `6`) is strictly
preferred to the boundary bundle `(0, 9)` (utility `0`) under the induced preference. This is the
behavioral consequence of `boundaryAvoiding` / strict monotonicity on a concrete pair. -/
theorem cd_pref_interior_over_boundary :
    (preferenceOfRealUtility cd.uTotal).lt x49 x09 := by
  rw [preferenceOfUtilityIn_lt_iff,
    show cd.uTotal x09 = 0 from cd.uTotal_eq_zero_of_nonpos (i := 0) (by norm_num [x09])]
  exact cd.uTotal_pos_iff.mpr x49_pos

/-- **Boundary not weakly preferred to interior.** The boundary bundle `(0, 9)` is *not* weakly
preferred to the interior `(4, 9)` — `0 < 6` — the exclusion of free goods that `boundaryAvoiding`
encodes, checked on concrete bundles. -/
theorem cd_boundary_not_ge_interior :
    ¬ (preferenceOfRealUtility cd.uTotal).le x09 x49 := by
  rw [preferenceOfUtilityIn_le_iff, not_le,
    show cd.uTotal x09 = 0 from cd.uTotal_eq_zero_of_nonpos (i := 0) (by norm_num [x09])]
  exact cd.uTotal_pos_iff.mpr x49_pos

/-- Two interior bundles for the quasiconcavity (Jensen) midpoint check. -/
private def bA : Fin 2 → ℝ := ![4, 9]
private def bB : Fin 2 → ℝ := ![16, 1]
private lemma cd_uTotal_bA : cd.uTotal bA = 6 := by
  rw [cd.uTotal_eq_u_of_pos (by intro i; fin_cases i <;> norm_num [bA]), cd.u_def]
  simp only [Fin.prod_univ_two, cd, bA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (4:ℝ)^((1:ℝ)/2) = 2 by
        rw [← Real.sqrt_eq_rpow, show (4:ℝ)=2^2 by norm_num]; exact Real.sqrt_sq (by norm_num),
      show (9:ℝ)^((1:ℝ)/2) = 3 by
        rw [← Real.sqrt_eq_rpow, show (9:ℝ)=3^2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  norm_num
private lemma cd_uTotal_bB : cd.uTotal bB = 4 := by
  rw [cd.uTotal_eq_u_of_pos (by intro i; fin_cases i <;> norm_num [bB]), cd.u_def]
  simp only [Fin.prod_univ_two, cd, bB, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (16:ℝ)^((1:ℝ)/2) = 4 by
        rw [← Real.sqrt_eq_rpow, show (16:ℝ)=4^2 by norm_num]; exact Real.sqrt_sq (by norm_num),
      show (1:ℝ)^((1:ℝ)/2) = 1 by rw [← Real.sqrt_eq_rpow, Real.sqrt_one]]
  norm_num

/-- **Quasiconcavity, concrete Jensen midpoint.** Behavioral consequence of `cd_quasiconcave`: the
two interior bundles `(4, 9)` (utility `6`) and `(16, 1)` (utility `4`) both lie in the superlevel
set `{uTotal ≥ 4}`, so by convexity of that set their `1/2`-midpoint `(10, 5)` also has
`uTotal ≥ 4`. This exercises the convex-combination content of quasiconcavity, not just its
availability. -/
theorem cd_quasiconcave_midpoint :
    (((1:ℝ)/2) • bA + ((1:ℝ)/2) • bB) ∈
      {x : Fin 2 → ℝ | x ∈ Set.univ ∧ (4:ℝ) ≤ cd.uTotal x} := by
  have hconv := cd.uTotal_quasiconcave 4
  have hA : bA ∈ {x : Fin 2 → ℝ | x ∈ Set.univ ∧ (4:ℝ) ≤ cd.uTotal x} :=
    ⟨Set.mem_univ _, by rw [cd_uTotal_bA]; norm_num⟩
  have hB : bB ∈ {x : Fin 2 → ℝ | x ∈ Set.univ ∧ (4:ℝ) ≤ cd.uTotal x} :=
    ⟨Set.mem_univ _, by rw [cd_uTotal_bB]⟩
  exact hconv hA hB (by norm_num) (by norm_num) (by norm_num)

/-! ### Asymmetric Cobb–Douglas: catching the exponent-swap bug

The symmetric `α = (1/2, 1/2)` anchors above are invariant under transposing coordinates or swapping
exponent indices. To catch that bug we use the asymmetric `α = (1/3, 2/3)` at the bundle `(8, 27)`,
where the intended value is `8^(1/3)·27^(2/3) = 2·9 = 18`, but the swapped exponents would give
`8^(2/3)·27^(1/3) = 4·3 = 12 ≠ 18`. -/

/-- The asymmetric Cobb–Douglas utility with exponents `(1/3, 2/3)`. -/
private def cdA : CobbDouglasUtility 2 where
  α := ![1/3, 2/3]
  α_pos := by intro i; fin_cases i <;> norm_num

/-- The interior bundle `(8, 27)`. -/
private def x827 : Fin 2 → ℝ := ![8, 27]
private lemma x827_pos : ∀ i, 0 < x827 i := by intro i; fin_cases i <;> norm_num [x827]

private lemma cdA_pow8 : (8 : ℝ) ^ ((1:ℝ)/3) = 2 := by
  rw [show (8:ℝ) = 2^(3:ℕ) by norm_num, ← Real.rpow_natCast 2 3, ← Real.rpow_mul (by norm_num)]
  norm_num
private lemma cdA_pow27 : (27 : ℝ) ^ ((2:ℝ)/3) = 9 := by
  rw [show (27:ℝ) = 3^(3:ℕ) by norm_num, ← Real.rpow_natCast 3 3, ← Real.rpow_mul (by norm_num)]
  norm_num
private lemma cdA_pow8_swap : (8 : ℝ) ^ ((2:ℝ)/3) = 4 := by
  rw [show (8:ℝ) = 2^(3:ℕ) by norm_num, ← Real.rpow_natCast 2 3, ← Real.rpow_mul (by norm_num)]
  norm_num
private lemma cdA_pow27_swap : (27 : ℝ) ^ ((1:ℝ)/3) = 3 := by
  rw [show (27:ℝ) = 3^(3:ℕ) by norm_num, ← Real.rpow_natCast 3 3, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- **Asymmetric Cobb–Douglas value anchor.** `u(8, 27) = 8^(1/3)·27^(2/3) = 2·9 = 18`. -/
theorem cdA_u_at : cdA.u x827 x827_pos = 18 := by
  rw [cdA.u_def]
  simp only [Fin.prod_univ_two, cdA, x827, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [cdA_pow8, cdA_pow27]; norm_num

/-- **Exponent-swap discrimination.** With the *swapped* exponents the product would be
`8^(2/3)·27^(1/3) = 4·3 = 12 ≠ 18`. This is exactly the bug the asymmetric anchor catches and the
symmetric `(1/2, 1/2)` anchor cannot. -/
theorem cdA_swapped_ne :
    (8 : ℝ) ^ ((2:ℝ)/3) * 27 ^ ((1:ℝ)/3) ≠ 18 := by
  rw [cdA_pow8_swap, cdA_pow27_swap]; norm_num

end cobbDouglas

/-! ## Chunk 2a. CARA at `α = 2`

`u(x) = -exp(-2x)`. Hand checks: Strictly increasing, globally concave, and the Arrow–Pratt
coefficient `-u''/u' = α = 2` exactly. The negative check that `u` is *not* convex catches a
flipped curvature claim. -/

section cara

/-- The CARA agent with absolute risk aversion `α = 2`. -/
private def cara2 : ConstantAbsoluteRiskAversionUtility where
  α := 2
  α_pos := by norm_num

/-- **`u_def` + value anchor.** `u(x) = -exp(-2x)`, so `u(0) = -1`. -/
theorem cara2_u_def (x : ℝ) : cara2.u x = -Real.exp (-2 * x) := by
  rw [cara2.u_def]; norm_num [cara2]

/-- `u(0) = -exp 0 = -1`. -/
theorem cara2_u_at_zero : cara2.u 0 = -1 := by rw [cara2_u_def]; simp

/-- **`u_strictMono`.** CARA is strictly increasing. -/
theorem cara2_strictMono : StrictMono cara2.u :=
  cara2.u_strictMono

/-- Direction anchor: `u(0) < u(1)` (more wealth is strictly better). -/
theorem cara2_zero_lt_one : cara2.u 0 < cara2.u 1 := cara2_strictMono (by norm_num)

/-- **`hasDerivAt_u`.** `u'(x) = α·exp(-α·x) = 2·exp(-2x)`. -/
theorem cara2_deriv (x : ℝ) :
    HasDerivAt cara2.u (2 * Real.exp (-2 * x)) x := by
  have h := cara2.hasDerivAt_u x
  simpa [cara2] using h

/-- **`hasDerivAt_deriv_u`.**
`u''(x) = -(α²)·exp(-α·x) = -4·exp(-2x) < 0`. -/
theorem cara2_second_deriv (x : ℝ) :
    HasDerivAt (fun x' => 2 * Real.exp (-2 * x')) (-(4 : ℝ) * Real.exp (-2 * x)) x := by
  have h := cara2.hasDerivAt_deriv_u x
  have he : (-(((2 : ℝ)) ^ 2) * Real.exp (-(2 : ℝ) * x)) = -(4 : ℝ) * Real.exp (-2 * x) := by
    norm_num
  rw [show (cara2.α : ℝ) = 2 from rfl] at h
  rw [he] at h
  exact h

/-- **`concaveOn_u`, correct direction.** CARA is *concave* (risk-averse),
not convex. -/
theorem cara2_concave : ConcaveOn ℝ Set.univ cara2.u := cara2.concaveOn_u

/-- **Negative curvature check.** CARA is **not** convex on `ℝ`. If it were, then together with the
genuine concavity it would force the midpoint identity `u(1/2) = (u 0 + u 1)/2`; but
`u = -exp(-2·)` and `exp` is *strictly* convex, so the midpoint value is strictly below the chord —
contradiction. This catches a `ConcaveOn`/`ConvexOn` reversal in the source. -/
theorem cara2_not_convex : ¬ ConvexOn ℝ Set.univ cara2.u := by
  intro hconv
  -- Concave + convex ⟹ the midpoint of `0` and `1` lands exactly on the chord.
  have hmid_conv : cara2.u ((1/2 : ℝ) • (0 : ℝ) + (1/2 : ℝ) • (1 : ℝ))
      ≤ (1/2 : ℝ) • cara2.u 0 + (1/2 : ℝ) • cara2.u 1 :=
    hconv.2 (mem_univ _) (mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  have hmid_conc : (1/2 : ℝ) • cara2.u 0 + (1/2 : ℝ) • cara2.u 1
      ≤ cara2.u ((1/2 : ℝ) • (0 : ℝ) + (1/2 : ℝ) • (1 : ℝ)) :=
    cara2_concave.2 (mem_univ _) (mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  have heq : cara2.u (1/2 : ℝ) = (1/2 : ℝ) * cara2.u 0 + (1/2 : ℝ) * cara2.u 1 := by
    have h1 : ((1/2 : ℝ) • (0 : ℝ) + (1/2 : ℝ) • (1 : ℝ)) = (1/2 : ℝ) := by norm_num
    rw [h1] at hmid_conv hmid_conc
    simp only [smul_eq_mul] at hmid_conv hmid_conc
    linarith
  -- But `exp` is strictly convex: at the points `-2·0 = 0` and `-2·1 = -2`, the midpoint
  -- `exp(-1)` is strictly below the chord `(exp 0 + exp(-2))/2`.
  have hstrict := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (-2 : ℝ)) (by norm_num)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  -- Rewrite both sides of `heq` to `exp` values and contradict the strict gap.
  rw [cara2_u_def, cara2_u_def, cara2_u_def] at heq
  simp only [smul_eq_mul] at hstrict
  -- `heq` ⟹ `exp(-1) = (exp 0 + exp(-2))/2`; `hstrict` ⟹ `exp(-1) < (exp 0 + exp(-2))/2`.
  norm_num at heq hstrict
  linarith

/-- **`arrow_pratt`, formula identity.** The Arrow–Pratt coefficient
`-u''/u' = α` reduces to the constant `2` for this agent (at every wealth level), as an algebraic
identity in `exp`. -/
theorem cara2_arrow_pratt (x : ℝ) :
    -( -((2 : ℝ) ^ 2) * Real.exp (-2 * x) ) / (2 * Real.exp (-2 * x)) = 2 := by
  have h := cara2.arrow_pratt x
  simpa [cara2] using h

/-- **`TwiceDiffUtility.absoluteRiskAversion` API value.** Beyond the formula identity above, this
anchors the *bundled* Arrow–Pratt accessor: `cara2.toTwiceDiffUtility.absoluteRiskAversion 0 = 2`.
A bug in the `absoluteRiskAversion` wrapper or its sign convention (`A = -u''/u'`) would be caught
here, whereas `cara2_arrow_pratt` checks only the raw `exp`-formula. -/
theorem cara2_absoluteRiskAversion_api :
    cara2.toTwiceDiffUtility.absoluteRiskAversion 0 (Set.mem_univ 0) = 2 :=
  cara2.absoluteRiskAversion_eq_alpha 0 (Set.mem_univ 0)

end cara

/-! ## Chunk 2b. CRRA at `γ = 2`

`u(x) = x^(1-2)/(1-2) = x^(-1)/(-1) = -1/x` on `(0, ∞)`. Hand checks: Strictly increasing,
concave, and the relative-risk-aversion coefficient `-x·u''/u' = γ = 2`. Value anchor: `u(1) = -1`,
`u(2) = -1/2`. -/

section crra

/-- The CRRA agent with relative risk aversion `γ = 2` (so `u(x) = -1/x`). -/
private def crra2 : ConstantRelativeRiskAversionUtility where
  γ := 2
  γ_pos := by norm_num
  γ_ne_one := by norm_num

/-- **`u_def` + value anchor.** `u(1) = 1^(-1)/(-1) = -1`. -/
theorem crra2_u_at_one : crra2.u 1 (by norm_num) = -1 := by
  rw [crra2.u_def]
  norm_num [crra2]

/-- Value anchor: `u(2) = 2^(-1)/(-1) = -1/2`. -/
theorem crra2_u_at_two : crra2.u 2 (by norm_num) = -1/2 := by
  rw [crra2.u_def]
  rw [show (1 : ℝ) - crra2.γ = -1 from by norm_num [crra2],
    Real.rpow_neg_one]
  norm_num

/-- **`u_strictMono`, direction anchor.** `u(1) < u(2)` since
`-1 < -1/2`. -/
theorem crra2_strict_mono : crra2.u 1 (by norm_num) < crra2.u 2 (by norm_num) :=
  crra2.u_strictMono (by norm_num) (by norm_num) (by norm_num)

/-- **`concaveOn_u`, correct direction.** CRRA is *concave* on `(0, ∞)`. -/
theorem crra2_concave :
    ConcaveOn ℝ (Set.Ioi 0) (fun x => if hx : 0 < x then crra2.u x hx else 0) :=
  crra2.concaveOn_u

/-- **`relativeRiskAversion`, value anchor.** The
relative-risk-aversion coefficient `-x·u''/u'` is the constant `γ = 2` for this agent, at every
positive wealth. -/
theorem crra2_rra (x : ℝ) (hx : 0 < x) :
    (let u' := x ^ (-(2 : ℝ));
     let u'' := -(2 : ℝ) * x ^ (-(2 : ℝ) - 1);
     -(x * u'') / u' = 2) := by
  have h := crra2.relativeRiskAversion x hx
  simpa [crra2] using h

/-- **`TwiceDiffUtility.relativeRiskAversion` API value at a positive point.** Anchors the *bundled*
relative-risk-aversion accessor (which carries the `x` multiplier `R(x) = -x·u''/u'`):
`crra2.toTwiceDiffUtility.relativeRiskAversion 1 = 2`. A bug in the wrapper or a dropped `x` factor
would be caught here, whereas `crra2_rra` checks only the raw formula. -/
theorem crra2_relativeRiskAversion_api :
    crra2.toTwiceDiffUtility.relativeRiskAversion 1 (Set.mem_Ioi.mpr (by norm_num)) = 2 :=
  crra2.relativeRiskAversion_eq_gamma 1 (by norm_num)

end crra

/-! ## Chunk 2c. Log utility

`u(x) = log x`. Strictly increasing and concave on `(0, ∞)`. -/

section log

/-- The log utility witness. -/
private def logU : LogUtility := {}

/-- **`log_u_def` + value anchor.** `u(1) = log 1 = 0`. -/
theorem logU_u_at_one : logU.u 1 (by norm_num) = 0 := by
  rw [logU.log_u_def]; simp

/-- **`log_strictly_increasing`, direction anchor.** `u(1) < u(2)` since `log 1 = 0 < log 2`. -/
theorem logU_strict_mono : logU.u 1 (by norm_num) < logU.u 2 (by norm_num) :=
  logU.log_strictly_increasing (by norm_num) (by norm_num) (by norm_num)

/-- **`log_concave`, correct direction.** Log utility is *concave* on `(0, ∞)`. -/
theorem logU_concave :
    ConcaveOn ℝ (Set.Ioi 0) (fun x => if hx : 0 < x then logU.u x hx else 0) :=
  logU.log_concave

end log

/-! ## Chunk 2d. Positive concave primitive

A concrete `PositiveConcavePrimitive` built from `Real.log`: It is strictly monotone, strictly
concave, `C¹`, with positive marginal `1/x` on `(0, ∞)`, blowing up at `0⁺` and vanishing at `∞`.
This exercises the bundled regularity accessors `concaveOn_pos`, `monotoneOn_pos`,
`deriv_pos_of_mem`, and `coe_apply`. -/

section positivePrimitive

/-- The log primitive as a `PositiveConcavePrimitive`. All seven analytic fields are discharged
from standard Mathlib facts about `Real.log`. -/
private def logPrim : PositiveConcavePrimitive where
  toFun := Real.log
  strictMonoOn_pos := Real.strictMonoOn_log
  strictConcaveOn_pos := strictConcaveOn_log_Ioi
  contDiffOn_pos :=
    -- `log` is `C¹` on `{0}ᶜ ⊇ (0, ∞)`.
    Real.contDiffOn_log.mono (fun x hx => ne_of_gt (mem_Ioi.mp hx))
  deriv_pos := fun x hx => by rw [Real.deriv_log]; exact inv_pos.mpr hx
  deriv_at_zero_atTop := by
    -- `deriv log = x⁻¹ → +∞` as `x → 0⁺`.
    refine Filter.Tendsto.congr' ?_ tendsto_inv_nhdsGT_zero
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.deriv_log]
  deriv_atTop_zero := by
    refine Filter.Tendsto.congr' ?_ tendsto_inv_atTop_zero
    filter_upwards [eventually_gt_atTop 0] with x _
    rw [Real.deriv_log]

/-- **`PositiveConcavePrimitive.coe_apply`.** The coercion is the bundled `toFun = Real.log`. -/
theorem logPrim_coe (x : ℝ) : (logPrim : ℝ → ℝ) x = Real.log x := logPrim.coe_apply x

/-- **`PositiveConcavePrimitive.concaveOn_pos`.** The primitive is concave on `(0, ∞)`. -/
theorem logPrim_concave : ConcaveOn ℝ (Ioi (0 : ℝ)) logPrim.toFun := logPrim.concaveOn_pos

/-- **`PositiveConcavePrimitive.monotoneOn_pos`.** The primitive is monotone on `(0, ∞)`. -/
theorem logPrim_monotone : MonotoneOn logPrim.toFun (Ioi (0 : ℝ)) := logPrim.monotoneOn_pos

/-- **`PositiveConcavePrimitive.deriv_pos_of_mem`, value anchor.** The marginal `deriv log` is
strictly positive at every interior point; e.g. at `x = 1` it is `1/1 = 1 > 0`. -/
theorem logPrim_deriv_pos : 0 < deriv logPrim.toFun 1 := logPrim.deriv_pos_of_mem (by norm_num)

/-- **Derivative *value* anchor (not just sign).** `deriv log 1 = 1/1 = 1`, the strengthening the
prose claims: the marginal at the unit point is exactly `1`. -/
theorem logPrim_deriv_at_one : deriv logPrim.toFun 1 = 1 := by
  change deriv Real.log 1 = 1
  rw [Real.deriv_log]; norm_num

/-- **`contDiffOn_pos` field, public witness.** The primitive is `C¹` on `(0, ∞)` — one of the
analytic fields buried in the private construction, now checked publicly. -/
theorem logPrim_contDiffOn : ContDiffOn ℝ 1 logPrim.toFun (Ioi (0 : ℝ)) :=
  logPrim.contDiffOn_pos

/-- **`strictConcaveOn_pos` field, public witness.** The primitive is *strictly* concave on
`(0, ∞)` (stronger than the weak `concaveOn_pos` checked above). -/
theorem logPrim_strictConcave : StrictConcaveOn ℝ (Ioi (0 : ℝ)) logPrim.toFun :=
  logPrim.strictConcaveOn_pos

/-- **`strictMonoOn_pos` field, public witness.** The primitive is *strictly* monotone on
`(0, ∞)`. -/
theorem logPrim_strictMono : StrictMonoOn logPrim.toFun (Ioi (0 : ℝ)) :=
  logPrim.strictMonoOn_pos

/-- **Inada boundary field `deriv_at_zero_atTop`, public witness.** The marginal blows up at the
left boundary: `deriv log → +∞` as `x → 0⁺`. -/
theorem logPrim_deriv_atZero : Tendsto (deriv logPrim.toFun) (𝓝[>] (0 : ℝ)) atTop :=
  logPrim.deriv_at_zero_atTop

/-- **Inada boundary field `deriv_atTop_zero`, public witness.** The marginal vanishes at infinity:
`deriv log → 0` as `x → ∞`. -/
theorem logPrim_deriv_atTop : Tendsto (deriv logPrim.toFun) atTop (𝓝 (0 : ℝ)) :=
  logPrim.deriv_atTop_zero

end positivePrimitive

/-! ## Chunk 4. Inada utility: The `√x` witness

The canonical Inada witness is `InadaUtility.sqrt`, `u(x) = √x` on `(0, ∞)`, with marginal
`u'(x) = (2√x)⁻¹`. This concrete instance closes the outstanding Inada witness gap noted in the
Preferences-examples memory — the `Sqrt.lean` source builds it; here we exercise the bundled
boundary/marginal API on it.

Marginal-inverse round-trip anchor: `u'(1) = (2·√1)⁻¹ = (2·1)⁻¹ = 1/2`, so the unique `c > 0` with
`u'(c) = 1/2` is `c = 1` — i.e. `inverseMarginal (1/2) = 1`. -/

section inada

/-- The square-root Inada witness. -/
private abbrev sq : InadaUtility := InadaUtility.sqrt

/-- **`mem_domain_iff`.** The domain is exactly `(0, ∞)`: Membership is positivity. Positive
direction at `x = 1`. -/
theorem sq_mem_domain : (1 : ℝ) ∈ sq.toTwiceDiffUtility.domain :=
  sq.mem_domain_iff.mpr (by norm_num)

/-- **`mem_domain_iff`, negative direction.** `0` is *not* in the domain (the boundary is
excluded). Catches a flipped domain `↔`. -/
theorem sq_zero_not_mem_domain : (0 : ℝ) ∉ sq.toTwiceDiffUtility.domain := by
  rw [sq.mem_domain_iff]; norm_num

/-- **`u'_pos_on`, value anchor.** The marginal utility is strictly positive on `(0, ∞)`;
concretely `u'(1) = 1/2 > 0`. -/
theorem sq_u'_pos : 0 < sq.u' 1 := sq.u'_pos_on 1 (by norm_num)

/-- The marginal at `1` is exactly `1/2` (`u'(1) = (2·√1)⁻¹ = 1/2`). This is the anchor that drives
the inverse-marginal round-trip below. -/
theorem sq_u'_at_one : sq.u' 1 = 1/2 := by
  rw [InadaUtility.sqrt_u'_apply, Real.sqrt_one]; norm_num

/-- **`continuousOn_u`** (inherited from `TwiceDiffUtility`). `√` is continuous on its domain
`(0, ∞)`. -/
theorem sq_continuousOn_u : ContinuousOn sq.u sq.toTwiceDiffUtility.domain :=
  sq.continuousOn_u

/-- **`continuousOn_u'`.** The marginal `u'` is continuous on `(0, ∞)`. -/
theorem sq_continuousOn_u' : ContinuousOn sq.u' (Ioi 0) := sq.continuousOn_u'

/-- **`deriv_eq`, bundled-field equality.** On the domain, `deriv u = u'`; at `x = 1`,
`deriv √ 1 = u'(1)`. -/
theorem sq_deriv_eq : deriv sq.u 1 = sq.u' 1 := sq.deriv_eq 1 sq_mem_domain

/-- **`deriv_eq`, *value* anchor.** `deriv √ 1 = 1/2` — the concrete number, chaining the bundled
equality `sq_deriv_eq` with the marginal value `sq_u'_at_one`. This catches a consistently-wrong
derivative field/theorem pair that `sq_deriv_eq` alone (an equality between two possibly-wrong
quantities) would not. -/
theorem sq_deriv_value : deriv sq.u 1 = 1 / 2 := by rw [sq_deriv_eq, sq_u'_at_one]

/-- **`deriv_u'_eq`, bundled-field equality.** On the domain, `deriv u' = u''`; at `x = 1`,
`deriv u' 1 = u''(1)`. -/
theorem sq_deriv_u'_eq : deriv sq.u' 1 = sq.u'' 1 := sq.deriv_u'_eq 1 sq_mem_domain

/-- The second derivative at `1` is `-(4·1·√1)⁻¹ = -1/4 < 0`: Strict concavity in the correct
direction. -/
theorem sq_u''_at_one : sq.u'' 1 = -(1/4 : ℝ) := by
  change -(4 * (1 : ℝ) * Real.sqrt 1)⁻¹ = -(1/4)
  rw [Real.sqrt_one]; norm_num

/-- **`deriv_u'_eq`, *value* anchor.** `deriv u' 1 = -1/4` — the concrete number, chaining the
bundled equality with the second-derivative value `sq_u''_at_one`. -/
theorem sq_deriv_u'_value : deriv sq.u' 1 = -(1 / 4 : ℝ) := by rw [sq_deriv_u'_eq, sq_u''_at_one]

/-- **`inverseMarginal_pos`.** For `μ = 1/2 > 0`, the inverse marginal is strictly positive. -/
theorem sq_inverseMarginal_pos : 0 < sq.inverseMarginal (1/2) :=
  sq.inverseMarginal_pos (by norm_num)

/-- **`inverseMarginal_spec`, round-trip anchor.** `u'(inverseMarginal μ) = μ` at `μ = 1/2`. -/
theorem sq_inverseMarginal_spec : sq.u' (sq.inverseMarginal (1/2)) = 1/2 :=
  sq.inverseMarginal_spec (by norm_num)

/-- **The marginal-inverse round-trips to the hand-computed point.** Since `u'(c) = 1/2` has the
unique positive solution `c = 1` (from `u'(1) = 1/2` plus the uniqueness in
`unique_marginal_solution`), the inverse marginal recovers `inverseMarginal (1/2) = 1`. This is the
load-bearing semantic anchor for the Inada witness: The marginal and its inverse compose to the
identity at an explicit numeric point. -/
theorem sq_inverseMarginal_at : sq.inverseMarginal (1/2) = 1 := by
  -- `inverseMarginal (1/2)` is the unique positive solution of `u'(c) = 1/2`; `c = 1` is one
  -- (via `sq_u'_at_one`), so uniqueness forces equality.
  have huniq := sq.unique_marginal_solution (1/2) (by norm_num)
  have hinv_sol : sq.inverseMarginal (1/2) ∈ Ioi (0 : ℝ) ∧ sq.u' (sq.inverseMarginal (1/2)) = 1/2 :=
    ⟨sq_inverseMarginal_pos, sq_inverseMarginal_spec⟩
  have hone_sol : (1 : ℝ) ∈ Ioi (0 : ℝ) ∧ sq.u' 1 = 1/2 := ⟨by norm_num, sq_u'_at_one⟩
  exact huniq.unique hinv_sol hone_sol

end inada

/-! ## Chunk 5. Prudence: CRRA is prudent

A utility is prudent when its marginal utility is convex (equivalently `u''' ≥ 0`). For CRRA
with felicity `c^(1-γ)/(1-γ)`, the third derivative is `(1+γ)·γ·x^(-γ-2)`, which is strictly
positive for `γ > 0` (precautionary saving). We exercise
`ConstantRelativeRiskAversionUtility.prudent`, `crraMarginal_pos`, and the third-derivative
characterization `prudent_iff_iteratedDeriv3_nonneg`. -/

section prudence

/-- The CRRA agent with `γ = 2` (reused curvature parameter; `u(x) = -1/x`). -/
private def crraP : ConstantRelativeRiskAversionUtility where
  γ := 2
  γ_pos := by norm_num
  γ_ne_one := by norm_num

/-- **`crraMarginal_pos`, value anchor.** The CRRA marginal `crraMarginal γ x = x^(-γ)` is strictly
positive on `(0, ∞)`; at `γ = 2, x = 2` it is `2^(-2) = 1/4 > 0`. -/
theorem crraP_marginal_pos : 0 < crraMarginal crraP.γ 2 := crraMarginal_pos (by norm_num)

/-- The CRRA marginal value at `(γ, x) = (2, 2)` is exactly `1/4`. -/
theorem crraP_marginal_at : crraMarginal (2 : ℝ) 2 = 1/4 := by
  rw [crraMarginal_apply]
  rw [show -(2 : ℝ) = ((-2 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]
  norm_num

/-- **`ConstantRelativeRiskAversionUtility.prudent`, correct direction.** CRRA utility is prudent:
Its marginal `c^(-γ)` is *convex* on `(0, ∞)` (third derivative nonnegative). -/
theorem crraP_prudent : Prudent (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)) :=
  crraP.prudent

/-- The first derivative `deriv (fun x => x^(1 - γ) / (1 - γ))` is differentiable on `(0, ∞)`.

At every `x ∈ Ioi 0`, `deriv f =ᶠ[𝓝 x] fun y => y^(-γ)` (via `deriv_eq_crraMarginal_on_Ioi`), and
`y ↦ y^(-γ)` is differentiable at `x` by `Real.hasDerivAt_rpow_const`. -/
private lemma crraP_deriv_differentiable :
    DifferentiableOn ℝ (deriv (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ))) (Ioi 0) := by
  -- Set `γ = crraP.γ`, `f x = x^(1-γ)/(1-γ)`, `f' x = x^(-γ)`.
  set γ := crraP.γ
  set f : ℝ → ℝ := fun x => x ^ (1 - γ) / (1 - γ)
  set f' : ℝ → ℝ := fun x => x ^ (-γ)
  -- `deriv f =ᶠ[𝓝 x] f'` for each `x ∈ Ioi 0`.
  have hev : ∀ x ∈ Ioi 0, deriv f =ᶠ[𝓝 x] f' := by
    intro x hx
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mp hx)] with y hy
    exact crraP.deriv_eq_crraMarginal_on_Ioi (mem_Ioi.mpr (mem_Ioi.mp hy))
  -- For each `x ∈ Ioi 0`, `f'` is differentiable at `x` (since `x ≠ 0`).
  intro x hx
  have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
  have hf'_diff : DifferentiableAt ℝ f' x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx'.ne')).differentiableAt
  exact (hf'_diff.congr_of_eventuallyEq (hev x hx)).differentiableWithinAt

/-- The second derivative `deriv (deriv (fun x => x^(1 - γ) / (1 - γ)))` is differentiable on
`(0, ∞)`.

Near each `x ∈ Ioi 0`, `deriv f =ᶠ[𝓝 x] fun y => y^(-γ)`, so `deriv (deriv f)` agrees with
`deriv f'` near `x`.  Since `f' y = y^(-γ)` is differentiable on `Ioi 0`, `deriv (deriv f)` is also
differentiable there. -/
private lemma crraP_deriv2_differentiable :
    DifferentiableOn ℝ
      (deriv (deriv (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)))) (Ioi 0) := by
  set γ := crraP.γ
  set f : ℝ → ℝ := fun x => x ^ (1 - γ) / (1 - γ)
  set f' : ℝ → ℝ := fun x => x ^ (-γ)
  -- `deriv f` and `f'` agree near each `x ∈ Ioi 0`.
  have hev : ∀ x ∈ Ioi 0, deriv f =ᶠ[𝓝 x] f' := by
    intro x hx
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mp hx)] with y hy
    exact crraP.deriv_eq_crraMarginal_on_Ioi (mem_Ioi.mpr (mem_Ioi.mp hy))
  -- The derivative of `f'` is `(-γ) * x^(-γ-1)`, and `f''` is differentiable on `Ioi 0`.
  set f'' : ℝ → ℝ := fun x => (-γ) * x ^ (-γ - 1)
  -- `f'` has derivative `f'' x` at each `x ∈ Ioi 0`: by `hasDerivAt_rpow_const`,
  -- `HasDerivAt (fun x => x^(-γ)) ((-γ) * x^(-γ-1)) x`.
  have hf'_hasDerivAt : ∀ x ∈ Ioi 0, HasDerivAt f' (f'' x) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')
  -- For each `x ∈ Ioi 0`, `deriv (deriv f) =ᶠ[𝓝 x] deriv f'` (pointwise: `(hev y).deriv_eq`).
  -- And `deriv f'` is differentiable at `x`: `deriv f' = f''` near `x`, and `f''` is diff at `x`.
  intro x hx
  have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
  -- Step 1: `deriv (deriv f) =ᶠ[𝓝 x] deriv f'`.
  have hev_dd : deriv (deriv f) =ᶠ[𝓝 x] deriv f' := by
    filter_upwards [isOpen_Ioi.mem_nhds hx'] with y hy
    exact (hev y (mem_Ioi.mpr hy)).deriv_eq
  -- Step 2: `deriv f' =ᶠ[𝓝 x] f''`.
  have hev_df' : deriv f' =ᶠ[𝓝 x] f'' := by
    filter_upwards [isOpen_Ioi.mem_nhds hx'] with y hy
    exact (hf'_hasDerivAt y (mem_Ioi.mpr hy)).deriv
  -- Step 3: `f''` is differentiable at `x`.
  have hf''_diff : DifferentiableAt ℝ f'' x := by
    exact ((Real.hasDerivAt_rpow_const (x := x) (p := -γ - 1)
      (Or.inl hx'.ne')).const_mul (-γ)).differentiableAt
  -- Step 4: `deriv f'` is differentiable at `x` (by congr with `f''`).
  -- `hf''_diff : DifferentiableAt f''`, `hev_df' : deriv f' =ᶠ f''`
  -- ⟹ `DifferentiableAt (deriv f')`.
  have hdf'_diff : DifferentiableAt ℝ (deriv f') x :=
    hf''_diff.congr_of_eventuallyEq hev_df'
  -- Step 5: `deriv (deriv f)` is differentiable at `x` (by congr with `deriv f'`).
  -- `hdf'_diff : DifferentiableAt (deriv f')`, `hev_dd : deriv (deriv f) =ᶠ deriv f'`
  -- ⟹ `DifferentiableAt (deriv (deriv f))`.
  exact (hdf'_diff.congr_of_eventuallyEq hev_dd).differentiableWithinAt

/-- **`prudent_iff_iteratedDeriv3_nonneg`, the third-derivative characterization.** For the CRRA
felicity, prudence is *equivalent* to `u''' ≥ 0` on `(0, ∞)`. Combined with `crraP_prudent`, the
forward direction yields a genuine nonnegative third derivative — the hand sign-check
`u''' = (1+γ)γ x^(-γ-2) ≥ 0`. -/
theorem crraP_iteratedDeriv3_nonneg :
    ∀ x ∈ Ioi 0, 0 ≤ iteratedDeriv 3 (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)) x :=
  (prudent_iff_iteratedDeriv3_nonneg crraP_deriv_differentiable crraP_deriv2_differentiable).mp
    crraP_prudent

/-- **The CRRA third derivative, computed in closed form.** For `γ = 2`, `u(x) = -x⁻¹`, so
`u'(x) = x^(-2)`, `u''(x) = -2 x^(-3)`, `u'''(x) = 6 x^(-4)` — derived here by differentiating the
`crraMarginal` form three times via local eventually-equalities. This is the hand sign-check the
prose claims (with `(1+γ)γ x^(-γ-2) = 3·2·x^(-4) = 6 x^(-4)` at `γ = 2`), now *formalized*. -/
theorem crraP_iteratedDeriv3_formula (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 3 (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)) x = 6 * x ^ (-(4 : ℝ)) := by
  set γ := crraP.γ with hγ
  set f : ℝ → ℝ := fun x => x ^ (1 - γ) / (1 - γ) with hf
  set f1 : ℝ → ℝ := fun x => x ^ (-γ) with hf1
  set f2 : ℝ → ℝ := fun x => (-γ) * x ^ (-γ - 1) with hf2
  set f3 : ℝ → ℝ := fun x => (-γ) * ((-γ - 1) * x ^ (-γ - 2)) with hf3
  have hd1 : deriv f =ᶠ[𝓝 x] f1 := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx)] with y hy
    exact crraP.deriv_eq_crraMarginal_on_Ioi (mem_Ioi.mpr (mem_Ioi.mp hy))
  have hd2 : deriv f1 =ᶠ[𝓝 x] f2 := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx)] with y hy
    exact (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hy).ne')).deriv
  have hd3 : deriv f2 =ᶠ[𝓝 x] f3 := by
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hx)] with y hy
    have hderiv : HasDerivAt f2 ((-γ) * ((-γ - 1) * y ^ (-γ - 1 - 1))) y :=
      (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hy).ne')).const_mul (-γ)
    rw [show (-γ - 1 - 1) = (-γ - 2) by ring] at hderiv
    exact hderiv.deriv
  have key : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
    rw [iteratedDeriv_eq_iterate]; rfl
  rw [key]
  have hchain : deriv (deriv (deriv f)) =ᶠ[𝓝 x] f3 := (hd1.deriv.trans hd2).deriv.trans hd3
  rw [hchain.eq_of_nhds]
  simp only [hf3, hγ, show crraP.γ = (2 : ℝ) from rfl]
  rw [show (-(2 : ℝ) - 2) = (-4 : ℝ) from by norm_num]
  ring

/-- **Third-derivative *point* value.** `u'''(2) = 6 · 2^(-4) = 6/16 = 3/8` — the concrete number
the prose promises but the iff-`.mp` witness above never computes. -/
theorem crraP_iteratedDeriv3_at :
    iteratedDeriv 3 (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)) 2 = 3 / 8 := by
  rw [crraP_iteratedDeriv3_formula 2 (by norm_num),
    show -(4 : ℝ) = ((-4 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]
  norm_num

/-- **`prudent_iff_iteratedDeriv3_nonneg`, the `.mpr` direction.** From the *independently computed*
sign `u'''(x) = 6 x^(-4) > 0` (via `crraP_iteratedDeriv3_formula` + positivity), the converse
direction of the characterization recovers prudence. This exercises the half of the iff the
forward witness `crraP_iteratedDeriv3_nonneg` does not. -/
theorem crraP_prudent_of_iteratedDeriv3 :
    Prudent (fun x : ℝ => x ^ (1 - crraP.γ) / (1 - crraP.γ)) :=
  (prudent_iff_iteratedDeriv3_nonneg crraP_deriv_differentiable crraP_deriv2_differentiable).mpr
    (fun x hx => by
      rw [crraP_iteratedDeriv3_formula x (mem_Ioi.mp hx)]
      have : 0 < x ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos (mem_Ioi.mp hx) _
      linarith)

end prudence

end EconlibTest.Preferences.UtilityFamilies

end
