/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# First-Order Stochastic Dominance Non-Vacuity Checks

Compile-time semantic witnesses for the finite-distribution FOSD layer
(`Econlib.Probability.Order.FOSD.FinDist`). Stochastic-order facts are especially prone to silent
*direction* reversals (FOSD vs. reverse-FOSD), so these witnesses fix an unambiguous dominant /
dominated pair and check that the higher law raises monotone expectations and lowers antitone ones.

The pair, over `Fin 3`:

* `dHi = (1/6, 1/3, 1/2)` — mass pushed toward high outcomes (mean `4/3`);
* `dLo = (1/2, 1/3, 1/6)` — the mirror image, mass toward low outcomes (mean `2/3`).

`dHi` first-order stochastically dominates `dLo`: its CDF lies weakly below `dLo`'s at every cutoff.
A reversed inequality, a swapped pair, or a sign error in the antitone direction breaks a witness.
-/

noncomputable section

namespace EconlibTest.Probability.Order.FOSD

open Econlib.Probability

/-- The dominant law: mass concentrated on high outcomes. -/
private abbrev dHi : FinDist (Fin 3) := finDist% ![1 / 6, 1 / 3, 1 / 2]

/-- The dominated law: the mirror image, mass on low outcomes. -/
private abbrev dLo : FinDist (Fin 3) := finDist% ![1 / 2, 1 / 3, 1 / 6]

/-- The integer outcome map. -/
private abbrev outcome : Fin 3 → ℝ := fun i => (i.val : ℝ)

private theorem outcome_mono : Monotone (outcome : Fin 3 → ℝ) := fun i j hij => by
  have : (i.val : ℝ) ≤ j.val := by exact_mod_cast Fin.le_def.mp hij
  simpa [outcome] using this

section dominance

/-- **The dominance relation.** `dHi` FOSD-dominates `dLo`: at every cutoff its lower-tail mass is
no larger (`F_hi ≤ F_lo`). The CDFs are `(1/6, 1/2, 1)` vs. `(1/2, 5/6, 1)`. -/
theorem dHi_fosd_dLo : FinDist.FOSD dHi dLo := by
  rw [FinDist.FOSD_iff]
  intro a
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three]
  fin_cases a <;>
    simp only [dHi, dLo, FinDist.ofVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.le_def, Fin.val_zero,
      Fin.val_one, Fin.val_two, Fin.isValue] <;>
    norm_num

/-- **CDF values for `dHi`.** Hand-computation:
- `cdf(0) = P(X ≤ 0) = 1/6`
- `cdf(1) = P(X ≤ 1) = 1/6 + 1/3 = 1/2`
- `cdf(2) = P(X ≤ 2) = 1/6 + 1/3 + 1/2 = 1` -/
theorem dHi_cdf_zero : dHi.cdf 0 = 1 / 6 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dHi, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

theorem dHi_cdf_one : dHi.cdf 1 = 1 / 2 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dHi, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

theorem dHi_cdf_two : dHi.cdf 2 = 1 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dHi, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

/-- **CDF values for `dLo`.** Hand-computation:
- `cdf(0) = P(X ≤ 0) = 1/2`
- `cdf(1) = P(X ≤ 1) = 1/2 + 1/3 = 5/6`
- `cdf(2) = P(X ≤ 2) = 1/2 + 1/3 + 1/6 = 1` -/
theorem dLo_cdf_zero : dLo.cdf 0 = 1 / 2 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dLo, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

theorem dLo_cdf_one : dLo.cdf 1 = 5 / 6 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dLo, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

theorem dLo_cdf_two : dLo.cdf 2 = 1 := by
  simp only [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, dLo, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.le_def, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  norm_num

/-- **Pure dominance.** A point mass higher up FOSD-dominates one lower down: `pure 2 ⪰ pure 0`. -/
theorem pure_fosd : FinDist.FOSD (FinDist.pure (2 : Fin 3)) (FinDist.pure 0) :=
  FinDist.FOSD_pure (by decide)

/-- **Reflexivity** in the combinatorial form (every law dominates itself). -/
theorem fosd_refl : FinDist.FOSD dHi dHi := by
  rw [FinDist.FOSD_iff]; intro a; exact le_refl _

/-- **Asymmetry guard.** `dLo` does NOT FOSD-dominate `dHi`: `dLo.cdf 0 = 1/2 > 1/6 = dHi.cdf 0`,
so the CDF comparison fails at cutoff `0`. This confirms the strict direction of `dHi_fosd_dLo`. -/
theorem fosd_not_reverse : ¬ FinDist.FOSD dLo dHi := by
  rw [FinDist.FOSD_iff]
  push Not
  exact ⟨0, by rw [dLo_cdf_zero, dHi_cdf_zero]; norm_num⟩

end dominance

section expectations

/-- Mean of the dominant law: `0·1/6 + 1·1/3 + 2·1/2 = 4/3`. -/
theorem dHi_mean : dHi.expect outcome = 4 / 3 := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three, dHi, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, outcome]
  norm_num

/-- Mean of the dominated law: `0·1/2 + 1·1/3 + 2·1/6 = 2/3`. -/
theorem dLo_mean : dLo.expect outcome = 2 / 3 := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three, dLo, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, outcome]
  norm_num

/-- **FOSD raises monotone expectations.** Every increasing payoff has a weakly higher mean under
the dominant law: `E_lo[u] ≤ E_hi[u]`. Anchored by `dHi_mean = 4/3 > 2/3 = dLo_mean`, this is the
*right* direction — a reversed FOSD would give `≥`. -/
theorem fosd_raises_monotone_mean : dLo.expect outcome ≤ dHi.expect outcome :=
  FinDist.FOSD_expect_mono dHi_fosd_dLo outcome_mono

/-- **FOSD lowers antitone expectations.** A decreasing payoff is worth weakly *less* under the
dominant law: `E_hi[-u] ≤ E_lo[-u]`. -/
theorem fosd_lowers_antitone_mean :
    dHi.expect (fun i => -outcome i) ≤ dLo.expect (fun i => -outcome i) :=
  FinDist.FOSD_expect_antitone dHi_fosd_dLo outcome_mono.neg

/-- **Direct expectation ordering.** For any monotone `f : Fin 3 → ℝ`:
`E_hi[f] = (1/6)f(0) + (1/3)f(1) + (1/2)f(2)` and
`E_lo[f] = (1/2)f(0) + (1/3)f(1) + (1/6)f(2)`.
Difference: `E_hi - E_lo = (1/3)(f(2) - f(0)) ≥ 0` since `f(0) ≤ f(2)` by monotonicity. -/
theorem dHi_expect_ge_dLo (f : Fin 3 → ℝ) (hf : Monotone f) :
    dLo.expect f ≤ dHi.expect f := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three, dHi, dLo, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h02 : f 0 ≤ f 2 := hf (by decide)
  nlinarith

/-- **Threshold-payoff converse.** `FOSD_of_expect_mono` applied to the DIRECT expectation
ordering `dHi_expect_ge_dLo` (not a round-trip through dominance). This exercises the converse
direction on genuinely hand-computed concrete data. -/
theorem fosd_of_expect_mono_witness : FinDist.FOSD dHi dLo :=
  FinDist.FOSD_of_expect_mono dHi_expect_ge_dLo

/-- **The characterization.** FOSD holds exactly when every monotone decision maker prefers
`dHi`. The `.mp` direction recovers the expectation ordering from `dHi_fosd_dLo`; the `.mpr`
direction recovers dominance from the direct expectation proof `dHi_expect_ge_dLo`. -/
theorem fosd_iff_witness :
    FinDist.FOSD dHi dLo ↔ ∀ f : Fin 3 → ℝ, Monotone f → dLo.expect f ≤ dHi.expect f :=
  FinDist.FOSD_iff_expect_mono dHi dLo

/-- **`.mp` direction applied concretely.** `dHi_fosd_dLo` feeds `FOSD_iff_expect_mono.mp`
to produce the expectation ordering. -/
theorem fosd_iff_mp_witness : ∀ f : Fin 3 → ℝ, Monotone f → dLo.expect f ≤ dHi.expect f :=
  fosd_iff_witness.mp dHi_fosd_dLo

/-- **`.mpr` direction applied concretely.** The direct expectation proof `dHi_expect_ge_dLo`
feeds `FOSD_iff_expect_mono.mpr` to recover dominance. -/
theorem fosd_iff_mpr_witness : FinDist.FOSD dHi dLo :=
  fosd_iff_witness.mpr dHi_expect_ge_dLo

end expectations

end EconlibTest.Probability.Order.FOSD

end
