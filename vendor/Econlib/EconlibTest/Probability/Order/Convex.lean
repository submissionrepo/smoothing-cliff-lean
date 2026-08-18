/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Convex-Order / Mean-Preserving-Spread Non-Vacuity Checks

Compile-time semantic witnesses for the convex-order stack (`Econlib.Probability.Order.Convex`):
The finite mean-preserving-spread predicate (`MPS.lean`), the concavification / affine-majorant
machinery (`Concavification`), the conditional-mean-partition coarsening
(`ConditionalMeanPartition`), the convex-order duality (`Duality`), and the stop-loss bound
(`StopLoss`). The Beta convex-order slice is covered separately in
`EconlibTest/Probability/Distributions/Order.lean`; this file exercises the abstract layers.

The anchors are three concrete mean-preserving spreads:

* **Finite MPS** over `Fin 3` with values `y = (0, 1/2, 1)`: The point mass `δ_{1/2} = (0,1,0)` is
  spread to `½δ_0 + ½δ_1 = (1/2,0,1/2)`, same mean `1/2`, variance `0 → 1/4`.
* **Convex order on `[0,1]`**: The Dirac `δ_{1/2}` at the mean lies below the two-point law
  `½δ_0 + ½δ_1` (mean `1/2`) — `E[x²]` rises `1/4 → 1/2`, the convex direction.
* **Conditional-mean coarsening**: The 2-cell conditional-mean partition of `Beta(2,2)` lies below
  the prior `Beta(2,2)` in convex order, preserving the mean `1/2`.

The orientation-critical anchors: Variance rises under the spread, `E[x²]` rises (convex test),
affine tests give equality, and a *concave* test (or reversed order) would flip the inequality.
-/

noncomputable section

namespace EconlibTest.Probability.Order.Convex

open Econlib.Probability MeasureTheory Set
open Econlib.Probability.Order.Convex.Duality
open scoped BigOperators

/-! ## Finite mean-preserving spread (`IsMPS`) -/

section finiteMPS

/-- The outcome values `(0, 1/2, 1)`. -/
private abbrev yv : Fin 3 → ℝ := ![0, 1 / 2, 1]

/-- The point mass `δ_{1/2}` (all mass on the middle value `1/2`); the *un*-spread law. -/
private abbrev dPt : FinDist (Fin 3) := finDist% ![0, 1, 0]

/-- The mean-preserving spread `½δ_0 + ½δ_1` (mass on the extremes). -/
private abbrev dSpread : FinDist (Fin 3) := finDist% ![1 / 2, 0, 1 / 2]

/-- **Same mean:** both have mean `1/2` — the spread preserves the mean. -/
theorem mps_same_mean : dSpread.expect yv = dPt.expect yv := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three, dPt, dSpread, yv, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-- **The expected-shortfall ordering** (the characterizing condition of MPS): The spread has a
weakly larger shortfall `E[max(t - y, 0)]` at every threshold. Verified region by region in `t`. -/
private theorem mps_shortfall_le (t : ℝ) :
    dPt.expectedShortfall yv t ≤ dSpread.expectedShortfall yv t := by
  rw [FinDist.expectedShortfall_eq, FinDist.expectedShortfall_eq]
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three, dPt, dSpread, yv, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, zero_mul, one_mul, add_zero, zero_add, sub_zero]
  rcases le_or_gt t 0 with h | h
  · rw [max_eq_right (by linarith : t - 1 / 2 ≤ 0), max_eq_right (by linarith : t ≤ 0),
      max_eq_right (by linarith : t - 1 ≤ 0)]; norm_num
  rcases le_or_gt t (1 / 2) with h2 | h2
  · rw [max_eq_right (by linarith : t - 1 / 2 ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ t),
      max_eq_right (by linarith : t - 1 ≤ 0)]; nlinarith
  rcases le_or_gt t 1 with h3 | h3
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ t - 1 / 2), max_eq_left (by linarith : (0 : ℝ) ≤ t),
      max_eq_right (by linarith : t - 1 ≤ 0)]; nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ t - 1 / 2), max_eq_left (by linarith : (0 : ℝ) ≤ t),
      max_eq_left (by linarith : (0 : ℝ) ≤ t - 1)]; nlinarith

/-- **The mean-preserving spread.** `dSpread` is a genuine MPS of `dPt`: Same mean and a weakly
larger shortfall at every threshold. -/
theorem isMPS_witness : FinDist.IsMPS dPt dSpread yv :=
  (FinDist.isMPS_iff_shortfall dPt dSpread yv).mpr ⟨mps_same_mean, mps_shortfall_le⟩

/-- **MPS reflexivity** and **transitivity** (through reflexivity). -/
theorem mps_refl : FinDist.IsMPS dPt dPt yv := FinDist.IsMPS.refl dPt yv
theorem mps_trans : FinDist.IsMPS dPt dSpread yv := FinDist.IsMPS.trans mps_refl isMPS_witness

/-- **Affine tests give equality** under MPS: `E_spread[a·y + b] = E_pt[a·y + b]`. -/
theorem mps_affine_expect_eq (a b : ℝ) :
    (dSpread.expect fun i => a * yv i + b) = dPt.expect fun i => a * yv i + b :=
  isMPS_witness.affine_expect_eq a b

/-- **Variance rises under the spread:** `Var_spread ≥ Var_pt`, anchored `1/4 ≥ 0`. -/
theorem mps_variance_ge : dSpread.variance yv ≥ dPt.variance yv := isMPS_witness.variance_ge

/-- Concrete variance of the un-spread law: `0`. -/
theorem dPt_variance : dPt.variance yv = 0 := by
  simp only [FinDist.variance, FinDist.expect_eq_sum, Fin.sum_univ_three, dPt, yv,
    FinDist.ofVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- Concrete variance of the spread: `1/4`. The spread strictly raises variance, `0 < 1/4`. -/
theorem dSpread_variance : dSpread.variance yv = 1 / 4 := by
  simp only [FinDist.variance, FinDist.expect_eq_sum, Fin.sum_univ_three, dSpread, yv,
    FinDist.ofVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- **Convex test rises under the spread** (`convex_expect_ge`): `E_pt[y²] ≤ E_spread[y²]`. -/
theorem mps_convex_expect_ge :
    dPt.expect ((fun x => x ^ 2) ∘ yv) ≤ dSpread.expect ((fun x => x ^ 2) ∘ yv) :=
  isMPS_witness.convex_expect_ge (fun x => x ^ 2) (even_two.convexOn_pow)

/-- **Concave test falls under the spread** (`concave_expect_le`): `E_spread[-y²] ≤ E_pt[-y²]` —
the risk-averse direction, reversed from the convex test. -/
theorem mps_concave_expect_le :
    dSpread.expect ((fun x => -x ^ 2) ∘ yv) ≤ dPt.expect ((fun x => -x ^ 2) ∘ yv) :=
  isMPS_witness.concave_expect_le (fun x => -x ^ 2) (even_two.convexOn_pow).neg

/-- **The `Fin n` ⇔ generic-`FinDist` MPS bridge** transports the witness to
`Econlib.Probability.IsMPS`. -/
theorem mps_ofFinDist : Econlib.Probability.IsMPS dPt dSpread yv :=
  (FinDist.IsMPS.ofFinDist_iff dPt dSpread yv).mp isMPS_witness

/-- The `Fin n`-specialized variance form: `1/4 ≥ 0` written through `expect`. -/
theorem mps_fin_variance_ge :
    (dSpread.expect fun i => yv i ^ 2) - dSpread.expect yv ^ 2 ≥
      (dPt.expect fun i => yv i ^ 2) - dPt.expect yv ^ 2 :=
  mps_ofFinDist.variance_ge

end finiteMPS

/-! ## Convex order on `[0,1]`, two-point laws, and the concavification machinery -/

section convexOrder

/-- The two-point law `½δ_0 + ½δ_1` on `[0,1]`, mean `1/2`. -/
private abbrev q2 : ProbDist ℝ := twoPointLaw (1 / 2) 0 1 (by norm_num) (by norm_num)

/-- **Two-point mean:** `(1-q)·0 + q·1 = 1/2`. -/
theorem q2_expect_id : q2.expect id = 1 / 2 := by rw [twoPointLaw_expect_id]; norm_num

/-- **Two-point expectation of a convex test** `x²`: `(1-q)·0 + q·1 = 1/2`. -/
theorem q2_expect_sq : q2.expect (fun x => x ^ 2) = 1 / 2 := by rw [twoPointLaw_expect]; norm_num

/-- **Two-point expectation of an affine test** collapses to evaluation at the mean. -/
theorem q2_expect_affine (m c : ℝ) :
    q2.expect (affineFun m c) = affineFun m c ((1 - 1 / 2) * 0 + 1 / 2 * 1) :=
  twoPointLaw_expect_affineFun (1 / 2) 0 1 m c (by norm_num) (by norm_num)

private theorem q2_supp : q2.supportsOn (Icc 0 1) :=
  twoPointLaw_supportsOn_Icc (1 / 2) 0 1 0 1 (by norm_num) (by norm_num) (by simp [Set.mem_Icc])
    (by simp [Set.mem_Icc])

/-- **The convex order.** The Dirac at the mean `δ_{1/2}` lies below the two-point spread `q2` in
the convex order on `[0,1]` — the canonical mean-preserving spread. -/
theorem dirac_le_q2 : ConvexOrderOnIcc 0 1 (ProbDist.dirac (q2.expect id)) q2 :=
  ConvexOrderOnIcc.dirac_left q2_supp

/-- **Convex order preserves the mean:** `E_dirac[id] = E_q2[id] = 1/2`. -/
theorem cx_mean_eq : (ProbDist.dirac (q2.expect id)).expect id = q2.expect id := dirac_le_q2.mean_eq

/-- **Convex test rises:** `E_dirac[x²] = 1/4 ≤ 1/2 = E_q2[x²]`. The convex direction; a concave
test would reverse it. -/
theorem cx_convex_le :
    (ProbDist.dirac (q2.expect id)).expect (fun x => x ^ 2) ≤ q2.expect (fun x => x ^ 2) :=
  dirac_le_q2.convex_expect_le (fun x => x ^ 2)
    (even_two.convexOn_pow.subset (subset_univ _) (convex_Icc 0 1))
    ((continuous_pow 2).continuousOn)

/-- An **asymmetric** two-point law `q = 1/4` on `xL = 1/5`, `xR = 4/5`. Asymmetry (in both the
weight `q ≠ 1/2` and the unequal support points) is what makes the mean/second-moment anchors below
discriminate a left/right (`xL ↔ xR`) swap or a Bernoulli `q ↔ 1 - q` orientation bug — the
symmetric `q2` masks all of those. -/
private abbrev q2asym : ProbDist ℝ :=
  twoPointLaw (1 / 4) (1 / 5) (4 / 5) (by norm_num) (by norm_num)

/-- **Asymmetric two-point mean** `= (1-q)·xL + q·xR = (3/4)(1/5) + (1/4)(4/5) = 7/20`.
A weight or support swap gives a different value
(e.g. swapping `xL ↔ xR` gives `(3/4)(4/5)+(1/4)(1/5) = 13/20`). -/
theorem q2asym_expect_id : q2asym.expect id = 7 / 20 := by
  rw [twoPointLaw_expect_id]; norm_num

/-- **Asymmetric two-point second moment** `= (3/4)(1/25) + (1/4)(16/25) = 19/100`. -/
theorem q2asym_expect_sq : q2asym.expect (fun x => x ^ 2) = 19 / 100 := by
  rw [twoPointLaw_expect]; norm_num

/-- **Convex order against the *literal* `δ_{1/2}`.** `δ_{1/2} ≼cx[0,1] q2`. Since `q2.expect id`
computes to `1/2`, this is `dirac_le_q2` with the mean pinned to the numeric value `1/2`, so the
"mean is `1/2`" story is part of the statement, not just prose. -/
theorem dirac_half_le_q2 : ConvexOrderOnIcc 0 1 (ProbDist.dirac (1 / 2)) q2 := by
  have h := dirac_le_q2
  rwa [q2_expect_id] at h

/-- **The Dirac's second moment is the concrete `1/4`** — strictly below the spread's `1/2`. The
explicit numeric gap `1/4 ≤ 1/2` certifies the convex direction on hard numbers. -/
theorem dirac_half_expect_sq : (ProbDist.dirac (1 / 2 : ℝ)).expect (fun x => x ^ 2) = 1 / 4 := by
  rw [ProbDist.expect_dirac]; norm_num

/-- **The literal convex gap** `E_{δ_{1/2}}[x²] = 1/4 ≤ 1/2 = E_q2[x²]`, both sides pinned. -/
theorem dirac_half_convex_lt_q2 :
    (ProbDist.dirac (1 / 2 : ℝ)).expect (fun x => x ^ 2) ≤ q2.expect (fun x => x ^ 2) := by
  rw [dirac_half_expect_sq, q2_expect_sq]; norm_num

/-- **The hinge payoff is convex** on `[a,b]` — the building block of stop-loss / option pricing. -/
theorem hinge_convex (z : ℝ) : ConvexOn ℝ (Icc 0 1) (fun x => max (x - z) 0) :=
  convexOn_hinge_on 0 1 z

/-- **Affine-majorant bound** (`expect_le_affineFun`): With `x² ≤ x` on `[0,1]` (affine majorant
`affineFun 1 0 = id`), the dominated law's expectation is bounded by the majorant at the dominant
mean: `E_dirac[x²] = 1/4 ≤ 1/2 = affineFun 1 0 (E_q2[id])`. -/
theorem affine_bound :
    (ProbDist.dirac (q2.expect id)).expect (fun x => x ^ 2) ≤ affineFun 1 0 (q2.expect id) :=
  expect_le_affineFun_of_convexOrderOnIcc dirac_le_q2
    (fun x hx => by simp only [Set.mem_Icc] at hx; simp only [affineFun]; nlinarith [hx.1, hx.2])
    (by fun_prop)

/-- **The affine-majorant bound, numerically pinned:** `1/4 ≤ 1/2`. The LHS is `E_{δ_{1/2}}[x²] =
1/4` and the majorant value at the dominant mean is `affineFun 1 0 (1/2) = 1·(1/2) + 0 = 1/2`. -/
theorem affine_bound_value :
    (ProbDist.dirac (1 / 2 : ℝ)).expect (fun x => x ^ 2) ≤ affineFun 1 0 (1 / 2 : ℝ) := by
  rw [dirac_half_expect_sq]
  simp only [affineFun]
  norm_num

/-- **Concave-envelope bound** (`expect_le_concaveEnvelope`): The dominated expectation is below
the concave envelope of the test at the dominant mean. -/
theorem concaveEnvelope_bound :
    (ProbDist.dirac (q2.expect id)).expect (fun x => x ^ 2) ≤
      concaveEnvelope 0 1 (fun x => x ^ 2) (q2.expect id) :=
  expect_le_concaveEnvelope_of_convexOrderOnIcc (by norm_num) dirac_le_q2 (by fun_prop)

/-- **Contact-set support.** For the concave payoff `-(x-1/2)²` with the constant affine majorant
`0` (contact at `1/2`), the dominated Dirac is supported on the contact set where payoff meets
majorant. -/
theorem contactSet_witness :
    (ProbDist.dirac (q2.expect id)).supportsOn
      (contactSet 0 1 (fun x => -(x - 1 / 2) ^ 2) 0 0) := by
  apply supportsOn_contactSet_of_convexOrder_eq_affineFun dirac_le_q2
    (fun x _ => by simp only [affineFun]; nlinarith [sq_nonneg (x - 1 / 2)])
    (by fun_prop)
  rw [q2_expect_id]
  simp only [affineFun, ProbDist.expect_dirac]
  norm_num

end convexOrder

/-! ## Convex-order duality and the stop-loss bound -/

section dualityAndStopLoss

private abbrev q2' : ProbDist ℝ := twoPointLaw (1 / 2) 0 1 (by norm_num) (by norm_num)

private theorem q2'_supp : q2'.supportsOn (Icc 0 1) :=
  twoPointLaw_supportsOn_Icc (1 / 2) 0 1 0 1 (by norm_num) (by norm_num) (by simp [Set.mem_Icc])
    (by simp [Set.mem_Icc])

/-- The convex payoff `x²` as a `PayoffOnIcc 0 1`. -/
private abbrev vPay : PayoffOnIcc 0 1 := ⟨fun x => x ^ 2, by fun_prop⟩

/-- The affine price `p(x) = x` as a `PayoffOnIcc 0 1` — the convex majorant of `x²` on `[0,1]`. -/
private abbrev pPay : PayoffOnIcc 0 1 := ⟨fun x => x, by fun_prop⟩

/-- **A concrete feasible primal value `1/4`.** The dominated Dirac `δ_{1/2}` (convex-order below
`q2'`) has payoff expectation `E_{δ_{1/2}}[x²] = (1/2)² = 1/4`, so `1/4` is a feasible primal value.
This *constructs* a member of `primalValueSet`, where the old `duality_witness` only assumed one. -/
theorem primal_value_quarter : (1 / 4 : ℝ) ∈ primalValueSet 0 1 q2' vPay := by
  refine ⟨ProbDist.dirac (q2'.expect id), ConvexOrderOnIcc.dirac_left q2'_supp, ?_⟩
  rw [ProbDist.expect_dirac, q2_expect_id]
  norm_num

/-- **A concrete feasible dual value `1/2`.** The affine price `p(x) = x` is convex and dominates
`x²` on `[0,1]` (since `x² ≤ x` there), so it is a feasible convex majorant; its dual objective is
`E_{q2'}[x] = 1/2`. This constructs a member of `dualValueSet`. -/
theorem dual_value_half : (1 / 2 : ℝ) ∈ dualValueSet 0 1 q2' vPay := by
  refine ⟨pPay, ⟨?_, ?_⟩, ?_⟩
  · -- `p(x) = x` is convex on `[0,1]`.
    exact (convexOn_id (convex_Icc 0 1))
  · -- `x² ≤ x` on `[0,1]`.
    intro x hx
    simp only [Set.mem_Icc] at hx
    change x ^ 2 ≤ x
    nlinarith [hx.1, hx.2]
  · -- `E_{q2'}[x] = 1/2`.
    rw [dualObjectiveConvexOrder, show ⇑pPay = (id : ℝ → ℝ) from rfl, twoPointLaw_expect_id]
    norm_num

/-- **Weak duality on the concrete feasible pair** (`primalValueSet_le_dualValueSet`): the feasible
primal value `1/4` is below the feasible dual value `1/2`. Unlike a witness that only *assumes*
membership, this derives the concrete numeric gap `1/4 ≤ 1/2` from the two constructed members. -/
theorem duality_witness : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) :=
  primalValueSet_le_dualValueSet primal_value_quarter dual_value_half

/-- **The stop-loss bound** `(r - s)·P(X ≥ r) ≤ E_ν[max(X - s, 0)]` for the dominated Dirac against
the spread — Markov's inequality for the convex stop-loss payoff under convex order, quantified over
every threshold pair `(s, r)`. This is the API-shape witness on the general theorem; the concrete
stop-loss value of the two-point law `q2'` is anchored numerically in `q2'_stopLoss_zero` below. -/
theorem stopLoss_bound (s r : ℝ) :
    (r - s) * (ProbDist.dirac (q2'.expect id)).toMeasure.real (Ici r) ≤ q2'.toMeasure.stopLoss s :=
  mul_measureReal_Ici_le_stopLoss_of_convexOrderOnIcc
    (ConvexOrderOnIcc.dirac_left
      (twoPointLaw_supportsOn_Icc (1 / 2) 0 1 0 1 (by norm_num) (by norm_num)
        (by simp [Set.mem_Icc]) (by simp [Set.mem_Icc]))) s r

/-- **Concrete stop-loss value.** `E_{q2'}[max(X - 0, 0)] = (1/2)·max(0,0) + (1/2)·max(1,0) = 1/2`.
The stop-loss is the expectation of the convex hinge `max(x - s, 0)`; at `s = 0` over `q2' =
½δ₀ + ½δ₁` only the `x = 1` atom contributes, giving `1/2`. A nonzero numeric anchor for the
otherwise abstract stop-loss API. -/
theorem q2'_stopLoss_zero : q2'.toMeasure.stopLoss 0 = 1 / 2 := by
  rw [Measure.stopLoss, show (∫ x, max (x - 0) 0 ∂q2'.toMeasure)
      = q2'.expect (fun x => max (x - 0) 0) from rfl, twoPointLaw_expect]
  norm_num

end dualityAndStopLoss

/-! ## The conditional-mean-partition coarsening -/

section conditionalMeanPartition

/-- The 2-cell partition of `[0,1]` split at `1/2`. -/
private def P2 : OrderedCutoffPartition 2 0 1 where
  cutoff := ![0, 1 / 2, 1]
  lt := by norm_num
  left_eq := rfl
  right_eq := rfl
  monotone := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]; norm_num

/-- The prior law `Beta(2,2)` (density `6x(1-x)`, mean `1/2`). -/
private abbrev b22 : ContDist := ContDist.beta 2 2 (by norm_num) (by norm_num)

private theorem b22_cont : ContinuousOn b22.density (Set.Icc 0 1) := by
  -- On `[0,1]`, `betaPDFReal 2 2` agrees with the globally continuous
  -- `g x = (1/B(2,2)) · x^(2-1) · (1-x)^(2-1)`: at the endpoints both sides are `0`.
  set g : ℝ → ℝ :=
    fun x => 1 / ProbabilityTheory.beta 2 2 * x ^ ((2 : ℝ) - 1) * (1 - x) ^ ((2 : ℝ) - 1) with hg
  have hg_cont : Continuous g := by fun_prop (disch := norm_num)
  refine hg_cont.continuousOn.congr ?_
  intro x hx
  simp only [ContDist.beta_density]
  by_cases hxi : 0 < x ∧ x < 1
  · simp only [ProbabilityTheory.betaPDFReal, hxi, and_self, if_true, hg]
  · rw [betaPDFReal_eq_zero_of_not_mem 2 2 hxi]
    rcases hx with ⟨hx0, hx1⟩
    rcases eq_or_lt_of_le hx0 with hx0' | hx0'
    · simp only [hg, ← hx0']; rw [Real.zero_rpow (by norm_num)]; ring
    · have hx1' : x = 1 := by
        rcases lt_or_eq_of_le hx1 with h | h
        · exact absurd ⟨hx0', h⟩ hxi
        · exact h
      simp only [hg, hx1']; rw [show (1 : ℝ) - 1 = 0 by ring, Real.zero_rpow (by norm_num)]; ring

private theorem b22_pos : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < b22.density x := by
  intro x hx
  simp only [ContDist.beta_density]
  exact ProbabilityTheory.betaPDFReal_pos hx.1 hx.2 (by norm_num) (by norm_num)

private theorem b22_supp : b22.toProbDist.supportsOn (Set.Icc 0 1) :=
  ContDist.toProbDist_supportsOn_Icc b22
    (fun x hx => ContDist.beta_density_eq_zero_of_not_mem 2 2 (by norm_num) (by norm_num) hx)

private theorem P2_eta : P2.EtaSpaced (1 / 2) := by
  intro j
  unfold OrderedCutoffPartition.rightEndpoint OrderedCutoffPartition.leftEndpoint
  fin_cases j <;>
    (show (1 : ℝ) / 2 ≤ P2.cutoff _ - P2.cutoff _
     simp only [P2, Fin.succ, Fin.castSucc, Fin.isValue, Matrix.cons_val_zero,
       Fin.castAdd, Fin.castLE, Fin.mk_zero]
     norm_num)

/-- **Cell masses are nonnegative.** -/
theorem cellMass_nonneg_witness (j : Fin 2) : 0 ≤ cellMass b22 P2 j := cellMass_nonneg b22 P2 j

/-- **Cell masses are positive** (`cellMass_pos_of_density_pos`) for the strictly-positive Beta
density on the `η`-spaced partition. -/
theorem hpos : ∀ j : Fin 2, 0 < cellMass b22 P2 j :=
  fun j => cellMass_pos_of_density_pos b22 P2 j b22_pos b22_cont P2_eta (by norm_num)

/-- **The conditional mean lands in its cell:** `cellMean ∈ cellClosed`. -/
theorem cellMean_mem (j : Fin 2) : cellMean b22 P2 j ∈ P2.cellClosed j :=
  cellMean_mem_cell b22 P2 j (hpos j) b22_cont

/-- **Cell masses sum to one** — the partition exhausts the probability. -/
theorem cellMass_sum : ∑ k : Fin 2, cellMass b22 P2 k = 1 :=
  cellMass_sum_eq_one b22 P2 b22_supp

/-- **The prior `Beta(2,2)` mean is `1/2`** — the concrete anchor the convex-order witness
preserves. `E[X] = α/(α+β) = 2/4 = 1/2`. -/
theorem b22_mean_half : b22.toProbDist.expect id = 1 / 2 := by
  rw [← ContDist.expect_eq_probDist_expect, ContDist.beta_expect]; norm_num

/-- **The prior `Beta(2,2)` second moment is `3/10`** — the *dispersed* prior value that the
coarsened law lies strictly below in convex order. `E[X²] = Var + mean² = 1/20 + 1/4 = 3/10`. -/
theorem b22_expect_sq : b22.expect (fun x => x ^ 2) = 3 / 10 := by
  have hvar : b22.variance id = 1 / 20 := by
    rw [ContDist.beta_variance]; norm_num
  have hdef : b22.variance id = b22.expect (fun x => x ^ 2) - (b22.expect id) ^ 2 := rfl
  have hmean : b22.expect id = 1 / 2 := by rw [ContDist.beta_expect]; norm_num
  rw [hvar, hmean] at hdef
  linarith [hdef]

/-- **The coarsening is mean-preserving, anchored to `1/2`:** the conditional-mean-partition law has
the same mean as the prior `Beta(2,2)`, namely the concrete value `1/2`. (The original witness only
stated equality to `b22.toProbDist.expect id`; here both are pinned to `1/2`.) -/
theorem cmpLaw_mean :
    (conditionalMeanPartitionLaw b22 P2 hpos).expect id = 1 / 2 := by
  rw [conditionalMeanPartitionLaw_expect_id_eq_prior b22 P2 hpos b22_cont b22_supp, b22_mean_half]

/-- **Cell masses are `(1/2, 1/2)`.** The split at `1/2` halves the symmetric `Beta(2,2)`:
`cellMass(0) = ∫₀^{1/2} 6x(1-x) dx = [3x² - 2x³]₀^{1/2} = 3/4 - 1/4 = 1/2`, and by symmetry
`cellMass(1) = 1/2`. A concrete, *nonzero* anchor — and the equal split is the discriminating fact a
broken cell-indexing would violate. -/
theorem cmpLaw_cellMass_zero : cellMass b22 P2 0 = 1 / 2 := by
  rw [show cellMass b22 P2 0 = ∫ x in P2.cellClosed 0, b22.density x from rfl]
  rw [show P2.cellClosed 0 = Set.Icc (0 : ℝ) (1 / 2) from by
    simp [OrderedCutoffPartition.cellClosed, P2, OrderedCutoffPartition.leftEndpoint,
      OrderedCutoffPartition.rightEndpoint]]
  -- Move to Ioc to have strict positivity at the left endpoint (null set difference)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- On Ioc 0 (1/2), every x satisfies 0 < x < 1, so betaPDFReal 2 2 x = 6x - 6x²
  have hbeta_val : ProbabilityTheory.beta 2 2 = 1 / 6 := by
    simp only [ProbabilityTheory.beta]
    rw [Real.Gamma_two]
    rw [show (2 : ℝ) + 2 = (3 : ℝ) + 1 from by norm_num,
        Real.Gamma_add_one (by norm_num : (3 : ℝ) ≠ 0),
        show (3 : ℝ) = (2 : ℝ) + 1 from by norm_num,
        Real.Gamma_add_one (by norm_num : (2 : ℝ) ≠ 0), Real.Gamma_two]
    norm_num
  rw [show (∫ x in Set.Ioc (0:ℝ) (1/2), b22.density x)
      = ∫ x in Set.Ioc (0:ℝ) (1/2), (6 * x - 6 * x ^ 2) from
        setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
          simp only [Set.mem_Ioc] at hx
          rw [ContDist.beta_density, ProbabilityTheory.betaPDFReal,
              if_pos ⟨hx.1, by linarith⟩, hbeta_val]
          rw [show (2 : ℝ) - 1 = 1 from by norm_num, Real.rpow_one, Real.rpow_one]
          ring)]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show (fun x : ℝ => 6 * x) = fun x => 6 * x ^ 1 from by funext x; ring]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num

/-- **The headline: The conditional-mean coarsening lies below the prior in convex order.** Coarse
information is a mean-preserving *contraction* of the prior — the genuine Blackwell/persuasion
content. The accompanying numeric anchors (`cmpLaw_mean = 1/2`, `b22_expect_sq = 3/10`,
`cmpLaw_cellMass_zero = 1/2`) certify that the dominated and dominant laws are genuinely distinct
spreads, not the degenerate equal case. -/
theorem cmpLaw_cx : conditionalMeanPartitionLaw b22 P2 hpos ≼cx[0,1] b22.toProbDist :=
  conditionalMeanPartitionLaw_convexOrderOnIcc b22 P2 hpos b22_cont b22_supp

/-- **The coarsened law is the cell-weighted point law on the conditional means.** -/
theorem cmpLaw_weighted :
    (conditionalMeanPartitionLaw b22 P2 hpos).expect (fun x => x) =
      ∑ j : Fin 2, (conditionalMeanWeights b22 P2 hpos).pmf j * cellMean b22 P2 j :=
  conditionalMeanPartitionLaw_expect_eq_weighted b22 P2 hpos (fun x => x)

end conditionalMeanPartition

end EconlibTest.Probability.Order.Convex

end
