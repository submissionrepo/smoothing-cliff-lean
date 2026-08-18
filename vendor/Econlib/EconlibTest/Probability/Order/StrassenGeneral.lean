/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Strassen Remainder Non-Vacuity Checks

Compile-time semantic witnesses for the parts of the Strassen layer
(`Econlib.Probability.Order.Strassen`) that `Strassen.lean` leaves open: The general
(non-uniform-weight) discrete Strassen theorem (`DiscreteGeneral`), the martingale-coupling /
dilation equivalence (`Dilation`), the dilation API itself, the conditional-mean-atomization
(`CondMeanAtom`), and the weak-limit martingale transfer (`WeakLimit`). The uniform δ₀ → ½δ₋₁+½δ₊₁
slice (martingale coupling, mean equality, `convex_expect_le`, packaged convex order) is covered in
`EconlibTest/Probability/Order/Strassen.lean`.

The headline anchor is a **non-uniform** convex-order pair:

* `p0 = δ₀` — a point mass at `0` (the un-spread law);
* `q3 = ¼δ₋₂ + ½δ₀ + ¼δ₊₂` — a *non-uniformly weighted* three-point spread with the **same mean**
  `0` but strictly larger dispersion (`E[x²] = 2`).

Because `p0` is a point mass, `p0 ≼cx q3` is exactly finite Jensen: `φ(0) = φ(E_q3[x]) ≤ E_q3[φ]`
for every convex `φ`. The general discrete Strassen theorem then produces a martingale coupling,
the orientation-critical content (a reversed order, or non-equal means, would have no coupling).

The dilation API is exercised through the trivial identity-mean-preserving kernel `K x = δ_x`; the
weak-limit transfer through the constant sequence of the uniform δ₀/spread coupling.
-/

noncomputable section

namespace EconlibTest.Probability.Order.StrassenGeneral

open Econlib.Probability MeasureTheory Set Finset
open scoped BigOperators

/-! ## The non-uniform convex-order pair and the general discrete Strassen theorem -/

/-- The un-spread law `δ₀` (point mass at `0`). -/
private abbrev p0 : DiscreteLaw := ⟨1, ![0], ![1], fun i => by fin_cases i; norm_num, by simp⟩

/-- The non-uniformly weighted spread `¼δ₋₂ + ½δ₀ + ¼δ₊₂`, mean `0`. -/
private abbrev q3 : DiscreteLaw :=
  ⟨3, ![-2, 0, 2], ![1 / 4, 1 / 2, 1 / 4], fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num⟩

/-- **Same mean (point mass):** `mean(δ₀) = 0`. -/
theorem p0_mean : p0.mean = 0 := by simp [DiscreteLaw.mean]

/-- **Same mean (non-uniform spread):** `mean(¼δ₋₂ + ½δ₀ + ¼δ₊₂) = 0`. -/
theorem q3_mean : q3.mean = 0 := by simp [DiscreteLaw.mean, Fin.sum_univ_three]

/-- **The discrete convex order.** `δ₀ ≼cx q3`: A point mass below a same-mean spread. The point
mass makes this exactly finite Jensen — `φ(0) = φ(E_q3[x]) ≤ E_q3[φ]` for every convex `φ`. A
reversed order or a non-mean-preserving spread would break the Jensen step. -/
theorem p0_cx_q3 : p0.ConvexOrder q3 := by
  intro φ hφ
  simp only [Fin.sum_univ_one, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, one_mul]
  have hjensen := hφ.map_sum_le (t := Finset.univ) (w := ![1 / 4, 1 / 2, 1 / 4])
    (p := ![(-2 : ℝ), 0, 2]) (fun i _ => by fin_cases i <;> norm_num)
    (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]; norm_num)
    (fun i _ => Set.mem_univ _)
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at hjensen
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, smul_eq_mul] at hjensen
  rw [show (1 / 4 * (-2 : ℝ) + 1 / 2 * 0 + 1 / 4 * 2) = 0 by norm_num] at hjensen
  linarith

/-- **`x²`-expectation of point mass is 0.** Hand-check: `E_{δ₀}[x²] = 1·0² = 0`. -/
theorem p0_expect_sq : p0.toProbDist.expect (fun x => x ^ 2) = 0 := by
  rw [DiscreteLaw.expect_eq p0 (by fun_prop)]
  simp

/-- **`E[x²]` rises under the spread:** `E_q3[x²] = 2`, against `E_{δ₀}[x²] = 0` — the convex
direction (`δ₀` below `q3`).
Hand-check: `¼·(-2)² + ½·0² + ¼·2² = ¼·4 + 0 + ¼·4 = 1 + 1 = 2`. -/
theorem q3_expect_sq : q3.toProbDist.expect (fun x => x ^ 2) = 2 := by
  rw [DiscreteLaw.expect_eq q3 (by fun_prop)]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- **Strict dispersion gap.** `E_{δ₀}[x²] = 0 < 2 = E_{q3}[x²]` — confirms the convex-order
direction is strict between two genuinely distinct laws. -/
theorem p0_expect_sq_lt_q3 : p0.toProbDist.expect (fun x => x ^ 2) <
    q3.toProbDist.expect (fun x => x ^ 2) := by
  rw [p0_expect_sq, q3_expect_sq]; norm_num

/-- **The headline: General (non-uniform) discrete Strassen.** From the convex order on the
non-uniformly weighted pair, `DiscreteLaw.exists_martingaleCoupling` produces a genuine martingale
coupling of `δ₀` and `q3` — the recent generalization beyond uniform weights. -/
theorem exists_mart :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling p0.toProbDist q3.toProbDist π :=
  DiscreteLaw.exists_martingaleCoupling p0 q3 p0_cx_q3

/-- **The discrete convex order embeds into `ConvexOrderOnIcc`** on some bounding interval. -/
theorem cx_to_icc : ∃ a b : ℝ, p0.toProbDist ≼cx[a,b] q3.toProbDist :=
  convexOrderOnIcc_toProbDist_of_convexOrder p0_cx_q3

/-! ## The martingale-coupling ⇔ dilation equivalence -/

/-- **The equivalence `isMartingaleCoupling_iff_dilation`:** a martingale coupling exists iff there
is a mean-preserving kernel whose `snd` marginal is `q3`. This is an abstract API check — the
equivalence itself (not the specific kernel) is what's tested; the concrete witness is
existential. -/
theorem mart_iff_dilation :
    (∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling p0.toProbDist q3.toProbDist π) ↔
      ∃ (K : ProbabilityTheory.Kernel ℝ ℝ) (h : IsMeanPreservingKernel p0.toProbDist K),
        h.snd = q3.toProbDist :=
  isMartingaleCoupling_iff_dilation p0.toProbDist q3.toProbDist

/-- **Forward direction:** the existential coupling from general Strassen transports to the kernel-
dilation form via `mart_iff_dilation.mp`. The resulting kernel is existential (not displayed). -/
theorem dilation_form :
    ∃ (K : ProbabilityTheory.Kernel ℝ ℝ) (h : IsMeanPreservingKernel p0.toProbDist K),
      h.snd = q3.toProbDist :=
  mart_iff_dilation.mp exists_mart

/-! ## The dilation API via the identity mean-preserving kernel -/

/-- The identity (deterministic) kernel `K x = δ_x`. -/
private abbrev Kid : ProbabilityTheory.Kernel ℝ ℝ :=
  ProbabilityTheory.Kernel.deterministic id measurable_id

private theorem q3_integrable_id : Integrable (fun x : ℝ => x) q3.toProbDist.toMeasure := by
  have hsupp : q3.toProbDist.supportsOn (Icc (-2 : ℝ) 2) :=
    q3.toProbDist_supportsOn_of_atoms_mem measurableSet_Icc
      (fun i => by fin_cases i <;> simp [Set.mem_Icc])
  exact ProbDist.integrable_of_supportsOn_Icc hsupp continuousOn_id

/-- **Mean-preserving kernel (diagonal case).** The identity kernel `K x = δ_x` is Markov, has
integrable second coordinate, and preserves the mean (`∫ y dδ_x = x`). Its `snd` marginal is
`q3` itself — the trivial (diagonal) dilation. This exercises the `IsMeanPreservingKernel` API
on the simplest case; a non-trivial kernel would spread mass from each point to a genuine
conditional distribution. -/
theorem mpk : IsMeanPreservingKernel q3.toProbDist Kid where
  markov := ProbabilityTheory.Kernel.isMarkovKernel_deterministic measurable_id
  integrable_snd := by
    haveI : ProbabilityTheory.IsMarkovKernel Kid :=
      ProbabilityTheory.Kernel.isMarkovKernel_deterministic measurable_id
    rw [MeasureTheory.Measure.integrable_compProd_iff measurable_snd.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards with x
      rw [Kid, ProbabilityTheory.Kernel.deterministic_apply]
      exact integrable_dirac (by simp [enorm_lt_top])
    · simp only [Kid, ProbabilityTheory.Kernel.deterministic_apply, id_eq,
        MeasureTheory.integral_dirac, Real.norm_eq_abs]
      exact q3_integrable_id.abs
  ae_mean_eq := by
    filter_upwards with x
    rw [Kid, ProbabilityTheory.Kernel.deterministic_apply]; simp

/-- **The dilation's first marginal recovers the base law.** For the identity kernel `K x = δ_x`,
the dilation `q3 ⊗ Kid` is supported on the diagonal, so `fst`-pushforward = `q3`. This exercises
the `dilation_fst` API on a diagonal (identity-kernel) dilation — the trivial case. A non-diagonal
dilation would require a different kernel with genuine spread. -/
theorem dilation_fst_witness :
    (q3.toProbDist.dilation Kid).map Prod.fst (by fun_prop) = q3.toProbDist :=
  q3.toProbDist.dilation_fst Kid

/-- **A mean-preserving kernel's dilation is a martingale coupling.** For the identity kernel
`K x = δ_x`, the dilation is the diagonal coupling — a martingale coupling of `q3` with `q3`
(its own `snd` marginal under `Kid`). This is the diagonal (trivial) case; a non-diagonal
martingale coupling requires a spreading kernel. -/
theorem dilation_mart :
    IsMartingaleCoupling q3.toProbDist mpk.snd (q3.toProbDist.dilation Kid) :=
  mpk.dilation_isMartingaleCoupling

/-! ## Conditional-mean atomization -/

/-- **The atomization has `n = 2` atoms** (structural, from `condMeanAtomize_n`). The atom *values*
are `condMeanAtom q3.toProbDist 2 _ k = 2 · ∫_{(k/2,(k+1)/2]} quantile(q3)`, defined as quantile
integrals — not computable to closed form in this test file without additional quantile API. -/
theorem cma_n : (DiscreteLaw.condMeanAtomize q3.toProbDist 2 (by norm_num)).n = 2 :=
  DiscreteLaw.condMeanAtomize_n

/-- **The atomization is uniformly weighted** (`1/2` per atom, from `condMeanAtomize_weight`). -/
theorem cma_weight (k : Fin 2) :
    (DiscreteLaw.condMeanAtomize q3.toProbDist 2 (by norm_num)).weight k = 1 / 2 :=
  DiscreteLaw.condMeanAtomize_weight

/-- **Atomization preserves the convex order.** The conditional-mean atomizations of `δ₀` and `q3`
remain convex-ordered — the key monotonicity behind the continuous-Strassen approximation. The
result is existential (bounding interval inherited from `cx_to_icc`); the atomized atom values are
quantile integrals not computed to closed form in this test file. -/
theorem cma_cx :
    ∃ _ _ : ℝ, (DiscreteLaw.condMeanAtomize p0.toProbDist 2 (by norm_num)).ConvexOrder
      (DiscreteLaw.condMeanAtomize q3.toProbDist 2 (by norm_num)) := by
  obtain ⟨a, b, hcx⟩ := cx_to_icc
  exact ⟨a, b, DiscreteLaw.condMeanAtomize_convexOrder hcx 2 (by norm_num)⟩

/-! ## The weak-limit martingale transfer -/

/-- The canonical uniform spread law `½δ₋₁ + ½δ₊₁` and its δ₀-coupling, used to drive the
weak-limit theorem through a constant sequence. -/
private abbrev pd0 : DiscreteLaw := ⟨1, ![0], ![1], fun i => by fin_cases i; norm_num, by simp⟩

private abbrev qd2 : DiscreteLaw :=
  ⟨2, ![-1, 1], ![1 / 2, 1 / 2], fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]; norm_num⟩

private def Mspread : BistochasticMartingaleMatrix pd0 qd2 where
  T := ![![1 / 2, 1 / 2]]
  nonneg := by intro i j; fin_cases i; fin_cases j <;> norm_num
  row_sum := by intro i _; fin_cases i; simp [Fin.sum_univ_two]; norm_num
  mean_eq := by intro i _; fin_cases i; simp [Fin.sum_univ_two]
  col_marginal := by intro j; fin_cases j <;> simp

private theorem Mspread_supp_prod :
    Mspread.toProbDist.toMeasure (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = 1 := by
  rw [BistochasticMartingaleMatrix.toProbDist_toMeasure]
  simp only [Measure.add_apply, Measure.smul_apply,
    smul_eq_mul, Fin.sum_univ_one, Fin.sum_univ_two, pd0, qd2, Mspread, Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Measure.dirac_apply' _ (measurableSet_Icc.prod measurableSet_Icc),
    Set.indicator_of_mem (show ((0 : ℝ), (-1 : ℝ)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 by
      simp [Set.mem_Icc]),
    Set.indicator_of_mem (show ((0 : ℝ), (1 : ℝ)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 by
      simp [Set.mem_Icc])]
  simp only [Pi.one_apply, mul_one, one_mul]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

/-- **The weak-limit martingale transfer** (`tested_martingale_of_weak_limit`). Applied to the
constant sequence of the uniform δ₀/spread coupling (which trivially converges to itself), the
tested martingale identity `∫ (y - x)·φ(x) dπ = 0` is transported to the weak limit.

**What is tested:** The constant sequence `π_n = Mspread` is the simplest witness: the limit
is `Mspread` itself, so the transfer is a tautology (`const_tendsto_nhds`). This exercises the
`tested_martingale_of_weak_limit` API type-signature — not a genuine weak-limit approximation
of distinct couplings converging to a new limit. The deep content (passing the martingale identity
to a limit of genuinely distinct couplings) requires a separate non-constant sequence witness. -/
theorem weakLimit_witness (φ : ℝ → ℝ) (hφ : Continuous φ) (hbdd : ∃ M, ∀ x, |φ x| ≤ M) :
    ∫ p, (p.2 - p.1) * φ p.1 ∂Mspread.toProbDist.toMeasure = 0 :=
  tested_martingale_of_weak_limit (a := -1) (b := 1) (π_seq := fun _ => Mspread.toProbDist)
    (πInf := Mspread.toProbDist) (fun _ => Mspread_supp_prod) Mspread_supp_prod
    (fun _ ψ hψ hbd => Mspread.isMartingaleCoupling.martingale ψ hψ hbd)
    tendsto_const_nhds φ hφ hbdd

end EconlibTest.Probability.Order.StrassenGeneral

end
