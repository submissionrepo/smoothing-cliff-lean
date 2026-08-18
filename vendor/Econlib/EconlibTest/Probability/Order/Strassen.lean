/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Strassen / Convex-Order Non-Vacuity Checks

Compile-time semantic witnesses for the discrete Strassen layer
(`Econlib.Probability.Order.Strassen`). The anchor is the canonical mean-preserving spread:

* `p0 = δ₀` — a point mass at `0`;
* `q2 = ½·δ₋₁ + ½·δ₊₁` — a two-point spread with the **same mean** `0` but strictly larger
  dispersion.

The `1 × 2` bistochastic martingale matrix `T = (½, ½)` transports `p0` to `q2`, so by Strassen the
point mass is below the two-point law in the convex order. The martingale **mean preservation**
(`E_p[id] = E_q[id]`) and the convex-order direction (`E_p[x²] = 0 ≤ 1 = E_q[x²]`) are the
orientation-critical spots — a reversed order or a non-mean-preserving "spread" would break them.
-/

noncomputable section

namespace EconlibTest.Probability.Order.Strassen

open Econlib.Probability MeasureTheory Set

/-- The point mass `δ₀` as a `DiscreteLaw` (reducible, so its projections unfold in sum binders). -/
private abbrev p0 : DiscreteLaw :=
  ⟨1, ![0], ![1], fun i => by fin_cases i; norm_num, by simp⟩

/-- The two-point spread `½·δ₋₁ + ½·δ₊₁` as a `DiscreteLaw`. -/
private abbrev q2 : DiscreteLaw :=
  ⟨2, ![-1, 1], ![1 / 2, 1 / 2], fun i => by fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_two]; norm_num⟩

/-- The `1 × 2` bistochastic martingale matrix `T = (1/2, 1/2)` transporting `δ₀` to the spread. -/
private def M : BistochasticMartingaleMatrix p0 q2 where
  T := ![![1 / 2, 1 / 2]]
  nonneg := by intro i j; fin_cases i; fin_cases j <;> norm_num
  row_sum := by intro i _; fin_cases i; simp [Fin.sum_univ_two]; norm_num
  mean_eq := by intro i _; fin_cases i; simp [Fin.sum_univ_two]
  col_marginal := by intro j; fin_cases j <;> simp

section means

/-- **Same mean (point mass):** `mean(δ₀) = 0`. -/
theorem p0_mean : p0.mean = 0 := by simp [DiscreteLaw.mean]

/-- **Same mean (spread):** `mean(½δ₋₁ + ½δ₊₁) = 0` — the spread is mean-preserving. -/
theorem q2_mean : q2.mean = 0 := by simp [DiscreteLaw.mean, Fin.sum_univ_two]

/-- **`id`-expectation of point mass is 0** — independent check via `expect_id_eq_mean`. -/
theorem p0_expect_id : p0.toProbDist.expect id = 0 := by
  rw [DiscreteLaw.expect_id_eq_mean]; exact p0_mean

/-- **`id`-expectation of spread is 0** — independent check via `expect_id_eq_mean`. -/
theorem q2_expect_id : q2.toProbDist.expect id = 0 := by
  rw [DiscreteLaw.expect_id_eq_mean]; exact q2_mean

end means

section coupling

/-- Both laws are supported on `[-1, 1]`. -/
private theorem p0_supp : p0.toProbDist.supportsOn (Icc (-1) 1) :=
  p0.toProbDist_supportsOn_of_atoms_mem measurableSet_Icc
    (fun i => by fin_cases i; simp [Set.mem_Icc])

private theorem q2_supp : q2.toProbDist.supportsOn (Icc (-1) 1) :=
  q2.toProbDist_supportsOn_of_atoms_mem measurableSet_Icc
    (fun i => by fin_cases i <;> simp [Set.mem_Icc])

/-- **The bistochastic martingale matrix assembles into a genuine martingale coupling** with the
prescribed marginals. -/
theorem isMartingaleCoupling_witness :
    IsMartingaleCoupling p0.toProbDist q2.toProbDist M.toProbDist :=
  M.isMartingaleCoupling

/-- **Martingale mean preservation:** the coupling forces equal first moments,
`E_{δ₀}[id] = E_{spread}[id]`. Re-derivable from `p0_expect_id` and `q2_expect_id` (both = 0). -/
theorem coupling_mean_eq : p0.toProbDist.expect id = q2.toProbDist.expect id :=
  M.isMartingaleCoupling.mean_eq

/-- **`x²`-expectation of point mass is 0.** Hand-check: `E_{δ₀}[x²] = 1·0² = 0`. -/
theorem p0_expect_sq : p0.toProbDist.expect (fun x => x ^ 2) = 0 := by
  rw [DiscreteLaw.expect_eq p0 (by fun_prop)]
  simp

/-- **`x²`-expectation of spread is 1.** Hand-check: `E[x²] = ½·(-1)² + ½·1² = ½ + ½ = 1`. -/
theorem q2_expect_sq : q2.toProbDist.expect (fun x => x ^ 2) = 1 := by
  rw [DiscreteLaw.expect_eq q2 (by fun_prop)]
  simp [Fin.sum_univ_two]; norm_num

/-- **Strict dispersion gap.** `E_{δ₀}[x²] = 0 < 1 = E_{spread}[x²]` — confirms the convex-order
direction is strict (not an equality), so both laws are genuinely distinct. -/
theorem p0_expect_sq_lt_q2 : p0.toProbDist.expect (fun x => x ^ 2) <
    q2.toProbDist.expect (fun x => x ^ 2) := by
  rw [p0_expect_sq, q2_expect_sq]; norm_num

/-- **Convex-order direction.** A convex payoff is worth weakly *more* under the spread:
`E_{δ₀}[x²] = 0 ≤ 1 = E_{spread}[x²]`. A reversed order would fail this. -/
theorem coupling_convex_expect_le :
    p0.toProbDist.expect (fun x => x ^ 2) ≤ q2.toProbDist.expect (fun x => x ^ 2) :=
  M.isMartingaleCoupling.convex_expect_le p0_supp q2_supp (fun x => x ^ 2)
    ((even_two.convexOn_pow).subset (Set.subset_univ _) (convex_Icc _ _))
    ((continuous_pow 2).continuousOn)

/-- **Easy-direction witness (constructed martingale coupling ⇒ convex order on `[-1,1]`).** This
checks that the `BistochasticMartingaleMatrix` API correctly assembles `δ₀ ⪯_cx spread` via the
martingale coupling `M`. It exercises only the forward direction of Strassen's theorem (coupling
⇒ convex order), not the full equivalence (convex order ⇒ coupling) which is in `Strassen.lean`
via `exists_mart`. -/
theorem coupling_convexOrderOnIcc :
    ConvexOrderOnIcc (-1) 1 p0.toProbDist q2.toProbDist :=
  M.isMartingaleCoupling.convexOrderOnIcc p0_supp q2_supp

end coupling

end EconlibTest.Probability.Order.Strassen

end
