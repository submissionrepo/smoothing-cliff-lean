/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Binomial Tail Non-Vacuity Checks

These are compile-time semantic witnesses for the upper binomial tail API
(`Binomial/Tail/Basic.lean`), the binomial-expectation convexity engine
(`Binomial/Tail/Convexity.lean`), and the tail mixture identities (`Binomial/Tail/Mixture.lean`).
Concrete legal parameters check tail direction, threshold semantics, the CDF complement, the
convexity reading, and the mixture collapse so the statements cannot drift from
`Pr(X ≥ k)`.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.BinomialTail

open Econlib.Probability

section basic

/-- The upper tail `Pr(Bin(2, 1/4) ≥ 1) = 7/16`: the chance of at least one success, which is
`1 - Pr(= 0) = 1 - 9/16`. -/
theorem binomialTail_two_quarter_one :
    binomialTail 2 (1 / 4 : ℝ) 1 = 7 / 16 := by
  simp only [binomialTail, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

/-- The tail at threshold `0` is the full mass `1`. -/
theorem binomialTail_two_quarter_zero :
    binomialTail 2 (1 / 4 : ℝ) 0 = 1 :=
  binomialTail_zero 2 (1 / 4 : ℝ)

/-- The tail at the top threshold `n` is `p ^ n`: `Pr(Bin(2, 1/4) ≥ 2) = (1/4)^2 = 1/16`. -/
theorem binomialTail_two_quarter_two :
    binomialTail 2 (1 / 4 : ℝ) 2 = 1 / 16 := by
  rw [binomialTail_last]; norm_num

/-- The tail vanishes once the threshold exceeds `n`: `Pr(Bin(2, 1/4) ≥ 3) = 0`. -/
theorem binomialTail_two_quarter_three :
    binomialTail 2 (1 / 4 : ℝ) 3 = 0 :=
  binomialTail_large 2 (1 / 4 : ℝ) 3 (by norm_num)

/-- **Antitone in the threshold:** raising the bar lowers the tail probability,
`Pr(X ≥ 2) ≤ Pr(X ≥ 1)`. -/
theorem binomialTail_two_quarter_anti :
    binomialTail 2 (1 / 4 : ℝ) 2 ≤ binomialTail 2 (1 / 4 : ℝ) 1 :=
  binomialTail_anti_k (by norm_num) (by norm_num) 2 (by norm_num)

end basic

section monotonicityInP

/-- **Monotone in the success probability:** a more-likely-to-succeed coin has a larger tail,
`Pr(Bin(2, 1/4) ≥ 1) ≤ Pr(Bin(2, 1/2) ≥ 1)`. -/
theorem binomialTail_mono_p_quarter_half :
    binomialTail 2 (1 / 4 : ℝ) 1 ≤ binomialTail 2 (1 / 2 : ℝ) 1 :=
  binomialTail_mono_p (by norm_num) (by norm_num) (by norm_num) 2 1

/-- **Strictly monotone in the success probability** for an interior threshold `1 ≤ k ≤ n`:
`Pr(Bin(2, 1/4) ≥ 1) < Pr(Bin(2, 1/2) ≥ 1)`. -/
theorem binomialTail_strict_mono_p_quarter_half :
    binomialTail 2 (1 / 4 : ℝ) 1 < binomialTail 2 (1 / 2 : ℝ) 1 :=
  binomialTail_strict_mono_p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end monotonicityInP

section complement

/-- **CDF–tail complement:** `Pr(X ≤ 1) = 1 - Pr(X ≥ 2)`. The left side is `15/16` (from the
binomial CDF) and the right side is `1 - 1/16`, so the witness pins the `k+1` threshold shift. -/
theorem binomial_cdf_eq_one_sub_tail_two_quarter :
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).cdf (1 : Fin 3) =
      1 - binomialTail 2 (1 / 4 : ℝ) 2 := by
  simpa using
    FinDist.binomial_cdf_eq_one_sub_binomialTail (1 / 4 : ℝ) (by norm_num) (by norm_num) 2
      (1 : Fin 3)

/-- Sanity check on the complement: both sides of the previous witness equal `15/16`. -/
theorem binomial_cdf_one_sub_tail_value :
    1 - binomialTail 2 (1 / 4 : ℝ) 2 = 15 / 16 := by
  rw [binomialTail_two_quarter_two]; norm_num

/-- **Direct CDF witness:** `Bin(2, 1/4)` CDF at `1` is `15/16`, computed directly via the
binomial CDF formula (not via the tail complement). Masses: P(0) = 9/16, P(1) = 6/16,
P(2) = 1/16; CDF(1) = 9/16 + 6/16 = 15/16. This witnesses that the CDF unfolds correctly
at an interior point, independently of the complement identity. -/
theorem binomial_cdf_direct_two_quarter :
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).cdf (1 : Fin 3) = 15 / 16 := by
  rw [FinDist.binomial_cdf]
  norm_num [Finset.sum_range_succ, Nat.choose]

end complement

section pascal

/-- **Pascal recursion for the tail:**
`Pr(Bin(3, 1/4) ≥ 2) = (1-p)·Pr(Bin(2, 1/4) ≥ 2) + p·Pr(Bin(2, 1/4) ≥ 1)`. -/
theorem binomialTail_succ_succ_three_quarter :
    binomialTail 3 (1 / 4 : ℝ) 2 =
      (1 - 1 / 4) * binomialTail 2 (1 / 4 : ℝ) 2 + (1 / 4) * binomialTail 2 (1 / 4 : ℝ) 1 := by
  simpa using binomialTail_succ_succ 2 (1 / 4 : ℝ) 1

end pascal

section convexity

/-- The binomial expectation `E_{Bin(2,p)}[X]` evaluates to the mean `2p`: at `p = 1/4` it is
`1/2`. This checks that `binomialExpect` reads as a genuine expectation. -/
theorem binomialExpect_two_id_quarter :
    binomialExpect 2 (fun k => (k : ℝ)) (1 / 4) = 1 / 2 := by
  unfold binomialExpect
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Nat.choose]

/-- **Binomial expectation preserves convexity:** for the convex payoff `φ(k) = k²` (which has
nondecreasing differences), `p ↦ E_{Bin(2,p)}[φ(X)]` is convex on `[0, 1]`. -/
theorem binomialExpect_sq_convexOn :
    ConvexOn ℝ (Set.Icc 0 1) (binomialExpect 2 (fun k => (k : ℝ) ^ 2)) :=
  binomialExpect_convexOn 2 (fun k => (k : ℝ) ^ 2) (by intro k; dsimp only; push_cast; nlinarith)

end convexity

section mixture

/-- **Compound Bernoulli collapse:** a two-stage trial — activate with prob `1/2`, then succeed
with prob `1/2` — has overall success prob `1/4`, so the mixture over activations equals
`Pr(Bin(2, 1/4) ≥ 1) = 7/16`. -/
theorem binomialTail_compound_half_half :
    (∑ h ∈ Finset.range 3,
      (Nat.choose 2 h : ℝ) * (1 / 2) ^ h * (1 - 1 / 2) ^ (2 - h) *
        binomialTail h (1 / 2 : ℝ) 1) = 7 / 16 := by
  rw [binomialTail_compound 2 (1 / 2 : ℝ) (1 / 2 : ℝ) 1]
  norm_num [binomialTail, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose]

/-- **Asymmetric compound anchor:** two-stage process with activation `σ = 1/3` and conditional
success `π = 1/4`. Compound success probability = `σ·π = (1/3)·(1/4) = 1/12`. Result:
`Pr(Bin(2, 1/12) ≥ 1) = 1 − (1 − 1/12)² = 1 − (11/12)² = 1 − 121/144 = 23/144`.
The distinct parameters `σ ≠ π` discriminate a σ ↔ π transpose. -/
theorem binomialTail_compound_third_quarter :
    (∑ h ∈ Finset.range 3,
      (Nat.choose 2 h : ℝ) * (1 / 3) ^ h * (1 - 1 / 3) ^ (2 - h) *
        binomialTail h (1 / 4 : ℝ) 1) = 23 / 144 := by
  rw [binomialTail_compound 2 (1 / 3 : ℝ) (1 / 4 : ℝ) 1]
  norm_num [binomialTail, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose]

/-- **Tail mixture at a blended parameter:** the type mixture `Bern(1/2)` with conditional success
`1/2` blends to `z + (1-z)q = 3/4`, so the mixture equals `Pr(Bin(1, 3/4) ≥ 1) = 3/4`. -/
theorem binomialTail_mixture_half_half :
    (∑ h ∈ Finset.range 2,
      (Nat.choose 1 h : ℝ) * (1 / 2) ^ h * (1 - 1 / 2) ^ (1 - h) *
        binomialTail (1 - h) (1 / 2 : ℝ) (1 - h)) = 3 / 4 := by
  rw [binomialTail_mixture 1 (1 / 2 : ℝ) (1 / 2 : ℝ) 1]
  norm_num [binomialTail, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose]

/-- **Asymmetric mixture anchor:** type mixture `Bern(1/3)` with conditional success `q = 1/5`.
The blend formula is `z + (1-z)·q = 1/3 + (2/3)·(1/5) = 1/3 + 2/15 = 5/15 + 2/15 = 7/15`.
Result: `Pr(Bin(1, 7/15) ≥ 1) = 7/15`. The distinct values `z = 1/3 ≠ q = 1/5` discriminate a
z ↔ q transpose in the blend formula. -/
theorem binomialTail_mixture_third_fifth :
    (∑ h ∈ Finset.range 2,
      (Nat.choose 1 h : ℝ) * (1 / 3) ^ h * (1 - 1 / 3) ^ (1 - h) *
        binomialTail (1 - h) (1 / 5 : ℝ) (1 - h)) = 7 / 15 := by
  rw [binomialTail_mixture 1 (1 / 3 : ℝ) (1 / 5 : ℝ) 1]
  norm_num [binomialTail, Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose]

end mixture

end EconlibTest.Probability.Distributions.BinomialTail

end
