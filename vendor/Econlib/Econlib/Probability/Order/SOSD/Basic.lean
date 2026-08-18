/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.FOSD.Basic

/-!
# Second-order stochastic dominance on `ProbDist`

`SOSD μ ν` is the canonical **second-order stochastic dominance** relation on `ProbDist ℝ` — the
`n = 2` specialization of the general nth-order relation `CDF.NOSD`/`NOSD` defined in the sibling
core file `Order/Core/Basic.lean`. `CDF.SOSD` is definitionally `CDF.NOSD 2`: It bundles the
integrated-CDF inequality `IntegratedCDFTower 2 F G` with the lower-tail integrability witnesses
(`IntegrableTailsUpTo 2`, equivalently `CDF.IntegrableTails`), so the relation cannot be satisfied
vacuously via the Bochner junk value `0` on an infinite-`E[X⁻]` law (Hadar and Russell 1969; Hanoch
and Levy 1969; Rothschild and Stiglitz 1970).

## Main definitions

* `CDF.SOSD` — second-order stochastic dominance at the CDF level.
* `SOSD` — the user-facing relation on `ProbDist ℝ`.

## Main statements

* `nosd_two_iff` — `NOSD 2 ↔ SOSD` (definitional).
* `nosd_one_iff` — `NOSD 1 ↔ FOSD`.
* `CDF.SOSD.of_integratedCDFTower_one` — first-order dominance plus integrable tails implies
  second-order dominance.

## Notes

The two bridges `nosd_two_iff` and `nosd_one_iff` live here because they must see both `FOSD` and
`SOSD`.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.
* Hanoch, G., and H. Levy. 1969. “The Efficiency Analysis of Choices Involving Risk.” *The Review
  of Economic Studies* 36 (3): 335–46. [https://doi.org/10.2307/2296431](https://doi.org/10.2307/2296431).
* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

second-order stochastic dominance, sosd, increasing risk, concave order
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Econlib

/-- **Second-order stochastic dominance at the CDF level** — the analytic engine, defined as the
order-`2` instance of `CDF.NOSD`. Bundles the integrated-CDF inequality `IntegratedCDFTower 2 F G`
with the lower-tail integrability witnesses (`IntegrableTailsUpTo 2`, equivalently
`CDF.IntegrableTails`) so the comparison is always between finite partial integrals rather than the
Bochner junk value `0`. -/
def CDF.SOSD (F G : CDF) : Prop :=
  CDF.NOSD 2 F G

namespace CDF.SOSD

/-- The dominated CDF has integrable lower tails. -/
lemma tails_left {F G : CDF} (h : CDF.SOSD F G) : F.IntegrableTails :=
  (CDF.integrableTailsUpTo_two F).mp (CDF.NOSD.tails_left h)

/-- The dominating CDF has integrable lower tails. -/
lemma tails_right {F G : CDF} (h : CDF.SOSD F G) : G.IntegrableTails :=
  (CDF.integrableTailsUpTo_two G).mp (CDF.NOSD.tails_right h)

/-- The underlying integrated-CDF inequality. -/
lemma dominance {F G : CDF} (h : CDF.SOSD F G) : IntegratedCDFTower 2 F G :=
  CDF.NOSD.tower h

/-- Assemble `CDF.SOSD` from the tail witnesses and the integrated-CDF inequality. -/
lemma mk' {F G : CDF} (hF : F.IntegrableTails) (hG : G.IntegrableTails)
    (h : IntegratedCDFTower 2 F G) : CDF.SOSD F G :=
  ⟨(CDF.integrableTailsUpTo_two F).mpr hF, (CDF.integrableTailsUpTo_two G).mpr hG, h⟩

/-- Reflexivity: A CDF with integrable lower tails second-order dominates itself. -/
lemma refl {F : CDF} (hF : F.IntegrableTails) : CDF.SOSD F F :=
  CDF.SOSD.mk' hF hF (IntegratedCDFTower.refl 2 F)

/-- Transitivity of `CDF.SOSD`. -/
lemma trans {F G H : CDF} (h1 : CDF.SOSD F G) (h2 : CDF.SOSD G H) : CDF.SOSD F H :=
  CDF.SOSD.mk' h1.tails_left h2.tails_right
    (IntegratedCDFTower.trans h1.dominance h2.dominance)

end CDF.SOSD

/-- **Second-order stochastic dominance** on `ProbDist ℝ`: The canonical user-facing relation,
defined as the CDF-level `CDF.SOSD` of the associated CDFs (so the lower-tail finiteness witnesses
are folded in). Definitionally `NOSD 2`. -/
def SOSD (μ ν : ProbDist ℝ) : Prop :=
  CDF.SOSD (CDF.ofProbDist μ) (CDF.ofProbDist ν)

namespace SOSD

/-- The dominated law has integrable lower tails. -/
lemma tails_left {μ ν : ProbDist ℝ} (h : SOSD μ ν) : (CDF.ofProbDist μ).IntegrableTails :=
  CDF.SOSD.tails_left h

/-- The dominating law has integrable lower tails. -/
lemma tails_right {μ ν : ProbDist ℝ} (h : SOSD μ ν) : (CDF.ofProbDist ν).IntegrableTails :=
  CDF.SOSD.tails_right h

/-- The underlying integrated-CDF inequality. -/
lemma dominance {μ ν : ProbDist ℝ} (h : SOSD μ ν) :
    IntegratedCDFTower 2 (CDF.ofProbDist μ) (CDF.ofProbDist ν) :=
  CDF.SOSD.dominance h

/-- Reflexivity: A law with integrable lower tails second-order dominates itself. -/
lemma refl {μ : ProbDist ℝ} (hμ : (CDF.ofProbDist μ).IntegrableTails) : SOSD μ μ :=
  CDF.SOSD.refl hμ

/-- Transitivity of `SOSD`. -/
lemma trans {μ ν ρ : ProbDist ℝ} (h1 : SOSD μ ν) (h2 : SOSD ν ρ) : SOSD μ ρ :=
  CDF.SOSD.trans h1 h2

end SOSD

/-- `NOSD 2` is definitionally the canonical second-order relation `SOSD`. -/
@[simp] lemma nosd_two_iff (μ ν : ProbDist ℝ) : NOSD 2 μ ν ↔ SOSD μ ν := Iff.rfl

/-- `NOSD 1` is first-order stochastic dominance: At order `1` the tower witnesses are vacuous and
the bare inequality `IntegratedCDFTower 1` is exactly `FOSD` (via
`fosd_iff_integratedCDFTower_one`). -/
lemma nosd_one_iff (μ ν : ProbDist ℝ) : NOSD 1 μ ν ↔ FOSD μ ν := by
  rw [NOSD, fosd_iff_integratedCDFTower_one]
  refine ⟨fun h => h.tower, fun h => CDF.NOSD.mk' ?_ ?_ h⟩ <;>
    simp [CDF.integrableTailsUpTo_one]

/-- If `F` first-order dominates `G` (`IntegratedCDFTower 1`) and `G` has integrable lower tails,
then `F` second-order dominates `G` at the CDF level. -/
lemma CDF.SOSD.of_integratedCDFTower_one {F G : CDF} (h : IntegratedCDFTower 1 F G)
    (hG : G.IntegrableTails) : CDF.SOSD F G := by
  refine CDF.SOSD.mk' ?_ hG (IntegratedCDFTower.step (n := 0) h hG)
  -- `F.IntegrableTails`: `0 ≤ F ≤ G` pointwise and `G` is integrable on each `Iic x`.
  intro x
  refine (hG x).mono' F.mono.measurable.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (F.range t).1]
  exact h t

end Econlib.Probability
