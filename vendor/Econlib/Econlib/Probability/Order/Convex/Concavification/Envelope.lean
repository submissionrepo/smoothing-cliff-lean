/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.Envelope
public import Econlib.Probability.Order.Convex.Concavification.Defs

/-!
# Concave-envelope expectation bounds

Probability layer over the pure **concave envelope** core
(`Econlib.Math.Analysis.Concavification1D.Envelope`). The core expectation bound: Any distribution
supported on `[a, b]` has `φ`-expectation bounded above by the concave envelope evaluated at the
mean. This drives the concavification value characterization of Bayesian persuasion (Kamenica and
Gentzkow 2011).

## Main statements

* `ProbDist.expect_id_mem_Icc_of_supportsOn` — the mean of a supported distribution is in `[a, b]`.
* `expect_le_concaveEnvelope_of_supportsOn_Icc`, `expect_le_concaveEnvelope_of_convexOrderOnIcc` —
  the concave-envelope expectation bound.
* `exists_twoPointLaw_expect_eq_twoPointValue` — the two-point supremum is attained by a concrete
  two-point law.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

concave envelope, concavification, expectation bound, convex order, two-point law, persuasion
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- The mean of a distribution supported on `[a, b]` lies in `[a, b]`. -/
lemma ProbDist.expect_id_mem_Icc_of_supportsOn
    -- `hab` is unused in the proof (only `hsupp` is needed) but kept to match the
    -- call sites' natural hypothesis set and the theorem's intended reading.
    {d : ProbDist ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hsupp : d.supportsOn (Icc a b)) :
    d.expect id ∈ Icc a b := by
  have hid : Integrable id d.toMeasure :=
    ProbDist.integrable_id_of_supportsOn_Icc hsupp
  have hae : ∀ᵐ x ∂d.toMeasure, x ∈ Icc a b :=
    ProbDist.ae_mem_of_supportsOn measurableSet_Icc hsupp
  have hprob : IsProbabilityMeasure d.toMeasure := d.2
  have h_lo : a ≤ d.expect id := by
    have h1 : (∫ _x, a ∂d.toMeasure) = a := by simp
    rw [show d.expect id = ∫ x, x ∂d.toMeasure from rfl, ← h1]
    refine integral_mono_ae (integrable_const a) hid ?_
    filter_upwards [hae] with x hx using hx.1
  have h_hi : d.expect id ≤ b := by
    have h2 : (∫ _x, b ∂d.toMeasure) = b := by simp
    rw [show d.expect id = ∫ x, x ∂d.toMeasure from rfl, ← h2]
    refine integral_mono_ae hid (integrable_const b) ?_
    filter_upwards [hae] with x hx using hx.2
  exact ⟨h_lo, h_hi⟩

/-- **Core expectation bound.** Any distribution supported on `[a, b]` has `φ`-expectation bounded
above by the concave envelope evaluated at the mean. -/
theorem expect_le_concaveEnvelope_of_supportsOn_Icc
    {d : ProbDist ℝ} {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hsupp : d.supportsOn (Icc a b))
    (hφ : Continuous φ) :
    d.expect φ ≤ concaveEnvelope a b φ (d.expect id) := by
  have hmean : d.expect id ∈ Icc a b :=
    ProbDist.expect_id_mem_Icc_of_supportsOn hab hsupp
  obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ.continuousOn
  refine le_csInf ⟨m₀ * d.expect id + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩ ?_
  rintro y ⟨m, c, hm, rfl⟩
  have hbound :
      d.expect φ ≤ affineFun m c (d.expect id) :=
    expect_le_affineFun_of_supportsOn_Icc hsupp hm hφ
  simpa [affineFun] using hbound

/-- Convex-order version of the core bound: If `ν ≼cx[a,b] μ`, then `ν`'s `φ`-expectation is
bounded by the concave envelope evaluated at `μ`'s mean. -/
theorem expect_le_concaveEnvelope_of_convexOrderOnIcc
    {a b : ℝ} (hab : a ≤ b) {ν μ : ProbDist ℝ}
    (hcx : ConvexOrderOnIcc a b ν μ) {φ : ℝ → ℝ}
    (hφ : Continuous φ) :
    ν.expect φ ≤ concaveEnvelope a b φ (μ.expect id) := by
  have hmean_eq : μ.expect id = ν.expect id := hcx.mean_eq.symm
  have hmean : μ.expect id ∈ Icc a b := by
    rw [hmean_eq]
    exact ProbDist.expect_id_mem_Icc_of_supportsOn hab hcx.support_left
  obtain ⟨m₀, c₀, hm₀⟩ := exists_affineMajorant_of_continuousOn hab hφ.continuousOn
  refine le_csInf ⟨m₀ * μ.expect id + c₀, ⟨m₀, c₀, hm₀, rfl⟩⟩ ?_
  rintro y ⟨m, c, hm, rfl⟩
  have hbound :
      ν.expect φ ≤ affineFun m c (μ.expect id) :=
    expect_le_affineFun_of_convexOrderOnIcc hcx hm hφ
  simpa [affineFun] using hbound

/-- Optimizer-existence theorem in `twoPointValue` form: There is a concrete `twoPointLaw` whose
`φ`-expectation equals the two-point value at `μ`. -/
theorem exists_twoPointLaw_expect_eq_twoPointValue
    -- `hab` is unused in the proof (`hμ : μ ∈ Icc a b` already forces `a ≤ b`) but kept so
    -- the hypothesis set matches the sibling bound theorems above.
    {a b : ℝ} (_hab : a ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {μ : ℝ} (hμ : μ ∈ Icc a b) :
    ∃ (xL xR q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      xL ∈ Icc a b ∧ xR ∈ Icc a b ∧
      (1 - q) * xL + q * xR = μ ∧
      (twoPointLaw q xL xR hq0 hq1).expect φ = twoPointValue a b φ μ := by
  obtain ⟨⟨xL, xR, q⟩, hmem, hmax⟩ := exists_twoPointOptimum hφ hμ
  have hxL : xL ∈ Icc a b := hmem.1
  have hxR : xR ∈ Icc a b := hmem.2.1
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := hmem.2.2.1
  have hmean : (1 - q) * xL + q * xR = μ := hmem.2.2.2
  refine ⟨xL, xR, q, hq_mem.1, hq_mem.2, hxL, hxR, hmean, ?_⟩
  -- The value `twoPointValue a b φ μ` is the sup; `hmax` says our point attains it.
  -- The optimizer is the greatest value in the image, so it equals the sSup.
  have hgreatest :
      IsGreatest (twoPointObjective φ '' twoPointFeasibleSet a b μ)
        (twoPointObjective φ (xL, xR, q)) :=
    ⟨⟨(xL, xR, q), hmem, rfl⟩, by rintro v ⟨p, hp, rfl⟩; exact hmax hp⟩
  have hval : twoPointObjective φ (xL, xR, q) = twoPointValue a b φ μ :=
    hgreatest.csSup_eq.symm
  -- Bridge `twoPointLaw_expect` value to the objective.
  have hbridge :
      (twoPointLaw q xL xR hq_mem.1 hq_mem.2).expect φ = twoPointObjective φ (xL, xR, q) := by
    simpa [twoPointObjective] using twoPointLaw_expect q xL xR hq_mem.1 hq_mem.2 φ
  rw [hbridge, hval]

end Econlib.Probability
