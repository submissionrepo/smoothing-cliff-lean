/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Convex.Basic

/-!
# Persuasion on the line: The sender's objective and an optimality certificate

This file adds the objective and optimality layer to the convex-order ("posterior-mean law")
formulation of persuasion. A sender persuades a receiver whose action depends on the state only
through the posterior mean; a **signal** is a distribution `ν` of posterior means. It is feasible
exactly when it is a mean-preserving contraction of the prior `d`, i.e. `ConvexOrderOnIcc a b ν d`.
The sender's payoff is `ν.expect φ`.

The core result is a **convex-price optimality certificate** (Dworczak and Martini 2019): A
feasible signal `ν` is optimal whenever the objective `φ` admits a convex continuous majorant
`c ≥ φ` on `[a, b]` that is tight in expectation against the prior, `ν.expect φ = d.expect c`.

## Main definitions

* `IsFeasibleSignal` — a posterior-mean law is feasible iff it is a mean-preserving contraction of
  the prior.
* `IsOptimalSignal` — a feasible signal maximizes the sender's expected payoff `ν.expect φ`.

## Main statements

* `expect_mono_of_supportsOn` — support-aware monotonicity of `ProbDist.expect`.
* `isOptimalSignal_of_convexMajorant` — the convex-price optimality certificate.

## Notes

The certificate is the constrained optimum over `{ν : ν ≼cx[a,b] d}`. The one-dimensional concave
envelope `concaveEnvelope` evaluated at the prior mean is a generally-slack upper bound by
comparison.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, bayes plausibility, convex order, optimal signal, concavification
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

open Econlib.Probability

variable {a b : ℝ}

/-- A posterior-mean law `ν` is a **feasible signal** relative to the prior `d` when it is a
mean-preserving contraction of `d` on `[a, b]`. By the Blackwell–Strassen realization
`isFeasibleSignal_iff_exists_experiment` this is equivalent to `ν` being the posterior-mean law of
an actual Bayes-plausible experiment, so the optimality certificates below range over genuine
signal structures. -/
def IsFeasibleSignal (a b : ℝ) (d ν : ProbDist ℝ) : Prop := ConvexOrderOnIcc a b ν d

/-- The feasible signal `ν` is **optimal** for the sender objective `φ` when it maximizes the
expected payoff `ν.expect φ` over all feasible signals. -/
structure IsOptimalSignal (a b : ℝ) (d : ProbDist ℝ) (φ : ℝ → ℝ) (ν : ProbDist ℝ) : Prop where
  /-- The signal is feasible (Bayes-plausible on `[a, b]`). -/
  feasible : IsFeasibleSignal a b d ν
  /-- The signal maximizes the sender's expected payoff over all feasible signals. -/
  optimal : ∀ ν', IsFeasibleSignal a b d ν' → ν'.expect φ ≤ ν.expect φ

/-- Support-aware monotonicity of `ProbDist.expect`: A distribution supported on `[a, b]` respects
a pointwise inequality between continuous functions that holds on `[a, b]`. -/
lemma expect_mono_of_supportsOn {d : ProbDist ℝ} (hsupp : d.supportsOn (Icc a b))
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    d.expect f ≤ d.expect g := by
  have hf_int : Integrable f d.toMeasure := d.integrable_of_supportsOn_Icc hsupp hf
  have hg_int : Integrable g d.toMeasure := d.integrable_of_supportsOn_Icc hsupp hg
  have hae : ∀ᵐ x ∂d.toMeasure, f x ≤ g x := by
    filter_upwards [d.ae_mem_of_supportsOn measurableSet_Icc hsupp] with x hx
    exact hfg x hx
  exact integral_mono_ae hf_int hg_int hae

/-- **Convex-price optimality certificate** (Dworczak and Martini 2019). A feasible signal `ν` is
optimal for `φ` whenever there is a convex continuous function `c` on `[a, b]` that majorizes `φ`
(`φ ≤ c`) and is tight in expectation against the prior (`ν.expect φ = d.expect c`). -/
theorem isOptimalSignal_of_convexMajorant {d ν : ProbDist ℝ} {φ c : ℝ → ℝ}
    (hfeas : IsFeasibleSignal a b d ν)
    (hc_cvx : ConvexOn ℝ (Icc a b) c) (hc_cont : ContinuousOn c (Icc a b))
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hc_ge : ∀ x ∈ Icc a b, φ x ≤ c x)
    (htight : ν.expect φ = d.expect c) :
    IsOptimalSignal a b d φ ν := by
  refine ⟨hfeas, fun ν' hν' => ?_⟩
  have hcx' : ConvexOrderOnIcc a b ν' d := hν'
  calc ν'.expect φ
      ≤ ν'.expect c := expect_mono_of_supportsOn hcx'.support_left hφ_cont hc_cont hc_ge
    _ ≤ d.expect c := hcx'.convex_expect_le c hc_cvx hc_cont
    _ = ν.expect φ := htight.symm

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
