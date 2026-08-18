/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Basic
public import Econlib.Probability.ProbDist.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Moment persuasion: Setup

Moment persuasion is the regime where the sender's payoff depends on the posterior only through a
finite-dimensional moment

`m : Ω → ℝⁿ`,

valued in a compact convex set `X ⊆ ℝⁿ` of nonempty interior, with the value function `v : X → ℝ`
Lipschitz.  The set `X` is not merely a compact convex superset of the moment image: The
`MomentSetup` structure requires `X` to be exactly the achievable posterior-moment set
(`moment_surjOn_X`), so every `y ∈ X` is the posterior moment `∫ m dμ` of some posterior `μ`. Under
these assumptions the abstract persuasion problem reduces to optimizing a *joint* distribution on
`X × Ω` whose `Ω`-marginal is the prior and which satisfies a martingale condition
`E[m(ω) ∣ x] = x`.

This file packages the primitive objects of the moment model and defines the feasible joint set and
the primal value. The feasibility predicate records both Bayes plausibility and the martingale
moment constraint, so later optimality statements can quantify directly over feasible joints.

## Main definitions

* `MomentSetup` — moment dimension, moment map, compact convex moment image, prior.
* `IsFeasibleJoint` — Bayes-plausibility + martingale constraint on joints.
* `feasibleJoint` — the feasible joint set `Π(μ₀)`.
* `momentPrimal` — the primal value of the moment-persuasion problem.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Section 4.

## Tags

persuasion, moment persuasion, bayes plausibility, martingale
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

/-! ## 1. Moment setup

We work with a finite dimension `n` and the Euclidean space `EuclideanSpace ℝ (Fin n)` as the
moment range. The state space `Ω` is an arbitrary pseudometric measurable space; the moment map
`m : Ω → ℝⁿ` is continuous and takes values in a compact convex subset `X` with nonempty
interior. -/

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]

/-- Moment-persuasion setup.  Records:

* `n` — the moment dimension;
* `m : Ω → ℝⁿ` — the moment map (continuous, valued in `X`);
* `X` — a compact convex subset of `ℝⁿ` with nonempty interior that is *exactly* the achievable
  posterior-moment set: It contains every `m ω` (`m_mem_X`) and, conversely, every `y ∈ X` is the
  posterior moment of some posterior (`moment_surjOn_X`).  So `X` is the closed convex hull of the
  moment image, not merely some compact convex superset of it;
* `prior` — the Bayesian prior on `Ω`. -/
structure MomentSetup (Ω : Type*) (n : ℕ)
    [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω] where
  /-- Vector of moments `m(ω) ∈ ℝⁿ`. -/
  m : Ω → EuclideanSpace ℝ (Fin n)
  /-- The moment map is continuous, and a fortiori measurable. -/
  m_continuous : Continuous m
  /-- Compact convex moment image set. -/
  X : Set (EuclideanSpace ℝ (Fin n))
  /-- `X` is compact. -/
  X_compact : IsCompact X
  /-- `X` is convex. -/
  X_convex : Convex ℝ X
  /-- `X` has nonempty interior (so its dimension is `n`). -/
  X_interior : (interior X).Nonempty
  /-- Every state has its moment vector in `X`. -/
  m_mem_X : ∀ ω, m ω ∈ X
  /-- **Moment surjectivity.**  `X` is exactly the achievable moment set: Every `y ∈ X` is the
  posterior moment `∫ m dμ` of some posterior `μ`.  This is a feasibility/surjectivity condition
  strictly stronger than "`X` contains the moment image" — it restricts `X` to the closed convex
  hull of the moment image — and is carried as a field rather than a per-theorem hypothesis.
  Phrased with the raw integral because `posteriorMoment` is defined below; see
  `MomentSetup.feasible` for the `posteriorMoment` restatement, and `MomentSetup.ofMomentImage` for
  the canonical `X = conv(range m)` instance that discharges it. -/
  moment_surjOn_X : ∀ y ∈ X, ∃ μ : ProbDist Ω, (∫ ω, m ω ∂μ.toMeasure) = y
  /-- The prior distribution over `Ω`. -/
  prior : ProbDist Ω

namespace MomentSetup

variable {n : ℕ}

/-- The moment map is measurable. -/
lemma m_measurable (s : MomentSetup Ω n) : Measurable s.m :=
  s.m_continuous.measurable

/-- Posterior moment vector under a posterior `μ`:

`posteriorMoment μ = ∫ ω, m(ω) dμ(ω) ∈ ℝⁿ`.

This is the receiver-relevant statistic.  Under the assumption that `m ω ∈ X` for every `ω` and
that `X` is convex compact, this integral lies in `X`. -/
noncomputable def posteriorMoment (s : MomentSetup Ω n) (μ : ProbDist Ω) :
    EuclideanSpace ℝ (Fin n) :=
  ∫ ω, s.m ω ∂μ.toMeasure

/-- Feasibility / Bayes-plausibility restatement of the `moment_surjOn_X` field in terms of
`posteriorMoment`: Every `y ∈ s.X` is the posterior moment of some posterior.  This is the form the
pricing/duality theorems consume. -/
lemma feasible (s : MomentSetup Ω n) :
    ∀ y ∈ s.X, ∃ μ : ProbDist Ω, s.posteriorMoment μ = y :=
  s.moment_surjOn_X

/-- The composed sender value `V(μ) := v(E_μ[m])`. -/
noncomputable def composedValue (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ProbDist Ω) : ℝ :=
  v (s.posteriorMoment μ)

@[simp] lemma composedValue_def (s : MomentSetup Ω n) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (μ : ProbDist Ω) : s.composedValue v μ = v (s.posteriorMoment μ) := rfl

end MomentSetup

/-! ## 2. Joint formulation: Feasible joints and primal value

A *joint* is a probability measure `π` on `X × Ω` whose `Ω`-marginal is the prior `μ₀` and
which satisfies the martingale condition `E_π[m(ω) − x ∣ x] = 0`. -/

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]

/-- A joint distribution `π : ProbDist (ℝⁿ × Ω)` is *feasible* relative to `s` if its `Ω`-marginal
equals `s.prior`, its `ℝⁿ`-marginal is supported on `s.X`, and it satisfies the martingale
constraint `E_π[φ(x)(m(ω) − x)] = 0` for every bounded continuous `φ : ℝⁿ → ℝ`. -/
structure IsFeasibleJoint {n : ℕ} (s : MomentSetup Ω n)
    (π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) : Prop where
  /-- `Ω`-marginal recovers the prior. -/
  marginal : ProbDist.map π Prod.snd measurable_snd = s.prior
  /-- The first marginal lives inside `X`. -/
  fst_supportsOn :
    π.toMeasure (Prod.fst ⁻¹' s.X) = 1
  /-- Martingale constraint — tested form: For every bounded continuous `φ : ℝⁿ → ℝ` and every
  coordinate `i`, the inner-product test integral vanishes.  Equivalently
  `E_π[φ(x) (m(ω) − x)] = 0`. -/
  martingale :
    ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
        ∀ i : Fin n,
          ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure = 0

/-- Feasible-joint set `Π(μ₀)`. -/
def feasibleJoint {n : ℕ} (s : MomentSetup Ω n) :
    Set (ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :=
  {π | IsFeasibleJoint s π}

/-- Primal value of the moment-persuasion problem:

`momentPrimal v s = sup { ∫ v(x) dπ(x, ω) : π ∈ Π(μ₀) }`.

This is the joint-formulation analog of `concaveClosure`: `V̂(μ₀) = sup_{π ∈ Π(μ₀)} ∫ v(x) dπ`. -/
noncomputable def momentPrimal {n : ℕ} (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ π ∈ feasibleJoint s, y = ∫ p, v p.1 ∂π.toMeasure}

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
