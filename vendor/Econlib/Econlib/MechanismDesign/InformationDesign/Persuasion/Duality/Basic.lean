/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.FiniteFenchelMoreau
public import Econlib.Math.MeasureTheory.WeakConvergence.PortmanteauIntegral
public import Econlib.Optimization.OptimalTransport.CTransform
public import Econlib.Optimization.OptimalTransport.UpperLipschitzEnvelope
public import Econlib.Probability.ProbDist.Basic

/-!
# Persuasion duality: Primal and dual feasibility

Foundational definitions for the persuasion duality.  A sender's expected payoff under a
Bayes-plausible distribution of posteriors is captured by the *primal* value; its concave envelope
is captured by the *dual* problem over Lipschitz price functions majorizing the value. The two
values coincide under regularity (`StrongDuality`, `KRStrongDuality`).

## Main definitions

* `IsBayesPlausible` / `feasiblePrimal` — Bayes-plausibility of a distribution of posteriors.
* `primalValue` / `concaveClosure` — the primal objective and its supremum (value of (P)).
* `IsDualFeasible` / `feasibleDual` — Lipschitz majorants of the lifted objective.
* `dualObjective` / `dualValue` — the dual objective and its infimum (value of (D)).
* `IsSupergradient` / `IsSuperdifferentiable` — supporting Lipschitz prices at the prior.
* `HasBoundedSteepness` — KR-Lipschitz steepness of the value at the prior.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Section 2 (the primal and dual programs).

## Tags

persuasion, bayes plausibility, convex order, duality
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

/-! ## 1. Bayes plausibility and primal feasibility -/

section BayesPlausibility

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Bayes plausibility for a distribution of posteriors.

A distribution `τ` of posterior beliefs is Bayes-plausible relative to a prior `μ₀` when, for every
bounded continuous test function `f`, the average posterior expectation equals the prior
expectation:

`∫ (μ.expect f) dτ(μ) = μ₀.expect f`.

This formalizes `∫ μ dτ(μ) = μ₀` via duality with bounded continuous functions. When `Ω` is compact
the family `Cb(Ω, ℝ)` is separating, so this is equivalent to the set-by-set formulation
`∫ μ(B) dτ(μ) = μ₀(B)` for every Borel set `B`. -/
def IsBayesPlausible (μ₀ : ProbDist Ω) (τ : ProbDist (ProbDist Ω)) : Prop :=
  ∀ f : Ω →ᵇ ℝ,
    ∫ μ, ProbDist.expect μ f ∂τ.toMeasure = ProbDist.expect μ₀ f

/-- The set of Bayes-plausible distributions of posteriors — the feasible set `T(μ₀)` of the primal
problem `(P)`. -/
def feasiblePrimal (μ₀ : ProbDist Ω) : Set (ProbDist (ProbDist Ω)) :=
  {τ | IsBayesPlausible μ₀ τ}

end BayesPlausibility

/-! ## 2. Primal value and concave closure -/

section Primal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Primal payoff at a feasible distribution of posteriors: `primalValue V τ = ∫ V(μ) dτ(μ)`. -/
noncomputable def primalValue (V : ProbDist Ω → ℝ) (τ : ProbDist (ProbDist Ω)) : ℝ :=
  ∫ μ, V μ ∂τ.toMeasure

@[simp] lemma primalValue_def (V : ProbDist Ω → ℝ) (τ : ProbDist (ProbDist Ω)) :
    primalValue V τ = ∫ μ, V μ ∂τ.toMeasure := rfl

/-- Concave closure `V̂(μ₀)` of `V` at `μ₀`: Value of the primal problem `(P)`.

`V̂(μ₀) = sup { ∫ V(μ) dτ(μ) : τ ∈ T(μ₀) }`. -/
noncomputable def concaveClosure [TopologicalSpace Ω] (V : ProbDist Ω → ℝ) (μ₀ : ProbDist Ω) : ℝ :=
  sSup {y : ℝ | ∃ τ ∈ feasiblePrimal μ₀, y = primalValue V τ}

end Primal

/-! ## 3. Dual feasibility and the dual value -/

section Dual

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- A real-valued price function `p : Ω → ℝ` is dual-feasible for the objective `V` when

* `p` is Lipschitz (with some Lipschitz constant) — so `p ∈ Lip(Ω)`;
* `p` majorizes the linearized objective: `V μ ≤ μ.expect p` for every probability `μ`.

The space `Lip(Ω)` is dual to `M(Ω)` under the Kantorovich–Rubinstein norm (Hanin 1992, Bogachev
2007 Ex. 8.10.143), and the second condition is the affine-majorant constraint of `(D)`. -/
structure IsDualFeasible (V : ProbDist Ω → ℝ) (p : Ω → ℝ) : Prop where
  /-- `p` is Lipschitz with some constant `K`. -/
  lipschitz : ∃ K : NNReal, LipschitzWith K p
  /-- `p` majorizes the value at every probability law. -/
  majorizes : ∀ μ : ProbDist Ω, V μ ≤ ProbDist.expect μ p

/-- Dual objective at a price function: `∫ p dμ₀`. -/
noncomputable def dualObjective (μ₀ : ProbDist Ω) (p : Ω → ℝ) : ℝ :=
  ProbDist.expect μ₀ p
omit [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] in
@[simp] lemma dualObjective_def (μ₀ : ProbDist Ω) (p : Ω → ℝ) :
    dualObjective μ₀ p = ProbDist.expect μ₀ p := rfl

/-- The set of dual-feasible price functions: The set `P(V)` of the dual problem `(D)`. -/
def feasibleDual (V : ProbDist Ω → ℝ) : Set (Ω → ℝ) :=
  {p | IsDualFeasible V p}

/-- Coerce a Lipschitz function on a compact pseudometric space to a bounded continuous function. -/
noncomputable def lipschitzToBounded [CompactSpace Ω]
    {p : Ω → ℝ} (hp : ∃ K : NNReal, LipschitzWith K p) : Ω →ᵇ ℝ :=
  haveI hcont : Continuous p := by
    obtain ⟨_, hK⟩ := hp
    exact hK.continuous
  BoundedContinuousFunction.mkOfCompact ⟨p, hcont⟩

omit [MeasurableSpace Ω] [OpensMeasurableSpace Ω] in
@[simp] lemma lipschitzToBounded_apply [CompactSpace Ω]
    {p : Ω → ℝ} (hp : ∃ K : NNReal, LipschitzWith K p) (x : Ω) :
  (lipschitzToBounded hp) x = p x := rfl

/-- Dual value `V̄(μ₀)` of `V` at `μ₀`: Value of the dual problem `(D)`.

`V̄(μ₀) = inf { ∫ p dμ₀ : p ∈ P(V) }`.

The name "envelope" is reserved for the 1-D
`Econlib.Math.Analysis.Concavification1D.concaveEnvelope`, a different object. -/
noncomputable def dualValue (V : ProbDist Ω → ℝ) (μ₀ : ProbDist Ω) : ℝ :=
  sInf {y : ℝ | ∃ p ∈ feasibleDual V, y = dualObjective μ₀ p}

end Dual

/-! ## 4. Supergradients and bounded steepness -/

section Supergradient

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- A Lipschitz price `p` is a supergradient of `V̂` at `μ₀` when it supports `V̂` at `μ₀`:

* `p` is a Lipschitz price on the state space;
* the supporting affine functional is tight at `μ₀`;
* it lies above `V̂` at every posterior law. -/
structure IsSupergradient (Vhat : ProbDist Ω → ℝ) (μ₀ : ProbDist Ω)
    (p : Ω → ℝ) : Prop where
  /-- Supergradients live in `Lip(Ω)`. -/
  lipschitz : ∃ K : NNReal, LipschitzWith K p
  /-- The supporting hyperplane is tight at the prior. -/
  value_eq : Vhat μ₀ = ProbDist.expect μ₀ p
  /-- The supporting hyperplane dominates `V̂` globally. -/
  majorizes : ∀ μ : ProbDist Ω, Vhat μ ≤ ProbDist.expect μ p

/-- `V̂` is superdifferentiable at `μ₀` if it has a Lipschitz supporting price. -/
def IsSuperdifferentiable (Vhat : ProbDist Ω → ℝ) (μ₀ : ProbDist Ω) : Prop :=
  ∃ p : Ω → ℝ, IsSupergradient Vhat μ₀ p

/-- Bounded steepness of `V̂` at `μ₀`, measured in the KR norm.

In compact Hausdorff metrizable settings, `krDist μ μ₀ = 0` implies `μ = μ₀`, so the denominator is
positive whenever the hypothesis `μ ≠ μ₀` is available. -/
def HasBoundedSteepness (Vhat : ProbDist Ω → ℝ) (μ₀ : ProbDist Ω) (L : ℝ) : Prop :=
  ∀ μ : ProbDist Ω, μ ≠ μ₀ → (Vhat μ - Vhat μ₀) / krDist μ μ₀ ≤ L

end Supergradient

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
