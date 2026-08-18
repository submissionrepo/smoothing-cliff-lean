/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.LinearAlgebra.AggregateFunctional
public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.Markov.Ergodic
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbDist.Stationary

/-!
# Stationary laws and endogenous Markov kernels

This module defines policy-induced Markov dynamics in two layers. The **measure-valued layer**
(`MarkovKernel`) wraps a Mathlib measure-valued `Kernel` and packages stationary probability laws,
aggregation, event mass, compact-Feller existence, a uniqueness lemma for stationary laws, and
parameter-continuity certificates. The **finite-support layer** (`FiniteSupportKernel`,
`ControlledFiniteSupportKernel`) describes endogenous dynamics driven by finitely many shocks, with
expectations as finite sums, invariance stated by the Koopman identity, and reachable support sets
defined directly — useful before committing to a measure-theoretic representation.

## Main definitions

* `MarkovKernel Z` — a Markov kernel bundled as data, with `step`, `Invariant`, and `StationaryLaw`
* `MarkovKernel.StationaryLaw.law_eq_of_unique` — stationary laws coincide given a
  kernel-uniqueness hypothesis
* `FiniteSupportKernel Z Shock` — endogenous dynamics from a finite shock space, with `expect`,
  `successors`, `ClosedUnder`, `reachableFrom`, and `StationaryFunctional`
* `ControlledFiniteSupportKernel State Action Shock` — a controlled finite-support system, with
  `Policy` and `inducedKernel`

## Main statements

* `MarkovKernel.exists_stationary_of_feller` — existence of a stationary law for a Feller kernel on
  a compact metrizable space
* `MarkovKernel.exists_stationary_of_endogenousMarkovChain` — stationary existence for an
  `EndogenousMarkovChain` without an external Feller hypothesis
* `MarkovKernel.ofEndogenousMarkovChain_stationary_snd_marginal` — the `Prod.snd`-marginal of a
  product-space stationary law is stationary for the discrete chain
* `FiniteSupportKernel.closedUnder_iff_imageSet_subset`,
  `FiniteSupportKernel.reachableFrom_closedUnder` — characterization and closure of reachable sets

## Tags

markov kernel, stationary distribution, invariant measure, endogenous chain, policy, feller kernel
-/

@[expose] public section

open BigOperators MeasureTheory ProbabilityTheory Filter Topology

namespace Econlib.Probability

/-! ## Measure-valued Markov kernels and stationary laws -/

/-- A Markov kernel on a measurable state space, bundled as data rather than an instance.  The
local instance can be recovered with `letI := K.markov`. -/
structure MarkovKernel (Z : Type*) [MeasurableSpace Z] where
  /-- The transition kernel. -/
  kernel : Kernel Z Z
  /-- The kernel is Markov. -/
  markov : IsMarkovKernel kernel

namespace MarkovKernel

variable {Z : Type*} [MeasurableSpace Z]
variable (K : MarkovKernel Z)

/-- Invariance of a probability law under a Markov kernel. -/
def Invariant (μ : ProbDist Z) : Prop :=
  Kernel.Invariant K.kernel μ.toMeasure

/-- One-step push-forward of a probability law through the kernel. -/
noncomputable def step (μ : ProbDist Z) : ProbDist Z := by
  letI : IsMarkovKernel K.kernel := K.markov
  exact ⟨K.kernel ∘ₘ μ.toMeasure, inferInstance⟩

/-- Stationary probability law for a Markov kernel. -/
structure StationaryLaw where
  /-- The underlying probability law. -/
  law : ProbDist Z
  /-- Invariance under the kernel. -/
  invariant : K.Invariant law

namespace StationaryLaw

variable {K : MarkovKernel Z}
variable (π : K.StationaryLaw)

/-- Aggregate/integrate a real-valued function under a stationary law. -/
noncomputable def aggregate (f : Z → ℝ) : ℝ :=
  π.law.expect f

/-- Mass assigned to a measurable event. -/
noncomputable def eventMass (A : Set Z) : ENNReal :=
  π.law.toMeasure A

/-- The support predicate represented as full measure of a set. -/
def SupportsOn (A : Set Z) : Prop :=
  π.law.toMeasure A = 1

/-- Aggregation under a stationary law is the expectation under its underlying law. -/
@[simp] theorem aggregate_eq_expect (f : Z → ℝ) :
    π.aggregate f = π.law.expect f := rfl

/-- A stationary law assigns unit mass to the whole space. -/
@[simp] theorem eventMass_univ : π.eventMass Set.univ = 1 := by
  simp [eventMass]

/-- The kernel step leaves a stationary law fixed. -/
theorem invariant_step_eq : K.step π.law = π.law := by
  apply ProbabilityMeasure.toMeasure_injective
  exact π.invariant

end StationaryLaw

/-- A Feller kernel on a compact metrizable space admits a stationary law. -/
theorem exists_stationary_of_feller
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [BorelSpace Z] [Nonempty Z]
    (K : MarkovKernel Z)
    (hFeller :
      letI : IsMarkovKernel K.kernel := K.markov
      ProbabilityTheory.IsFellerKernel K.kernel) :
    ∃ π : K.StationaryLaw, K.Invariant π.law := by
  letI : IsMarkovKernel K.kernel := K.markov
  letI : ProbabilityTheory.IsFellerKernel K.kernel := hFeller
  obtain ⟨μ, hμ⟩ := exists_invariant_probDist K.kernel
  exact ⟨⟨μ, hμ⟩, hμ⟩

/-- Bridge `EndogenousMarkovChain` (a finite-shock × compact-interval chain with a continuous
policy) to the abstract `MarkovKernel` API.  The Markov-kernel property is inherited from
`EndogenousMarkovChain.toKernel_isMarkov`. -/
noncomputable def ofEndogenousMarkovChain {n : ℕ} (E : EndogenousMarkovChain n) :
    MarkovKernel (Set.Icc E.w_min E.w_max × Fin n) where
  kernel := E.toKernel
  markov := E.toKernel_isMarkov

/-- The underlying kernel of `ofEndogenousMarkovChain E` is `E.toKernel`. -/
@[simp] theorem ofEndogenousMarkovChain_kernel
    {n : ℕ} (E : EndogenousMarkovChain n) :
    (ofEndogenousMarkovChain E).kernel = E.toKernel := rfl

/-- **Stationary existence for `EndogenousMarkovChain`** without an external Feller hypothesis,
since the Krylov–Bogolyubov theorem applies to `EndogenousMarkovChain.toKernel_isFeller`. -/
noncomputable def stationaryLawOfEndogenousMarkovChain {n : ℕ} [NeZero n]
    (E : EndogenousMarkovChain n) :
    (ofEndogenousMarkovChain E).StationaryLaw :=
  let K := ofEndogenousMarkovChain E
  haveI : Nonempty (Set.Icc E.w_min E.w_max × Fin n) :=
    ⟨⟨⟨E.w_min, le_refl _, le_of_lt E.hw⟩, ⟨0, NeZero.pos n⟩⟩⟩
  haveI : IsMarkovKernel K.kernel := K.markov
  haveI : ProbabilityTheory.IsFellerKernel K.kernel := E.toKernel_isFeller
  ⟨(exists_invariant_probDist K.kernel).choose,
   (exists_invariant_probDist K.kernel).choose_spec⟩

/-- An `EndogenousMarkovChain` admits a stationary law, with no external Feller hypothesis. -/
theorem exists_stationary_of_endogenousMarkovChain {n : ℕ} [NeZero n]
    (E : EndogenousMarkovChain n) :
    ∃ π : (ofEndogenousMarkovChain E).StationaryLaw,
      (ofEndogenousMarkovChain E).Invariant π.law :=
  ⟨stationaryLawOfEndogenousMarkovChain E,
   (stationaryLawOfEndogenousMarkovChain E).invariant⟩

open MeasureTheory ProbabilityTheory Set in
/-- **The discrete marginal of a product-space stationary law is stationary for the discrete
chain.** The `Prod.snd`-pushforward of any stationary law `π` of the endogenous kernel
`ofEndogenousMarkovChain E` is a stationary distribution for the finite discrete chain
`⟨E.discrete_trans⟩`.

The deterministic policy moves only the continuous coordinate, so the kernel mass placed on a
discrete fiber `{s'}` is exactly the discrete transition weight `discrete_trans(s)(s')`,
independent of the continuous coordinate. -/
theorem ofEndogenousMarkovChain_stationary_snd_marginal {n : ℕ} [NeZero n]
    (E : EndogenousMarkovChain n)
    (π : (ofEndogenousMarkovChain E).StationaryLaw) :
    FiniteMarkovChain.IsStationary (⟨E.discrete_trans⟩ : FiniteMarkovChain (Fin n))
      ((π.law.map Prod.snd measurable_snd).toFinDist) := by
  classical
  set ν : Measure (Fin n) := Measure.map Prod.snd π.law.toMeasure with hν
  -- The kernel mass placed on a discrete fiber `{s'}` is the discrete transition weight; the
  -- deterministic policy only relocates the continuous coordinate, never the discrete one.
  have hkernel : ∀ (x : Icc E.w_min E.w_max × Fin n) (s' : Fin n),
      E.toKernel x (Prod.snd ⁻¹' ({s'} : Set (Fin n)))
        = ENNReal.ofReal ((E.discrete_trans x.2).pmf s') := by
    intro x s'
    have hA : MeasurableSet
        ((Prod.snd : Icc E.w_min E.w_max × Fin n → Fin n) ⁻¹' ({s'} : Set (Fin n))) :=
      measurable_snd (measurableSet_singleton s')
    change E.transitionMeasure x _ = _
    simp only [EndogenousMarkovChain.transitionMeasure, Measure.coe_finset_sum, Finset.sum_apply,
      Measure.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single s']
    · rw [Measure.dirac_apply_of_mem (by simp [Set.mem_preimage]), mul_one]
    · intro b _ hb
      rw [Measure.dirac_apply' _ hA,
        Set.indicator_of_notMem (by simp [Set.mem_preimage, hb]), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s') h
  -- Invariance, in `bind` form, as a measure identity on the product space.
  have hinv : π.law.toMeasure.bind E.toKernel = π.law.toMeasure := π.invariant
  -- Disintegrate the marginal mass along `Prod.snd`, in `ℝ≥0∞`.
  have hmass : ∀ s' : Fin n,
      ν {s'} = ∑ s, ENNReal.ofReal ((E.discrete_trans s).pmf s') * ν {s} := by
    intro s'
    -- Push the invariance identity onto the discrete fiber `{s'}` and integrate the kernel mass.
    have hstep : ν {s'}
        = ∫⁻ x, E.toKernel x (Prod.snd ⁻¹' ({s'} : Set (Fin n))) ∂π.law.toMeasure := by
      have hfold : π.law.toMeasure (Prod.snd ⁻¹' ({s'} : Set (Fin n)))
          = (π.law.toMeasure.bind E.toKernel) (Prod.snd ⁻¹' ({s'} : Set (Fin n))) := by
        rw [hinv]
      rw [hν, Measure.map_apply measurable_snd (measurableSet_singleton s'), hfold,
        Measure.bind_apply (measurable_snd (measurableSet_singleton s'))
          E.toKernel.measurable.aemeasurable]
    -- The integrand depends only on the discrete coordinate, so it pushes through `Prod.snd`.
    have hmap : (∫⁻ x, ENNReal.ofReal ((E.discrete_trans x.2).pmf s') ∂π.law.toMeasure)
        = ∫⁻ s, ENNReal.ofReal ((E.discrete_trans s).pmf s') ∂ν := by
      rw [hν, lintegral_map (measurable_of_finite _) measurable_snd]
    rw [hstep]
    simp_rw [hkernel]
    rw [hmap, lintegral_fintype]
  -- Translate the `ℝ≥0∞` identity to the real-valued stationarity equation.
  have hpmf : ∀ a : Fin n,
      (π.law.map Prod.snd measurable_snd).toFinDist.pmf a = (ν {a}).toReal := by
    intro a
    simp only [ProbDist.toFinDist, ProbDist.map_toMeasure, ← hν]
  rw [FiniteMarkovChain.isStationary_iff]
  intro s'
  -- The marginal mass identity, after `toReal`, with `ofReal` collapsed against nonnegativity.
  have key : (ν {s'}).toReal
      = ∑ s, (E.discrete_trans s).pmf s' * (ν {s}).toReal := by
    rw [hmass s', ENNReal.toReal_sum
      (fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν {s}))]
    exact Finset.sum_congr rfl fun s _ => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ((E.discrete_trans s).nonneg s')]
  change ∑ s : Fin n, (π.law.map Prod.snd measurable_snd).toFinDist.pmf s
        * (E.discrete_trans s).pmf s'
      = (π.law.map Prod.snd measurable_snd).toFinDist.pmf s'
  simp only [hpmf]
  rw [key]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

section Uniqueness

variable {K : MarkovKernel Z}

/-- Two stationary-law structures share the same underlying probability law whenever the kernel has
at most one invariant probability law.  Downstream comparative-statics results take the uniqueness
hypothesis directly — e.g. from `FiniteMarkovChain.unique_stationary` under Doeblin positivity —
and apply this lemma, rather than carrying a uniqueness certificate. -/
theorem StationaryLaw.law_eq_of_unique
    (huniq : ∀ μ ν : ProbDist Z, K.Invariant μ → K.Invariant ν → μ = ν)
    (π ρ : K.StationaryLaw) : π.law = ρ.law :=
  huniq π.law ρ.law π.invariant ρ.invariant

end Uniqueness

end MarkovKernel

/-! ## Finite-support endogenous kernels -/

/-- A Markov transition with finitely many shocks from an arbitrary state space.

For current state `z`, draw a shock `e` from `shock z`, then move to `next z e`.  This
representation covers policy-induced wealth/state dynamics where the exogenous shock space is
finite but the endogenous state need not be. -/
structure FiniteSupportKernel (Z : Type*) (Shock : Type*)
    [Fintype Shock] [DecidableEq Shock] where
  /-- Shock distribution at each current state. -/
  shock : Z → FinDist Shock
  /-- Next state as a deterministic function of the current state and shock. -/
  next : Z → Shock → Z

namespace FiniteSupportKernel

variable {Z : Type*} {Shock : Type*} [Fintype Shock] [DecidableEq Shock]
variable (K : FiniteSupportKernel Z Shock)

/-- One-step expectation operator `P f`. -/
noncomputable def expect (z : Z) (f : Z → ℝ) : ℝ :=
  (K.shock z).expect (fun e => f (K.next z e))

/-- The set of one-step successors reached with positive probability. -/
def successors (z : Z) : Set Z :=
  {z' | ∃ e : Shock, 0 < K.shock z e ∧ K.next z e = z'}

/-- A set is closed under the kernel if every positive-probability successor of any state in the
set remains in the set. -/
def ClosedUnder (A : Set Z) : Prop :=
  ∀ ⦃z : Z⦄, z ∈ A → ∀ e : Shock, 0 < K.shock z e → K.next z e ∈ A

/-- One-step image of a set under positive-probability transitions. -/
def imageSet (A : Set Z) : Set Z :=
  {z' | ∃ z ∈ A, z' ∈ K.successors z}

/-- `ClosedUnder` is equivalent to the one-step image being contained in the set. -/
theorem closedUnder_iff_imageSet_subset (A : Set Z) :
    K.ClosedUnder A ↔ K.imageSet A ⊆ A := by
  constructor
  · intro h z' hz'
    rcases hz' with ⟨z, hzA, e, he, rfl⟩
    exact h hzA e he
  · intro h z hzA e he
    exact h ⟨z, hzA, e, he, rfl⟩

/-- States reachable in exactly `n` steps from an initial state. -/
def reachableExact (z₀ : Z) : ℕ → Set Z
  | 0 => {z₀}
  | n + 1 => K.imageSet (reachableExact z₀ n)

/-- States reachable in finitely many steps from an initial state. -/
def reachableFrom (z₀ : Z) : Set Z :=
  {z | ∃ n : ℕ, z ∈ K.reachableExact z₀ n}

/-- The initial state is reachable from itself. -/
theorem start_mem_reachableFrom (z₀ : Z) : z₀ ∈ K.reachableFrom z₀ :=
  ⟨0, rfl⟩

/-- The finite-reachability set is forward closed under all positive-probability successors. -/
theorem reachableFrom_closedUnder (z₀ : Z) :
    K.ClosedUnder (K.reachableFrom z₀) := by
  intro z hz e he
  rcases hz with ⟨n, hn⟩
  exact ⟨n + 1, ⟨z, hn, e, he, rfl⟩⟩

/-- A stationary aggregation functional for a finite-support kernel.  This is a measure-free
interface useful for algebraic aggregate accounting. It refines `AggregateFunctional` (a unital
positive linear functional) with the kernel-invariance field, so its positivity/additivity/
homogeneity/normalization API — and the `.toAggregateFunctional` / `.toPositiveLinearFunctional`
coercions — are inherited rather than re-declared. -/
structure StationaryFunctional extends AggregateFunctional Z where
  /-- Stationarity/invariance in Koopman form: `∫ Pf dπ = ∫ f dπ`. -/
  invariant : ∀ f : Z → ℝ, aggregate (fun z => K.expect z f) = aggregate f

namespace StationaryFunctional

variable {K : FiniteSupportKernel Z Shock}
variable (π : K.StationaryFunctional)

/-- Invariance of aggregates under the finite-support expectation operator. -/
theorem aggregate_expect_eq (f : Z → ℝ) :
    π.aggregate (fun z => K.expect z f) = π.aggregate f :=
  π.invariant f

end StationaryFunctional

end FiniteSupportKernel

/-! ## Controlled finite-support kernels and policy induction -/

/-- A controlled finite-support transition system.  Given current state `z` and action `a`, a
finite shock is drawn from `shock z a`, and the next state is `next z a e`. -/
structure ControlledFiniteSupportKernel (State : Type*) (Action : Type*)
    (Shock : Type*) [Fintype Shock] [DecidableEq Shock] where
  /-- Feasible action set. -/
  feasible : State → Set Action
  /-- Shock law conditional on state and action. -/
  shock : State → Action → FinDist Shock
  /-- Deterministic state transition after the shock. -/
  next : State → Action → Shock → State

namespace ControlledFiniteSupportKernel

variable {State : Type*} {Action : Type*} {Shock : Type*}
variable [Fintype Shock] [DecidableEq Shock]
variable (C : ControlledFiniteSupportKernel State Action Shock)

/-- A stationary deterministic policy for the controlled kernel. -/
structure Policy where
  /-- Selected action. -/
  action : State → Action
  /-- Feasibility of the selected action. -/
  feasible : ∀ z, action z ∈ C.feasible z

/-- Kernel induced by a stationary deterministic policy. -/
def inducedKernel (π : C.Policy) : FiniteSupportKernel State Shock where
  shock z := C.shock z (π.action z)
  next z e := C.next z (π.action z) e

/-- One-step expectation under the policy-induced kernel. -/
@[simp] theorem inducedKernel_expect (π : C.Policy) (z : State) (f : State → ℝ) :
    (C.inducedKernel π).expect z f =
      (C.shock z (π.action z)).expect
        (fun e => f (C.next z (π.action z) e)) := rfl

/-- Positive-probability successors under the policy-induced kernel. -/
theorem inducedKernel_successors_iff (π : C.Policy) (z z' : State) :
    z' ∈ (C.inducedKernel π).successors z ↔
      ∃ e : Shock, 0 < C.shock z (π.action z) e ∧
        C.next z (π.action z) e = z' := by
  rfl

end ControlledFiniteSupportKernel

end Econlib.Probability
