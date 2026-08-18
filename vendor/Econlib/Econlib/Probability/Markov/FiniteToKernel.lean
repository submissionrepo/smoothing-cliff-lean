/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.Markov.Basic
public import Econlib.Probability.Markov.Endogenous

/-!
# Bridging finite Markov chains to measure-theoretic Markov kernels

`FiniteMarkovChain α` (finite-sum transition data over `[Fintype α] [DecidableEq α]`) and
`MarkovKernel α` (a bundled measure-valued `Kernel`) describe the same dynamics at two levels of
abstraction. This module embeds a finite chain into the measure-theoretic kernel API and proves
that the finite and measure-theoretic notions of a one-step push-forward and of stationarity agree.

## Main definitions

* `FiniteMarkovChain.toKernel` — the Mathlib `Kernel α α` whose fiber at `a` is the probability
  measure of `transition a`
* `FiniteMarkovChain.toMarkovKernel` — the bundled `MarkovKernel α`

## Main statements

* `FiniteMarkovChain.step_toProbDist` — one finite step `P.step d` agrees with the kernel
  push-forward `P.toMarkovKernel.step d.toProbDist`
* `FiniteMarkovChain.isStationary_iff_invariant` — the finite stationarity predicate
  `P.IsStationary μ` coincides with kernel invariance `P.toMarkovKernel.Invariant μ.toProbDist`

## Notes

Measurability of `toKernel` is automatic because `α` is finite (hence countable) with measurable
singletons (`measurable_of_countable`).

## Tags

markov chain, transition kernel, stationary distribution, invariant measure
-/

@[expose] public section

open BigOperators MeasureTheory ProbabilityTheory Finset

namespace Econlib.Probability
namespace FiniteMarkovChain

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable (P : FiniteMarkovChain α)

/-! ## The transition kernel of a finite Markov chain -/

/-- The measure-theoretic transition kernel of a finite Markov chain.  The fiber at `a` is the
probability measure attached to the finite distribution `transition a`.  Measurability is automatic
because `α` is finite (hence countable) with measurable singletons. -/
noncomputable def toKernel : Kernel α α where
  toFun a := (P.transition a).toProbDist.toMeasure
  measurable' := measurable_of_countable _

/-- The fiber of `toKernel` at `a` is the probability measure of `transition a`. -/
@[simp] lemma toKernel_apply (a : α) :
    P.toKernel a = (P.transition a).toProbDist.toMeasure := rfl

/-- Each fiber of `toKernel` is a probability measure, so the kernel is Markov. -/
instance instIsMarkovKernel_toKernel : IsMarkovKernel P.toKernel where
  isProbabilityMeasure a := by
    rw [toKernel_apply]
    exact (P.transition a).toProbDist.2

/-- The bundled `MarkovKernel` of a finite Markov chain. -/
noncomputable def toMarkovKernel : MarkovKernel α :=
  ⟨P.toKernel, inferInstance⟩

/-- The underlying kernel of `toMarkovKernel` is `toKernel`. -/
@[simp] lemma toMarkovKernel_kernel : P.toMarkovKernel.kernel = P.toKernel := rfl

/-! ## Step commutation -/

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- One finite step agrees with the PMF-`bind` of the transition family. -/
lemma step_toPMF (d : FinDist α) :
    (P.step d).toPMF = d.toPMF.bind (fun a => (P.transition a).toPMF) := by
  -- Both PMFs assign mass `ofReal (∑ s, d s * P.transition s s')` to `s'`; the bind side expands
  -- the finite tsum into a sum of `ofReal` products.
  ext s'
  rw [PMF.bind_apply]
  -- The bind tsum over the finite type collapses to a `Finset.univ` sum.
  rw [tsum_fintype]
  -- The step mass is `ofReal` of a finite sum; distribute `ofReal` over sum and product. All PMF
  -- coercions are `ENNReal.ofReal` of the underlying masses by definition.
  have hstep : (P.step d).toPMF s' = ENNReal.ofReal (∑ s, d.pmf s * (P.transition s).pmf s') := rfl
  rw [hstep, ENNReal.ofReal_sum_of_nonneg
    (fun s _ => mul_nonneg (d.nonneg s) ((P.transition s).nonneg s'))]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- Per term: `ofReal (a*b) = ofReal a * ofReal b`, and each factor is defeq to its PMF coercion.
  rw [ENNReal.ofReal_mul (d.nonneg s)]; rfl

/-- **Step-commutation bridge.**  One finite step `P.step d` corresponds, after embedding into
probability measures, to one push-forward of `d` through the measure-theoretic kernel:
`(P.step d).toProbDist = P.toMarkovKernel.step d.toProbDist`.  At the measure level this is the
identity `(P.step d).toProbDist.toMeasure = P.toKernel ∘ₘ d.toProbDist.toMeasure`. -/
theorem step_toProbDist (d : FinDist α) :
    (P.step d).toProbDist = P.toMarkovKernel.step d.toProbDist := by
  -- It suffices to check the underlying measures agree.
  apply ProbabilityMeasure.toMeasure_injective
  -- Unfold the kernel push-forward `step` to `Measure.bind`.
  letI : IsMarkovKernel P.toKernel := P.instIsMarkovKernel_toKernel
  change (P.step d).toProbDist.toMeasure
      = (P.toKernel ∘ₘ d.toProbDist.toMeasure)
  -- Compare both probability measures on an arbitrary measurable set.
  ext s hs
  -- Left: rewrite `P.step d` via the PMF-bind identity and expand on `s`.
  rw [FinDist.toProbDist_toMeasure, step_toPMF, PMF.toMeasure_bind_apply _ _ _ hs, tsum_fintype]
  -- Right: `Measure.bind` against the kernel becomes a `lintegral`, then a finite tsum.
  rw [Measure.bind_apply hs (P.toKernel.aemeasurable)]
  rw [FinDist.toProbDist_toMeasure]
  rw [MeasureTheory.lintegral_countable' (fun a => P.toKernel a s)]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Both summands are `d.toPMF a * (P.transition a).toPMF.toMeasure s`, up to commutativity and
  -- the singleton evaluation `d.toPMF.toMeasure {a} = d.toPMF a`.
  rw [toKernel_apply, FinDist.toProbDist_toMeasure,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a), mul_comm]

/-! ## Stationary coherence -/

/-- `FinDist.toProbDist` is injective on a finite measurable-singleton space. -/
lemma toProbDist_injective :
    Function.Injective (FinDist.toProbDist (α := α)) := by
  intro μ ν h
  -- Pass through the measure and PMF layers, each of which is injective here.
  have hmeasure : μ.toPMF.toMeasure = ν.toPMF.toMeasure := by
    have := congrArg ProbabilityMeasure.toMeasure h
    simpa [FinDist.toProbDist_toMeasure] using this
  have hpmf : μ.toPMF = ν.toPMF := PMF.toMeasure_injective hmeasure
  -- `toPMF` is `ENNReal.ofReal` of the masses, and `ofReal` is injective on nonnegatives.
  ext a
  have hμν : ENNReal.ofReal (μ.pmf a) = ENNReal.ofReal (ν.pmf a) := DFunLike.congr_fun hpmf a
  exact (ENNReal.ofReal_eq_ofReal_iff (μ.nonneg a) (ν.nonneg a)).mp hμν

/-- **Stationary coherence.**  A finite distribution is stationary for `P` iff its image is
invariant under the associated Markov kernel. -/
theorem isStationary_iff_invariant (μ : FinDist α) :
    P.IsStationary μ ↔ P.toMarkovKernel.Invariant μ.toProbDist := by
  -- `Invariant` unfolds to `P.toKernel ∘ₘ μ.toProbDist.toMeasure = μ.toProbDist.toMeasure`; the
  -- step-commutation bridge identifies the left side with `(P.step μ).toProbDist.toMeasure`.
  have hmeas : P.toKernel ∘ₘ μ.toProbDist.toMeasure = (P.step μ).toProbDist.toMeasure := by
    have h := step_toProbDist P μ
    have := congrArg ProbabilityMeasure.toMeasure h
    rw [this]; rfl
  rw [MarkovKernel.Invariant, toMarkovKernel_kernel, Kernel.Invariant, hmeas,
    FiniteMarkovChain.IsStationary]
  constructor
  · intro h; rw [h]
  · intro h
    apply toProbDist_injective
    apply ProbabilityMeasure.toMeasure_injective
    exact h

end FiniteMarkovChain
end Econlib.Probability
