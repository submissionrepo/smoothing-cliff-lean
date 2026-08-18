/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Convex.Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ContinuousMap.Interval

/-!
# Topology of convex-order feasible sets

This file packages continuous functions on intervals and proves compactness and closedness results
for probability measures supported on an interval and constrained by convex order.

## Main definitions

* `continuousMapOnIcc`: Continuous maps on an interval as bundled continuous functions.
* `boundedContinuousExtendIcc`: Bounded continuous extension from an interval.

## Main statements

* `isCompact_setOf_supportsOn_Icc`: Compactness of interval-supported probability measures.
* `isClosed_setOf_convexOrderOnIcc_right`: Closedness of a right convex-order section.

## Tags

probability, convex order, topology
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Econlib.Probability

/-- A continuous function on `Icc a b`, viewed as a bundled map on the subtype. -/
noncomputable def continuousMapOnIcc {a b : ℝ} (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc a b)) : C(Set.Icc a b, ℝ) :=
  ⟨fun x => φ x, continuousOn_iff_continuous_restrict.mp hφ⟩

/-- Extend a function continuous on `Icc a b` to a continuous function on `ℝ` by composing with
`projIcc`. -/
noncomputable def continuousExtendIcc {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc a b)) : C(ℝ, ℝ) := by
  letI : Fact (a ≤ b) := ⟨hab⟩
  exact ContinuousMap.IccExtendCM (continuousMapOnIcc φ hφ)

/-- On `[a, b]` the extension `continuousExtendIcc` agrees with the original function. -/
lemma continuousExtendIcc_eq {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    continuousExtendIcc hab φ hφ x = φ x := by
  letI : Fact (a ≤ b) := ⟨hab⟩
  rw [continuousExtendIcc, ContinuousMap.IccExtendCM_of_mem (f := continuousMapOnIcc φ hφ) hx]
  rfl

/-- The extension of a continuous function on `Icc a b` is bounded, hence defines a bounded
continuous function on `ℝ`. -/
noncomputable def boundedContinuousExtendIcc {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ)
    (hφ : ContinuousOn φ (Set.Icc a b)) : BoundedContinuousFunction ℝ ℝ := by
  classical
  let C₀ : ℝ := Classical.choose
    ((isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ)
  have hC₀ : ∀ x ∈ Set.Icc a b, ‖φ x‖ ≤ C₀ := Classical.choose_spec
    ((isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ)
  let C : ℝ := max C₀ 0
  let φExtCM := continuousExtendIcc hab φ hφ
  -- The extension is bounded by `C` everywhere: each value is `φ` at the clamped point.
  have hbound : ∀ z, |φExtCM z| ≤ C := fun z => by
    have hz' : |φ (Set.projIcc a b hab z)| ≤ C :=
      (hC₀ (Set.projIcc a b hab z) (Set.projIcc a b hab z).2).trans (le_max_left _ _)
    simpa [φExtCM, continuousExtendIcc, continuousMapOnIcc] using hz'
  exact BoundedContinuousFunction.mkOfBound φExtCM (2 * C) (fun x y => by
    rw [Real.dist_eq]
    calc
      |φExtCM x - φExtCM y| ≤ |φExtCM x| + |φExtCM y| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbound x) (hbound y)
      _ = 2 * C := by ring)

/-- On `[a, b]` the bounded extension `boundedContinuousExtendIcc` agrees with the original
function. -/
lemma boundedContinuousExtendIcc_eq {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b)) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (boundedContinuousExtendIcc hab φ hφ x : ℝ) = φ x := by
  unfold boundedContinuousExtendIcc
  simp [continuousExtendIcc_eq hab hφ hx]

/-- Probability laws supported on a fixed compact interval form a weak-* compact set. -/
theorem isCompact_setOf_supportsOn_Icc (a b : ℝ) :
    IsCompact {π : ProbabilityMeasure ℝ | ProbDist.supportsOn π (Set.Icc a b)} := by
  have hK_prok : IsCompact
      {π : ProbabilityMeasure ℝ | ∀ _ : ℕ, π (Set.Icc a b)ᶜ ≤ (0 : NNReal)} :=
    isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ => (0 : NNReal)) (K := fun _ => Set.Icc a b)
      tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inr monotone_const)
  have hsupp_eq :
      {π : ProbabilityMeasure ℝ | ∀ _ : ℕ, π (Set.Icc a b)ᶜ ≤ (0 : NNReal)}
        = {π : ProbabilityMeasure ℝ | ProbDist.supportsOn π (Set.Icc a b)} := by
    ext π
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have h0 : π (Set.Icc a b)ᶜ = 0 := le_antisymm (h 0) (zero_le)
      have h0' : (π : Measure ℝ) (Set.Icc a b)ᶜ = 0 :=
        (ProbabilityMeasure.null_iff_toMeasure_null π _).mp h0
      unfold ProbDist.supportsOn
      exact (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mp h0'
    · intro h _
      have h1 : (π : Measure ℝ) (Set.Icc a b) = 1 := h
      have h0 : (π : Measure ℝ) (Set.Icc a b)ᶜ = 0 :=
        (MeasureTheory.prob_compl_eq_zero_iff measurableSet_Icc).mpr h1
      have h0n : π (Set.Icc a b)ᶜ = 0 :=
        (ProbabilityMeasure.null_iff_toMeasure_null π _).mpr h0
      exact le_of_eq h0n
  rwa [hsupp_eq] at hK_prok

/-- Probability laws supported on a fixed compact interval form a weak-* closed set. -/
theorem isClosed_setOf_supportsOn_Icc (a b : ℝ) :
    IsClosed {π : ProbabilityMeasure ℝ | ProbDist.supportsOn π (Set.Icc a b)} :=
  (isCompact_setOf_supportsOn_Icc a b).isClosed

/-- For fixed right-hand law `ν` supported on `Icc a b`, the left-hand convex-order feasible set is
weak-* closed. -/
theorem isClosed_setOf_convexOrderOnIcc_right {a b : ℝ} {ν : ProbDist ℝ}
    (hν : ν.supportsOn (Set.Icc a b)) :
    IsClosed {μ : ProbDist ℝ | ConvexOrderOnIcc a b μ ν} := by
  have hab : a ≤ b := by
    by_contra hab'
    have : ν.supportsOn (∅ : Set ℝ) := by simpa [Set.Icc_eq_empty hab'] using hν
    unfold ProbDist.supportsOn at this
    simp at this
  let clampBCF := boundedContinuousExtendIcc hab id continuousOn_id
  let meanSet : Set (ProbDist ℝ) := {μ : ProbDist ℝ |
    ∫ x, (clampBCF : ℝ → ℝ) x ∂(μ : Measure ℝ) =
      ∫ x, (clampBCF : ℝ → ℝ) x ∂(ν : Measure ℝ)}
  let I := {φ : ℝ → ℝ // ConvexOn ℝ (Set.Icc a b) φ ∧ ContinuousOn φ (Set.Icc a b)}
  let testSet : I → Set (ProbDist ℝ) := fun φ => {μ : ProbDist ℝ |
    ∫ x, (boundedContinuousExtendIcc hab φ.1 φ.2.2 : ℝ → ℝ) x ∂(μ : Measure ℝ) ≤
      ∫ x, (boundedContinuousExtendIcc hab φ.1 φ.2.2 : ℝ → ℝ) x ∂(ν : Measure ℝ)}
  have hmean_closed : IsClosed meanSet := by
    have hcont :
        Continuous (fun μ : ProbabilityMeasure ℝ =>
          ∫ x, (clampBCF : ℝ → ℝ) x ∂(μ : Measure ℝ)) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction clampBCF
    simpa [meanSet] using isClosed_eq hcont continuous_const
  have htest_closed : ∀ φ, IsClosed (testSet φ) := by
    intro φ
    have hcont :
        Continuous (fun μ : ProbabilityMeasure ℝ =>
          ∫ x, (boundedContinuousExtendIcc hab φ.1 φ.2.2 : ℝ → ℝ) x ∂(μ : Measure ℝ)) :=
      ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (boundedContinuousExtendIcc hab φ.1 φ.2.2)
    simpa [testSet] using isClosed_le hcont continuous_const
  -- On a measure supported on `Icc a b`, the bounded extension of `ψ` agrees with `ψ` a.e.
  have hbcf_ae : ∀ (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Set.Icc a b)) (d : ProbDist ℝ),
      d.supportsOn (Set.Icc a b) →
        ∀ᵐ x ∂(d : Measure ℝ), (boundedContinuousExtendIcc hab ψ hψ : ℝ → ℝ) x = ψ x := by
    intro ψ hψ d hd
    filter_upwards [d.ae_mem_of_supportsOn measurableSet_Icc hd] with x hx using
      boundedContinuousExtendIcc_eq hab hψ hx
  have hclosed_aux : IsClosed
      (({μ : ProbDist ℝ | ProbDist.supportsOn μ (Set.Icc a b)} ∩ meanSet) ∩ ⋂ φ, testSet φ) := by
    exact
      ((isClosed_setOf_supportsOn_Icc a b).inter hmean_closed).inter
        (isClosed_iInter htest_closed)
  have hset_eq :
      {μ : ProbDist ℝ | ConvexOrderOnIcc a b μ ν}
        = (({μ : ProbDist ℝ | ProbDist.supportsOn μ (Set.Icc a b)} ∩ meanSet) ∩
            ⋂ φ, testSet φ) := by
    ext μ
    simp only [Set.mem_setOf_eq, meanSet, testSet, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      rcases h with ⟨hμ, hν', hmean, hconv⟩
      refine ⟨⟨hμ, ?_⟩, ?_⟩
      · rw [integral_congr_ae (hbcf_ae id continuousOn_id μ hμ),
          integral_congr_ae (hbcf_ae id continuousOn_id ν hν')]
        simpa [ProbDist.expect] using hmean
      · intro φ
        rw [integral_congr_ae (hbcf_ae φ.1 φ.2.2 μ hμ),
          integral_congr_ae (hbcf_ae φ.1 φ.2.2 ν hν')]
        exact hconv φ.1 φ.2.1 φ.2.2
    · rintro ⟨⟨hμ, hmean⟩, htests⟩
      refine ⟨hμ, hν, ?_, ?_⟩
      · have hμcongr :
            ∫ x, (clampBCF : ℝ → ℝ) x ∂(μ : Measure ℝ) = ∫ x, id x ∂(μ : Measure ℝ) :=
          integral_congr_ae (hbcf_ae id continuousOn_id μ hμ)
        have hνcongr :
            ∫ x, (clampBCF : ℝ → ℝ) x ∂(ν : Measure ℝ) = ∫ x, id x ∂(ν : Measure ℝ) :=
          integral_congr_ae (hbcf_ae id continuousOn_id ν hν)
        simpa [ProbDist.expect] using hμcongr.symm.trans (hmean.trans hνcongr)
      · intro φ hφ_conv hφ_cont
        have htest := htests ⟨φ, hφ_conv, hφ_cont⟩
        unfold ProbDist.expect
        rw [← integral_congr_ae (hbcf_ae φ hφ_cont μ hμ),
          ← integral_congr_ae (hbcf_ae φ hφ_cont ν hν)]
        exact htest
  rw [hset_eq]
  exact hclosed_aux

/-- For fixed right-hand law `ν` supported on `Icc a b`, the left-hand convex-order feasible set is
weak-* compact. -/
theorem isCompact_setOf_convexOrderOnIcc_right {a b : ℝ} {ν : ProbDist ℝ}
    (hν : ν.supportsOn (Set.Icc a b)) :
    IsCompact {μ : ProbDist ℝ | ConvexOrderOnIcc a b μ ν} := by
  exact (isCompact_setOf_supportsOn_Icc a b).of_isClosed_subset
    (isClosed_setOf_convexOrderOnIcc_right hν) (fun _ h => h.1)

end Econlib.Probability

end
