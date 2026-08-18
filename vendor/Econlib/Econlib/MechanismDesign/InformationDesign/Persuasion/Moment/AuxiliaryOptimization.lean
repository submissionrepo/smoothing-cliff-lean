/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.MeasurableCaratheodory
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Existence
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.MeanTests
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Measurable Carathéodory kernels by auxiliary optimization

For a closed-graph compact-bound multifunction `F : Y → Set (EuclideanSpace ℝ (Fin n))` with convex
fibers, a measurable barycenter `z₀ : Y → ℝⁿ`, and a finite reference measure `ν` on `Y`, this file
constructs a measurable kernel `κ : Y → Measure ℝⁿ` such that for `ν`-a.e. `y`, `κ y` is a
probability measure supported on `extremePoints (F y)` with barycenter `z₀ y`.

The auxiliary objective rewards conditional spread while preserving the barycenter. Optimality then
forces conditional mass onto extreme points, giving an a.e. measurable Carathéodory representation
suited to persuasion duality.

## Main definitions

* `twoPointSpread` — the symmetric two-point mean-preserving spread `(x ± εd) ↦ ½`.
* `patchedEval` — the joint evaluation `(y, x) ↦ x` on the graph of `F`, `z₀ y` elsewhere.
* `jointF` — the joint multifunction `(y, x) ↦ F y`.

## Main statements

* `exists_strict_improvement_of_nonextreme_kernel` — a kernel placing positive mass off the extreme
  points admits a measurable perturbation with the same conditional mean and strictly higher
  integrated second moment.
* `exists_optimal_kernel` — existence of a measurable admissible kernel maximizing the integrated
  second moment.
* `exists_measurable_caratheodory_kernel_ae` — a measurable kernel supported `ν`-a.e. on the
  extreme points of `F` with barycenter `z₀`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.10.
* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).

## Tags

carathéodory, extreme points, measurable kernel, mean-preserving spread, persuasion
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization

-- The measurable-selection machinery (`measurableSet_extremePoints_graph`,
-- `exists_measurable_descent_direction`) lives in `Econlib.Math.Analysis.MeasurableCaratheodory`.
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal Topology Pointwise

/-! ## Two-point mean-preserving spread

The pointwise perturbation behind the auxiliary-optimization argument: Replace mass at a point
`x` with half mass at `x + ε d` and half mass at `x - ε d`. The mean is preserved (linearity); the
second moment strictly increases (parallelogram law). -/

/-- For a non-zero direction `d` and positive `ε`, the symmetric two-point spread
`(x + εd) ↦ ½, (x - εd) ↦ ½` has second moment strictly greater than `‖x‖²`. -/
lemma twoPointSpread_secondMoment_gt
    {n : ℕ} (x d : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (hd : d ≠ 0) :
    ‖x‖^2 < (‖x + ε • d‖^2 + ‖x - ε • d‖^2) / 2 := by
  -- Parallelogram law: ‖x + εd‖² + ‖x - εd‖² = 2‖x‖² + 2‖εd‖².
  have h_para :
      ‖x + ε • d‖^2 + ‖x - ε • d‖^2 = 2 * ‖x‖^2 + 2 * ‖ε • d‖^2 := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hεd : ‖ε • d‖ = ε * ‖d‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
  have hεd_sq_pos : 0 < ‖ε • d‖^2 := by
    rw [hεd]
    positivity
  rw [h_para]
  linarith

/-- Mean of the two-point spread: `½(x + εd) + ½(x - εd) = x`. -/
lemma twoPointSpread_mean_eq
    {n : ℕ} (x d : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    (1/2 : ℝ) • (x + ε • d) + (1/2 : ℝ) • (x - ε • d) = x := by
  module

/-- The two-point spread, as a probability measure on `ℝⁿ`. -/
noncomputable def twoPointSpread {n : ℕ}
    (x d : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
  (1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac (x + ε • d) +
  (1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac (x - ε • d)

/-! ## Patched descent on `Y × ℝⁿ`

A measurable descent direction `d : Y × ℝⁿ → ℝⁿ` is needed such that on the graph of `F` (where
`x ∈ F y`), `d(y, x)` is a non-zero bidirectional descent at `x` in `F y` whenever `x ∉ ext (F y)`.
Since `exists_measurable_descent_direction` requires the base evaluation to lie in `F` everywhere,
the patched evaluation `patchedEval` takes the value `x` on `graph F` and `z₀ y` off it. -/

/-- The patched evaluation `z̃ : Y × ℝⁿ → ℝⁿ`, equal to `x` on `graph F` and `z₀ y` elsewhere. Used
to apply `exists_measurable_descent_direction` on the joint parameter space `Y × ℝⁿ`. -/
noncomputable def patchedEval {n : ℕ} {Y : Type*}
    (F : Y → Set (EuclideanSpace ℝ (Fin n)))
    (z₀ : Y → EuclideanSpace ℝ (Fin n)) :
    Y × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := by
  classical
  exact fun p => if p.2 ∈ F p.1 then p.2 else z₀ p.1

/-- The patched evaluation always lands in the fiber `F p.1`. -/
lemma patchedEval_mem
    {n : ℕ} {Y : Type*}
    (F : Y → Set (EuclideanSpace ℝ (Fin n)))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (p : Y × EuclideanSpace ℝ (Fin n)) :
    patchedEval F z₀ p ∈ F p.1 := by
  classical
  unfold patchedEval
  by_cases h : p.2 ∈ F p.1
  · simpa only [if_pos h] using h
  · simpa only [if_neg h] using hz₀_mem p.1

/-- The patched evaluation is measurable, given a measurable barycenter and a measurable graph. -/
lemma patchedEval_measurable
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) :
    Measurable (patchedEval F z₀) := by
  classical
  unfold patchedEval
  refine Measurable.ite hF_graph_meas measurable_snd ?_
  exact hz₀_meas.comp measurable_fst

/-- The joint multifunction `F̃ : Y × ℝⁿ → Set ℝⁿ` given by `F̃(y, x) := F y` (constant in the
second coordinate). -/
@[reducible] noncomputable def jointF {n : ℕ} {Y : Type*}
    (F : Y → Set (EuclideanSpace ℝ (Fin n))) :
    Y × EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)) :=
  fun p => F p.1

/-- The graph of the joint multifunction `jointF F` is closed when the graph of `F` is. -/
lemma jointF_graph_closed
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) :
    IsClosed {p : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ jointF F p.1} := by
  -- {((y, x), w) | w ∈ F y} = preimage of {(y, w) | w ∈ F y} under
  -- (y, x, w) ↦ (y, w), which is continuous.
  have h_cont : Continuous
      (fun p : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
        (p.1.1, p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  exact hF_graph_closed.preimage h_cont

/-- **Lifted descent direction.**  For each `(y, x) ∈ Y × ℝⁿ`, returns a measurable direction
`d(y, x)` such that, for every `(y, x)` with `x ∈ F y` and `x ∉ ext(F y)`, `d(y, x) ≠ 0` and a
bidirectional perturbation `x ± ε d(y, x) ∈ F y` exists. -/
lemma exists_jointDescent_direction
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y) :
    ∃ d : Y × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable d ∧
      (∀ p : Y × EuclideanSpace ℝ (Fin n),
        ∃ ε > (0 : ℝ),
          patchedEval F z₀ p + ε • d p ∈ F p.1 ∧
          patchedEval F z₀ p - ε • d p ∈ F p.1) ∧
      (∀ p : Y × EuclideanSpace ℝ (Fin n),
        patchedEval F z₀ p ∉ Set.extremePoints ℝ (F p.1) → d p ≠ 0) := by
  -- Apply `exists_measurable_descent_direction` with parameter space `Y × ℝⁿ`,
  -- multifunction `F̃(y, x) := F y`, and evaluation `z̃ := patchedEval F z₀`.
  have hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} :=
    hF_graph_closed.measurableSet
  have h_patched_meas : Measurable (patchedEval F z₀) :=
    patchedEval_measurable hz₀_meas hF_graph_meas
  have h_patched_mem : ∀ p, patchedEval F z₀ p ∈ jointF F p :=
    patchedEval_mem F hz₀_mem
  have hF_tilde_graph_closed :
      IsClosed {p : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
        p.2 ∈ jointF F p.1} := jointF_graph_closed hF_graph_closed
  -- The conclusion of `exists_measurable_descent_direction` applied to F̃ is
  -- precisely what we want, since F̃ p = F p.1.
  obtain ⟨d, hd_meas, hd_in, hd_ne⟩ :=
    exists_measurable_descent_direction (Y := Y × EuclideanSpace ℝ (Fin n))
      (F := jointF F) (K := K) hK_compact (fun _ => hF_sub_K _)
      hF_tilde_graph_closed (fun _ => hF_convex _) h_patched_meas h_patched_mem
  exact ⟨d, hd_meas, hd_in, hd_ne⟩

/-- **Measurable bidirectional step length.** For the lifted descent direction `d`, there is a
measurable, strictly positive step length `ε(p)` such that at every non-extreme point both
`patchedEval F z₀ p ± ε(p) • d p` lie in `F p.1`. -/
lemma exists_jointDescent_with_measurable_step
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y) :
    ∃ (d : Y × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (ε : Y × EuclideanSpace ℝ (Fin n) → ℝ),
      Measurable d ∧ Measurable ε ∧
      (∀ p, 0 < ε p) ∧
      (∀ p : Y × EuclideanSpace ℝ (Fin n),
        patchedEval F z₀ p ∉ Set.extremePoints ℝ (F p.1) →
          patchedEval F z₀ p + ε p • d p ∈ F p.1 ∧
          patchedEval F z₀ p - ε p • d p ∈ F p.1 ∧
          d p ≠ 0) := by
  classical
  obtain ⟨d, hd_meas, hd_in, hd_ne⟩ :=
    exists_jointDescent_direction hK_compact hF_sub_K hF_graph_closed hF_convex
      hz₀_meas hz₀_mem
  have hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} :=
    hF_graph_closed.measurableSet
  have h_patched_meas : Measurable (patchedEval F z₀) :=
    patchedEval_measurable hz₀_meas hF_graph_meas
  -- Predicate P(k, p): the step 1/(k+1) is a valid bidirectional perturbation.
  set P : ℕ → Y × EuclideanSpace ℝ (Fin n) → Prop := fun k p =>
    patchedEval F z₀ p + (1 / ((k : ℝ) + 1)) • d p ∈ F p.1 ∧
    patchedEval F z₀ p - (1 / ((k : ℝ) + 1)) • d p ∈ F p.1
    with hP_def
  -- Each {p | P k p} is measurable.
  have hP_meas : ∀ k, MeasurableSet {p | P k p} := by
    intro k
    have h_fwd : Measurable (fun p : Y × EuclideanSpace ℝ (Fin n) =>
        patchedEval F z₀ p + (1 / ((k : ℝ) + 1)) • d p) :=
      h_patched_meas.add (measurable_const.smul hd_meas)
    have h_bwd : Measurable (fun p : Y × EuclideanSpace ℝ (Fin n) =>
        patchedEval F z₀ p - (1 / ((k : ℝ) + 1)) • d p) :=
      h_patched_meas.sub (measurable_const.smul hd_meas)
    -- {p | g(p) ∈ F p.1} is measurable: pull back graph(F) under p ↦ (p.1, g p).
    have h_mem_meas : ∀ g : Y × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Measurable g → MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | g p ∈ F p.1} := by
      intro g hg
      have h_eq : {p : Y × EuclideanSpace ℝ (Fin n) | g p ∈ F p.1} =
          (fun p : Y × EuclideanSpace ℝ (Fin n) => (p.1, g p)) ⁻¹'
            {q : Y × EuclideanSpace ℝ (Fin n) | q.2 ∈ F q.1} := by
        ext; simp
      rw [h_eq]
      exact (measurable_fst.prodMk hg) hF_graph_meas
    have h_fwd_mem := h_mem_meas _ h_fwd
    have h_bwd_mem := h_mem_meas _ h_bwd
    have h_inter : {p | P k p} =
        {p : Y × EuclideanSpace ℝ (Fin n) |
            patchedEval F z₀ p + (1 / ((k : ℝ) + 1)) • d p ∈ F p.1} ∩
          {p : Y × EuclideanSpace ℝ (Fin n) |
            patchedEval F z₀ p - (1 / ((k : ℝ) + 1)) • d p ∈ F p.1} := by
      ext p; simp [P]
    rw [h_inter]
    exact h_fwd_mem.inter h_bwd_mem
  -- Helper: for s ∈ [0, ε₀], the point z + s • d is in F p.1 (by convexity).
  have h_seg_fwd : ∀ p, ∀ ε₀ : ℝ, 0 < ε₀ →
      patchedEval F z₀ p + ε₀ • d p ∈ F p.1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ →
      patchedEval F z₀ p + s • d p ∈ F p.1 := by
    intro p ε₀ hε₀_pos hε₀_fwd s hs0 hsε
    have h_z_in : patchedEval F z₀ p ∈ F p.1 := patchedEval_mem F hz₀_mem p
    have h_conv := hF_convex p.1
    have hε₀_ne : ε₀ ≠ 0 := ne_of_gt hε₀_pos
    have ht_unit : (s / ε₀) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs0 hε₀_pos.le, (div_le_one hε₀_pos).mpr hsε⟩
    have h_step :
        patchedEval F z₀ p + (s / ε₀) • (ε₀ • d p) ∈ F p.1 :=
      h_conv.add_smul_mem h_z_in hε₀_fwd ht_unit
    have h_eq : (s / ε₀) • (ε₀ • d p) = s • d p := by
      rw [smul_smul, div_mul_cancel₀ _ hε₀_ne]
    rwa [h_eq] at h_step
  have h_seg_bwd : ∀ p, ∀ ε₀ : ℝ, 0 < ε₀ →
      patchedEval F z₀ p - ε₀ • d p ∈ F p.1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ ε₀ →
      patchedEval F z₀ p - s • d p ∈ F p.1 := by
    intro p ε₀ hε₀_pos hε₀_bwd s hs0 hsε
    have h_z_in : patchedEval F z₀ p ∈ F p.1 := patchedEval_mem F hz₀_mem p
    have h_conv := hF_convex p.1
    have hε₀_ne : ε₀ ≠ 0 := ne_of_gt hε₀_pos
    have ht_unit : (s / ε₀) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs0 hε₀_pos.le, (div_le_one hε₀_pos).mpr hsε⟩
    -- z + ε₀ • (-d) = z - ε₀ • d ∈ F.
    have h_neg_in : patchedEval F z₀ p + ε₀ • (-d p) ∈ F p.1 := by
      rw [smul_neg, ← sub_eq_add_neg]; exact hε₀_bwd
    have h_step :
        patchedEval F z₀ p + (s / ε₀) • (ε₀ • (-d p)) ∈ F p.1 :=
      h_conv.add_smul_mem h_z_in h_neg_in ht_unit
    have h_eq : (s / ε₀) • (ε₀ • (-d p)) = -(s • d p) := by
      rw [smul_smul, div_mul_cancel₀ _ hε₀_ne, smul_neg]
    rw [h_eq, ← sub_eq_add_neg] at h_step
    exact h_step
  have hP_exists : ∀ p, ∃ k, P k p := by
    intro p
    obtain ⟨ε₀, hε₀_pos, hε₀_fwd, hε₀_bwd⟩ := hd_in p
    -- Choose k large enough that 1/(k+1) ≤ ε₀.
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε₀)
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h_inv_lt : 1 / ((k : ℝ) + 1) < ε₀ := by
      rw [div_lt_iff₀ hk_pos]
      have h_one_over : (1 : ℝ) / ε₀ < (k : ℝ) + 1 := lt_of_lt_of_le hk (by linarith)
      rw [div_lt_iff₀ hε₀_pos] at h_one_over
      linarith
    refine ⟨k, ?_, ?_⟩
    · exact h_seg_fwd p ε₀ hε₀_pos hε₀_fwd (1 / ((k : ℝ) + 1)) (by positivity)
        h_inv_lt.le
    · exact h_seg_bwd p ε₀ hε₀_pos hε₀_bwd (1 / ((k : ℝ) + 1)) (by positivity)
        h_inv_lt.le
  -- ε(p) := 1 / (Nat.find _ + 1).  Measurable via the constant family
  -- g m := fun _ => 1/((m : ℝ) + 1).
  refine ⟨d,
    fun p => 1 / (((Nat.find (hP_exists p) : ℕ) : ℝ) + 1),
    hd_meas, ?_, ?_, ?_⟩
  · -- Measurability.
    exact Measurable.find
      (f := fun m (_ : Y × EuclideanSpace ℝ (Fin n)) => 1 / (((m : ℕ) : ℝ) + 1))
      (fun _ => measurable_const) hP_meas hP_exists
  · -- Positivity.
    intro p
    have hk_pos : (0 : ℝ) < ((Nat.find (hP_exists p) : ℕ) : ℝ) + 1 := by positivity
    positivity
  · -- Descent conclusion.
    intro p hp_nonExt
    have hP_holds : P (Nat.find (hP_exists p)) p := Nat.find_spec (hP_exists p)
    refine ⟨hP_holds.1, hP_holds.2, hd_ne p hp_nonExt⟩

/-! ## Strict-improvement core

The substantive content of the auxiliary-optimization argument: A candidate kernel `κ` that is
not supported on extreme points over a `ν`-positive set admits a measurable perturbation `κ'` with
the same conditional mean and a strictly higher second moment integrated against `ν`. -/

/-- **Strict improvement off extreme points.** Given a measurable kernel `κ` supported in `F` with
conditional mean `z₀` `ν`-a.e., if `κ y` places positive mass on `F y \ ext(F y)` over a
`ν`-positive set, then there is a measurable perturbation `κ'` with the same properties
(probability, supported on `F`, conditional mean `z₀` `ν`-a.e.) and strictly higher integrated
second moment. -/
theorem exists_strict_improvement_of_nonextreme_kernel
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    (κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (hκ_meas : Measurable κ)
    (hκ_prob : ∀ y, MeasureTheory.IsProbabilityMeasure (κ y))
    (hκ_supp : ∀ y, ∀ᵐ x ∂(κ y), x ∈ F y)
    (hκ_mean : ∀ᵐ y ∂ν, ∫ x, x ∂(κ y) = z₀ y)
    (hκ_nonExt :
      0 < ν {y | 0 < (κ y) ((F y) \ Set.extremePoints ℝ (F y))}) :
    ∃ κ' : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      Measurable κ' ∧
      (∀ y, MeasureTheory.IsProbabilityMeasure (κ' y)) ∧
      (∀ y, ∀ᵐ x ∂(κ' y), x ∈ F y) ∧
      (∀ᵐ y ∂ν, ∫ x, x ∂(κ' y) = z₀ y) ∧
      ∫ y, ∫ x, ‖x‖^2 ∂(κ y) ∂ν <
        ∫ y, ∫ x, ‖x‖^2 ∂(κ' y) ∂ν := by
  classical
  obtain ⟨d, ε, hd_meas, hε_meas, hε_pos, hd_ε⟩ :=
    exists_jointDescent_with_measurable_step hK_compact hF_sub_K hF_graph_closed
      hF_convex hz₀_meas hz₀_mem
  have hExtG_meas : MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ Set.extremePoints ℝ (F p.1)} :=
    measurableSet_extremePoints_graph hK_compact hF_sub_K hF_graph_closed hF_convex
  --   On extreme points (or off graph): θ(y,x) = δ_x  (no perturbation).
  --   Elsewhere: θ(y,x) = ½ δ_{x + ε(y,x) d(y,x)} + ½ δ_{x - ε(y,x) d(y,x)}.
  -- Both branches are probability measures with mean x; the off-extreme branch
  -- has strict second-moment gain by parallelogram.
  set θ : Y × EuclideanSpace ℝ (Fin n) → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    fun p =>
      if p.2 ∈ Set.extremePoints ℝ (F p.1) then
        MeasureTheory.Measure.dirac p.2
      else
        twoPointSpread p.2 (d p) (ε p)
    with hθ_def
  -- κ' y := bind (κ y) (fun x => θ (y, x)).
  -- Auxiliary: θ(y, x) is always a probability measure (dirac or ½δ_a + ½δ_b).
  have h_twoPS_prob : ∀ p : Y × EuclideanSpace ℝ (Fin n),
      MeasureTheory.IsProbabilityMeasure (twoPointSpread p.2 (d p) (ε p)) := by
    intro p
    refine ⟨?_⟩
    unfold twoPointSpread
    rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply,
        MeasureTheory.measure_univ, MeasureTheory.measure_univ]
    simp only [smul_eq_mul, mul_one]
    exact ENNReal.add_halves 1
  have h_θ_prob : ∀ p, MeasureTheory.IsProbabilityMeasure (θ p) := by
    intro p
    by_cases h : p.2 ∈ Set.extremePoints ℝ (F p.1)
    · rw [hθ_def]; simp only [h, if_true]
      infer_instance
    · rw [hθ_def]; simp only [h, if_false]
      exact h_twoPS_prob p
  -- Joint measurability of θ : Y × ℝⁿ → Measure ℝⁿ.
  -- Coercion to set-function is measurable for each measurable s; combine via
  -- `Measure.measurable_of_measurable_coe`.
  have hθ_meas : Measurable θ := by
    refine MeasureTheory.Measure.measurable_of_measurable_coe _ fun s hs => ?_
    -- (fun p ↦ θ p s) = if p.2 ∈ ext(F p.1) then δ_{p.2} s else twoPS p.2 (d p) (ε p) s.
    have h_dirac_branch : Measurable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => MeasureTheory.Measure.dirac p.2 s) :=
      (MeasureTheory.Measure.measurable_coe hs).comp
        (MeasureTheory.Measure.measurable_dirac.comp measurable_snd)
    have h_g_fwd : Measurable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2 + ε p • d p) :=
      measurable_snd.add (hε_meas.smul hd_meas)
    have h_g_bwd : Measurable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2 - ε p • d p) :=
      measurable_snd.sub (hε_meas.smul hd_meas)
    have h_twoPS_branch : Measurable
        (fun p : Y × EuclideanSpace ℝ (Fin n) =>
          twoPointSpread p.2 (d p) (ε p) s) := by
      unfold twoPointSpread
      simp_rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        smul_eq_mul]
      refine Measurable.add ?_ ?_
      · exact measurable_const.mul
          ((MeasureTheory.Measure.measurable_coe hs).comp
            (MeasureTheory.Measure.measurable_dirac.comp h_g_fwd))
      · exact measurable_const.mul
          ((MeasureTheory.Measure.measurable_coe hs).comp
            (MeasureTheory.Measure.measurable_dirac.comp h_g_bwd))
    have h_pointwise :
        (fun p : Y × EuclideanSpace ℝ (Fin n) => θ p s) =
        fun p =>
          if p.2 ∈ Set.extremePoints ℝ (F p.1) then
            MeasureTheory.Measure.dirac p.2 s
          else
            twoPointSpread p.2 (d p) (ε p) s := by
      funext p; simp only [hθ_def, apply_ite (fun μ : MeasureTheory.Measure _ => μ s)]
    rw [h_pointwise]
    exact Measurable.ite hExtG_meas h_dirac_branch h_twoPS_branch
  refine ⟨fun y => (κ y).bind (fun x => θ (y, x)), ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) Measurable κ'.
    -- κ' y s = ∫⁻ x, θ(y,x) s ∂(κ y); applies `Measurable.lintegral_kernel_prod_right`
    -- after wrapping κ as a finite kernel.
    refine MeasureTheory.Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have h_bind_apply : ∀ y,
        ((κ y).bind (fun x => θ (y, x))) s = ∫⁻ x, θ (y, x) s ∂(κ y) := by
      intro y
      refine MeasureTheory.Measure.bind_apply hs ?_
      exact (hθ_meas.comp measurable_prodMk_left).aemeasurable
    simp_rw [h_bind_apply]
    -- Wrap κ as a kernel; it is finite because each κ y is a probability measure.
    let K : ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) := ⟨κ, hκ_meas⟩
    haveI hK_finite : ProbabilityTheory.IsFiniteKernel K :=
      ⟨1, ENNReal.one_lt_top, fun y => by
        change (κ y) Set.univ ≤ 1
        rw [(hκ_prob y).measure_univ]⟩
    have hf_meas :
        Measurable
          (Function.uncurry (fun (y : Y) (x : EuclideanSpace ℝ (Fin n)) => θ (y, x) s)) :=
      (MeasureTheory.Measure.measurable_coe hs).comp hθ_meas
    -- κ y = K y, so the lintegral against κ y matches the kernel form.
    exact Measurable.lintegral_kernel_prod_right (κ := K) hf_meas
  · -- (b) IsProbabilityMeasure (κ' y).
    intro y
    haveI : MeasureTheory.IsProbabilityMeasure (κ y) := hκ_prob y
    refine MeasureTheory.isProbabilityMeasure_bind
      (hθ_meas.comp measurable_prodMk_left).aemeasurable ?_
    exact Filter.Eventually.of_forall (fun x => h_θ_prob (y, x))
  · -- (c) Support: ∀ᵐ x ∂(κ' y), x ∈ F y.
    -- Each fibre F y is closed (section of the closed graph) hence measurable.
    -- Wrap x ↦ θ(y, x) as a kernel and use the kernel-composition ae lemma to
    -- reduce to: for κ y-a.e. x ∈ F y, ∀ᵐ x' ∂(θ(y, x)), x' ∈ F y.  Case-split:
    --  - x ∈ ext(F y): θ(y, x) = δ_x; immediate from `ae_dirac_iff`.
    --  - x ∉ ext(F y): θ(y, x) = twoPointSpread; both `x ± ε•d ∈ F y` by `hd_ε`,
    --    and `(1/2)δ_a + (1/2)δ_b` is ae-concentrated on `{a, b} ⊆ F y`.
    intro y
    haveI : MeasureTheory.IsProbabilityMeasure (κ y) := hκ_prob y
    have hFy_closed : IsClosed (F y) := by
      have h_eq : F y =
          (fun x : EuclideanSpace ℝ (Fin n) => (y, x)) ⁻¹'
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} := by
        ext; simp
      rw [h_eq]
      exact hF_graph_closed.preimage (continuous_const.prodMk continuous_id)
    have hFy_meas : MeasurableSet (F y) := hFy_closed.measurableSet
    let Tθ_y : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n)) :=
      ⟨fun x => θ (y, x), hθ_meas.comp measurable_prodMk_left⟩
    change ∀ᵐ x' ∂((κ y).bind (fun x => θ (y, x))), x' ∈ F y
    have h_bind_eq : (κ y).bind (fun x => θ (y, x)) = Tθ_y ∘ₘ (κ y) := rfl
    rw [h_bind_eq]
    refine MeasureTheory.Measure.ae_comp_of_ae_ae hFy_meas ?_
    filter_upwards [hκ_supp y] with x hx_in_Fy
    change ∀ᵐ x' ∂(θ (y, x)), x' ∈ F y
    by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
    · -- θ(y, x) = δ_x with x ∈ F y.
      have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
        rw [hθ_def]; simp [h_ext]
      rw [h_θ_eq]
      exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr hx_in_Fy
    · -- θ(y, x) = twoPointSpread; perturbations land in F y by `hd_ε`.
      have h_patched : patchedEval F z₀ (y, x) = x := by
        classical
        unfold patchedEval; simp [hx_in_Fy]
      have h_pe_nonext :
          patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
        rw [h_patched]; exact h_ext
      obtain ⟨h_fwd_in, h_bwd_in, _⟩ := hd_ε (y, x) h_pe_nonext
      rw [h_patched] at h_fwd_in h_bwd_in
      have h_θ_eq :
          θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
        rw [hθ_def]; simp [h_ext]
      rw [h_θ_eq]
      unfold twoPointSpread
      rw [MeasureTheory.ae_add_measure_iff]
      have h_half_ne : (1/2 : ℝ≥0∞) ≠ 0 := by norm_num
      refine ⟨?_, ?_⟩
      · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
        exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr h_fwd_in
      · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
        exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr h_bwd_in
  · -- (d) Mean preservation: ν-a.e. y, ∫ x ∂(κ' y) = z₀ y.
    -- θ preserves the mean pointwise (dirac leaves x fixed; twoPointSpread_mean_eq gives the
    -- symmetric case).  Route through `(κ y).bind θ_y = (κ y ⊗ₘ Tθ_y).snd` and
    -- `integral_compProd` to reduce to `∫ x, x ∂(κ y) = z₀ y`.
    filter_upwards [hκ_mean] with y hy_mean
    haveI hκy_prob : MeasureTheory.IsProbabilityMeasure (κ y) := hκ_prob y
    -- F y closed and bounded by some M (since F y ⊆ K compact).
    have hFy_closed : IsClosed (F y) := by
      have h_eq : F y =
          (fun x : EuclideanSpace ℝ (Fin n) => (y, x)) ⁻¹'
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} := by
        ext; simp
      rw [h_eq]
      exact hF_graph_closed.preimage (continuous_const.prodMk continuous_id)
    have hFy_meas : MeasurableSet (F y) := hFy_closed.measurableSet
    obtain ⟨M, hM_K⟩ := hK_compact.isBounded.exists_norm_le
    have hM_F : ∀ x ∈ F y, ‖x‖ ≤ M := fun x hx => hM_K x (hF_sub_K y hx)
    -- Build the kernel Tθ_y from x ↦ θ(y, x).
    let Tθ_y : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n)) :=
      ⟨fun x => θ (y, x), hθ_meas.comp measurable_prodMk_left⟩
    haveI hTθ_markov : ProbabilityTheory.IsMarkovKernel Tθ_y :=
      ⟨fun x => h_θ_prob (y, x)⟩
    -- (i) Pointwise mean of θ for κ y-a.e. x ∈ F y.
    have hθ_pointwise_mean :
        ∀ᵐ x ∂(κ y), ∫ x', x' ∂(θ (y, x)) = x := by
      filter_upwards [hκ_supp y] with x hx_in_Fy
      by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
      · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq, MeasureTheory.integral_dirac]
      · have h_patched : patchedEval F z₀ (y, x) = x := by
          classical
          unfold patchedEval
          simp [hx_in_Fy]
        have h_pe_nonext :
            patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
          rw [h_patched]; exact h_ext
        obtain ⟨_, _, _⟩ := hd_ε (y, x) h_pe_nonext
        have h_θ_eq :
            θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq]
        unfold twoPointSpread
        have h_int_a : MeasureTheory.Integrable
            (fun x' : EuclideanSpace ℝ (Fin n) => x')
            ((1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac (x + ε (y, x) • d (y, x))) :=
          (MeasureTheory.integrable_dirac (by simp)).smul_measure (by norm_num)
        have h_int_b : MeasureTheory.Integrable
            (fun x' : EuclideanSpace ℝ (Fin n) => x')
            ((1/2 : ℝ≥0∞) • MeasureTheory.Measure.dirac (x - ε (y, x) • d (y, x))) :=
          (MeasureTheory.integrable_dirac (by simp)).smul_measure (by norm_num)
        rw [MeasureTheory.integral_add_measure h_int_a h_int_b,
            MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
            MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
        have h_half_toReal : ((1/2 : ℝ≥0∞).toReal : ℝ) = (1/2 : ℝ) := by norm_num
        rw [h_half_toReal]
        exact twoPointSpread_mean_eq x (d (y, x)) (ε (y, x))
    change ∫ x', x' ∂((κ y).bind (fun x => θ (y, x))) = z₀ y
    have h_bind_snd : (κ y).bind (fun x => θ (y, x)) = ((κ y) ⊗ₘ Tθ_y).snd := by
      rw [MeasureTheory.Measure.snd_compProd]; rfl
    rw [h_bind_snd, MeasureTheory.Measure.snd,
        MeasureTheory.integral_map measurable_snd.aemeasurable
          (by fun_prop : MeasureTheory.AEStronglyMeasurable
            (fun x : EuclideanSpace ℝ (Fin n) => x) _)]
    have h_compProd_supp : ∀ᵐ p ∂((κ y) ⊗ₘ Tθ_y), p.2 ∈ F y := by
      apply MeasureTheory.Measure.ae_compProd_of_ae_ae
        (measurable_snd hFy_meas)
      filter_upwards [hκ_supp y] with x hx_in_Fy
      change ∀ᵐ x' ∂(θ (y, x)), x' ∈ F y
      by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
      · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq]
        exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr hx_in_Fy
      · have h_patched : patchedEval F z₀ (y, x) = x := by
          classical
          unfold patchedEval
          simp [hx_in_Fy]
        have h_pe_nonext :
            patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
          rw [h_patched]; exact h_ext
        obtain ⟨h_fwd_in, h_bwd_in, _⟩ := hd_ε (y, x) h_pe_nonext
        rw [h_patched] at h_fwd_in h_bwd_in
        have h_θ_eq :
            θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq]
        unfold twoPointSpread
        rw [MeasureTheory.ae_add_measure_iff]
        have h_half_ne : (1/2 : ℝ≥0∞) ≠ 0 := by norm_num
        refine ⟨?_, ?_⟩
        · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
          exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr h_fwd_in
        · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
          exact (MeasureTheory.ae_dirac_iff hFy_meas).mpr h_bwd_in
    have h_integrable : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2)
        ((κ y) ⊗ₘ Tθ_y) := by
      refine MeasureTheory.Integrable.of_bound (by fun_prop) M ?_
      filter_upwards [h_compProd_supp] with p hp
      exact hM_F p.2 hp
    rw [MeasureTheory.Measure.integral_compProd h_integrable]
    have h_congr_ae :
        (fun x => ∫ x', x' ∂(Tθ_y x)) =ᵐ[κ y] fun x => x := by
      filter_upwards [hθ_pointwise_mean] with x hx using hx
    rw [MeasureTheory.integral_congr_ae h_congr_ae]
    exact hy_mean
  · -- (e) Strict cost inequality.
    --
    -- Strategy.  Let `A(y) := ∫ x, ‖x‖² ∂(κ y)`, `B(y) := ∫ x', ‖x'‖² ∂(κ' y)`.
    -- By `snd_compProd` + `integral_compProd` + linearity (over a per-y kernel
    -- `Tθ y x := θ(y, x)`),
    --   `B(y) = A(y) + ∫ x, gain(y, x) ∂(κ y)`
    -- where `gain(y, x) := ∫ x', ‖x'‖² ∂(θ(y, x)) - ‖x‖²`.  On extreme `x`, the
    -- pointwise integral is `‖x‖²` (Dirac) so `gain = 0`.  On non-extreme `x ∈ F y`,
    -- `twoPointSpread_secondMoment_gt` gives strict `gain > 0`.
    -- Hence `B(y) - A(y) ≥ 0` pointwise and `> 0` on `{y | 0 < (κ y)(F y \ ext F y)}`,
    -- a positive-ν set by `hκ_nonExt`.  Strict integral via
    -- `integral_pos_iff_support_of_nonneg_ae`.
    -- ───────────────── Infrastructure ─────────────────
    -- Bound for ‖·‖ on K.
    obtain ⟨M, hM_K⟩ := hK_compact.isBounded.exists_norm_le
    -- Per-y kernel.
    have hθ_meas_slice : ∀ y, Measurable (fun x => θ (y, x)) :=
      fun _ => hθ_meas.comp measurable_prodMk_left
    let Tθ : Y → ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n)) :=
      fun y => ⟨fun x => θ (y, x), hθ_meas_slice y⟩
    have hTθ_apply : ∀ y x, (Tθ y) x = θ (y, x) := fun _ _ => rfl
    have hTθ_markov : ∀ y, ProbabilityTheory.IsMarkovKernel (Tθ y) :=
      fun y => ⟨fun x => h_θ_prob (y, x)⟩
    -- F y closed and measurable.
    have hFy_closed : ∀ y, IsClosed (F y) := by
      intro y
      have h_eq : F y =
          (fun x : EuclideanSpace ℝ (Fin n) => (y, x)) ⁻¹'
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} := by
        ext; simp
      rw [h_eq]
      exact hF_graph_closed.preimage (continuous_const.prodMk continuous_id)
    have hFy_meas : ∀ y, MeasurableSet (F y) := fun y => (hFy_closed y).measurableSet
    have hExtFy_meas : ∀ y, MeasurableSet (Set.extremePoints ℝ (F y)) := by
      intro y
      have h_eq : Set.extremePoints ℝ (F y) =
          (fun x : EuclideanSpace ℝ (Fin n) => (y, x)) ⁻¹'
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ Set.extremePoints ℝ (F p.1)} := by
        ext; simp
      rw [h_eq]
      exact hExtG_meas.preimage (by fun_prop)
    -- compProd support on F y × F y.
    have h_compProd_supp : ∀ y, ∀ᵐ p ∂((κ y) ⊗ₘ (Tθ y)),
        p.1 ∈ F y ∧ p.2 ∈ F y := by
      intro y
      haveI := hκ_prob y
      haveI := hTθ_markov y
      refine MeasureTheory.Measure.ae_compProd_of_ae_ae
        ((measurable_fst (hFy_meas y)).inter (measurable_snd (hFy_meas y))) ?_
      filter_upwards [hκ_supp y] with x hx_in_Fy
      refine Filter.Eventually.and (Filter.Eventually.of_forall fun _ => hx_in_Fy) ?_
      change ∀ᵐ x' ∂(θ (y, x)), x' ∈ F y
      by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
      · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq]
        exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr hx_in_Fy
      · have h_patched : patchedEval F z₀ (y, x) = x := by
          classical
          unfold patchedEval
          simp [hx_in_Fy]
        have h_pe_nonext :
            patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
          rw [h_patched]; exact h_ext
        obtain ⟨h_fwd_in, h_bwd_in, _⟩ := hd_ε (y, x) h_pe_nonext
        rw [h_patched] at h_fwd_in h_bwd_in
        have h_θ_eq :
            θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq]
        unfold twoPointSpread
        rw [MeasureTheory.ae_add_measure_iff]
        have h_half_ne : (1/2 : ℝ≥0∞) ≠ 0 := by norm_num
        refine ⟨?_, ?_⟩
        · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
          exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_fwd_in
        · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
          exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_bwd_in
    -- ───────────────── Pointwise gain ─────────────────
    -- θ-mean square dominates ‖x‖² with equality iff x ∈ ext F y.
    -- On non-extreme points the inequality is strict (parallelogram law).
    have hθ_secondMoment_gt :
        ∀ y x, x ∈ F y → x ∉ Set.extremePoints ℝ (F y) →
          ‖x‖^2 < ∫ x', ‖x'‖^2 ∂(θ (y, x)) := by
      intro y x hx_in_Fy h_nonext
      have h_patched : patchedEval F z₀ (y, x) = x := by
        classical
        unfold patchedEval
        simp [hx_in_Fy]
      have h_pe_nonext :
          patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
        rw [h_patched]; exact h_nonext
      obtain ⟨_, _, hd_ne⟩ := hd_ε (y, x) h_pe_nonext
      have h_θ_eq : θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
        rw [hθ_def]; simp [h_nonext]
      rw [h_θ_eq]
      unfold twoPointSpread
      rw [MeasureTheory.integral_add_measure
          ((MeasureTheory.integrable_dirac (by simp)).smul_measure
            (by norm_num : (1/2:ℝ≥0∞) ≠ ∞))
          ((MeasureTheory.integrable_dirac (by simp)).smul_measure
            (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)),
        MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure,
        MeasureTheory.integral_dirac, MeasureTheory.integral_dirac]
      have h_half_toReal : ((1/2 : ℝ≥0∞).toReal : ℝ) = (1/2 : ℝ) := by norm_num
      rw [h_half_toReal]
      have h_strict := twoPointSpread_secondMoment_gt x (d (y, x)) (ε (y, x))
          (hε_pos (y, x)) hd_ne
      simp only [smul_eq_mul]
      linarith
    have hθ_secondMoment_ge :
        ∀ y x, x ∈ F y → ‖x‖^2 ≤ ∫ x', ‖x'‖^2 ∂(θ (y, x)) := by
      intro y x hx_in_Fy
      by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
      · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
          rw [hθ_def]; simp [h_ext]
        rw [h_θ_eq, MeasureTheory.integral_dirac]
      · exact (hθ_secondMoment_gt y x hx_in_Fy h_ext).le
    -- ───────────────── Integrability ─────────────────
    -- ‖·‖² is integrable against κ y (bounded by M²).
    have hA_int : ∀ y, MeasureTheory.Integrable (fun x => ‖x‖^2) (κ y) := by
      intro y
      haveI := hκ_prob y
      refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
      filter_upwards [hκ_supp y] with x hx_in_Fy
      have h1 : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx_in_Fy)
      have h2 : 0 ≤ ‖x‖ := norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
    -- ‖·.snd‖² is integrable against compProd (bounded by M² via support).
    haveI hcompProd_prob : ∀ y, MeasureTheory.IsProbabilityMeasure
        ((κ y) ⊗ₘ (Tθ y)) := by
      intro y
      haveI := hκ_prob y
      haveI := hTθ_markov y
      infer_instance
    have h_compProd_sqIntegrable : ∀ y, MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2)
        ((κ y) ⊗ₘ (Tθ y)) := by
      intro y
      refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
      filter_upwards [h_compProd_supp y] with p hp
      have h1 : ‖p.2‖ ≤ M := hM_K p.2 (hF_sub_K y hp.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg p.2]
    -- For each y, B(y) is the integral over κ' y, equal to compProd-snd integral.
    have hB_int : ∀ y, MeasureTheory.Integrable (fun x' => ‖x'‖^2)
        ((κ y).bind (fun x => θ (y, x))) := by
      intro y
      haveI := hκ_prob y
      haveI := hTθ_markov y
      have h_bind_snd : (κ y).bind (fun x => θ (y, x)) = ((κ y) ⊗ₘ (Tθ y)).snd := by
        rw [MeasureTheory.Measure.snd_compProd]; rfl
      rw [h_bind_snd, MeasureTheory.Measure.snd]
      refine (MeasureTheory.integrable_map_measure (by fun_prop)
        measurable_snd.aemeasurable).mpr ?_
      exact h_compProd_sqIntegrable y
    -- ───────────────── B = A + gain ─────────────────
    -- gain(y) := ∫ x, (∫ x', ‖x'‖² ∂(θ(y,x)) - ‖x‖²) ∂(κ y).
    have h_inner_int_bound : ∀ y, MeasureTheory.Integrable
        (fun x => ∫ x', ‖x'‖^2 ∂(θ (y, x))) (κ y) := by
      intro y
      haveI := hκ_prob y
      haveI := hTθ_markov y
      refine MeasureTheory.Integrable.of_bound ?_ (M^2) ?_
      · -- AEStronglyMeasurable.
        have h_meas : MeasureTheory.StronglyMeasurable
            (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              ‖p.2‖^2) := by fun_prop
        exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
          (κ := Tθ y) h_meas).aestronglyMeasurable
      · filter_upwards [hκ_supp y] with x hx_in_Fy
        rw [Real.norm_eq_abs, abs_of_nonneg
            (MeasureTheory.integral_nonneg (fun _ => by positivity))]
        -- ∫ x', ‖x'‖² ∂(θ(y,x)) ≤ M² since θ is supported on F y a.e. (for x ∈ F y)
        have h_θ_supp : ∀ᵐ x' ∂(θ (y, x)), x' ∈ F y := by
          by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
          · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
              rw [hθ_def]; simp [h_ext]
            rw [h_θ_eq]
            exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr hx_in_Fy
          · have h_patched : patchedEval F z₀ (y, x) = x := by
              classical
              unfold patchedEval
              simp [hx_in_Fy]
            have h_pe_nonext :
                patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
              rw [h_patched]; exact h_ext
            obtain ⟨h_fwd_in, h_bwd_in, _⟩ := hd_ε (y, x) h_pe_nonext
            rw [h_patched] at h_fwd_in h_bwd_in
            have h_θ_eq :
                θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
              rw [hθ_def]; simp [h_ext]
            rw [h_θ_eq]
            unfold twoPointSpread
            rw [MeasureTheory.ae_add_measure_iff]
            have h_half_ne : (1/2 : ℝ≥0∞) ≠ 0 := by norm_num
            refine ⟨?_, ?_⟩
            · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
              exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_fwd_in
            · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
              exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_bwd_in
        haveI := h_θ_prob (y, x)
        calc ∫ x', ‖x'‖^2 ∂(θ (y, x))
            ≤ ∫ _, (M^2 : ℝ) ∂(θ (y, x)) := by
              refine MeasureTheory.integral_mono_ae ?_ (MeasureTheory.integrable_const _) ?_
              · -- Integrable (‖x'‖²) (θ(y,x))
                refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
                filter_upwards [h_θ_supp] with x' hx'_in_Fy
                have : ‖x'‖ ≤ M := hM_K x' (hF_sub_K y hx'_in_Fy)
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                nlinarith [norm_nonneg x']
              · filter_upwards [h_θ_supp] with x' hx'_in_Fy
                have : ‖x'‖ ≤ M := hM_K x' (hF_sub_K y hx'_in_Fy)
                nlinarith [norm_nonneg x']
          _ = M^2 := by simp
    have h_B_eq : ∀ y,
        (∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) =
        (∫ x, ‖x‖^2 ∂(κ y)) +
          ∫ x, ((∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2) ∂(κ y) := by
      intro y
      haveI := hκ_prob y
      haveI := hTθ_markov y
      have h_bind_snd : (κ y).bind (fun x => θ (y, x)) = ((κ y) ⊗ₘ (Tθ y)).snd := by
        rw [MeasureTheory.Measure.snd_compProd]; rfl
      rw [h_bind_snd, MeasureTheory.Measure.snd,
        MeasureTheory.integral_map measurable_snd.aemeasurable
          (by fun_prop : MeasureTheory.AEStronglyMeasurable
            (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖^2) _),
        MeasureTheory.Measure.integral_compProd (h_compProd_sqIntegrable y)]
      -- ∫ x, ∫ x', ‖x'‖² ∂(Tθ y x) ∂κ y = ∫ x, ‖x‖² ∂κ y + ∫ x, (∫ x', ‖x'‖² ∂θ(y,x) - ‖x‖²) ∂κ y
      have h_split : ∀ x,
          ∫ x', ‖x'‖^2 ∂((Tθ y) x) =
            ‖x‖^2 + ((∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2) := by
        intro x; rw [hTθ_apply]; ring
      simp_rw [h_split]
      have h_gain_int : MeasureTheory.Integrable
          (fun x => (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2) (κ y) :=
        (h_inner_int_bound y).sub (hA_int y)
      rw [MeasureTheory.integral_add (hA_int y) h_gain_int]
    -- gain(y) ≥ 0 pointwise.
    set gainIntegral : Y → ℝ :=
      fun y => ∫ x, ((∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2) ∂(κ y) with hGI_def
    have h_gain_nonneg : ∀ y, 0 ≤ gainIntegral y := by
      intro y
      haveI := hκ_prob y
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hκ_supp y] with x hx
      change 0 ≤ (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2
      linarith [hθ_secondMoment_ge y x hx]
    -- gain(y) > 0 ⟺ positive κ y mass on non-extreme.
    have h_gain_pos_of_nonExt :
        ∀ y, 0 < (κ y) (F y \ Set.extremePoints ℝ (F y)) → 0 < gainIntegral y := by
      intro y hy
      haveI := hκ_prob y
      have h_diff_meas : MeasurableSet (F y \ Set.extremePoints ℝ (F y)) :=
        (hFy_meas y).diff (hExtFy_meas y)
      -- The integrand `fun x => integral - ‖x‖²` is strictly positive on F y \ ext F y.
      have h_supp_strict : ∀ x ∈ F y \ Set.extremePoints ℝ (F y),
          0 < (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2 := by
        intro x ⟨hx_in_Fy, hx_nonExt⟩
        linarith [hθ_secondMoment_gt y x hx_in_Fy hx_nonExt]
      have h_int : MeasureTheory.Integrable
          (fun x => (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2) (κ y) :=
        (h_inner_int_bound y).sub (hA_int y)
      have h_ae_nonneg : 0 ≤ᵐ[κ y]
          fun x => (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2 := by
        filter_upwards [hκ_supp y] with x hx
        change 0 ≤ (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2
        linarith [hθ_secondMoment_ge y x hx]
      have h_iff := MeasureTheory.integral_pos_iff_support_of_nonneg_ae h_ae_nonneg h_int
      rw [hGI_def, h_iff]
      -- Show support ⊇ (F y \ ext) and use κ y measure.
      refine lt_of_lt_of_le hy ?_
      apply MeasureTheory.measure_mono
      intro x hx
      rcases hx with ⟨hx_in_Fy, hx_nonExt⟩
      have := h_supp_strict x ⟨hx_in_Fy, hx_nonExt⟩
      simp [Function.support, ne_of_gt this]
    -- ───────────────── Aggregate over ν ─────────────────
    -- A and gainIntegral are integrable over ν.
    have hA_meas : Measurable (fun y => ∫ x, ‖x‖^2 ∂(κ y)) := by
      let K' : ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) := ⟨κ, hκ_meas⟩
      haveI : ProbabilityTheory.IsFiniteKernel K' :=
        ⟨1, ENNReal.one_lt_top, fun y => by
          change (κ y) Set.univ ≤ 1
          rw [(hκ_prob y).measure_univ]⟩
      have h_meas : MeasureTheory.StronglyMeasurable
          (fun p : Y × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) := by fun_prop
      exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
        (κ := K') h_meas).measurable
    have hA_int_outer : MeasureTheory.Integrable
        (fun y => ∫ x, ‖x‖^2 ∂(κ y)) ν := by
      refine MeasureTheory.Integrable.of_bound hA_meas.aestronglyMeasurable (M^2) ?_
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg
          (MeasureTheory.integral_nonneg (fun _ => by positivity))]
      haveI := hκ_prob y
      calc ∫ x, ‖x‖^2 ∂(κ y)
          ≤ ∫ _, (M^2 : ℝ) ∂(κ y) := by
            refine MeasureTheory.integral_mono_ae (hA_int y) (MeasureTheory.integrable_const _) ?_
            filter_upwards [hκ_supp y] with x hx_in_Fy
            have : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx_in_Fy)
            nlinarith [norm_nonneg x]
        _ = M^2 := by simp
    have hB_meas : Measurable
        (fun y => ∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) := by
      -- Build a kernel from `κ' y := bind κ y θ_y` and apply
      -- `integral_kernel_prod_right'` for Bochner measurability.
      let K' : ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) :=
        ⟨fun y => (κ y).bind (fun x => θ (y, x)), by
          -- This is exactly the κ' measurability from subgoal (a), reproved.
          refine MeasureTheory.Measure.measurable_of_measurable_coe _ fun s hs => ?_
          have h_bind_apply : ∀ y,
              ((κ y).bind (fun x => θ (y, x))) s = ∫⁻ x, θ (y, x) s ∂(κ y) := by
            intro y
            refine MeasureTheory.Measure.bind_apply hs ?_
            exact (hθ_meas.comp measurable_prodMk_left).aemeasurable
          simp_rw [h_bind_apply]
          let Kκ : ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) := ⟨κ, hκ_meas⟩
          haveI : ProbabilityTheory.IsFiniteKernel Kκ :=
            ⟨1, ENNReal.one_lt_top, fun y => by
              change (κ y) Set.univ ≤ 1
              rw [(hκ_prob y).measure_univ]⟩
          have hf_meas : Measurable
              (Function.uncurry
                (fun (y : Y) (x : EuclideanSpace ℝ (Fin n)) => θ (y, x) s)) :=
            (MeasureTheory.Measure.measurable_coe hs).comp hθ_meas
          exact Measurable.lintegral_kernel_prod_right (κ := Kκ) hf_meas⟩
      haveI : ProbabilityTheory.IsFiniteKernel K' := by
        refine ⟨1, ENNReal.one_lt_top, fun y => ?_⟩
        change ((κ y).bind (fun x => θ (y, x))) Set.univ ≤ 1
        haveI := hκ_prob y
        have h_prob : MeasureTheory.IsProbabilityMeasure ((κ y).bind (fun x => θ (y, x))) := by
          refine MeasureTheory.isProbabilityMeasure_bind
            (hθ_meas.comp measurable_prodMk_left).aemeasurable ?_
          exact Filter.Eventually.of_forall fun x => h_θ_prob (y, x)
        rw [h_prob.measure_univ]
      have h_meas : MeasureTheory.StronglyMeasurable
          (fun p : Y × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) := by fun_prop
      exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
        (κ := K') h_meas).measurable
    have hB_int_outer : MeasureTheory.Integrable
        (fun y => ∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) ν := by
      refine MeasureTheory.Integrable.of_bound hB_meas.aestronglyMeasurable (M^2 + M^2) ?_
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg
          (MeasureTheory.integral_nonneg (fun _ => by positivity))]
      rw [h_B_eq y]
      have h_gain_bound : gainIntegral y ≤ M^2 := by
        haveI := hκ_prob y
        calc gainIntegral y
            ≤ ∫ x, M^2 ∂(κ y) := by
              refine MeasureTheory.integral_mono_ae
                ((h_inner_int_bound y).sub (hA_int y)) (MeasureTheory.integrable_const _) ?_
              filter_upwards [hκ_supp y] with x hx_in_Fy
              have h1 : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx_in_Fy)
              have h2 : ‖x‖^2 ≤ M^2 := by nlinarith [norm_nonneg x]
              -- ∫ x', ‖x'‖² ∂θ ≤ M² (proved similarly to inner_int_bound)
              have h_θ_supp : ∀ᵐ x' ∂(θ (y, x)), x' ∈ F y := by
                by_cases h_ext : x ∈ Set.extremePoints ℝ (F y)
                · have h_θ_eq : θ (y, x) = MeasureTheory.Measure.dirac x := by
                    rw [hθ_def]; simp [h_ext]
                  rw [h_θ_eq]
                  exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr hx_in_Fy
                · have h_patched : patchedEval F z₀ (y, x) = x := by
                    classical
                    unfold patchedEval
                    simp [hx_in_Fy]
                  have h_pe_nonext :
                      patchedEval F z₀ (y, x) ∉ Set.extremePoints ℝ (F (y, x).1) := by
                    rw [h_patched]; exact h_ext
                  obtain ⟨h_fwd_in, h_bwd_in, _⟩ := hd_ε (y, x) h_pe_nonext
                  rw [h_patched] at h_fwd_in h_bwd_in
                  have h_θ_eq :
                      θ (y, x) = twoPointSpread x (d (y, x)) (ε (y, x)) := by
                    rw [hθ_def]; simp [h_ext]
                  rw [h_θ_eq]
                  unfold twoPointSpread
                  rw [MeasureTheory.ae_add_measure_iff]
                  have h_half_ne : (1/2 : ℝ≥0∞) ≠ 0 := by norm_num
                  refine ⟨?_, ?_⟩
                  · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
                    exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_fwd_in
                  · rw [MeasureTheory.Measure.ae_ennreal_smul_measure_iff h_half_ne]
                    exact (MeasureTheory.ae_dirac_iff (hFy_meas y)).mpr h_bwd_in
              haveI := h_θ_prob (y, x)
              have h_θ_sqInt : MeasureTheory.Integrable
                  (fun x' => ‖x'‖^2) (θ (y, x)) := by
                refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
                filter_upwards [h_θ_supp] with x' hx'
                have : ‖x'‖ ≤ M := hM_K x' (hF_sub_K y hx')
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                nlinarith [norm_nonneg x']
              have h_θ_bdd : (∫ x', ‖x'‖^2 ∂(θ (y, x))) ≤ M^2 := by
                calc ∫ x', ‖x'‖^2 ∂(θ (y, x))
                    ≤ ∫ _, M^2 ∂(θ (y, x)) := by
                      refine MeasureTheory.integral_mono_ae h_θ_sqInt
                        (MeasureTheory.integrable_const _) ?_
                      filter_upwards [h_θ_supp] with x' hx'
                      have : ‖x'‖ ≤ M := hM_K x' (hF_sub_K y hx')
                      nlinarith [norm_nonneg x']
                  _ = M^2 := by simp
              change (∫ x', ‖x'‖^2 ∂(θ (y, x))) - ‖x‖^2 ≤ M^2
              linarith [sq_nonneg ‖x‖]
          _ = M^2 := by simp
      have hA_bound : ∫ x, ‖x‖^2 ∂(κ y) ≤ M^2 := by
        haveI := hκ_prob y
        calc ∫ x, ‖x‖^2 ∂(κ y)
            ≤ ∫ _, (M^2 : ℝ) ∂(κ y) := by
              refine MeasureTheory.integral_mono_ae (hA_int y)
                (MeasureTheory.integrable_const _) ?_
              filter_upwards [hκ_supp y] with x hx_in_Fy
              have : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx_in_Fy)
              nlinarith [norm_nonneg x]
          _ = M^2 := by simp
      linarith [h_gain_nonneg y]
    -- ───────────────── Final strict inequality ─────────────────
    -- ∫ y, B(y) ∂ν - ∫ y, A(y) ∂ν = ∫ y, gainIntegral(y) ∂ν > 0.
    have h_diff_eq :
        (∫ y, (∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) ∂ν) -
          (∫ y, (∫ x, ‖x‖^2 ∂(κ y)) ∂ν) =
        ∫ y, gainIntegral y ∂ν := by
      rw [← MeasureTheory.integral_sub hB_int_outer hA_int_outer]
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall fun y => ?_
      change (∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) -
            (∫ x, ‖x‖^2 ∂(κ y)) = gainIntegral y
      rw [h_B_eq y]; ring
    -- Show ∫ y, gainIntegral(y) ∂ν > 0.
    -- Integrability of gainIntegral via gainIntegral = B - A.
    have h_gain_outer_int : MeasureTheory.Integrable gainIntegral ν := by
      have : gainIntegral =
          (fun y => ∫ x', ‖x'‖^2 ∂(((κ y).bind (fun x => θ (y, x))))) -
          (fun y => ∫ x, ‖x‖^2 ∂(κ y)) := by
        funext y; simp [hGI_def, h_B_eq y]
      rw [this]
      exact hB_int_outer.sub hA_int_outer
    have h_gain_ae_nonneg : 0 ≤ᵐ[ν] gainIntegral :=
      Filter.Eventually.of_forall h_gain_nonneg
    have h_gain_pos_set : 0 < ν (Function.support gainIntegral) := by
      refine lt_of_lt_of_le hκ_nonExt ?_
      apply MeasureTheory.measure_mono
      intro y hy
      have hpos : 0 < gainIntegral y := h_gain_pos_of_nonExt y hy
      simp [Function.support, ne_of_gt hpos]
    have h_gain_pos :=
      (MeasureTheory.integral_pos_iff_support_of_nonneg_ae h_gain_ae_nonneg
        h_gain_outer_int).mpr h_gain_pos_set
    linarith [h_diff_eq, h_gain_pos]

/-! ## Existence of a cost-maximizing kernel

Among all measurable kernels `κ : Y → Measure ℝⁿ` with `κ y` a probability measure supported in
`F y` and conditional mean `z₀ y` `ν`-a.e., there is one maximizing the integrated second moment
`∫ y, ∫ x, ‖x‖² ∂(κ y) ∂ν`. The argument lifts an admissible kernel to an admissible joint measure
`ν ⊗ₘ κ̂`, takes a maximizer of the joint cost on the narrow-compact admissible set, and
disintegrates it back to a kernel, comparing costs through the compProd cost equality. -/

/-- A kernel `κ : Y → Measure ℝⁿ` is *admissible* if it is measurable, each `κ y` is a probability
measure supported in `F y` for all `y`, and the conditional mean equals `z₀ y` `ν`-a.e. -/
private def IsAdmissibleKernel
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (F : Y → Set (EuclideanSpace ℝ (Fin n)))
    (z₀ : Y → EuclideanSpace ℝ (Fin n))
    (ν : MeasureTheory.Measure Y)
    (κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  Measurable κ ∧
  (∀ y, MeasureTheory.IsProbabilityMeasure (κ y)) ∧
  (∀ y, ∀ᵐ x ∂(κ y), x ∈ F y) ∧
  (∀ᵐ y ∂ν, ∫ x, x ∂(κ y) = z₀ y)

/-- A joint measure `π` on `Y × ℝⁿ` is *admissible* if it is a finite measure with first marginal
`ν`, supported on `Graph(F)`, and with conditional mean `z₀` in the set-restricted form
`∫ p in A ×ˢ univ, p.2 ∂π = ∫ y in A, z₀ y ∂ν` for every measurable `A ⊆ Y`. -/
private def IsAdmissibleJointMeasure
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (F : Y → Set (EuclideanSpace ℝ (Fin n)))
    (z₀ : Y → EuclideanSpace ℝ (Fin n))
    (ν : MeasureTheory.Measure Y)
    (π : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))) : Prop :=
  MeasureTheory.IsFiniteMeasure π ∧
  π.fst = ν ∧
  (∀ᵐ p ∂π, p.2 ∈ F p.1) ∧
  (∀ A : Set Y, MeasurableSet A →
    ∫ p in (A ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))), p.2 ∂π =
      ∫ y in A, z₀ y ∂ν)

/-- Cost functional on kernels. -/
private noncomputable def kernelCost
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (ν : MeasureTheory.Measure Y)
    (κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ y, ∫ x, ‖x‖^2 ∂(κ y) ∂ν

/-- Cost functional on joint measures. -/
private noncomputable def jointCost
    {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (π : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ p, ‖p.2‖^2 ∂π

/-- Existence of a cost-maximizing admissible joint measure on `Y × ℝⁿ`, obtained from narrow
compactness of the admissible set and narrow continuity of `π ↦ ∫ ‖x‖² dπ`. -/
private lemma exists_optimal_joint_measure
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν] :
    ∃ π : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n)),
      IsAdmissibleJointMeasure F z₀ ν π ∧
      ∀ π' : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n)),
        IsAdmissibleJointMeasure F z₀ ν π' →
        jointCost π' ≤ jointCost π := by
  -- Invoke the CTF-form existence theorem.
  obtain ⟨μ_star, hμ_marg, hμ_graph, hμ_ctf, hμ_max⟩ :=
    exists_admissibleJointMeasure_max_ctf
      hK_compact hF_sub_K hF_graph_closed hz₀_meas hz₀_mem ν
  refine ⟨(μ_star : MeasureTheory.Measure _), ?_, ?_⟩
  · -- μ_star is `IsAdmissibleJointMeasure`.
    -- Convert CTF → SF via `meanPreservation_set_iff_contTest`.
    haveI hμ_star_fin : MeasureTheory.IsFiniteMeasure
        ((μ_star : MeasureTheory.FiniteMeasure _) :
          MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))) :=
      inferInstance
    -- Support a.e. on K (from F y ⊆ K and graph support).
    have hπ_supp_K_star :
        ∀ᵐ p ∂((μ_star : MeasureTheory.FiniteMeasure _) :
          MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))), p.2 ∈ K := by
      have h_subset :
          {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ K} ⊆
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} := by
        intro p hp hpF; exact hp (hF_sub_K _ hpF)
      have h_zero :
          ((μ_star : MeasureTheory.FiniteMeasure _) :
              MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n)))
              {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ K} = 0 :=
        le_antisymm ((MeasureTheory.measure_mono h_subset).trans hμ_graph.le)
          (zero_le)
      rw [MeasureTheory.ae_iff]; exact h_zero
    have hz₀_in_K : ∀ y, z₀ y ∈ K := fun y => hF_sub_K y (hz₀_mem y)
    have hSF_star :
        ∀ A : Set Y, MeasurableSet A →
          ∫ p in A ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n))), p.2
              ∂((μ_star : MeasureTheory.FiniteMeasure _) :
                MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))) =
            ∫ y in A, z₀ y ∂ν :=
      (meanPreservation_set_iff_contTest
        hK_compact hz₀_meas hz₀_in_K ν hμ_marg hπ_supp_K_star).mpr hμ_ctf
    refine ⟨inferInstance, hμ_marg, ?_, hSF_star⟩
    -- ν-a.e. graph constraint from zero measure.
    rw [MeasureTheory.ae_iff]; exact hμ_graph
  · -- Maximality.
    intro π' hπ'_adm
    obtain ⟨hπ'_fin, hπ'_marg, hπ'_supp_F, hπ'_SF⟩ := hπ'_adm
    haveI : MeasureTheory.IsFiniteMeasure π' := hπ'_fin
    -- Build FiniteMeasure wrapper.
    let π'_FM : MeasureTheory.FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) :=
      ⟨π', inferInstance⟩
    -- Convert SF → CTF.
    have hπ'_supp_K : ∀ᵐ p ∂π', p.2 ∈ K := by
      filter_upwards [hπ'_supp_F] with p hp; exact hF_sub_K _ hp
    have hz₀_in_K : ∀ y, z₀ y ∈ K := fun y => hF_sub_K y (hz₀_mem y)
    have hπ'_CTF :
        ∀ φ : BoundedContinuousFunction Y ℝ,
          ∫ p, φ p.1 • p.2 ∂π' = ∫ y, φ y • z₀ y ∂ν :=
      (meanPreservation_set_iff_contTest
        hK_compact hz₀_meas hz₀_in_K ν hπ'_marg hπ'_supp_K).mp hπ'_SF
    -- Graph constraint as zero measure.
    have hπ'_graph_zero :
        π' {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 := by
      rw [← MeasureTheory.ae_iff]; exact hπ'_supp_F
    exact hμ_max π'_FM hπ'_marg hπ'_graph_zero hπ'_CTF

/-- Lifting an admissible kernel to an admissible joint measure via `compProd` with the reference
measure `ν`. -/
private lemma compProd_admissible_of_admissibleKernel
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    {κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))}
    (hκ_adm : IsAdmissibleKernel F z₀ ν κ) :
    IsAdmissibleJointMeasure F z₀ ν
      (ν ⊗ₘ (⟨κ, hκ_adm.1⟩ :
        ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)))) := by
  have hκ_meas := hκ_adm.1
  have hκ_prob := hκ_adm.2.1
  have hκ_supp := hκ_adm.2.2.1
  have hκ_mean := hκ_adm.2.2.2
  let kappaHat : ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) :=
    ⟨κ, hκ_adm.1⟩
  change IsAdmissibleJointMeasure F z₀ ν (ν ⊗ₘ kappaHat)
  haveI hkappaHat_markov : ProbabilityTheory.IsMarkovKernel kappaHat :=
    ⟨fun y => hκ_prob y⟩
  haveI hν_sfinite : MeasureTheory.SFinite ν := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i) `IsFiniteMeasure (ν ⊗ₘ κ̂)`.
    infer_instance
  · -- (ii) `(ν ⊗ₘ κ̂).fst = ν`.
    exact MeasureTheory.Measure.fst_compProd ν kappaHat
  · -- (iii) `∀ᵐ p ∂(ν ⊗ₘ κ̂), p.2 ∈ F p.1`.
    refine MeasureTheory.Measure.ae_compProd_of_ae_ae hF_graph_meas ?_
    exact Filter.Eventually.of_forall hκ_supp
  · -- (iv) Mean preservation in set-restricted form.
    intro A hA
    -- Bound `M` on K.
    obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
      hK_compact.isBounded.exists_norm_le
    have h_snd_meas : Measurable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) := measurable_snd
    -- Inner integral integrability (for each y, x ↦ x is integrable against κ y).
    have h_inner_int : ∀ y, MeasureTheory.Integrable (fun x => x) (κ y) := by
      intro y
      haveI := hκ_prob y
      refine MeasureTheory.Integrable.of_bound (by fun_prop) M ?_
      filter_upwards [hκ_supp y] with x hx
      exact hM_K x (hF_sub_K y hx)
    -- Joint integrability of `fun p => p.2` w.r.t. `ν ⊗ₘ κ̂`.
    have h_joint_int : MeasureTheory.Integrable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) (ν ⊗ₘ kappaHat) := by
      refine MeasureTheory.Integrable.of_bound h_snd_meas.aestronglyMeasurable M ?_
      have h_bound_meas : MeasurableSet
          {p : Y × EuclideanSpace ℝ (Fin n) | ‖p.2‖ ≤ M} :=
        measurableSet_le h_snd_meas.norm measurable_const
      refine MeasureTheory.Measure.ae_compProd_of_ae_ae h_bound_meas ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      filter_upwards [hκ_supp y] with x hx
      exact hM_K x (hF_sub_K y hx)
    rw [show (A ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) =
          (A ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) from rfl]
    rw [MeasureTheory.Measure.setIntegral_compProd hA MeasurableSet.univ
      h_joint_int.integrableOn]
    -- ∫ y in A, ∫ x in univ, x ∂κ̂ y ∂ν = ∫ y in A, ∫ x, x ∂κ y ∂ν
    simp only [MeasureTheory.Measure.restrict_univ]
    refine MeasureTheory.setIntegral_congr_ae hA ?_
    filter_upwards [hκ_mean] with y hy _
    exact hy

/-- Disintegrating an admissible joint measure to a kernel that is admissible `ν`-a.e.: Its
conditional kernel is measurable, a probability measure for each `y`, supported on `F y` for
`ν`-a.e. `y`, and has barycenter `z₀ y` for `ν`-a.e. `y`. -/
private lemma condKernel_ae_admissible_of_admissibleJoint
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    -- Kept for signature parity with the sibling `exists_admissibleKernel_of_admissibleJoint`,
    -- which consumes graph measurability directly; here the support claim comes from `hπ_adm`.
    (_hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    {π : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))}
    [MeasureTheory.IsFiniteMeasure π]
    (hπ_adm : IsAdmissibleJointMeasure F z₀ ν π) :
    Measurable (fun y => π.condKernel y) ∧
    (∀ y, MeasureTheory.IsProbabilityMeasure (π.condKernel y)) ∧
    (∀ᵐ y ∂ν, ∀ᵐ x ∂(π.condKernel y), x ∈ F y) ∧
    (∀ᵐ y ∂ν, ∫ x, x ∂(π.condKernel y) = z₀ y) := by
  obtain ⟨_, hπ_fst, hπ_supp, hπ_mean⟩ := hπ_adm
  -- Common bound: ∀ x ∈ K, ‖x‖ ≤ M.
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  -- The support-a.e. claim, used twice.
  have h_supp_ae : ∀ᵐ y ∂ν, ∀ᵐ x ∂(π.condKernel y), x ∈ F y := by
    have h_eq : π = π.fst ⊗ₘ π.condKernel := (π.disintegrate π.condKernel).symm
    have h_ae_cp : ∀ᵐ p ∂(π.fst ⊗ₘ π.condKernel), p.2 ∈ F p.1 := h_eq ▸ hπ_supp
    have h_ae_ae : ∀ᵐ y ∂π.fst, ∀ᵐ x ∂(π.condKernel y), x ∈ F y :=
      MeasureTheory.Measure.ae_ae_of_ae_compProd h_ae_cp
    rw [hπ_fst] at h_ae_ae
    exact h_ae_ae
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Measurability of `fun y => π.condKernel y`.
    exact π.condKernel.measurable
  · -- IsProbabilityMeasure for each y, from the Markov instance.
    intro y; infer_instance
  · -- Support a.e.: already prepared.
    exact h_supp_ae
  · -- Mean a.e.: setIntegral equality on every measurable set + Integrable.ae_eq.
    -- Joint integrability of `fun p => p.2`.
    have h_joint_int : MeasureTheory.Integrable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) π := by
      refine MeasureTheory.Integrable.of_bound
        measurable_snd.aestronglyMeasurable M ?_
      filter_upwards [hπ_supp] with p hp
      exact hM_K _ (hF_sub_K _ hp)
    -- AEStronglyMeasurable of the inner integral w.r.t. ν.
    have h_aesm_inner : MeasureTheory.AEStronglyMeasurable
        (fun y => ∫ x, x ∂(π.condKernel y)) ν := by
      have := h_joint_int.aestronglyMeasurable.integral_condKernel
      rwa [hπ_fst] at this
    -- ν-a.e. bound `‖∫ x ∂(π.condKernel y)‖ ≤ M`, hence integrability of inner integral.
    have h_int_lhs : MeasureTheory.Integrable
        (fun y => ∫ x, x ∂(π.condKernel y)) ν := by
      refine MeasureTheory.Integrable.of_bound h_aesm_inner M ?_
      filter_upwards [h_supp_ae] with y hy_supp
      have h_bd : ∀ᵐ x ∂(π.condKernel y), ‖x‖ ≤ M := by
        filter_upwards [hy_supp] with x hx; exact hM_K _ (hF_sub_K _ hx)
      haveI : MeasureTheory.IsProbabilityMeasure (π.condKernel y) := inferInstance
      have h_norm_le : ‖∫ x, x ∂(π.condKernel y)‖ ≤ ∫ x, ‖x‖ ∂(π.condKernel y) :=
        MeasureTheory.norm_integral_le_integral_norm _
      have h_norm_int : MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (π.condKernel y) := by
        refine MeasureTheory.Integrable.of_bound (by fun_prop) M ?_
        filter_upwards [h_bd] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hx
      have h_int_le : ∫ x, ‖x‖ ∂(π.condKernel y) ≤ M := by
        calc ∫ x, ‖x‖ ∂(π.condKernel y)
            ≤ ∫ _, (M : ℝ) ∂(π.condKernel y) :=
              MeasureTheory.integral_mono_ae h_norm_int
                (MeasureTheory.integrable_const M) h_bd
          _ = M := by simp
      linarith
    -- Integrability of `z₀`.
    have h_int_z₀ : MeasureTheory.Integrable z₀ ν := by
      refine MeasureTheory.Integrable.of_bound hz₀_meas.aestronglyMeasurable M ?_
      exact Filter.Eventually.of_forall fun y => hM_K _ (hF_sub_K _ (hz₀_mem y))
    -- setIntegral equality on every measurable set, from setIntegral_condKernel + hπ_mean.
    have h_setInt_eq : ∀ A : Set Y, MeasurableSet A →
        ∫ y in A, ∫ x, x ∂(π.condKernel y) ∂ν = ∫ y in A, z₀ y ∂ν := by
      intro A hA
      have h_int_on : MeasureTheory.IntegrableOn
          (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2)
          (A ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) π :=
        h_joint_int.integrableOn
      have h_eq := MeasureTheory.Measure.setIntegral_condKernel
        (ρ := π) hA MeasurableSet.univ h_int_on
      simp only [MeasureTheory.Measure.restrict_univ] at h_eq
      rw [hπ_fst] at h_eq
      rw [h_eq]
      exact hπ_mean A hA
    -- a.e. equality via `Integrable.ae_eq_of_forall_setIntegral_eq`.
    refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq _ _ h_int_lhs h_int_z₀ ?_
    intro A hA _; exact h_setInt_eq A hA

/-- From an admissible joint measure, an admissible kernel (support for all `y`, not merely
`ν`-a.e.) with the same cost, obtained by replacing the conditional kernel with the Dirac mass at
`z₀ y` on the `ν`-null set where the support fails. -/
private lemma exists_admissibleKernel_of_admissibleJoint
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    {π : MeasureTheory.Measure (Y × EuclideanSpace ℝ (Fin n))}
    [MeasureTheory.IsFiniteMeasure π]
    (hπ_adm : IsAdmissibleJointMeasure F z₀ ν π) :
    ∃ κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      IsAdmissibleKernel F z₀ ν κ ∧
      kernelCost ν κ = jointCost π := by
  classical
  obtain ⟨hcond_meas, hcond_prob, hcond_supp, hcond_mean⟩ :=
    condKernel_ae_admissible_of_admissibleJoint
      hK_compact hF_sub_K hF_graph_meas hz₀_meas hz₀_mem ν hπ_adm
  obtain ⟨_, hπ_fst, hπ_supp, _⟩ := hπ_adm
  -- Bad set: y where π.condKernel y is NOT a.e.-supported on F y.
  let bad : Set (Y × EuclideanSpace ℝ (Fin n)) :=
    {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}
  have h_bad_meas : MeasurableSet bad := hF_graph_meas.compl
  let N : Set Y := {y | (π.condKernel y) (Prod.mk y ⁻¹' bad) ≠ 0}
  have hN_meas : MeasurableSet N := by
    have hf_meas : Measurable fun y => (π.condKernel y) (Prod.mk y ⁻¹' bad) :=
      Kernel.measurable_kernel_prodMk_left h_bad_meas
    exact hf_meas (measurableSet_singleton 0).compl
  have hN_null : ν N = 0 := by
    rw [← MeasureTheory.ae_iff]
    filter_upwards [hcond_supp] with y hy
    -- hy : ∀ᵐ x ∂(π.condKernel y), x ∈ F y; want (π.condKernel y) (Prod.mk y ⁻¹' bad) = 0.
    rw [MeasureTheory.ae_iff] at hy
    convert hy using 1
  -- Define `κ y := if y ∈ N then dirac (z₀ y) else π.condKernel y`.
  let κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    fun y => if y ∈ N then MeasureTheory.Measure.dirac (z₀ y) else π.condKernel y
  -- Bound on `K`.
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  refine ⟨κ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- Measurability of κ.
    refine Measurable.ite hN_meas ?_ hcond_meas
    exact MeasureTheory.Measure.measurable_dirac.comp hz₀_meas
  · -- IsProbabilityMeasure (κ y) for all y.
    intro y
    by_cases hy : y ∈ N
    · simp only [κ, hy, if_true]; exact MeasureTheory.Measure.dirac.isProbabilityMeasure
    · simp only [κ, hy, if_false]; exact hcond_prob y
  · -- Support ∀ y.
    intro y
    by_cases hy : y ∈ N
    · -- κ y = dirac (z₀ y), z₀ y ∈ F y.
      simp only [κ, hy, if_true]
      have h_meas_F : MeasurableSet (F y) := by
        have : MeasurableSet (Prod.mk y ⁻¹' {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) :=
          measurable_prodMk_left hF_graph_meas
        convert this
      exact (MeasureTheory.ae_dirac_iff h_meas_F).mpr (hz₀_mem y)
    · -- κ y = π.condKernel y; y ∉ N gives (π.condKernel y) (Prod.mk y ⁻¹' bad) = 0.
      simp only [κ, hy, if_false]
      have h0 : (π.condKernel y) (Prod.mk y ⁻¹' bad) = 0 := by
        by_contra h; exact hy h
      rw [MeasureTheory.ae_iff]
      convert h0 using 1
  · -- Mean ν-a.e.
    filter_upwards [hcond_mean] with y hy_mean
    by_cases hy : y ∈ N
    · simp only [κ, hy, if_true]; rw [MeasureTheory.integral_dirac]
    · simp only [κ, hy, if_false]; exact hy_mean
  · -- Cost equality.
    unfold kernelCost jointCost
    -- Integrability of `‖p.2‖²` against π.
    have h_joint_int_sq : MeasureTheory.Integrable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) π := by
      refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
      filter_upwards [hπ_supp] with p hp
      have h1 : ‖p.2‖ ≤ M := hM_K _ (hF_sub_K _ hp)
      have h2 : 0 ≤ ‖p.2‖ := norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; nlinarith
    -- Disintegration of the cost integral.
    have h_dis : ∫ p, ‖p.2‖^2 ∂π
        = ∫ y, ∫ x, ‖x‖^2 ∂(π.condKernel y) ∂ν := by
      have := MeasureTheory.Measure.integral_condKernel (ρ := π) h_joint_int_sq
      rw [hπ_fst] at this
      exact this.symm
    rw [h_dis]
    -- ν-a.e. on `Nᶜ`, κ y = π.condKernel y, so integrands agree.
    refine MeasureTheory.integral_congr_ae ?_
    have hN_ae : ∀ᵐ y ∂ν, y ∉ N := by rw [MeasureTheory.ae_iff]; simpa using hN_null
    filter_upwards [hN_ae] with y hy
    simp only [κ, hy, if_false]

/-- Cost equality between an admissible kernel and its compProd joint measure. -/
private lemma kernelCost_eq_jointCost_compProd
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν]
    {κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))}
    (hκ_adm : IsAdmissibleKernel F z₀ ν κ) :
    kernelCost ν κ =
      jointCost
        (ν ⊗ₘ (⟨κ, hκ_adm.1⟩ :
          ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)))) := by
  have hκ_meas := hκ_adm.1
  have hκ_prob := hκ_adm.2.1
  have hκ_supp := hκ_adm.2.2.1
  set kappaHat: ProbabilityTheory.Kernel Y (EuclideanSpace ℝ (Fin n)) :=
    ⟨κ, hκ_adm.1⟩ with hkappaHat_def
  haveI hkappaHat_markov : ProbabilityTheory.IsMarkovKernel kappaHat := ⟨fun y => hκ_prob y⟩
  -- Bound `M` on `K`: ∀ x ∈ K, ‖x‖ ≤ M.
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  -- Integrand `f (y, x) = ‖x‖²` and its measurability.
  set f : Y × EuclideanSpace ℝ (Fin n) → ℝ := fun p => ‖p.2‖^2 with hf_def
  have hf_meas : Measurable f := by fun_prop
  -- Pointwise integrability against `κ y`: bounded by M².
  have h_inner_int : ∀ y, MeasureTheory.Integrable (fun x => ‖x‖^2) (κ y) := by
    intro y
    haveI := hκ_prob y
    refine MeasureTheory.Integrable.of_bound (by fun_prop) (M^2) ?_
    filter_upwards [hκ_supp y] with x hx
    have h1 : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx)
    have h2 : 0 ≤ ‖x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  -- Joint integrability of `f` w.r.t. `ν ⊗ₘ κ̂`.
  have h_joint_int : MeasureTheory.Integrable f (ν ⊗ₘ kappaHat) := by
    -- ‖f‖ ≤ M² (ν ⊗ₘ κ̂)-a.e., since for ν-a.e. y, κ y supported on F y ⊆ K.
    refine MeasureTheory.Integrable.of_bound hf_meas.aestronglyMeasurable (M^2) ?_
    -- Use `MeasureTheory.Measure.ae_compProd_of_ae_ae`: ∀ᵐ y ∂ν, ∀ᵐ x ∂κ̂ y, ... ⇒
    -- ∀ᵐ p ∂(ν ⊗ₘ κ̂), ... on p = (y, x).
    have h_pred_meas : MeasurableSet
        {p : Y × EuclideanSpace ℝ (Fin n) | ‖f p‖ ≤ M^2} := by
      refine measurableSet_le ?_ measurable_const
      exact hf_meas.norm
    refine MeasureTheory.Measure.ae_compProd_of_ae_ae h_pred_meas ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    filter_upwards [hκ_supp y] with x hx
    have h1 : ‖x‖ ≤ M := hM_K x (hF_sub_K y hx)
    have h2 : 0 ≤ ‖x‖ := norm_nonneg _
    change ‖f (y, x)‖ ≤ M^2
    rw [hf_def, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  change kernelCost ν κ = jointCost (ν ⊗ₘ kappaHat)
  unfold kernelCost jointCost
  rw [MeasureTheory.Measure.integral_compProd h_joint_int]
  rfl

/-- **Cost-maximizing admissible kernel.** There is a measurable admissible kernel maximizing the
integrated second moment `∫ y, ∫ x, ‖x‖² ∂(κ y) ∂ν` over all admissible kernels. -/
lemma exists_optimal_kernel
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    -- Standing convexity assumption of the moment-persuasion problem, kept on the public
    -- signature for parity with the rest of the assembly; this step routes through the
    -- closed-graph maximizer and the disintegration, neither of which needs it directly.
    (_hF_convex : ∀ y, Convex ℝ (F y))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν] :
    ∃ κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      Measurable κ ∧
      (∀ y, MeasureTheory.IsProbabilityMeasure (κ y)) ∧
      (∀ y, ∀ᵐ x ∂(κ y), x ∈ F y) ∧
      (∀ᵐ y ∂ν, ∫ x, x ∂(κ y) = z₀ y) ∧
      ∀ κ' : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
        Measurable κ' →
        (∀ y, MeasureTheory.IsProbabilityMeasure (κ' y)) →
        (∀ y, ∀ᵐ x ∂(κ' y), x ∈ F y) →
        (∀ᵐ y ∂ν, ∫ x, x ∂(κ' y) = z₀ y) →
        ∫ y, ∫ x, ‖x‖^2 ∂(κ' y) ∂ν ≤ ∫ y, ∫ x, ‖x‖^2 ∂(κ y) ∂ν := by
  -- Graph measurability (from closed graph).
  have hF_graph_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} :=
    hF_graph_closed.measurableSet
  obtain ⟨π_star, hπ_adm, hπ_max⟩ :=
    exists_optimal_joint_measure hK_compact hF_sub_K hF_graph_closed hz₀_meas hz₀_mem ν
  haveI hπ_fin : MeasureTheory.IsFiniteMeasure π_star := hπ_adm.1
  obtain ⟨κ, hκ_adm, hκ_cost⟩ :=
    exists_admissibleKernel_of_admissibleJoint hK_compact hF_sub_K hF_graph_meas
      hz₀_meas hz₀_mem ν hπ_adm
  obtain ⟨hκ_meas, hκ_prob, hκ_supp, hκ_mean⟩ := hκ_adm
  refine ⟨κ, hκ_meas, hκ_prob, hκ_supp, hκ_mean, ?_⟩
  intro κ' hκ'_meas hκ'_prob hκ'_supp hκ'_mean
  -- Convert κ'-admissibility to bundle.
  have hκ'_adm : IsAdmissibleKernel F z₀ ν κ' :=
    ⟨hκ'_meas, hκ'_prob, hκ'_supp, hκ'_mean⟩
  -- Lift κ' to admissible joint π' := ν ⊗ₘ κ̂'.
  have hπ'_adm :=
    compProd_admissible_of_admissibleKernel hK_compact hF_sub_K hF_graph_meas
      (z₀ := z₀) ν hκ'_adm
  -- Cost equality for κ' ↔ π'.
  have hκ'_cost :=
    kernelCost_eq_jointCost_compProd hK_compact hF_sub_K ν hκ'_adm
  -- Cost comparison: jointCost π' ≤ jointCost π_star.
  have h_joint_le := hπ_max _ hπ'_adm
  change kernelCost ν κ' ≤ kernelCost ν κ
  rw [hκ'_cost, hκ_cost]
  exact h_joint_le

/-! ## A.e.-extreme-point-supported Carathéodory kernel -/

/-- A.e.-extreme-point-supported measurable Carathéodory kernel.

For a closed-graph compact-bound convex-fiber multifunction `F : Y → Set ℝⁿ`, a measurable
barycenter `z₀`, and a finite reference measure `ν`, there is a measurable kernel
`κ : Y → Measure ℝⁿ` such that `ν`-a.e. `y`, `κ y` is a probability measure supported on
`extremePoints (F y)` with mean `z₀ y`. -/
theorem exists_measurable_caratheodory_kernel_ae
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (hz₀_meas : Measurable z₀) (hz₀_mem : ∀ y, z₀ y ∈ F y)
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasure ν] :
    ∃ κ : Y → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      Measurable κ ∧
      (∀ y, MeasureTheory.IsProbabilityMeasure (κ y)) ∧
      ∀ᵐ y ∂ν,
        (κ y) (Set.extremePoints ℝ (F y)) = 1 ∧
        ∫ x, x ∂(κ y) = z₀ y := by
  obtain ⟨κ, hκ_meas, hκ_prob, hκ_supp, hκ_mean, hκ_opt⟩ :=
    exists_optimal_kernel hK_compact hF_sub_K hF_graph_closed hF_convex
      hz₀_meas hz₀_mem ν
  -- must be zero, else `exists_strict_improvement_of_nonextreme_kernel` gives a
  -- strictly better kernel, contradicting `hκ_opt`.
  have h_no_nonext_meas :
      ν {y | 0 < (κ y) ((F y) \ Set.extremePoints ℝ (F y))} = 0 := by
    by_contra h_ne
    have h_pos : 0 < ν {y | 0 < (κ y) ((F y) \ Set.extremePoints ℝ (F y))} :=
      pos_iff_ne_zero.mpr h_ne
    obtain ⟨κ', hκ'_meas, hκ'_prob, hκ'_supp, hκ'_mean, hκ'_gain⟩ :=
      exists_strict_improvement_of_nonextreme_kernel
        hK_compact hF_sub_K hF_graph_closed hF_convex hz₀_meas hz₀_mem
        ν κ hκ_meas hκ_prob hκ_supp hκ_mean h_pos
    have h_le := hκ_opt κ' hκ'_meas hκ'_prob hκ'_supp hκ'_mean
    linarith
  have h_no_nonext_ae :
      ∀ᵐ y ∂ν, (κ y) ((F y) \ Set.extremePoints ℝ (F y)) = 0 := by
    rw [MeasureTheory.ae_iff]
    have h_set_eq :
        {y | ¬ (κ y) ((F y) \ Set.extremePoints ℝ (F y)) = 0} =
        {y | 0 < (κ y) ((F y) \ Set.extremePoints ℝ (F y))} := by
      ext y
      exact pos_iff_ne_zero.symm
    rw [h_set_eq]
    exact h_no_nonext_meas
  --   - `(κ y)(F y \ ext) = 0`  (from `h_no_nonext_ae`)
  --   - `(κ y)(F y) = 1`        (from `hκ_supp y` + probability)
  --   - `(κ y)(F y) = (κ y)(F y ∩ ext) + (κ y)(F y \ ext)` (measure split)
  -- to conclude `(κ y)(ext F y) = 1` via `F y ∩ ext F y = ext F y`.
  refine ⟨κ, hκ_meas, hκ_prob, ?_⟩
  -- Graph measurability for fibre arguments.
  have h_ext_graph_meas : MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ Set.extremePoints ℝ (F p.1)} :=
    measurableSet_extremePoints_graph hK_compact hF_sub_K hF_graph_closed hF_convex
  filter_upwards [h_no_nonext_ae, hκ_mean] with y hy_no_nonext hy_mean
  refine ⟨?_, hy_mean⟩
  -- Section of the closed graph at `y` is closed.
  have hF_y_closed : IsClosed (F y) := by
    have h_eq : F y = {x | (y, x) ∈ {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}} := by
      ext x; simp
    rw [h_eq]
    exact hF_graph_closed.preimage (by fun_prop)
  have hF_y_meas : MeasurableSet (F y) := hF_y_closed.measurableSet
  -- Fibre of the extreme-points graph at `y` is measurable.
  have h_ext_y_meas : MeasurableSet (Set.extremePoints ℝ (F y)) := by
    have h_eq : Set.extremePoints ℝ (F y) =
        {x | (y, x) ∈
          {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ Set.extremePoints ℝ (F p.1)}} := by
      ext x; simp
    rw [h_eq]
    exact measurable_prodMk_left h_ext_graph_meas
  -- `(κ y)(F y) = 1`.
  have h_kappa_y_F : (κ y) (F y) = 1 := by
    have h_univ : (κ y) Set.univ = 1 := (hκ_prob y).measure_univ
    have h_compl : (κ y) (F y)ᶜ = 0 := by
      have := hκ_supp y
      rwa [MeasureTheory.ae_iff] at this
    have h_split : (κ y) Set.univ = (κ y) (F y) + (κ y) (F y)ᶜ := by
      rw [← MeasureTheory.measure_add_measure_compl hF_y_meas]
    rw [h_univ, h_compl, add_zero] at h_split
    exact h_split.symm
  -- `(κ y)(F y) = (κ y)(F y ∩ ext) + (κ y)(F y \ ext)`.
  have h_split_ext :
      (κ y) (F y) =
        (κ y) (F y ∩ Set.extremePoints ℝ (F y)) +
        (κ y) (F y \ Set.extremePoints ℝ (F y)) :=
    (MeasureTheory.measure_inter_add_diff (F y) h_ext_y_meas).symm
  have h_inter_one : (κ y) (F y ∩ Set.extremePoints ℝ (F y)) = 1 := by
    rw [h_kappa_y_F, hy_no_nonext, add_zero] at h_split_ext
    exact h_split_ext.symm
  -- `F y ∩ ext F y = ext F y` since `ext F y ⊆ F y`.
  have h_ext_sub : Set.extremePoints ℝ (F y) ⊆ F y := extremePoints_subset
  rwa [Set.inter_eq_right.mpr h_ext_sub] at h_inter_one

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
