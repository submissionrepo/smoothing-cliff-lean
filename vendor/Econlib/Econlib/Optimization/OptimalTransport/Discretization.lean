/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.FiniteFenchelMoreau
public import Econlib.Optimization.OptimalTransport.Atomization
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Finite discretization of measures over a set of atoms

This file builds the finite probability law `∑ i, lam i • δ_{atom i}` carried by a standard-simplex
weight vector and a finite collection of atoms, and records how it interacts with expectations,
continuity, pushforwards along reindexing maps, and the Kantorovich–Rubinstein distance. It then
introduces the finite objective obtained by composing a value functional `V` with this discretizing
map, together with its boundedness and upper semicontinuity in the simplex weights. This is the
discretization layer used to reduce optimal-transport duality to a finite-dimensional problem.

## Main definitions

* `simplexToProbDist` — the probability law on `Fin n` given by a simplex weight vector.
* `finiteLaw` — the pushforward law `∑ i, lam i • δ_{atom i}` on the ambient space.
* `simplexPush` — the pushforward of a simplex weight vector along a reindexing map.
* `finiteObjective` — the value functional `V` composed with `finiteLaw`.

## Main results

* `simplexToProbDist_expect`, `finiteLaw_expect`, `finiteLaw_expect_boundedContinuous` —
  expectations against the finite law.
* `continuous_finiteLaw` — continuity of `finiteLaw` in the simplex weights.
* `finiteLaw_krDist_push_le` — a Kantorovich–Rubinstein bound under reindexing.
* `finiteObjective_bdd`, `finiteObjective_usc` — boundedness and upper semicontinuity of the finite
  objective.

## Tags

discretization, simplex, Dirac measure, optimal transport, Kantorovich–Rubinstein
-/

@[expose] public section

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {n : ℕ}

/-- The probability law on `Fin n` associated with a standard-simplex vector, built as the finite
convex combination of Dirac point masses `∑ i, lam i • δ_i`. -/
noncomputable def simplexToProbDist (lam : stdSimplex ℝ (Fin n)) : ProbabilityMeasure (Fin n) :=
  ⟨∑ i, ENNReal.ofReal (lam i) • Measure.dirac i, by
    constructor
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      MeasurableSet.univ, Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem,
      Pi.one_apply, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => stdSimplex.zero_le lam i),
      stdSimplex.sum_eq_one lam, ENNReal.ofReal_one]⟩

/-- The underlying measure of `simplexToProbDist` is the weighted sum of Dirac masses. -/
@[simp] lemma simplexToProbDist_toMeasure (lam : stdSimplex ℝ (Fin n)) :
    (simplexToProbDist lam : Measure (Fin n))
      = ∑ i, ENNReal.ofReal (lam i) • Measure.dirac i := rfl

/-- The expectation of `f` against `simplexToProbDist lam` is `∑ i, lam i * f i`. -/
lemma simplexToProbDist_expect (lam : stdSimplex ℝ (Fin n)) (f : Fin n → ℝ) :
    expect (simplexToProbDist lam) f = ∑ i, lam i * f i := by
  rw [expect, simplexToProbDist_toMeasure,
    integral_finset_sum_measure (fun i _ =>
      ((integrable_dirac (a := i) (f := f) (by simp)).smul_measure
        (by simp [ENNReal.ofReal_ne_top])))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (stdSimplex.zero_le lam i),
    smul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Push a finite-simplex law through a list of atoms in the state space. -/
noncomputable def finiteLaw (atom : Fin n → Ω) (lam : stdSimplex ℝ (Fin n)) :
    ProbabilityMeasure Ω :=
  map (simplexToProbDist lam) atom (measurable_of_finite atom)

/-- The expectation of `f` against `finiteLaw atom lam` is `∑ i, lam i * f (atom i)`. -/
lemma finiteLaw_expect
    (atom : Fin n → Ω) (lam : stdSimplex ℝ (Fin n)) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f (finiteLaw atom lam).toMeasure) :
    expect (finiteLaw atom lam) f = ∑ i, lam i * f (atom i) := by
  unfold finiteLaw
  rw [expect_map (hf := measurable_of_finite atom) (hg := hf)]
  exact simplexToProbDist_expect lam (fun i => f (atom i))

/-- `finiteLaw_expect` for a bounded continuous test function. -/
lemma finiteLaw_expect_boundedContinuous
    [TopologicalSpace Ω] [CompactSpace Ω] [OpensMeasurableSpace Ω]
    (atom : Fin n → Ω) (lam : stdSimplex ℝ (Fin n))
    (f : BoundedContinuousFunction Ω ℝ) :
    expect (finiteLaw atom lam) f = ∑ i, lam i * f (atom i) :=
  finiteLaw_expect atom lam f f.continuous.aestronglyMeasurable

/-- The finite-law embedding is continuous for the weak topology on probability measures. -/
lemma continuous_finiteLaw
    [TopologicalSpace Ω] [CompactSpace Ω] [OpensMeasurableSpace Ω]
    (atom : Fin n → Ω) :
    Continuous (finiteLaw atom) := by
  rw [MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have h_eq :
      (fun lam : stdSimplex ℝ (Fin n) =>
          ∫ x, f x ∂(finiteLaw atom lam).toMeasure)
        = fun lam : stdSimplex ℝ (Fin n) => ∑ i, lam i * f (atom i) := by
    funext lam
    rw [← finiteLaw_expect_boundedContinuous atom lam f]
    rfl
  rw [h_eq]
  exact continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- The finite law is supported on the range of the atom map. -/
lemma finiteLaw_support_range [MeasurableSingletonClass Ω]
    (atom : Fin n → Ω) (lam : stdSimplex ℝ (Fin n)) :
    (finiteLaw atom lam).toMeasure (Set.range atom) = 1 := by
  unfold finiteLaw
  rw [map_toMeasure, Measure.map_apply (measurable_of_finite atom) ?_]
  · have hpre : atom ⁻¹' Set.range atom = Set.univ := by ext i; simp
    rw [hpre]
    exact measure_univ
  · exact (Set.finite_range atom).measurableSet

/-- Push simplex weights forward along a finite index map. -/
noncomputable def simplexPush (lam : stdSimplex ℝ (Fin n)) (κ : Fin n → Fin n) :
    stdSimplex ℝ (Fin n) where
  val j := ∑ i ∈ (Finset.univ : Finset (Fin n)) with κ i = j, lam i
  property := by
    classical
    constructor
    · intro j
      exact Finset.sum_nonneg fun i _hi => stdSimplex.zero_le lam i
    · rw [Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) κ (fun i => lam i)]
      exact stdSimplex.sum_eq_one lam

/-- Summing a function against the pushed-forward weights reindexes through `κ`. -/
lemma simplexPush_sum (lam : stdSimplex ℝ (Fin n)) (κ : Fin n → Fin n)
    (φ : Fin n → ℝ) :
    ∑ j, simplexPush lam κ j * φ j = ∑ i, lam i * φ (κ i) := by
  classical
  calc
    ∑ j, simplexPush lam κ j * φ j
        = ∑ j, (∑ i ∈ (Finset.univ : Finset (Fin n)) with κ i = j, lam i) * φ j := rfl
    _ = ∑ j, ∑ i ∈ (Finset.univ : Finset (Fin n)) with κ i = j, lam i * φ j := by
      simp_rw [Finset.sum_mul]
    _ = ∑ j, ∑ i ∈ (Finset.univ : Finset (Fin n)) with κ i = j, lam i * φ (κ i) := by
      refine Finset.sum_congr rfl fun j _hj => ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      have hκ : κ i = j := by
        simpa using (Finset.mem_filter.mp hi).2
      rw [hκ]
    _ = ∑ i, lam i * φ (κ i) :=
      Finset.sum_fiberwise (Finset.univ : Finset (Fin n)) κ (fun i => lam i * φ (κ i))

/-- `simplexPush_sum` with the factors of the product commuted (price-vector form). -/
lemma simplexPush_price_sum (lam : stdSimplex ℝ (Fin n)) (κ : Fin n → Fin n)
    (p : Fin n → ℝ) :
    ∑ j, p j * simplexPush lam κ j = ∑ i, lam i * p (κ i) := by
  rw [← simplexPush_sum lam κ p]
  exact Finset.sum_congr rfl fun j _hj => by ring

/-- Reindexing the atoms through `κ` moves the finite law by at most the weighted reindexing
displacement in KR distance. -/
lemma finiteLaw_krDist_push_le
    [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    [CompactSpace Ω]
    (atom : Fin n → Ω) (lam : stdSimplex ℝ (Fin n)) (κ : Fin n → Fin n) :
    krDist (finiteLaw atom lam) (finiteLaw atom (simplexPush lam κ))
      ≤ ∑ i, lam i * dist (atom i) (atom (κ i)) := by
  unfold krDist
  refine csSup_le ?_ ?_
  · refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [expect]
  · rintro x ⟨p, hp_lip, rfl⟩
    have hp_cont : Continuous p := hp_lip.continuous
    have hμ :
        expect (finiteLaw atom lam) p = ∑ i, lam i * p (atom i) :=
      finiteLaw_expect atom lam p hp_cont.aestronglyMeasurable
    have hν :
        expect (finiteLaw atom (simplexPush lam κ)) p =
          ∑ i, simplexPush lam κ i * p (atom i) :=
      finiteLaw_expect atom (simplexPush lam κ) p hp_cont.aestronglyMeasurable
    rw [hμ, hν, simplexPush_sum lam κ (fun i => p (atom i))]
    calc
      (∑ i, lam i * p (atom i)) - ∑ i, lam i * p (atom (κ i))
          = ∑ i, lam i * (p (atom i) - p (atom (κ i))) := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _hi => by ring
      _ ≤ ∑ i, lam i * dist (atom i) (atom (κ i)) := by
            refine Finset.sum_le_sum fun i _hi => ?_
            have hp_bound : p (atom i) - p (atom (κ i))
                ≤ dist (atom i) (atom (κ i)) := by
              have hdist := hp_lip.dist_le_mul (atom i) (atom (κ i))
              rw [Real.dist_eq, NNReal.coe_one, one_mul] at hdist
              exact (abs_le.mp hdist).2
            exact mul_le_mul_of_nonneg_left hp_bound (stdSimplex.zero_le lam i)

/-- Pull an objective on laws back to the finite simplex generated by `atom`. -/
noncomputable def finiteObjective (V : ProbabilityMeasure Ω → ℝ) (atom : Fin n → Ω)
    (lam : Fin n → ℝ) : ℝ := by
  classical
  exact
    if hlam : lam ∈ stdSimplex ℝ (Fin n) then
      V (finiteLaw atom ⟨lam, hlam⟩)
    else
      0

/-- On the simplex, `finiteObjective` evaluates `V` at the corresponding finite law. -/
@[simp] lemma finiteObjective_of_mem
    {V : ProbabilityMeasure Ω → ℝ} {atom : Fin n → Ω} {lam : Fin n → ℝ}
    (hlam : lam ∈ stdSimplex ℝ (Fin n)) :
    finiteObjective V atom lam = V (finiteLaw atom ⟨lam, hlam⟩) := by
  classical
  simp [finiteObjective, hlam]

/-- Boundedness of the finite objective induced by a bounded objective on probability laws. -/
theorem finiteObjective_bdd
    {V : ProbabilityMeasure Ω → ℝ} (atom : Fin n → Ω)
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbabilityMeasure Ω, |V μ| ≤ M) :
    ∃ M : ℝ, ∀ lam : Fin n → ℝ, |finiteObjective V atom lam| ≤ M := by
  classical
  obtain ⟨M, hM⟩ := hV_bdd
  refine ⟨max M 0, ?_⟩
  intro lam
  by_cases hlam : lam ∈ stdSimplex ℝ (Fin n)
  · rw [finiteObjective_of_mem hlam]
    exact le_trans (hM (finiteLaw atom ⟨lam, hlam⟩)) (le_max_left M 0)
  · rw [show finiteObjective V atom lam = 0 from by simp [finiteObjective, hlam], abs_zero]
    exact le_max_right M 0

/-- Upper semicontinuity of the finite objective on the simplex, inherited from the objective on
probability laws through `finiteLaw`. -/
theorem finiteObjective_usc
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [CompactSpace Ω]
    {V : ProbabilityMeasure Ω → ℝ} (atom : Fin n → Ω)
    (hV_usc : UpperSemicontinuous V) :
    UpperSemicontinuousOn (finiteObjective V atom) (stdSimplex ℝ (Fin n)) := by
  have hcomp : UpperSemicontinuous (V ∘ finiteLaw atom) :=
    hV_usc.comp (continuous_finiteLaw atom)
  apply upperSemicontinuousOn_iff_restrict.mp
  change UpperSemicontinuous (fun lam : stdSimplex ℝ (Fin n) =>
    finiteObjective V atom lam)
  have h_eq :
      (fun lam : stdSimplex ℝ (Fin n) => finiteObjective V atom lam)
        = V ∘ finiteLaw atom := by
    funext lam
    exact finiteObjective_of_mem lam.property
  rw [h_eq]
  exact hcomp

end Econlib.Optimization.OptimalTransport
