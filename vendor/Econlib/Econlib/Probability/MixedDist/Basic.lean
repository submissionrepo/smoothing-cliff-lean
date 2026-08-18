/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.FinDist.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# `MixedDist` — distribution on `ℝ` with finitely many atoms plus a density

The atoms are stored as a finitely-supported function `atoms : ℝ →₀ ℝ` sending each atom location
to its probability weight. The measure is `∑ x ∈ atoms.support, atoms x • δ(x) + density · λ`. The
density is **un-normalized**: `∫ density` equals the total continuous mass, and
`(∑ atoms) + ∫ density = 1`.

Representing the atoms by a `Finsupp` (rather than an atom count `n` with
`atomLocation atomWeight : Fin n → ℝ`) means convex mixtures stay within `MixedDist` instead of
growing the index, and duplicate atom locations merge automatically.

This file collects the structure, the discrete/continuous mass decomposition, and the constructors
(`ofContDist`, `ofAtoms`, `dirac`, `mk'`).

## Main definitions

* `MixedDist` — finitely-supported atoms plus an un-normalized density summing to one.
* `MixedDist.discreteWeight`, `MixedDist.continuousWeight` — total atom / density mass.
* `MixedDist.ofContDist`, `ofAtoms`, `dirac`, `mk'` — constructors.

## Main statements

* `MixedDist.atoms_le_one` — each atom weight is at most one.
* `MixedDist.continuousWeight_eq` — continuous mass is `1 - discreteWeight`.

## Tags

mixed distribution, atoms, density, finsupp
-/

@[expose] public section

open BigOperators MeasureTheory Set

namespace Econlib.Probability

/-- A probability distribution on `ℝ` with finitely many atoms (point masses) and an absolutely
continuous component. -/
structure MixedDist where
  /-- Atom locations ↦ probability weights, finitely supported. -/
  atoms : ℝ →₀ ℝ
  /-- Atom weights are nonnegative. -/
  atoms_nonneg : ∀ x, 0 ≤ atoms x
  /-- Un-normalized density of the continuous component. -/
  density : ℝ → ℝ
  /-- Density is nonnegative. -/
  density_nonneg : ∀ x, 0 ≤ density x
  /-- Density is integrable. -/
  density_integrable : Integrable density
  /-- Total probability is 1. -/
  total_one : (atoms.sum fun _ w => w) + ∫ x, density x = 1

namespace MixedDist

/-- Continuous support: Points where the density is positive. -/
def continuousSupport (d : MixedDist) : Set ℝ :=
  {x | 0 < d.density x}

/-- Full support: Atom locations ∪ continuous support. -/
def support (d : MixedDist) : Set ℝ :=
  (↑d.atoms.support : Set ℝ) ∪ d.continuousSupport

/-- Two mixed distributions agree when their atoms and densities agree. -/
@[ext]
lemma ext (d₁ d₂ : MixedDist)
    (h_atoms : d₁.atoms = d₂.atoms)
    (h_den : d₁.density = d₂.density) : d₁ = d₂ := by
  cases d₁; cases d₂
  congr

/-! ### Discrete and continuous mass -/

/-- Total discrete mass. -/
noncomputable def discreteWeight (d : MixedDist) : ℝ :=
  d.atoms.sum fun _ w => w

/-- Total continuous mass. -/
noncomputable def continuousWeight (d : MixedDist) : ℝ :=
  ∫ x, d.density x

/-- The continuous mass is `1` minus the discrete mass. -/
lemma continuousWeight_eq (d : MixedDist) :
    d.continuousWeight = 1 - d.discreteWeight := by
  simp only [continuousWeight, discreteWeight]; linarith [d.total_one]

/-- The discrete mass is `1` minus the continuous mass. -/
lemma discreteWeight_eq (d : MixedDist) :
    d.discreteWeight = 1 - d.continuousWeight := by
  simp only [continuousWeight, discreteWeight]; linarith [d.total_one]

/-- The discrete mass is nonnegative. -/
lemma discreteWeight_nonneg (d : MixedDist) : 0 ≤ d.discreteWeight :=
  Finset.sum_nonneg (fun x _ => d.atoms_nonneg x)

/-- The continuous mass is nonnegative. -/
lemma continuousWeight_nonneg (d : MixedDist) : 0 ≤ d.continuousWeight :=
  integral_nonneg d.density_nonneg

/-- The discrete mass is at most `1`. -/
lemma discreteWeight_le_one (d : MixedDist) : d.discreteWeight ≤ 1 := by
  linarith [d.continuousWeight_eq, d.continuousWeight_nonneg]

/-- The continuous mass is at most `1`. -/
lemma continuousWeight_le_one (d : MixedDist) : d.continuousWeight ≤ 1 := by
  linarith [d.discreteWeight_eq, d.discreteWeight_nonneg]

/-- Each atom weight is at most the total probability, hence at most `1`. -/
lemma atoms_le_one (d : MixedDist) (x : ℝ) : d.atoms x ≤ 1 := by
  have h_le : d.atoms x ≤ d.discreteWeight := by
    rw [discreteWeight, Finsupp.sum]
    by_cases hx : x ∈ d.atoms.support
    · exact Finset.single_le_sum (fun y _ => d.atoms_nonneg y) hx
    · rw [Finsupp.notMem_support_iff.mp hx]
      exact Finset.sum_nonneg (fun y _ => d.atoms_nonneg y)
  linarith [d.discreteWeight_le_one]

/-! ### Constructors -/

variable {n : ℕ}

/-- The total weight of a finite family of single-location atoms is the sum of the individual
weights. -/
lemma sum_finsetSum_single (s : Finset (Fin n)) (loc : Fin n → ℝ) (w : Fin n → ℝ) :
    ((∑ i ∈ s, Finsupp.single (loc i) (w i)).sum fun _ v => v) = ∑ i ∈ s, w i := by
  rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact Finset.sum_congr rfl (fun i _ => Finsupp.sum_single_index rfl)

/-- A finite family of single-location atoms is nonnegative everywhere when each weight is. -/
lemma finsetSum_single_nonneg (loc : Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x : ℝ) : 0 ≤ (∑ i, Finsupp.single (loc i) (w i)) x := by
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [Finsupp.single_apply]
  split_ifs with h
  · exact hw i
  · exact le_rfl

/-- Pure continuous distribution (no atoms). -/
noncomputable def ofContDist (d : ContDist) : MixedDist where
  atoms := 0
  atoms_nonneg := fun _ => by simp
  density := d.density
  density_nonneg := d.nonneg
  density_integrable := d.integrable
  total_one := by simp [d.integral_one]

/-- Pure discrete distribution (zero density). -/
noncomputable def ofAtoms (locations : Fin n → ℝ) (weights : FinDist (Fin n)) :
    MixedDist where
  atoms := ∑ i, Finsupp.single (locations i) (weights.pmf i)
  atoms_nonneg := finsetSum_single_nonneg locations weights.pmf weights.nonneg
  density := fun _ => 0
  density_nonneg := fun _ => le_refl 0
  density_integrable := integrable_zero _ _ _
  total_one := by
    rw [sum_finsetSum_single Finset.univ locations weights.pmf]
    simp [weights.sum_one]

/-- Point mass at a single location. -/
noncomputable def dirac (x : ℝ) : MixedDist where
  atoms := Finsupp.single x 1
  atoms_nonneg := fun y => by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  density := fun _ => 0
  density_nonneg := fun _ => le_refl 0
  density_integrable := integrable_zero _ _ _
  total_one := by
    rw [Finsupp.sum_single_index rfl]; simp

/-- General constructor from atoms + a weighted `ContDist`. -/
noncomputable def mk' (locations : Fin n → ℝ) (atomWeights : Fin n → ℝ)
    (cont : ContDist) (contWeight : ℝ)
    (h_aw_nn : ∀ i, 0 ≤ atomWeights i)
    (h_cw_nn : 0 ≤ contWeight)
    (h_total : ∑ i, atomWeights i + contWeight = 1) : MixedDist where
  atoms := ∑ i, Finsupp.single (locations i) (atomWeights i)
  atoms_nonneg := finsetSum_single_nonneg locations atomWeights h_aw_nn
  density := fun x => contWeight * cont.density x
  density_nonneg := fun x => mul_nonneg h_cw_nn (cont.nonneg x)
  density_integrable := cont.integrable.const_mul contWeight
  total_one := by
    rw [sum_finsetSum_single Finset.univ locations atomWeights]
    have : ∫ (x : ℝ), contWeight * cont.density x = contWeight * ∫ x, cont.density x :=
      integral_const_mul_of_integrable cont.integrable
    rw [this, cont.integral_one, mul_one]
    exact h_total

/-! ### Embedding lemmas -/

/-- The density of `ofContDist d` is the density of `d`. -/
@[simp] lemma ofContDist_density (d : ContDist) : (ofContDist d).density = d.density := by
  rfl

/-- `ofContDist d` has no atoms. -/
@[simp] lemma ofContDist_atoms (d : ContDist) : (ofContDist d).atoms = 0 := rfl

/-- A pure continuous distribution carries all of its mass continuously. -/
@[simp] lemma ofContDist_continuousWeight (d : ContDist) :
    (ofContDist d).continuousWeight = 1 := by
  unfold continuousWeight ofContDist
  exact d.integral_one

/-- A pure continuous distribution has zero discrete mass. -/
@[simp] lemma ofContDist_discreteWeight (d : ContDist) :
    (ofContDist d).discreteWeight = 0 := by
  unfold discreteWeight ofContDist
  simp

/-- A pure discrete distribution carries all of its mass on atoms. -/
@[simp] lemma ofAtoms_discreteWeight (locations : Fin n → ℝ) (weights : FinDist (Fin n)) :
    (ofAtoms locations weights).discreteWeight = 1 := by
  rw [discreteWeight, ofAtoms, sum_finsetSum_single Finset.univ locations weights.pmf]
  simp [weights.sum_one]

/-- A pure discrete distribution has zero continuous mass. -/
@[simp] lemma ofAtoms_continuousWeight (locations : Fin n → ℝ) (weights : FinDist (Fin n)) :
    (ofAtoms locations weights).continuousWeight = 0 := by
  simp [continuousWeight, ofAtoms]

end MixedDist

end Econlib.Probability
