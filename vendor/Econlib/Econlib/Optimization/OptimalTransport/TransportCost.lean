/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.Coupling
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Optimal-transport cost

`transportCost c μ ν` is the infimum of `∫ c dπ` over couplings `π` of `μ` and `ν`, the primal
Kantorovich transport problem (Kantorovich 1942) for a real-valued cost `c` on `Ω₁ × Ω₂`. The cost
is real-valued; the existence theorem `exists_optimal_coupling` is stated for bounded continuous
`c`, which covers the Wasserstein-1 / Kantorovich–Rubinstein case (`c = dist`) on compact metric
spaces.

## Main definitions

* `transportCost` — the infimum of `∫ c dπ` over `π ∈ couplings μ ν`.

## Main statements

* `couplingIntegrals_bddBelow_of_bdd` — under a uniform bound on `c`, the set of coupling integrals
  is bounded below.
* `transportCost_le_integral_of_bdd` — every coupling provides an upper bound on the infimum, under
  a uniform bound on `c`.
* `exists_optimal_coupling` — for a bounded continuous cost `c` on a compact product space, the
  infimum is attained by some coupling.

## References

* Kantorovich, Leonid V. 1942. “On the Translocation of Masses.” *Doklady Akademii Nauk SSSR* 37 :
  199–201.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

optimal transport, transport cost, coupling, kantorovich, optimal coupling
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- The set of integral values `∫ c dπ` as `π` ranges over couplings of `μ` and `ν`.  Auxiliary set
used to define `transportCost`. -/
def couplingIntegrals (c : Ω₁ × Ω₂ → ℝ) (μ : ProbabilityMeasure Ω₁)
    (ν : ProbabilityMeasure Ω₂) : Set ℝ :=
  { x | ∃ π ∈ couplings μ ν, x = ∫ z, c z ∂π.toMeasure }

/-- **Optimal transport cost** between `μ` and `ν` for the cost function `c`. -/
noncomputable def transportCost (c : Ω₁ × Ω₂ → ℝ)
    (μ : ProbabilityMeasure Ω₁) (ν : ProbabilityMeasure Ω₂) : ℝ :=
  sInf (couplingIntegrals c μ ν)

/-- The set of coupling integrals is non-empty, witnessed by the product coupling. -/
lemma couplingIntegrals_nonempty (c : Ω₁ × Ω₂ → ℝ)
    (μ : ProbabilityMeasure Ω₁) (ν : ProbabilityMeasure Ω₂) :
    (couplingIntegrals c μ ν).Nonempty :=
  ⟨_, prod μ ν, prod_mem_couplings μ ν, rfl⟩

/-- For a measurable cost bounded below by `-C`, every coupling integral is at least `-C`.  Used
downstream to establish `BddBelow` for `transportCost`. -/
lemma couplingIntegrals_bddBelow_of_bdd
    {c : Ω₁ × Ω₂ → ℝ} (hc_meas : Measurable c) (μ : ProbabilityMeasure Ω₁)
    (ν : ProbabilityMeasure Ω₂)
    {C : ℝ} (hC_lo : ∀ z, -C ≤ c z) (hC_hi : ∀ z, c z ≤ C) :
    BddBelow (couplingIntegrals c μ ν) := by
  refine ⟨-C, ?_⟩
  rintro y ⟨π, _, rfl⟩
  have hint : Integrable c π.toMeasure := by
    refine ⟨hc_meas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const C).mono'
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hC_lo z, hC_hi z⟩
  calc (-C : ℝ)
      = ∫ _, (-C : ℝ) ∂π.toMeasure := by
        rw [integral_const]
        simp
    _ ≤ ∫ z, c z ∂π.toMeasure :=
        integral_mono_ae (integrable_const _) hint
          (Filter.Eventually.of_forall hC_lo)

/-- Membership form: `transportCost c μ ν ≤ ∫ c dπ` for any coupling `π`, under a two-sided uniform
bound on `c`. -/
lemma transportCost_le_integral_of_bdd
    {c : Ω₁ × Ω₂ → ℝ} (hc_meas : Measurable c) (μ : ProbabilityMeasure Ω₁)
    (ν : ProbabilityMeasure Ω₂)
    {C : ℝ} (hC_lo : ∀ z, -C ≤ c z) (hC_hi : ∀ z, c z ≤ C)
    {π : ProbabilityMeasure (Ω₁ × Ω₂)} (hπ : π ∈ couplings μ ν) :
    transportCost c μ ν ≤ ∫ z, c z ∂π.toMeasure :=
  csInf_le (couplingIntegrals_bddBelow_of_bdd hc_meas μ ν hC_lo hC_hi) ⟨π, hπ, rfl⟩

/-! ## Existence of an optimal coupling for bounded continuous costs -/

section Existence

variable [TopologicalSpace Ω₁] [BorelSpace Ω₁] [SecondCountableTopology Ω₁]
  [TopologicalSpace.PseudoMetrizableSpace Ω₁] [T2Space Ω₁] [CompactSpace Ω₁]
  [TopologicalSpace Ω₂] [BorelSpace Ω₂] [SecondCountableTopology Ω₂]
  [TopologicalSpace.PseudoMetrizableSpace Ω₂] [T2Space Ω₂] [CompactSpace Ω₂]

omit [SecondCountableTopology Ω₁] [TopologicalSpace.PseudoMetrizableSpace Ω₁] [T2Space Ω₁]
  [CompactSpace Ω₁] [TopologicalSpace.PseudoMetrizableSpace Ω₂] [T2Space Ω₂]
  [CompactSpace Ω₂] in
/-- Continuity of `π ↦ ∫ c dπ` on `ProbabilityMeasure (Ω₁ × Ω₂)`, for bounded continuous `c`. -/
lemma continuous_integral_coupling (c : (Ω₁ × Ω₂) →ᵇ ℝ) :
    Continuous (fun π : ProbabilityMeasure (Ω₁ × Ω₂) => ∫ z, c z ∂π.toMeasure) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction c

omit [SecondCountableTopology Ω₁] in
/-- **Existence of an optimal transport plan.**  For a bounded continuous cost `c` on a compact
product space, the infimum in `transportCost` is attained by some coupling `π`. -/
theorem exists_optimal_coupling (c : (Ω₁ × Ω₂) →ᵇ ℝ)
    (μ : ProbabilityMeasure Ω₁) (ν : ProbabilityMeasure Ω₂) :
    ∃ π ∈ couplings μ ν,
      transportCost (fun z => c z) μ ν = ∫ z, c z ∂π.toMeasure := by
  -- Compactness of `couplings μ ν` and continuity of `π ↦ ∫ c dπ` yield a minimizer.
  obtain ⟨π, hπ_mem, hπ_min⟩ :=
    (couplings_isCompact μ ν).exists_isMinOn (couplings_nonempty μ ν)
      (continuous_integral_coupling c).continuousOn
  refine ⟨π, hπ_mem, ?_⟩
  have hC_lo : ∀ z, -‖c‖ ≤ c z := fun z =>
    (abs_le.mp (BoundedContinuousFunction.norm_coe_le_norm c z)).1
  have hC_hi : ∀ z, c z ≤ ‖c‖ := fun z =>
    (abs_le.mp (BoundedContinuousFunction.norm_coe_le_norm c z)).2
  have h_le_inf :
      ∫ z, c z ∂π.toMeasure ≤ transportCost (fun z => c z) μ ν := by
    refine le_csInf (couplingIntegrals_nonempty (fun z => c z) μ ν) ?_
    rintro y ⟨π', hπ', rfl⟩
    exact hπ_min hπ'
  exact le_antisymm
    (transportCost_le_integral_of_bdd c.continuous.measurable μ ν hC_lo hC_hi hπ_mem) h_le_inf

end Existence

end Econlib.Optimization.OptimalTransport
