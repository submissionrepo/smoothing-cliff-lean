/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.Atomization
public import Econlib.Optimization.OptimalTransport.DualityFinite

/-!
# Kantorovich–Rubinstein duality

On a compact pseudometric space, the Kantorovich–Rubinstein functional `krDist μ ν` (the supremum
over 1-Lipschitz tests) equals the transport-cost functional `krTransportCost μ ν` (the infimum
over couplings): `krDist μ ν = krTransportCost μ ν` (Kantorovich 1942, Villani 2009). This is the
Wasserstein-1 specialization of Kantorovich duality. The ambient assumption is
`[PseudoMetricSpace
Ω]` together with `[CompactSpace Ω]`; `krDist` is the KR functional and is not
proved to be a metric (identity of indiscernibles needs separation on `Ω`).

The easy direction `krDist ≤ krTransportCost` is in `KantorovichRubinstein.lean`. The reverse
direction is obtained by atomizing both laws on a common finite ε-net, applying finite KR duality
(`krDist_eq_krTransportCost_of_finsupp`), and letting ε tend to zero via the atomization bounds and
triangle inequalities.

## Main statements

* `krDist_eq_krTransportCost` — on a compact pseudometric space the Lipschitz-dual and
  transport-cost definitions of the KR functional coincide.
* `exists_optimal_kr_coupling` — the KR distance is attained by a coupling whose `dist`-cost equals
  it.

## References

* Kantorovich, Leonid V. 1942. “On the Translocation of Masses.” *Doklady Akademii Nauk SSSR* 37 :
  199–201.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

kantorovich-rubinstein, kantorovich duality, optimal transport, wasserstein, coupling
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] [CompactSpace Ω]

/-- **Kantorovich–Rubinstein duality.**  On a compact pseudometric space, the Lipschitz-dual
definition and the transport-cost definition of the KR functional coincide. -/
theorem krDist_eq_krTransportCost (μ ν : ProbabilityMeasure Ω) :
    krDist μ ν = krTransportCost μ ν := by
  refine le_antisymm (krDist_le_krTransportCost μ ν) ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / 4 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  obtain ⟨S, V, hV_meas, hV_dist_lt⟩ :=
    exists_eps_partition (Ω := Ω) δ hδ_pos
  have hV_dist_le : ∀ x, dist x (V x : Ω) ≤ δ := fun x =>
    le_of_lt (hV_dist_lt x)
  set μδ : ProbabilityMeasure Ω := atomize μ V hV_meas with hμδ_def
  set νδ : ProbabilityMeasure Ω := atomize ν V hV_meas with hνδ_def
  have hμ_supp : μδ.toMeasure (S : Set Ω) = 1 := by
    simpa [hμδ_def] using atomize_support μ V hV_meas
  have hν_supp : νδ.toMeasure (S : Set Ω) = 1 := by
    simpa [hνδ_def] using atomize_support ν V hV_meas
  have hfinite : krDist μδ νδ = krTransportCost μδ νδ :=
    krDist_eq_krTransportCost_of_finsupp μδ νδ hμ_supp hν_supp
  have htc_μ : krTransportCost μ μδ ≤ δ := by
    simpa [hμδ_def] using
      atomize_krTransportCost_le μ V hV_meas hV_dist_le
  have htc_ν : krTransportCost ν νδ ≤ δ := by
    simpa [hνδ_def] using
      atomize_krTransportCost_le ν V hV_meas hV_dist_le
  have htc_ν_rev : krTransportCost νδ ν ≤ δ := by
    simpa [krTransportCost_comm νδ ν] using htc_ν
  have hkr_μ : krDist μ μδ ≤ δ := by
    simpa [hμδ_def] using
      atomize_krDist_le μ V hV_meas hV_dist_le
  have hkr_ν : krDist ν νδ ≤ δ := by
    simpa [hνδ_def] using
      atomize_krDist_le ν V hV_meas hV_dist_le
  have hkr_μ_rev : krDist μδ μ ≤ δ := by
    simpa [krDist_comm μδ μ] using hkr_μ
  have hkr_mid : krDist μδ νδ ≤ krDist μ ν + 2 * δ := by
    have h₁ := krDist_triangle μδ νδ μ
    have h₂ := krDist_triangle μ νδ ν
    linarith
  have htc_mid : krTransportCost μ ν ≤ krDist μ ν + 4 * δ := by
    have h₁ := krTransportCost_triangle μ μδ ν
    have h₂ := krTransportCost_triangle μδ νδ ν
    linarith
  rw [hδ_def] at htc_mid
  linarith

/-- **Existence of an optimal KR-coupling.**  Combines `exists_optimal_coupling` (applied to the
bounded continuous cost `dist`) with `krDist_eq_krTransportCost` to produce a coupling `π` whose
`dist`-cost equals the KR distance. -/
theorem exists_optimal_kr_coupling (μ ν : ProbabilityMeasure Ω) :
    ∃ π ∈ couplings μ ν,
      krDist μ ν = ∫ z, dist z.1 z.2 ∂π.toMeasure := by
  -- The bounded continuous lift of `dist : Ω × Ω → ℝ`.
  let dBC : BoundedContinuousFunction (Ω × Ω) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩
  obtain ⟨π, hπ_mem, hπ_eq⟩ := exists_optimal_coupling dBC μ ν
  refine ⟨π, hπ_mem, ?_⟩
  rw [krDist_eq_krTransportCost]
  -- `transportCost (fun z => dBC z) = transportCost (fun z => dist z.1 z.2) = krTransportCost`
  -- by definition of `krTransportCost` and `mkOfCompact_apply`.
  show krTransportCost μ ν = ∫ z, dist z.1 z.2 ∂π.toMeasure
  unfold krTransportCost
  exact hπ_eq

end Econlib.Optimization.OptimalTransport
