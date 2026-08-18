/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.CompProdProjections
public import Econlib.Optimization.OptimalTransport.TransportCost
public import Econlib.Probability.ProbDist.Borel
public import Econlib.Probability.ProbDist.Disintegration
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Kantorovich–Rubinstein pseudometric

`krDist μ ν` is the **Kantorovich–Rubinstein functional** (Wasserstein-1, the KR "distance")
between two probability measures `μ, ν : ProbabilityMeasure Ω`, defined via the Lipschitz dual as
the supremum of `∫ p dμ − ∫ p dν` over **1-Lipschitz** test functions `p : Ω → ℝ`.

The ambient assumption here is `[PseudoMetricSpace Ω]`, so the algebra established below —
self-zero, nonnegativity, symmetry, triangle inequality — makes `krDist` a **pseudometric /
extended KR functional**, not yet a genuine metric: Identity of indiscernibles
(`krDist μ ν = 0 → μ = ν`) is *not* among the results here and requires separation on `Ω` (e.g.
`[MetricSpace Ω]`). We call it the KR "distance" only as the conventional name for the functional.

`krTransportCost μ ν` is the transport-cost form: The infimum of `∫ dist x y dπ` over couplings `π`
of `μ` and `ν`. This file establishes the two forms, the easy direction
`krDist μ ν ≤ krTransportCost μ ν` of Kantorovich–Rubinstein duality, the metric algebra of
`krDist` (symmetry, triangle inequality), and convexity of `krDist` under barycenters.

## Main definitions

* `krDist` — the Kantorovich–Rubinstein distance via the Lipschitz dual.
* `krTransportCost` — the transport-cost form via couplings.
* `IsKRLipschitz` — Lipschitz continuity of an objective with respect to `krDist`.
* `gluedPlan` — the coupling obtained by gluing two couplings over a shared marginal.

## Main statements

* `krDist_le_krTransportCost` — the easy direction of Kantorovich–Rubinstein duality.
* `krDist_self`, `krDist_nonneg`, `krDist_comm`, `krDist_triangle` — metric algebra of `krDist`.
* `krTransportCost_comm`, `krTransportCost_triangle` — metric algebra of the transport-cost form.
* `krDist_le_integral_krDist`, `krDist_le_integral_krDist_pair` — convexity of `krDist` under
  barycenters of probability laws.

## References

* Kantorovich, Leonid V., and G. Sh. Rubinstein. 1958. “On a Space of Completely Additive
  Functions.” *Vestnik Leningrad University* 13 : 52–59.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

kantorovich-rubinstein, wasserstein distance, optimal transport, coupling, lipschitz dual
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set BoundedContinuousFunction
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-! ## Definitions -/

/-- The **Kantorovich–Rubinstein functional** (Wasserstein-1) between two probability measures,
defined via the Lipschitz dual. Under the ambient `[PseudoMetricSpace Ω]` this is a pseudometric;
identity of indiscernibles needs separation on `Ω` and is not proved here. -/
noncomputable def krDist (μ ν : ProbabilityMeasure Ω) : ℝ :=
  sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
    x = expect μ p - expect ν p}

/-- An objective `V : ProbabilityMeasure Ω → ℝ` is **`L`-Lipschitz with respect to the KR
distance** if `V μ − V ν ≤ L · krDist μ ν` for every pair of laws.

Symmetrizing in `μ, ν` recovers the usual `|V μ − V ν| ≤ L · krDist μ ν`. -/
def IsKRLipschitz (V : ProbabilityMeasure Ω → ℝ) (L : ℝ) : Prop :=
  ∀ μ ν : ProbabilityMeasure Ω, V μ - V ν ≤ L * krDist μ ν

/-- The **transport-cost form** of the Kantorovich–Rubinstein distance: The infimum of
`∫ dist x y dπ` over couplings `π` of `μ, ν`. -/
noncomputable def krTransportCost (μ ν : ProbabilityMeasure Ω) : ℝ :=
  transportCost (fun p : Ω × Ω => dist p.1 p.2) μ ν

omit [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] in
lemma nonempty_of_measure_univ {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α) :
    Nonempty α := by
  by_contra h
  have hempty : (Set.univ : Set α) = ∅ := by
    ext x
    exact False.elim (h ⟨x⟩)
  have h0 : μ.toMeasure Set.univ = 0 := by rw [hempty, measure_empty]
  rw [measure_univ] at h0
  norm_num at h0

/-! ## Easy direction of duality

`krDist μ ν ≤ krTransportCost μ ν` follows from applying 1-Lipschitz-ness inside the integral:
`∫ p dμ − ∫ p dν = ∫ (p(x) − p(y)) dπ ≤ ∫ dist x y dπ`. -/

section EasyDuality

variable [SecondCountableTopology Ω] [CompactSpace Ω]

/-- **Per-coupling Lipschitz bound.**  For any 1-Lipschitz `p` and any coupling `π` of `μ, ν`, the
difference of test integrals is bounded by the coupling's `dist`-cost:

`∫p dμ − ∫p dν = ∫ (p(x) − p(y)) dπ(x,y) ≤ ∫ dist x y dπ(x,y)`. -/
lemma lipschitz_expect_sub_le_integral_dist
    {μ ν : ProbabilityMeasure Ω} {π : ProbabilityMeasure (Ω × Ω)} (hπ : π ∈ couplings μ ν)
    {p : Ω → ℝ} (hp_lip : LipschitzWith 1 p) :
    expect μ p - expect ν p
      ≤ ∫ z, dist z.1 z.2 ∂π.toMeasure := by
  have hp_cont : Continuous p := hp_lip.continuous
  -- Marginal pushforwards `μ = π.fst`, `ν = π.snd`.
  have hμ_eq : μ.toMeasure = Measure.map Prod.fst π.toMeasure := by
    rw [← hπ.fst_marginal, map_toMeasure]
  have hν_eq : ν.toMeasure = Measure.map Prod.snd π.toMeasure := by
    rw [← hπ.snd_marginal, map_toMeasure]
  -- Integrability for free: each test is bounded continuous (wrap as a BCF on the compact space).
  have hpfst_int : Integrable (fun z : Ω × Ω => p z.1) π.toMeasure :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hp_cont.comp continuous_fst⟩).integrable π.toMeasure
  have hpsnd_int : Integrable (fun z : Ω × Ω => p z.2) π.toMeasure :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hp_cont.comp continuous_snd⟩).integrable π.toMeasure
  have hd_int : Integrable (fun z : Ω × Ω => dist z.1 z.2) π.toMeasure :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_dist⟩).integrable π.toMeasure
  -- Pushforward identities `∫ p dμ = ∫ z, p z.1 ∂π` and similarly for ν.
  have hμp : expect μ p = ∫ z, p z.1 ∂π.toMeasure := by
    unfold expect
    rw [hμ_eq]
    exact MeasureTheory.integral_map measurable_fst.aemeasurable
      hp_cont.aestronglyMeasurable
  have hνp : expect ν p = ∫ z, p z.2 ∂π.toMeasure := by
    unfold expect
    rw [hν_eq]
    exact MeasureTheory.integral_map measurable_snd.aemeasurable
      hp_cont.aestronglyMeasurable
  -- Difference as a single integral.
  have hdiff : expect μ p - expect ν p
      = ∫ z, (p z.1 - p z.2) ∂π.toMeasure := by
    rw [hμp, hνp, ← integral_sub hpfst_int hpsnd_int]
  -- Pointwise 1-Lipschitz bound `p z.1 − p z.2 ≤ dist z.1 z.2`.
  have hbound : ∀ z : Ω × Ω, p z.1 - p z.2 ≤ dist z.1 z.2 := fun z => by
    have h := hp_lip.dist_le_mul z.1 z.2
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
    exact (abs_le.mp h).2
  rw [hdiff]
  exact integral_mono_ae (hpfst_int.sub hpsnd_int) hd_int
    (Filter.Eventually.of_forall hbound)

/-- **Per-Lipschitz bound by transport cost.**  For any 1-Lipschitz `p`, the test-function
difference is bounded by the KR transport cost. -/
lemma lipschitz_expect_sub_le_krTransportCost
    (μ ν : ProbabilityMeasure Ω) {p : Ω → ℝ} (hp_lip : LipschitzWith 1 p) :
    expect μ p - expect ν p ≤ krTransportCost μ ν := by
  unfold krTransportCost transportCost
  refine le_csInf (couplingIntegrals_nonempty _ μ ν) ?_
  rintro y ⟨π, hπ, rfl⟩
  exact lipschitz_expect_sub_le_integral_dist hπ hp_lip

/-- The set of test-integral differences defining `krDist` is bounded above by the KR transport
cost. -/
lemma bddAbove_krDist_setOf (μ ν : ProbabilityMeasure Ω) :
    BddAbove {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
      x = expect μ p - expect ν p} := by
  refine ⟨krTransportCost μ ν, ?_⟩
  rintro x ⟨p, hp_lip, rfl⟩
  exact lipschitz_expect_sub_le_krTransportCost μ ν hp_lip

/-- **Easy direction of Kantorovich–Rubinstein duality.** The Lipschitz-sup form is bounded above
by the coupling-inf form. -/
theorem krDist_le_krTransportCost (μ ν : ProbabilityMeasure Ω) :
    krDist μ ν ≤ krTransportCost μ ν := by
  refine csSup_le ?ne ?bd
  · refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [expect]
  rintro x ⟨p, hp_lip, rfl⟩
  exact lipschitz_expect_sub_le_krTransportCost μ ν hp_lip

end EasyDuality

/-! ## Basic KR algebra -/

section Algebra

omit [OpensMeasurableSpace Ω] in
/-- The KR distance from a law to itself is zero. -/
lemma krDist_self (μ : ProbabilityMeasure Ω) : krDist μ μ = 0 := by
  unfold krDist
  have hset :
      {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
        x = expect μ p - expect μ p} = {0} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      simp
    · intro hx
      rw [mem_singleton_iff] at hx
      subst x
      refine ⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
      simp
  rw [hset, csSup_singleton]

/-- The transport-cost form of KR is symmetric. -/
lemma krTransportCost_comm [SecondCountableTopology Ω] (μ ν : ProbabilityMeasure Ω) :
    krTransportCost μ ν = krTransportCost ν μ := by
  unfold krTransportCost transportCost couplingIntegrals
  congr 1
  ext y
  -- Both inclusions are the same swap argument with `A, B` exchanged: the pushforward of a
  -- coupling under `Prod.swap` is a coupling of the reversed pair with the same `dist`-cost.
  have hswap : ∀ A B : ProbabilityMeasure Ω,
      y ∈ {c : ℝ | ∃ π ∈ couplings A B, c = ∫ z, dist z.1 z.2 ∂π.toMeasure} →
      y ∈ {c : ℝ | ∃ π ∈ couplings B A, c = ∫ z, dist z.1 z.2 ∂π.toMeasure} := by
    rintro A B ⟨π, hπ, rfl⟩
    refine ⟨map π Prod.swap measurable_swap, ⟨?_, ?_⟩, ?_⟩
    · apply ProbabilityMeasure.toMeasure_injective
      have hsnd := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ.snd_marginal
      rw [map_toMeasure, map_toMeasure]
      change Measure.map Prod.fst (Measure.map Prod.swap π.toMeasure) = B.toMeasure
      rw [Measure.map_map measurable_fst measurable_swap]
      simpa [map_toMeasure] using hsnd
    · apply ProbabilityMeasure.toMeasure_injective
      have hfst := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ.fst_marginal
      rw [map_toMeasure, map_toMeasure]
      change Measure.map Prod.snd (Measure.map Prod.swap π.toMeasure) = A.toMeasure
      rw [Measure.map_map measurable_snd measurable_swap]
      simpa [map_toMeasure] using hfst
    · change ∫ z, dist z.1 z.2 ∂π.toMeasure =
        ∫ z, dist z.1 z.2 ∂(Measure.map Prod.swap π.toMeasure)
      rw [MeasureTheory.integral_map measurable_swap.aemeasurable
        (continuous_dist.aestronglyMeasurable)]
      exact (integral_congr_ae <| Filter.Eventually.of_forall fun z => by
        simp [dist_comm]).symm
  exact ⟨hswap μ ν, hswap ν μ⟩

variable [SecondCountableTopology Ω] [CompactSpace Ω]

/-- The KR distance is nonnegative. -/
lemma krDist_nonneg (μ ν : ProbabilityMeasure Ω) : 0 ≤ krDist μ ν := by
  refine le_csSup (bddAbove_krDist_setOf μ ν) ?_
  refine ⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
  simp [expect]

/-- The KR distance is symmetric. -/
lemma krDist_comm (μ ν : ProbabilityMeasure Ω) : krDist μ ν = krDist ν μ := by
  -- One direction: a 1-Lipschitz test for `(a, b)` gives a bound by `krDist b a` via `-p`,
  -- using that `expect` of `-p` is `-expect p` (`integral_neg`, unconditional).
  have hdir : ∀ a b : ProbabilityMeasure Ω, krDist a b ≤ krDist b a := by
    intro a b
    refine csSup_le ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), by
      simp [expect]⟩ ?_
    rintro x ⟨p, hp_lip, rfl⟩
    have hneg_lip : LipschitzWith 1 (fun x : Ω => -p x) := by
      intro x y
      simpa [Real.dist_eq, abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using hp_lip x y
    have hneg_expect : ∀ c : ProbabilityMeasure Ω,
        expect c (fun x : Ω => -p x) = -expect c p := fun c => by
      unfold expect; rw [integral_neg]
    have hrewrite :
        expect a p - expect b p =
          expect b (fun x : Ω => -p x)
            - expect a (fun x : Ω => -p x) := by
      rw [hneg_expect a, hneg_expect b]; ring
    rw [hrewrite]
    exact le_csSup (bddAbove_krDist_setOf b a) ⟨fun x : Ω => -p x, hneg_lip, rfl⟩
  exact le_antisymm (hdir μ ν) (hdir ν μ)

/-- The KR distance satisfies the triangle inequality. -/
lemma krDist_triangle (μ ν ξ : ProbabilityMeasure Ω) :
    krDist μ ν ≤ krDist μ ξ + krDist ξ ν := by
  unfold krDist
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [expect]
  · rintro x ⟨p, hp_lip, rfl⟩
    have hμξ :
        expect μ p - expect ξ p
          ≤ sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
              x = expect μ p - expect ξ p} :=
      le_csSup (bddAbove_krDist_setOf μ ξ) ⟨p, hp_lip, rfl⟩
    have hξν :
        expect ξ p - expect ν p
          ≤ sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
              x = expect ξ p - expect ν p} :=
      le_csSup (bddAbove_krDist_setOf ξ ν) ⟨p, hp_lip, rfl⟩
    linarith

variable [BorelSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω]

/-- The coupling obtained by gluing `π₁ : Π(μ,ν)` and `π₂ : Π(ν,ξ)` over their common `ν` marginal
and then projecting to the outer coordinates. -/
noncomputable def gluedPlan (ν : ProbabilityMeasure Ω)
    (π₁ π₂ : ProbabilityMeasure (Ω × Ω)) : ProbabilityMeasure (Ω × Ω) := by
  letI : Nonempty Ω := nonempty_of_measure_univ ν
  let Kx : Kernel Ω Ω := (Measure.map Prod.swap π₁.toMeasure).condKernel
  let Kz : Kernel Ω Ω := π₂.toMeasure.condKernel
  let K : Kernel Ω (Ω × Ω) := Kx.prod Kz
  let ρ : ProbabilityMeasure (Ω × (Ω × Ω)) := ⟨ν.toMeasure.compProd K, inferInstance⟩
  exact map ρ Prod.snd measurable_snd

omit [OpensMeasurableSpace Ω] in
lemma gluedPlan_mem_couplings (μ ν ξ : ProbabilityMeasure Ω)
    {π₁ π₂ : ProbabilityMeasure (Ω × Ω)} (hπ₁ : π₁ ∈ couplings μ ν)
    (hπ₂ : π₂ ∈ couplings ν ξ) :
    gluedPlan ν π₁ π₂ ∈ couplings μ ξ := by
  letI : Nonempty Ω := nonempty_of_measure_univ ν
  let Kx : Kernel Ω Ω := (Measure.map Prod.swap π₁.toMeasure).condKernel
  let Kz : Kernel Ω Ω := π₂.toMeasure.condKernel
  let K : Kernel Ω (Ω × Ω) := Kx.prod Kz
  let ρ : ProbabilityMeasure (Ω × (Ω × Ω)) := ⟨ν.toMeasure.compProd K, inferInstance⟩
  have hglued_toMeasure :
      (gluedPlan ν π₁ π₂).toMeasure = Measure.map Prod.snd ρ.toMeasure := by
    simp [gluedPlan, Kx, Kz, K, ρ]
  have hρ_toMeasure : ρ.toMeasure = ν.toMeasure.compProd K := rfl
  have hπ₁_swap_fst : (Measure.map Prod.swap π₁.toMeasure).fst = ν.toMeasure := by
    have hsnd := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₁.snd_marginal
    have hsnd' : Measure.map Prod.snd π₁.toMeasure = ν.toMeasure := by
      simpa [map_toMeasure] using hsnd
    rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    simpa using hsnd'
  have hπ₁_swap_snd : (Measure.map Prod.swap π₁.toMeasure).snd = μ.toMeasure := by
    have hfst := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₁.fst_marginal
    have hfst' : Measure.map Prod.fst π₁.toMeasure = μ.toMeasure := by
      simpa [map_toMeasure] using hfst
    rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
    simpa using hfst'
  have hπ₂_fst : π₂.toMeasure.fst = ν.toMeasure := by
    have hfst := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₂.fst_marginal
    simpa [Measure.fst, map_toMeasure] using hfst
  have hπ₂_snd : π₂.toMeasure.snd = ξ.toMeasure := by
    have hsnd := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₂.snd_marginal
    simpa [Measure.snd, map_toMeasure] using hsnd
  have hνKx : ν.toMeasure.compProd Kx = Measure.map Prod.swap π₁.toMeasure := by
    have hdis : (Measure.map Prod.swap π₁.toMeasure).fst.compProd Kx =
        Measure.map Prod.swap π₁.toMeasure := by
      simpa [Kx, map_toMeasure] using
        (condFst_compProd (map π₁ Prod.swap measurable_swap))
    rw [← hπ₁_swap_fst]
    exact hdis
  have hνKz : ν.toMeasure.compProd Kz = π₂.toMeasure := by
    have hdis : π₂.toMeasure.fst.compProd Kz = π₂.toMeasure := by
      simpa [Kz] using (condFst_compProd π₂)
    rw [← hπ₂_fst]
    exact hdis
  refine ⟨?_, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    rw [map_toMeasure, hglued_toMeasure]
    rw [Measure.map_map measurable_fst measurable_snd]
    change Measure.map (fun p : Ω × (Ω × Ω) => p.2.1) ρ.toMeasure = μ.toMeasure
    calc Measure.map (fun p : Ω × (Ω × Ω) => p.2.1) ρ.toMeasure
        = (Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.1)) ρ.toMeasure).snd := by
          rw [Measure.snd]
          have hpair : Measurable (fun p : Ω × (Ω × Ω) => (p.1, p.2.1)) := by
            refine Measurable.prod ?_ ?_
            · exact measurable_fst
            · exact (measurable_fst : Measurable (fun p : Ω × Ω => p.1)).comp
                measurable_snd
          rw [Measure.map_map measurable_snd hpair]
          rfl
      _ = (ν.toMeasure.compProd Kx).snd := by
          rw [hρ_toMeasure, measure_map_compProd_kernel_prod_fst]
      _ = μ.toMeasure := by
          rw [hνKx, hπ₁_swap_snd]
  · apply ProbabilityMeasure.toMeasure_injective
    rw [map_toMeasure, hglued_toMeasure]
    rw [Measure.map_map measurable_snd measurable_snd]
    change Measure.map (fun p : Ω × (Ω × Ω) => p.2.2) ρ.toMeasure = ξ.toMeasure
    calc Measure.map (fun p : Ω × (Ω × Ω) => p.2.2) ρ.toMeasure
        = (Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.2)) ρ.toMeasure).snd := by
          rw [Measure.snd]
          have hpair : Measurable (fun p : Ω × (Ω × Ω) => (p.1, p.2.2)) := by
            refine Measurable.prod ?_ ?_
            · exact measurable_fst
            · exact (show Measurable (fun p : Ω × (Ω × Ω) => p.2.2) from
                (show Measurable (fun q : Ω × Ω => q.2) from measurable_snd).comp
                  (show Measurable (fun p : Ω × (Ω × Ω) => p.2) from measurable_snd))
          rw [Measure.map_map measurable_snd hpair]
          rfl
      _ = (ν.toMeasure.compProd Kz).snd := by
          rw [hρ_toMeasure, measure_map_compProd_kernel_prod_snd]
      _ = ξ.toMeasure := by
          rw [hνKz, hπ₂_snd]

lemma gluedPlan_cost_le (μ ν ξ : ProbabilityMeasure Ω)
    {π₁ π₂ : ProbabilityMeasure (Ω × Ω)} (hπ₁ : π₁ ∈ couplings μ ν)
    (hπ₂ : π₂ ∈ couplings ν ξ) :
    ∫ z, dist z.1 z.2 ∂(gluedPlan ν π₁ π₂).toMeasure
      ≤ ∫ z, dist z.1 z.2 ∂π₁.toMeasure
        + ∫ z, dist z.1 z.2 ∂π₂.toMeasure := by
  letI : Nonempty Ω := nonempty_of_measure_univ ν
  let Kx : Kernel Ω Ω := (Measure.map Prod.swap π₁.toMeasure).condKernel
  let Kz : Kernel Ω Ω := π₂.toMeasure.condKernel
  let K : Kernel Ω (Ω × Ω) := Kx.prod Kz
  let ρ : ProbabilityMeasure (Ω × (Ω × Ω)) := ⟨ν.toMeasure.compProd K, inferInstance⟩
  have hglued_toMeasure :
      (gluedPlan ν π₁ π₂).toMeasure = Measure.map Prod.snd ρ.toMeasure := by
    simp [gluedPlan, Kx, Kz, K, ρ]
  have hρ_toMeasure : ρ.toMeasure = ν.toMeasure.compProd K := rfl
  have hπ₁_swap_fst : (Measure.map Prod.swap π₁.toMeasure).fst = ν.toMeasure := by
    have hsnd := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₁.snd_marginal
    have hsnd' : Measure.map Prod.snd π₁.toMeasure = ν.toMeasure := by
      simpa [map_toMeasure] using hsnd
    rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    simpa using hsnd'
  have hπ₂_fst : π₂.toMeasure.fst = ν.toMeasure := by
    have hfst := congrArg (fun d : ProbabilityMeasure Ω => (d : Measure Ω)) hπ₂.fst_marginal
    simpa [Measure.fst, map_toMeasure] using hfst
  have hνKx : ν.toMeasure.compProd Kx = Measure.map Prod.swap π₁.toMeasure := by
    have hdis : (Measure.map Prod.swap π₁.toMeasure).fst.compProd Kx =
        Measure.map Prod.swap π₁.toMeasure := by
      simpa [Kx, map_toMeasure] using
        (condFst_compProd (map π₁ Prod.swap measurable_swap))
    rw [← hπ₁_swap_fst]
    exact hdis
  have hνKz : ν.toMeasure.compProd Kz = π₂.toMeasure := by
    have hdis : π₂.toMeasure.fst.compProd Kz = π₂.toMeasure := by
      simpa [Kz] using (condFst_compProd π₂)
    rw [← hπ₂_fst]
    exact hdis
  have hpair_x : Measurable (fun p : Ω × (Ω × Ω) => (p.1, p.2.1)) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_fst
    · exact (measurable_fst : Measurable (fun p : Ω × Ω => p.1)).comp measurable_snd
  have hpair_z : Measurable (fun p : Ω × (Ω × Ω) => (p.1, p.2.2)) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_fst
    · exact (show Measurable (fun p : Ω × (Ω × Ω) => p.2.2) from
        (show Measurable (fun q : Ω × Ω => q.2) from measurable_snd).comp
          (show Measurable (fun p : Ω × (Ω × Ω) => p.2) from measurable_snd))
  have hmap_x : Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.1)) ρ.toMeasure =
      Measure.map Prod.swap π₁.toMeasure := by
    rw [hρ_toMeasure, measure_map_compProd_kernel_prod_fst, hνKx]
  have hmap_z : Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.2)) ρ.toMeasure =
      π₂.toMeasure := by
    rw [hρ_toMeasure, measure_map_compProd_kernel_prod_snd, hνKz]
  let dBC : (Ω × Ω) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => dist z.1 z.2, continuous_dist⟩
  have hdist_bound : ∀ x y : Ω, ‖dist x y‖ ≤ ‖dBC‖ := by
    intro x y
    have h := BoundedContinuousFunction.norm_coe_le_norm dBC (x, y)
    simpa [dBC, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h
  have hmeas_xz : Measurable (fun p : Ω × (Ω × Ω) => dist p.2.1 p.2.2) :=
    continuous_dist.measurable.comp measurable_snd
  have hmeas_xy : Measurable (fun p : Ω × (Ω × Ω) => dist p.2.1 p.1) := by
    have hpair : Measurable (fun p : Ω × (Ω × Ω) => (p.2.1, p.1)) := by
      refine Measurable.prod ?_ ?_
      · exact (show Measurable (fun p : Ω × (Ω × Ω) => p.2.1) from
          (show Measurable (fun q : Ω × Ω => q.1) from measurable_fst).comp
            (show Measurable (fun p : Ω × (Ω × Ω) => p.2) from measurable_snd))
      · exact measurable_fst
    exact continuous_dist.measurable.comp hpair
  have hmeas_yz : Measurable (fun p : Ω × (Ω × Ω) => dist p.1 p.2.2) := by
    exact continuous_dist.measurable.comp hpair_z
  -- Each `dist`-of-projections is bounded by `‖dBC‖`, hence integrable against the finite `ρ`.
  have hbdd_int : ∀ a c : Ω × (Ω × Ω) → Ω,
      Measurable (fun p => dist (a p) (c p)) →
      Integrable (fun p : Ω × (Ω × Ω) => dist (a p) (c p)) ρ.toMeasure := fun a c hmeas =>
    ⟨hmeas.aestronglyMeasurable,
      (hasFiniteIntegral_const ‖dBC‖).mono'
        (Filter.Eventually.of_forall fun p => hdist_bound (a p) (c p))⟩
  have hdxz_int := hbdd_int _ _ hmeas_xz
  have hdxy_int := hbdd_int _ _ hmeas_xy
  have hdyz_int := hbdd_int _ _ hmeas_yz
  have hdsum_int :
      Integrable (fun p : Ω × (Ω × Ω) =>
        dist p.2.1 p.1 + dist p.1 p.2.2) ρ.toMeasure :=
    hdxy_int.add hdyz_int
  have hγ_cost :
      ∫ z, dist z.1 z.2 ∂(gluedPlan ν π₁ π₂).toMeasure =
        ∫ p, dist p.2.1 p.2.2 ∂ρ.toMeasure := by
    rw [hglued_toMeasure]
    rw [MeasureTheory.integral_map measurable_snd.aemeasurable
      continuous_dist.aestronglyMeasurable]
  have htriangle_int :
      ∫ p, dist p.2.1 p.2.2 ∂ρ.toMeasure
        ≤ ∫ p, (dist p.2.1 p.1 + dist p.1 p.2.2) ∂ρ.toMeasure := by
    refine integral_mono_ae hdxz_int hdsum_int ?_
    exact Filter.Eventually.of_forall fun p => dist_triangle p.2.1 p.1 p.2.2
  have hsum_split :
      ∫ p, (dist p.2.1 p.1 + dist p.1 p.2.2) ∂ρ.toMeasure =
        ∫ p, dist p.2.1 p.1 ∂ρ.toMeasure
          + ∫ p, dist p.1 p.2.2 ∂ρ.toMeasure := by
    rw [integral_add hdxy_int hdyz_int]
  have hxy_eq :
      ∫ p, dist p.2.1 p.1 ∂ρ.toMeasure
        = ∫ z, dist z.1 z.2 ∂π₁.toMeasure := by
    have hmap_integral :
        ∫ q, dist q.2 q.1
            ∂(Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.1)) ρ.toMeasure)
          = ∫ p, dist p.2.1 p.1 ∂ρ.toMeasure := by
      have hmeas_yx : Measurable (fun q : Ω × Ω => dist q.2 q.1) := by
        simpa [Function.comp_def] using continuous_dist.measurable.comp measurable_swap
      rw [MeasureTheory.integral_map hpair_x.aemeasurable hmeas_yx.aestronglyMeasurable]
    rw [← hmap_integral, hmap_x]
    rw [MeasureTheory.integral_map measurable_swap.aemeasurable]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp)
    · exact (continuous_dist.measurable.comp measurable_swap).aestronglyMeasurable
  have hyz_eq :
      ∫ p, dist p.1 p.2.2 ∂ρ.toMeasure
        = ∫ z, dist z.1 z.2 ∂π₂.toMeasure := by
    have hmap_integral :
        ∫ q, dist q.1 q.2
            ∂(Measure.map (fun p : Ω × (Ω × Ω) => (p.1, p.2.2)) ρ.toMeasure)
          = ∫ p, dist p.1 p.2.2 ∂ρ.toMeasure := by
      have hmeas : Measurable (fun q : Ω × Ω => dist q.1 q.2) :=
        continuous_dist.measurable
      rw [MeasureTheory.integral_map hpair_z.aemeasurable hmeas.aestronglyMeasurable]
    rw [← hmap_integral, hmap_z]
  calc ∫ z, dist z.1 z.2 ∂(gluedPlan ν π₁ π₂).toMeasure
      = ∫ p, dist p.2.1 p.2.2 ∂ρ.toMeasure := hγ_cost
    _ ≤ ∫ p, (dist p.2.1 p.1 + dist p.1 p.2.2) ∂ρ.toMeasure := htriangle_int
    _ = ∫ p, dist p.2.1 p.1 ∂ρ.toMeasure
          + ∫ p, dist p.1 p.2.2 ∂ρ.toMeasure := hsum_split
    _ = ∫ z, dist z.1 z.2 ∂π₁.toMeasure
          + ∫ z, dist z.1 z.2 ∂π₂.toMeasure := by
      rw [hxy_eq, hyz_eq]

/-- The transport-cost form of KR satisfies the triangle inequality. -/
lemma krTransportCost_triangle (μ ν ξ : ProbabilityMeasure Ω) :
    krTransportCost μ ξ ≤ krTransportCost μ ν + krTransportCost ν ξ := by
  let dBC : (Ω × Ω) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩
  obtain ⟨π₁, hπ₁, hπ₁_opt⟩ := exists_optimal_coupling dBC μ ν
  obtain ⟨π₂, hπ₂, hπ₂_opt⟩ := exists_optimal_coupling dBC ν ξ
  let γ : ProbabilityMeasure (Ω × Ω) := gluedPlan ν π₁ π₂
  have hγ : γ ∈ couplings μ ξ := gluedPlan_mem_couplings μ ν ξ hπ₁ hπ₂
  have hC_lo : ∀ z : Ω × Ω, -‖dBC‖ ≤ dist z.1 z.2 := fun _ =>
    le_trans (neg_nonpos.mpr (norm_nonneg dBC)) dist_nonneg
  have hC_hi : ∀ z : Ω × Ω, dist z.1 z.2 ≤ ‖dBC‖ := fun z => by
    have h := BoundedContinuousFunction.norm_coe_le_norm dBC z
    simpa [dBC, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h
  have htc_le :
      krTransportCost μ ξ ≤ ∫ z, dist z.1 z.2 ∂γ.toMeasure := by
    simpa [krTransportCost, γ] using
      transportCost_le_integral_of_bdd continuous_dist.measurable μ ξ hC_lo hC_hi hγ
  have hcost_le :
      ∫ z, dist z.1 z.2 ∂γ.toMeasure
        ≤ ∫ z, dist z.1 z.2 ∂π₁.toMeasure
          + ∫ z, dist z.1 z.2 ∂π₂.toMeasure := by
    simpa [γ] using gluedPlan_cost_le μ ν ξ hπ₁ hπ₂
  have hπ₁_opt' :
      krTransportCost μ ν = ∫ z, dist z.1 z.2 ∂π₁.toMeasure := by
    unfold krTransportCost
    exact hπ₁_opt
  have hπ₂_opt' :
      krTransportCost ν ξ = ∫ z, dist z.1 z.2 ∂π₂.toMeasure := by
    unfold krTransportCost
    exact hπ₂_opt
  calc krTransportCost μ ξ
      ≤ ∫ z, dist z.1 z.2 ∂γ.toMeasure := htc_le
    _ ≤ ∫ z, dist z.1 z.2 ∂π₁.toMeasure
          + ∫ z, dist z.1 z.2 ∂π₂.toMeasure := hcost_le
    _ = krTransportCost μ ν + krTransportCost ν ξ := by
      rw [← hπ₁_opt', ← hπ₂_opt']

end Algebra

/-! ## Convexity of `krDist` under barycenters

The KR distance is convex along barycenters of probability laws: If a law `η₀` is the
barycenter of a measure `τ` over `ProbabilityMeasure Ω` (the pushforward identity on bounded
continuous tests), then `krDist μ₀ η₀ ≤ ∫ krDist μ₀ μ ∂τ`.  This follows from convexity of the
supremum alone, without Kantorovich–Rubinstein duality.

These barycenter inequalities are used downstream by
`Econlib.MechanismDesign.InformationDesign.Persuasion`. -/

section Convexity

variable [BorelSpace Ω] [SecondCountableTopology Ω] [T2Space Ω] [CompactSpace Ω]

/-- **Convexity of the KR distance under averaging.**

If `τ : ProbabilityMeasure (ProbabilityMeasure Ω)` averages bounded continuous tests to `η₀` (the
barycenter / pushforward identity), then for every `μ₀`, `krDist μ₀ η₀ ≤ ∫ μ, krDist μ₀ μ ∂τ`. -/
theorem krDist_le_integral_krDist (μ₀ η₀ : ProbabilityMeasure Ω)
    (τ : ProbabilityMeasure (ProbabilityMeasure Ω))
    (havg : ∀ f : Ω →ᵇ ℝ,
      ∫ μ, expect μ f ∂τ.toMeasure = expect η₀ f)
    (hint : Integrable (fun μ => krDist μ₀ μ) τ.toMeasure) :
    krDist μ₀ η₀ ≤ ∫ μ, krDist μ₀ μ ∂τ.toMeasure := by
  unfold krDist
  refine csSup_le ?ne ?bd
  · -- `0 ∈ S` via `p = 0`.
    refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [expect]
  rintro x ⟨p, hp_lip, rfl⟩
  -- Goal: `μ₀.expect p − η₀.expect p ≤ ∫ μ, krDist μ₀ μ ∂τ`.
  have hp_cont : Continuous p := hp_lip.continuous
  let pBCF : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨p, hp_cont⟩
  -- `havg pBCF` rewritten without the BCF coercion.
  have havg_p :
      ∫ μ, expect μ p ∂τ.toMeasure = expect η₀ p := havg pBCF
  -- Continuity of `μ ↦ μ.expect p` on `ProbabilityMeasure Ω` (Portmanteau via `pBCF`).
  have hexpect_cont : Continuous (fun μ : ProbabilityMeasure Ω => expect μ p) := by
    simpa [expect] using
      MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (X := Ω) pBCF
  have hexpect_int : Integrable (fun μ : ProbabilityMeasure Ω => expect μ p) τ.toMeasure :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hexpect_cont⟩).integrable τ.toMeasure
  -- Pointwise: `μ₀.expect p − μ.expect p ≤ krDist μ₀ μ` by `le_csSup` on the
  -- bounded set defining `krDist μ₀ μ`.
  have hpoint : ∀ μ : ProbabilityMeasure Ω,
      expect μ₀ p - expect μ p ≤ krDist μ₀ μ := fun μ =>
    le_csSup (bddAbove_krDist_setOf μ₀ μ) ⟨p, hp_lip, rfl⟩
  -- The constant `μ₀.expect p` integrated against `τ` equals itself.
  have hconst :
      ∫ _, expect μ₀ p ∂τ.toMeasure = expect μ₀ p := by
    rw [integral_const, MeasureTheory.probReal_univ, one_smul]
  -- Algebraic chain.
  calc expect μ₀ p - expect η₀ p
      = expect μ₀ p - ∫ μ, expect μ p ∂τ.toMeasure := by
        rw [havg_p]
    _ = ∫ _, expect μ₀ p ∂τ.toMeasure
          - ∫ μ, expect μ p ∂τ.toMeasure := by rw [hconst]
    _ = ∫ μ, (expect μ₀ p - expect μ p) ∂τ.toMeasure := by
        rw [← integral_sub (integrable_const _) hexpect_int]
    _ ≤ ∫ μ, krDist μ₀ μ ∂τ.toMeasure :=
        integral_mono_ae ((integrable_const _).sub hexpect_int) hint
          (Filter.Eventually.of_forall hpoint)

/-- **Pair-form convexity of the KR distance.**

Suppose `τ : ProbabilityMeasure (ProbabilityMeasure Ω)` averages identity-tests to `μ₀` (the
barycenter identity for `μ₀`) and averages `ν`-tests to `η₀`.  Then for any measurable family
`ν : ProbabilityMeasure Ω → ProbabilityMeasure Ω`,

`krDist μ₀ η₀ ≤ ∫ μ, krDist μ (ν μ) ∂τ`.

The average KR distance from `μ` to `ν μ` upper-bounds the KR distance between the two
barycenters. -/
theorem krDist_le_integral_krDist_pair
    (μ₀ η₀ : ProbabilityMeasure Ω) (τ : ProbabilityMeasure (ProbabilityMeasure Ω))
    {ν : ProbabilityMeasure Ω → ProbabilityMeasure Ω} (hν_meas : Measurable ν)
    (hμ₀_avg : ∀ f : Ω →ᵇ ℝ,
      ∫ μ, expect μ f ∂τ.toMeasure = expect μ₀ f)
    (hη₀_avg : ∀ f : Ω →ᵇ ℝ,
      ∫ μ, expect (ν μ) f ∂τ.toMeasure = expect η₀ f)
    (hint : Integrable (fun μ => krDist μ (ν μ)) τ.toMeasure) :
    krDist μ₀ η₀ ≤ ∫ μ, krDist μ (ν μ) ∂τ.toMeasure := by
  unfold krDist
  refine csSup_le ?ne ?bd
  · refine ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩
    simp [expect]
  rintro x ⟨p, hp_lip, rfl⟩
  -- Goal: `μ₀.expect p − η₀.expect p ≤ ∫ μ, krDist μ (ν μ) ∂τ`.
  have hp_cont : Continuous p := hp_lip.continuous
  let pBCF : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨p, hp_cont⟩
  have hμ₀_p :
      ∫ μ, expect μ p ∂τ.toMeasure = expect μ₀ p := hμ₀_avg pBCF
  have hη₀_p :
      ∫ μ, expect (ν μ) p ∂τ.toMeasure = expect η₀ p := hη₀_avg pBCF
  -- Continuity of `μ ↦ μ.expect p` (Portmanteau).
  have hexpect_cont : Continuous (fun μ : ProbabilityMeasure Ω => expect μ p) := by
    simpa [expect] using
      MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (X := Ω) pBCF
  let expectBCF : ProbabilityMeasure Ω →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, hexpect_cont⟩
  have hexpect_int : Integrable (fun μ : ProbabilityMeasure Ω => expect μ p) τ.toMeasure :=
    expectBCF.integrable τ.toMeasure
  -- Measurability and integrability of `μ ↦ (ν μ).expect p` via `expectBCF ∘ ν`.
  have hνp_meas : Measurable (fun μ : ProbabilityMeasure Ω => expect (ν μ) p) :=
    hexpect_cont.measurable.comp hν_meas
  have hνp_int : Integrable (fun μ : ProbabilityMeasure Ω => expect (ν μ) p) τ.toMeasure := by
    refine ⟨hνp_meas.aestronglyMeasurable, ?_⟩
    refine (hasFiniteIntegral_const ‖expectBCF‖).mono' ?_
    refine Filter.Eventually.of_forall fun μ => ?_
    change ‖expect (ν μ) p‖ ≤ _
    -- `(ν μ).expect p = expectBCF (ν μ)` definitionally.
    exact (BoundedContinuousFunction.norm_coe_le_norm expectBCF (ν μ)).trans (le_refl _)
  -- Pointwise: `μ.expect p − (ν μ).expect p ≤ krDist μ (ν μ)`.
  have hpoint : ∀ μ : ProbabilityMeasure Ω,
      expect μ p - expect (ν μ) p ≤ krDist μ (ν μ) := fun μ =>
    le_csSup (bddAbove_krDist_setOf μ (ν μ)) ⟨p, hp_lip, rfl⟩
  calc expect μ₀ p - expect η₀ p
      = ∫ μ, expect μ p ∂τ.toMeasure
          - ∫ μ, expect (ν μ) p ∂τ.toMeasure := by rw [hμ₀_p, hη₀_p]
    _ = ∫ μ, (expect μ p - expect (ν μ) p) ∂τ.toMeasure := by
        rw [← integral_sub hexpect_int hνp_int]
    _ ≤ ∫ μ, krDist μ (ν μ) ∂τ.toMeasure :=
        integral_mono_ae (hexpect_int.sub hνp_int) hint
          (Filter.Eventually.of_forall hpoint)

end Convexity

end Econlib.Optimization.OptimalTransport
