/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.DistributionalRepr
public import Econlib.Math.MeasureTheory.PiUpdate
public import Econlib.Math.MeasureTheory.WeakConvergence.FixedMarginalContinuity
public import Econlib.Math.MeasureTheory.WeakConvergence.ProbabilityMeasureWeakDual
public import Econlib.Math.Topology.FanGlicksberg
public import Econlib.Optimization.MaximumTheorem

/-!
# Existence of distributional Bayesian Nash equilibrium (Milgrom–Weber)

The **Milgrom–Weber existence theorem** (1985, Theorem 1) for `MeasBayesianGame`: A Bayesian game
with standard Borel type spaces, compact metrizable action spaces, bounded jointly measurable
payoffs that are continuous in actions, and absolutely continuous information (the common prior is
absolutely continuous with respect to the product of its marginals) has a Bayesian Nash equilibrium
in distributional strategies.

## Main statements

* `MeasBayesianGame.exists_isDistBNE` — the Milgrom–Weber existence theorem.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

bayesian games, distributional strategies, bayesian nash equilibrium, existence, milgrom-weber,
fan-glicksberg
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Econlib.Optimization
open scoped ENNReal BoundedContinuousFunction

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

/-- **Milgrom–Weber existence theorem** (1985, Theorem 1). A measure-theoretic Bayesian game with
compact metrizable action spaces, bounded payoffs continuous in actions, and absolutely continuous
information (the prior is absolutely continuous with respect to the product of its marginals — R2)
has a Bayesian Nash equilibrium in distributional strategies.

The `StandardBorelSpace` instances on the action spaces are automatic content-wise (compact
metrizable spaces are Polish) but are not an instance chain Lean can synthesize, so they are
carried as hypotheses; concrete consumers have them. -/
theorem exists_isDistBNE (G : MeasBayesianGame)
    [∀ i, TopologicalSpace (G.Action i)] [∀ i, CompactSpace (G.Action i)]
    [∀ i, TopologicalSpace.MetrizableSpace (G.Action i)] [∀ i, BorelSpace (G.Action i)]
    [∀ i, StandardBorelSpace (G.Action i)] [∀ i, Nonempty (G.Action i)]
    (hbdd : ∀ i, ∃ C, ∀ a θ, |G.payoff i a θ| ≤ C)
    (hcont : ∀ i θ, Continuous fun a => G.payoff i a θ)
    (hac : G.prior ≪ Measure.pi fun i => G.marginalType i) :
    ∃ σ : G.DistProfile, G.IsDistBNE σ := by
  classical
  letI : ∀ i, UpgradedStandardBorel (G.Theta i) := fun i => upgradeStandardBorel (G.Theta i)
  choose C hC using hbdd
  set u : G.Player → (G.TypeProfile × G.ActionProfile) → ℝ := fun i p => G.payoff i p.2 p.1
    with hu_def
  have hu_meas : ∀ i, Measurable (u i) := fun i =>
    (G.measurable_payoff i).comp (measurable_snd.prodMk measurable_fst)
  have hu_bdd : ∀ i p, |u i p| ≤ C i := fun i p => hC i p.2 p.1
  have hu_cont : ∀ i t, Continuous fun a => u i (t, a) := fun i t => hcont i t
  have hg_int := G.integrable_informationDensity
  set F : G.Player → (∀ j, ProbabilityMeasure (G.Theta j × G.Action j)) → ℝ := fun i μp =>
    ∫ s, u i (fun j => (s j).1, fun j => (s j).2) * G.informationDensity (fun j => (s j).1)
      ∂(Measure.pi fun j => (μp j : Measure (G.Theta j × G.Action j))) with hF_def
  set D : ∀ i, Set (ProbabilityMeasure (G.Theta i × G.Action i)) :=
    fun i => fixedFstMarginal (G.marginalType i) with hD_def
  set ε : ∀ i, ProbabilityMeasure (G.Theta i × G.Action i) →
      WeakDual ℝ ((G.Theta i × G.Action i) →ᵇ ℝ) :=
    fun i => ProbabilityMeasure.toWeakDualBCF with hε_def
  set K : ∀ i, Set (WeakDual ℝ ((G.Theta i × G.Action i) →ᵇ ℝ)) :=
    fun i => ε i '' D i with hK_def
  have hD_cpt : ∀ i, IsCompact (D i) := fun i => isCompact_fixedFstMarginal _
  have hD_ne : ∀ i, (D i).Nonempty := fun i => nonempty_fixedFstMarginal _
  have hε_cont : ∀ i, Continuous (ε i) := fun i => ProbabilityMeasure.continuous_toWeakDualBCF
  have hε_inj : ∀ i, Function.Injective (ε i) := fun i =>
    ProbabilityMeasure.toWeakDualBCF_injective
  have hK_cpt : ∀ i, IsCompact (K i) := fun i => (hD_cpt i).image (hε_cont i)
  have hK_ne : ∀ i, (K i).Nonempty := fun i => (hD_ne i).image _
  have hD_combo : ∀ i (μ ν : ProbabilityMeasure (G.Theta i × G.Action i)), μ ∈ D i → ν ∈ D i →
      ∀ a b : ℝ≥0∞, a + b = 1 →
        ∃ ξ ∈ D i, (ξ : Measure (G.Theta i × G.Action i)) =
          a • (μ : Measure (G.Theta i × G.Action i)) +
            b • (ν : Measure (G.Theta i × G.Action i)) := by
    intro i μ ν hμ hν a b hab
    haveI hprob : IsProbabilityMeasure
        (a • (μ : Measure (G.Theta i × G.Action i)) +
          b • (ν : Measure (G.Theta i × G.Action i))) := by
      constructor
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      exact hab
    refine ⟨⟨a • (μ : Measure (G.Theta i × G.Action i)) +
      b • (ν : Measure (G.Theta i × G.Action i)), hprob⟩, ?_, rfl⟩
    have hμ' : (μ : Measure (G.Theta i × G.Action i)).map Prod.fst = G.marginalType i := hμ
    have hν' : (ν : Measure (G.Theta i × G.Action i)).map Prod.fst = G.marginalType i := hν
    change (a • (μ : Measure (G.Theta i × G.Action i)) +
        b • (ν : Measure (G.Theta i × G.Action i))).map Prod.fst = G.marginalType i
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hμ', hν',
      ← add_smul, hab, one_smul]
  have hK_cvx : ∀ i, Convex ℝ (K i) := fun i =>
    ProbabilityMeasure.convex_image_toWeakDualBCF (hD_combo i)
  have hhomeo : ∀ i, ∃ pK : ↥(K i) → ProbabilityMeasure (G.Theta i × G.Action i),
      Continuous pK ∧ (∀ y, pK y ∈ D i) ∧ (∀ y, ε i (pK y) = (y : WeakDual ℝ _)) ∧
        (∀ μ (h : μ ∈ D i), pK ⟨ε i μ, Set.mem_image_of_mem _ h⟩ = μ) := by
    intro i
    haveI : CompactSpace ↥(D i) := isCompact_iff_compactSpace.mp (hD_cpt i)
    -- The embedding restricted to the strategy set, as an equivalence onto its image; compact
    -- domain and T2 codomain upgrade it to a homeomorphism, whose inverse is the pullback.
    let eqv : ↥(D i) ≃ ↥(K i) := Equiv.Set.imageOfInjOn (ε i) (D i) (hε_inj i).injOn
    have heqv_cont : Continuous eqv :=
      Continuous.subtype_mk ((hε_cont i).comp continuous_subtype_val) _
    let h2 : ↥(D i) ≃ₜ ↥(K i) := heqv_cont.homeoOfEquivCompactToT2
    refine ⟨fun y => (h2.symm y : ProbabilityMeasure (G.Theta i × G.Action i)),
      continuous_subtype_val.comp h2.symm.continuous, fun y => (h2.symm y).2, ?_, ?_⟩
    · intro y
      exact congrArg Subtype.val (h2.apply_symm_apply y)
    · intro μ h
      have hpt : (⟨ε i μ, Set.mem_image_of_mem _ h⟩ : ↥(K i)) = h2 ⟨μ, h⟩ := Subtype.ext rfl
      rw [hpt]
      exact congrArg Subtype.val (h2.symm_apply_apply ⟨μ, h⟩)
  choose pK hpK_cont hpK_memD hpK_right hpK_left using hhomeo
  set KK : Set (∀ i, WeakDual ℝ ((G.Theta i × G.Action i) →ᵇ ℝ)) :=
    Set.pi Set.univ K with hKK_def
  have hKK_cpt : IsCompact KK := isCompact_univ_pi hK_cpt
  have hKK_cvx : Convex ℝ KK := convex_pi (fun i _ => hK_cvx i)
  have hKK_ne : KK.Nonempty :=
    ⟨fun i => (hK_ne i).choose, fun i _ => (hK_ne i).choose_spec⟩
  set prof : ↥KK → ∀ j, ProbabilityMeasure (G.Theta j × G.Action j) := fun x j =>
    pK j ⟨x.1 j, x.2 j (Set.mem_univ j)⟩ with hprof_def
  have hprof_mem : ∀ x j, prof x j ∈ D j := fun x j => hpK_memD j _
  have hprof_cont : Continuous prof :=
    continuous_pi fun j => (hpK_cont j).comp
      (Continuous.subtype_mk ((continuous_apply j).comp continuous_subtype_val) _)
  set toD : G.DistProfile → ∀ j, ProbabilityMeasure (G.Theta j × G.Action j) :=
    fun σ j => ⟨(σ j).law, (σ j).instProbLaw⟩ with htoD_def
  have htoD_mem : ∀ σ j, toD σ j ∈ D j := fun σ j => (σ j).marginal_fst
  have hF_toD : ∀ i σ, F i (toD σ) = G.distPayoff i σ := fun i σ =>
    (G.integral_outcome_eq_density hac σ (hu_meas i)).symm
  have hF_contOn : ∀ i, ContinuousOn (F i) (Set.univ.pi D) := fun i =>
    continuousOn_integral_pi_of_fixedFstMarginal _ (hu_meas i) (hu_bdd i) (hu_cont i) hg_int
  set obj : ∀ i, ↥KK → ↥(K i) → ℝ := fun i x y =>
    F i (Function.update (prof x) i (pK i y)) with hobj_def
  have hobj_cont : ∀ i, Continuous fun p : ↥KK × ↥(K i) => obj i p.1 p.2 := by
    intro i
    -- The profile-with-deviation map lands in the fixed-marginal product, where `F i` is
    -- continuous; the map itself is continuous via `continuous_update`.
    have hq_cont : Continuous fun p : ↥KK × ↥(K i) =>
        Function.update (prof p.1) i (pK i p.2) :=
      (continuous_update i).comp ((hprof_cont.comp continuous_fst).prodMk
        ((hpK_cont i).comp continuous_snd))
    have hq_mem : ∀ p : ↥KK × ↥(K i),
        Function.update (prof p.1) i (pK i p.2) ∈ Set.univ.pi D := by
      intro p j _
      rcases eq_or_ne j i with rfl | hji
      · simpa using hpK_memD j p.2
      · simpa [Function.update_of_ne hji] using hprof_mem p.1 j
    exact (hF_contOn i).comp_continuous hq_cont hq_mem
  set objAmb : ∀ i, ↥KK → WeakDual ℝ ((G.Theta i × G.Action i) →ᵇ ℝ) → ℝ := fun i x y =>
    if h : y ∈ K i then obj i x ⟨y, h⟩ else 0 with hobjAmb_def
  have hobjAmb_agree : ∀ i x (y : ↥(K i)), objAmb i x (y : WeakDual ℝ _) = obj i x y := by
    intro i x y
    simp only [hobjAmb_def, dif_pos y.2]
  have hobjAmb_concave : ∀ i x, ConcaveOn ℝ (K i) (objAmb i x) := by
    intro i x
    refine ⟨hK_cvx i, ?_⟩
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    have hcombo : a • y₁ + b • y₂ ∈ K i := hK_cvx i hy₁ hy₂ ha hb hab
    obtain ⟨ξ, hξD, hξeq⟩ := hD_combo i (pK i ⟨y₁, hy₁⟩) (pK i ⟨y₂, hy₂⟩)
      (hpK_memD i _) (hpK_memD i _) (ENNReal.ofReal a) (ENNReal.ofReal b)
      (by rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one])
    have hεξ : ε i ξ = a • y₁ + b • y₂ := by
      refine ContinuousLinearMap.ext fun f => ?_
      have hint₁ : Integrable (⇑f)
          (ENNReal.ofReal a • (pK i ⟨y₁, hy₁⟩ : Measure (G.Theta i × G.Action i))) := by
        haveI := (pK i ⟨y₁, hy₁⟩ : Measure (G.Theta i × G.Action i)).smul_finite
          (c := ENNReal.ofReal a) ENNReal.ofReal_ne_top
        exact f.integrable _
      have hint₂ : Integrable (⇑f)
          (ENNReal.ofReal b • (pK i ⟨y₂, hy₂⟩ : Measure (G.Theta i × G.Action i))) := by
        haveI := (pK i ⟨y₂, hy₂⟩ : Measure (G.Theta i × G.Action i)).smul_finite
          (c := ENNReal.ofReal b) ENNReal.ofReal_ne_top
        exact f.integrable _
      change ∫ ω, f ω ∂(ξ : Measure (G.Theta i × G.Action i)) = (a • y₁ + b • y₂) f
      rw [hξeq, integral_add_measure hint₁ hint₂, integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
      have h₁ : ∫ ω, f ω ∂(pK i ⟨y₁, hy₁⟩ : Measure (G.Theta i × G.Action i)) = y₁ f :=
        DFunLike.congr_fun (hpK_right i ⟨y₁, hy₁⟩) f
      have h₂ : ∫ ω, f ω ∂(pK i ⟨y₂, hy₂⟩ : Measure (G.Theta i × G.Action i)) = y₂ f :=
        DFunLike.congr_fun (hpK_right i ⟨y₂, hy₂⟩) f
      rw [h₁, h₂]
      rfl
    have hpull_combo : pK i ⟨a • y₁ + b • y₂, hcombo⟩ = ξ := by
      refine hε_inj i ?_
      rw [hpK_right i ⟨a • y₁ + b • y₂, hcombo⟩, hεξ]
    have haff := integral_pi_update_convexCombo (η := fun j => G.marginalType j)
      (hu_meas i) (hu_bdd i) hg_int (fun j => hprof_mem x j) i
      (hpK_memD i ⟨y₁, hy₁⟩) (hpK_memD i ⟨y₂, hy₂⟩) ha hb hab hξeq
    have hgoal : objAmb i x (a • y₁ + b • y₂) = a * objAmb i x y₁ + b * objAmb i x y₂ := by
      rw [show objAmb i x (a • y₁ + b • y₂) = obj i x ⟨a • y₁ + b • y₂, hcombo⟩ from
          dif_pos hcombo,
        show objAmb i x y₁ = obj i x ⟨y₁, hy₁⟩ from dif_pos hy₁,
        show objAmb i x y₂ = obj i x ⟨y₂, hy₂⟩ from dif_pos hy₂]
      change F i (Function.update (prof x) i (pK i ⟨a • y₁ + b • y₂, hcombo⟩))
        = a * F i (Function.update (prof x) i (pK i ⟨y₁, hy₁⟩))
          + b * F i (Function.update (prof x) i (pK i ⟨y₂, hy₂⟩))
      rw [hpull_combo]
      exact haff
    rw [hgoal]
    simp [smul_eq_mul]
  set Φ : ↥KK → Set (∀ j, WeakDual ℝ ((G.Theta j × G.Action j) →ᵇ ℝ)) := fun x =>
    Set.pi Set.univ (fun i => argmax (objAmb i x) (K i)) with hΦ_def
  have hargmax_sub : ∀ i x, argmax (objAmb i x) (K i) ⊆ K i := fun i x =>
    fun y hy => hy.1
  have hargmax_ne : ∀ i x, (argmax (objAmb i x) (K i)).Nonempty := by
    intro i x
    refine argmax_nonempty (hK_cpt i) (hK_ne i) ?_
    -- The objective is continuous on `K i`: it agrees there with the continuous composite.
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict : (K i).restrict (objAmb i x) = fun y : ↥(K i) => obj i x y :=
      funext fun y => hobjAmb_agree i x y
    rw [hrestrict]
    exact (hobj_cont i).comp (continuous_const.prodMk continuous_id)
  have hargmax_cvx : ∀ i x, Convex ℝ (argmax (objAmb i x) (K i)) := fun i x =>
    argmax_convex (hobjAmb_concave i x).quasiconcaveOn
  have hΦ_cg : IsClosedGraph Φ := by
    have hgraph_i : ∀ i, IsClosedGraph fun x : ↥KK => argmax (objAmb i x) (K i) := by
      intro i
      haveI : CompactSpace ↥(K i) := isCompact_iff_compactSpace.mp (hK_cpt i)
      haveI : Nonempty ↥(K i) := (hK_ne i).to_subtype
      have hconst_uhc : UpperHemicontinuous (fun _ : ↥KK => (Set.univ : Set ↥(K i))) :=
        fun _x t ht => Filter.Eventually.of_forall fun _ => ht
      have hconst_lhc : LowerHemicontinuous (fun _ : ↥KK => (Set.univ : Set ↥(K i))) :=
        fun _x t ht => Filter.Eventually.of_forall fun _ => ht
      have huhc := argmax_upperHemicontinuous (f := fun (x : ↥KK) (y : ↥(K i)) => obj i x y)
        (Φ := fun _ => Set.univ) (hobj_cont i) hconst_uhc hconst_lhc
        (fun _ => isCompact_univ) (fun _ => Set.univ_nonempty)
      have hclosed_vals : ∀ x : ↥KK,
          IsClosed (argmax (fun y : ↥(K i) => obj i x y) Set.univ) := fun x =>
        (argmax_compact isCompact_univ
          ((hobj_cont i).comp (continuous_const.prodMk continuous_id)).continuousOn).isClosed
      have hsub : IsClosedGraph fun x : ↥KK =>
          argmax (fun y : ↥(K i) => obj i x y) Set.univ :=
        huhc.isClosedGraph hclosed_vals
      have htransfer := hsub.image_subtypeVal (hK_cpt i).isClosed
      have hident : (fun x : ↥KK =>
          Subtype.val '' argmax (fun y : ↥(K i) => obj i x y) Set.univ) =
          fun x : ↥KK => argmax (objAmb i x) (K i) :=
        funext fun x => image_val_argmax_univ fun z => (hobjAmb_agree i x z).symm
      rwa [hident] at htransfer
    change IsClosed {p : ↥KK × (∀ j, WeakDual ℝ ((G.Theta j × G.Action j) →ᵇ ℝ)) |
        p.2 ∈ Φ p.1}
    have hgraph_eq : {p : ↥KK × (∀ j, WeakDual ℝ ((G.Theta j × G.Action j) →ᵇ ℝ)) | p.2 ∈ Φ p.1}
        = ⋂ i, (fun p : ↥KK × (∀ j, WeakDual ℝ ((G.Theta j × G.Action j) →ᵇ ℝ)) =>
            (p.1, p.2 i)) ⁻¹'
          {q : ↥KK × WeakDual ℝ ((G.Theta i × G.Action i) →ᵇ ℝ) |
            q.2 ∈ argmax (objAmb i q.1) (K i)} := by
      ext p
      simp [hΦ_def, Set.mem_pi]
    rw [hgraph_eq]
    exact isClosed_iInter fun i => IsClosed.preimage
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)) (hgraph_i i)
  obtain ⟨x, hx⟩ := fanGlicksbergFixedPoint KK hKK_cpt hKK_cvx hKK_ne Φ hΦ_cg
    (fun x => ⟨fun y hy j hj => hargmax_sub j x (hy j hj),
      convex_pi fun i _ => hargmax_cvx i x,
      ⟨fun i => (hargmax_ne i x).choose, fun i _ => (hargmax_ne i x).choose_spec⟩⟩)
  refine ⟨fun i => { law := (prof x i : Measure (G.Theta i × G.Action i))
                     marginal_fst := hprof_mem x i }, ?_⟩
  rw [G.isDistBNE_iff]
  refine ⟨?_, fun i => ?_⟩
  -- Incumbent integrability: the payoff is bounded by `C i` against the probability outcome.
  on_goal 2 =>
    exact ⟨((G.measurable_payoff i).comp
        (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := C i)
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC i p.2 p.1)⟩
  -- intentionally unused: the integrability guard is not needed once payoffs are bounded
  intro i σ' hagree _hint
  have hτD : toD σ' i ∈ D i := htoD_mem σ' i
  have hτK : ε i (toD σ' i) ∈ K i := Set.mem_image_of_mem _ hτD
  have hmax := hx i (Set.mem_univ i)
  have hineq : objAmb i x (ε i (toD σ' i)) ≤ objAmb i x (x.1 i) := hmax.2 hτK
  have hdev : objAmb i x (ε i (toD σ' i)) = G.distPayoff i σ' := by
    rw [show objAmb i x (ε i (toD σ' i)) = obj i x ⟨ε i (toD σ' i), hτK⟩ from dif_pos hτK]
    change F i (Function.update (prof x) i (pK i ⟨ε i (toD σ' i), hτK⟩)) = G.distPayoff i σ'
    rw [hpK_left i (toD σ' i) hτD, ← hF_toD i σ']
    congr 1
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · rw [Function.update_of_ne hji]
      have hlaw : (σ' j).law = (prof x j : Measure (G.Theta j × G.Action j)) := by
        rw [hagree j hji]
      exact Subtype.ext hlaw.symm
  have heq : objAmb i x (x.1 i) = G.distPayoff i
      (fun j => { law := (prof x j : Measure (G.Theta j × G.Action j))
                  marginal_fst := hprof_mem x j }) := by
    have hximem : x.1 i ∈ K i := x.2 i (Set.mem_univ i)
    rw [show objAmb i x (x.1 i) = obj i x ⟨x.1 i, hximem⟩ from dif_pos hximem]
    change F i (Function.update (prof x) i (pK i ⟨x.1 i, hximem⟩)) = _
    rw [show pK i ⟨x.1 i, hximem⟩ = prof x i from rfl, Function.update_eq_self, ← hF_toD]
    congr 1
  rw [← hdev, ← heq] at *
  exact hineq

end MeasBayesianGame

end Econlib.GameTheory
end
