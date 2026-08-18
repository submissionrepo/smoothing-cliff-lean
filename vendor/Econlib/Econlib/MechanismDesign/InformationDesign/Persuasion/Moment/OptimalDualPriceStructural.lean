/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPrice
public import Econlib.Probability.ProbDist.Borel

/-!
# Structural lemmas for formula-S optimality

Structural follow-ups to the formula-S envelope and condition (M): Relations between the envelope,
feasible joints, and active hyperplanes used in optimality characterizations.

## Main statements

* `pStar_image_bddAbove`, `pStar_convexOn`, `pStar_lipschitzWith`, `pStar_lipschitzOn` —
  boundedness, convexity, and Lipschitz regularity of the formula-S envelope `pStar v S`.
* `MomentSetup.m_lipschitzWith` — the vector moment map is `√n`-Lipschitz when each coordinate is
  `1`-Lipschitz.
* `dualFeasible_of_conditionM` — under condition (M), `pStar v S ∘ m` is dual-feasible for
  `composedValue v`.
* `feasibleJoint_fderiv_cross_zero` — the gradient cross-term vanishes for a feasible joint.
* `objective_eq_pStar_integral_of_conditionM` — under condition (M), the primal objective equals
  the `pStar` integral against the prior.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorems 6–7.

## Tags

persuasion, moment persuasion, formula S, subgradient
-/

@[expose] public section

open MeasureTheory Set Real Filter
open scoped NNReal Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

variable {n : ℕ}

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For `C¹` `v` and `S ⊆ s.X`, the per-`y` family `x ↦ v(x) + ⟨∇v(x), y - x⟩` is bounded above on
`S` uniformly for `y` in any compact subset of `ℝⁿ`. -/
lemma pStar_image_bddAbove
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    (y : EuclideanSpace ℝ (Fin n)) :
    BddAbove ((fun x => v x + (fderiv ℝ v x) (y - x)) '' S) := by
  have hv_cont : Continuous v := hv_diff.continuous
  have h_app_cont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ v x) (y - x)) := by
    have h_joint : Continuous fun p : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
        (fderiv ℝ v p.1) p.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    exact h_joint.comp (Continuous.prodMk continuous_id (continuous_const.sub continuous_id))
  have h_cont : Continuous (fun x => v x + (fderiv ℝ v x) (y - x)) :=
    hv_cont.add h_app_cont
  have h_compact : IsCompact ((fun x => v x + (fderiv ℝ v x) (y - x)) '' s.X) :=
    s.X_compact.image h_cont
  have h_bdd_X : BddAbove ((fun x => v x + (fderiv ℝ v x) (y - x)) '' s.X) :=
    h_compact.bddAbove
  exact h_bdd_X.mono (Set.image_mono hS)

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The formula `pStar v S` is convex on `s.X` for any `S ⊆ s.X`, as a supremum of affine functions
in `y`. -/
lemma pStar_convexOn
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X) :
    ConvexOn ℝ s.X (pStar v S) := by
  refine ⟨s.X_convex, ?_⟩
  intro y₁ hy₁ y₂ hy₂ α β hα hβ hαβ
  by_cases hSnonempty : S.Nonempty
  · have h_img_ne : ((fun x => v x + (fderiv ℝ v x) (α • y₁ + β • y₂ - x)) '' S).Nonempty :=
      hSnonempty.image _
    have h_bdd₁ := pStar_image_bddAbove s hv_diff hS y₁
    have h_bdd₂ := pStar_image_bddAbove s hv_diff hS y₂
    have h_pointwise : ∀ z ∈ (fun x => v x + (fderiv ℝ v x) (α • y₁ + β • y₂ - x)) '' S,
        z ≤ α * pStar v S y₁ + β * pStar v S y₂ := by
      rintro _ ⟨x, hxS, rfl⟩
      simp only
      have h_id : α • y₁ + β • y₂ - x = α • (y₁ - x) + β • (y₂ - x) := by
        rw [smul_sub, smul_sub]
        have : α • x + β • x = x := by
          rw [← add_smul, hαβ, one_smul]
        match_scalars <;> linarith
      rw [h_id, map_add, map_smul, map_smul]
      have h_bound₁ : v x + (fderiv ℝ v x) (y₁ - x) ≤ pStar v S y₁ :=
        le_csSup h_bdd₁ ⟨x, hxS, rfl⟩
      have h_bound₂ : v x + (fderiv ℝ v x) (y₂ - x) ≤ pStar v S y₂ :=
        le_csSup h_bdd₂ ⟨x, hxS, rfl⟩
      have h_split : v x + (α • (fderiv ℝ v x) (y₁ - x) + β • (fderiv ℝ v x) (y₂ - x))
          = α * (v x + (fderiv ℝ v x) (y₁ - x)) + β * (v x + (fderiv ℝ v x) (y₂ - x)) := by
        simp only [smul_eq_mul]
        have hvx : v x = (α + β) * v x := by rw [hαβ, one_mul]
        nlinarith [hvx, hαβ]
      rw [h_split]
      have hα' : (0:ℝ) ≤ α := hα
      have hβ' : (0:ℝ) ≤ β := hβ
      have := add_le_add (mul_le_mul_of_nonneg_left h_bound₁ hα')
        (mul_le_mul_of_nonneg_left h_bound₂ hβ')
      linarith
    exact csSup_le h_img_ne h_pointwise
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSnonempty
    simp [pStar, hSe, Real.sSup_empty]

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The formula `pStar v S` is globally `L`-Lipschitz whenever each slope `‖∇v(x)‖` is bounded by
`L` on `S`. The bound does not require `y₁, y₂ ∈ s.X`. -/
lemma pStar_lipschitzWith
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    (h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ)) :
    LipschitzWith L (pStar v S) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro y₁ y₂
  by_cases hS_ne : S.Nonempty
  · have h_dir : ∀ z₁ z₂ : EuclideanSpace ℝ (Fin n),
        pStar v S z₁ - pStar v S z₂ ≤ (L : ℝ) * dist z₁ z₂ := by
      intros z₁ z₂
      have h_ne : ((fun x => v x + (fderiv ℝ v x) (z₁ - x)) '' S).Nonempty := hS_ne.image _
      apply sub_le_iff_le_add.mpr
      apply csSup_le h_ne
      rintro _ ⟨x, hxS, rfl⟩
      have h_z₂ : v x + (fderiv ℝ v x) (z₂ - x) ≤ pStar v S z₂ :=
        le_csSup (pStar_image_bddAbove s hv_diff hS z₂) ⟨x, hxS, rfl⟩
      have h_diff_eq : (fderiv ℝ v x) (z₁ - x) - (fderiv ℝ v x) (z₂ - x)
          = (fderiv ℝ v x) (z₁ - z₂) := by
        rw [← map_sub]; congr 1; abel
      have hop_bd : ‖(fderiv ℝ v x) (z₁ - z₂)‖
          ≤ ‖fderiv ℝ v x‖ * ‖z₁ - z₂‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have h_slope_x : ‖fderiv ℝ v x‖ ≤ (L : ℝ) := h_slope x hxS
      have h_norm_dist : ‖z₁ - z₂‖ = dist z₁ z₂ := by rw [dist_eq_norm]
      have h_abs_le : |(fderiv ℝ v x) (z₁ - z₂)| ≤ (L : ℝ) * dist z₁ z₂ := by
        rw [Real.norm_eq_abs, h_norm_dist] at hop_bd
        calc |(fderiv ℝ v x) (z₁ - z₂)|
            ≤ ‖fderiv ℝ v x‖ * dist z₁ z₂ := hop_bd
          _ ≤ (L : ℝ) * dist z₁ z₂ := mul_le_mul_of_nonneg_right h_slope_x dist_nonneg
      have h_le : (fderiv ℝ v x) (z₁ - z₂) ≤ (L : ℝ) * dist z₁ z₂ :=
        (abs_le.mp h_abs_le).2
      linarith
    have h_le₁ := h_dir y₁ y₂
    have h_le₂ := h_dir y₂ y₁
    rw [dist_comm y₂ y₁] at h_le₂
    rw [Real.dist_eq]
    exact abs_sub_le_iff.mpr ⟨h_le₁, by linarith⟩
  · have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_ne
    have hpStar_empty : ∀ y, pStar v S y = 0 := by
      intro y
      rw [pStar, hSe]
      simp only [Set.image_empty, Real.sSup_empty]
    rw [hpStar_empty y₁, hpStar_empty y₂, dist_self]
    exact mul_nonneg L.coe_nonneg (dist_nonneg : 0 ≤ dist y₁ y₂)

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The restriction of `pStar_lipschitzWith` to `s.X`. -/
lemma pStar_lipschitzOn
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    (h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ)) :
    LipschitzOnWith L (pStar v S) s.X :=
  (pStar_lipschitzWith s hv_diff hS h_slope).lipschitzOnWith

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The vector moment map `m : Ω → ℝⁿ` is `√n`-Lipschitz globally when each coordinate is
`1`-Lipschitz (Cauchy–Schwarz across coordinates). -/
lemma MomentSetup.m_lipschitzWith (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz) :
    LipschitzWith (Real.toNNReal (Real.sqrt n)) s.m := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro ω₁ ω₂
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have hsqrt_n_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_each : ∀ i : Fin n,
      ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2 ≤ dist ω₁ ω₂ ^ 2 := by
    intro i
    rw [PiLp.sub_apply]
    simp only [Real.norm_eq_abs, sq_abs]
    have h_lipi := (hm_lip i).dist_le_mul ω₁ ω₂
    rw [Real.dist_eq] at h_lipi
    have h_abs : |s.m ω₁ i - s.m ω₂ i| ≤ dist ω₁ ω₂ := by
      have hone : ((1 : NNReal) : ℝ) = 1 := by simp
      rw [hone] at h_lipi; linarith
    have h_nn : 0 ≤ |s.m ω₁ i - s.m ω₂ i| := abs_nonneg _
    calc (s.m ω₁ i - s.m ω₂ i) ^ 2
        = |s.m ω₁ i - s.m ω₂ i| ^ 2 := by rw [sq_abs]
      _ ≤ dist ω₁ ω₂ ^ 2 := pow_le_pow_left₀ h_nn h_abs 2
  have h_sum_le : ∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2
                ≤ (n : ℝ) * dist ω₁ ω₂ ^ 2 := by
    calc ∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2
        ≤ ∑ _i : Fin n, dist ω₁ ω₂ ^ 2 :=
          Finset.sum_le_sum (fun i _ => h_each i)
      _ = (n : ℝ) * dist ω₁ ω₂ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_sqrt_le : Real.sqrt (∑ i : Fin n, ‖(s.m ω₁ - s.m ω₂).ofLp i‖ ^ 2)
        ≤ Real.sqrt ((n : ℝ) * dist ω₁ ω₂ ^ 2) :=
    Real.sqrt_le_sqrt h_sum_le
  have h_sqrt_eq : Real.sqrt ((n : ℝ) * dist ω₁ ω₂ ^ 2)
        = Real.sqrt n * dist ω₁ ω₂ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq dist_nonneg]
  rw [h_sqrt_eq] at h_sqrt_le
  have hcoe : ((Real.toNNReal (Real.sqrt n) : NNReal) : ℝ) = Real.sqrt n :=
    Real.coe_toNNReal _ hsqrt_n_nn
  rw [hcoe]
  exact h_sqrt_le

omit [T2Space Ω] [SecondCountableTopology Ω] [Inhabited Ω] in
/-- Given `ConditionM s v pi S`, the dual price `pStar v S ∘ m : Ω → ℝ` is dual-feasible for the
lifted objective `composedValue v`. -/
lemma dualFeasible_of_conditionM
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hM : ConditionM s v pi S) (hS : S ⊆ s.X) :
    IsDualFeasible (s.composedValue v) (fun ω => pStar v S (s.m ω)) := by
  have h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) := by
    intro x _
    exact norm_fderiv_le_of_lipschitz ℝ hv_lip
  have h_pStar_lip := pStar_lipschitzWith s hv_diff hS h_slope
  have h_pStar_cont : Continuous (pStar v S) := h_pStar_lip.continuous
  have h_m_lip_vec := s.m_lipschitzWith hm_lip
  have h_pStar_m_lip : LipschitzWith (L * Real.toNNReal (Real.sqrt n))
      (fun ω => pStar v S (s.m ω)) :=
    h_pStar_lip.comp h_m_lip_vec
  refine ⟨⟨_, h_pStar_m_lip⟩, ?_⟩
  intro μ
  unfold MomentSetup.composedValue
  have h_post_mem : s.posteriorMoment μ ∈ s.X := s.posteriorMoment_mem_X μ
  have h₁ : v (s.posteriorMoment μ) ≤ pStar v S (s.posteriorMoment μ) :=
    hM.pStar_majorizes _ h_post_mem
  have h_pStar_int : MeasureTheory.Integrable (fun ω => pStar v S (s.m ω)) μ.toMeasure := by
    have h_supp : HasCompactSupport (fun ω => pStar v S (s.m ω)) :=
      HasCompactSupport.of_compactSpace _
    have h_cont : Continuous (fun ω => pStar v S (s.m ω)) := h_pStar_cont.comp s.m_continuous
    exact h_cont.integrable_of_hasCompactSupport h_supp
  have h_m_int : MeasureTheory.Integrable s.m μ.toMeasure := s.m_integrable μ
  have h_pStar_convexOn : ConvexOn ℝ s.X (pStar v S) := pStar_convexOn s hv_diff hS
  have h_ae_m : ∀ᵐ ω ∂μ.toMeasure, s.m ω ∈ s.X := ae_of_all _ s.m_mem_X
  have h_jensen := h_pStar_convexOn.map_integral_le h_pStar_cont.continuousOn
    s.X_compact.isClosed h_ae_m h_m_int h_pStar_int
  change v (s.posteriorMoment μ) ≤ ProbDist.expect μ (fun ω => pStar v S (s.m ω))
  unfold ProbDist.expect
  unfold MomentSetup.posteriorMoment at h_jensen h₁ ⊢
  linarith

omit [CompactSpace Ω] [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- For a feasible joint `π` and `C¹` `v`,

`∫ (fderiv v p.1) (m p.2 − p.1) dπ = 0`. -/
lemma feasibleJoint_fderiv_cross_zero
    (s : MomentSetup Ω n) {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v) :
    ∫ p, (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 := by
  set φ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => (fderiv ℝ v x) (EuclideanSpace.single i 1) with hφ_def
  have hφ_cont : ∀ i, Continuous (φ i) := by
    intro i
    have h_joint : Continuous fun p : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
        (fderiv ℝ v p.1) p.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    exact h_joint.comp (Continuous.prodMk continuous_id continuous_const)
  -- Each coordinate slope `|φ i x| = |∇v(x)·eᵢ|` is bounded by the Lipschitz constant `L`.
  have h_φ_le_L : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)), |φ i x| ≤ (L : ℝ) := by
    intro i x
    have hop : ‖(fderiv ℝ v x) (EuclideanSpace.single i 1)‖
        ≤ ‖fderiv ℝ v x‖ * ‖(EuclideanSpace.single (𝕜 := ℝ) i (1:ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h_norm_e : ‖(EuclideanSpace.single (𝕜 := ℝ) i (1:ℝ))‖ = 1 := by
      rw [PiLp.norm_single 2 _]; exact norm_one
    rw [h_norm_e, mul_one] at hop
    have h_fd : ‖fderiv ℝ v x‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_le : ‖(fderiv ℝ v x) (EuclideanSpace.single i 1)‖ ≤ (L : ℝ) := hop.trans h_fd
    rwa [Real.norm_eq_abs] at h_le
  have hφ_bdd : ∀ i, ∃ M, ∀ x, |φ i x| ≤ M := fun i => ⟨(L : ℝ), h_φ_le_L i⟩
  have h_decomp_w : ∀ w : EuclideanSpace ℝ (Fin n),
      w = ∑ i : Fin n, w.ofLp i • EuclideanSpace.single (𝕜 := ℝ) i 1 := by
    intro w
    set b := EuclideanSpace.basisFun (Fin n) ℝ
    have hsum : ∑ i, (b.repr w).ofLp i • b i = w := b.sum_repr w
    have h_repr : ∀ i, (b.repr w).ofLp i = w.ofLp i := by
      intro i; exact EuclideanSpace.basisFun_repr (Fin n) ℝ w i
    have h_b : ∀ i, b i = EuclideanSpace.single i (1:ℝ) :=
      fun i => EuclideanSpace.basisFun_apply (Fin n) ℝ i
    rw [show (fun i => w.ofLp i • EuclideanSpace.single (𝕜 := ℝ) i 1)
        = (fun i => (b.repr w).ofLp i • b i) from by funext i; rw [h_repr i, h_b i]]
    exact hsum.symm
  have h_integrand : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      (fderiv ℝ v p.1) (s.m p.2 - p.1)
        = ∑ i : Fin n, φ i p.1 * (s.m p.2 - p.1).ofLp i := by
    intro p
    conv_lhs => rw [h_decomp_w (s.m p.2 - p.1)]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]
    change (s.m p.2 - p.1).ofLp i * (fderiv ℝ v p.1) (EuclideanSpace.single i 1)
        = (fderiv ℝ v p.1) (EuclideanSpace.single i 1) * (s.m p.2 - p.1).ofLp i
    ring
  have h_integrand' : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      (fderiv ℝ v p.1) (s.m p.2 - p.1)
        = ∑ i : Fin n, φ i p.1 * (s.m p.2 i - p.1 i) := by
    intro p; rw [h_integrand p]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [PiLp.sub_apply]
  have h_X_bdd : ∃ R : ℝ, ∀ x ∈ s.X, ‖x‖ ≤ R := by
    obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
    exact ⟨R, hR⟩
  obtain ⟨R, hR⟩ := h_X_bdd
  have h_proj_cont : Continuous fun x : EuclideanSpace ℝ (Fin n) => fun i => x.ofLp i :=
    PiLp.continuous_ofLp 2 _
  have h_proj_each : ∀ i, Continuous fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i :=
    fun i => (continuous_apply i).comp h_proj_cont
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
      s.X_compact.isClosed.measurableSet
    have h_meas : MeasurableSet
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
      h_X_meas.preimage measurable_fst
    have h_set_eq :
        {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
          = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
              ⁻¹' s.X)ᶜ := rfl
    rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_meas]
    exact hpi.fst_supportsOn
  have h_intg_each : ∀ i : Fin n,
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        φ i p.1 * (s.m p.2 i - p.1 i)) pi.toMeasure := by
    intro i
    have h_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        φ i p.1 * (s.m p.2 i - p.1 i)) := by
      refine ((hφ_cont i).comp continuous_fst).mul ?_
      refine ((h_proj_each i).comp (s.m_continuous.comp continuous_snd)).sub
        ((h_proj_each i).comp continuous_fst)
    have h_meas : MeasureTheory.AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ i p.1 * (s.m p.2 i - p.1 i))
        pi.toMeasure := h_cont.aestronglyMeasurable
    set C : ℝ := (L : ℝ) * (R + R) with hC_def
    refine MeasureTheory.Integrable.of_bound h_meas C ?_
    filter_upwards [h_ae_p1] with p hp1_in_X
    have hφ_le : |φ i p.1| ≤ (L : ℝ) := h_φ_le_L i p.1
    have h_m_norm : ‖s.m p.2‖ ≤ R := hR _ (s.m_mem_X p.2)
    have h_p1_norm : ‖p.1‖ ≤ R := hR _ hp1_in_X
    -- Each coordinate `|w i|` is bounded by `‖w‖`, hence by `R`.
    have h_coord_le : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R → |w i| ≤ R := by
      intro w hw
      have hbase : ‖w.ofLp i‖ ≤ ‖w‖ := PiLp.norm_apply_le w i
      rw [Real.norm_eq_abs] at hbase
      exact (hbase.trans hw)
    have h_m_i_le : |s.m p.2 i| ≤ R := h_coord_le _ h_m_norm
    have h_p1_i_le : |p.1 i| ≤ R := h_coord_le _ h_p1_norm
    have h_diff : |s.m p.2 i - p.1 i| ≤ R + R := by
      calc |s.m p.2 i - p.1 i|
          ≤ |s.m p.2 i| + |p.1 i| := abs_sub _ _
        _ ≤ R + R := add_le_add h_m_i_le h_p1_i_le
    have h_φ_nn : 0 ≤ |φ i p.1| := abs_nonneg _
    calc ‖φ i p.1 * (s.m p.2 i - p.1 i)‖
        = |φ i p.1| * |s.m p.2 i - p.1 i| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (L : ℝ) * (R + R) := by
          have h1 : |φ i p.1| * |s.m p.2 i - p.1 i| ≤ |φ i p.1| * (R + R) :=
            mul_le_mul_of_nonneg_left h_diff h_φ_nn
          have h2 : |φ i p.1| * (R + R) ≤ (L : ℝ) * (R + R) :=
            mul_le_mul_of_nonneg_right hφ_le (by
              have : (0:ℝ) ≤ R := (norm_nonneg _).trans h_m_norm
              linarith)
          linarith
  calc ∫ p, (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi.toMeasure
      = ∫ p, ∑ i : Fin n, φ i p.1 * (s.m p.2 i - p.1 i) ∂pi.toMeasure := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro p; exact h_integrand' p
    _ = ∑ i : Fin n, ∫ p, φ i p.1 * (s.m p.2 i - p.1 i) ∂pi.toMeasure := by
        rw [MeasureTheory.integral_finset_sum]
        intro i _; exact h_intg_each i
    _ = ∑ i : Fin n, (0 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact hpi.martingale (φ i) (hφ_cont i) (hφ_bdd i) i
    _ = 0 := by simp

omit [CompactSpace Ω] [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- Given `ConditionM s v pi S` and `pi` feasible, the joint primal objective equals the dual
objective evaluated against the prior:

`∫ v(x) dπ(x, ω) = ∫ pStar v S (m(ω)) dμ₀(ω)`. -/
lemma objective_eq_pStar_integral_of_conditionM
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    (hM : ConditionM s v pi S) :
    ∫ p, v p.1 ∂pi.toMeasure
      = ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure := by
  have hpi : pi ∈ feasibleJoint s := hM.feasible
  have h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) := by
    intro x _; exact norm_fderiv_le_of_lipschitz ℝ hv_lip
  have h_pStar_lip := pStar_lipschitzWith s hv_diff hS h_slope
  have h_pStar_cont : Continuous (pStar v S) := h_pStar_lip.continuous
  have h_pStarm_cont : Continuous (fun ω => pStar v S (s.m ω)) := h_pStar_cont.comp s.m_continuous
  have h_pStarm_p_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
      pStar v S (s.m p.2)) := h_pStarm_cont.comp continuous_snd
  have h_v_p_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) :=
    hv_lip.continuous.comp continuous_fst
  have h_fd_p_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
      (fderiv ℝ v p.1) (s.m p.2 - p.1)) := by
    have h_joint : Continuous fun q : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin n)) =>
        (fderiv ℝ v q.1) q.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    refine h_joint.comp (Continuous.prodMk continuous_fst ?_)
    exact (s.m_continuous.comp continuous_snd).sub continuous_fst
  have h_X_bdd : ∃ R : ℝ, ∀ x ∈ s.X, ‖x‖ ≤ R := by
    obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
    exact ⟨R, hR⟩
  obtain ⟨R, hR⟩ := h_X_bdd
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
      s.X_compact.isClosed.measurableSet
    have h_meas : MeasurableSet
        ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
      h_X_meas.preimage measurable_fst
    have h_set_eq :
        {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
          = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
              ⁻¹' s.X)ᶜ := rfl
    rw [h_set_eq, MeasureTheory.prob_compl_eq_zero_iff h_meas]
    exact hpi.fst_supportsOn
  have h_pStar_compact_image : IsCompact (pStar v S '' s.X) := s.X_compact.image h_pStar_cont
  obtain ⟨K_pStar, hK_pStar⟩ := h_pStar_compact_image.isBounded.exists_norm_le
  have h_pStarm_int : MeasureTheory.Integrable (fun p => pStar v S (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pStarm_p_cont.aestronglyMeasurable K_pStar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hK_pStar (pStar v S (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  have h_v_int : MeasureTheory.Integrable (fun p => v p.1) pi.toMeasure := by
    have h_v_compact_image : IsCompact (v '' s.X) := s.X_compact.image hv_lip.continuous
    obtain ⟨K_v, hK_v⟩ := h_v_compact_image.isBounded.exists_norm_le
    refine MeasureTheory.Integrable.of_bound h_v_p_cont.aestronglyMeasurable K_v ?_
    filter_upwards [h_ae_p1] with p hp1
    have := hK_v (v p.1) ⟨p.1, hp1, rfl⟩
    simpa using this
  have h_fd_int : MeasureTheory.Integrable
      (fun p => (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_fd_p_cont.aestronglyMeasurable
      ((L : ℝ) * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_op : ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := ContinuousLinearMap.le_opNorm _ _
    have h_fd_norm : ‖fderiv ℝ v p.1‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    calc ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := h_op
      _ ≤ (L : ℝ) * (R + R) :=
          mul_le_mul h_fd_norm h_diff_norm (norm_nonneg _) L.coe_nonneg
  have h_active : ∫ p, pStar v S (s.m p.2) ∂pi.toMeasure
      = ∫ p, v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi.toMeasure := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hM.active_ae] with p hp using hp
  have h_lin : ∫ p, v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi.toMeasure
      = ∫ p, v p.1 ∂pi.toMeasure
        + ∫ p, (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi.toMeasure :=
    MeasureTheory.integral_add h_v_int h_fd_int
  have h_cross := feasibleJoint_fderiv_cross_zero s hpi hv_lip hv_diff
  have h_marginal : ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure
      = ∫ p, pStar v S (s.m p.2) ∂pi.toMeasure := by
    have hmarg := hpi.marginal
    have h_aem_pStar : AEStronglyMeasurable (fun ω => pStar v S (s.m ω))
        ((ProbDist.map pi Prod.snd measurable_snd).toMeasure) :=
      h_pStarm_cont.aestronglyMeasurable
    have := ProbDist.expect_map pi Prod.snd measurable_snd
      (fun ω => pStar v S (s.m ω)) h_aem_pStar
    rw [hmarg] at this
    exact this
  linarith [h_active, h_lin, h_cross, h_marginal]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
