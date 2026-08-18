/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Danskin
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Basic
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbDist.Mixture

/-!
# Convex roof and upper envelope of a price

This file defines two convex operations on a Lipschitz price:

* The **convex roof** of a Lipschitz price `p : Ω → ℝ`,
  `convexRoof s p y := inf { ProbDist.expect μ p | μ : ProbDist Ω, posteriorMoment μ = y }`,
  obtained by infimizing `p` over posteriors with a given moment vector `y`; it is convex on `s.X`.
* The **upper envelope** of affine minorants with intercept `v` and slope selection `q : ℝⁿ → ℝⁿ`,
  `upperEnvelope s v q y := sup_{x ∈ s.X} { v(x) + ⟨q(x), y - x⟩ }`.

It proves their convexity and Lipschitz bounds and the sandwich inequalities
`v(y) ≤ upperEnvelope ≤ convexRoof` on `s.X`, giving the envelope comparison used in moment-price
duality.

## Main definitions

* `convexRoof` — the convex roof of a scalar price over moment-feasibility.
* `upperEnvelope` — the upper envelope of affine minorants with intercept `v` and slope `q`.

## Main statements

* `convexRoof_convexOn` — `convexRoof s p` is convex on `s.X`.
* `convexRoof_le_lifted_p` — `convexRoof s p (s.m ω) ≤ p ω` for every state.
* `upperEnvelope_convexOn` — `upperEnvelope s v q` is convex (globally).
* `upperEnvelope_lipschitzWith` — Lipschitz with constant `sup_x ‖q x‖`.
* `upperEnvelope_ge_v_on_X` — `v(y) ≤ upperEnvelope s v q y` for `y ∈ s.X`.
* `upperEnvelope_le_convexRoof_on_X` — assuming `q x ∈ ∂(convexRoof s p) x` and
  `v ≤ convexRoof s p` on `s.X`, the envelope is bounded by the roof on `s.X`.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Section 4.

## Tags

persuasion, moment persuasion, convex roof, envelope
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Set MeasureTheory
open Econlib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}

/-- The vector-valued moment map is integrable with respect to every probability law on a compact
`Ω`. -/
private lemma m_integrable_aux [CompactSpace Ω] (s : MomentSetup Ω n)
    (μ : ProbDist Ω) : MeasureTheory.Integrable s.m μ.toMeasure := by
  have h_supp : HasCompactSupport s.m := HasCompactSupport.of_compactSpace _
  exact s.m_continuous.integrable_of_hasCompactSupport h_supp

/-- A continuous scalar price on a compact `Ω` is integrable against every probability law. -/
private lemma p_integrable_aux [CompactSpace Ω] {p : Ω → ℝ} (hp_cont : Continuous p)
    (μ : ProbDist Ω) : MeasureTheory.Integrable p μ.toMeasure :=
  hp_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Posterior moment of a finite mixture is the weighted sum of the constituent moments. -/
lemma posteriorMoment_finMixture [CompactSpace Ω]
    (s : MomentSetup Ω n) {N : ℕ}
    (w : FinDist (Fin N)) (ds : Fin N → ProbDist Ω) :
    s.posteriorMoment (ProbDist.finMixture w ds)
      = ∑ i, w.pmf i • s.posteriorMoment (ds i) := by
  unfold MomentSetup.posteriorMoment ProbDist.finMixture
  change ∫ ω, s.m ω ∂(∑ i, ENNReal.ofReal (w.pmf i) • (ds i).toMeasure)
      = ∑ i, w.pmf i • ∫ ω, s.m ω ∂(ds i).toMeasure
  rw [MeasureTheory.integral_finset_sum_measure (fun i _ =>
    (m_integrable_aux s (ds i)).smul_measure (ENNReal.ofReal_ne_top))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (w.nonneg i)]

/-- The convex roof of a scalar price `p` over moment-feasibility:

`convexRoof s p y = inf { ∫ p dμ : μ ∈ ProbDist Ω, ∫ m dμ = y }`.

For `y ∉ image(posteriorMoment)`, the underlying set is empty and the infimum reduces to
`sInf ∅`. -/
noncomputable def convexRoof (s : MomentSetup Ω n) (p : Ω → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => sInf { z : ℝ | ∃ μ : ProbDist Ω,
    s.posteriorMoment μ = y ∧ z = ProbDist.expect μ p }

/-- The set of expectations entering `convexRoof s p y` is bounded below: A continuous price on a
compact `Ω` is bounded below, and the expectation dominates that pointwise bound. -/
private lemma convexRoof_expectSet_bddBelow [CompactSpace Ω] (s : MomentSetup Ω n) {p : Ω → ℝ}
    (hp_cont : Continuous p) (y : EuclideanSpace ℝ (Fin n)) :
    BddBelow { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = y ∧ z = ProbDist.expect μ p } := by
  obtain ⟨M, hM⟩ := ((isCompact_range hp_cont).isBounded).exists_norm_le
  -- `‖p ω‖ ≤ M` gives the pointwise lower bound `-M ≤ p ω`.
  have hM_lb : ∀ ω, -M ≤ p ω :=
    fun ω => (abs_le.mp (by simpa [Real.norm_eq_abs] using hM (p ω) ⟨ω, rfl⟩)).1
  refine ⟨-M, ?_⟩
  rintro z ⟨μ, _, rfl⟩
  calc (-M : ℝ) = ∫ _x, (-M : ℝ) ∂μ.toMeasure := by simp
    _ ≤ ProbDist.expect μ p :=
      MeasureTheory.integral_mono_ae (MeasureTheory.integrable_const _)
        (p_integrable_aux hp_cont μ) (ae_of_all _ hM_lb)

/-- The upper envelope of affine minorants with intercept `v` and slope `q`:

`upperEnvelope s v q y = sup_{x ∈ s.X} { v(x) + ⟨q(x), y - x⟩ }`. -/
noncomputable def upperEnvelope (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y => sSup ((fun x : EuclideanSpace ℝ (Fin n) =>
    v x + inner ℝ (q x) (y - x)) '' s.X)

/-- The affine envelope `x ↦ v x + ⟨q x, y - x⟩` is bounded above on `s.X` when `v` is continuous
and `q` has bounded norm. -/
lemma bddAbove_envelope_image (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_cont : Continuous v)
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {K : ℝ} (hq : ∀ x, ‖q x‖ ≤ K) (y : EuclideanSpace ℝ (Fin n)) :
    BddAbove ((fun x : EuclideanSpace ℝ (Fin n) =>
      v x + inner ℝ (q x) (y - x)) '' s.X) := by
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => v x + K * ‖y - x‖ with hh_def
  have hh_cont : Continuous h := by
    refine hv_cont.add ?_
    exact continuous_const.mul ((continuous_const.sub continuous_id).norm)
  obtain ⟨M, hM⟩ : BddAbove (h '' s.X) :=
    s.X_compact.bddAbove_image hh_cont.continuousOn
  refine ⟨M, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have h_inner : inner ℝ (q x) (y - x) ≤ K * ‖y - x‖ := by
    calc inner ℝ (q x) (y - x)
        ≤ ‖q x‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ ≤ K * ‖y - x‖ := mul_le_mul_of_nonneg_right (hq x) (norm_nonneg _)
  have h_le_h : v x + inner ℝ (q x) (y - x) ≤ h x := by
    simp only [h]; linarith
  exact h_le_h.trans (hM ⟨x, hx, rfl⟩)

/-- The convex roof is convex on `s.X`, assuming `Ω` is compact and that every `y ∈ s.X` is the
posterior moment of some distribution (Bayes-plausibility). -/
lemma convexRoof_convexOn [CompactSpace Ω] (s : MomentSetup Ω n) {p : Ω → ℝ}
    {L : NNReal} (hp : LipschitzWith L p) :
    ConvexOn ℝ s.X (convexRoof s p) := by
  refine ⟨s.X_convex, ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  rw [smul_eq_mul, smul_eq_mul]
  unfold convexRoof
  have hp_cont : Continuous p := hp.continuous
  have hp_int : ∀ (μ : ProbDist Ω), MeasureTheory.Integrable p μ.toMeasure :=
    p_integrable_aux hp_cont
  have h_bdd_y : ∀ y, BddBelow { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = y ∧ z = ProbDist.expect μ p } :=
    fun y => convexRoof_expectSet_bddBelow s hp_cont y
  obtain ⟨μ₁₀, hμ₁₀⟩ := s.feasible y₁ hy₁
  obtain ⟨μ₂₀, hμ₂₀⟩ := s.feasible y₂ hy₂
  set S₁ : Set ℝ := { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = y₁ ∧ z = ProbDist.expect μ p } with hS₁_def
  set S₂ : Set ℝ := { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = y₂ ∧ z = ProbDist.expect μ p } with hS₂_def
  set S₃ : Set ℝ := { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = a • y₁ + b • y₂ ∧ z = ProbDist.expect μ p } with hS₃_def
  have hS₁_ne : S₁.Nonempty := ⟨ProbDist.expect μ₁₀ p, μ₁₀, hμ₁₀, rfl⟩
  have hS₂_ne : S₂.Nonempty := ⟨ProbDist.expect μ₂₀ p, μ₂₀, hμ₂₀, rfl⟩
  rw [← sub_nonneg]
  by_contra h_neg
  push Not at h_neg
  set δ : ℝ := sInf S₃ - (a * sInf S₁ + b * sInf S₂) with hδ_def
  have hδ_pos : 0 < δ := by
    have : sInf S₃ - (a * sInf S₁ + b * sInf S₂)
        = -(a * sInf S₁ + b * sInf S₂ - sInf S₃) := by ring
    rw [hδ_def, this]
    linarith
  set ε : ℝ := δ / 4 with hε_def
  have hε_pos : 0 < ε := by positivity
  have hS₁_inf : sInf S₁ < sInf S₁ + ε := by linarith
  obtain ⟨z₁, hz₁_mem, hz₁_lt⟩ := exists_lt_of_csInf_lt hS₁_ne hS₁_inf
  obtain ⟨μ₁, hμ₁, hz₁_eq⟩ := hz₁_mem
  have hS₂_inf : sInf S₂ < sInf S₂ + ε := by linarith
  obtain ⟨z₂, hz₂_mem, hz₂_lt⟩ := exists_lt_of_csInf_lt hS₂_ne hS₂_inf
  obtain ⟨μ₂, hμ₂, hz₂_eq⟩ := hz₂_mem
  let w : FinDist (Fin 2) := ⟨![a, b], by
    intro i; fin_cases i <;> simpa, by simp [Fin.sum_univ_succ]; linarith⟩
  let ds : Fin 2 → ProbDist Ω := ![μ₁, μ₂]
  let μ : ProbDist Ω := ProbDist.finMixture w ds
  have h_mix_moment : s.posteriorMoment μ = a • y₁ + b • y₂ := by
    rw [posteriorMoment_finMixture s w ds]
    simp [Fin.sum_univ_succ, w, ds, hμ₁, hμ₂]
  have h_mix_expect : ProbDist.expect μ p = a * ProbDist.expect μ₁ p
                                            + b * ProbDist.expect μ₂ p := by
    rw [ProbDist.expect_finMixture w ds p (fun i => by
      fin_cases i <;> exact hp_int _)]
    simp [Fin.sum_univ_succ, w, ds]
  have h_in_S₃ : ProbDist.expect μ p ∈ S₃ := ⟨μ, h_mix_moment, rfl⟩
  have h_sInf_le : sInf S₃ ≤ ProbDist.expect μ p :=
    csInf_le (h_bdd_y _) h_in_S₃
  have h_lt : ProbDist.expect μ p < a * sInf S₁ + b * sInf S₂ + ε := by
    rw [h_mix_expect]
    have ha_lt : a * ProbDist.expect μ₁ p ≤ a * (sInf S₁ + ε) :=
      mul_le_mul_of_nonneg_left (by linarith [hz₁_eq, hz₁_lt]) ha
    have hb_lt : b * ProbDist.expect μ₂ p ≤ b * (sInf S₂ + ε) :=
      mul_le_mul_of_nonneg_left (by linarith [hz₂_eq, hz₂_lt]) hb
    have h_sum : a * (sInf S₁ + ε) + b * (sInf S₂ + ε)
                = a * sInf S₁ + b * sInf S₂ + (a + b) * ε := by ring
    have h_total : a * ProbDist.expect μ₁ p + b * ProbDist.expect μ₂ p
                 ≤ a * sInf S₁ + b * sInf S₂ + ε := by
      have := add_le_add ha_lt hb_lt
      rw [h_sum] at this
      rw [hab, one_mul] at this
      exact this
    -- At least one of `a`, `b` is positive since `a + b = 1`.
    have h_one_pos : 0 < a ∨ 0 < b := by
      by_contra h_both
      push Not at h_both
      have ha0 : a = 0 := le_antisymm h_both.1 ha
      have hb0 : b = 0 := le_antisymm h_both.2 hb
      simp [ha0, hb0] at hab
    rcases h_one_pos with ha_pos | hb_pos
    · have ha_lt_strict : a * ProbDist.expect μ₁ p < a * (sInf S₁ + ε) := by
        have h1 : ProbDist.expect μ₁ p < sInf S₁ + ε := by
          linarith [hz₁_eq, hz₁_lt]
        exact mul_lt_mul_of_pos_left h1 ha_pos
      have h_sum_lt : a * ProbDist.expect μ₁ p + b * ProbDist.expect μ₂ p
                    < a * (sInf S₁ + ε) + b * (sInf S₂ + ε) := by
        linarith
      rw [h_sum, hab, one_mul] at h_sum_lt
      linarith
    · have hb_lt_strict : b * ProbDist.expect μ₂ p < b * (sInf S₂ + ε) := by
        have h2 : ProbDist.expect μ₂ p < sInf S₂ + ε := by
          linarith [hz₂_eq, hz₂_lt]
        exact mul_lt_mul_of_pos_left h2 hb_pos
      have h_sum_lt : a * ProbDist.expect μ₁ p + b * ProbDist.expect μ₂ p
                    < a * (sInf S₁ + ε) + b * (sInf S₂ + ε) := by
        linarith
      rw [h_sum, hab, one_mul] at h_sum_lt
      linarith
  have : sInf S₃ < a * sInf S₁ + b * sInf S₂ + ε := lt_of_le_of_lt h_sInf_le h_lt
  have : δ < ε := by
    rw [hδ_def]; linarith
  rw [hε_def] at this
  linarith

/-- The convex roof at a posterior moment is bounded above by the price at the state. -/
lemma convexRoof_le_lifted_p (s : MomentSetup Ω n)
    [MeasurableSingletonClass Ω] [CompactSpace Ω] {p : Ω → ℝ}
    (hp_cont : Continuous p) (ω : Ω) :
    convexRoof s p (s.m ω) ≤ p ω := by
  unfold convexRoof
  set S : Set ℝ := { z : ℝ | ∃ μ : ProbDist Ω,
      s.posteriorMoment μ = s.m ω ∧ z = ProbDist.expect μ p } with hS_def
  have h_mem : p ω ∈ S := by
    refine ⟨ProbDist.dirac ω, ?_, ?_⟩
    · unfold MomentSetup.posteriorMoment
      have h : (ProbDist.dirac ω).toMeasure = Measure.dirac ω := rfl
      rw [h, MeasureTheory.integral_dirac _ ω]
    · exact (ProbDist.expect_dirac ω p).symm
  exact csInf_le (convexRoof_expectSet_bddBelow s hp_cont (s.m ω)) h_mem

/-- The upper envelope is convex on the whole space. -/
lemma upperEnvelope_convexOn (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv_cont : Continuous v)
    {K : ℝ} (hq : ∀ x, ‖q x‖ ≤ K) :
    ConvexOn ℝ Set.univ (upperEnvelope s v q) := by
  refine ⟨convex_univ, ?_⟩
  intro y₁ _ y₂ _ a b ha hb hab
  set g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y x => v x + inner ℝ (q x) (y - x) with hg_def
  have hX_ne : s.X.Nonempty := s.X_interior.mono interior_subset
  have h_bdd₁ : BddAbove (g y₁ '' s.X) := bddAbove_envelope_image s hv_cont hq y₁
  have h_bdd₂ : BddAbove (g y₂ '' s.X) := bddAbove_envelope_image s hv_cont hq y₂
  have hX_ne₁₂ : (g (a • y₁ + b • y₂) '' s.X).Nonempty := hX_ne.image _
  have h_pt : ∀ x ∈ s.X,
      g (a • y₁ + b • y₂) x = a * g y₁ x + b * g y₂ x := by
    intro x _
    simp only [g]
    have h_split : (a • y₁ + b • y₂) - x = a • (y₁ - x) + b • (y₂ - x) := by
      have hax : a • x + b • x = x := by
        rw [← add_smul, hab, one_smul]
      rw [show (a • y₁ + b • y₂) - x
            = (a • y₁ + b • y₂) - (a • x + b • x) from by rw [hax]]
      simp [smul_sub]; abel
    rw [h_split, inner_add_right, inner_smul_right, inner_smul_right]
    have : a * v x + b * v x = v x := by
      rw [← add_mul, hab, one_mul]
    linarith [this]
  change sSup (g (a • y₁ + b • y₂) '' s.X) ≤
      a * sSup (g y₁ '' s.X) + b * sSup (g y₂ '' s.X)
  refine csSup_le hX_ne₁₂ ?_
  rintro z ⟨x, hx, rfl⟩
  rw [h_pt x hx]
  have h₁_le : g y₁ x ≤ sSup (g y₁ '' s.X) := le_csSup h_bdd₁ ⟨x, hx, rfl⟩
  have h₂_le : g y₂ x ≤ sSup (g y₂ '' s.X) := le_csSup h_bdd₂ ⟨x, hx, rfl⟩
  have ha_mul := mul_le_mul_of_nonneg_left h₁_le ha
  have hb_mul := mul_le_mul_of_nonneg_left h₂_le hb
  linarith

/-- The upper envelope is `K`-Lipschitz with `K = sup_{x ∈ s.X} ‖q x‖`. -/
lemma upperEnvelope_lipschitzWith (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv_cont : Continuous v)
    {K : NNReal} (hq : ∀ x, ‖q x‖ ≤ (K : ℝ)) :
    LipschitzWith K (upperEnvelope s v q) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro y₁ y₂
  set g₁ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => v x + inner ℝ (q x) (y₁ - x) with hg₁_def
  set g₂ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => v x + inner ℝ (q x) (y₂ - x) with hg₂_def
  have hX_ne : s.X.Nonempty := s.X_interior.mono interior_subset
  have h_bdd₁ : BddAbove (g₁ '' s.X) := bddAbove_envelope_image s hv_cont hq y₁
  have h_bdd₂ : BddAbove (g₂ '' s.X) := bddAbove_envelope_image s hv_cont hq y₂
  have hX_ne₁ : (g₁ '' s.X).Nonempty := hX_ne.image _
  have hX_ne₂ : (g₂ '' s.X).Nonempty := hX_ne.image _
  -- A single bound on the directed difference; both orientations follow by specialization.
  have h_diff : ∀ (u w : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
      (v x + inner ℝ (q x) (u - x)) - (v x + inner ℝ (q x) (w - x)) ≤ (K : ℝ) * dist u w := by
    intro u w x
    have h_eq : (v x + inner ℝ (q x) (u - x)) - (v x + inner ℝ (q x) (w - x))
        = inner ℝ (q x) (u - w) := by
      rw [show u - w = (u - x) - (w - x) by abel]
      simp only [inner_sub_right]; ring
    rw [h_eq]
    calc inner ℝ (q x) (u - w)
        ≤ ‖q x‖ * ‖u - w‖ := real_inner_le_norm _ _
      _ ≤ (K : ℝ) * dist u w := by
          rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right (hq x) (norm_nonneg _)
  have h_pt : ∀ x ∈ s.X, g₁ x - g₂ x ≤ (K : ℝ) * dist y₁ y₂ := fun x _ => h_diff y₁ y₂ x
  have h_pt' : ∀ x ∈ s.X, g₂ x - g₁ x ≤ (K : ℝ) * dist y₁ y₂ := fun x _ =>
    dist_comm y₂ y₁ ▸ h_diff y₂ y₁ x
  have h_le₁ : upperEnvelope s v q y₁
              ≤ upperEnvelope s v q y₂ + (K : ℝ) * dist y₁ y₂ := by
    change sSup (g₁ '' s.X) ≤ sSup (g₂ '' s.X) + (K : ℝ) * dist y₁ y₂
    refine csSup_le hX_ne₁ ?_
    rintro z ⟨x, hx, rfl⟩
    have h₂_mem : g₂ x ∈ g₂ '' s.X := ⟨x, hx, rfl⟩
    have h₂_le : g₂ x ≤ sSup (g₂ '' s.X) := le_csSup h_bdd₂ h₂_mem
    linarith [h_pt x hx]
  have h_le₂ : upperEnvelope s v q y₂
              ≤ upperEnvelope s v q y₁ + (K : ℝ) * dist y₁ y₂ := by
    change sSup (g₂ '' s.X) ≤ sSup (g₁ '' s.X) + (K : ℝ) * dist y₁ y₂
    refine csSup_le hX_ne₂ ?_
    rintro z ⟨x, hx, rfl⟩
    have h₁_mem : g₁ x ∈ g₁ '' s.X := ⟨x, hx, rfl⟩
    have h₁_le : g₁ x ≤ sSup (g₁ '' s.X) := le_csSup h_bdd₁ h₁_mem
    linarith [h_pt' x hx]
  rw [Real.dist_eq, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · linarith [h_le₁]
  · linarith [h_le₂]

/-- On `s.X`, the upper envelope dominates `v`. -/
lemma upperEnvelope_ge_v_on_X (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv_cont : Continuous v)
    {K : ℝ} (hq : ∀ x, ‖q x‖ ≤ K) :
    ∀ y ∈ s.X, v y ≤ upperEnvelope s v q y := by
  intro y hy
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => v x + inner ℝ (q x) (y - x) with hg_def
  have h_bdd : BddAbove (g '' s.X) := bddAbove_envelope_image s hv_cont hq y
  have h_mem : v y ∈ g '' s.X := by
    refine ⟨y, hy, ?_⟩
    simp [g, sub_self, inner_zero_right]
  exact le_csSup h_bdd h_mem

/-- On `s.X`, the upper envelope is bounded above by the convex roof, provided each `q x` is a
subgradient of the roof at `x` and `v ≤ p̌` on `s.X`. -/
lemma upperEnvelope_le_convexRoof_on_X (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {p : Ω → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_subg : ∀ x ∈ s.X,
      q x ∈ SubderivWithinAt (convexRoof s p) s.X x)
    (h_v_le : ∀ x ∈ s.X, v x ≤ convexRoof s p x) :
    ∀ y ∈ s.X, upperEnvelope s v q y ≤ convexRoof s p y := by
  intro y hy
  unfold upperEnvelope
  have hX_ne : s.X.Nonempty := s.X_interior.mono interior_subset
  refine csSup_le (hX_ne.image _) ?_
  rintro z ⟨x, hx, rfl⟩
  have h_sub : convexRoof s p x + inner ℝ (q x) (y - x) ≤ convexRoof s p y :=
    h_subg x hx y hy
  have h_v : v x ≤ convexRoof s p x := h_v_le x hx
  linarith

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
