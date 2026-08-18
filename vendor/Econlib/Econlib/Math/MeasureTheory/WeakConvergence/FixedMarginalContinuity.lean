/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.LusinContinuity
public import Econlib.Math.MeasureTheory.PiUpdate
public import Econlib.Math.MeasureTheory.WeakConvergence.FixedMarginal

/-!
# Weak continuity of density-weighted payoffs on fixed-marginal products

The analytic core of the Milgrom and Weber (1985) existence theorem. For Polish type spaces `T i`
with laws `η i` and compact metrizable action spaces `A i`, the functional

`μ ↦ ∫ u(t, a) · g(t) d(⊗ᵢ μᵢ)`

is weakly continuous in the distributional-strategy profile `μ`, where each `μ i` is a probability
measure on `T i × A i` with first marginal `η i`, the integrand `u` is bounded, jointly measurable,
and continuous in the action block, and `g ∈ L¹(⊗ᵢ η i)` is a density. In the application `g` is
the Radon–Nikodym derivative of the common prior with respect to the product of its marginals
("absolutely continuous information").

The functional is also affine in any one player's strategy, the convexity input to the
best-response fixed-point argument.

## Main statements

* `MeasureTheory.continuousOn_integral_pi_of_fixedFstMarginal` — the weak continuity theorem.
* `MeasureTheory.integral_pi_update_convexCombo` — affinity in a single coordinate.

## Notes

Continuity is uniform over the fixed-marginal product because every member has type-block marginal
exactly `⊗ᵢ η i`, so the approximation errors do not depend on the profile.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

milgrom-weber, distributional strategy, weak convergence, caratheodory, uniform approximation
-/

@[expose] public section

open scoped ENNReal Topology
open TopologicalSpace

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {T A : ι → Type*}
  [∀ i, TopologicalSpace (T i)] [∀ i, PolishSpace (T i)]
  [∀ i, MeasurableSpace (T i)] [∀ i, BorelSpace (T i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, MetrizableSpace (A i)]
  [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)]
  (η : ∀ i, Measure (T i)) [∀ i, IsProbabilityMeasure (η i)]

omit [∀ i, BorelSpace (T i)] [∀ i, CompactSpace (A i)] [∀ i, MetrizableSpace (A i)]
  [∀ i, BorelSpace (A i)] [∀ i, TopologicalSpace (A i)] in
/-- Every profile in the fixed-marginal product has type-block marginal exactly `⊗ᵢ η i`. -/
lemma map_pi_fst_of_fixedFstMarginal {μ : ∀ i, ProbabilityMeasure (T i × A i)}
    (hμ : ∀ i, μ i ∈ fixedFstMarginal (η i)) :
    (Measure.pi fun i => (μ i : Measure (T i × A i))).map (fun s i => (s i).1) =
      Measure.pi η := by
  haveI hsf : ∀ i, SigmaFinite (((μ i : Measure (T i × A i))).map Prod.fst) := fun i => by
    rw [hμ i]; infer_instance
  rw [Measure.pi_map_pi (f := fun i => (Prod.fst : T i × A i → T i))
    (fun i => measurable_fst.aemeasurable)]
  exact congrArg Measure.pi (funext fun i => hμ i)

/-- Integration of a fixed bounded continuous function against the product measure is continuous in
the profile of probability measures. -/
private lemma continuous_integral_pi_boundedContinuousFunction
    (W : BoundedContinuousFunction (∀ i, T i × A i) ℝ) :
    Continuous fun μ : ∀ i, ProbabilityMeasure (T i × A i) =>
      ∫ s, W s ∂(Measure.pi fun i => (μ i : Measure (T i × A i))) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction W).comp
    ProbabilityMeasure.continuous_pi

/-- Bounded continuous uniform approximation of the density-weighted payoff functional over the
fixed-marginal sets: There exists a bounded continuous `W` whose integral against `⊗ᵢ μᵢ` is
uniformly `3 · (max B 0) · ε`-close to the functional for every fixed-marginal profile `μ`. -/
private lemma exists_boundedContinuous_uniform_approx
    {u : (∀ i, T i) × (∀ i, A i) → ℝ} (hu_meas : Measurable u)
    {B : ℝ} (hu_bdd : ∀ p, |u p| ≤ B)
    (hu_cont : ∀ t, Continuous fun a => u (t, a))
    {g : (∀ i, T i) → ℝ} (hg : Integrable g (Measure.pi η))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : BoundedContinuousFunction (∀ i, T i × A i) ℝ,
      ∀ μ : ∀ i, ProbabilityMeasure (T i × A i), (∀ i, μ i ∈ fixedFstMarginal (η i)) →
        |(∫ s, u (fun i => (s i).1, fun i => (s i).2) * g (fun i => (s i).1)
            ∂(Measure.pi fun i => (μ i : Measure (T i × A i)))) -
          ∫ s, W s ∂(Measure.pi fun i => (μ i : Measure (T i × A i)))| ≤ 3 * max B 0 * ε := by
  set B' := max B 0 with hB'_def
  have hu_bdd' : ∀ p, |u p| ≤ B' := fun p => (hu_bdd p).trans (le_max_left _ _)
  set ηhat := Measure.pi η with hηhat_def
  letI : MetricSpace (∀ i, T i) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨f_b, hfb_close, _hfb_int⟩ := hg.exists_boundedContinuous_integral_sub_le hε
  haveI : IsFiniteMeasure (ηhat.withDensity (fun t => ‖g t‖ₑ)) :=
    isFiniteMeasure_withDensity hg.2.ne
  obtain ⟨K, V, hK_cpt, hKc_small, hV_norm, hV_eq⟩ :=
    exists_boundedContinuous_eqOn_compact_prod
      (μ := ηhat + ηhat.withDensity (fun t => ‖g t‖ₑ)) hu_meas hu_cont
      (B := B') (le_max_right B 0) hu_bdd' (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε).ne'
  refine ⟨(V.compContinuous ⟨fun s => (fun i => (s i).1, fun i => (s i).2), by fun_prop⟩) *
      (f_b.compContinuous ⟨fun s => fun i => (s i).1, by fun_prop⟩), fun μ hμ => ?_⟩
  set m := Measure.pi (fun i => (μ i : Measure (T i × A i))) with hm_def
  set tp : (∀ i, T i × A i) → ∀ i, T i := fun s i => (s i).1 with htp_def
  set rdx : (∀ i, T i × A i) → (∀ i, T i) × (∀ i, A i) :=
    fun s => (fun i => (s i).1, fun i => (s i).2) with hrdx_def
  have htp_meas : Measurable tp := measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst
  have hrdx_meas : Measurable rdx :=
    htp_meas.prodMk (measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd)
  haveI hm_prob : IsProbabilityMeasure m := by rw [hm_def]; infer_instance
  have hmap : m.map tp = ηhat := map_pi_fst_of_fixedFstMarginal η hμ
  have hg_comp : Integrable (fun s => g (tp s)) m := by
    have hg_map : AEStronglyMeasurable g (m.map tp) := by rw [hmap]; exact hg.1
    exact (integrable_map_measure hg_map htp_meas.aemeasurable).1 (by rw [hmap]; exact hg)
  have hu_comp_meas : AEStronglyMeasurable (fun s => u (rdx s)) m :=
    (hu_meas.comp hrdx_meas).aestronglyMeasurable
  have hexact_int : Integrable (fun s => u (rdx s) * g (tp s)) m :=
    hg_comp.bdd_mul hu_comp_meas (ae_of_all _ fun s => by
      simpa [Real.norm_eq_abs] using hu_bdd' (rdx s))
  have hfb_comp : Integrable (fun s => f_b (tp s)) m := by
    have hfb_map : AEStronglyMeasurable (⇑f_b) (m.map tp) := f_b.continuous.aestronglyMeasurable
    simpa [Function.comp_def] using
      (integrable_map_measure hfb_map htp_meas.aemeasurable).1
        (by rw [hmap]; exact f_b.integrable _)
  have hW_int : Integrable
      (fun s => V (rdx s) * f_b (tp s)) m :=
    hfb_comp.bdd_mul ((V.continuous.measurable.comp hrdx_meas).aestronglyMeasurable)
      (ae_of_all _ fun s => V.norm_coe_le_norm (rdx s))
  have hKc_meas : MeasurableSet Kᶜ := hK_cpt.isClosed.measurableSet.compl
  have hV_bdd : ∀ p, |V p| ≤ B' := fun p => le_trans (by
    simpa [Real.norm_eq_abs] using V.norm_coe_le_norm p) hV_norm
  -- Pointwise: on the slab `V = u`, so the first difference vanishes; off it bound `|u - V| ≤ 2B'`.
  have hpoint : ∀ s, |u (rdx s) * g (tp s) - V (rdx s) * f_b (tp s)| ≤
      Set.indicator (tp ⁻¹' Kᶜ) (fun s' => 2 * B' * |g (tp s')|) s
        + B' * |g (tp s) - f_b (tp s)| := by
    intro s
    have hsplit : u (rdx s) * g (tp s) - V (rdx s) * f_b (tp s)
        = (u (rdx s) - V (rdx s)) * g (tp s) + V (rdx s) * (g (tp s) - f_b (tp s)) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rcases Classical.em (tp s ∈ K) with hsK | hsK
      · have hVu : V (rdx s) = u (rdx s) := hV_eq (rdx s) hsK
        have hzero : |(u (rdx s) - V (rdx s)) * g (tp s)| = 0 := by
          rw [hVu]; simp
        rw [hzero]
        exact Set.indicator_nonneg (fun s' _ => by positivity) s
      · have hmem : s ∈ tp ⁻¹' Kᶜ := hsK
        rw [Set.indicator_of_mem hmem, abs_mul]
        have habs : |u (rdx s) - V (rdx s)| ≤ 2 * B' := by
          calc |u (rdx s) - V (rdx s)| ≤ |u (rdx s)| + |V (rdx s)| := by
                simpa using abs_add_le (u (rdx s)) (-(V (rdx s)))
            _ ≤ B' + B' := add_le_add (hu_bdd' _) (hV_bdd _)
            _ = 2 * B' := by ring
        exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hV_bdd _) (abs_nonneg _)
  have hind_int : Integrable
      (Set.indicator (tp ⁻¹' Kᶜ) fun s' => 2 * B' * |g (tp s')|) m :=
    ((hg_comp.abs.const_mul _).indicator (htp_meas hKc_meas))
  have hsecond_int : Integrable (fun s => B' * |g (tp s) - f_b (tp s)|) m :=
    ((hg_comp.sub hfb_comp).abs.const_mul _)
  -- The `g`-tail over `Kᶜ` is small: the Lusin base measure was chosen to control it.
  have htail : ∫ t in Kᶜ, |g t| ∂ηhat ≤ ε := by
    have htail_lint : ∫⁻ t in Kᶜ, ‖g t‖ₑ ∂ηhat ≤ ENNReal.ofReal ε := by
      calc ∫⁻ t in Kᶜ, ‖g t‖ₑ ∂ηhat
          = ηhat.withDensity (fun t => ‖g t‖ₑ) Kᶜ := (withDensity_apply _ hKc_meas).symm
        _ ≤ (ηhat + ηhat.withDensity fun t => ‖g t‖ₑ) Kᶜ := by
            rw [Measure.add_apply]; exact le_add_self
        _ ≤ ENNReal.ofReal ε := hKc_small
    have heq : ∫ t in Kᶜ, |g t| ∂ηhat = (∫⁻ t in Kᶜ, ‖g t‖ₑ ∂ηhat).toReal := by
      simpa [Real.norm_eq_abs] using
        integral_norm_eq_lintegral_enorm (hg.1.restrict (s := Kᶜ))
    rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal hε.le htail_lint
  have hterm1 : ∫ s, Set.indicator (tp ⁻¹' Kᶜ) (fun s' => 2 * B' * |g (tp s')|) s ∂m
      ≤ 2 * B' * ε := by
    have habs_map : AEStronglyMeasurable (fun t => |g t|) (m.map tp) := by
      rw [hmap]; simpa [Real.norm_eq_abs] using hg.1.norm
    calc ∫ s, Set.indicator (tp ⁻¹' Kᶜ) (fun s' => 2 * B' * |g (tp s')|) s ∂m
        = ∫ s in tp ⁻¹' Kᶜ, 2 * B' * |g (tp s)| ∂m := integral_indicator (htp_meas hKc_meas)
      _ = 2 * B' * ∫ s in tp ⁻¹' Kᶜ, |g (tp s)| ∂m := integral_const_mul _ _
      _ = 2 * B' * ∫ t in Kᶜ, |g t| ∂(m.map tp) := by
          rw [setIntegral_map hKc_meas habs_map htp_meas.aemeasurable]
      _ = 2 * B' * ∫ t in Kᶜ, |g t| ∂ηhat := by rw [hmap]
      _ ≤ 2 * B' * ε := by
          have hB'_nonneg : (0 : ℝ) ≤ 2 * B' := by positivity
          exact mul_le_mul_of_nonneg_left htail hB'_nonneg
  have hterm2 : ∫ s, B' * |g (tp s) - f_b (tp s)| ∂m ≤ B' * ε := by
    have hsub_map : AEStronglyMeasurable (fun t => |g t - f_b t|) (m.map tp) := by
      rw [hmap]
      simpa [Real.norm_eq_abs] using (hg.1.sub f_b.continuous.aestronglyMeasurable).norm
    calc ∫ s, B' * |g (tp s) - f_b (tp s)| ∂m
        = B' * ∫ s, |g (tp s) - f_b (tp s)| ∂m := integral_const_mul _ _
      _ = B' * ∫ t, |g t - f_b t| ∂(m.map tp) := by
          rw [integral_map htp_meas.aemeasurable hsub_map]
      _ = B' * ∫ t, |g t - f_b t| ∂ηhat := by rw [hmap]
      _ ≤ B' * ε := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right B 0)
          simpa [Real.norm_eq_abs] using hfb_close
  have hgoal : |(∫ s, u (rdx s) * g (tp s) ∂m) - ∫ s, V (rdx s) * f_b (tp s) ∂m|
      ≤ 3 * B' * ε := by
    calc |(∫ s, u (rdx s) * g (tp s) ∂m) - ∫ s, V (rdx s) * f_b (tp s) ∂m|
        = |∫ s, (u (rdx s) * g (tp s) - V (rdx s) * f_b (tp s)) ∂m| := by
          rw [integral_sub hexact_int hW_int]
      _ ≤ ∫ s, |u (rdx s) * g (tp s) - V (rdx s) * f_b (tp s)| ∂m :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s, (Set.indicator (tp ⁻¹' Kᶜ) (fun s' => 2 * B' * |g (tp s')|) s
            + B' * |g (tp s) - f_b (tp s)|) ∂m := by
          refine integral_mono (hexact_int.sub hW_int).abs (hind_int.add hsecond_int) hpoint
      _ = (∫ s, Set.indicator (tp ⁻¹' Kᶜ) (fun s' => 2 * B' * |g (tp s')|) s ∂m)
            + ∫ s, B' * |g (tp s) - f_b (tp s)| ∂m := integral_add hind_int hsecond_int
      _ ≤ 2 * B' * ε + B' * ε := add_le_add hterm1 hterm2
      _ = 3 * B' * ε := by ring
  exact hgoal

/-- **Weak continuity of density-weighted payoff functionals on fixed-marginal products**
(Milgrom–Weber). Let `u` be bounded, jointly measurable, and continuous in the action block for
each fixed type block, and let `g ∈ L¹(⊗ᵢ η i)`. Then

`μ ↦ ∫ u(t(s), a(s)) · g(t(s)) d(⊗ᵢ μᵢ)(s)`

is continuous on the product of the fixed-marginal sets `{μᵢ : (μᵢ)₁ = η i}` in the topology of
weak convergence. -/
theorem continuousOn_integral_pi_of_fixedFstMarginal
    {u : (∀ i, T i) × (∀ i, A i) → ℝ} (hu_meas : Measurable u)
    {B : ℝ} (hu_bdd : ∀ p, |u p| ≤ B)
    (hu_cont : ∀ t, Continuous fun a => u (t, a))
    {g : (∀ i, T i) → ℝ} (hg : Integrable g (Measure.pi η)) :
    ContinuousOn
      (fun μ : ∀ i, ProbabilityMeasure (T i × A i) =>
        ∫ s, u (fun i => (s i).1, fun i => (s i).2) * g (fun i => (s i).1)
          ∂(Measure.pi fun i => (μ i : Measure (T i × A i))))
      (Set.univ.pi fun i => fixedFstMarginal (η i)) := by
  have hex : ∀ n : ℕ, ∃ W : BoundedContinuousFunction (∀ i, T i × A i) ℝ,
      ∀ μ : ∀ i, ProbabilityMeasure (T i × A i), (∀ i, μ i ∈ fixedFstMarginal (η i)) →
        |(∫ s, u (fun i => (s i).1, fun i => (s i).2) * g (fun i => (s i).1)
            ∂(Measure.pi fun i => (μ i : Measure (T i × A i)))) -
          ∫ s, W s ∂(Measure.pi fun i => (μ i : Measure (T i × A i)))|
          ≤ 3 * max B 0 * (1 / (n + 1)) := fun n =>
    exists_boundedContinuous_uniform_approx η hu_meas hu_bdd hu_cont hg (by positivity)
  choose W hW using hex
  have huniform : TendstoUniformlyOn
      (fun n μ => ∫ s, (W n) s ∂(Measure.pi fun i => (μ i : Measure (T i × A i))))
      (fun μ : ∀ i, ProbabilityMeasure (T i × A i) =>
        ∫ s, u (fun i => (s i).1, fun i => (s i).2) * g (fun i => (s i).1)
          ∂(Measure.pi fun i => (μ i : Measure (T i × A i))))
      Filter.atTop (Set.univ.pi fun i => fixedFstMarginal (η i)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hbound : Filter.Tendsto (fun n : ℕ => 3 * max B 0 * (1 / ((n : ℝ) + 1)))
        Filter.atTop (𝓝 0) := by
      have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h0.const_mul (3 * max B 0)
    filter_upwards [hbound.eventually (gt_mem_nhds hδ)] with n hn μ hμ
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hW n μ fun i => hμ i (Set.mem_univ i)) hn
  exact huniform.continuousOn (Filter.Eventually.of_forall fun n =>
    (continuous_integral_pi_boundedContinuousFunction (W n)).continuousOn).frequently

omit [∀ (i : ι), BorelSpace (T i)] [∀ (i : ι), CompactSpace (A i)] [∀ (i : ι), BorelSpace (A i)]
  [∀ (i : ι), MetrizableSpace (A i)] [(i : ι) → TopologicalSpace (A i)]
/-- **Affinity of the density-weighted payoff functional in one coordinate.** Replacing player
`i`'s strategy by a convex combination of strategies (taken at the level of measures) takes the
functional to the convex combination of its values. Together with
`continuousOn_integral_pi_of_fixedFstMarginal` this is the convexity input to the best-response
fixed-point argument. -/
theorem integral_pi_update_convexCombo [DecidableEq ι]
    {u : (∀ i, T i) × (∀ i, A i) → ℝ} (hu_meas : Measurable u)
    {B : ℝ} (hu_bdd : ∀ p, |u p| ≤ B)
    {g : (∀ i, T i) → ℝ} (hg : Integrable g (Measure.pi η))
    {μ : ∀ i, ProbabilityMeasure (T i × A i)} (hμ : ∀ i, μ i ∈ fixedFstMarginal (η i))
    (i : ι) {ν₁ ν₂ ξ : ProbabilityMeasure (T i × A i)}
    (hν₁ : ν₁ ∈ fixedFstMarginal (η i)) (hν₂ : ν₂ ∈ fixedFstMarginal (η i))
    -- `_hab` is not used by the affinity algebra (which holds for any nonnegative weights); it
    -- restricts the lemma's contract to convex combinations, where `ξ` is a probability law.
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hab : a + b = 1)
    (hξ : (ξ : Measure (T i × A i)) =
      ENNReal.ofReal a • (ν₁ : Measure (T i × A i)) +
        ENNReal.ofReal b • (ν₂ : Measure (T i × A i))) :
    (∫ s, u (fun j => (s j).1, fun j => (s j).2) * g (fun j => (s j).1)
        ∂(Measure.pi fun j =>
          ((Function.update μ i ξ j : ProbabilityMeasure (T j × A j)) : Measure (T j × A j)))) =
      a * (∫ s, u (fun j => (s j).1, fun j => (s j).2) * g (fun j => (s j).1)
          ∂(Measure.pi fun j =>
            ((Function.update μ i ν₁ j : ProbabilityMeasure (T j × A j)) : Measure (T j × A j))))
        + b * (∫ s, u (fun j => (s j).1, fun j => (s j).2) * g (fun j => (s j).1)
          ∂(Measure.pi fun j =>
            ((Function.update μ i ν₂ j : ProbabilityMeasure (T j × A j)) :
              Measure (T j × A j)))) := by
  classical
  set rdx : (∀ j, T j × A j) → (∀ j, T j) × (∀ j, A j) :=
    fun s => (fun j => (s j).1, fun j => (s j).2) with hrdx_def
  set tp : (∀ j, T j × A j) → ∀ j, T j := fun s j => (s j).1 with htp_def
  set F : (∀ j, T j × A j) → ℝ := fun s => u (rdx s) * g (tp s) with hF_def
  set c₁ : ℝ≥0∞ := ENNReal.ofReal a with hc₁_def
  set c₂ : ℝ≥0∞ := ENNReal.ofReal b with hc₂_def
  have htp_meas : Measurable tp := measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst
  have hrdx_meas : Measurable rdx :=
    htp_meas.prodMk (measurable_pi_lambda _ fun j => (measurable_pi_apply j).snd)
  have hupd_coe : ∀ ν : ProbabilityMeasure (T i × A i),
      (fun j => ((Function.update μ i ν j : ProbabilityMeasure (T j × A j)) :
          Measure (T j × A j))) =
        Function.update (fun j => (μ j : Measure (T j × A j))) i (ν : Measure (T i × A i)) := by
    intro ν
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  have hupd_mem : ∀ (ν : ProbabilityMeasure (T i × A i)), ν ∈ fixedFstMarginal (η i) →
      ∀ j, (Function.update μ i ν j) ∈ fixedFstMarginal (η j) := by
    intro ν hν j
    rcases eq_or_ne j i with rfl | hji
    · simpa only [Function.update_self] using hν
    · simpa only [Function.update_of_ne hji] using hμ j
  have hF_int : ∀ (ρ : ∀ j, ProbabilityMeasure (T j × A j)),
      (∀ j, ρ j ∈ fixedFstMarginal (η j)) →
      Integrable F (Measure.pi fun j => (ρ j : Measure (T j × A j))) := by
    intro ρ hρ
    set m := Measure.pi (fun j => (ρ j : Measure (T j × A j))) with hm_def
    haveI hm_prob : IsProbabilityMeasure m := by rw [hm_def]; infer_instance
    have hmap : m.map tp = Measure.pi η := map_pi_fst_of_fixedFstMarginal η hρ
    have hg_comp : Integrable (fun s => g (tp s)) m := by
      have hg_map : AEStronglyMeasurable g (m.map tp) := by rw [hmap]; exact hg.1
      exact (integrable_map_measure hg_map htp_meas.aemeasurable).1 (by rw [hmap]; exact hg)
    have hu_comp_meas : AEStronglyMeasurable (fun s => u (rdx s)) m :=
      (hu_meas.comp hrdx_meas).aestronglyMeasurable
    exact hg_comp.bdd_mul hu_comp_meas (ae_of_all _ fun s => by
      simpa [Real.norm_eq_abs] using hu_bdd (rdx s))
  have hF_int_ν₁ : Integrable F
      (Measure.pi fun j => ((Function.update μ i ν₁ j :
        ProbabilityMeasure (T j × A j)) : Measure (T j × A j))) :=
    hF_int (Function.update μ i ν₁) (hupd_mem ν₁ hν₁)
  have hF_int_ν₂ : Integrable F
      (Measure.pi fun j => ((Function.update μ i ν₂ j :
        ProbabilityMeasure (T j × A j)) : Measure (T j × A j))) :=
    hF_int (Function.update μ i ν₂) (hupd_mem ν₂ hν₂)
  haveI hμfin : ∀ j, IsFiniteMeasure (μ j : Measure (T j × A j)) := fun j => inferInstance
  haveI hc₁ν₁_fin : IsFiniteMeasure (c₁ • (ν₁ : Measure (T i × A i))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI hc₂ν₂_fin : IsFiniteMeasure (c₂ • (ν₂ : Measure (T i × A i))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hpi_split :
      (Measure.pi fun j => ((Function.update μ i ξ j :
          ProbabilityMeasure (T j × A j)) : Measure (T j × A j))) =
        c₁ • (Measure.pi fun j => ((Function.update μ i ν₁ j :
            ProbabilityMeasure (T j × A j)) : Measure (T j × A j))) +
          c₂ • (Measure.pi fun j => ((Function.update μ i ν₂ j :
            ProbabilityMeasure (T j × A j)) : Measure (T j × A j))) := by
    rw [hupd_coe ξ, hupd_coe ν₁, hupd_coe ν₂, hξ]
    rw [Measure.pi_update_add (fun j => (μ j : Measure (T j × A j))) i
        (c₁ • (ν₁ : Measure (T i × A i))) (c₂ • (ν₂ : Measure (T i × A i)))]
    rw [Measure.pi_update_smul (fun j => (μ j : Measure (T j × A j))) i (c := c₁)
        ENNReal.ofReal_ne_top (ν₁ : Measure (T i × A i)),
      Measure.pi_update_smul (fun j => (μ j : Measure (T j × A j))) i (c := c₂)
        ENNReal.ofReal_ne_top (ν₂ : Measure (T i × A i))]
  rw [hpi_split]
  rw [integral_add_measure
        (hF_int_ν₁.smul_measure ENNReal.ofReal_ne_top)
        (hF_int_ν₂.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]

end MeasureTheory
