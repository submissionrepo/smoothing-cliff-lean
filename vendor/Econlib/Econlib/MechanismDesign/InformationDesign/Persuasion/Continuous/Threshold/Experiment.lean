/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Basic

/-!
# Threshold persuasion: The cutoff experiment

The pass/fail disclosure policy as a `ContinuousExperiment` (Blackwell 1953): The deterministic
kernel sending state `θ` to the binary signal `pass iff u ≤ θ`. This file computes its Bayesian
ingredients in closed form and shows that the signal law is the Bernoulli distribution with success
probability `P(θ ≥ u)`, the posterior at each positive-probability signal is the prior conditioned
on the corresponding side of the cutoff, and the posterior-mean law is exactly
`thresholdTwoPointLaw`.

The qualifier "positive-probability" is essential. The Bayes posterior is a regular conditional
distribution, so its value at a signal of probability zero is version-dependent: The abstract
`posteriorKernel` agrees with the side-conditioned prior only almost everywhere under the signal
law (`posteriorKernel_cutoffExperiment_ae`). At a signal `b` of positive mass the identity is
pointwise: `posteriorLaw prior (cutoffExperiment u) b` equals the **canonical posterior**
`canonicalPosterior` — the prior conditioned on `[u, ∞)` at `true` and on `(-∞, u)` at `false`
(`posteriorLaw_eq_canonical`). The `PositiveSignal` subtype packages the positive-mass condition at
the type level, with `true`/`false` membership characterized by `prior (Ici u) ≠ 0` /
`prior (Iio u) ≠ 0`.

## Main definitions

* `cutoffStatistic` — the pass/fail statistic `θ ↦ (u ≤ θ : Bool)`.
* `cutoffExperiment` — the deterministic cutoff experiment `Kernel ℝ Bool`.
* `PositiveSignal` — the subtype of cutoff signals carrying positive mass under the signal law,
  with membership characterized by `PositiveSignal.true_iff` / `PositiveSignal.false_iff`.
* `canonicalPosterior` — the cutoff-geometry posterior: The prior conditioned on `[u, ∞)` at `true`
  and on `(-∞, u)` at `false`, built directly from the prior rather than the version-dependent
  regular conditional.

## Main statements

* `posteriorKernel_cutoffExperiment_ae` — the posterior of the cutoff experiment is (a.e.) the
  Bayes-conditioned prior: `prior[|Iio u]` at signal `false`, `prior[|Ici u]` at `true`.
* `posteriorLaw_eq_canonical` — at a `PositiveSignal`, the abstract `posteriorLaw` equals the
  `canonicalPosterior` *pointwise* (not merely a.e.).
* `posteriorValue_cutoffExperiment_true` / `_false` — the posterior means at the two signals are
  the conditional expectations `𝔼[θ | θ ∈ [u, b]]` / `𝔼[θ | θ ∈ [a, u]]`.
* `posteriorMeanLaw_cutoffExperiment` — the posterior-mean law of the cutoff experiment is
  `thresholdTwoPointLaw`.

## Notes

`posteriorMeanLaw_cutoffExperiment` connects the two-point law (constructed directly as a
`ProbDist` in `Threshold.Basic`) to the kernel-experiment framework of `Continuous.Basic`: The
two-point law is the posterior-mean law of an experiment, so achievability statements about
`thresholdTwoPointLaw` are achievability statements about disclosure policies.

## References

* Blackwell, David. 1953. “Equivalent Comparisons of Experiments.” *The Annals of Mathematical
  Statistics* 24 (2): 265–72. [https://doi.org/10.1214/aoms/1177729032](https://doi.org/10.1214/aoms/1177729032).
* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, threshold persuasion, cutoff, experiment, posterior, bayes
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

/-! ## The cutoff experiment -/

/-- The **pass/fail statistic**: Signal `true` iff the state clears the cutoff `u`. -/
noncomputable def cutoffStatistic (u : ℝ) : ℝ → Bool := fun θ => if u ≤ θ then true else false

lemma measurable_cutoffStatistic (u : ℝ) : Measurable (cutoffStatistic u) := by
  -- `cutoffStatistic u θ = if u ≤ θ ...`; the set `{θ | u ≤ θ}` is the measurable set `Ici u`
  unfold cutoffStatistic
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- The **cutoff experiment**: The deterministic disclosure policy announcing whether the state
clears the cutoff `u`. -/
noncomputable def cutoffExperiment (u : ℝ) : ContinuousExperiment ℝ Bool :=
  Kernel.deterministic (cutoffStatistic u) (measurable_cutoffStatistic u)

instance (u : ℝ) : IsMarkovKernel (cutoffExperiment u) :=
  Kernel.isMarkovKernel_deterministic (measurable_cutoffStatistic u)

/-! ## The signal law -/

/-- The signal law of the cutoff experiment is the pushforward of the prior under the pass/fail
statistic. -/
lemma signalLaw_cutoffExperiment (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    (signalLaw prior (cutoffExperiment u)).toMeasure
      = prior.toMeasure.map (cutoffStatistic u) := by
  rw [signalLaw_toMeasure, cutoffExperiment,
    Measure.deterministic_comp_eq_map (measurable_cutoffStatistic u)]

/-- Pass probability: The signal-law mass of `{true}` is the prior mass of `[u, ∞)`. -/
lemma signalLaw_cutoffExperiment_true (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    (signalLaw prior (cutoffExperiment u)).toMeasure {true} = prior.toMeasure (Ici u) := by
  rw [signalLaw_cutoffExperiment,
    Measure.map_apply (measurable_cutoffStatistic u) (measurableSet_singleton _)]
  congr 1
  ext θ
  simp only [cutoffStatistic, mem_preimage, mem_singleton_iff, mem_Ici]
  split_ifs with h <;> simp [h]

/-- Fail probability: The signal-law mass of `{false}` is the prior mass of `(-∞, u)`. -/
lemma signalLaw_cutoffExperiment_false (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    (signalLaw prior (cutoffExperiment u)).toMeasure {false} = prior.toMeasure (Iio u) := by
  rw [signalLaw_cutoffExperiment,
    Measure.map_apply (measurable_cutoffStatistic u) (measurableSet_singleton _)]
  congr 1
  ext θ
  simp only [cutoffStatistic, mem_preimage, mem_singleton_iff, mem_Iio]
  split_ifs with h <;> simp [h, not_le.mp]

/-! ## The posterior

The Bayes posterior of the cutoff experiment conditions the prior on the realized side of the
cutoff: `prior[|Iio u]` at a fail signal and `prior[|Ici u]` at a pass signal. -/

/-- **Bayes for the cutoff experiment.** The posterior kernel is, a.e. under the signal law, the
prior conditioned on the realized side of the cutoff: `prior[|Iio u]` at `false` and
`prior[|Ici u]` at `true`. -/
theorem posteriorKernel_cutoffExperiment_ae (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    posteriorKernel prior (cutoffExperiment u)
      =ᵐ[(signalLaw prior (cutoffExperiment u)).toMeasure]
        Kernel.boolKernel (prior.toMeasure[|Iio u]) (prior.toMeasure[|Ici u]) := by
  set μ : Measure ℝ := prior.toMeasure with hμ
  have hmeas := measurable_cutoffStatistic u
  -- Preimage of the pair map `θ ↦ (cutoff θ, θ)` restricted to the two sides of the cutoff.
  have hpre_false : ∀ θ, cutoffStatistic u θ = false ↔ θ ∈ Iio u := by
    intro θ; simp only [cutoffStatistic, mem_Iio]
    split_ifs with h <;> simp [h, not_le.mp]
  have hpre_true : ∀ θ, cutoffStatistic u θ = true ↔ θ ∈ Ici u := by
    intro θ; simp only [cutoffStatistic, mem_Ici]
    split_ifs with h <;> simp [h]
  -- Atom masses of the pushforward statistic law.
  have hmap_false : (μ.map (cutoffStatistic u)) {false} = μ (Iio u) := by
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    congr 1; ext θ; simp only [mem_preimage, mem_singleton_iff]; exact hpre_false θ
  have hmap_true : (μ.map (cutoffStatistic u)) {true} = μ (Ici u) := by
    rw [Measure.map_apply hmeas (measurableSet_singleton _)]
    congr 1; ext θ; simp only [mem_preimage, mem_singleton_iff]; exact hpre_true θ
  have hidentity :
      (cutoffExperiment u ∘ₘ μ) ⊗ₘ
          Kernel.boolKernel (μ[|Iio u]) (μ[|Ici u])
        = (μ ⊗ₘ cutoffExperiment u).map Prod.swap := by
    rw [cutoffExperiment, Measure.deterministic_comp_eq_map hmeas, Measure.compProd_deterministic,
      Measure.map_map measurable_swap (by fun_prop)]
    ext s hs
    rw [Measure.compProd_apply hs, lintegral_fintype]
    rw [Measure.map_apply (by fun_prop) hs]
    set T₀ : Set ℝ := Prod.mk false ⁻¹' s with hT₀
    set T₁ : Set ℝ := Prod.mk true ⁻¹' s with hT₁
    have hT₀_meas : MeasurableSet T₀ := hs.preimage (by fun_prop)
    have hT₁_meas : MeasurableSet T₁ := hs.preimage (by fun_prop)
    -- The conditional-mass identity `μ[T|S] * μ S = μ (S ∩ T)`, valid even when `μ S = 0`.
    have hcond_mul : ∀ (S T : Set ℝ), MeasurableSet S →
        (μ[T | S]) * μ S = μ (S ∩ T) := by
      intro S T hS
      rw [cond_apply hS]
      by_cases hSz : μ S = 0
      · rw [hSz]
        have : μ (S ∩ T) = 0 := measure_mono_null Set.inter_subset_left hSz
        simp [this]
      · rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hSz (measure_ne_top μ S), one_mul]
    rw [Fintype.sum_bool]
    simp only [Kernel.boolKernel_false, Kernel.boolKernel_true, hmap_false, hmap_true]
    rw [hcond_mul (Iio u) T₀ measurableSet_Iio, hcond_mul (Ici u) T₁ measurableSet_Ici]
    have hpre_false_eq :
        (Prod.swap ∘ fun a => (a, cutoffStatistic u a)) ⁻¹' s ∩ Iio u = Iio u ∩ T₀ := by
      ext θ
      simp only [Function.comp, mem_inter_iff, mem_preimage, Prod.swap_prod_mk, hT₀]
      constructor
      · rintro ⟨hθs, hθu⟩
        exact ⟨hθu, by rwa [(hpre_false θ).mpr hθu] at hθs⟩
      · rintro ⟨hθu, hθs⟩
        exact ⟨by rwa [(hpre_false θ).mpr hθu], hθu⟩
    have hpre_true_eq :
        (Prod.swap ∘ fun a => (a, cutoffStatistic u a)) ⁻¹' s ∩ Ici u = Ici u ∩ T₁ := by
      ext θ
      simp only [Function.comp, mem_inter_iff, mem_preimage, Prod.swap_prod_mk, hT₁]
      constructor
      · rintro ⟨hθs, hθu⟩
        exact ⟨hθu, by rwa [(hpre_true θ).mpr hθu] at hθs⟩
      · rintro ⟨hθu, hθs⟩
        exact ⟨by rwa [(hpre_true θ).mpr hθu], hθu⟩
    -- Mass of the preimage = sum of its masses on the two sides of the cutoff.
    have hsplit :
        μ ((Prod.swap ∘ fun a => (a, cutoffStatistic u a)) ⁻¹' s)
          = μ (Iio u ∩ T₀) + μ (Ici u ∩ T₁) := by
      rw [← measure_inter_add_diff _ measurableSet_Iio, hpre_false_eq]
      have hdiff : (Prod.swap ∘ fun a => (a, cutoffStatistic u a)) ⁻¹' s \ Iio u
          = (Prod.swap ∘ fun a => (a, cutoffStatistic u a)) ⁻¹' s ∩ Ici u := by
        rw [diff_eq, compl_Iio]
      rw [hdiff, hpre_true_eq]
    rw [hsplit, add_comm]
  -- The candidate kernel is the posterior (a.e.); the goal is the symmetric statement.
  have hae := ae_eq_posterior_of_compProd_eq (κ := cutoffExperiment u) (μ := μ) hidentity
  refine (Filter.EventuallyEq.symm ?_)
  rw [signalLaw_toMeasure]
  exact hae

/-- At a pass signal of positive probability, the posterior law is the prior conditioned on
`[u, ∞)`. -/
lemma posteriorLaw_cutoffExperiment_true (prior : ProbabilityMeasure ℝ) (u : ℝ)
    (hpos : prior.toMeasure (Ici u) ≠ 0) :
    (posteriorLaw prior (cutoffExperiment u) true).toMeasure = prior.toMeasure[|Ici u] := by
  have hae := posteriorKernel_cutoffExperiment_ae prior u
  have hatom : (signalLaw prior (cutoffExperiment u)).toMeasure {true} ≠ 0 := by
    rw [signalLaw_cutoffExperiment_true]; exact hpos
  rw [Filter.EventuallyEq, ae_iff] at hae
  by_contra hne
  apply hatom
  refine measure_mono_null (fun x (hx : x = true) => ?_) hae
  rw [hx]
  simp only [mem_setOf_eq, Kernel.boolKernel_true]
  rwa [posteriorLaw_toMeasure] at hne

/-- At a fail signal of positive probability, the posterior law is the prior conditioned on
`(-∞, u)`. -/
lemma posteriorLaw_cutoffExperiment_false (prior : ProbabilityMeasure ℝ) (u : ℝ)
    (hpos : prior.toMeasure (Iio u) ≠ 0) :
    (posteriorLaw prior (cutoffExperiment u) false).toMeasure = prior.toMeasure[|Iio u] := by
  have hae := posteriorKernel_cutoffExperiment_ae prior u
  have hatom : (signalLaw prior (cutoffExperiment u)).toMeasure {false} ≠ 0 := by
    rw [signalLaw_cutoffExperiment_false]; exact hpos
  rw [Filter.EventuallyEq, ae_iff] at hae
  by_contra hne
  apply hatom
  refine measure_mono_null (fun x (hx : x = false) => ?_) hae
  rw [hx]
  simp only [mem_setOf_eq, Kernel.boolKernel_false]
  rwa [posteriorLaw_toMeasure] at hne

/-! ## Positive signals and the canonical posterior

At a signal of probability zero the regular conditional `posteriorKernel` is version-dependent,
so a pointwise posterior identity is only available at signals carrying positive mass. We package
that side condition as the `PositiveSignal` subtype and read off, for each positive signal, a
*canonical* posterior built directly from the cutoff geometry — the prior conditioned on the
realized side. -/

/-- A **positive cutoff signal**: A Boolean signal of the cutoff experiment carrying strictly
positive mass under the signal law. At such signals the Bayes posterior is determined pointwise
(`posteriorLaw_eq_canonical`); at a zero-mass signal the regular conditional is
version-dependent. -/
def PositiveSignal (prior : ProbabilityMeasure ℝ) (u : ℝ) : Type :=
  {b : Bool // (signalLaw prior (cutoffExperiment u)).toMeasure {b} ≠ 0}

/-- The pass signal `true` is positive exactly when the prior assigns positive mass to `[u, ∞)`. -/
lemma PositiveSignal.true_iff (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    (signalLaw prior (cutoffExperiment u)).toMeasure {true} ≠ 0 ↔ prior.toMeasure (Ici u) ≠ 0 := by
  rw [signalLaw_cutoffExperiment_true]

/-- The fail signal `false` is positive exactly when the prior assigns positive mass to
`(-∞, u)`. -/
lemma PositiveSignal.false_iff (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    (signalLaw prior (cutoffExperiment u)).toMeasure {false} ≠ 0 ↔ prior.toMeasure (Iio u) ≠ 0 := by
  rw [signalLaw_cutoffExperiment_false]

/-- Construct the pass signal as a `PositiveSignal` from positive prior mass above the cutoff. -/
def PositiveSignal.mkTrue (prior : ProbabilityMeasure ℝ) (u : ℝ)
    (hpos : prior.toMeasure (Ici u) ≠ 0) : PositiveSignal prior u :=
  ⟨true, (PositiveSignal.true_iff prior u).mpr hpos⟩

/-- Construct the fail signal as a `PositiveSignal` from positive prior mass below the cutoff. -/
def PositiveSignal.mkFalse (prior : ProbabilityMeasure ℝ) (u : ℝ)
    (hpos : prior.toMeasure (Iio u) ≠ 0) : PositiveSignal prior u :=
  ⟨false, (PositiveSignal.false_iff prior u).mpr hpos⟩

/-- The **canonical posterior** at a cutoff signal, read off directly from the cutoff geometry: The
prior conditioned on `[u, ∞)` at a pass (`true`) signal and on `(-∞, u)` at a fail (`false`)
signal. Unlike the abstract `posteriorKernel`, this is a concrete construction with no version
ambiguity; it coincides with the Bayes posterior at every positive signal
(`posteriorLaw_eq_canonical`). -/
noncomputable def canonicalPosterior (prior : ProbabilityMeasure ℝ) (u : ℝ) (b : Bool) :
    Measure ℝ :=
  bif b then prior.toMeasure[|Ici u] else prior.toMeasure[|Iio u]

@[simp] lemma canonicalPosterior_true (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    canonicalPosterior prior u true = prior.toMeasure[|Ici u] := rfl

@[simp] lemma canonicalPosterior_false (prior : ProbabilityMeasure ℝ) (u : ℝ) :
    canonicalPosterior prior u false = prior.toMeasure[|Iio u] := rfl

/-- At a positive pass signal the canonical posterior is a probability measure (the prior
conditioned on `[u, ∞)`, a positive-mass set). -/
instance canonicalPosterior_true_isProbabilityMeasure (prior : ProbabilityMeasure ℝ) (u : ℝ)
    [hpos : Fact (prior.toMeasure (Ici u) ≠ 0)] :
    IsProbabilityMeasure (canonicalPosterior prior u true) := by
  rw [canonicalPosterior_true]
  exact ProbabilityTheory.cond_isProbabilityMeasure hpos.out

/-- At a positive fail signal the canonical posterior is a probability measure (the prior
conditioned on `(-∞, u)`, a positive-mass set). -/
instance canonicalPosterior_false_isProbabilityMeasure (prior : ProbabilityMeasure ℝ) (u : ℝ)
    [hpos : Fact (prior.toMeasure (Iio u) ≠ 0)] :
    IsProbabilityMeasure (canonicalPosterior prior u false) := by
  rw [canonicalPosterior_false]
  exact ProbabilityTheory.cond_isProbabilityMeasure hpos.out

/-- **Pointwise Bayes at a positive cutoff signal.** At any `PositiveSignal`, the abstract
posterior law equals the canonical cutoff-geometry posterior. This is a pointwise equality, not the
a.e. identity of `posteriorKernel_cutoffExperiment_ae`: The positive-mass condition packaged in the
subtype supplies exactly the hypothesis the version-dependence argument needs. -/
theorem posteriorLaw_eq_canonical (prior : ProbabilityMeasure ℝ) (u : ℝ)
    (s : PositiveSignal prior u) :
    (posteriorLaw prior (cutoffExperiment u) s.val).toMeasure
      = canonicalPosterior prior u s.val := by
  obtain ⟨b, hb⟩ := s
  cases b with
  | true =>
    -- positive mass at `true` ⟹ positive prior mass on `[u, ∞)`; apply the pass-side identity
    rw [canonicalPosterior_true]
    exact posteriorLaw_cutoffExperiment_true prior u ((PositiveSignal.true_iff prior u).mp hb)
  | false =>
    -- positive mass at `false` ⟹ positive prior mass on `(-∞, u)`; apply the fail-side identity
    rw [canonicalPosterior_false]
    exact posteriorLaw_cutoffExperiment_false prior u ((PositiveSignal.false_iff prior u).mp hb)

/-! ## Posterior means: The `ContDist` closed forms

For a prior given by a continuous density supported on `[a, b]` with an interior cutoff
`u ∈ (a, b)`, the two posterior means are the conditional expectations on the two cells of the
threshold partition — the atoms of `thresholdTwoPointLaw`. -/

variable (d : Econlib.Probability.ContDist) {a u b : ℝ}

/-- Ray mass of a compactly-supported `ContDist`: The mass of `[u, ∞)` is `prob_interval u b` when
the density vanishes outside `[a, b]`. -/
-- `_hub` (`u ≤ b`) fixes the cutoff inside the support for symmetry with the fail-case lemma; it is
-- not needed now that `prob_interval` is the (atomless) closed-interval mass.
lemma contDist_toMeasure_Ici (_hub : u ≤ b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    d.toMeasure (Ici u) = ENNReal.ofReal (d.prob_interval u b) := by
  rw [d.toMeasure_eq, withDensity_apply _ measurableSet_Ici]
  have hcongr :
      ∫⁻ x in Ici u, ENNReal.ofReal (d.density x)
        = ∫⁻ x in Icc u b, ENNReal.ofReal (d.density x) := by
    have hae :
        (fun x => ENNReal.ofReal (d.density x)) =ᵐ[volume.restrict (Ici u)]
          (Icc u b).indicator (fun x => ENNReal.ofReal (d.density x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      by_cases hxb : x ∈ Icc u b
      · rw [indicator_of_mem hxb]
      · rw [Set.indicator_of_notMem hxb, hsupport x (fun hmem => hxb ⟨hx, hmem.2⟩),
          ENNReal.ofReal_zero]
    rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.mpr (Icc_subset_Ici_self)]
  rw [hcongr]
  -- Convert the Lebesgue integral of the nonnegative density to `ofReal` of the Bochner
  -- integral; the resulting `∫ x in Icc u b, density` is `prob_interval u b` by definition
  -- (`congr 1` closes).
  rw [← ofReal_integral_eq_lintegral_ofReal d.integrable.integrableOn
    (ae_restrict_of_ae (ae_of_all _ d.nonneg))]
  congr 1

/-- Ray mass of a compactly-supported `ContDist`: The mass of `(-∞, u)` is `prob_interval a u` when
the density vanishes outside `[a, b]` (the density measure carries no atom at `u`). -/
-- `_hau` (`a ≤ u`) and `_hub` (`u ≤ b`) fix the cutoff inside the support `[a, b]` for symmetry
-- with `contDist_toMeasure_Ici`; neither is needed for the ray-mass identity `μ (Iio u) =
-- prob_interval a u` now that `prob_interval` is the (atomless) closed-interval mass.
lemma contDist_toMeasure_Iio (_hau : a ≤ u) (_hub : u ≤ b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    d.toMeasure (Iio u) = ENNReal.ofReal (d.prob_interval a u) := by
  -- symmetric: the ray integral collapses to `Ioo a u`, which differs from `Ioc a u` (hence from
  -- the interval integral `∫ a..u`) only by the Lebesgue-null endpoint `{u}`
  rw [d.toMeasure_eq, withDensity_apply _ measurableSet_Iio]
  have hcongr :
      ∫⁻ x in Iio u, ENNReal.ofReal (d.density x)
        = ∫⁻ x in Ioo a u, ENNReal.ofReal (d.density x) := by
    have hae :
        (fun x => ENNReal.ofReal (d.density x)) =ᵐ[volume.restrict (Iio u)]
          (Ioo a u).indicator (fun x => ENNReal.ofReal (d.density x)) := by
      -- The only mismatch with the indicator is the single point `x = a`, which is `volume`-null.
      filter_upwards [ae_restrict_mem measurableSet_Iio,
        (Filter.Eventually.filter_mono (ae_restrict_le)
          (compl_mem_ae_iff.mpr (measure_singleton (a : ℝ))) : ∀ᵐ x ∂volume.restrict (Iio u),
            x ∈ ({a} : Set ℝ)ᶜ)] with x hx hxa
      by_cases hxo : x ∈ Ioo a u
      · rw [indicator_of_mem hxo]
      · rw [Set.indicator_of_notMem hxo]
        -- `x < u`, `x ∉ Ioo a u`, `x ≠ a` ⟹ `x < a`, so the density vanishes.
        have hxlt : x < a := by
          rcases lt_trichotomy x a with h | h | h
          · exact h
          · exact absurd h hxa
          · exact absurd ⟨h, hx⟩ hxo
        rw [hsupport x (fun hmem => absurd hmem.1 (not_le.mpr hxlt)), ENNReal.ofReal_zero]
    rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (Ioo_subset_Iio_self)]
  rw [hcongr]
  rw [← ofReal_integral_eq_lintegral_ofReal d.integrable.integrableOn
    (ae_restrict_of_ae (ae_of_all _ d.nonneg))]
  congr 1
  rw [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
    ← integral_Ioc_eq_integral_Ioo]

/-- For a `ContDist` prior supported on `[a, b]`, the pass probability is `prob_interval u b`. -/
-- `_hau` (`a < u`) fixes the cutoff strictly inside the support for symmetry with the fail-case
-- lemma; the pass probability `μ {true} = prob_interval u b` only needs `u ≤ b`.
lemma signalLaw_cutoffExperiment_true_contDist (_hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure {true}
      = ENNReal.ofReal (d.prob_interval u b) := by
  -- `signalLaw_cutoffExperiment_true` + `Ici u` agrees with `Icc u b` up to the `d`-null set
  -- `(b, ∞)`
  rw [signalLaw_cutoffExperiment_true, Econlib.Probability.ContDist.toProbDist_toMeasure,
    contDist_toMeasure_Ici d hub.le (fun x hx => hsupport x hx)]

/-- For a `ContDist` prior supported on `[a, b]`, the fail probability is `prob_interval a u`. -/
lemma signalLaw_cutoffExperiment_false_contDist (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0) :
    (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure {false}
      = ENNReal.ofReal (d.prob_interval a u) := by
  -- `signalLaw_cutoffExperiment_false` + `Iio u` agrees with `Icc a u` up to the `d`-null sets
  -- `(-∞, a)` and `{u}` (the density measure is atomless)
  rw [signalLaw_cutoffExperiment_false, Econlib.Probability.ContDist.toProbDist_toMeasure,
    contDist_toMeasure_Iio d hau.le hub.le (fun x hx => hsupport x hx)]

/-- The posterior mean at a pass signal is `𝔼[θ | θ ∈ [u, b]]`. -/
lemma posteriorValue_cutoffExperiment_true (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    posteriorValue d.toProbDist (cutoffExperiment u) id true
      = d.conditionalExpectOrZero id (Icc u b) := by
  have hmass_pos : 0 < d.prob_interval u b :=
    d.prob_interval_pos_of_pos_density hub
      (fun x hx => hd_pos x (Icc_subset_Icc hau.le le_rfl hx))
      (hd_cont.mono (Icc_subset_Icc hau.le le_rfl))
  have hmass_ne : d.toProbDist.toMeasure (Ici u) ≠ 0 := by
    rw [Econlib.Probability.ContDist.toProbDist_toMeasure,
      contDist_toMeasure_Ici d hub.le (fun x hx => hsupport x hx)]
    exact (ENNReal.ofReal_ne_zero_iff.mpr hmass_pos)
  rw [posteriorValue, ← posteriorLaw_toMeasure,
    posteriorLaw_cutoffExperiment_true d.toProbDist u hmass_ne,
    Econlib.Probability.ContDist.toProbDist_toMeasure, ProbabilityTheory.cond,
    integral_smul_measure]
  rw [contDist_toMeasure_Ici d hub.le (fun x hx => hsupport x hx),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hmass_pos.le]
  have hint :
      ∫ x in Ici u, id x ∂d.toMeasure = ∫ x in Icc u b, d.density x * x := by
    rw [d.setIntegral_toMeasure_eq id measurableSet_Ici]
    simp only [id_eq]
    rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hxu : u ≤ x
    · by_cases hxb : x ≤ b
      · rw [indicator_of_mem (by exact ⟨hxu, hxb⟩ : x ∈ Icc u b),
          indicator_of_mem (mem_Ici.mpr hxu)]
      · rw [indicator_of_mem (mem_Ici.mpr hxu),
          Set.indicator_of_notMem (fun h => hxb h.2),
          hsupport x (fun h => hxb h.2), zero_mul]
    · rw [Set.indicator_of_notMem (fun h => hxu (mem_Ici.mp h)),
        Set.indicator_of_notMem (fun h => hxu h.1)]
  rw [hint]
  -- The conditional expectation as a density-weighted ratio.
  have hset_pos : 0 < ∫ x in Icc u b, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hub.le] using hmass_pos
  rw [d.conditionalExpectOrZero_eq_of_pos id (Icc u b) hset_pos]
  have hmass_eq : ∫ x in Icc u b, d.density x = d.prob_interval u b := rfl
  rw [hmass_eq, smul_eq_mul, div_eq_inv_mul]
  simp [id]

/-- The posterior mean at a fail signal is `𝔼[θ | θ ∈ [a, u]]`. -/
lemma posteriorValue_cutoffExperiment_false (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    posteriorValue d.toProbDist (cutoffExperiment u) id false
      = d.conditionalExpectOrZero id (Icc a u) := by
  have hmass_pos : 0 < d.prob_interval a u :=
    d.prob_interval_pos_of_pos_density hau
      (fun x hx => hd_pos x (Icc_subset_Icc le_rfl hub.le hx))
      (hd_cont.mono (Icc_subset_Icc le_rfl hub.le))
  have hmass_ne : d.toProbDist.toMeasure (Iio u) ≠ 0 := by
    rw [Econlib.Probability.ContDist.toProbDist_toMeasure,
      contDist_toMeasure_Iio d hau.le hub.le (fun x hx => hsupport x hx)]
    exact (ENNReal.ofReal_ne_zero_iff.mpr hmass_pos)
  rw [posteriorValue, ← posteriorLaw_toMeasure,
    posteriorLaw_cutoffExperiment_false d.toProbDist u hmass_ne,
    Econlib.Probability.ContDist.toProbDist_toMeasure, ProbabilityTheory.cond,
    integral_smul_measure]
  rw [contDist_toMeasure_Iio d hau.le hub.le (fun x hx => hsupport x hx),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hmass_pos.le]
  have hint :
      ∫ x in Iio u, id x ∂d.toMeasure = ∫ x in Icc a u, d.density x * x := by
    rw [d.setIntegral_toMeasure_eq id measurableSet_Iio]
    simp only [id_eq]
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [(compl_mem_ae_iff.mpr (measure_singleton (u : ℝ)) :
      ∀ᵐ x ∂volume, x ∈ ({u} : Set ℝ)ᶜ)] with x hxu_ne
    by_cases hxu : x < u
    · by_cases hxa : a ≤ x
      · rw [indicator_of_mem (mem_Iio.mpr hxu),
          indicator_of_mem (mem_Icc.mpr ⟨hxa, hxu.le⟩)]
      · rw [indicator_of_mem (mem_Iio.mpr hxu),
          Set.indicator_of_notMem (fun h => hxa h.1),
          hsupport x (fun h => hxa h.1), zero_mul]
    · -- `x ∉ Iio u`; and `x ≠ u`, so `x ∉ Icc a u` either.
      have hxu_gt : u < x := lt_of_le_of_ne (not_lt.mp hxu) (Ne.symm (by simpa using hxu_ne))
      rw [Set.indicator_of_notMem (fun h => hxu (mem_Iio.mp h)),
        Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hxu_gt))]
  rw [hint]
  -- The conditional expectation as a density-weighted ratio.
  have hset_pos : 0 < ∫ x in Icc a u, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hau.le] using hmass_pos
  rw [d.conditionalExpectOrZero_eq_of_pos id (Icc a u) hset_pos]
  have hmass_eq : ∫ x in Icc a u, d.density x = d.prob_interval a u := rfl
  rw [hmass_eq, smul_eq_mul, div_eq_inv_mul]
  simp [id]

/-! ## The posterior-mean law -/

/-- **The cutoff experiment realizes the two-point law.** The posterior-mean law of the cutoff
experiment is exactly `thresholdTwoPointLaw`: The Bernoulli signal law pushed forward through the
two conditional means. -/
theorem posteriorMeanLaw_cutoffExperiment (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    posteriorMeanLaw d.toProbDist (cutoffExperiment u)
        (posteriorValue d.toProbDist (cutoffExperiment u) id)
        ((stronglyMeasurable_posteriorValue d.toProbDist (cutoffExperiment u)
          stronglyMeasurable_id).measurable)
      = thresholdTwoPointLaw d a u b hub.le := by
  classical
  apply Subtype.ext
  change Measure.map (posteriorValue d.toProbDist (cutoffExperiment u) id)
      (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure
      = (thresholdTwoPointLaw d a u b hub.le).toMeasure
  set mfalse : ℝ := d.conditionalExpectOrZero id (Icc a u) with hmfalse_def
  set mtrue : ℝ := d.conditionalExpectOrZero id (Icc u b) with hmtrue_def
  have hpv_false : posteriorValue d.toProbDist (cutoffExperiment u) id false = mfalse :=
    posteriorValue_cutoffExperiment_false d hau hub hsupport hd_pos hd_cont
  have hpv_true : posteriorValue d.toProbDist (cutoffExperiment u) id true = mtrue :=
    posteriorValue_cutoffExperiment_true d hau hub hsupport hd_pos hd_cont
  ext s hs
  -- LHS: pull back `s` through the posterior-value map, then evaluate the Bool signal measure on
  -- its two atoms.
  rw [Measure.map_apply
    (stronglyMeasurable_posteriorValue d.toProbDist (cutoffExperiment u)
      stronglyMeasurable_id).measurable hs]
  have hsignal_split : ∀ (T : Set Bool),
      (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure T
        = (if false ∈ T then (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure {false} else 0)
          + (if true ∈ T then (signalLaw d.toProbDist (cutoffExperiment u)).toMeasure {true}
              else 0) := by
    intro T
    rw [← measure_inter_add_diff T (measurableSet_singleton false)]
    congr 1
    · by_cases hf : false ∈ T
      · rw [if_pos hf, Set.inter_eq_right.mpr (by simpa using hf)]
      · rw [if_neg hf]
        have : T ∩ {false} = ∅ := by
          ext x; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
          rintro ⟨hx, rfl⟩; exact hf hx
        rw [this, measure_empty]
    · by_cases ht : true ∈ T
      · rw [if_pos ht]
        have hdiff : T \ {false} = {true} := by
          ext x; cases x <;> simp_all
        rw [hdiff]
      · rw [if_neg ht]
        have hdiff : T \ {false} = ∅ := by
          ext x; cases x <;> simp_all
        rw [hdiff, measure_empty]
  rw [hsignal_split,
    signalLaw_cutoffExperiment_false_contDist d hau hub (fun x hx => hsupport x hx),
    signalLaw_cutoffExperiment_true_contDist d hau hub (fun x hx => hsupport x hx)]
  simp only [mem_preimage, hpv_false, hpv_true]
  -- RHS: evaluate `thresholdTwoPointLaw` as in `thresholdTwoPointLaw_eq_finMixture_dirac`.
  set p := d.prob_interval u b with hp_def
  set w : Econlib.Probability.FinDist (Fin 2) :=
    Econlib.Probability.FinDist.bernoulli p
      (d.prob_interval_nonneg u b) (d.prob_interval_le_one u b) with hw_def
  set stat : Fin 2 → ℝ :=
    fun i => if i = 0 then mfalse else mtrue with hstat_def
  have hstat_meas : Measurable stat := measurable_of_finite _
  rw [show thresholdTwoPointLaw d a u b hub.le
      = Econlib.Probability.ProbDist.map w.toProbDist stat hstat_meas from rfl,
    Econlib.Probability.ProbDist.map_toMeasure,
    Measure.map_apply hstat_meas hs,
    Econlib.Probability.FinDist.toProbDist_toMeasure, PMF.toMeasure_apply_fintype]
  change
    _ = ∑ x : Fin 2, (stat ⁻¹' s).indicator (⇑w.toPMF) x
  rw [Fin.sum_univ_two]
  -- The Bernoulli `toPMF` values, with `1 - p = prob_interval a u`.
  have hsum_one : d.prob_interval a u + p = 1 :=
    threshold_prob_intervals_sum_one d hau hub (fun x hx => hsupport x hx)
  have hw0 : w.toPMF 0 = ENNReal.ofReal (d.prob_interval a u) := by
    change ENNReal.ofReal (w.pmf 0) = _
    have hpmf0 : w.pmf 0 = 1 - p := by simp [hw_def, Econlib.Probability.FinDist.bernoulli]
    rw [hpmf0]
    congr 1
    linarith
  have hw1 : w.toPMF 1 = ENNReal.ofReal p := by
    change ENNReal.ofReal (w.pmf 1) = _
    rw [hw_def]; simp [Econlib.Probability.FinDist.bernoulli]
  have hind0 : (stat ⁻¹' s).indicator (⇑w.toPMF) 0 = if mfalse ∈ s then w.toPMF 0 else 0 := by
    simp [stat, Set.indicator_apply]
  have hind1 : (stat ⁻¹' s).indicator (⇑w.toPMF) 1 = if mtrue ∈ s then w.toPMF 1 else 0 := by
    simp [stat, Set.indicator_apply]
  rw [hind0, hind1, hw0, hw1]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
