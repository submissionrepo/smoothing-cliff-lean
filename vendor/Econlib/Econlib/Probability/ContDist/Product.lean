/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The IID product of a continuous distribution

For the symmetric independent-private-values auction model, the `n` bidders' types are drawn
independently from a single shared `ContDist`. Their joint law is the `n`-fold product measure on
`Fin n → ℝ`. This file packages that product together with the integration identities the auction
reduced form needs: The coordinate marginal and the coordinate re-draw (reduced-form) bridge, in
both the Bochner and lower-integral forms.

## Main definitions

* `ContDist.piMeasure d n` — the product `Measure.pi (fun _ : Fin n => d.toMeasure)`, a probability
  measure.

## Main statements

* `ContDist.integral_piMeasure_eval` — coordinate marginal: A function of a single coordinate `θ i`
  integrates to its one-dimensional expectation, `∫ θ, f (θ i) ∂(piMeasure) = d.expect f`.
* `ContDist.integral_piMeasure_reduce` — coordinate re-draw identity: Averaging an integrand over a
  fresh draw of coordinate `i` leaves the product integral unchanged,
  `∫ θ, g θ ∂(piMeasure) = ∫ t, (∫ θ', g (update θ' i t) ∂d.toMeasure) ∂(piMeasure)`.
* `ContDist.lintegral_piMeasure_reduce` — the Tonelli analog of `integral_piMeasure_reduce` for an
  `ℝ≥0∞`-valued integrand, carrying no integrability side condition.

## Notes

The coordinate re-draw identity is the ex-post to interim bridge: The inner integral is the
reduced-form average over the other bidders' types, so the identity says expected ex-post
quantities equal expected interim ones. The lower-integral form is the right tool for comparing
`∫⁻ ‖·‖` masses across the coordinate split, since it needs no integrability hypothesis.

## Tags

product measure, iid, fubini, reduced form, marginal
-/

@[expose] public section

open MeasureTheory Function

namespace Econlib.Probability

namespace ContDist

variable (d : ContDist) (n : ℕ)

/-- The `n`-fold IID product of `d` over `Fin n → ℝ`: The joint law of `n` independent draws from
`d`. -/
noncomputable def piMeasure : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => d.toMeasure)

instance isProbabilityMeasure_piMeasure : IsProbabilityMeasure (d.piMeasure n) := by
  have : ∀ _ : Fin n, IsProbabilityMeasure d.toMeasure := fun _ => d.toMeasure_isProbability
  unfold piMeasure
  infer_instance

variable {d n}

/-- **Coordinate marginal.** Integrating a function of a single coordinate against the IID product
recovers the one-dimensional expectation: The `i`-th marginal of `piMeasure` is `d.toMeasure`. -/
lemma integral_piMeasure_eval (i : Fin n) {f : ℝ → ℝ} (hf : Integrable f d.toMeasure) :
    ∫ θ, f (θ i) ∂(d.piMeasure n) = d.expect f := by
  haveI : IsProbabilityMeasure d.toMeasure := d.toMeasure_isProbability
  -- The `i`-th marginal of the IID product is `d.toMeasure`.
  have hmap : Measure.map (Function.eval i) (d.piMeasure n) = d.toMeasure := by
    rw [piMeasure, Measure.pi_map_eval, Finset.prod_eq_one fun _ _ => measure_univ, one_smul]
  -- Push the integral through the evaluation map.
  have heval : ∫ θ, f (θ i) ∂(d.piMeasure n) = ∫ t, f t ∂d.toMeasure := by
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable]
    rw [hmap]; exact hf.aestronglyMeasurable
  rw [heval, d.expect_eq_measure_integral]

/-- **Reduced-form bridge.** The product integral equals the integral over coordinate `i`'s law of
the conditional average over the other coordinates: Fix coordinate `i` at `t`, average the rest,
then average over `t ~ d`. This is the ex-post to interim identity for the symmetric IID auction. -/
lemma integral_piMeasure_reduce (i : Fin n) {h : (Fin n → ℝ) → ℝ}
    (hh : Integrable h (d.piMeasure n)) :
    ∫ θ, h θ ∂(d.piMeasure n)
      = ∫ t, (∫ θ', h (update θ' i t) ∂(d.piMeasure n)) ∂d.toMeasure := by
  -- `i : Fin n` forces `n` to be a successor; split coordinate `i` off the product.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  haveI : IsProbabilityMeasure d.toMeasure := d.toMeasure_isProbability
  set μ : Measure ℝ := d.toMeasure with hμ
  set π : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => μ) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  -- The measurable equivalence splitting coordinate `i` and its measure-preserving property.
  set e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with he
  have hmp : MeasurePreserving e (d.piMeasure (m + 1)) (μ.prod π) := by
    rw [piMeasure, he, hμ, hπ]
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
  have hmps : MeasurePreserving e.symm (μ.prod π) (d.piMeasure (m + 1)) := hmp.symm e
  -- `e.symm p = i.insertNth p.1 p.2`.
  have hesym : ∀ p : ℝ × (Fin m → ℝ), e.symm p = i.insertNth p.1 p.2 := by
    intro p
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    ext j
    rw [Fin.insertNthEquiv_apply]
  -- `h ∘ e.symm` is integrable on the product, as `e.symm` is measure-preserving.
  have hH : Integrable (fun p => h (e.symm p)) (μ.prod π) :=
    hmps.integrable_comp_of_integrable hh
  -- LHS: transport `θ` through `e`, then Fubini over the product.
  have hLHS : ∫ θ, h θ ∂(d.piMeasure (m + 1))
      = ∫ t, ∫ ρ, h (i.insertNth t ρ) ∂π ∂μ := by
    rw [← hmps.integral_comp' (f := e.symm) h, integral_prod _ hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
    simp only [hesym]
  -- For a.e. `t`, the slice `ρ ↦ h (i.insertNth t ρ)` is integrable on `π` (Fubini integrability).
  have hslice : ∀ᵐ t ∂μ, Integrable (fun ρ => h (i.insertNth t ρ)) π := by
    have h1 := ((integrable_prod_iff hH.aestronglyMeasurable).mp hH).1
    refine h1.mono fun t ht => ?_
    refine ht.congr (Filter.Eventually.of_forall fun ρ => ?_)
    simp only [hesym]
  -- RHS inner average: transport `θ'` through `e`, use `update_insertNth`, collapse the `μ` factor.
  have hRHS_inner : ∀ t : ℝ, Integrable (fun ρ => h (i.insertNth t ρ)) π →
      ∫ θ', h (update θ' i t) ∂(d.piMeasure (m + 1))
        = ∫ ρ, h (i.insertNth t ρ) ∂π := by
    intro t hint
    rw [← hmps.integral_comp' (f := e.symm) (fun θ' => h (update θ' i t))]
    have hpoint : ∀ p : ℝ × (Fin m → ℝ),
        h (update (e.symm p) i t) = h (i.insertNth t p.2) := by
      intro p; rw [hesym p, Fin.update_insertNth]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
      integral_prod _ (hint.comp_snd μ)]
    -- The integrand no longer depends on the first coordinate; `μ` is a probability measure.
    simp only []
    rw [integral_const, probReal_univ, one_smul]
  -- Combine: the RHS equals the LHS after Fubini.
  rw [hLHS]
  refine integral_congr_ae ?_
  filter_upwards [hslice] with t ht
  rw [hRHS_inner t ht]

/-- **Lower-integral reduced-form bridge.** The Tonelli analog of `integral_piMeasure_reduce`: For
a measurable `ℝ≥0∞`-valued integrand, the product lower integral equals the lower integral over
coordinate `i`'s law of the conditional lower integral over the other coordinates. Unlike the
Bochner version this carries no integrability side condition. -/
lemma lintegral_piMeasure_reduce (i : Fin n) {h : (Fin n → ℝ) → ENNReal} (hh : Measurable h) :
    ∫⁻ θ, h θ ∂(d.piMeasure n)
      = ∫⁻ t, (∫⁻ θ', h (update θ' i t) ∂(d.piMeasure n)) ∂d.toMeasure := by
  -- `i : Fin n` forces `n` to be a successor; split coordinate `i` off the product.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  haveI : IsProbabilityMeasure d.toMeasure := d.toMeasure_isProbability
  set μ : Measure ℝ := d.toMeasure with hμ
  set π : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => μ) with hπ
  haveI : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  -- The measurable equivalence splitting coordinate `i` and its measure-preserving property.
  set e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with he
  have hmp : MeasurePreserving e (d.piMeasure (m + 1)) (μ.prod π) := by
    rw [piMeasure, he, hμ, hπ]
    exact measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
  have hmps : MeasurePreserving e.symm (μ.prod π) (d.piMeasure (m + 1)) := hmp.symm e
  -- `e.symm p = i.insertNth p.1 p.2`.
  have hesym : ∀ p : ℝ × (Fin m → ℝ), e.symm p = i.insertNth p.1 p.2 := by
    intro p
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    ext j
    rw [Fin.insertNthEquiv_apply]
  -- `h ∘ e.symm` is measurable.
  have hHmeas : Measurable (fun p => h (e.symm p)) := hh.comp e.symm.measurable
  -- LHS: transport `θ` through `e`, then Tonelli over the product.
  have hLHS : ∫⁻ θ, h θ ∂(d.piMeasure (m + 1))
      = ∫⁻ t, ∫⁻ ρ, h (i.insertNth t ρ) ∂π ∂μ := by
    rw [← hmps.lintegral_comp hh, lintegral_prod _ hHmeas.aemeasurable]
    refine lintegral_congr fun t => ?_
    refine lintegral_congr fun ρ => ?_
    simp only [hesym]
  -- RHS inner: transport `θ'` through `e`, use `update_insertNth`, collapse the `μ` factor.
  have hRHS_inner : ∀ t : ℝ,
      ∫⁻ θ', h (update θ' i t) ∂(d.piMeasure (m + 1))
        = ∫⁻ ρ, h (i.insertNth t ρ) ∂π := by
    intro t
    rw [← hmps.lintegral_comp (f := fun θ' => h (update θ' i t))
      (hh.comp measurable_update_left)]
    have hpoint : ∀ p : ℝ × (Fin m → ℝ),
        h (update (e.symm p) i t) = h (i.insertNth t p.2) := by
      intro p; rw [hesym p, Fin.update_insertNth]
    have hins : Measurable (fun ρ : Fin m → ℝ => h (i.insertNth t ρ)) := by
      have hcomp : (fun ρ : Fin m → ℝ => h (i.insertNth t ρ))
          = fun ρ => h (e.symm (t, ρ)) := by funext ρ; rw [hesym]
      rw [hcomp]
      exact (hh.comp e.symm.measurable).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_congr hpoint,
      lintegral_prod (fun a => h (i.insertNth t a.2)) (hins.comp measurable_snd).aemeasurable]
    -- The integrand no longer depends on the first coordinate; `μ` is a probability measure.
    simp only []
    rw [lintegral_const, measure_univ, mul_one]
  rw [hLHS]
  refine lintegral_congr fun t => ?_
  rw [hRHS_inner t]

end ContDist

end Econlib.Probability
