/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.MinkowskiCaratheodory
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ConvexRoof
public import Mathlib.Analysis.Convex.Caratheodory

/-!
# Canonical moment setup from the moment image

`MomentSetup.ofMomentImage` is the smart constructor for the canonical moment setup in which the
moment set `X` is the achievable moment set — the convex hull of the moment image `conv(range m)`.
It discharges all geometric fields (`X_compact`, `X_convex`, `m_mem_X`) and the feasibility field
`moment_surjOn_X` (every `y ∈ X` is the posterior moment of some posterior).  The only input it
cannot discharge is full-dimensionality of the moment image (`X_interior`), required as a
hypothesis.

Packaging the canonical `X = conv(range m)` case as a builder of the general `MomentSetup` type
rather than a separate structure keeps the general type free for setups that describe `X`
extrinsically (e.g. as a polytope) and prove it equals the hull.  See
`DesignNotes/MomentSetupFeasibilityField.md` for the rationale.

## Main definitions

* `MomentSetup.ofMomentImage` — the canonical setup with `X := convexHull ℝ (range m)`.

## Main statements

* `exists_probDist_integral_eq` — every point of `convexHull ℝ (range m)` is the posterior moment
  of some posterior.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).

## Tags

persuasion, moment persuasion, convex hull, caratheodory
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Set MeasureTheory
open Econlib.Probability

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}

/-! ## Auxiliary moment-mixture fact

The convex hull of a compact set is compact in finite dimension — this is
`isCompact_convexHull_of_isCompact` in `Econlib.Math.Analysis.MinkowskiCaratheodory`, imported
above and used directly for the `X_compact` field.

The remaining fact, proved here, is that every point of `convexHull ℝ (range m)` is the posterior
moment of a finite mixture of Dirac masses (the Carathéodory representation realized as a
mixture). -/

/-- The integral of a continuous moment map against a finite Dirac mixture is the corresponding
finite convex combination of moment values.  This is the raw-integral analog of
`posteriorMoment_finMixture`, computed directly so it can be used inside the smart constructor
before a `MomentSetup` is available. -/
lemma integral_finMixture_dirac [CompactSpace Ω] [MeasurableSingletonClass Ω]
    {m : Ω → EuclideanSpace ℝ (Fin n)} (m_continuous : Continuous m)
    {N : ℕ} (w : FinDist (Fin N)) (ω : Fin N → Ω) :
    (∫ a, m a ∂(ProbDist.finMixture w (fun i => ProbDist.dirac (ω i))).toMeasure)
      = ∑ i, w.pmf i • m (ω i) := by
  have hm_int : ∀ μ : ProbDist Ω, MeasureTheory.Integrable m μ.toMeasure := fun μ =>
    m_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold ProbDist.finMixture
  change ∫ a, m a ∂(∑ i, ENNReal.ofReal (w.pmf i) • (ProbDist.dirac (ω i)).toMeasure)
      = ∑ i, w.pmf i • m (ω i)
  rw [MeasureTheory.integral_finset_sum_measure (fun i _ =>
    (hm_int (ProbDist.dirac (ω i))).smul_measure (ENNReal.ofReal_ne_top))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (w.nonneg i)]
  rw [ProbDist.dirac_toMeasure, MeasureTheory.integral_dirac]

/-- **Feasibility of the moment hull.**  Every point of `convexHull ℝ (range m)` is the posterior
moment `∫ m dμ` of some posterior `μ`, namely a finite mixture of Dirac masses obtained from a
Carathéodory representation. -/
lemma exists_probDist_integral_eq [CompactSpace Ω] [MeasurableSingletonClass Ω]
    {m : Ω → EuclideanSpace ℝ (Fin n)} (m_continuous : Continuous m)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ convexHull ℝ (Set.range m)) :
    ∃ μ : ProbDist Ω, (∫ ω, m ω ∂μ.toMeasure) = y := by
  classical
  -- Carathéodory representation `y = ∑ wᵢ • zᵢ`, `zᵢ ∈ range m`, `wᵢ > 0`, `∑ wᵢ = 1`.
  obtain ⟨ι, hιfin, z, w, hz_range, _hz_aff, hw_pos, hw_sum, hw_comb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  haveI : Fintype ι := hιfin
  -- Restate Carathéodory facts under the ambient `Fintype` instance (avoids instance diamond).
  have hinst : this = hιfin := Subsingleton.elim _ _
  have hw_sum : ∑ i, w i = 1 := by rw [hinst]; exact hw_sum
  have hw_comb : ∑ i, w i • z i = y := by rw [hinst]; exact hw_comb
  -- Reindex to `Fin (card ι)`.
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  -- Preimages `ω k` with `m (ω k) = z (e.symm k)`.
  have hpre : ∀ k : Fin (Fintype.card ι), ∃ a : Ω, m a = z (e.symm k) := fun k =>
    hz_range ⟨e.symm k, rfl⟩
  let ω : Fin (Fintype.card ι) → Ω := fun k => (hpre k).choose
  have hω : ∀ k, m (ω k) = z (e.symm k) := fun k => (hpre k).choose_spec
  -- The reindexed weights as a `FinDist`.
  let W : FinDist (Fin (Fintype.card ι)) :=
    { pmf := fun k => w (e.symm k)
      nonneg := fun k => (hw_pos (e.symm k)).le
      sum_one := (Equiv.sum_comp e.symm w).trans hw_sum }
  refine ⟨ProbDist.finMixture W (fun k => ProbDist.dirac (ω k)), ?_⟩
  rw [integral_finMixture_dirac m_continuous W ω]
  -- `∑ₖ W(k) • m(ω k) = ∑ₖ w(e.symm k) • z(e.symm k) = ∑ᵢ wᵢ • zᵢ = y`.
  calc ∑ k, W.pmf k • m (ω k)
      = ∑ k, w (e.symm k) • z (e.symm k) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hω k]
    _ = ∑ i, w i • z i := Equiv.sum_comp e.symm (fun i => w i • z i)
    _ = y := hw_comb

/-- The canonical moment setup whose moment set is the convex hull of the moment image,
`X := convexHull ℝ (range m)`.  Requires a compact state space (so the hull is compact) and
full-dimensionality of the moment image; every other field — including moment feasibility — is
discharged automatically. -/
noncomputable def MomentSetup.ofMomentImage [CompactSpace Ω] [MeasurableSingletonClass Ω]
    (m : Ω → EuclideanSpace ℝ (Fin n)) (m_continuous : Continuous m)
    (prior : ProbDist Ω)
    (h_int : (interior (convexHull ℝ (Set.range m))).Nonempty) :
    MomentSetup Ω n where
  m := m
  m_continuous := m_continuous
  X := convexHull ℝ (Set.range m)
  X_compact := isCompact_convexHull_of_isCompact (isCompact_range m_continuous)
  X_convex := convex_convexHull ℝ _
  X_interior := h_int
  m_mem_X := fun ω => subset_convexHull ℝ _ (Set.mem_range_self ω)
  moment_surjOn_X := fun _ hy => exists_probDist_integral_eq m_continuous hy
  prior := prior

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
