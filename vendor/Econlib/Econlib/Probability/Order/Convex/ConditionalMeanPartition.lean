/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.OrderedCutoffPartition
public import Econlib.Probability.ContDist.Conditioning
public import Econlib.Probability.ContDist.ProbDist
public import Econlib.Probability.Order.Convex.Basic
public import Econlib.Probability.ProbDist.Support

/-!
# Conditional-mean partition laws

Given a continuous distribution `d : ContDist` and an ordered cutoff partition
`P : OrderedCutoffPartition K a b`, we build a discrete **partition law** supported at the
conditional means of each cell. This generalizes the three-rating Bayes-plausibility argument to
arbitrary `K` and an arbitrary nondegenerate compact interval `[a, b]`.

## Main definitions

* `cellMass d P j`  — probability mass of cell `j` under `d`.
* `cellMean d P j`  — conditional mean of `id` on cell `j`.
* `conditionalMeanWeights d P hpos` — `FinDist (Fin K)` of normalized cell masses.
* `conditionalMeanPartitionLaw d P hpos` — mixture of Diracs at cell means.

## Main statements

* `sum_integral_cellClosed` — cellwise set integrals telescope to the full-interval integral.
* `conditionalMeanPartitionLaw_convexOrderOnIcc` — the partition law is below `d` in the convex
  order on `[a, b]` (Bayes plausibility).

## Tags

conditional mean, partition law, convex order, bayes plausibility, mean-preserving spread
-/

@[expose] public noncomputable section

open MeasureTheory Set BigOperators

namespace Econlib.Probability

variable {K : ℕ} {a b : ℝ}

/-! ## Cell mass and mean -/

/-- Probability mass of cell `j`: `∫_{cellClosed j} d.density`. -/
noncomputable def cellMass (d : ContDist) (P : OrderedCutoffPartition K a b) (j : Fin K) : ℝ :=
  ∫ x in P.cellClosed j, d.density x

/-- Conditional mean of `id` on cell `j`: `E[id | X ∈ cellClosed j]`. Defined for every cell,
including zero-mass ones, so it uses the totalized `conditionalExpectOrZero`; on cells with
positive mass it is the conditional mean. -/
noncomputable def cellMean (d : ContDist) (P : OrderedCutoffPartition K a b) (j : Fin K) : ℝ :=
  d.conditionalExpectOrZero id (P.cellClosed j)

/-! ## Weights and partition law -/

/-- Normalized cell masses as a `FinDist (Fin K)`. Requires all cells to have positive mass. -/
noncomputable def conditionalMeanWeights (d : ContDist) (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j) : FinDist (Fin K) where
  pmf j := cellMass d P j / ∑ k : Fin K, cellMass d P k
  nonneg j := by
    apply div_nonneg (le_of_lt (hpos j))
    exact Finset.sum_nonneg fun k _ => le_of_lt (hpos k)
  sum_one := by
    -- When K = 0, derive contradiction from P (cutoff 0 must be both a and b, against a < b)
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · subst hK0
      have heq : (⟨0, Nat.lt_succ_self 0⟩ : Fin 1) = (0 : Fin 1) := rfl
      have hr := P.right_eq
      rw [heq, P.left_eq] at hr
      exact absurd hr P.lt.ne
    · -- K > 0: standard normalization argument
      haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
      have hne : (Finset.univ : Finset (Fin K)).Nonempty := Finset.univ_nonempty
      have hS_pos : 0 < ∑ k : Fin K, cellMass d P k :=
        Finset.sum_pos (fun k _ => hpos k) hne
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hS_pos)

/-- Partition law: Mixture of Diracs at each cell's conditional mean. -/
noncomputable def conditionalMeanPartitionLaw (d : ContDist) (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j) : ProbDist ℝ :=
  ProbDist.finMixture (conditionalMeanWeights d P hpos)
    (fun j => ProbDist.dirac (cellMean d P j))

/-! ## Lemmas about cell mass -/

/-- Cell mass is nonnegative. -/
lemma cellMass_nonneg (d : ContDist) (P : OrderedCutoffPartition K a b) (j : Fin K) :
    0 ≤ cellMass d P j :=
  setIntegral_nonneg measurableSet_Icc (fun x _ => d.nonneg x)

/-- Cell mass is positive when the density is positive on the interior of `[a,b]` and the partition
is η-spaced with η > 0. -/
lemma cellMass_pos_of_density_pos (d : ContDist) (P : OrderedCutoffPartition K a b) (j : Fin K)
    {η : ℝ}
    (hd_pos : ∀ x ∈ Ioo a b, 0 < d.density x)
    (_hd_cont : ContinuousOn d.density (Icc a b))
    (hη : P.EtaSpaced η) (hηpos : 0 < η) :
    0 < cellMass d P j := by
  unfold cellMass OrderedCutoffPartition.cellClosed
  set L := P.leftEndpoint j
  set R := P.rightEndpoint j
  have hLR : L < R := P.cell_width_pos_of_eta hη hηpos j
  have hL_le : a ≤ L := P.le_leftEndpoint j
  have hR_le : R ≤ b := P.rightEndpoint_le j
  -- d.density is nonneg a.e. on Icc L R
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Icc L R)] d.density :=
    ae_of_all _ (fun x => d.nonneg x)
  -- The support of d.density (intersected with Icc L R) contains Ioo L R
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn_ae d.integrable.integrableOn]
  -- Need: 0 < volume (Function.support d.density ∩ Icc L R)
  have hIoo_sub : Ioo L R ⊆ Function.support d.density ∩ Icc L R := by
    intro x hx
    have hxab : x ∈ Ioo a b := by
      refine ⟨?_, ?_⟩
      · exact lt_of_le_of_lt hL_le hx.1
      · exact lt_of_lt_of_le hx.2 hR_le
    refine ⟨?_, Ioo_subset_Icc_self hx⟩
    exact Function.mem_support.mpr (ne_of_gt (hd_pos x hxab))
  have hIoo_pos : 0 < volume (Ioo L R) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hLR)
  exact lt_of_lt_of_le hIoo_pos (measure_mono hIoo_sub)

/-! ## Cell mean lies in its cell -/

/-- The conditional mean of `id` on cell `j` lies in `cellClosed j`. -/
lemma cellMean_mem_cell (d : ContDist) (P : OrderedCutoffPartition K a b) (j : Fin K)
    (hpos : 0 < cellMass d P j)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    cellMean d P j ∈ P.cellClosed j := by
  unfold cellMean cellMass at *
  -- On a positive-mass cell the totalized value is the conditional mean, which lies in
  -- the cell by `conditionalExpect_id_mem_Icc`.
  rw [show d.conditionalExpectOrZero id (P.cellClosed j) =
      d.conditionalExpect id (P.cellClosed j) hpos from rfl]
  apply ContDist.conditionalExpect_id_mem_Icc
  · exact (hd_cont.mono (P.cellClosed_subset_Icc j) |>.mul
        continuousOn_id).integrableOn_compact isCompact_Icc
  · exact P.leftEndpoint_le_rightEndpoint j

/-! ## Support of the partition law -/

/-- The partition law is supported on `[a, b]`: Each cell mean lies in its cell, hence in
`[a, b]`. -/
lemma conditionalMeanPartitionLaw_supportsOn (d : ContDist) (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    (conditionalMeanPartitionLaw d P hpos).supportsOn (Icc a b) := by
  apply ProbDist.supportsOn_finMixture _ _ measurableSet_Icc
  intro j
  apply ProbDist.supportsOn_dirac measurableSet_Icc
  exact P.cellClosed_subset_Icc j (cellMean_mem_cell d P j (hpos j) hd_cont)

/-! ## Telescoping cellwise integrals -/

/-- **Cellwise integrals telescope.** Summing `∫_{cellClosed j} g` over the cells of the partition
recovers `∫_{[a,b]} g`, for any `g` integrable on each closed cell. Adjacent closed cells overlap
in a single cutpoint, which is Lebesgue-null. -/
lemma sum_integral_cellClosed (P : OrderedCutoffPartition K a b) (g : ℝ → ℝ)
    (hg : ∀ j : Fin K, IntegrableOn g (P.cellClosed j) volume) :
    ∑ j : Fin K, ∫ x in P.cellClosed j, g x = ∫ x in Icc a b, g x := by
  -- Bring cellClosed j = Icc (cutoff j.castSucc) (cutoff j.succ) to interval-integral form.
  have hcell_int : ∀ j : Fin K,
      ∫ x in P.cellClosed j, g x = ∫ x in P.cutoff j.castSucc..P.cutoff j.succ, g x := by
    intro j
    unfold OrderedCutoffPartition.cellClosed OrderedCutoffPartition.leftEndpoint
      OrderedCutoffPartition.rightEndpoint
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (P.cutoff_le_succ j)]
  rw [Finset.sum_congr rfl (fun j _ => hcell_int j)]
  -- Define a ℕ → ℝ extension of cutoff for sum_integral_adjacent_intervals.
  set cseq : ℕ → ℝ := fun k => if h : k ≤ K then P.cutoff ⟨k, Nat.lt_succ_of_le h⟩ else b
    with hcseq_def
  have hcseq_eq : ∀ (k : ℕ) (h : k ≤ K), cseq k = P.cutoff ⟨k, Nat.lt_succ_of_le h⟩ := by
    intro k h; simp [cseq, h]
  have hcseq_zero : cseq 0 = a := by
    have h0 : (⟨0, Nat.zero_lt_succ K⟩ : Fin (K+1)) = 0 := rfl
    rw [hcseq_eq 0 (Nat.zero_le _), h0, P.left_eq]
  have hcseq_K : cseq K = b := by
    rw [hcseq_eq K le_rfl]
    convert P.right_eq
  -- Sum over Fin K equals sum over Finset.range K of the lifted integrals.
  have hsum_eq : ∑ j : Fin K, ∫ x in P.cutoff j.castSucc..P.cutoff j.succ, g x =
      ∑ k ∈ Finset.range K, ∫ x in cseq k..cseq (k+1), g x := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => ∫ x in cseq k..cseq (k+1), g x) K]
    apply Finset.sum_congr rfl
    intro j _
    have hjK' : (j : ℕ) ≤ K := j.isLt.le
    have hj1K : (j : ℕ) + 1 ≤ K := j.isLt
    have h1 : cseq (j : ℕ) = P.cutoff j.castSucc := by
      rw [hcseq_eq (j : ℕ) hjK']
      rfl
    have h2 : cseq ((j : ℕ) + 1) = P.cutoff j.succ := by
      rw [hcseq_eq ((j : ℕ) + 1) hj1K]
      rfl
    rw [h1, h2]
  rw [hsum_eq]
  -- Apply sum_integral_adjacent_intervals; per-piece integrability comes from `hg`.
  have hint_adj : ∀ k, k < K →
      IntervalIntegrable g volume (cseq k) (cseq (k+1)) := by
    intro k hk
    have hk1 : k + 1 ≤ K := hk
    have hkK : k ≤ K := le_of_lt hk
    rw [hcseq_eq k hkK, hcseq_eq (k+1) hk1]
    have hLR : P.cutoff ⟨k, Nat.lt_succ_of_le hkK⟩ ≤ P.cutoff ⟨k+1, Nat.lt_succ_of_le hk1⟩ :=
      P.monotone (by simp [Fin.le_iff_val_le_val])
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hLR]
    exact (hg ⟨k, hk⟩).mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := cseq) (n := K) hint_adj]
  -- Now we have ∫ x in cseq 0 .. cseq K, g x. Substitute boundary values.
  rw [hcseq_zero, hcseq_K]
  -- Convert ∫ x in a..b to ∫ x in Icc a b.
  rw [intervalIntegral.integral_of_le P.lt.le, ← integral_Icc_eq_integral_Ioc]

/-! ## Expectation identities -/

/-- The weighted sum of conditional expectations equals the total expectation:
`∑ j, cellMass j * E[φ | cell j] = E[φ]`. -/
lemma weighted_conditionalExpect_eq_expect (d : ContDist) (P : OrderedCutoffPartition K a b)
    (φ : ℝ → ℝ)
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hd_support : d.toProbDist.supportsOn (Icc a b)) :
    ∑ j : Fin K, cellMass d P j * d.conditionalExpectOrZero φ (P.cellClosed j) =
      d.toProbDist.expect φ := by
  -- Each summand equals ∫_{cellClosed j} density * φ.
  have per_cell : ∀ j : Fin K,
      cellMass d P j * d.conditionalExpectOrZero φ (P.cellClosed j) =
        ∫ x in P.cellClosed j, d.density x * φ x := by
    intro j
    unfold cellMass
    by_cases hpos : 0 < ∫ x in P.cellClosed j, d.density x
    · rw [ContDist.conditionalExpectOrZero_eq_of_pos _ _ _ hpos]
      field_simp
    · -- cellMass = 0, so density = 0 a.e. on cell, so ∫ density·φ = 0.
      have hnn : 0 ≤ ∫ x in P.cellClosed j, d.density x :=
        cellMass_nonneg d P j
      have hzero : ∫ x in P.cellClosed j, d.density x = 0 := le_antisymm (not_lt.mp hpos) hnn
      rw [ContDist.conditionalExpectOrZero_zero _ _ _ hpos, mul_zero]
      -- density = 0 a.e. on cellClosed j
      have hae : d.density =ᵐ[volume.restrict (P.cellClosed j)] 0 := by
        rw [← MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
            (ae_of_all _ (fun x => d.nonneg x))
            d.integrable.integrableOn]
        exact hzero
      have hzeroφ : (fun x => d.density x * φ x) =ᵐ[volume.restrict (P.cellClosed j)] 0 := by
        filter_upwards [hae] with x hx
        simp [hx]
      exact (MeasureTheory.integral_eq_zero_of_ae hzeroφ).symm
  -- Rewrite the sum and telescope the cellwise integrals.
  rw [Finset.sum_congr rfl (fun j _ => per_cell j)]
  rw [sum_integral_cellClosed P (fun x => d.density x * φ x) (fun j =>
    ((hd_cont.mono (P.cellClosed_subset_Icc j)).mul
      (hφ_cont.mono (P.cellClosed_subset_Icc j))).integrableOn_compact isCompact_Icc)]
  -- Now LHS = ∫ x in Icc a b, density x * φ x; convert RHS to use d.toMeasure:
  -- d.toProbDist.expect φ = ∫ φ ∂d.toMeasure = ∫_{Icc a b} φ ∂d.toMeasure
  --                       = ∫_{Icc a b} density · φ ∂volume.
  have hae_mem : ∀ᵐ x ∂d.toMeasure, x ∈ Icc a b :=
    d.toProbDist.ae_mem_of_supportsOn measurableSet_Icc hd_support
  change ∫ t in Icc a b, d.density t * φ t = ∫ x, φ x ∂d.toMeasure
  rw [MeasureTheory.integral_eq_setIntegral hae_mem,
    d.setIntegral_toMeasure_eq φ measurableSet_Icc]

/-- The total cell mass is `1`: Summing each cell's mass recovers the probability of `[a,b]`, which
is `1` since `d` is supported there. Direct telescoping (`sum_integral_cellClosed`) — neither
positivity of the cell masses nor continuity of the density is needed. -/
lemma cellMass_sum_eq_one (d : ContDist) (P : OrderedCutoffPartition K a b)
    (hd_support : d.toProbDist.supportsOn (Icc a b)) :
    ∑ k : Fin K, cellMass d P k = 1 := by
  have htel : ∑ k : Fin K, cellMass d P k = ∫ x in Icc a b, d.density x :=
    sum_integral_cellClosed P d.density (fun j => d.integrable.integrableOn)
  -- The full-interval mass is 1 by the support hypothesis.
  have hmass_measure : d.toMeasure (Icc a b) = 1 := by
    have hsupp := hd_support
    unfold ProbDist.supportsOn at hsupp
    rwa [ContDist.toProbDist_toMeasure] at hsupp
  have hmass : ∫ x in Icc a b, d.density x = 1 := by
    calc
      ∫ x in Icc a b, d.density x = ∫ x in Icc a b, (1 : ℝ) ∂d.toMeasure := by
        symm
        simpa [one_mul] using d.setIntegral_toMeasure_eq (fun _ => (1 : ℝ)) measurableSet_Icc
      _ = (d.toMeasure (Icc a b)).toReal := by
        simp [MeasureTheory.Measure.real_def]
      _ = 1 := by rw [hmass_measure]; norm_num
  rw [htel, hmass]

/-- Expectation under the partition law equals the weighted sum of cell means under `φ`. -/
lemma conditionalMeanPartitionLaw_expect_eq_weighted (d : ContDist)
    (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j)
    (φ : ℝ → ℝ) :
    (conditionalMeanPartitionLaw d P hpos).expect φ =
      ∑ j : Fin K, (conditionalMeanWeights d P hpos).pmf j * φ (cellMean d P j) := by
  unfold conditionalMeanPartitionLaw
  rw [ProbDist.expect_finMixture]
  · simp [ProbDist.expect_dirac]
  · -- Integrability w.r.t. a Dirac measure: ∫ φ d(δ_x) = φ(x), always integrable
    intro j; exact MeasureTheory.integrable_dirac (by simp)

/-- The partition law preserves the mean. -/
lemma conditionalMeanPartitionLaw_expect_id_eq_prior (d : ContDist)
    (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hd_support : d.toProbDist.supportsOn (Icc a b)) :
    (conditionalMeanPartitionLaw d P hpos).expect id = d.toProbDist.expect id := by
  -- Total mass equals 1: ∑ j, cellMass j = 1.
  haveI := d.toMeasure_isProbability
  have htotal : ∑ k : Fin K, cellMass d P k = 1 :=
    cellMass_sum_eq_one d P hd_support
  -- Expand LHS via `expect_eq_weighted` and reduce to weighted_conditionalExpect_eq_expect.
  rw [conditionalMeanPartitionLaw_expect_eq_weighted d P hpos id]
  unfold conditionalMeanWeights cellMean
  simp only [htotal, div_one]
  -- Goal: ∑ j, cellMass j * id (conditionalExpectOrZero id (cell j)) = d.toProbDist.expect id.
  change ∑ j : Fin K, cellMass d P j * d.conditionalExpectOrZero id (P.cellClosed j) =
      d.toProbDist.expect id
  exact weighted_conditionalExpect_eq_expect d P id continuousOn_id hd_cont hd_support

/-! ## Bayes plausibility (convex order) -/

/-- Jensen step: The partition law assigns weakly smaller expectation than `d` to every convex
function on `[a,b]`. -/
lemma conditionalMeanPartitionLaw_convex_expect_le_prior (d : ContDist)
    (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hd_support : d.toProbDist.supportsOn (Icc a b))
    {φ : ℝ → ℝ}
    (hφ_conv : ConvexOn ℝ (Icc a b) φ)
    (hφ_cont : ContinuousOn φ (Icc a b)) :
    (conditionalMeanPartitionLaw d P hpos).expect φ ≤ d.toProbDist.expect φ := by
  haveI := d.toMeasure_isProbability
  -- Total mass = 1 (same argument as in expect_id_eq_prior).
  have htotal : ∑ k : Fin K, cellMass d P k = 1 :=
    cellMass_sum_eq_one d P hd_support
  -- LHS expanded using `expect_eq_weighted`, weights simplify to cellMass via htotal.
  rw [conditionalMeanPartitionLaw_expect_eq_weighted d P hpos φ]
  unfold conditionalMeanWeights
  simp only [htotal, div_one]
  -- Goal: ∑ j, cellMass j * φ (cellMean j) ≤ d.toProbDist.expect φ
  -- RHS = ∑ j, cellMass j * conditionalExpect φ (cell j) by the weighted identity.
  rw [← weighted_conditionalExpect_eq_expect d P φ hφ_cont hd_cont hd_support]
  -- Reduce to per-cell Jensen: φ(cellMean j) ≤ conditionalExpect φ (cell j),
  -- then multiply by positive cellMass j and sum.
  apply Finset.sum_le_sum
  intro j _
  have hmj_pos : 0 < cellMass d P j := hpos j
  have hmj_nn : 0 ≤ cellMass d P j := le_of_lt hmj_pos
  -- d.toMeasure-real of cellClosed j = cellMass j.
  have hμreal :
      d.toMeasure.real (P.cellClosed j) = cellMass d P j := by
    have h1 :
        ∫ x in P.cellClosed j, (1 : ℝ) ∂d.toMeasure = d.toMeasure.real (P.cellClosed j) :=
      MeasureTheory.setIntegral_one_eq_measureReal
    have h2 :
        ∫ x in P.cellClosed j, (1 : ℝ) ∂d.toMeasure =
          ∫ x in P.cellClosed j, d.density x * 1 :=
      d.setIntegral_toMeasure_eq (fun _ => 1) measurableSet_Icc
    have h3 : ∫ x in P.cellClosed j, d.density x * 1 = cellMass d P j := by
      simp [cellMass]
    linarith [h1, h2, h3]
  have hμne_zero : d.toMeasure (P.cellClosed j) ≠ 0 := by
    intro h
    have : d.toMeasure.real (P.cellClosed j) = 0 := by
      rw [MeasureTheory.measureReal_def, h, ENNReal.toReal_zero]
    rw [hμreal] at this
    linarith [hmj_pos]
  have hμne_top := MeasureTheory.measure_ne_top d.toMeasure (P.cellClosed j)
  -- The cell is contained in Icc a b (the convex set s for Jensen).
  have hsub : P.cellClosed j ⊆ Icc a b := P.cellClosed_subset_Icc j
  -- a.e. f x = x in cellClosed j ⇒ x ∈ Icc a b.
  have hfs : ∀ᵐ x ∂(d.toMeasure.restrict (P.cellClosed j)), id x ∈ Icc a b := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro x hx
    exact hsub hx
  -- f = id is integrable on cellClosed j w.r.t. d.toMeasure.
  -- IntegrableOn f t μ ↔ Integrable f (μ.restrict t).
  have hcell_meas : MeasurableSet (P.cellClosed j) := measurableSet_Icc
  have hd_cont_cell : ContinuousOn d.density (P.cellClosed j) :=
    hd_cont.mono hsub
  have hφ_cont_cell : ContinuousOn φ (P.cellClosed j) :=
    hφ_cont.mono hsub
  have hcompact : IsCompact (P.cellClosed j) := isCompact_Icc
  -- Both density·id and density·φ are continuous on the compact cell, so integrable.
  have hd_id_int : IntegrableOn (fun x => d.density x * id x) (P.cellClosed j) :=
    (hd_cont_cell.mul continuousOn_id).integrableOn_compact hcompact
  have hd_φ_int : IntegrableOn (fun x => d.density x * φ x) (P.cellClosed j) :=
    (hd_cont_cell.mul hφ_cont_cell).integrableOn_compact hcompact
  -- Convert to integrability w.r.t. d.toMeasure.
  have hfi : MeasureTheory.IntegrableOn id (P.cellClosed j) d.toMeasure := by
    change MeasureTheory.Integrable id (d.toMeasure.restrict (P.cellClosed j))
    rw [d.toMeasure_eq, MeasureTheory.restrict_withDensity hcell_meas]
    rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
      (d.integrable.aemeasurable.ennreal_ofReal.restrict)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine hd_id_int.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x)]
  have hgi : MeasureTheory.IntegrableOn (φ ∘ id) (P.cellClosed j) d.toMeasure := by
    change MeasureTheory.Integrable (φ ∘ id) (d.toMeasure.restrict (P.cellClosed j))
    rw [d.toMeasure_eq, MeasureTheory.restrict_withDensity hcell_meas]
    rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀'
      (d.integrable.aemeasurable.ennreal_ofReal.restrict)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine hd_φ_int.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x)]
  -- Apply Jensen on the cell with the d.toMeasure-restricted measure.
  have hjensen :
      φ (⨍ x in P.cellClosed j, id x ∂d.toMeasure) ≤
        ⨍ x in P.cellClosed j, φ (id x) ∂d.toMeasure :=
    hφ_conv.map_set_average_le hφ_cont isClosed_Icc hμne_zero hμne_top hfs hfi hgi
  -- Compute the averages.
  have hsetint_id : ∫ x in P.cellClosed j, id x ∂d.toMeasure =
      ∫ x in P.cellClosed j, d.density x * id x :=
    d.setIntegral_toMeasure_eq id hcell_meas
  have hsetint_φ : ∫ x in P.cellClosed j, φ x ∂d.toMeasure =
      ∫ x in P.cellClosed j, d.density x * φ x :=
    d.setIntegral_toMeasure_eq φ hcell_meas
  have havg_id :
      ⨍ x in P.cellClosed j, id x ∂d.toMeasure = cellMean d P j := by
    rw [MeasureTheory.setAverage_eq, hμreal, hsetint_id]
    -- Goal: (cellMass j)⁻¹ • ∫ x in cell, density x * id x = cellMean j
    change (cellMass d P j)⁻¹ * (∫ x in P.cellClosed j, d.density x * id x) =
      cellMean d P j
    unfold cellMean
    rw [ContDist.conditionalExpectOrZero_eq_of_pos _ _ _ (hpos j)]
    unfold cellMass
    rw [div_eq_inv_mul]
  have havg_φ :
      ⨍ x in P.cellClosed j, φ (id x) ∂d.toMeasure =
        d.conditionalExpectOrZero φ (P.cellClosed j) := by
    rw [show (⨍ x in P.cellClosed j, φ (id x) ∂d.toMeasure) =
        ⨍ x in P.cellClosed j, φ x ∂d.toMeasure from rfl]
    rw [MeasureTheory.setAverage_eq, hμreal, hsetint_φ]
    change (cellMass d P j)⁻¹ * (∫ x in P.cellClosed j, d.density x * φ x) =
      d.conditionalExpectOrZero φ (P.cellClosed j)
    rw [ContDist.conditionalExpectOrZero_eq_of_pos _ _ _ (hpos j)]
    unfold cellMass
    rw [div_eq_inv_mul]
  rw [havg_id, havg_φ] at hjensen
  -- Multiply by cellMass j ≥ 0.
  exact mul_le_mul_of_nonneg_left hjensen hmj_nn

/-- **Bayes plausibility**: The partition law is below `d` in the convex order on `[a,b]`.

`conditionalMeanPartitionLaw d P hpos ≼cx[a,b] d.toProbDist`

This is the key reusable theorem for rating-law feasibility. -/
theorem conditionalMeanPartitionLaw_convexOrderOnIcc (d : ContDist)
    (P : OrderedCutoffPartition K a b)
    (hpos : ∀ j, 0 < cellMass d P j)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (hd_support : d.toProbDist.supportsOn (Icc a b)) :
    ConvexOrderOnIcc a b
      (conditionalMeanPartitionLaw d P hpos)
      d.toProbDist := by
  refine ⟨conditionalMeanPartitionLaw_supportsOn d P hpos hd_cont, hd_support, ?_, ?_⟩
  · exact conditionalMeanPartitionLaw_expect_id_eq_prior d P hpos hd_cont hd_support
  · intro φ hφ_conv hφ_cont
    exact conditionalMeanPartitionLaw_convex_expect_le_prior d P hpos hd_cont hd_support
      hφ_conv hφ_cont

end Econlib.Probability

end
