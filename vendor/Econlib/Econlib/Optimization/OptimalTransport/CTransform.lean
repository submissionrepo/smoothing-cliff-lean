/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.Discretization
public import Econlib.Probability.ProbDist.Borel

/-!
# The finite `c`-transform on a set of atoms

The finite `c`-transform `cConjugate atom L pRaw i = inf_j (pRaw j + L · dist (atom i) (atom j))`
replaces an arbitrary finite affine price vector `pRaw` over a set of atoms by an `L`-Lipschitz
price that lies below it. This is the discrete counterpart of the `c`-transform from
optimal-transport duality: It converts a finite affine majorant of an objective into an
`L`-Lipschitz majorant, the form required to invoke Kantorovich–Rubinstein duality.

## Main definitions

* `cConjugate` — the finite `c`-transform of a raw price vector over the atoms.

## Main statements

* `cConjugate_le_raw` — the transform lies below the raw price at each atom.
* `cConjugate_lipschitz`, `cConjugate_abs_sub_le` — the transform is `L`-Lipschitz on the atoms.
* `finiteObjective_majorized_by_cConjugate` — replacing a raw affine majorant by its `c`-transform
  preserves finite majorization of a KR-Lipschitz objective.
* `atomize_coords_mem_stdSimplex`, `finiteLaw_atomize_eq`, `expect_atomize_bound` — supporting
  facts relating atomization coordinates, finite laws, and expectations.

## References

* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

c-transform, c-conjugate, lipschitz, optimal transport, kantorovich-rubinstein
-/

@[expose] public section

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {n : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The finite c-transform used to replace arbitrary finite affine prices by `L`-Lipschitz prices
on the selected atoms. -/
noncomputable def cConjugate [PseudoMetricSpace Ω]
    (atom : Fin n → Ω) (L : ℝ) (pRaw : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ : Finset (Fin n)).inf' ⟨i, Finset.mem_univ i⟩
    (fun j => pRaw j + L * dist (atom i) (atom j))

omit [MeasurableSpace Ω] in
/-- The c-transform lies below the raw price at each atom. -/
theorem cConjugate_le_raw [PseudoMetricSpace Ω]
    {atom : Fin n → Ω} {L : ℝ} {pRaw : Fin n → ℝ} (i : Fin n) :
    cConjugate atom L pRaw i ≤ pRaw i := by
  simpa [cConjugate] using
    Finset.inf'_le (f := fun j => pRaw j + L * dist (atom i) (atom j)) (Finset.mem_univ i)

omit [MeasurableSpace Ω] in
/-- The c-transform is `L`-Lipschitz on the finite atom set. -/
theorem cConjugate_lipschitz [PseudoMetricSpace Ω]
    {atom : Fin n → Ω} {L : ℝ} {pRaw : Fin n → ℝ}
    (hL_nonneg : 0 ≤ L) :
    ∀ i j : Fin n,
      cConjugate atom L pRaw i - cConjugate atom L pRaw j
        ≤ L * dist (atom i) (atom j) := by
  intro i j
  obtain ⟨k, _hk, hk_eq⟩ :=
    Finset.exists_mem_eq_inf' ⟨j, Finset.mem_univ j⟩
      (fun k => pRaw k + L * dist (atom j) (atom k))
  have hci_le : cConjugate atom L pRaw i ≤ pRaw k + L * dist (atom i) (atom k) :=
    Finset.inf'_le (f := fun k => pRaw k + L * dist (atom i) (atom k)) (Finset.mem_univ k)
  -- L scales the triangle inequality at the minimizing atom k for index j.
  have hmul :
      L * dist (atom i) (atom k) ≤
        L * dist (atom i) (atom j) + L * dist (atom j) (atom k) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (dist_triangle (atom i) (atom j) (atom k)) hL_nonneg
  have hcj_eq : cConjugate atom L pRaw j = pRaw k + L * dist (atom j) (atom k) := by
    simpa [cConjugate] using hk_eq
  linarith

omit [MeasurableSpace Ω] in
/-- Symmetric absolute-value form of the finite c-transform Lipschitz bound. -/
theorem cConjugate_abs_sub_le [PseudoMetricSpace Ω]
    {atom : Fin n → Ω} {L : ℝ} {pRaw : Fin n → ℝ}
    (hL_nonneg : 0 ≤ L) (i j : Fin n) :
    |cConjugate atom L pRaw i - cConjugate atom L pRaw j|
      ≤ L * dist (atom i) (atom j) := by
  rw [abs_sub_le_iff]
  constructor
  · exact cConjugate_lipschitz hL_nonneg i j
  · simpa [dist_comm] using cConjugate_lipschitz hL_nonneg j i

/-- Replacing a raw affine majorant by its c-transform preserves finite majorization when the
pulled-back objective is KR-Lipschitz. -/
theorem finiteObjective_majorized_by_cConjugate
    [PseudoMetricSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
    [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω] [CompactSpace Ω]
    {V : ProbabilityMeasure Ω → ℝ} {atom : Fin n → Ω} {L c : ℝ} {pRaw : Fin n → ℝ}
    (hL_nonneg : 0 ≤ L)
    (hV_lip : IsKRLipschitz V L)
    (hraw : ∀ lam ∈ stdSimplex ℝ (Fin n),
      finiteObjective V atom lam ≤ ∑ i, pRaw i * lam i + c) :
    ∀ lam ∈ stdSimplex ℝ (Fin n),
      finiteObjective V atom lam ≤ ∑ i, cConjugate atom L pRaw i * lam i + c := by
  classical
  have hmin_exists : ∀ i : Fin n,
      ∃ j : Fin n, cConjugate atom L pRaw i =
        pRaw j + L * dist (atom i) (atom j) := by
    intro i
    obtain ⟨j, _hj, hj_eq⟩ :=
      Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Fin n)))
        ⟨i, Finset.mem_univ i⟩
        (fun j => pRaw j + L * dist (atom i) (atom j))
    exact ⟨j, by simpa [cConjugate] using hj_eq⟩
  let κ : Fin n → Fin n := fun i => Classical.choose (hmin_exists i)
  have hκ_eq : ∀ i : Fin n,
      cConjugate atom L pRaw i =
        pRaw (κ i) + L * dist (atom i) (atom (κ i)) := by
    intro i
    exact Classical.choose_spec (hmin_exists i)
  intro lam hlam
  let lamS : stdSimplex ℝ (Fin n) := ⟨lam, hlam⟩
  let lamP : stdSimplex ℝ (Fin n) := simplexPush lamS κ
  have hrawP :
      V (finiteLaw atom lamP) ≤ ∑ i, pRaw i * lamP i + c := by
    have h := hraw lamP lamP.property
    have hobjP : finiteObjective V atom lamP = V (finiteLaw atom lamP) :=
      finiteObjective_of_mem lamP.property
    rwa [hobjP] at h
  have hcost :
      krDist (finiteLaw atom lamS) (finiteLaw atom lamP)
        ≤ ∑ i, lamS i * dist (atom i) (atom (κ i)) :=
    finiteLaw_krDist_push_le atom lamS κ
  have hlip_cost :
      V (finiteLaw atom lamS) - V (finiteLaw atom lamP)
        ≤ L * (∑ i, lamS i * dist (atom i) (atom (κ i))) :=
    le_trans (hV_lip (finiteLaw atom lamS) (finiteLaw atom lamP))
      (mul_le_mul_of_nonneg_left hcost hL_nonneg)
  have hprice :
      ∑ i, pRaw i * lamP i = ∑ i, lamS i * pRaw (κ i) :=
    simplexPush_price_sum lamS κ pRaw
  have hconj_sum :
      ∑ i, cConjugate atom L pRaw i * lamS i =
        (∑ i, lamS i * pRaw (κ i)) +
          L * (∑ i, lamS i * dist (atom i) (atom (κ i))) := by
    calc
      ∑ i, cConjugate atom L pRaw i * lamS i
          = ∑ i, (pRaw (κ i) + L * dist (atom i) (atom (κ i))) * lamS i := by
            refine Finset.sum_congr rfl fun i _hi => ?_
            rw [hκ_eq i]
      _ = (∑ i, lamS i * pRaw (κ i)) +
            L * (∑ i, lamS i * dist (atom i) (atom (κ i))) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _hi => by ring
  have htotal :
      (∑ i, pRaw i * lamP i + c) +
          L * (∑ i, lamS i * dist (atom i) (atom (κ i)))
        = ∑ i, cConjugate atom L pRaw i * lamS i + c := by
    rw [hprice, hconj_sum]
    ring
  calc
    finiteObjective V atom lam = V (finiteLaw atom lamS) := finiteObjective_of_mem hlam
    _ ≤ V (finiteLaw atom lamP) +
          L * (∑ i, lamS i * dist (atom i) (atom (κ i))) := by
        linarith
    _ ≤ (∑ i, pRaw i * lamP i + c) +
          L * (∑ i, lamS i * dist (atom i) (atom (κ i))) := by
        linarith
    _ = ∑ i, cConjugate atom L pRaw i * lam i + c := by
        simpa [lamS] using htotal

/-- The pre-image partition coordinates of any law `μ` under the selector `Vsel` lie in the
standard simplex.  This is the basic fact that pre-image measures under `Subtype.val ∘ Vsel` form a
probability vector indexed by `Fin S.card`. -/
lemma atomize_coords_mem_stdSimplex
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω]
    (μ : ProbabilityMeasure Ω) {S : Finset Ω}
    (Vsel : Ω → S) (hVsel_meas : Measurable Vsel) :
    (fun i : Fin S.card =>
        (μ.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹'
          {(((S.equivFin.symm i : ↥S) : Ω))})).toReal) ∈
      stdSimplex ℝ (Fin S.card) := by
  classical
  set atom : Fin S.card → Ω := fun i => ((S.equivFin.symm i : ↥S) : Ω) with hatom_def
  have hatom_inj : Function.Injective atom :=
    Subtype.coe_injective.comp S.equivFin.symm.injective
  have hVsel_val_meas : Measurable (fun x : Ω => (Vsel x : Ω)) :=
    hVsel_meas.subtype_val
  refine ⟨fun i => ENNReal.toReal_nonneg, ?_⟩
  -- Sum equals 1 since the preimages partition Ω.
  have hpre_partition :
      (Set.univ : Set Ω) = ⋃ i : Fin S.card,
        (fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)} := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
    refine ⟨S.equivFin (Vsel x), ?_⟩
    simp [hatom_def]
  have hpre_disjoint : Pairwise (Function.onFun Disjoint
      (fun i : Fin S.card =>
        (fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    apply hij
    apply hatom_inj
    rw [← h1, ← h2]
  have hpre_meas : ∀ i : Fin S.card,
      MeasurableSet ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)}) :=
    fun i => hVsel_val_meas (MeasurableSet.singleton _)
  have hsum_eq :
      ∑ i : Fin S.card, μ.toMeasure
        ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})
        = μ.toMeasure Set.univ := by
    rw [hpre_partition, MeasureTheory.measure_iUnion hpre_disjoint hpre_meas, tsum_fintype]
  have hsum_real :
      ∑ i : Fin S.card, (μ.toMeasure
        ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})).toReal =
        (μ.toMeasure Set.univ).toReal := by
    rw [← hsum_eq, ENNReal.toReal_sum]
    intro i _
    exact (measure_lt_top μ.toMeasure _).ne
  rw [hsum_real, MeasureTheory.measure_univ]
  exact ENNReal.toReal_one

/-- Bridge: The atomized law equals the finite-law embedding of its singleton coordinates.  This is
the core measure-theoretic identification underlying the discretization argument. -/
lemma finiteLaw_atomize_eq
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    (μ₀ : ProbabilityMeasure Ω) {S : Finset Ω}
    (Vsel : Ω → S) (hVsel_meas : Measurable Vsel)
    (μ₀_coords : Fin S.card → ℝ)
    (h_simplex : μ₀_coords ∈ stdSimplex ℝ (Fin S.card))
    (h_coord_eq : ∀ i : Fin S.card,
      μ₀_coords i =
        (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹'
          {((S.equivFin.symm i : ↥S) : Ω)})).toReal) :
    finiteLaw (fun i : Fin S.card => ((S.equivFin.symm i : ↥S) : Ω))
        ⟨μ₀_coords, h_simplex⟩ =
      atomize μ₀ Vsel hVsel_meas := by
  classical
  set atom : Fin S.card → Ω := fun i => ((S.equivFin.symm i : ↥S) : Ω)
  -- Measurability of (Vsel x : Ω).
  have hVsel_val_meas : Measurable (fun x : Ω => (Vsel x : Ω)) :=
    hVsel_meas.subtype_val
  -- The atomization is a sum of Diracs at points of S.
  have hae : ∀ᵐ x ∂μ₀.toMeasure, (Vsel x : Ω) ∈ S := by
    refine Filter.Eventually.of_forall ?_
    intro x; exact (Vsel x).property
  have hμ₀_δ_eq :
      (atomize μ₀ Vsel hVsel_meas).toMeasure =
        ∑ a ∈ S, μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {a}) •
          MeasureTheory.Measure.dirac a := by
    change (map μ₀ (fun x => (Vsel x : Ω)) hVsel_val_meas).toMeasure = _
    rw [map_toMeasure]
    exact (MeasureTheory.Measure.ae_mem_finset_iff_map_eq_sum_dirac
        hVsel_val_meas.aemeasurable).mp hae
  -- Compare both measures via integrals against bounded continuous functions.
  apply ProbabilityMeasure.toMeasure_injective
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure ?_
  intro f
  -- LHS: ∫ f dfiniteLaw = ∑ μ₀_coords_i * f(atom i).
  have hLHS :
      ∫ x, f x ∂(finiteLaw atom ⟨μ₀_coords, h_simplex⟩).toMeasure =
        ∑ i, μ₀_coords i * f (atom i) := by
    change expect (finiteLaw atom ⟨μ₀_coords, h_simplex⟩) f =
        ∑ i, μ₀_coords i * f (atom i)
    exact finiteLaw_expect_boundedContinuous atom ⟨μ₀_coords, h_simplex⟩ f
  -- RHS: ∫ f dμ₀_δ = ∑_{a ∈ S} (μ₀.toMeasure (Vsel ⁻¹ {a})).toReal * f a.
  -- Each summand measure `c • Dirac a` is finite (c is finite, Dirac is finite).
  have hsmul_finite : ∀ a ∈ S,
      MeasureTheory.IsFiniteMeasure
        (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {a}) •
          MeasureTheory.Measure.dirac a) := by
    intro a _
    refine MeasureTheory.Measure.smul_finite _ ?_
    exact (measure_lt_top μ₀.toMeasure _).ne
  have hRHS :
      ∫ x, f x ∂(atomize μ₀ Vsel hVsel_meas).toMeasure =
        ∑ a ∈ S, (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {a})).toReal * f a := by
    rw [hμ₀_δ_eq]
    rw [MeasureTheory.integral_finset_sum_measure (fun a ha =>
      letI := hsmul_finite a ha
      f.integrable _)]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac, smul_eq_mul]
  rw [hLHS, hRHS]
  -- Reindex the sum over `S` to a sum over `Fin S.card` via `atom = Subtype.val ∘ S.equivFin.symm`.
  rw [← Finset.sum_attach S (f := fun a =>
      (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {a})).toReal * f a),
    ← Finset.sum_equiv S.equivFin.symm
        (s := (Finset.univ : Finset (Fin S.card)))
        (t := S.attach)
        (g := fun (a : ↥S) =>
          (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(a : Ω)})).toReal * f (a : Ω))
        (by intro i; simp [Finset.mem_attach])
        (by intro i _; rfl)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [h_coord_eq i]

/-- The expectation of an integrable function shifted by a constant shifts by that constant. -/
lemma expect_add_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f μ.toMeasure) :
    expect μ (fun x => f x + c) = expect μ f + c := by
  unfold expect
  rw [MeasureTheory.integral_add hf (integrable_const _)]
  simp [MeasureTheory.probReal_univ]

/-- For an `L`-Lipschitz price `pTilde` and an atomization that moves each point by at most `δ`,
the expectation of `pTilde` under a law `μ` and under its atomization differ by at most `L * δ`. -/
lemma expect_atomize_bound
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    {S : Finset Ω} (Vsel : Ω → S) (hVsel_meas : Measurable Vsel)
    {pTilde : Ω → ℝ} {L δ : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hpTilde_lip : LipschitzWith L.toNNReal pTilde)
    (hVsel_dist_le : ∀ x : Ω, dist x (Vsel x : Ω) ≤ δ) :
    ∀ μ : ProbabilityMeasure Ω,
      |expect μ pTilde -
        expect (atomize μ Vsel hVsel_meas) pTilde| ≤ L * δ := by
  intro μ
  -- Use the atomize coupling and pointwise L-Lipschitz bound.
  set μ' : ProbabilityMeasure Ω := atomize μ Vsel hVsel_meas with hμ'_def
  set π : ProbabilityMeasure (Ω × Ω) := atomizeCoupling μ Vsel hVsel_meas with hπ_def
  have hπ_couple : π ∈ couplings μ μ' :=
    atomizeCoupling_isCoupling μ Vsel hVsel_meas
  have hpTilde_cont : Continuous pTilde := hpTilde_lip.continuous
  have hμ_eq : μ.toMeasure = MeasureTheory.Measure.map Prod.fst π.toMeasure := by
    rw [← hπ_couple.fst_marginal, map_toMeasure]
  have hν_eq : μ'.toMeasure = MeasureTheory.Measure.map Prod.snd π.toMeasure := by
    rw [← hπ_couple.snd_marginal, map_toMeasure]
  have hpfst_cont : Continuous (fun z : Ω × Ω => pTilde z.1) := hpTilde_cont.comp continuous_fst
  have hpsnd_cont : Continuous (fun z : Ω × Ω => pTilde z.2) := hpTilde_cont.comp continuous_snd
  let pfstBCF : BoundedContinuousFunction (Ω × Ω) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, hpfst_cont⟩
  let psndBCF : BoundedContinuousFunction (Ω × Ω) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, hpsnd_cont⟩
  have hpfst_int : Integrable (fun z : Ω × Ω => pTilde z.1) π.toMeasure :=
    pfstBCF.integrable π.toMeasure
  have hpsnd_int : Integrable (fun z : Ω × Ω => pTilde z.2) π.toMeasure :=
    psndBCF.integrable π.toMeasure
  have hVsel_val_meas : Measurable (fun x : Ω => (Vsel x : Ω)) :=
    hVsel_meas.subtype_val
  have hμ_p :
      expect μ pTilde = ∫ z, pTilde z.1 ∂π.toMeasure := by
    unfold expect
    rw [hμ_eq]
    exact MeasureTheory.integral_map measurable_fst.aemeasurable
      hpTilde_cont.aestronglyMeasurable
  have hν_p :
      expect μ' pTilde = ∫ z, pTilde z.2 ∂π.toMeasure := by
    unfold expect
    rw [hν_eq]
    exact MeasureTheory.integral_map measurable_snd.aemeasurable
      hpTilde_cont.aestronglyMeasurable
  have hcoupling_dist : ∀ᵐ z ∂π.toMeasure, dist z.1 z.2 ≤ δ := by
    have : π.toMeasure = MeasureTheory.Measure.map
        (fun x : Ω => (x, ((Vsel x : Ω)))) μ.toMeasure := by
      unfold π atomizeCoupling
      rw [map_toMeasure]
    rw [this]
    refine (MeasureTheory.ae_map_iff
      (measurable_id.prod hVsel_val_meas).aemeasurable
      (measurableSet_le measurable_dist measurable_const)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact hVsel_dist_le x
  -- Symmetric L-Lipschitz bound: |pTilde x - pTilde y| ≤ L * dist x y.
  have hL_lip_abs : ∀ x y : Ω, |pTilde x - pTilde y| ≤ L * dist x y := by
    intro x y
    have hd := hpTilde_lip.dist_le_mul x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ hL_nonneg] at hd
  -- |expect μ pTilde - expect μ' pTilde| = |∫ (pTilde z.1 - pTilde z.2) dπ| ≤ ∫|...| ≤ L · δ.
  rw [hμ_p, hν_p, ← MeasureTheory.integral_sub hpfst_int hpsnd_int]
  have habs_le_int :
      |∫ z, (pTilde z.1 - pTilde z.2) ∂π.toMeasure| ≤
        ∫ z, |pTilde z.1 - pTilde z.2| ∂π.toMeasure :=
    MeasureTheory.abs_integral_le_integral_abs
  have hL_int : Integrable (fun _ : Ω × Ω => L * δ) π.toMeasure :=
    integrable_const _
  have habs_int_le :
      ∫ z, |pTilde z.1 - pTilde z.2| ∂π.toMeasure ≤ L * δ := by
    calc ∫ z, |pTilde z.1 - pTilde z.2| ∂π.toMeasure
        ≤ ∫ _, L * δ ∂π.toMeasure := by
          refine MeasureTheory.integral_mono_ae
            ((hpfst_int.sub hpsnd_int).abs) hL_int ?_
          filter_upwards [hcoupling_dist] with z hz
          exact (hL_lip_abs z.1 z.2).trans
            (mul_le_mul_of_nonneg_left hz hL_nonneg)
      _ = L * δ := by
          rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  linarith

end Econlib.Optimization.OptimalTransport
