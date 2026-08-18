/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.Discretization.Basic
public import Econlib.Probability.ProbDist.Borel

/-!
# Dual approximation via finite discretization

The discretization pipeline produces dual-feasible prices whose values approximate the concave
closure from above for bounded upper-semicontinuous KR-Lipschitz objectives. Atomizing the prior to
a finite support, solving the finite dual, and extending the resulting price by Lipschitz extension
yields a price feasible for the original problem whose value exceeds the concave closure by an
amount controlled by the chosen mesh.

## Main statements

* `exists_dual_feasible_value_le_concaveClosure_add` — for a bounded upper-semicontinuous
  KR-Lipschitz objective `V` and every `ε > 0`, there is a dual-feasible price `p` with
  `dualObjective μ₀ p ≤ concaveClosure V μ₀ + ε`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 2.

## Tags

persuasion, duality, discretization, approximation
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

section NoDualityGap

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]

variable {n : ℕ}

/-- For a bounded upper-semicontinuous objective `V` that is KR-Lipschitz with constant `L ≥ 0`,
every `ε > 0` admits a dual-feasible price `p` with
`dualObjective μ₀ p ≤ concaveClosure V μ₀ + ε`. -/
theorem exists_dual_feasible_value_le_concaveClosure_add
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
    {V : ProbDist Ω → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hV_bdd : ∃ M : ℝ, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (hV_lip : IsKRLipschitz V L)
    (μ₀ : ProbDist Ω) :
    ∀ ε > 0, ∃ p ∈ feasibleDual V,
      dualObjective μ₀ p
        ≤ concaveClosure V μ₀ + ε := by
  classical
  intro ε hε
  -- The choice `δ = ε / (8(L+1))` ensures `ε/4 + 4Lδ ≤ 3ε/4 ≤ ε` for all `L ≥ 0`.
  set δ : ℝ := ε / (8 * (L + 1)) with hδ_def
  have hLp1_pos : 0 < L + 1 := by linarith
  have h8Lp1_pos : 0 < 8 * (L + 1) := by linarith
  have hδ_pos : 0 < δ := div_pos hε h8Lp1_pos
  have hδ_le : 0 ≤ δ := hδ_pos.le
  obtain ⟨S, Vsel, hVsel_meas, hVsel_dist_lt⟩ :=
    exists_eps_partition (Ω := Ω) δ hδ_pos
  have hVsel_dist_le : ∀ x : Ω, dist x (Vsel x : Ω) ≤ δ :=
    fun x => (hVsel_dist_lt x).le
  set μ₀_δ : ProbDist Ω := atomize μ₀ Vsel hVsel_meas with hμ₀_δ_def
  haveI hΩ : Nonempty Ω := nonempty_of_measure_univ μ₀
  obtain ⟨ω₀⟩ := hΩ
  haveI hS_ne : Nonempty (↥S) := ⟨Vsel ω₀⟩
  have hS_card_pos : 0 < S.card := by
    rw [Finset.card_pos]; exact ⟨(Vsel ω₀ : Ω), (Vsel ω₀).property⟩
  set n : ℕ := S.card with hn_def
  haveI hFn_ne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hS_card_pos
  set atom : Fin n → Ω := fun i => ((S.equivFin.symm i : ↥S) : Ω) with hatom_def
  have hatom_inj : Function.Injective atom := by
    intro i j hij
    have h1 : (S.equivFin.symm i : ↥S) = S.equivFin.symm j := Subtype.ext hij
    exact S.equivFin.symm.injective h1
  set μ₀_coords : Fin n → ℝ := fun i =>
    (μ₀.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})).toReal
    with hμ₀_coords_def
  have hVsel_val_meas : Measurable (fun x : Ω => (Vsel x : Ω)) :=
    hVsel_meas.subtype_val
  have h_simplex : μ₀_coords ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun i => ENNReal.toReal_nonneg, ?_⟩
    have hpre_partition :
        (Set.univ : Set Ω) = ⋃ i : Fin n,
          (fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
      have hin : (Vsel x : Ω) ∈ Set.range atom := by
        refine ⟨S.equivFin (Vsel x), ?_⟩
        simp [hatom_def]
      obtain ⟨i, hi⟩ := hin
      exact ⟨i, hi.symm⟩
    have hpre_disjoint : Pairwise (Function.onFun Disjoint
        (fun i : Fin n =>
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
    have hpre_meas : ∀ i : Fin n,
        MeasurableSet ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)}) :=
      fun i => hVsel_val_meas (MeasurableSet.singleton _)
    have hsum_eq :
        ∑ i : Fin n, μ₀.toMeasure
          ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})
          = μ₀.toMeasure Set.univ := by
      rw [hpre_partition]
      rw [MeasureTheory.measure_iUnion hpre_disjoint hpre_meas]
      rw [tsum_fintype]
    have hsum_real :
        ∑ i : Fin n, (μ₀.toMeasure
          ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})).toReal =
          (μ₀.toMeasure Set.univ).toReal := by
      rw [← hsum_eq]
      rw [ENNReal.toReal_sum]
      intro i _
      exact (measure_lt_top μ₀.toMeasure _).ne
    change ∑ i, (μ₀.toMeasure
        ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})).toReal = 1
    rw [hsum_real, MeasureTheory.measure_univ, ENNReal.toReal_one]
  set μ₀_coords_sub : stdSimplex ℝ (Fin n) := ⟨μ₀_coords, h_simplex⟩
    with hμ₀_coords_sub_def
  have h_match : finiteLaw atom μ₀_coords_sub = μ₀_δ := by
    apply finiteLaw_atomize_eq μ₀ Vsel hVsel_meas μ₀_coords h_simplex
    intro i
    rfl
  have h_krDist_le :
      krDist μ₀ μ₀_δ ≤ δ :=
    atomize_krDist_le μ₀ Vsel hVsel_meas hVsel_dist_le
  have hV_bddAbove : BddAbove (Set.range V) := by
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨μ, rfl⟩
    exact (abs_le.mp (hM μ)).2
  have hV_fin_bddAbove : BddAbove (Set.range (finiteObjective V atom)) := by
    obtain ⟨M, hM⟩ := finiteObjective_bdd atom hV_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨lam, rfl⟩
    exact (abs_le.mp (hM lam)).2
  have hV_fin_usc : UpperSemicontinuousOn (finiteObjective V atom) (stdSimplex ℝ (Fin n)) :=
    finiteObjective_usc atom hV_usc
  have hFM : finConcaveClosure (finiteObjective V atom) μ₀_coords =
      finConcaveEnvelope (finiteObjective V atom) μ₀_coords :=
    finFenchelMoreau h_simplex hV_fin_bddAbove hV_fin_usc
  have hFE_ne :
      { y : ℝ | ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), finiteObjective V atom μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀_coords i + c }.Nonempty :=
    finConcaveEnvelope_values_nonempty hV_fin_bddAbove
  have hFE_bdd :
      BddBelow { y : ℝ | ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), finiteObjective V atom μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀_coords i + c } := by
    refine ⟨finiteObjective V atom μ₀_coords, ?_⟩
    rintro y ⟨p, c, haff, rfl⟩
    exact haff μ₀_coords h_simplex
  have hε4_pos : (0 : ℝ) < ε / 4 := by linarith
  have h_inf_lt :
      sInf { y : ℝ | ∃ (p : Fin n → ℝ) (c : ℝ),
        (∀ μ ∈ stdSimplex ℝ (Fin n), finiteObjective V atom μ ≤ ∑ i, p i * μ i + c) ∧
        y = ∑ i, p i * μ₀_coords i + c } <
      finConcaveEnvelope (finiteObjective V atom) μ₀_coords + ε / 4 := by
    change finConcaveEnvelope (finiteObjective V atom) μ₀_coords <
      finConcaveEnvelope (finiteObjective V atom) μ₀_coords + ε / 4
    linarith
  obtain ⟨y, hy_mem, hy_lt⟩ := exists_lt_of_csInf_lt hFE_ne h_inf_lt
  obtain ⟨p_raw, c, hp_raw_aff, hy_eq⟩ := hy_mem
  have h_p_raw_near :
      ∑ i, p_raw i * μ₀_coords i + c ≤
        finConcaveClosure (finiteObjective V atom) μ₀_coords + ε / 4 := by
    have h1 : y ≤ finConcaveClosure (finiteObjective V atom) μ₀_coords + ε / 4 := by
      rw [hFM]; linarith
    rw [hy_eq] at h1; exact h1
  set p_S : Fin n → ℝ := cConjugate atom L p_raw with hp_S_def
  have hp_S_le_raw : ∀ i, p_S i ≤ p_raw i := fun i => cConjugate_le_raw i
  have hp_S_aff : ∀ μ ∈ stdSimplex ℝ (Fin n),
      finiteObjective V atom μ ≤ ∑ i, p_S i * μ i + c :=
    finiteObjective_majorized_by_cConjugate hL_nonneg hV_lip hp_raw_aff
  have hp_S_lipFinite : ∀ i j : Fin n,
      |p_S i - p_S j| ≤ L * dist (atom i) (atom j) :=
    fun i j => cConjugate_abs_sub_le hL_nonneg i j
  set f₀ : Ω → ℝ := fun x =>
    if h : x ∈ Set.range atom then p_S (Function.invFun atom x) else 0
    with hf₀_def
  have hf₀_atom : ∀ i : Fin n, f₀ (atom i) = p_S i := by
    intro i
    have hmem : atom i ∈ Set.range atom := ⟨i, rfl⟩
    rw [hf₀_def]
    simp only [hmem, dite_true]
    have hinv : Function.invFun atom (atom i) = i :=
      Function.leftInverse_invFun hatom_inj i
    rw [hinv]
  have hf₀_lipOn : LipschitzOnWith L.toNNReal f₀ (Set.range atom) := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    have hf₀x : f₀ x = p_S i := by rw [← hi]; exact hf₀_atom i
    have hf₀y : f₀ y = p_S j := by rw [← hj]; exact hf₀_atom j
    rw [edist_dist (f₀ x) (f₀ y), edist_dist x y]
    rw [hf₀x, hf₀y, Real.dist_eq]
    have hLip : |p_S i - p_S j| ≤ L * dist x y := by
      rw [← hi, ← hj]; exact hp_S_lipFinite i j
    have hLp : 0 ≤ L * dist x y := mul_nonneg hL_nonneg dist_nonneg
    have hofreal_L : ENNReal.ofReal L = (L.toNNReal : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hL_nonneg, Real.toNNReal_of_nonneg hL_nonneg]
    calc ENNReal.ofReal |p_S i - p_S j|
        ≤ ENNReal.ofReal (L * dist x y) := ENNReal.ofReal_le_ofReal hLip
      _ = ENNReal.ofReal L * ENNReal.ofReal (dist x y) :=
          ENNReal.ofReal_mul hL_nonneg
      _ = (L.toNNReal : ENNReal) * ENNReal.ofReal (dist x y) := by
          rw [hofreal_L]
  obtain ⟨pTilde, hpTilde_lip, hpTilde_eq⟩ := hf₀_lipOn.extend_real
  have hpTilde_atom : ∀ i : Fin n, pTilde (atom i) = p_S i := by
    intro i
    have h := hpTilde_eq ⟨i, rfl⟩
    rw [← h]; exact hf₀_atom i
  set constant : ℝ := c + 2 * L * δ with hconstant_def
  set p_dual : Ω → ℝ := fun x => pTilde x + constant with hp_dual_def
  have h_pTilde_finiteLaw :
      ∀ lam : stdSimplex ℝ (Fin n),
        ProbDist.expect (finiteLaw atom lam) pTilde
          = ∑ i, (lam : Fin n → ℝ) i * p_S i := by
    intro lam
    rw [finiteLaw_expect atom lam pTilde hpTilde_lip.continuous.aestronglyMeasurable]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hpTilde_atom i]
  have h_pTilde_atomize_bound :=
    expect_atomize_bound (Vsel := Vsel) (hVsel_meas := hVsel_meas)
      (pTilde := pTilde) (hL_nonneg := hL_nonneg) hpTilde_lip hVsel_dist_le
  -- `pTilde` is Lipschitz on a compact space, hence bounded continuous, hence integrable.
  have hpTilde_int : ∀ μ : ProbDist Ω, Integrable pTilde μ.toMeasure := fun μ =>
    (BoundedContinuousFunction.mkOfCompact ⟨pTilde, hpTilde_lip.continuous⟩).integrable _
  obtain ⟨M, hM⟩ := hV_bdd
  refine ⟨p_dual, ?_, ?_⟩
  · refine ⟨⟨L.toNNReal, ?_⟩, ?_⟩
    · change LipschitzWith L.toNNReal (fun x : Ω => pTilde x + constant)
      intro x y
      have h := hpTilde_lip x y
      simp only [edist_dist, Real.dist_eq] at h ⊢
      have heq : pTilde x + constant - (pTilde y + constant) = pTilde x - pTilde y := by ring
      rw [heq]
      exact h
    · intro μ
      set μ_δ : ProbDist Ω := atomize μ Vsel hVsel_meas with hμ_δ_def
      set μ_coords : Fin n → ℝ := fun i =>
        (μ.toMeasure ((fun x : Ω => (Vsel x : Ω)) ⁻¹' {(atom i : Ω)})).toReal
        with hμ_coords_def
      have hμ_simplex : μ_coords ∈ stdSimplex ℝ (Fin n) :=
        atomize_coords_mem_stdSimplex μ Vsel hVsel_meas
      set μ_coords_sub : stdSimplex ℝ (Fin n) := ⟨μ_coords, hμ_simplex⟩
        with hμ_coords_sub_def
      have hμ_match : finiteLaw atom μ_coords_sub = μ_δ := by
        apply finiteLaw_atomize_eq μ Vsel hVsel_meas μ_coords hμ_simplex
        intro i; rfl
      have hμ_kr : krDist μ μ_δ ≤ δ :=
        atomize_krDist_le μ Vsel hVsel_meas hVsel_dist_le
      have step_a : V μ ≤ V μ_δ + L * δ := by
        have h1 : V μ - V μ_δ ≤ L * krDist μ μ_δ := hV_lip μ μ_δ
        have h2 : L * krDist μ μ_δ ≤ L * δ :=
          mul_le_mul_of_nonneg_left hμ_kr hL_nonneg
        linarith
      have step_b : V μ_δ = finiteObjective V atom μ_coords := by
        rw [finiteObjective_of_mem hμ_simplex]
        congr 1
        exact hμ_match.symm
      have step_c : finiteObjective V atom μ_coords ≤ ∑ i, p_S i * μ_coords i + c :=
        hp_S_aff μ_coords hμ_simplex
      have step_d : ∑ i, p_S i * μ_coords i = ProbDist.expect μ_δ pTilde := by
        rw [← hμ_match]
        rw [h_pTilde_finiteLaw μ_coords_sub]
        refine Finset.sum_congr rfl ?_
        intro i _
        show p_S i * μ_coords i = (μ_coords_sub : Fin n → ℝ) i * p_S i
        change p_S i * μ_coords i = μ_coords i * p_S i
        ring
      have step_e : ProbDist.expect μ_δ pTilde ≤ ProbDist.expect μ pTilde + L * δ := by
        have h2 := abs_le.mp (h_pTilde_atomize_bound μ)
        linarith [h2.1, h2.2]
      have h_expect_p_dual : ProbDist.expect μ p_dual = ProbDist.expect μ pTilde + constant := by
        simpa [hp_dual_def] using expect_add_const μ pTilde constant (hpTilde_int μ)
      rw [h_expect_p_dual]
      have hsum : V μ ≤ ProbDist.expect μ pTilde + constant := by
        calc V μ ≤ V μ_δ + L * δ := step_a
          _ = finiteObjective V atom μ_coords + L * δ := by rw [step_b]
          _ ≤ (∑ i, p_S i * μ_coords i + c) + L * δ := by linarith [step_c]
          _ = ProbDist.expect μ_δ pTilde + c + L * δ := by rw [step_d]
          _ ≤ (ProbDist.expect μ pTilde + L * δ) + c + L * δ := by linarith [step_e]
          _ = ProbDist.expect μ pTilde + (c + 2 * L * δ) := by ring
          _ = ProbDist.expect μ pTilde + constant := by rw [hconstant_def]
      exact hsum
  · have h_expect_p_dual_at_μ₀ :
        ProbDist.expect μ₀ p_dual = ProbDist.expect μ₀ pTilde + constant := by
      simpa [hp_dual_def] using expect_add_const μ₀ pTilde constant (hpTilde_int μ₀)
    have h_Vhat_lip :
        IsKRLipschitz (concaveClosure V) L :=
      isKRLipschitz_concaveClosure_of_isKRLipschitz ⟨M, hM⟩ hV_usc hV_lip
    have step_a' : ProbDist.expect μ₀ pTilde ≤ ProbDist.expect μ₀_δ pTilde + L * δ := by
      have h2 := abs_le.mp (h_pTilde_atomize_bound μ₀)
      linarith [h2.1, h2.2]
    have step_b' : ProbDist.expect μ₀_δ pTilde = ∑ i, p_S i * μ₀_coords i := by
      rw [← h_match]
      rw [h_pTilde_finiteLaw μ₀_coords_sub]
      refine Finset.sum_congr rfl ?_
      intro i _
      change μ₀_coords i * p_S i = p_S i * μ₀_coords i
      ring
    have step_c' : ∑ i, p_S i * μ₀_coords i ≤ ∑ i, p_raw i * μ₀_coords i := by
      refine Finset.sum_le_sum ?_
      intro i _
      exact mul_le_mul_of_nonneg_right (hp_S_le_raw i) (h_simplex.1 i)
    -- Each finite splitting of `μ₀_coords` in the simplex lifts to a Bayes-plausible
    -- distribution over `μ₀_δ` via `finiteLaw atom`, so the finite concave closure
    -- is bounded above by the continuous concave closure at `μ₀_δ`.
    have step_e' :
        finConcaveClosure (finiteObjective V atom) μ₀_coords ≤
          concaveClosure V μ₀_δ := by
      unfold finConcaveClosure concaveClosure
      refine csSup_le (finConcaveClosure_values_nonempty (finiteObjective V atom) h_simplex) ?_
      rintro v ⟨k, _hk, lam, ν, hlam_nonneg, hlam_sum, hν_simplex, hbayes, rfl⟩
      classical
      let lift_post : Fin k → ProbDist Ω := fun j => finiteLaw atom ⟨ν j, hν_simplex j⟩
      let lam_findist : FinDist (Fin k) :=
        { pmf := lam
          nonneg := hlam_nonneg
          sum_one := hlam_sum }
      let τ : ProbDist (ProbDist Ω) :=
        ProbDist.map lam_findist.toProbDist lift_post (measurable_of_finite _)
      have hτ_bayes : IsBayesPlausible μ₀_δ τ := by
        intro f
        change ProbDist.expect τ (fun μ => ProbDist.expect μ f) = ProbDist.expect μ₀_δ f
        have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ f) := by
          simpa [ProbDist.expect] using
            (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
              (X := Ω) f)
        have hτ_eq : τ = ProbDist.map lam_findist.toProbDist lift_post
            (measurable_of_finite _) := rfl
        rw [hτ_eq, ProbDist.expect_map lam_findist.toProbDist lift_post
            (measurable_of_finite _) (fun μ => ProbDist.expect μ f)
            hcont.aestronglyMeasurable]
        rw [← FinDist.expect_eq_probDist_expect]
        change ∑ j, lam j * ProbDist.expect (finiteLaw atom ⟨ν j, hν_simplex j⟩) f =
            ProbDist.expect μ₀_δ f
        have hlift_f : ∀ j, ProbDist.expect (finiteLaw atom ⟨ν j, hν_simplex j⟩) f =
            ∑ i, ν j i * f (atom i) := by
          intro j
          exact finiteLaw_expect_boundedContinuous atom ⟨ν j, hν_simplex j⟩ f
        simp_rw [hlift_f]
        rw [show
            (∑ j : Fin k, lam j * (∑ i : Fin n, ν j i * f (atom i)))
              = (∑ i : Fin n, (∑ j : Fin k, lam j * ν j i) * f (atom i)) from by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            ring]
        have hcoord : ∀ i : Fin n, (∑ j : Fin k, lam j * ν j i) = μ₀_coords i := by
          intro i
          have h := congrFun hbayes i
          have hsmul : (∑ j, lam j • ν j) i = ∑ j, lam j * ν j i := by
            rw [Finset.sum_apply]
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [Pi.smul_apply, smul_eq_mul]
          rw [hsmul] at h
          exact h
        simp_rw [hcoord]
        rw [show ProbDist.expect μ₀_δ f = ∑ i : Fin n, μ₀_coords i * f (atom i) from by
          rw [← h_match]
          exact finiteLaw_expect_boundedContinuous atom μ₀_coords_sub f]
      have hτ_value :
          primalValue V τ =
            ∑ j : Fin k, lam j * finiteObjective V atom (ν j) := by
        unfold primalValue τ lift_post
        rw [show (fun μ => V μ) = V from rfl]
        have hVmeas : Measurable V := hV_usc.measurable
        rw [ProbDist.map_toMeasure]
        rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
            hVmeas.aestronglyMeasurable]
        change ∫ j, V (finiteLaw atom ⟨ν j, hν_simplex j⟩) ∂lam_findist.toProbDist.toMeasure = _
        rw [show (fun j : Fin k => V (finiteLaw atom ⟨ν j, hν_simplex j⟩)) =
              (fun j : Fin k => finiteObjective V atom (ν j)) from by
          funext j
          exact (finiteObjective_of_mem (hν_simplex j)).symm]
        change ProbDist.expect lam_findist.toProbDist
            (fun j => finiteObjective V atom (ν j)) = _
        rw [← FinDist.expect_eq_probDist_expect]
        rfl
      have hτ_value_le : primalValue V τ ≤
          concaveClosure V μ₀_δ := by
        unfold concaveClosure
        refine le_csSup ?_ ?_
        · refine ⟨M, ?_⟩
          rintro w ⟨σ, _, rfl⟩
          unfold primalValue
          have hVle : ∀ μ : ProbDist Ω, V μ ≤ M := fun μ => (abs_le.mp (hM μ)).2
          have hV_int : Integrable V σ.toMeasure := by
            refine ⟨hV_usc.measurable.aestronglyMeasurable, ?_⟩
            refine (hasFiniteIntegral_const M).mono' ?_
            refine Filter.Eventually.of_forall fun μ => ?_
            simp only [Real.norm_eq_abs]
            exact hM μ
          calc ∫ μ, V μ ∂σ.toMeasure
              ≤ ∫ _, M ∂σ.toMeasure :=
                MeasureTheory.integral_mono hV_int (integrable_const _) hVle
            _ = M := by simp [MeasureTheory.probReal_univ]
        · exact ⟨τ, hτ_bayes, rfl⟩
      rw [← hτ_value] at *
      exact hτ_value_le
    have step_f' :
        concaveClosure V μ₀_δ ≤
          concaveClosure V μ₀ + L * δ := by
      have h := h_Vhat_lip μ₀_δ μ₀
      have hkr_sym : krDist μ₀_δ μ₀ = krDist μ₀ μ₀_δ :=
        krDist_comm μ₀_δ μ₀
      rw [hkr_sym] at h
      have h2 : L * krDist μ₀ μ₀_δ ≤ L * δ :=
        mul_le_mul_of_nonneg_left h_krDist_le hL_nonneg
      linarith
    have hδ_choice : ε / 4 + 4 * L * δ ≤ ε := by
      have hL_le : L ≤ L + 1 := by linarith
      have hL_div_le : L / (L + 1) ≤ 1 := by
        rw [div_le_one hLp1_pos]; linarith
      have h_4Lδ_le : 4 * L * δ ≤ ε / 2 := by
        rw [hδ_def]
        rw [show 4 * L * (ε / (8 * (L + 1))) =
              (ε / 2) * (L / (L + 1)) from by field_simp; ring]
        have : (ε / 2) * (L / (L + 1)) ≤ (ε / 2) * 1 :=
          mul_le_mul_of_nonneg_left hL_div_le (by linarith)
        linarith
      linarith
    change ProbDist.expect μ₀ p_dual ≤ concaveClosure V μ₀ + ε
    rw [h_expect_p_dual_at_μ₀]
    calc ProbDist.expect μ₀ pTilde + constant
        ≤ (ProbDist.expect μ₀_δ pTilde + L * δ) + constant := by linarith [step_a']
      _ = (∑ i, p_S i * μ₀_coords i + L * δ) + constant := by rw [step_b']
      _ ≤ (∑ i, p_raw i * μ₀_coords i + L * δ) + constant := by linarith [step_c']
      _ = (∑ i, p_raw i * μ₀_coords i + c) + (3 * L * δ) := by
            rw [hconstant_def]; ring
      _ ≤ (finConcaveClosure (finiteObjective V atom) μ₀_coords + ε / 4) + 3 * L * δ := by
            linarith [h_p_raw_near]
      _ ≤ concaveClosure V μ₀_δ + ε / 4 + 3 * L * δ := by
            linarith [step_e']
      _ ≤ (concaveClosure V μ₀ + L * δ) + ε / 4 + 3 * L * δ := by
            linarith [step_f']
      _ = concaveClosure V μ₀ + (ε / 4 + 4 * L * δ) := by ring
      _ ≤ concaveClosure V μ₀ + ε := by linarith [hδ_choice]

end NoDualityGap

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
