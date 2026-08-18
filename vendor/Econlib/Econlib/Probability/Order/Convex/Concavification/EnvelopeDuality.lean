/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.EnvelopeDuality
public import Econlib.Probability.Order.Convex.Concavification.Envelope

open MeasureTheory Set

/-!
# Optimizer existence and contact sets at the envelope value

Probability layer over the pure envelope-duality core
(`Econlib.Math.Analysis.Concavification1D.EnvelopeDuality`). Translates the concave-envelope =
two-point-value identity into probabilistic statements: A concrete optimal two-point law attaining
the envelope value, and a contact-set refinement for distributions achieving the envelope upper
bound at their mean. This is the optimal-signal characterization for 1D Bayesian persuasion
(Kamenica and Gentzkow 2011).

## Main statements

* `exists_twoPointLaw_expect_eq_concaveEnvelope` — a mean-`μ` two-point law attains the envelope.
* `supportsOn_contactSet_of_expect_eq_concaveEnvelope` — a distribution achieving the envelope
  bound at an interior mean is supported on the contact set of an attaining affine majorant.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

concave envelope, concavification, optimal signal, contact set, two-point law, bayesian persuasion
-/

@[expose] public section

namespace Econlib.Probability

/-- **Optimizer existence in envelope form.** For any `μ ∈ [a, b]` there exists a two-point law
with mean `μ`, atoms in `[a, b]`, whose `φ`-expectation equals the concave envelope of `φ` at
`μ`. -/
theorem exists_twoPointLaw_expect_eq_concaveEnvelope
    {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {μ : ℝ} (hμ : μ ∈ Icc a b) :
    ∃ (xL xR q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      xL ∈ Icc a b ∧ xR ∈ Icc a b ∧
      (1 - q) * xL + q * xR = μ ∧
      (twoPointLaw q xL xR hq0 hq1).expect φ = concaveEnvelope a b φ μ := by
  obtain ⟨xL, xR, q, hq0, hq1, hxL, hxR, hmean, hexpect⟩ :=
    exists_twoPointLaw_expect_eq_twoPointValue hab hφ hμ
  refine ⟨xL, xR, q, hq0, hq1, hxL, hxR, hmean, ?_⟩
  rw [hexpect, ← concaveEnvelope_eq_twoPointValue hab hφ hμ]

/-- Interior supporting-affine-majorant construction for the degenerate case: When every two-point
splitting of an interior mean `μ` has `φ`-expectation at most `φ μ`, there is an affine majorant of
`φ` on `[a, b]` touching `φ` exactly at `μ`. -/
private lemma exists_affineMajorant_through_phi_of_degenerate_twoPointOptimum_interior
    -- `_hφ` unused: the chord inequality alone drives the sSup/csSup slope argument below;
    -- kept for parity with the calling context, which only has continuity in hand.
    {a b μ : ℝ} {φ : ℝ → ℝ} (_hφ : Continuous φ)
    (ha_lt_μ : a < μ) (hμ_lt_b : μ < b)
    (hchord : ∀ p ∈ twoPointFeasibleSet a b μ, twoPointObjective φ p ≤ φ μ) :
    ∃ m c, IsAffineMajorant a b φ m c ∧ affineFun m c μ = φ μ := by
  have hchord_ineq : ∀ t₁ t₂ : ℝ, t₁ ∈ Icc a μ → t₂ ∈ Icc μ b → t₁ < t₂ →
      (t₂ - μ) * φ t₁ + (μ - t₁) * φ t₂ ≤ (t₂ - t₁) * φ μ := by
    intro t₁ t₂ ht₁ ht₂ hlt
    have ht₁' : t₁ ∈ Icc a b := ⟨ht₁.1, le_trans ht₁.2 (le_of_lt hμ_lt_b)⟩
    have ht₂' : t₂ ∈ Icc a b := ⟨le_trans (le_of_lt ha_lt_μ) ht₂.1, ht₂.2⟩
    have ht₂_sub_t₁_pos : 0 < t₂ - t₁ := sub_pos.mpr hlt
    set q' := (μ - t₁) / (t₂ - t₁) with hq'_def
    have hq'_nn : 0 ≤ q' :=
      div_nonneg (by linarith [ht₁.2]) (le_of_lt ht₂_sub_t₁_pos)
    have hq'_le1 : q' ≤ 1 := by
      rw [hq'_def, div_le_one ht₂_sub_t₁_pos]
      linarith [ht₂.1]
    have hmean' : (1 - q') * t₁ + q' * t₂ = μ := by
      rw [hq'_def]
      field_simp
      ring
    have hpair_mem : (t₁, t₂, q') ∈ twoPointFeasibleSet a b μ :=
      ⟨ht₁', ht₂', ⟨hq'_nn, hq'_le1⟩, hmean'⟩
    have hobj_le := hchord (t₁, t₂, q') hpair_mem
    simp only [twoPointObjective] at hobj_le
    have hstep :
        ((1 - q') * φ t₁ + q' * φ t₂) * (t₂ - t₁) ≤ φ μ * (t₂ - t₁) :=
      mul_le_mul_of_nonneg_right hobj_le (le_of_lt ht₂_sub_t₁_pos)
    have hexpand :
        ((1 - q') * φ t₁ + q' * φ t₂) * (t₂ - t₁) =
          (t₂ - μ) * φ t₁ + (μ - t₁) * φ t₂ := by
      rw [hq'_def]
      field_simp
      ring
    linarith [hexpand ▸ hstep]
  have hμ_sub_a_pos : 0 < μ - a := sub_pos.mpr ha_lt_μ
  have hb_sub_μ_pos : 0 < b - μ := sub_pos.mpr hμ_lt_b
  set rSlopes : Set ℝ := (fun t => (φ t - φ μ) / (t - μ)) '' Set.Ioc μ b with hrSlopes_def
  have hrSlopes_nonempty : rSlopes.Nonempty :=
    ⟨(φ b - φ μ) / (b - μ), b, ⟨hμ_lt_b, le_rfl⟩, rfl⟩
  set leftBound := (φ μ - φ a) / (μ - a) with hleftBound_def
  have hrSlopes_bdd : ∀ x ∈ rSlopes, x ≤ leftBound := by
    rintro _ ⟨t, ⟨ht_gt, ht_le⟩, rfl⟩
    have ht_in_right : t ∈ Set.Icc μ b := ⟨le_of_lt ht_gt, ht_le⟩
    have ha_in_left : (a : ℝ) ∈ Set.Icc a μ := ⟨le_rfl, le_of_lt ha_lt_μ⟩
    have ha_lt_t : a < t := lt_trans ha_lt_μ ht_gt
    have hcineq := hchord_ineq a t ha_in_left ht_in_right ha_lt_t
    have ht_sub_μ_pos : 0 < t - μ := sub_pos.mpr ht_gt
    have hcross : (φ t - φ μ) * (μ - a) ≤ (φ μ - φ a) * (t - μ) := by
      nlinarith [hcineq]
    rw [hleftBound_def]
    rw [div_le_div_iff₀ ht_sub_μ_pos hμ_sub_a_pos]
    linarith
  have hrSlopes_bddAbove : BddAbove rSlopes := ⟨leftBound, hrSlopes_bdd⟩
  set m := sSup rSlopes with hm_def
  have hm_upper : ∀ x ∈ rSlopes, x ≤ m := fun x hx => le_csSup hrSlopes_bddAbove hx
  have hm_le_leftSlope : ∀ t₁ ∈ Set.Ico a μ, m ≤ (φ μ - φ t₁) / (μ - t₁) := by
    intro t₁ ht₁
    have ht₁_lt_μ : t₁ < μ := ht₁.2
    have hμ_sub_t₁_pos : 0 < μ - t₁ := sub_pos.mpr ht₁_lt_μ
    have ht₁_in_left : t₁ ∈ Set.Icc a μ := ⟨ht₁.1, le_of_lt ht₁_lt_μ⟩
    refine csSup_le hrSlopes_nonempty ?_
    rintro _ ⟨t₂, ⟨ht₂_gt, ht₂_le⟩, rfl⟩
    have ht₂_in_right : t₂ ∈ Set.Icc μ b := ⟨le_of_lt ht₂_gt, ht₂_le⟩
    have ht₂_sub_μ_pos : 0 < t₂ - μ := sub_pos.mpr ht₂_gt
    have ht₁_lt_t₂ : t₁ < t₂ := lt_trans ht₁_lt_μ ht₂_gt
    have hcineq := hchord_ineq t₁ t₂ ht₁_in_left ht₂_in_right ht₁_lt_t₂
    rw [div_le_div_iff₀ ht₂_sub_μ_pos hμ_sub_t₁_pos]
    nlinarith [hcineq]
  set c := φ μ - m * μ with hc_def
  have hline_μ : m * μ + c = φ μ := by
    rw [hc_def]
    ring
  have hmaj : IsAffineMajorant a b φ m c := by
    intro t ht
    rcases lt_trichotomy t μ with ht_lt | ht_eq | ht_gt
    · have ht_in_Ico : t ∈ Set.Ico a μ := ⟨ht.1, ht_lt⟩
      have hslope := hm_le_leftSlope t ht_in_Ico
      have hμ_sub_t_pos : 0 < μ - t := sub_pos.mpr ht_lt
      have hineq : m * (μ - t) ≤ φ μ - φ t := by
        rw [le_div_iff₀ hμ_sub_t_pos] at hslope
        linarith
      have hL_eq : m * t + c = φ μ - m * (μ - t) := by
        rw [hc_def]
        ring
      rw [hL_eq]
      linarith
    · rw [ht_eq, hline_μ]
    · have ht_in_Ioc : t ∈ Set.Ioc μ b := ⟨ht_gt, ht.2⟩
      have ht_in_rSlopes : (φ t - φ μ) / (t - μ) ∈ rSlopes := ⟨t, ht_in_Ioc, rfl⟩
      have hslope := hm_upper _ ht_in_rSlopes
      have ht_sub_μ_pos : 0 < t - μ := sub_pos.mpr ht_gt
      have hineq : φ t - φ μ ≤ m * (t - μ) := by
        rw [div_le_iff₀ ht_sub_μ_pos] at hslope
        linarith
      have hL_eq : m * t + c = m * (t - μ) + φ μ := by
        rw [hc_def]
        ring
      rw [hL_eq]
      linarith
  exact ⟨m, c, hmaj, hline_μ⟩

/-- **Contact-set refinement in envelope form.** If a distribution supported on `[a, b]` achieves
the concave-envelope upper bound at its mean, then it is supported on the contact set of some
affine majorant attaining the envelope value.

The interior-mean hypothesis is necessary. At endpoints, continuous functions can have concave
envelopes with no finite supporting affine majorant touching the value (for example
`x ↦ Real.sqrt x` at `0` on `[0,1]`). -/
theorem supportsOn_contactSet_of_expect_eq_concaveEnvelope
    {d : ProbDist ℝ} {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hsupp : d.supportsOn (Icc a b))
    (hmean : d.expect id ∈ Ioo a b)
    (heq : d.expect φ = concaveEnvelope a b φ (d.expect id)) :
    ∃ m c, IsAffineMajorant a b φ m c ∧
      d.supportsOn (contactSet a b φ m c) ∧
      d.expect φ = affineFun m c (d.expect id) := by
  let μ := d.expect id
  have hμIcc : μ ∈ Icc a b := ⟨hmean.1.le, hmean.2.le⟩
  obtain ⟨⟨xL₀, xR₀, q₀⟩, hmem₀, hmax₀⟩ := exists_twoPointOptimum hφ hμIcc
  have hsym_feasible :
      ∀ {xL xR q : ℝ}, (xL, xR, q) ∈ twoPointFeasibleSet a b μ →
        (xR, xL, 1 - q) ∈ twoPointFeasibleSet a b μ := by
    intro xL xR q hp
    rcases hp with ⟨hxL, hxR, hq_mem, hμeq⟩
    refine ⟨hxR, hxL, ⟨?_, ?_⟩, ?_⟩
    · linarith [hq_mem.2]
    · linarith [hq_mem.1]
    · have : (1 - (1 - q)) * xR + (1 - q) * xL = q * xR + (1 - q) * xL := by ring
      rw [this]
      linarith [hμeq]
  have hsym_obj : ∀ (xL xR q : ℝ),
      twoPointObjective φ (xR, xL, 1 - q) = twoPointObjective φ (xL, xR, q) := by
    intro xL xR q
    simp [twoPointObjective]
    ring
  let xL := if hx : xL₀ ≤ xR₀ then xL₀ else xR₀
  let xR := if hx : xL₀ ≤ xR₀ then xR₀ else xL₀
  let q := if hx : xL₀ ≤ xR₀ then q₀ else 1 - q₀
  have hxLxR : xL ≤ xR := by
    by_cases hx : xL₀ ≤ xR₀
    · simp [xL, xR, hx]
    · simp [xL, xR, hx, le_of_not_ge hx]
  have hmem : (xL, xR, q) ∈ twoPointFeasibleSet a b μ := by
    by_cases hx : xL₀ ≤ xR₀
    · simpa [xL, xR, q, hx] using hmem₀
    · simpa [xL, xR, q, hx] using hsym_feasible hmem₀
  have hmax : IsMaxOn (twoPointObjective φ) (twoPointFeasibleSet a b μ) (xL, xR, q) := by
    by_cases hx : xL₀ ≤ xR₀
    · simpa [xL, xR, q, hx] using hmax₀
    · intro p hp
      have h1 := hsym_feasible hp
      have h2 := hmax₀ h1
      have hp_eq : twoPointObjective φ p = twoPointObjective φ (p.2.1, p.1, 1 - p.2.2) := by
        simpa using (hsym_obj p.1 p.2.1 p.2.2).symm
      have hxr_eq :
          twoPointObjective φ (xL₀, xR₀, q₀) =
            twoPointObjective φ (xR₀, xL₀, 1 - q₀) := by
        simpa using (hsym_obj xL₀ xR₀ q₀).symm
      simpa [xL, xR, q, hx] using (hp_eq.trans_le (h2.trans_eq hxr_eq))
  have hval_eq :
      twoPointValue a b φ μ = (1 - q) * φ xL + q * φ xR := by
    unfold twoPointValue
    refine le_antisymm ?_ ?_
    · refine csSup_le ((twoPointFeasibleSet_nonempty hμIcc).image _) ?_
      rintro v ⟨p, hp, rfl⟩
      have := hmax hp
      simpa [twoPointObjective] using this
    · refine le_csSup ?_ ⟨(xL, xR, q), hmem, ?_⟩
      · exact (twoPointFeasibleSet_isCompact a b μ).bddAbove_image
          (twoPointObjective_continuous hφ).continuousOn
      · simp [twoPointObjective]
  have hval_eq_env : (1 - q) * φ xL + q * φ xR = concaveEnvelope a b φ μ := by
    rw [← hval_eq, ← concaveEnvelope_eq_twoPointValue hab hφ hμIcc]
  rcases hmem with ⟨hxL_mem, hxR_mem, hq_mem, hμeq⟩
  by_cases hnondeg : xL < xR ∧ 0 < q ∧ q < 1
  · obtain ⟨hxLR_lt, hq_pos, hq_lt1⟩ := hnondeg
    let m : ℝ := (φ xR - φ xL) / (xR - xL)
    let c : ℝ := φ xL - m * xL
    have hμeq' : (1 - q) * xL + q * xR ∈ Icc a b := hμeq ▸ hμIcc
    have hmaj :
        IsAffineMajorant a b φ m c := by
      have hopt' :
          IsMaxOn (twoPointObjective φ)
            (twoPointFeasibleSet a b ((1 - q) * xL + q * xR)) (xL, xR, q) := by
        rw [hμeq]
        exact hmax
      simpa [m, c] using
        isAffineMajorant_secant_of_twoPointOptimum hφ hxL_mem hxR_mem hxLR_lt hq_pos hq_lt1
          hμeq' hopt'
    have hline : affineFun m c μ = concaveEnvelope a b φ μ := by
      have h1 : m * xL + c = φ xL := by
        simp [m, c]
      have h2 : m * xR + c = φ xR := by
        dsimp [m, c]
        field_simp [sub_ne_zero.mpr hxLR_lt.ne']
        ring
      have hline_μ : m * μ + c = (1 - q) * φ xL + q * φ xR := by
        rw [← hμeq]
        have hrw : m * ((1 - q) * xL + q * xR) + c
            = (1 - q) * (m * xL + c) + q * (m * xR + c) := by ring
        rw [hrw, h1, h2]
      rw [show affineFun m c μ = m * μ + c by rfl, hline_μ, hval_eq_env]
    have heq' : d.expect φ = affineFun m c μ := by
      rw [heq, hline]
    refine ⟨m, c, hmaj, ?_, ?_⟩
    · simpa [μ] using supportsOn_contactSet_of_expect_eq_affineFun hsupp hmaj hφ heq'
    · simpa [μ] using heq'
  · have hval_eq_phi : (1 - q) * φ xL + q * φ xR = φ μ := by
      rcases not_and_or.mp hnondeg with hxLR_nlt | hq_not_in_Ioo
      · have hxLR_eq : xL = xR := le_antisymm hxLxR (not_lt.mp hxLR_nlt)
        have hμ_eq : μ = xL := by
          rw [← hxLR_eq] at hμeq
          linarith
        rw [← hxLR_eq, hμ_eq]
        ring
      · rcases not_and_or.mp hq_not_in_Ioo with hq_not_pos | hq_not_lt1
        · have hq_zero : q = 0 := le_antisymm (not_lt.mp hq_not_pos) hq_mem.1
          have hμ_eq : μ = xL := by
            rw [hq_zero] at hμeq
            linarith
          rw [hq_zero, hμ_eq]
          ring
        · have hq_one : q = 1 := le_antisymm hq_mem.2 (not_lt.mp hq_not_lt1)
          have hμ_eq : μ = xR := by
            rw [hq_one] at hμeq
            linarith
          rw [hq_one, hμ_eq]
          ring
    have hchord : ∀ p ∈ twoPointFeasibleSet a b μ, twoPointObjective φ p ≤ φ μ := by
      intro p hp
      have hp_le : twoPointObjective φ p ≤ (1 - q) * φ xL + q * φ xR := hmax hp
      linarith [hval_eq_phi]
    obtain ⟨m, c, hmaj, hlineμ⟩ :=
      exists_affineMajorant_through_phi_of_degenerate_twoPointOptimum_interior
        hφ hmean.1 hmean.2 hchord
    have hline : affineFun m c μ = concaveEnvelope a b φ μ := by
      rw [hlineμ, ← hval_eq_phi, hval_eq_env]
    have heq' : d.expect φ = affineFun m c μ := by
      rw [heq, hline]
    refine ⟨m, c, hmaj, ?_, ?_⟩
    · simpa [μ] using supportsOn_contactSet_of_expect_eq_affineFun hsupp hmaj hφ heq'
    · simpa [μ] using heq'

end Econlib.Probability
