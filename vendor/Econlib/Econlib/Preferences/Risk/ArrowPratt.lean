/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Risk.Basic
public import Econlib.Preferences.Utility.Differentiable
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology

/-!
# Arrow–Pratt risk-aversion measures

This file defines the Arrow–Pratt coefficients of absolute and relative risk aversion for a
`TwiceDiffUtility` and characterizes the risk-attitude predicates of `Preferences.Risk.Basic`
through the sign of the absolute coefficient: A twice-differentiable agent is concave (risk averse)
when its absolute coefficient is everywhere nonnegative, strictly concave when it is everywhere
positive, and affine when it vanishes everywhere. The coefficients of the CARA and CRRA families
are computed to be the defining constants.

## Main definitions

* `TwiceDiffUtility.absoluteRiskAversion` — the coefficient `-u''/u'`.
* `TwiceDiffUtility.relativeRiskAversion` — the coefficient `-x·u''/u'`.

## Main statements

* `risk_averse_iff_absoluteRiskAversion_nonneg` — concavity ⇔ nonnegative absolute coefficient.
* `strictly_risk_averse_iff_absoluteRiskAversion_pos` — strict concavity ⇔ positive absolute
  coefficient (under a nonvanishing-`u''` hypothesis).
* `risk_neutral_iff_absoluteRiskAversion_zero` — affinity ⇔ vanishing absolute coefficient.
* `ConstantAbsoluteRiskAversionUtility.absoluteRiskAversion_eq_alpha` and
  `ConstantRelativeRiskAversionUtility.relativeRiskAversion_eq_gamma` — the CARA and CRRA
  coefficients equal `α` and `γ`.

## References

* Pratt, John W. 1964. “Risk Aversion in the Small and in the Large.” *Econometrica* 32 (1/2): 122.
  [https://doi.org/10.2307/1913738](https://doi.org/10.2307/1913738).
* Arrow, Kenneth J. 1971. *Essays in the Theory of Risk-Bearing*. Markham.

## Tags

arrow-pratt, absolute risk aversion, relative risk aversion, cara, crra, concavity
-/

@[expose] public section

namespace Econlib.Preferences

namespace TwiceDiffUtility

variable (f : TwiceDiffUtility)

/-- The **Arrow–Pratt coefficient of absolute risk aversion** `-u''(x)/u'(x)` (Pratt 1964; Arrow
1971). -/
noncomputable def absoluteRiskAversion (x : ℝ) (_ : x ∈ domain f) : ℝ :=
  -(f.u'' x) / (f.u' x)

/-- The **Arrow–Pratt coefficient of relative risk aversion** `-x·u''(x)/u'(x)` (Pratt 1964; Arrow
1971). -/
noncomputable def relativeRiskAversion (x : ℝ) (_ : x ∈ domain f) : ℝ :=
  -(x * f.u'' x) / (f.u' x)

/-! ### Auxiliary lemmas -/

lemma absoluteRiskAversion_nonneg_iff (x : ℝ) (hx : x ∈ f.domain) :
    0 ≤ f.absoluteRiskAversion x hx ↔ f.u'' x ≤ 0 := by
  simp only [absoluteRiskAversion, le_div_iff₀ (f.u'_pos x hx), zero_mul, neg_nonneg]

-- `hxy` fixes the orientation `x < y` for callers; the convex⇒ord-connected argument needs only `≤`
lemma Icc_subset_domain {x y : ℝ} (hx : x ∈ f.domain) (hy : y ∈ f.domain) (_hxy : x < y) :
    Set.Icc x y ⊆ f.domain :=
  f.domain_convex.ordConnected.out hx hy

lemma u'_strict_anti (h : ∀ x ∈ f.domain, f.u'' x < 0) :
    StrictAntiOn f.u' f.domain := by
  refine strictAntiOn_of_deriv_neg f.domain_convex ?_ ?_
  · intro x hx
    exact (f.has_second_deriv x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ f.domain := by
      simpa [f.domain_open.interior_eq] using hx
    rw [(f.has_second_deriv x hx').deriv]
    exact h x hx'

lemma strict_concave_of_strict_anti_u' (h_anti : StrictAntiOn f.u' f.domain) :
    StrictConcaveOn ℝ f.domain f.u := by
  apply StrictAntiOn.strictConcaveOn_of_deriv f.domain_convex f.continuousOn_u
  rw [f.domain_open.interior_eq]
  intro x hx b hb hxb
  rw [(f.has_deriv x hx).deriv, (f.has_deriv b hb).deriv]
  exact h_anti hx hb hxb

lemma u'_eq_of_u''_zero (h0 : ∀ z ∈ f.domain, f.u'' z = 0) {x y : ℝ}
    (hx : x ∈ f.domain) (hy : y ∈ f.domain) : f.u' x = f.u' y := by
  wlog hle : x ≤ y with H
  · exact (H f h0 hy hx (le_of_not_ge hle)).symm
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · have h_sub : Set.Icc x y ⊆ f.domain := f.Icc_subset_domain hx hy hlt
    have h_cont : ContinuousOn f.u' (Set.Icc x y) :=
      fun z hz => (f.has_second_deriv z (h_sub hz)).continuousAt.continuousWithinAt
    have h_deriv : ∀ z ∈ Set.Ioo x y, HasDerivAt f.u' 0 z := by
      intro z hz
      have hz_dom := h_sub (Set.Ioo_subset_Icc_self hz)
      rw [← h0 z hz_dom]
      exact f.has_second_deriv z hz_dom
    rcases exists_hasDerivAt_eq_slope f.u' (fun _ => 0) hlt h_cont h_deriv with ⟨_, _, hc_eq⟩
    linarith [eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt)) |>.mp hc_eq]

/-! ### Main theorem -/

lemma risk_averse_iff_absoluteRiskAversion_nonneg :
    (∀ x (hx : x ∈ f.domain), 0 ≤ f.absoluteRiskAversion x hx) ↔
      ConcaveOn ℝ f.domain f.u := by
  simp_rw [f.absoluteRiskAversion_nonneg_iff]
  constructor
  · intro hu''
    exact concaveOn_of_hasDerivWithinAt2_nonpos f.domain_convex f.continuousOn_u
      (fun x hx => by rw [f.domain_open.interior_eq] at hx ⊢
                      exact (f.has_deriv x hx).hasDerivWithinAt)
      (fun x hx => by rw [f.domain_open.interior_eq] at hx ⊢
                      exact (f.has_second_deriv x hx).hasDerivWithinAt)
      (fun x hx => by rw [f.domain_open.interior_eq] at hx; exact hu'' x hx)
  · intro hconc x hx
    have h_anti_deriv : AntitoneOn (deriv f.u) f.domain :=
      hconc.antitoneOn_deriv (fun y hy => (f.has_deriv y hy).differentiableAt)
    have h_anti_u' : AntitoneOn f.u' f.domain := by
      intro a ha b hb hab
      have := h_anti_deriv ha hb hab
      rwa [(f.has_deriv a ha).deriv, (f.has_deriv b hb).deriv] at this
    have : AccPt x (𝓟 f.domain) := by
      rw [AccPt]
      exact Filter.NeBot.mono (inferInstance : (𝓝[≠] x).NeBot)
        (le_inf le_rfl (le_principal_iff.mpr
          (mem_nhdsWithin_of_mem_nhds (f.domain_open.mem_nhds hx))))
    exact HasDerivWithinAt.nonpos_of_antitoneOn
      this
      (f.has_second_deriv x hx).hasDerivWithinAt
      h_anti_u'

lemma strictly_risk_averse_iff_absoluteRiskAversion_pos
    (h_nz : ∀ x ∈ f.domain, f.u'' x ≠ 0) :
    (∀ x (hx : x ∈ f.domain), 0 < f.absoluteRiskAversion x hx) ↔
      StrictConcaveOn ℝ f.domain f.u := by
  constructor
  · intro h
    have hu'' : ∀ x ∈ f.domain, f.u'' x < 0 := by
      intro x hx
      have h1 := h x hx
      dsimp [TwiceDiffUtility.absoluteRiskAversion] at h1
      have h_num : 0 < -(f.u'' x) := (div_pos_iff_of_pos_right (f.u'_pos x hx)).mp h1
      linarith
    exact f.strict_concave_of_strict_anti_u' (f.u'_strict_anti hu'')
  · intro h x hx
    dsimp [TwiceDiffUtility.absoluteRiskAversion]
    have hpos := f.u'_pos x hx
    have h_le := (risk_averse_iff_absoluteRiskAversion_nonneg f).mpr
    have hu''_le : f.u'' x ≤ 0 :=
      (f.absoluteRiskAversion_nonneg_iff x hx).mp (h_le h.concaveOn x hx)
    have hu''_lt : f.u'' x < 0 := lt_of_le_of_ne hu''_le (h_nz x hx)
    exact div_pos (neg_pos.mpr hu''_lt) hpos

lemma risk_neutral_iff_absoluteRiskAversion_zero :
    (∀ x (hx : x ∈ f.domain),
    f.absoluteRiskAversion x hx = 0) ↔ ∃ a b, ∀ x ∈ f.domain, f.u x = a * x + b := by
  constructor
  · intro h
    have h0 : ∀ x ∈ f.domain, f.u'' x = 0 := by
      intro x hx
      have h1 := h x hx
      dsimp [TwiceDiffUtility.absoluteRiskAversion] at h1
      cases div_eq_zero_iff.mp h1 with
      | inl hp => linarith
      | inr hn => linarith [f.u'_pos x hx]
    rcases Set.eq_empty_or_nonempty f.domain with h_emp | ⟨x0, hx0⟩
    · exact ⟨0, 0, fun x hx => absurd (h_emp ▸ hx) (Set.notMem_empty x)⟩
    · set a := f.u' x0
      have hu' : ∀ x ∈ f.domain, f.u' x = a := fun x hx => f.u'_eq_of_u''_zero h0 hx hx0
      set g := fun x => f.u x - a * x
      have hg_deriv : ∀ x ∈ f.domain, HasDerivAt g 0 x := by
        intro x hx
        have h_sub := (f.has_deriv x hx).sub (hasDerivAt_const_mul a)
        rwa [hu' x hx, sub_self] at h_sub
      -- `g` has zero derivative throughout, so the MVT forces it constant between any two domain
      -- points; prove it once for an ordered pair and apply it in both `≤` orientations.
      have hg_eq : ∀ {p q : ℝ}, p ∈ f.domain → q ∈ f.domain → p < q → g p = g q := by
        intro p q hp hq hpq
        have h_sub : Set.Icc p q ⊆ f.domain := f.Icc_subset_domain hp hq hpq
        have h_cont : ContinuousOn g (Set.Icc p q) :=
          (f.continuousOn_u.mono h_sub).sub (continuous_const.mul continuous_id).continuousOn
        have hd : ∀ z ∈ Set.Ioo p q, HasDerivAt g 0 z :=
          fun z hz => hg_deriv z (h_sub (Set.Ioo_subset_Icc_self hz))
        rcases exists_hasDerivAt_eq_slope g (fun _ => 0) hpq h_cont hd with ⟨c, _, hc_eq⟩
        linarith [eq_div_iff (sub_ne_zero.mpr (ne_of_gt hpq)) |>.mp hc_eq]
      have hg_const : ∀ x ∈ f.domain, g x = g x0 := by
        intro x hx
        rcases lt_trichotomy x0 x with hlt | rfl | hlt
        · exact (hg_eq hx0 hx hlt).symm
        · rfl
        · exact hg_eq hx hx0 hlt
      use a, g x0
      intro x hx
      have : f.u x - a * x = g x0 := hg_const x hx
      linarith
  · intro h_affine
    rcases h_affine with ⟨a, b, hab⟩
    intro x hx
    have hu'_eq : ∀ y ∈ f.domain, f.u' y = a := by
      intro y hy
      have hd2 : HasDerivAt (fun z => a * z + b) a y := (hasDerivAt_const_mul a).add_const b
      have heq : f.u =ᶠ[𝓝 y] (fun z => a * z + b) :=
        Filter.eventuallyEq_of_mem (f.domain_open.mem_nhds hy) hab
      exact (f.has_deriv y hy).unique (hd2.congr_of_eventuallyEq heq)
    have hd_u' : HasDerivAt f.u' (f.u'' x) x := f.has_second_deriv x hx
    have hd_const : HasDerivAt (fun y => a) 0 x := hasDerivAt_const x a
    have heq' : f.u' =ᶠ[𝓝 x] (fun y => a) :=
      Filter.eventuallyEq_of_mem (f.domain_open.mem_nhds hx) hu'_eq
    have h_u'' : f.u'' x = 0 := hd_u'.unique (hd_const.congr_of_eventuallyEq heq')
    dsimp [TwiceDiffUtility.absoluteRiskAversion]
    rw [h_u'', neg_zero, zero_div]

end TwiceDiffUtility

namespace ConstantAbsoluteRiskAversionUtility

/-- The Arrow–Pratt coefficient of absolute risk aversion of a CARA agent is the constant `α` at
every wealth level — the defining feature of the CARA family. -/
lemma absoluteRiskAversion_eq_alpha
    (c : ConstantAbsoluteRiskAversionUtility) (x : ℝ) (hx : x ∈ Set.univ) :
    (c.toTwiceDiffUtility).absoluteRiskAversion x hx = c.α :=
  c.arrow_pratt x

end ConstantAbsoluteRiskAversionUtility

namespace ConstantRelativeRiskAversionUtility

/-- The Arrow–Pratt coefficient of relative risk aversion of a CRRA agent is the constant `γ` at
every positive wealth level — the defining feature of the CRRA family. -/
lemma relativeRiskAversion_eq_gamma
    (c : ConstantRelativeRiskAversionUtility) (x : ℝ) (hx : 0 < x) :
    let tu : TwiceDiffUtility := c.toTwiceDiffUtility;
    tu.relativeRiskAversion x (Set.mem_Ioi.mpr hx) = c.γ := by
  intro tu
  change -(x * c.toTwiceDiffUtility.u'' x) / c.toTwiceDiffUtility.u' x = c.γ
  have h_u' : c.toTwiceDiffUtility.u' x = x ^ (-c.γ) := dif_pos hx
  have h_u'' : c.toTwiceDiffUtility.u'' x = -c.γ * x ^ (-c.γ - 1) := dif_pos hx
  rw [h_u', h_u'']
  exact c.relativeRiskAversion x hx

end ConstantRelativeRiskAversionUtility

end Econlib.Preferences
