/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Expect
public import Econlib.Probability.FinDist.Map

/-!
# Variance of finite distributions: Extended API and the law of total variance

This file extends the basic variance definition in `FinDist/Expect.lean` with the centered
second-moment form, affine identities, Popoviciu's inequality, and the law of total variance for
the conditional mean of `f` given a coarsening `π`.

## Main definitions

* `FinDist.condMean` — the conditional mean of `f` given the fibers of `π : α → β`.

## Main statements

* `FinDist.variance_eq_expect_sub_sq` — the centered form `Var(f) = E[(f - E f)²]`.
* `FinDist.expect_sub_sq_eq_variance_add_bias_sq` — Pythagorean identity
  `E[(f - c)²] = Var f + (E f - c)²`.
* `FinDist.variance_le_expect_sub_sq` — variance is the minimal mean-squared deviation over the
  choice of center.
* `FinDist.variance_le_quarter_diam_sq` — Popoviciu's inequality: `f s ∈ [a, b]` implies
  `Var f ≤ ((b - a) / 2)²`.
* `FinDist.variance_eq_zero_iff` — variance vanishes iff `f` is constant on the support of `d`.
* `FinDist.variance_add_const`, `FinDist.variance_smul`, `FinDist.variance_affine` — affine
  invariance and homogeneity.
* `FinDist.expect_condMean_map` — the tower rule.
* `FinDist.variance_decomposition` — law of total variance, `Var(f) = within + between`.
* `FinDist.variance_map_le` — `Var(E[f|π]) ≤ Var(f)`.

## Notes

The pushforward `FinDist.map` and its change-of-variables rule `FinDist.expect_map` live in
`FinDist/Map.lean`.

## Tags

probability, finite distributions, variance, law of total variance, popoviciu
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α β : Type*} [Fintype α] [DecidableEq α]

/-! ## Centered form. -/

/-- **Pythagorean identity.** The mean-squared deviation about any point `c` decomposes as the
variance plus the squared bias from the mean. -/
lemma expect_sub_sq_eq_variance_add_bias_sq (d : FinDist α) (f : α → ℝ) (c : ℝ) :
    d.expect (fun a => (f a - c) ^ 2) = d.variance f + (d.expect f - c) ^ 2 := by
  unfold variance expect
  set μ := ∑ a, d a * f a with hμ
  have ha : ∀ a, d a * (f a - c) ^ 2 =
      d a * (f a) ^ 2 - 2 * c * (d a * f a) + c ^ 2 * d a := fun _ => by ring
  simp_rw [ha]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show ∑ a, 2 * c * (d a * f a) = 2 * c * ∑ a, d a * f a from
    (Finset.mul_sum _ _ _).symm]
  rw [show ∑ a, c ^ 2 * d a = c ^ 2 * ∑ a, d a from
    (Finset.mul_sum _ _ _).symm]
  rw [d.sum_one, ← hμ]
  ring

/-- Variance equals the central second moment `E[(f - E f)²]`. -/
lemma variance_eq_expect_sub_sq (d : FinDist α) (f : α → ℝ) :
    d.variance f = d.expect (fun a => (f a - d.expect f) ^ 2) := by
  -- The Pythagorean identity at the mean (`c = E f`) has zero bias term.
  rw [expect_sub_sq_eq_variance_add_bias_sq, sub_self]
  ring

/-! ## Affine identities for `expect`. -/

/-- Adding a constant to the integrand shifts the expectation by that constant. -/
lemma expect_add_const (d : FinDist α) (f : α → ℝ) (c : ℝ) :
    d.expect (fun a => f a + c) = d.expect f + c := by
  have heq : (fun a : α => f a + c) = f + (fun _ => c) := by
    funext a; rfl
  rw [heq, d.expect_add, d.expect_const]

/-- Scaling the integrand scales the expectation. -/
lemma expect_smul_left (d : FinDist α) (c : ℝ) (f : α → ℝ) :
    d.expect (fun a => c * f a) = c * d.expect f := by
  have heq : (fun a : α => c * f a) = c • f := by
    funext a; simp [smul_eq_mul]
  rw [heq, d.expect_smul]

/-! ## Constants, pure distributions, and affine invariance of variance. -/

/-- A constant function has zero variance. -/
@[simp] lemma variance_const (d : FinDist α) (c : ℝ) :
    d.variance (fun _ : α => c) = 0 := by
  unfold variance
  change d.expect (fun _ : α => c ^ 2) - d.expect (fun _ : α => c) ^ 2 = 0
  rw [d.expect_const, d.expect_const]
  ring

/-- A point mass has zero variance. -/
@[simp] lemma variance_pure (a : α) (f : α → ℝ) :
    (FinDist.pure a).variance f = 0 := by
  unfold variance
  rw [expect_pure, expect_pure]
  ring

/-- Variance is invariant under adding a constant to the integrand. -/
@[simp] lemma variance_add_const (d : FinDist α) (f : α → ℝ) (c : ℝ) :
    d.variance (fun a => f a + c) = d.variance f := by
  rw [variance_eq_expect_sub_sq d (fun a => f a + c),
    variance_eq_expect_sub_sq d f, expect_add_const]
  congr 1
  funext a
  ring

/-- Scaling the integrand by `c` scales the variance by `c²`. -/
@[simp] lemma variance_smul (d : FinDist α) (c : ℝ) (f : α → ℝ) :
    d.variance (fun a => c * f a) = c ^ 2 * d.variance f := by
  rw [variance_eq_expect_sub_sq d (fun a => c * f a),
    variance_eq_expect_sub_sq d f, expect_smul_left]
  have heq : (fun a : α => (c * f a - c * d.expect f) ^ 2) =
      (fun a : α => c ^ 2 * (f a - d.expect f) ^ 2) := by
    funext a; ring
  rw [heq, ← expect_smul_left]

/-- Variance under an affine transformation `a * f + b` scales by `a²`. -/
lemma variance_affine (d : FinDist α) (a b : ℝ) (f : α → ℝ) :
    d.variance (fun s => a * f s + b) = a ^ 2 * d.variance f := by
  rw [variance_add_const, variance_smul]

/-! ## Pythagorean identity and consequences. -/

/-- Variance is the minimal mean-squared deviation: Any choice of center `c` yields an upper
bound. -/
lemma variance_le_expect_sub_sq (d : FinDist α) (f : α → ℝ) (c : ℝ) :
    d.variance f ≤ d.expect (fun a => (f a - c) ^ 2) := by
  rw [expect_sub_sq_eq_variance_add_bias_sq]
  have hbias : 0 ≤ (d.expect f - c) ^ 2 := sq_nonneg _
  linarith

/-- **Popoviciu's inequality.** If `f` takes values in `[a, b]` then `Var f ≤ ((b - a) / 2)²`. -/
lemma variance_le_quarter_diam_sq (d : FinDist α) (f : α → ℝ)
    {a b : ℝ} (hf : ∀ s, f s ∈ Set.Icc a b) :
    d.variance f ≤ ((b - a) / 2) ^ 2 := by
  -- Centre at the midpoint `(a + b) / 2`; then `|f s - midpoint| ≤ (b - a)/2`.
  have hbound : ∀ s, (f s - (a + b) / 2) ^ 2 ≤ ((b - a) / 2) ^ 2 := by
    intro s
    have hf_s := hf s
    rw [Set.mem_Icc] at hf_s
    have habs : |f s - (a + b) / 2| ≤ (b - a) / 2 := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩ <;> linarith [hf_s.1, hf_s.2]
    exact sq_le_sq' (neg_le_of_abs_le habs) (le_of_abs_le habs)
  calc d.variance f
      ≤ d.expect (fun s => (f s - (a + b) / 2) ^ 2) :=
          variance_le_expect_sub_sq d f _
    _ ≤ d.expect (fun _ : α => ((b - a) / 2) ^ 2) := d.expect_mono _ _ hbound
    _ = ((b - a) / 2) ^ 2 := d.expect_const _

/-- Variance vanishes iff `f` is constant on the support of `d`. -/
lemma variance_eq_zero_iff (d : FinDist α) (f : α → ℝ) :
    d.variance f = 0 ↔ ∀ a, 0 < d a → f a = d.expect f := by
  rw [variance_eq_expect_sub_sq]
  -- Convert the outer expect to a Finset.sum without unfolding the inner d.expect f.
  change ∑ a, d a * (f a - d.expect f) ^ 2 = 0 ↔ _
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => mul_nonneg (d.nonneg a) (sq_nonneg _))]
  refine ⟨fun h a hpos => ?_, fun h a _ => ?_⟩
  · have hzero := h a (Finset.mem_univ a)
    rcases mul_eq_zero.mp hzero with hda | hsq
    · exact absurd hda (ne_of_gt hpos)
    · linarith [sq_eq_zero_iff.mp hsq]
  · by_cases hpos : 0 < d a
    · rw [h a hpos]; ring
    · have hda : d a = 0 := le_antisymm (not_lt.mp hpos) (d.nonneg a)
      rw [hda]; ring

/-! ## Conditional mean and the law of total variance. -/

variable [Fintype β] [DecidableEq β]

/-- Conditional mean of `f` given the fiber of `π`.

When the fiber `π⁻¹{b}` has zero mass the numerator also vanishes, so the junk value `0 / 0 = 0` is
consistent with the tower rule below. -/
noncomputable def condMean (d : FinDist α) (π : α → β) (f : α → ℝ) (b : β) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * f a) /
    (∑ a ∈ Finset.univ.filter (fun a => π a = b), d a)

omit [Fintype β] in
/-- The numerator vanishes whenever the fiber mass vanishes. -/
private lemma fibreNumerator_eq_zero_of_mass_zero
    (d : FinDist α) (π : α → β) (f : α → ℝ) (b : β)
    (hmass : ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a = 0) :
    ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * f a = 0 := by
  have hzero : ∀ a ∈ Finset.univ.filter (fun a => π a = b), d a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun a _ => d.nonneg a).mp hmass
  apply Finset.sum_eq_zero
  intro a ha
  rw [hzero a ha, zero_mul]

/-- Per-fiber identity: `mass(b) * condMean(b) = ∑ d a · f a` over the fiber. -/
private lemma mass_mul_condMean (d : FinDist α) (π : α → β) (f : α → ℝ) (b : β) :
    (d.map π) b * condMean d π f b
      = ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * f a := by
  rw [map_apply]
  unfold condMean
  set mass := ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a with hmass_def
  set num := ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * f a with hnum_def
  by_cases hmass_zero : mass = 0
  · rw [hmass_zero, zero_mul]
    rw [hnum_def]
    exact (fibreNumerator_eq_zero_of_mass_zero d π f b
      (by rw [← hmass_def]; exact hmass_zero)).symm
  · field_simp

/-- **Tower rule.** Expectation of the conditional mean under the pushforward recovers the original
expectation. -/
lemma expect_condMean_map (d : FinDist α) (π : α → β) (f : α → ℝ) :
    (d.map π).expect (condMean d π f) = d.expect f := by
  unfold expect
  simp_rw [mass_mul_condMean d π f]
  rw [Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset β)) (g := π) (f := fun a => d a * f a)
    (fun _ _ => Finset.mem_univ _)]

/-- **Law of total variance** (decomposition form). The total variance splits into the within-fiber
variance plus the between-fiber variance:

`Var(f) = E_d[(f - condMean(π·))²] + Var_{π·d}(condMean)`. -/
lemma variance_decomposition (d : FinDist α) (π : α → β) (f : α → ℝ) :
    d.variance f
      = d.expect (fun a => (f a - condMean d π f (π a)) ^ 2)
        + (d.map π).variance (condMean d π f) := by
  set μ := d.expect f with hμ_def
  -- Fibrewise: on each fibre {π a = b}, the centred conditional sum vanishes.
  have h_fibre_centred : ∀ b : β,
      ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * (f a - condMean d π f b) = 0 := by
    intro b
    set mass := ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a with hmass_def
    set num := ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * f a with hnum_def
    have hexpand_fibre : ∀ a, d a * (f a - condMean d π f b)
        = d a * f a - condMean d π f b * d a := fun _ => by ring
    have hsplit : ∑ a ∈ Finset.univ.filter (fun a => π a = b), d a * (f a - condMean d π f b)
        = num - condMean d π f b * mass := by
      simp_rw [hexpand_fibre]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsplit]
    by_cases hmass_zero : mass = 0
    · have hnum_zero : num = 0 := by
        rw [hnum_def]
        exact fibreNumerator_eq_zero_of_mass_zero d π f b
          (by rw [← hmass_def]; exact hmass_zero)
      rw [hmass_zero, mul_zero, sub_zero, hnum_zero]
    · have hcm_eq : condMean d π f b * mass = num := by
        unfold condMean
        rw [← hnum_def, ← hmass_def, div_mul_cancel₀ _ hmass_zero]
      rw [hcm_eq, sub_self]
  rw [variance_eq_expect_sub_sq, variance_eq_expect_sub_sq]
  rw [expect_condMean_map d π f, ← hμ_def]
  -- Convert outer expects to Finset sums without disturbing the bound `μ`.
  change ∑ a, d a * (f a - μ) ^ 2
    = (∑ a, d a * (f a - condMean d π f (π a)) ^ 2)
      + ∑ b, (d.map π) b * (condMean d π f b - μ) ^ 2
  -- Expand the LHS into within + cross + between (over a).
  have h_expand : ∀ a, d a * (f a - μ) ^ 2
      = d a * (f a - condMean d π f (π a)) ^ 2
        + 2 * (d a * (f a - condMean d π f (π a))) * (condMean d π f (π a) - μ)
        + d a * (condMean d π f (π a) - μ) ^ 2 := fun a => by ring
  simp_rw [h_expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Cross term vanishes fibrewise.
  have h_cross_zero :
      ∑ a, 2 * (d a * (f a - condMean d π f (π a))) * (condMean d π f (π a) - μ) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (g := π)
      (f := fun a => 2 * (d a * (f a - condMean d π f (π a))) *
        (condMean d π f (π a) - μ)) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_eq_zero
    intro b _
    have hfibre_form : ∑ a ∈ Finset.univ.filter (fun a => π a = b),
          2 * (d a * (f a - condMean d π f (π a))) * (condMean d π f (π a) - μ)
        = (2 * (condMean d π f b - μ)) *
            ∑ a ∈ Finset.univ.filter (fun a => π a = b),
              d a * (f a - condMean d π f b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_filter] at ha
      rw [ha.2]
      ring
    rw [hfibre_form, h_fibre_centred b, mul_zero]
  rw [h_cross_zero, add_zero]
  -- Between term: collapse `∑_b mass(b) · X(b)` to `∑_a d a · X(π a)` via fibrewise reorg.
  congr 1
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset β)) (g := π)
    (f := fun a => d a * (condMean d π f (π a) - μ) ^ 2)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_filter] at ha
  rw [ha.2]

/-- **Law of total variance** (inequality form). The variance of the conditional mean under the
pushforward is bounded above by the original variance. -/
lemma variance_map_le (d : FinDist α) (π : α → β) (f : α → ℝ) :
    (d.map π).variance (condMean d π f) ≤ d.variance f := by
  rw [variance_decomposition d π f]
  have hwithin : 0 ≤ d.expect (fun a => (f a - condMean d π f (π a)) ^ 2) :=
    d.expect_nonneg _ fun _ => sq_nonneg _
  linarith

end FinDist
end Econlib.Probability
