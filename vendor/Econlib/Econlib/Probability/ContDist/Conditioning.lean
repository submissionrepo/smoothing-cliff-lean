/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.CDF

/-!
# Conditioning a `ContDist`: Bayesian updating, conditional expectation, truncation

This file collects the operations that condition a continuous distribution on information.
`ContDist.posterior` reweights the prior density by a likelihood and renormalizes (Bayes' rule);
`ContDist.conditionalExpect` computes `E[g(X) | X ∈ A]`; and `ContDist.truncate` restricts a
distribution to an interval and renormalizes.

The core analytic result is that the conditional mean of a strictly increasing function on a
shrinking interval is itself strictly increasing: `u ↦ E[g(X) | X ∈ [u, b]]` increases when `g` is
strictly monotone and the density is positive on `[a, b]`.

## Main definitions

* `ContDist.posteriorOfLikelihoodOrPrior` — totalized Bayesian update from a bare likelihood value
  `ℓ : ℝ → ℝ` (returns the prior on zero evidence).
* `ContDist.posteriorOrPrior` — totalized Bayesian update from a signal kernel (returns the prior
  on zero evidence).
* `ContDist.posteriorOfLikelihood` — Bayesian update from a bare likelihood value `ℓ : ℝ → ℝ`,
  gated on positive evidence.
* `ContDist.posterior` — Bayesian update from a signal kernel `likelihood : ℝ → ℝ → ℝ`, gated on
  positive evidence.
* `ContDist.conditionalExpectOrZero` — totalized conditional expectation `E[g | X ∈ A]` (returns
  `0` on a zero-probability event).
* `ContDist.conditionalExpect` — conditional expectation `E[g | X ∈ A]`, gated on positive event
  probability.
* `ContDist.truncate` — truncation of a distribution to an interval `[a, b]`.

## Main statements

* `ContDist.conditionalExpect_strict_mono` — strict conditional domination.
* `conditionalExpect_strictMono_right`, `conditionalExpect_strictMono_left` — the conditional mean
  of a strictly increasing function is strictly increasing in the interval endpoint.

## Notes

The names `posteriorOfLikelihood`, `posterior`, and `conditionalExpect` carry a positive-evidence
hypothesis (`0 < ∫ θ, prior.density θ * ℓ θ` for the posteriors, `0 < ∫ x in A, d.density x` for
the conditional expectation), under which the characterization lemmas
`posteriorOfLikelihood_density`, `posterior_density`, and `conditionalExpect_eq` give the Bayes /
conditional-mean formulas. The totalized conventions
`posteriorOfLikelihoodOrPrior`/`posteriorOrPrior` return the prior on zero evidence, and
`conditionalExpectOrZero` returns `0` on a zero-probability event; a value read under an
`…OrPrior`/`…OrZero` name must not be interpreted as Bayesian without first checking that the
evidence is positive.

## Tags

bayesian updating, posterior, conditional expectation, truncation
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

namespace ContDist

/-! ### Bayesian updating -/

/-- Totalized posterior density from a bare per-state likelihood value `ℓ : ℝ → ℝ`.

This is the carrier-independent Bayesian primitive: Reweight the prior density by `ℓ` and
renormalize. If the normalizer `∫ θ, prior.density θ * ℓ θ` is not positive, the posterior is
defined to be the prior, keeping the result total. The positivity-gated object is
`ContDist.posteriorOfLikelihood`; a value read under this name on zero evidence is the prior, not a
Bayesian posterior. -/
noncomputable def posteriorOfLikelihoodOrPrior
    (prior : ContDist) (ℓ : ℝ → ℝ)
    (h_nn : ∀ θ, 0 ≤ ℓ θ)
    (h_int : Integrable (fun θ => prior.density θ * ℓ θ)) : ContDist :=
  let denom := ∫ θ, prior.density θ * ℓ θ
  if h : 0 < denom then
    { density := fun θ => (prior.density θ * ℓ θ) / denom,
      nonneg := fun θ => div_nonneg (mul_nonneg (prior.nonneg θ) (h_nn θ)) (le_of_lt h),
      integrable := h_int.div_const denom,
      integral_one := by
        show ∫ θ, prior.density θ * ℓ θ / denom = 1
        rw [integral_div, div_self (ne_of_gt h)] }
  else
    prior

/-- Totalized posterior density via Bayes' rule, continuous case. `likelihood θ x` is the density
of signal `x` given state `θ`.

The effective likelihood value of state `θ` is `likelihood θ signal`; this is a thin wrapper over
`posteriorOfLikelihoodOrPrior`. Returns the prior on zero evidence; the positivity-gated object is
`ContDist.posterior`. -/
noncomputable def posteriorOrPrior
  (prior : ContDist) (likelihood : ℝ → ℝ → ℝ) (signal : ℝ)
  (h_lk_nn : ∀ θ, 0 ≤ likelihood θ signal)
  (h_lk_int : Integrable (fun θ => prior.density θ * likelihood θ signal)) : ContDist :=
  prior.posteriorOfLikelihoodOrPrior (fun θ => likelihood θ signal) h_lk_nn h_lk_int

/-- Posterior density from a bare per-state likelihood value `ℓ : ℝ → ℝ`, gated on positive
evidence.

The hypothesis `h_pos : 0 < ∫ θ, prior.density θ * ℓ θ` fixes the regime in which the Bayes formula
(`posteriorOfLikelihood_density`) is valid. On the value level this agrees with
`posteriorOfLikelihoodOrPrior` (see the bridge lemma `posteriorOfLikelihood_eq_orPrior`). -/
noncomputable def posteriorOfLikelihood
    (prior : ContDist) (ℓ : ℝ → ℝ)
    (h_nn : ∀ θ, 0 ≤ ℓ θ)
    (h_int : Integrable (fun θ => prior.density θ * ℓ θ))
    -- `h_pos` gates the positive-evidence regime; load-bearing for `posteriorOfLikelihood_density`.
    (_h_pos : 0 < ∫ θ, prior.density θ * ℓ θ) : ContDist :=
  prior.posteriorOfLikelihoodOrPrior ℓ h_nn h_int

/-- Posterior density via Bayes' rule, continuous case, gated on positive evidence.

The hypothesis `h_pos : 0 < ∫ θ, prior.density θ * likelihood θ signal` fixes the regime in which
the signal has positive marginal density and the Bayes formula (`posterior_density`) is valid. On
the value level this agrees with `posteriorOrPrior` (see `posterior_eq_orPrior`). -/
noncomputable def posterior
  (prior : ContDist) (likelihood : ℝ → ℝ → ℝ) (signal : ℝ)
  (h_lk_nn : ∀ θ, 0 ≤ likelihood θ signal)
  (h_lk_int : Integrable (fun θ => prior.density θ * likelihood θ signal))
  -- `h_pos` gates the positive-evidence regime; load-bearing for `posterior_density`.
  (_h_pos : 0 < ∫ θ, prior.density θ * likelihood θ signal) : ContDist :=
  prior.posteriorOrPrior likelihood signal h_lk_nn h_lk_int

/-- The positivity-gated posterior agrees on the value level with the totalized `…OrPrior`
convention; the only difference is the positivity gate. Applied explicitly (not `@[simp]`) so that
proofs working on `posterior` are not silently rewritten to the totalized form. -/
lemma posteriorOfLikelihood_eq_orPrior (prior : ContDist) (ℓ : ℝ → ℝ)
    (h_nn : ∀ θ, 0 ≤ ℓ θ) (h_int : Integrable (fun θ => prior.density θ * ℓ θ))
    (h_pos : 0 < ∫ θ, prior.density θ * ℓ θ) :
    prior.posteriorOfLikelihood ℓ h_nn h_int h_pos =
      prior.posteriorOfLikelihoodOrPrior ℓ h_nn h_int := rfl

/-- The positivity-gated posterior agrees on the value level with the totalized `…OrPrior`
convention; the only difference is the positivity gate. Applied explicitly (not `@[simp]`) so that
proofs working on `posterior` are not silently rewritten to the totalized form. -/
lemma posterior_eq_orPrior (prior : ContDist) (lk : ℝ → ℝ → ℝ) (signal : ℝ)
    (h_lk_nn : ∀ θ, 0 ≤ lk θ signal)
    (h_lk_int : Integrable (fun θ => prior.density θ * lk θ signal))
    (h_pos : 0 < ∫ θ, prior.density θ * lk θ signal) :
    prior.posterior lk signal h_lk_nn h_lk_int h_pos =
      prior.posteriorOrPrior lk signal h_lk_nn h_lk_int := rfl

/-- Bayes' rule for the positivity-gated posterior: Its density at `θ` is the prior density times
the likelihood, divided by the normalizer. -/
lemma posteriorOfLikelihood_density (prior : ContDist) (ℓ : ℝ → ℝ) (θ : ℝ)
    (h_nn : ∀ θ, 0 ≤ ℓ θ)
    (h_int : Integrable (fun θ => prior.density θ * ℓ θ))
    (h_denom : 0 < ∫ θ', prior.density θ' * ℓ θ') :
    (prior.posteriorOfLikelihood ℓ h_nn h_int h_denom).density θ =
      (prior.density θ * ℓ θ) / ∫ θ', prior.density θ' * ℓ θ' := by
  unfold posteriorOfLikelihood posteriorOfLikelihoodOrPrior; rw [dif_pos h_denom]

/-- Bayes' rule for the positivity-gated posterior from a signal kernel: Its density at `θ` is the
prior density times the likelihood `lk θ signal`, divided by the marginal density of the signal. -/
lemma posterior_density (prior : ContDist) (lk : ℝ → ℝ → ℝ) (signal θ : ℝ)
    (h_lk_nn : ∀ θ, 0 ≤ lk θ signal)
    (h_lk_int : Integrable (fun θ => prior.density θ * lk θ signal))
    (h_denom : 0 < ∫ θ', prior.density θ' * lk θ' signal) :
    (prior.posterior lk signal h_lk_nn h_lk_int h_denom).density θ =
      (prior.density θ * lk θ signal) / ∫ θ', prior.density θ' * lk θ' signal := by
  unfold posterior posteriorOrPrior
  exact posteriorOfLikelihood_density prior _ θ h_lk_nn h_lk_int h_denom

/-- The posterior density integrates to one. -/
lemma posterior_is_dist (prior : ContDist) (lk : ℝ → ℝ → ℝ) (signal : ℝ)
    (h_lk_nn : ∀ θ, 0 ≤ lk θ signal)
    (h_lk_int : Integrable (fun θ => prior.density θ * lk θ signal))
    (h_pos : 0 < ∫ θ, prior.density θ * lk θ signal) :
    ∫ θ, (prior.posterior lk signal h_lk_nn h_lk_int h_pos).density θ = 1 :=
  (prior.posterior lk signal h_lk_nn h_lk_int h_pos).integral_one

/-! ### Conditional expectation -/

/-- Totalized conditional expectation of `g` given event `A` under distribution `d`. Returns 0 when
`A` has zero probability. The positivity-gated object is `ContDist.conditionalExpect`; a value read
under this name on a zero-probability event is `0`, not a conditional mean. -/
noncomputable def conditionalExpectOrZero
    (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ) : ℝ :=
  if _ : 0 < ∫ x in A, d.density x
  then (∫ x in A, d.density x * g x) / (∫ x in A, d.density x)
  else 0

/-- Conditional expectation of `g` given event `A` under distribution `d`, gated on positive event
probability.

The hypothesis `h_pos : 0 < ∫ x in A, d.density x` fixes the regime in which the conditional-mean
formula (`conditionalExpect_eq`) is valid. On the value level this agrees with
`conditionalExpectOrZero` (see the bridge lemma `conditionalExpect_eq_orZero`); the hypothesis
makes the value definable only on a positive-probability event. -/
noncomputable def conditionalExpect
    (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ)
    -- `h_pos` gates the positive-probability regime; load-bearing for `conditionalExpect_eq`.
    (_h_pos : 0 < ∫ x in A, d.density x) : ℝ :=
  d.conditionalExpectOrZero g A

/-- The positivity-gated conditional expectation agrees on the value level with the totalized
`…OrZero` convention; the only difference is the positivity gate. Not marked `@[simp]`: The gated
and totalized forms are needed in different positions (point statements vs. interval-family
statements), so the rewrite is applied explicitly where the regime is known. -/
lemma conditionalExpect_eq_orZero (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ)
    (h_pos : 0 < ∫ x in A, d.density x) :
    d.conditionalExpect g A h_pos = d.conditionalExpectOrZero g A := rfl

/-- Unfold conditional expectation when the event has positive probability. -/
lemma conditionalExpect_eq (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ)
    (h_pos : 0 < ∫ x in A, d.density x) :
    d.conditionalExpect g A h_pos =
      (∫ x in A, d.density x * g x) / (∫ x in A, d.density x) :=
  dif_pos h_pos

/-- When `A` has zero probability, the totalized conditional expectation returns 0. -/
lemma conditionalExpectOrZero_zero (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ)
    (h_zero : ¬(0 < ∫ x in A, d.density x)) :
    d.conditionalExpectOrZero g A = 0 :=
  dif_neg h_zero

/-- Unfold the totalized conditional expectation when the event has positive probability — on that
regime it coincides with the conditional mean. -/
lemma conditionalExpectOrZero_eq_of_pos (d : ContDist) (g : ℝ → ℝ) (A : Set ℝ)
    (h_pos : 0 < ∫ x in A, d.density x) :
    d.conditionalExpectOrZero g A =
      (∫ x in A, d.density x * g x) / (∫ x in A, d.density x) :=
  dif_pos h_pos

/-- Conditional expectation of a constant. -/
lemma conditionalExpect_const (d : ContDist) (c : ℝ) (A : Set ℝ)
    (h_pos : 0 < ∫ x in A, d.density x) :
    d.conditionalExpect (fun _ => c) A h_pos = c := by
  simp only [conditionalExpect_eq _ _ _ h_pos]
  rw [integral_mul_const, mul_comm, mul_div_assoc, div_self (ne_of_gt h_pos), mul_one]

/-- Conditional expectation is monotone. -/
lemma conditionalExpect_mono (d : ContDist) (g h : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (h_pos : 0 < ∫ x in A, d.density x)
    (hgh : ∀ x ∈ A, g x ≤ h x)
    (hg_int : IntegrableOn (fun x => d.density x * g x) A)
    (hh_int : IntegrableOn (fun x => d.density x * h x) A) :
    d.conditionalExpect g A h_pos ≤ d.conditionalExpect h A h_pos := by
  simp only [conditionalExpect_eq _ _ _ h_pos]
  apply div_le_div_of_nonneg_right _ (le_of_lt h_pos)
  exact setIntegral_mono_on hg_int hh_int hA
    (fun x hx => mul_le_mul_of_nonneg_left (hgh x hx) (d.nonneg x))

/-- The conditional mean of a monotone function on `[u, b]` is at least `g(u)`. -/
lemma conditionalExpect_ge_left (d : ContDist) (g : ℝ → ℝ) (u b : ℝ)
    (h_pos : 0 < ∫ x in Icc u b, d.density x)
    (hg_mono : MonotoneOn g (Icc u b))
    (hg_int : IntegrableOn (fun x => d.density x * g x) (Icc u b))
    (hub : u ≤ b) :
    g u ≤ d.conditionalExpect g (Icc u b) h_pos := by
  rw [conditionalExpect_eq _ _ _ h_pos, le_div_iff₀ h_pos]
  -- g(u) * ∫ f ≤ ∫ f·g because g(u) ≤ g(x) for x ∈ [u, b]
  have h_const_int : IntegrableOn (fun x => d.density x * g u) (Icc u b) :=
    d.integrable.integrableOn.mul_const _
  calc g u * ∫ x in Icc u b, d.density x
      = ∫ x in Icc u b, g u * d.density x := by
        exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x in Icc u b, d.density x * g u := by
        congr 1; ext x; ring
    _ ≤ ∫ x in Icc u b, d.density x * g x :=
        setIntegral_mono_on h_const_int hg_int measurableSet_Icc
          (fun x hx => mul_le_mul_of_nonneg_left
            (hg_mono (left_mem_Icc.mpr hub) hx hx.1) (d.nonneg x))

/-- The conditional mean of a monotone function on `[a, b]` is at most `g(b)`. -/
lemma conditionalExpect_le_right (d : ContDist) (g : ℝ → ℝ) (a b : ℝ)
    (h_pos : 0 < ∫ x in Icc a b, d.density x)
    (hg_mono : MonotoneOn g (Icc a b))
    (hg_int : IntegrableOn (fun x => d.density x * g x) (Icc a b))
    (hab : a ≤ b) :
    d.conditionalExpect g (Icc a b) h_pos ≤ g b := by
  have h_const_int : IntegrableOn (fun x => d.density x * g b) (Icc a b) :=
    d.integrable.integrableOn.mul_const _
  have hmono :
      d.conditionalExpect g (Icc a b) h_pos ≤ d.conditionalExpect (fun _ => g b) (Icc a b) h_pos :=
    d.conditionalExpect_mono g (fun _ => g b) (Icc a b) measurableSet_Icc h_pos
      (fun x hx => hg_mono hx (right_mem_Icc.mpr hab) hx.2)
      hg_int h_const_int
  rwa [d.conditionalExpect_const (g b) (Icc a b) h_pos] at hmono

/-- The conditional mean of the identity on `[a, b]` lies in `[a, b]`. -/
lemma conditionalExpect_id_mem_Icc (d : ContDist) (a b : ℝ)
    (h_pos : 0 < ∫ x in Icc a b, d.density x)
    (hid_int : IntegrableOn (fun x => d.density x * x) (Icc a b))
    (hab : a ≤ b) :
    d.conditionalExpect id (Icc a b) h_pos ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · simpa using d.conditionalExpect_ge_left id a b h_pos monotoneOn_id hid_int hab
  · simpa using d.conditionalExpect_le_right id a b h_pos monotoneOn_id hid_int hab

/-- Strict conditional expectation domination: If `g ≥ f` pointwise on `A` with `g > f` on a
positive-measure subset `B ⊆ A`, then `E[g|A] > E[f|A]`. -/
theorem conditionalExpect_strict_mono
    (d : ContDist) (f g : ℝ → ℝ) (A : Set ℝ)
    (hA : MeasurableSet A)
    (h_pos : 0 < ∫ x in A, d.density x)
    (hfg : ∀ x ∈ A, f x ≤ g x)
    (hf_int : IntegrableOn (fun x => d.density x * f x) A)
    (hg_int : IntegrableOn (fun x => d.density x * g x) A)
    (B : Set ℝ) (hBA : B ⊆ A) (hB : MeasurableSet B)
    (hB_pos : 0 < ∫ x in B, d.density x)
    (hfg_strict : ∀ x ∈ B, f x < g x) :
    d.conditionalExpect f A h_pos < d.conditionalExpect g A h_pos := by
  simp only [conditionalExpect_eq _ _ _ h_pos]
  rw [div_lt_div_iff₀ h_pos h_pos]
  -- Reduce to: ∫_A d·f < ∫_A d·g
  have h_diff_int : IntegrableOn (fun x => d.density x * (g x - f x)) A := by
    simp_rw [mul_sub]; exact hg_int.sub hf_int
  have h_eq : (∫ x in A, d.density x * g x) - (∫ x in A, d.density x * f x) =
      ∫ x in A, d.density x * (g x - f x) := by
    simp_rw [mul_sub]; rw [integral_sub hg_int hf_int]
  suffices h : 0 < ∫ x in A, d.density x * (g x - f x) by nlinarith [h_eq]
  -- Strategy: ∫_A d·(g-f) = ∫_B d·(g-f) + ∫_{A\B} d·(g-f), both nonneg, first strictly pos
  have hB_int : IntegrableOn (fun x => d.density x * (g x - f x)) B :=
    h_diff_int.mono_set hBA
  have hAB_int : IntegrableOn (fun x => d.density x * (g x - f x)) (A \ B) :=
    h_diff_int.mono_set diff_subset
  -- ∫_{A\B} d·(g-f) ≥ 0
  have hAB_nn : 0 ≤ ∫ x in A \ B, d.density x * (g x - f x) :=
    setIntegral_nonneg (hA.diff hB) fun x hx =>
      mul_nonneg (d.nonneg x) (sub_nonneg.mpr (hfg x (diff_subset hx)))
  -- ∫_B d·(g-f) > 0 via setIntegral_pos_iff_support_of_nonneg_ae
  have hB_pos' : 0 < ∫ x in B, d.density x * (g x - f x) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (by filter_upwards [ae_restrict_mem hB] with x hx
          exact mul_nonneg (d.nonneg x) (sub_nonneg.mpr (le_of_lt (hfg_strict x hx))))
      hB_int]
    -- Need: 0 < volume (support(d·(g-f)) ∩ B)
    -- support(d·(g-f)) ⊇ support(d) ∩ B (where d > 0 and g-f > 0)
    -- And volume(support(d) ∩ B) > 0 because ∫_B d > 0
    have hd_supp : 0 < volume (Function.support d.density ∩ B) := by
      rw [← setIntegral_pos_iff_support_of_nonneg_ae
        (by filter_upwards [ae_restrict_mem hB] with x _ ; exact d.nonneg x)
        d.integrable.integrableOn]
      exact hB_pos
    apply lt_of_lt_of_le hd_supp (measure_mono _)
    intro x ⟨hx_supp, hx_B⟩
    constructor
    · rw [Function.mem_support] at hx_supp ⊢
      exact ne_of_gt (mul_pos
        (lt_of_le_of_ne (d.nonneg x) (Ne.symm hx_supp))
        (sub_pos.mpr (hfg_strict x hx_B)))
    · exact hx_B
  -- Combine: ∫_A = ∫_B + ∫_{A\B}
  have h_split : ∫ x in A, d.density x * (g x - f x) =
      (∫ x in B, d.density x * (g x - f x)) +
      (∫ x in A \ B, d.density x * (g x - f x)) := by
    rw [← setIntegral_union disjoint_sdiff_self_right (hA.diff hB) hB_int hAB_int,
        union_diff_cancel hBA]
  linarith

end ContDist

/-! ### Monotone conditional expectation in the interval endpoint -/

/-- The conditional mean of a strictly increasing function on `[u, b]` is strictly increasing in
`u`. -/
theorem conditionalExpect_strictMono_right
    (d : ContDist) (g : ℝ → ℝ) (a b : ℝ)
    (hg_mono : StrictMonoOn g (Icc a b))
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hg_cont : ContinuousOn g (Icc a b))
    (hd_cont : ContinuousOn d.density (Icc a b))
    (_hab : a < b) :
    StrictMonoOn (fun u => d.conditionalExpectOrZero g (Icc u b)) (Ico a b) := by
  intro u₁ hu₁ u₂ hu₂ h12
  have hu₁b : u₁ < b := hu₁.2
  have hu₂b : u₂ < b := hu₂.2
  have hu₁a : a ≤ u₁ := hu₁.1
  have hu₂a : a ≤ u₂ := hu₂.1
  simp only [gt_iff_lt]
  -- Subset inclusions
  have h_sub₁₂ : Icc u₁ u₂ ⊆ Icc a b := Icc_subset_Icc hu₁a (hu₂b.le.trans le_rfl)
  have h_sub₂b : Icc u₂ b ⊆ Icc a b := Icc_subset_Icc hu₂a le_rfl
  have h_sub₁b : Icc u₁ b ⊆ Icc a b := Icc_subset_Icc hu₁a le_rfl
  -- Restricted continuity and monotonicity
  have hd_cont₁₂ := hd_cont.mono h_sub₁₂
  have hg_cont₁₂ := hg_cont.mono h_sub₁₂
  have hd_cont₂b := hd_cont.mono h_sub₂b
  have hg_cont₂b := hg_cont.mono h_sub₂b
  have hd_cont₁b := hd_cont.mono h_sub₁b
  have hg_cont₁b := hg_cont.mono h_sub₁b
  have hg_mono₁₂ := hg_mono.mono h_sub₁₂
  have hg_mono₂b : MonotoneOn g (Icc u₂ b) := (hg_mono.mono h_sub₂b).monotoneOn
  have hd_pos₁₂ : ∀ x ∈ Icc u₁ u₂, 0 < d.density x := fun x hx => hd_pos x (h_sub₁₂ hx)
  -- Integrability on sub-intervals (continuous on compact)
  have hfg_int₂b : IntegrableOn (fun x => d.density x * g x) (Icc u₂ b) :=
    (hd_cont₂b.mul hg_cont₂b).integrableOn_compact isCompact_Icc
  have hfg_int₁b : IntegrableOn (fun x => d.density x * g x) (Icc u₁ b) :=
    (hd_cont₁b.mul hg_cont₁b).integrableOn_compact isCompact_Icc
  -- Density integrals positive on non-degenerate sub-intervals
  have pos_of_lt : ∀ (p q : ℝ), p < q → Icc p q ⊆ Icc a b →
      0 < ∫ x in Icc p q, d.density x := by
    intro p q hpq hsub
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (fun x => d.nonneg x)) d.integrable.integrableOn]
    exact lt_of_lt_of_le (by simp [hpq]) (measure_mono
      (fun x hx => ⟨Function.mem_support.mpr
        (ne_of_gt (hd_pos x (hsub (Ioo_subset_Icc_self hx)))),
        Ioo_subset_Icc_self hx⟩))
  have DL_pos : 0 < ∫ x in Icc u₁ u₂, d.density x := pos_of_lt _ _ h12 h_sub₁₂
  have D2_pos : 0 < ∫ x in Icc u₂ b, d.density x := pos_of_lt _ _ hu₂b h_sub₂b
  have D1_pos : 0 < ∫ x in Icc u₁ b, d.density x := pos_of_lt _ _ hu₁b h_sub₁b
  -- KEY INEQUALITY 1: ∫_{[u₁,u₂]} f·g < g(u₂) · ∫_{[u₁,u₂]} f
  -- Since g is strictly increasing, g(x) < g(u₂) for x near u₁, with f(x) > 0.
  have ineq1 : ∫ x in Icc u₁ u₂, d.density x * g x <
      g u₂ * ∫ x in Icc u₁ u₂, d.density x := by
    simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h12.le]
    rw [show g u₂ * ∫ x in u₁..u₂, d.density x = ∫ x in u₁..u₂, g u₂ * d.density x from
      (intervalIntegral.integral_const_mul _ _).symm]
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h12
      (hd_cont₁₂.mul hg_cont₁₂) (continuousOn_const.mul hd_cont₁₂)
      (fun x ⟨hx1, hx2⟩ => by
        rw [mul_comm (g u₂)]; exact mul_le_mul_of_nonneg_left
          (hg_mono₁₂.monotoneOn (Ioc_subset_Icc_self ⟨hx1, hx2⟩)
            (right_mem_Icc.mpr h12.le) hx2)
          (d.nonneg x))
      ⟨u₁, left_mem_Icc.mpr h12.le, by
        rw [mul_comm (g u₂)]; exact mul_lt_mul_of_pos_left
          (hg_mono₁₂ (left_mem_Icc.mpr h12.le) (right_mem_Icc.mpr h12.le) h12)
          (hd_pos₁₂ u₁ (left_mem_Icc.mpr h12.le))⟩
  -- KEY INEQUALITY 2: g(u₂) · ∫_{[u₂,b]} f ≤ ∫_{[u₂,b]} f·g
  -- Since g(x) ≥ g(u₂) for x ∈ [u₂,b] by monotonicity.
  have ineq2 : g u₂ * ∫ x in Icc u₂ b, d.density x ≤
      ∫ x in Icc u₂ b, d.density x * g x := by
    calc g u₂ * ∫ x in Icc u₂ b, d.density x
        = ∫ x in Icc u₂ b, g u₂ * d.density x := (integral_const_mul _ _).symm
      _ = ∫ x in Icc u₂ b, d.density x * g u₂ := by congr 1; ext x; ring
      _ ≤ ∫ x in Icc u₂ b, d.density x * g x :=
          setIntegral_mono_on (d.integrable.integrableOn.mul_const _) hfg_int₂b
            measurableSet_Icc
            (fun x hx => mul_le_mul_of_nonneg_left
              (hg_mono₂b (left_mem_Icc.mpr hu₂b.le) hx hx.1) (d.nonneg x))
  -- Cross-multiplication: NL · D₂ < N₂ · DL
  have cross : (∫ x in Icc u₁ u₂, d.density x * g x) * (∫ x in Icc u₂ b, d.density x) <
      (∫ x in Icc u₂ b, d.density x * g x) * (∫ x in Icc u₁ u₂, d.density x) := by
    calc (∫ x in Icc u₁ u₂, d.density x * g x) * (∫ x in Icc u₂ b, d.density x)
        < (g u₂ * ∫ x in Icc u₁ u₂, d.density x) * (∫ x in Icc u₂ b, d.density x) :=
          mul_lt_mul_of_pos_right ineq1 D2_pos
      _ = (g u₂ * ∫ x in Icc u₂ b, d.density x) * (∫ x in Icc u₁ u₂, d.density x) := by ring
      _ ≤ (∫ x in Icc u₂ b, d.density x * g x) * (∫ x in Icc u₁ u₂, d.density x) :=
          mul_le_mul_of_nonneg_right ineq2 DL_pos.le
  -- Integral splitting: ∫_{[u₁,b]} = ∫_{[u₁,u₂]} + ∫_{[u₂,b]}
  have split_Icc : ∀ (f : ℝ → ℝ), IntegrableOn f (Icc u₁ b) →
      ∫ x in Icc u₁ b, f x = (∫ x in Icc u₁ u₂, f x) + ∫ x in Icc u₂ b, f x := by
    intro f hf
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h12.le,
      ← intervalIntegral.integral_of_le hu₂b.le,
      ← intervalIntegral.integral_of_le hu₁b.le]
    have hi12 : IntervalIntegrable f volume u₁ u₂ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12.le]
      exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hu₂b.le)) le_rfl
    have hi2b : IntervalIntegrable f volume u₂ b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu₂b.le]
      exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc h12.le le_rfl)) le_rfl
    exact (intervalIntegral.integral_add_adjacent_intervals (a := u₁) (b := u₂) (c := b)
      hi12 hi2b).symm
  have split_D := split_Icc d.density d.integrable.integrableOn
  have split_N := split_Icc _ hfg_int₁b
  -- Unfold conditional expectations and conclude via cross-multiplication
  rw [d.conditionalExpectOrZero_eq_of_pos g _ D1_pos,
      d.conditionalExpectOrZero_eq_of_pos g _ D2_pos, split_N, split_D]
  rw [div_lt_div_iff₀ (by linarith : 0 < (∫ x in Icc u₁ u₂, d.density x) +
      ∫ x in Icc u₂ b, d.density x) D2_pos]
  nlinarith

/-- The conditional mean of a strictly increasing function on `[a, u]` is strictly increasing in
`u`. -/
theorem conditionalExpect_strictMono_left
    (d : ContDist) (g : ℝ → ℝ) (a b : ℝ)
    (hg_mono : StrictMonoOn g (Icc a b))
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hg_cont : ContinuousOn g (Icc a b))
    (hd_cont : ContinuousOn d.density (Icc a b))
    (_hab : a < b) :
    StrictMonoOn (fun u => d.conditionalExpectOrZero g (Icc a u)) (Ioc a b) := by
  intro u₁ hu₁ u₂ hu₂ h12
  have hu₁a : a < u₁ := hu₁.1
  have hu₂a : a < u₂ := lt_of_lt_of_le hu₁a h12.le
  have hu₁b : u₁ ≤ b := hu₁.2
  have hu₂b : u₂ ≤ b := hu₂.2
  simp only [gt_iff_lt]
  have h_sub_a1 : Icc a u₁ ⊆ Icc a b := Icc_subset_Icc le_rfl hu₁b
  have h_sub_12 : Icc u₁ u₂ ⊆ Icc a b := Icc_subset_Icc hu₁a.le hu₂b
  have h_sub_a2 : Icc a u₂ ⊆ Icc a b := Icc_subset_Icc le_rfl hu₂b
  have hd_cont_a1 := hd_cont.mono h_sub_a1
  have hg_cont_a1 := hg_cont.mono h_sub_a1
  have hd_cont_12 := hd_cont.mono h_sub_12
  have hg_cont_12 := hg_cont.mono h_sub_12
  have hd_cont_a2 := hd_cont.mono h_sub_a2
  have hg_cont_a2 := hg_cont.mono h_sub_a2
  have hg_mono_a1 : MonotoneOn g (Icc a u₁) := (hg_mono.mono h_sub_a1).monotoneOn
  have hg_mono_12 := hg_mono.mono h_sub_12
  have hd_pos_a1 : ∀ x ∈ Icc a u₁, 0 < d.density x := fun x hx => hd_pos x (h_sub_a1 hx)
  have hd_pos_12 : ∀ x ∈ Icc u₁ u₂, 0 < d.density x := fun x hx => hd_pos x (h_sub_12 hx)
  have pos_of_lt : ∀ (p q : ℝ), p < q → Icc p q ⊆ Icc a b →
      0 < ∫ x in Icc p q, d.density x := by
    intro p q hpq hsub
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (fun x => d.nonneg x)) d.integrable.integrableOn]
    exact lt_of_lt_of_le (by simp [hpq]) (measure_mono
      (fun x hx => ⟨Function.mem_support.mpr
        (ne_of_gt (hd_pos x (hsub (Ioo_subset_Icc_self hx)))),
        Ioo_subset_Icc_self hx⟩))
  have D1_pos : 0 < ∫ x in Icc a u₁, d.density x := pos_of_lt _ _ hu₁a h_sub_a1
  have DΔ_pos : 0 < ∫ x in Icc u₁ u₂, d.density x := pos_of_lt _ _ h12 h_sub_12
  have D2_pos : 0 < ∫ x in Icc a u₂, d.density x := pos_of_lt _ _ hu₂a h_sub_a2
  have hfg_int_a1 : IntegrableOn (fun x => d.density x * g x) (Icc a u₁) :=
    (hd_cont_a1.mul hg_cont_a1).integrableOn_compact isCompact_Icc
  have hfg_int_12 : IntegrableOn (fun x => d.density x * g x) (Icc u₁ u₂) :=
    (hd_cont_12.mul hg_cont_12).integrableOn_compact isCompact_Icc
  have hfg_int_a2 : IntegrableOn (fun x => d.density x * g x) (Icc a u₂) :=
    (hd_cont_a2.mul hg_cont_a2).integrableOn_compact isCompact_Icc
  have ineq1 : ∫ x in Icc a u₁, d.density x * g x ≤
      g u₁ * ∫ x in Icc a u₁, d.density x := by
    calc
      ∫ x in Icc a u₁, d.density x * g x
        ≤ ∫ x in Icc a u₁, d.density x * g u₁ :=
          setIntegral_mono_on hfg_int_a1 (d.integrable.integrableOn.mul_const _) measurableSet_Icc
            (fun x hx => mul_le_mul_of_nonneg_left
              (hg_mono_a1 hx (right_mem_Icc.mpr hu₁a.le) hx.2) (d.nonneg x))
      _ = g u₁ * ∫ x in Icc a u₁, d.density x := by
          rw [← integral_const_mul]
          congr 1
          ext x
          ring
  have ineq2 : g u₁ * ∫ x in Icc u₁ u₂, d.density x <
      ∫ x in Icc u₁ u₂, d.density x * g x := by
    simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h12.le]
    rw [show g u₁ * ∫ x in u₁..u₂, d.density x = ∫ x in u₁..u₂, g u₁ * d.density x from
      (intervalIntegral.integral_const_mul _ _).symm]
    exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h12
      (continuousOn_const.mul hd_cont_12) (hd_cont_12.mul hg_cont_12)
      (fun x ⟨hx1, hx2⟩ => by
        rw [mul_comm (g u₁)]
        exact mul_le_mul_of_nonneg_left
          (hg_mono_12.monotoneOn (left_mem_Icc.mpr h12.le) (Ioc_subset_Icc_self ⟨hx1, hx2⟩)
            hx1.le)
          (d.nonneg x))
      ⟨u₂, right_mem_Icc.mpr h12.le, by
        rw [mul_comm (g u₁)]
        exact mul_lt_mul_of_pos_left
          (hg_mono_12 (left_mem_Icc.mpr h12.le) (right_mem_Icc.mpr h12.le) h12)
          (hd_pos_12 u₂ (right_mem_Icc.mpr h12.le))⟩
  have cross :
      (∫ x in Icc a u₁, d.density x * g x) * (∫ x in Icc u₁ u₂, d.density x) <
        (∫ x in Icc u₁ u₂, d.density x * g x) * (∫ x in Icc a u₁, d.density x) := by
    calc
      (∫ x in Icc a u₁, d.density x * g x) * (∫ x in Icc u₁ u₂, d.density x)
        ≤ (g u₁ * ∫ x in Icc a u₁, d.density x) * (∫ x in Icc u₁ u₂, d.density x) :=
          mul_le_mul_of_nonneg_right ineq1 DΔ_pos.le
      _ = (g u₁ * ∫ x in Icc u₁ u₂, d.density x) * (∫ x in Icc a u₁, d.density x) := by ring
      _ < (∫ x in Icc u₁ u₂, d.density x * g x) * (∫ x in Icc a u₁, d.density x) :=
          mul_lt_mul_of_pos_right ineq2 D1_pos
  have split_Icc : ∀ (f : ℝ → ℝ), IntegrableOn f (Icc a u₂) →
      ∫ x in Icc a u₂, f x = (∫ x in Icc a u₁, f x) + ∫ x in Icc u₁ u₂, f x := by
    intro f hf
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hu₁a.le,
      ← intervalIntegral.integral_of_le h12.le,
      ← intervalIntegral.integral_of_le hu₂a.le]
    have hi_a1 : IntervalIntegrable f volume a u₁ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu₁a.le]
      exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl h12.le)) le_rfl
    have hi_12 : IntervalIntegrable f volume u₁ u₂ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12.le]
      exact hf.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hu₁a.le le_rfl)) le_rfl
    exact (intervalIntegral.integral_add_adjacent_intervals (a := a) (b := u₁) (c := u₂)
      hi_a1 hi_12).symm
  have split_D := split_Icc d.density d.integrable.integrableOn
  have split_N := split_Icc _ hfg_int_a2
  rw [d.conditionalExpectOrZero_eq_of_pos g _ D1_pos,
      d.conditionalExpectOrZero_eq_of_pos g _ D2_pos, split_N, split_D]
  rw [div_lt_div_iff₀ D1_pos (by linarith : 0 < (∫ x in Icc a u₁, d.density x) +
      ∫ x in Icc u₁ u₂, d.density x)]
  nlinarith

/-- As the upper endpoint `u` shrinks to `a`, the conditional mean of the identity on `[a, u]`
tends to `a`. -/
theorem tendsto_conditionalExpect_id_left_boundary
    (d : ContDist) (a b : ℝ)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (_hab : a < b) :
    Filter.Tendsto (fun u => d.conditionalExpectOrZero id (Icc a u))
        (nhdsWithin a (Ioc a b)) (nhds a) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro u hu hudist
  have hau : a < u := hu.1
  have hub : u ≤ b := hu.2
  have hd_pos_left : ∀ x ∈ Icc a u, 0 < d.density x := fun x hx =>
    hd_pos x (Icc_subset_Icc le_rfl hub hx)
  have hd_cont_left : ContinuousOn d.density (Icc a u) :=
    hd_cont.mono (Icc_subset_Icc le_rfl hub)
  have hpos : 0 < ∫ x in Icc a u, d.density x := by
    simpa [ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hau.le] using
      d.prob_interval_pos_of_pos_density hau hd_pos_left hd_cont_left
  have hid_int : IntegrableOn (fun x => d.density x * x) (Icc a u) :=
    (hd_cont_left.mul continuousOn_id).integrableOn_compact isCompact_Icc
  -- On the positive-probability regime the totalized value equals the conditional mean.
  rw [show d.conditionalExpectOrZero id (Icc a u) = d.conditionalExpect id (Icc a u) hpos from rfl]
  have hmem : d.conditionalExpect id (Icc a u) hpos ∈ Icc a u :=
    d.conditionalExpect_id_mem_Icc a u hpos hid_int hau.le
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmem.1)]
  rw [Real.dist_eq] at hudist
  have hu_lt : u - a < ε := by
    simpa [abs_of_pos (sub_pos.mpr hau)] using hudist
  calc
    d.conditionalExpect id (Icc a u) hpos - a ≤ u - a := sub_le_sub_right hmem.2 a
    _ < ε := hu_lt

/-- As the lower endpoint `u` grows to `b`, the conditional mean of the identity on `[u, b]` tends
to `b`. -/
theorem tendsto_conditionalExpect_id_right_boundary
    (d : ContDist) (a b : ℝ)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b))
    (_hab : a < b) :
    Filter.Tendsto (fun u => d.conditionalExpectOrZero id (Icc u b))
        (nhdsWithin b (Ico a b)) (nhds b) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro u hu hudist
  have hua : a ≤ u := hu.1
  have hub : u < b := hu.2
  have hd_pos_right : ∀ x ∈ Icc u b, 0 < d.density x := fun x hx =>
    hd_pos x (Icc_subset_Icc hua le_rfl hx)
  have hd_cont_right : ContinuousOn d.density (Icc u b) :=
    hd_cont.mono (Icc_subset_Icc hua le_rfl)
  have hpos : 0 < ∫ x in Icc u b, d.density x := by
    simpa [ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hub.le] using
      d.prob_interval_pos_of_pos_density hub hd_pos_right hd_cont_right
  have hid_int : IntegrableOn (fun x => d.density x * x) (Icc u b) :=
    (hd_cont_right.mul continuousOn_id).integrableOn_compact isCompact_Icc
  -- On the positive-probability regime the totalized value equals the conditional mean.
  rw [show d.conditionalExpectOrZero id (Icc u b) = d.conditionalExpect id (Icc u b) hpos from rfl]
  have hmem : d.conditionalExpect id (Icc u b) hpos ∈ Icc u b :=
    d.conditionalExpect_id_mem_Icc u b hpos hid_int hub.le
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmem.2)]
  rw [Real.dist_eq] at hudist
  have hu_lt : b - u < ε := by
    have : |u - b| < ε := hudist
    simpa [abs_of_neg (sub_neg.mpr hub)] using this
  calc
    -(d.conditionalExpect id (Icc u b) hpos - b) = b - d.conditionalExpect id (Icc u b) hpos :=
        neg_sub _ _
    _ ≤ b - u := sub_le_sub_left hmem.1 b
    _ < ε := hu_lt

/-! ### Truncation -/

namespace ContDist

/-- Truncation to interval `[a, b]` with renormalization. The nondegeneracy `_h_ab : a < b` is kept
to document the intended regime; the renormalization only needs the positive mass `h_pos`. -/
noncomputable def truncate (d : ContDist) (a b : ℝ)
    (_h_ab : a < b) (h_pos : 0 < d.prob_interval a b) : ContDist where
  density x := if x ∈ Icc a b then d.density x / d.prob_interval a b else 0
  nonneg := by
    intro x; split_ifs with hx
    · -- density and prob_interval are both nonneg
      exact div_nonneg (d.nonneg x) (le_of_lt h_pos)
    · exact le_refl 0
  integrable := by
    -- density_trunc = (Icc a b).indicator (density / c), integrable via indicator lemma
    have h_eq : (fun x => if x ∈ Icc a b then d.density x / d.prob_interval a b else 0) =
        (Icc a b).indicator (fun x => d.density x / d.prob_interval a b) := by
      ext x; simp [indicator]
    rw [h_eq]
    exact (d.integrable.div_const _).indicator measurableSet_Icc
  integral_one := by
    -- ∫ density_trunc = ∫ₓ∈Icc indicator (density / c) = (1/c) * ∫ₓ∈Icc density = c/c = 1
    have h_eq : (fun x => if x ∈ Icc a b then d.density x / d.prob_interval a b else 0) =
        (Icc a b).indicator (fun x => d.density x / d.prob_interval a b) := by
      ext x; simp [indicator]
    rw [h_eq, integral_indicator measurableSet_Icc]
    rw [integral_div]
    -- `∫ₓ∈Icc density` is `prob_interval a b` by definition.
    rw [show ∫ x in Icc a b, d.density x = d.prob_interval a b from rfl,
      div_self (ne_of_gt h_pos)]

lemma truncate_density (d : ContDist) (a b : ℝ) (h_ab : a < b)
    (h_pos : 0 < d.prob_interval a b) (x : ℝ) :
    (d.truncate a b h_ab h_pos).density x =
      if x ∈ Icc a b then d.density x / d.prob_interval a b else 0 := rfl

end ContDist

end Econlib.Probability
