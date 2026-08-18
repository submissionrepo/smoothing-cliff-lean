/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Concavity.ConcavityPreservation
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Convex.Deriv

/-!
# Benveniste-Scheinkman theorem and envelope condition

This file establishes differentiability of concave value functions in dynamic programing via
supporting functions. The **Benveniste-Scheinkman** result (Benveniste and Scheinkman 1979) is that
a concave function touched from below by a differentiable function must itself be differentiable,
with the same derivative at the contact point. We apply it to the deterministic Bellman equation to
obtain the **envelope condition** for the value function.

The DP results come in two flavors, distinguished by whether value-function differentiability is
assumed or derived. The Benveniste-Scheinkman support argument can construct a differentiable lower
support for `v*` only when the optimal frozen action keeps the successor state locally constant in
the current state, so that the continuation term is constant. When the transition depends on the
current state, the continuation term inherits whatever differentiability `v*` has at the successor,
which must then be supplied as a hypothesis.

## Main statements

* `ConcaveOn.differentiableAt_of_support` — the abstract Benveniste-Scheinkman lemma:
  Differentiability of a concave function from a differentiable lower support.
* `deriv_eq_of_eventuallyLE_of_eq` — the derivative equals that of any supporting function.
* `envelope_condition_dp_of_diffSucc` / `envelope_deriv_dp_of_diffSucc` — general reusable envelope
  results for a state-dependent transition, taking successor-differentiability of `v*` as an
  explicit hypothesis (`hv_diff_succ`).
* `envelope_condition_dp` / `envelope_deriv_dp` — the headline theorems. Value-function
  differentiability on `O` is derived from concavity of `v*`, a differentiable reward, an optimal
  locally feasible policy, and the structural condition `h_trans_frozen` that the optimal frozen
  action leaves the successor state locally constant in the current state. The envelope derivative
  then reduces to `(v*)'(w₀) = ∂reward/∂w(w₀, a*(w₀))`.
* `envelope_deriv_dp_of_transition_indep` — corollary: When the transition does not depend on the
  current state, `h_trans_frozen` holds automatically.
* `envelope_condition_consumption` — specialization to consumption models: `(v*)'(w) = u'(c*(w))`.

## Notes

The `..._of_diffSucc` results allow a transition depending on the current state and so generalize
beyond the next-state-as-control reduction of Stokey, Lucas, and Prescott (1989), Theorem 4.11.
Theorem 4.10 there is the abstract Benveniste-Scheinkman lemma
(`ConcaveOn.differentiableAt_of_support`).

## References

* Benveniste, L. M., and J. A. Scheinkman. 1979. “On the Differentiability of the Value Function in
  Dynamic Models of Economics.” *Econometrica* 47 (3): 727. [https://doi.org/10.2307/1910417](https://doi.org/10.2307/1910417).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

benveniste-scheinkman, envelope theorem, dynamic programing, concave value function
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell UnboundedDetMDP

open Set Filter Topology

/-! ## Abstract Benveniste-Scheinkman -/

/-- **Benveniste-Scheinkman Theorem** (SLP Theorem 4.10, 1-D case). Let `v : ℝ → ℝ` be concave on
an open convex domain `D ⊆ ℝ`. If at each `w₀ ∈ D` there exists a differentiable `φ` with
`φ(w₀) = v(w₀)` and `φ ≤ v` on a neighborhood of `w₀`, then `v` is differentiable at every point of
`D`. (SLP additionally assume `φ` concave; only differentiability of `φ` is needed here.) -/
theorem ConcaveOn.differentiableAt_of_support {D : Set ℝ}
    (hD_open : IsOpen D)
    -- kept for symmetry with the statement's convex-domain hypothesis; `hv_concave` already
    -- forces `D` convex, so the proof does not need this separately.
    (_hD_convex : Convex ℝ D)
    (v : ℝ → ℝ) (hv_concave : ConcaveOn ℝ D v)
    (h_support : ∀ w₀ ∈ D, ∃ φ : ℝ → ℝ,
      DifferentiableAt ℝ φ w₀ ∧
      φ w₀ = v w₀ ∧
      ∀ᶠ w in 𝓝 w₀, φ w ≤ v w) :
    ∀ w₀ ∈ D, DifferentiableAt ℝ v w₀ := by
  intro w₀ hw₀
  obtain ⟨φ, hφ_diff, hφ_eq, hφ_le⟩ := h_support w₀ hw₀
  have hcvx : ConvexOn ℝ D (-v) := hv_concave.neg
  have hint : w₀ ∈ interior D := by rw [hD_open.interior_eq]; exact hw₀
  set L := derivWithin (-v) (Iio w₀) w₀ with hL_def
  set R := derivWithin (-v) (Ioi w₀) w₀ with hR_def
  -- Concavity gives L ≤ R for -v; the support φ squeezes both to d = -φ'(w₀).
  have hLR : L ≤ R := hcvx.leftDeriv_le_rightDeriv_of_mem_interior hint
  have hR_tendsto : Tendsto (slope (-v) w₀) (𝓝[>] w₀) (𝓝 R) := by
    have h := hcvx.hasDerivWithinAt_rightDeriv_of_mem_interior hint
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    rwa [diff_singleton_eq_self (by simp : w₀ ∉ Ioi w₀)] at h
  have hL_tendsto : Tendsto (slope (-v) w₀) (𝓝[<] w₀) (𝓝 L) := by
    have h := hcvx.hasDerivWithinAt_leftDeriv_of_mem_interior hint
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    rwa [diff_singleton_eq_self (by simp : w₀ ∉ Iio w₀)] at h
  set d := -deriv φ w₀ with hd_def
  have hφ_da : HasDerivAt (-φ) d w₀ := hφ_diff.hasDerivAt.neg
  have hd_right : Tendsto (slope (-φ) w₀) (𝓝[>] w₀) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hφ_da).2
  have hd_left : Tendsto (slope (-φ) w₀) (𝓝[<] w₀) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hφ_da).1
  -- φ ≤ v with equality at w₀ forces slope(-v) ≤ slope(-φ) to the right
  -- (positive denominator) and slope(-φ) ≤ slope(-v) to the left.
  have hR_le_d : R ≤ d := by
    refine tendsto_le_of_eventuallyLE hR_tendsto hd_right ?_
    refine ((hφ_le.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).mono ?_
    intro y ⟨hle, hgt⟩
    simp only [slope_def_field, Pi.neg_apply]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hd_le_L : d ≤ L := by
    refine tendsto_le_of_eventuallyLE hd_left hL_tendsto ?_
    refine ((hφ_le.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin).mono ?_
    intro y ⟨hle, hlt⟩
    simp only [slope_def_field, Pi.neg_apply]
    exact div_le_div_of_nonpos_of_le (by linarith) (by linarith)
  have hL_eq_d : L = d := le_antisymm (hLR.trans hR_le_d) hd_le_L
  have hR_eq_d : R = d := le_antisymm hR_le_d (hd_le_L.trans hLR)
  have hda_neg : HasDerivAt (-v) d w₀ := by
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    exact ⟨hL_eq_d ▸ hL_tendsto, hR_eq_d ▸ hR_tendsto⟩
  have hda_v : HasDerivAt v (-d) w₀ := by
    have := hda_neg.neg
    simp only [neg_neg] at this
    convert this using 1
  exact hda_v.differentiableAt

/-- The derivative of `v` at `w₀` equals that of any supporting function `φ`. -/
lemma deriv_eq_of_eventuallyLE_of_eq
    (v : ℝ → ℝ)
    (w₀ : ℝ)
    (φ : ℝ → ℝ)
    (hφ_diff : DifferentiableAt ℝ φ w₀)
    (hφ_eq : φ w₀ = v w₀)
    (hφ_le : ∀ᶠ w in 𝓝 w₀, φ w ≤ v w)
    (hv_diff : DifferentiableAt ℝ v w₀) :
    deriv v w₀ = deriv φ w₀ := by
  have h_min : IsLocalMin (v - φ) w₀ := by
    rw [IsLocalMin, IsMinFilter]
    apply Filter.Eventually.mono hφ_le
    intro w hw
    simp only [Pi.sub_apply]
    linarith [hφ_eq]
  have h_deriv_zero := h_min.deriv_eq_zero
  simp only [deriv_sub hv_diff hφ_diff] at h_deriv_zero
  linarith

/-! ## General Envelope Lemma (successor-differentiability assumed) -/

/-- **Envelope condition for DP, general form.** Given a deterministic DP with differentiable
reward and transition, a concave value function, an optimal policy, and local feasibility of the
frozen action, the value function is differentiable, provided `v*` is differentiable at every
successor state `f(w, a*(w))` (`hv_diff_succ`).

This is the general building block for a transition that may depend on the current state.
Successor-differentiability is a hypothesis here, not a conclusion. For the headline theorem that
derives differentiability under a state-independent (frozen-successor) transition, see
`envelope_condition_dp`. -/
theorem envelope_condition_dp_of_diffSucc (D : ConcaveDPData)
    {O : Set ℝ} (hO_open : IsOpen O) (hO_convex : Convex ℝ O)
    (hO_sub : O ⊆ D.domain)
    (h_reward_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.reward w' a) w)
    (h_trans_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.transition w' a) w)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    (ha_feasible :
      ∀ w ∈ O, a_star w ∈ D.toDetMDP.Γ w)
    (ha_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
      D.toDetMDP.reward w a +
        D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (a_star w) +
        D.toDetMDP.β *
          v_star
            (D.toDetMDP.transition w (a_star w)))
    -- a*(w₀) remains feasible for nearby states
    (ha_locally_feasible : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀, a_star w₀ ∈ D.toDetMDP.Γ w)
    (hv_bdd : UniformBounded v_star)
    (hv_fp : ∀ s,
      v_star s = D.toDetMDP.bellmanOperator v_star s)
    (hv_concave : ConcaveOn ℝ D.domain v_star)
    (hv_diff_succ : ∀ w ∈ O,
      DifferentiableAt ℝ v_star
        (D.toDetMDP.transition w (a_star w))) :
    ∀ w₀ ∈ O, DifferentiableAt ℝ v_star w₀ := by
  intro w₀ hw₀
  apply ConcaveOn.differentiableAt_of_support hO_open hO_convex v_star
    (hv_concave.subset hO_sub hO_convex) _ w₀ hw₀
  -- For each w₀' ∈ O, construct the supporting function
  intro w₀' hw₀'
  set a₀ := a_star w₀'
  set φ : ℝ → ℝ := fun w =>
    D.toDetMDP.reward w a₀ +
      D.toDetMDP.β * v_star (D.toDetMDP.transition w a₀)
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- φ differentiable at w₀'
    exact (h_reward_diff w₀' a₀ hw₀'
        (ha_feasible w₀' hw₀')).add
      (DifferentiableAt.const_mul
        ((hv_diff_succ w₀' hw₀').comp w₀'
          (h_trans_diff w₀' a₀ hw₀'
            (ha_feasible w₀' hw₀'))) _)
  · -- φ(w₀') = v*(w₀')
    have hfp := hv_fp w₀'
    unfold bellmanOperator at hfp
    have hle : φ w₀' ≤ v_star w₀' := by
      rw [hfp]
      exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w₀')
        ⟨a₀, ha_feasible w₀' hw₀', rfl⟩
    have hge : v_star w₀' ≤ φ w₀' := by
      rw [hfp]
      exact csSup_le
        (D.toDetMDP.bellmanSet_nonempty v_star w₀')
        (fun r ⟨a, ha, hr⟩ => hr ▸ ha_optimal w₀' hw₀' a ha)
    linarith
  · -- φ(w) ≤ v*(w) for w near w₀'
    apply Filter.Eventually.mono
      (ha_locally_feasible w₀' hw₀')
    intro w ha₀_feasible
    have hfp := hv_fp w
    rw [hfp]; unfold bellmanOperator
    exact le_csSup
      (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w)
      ⟨a₀, ha₀_feasible, rfl⟩

/-- **Envelope derivative formula, general form.** Under the hypotheses of
`envelope_condition_dp_of_diffSucc` (concavity of `v*`, differentiable reward and transition, an
optimal locally feasible policy, and differentiability of `v*` at the successor states
`f(w, a*(w))`), the derivative of the value function satisfies
`(v*)'(w₀) = ∂u/∂w(w₀, a*(w₀)) + β (v*)'(f(w₀, a*(w₀))) · ∂f/∂w(w₀, a*(w₀))`.

Successor-differentiability of `v*` is a hypothesis here (`hv_diff_succ`). For the headline theorem
that derives differentiability under a state-independent transition, see `envelope_deriv_dp`. -/
theorem envelope_deriv_dp_of_diffSucc (D : ConcaveDPData)
    {O : Set ℝ} (hO_open : IsOpen O)
    (hO_convex : Convex ℝ O)
    (hO_sub : O ⊆ D.domain)
    (h_reward_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.reward w' a) w)
    (h_trans_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.transition w' a) w)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    (ha_feasible :
      ∀ w ∈ O, a_star w ∈ D.toDetMDP.Γ w)
    (ha_locally_feasible : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀, a_star w₀ ∈ D.toDetMDP.Γ w)
    (ha_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
      D.toDetMDP.reward w a +
        D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (a_star w) +
        D.toDetMDP.β *
          v_star
            (D.toDetMDP.transition w (a_star w)))
    (hv_bdd : UniformBounded v_star)
    (hv_fp : ∀ s,
      v_star s = D.toDetMDP.bellmanOperator v_star s)
    (hv_concave : ConcaveOn ℝ D.domain v_star)
    -- v* differentiable at every successor state: an explicit B-S hypothesis (not derived here).
    (hv_diff_succ : ∀ w ∈ O,
      DifferentiableAt ℝ v_star
        (D.toDetMDP.transition w (a_star w)))
    (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv v_star w₀ =
      deriv (fun w => D.toDetMDP.reward w (a_star w₀))
        w₀ +
      D.toDetMDP.β *
        deriv v_star
          (D.toDetMDP.transition w₀ (a_star w₀)) *
        deriv
          (fun w => D.toDetMDP.transition w (a_star w₀))
          w₀ := by
  -- Value-function differentiability on `O` follows from the general envelope lemma applied to the
  -- successor-differentiability input.
  have hv_diff : ∀ w ∈ O, DifferentiableAt ℝ v_star w :=
    envelope_condition_dp_of_diffSucc D hO_open hO_convex hO_sub h_reward_diff h_trans_diff
      v_star a_star ha_feasible ha_optimal ha_locally_feasible hv_bdd hv_fp
      hv_concave hv_diff_succ
  have hv_diff_succ₀ := hv_diff_succ w₀ hw₀
  set a₀ := a_star w₀
  set φ : ℝ → ℝ := fun w =>
    D.toDetMDP.reward w a₀ +
      D.toDetMDP.β * v_star (D.toDetMDP.transition w a₀)
  have hrd := h_reward_diff w₀ a₀ hw₀ (ha_feasible w₀ hw₀)
  have htd := h_trans_diff w₀ a₀ hw₀ (ha_feasible w₀ hw₀)
  have hφ_diff : DifferentiableAt ℝ φ w₀ :=
    hrd.add (DifferentiableAt.const_mul
      (hv_diff_succ₀.comp w₀ htd) _)
  have hφ_eq : φ w₀ = v_star w₀ := by
    have hfp := hv_fp w₀
    unfold bellmanOperator at hfp
    have hle : φ w₀ ≤ v_star w₀ := by
      rw [hfp]
      exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w₀)
        ⟨a₀, ha_feasible w₀ hw₀, rfl⟩
    have hge : v_star w₀ ≤ φ w₀ := by
      rw [hfp]
      exact csSup_le
        (D.toDetMDP.bellmanSet_nonempty v_star w₀)
        (fun r ⟨a, ha, hr⟩ => hr ▸ ha_optimal w₀ hw₀ a ha)
    linarith
  have hφ_le : ∀ᶠ w in 𝓝 w₀, φ w ≤ v_star w := by
    apply Filter.Eventually.mono
      (ha_locally_feasible w₀ hw₀)
    intro w ha₀_feasible
    have hfp := hv_fp w
    rw [hfp]; unfold bellmanOperator
    exact le_csSup
      (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w)
      ⟨a₀, ha₀_feasible, rfl⟩
  -- φ supports v* from below with equality at w₀, so their derivatives agree there.
  have h_deriv_eq : deriv v_star w₀ = deriv φ w₀ :=
    deriv_eq_of_eventuallyLE_of_eq v_star w₀ φ hφ_diff hφ_eq hφ_le
      (hv_diff w₀ hw₀)
  have hderiv_φ : deriv φ w₀ =
      deriv (fun w => D.toDetMDP.reward w a₀) w₀ +
      D.toDetMDP.β *
        deriv v_star
          (D.toDetMDP.transition w₀ a₀) *
        deriv
          (fun w => D.toDetMDP.transition w a₀) w₀ := by
    have h1 : deriv φ w₀ =
        deriv (fun w => D.toDetMDP.reward w a₀) w₀ +
        deriv (fun w => D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a₀)) w₀ :=
      deriv_add hrd (DifferentiableAt.const_mul
        (hv_diff_succ₀.comp w₀ htd) _)
    have h2 : deriv (fun w => D.toDetMDP.β *
        v_star (D.toDetMDP.transition w a₀)) w₀ =
        D.toDetMDP.β * deriv (fun w =>
          v_star (D.toDetMDP.transition w a₀)) w₀ :=
      deriv_const_mul _ (hv_diff_succ₀.comp w₀ htd)
    have h3 : deriv (fun w =>
        v_star (D.toDetMDP.transition w a₀)) w₀ =
        deriv v_star (D.toDetMDP.transition w₀ a₀) *
        deriv (fun w => D.toDetMDP.transition w a₀)
          w₀ := by
      have := (hv_diff_succ₀.hasDerivAt.comp w₀
        htd.hasDerivAt).deriv
      simp only [Function.comp_def] at this
      exact this
    rw [h1, h2, h3]; ring
  rw [h_deriv_eq, hderiv_φ]

/-! ## Headline Envelope Condition (differentiability derived) -/

/-- **Envelope condition for DP.** Given a deterministic DP with differentiable reward, a concave
value function, an optimal locally feasible policy, and the structural condition `h_trans_frozen`
that the optimal frozen action keeps the successor state locally constant in the current state, the
value function is differentiable on `O`.

Differentiability of `v*` is a conclusion, not a hypothesis: The support function freezes the
continuation value at the successor of `w₀'`, so it is differentiable from the reward alone, with
no successor-differentiability of `v*` assumed. `h_trans_frozen` is the next-state-as-control
condition (it holds whenever the transition does not depend on the current state, e.g.
`f(w, a) = a` or `f(w, a) = F(a)`). -/
theorem envelope_condition_dp (D : ConcaveDPData)
    {O : Set ℝ} (hO_open : IsOpen O) (hO_convex : Convex ℝ O)
    (hO_sub : O ⊆ D.domain)
    (h_reward_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.reward w' a) w)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    (ha_feasible :
      ∀ w ∈ O, a_star w ∈ D.toDetMDP.Γ w)
    (ha_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
      D.toDetMDP.reward w a +
        D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (a_star w) +
        D.toDetMDP.β *
          v_star
            (D.toDetMDP.transition w (a_star w)))
    -- a*(w₀) remains feasible for nearby states
    (ha_locally_feasible : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀, a_star w₀ ∈ D.toDetMDP.Γ w)
    -- the optimal frozen action keeps the successor locally constant in the current state
    (h_trans_frozen : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀,
        D.toDetMDP.transition w (a_star w₀) =
          D.toDetMDP.transition w₀ (a_star w₀))
    (hv_bdd : UniformBounded v_star)
    (hv_fp : ∀ s,
      v_star s = D.toDetMDP.bellmanOperator v_star s)
    (hv_concave : ConcaveOn ℝ D.domain v_star) :
    ∀ w₀ ∈ O, DifferentiableAt ℝ v_star w₀ := by
  intro w₀ hw₀
  apply ConcaveOn.differentiableAt_of_support hO_open hO_convex v_star
    (hv_concave.subset hO_sub hO_convex) _ w₀ hw₀
  -- For each w₀' ∈ O, build a support whose continuation value is frozen at w₀'s successor.
  intro w₀' hw₀'
  set a₀ := a_star w₀' with ha₀_def
  set φ : ℝ → ℝ := fun w =>
    D.toDetMDP.reward w a₀ +
      D.toDetMDP.β * v_star (D.toDetMDP.transition w₀' a₀) with hφ_def
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- φ differentiable at w₀': reward is C¹ and the continuation term is constant in w.
    exact (h_reward_diff w₀' a₀ hw₀' (ha_feasible w₀' hw₀')).add
      (differentiableAt_const _)
  · -- φ(w₀') = v*(w₀'): at w₀' the frozen successor is the actual successor.
    have hfp := hv_fp w₀'
    unfold bellmanOperator at hfp
    have hle : φ w₀' ≤ v_star w₀' := by
      rw [hfp]
      exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w₀')
        ⟨a₀, ha_feasible w₀' hw₀', rfl⟩
    have hge : v_star w₀' ≤ φ w₀' := by
      rw [hfp]
      exact csSup_le
        (D.toDetMDP.bellmanSet_nonempty v_star w₀')
        (fun r ⟨a, ha, hr⟩ => hr ▸ ha_optimal w₀' hw₀' a ha)
    linarith
  · -- φ(w) ≤ v*(w) near w₀': where a₀ stays feasible and the successor is frozen, φ agrees with
    -- the Bellman lower bound reward(w,a₀) + β v*(f(w,a₀)) ≤ v*(w).
    filter_upwards [ha_locally_feasible w₀' hw₀', h_trans_frozen w₀' hw₀']
      with w ha₀_feasible h_frozen
    have hφw : φ w =
        D.toDetMDP.reward w a₀ +
          D.toDetMDP.β * v_star (D.toDetMDP.transition w a₀) := by
      change D.toDetMDP.reward w a₀ +
          D.toDetMDP.β * v_star (D.toDetMDP.transition w₀' a₀) = _
      rw [← h_frozen]
    have hfp := hv_fp w
    rw [hφw, hfp]; unfold bellmanOperator
    exact le_csSup
      (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w)
      ⟨a₀, ha₀_feasible, rfl⟩

/-- **Envelope derivative formula.** Under the hypotheses of `envelope_condition_dp` (concavity of
`v*`, differentiable reward, an optimal locally feasible policy, and the frozen-successor condition
`h_trans_frozen`), the derivative of the value function satisfies
`(v*)'(w₀) = ∂reward/∂w(w₀, a*(w₀))`.

Value-function differentiability on `O` is not assumed; it is derived internally by invoking
`envelope_condition_dp`. Because the optimal frozen action keeps the successor constant in the
current state, the continuation term contributes no derivative, so the envelope formula reduces to
the partial derivative of the reward in the state. -/
theorem envelope_deriv_dp (D : ConcaveDPData)
    {O : Set ℝ} (hO_open : IsOpen O)
    (hO_convex : Convex ℝ O)
    (hO_sub : O ⊆ D.domain)
    (h_reward_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.reward w' a) w)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    (ha_feasible :
      ∀ w ∈ O, a_star w ∈ D.toDetMDP.Γ w)
    (ha_locally_feasible : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀, a_star w₀ ∈ D.toDetMDP.Γ w)
    (ha_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
      D.toDetMDP.reward w a +
        D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (a_star w) +
        D.toDetMDP.β *
          v_star
            (D.toDetMDP.transition w (a_star w)))
    (h_trans_frozen : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀,
        D.toDetMDP.transition w (a_star w₀) =
          D.toDetMDP.transition w₀ (a_star w₀))
    (hv_bdd : UniformBounded v_star)
    (hv_fp : ∀ s,
      v_star s = D.toDetMDP.bellmanOperator v_star s)
    (hv_concave : ConcaveOn ℝ D.domain v_star)
    (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv v_star w₀ =
      deriv (fun w => D.toDetMDP.reward w (a_star w₀)) w₀ := by
  -- Value-function differentiability on `O` is derived from the headline envelope condition.
  have hv_diff : ∀ w ∈ O, DifferentiableAt ℝ v_star w :=
    envelope_condition_dp D hO_open hO_convex hO_sub h_reward_diff
      v_star a_star ha_feasible ha_optimal ha_locally_feasible h_trans_frozen
      hv_bdd hv_fp hv_concave
  set a₀ := a_star w₀ with ha₀_def
  set φ : ℝ → ℝ := fun w =>
    D.toDetMDP.reward w a₀ +
      D.toDetMDP.β * v_star (D.toDetMDP.transition w₀ a₀) with hφ_def
  have hrd := h_reward_diff w₀ a₀ hw₀ (ha_feasible w₀ hw₀)
  have hφ_diff : DifferentiableAt ℝ φ w₀ :=
    hrd.add (differentiableAt_const _)
  have hφ_eq : φ w₀ = v_star w₀ := by
    have hfp := hv_fp w₀
    unfold bellmanOperator at hfp
    have hle : φ w₀ ≤ v_star w₀ := by
      rw [hfp]
      exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w₀)
        ⟨a₀, ha_feasible w₀ hw₀, rfl⟩
    have hge : v_star w₀ ≤ φ w₀ := by
      rw [hfp]
      exact csSup_le
        (D.toDetMDP.bellmanSet_nonempty v_star w₀)
        (fun r ⟨a, ha, hr⟩ => hr ▸ ha_optimal w₀ hw₀ a ha)
    linarith
  have hφ_le : ∀ᶠ w in 𝓝 w₀, φ w ≤ v_star w := by
    filter_upwards [ha_locally_feasible w₀ hw₀, h_trans_frozen w₀ hw₀]
      with w ha₀_feasible h_frozen
    have hφw : φ w =
        D.toDetMDP.reward w a₀ +
          D.toDetMDP.β * v_star (D.toDetMDP.transition w a₀) := by
      change D.toDetMDP.reward w a₀ +
          D.toDetMDP.β * v_star (D.toDetMDP.transition w₀ a₀) = _
      rw [← h_frozen]
    have hfp := hv_fp w
    rw [hφw, hfp]; unfold bellmanOperator
    exact le_csSup
      (bellmanSet_bddAbove D.toDetMDP v_star hv_bdd w)
      ⟨a₀, ha₀_feasible, rfl⟩
  -- φ supports v* from below with equality at w₀, so their derivatives agree there.
  have h_deriv_eq : deriv v_star w₀ = deriv φ w₀ :=
    deriv_eq_of_eventuallyLE_of_eq v_star w₀ φ hφ_diff hφ_eq hφ_le
      (hv_diff w₀ hw₀)
  -- The continuation term in φ is constant in w, so deriv φ = deriv (reward · a₀).
  have hderiv_φ : deriv φ w₀ =
      deriv (fun w => D.toDetMDP.reward w a₀) w₀ := by
    rw [hφ_def]
    exact deriv_add_const _
  rw [h_deriv_eq, hderiv_φ]

/-- **Envelope condition under a state-independent transition.** When the transition does not
depend on the current state (`h_trans_indep`), the frozen-successor condition holds automatically,
so the envelope derivative `(v*)'(w₀) = ∂reward/∂w(w₀, a*(w₀))` is derived from concavity, a
differentiable reward, and an optimal locally feasible policy, with no successor-differentiability
of `v*` assumed. -/
theorem envelope_deriv_dp_of_transition_indep (D : ConcaveDPData)
    {O : Set ℝ} (hO_open : IsOpen O)
    (hO_convex : Convex ℝ O)
    (hO_sub : O ⊆ D.domain)
    (h_reward_diff :
      ∀ (w : ℝ) (a : ℝ), w ∈ O →
        a ∈ D.toDetMDP.Γ w →
        DifferentiableAt ℝ
          (fun w' => D.toDetMDP.reward w' a) w)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    (ha_feasible :
      ∀ w ∈ O, a_star w ∈ D.toDetMDP.Γ w)
    (ha_locally_feasible : ∀ w₀ ∈ O,
      ∀ᶠ w in 𝓝 w₀, a_star w₀ ∈ D.toDetMDP.Γ w)
    (ha_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
      D.toDetMDP.reward w a +
        D.toDetMDP.β *
          v_star (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (a_star w) +
        D.toDetMDP.β *
          v_star
            (D.toDetMDP.transition w (a_star w)))
    (h_trans_indep : ∀ (a w w' : ℝ),
      D.toDetMDP.transition w a = D.toDetMDP.transition w' a)
    (hv_bdd : UniformBounded v_star)
    (hv_fp : ∀ s,
      v_star s = D.toDetMDP.bellmanOperator v_star s)
    (hv_concave : ConcaveOn ℝ D.domain v_star)
    (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv v_star w₀ =
      deriv (fun w => D.toDetMDP.reward w (a_star w₀)) w₀ :=
  envelope_deriv_dp D hO_open hO_convex hO_sub h_reward_diff v_star a_star ha_feasible
    ha_locally_feasible ha_optimal
    (fun w₀' _ => Filter.Eventually.of_forall
      (fun w => h_trans_indep (a_star w₀') w w₀'))
    hv_bdd hv_fp hv_concave w₀ hw₀

/-! ## Consumption Model Specialization -/

/-- **Envelope condition for consumption DP.** When the reward decomposes as `u(c)` with
`c = w - g(a)`, the derivative of the value function satisfies `(v*)'(w) = u'(w - g(a*(w)))`.

Differentiability of `v*` is not assumed: Because the optimal action freezes the successor state
`f_prod (a*(w₀))` to a constant in the current state `w`, the support function is differentiable
from `u` alone. Differentiability of `v*` is then derived from concavity (`hv_concave`) together
with differentiability of `u` via `ConcaveOn.differentiableAt_of_support`, requiring no
successor-differentiability of `v*`. -/
theorem envelope_condition_consumption
    (u : ℝ → ℝ) (g : ℝ → ℝ) (f_prod : ℝ → ℝ)
    (hu_diff : Differentiable ℝ u)
    -- Strict monotonicity of `u`; fixes the economic contract even though unused in this proof.
    (_hu_pos : ∀ c, 0 < deriv u c)
    -- Differentiability of `g` and `f_prod`; part of standard DP smoothness assumptions.
    (_hg_diff : Differentiable ℝ g)
    (_hf_diff : Differentiable ℝ f_prod)
    -- Discount factor bounds; part of standard DP assumptions, ensures fixed-point exists.
    (β : ℝ) (_hβ_nonneg : 0 ≤ β) (_hβ_lt_one : β < 1)
    (v_star : ℝ → ℝ) (a_star : ℝ → ℝ)
    -- Concavity of the value function: a primitive Benveniste-Scheinkman input. Together with
    -- `u`'s differentiability it yields differentiability of `v*` via the support argument; no
    -- successor-differentiability of `v*` is needed because the frozen action makes the
    -- successor state `f_prod (a*(w₀))` constant in the current state `w`.
    (hv_concave : ConcaveOn ℝ Set.univ v_star)
    -- Bellman equation
    (hv_bellman : ∀ w,
      v_star w = u (w - g (a_star w)) +
        β * v_star (f_prod (a_star w)))
    -- Optimality: a*(w) maximizes the Bellman objective
    (ha_optimal : ∀ w a,
      u (w - g a) + β * v_star (f_prod a) ≤ v_star w)
    (w₀ : ℝ) :
    deriv v_star w₀ =
      deriv u (w₀ - g (a_star w₀)) := by
  -- φ_{w'}(w) = u(w - g(a*(w'))) + β v*(f(a*(w'))) freezes the action at a*(w'); the successor
  -- f_prod(a*(w')) is then constant in w, so the support is differentiable from u alone.
  -- It touches v* from below with equality at w', so v* is differentiable there.
  have h_support : ∀ w' ∈ (Set.univ : Set ℝ), ∃ ψ : ℝ → ℝ,
      DifferentiableAt ℝ ψ w' ∧ ψ w' = v_star w' ∧ ∀ᶠ w in 𝓝 w', ψ w ≤ v_star w := by
    intro w' _
    refine ⟨fun w => u (w - g (a_star w')) + β * v_star (f_prod (a_star w')), ?_,
      (hv_bellman w').symm, Filter.Eventually.of_forall (fun w => ha_optimal w (a_star w'))⟩
    exact (hu_diff.differentiableAt.comp w'
      (differentiableAt_id.sub (differentiableAt_const _))).add (differentiableAt_const _)
  -- Differentiability of v* on all of ℝ is derived from concavity + the support, via B-S.
  have hv_diff_w₀ : DifferentiableAt ℝ v_star w₀ :=
    ConcaveOn.differentiableAt_of_support isOpen_univ convex_univ v_star hv_concave
      h_support w₀ (Set.mem_univ w₀)
  -- φ(w) = u(w - g(a₀)) + β v*(f(a₀)) with a₀ = a*(w₀) frozen touches v* from below at w₀,
  -- so (v* - φ) has a local minimum there and its derivative vanishes.
  set a₀ := a_star w₀
  set φ : ℝ → ℝ := fun w =>
    u (w - g a₀) + β * v_star (f_prod a₀)
  have hφ_eq : φ w₀ = v_star w₀ := (hv_bellman w₀).symm
  have hφ_le : ∀ w, φ w ≤ v_star w :=
    fun w => ha_optimal w a₀
  have hφ_diff : DifferentiableAt ℝ φ w₀ :=
    (hu_diff.differentiableAt.comp w₀
      (differentiableAt_id.sub
        (differentiableAt_const _))).add
      (differentiableAt_const _)
  -- φ supports v* from below with equality at w₀, so their derivatives agree there.
  have h_deriv_eq : deriv v_star w₀ = deriv φ w₀ :=
    deriv_eq_of_eventuallyLE_of_eq v_star w₀ φ hφ_diff hφ_eq
      (Filter.Eventually.of_forall hφ_le) hv_diff_w₀
  have hderiv_φ :
      deriv φ w₀ = deriv u (w₀ - g a₀) := by
    have hsub : HasDerivAt (fun w => w - g a₀) 1 w₀ := by
      have h := (hasDerivAt_id w₀).sub (hasDerivAt_const w₀ (g a₀))
      simp only [sub_zero] at h; exact h
    have hcomp : HasDerivAt (fun w => u (w - g a₀)) (deriv u (w₀ - g a₀)) w₀ := by
      have h := (hu_diff _).hasDerivAt.comp w₀ hsub
      simp only [mul_one] at h; exact h
    exact (hcomp.add (hasDerivAt_const w₀ _)).deriv.trans (by ring)
  rw [h_deriv_eq, hderiv_φ]

end Econlib.Optimization.DynamicProgramming
