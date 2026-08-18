/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# The Benveniste-Scheinkman Envelope Condition: A Worked Growth Example

A worked example exercising the **headline** Benveniste-Scheinkman envelope condition
(`Econlib.Optimization.DynamicProgramming.envelope_deriv_dp_of_transition_indep`), where
value-function differentiability is *derived* from primitive data rather than assumed.

This file proves no new general-purpose theorem. It supplies a concrete `ConcaveDPData` in the
canonical "next state as control" formulation (the transition does not depend on the current
state), solves its Bellman equation in closed form, and checks that all the envelope-condition
hypotheses hold — in particular the structural condition `h_trans_indep` that the transition
ignores the current state, which is what makes differentiability derivable with *no*
successor-differentiability assumption.

## The model

A bounded one-dimensional accumulation program on the capital interval `[0, 1]`:

* State `w : ℝ` — the capital stock, restricted to the domain `[0, 1]`.
* Action `a : ℝ` — next period's capital, freely chosen in `Γ(w) = [0, 1]` (next state as control).
* Reward `reward(w, a) = arctan w + arctan a` — bounded felicity, jointly concave on `[0,1]²` and
  `C¹` in the current state `w`.
* Transition `f(w, a) = a` — the chosen control is next period's state; it does not depend on the
  current state `w`, so the frozen-successor condition `h_trans_indep` holds.
* Discount `β = 1/2 ∈ [0, 1)`.

`arctan` is used because it is the canonical globally bounded, smooth, concave-on-`[0,∞)` felicity:
The `DetMDP` reward bound and the value bound `UniformBounded` both need a *global* bound, which a
linear or quadratic felicity could not provide.

## The mathematics

Because the felicity is increasing in next capital and discounting makes the continuation strictly
contractive, it is optimal to accumulate the maximal feasible stock: `a*(w) = 1`. The closed-form
value is `v*(w) = arctan w + 3π/4`, which solves the Bellman equation `v* = T v*` (the one-step
supremum `sup_{a∈[0,1]} [arctan w + arctan a + ½ v*(a)]` has greatest element at `a = 1`).

The headline envelope condition then *derives* differentiability of `v*` on the open interior
`(0,1)` and yields the envelope derivative

`(v*)'(w₀) = ∂reward/∂w (w₀, a*(w₀)) = arctan'(w₀) = 1 / (1 + w₀²)`,

matching the direct derivative of the closed form. No successor-differentiability of `v*` is
assumed anywhere.

## Main definitions and theorems

* `D : ConcaveDPData` — the bounded `arctan` accumulation program.
* `vStar : ℝ → ℝ` — the closed-form value `w ↦ arctan w + 3π/4`.
* `aStar : ℝ → ℝ` — the one-step Bellman maximizer `w ↦ 1` (accumulate to the cap).
* `vStar_eq_bellman` — the Bellman fixed-point identity `v* = T v*`.
* `deriv_vStar` — the headline result: For `w₀ ∈ (0,1)`, `(v*)'(w₀) = 1 / (1 + w₀²)`, obtained by
  instantiating the *derived* envelope condition.
-/

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Filter Topology UnboundedDetMDP Blackwell
open Real Set

namespace EconlibExamples.EnvelopeGrowth

/-! ## The bounded `arctan` accumulation program -/

/-- `arctan` is concave on the capital interval `[0, 1]`: It restricts the nonnegative-reals
concavity `Real.arctan_concaveOn_nonneg`. This is the one-dimensional concavity that powers both
`reward_concave` and `hv_concave`. -/
lemma arctan_concaveOn_Icc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) Real.arctan :=
  Real.arctan_concaveOn_nonneg.subset Set.Icc_subset_Ici_self (convex_Icc 0 1)

/-- The bounded `arctan` accumulation program as a `ConcaveDPData`. -/
noncomputable def D : ConcaveDPData where
  Γ _ := Set.Icc (0:ℝ) 1
  reward w a := Real.arctan w + Real.arctan a
  transition _ a := a
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty _ := ⟨0, by norm_num⟩
  reward_bounded := by
    -- |arctan w + arctan a| ≤ |arctan w| + |arctan a| ≤ π/2 + π/2 = π, so π is a global bound.
    refine ⟨Real.pi, fun s a => ?_⟩
    have hsa : |Real.arctan s| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two s
    have haa : |Real.arctan a| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two a
    calc |Real.arctan s + Real.arctan a|
        ≤ |Real.arctan s| + |Real.arctan a| := abs_add_le _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add hsa haa
      _ = Real.pi := by ring
  domain := Set.Icc (0:ℝ) 1
  domain_convex := convex_Icc 0 1
  Γ_graph_convex := by
    intro w w' a a' α _ _ ha ha' hα0 hα1
    simp only [smul_eq_mul] at *
    rw [Set.mem_Icc] at ha ha' ⊢
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨ha'0, ha'1⟩ := ha'
    constructor
    · nlinarith [ha0, ha'0, hα0, hα1]
    · nlinarith [ha1, ha'1, hα0, hα1]
  reward_concave := by
    -- `(p ↦ arctan p.1) + (p ↦ arctan p.2)`, each concave on the box `[0,1]²` via the
    -- `ConcaveDPData.concaveOn_fst`/`concaveOn_snd` projection lifts of `arctan_concaveOn_Icc`.
    have hconv := ConcaveDPData.convex_graph_const (convex_Icc (0:ℝ) 1) (convex_Icc (0:ℝ) 1)
    exact (ConcaveDPData.concaveOn_fst hconv arctan_concaveOn_Icc fun _ hp => hp.1).add
      (ConcaveDPData.concaveOn_snd hconv arctan_concaveOn_Icc fun _ hp => hp.2)
  transition_concave :=
    (ConcaveDPData.concaveOn_convexOn_of_eqOn_linearMap
      (ConcaveDPData.convex_graph_const (convex_Icc (0:ℝ) 1) (convex_Icc (0:ℝ) 1))
      (LinearMap.snd ℝ ℝ ℝ) fun _ _ => rfl).1
  transition_convex :=
    (ConcaveDPData.concaveOn_convexOn_of_eqOn_linearMap
      (ConcaveDPData.convex_graph_const (convex_Icc (0:ℝ) 1) (convex_Icc (0:ℝ) 1))
      (LinearMap.snd ℝ ℝ ℝ) fun _ _ => rfl).2
  transition_domain := by
    intro w _ a ha
    exact ha

/-- The closed-form value function `v*(w) = arctan w + 3π/4`. -/
noncomputable def vStar : ℝ → ℝ := fun w => Real.arctan w + 3 * Real.pi / 4

/-- The stationary policy that maximizes the one-step Bellman objective: Accumulate to the cap,
`a*(w) = 1` (`aStar_optimal`). It is this one-step maximality — not a separately proved
infinite-horizon optimality — that the envelope condition consumes; the policy is here to pin the
active constraint `a*(w₀)` at which the value derivative is read off. -/
noncomputable def aStar : ℝ → ℝ := fun _ => 1

/-- The open interior `(0,1)` on which differentiability is derived. -/
def O : Set ℝ := Set.Ioo (0:ℝ) 1

/-! ## Closed-form solution and hypotheses -/

/-- **Bellman fixed-point identity.** `v*(w) = arctan w + 3π/4` solves `v* = T v*`. The one-step
problem `sup_{a∈[0,1]} [arctan w + arctan a + ½ v*(a)]` has greatest element at `a = 1`, since the
objective is increasing in `a` and `arctan a ≤ arctan 1`. -/
theorem vStar_eq_bellman : ∀ s, vStar s = D.toDetMDP.bellmanOperator vStar s := by
  intro s
  have hgreatest : IsGreatest (D.toDetMDP.bellmanSet vStar s) (vStar s) := by
    constructor
    · -- Membership: the maximizer `a = 1`.
      refine ⟨1, ?_, ?_⟩
      all_goals simp only [D, one_div, vStar]
      · -- `1 ∈ Γ s = [0,1]`.
        exact Set.mem_Icc.mpr ⟨by norm_num, le_refl _⟩
      · -- vStar s = arctan s + arctan 1 + (1/2) * vStar 1; uses `arctan 1 = π/4`.
        rw [Real.arctan_one]; ring
    · -- Upper bound: `arctan a ≤ arctan 1` for `a ≤ 1`.
      rintro r ⟨a, ⟨_, ha_le⟩, rfl⟩
      -- objective `arctan s + arctan a + ½(arctan a + 3π/4)` is increasing in `a`.
      simp only [D, one_div, vStar]
      nlinarith [Real.arctan_one, Real.arctan_mono ha_le]
  rw [UnboundedDetMDP.bellmanOperator_eq, hgreatest.csSup_eq]

/-- `v*` is concave on the domain `[0, 1]`: It is `arctan` (concave there) plus a constant. -/
theorem vStar_concave : ConcaveOn ℝ D.domain vStar :=
  arctan_concaveOn_Icc.add_const (3 * Real.pi / 4)

/-- `v*` is uniformly bounded: `|v*(w)| ≤ 2π`. -/
theorem vStar_bounded : UniformBounded vStar := by
  refine ⟨2 * Real.pi, fun w => ?_⟩
  have hw : |Real.arctan w| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two w
  have hpi : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have habs : |3 * Real.pi / 4| = 3 * Real.pi / 4 := abs_of_nonneg (by positivity)
  calc |Real.arctan w + 3 * Real.pi / 4|
      ≤ |Real.arctan w| + |3 * Real.pi / 4| := abs_add_le _ _
    _ = |Real.arctan w| + 3 * Real.pi / 4 := by rw [habs]
    _ ≤ Real.pi / 2 + 3 * Real.pi / 4 := by linarith [hw]
    _ ≤ 2 * Real.pi := by linarith [hpi]

/-- The reward is `C¹` in the current state: `w ↦ arctan w + arctan a` is differentiable. -/
-- The hypotheses `w ∈ O` and `a ∈ Γ w` are required by the `h_reward_diff` API of the
-- envelope theorem; `arctan` is differentiable everywhere so neither is used in the proof body.
theorem reward_diff (w a : ℝ) (_ : w ∈ O) (_ : a ∈ D.toDetMDP.Γ w) :
    DifferentiableAt ℝ (fun w' => D.toDetMDP.reward w' a) w := by
  exact (Real.differentiableAt_arctan w).add (differentiableAt_const _)

/-- The policy `a*(w) = 1` is feasible. -/
theorem aStar_feasible : ∀ w ∈ O, aStar w ∈ D.toDetMDP.Γ w := by
  intro w _
  exact Set.right_mem_Icc.mpr zero_le_one

/-- The policy `a*(w) = 1` stays feasible for nearby states (trivially: `1 ∈ [0,1]` always). -/
theorem aStar_locally_feasible : ∀ w₀ ∈ O, ∀ᶠ w in 𝓝 w₀, aStar w₀ ∈ D.toDetMDP.Γ w := by
  intro w₀ _
  refine Filter.Eventually.of_forall (fun w => ?_)
  exact Set.right_mem_Icc.mpr zero_le_one

/-- `a*(w) = 1` maximizes the one-step Bellman objective. -/
theorem aStar_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
    D.toDetMDP.reward w a + D.toDetMDP.β * vStar (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (aStar w) +
        D.toDetMDP.β * vStar (D.toDetMDP.transition w (aStar w)) := by
  -- The objective `arctan w + (3/2) arctan a + const` is increasing in `a`, maximal at `a = 1`.
  intro w _ a ha
  have ha_le : a ≤ 1 := (Set.mem_Icc.mp ha).2
  simp only [D, one_div, vStar, aStar, arctan_one, ge_iff_le]
  nlinarith [Real.arctan_one, Real.arctan_mono ha_le]

/-- The transition `f(w, a) = a` does not depend on the current state. -/
theorem transition_indep (a w w' : ℝ) :
    D.toDetMDP.transition w a = D.toDetMDP.transition w' a := rfl

/-! ## The derived envelope condition -/

/-- **Headline result.** For every interior capital level `w₀ ∈ (0, 1)`, the value-function
derivative is `(v*)'(w₀) = 1 / (1 + w₀²)`.

This is obtained purely from primitive data (concavity of `v*`, `C¹` reward, an optimal locally
feasible policy, and the state-independent transition) by instantiating
`envelope_deriv_dp_of_transition_indep`. Differentiability of `v*` is not assumed: It is derived
by the Benveniste-Scheinkman support argument, and the continuation term contributes no derivative
because the transition is state-independent, collapsing the envelope formula to the marginal
felicity of current capital `arctan'(w₀) = 1 / (1 + w₀²)`. -/
theorem deriv_vStar (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv vStar w₀ = 1 / (1 + w₀ ^ 2) := by
  have hO_open : IsOpen O := isOpen_Ioo
  have hO_convex : Convex ℝ O := convex_Ioo 0 1
  have hO_sub : O ⊆ D.domain := Set.Ioo_subset_Icc_self
  -- The derived envelope formula: deriv v* w₀ = deriv (fun w => reward w (a*(w₀))) w₀.
  have h_env : deriv vStar w₀ =
      deriv (fun w => D.toDetMDP.reward w (aStar w₀)) w₀ :=
    envelope_deriv_dp_of_transition_indep D hO_open hO_convex hO_sub reward_diff
      vStar aStar aStar_feasible aStar_locally_feasible aStar_optimal transition_indep
      vStar_bounded vStar_eq_bellman vStar_concave w₀ hw₀
  rw [h_env]
  exact ((Real.hasDerivAt_arctan w₀).add_const (Real.arctan (aStar w₀))).deriv

end EconlibExamples.EnvelopeGrowth
