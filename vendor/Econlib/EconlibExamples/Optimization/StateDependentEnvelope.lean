/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# The Benveniste-Scheinkman Envelope Condition with a State-Dependent Transition

A second worked example exercising the general Benveniste-Scheinkman envelope theorem
`Econlib.Optimization.DynamicProgramming.envelope_deriv_dp_of_diffSucc`, complementing the
state-*independent* `arctan` accumulation model of `EnvelopeGrowth`. Here the transition
depends on the current state, so the discounted continuation chain term

`β · (v*)'(f(w₀, a*(w₀))) · ∂f/∂w (w₀, a*(w₀))`

does not vanish: `∂f/∂w = 1/2 ≠ 0`, and the envelope identity holds with a live multiplier,
so a sign error in the continuation derivative would break the closed-form match.

## The model

A bounded one-dimensional accumulation program on the capital interval `[1, 2]`:

* State `w : ℝ` — capital, restricted to `[1, 2]`.
* Action `a : ℝ` — investment intensity, chosen in `Γ(w) = [1, 2]`.
* Transition `f(w, a) = (w + a)/2` — the next state is the **midpoint** of current capital and the
  action. This is affine and **state-dependent** (`∂f/∂w = 1/2`), the feature that
  distinguishes this example from `EnvelopeGrowth` (where `f(w,a) = a`). It maps `[1,2]² → [1,2]`.
* Reward `r(w, a) = arctan w − ½·arctan((w+2)/2) + arctan a − arctan 2` — bounded, jointly concave
  on `[1,2]²`, and `C¹` in `w`. The `−½·arctan((w+2)/2)` term is the continuation *compensator*
  that makes the closed form below an exact Bellman fixed point.
* Discount `β = 1/2 ∈ [0, 1)`.

## The mathematics

Because the `a`-dependent part `arctan a + ½·arctan((w+a)/2)` is increasing in `a`, the one-step
objective is maximized at the cap `a*(w) = 2`. At that policy the compensator exactly cancels the
continuation, so the closed-form value `v*(w) = arctan w` solves the Bellman equation `v* = T v*`:
`sup_{a∈[1,2]} [r(w,a) + ½·v*((w+a)/2)] = arctan w`, with greatest element at `a = 2`.

The headline envelope theorem `envelope_deriv_dp_of_diffSucc` then gives the value derivative as the
marginal current-period return **plus** the discounted continuation chain term:

`(v*)'(w₀) = ∂r/∂w(w₀, 2) + β·(v*)'((w₀+2)/2)·∂f/∂w(w₀, 2)`
          `= [1/(1+w₀²) − ¼/(1+((w₀+2)/2)²)] + [¼/(1+((w₀+2)/2)²)] = 1/(1+w₀²)`,

matching the direct derivative `arctan'(w₀)`. Unlike `EnvelopeGrowth`, the chain term is **nonzero**
and cancels the compensator's contribution rather than vanishing factor-by-factor.

## Main definitions and theorems

* `D : ConcaveDPData` — the bounded midpoint accumulation program.
* `vStar : ℝ → ℝ` — the closed-form value `w ↦ arctan w`.
* `aStar : ℝ → ℝ` — the one-step Bellman maximizer `w ↦ 2`.
* `vStar_eq_bellman` — the Bellman fixed-point identity `v* = T v*`.
* `vStar_envelope_diffSucc` — the full Benveniste-Scheinkman identity with the live chain term.
* `trans_deriv_eq` — the **nonzero** transition state-derivative `∂f/∂w(w₀, 2) = 1/2`.
* `deriv_vStar` — the headline result `(v*)'(w₀) = 1/(1+w₀²)` on `(1,2)`, obtained by collapsing the
  chain identity (continuation term cancels the compensator, not vanishes).
-/

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Filter Topology UnboundedDetMDP Blackwell
open Real Set

namespace EconlibExamples.StateDependentEnvelope

/-! ## Concavity of the reward's state-dependent part -/

/-- `arctan` is concave on the capital interval `[1, 2]`: It restricts the nonnegative-reals
concavity `Real.arctan_concaveOn_nonneg`. Powers the `arctan a` summand of the reward and the
concavity of `v*`. -/
lemma arctan_concaveOn_Icc12 : ConcaveOn ℝ (Set.Icc (1:ℝ) 2) Real.arctan :=
  Real.arctan_concaveOn_nonneg.subset (fun _ hx => le_trans zero_le_one hx.1) (convex_Icc 1 2)

/-- The state-dependent part of the reward, `f₁(w) = arctan w − ½·arctan((w+2)/2)`. Its derivative
is `f₁'(w) = 1/(1+w²) − ¼/(1+((w+2)/2)²)` and its second derivative is
`f₁''(w) = −2w/(1+w²)² + ((w+2)/2)/(4·(1+((w+2)/2)²)²)`. -/
noncomputable def f1 : ℝ → ℝ := fun w => Real.arctan w - (1/2) * Real.arctan ((w + 2) / 2)

/-- The first derivative of `f₁`, as an explicit function. -/
noncomputable def f1' : ℝ → ℝ :=
  fun w => 1 / (1 + w ^ 2) - (1/2) * ((1 / (1 + ((w + 2) / 2) ^ 2)) * (1/2))

/-- The second derivative of `f₁`, as an explicit function. -/
noncomputable def f1'' : ℝ → ℝ :=
  fun w => -(2 * w) / (1 + w ^ 2) ^ 2 -
    (1/2) * ((-(2 * ((w + 2) / 2)) / (1 + ((w + 2) / 2) ^ 2) ^ 2) * (1/2) * (1/2))

/-- `f₁` has derivative `f₁'` at every point. -/
lemma hasDerivAt_f1 (w : ℝ) : HasDerivAt f1 (f1' w) w := by
  have ha : HasDerivAt Real.arctan (1 / (1 + w ^ 2)) w := Real.hasDerivAt_arctan w
  have hu : HasDerivAt (fun w => (w + 2) / 2) (1/2) w := by
    simpa using (((hasDerivAt_id w).add_const 2).div_const 2)
  have hb : HasDerivAt (fun w => Real.arctan ((w + 2) / 2))
      ((1 / (1 + ((w + 2) / 2) ^ 2)) * (1/2)) w := by
    simpa [Function.comp_def] using (Real.hasDerivAt_arctan ((w + 2) / 2)).comp w hu
  exact ha.sub (hb.const_mul (1/2))

/-- `f₁'` has derivative `f₁''` at every point. -/
lemma hasDerivAt_f1' (w : ℝ) : HasDerivAt f1' (f1'' w) w := by
  -- d/dw [1/(1+w²)] = −2w/(1+w²)²
  have h1 : HasDerivAt (fun w => 1 / (1 + w ^ 2)) (-(2 * w) / (1 + w ^ 2) ^ 2) w := by
    have hden : HasDerivAt (fun w : ℝ => 1 + w ^ 2) (2 * w) w := by
      simpa using (hasDerivAt_pow 2 w).const_add 1
    have hne : (1 + w ^ 2) ≠ 0 := by positivity
    have := (hden.inv hne)
    -- (1/(1+w²))' = −(2w)/(1+w²)²
    simpa [one_div, neg_div] using this
  -- d/dw [1/(1+((w+2)/2)²)] = −(2·((w+2)/2))/(1+((w+2)/2)²)² · (1/2)
  have h2 : HasDerivAt (fun w => 1 / (1 + ((w + 2) / 2) ^ 2))
      ((-(2 * ((w + 2) / 2)) / (1 + ((w + 2) / 2) ^ 2) ^ 2) * (1/2)) w := by
    have hu : HasDerivAt (fun w => (w + 2) / 2) (1/2) w := by
      simpa using (((hasDerivAt_id w).add_const 2).div_const 2)
    have hden : HasDerivAt (fun w : ℝ => 1 + ((w + 2) / 2) ^ 2)
        (2 * ((w + 2) / 2) * (1/2)) w := by
      have := (hu.pow 2)
      simpa using this.const_add 1
    have hne : (1 + ((w + 2) / 2) ^ 2) ≠ 0 := by positivity
    have hinv := hden.inv hne
    -- rearrange to the stated factored form
    have : HasDerivAt (fun w => 1 / (1 + ((w + 2) / 2) ^ 2))
        (-(2 * ((w + 2) / 2) * (1/2)) / (1 + ((w + 2) / 2) ^ 2) ^ 2) w := by
      simpa [one_div, neg_div] using hinv
    convert this using 1
    ring
  -- `f1'` equals `w ↦ 1/(1+w²) − ¼·(1/(1+((w+2)/2)²))`, the function whose derivative we computed.
  have hfeq : f1' = fun w => 1 / (1 + w ^ 2) - (1/4) * (1 / (1 + ((w + 2) / 2) ^ 2)) := by
    funext y; simp only [f1']; ring
  rw [hfeq]
  have hsub := h1.sub (h2.const_mul (1/4))
  convert hsub using 1
  simp only [f1'']
  ring

/-- `deriv f₁ = f₁'` everywhere. -/
lemma deriv_f1 : deriv f1 = f1' := funext fun w => (hasDerivAt_f1 w).deriv

/-- **`f₁` is concave on `[1, 2]`.** Its second derivative `f₁''(w) < 0` on `(1, 2)`: clearing the
(positive) denominators, this is `8w·(1+((w+2)/2)²)² > ((w+2)/2)·(1+w²)²`, which holds with a large
margin since `arctan` is strongly concave on `[1,2]` while the `½·arctan((w+2)/2)` perturbation has
half the slope and a milder curvature. -/
lemma f1_concaveOn : ConcaveOn ℝ (Set.Icc (1:ℝ) 2) f1 := by
  refine (strictConcaveOn_of_deriv2_neg' (convex_Icc 1 2) ?_ ?_).concaveOn
  · -- continuity of f₁ on [1,2]
    exact (Real.continuous_arctan.sub
      (continuous_const.mul (Real.continuous_arctan.comp
        (by continuity)))).continuousOn
  · -- second derivative strictly negative on the closed interval `[1, 2]`
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    -- deriv^[2] f₁ x = deriv f₁' x = f₁'' x
    have hdd : deriv^[2] f1 x = f1'' x := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
        deriv_f1]
      exact (hasDerivAt_f1' x).deriv
    rw [hdd]
    have hx0 : (0:ℝ) < x := by linarith
    have hu : (0:ℝ) < (x + 2) / 2 := by linarith
    have hdw : (0:ℝ) < (1 + x ^ 2) ^ 2 := by positivity
    have hduu : (0:ℝ) < (1 + ((x + 2) / 2) ^ 2) ^ 2 := by positivity
    -- Combine `f₁''(x)` over the common positive denominator `4(1+x²)²(1+((x+2)/2)²)²`; the
    -- numerator is `(x+2)/2·(1+x²)² − 8x·(1+((x+2)/2)²)² < 0`, with a large margin on `[1,2]`
    -- (`−78.5` at `x=1`, `−350` at `x=2`).
    have hnum : ((x + 2) / 2) * (1 + x ^ 2) ^ 2 - 8 * x * (1 + ((x + 2) / 2) ^ 2) ^ 2 < 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg x, sq_nonneg (x ^ 2 - 1),
        hx1, hx2, hx0, mul_pos hx0 hx0]
    have hf1'' : f1'' x =
        (((x + 2) / 2) * (1 + x ^ 2) ^ 2 - 8 * x * (1 + ((x + 2) / 2) ^ 2) ^ 2) /
          (4 * (1 + x ^ 2) ^ 2 * (1 + ((x + 2) / 2) ^ 2) ^ 2) := by
      simp only [f1'']
      field_simp
      ring
    rw [hf1'']
    exact div_neg_of_neg_of_pos hnum (by positivity)

/-! ## The bounded midpoint accumulation program -/

/-- The bounded midpoint accumulation program as a `ConcaveDPData`. -/
noncomputable def D : ConcaveDPData where
  Γ _ := Set.Icc (1:ℝ) 2
  reward w a := Real.arctan w - (1/2) * Real.arctan ((w + 2) / 2) + Real.arctan a - Real.arctan 2
  transition w a := (w + a) / 2
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty _ := ⟨1, by norm_num⟩
  reward_bounded := by
    -- Each `arctan` term has `|·| ≤ π/2`; with the `½` weight on the second, the four terms sum to
    -- at most `π/2 + π/4 + π/2 + π/2 = 7π/4 ≤ 2π`.
    refine ⟨2 * Real.pi, fun s a => ?_⟩
    have hs : |Real.arctan s| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two s
    have hsu : |Real.arctan ((s + 2) / 2)| ≤ Real.pi / 2 :=
      Real.abs_arctan_le_pi_div_two ((s + 2) / 2)
    have ha : |Real.arctan a| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two a
    have h2 : |Real.arctan 2| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two 2
    have hpi : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    calc |Real.arctan s - (1/2) * Real.arctan ((s + 2) / 2) + Real.arctan a - Real.arctan 2|
        ≤ |Real.arctan s - (1/2) * Real.arctan ((s + 2) / 2) + Real.arctan a| + |Real.arctan 2| :=
          abs_sub _ _
      _ ≤ (|Real.arctan s - (1/2) * Real.arctan ((s + 2) / 2)| + |Real.arctan a|) +
            |Real.arctan 2| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|Real.arctan s| + |(1/2) * Real.arctan ((s + 2) / 2)|) + |Real.arctan a|) +
            |Real.arctan 2| := by gcongr; exact abs_sub _ _
      _ = ((|Real.arctan s| + (1/2) * |Real.arctan ((s + 2) / 2)|) + |Real.arctan a|) +
            |Real.arctan 2| := by rw [abs_mul]; norm_num
      _ ≤ ((Real.pi / 2 + (1/2) * (Real.pi / 2)) + Real.pi / 2) + Real.pi / 2 := by
            gcongr
      _ ≤ 2 * Real.pi := by linarith
  domain := Set.Icc (1:ℝ) 2
  domain_convex := convex_Icc 1 2
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
    -- `reward p.1 p.2 = f₁(p.1) + (arctan p.2 − arctan 2)`, a sum of a concave function of `p.1`
    -- and a concave function of `p.2`, each lifted to the box `[1,2]²` via the
    -- `ConcaveDPData.concaveOn_fst`/`concaveOn_snd` projection helpers.
    have hconv := ConcaveDPData.convex_graph_const (convex_Icc (1:ℝ) 2) (convex_Icc (1:ℝ) 2)
    have hsum := (ConcaveDPData.concaveOn_fst hconv f1_concaveOn fun _ hp => hp.1).add
      (ConcaveDPData.concaveOn_snd hconv (arctan_concaveOn_Icc12.add_const (-Real.arctan 2))
        fun _ hp => hp.2)
    convert hsum using 1
    funext p
    simp only [f1, Pi.add_apply]
    ring
  transition_concave :=
    -- `transition p.1 p.2 = (p.1 + p.2)/2` agrees with the linear map `½·fst + ½·snd`, so affine.
    (ConcaveDPData.concaveOn_convexOn_of_eqOn_linearMap
      (ConcaveDPData.convex_graph_const (convex_Icc (1:ℝ) 2) (convex_Icc (1:ℝ) 2))
      ((1/2 : ℝ) • LinearMap.fst ℝ ℝ ℝ + (1/2 : ℝ) • LinearMap.snd ℝ ℝ ℝ) fun p _ => by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, smul_eq_mul]; ring).1
  transition_convex :=
    (ConcaveDPData.concaveOn_convexOn_of_eqOn_linearMap
      (ConcaveDPData.convex_graph_const (convex_Icc (1:ℝ) 2) (convex_Icc (1:ℝ) 2))
      ((1/2 : ℝ) • LinearMap.fst ℝ ℝ ℝ + (1/2 : ℝ) • LinearMap.snd ℝ ℝ ℝ) fun p _ => by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, smul_eq_mul]; ring).2
  transition_domain := by
    -- `w ∈ [1,2], a ∈ [1,2] ⟹ (w+a)/2 ∈ [1,2]`.
    intro w hw a ha
    rw [Set.mem_Icc] at hw ha ⊢
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨ha1, ha2⟩ := ha
    constructor <;> linarith
/-- The closed-form value function `v*(w) = arctan w`. -/
noncomputable def vStar : ℝ → ℝ := fun w => Real.arctan w

/-- The stationary policy that maximizes the one-step Bellman objective: invest at the cap,
`a*(w) = 2` (`aStar_optimal`). The one-step objective is increasing in `a`, so the maximum is the
right endpoint; the policy fixes the active constraint `a*(w₀) = 2` at which the value derivative
and the live continuation chain term are read off. -/
noncomputable def aStar : ℝ → ℝ := fun _ => 2

/-- The open interior `(1, 2)` on which the envelope identity is read off. -/
def O : Set ℝ := Set.Ioo (1:ℝ) 2

/-! ## Closed-form solution and hypotheses -/

/-- **Bellman fixed-point identity.** `v*(w) = arctan w` solves `v* = T v*`. At the maximizer
`a = 2` the continuation compensator `−½·arctan((w+2)/2)` exactly cancels `½·v*((w+2)/2)` and
`arctan 2 − arctan 2 = 0`, leaving `arctan w`. For `a ∈ [1,2]` the objective is bounded above by
this value (`arctan a ≤ arctan 2` and `arctan((w+a)/2) ≤ arctan((w+2)/2)`), so `a = 2` is the
greatest element. -/
theorem vStar_eq_bellman : ∀ s, vStar s = D.toDetMDP.bellmanOperator vStar s := by
  intro s
  have hgreatest : IsGreatest (D.toDetMDP.bellmanSet vStar s) (vStar s) := by
    constructor
    · -- Membership: the maximizer `a = 2`, where the compensator cancels the continuation.
      refine ⟨2, ?_, ?_⟩
      · -- `2 ∈ Γ s = [1,2]`.
        simp only [D]
        exact Set.mem_Icc.mpr ⟨by norm_num, le_refl _⟩
      · -- `vStar s = reward s 2 + ½·vStar((s+2)/2)`; the `±½·arctan((s+2)/2)` terms cancel.
        simp only [D, vStar]
        ring
    · -- Upper bound: the objective is increasing in `a`, maximal at `a = 2`.
      rintro r ⟨a, ⟨_, ha_le⟩, rfl⟩
      simp only [D, vStar]
      have ha2 : Real.arctan a ≤ Real.arctan 2 := Real.arctan_mono ha_le
      have hmid : Real.arctan ((s + a) / 2) ≤ Real.arctan ((s + 2) / 2) :=
        Real.arctan_mono (by linarith)
      nlinarith [ha2, hmid]
  rw [UnboundedDetMDP.bellmanOperator_eq, hgreatest.csSup_eq]

/-- `v*` is concave on the domain `[1, 2]`: it is exactly `arctan`, concave there. -/
theorem vStar_concave : ConcaveOn ℝ D.domain vStar := by
  change ConcaveOn ℝ (Set.Icc (1:ℝ) 2) vStar
  exact arctan_concaveOn_Icc12

/-- `v*` is uniformly bounded: `|v*(w)| = |arctan w| ≤ π/2 ≤ 2π`. -/
theorem vStar_bounded : UniformBounded vStar := by
  refine ⟨2 * Real.pi, fun w => ?_⟩
  have hw : |Real.arctan w| ≤ Real.pi / 2 := Real.abs_arctan_le_pi_div_two w
  have hpi : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  change |Real.arctan w| ≤ 2 * Real.pi
  linarith [hw]

/-- The reward is `C¹` in the current state: `w ↦ arctan w − ½·arctan((w+2)/2) + arctan a −
arctan 2` is differentiable (each summand is `arctan` of an affine argument, smooth everywhere). -/
-- The hypotheses `w ∈ O` and `a ∈ Γ w` are required by the `h_reward_diff` API of the envelope
-- theorem; `arctan` is differentiable everywhere so neither is used in the proof body.
theorem reward_diff (w a : ℝ) (_ : w ∈ O) (_ : a ∈ D.toDetMDP.Γ w) :
    DifferentiableAt ℝ (fun w' => D.toDetMDP.reward w' a) w := by
  change DifferentiableAt ℝ
    (fun w' => Real.arctan w' - (1/2) * Real.arctan ((w' + 2) / 2) + Real.arctan a - Real.arctan 2)
    w
  have h1 : DifferentiableAt ℝ (fun w' : ℝ => Real.arctan w') w := Real.differentiableAt_arctan w
  have h2 : DifferentiableAt ℝ (fun w' : ℝ => Real.arctan ((w' + 2) / 2)) w :=
    (Real.differentiableAt_arctan _).comp w (by fun_prop)
  exact (((h1.sub ((differentiableAt_const _).mul h2)).add (differentiableAt_const _)).sub
    (differentiableAt_const _))

/-- The transition is `C¹` in the current state: `w ↦ (w+a)/2` is affine, differentiable. -/
-- The hypotheses are required by the `h_trans_diff` API; the transition is affine, so unused here.
theorem trans_diff (w a : ℝ) (_ : w ∈ O) (_ : a ∈ D.toDetMDP.Γ w) :
    DifferentiableAt ℝ (fun w' => D.toDetMDP.transition w' a) w := by
  change DifferentiableAt ℝ (fun w' => (w' + a) / 2) w
  fun_prop

/-- The policy `a*(w) = 2` is feasible: `2 ∈ [1,2]`. -/
theorem aStar_feasible : ∀ w ∈ O, aStar w ∈ D.toDetMDP.Γ w := by
  intro w _
  change (2:ℝ) ∈ Set.Icc (1:ℝ) 2
  exact Set.mem_Icc.mpr ⟨by norm_num, le_refl _⟩

/-- The policy `a*(w) = 2` stays feasible for nearby states (trivially: `2 ∈ [1,2]` always). -/
theorem aStar_locally_feasible : ∀ w₀ ∈ O, ∀ᶠ w in 𝓝 w₀, aStar w₀ ∈ D.toDetMDP.Γ w := by
  intro w₀ _
  refine Filter.Eventually.of_forall (fun w => ?_)
  change (2:ℝ) ∈ Set.Icc (1:ℝ) 2
  exact Set.mem_Icc.mpr ⟨by norm_num, le_refl _⟩

/-- `a*(w) = 2` maximizes the one-step Bellman objective. The `a`-dependent part
`arctan a + ½·arctan((w+a)/2)` is increasing in `a`, so the maximum is the right endpoint. -/
theorem aStar_optimal : ∀ w ∈ O, ∀ a ∈ D.toDetMDP.Γ w,
    D.toDetMDP.reward w a + D.toDetMDP.β * vStar (D.toDetMDP.transition w a) ≤
      D.toDetMDP.reward w (aStar w) +
        D.toDetMDP.β * vStar (D.toDetMDP.transition w (aStar w)) := by
  intro w _ a ha
  have ha_le : a ≤ 2 := (Set.mem_Icc.mp ha).2
  simp only [D, vStar, aStar]
  have ha2 : Real.arctan a ≤ Real.arctan 2 := Real.arctan_mono ha_le
  have hmid : Real.arctan ((w + a) / 2) ≤ Real.arctan ((w + 2) / 2) :=
    Real.arctan_mono (by linarith)
  nlinarith [ha2, hmid]

/-! ## The Benveniste-Scheinkman envelope identity with a live continuation chain term -/

/-- **The full Benveniste-Scheinkman identity.** With a state-dependent transition the discounted
continuation chain term does not vanish:
`(v*)'(w₀) = ∂r/∂w(w₀, 2) + β·(v*)'((w₀+2)/2)·∂f/∂w(w₀, 2)`. -/
theorem vStar_envelope_diffSucc (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv vStar w₀ =
      deriv (fun w => D.toDetMDP.reward w (aStar w₀)) w₀ +
        D.toDetMDP.β * deriv vStar (D.toDetMDP.transition w₀ (aStar w₀)) *
          deriv (fun w => D.toDetMDP.transition w (aStar w₀)) w₀ :=
  -- The final argument is the live Benveniste-Scheinkman successor hypothesis `hv_diff_succ`
  -- (required because the transition is state-dependent): `v* = arctan` is smooth everywhere, so it
  -- is a one-liner inlined here rather than stated as a named lemma.
  envelope_deriv_dp_of_diffSucc D isOpen_Ioo (convex_Ioo 1 2) Set.Ioo_subset_Icc_self
    reward_diff trans_diff vStar aStar aStar_feasible aStar_locally_feasible aStar_optimal
    vStar_bounded vStar_eq_bellman vStar_concave (fun _ _ => Real.differentiableAt_arctan _) w₀ hw₀

/-- The transition state-derivative is the **nonzero** multiplier `∂f/∂w(w₀, 2) = 1/2`. This is the
whole point of the example: the chain term in `vStar_envelope_diffSucc` is nonzero. -/
theorem trans_deriv_eq (w₀ : ℝ) :
    deriv (fun w => D.toDetMDP.transition w (aStar w₀)) w₀ = 1 / 2 := by
  change deriv (fun w => (w + 2) / 2) w₀ = 1 / 2
  have h : HasDerivAt (fun w => (w + 2) / 2) (1/2) w₀ := by
    simpa using (((hasDerivAt_id w₀).add_const 2).div_const 2)
  exact h.deriv

/-- The successor value-slope is `(v*)'((w₀+2)/2) = arctan'((w₀+2)/2) = 1/(1+((w₀+2)/2)²)`. -/
theorem vStar_deriv_succ_eq (w₀ : ℝ) :
    deriv vStar (D.toDetMDP.transition w₀ (aStar w₀)) = 1 / (1 + ((w₀ + 2)/2) ^ 2) := by
  change deriv (fun w => Real.arctan w) ((w₀ + 2)/2) = 1 / (1 + ((w₀ + 2)/2) ^ 2)
  exact (Real.hasDerivAt_arctan ((w₀ + 2)/2)).deriv

/-- The current-period marginal return at the optimal policy:
`∂r/∂w(w₀, 2) = 1/(1+w₀²) − ½·(1/(1+((w₀+2)/2)²)·½)`, i.e. `f₁'(w₀)`. The `arctan a` and `arctan 2`
terms are constants in `w`, so the reward's `w`-derivative is exactly `f₁'`. -/
theorem reward_deriv_eq (w₀ : ℝ) :
    deriv (fun w => D.toDetMDP.reward w (aStar w₀)) w₀ =
      1 / (1 + w₀ ^ 2) - (1/2) * ((1 / (1 + ((w₀ + 2)/2) ^ 2)) * (1/2)) := by
  have hfun : (fun w => D.toDetMDP.reward w (aStar w₀))
      = fun w => f1 w + (Real.arctan 2 - Real.arctan 2) := by
    funext w
    simp only [D, aStar, f1]
    ring
  rw [hfun]
  have hd : HasDerivAt (fun w => f1 w + (Real.arctan 2 - Real.arctan 2)) (f1' w₀) w₀ :=
    (hasDerivAt_f1 w₀).add_const _
  rw [hd.deriv]
  simp only [f1']

/-- **Headline result.** For every interior capital level `w₀ ∈ (1, 2)`, the value-function
derivative is `(v*)'(w₀) = 1/(1+w₀²)`.

Collapsing the live envelope identity `vStar_envelope_diffSucc`: the discounted continuation chain
term `β·(v*)'((w₀+2)/2)·(1/2) = ¼/(1+((w₀+2)/2)²)` exactly cancels the reward's compensator term
`−½·(1/(1+((w₀+2)/2)²)·½) = −¼/(1+((w₀+2)/2)²)`, leaving the marginal felicity of current capital
`arctan'(w₀) = 1/(1+w₀²)`. Unlike `EnvelopeGrowth`, the chain term is **nonzero** and cancels the
compensator rather than vanishing factor-by-factor. -/
theorem deriv_vStar (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv vStar w₀ = 1 / (1 + w₀ ^ 2) := by
  rw [vStar_envelope_diffSucc w₀ hw₀, reward_deriv_eq, trans_deriv_eq, vStar_deriv_succ_eq]
  change (1 / (1 + w₀ ^ 2) - (1/2) * ((1 / (1 + ((w₀ + 2)/2) ^ 2)) * (1/2)))
      + (1/2) * (1 / (1 + ((w₀ + 2)/2) ^ 2)) * (1/2) = 1 / (1 + w₀ ^ 2)
  ring

-- Consistency check: the direct derivative of the closed form `v*(w) = arctan w` agrees with the
-- envelope-derived value `1/(1+w₀²)` of `deriv_vStar`.
example (w₀ : ℝ) : deriv vStar w₀ = 1 / (1 + w₀ ^ 2) :=
  (Real.hasDerivAt_arctan w₀).deriv

end EconlibExamples.StateDependentEnvelope
