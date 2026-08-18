/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Optimization.EnvelopeGrowth
import EconlibExamples.Optimization.StateDependentEnvelope
import Mathlib

/-!
# Dynamic-programming regularity non-vacuity witnesses (concavity, envelope, weighted Blackwell)

Compile-time semantic witnesses for the *regularity* layer of
`Econlib.Optimization.DynamicProgramming`: Concavity preservation (`ConcavityPreservation`), the
closed-invariant-set principle (`ClosedInvariantSet`), the Benveniste-Scheinkman envelope
(`BenvenisteScheinkman`), the regularity-certificate interfaces (`Regularity`), and the
weighted/unbounded Boyd-norm Blackwell contraction (`Weighted`). Each abstract shape claim —
concavity preserved (not convexity), value function concave, and the weighted contraction modulus
`β = 1/2` (with the Boyd weight `ω` genuinely required, since the constant weight cannot bound the
unbounded reward) — is forced through a concrete model.

## Anchoring models

* **Chunk 3 (concavity / envelope):** the bounded `arctan` accumulation `ConcaveDPData` of
  `EconlibExamples.EnvelopeGrowth` (concave reward `arctan w + arctan a`, affine transition
  `f(w,a) = a`, value `v*(w) = arctan w + 3π/4`). It already discharges every `ConcaveDPData`
  field, so the concavity-preservation and envelope endpoints attach to it directly.
* **Chunk 4 (weighted Blackwell):** a fresh hand-solved **affine-growth** operator on the
  *unbounded* state space `ℝ`. With the Boyd weight `ω(s) = 1 + |s|`, the operator
  `T v (s) = s + β · v (s/2)` (`β = 1/2`) has the **unbounded** reward `r(s) = s` — so the sup-norm
  (`UniformBounded`) Blackwell theory of `Bellman.lean` *cannot* apply (there is no uniform bound
  on `|r|`) — yet `T` is a genuine `WeightedBlackwell ω T β`, and its closed-form fixed point is
  `v*(s) = (4/3) · s` (from `c = 1 + c/4`). The non-trivial weight is *required*: The constant
  weight `Weight.one` could not make the linear reward weighted-bounded. So this witness confirms
  the weighted machinery is doing real work the bounded core cannot, with modulus exactly `β = 1/2`.

## What each block catches

* **Concavity preservation** — `bellmanOperator_concave` / `valueFunction_concave` are run on the
  concave `arctan` DP; a convex-vs-concave preservation flip would fail to typecheck. The
  value-function-in-invariant-set principle (`valueFunction_mem_closedInvariant`) is exercised too.
  (Strict concavity is *not* checked here — `arctan` is concave but not strictly concave at the
  boundary point `0` of the state interval, so the strict-preservation layer is left to a model with
  a strictly concave reward.)
* **Envelope** — `envelope_deriv_dp_of_diffSucc` is exercised on the `arctan` accumulation DP,
  confirming the value derivative is the marginal current return plus a discounted continuation
  chain term that *vanishes* here because the transition ignores the current state (no sign error
  in the continuation derivative).
* **Weighted Blackwell** — `WeightedBlackwell.fixedPoint` / `fixedPoint_isFixedPt` /
  `fixedPoint_unique` / `iter_tendsto_fixedPoint` / `iter_dist_le_geometric`, the `Weight` carrier
  (`Weight.one`, `coe_apply`), `WeightedBounded.of_uniformBound` / `.smul`, and
  `FixedPointCertificate.eq_value` are all anchored on the unbounded affine-growth operator. The
  weighted discounting axiom holds with modulus `β = 1/2` via the weight monotonicity
  `ω(s/2) ≤ ω(s)` (`ω_half_le`); the structure `WeightedBlackwell` carries no separate growth factor
  `μ`, so the load-bearing fact is the genuine Boyd weight, not `Weight.one` (which cannot bound the
  linear reward — `reward_not_uniformBounded`).
-/

noncomputable section

namespace EconlibTest.Optimization.DPRegularity

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Blackwell UnboundedDetMDP

/-! ## Chunk 3 — Concavity preservation, closed invariant set, and the envelope

We reuse the bounded `arctan` accumulation `ConcaveDPData` of `EnvelopeGrowth`, whose value
function `v*(w) = arctan w + 3π/4` is concave on `[0,1]`. -/

private abbrev cD : ConcaveDPData := EconlibExamples.EnvelopeGrowth.D
private abbrev cV : ℝ → ℝ := EconlibExamples.EnvelopeGrowth.vStar

open EconlibExamples.EnvelopeGrowth (vStar_eq_bellman vStar_concave vStar_bounded aStar O
  reward_diff aStar_feasible aStar_locally_feasible aStar_optimal transition_indep)

/-- **`bellmanOperator_concave`: The Bellman operator preserves *concavity* (not convexity).**
Since `v*` is concave on `[0,1]`, its Bellman image `T v*` is again concave there — SLP Theorem 9.6
on a concrete concave-reward / affine-transition program. A convex-vs-concave preservation flip
would break this. -/
theorem arctan_bellmanOperator_concave :
    ConcaveOn ℝ cD.domain (cD.toDetMDP.bellmanOperator cV) :=
  bellmanOperator_concave cD cV vStar_concave vStar_bounded

/-- **`valueFunction_concave`: The value function is concave.** The unique bounded Bellman fixed
point is concave on `[0,1]` — the shape property transferred from the operator via the closed
invariant set principle. We supply the closed-form `v*` as the fixed point. -/
theorem arctan_valueFunction_concave :
    ConcaveOn ℝ cD.domain cV :=
  valueFunction_concave cD cV vStar_bounded vStar_eq_bellman

/-- **`DetMDP.valueFunction_mem_closedInvariant`: The canonical value function lands in a closed
invariant set.** Take `C = {f : BddFun | f concave on the domain}` — nonempty (constants), closed
under sup-norm limits, and invariant under the Bellman operator (concavity preservation). The
abstract `cD.toDetMDP.valueFunction` (the Banach fixed point) therefore lies in `C`. This is the
exact mechanism by which the concavity shape property is transferred to the value function. -/
theorem arctan_valueFunction_mem_closedInvariant :
    toBddFun cD.toDetMDP.valueFunction cD.toDetMDP.valueFunction_bounded ∈
      {f : @BddFun ℝ | ConcaveOn ℝ cD.domain (f : DState → ℝ)} :=
  cD.toDetMDP.valueFunction_mem_closedInvariant
    ⟨0, concaveOn_const 0 cD.domain_convex⟩
    (by
      -- The concavity set is closed under sup-norm limits (reuse the upstream argument shape).
      apply isClosed_of_closure_subset
      intro f hf
      refine ⟨cD.domain_convex, fun x hx y hy a b ha hb hab => ?_⟩
      by_contra h_neg
      push Not at h_neg
      set ε := a • (f : DState → ℝ) x + b • (f : DState → ℝ) y -
        (f : DState → ℝ) (a • x + b • y) with hε_def
      have hε : 0 < ε := by linarith
      rw [Metric.mem_closure_iff] at hf
      obtain ⟨g, hg_mem, hg_dist⟩ := hf (ε / 3) (by linarith)
      have hg_conc : ConcaveOn ℝ cD.domain (g : DState → ℝ) := hg_mem
      have hg_ineq := hg_conc.2 hx hy ha hb hab
      simp only [smul_eq_mul] at hg_ineq
      have hclose : ∀ z : @DState ℝ, |(f : DState → ℝ) z - (g : DState → ℝ) z| < ε / 3 := by
        intro z
        have := BoundedContinuousFunction.dist_coe_le_dist z
          (α := @DState ℝ) (β := ℝ) (f := f) (g := g)
        rw [Real.dist_eq] at this
        linarith [this, hg_dist]
      have hx' := hclose x
      have hy' := hclose y
      have hm' := hclose (a • x + b • y)
      rw [abs_lt] at hx' hy' hm'
      have hkey : ε ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 := by
        have h1 : a * ((f : DState → ℝ) x - (g : DState → ℝ) x) ≤ a * (ε / 3) :=
          mul_le_mul_of_nonneg_left hx'.2.le ha
        have h2 : b * ((f : DState → ℝ) y - (g : DState → ℝ) y) ≤ b * (ε / 3) :=
          mul_le_mul_of_nonneg_left hy'.2.le hb
        have h3 : (g : DState → ℝ) (a • x + b • y) -
            (f : DState → ℝ) (a • x + b • y) ≤ ε / 3 := by linarith [hm'.1]
        have key : ε = a * ((f : DState → ℝ) x - (g : DState → ℝ) x) +
            b * ((f : DState → ℝ) y - (g : DState → ℝ) y) +
            ((g : DState → ℝ) (a • x + b • y) - (f : DState → ℝ) (a • x + b • y)) +
            (a * (g : DState → ℝ) x + b * (g : DState → ℝ) y -
              (g : DState → ℝ) (a • x + b • y)) := by
          simp only [hε_def, smul_eq_mul]; ring
        calc ε = _ := key
          _ ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 +
              (a * (g : DState → ℝ) x + b * (g : DState → ℝ) y -
                (g : DState → ℝ) (a • x + b • y)) := by linarith
          _ ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 + 0 := by
            have hgi := hg_ineq; simp only [smul_eq_mul] at hgi ⊢; linarith
          _ = a * (ε / 3) + b * (ε / 3) + ε / 3 := by ring
      have hsum : (a + b + 1) * (ε / 3) = 2 * ε / 3 := by rw [hab]; ring
      linarith)
    (by
      -- The Bellman operator preserves the concavity set: it is the invariance of the shape class.
      intro f hf
      change ConcaveOn ℝ cD.domain ((bellmanOperatorBddFun cD.toDetMDP f : DState → ℝ))
      simp only [show (bellmanOperatorBddFun cD.toDetMDP f : DState → ℝ) =
        cD.toDetMDP.bellmanOperator f from by
          ext s; exact bellmanOperatorBddFun_apply cD.toDetMDP f s]
      exact bellmanOperator_concave cD f hf (bddFun_bounded f))

/-! ### Benveniste-Scheinkman envelope (state-derivative form)

`envelope_deriv_dp_of_diffSucc` gives the value-function derivative as the marginal
current-period return plus a discounted continuation chain term. We anchor it on the `arctan`
accumulation `D`, whose transition `f(w,a) = a` is independent of the current state, so the
continuation chain term vanishes (its `w`-derivative is `0`) and the formula collapses to the
marginal felicity of current capital — `(v*)'(w₀) = arctan'(w₀) = 1/(1 + w₀²)`. -/

/-- The transition `f(w, a) = a` is differentiable in `w` (it is constant in `w`). -/
private theorem arctan_trans_diff (w a : ℝ) (_ : w ∈ O) (_ : a ∈ cD.toDetMDP.Γ w) :
    DifferentiableAt ℝ (fun w' => cD.toDetMDP.transition w' a) w :=
  differentiableAt_const a

/-- **`envelope_deriv_dp_of_diffSucc`: The value derivative is the marginal current-period return
plus a discounted continuation chain term.** On the `arctan` accumulation DP, the chain term
carries `deriv (fun w => f(w, a*(w₀))) w₀`; since the transition `f(w,a) = a` ignores `w`, that
inner derivative is `0`, so the formula reduces to
`(v*)'(w₀) = deriv (fun w => reward w (a*(w₀))) w₀`. We record the full identity exactly as the
upstream theorem states it (chain term present, then shown to vanish), which is the genuine
Benveniste-Scheinkman envelope. A sign error in the continuation derivative would surface as a
nonzero spurious term. -/
private theorem arctan_envelope_diffSucc (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv cV w₀ =
      deriv (fun w => cD.toDetMDP.reward w (aStar w₀)) w₀ +
        cD.toDetMDP.β * deriv cV (cD.toDetMDP.transition w₀ (aStar w₀)) *
          deriv (fun w => cD.toDetMDP.transition w (aStar w₀)) w₀ :=
  -- Successor-differentiability `hv_diff_succ`: `v* = arctan + const` is smooth everywhere, a
  -- one-liner inlined here rather than stated as a named lemma.
  envelope_deriv_dp_of_diffSucc cD isOpen_Ioo (convex_Ioo 0 1) Set.Ioo_subset_Icc_self
    reward_diff arctan_trans_diff cV aStar aStar_feasible aStar_locally_feasible aStar_optimal
    vStar_bounded vStar_eq_bellman vStar_concave
    (fun _ _ => (Real.differentiableAt_arctan _).add (differentiableAt_const _)) w₀ hw₀

/-- **The transition's state-derivative is zero.** The transition `f(w, a) = a` ignores the current
state, so `w ↦ f(w, a*(w₀))` is the *constant* `a*(w₀)` and its derivative at `w₀` is `0`. This is
the explicit factor that makes the envelope continuation chain term vanish. -/
private theorem arctan_trans_deriv_zero (w₀ : ℝ) :
    deriv (fun w => cD.toDetMDP.transition w (aStar w₀)) w₀ = 0 := by
  -- `transition w a = a` by definition of the EnvelopeGrowth `D`, so the map is constant in `w`.
  have hconst : (fun w => cD.toDetMDP.transition w (aStar w₀)) = fun _ => aStar w₀ := rfl
  rw [hconst, deriv_const]

/-- **The current-period marginal return equals `1/(1 + w₀²)`.** The reward `r(w, a) = arctan w +
arctan a` has `w`-derivative `arctan'(w₀) = 1/(1 + w₀²)`, the marginal felicity of current capital
(the continuation term `arctan (a*(w₀))` is constant in `w`). -/
private theorem arctan_reward_deriv (w₀ : ℝ) :
    deriv (fun w => cD.toDetMDP.reward w (aStar w₀)) w₀ = 1 / (1 + w₀ ^ 2) := by
  -- `reward w a = arctan w + arctan a`; the second summand is constant in `w`.
  have hrw : (fun w => cD.toDetMDP.reward w (aStar w₀))
      = fun w => Real.arctan w + Real.arctan (aStar w₀) := rfl
  rw [hrw, deriv_add_const, Real.deriv_arctan]

/-- **The continuation chain term genuinely vanishes** on the state-independent transition —
*derived
from* the full Benveniste-Scheinkman envelope `arctan_envelope_diffSucc`, not from the closed-form
shortcut. Substituting the explicit zero `arctan_trans_deriv_zero` for the transition's
state-derivative kills the entire continuation chain term `β · (v*)'(succ) · 0`, and
`arctan_reward_deriv` reads off the surviving marginal felicity, giving `(v*)'(w₀) = 1/(1 + w₀²)`.
A sign error in the continuation derivative would surface as a spurious nonzero term in
`arctan_envelope_diffSucc` and break this collapse. -/
private theorem arctan_envelope_collapses (w₀ : ℝ) (hw₀ : w₀ ∈ O) :
    deriv cV w₀ = 1 / (1 + w₀ ^ 2) := by
  rw [arctan_envelope_diffSucc w₀ hw₀, arctan_trans_deriv_zero, arctan_reward_deriv,
    mul_zero, add_zero]

/-- **The non-degenerate factors of the continuation chain term are nonzero.** The chain term in
`arctan_envelope_diffSucc` is the product `β · (v*)'(succ) · deriv(transition)`. Its vanishing in
`arctan_envelope_collapses` comes *only* from the transition's zero state-derivative
(`arctan_trans_deriv_zero`), **not** from an accidentally-zero other factor: here the discount
`β = 1/2 ≠ 0` and, at the successor `f(w₀, a*(w₀)) = a*(w₀) = 1`, the value-function slope is
`(v*)'(1) = arctan'(1) = 1/(1 + 1²) = 1/2 ≠ 0`. So the chain term is a genuine `½ · ½ · 0`, with two
live factors — a structural sign/factor error in `β` or `(v*)'` would not be masked by a spurious
zero. -/
private theorem arctan_envelope_chain_factors_nonzero :
    cD.toDetMDP.β = 1 / 2 ∧ cD.toDetMDP.β ≠ 0 ∧
      deriv cV (cD.toDetMDP.transition (0 : ℝ) (aStar 0)) = 1 / 2 ∧
      deriv cV (cD.toDetMDP.transition (0 : ℝ) (aStar 0)) ≠ 0 := by
  -- `β = 1/2` and the successor `transition w₀ (a*(w₀)) = a*(w₀) = 1`.
  have hsucc : cD.toDetMDP.transition (0 : ℝ) (aStar 0) = 1 := rfl
  have hβ : cD.toDetMDP.β = 1 / 2 := rfl
  -- `(v*)'(1) = arctan'(1) = 1/(1+1) = 1/2`.
  have hderiv : deriv cV (cD.toDetMDP.transition (0 : ℝ) (aStar 0)) = 1 / 2 := by
    rw [hsucc]
    change deriv (fun w => Real.arctan w + 3 * Real.pi / 4) 1 = 1 / 2
    rw [deriv_add_const, Real.deriv_arctan]; norm_num
  exact ⟨hβ, by rw [hβ]; norm_num, hderiv, by rw [hderiv]; norm_num⟩

/-! ### Benveniste-Scheinkman envelope with a *state-dependent* transition (live chain term)

The collapse above hinges on the transition `f(w,a) = a` ignoring the current state, so the
continuation chain term vanishes by its *transition* factor. To exercise the **non-vanishing**
branch of `envelope_deriv_dp_of_diffSucc` — where `∂f/∂w ≠ 0` and the chain term is a genuine live
multiplier — we anchor on the companion `StateDependentEnvelope` model: `f(w,a) = (w+a)/2` on
`[1,2]`, value `v*(w) = arctan w`, optimal policy `a*(w) = 2`. Here the chain term does *not*
vanish; instead it exactly cancels the reward's continuation *compensator*. A sign error in the
continuation derivative would no longer be masked by a zero transition factor — it would surface as
a numeric mismatch in the hand-computed identity below. -/

private abbrev sD : ConcaveDPData := EconlibExamples.StateDependentEnvelope.D
private abbrev sV : ℝ → ℝ := EconlibExamples.StateDependentEnvelope.vStar
private abbrev sA : ℝ → ℝ := EconlibExamples.StateDependentEnvelope.aStar
private abbrev sO : Set ℝ := EconlibExamples.StateDependentEnvelope.O

open EconlibExamples.StateDependentEnvelope (vStar_envelope_diffSucc trans_deriv_eq
  vStar_deriv_succ_eq reward_deriv_eq deriv_vStar)

/-- **`envelope_deriv_dp_of_diffSucc` on a state-dependent transition.** The full
Benveniste-Scheinkman identity — value derivative = marginal current return **plus** the discounted
continuation chain term — holds on the midpoint-accumulation model, where the transition genuinely
depends on the current state. This is the live-chain-term counterpart of `arctan_envelope_diffSucc`
(whose chain term vanishes). -/
private theorem sd_envelope_diffSucc (w₀ : ℝ) (hw₀ : w₀ ∈ sO) :
    deriv sV w₀ =
      deriv (fun w => sD.toDetMDP.reward w (sA w₀)) w₀ +
        sD.toDetMDP.β * deriv sV (sD.toDetMDP.transition w₀ (sA w₀)) *
          deriv (fun w => sD.toDetMDP.transition w (sA w₀)) w₀ :=
  vStar_envelope_diffSucc w₀ hw₀

/-- **The transition's state-derivative is the nonzero multiplier `∂f/∂w = 1/2`.** Unlike the
`arctan` accumulation model (`arctan_trans_deriv_zero`), the chain term in `sd_envelope_diffSucc`
carries a genuine *live* factor, so its vanishing is impossible — the identity collapse must come
from cancellation, not from a zero factor. -/
private theorem sd_trans_deriv_nonzero (w₀ : ℝ) :
    deriv (fun w => sD.toDetMDP.transition w (sA w₀)) w₀ = 1 / 2 ∧
      deriv (fun w => sD.toDetMDP.transition w (sA w₀)) w₀ ≠ 0 :=
  ⟨trans_deriv_eq w₀, by rw [trans_deriv_eq]; norm_num⟩

/-- **The continuation chain term is live and load-bearing at `w₀ = 3/2`.** At the interior state
`w₀ = 3/2` the successor is `(3/2 + 2)/2 = 7/4`, so the value slope there is `1/(1+(7/4)²) = 16/65`,
and the chain term is `β · 16/65 · ∂f/∂w = (1/2)·(16/65)·(1/2) = 4/65 ≠ 0`. Crucially the marginal
current return *alone* is `16/65`, which differs from the value derivative `1/(1+(3/2)²) = 20/65`:
the chain term `4/65` is exactly the gap that restores the identity (`16/65 + 4/65 = 20/65`). A sign
error in the continuation derivative would break this hand-computed match. -/
private theorem sd_chain_term_live :
    sD.toDetMDP.β * deriv sV (sD.toDetMDP.transition (3 / 2) (sA (3 / 2))) *
          deriv (fun w => sD.toDetMDP.transition w (sA (3 / 2))) (3 / 2) = 4 / 65 ∧
      deriv (fun w => sD.toDetMDP.reward w (sA (3 / 2))) (3 / 2) = 16 / 65 ∧
        deriv sV (3 / 2) = 20 / 65 ∧
          deriv (fun w => sD.toDetMDP.reward w (sA (3 / 2))) (3 / 2) ≠ deriv sV (3 / 2) := by
  have hβ : sD.toDetMDP.β = 1 / 2 := rfl
  have h_chain : sD.toDetMDP.β * deriv sV (sD.toDetMDP.transition (3 / 2) (sA (3 / 2))) *
      deriv (fun w => sD.toDetMDP.transition w (sA (3 / 2))) (3 / 2) = 4 / 65 := by
    rw [hβ, vStar_deriv_succ_eq, trans_deriv_eq]; norm_num
  have h_reward : deriv (fun w => sD.toDetMDP.reward w (sA (3 / 2))) (3 / 2) = 16 / 65 := by
    rw [reward_deriv_eq]; norm_num
  have h_value : deriv sV (3 / 2) = 20 / 65 := by
    rw [deriv_vStar (3 / 2) (by
      change (3 : ℝ) / 2 ∈ Set.Ioo (1 : ℝ) 2
      exact Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩)]
    norm_num
  exact ⟨h_chain, h_reward, h_value, by rw [h_reward, h_value]; norm_num⟩

/-! ### Regularity certificate carriers

`ConcaveFiniteDPData` is the theorem-facing interface structure of `ConcavityPreservation`. We
build a concrete instance and exercise its lemmas, so the carrier is non-vacuous. -/

/-- The clamp `cl a = max 0 (min 1 a)` projecting a real action into the feasible interval `[0, 1]`.
It is the identity on `[0, 1]` and keeps the reward / transition pmf globally bounded (the `FinMDP`
boundedness fields are quantified over *all* real actions, not just feasible ones), while the
objective is genuinely **non**-constant on the feasible set. -/
private def cl (a : ℝ) : ℝ := max 0 (min 1 a)

/-- The clamp lands in `[0, 1]`. -/
private theorem cl_mem (a : ℝ) : cl a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The clamp is the identity on the feasible interval `[0, 1]`. -/
private theorem cl_eq {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) : cl a = a := by
  obtain ⟨ha0, ha1⟩ := ha
  simp only [cl, min_eq_right ha1, max_eq_right ha0]

/-- The transition pmf vector `(cl a, 1 − cl a)` is nonnegative for every real action. -/
private theorem cfd_pmf_nonneg (a : ℝ) (i : Fin 2) : 0 ≤ (![cl a, 1 - cl a] : Fin 2 → ℝ) i := by
  have h := cl_mem a
  simp only [Set.mem_Icc] at h
  fin_cases i
  · simpa using h.1
  · simpa using by linarith [h.2]

/-- The transition pmf vector `(cl a, 1 − cl a)` sums to one. -/
private theorem cfd_pmf_sum (a : ℝ) : ∑ i, (![cl a, 1 - cl a] : Fin 2 → ℝ) i = 1 := by
  rw [Fin.sum_univ_two]; simp

/-- Global concavity of `-(a − 1/2)²` on `[0, 1]`: as a downward parabola its second derivative is
the constant `-2 < 0`, so it is strictly concave on all of ℝ. -/
private theorem neg_sq_concave :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun a : ℝ => -(a - 1 / 2) ^ 2) := by
  -- `-(a - 1/2)² = -a² + a - 1/4`, with first derivative `-2a + 1` and second derivative `-2`.
  have heq : (fun a : ℝ => -(a - 1 / 2) ^ 2) = fun a : ℝ => -a ^ 2 + a - 1 / 4 := by
    funext a; ring
  rw [heq]
  refine (strictConcaveOn_univ_of_deriv2_neg (by fun_prop) (fun x => ?_)).concaveOn.subset
    (Set.subset_univ _) (convex_Icc 0 1)
  have hd1 : deriv (fun a : ℝ => -a ^ 2 + a - 1 / 4) = fun a => -2 * a + 1 := by
    funext a
    have h : HasDerivAt (fun a : ℝ => -a ^ 2 + a - 1 / 4) (-2 * a + 1) a := by
      have hp2 : HasDerivAt (fun a : ℝ => -a ^ 2) (-(2 * a)) a := by
        simpa using ((hasDerivAt_pow 2 a).const_mul (-1 : ℝ))
      simpa using (hp2.add (hasDerivAt_id a)).sub_const (1 / 4)
    exact h.deriv
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hd1]
  have h2 : HasDerivAt (fun a : ℝ => -2 * a + 1) (-2) x := by
    simpa using ((hasDerivAt_id x).const_mul (-2)).add_const 1
  rw [h2.deriv]; norm_num

/-- A concrete **non-degenerate** `ConcaveFiniteDPData 2`. The feasible set is the *compact*
interval
`Γ s = [0, 1]` (so the reward can be genuinely non-constant without violating the global reward
bound), the reward `r(s, a) = -(cl a − 1/2)²` is a **strictly concave-shaped**, non-constant
(`r(·,0) = -1/4 ≠ 0 = r(·,1/2)`) function on `[0, 1]`, and the transition is the **non-constant
affine** pmf `(cl a, 1 − cl a)` — so on `[0, 1]` the next-state probabilities move with the action
`(a, 1 − a)`. This exercises SLP 9.7 on a real, action-dependent concave program rather than a
constant-objective degeneracy. -/
private def cfd : ConcaveFiniteDPData 2 where
  toFinMDP :=
    { Γ := fun _ => Set.Icc (0 : ℝ) 1
      reward := fun _ a => -(cl a - 1 / 2) ^ 2
      transition := fun _ a =>
        Econlib.Probability.FinDist.ofVec ![cl a, 1 - cl a] (cfd_pmf_nonneg a) (cfd_pmf_sum a)
      β := 1 / 2
      β_nonneg := by norm_num
      β_lt_one := by norm_num
      Γ_nonempty := fun _ => ⟨0, by norm_num⟩
      -- `|-(cl a - 1/2)²| ≤ 1/4` since `cl a ∈ [0,1]` forces `(cl a - 1/2)² ≤ 1/4`.
      reward_bounded := ⟨1 / 4, fun _ a => by
        have h := cl_mem a
        simp only [Set.mem_Icc] at h
        rw [abs_le]
        constructor <;> nlinarith [h.1, h.2, sq_nonneg (cl a - 1 / 2)]⟩ }
  Γ_convex := fun _ => convex_Icc 0 1
  reward_concave := fun _ => by
    -- On `[0,1]`, `-(cl a - 1/2)² = -(a - 1/2)²`, which is concave (`neg_sq_concave`).
    refine neg_sq_concave.congr (fun a ha => ?_)
    change -(a - 1 / 2) ^ 2 = -(cl a - 1 / 2) ^ 2
    rw [cl_eq ha]
  transition_weights_concave := fun _ i => by
    -- pmf component `i` is `cl a` (i = 0) or `1 - cl a` (i = 1); both are affine on `[0,1]` (= id /
    -- 1 - id there), hence concave.
    fin_cases i
    · -- pmf 0 = cl a, equal to `a` on `[0,1]`.
      have hid : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun a : ℝ => a) :=
        (LinearMap.id : ℝ →ₗ[ℝ] ℝ).concaveOn (convex_Icc 0 1)
      refine hid.congr (fun a ha => ?_)
      change a = (Econlib.Probability.FinDist.ofVec ![cl a, 1 - cl a]
        (cfd_pmf_nonneg a) (cfd_pmf_sum a)).pmf 0
      rw [Econlib.Probability.FinDist.ofVec_pmf]
      change a = (![cl a, 1 - cl a] : Fin 2 → ℝ) 0
      rw [show (![cl a, 1 - cl a] : Fin 2 → ℝ) 0 = cl a from rfl, cl_eq ha]
    · -- pmf 1 = 1 - cl a, equal to `1 - a` on `[0,1]`.
      have hsub : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun a : ℝ => 1 - a) :=
        (concaveOn_const 1 (convex_Icc 0 1)).sub
          ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn (convex_Icc 0 1))
      refine hsub.congr (fun a ha => ?_)
      change 1 - a = (Econlib.Probability.FinDist.ofVec ![cl a, 1 - cl a]
        (cfd_pmf_nonneg a) (cfd_pmf_sum a)).pmf 1
      rw [Econlib.Probability.FinDist.ofVec_pmf]
      change 1 - a = (![cl a, 1 - cl a] : Fin 2 → ℝ) 1
      rw [show (![cl a, 1 - cl a] : Fin 2 → ℝ) 1 = 1 - cl a from rfl, cl_eq ha]

/-- The reward is genuinely **non-constant** in the action on the feasible interval:
`r(s, 0) = -1/4`
while `r(s, 1/2) = 0`. So the concavity check below is not the tautological constant-objective
case. -/
private theorem cfd_reward_not_constant (s : Fin 2) :
    cfd.toFinMDP.reward s 0 ≠ cfd.toFinMDP.reward s (1 / 2) := by
  change -(cl 0 - 1 / 2) ^ 2 ≠ -(cl (1 / 2) - 1 / 2) ^ 2
  rw [cl_eq (by norm_num), cl_eq (by norm_num)]; norm_num

/-- The transition pmf genuinely **moves** with the action on the feasible interval:
at `a = 1/4` the
next-state probabilities are `(1/4, 3/4)`, not the `(1/2, 1/2)` of `a = 1/2`. So the transition is
action-dependent, not a constant kernel. -/
private theorem cfd_transition_not_constant (s : Fin 2) :
    (cfd.toFinMDP.transition s (1 / 4)).pmf 0 ≠ (cfd.toFinMDP.transition s (1 / 2)).pmf 0 := by
  change (Econlib.Probability.FinDist.ofVec ![cl (1 / 4), 1 - cl (1 / 4)]
      (cfd_pmf_nonneg _) (cfd_pmf_sum _)).pmf 0 ≠
    (Econlib.Probability.FinDist.ofVec ![cl (1 / 2), 1 - cl (1 / 2)]
      (cfd_pmf_nonneg _) (cfd_pmf_sum _)).pmf 0
  rw [Econlib.Probability.FinDist.ofVec_pmf, Econlib.Probability.FinDist.ofVec_pmf,
    Matrix.cons_val_zero, Matrix.cons_val_zero, cl_eq (by norm_num), cl_eq (by norm_num)]
  norm_num

/-- **`finiteBellmanOperator_concave_in_action`: The finite-stochastic Bellman objective is concave
in the action.** With the **non-constant** concave reward `-(a − 1/2)²` and the **non-constant**
affine transition weights `(a, 1 − a)` on the feasible interval `[0, 1]`, the objective
`u(s, a) + β·𝔼[v]` is concave in `a` for any non-negative `v` — the finite-state concavity
preservation (SLP Theorem 9.7), exercised on a genuinely action-dependent program. A
convex-vs-concave flip would break this. -/
private theorem cfd_concave_in_action (v : Fin 2 → ℝ) (hv_nonneg : ∀ i, 0 ≤ v i) (s : Fin 2) :
    ConcaveOn ℝ (cfd.toFinMDP.Γ s)
      (fun a => cfd.toFinMDP.reward s a +
        cfd.toFinMDP.β * Econlib.Probability.FinDist.expect (cfd.toFinMDP.transition s a) v) :=
  finiteBellmanOperator_concave_in_action cfd v hv_nonneg s

/-! ## Chunk 4 — Weighted / unbounded (Boyd-norm) Blackwell contraction

A fresh hand-solved affine-growth operator on the unbounded state space `ℝ`, with Boyd weight
`ω(s) = 1 + |s|`. The reward `r(s) = s` is unbounded, so the bounded sup-norm Blackwell theory does
not apply; the weighted theory does, with fixed point `v*(s) = (4/3)·s`. -/

/-- The **Boyd weight** `ω(s) = 1 + |s|`: Strictly positive and `≥ 1`, so it makes the linear
(unbounded) reward weighted-bounded. -/
private def ω : Weight ℝ where
  toFun := fun s => 1 + |s|
  pos := fun s => by positivity
  one_le := fun s => by simp [abs_nonneg]

/-- The **affine-growth Bellman operator** `T v (s) = s + β · v (s/2)` with `β = 1/2`. Its reward
`r(s) = s` is unbounded over `ℝ`. -/
private def T (v : ℝ → ℝ) (s : ℝ) : ℝ := s + (1 / 2) * v (s / 2)

/-- The closed-form weighted fixed point `v*(s) = (4/3) · s`, from `c = 1 + c/4 ⟹ c = 4/3`. -/
private def wV : ℝ → ℝ := fun s => (4 / 3) * s

/-- The weight `ω(s/2) ≤ ω(s)` — the monotone-Boyd fact powering the discounting axiom. -/
private theorem ω_half_le (s : ℝ) : ω (s / 2) ≤ ω s := by
  simp only [ω]
  have h : |s / 2| ≤ |s| := by
    rw [abs_div, abs_two, half_le_self_iff]; exact abs_nonneg s
  linarith

/-- **The affine-growth operator is a genuine weighted Blackwell operator with modulus `β = 1/2`.**
Monotone (β ≥ 0), maps weighted-bounded to weighted-bounded (the weight absorbs the linear reward),
and satisfies the weighted discounting axiom `T(v + cω) ≤ Tv + β·c·ω` (via `ω(s/2) ≤ ω(s)`). -/
private def Hwb : WeightedBlackwell ω T (1 / 2) where
  beta_nonneg := by norm_num
  beta_lt_one := by norm_num
  maps_weightedBounded := fun v hv => by
    obtain ⟨C, hC, hbound⟩ := hv
    refine ⟨1 + (1 / 2) * C, by positivity, fun s => ?_⟩
    have hr : |s| ≤ ω s := by simp only [ω]; linarith [abs_nonneg s]
    have hv2 : |v (s / 2)| ≤ C * ω (s / 2) := hbound (s / 2)
    calc |T v s| = |s + (1 / 2) * v (s / 2)| := rfl
      _ ≤ |s| + |(1 / 2) * v (s / 2)| := abs_add_le _ _
      _ = |s| + (1 / 2) * |v (s / 2)| := by rw [abs_mul]; norm_num
      _ ≤ ω s + (1 / 2) * (C * ω (s / 2)) :=
          add_le_add hr (by nlinarith [hv2, ω_half_le s, ω.pos (s / 2)])
      _ ≤ ω s + (1 / 2) * (C * ω s) := by nlinarith [ω_half_le s, ω.pos s, hC]
      _ = (1 + (1 / 2) * C) * ω s := by ring
  monotone := fun v w _ _ hvw s => by
    simp only [T]
    have := hvw (s / 2)
    linarith
  discounting := fun v c _ hc s => by
    simp only [T]
    -- T(v + cω)(s) = s + ½(v(s/2) + c·ω(s/2)) = Tv(s) + ½·c·ω(s/2) ≤ Tv(s) + ½·c·ω(s)
    have hstep : (1 / 2) * c * ω (s / 2) ≤ (1 / 2) * c * ω s :=
      mul_le_mul_of_nonneg_left (ω_half_le s) (by positivity)
    nlinarith [hstep]

/-- The closed form `v*(s) = (4/3)·s` is weighted bounded (`|v*(s)| ≤ (4/3)·ω(s)`). -/
private theorem wV_weightedBounded : WeightedBounded ω wV := by
  refine ⟨4 / 3, by norm_num, fun s => ?_⟩
  simp only [wV, ω]
  rw [abs_mul]
  have : |(4 : ℝ) / 3| = 4 / 3 := by norm_num
  rw [this]
  nlinarith [abs_nonneg s]

/-- The closed form `v*(s) = (4/3)·s` solves the weighted Bellman equation `v* = T v*`. -/
private theorem wV_isFixedPt (s : ℝ) : wV s = T wV s := by
  simp only [wV, T]; ring

/-- **`WeightedBlackwell.fixedPoint_unique` identifies the closed form with the abstract fixed
point.** The hand-solved `v*(s) = (4/3)·s` is *the* weighted-bounded fixed point of the
affine-growth operator. -/
private theorem wV_eq_fixedPoint : wV = WeightedBlackwell.fixedPoint Hwb :=
  WeightedBlackwell.fixedPoint_unique Hwb wV wV_weightedBounded wV_isFixedPt

/-- **`WeightedBlackwell.fixedPoint_isFixedPt`: The abstract fixed point solves Bellman.** The
pointwise-limit fixed point `fixedPoint Hwb` is a genuine fixed point of `T`; with
`wV_eq_fixedPoint` this is the closed-form `(4/3)·s`. -/
private theorem affine_fixedPoint_isFixedPt (s : ℝ) :
    WeightedBlackwell.fixedPoint Hwb s = T (WeightedBlackwell.fixedPoint Hwb) s :=
  WeightedBlackwell.fixedPoint_isFixedPt Hwb s

/-- **`WeightedBlackwell.FixedPointCertificate.eq_value` on the affine-growth certificate.** Any
weighted-bounded fixed point equals the certified value function. We feed the closed form `wV` and
recover `wV = (fixedPointCertificate Hwb).value`. -/
private theorem affine_certificate_eq_value :
    wV = (WeightedBlackwell.fixedPointCertificate Hwb).value :=
  (WeightedBlackwell.fixedPointCertificate Hwb).eq_value wV_weightedBounded wV_isFixedPt

/-- **`WeightedBlackwell.iter_tendsto_fixedPoint`: Value iteration from zero converges.** For each
state `s`, the iterates `Tⁿ 0 (s)` converge to `fixedPoint Hwb s = (4/3)·s`. Non-vacuous geometric
convergence on an unbounded state space where the sup-norm route is unavailable. -/
private theorem affine_iter_tendsto (s : ℝ) :
    Filter.Tendsto (fun n => WeightedBlackwell.iter T n s) Filter.atTop
      (nhds (WeightedBlackwell.fixedPoint Hwb s)) :=
  WeightedBlackwell.iter_tendsto_fixedPoint Hwb s

/-- **`WeightedBlackwell.iter_dist_le_geometric`: The geometric convergence rate is explicit.** The
distance from the `n`-th iterate to the fixed point is bounded by `β^n · d₀ · ω(s) / (1 - β)` — a
non-vacuous geometric decay with modulus `β = 1/2`. -/
private theorem affine_iter_dist_le_geometric (n : ℕ) (s : ℝ) :
    |WeightedBlackwell.iter T n s - WeightedBlackwell.fixedPoint Hwb s| ≤
      (1 / 2) ^ n *
        weightedOscillation ω (WeightedBlackwell.iter T 1) (WeightedBlackwell.iter T 0) *
          ω s / (1 - 1 / 2) :=
  WeightedBlackwell.iter_dist_le_geometric Hwb n s

/-! ### The `Weight` carrier and `WeightedBounded` API -/

/-- **`Weight.one` and `Weight.coe_apply`.** The constant weight evaluates to `1` everywhere. (And,
crucially, it could *not* make the linear reward `r(s) = s` weighted-bounded — `|s| ≤ C · 1` fails
— which is exactly why the non-trivial Boyd weight `ω` was needed above.) -/
private theorem weight_one_apply (s : ℝ) : (Weight.one ℝ : ℝ → ℝ) s = 1 := by
  rw [Weight.coe_apply]; rfl

/-- **`Weight.one` cannot bound the unbounded reward.** There is no constant `C` with `|s| ≤ C · 1`
for all `s` — so the constant-weight (equivalently sup-norm) theory genuinely fails on this model,
forcing the Boyd weight. -/
private theorem reward_not_uniformBounded :
    ¬ ∃ C : ℝ, ∀ s : ℝ, |s| ≤ C * (Weight.one ℝ : ℝ → ℝ) s := by
  rintro ⟨C, hC⟩
  have := hC (|C| + 1)
  rw [weight_one_apply, mul_one, abs_of_nonneg (by positivity)] at this
  linarith [le_abs_self C]

/-- **`WeightedBounded.of_uniformBound`: A uniformly bounded function is weighted bounded.** Any
function with a sup bound (e.g. `arctan`, bounded by `π/2`) is automatically weighted bounded
against the Boyd weight — the normalization `ω ≥ 1` makes the embedding free. -/
private theorem arctan_weightedBounded : WeightedBounded ω Real.arctan :=
  WeightedBounded.of_uniformBound (B := Real.pi / 2) (by positivity)
    (fun s => abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan s),
      le_of_lt (Real.arctan_lt_pi_div_two s)⟩)

/-- **`WeightedBounded.smul`: Scaling preserves weighted boundedness.** `3 · v*` is weighted
bounded whenever `v*` is — used pervasively when assembling weighted-norm estimates. -/
private theorem scaled_wV_weightedBounded : WeightedBounded ω (fun s => 3 * wV s) :=
  WeightedBounded.smul 3 wV_weightedBounded

end EconlibTest.Optimization.DPRegularity
