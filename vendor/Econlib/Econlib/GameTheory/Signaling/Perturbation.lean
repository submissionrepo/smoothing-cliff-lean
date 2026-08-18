/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.Basic
public import Econlib.Math.Analysis.Convex.PerturbedSimplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# ε-perturbed simplex slice and posterior continuity

This file defines the ε-perturbed signaling strategy space used in the Kreps-Wilson (1982)
trembling-hand construction. A fully mixed sender strategy makes every message on path, so the
Bayes posterior and payoff maps are continuous on the perturbed profile space. The resulting
`NashExistenceData` packages the finite fixed-point problem for perturbed signaling profiles.

The geometric properties of the perturbed simplex slice `Econlib.PerturbedSimplex` (convexity,
compactness, nonemptiness) live in `Econlib.Math.Analysis.Convex.PerturbedSimplex`.

## Main definitions

* `marginalProbRaw`: Marginal message probability as a function of raw sender strategies.
* `posteriorNumerator`: The receiver payoff numerator weighted by the prior and sender strategy.
* `deviatorAmbient`, `deviatorSlice`: Per-deviator ambient spaces and feasible slices.
* `profileSenderRaw`, `profileReceiverRaw`: Raw sender and receiver strategy projections from a
  Kakutani profile.
* `perturbedPayoff`: The payoff functional for the perturbed fixed-point problem.
* `toPerturbedNashExistenceData`: The ε-perturbed signaling game as `NashExistenceData`.

## Main statements

* `marginalProbRaw_continuous`, `marginalProbRaw_ge_eps_of_perturbed`: Continuity and positivity
  properties of message marginals.
* `posteriorNumerator_continuous`: Continuity of the posterior numerator.
* `profileSenderRaw_continuous_eval`, `profileReceiverRaw_continuous_eval`: Continuity of raw
  profile coordinates.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).

## Tags

signaling games, perturbations, kakutani, posterior continuity
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability Topology

namespace Econlib.GameTheory

/-! ## Continuity of marginal-probability and posterior on PerturbedSimplex -/

namespace SignalingGame

variable (sg : SignalingGame)

/-- Marginal probability of message `m` as a function of an *unconstrained* sender strategy
`f : sg.Theta → sg.Msg → ℝ`. Equals `sg.marginalProb` when `f θ = (σ_S θ).val`. -/
def marginalProbRaw (f : sg.Theta → sg.Msg → ℝ) (m : sg.Msg) : ℝ :=
  ∑ θ : sg.Theta, sg.prior.pmf θ * f θ m

/-- Marginal probability is continuous in the unconstrained sender strategy. -/
lemma marginalProbRaw_continuous (m : sg.Msg) :
    Continuous (fun f : sg.Theta → sg.Msg → ℝ => sg.marginalProbRaw f m) := by
  unfold marginalProbRaw
  refine continuous_finset_sum _ (fun θ _ => ?_)
  exact continuous_const.mul ((continuous_apply m).comp (continuous_apply θ))

/-- At an ε-perturbed sender strategy, the marginal at every message is at least
`ε * (∑ θ, sg.prior.pmf θ) = ε`. -/
lemma marginalProbRaw_ge_eps_of_perturbed
    {ε : ℝ} (_hε_nn : 0 ≤ ε) (f : sg.Theta → sg.Msg → ℝ)
    (hf : ∀ θ, f θ ∈ PerturbedSimplex (α := sg.Msg) ε) (m : sg.Msg) :
    ε ≤ sg.marginalProbRaw f m := by
  unfold marginalProbRaw
  calc ε = ∑ θ : sg.Theta, sg.prior.pmf θ * ε := by
        rw [← Finset.sum_mul, sg.prior.sum_one, one_mul]
    _ ≤ ∑ θ : sg.Theta, sg.prior.pmf θ * f θ m :=
        Finset.sum_le_sum fun θ _ =>
          mul_le_mul_of_nonneg_left ((hf θ).2 m) (sg.prior.nonneg θ)

/-- The receiver's expected-payoff-times-marginal numerator: A polynomial in the sender strategy,
hence continuous. Useful because dividing by the (positive) marginal recovers the
posterior-weighted receiver payoff. -/
def posteriorNumerator (f : sg.Theta → sg.Msg → ℝ) (m : sg.Msg) (a : sg.Act) : ℝ :=
  ∑ θ : sg.Theta, sg.prior.pmf θ * f θ m * sg.payoff .receiver θ m a

/-- The posterior numerator is continuous in the unconstrained sender strategy. -/
lemma posteriorNumerator_continuous (m : sg.Msg) (a : sg.Act) :
    Continuous (fun f : sg.Theta → sg.Msg → ℝ => sg.posteriorNumerator f m a) := by
  unfold posteriorNumerator
  refine continuous_finset_sum _ (fun θ _ => ?_)
  have h_eval : Continuous (fun f : sg.Theta → sg.Msg → ℝ => f θ m) :=
    (continuous_apply m).comp (continuous_apply θ)
  exact (continuous_const.mul h_eval).mul continuous_const

end SignalingGame

/-! ## Instances on `SignalingDeviator` -/

namespace SignalingGame.SignalingDeviator

variable {sg : SignalingGame}

/-- Equivalence with the canonical sum representation. -/
def equivSum : sg.SignalingDeviator ≃ (sg.Theta ⊕ sg.Msg) where
  toFun
    | .sender θ => .inl θ
    | .receiver m => .inr m
  invFun
    | .inl θ => .sender θ
    | .inr m => .receiver m
  left_inv := fun d => by cases d <;> rfl
  right_inv := fun s => by cases s <;> rfl

instance : DecidableEq sg.SignalingDeviator :=
  fun d₁ d₂ => decidable_of_iff (equivSum d₁ = equivSum d₂) equivSum.injective.eq_iff

instance : Fintype sg.SignalingDeviator := Fintype.ofEquiv _ equivSum.symm

instance : Inhabited sg.SignalingDeviator := ⟨.sender default⟩

end SignalingGame.SignalingDeviator

/-! ## Per-deviator ambient space -/

namespace SignalingGame

variable (sg : SignalingGame)

/-- Ambient strategy-space type per signaling deviator. Sender deviators control a distribution
over messages (ambient `sg.Msg → ℝ`); receiver deviators control a distribution over actions
(ambient `sg.Act → ℝ`). -/
def deviatorAmbient : sg.SignalingDeviator → Type
  | .sender _ => sg.Msg → ℝ
  | .receiver _ => sg.Act → ℝ

instance instNAGDeviatorAmbient (d : sg.SignalingDeviator) :
    NormedAddCommGroup (sg.deviatorAmbient d) := by
  cases d
  · change NormedAddCommGroup (sg.Msg → ℝ); exact inferInstance
  · change NormedAddCommGroup (sg.Act → ℝ); exact inferInstance

instance instNSDeviatorAmbient (d : sg.SignalingDeviator) :
    NormedSpace ℝ (sg.deviatorAmbient d) := by
  cases d
  · change NormedSpace ℝ (sg.Msg → ℝ); exact inferInstance
  · change NormedSpace ℝ (sg.Act → ℝ); exact inferInstance

instance instFDDeviatorAmbient (d : sg.SignalingDeviator) :
    FiniteDimensional ℝ (sg.deviatorAmbient d) := by
  cases d
  · change FiniteDimensional ℝ (sg.Msg → ℝ); exact inferInstance
  · change FiniteDimensional ℝ (sg.Act → ℝ); exact inferInstance

/-- Per-deviator slice: Sender slot lives in the ε-perturbed simplex over `sg.Msg`; receiver slot
in the standard simplex over `sg.Act`. -/
def deviatorSlice (ε : ℝ) : (d : sg.SignalingDeviator) → Set (sg.deviatorAmbient d)
  | .sender _ => PerturbedSimplex (α := sg.Msg) ε
  | .receiver _ => stdSimplex ℝ sg.Act

/-! ## Profile extraction helpers

Given a Kakutani profile `σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)`, the
sender's mixed strategy and receiver's mixed strategy are extracted by pattern-matching on the
deviator. -/

/-- Underlying sender strategy from a Kakutani profile: `θ ↦ (σ (.sender θ)).val`. -/
def profileSenderRaw (ε : ℝ) (σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)) :
    sg.Theta → sg.Msg → ℝ :=
  fun θ => (σ (.sender θ)).val

/-- Underlying receiver strategy from a Kakutani profile: `m ↦ (σ (.receiver m)).val`. -/
def profileReceiverRaw (ε : ℝ) (σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)) :
    sg.Msg → sg.Act → ℝ :=
  fun m => (σ (.receiver m)).val

/-! ## Kakutani payoff

We use the simplified payoff that does not divide by `marginalProb`. Since the marginal is
strictly positive on `PerturbedSimplex ε` (for `ε > 0`), the argmax of `posteriorNumerator` agrees
with the argmax of the posterior-weighted receiver expected payoff. The simplified payoff is a
polynomial in the raw strategies, hence trivially continuous (and obviously affine in the own
slice). -/

/-- Kakutani payoff at deviator `d` on profile `σ`. Sender deviators see the standard signaling
expectation against the receiver's strategy; receiver deviators see the
`posteriorNumerator`-weighted action expectation (no division). -/
def perturbedPayoff (ε : ℝ) (σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)) :
    sg.SignalingDeviator → ℝ
  | .sender θ =>
      ∑ m : sg.Msg, sg.profileSenderRaw ε σ θ m *
        ∑ a : sg.Act, sg.profileReceiverRaw ε σ m a * sg.payoff .sender θ m a
  | .receiver m =>
      ∑ a : sg.Act, sg.profileReceiverRaw ε σ m a *
        sg.posteriorNumerator (sg.profileSenderRaw ε σ) m a

/-! ## Continuity helpers for the perturbed payoff -/

/-- Continuity of the coordinate evaluation `σ ↦ (σ (.sender θ)).val m`. -/
lemma profileSenderRaw_continuous_eval (ε : ℝ) (θ : sg.Theta) (m : sg.Msg) :
    Continuous (fun σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d) =>
      sg.profileSenderRaw ε σ θ m) := by
  have h_eval : Continuous (fun (f : sg.Msg → ℝ) => f m) := continuous_apply m
  exact h_eval.comp
    (continuous_subtype_val.comp (continuous_apply (SignalingDeviator.sender θ)))

/-- Continuity of the coordinate evaluation `σ ↦ (σ (.receiver m)).val a`. -/
lemma profileReceiverRaw_continuous_eval (ε : ℝ) (m : sg.Msg) (a : sg.Act) :
    Continuous (fun σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d) =>
      sg.profileReceiverRaw ε σ m a) := by
  have h_eval : Continuous (fun (f : sg.Act → ℝ) => f a) := continuous_apply a
  exact h_eval.comp
    (continuous_subtype_val.comp (continuous_apply (SignalingDeviator.receiver m)))

/-! ## NashExistenceData for the ε-perturbed signaling game

We package the perturbed signaling fixed-point problem as a `NashExistenceData`. The existence
of an ε-equilibrium then follows from `NashExistenceData.exists_equilibrium`. -/

/-- The ε-perturbed signaling game as a `NashExistenceData`. The deviator index is
`SignalingDeviator`; sender slots live in the ε-perturbed simplex; receiver slots in the standard
simplex. Payoff is `perturbedPayoff` (the simplified version without dividing by the marginal; see
the `perturbedPayoff` docstring for why this preserves the argmax). -/
noncomputable def toPerturbedNashExistenceData (ε : ℝ)
    (hε_nn : 0 ≤ ε) (hε_le : ε ≤ 1 / (Fintype.card sg.Msg : ℝ)) :
    NashExistenceData where
  Player := sg.SignalingDeviator
  V := sg.deviatorAmbient
  Slice := sg.deviatorSlice ε
  hSlice_convex := fun d => by
    cases d with
    | sender _ => exact convex_PerturbedSimplex (α := sg.Msg) ε
    | receiver _ => exact convex_stdSimplex ℝ sg.Act
  hSlice_compact := fun d => by
    cases d with
    | sender _ => exact isCompact_PerturbedSimplex (α := sg.Msg) ε
    | receiver _ => exact isCompact_stdSimplex ℝ sg.Act
  hSlice_nonempty := fun d => by
    cases d with
    | sender _ => exact nonempty_PerturbedSimplex_of_le_inv (α := sg.Msg) hε_nn hε_le
    | receiver _ =>
      refine ⟨fun a => if a = default then 1 else 0, ?_, ?_⟩
      · intro a; dsimp; split_ifs <;> norm_num
      · simp [Finset.sum_ite_eq']
  payoff := fun d σ => sg.perturbedPayoff ε σ d
  payoff_continuous := fun d => by
    cases d with
    | sender θ =>
      unfold perturbedPayoff
      refine continuous_finset_sum _ (fun m _ => ?_)
      refine (sg.profileSenderRaw_continuous_eval ε θ m).mul ?_
      refine continuous_finset_sum _ (fun a _ => ?_)
      exact (sg.profileReceiverRaw_continuous_eval ε m a).mul continuous_const
    | receiver m =>
      unfold perturbedPayoff
      refine continuous_finset_sum _ (fun a _ => ?_)
      refine (sg.profileReceiverRaw_continuous_eval ε m a).mul ?_
      unfold posteriorNumerator
      refine continuous_finset_sum _ (fun θ _ => ?_)
      exact (continuous_const.mul (sg.profileSenderRaw_continuous_eval ε θ m)).mul
        continuous_const
  payoff_affine_in_own := fun d σ => by
    cases d with
    | sender θ =>
      let c : sg.Msg → ℝ := fun m =>
        ∑ a : sg.Act, sg.profileReceiverRaw ε σ m a * sg.payoff .sender θ m a
      refine ⟨(Fintype.linearCombination ℝ c).toAffineMap, ?_⟩
      intro y
      unfold perturbedPayoff
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have hS : sg.profileSenderRaw ε
          (Function.update σ (SignalingDeviator.sender θ) y) θ m = y.1 m := by
        unfold profileSenderRaw; rw [Function.update_self]
      have hR : ∀ a, sg.profileReceiverRaw ε
          (Function.update σ (SignalingDeviator.sender θ) y) m a =
          sg.profileReceiverRaw ε σ m a := by
        intro a
        unfold profileReceiverRaw
        rw [Function.update_of_ne]
        intro h; nomatch h
      rw [hS]
      have hsum_eq : (∑ a, sg.profileReceiverRaw ε σ m a * sg.payoff .sender θ m a) =
          ∑ a, sg.profileReceiverRaw ε
            (Function.update σ (SignalingDeviator.sender θ) y) m a *
            sg.payoff .sender θ m a :=
        Finset.sum_congr rfl fun a _ => by rw [hR a]
      change y.1 m * (∑ a, sg.profileReceiverRaw ε σ m a * sg.payoff .sender θ m a) =
        y.1 m * (∑ a, sg.profileReceiverRaw ε
          (Function.update σ (SignalingDeviator.sender θ) y) m a *
          sg.payoff .sender θ m a)
      rw [hsum_eq]
    | receiver m =>
      let c : sg.Act → ℝ := fun a =>
        sg.posteriorNumerator (sg.profileSenderRaw ε σ) m a
      refine ⟨(Fintype.linearCombination ℝ c).toAffineMap, ?_⟩
      intro y
      unfold perturbedPayoff
      have hS : ∀ θ m', sg.profileSenderRaw ε
          (Function.update σ (SignalingDeviator.receiver m) y) θ m' =
          sg.profileSenderRaw ε σ θ m' := by
        intro θ m'
        unfold profileSenderRaw
        rw [Function.update_of_ne]
        intro h; nomatch h
      have hR : sg.profileReceiverRaw ε
          (Function.update σ (SignalingDeviator.receiver m) y) m = y.1 := by
        unfold profileReceiverRaw; funext a; rw [Function.update_self]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hR_a : sg.profileReceiverRaw ε
          (Function.update σ (SignalingDeviator.receiver m) y) m a = y.1 a := by rw [hR]
      rw [hR_a]
      have hPN : sg.posteriorNumerator (sg.profileSenderRaw ε
          (Function.update σ (SignalingDeviator.receiver m) y)) m a =
          sg.posteriorNumerator (sg.profileSenderRaw ε σ) m a := by
        unfold posteriorNumerator
        exact Finset.sum_congr rfl fun θ _ => by rw [hS θ m]
      rw [hPN, smul_eq_mul]

end SignalingGame

end Econlib.GameTheory
