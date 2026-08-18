/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.Bridge.Assessment

/-!
# Morphism from signaling refined equilibrium to extensive PBE

The morphism `signalingToExtensiveMorphism` transports a signaling-level refined equilibrium to a
perfect Bayesian equilibrium of the encoded extensive game. The forward map of strategies is
`SignalingAssessment.toAssessment`, and the backward deviator map sends `(.sender, θ) ↦ .sender θ`
and `(.receiver, m) ↦ .receiver m`.

## Main definitions

* `SignalingGame.signalingToExtensiveMorphism`: The refined-game morphism transporting signaling
  equilibria to PBE of the encoded extensive game.

## Main statements

* `SignalingGame.isSequentiallyRational_toAssessment_of_oneShot`: One-shot sequential rationality
  of the embedded assessment already implies full sequential rationality, because each player moves
  at most once on any play path.
* `IsPerfectBayesianEquilibrium.of_isSignalingPerfectBayesianEquilibrium_toAssessment`: A signaling
  PBE induces a PBE of the encoded extensive game.

## References

* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling game, perfect bayesian equilibrium, sequential rationality, one-shot deviation, morphism
-/

@[expose] public noncomputable section

open Econlib.Probability

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ## Morphism from signaling refined equilibrium to extensive PBE -/

/-- Continuation value at `[type θ]` under `SignalingAssessment.toBehavioral` equals the sender's
expected payoff at type θ, weighted by the sender's mixed strategy at θ. -/
lemma SignalingAssessment.continuationValue_type
    (a : sg.SignalingAssessment) (θ : sg.Theta) :
    sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
        [Event.type θ] .sender =
      ∑ m : sg.Msg, (a.senderStrategy θ).pmf m *
        sg.senderExpectedPayoff a.receiverStrategy θ m := by
  refine Finset.sum_congr rfl (fun m _ => ?_)
  change (a.senderStrategy θ).pmf m *
      ∑ act : sg.Act, (a.receiverStrategy m).pmf act *
        sg.payoff .sender θ m act =
    (a.senderStrategy θ).pmf m * sg.senderExpectedPayoff a.receiverStrategy θ m
  rw [SignalingGame.senderExpectedPayoff, FinDist.expect_eq_sum]

/-- Continuation value at `[type θ, msg m]` under `SignalingAssessment.toBehavioral` for the
receiver: A per-action sum weighted by the receiver's mixed strategy at message m. -/
lemma SignalingAssessment.continuationValue_typeMsg
    (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) :
    sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
        [Event.type θ, Event.msg m] .receiver =
      ∑ act : sg.Act, (a.receiverStrategy m).pmf act *
        sg.payoff .receiver θ m act := rfl

/-- The signaling-to-extensive morphism. Transports refined signaling equilibria forward to PBE of
the encoded extensive game. -/
def signalingToExtensiveMorphism (sg : SignalingGame) :
    RefinedGameMorphism sg.signalingPBEPred ((sg.toExtensiveGame).pbePred) where
  toFun := fun a => SignalingAssessment.toAssessment (sg := sg) a
  deviatorMap := fun ⟨i, obs⟩ =>
    match i, obs with
    | .sender, θ => .sender θ
    | .receiver, m => .receiver m
  swap_lifts := by
    rintro ⟨(i : SignalingPlayer), obs⟩ a a_target' ⟨h_beliefs_eq, h_strat_dev⟩
    classical
    cases i with
    | sender =>
      refine ⟨{
        senderStrategy := fun θ' =>
          if θ' = obs then
            (FinDist.ofSimplex (a_target'.strategy .sender obs))
          else a.senderStrategy θ'
        receiverStrategy := a.receiverStrategy
        belief := a.belief }, ?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        intro θ' hne
        change (if θ' = obs then
            (FinDist.ofSimplex (a_target'.strategy .sender obs))
          else a.senderStrategy θ') = a.senderStrategy θ'
        rw [if_neg hne]
      · have h_strat :
            (SignalingAssessment.toAssessment (sg := sg)
              { senderStrategy := fun θ' =>
                  if θ' = obs then
                    (FinDist.ofSimplex (a_target'.strategy .sender obs))
                  else a.senderStrategy θ'
                receiverStrategy := a.receiverStrategy
                belief := a.belief }).strategy = a_target'.strategy := by
          funext j obs'
          match j with
          | .sender =>
            simp only [SignalingAssessment.toAssessment_strategy,
              SignalingAssessment.toBehavioral_sender]
            split_ifs with hθ
            · subst hθ; rfl
            · exact (h_strat_dev .sender obs' (by
                intro h
                have h1 := (Sigma.mk.injEq _ _ _ _).mp h
                exact hθ (eq_of_heq h1.2))).symm
          | .receiver =>
            simp only [SignalingAssessment.toAssessment_strategy,
              SignalingAssessment.toBehavioral_receiver]
            exact (h_strat_dev .receiver obs' (by
              intro h
              have h1 := (Sigma.mk.injEq _ _ _ _).mp h
              exact SignalingPlayer.noConfusion h1.1)).symm
        have h_bels :
            (SignalingAssessment.toAssessment (sg := sg)
              { senderStrategy := fun θ' =>
                  if θ' = obs then
                    (FinDist.ofSimplex (a_target'.strategy .sender obs))
                  else a.senderStrategy θ'
                receiverStrategy := a.receiverStrategy
                belief := a.belief }).beliefs = a_target'.beliefs := h_beliefs_eq.symm
        -- The transported inner assessment equals the target: equal field-by-field, so equal by
        -- structure eta on the target.
        obtain ⟨t_strat, t_bels⟩ := a_target'
        exact congr_arg₂ Assessment.mk h_strat h_bels
    | receiver =>
      refine ⟨{
        senderStrategy := a.senderStrategy
        receiverStrategy := fun m' =>
          if m' = obs then
            (FinDist.ofSimplex (a_target'.strategy .receiver obs))
          else a.receiverStrategy m'
        belief := a.belief }, ?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        intro m' hne
        change (if m' = obs then
            (FinDist.ofSimplex (a_target'.strategy .receiver obs))
          else a.receiverStrategy m') = a.receiverStrategy m'
        rw [if_neg hne]
      · have h_strat :
            (SignalingAssessment.toAssessment (sg := sg)
              { senderStrategy := a.senderStrategy
                receiverStrategy := fun m' =>
                  if m' = obs then
                    (FinDist.ofSimplex (a_target'.strategy .receiver obs))
                  else a.receiverStrategy m'
                belief := a.belief }).strategy = a_target'.strategy := by
          funext j obs'
          match j with
          | .sender =>
            simp only [SignalingAssessment.toAssessment_strategy,
              SignalingAssessment.toBehavioral_sender]
            exact (h_strat_dev .sender obs' (by
              intro h
              have h1 := (Sigma.mk.injEq _ _ _ _).mp h
              exact SignalingPlayer.noConfusion h1.1)).symm
          | .receiver =>
            simp only [SignalingAssessment.toAssessment_strategy,
              SignalingAssessment.toBehavioral_receiver]
            split_ifs with hm
            · subst hm; rfl
            · exact (h_strat_dev .receiver obs' (by
                intro h
                have h1 := (Sigma.mk.injEq _ _ _ _).mp h
                exact hm (eq_of_heq h1.2))).symm
        have h_bels :
            (SignalingAssessment.toAssessment (sg := sg)
              { senderStrategy := a.senderStrategy
                receiverStrategy := fun m' =>
                  if m' = obs then
                    (FinDist.ofSimplex (a_target'.strategy .receiver obs))
                  else a.receiverStrategy m'
                belief := a.belief }).beliefs = a_target'.beliefs := h_beliefs_eq.symm
        -- The transported inner assessment equals the target: equal field-by-field, so equal by
        -- structure eta on the target.
        obtain ⟨t_strat, t_bels⟩ := a_target'
        exact congr_arg₂ Assessment.mk h_strat h_bels
  value_eq := by
    rintro ⟨i, obs⟩ a
    cases i with
    | sender =>
      change ∑ x ∈
          ({sg.senderInfoSet obs} :
            Finset ((sg.toExtensiveForm).InfoSet .sender obs)),
        (SignalingAssessment.toBeliefSystem (sg := sg) a).belief .sender obs x *
          sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
            x.1 .sender = _
      rw [Finset.sum_singleton]
      change (1 : ℝ) *
        sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
          [Event.type obs] .sender = _
      rw [one_mul]
      exact SignalingAssessment.continuationValue_type (sg := sg) a obs
    | receiver =>
      change ∑ x ∈ sg.receiverSupport obs,
        (SignalingAssessment.toBeliefSystem (sg := sg) a).belief .receiver obs x *
          sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
            x.1 .receiver = _
      unfold receiverSupport
      rw [Finset.sum_image
        (fun θ₁ _ θ₂ _ heq => sg.receiverInfoSet_injective obs heq)]
      change ∑ θ : sg.Theta,
        (SignalingAssessment.toBeliefSystem (sg := sg) a).belief
          .receiver obs (sg.receiverInfoSet obs θ) *
          sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
            [Event.type θ, Event.msg obs] .receiver =
        ∑ θ : sg.Theta, (a.belief obs).pmf θ *
          ∑ act : sg.Act, (a.receiverStrategy obs).pmf act *
            sg.payoff .receiver θ obs act
      refine Finset.sum_congr rfl (fun θ _ => ?_)
      change sg.receiverBelief a obs
          (sg.receiverInfoSet obs θ) *
          sg.continuationValue (SignalingAssessment.toBehavioral (sg := sg) a)
            [Event.type θ, Event.msg obs] .receiver = _
      rw [sg.receiverBelief_canonical a obs θ,
        SignalingAssessment.continuationValue_typeMsg (sg := sg) a θ obs]
  valid_preserves := fun a h_consistent =>
    SignalingAssessment.toAssessment_IsBayesConsistent (sg := sg) a h_consistent

/-- **Single-move upgrade.** In a signaling game each player moves at most once on any play path
(the sender at its type, the receiver at its message), so no player has two information sets
stacked on a single path. Consequently a **unilateral** deviation by player `i` affects the
continuation value at any information set of `i` only through the single on-path coordinate, acting
there exactly as a **one-shot** deviation. Hence one-shot sequential rationality already implies
full sequential rationality.

Concretely, `continuationValue s [type θ] i` (sender information set) depends on `s` only through
`s .sender θ` and `s .receiver ·`, and `continuationValue s [type θ, msg m] i` (receiver
information set) only through `s .receiver m`; see the closed forms in
`SignalingGame.continuationValue`. -/
theorem isSequentiallyRational_toAssessment_of_oneShot
    (sg : SignalingGame) (a : sg.SignalingAssessment)
    (hone : IsSequentiallyRationalOneShot sg.toExtensiveGame
      (SignalingAssessment.toAssessment (sg := sg) a)) :
    IsSequentiallyRational sg.toExtensiveGame
      (SignalingAssessment.toAssessment (sg := sg) a) := by
  classical
  intro i obs σ' hdev
  -- One-shot surgery: τ copies σ' at the single deviating coordinate (i, obs) and the equilibrium
  -- strategy `toBehavioral a` elsewhere. Equality is decided classically on the sigma type.
  set τ : sg.toExtensiveForm.BehavioralStrategy := fun j obs' =>
    if (⟨j, obs'⟩ : Σ k, sg.toExtensiveForm.info.Obs k) = ⟨i, obs⟩ then σ' j obs'
    else (SignalingAssessment.toBehavioral (sg := sg) a) j obs' with hτ_def
  -- τ is a one-shot deviation: off the (i, obs) coordinate it is the equilibrium strategy.
  have hτ_dev : IsInfoSetDeviation sg.toExtensiveForm i obs
      (SignalingAssessment.toBehavioral (sg := sg) a) τ := by
    intro j obs' hne
    rw [hτ_def]
    exact if_neg hne
  -- Both σ' and τ are unilateral i-deviations agreeing with `toBehavioral a` off (i, obs); at the
  -- single info set `obs` the continuation value only sees the on-path coordinate, so the two
  -- assessment values coincide.
  have hval_eq :
      assessmentValue sg.toExtensiveGame
          { strategy := σ', beliefs := (SignalingAssessment.toAssessment (sg := sg) a).beliefs }
          i obs =
        assessmentValue sg.toExtensiveGame
          { strategy := τ, beliefs := (SignalingAssessment.toAssessment (sg := sg) a).beliefs }
          i obs := by
    -- Both assessment values are belief-weighted sums of continuation values over the same support
    -- with the same belief weights; only the continuation-value factor differs by strategy.
    -- σ' and τ agree at every coordinate read by the continuation value: the on-path coordinate
    -- `(i, obs)` (where both equal σ') and every off-player coordinate `k ≠ i` (where both equal
    -- the equilibrium strategy — σ' by unilaterality, τ by the `if_neg` branch).
    have hστ : ∀ (k : SignalingPlayer) (obs'' : sg.toExtensiveForm.info.Obs k),
        (⟨k, obs''⟩ : Σ l, sg.toExtensiveForm.info.Obs l) = ⟨i, obs⟩ ∨ k ≠ i →
          σ' k obs'' = τ k obs'' := by
      intro k obs'' hk
      rw [hτ_def]
      simp only
      rcases hk with hk | hk
      · rw [if_pos hk]
      · rw [if_neg (fun h => hk (congrArg Sigma.fst h))]
        exact hdev k obs'' hk
    unfold assessmentValue
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine congrArg (_ * ·) ?_
    -- The continuation value at `x.1` reads the strategy only through coordinates on which σ' and τ
    -- agree (`hστ`); case on the mover to fix the canonical history shape of `x.1`.
    obtain ⟨h, hmoves, hobs⟩ := x
    cases i with
    | sender =>
      obtain ⟨θ, rfl⟩ := (sg.sender_movesAt_iff h).mp hmoves
      have hθ : θ = obs := hobs
      subst hθ
      -- Sender continuation at `[type θ]` reads `σ .sender θ` (the on-path coordinate) and every
      -- `σ .receiver m` (off-player); σ' and τ agree on both via `hστ`.
      have hs : sg.behavioralSender σ' θ = sg.behavioralSender τ θ :=
        hστ .sender θ (Or.inl rfl)
      have hr : ∀ m : sg.Msg, sg.behavioralReceiver σ' θ m = sg.behavioralReceiver τ θ m :=
        fun m => hστ .receiver m (Or.inr (fun h => SignalingPlayer.noConfusion h))
      change ∑ m : sg.Msg, (sg.behavioralSender σ' θ).val m *
          ∑ act : sg.Act, (sg.behavioralReceiver σ' θ m).val act *
            sg.terminalPayoff .sender θ m act =
        ∑ m : sg.Msg, (sg.behavioralSender τ θ).val m *
          ∑ act : sg.Act, (sg.behavioralReceiver τ θ m).val act *
            sg.terminalPayoff .sender θ m act
      rw [hs]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hr m]
    | receiver =>
      obtain ⟨θ, m, rfl⟩ := (sg.receiver_movesAt_iff h).mp hmoves
      have hm : m = obs := hobs
      subst hm
      -- Receiver continuation at `[type θ, msg m]` reads only `σ .receiver m` (the on-path
      -- coordinate), on which σ' and τ agree via `hστ`.
      have hr : sg.behavioralReceiver σ' θ m = sg.behavioralReceiver τ θ m :=
        hστ .receiver m (Or.inl rfl)
      change ∑ act : sg.Act, (sg.behavioralReceiver σ' θ m).val act *
            sg.terminalPayoff .receiver θ m act =
        ∑ act : sg.Act, (sg.behavioralReceiver τ θ m).val act *
            sg.terminalPayoff .receiver θ m act
      rw [hr]
  -- One-shot rationality at `(i, obs)` against τ, rewritten back to σ' via `hval_eq`.
  rw [hval_eq]
  exact hone i obs τ hτ_dev

/-- A signaling PBE assessment induces a (full) PBE of the encoded extensive game. The morphism
delivers the one-shot refinement; `isSequentiallyRational_toAssessment_of_oneShot` upgrades the
sequential-rationality half to the full Fudenberg–Tirole notion using the single-move structure. -/
theorem IsPerfectBayesianEquilibrium.of_isSignalingPerfectBayesianEquilibrium_toAssessment
    {sg : SignalingGame} {a : sg.SignalingAssessment}
    (h : sg.IsSignalingPBE a) :
    IsPerfectBayesianEquilibrium (sg.toExtensiveGame)
      (SignalingAssessment.toAssessment (sg := sg) a) := by
  have hone : IsPerfectBayesianEquilibriumOneShot (sg.toExtensiveGame)
      (SignalingAssessment.toAssessment (sg := sg) a) := by
    rw [IsPerfectBayesianEquilibriumOneShot_iff_pbePred]
    exact (signalingToExtensiveMorphism sg).transport h
  exact ⟨sg.isSequentiallyRational_toAssessment_of_oneShot a hone.1, hone.2⟩

end SignalingGame

end Econlib.GameTheory
