/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE
public import Econlib.GameTheory.Signaling.Perturbation

/-!
# Signaling games as extensive-form games: The encoded game tree

Encodes a `SignalingGame` (Spence 1973) as an `ExtensiveGame` over the public-event type
`SignalingGame.Event sg = type θ ⊕ msg m ⊕ act a`. The root is a chance node, the sender moves
after `[type θ]`, the receiver moves after `[type θ, msg m]`, and `[type θ, msg m, act a]` is
terminal. The `infoStructure` hides the type from the receiver.

## Main definitions

* `SignalingGame.Event`: Public events at signaling-game histories (type, message, action).
* `SignalingGame.toNodeKind` / `toGameTree`: The encoded game form.
* `SignalingGame.infoStructure`: The information structure hiding the type from the receiver.
* `SignalingGame.toExtensiveForm` / `toExtensiveGame`: The bundled extensive form and game.
* `SignalingGame.continuationValue`: Belief-weighted expected payoff at a public history.

## Main statements

* `SignalingGame.sender_movesAt_iff` / `receiver_movesAt_iff`: Characterizations of the histories
  at which each player moves.

## References

* Spence, Michael. 1973. “Job Market Signaling.” *The Quarterly Journal of Economics* 87 (3): 355.
  [https://doi.org/10.2307/1882010](https://doi.org/10.2307/1882010).

## Tags

signaling game, extensive form, game tree, information structure
-/

@[expose] public noncomputable section

open Econlib.Probability

namespace Econlib.GameTheory

namespace SignalingGame

/-! ## Public events -/

/-- Public events at signaling-game histories: Nature emits a `type`, the sender emits a `msg`, the
receiver emits an `act`. These are all *public* in the framework's sense; the receiver's privacy of
θ is enforced by `infoStructure`. -/
inductive Event (sg : SignalingGame) where
  | type (θ : sg.Theta)
  | msg (m : sg.Msg)
  | act (a : sg.Act)
deriving DecidableEq

variable (sg : SignalingGame)

/-! ## Game tree

`toNodeKind` dispatches on history length; helpers do content-based dispatch inside each length
stratum. -/

/-- Default zero-payoff terminal node, used at every off-canonical history. -/
def junkTerminal : NodeKind SignalingPlayer sg.Event :=
  .terminal (fun _ => 0)

/-- Length-1 dispatch: Sender's decision node at `[type θ]`, terminal otherwise. -/
def handleSingleton (e : sg.Event) : NodeKind SignalingPlayer sg.Event :=
  match e with
  | .type _ =>
      .player
        { mover := .sender
          Choice := sg.Msg
          emit := Event.msg }
  | _ => sg.junkTerminal

/-- Length-2 dispatch: Receiver's decision node at `[type _, msg _]`, terminal otherwise. -/
def handlePair (e1 e2 : sg.Event) : NodeKind SignalingPlayer sg.Event :=
  match e1, e2 with
  | .type _, .msg _ =>
      .player
        { mover := .receiver
          Choice := sg.Act
          emit := Event.act }
  | _, _ => sg.junkTerminal

/-- Length-3 dispatch: Terminal at `[type θ, msg m, act a]` with realized payoffs, junk terminal
otherwise. -/
def handleTriple (e1 e2 e3 : sg.Event) : NodeKind SignalingPlayer sg.Event :=
  match e1, e2, e3 with
  | .type θ, .msg m, .act a =>
      .terminal
        (fun
          | .sender => sg.payoff .sender θ m a
          | .receiver => sg.payoff .receiver θ m a)
  | _, _, _ => sg.junkTerminal

/-- Node kind at a public history. The match is on length: Chance at length 0, the length-1/2/3
helpers, and a junk terminal at length ≥ 4. -/
def toNodeKind : List sg.Event → NodeKind SignalingPlayer sg.Event
  | [] =>
      .chanceFinite
        { Outcome := sg.Theta
          dist := sg.prior
          emit := Event.type }
  | [e] => sg.handleSingleton e
  | [e1, e2] => sg.handlePair e1 e2
  | [e1, e2, e3] => sg.handleTriple e1 e2 e3
  | _ :: _ :: _ :: _ :: _ => sg.junkTerminal

/-- The encoded game form. -/
def toGameTree : GameTree SignalingPlayer sg.Event where
  nodeKind := sg.toNodeKind

@[simp] lemma toGameTree_nodeKind (h : List sg.Event) :
    sg.toGameTree.nodeKind h = sg.toNodeKind h := rfl

@[simp] lemma toNodeKind_nil :
    sg.toNodeKind [] =
      .chanceFinite
        { Outcome := sg.Theta
          dist := sg.prior
          emit := Event.type } := rfl

@[simp] lemma toNodeKind_type (θ : sg.Theta) :
    sg.toNodeKind [.type θ] =
      .player
        { mover := .sender
          Choice := sg.Msg
          emit := Event.msg } := rfl

@[simp] lemma toNodeKind_typeMsg (θ : sg.Theta) (m : sg.Msg) :
    sg.toNodeKind [.type θ, .msg m] =
      .player
        { mover := .receiver
          Choice := sg.Act
          emit := Event.act } := rfl

@[simp] lemma toNodeKind_terminal
    (θ : sg.Theta) (m : sg.Msg) (a : sg.Act) :
    sg.toNodeKind [.type θ, .msg m, .act a] =
      .terminal
        (fun
          | .sender => sg.payoff .sender θ m a
          | .receiver => sg.payoff .receiver θ m a) := rfl

/-! ## Canonical movesAt characterizations

These lemmas characterize the histories at which each player moves. They are used both for
discharging `info_kind_coherent` on `toExtensiveForm` and for downstream proofs that need to reduce
a `movesAt` hypothesis to a canonical history shape. -/

/-- A history at which the sender moves must be of the form `[Event.type θ]`. -/
lemma sender_movesAt_iff (h : List sg.Event) :
    (sg.toGameTree.nodeKind h).movesAt SignalingPlayer.sender ↔
      ∃ θ : sg.Theta, h = [Event.type θ] := by
  constructor
  · intro hm
    match h with
    | [] => exact hm.elim
    | [Event.type θ] => exact ⟨θ, rfl⟩
    | [Event.msg _] => exact hm.elim
    | [Event.act _] => exact hm.elim
    | [_, _] =>
      change (sg.handlePair _ _).movesAt _ at hm
      unfold handlePair at hm
      split at hm
      · cases hm
      · exact hm.elim
    | [_, _, _] =>
      change (sg.handleTriple _ _ _).movesAt _ at hm
      unfold handleTriple at hm
      split at hm <;> exact hm.elim
    | _ :: _ :: _ :: _ :: _ => exact hm.elim
  · rintro ⟨θ, rfl⟩
    rfl

/-- A history at which the receiver moves must be of the form `[Event.type θ, Event.msg m]`. -/
lemma receiver_movesAt_iff (h : List sg.Event) :
    (sg.toGameTree.nodeKind h).movesAt SignalingPlayer.receiver ↔
      ∃ (θ : sg.Theta) (m : sg.Msg), h = [Event.type θ, Event.msg m] := by
  constructor
  · intro hm
    match h with
    | [] => exact hm.elim
    | [Event.type _] => cases hm
    | [Event.msg _] => exact hm.elim
    | [Event.act _] => exact hm.elim
    | [Event.type θ, Event.msg m] => exact ⟨θ, m, rfl⟩
    | [Event.type _, Event.type _] => exact hm.elim
    | [Event.type _, Event.act _] => exact hm.elim
    | [Event.msg _, _] => exact hm.elim
    | [Event.act _, _] => exact hm.elim
    | [_, _, _] =>
      change (sg.handleTriple _ _ _).movesAt _ at hm
      unfold handleTriple at hm
      split at hm <;> exact hm.elim
    | _ :: _ :: _ :: _ :: _ => exact hm.elim
  · rintro ⟨θ, m, rfl⟩
    rfl

/-! ## Information structure -/

/-- The signaling information structure: Sender observes their type, receiver observes the message.
Off-canonical histories return junk observations; these are inert because deviation predicates fire
only at histories where the player moves, and `movesAt` is false at the terminal nodes assigned to
off-canonical histories.

The per-info-set choice types are: Sender (at any θ) plays `Msg`; receiver (at any msg) plays
`Act`. These are direct from the signaling primitives. -/
def infoStructure :
    InfoStructure SignalingPlayer sg.Event where
  Obs
    | .sender   => sg.Theta
    | .receiver => sg.Msg
  observe
    | .sender,   [.type θ]         => θ
    | .receiver, [.type _, .msg m] => m
    | .sender,   _                 => default
    | .receiver, _                 => default
  iChoiceType
    | .sender,   _ => sg.Msg
    | .receiver, _ => sg.Act
  iChoiceFintype
    | .sender,   _ => inferInstance
    | .receiver, _ => inferInstance
  iChoiceDecEq
    | .sender,   _ => inferInstance
    | .receiver, _ => inferInstance
  iChoiceInhabited
    | .sender,   _ => inferInstance
    | .receiver, _ => inferInstance

@[simp] lemma observe_sender_type (θ : sg.Theta) :
    (sg.infoStructure).observe .sender [.type θ] = θ := rfl

@[simp] lemma observe_receiver_typeMsg (θ : sg.Theta) (m : sg.Msg) :
    (sg.infoStructure).observe .receiver [.type θ, .msg m] = m := rfl

/-- The bundled extensive form: The tree paired with the signaling information structure. -/
def toExtensiveForm :
    ExtensiveForm SignalingPlayer sg.Event where
  tree := sg.toGameTree
  info := sg.infoStructure
  iChoice_compatible := by
    intro i h hm
    cases i with
    | sender =>
      obtain ⟨θ, rfl⟩ := (sg.sender_movesAt_iff h).mp hm
      rfl
    | receiver =>
      obtain ⟨θ, m, rfl⟩ := (sg.receiver_movesAt_iff h).mp hm
      rfl

@[simp] lemma toExtensiveForm_tree :
    (sg.toExtensiveForm).tree = sg.toGameTree := rfl

@[simp] lemma toExtensiveForm_info :
    (sg.toExtensiveForm).info = sg.infoStructure := rfl

/-! ## Strategy accessors

Behavioral strategies live in `(sg.toExtensiveForm).BehavioralStrategy`, with one mixed action
at each sender or receiver information set. -/

/-- The sender's mixed strategy at type θ extracted from a behavioral strategy on the encoded
extensive form. -/
def behavioralSender (σ : (sg.toExtensiveForm).BehavioralStrategy) (θ : sg.Theta) :
    stdSimplex ℝ (sg.Msg) :=
  σ .sender θ

/-- The receiver's mixed strategy at message m extracted from a behavioral strategy. The θ argument
is unused because the receiver observes messages, not types. -/
def behavioralReceiver (σ : (sg.toExtensiveForm).BehavioralStrategy)
    (_θ : sg.Theta) (m : sg.Msg) :
    stdSimplex ℝ (sg.Act) :=
  σ .receiver m

/-! ## Continuation value

Belief-weighted expected payoff at a public history, inlining the four canonical depths
(terminal, post-message, post-type, root). Off-canonical histories return `0`. -/

/-- Terminal payoff at `[type θ, msg m, act a]` for player `i`. -/
def terminalPayoff (i : SignalingPlayer)
    (θ : sg.Theta) (m : sg.Msg) (a : sg.Act) : ℝ :=
  sg.payoff i θ m a

/-- Continuation value of a behavioral strategy at a public history. -/
def continuationValue (σ : (sg.toExtensiveForm).BehavioralStrategy) :
    List sg.Event → SignalingPlayer → ℝ
  | [], i =>
      ∑ θ : sg.Theta, sg.prior.pmf θ *
        ∑ m : sg.Msg, (sg.behavioralSender σ θ).val m *
          ∑ a : sg.Act, (sg.behavioralReceiver σ θ m).val a *
            sg.terminalPayoff i θ m a
  | [.type θ], i =>
      ∑ m : sg.Msg, (sg.behavioralSender σ θ).val m *
        ∑ a : sg.Act, (sg.behavioralReceiver σ θ m).val a *
          sg.terminalPayoff i θ m a
  | [.type θ, .msg m], i =>
      ∑ a : sg.Act, (sg.behavioralReceiver σ θ m).val a *
        sg.terminalPayoff i θ m a
  | [.type θ, .msg m, .act a], i => sg.terminalPayoff i θ m a
  | _, _ => 0

/-! ### Bridge lemmas between `playerBehavior` and the signaling-specific accessors

These identify `playerBehavior` at the sender and receiver histories with the
signaling-specific accessors `behavioralSender` and `behavioralReceiver`. -/

/-- At `[Event.type θ]`, the cast `playerBehavior` value-function coincides with the sender's
behavioral mix at type `θ`. -/
lemma playerBehavior_sender_val
    (σ : (sg.toExtensiveForm).BehavioralStrategy) (θ : sg.Theta) :
    (σ.playerBehavior (G := sg.toExtensiveForm) [Event.type θ] rfl).val =
      (sg.behavioralSender σ θ).val := by
  rfl

/-- At `[Event.type θ, Event.msg m]`, the cast `playerBehavior` value-function coincides with the
receiver's behavioral mix at message `m`. -/
lemma playerBehavior_receiver_val
    (σ : (sg.toExtensiveForm).BehavioralStrategy) (θ : sg.Theta) (m : sg.Msg) :
    (σ.playerBehavior (G := sg.toExtensiveForm) [Event.type θ, Event.msg m] rfl).val =
      (sg.behavioralReceiver σ θ m).val := by
  rfl

/-- The encoded extensive game. Unilateral deviation is fixed by
`ExtensiveForm.unilateralDeviation` (the standard "i-only agreement at every history" predicate);
there is no game-supplied notion to override. -/
def toExtensiveGame :
    ExtensiveGame SignalingPlayer sg.Event where
  toExtensiveForm := sg.toExtensiveForm
  stepPayoff := fun _ _ _ => 0
  discount := 1
  discount_mem := ⟨zero_le_one, le_refl _⟩
  no_chanceGeneral := by
    -- Ban general-chance by inspection of `toNodeKind`: every branch produces a constructor
    -- other than `.chanceGeneral`.
    intro h n
    match h with
    | [] => intro hbad; cases hbad
    | [e] =>
      change sg.handleSingleton e ≠ _
      unfold handleSingleton
      split <;> (intro hbad; cases hbad)
    | [e1, e2] =>
      change sg.handlePair e1 e2 ≠ _
      unfold handlePair
      split <;> (intro hbad; cases hbad)
    | [e1, e2, e3] =>
      change sg.handleTriple e1 e2 e3 ≠ _
      unfold handleTriple
      split <;> (intro hbad; cases hbad)
    | _ :: _ :: _ :: _ :: _ =>
      change sg.junkTerminal ≠ _
      unfold junkTerminal
      intro hbad; cases hbad
  continuationValue := sg.continuationValue
  continuationValue_eq := by
    -- Bellman at every history: case-split on history shape (5 canonical cases plus junk
    -- terminals at off-canonical shapes). Each branch reduces by the simp lemmas for `toNodeKind`
    -- together with the `playerBehavior_*_val` bridges defined above.
    intro σ h i
    match h with
    | [] =>
      -- Root chance node: nodeStepValue_chanceFinite produces
      -- ∑ θ, prior θ * (0 + 1 * cont [type θ])
      simp only [continuationValue, nodeStepValue_chanceFinite, toExtensiveForm_tree,
        toGameTree_nodeKind, toNodeKind_nil, zero_add, one_mul]
      rfl
    | [Event.type θ] =>
      simp only [continuationValue, nodeStepValue_player, toExtensiveForm_tree,
        toGameTree_nodeKind, toNodeKind_type, zero_add, one_mul,
        playerBehavior_sender_val]
      rfl
    | [Event.msg _] =>
      -- Junk terminal: nodeStepValue_terminal returns (fun _ => 0) i = 0, matches continuationValue
      rfl
    | [Event.act _] => rfl
    | [Event.type θ, Event.msg m] =>
      simp only [continuationValue, nodeStepValue_player, toExtensiveForm_tree,
        toGameTree_nodeKind, toNodeKind_typeMsg, zero_add, one_mul,
        playerBehavior_receiver_val]
      rfl
    | [Event.type _, Event.type _] => rfl
    | [Event.type _, Event.act _] => rfl
    | [Event.msg _, _] => rfl
    | [Event.act _, _] => rfl
    | [Event.type θ, Event.msg m, Event.act a] =>
      -- Terminal: nodeStepValue_terminal evaluates (fun | .sender => … | .receiver => …) i.
      cases i <;> rfl
    | [Event.type _, Event.msg _, Event.type _] => rfl
    | [Event.type _, Event.msg _, Event.msg _] => rfl
    | [Event.type _, Event.type _, _] => rfl
    | [Event.type _, Event.act _, _] => rfl
    | [Event.msg _, _, _] => rfl
    | [Event.act _, _, _] => rfl
    | a :: b :: c :: d :: tail =>
      -- Junk terminal: LHS continuationValue falls through to the `_, _ => 0` branch; RHS reduces
      -- by nodeStepValue_terminal at junkTerminal = .terminal (fun _ => 0). Splitting on each of
      -- the first four cells separates the catchall match arm from the constructor-specific ones.
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
  continuationValue_unique := by
    -- Left disjunct: the tree has finite depth 4. Every history of length ≥ 4 falls into the
    -- `_ :: _ :: _ :: _ :: _` branch of `toNodeKind`, which returns `junkTerminal`.
    refine Or.inl ⟨4, ?_⟩
    intro h hlen
    refine ⟨fun _ => 0, ?_⟩
    match h, hlen with
    | _ :: _ :: _ :: _ :: _, _ => rfl

@[simp] lemma toExtensiveGame_toExtensiveForm :
    (sg.toExtensiveGame).toExtensiveForm = sg.toExtensiveForm := rfl

end SignalingGame

end Econlib.GameTheory
