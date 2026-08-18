/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE
public import Econlib.Math.Data.Option.HEq
import Mathlib.Data.Finset.Max

/-!
# Finite perfect-information trees: Basic API

This file defines `FinitePerfectInfoTree`, a scoped `Choice`-indexed inductive representation of
finite perfect-information trees (Kuhn 1953), together with its embedding into the history-based
extensive-form API.

Each nonterminal node carries its own finite `Choice` type and an injective `emit : Choice ↪ E`
mapping local choices to public events; the partial inverse `decodeEmit` is derived from `emit`'s
injectivity. Every player observes the full history, so information sets are singletons and
info-set respect is automatic on the embedded `ExtensiveForm`.

## Main definitions

* `FinitePerfectInfoTree`: Scoped `Choice`-indexed inductive tree of terminal and single-player
  decision nodes.
* `decodeEmit`: Partial inverse of an injective `emit : Choice ↪ E`.
* `LocalBehavioralStrategy`, `LocalPureStrategy`: Per-node strategy types for a scoped tree.
* `subtreeAt`, `nodeKindAt`, `toGameTree`, `toExtensiveForm`: The embedding into the history-based
  game form and the perfect-information `ExtensiveForm`.
* `LocalBehavioralStrategy.toBehavioral`, `LocalBehavioralStrategy.toBehavioralStrategy`: Embedding
  of a local strategy into a per-history behavioral profile and the framework `BehavioralStrategy`.
* `LocalBehavioralStrategy.at`, `shiftBehavioralAtChoice`: Per-history and per-choice navigators.

## Main statements

* `decodeEmit_emit`, `decodeEmit_eq_some_iff`: Round-trip and characterization of `decodeEmit`.
* `subtreeAt_append`, `subtreeAt_emit_cons`: Navigation laws for `subtreeAt`.
* `shiftBehavioralAtChoice_toBehavioral`: Shifting an embedded strategy past an emitted event
  recovers the embedded child strategy.

## Notes

Recursive value evaluation, backward induction, the subgame-perfect strategy predicate, the
one-shot deviation principle, and the `EquilibriumProblem` packaging live in sibling files.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, perfect information, game tree, behavioral strategy
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u v

/-- Partial inverse of an injective `emit : Choice ↪ E`: Returns the unique preimage when one
exists, `none` otherwise. -/
noncomputable def decodeEmit {Choice E : Type u} (emit : Choice ↪ E) (e : E) : Option Choice :=
  open Classical in
  if h : ∃ c, emit c = e then some (Classical.choose h) else none

/-- `decodeEmit` inverts `emit` on its range: Decoding an emitted event recovers the choice. -/
theorem decodeEmit_emit {Choice E : Type u} (emit : Choice ↪ E) (c : Choice) :
    decodeEmit emit (emit c) = some c := by
  have hex : ∃ c', emit c' = emit c := ⟨c, rfl⟩
  unfold decodeEmit
  rw [dif_pos hex]
  exact congrArg some (emit.injective (Classical.choose_spec hex))

/-- `decodeEmit emit e` returns `some c` exactly when `e` is the event emitted by `c`. -/
theorem decodeEmit_eq_some_iff {Choice E : Type u} (emit : Choice ↪ E) (e : E) (c : Choice) :
    decodeEmit emit e = some c ↔ emit c = e := by
  refine ⟨fun hsome => ?_, fun hemit => hemit ▸ decodeEmit_emit emit c⟩
  -- forward: the `some` value fixes `Classical.choose`'s witness
  unfold decodeEmit at hsome
  by_cases h : ∃ c', emit c' = e
  · rw [dif_pos h] at hsome
    rw [← Option.some.inj hsome]
    exact Classical.choose_spec h
  · rw [dif_neg h] at hsome; exact absurd hsome (by simp)

/-- A finite perfect-information tree. Each nonterminal node carries a node-local finite choice
type `Choice` and an injective public-event encoder `emit : Choice ↪ E`. The decoder that navigates
histories back into choices is derived from `emit`'s injectivity (see `decodeEmit`), not carried as
a separate field. -/
inductive FinitePerfectInfoTree (I : Type u) (E : Type u) where
  /-- A terminal node with realized payoffs. -/
  | terminal (payoff : I → ℝ)
  /-- A single-player decision node with a node-local finite choice type and injective emit. -/
  | decision
      (mover : I)
      (Choice : Type u)
      [Fintype Choice]
      [DecidableEq Choice]
      [Nonempty Choice]
      [Inhabited Choice]
      (emit : Choice ↪ E)
      (child : Choice → FinitePerfectInfoTree I E)

namespace FinitePerfectInfoTree

variable {I E : Type u}

/-- A selected maximizer of a real-valued function over a nonempty fintype of choices. -/
noncomputable def bestChoice (Choice : Type u) [Fintype Choice] [Nonempty Choice]
    (score : Choice → ℝ) : Choice :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset Choice) score
    (Finset.univ_nonempty (α := Choice)))

/-- `bestChoice` attains the maximum: Every choice scores at most as high as `bestChoice`. -/
theorem bestChoice_isBest (Choice : Type u) [Fintype Choice] [Nonempty Choice]
    (score : Choice → ℝ) (a : Choice) :
    score a ≤ score (bestChoice Choice score) :=
  (Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset Choice) score
      (Finset.univ_nonempty (α := Choice)))).2 a (Finset.mem_univ a)

/-- If `c` strictly dominates every other choice under `score`, then `bestChoice` returns `c`. -/
theorem bestChoice_eq_of_strictArgmax (Choice : Type u) [Fintype Choice] [Nonempty Choice]
    (score : Choice → ℝ) (c : Choice)
    (h : ∀ c' : Choice, c' ≠ c → score c' < score c) :
    bestChoice Choice score = c := by
  by_contra hne
  have hbest : score c ≤ score (bestChoice Choice score) :=
    bestChoice_isBest Choice score c
  have hlt : score (bestChoice Choice score) < score c := h _ hne
  linarith

/-- A local behavioral strategy for a scoped finite tree. -/
def LocalBehavioralStrategy : FinitePerfectInfoTree I E → Type u
  | .terminal _payoff => PUnit
  | @FinitePerfectInfoTree.decision _ _ _mover Choice _ _ _ _ _emit child =>
      stdSimplex ℝ Choice × ((c : Choice) → (child c).LocalBehavioralStrategy)

/-- A local pure strategy for a scoped finite tree. -/
def LocalPureStrategy : FinitePerfectInfoTree I E → Type u
  | .terminal _payoff => PUnit
  | @FinitePerfectInfoTree.decision _ _ _mover Choice _ _ _ _ _emit child =>
      Choice × ((c : Choice) → (child c).LocalPureStrategy)

/-- The node kind at the root of a scoped finite tree. -/
def rootNodeKind : FinitePerfectInfoTree I E → NodeKind I E
  | .terminal payoff => .terminal payoff
  | @FinitePerfectInfoTree.decision _ _ mover Choice _ _ _ _ emit _child =>
      .player
        { mover := mover
          Choice := Choice
          emit := emit }

/-- The subtree reached after a finite public history.

Illegal continuations (events not in `emit`'s range) are sent to a zero-payoff terminal node. This
keeps the embedded history-based `GameTree` total while preserving the intended tree on legal
histories. -/
def subtreeAt : FinitePerfectInfoTree I E → List E →
    FinitePerfectInfoTree I E
  | .terminal payoff, _ => .terminal payoff
  | T@(@FinitePerfectInfoTree.decision _ _ _ _ _ _ _ _ _ _), [] => T
  | @FinitePerfectInfoTree.decision _ _ _mover _Choice _ _ _ _ emit child, e :: rest =>
      match decodeEmit emit e with
      | some c => subtreeAt (child c) rest
      | none => .terminal (fun _ => 0)

/-- Node kind reached by a finite public history in the embedded history-based game form. -/
def nodeKindAt (T : FinitePerfectInfoTree I E) (h : List E) : NodeKind I E :=
  (T.subtreeAt h).rootNodeKind

/-- Embed a scoped finite perfect-information tree into the unified history-based `GameTree`. -/
def toGameTree (T : FinitePerfectInfoTree I E) : GameTree I E where
  nodeKind := T.nodeKindAt

/-- The perfect-information `ExtensiveForm` associated to a finite tree. Every player observes the
full history; info sets are singletons so info-set respect is automatic. -/
abbrev toExtensiveForm [DecidableEq I] (T : FinitePerfectInfoTree I E) : ExtensiveForm I E :=
  ExtensiveForm.ofGameTreePerfectInfo T.toGameTree

/-- Per-history behavioral profile shape on the embedded game tree. This is the underlying function
type of `T.toExtensiveForm.BehavioralStrategy`; the framework subtype additionally carries an
info-set-respect proof which is automatic for perfect-information forms. Internal proofs work in
this raw shape and convert at the boundary via `BehavioralStrategy.ofPerfectInfo`. -/
abbrev RawBehavioral (T : FinitePerfectInfoTree I E) : Type u :=
  (h : List E) → (T.toGameTree.nodeKind h).Behavior

/-- The root behavior induced by a local finite-tree strategy. -/
def LocalBehavioralStrategy.rootBehavior {T : FinitePerfectInfoTree I E}
    (s : T.LocalBehavioralStrategy) : T.rootNodeKind.Behavior :=
  match T, s with
  | .terminal _payoff, _ => PUnit.unit
  | @FinitePerfectInfoTree.decision _ _ _ _ _ _ _ _ _ _, s => s.1

/-- The continuation finite-tree strategy reached after a public history. -/
def LocalBehavioralStrategy.at :
    (T : FinitePerfectInfoTree I E) → T.LocalBehavioralStrategy → (h : List E) →
      (T.subtreeAt h).LocalBehavioralStrategy
  | .terminal _payoff, _s, _h => PUnit.unit
  | @FinitePerfectInfoTree.decision _ _ _ _ _ _ _ _ _ _, s, [] => s
  | @FinitePerfectInfoTree.decision _ _ _mover _Choice _ _ _ _ emit child, s, e :: rest => by
      unfold subtreeAt
      cases hdec : decodeEmit emit e with
      | some c => exact (s.2 c).at (child c) rest
      | none => exact PUnit.unit

/-- Embed a local finite-tree strategy into a per-history behavioral profile on the embedded
`GameTree`. The framework `BehavioralStrategy` (subtype with info-set-respect proof) is built by
`LocalBehavioralStrategy.toBehavioralStrategy`. -/
def LocalBehavioralStrategy.toBehavioral :
    (T : FinitePerfectInfoTree I E) → T.LocalBehavioralStrategy → T.RawBehavioral
  | .terminal _payoff, _s => fun _h => PUnit.unit
  | @FinitePerfectInfoTree.decision _ _ _mover _Choice _ _ _ _ emit child, s => fun h => by
      cases h with
      | nil => exact s.1
      | cons e rest =>
          change NodeKind.Behavior (((@FinitePerfectInfoTree.decision _ _ _mover _Choice _ _ _ _
            emit child).subtreeAt (e :: rest)).rootNodeKind)
          unfold subtreeAt
          cases hdec : decodeEmit emit e with
          | some c =>
              exact LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) rest
          | none =>
              exact PUnit.unit

/-- Wrap a local strategy as a framework `BehavioralStrategy` on the perfect-information extensive
form. Info-set respect is automatic for perfect-information forms. -/
noncomputable def LocalBehavioralStrategy.toBehavioralStrategy [DecidableEq I]
    (T : FinitePerfectInfoTree I E) (s : T.LocalBehavioralStrategy) :
    T.toExtensiveForm.BehavioralStrategy :=
  ExtensiveForm.BehavioralStrategy.ofPerfectInfo (LocalBehavioralStrategy.toBehavioral T s)

/-- At a terminal root, the embedded behavior is the unique `PUnit` element. -/
@[simp] theorem toBehavioral_terminal_root
    (payoff : I → ℝ) (s : LocalBehavioralStrategy (.terminal (I := I) (E := E) payoff)) :
    LocalBehavioralStrategy.toBehavioral (.terminal payoff) s [] = PUnit.unit := rfl

/-- At a decision root, the embedded behavior is the local root mix `s.1`. -/
@[simp] theorem toBehavioral_decision_root
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child)) :
    LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child) s [] = s.1 := rfl

/-- Transporting an equality-indexed function and immediately applying it is heterogeneously equal
to applying the original function to the inverse equality. -/
theorem eqRec_function_apply_heq
    {α : Sort u} {D : α → Sort v}
    {a b : α}
    (f : a = b → D b)
    (hba : b = a) (haa : a = a) :
    HEq
      (Eq.rec
        (motive := fun x _ => a = x → D x)
        f hba haa)
      (f hba.symm) := by
  cases hba
  rfl

/-- When `decodeEmit emit e = some c`, the embedded behavior at `e :: h` agrees up to HEq with the
embedded child behavior at `h`. -/
theorem toBehavioral_decision_cons_some_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (e : E) (c : Choice) (h : List E) (hdec : decodeEmit emit e = some c) :
    HEq
      (LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child) s (e :: h))
      (LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h) := by
  rw [LocalBehavioralStrategy.toBehavioral.eq_2]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans
    (Option.rec_apply_heq_some
      (C := fun x =>
        (match x with
          | some c => (child c).subtreeAt h
          | none => terminal fun _ => 0).rootNodeKind.Behavior)
      (x := decodeEmit emit e) (c := c) (h := hdec)
      _ _)
  exact eqRec_function_apply_heq
    (D := fun x =>
      (match x with
        | some c => (child c).subtreeAt h
        | none => terminal fun _ => 0).rootNodeKind.Behavior)
    (a := decodeEmit emit e) (b := some c)
    (fun _ => LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h) _ _

/-- Specialization of `toBehavioral_decision_cons_some_heq` to an emitted event `emit c`. -/
@[simp] theorem toBehavioral_decision_emit_cons_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (h : List E) :
    HEq
      (LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child) s (emit c :: h))
      (LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h) :=
  toBehavioral_decision_cons_some_heq mover Choice emit child s
    (emit c) c h (decodeEmit_emit emit c)

/-! ### `LocalBehavioralStrategy.at` simp/eq kit

Navigation lemmas for `LocalBehavioralStrategy.at`. Together these let us peel off the
annotated `cases hdec : decodeEmit emit e` discriminant inside the `at` body and rewrite
subtree-rooted strategies in terms of canonical child strategies. -/

/-- The continuation navigator at a terminal tree returns the unique `PUnit` element. -/
@[simp] theorem at_terminal (payoff : I → ℝ)
    (s : LocalBehavioralStrategy (.terminal (I := I) (E := E) payoff)) (h : List E) :
    LocalBehavioralStrategy.at (.terminal payoff) s h = PUnit.unit := rfl

/-- The continuation navigator at the empty history returns the strategy unchanged. -/
@[simp] theorem at_decision_nil (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child)) :
    LocalBehavioralStrategy.at (.decision mover Choice emit child) s [] = s := rfl

/-- Parallel of `toBehavioral_decision_cons_some_heq` for the continuation-strategy navigator. -/
theorem at_decision_cons_some_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (e : E) (c : Choice) (h : List E) (hdec : decodeEmit emit e = some c) :
    HEq
      (LocalBehavioralStrategy.at (.decision mover Choice emit child) s (e :: h))
      ((s.2 c).at (child c) h) := by
  rw [LocalBehavioralStrategy.at.eq_3]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans
    (Option.rec_apply_heq_some
      (C := fun x =>
        LocalBehavioralStrategy (match x with
          | some c => (child c).subtreeAt h
          | none => terminal fun _ => 0))
      (x := decodeEmit emit e) (c := c) (h := hdec)
      _ _)
  exact eqRec_function_apply_heq
    (D := fun x =>
      LocalBehavioralStrategy (match x with
        | some c => (child c).subtreeAt h
        | none => terminal fun _ => 0))
    (a := decodeEmit emit e) (b := some c)
    (fun _ => (s.2 c).at (child c) h) _ _

/-- Specialization of `at_decision_cons_some_heq` to an emitted event `emit c`. -/
@[simp] theorem at_decision_emit_cons_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (h : List E) :
    HEq
      (LocalBehavioralStrategy.at (.decision mover Choice emit child) s (emit c :: h))
      ((s.2 c).at (child c) h) :=
  at_decision_cons_some_heq mover Choice emit child s
    (emit c) c h (decodeEmit_emit emit c)

/-- When `decodeEmit emit e = none`, the subtree at `e :: rest` reduces to the absorbing terminal
node and `at` gives the unique PUnit element, independent of the strategy. -/
theorem at_decision_cons_none_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (e : E) (rest : List E) (hdec : decodeEmit emit e = none) :
    HEq
      (LocalBehavioralStrategy.at (.decision mover Choice emit child) s (e :: rest))
      (PUnit.unit : PUnit.{u + 1}) := by
  rw [LocalBehavioralStrategy.at.eq_3]
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans
    (Option.rec_apply_heq_none
      (C := fun x =>
        LocalBehavioralStrategy (match x with
          | some c => (child c).subtreeAt rest
          | none => terminal fun _ => 0))
      (x := decodeEmit emit e) (h := hdec)
      _ _)
  -- The result of the noneBranch at x = none is `PUnit.unit`, after eqRec transports.
  exact eqRec_function_apply_heq
    (D := fun x =>
      LocalBehavioralStrategy (match x with
        | some c => (child c).subtreeAt rest
        | none => terminal fun _ => 0))
    (a := decodeEmit emit e) (b := none)
    (fun (_ : decodeEmit emit e = none) =>
      show LocalBehavioralStrategy (terminal (fun _ : I => (0 : ℝ))) from PUnit.unit) _ _

/-- `subtreeAt` is associative with respect to history concatenation. -/
theorem subtreeAt_append :
    ∀ (T : FinitePerfectInfoTree I E) (h₁ h₂ : List E),
      T.subtreeAt (h₁ ++ h₂) = (T.subtreeAt h₁).subtreeAt h₂ := by
  intro T h₁
  induction h₁ generalizing T with
  | nil =>
      intro h₂
      cases T with
      | terminal payoff => rfl
      | decision _ _ _ _ => rfl
  | cons e rest ih =>
      intro h₂
      cases T with
      | terminal payoff => rfl
      | decision mover Choice emit child =>
          change (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
              (e :: (rest ++ h₂)) =
            ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                (e :: rest)).subtreeAt h₂
          conv_lhs => unfold subtreeAt
          conv_rhs => arg 1; unfold subtreeAt
          cases hdec : decodeEmit emit e with
          | some c => exact ih (child c) h₂
          | none => rfl

/-- Stepping past an emitted public event commutes with subtree navigation. -/
theorem subtreeAt_emit_cons
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (c : Choice) (h : List E) :
    (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt (emit c :: h) =
      (child c).subtreeAt h := by
  conv_lhs => unfold subtreeAt
  rw [decodeEmit_emit emit c]

/-- Shift a behavioral strategy on a `decision`-rooted tree into the subtree under choice `c`. -/
def shiftBehavioralAtChoice
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral)
    (c : Choice) :
    (child c).RawBehavioral :=
  fun h => by
    have hType :
        ((FinitePerfectInfoTree.decision mover Choice emit
            child).subtreeAt (emit c :: h)).rootNodeKind.Behavior =
          ((child c).subtreeAt h).rootNodeKind.Behavior := by
      rw [subtreeAt_emit_cons mover Choice emit child c h]
    exact cast hType (σ (emit c :: h))

/-- Shifting an embedded strategy `toBehavioral s` past an emitted event recovers the embedded
child strategy. -/
theorem shiftBehavioralAtChoice_toBehavioral
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) :
    shiftBehavioralAtChoice mover Choice emit child
      (LocalBehavioralStrategy.toBehavioral _ s) c =
      LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) := by
  funext h
  unfold shiftBehavioralAtChoice
  apply eq_of_heq
  rw [cast_heq_iff_heq]
  exact toBehavioral_decision_emit_cons_heq mover Choice emit child s c h

end FinitePerfectInfoTree

end Econlib.GameTheory
