/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import Mathlib

/-!
# Extensive-Form Core — Non-Vacuity Checks (Chunks 1 & 5)

Compile-time
semantic
witnesses
for
the
history-based
core
of
the
extensive-form
API
(
`Econlib.GameTheory.ExtensiveForm.{Node, Reachable, Game, Tree, Strategy, PureStrategy,
BeliefSystem}`
). The structural invariants of an extensive form — node-step probabilities, reachability of
histories, node-step values, and belief support — are stated unconditionally in the library and
never exercised on a concrete tree, so a silently vacuous reachability predicate, a player-index
swap in the node-step value, or an off/on-path belief-support swap would pass the abstract API
unnoticed.

We anchor every witness on **one** small concrete carrier, the two-stage two-action
perfect-information tree `coreTree : FinitePerfectInfoTree (Fin 2) (Fin 2)`, reusing the
`FinitePerfectInfoTree` wrapper (which auto-generates the `GameTree`, `ExtensiveForm`, and
`ExtensiveGame` layers) rather than hand-rolling a raw `ExtensiveForm`.

## The game

`coreTree` is the tree

```
              root  (player 0 moves, history [])
             /    \
          a=0      a=1
          /          \
   node A             terminal (5, 6)          history [1]
 (player 1, [0])
    /     \
  b=0      b=1
  /          \
(1,2)        (3,4)
history       history
[0,0]         [0,1]
```

Every node-local choice type is `Fin 2`; the public event alphabet is `E = Fin 2`; the two players
are `I = Fin 2`. Each `decision` node emits its `Fin 2` choice through the identity embedding
`Function.Embedding.refl (Fin 2)`, so `decodeEmit emit e = some e` and a history step *is* its
emitted event.

**Reachable histories (proved here).** The inductive `IsReachable` witnesses below exhibit `[]`
(`coreTree_isReachable_nil`), the decision history `[0]` (`coreTree_isReachable_zero`), and the
terminal history `[0,1]` (`coreTree_isReachable_zero_one`) as reachable; the history `[0,0,0]` —
one step *past* the terminal `[0,0]` — is proved **not** reachable
(`coreTree_not_isReachable_zero_zero_zero`). We do *not* attach root reach-*probabilities* to
`coreTree` here: `reachProb`/`finitePrefixProb` under a concrete strategy is exercised on the
sibling file `ExtensiveFormSPE.lean` (on `centipede4`), not on this carrier. The
`finitePrefixProbFrom_nil`/`_cons` *structural* factorizations are checked below under `σbi`, but
no numeric reach-probability value is claimed for `coreTree`.

**Hand-computed terminal payoffs:** terminal `[0,0]` pays `(1, 2)` — player 0 gets `1`, player 1
gets `2`; terminal `[0,1]` pays `(3, 4)`; terminal `[1]` pays `(5, 6)`. These distinct first/second
coordinates anchor the player-index direction checks (`nodeStepValue_terminal`): A player-index
swap would read player 1's payoff at player 0's slot.

**Terminal reachability lives on `oneShotFEF`, not `coreTree`.** The `terminalReach` finset is a
`FiniteExtensiveForm` notion (it needs a finite `reach` enumeration and finite observation types).
`coreTree.toExtensiveForm` has infinite observations (`Obs i = List E`), so it cannot host
`terminalReach`. The `mem_terminalReach_iff` witnesses are therefore proved on the hand-rolled
finite carrier `oneShotFEF` further down: The terminal history `[0]` is *in* `oneShotFEF`'s
`terminalReach` (`oneShotFEF_zero_mem_terminalReach`) while the decision root `[]` is *excluded*
(`oneShotFEF_nil_not_mem_terminalReach`).

## Failure modes caught

* **vacuous reachability** — `coreTree_isReachable_nil`/`isReachable_nil` hold at the root, the
  decision/terminal histories `[0]` and `[0,1]` are exhibited as reachable, and `[0,0,0]` is proved
  *un*reachable (`coreTree_not_isReachable_zero_zero_zero`); on the finite carrier `oneShotFEF`,
  `mem_terminalReach_iff` includes the terminal `[0]` and excludes the decision root `[]`;
* **player-index swap in the node-step value** — `nodeStepValue_terminal` at `[0,0]` returns `1`
  for player 0 and `2` for player 1 (not the reverse); `nodeStepValue_player` at the root is
  exercised on the player branch (a weight-normalization check, see its docstring);
* **off/on-path belief-support swap** — `trivialBeliefs_prob_self` puts mass `1` on the reached
  history `[0]` of player 1's information set, while `trivialBeliefs_prob_zero_of_ne` gives `0` at
  the off-info-set history `[0,1]` — a support swap would invert these.
-/

noncomputable section

namespace EconlibTest.GameTheory.ExtensiveFormCore

open Econlib.GameTheory

/-! ## The concrete carrier `coreTree` -/

/-- The right-branch leaf `terminal (5, 6)`, reached by the history `[1]`. -/
def leafB : FinitePerfectInfoTree (Fin 2) (Fin 2) := .terminal ![5, 6]

/-- Player 1's decision node `A`, reached by the history `[0]`: Player `1` chooses between the
terminal `(1, 2)` (choice `0`, history `[0,0]`) and `(3, 4)` (choice `1`, history `[0,1]`). -/
def nodeA : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 1 (Fin 2) (Function.Embedding.refl _) ![.terminal ![1, 2], .terminal ![3, 4]]

/-- The two-stage two-action perfect-information tree. Player `0` at the root chooses between
entering `nodeA` (choice `0`) and the terminal `(5, 6)` (choice `1`). -/
def coreTree : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 0 (Fin 2) (Function.Embedding.refl _) ![nodeA, leafB]

/-! ## Node kinds along the reachable histories

The identity embedding makes `decodeEmit (Function.Embedding.refl _) e = some e`, so
`subtreeAt` follows the history literally. We pin the node kind at each reachable history; these
feed the `nodeStepValue`, `stepProb`, and `emits` witnesses below. -/

/-- The root player node, reached by `[]`. -/
def rootPlayerNode : PlayerNode (Fin 2) (Fin 2) :=
  { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }

/-- Player 1's player node, reached by `[0]`. -/
def nodeAPlayerNode : PlayerNode (Fin 2) (Fin 2) :=
  { mover := 1, Choice := Fin 2, emit := Function.Embedding.refl _ }

/-- The subtree reached after history `h` determines the node kind: `nodeKindAt h` is the root node
kind of `subtreeAt h`. A single `change`-free helper for the terminal histories, whose `subtreeAt`
requires the `decodeEmit`-reducing `subtreeAt_emit_cons` rather than `rfl`. -/
private theorem nodeKind_eq_of_subtree {h : List (Fin 2)}
    {T : FinitePerfectInfoTree (Fin 2) (Fin 2)} (hsub : coreTree.subtreeAt h = T) :
    coreTree.toGameTree.nodeKind h = T.rootNodeKind := by
  change coreTree.nodeKindAt h = T.rootNodeKind
  unfold FinitePerfectInfoTree.nodeKindAt
  rw [hsub]

/-- **Root node kind.** History `[]` is player 0's decision node. -/
@[simp] theorem nodeKind_nil :
    coreTree.toGameTree.nodeKind [] = .player rootPlayerNode := rfl

/-- **Node `A` kind.** History `[0]` is player 1's decision node. The root choice `0` emits the
event `0` through the identity embedding, so the subtree at `[0]` is `nodeA`. -/
@[simp] theorem nodeKind_zero :
    coreTree.toGameTree.nodeKind [0] = .player nodeAPlayerNode := by
  refine nodeKind_eq_of_subtree (T := nodeA) ?_
  change (FinitePerfectInfoTree.decision 0 (Fin 2) (Function.Embedding.refl _)
    ![nodeA, leafB]).subtreeAt ((Function.Embedding.refl (Fin 2)) 0 :: []) = nodeA
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  rfl

/-- **Right leaf kind.** History `[1]` is the terminal `(5, 6)`. -/
@[simp] theorem nodeKind_one :
    coreTree.toGameTree.nodeKind [1] = .terminal ![5, 6] := by
  refine nodeKind_eq_of_subtree (T := leafB) ?_
  change (FinitePerfectInfoTree.decision 0 (Fin 2) (Function.Embedding.refl _)
    ![nodeA, leafB]).subtreeAt ((Function.Embedding.refl (Fin 2)) 1 :: []) = leafB
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  rfl

/-- **Left-left leaf kind.** History `[0, 0]` is the terminal `(1, 2)`. -/
@[simp] theorem nodeKind_zero_zero :
    coreTree.toGameTree.nodeKind [0, 0] = .terminal ![1, 2] := by
  refine nodeKind_eq_of_subtree (T := .terminal ![1, 2]) ?_
  change (FinitePerfectInfoTree.decision 0 (Fin 2) (Function.Embedding.refl _)
    ![nodeA, leafB]).subtreeAt ((Function.Embedding.refl (Fin 2)) 0 ::
      (Function.Embedding.refl (Fin 2)) 0 :: []) = _
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  change (FinitePerfectInfoTree.decision 1 (Fin 2) (Function.Embedding.refl _)
    ![.terminal ![1, 2], .terminal ![3, 4]]).subtreeAt
      ((Function.Embedding.refl (Fin 2)) 0 :: []) = _
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  rfl

/-- **Left-right leaf kind.** History `[0, 1]` is the terminal `(3, 4)`. -/
@[simp] theorem nodeKind_zero_one :
    coreTree.toGameTree.nodeKind [0, 1] = .terminal ![3, 4] := by
  refine nodeKind_eq_of_subtree (T := .terminal ![3, 4]) ?_
  change (FinitePerfectInfoTree.decision 0 (Fin 2) (Function.Embedding.refl _)
    ![nodeA, leafB]).subtreeAt ((Function.Embedding.refl (Fin 2)) 0 ::
      (Function.Embedding.refl (Fin 2)) 1 :: []) = _
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  change (FinitePerfectInfoTree.decision 1 (Fin 2) (Function.Embedding.refl _)
    ![.terminal ![1, 2], .terminal ![3, 4]]).subtreeAt
      ((Function.Embedding.refl (Fin 2)) 1 :: []) = _
  rw [FinitePerfectInfoTree.subtreeAt_emit_cons]
  rfl

/-! ## Chunk 1 — `emits`, decision vs. leaf (Reachable.lean) -/

/-- **`emits_player_iff` fires at a decision node.** The root node (player 0) emits the event `1`,
witnessed by the choice `1` under the identity embedding. So a *decision* node has emitted events —
the engine that makes its successor histories reachable. -/
theorem root_emits_one :
    (coreTree.toGameTree.nodeKind []).emits (1 : Fin 2) := by
  rw [nodeKind_nil, NodeKind.emits_player_iff]
  exact ⟨(show rootPlayerNode.Choice from (1 : Fin 2)), rfl⟩

/-- **`emits_player_iff`, the full characterization on a surjective-emit node.** At the root, the
emitted events are exactly the images of the choices under `emit`; concretely event `0` is emitted
by choice `0`. Because `emit = refl` here is *surjective* (every `Fin 2` event is in the image),
this iff cannot by itself rule out a node that emits events outside its choice image — see
`nonSurjEmitNode_not_emits_two` for the discriminating off-image witness on a non-surjective
emit. -/
theorem root_emits_zero_iff :
    (coreTree.toGameTree.nodeKind []).emits (0 : Fin 2) ↔
      ∃ c : rootPlayerNode.Choice, rootPlayerNode.emit c = 0 := by
  rw [nodeKind_nil]
  exact NodeKind.emits_player_iff rootPlayerNode 0

/-- The strictly-order-preserving embedding `Fin 2 ↪ Fin 3` (`0 ↦ 0`, `1 ↦ 1`); event `2` is *not*
in its image. This is the non-surjective emit that the identity-emit root cannot exercise. -/
def emit23 : Fin 2 ↪ Fin 3 := ⟨fun c => c.castLE (by decide), fun a b h => by
  simpa using h⟩

/-- A player node over the `Fin 3` event alphabet whose two choices emit only events `0` and `1`
through `emit23`. Event `2` is unreachable from this node. -/
def nonSurjEmitNode : PlayerNode (Fin 3) (Fin 3) :=
  { mover := 0, Choice := Fin 2, emit := emit23 }

/-- **`emits_player_iff`, the *negative* off-image witness.** The non-surjective-emit node
`nonSurjEmitNode` does **not** emit event `2`: No `Fin 2` choice maps to `2` under `emit23`
(`emit23 0 = 0`, `emit23 1 = 1`). A bug that declared "every event is emitted" — invisible on the
surjective identity-emit root — is caught here. -/
theorem nonSurjEmitNode_not_emits_two :
    ¬ (NodeKind.player nonSurjEmitNode : NodeKind (Fin 3) (Fin 3)).emits (2 : Fin 3) := by
  rw [NodeKind.emits_player_iff]
  rintro ⟨c, hc⟩
  -- `emit23 c ∈ {0, 1}` for every `c : Fin 2`, never `2`.
  fin_cases c <;> simp [nonSurjEmitNode, emit23] at hc

/-- **`not_emits_terminal` at a leaf.** The terminal history `[0, 0]` (payoffs `(1, 2)`) emits *no*
event: Its node kind is `.terminal`, which has no successors. A leaf is genuinely a dead end. -/
theorem leaf_zero_zero_not_emits (e : Fin 2) :
    ¬ (coreTree.toGameTree.nodeKind [0, 0]).emits e := by
  rw [nodeKind_zero_zero]
  exact NodeKind.not_emits_terminal _ e

/-- **Negative reachability past a terminal.** The history `[0, 0, 0]` — one step beyond the
terminal `[0, 0]` — is **not** reachable. Inverting the inductive `IsReachable`, any reach of a
length-3 history must be a `step` from `[0, 0]` emitting `0`; but `[0, 0]` is a terminal node and
emits nothing (`leaf_zero_zero_not_emits`). This is the genuine "no history extends the leaf"
witness: It rules reachability out, where `leaf_zero_zero_not_emits` only ruled out emission. -/
theorem coreTree_not_isReachable_zero_zero_zero :
    ¬ coreTree.toExtensiveForm.IsReachable [0, 0, 0] := by
  -- Generalize the history to a variable so the inductive's `step` index `h ++ [e]` can unify.
  suffices h : ∀ l : List (Fin 2), coreTree.toExtensiveForm.IsReachable l → l ≠ [0, 0, 0] from
    fun hreach => h _ hreach rfl
  intro l hreach
  cases hreach with
  | root => simp
  | step h e hr he =>
    intro hl
    -- `h ++ [e] = [0, 0, 0]` forces `h = [0, 0]` and `e = 0` by list-append injectivity.
    have happ : h ++ [e] = [0, 0] ++ [0] := by simpa using hl
    have hh : h = [0, 0] := List.append_inj_left' happ rfl
    have he0 : e = 0 := by have := List.append_inj_right' happ rfl; simpa using this
    subst hh; subst he0
    -- The predecessor `[0, 0]` is terminal, so it emits nothing — contradiction with `he`.
    have hnk : coreTree.toExtensiveForm.tree.nodeKind [0, 0] =
        coreTree.toGameTree.nodeKind [0, 0] := rfl
    rw [hnk] at he
    exact leaf_zero_zero_not_emits 0 he

/-! ## Chunk 1 — Reachability on the embedded extensive form (Reachable.lean)

`coreTree.toExtensiveForm = ofGameTreePerfectInfo coreTree.toGameTree` is a plain
`ExtensiveForm`, so the *inductive* `ExtensiveForm.IsReachable` predicate (and `isReachable_nil`)
applies directly. -/

/-- **`isReachable_nil`.** The empty root history `[]` is reachable — reachability is non-vacuous
at the root. -/
theorem coreTree_isReachable_nil : coreTree.toExtensiveForm.IsReachable [] :=
  coreTree.toExtensiveForm.isReachable_nil

/-- **A reachable decision history.** History `[0]` (player 1's node) is reachable: It extends the
reachable root by the event `0`, which the root decision node emits. -/
theorem coreTree_isReachable_zero : coreTree.toExtensiveForm.IsReachable [0] := by
  have hstep : coreTree.toExtensiveForm.IsReachable ([] ++ [0]) :=
    .step [] 0 coreTree.toExtensiveForm.isReachable_nil
      (by rw [show coreTree.toExtensiveForm.tree = coreTree.toGameTree from rfl];
          exact (root_emits_zero_iff).mpr ⟨(show rootPlayerNode.Choice from (0 : Fin 2)), rfl⟩)
  simpa using hstep

/-- **A reachable terminal history.** The terminal history `[0, 1]` (payoffs `(3, 4)`) is
reachable: It extends the reachable decision history `[0]` by player 1's choice `1`. -/
theorem coreTree_isReachable_zero_one : coreTree.toExtensiveForm.IsReachable [0, 1] := by
  have hzero_emits : (coreTree.toExtensiveForm.tree.nodeKind [0]).emits (1 : Fin 2) := by
    change (coreTree.toGameTree.nodeKind [0]).emits (1 : Fin 2)
    rw [nodeKind_zero, NodeKind.emits_player_iff]
    exact ⟨(show nodeAPlayerNode.Choice from (1 : Fin 2)), rfl⟩
  have hstep : coreTree.toExtensiveForm.IsReachable ([0] ++ [1]) :=
    .step [0] 1 coreTree_isReachable_zero hzero_emits
  simpa using hstep

/-! ## Chunk 1 — Node-local behavior and total mixedness (Node.lean)

We work with the root player node `rootPlayerNode` (mover 0, choices `Fin 2`). Its `Behavior`
is `stdSimplex ℝ (Fin 2)`; its `PureChoice` is `Fin 2`. -/

/-- The uniform mixed behavior `(1/2, 1/2)` at a binary player node. Totally mixed: Both choices
get positive probability. -/
def uniformBehavior : (NodeKind.player rootPlayerNode).Behavior :=
  ⟨fun _ => 1 / 2, by
    refine ⟨fun _ => by norm_num, ?_⟩
    change (∑ _i : Fin 2, (1 : ℝ) / 2) = 1
    rw [Fin.sum_univ_two]; norm_num⟩

/-- The **asymmetric** mixed behavior `(1/3, 2/3)` at the binary root node: Choice `0` gets mass
`1/3`, choice `1` gets mass `2/3`. The asymmetry is what lets `eventProb` discriminate between the
two events — under the symmetric `uniformBehavior` an event-label swap is invisible. -/
def asymBehavior : (NodeKind.player rootPlayerNode).Behavior :=
  ⟨(![1 / 3, 2 / 3] : Fin 2 → ℝ), by
    refine ⟨fun c => ?_, ?_⟩
    · fin_cases c <;> norm_num
    · change (∑ c : Fin 2, (![1 / 3, 2 / 3] : Fin 2 → ℝ) c) = 1
      rw [Fin.sum_univ_two]; norm_num⟩

/-- **`NodeKind.pureBehavior` embeds a pure choice as a node behavior.** The pure choice `1` at the
root node embeds to the vertex simplex `stdSimplex.vertex 1`. -/
theorem pureBehavior_root_one :
    (NodeKind.player rootPlayerNode).pureBehavior (show (NodeKind.player rootPlayerNode).PureChoice
      from (1 : Fin 2)) = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := rfl

/-- **A totally-mixed behavior IS totally mixed.** The uniform behavior `(1/2, 1/2)` puts positive
probability on every choice, so it satisfies `IsTotallyMixed`. -/
theorem uniformBehavior_isTotallyMixed :
    (NodeKind.player rootPlayerNode).IsTotallyMixed uniformBehavior := by
  intro c
  change (0 : ℝ) < 1 / 2
  norm_num

/-- **A pure behavior is NOT totally mixed** (negative witness). The vertex behavior
`stdSimplex.vertex 0` puts probability `0` on the choice `1`, so it fails `IsTotallyMixed` — the
off-vertex choice is starved. A test that read "totally mixed" as "is a valid distribution" would
wrongly accept this. -/
theorem pureBehavior_root_zero_not_totallyMixed :
    ¬ (NodeKind.player rootPlayerNode).IsTotallyMixed
      ((NodeKind.player rootPlayerNode).pureBehavior
        (show (NodeKind.player rootPlayerNode).PureChoice from (0 : Fin 2))) := by
  intro htm
  have hpos := htm (show rootPlayerNode.Choice from (1 : Fin 2))
  -- The mass at choice `1` of `vertex 0` is `0`, contradicting `0 < 0`.
  have hzero : ((stdSimplex.vertex (S := ℝ) (0 : Fin 2) : stdSimplex ℝ (Fin 2)) :
      Fin 2 → ℝ) 1 = 0 :=
    stdSimplex.vertex_apply_ne (show (0 : Fin 2) ≠ 1 by decide)
  rw [show ((NodeKind.player rootPlayerNode).pureBehavior
      (show (NodeKind.player rootPlayerNode).PureChoice from (0 : Fin 2))
      : stdSimplex ℝ rootPlayerNode.Choice).val (show rootPlayerNode.Choice from (1 : Fin 2)) =
    ((stdSimplex.vertex (S := ℝ) (0 : Fin 2) : stdSimplex ℝ (Fin 2)) : Fin 2 → ℝ) 1 from rfl,
    hzero] at hpos
  exact lt_irrefl _ hpos

/-- **`eventProb_nonneg`.** The probability that the uniform root behavior emits the event `1` is
nonnegative. -/
theorem eventProb_nonneg_root :
    0 ≤ (NodeKind.player rootPlayerNode).eventProb uniformBehavior (1 : Fin 2) :=
  NodeKind.eventProb_nonneg _ _ _

/-- **`eventProb_cast`, reflexive transport check.** Confirms `eventProb_cast` is *well-typed* and
discharges at the concrete root node. Note this is the **reflexive** instance: The kind equality is
`rootPlayerNode = rootPlayerNode` (`rfl`), so the cast is the identity transport and the equation
is a transport tautology — it checks that the lemma type-checks against the concrete node, not that
a nontrivial kind change preserves `eventProb`. -/
theorem eventProb_cast_root (e : Fin 2) :
    (NodeKind.player rootPlayerNode).eventProb uniformBehavior e =
      (NodeKind.player rootPlayerNode).eventProb
        (cast (congrArg NodeKind.Behavior (rfl : NodeKind.player rootPlayerNode =
          NodeKind.player rootPlayerNode)) uniformBehavior) e :=
  NodeKind.eventProb_cast rfl uniformBehavior e

/-- **The root behavior emits event `1` with probability `1/2`.** The identity-embedding root node
emits the choice `1` as event `1`; under the uniform behavior its mass is `1/2`. This pins the
`eventProb` *value*, not just its sign. (Symmetric — see `asymEventProb_root_*` for the
discriminating asymmetric anchors.) -/
theorem eventProb_root_one_eq_half :
    (NodeKind.player rootPlayerNode).eventProb uniformBehavior (1 : Fin 2) = 1 / 2 := by
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = 1 then
    (uniformBehavior : stdSimplex ℝ (Fin 2)).val c else 0) = 1 / 2
  rw [Fin.sum_univ_two]
  -- `emit = refl`, so `emit 0 = 0 ≠ 1` (first term `0`) and `emit 1 = 1` (second term `1/2`).
  rw [if_neg (show (Function.Embedding.refl (Fin 2)) 0 ≠ 1 by decide),
    if_pos (show (Function.Embedding.refl (Fin 2)) 1 = 1 from rfl)]
  change (0 : ℝ) + 1 / 2 = 1 / 2
  norm_num

/-- **Asymmetric anchor, event `0`.** Under the asymmetric behavior `(1/3, 2/3)`, the root emits
event `0` with probability `1/3` — choice `0` (mass `1/3`) is the only choice whose identity emit
hits event `0`. A label swap of the two events would instead read `2/3` here, so this value
genuinely discriminates the event index (unlike the symmetric `1/2`). -/
theorem asymEventProb_root_zero_eq_third :
    (NodeKind.player rootPlayerNode).eventProb asymBehavior (0 : Fin 2) = 1 / 3 := by
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = 0 then
    (asymBehavior : stdSimplex ℝ (Fin 2)).val c else 0) = 1 / 3
  rw [Fin.sum_univ_two]
  -- `emit 0 = 0` (first term is the mass `1/3` at choice `0`); `emit 1 = 1 ≠ 0` (second term `0`).
  rw [if_pos (show (Function.Embedding.refl (Fin 2)) 0 = 0 from rfl),
    if_neg (show (Function.Embedding.refl (Fin 2)) 1 ≠ 0 by decide)]
  -- The mass at choice `0` is the first vector entry `1/3`.
  change (![1 / 3, 2 / 3] : Fin 2 → ℝ) 0 + 0 = 1 / 3
  norm_num

/-- **Asymmetric anchor, event `1`.** Under the same asymmetric behavior `(1/3, 2/3)`, the root
emits event `1` with probability `2/3` — choice `1` (mass `2/3`). Together with
`asymEventProb_root_zero_eq_third` (value `1/3`) the two events receive *distinct* masses, so an
event-label swap in `eventProb` is caught. -/
theorem asymEventProb_root_one_eq_two_thirds :
    (NodeKind.player rootPlayerNode).eventProb asymBehavior (1 : Fin 2) = 2 / 3 := by
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = 1 then
    (asymBehavior : stdSimplex ℝ (Fin 2)).val c else 0) = 2 / 3
  rw [Fin.sum_univ_two]
  -- `emit 0 = 0 ≠ 1` (first term `0`); `emit 1 = 1` (second term is the mass `2/3` at choice `1`).
  rw [if_neg (show (Function.Embedding.refl (Fin 2)) 0 ≠ 1 by decide),
    if_pos (show (Function.Embedding.refl (Fin 2)) 1 = 1 from rfl)]
  -- The mass at choice `1` is the second vector entry `2/3`.
  change (0 : ℝ) + (![1 / 3, 2 / 3] : Fin 2 → ℝ) 1 = 2 / 3
  norm_num

/-! ## Chunk 1 — `iChoiceTypeAt` instances and `ChanceGeneralNode` constructors (Node.lean) -/

/-- The root node's `movesAt 0` proof — player 0 moves at the root. -/
theorem root_movesAt_zero : (NodeKind.player rootPlayerNode).movesAt 0 := rfl

/-- **The `iChoiceTypeAt` `Fintype` instance is available** at the root node for the mover. The
choice type is `Fin 2`, finite. -/
example : Fintype ((NodeKind.player rootPlayerNode).iChoiceTypeAt 0 root_movesAt_zero) :=
  inferInstance

/-- **The `iChoiceTypeAt` `DecidableEq` instance is available** at the root node for the mover. -/
example : DecidableEq ((NodeKind.player rootPlayerNode).iChoiceTypeAt 0 root_movesAt_zero) :=
  inferInstance

/-- **The `iChoiceTypeAt` `Inhabited` instance is available** at the root node for the mover. -/
example : Inhabited ((NodeKind.player rootPlayerNode).iChoiceTypeAt 0 root_movesAt_zero) :=
  inferInstance

/-- A deterministic general-chance node emitting the fixed event `0`. -/
def diracNode : ChanceGeneralNode (Fin 2) := ChanceGeneralNode.dirac (0 : Fin 2)

/-- **`ChanceGeneralNode.dirac` is non-vacuous.** Its `dirac (0)` node emits the event `0` with
probability one: The singleton preimage `emit ⁻¹' {0}` is all of `PUnit`. -/
theorem diracNode_eventProb_zero :
    NodeKind.eventProb (I := Fin 2) (.chanceGeneral diracNode) PUnit.unit (0 : Fin 2) = 1 := by
  change ((diracNode.dist (diracNode.emit ⁻¹' {(0 : Fin 2)}) : NNReal) : ℝ) = 1
  have hpre : diracNode.emit ⁻¹' {(0 : Fin 2)} = Set.univ := by
    ext x; simp [diracNode, ChanceGeneralNode.dirac]
  rw [hpre]
  change ((diracNode.dist Set.univ : NNReal) : ℝ) = 1
  rw [MeasureTheory.ProbabilityMeasure.coeFn_univ]
  norm_num

/-- **`ChanceGeneralNode.ofMeasurable` is non-vacuous.** Building a general-chance node over
`Fin 2` outcomes from a measurable emitter yields a well-typed node — the convenience constructor
closes its singleton-measurability obligation automatically for the discrete `Fin 2` event type. -/
def ofMeasurableNode : ChanceGeneralNode (Fin 2) :=
  ChanceGeneralNode.ofMeasurable
    (Econlib.Probability.ProbDist.dirac (0 : Fin 2)) (id) measurable_id

/-- The `ofMeasurable` node carries the supplied emitter (`id`). -/
theorem ofMeasurableNode_emit : ofMeasurableNode.emit = id := rfl

/-! ## Chunk 1 — Node-step values and step probabilities (Game.lean)

We evaluate `nodeStepValue` and `stepProb` on `coreTree.toExtensiveForm` under a concrete
behavioral strategy. The headline semantic check: A player-index swap is caught by the *distinct*
first/second terminal coordinates. -/

/-- The extensive form embedded by `coreTree`. Abbreviation to shorten the witnesses. -/
abbrev G : ExtensiveForm (Fin 2) (Fin 2) := coreTree.toExtensiveForm

/-- The backward-induction behavioral strategy on `coreTree`, used as a concrete strategy
argument. -/
abbrev σbi : G.BehavioralStrategy := coreTree.backwardInductionBehavioralStrategy

/-- **Backward induction picks `leafB` (choice `1`) at the root of `coreTree`.** Player `0`
compares entering `nodeA` (choice `0`) against the terminal `(5, 6)` (choice `1`). Inside `nodeA`,
player `1` moves and prefers `(3, 4)` (own payoff `4`) to `(1, 2)` (own payoff `2`), so `nodeA`
delivers player `0` the continuation value `3`. The terminal `(5, 6)` delivers player `0` the value
`5 > 3`, so the root's best choice is `1`. -/
theorem coreTree_backwardInductionRootChoice_eq_one :
    coreTree.backwardInductionRootChoice = (1 : Fin 2) := by
  unfold coreTree FinitePerfectInfoTree.backwardInductionRootChoice
  -- `bestChoice` over the two root subtree values `(nodeA →ₚ₀ 3, leafB →ₚ₀ 5)`; choice `1` wins.
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 2) _ 1 ?_
  intro c hc
  fin_cases c
  -- Reduce the two vector lookups: child 0 = nodeA, child 1 = leafB.
  · change (![nodeA, leafB] 0).backwardInductionValue 0 <
      (![nodeA, leafB] 1).backwardInductionValue 0
    rw [show (![nodeA, leafB] 0 : FinitePerfectInfoTree (Fin 2) (Fin 2)) = nodeA from rfl,
      show (![nodeA, leafB] 1 : FinitePerfectInfoTree (Fin 2) (Fin 2)) = leafB from rfl]
    -- leafB = terminal (5, 6): value to player 0 is 5.
    rw [show leafB = .terminal ![5, 6] from rfl,
      FinitePerfectInfoTree.backwardInductionValue_terminal]
    -- nodeA: player 1 strictly prefers (3,4) (own payoff 4) over (1,2), choosing `1`.
    rw [show nodeA =
        .decision 1 (Fin 2) (Function.Embedding.refl _) ![.terminal ![1, 2], .terminal ![3, 4]]
        from rfl]
    rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax
        (mover := (1 : Fin 2)) (Choice := Fin 2) (emit := Function.Embedding.refl _)
        (child := ![.terminal ![1, 2], .terminal ![3, 4]]) (c := (1 : Fin 2))
        (i := (0 : Fin 2))
        (h := by
          -- player 1's payoff: `(1,2)` gives `2`, `(3,4)` gives `4`, so child 0 < child 1.
          bi_dominates)]
    -- child 1 of nodeA is the terminal `(3,4)`: value to player 0 is 3 < 5.
    rw [show (![.terminal ![1, 2], .terminal ![3, 4]] 1
          : FinitePerfectInfoTree (Fin 2) (Fin 2)) = .terminal ![3, 4] from rfl,
      FinitePerfectInfoTree.backwardInductionValue_terminal]
    change (![3, 4] : Fin 2 → ℝ) 0 < (![5, 6] : Fin 2 → ℝ) 0
    norm_num
  · exact absurd rfl hc

/-- **The backward-induction behavior at the root is the pure vertex on choice `1`.** Combining the
root-choice computation (`coreTree_backwardInductionRootChoice_eq_one`) with the
`ofPerfectInfo`/`toBehavioral` lift: Player `0`'s node-local behavior under `σbi` at the root puts
all mass on choice `1` (the leaf branch). All the choice types here are literally `Fin 2`, so the
`simplexTransport` bridges are identities up to `Fintype`-instance defeq. -/
theorem playerBehavior_root_eq_vertex_one :
    σbi.playerBehavior [] nodeKind_nil = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  -- `backwardInductionRaw []` is the root local decision behavior `vertex (rootChoice)`.
  have hraw : coreTree.backwardInductionRaw [] = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
    change coreTree.backwardInductionStrategy.1 = _
    rw [show coreTree.backwardInductionStrategy.1 =
          stdSimplex.vertex (S := ℝ) coreTree.backwardInductionRootChoice from rfl,
        coreTree_backwardInductionRootChoice_eq_one]
    rfl
  have hm : (coreTree.toGameTree.nodeKind []).movesAt (0 : Fin 2) := rfl
  -- `σbi 0 []` is `simplexTransport _ (backwardInductionRaw [])`, hence `HEq` to `vertex 1`.
  have hsigma_heq : HEq (σbi (0 : Fin 2) []) (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) := by
    have hunfold : σbi (0 : Fin 2) [] =
        simplexTransport
          ((NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ (0 : Fin 2) hm).symm)
          ((coreTree.toGameTree.nodeKind []).iLocalBehavior (0 : Fin 2) hm
            (coreTree.backwardInductionRaw [])) := by
      change coreTree.backwardInductionBehavioralStrategy (0 : Fin 2) [] = _
      unfold FinitePerfectInfoTree.backwardInductionBehavioralStrategy
      unfold ExtensiveForm.BehavioralStrategy.ofPerfectInfo
      rw [dif_pos hm]
      rfl
    rw [hunfold]
    -- `iLocalBehavior` at a player node is the identity; `simplexTransport _ s =HEq= s`.
    refine HEq.trans (simplexTransport_heq _ _) ?_
    -- `iLocalBehavior (.player rootPlayerNode) 0 hm (raw []) = raw [] = vertex 1`.
    rw [show (coreTree.toGameTree.nodeKind []).iLocalBehavior (0 : Fin 2) hm
        (coreTree.backwardInductionRaw []) = coreTree.backwardInductionRaw [] from rfl, hraw]
    -- Remaining `vertex 1 ≍ vertex 1` (both at `stdSimplex ℝ (Fin 2)` defeq).
    rfl
  -- `playerBehavior = cast _ (atHistory [])`; chain the HEqs and collapse to equality.
  have hheq : HEq (σbi.atHistory []) (σbi (0 : Fin 2) []) :=
    σbi.atHistory_player_heq nodeKind_nil
  change cast (congrArg NodeKind.Behavior nodeKind_nil) (σbi.atHistory []) = _
  exact eq_of_heq ((cast_heq _ _).trans (hheq.trans hsigma_heq))

/-- **`nodeStepValue_terminal`, the player-index direction anchor.** At the terminal history
`[0, 0]` (payoffs `(1, 2)`), the node-step value for player `0` is `1` and for player `1` is `2` —
the intended coordinates, not the reverse. A player-index swap in the terminal lookup would read
`2` at player `0`'s slot. -/
theorem nodeStepValue_terminal_zero_zero_player0 :
    nodeStepValue G σbi [0, 0] 0 (.terminal ![1, 2]) nodeKind_zero_zero (by simp)
      (fun _ _ _ => 0) 1 (fun _ _ _ => 0) = 1 := by
  rw [nodeStepValue_terminal]; rfl

/-- The player-index anchor's *other* coordinate: Player `1` collects `2` at the same terminal. -/
theorem nodeStepValue_terminal_zero_zero_player1 :
    nodeStepValue G σbi [0, 0] 1 (.terminal ![1, 2]) nodeKind_zero_zero (by simp)
      (fun _ _ _ => 0) 1 (fun _ _ _ => 0) = 2 := by
  rw [nodeStepValue_terminal]; rfl

/-- **`nodeStepValue_player`, weight-normalization check.** At the root (player 0's node), the
node-step value unfolds to the expected `stepPayoff + discount · V` over the root simplex. With the
*constant* continuation evaluator `fun _ _ _ => 7`, `stepPayoff := 0`, `discount := 1`, the value
is `∑ c, weight(c) · 7 = 7` because the root simplex weights sum to one. NOTE: With a constant `V`
this checks only that the player branch reduces and the weights normalize — it cannot see *which*
child is selected. The discriminating, child-keyed version is
`nodeStepValue_player_root_selects_leaf`. -/
theorem nodeStepValue_player_root :
    nodeStepValue G σbi [] 0 (.player rootPlayerNode) nodeKind_nil (by simp)
      (fun _ _ _ => 0) 1 (fun _ _ _ => 7) = 7 := by
  rw [nodeStepValue_player]
  -- Each summand is `weight(c) · (0 + 1 · 7) = weight(c) · 7`; the simplex weights sum to one.
  simp only [zero_add, one_mul, ← Finset.sum_mul]
  rw [(σbi.playerBehavior [] nodeKind_nil).2.2, one_mul]

/-- **`nodeStepValue_player`, the child-selection anchor.** With a continuation evaluator `V` keyed
by the *child history* (`V σ h i := 5` exactly at `h = [1]`, else `0`), `stepPayoff := 0`,
`discount := 1`, the root node-step value under the backward-induction strategy is `5`: Player `0`
places mass `1` on choice `1` (`playerBehavior_root_eq_vertex_one`), whose emitted event `1` leads
to the child history `[1]` where `V = 5`. This *discriminates* the selected child — a strategy that
instead favored choice `0` (child history `[0]`, where `V = 0`) would read `0`, not `5`. Hand
computation: `∑ c, (vertex 1).val c · V σ ([]++[emit c]) 0 = 1 · V σ [1] 0 = 5`. -/
theorem nodeStepValue_player_root_selects_leaf :
    nodeStepValue G σbi [] 0 (.player rootPlayerNode) nodeKind_nil (by simp)
      (fun _ _ _ => 0) 1 (fun _ h _ => if h = [1] then 5 else 0) = 5 := by
  rw [nodeStepValue_player]
  -- Reduce the per-choice weights to the vertex `1`, then evaluate the surviving `c = 1` summand.
  rw [show σbi.playerBehavior [] nodeKind_nil = stdSimplex.vertex (S := ℝ) (1 : Fin 2) from
    playerBehavior_root_eq_vertex_one]
  change (∑ c : Fin 2, (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val c *
    (0 + 1 * (if [] ++ [(Function.Embedding.refl (Fin 2)) c] = [1] then (5 : ℝ) else 0))) = 5
  rw [Fin.sum_univ_two]
  -- choice 0: weight `0`; choice 1: weight `1`, child history `[1]`, `V = 5`.
  rw [show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val (0 : Fin 2)) =
      (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 0 from rfl,
    show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val (1 : Fin 2)) =
      (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 from rfl,
    stdSimplex.vertex_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    stdSimplex.vertex_apply_self]
  -- `emit 1 = 1`, so the child history is `[] ++ [1] = [1]` and the `if` fires.
  rw [if_pos (show ([] : List (Fin 2)) ++ [(Function.Embedding.refl (Fin 2)) 1] = [1] from rfl)]
  norm_num

/-- **`nodeStepValue_chanceFinite`, a generic restatement check.** Reduction at a finite chance
node: The value is the chance-weighted expectation over outcomes. NOTE: `coreTree` has *no* chance
nodes, so there is no concrete carrier to instantiate this on; the statement is therefore fully
generic in `(Gc, σ, n, sp, disk, V)` and merely re-exports the library lemma
`nodeStepValue_chanceFinite` — it checks that the chance branch reduces to a `dist`-weighted sum
and that the restated shape type-checks, *not* a numeric value on a concrete chance game. -/
theorem nodeStepValue_chanceFinite_reduces
    (Gc : ExtensiveForm (Fin 2) (Fin 2)) (σ : Gc.BehavioralStrategy)
    (h : List (Fin 2)) (i : Fin 2)
    (n : ChanceFiniteNode (Fin 2)) (hnk : Gc.tree.nodeKind h = .chanceFinite n)
    (sp : List (Fin 2) → Fin 2 → Fin 2 → ℝ) (disc : ℝ)
    (V : Gc.BehavioralStrategy → List (Fin 2) → Fin 2 → ℝ) :
    nodeStepValue Gc σ h i (.chanceFinite n) hnk (by simp) sp disc V =
      ∑ ω : n.Outcome, n.dist ω * (sp h (n.emit ω) i + disc * V σ (h ++ [n.emit ω]) i) :=
  nodeStepValue_chanceFinite Gc σ h i n hnk (by simp) sp disc V

/-- **`nodeStepValue_joint`, a generic restatement check.** Reduction at a joint node: The value is
the product-simplex-weighted sum over joint choice profiles. NOTE: `coreTree` has *no* joint nodes
(indeed the whole finite-extensive-form layer excludes them via `no_joint`), so this cannot be
instantiated on a concrete carrier; the statement is fully generic in `(Gc, σ, n, sp, disk, V)` and
re-exports the library lemma `nodeStepValue_joint`. It checks the joint branch reduces to a
product-weighted sum and that the restated shape type-checks, *not* a numeric value. -/
theorem nodeStepValue_joint_reduces
    (Gc : ExtensiveForm (Fin 2) (Fin 2)) (σ : Gc.BehavioralStrategy)
    (h : List (Fin 2)) (i : Fin 2)
    (n : JointNode (Fin 2) (Fin 2)) (hnk : Gc.tree.nodeKind h = .joint n)
    (sp : List (Fin 2) → Fin 2 → Fin 2 → ℝ) (disc : ℝ)
    (V : Gc.BehavioralStrategy → List (Fin 2) → Fin 2 → ℝ) :
    nodeStepValue Gc σ h i (.joint n) hnk (by simp) sp disc V =
      ∑ c : (a : n.Active) → n.Choice a,
        (∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a)) *
          (sp h (n.emit c) i + disc * V σ (h ++ [n.emit c]) i) :=
  nodeStepValue_joint Gc σ h i n hnk (by simp) sp disc V

/-- The uniform behavioral strategy on `G`: At every `(player, observation)` it puts mass `1/card`
on every legal choice. It is totally mixed, hence *not* the pure backward-induction `σbi`. -/
def uniformG : G.BehavioralStrategy :=
  fun i obs =>
    ⟨fun _ => 1 / (Fintype.card (G.info.iChoiceType i obs) : ℝ), by
      refine ⟨fun c => by positivity, ?_⟩
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one_div, div_self]
      have : 0 < Fintype.card (G.info.iChoiceType i obs) := Fintype.card_pos
      positivity⟩

/-- A **second** strategy that *agrees with `σbi` at the root*: The one-shot surgery installing the
uniform action at player 1's info set `(1, [0])`, copying `σbi` at every other coordinate. -/
def σbiDeviated : G.BehavioralStrategy := oneShotSurgery G σbi uniformG 1 [0]

/-- **`σbiDeviated` is totally mixed at `(1, [0])`.** There the surgery copies `uniformG`, which
puts strictly positive mass `1/card > 0` on *every* legal choice. This is the substantive content
that makes `σbiDeviated` an extensional deviation from the *pure* backward-induction `σbi` (whose
node-local behavior is a vertex, with mass `0` off its chosen action) — so the congruence below is
a genuine locality check, not the reflexive `σbi = σbi` tautology. -/
theorem σbiDeviated_totallyMixed_at_one_zero (c : (G.info.iChoiceType (1 : Fin 2) [0])) :
    0 < (σbiDeviated (1 : Fin 2) [0]).val c := by
  -- At `(1, [0])` the surgery copies `uniformG`, whose mass at any choice is `1/card > 0`.
  rw [show σbiDeviated (1 : Fin 2) [0] = uniformG (1 : Fin 2) [0] from
    oneShotSurgery_at_self G σbi uniformG 1 [0]]
  change 0 < 1 / (Fintype.card (G.info.iChoiceType (1 : Fin 2) [0]) : ℝ)
  have : 0 < Fintype.card (G.info.iChoiceType (1 : Fin 2) [0]) := Fintype.card_pos
  positivity

/-- **`nodeStepValue_congr`, a genuine locality check.** Two strategies — the backward-induction
`σbi` and its deviation `σbiDeviated`, which copies the *totally-mixed* uniform action at
`(1, [0])` (`σbiDeviated_totallyMixed_at_one_zero`) where `σbi` is pure — that nevertheless agree
at the root coordinates `(j, [])` and induce equal (constant) child values produce equal node-step
values. The agreement hypotheses, not a reflexive `σbi = σbi`, drive the equality:
`nodeStepValue_congr` reads the strategies only at the root observation, where the surgery
coincides with `σbi` (it edits only `(1, [0])`, and `[] ≠ [0]`). -/
theorem nodeStepValue_congr_root :
    nodeStepValue G σbi [] 0 (.player rootPlayerNode) nodeKind_nil (by simp) (fun _ _ _ => 0) 1
        (fun _ _ _ => 7) =
      nodeStepValue G σbiDeviated [] 0 (.player rootPlayerNode) nodeKind_nil (by simp)
        (fun _ _ _ => 0) 1 (fun _ _ _ => 7) :=
  nodeStepValue_congr G σbi σbiDeviated [] 0 (.player rootPlayerNode) nodeKind_nil (by simp)
    (fun _ _ _ => 0) 1 (fun _ _ _ => 7)
    (fun j => by
      -- At root coordinate `(j, observe j []) = (j, [])`: surgery copies `σbi` since `[] ≠ [0]`.
      change σbi j (G.info.observe j []) =
        oneShotSurgery G σbi uniformG 1 [0] j (G.info.observe j [])
      refine (oneShotSurgery_isInfoSetDeviation G σbi uniformG 1 [0] j
        (G.info.observe j []) ?_).symm
      -- `(j, observe j []) = (j, []) ≠ (1, [0])`: the observation `[]` differs from `[0]`.
      intro hsig
      -- `observe j [] = []` (perfect info), so the second components are `[]` vs `[0]`.
      have hfst : j = 1 := congrArg Sigma.fst hsig
      subst hfst
      -- Now `hsig : ⟨1, observe 1 []⟩ = ⟨1, [0]⟩`, i.e. `[] = [0]` on the second component.
      have hsnd : (G.info.observe (1 : Fin 2) [] : List (Fin 2)) = [0] :=
        eq_of_heq (Sigma.mk.injEq .. ▸ hsig).2
      -- `observe 1 [] = []` (perfect info), contradicting `[] = [0]`.
      rw [show G.info.observe (1 : Fin 2) [] = ([] : List (Fin 2)) from rfl] at hsnd
      exact List.cons_ne_nil (0 : Fin 2) [] hsnd.symm)
    (fun _ => rfl)

/-- A **non-injective** tag `Fin 3 → Fin 2`: Choice `0` tags event `0`; choices `1` and `2` *both*
tag event `1`. This collapses a genuine two-element fiber `{1, 2}` over event `1`, exercising the
fiber-regrouping past the trivial singleton-fiber (identity-tag) case. -/
def tagNI : Fin 3 → Fin 2 := fun c => if c = 0 then 0 else 1

/-- **`sum_choice_eq_sum_tag` on a non-injective tag.** Regrouping the per-choice sum
`∑ c, w c * F (g c)` by the emitted tag `g = tagNI` leaves the total unchanged — even though
choices `1` and `2` share the event-`1` fiber, whose masses must be *added* (`5 + 7 = 12`), not
double-counted or dropped. With the identity tag every fiber is a singleton, so this collapse is
invisible there; here it is the load-bearing check. -/
theorem sum_choice_eq_sum_tag_concrete :
    (∑ c : Fin 3, ![3, 5, 7] c * (fun e : Fin 2 => (e.val : ℝ)) (tagNI c)) =
      ∑ e ∈ Finset.univ.image tagNI,
        (∑ c : Fin 3, if tagNI c = e then ![3, 5, 7] c else 0) * (fun e : Fin 2 => (e.val : ℝ)) e :=
  ExtensiveForm.sum_choice_eq_sum_tag tagNI (fun c => ![3, 5, 7] c)
    (fun e : Fin 2 => (e.val : ℝ))

/-- **The non-injective regrouping evaluates to `12`.** Hand computation: The LHS is
`3·F(0) + 5·F(1) + 7·F(1) = 0 + 5 + 7 = 12`; the RHS collapses the `{1, 2}` fiber to mass
`5 + 7 = 12` over event `1` (value `F 1 = 1`) and the singleton `{0}` fiber to mass `3` over event
`0` (value `F 0 = 0`), giving `3·0 + 12·1 = 12`. Pins the *value* of the regrouped sum, so a fiber
that silently dropped one of the colliding choices would read `5` or `7`, not `12`. -/
theorem sum_choice_eq_sum_tag_concrete_value :
    (∑ c : Fin 3, ![3, 5, 7] c * (fun e : Fin 2 => (e.val : ℝ)) (tagNI c)) = 12 := by
  -- `tagNI 0 = 0`, `tagNI 1 = 1`, `tagNI 2 = 1`; `F 0 = 0`, `F 1 = 1`.
  simp only [Fin.sum_univ_three, tagNI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    if_neg (show (2 : Fin 3) ≠ 0 by decide), if_neg (show (1 : Fin 3) ≠ 0 by decide)]
  norm_num

/-- **`stepProb_player`.** The one-step probability at the root for event `e` is the simplex mass
of the choices emitting `e`. The concrete `σbi`-values are pinned in `stepProb_root_one_eq_one` /
`stepProb_root_zero_eq_zero` below. -/
theorem stepProb_player_root (e : Fin 2) :
    G.stepProb σbi [] e =
      ∑ c : rootPlayerNode.Choice,
        if rootPlayerNode.emit c = e then (σbi.playerBehavior [] nodeKind_nil).val c else 0 :=
  G.stepProb_player σbi nodeKind_nil e

/-- **`stepProb σbi [] 1 = 1`** (concrete value). Under backward induction player `0` enters the
leaf branch with certainty, so event `1` (the only event emitted by the root choice `1` under the
identity embedding) carries the full one-step reach mass `1`. -/
theorem stepProb_root_one_eq_one : G.stepProb σbi [] 1 = 1 := by
  rw [stepProb_player_root, playerBehavior_root_eq_vertex_one]
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = 1 then
    (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val c else 0) = 1
  rw [Fin.sum_univ_two]
  -- emit = refl: `emit 0 = 0 ≠ 1` (term 0), `emit 1 = 1` (term = vertex mass at 1 = 1).
  rw [if_neg (show (Function.Embedding.refl (Fin 2)) 0 ≠ 1 by decide),
    if_pos (show (Function.Embedding.refl (Fin 2)) 1 = 1 from rfl)]
  -- The mass of `vertex 1` at index `1` is `1`.
  rw [zero_add, show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val
    (1 : Fin 2)) = (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 from rfl,
    stdSimplex.vertex_apply_self]

/-- **`stepProb σbi [] 0 = 0`** (concrete value). Player `0` puts *zero* mass on entering `nodeA`
(choice `0`, event `0`), so event `0` carries no one-step reach mass. Together with
`stepProb_root_one_eq_one` this pins the deterministic backward-induction step: A strategy that
mistakenly favored the dominated branch would invert these `0`/`1` values. -/
theorem stepProb_root_zero_eq_zero : G.stepProb σbi [] 0 = 0 := by
  rw [stepProb_player_root, playerBehavior_root_eq_vertex_one]
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = 0 then
    (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val c else 0) = 0
  rw [Fin.sum_univ_two]
  -- emit = refl: `emit 0 = 0` (term = vertex mass at 0 = 0), `emit 1 = 1 ≠ 0` (term 0).
  rw [if_pos (show (Function.Embedding.refl (Fin 2)) 0 = 0 from rfl),
    if_neg (show (Function.Embedding.refl (Fin 2)) 1 ≠ 0 by decide)]
  -- The mass of `vertex 1` at index `0` is `0`.
  rw [add_zero, show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val
    (0 : Fin 2)) = (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 0 from rfl,
    stdSimplex.vertex_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]

/-- `coreTree` has no general-chance nodes. -/
theorem coreTree_no_chanceGeneral :
    ∀ h : List (Fin 2), ∀ n : ChanceGeneralNode (Fin 2),
      G.tree.nodeKind h ≠ .chanceGeneral n :=
  fun h n => coreTree.toExtensiveGame.no_chanceGeneral h n

/-- **`recursiveContinuationValue_eq` (Bellman) on the embedded game.** The recursive continuation
value satisfies the unified Bellman equation at every history. Instantiated at the root for
player 0 on the embedded finite-depth form. -/
theorem recursiveContinuationValue_eq_root :
    G.recursiveContinuationValue coreTree.finiteDepth coreTree_no_chanceGeneral σbi [] 0 =
      nodeStepValue G σbi [] 0 (G.tree.nodeKind []) rfl (coreTree_no_chanceGeneral [])
        (fun _ _ _ => 0) 1
        (G.recursiveContinuationValue coreTree.finiteDepth coreTree_no_chanceGeneral) :=
  ExtensiveGame.recursiveContinuationValue_eq G coreTree.finiteDepth
    coreTree_no_chanceGeneral σbi [] 0

/-! ### Regression (gt-general-chance): The no-general-chance guard bites

A form whose root *is* a general-chance node cannot satisfy the `hNG` hypothesis now demanded
by `recursiveContinuationValue`, so the placeholder-`0` evaluator can no longer be applied to it.
We build such a form and refute its guard. -/

/-- A one-node game tree whose root is the deterministic general-chance node `diracNode`. -/
def gcTree : GameTree (Fin 2) (Fin 2) where
  nodeKind _ := .chanceGeneral diracNode

/-- The perfect-information extensive form over `gcTree`: Its root is a general-chance node. -/
noncomputable def gcForm : ExtensiveForm (Fin 2) (Fin 2) :=
  ExtensiveForm.ofGameTreePerfectInfo gcTree

/-- **The no-general-chance guard is unsatisfiable for `gcForm`.** Since every node of `gcForm`
is a general-chance node, the guard `∀ h n, nodeKind h ≠ .chanceGeneral n` cannot be satisfied. -/
theorem gcForm_no_chanceGeneral_guard_unsatisfiable :
    ¬ (∀ h : List (Fin 2), ∀ n : ChanceGeneralNode (Fin 2),
        gcForm.tree.nodeKind h ≠ .chanceGeneral n) :=
  fun hNG => hNG [] diracNode rfl

/-- **`finitePrefixProbFrom_nil`.** The probability of the empty continuation suffix is `1`. -/
theorem finitePrefixProbFrom_nil_witness :
    G.finitePrefixProbFrom σbi [0] [] = 1 :=
  G.finitePrefixProbFrom_nil σbi [0]

/-- **`finitePrefixProbFrom_cons`.** The probability of a one-event continuation factors as the
step probability times the remaining-suffix probability. -/
theorem finitePrefixProbFrom_cons_witness (e : Fin 2) :
    G.finitePrefixProbFrom σbi [] (e :: []) =
      G.stepProb σbi [] e * G.finitePrefixProbFrom σbi ([] ++ [e]) [] :=
  G.finitePrefixProbFrom_cons σbi [] e []

/-- **`BehavioralStrategy.atHistory_player_heq`.** At the root player node, the behavioral
strategy's local behavior is heterogeneously equal to its `(mover, observation)` simplex — the
player branch of the `atHistory` kit, exercised on the concrete strategy. -/
theorem atHistory_player_heq_root :
    HEq (σbi.atHistory []) (σbi rootPlayerNode.mover (G.info.observe rootPlayerNode.mover [])) :=
  σbi.atHistory_player_heq nodeKind_nil

/-- **`BehavioralStrategy.atHistory_terminal_heq`.** At the terminal history `[1]`, the local
behavior is the trivial `PUnit.unit` — the terminal branch of the `atHistory` kit. -/
theorem atHistory_terminal_heq_one :
    HEq (σbi.atHistory [1]) (PUnit.unit : PUnit) :=
  σbi.atHistory_terminal_heq nodeKind_one

/-! ## Chunk 5 — Beliefs and consistency (BeliefSystem.lean)

The canonical perfect-information beliefs `trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree`
are a `BeliefSystem` over the perfect-info form. Player 1's information set is anchored at the
observation `[0]` (player 1's only decision node). Under perfect information `observe i h = h`, so
the info set at observation `[0]` contains exactly the history `[0]`; the belief support is the
singleton `{[0]}`. The semantic checks below catch an on/off-path belief-support swap. -/

/-- Player 1 moves at history `[0]` (node `A`). -/
theorem player1_movesAt_zero : (coreTree.toGameTree.nodeKind [0]).movesAt 1 := by
  rw [nodeKind_zero]; rfl

/-- **`trivialBeliefs_prob_self`: Mass on the reached node.** Player 1's belief at her information
set (observation `[0]`) puts probability `1` on the *reached* history `[0]` — the on-path support
point. -/
theorem trivialBeliefs_prob_self_zero :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] [0] = 1 :=
  trivialBeliefs_prob_self coreTree.toGameTree 1 [0] player1_movesAt_zero

/-- **`trivialBeliefs_prob_zero_of_ne`: Observation-mismatch zero.** The belief queried at
observation `[0]` puts probability `0` on the history `[0, 1]`. Under perfect information the lemma
fires precisely because the *observation* of `[0, 1]` is `[0, 1]` (`observe i h = h`), which does
**not** equal the queried observation `[0]` — so `[0, 1]` is *not a member* of player 1's info set
at observation `[0]` (it is moreover a terminal node where player 1 does not move). This is an
observation-mismatch / off-info-set check, not a "different history of the same info set" check:
The `trivialBeliefs` info set at `[0]` is the singleton `{[0]}`. Together with
`trivialBeliefs_prob_self_zero` (mass `1` on `[0]`) it catches a support placed on a non-member. -/
theorem trivialBeliefs_prob_zero_of_ne_zero_one :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] [0, 1] = 0 :=
  trivialBeliefs_prob_zero_of_ne coreTree.toGameTree 1 [0] [0, 1] (by decide)

/-- **`trivialBeliefs_prob_zero_of_not_movesAt`.** At a history where player 1 does *not* move —
the root `[]` (player 0's node) — the belief is `0`. Player 1 holds no beliefs at player 0's
decision node. -/
theorem trivialBeliefs_prob_zero_of_not_movesAt_nil :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] [] = 0 := by
  refine trivialBeliefs_prob_zero_of_not_movesAt coreTree.toGameTree 1 [0] [] ?_
  rw [nodeKind_nil]
  -- Player 1 is not the mover at the root (player 0 is).
  exact fun (h : (NodeKind.player rootPlayerNode).movesAt 1) => by
    simp only [NodeKind.movesAt, rootPlayerNode] at h; exact absurd h (by decide)

/-- The subtype element of player 1's information set at observation `[0]`: The reached history
`[0]` together with the moves-and-observation witness. -/
def infoSetElt : (ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree).InfoSet 1 [0] :=
  ⟨[0], player1_movesAt_zero, rfl⟩

/-- **The raw `belief` field is `1` at the support point** (numeric anchor). The `trivialBeliefs`
`belief` field is the constant `1`, so player 1's belief at the info-set element `[0]` evaluates to
`1`. This pins the *value* the `prob = belief` bridges below transport — without it, those bridges
only assert two unevaluated expressions are equal. -/
theorem belief_value_one :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).belief 1 [0] infoSetElt = 1 := rfl

/-- **`BeliefSystem.prob_of_mem` bridge.** The belief probability at a history *in* the info set
equals the raw `belief` field. Combined with `belief_value_one` (value `1`) this gives
`prob 1 [0] [0] = 1`; see `belief_prob_value_one` for the composed numeric statement. -/
theorem belief_prob_of_mem :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] infoSetElt.1 =
      (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).belief 1 [0] infoSetElt :=
  BeliefSystem.prob_of_mem (G := ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree)
    _ 1 ([0] : List (Fin 2)) infoSetElt.2

/-- **The belief probability at the support point is `1`** (composed numeric anchor). Chaining the
`prob = belief` bridge `belief_prob_of_mem` with `belief_value_one`: Player 1's belief probability
at the reached history `[0]` of her info set is exactly `1`, the full mass of the singleton
support. -/
theorem belief_prob_value_one :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] infoSetElt.1 = 1 := by
  rw [belief_prob_of_mem, belief_value_one]

/-- **`BeliefSystem.prob_of_not_mem`.** At a history *outside* the info set (the root `[]`, where
player 1 does not move), the belief probability is `0`. -/
theorem belief_prob_of_not_mem :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] [] = 0 := by
  refine BeliefSystem.prob_of_not_mem (G := ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree)
    _ 1 ([0] : List (Fin 2)) (h := ([] : List (Fin 2))) ?_
  rintro ⟨hmoves, -⟩
  have hmoves' : (coreTree.toGameTree.nodeKind []).movesAt 1 := hmoves
  rw [nodeKind_nil] at hmoves'
  simp only [NodeKind.movesAt, rootPlayerNode] at hmoves'
  exact absurd hmoves' (by decide)

/-- **`BeliefSystem.prob_nonneg`.** Belief probabilities are nonnegative. -/
theorem belief_prob_nonneg :
    0 ≤ (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] [0] :=
  BeliefSystem.prob_nonneg (G := ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree)
    _ 1 ([0] : List (Fin 2)) ([0] : List (Fin 2))

/-- **`BeliefSystem.prob_subtype` bridge.** A subtype info-set element's `prob` equals its `belief`
— the same equality as `belief_prob_of_mem`, but routed through the `prob_subtype` API entry rather
than `prob_of_mem`. Its numeric content (`= 1`) is recorded in `belief_prob_value_one`. -/
theorem belief_prob_subtype :
    (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] infoSetElt.1 =
      (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).belief 1 [0] infoSetElt :=
  BeliefSystem.prob_subtype (G := ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree)
    _ 1 ([0] : List (Fin 2)) infoSetElt

/-- **`BeliefSystem.sum_support_prob`.** The belief masses over the (nonempty singleton) support of
player 1's info set at observation `[0]` sum to `1` — the beliefs form a genuine distribution
there. -/
theorem belief_sum_support_prob :
    ∑ x ∈ (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).support 1 [0],
      (trivialBeliefs (Fin 2) (Fin 2) coreTree.toGameTree).prob 1 [0] x.1 = 1 := by
  classical
  refine BeliefSystem.sum_support_prob
      (G := ExtensiveForm.ofGameTreePerfectInfo coreTree.toGameTree)
      _ 1 ([0] : List (Fin 2)) ?_
  -- The support is the nonempty singleton `{⟨[0], _⟩}`.
  refine ⟨infoSetElt, ?_⟩
  change infoSetElt ∈ (if hm : (coreTree.toGameTree.nodeKind [0]).movesAt 1 then
    ({⟨[0], hm, rfl⟩} : Finset _) else ∅)
  rw [dif_pos player1_movesAt_zero, Finset.mem_singleton]
  exact Subtype.ext rfl

/-! ## Chunk 1 (Reachable / PureStrategy / StrategicForm) & Chunk 5 (FiniteExtensiveForm beliefs)

The lemmas `nil_mem_reach`, `mem_terminalReach_iff`, `canonicalRep_mem_reach`,
`iChoiceTypeAt_eq_canonicalRep`, the `PureStrategy`/`infoSetChoiceForObs` instances, and the
`purePrefixStep_of_*`/`lookupPlayerChoice_eq_of_obs_agree` reductions all live on
`FiniteExtensiveForm`, which carries a *finite* observation type — so the perfect-information
`coreTree.toExtensiveForm` (whose `Obs i = List E` is infinite) cannot host them. We therefore
build one hand-rolled `FiniteExtensiveForm`.

`oneShotFEF` is the one-decision game: Player `0` moves once at the root over `Fin 2`, then the
game terminates. Player `0` (mover) collects `1` after choice `0` and `2` after choice `1`; player
`1` (never moves) collects the mirror payoffs. Each player has a *single* information set, encoded
as `Obs i = Unit`. The reachable histories are exactly `[]`, `[0]`, `[1]`. This is the cheapest
carrier that exercises the `FiniteExtensiveForm` structural API non-vacuously; it is trivially
perfect-recall (player 0's lone info set is visited once on every path). -/

/-- The game tree of `oneShotFEF`: Player `0` decides over `Fin 2` at the root (emit = identity),
and every nonempty history is a terminal node. The terminal payoff after the single event `e` is
`![e + 1, 2 - e]` (so event `0` pays `(1, 2)`, event `1` pays `(2, 1)`). -/
def oneShotTree : GameTree (Fin 2) (Fin 2) where
  nodeKind h :=
    match h with
    | [] => .player { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }
    | e :: _ => .terminal ![(e.val : ℝ) + 1, 2 - (e.val : ℝ)]

/-- The root player node of `oneShotTree`. -/
def oneShotRootNode : PlayerNode (Fin 2) (Fin 2) :=
  { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }

/-- **Root node kind of `oneShotTree`.** -/
@[simp] theorem oneShotTree_nodeKind_nil :
    oneShotTree.nodeKind [] = .player oneShotRootNode := rfl

/-- **Terminal node kind of `oneShotTree` after one event.** -/
@[simp] theorem oneShotTree_nodeKind_cons (e : Fin 2) (rest : List (Fin 2)) :
    oneShotTree.nodeKind (e :: rest) = .terminal ![(e.val : ℝ) + 1, 2 - (e.val : ℝ)] := rfl

/-- Player `0` moves at the root of `oneShotTree`; nowhere else (every nonempty history is
terminal). -/
theorem oneShotTree_movesAt_iff (i : Fin 2) (h : List (Fin 2)) :
    (oneShotTree.nodeKind h).movesAt i ↔ (h = [] ∧ i = 0) := by
  cases h with
  | nil =>
    rw [oneShotTree_nodeKind_nil]
    constructor
    · intro hm; exact ⟨rfl, hm.symm⟩
    · rintro ⟨-, rfl⟩; rfl
  | cons e rest =>
    rw [oneShotTree_nodeKind_cons]
    simp only [NodeKind.movesAt, reduceCtorEq, false_and]

/-- The finite information structure for `oneShotFEF`: Each player has a single information set
(`Obs i = Unit`). Player `0`'s only info set carries the choice type `Fin 2` (its root choices);
player `1` (who never moves) carries the degenerate `Unit` choice type. -/
def oneShotInfo : InfoStructure (Fin 2) (Fin 2) where
  Obs _ := Unit
  observe _ _ := ()
  iChoiceType i _ := if i = 0 then Fin 2 else Unit
  iChoiceFintype i _ := by split <;> infer_instance
  iChoiceDecEq i _ := by split <;> infer_instance
  iChoiceInhabited i _ := by split <;> infer_instance

/-- The extensive form of `oneShotFEF`. The only history where a player moves is the root `[]`
(player 0), where `iChoiceTypeAt 0 = Fin 2 = iChoiceType 0 ()`, so `iChoice_compatible` holds. -/
def oneShotEF : ExtensiveForm (Fin 2) (Fin 2) where
  tree := oneShotTree
  info := oneShotInfo
  iChoice_compatible := by
    intro i h hm
    rw [oneShotTree_movesAt_iff] at hm
    obtain ⟨rfl, rfl⟩ := hm
    -- At `(0, [])`: `iChoiceTypeAt 0 _` reduces to `Fin 2` (the player node's choice type), and
    -- `iChoiceType 0 () = (if 0 = 0 then Fin 2 else Unit) = Fin 2`, both by `rfl`.
    rfl

/-- The complete `FiniteExtensiveForm` of the one-decision game. -/
def oneShotFEF : FiniteExtensiveForm (Fin 2) (Fin 2) where
  toExtensiveForm := oneShotEF
  reach := {[], [0], [1]}
  mem_reach_iff := by
    intro h
    constructor
    · -- membership in the explicit finset ⇒ reachable, by enumerating the three histories.
      intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact .root
      · -- `[0] = [] ++ [0]`, emitted by the root player node.
        have hstep : oneShotEF.IsReachable ([] ++ [0]) :=
          .step [] 0 .root (by
            change (oneShotTree.nodeKind []).emits (0 : Fin 2)
            rw [oneShotTree_nodeKind_nil, NodeKind.emits_player_iff]
            exact ⟨(show oneShotRootNode.Choice from (0 : Fin 2)), rfl⟩)
        simpa using hstep
      · have hstep : oneShotEF.IsReachable ([] ++ [1]) :=
          .step [] 1 .root (by
            change (oneShotTree.nodeKind []).emits (1 : Fin 2)
            rw [oneShotTree_nodeKind_nil, NodeKind.emits_player_iff]
            exact ⟨(show oneShotRootNode.Choice from (1 : Fin 2)), rfl⟩)
        simpa using hstep
    · -- reachable ⇒ membership: induction on `IsReachable`; only the root emits.
      intro hreach
      induction hreach with
      | root => simp
      | step h e hr he ih =>
        simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        -- The predecessor `h` is one of `[], [0], [1]`. Only `[]` (the player node) emits, so the
        -- step must extend `[]`, giving `[0]` or `[1]`.
        rcases ih with rfl | rfl | rfl
        · -- `h = []`: the emitted `e` is `0` or `1` (a `Fin 2`), so `[] ++ [e] = [e] ∈ {[0],[1]}`.
          fin_cases e <;> simp
        · -- `h = [0]`: a terminal node, emits nothing — contradiction.
          exact absurd he (by
            change ¬ (oneShotTree.nodeKind [0]).emits e
            rw [oneShotTree_nodeKind_cons]; exact NodeKind.not_emits_terminal _ e)
        · exact absurd he (by
            change ¬ (oneShotTree.nodeKind [1]).emits e
            rw [oneShotTree_nodeKind_cons]; exact NodeKind.not_emits_terminal _ e)
  obsType_fintype := fun _ => (inferInstance : Fintype Unit)
  obsType_decidable := fun _ => (inferInstance : DecidableEq Unit)
  no_joint := by
    intro h n hk
    have hk' : oneShotTree.nodeKind h = .joint n := hk
    cases h with
    | nil => rw [oneShotTree_nodeKind_nil] at hk'; cases hk'
    | cons e rest => rw [oneShotTree_nodeKind_cons] at hk'; cases hk'
  no_general_chance := by
    intro h n hk
    have hk' : oneShotTree.nodeKind h = .chanceGeneral n := hk
    cases h with
    | nil => rw [oneShotTree_nodeKind_nil] at hk'; cases hk'
    | cons e rest => rw [oneShotTree_nodeKind_cons] at hk'; cases hk'
  has_injective_emit := by
    intro h n hk
    have hk' : oneShotTree.nodeKind h = .player n := hk
    cases h with
    | nil =>
      rw [oneShotTree_nodeKind_nil] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact (Function.Embedding.refl _).injective
    | cons e rest => rw [oneShotTree_nodeKind_cons] at hk'; cases hk'
  nonempty_player_choice := by
    intro h n hk
    have hk' : oneShotTree.nodeKind h = .player n := hk
    cases h with
    | nil =>
      rw [oneShotTree_nodeKind_nil] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact ⟨(0 : Fin 2)⟩
    | cons e rest => rw [oneShotTree_nodeKind_cons] at hk'; cases hk'

/-- **`FiniteExtensiveForm.nil_mem_reach`.** The root `[]` is in the reach finset — reachability is
non-vacuous and the materialized `reach` enumeration contains the root. -/
theorem oneShotFEF_nil_mem_reach : ([] : List (Fin 2)) ∈ oneShotFEF.reach :=
  oneShotFEF.nil_mem_reach

/-- The terminal history `[0]` is reachable. -/
theorem oneShotFEF_zero_mem_reach : ([0] : List (Fin 2)) ∈ oneShotFEF.reach := by
  rw [oneShotFEF.mem_reach_iff]
  have hstep : oneShotEF.IsReachable ([] ++ [0]) :=
    .step [] 0 .root (by
      change (oneShotTree.nodeKind []).emits (0 : Fin 2)
      rw [oneShotTree_nodeKind_nil, NodeKind.emits_player_iff]
      exact ⟨(show oneShotRootNode.Choice from (0 : Fin 2)), rfl⟩)
  simpa using hstep

/-- **`mem_terminalReach_iff`: A reachable terminal.** The history `[0]` is both reachable and
terminal, so it lies in `terminalReach`. -/
theorem oneShotFEF_zero_mem_terminalReach :
    ([0] : List (Fin 2)) ∈ oneShotFEF.terminalReach := by
  rw [oneShotFEF.mem_terminalReach_iff]
  refine ⟨oneShotFEF_zero_mem_reach, ?_⟩
  -- `[0]` is a terminal node, with payoff `![1, 2]`.
  refine ⟨![((0 : Fin 2).val : ℝ) + 1, 2 - ((0 : Fin 2).val : ℝ)], ?_⟩
  change oneShotTree.nodeKind ((0 : Fin 2) :: []) = _
  rw [oneShotTree_nodeKind_cons]

/-- **`mem_terminalReach_iff`: The root is excluded.** The root `[]` is reachable but *not*
terminal (it is player 0's decision node), so it does *not* lie in `terminalReach`. A check that
`terminalReach` filters genuinely on the terminal predicate, not vacuously. -/
theorem oneShotFEF_nil_not_mem_terminalReach :
    ([] : List (Fin 2)) ∉ oneShotFEF.terminalReach := by
  rw [oneShotFEF.mem_terminalReach_iff]
  rintro ⟨-, payoff, hk⟩
  -- `nodeKind [] = .player _`, contradicting `.terminal payoff`.
  have hk' : oneShotTree.nodeKind [] = .terminal payoff := hk
  rw [oneShotTree_nodeKind_nil] at hk'
  cases hk'

/-- **`canonicalRep_mem_reach`.** The canonical representative of player 0's (single) information
set is reachable. NOTE: This membership alone is *not* discriminating — `canonicalRep` falls back
to the root `[]` even for *unreached* info sets, and `[] ∈ reach` always. The genuine content is
`oneShotFEF_canonicalRep_eq_nil` below, which pins the representative to the *unique* history where
player 0 actually moves. -/
theorem oneShotFEF_canonicalRep_mem_reach :
    oneShotFEF.canonicalRep 0 () ∈ oneShotFEF.reach :=
  oneShotFEF.canonicalRep_mem_reach 0 ()

/-- **The canonical representative is the root `[]`** (discriminating anchor). Player 0's only
information set (observation `()`) is genuinely *reached*: Player 0 moves at the root `[]`. Since
`[]` is the *unique* history where player 0 moves (`oneShotTree_movesAt_iff`), every canonical
witness — in particular the `Classical.choose` one inside `canonicalRep` — must equal `[]`. This
rules out the vacuous reading of `canonicalRep_mem_reach`: The representative is the actual
decision node, not the `[]`-fallback that an *unreached* info set would also return. -/
theorem oneShotFEF_canonicalRep_eq_nil :
    oneShotFEF.canonicalRep 0 () = [] := by
  -- The info set is reached (player 0 moves at the root), so `canonicalRep_spec` applies.
  have h_reached : oneShotFEF.IsReachedInfoSet 0 () :=
    ⟨[], oneShotFEF_nil_mem_reach, rfl, (by
      change (oneShotTree.nodeKind []).movesAt 0
      rw [oneShotTree_movesAt_iff]; exact ⟨rfl, rfl⟩)⟩
  obtain ⟨_, _, hmoves⟩ := oneShotFEF.canonicalRep_spec 0 () h_reached
  -- The representative moves player 0, and only `[]` does — so it equals `[]`.
  have hmoves' : (oneShotTree.nodeKind (oneShotFEF.canonicalRep 0 ())).movesAt 0 := hmoves
  rw [oneShotTree_movesAt_iff] at hmoves'
  exact hmoves'.1

/-- **`iChoiceTypeAt_eq_canonicalRep`.** At the reachable root `[]` where player 0 moves, the
node-local choice type coincides with that at the canonical representative of the info set — the
info-set choice-type coherence. -/
theorem oneShotFEF_iChoiceTypeAt_eq_canonicalRep
    (hm : (oneShotFEF.tree.nodeKind []).movesAt 0) :
    (oneShotFEF.tree.nodeKind []).iChoiceTypeAt 0 hm =
      NodeKind.iChoiceTypeAt
        (oneShotFEF.tree.nodeKind (oneShotFEF.canonicalRep 0 (oneShotFEF.info.observe 0 [])))
        0
        (oneShotFEF.canonicalRep_spec 0 (oneShotFEF.info.observe 0 [])
          ⟨[], oneShotFEF_nil_mem_reach, rfl, hm⟩).2.2 :=
  oneShotFEF.iChoiceTypeAt_eq_canonicalRep 0 [] oneShotFEF_nil_mem_reach hm

/-- **The `infoSetChoiceForObs` `Fintype` instance is available** for player 0's info set. -/
example : Fintype (oneShotFEF.infoSetChoiceForObs 0 ()) := inferInstance

/-- **The `infoSetChoiceForObs` `DecidableEq` instance is available.** -/
example : DecidableEq (oneShotFEF.infoSetChoiceForObs 0 ()) := inferInstance

/-- **The `infoSetChoiceForObs` `Inhabited` instance is available.** -/
example : Inhabited (oneShotFEF.infoSetChoiceForObs 0 ()) := inferInstance

/-- **The `PureStrategy` `Fintype` instance is available** for player 0. -/
example : Fintype (oneShotFEF.PureStrategy 0) := inferInstance

/-- **The `PureStrategy` `DecidableEq` instance is available.** -/
example : DecidableEq (oneShotFEF.PureStrategy 0) := inferInstance

/-- **The `PureStrategy` `Inhabited` instance is available.** -/
example : Inhabited (oneShotFEF.PureStrategy 0) := inferInstance

/-! ### Pure-profile step probabilities (StrategicForm.lean) -/

/-- A pure profile built from the `Inhabited` default pure strategy for every player. NOTE: The
per-info-set default choice is `Classical.inhabited_of_nonempty` of the player-choice nonemptiness
witness (`PureStrategy.instInhabited`), i.e. a `Classical.choice` — it does **not** reduce to a
concrete `Fin 2` numeral, so the *value* of the chosen event under this profile is not computable.
Used to exercise the structural `purePrefixStep` reductions (whose statements do not depend on the
concrete choice), not a concrete event value. -/
def oneShotPureProfile : ∀ i, oneShotFEF.PureStrategy i := fun _ => default

/-- **`purePrefixStep_of_player`, the exported indicator formula.** At the root (player 0's node)
the pure-profile step probability of event `e` reduces to the indicator of whether the profile's
*looked-up* choice emits `e`: `1` if `emit (lookupPlayerChoice …) = e`, else `0`. This fixes the
*shape* of the deterministic step (an emit-indicator, the signature that distinguishes a *pure*
profile from a mixed one), but does **not** evaluate the chosen event: `oneShotPureProfile`'s
default choice is `Classical.choice`-opaque (see its docstring), so the looked-up choice does not
reduce to a `Fin 2` numeral and no concrete `prob = 1` / `prob = 0` value is claimed here. -/
theorem oneShotFEF_purePrefixStep_of_player (e : Fin 2) :
    oneShotFEF.purePrefixStep oneShotPureProfile [] e =
      (if oneShotRootNode.emit (oneShotFEF.lookupPlayerChoice oneShotPureProfile []
        oneShotRootNode oneShotTree_nodeKind_nil) = e then 1 else 0) :=
  oneShotFEF.purePrefixStep_of_player oneShotPureProfile oneShotTree_nodeKind_nil e

/-- **`purePrefixStep_of_terminal`.** At the terminal history `[0]` the pure-profile step
probability of any continuation event is `0` — a terminal node never emits, so it contributes no
further reach mass. -/
theorem oneShotFEF_purePrefixStep_of_terminal (e : Fin 2) :
    oneShotFEF.purePrefixStep oneShotPureProfile [0] e = 0 :=
  oneShotFEF.purePrefixStep_of_terminal oneShotPureProfile
    (show oneShotFEF.tree.nodeKind [0] = .terminal _ from rfl) e

/-- **`lookupPlayerChoice_eq_of_obs_agree`.** Two pure profiles that agree at player 0's
observation of the root look up the *same* node-local choice there. The looked-up action depends
only on the player's information set, not on the rest of the profile — the defining locality of a
pure strategy's behavior at a node. -/
theorem oneShotFEF_lookupPlayerChoice_eq_of_obs_agree
    (s s' : ∀ i, oneShotFEF.PureStrategy i)
    (h_eq : s oneShotRootNode.mover (oneShotFEF.info.observe oneShotRootNode.mover []) =
      s' oneShotRootNode.mover (oneShotFEF.info.observe oneShotRootNode.mover [])) :
    oneShotFEF.lookupPlayerChoice s [] oneShotRootNode oneShotTree_nodeKind_nil =
      oneShotFEF.lookupPlayerChoice s' [] oneShotRootNode oneShotTree_nodeKind_nil :=
  oneShotFEF.lookupPlayerChoice_eq_of_obs_agree s s' [] oneShotRootNode
    oneShotTree_nodeKind_nil h_eq

end EconlibTest.GameTheory.ExtensiveFormCore

end
