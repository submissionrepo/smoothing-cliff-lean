/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.OneShot

/-!
# Subgame perfection of finite perfect-information trees as an `EquilibriumProblem`

Packages **subgame perfect equilibrium** (Selten 1965) of a finite perfect-information tree as an
`EquilibriumProblem` via `subgamePerfectStrategyPred`, working directly on local finite-tree
strategies. The file provides the game morphism `perfectInfoTreeToExtensiveMorphism` from this
predicate to the flat extensive-game `spePred`, with constructive inverse `localOf` recovering a
local strategy from any history-indexed behavioral strategy on the canonical embedding, and proves
that the two predicates agree.

## Main definitions

* `subgamePerfectStrategyPred`: Subgame perfection as an `EquilibriumProblem` on local strategies.
* `rootDecisionMover`, `rootBehaviorOf`: The root mover and root behavior of a local strategy.
* `perfectInfoTreeToExtensiveMorphism`: The game morphism to the extensive-game `spePred`.

## Main statements

* `isSubgamePerfectStrategy_iff_subgamePerfectStrategyPred`: Recursive subgame perfection coincides
  with the multi-shot one-player-deviation predicate.

## References

* Selten, Reinhard. 1965. “Spieltheoretische Behandlung Eines Oligopolmodells Mit
  Nachfragetragheit.” *Zeitschrift Fur Die Gesamte Staatswissenschaft* 121 : 301–24, 667–89.

## Tags

subgame perfect equilibrium, perfect information, extensive form, game morphism
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

namespace FinitePerfectInfoTree

variable {I E : Type u}

/-! ### Subgame-perfection as an `EquilibriumProblem` -/

/-- The mover at the root of a finite perfect-info tree, packaged as `Option I` so that terminal
nodes return `none`. Used to default the deviator-value at non-decision histories. -/
def rootDecisionMover : FinitePerfectInfoTree I E → Option I
  | .terminal _ => none
  | @FinitePerfectInfoTree.decision _ _ mover _ _ _ _ _ _ _ => some mover

/-- A terminal tree has no root decision mover. -/
@[simp] lemma rootDecisionMover_terminal (payoff : I → ℝ) :
    (FinitePerfectInfoTree.terminal (I := I) (E := E) payoff).rootDecisionMover = none := rfl

/-- The root decision mover of a decision node is its mover. -/
@[simp] lemma rootDecisionMover_decision (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E) (child : Choice → FinitePerfectInfoTree I E) :
    (FinitePerfectInfoTree.decision mover Choice emit child).rootDecisionMover = some mover := rfl

/-- The root behavior of a local strategy, as a method on the tree: A curried form of
`LocalBehavioralStrategy.rootBehavior`. -/
def rootBehaviorOf (T : FinitePerfectInfoTree I E) (s : T.LocalBehavioralStrategy) :
    T.rootNodeKind.Behavior :=
  LocalBehavioralStrategy.rootBehavior s

/-- Subgame-perfection of a finite perfect-info tree as an `EquilibriumProblem`. The deviator index
is a pair `(i, h) : I × List E` — player `i` deviates at the subtree reached after public history
`h`. The swap is a multi-shot `i`-unilateral deviation: Root behaviors agree at every history where
the mover is not `i`. This mirrors `ExtensiveGame.spePred`'s player-tied `unilateralDeviation i`,
making `perfectInfoTreeToExtensiveMorphism` a `GameMorphism` with constructive inverse `localOf`. -/
def subgamePerfectStrategyPred (T : FinitePerfectInfoTree I E) :
    EquilibriumProblem where
  S := T.LocalBehavioralStrategy
  I := I × List E
  swap p s s' :=
    ∀ h', (T.subtreeAt h').rootDecisionMover ≠ some p.1 →
      (T.subtreeAt h').rootBehaviorOf (LocalBehavioralStrategy.at T s h') =
        (T.subtreeAt h').rootBehaviorOf (LocalBehavioralStrategy.at T s' h')
  value p s := (T.subtreeAt p.2).strategyValue (LocalBehavioralStrategy.at T s p.2) p.1

/-! ### Helpers for `isSubgamePerfectStrategy_iff_subgamePerfectStrategyPred` -/

/-- HEq congruence for `rootBehaviorOf`: Equal trees and HEq strategies give HEq root behaviors. -/
private theorem rootBehaviorOf_heq_congr {T1 T2 : FinitePerfectInfoTree I E}
    (hT : T1 = T2) {s1 : T1.LocalBehavioralStrategy} {s2 : T2.LocalBehavioralStrategy}
    (hs : HEq s1 s2) :
    HEq (T1.rootBehaviorOf s1) (T2.rootBehaviorOf s2) := by
  subst hT
  rw [eq_of_heq hs]

/-- Root behavior at history `emit c :: h_inner` on a `decision`-rooted tree is HEq the root
behavior at history `h_inner` on the `c`-child subtree, where both navigators use `at`. -/ private
theorem rootBehaviorOf_at_emit_cons_heq {mover : I}
    {Choice : Type u} [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (h_inner : List E) :
    HEq
      (((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
        (emit c :: h_inner)).rootBehaviorOf (LocalBehavioralStrategy.at _ s (emit c :: h_inner)))
      (((child c).subtreeAt h_inner).rootBehaviorOf
        (LocalBehavioralStrategy.at _ (s.2 c) h_inner)) :=
  rootBehaviorOf_heq_congr
    (subtreeAt_emit_cons mover Choice emit child c h_inner)
    (at_decision_emit_cons_heq mover Choice emit child s c h_inner)

/-! ### `localOf`: Constructive inverse of `toBehavioralStrategy` on perfect-info trees -/
open FinitePerfectInfoTree in
/-- Restrict a perfect-info `BehavioralStrategy` on `T = decision ... emit child` to the c-th child
subtree. The history prefix `emit c ::` is dropped and choice types transport via
`subtreeAt_emit_cons`. -/
private noncomputable def subBehaviorAtChild [DecidableEq I] {mover : I}
    {Choice : Type u} [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (τ : (decision mover Choice emit child).toExtensiveForm.BehavioralStrategy)
    (c : Choice) : (child c).toExtensiveForm.BehavioralStrategy := by
  intro i obs
  have heq :
      ((decision mover Choice emit child).toGameTree.nodeKind
        (emit c :: obs)).iChoiceTypeAt' i =
        ((child c).toGameTree.nodeKind obs).iChoiceTypeAt' i := by
    change (((decision mover Choice emit child).subtreeAt
      (emit c :: obs)).rootNodeKind).iChoiceTypeAt' i = _
    rw [subtreeAt_emit_cons]
    rfl
  exact simplexTransport heq (τ i (emit c :: obs))

/-- Constructive inverse of `toBehavioralStrategy`: Extract a `LocalBehavioralStrategy` from any
perfect-info `BehavioralStrategy`. At a decision node, the root mix is the mover's mix at the root
info set; continuations are recursively extracted from the subtree-restricted strategies. -/
private noncomputable def localOf [DecidableEq I] : (T : FinitePerfectInfoTree I E) →
T.toExtensiveForm.BehavioralStrategy → T.LocalBehavioralStrategy
  | .terminal _, _ => PUnit.unit
  | @FinitePerfectInfoTree.decision _ _ _mover _Choice _ _ _ _ _emit child, τ =>
      (τ.atHistory [], fun c => localOf (child c) (subBehaviorAtChild τ c))

/-- Stepping `atHistory` past an `emit c :: _` prefix on `T = decision ...` agrees with the
subtree-restricted `subBehaviorAtChild`-atHistory, modulo the type alignment from
`subtreeAt_emit_cons`. -/
private theorem atHistory_emit_cons_heq [DecidableEq I]
    {mover : I} {Choice : Type u} [Fintype Choice] [DecidableEq Choice] [Nonempty Choice]
    [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (τ :
      (FinitePerfectInfoTree.decision mover Choice emit child).toExtensiveForm.BehavioralStrategy)
    (c : Choice) (rest : List E) :
    HEq (τ.atHistory (emit c :: rest))
      ((subBehaviorAtChild τ c).atHistory rest) := by
  have hKind :
      (FinitePerfectInfoTree.decision mover Choice emit child).toGameTree.nodeKind
        (emit c :: rest) = (child c).toGameTree.nodeKind rest := by
    change (((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
      (emit c :: rest)).rootNodeKind) = _
    rw [subtreeAt_emit_cons]
    rfl
  rcases (FinitePerfectInfoTree.decision mover Choice emit child).toGameTree_nodeKind_cases
      (emit c :: rest) with ⟨payoff, hk⟩ | ⟨n, hk⟩
  · -- Terminal: both PUnit.unit.
    have hk_sub : (child c).toGameTree.nodeKind rest = .terminal payoff := by
      rw [← hKind]; exact hk
    have h_L := τ.atHistory_terminal_heq hk
    have h_R := (subBehaviorAtChild τ c).atHistory_terminal_heq hk_sub
    exact h_L.trans h_R.symm
  · -- Player n.
    have hk_sub : (child c).toGameTree.nodeKind rest = .player n := by
      rw [← hKind]; exact hk
    have h_L := τ.atHistory_player_heq hk
    have h_R := (subBehaviorAtChild τ c).atHistory_player_heq hk_sub
    change HEq ((subBehaviorAtChild τ c).atHistory rest)
      ((subBehaviorAtChild τ c) n.mover rest) at h_R
    have h_sub_def :
        (subBehaviorAtChild τ c) n.mover rest =
          simplexTransport
            (by
              change (((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                (emit c :: rest)).rootNodeKind).iChoiceTypeAt' n.mover =
                ((child c).subtreeAt rest).rootNodeKind.iChoiceTypeAt' n.mover
              rw [subtreeAt_emit_cons])
            (τ n.mover (emit c :: rest)) := rfl
    rw [h_sub_def] at h_R
    have h_R_clean : HEq ((subBehaviorAtChild τ c).atHistory rest)
        (τ n.mover (emit c :: rest)) :=
      h_R.trans (simplexTransport_heq _ (τ n.mover (emit c :: rest)))
    exact h_L.trans h_R_clean.symm

/-- The `toBehavioral` of the `localOf`-extracted strategy agrees with `atHistory` at every
history. -/
private theorem toBehavioral_localOf_eq_atHistory [DecidableEq I] :
    ∀ (T : FinitePerfectInfoTree I E) (τ : T.toExtensiveForm.BehavioralStrategy) (h : List E),
      LocalBehavioralStrategy.toBehavioral T (localOf T τ) h = τ.atHistory h := by
  intro T
  induction T with
  | terminal payoff =>
      intro τ h
      have hSub : Subsingleton ((FinitePerfectInfoTree.terminal (I := I) (E := E) payoff
          ).toGameTree.nodeKind h).Behavior := by
        cases h with
        | nil => change Subsingleton PUnit; infer_instance
        | cons _ _ => change Subsingleton PUnit; infer_instance
      exact hSub.elim _ _
  | decision mover Choice emit child ih =>
      intro τ h
      cases h with
      | nil => rfl
      | cons e rest =>
          cases hdec : decodeEmit emit e with
          | some c =>
              have he : e = emit c := ((decodeEmit_eq_some_iff emit e c).mp hdec).symm
              subst he
              apply eq_of_heq
              have h_L := toBehavioral_decision_emit_cons_heq mover Choice emit child
                (localOf _ τ) c rest
              have h_loc :
                  ((localOf (FinitePerfectInfoTree.decision mover Choice emit child) τ).2 c) =
                    localOf (child c) (subBehaviorAtChild τ c) := rfl
              rw [h_loc] at h_L
              have h_ih := ih c (subBehaviorAtChild τ c) rest
              rw [h_ih] at h_L
              have h_sub := atHistory_emit_cons_heq τ c rest
              exact h_L.trans h_sub.symm
          | none =>
              apply eq_of_heq
              have hSubT :
                  (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                    (e :: rest) = .terminal (fun _ : I => (0 : ℝ)) := by
                conv_lhs => unfold subtreeAt
                rw [hdec]
              have hKind :
                  (FinitePerfectInfoTree.decision mover Choice emit child).toGameTree.nodeKind
                    (e :: rest) = .terminal (fun _ : I => (0 : ℝ)) := by
                change ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                  (e :: rest)).rootNodeKind = _
                rw [hSubT]; rfl
              have h_L : HEq
                  (LocalBehavioralStrategy.toBehavioral
                    (FinitePerfectInfoTree.decision mover Choice emit child)
                    (localOf _ τ) (e :: rest))
                  (PUnit.unit : PUnit.{u + 1}) := by
                rw [LocalBehavioralStrategy.toBehavioral.eq_2]
                dsimp
                apply HEq.trans (cast_heq _ _)
                apply HEq.trans
                  (Option.rec_apply_heq_none
                    (C := fun x =>
                      ((match x with
                        | some c => (child c).subtreeAt rest
                        | none => terminal fun _ => 0).rootNodeKind).Behavior)
                    (x := decodeEmit emit e) (h := hdec) _ _)
                refine HEq.trans ?_ (HEq.refl (PUnit.unit : PUnit.{u + 1}))
                exact eqRec_function_apply_heq
                  (D := fun x =>
                    ((match x with
                      | some c => (child c).subtreeAt rest
                      | none => terminal fun _ => 0).rootNodeKind).Behavior)
                  (a := decodeEmit emit e) (b := none)
                  (fun (_ : decodeEmit emit e = none) =>
                    show NodeKind.Behavior (terminal (I := I) (fun _ : I => (0 : ℝ))).rootNodeKind
                    from PUnit.unit) _ _
              have h_R := τ.atHistory_terminal_heq hKind
              exact h_L.trans h_R.symm

/-- Round-trip: `toBehavioralStrategy T` is a left inverse of `localOf T`. At a (player, obs) slot
where the player is the mover, the extracted root mix is re-embedded as the player's mix via
`iLocalBehavior` (identity at `.player`) + `simplexTransport`. At non-mover slots, both sides land
in `stdSimplex ℝ PUnit` which is a subsingleton. -/
private theorem toBehavioralStrategy_localOf [DecidableEq I]
  (T : FinitePerfectInfoTree I E) (τ : T.toExtensiveForm.BehavioralStrategy) :
    LocalBehavioralStrategy.toBehavioralStrategy T (localOf T τ) = τ := by
  funext i obs
  by_cases hm : (T.toGameTree.nodeKind obs).movesAt i
  · rcases T.toGameTree_nodeKind_cases obs with ⟨payoff, hk⟩ | ⟨n, hk⟩
    · -- Contradicts movesAt i.
      exfalso; rw [hk] at hm; exact hm.elim
    · -- Player n. From hm, n.mover = i.
      have hm_eq : n.mover = i := by
        rw [hk] at hm
        exact hm
      subst hm_eq
      have h_at_eq :
          (LocalBehavioralStrategy.toBehavioralStrategy T (localOf T τ)).atHistory obs =
            τ.atHistory obs :=
        (congrFun (atHistory_toBehavioralStrategy_eq T (localOf T τ)) obs).trans
          (toBehavioral_localOf_eq_atHistory T τ obs)
      have h_L := (LocalBehavioralStrategy.toBehavioralStrategy T (localOf T τ)
        ).atHistory_player_heq hk
      have h_R := τ.atHistory_player_heq hk
      rw [h_at_eq] at h_L
      exact eq_of_heq (h_L.symm.trans h_R)
  · have hSub : Subsingleton ((T.toExtensiveForm).info.iChoiceType i obs) :=
      T.toExtensiveForm_iChoiceType_subsingleton i obs hm
    haveI : Subsingleton (stdSimplex ℝ ((T.toExtensiveForm).info.iChoiceType i obs)) :=
      inferInstance
    exact Subsingleton.elim _ _

/-- Bridge: The rootBehavior of `σ.at h` equals `toBehavioral T σ h`. Both are at type
`(T.subtreeAt h).rootNodeKind.Behavior`. -/
private theorem rootBehaviorOf_at_eq_toBehavioral (T : FinitePerfectInfoTree I E) (σ :
T.LocalBehavioralStrategy) (h : List E) :
    (T.subtreeAt h).rootBehaviorOf (LocalBehavioralStrategy.at T σ h) =
      LocalBehavioralStrategy.toBehavioral T σ h := by
  induction T generalizing h with
  | terminal payoff =>
      apply eq_of_heq
      have hSub : Subsingleton ((FinitePerfectInfoTree.terminal (I := I) (E := E)
          payoff).toGameTree.nodeKind h).Behavior := by
        cases h with
        | nil => change Subsingleton PUnit; infer_instance
        | cons _ _ => change Subsingleton PUnit; infer_instance
      exact heq_of_eq (hSub.elim _ _)
  | decision mover Choice emit child ih =>
      cases h with
      | nil => rfl
      | cons e rest =>
          cases hdec : decodeEmit emit e with
          | some c =>
              have he : e = emit c := ((decodeEmit_eq_some_iff emit e c).mp hdec).symm
              subst he
              apply eq_of_heq
              have hL := rootBehaviorOf_at_emit_cons_heq σ c rest
              have hMid := ih c (σ.2 c) rest
              have hR_HEq := toBehavioral_decision_emit_cons_heq mover Choice emit child σ c rest
              exact hL.trans ((heq_of_eq hMid).trans hR_HEq.symm)
          | none =>
              apply eq_of_heq
              have hSubT :
                  (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                    (e :: rest) = .terminal (fun _ : I => (0 : ℝ)) := by
                conv_lhs => unfold subtreeAt
                rw [hdec]
              have hSub : Subsingleton ((FinitePerfectInfoTree.decision mover Choice emit child
                  ).toGameTree.nodeKind (e :: rest)).Behavior := by
                change Subsingleton (((FinitePerfectInfoTree.decision mover Choice emit child
                  ).subtreeAt (e :: rest)).rootNodeKind.Behavior)
                rw [hSubT]; change Subsingleton PUnit; infer_instance
              exact heq_of_eq (hSub.elim _ _)

/-- At a history whose embedded node kind is `player n`, the subtree's `rootDecisionMover` is
`some n.mover`. Shared by both directions of the morphism, where a `player n` node kind must be
read back as a decision-rooted subtree with mover `n.mover`. -/
private theorem rootDecisionMover_of_nodeKind_player (T : FinitePerfectInfoTree I E) {h : List E}
    {n : PlayerNode I E} (hk : T.toGameTree.nodeKind h = .player n) :
    (T.subtreeAt h).rootDecisionMover = some n.mover := by
  change T.nodeKindAt h = .player n at hk
  unfold FinitePerfectInfoTree.nodeKindAt FinitePerfectInfoTree.rootNodeKind at hk
  cases hsub : T.subtreeAt h with
  | terminal _ => rw [hsub] at hk; exact absurd hk (by simp)
  | decision mover' Choice' emit' child' =>
      rw [hsub] at hk
      simp only [NodeKind.player.injEq] at hk
      obtain ⟨hMover_eq, _, _⟩ := hk
      rw [show (FinitePerfectInfoTree.decision mover' Choice' emit' child'
        ).rootDecisionMover = some mover' from rfl]

/-- The substrate-uniform bridge from `subgamePerfectStrategyPred` (`EquilibriumProblem` on local
finite-tree strategies) to the embedded `ExtensiveGame`'s `spePred`. Both substrates carry the same
deviator type `I × List E`, so the deviator map is the identity. The forward map is the canonical
embedding `LocalBehavioralStrategy.toBehavioralStrategy`. The inverse is `localOf`, constructed by
recursive extraction of mover mixes from `atHistory`. -/
noncomputable def perfectInfoTreeToExtensiveMorphism [DecidableEq I]
  (T : FinitePerfectInfoTree I E) :
    GameMorphism T.subgamePerfectStrategyPred T.toExtensiveGame.spePred where
  toFun s := LocalBehavioralStrategy.toBehavioralStrategy T s
  deviatorMap p := p
  swap_lifts := by
    rintro ⟨i, h⟩ σ τ' hQ
    refine ⟨localOf T τ', ?_, toBehavioralStrategy_localOf T τ'⟩
    intro h' hMover
    rw [rootBehaviorOf_at_eq_toBehavioral, rootBehaviorOf_at_eq_toBehavioral,
        toBehavioral_localOf_eq_atHistory]
    rcases T.toGameTree_nodeKind_cases h' with ⟨payoff, hk⟩ | ⟨n, hk⟩
    · -- Terminal: Behavior at terminal is PUnit (subsingleton).
      have hSub : Subsingleton (T.toGameTree.nodeKind h').Behavior := by
        rw [hk]; change Subsingleton PUnit; infer_instance
      exact hSub.elim _ _
    · -- Player n: derive n.mover ≠ i from hMover, then apply Q.swap at (n.mover, h').
      have hRDM : (T.subtreeAt h').rootDecisionMover = some n.mover :=
        rootDecisionMover_of_nodeKind_player T hk
      have hne : n.mover ≠ i := by
        intro habs
        apply hMover
        rw [hRDM, habs]
      have h_eq_τ_σ : τ' n.mover h' =
          (LocalBehavioralStrategy.toBehavioralStrategy T σ) n.mover h' :=
        hQ n.mover h' hne
      have h_L_HEq := τ'.atHistory_player_heq hk
      have h_R_HEq := (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory_player_heq hk
      have h_at_eq :
          (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory h' = τ'.atHistory h' := by
        apply eq_of_heq
        exact (h_R_HEq.trans (heq_of_eq h_eq_τ_σ.symm)).trans h_L_HEq.symm
      have h_ofp : (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory h' =
          LocalBehavioralStrategy.toBehavioral T σ h' :=
        congrFun (atHistory_toBehavioralStrategy_eq T σ) h'
      rw [← h_ofp, h_at_eq]
      rfl
  value_eq := by
    intro p s
    obtain ⟨i, h⟩ := p
    change (T.subtreeAt h).behavioralValue (T.subtreeBehavioral
        (fun h' => (LocalBehavioralStrategy.toBehavioralStrategy T s).atHistory h') h) i =
      (T.subtreeAt h).strategyValue (LocalBehavioralStrategy.at T s h) i
    rw [atHistory_toBehavioralStrategy_eq, subtreeBehavioral_toBehavioral,
        behavioralValue_toBehavioral]

/-- Swap preservation under the canonical embedding `toBehavioralStrategy`: A local multi-shot swap
on σ, σ' translates to an extensive-form `unilateralDeviation i` on their embeddings. -/
private theorem unilateralDeviation_of_subgamePerfectStrategyPred_swap [DecidableEq I]
    (T : FinitePerfectInfoTree I E) (i : I) (σ σ' : T.LocalBehavioralStrategy)
    (h_swap : ∀ h', (T.subtreeAt h').rootDecisionMover ≠ some i →
      (T.subtreeAt h').rootBehaviorOf (LocalBehavioralStrategy.at T σ h') =
        (T.subtreeAt h').rootBehaviorOf (LocalBehavioralStrategy.at T σ' h')) :
    T.toExtensiveForm.unilateralDeviation i
      (LocalBehavioralStrategy.toBehavioralStrategy T σ)
      (LocalBehavioralStrategy.toBehavioralStrategy T σ') := by
  intro j obs hne
  by_cases hm : (T.toGameTree.nodeKind obs).movesAt j
  · -- j moves at obs ⇒ obs's subtree is decision with mover j ≠ i.
    rcases T.toGameTree_nodeKind_cases obs with ⟨payoff, hk⟩ | ⟨n, hk⟩
    · -- Contradicts movesAt j: terminal has no movers.
      rw [hk] at hm; exact hm.elim
    · -- Player n with n.mover = j.
      have hm_eq : n.mover = j := by
        rw [hk] at hm
        exact hm
      have hRDM : (T.subtreeAt obs).rootDecisionMover = some j :=
        (rootDecisionMover_of_nodeKind_player T hk).trans (congrArg some hm_eq)
      have hRDM_ne : (T.subtreeAt obs).rootDecisionMover ≠ some i := by
        rw [hRDM]; intro habs; exact hne (Option.some.inj habs)
      have h_root_eq := h_swap obs hRDM_ne
      rw [rootBehaviorOf_at_eq_toBehavioral, rootBehaviorOf_at_eq_toBehavioral] at h_root_eq
      have h_ofp_σ : (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory obs =
          LocalBehavioralStrategy.toBehavioral T σ obs :=
        congrFun (atHistory_toBehavioralStrategy_eq T σ) obs
      have h_ofp_σ' : (LocalBehavioralStrategy.toBehavioralStrategy T σ').atHistory obs =
          LocalBehavioralStrategy.toBehavioral T σ' obs :=
        congrFun (atHistory_toBehavioralStrategy_eq T σ') obs
      have h_at_eq :
          (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory obs =
            (LocalBehavioralStrategy.toBehavioralStrategy T σ').atHistory obs := by
        rw [h_ofp_σ, h_ofp_σ', h_root_eq]
      have h_L := (LocalBehavioralStrategy.toBehavioralStrategy T σ).atHistory_player_heq hk
      have h_R := (LocalBehavioralStrategy.toBehavioralStrategy T σ').atHistory_player_heq hk
      rw [← hm_eq]
      apply eq_of_heq
      exact (h_R.symm.trans (heq_of_eq h_at_eq.symm)).trans h_L
  · -- ¬ movesAt j: both (toFun _) j obs are subsingleton-equal.
    have hSub : Subsingleton ((T.toExtensiveForm).info.iChoiceType j obs) :=
      T.toExtensiveForm_iChoiceType_subsingleton j obs hm
    haveI : Subsingleton (stdSimplex ℝ ((T.toExtensiveForm).info.iChoiceType j obs)) :=
      inferInstance
    exact Subsingleton.elim _ _

/-- Recursive subgame perfection of a local strategy is equivalent to the multi-shot
one-player-deviation predicate `subgamePerfectStrategyPred`. -/
theorem isSubgamePerfectStrategy_iff_subgamePerfectStrategyPred
    (T : FinitePerfectInfoTree I E) (s : T.LocalBehavioralStrategy) :
    T.IsSubgamePerfectStrategy s ↔ T.subgamePerfectStrategyPred.IsEquilibrium s := by
  classical
  rw [isSubgamePerfectStrategy_iff_spePred]
  refine ⟨fun hQ ⟨i, h⟩ s' hP => ?_, fun hP => T.perfectInfoTreeToExtensiveMorphism.transport hP⟩
  have hQ_swap := unilateralDeviation_of_subgamePerfectStrategyPred_swap T i s s' hP
  have h_app := hQ (i, h) (LocalBehavioralStrategy.toBehavioralStrategy T s') hQ_swap
  have h_eq_s :
      T.toExtensiveGame.spePred.value (i, h) (LocalBehavioralStrategy.toBehavioralStrategy T s) =
        T.subgamePerfectStrategyPred.value (i, h) s :=
    T.perfectInfoTreeToExtensiveMorphism.value_eq (i, h) s
  have h_eq_s' :
      T.toExtensiveGame.spePred.value (i, h) (LocalBehavioralStrategy.toBehavioralStrategy T s') =
        T.subgamePerfectStrategyPred.value (i, h) s' :=
    T.perfectInfoTreeToExtensiveMorphism.value_eq (i, h) s'
  rw [h_eq_s, h_eq_s'] at h_app
  exact h_app

end FinitePerfectInfoTree

end Econlib.GameTheory
