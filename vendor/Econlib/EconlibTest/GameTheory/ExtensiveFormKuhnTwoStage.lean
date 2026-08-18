/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import Mathlib

/-!
# Extensive-Form Kuhn — Two-Stage Non-Vacuity Checks

Compile-time semantic witnesses for Kuhn's realization-equivalence theorem
(`Econlib.GameTheory.ExtensiveForm.Kuhn.{Forward, Maps, Converse, PerfectRecall}`) on a carrier
where behavioral and mixed strategies are *non-trivially distinct*. The single-info-set carrier
`oneShotPR` (in `ExtensiveFormKuhn.lean`) cannot expose the difference: with one information set a
behavioral strategy and the mixed strategy on its strategic normalization carry the same data. Here
the same player has **two sequential information sets**, so a mixed strategy can *correlate* its
choices across the two stages while a behavioral one cannot — Kuhn's theorem says the realization
probabilities still agree, and the witnesses below check that on this genuinely two-stage game.

`twoStagePR` is `twoStageFEF` (a finite extensive form) bundled with its perfect-recall witness.
Player `0` moves twice in sequence, each time over `Fin 2`; player `1` never moves. The three
decision nodes are the root `[]` and the two length-one histories `[0]`, `[1]`; the four leaves are
the length-two histories `[e₁, e₂]`. Player `0`'s observation type is `Fin 3` (root ↦ `0`, after
first move `0` ↦ `1`, after first move `1` ↦ `2`), so the two stages live in *distinct* information
sets `1` and `2`. The terminal payoff at history `[e₁, e₂]` is `![2·e₁ + e₂ + 1, 4 − (2·e₁ + e₂)]`,
so the four leaves carry distinct mover payoffs `1, 2, 3, 4`. The reachable histories are exactly
`[], [0], [1], [0,0], [0,1], [1,0], [1,1]`.

## Main definitions

- `twoStageFEF`: the finite extensive form of the two-stage game.
- `twoStagePR`: `twoStageFEF` bundled with its perfect-recall certificate.
- `twoStageσ`: a genuinely two-stage behavioral strategy with distinct per-stage mixtures.
- `twoStageCorrelated`: a correlated (non-product) mixed strategy on the strategic normalization.

## Main statements

- `behavioral_realizes_mixed_twoStage`: the forward Kuhn map is realization-equivalent to
  `twoStageσ`.
- `mixed_realizes_behavioral_correlated`: the converse Kuhn map applied to the correlated mixed
  strategy `twoStageCorrelated` yields a realization-equivalent behavioral strategy.
- `reachProb_one_one_eq_third`: the two-stage path `[1,1]` has reach probability `1/2 · 2/3 = 1/3`.

## Tags

game theory, extensive form, kuhn's theorem, perfect recall, behavioral strategy, mixed strategy
-/

noncomputable section

open Econlib.GameTheory

namespace EconlibTest.GameTheory.ExtensiveFormKuhnTwoStage

/-! ## The two-stage game tree -/

/-- The game tree of `twoStageFEF`: Player `0` decides over `Fin 2` at the root `[]` (emit =
identity) and again at each length-one history `[e₁]` (emit = identity); every length-two history
is a terminal node. The terminal payoff at history `[e₁, e₂]` is
`![2·e₁ + e₂ + 1, 4 − (2·e₁ + e₂)]`, so the four leaves pay the mover `1, 2, 3, 4` and player `1`
the mirror values `3, 2, 1, 0`. -/
def twoStageTree : GameTree (Fin 2) (Fin 2) where
  nodeKind h :=
    match h with
    | [] => .player { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }
    | [_] => .player { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }
    | e₁ :: e₂ :: _ =>
        .terminal ![(2 * (e₁.val : ℝ) + (e₂.val : ℝ)) + 1, 4 - (2 * (e₁.val : ℝ) + (e₂.val : ℝ))]

/-- The player node shared by the root and the two length-one histories (player `0` over `Fin 2`,
emit = identity). -/
def twoStageNode : PlayerNode (Fin 2) (Fin 2) :=
  { mover := 0, Choice := Fin 2, emit := Function.Embedding.refl _ }

/-- The root of `twoStageTree` is a player node. -/
@[simp] lemma twoStageTree_nodeKind_nil :
    twoStageTree.nodeKind [] = .player twoStageNode := rfl

/-- A length-one history of `twoStageTree` is a player node (player `0`'s second decision). -/
@[simp] lemma twoStageTree_nodeKind_single (e : Fin 2) :
    twoStageTree.nodeKind [e] = .player twoStageNode := rfl

/-- A length-two-or-more history of `twoStageTree` is a terminal node. -/
@[simp] lemma twoStageTree_nodeKind_cons_cons (e₁ e₂ : Fin 2) (rest : List (Fin 2)) :
    twoStageTree.nodeKind (e₁ :: e₂ :: rest) =
      .terminal ![(2 * (e₁.val : ℝ) + (e₂.val : ℝ)) + 1,
        4 - (2 * (e₁.val : ℝ) + (e₂.val : ℝ))] := rfl

/-- Player `0` moves at the root and at each length-one history of `twoStageTree`; nowhere else
(every length-two history is terminal). -/
lemma twoStageTree_movesAt_iff (i : Fin 2) (h : List (Fin 2)) :
    (twoStageTree.nodeKind h).movesAt i ↔
      ((h = [] ∨ h = [0] ∨ h = [1]) ∧ i = 0) := by
  match h with
  | [] =>
    rw [twoStageTree_nodeKind_nil]
    constructor
    · intro hm; exact ⟨Or.inl rfl, hm.symm⟩
    · rintro ⟨-, rfl⟩; rfl
  | [e] =>
    rw [twoStageTree_nodeKind_single]
    constructor
    · intro hm
      refine ⟨?_, hm.symm⟩
      fin_cases e
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro ⟨-, rfl⟩; rfl
  | e₁ :: e₂ :: rest =>
    rw [twoStageTree_nodeKind_cons_cons]
    simp only [NodeKind.movesAt, reduceCtorEq, false_iff, not_and]
    intro h_or
    rcases h_or with h | h | h <;> simp at h

/-! ## The two-stage information structure -/

/-- The finite information structure for `twoStageFEF`: Player `0` has three information sets
(`Obs 0 = Fin 3`) — the root (observation `0`), and the two second-stage nodes after first move `0`
(observation `1`) and after first move `1` (observation `2`). Player `1` never moves and has a
single degenerate info set (`Obs 1 = Unit`). The observation map sends `[]` ↦ `0`, `0 :: _` ↦ `1`,
`1 :: _` ↦ `2` (any total extension of this agrees on the three decision nodes). -/
def twoStageInfo : InfoStructure (Fin 2) (Fin 2) where
  Obs i := match i with | 0 => Fin 3 | 1 => Unit
  observe i := match i with
    | 0 => fun h => match h with | [] => 0 | (0 : Fin 2) :: _ => 1 | (1 : Fin 2) :: _ => 2
    | 1 => fun _ => ()
  iChoiceType i _ := if i = 0 then Fin 2 else Unit
  iChoiceFintype i _ := by split <;> infer_instance
  iChoiceDecEq i _ := by split <;> infer_instance
  iChoiceInhabited i _ := by split <;> infer_instance

/-- The extensive form of `twoStageFEF`. The only histories where a player moves are `[]`, `[0]`,
`[1]` (all player `0`), where `iChoiceTypeAt 0 = Fin 2 = iChoiceType 0 (observe 0 _)`, so
`iChoice_compatible` holds by `rfl` after casing on the moving history. -/
def twoStageEF : ExtensiveForm (Fin 2) (Fin 2) where
  tree := twoStageTree
  info := twoStageInfo
  iChoice_compatible := by
    intro i h hm
    rw [twoStageTree_movesAt_iff] at hm
    obtain ⟨h_or, rfl⟩ := hm
    rcases h_or with rfl | rfl | rfl <;> rfl

/-! ## The finite extensive form -/

/-- Player `0`'s node emits its `Fin 2` choice `c` at any decision history (root or length-one):
The player node `twoStageNode` has identity emit, so it emits `c`. -/
lemma twoStageNode_emits (c : Fin 2) :
    (NodeKind.player (I := Fin 2) (E := Fin 2) twoStageNode).emits c :=
  ⟨(show twoStageNode.Choice from c), rfl⟩

/-- The complete `FiniteExtensiveForm` of the two-stage game. The reachable histories are exactly
the seven `[], [0], [1], [0,0], [0,1], [1,0], [1,1]`: The two decision stages (each a `Fin 2`
choice) followed by termination. -/
def twoStageFEF : FiniteExtensiveForm (Fin 2) (Fin 2) where
  toExtensiveForm := twoStageEF
  reach := {[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]}
  mem_reach_iff := by
    intro h
    constructor
    · intro hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hroot : twoStageEF.IsReachable [] := .root
      have step1 : ∀ e₁ : Fin 2, twoStageEF.IsReachable [e₁] := fun e₁ => by
        have : twoStageEF.IsReachable ([] ++ [e₁]) :=
          .step [] e₁ hroot (twoStageNode_emits e₁)
        simpa using this
      have step2 : ∀ e₁ e₂ : Fin 2, twoStageEF.IsReachable [e₁, e₂] := fun e₁ e₂ => by
        have : twoStageEF.IsReachable ([e₁] ++ [e₂]) :=
          .step [e₁] e₂ (step1 e₁) (twoStageNode_emits e₂)
        simpa using this
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hroot
      · exact step1 0
      · exact step1 1
      · exact step2 0 0
      · exact step2 0 1
      · exact step2 1 0
      · exact step2 1 1
    · intro hreach
      induction hreach with
      | root => simp
      | step h e hr he ih =>
        simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        rcases ih with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · fin_cases e <;> simp
        · fin_cases e <;> simp
        · fin_cases e <;> simp
        all_goals exact absurd he (NodeKind.not_emits_terminal _ e)
  obsType_fintype := fun i => match i with
    | 0 => (inferInstance : Fintype (Fin 3))
    | 1 => (inferInstance : Fintype Unit)
  obsType_decidable := fun i => match i with
    | 0 => (inferInstance : DecidableEq (Fin 3))
    | 1 => (inferInstance : DecidableEq Unit)
  no_joint := by
    intro h n hk
    have hk' : twoStageTree.nodeKind h = .joint n := hk
    match h with
    | [] => rw [twoStageTree_nodeKind_nil] at hk'; cases hk'
    | [e] => rw [twoStageTree_nodeKind_single] at hk'; cases hk'
    | e₁ :: e₂ :: rest => rw [twoStageTree_nodeKind_cons_cons] at hk'; cases hk'
  no_general_chance := by
    intro h n hk
    have hk' : twoStageTree.nodeKind h = .chanceGeneral n := hk
    match h with
    | [] => rw [twoStageTree_nodeKind_nil] at hk'; cases hk'
    | [e] => rw [twoStageTree_nodeKind_single] at hk'; cases hk'
    | e₁ :: e₂ :: rest => rw [twoStageTree_nodeKind_cons_cons] at hk'; cases hk'
  has_injective_emit := by
    intro h n hk
    have hk' : twoStageTree.nodeKind h = .player n := hk
    match h with
    | [] =>
      rw [twoStageTree_nodeKind_nil] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact (Function.Embedding.refl _).injective
    | [e] =>
      rw [twoStageTree_nodeKind_single] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact (Function.Embedding.refl _).injective
    | e₁ :: e₂ :: rest => rw [twoStageTree_nodeKind_cons_cons] at hk'; cases hk'
  nonempty_player_choice := by
    intro h n hk
    have hk' : twoStageTree.nodeKind h = .player n := hk
    match h with
    | [] =>
      rw [twoStageTree_nodeKind_nil] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact ⟨(0 : Fin 2)⟩
    | [e] =>
      rw [twoStageTree_nodeKind_single] at hk'
      obtain rfl := (NodeKind.player.injEq _ _).mp hk'.symm
      exact ⟨(0 : Fin 2)⟩
    | e₁ :: e₂ :: rest => rw [twoStageTree_nodeKind_cons_cons] at hk'; cases hk'

/-! ## The perfect-recall witness -/

/-- **`twoStageFEF` has perfect recall.** This is `FiniteExtensiveForm.IsPerfectRecall`, the
experience-based ∀-definition: Any two reachable histories in the same information set of a player
induce the same experience. On `twoStageFEF` the proof is structural rather than vacuous (unlike
the single-info-set `oneShotFEF`, where both moving histories are forced to be the root). Here
player `0` moves at *three* distinct histories `[], [0], [1]` carrying *three distinct*
observations `0, 1, 2 : Fin 3`; observation-equality therefore forces the two histories to be
literally equal, so the experiences coincide by `rfl` after substitution. The non-vacuity is
exactly that two of the three movers (`[0]` and `[1]`) are second-stage nodes in genuinely
different information sets — the perfect-recall clause separates them by observation. -/
theorem twoStageFEF_isPerfectRecall : twoStageFEF.IsPerfectRecall := by
  intro i h₁ h₂ _ _ hm₁ hm₂ hobs
  obtain ⟨h₁_or, rfl⟩ := (twoStageTree_movesAt_iff i h₁).mp hm₁
  obtain ⟨h₂_or, -⟩ := (twoStageTree_movesAt_iff 0 h₂).mp hm₂
  -- The three observations `0, 1, 2 : Fin 3` are pairwise distinct, so observation-equality
  -- forces `h₁ = h₂`; the experiences then coincide by `rfl`.
  rcases h₁_or with rfl | rfl | rfl <;> rcases h₂_or with rfl | rfl | rfl <;>
    first
      | rfl
      | (exact absurd hobs (by decide))

/-- The two-stage game bundled with its perfect-recall witness — a
`PerfectRecallFiniteExtensiveForm`, the type Kuhn's realization equivalence consumes. -/
def twoStagePR : PerfectRecallFiniteExtensiveForm (Fin 2) (Fin 2) where
  toFiniteExtensiveForm := twoStageFEF
  perfectRecall := twoStageFEF_isPerfectRecall

/-! ## A genuinely two-stage behavioral strategy

The witnesses below need a behavioral strategy whose two stages carry *different, non-vertex*
mixtures — this is what makes the two-stage structure observable. We build the simplex points
`(1/2, 1/2)` and `(1/3, 2/3)` over `Fin 2` and assemble them. -/

/-- The mixed point `(1/2, 1/2) ∈ stdSimplex ℝ (Fin 2)`. -/
def half : stdSimplex ℝ (Fin 2) :=
  ⟨![1/2, 1/2], by
    refine ⟨fun c => by fin_cases c <;> norm_num, ?_⟩
    rw [Fin.sum_univ_two]; norm_num⟩

/-- The mixed point `(1/3, 2/3) ∈ stdSimplex ℝ (Fin 2)`. -/
def thirds : stdSimplex ℝ (Fin 2) :=
  ⟨![1/3, 2/3], by
    refine ⟨fun c => by fin_cases c <;> norm_num, ?_⟩
    rw [Fin.sum_univ_two]; norm_num⟩

/-- A genuinely two-stage behavioral strategy on `twoStageFEF`: Player `0` mixes `(1/2, 1/2)` at
the root (obs `0`), plays the vertex on choice `0` at the obs-`1` info set (after first move `0`),
and mixes `(1/3, 2/3)` at the obs-`2` info set (after first move `1`); player `1` plays its
degenerate vertex. The two stages carry *distinct* mixtures, so this strategy genuinely uses player
`0`'s two information sets — the property that the single-info-set `oneShotσ` cannot express. The
strategy is defined by matching on `i` so that `iChoiceType i obs = if i = 0 then Fin 2 else Unit`
reduces definitionally per arm. -/
def twoStageσ : twoStageFEF.toExtensiveForm.BehavioralStrategy := fun i =>
  match i with
  | 0 => fun (obs : Fin 3) => match obs with
      | 0 => half
      | 1 => stdSimplex.vertex (S := ℝ) (0 : Fin 2)
      | 2 => thirds
  | 1 => fun obs => stdSimplex.vertex (S := ℝ) (default : twoStageFEF.info.iChoiceType 1 obs)

/-! ## Forward Kuhn map (Maps.lean, Forward.lean)

The forward map `behavioralToMixed σ` turns `twoStageσ` into a mixed strategy on the strategic
normalization. On this two-stage carrier the per-player product `∏ obs` ranges over *three*
observations (`Fin 3`), so the normalization checks below are genuine products across stages, not
single-factor identities. -/

/-- The per-info-set mixed factor of player `0`'s mixed image at a pure strategy is nonnegative. -/
lemma behavioralToMixedFactor_nonneg (s : twoStageFEF.PureStrategy 0) (obs : Fin 3) :
    0 ≤ twoStageFEF.behavioralToMixedFactor twoStageσ 0 s obs :=
  twoStageFEF.behavioralToMixedFactor_nonneg twoStageσ 0 s obs

/-- At each of player `0`'s three info sets, the mixed factors of `twoStageσ` sum to one over
that info set's choices. -/
lemma behavioralToMixedFactor_sum_one (obs : Fin 3) :
    ∑ c : twoStageFEF.infoSetChoiceForObs 0 obs,
      (twoStageFEF.tree.nodeKind (twoStageFEF.canonicalRep 0 obs)).behaviorEval
        (twoStageσ.atHistory (twoStageFEF.canonicalRep 0 obs)) c = 1 :=
  twoStageFEF.behavioralToMixedFactor_sum_one twoStageσ 0 obs

/-- The mixed image of `twoStageσ` is a genuine distribution: the product masses
`∏ i, behavioralToMixed twoStageσ i (s i)` sum to one over all pure profiles `s`. Player `0`'s
pure-strategy space is the product over the three info sets (`2 × 2 × 2 = 8` pure strategies),
so this is a genuine two-stage product normalization. -/
theorem behavioralToMixed_total_sum_one :
    ∑ s : (i : Fin 2) → twoStageFEF.PureStrategy i,
      ∏ i : Fin 2, (twoStageFEF.behavioralToMixed twoStageσ i) (s i) = 1 :=
  twoStageFEF.behavioralToMixed_total_sum_one twoStageσ

/-- The forward map `behavioralToMixed twoStageσ` is realization-equivalent to `twoStageσ`: they
assign the same probability to every reachable terminal history. Unlike the `oneShotσ` witness,
`twoStageσ` is genuinely mixed at *both* stages, so the realized terminal distribution is
non-degenerate — every length-two leaf gets positive mass except those behind the obs-`1` vertex. -/
theorem behavioral_realizes_mixed_twoStage :
    twoStagePR.toFiniteExtensiveForm.RealizationEquivalent twoStageσ
      (twoStagePR.toFiniteExtensiveForm.behavioralToMixed twoStageσ) :=
  twoStagePR.behavioral_realizes_mixed twoStageσ

/-! ## A genuinely correlated mixed strategy (Converse.lean, headline)

On the strategic normalization, player `0`'s action set is `PureStrategy 0`, a *function* from
the three info sets to choices. A mixed strategy here may place mass on a *correlated* pair of pure
strategies — one that no behavioral strategy (which mixes each info set independently) can
reproduce as a product. We build the maximally correlated point: Mass `1/2` on "play `0` at every
info set" and `1/2` on "play `1` at every info set", with *zero* mass on the two cross strategies
"play `0` then `1`" and "play `1` then `0`". This is the carrier on which Kuhn's converse is
non-trivial. -/

/-- Each of player `0`'s three information sets is reached: the root, the node after first move `0`,
and the node after first move `1`. -/
lemma twoStageFEF_reachedObs (obs : Fin 3) : twoStageFEF.IsReachedInfoSet 0 obs := by
  fin_cases obs
  · -- root info set: reached by `[]`.
    refine ⟨[], ?_, rfl, ?_⟩
    · rw [twoStageFEF.mem_reach_iff]; exact .root
    · change (twoStageTree.nodeKind []).movesAt 0
      rw [twoStageTree_movesAt_iff]; exact ⟨Or.inl rfl, rfl⟩
  · -- obs `1`: reached by `[0]`.
    refine ⟨[0], ?_, rfl, ?_⟩
    · rw [twoStageFEF.mem_reach_iff]
      have : twoStageEF.IsReachable ([] ++ [(0 : Fin 2)]) :=
        .step [] 0 .root (twoStageNode_emits 0)
      simpa using this
    · change (twoStageTree.nodeKind [0]).movesAt 0
      rw [twoStageTree_movesAt_iff]; exact ⟨Or.inr (Or.inl rfl), rfl⟩
  · -- obs `2`: reached by `[1]`.
    refine ⟨[1], ?_, rfl, ?_⟩
    · rw [twoStageFEF.mem_reach_iff]
      have : twoStageEF.IsReachable ([] ++ [(1 : Fin 2)]) :=
        .step [] 1 .root (twoStageNode_emits 1)
      simpa using this
    · change (twoStageTree.nodeKind [1]).movesAt 0
      rw [twoStageTree_movesAt_iff]; exact ⟨Or.inr (Or.inr rfl), rfl⟩

/-- At each of player `0`'s three info sets, the canonical-rep choice type
`infoSetChoiceForObs 0 obs` equals `Fin 2`. -/
lemma twoStageFEF_infoSetChoice_eq (obs : Fin 3) :
    twoStageFEF.infoSetChoiceForObs 0 obs = Fin 2 := by
  unfold FiniteExtensiveForm.infoSetChoiceForObs
  have hm := (twoStageFEF.canonicalRep_spec 0 obs (twoStageFEF_reachedObs obs)).2.2
  obtain ⟨h_or, -⟩ := (twoStageTree_movesAt_iff 0 (twoStageFEF.canonicalRep 0 obs)).mp hm
  rcases h_or with h | h | h <;> rw [h] <;> rfl

/-- Player `0`'s pure strategy "play choice `0` at every information set" (transporting the `Fin 2`
numeral `0` through the canonical-rep choice-type equality). -/
def twoStagePureAll0 : twoStageFEF.PureStrategy 0 :=
  fun obs => cast (twoStageFEF_infoSetChoice_eq obs).symm (0 : Fin 2)

/-- Player `0`'s pure strategy "play choice `1` at every information set". -/
def twoStagePureAll1 : twoStageFEF.PureStrategy 0 :=
  fun obs => cast (twoStageFEF_infoSetChoice_eq obs).symm (1 : Fin 2)

/-- The two pure strategies `twoStagePureAll0` and `twoStagePureAll1` are distinct (they differ at
the root info set, where `0 ≠ 1` in `Fin 2`). -/
lemma twoStagePureAll0_ne_pureAll1 : twoStagePureAll0 ≠ twoStagePureAll1 := by
  intro h
  have h0 : twoStagePureAll0 (0 : Fin 3) = twoStagePureAll1 (0 : Fin 3) := congrFun h (0 : Fin 3)
  unfold twoStagePureAll0 twoStagePureAll1 at h0
  have : (0 : Fin 2) = (1 : Fin 2) :=
    (cast_inj (twoStageFEF_infoSetChoice_eq (0 : Fin 3)).symm).mp h0
  exact absurd this (by decide)

/-- The genuinely **correlated** mixed point for player `0`: Mass `1/2` on `twoStagePureAll0` and
`1/2` on `twoStagePureAll1`, with `0` on every other pure strategy. The two support strategies
*correlate* the two stages (always-`0` or always-`1`); no behavioral strategy can reproduce this as
an independent per-info-set product, since a product would also place mass on the two cross
strategies. This is the non-product mixed strategy that exercises Kuhn's converse non-vacuously. -/
def twoStageCorrelated0 : stdSimplex ℝ (twoStageFEF.PureStrategy 0) :=
  ⟨fun s => if s = twoStagePureAll0 then 1/2 else if s = twoStagePureAll1 then 1/2 else 0, by
    refine ⟨fun s => ?_, ?_⟩
    · dsimp only; split_ifs <;> norm_num
    · -- The sum splits into the two point masses `1/2` (distinct supports), totalling `1`.
      have hsum : ∑ s : twoStageFEF.PureStrategy 0,
          (if s = twoStagePureAll0 then (1 : ℝ)/2 else if s = twoStagePureAll1 then 1/2 else 0) =
          (∑ s : twoStageFEF.PureStrategy 0, (if s = twoStagePureAll0 then (1 : ℝ)/2 else 0)) +
          (∑ s : twoStageFEF.PureStrategy 0, (if s = twoStagePureAll1 then (1 : ℝ)/2 else 0)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases h0 : s = twoStagePureAll0
        · subst h0
          rw [if_pos rfl, if_pos rfl, if_neg twoStagePureAll0_ne_pureAll1, add_zero]
        · rw [if_neg h0, if_neg h0, zero_add]
      rw [hsum, Finset.sum_ite_eq' Finset.univ twoStagePureAll0 (fun _ => (1 : ℝ)/2),
        Finset.sum_ite_eq' Finset.univ twoStagePureAll1 (fun _ => (1 : ℝ)/2),
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
      norm_num⟩

/-- The correlated mixed strategy profile on the strategic normalization: Player `0` plays the
correlated two-point mixture `twoStageCorrelated0`; player `1` (who never moves) plays its default
vertex. -/
def twoStageCorrelated : twoStagePR.toFiniteStrategicGame.MixedStrategy := fun (i : Fin 2) =>
  match i with
  | 0 => twoStageCorrelated0
  | 1 => stdSimplex.vertex (S := ℝ) (default : twoStagePR.PureStrategy 1)

/-- The behavioral strategy `behavioralFromMixed twoStageCorrelated` reconstructed from the
genuinely correlated (non-product) mixed strategy `twoStageCorrelated` is realization-equivalent
to `twoStageCorrelated`: they assign the same probability to every reachable terminal history.
This is exactly the case Kuhn's theorem is about — behavioral strategies cannot correlate across
information sets, yet the converse map recovers one whose realization probabilities match. -/
theorem mixed_realizes_behavioral_correlated :
    twoStagePR.toFiniteExtensiveForm.RealizationEquivalent
      (twoStagePR.toFiniteExtensiveForm.behavioralFromMixed twoStageCorrelated)
      twoStageCorrelated :=
  twoStagePR.mixed_realizes_behavioral twoStageCorrelated

/-! ## A numeric two-stage realization fact (Game.lean, Strategy.lean)

The single root-reach probability of the two-stage path `[1, 1]` under `twoStageσ` is the
*product* of the two stages' behavioral masses on event `1` — `1/2` at the root and `2/3` at the
obs-`2` info set. A bug that collapsed the two stages, or read the second-stage behavior from the
wrong info set, would get a different number. This is the concrete numeric heart of the two-stage
non-vacuity. -/

/-- At the root, `twoStageσ` plays `half = (1/2, 1/2)`, so event `1` has step probability `1/2`. -/
lemma twoStageσ_step_root_one : twoStageEF.stepProb twoStageσ [] (1 : Fin 2) = 1/2 := by
  rw [twoStageEF.stepProb_player twoStageσ (n := twoStageNode) twoStageTree_nodeKind_nil 1]
  have hread : ∀ c : Fin 2, (twoStageσ.playerBehavior [] twoStageTree_nodeKind_nil).val c
      = (half : stdSimplex ℝ (Fin 2)).val c := by
    intro c
    have hheq : HEq (twoStageσ.playerBehavior [] twoStageTree_nodeKind_nil)
        (twoStageσ 0 (twoStageEF.info.observe 0 [])) :=
      (cast_heq _ _).trans (twoStageσ.atHistory_player_heq twoStageTree_nodeKind_nil)
    have hchoice : (twoStageNode.Choice)
        = twoStageEF.info.iChoiceType 0 (twoStageEF.info.observe 0 []) := rfl
    rw [stdSimplex.heq_val hchoice _ _ hheq c]; rfl
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = (1 : Fin 2) then
    (twoStageσ.playerBehavior [] twoStageTree_nodeKind_nil).val c else 0) = 1 / 2
  rw [Fin.sum_univ_two, hread 0, hread 1]
  norm_num [half]

/-- At the obs-`2` info set `[1]`, `twoStageσ` plays `thirds = (1/3, 2/3)`, so event `1` has step
probability `2/3`. The second stage reads from a different information set (obs `2`) than the first,
which the single-info-set carrier cannot test. -/
lemma twoStageσ_step_one_one : twoStageEF.stepProb twoStageσ [1] (1 : Fin 2) = 2/3 := by
  rw [twoStageEF.stepProb_player twoStageσ (n := twoStageNode) (twoStageTree_nodeKind_single 1) 1]
  have hread : ∀ c : Fin 2, (twoStageσ.playerBehavior [1] (twoStageTree_nodeKind_single 1)).val c
      = (thirds : stdSimplex ℝ (Fin 2)).val c := by
    intro c
    have hheq : HEq (twoStageσ.playerBehavior [1] (twoStageTree_nodeKind_single 1))
        (twoStageσ 0 (twoStageEF.info.observe 0 [1])) :=
      (cast_heq _ _).trans (twoStageσ.atHistory_player_heq (twoStageTree_nodeKind_single 1))
    have hchoice : (twoStageNode.Choice)
        = twoStageEF.info.iChoiceType 0 (twoStageEF.info.observe 0 [1]) := rfl
    rw [stdSimplex.heq_val hchoice _ _ hheq c]; rfl
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = (1 : Fin 2) then
    (twoStageσ.playerBehavior [1] (twoStageTree_nodeKind_single 1)).val c else 0) = 2 / 3
  rw [Fin.sum_univ_two, hread 0, hread 1]
  norm_num [thirds]

/-- The root-reach probability of the path `[1, 1]` under `twoStageσ` is `1/2 · 2/3 = 1/3` — the
product of the two stages' behavioral masses on event `1`. A stage-collapsing bug or one reading
the second stage from the wrong info set would not produce `1/3`. -/
theorem reachProb_one_one_eq_third :
    reachProb twoStagePR.toExtensiveForm twoStageσ [1, 1] = 1/3 := by
  change reachProb twoStageEF twoStageσ [1, 1] = 1/3
  unfold reachProb ExtensiveForm.finitePrefixProb
  rw [ExtensiveForm.finitePrefixProbFrom_cons, ExtensiveForm.finitePrefixProbFrom_cons,
    ExtensiveForm.finitePrefixProbFrom_nil, List.nil_append,
    twoStageσ_step_root_one, twoStageσ_step_one_one]
  norm_num

end EconlibTest.GameTheory.ExtensiveFormKuhnTwoStage

end
