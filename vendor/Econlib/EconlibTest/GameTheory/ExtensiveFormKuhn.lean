/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibTest.GameTheory.ExtensiveFormCore
import Mathlib

/-!
# Extensive-Form Kuhn — Non-Vacuity Checks (Chunk 2)

Compile-time semantic witnesses for Kuhn's realization-equivalence theorem and its converse
(`Econlib.GameTheory.ExtensiveForm.{Kuhn, KuhnConverse, KuhnMaps, PathConsistency,
ReachInvariance}`). Kuhn's theorem maps a behavioral strategy to a mixed strategy (and back) so that
*realization probabilities agree*; the failure mode is a **behavioral/mixed direction reversal** —
the mixed image must be a genuine distribution (masses sum to one) and the round-trip must preserve
reach probabilities, not invert them.

These lemmas all live on `FiniteExtensiveForm` / `PerfectRecallFiniteExtensiveForm`, which carry a
*finite* observation type, so the perfect-information `FinitePerfectInfoTree` lift (whose
`Obs i = List E` is infinite) cannot host them. We reuse the hand-rolled one-decision finite
extensive form `oneShotFEF` from `ExtensiveFormCore` and bundle it with a perfect-recall witness to
obtain a `PerfectRecallFiniteExtensiveForm`.

## The carrier

`oneShotPR` is `oneShotFEF` (player 0 moves once over `Fin 2`, then the game terminates) bundled
with its perfect-recall witness. It is trivially perfect-recall: The only history where a player
moves is the root `[]` (player 0). The Kuhn round-trip is therefore "small" — a single information
set. *Cardinality caveat:* the *strategic-form* normalization has four pure profiles, not two:
`PureStrategy 0` has two values (player 0's two root choices), but `PureStrategy 1` is *also*
nontrivial — player 1's unreached info set falls back to the root `PureChoice`, so the total profile
sum `∑ s ∏ i …` ranges over `2 × 2 = 4` pure profiles. The numeric content of the witnesses below is
therefore meaningful only for *player 0*'s coordinate; player 1's strategic-form labels are spurious
root-choice fallbacks. The deeper multi-stage Kuhn realization equivalence (where behavioral ≠ mixed
in general) is documented as out of scope for this compile-only test.

## Failure modes caught

* **the mixed image is not a distribution** — `behavioralToMixed_total_sum_one` confirms the masses
  `∏ i, behavioralToMixed σ i (s i)` over pure profiles sum to one; a direction reversal that
  emitted un-normalized weights would fail;
* **realization probabilities disagree** — `mixed_realizes_behavioral` confirms the converse map
  (`behavioralFromMixed μ`) is realization-equivalent to `μ`, so the reach probabilities computed
  in the behavioral and mixed worlds coincide.
-/

noncomputable section

namespace EconlibTest.GameTheory.ExtensiveFormKuhn

open Econlib.GameTheory
open EconlibTest.GameTheory.ExtensiveFormCore
  (oneShotFEF oneShotTree oneShotTree_movesAt_iff oneShotRootNode oneShotTree_nodeKind_nil)

/-! ## The perfect-recall carrier -/

/-- `oneShotFEF` has perfect recall: The only mover history is the root `[]`, so the no-revisit and
action-recall clauses reduce to `[] = []`. (Re-derived here so this file does not depend on the SPE
file's copy.) -/
theorem oneShotFEF_isPerfectRecall : oneShotFEF.IsPerfectRecall := by
  -- Both moving histories are the root `[]`, so the experiences coincide by `rfl`.
  intro i h₁ h₂ _ _ hm₁ hm₂ _
  rw [((oneShotTree_movesAt_iff i h₁).mp hm₁).1, ((oneShotTree_movesAt_iff i h₂).mp hm₂).1]

/-- The one-decision game bundled with its perfect-recall witness — a
`PerfectRecallFiniteExtensiveForm`, the type Kuhn's realization equivalence consumes. -/
def oneShotPR : PerfectRecallFiniteExtensiveForm (Fin 2) (Fin 2) where
  toFiniteExtensiveForm := oneShotFEF
  perfectRecall := oneShotFEF_isPerfectRecall

/-- A concrete behavioral strategy on `oneShotFEF`: Every player plays the vertex on its default
info-set choice. (The Kuhn realization lemmas hold for *any* behavioral strategy, mixed or pure, so
a vertex strategy is a valid — and cheaply well-typed — carrier; total mixedness is not needed.) -/
def oneShotσ : oneShotFEF.BehavioralStrategy := fun i _ =>
  stdSimplex.vertex (S := ℝ) (default : oneShotFEF.info.iChoiceType i ())

/-! ## Chunk 2 — Node-local evaluation (KuhnMaps.lean) -/

/-- **`NodeKind.behaviorEval_nonneg`.** The per-choice behavior evaluation is nonnegative. -/
theorem behaviorEval_nonneg (b : (oneShotTree.nodeKind []).Behavior)
    (c : (oneShotTree.nodeKind []).PureChoice) :
    0 ≤ (oneShotTree.nodeKind []).behaviorEval b c :=
  NodeKind.behaviorEval_nonneg _ b c

/-- **`NodeKind.behaviorEval_sum_one`.** The per-choice behavior evaluations sum to one — the node
behavior is a genuine distribution over the node's pure choices. -/
theorem behaviorEval_sum_one (b : (oneShotTree.nodeKind []).Behavior) :
    ∑ c : (oneShotTree.nodeKind []).PureChoice, (oneShotTree.nodeKind []).behaviorEval b c = 1 :=
  NodeKind.behaviorEval_sum_one _ b

/-- **`behavioralToMixedFactor_nonneg`.** The mixed-strategy factor of `oneShotσ` for player 0 at a
pure strategy is nonnegative. -/
theorem behavioralToMixedFactor_nonneg (s : oneShotFEF.PureStrategy 0) :
    0 ≤ oneShotFEF.behavioralToMixedFactor oneShotσ 0 s () :=
  oneShotFEF.behavioralToMixedFactor_nonneg oneShotσ 0 s ()

/-- **`behavioralToMixedFactor_sum_one`.** The mixed-strategy factors of `oneShotσ` for player 0
sum to one over the info-set choices. -/
theorem behavioralToMixedFactor_sum_one :
    ∑ c : oneShotFEF.infoSetChoiceForObs 0 (),
      oneShotFEF.behavioralToMixedFactor oneShotσ 0
        (fun _ => c) () = 1 :=
  oneShotFEF.behavioralToMixedFactor_sum_one oneShotσ 0 ()

/-! ## Chunk 2 — The mixed image is a distribution (Kuhn.lean, headline) -/

/-- **`behavioralToMixed_total_sum_one`: The mixed image is a genuine distribution.** The product
masses `∏ i, behavioralToMixed σ i (s i)` of `oneShotσ` over all pure profiles `s` sum to one. This
is the non-vacuity heart of Kuhn's forward map: A behavioral strategy maps to a *bona fide* mixed
strategy. A behavioral/mixed direction reversal that emitted un-normalized weights would fail this.
(Note: the sum ranges over all `2 × 2 = 4` pure profiles, including player 1's spurious root-choice
fallbacks — see the cardinality caveat in the module header; normalization still holds because each
per-player factor is itself a distribution.) -/
theorem behavioralToMixed_total_sum_one :
    ∑ s : (i : Fin 2) → oneShotFEF.PureStrategy i,
      ∏ i : Fin 2, (oneShotFEF.behavioralToMixed oneShotσ i) (s i) = 1 :=
  oneShotFEF.behavioralToMixed_total_sum_one oneShotσ

/-! ## Chunk 2 — Node event probabilities (Kuhn.lean) -/

/-- **`NodeKind.eventProb_of_terminal`.** A terminal node emits no event with positive probability:
Its `eventProb` is `0`. -/
theorem eventProb_of_terminal (b : (NodeKind.terminal (I := Fin 2) (E := Fin 2) ![1, 2]).Behavior)
    (e : Fin 2) :
    (NodeKind.terminal (I := Fin 2) (E := Fin 2) ![1, 2]).eventProb b e = 0 :=
  NodeKind.eventProb_of_terminal rfl b e

/-- **`NodeKind.eventProb_of_player`.** At the root player node, the event probability of `e` is
the simplex mass of the choices emitting `e` — a genuine `if`-sum over `Fin 2` choices, not the
identically-zero terminal formula. We exercise the *named* lemma `NodeKind.eventProb_of_player`
(via `rw`, so a broken lemma would surface here) with `b := stdSimplex.vertex 0` and event `e := 0`:
Only choice `0` (which emits `0` under the identity embedding) contributes, so the probability is
`1`. -/
theorem eventProb_of_player_root_zero :
    (NodeKind.player oneShotRootNode).eventProb (stdSimplex.vertex (S := ℝ) (0 : Fin 2))
      (0 : Fin 2) = 1 := by
  rw [NodeKind.eventProb_of_player (n := oneShotRootNode) rfl]
  -- `eventProb` at a player node is `∑ c, if emit c = e then b-mass else 0`.
  change (∑ c : Fin 2, if (Function.Embedding.refl (Fin 2)) c = (0 : Fin 2) then
    (stdSimplex.vertex (S := ℝ) (0 : Fin 2) : Fin 2 → ℝ) c else 0) = 1
  rw [Fin.sum_univ_two]
  rw [if_pos (show (Function.Embedding.refl (Fin 2)) 0 = 0 from rfl),
    if_neg (show (Function.Embedding.refl (Fin 2)) 1 ≠ 0 by decide)]
  rw [stdSimplex.vertex_apply_self]; norm_num

/-- A concrete finite chance node over `Fin 2`: nature draws outcome `k` with the *asymmetric*
distribution `(1/3, 2/3)` and emits event `k` (identity emitter). The asymmetry makes the two events
distinguishable, so the `eventProb` witness below has an anchor a swapped lookup would miss. -/
def oneShotChance : ChanceFiniteNode (Fin 2) where
  Outcome := Fin 2
  dist :=
    ⟨![1 / 3, 2 / 3],
      by intro a; fin_cases a <;>
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons],
      by rw [Fin.sum_univ_two]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]⟩
  emit := id

/-- **`NodeKind.eventProb_of_chanceFinite`.** At a finite chance node the event probability of `e`
is nature's mass on the outcomes emitting `e` — `∑ ω, if emit ω = e then dist ω else 0`. We exercise
the *named* lemma (via `rw`) on `oneShotChance`: under the identity emitter only outcome `0` emits
event `0`, so its probability is the mass `1/3` — distinct from the `2/3` carried by event `1`, so
an outcome/mass mismatch would surface here. -/
theorem eventProb_of_chanceFinite_zero
    (b : (NodeKind.chanceFinite (I := Fin 2) oneShotChance).Behavior) :
    (NodeKind.chanceFinite (I := Fin 2) oneShotChance).eventProb b (0 : Fin 2) = 1 / 3 := by
  rw [NodeKind.eventProb_of_chanceFinite (n := oneShotChance) rfl]
  -- `oneShotChance.Outcome` is `Fin 2` definitionally; align the binder for `Fin.sum_univ_two`.
  change
    (∑ ω : Fin 2, if oneShotChance.emit ω = (0 : Fin 2) then oneShotChance.dist ω else 0) = 1 / 3
  rw [Fin.sum_univ_two,
    if_pos (show oneShotChance.emit (0 : Fin 2) = (0 : Fin 2) from rfl),
    if_neg (show oneShotChance.emit (1 : Fin 2) ≠ (0 : Fin 2) by decide), add_zero]
  -- `oneShotChance.dist.pmf 0` reduces to the first vector entry `1/3` definitionally.
  rfl

/-! ## Chunk 2 — KuhnConverse weights (KuhnConverse.lean) -/

/-- A concrete mixed-strategy profile on the strategic-form normalization: Each player plays the
vertex on its default pure strategy. -/
def oneShotμ : (i : Fin 2) → ↑(stdSimplex ℝ (oneShotFEF.PureStrategy i)) := fun _ =>
  stdSimplex.vertex (S := ℝ) (default : oneShotFEF.PureStrategy _)

/-- **`reachPlayWeight_nonneg`.** The reach-play weight (mass that player `i`'s mixed strategy
plays into the info-set choice `c` while reaching it) is nonnegative. -/
theorem reachPlayWeight_nonneg (c : oneShotFEF.infoSetChoiceForObs 0 ()) :
    0 ≤ oneShotFEF.reachPlayWeight oneShotμ 0 () c :=
  oneShotFEF.reachPlayWeight_nonneg oneShotμ 0 () c

/-- **`reachWeight_nonneg`.** The total reach weight of player 0's info set is nonnegative. -/
theorem reachWeight_nonneg :
    0 ≤ oneShotFEF.reachWeight oneShotμ 0 () :=
  oneShotFEF.reachWeight_nonneg oneShotμ 0 ()

/-- **`sum_reachPlayWeight_eq_reachWeight`.** Summing the per-choice reach-play weights over the
info-set choices recovers the total reach weight — the weight decomposition is exact. -/
theorem sum_reachPlayWeight_eq_reachWeight :
    ∑ c : oneShotFEF.infoSetChoiceForObs 0 (), oneShotFEF.reachPlayWeight oneShotμ 0 () c =
      oneShotFEF.reachWeight oneShotμ 0 () :=
  oneShotFEF.sum_reachPlayWeight_eq_reachWeight oneShotμ 0 ()

/-- **`condPlaySimplex_val_mul_reachWeight`.** The conditional-play simplex value times the total
reach weight equals the reach-play weight — the defining factorization that makes the converse map
realization-equivalent. -/
theorem condPlaySimplex_val_mul_reachWeight (c : oneShotFEF.infoSetChoiceForObs 0 ()) :
    (oneShotFEF.condPlaySimplex oneShotμ 0 () : _ → ℝ) c * oneShotFEF.reachWeight oneShotμ 0 () =
      oneShotFEF.reachPlayWeight oneShotμ 0 () c :=
  oneShotFEF.condPlaySimplex_val_mul_reachWeight oneShotμ 0 () c

/-! ## Chunk 2 — The converse endpoint (KuhnConverse.lean)

`mixed_realizes_behavioral` is the converse direction of Kuhn: The behavioral strategy
reconstructed from a mixed strategy `μ` realizes the *same* reach probabilities as `μ`. This is the
witness that the round-trip does not invert reach probabilities. -/

/-- A mixed strategy on the strategic-form normalization of `oneShotPR`: Each player's default-pure
vertex. -/
def oneShotMixed : oneShotPR.toFiniteStrategicGame.MixedStrategy := fun _ =>
  stdSimplex.vertex (S := ℝ) (default : oneShotPR.PureStrategy _)

/-- **`mixed_realizes_behavioral`: The converse realization endpoint.** The behavioral strategy
`behavioralFromMixed oneShotMixed` reconstructed from the mixed strategy `oneShotMixed` is
realization-equivalent to `oneShotMixed` — reach probabilities agree both ways. *Caveat:*
`oneShotMixed` is the *default-vertex* mixed strategy, whose realized terminal probabilities are the
degenerate `[0] ↦ 1, [1] ↦ 0`; this witness exercises the equivalence *map's well-typedness and
endpoint* but would still pass if the map ignored its input (since the default vertex is a fixed
point of the round-trip). The genuine *asymmetric* event-probability discrimination (`1/3` vs `2/3`,
distinguishing event labels) is exercised in `ExtensiveFormCore.lean`
(`asymEventProb_root_zero_eq_third` / `_one_eq_two_thirds`). -/
theorem mixed_realizes_behavioral_witness :
    oneShotPR.RealizationEquivalent (oneShotPR.behavioralFromMixed oneShotMixed) oneShotMixed :=
  oneShotPR.mixed_realizes_behavioral oneShotMixed

/-- **`behavioral_realizes_mixed`: The forward realization endpoint.** Dually, the forward map
`behavioralToMixed` is realization-equivalent to the original behavioral strategy — the *other*
direction of the round-trip, confirming reach probabilities agree forwards too. *Same caveat as the
converse:* `oneShotσ` is the default-vertex behavioral strategy (degenerate realization
`[0] ↦ 1, [1] ↦ 0`), so this is an endpoint/well-typedness check, not a non-degenerate
input-sensitivity test. -/
theorem behavioral_realizes_mixed_witness :
    oneShotPR.RealizationEquivalent oneShotσ (oneShotPR.behavioralToMixed oneShotσ) :=
  oneShotPR.behavioral_realizes_mixed oneShotσ

/-! ## Chunk 2 — Path consistency and reach invariance

(`PathConsistency.lean`, `ReachInvariance.lean`) -/

/-- A default pure strategy for player 0, used to exercise the path-consistency indicators. -/
def oneShotPure0 : oneShotFEF.PureStrategy 0 := default

/-- **`iStepIndicator_nonneg`.** The single-step path-consistency indicator is nonnegative. -/
theorem iStepIndicator_nonneg (h : List (Fin 2)) (e : Fin 2) :
    0 ≤ oneShotFEF.iStepIndicator 0 oneShotPure0 h e :=
  oneShotFEF.iStepIndicator_nonneg 0 oneShotPure0 h e

/-- **`iPathConsistent_nonneg`.** Player 0's path-consistency weight along any history is
nonnegative. -/
theorem iPathConsistent_nonneg (h : List (Fin 2)) :
    0 ≤ oneShotFEF.iPathConsistent 0 oneShotPure0 h :=
  oneShotFEF.iPathConsistent_nonneg 0 oneShotPure0 h

/-- **`iPathConsistentFrom_append`.** Path consistency factorizes over concatenation — the
indicator of `path₁ ++ path₂` from `h_start` is the product of the two segment indicators. The
defining multiplicativity that makes the realization factorization work. -/
theorem iPathConsistentFrom_append (h_start path₁ path₂ : List (Fin 2)) :
    oneShotFEF.iPathConsistentFrom 0 oneShotPure0 h_start (path₁ ++ path₂) =
      oneShotFEF.iPathConsistentFrom 0 oneShotPure0 h_start path₁ *
        oneShotFEF.iPathConsistentFrom 0 oneShotPure0 (h_start ++ path₁) path₂ :=
  oneShotFEF.iPathConsistentFrom_append 0 oneShotPure0 h_start path₁ path₂

/-- **`realization_factor`** (general form). The behavioral reach probability factorizes as the
chance-only weight times the product over players of their realization marginals — the realization
identity that underlies reach invariance. Stated for an arbitrary reachable `h`; the *concrete*
reachability discharge at `[0]` is `realization_factor_zero` below (the reachability hypothesis is
supplied, not assumed). -/
theorem realization_factor (h : List (Fin 2)) (hr : h ∈ oneShotFEF.reach) :
    reachProb oneShotPR.toExtensiveForm oneShotσ h =
      oneShotFEF.chanceWeight h * ∏ j : Fin 2, oneShotFEF.iMarginal oneShotσ j h :=
  FiniteExtensiveForm.realization_factor oneShotPR oneShotσ h hr

/-- **`realization_factor`, at the concrete reachable history `[0]`.** The reachability hypothesis
is *discharged* via `oneShotFEF_zero_mem_reach` (player 0's choice `0` leads there), not assumed —
so this is the realization identity on genuine concrete data, not a re-export of the library
contract. -/
theorem realization_factor_zero :
    reachProb oneShotPR.toExtensiveForm oneShotσ [0] =
      oneShotFEF.chanceWeight [0] * ∏ j : Fin 2, oneShotFEF.iMarginal oneShotσ j [0] :=
  FiniteExtensiveForm.realization_factor oneShotPR oneShotσ [0]
    EconlibTest.GameTheory.ExtensiveFormCore.oneShotFEF_zero_mem_reach

/-- **`iMarginal_repr_invariant`** (type instantiation only). For the moving player, the realization
marginal is the same at any two reachable histories in the same information set — representative
independence, the action-recall content. *Degeneracy caveat:* on `oneShotFEF` the `movesAt 0`
hypotheses force `x = x' = []` (the only mover history), so the conclusion is representative
equality
*at the same history* — this confirms the lemma instantiates and type-checks on a perfect-recall
carrier, but does **not** test genuine representative independence (which needs two distinct moving
histories in one info set, i.e. a richer multi-stage carrier). -/
theorem iMarginal_repr_invariant
    (σ : oneShotPR.toExtensiveForm.BehavioralStrategy)
    (x x' : List (Fin 2)) (hx : x ∈ oneShotFEF.reach)
    (hx' : x' ∈ oneShotFEF.reach)
    (hmx : (oneShotPR.toExtensiveForm.tree.nodeKind x).movesAt 0)
    (hmx' : (oneShotPR.toExtensiveForm.tree.nodeKind x').movesAt 0)
    (hobs : oneShotPR.toExtensiveForm.info.observe 0 x =
      oneShotPR.toExtensiveForm.info.observe 0 x') :
    oneShotFEF.iMarginal σ 0 x = oneShotFEF.iMarginal σ 0 x' :=
  FiniteExtensiveForm.iMarginal_repr_invariant oneShotPR oneShotFEF_isPerfectRecall.actionRecall
    0 σ x x' hx hx' hmx hmx' hobs

/-- **`reachProb_infoSet_invariant_unilateral`** (type instantiation only). A unilateral
`0`-deviation rescales the reach probability of every node in a fixed information set by the *same*
factor (cross-multiplied form). This is the realization-equivalence core that lets the one-shot
inequality compose across info sets. *Degeneracy caveat:* on `oneShotFEF` the `movesAt 0`
hypotheses force `x = x' = []`, and `reachProb σ [] = 1` for every strategy, so the cross-multiplied
equality reduces to `1 · 1 = 1 · 1` and the unilateral-deviation hypothesis is irrelevant. This
confirms the lemma instantiates on a perfect-recall carrier but does not test same-factor rescaling
across two distinct nodes of an information set (which needs a richer carrier). -/
theorem reachProb_infoSet_invariant_unilateral
    (σ σ' : oneShotFEF.toExtensiveForm.BehavioralStrategy)
    (hdev : oneShotFEF.toExtensiveForm.unilateralDeviation 0 σ σ')
    (ω : Unit) (x x' : List (Fin 2))
    (hx_reach : x ∈ oneShotFEF.reach) (hx'_reach : x' ∈ oneShotFEF.reach)
    (hx : (oneShotFEF.toExtensiveForm.tree.nodeKind x).movesAt 0 ∧
      oneShotFEF.toExtensiveForm.info.observe 0 x = ω)
    (hx' : (oneShotFEF.toExtensiveForm.tree.nodeKind x').movesAt 0 ∧
      oneShotFEF.toExtensiveForm.info.observe 0 x' = ω) :
    reachProb oneShotFEF.toExtensiveForm σ' x * reachProb oneShotFEF.toExtensiveForm σ x' =
      reachProb oneShotFEF.toExtensiveForm σ' x' * reachProb oneShotFEF.toExtensiveForm σ x :=
  Econlib.GameTheory.reachProb_infoSet_invariant_unilateral oneShotFEF oneShotFEF_isPerfectRecall
    0 σ σ' hdev ω x x' hx_reach hx'_reach hx hx'

end EconlibTest.GameTheory.ExtensiveFormKuhn

end
