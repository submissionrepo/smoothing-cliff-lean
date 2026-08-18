/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Tree
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Behavioral strategies on extensive forms

A **behavioral strategy** (Kuhn 1953) is an information-set-indexed function assigning, at each
information set, an independent distribution over the choices available there. This file defines
behavioral strategies as functions from `(player, observation)` pairs to distributions over the
declared choice type at that information set. Because the carrier has no history parameter, a
behavioral strategy cannot depend on information beyond a player's observation, so the
information-set respecting requirement holds by construction.

The `atHistory` API projects an information-set strategy to the node-local behavior at a concrete
history, with `simplexTransport` bridging the `Fintype`-instance mismatch between `iChoiceTypeAt`
and `iChoiceType`. The file also defines reach probabilities, total mixedness, the
unilateral-deviation relation, and a behavioral-strategy builder for perfect-information forms.

## Main definitions

* `simplexTransport`: Transport a simplex element across a type equality.
* `ExtensiveForm.BehavioralStrategy`: Information-set-indexed behavioral strategy.
* `ExtensiveForm.BehavioralStrategy.atHistory`: Node-local behavior induced at a history.
* `ExtensiveForm.stepProb`: One-step finite-prefix probability.
* `ExtensiveForm.finitePrefixProbFrom`: Finite-suffix reach probability.
* `ExtensiveForm.IsTotallyMixed`: Total mixedness of a behavioral strategy.
* `ExtensiveForm.unilateralDeviation`: Canonical extensive-form unilateral-deviation relation.
* `ExtensiveForm.BehavioralStrategy.ofPerfectInfo`: Behavioral strategy for a perfect-information
  form built from a per-history behavior assignment.

## Main statements

* `simplexTransport_heq`: A transported simplex is heterogeneously equal to the original.
* `ExtensiveForm.BehavioralStrategy.atHistory_*_heq`: Constructor-specific characterizations of
  `atHistory` at a node of known kind.
* `ExtensiveForm.finitePrefixProbFrom_append`: Finite-prefix probability factors along a path
  concatenation.
* `ExtensiveForm.BehavioralStrategy.atHistory_congr_movers`: `atHistory` depends on the strategy
  only through the moving players' coordinates.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, behavioral strategy, reach probability
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

/-- Transport a simplex element across a type equality `h : α = β`. The underlying function `α → ℝ`
transports directly; the sum-to-one property is re-derived in the target `Fintype`, which is
propositionally equal to the source one on the shared carrier. This localizes the
`Fintype`-instance mismatch arising inside `BehavioralStrategy.atHistory`. -/
noncomputable def simplexTransport {α β : Type u} [instA : Fintype α] [instB : Fintype β]
    (h : α = β) (s : stdSimplex ℝ α) : stdSimplex ℝ β := by
  subst h
  -- The two `Fintype` instances on `α` are propositionally equal, so the simplex constraint
  -- transports after aligning them.
  cases Subsingleton.elim instA instB
  exact s

/-- A transported simplex is heterogeneously equal to the original: `simplexTransport` preserves
the underlying function, and the target `Fintype` instance is propositionally equal, so the bundled
subtypes coincide up to `HEq`. -/
theorem simplexTransport_heq {α β : Type u} [instA : Fintype α] [instB : Fintype β]
    (h : α = β) (s : stdSimplex ℝ α) : HEq (simplexTransport h s) s := by
  subst h
  cases Subsingleton.elim instA instB
  unfold simplexTransport; rfl

namespace ExtensiveForm

variable {I E : Type u}

/-- A **behavioral strategy**: An information-set-indexed function from `(player, observation)` to
a simplex over the declared choice type at that information set. Information-set respect holds by
construction, since the carrier has no history parameter and so a strategy cannot depend on
information beyond the player's observation. -/
def BehavioralStrategy (G : ExtensiveForm I E) : Type u :=
  (i : I) → (obs : G.info.Obs i) → stdSimplex ℝ (G.info.iChoiceType i obs)

/-- Per-history behavior obtained from a behavioral strategy together with an explicit proof that
the node kind at `h` equals a particular `k`. Taking `k` as a free parameter (rather than matching
on the discriminant `G.tree.nodeKind h` directly) lets each per-constructor branch reduce once `k`
is fixed, which is what the `atHistory_*_heq` characterizations below exploit. -/
noncomputable def BehavioralStrategy.atHistoryAux {G : ExtensiveForm I E}
    (σ : G.BehavioralStrategy) (h : List E) :
    (k : NodeKind I E) → (hk : G.tree.nodeKind h = k) → k.Behavior
  | .terminal _, _ => PUnit.unit
  | .player n, hk => by
      have hm : (G.tree.nodeKind h).movesAt n.mover := by rw [hk]; rfl
      have hcompat : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm =
          G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
        G.iChoice_compatible n.mover h hm
      have hbridge : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm = n.Choice := by
        clear hcompat
        revert hm
        rw [hk]
        intro _
        rfl
      have heq : G.info.iChoiceType n.mover (G.info.observe n.mover h) = n.Choice :=
        hcompat.symm.trans hbridge
      exact simplexTransport heq (σ n.mover (G.info.observe n.mover h))
  | .joint n, hk => by
      intro a
      let i : I := n.player a
      have hm : (G.tree.nodeKind h).movesAt i := by rw [hk]; exact ⟨a, rfl⟩
      have hcompat : (G.tree.nodeKind h).iChoiceTypeAt i hm =
          G.info.iChoiceType i (G.info.observe i h) :=
        G.iChoice_compatible i h hm
      have hbridge : (G.tree.nodeKind h).iChoiceTypeAt i hm = n.Choice a := by
        clear hcompat
        revert hm
        rw [hk]
        intro hm'
        change n.Choice (n.iPosition i hm') = n.Choice a
        congr 1
        apply n.player_injective
        rw [n.iPosition_player i hm']
      have heq : G.info.iChoiceType i (G.info.observe i h) = n.Choice a :=
        hcompat.symm.trans hbridge
      exact simplexTransport heq (σ i (G.info.observe i h))
  | .chanceFinite _, _ => PUnit.unit
  | .chanceGeneral _, _ => PUnit.unit

/-- Per-history behavior obtained from a behavioral strategy. The dependent case analysis is
delegated to `atHistoryAux`, which takes the node kind as an explicit parameter so that each
per-branch reduction holds by `rfl` (see the `atHistory_*_heq` kit below). -/
noncomputable def BehavioralStrategy.atHistory {G : ExtensiveForm I E}
    (σ : G.BehavioralStrategy) (h : List E) : (G.tree.nodeKind h).Behavior :=
  σ.atHistoryAux h (G.tree.nodeKind h) rfl

/-! ### `atHistory` characterizations at a known node kind

Given `hk : G.tree.nodeKind h = .ctor n`, the following heterogeneous-equality lemmas (one per
`NodeKind` constructor) commit `atHistory` to the corresponding branch: `PUnit.unit` at terminal
and chance nodes, the mover's local distribution at a player node, and the per-active-player
distributions at a joint node. -/

/-- HEq congruence for `atHistoryAux`: Substituting an equal discriminant gives an HEq value. -/
theorem BehavioralStrategy.atHistoryAux_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) (h : List E)
    {k1 k2 : NodeKind I E} (hk_eq : k1 = k2)
    (hk1 : G.tree.nodeKind h = k1) (hk2 : G.tree.nodeKind h = k2) :
    HEq (σ.atHistoryAux h k1 hk1) (σ.atHistoryAux h k2 hk2) := by
  subst hk_eq; rfl

theorem BehavioralStrategy.atHistory_terminal_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) {h : List E} {payoff : I → ℝ}
    (hk : G.tree.nodeKind h = .terminal payoff) :
    HEq (σ.atHistory h) (PUnit.unit : PUnit) :=
  (σ.atHistoryAux_heq h hk rfl hk).trans (HEq.refl _)

theorem BehavioralStrategy.atHistory_chanceFinite_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) {h : List E}
    {n : ChanceFiniteNode E} (hk : G.tree.nodeKind h = .chanceFinite n) :
    HEq (σ.atHistory h) (PUnit.unit : PUnit) :=
  (σ.atHistoryAux_heq h hk rfl hk).trans (HEq.refl _)

theorem BehavioralStrategy.atHistory_chanceGeneral_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) {h : List E}
    {n : ChanceGeneralNode E} (hk : G.tree.nodeKind h = .chanceGeneral n) :
    HEq (σ.atHistory h) (PUnit.unit : PUnit) :=
  (σ.atHistoryAux_heq h hk rfl hk).trans (HEq.refl _)

theorem BehavioralStrategy.atHistory_player_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) {h : List E} {n : PlayerNode I E}
    (hk : G.tree.nodeKind h = .player n) :
    HEq (σ.atHistory h) (σ n.mover (G.info.observe n.mover h)) :=
  (σ.atHistoryAux_heq h hk rfl hk).trans (simplexTransport_heq _ _)

theorem BehavioralStrategy.atHistory_joint_heq
    {G : ExtensiveForm I E} (σ : G.BehavioralStrategy) {h : List E} {n : JointNode I E}
    (hk : G.tree.nodeKind h = .joint n) :
    HEq (σ.atHistory h)
        (fun (a : n.Active) => σ (n.player a) (G.info.observe (n.player a) h)) := by
  refine (σ.atHistoryAux_heq h hk rfl hk).trans (Function.hfunext rfl ?_)
  intro a a' ha
  cases eq_of_heq ha
  exact simplexTransport_heq _ _

/-- One-step finite-prefix probability. -/
noncomputable def stepProb (G : ExtensiveForm I E) [DecidableEq E] (σ : G.BehavioralStrategy)
    (h : List E) (e : E) : ℝ :=
  (G.tree.nodeKind h).eventProb (σ.atHistory h) e

/-- Probability of a finite continuation suffix from a current public history. -/
noncomputable def finitePrefixProbFrom (G : ExtensiveForm I E) [DecidableEq E]
    (σ : G.BehavioralStrategy) :
    List E → List E → ℝ
  | _h, [] => 1
  | h, e :: suffix =>
      G.stepProb σ h e * G.finitePrefixProbFrom σ (h ++ [e]) suffix

/-- Probability of a finite public history from the root. -/
noncomputable def finitePrefixProb (G : ExtensiveForm I E) [DecidableEq E]
    (σ : G.BehavioralStrategy) (h : List E) : ℝ :=
  G.finitePrefixProbFrom σ [] h

/-- A behavioral strategy is totally mixed if every (player, observation) component puts positive
probability on every legal choice in the declared `iChoiceType`. -/
def IsTotallyMixed (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) : Prop :=
  ∀ i obs c, 0 < (σ i obs).val c

/-- The canonical unilateral-deviation relation for extensive forms: `σ'` is an `i`-deviation of
`σ` iff they agree on every (player, observation) coordinate where the player is not `i`. -/
def unilateralDeviation (G : ExtensiveForm I E) (i : I) (σ σ' : G.BehavioralStrategy) : Prop :=
  ∀ j obs, j ≠ i → σ' j obs = σ j obs

@[simp] lemma finitePrefixProbFrom_nil (G : ExtensiveForm I E) [DecidableEq E]
    (σ : G.BehavioralStrategy) (h : List E) :
    G.finitePrefixProbFrom σ h [] = 1 := rfl

@[simp] lemma finitePrefixProbFrom_cons (G : ExtensiveForm I E) [DecidableEq E]
    (σ : G.BehavioralStrategy) (h : List E) (e : E) (suffix : List E) :
    G.finitePrefixProbFrom σ h (e :: suffix) =
      G.stepProb σ h e * G.finitePrefixProbFrom σ (h ++ [e]) suffix := rfl

end ExtensiveForm

namespace ExtensiveForm

variable {I E : Type u}

/-- Build a `BehavioralStrategy` for the perfect-information form of a tree from any per-history
behavior assignment. The lift extracts `iLocalBehavior` from `σ h` at each `(player, obs)` info set
and transports through the total-vs-partial bridge. -/
noncomputable def BehavioralStrategy.ofPerfectInfo [DecidableEq I] {t : GameTree I E}
    (σ : (h : List E) → (t.nodeKind h).Behavior) :
    (ofGameTreePerfectInfo t).BehavioralStrategy := by
  intro i obs
  by_cases hm : (t.nodeKind obs).movesAt i
  · have heq : (t.nodeKind obs).iChoiceTypeAt i hm = (t.nodeKind obs).iChoiceTypeAt' i :=
      (NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ _ hm).symm
    exact simplexTransport heq ((t.nodeKind obs).iLocalBehavior i hm (σ obs))
  · exact stdSimplex.vertex (default : (t.nodeKind obs).iChoiceTypeAt' i)

end ExtensiveForm

/-! ## Reach-probability tower and mover-restricted congruence

Multiplicative factorization of finite-prefix probabilities along a path concatenation,
nonnegativity of the step and prefix probabilities, and the fact that a node's step probability
depends on the strategy only through its moving players' coordinates. -/

variable {I E : Type u} [DecidableEq E]
/-- **Reach tower.** The finite-prefix probability of a concatenated continuation factors:
Following `pre` then `suf` from `start` has probability
`P(pre from start) · P(suf from start ++ pre)`. -/
theorem ExtensiveForm.finitePrefixProbFrom_append (G : ExtensiveForm I E)
    (σ : G.BehavioralStrategy) (start pre suf : List E) :
    G.finitePrefixProbFrom σ start (pre ++ suf) =
      G.finitePrefixProbFrom σ start pre * G.finitePrefixProbFrom σ (start ++ pre) suf := by
  induction pre generalizing start with
  | nil => simp
  | cons e rest ih =>
    have hlist : start ++ [e] ++ rest = start ++ (e :: rest) := by
      rw [List.append_assoc]; rfl
    rw [List.cons_append, G.finitePrefixProbFrom_cons, G.finitePrefixProbFrom_cons,
      ih (start ++ [e]), hlist]
    ring

/-- Each one-step factor `stepProb` is an `eventProb` of a simplex/chance distribution, hence
nonnegative (by `NodeKind.eventProb_nonneg`). -/
theorem ExtensiveForm.stepProb_nonneg (G : ExtensiveForm I E) (σ : G.BehavioralStrategy)
    (h : List E) (e : E) : 0 ≤ G.stepProb σ h e :=
  NodeKind.eventProb_nonneg _ _ _

/-- A finite-prefix continuation probability is a product of nonnegative `stepProb` factors, hence
nonnegative. -/
theorem ExtensiveForm.finitePrefixProbFrom_nonneg (G : ExtensiveForm I E) (σ : G.BehavioralStrategy)
    (start suf : List E) : 0 ≤ G.finitePrefixProbFrom σ start suf := by
  induction suf generalizing start with
  | nil => simp
  | cons e rest ih =>
    rw [G.finitePrefixProbFrom_cons]
    exact mul_nonneg (G.stepProb_nonneg σ start e) (ih (start ++ [e]))

omit [DecidableEq E] in
/-- `atHistory` reads the strategy only at the moving players' coordinates: Agreement at every
`(j, observe j h)` with `j` a mover at `h` forces equal node-local behavior. This refines
`atHistory_congr`, whose hypothesis quantifies over all players. -/
theorem BehavioralStrategy.atHistory_congr_movers (G : ExtensiveForm I E)
    (σ τ : G.BehavioralStrategy) (h : List E)
    (hagree : ∀ j : I, (G.tree.nodeKind h).movesAt j →
      σ j (G.info.observe j h) = τ j (G.info.observe j h)) :
    σ.atHistory h = τ.atHistory h := by
  -- Mirror `atHistoryAux_congr`, with the kind made explicit so the per-branch reductions fire and
  -- only the moving-coordinate agreement is consumed.
  have aux : ∀ (k : NodeKind I E) (hk : G.tree.nodeKind h = k),
      σ.atHistoryAux h k hk = τ.atHistoryAux h k hk := by
    intro k hk
    cases k with
    | terminal _ => rfl
    | player n =>
        have hm : (G.tree.nodeKind h).movesAt n.mover := by rw [hk]; rfl
        simp only [ExtensiveForm.BehavioralStrategy.atHistoryAux, hagree n.mover hm]
    | joint n =>
        refine funext fun a => ?_
        have hm : (G.tree.nodeKind h).movesAt (n.player a) := by rw [hk]; exact ⟨a, rfl⟩
        simp only [ExtensiveForm.BehavioralStrategy.atHistoryAux, hagree (n.player a) hm]
    | chanceFinite _ => rfl
    | chanceGeneral _ => rfl
  exact aux (G.tree.nodeKind h) rfl

/-- `stepProb` reads the strategy only at the moving players' coordinates. -/
theorem stepProb_congr_movers (G : ExtensiveForm I E)
    (σ τ : G.BehavioralStrategy) (h : List E) (e : E)
    (hagree : ∀ j : I, (G.tree.nodeKind h).movesAt j →
      σ j (G.info.observe j h) = τ j (G.info.observe j h)) :
    G.stepProb σ h e = G.stepProb τ h e := by
  unfold ExtensiveForm.stepProb
  rw [BehavioralStrategy.atHistory_congr_movers G σ τ h hagree]

/-- `finitePrefixProbFrom` reads the strategy only at the intermediate nodes of the walk: If two
strategies have equal step probabilities at `start ++ pre` for every proper prefix `pre` of `suf`,
their prefix probabilities from `start` along `suf` agree. -/
theorem ExtensiveForm.finitePrefixProbFrom_congr (G : ExtensiveForm I E)
    (ρ ρ' : G.BehavioralStrategy) (start suf : List E)
    (hag : ∀ pre : List E, pre <+: suf → pre ≠ suf →
      ∀ e : E, G.stepProb ρ (start ++ pre) e = G.stepProb ρ' (start ++ pre) e) :
    G.finitePrefixProbFrom ρ start suf = G.finitePrefixProbFrom ρ' start suf := by
  induction suf generalizing start with
  | nil => rw [G.finitePrefixProbFrom_nil, G.finitePrefixProbFrom_nil]
  | cons e rest ih =>
    rw [G.finitePrefixProbFrom_cons ρ, G.finitePrefixProbFrom_cons ρ']
    have hhead := hag [] List.nil_prefix (by simp) e
    rw [List.append_nil] at hhead
    rw [hhead]
    congr 1
    refine ih (start ++ [e]) (fun pre hpre hne e' => ?_)
    have hassoc : start ++ [e] ++ pre = start ++ (e :: pre) := by
      rw [List.append_assoc]; rfl
    rw [hassoc]
    refine hag (e :: pre) (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩) ?_ e'
    intro hcc
    injection hcc with _ h2
    exact hne h2

end Econlib.GameTheory
