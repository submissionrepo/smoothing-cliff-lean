/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Problem
public import Econlib.GameTheory.ExtensiveForm.Core.Reachable
public import Econlib.GameTheory.ExtensiveForm.Core.Strategy

/-!
# Extensive games and subgame-perfect equilibrium

`ExtensiveGame I E` extends `ExtensiveForm I E` (Kuhn 1953) with a `continuationValue` evaluator
together with a Bellman contract fixing its semantics. The contract has two layers: A unified
Bellman equation `continuationValue_eq` requiring the continuation value at every history to equal
the node-local recursion `nodeStepValue` over the kind at that history (folding a per-step reward
`stepPayoff` and a common discount `discount`), and a uniqueness side condition
`continuationValue_unique` (finite depth, or a strict discount with a uniform value bound).

`ExtensiveGame.ofFiniteHorizonTree` constructs a canonical `ExtensiveGame` on any finite-depth,
no-general-chance `ExtensiveForm`, deriving `continuationValue` from the recursive evaluator
`ExtensiveForm.recursiveContinuationValue`. This is the workhorse for finite-horizon builders.

The deviation relation is fixed on the `ExtensiveForm` side (`unilateralDeviation`), so subgame
perfection uses the canonical predicate rather than a builder-supplied relation.

## Main definitions

* `ExtensiveForm.FiniteDepth N`: Every history of length `≥ N` is terminal.
* `ExtensiveForm.BehavioralStrategy.playerBehavior` / `jointBehavior`: Cast `atHistory` onto the
  player- or joint-node simplex given equality evidence.
* `nodeStepValue`: Node-local one-step value, case-split on `NodeKind`.
* `ExtensiveForm.recursiveContinuationValue`: Well-founded continuation value on a finite-depth
  form with stage payoff `0` and discount `1`.
* `ExtensiveGame`: Extensive form with continuation-value evaluator, stage payoff, discount, the
  unified Bellman, and the uniqueness side condition.
* `ExtensiveGame.ofFiniteHorizonTree`: Canonical `ExtensiveGame` on a finite-depth, no-general-
  chance form.
* `ExtensiveGame.spePred`: Equilibrium problem for subgame perfection.
* `ExtensiveGame.IsSubgamePerfectEquilibrium`: Canonical predicate for subgame-perfect equilibrium.

## Main statements

* `nodeStepValue_terminal` / `_player` / `_joint` / `_chanceFinite`: Per-branch reductions.

## Notes

The Bellman equation alone underdetermines the continuation value: It admits spurious fixed points
(e.g. `V σ h i = discount ^ (-h.length)`, unbounded when `discount < 1`). Each disjunct of
`continuationValue_unique` is incompatible with such a fixed point — finite depth bottoms the
recursion out at terminal payoffs, and a strict discount makes the step a contraction on bounded
values — so a spurious game is unconstructible. See the `ExtensiveGame` structure docstring.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, subgame perfection, equilibrium, Bellman
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

/-! ### Cast σ.atHistory onto a kind-specific Behavior -/

namespace ExtensiveForm

variable {I E : Type u}

/-- A finite-depth bound on an extensive form: Every history of length `≥ N` is terminal. -/
def FiniteDepth (G : ExtensiveForm I E) (N : ℕ) : Prop :=
  ∀ h : List E, N ≤ h.length → ∃ p : I → ℝ, G.tree.nodeKind h = .terminal p

/-- Cast `σ.atHistory h` onto a player node's simplex, given evidence the node at `h` matches. -/
noncomputable def BehavioralStrategy.playerBehavior {G : ExtensiveForm I E}
    (σ : G.BehavioralStrategy) (h : List E) {n : PlayerNode I E}
    (hnk : G.tree.nodeKind h = .player n) : stdSimplex ℝ n.Choice :=
  cast (congrArg NodeKind.Behavior hnk) (σ.atHistory h)

/-- Cast `σ.atHistory h` onto a joint node's product simplex, given matching evidence. -/
noncomputable def BehavioralStrategy.jointBehavior {G : ExtensiveForm I E}
    (σ : G.BehavioralStrategy) (h : List E) {n : JointNode I E}
    (hnk : G.tree.nodeKind h = .joint n) :
    (a : n.Active) → stdSimplex ℝ (n.Choice a) :=
  cast (congrArg NodeKind.Behavior hnk) (σ.atHistory h)

/-- **Locality of `atHistoryAux`.** The node-local behavior at `h` depends on the strategy only
through its values at the observations player `h`'s movers induce. If two strategies agree at every
`(j, observe j h)` coordinate, their `atHistoryAux` outputs coincide (for the same kind
evidence). -/
theorem BehavioralStrategy.atHistoryAux_congr {G : ExtensiveForm I E}
    (σ τ : G.BehavioralStrategy) (h : List E)
    (hagree : ∀ j : I, σ j (G.info.observe j h) = τ j (G.info.observe j h))
    (k : NodeKind I E) (hk : G.tree.nodeKind h = k) :
    σ.atHistoryAux h k hk = τ.atHistoryAux h k hk := by
  cases k with
  | terminal _ => rfl
  | player n => simp only [BehavioralStrategy.atHistoryAux, hagree n.mover]
  | joint n => exact funext fun a => by simp only [BehavioralStrategy.atHistoryAux, hagree _]
  | chanceFinite _ => rfl
  | chanceGeneral _ => rfl

/-- **Locality of `atHistory`.** Two strategies agreeing at every `(j, observe j h)` coordinate
induce the same node-local behavior at `h`. -/
theorem BehavioralStrategy.atHistory_congr {G : ExtensiveForm I E}
    (σ τ : G.BehavioralStrategy) (h : List E)
    (hagree : ∀ j : I, σ j (G.info.observe j h) = τ j (G.info.observe j h)) :
    σ.atHistory h = τ.atHistory h :=
  σ.atHistoryAux_congr τ h hagree (G.tree.nodeKind h) rfl

/-- `playerBehavior` is local: Agreement of the strategies at `h`'s coordinates forces equal player
behavior. -/
theorem BehavioralStrategy.playerBehavior_congr {G : ExtensiveForm I E}
    (σ τ : G.BehavioralStrategy) (h : List E) {n : PlayerNode I E}
    (hnk : G.tree.nodeKind h = .player n)
    (hagree : ∀ j : I, σ j (G.info.observe j h) = τ j (G.info.observe j h)) :
    σ.playerBehavior h hnk = τ.playerBehavior h hnk := by
  unfold BehavioralStrategy.playerBehavior
  rw [σ.atHistory_congr τ h hagree]

/-- `jointBehavior` is local: Agreement of the strategies at `h`'s coordinates forces equal joint
behavior. -/
theorem BehavioralStrategy.jointBehavior_congr {G : ExtensiveForm I E}
    (σ τ : G.BehavioralStrategy) (h : List E) {n : JointNode I E}
    (hnk : G.tree.nodeKind h = .joint n)
    (hagree : ∀ j : I, σ j (G.info.observe j h) = τ j (G.info.observe j h)) :
    σ.jointBehavior h hnk = τ.jointBehavior h hnk := by
  unfold BehavioralStrategy.jointBehavior
  rw [σ.atHistory_congr τ h hagree]

end ExtensiveForm

/-! ### `nodeStepValue`: Node-local Bellman step

Indexed by the node kind `nk` and an equality `hnk : G.tree.nodeKind h = nk`. The equality is
the evidence that licenses transporting `σ.atHistory h` onto the kind-specific Behavior. Pattern-
matching on `nk` (a variable) rather than on `G.tree.nodeKind h` means each per-constructor
specialization reduces by `rfl`, giving the four reduction simp lemmas below. -/

/-- Node-local one-step value at history `h`: The terminal payoff at terminal nodes; the expected
`(stepPayoff + discount · V on continuations)` sum at non-terminal nodes. The kind argument carries
`hng`, a proof that it is not a general-chance node, so the general-chance branch is unreachable by
construction (`absurd`) rather than a placeholder value — there is no `0` to leak. A consumer that
wants a general-chance node must supply the missing integral Bellman; until then the kind is
inexpressible here. The whole-tree machinery discharges `hng` once via
`ExtensiveGame.no_chanceGeneral` (or `recursiveContinuationValue`'s `hNG`). -/
noncomputable def nodeStepValue {I E : Type u}
    (G : ExtensiveForm I E)
    (σ : G.BehavioralStrategy) (h : List E) (i : I)
    (nk : NodeKind I E) (hnk : G.tree.nodeKind h = nk)
    (hng : ∀ n : ChanceGeneralNode E, nk ≠ .chanceGeneral n)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) : ℝ :=
  match nk, hnk, hng with
  | .terminal p, _, _ => p i
  | .player n, hnk, _ =>
      ∑ c : n.Choice,
        (σ.playerBehavior h hnk).val c *
          (stepPayoff h (n.emit c) i + discount * V σ (h ++ [n.emit c]) i)
  | .joint n, hnk, _ =>
      ∑ c : (a : n.Active) → n.Choice a,
        (∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a)) *
          (stepPayoff h (n.emit c) i + discount * V σ (h ++ [n.emit c]) i)
  | .chanceFinite n, _, _ =>
      ∑ ω : n.Outcome,
        n.dist ω *
          (stepPayoff h (n.emit ω) i + discount * V σ (h ++ [n.emit ω]) i)
  | .chanceGeneral n, _, hng => absurd rfl (hng n)

/-- `nodeStepValue` at a terminal node is the realized payoff `p i`. -/
@[simp] lemma nodeStepValue_terminal {I E : Type u}
    (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (h : List E) (i : I) (p : I → ℝ)
    (hnk : G.tree.nodeKind h = .terminal p)
    (hng : ∀ n : ChanceGeneralNode E, (NodeKind.terminal p : NodeKind I E) ≠ .chanceGeneral n)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.terminal p) hnk hng stepPayoff discount V = p i := rfl

/-- `nodeStepValue` at a player node is the simplex-weighted sum over choices of the immediate
reward plus discounted continuation value at the emitted child. -/
@[simp] lemma nodeStepValue_player {I E : Type u}
    (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (h : List E) (i : I) (n : PlayerNode I E)
    (hnk : G.tree.nodeKind h = .player n)
    (hng : ∀ m : ChanceGeneralNode E, (NodeKind.player n : NodeKind I E) ≠ .chanceGeneral m)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.player n) hnk hng stepPayoff discount V =
      ∑ c : n.Choice,
        (σ.playerBehavior h hnk).val c *
          (stepPayoff h (n.emit c) i + discount * V σ (h ++ [n.emit c]) i) := rfl

/-- `nodeStepValue` at a joint node is the product-simplex-weighted sum over profiles of the
immediate reward plus discounted continuation value at the emitted child. -/
@[simp] lemma nodeStepValue_joint {I E : Type u}
    (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (h : List E) (i : I) (n : JointNode I E)
    (hnk : G.tree.nodeKind h = .joint n)
    (hng : ∀ m : ChanceGeneralNode E, (NodeKind.joint n : NodeKind I E) ≠ .chanceGeneral m)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.joint n) hnk hng stepPayoff discount V =
      ∑ c : (a : n.Active) → n.Choice a,
        (∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a)) *
          (stepPayoff h (n.emit c) i + discount * V σ (h ++ [n.emit c]) i) := rfl

/-- `nodeStepValue` at a finite chance node is nature's distribution-weighted sum over outcomes of
the immediate reward plus discounted continuation value at the emitted child. -/
@[simp] lemma nodeStepValue_chanceFinite {I E : Type u}
    (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (h : List E) (i : I)
    (n : ChanceFiniteNode E) (hnk : G.tree.nodeKind h = .chanceFinite n)
    (hng : ∀ m : ChanceGeneralNode E, (NodeKind.chanceFinite n : NodeKind I E) ≠ .chanceGeneral m)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.chanceFinite n) hnk hng stepPayoff discount V =
      ∑ ω : n.Outcome,
        n.dist ω *
          (stepPayoff h (n.emit ω) i + discount * V σ (h ++ [n.emit ω]) i) := rfl

/-- **Locality of `nodeStepValue`.** If two strategies agree at `h`'s coordinates (forcing equal
node-local weights) and induce equal child values at every emitted continuation, their node-step
values coincide. The case-split is on the explicit `nk`/`hnk` parameters, so the dependent kind
evidence is handled without a motive. -/
lemma nodeStepValue_congr {I E : Type u}
    (G : ExtensiveForm I E) (σ τ : G.BehavioralStrategy) (h : List E) (i : I)
    (nk : NodeKind I E) (hnk : G.tree.nodeKind h = nk)
    (hng : ∀ n : ChanceGeneralNode E, nk ≠ .chanceGeneral n)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ)
    (hbeh : ∀ j : I, σ j (G.info.observe j h) = τ j (G.info.observe j h))
    (hchild : ∀ e : E, V σ (h ++ [e]) i = V τ (h ++ [e]) i) :
    nodeStepValue G σ h i nk hnk hng stepPayoff discount V =
      nodeStepValue G τ h i nk hnk hng stepPayoff discount V := by
  cases nk with
  | terminal p => rfl
  | player n =>
      rw [nodeStepValue_player _ _ _ _ _ hnk, nodeStepValue_player _ _ _ _ _ hnk,
        σ.playerBehavior_congr τ h hnk hbeh]
      exact Finset.sum_congr rfl fun c _ => by rw [hchild (n.emit c)]
  | joint n =>
      rw [nodeStepValue_joint _ _ _ _ _ hnk, nodeStepValue_joint _ _ _ _ _ hnk,
        σ.jointBehavior_congr τ h hnk hbeh]
      exact Finset.sum_congr rfl fun c _ => by rw [hchild (n.emit c)]
  | chanceFinite n =>
      rw [nodeStepValue_chanceFinite _ _ _ _ _ hnk, nodeStepValue_chanceFinite _ _ _ _ _ hnk]
      exact Finset.sum_congr rfl fun ω _ => by rw [hchild (n.emit ω)]
  | chanceGeneral n => rfl

/-! ### Event-regrouped Bellman

`nodeStepValue` at a player/joint node sums over per-choice simplex weights, but the child term
depends on the choice only through the emitted event. Regrouping the per-choice sum by emitted
event collapses the weight of each event class to its `eventProb = stepProb`. This is the form in
which the Bellman is continuous in the step-probability profile (the per-choice weights are not). -/

namespace ExtensiveForm

variable {I E : Type u} (G : ExtensiveForm I E) [DecidableEq E]

/-- `stepProb` at a terminal history is zero. -/
lemma stepProb_of_terminal (σ : G.BehavioralStrategy)
    {h : List E} {payoff : I → ℝ} (hnk : G.tree.nodeKind h = .terminal payoff) (e : E) :
    G.stepProb σ h e = 0 := by
  rw [stepProb, NodeKind.eventProb_cast hnk (σ.atHistory h) e]
  rfl

/-- `stepProb` at a player node is the simplex mass of the choices emitting `e`. -/
lemma stepProb_player (σ : G.BehavioralStrategy) {h : List E} {n : PlayerNode I E}
    (hnk : G.tree.nodeKind h = .player n) (e : E) :
    G.stepProb σ h e =
      ∑ c : n.Choice, if n.emit c = e then (σ.playerBehavior h hnk).val c else 0 := by
  rw [stepProb, NodeKind.eventProb_cast hnk (σ.atHistory h) e]
  rfl

/-- `stepProb` at a joint node is the product-simplex mass of the profiles emitting `e`. -/
lemma stepProb_joint (σ : G.BehavioralStrategy) {h : List E} {n : JointNode I E}
    (hnk : G.tree.nodeKind h = .joint n) (e : E) :
    G.stepProb σ h e =
      ∑ c : (a : n.Active) → n.Choice a,
        if n.emit c = e then ∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a) else 0 := by
  rw [stepProb, NodeKind.eventProb_cast hnk (σ.atHistory h) e]
  rfl

/-- `stepProb` at a finite chance node is nature's event mass. -/
lemma stepProb_of_chanceFinite (σ : G.BehavioralStrategy)
    {h : List E} {n : ChanceFiniteNode E} (hnk : G.tree.nodeKind h = .chanceFinite n) (e : E) :
    G.stepProb σ h e =
      ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0 := by
  rw [stepProb, NodeKind.eventProb_cast hnk (σ.atHistory h) e]
  rfl

/-- **Event-regrouped Bellman, general per-choice form.** A per-choice weighted sum whose summand
depends on the choice only through a "tag" `g c` regroups as a sum over the tags in the image, with
each tag weighted by the total mass of its fiber. The abstract step underlying the player/joint
event regroupings. -/
lemma sum_choice_eq_sum_tag {C : Type u} [Fintype C] (g : C → E)
    (w : C → ℝ) (F : E → ℝ) :
    ∑ c : C, w c * F (g c) =
      ∑ e ∈ Finset.univ.image g, (∑ c : C, if g c = e then w c else 0) * F e := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image g)
        (fun c _ => Finset.mem_image_of_mem g (Finset.mem_univ c)) (fun c => w c * F (g c))]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases hc : g c = e <;> simp [hc]

/-- **Event-regrouped Bellman at a player node.** Regroup the per-choice sum by emitted event: Each
event class carries weight `stepProb σ h e`, independent of the per-choice split. -/
lemma nodeStepValue_player_eventSum (σ : G.BehavioralStrategy) (h : List E) (i : I)
    {n : PlayerNode I E} (hnk : G.tree.nodeKind h = .player n)
    (hng : ∀ m : ChanceGeneralNode E, (NodeKind.player n : NodeKind I E) ≠ .chanceGeneral m)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.player n) hnk hng stepPayoff discount V =
      ∑ e ∈ Finset.univ.image n.emit,
        G.stepProb σ h e * (stepPayoff h e i + discount * V σ (h ++ [e]) i) := by
  rw [nodeStepValue_player _ _ _ _ _ hnk,
    sum_choice_eq_sum_tag (E := E) n.emit (fun c => (σ.playerBehavior h hnk).val c)
      (fun e => stepPayoff h e i + discount * V σ (h ++ [e]) i)]
  exact Finset.sum_congr rfl (fun e _ => by rw [G.stepProb_player σ hnk e])

/-- **Event-regrouped Bellman at a joint node.** Same regrouping, with profile masses summed over
each event class to `stepProb σ h e`. -/
lemma nodeStepValue_joint_eventSum (σ : G.BehavioralStrategy) (h : List E) (i : I)
    {n : JointNode I E} (hnk : G.tree.nodeKind h = .joint n)
    (hng : ∀ m : ChanceGeneralNode E, (NodeKind.joint n : NodeKind I E) ≠ .chanceGeneral m)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ) :
    nodeStepValue G σ h i (.joint n) hnk hng stepPayoff discount V =
      ∑ e ∈ Finset.univ.image n.emit,
        G.stepProb σ h e * (stepPayoff h e i + discount * V σ (h ++ [e]) i) := by
  rw [nodeStepValue_joint _ _ _ _ _ hnk,
    sum_choice_eq_sum_tag (E := E) n.emit
      (fun c => ∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a))
      (fun e => stepPayoff h e i + discount * V σ (h ++ [e]) i)]
  exact Finset.sum_congr rfl (fun e _ => by rw [G.stepProb_joint σ hnk e])

/-- **Continuity of `nodeStepValue` in the step-probability profile.** With the general-chance kind
excluded, the node-step value is a finite event sum (terminal: Constant; interior: The regrouped
`stepProb`-weighted sum) of products of convergent step probabilities and convergent child values,
so it converges. The case-split is on the explicit `nk`/`hnk` parameters, avoiding a dependent
kind-evidence motive. -/
lemma nodeStepValue_tendsto (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy)
    (h : List E) (i : I) (nk : NodeKind I E) (hnk : G.tree.nodeKind h = nk)
    (stepPayoff : List E → E → I → ℝ) (discount : ℝ)
    (V : G.BehavioralStrategy → List E → I → ℝ)
    (hno : ∀ nG : ChanceGeneralNode E, nk ≠ .chanceGeneral nG)
    (hstep : ∀ e, Filter.Tendsto (fun n => G.stepProb (σseq n) h e)
      Filter.atTop (nhds (G.stepProb σ h e)))
    (hchild : ∀ e, Filter.Tendsto (fun n => V (σseq n) (h ++ [e]) i)
      Filter.atTop (nhds (V σ (h ++ [e]) i))) :
    Filter.Tendsto (fun n => nodeStepValue G (σseq n) h i nk hnk hno stepPayoff discount V)
      Filter.atTop (nhds (nodeStepValue G σ h i nk hnk hno stepPayoff discount V)) := by
  have hterm : ∀ e : E, Filter.Tendsto
      (fun n => stepPayoff h e i + discount * V (σseq n) (h ++ [e]) i)
      Filter.atTop (nhds (stepPayoff h e i + discount * V σ (h ++ [e]) i)) := fun e =>
    (tendsto_const_nhds).add ((hchild e).const_mul discount)
  cases nk with
  | terminal p =>
      simp only [nodeStepValue_terminal]
      exact tendsto_const_nhds
  | player n =>
      simp only [nodeStepValue_player_eventSum _ _ _ _ hnk]
      exact tendsto_finset_sum _ (fun e _ => (hstep e).mul (hterm e))
  | joint n =>
      simp only [nodeStepValue_joint_eventSum _ _ _ _ hnk]
      exact tendsto_finset_sum _ (fun e _ => (hstep e).mul (hterm e))
  | chanceFinite n =>
      -- Chance weights `n.dist ω` are constant; the child term converges by `hchild`.
      simp only [nodeStepValue_chanceFinite _ _ _ _ _ hnk]
      exact tendsto_finset_sum _ (fun ω _ => (hterm (n.emit ω)).const_mul (n.dist ω))
  | chanceGeneral nG => exact absurd rfl (hno nG)

end ExtensiveForm

/-! ### Recursive continuation value on finite-depth forms

The well-founded recursion measures the gap `N - h.length`. The auxiliary form
`recursiveContinuationValueAux` takes `nk` and `hnk : G.tree.nodeKind h = nk` as explicit
parameters; the wrapper `recursiveContinuationValue` invokes the auxiliary with
`(G.tree.nodeKind h, rfl)`. This auxiliary pattern sidesteps the annotated-match elaboration that
resists `generalize`. -/

namespace ExtensiveForm

variable {I E : Type u}

/-- Auxiliary form of `recursiveContinuationValue` taking the node kind `nk` and the equality
`hnk : G.tree.nodeKind h = nk` as parameters. The well-founded measure is `N - h.length`.

`hNG` rules out general-chance nodes at every history, making the evaluator faithful: The
`.chanceGeneral` branch is discharged as impossible rather than silently returning `0` (which would
be a semantic falsehood, not an integral over outcomes). A consumer cannot invoke this evaluator on
a form that actually contains a general-chance node. -/
noncomputable def recursiveContinuationValueAux
    (G : ExtensiveForm I E) {N : ℕ} (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (σ : G.BehavioralStrategy) (i : I) :
    (h : List E) → (nk : NodeKind I E) → (hnk : G.tree.nodeKind h = nk) → ℝ
  | h, nk, hnk =>
    if hguard : N ≤ h.length then
      (Classical.choose (hFD h hguard)) i
    else
      match nk, hnk with
      | .terminal p, _ => p i
      | .player n, hnk =>
          ∑ c : n.Choice,
            (σ.playerBehavior h hnk).val c *
              recursiveContinuationValueAux G hFD hNG σ i (h ++ [n.emit c])
                (G.tree.nodeKind (h ++ [n.emit c])) rfl
      | .joint n, hnk =>
          ∑ c : (a : n.Active) → n.Choice a,
            (∏ a : n.Active, (σ.jointBehavior h hnk a).val (c a)) *
              recursiveContinuationValueAux G hFD hNG σ i (h ++ [n.emit c])
                (G.tree.nodeKind (h ++ [n.emit c])) rfl
      | .chanceFinite n, _ =>
          ∑ ω : n.Outcome,
            n.dist ω * recursiveContinuationValueAux G hFD hNG σ i (h ++ [n.emit ω])
              (G.tree.nodeKind (h ++ [n.emit ω])) rfl
      | .chanceGeneral nG, hnk => (hNG h nG hnk).elim
termination_by h _ _ => N - h.length
decreasing_by
  all_goals
    simp only [List.length_append, List.length_singleton]
    omega

/-- Recursive continuation value on a finite-depth extensive form. Uses `stepPayoff = 0` and
`discount = 1`, so the value at a history is the expected terminal payoff over the subtree rooted
at it. `hNG` requires no general-chance nodes, ensuring the recursion is faithful at every chance
node (see `recursiveContinuationValueAux`). -/
noncomputable def recursiveContinuationValue
    (G : ExtensiveForm I E) {N : ℕ} (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (σ : G.BehavioralStrategy) (h : List E) (i : I) : ℝ :=
  recursiveContinuationValueAux G hFD hNG σ i h (G.tree.nodeKind h) rfl

end ExtensiveForm

/-! ### `ExtensiveGame`: Contract -/

/-- An extensive game: An `ExtensiveForm` together with a `continuationValue` evaluator and a
Bellman contract. The unilateral-deviation relation is fixed once and for all by
`ExtensiveForm.unilateralDeviation`, which encodes the "agree on every non-`i` info-set" predicate.
This allows subgame perfection to be derived via `spePred` rather than supplied per game.

Two fields carry the semantics. `continuationValue_eq` is the unified Bellman: At every history the
value equals the node-local step `nodeStepValue`, folding the per-step reward `stepPayoff` and the
common `discount`. Because the Bellman alone underdetermines the value (the local recursion admits
spurious fixed points, such as `V σ h i = discount ^ (-h.length)`, unbounded when `discount < 1`),
the side condition `continuationValue_unique` requires that each disjunct is incompatible with the
Bellman holding at a spurious value, so requiring it makes a spurious-fixed-point game
unconstructible —

* *finite depth* (left): The Bellman bottoms out at terminal payoffs and determines the value by
  reverse recursion, so nothing but the canonical value satisfies it;
* *strict discount + uniform bound* (right): The Bellman step is a `discount`-contraction on
  bounded values, so Banach gives a unique bounded fixed point — and the spurious example is
  unbounded.

The remaining fields are routine: `discount_mem` keeps `discount ∈ [0, 1]`, and `no_chanceGeneral`
closes the chance-node semantic hole (the Bellman places a placeholder `0` at general-chance
histories). -/
structure ExtensiveGame (I : Type u) (E : Type u) extends ExtensiveForm I E where
  /-- Per-step immediate reward, keyed by `(history, emitted event, player)`. Zero for terminal-
  payoff games; equals `(1 - δ) · u_i(a)` for repeated games. -/
  stepPayoff : List E → E → I → ℝ
  /-- Common discount factor. `1` for finite-horizon games; `δ ∈ [0, 1)` for repeated games. -/
  discount : ℝ
  /-- The discount factor lies in `[0, 1]`. -/
  discount_mem : discount ∈ Set.Icc (0 : ℝ) 1
  /-- No general-chance nodes (the histories where the Bellman places its placeholder `0`). Re-open
  with an integral Bellman if a concrete consumer requires them. -/
  no_chanceGeneral : ∀ h : List E, ∀ n : ChanceGeneralNode E,
    toExtensiveForm.tree.nodeKind h ≠ .chanceGeneral n
  /-- Continuation value under a behavioral strategy after a finite public history. -/
  continuationValue : toExtensiveForm.BehavioralStrategy → List E → I → ℝ
  /-- Unified Bellman: At every history the continuation value equals the node-local Bellman step,
  folding `stepPayoff` and `discount`. -/
  continuationValue_eq :
    ∀ σ h i,
      continuationValue σ h i =
        nodeStepValue toExtensiveForm σ h i
          (toExtensiveForm.tree.nodeKind h) rfl (no_chanceGeneral h)
          stepPayoff discount continuationValue
  /-- Uniqueness side condition: Finite depth (left) or strict discount with a uniform value bound
  (right). Either disjunct, together with `continuationValue_eq`, determines `continuationValue`;
  see the structure docstring for why. -/
  continuationValue_unique :
    (∃ N : ℕ, toExtensiveForm.FiniteDepth N) ∨
      (discount < 1 ∧ ∃ M : ℝ, ∀ σ h i, |continuationValue σ h i| ≤ M)

namespace ExtensiveGame

variable {I E : Type u}

/-- The equilibrium problem associated with subgame perfection of an `ExtensiveGame`. The swap
relation is the canonical `ExtensiveForm.unilateralDeviation`, not a builder-supplied field. -/
def spePred (G : ExtensiveGame I E) : EquilibriumProblem where
  S := G.toExtensiveForm.BehavioralStrategy
  I := I × List E
  swap := fun p σ τ => G.toExtensiveForm.unilateralDeviation p.1 σ τ
  value := fun p σ => G.continuationValue σ p.2 p.1

/-- Subgame-perfection: No profitable unilateral deviation by any player at any public history. -/
def IsSubgamePerfectEquilibrium
    (G : ExtensiveGame I E) (σ : G.toExtensiveForm.BehavioralStrategy) : Prop :=
  G.spePred.IsEquilibrium σ

end ExtensiveGame

/-! ### `ofFiniteHorizonTree`: Canonical builder

Discharges the contract by `recursiveContinuationValue`: `stepPayoff := 0`, `discount := 1`,
and the unified Bellman is the definitional unfolding of the recursion. Uniqueness is via the
finite-depth disjunct. -/

namespace ExtensiveGame

variable {I E : Type u}

/-- The unfolding lemma for `recursiveContinuationValueAux`, case-split on the explicit `nk`
parameter. -/
lemma recursiveContinuationValueAux_eq
    (G : ExtensiveForm I E) {N : ℕ} (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (σ : G.BehavioralStrategy) (h : List E) (i : I)
    (nk : NodeKind I E) (hnk : G.tree.nodeKind h = nk) :
    G.recursiveContinuationValueAux hFD hNG σ i h nk hnk =
      nodeStepValue G σ h i nk hnk (hnk ▸ hNG h)
        (fun _ _ _ => 0) 1 (G.recursiveContinuationValue hFD hNG) := by
  have hRec : ∀ h', G.recursiveContinuationValue hFD hNG σ h' i =
      G.recursiveContinuationValueAux hFD hNG σ i h' (G.tree.nodeKind h') rfl := fun _ => rfl
  -- At depth ≥ N every node is terminal by `hFD`, so a non-terminal kind at `h` gives a
  -- contradiction.
  have hFloor : ∀ {nk' : NodeKind I E}, (∀ p, nk' ≠ .terminal p) →
      N ≤ h.length → G.tree.nodeKind h = nk' → False := by
    intro nk' hnt hguard hnk'
    obtain ⟨p, hp⟩ := hFD h hguard
    exact absurd (hnk'.symm.trans hp) (hnt p)
  cases nk with
  | terminal p =>
      rw [nodeStepValue_terminal]
      rw [ExtensiveForm.recursiveContinuationValueAux]
      split_ifs with hguard
      · -- Floor: `Classical.choose (hFD h hguard) = p` from `hnk` together with the choice spec.
        rw [NodeKind.terminal.inj ((Classical.choose_spec (hFD h hguard)).symm.trans hnk)]
      · rfl
  | player n =>
      rw [ExtensiveForm.recursiveContinuationValueAux]
      split_ifs with hguard
      · exact (hFloor (by simp) hguard hnk).elim
      · rw [nodeStepValue_player]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hRec (h ++ [n.emit c])]
        ring
  | joint n =>
      rw [ExtensiveForm.recursiveContinuationValueAux]
      split_ifs with hguard
      · exact (hFloor (by simp) hguard hnk).elim
      · rw [nodeStepValue_joint]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [hRec (h ++ [n.emit c])]
        ring
  | chanceFinite n =>
      rw [ExtensiveForm.recursiveContinuationValueAux]
      split_ifs with hguard
      · exact (hFloor (by simp) hguard hnk).elim
      · rw [nodeStepValue_chanceFinite]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [hRec (h ++ [n.emit ω])]
        ring
  | chanceGeneral nG =>
      exact absurd hnk (hNG h nG)

/-- The unified Bellman for `recursiveContinuationValue`. -/
lemma recursiveContinuationValue_eq
    (G : ExtensiveForm I E) {N : ℕ} (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (σ : G.BehavioralStrategy) (h : List E) (i : I) :
    G.recursiveContinuationValue hFD hNG σ h i =
      nodeStepValue G σ h i (G.tree.nodeKind h) rfl (hNG h)
        (fun _ _ _ => 0) 1 (G.recursiveContinuationValue hFD hNG) :=
  recursiveContinuationValueAux_eq G hFD hNG σ h i (G.tree.nodeKind h) rfl

/-- Canonical `ExtensiveGame` on a finite-depth, no-general-chance `ExtensiveForm`. Sets
`stepPayoff := 0` and `discount := 1`; `continuationValue` is `recursiveContinuationValue`. -/
noncomputable def ofFiniteHorizonTree
    {N : ℕ} (G : ExtensiveForm I E) (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n) :
    ExtensiveGame I E where
  toExtensiveForm := G
  stepPayoff := fun _ _ _ => 0
  discount := 1
  discount_mem := ⟨zero_le_one, le_refl _⟩
  no_chanceGeneral := hNG
  continuationValue := G.recursiveContinuationValue hFD hNG
  continuationValue_eq σ h i := recursiveContinuationValue_eq G hFD hNG σ h i
  continuationValue_unique := Or.inl ⟨N, hFD⟩

/-- The `continuationValue` field of `ofFiniteHorizonTree` is `recursiveContinuationValue`. -/
@[simp] lemma ofFiniteHorizonTree_continuationValue
    {N : ℕ} (G : ExtensiveForm I E) (hFD : G.FiniteDepth N)
    (hNG : ∀ h : List E, ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (σ : G.BehavioralStrategy) (h : List E) (i : I) :
    (ofFiniteHorizonTree G hFD hNG).continuationValue σ h i =
      G.recursiveContinuationValue hFD hNG σ h i := rfl

end ExtensiveGame

/-! ## Continuation-value locality and continuity; emitted-children frontier

Locality and step-probability continuity of `continuationValue`, the player-node Bellman step
as a sum over emitted events, and the emitted-children frontier (`emitImage`, `childrenOf`) of a
node together with its pushed transition weight. -/

variable {I E : Type u} [DecidableEq E]
omit [DecidableEq E] in
/-- **Locality of `continuationValue`.** If two strategies prescribe the same behavior at every
history extending `h` (for every player, at the observation that history induces), they induce the
same continuation value at `h`. Play off the continuation cone of `h` is irrelevant. -/
theorem ExtensiveGame.continuationValue_congr (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (σ τ : G.toExtensiveForm.BehavioralStrategy)
    (h : List E) (i : I)
    (hagree : ∀ (g : List E), h <+: g →
      ∀ j : I, σ j (G.info.observe j g) = τ j (G.info.observe j g)) :
    G.continuationValue σ h i = G.continuationValue τ h i := by
  -- Induction on the depth budget `k ≥ N - h.length`, generalizing the history so the recursion
  -- can step into children (whose continuation cone is a sub-cone of `h`'s).
  suffices haux : ∀ (k : ℕ) (h' : List E), N - h'.length ≤ k →
      (∀ (g : List E), h' <+: g →
        ∀ j : I, σ j (G.info.observe j g) = τ j (G.info.observe j g)) →
      G.continuationValue σ h' i = G.continuationValue τ h' i from
    haux (N - h.length) h le_rfl hagree
  intro k
  induction k with
  | zero =>
    intro h' hk _hag
    have hge : N ≤ h'.length := by omega
    obtain ⟨p, hp⟩ := hfd h' hge
    rw [G.continuationValue_eq σ h' i, G.continuationValue_eq τ h' i]
    simp only [hp, nodeStepValue_terminal]
  | succ k ih =>
    intro h' _hk hag
    -- Agreement at `h'` itself (the `g = h'` instance) drives the weight equality.
    have hag_h' : ∀ j : I, σ j (G.info.observe j h') = τ j (G.info.observe j h') :=
      hag h' (List.prefix_refl h')
    rw [G.continuationValue_eq σ h' i, G.continuationValue_eq τ h' i]
    -- The child-agreement hypothesis, restricted to continuations of a child `h' ++ [e]`, lifts the
    -- IH to every emitted child (whose history is longer, so still within the budget `k`).
    refine nodeStepValue_congr G.toExtensiveForm σ τ h' i _ rfl (G.no_chanceGeneral h') _ _ _
      hag_h' (fun e => ?_)
    refine ih (h' ++ [e]) (by simp only [List.length_append, List.length_singleton]; omega)
      (fun g hg j => hag g ((List.prefix_append h' [e]).trans hg) j)

/-- **Continuity of `continuationValue` in the step-probability profile.** On a finite-depth form
(with no general-chance nodes), the continuation value at every history is a finite polynomial in
the per-node step probabilities, so step-probability convergence forces continuation-value
convergence.

The hypothesis `hstep` gives convergence of `stepProb = eventProb` (probability of an emitted event
`e`). This suffices because `nodeStepValue` can be regrouped as an `eventProb`-weighted sum over
emitted events: Even when `emit` is non-injective, the per-choice weights need not converge
individually, but their fiber sums (`stepProb`) do, and the child values and payoffs depend on each
choice only through its emitted event. -/
theorem ExtensiveGame.continuationValue_tendsto (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (σseq : ℕ → G.toExtensiveForm.BehavioralStrategy)
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => G.toExtensiveForm.stepProb (σseq n) h e)
      Filter.atTop (nhds (G.toExtensiveForm.stepProb σ h e)))
    (h : List E) (i : I) :
    Filter.Tendsto (fun n => G.continuationValue (σseq n) h i) Filter.atTop
      (nhds (G.continuationValue σ h i)) := by
  -- Induction on the depth budget `k ≥ N - h.length`, generalizing the history so each child
  -- `h' ++ [e]` (longer, still within the budget) admits the IH.
  suffices haux : ∀ (k : ℕ) (h' : List E), N - h'.length ≤ k →
      Filter.Tendsto (fun n => G.continuationValue (σseq n) h' i) Filter.atTop
        (nhds (G.continuationValue σ h' i)) from
    haux (N - h.length) h le_rfl
  intro k
  induction k with
  | zero =>
    intro h' hk
    have hge : N ≤ h'.length := by omega
    obtain ⟨p, hp⟩ := hfd h' hge
    have hconst : ∀ τ : G.toExtensiveForm.BehavioralStrategy,
        G.continuationValue τ h' i = p i := fun τ => by
      rw [G.continuationValue_eq τ h' i]; simp only [hp, nodeStepValue_terminal]
    simp only [hconst]
    exact tendsto_const_nhds
  | succ k ih =>
    intro h' _hk
    simp only [G.continuationValue_eq]
    refine G.toExtensiveForm.nodeStepValue_tendsto σseq σ h' i _ rfl _ _ _
      (fun nG => G.no_chanceGeneral h' nG) (fun e => hstep h' e) (fun e => ?_)
    exact ih (h' ++ [e]) (by simp only [List.length_append, List.length_singleton]; omega)

/-- **Player-node Bellman as an event sum.** Specializes the unified Bellman `continuationValue_eq`
at a player node `y` to the event-regrouped form `∑ₑ stepProb σ y e · (stepPayoff + δ·V(y++[e]))`,
transporting the dependent kind evidence `G.tree.nodeKind y` to `.player n` via `hnk`. -/
theorem ExtensiveGame.continuationValue_player_eventSum (G : ExtensiveGame I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (y : List E) (i : I)
    {n : PlayerNode I E} (hnk : G.toExtensiveForm.tree.nodeKind y = .player n) :
    G.continuationValue σ y i =
      ∑ e ∈ Finset.univ.image n.emit,
        G.toExtensiveForm.stepProb σ y e *
          (G.stepPayoff y e i + G.discount * G.continuationValue σ (y ++ [e]) i) := by
  rw [G.continuationValue_eq σ y i,
    ← G.toExtensiveForm.nodeStepValue_player_eventSum σ y i hnk (by simp)]
  -- Both sides are `nodeStepValue` at the same node with definitionally equal kind evidence.
  congr 1

/-- **Emitted-event finset of a node.** The finite set of events the node kind at `y` emits
(`image emit` at player / joint / chance-finite kinds; empty at terminal / general-chance). Indexes
the children frontier of the one-shot deviation backward induction. -/
noncomputable def ExtensiveForm.emitImage (G : ExtensiveForm I E) (y : List E) : Finset E :=
  match G.tree.nodeKind y with
  | .player n => Finset.univ.image n.emit
  | .joint n => Finset.univ.image n.emit
  | .chanceFinite n => Finset.univ.image n.emit
  | .terminal _ => ∅
  | .chanceGeneral _ => ∅

/-- The emitted children of a history: `y ++ [e]` for each `e ∈ emitImage y`. -/
noncomputable def ExtensiveForm.childrenOf (G : ExtensiveForm I E) (y : List E) : Finset (List E) :=
  (G.emitImage y).image (fun e => y ++ [e])

/-- The children frontier of a finite set of histories: The union of every node's emitted children.
The per-node child families are pairwise disjoint (`y ++ [e]` recovers `y` as its `dropLast`), so a
sum over the frontier splits as a double sum over `(node, event)`. -/
noncomputable def ExtensiveForm.frontier (G : ExtensiveForm I E) (S : Finset (List E)) :
    Finset (List E) :=
  S.biUnion G.childrenOf

/-- The weight pushed one layer down along `σ'`: At a child `z = y ++ [e]` it reads
`W (z.dropLast) · stepProb σ' (z.dropLast) (last z)`, which on `childrenOf y` equals
`W y · stepProb σ' y e`. The `dropLast` / `getLast` reconstruction recovers the parent and edge of
a child node, sidestepping the need for an `Inhabited E` default. -/
noncomputable def pushWeight (G : ExtensiveForm I E) (σ' : G.BehavioralStrategy)
    (W : List E → ℝ) (z : List E) : ℝ :=
  if h : z ≠ [] then W z.dropLast * G.stepProb σ' z.dropLast (z.getLast h) else 0

/-- The pushed weight at a child `y ++ [e]` is `W y · stepProb σ' y e`. -/
theorem pushWeight_concat (G : ExtensiveForm I E) (σ' : G.BehavioralStrategy)
    (W : List E → ℝ) (y : List E) (e : E) :
    pushWeight G σ' W (y ++ [e]) = W y * G.stepProb σ' y e := by
  have hne : y ++ [e] ≠ [] := by simp
  unfold pushWeight
  rw [dif_pos hne, List.dropLast_concat, List.getLast_concat]

/-- `childrenOf y` is exactly the nodes whose `dropLast` is `y` and whose last edge is emitted;
membership unfolds to a witnessing emitted event. -/
theorem ExtensiveForm.mem_childrenOf (G : ExtensiveForm I E) {y z : List E} :
    z ∈ G.childrenOf y ↔ ∃ e ∈ G.emitImage y, y ++ [e] = z := by
  simp only [ExtensiveForm.childrenOf, Finset.mem_image]

/-- A child `y ++ [e]` is longer than its parent `y`. -/
theorem ExtensiveForm.length_lt_of_mem_childrenOf (G : ExtensiveForm I E) {y z : List E}
    (hz : z ∈ G.childrenOf y) : y.length < z.length := by
  obtain ⟨e, _, rfl⟩ := (ExtensiveForm.mem_childrenOf G).mp hz
  simp

/-- **Children-frontier sum split.** A `pushWeight`-weighted sum over the children frontier of `S`
equals the double sum over `(y ∈ S, e ∈ emitImage y)` of `(W y · stepProb σ' y e) · g (y ++ [e])`.
The per-node child families are disjoint (recover the parent by `dropLast`), so
`Finset.sum_biUnion` applies and `pushWeight_concat` evaluates each term. -/
theorem sum_frontier_pushWeight (G : ExtensiveForm I E) (σ' : G.BehavioralStrategy)
    (W : List E → ℝ) (g : List E → ℝ) (S : Finset (List E)) :
    ∑ z ∈ G.frontier S, pushWeight G σ' W z * g z =
      ∑ y ∈ S, ∑ e ∈ G.emitImage y, (W y * G.stepProb σ' y e) * g (y ++ [e]) := by
  unfold ExtensiveForm.frontier
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold ExtensiveForm.childrenOf
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [pushWeight_concat]
  · -- disjointness of the per-node child families: a child's `dropLast` is its parent
    intro y₁ _ y₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, ExtensiveForm.childrenOf, Finset.mem_image]
    rintro z ⟨e₁, _, rfl⟩ ⟨e₂, _, heq⟩
    exact hne (by
      have hd : (y₁ ++ [e₁]).dropLast = (y₂ ++ [e₂]).dropLast := by rw [heq]
      rwa [List.dropLast_concat, List.dropLast_concat] at hd)

/-- The emitted-event finset of a node is exactly the set of emitted events:
`e ∈ emitImage y ↔ (G.tree.nodeKind y).emits e`. At player/joint/chance-finite nodes both sides are
`∃ c, emit c = e`; at terminal/general-chance nodes both are empty/`False`. -/
theorem ExtensiveForm.mem_emitImage_iff_emits (G : ExtensiveForm I E) (y : List E) (e : E) :
    e ∈ G.emitImage y ↔ (G.tree.nodeKind y).emits e := by
  unfold ExtensiveForm.emitImage NodeKind.emits
  rcases G.tree.nodeKind y with p | n | n | n | n <;>
    simp [Finset.mem_image]

/-- A node's emitted children are reachable: If `y` is reachable and `e ∈ emitImage y`, then
`y ++ [e]` is reachable. -/
theorem ExtensiveForm.isReachable_concat_of_mem_emitImage (G : ExtensiveForm I E) {y : List E}
    (hyr : G.IsReachable y) {e : E} (he : e ∈ G.emitImage y) :
    G.IsReachable (y ++ [e]) :=
  ExtensiveForm.IsReachable.step y e hyr ((G.mem_emitImage_iff_emits y e).mp he)

omit [DecidableEq E] in
/-- A node moving a player is not terminal. -/
theorem NodeKind.not_terminal_of_movesAt {nk : NodeKind I E} {i : I} (h : nk.movesAt i) :
    ∀ p : I → ℝ, nk ≠ .terminal p := by
  intro p hp
  rw [hp] at h
  exact h

omit [DecidableEq E] in
/-- Any `i`-mover lies strictly inside the depth bound: At depth `≥ N` every node is terminal. -/
theorem length_lt_of_movesAt (G : ExtensiveForm I E) {N : ℕ} (hfd : G.FiniteDepth N)
    {z : List E} {i : I} (h : (G.tree.nodeKind z).movesAt i) : z.length < N := by
  by_contra hge
  push Not at hge
  obtain ⟨p, hp⟩ := hfd z hge
  rw [hp] at h
  exact h

end Econlib.GameTheory
