/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.StrategicForm
public import Econlib.GameTheory.ExtensiveForm.Core.Strategy

/-!
# Behavioral-to-mixed map and realization equivalence

This file defines the **Kuhn**-style bridge (Kuhn 1953) between behavioral strategies on a finite
extensive form and mixed strategies on its strategic normalization. The map `behavioralToMixed σ`
assigns each pure strategy the independent product of the behavioral probabilities at the player's
observation sets, and `RealizationEquivalent σ μ` records agreement on every reachable terminal
history.

The realization-equivalence theorem (`behavioral_realizes_mixed`) is in `Forward.lean`.

## Main definitions

* `NodeKind.behaviorEval`: Scalar weight assigned to a pure local choice by a node behavior.
* `FiniteExtensiveForm.behavioralToMixed`: Mixed strategy induced by independent behavioral choices.
* `FiniteExtensiveForm.RealizationEquivalent`: Equality of terminal-history probabilities.

## Main statements

* `NodeKind.behaviorEval_sum_one`: Node-local behavior weights sum to one.
* `FiniteExtensiveForm.behavioralToMixedFactor_sum_one`: Per-info-set factors sum to one.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, kuhn theorem, behavioral strategy, mixed strategy
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace NodeKind

/-- Evaluate a node-local Behavior at a node-local pure choice as a scalar weight. Player and joint
nodes give the simplex value at the pure choice (or product of marginals); terminal and chance
nodes contribute weight `1` (no strategic choice to weight). -/
noncomputable def behaviorEval : (k : NodeKind I E) → k.Behavior → k.PureChoice → ℝ
  | .terminal _, _, _ => 1
  | .player n, b, c => (b : stdSimplex ℝ n.Choice).val c
  | .joint n, b, c =>
      ∏ a : n.Active, ((b : (a : n.Active) → stdSimplex ℝ (n.Choice a)) a).val (c a)
  | .chanceFinite _, _, _ => 1
  | .chanceGeneral _, _, _ => 1

lemma behaviorEval_nonneg (k : NodeKind I E) (b : k.Behavior) (c : k.PureChoice) :
    0 ≤ k.behaviorEval b c := by
  match k, b, c with
  | .player n, b, c => exact b.2.1 c
  | .joint n, b, c =>
      exact Finset.prod_nonneg (fun a _ => (b a).2.1 (c a))
  -- terminal / chance nodes contribute weight `1`
  | .terminal _, _, _ | .chanceFinite _, _, _ | .chanceGeneral _, _, _ => exact zero_le_one

lemma behaviorEval_sum_one (k : NodeKind I E) (b : k.Behavior) :
    ∑ c : k.PureChoice, k.behaviorEval b c = 1 := by
  match k, b with
  | .player n, b => exact b.2.2
  | .joint n, b =>
      change ∑ c : ((a : n.Active) → n.Choice a),
        ∏ a : n.Active, ((b : (a : n.Active) → stdSimplex ℝ (n.Choice a)) a).val (c a) = 1
      rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
      exact Finset.prod_eq_one (fun a _ => (b a).2.2)
  -- terminal / chance nodes have a unique pure choice of weight `1`
  | .terminal _, _ | .chanceFinite _, _ | .chanceGeneral _, _ =>
      simp [behaviorEval, PureChoice]

end NodeKind

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-- The scalar weight a behavioral strategy `σ` assigns to a pure strategy `s` for player `i` at a
single information set indexed by `obs`. Computed as `behaviorEval` at the canonical-rep
node-kind. -/
noncomputable def behavioralToMixedFactor (σ : G.toExtensiveForm.BehavioralStrategy) (i : I)
    (s : G.PureStrategy i) (obs : G.info.Obs i) : ℝ :=
  (G.tree.nodeKind (G.canonicalRep i obs)).behaviorEval
    (σ.atHistory (G.canonicalRep i obs)) (s obs)

lemma behavioralToMixedFactor_nonneg (σ : G.toExtensiveForm.BehavioralStrategy) (i : I)
    (s : G.PureStrategy i) (obs : G.info.Obs i) :
    0 ≤ G.behavioralToMixedFactor σ i s obs :=
  NodeKind.behaviorEval_nonneg _ _ _

/-- Sum over pure strategies of the per-info-set factor evaluated at `s obs` equals `1`. The core
algebraic step in proving `behavioralToMixed` lands in the simplex. -/
lemma behavioralToMixedFactor_sum_one (σ : G.toExtensiveForm.BehavioralStrategy) (i : I)
    (obs : G.info.Obs i) :
    ∑ c : G.infoSetChoiceForObs i obs,
      (G.tree.nodeKind (G.canonicalRep i obs)).behaviorEval
        (σ.atHistory (G.canonicalRep i obs)) c = 1 :=
  NodeKind.behaviorEval_sum_one _ _

/-- The mixed strategy on the strategic normalization induced by a behavioral strategy. The weight
on a pure strategy `s` is the independent product over `i`'s information sets of the simplex value
`σ` puts on `s`'s chosen action there. -/
noncomputable def behavioralToMixed (σ : G.toExtensiveForm.BehavioralStrategy) (i : I) :
    stdSimplex ℝ (G.PureStrategy i) :=
  ⟨fun s => ∏ obs : G.info.Obs i, G.behavioralToMixedFactor σ i s obs, by
    refine ⟨fun s => Finset.prod_nonneg fun obs _ =>
      G.behavioralToMixedFactor_nonneg σ i s obs, ?_⟩
    -- ∑_s ∏_obs factor(s obs) = ∏_obs ∑_c factor(c) = ∏_obs 1 = 1
    change ∑ s : (obs : G.info.Obs i) → G.infoSetChoiceForObs i obs,
      ∏ obs : G.info.Obs i,
        (G.tree.nodeKind (G.canonicalRep i obs)).behaviorEval
          (σ.atHistory (G.canonicalRep i obs)) (s obs) = 1
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun obs _ => G.behavioralToMixedFactor_sum_one σ i obs⟩

/-- Realization equivalence: A behavioral strategy `σ` and a mixed strategy `μ` on the strategic
normalization induce the same probability on every reachable terminal history. -/
def RealizationEquivalent [DecidableEq E] [Fintype I] [DecidableEq I] [Inhabited I]
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (μ : (G.toFiniteStrategicGame).MixedStrategy) : Prop :=
  ∀ h ∈ G.terminalReach,
    G.toExtensiveForm.finitePrefixProb σ h =
      ∑ s : ∀ i, G.PureStrategy i, (∏ i, (μ i).val (s i)) * G.pureReachProb s h

end FiniteExtensiveForm

end Econlib.GameTheory
