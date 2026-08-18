/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Refinement
public import Econlib.GameTheory.ExtensiveForm.Core.Game
public import Econlib.GameTheory.ExtensiveForm.Refinements.BeliefSystem

/-!
# Perfect Bayesian equilibrium

**Perfect Bayesian equilibrium** (Fudenberg and Tirole 1991) on the extensive-form core: An
assessment that is sequentially rational and whose beliefs are Bayes-consistent on every
positive-probability information set. Belief supports are type-level constrained both to lie inside
their information sets and to be reachability-complete — by `BeliefSystem.support_exhaustive`,
every `IsReachable` history of an info set is in its support, so no on-path reachable node can be
omitted. This makes a truncated-support assessment inexpressible, so `IsBayesConsistent` needs no
separate reachability-completeness conjunct. Sequential rationality delegates to the
`ExtensiveGame` value semantics.

## Main definitions

* `reachProb`: Root reach probability of a finite public history.
* `IsOnPath`: Positive reach probability.
* `infoSetProb`: Total represented probability mass of an information set.
* `bayesBeliefAt`: Bayesian posterior on a represented information set.
* `IsBayesConsistent`: Bayesian consistency for assessments.
* `IsSequentiallyRational`: (full) sequential rationality of an assessment, Fudenberg–Tirole.
* `IsSequentiallyRationalOneShot`: The one-shot specialization (one information-set coordinate).
* `IsPerfectBayesianEquilibrium`: Perfect Bayesian equilibrium predicate (full sequential
  rationality + Bayes consistency).
* `IsPerfectBayesianEquilibriumOneShot`: The one-shot variant characterized by `pbePred`.

## Main statements

* `IsPerfectBayesianEquilibriumOneShot_iff_pbePred`: One-shot PBE is the refined-equilibrium
  predicate of `pbePred`.
* `IsBayesConsistent_trivialBeliefs_perfectInfo`: Trivial singleton beliefs are Bayes-consistent
  under perfect information.

## Notes

Both the strategy and belief fields carry type-level info-set respect. A `G.BehavioralStrategy`
reads only the player's observation, so an `IsInfoSetDeviation` cannot admit type-dependent
deviations — both strategies use the same node-local distribution at every history within an info
set. Each `support i obs` element is subtype-witnessed, so it cannot place mass outside the info
set, and `BeliefSystem.support_exhaustive` forces the support to contain every reachable history of
the info set, so no reachable history is silently dropped from the Bayes normalization.

## References

* Fudenberg, Drew, and Jean Tirole. 1993. *Game Theory*. The MIT Press.

## Tags

extensive form, beliefs, perfect bayesian equilibrium
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-- Root reach probability of a finite public history under a behavioral strategy. -/
def reachProb (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (history : List E) : ℝ :=
  G.finitePrefixProb σ history

/-- A finite public history is on path if it has positive root reach probability. -/
def IsOnPath (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (history : List E) : Prop :=
  0 < reachProb G σ history

/-- Total represented probability mass of an information set, summing reach probabilities over the
subtype-witnessed support. -/
def infoSetProb (G : ExtensiveForm I E) (σ : G.BehavioralStrategy)
    (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i) : ℝ :=
  ∑ x ∈ μ.support i obs, reachProb G σ x.1

/-- Bayesian posterior over the represented support of an information set. Off-support histories,
histories outside the info set, and zero-mass information sets all receive zero. -/
def bayesBeliefAt (G : ExtensiveForm I E) (σ : G.BehavioralStrategy)
    (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i) (h : List E) : ℝ := by
  classical
  exact
    if hin : (G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs then
      if (⟨h, hin⟩ : G.InfoSet i obs) ∈ μ.support i obs then
        if _hpos : 0 < infoSetProb G σ μ i obs then
          reachProb G σ h / infoSetProb G σ μ i obs
        else 0
      else 0
    else 0

/-- Bayesian consistency on represented finite information-set supports: The declared beliefs equal
the Bayesian posterior on every positive-probability information set.

Reachability-completeness of the support — no node reached on path under `assess.strategy` is
omitted, so the posterior is taken over the full reachable information set rather than a truncation
— is not a conjunct here: It is guaranteed at the type level by `BeliefSystem.support_exhaustive`
(every `IsReachable` history of an info set is in its support). Since
`0 < reachProb σ h → G.IsReachable h` (`ExtensiveGame.reachProb_pos_imp_isReachable`), the support
already contains every on-path node, for every strategy; see
`DesignNotes/BeliefSupportReachabilityCompleteness.md`. -/
def IsBayesConsistent (G : ExtensiveForm I E) (assess : Assessment G) : Prop :=
  ∀ (i : I) (obs : G.info.Obs i),
    0 < infoSetProb G assess.strategy assess.beliefs i obs →
      ∀ h : List E,
        assess.beliefs.prob i obs h =
          bayesBeliefAt G assess.strategy assess.beliefs i obs h

/-- Belief-weighted continuation value of an assessment at an information set: The player's
expected payoff at the information set, integrating over their beliefs about which history they are
at and over the prescribed continuation. -/
def assessmentValue (G : ExtensiveGame I E) (assess : Assessment G.toExtensiveForm)
    (i : I) (obs : G.info.Obs i) : ℝ :=
  ∑ x ∈ assess.beliefs.support i obs,
    assess.beliefs.belief i obs x * G.continuationValue assess.strategy x.1 i

/-- A one-shot information-set deviation by player `i` at observation `obs`: σ' agrees with σ at
every (player, observation) coordinate except `(i, obs)`. Info-set respect is type-level via the
info-set-indexed strategy carrier. -/
def IsInfoSetDeviation (G : ExtensiveForm I E) (i : I) (obs : G.info.Obs i)
    (σ σ' : G.BehavioralStrategy) : Prop :=
  ∀ (j : I) (obs' : G.info.Obs j), (⟨j, obs'⟩ : Σ k, G.info.Obs k) ≠ ⟨i, obs⟩ →
    σ' j obs' = σ j obs'

omit [DecidableEq E] in
/-- A one-shot information-set deviation is in particular a *unilateral* deviation by the same
player: It changes player `i`'s behavior only (at the single coordinate `(i, obs)`), hence agrees
with `σ` at every coordinate of every other player. The converse fails in general — a unilateral
deviation may change `i`'s behavior at many information sets at once — and the one-shot deviation
principle recovers it only under perfect recall, finite depth (or discounting), and
Bayes-consistent beliefs; hence at the level of `IsPerfectBayesianEquilibrium`, not of bare
sequential rationality. -/
lemma unilateralDeviation_of_isInfoSetDeviation (G : ExtensiveForm I E) (i : I)
    (obs : G.info.Obs i) {σ σ' : G.BehavioralStrategy}
    (hdev : IsInfoSetDeviation G i obs σ σ') :
    G.unilateralDeviation i σ σ' :=
  fun j obs' hji => hdev j obs' (fun heq => hji (congrArg Sigma.fst heq))

/-- **Sequential rationality** of an assessment (Fudenberg–Tirole 1991): At every information set
of every player, the prescribed continuation is a best response given beliefs — no unilateral
deviation by that player (one that may change their behavior at any or all of their information
sets at once) increases their belief-weighted continuation value at the information set.

This is the textbook notion: The deviation is over the player's whole continuation strategy, not a
single information set. The one-shot specialization is `IsSequentiallyRationalOneShot`; the two
coincide via the one-shot deviation principle under perfect recall, finite depth (or discounting),
and Bayes-consistent beliefs — so the clean bridge is at the equilibrium level
(`IsPerfectBayesianEquilibriumOneShot → IsPerfectBayesianEquilibrium`), where consistency is
already assumed.

At an unrealized information set (empty represented support) `assessmentValue` is the empty sum for
both the assessment and any deviation, so the inequality is vacuously `0 ≥ 0`; the substantive
content there is carried by the consistency predicate, not by this one. -/
def IsSequentiallyRational (G : ExtensiveGame I E) (assess : Assessment G.toExtensiveForm) :
    Prop :=
  ∀ (i : I) (obs : G.info.Obs i) (σ' : G.toExtensiveForm.BehavioralStrategy),
    G.toExtensiveForm.unilateralDeviation i assess.strategy σ' →
      assessmentValue G assess i obs ≥
        assessmentValue G { strategy := σ', beliefs := assess.beliefs } i obs

/-- One-shot sequential rationality: At every information set of every player, no one-shot
information-set deviation by that player (changing behavior at that one information set only)
increases their belief-weighted continuation value at the information set. This is the
easy-to-verify specialization of `IsSequentiallyRational`; the implication
`IsSequentiallyRational → this` is `IsSequentiallyRational.oneShot`, and the converse is the
one-shot deviation principle (perfect recall, finite depth or discounting, and Bayes-consistent
beliefs). -/
def IsSequentiallyRationalOneShot (G : ExtensiveGame I E)
    (assess : Assessment G.toExtensiveForm) : Prop :=
  ∀ (i : I) (obs : G.info.Obs i) (σ' : G.toExtensiveForm.BehavioralStrategy),
    IsInfoSetDeviation G.toExtensiveForm i obs assess.strategy σ' →
      assessmentValue G assess i obs ≥
        assessmentValue G { strategy := σ', beliefs := assess.beliefs } i obs

/-- Full sequential rationality implies its one-shot specialization: A one-shot deviation is a
unilateral deviation, so it is already covered by the full quantifier. -/
theorem IsSequentiallyRational.oneShot {G : ExtensiveGame I E}
    {assess : Assessment G.toExtensiveForm} (h : IsSequentiallyRational G assess) :
    IsSequentiallyRationalOneShot G assess :=
  fun i obs σ' hdev =>
    h i obs σ' (unilateralDeviation_of_isInfoSetDeviation G.toExtensiveForm i obs hdev)

/-- Perfect Bayesian equilibrium (Fudenberg–Tirole 1991): (full) sequential rationality of the
assessment plus Bayes consistency of the belief system on positive-probability information sets. -/
structure IsPerfectBayesianEquilibrium
    (G : ExtensiveGame I E) (assess : Assessment G.toExtensiveForm) : Prop where
  /-- The assessment is (fully) sequentially rational. -/
  sequentiallyRational : IsSequentiallyRational G assess
  /-- The belief system is Bayes consistent on positive-probability information sets. -/
  bayesConsistent : IsBayesConsistent G.toExtensiveForm assess

/-- One-shot perfect Bayesian equilibrium: One-shot sequential rationality plus Bayes consistency.
This is the predicate characterized by the `pbePred` refinement scaffold (`pbePred` quantifies one
information-set coordinate at a time). It implies `IsPerfectBayesianEquilibrium` under perfect
recall and finite depth (or discounting) via the one-shot deviation principle — the
Bayes-consistency half of a one-shot PBE supplies the belief consistency that principle needs. The
reverse implication is unconditional (`IsPerfectBayesianEquilibrium.oneShot`). -/
structure IsPerfectBayesianEquilibriumOneShot
    (G : ExtensiveGame I E) (assess : Assessment G.toExtensiveForm) : Prop where
  /-- The assessment is one-shot sequentially rational. -/
  sequentiallyRationalOneShot : IsSequentiallyRationalOneShot G assess
  /-- The belief system is Bayes consistent on positive-probability information sets. -/
  bayesConsistent : IsBayesConsistent G.toExtensiveForm assess

/-- A perfect Bayesian equilibrium is in particular a one-shot PBE. -/
theorem IsPerfectBayesianEquilibrium.oneShot {G : ExtensiveGame I E}
    {assess : Assessment G.toExtensiveForm} (h : IsPerfectBayesianEquilibrium G assess) :
    IsPerfectBayesianEquilibriumOneShot G assess :=
  ⟨h.sequentiallyRational.oneShot, h.bayesConsistent⟩

/-! ## PBE as an `EquilibriumRefinement`

PBE rides on the abstract `EquilibriumRefinement` scaffold from
`Econlib/GameTheory/Equilibrium`. The deviation half is sequential rationality (deviator =
`(i, obs) : Σ i, Obs i`, swap = info-set deviation that fixes beliefs, value = belief-weighted
continuation value); the validity half is Bayes consistency. The
`IsPerfectBayesianEquilibriumOneShot_iff_pbePred` equivalence packages the refinement view for
bridges from other game forms. -/
/-- Assessment-level info-set deviation: The deviating assessment keeps beliefs fixed and performs
a strategy-level info-set deviation. -/
@[reducible] def IsAssessmentInfoSetDeviation (G : ExtensiveForm I E) (i : I) (obs : G.info.Obs i)
    (a a' : Assessment G) : Prop :=
  a'.beliefs = a.beliefs ∧ IsInfoSetDeviation G i obs a.strategy a'.strategy

/-- The PBE refinement: Assessments are candidates, the deviation half is sequential rationality
phrased as an `EquilibriumProblem`, and validity is Bayes consistency. -/
def ExtensiveGame.pbePred (G : ExtensiveGame I E) : EquilibriumRefinement where
  S      := Assessment G.toExtensiveForm
  I      := Σ i, G.info.Obs i
  swap   := fun p a a' => IsAssessmentInfoSetDeviation G.toExtensiveForm p.1 p.2 a a'
  value  := fun p a => assessmentValue G a p.1 p.2
  valid  := IsBayesConsistent G.toExtensiveForm

/-- One-shot perfect Bayesian equilibrium is exactly the refined-equilibrium predicate of `pbePred`
(whose deviation half fixes all but one information-set coordinate). For the full Fudenberg–Tirole
predicate, compose with the one-shot deviation principle. -/
theorem IsPerfectBayesianEquilibriumOneShot_iff_pbePred
    (G : ExtensiveGame I E) (a : Assessment G.toExtensiveForm) :
    IsPerfectBayesianEquilibriumOneShot G a ↔ G.pbePred.IsRefinedEquilibrium a := by
  constructor
  · rintro ⟨hSR, hBayes⟩
    refine ⟨hBayes, ?_⟩
    rintro ⟨i, obs⟩ ⟨s', b'⟩ ⟨hbeliefs, hdev⟩
    subst hbeliefs
    exact hSR i obs s' hdev
  · rintro ⟨hValid, hIsEq⟩
    refine ⟨?_, hValid⟩
    intro i obs σ' hdev
    exact hIsEq ⟨i, obs⟩ ⟨σ', a.beliefs⟩ ⟨rfl, hdev⟩

/-! ## Perfect-information specialization -/

/-- The perfect-information extensive form on a tree: Every player observes the full history,
trivially info-set-respecting because info sets are singletons. -/
abbrev perfectInfoForm [DecidableEq I] (t : GameTree I E) : ExtensiveForm I E :=
  ExtensiveForm.ofGameTreePerfectInfo t

/-- Under perfect information with trivial singleton beliefs, the probability of an information set
at observation `obs` reduces to the reach probability of `obs` itself, provided player `i` actually
moves at history `obs`. -/
lemma infoSetProb_trivialBeliefs_perfectInfo_pos [DecidableEq I]
    (t : GameTree I E) (σ : (perfectInfoForm t).BehavioralStrategy)
    {i : I} {obs : List E} (hm : (t.nodeKind obs).movesAt i) :
    infoSetProb (perfectInfoForm t) σ (trivialBeliefs I E t) i obs =
      reachProb _ σ obs := by
  classical
  unfold infoSetProb
  have hsupp :
      (trivialBeliefs I E t).support i obs =
        ({⟨obs, hm, rfl⟩} :
          Finset ((perfectInfoForm t).InfoSet i obs)) :=
    show (if hm' : (t.nodeKind obs).movesAt i then
            ({⟨obs, hm', rfl⟩} :
              Finset ((perfectInfoForm t).InfoSet i obs))
          else ∅) = _ from dif_pos hm
  rw [hsupp, Finset.sum_singleton]

/-- Under perfect information with trivial singleton beliefs, the probability of an information set
at observation `obs` is zero when player `i` does not move at history `obs` (the info set is
empty). -/
lemma infoSetProb_trivialBeliefs_perfectInfo_neg [DecidableEq I]
    (t : GameTree I E) (σ : (perfectInfoForm t).BehavioralStrategy)
    {i : I} {obs : List E} (hm : ¬ (t.nodeKind obs).movesAt i) :
    infoSetProb (perfectInfoForm t) σ (trivialBeliefs I E t) i obs = 0 := by
  classical
  unfold infoSetProb
  have hsupp : (trivialBeliefs I E t).support i obs = ∅ :=
    show (if hm' : (t.nodeKind obs).movesAt i then
            ({⟨obs, hm', rfl⟩} :
              Finset ((perfectInfoForm t).InfoSet i obs))
          else ∅) = _ from dif_neg hm
  rw [hsupp, Finset.sum_empty]

/-- Trivial singleton beliefs are Bayes-consistent under perfect information. -/
theorem IsBayesConsistent_trivialBeliefs_perfectInfo [DecidableEq I]
    (t : GameTree I E) (σ : (perfectInfoForm t).BehavioralStrategy) :
    IsBayesConsistent (perfectInfoForm t)
      { strategy := σ, beliefs := trivialBeliefs I E t } := by
  classical
  intro i obs hpos h
  by_cases hm : (t.nodeKind obs).movesAt i
  · rw [infoSetProb_trivialBeliefs_perfectInfo_pos t σ hm] at hpos
    by_cases hheq : h = obs
    · subst hheq
      rw [trivialBeliefs_prob_self t i h hm]
      unfold bayesBeliefAt
      have hin :
          ((perfectInfoForm t).tree.nodeKind h).movesAt i ∧
            (perfectInfoForm t).info.observe i h = h := ⟨hm, rfl⟩
      have hmem : (⟨h, hin⟩ :
            (perfectInfoForm t).InfoSet i h) ∈ (trivialBeliefs I E t).support i h := by
        change ⟨h, hin⟩ ∈ (if hm' : (t.nodeKind h).movesAt i then
                            ({⟨h, hm', rfl⟩} :
                              Finset ((perfectInfoForm t).InfoSet i h)) else ∅)
        rw [dif_pos hm, Finset.mem_singleton]
      have hpos' : 0 < infoSetProb (perfectInfoForm t) σ (trivialBeliefs I E t) i h := by
        rw [infoSetProb_trivialBeliefs_perfectInfo_pos t σ hm]; exact hpos
      simp only [dif_pos hin, if_pos hmem, dif_pos hpos']
      rw [infoSetProb_trivialBeliefs_perfectInfo_pos t σ hm,
        div_self (ne_of_gt hpos)]
    · -- h ≠ obs: LHS is 0 by trivialBeliefs_prob_zero_of_ne.
      rw [trivialBeliefs_prob_zero_of_ne t i obs h hheq]
      unfold bayesBeliefAt
      have hnot :
          ¬ (((perfectInfoForm t).tree.nodeKind h).movesAt i ∧
              (perfectInfoForm t).info.observe i h = obs) :=
        fun ⟨_, hobs⟩ => hheq hobs
      simp only [dif_neg hnot]
  · -- Player i doesn't move at obs; infoSetProb = 0, contradicting hpos.
    exfalso
    rw [infoSetProb_trivialBeliefs_perfectInfo_neg t σ hm] at hpos
    exact lt_irrefl _ hpos

/-! ## Reach-probability tower

The root reach of a path concatenation factors through the intermediate history, reach
probabilities are nonnegative, and reach is monotone under taking prefixes. -/
/-- **Reach tower from the root.** Specialization of `finitePrefixProbFrom_append` to `reachProb`:
The root reach of `pre ++ suf` is the root reach of `pre` times the continuation probability of
`suf` from `pre`. -/
theorem reachProb_append (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (pre suf : List E) :
    reachProb G σ (pre ++ suf) =
      reachProb G σ pre * G.finitePrefixProbFrom σ pre suf := by
  unfold reachProb ExtensiveForm.finitePrefixProb
  rw [G.finitePrefixProbFrom_append σ [] pre suf, List.nil_append]

/-- **Reach probabilities are nonnegative.** Each one-step factor `stepProb` is an `eventProb` of a
simplex/chance distribution, hence nonnegative; the product over the path stays nonnegative. -/
theorem reachProb_nonneg (G : ExtensiveForm I E) (σ : G.BehavioralStrategy) (h : List E) :
    0 ≤ reachProb G σ h :=
  G.finitePrefixProbFrom_nonneg σ [] h

/-- **Reach factors through any prefix.** If a history `y` has positive reach under `σ`, so does
every prefix of `y`: The reach of `y` is the reach of the prefix times the (nonnegative)
continuation probability, and a product is positive only if both factors are. -/
theorem reachProb_pos_of_prefix (G : ExtensiveForm I E) (σ : G.BehavioralStrategy)
    {y pre : List E} (hpre : pre <+: y) (hpos : 0 < reachProb G σ y) :
    0 < reachProb G σ pre := by
  obtain ⟨suf, rfl⟩ := hpre
  rw [reachProb_append G σ pre suf] at hpos
  by_contra hle
  push Not at hle
  have h0 : reachProb G σ pre = 0 := le_antisymm hle (reachProb_nonneg G σ pre)
  rw [h0, zero_mul] at hpos
  exact lt_irrefl 0 hpos

end Econlib.GameTheory
