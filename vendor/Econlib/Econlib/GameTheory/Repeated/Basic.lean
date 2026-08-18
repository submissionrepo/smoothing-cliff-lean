/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE
public import Econlib.GameTheory.Strategic.Basic

/-!
# Repeated games

Perfect-monitoring repeated games are represented as history-based extensive-form games. Each
nonterminal public history is a joint node where all stage-game players choose simultaneously, and
the emitted public event is the realized stage-game action profile. The file provides the
infrastructure used in folk-theorem-style arguments — feasible and individually rational payoffs,
the pure-action minmax benchmark, and self-generating payoff sets — as objects and conditions; it
does not itself prove a folk theorem.

## Main definitions

* `FiniteStrategicGame.PublicHistory`: Finite public histories of stage-game action profiles.
* `RepeatedGame`: An infinite-horizon repeated game with a finite stage game and common discount
  factor.
* `RepeatedGame.PublicStrategy`: Behavioral strategies on the perfect-information extensive-form
  lift.
* `RepeatedGame.continuationValue`: Normalized discounted continuation payoffs induced by public
  strategies.
* `RepeatedGame.toExtensiveGame`: The repeated game as an extensive game with node-local Bellman
  continuation values.
* `RepeatedGame.IsSubgamePerfectEquilibrium`: Repeated-game subgame perfection, defined as the
  extensive-game predicate on the perfect-information lift.
* `RepeatedGame.grimTrigger`: The grim-trigger / Nash-reversion pure-action rule.
* `RepeatedGame.MinmaxValue`: The pure-action minmax benchmark for a player.
* `RepeatedGame.IsPureFeasiblePayoff`, `RepeatedGame.IsIndividuallyRationalPayoffSet`,
  `RepeatedGame.IsSelfGenerating`: Payoff-set conditions used in folk-theorem-style arguments.

## Main statements

* `RepeatedGame.IsPerfectBayesianEquilibrium_toExtensiveGame_of_IsSubgamePerfectEquilibrium`: A
  public-strategy subgame-perfect equilibrium induces a perfect Bayesian equilibrium of the
  associated perfect-information extensive game with singleton beliefs.

## References

* Friedman, James W. 1971. “A Non-Cooperative Equilibrium for Supergames.” *The Review of Economic
  Studies* 38 (1): 1. [https://doi.org/10.2307/2296617](https://doi.org/10.2307/2296617).

## Tags

repeated games, extensive form games, subgame perfection, perfect bayesian equilibrium, folk theorem
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

namespace FiniteStrategicGame

/-- A public history in a perfect-monitoring repeated game is a finite list of stage-game action
profiles. -/
abbrev PublicHistory (G : FiniteStrategicGame) := List G.ActionProfile

/-- An infinite public path is a stream of stage-game action profiles. -/
abbrev PublicPath (G : FiniteStrategicGame) := ℕ → G.ActionProfile

/-- Finite public histories of exactly `T` periods. -/
def HistoriesOfLength (G : FiniteStrategicGame) : ℕ → Finset G.PublicHistory
  | 0 => {[]}
  | T + 1 =>
      (G.HistoriesOfLength T).biUnion
        (fun h => Finset.univ.image (fun a : G.ActionProfile => h ++ [a]))

end FiniteStrategicGame

/-- An infinite-horizon repeated game with common discount factor. -/
structure RepeatedGame where
  /-- The finite strategic-form stage game. -/
  stage : FiniteStrategicGame
  /-- Common discount factor. -/
  discount : ℝ
  /-- The common discount factor is nonnegative. -/
  discount_nonneg : 0 ≤ discount
  /-- The common discount factor is strictly less than one. -/
  discount_lt_one : discount < 1

namespace RepeatedGame

variable (R : RepeatedGame)

/-- The joint decision node used at every public history of the repeated game. -/
def stageJointNode : JointNode R.stage.Player R.stage.ActionProfile where
  Active := R.stage.Player
  player := id
  player_injective := Function.injective_id
  Choice := R.stage.Action
  emit := id

/-- The repeated game as a history-based extensive-form game tree. -/
def toGameTree : GameTree R.stage.Player R.stage.ActionProfile where
  nodeKind _ := .joint R.stageJointNode

/-- The repeated game as an extensive form (perfect-monitoring => perfect information). -/
noncomputable def toExtensiveForm : ExtensiveForm R.stage.Player R.stage.ActionProfile :=
  ExtensiveForm.ofGameTreePerfectInfo R.toGameTree

/-- Repeated-game public strategies: Behavioral strategies on the perfect-information lift. The
per-history accessor `atHistory` retrieves the stage-action simplex by transport across
`iChoiceType_eq`. -/
abbrev PublicStrategy (R : RepeatedGame) : Type _ := R.toExtensiveForm.BehavioralStrategy

/-- The behavioral-strategy choice type at observation `h` for player `i` is propositionally equal
to `R.stage.Action i`, up to the `Classical.choose` indirection in `iPosition`. -/
lemma iChoiceType_eq (i : R.stage.Player) (h : R.stage.PublicHistory) :
    R.toExtensiveForm.info.iChoiceType i h = R.stage.Action i := by
  have hex : ∃ a : R.stageJointNode.Active, R.stageJointNode.player a = i := ⟨i, rfl⟩
  have hm : (R.toGameTree.nodeKind h).movesAt i := hex
  change (R.toGameTree.nodeKind h).iChoiceTypeAt' i = R.stage.Action i
  rw [NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ _ hm]
  exact congrArg R.stage.Action (R.stageJointNode.iPosition_player i hm)

/-- Per-history accessor for public strategies.

Every node of the repeated game's extensive lift is a joint stage node, so a behavioral strategy at
history `h` is a profile of mixed stage actions. The transport from the perfect-information
builder's `iChoiceType` to `R.stage.Action i` is mediated by `simplexTransport` across
`iChoiceType_eq`. -/
@[simp] noncomputable def atHistory (σ : R.PublicStrategy) (i : R.stage.Player)
    (h : R.stage.PublicHistory) : stdSimplex ℝ (R.stage.Action i) :=
  simplexTransport (R.iChoiceType_eq i h) (σ i h)

/-- Evaluating `atHistory` on a strategy built by `ofPerfectInfo` returns the per-history behavior
coordinate directly. At every node of a repeated game the stage joint node has its `player` map
equal to the identity, so player `i` moves at position `i`. Both the `ofPerfectInfo` transport and
the `atHistory` transport cancel, leaving `b h i`. -/
lemma atHistory_ofPerfectInfo
    (b : (h : R.stage.PublicHistory) → (R.toGameTree.nodeKind h).Behavior)
    (i : R.stage.Player) (h : R.stage.PublicHistory) :
    R.atHistory (ExtensiveForm.BehavioralStrategy.ofPerfectInfo b) i h = b h i := by
  have hatHistory : HEq (R.atHistory (ExtensiveForm.BehavioralStrategy.ofPerfectInfo b) i h)
      (ExtensiveForm.BehavioralStrategy.ofPerfectInfo b i h) := by
    simp only [atHistory]
    exact simplexTransport_heq _ _
  -- `i` moves at every joint node, so `ofPerfectInfo` takes the `dif_pos` branch: a transport of
  -- `iLocalBehavior`, which projects the position representing `i`.
  have hm : (R.toGameTree.nodeKind h).movesAt i := ⟨i, rfl⟩
  have hofp : ExtensiveForm.BehavioralStrategy.ofPerfectInfo b i h =
      simplexTransport ((NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ _ hm).symm)
        ((R.toGameTree.nodeKind h).iLocalBehavior i hm (b h)) := by
    unfold ExtensiveForm.BehavioralStrategy.ofPerfectInfo
    split
    · rfl
    · exact absurd hm (by assumption)
  -- The projected position represents `i`, and equals `i` since the joint `player` map is the
  -- identity; so the projected coordinate is heterogeneously `b h i`.
  have hpos : R.stageJointNode.iPosition i hm = i := R.stageJointNode.iPosition_player i hm
  have hilb : HEq ((R.toGameTree.nodeKind h).iLocalBehavior i hm (b h)) (b h i) :=
    congr_arg_heq (b h) hpos
  -- Chain: accessor ≍ raw ≍ projected coordinate ≍ `b h i`; both ends at `stdSimplex ℝ (Action i)`.
  refine eq_of_heq (hatHistory.trans ?_)
  rw [hofp]
  exact (simplexTransport_heq _ _).trans hilb

/-- The one-period expected stage payoff after public history `h`. -/
noncomputable def stagePayoff (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) : ℝ :=
  R.stage.expectedPayoff i (fun j => R.atHistory σ j h)

/-- The probability of a stage-game action profile at public history `h`. -/
noncomputable def stageProfileProb (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.ActionProfile) : ℝ :=
  ∏ i : R.stage.Player, R.atHistory σ i h (a i)

/-- The one-period product distribution over stage-game action profiles at public history `h`. -/
noncomputable def stageProfileDist (σ : R.PublicStrategy) (h : R.stage.PublicHistory) :
    Probability.FinDist R.stage.ActionProfile :=
  Probability.FinDist.productD (fun i => Probability.FinDist.ofSimplex (R.atHistory σ i h))

/-- Probability assigned by a public strategy to a finite continuation history, starting from
public history `h`. -/
noncomputable def publicHistoryProbFrom (σ : R.PublicStrategy)
    (h suffix : R.stage.PublicHistory) : ℝ :=
  R.toExtensiveForm.finitePrefixProbFrom σ h suffix

/-- Probability assigned by a public strategy to a finite public history from the root. -/
noncomputable def publicHistoryProb (σ : R.PublicStrategy) (h : R.stage.PublicHistory) : ℝ :=
  R.publicHistoryProbFrom σ [] h

/-- Normalized discounted payoff over a realized finite public-history prefix. -/
def discountedPrefixPayoff : R.stage.PublicHistory → R.stage.Player → ℝ
  | [], _i => 0
  | a :: rest, i =>
      (1 - R.discount) * R.stage.payoff i a +
        R.discount * discountedPrefixPayoff rest i

/-- Expected normalized payoff over all length-`T` public histories induced by a public strategy,
conditional on a starting history. -/
noncomputable def finiteHorizonContinuationValue (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (T : ℕ) (i : R.stage.Player) : ℝ :=
  ∑ suffix ∈ R.stage.HistoriesOfLength T,
    R.publicHistoryProbFrom σ h suffix * R.discountedPrefixPayoff suffix i

/-- Expected stage payoff in period `t` after public history `h`, integrating over all public
continuations of length `t`. -/
noncomputable def periodExpectedPayoff (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (t : ℕ) (i : R.stage.Player) : ℝ :=
  ∑ suffix ∈ R.stage.HistoriesOfLength t,
    R.publicHistoryProbFrom σ h suffix * R.stagePayoff σ (h ++ suffix) i

/-- Induced normalized discounted continuation value after public history `h`. -/
noncomputable def continuationValue (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (i : R.stage.Player) : ℝ :=
  (1 - R.discount) *
    ∑' t : ℕ, R.discount ^ t * R.periodExpectedPayoff σ h t i

/-! ### Sub-step 1: σ-coordinate identification

The Bellman side of `continuationValue_eq` uses `σ.jointBehavior h rfl a` indexed over
`R.stageJointNode.Active = R.stage.Player`. We need this to coincide with `R.atHistory σ a h`,
which is the user-facing accessor. Both transport `σ a h` across the same propositional equality of
choice types, so they agree up to proof-irrelevance of the underlying `Fintype` instances. -/

/-- Coordinate-wise identification of `σ.jointBehavior` with `R.atHistory`. Both are
`simplexTransport` applications of `σ a h` across propositionally-equal choice types, so they
coincide as elements of `stdSimplex ℝ (R.stage.Action a)`. -/
lemma jointBehavior_HEq_atHistory (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.Player) :
    HEq (σ.jointBehavior (n := R.stageJointNode) h rfl a) (R.atHistory σ a h) := by
  have hLHS : HEq (σ.atHistory h a) (σ a h) := simplexTransport_heq _ _
  have hRHS : HEq (R.atHistory σ a h) (σ a h) := simplexTransport_heq (R.iChoiceType_eq a h) (σ a h)
  exact hLHS.trans hRHS.symm

/-- Real-valued coordinate identification: The components of `σ.jointBehavior` and `R.atHistory`
agree as real-valued functions on choices. -/
lemma jointBehavior_val_eq_atHistory_val (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.Player) (c : R.stage.Action a) :
    (σ.jointBehavior (n := R.stageJointNode) h rfl a).val c = (R.atHistory σ a h).val c := by
  have : σ.jointBehavior (n := R.stageJointNode) h rfl a = R.atHistory σ a h := eq_of_heq
    (R.jointBehavior_HEq_atHistory σ h a)
  rw [this]

/-! ### Sub-step 1b: Stage profile probabilities sum to 1 -/

/-- The stage profile probabilities form a normalized distribution: Summing over all action
profiles yields 1. This is the product-of-marginals normalization. -/
lemma sum_stageProfileProb (σ : R.PublicStrategy) (h : R.stage.PublicHistory) :
    ∑ a : R.stage.ActionProfile, R.stageProfileProb σ h a = 1 := by
  classical
  change (∑ a : R.stage.ActionProfile, ∏ i, (R.atHistory σ i h).val (a i)) = 1
  rw [show
        (∑ a : R.stage.ActionProfile, ∏ i, (R.atHistory σ i h).val (a i))
          = ∏ i, ∑ aᵢ : R.stage.Action i, (R.atHistory σ i h).val aᵢ from
        (Fintype.prod_sum (κ := fun i => R.stage.Action i)
          (f := fun i aᵢ => (R.atHistory σ i h).val aᵢ)).symm]
  refine Finset.prod_eq_one (fun i _ => ?_)
  exact (R.atHistory σ i h).property.2

/-- The stage profile probabilities are nonnegative. -/
lemma stageProfileProb_nonneg (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.ActionProfile) : 0 ≤ R.stageProfileProb σ h a :=
  Finset.prod_nonneg (fun i _ => (R.atHistory σ i h).property.1 (a i))

/-- The stage profile probabilities are bounded by 1 per coordinate (each factor is ≤ 1). -/
lemma stageProfileProb_le_one (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.ActionProfile) : R.stageProfileProb σ h a ≤ 1 := by
  have hle : ∀ i, (R.atHistory σ i h).val (a i) ≤ 1 := by
    intro i
    have hsum : ∑ x : R.stage.Action i, (R.atHistory σ i h).val x = 1 :=
      (R.atHistory σ i h).property.2
    have hnn : ∀ x, 0 ≤ (R.atHistory σ i h).val x := (R.atHistory σ i h).property.1
    have hmem : a i ∈ (Finset.univ : Finset (R.stage.Action i)) := Finset.mem_univ _
    calc (R.atHistory σ i h).val (a i)
        ≤ ∑ x : R.stage.Action i, (R.atHistory σ i h).val x :=
          Finset.single_le_sum (f := fun x => (R.atHistory σ i h).val x)
            (fun x _ => hnn x) hmem
      _ = 1 := hsum
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => hle i)
  exact (R.atHistory σ i h).property.1 (a i)

/-! ### Sub-step 1c: StepProb / stagePayoff bridges -/

/-- One-step probability under the repeated game's extensive form equals the stage profile
probability. The joint node has `emit = id` so the `if`-sum in `NodeKind.eventProb` collapses to a
single nonzero term at `c = a`. -/
lemma stepProb_eq_stageProfileProb (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (a : R.stage.ActionProfile) :
    R.toExtensiveForm.stepProb σ h a = R.stageProfileProb σ h a := by
  classical
  have hsingle :
      (∑ c : (a' : R.stageJointNode.Active) → R.stageJointNode.Choice a',
        if R.stageJointNode.emit c = a then
          ∏ a' : R.stageJointNode.Active,
            (σ.atHistory h a').val (c a')
        else 0)
        = ∏ a' : R.stageJointNode.Active, (σ.atHistory h a').val (a a') := by
    refine (Finset.sum_eq_single a ?_ ?_).trans ?_
    · intro c _ hc
      simp only [show R.stageJointNode.emit c = c from rfl, if_neg hc]
    · intro h_not_mem
      exact absurd (Finset.mem_univ a) h_not_mem
    · simp only [show R.stageJointNode.emit a = a from rfl, if_true]
  have hprod :
      (∏ a' : R.stageJointNode.Active, (σ.atHistory h a').val (a a'))
        = R.stageProfileProb σ h a := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact R.jointBehavior_val_eq_atHistory_val σ h i (a i)
  exact hsingle.trans hprod

/-- The expected stage payoff under `σ` at history `h` equals the weighted sum of pure-action stage
payoffs against the product distribution `stageProfileProb σ h`. -/
lemma stagePayoff_eq_sum_stageProfileProb (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) :
    R.stagePayoff σ h i =
      ∑ c : R.stage.ActionProfile, R.stageProfileProb σ h c * R.stage.payoff i c := by trivial

/-! Definitional simp lemmas for `publicHistoryProbFrom` (used by Bellman-shift proofs below). -/

@[simp] lemma publicHistoryProbFrom_nil (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) :
    R.publicHistoryProbFrom σ h [] = 1 := rfl

@[simp] lemma publicHistoryProbFrom_cons (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (a : R.stage.ActionProfile) (suffix : R.stage.PublicHistory) :
    R.publicHistoryProbFrom σ h (a :: suffix) =
      R.toExtensiveForm.stepProb σ h a * R.publicHistoryProbFrom σ (h ++ [a]) suffix := rfl

/-! ### Sub-step 2: First-action decomposition of `HistoriesOfLength`

`HistoriesOfLength` is defined by last-action extension. But the path-probability decomposition
factors out the *first* action. We bridge the two via a `Finset.sum` identity, which is all we need
for the Bellman shift. -/

/-- Every element of `HistoriesOfLength T` is a list of length `T`. -/
lemma length_of_mem_HistoriesOfLength (G : FiniteStrategicGame) :
    ∀ (T : ℕ) (h : G.PublicHistory), h ∈ G.HistoriesOfLength T → h.length = T := by
  intro T
  induction T with
  | zero => simp [FiniteStrategicGame.HistoriesOfLength]
  | succ T ih =>
    intro _ hh
    rcases Finset.mem_biUnion.mp hh with ⟨h', hh', hmem⟩
    rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
    have hlen : h'.length = T := ih h' hh'
    subst ha
    simp [hlen]

/-- Auxiliary decomposition: `HoL (T+1) = (HoL T).biUnion (h ↦ univ.image (a ↦ h ++ [a]))` as a
sum, with the per-h image expanded via `Finset.sum_image` and the disjointness coming from list
length equality on HoL elements. -/
lemma sum_HistoriesOfLength_succ_last_action (G : FiniteStrategicGame) (T : ℕ)
    (f : G.PublicHistory → ℝ) :
    ∑ suffix ∈ G.HistoriesOfLength (T + 1), f suffix =
      ∑ h ∈ G.HistoriesOfLength T, ∑ a : G.ActionProfile, f (h ++ [a]) := by
  classical
  change ∑ suffix ∈ (G.HistoriesOfLength T).biUnion
      (fun h => Finset.univ.image (fun a : G.ActionProfile => h ++ [a])), f suffix = _
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.sum_image (fun a _ b _ hab => by
      simpa using List.append_cancel_left (as := h) hab)]
  · intro h₁ hh₁ h₂ hh₂ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro x ⟨a₁, _, hxa₁⟩ ⟨a₂, _, hxa₂⟩
    apply hne
    have hxe : h₁ ++ [a₁] = h₂ ++ [a₂] := hxa₁.trans hxa₂.symm
    have hlen₁ : h₁.length = T :=
      length_of_mem_HistoriesOfLength G _ h₁ (Finset.mem_coe.mp hh₁)
    have hlen₂ : h₂.length = T :=
      length_of_mem_HistoriesOfLength G _ h₂ (Finset.mem_coe.mp hh₂)
    exact (List.append_inj hxe (hlen₁.trans hlen₂.symm)).1

/-- A length-`(t+1)` history decomposes as `a :: rest` where `a` is the first action profile and
`rest` is a length-`t` history. As a `Finset.sum` identity over the (last-action-defined)
`HistoriesOfLength`. -/
lemma sum_HistoriesOfLength_succ_first_action (G : FiniteStrategicGame) :
    ∀ (t : ℕ) (f : G.PublicHistory → ℝ),
      ∑ suffix ∈ G.HistoriesOfLength (t + 1), f suffix =
        ∑ a : G.ActionProfile, ∑ rest ∈ G.HistoriesOfLength t, f (a :: rest) := by
  classical
  intro t
  induction t with
  | zero =>
    intro f
    -- HoL 1 = univ.image (a ↦ [a]); HoL 0 = {[]}.
    have hHoL1 : G.HistoriesOfLength 1 =
        (Finset.univ : Finset G.ActionProfile).image (fun a => [a]) := by
      simp [FiniteStrategicGame.HistoriesOfLength]
    rw [hHoL1]
    rw [Finset.sum_image (fun a _ b _ hab => by simpa using hab)]
    simp [FiniteStrategicGame.HistoriesOfLength]
  | succ T ih =>
    intro f
    rw [sum_HistoriesOfLength_succ_last_action G (T + 1) f,
        ih (fun h' => ∑ a : G.ActionProfile, f (h' ++ [a]))]
    have :
        ∀ a : G.ActionProfile,
          ∑ rest ∈ G.HistoriesOfLength (T + 1), f (a :: rest) =
            ∑ h ∈ G.HistoriesOfLength T, ∑ a' : G.ActionProfile, f (a :: (h ++ [a'])) := by
      intro a
      exact sum_HistoriesOfLength_succ_last_action G T (fun rest => f (a :: rest))
    simp [this]

/-! ### Sub-step 3: PeriodExpectedPayoff Bellman shift -/

/-- One-step Bellman shift for `periodExpectedPayoff`: Integrating over length-`(t+1)`
continuations factors as a stage-profile expectation of length-`t` continuations after the one-step
extension. -/
lemma periodExpectedPayoff_succ (σ : R.PublicStrategy) (h : R.stage.PublicHistory) (t : ℕ)
    (i : R.stage.Player) :
    R.periodExpectedPayoff σ h (t + 1) i =
      ∑ c : R.stage.ActionProfile,
        R.stageProfileProb σ h c * R.periodExpectedPayoff σ (h ++ [c]) t i := by
  classical
  unfold periodExpectedPayoff
  rw [sum_HistoriesOfLength_succ_first_action R.stage t
    (fun suffix => R.publicHistoryProbFrom σ h suffix * R.stagePayoff σ (h ++ suffix) i)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun rest _ => ?_)
  have hprob : R.publicHistoryProbFrom σ h (c :: rest) =
      R.stageProfileProb σ h c * R.publicHistoryProbFrom σ (h ++ [c]) rest := by
    rw [publicHistoryProbFrom_cons, R.stepProb_eq_stageProfileProb σ h c]
  have hlist : h ++ c :: rest = h ++ [c] ++ rest := by
    simp [List.append_assoc]
  rw [hprob, hlist]
  ring

/-! ### Sub-step 3b: Path probabilities are nonneg and sum to one -/

/-- Path probabilities are nonnegative. By induction on the suffix, using nonnegativity of
`stageProfileProb` at each step. -/
lemma publicHistoryProbFrom_nonneg (σ : R.PublicStrategy) :
    ∀ (h suffix : R.stage.PublicHistory), 0 ≤ R.publicHistoryProbFrom σ h suffix := by
  intro h suffix
  induction suffix generalizing h with
  | nil => simp [publicHistoryProbFrom]
  | cons c rest ih =>
    rw [publicHistoryProbFrom_cons, R.stepProb_eq_stageProfileProb σ h c]
    exact mul_nonneg (R.stageProfileProb_nonneg σ h c) (ih (h ++ [c]))

/-- Path probabilities sum to one along all length-`t` continuations. -/
lemma pathProb_sum_one (σ : R.PublicStrategy) (h : R.stage.PublicHistory) (t : ℕ) :
    ∑ suffix ∈ R.stage.HistoriesOfLength t, R.publicHistoryProbFrom σ h suffix = 1 := by
  classical
  induction t generalizing h with
  | zero =>
    simp [FiniteStrategicGame.HistoriesOfLength]
  | succ T ih =>
    rw [sum_HistoriesOfLength_succ_first_action R.stage T
      (fun suffix => R.publicHistoryProbFrom σ h suffix)]
    have hstep :
        ∀ c : R.stage.ActionProfile,
          ∑ rest ∈ R.stage.HistoriesOfLength T, R.publicHistoryProbFrom σ h (c :: rest) =
            R.stageProfileProb σ h c := by
      intro c
      have : ∀ rest, R.publicHistoryProbFrom σ h (c :: rest) =
          R.stageProfileProb σ h c * R.publicHistoryProbFrom σ (h ++ [c]) rest := by
        intro rest
        rw [publicHistoryProbFrom_cons, R.stepProb_eq_stageProfileProb σ h c]
      simp_rw [this, ← Finset.mul_sum, ih (h ++ [c]), mul_one]
    simp_rw [hstep]
    exact R.sum_stageProfileProb σ h

/-! ### Sub-step 3c: Uniform boundedness of periodExpectedPayoff -/

/-- The uniform bound used for the continuation-value uniqueness witness: The total absolute mass
of the stage payoffs. -/
noncomputable def payoffBound (R : RepeatedGame) : ℝ :=
  ∑ i : R.stage.Player, ∑ a : R.stage.ActionProfile, |R.stage.payoff i a|

lemma payoffBound_nonneg : 0 ≤ R.payoffBound :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- Single-coordinate bound: `|payoff i a| ≤ payoffBound` for any `(i, a)`. -/
lemma abs_payoff_le_payoffBound (i : R.stage.Player) (a : R.stage.ActionProfile) :
    |R.stage.payoff i a| ≤ R.payoffBound := by
  unfold payoffBound
  -- Pick out the (i, a) summand.
  calc |R.stage.payoff i a|
      ≤ ∑ a' : R.stage.ActionProfile, |R.stage.payoff i a'| :=
        Finset.single_le_sum (f := fun a' => |R.stage.payoff i a'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    _ ≤ ∑ i' : R.stage.Player, ∑ a' : R.stage.ActionProfile, |R.stage.payoff i' a'| :=
        Finset.single_le_sum
          (f := fun i' => ∑ a' : R.stage.ActionProfile, |R.stage.payoff i' a'|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

/-- The stage payoff is bounded by `payoffBound`. -/
lemma abs_stagePayoff_le_payoffBound (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) : |R.stagePayoff σ h i| ≤ R.payoffBound := by
  rw [R.stagePayoff_eq_sum_stageProfileProb σ h i]
  calc |∑ c : R.stage.ActionProfile, R.stageProfileProb σ h c * R.stage.payoff i c|
      ≤ ∑ c : R.stage.ActionProfile, |R.stageProfileProb σ h c * R.stage.payoff i c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : R.stage.ActionProfile, R.stageProfileProb σ h c * |R.stage.payoff i c| := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [abs_mul, abs_of_nonneg (R.stageProfileProb_nonneg σ h c)]
    _ ≤ ∑ c : R.stage.ActionProfile, R.stageProfileProb σ h c * R.payoffBound :=
        Finset.sum_le_sum (fun c _ =>
          mul_le_mul_of_nonneg_left (R.abs_payoff_le_payoffBound i c)
            (R.stageProfileProb_nonneg σ h c))
    _ = (∑ c : R.stage.ActionProfile, R.stageProfileProb σ h c) * R.payoffBound := by
        rw [← Finset.sum_mul]
    _ = R.payoffBound := by rw [R.sum_stageProfileProb σ h, one_mul]

/-- The period-`t` expected payoff is bounded by `payoffBound`. -/
lemma abs_periodExpectedPayoff_le_payoffBound (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (t : ℕ) (i : R.stage.Player) : |R.periodExpectedPayoff σ h t i| ≤ R.payoffBound := by
  unfold periodExpectedPayoff
  calc |∑ suffix ∈ R.stage.HistoriesOfLength t,
          R.publicHistoryProbFrom σ h suffix * R.stagePayoff σ (h ++ suffix) i|
      ≤ ∑ suffix ∈ R.stage.HistoriesOfLength t,
          |R.publicHistoryProbFrom σ h suffix * R.stagePayoff σ (h ++ suffix) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ suffix ∈ R.stage.HistoriesOfLength t,
          R.publicHistoryProbFrom σ h suffix * |R.stagePayoff σ (h ++ suffix) i| := by
        refine Finset.sum_congr rfl (fun suffix _ => ?_)
        rw [abs_mul, abs_of_nonneg (R.publicHistoryProbFrom_nonneg σ h suffix)]
    _ ≤ ∑ suffix ∈ R.stage.HistoriesOfLength t,
          R.publicHistoryProbFrom σ h suffix * R.payoffBound :=
        Finset.sum_le_sum (fun suffix _ =>
          mul_le_mul_of_nonneg_left (R.abs_stagePayoff_le_payoffBound σ (h ++ suffix) i)
            (R.publicHistoryProbFrom_nonneg σ h suffix))
    _ = (∑ suffix ∈ R.stage.HistoriesOfLength t,
          R.publicHistoryProbFrom σ h suffix) * R.payoffBound := by
        rw [← Finset.sum_mul]
    _ = R.payoffBound := by rw [R.pathProb_sum_one σ h t, one_mul]

/-! ### Sub-step 4: ContinuationValue Bellman shift and final assembly -/

/-- Summability of the discounted period-expected-payoff sequence. -/
lemma summable_discount_periodExpectedPayoff (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) :
    Summable (fun t : ℕ => R.discount ^ t * R.periodExpectedPayoff σ h t i) := by
  -- Compare against the geometric series `δ^t * payoffBound` via `Summable.of_norm_bounded`.
  apply Summable.of_norm_bounded
    (g := fun t : ℕ => R.discount ^ t * R.payoffBound)
  · exact (summable_geometric_of_lt_one R.discount_nonneg R.discount_lt_one).mul_right _
  · intro t
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg R.discount_nonneg]
    exact mul_le_mul_of_nonneg_left (R.abs_periodExpectedPayoff_le_payoffBound σ h t i)
      (pow_nonneg R.discount_nonneg t)

/-- The continuation value is uniformly bounded by `payoffBound`: The normalized discounted series
of period payoffs, each bounded by `payoffBound`, telescopes against the geometric normalization
`(1 - δ) / (1 - δ)`. -/
lemma abs_continuationValue_le_payoffBound (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) : |R.continuationValue σ h i| ≤ R.payoffBound := by
  unfold continuationValue
  have h1mδ : 0 ≤ 1 - R.discount := by linarith [R.discount_lt_one]
  have h1mδ_pos : 0 < 1 - R.discount := by linarith [R.discount_lt_one]
  have hgeom : Summable (fun t : ℕ => R.discount ^ t * R.payoffBound) :=
    (summable_geometric_of_lt_one R.discount_nonneg R.discount_lt_one).mul_right _
  have hgeom_sum :
      (∑' t : ℕ, R.discount ^ t * R.payoffBound) = (1 - R.discount)⁻¹ * R.payoffBound := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one R.discount_nonneg R.discount_lt_one]
  rw [abs_mul, abs_of_nonneg h1mδ]
  have habs_le_geom : ∀ t : ℕ,
      |R.discount ^ t * R.periodExpectedPayoff σ h t i| ≤ R.discount ^ t * R.payoffBound := by
    intro t
    rw [abs_mul, abs_pow, abs_of_nonneg R.discount_nonneg]
    exact mul_le_mul_of_nonneg_left
      (R.abs_periodExpectedPayoff_le_payoffBound σ h t i)
      (pow_nonneg R.discount_nonneg t)
  have habs_summable :
      Summable (fun t : ℕ => |R.discount ^ t * R.periodExpectedPayoff σ h t i|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) habs_le_geom hgeom
  calc (1 - R.discount) * |∑' t : ℕ, R.discount ^ t * R.periodExpectedPayoff σ h t i|
      ≤ (1 - R.discount) * ∑' t : ℕ, |R.discount ^ t * R.periodExpectedPayoff σ h t i| := by
        apply mul_le_mul_of_nonneg_left _ h1mδ
        have := norm_tsum_le_tsum_norm
          (f := fun t : ℕ => R.discount ^ t * R.periodExpectedPayoff σ h t i)
          (by simpa [Real.norm_eq_abs] using habs_summable)
        simpa [Real.norm_eq_abs] using this
    _ ≤ (1 - R.discount) * ∑' t : ℕ, R.discount ^ t * R.payoffBound := by
        apply mul_le_mul_of_nonneg_left _ h1mδ
        exact Summable.tsum_le_tsum habs_le_geom habs_summable hgeom
    _ = (1 - R.discount) * ((1 - R.discount)⁻¹ * R.payoffBound) := by rw [hgeom_sum]
    _ = R.payoffBound := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h1mδ_pos), one_mul]

/-- One-step Bellman shift for `continuationValue`. -/
lemma continuationValue_eq_step (σ : R.PublicStrategy) (h : R.stage.PublicHistory)
    (i : R.stage.Player) :
    R.continuationValue σ h i =
      (1 - R.discount) * R.stagePayoff σ h i +
        R.discount * ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ h c * R.continuationValue σ (h ++ [c]) i := by
  classical
  unfold continuationValue
  -- Use tsum_eq_zero_add to split off t = 0.
  have hsum :
      Summable (fun t : ℕ => R.discount ^ t * R.periodExpectedPayoff σ h t i) :=
    R.summable_discount_periodExpectedPayoff σ h i
  rw [hsum.tsum_eq_zero_add]
  -- Discount^0 = 1; period 0 = stagePayoff (unfold directly since `periodExpectedPayoff_zero`
  -- lives below in this file).
  have hzero :
      R.discount ^ 0 * R.periodExpectedPayoff σ h 0 i = R.stagePayoff σ h i := by
    have : R.periodExpectedPayoff σ h 0 i = R.stagePayoff σ h i := by
      simp [periodExpectedPayoff, FiniteStrategicGame.HistoriesOfLength]
    rw [this]; ring
  rw [hzero]
  -- δ^(t+1) * P(t+1) = δ * (δ^t * P(t+1)). Pull out δ.
  have hshift :
      (∑' t : ℕ, R.discount ^ (t + 1) * R.periodExpectedPayoff σ h (t + 1) i) =
        R.discount * ∑' t : ℕ, R.discount ^ t * R.periodExpectedPayoff σ h (t + 1) i := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun t => ?_)
    ring
  rw [mul_add, hshift]
  -- Now we have:
  -- (1-δ) * (stagePayoff σ h i + δ * ∑' t, δ^t * P(t+1))
  --   = (1-δ) * stagePayoff + (1-δ) * δ * ∑' t, δ^t * P(t+1)
  -- Goal RHS:
  -- (1-δ) * stagePayoff + δ * ∑ c, ssp * contVal σ (h++[c]) i
  -- Need to show: (1-δ) * δ * ∑' t, δ^t * P(t+1) = δ * ∑ c, ssp * contVal σ (h++[c]) i.
  -- Substitute P(t+1) using periodExpectedPayoff_succ.
  have hperiod :
      ∀ t : ℕ, R.periodExpectedPayoff σ h (t + 1) i =
        ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ h c * R.periodExpectedPayoff σ (h ++ [c]) t i :=
    fun t => R.periodExpectedPayoff_succ σ h t i
  -- Swap tsum and finite sum.
  have hsumc :
      ∀ c : R.stage.ActionProfile,
        Summable (fun t : ℕ => R.discount ^ t *
          (R.stageProfileProb σ h c * R.periodExpectedPayoff σ (h ++ [c]) t i)) := by
    intro c
    have := (R.summable_discount_periodExpectedPayoff σ (h ++ [c]) i).mul_left
      (R.stageProfileProb σ h c)
    simp_rw [mul_comm (R.stageProfileProb σ h c) _, mul_assoc] at this
    convert this using 1
    funext t
    ring
  have htsum :
      (∑' t : ℕ, R.discount ^ t * R.periodExpectedPayoff σ h (t + 1) i) =
        ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ h c *
            ∑' t : ℕ, R.discount ^ t * R.periodExpectedPayoff σ (h ++ [c]) t i := by
    simp_rw [hperiod, Finset.mul_sum]
    rw [Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← tsum_mul_left]
      refine tsum_congr (fun t => ?_)
      ring
    · intro c _; exact hsumc c
  rw [htsum]
  -- Both sides are sums of two terms; the first matches; the second needs
  -- `(1-δ) * δ * X = δ * (1-δ) * X` and pulling `(1-δ)` through the finite sum.
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

/-! ### Step E: Bridge to nodeStepValue and final discharge -/

/-- The repeated game as an extensive game.

Continuation values are defined directly in terms of the discounted geometric series of expected
stage payoffs along reach distributions induced by `σ`. The unilateral-deviation relation is the
canonical `ExtensiveForm.unilateralDeviation`, and subgame perfection is derived via
`ExtensiveGame.IsSubgamePerfectEquilibrium`. The continuation value satisfies a node-local Bellman
equation with `stepPayoff h a i = (1 - δ) · u_i(a)` and discount `δ`, and the uniqueness clause
holds because `δ < 1` together with the uniform bound on stage payoffs. -/
noncomputable def toExtensiveGame : ExtensiveGame R.stage.Player R.stage.ActionProfile where
  toExtensiveForm := R.toExtensiveForm
  stepPayoff h a i := (1 - R.discount) * R.stage.payoff i a
  discount := R.discount
  discount_mem := ⟨R.discount_nonneg, R.discount_lt_one.le⟩
  no_chanceGeneral := by
    intro h n hk
    cases hk
  continuationValue σ h i := R.continuationValue σ h i
  continuationValue_eq := by
    intro σ h i
    rw [R.continuationValue_eq_step σ h i]
    have hkind : R.toExtensiveForm.tree.nodeKind h = .joint R.stageJointNode := rfl
    change _ = nodeStepValue R.toExtensiveForm σ h i
          (.joint R.stageJointNode) hkind (by simp)
          (fun h a i => (1 - R.discount) * R.stage.payoff i a) R.discount
          R.continuationValue
    rw [nodeStepValue_joint]
    have hprod_eq :
        ∀ c : R.stage.ActionProfile,
          (∏ a : R.stageJointNode.Active, (σ.jointBehavior h hkind a).val (c a)) =
            R.stageProfileProb σ h c := by
      intro c
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact R.jointBehavior_val_eq_atHistory_val σ h j (c j)
    change (1 - R.discount) * R.stagePayoff σ h i +
        R.discount * ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ h c * R.continuationValue σ (h ++ [c]) i =
      ∑ c : R.stage.ActionProfile,
        (∏ a : R.stage.Player, (σ.jointBehavior h hkind a).val (c a)) *
          ((1 - R.discount) * R.stage.payoff i c +
            R.discount * R.continuationValue σ (h ++ [c]) i)
    have hRHS_pt : ∀ c : R.stage.ActionProfile,
        (∏ a : R.stage.Player, (σ.jointBehavior h hkind a).val (c a)) *
            ((1 - R.discount) * R.stage.payoff i c +
              R.discount * R.continuationValue σ (h ++ [c]) i) =
          R.stageProfileProb σ h c *
            ((1 - R.discount) * R.stage.payoff i c +
              R.discount * R.continuationValue σ (h ++ [c]) i) := by
      intro c; congr 1
    simp_rw [hRHS_pt]
    rw [R.stagePayoff_eq_sum_stageProfileProb σ h i]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    ring
  continuationValue_unique :=
    Or.inr ⟨R.discount_lt_one, R.payoffBound,
      fun σ h i => R.abs_continuationValue_le_payoffBound σ h i⟩

/-- The equilibrium problem associated with repeated-game subgame perfection: It is exactly the
extensive-game subgame-perfection problem of the perfect-information lift. -/
def spePred (R : RepeatedGame) : EquilibriumProblem :=
  R.toExtensiveGame.spePred

/-- Repeated-game subgame perfection: No profitable unilateral deviation by any player at any
public history, using the extensive-game predicate on `R.toExtensiveGame`. -/
def IsSubgamePerfectEquilibrium (R : RepeatedGame) (σ : R.PublicStrategy) : Prop :=
  R.spePred.IsEquilibrium σ

/-- Repeated-game subgame perfection is the extensive-game predicate on the lift. -/
@[simp] lemma IsSubgamePerfectEquilibrium_iff (σ : R.PublicStrategy) :
    R.IsSubgamePerfectEquilibrium σ ↔ R.toExtensiveGame.IsSubgamePerfectEquilibrium σ :=
  Iff.rfl

/-- Specialization of the canonical extensive-form unilateral-deviation predicate to the repeated
game: Per-coordinate equality at every off-deviator info set. -/
lemma toExtensiveForm_unilateralDeviation_iff (R : RepeatedGame) (i : R.stage.Player)
    (σ σ' : R.PublicStrategy) :
    R.toExtensiveForm.unilateralDeviation i σ σ' ↔
      ∀ (j : R.stage.Player) (obs : R.toExtensiveForm.info.Obs j), j ≠ i →
        σ' j obs = σ j obs := Iff.rfl

@[simp] lemma stageProfileDist_apply (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (a : R.stage.ActionProfile) :
    R.stageProfileDist σ h a = R.stageProfileProb σ h a := rfl

@[simp] lemma periodExpectedPayoff_zero (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (i : R.stage.Player) :
    R.periodExpectedPayoff σ h 0 i = R.stagePayoff σ h i := by
  simp [periodExpectedPayoff, FiniteStrategicGame.HistoriesOfLength]

/-- The continuationValue field of `R.toExtensiveGame` is, by construction, the repeated-game
continuation value. -/
@[simp] lemma toExtensiveGame_continuationValue (σ : R.PublicStrategy)
    (h : R.stage.PublicHistory) (i : R.stage.Player) :
    R.toExtensiveGame.continuationValue σ h i = R.continuationValue σ h i := rfl

/-- For the repeated-game extensive form, any one-shot information-set deviation is a (canonical)
unilateral deviation. The substrate predicates are per-coordinate. -/
lemma toExtensiveGame_infoSetDeviation_unilateral (R : RepeatedGame)
    (σ : R.PublicStrategy) (i : R.stage.Player)
    (obs : R.toExtensiveForm.info.Obs i) (σ' : R.PublicStrategy)
    (h_dev : IsInfoSetDeviation R.toExtensiveForm i obs σ σ') :
    R.toExtensiveForm.unilateralDeviation i σ σ' := fun j obs' hj =>
  h_dev j obs' (fun heq => hj (by cases heq; rfl))

/-- In perfect-monitoring repeated games, every public-strategy SPE induces a PBE of the associated
perfect-information extensive game with singleton beliefs.

Sequential rationality follows because under perfect info with `trivialBeliefs`, the assessment
value at observation `obs` collapses to the continuation value at history `obs`; the (full)
sequential-rationality deviation is already a unilateral deviation, so subgame perfection rules it
out directly. Bayes consistency is `trivialBeliefs` consistency under perfect information
(`IsBayesConsistent_trivialBeliefs_perfectInfo`). -/
theorem IsPerfectBayesianEquilibrium_toExtensiveGame_of_IsSubgamePerfectEquilibrium
    (σ : R.PublicStrategy) (hspe : R.IsSubgamePerfectEquilibrium σ) :
    IsPerfectBayesianEquilibrium R.toExtensiveGame
      { strategy := σ
        beliefs := trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree } := by
  classical
  have hmoves : ∀ (i : R.stage.Player) (obs : List R.stage.ActionProfile),
      (R.toGameTree.nodeKind obs).movesAt i := fun i _ => ⟨i, rfl⟩
  refine ⟨?_, ?_⟩
  · intro i obs σ' h_dev
    have hvalue_eq :
        ∀ (s : R.toExtensiveForm.BehavioralStrategy),
          assessmentValue R.toExtensiveGame
            { strategy := s
              beliefs := trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree }
              i obs =
            R.toExtensiveGame.continuationValue s obs i := by
      intro s
      have key :
          assessmentValue R.toExtensiveGame
              { strategy := s
                beliefs := trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree }
              i obs =
            (trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree).belief i obs
              ⟨obs, hmoves i obs, rfl⟩ *
              R.toExtensiveGame.continuationValue s obs i := by
        change ∑ x ∈ (trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree).support
                i obs,
            (trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree).belief i obs x *
              R.toExtensiveGame.continuationValue s x.1 i = _
        have hsupp :
            (trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree).support i obs =
              ({⟨obs, hmoves i obs, rfl⟩} :
                Finset (R.toExtensiveForm.InfoSet i obs)) := by
          change (if hm' : (R.toGameTree.nodeKind obs).movesAt i then
                    ({⟨obs, hm', rfl⟩} :
                      Finset (R.toExtensiveForm.InfoSet i obs))
                  else ∅) = _
          rw [dif_pos (hmoves i obs)]
        rw [hsupp]
        exact Finset.sum_singleton
          (fun x : R.toExtensiveForm.InfoSet i obs =>
            (trivialBeliefs R.stage.Player R.stage.ActionProfile R.toGameTree).belief i obs x *
              R.toExtensiveGame.continuationValue s x.1 i)
          ⟨obs, hmoves i obs, rfl⟩
      rw [key]
      change (1 : ℝ) * _ = _
      rw [one_mul]
    rw [hvalue_eq, hvalue_eq]
    exact hspe (i, obs) σ' h_dev
  · exact IsBayesConsistent_trivialBeliefs_perfectInfo R.toGameTree σ

/-- A pure grim-trigger or Nash-reversion action rule.

These rules are convenient witnesses for repeated-game equilibria but require a separate
pure-action lift to land in `R.PublicStrategy`. This construction returns the chosen pure action at
each public history and is independent of the strategy carrier. -/
def grimTrigger (cooperate punish : R.stage.ActionProfile) :
    (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i :=
  fun i h => if ∀ a ∈ h, a = cooperate then cooperate i else punish i

/-- A payoff vector for the stage-game players. -/
abbrev PayoffVector := R.stage.Player → ℝ

/-- A payoff vector is feasible if it is generated by a pure stage-game action profile. Later
extensions can replace this with the convex hull generated by mixed/public randomization. -/
def IsPureFeasiblePayoff (w : R.PayoffVector) : Prop :=
  ∃ a : R.stage.ActionProfile, ∀ i, w i = R.stage.payoff i a

/-- All target payoff vectors in `W` are feasible for the repeated stage game. -/
def IsFeasiblePayoffSet (W : Set R.PayoffVector) : Prop :=
  ∀ w ∈ W, R.IsPureFeasiblePayoff w

/-- The pure-action minmax benchmark for player `i`: The lowest payoff opponents can hold `i` to if
`i` best-responds to each opponent profile. Concretely, `min_{a₋ᵢ} max_{aᵢ} payoff i (aᵢ, a₋ᵢ)`,
taken over pure stage-game action profiles. The quantification ranges over full `ActionProfile`s
but the inner `Function.update a i aᵢ` overwrites `a i`, so only the opponents' coordinates matter
in the outer minimum. -/
def MinmaxValue (i : R.stage.Player) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun a : R.stage.ActionProfile =>
    Finset.univ.sup' Finset.univ_nonempty fun aᵢ : R.stage.Action i =>
      R.stage.payoff i (Function.update a i aᵢ)

/-- Target payoffs are individually rational relative to the pure-action minmax benchmark. -/
def IsIndividuallyRationalPayoffSet (W : Set R.PayoffVector) : Prop :=
  ∀ w ∈ W, ∀ i, R.MinmaxValue i ≤ w i

/-- The discount factor is above a threshold required by a folk-theorem construction. -/
structure IsSufficientlyPatient (δ₀ : ℝ) : Prop where
  /-- The threshold is below one. -/
  lt_one : δ₀ < 1
  /-- The discount factor clears the threshold. -/
  discount_ge : δ₀ ≤ R.discount

/-- A finite-dimensional richness condition for target payoffs: Some target payoff strictly clears
all minmax bounds. -/
def HasFullDimensionalPayoffWitness (W : Set R.PayoffVector) : Prop :=
  ∃ w ∈ W, ∀ i, R.MinmaxValue i < w i

/-- A set of payoff vectors is self-generating if every payoff vector in it can be decomposed into
a current action profile and continuation payoff vector in the set. -/
def IsSelfGenerating (W : Set R.PayoffVector) : Prop :=
  ∀ w ∈ W, ∃ (a : R.stage.ActionProfile) (v : R.PayoffVector), v ∈ W ∧
    ∀ i, w i = (1 - R.discount) * R.stage.payoff i a + R.discount * v i

end RepeatedGame

end Econlib.GameTheory
