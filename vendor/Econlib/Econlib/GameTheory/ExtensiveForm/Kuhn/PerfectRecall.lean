/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Kuhn.Maps
public import Econlib.GameTheory.ExtensiveForm.Kuhn.PathConsistency
public import Econlib.GameTheory.ExtensiveForm.Kuhn.Recall

/-!
# Perfect recall

This file formalizes **perfect recall** (Kuhn 1953): A game has perfect recall iff each player is
allowed by the rules of the game to remember everything he knew at previous moves and all of his
choices at those moves. Concretely, whenever two reachable histories lie in the same information
set of player `i`, the **experience** player `i` accumulated reaching them — the ordered list of
`(information set, action taken)` pairs at `i`'s own prior decision nodes — must be identical
(`FiniteExtensiveForm.IsPerfectRecall`).

The experience-based predicate carries the canonical perfect-recall name and entails the named
recall consequences used elsewhere in the extensive-form API: No information-set revisits,
representative-independent action recall, last-stop alignment, and reach coherence.

## Notes

A player's "choice" at one of her decision nodes is an element of the information-set action type
`infoSetChoiceForObs i (observe i h)`, shared across the information set (by `iChoice_compatible`).
It is not the emitted public event: Two nodes in the same information set may label the same action
with different events (`n.emit` can differ node-to-node), so recording the emitted event would fail
to imply `ActionRecall`. We recover the action taken from the realized event using
`has_injective_emit`, transported into the shared action type — exactly the data a player is said
to remember.

## Main definitions

* `FiniteExtensiveForm.iRealizedAction`: The action `i` takes at a reachable decision node, read
  off the realized continuation event.
* `FiniteExtensiveForm.iExperience`: Player `i`'s experience (list of `(info set, action)` pairs)
  along a history.
* `FiniteExtensiveForm.IsPerfectRecall`: The perfect-recall predicate (experience constant across
  an information set).
* `FiniteExtensiveForm.ActionRecall`: Representative-independence of `iPathConsistent` — the
  minimal realization-equivalence recall consequence.
* `PerfectRecallFiniteExtensiveForm`: A finite extensive form bundled with a perfect-recall witness.

## Main statements

* `FiniteExtensiveForm.IsPerfectRecall.actionRecall`
* `FiniteExtensiveForm.IsPerfectRecall.noInfoSetRevisit`

## Tags

extensive form, perfect recall, kuhn theorem, experience, action recall
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace NodeKind

/-- A node-local pure choice that emits the event `e`: At a player node, a
`Classical.choose`-picked choice with `n.emit c = e` (default if none emits `e`); at
terminal/chance/joint nodes a default pure choice (no single-event recovery is needed there). Used
to read a player's *action* off the realized continuation event. -/
noncomputable def choiceEmitting [DecidableEq E] : (k : NodeKind I E) → E → k.PureChoice
  | .terminal _, _ => PUnit.unit
  | .player n, e =>
      open Classical in
      (if h : ∃ c : n.Choice, n.emit c = e then h.choose else (default : n.Choice))
  | .joint n, _ => (default : (a : n.Active) → n.Choice a)
  | .chanceFinite _, _ => PUnit.unit
  | .chanceGeneral _, _ => PUnit.unit

/-- At a player node, the recovered choice indeed emits `e` whenever some choice does. -/
lemma emit_choiceEmitting [DecidableEq E] {n : PlayerNode I E} (e : E)
    (he : ∃ c : n.Choice, n.emit c = e) :
    n.emit ((NodeKind.player n).choiceEmitting e) = e := by
  classical
  change n.emit (if h : ∃ c : n.Choice, n.emit c = e then h.choose else default) = e
  rw [dif_pos he]
  exact he.choose_spec

end NodeKind

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-- The **action player `i` takes** at history `pre`, read off the realized next event `e`. At a
reachable history where `i` moves, this is the (unique, by `has_injective_emit`) choice emitting
`e`, transported into the shared information-set action type
`infoSetChoiceForObs i (observe i pre)`. Off the diagonal (unreachable, or `i` not moving) it is
the default action — these branches never occur when reading the experience of a reachable
history. -/
noncomputable def iRealizedAction (i : I) (pre : List E) (e : E) :
    G.infoSetChoiceForObs i (G.info.observe i pre) :=
  open Classical in
  if h : pre ∈ G.reach ∧ (G.tree.nodeKind pre).movesAt i then
    cast (G.pureChoice_eq_canonicalRep i pre h.1 h.2) ((G.tree.nodeKind pre).choiceEmitting e)
  else default

/-- Player `i`'s **experience** along the continuation `path` from `pre`: The ordered list of
`⟨information set, action taken⟩` pairs at every prefix where `i` moves. -/
noncomputable def iExperienceFrom (G : FiniteExtensiveForm I E) (i : I) :
    (pre : List E) → (path : List E) → List (Σ obs : G.info.Obs i, G.infoSetChoiceForObs i obs)
  | _pre, [] => []
  | pre, e :: rest =>
      (open Classical in
        if (G.tree.nodeKind pre).movesAt i then
          [⟨G.info.observe i pre, G.iRealizedAction i pre e⟩]
        else []) ++ iExperienceFrom G i (pre ++ [e]) rest

/-- Player `i`'s experience along a history from the root: The ordered list of
`⟨information set, action taken⟩` pairs at `i`'s own decision nodes. This is the object textbook
perfect recall requires to be constant across an information set. -/
noncomputable def iExperience (i : I) (h : List E) :
    List (Σ obs : G.info.Obs i, G.infoSetChoiceForObs i obs) :=
  iExperienceFrom G i [] h

/-- **Perfect recall** (Kuhn 1953). Any two reachable histories in the same information set of
player `i` induce the *same* experience for `i`: The same ordered sequence of information sets
visited and actions chosen at `i`'s own prior decision nodes. This is "each player remembers
everything he knew at previous moves and all of his choices at those moves." -/
def IsPerfectRecall (G : FiniteExtensiveForm I E) : Prop :=
  ∀ (i : I) (h₁ h₂ : List E),
    h₁ ∈ G.reach → h₂ ∈ G.reach →
    (G.tree.nodeKind h₁).movesAt i → (G.tree.nodeKind h₂).movesAt i →
    G.info.observe i h₁ = G.info.observe i h₂ →
    G.iExperience i h₁ = G.iExperience i h₂

/-! ## Path consistency is a function of the experience

The action-recall content: `iPathConsistent i c h` reads `c`'s choice at each of `i`'s decision
nodes and tests it against the action realized there. We show it is literally a fold over
`iExperience i h`, so two histories with equal experience impose identical consistency on every
pure strategy `c`. -/

/-- The consistency weight of a pure strategy `c` against an experience list: The product over
entries `⟨obs, a⟩` of the `0/1` indicator that `c` selects action `a` at information set `obs`. -/
noncomputable def expConsistency (i : I)
    (c : G.PureStrategy i) (L : List (Σ obs : G.info.Obs i, G.infoSetChoiceForObs i obs)) : ℝ :=
  (L.map (fun entry => if c entry.1 = entry.2 then (1 : ℝ) else 0)).prod

/-- **Per-step action read-off.** At a reachable history where `i` moves and `e` is an emitted
event, the path-consistency step indicator equals the `0/1` test that `c`'s information-set action
matches the action realized by `e`. The crux uses `has_injective_emit` to convert "the chosen
choice emits `e`" into "the chosen choice *is* the action realized by `e`." -/
lemma iStepIndicator_eq_indicator [DecidableEq E] [DecidableEq I] (i : I) (c : G.PureStrategy i)
    (pre : List E) (hr : pre ∈ G.reach) (hm : (G.tree.nodeKind pre).movesAt i) (e : E)
    (he : (G.tree.nodeKind pre).emits e) :
    G.iStepIndicator i c pre e =
      (if c (G.info.observe i pre) = G.iRealizedAction i pre e then 1 else 0) := by
  classical
  rcases hk : G.tree.nodeKind pre with payoff | n | n | n | n
  · rw [hk] at hm; exact absurd hm id
  · have hmover : n.mover = i := by rw [hk] at hm; exact hm
    subst hmover
    rw [G.iStepIndicator_of_player n.mover c hk rfl e]
    have hQ : (G.tree.nodeKind pre).PureChoice = n.Choice := by rw [hk]; rfl
    have hlook : G.lookupPlayerChoice (G.singletonProfile n.mover c) pre n hk =
        cast hQ (c.applyAt pre hr hm) := by
      unfold lookupPlayerChoice
      rw [dif_pos hr]
      have hprofile : G.singletonProfile n.mover c n.mover = c := by
        unfold singletonProfile; rw [Function.update_self]
      rw [hprofile]
    rw [hlook]
    set obs := G.info.observe n.mover pre with hobs
    have hP : (G.tree.nodeKind pre).PureChoice =
        (G.tree.nodeKind (G.canonicalRep n.mover obs)).PureChoice :=
      G.pureChoice_eq_canonicalRep n.mover pre hr hm
    set ce : n.Choice := (NodeKind.player n).choiceEmitting e with hce
    have hce_emit : n.emit ce = e := by
      have he' : ∃ d : n.Choice, n.emit d = e := by rw [hk] at he; exact he
      exact NodeKind.emit_choiceEmitting e he'
    have hcast_hk : cast hQ ((G.tree.nodeKind pre).choiceEmitting e) = ce := by
      rw [hce]
      apply cast_eq_iff_heq.mpr
      rw [hk]
      exact HEq.rfl
    have hraw : G.iRealizedAction n.mover pre e =
        cast hP ((G.tree.nodeKind pre).choiceEmitting e) := by
      rw [iRealizedAction,
        dif_pos (⟨hr, hm⟩ : pre ∈ G.reach ∧ (G.tree.nodeKind pre).movesAt n.mover)]
      congr 1
      exact congrFun (congrFun (congrArg _ (Subsingleton.elim _ _)) _) _
    have happly : c.applyAt pre hr hm = cast hP.symm (c obs) := rfl
    have hinj : Function.Injective n.emit := G.has_injective_emit pre n hk
    -- The injectivity of `emit` converts "emits `e`" to "is the recovered action" —
    -- the crux linking the event-level indicator to the info-set action comparison.
    have hemitX : n.emit (cast hQ ((G.tree.nodeKind pre).choiceEmitting e)) = e := by
      rw [hcast_hk]; exact hce_emit
    have hkey : (n.emit (cast hQ (c.applyAt pre hr hm)) = e) ↔
        (c.applyAt pre hr hm = (G.tree.nodeKind pre).choiceEmitting e) := by
      constructor
      · intro hL
        exact (cast_inj hQ).mp (hinj (hL.trans hemitX.symm))
      · intro hR
        rw [hR]; exact hemitX
    have hcond : (n.emit (cast hQ (c.applyAt pre hr hm)) = e) ↔
        (c obs = G.iRealizedAction n.mover pre e) := by
      rw [hkey, happly, hraw, cast_eq_iff_heq]
      exact (eq_cast_iff_heq).symm
    rw [if_congr hcond rfl rfl]
  · exact absurd hk (G.no_joint pre n)
  · rw [hk] at hm; exact absurd hm id
  · exact absurd hk (G.no_general_chance pre n)

/-- **Prefixes of a reachable history are reachable.** Reproved locally from the `IsReachable`
inductive, since the general copy lives in a downstream module. -/
private lemma reach_prefix_mem (h_full h_pre : List E) (h_reach : h_full ∈ G.reach)
    (h_prefix : h_pre <+: h_full) : h_pre ∈ G.reach := by
  rw [G.mem_reach_iff] at h_reach ⊢
  obtain ⟨rest, hrfl⟩ := h_prefix
  have hpe : h_pre = h_full.take h_pre.length := by rw [← hrfl, List.take_left]
  rw [hpe]
  clear hpe hrfl rest
  induction h_reach with
  | root => simp only [List.take_nil]; exact ExtensiveForm.IsReachable.root
  | step h_path e hr he ih =>
      by_cases hk : h_pre.length ≤ h_path.length
      · rw [List.take_append_of_le_length hk]; exact ih
      · have hlen : (h_path ++ [e]).take h_pre.length = h_path ++ [e] := by
          apply List.take_of_length_le
          rw [List.length_append]; simp only [List.length_singleton]; omega
        rw [hlen]
        exact ExtensiveForm.IsReachable.step h_path e hr he

/-- **Reachability inversion at a step.** If `pre ++ [e]` is reachable then `pre`'s node emits `e`.
Reproved locally for the same import-order reason as `reach_prefix_mem`. -/
private lemma emits_of_concat_mem (pre : List E) (e : E) (h : (pre ++ [e]) ∈ G.reach) :
    (G.tree.nodeKind pre).emits e := by
  rw [G.mem_reach_iff] at h
  generalize hzx : pre ++ [e] = zx at h
  cases h with
  | root => exact absurd hzx (by simp)
  | step h' e' hr he =>
      obtain ⟨rfl, he2⟩ := List.append_inj' hzx rfl
      obtain rfl : e = e' := by injection he2
      exact he

/-- **`iPathConsistent` is a fold over the experience** (from an arbitrary reachable anchor along a
reachable continuation). -/
lemma iPathConsistentFrom_eq_expConsistency [DecidableEq E] [DecidableEq I] (i : I)
    (c : G.PureStrategy i) (pre path : List E)
    (hr : pre ∈ G.reach) (hrp : (pre ++ path) ∈ G.reach) :
    G.iPathConsistentFrom i c pre path = G.expConsistency i c (G.iExperienceFrom i pre path) := by
  classical
  induction path generalizing pre with
  | nil => simp [iPathConsistentFrom, expConsistency, iExperienceFrom]
  | cons e rest ih =>
      -- Peel the first step: `pre ++ [e]` is a reachable prefix, so `e` is emitted at `pre`.
      have hre : (pre ++ [e]) ∈ G.reach := by
        apply G.reach_prefix_mem (pre ++ e :: rest) (pre ++ [e]) hrp
        exact ⟨rest, by rw [List.append_assoc, List.cons_append, List.nil_append]⟩
      have hrest : ((pre ++ [e]) ++ rest) ∈ G.reach := by
        rw [List.append_assoc, List.cons_append, List.nil_append]; exact hrp
      have hemit : (G.tree.nodeKind pre).emits e := G.emits_of_concat_mem pre e hre
      rw [iPathConsistentFrom, iExperienceFrom]
      rw [expConsistency, List.map_append, List.prod_append, ← expConsistency, ← expConsistency,
        ih (pre ++ [e]) hre hrest]
      by_cases hm : (G.tree.nodeKind pre).movesAt i
      · rw [if_pos hm, G.iStepIndicator_eq_indicator i c pre hr hm e hemit]
        simp [expConsistency]
      · rw [if_neg hm, G.iStepIndicator_of_not_movesAt i c pre e hm]
        simp [expConsistency]

/-- **`iPathConsistent` is a fold over the experience.** Hence it depends on the history only
through `iExperience i h`. -/
lemma iPathConsistent_eq_expConsistency [DecidableEq E] [DecidableEq I] (i : I)
    (c : G.PureStrategy i) (h : List E) (hr : h ∈ G.reach) :
    G.iPathConsistent i c h = G.expConsistency i c (G.iExperience i h) := by
  unfold iPathConsistent iExperience
  exact G.iPathConsistentFrom_eq_expConsistency i c [] h G.nil_mem_reach
    (by rw [List.nil_append]; exact hr)

/-! ## Experience factorizes over concatenation (for the no-revisit argument) -/

/-- The experience of a concatenated continuation is the concatenation of the experiences. -/
lemma iExperienceFrom_append (i : I) (pre p₁ p₂ : List E) :
    G.iExperienceFrom i pre (p₁ ++ p₂) =
      G.iExperienceFrom i pre p₁ ++ G.iExperienceFrom i (pre ++ p₁) p₂ := by
  classical
  induction p₁ generalizing pre with
  | nil => simp [iExperienceFrom]
  | cons e rest ih =>
      rw [List.cons_append, iExperienceFrom, iExperienceFrom, ih (pre ++ [e]),
        List.append_assoc, List.append_assoc, List.cons_append, List.nil_append]

/-- A nonempty continuation from a history where `i` moves contributes at least one experience
entry. -/
lemma length_iExperienceFrom_pos_of_movesAt (i : I) (pre : List E) (e : E) (rest : List E)
    (hm : (G.tree.nodeKind pre).movesAt i) :
    0 < (G.iExperienceFrom i pre (e :: rest)).length := by
  classical
  rw [iExperienceFrom, if_pos hm, List.length_append, List.length_singleton]
  omega

/-- **A move-free continuation contributes no experience.** If `i` never moves at any prefix
`pre ++ path.take r` (`r < path.length`) of the continuation, then the experience accumulated along
`path` from `pre` is empty. The contrapositive feeds the "find the last `i`-move" step. -/
lemma iExperienceFrom_eq_nil_of_no_movesAt (i : I) (pre path : List E)
    (hno : ∀ r : ℕ, r < path.length → ¬ (G.tree.nodeKind (pre ++ path.take r)).movesAt i) :
    G.iExperienceFrom i pre path = [] := by
  classical
  induction path generalizing pre with
  | nil => rfl
  | cons e rest ih =>
      have hhead : ¬ (G.tree.nodeKind pre).movesAt i := by
        have := hno 0 (by simp)
        simpa using this
      rw [iExperienceFrom, if_neg hhead, List.nil_append]
      refine ih (pre ++ [e]) (fun r hr => ?_)
      have hrw : (pre ++ [e]) ++ rest.take r = pre ++ (e :: rest).take (r + 1) := by
        rw [List.take_succ_cons, List.append_assoc, List.singleton_append]
      rw [hrw]
      exact hno (r + 1) (by simpa using Nat.succ_lt_succ hr)

/-- **Nonempty experience exposes an `i`-move prefix.** If the experience accumulated along `path`
from `pre` is nonempty, some strict prefix `pre ++ path.take r` is an `i`-move node. Contrapositive
of `iExperienceFrom_eq_nil_of_no_movesAt`. -/
lemma exists_movesAt_of_iExperienceFrom_ne_nil (i : I) (pre path : List E)
    (hne : G.iExperienceFrom i pre path ≠ []) :
    ∃ r : ℕ, r < path.length ∧ (G.tree.nodeKind (pre ++ path.take r)).movesAt i := by
  classical
  by_contra hcon
  refine hne (G.iExperienceFrom_eq_nil_of_no_movesAt i pre path (fun r hr hm => hcon ⟨r, hr, hm⟩))

/-- **Last-entry decomposition of the experience.** If `m` is the *last* prefix strictly before a
history `z` at which player `i` moves (`m < z.length`, `i` moves at `z.take m`, and `i` moves at no
prefix `z.take r` with `m < r < z.length`), then `i`'s experience along `z` is `i`'s experience up
to that last move, followed by the single entry recording the information set and action taken at
that move. The realized edge `e` is the event extending `z.take m` along `z`
(`z.take (m+1) =
z.take m ++ [e]`). The tail past the last move contributes nothing because `i`
never moves there. -/
lemma iExperience_eq_lastEntry (i : I) (z : List E) (m : ℕ) (e : E)
    (hm_lt : m < z.length) (hmm : (G.tree.nodeKind (z.take m)).movesAt i)
    (hlast : ∀ r : ℕ, m < r → r < z.length → ¬ (G.tree.nodeKind (z.take r)).movesAt i)
    (he : z.take (m + 1) = z.take m ++ [e]) :
    G.iExperience i z =
      G.iExperience i (z.take m) ++
        [⟨G.info.observe i (z.take m), G.iRealizedAction i (z.take m) e⟩] := by
  classical
  -- Split `z` at `m + 1`; the experience factors over the concatenation.
  have hsplit : z = z.take (m + 1) ++ z.drop (m + 1) := (List.take_append_drop (m + 1) z).symm
  unfold iExperience
  conv_lhs => rw [hsplit]
  rw [G.iExperienceFrom_append i [] (z.take (m + 1)) (z.drop (m + 1))]
  -- The tail past the last move is move-free, hence contributes no experience.
  have htail :
      G.iExperienceFrom i ([] ++ z.take (m + 1)) (z.drop (m + 1)) = [] := by
    rw [List.nil_append]
    refine G.iExperienceFrom_eq_nil_of_no_movesAt i (z.take (m + 1)) (z.drop (m + 1)) ?_
    intro r hr
    have hcat : z.take (m + 1) ++ (z.drop (m + 1)).take r = z.take (m + 1 + r) :=
      (List.take_add).symm
    rw [hcat]
    have hlen_drop : (z.drop (m + 1)).length = z.length - (m + 1) := by
      rw [List.length_drop]
    have hr' : r < z.length - (m + 1) := by rw [hlen_drop] at hr; exact hr
    exact hlast (m + 1 + r) (by omega) (by omega)
  rw [htail, List.append_nil]
  rw [he, G.iExperienceFrom_append i [] (z.take m) [e], List.nil_append]
  have hentry :
      G.iExperienceFrom i (z.take m) [e] =
        [⟨G.info.observe i (z.take m), G.iRealizedAction i (z.take m) e⟩] := by
    rw [iExperienceFrom, iExperienceFrom, if_pos hmm, List.append_nil]
  rw [hentry]

/-! ## Action recall and the realization-equivalence consequences

Perfect recall implies the minimal recall consequences the realization-equivalence machinery
consumes: **action recall** (here) and **no information-set revisits** (`NoInfoSetRevisit`, in
`Recall.lean`). Each is a standalone predicate so a theorem can take exactly the one it needs. -/

/-- **Action recall.** Player `i`'s path-consistency weight at a reachable decision node depends
only on her information set, not on the representative history — equivalently, `i` remembers her
own past actions and the action-to-event labeling is consistent across the information set. Stated
at classical `DecidableEq` instances (bridged to ambient ones via `iPathConsistent_classical_eq`;
the `ℝ` value is `DecidableEq`-instance-independent).

This is **not** perfect recall — it is the strictly weaker recall consequence that the realization-
equivalence linchpin (`reachProb_infoSet_invariant_unilateral`) and Kuhn's converse consume.
Perfect recall implies it (`IsPerfectRecall.actionRecall`). -/
def ActionRecall (G : FiniteExtensiveForm I E) : Prop :=
  ∀ (i : I) (c : G.PureStrategy i) (h₁ h₂ : List E),
    h₁ ∈ G.reach → h₂ ∈ G.reach →
    (G.tree.nodeKind h₁).movesAt i → (G.tree.nodeKind h₂).movesAt i →
    G.info.observe i h₁ = G.info.observe i h₂ →
    @FiniteExtensiveForm.iPathConsistent I E G (Classical.decEq E) (Classical.decEq I) i c h₁ =
      @FiniteExtensiveForm.iPathConsistent I E G (Classical.decEq E) (Classical.decEq I) i c h₂

/-- **Perfect recall ⟹ action recall.** Two reachable histories in the same information set impose
identical path consistency on every pure strategy. -/
theorem IsPerfectRecall.actionRecall {G : FiniteExtensiveForm I E} (htpr : G.IsPerfectRecall) :
    G.ActionRecall := by
  intro i c h₁ h₂ hr₁ hr₂ hm₁ hm₂ hobs
  classical
  -- Bridge the classical `DecidableEq` instances to the ambient ones, then to the experience fold.
  rw [G.iPathConsistent_classical_eq i c h₁, G.iPathConsistent_classical_eq i c h₂,
    G.iPathConsistent_eq_expConsistency i c h₁ hr₁,
    G.iPathConsistent_eq_expConsistency i c h₂ hr₂]
  rw [htpr i h₁ h₂ hr₁ hr₂ hm₁ hm₂ hobs]

/-- **Perfect recall ⟹ no information-set revisits.** If a player would revisit one of her own
information sets along a reachable path, her experience would strictly grow, contradicting that
perfect recall keeps it constant across the information set. Packaged as the bare-form predicate
`ExtensiveForm.NoInfoSetRevisit` (bridging `reach` and `IsReachable` via `mem_reach_iff`). -/
theorem IsPerfectRecall.noInfoSetRevisit {G : FiniteExtensiveForm I E} (htpr : G.IsPerfectRecall) :
    G.toExtensiveForm.NoInfoSetRevisit := by
  intro i h₁ h₂ hr₁' hr₂' hpre hobs hm₁ hm₂
  classical
  have hr₁ : h₁ ∈ G.reach := (G.mem_reach_iff h₁).mpr hr₁'
  have hr₂ : h₂ ∈ G.reach := (G.mem_reach_iff h₂).mpr hr₂'
  -- Write `h₂ = h₁ ++ suf`; perfect recall forces the suffix to contribute no experience.
  obtain ⟨suf, hsuf⟩ := hpre
  have hexp : G.iExperience i h₁ = G.iExperience i h₂ :=
    htpr i h₁ h₂ hr₁ hr₂ hm₁ hm₂ hobs
  have hfac : G.iExperience i h₂ =
      G.iExperience i h₁ ++ G.iExperienceFrom i h₁ suf := by
    unfold iExperience
    rw [← hsuf, G.iExperienceFrom_append i [] h₁ suf, List.nil_append]
  have hlen : (G.iExperienceFrom i h₁ suf).length = 0 := by
    have hl := congrArg List.length (hexp.trans hfac)
    rw [List.length_append] at hl
    omega
  -- A nonempty suffix from a history where `i` moves would contribute an entry: contradiction.
  have hsuf_nil : suf = [] := by
    cases suf with
    | nil => rfl
    | cons e rest =>
        have := G.length_iExperienceFrom_pos_of_movesAt i h₁ e rest hm₁
        omega
  rw [← hsuf, hsuf_nil, List.append_nil]

end FiniteExtensiveForm

/-- A finite extensive form bundled with a perfect-recall witness. Theorems whose statements
require perfect recall (Kuhn's realization equivalence; backwards induction's well-definedness on
imperfect-information games) take this type rather than `FiniteExtensiveForm` so that the
hypothesis is type-level rather than propagated as a precondition. Its proofs consume only the
weaker recall consequences each one needs (`NoInfoSetRevisit`, `ActionRecall`), extracted from the
witness via the bridge suite. -/
structure PerfectRecallFiniteExtensiveForm (I E : Type u) extends FiniteExtensiveForm I E where
  /-- The witness that the underlying finite extensive form has perfect recall. -/
  perfectRecall : toFiniteExtensiveForm.IsPerfectRecall

namespace PerfectRecallFiniteExtensiveForm

variable (G : PerfectRecallFiniteExtensiveForm I E)

/-- The strategic-form normalization is inherited from the underlying finite extensive form. -/
noncomputable def toFiniteStrategicGame [DecidableEq E] [Fintype I] [DecidableEq I]
    [Inhabited I] : FiniteStrategicGame :=
  G.toFiniteExtensiveForm.toFiniteStrategicGame

end PerfectRecallFiniteExtensiveForm

end Econlib.GameTheory
