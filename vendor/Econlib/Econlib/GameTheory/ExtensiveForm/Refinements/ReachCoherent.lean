/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.ReachInvariance
public import Econlib.GameTheory.ExtensiveForm.Refinements.SequentialEquilibrium
public import Econlib.Math.Analysis.Convex.StdSimplex

/-!
# Reach-coherence and last-stop alignment from perfect recall

The reach-level and stop-level consequences of perfect recall that the extensive-form one-shot
deviation principle consumes: Reach-coherence (`ExtensiveForm.IsReachCoherent`) and last-stop
alignment (`ExtensiveForm.LastStopAlign`), each derived from `FiniteExtensiveForm.IsPerfectRecall`,
together with the step-probability bridges expressing a one-step probability as the behavioral mass
on the realized action.

## Main definitions

* `ExtensiveForm.IsReachCoherent`: The reach-level consequence pack of perfect recall.

## Main statements

* `IsPerfectRecall.reachCoherent`: Perfect recall implies reach-coherence.
* `FiniteExtensiveForm.IsPerfectRecall.lastStopAlign`: Perfect recall implies last-stop alignment.

## Tags

extensive form, perfect recall, reach coherence, last-stop alignment
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-- **`stepProb` reads off the emitting choice.** At a player node where `e` is emitted, the
one-step probability of `e` is exactly the behavioral mass on the (unique, by `has_injective_emit`)
choice emitting `e`. The pure-strategy analog is `iStepIndicator_eq_indicator`. -/
theorem stepProb_player_eq_choiceEmitting (G : FiniteExtensiveForm I E)
    (ρ : G.BehavioralStrategy) {h : List E} {n : PlayerNode I E}
    (hnk : G.tree.nodeKind h = .player n) {e : E} (he : ∃ c : n.Choice, n.emit c = e) :
    G.stepProb ρ h e = (ρ.playerBehavior h hnk).val ((NodeKind.player n).choiceEmitting e) := by
  classical
  -- The per-choice sum collapses: `n.emit c = e ↔ c = choiceEmitting e` by injectivity.
  rw [G.stepProb_player ρ hnk e]
  have hinj : Function.Injective n.emit := G.has_injective_emit h n hnk
  have hce_emit : n.emit ((NodeKind.player n).choiceEmitting e) = e :=
    NodeKind.emit_choiceEmitting e he
  -- Replace the `if`-condition `n.emit c = e` with `c = choiceEmitting e`, then collapse the sum.
  have hcond : ∀ c : n.Choice,
      (if n.emit c = e then (ρ.playerBehavior h hnk).val c else 0) =
        (if c = (NodeKind.player n).choiceEmitting e then (ρ.playerBehavior h hnk).val c else 0) :=
    fun c => if_congr ⟨fun hh => hinj (hh.trans hce_emit.symm), fun hh => hh ▸ hce_emit⟩ rfl rfl
  rw [Finset.sum_congr rfl (fun c _ => hcond c),
    Finset.sum_ite_eq_of_mem' Finset.univ _ _ (Finset.mem_univ _)]

/-- **`stepProb` is the behavioral mass on the realized action.** At a reachable history where `i`
moves and `e` is emitted, the one-step probability of `e` under `ρ` equals the behavioral mass `ρ`
places on the action realized by `e` at the information set `observe i h` — `iRealizedAction`
transported into the info-structure choice type via `infoSetChoiceForObs_eq_iChoiceType`. This is
the bridge that makes `stepProb` a function of the (information set, realized action) pair, hence
aligned across an information set by perfect recall. -/
theorem stepProb_eq_behavior_iRealizedAction (G : FiniteExtensiveForm I E)
    (ρ : G.BehavioralStrategy) (i : I) (h : List E) (hr : h ∈ G.reach)
    (hm : (G.tree.nodeKind h).movesAt i) {e : E} (he : (G.tree.nodeKind h).emits e) :
    G.stepProb ρ h e =
      (ρ i (G.info.observe i h)).val
        (cast (G.infoSetChoiceForObs_eq_iChoiceType i (G.info.observe i h) ⟨h, hr, rfl, hm⟩)
          (G.iRealizedAction i h e)) := by
  classical
  -- The node is a player node with `i` as mover; extract `n` without destructing the goal's casts.
  obtain ⟨n, hk, hmover⟩ := G.exists_playerNode_of_movesAt h i hm
  subst hmover
  -- `e` is emitted ⇒ some choice emits it; `choiceEmitting e` is that choice.
  have he' : ∃ c : n.Choice, n.emit c = e := by rw [hk] at he; exact he
  rw [stepProb_player_eq_choiceEmitting G ρ hk he']
  -- Transport `playerBehavior` to `ρ n.mover (observe n.mover h)` (the `atHistory` HEq).
  have hheq : HEq (ρ.playerBehavior h hk) (ρ n.mover (G.info.observe n.mover h)) :=
    (cast_heq _ _).trans (ρ.atHistory_player_heq hk)
  have hmm : (G.tree.nodeKind h).movesAt n.mover := by rw [hk]; rfl
  have hcompat : (G.tree.nodeKind h).iChoiceTypeAt n.mover hmm =
      G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    G.iChoice_compatible n.mover h hmm
  have hbridge : (G.tree.nodeKind h).iChoiceTypeAt n.mover hmm = n.Choice := by
    clear hcompat; revert hmm; rw [hk]; intro _; rfl
  have hchoice : n.Choice = G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    (hcompat.symm.trans hbridge).symm
  rw [stdSimplex.heq_val hchoice (ρ.playerBehavior h hk)
    (ρ n.mover (G.info.observe n.mover h)) hheq ((NodeKind.player n).choiceEmitting e)]
  -- The two transported simplex arguments agree. Both are transports of `choiceEmitting e`.
  -- `iRealizedAction` at this reachable player node is `cast P ((nodeKind h).choiceEmitting e)`.
  have hraw : G.iRealizedAction n.mover h e =
      cast (G.pureChoice_eq_canonicalRep n.mover h hr hmm)
        ((G.tree.nodeKind h).choiceEmitting e) := by
    rw [FiniteExtensiveForm.iRealizedAction,
      dif_pos (⟨hr, hmm⟩ : h ∈ G.reach ∧ (G.tree.nodeKind h).movesAt n.mover)]
    -- `choiceEmitting` depends on `DecidableEq E` only up to the instance subsingleton.
    congr 1
    exact congrFun (congrFun (congrArg _ (Subsingleton.elim _ _)) _) _
  -- The two simplex arguments are equal: both transport `(nodeKind h).choiceEmitting e`.
  have harg :
      (hchoice ▸ (NodeKind.player n).choiceEmitting e :
        G.info.iChoiceType n.mover (G.info.observe n.mover h)) =
      cast (G.infoSetChoiceForObs_eq_iChoiceType n.mover (G.info.observe n.mover h)
          ⟨h, hr, rfl, hmm⟩) (G.iRealizedAction n.mover h e) := by
    apply eq_of_heq
    -- LHS `hchoice ▸ (player n).choiceEmitting e ≍ (nodeKind h).choiceEmitting e` (via `hk`).
    have hL : HEq ((hchoice ▸ (NodeKind.player n).choiceEmitting e :
        G.info.iChoiceType n.mover (G.info.observe n.mover h)))
        ((G.tree.nodeKind h).choiceEmitting e) := by
      refine (eqRec_heq_self _ _).trans ?_
      rw [hk]
      exact HEq.rfl
    -- RHS `cast hTC (iRealizedAction) ≍ (nodeKind h).choiceEmitting e` (via `hraw`).
    have hR : HEq
        (cast (G.infoSetChoiceForObs_eq_iChoiceType n.mover (G.info.observe n.mover h)
            ⟨h, hr, rfl, hmm⟩) (G.iRealizedAction n.mover h e))
        ((G.tree.nodeKind h).choiceEmitting e) := by
      refine (cast_heq _ _).trans ?_
      rw [hraw]
      exact cast_heq _ _
    exact hL.trans hR.symm
  rw [harg]

/-- **Perfect recall implies last-stop alignment.** Two reachable histories in the same information
set of `i` have, by perfect recall, identical experiences; the last entries of those experiences
determine both the information set and the action taken at `i`'s last prior move, which is the
aligned stop. The strategy-quantified `stepProb` equality holds because the matched action fixes
the behavioral mass on the realized edge at the common information set. -/
theorem FiniteExtensiveForm.IsPerfectRecall.lastStopAlign
    {G : FiniteExtensiveForm I E} (htpr : G.IsPerfectRecall) :
    G.toExtensiveForm.LastStopAlign := by
  classical
  intro i z w hz hw hmz hmw hobs m hm_lt hmm hlast
  -- Reachability of `z`, `w` as `reach`-membership.
  have hzr : z ∈ G.reach := (G.mem_reach_iff z).mpr hz
  have hwr : w ∈ G.reach := (G.mem_reach_iff w).mpr hw
  -- `z`'s realized edge at its last `i`-move: `z[m]`, with `z.take (m+1) = z.take m ++ [z[m]]`.
  set ez : E := z[m]'hm_lt with hez_def
  have hz_e : z.take (m + 1) = z.take m ++ [ez] := List.take_succ_eq_append_getElem hm_lt
  -- `z`'s experience ends in the entry recording its last `i`-move.
  have hexp_z : G.iExperience i z =
      G.iExperience i (z.take m) ++
        [⟨G.info.observe i (z.take m), G.iRealizedAction i (z.take m) ez⟩] :=
    G.iExperience_eq_lastEntry i z m ez hm_lt hmm hlast hz_e
  -- Perfect recall: `z` and `w` (same info set) have identical experiences.
  have hexp_eq : G.iExperience i z = G.iExperience i w :=
    htpr i z w hzr hwr hmz hmw hobs
  -- `w`'s experience is nonempty (equals `z`'s, which ends in an entry), so some prefix is an
  -- `i`-move. Take the LAST such prefix index as `m'`.
  have hw_exp_ne : G.iExperience i w ≠ [] := by
    rw [← hexp_eq, hexp_z]; exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  obtain ⟨r₀, hr₀_lt, hr₀_move⟩ :
      ∃ r : ℕ, r < w.length ∧ (G.tree.nodeKind (w.take r)).movesAt i := by
    have := G.exists_movesAt_of_iExperienceFrom_ne_nil i [] w (by rwa [iExperience] at hw_exp_ne)
    simpa using this
  -- `m'` is the greatest `i`-move index below `w.length` (search up to `w.length - 1`).
  set P : ℕ → Prop := fun r => (G.tree.nodeKind (w.take r)).movesAt i with hP_def
  set m' : ℕ := Nat.findGreatest P (w.length - 1) with hm'_def
  have hr₀_le : r₀ ≤ w.length - 1 := by omega
  have hm'_move : P m' := Nat.findGreatest_spec hr₀_le hr₀_move
  have hm'_lt : m' < w.length := by
    have := Nat.findGreatest_le (P := P) (w.length - 1)
    omega
  have hm'_last : ∀ r : ℕ, m' < r → r < w.length → ¬ P r := by
    intro r hgt hlt
    exact Nat.findGreatest_is_greatest hgt (by omega)
  -- `w`'s realized edge at `m'`: `w[m']`.
  set ew : E := w[m']'hm'_lt with hew_def
  have hw_e : w.take (m' + 1) = w.take m' ++ [ew] := List.take_succ_eq_append_getElem hm'_lt
  -- Again for `w` at its last `i`-move `m'`.
  have hexp_w : G.iExperience i w =
      G.iExperience i (w.take m') ++
        [⟨G.info.observe i (w.take m'), G.iRealizedAction i (w.take m') ew⟩] :=
    G.iExperience_eq_lastEntry i w m' ew hm'_lt hm'_move hm'_last hw_e
  -- The last entries of the two equal experiences coincide.
  have hlast_eq :
      (⟨G.info.observe i (z.take m), G.iRealizedAction i (z.take m) ez⟩ :
        Σ obs : G.info.Obs i, G.infoSetChoiceForObs i obs) =
      ⟨G.info.observe i (w.take m'), G.iRealizedAction i (w.take m') ew⟩ := by
    have hcat : G.iExperience i (z.take m) ++
          [(⟨G.info.observe i (z.take m), G.iRealizedAction i (z.take m) ez⟩ :
            Σ obs : G.info.Obs i, G.infoSetChoiceForObs i obs)] =
        G.iExperience i (w.take m') ++
          [⟨G.info.observe i (w.take m'), G.iRealizedAction i (w.take m') ew⟩] := by
      rw [← hexp_z, hexp_eq, hexp_w]
    have := congrArg List.getLast? hcat
    rwa [List.getLast?_concat, List.getLast?_concat, Option.some.injEq] at this
  -- Unpack the Sigma equality: equal observations + heterogeneously-equal realized actions.
  obtain ⟨hobs_eq, haction_heq⟩ := Sigma.ext_iff.mp hlast_eq
  -- Reachability of the two stop nodes (prefixes of reachable `z`, `w`).
  have hzm_reach : z.take m ∈ G.reach := G.reach_take_of_reach z hzr m
  have hwm_reach : w.take m' ∈ G.reach := G.reach_take_of_reach w hwr m'
  -- Assemble the aligned stop `m'`.
  refine ⟨m', hm'_lt, hm'_move, hobs_eq.symm, hm'_last, ?_⟩
  -- The strategy-quantified `stepProb` equality at the matched stop.
  intro e e' hze hwe ρ
  -- The given edges `e, e'` coincide with the realized edges `ez, ew` (cancel the common prefix).
  have he_eq : e = ez := by
    have hcancel : [e] = [ez] := List.append_cancel_left (hze.symm.trans hz_e)
    exact List.head_eq_of_cons_eq hcancel
  have he'_eq : e' = ew := by
    have hcancel : [e'] = [ew] := List.append_cancel_left (hwe.symm.trans hw_e)
    exact List.head_eq_of_cons_eq hcancel
  subst he_eq he'_eq
  -- A reachable `pre ++ [a]` emits `a` at `pre` (invert the `IsReachable` step).
  have emits_of_concat : ∀ (pre : List E) (a : E), (pre ++ [a]) ∈ G.reach →
      (G.tree.nodeKind pre).emits a := by
    intro pre a hcat
    rw [G.mem_reach_iff] at hcat
    generalize hzx : pre ++ [a] = zx at hcat
    cases hcat with
    | root => exact absurd hzx (by simp)
    | step h' a' hr' ha' =>
        obtain ⟨rfl, ha2⟩ := List.append_inj' hzx rfl
        obtain rfl : a = a' := by injection ha2
        exact ha'
  -- `ez` is emitted at `z.take m`, `ew` at `w.take m'` (last edges of reachable prefixes).
  have hez_emit : (G.tree.nodeKind (z.take m)).emits ez :=
    emits_of_concat (z.take m) ez (by rw [← hz_e]; exact G.reach_take_of_reach z hzr _)
  have hew_emit : (G.tree.nodeKind (w.take m')).emits ew :=
    emits_of_concat (w.take m') ew (by rw [← hw_e]; exact G.reach_take_of_reach w hwr _)
  -- Both step probabilities are the behavioral mass on the realized action; observations and
  -- actions match, so the masses coincide.
  rw [stepProb_eq_behavior_iRealizedAction G ρ i (z.take m) hzm_reach hmm hez_emit,
    stepProb_eq_behavior_iRealizedAction G ρ i (w.take m') hwm_reach hm'_move hew_emit]
  -- The observations match (`hobs_eq`) and the realized actions are HEq (`haction_heq`); equal
  -- observations make the simplices `ρ i ω` heterogeneously equal and the index types coincide, so
  -- the two transported realized actions are HEq, and the behavioral masses agree.
  have hobs_eq' : G.info.observe i (z.take m) = G.info.observe i (w.take m') := hobs_eq
  -- The simplices `ρ i ·` and their (info-structure) index types coincide via the observation.
  have hs_heq : HEq (ρ i (G.info.observe i (z.take m))) (ρ i (G.info.observe i (w.take m'))) := by
    rw [hobs_eq']
  have hT_eq : G.info.iChoiceType i (G.info.observe i (z.take m)) =
      G.info.iChoiceType i (G.info.observe i (w.take m')) :=
    congrArg (G.info.iChoiceType i) hobs_eq'
  -- The two transported realized actions are HEq via `haction_heq`.
  have harg_heq :
      HEq (cast (G.infoSetChoiceForObs_eq_iChoiceType i (G.info.observe i (z.take m))
            ⟨z.take m, hzm_reach, rfl, hmm⟩) (G.iRealizedAction i (z.take m) ez))
        (cast (G.infoSetChoiceForObs_eq_iChoiceType i (G.info.observe i (w.take m'))
            ⟨w.take m', hwm_reach, rfl, hm'_move⟩) (G.iRealizedAction i (w.take m') ew)) :=
    (cast_heq _ _).trans (haction_heq.trans (cast_heq _ _).symm)
  exact stdSimplex.val_congr_heq hT_eq _ _ _ _ hs_heq harg_heq

/-- **Reach-coherence.** The reach-phrased properties the one-shot deviation principle consumes,
packaged as a structure so consumers receive them as a bundle. This is not perfect recall itself —
it is the reach-level consequence pack of perfect recall:

* `noRevisit` — along any reachable path a player never returns to the same information set, making
  each one-shot edit a single edit to the play and terminating the deviation factorization.
* `reachInvariant` — a unilateral `i`-deviation rescales the reach probability of every node in a
  fixed information set `(i, ω)` by the same factor, stated in cross-multiplied form so that no
  positivity is needed. This is the realization-equivalence consequence of action recall.

Both are implied by perfect recall via `IsPerfectRecall.reachCoherent`. -/
structure ExtensiveForm.IsReachCoherent (G : ExtensiveForm I E) : Prop where
  /-- No information-set revisits along a reachable path. -/
  noRevisit : G.NoInfoSetRevisit
  /-- A unilateral `i`-deviation rescales reach within an information set by a common factor
  (cross-multiplied form): For reachable `x, x'` in the same information set `(i, ω)`,
  `reachProb σ' x · reachProb σ x' = reachProb σ' x' · reachProb σ x`. The realization-equivalence
  core of the one-shot deviation principle. -/
  reachInvariant :
    ∀ (i : I) (σ σ' : G.BehavioralStrategy), G.unilateralDeviation i σ σ' →
      ∀ (ω : G.info.Obs i) (x x' : List E),
        G.IsReachable x → G.IsReachable x' →
        ((G.tree.nodeKind x).movesAt i ∧ G.info.observe i x = ω) →
        ((G.tree.nodeKind x').movesAt i ∧ G.info.observe i x' = ω) →
        reachProb G σ' x * reachProb G σ x' = reachProb G σ' x' * reachProb G σ x

/-- **Perfect recall implies reach-coherence.** A perfect-recall finite extensive form satisfies
the bundle `ExtensiveForm.IsReachCoherent`: The `noRevisit` field is
`IsPerfectRecall.noInfoSetRevisit`, and the `reachInvariant` field is
`reachProb_infoSet_invariant_unilateral` (which needs finitely many players, hence the instance
hypotheses). -/
theorem IsPerfectRecall.reachCoherent [Finite I] [Inhabited I]
    {G : FiniteExtensiveForm I E} (hpr : G.IsPerfectRecall) :
    G.toExtensiveForm.IsReachCoherent := by
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  exact
    { noRevisit := hpr.noInfoSetRevisit
      reachInvariant := fun i σ σ' hdev ω x x' hrx hrx' hx hx' =>
        reachProb_infoSet_invariant_unilateral G hpr i σ σ' hdev ω x x'
          ((G.mem_reach_iff x).mpr hrx) ((G.mem_reach_iff x').mpr hrx') hx hx' }

end Econlib.GameTheory
