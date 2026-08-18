/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.BackwardInduction

/-!
# One-shot deviation principle for finite perfect-information trees

For a finite perfect-information tree `T` and local behavioral strategy `s`, the recursive
`Choice`-indexed subgame-perfect predicate `IsSubgamePerfectStrategy s` (Selten 1965) is equivalent
to the flat-quantifier predicate
`spePred.IsEquilibrium (LocalBehavioralStrategy.toBehavioralStrategy T s)` on the canonical
embedding. This **one-shot deviation** characterization reduces subgame perfection to per-node
optimality. The file then derives that backward induction yields a subgame-perfect equilibrium, and
a perfect Bayesian equilibrium under the singleton perfect-information beliefs.

## Main statements

* `isSubgamePerfectStrategy_iff_spePred`: One-shot deviation principle for finite-horizon games.
* `isSubgamePerfectEquilibrium_backwardInduction`: Backward induction yields a subgame-perfect
  equilibrium.
* `eq_backwardInductionStrategy_of_isSubgamePerfectEquilibrium`: In a generic tree, every
  subgame-perfect equilibrium of the embedding is the backward-induction strategy.
* `isPerfectBayesianEquilibrium_backwardInduction`: Backward induction yields a perfect Bayesian
  equilibrium with singleton perfect-information beliefs.

## References

* Selten, Reinhard. 1965. “Spieltheoretische Behandlung Eines Oligopolmodells Mit
  Nachfragetragheit.” *Zeitschrift Fur Die Gesamte Staatswissenschaft* 121 : 301–24, 667–89.

## Tags

subgame perfect equilibrium, one-shot deviation, backward induction, perfect bayesian equilibrium
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

namespace FinitePerfectInfoTree

variable {I E : Type u}

/-- The expected payoff of an embedded strategy equals the recursive strategy value of the
underlying local strategy. -/
theorem behavioralValue_toBehavioral
    (T : FinitePerfectInfoTree I E) (s : T.LocalBehavioralStrategy) (i : I) :
    T.behavioralValue (LocalBehavioralStrategy.toBehavioral T s) i = T.strategyValue s i := by
  induction T with
  | terminal payoff => rfl
  | decision mover Choice emit child ih =>
      unfold behavioralValue strategyValue
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [shiftBehavioralAtChoice_toBehavioral, ih c (s.2 c)]
      rfl

/-- The empty-history restriction of a behavioral strategy agrees with the strategy itself on every
continuation. -/
theorem subtreeBehavioral_nil (T : FinitePerfectInfoTree I E)
    (σ : T.RawBehavioral) (rest : List E) :
    HEq (T.subtreeBehavioral σ [] rest) (σ rest) := by
  unfold subtreeBehavioral
  simp only [List.nil_append, cast_heq_iff_heq]
  rfl

/-- Embedding via `toBehavioralStrategy` factors through `atHistory`. -/
theorem atHistory_toBehavioralStrategy_eq [DecidableEq I]
    (T : FinitePerfectInfoTree I E) (s : T.LocalBehavioralStrategy) :
    (fun h' => (LocalBehavioralStrategy.toBehavioralStrategy T s).atHistory h') =
      LocalBehavioralStrategy.toBehavioral T s := by
  funext h'; exact atHistory_ofPerfectInfo _ _ _

/-- The perfect-information embedding of a raw behavior recovers the original on every history. -/
theorem atHistory_ofPerfectInfo_eq [DecidableEq I]
    (T : FinitePerfectInfoTree I E) (σ : T.RawBehavioral) :
    (fun h' => (ExtensiveForm.BehavioralStrategy.ofPerfectInfo σ).atHistory h') = σ := by
  funext h'; exact atHistory_ofPerfectInfo _ _ _

/-- The mover at history `emit c :: h` in a `decision`-rooted tree equals the mover at history `h`
in the `c`-th child subtree. -/
theorem isMoverAt_emit_cons (mover : I) (Choice : Type u) [Fintype Choice] [DecidableEq Choice]
[Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (c : Choice) (h : List E) (i : I) :
    (FinitePerfectInfoTree.decision mover Choice emit child).isMoverAt (emit c :: h) i ↔
      (child c).isMoverAt h i := by
  unfold isMoverAt
  rw [subtreeAt_emit_cons]

/-- The mover at history `h0 ++ rest` in `T` equals the mover at history `rest` in
`T.subtreeAt h0`. -/
theorem isMoverAt_append (T : FinitePerfectInfoTree I E) (h0 rest : List E) (i : I) : T.isMoverAt
(h0 ++ rest) i ↔ (T.subtreeAt h0).isMoverAt rest i := by
  unfold isMoverAt
  rw [T.subtreeAt_append h0 rest]

/-- If two strategies agree at history `emit c :: h`, their `c`-shifts agree at history `h`. -/
theorem shiftBehavioralAtChoice_apply_congr
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E)
    (child : Choice → FinitePerfectInfoTree I E)
    (σ τ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral)
    (c : Choice) (h : List E) (heq : τ (emit c :: h) = σ (emit c :: h)) :
    shiftBehavioralAtChoice mover Choice emit child τ c h =
      shiftBehavioralAtChoice mover Choice emit child σ c h := by
  unfold shiftBehavioralAtChoice
  rw [heq]

/-- Appending histories commutes with `toBehavioral` up to HEq. -/
private theorem toBehavioral_append_heq : ∀ (T : FinitePerfectInfoTree I E) (s :
T.LocalBehavioralStrategy) (h rest : List E),
      HEq
        (LocalBehavioralStrategy.toBehavioral T s (h ++ rest))
        (LocalBehavioralStrategy.toBehavioral (T.subtreeAt h)
          (LocalBehavioralStrategy.at T s h) rest) := by
  intro T s h
  induction h generalizing T s with
  | nil =>
      intro rest
      cases T with
      | terminal payoff => rfl
      | decision _ _ _ _ => rfl
  | cons e hRest ih =>
      intro rest
      cases T with
      | terminal payoff =>
          rfl
      | decision mover Choice emit child =>
          cases hdec : decodeEmit emit e with
          | some c =>
              have he : e = emit c := ((decodeEmit_eq_some_iff emit e c).mp hdec).symm
              subst he
              have hL := toBehavioral_decision_emit_cons_heq mover Choice emit child s c
                (hRest ++ rest)
              have hMid := ih (child c) (s.2 c) rest
              have hR :
                  HEq
                    (LocalBehavioralStrategy.toBehavioral
                      ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                        (emit c :: hRest))
                      (LocalBehavioralStrategy.at _ s (emit c :: hRest)) rest)
                    (LocalBehavioralStrategy.toBehavioral ((child c).subtreeAt hRest)
                      (LocalBehavioralStrategy.at _ (s.2 c) hRest) rest) := by
                have hSub := subtreeAt_emit_cons mover Choice emit child c hRest
                have hAt := at_decision_emit_cons_heq mover Choice emit child s c hRest
                congr! 1
              exact hL.trans (hMid.trans hR.symm)
          | none =>
              have hL : HEq
                  (LocalBehavioralStrategy.toBehavioral
                    (FinitePerfectInfoTree.decision mover Choice emit child) s (e :: hRest ++ rest))
                  (PUnit.unit : PUnit.{u + 1}) := by
                rw [LocalBehavioralStrategy.toBehavioral.eq_2]
                dsimp
                apply HEq.trans (cast_heq _ _)
                apply HEq.trans
                  (Option.rec_apply_heq_none
                    (C := fun x =>
                      ((match x with
                        | some c => (child c).subtreeAt (hRest ++ rest)
                        | none => terminal fun _ => 0).rootNodeKind).Behavior)
                    (x := decodeEmit emit e) (h := hdec) _ _)
                refine HEq.trans ?_ (HEq.refl (PUnit.unit : PUnit.{u + 1}))
                exact eqRec_function_apply_heq
                  (D := fun x =>
                    ((match x with
                      | some c => (child c).subtreeAt (hRest ++ rest)
                      | none => terminal fun _ => 0).rootNodeKind).Behavior)
                  (a := decodeEmit emit e) (b := none)
                  (fun (_ : decodeEmit emit e = none) =>
                    show NodeKind.Behavior (terminal (I := I) (fun _ : I => (0 : ℝ))).rootNodeKind
                    from PUnit.unit) _ _
              have hSubT :
                  (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                    (e :: hRest) = .terminal (fun _ : I => (0 : ℝ)) := by
                conv_lhs => unfold subtreeAt
                rw [hdec]
              have hAt := at_decision_cons_none_heq mover Choice emit child s e hRest hdec
              have hR : HEq
                  (LocalBehavioralStrategy.toBehavioral
                    ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                      (e :: hRest))
                    (LocalBehavioralStrategy.at _ s (e :: hRest)) rest)
                  (PUnit.unit : PUnit.{u + 1}) := by
                have h_inner :
                    LocalBehavioralStrategy.toBehavioral
                      (FinitePerfectInfoTree.terminal (I := I) (E := E) (fun _ : I => (0 : ℝ)))
                      PUnit.unit rest = PUnit.unit := by
                  cases rest <;> rfl
                have h_combined : HEq
                    (LocalBehavioralStrategy.toBehavioral
                      ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                        (e :: hRest))
                      (LocalBehavioralStrategy.at _ s (e :: hRest)) rest)
                    (LocalBehavioralStrategy.toBehavioral
                      (FinitePerfectInfoTree.terminal (I := I) (E := E) (fun _ : I => (0 : ℝ)))
                      PUnit.unit rest) := by
                  congr! 1
                exact h_combined.trans (heq_of_eq h_inner)
              exact hL.trans hR.symm

/-- The subtree-restricted version of `toBehavioral` equals `toBehavioral` of the restricted
strategy. -/
theorem subtreeBehavioral_toBehavioral (T : FinitePerfectInfoTree I E)
    (s : T.LocalBehavioralStrategy) (h : List E) :
    T.subtreeBehavioral (LocalBehavioralStrategy.toBehavioral T s) h =
      LocalBehavioralStrategy.toBehavioral (T.subtreeAt h) (LocalBehavioralStrategy.at T s h) := by
  funext rest
  unfold subtreeBehavioral
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  exact toBehavioral_append_heq T s h rest

/-- If `s` is subgame-perfect and `τ` agrees with the embedding of `s` at every non-`i` history,
then the `τ`-induced behavioral value is bounded by the `s`-strategy value for player `i`. -/
theorem behavioralValue_le_of_isSubgamePerfectStrategy (T : FinitePerfectInfoTree I E) {s :
T.LocalBehavioralStrategy} (hs : T.IsSubgamePerfectStrategy s) (i : I) (τ : T.RawBehavioral)
    (hdev : ∀ h, ¬ T.isMoverAt h i → τ h = LocalBehavioralStrategy.toBehavioral T s h) :
    T.behavioralValue τ i ≤ T.strategyValue s i := by
  induction T with
  | terminal payoff =>
      exact le_refl _
  | decision mover Choice emit child ih =>
      obtain ⟨h1, h2⟩ := hs
      have h_shift_dev : ∀ c h_inner, ¬ (child c).isMoverAt h_inner i →
          shiftBehavioralAtChoice mover Choice emit child τ c h_inner =
            LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h_inner := by
        intro c h_inner hnot
        have hτs : τ (emit c :: h_inner) =
            (LocalBehavioralStrategy.toBehavioral _ s) (emit c :: h_inner) :=
          hdev _ (by rw [isMoverAt_emit_cons]; exact hnot)
        rw [shiftBehavioralAtChoice_apply_congr mover Choice emit child _ τ c h_inner hτs,
          shiftBehavioralAtChoice_toBehavioral]
      let τnil : stdSimplex ℝ Choice := τ []
      let σnil : stdSimplex ℝ Choice := s.1
      set X : Choice → ℝ := fun c => (child c).strategyValue (s.2 c) i
      set Y : Choice → ℝ := fun c => (child c).behavioralValue
        (shiftBehavioralAtChoice mover Choice emit child τ c) i
      have hYX : ∀ c, Y c ≤ X c :=
        fun c => ih c (h2 c) _ (h_shift_dev c)
      have h_step1 : ∑ c, (τnil : Choice → ℝ) c * Y c ≤
          ∑ c, (τnil : Choice → ℝ) c * X c :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hYX c) (τnil.2.1 c)
      have h_step2 : ∑ c, (τnil : Choice → ℝ) c * X c ≤ ∑ c, (σnil : Choice → ℝ) c * X c := by
        by_cases hmover : mover = i
        · subst hmover
          have hτsum : ∑ c, (τnil : Choice → ℝ) c = 1 := τnil.2.2
          calc ∑ c, (τnil : Choice → ℝ) c * X c
              ≤ ∑ c, (τnil : Choice → ℝ) c * ∑ c', (σnil : Choice → ℝ) c' * X c' :=
                Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h1 c) (τnil.2.1 c)
            _ = (∑ c, (τnil : Choice → ℝ) c) * ∑ c', (σnil : Choice → ℝ) c' * X c' := by
                rw [← Finset.sum_mul]
            _ = ∑ c', (σnil : Choice → ℝ) c' * X c' := by rw [hτsum, one_mul]
        · have hτnil_eq : τnil = σnil := by
            change τ [] = s.1
            rw [hdev [] (fun habs => hmover habs), toBehavioral_decision_root]
          rw [hτnil_eq]
      exact le_trans h_step1 h_step2

/-- `subtreeBehavioral` at `emit c :: rest` agrees up to HEq with the `σ`-shifted
`subtreeBehavioral` at `rest` on the `c`-th child. -/
theorem subtreeBehavioral_emit_cons_apply_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E) (child : Choice → FinitePerfectInfoTree I E)
    (σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral)
    (c : Choice) (rest h : List E) :
    HEq
      ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral σ
        (emit c :: rest) h)
      ((child c).subtreeBehavioral
        (shiftBehavioralAtChoice mover Choice emit child σ c) rest h) := by
  unfold subtreeBehavioral shiftBehavioralAtChoice
  refine HEq.trans (cast_heq _ _) (HEq.symm ?_)
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- Functional form of `subtreeBehavioral_emit_cons_apply_heq`. -/
theorem subtreeBehavioral_emit_cons_heq
    (mover : I) (Choice : Type u)
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E) (child : Choice → FinitePerfectInfoTree I E)
    (σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral)
    (c : Choice) (rest : List E) :
    HEq
      ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral σ
        (emit c :: rest))
      ((child c).subtreeBehavioral
        (shiftBehavioralAtChoice mover Choice emit child σ c) rest) := by
  apply Function.hfunext rfl
  intro h h' hh
  cases eq_of_heq hh
  exact subtreeBehavioral_emit_cons_apply_heq mover Choice emit child σ c rest h

/-- HEq congruence for `behavioralValue`: Equal trees and HEq strategies give equal values. -/
theorem behavioralValue_heq_congr {T1 T2 : FinitePerfectInfoTree I E}
    (hT : T1 = T2) {σ1 : T1.RawBehavioral}
    {σ2 : T2.RawBehavioral} (hσ : HEq σ1 σ2) (i : I) :
    T1.behavioralValue σ1 i = T2.behavioralValue σ2 i := by
  subst hT
  rw [eq_of_heq hσ]

/-- Forward direction of the bridge: A recursively subgame-perfect local strategy `s` satisfies the
flat-quantifier SPE predicate when embedded via
`LocalBehavioralStrategy.toBehavioralStrategy T s`. -/
theorem isSubgamePerfectStrategy.toSpePred [DecidableEq I] : ∀ (T : FinitePerfectInfoTree I E) {s :
T.LocalBehavioralStrategy}
      (_hs : T.IsSubgamePerfectStrategy s),
      T.toExtensiveGame.spePred.IsEquilibrium
        (LocalBehavioralStrategy.toBehavioralStrategy T s) := by
  intro T
  induction T with
  | terminal payoff =>
      intro _s _hs ⟨i, h0⟩ τ _hdev
      exact le_refl _
  | decision mover Choice emit child ih =>
      intro s hs ⟨i, h0⟩ τ hdev
      have hdev' : ∀ h, ¬ (FinitePerfectInfoTree.decision mover Choice emit child).isMoverAt h i →
          τ.atHistory h = LocalBehavioralStrategy.toBehavioral _ s h := by
        intro h hnot
        have h1 := ((unilateralDeviation_iff_isMoverAt _ i _ τ).mp hdev h hnot).symm
        rwa [LocalBehavioralStrategy.toBehavioralStrategy, atHistory_ofPerfectInfo] at h1
      cases h0 with
      | nil =>
          have h_nil : ∀ σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral,
              (FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral σ [] = σ :=
            fun σ => funext fun rest => eq_of_heq (subtreeBehavioral_nil _ σ rest)
          change (FinitePerfectInfoTree.decision mover Choice emit child).behavioralValue
              ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                (fun h' =>
                  (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h') []) i ≥
            (FinitePerfectInfoTree.decision mover Choice emit child).behavioralValue
              ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                (fun h' => τ.atHistory h') []) i
          rw [atHistory_toBehavioralStrategy_eq, h_nil, h_nil, behavioralValue_toBehavioral]
          exact behavioralValue_le_of_isSubgamePerfectStrategy
            (FinitePerfectInfoTree.decision mover Choice emit child) hs i _ hdev'
      | cons e rest =>
          obtain ⟨_, h2⟩ := hs
          by_cases he : ∃ c, emit c = e
          · obtain ⟨c, hec⟩ := he
            subst hec
            have h_shift_dev : ∀ h_inner, ¬ (child c).isMoverAt h_inner i →
                shiftBehavioralAtChoice mover Choice emit child
                    (fun h' => τ.atHistory h') c h_inner =
                  LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h_inner := by
              intro h_inner hnot
              have hτs : τ.atHistory (emit c :: h_inner) =
                  (LocalBehavioralStrategy.toBehavioral _ s) (emit c :: h_inner) :=
                hdev' _ (by rw [isMoverAt_emit_cons]; exact hnot)
              rw [shiftBehavioralAtChoice_apply_congr mover Choice emit child _ _ c h_inner hτs,
                shiftBehavioralAtChoice_toBehavioral]
            let τ_child : (child c).toExtensiveForm.BehavioralStrategy :=
              ExtensiveForm.BehavioralStrategy.ofPerfectInfo
                (shiftBehavioralAtChoice mover Choice emit child (fun h' => τ.atHistory h') c)
            have h_shift_dev_can :
                (child c).toExtensiveForm.unilateralDeviation i
                  (LocalBehavioralStrategy.toBehavioralStrategy (child c) (s.2 c)) τ_child := by
              apply ((child c).unilateralDeviation_iff_isMoverAt i _ τ_child).mpr
              intro h_inner hnot
              change (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
                  (LocalBehavioralStrategy.toBehavioral (child c) (s.2 c))).atHistory h_inner =
                (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
                  (shiftBehavioralAtChoice mover Choice emit child
                    (fun h' => τ.atHistory h') c)).atHistory h_inner
              rw [atHistory_ofPerfectInfo, atHistory_ofPerfectInfo]
              exact (h_shift_dev h_inner hnot).symm
            have ih_apply := ih c (h2 c) ⟨i, rest⟩ τ_child h_shift_dev_can
            have hSub :
                (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                    (emit c :: rest) =
                  (child c).subtreeAt rest :=
              subtreeAt_emit_cons mover Choice emit child c rest
            change ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                  (emit c :: rest)).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' =>
                    (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h')
                  (emit c :: rest)) i ≥
              ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                  (emit c :: rest)).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' => τ.atHistory h') (emit c :: rest)) i
            rw [atHistory_toBehavioralStrategy_eq]
            rw [behavioralValue_heq_congr hSub
                (subtreeBehavioral_emit_cons_heq mover Choice emit child
                  (fun h' => τ.atHistory h') c rest) i,
              behavioralValue_heq_congr hSub
                (subtreeBehavioral_emit_cons_heq mover Choice emit child
                  (LocalBehavioralStrategy.toBehavioral _ s) c rest) i,
              shiftBehavioralAtChoice_toBehavioral]
            have ih' :
                ((child c).subtreeAt rest).behavioralValue
                  ((child c).subtreeBehavioral (fun h' =>
                    (LocalBehavioralStrategy.toBehavioralStrategy
                      (child c) (s.2 c)).atHistory h') rest) i ≥
                ((child c).subtreeAt rest).behavioralValue
                  ((child c).subtreeBehavioral (fun h' => τ_child.atHistory h') rest) i := ih_apply
            rw [atHistory_toBehavioralStrategy_eq, atHistory_ofPerfectInfo_eq] at ih'
            exact ih'
          · -- decode e = none: subtreeAt = junk-terminal, both sides = 0.
            have h_neg : ¬ ∃ c, emit c = e := he
            have hdec_none : decodeEmit emit e = none := by
              unfold decodeEmit
              rw [dif_neg h_neg]
            have hSub :
                (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt (e :: rest) =
                  (FinitePerfectInfoTree.terminal (I := I) (E := E) (fun _ : I => (0 : ℝ))) := by
              conv_lhs => unfold subtreeAt
              rw [hdec_none]
            have hbv : ∀ σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral,
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                    (e :: rest)).behavioralValue
                  ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                    σ (e :: rest)) i = 0 :=
              fun _ => behavioralValue_heq_congr hSub (cast_heq (by rw [hSub]) _).symm i
            change ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                  (e :: rest)).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' =>
                    (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h')
                  (e :: rest)) i ≥
              ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                  (e :: rest)).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' => τ.atHistory h') (e :: rest)) i
            rw [hbv, hbv]

/-- The Strategy `(stdSimplex.vertex c, s.2)` differs from `s` only at the root mixed action, so
its `toBehavioral` agrees with `s.toBehavioral` at every non-root history. -/
private theorem toBehavioral_pure_at_root_eq_at_cons (mover : I) (Choice : Type u) [Fintype Choice]
[DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E) (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child)) (c : Choice)
    (e : E) (rest : List E) :
    LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child)
        (stdSimplex.vertex c, s.2) (e :: rest) =
      LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child) s (e :: rest) :=
  rfl

/-- Eq form of `toBehavioral_decision_emit_cons_heq`, via cast. -/
private theorem toBehavioral_decision_emit_cons_eq_cast (mover : I) (Choice : Type u) [Fintype
Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    (emit : Choice ↪ E) (child : Choice → FinitePerfectInfoTree I E)
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (rest : List E) :
    LocalBehavioralStrategy.toBehavioral (.decision mover Choice emit child) s (emit c :: rest) =
      cast (congrArg (fun T : FinitePerfectInfoTree I E => T.rootNodeKind.Behavior)
        (subtreeAt_emit_cons mover Choice emit child c rest).symm)
        (LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) rest) :=
  eq_of_heq
    ((toBehavioral_decision_emit_cons_heq mover Choice emit child s c rest).trans
      (cast_heq _ _).symm)

/-- Lift a deviation `τ'` on `(child c)` to a deviation on the parent `decision`-rooted tree. At
histories of the form `emit c :: rest` the lift uses `τ' rest` (cast along the subtree equality
`subtreeAt_emit_cons`); elsewhere it matches `LocalBehavioralStrategy.toBehavioral _ s`. -/
private noncomputable def liftDeviation
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral) :
    (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral :=
  fun h => match h with
    | [] => LocalBehavioralStrategy.toBehavioral _ s []
    | e :: rest =>
        if h_dec : decodeEmit emit e = some c then
          have hsub :
              (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
                (e :: rest) = (child c).subtreeAt rest := by
            conv_lhs => unfold subtreeAt
            rw [h_dec]
          cast (congrArg (fun T : FinitePerfectInfoTree I E => T.rootNodeKind.Behavior)
            hsub.symm) (τ' rest)
        else
          LocalBehavioralStrategy.toBehavioral _ s (e :: rest)

@[simp] private theorem liftDeviation_nil
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral) :
    liftDeviation s c τ' [] = LocalBehavioralStrategy.toBehavioral _ s [] := rfl

private theorem liftDeviation_cons_neg
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral)
    (e : E) (rest : List E) (h_dec : decodeEmit emit e ≠ some c) :
    liftDeviation s c τ' (e :: rest) = LocalBehavioralStrategy.toBehavioral _ s (e :: rest) := by
  change (if h : decodeEmit emit e = some c then _ else _) = _
  rw [dif_neg h_dec]

private theorem liftDeviation_cons_pos
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral)
    (rest : List E) :
    liftDeviation s c τ' (emit c :: rest) =
      cast (congrArg (fun T : FinitePerfectInfoTree I E => T.rootNodeKind.Behavior)
        (subtreeAt_emit_cons mover Choice emit child c rest).symm) (τ' rest) := by
  change (if h : decodeEmit emit (emit c) = some c then _ else _) = _
  rw [dif_pos (decodeEmit_emit emit c)]
  rfl

/-- The lift is a unilateral i-deviation from `s.toBehavioral` whenever `τ'` is a unilateral
i-deviation from `(s.2 c).toBehavioral` on `(child c)`. -/
private theorem liftDeviation_eq_toBehavioral_of_not_isMoverAt {mover : I} {Choice : Type u}
[Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral) (i : I)
    (hdev' : ∀ h_inner, ¬ (child c).isMoverAt h_inner i →
      τ' h_inner = LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h_inner)
    (h : List E)
    (hnot : ¬ (FinitePerfectInfoTree.decision mover Choice emit child).isMoverAt h i) :
    liftDeviation s c τ' h = LocalBehavioralStrategy.toBehavioral _ s h := by
  cases h with
  | nil => rfl
  | cons e rest =>
      by_cases h_dec : decodeEmit emit e = some c
      · -- Canonical: e = emit c
        have he : e = emit c := ((decodeEmit_eq_some_iff emit e c).mp h_dec).symm
        subst he
        have hnot' : ¬ (child c).isMoverAt rest i :=
          fun habs => hnot (by rw [isMoverAt_emit_cons]; exact habs)
        rw [liftDeviation_cons_pos, hdev' rest hnot',
          ← toBehavioral_decision_emit_cons_eq_cast]
      · exact liftDeviation_cons_neg s c τ' e rest h_dec

/-- The shift of `liftDeviation s c τ'` past `c` recovers `τ'` exactly. -/
private theorem shiftBehavioralAtChoice_liftDeviation {mover : I} {Choice : Type u} [Fintype
Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).RawBehavioral) :
    shiftBehavioralAtChoice mover Choice emit child (liftDeviation s c τ') c = τ' := by
  funext h_inner
  unfold shiftBehavioralAtChoice
  rw [liftDeviation_cons_pos s c τ' h_inner]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- The continuation value of the canonical embedding at `emit c :: h0'` equals the continuation
value of the `c`-child embedding at `h0'`. -/
private theorem continuationValue_toBehavioral_emit_cons_eq [DecidableEq I]
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (h0' : List E) (i : I) :
    (FinitePerfectInfoTree.decision mover Choice emit child).toExtensiveGame.continuationValue
        (LocalBehavioralStrategy.toBehavioralStrategy _ s) (emit c :: h0') i =
      (child c).toExtensiveGame.continuationValue
        (LocalBehavioralStrategy.toBehavioralStrategy (child c) (s.2 c)) h0' i := by
  change
    ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
        (emit c :: h0')).behavioralValue
        ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
          (fun h' =>
            (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h') (emit c :: h0')) i =
      ((child c).subtreeAt h0').behavioralValue
        ((child c).subtreeBehavioral
          (fun h' =>
            (LocalBehavioralStrategy.toBehavioralStrategy (child c) (s.2 c)).atHistory h') h0') i
  rw [atHistory_toBehavioralStrategy_eq, atHistory_toBehavioralStrategy_eq]
  have hSub :
      (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt (emit c :: h0') =
        (child c).subtreeAt h0' := subtreeAt_emit_cons mover Choice emit child c h0'
  refine behavioralValue_heq_congr hSub ?_ i
  have h1 := subtreeBehavioral_emit_cons_heq mover Choice emit child
    (LocalBehavioralStrategy.toBehavioral _ s) c h0'
  rw [shiftBehavioralAtChoice_toBehavioral] at h1
  exact h1

/-- The continuation value of `liftDeviation s c τ'` at `emit c :: h0'` equals the continuation
value of `τ'` at `h0'` on the `c`-child. -/
private theorem continuationValue_liftDeviation_emit_cons_eq [DecidableEq I]
    {mover : I} {Choice : Type u}
    [Fintype Choice] [DecidableEq Choice] [Nonempty Choice] [Inhabited Choice]
    {emit : Choice ↪ E} {child : Choice → FinitePerfectInfoTree I E}
    (s : LocalBehavioralStrategy (.decision mover Choice emit child))
    (c : Choice) (τ' : (child c).toExtensiveForm.BehavioralStrategy)
    (h0' : List E) (i : I) :
    (FinitePerfectInfoTree.decision mover Choice emit child).toExtensiveGame.continuationValue
        (ExtensiveForm.BehavioralStrategy.ofPerfectInfo (liftDeviation s c
          (fun h' => τ'.atHistory h'))) (emit c :: h0') i =
      (child c).toExtensiveGame.continuationValue τ' h0' i := by
  change
    ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt
        (emit c :: h0')).behavioralValue
        ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
          (fun h' =>
            (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
              (liftDeviation s c (fun h'' => τ'.atHistory h''))).atHistory h')
          (emit c :: h0')) i =
      ((child c).subtreeAt h0').behavioralValue
        ((child c).subtreeBehavioral (fun h' => τ'.atHistory h') h0') i
  rw [atHistory_ofPerfectInfo_eq]
  have hSub :
      (FinitePerfectInfoTree.decision mover Choice emit child).subtreeAt (emit c :: h0') =
        (child c).subtreeAt h0' := subtreeAt_emit_cons mover Choice emit child c h0'
  refine behavioralValue_heq_congr hSub ?_ i
  have h1 := subtreeBehavioral_emit_cons_heq mover Choice emit child
    (liftDeviation s c (fun h'' => τ'.atHistory h'')) c h0'
  rw [shiftBehavioralAtChoice_liftDeviation] at h1
  exact h1

/-- Reverse direction of the bridge: If the canonical embedding
`LocalBehavioralStrategy.toBehavioralStrategy T s` satisfies the flat-quantifier SPE predicate,
then the underlying `s` is recursively subgame perfect. -/
theorem isSubgamePerfectStrategy.ofSpePred [DecidableEq I] : ∀ (T : FinitePerfectInfoTree I E) {s :
T.LocalBehavioralStrategy}
      (_h : T.toExtensiveGame.spePred.IsEquilibrium
              (LocalBehavioralStrategy.toBehavioralStrategy T s)),
      T.IsSubgamePerfectStrategy s := by
  intro T
  induction T with
  | terminal _payoff => intro _ _; trivial
  | decision mover Choice emit child ih =>
      intro s h_spe
      have h_root_ineq : ∀ c, (child c).strategyValue (s.2 c) mover ≤
          ∑ c', s.1 c' * (child c').strategyValue (s.2 c') mover := by
        intro c
        let s_c : LocalBehavioralStrategy (.decision mover Choice emit child) :=
          (stdSimplex.vertex c, s.2)
        have h_dev_pi : ∀ h, ¬ (FinitePerfectInfoTree.decision mover Choice emit child).isMoverAt
              h mover →
            (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h =
              (LocalBehavioralStrategy.toBehavioralStrategy _ s_c).atHistory h := by
          intro h hnot
          change (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
            (LocalBehavioralStrategy.toBehavioral _ s)).atHistory h =
            (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
              (LocalBehavioralStrategy.toBehavioral _ s_c)).atHistory h
          rw [atHistory_ofPerfectInfo, atHistory_ofPerfectInfo]
          cases h with
          | nil => exact absurd rfl hnot
          | cons e rest =>
              exact (toBehavioral_pure_at_root_eq_at_cons mover Choice emit child s c e rest).symm
        have h_dev :=
          (unilateralDeviation_iff_isMoverAt
            (FinitePerfectInfoTree.decision mover Choice emit child) mover _ _).mpr h_dev_pi
        have h_apply := h_spe ⟨mover, []⟩
          (LocalBehavioralStrategy.toBehavioralStrategy _ s_c) h_dev
        have h_nil : ∀ σ : (FinitePerfectInfoTree.decision mover Choice emit child).RawBehavioral,
            (FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral σ [] = σ :=
          fun σ => funext fun rest => eq_of_heq (subtreeBehavioral_nil _ σ rest)
        have h_strat_ineq :
            (FinitePerfectInfoTree.decision mover Choice emit child).strategyValue s_c mover ≤
            (FinitePerfectInfoTree.decision mover Choice emit child).strategyValue s mover := by
          have ha :
              (FinitePerfectInfoTree.decision mover Choice emit child).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' => (LocalBehavioralStrategy.toBehavioralStrategy _ s_c).atHistory h') [])
                    mover ≤
              (FinitePerfectInfoTree.decision mover Choice emit child).behavioralValue
                ((FinitePerfectInfoTree.decision mover Choice emit child).subtreeBehavioral
                  (fun h' => (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h') [])
                    mover := h_apply
          rw [atHistory_toBehavioralStrategy_eq, atHistory_toBehavioralStrategy_eq,
            h_nil, h_nil] at ha
          rw [← behavioralValue_toBehavioral, ← behavioralValue_toBehavioral]
          exact ha
        have h_sc_eq : (FinitePerfectInfoTree.decision mover Choice emit child).strategyValue
            s_c mover = (child c).strategyValue (s.2 c) mover :=
          sum_pure_mul Choice c (fun c' => (child c').strategyValue (s.2 c') mover)
        rw [h_sc_eq] at h_strat_ineq
        exact h_strat_ineq
      refine ⟨h_root_ineq, fun c => ?_⟩
      apply ih c
      intro p' τ' hdev'
      obtain ⟨i, h0'⟩ := p'
      have hdev'_pi : ∀ h_inner, ¬ (child c).isMoverAt h_inner i →
          τ'.atHistory h_inner =
            LocalBehavioralStrategy.toBehavioral (child c) (s.2 c) h_inner := by
        intro h_inner hnot
        have h1 := (((child c).unilateralDeviation_iff_isMoverAt i _ τ').mp hdev' h_inner hnot).symm
        rwa [LocalBehavioralStrategy.toBehavioralStrategy, atHistory_ofPerfectInfo] at h1
      let τ_lift : (
        FinitePerfectInfoTree.decision mover Choice emit child
          ).toExtensiveForm.BehavioralStrategy :=
            ExtensiveForm.BehavioralStrategy.ofPerfectInfo
              (liftDeviation s c (fun h' => τ'.atHistory h'))
      have h_dev_pi : ∀ h, ¬ (FinitePerfectInfoTree.decision mover Choice emit child).isMoverAt
            h i → (LocalBehavioralStrategy.toBehavioralStrategy _ s).atHistory h =
              τ_lift.atHistory h := by
        intro h hnot
        change (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
          (LocalBehavioralStrategy.toBehavioral _ s)).atHistory h =
          (ExtensiveForm.BehavioralStrategy.ofPerfectInfo
            (liftDeviation s c (fun h' => τ'.atHistory h'))).atHistory h
        rw [atHistory_ofPerfectInfo, atHistory_ofPerfectInfo]
        exact (liftDeviation_eq_toBehavioral_of_not_isMoverAt s c
          (fun h' => τ'.atHistory h') i hdev'_pi h hnot).symm
      have h_dev :=
        ((FinitePerfectInfoTree.decision mover Choice emit child).unilateralDeviation_iff_isMoverAt
          i _ _).mpr h_dev_pi
      have h_apply := h_spe (i, emit c :: h0') τ_lift h_dev
      rw [show
            (FinitePerfectInfoTree.decision mover Choice emit child).toExtensiveGame.spePred.value
              (i, emit c :: h0') (LocalBehavioralStrategy.toBehavioralStrategy _ s) =
            (child c).toExtensiveGame.continuationValue
              (LocalBehavioralStrategy.toBehavioralStrategy (child c) (s.2 c)) h0' i from
            continuationValue_toBehavioral_emit_cons_eq s c h0' i,
        show
            (FinitePerfectInfoTree.decision mover Choice emit child).toExtensiveGame.spePred.value
              (i, emit c :: h0') τ_lift =
            (child c).toExtensiveGame.continuationValue τ' h0' i from
            continuationValue_liftDeviation_emit_cons_eq s c τ' h0' i] at h_apply
      exact h_apply

/-- Bridge (one-shot deviation principle): The recursive SPE on `s` is equivalent to the
flat-quantifier `EquilibriumProblem` form on its canonical embedding. -/
theorem isSubgamePerfectStrategy_iff_spePred [DecidableEq I] (T : FinitePerfectInfoTree I E) (s :
T.LocalBehavioralStrategy) :
    T.IsSubgamePerfectStrategy s ↔
      T.toExtensiveGame.spePred.IsEquilibrium
        (LocalBehavioralStrategy.toBehavioralStrategy T s) :=
  ⟨isSubgamePerfectStrategy.toSpePred T,
    isSubgamePerfectStrategy.ofSpePred T⟩

/-- Backward induction induces an SPE of the derived `ExtensiveGame`. -/
theorem isSubgamePerfectEquilibrium_backwardInduction [DecidableEq I]
    (T : FinitePerfectInfoTree I E) :
    T.toExtensiveGame.IsSubgamePerfectEquilibrium T.backwardInductionBehavioralStrategy :=
  isSubgamePerfectStrategy.toSpePred T T.backwardInductionStrategy_isSubgamePerfect

/-- **Uniqueness of subgame-perfect equilibrium, flat form.** In a generic finite
perfect-information tree, a local strategy whose canonical embedding is a subgame-perfect
equilibrium of the derived `ExtensiveGame` must be the backward-induction strategy. -/
theorem eq_backwardInductionStrategy_of_isSubgamePerfectEquilibrium [DecidableEq I]
    {T : FinitePerfectInfoTree I E} {s : T.LocalBehavioralStrategy} (hgen : T.IsGeneric)
    (hspe : T.toExtensiveGame.IsSubgamePerfectEquilibrium
      (LocalBehavioralStrategy.toBehavioralStrategy T s)) :
    s = T.backwardInductionStrategy :=
  ((T.isSubgamePerfectStrategy_iff_spePred s).mpr hspe).eq_backwardInductionStrategy hgen

/-- For finite perfect-information trees, the embedded `(T.toGameTree.nodeKind h).movesAt i`
predicate coincides with `T.isMoverAt h i`. -/
lemma movesAt_iff_isMoverAt (T : FinitePerfectInfoTree I E) (h : List E) (i : I) :
(T.toGameTree.nodeKind h).movesAt i ↔ T.isMoverAt h i := by
  change (T.nodeKindAt h).movesAt i ↔ _
  unfold nodeKindAt rootNodeKind isMoverAt
  cases T.subtreeAt h with
  | terminal _ => exact Iff.rfl
  | decision _ _ _ _ => exact Iff.rfl

/-- A one-shot information-set deviation by player `i` is a unilateral deviation. -/
lemma toExtensiveGame_infoSetDeviation_unilateral [DecidableEq I] (T : FinitePerfectInfoTree I E)
(β : T.toExtensiveForm.BehavioralStrategy) (i : I)
    (obs : T.toExtensiveForm.info.Obs i) (β' : T.toExtensiveForm.BehavioralStrategy)
    (h_dev : IsInfoSetDeviation T.toExtensiveForm i obs β β') :
    T.toExtensiveForm.unilateralDeviation i β β' := by
  intro j obs' hj
  exact h_dev j obs' (by intro heq; cases heq; exact hj rfl)

/-- Under trivial perfect-information singleton beliefs, when player `i` moves at history `obs` the
assessment value at info set `(i, obs)` reduces to the continuation value of the strategy at
history `obs` for player `i`. -/
lemma assessmentValue_trivialBeliefs_perfectInfo_pos [DecidableEq I] [DecidableEq E]
    (T : FinitePerfectInfoTree I E)
    (σ : T.toExtensiveForm.BehavioralStrategy) {i : I} {obs : List E}
    (hm : (T.toGameTree.nodeKind obs).movesAt i) :
    assessmentValue T.toExtensiveGame
        { strategy := σ, beliefs := trivialBeliefs I E T.toGameTree } i obs =
      T.toExtensiveGame.continuationValue σ obs i := by
  classical
  change ∑ x ∈ (trivialBeliefs I E T.toGameTree).support i obs,
      (trivialBeliefs I E T.toGameTree).belief i obs x *
        T.toExtensiveGame.continuationValue σ x.1 i = _
  have hsupp :
      (trivialBeliefs I E T.toGameTree).support i obs =
        ({⟨obs, hm, rfl⟩} :
          Finset (T.toExtensiveForm.InfoSet i obs)) := by
    change (if hm' : (T.toGameTree.nodeKind obs).movesAt i then
              ({⟨obs, hm', rfl⟩} :
                Finset (T.toExtensiveForm.InfoSet i obs))
            else ∅) = _
    rw [dif_pos hm]
  rw [hsupp, Finset.sum_singleton]
  change (1 : ℝ) * _ = _
  rw [one_mul]

/-- Under trivial perfect-information singleton beliefs, when player `i` does not move at history
`obs` the info set is empty and the assessment value is zero. -/
lemma assessmentValue_trivialBeliefs_perfectInfo_neg [DecidableEq I] [DecidableEq E]
    (T : FinitePerfectInfoTree I E)
    (σ : T.toExtensiveForm.BehavioralStrategy) {i : I} {obs : List E}
    (hm : ¬ (T.toGameTree.nodeKind obs).movesAt i) :
    assessmentValue T.toExtensiveGame
        { strategy := σ, beliefs := trivialBeliefs I E T.toGameTree } i obs = 0 := by
  classical
  change ∑ x ∈ (trivialBeliefs I E T.toGameTree).support i obs,
      (trivialBeliefs I E T.toGameTree).belief i obs x *
        T.toExtensiveGame.continuationValue σ x.1 i = _
  have hsupp : (trivialBeliefs I E T.toGameTree).support i obs = ∅ := by
    change (if hm' : (T.toGameTree.nodeKind obs).movesAt i then
              ({⟨obs, hm', rfl⟩} :
                Finset (T.toExtensiveForm.InfoSet i obs))
            else ∅) = _
    rw [dif_neg hm]
  rw [hsupp, Finset.sum_empty]

/-- Backward induction induces a PBE with singleton perfect-information beliefs. -/
theorem isPerfectBayesianEquilibrium_backwardInduction [DecidableEq I] [DecidableEq E]
    (T : FinitePerfectInfoTree I E) :
    IsPerfectBayesianEquilibrium T.toExtensiveGame
      { strategy := T.backwardInductionBehavioralStrategy
        beliefs := trivialBeliefs I E T.toGameTree } := by
  refine ⟨?_, IsBayesConsistent_trivialBeliefs_perfectInfo T.toGameTree _⟩
  -- Full sequential rationality: at every (i, obs), no unilateral deviation by `i` is profitable.
  -- The deviation is already unilateral, so subgame perfection (backward induction) bounds it.
  intro i obs σ' hdev
  have hbound := T.isSubgamePerfectEquilibrium_backwardInduction (i, obs) σ' hdev
  by_cases hm : (T.toGameTree.nodeKind obs).movesAt i
  · rw [T.assessmentValue_trivialBeliefs_perfectInfo_pos _ hm,
      T.assessmentValue_trivialBeliefs_perfectInfo_pos _ hm]
    exact hbound
  · rw [T.assessmentValue_trivialBeliefs_perfectInfo_neg _ hm,
      T.assessmentValue_trivialBeliefs_perfectInfo_neg _ hm]

end FinitePerfectInfoTree

end Econlib.GameTheory
