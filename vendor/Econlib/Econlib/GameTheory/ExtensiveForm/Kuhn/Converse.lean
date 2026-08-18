/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Kuhn.Forward

/-!
# Kuhn's theorem (mixed → behavioral direction)

The converse half of **Kuhn's theorem** (Kuhn 1953): Every mixed strategy `μ` on the strategic
normalization of a perfect-recall finite extensive form is realization-equivalent to an induced
behavioral strategy `behavioralFromMixed μ`. Together with `behavioral_realizes_mixed`, this gives
the **realization equivalence** of mixed and behavioral strategies under perfect recall.

## Main definitions

* `FiniteExtensiveForm.reachPlayWeight` / `reachWeight`: Numerator / denominator reach weights.
* `FiniteExtensiveForm.condPlaySimplex`: The conditional-play distribution at an info set.
* `FiniteExtensiveForm.behavioralFromMixed`: The behavioral strategy induced by a mixed strategy.

## Main statements

* `PerfectRecallFiniteExtensiveForm.mixed_realizes_behavioral`: `behavioralFromMixed μ` is
  realization-equivalent to `μ`.

## Notes

At a reached info set `(i, obs)`, `behavioralFromMixed μ` assigns to each choice `c` the
conditional probability `reachPlayWeight μ i obs c / reachWeight μ i obs` that player `i` plays
`c`, given that `i`'s own past actions are consistent with reaching `obs`. The numerator
`reachPlayWeight` is the total `μ_i`-mass of pure strategies consistent with reaching the canonical
representative of `(i, obs)` that play `c` there; `reachWeight` is the same total without
conditioning on the choice. Perfect recall makes the probability that `i`'s own past actions are
consistent with `obs` depend only on `μ_i`. Unreached info sets, and reached info sets whose
denominator vanishes, receive the point mass on `default`.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, kuhn theorem, perfect recall, behavioral strategy, mixed strategy
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-! ## Reach weights -/

/-- Numerator weight: Total `μ_i`-mass of pure strategies that are consistent with reaching the
canonical representative of info set `(i, obs)` and play `c` there. -/
noncomputable def reachPlayWeight [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i)
    (c : G.infoSetChoiceForObs i obs) : ℝ :=
  ∑ s_i : G.PureStrategy i,
    (μ i).val s_i * G.iPathConsistent i s_i (G.canonicalRep i obs) * (if s_i obs = c then 1 else 0)

/-- Denominator weight: Total `μ_i`-mass of pure strategies consistent with reaching the canonical
representative of info set `(i, obs)`. -/
noncomputable def reachWeight [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i) : ℝ :=
  ∑ s_i : G.PureStrategy i, (μ i).val s_i * G.iPathConsistent i s_i (G.canonicalRep i obs)

lemma reachPlayWeight_nonneg [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i)
    (c : G.infoSetChoiceForObs i obs) : 0 ≤ G.reachPlayWeight μ i obs c := by
  refine Finset.sum_nonneg fun s_i _ => ?_
  refine mul_nonneg (mul_nonneg ((μ i).2.1 s_i) (G.iPathConsistent_nonneg i s_i _)) ?_
  split <;> norm_num

lemma reachWeight_nonneg [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i) :
    0 ≤ G.reachWeight μ i obs :=
  Finset.sum_nonneg fun s_i _ =>
    mul_nonneg ((μ i).2.1 s_i) (G.iPathConsistent_nonneg i s_i _)

/-- The denominator is the sum of the numerators over the choice. -/
lemma sum_reachPlayWeight_eq_reachWeight [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i) :
    ∑ c : G.infoSetChoiceForObs i obs, G.reachPlayWeight μ i obs c = G.reachWeight μ i obs := by
  unfold reachPlayWeight reachWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s_i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ (s_i obs) (fun _ => (1 : ℝ))]
  simp

/-! ## Choice-type equality at a reached info set -/

/-- At a reached info set, the pure-choice type of the canonical representative coincides with the
info-structure choice type. -/
theorem infoSetChoiceForObs_eq_iChoiceType (i : I) (obs : G.info.Obs i)
    (h_reached : G.IsReachedInfoSet i obs) :
    G.infoSetChoiceForObs i obs = G.info.iChoiceType i obs := by
  obtain ⟨_, h_obs, h_moves⟩ := G.canonicalRep_spec i obs h_reached
  have hcompat := G.iChoice_compatible i (G.canonicalRep i obs) h_moves
  rw [h_obs] at hcompat
  obtain ⟨n, hk, _⟩ := G.exists_playerNode_of_movesAt (G.canonicalRep i obs) i h_moves
  have e1 : G.infoSetChoiceForObs i obs = n.Choice := by
    unfold infoSetChoiceForObs; exact congrArg NodeKind.PureChoice hk
  have e2 : (G.tree.nodeKind (G.canonicalRep i obs)).iChoiceTypeAt i h_moves = n.Choice := by
    clear hcompat h_obs
    revert h_moves; rw [hk]; intro _; rfl
  rw [e1, ← e2, hcompat]

/-! ## The induced behavioral strategy -/

/-- Conditional-play simplex at info set `(i, obs)`, valued in the canonical-rep choice type. When
the denominator `reachWeight` is positive, the value at `c` is the conditional probability
`reachPlayWeight / reachWeight`; otherwise it is the point mass on `default`. -/
noncomputable def condPlaySimplex [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i) :
    stdSimplex ℝ (G.infoSetChoiceForObs i obs) :=
  if h_pos : 0 < G.reachWeight μ i obs then
    ⟨fun c => G.reachPlayWeight μ i obs c / G.reachWeight μ i obs, by
      refine ⟨fun c => div_nonneg (G.reachPlayWeight_nonneg μ i obs c) h_pos.le, ?_⟩
      rw [← Finset.sum_div, G.sum_reachPlayWeight_eq_reachWeight μ i obs, div_self h_pos.ne']⟩
  else
    stdSimplex.vertex (default : G.infoSetChoiceForObs i obs)

/-- Each numerator weight is bounded by the denominator. -/
lemma reachPlayWeight_le_reachWeight [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i)
    (c : G.infoSetChoiceForObs i obs) :
    G.reachPlayWeight μ i obs c ≤ G.reachWeight μ i obs := by
  rw [← G.sum_reachPlayWeight_eq_reachWeight μ i obs]
  refine Finset.single_le_sum (fun d _ => G.reachPlayWeight_nonneg μ i obs d)
    (Finset.mem_univ c)

/-- **Conditional-play ratio identity.** The conditional-play simplex value at `c` times the reach
weight equals the play weight, including the zero-reach edge case where both sides vanish. -/
lemma condPlaySimplex_val_mul_reachWeight [DecidableEq E] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i)
    (c : G.infoSetChoiceForObs i obs) :
    (G.condPlaySimplex μ i obs).val c * G.reachWeight μ i obs =
      G.reachPlayWeight μ i obs c := by
  unfold condPlaySimplex
  by_cases h_pos : 0 < G.reachWeight μ i obs
  · rw [dif_pos h_pos]
    exact div_mul_cancel₀ _ h_pos.ne'
  · rw [dif_neg h_pos]
    -- reachWeight = 0 ⟹ reachPlayWeight = 0 (it is ≤ reachWeight and ≥ 0).
    have hzero : G.reachWeight μ i obs = 0 :=
      le_antisymm (not_lt.mp h_pos) (G.reachWeight_nonneg μ i obs)
    have hpw : G.reachPlayWeight μ i obs c = 0 :=
      le_antisymm (hzero ▸ G.reachPlayWeight_le_reachWeight μ i obs c)
        (G.reachPlayWeight_nonneg μ i obs c)
    rw [hzero, mul_zero, hpw]

/-- **Kuhn's converse construction.** The behavioral strategy induced by a mixed strategy `μ`: At a
reached info set, the conditional play distribution `condPlaySimplex`, transported into the
info-structure choice type; at an unreached info set, the point mass on `default`. -/
noncomputable def behavioralFromMixed [DecidableEq E] [Fintype I] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) : G.toExtensiveForm.BehavioralStrategy :=
  fun i obs =>
    open Classical in
    if h_reached : G.IsReachedInfoSet i obs then
      simplexTransport (G.infoSetChoiceForObs_eq_iChoiceType i obs h_reached)
        (G.condPlaySimplex μ i obs)
    else
      stdSimplex.vertex (default : G.info.iChoiceType i obs)

/-- At a reached info set, the `behaviorEval` of the induced behavioral strategy at the canonical
representative coincides with the conditional-play simplex value. This is the transport bridge
between the `behaviorEval`/`atHistory` side and the `condPlaySimplex` (reach-weight ratio) side; it
carries no perfect-recall content. -/
lemma behaviorEval_canonicalRep_behavioralFromMixed [DecidableEq E] [Fintype I] [DecidableEq I]
    (μ : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (i : I) (obs : G.info.Obs i)
    (h_reached : G.IsReachedInfoSet i obs)
    (c' : G.infoSetChoiceForObs i obs) :
    (G.tree.nodeKind (G.canonicalRep i obs)).behaviorEval
        ((G.behavioralFromMixed μ).atHistory (G.canonicalRep i obs)) c' =
      (G.condPlaySimplex μ i obs).val c' := by
  classical
  obtain ⟨h_cr_reach, h_obs_eq, h_canon_move⟩ := G.canonicalRep_spec i obs h_reached
  -- The canonical representative is a player node `n_c` where `i` moves.
  obtain ⟨n_c, hkc, hmover_c⟩ := G.exists_playerNode_of_movesAt _ _ h_canon_move
  -- `behaviorEval` at a player node reads off the simplex value.
  have h_be_subst : ∀ {k : NodeKind I E} {m : PlayerNode I E}
      (h_k : k = NodeKind.player m) (b : k.Behavior) (c'' : k.PureChoice),
      k.behaviorEval b c'' = (NodeKind.player m).behaviorEval (h_k ▸ b) (h_k ▸ c'') := by aesop
  rw [h_be_subst hkc _ _]
  apply eq_of_heq
  -- The localized behavior simplex is `HEq` the conditional-play simplex.
  set σ := G.behavioralFromMixed μ with hσ
  -- `σ.atHistory cr` HEq `σ i obs = behavioralFromMixed μ i obs = simplexTransport (condPlay)`.
  have h_σc_heq : HEq _ (σ n_c.mover _) := σ.atHistory_player_heq hkc
  have h_σ_obs : HEq (σ n_c.mover (G.info.observe n_c.mover (G.canonicalRep i obs))) (σ i obs) := by
    refine (?_ : HEq _ (σ i (G.info.observe i (G.canonicalRep i obs)))).trans ?_
    · -- align the player index `n_c.mover = i`
      rw [hmover_c]
    · -- align the observation `observe i cr = obs`
      rw [h_obs_eq]
  have h_σi_def : σ i obs = simplexTransport
      (G.infoSetChoiceForObs_eq_iChoiceType i obs h_reached) (G.condPlaySimplex μ i obs) := by
    rw [hσ]
    unfold behavioralFromMixed
    rw [dif_pos h_reached]
  have h_simplex_heq : HEq (σ.atHistory (G.canonicalRep i obs)) (G.condPlaySimplex μ i obs) := by
    refine (h_σc_heq.trans h_σ_obs).trans ?_
    rw [h_σi_def]
    exact simplexTransport_heq _ _
  -- `behaviorEval (.player n_c) b c'' = (b : simplex).val c''`; reduce both `▸`-casts via HEq, then
  -- push the simplex-HEq through `.val` and the application.
  have h_choice_eq : n_c.Choice = G.infoSetChoiceForObs i obs := by
    unfold infoSetChoiceForObs; rw [hkc]; rfl
  -- value-level HEq helpers
  have aux_val : ∀ {T₁ T₂ : Type u} [ft₁ : Fintype T₁] [ft₂ : Fintype T₂] (h_T : T₁ = T₂)
      (s₁ : stdSimplex ℝ T₁) (s₂ : stdSimplex ℝ T₂),
      HEq s₁ s₂ → HEq (s₁.val : T₁ → ℝ) (s₂.val : T₂ → ℝ) := by
    rintro T₁ T₂ ft₁ ft₂ rfl s₁ s₂ h_s
    have hft : ft₁ = ft₂ := Subsingleton.elim _ _
    aesop
  have fun_HEq : ∀ {T₁ T₂ : Type u} (h_T : T₁ = T₂)
      (f₁ : T₁ → ℝ) (f₂ : T₂ → ℝ) (h_f : HEq f₁ f₂)
      (c₁ : T₁) (c₂ : T₂) (h_c : HEq c₁ c₂), HEq (f₁ c₁) (f₂ c₂) := by aesop
  -- Generalize the two `▸`-cast terms produced in the goal, recording their HEq to the originals.
  refine HEq.trans (b := (G.condPlaySimplex μ i obs).val c') ?_ HEq.rfl
  apply fun_HEq (T₁ := n_c.Choice) (T₂ := G.infoSetChoiceForObs i obs) h_choice_eq
  · -- the behavior simplex localized at `n_c` is HEq the cond-play simplex
    refine aux_val h_choice_eq _ _ ?_
    exact (eqRec_heq _ _).trans h_simplex_heq
  · -- the choice argument `hkc ▸ c'` is HEq `c'`
    exact eqRec_heq _ _

/-! ## Factorization of pure reach probability into chance × per-player consistency

`pureReachProb s h` factors as a chance-only weight (independent of the strategy profile) times
the product over players of their path-consistency indicators. This is the algebraic backbone of
the Fubini reduction: It lets the mixed reach probability separate into a per-player product. -/

/-- A fixed pure-strategy profile (default at every player), used to read out the chance-only step
weight where no player moves. -/
noncomputable def defaultProfile : ∀ j, G.PureStrategy j := fun _ => default

/-- The chance-only one-step weight at history `h`: `1` where some player moves, and the
(profile-independent) `purePrefixStep` at chance and terminal nodes. -/
noncomputable def chanceStep [DecidableEq E] (h : List E) (e : E) : ℝ :=
  open Classical in
  if (∃ i : I, (G.tree.nodeKind h).movesAt i) then 1 else G.purePrefixStep G.defaultProfile h e

/-- The chance-only reach weight over a continuation suffix. -/
noncomputable def chanceWeightFrom [DecidableEq E] (G : FiniteExtensiveForm I E) :
    List E → List E → ℝ
  | _h, [] => 1
  | h, e :: rest => G.chanceStep h e * chanceWeightFrom G (h ++ [e]) rest

/-- The chance-only reach weight of a history from the root. -/
noncomputable def chanceWeight [DecidableEq E] (h : List E) : ℝ :=
  G.chanceWeightFrom [] h

/-- **Per-step factorization.** At every history the one-step `purePrefixStep` factors as the
chance-only step times the product over players of their step indicators. -/
lemma purePrefixStep_eq_chanceStep_mul_prod [DecidableEq E] [Fintype I] [DecidableEq I]
    (s : ∀ i, G.PureStrategy i) (h : List E) (e : E) :
    G.purePrefixStep s h e = G.chanceStep h e * ∏ i, G.iStepIndicator i (s i) h e := by
  classical
  rcases hk : G.tree.nodeKind h with payoff | n | n | n | n
  · -- terminal: nobody moves, both sides vanish
    have hnomove : ¬ ∃ i : I, (G.tree.nodeKind h).movesAt i := by
      rintro ⟨i, hm⟩; rw [hk] at hm; exact hm
    have hprod : ∏ i, G.iStepIndicator i (s i) h e = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      unfold iStepIndicator; rw [if_neg (fun hm => hnomove ⟨i, hm⟩)]
    rw [hprod, mul_one, chanceStep, if_neg hnomove,
      G.purePrefixStep_of_terminal s hk, G.purePrefixStep_of_terminal G.defaultProfile hk]
  · -- player node: the mover `n.mover` is the only contributing factor
    have hmn : (G.tree.nodeKind h).movesAt n.mover := by rw [hk]; exact rfl
    have hmove : ∃ i : I, (G.tree.nodeKind h).movesAt i := ⟨n.mover, hmn⟩
    rw [chanceStep, if_pos hmove, one_mul,
      show ∏ i, G.iStepIndicator i (s i) h e = G.iStepIndicator n.mover (s n.mover) h e from
        Finset.prod_eq_single n.mover
          (fun i _ hi => by
            unfold iStepIndicator; rw [if_neg (by rw [hk]; exact fun hm => hi hm.symm)])
          (fun hcon => absurd (Finset.mem_univ n.mover) hcon)]
    unfold iStepIndicator
    rw [if_pos hmn]
    apply G.purePrefixStep_eq_of_focused_agree
    intro n' hk'
    have hnn : n = n' := NodeKind.player.inj (hk.symm.trans hk')
    subst hnn
    rw [singletonProfile, Function.update_self]
  · exact absurd hk (G.no_joint h n)
  · -- finite chance: nobody moves; both steps equal the profile-independent chance probability
    have hnomove : ¬ ∃ i : I, (G.tree.nodeKind h).movesAt i := by
      rintro ⟨i, hm⟩; rw [hk] at hm; exact hm
    have hprod : ∏ i, G.iStepIndicator i (s i) h e = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      unfold iStepIndicator; rw [if_neg (fun hm => hnomove ⟨i, hm⟩)]
    rw [hprod, mul_one, chanceStep, if_neg hnomove,
      G.purePrefixStep_of_chanceFinite s hk, G.purePrefixStep_of_chanceFinite G.defaultProfile hk]
  · exact absurd hk (G.no_general_chance h n)

/-- **Path factorization.** `pureReachProbFrom` factors as the chance-only weight times the product
over players of their path-consistency indicators. -/
lemma pureReachProbFrom_eq_chanceWeight_mul_prod [DecidableEq E] [Fintype I] [DecidableEq I]
    (s : ∀ i, G.PureStrategy i) (h_start path : List E) :
    G.pureReachProbFrom s h_start path =
      G.chanceWeightFrom h_start path * ∏ i, G.iPathConsistentFrom i (s i) h_start path := by
  induction path generalizing h_start with
  | nil =>
      simp only [pureReachProbFrom, chanceWeightFrom, iPathConsistentFrom, Finset.prod_const_one,
        mul_one]
  | cons e rest ih =>
      have hstep : G.pureReachProbFrom s h_start (e :: rest) =
          G.purePrefixStep s h_start e * G.pureReachProbFrom s (h_start ++ [e]) rest := rfl
      have hchance : G.chanceWeightFrom h_start (e :: rest) =
          G.chanceStep h_start e * G.chanceWeightFrom (h_start ++ [e]) rest := rfl
      have hpath : (∏ i, G.iPathConsistentFrom i (s i) h_start (e :: rest)) =
          ∏ i, G.iStepIndicator i (s i) h_start e *
            G.iPathConsistentFrom i (s i) (h_start ++ [e]) rest :=
        Finset.prod_congr rfl fun i _ => rfl
      rw [hstep, hchance, ih (h_start ++ [e]), G.purePrefixStep_eq_chanceStep_mul_prod s h_start e,
        hpath, Finset.prod_mul_distrib]
      ring

/-- **Fubini reduction.** The mixed reach probability separates into the chance-only weight times a
per-player product of expected path-consistency weights. -/
lemma sum_prod_pureReachProb_eq [DecidableEq E] [Fintype I] [DecidableEq I]
    (ν : ∀ i, stdSimplex ℝ (G.PureStrategy i)) (h : List E) :
    ∑ s : ∀ i, G.PureStrategy i, (∏ i, (ν i).val (s i)) * G.pureReachProb s h =
      G.chanceWeight h * ∏ i, ∑ c : G.PureStrategy i, (ν i).val c * G.iPathConsistent i c h := by
  simp only [pureReachProb, chanceWeight, iPathConsistent]
  have hA : ∀ s : ∀ i, G.PureStrategy i,
      (∏ i, (ν i).val (s i)) * G.pureReachProbFrom s [] h =
        G.chanceWeightFrom [] h *
          ∏ i, ((ν i).val (s i) * G.iPathConsistentFrom i (s i) [] h) := by
    intro s
    rw [G.pureReachProbFrom_eq_chanceWeight_mul_prod s [] h, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl (fun s _ => hA s), ← Finset.mul_sum]
  congr 1
  exact (Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun i c => (ν i).val c * G.iPathConsistentFrom i c [] h)).symm

end FiniteExtensiveForm

/-! ## Realization equivalence -/

namespace PerfectRecallFiniteExtensiveForm

variable {I E : Type u} (G : PerfectRecallFiniteExtensiveForm I E)

/-- **No-revisit consequence for path-consistency.** Along a reachable continuation strictly
extending an anchor where player `i` moves with observation `obs`, the path-consistency indicator
does not depend on the strategy's value at `obs`: By `noRevisit` the info set `obs` is never
visited again on the continuation. This is the `iPathConsistentFrom` analog of
`pureReachProbFrom_indep_of_anchor_focused`. -/
lemma iPathConsistentFrom_indep_of_anchor_focused
    [DecidableEq E] [DecidableEq I] (i : I) (c c' : G.toFiniteExtensiveForm.PureStrategy i)
    (h_anchor : List E) (h_anchor_reach : h_anchor ∈ G.toFiniteExtensiveForm.reach)
    (h_start : List E) (h_strict : h_anchor.length < h_start.length)
    (h_prefix : h_anchor <+: h_start)
    (rest : List E)
    (h_full_reach : (h_start ++ rest) ∈ G.toFiniteExtensiveForm.reach)
    (h_anchor_move : (G.toExtensiveForm.tree.nodeKind h_anchor).movesAt i)
    (h_eq_other_obs : ∀ obs : G.toExtensiveForm.info.Obs i,
      obs ≠ G.toExtensiveForm.info.observe i h_anchor → c obs = c' obs) :
    G.toFiniteExtensiveForm.iPathConsistentFrom i c h_start rest =
      G.toFiniteExtensiveForm.iPathConsistentFrom i c' h_start rest := by
  apply G.toFiniteExtensiveForm.iPathConsistentFrom_eq_of_eq_on_path
  intro k hk_lt hmove
  -- At each visited move-point `h_start ++ rest.take k`, the observed info set differs from `obs`.
  have h_step_reach : (h_start ++ rest.take k) ∈ G.toFiniteExtensiveForm.reach :=
    G.toFiniteExtensiveForm.reach_prefix_of_reach (h_start ++ rest) _ h_full_reach
      ⟨rest.drop k, by rw [List.append_assoc, List.take_append_drop]⟩
  have h_anchor_prefix_step : h_anchor <+: (h_start ++ rest.take k) := by
    obtain ⟨t, ht⟩ := h_prefix
    exact ⟨t ++ rest.take k, by rw [← List.append_assoc, ht]⟩
  have h_strict_step : h_anchor.length < (h_start ++ rest.take k).length := by
    rw [List.length_append]; omega
  have h_obs_neq := G.toFiniteExtensiveForm.not_revisit_on_strict_extension
    G.perfectRecall.noInfoSetRevisit h_anchor (h_start ++ rest.take k)
    h_anchor_reach h_step_reach h_anchor_prefix_step h_strict_step i h_anchor_move hmove
  exact h_eq_other_obs _ h_obs_neq

/-- **Representative independence of path-consistency.** Two reachable histories `h₁`, `h₂` lying
in the same information set of player `i` (same observation, `i` moving at both) impose the same
consistency constraint on every pure strategy `c`. This is `FiniteExtensiveForm.ActionRecall` at
ambient `DecidableEq` instances (the predicate is stated with classical instances;
`iPathConsistent_classical_eq` bridges the two), discharged from perfect recall via
`IsPerfectRecall.actionRecall`.

This is the **action-recall** consequence of perfect recall, not derivable from `NoInfoSetRevisit`
alone: The latter constrains the geometry of revisits but says nothing about a player's own
realized actions. -/
private lemma iPathConsistent_repr_indep
    [DecidableEq E] [DecidableEq I]
    (i : I) (c : G.toFiniteExtensiveForm.PureStrategy i) (h₁ h₂ : List E)
    (h₁_reach : h₁ ∈ G.toFiniteExtensiveForm.reach)
    (h₂_reach : h₂ ∈ G.toFiniteExtensiveForm.reach)
    (h₁_move : (G.toExtensiveForm.tree.nodeKind h₁).movesAt i)
    (h₂_move : (G.toExtensiveForm.tree.nodeKind h₂).movesAt i)
    (h_obs : G.toExtensiveForm.info.observe i h₁ = G.toExtensiveForm.info.observe i h₂) :
    G.toFiniteExtensiveForm.iPathConsistent i c h₁ =
      G.toFiniteExtensiveForm.iPathConsistent i c h₂ := by
  rw [← G.toFiniteExtensiveForm.iPathConsistent_classical_eq i c h₁,
    ← G.toFiniteExtensiveForm.iPathConsistent_classical_eq i c h₂]
  exact G.perfectRecall.actionRecall i c h₁ h₂ h₁_reach h₂_reach h₁_move h₂_move h_obs

/-- **Per-step telescoping factor (perfect-recall crux).** At a reachable player history `h_start`
where player `i` moves, the cross-multiplication identity driving the telescoping induction: The
`μ`-reach weight up to `h_start` times the `ν`-continuation over `e :: rest` equals the `μ`-reach
weight up to `h_start ++ [e]` times the `ν`-continuation over `rest`. Both equal a common scalar —
the conditional play probability at the info set times each tail — so they cross-multiply. The
identification of the reach weights uses `iPathConsistent_repr_indep`, the action-recall
consequence of perfect recall. -/
private lemma reach_step_factor
    [DecidableEq E] [Fintype I] [DecidableEq I] [Inhabited I]
    (μ : ∀ i, stdSimplex ℝ (G.toFiniteExtensiveForm.PureStrategy i)) (i : I)
    (h_start : List E) (e : E) (rest : List E)
    (h_start_reach : h_start ∈ G.toFiniteExtensiveForm.reach)
    (h_full_reach : (h_start ++ [e] ++ rest) ∈ G.toFiniteExtensiveForm.reach)
    (n : PlayerNode I E) (hk : G.toExtensiveForm.tree.nodeKind h_start = .player n)
    (hmover : n.mover = i) :
    (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start) *
      ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iStepIndicator i c h_start e *
          G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest =
    (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e])) *
      ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest := by
  classical
  set obs : G.toExtensiveForm.info.Obs i := G.toExtensiveForm.info.observe i h_start with hobs
  have h_anchor_move : (G.toExtensiveForm.tree.nodeKind h_start).movesAt i := by
    rw [hk]; exact hmover
  -- Abbreviations: R, L, R₁, L₁ and the continuation tail Q₁.
  set Q₁ : G.toFiniteExtensiveForm.PureStrategy i → ℝ := fun c =>
    G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest with hQ₁
  -- The emit-indicator on the focused info-set choice type (transported from `n.Choice`).
  have h_pc_eq : (G.toExtensiveForm.tree.nodeKind h_start).PureChoice =
      (G.toExtensiveForm.tree.nodeKind
        (G.toFiniteExtensiveForm.canonicalRep i obs)).PureChoice :=
    G.toFiniteExtensiveForm.pureChoice_eq_canonicalRep i h_start h_start_reach h_anchor_move
  have h_pc_eq_n : (G.toExtensiveForm.tree.nodeKind h_start).PureChoice = n.Choice :=
    congrArg NodeKind.PureChoice hk
  set g_focus : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs → ℝ := fun c' =>
    if n.emit (cast h_pc_eq_n (cast h_pc_eq.symm c')) = e then 1 else 0 with hg_focus
  -- The common scalar `w = σ̃(obs)(a')`: the focused-marginalization weight (`behaviorEval` of the
  -- induced behavioral strategy at the canonical rep, against the emit-indicator).
  set w : ℝ := ∑ c' : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs,
    (G.toExtensiveForm.tree.nodeKind (G.toFiniteExtensiveForm.canonicalRep i obs)).behaviorEval
      ((G.toFiniteExtensiveForm.behavioralFromMixed μ).atHistory
        (G.toFiniteExtensiveForm.canonicalRep i obs)) c' * g_focus c' with hw_def
  -- The step indicator at `h_start` is the focused emit-indicator at `c obs`.
  have hstep_eq : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
      G.toFiniteExtensiveForm.iStepIndicator i c h_start e = g_focus (c obs) := by
    intro c
    rw [G.toFiniteExtensiveForm.iStepIndicator_of_player i c hk hmover e, hg_focus]
    have h_lookup_eq :
        G.toFiniteExtensiveForm.lookupPlayerChoice (G.toFiniteExtensiveForm.singletonProfile i c)
            h_start n hk =
          cast h_pc_eq_n (cast h_pc_eq.symm (c obs)) := by
      have h1 : HEq (G.toFiniteExtensiveForm.lookupPlayerChoice
          (G.toFiniteExtensiveForm.singletonProfile i c) h_start n hk) (c obs) := by
        unfold FiniteExtensiveForm.lookupPlayerChoice
        rw [dif_pos h_start_reach]
        refine HEq.trans (cast_heq _ _) ?_
        unfold FiniteExtensiveForm.PureStrategy.applyAt
        refine HEq.trans (eqRec_heq (φ := id) _ _) ?_
        -- `singletonProfile i c n.mover (observe n.mover h_start) = c obs`
        unfold FiniteExtensiveForm.singletonProfile
        rw [hmover, Function.update_self]
        exact HEq.rfl
      have h2 : HEq (cast h_pc_eq_n (cast h_pc_eq.symm (c obs))) (c obs) :=
        (cast_heq _ _).trans (cast_heq _ _)
      exact eq_of_heq (h1.trans h2.symm)
    rw [h_lookup_eq]
  -- The tail `Q₁` is invariant under updating the focused coordinate `obs` (no-revisit).
  have hφ : ∀ (c : G.toFiniteExtensiveForm.PureStrategy i)
      (c' : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs),
      Q₁ (Function.update c obs c') = Q₁ c := by
    intro c c'
    simp only [hQ₁]
    apply G.iPathConsistentFrom_indep_of_anchor_focused i
      (Function.update c obs c') c
      (h_anchor := h_start) (h_anchor_reach := h_start_reach)
      (h_start := h_start ++ [e]) (h_strict := by simp [List.length_append])
      (h_prefix := ⟨[e], rfl⟩) (rest := rest)
      (h_full_reach := by rw [List.append_assoc] at h_full_reach ⊢; exact h_full_reach)
      (h_anchor_move := h_anchor_move)
    intro ob hob_ne
    rw [Function.update_of_ne (show ob ≠ obs by rw [hobs]; exact hob_ne)]
  -- B1: the ν-side continuation peels the scalar `w`.
  have hL : (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iStepIndicator i c h_start e * Q₁ c) =
      w * ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c * Q₁ c := by
    simp_rw [hstep_eq]
    rw [hw_def]
    exact Econlib.GameTheory.AbstractMarginal.sum_pi_focused_factor_with_phi
      (ι := G.toExtensiveForm.info.Obs i)
      (β := fun ob => G.toFiniteExtensiveForm.infoSetChoiceForObs i ob)
      (f := fun ob c' =>
        (G.toExtensiveForm.tree.nodeKind (G.toFiniteExtensiveForm.canonicalRep i ob)).behaviorEval
          ((G.toFiniteExtensiveForm.behavioralFromMixed μ).atHistory
            (G.toFiniteExtensiveForm.canonicalRep i ob)) c')
      (i₀ := obs)
      (h_sum_one := fun ob => G.toFiniteExtensiveForm.behavioralToMixedFactor_sum_one
        (G.toFiniteExtensiveForm.behavioralFromMixed μ) i ob)
      (g := g_focus) (φ := Q₁) (hφ := hφ)
  -- B2: the μ-side reach weight at `h_start ++ [e]` equals `w` times the reach weight at `h_start`.
  have h_reached : G.toFiniteExtensiveForm.IsReachedInfoSet i obs :=
    ⟨h_start, h_start_reach, hobs.symm, h_anchor_move⟩
  -- Representative independence: `h_start`-consistency matches canonical-rep consistency.
  have h_repr : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
      G.toFiniteExtensiveForm.iPathConsistent i c h_start =
        G.toFiniteExtensiveForm.iPathConsistent i c
          (G.toFiniteExtensiveForm.canonicalRep i obs) := by
    intro c
    obtain ⟨h_cr_reach, h_cr_obs, h_cr_move⟩ :=
      G.toFiniteExtensiveForm.canonicalRep_spec i obs h_reached
    exact G.iPathConsistent_repr_indep i c h_start (G.toFiniteExtensiveForm.canonicalRep i obs)
      h_start_reach h_cr_reach h_anchor_move h_cr_move (by rw [← hobs, h_cr_obs])
  -- `R = reachWeight obs`.
  have hR_eq : (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start) =
      G.toFiniteExtensiveForm.reachWeight μ i obs := by
    unfold FiniteExtensiveForm.reachWeight
    exact Finset.sum_congr rfl fun c _ => by rw [h_repr c]
  -- The constrained `μ`-side sum is the play weight.
  have hRPW : ∀ c' : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs,
      (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start *
          (if c obs = c' then (1 : ℝ) else 0)) =
        G.toFiniteExtensiveForm.reachPlayWeight μ i obs c' := by
    intro c'
    unfold FiniteExtensiveForm.reachPlayWeight
    exact Finset.sum_congr rfl fun c _ => by rw [h_repr c]
  -- Rewrite the LHS reach weight via the step indicator, expand the focused-choice indicator.
  have hLHS : (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e])) =
      ∑ c' : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs,
        g_focus c' * G.toFiniteExtensiveForm.reachPlayWeight μ i obs c' := by
    -- `P(·, h_start ++ [e]) = P(·, h_start) · g_focus (c obs)`, then expand the focused indicator.
    have hstepP : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e]) =
          ∑ c' : G.toFiniteExtensiveForm.infoSetChoiceForObs i obs,
            g_focus c' *
              ((μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start *
                (if c obs = c' then (1 : ℝ) else 0)) := by
      intro c
      rw [G.toFiniteExtensiveForm.iPathConsistent_append_singleton i c h_start e, hstep_eq c]
      rw [Finset.sum_eq_single (c obs)]
      · rw [if_pos rfl, mul_one]; ring
      · intro c' _ hc'_ne
        rw [if_neg (fun h => hc'_ne h.symm), mul_zero, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ (c obs)) hc
    simp_rw [hstepP]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.mul_sum, hRPW c']
  -- Combine: `LHS = ∑ g_focus·RPW = ∑ g_focus·(behaviorEval·RW) = w·RW = w·R`.
  have hR1 : (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e])) =
      w * ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start := by
    rw [hLHS, hR_eq, hw_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← G.toFiniteExtensiveForm.condPlaySimplex_val_mul_reachWeight μ i obs c',
      G.toFiniteExtensiveForm.behaviorEval_canonicalRep_behavioralFromMixed μ i obs h_reached c']
    ring
  rw [show (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iStepIndicator i c h_start e *
          G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest) =
      ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iStepIndicator i c h_start e * Q₁ c from rfl,
    hL, hR1]
  ring

/-- **Master telescoping invariant.** For player `i`, with `h_start` reachable and
`h_start ++ path` reachable, the `μ`-reach weight up to `h_start` times the `ν`-conditional
continuation over `path` equals the `μ`-weighted joint consistency over `h_start ++ path` (split as
a product). At `h_start = []` this is the marginal-preservation goal. -/
private lemma marginal_iPathConsistentFrom_eq
    [DecidableEq E] [Fintype I] [DecidableEq I] [Inhabited I]
    (μ : ∀ i, stdSimplex ℝ (G.toFiniteExtensiveForm.PureStrategy i)) (i : I)
    (h_start path : List E)
    (h_start_reach : h_start ∈ G.toFiniteExtensiveForm.reach)
    (h_full_reach : (h_start ++ path) ∈ G.toFiniteExtensiveForm.reach) :
    (∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start) *
      ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iPathConsistentFrom i c h_start path =
    ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start *
          G.toFiniteExtensiveForm.iPathConsistentFrom i c h_start path := by
  induction path generalizing h_start with
  | nil =>
      -- Q = 1; ν sums to 1, so LHS second factor = 1; RHS = R.
      simp only [FiniteExtensiveForm.iPathConsistentFrom, mul_one]
      rw [(G.toFiniteExtensiveForm.behavioralToMixed
            (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).2.2, mul_one]
  | cons e rest ih =>
      -- Peel the front step `e` at `h_start`.
      have h_se_reach : (h_start ++ [e]) ∈ G.toFiniteExtensiveForm.reach :=
        G.toFiniteExtensiveForm.reach_prefix_of_reach (h_start ++ (e :: rest)) _ h_full_reach
          ⟨rest, by simp [List.append_assoc]⟩
      have h_full_reach' : ((h_start ++ [e]) ++ rest) ∈ G.toFiniteExtensiveForm.reach := by
        rw [List.append_assoc]; exact h_full_reach
      -- Rewrite the continuation Q(c, h_start, e::rest) = iStep · Q(c, h_start++[e], rest)
      -- and the joint consistency P(c, h_start)·Q(c,h_start,e::rest).
      have hstepL : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
          G.toFiniteExtensiveForm.iPathConsistentFrom i c h_start (e :: rest) =
            G.toFiniteExtensiveForm.iStepIndicator i c h_start e *
              G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest := fun _ => rfl
      have ih_rec := ih (h_start ++ [e]) h_se_reach h_full_reach'
      -- Rewrite both occurrences of `Q(c, h_start, e :: rest)` and fold `P(c,h_start)·iStep` into
      -- `P(c, h_start ++ [e])` on the RHS sum.  Reassociate to left-associated products.
      simp_rw [hstepL, ← mul_assoc]
      have hRHS : ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
            (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start *
              G.toFiniteExtensiveForm.iStepIndicator i c h_start e *
                G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest =
          ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
            (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e]) *
              G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [G.toFiniteExtensiveForm.iPathConsistent_append_singleton i c h_start e]; ring
      rw [hRHS, ← ih_rec]
      -- Goal now: R · L = R₁ · L₁.  Case on whether `i` moves at `h_start`.
      by_cases hmove : (G.toExtensiveForm.tree.nodeKind h_start).movesAt i
      · -- Case B: `i` moves; identify the player node and apply `reach_step_factor`.
        obtain ⟨n, hk, hmover⟩ :=
          G.toFiniteExtensiveForm.exists_playerNode_of_movesAt h_start i hmove
        have h_full_reach'' : (h_start ++ [e] ++ rest) ∈ G.toFiniteExtensiveForm.reach := by
          rw [List.append_assoc]; exact h_full_reach
        exact G.reach_step_factor μ i h_start e rest h_start_reach h_full_reach'' n hk hmover
      · -- Case A: `i` does not move; `iStep = 1`, so R = R₁ and L = L₁.
        have hstep1 : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
            G.toFiniteExtensiveForm.iStepIndicator i c h_start e = 1 := fun c =>
          G.toFiniteExtensiveForm.iStepIndicator_of_not_movesAt i c h_start e hmove
        have hR1 : ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
              (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c (h_start ++ [e]) =
            ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
              (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h_start := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [G.toFiniteExtensiveForm.iPathConsistent_append_singleton i c h_start e, hstep1 c,
            mul_one]
        have hL : ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
              (G.toFiniteExtensiveForm.behavioralToMixed
                (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
                G.toFiniteExtensiveForm.iStepIndicator i c h_start e *
                G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest =
            ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
              (G.toFiniteExtensiveForm.behavioralToMixed
                (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
                G.toFiniteExtensiveForm.iPathConsistentFrom i c (h_start ++ [e]) rest := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hstep1 c, mul_one]
        rw [hR1, hL]

/-- **Per-player marginal preservation (perfect-recall crux).** Along a reachable history `h`, the
`behavioralToMixed (behavioralFromMixed μ)` marginal of player `i`'s path consistency equals the
`μ` marginal. This is the telescoping identity: The product of conditional play probabilities at
the info sets `i` visits along `h` equals the joint `μ_i`-probability that `i` plays the realized
action at each of them. Perfect recall makes the visited info sets distinct and the conditioning
well-defined per player. -/
lemma marginal_iPathConsistent_eq
    [DecidableEq E] [Fintype I] [DecidableEq I] [Inhabited I]
    (μ : ∀ i, stdSimplex ℝ (G.toFiniteExtensiveForm.PureStrategy i)) (i : I)
    (h : List E) (h_reach : h ∈ G.toFiniteExtensiveForm.reach) :
    ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (G.toFiniteExtensiveForm.behavioralToMixed
          (G.toFiniteExtensiveForm.behavioralFromMixed μ) i).val c *
          G.toFiniteExtensiveForm.iPathConsistent i c h =
      ∑ c : G.toFiniteExtensiveForm.PureStrategy i,
        (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h := by
  -- Instantiate the master invariant at `h_start = []`, `path = h`.
  have key := G.marginal_iPathConsistentFrom_eq μ i [] h G.toFiniteExtensiveForm.nil_mem_reach
    (by rw [List.nil_append]; exact h_reach)
  -- `iPathConsistent i c [] = 1` and `iPathConsistentFrom i c [] h = iPathConsistent i c h`.
  have hP0 : ∀ c : G.toFiniteExtensiveForm.PureStrategy i,
      G.toFiniteExtensiveForm.iPathConsistent i c [] = 1 := fun _ => rfl
  simp only [hP0, mul_one] at key
  rw [(μ i).2.2, one_mul] at key
  exact key

/-- **Kuhn's theorem (mixed → behavioral)** (Kuhn 1953). Every mixed strategy on a perfect-recall
finite extensive form is realization-equivalent to its induced behavioral strategy
`behavioralFromMixed`: They assign the same probability to every reachable terminal history. -/
theorem mixed_realizes_behavioral
    [DecidableEq E] [Fintype I] [DecidableEq I] [Inhabited I]
    (μ : (G.toFiniteStrategicGame).MixedStrategy) :
    G.toFiniteExtensiveForm.RealizationEquivalent
      (G.toFiniteExtensiveForm.behavioralFromMixed μ) μ := by
  intro h h_term
  obtain ⟨h_reach, _⟩ := (G.toFiniteExtensiveForm.mem_terminalReach_iff h).mp h_term
  -- LHS: behavioral reach of `behavioralFromMixed μ` equals its mixed image's reach (forward Kuhn).
  rw [G.behavioral_realizes_mixed (G.toFiniteExtensiveForm.behavioralFromMixed μ) h h_term]
  -- Both sides factor through chance × per-player marginals; equate the per-player factors.
  set ν := G.toFiniteExtensiveForm.behavioralToMixed (G.toFiniteExtensiveForm.behavioralFromMixed μ)
    with hν
  calc ∑ s : ∀ i, G.toFiniteExtensiveForm.PureStrategy i,
          (∏ i, (ν i).val (s i)) * G.toFiniteExtensiveForm.pureReachProb s h
      = G.toFiniteExtensiveForm.chanceWeight h *
          ∏ i, ∑ c, (ν i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h :=
        G.toFiniteExtensiveForm.sum_prod_pureReachProb_eq ν h
    _ = G.toFiniteExtensiveForm.chanceWeight h *
          ∏ i, ∑ c, (μ i).val c * G.toFiniteExtensiveForm.iPathConsistent i c h := by
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hν]; exact G.marginal_iPathConsistent_eq μ i h h_reach
    _ = ∑ s : ∀ i, G.toFiniteExtensiveForm.PureStrategy i,
          (∏ i, (μ i).val (s i)) * G.toFiniteExtensiveForm.pureReachProb s h :=
        (G.toFiniteExtensiveForm.sum_prod_pureReachProb_eq μ h).symm

end PerfectRecallFiniteExtensiveForm

end Econlib.GameTheory
