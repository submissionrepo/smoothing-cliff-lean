/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Game
public import Econlib.GameTheory.ExtensiveForm.Kuhn.PerfectRecall

/-!
# Kuhn's theorem (behavioral → mixed direction)

The forward half of **Kuhn's theorem** (Kuhn 1953): Every behavioral strategy on a finite extensive
form realizes the same probability on every reachable terminal history as its image under
`behavioralToMixed`. The converse direction (mixed → behavioral) is in `Converse.lean`; together
they give the **realization equivalence** of behavioral and mixed strategies under perfect recall.

The forward direction consumes only `ExtensiveForm.NoInfoSetRevisit`, which is strictly weaker than
perfect recall (perfect recall implies it via `IsPerfectRecall.noInfoSetRevisit`). The file builds
the step identities for pure-prefix probabilities, the focused-coordinate marginalization lemmas,
and the realization-equivalence statement.

## Main statements

* `FiniteExtensiveForm.behavioral_realizes_mixed`: A behavioral strategy and its
  `behavioralToMixed` image assign equal probability to every reachable terminal history, assuming
  `NoInfoSetRevisit`.
* `PerfectRecallFiniteExtensiveForm.behavioral_realizes_mixed`: The same statement on a
  perfect-recall finite extensive form, supplying its own `NoInfoSetRevisit` witness.

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

/-! ## Total mass of `behavioralToMixed σ` is 1 -/

/-- Total mass of the joint independent product of `behavioralToMixed σ_i` is 1. The product
factorizes via independence; each `μ_σ_i` is a simplex element so its components sum to 1. This is
the base case of the realization-equivalence induction (path of length 0). -/
lemma behavioralToMixed_total_sum_one [Fintype I] [DecidableEq I]
    (σ : G.toExtensiveForm.BehavioralStrategy) :
    ∑ s : ∀ i, G.PureStrategy i, ∏ i, (G.behavioralToMixed σ i).val (s i) = 1 := by
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_eq_one fun i _ => (G.behavioralToMixed σ i).2.2

end FiniteExtensiveForm

/-! ## NodeKind-level helpers: Dependent eventProb evaluation

These lemmas extract `eventProb` values from a node-kind hypothesis without dependent-rewrite
issues by using `subst` over a `(k : NodeKind I E)` variable. They are the workhorses for
state-level lemmas about `stepProb σ h e`. -/

namespace NodeKind

variable {I E : Type u}

lemma eventProb_of_terminal [DecidableEq E] {k : NodeKind I E} {payoff : I → ℝ}
    (hk : k = .terminal payoff) (b : k.Behavior) (e : E) :
    k.eventProb b e = 0 := by
  subst hk
  rfl

lemma eventProb_of_chanceFinite [DecidableEq E] {k : NodeKind I E} {n : ChanceFiniteNode E}
    (hk : k = .chanceFinite n) (b : k.Behavior) (e : E) :
    k.eventProb b e = ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0 := by
  subst hk
  rfl

/-- `eventProb` at a player node, made `subst`-friendly so consumers don't trip on the dependent
`b : k.Behavior` typing. -/
lemma eventProb_of_player [DecidableEq E] {k : NodeKind I E} {n : PlayerNode I E}
    (hk : k = .player n) (b : k.Behavior) (e : E) :
    k.eventProb b e =
      ∑ c : n.Choice, if n.emit c = e then (hk ▸ b : (NodeKind.player n).Behavior).val c
        else 0 := by
  subst hk
  rfl

end NodeKind

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E) [DecidableEq E]

lemma purePrefixStep_eq_stepProb_chanceFinite (σ : G.toExtensiveForm.BehavioralStrategy)
    (s : ∀ i, G.PureStrategy i) {h : List E} {n : ChanceFiniteNode E}
    (hk : G.tree.nodeKind h = .chanceFinite n) (e : E) :
    G.purePrefixStep s h e = G.toExtensiveForm.stepProb σ h e := by
  rw [G.purePrefixStep_of_chanceFinite s hk e, G.toExtensiveForm.stepProb_of_chanceFinite σ hk e]

/-! ## Extensionality of `lookupPlayerChoice` and `purePrefixStep` on the focused coordinate -/

lemma purePrefixStepAt_eq_of_focused_agree (s s' : ∀ i, G.PureStrategy i) (h : List E)
    (k : NodeKind I E) (e : E)
    (h_eq : ∀ n : PlayerNode I E, (hk : G.tree.nodeKind h = .player n) →
      s n.mover (G.info.observe n.mover h) = s' n.mover (G.info.observe n.mover h)) :
    G.purePrefixStepAt s h k e = G.purePrefixStepAt s' h k e := by
  unfold purePrefixStepAt
  match k with
  | .terminal _ => rfl
  | .player n =>
      simp only
      by_cases hk : G.tree.nodeKind h = .player n
      · rw [dif_pos hk, dif_pos hk,
          G.lookupPlayerChoice_eq_of_obs_agree s s' h n hk (h_eq n hk)]
      · rw [dif_neg hk, dif_neg hk]
  | .joint _ => rfl
  | .chanceFinite _ => rfl
  | .chanceGeneral _ => rfl

lemma purePrefixStep_eq_of_focused_agree (s s' : ∀ i, G.PureStrategy i) (h : List E) (e : E)
    (h_eq : ∀ n : PlayerNode I E, (hk : G.tree.nodeKind h = .player n) →
      s n.mover (G.info.observe n.mover h) = s' n.mover (G.info.observe n.mover h)) :
    G.purePrefixStep s h e = G.purePrefixStep s' h e := by
  unfold purePrefixStep
  exact G.purePrefixStepAt_eq_of_focused_agree s s' h _ e h_eq

/-! ## Reachability of intermediate histories on a reachable path -/

omit [DecidableEq E] in
lemma reach_take_of_reach (h : List E) (h_reach : h ∈ G.reach) (k : ℕ) :
    h.take k ∈ G.reach := by
  rw [G.mem_reach_iff] at h_reach ⊢
  induction h_reach with
  | root => simp only [List.take_nil]; exact ExtensiveForm.IsReachable.root
  | step h_path e hr he ih =>
      by_cases hk : k ≤ h_path.length
      · rw [List.take_append_of_le_length hk]; exact ih
      · push Not at hk
        have : (h_path ++ [e]).take k = h_path ++ [e] := by
          apply List.take_of_length_le
          rw [List.length_append]; simp; omega
        rw [this]
        exact ExtensiveForm.IsReachable.step h_path e hr he

omit [DecidableEq E] in
lemma reach_prefix_of_reach (h_full h_pre : List E) (h_reach : h_full ∈ G.reach)
    (h_prefix : h_pre <+: h_full) : h_pre ∈ G.reach := by
  obtain ⟨rest, hrfl⟩ := h_prefix
  have : h_pre = h_full.take h_pre.length := by
    rw [← hrfl, List.take_left]
  rw [this]
  exact G.reach_take_of_reach h_full h_reach _

/-! ## Path-level extensionality of `pureReachProbFrom`

`pureReachProbFrom s h_start path` depends on `s` only via its values at `(i, obs)` pairs where
some history `h_start ++ path.take k` along the path has player `i` moving with observation `obs`.
Extensionality at these "path-visited" coordinates is enough. -/

lemma pureReachProbFrom_eq_of_eq_on_path (s s' : ∀ i, G.PureStrategy i)
    (h_start : List E) (path : List E)
    (h_eq : ∀ k : ℕ, k < path.length →
      ∀ n : PlayerNode I E,
        G.tree.nodeKind (h_start ++ path.take k) = .player n →
        s n.mover (G.info.observe n.mover (h_start ++ path.take k)) =
          s' n.mover (G.info.observe n.mover (h_start ++ path.take k))) :
    G.pureReachProbFrom s h_start path = G.pureReachProbFrom s' h_start path := by
  induction path generalizing h_start with
  | nil => rfl
  | cons e rest ih =>
      unfold pureReachProbFrom
      have hstep : G.purePrefixStep s h_start e = G.purePrefixStep s' h_start e := by
        apply G.purePrefixStep_eq_of_focused_agree
        intro n hk
        have hH := h_eq 0 (by simp) n
        rw [List.take_zero, List.append_nil] at hH
        exact hH hk
      have hrest : G.pureReachProbFrom s (h_start ++ [e]) rest =
          G.pureReachProbFrom s' (h_start ++ [e]) rest := by
        apply ih
        intro k hk_lt n hkind
        have hk_lt' : k + 1 < (e :: rest).length := by
          simp only [List.length_cons]; omega
        have hH := h_eq (k + 1) hk_lt' n
        simp only [List.take_succ_cons] at hH
        have hlist : (h_start ++ [e]) ++ rest.take k = h_start ++ (e :: rest.take k) := by
          rw [List.append_assoc]; rfl
        rw [hlist] at hkind ⊢
        exact hH hkind
      rw [hstep, hrest]

end FiniteExtensiveForm

/-! ## Abstract one-level marginalization on a Pi type

Given a probability factorization `∏_i f_i(s_i) = 1` (each factor sums to one), and a function
`g` of just the `i₀` coordinate, the sum factors:

∑_s (∏*i f_i(s_i)) * g(s*{i₀}) = ∑*c f*{i₀}(c) * g(c)

This is the workhorse for the focused-coordinate marginalization at both the `I` (player) level and
the `Obs i₀` (info-set) level. -/

namespace Econlib.GameTheory.AbstractMarginal

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {β : ι → Type*}
  [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

omit [∀ i, DecidableEq (β i)] in
lemma sum_pi_focused_factor
    (f : ∀ i, β i → ℝ) (i₀ : ι) (h_sum_one_other : ∀ i, i ≠ i₀ → ∑ c : β i, f i c = 1)
    (g : β i₀ → ℝ) :
    ∑ s : ∀ i, β i, (∏ i, f i (s i)) * g (s i₀) =
      ∑ c : β i₀, f i₀ c * g c := by
  let F : (i : ι) → β i → ℝ :=
    fun i x => f i x * (if heq : i = i₀ then g (heq ▸ x) else 1)
  have step1 : ∀ s : ∀ i, β i,
      (∏ i, f i (s i)) * g (s i₀) = ∏ i, F i (s i) := by
    intro s
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single i₀ (fun i _ hi => dif_neg hi)
        (fun h => absurd (Finset.mem_univ i₀) h)]
    simp
  simp_rw [step1]
  have step2 : ∑ s : ∀ i, β i, ∏ i, F i (s i) = ∏ i, ∑ b : β i, F i b := by
    rw [← Fintype.piFinset_univ]; exact (Finset.prod_univ_sum (fun _ => Finset.univ) F).symm
  rw [step2, Finset.prod_eq_single i₀]
  · change (∑ x : β i₀, f i₀ x * (if heq : i₀ = i₀ then g (heq ▸ x) else 1)) =
      ∑ c, f i₀ c * g c
    apply Finset.sum_congr rfl
    intro x _
    rw [dif_pos rfl]
  · intro i _ hi
    change ∑ x : β i, f i x * (if heq : i = i₀ then g (heq ▸ x) else 1) = 1
    simp_rw [dif_neg hi, mul_one]
    exact h_sum_one_other i hi
  · intro h; exact absurd (Finset.mem_univ i₀) h

omit [∀ i, DecidableEq (β i)] in
/-- Generalization of `sum_pi_focused_factor` allowing a φ-factor that depends on the entire
profile but is invariant under updates of the focused coordinate. The non-focused factors are
required to sum to 1, and the focused factor is also required to sum to 1 (so that under the
substitution that resets the focused coord, the product `∏ i, f i (s i)` averages out to the
analogous product without dependence on `s i₀`). The result splits into the focused-coord weighted
sum times the φ-weighted full sum. -/
lemma sum_pi_focused_factor_with_phi
    [∀ i, Inhabited (β i)]
    (f : ∀ i, β i → ℝ) (i₀ : ι) (h_sum_one : ∀ i, ∑ c : β i, f i c = 1)
    (g : β i₀ → ℝ) (φ : (∀ i, β i) → ℝ)
    (hφ : ∀ (s : ∀ i, β i) (c : β i₀), φ (Function.update s i₀ c) = φ s) :
    ∑ s : ∀ i, β i, (∏ i, f i (s i)) * g (s i₀) * φ s =
      (∑ c : β i₀, f i₀ c * g c) *
        ∑ s : ∀ i, β i, (∏ i, f i (s i)) * φ s := by
  set e : (∀ i, β i) ≃ β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j) := Equiv.piSplitAt i₀ β
  have hLHS : ∑ s : ∀ i, β i, (∏ i, f i (s i)) * g (s i₀) * φ s =
      ∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        (∏ i, f i (e.symm p i)) * g ((e.symm p) i₀) * φ (e.symm p) := by
    rw [← Equiv.sum_comp e.symm]
  have hRHS_inner : ∑ s : ∀ i, β i, (∏ i, f i (s i)) * φ s =
      ∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        (∏ i, f i (e.symm p i)) * φ (e.symm p) := by
    rw [← Equiv.sum_comp e.symm]
  rw [hLHS, hRHS_inner]
  have hsym_i₀ : ∀ (p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j)), e.symm p i₀ = p.1 := by
    intro p
    rw [Equiv.piSplitAt_symm_apply, dif_pos rfl]
  have hsym_other : ∀ (p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j))
      (i : ι) (hi : i ≠ i₀), e.symm p i = p.2 ⟨i, hi⟩ := by
    intro p i hi
    rw [Equiv.piSplitAt_symm_apply, dif_neg hi]
  have hsym_update : ∀ (p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j)),
      e.symm p = Function.update (e.symm (default, p.2)) i₀ p.1 := by
    intro p
    funext i
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self, hsym_i₀]
    · rw [Function.update_of_ne hi, hsym_other p i hi, hsym_other (default, p.2) i hi]
  have hφ_indep : ∀ (p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j)),
      φ (e.symm p) = φ (e.symm (default, p.2)) := fun p => by
    rw [hsym_update p]; exact hφ _ p.1
  have hprod_split : ∀ (p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j)),
      (∏ i, f i (e.symm p i)) =
        f i₀ p.1 * ∏ j : { j // j ≠ i₀ }, f ↑j (p.2 j) := by
    intro p
    rw [Fintype.prod_eq_mul_prod_compl i₀]
    congr 1
    · rw [hsym_i₀]
    · rw [Finset.prod_subtype (s := ({i₀}ᶜ : Finset ι)) (p := fun j => j ≠ i₀)
          (by intro j; simp [Finset.mem_compl, Finset.mem_singleton])
          (f := fun j => f j (e.symm p j))]
      apply Finset.prod_congr rfl
      intro j _
      rw [hsym_other p j j.2]
  conv_lhs =>
    rw [show
      (∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        (∏ i, f i (e.symm p i)) * g (e.symm p i₀) * φ (e.symm p)) =
      (∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        f i₀ p.1 * (∏ j : { j // j ≠ i₀ }, f ↑j (p.2 j)) *
          g p.1 * φ (e.symm (default, p.2))) from by
      apply Finset.sum_congr rfl
      intro p _
      rw [hprod_split p, hsym_i₀ p, hφ_indep p]]
  conv_rhs =>
    rw [show
      (∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        (∏ i, f i (e.symm p i)) * φ (e.symm p)) =
      (∑ p : β i₀ × ((j : { j // j ≠ i₀ }) → β ↑j),
        f i₀ p.1 * (∏ j : { j // j ≠ i₀ }, f ↑j (p.2 j)) *
          φ (e.symm (default, p.2))) from by
      apply Finset.sum_congr rfl
      intro p _
      rw [hprod_split p, hφ_indep p]]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  have hLHS_inner : ∀ b : β i₀,
      (∑ s' : (j : { j // j ≠ i₀ }) → β ↑j,
        f i₀ b * (∏ j : { j // j ≠ i₀ }, f ↑j (s' j)) * g b *
          φ (e.symm (default, s'))) = f i₀ b * g b *
            ∑ s' : (j : { j // j ≠ i₀ }) → β ↑j,
              (∏ j : { j // j ≠ i₀ }, f ↑j (s' j)) * φ (e.symm (default, s')) := by
    intro b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  have hRHS_inner_inner : ∀ b : β i₀,
      (∑ s' : (j : { j // j ≠ i₀ }) → β ↑j,
        f i₀ b * (∏ j : { j // j ≠ i₀ }, f ↑j (s' j)) *
          φ (e.symm (default, s'))) = f i₀ b *
            ∑ s' : (j : { j // j ≠ i₀ }) → β ↑j,
              (∏ j : { j // j ≠ i₀ }, f ↑j (s' j)) * φ (e.symm (default, s')) := by
    intro b
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  simp_rw [hLHS_inner, hRHS_inner_inner]
  rw [← Finset.sum_mul, ← Finset.sum_mul, h_sum_one i₀, one_mul]

end Econlib.GameTheory.AbstractMarginal

/-! ## Focused-coord marginalization for `behavioralToMixed`

Apply `sum_pi_focused_factor` twice to peel off `i₀` then `obs₀`. -/

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E) [Fintype I] [DecidableEq I]

lemma sum_focused_marginalize
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (i₀ : I) (obs₀ : G.toExtensiveForm.info.Obs i₀)
    (g : G.infoSetChoiceForObs i₀ obs₀ → ℝ) :
    ∑ s : ∀ i, G.PureStrategy i, (∏ i, (G.behavioralToMixed σ i).val (s i)) * g (s i₀ obs₀) =
      ∑ c : G.infoSetChoiceForObs i₀ obs₀,
        (G.tree.nodeKind (G.canonicalRep i₀ obs₀)).behaviorEval
          (σ.atHistory (G.canonicalRep i₀ obs₀)) c * g c := by
  rw [Econlib.GameTheory.AbstractMarginal.sum_pi_focused_factor
    (β := G.PureStrategy)
    (f := fun i s_i => (G.behavioralToMixed σ i).val s_i)
    (i₀ := i₀)
    (h_sum_one_other := fun i _ => (G.behavioralToMixed σ i).2.2)
    (g := fun s_outer => g (s_outer obs₀))]
  exact Econlib.GameTheory.AbstractMarginal.sum_pi_focused_factor
    (β := fun obs : G.toExtensiveForm.info.Obs i₀ => G.infoSetChoiceForObs i₀ obs)
    (f := fun obs c =>
      (G.tree.nodeKind (G.canonicalRep i₀ obs)).behaviorEval
        (σ.atHistory (G.canonicalRep i₀ obs)) c)
    (i₀ := obs₀)
    (h_sum_one_other := fun obs _ => G.behavioralToMixedFactor_sum_one σ i₀ obs)
    (g := g)

end FiniteExtensiveForm

/-! ## No-revisit consequence: PureReachProbFrom invariant under focused-coord updates

Using `IsPerfectRecall.noRevisit`, we derive: If `h_start` is reachable and player `i₀` moves
there with observation `obs₀`, then no later history along a reachable continuation visits the same
`(i₀, obs₀)` info set as the moving player. Therefore `pureReachProbFrom s (h_start ++ [e]) rest`
does not depend on the coordinate `s i₀ obs₀` of `s`. -/

namespace FiniteExtensiveForm

variable {I E : Type u} (G : FiniteExtensiveForm I E) [DecidableEq E]

omit [DecidableEq E] in
/-- No-revisit along a reachable continuation: If `h_anchor` is a reachable history with player
`i₀` moving, then no STRICT extension of `h_anchor` along a reachable path has `i₀` moving with the
same observation. The operational consequence of the no-info-set-revisit hypothesis `hnr` (the only
recall property the forward realization theorem consumes). -/
lemma not_revisit_on_strict_extension (hnr : G.toExtensiveForm.NoInfoSetRevisit)
    (h_anchor h_step : List E)
    (h_anchor_reach : h_anchor ∈ G.reach)
    (h_step_reach : h_step ∈ G.reach)
    (h_prefix : h_anchor <+: h_step) (h_strict : h_anchor.length < h_step.length)
    (i₀ : I) (h_anchor_move : (G.toExtensiveForm.tree.nodeKind h_anchor).movesAt i₀)
    (h_step_move : (G.toExtensiveForm.tree.nodeKind h_step).movesAt i₀) :
    G.toExtensiveForm.info.observe i₀ h_step ≠
      G.toExtensiveForm.info.observe i₀ h_anchor := by
  intro h_obs_eq
  have h_eq_hist := hnr i₀ h_anchor h_step
    ((G.mem_reach_iff h_anchor).mp h_anchor_reach) ((G.mem_reach_iff h_step).mp h_step_reach)
    h_prefix h_obs_eq.symm h_anchor_move h_step_move
  rw [h_eq_hist] at h_strict
  exact lt_irrefl _ h_strict

/-- The pureReachProbFrom value over a strict continuation of `h_anchor` does not depend on
`s i₀ obs₀` where `obs₀ = G.info.observe i₀ h_anchor` — by perfect recall, this info set is not
visited along the continuation. -/
lemma pureReachProbFrom_indep_of_anchor_focused (hnr : G.toExtensiveForm.NoInfoSetRevisit)
    (s s' : ∀ i, G.PureStrategy i)
    (h_anchor : List E) (h_anchor_reach : h_anchor ∈ G.reach)
    (h_start : List E) (h_strict : h_anchor.length < h_start.length)
    (h_prefix : h_anchor <+: h_start)
    (rest : List E)
    (h_full_reach : (h_start ++ rest) ∈ G.reach)
    (i₀ : I) (h_anchor_move : (G.toExtensiveForm.tree.nodeKind h_anchor).movesAt i₀)
    (h_eq_other_player : ∀ i, i ≠ i₀ → s i = s' i)
    (h_eq_other_obs : ∀ obs : G.toExtensiveForm.info.Obs i₀,
      obs ≠ G.toExtensiveForm.info.observe i₀ h_anchor → s i₀ obs = s' i₀ obs) :
    G.pureReachProbFrom s h_start rest =
      G.pureReachProbFrom s' h_start rest := by
  apply G.pureReachProbFrom_eq_of_eq_on_path
  intro k hk_lt n hkind
  by_cases hi : n.mover = i₀
  · have h_step_reach : (h_start ++ rest.take k) ∈ G.reach :=
      G.reach_prefix_of_reach (h_start ++ rest) _ h_full_reach
        ⟨rest.drop k, by rw [List.append_assoc, List.take_append_drop]⟩
    have h_step_move : (G.toExtensiveForm.tree.nodeKind (h_start ++ rest.take k)).movesAt i₀ := by
      rw [hkind]; exact hi.symm ▸ rfl
    have h_anchor_prefix_step : h_anchor <+: (h_start ++ rest.take k) := by
      obtain ⟨t, ht⟩ := h_prefix
      exact ⟨t ++ rest.take k, by rw [← List.append_assoc, ht]⟩
    have h_strict_step : h_anchor.length < (h_start ++ rest.take k).length := by
      rw [List.length_append]; omega
    have h_obs_neq := G.not_revisit_on_strict_extension hnr h_anchor (h_start ++ rest.take k)
      h_anchor_reach h_step_reach h_anchor_prefix_step h_strict_step i₀
      h_anchor_move h_step_move
    rw [hi]
    exact h_eq_other_obs _ h_obs_neq
  · rw [h_eq_other_player n.mover hi]

omit [DecidableEq E] in
/-- General focused-coordinate marginalization with a `φ`-factor independent of the focused
coordinate: The sum factors into the focused-coordinate weighted sum times the `φ`-weighted full
sum. -/
lemma sum_focused_with_indep_phi
    [Fintype I] [DecidableEq I]
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (i₀ : I) (obs₀ : G.toExtensiveForm.info.Obs i₀)
    (g : G.infoSetChoiceForObs i₀ obs₀ → ℝ)
    (φ : (∀ i, G.PureStrategy i) → ℝ)
    (hφ : ∀ (s : ∀ i, G.PureStrategy i)
            (c : G.infoSetChoiceForObs i₀ obs₀),
        φ (Function.update s i₀ (Function.update (s i₀) obs₀ c)) = φ s) :
    ∑ s : ∀ i, G.PureStrategy i,
      (∏ i, (G.behavioralToMixed σ i).val (s i)) * g (s i₀ obs₀) * φ s =
      (∑ c : G.infoSetChoiceForObs i₀ obs₀,
        (G.toExtensiveForm.tree.nodeKind
          (G.canonicalRep i₀ obs₀)).behaviorEval
          (σ.atHistory (G.canonicalRep i₀ obs₀)) c * g c) *
        ∑ s : ∀ i, G.PureStrategy i,
          (∏ i, (G.behavioralToMixed σ i).val (s i)) * φ s := by
  let γ' : (i : I) → G.toExtensiveForm.info.Obs i → Type u :=
    fun i obs => G.infoSetChoiceForObs i obs
  let K : Type u := Σ i : I, G.toExtensiveForm.info.Obs i
  let γ : K → Type u := fun k => γ' k.1 k.2
  let f_K : (k : K) → γ k → ℝ := fun k c =>
    (G.toExtensiveForm.tree.nodeKind
      (G.canonicalRep k.1 k.2)).behaviorEval
      (σ.atHistory (G.canonicalRep k.1 k.2)) c
  let k₀ : K := ⟨i₀, obs₀⟩
  have h_sum_one_K : ∀ k : K, ∑ c : γ k, f_K k c = 1 := by
    intro k
    exact G.behavioralToMixedFactor_sum_one σ k.1 k.2
  let e : (∀ k : K, γ k) ≃ (∀ i : I, ∀ obs, γ' i obs) :=
    Equiv.piCurry γ'
  let g_K : γ k₀ → ℝ := g
  let φ_K : (∀ k : K, γ k) → ℝ := fun t => φ (e t)
  have hφ_K : ∀ (t : ∀ k : K, γ k) (c : γ k₀),
      φ_K (Function.update t k₀ c) = φ_K t := by
    intro t c
    let c' : G.infoSetChoiceForObs i₀ obs₀ := c
    change φ (Sigma.curry (Function.update t k₀ c)) = φ (Sigma.curry t)
    have h_curry_eq : Sigma.curry (Function.update t k₀ c) =
        Function.update (Sigma.curry t) i₀ (Function.update (Sigma.curry t i₀) obs₀ c') := by
      funext j ob
      by_cases hj : j = i₀
      · cases hj
        rw [Function.update_self]
        by_cases hob : ob = obs₀
        · cases hob
          rw [Function.update_self]
          exact Function.update_self _ _ _
        · have hne : (⟨i₀, ob⟩ : K) ≠ k₀ := fun h_eq =>
            hob (eq_of_heq (Sigma.mk.inj_iff.mp h_eq).2)
          change Sigma.curry (Function.update t k₀ c) i₀ ob =
            Function.update (Sigma.curry t i₀) obs₀ c' ob
          change Function.update t k₀ c ⟨i₀, ob⟩ = _
          rw [Function.update_of_ne hne, Function.update_of_ne hob]
          rfl
      · have hne : (⟨j, ob⟩ : K) ≠ k₀ := fun h_eq => hj (congrArg Sigma.fst h_eq)
        change Function.update t k₀ c ⟨j, ob⟩ = _
        rw [Function.update_of_ne hne, Function.update_of_ne hj]
        rfl
    rw [h_curry_eq]
    exact hφ (Sigma.curry t) c'
  have hprod_eq : ∀ t : ∀ k : K, γ k,
      (∏ i, (G.behavioralToMixed σ i).val (e t i)) =
        ∏ k : K, f_K k (t k) := by
    intro t
    have heq_per_i : ∀ i,
        (G.behavioralToMixed σ i).val (e t i) =
          ∏ obs : G.toExtensiveForm.info.Obs i,
            f_K ⟨i, obs⟩ (t ⟨i, obs⟩) := by
      intro i
      apply Finset.prod_congr rfl
      intro obs _
      rfl
    simp_rw [heq_per_i]
    rw [Finset.prod_sigma' (Finset.univ : Finset I) (fun _ => Finset.univ)
        (fun i obs => f_K ⟨i, obs⟩ (t ⟨i, obs⟩))]
    rw [show (Finset.univ : Finset I).sigma (fun _ => Finset.univ) =
          (Finset.univ : Finset K) from Finset.univ_sigma_univ]
  have hLHS_eq : ∑ s : ∀ i, G.PureStrategy i,
        (∏ i, (G.behavioralToMixed σ i).val (s i)) *
          g (s i₀ obs₀) * φ s =
      ∑ t : ∀ k : K, γ k, (∏ k : K, f_K k (t k)) * g_K (t k₀) * φ_K t := by
    have h_change_var :
        (∑ s : ∀ i, G.PureStrategy i,
          (∏ i, (G.behavioralToMixed σ i).val (s i)) *
            g (s i₀ obs₀) * φ s) =
        ∑ t : ∀ k : K, γ k,
          (∏ i, (G.behavioralToMixed σ i).val (e t i)) *
            g (e t i₀ obs₀) * φ (e t) :=
      (Equiv.sum_comp e (fun s : ∀ i : I, ∀ obs, γ' i obs =>
        (∏ i, (G.behavioralToMixed σ i).val (s i)) *
          g (s i₀ obs₀) * φ s)).symm
    rw [h_change_var]
    apply Finset.sum_congr rfl
    intro t _
    rw [hprod_eq t]
    rfl
  rw [hLHS_eq]
  have hRHS_eq : ∑ s : ∀ i, G.PureStrategy i,
        (∏ i, (G.behavioralToMixed σ i).val (s i)) * φ s =
      ∑ t : ∀ k : K, γ k, (∏ k : K, f_K k (t k)) * φ_K t := by
    have h_change_var :
        (∑ s : ∀ i, G.PureStrategy i,
          (∏ i, (G.behavioralToMixed σ i).val (s i)) * φ s) =
        ∑ t : ∀ k : K, γ k,
          (∏ i, (G.behavioralToMixed σ i).val (e t i)) * φ (e t) :=
      (Equiv.sum_comp e (fun s : ∀ i : I, ∀ obs, γ' i obs =>
        (∏ i, (G.behavioralToMixed σ i).val (s i)) * φ s)).symm
    rw [h_change_var]
    apply Finset.sum_congr rfl
    intro t _
    rw [hprod_eq t]
  rw [hRHS_eq]
  exact Econlib.GameTheory.AbstractMarginal.sum_pi_focused_factor_with_phi
    (β := γ) f_K k₀ h_sum_one_K g_K φ_K hφ_K

omit [DecidableEq E] in
/-- At a player history, `behaviorEval` at the canonical representative coincides with the
`behaviorEval` at the history itself, both viewed at the appropriate player-node simplex; both
equal the simplex value `σ` assigns at the info set to choice `c`. -/
lemma behaviorEval_canon_eq_h_player
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (h : List E) (h_reach : h ∈ G.reach)
    (n : PlayerNode I E) (hk : G.toExtensiveForm.tree.nodeKind h = .player n)
    (h_anchor_move : (G.toExtensiveForm.tree.nodeKind h).movesAt n.mover)
    (c : n.Choice) :
    let i₀ : I := n.mover
    let obs₀ : G.toExtensiveForm.info.Obs i₀ := G.toExtensiveForm.info.observe i₀ h
    (G.toExtensiveForm.tree.nodeKind
        (G.canonicalRep i₀ obs₀)).behaviorEval
        (σ.atHistory (G.canonicalRep i₀ obs₀))
        (cast ((congrArg NodeKind.PureChoice hk).symm.trans
          (G.pureChoice_eq_canonicalRep i₀ h h_reach h_anchor_move)) c) =
      ((hk ▸ σ.atHistory h : (NodeKind.player n).Behavior) :
        stdSimplex ℝ n.Choice).val c := by
  intro i₀ obs₀
  have h_reached : G.IsReachedInfoSet i₀ obs₀ :=
    ⟨h, h_reach, rfl, h_anchor_move⟩
  obtain ⟨_, h_obs_eq, h_canon_move⟩ :=
    G.canonicalRep_spec i₀ obs₀ h_reached
  have h_σh_heq : HEq (σ.atHistory h) (σ n.mover (G.toExtensiveForm.info.observe n.mover h)) :=
    σ.atHistory_player_heq hk
  obtain ⟨n_c, hkc⟩ : ∃ n_c : PlayerNode I E,
      G.toExtensiveForm.tree.nodeKind (G.canonicalRep i₀ obs₀) =
        .player n_c := by
    rcases hk_cas : G.toExtensiveForm.tree.nodeKind
        (G.canonicalRep i₀ obs₀) with _ | n_c | n_c | n_c | n_c
    · rw [hk_cas] at h_canon_move; exact absurd h_canon_move id
    · exact ⟨n_c, rfl⟩
    · exact absurd hk_cas (G.no_joint _ n_c)
    · rw [hk_cas] at h_canon_move; exact absurd h_canon_move id
    · exact absurd hk_cas (G.no_general_chance _ n_c)
  have hmover_c : n_c.mover = i₀ := by rw [hkc] at h_canon_move; exact h_canon_move
  have h_σc_heq :
      HEq (σ.atHistory (G.canonicalRep i₀ obs₀))
          (σ n_c.mover (G.toExtensiveForm.info.observe n_c.mover
            (G.canonicalRep i₀ obs₀))) :=
    σ.atHistory_player_heq hkc
  have h_be_subst : ∀ {k : NodeKind I E} {m : PlayerNode I E}
      (h_k : k = NodeKind.player m) (b : k.Behavior) (c' : k.PureChoice),
      k.behaviorEval b c' =
        (NodeKind.player m).behaviorEval (h_k ▸ b) (h_k ▸ c') := by
    rintro k m rfl b c'; rfl
  apply eq_of_heq
  rw [h_be_subst hkc _ _]
  have h_simplex_heq :
      HEq ((hkc ▸ σ.atHistory (G.canonicalRep i₀ obs₀) :
                (NodeKind.player n_c).Behavior) : stdSimplex ℝ n_c.Choice)
          ((hk ▸ σ.atHistory h : (NodeKind.player n).Behavior) : stdSimplex ℝ n.Choice) := by
    have h₁ : HEq ((hkc ▸ σ.atHistory (G.canonicalRep i₀ obs₀) :
              (NodeKind.player n_c).Behavior))
                (σ.atHistory (G.canonicalRep i₀ obs₀)) := eqRec_heq _ _
    have h₂ : HEq ((hk ▸ σ.atHistory h : (NodeKind.player n).Behavior))
                (σ.atHistory h) := eqRec_heq _ _
    have σ_heq : ∀ {i₁ i₂ : I} (h_i : i₁ = i₂)
        {obs₁ : G.toExtensiveForm.info.Obs i₁} {obs₂ : G.toExtensiveForm.info.Obs i₂}
        (h_obs : HEq obs₁ obs₂),
        HEq (σ i₁ obs₁) (σ i₂ obs₂) := by aesop
    have h_common :
        HEq (σ.atHistory (G.canonicalRep i₀ obs₀)) (σ.atHistory h) := by
      refine h_σc_heq.trans (HEq.trans ?_ h_σh_heq.symm)
      apply σ_heq (hmover_c.trans (rfl : n.mover = i₀).symm)
      have h_n_c_canon_HEq : HEq (G.toExtensiveForm.info.observe n_c.mover
          (G.canonicalRep i₀ obs₀)) obs₀ := by
        rw [hmover_c]; exact heq_of_eq h_obs_eq
      exact h_n_c_canon_HEq.trans (HEq.rfl : HEq obs₀ (G.toExtensiveForm.info.observe n.mover h))
    exact h₁.trans (h_common.trans h₂.symm)
  have h_c_heq :
      HEq (hkc ▸ cast ((congrArg NodeKind.PureChoice hk).symm.trans
        (G.pureChoice_eq_canonicalRep i₀ h h_reach h_anchor_move)) c) c :=
    (eqRec_heq _ _).trans (cast_heq _ _)
  have h_choice_eq : n_c.Choice = n.Choice := by
    have h_pc_eq := G.pureChoice_eq_canonicalRep i₀ h h_reach h_anchor_move
    have lhs_eq : (G.toExtensiveForm.tree.nodeKind h).PureChoice = n.Choice := by rw [hk]; rfl
    have rhs_eq : (G.toExtensiveForm.tree.nodeKind
        (G.canonicalRep i₀ obs₀)).PureChoice = n_c.Choice := by rw [hkc]; rfl
    exact rhs_eq.symm.trans (h_pc_eq.symm.trans lhs_eq)
  have fun_HEq : ∀ {T₁ T₂ : Type u} (h_T : T₁ = T₂)
      (f₁ : T₁ → ℝ) (f₂ : T₂ → ℝ) (h_f : HEq f₁ f₂)
      (c₁ : T₁) (c₂ : T₂) (h_c : HEq c₁ c₂), HEq (f₁ c₁) (f₂ c₂) := by aesop
  have h_funs_HEq :
      HEq (((hkc ▸ σ.atHistory (G.canonicalRep i₀ obs₀) :
                  (NodeKind.player n_c).Behavior) : stdSimplex ℝ n_c.Choice).val :
            n_c.Choice → ℝ)
          (((hk ▸ σ.atHistory h : (NodeKind.player n).Behavior) :
              stdSimplex ℝ n.Choice).val : n.Choice → ℝ) := by
    have aux : ∀ {T₁ T₂ : Type u} [ft₁ : Fintype T₁] [ft₂ : Fintype T₂] (h_T : T₁ = T₂)
        (s₁ : stdSimplex ℝ T₁) (s₂ : stdSimplex ℝ T₂),
        HEq s₁ s₂ → HEq (s₁.val : T₁ → ℝ) (s₂.val : T₂ → ℝ) := by
      rintro T₁ T₂ ft₁ ft₂ rfl s₁ s₂ h_s
      have hft : ft₁ = ft₂ := Subsingleton.elim _ _
      aesop
    exact aux (T₁ := n_c.Choice) (T₂ := n.Choice) h_choice_eq _ _ h_simplex_heq
  exact fun_HEq (T₁ := n_c.Choice) (T₂ := n.Choice) h_choice_eq
    _ _ h_funs_HEq _ _ h_c_heq

/-- General marginalization with a path-suffix integrand: Factor `stepProb σ h e` out from the
sum-over-`s` of `μ(s) * purePrefixStep(s, h, e) * pureReachProbFrom(s, h ++ [e], rest)`. Uses
no-revisit (perfect recall) plus the focused-coord marginalization from
`sum_focused_marginalize`. -/
lemma sum_step_marginalize_player
    [Fintype I] [DecidableEq I] (hnr : G.toExtensiveForm.NoInfoSetRevisit)
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (h : List E) (h_reach : h ∈ G.reach)
    (n : PlayerNode I E) (hk : G.toExtensiveForm.tree.nodeKind h = .player n)
    (e : E) (rest : List E)
    (h_full_reach : (h ++ [e] ++ rest) ∈ G.reach) :
    ∑ s : ∀ i, G.PureStrategy i,
      (∏ i, (G.behavioralToMixed σ i).val (s i)) *
        G.purePrefixStep s h e *
          G.pureReachProbFrom s (h ++ [e]) rest =
      G.toExtensiveForm.stepProb σ h e *
        ∑ s : ∀ i, G.PureStrategy i,
          (∏ i, (G.behavioralToMixed σ i).val (s i)) *
            G.pureReachProbFrom s (h ++ [e]) rest := by
  set i₀ : I := n.mover
  set obs₀ : G.toExtensiveForm.info.Obs i₀ := G.toExtensiveForm.info.observe i₀ h
  have h_anchor_move : (G.toExtensiveForm.tree.nodeKind h).movesAt i₀ := by rw [hk]; exact rfl
  let h_pc_eq : (G.toExtensiveForm.tree.nodeKind h).PureChoice =
      (G.toExtensiveForm.tree.nodeKind
        (G.canonicalRep i₀ obs₀)).PureChoice :=
    G.pureChoice_eq_canonicalRep i₀ h h_reach h_anchor_move
  let h_pc_eq_n : (G.toExtensiveForm.tree.nodeKind h).PureChoice = n.Choice :=
    congrArg NodeKind.PureChoice hk
  let g_focus : G.infoSetChoiceForObs i₀ obs₀ → ℝ := fun c =>
    if n.emit (cast h_pc_eq_n (cast h_pc_eq.symm c)) = e then 1 else 0
  let φ : (∀ i, G.PureStrategy i) → ℝ := fun s =>
    G.pureReachProbFrom s (h ++ [e]) rest
  have hφ : ∀ (s : ∀ i, G.PureStrategy i)
      (c : G.infoSetChoiceForObs i₀ obs₀),
      φ (Function.update s i₀ (Function.update (s i₀) obs₀ c)) = φ s := by
    intro s c
    apply G.pureReachProbFrom_indep_of_anchor_focused hnr
      (s := Function.update s i₀ (Function.update (s i₀) obs₀ c)) (s' := s)
      (h_anchor := h) (h_anchor_reach := h_reach)
      (h_start := h ++ [e])
      (h_strict := by simp [List.length_append])
      (h_prefix := ⟨[e], rfl⟩)
      (rest := rest) (h_full_reach := h_full_reach)
      (i₀ := i₀) (h_anchor_move := h_anchor_move)
    · intro j hj_ne
      rw [Function.update_of_ne hj_ne]
    · intro ob hob_ne
      rw [Function.update_self, Function.update_of_ne hob_ne]
  have hstep_eq : ∀ s : ∀ i, G.PureStrategy i,
      G.purePrefixStep s h e = g_focus (s i₀ obs₀) := by
    intro s
    rw [G.purePrefixStep_of_player s hk e]
    have h_lookup_eq :
        G.lookupPlayerChoice s h n hk =
          cast h_pc_eq_n (cast h_pc_eq.symm (s i₀ obs₀)) := by
      have h1 : HEq (G.lookupPlayerChoice s h n hk) (s i₀ obs₀) := by
        unfold FiniteExtensiveForm.lookupPlayerChoice
        rw [dif_pos h_reach]
        apply HEq.trans (cast_heq _ _)
        unfold FiniteExtensiveForm.PureStrategy.applyAt
        refine HEq.trans (eqRec_heq (φ := id) _ _) ?_
        rfl
      have h2 : HEq (cast h_pc_eq_n (cast h_pc_eq.symm (s i₀ obs₀))) (s i₀ obs₀) :=
        (cast_heq _ _).trans (cast_heq _ _)
      exact eq_of_heq (h1.trans h2.symm)
    rw [h_lookup_eq]
  simp_rw [hstep_eq]
  rw [G.sum_focused_with_indep_phi σ i₀ obs₀ g_focus φ hφ]
  congr 1
  unfold ExtensiveForm.stepProb
  rw [NodeKind.eventProb_of_player hk (σ.atHistory h) e]
  have TypeEq : G.infoSetChoiceForObs i₀ obs₀ = n.Choice :=
    h_pc_eq.symm.trans h_pc_eq_n
  rw [← Equiv.sum_comp (Equiv.cast TypeEq).symm (fun c =>
    (G.toExtensiveForm.tree.nodeKind
        (G.canonicalRep i₀ obs₀)).behaviorEval
        (σ.atHistory (G.canonicalRep i₀ obs₀)) c *
      g_focus c)]
  apply Finset.sum_congr rfl
  intro c _
  have hg_simp :
      g_focus ((Equiv.cast TypeEq).symm c) = if n.emit c = e then (1:ℝ) else 0 := by
    change (if n.emit (cast h_pc_eq_n (cast h_pc_eq.symm ((Equiv.cast TypeEq).symm c))) = e
            then (1:ℝ) else 0) = _
    have h_chain : cast h_pc_eq_n (cast h_pc_eq.symm ((Equiv.cast TypeEq).symm c)) = c := by
      apply eq_of_heq
      exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))
    rw [h_chain]
  rw [hg_simp]
  by_cases h_emit : n.emit c = e
  · rw [if_pos h_emit, if_pos h_emit, mul_one]
    have h_helper := G.behaviorEval_canon_eq_h_player σ h h_reach n hk h_anchor_move c
    apply eq_of_heq
    apply HEq.trans (b := ((hk ▸ σ.atHistory h : (NodeKind.player n).Behavior) :
        stdSimplex ℝ n.Choice).val c)
    · apply heq_of_eq
      have h_cast_heq : HEq ((Equiv.cast TypeEq).symm c)
          (cast ((congrArg NodeKind.PureChoice hk).symm.trans
            (G.pureChoice_eq_canonicalRep i₀ h h_reach h_anchor_move))
              c) :=
        (cast_heq _ _).trans (cast_heq _ _).symm
      congr 1
    · rfl
  · rw [if_neg h_emit, if_neg h_emit, mul_zero]

/-- The chance-finite case: At a chance-finite step, `purePrefixStep` is constant in `s` and equals
`stepProb σ h e`, so the marginalization is trivial. -/
lemma sum_step_marginalize_chanceFinite
    [Fintype I] [DecidableEq I]
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (h : List E) (n : ChanceFiniteNode E)
    (hk : G.toExtensiveForm.tree.nodeKind h = .chanceFinite n)
    (e : E) (rest : List E) :
    ∑ s : ∀ i, G.PureStrategy i,
      (∏ i, (G.behavioralToMixed σ i).val (s i)) *
        G.purePrefixStep s h e *
          G.pureReachProbFrom s (h ++ [e]) rest =
      G.toExtensiveForm.stepProb σ h e *
        ∑ s : ∀ i, G.PureStrategy i,
          (∏ i, (G.behavioralToMixed σ i).val (s i)) *
            G.pureReachProbFrom s (h ++ [e]) rest := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [G.purePrefixStep_eq_stepProb_chanceFinite σ s hk e]
  ring

/-! ## Strong inductive realization-equivalence helper -/

lemma realization_aux [Fintype I] [DecidableEq I] (hnr : G.toExtensiveForm.NoInfoSetRevisit)
    (σ : G.toExtensiveForm.BehavioralStrategy)
    (h_start : List E) (path : List E)
    (h_start_reach : h_start ∈ G.reach)
    (h_full_reach : (h_start ++ path) ∈ G.reach) :
    G.toExtensiveForm.finitePrefixProbFrom σ h_start path =
      ∑ s : ∀ i, G.PureStrategy i,
        (∏ i, (G.behavioralToMixed σ i).val (s i)) *
          G.pureReachProbFrom s h_start path := by
  induction path generalizing h_start with
  | nil =>
      simp only [ExtensiveForm.finitePrefixProbFrom, FiniteExtensiveForm.pureReachProbFrom, mul_one]
      exact (G.behavioralToMixed_total_sum_one σ).symm
  | cons e rest ih =>
      simp only [ExtensiveForm.finitePrefixProbFrom]
      have h_se_reach : (h_start ++ [e]) ∈ G.reach :=
        G.reach_prefix_of_reach (h_start ++ (e :: rest)) _ h_full_reach
          ⟨rest, by simp [List.append_assoc]⟩
      have h_full_reach' : ((h_start ++ [e]) ++ rest) ∈ G.reach := by
        rw [List.append_assoc]; exact h_full_reach
      have ih_rec := ih (h_start ++ [e]) h_se_reach h_full_reach'
      rw [ih_rec]
      simp_rw [show ∀ s : ∀ i, G.PureStrategy i,
          G.pureReachProbFrom s h_start (e :: rest) =
          G.purePrefixStep s h_start e *
            G.pureReachProbFrom s (h_start ++ [e]) rest from fun _ => rfl]
      -- reassociate the integrand from `μ * (step * reach)` to `μ * step * reach`
      simp_rw [← mul_assoc]
      rcases h_kind : G.toExtensiveForm.tree.nodeKind h_start with payoff | n | n | n | n
      · -- terminal: contradicts (h_start ++ [e]) ∈ reach (terminal doesn't emit).
        exfalso
        rw [G.mem_reach_iff] at h_se_reach
        generalize hL : h_start ++ [e] = L at h_se_reach
        cases h_se_reach with
        | root =>
            have : (h_start ++ [e]).length = 0 := by rw [hL]; rfl
            rw [List.length_append] at this; simp at this
        | step h' e' hr he =>
            have hlen : h_start.length = h'.length := by
              have := congrArg List.length hL
              simp at this; omega
            obtain ⟨hh', he_'⟩ := List.append_inj hL hlen
            have he_eq : e = e' := by
              simpa only [List.cons.injEq, and_true] using he_'
            subst hh'
            subst he_eq
            rw [h_kind] at he
            exact he
      · exact (G.sum_step_marginalize_player hnr σ h_start h_start_reach n h_kind e rest
          h_full_reach').symm
      · exact absurd h_kind (G.no_joint h_start n)
      · exact (G.sum_step_marginalize_chanceFinite σ h_start n h_kind e rest).symm
      · exact absurd h_kind (G.no_general_chance h_start n)

/-- **Kuhn's theorem (behavioral → mixed)** (Kuhn 1953). Every behavioral strategy on a finite
extensive form satisfying no information-set revisits is realization-equivalent to its image under
`behavioralToMixed`: They assign the same probability to every reachable terminal history. The
forward direction consumes only `NoInfoSetRevisit`, strictly weaker than perfect recall (which
implies it via `IsPerfectRecall.noInfoSetRevisit`). -/
theorem behavioral_realizes_mixed
    [Fintype I] [DecidableEq I] [Inhabited I] (hnr : G.toExtensiveForm.NoInfoSetRevisit)
    (σ : G.toExtensiveForm.BehavioralStrategy) :
    G.RealizationEquivalent σ
      (G.behavioralToMixed σ) := by
  intro h h_term
  rw [G.mem_terminalReach_iff] at h_term
  obtain ⟨h_reach, _⟩ := h_term
  unfold ExtensiveForm.finitePrefixProb FiniteExtensiveForm.pureReachProb
  have h_reach' : ([] : List E) ++ h ∈ G.reach := by
    rw [List.nil_append]; exact h_reach
  exact G.realization_aux hnr σ [] h G.nil_mem_reach h_reach'

end FiniteExtensiveForm

namespace PerfectRecallFiniteExtensiveForm

variable {I E : Type u} (G : PerfectRecallFiniteExtensiveForm I E) [DecidableEq E]

/-- **Kuhn's theorem (behavioral → mixed) on a perfect-recall form** (Kuhn 1953). A perfect-recall
finite extensive form supplies its `NoInfoSetRevisit` witness to the bare-form
`FiniteExtensiveForm.behavioral_realizes_mixed`. -/
theorem behavioral_realizes_mixed
    [Fintype I] [DecidableEq I] [Inhabited I]
    (σ : G.toExtensiveForm.BehavioralStrategy) :
    G.toFiniteExtensiveForm.RealizationEquivalent σ
      (G.toFiniteExtensiveForm.behavioralToMixed σ) :=
  G.toFiniteExtensiveForm.behavioral_realizes_mixed G.perfectRecall.noInfoSetRevisit σ

end PerfectRecallFiniteExtensiveForm

end Econlib.GameTheory
