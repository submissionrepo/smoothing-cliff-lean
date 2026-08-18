/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.OneShotSurgery

/-!
# Next-stop frontier of the one-shot deviation backward induction

The backward induction of the extensive-form one-shot deviation principle advances from an
information set's support to the next `i`-moves, skipping through terminal and non-`i` layers where
the strategies share step probabilities. `stopsBelow`/`nextStops` materialize this frontier and
`continuationValue_residual_stops`/`oneShotSurgery_residual_nextStops` expand a deviation residual
onto it with undiscounted (`discount = 1`) transition weights.

## Main definitions

* `ExtensiveForm.stopsBelow` / `ExtensiveForm.nextStops`: The next `i`-stop frontier below a node.

## Main statements

* `continuationValue_residual_stops`: Segment expansion of a deviation residual onto the frontier.
* `oneShotSurgery_residual_nextStops`: Surgery-residual expansion onto the next-stop frontier.

## Tags

extensive form, one-shot deviation principle, backward induction
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-! ### The next-stop frontier -/

open Classical in
/-- The next `i`-stops weakly below `z`, within fuel `k`: Descend through emitted children,
stopping at the first `i`-mover met (including `z` itself). Fuel `0` returns `∅`; with fuel at
least the remaining depth every branch ends at an `i`-mover or a terminal, so the frontier is
complete (`continuationValue_residual_stops`). -/
noncomputable def ExtensiveForm.stopsBelow (G : ExtensiveForm I E) (i : I) :
    ℕ → List E → Finset (List E)
  | 0, _ => ∅
  | k + 1, z =>
    if (G.tree.nodeKind z).movesAt i then {z}
    else (G.emitImage z).biUnion (fun e => G.stopsBelow i k (z ++ [e]))

@[simp] theorem ExtensiveForm.stopsBelow_zero (G : ExtensiveForm I E) (i : I) (z : List E) :
    G.stopsBelow i 0 z = ∅ := rfl

theorem ExtensiveForm.stopsBelow_succ_of_movesAt (G : ExtensiveForm I E) (i : I) (k : ℕ)
    {z : List E} (hmv : (G.tree.nodeKind z).movesAt i) :
    G.stopsBelow i (k + 1) z = {z} := by
  rw [ExtensiveForm.stopsBelow, if_pos hmv]

theorem ExtensiveForm.stopsBelow_succ_of_not_movesAt (G : ExtensiveForm I E) (i : I) (k : ℕ)
    {z : List E} (hmv : ¬ (G.tree.nodeKind z).movesAt i) :
    G.stopsBelow i (k + 1) z =
      (G.emitImage z).biUnion (fun e => G.stopsBelow i k (z ++ [e])) := by
  rw [ExtensiveForm.stopsBelow, if_neg hmv]

/-- A stop is an extension of the node the frontier descends from. -/
theorem ExtensiveForm.prefix_of_mem_stopsBelow (G : ExtensiveForm I E) {i : I} {k : ℕ}
    {z w : List E} (hw : w ∈ G.stopsBelow i k z) : z <+: w := by
  induction k generalizing z with
  | zero => simp at hw
  | succ k ih =>
    by_cases hmv : (G.tree.nodeKind z).movesAt i
    · rw [G.stopsBelow_succ_of_movesAt i k hmv, Finset.mem_singleton] at hw
      exact hw ▸ List.prefix_refl z
    · rw [G.stopsBelow_succ_of_not_movesAt i k hmv, Finset.mem_biUnion] at hw
      obtain ⟨e, _, hw⟩ := hw
      exact (z.prefix_append [e]).trans (ih hw)

/-- **Membership in the next-stop frontier**, characterized: Starting from a reachable `z`, the
fuel-`k` frontier collects exactly the reachable `i`-movers `w` extending `z` with no `i`-mover
strictly between `z` and `w` (positions `r` with `|z| ≤ r < |w|`) and depth less than `|z| + k`. -/
theorem ExtensiveForm.mem_stopsBelow_iff (G : ExtensiveForm I E) (i : I) (k : ℕ)
    {z w : List E} (hz : G.IsReachable z) :
    w ∈ G.stopsBelow i k z ↔
      z <+: w ∧ G.IsReachable w ∧ (G.tree.nodeKind w).movesAt i ∧
        (∀ r : ℕ, z.length ≤ r → r < w.length →
          ¬ (G.tree.nodeKind (w.take r)).movesAt i) ∧
        w.length < z.length + k := by
  induction k generalizing z with
  | zero =>
    simp only [ExtensiveForm.stopsBelow_zero, Finset.notMem_empty, false_iff]
    rintro ⟨hpre, -, -, -, hlen⟩
    have := hpre.length_le
    omega
  | succ k ih =>
    by_cases hmv : (G.tree.nodeKind z).movesAt i
    · rw [G.stopsBelow_succ_of_movesAt i k hmv, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨List.prefix_refl w, hz, hmv, fun r hr hr' => absurd (lt_of_le_of_lt hr hr')
          (lt_irrefl _), by omega⟩
      · rintro ⟨hpre, -, -, hbet, -⟩
        by_contra hne
        have hlt : z.length < w.length := by
          have hle := hpre.length_le
          rcases Nat.eq_or_lt_of_le hle with heq | hlt
          · exact absurd (List.IsPrefix.eq_of_length hpre heq).symm hne
          · exact hlt
        have htake : w.take z.length = z := (List.prefix_iff_eq_take.mp hpre).symm
        exact hbet z.length le_rfl hlt (by rw [htake]; exact hmv)
    · rw [G.stopsBelow_succ_of_not_movesAt i k hmv, Finset.mem_biUnion]
      constructor
      · rintro ⟨e, he, hw⟩
        have hchild : G.IsReachable (z ++ [e]) :=
          G.isReachable_concat_of_mem_emitImage hz he
        obtain ⟨hpre, hwr, hwmv, hbet, hlen⟩ := (ih hchild).mp hw
        refine ⟨(z.prefix_append [e]).trans hpre, hwr, hwmv, ?_, ?_⟩
        · intro r hr hr'
          rcases Nat.eq_or_lt_of_le hr with heq | hlt
          · -- `r = |z|`: the prefix node is `z` itself, where `i` does not move.
            have htake : w.take z.length = z := by
              have hzw : z <+: w := (z.prefix_append [e]).trans hpre
              exact (List.prefix_iff_eq_take.mp hzw).symm
            rw [heq] at htake
            rw [htake]
            exact hmv
          · refine hbet r ?_ hr'
            rw [List.length_append, List.length_singleton]
            omega
        · rw [List.length_append, List.length_singleton] at hlen
          omega
      · rintro ⟨hpre, hwr, hwmv, hbet, hlen⟩
        -- `w ≠ z` (`i` moves at `w` but not at `z`), so `w` extends `z` through a first edge `e`.
        obtain ⟨t, rfl⟩ := hpre
        rcases t with _ | ⟨e, t⟩
        · rw [List.append_nil] at hwmv ⊢
          exact absurd hwmv hmv
        · have hsplit : z ++ e :: t = (z ++ [e]) ++ t := by
            rw [List.append_assoc]; rfl
          have hchild_pre : z ++ [e] <+: z ++ e :: t := by
            rw [hsplit]; exact List.prefix_append _ _
          have hchild : G.IsReachable (z ++ [e]) :=
            ExtensiveForm.IsReachable.of_prefix G hwr hchild_pre
          have he : e ∈ G.emitImage z :=
            (G.mem_emitImage_iff_emits z e).mpr (G.emits_of_isReachable_concat hchild)
          refine ⟨e, he, (ih hchild).mpr ⟨?_, hwr, hwmv, ?_, ?_⟩⟩
          · rw [hsplit]; exact List.prefix_append _ _
          · intro r hr hr'
            refine hbet r ?_ hr'
            simp only [List.length_append, List.length_singleton] at hr
            omega
          · simp only [List.length_append, List.length_cons] at hlen ⊢
            omega

/-! ### Residual expansion onto the frontier -/

/-- **Segment expansion of the deviation residual (undiscounted).** Below any node `z`, the
residual `V_σ(z) − V_{σ'}(z)` of a unilateral `i`-deviation propagates through the `i`-free segment
onto the next-stop frontier: It equals the `σ'`-transition-weighted sum of the stop residuals. -/
theorem continuationValue_residual_stops (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hδ : G.discount = 1) (i : I) (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ')
    (k : ℕ) (z : List E) (hk : N ≤ z.length + k) :
    G.continuationValue σ z i - G.continuationValue σ' z i =
      ∑ w ∈ G.toExtensiveForm.stopsBelow i k z,
        G.toExtensiveForm.finitePrefixProbFrom σ' z (w.drop z.length) *
          (G.continuationValue σ w i - G.continuationValue σ' w i) := by
  induction k generalizing z with
  | zero =>
    rw [ExtensiveForm.stopsBelow_zero, Finset.sum_empty]
    exact continuationValue_residual_eq_zero_of_terminal G hfd σ σ' i (by omega)
  | succ k ih =>
    by_cases hmv : (G.toExtensiveForm.tree.nodeKind z).movesAt i
    · -- `z` is itself the stop: the frontier is `{z}` and the weight is `1`.
      rw [G.toExtensiveForm.stopsBelow_succ_of_movesAt i k hmv, Finset.sum_singleton,
        List.drop_length, G.toExtensiveForm.finitePrefixProbFrom_nil, one_mul]
    · rw [G.toExtensiveForm.stopsBelow_succ_of_not_movesAt i k hmv]
      by_cases hterm : ∃ p : I → ℝ, G.toExtensiveForm.tree.nodeKind z = .terminal p
      · -- Terminal: residual `0`; no emitted children, empty frontier.
        obtain ⟨p, hp⟩ := hterm
        have hres : G.continuationValue σ z i - G.continuationValue σ' z i = 0 := by
          rw [G.continuationValue_eq σ z i, G.continuationValue_eq σ' z i]
          simp only [hp, nodeStepValue_terminal]
          ring
        have hemit : G.toExtensiveForm.emitImage z = ∅ := by
          unfold ExtensiveForm.emitImage
          rw [hp]
        rw [hres, hemit]
        simp
      · push Not at hterm
        -- Interior non-`i` node: shared heads peel; recurse into the children.
        have hshared : ∀ e, G.toExtensiveForm.stepProb σ z e =
            G.toExtensiveForm.stepProb σ' z e := by
          intro e
          refine stepProb_congr_movers G.toExtensiveForm σ σ' z e (fun j hj => ?_)
          exact (hdev j (G.info.observe j z) (fun h0 => hmv (h0 ▸ hj))).symm
        rw [G.continuationValue_eventSum hno_joint σ z i hterm,
          G.continuationValue_eventSum hno_joint σ' z i hterm, ← Finset.sum_sub_distrib,
          Finset.sum_biUnion]
        · refine Finset.sum_congr rfl (fun e he => ?_)
          have hchild := ih (z ++ [e])
            (by rw [List.length_append, List.length_singleton]; omega)
          calc G.toExtensiveForm.stepProb σ z e *
                  (G.stepPayoff z e i + G.discount * G.continuationValue σ (z ++ [e]) i) -
                G.toExtensiveForm.stepProb σ' z e *
                  (G.stepPayoff z e i + G.discount * G.continuationValue σ' (z ++ [e]) i)
              = G.toExtensiveForm.stepProb σ' z e *
                  (G.continuationValue σ (z ++ [e]) i -
                    G.continuationValue σ' (z ++ [e]) i) := by
                rw [hshared e, hδ]; ring
            _ = G.toExtensiveForm.stepProb σ' z e *
                  ∑ w ∈ G.toExtensiveForm.stopsBelow i k (z ++ [e]),
                    G.toExtensiveForm.finitePrefixProbFrom σ' (z ++ [e])
                        (w.drop (z ++ [e]).length) *
                      (G.continuationValue σ w i - G.continuationValue σ' w i) := by
                rw [hchild]
            _ = ∑ w ∈ G.toExtensiveForm.stopsBelow i k (z ++ [e]),
                  G.toExtensiveForm.finitePrefixProbFrom σ' z (w.drop z.length) *
                    (G.continuationValue σ w i - G.continuationValue σ' w i) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun w hw => ?_)
                obtain ⟨t, rfl⟩ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw
                have hassoc : z ++ [e] ++ t = z ++ e :: t := by
                  rw [List.append_assoc]; rfl
                have hdrop : (z ++ [e] ++ t).drop z.length = e :: t := by
                  rw [hassoc, List.drop_left]
                have hdrop' : (z ++ [e] ++ t).drop (z ++ [e]).length = t := List.drop_left
                rw [hdrop, hdrop', G.toExtensiveForm.finitePrefixProbFrom_cons σ' z e t,
                  mul_assoc]
        · -- Stops below distinct children are disjoint: a common stop would force equal edges.
          intro e₁ _ e₂ _ hne
          simp only [Function.onFun, Finset.disjoint_left]
          intro w hw₁ hw₂
          have h₁ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw₁
          have h₂ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw₂
          have htake₁ : z ++ [e₁] = w.take (z.length + 1) := by
            have := List.prefix_iff_eq_take.mp h₁
            rwa [List.length_append, List.length_singleton] at this
          have htake₂ : z ++ [e₂] = w.take (z.length + 1) := by
            have := List.prefix_iff_eq_take.mp h₂
            rwa [List.length_append, List.length_singleton] at this
          have : z ++ [e₁] = z ++ [e₂] := htake₁.trans htake₂.symm
          exact hne (by simpa using this)

/-- **The next-stop frontier below an `i`-mover**: The union of the children's stop frontiers. The
deeper-deviation step expands the surgery residual at a support node onto exactly this set
(`oneShotSurgery_residual_nextStops`). -/
noncomputable def ExtensiveForm.nextStops (G : ExtensiveForm I E) (i : I) (k : ℕ)
    (x : List E) : Finset (List E) :=
  (G.emitImage x).biUnion (fun e => G.stopsBelow i k (x ++ [e]))

/-- Membership in the next-stop frontier of a reachable node, characterized: The strict extensions
of `x` that are reachable `i`-movers with no `i`-mover strictly between, within the depth budget. -/
theorem ExtensiveForm.mem_nextStops_iff (G : ExtensiveForm I E) (i : I) (k : ℕ)
    {x w : List E} (hx : G.IsReachable x) :
    w ∈ G.nextStops i k x ↔
      x <+: w ∧ x ≠ w ∧ G.IsReachable w ∧ (G.tree.nodeKind w).movesAt i ∧
        (∀ r : ℕ, x.length < r → r < w.length →
          ¬ (G.tree.nodeKind (w.take r)).movesAt i) ∧
        w.length < x.length + 1 + k := by
  unfold ExtensiveForm.nextStops
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hw⟩
    have hchild : G.IsReachable (x ++ [e]) := G.isReachable_concat_of_mem_emitImage hx he
    obtain ⟨hpre_c, hwr, hwmv, hbet_c, hlen_c⟩ := (G.mem_stopsBelow_iff i k hchild).mp hw
    have hxlt : x.length < w.length := by
      have h1 : (x ++ [e]).length ≤ w.length := hpre_c.length_le
      simp only [List.length_append, List.length_singleton] at h1
      omega
    refine ⟨(x.prefix_append [e]).trans hpre_c,
      fun heq => by rw [heq] at hxlt; exact absurd hxlt (lt_irrefl _), hwr, hwmv, ?_, ?_⟩
    · intro r hr hr'
      refine hbet_c r ?_ hr'
      simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton] at hlen_c
      omega
  · rintro ⟨hpre, hne, hwr, hwmv, hbet, hlen⟩
    have hxlt : x.length < w.length := by
      rcases Nat.eq_or_lt_of_le hpre.length_le with heq | hlt
      · exact absurd (List.IsPrefix.eq_of_length hpre heq) hne
      · exact hlt
    have htake : w.take x.length = x := (List.prefix_iff_eq_take.mp hpre).symm
    obtain ⟨e, hxe⟩ : ∃ e, w.take (x.length + 1) = x ++ [e] := by
      refine ⟨w[x.length], ?_⟩
      rw [List.take_add_one, List.getElem?_eq_getElem hxlt, htake]
      rfl
    have hchild_pre : x ++ [e] <+: w := by
      rw [← hxe]
      exact List.take_prefix _ w
    have hchild : G.IsReachable (x ++ [e]) :=
      ExtensiveForm.IsReachable.of_prefix G hwr hchild_pre
    have he : e ∈ G.emitImage x :=
      (G.mem_emitImage_iff_emits x e).mpr (G.emits_of_isReachable_concat hchild)
    refine ⟨e, he, (G.mem_stopsBelow_iff i k hchild).mpr ⟨hchild_pre, hwr, hwmv, ?_, ?_⟩⟩
    · intro r hr hr'
      refine hbet r ?_ hr'
      simp only [List.length_append, List.length_singleton] at hr
      omega
    · simp only [List.length_append, List.length_singleton]
      omega

/-- **Surgery-residual expansion onto the next-stop frontier (undiscounted).** At a reachable
`i`-mover `x`, the residual between the one-shot surgery at `x`'s own information set and the full
deviation `σ'` expands onto the next-stop frontier with `σ'`-transition weights and full-deviation
stop residuals: The surgery and `σ'` share the head step at `x`
(`oneShotSurgery_stepProb_eq_of_movesAt`), below the head the surgery values coincide with `σ`'s
(`oneShotSurgery_continuationValue_eq_below`, via `noRevisit`), and the `σ`-vs-`σ'` residual then
propagates by `continuationValue_residual_stops`. -/
theorem oneShotSurgery_residual_nextStops (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hδ : G.discount = 1) (i : I) (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ') {x : List E}
    (hxr : G.toExtensiveForm.IsReachable x)
    (hxm : (G.toExtensiveForm.tree.nodeKind x).movesAt i) (k : ℕ)
    (hk : N ≤ x.length + 1 + k) :
    G.continuationValue (oneShotSurgery G.toExtensiveForm σ σ' i (G.info.observe i x)) x i -
        G.continuationValue σ' x i =
      ∑ w ∈ G.toExtensiveForm.nextStops i k x,
        G.toExtensiveForm.finitePrefixProbFrom σ' x (w.drop x.length) *
          (G.continuationValue σ w i - G.continuationValue σ' w i) := by
  have hnt : ∀ p : I → ℝ, G.toExtensiveForm.tree.nodeKind x ≠ .terminal p :=
    NodeKind.not_terminal_of_movesAt hxm
  rw [G.continuationValue_eventSum hno_joint _ x i hnt,
    G.continuationValue_eventSum hno_joint σ' x i hnt, ← Finset.sum_sub_distrib]
  unfold ExtensiveForm.nextStops
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun e he => ?_)
    have hsurg_step := oneShotSurgery_stepProb_eq_of_movesAt G i σ σ' hdev hxm e
    have hcr : G.toExtensiveForm.IsReachable (x ++ [e]) :=
      G.toExtensiveForm.isReachable_concat_of_mem_emitImage hxr he
    have hbelow := oneShotSurgery_continuationValue_eq_below G hfd hpr hno_joint σ σ' i hxr
      hxm hcr i
    have hseg := continuationValue_residual_stops G hfd hno_joint hδ i σ σ' hdev k (x ++ [e])
      (by rw [List.length_append, List.length_singleton]; omega)
    calc G.toExtensiveForm.stepProb (oneShotSurgery G.toExtensiveForm σ σ' i
              (G.info.observe i x)) x e *
            (G.stepPayoff x e i + G.discount *
              G.continuationValue (oneShotSurgery G.toExtensiveForm σ σ' i
                (G.info.observe i x)) (x ++ [e]) i) -
          G.toExtensiveForm.stepProb σ' x e *
            (G.stepPayoff x e i + G.discount * G.continuationValue σ' (x ++ [e]) i)
        = G.toExtensiveForm.stepProb σ' x e *
            (G.continuationValue σ (x ++ [e]) i - G.continuationValue σ' (x ++ [e]) i) := by
          rw [hsurg_step, hbelow, hδ]
          ring
      _ = G.toExtensiveForm.stepProb σ' x e *
            ∑ w ∈ G.toExtensiveForm.stopsBelow i k (x ++ [e]),
              G.toExtensiveForm.finitePrefixProbFrom σ' (x ++ [e]) (w.drop (x ++ [e]).length) *
                (G.continuationValue σ w i - G.continuationValue σ' w i) := by
          rw [hseg]
      _ = ∑ w ∈ G.toExtensiveForm.stopsBelow i k (x ++ [e]),
            G.toExtensiveForm.finitePrefixProbFrom σ' x (w.drop x.length) *
              (G.continuationValue σ w i - G.continuationValue σ' w i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun w hw => ?_)
          obtain ⟨t, rfl⟩ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw
          have hassoc : x ++ [e] ++ t = x ++ e :: t := by
            rw [List.append_assoc]; rfl
          have hdrop : (x ++ [e] ++ t).drop x.length = e :: t := by
            rw [hassoc, List.drop_left]
          have hdrop' : (x ++ [e] ++ t).drop (x ++ [e]).length = t := List.drop_left
          rw [hdrop, hdrop', G.toExtensiveForm.finitePrefixProbFrom_cons σ' x e t, mul_assoc]
  · intro e₁ _ e₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro w hw₁ hw₂
    have h₁ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw₁
    have h₂ := G.toExtensiveForm.prefix_of_mem_stopsBelow hw₂
    have htake₁ : x ++ [e₁] = w.take (x.length + 1) := by
      have := List.prefix_iff_eq_take.mp h₁
      rwa [List.length_append, List.length_singleton] at this
    have htake₂ : x ++ [e₂] = w.take (x.length + 1) := by
      have := List.prefix_iff_eq_take.mp h₂
      rwa [List.length_append, List.length_singleton] at this
    exact hne (by simpa using htake₁.trans htake₂.symm)

end Econlib.GameTheory
