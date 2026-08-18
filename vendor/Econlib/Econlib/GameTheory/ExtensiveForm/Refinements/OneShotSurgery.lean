/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.BeliefTower

/-!
# One-shot surgery and reach/belief-weighted comparison atoms

The single-information-set edit (`oneShotSurgery`) reverting one coordinate of a deviation, and the
per-information-set comparison atoms — both the reach-weighted form (`reachWeighted_oneShot_step`)
and the belief-weighted form (`beliefWeighted_oneShot_step`) — that the backward induction of the
extensive-form one-shot deviation principle invokes at each touched information set, together with
the weighted Bellman peels of a continuation-value residual.

## Main definitions

* `oneShotSurgery`: The strategy copying a deviation's action at one information set, `σ` elsewhere.

## Main statements

* `beliefWeighted_oneShot_step`: The belief-weighted one-shot atom, valid on and off path.
* `reachWeighted_surgery_atom_nonneg`: The reach-weighted surgery residual is nonnegative.
* `weighted_peel`: A multiplicatively-pushed weighted Bellman peel of a value residual.

## References

* Fudenberg, Drew, and Jean Tirole. 1993. *Game Theory*. The MIT Press.

## Tags

extensive form, one-shot deviation principle, sequential rationality
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-! ### Reach- and belief-weighted one-shot atoms -/

/-- At a positive-probability information set, Bayes consistency rewrites the belief-weighted
`assessmentValue` of any strategy (kept on the equilibrium beliefs) as the reach-weighted average
of continuation values: The equilibrium belief at a node is its reach probability divided by the
total information-set mass (`bayesBeliefAt`), so

`assessmentValue {strategy := s, beliefs := μ} i obs`
`= (∑ x ∈ μ.support i obs, reachProb σ x.1 * continuationValue s x.1 i)`
`    / infoSetProb σ μ i obs`.

Here `σ = a.strategy` is the equilibrium strategy that fixes the beliefs; `s` ranges over the
deviations being scored. -/
theorem assessmentValue_eq_reachWeighted (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (hbayes : IsBayesConsistent G.toExtensiveForm a)
    (i : I) (obs : G.info.Obs i)
    (hpos : 0 < infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs)
    (s : G.toExtensiveForm.BehavioralStrategy) :
    assessmentValue G { strategy := s, beliefs := a.beliefs } i obs =
      (∑ x ∈ a.beliefs.support i obs,
          reachProb G.toExtensiveForm a.strategy x.1 * G.continuationValue s x.1 i) /
        infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs := by
  set μ := a.beliefs with hμ
  set σ := a.strategy with hσ
  -- Bayes consistency rewrites each belief weight `μ.belief i obs x` as the Bayesian posterior, and
  -- on the positive branch the posterior is `reachProb σ x.1 / infoSetProb σ μ i obs`.
  have hweight : ∀ x ∈ μ.support i obs,
      μ.belief i obs x =
        reachProb G.toExtensiveForm σ x.1 /
          infoSetProb G.toExtensiveForm σ μ i obs := by
    intro x hx
    -- `μ.belief i obs x = μ.prob i obs x.1` (subtype) `= bayesBeliefAt σ μ i obs x.1` (Bayes).
    rw [← μ.prob_subtype i obs x, hbayes i obs hpos x.1]
    -- All three guards of `bayesBeliefAt` fire: info-set membership `x.2`, support `hx`, `hpos`.
    unfold bayesBeliefAt
    rw [dif_pos x.2]
    have hmem : (⟨x.1, x.2⟩ : G.InfoSet i obs) ∈ μ.support i obs := by
      simpa using hx
    rw [if_pos hmem, dif_pos hpos]
  -- Substitute the weights and pull the common denominator out of the sum.
  unfold assessmentValue
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [hweight x hx, div_mul_eq_mul_div]

/-- At an *unrealized* information set (empty represented support) the belief-weighted value is the
empty sum, hence `0`, for *any* strategy kept on the equilibrium beliefs. So the sequential-
rationality inequality is the vacuous `0 ≥ 0` there. -/
theorem assessmentValue_eq_zero_of_support_empty (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (i : I) (obs : G.info.Obs i)
    (hempty : a.beliefs.support i obs = ∅) (s : G.toExtensiveForm.BehavioralStrategy) :
    assessmentValue G { strategy := s, beliefs := a.beliefs } i obs = 0 := by
  -- `assessmentValue` is a sum over `support i obs = ∅`, hence `0`.
  unfold assessmentValue
  simp [hempty]

/-- **Reach degeneracy off path.** If an information set has zero total mass under `σ` but nonempty
represented support, then — since each reach probability is nonnegative and they sum to zero —
every represented node has zero reach probability under `σ`. This is why the reach-weighted form is
useless off path: The reach-weighted sum collapses to `0`, and the belief weights must be obtained
by a limiting argument instead. -/
theorem reachProb_eq_zero_of_infoSetProb_eq_zero (G : ExtensiveGame I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (μ : BeliefSystem G.toExtensiveForm)
    (i : I) (obs : G.info.Obs i)
    (hzero : infoSetProb G.toExtensiveForm σ μ i obs = 0)
    (x : G.toExtensiveForm.InfoSet i obs) (hx : x ∈ μ.support i obs) :
    reachProb G.toExtensiveForm σ x.1 = 0 := by
  -- A finite sum of nonnegatives is zero iff every term is zero.
  unfold infoSetProb at hzero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => reachProb_nonneg G.toExtensiveForm σ y.1)).mp hzero x hx

/-! ### One-shot surgery -/

/-- **Single-layer reach-weighted one-shot inequality (the induction atom).** At an *on-path*
information set `(i, obs')` (positive `infoSetProb`), one-shot sequential rationality, rewritten in
reach-weighted form by `assessmentValue_eq_reachWeighted` on both sides and cleared of the positive
denominator, says: A one-shot info-set deviation `τ` at `(i, obs')` weakly lowers the
reach-weighted continuation sum over that information set's represented support. This is the
per-layer comparison the backward induction of `reachWeighted_continuationValue_le_of_oneShot`
invokes at each touched information set; off-path layers carry zero reach weight and drop out, so
`hone` is only ever used where its reach-weighted form is valid. -/
theorem reachWeighted_oneShot_step (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (hbayes : IsBayesConsistent G.toExtensiveForm a)
    (hone : IsSequentiallyRationalOneShot G a) (i : I) (obs' : G.info.Obs i)
    (hpos : 0 < infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs')
    (τ : G.toExtensiveForm.BehavioralStrategy)
    (hτ : IsInfoSetDeviation G.toExtensiveForm i obs' a.strategy τ) :
    (∑ x ∈ a.beliefs.support i obs',
        reachProb G.toExtensiveForm a.strategy x.1 * G.continuationValue τ x.1 i) ≤
      (∑ x ∈ a.beliefs.support i obs',
        reachProb G.toExtensiveForm a.strategy x.1 * G.continuationValue a.strategy x.1 i) := by
  -- `hone` gives `assessmentValue a ≥ assessmentValue {τ, beliefs}`; both rewrite to reach-weighted
  -- averages over the same positive denominator `infoSetProb`, and clearing it preserves the order.
  have hone_step := hone i obs' τ hτ
  rw [ge_iff_le, assessmentValue_eq_reachWeighted G a hbayes i obs' hpos τ,
    show a = { strategy := a.strategy, beliefs := a.beliefs } from rfl,
    assessmentValue_eq_reachWeighted G a hbayes i obs' hpos a.strategy] at hone_step
  exact (div_le_div_iff_of_pos_right hpos).mp hone_step

open Classical in
/-- **One-shot surgery.** The strategy agreeing with `τ` at the single coordinate `(i, obs)` and
with `σ` at every other `(j, obs')`. By construction it is a one-shot info-set deviation of `σ` at
`(i, obs)` (`oneShotSurgery_isInfoSetDeviation`), in particular a unilateral `i`-deviation
(`oneShotSurgery_unilateralDeviation`); it copies `τ`'s action at `(i, obs)`
(`oneShotSurgery_at_self`). -/
noncomputable def oneShotSurgery (G : ExtensiveForm I E) (σ τ : G.BehavioralStrategy)
    (i : I) (obs : G.info.Obs i) : G.BehavioralStrategy :=
  fun j obs' => if (⟨j, obs'⟩ : Σ k, G.info.Obs k) = ⟨i, obs⟩ then τ j obs' else σ j obs'

omit [DecidableEq E] in
/-- The surgery is a one-shot info-set deviation of `σ` at `(i, obs)`: It agrees with `σ` at every
coordinate other than `(i, obs)`. -/
theorem oneShotSurgery_isInfoSetDeviation (G : ExtensiveForm I E) (σ τ : G.BehavioralStrategy)
    (i : I) (obs : G.info.Obs i) :
    IsInfoSetDeviation G i obs σ (oneShotSurgery G σ τ i obs) := by
  intro j obs' hjg
  simp only [oneShotSurgery]
  rw [if_neg hjg]

omit [DecidableEq E] in
/-- A one-shot surgery is in particular a unilateral `i`-deviation of `σ`. -/
theorem oneShotSurgery_unilateralDeviation (G : ExtensiveForm I E) (σ τ : G.BehavioralStrategy)
    (i : I) (obs : G.info.Obs i) :
    G.unilateralDeviation i σ (oneShotSurgery G σ τ i obs) :=
  unilateralDeviation_of_isInfoSetDeviation G i obs
    (oneShotSurgery_isInfoSetDeviation G σ τ i obs)

omit [DecidableEq E] in
/-- The surgery copies `τ`'s action at the coordinate `(i, obs)`. -/
theorem oneShotSurgery_at_self (G : ExtensiveForm I E) (σ τ : G.BehavioralStrategy)
    (i : I) (obs : G.info.Obs i) :
    oneShotSurgery G σ τ i obs i obs = τ i obs := by
  simp only [oneShotSurgery, if_pos]

/-- **Belief-weighted one-shot atom (valid on and off path).** The raw content of `hone`, unfolded:
A one-shot info-set deviation `τ` at `(i, obs')` does not raise the belief-weighted continuation
sum over that information set's represented support. No positivity is required — this is the
belief-weighted form, in which the equilibrium beliefs `a.beliefs` are the fixed weights regardless
of whether `(i, obs')` is reached by `σ`. -/
theorem beliefWeighted_oneShot_step (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (hone : IsSequentiallyRationalOneShot G a)
    (i : I) (obs' : G.info.Obs i) (τ : G.toExtensiveForm.BehavioralStrategy)
    (hτ : IsInfoSetDeviation G.toExtensiveForm i obs' a.strategy τ) :
    (∑ x ∈ a.beliefs.support i obs',
        a.beliefs.belief i obs' x * G.continuationValue τ x.1 i) ≤
      (∑ x ∈ a.beliefs.support i obs',
        a.beliefs.belief i obs' x * G.continuationValue a.strategy x.1 i) := by
  -- `hone i obs' τ hτ` is exactly `assessmentValue {τ, μ} ≤ assessmentValue {σ, μ}`, which unfolds
  -- termwise to the belief-weighted sums above.
  have h := hone i obs' τ hτ
  simpa only [assessmentValue, ge_iff_le] using h

/-! ### Weighted Bellman peels of a value residual -/

/-- **Reach-weighted player-node peel.** At a player node `y`, if two strategies `τ, ρ` both share
the deviation `σ'`'s head step probabilities at `y`, the `reachProb σ'`-weighted continuation-value
residual at `y` equals `δ` times the sum of the children's `reachProb σ'`-weighted residuals. -/
theorem reachWeighted_player_peel (G : ExtensiveGame I E) (i : I)
    (σ' τ ρ : G.toExtensiveForm.BehavioralStrategy)
    {y : List E} {n : PlayerNode I E} (hnk : G.toExtensiveForm.tree.nodeKind y = .player n)
    (hτ : ∀ e, G.toExtensiveForm.stepProb τ y e = G.toExtensiveForm.stepProb σ' y e)
    (hρ : ∀ e, G.toExtensiveForm.stepProb ρ y e = G.toExtensiveForm.stepProb σ' y e) :
    reachProb G.toExtensiveForm σ' y *
        (G.continuationValue τ y i - G.continuationValue ρ y i) =
      G.discount * ∑ e ∈ Finset.univ.image n.emit,
        reachProb G.toExtensiveForm σ' (y ++ [e]) *
          (G.continuationValue τ (y ++ [e]) i - G.continuationValue ρ (y ++ [e]) i) := by
  -- Peel the Bellman at `y` on both `τ` and `ρ`, regrouped to the `stepProb`-weighted event sum.
  rw [G.continuationValue_player_eventSum τ y i hnk, G.continuationValue_player_eventSum ρ y i hnk]
  -- The head step weights agree with `σ'`'s, so each event class shares a common weight.
  simp only [hτ, hρ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  -- `reachProb σ' y · stepProb σ' y e = reachProb σ' (y ++ [e])`.
  have hreach : reachProb G.toExtensiveForm σ' (y ++ [e]) =
      reachProb G.toExtensiveForm σ' y * G.toExtensiveForm.stepProb σ' y e := by
    rw [reachProb_append G.toExtensiveForm σ' y [e],
      G.toExtensiveForm.finitePrefixProbFrom_cons σ' y e [],
      G.toExtensiveForm.finitePrefixProbFrom_nil σ' (y ++ [e]), mul_one]
  rw [hreach]; ring

/-- **Proportional-weight conversion (abstract).** If two weight families `w, v` on a finset `s`
are cross-proportional (`w y · v y' = w y' · v y` for all `y, y' ∈ s`), then for any scoring
function `f` the `w`-weighted and `v`-weighted sums are proportional with the total masses as the
proportionality constants: `(∑ v) · (∑ w·f) = (∑ w) · (∑ v·f)`. This is the algebraic core that
interconverts the reach-weighted (`w = reachProb σ'`) and belief-weighted (`v = μ`) sums over an
information set's support. -/
theorem sum_mul_sum_proportional {ι : Type*} (s : Finset ι) (w v f : ι → ℝ)
    (hprop : ∀ y ∈ s, ∀ y' ∈ s, w y * v y' = w y' * v y) :
    (∑ y ∈ s, v y) * (∑ y ∈ s, w y * f y) =
      (∑ y ∈ s, w y) * (∑ y ∈ s, v y * f y) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun y hy => Finset.sum_congr rfl (fun y' hy' => ?_))
  -- termwise: `v y · (w y' · f y') = w y · (v y' · f y')`, since `v y · w y' = w y · v y'`
  -- (the commuted cross-proportionality `hprop`).
  have h : v y * w y' = w y * v y' := by
    have := hprop y' hy' y hy; linarith [this, mul_comm (w y') (v y), mul_comm (w y) (v y')]
  calc v y * (w y' * f y') = (v y * w y') * f y' := by ring
    _ = (w y * v y') * f y' := by rw [h]
    _ = w y * (v y' * f y') := by ring

/-- **Uniform weighted Bellman peel of a value residual.** At a reachable non-terminal node `y`
(joint / general-chance excluded), if two strategies `τ, ρ` share the deviation `σ'`'s head step
probabilities at `y` and the weight `W` is pushed down multiplicatively along `σ'`
(`W (y ++ [e]) = W y · stepProb σ' y e`), the `W`-weighted residual `V_τ − V_ρ` at `y` equals `δ`
times the `W`-weighted children residual sum over `emitImage y`. Generalizes
`reachWeighted_player_peel` to an arbitrary multiplicatively-pushed weight (so the recursion can
carry the belief-induced weight, not only `reachProb σ'`) and to chance-finite nodes. -/
theorem weighted_peel (G : ExtensiveGame I E) (i : I)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σ' τ ρ : G.toExtensiveForm.BehavioralStrategy) (W : List E → ℝ) {y : List E}
    (hnt : ∀ p : I → ℝ, G.toExtensiveForm.tree.nodeKind y ≠ .terminal p)
    (hτ : ∀ e, G.toExtensiveForm.stepProb τ y e = G.toExtensiveForm.stepProb σ' y e)
    (hρ : ∀ e, G.toExtensiveForm.stepProb ρ y e = G.toExtensiveForm.stepProb σ' y e)
    (hW : ∀ e ∈ G.toExtensiveForm.emitImage y,
      W (y ++ [e]) = W y * G.toExtensiveForm.stepProb σ' y e) :
    W y * (G.continuationValue τ y i - G.continuationValue ρ y i) =
      G.discount * ∑ e ∈ G.toExtensiveForm.emitImage y,
        W (y ++ [e]) *
          (G.continuationValue τ (y ++ [e]) i - G.continuationValue ρ (y ++ [e]) i) := by
  rw [G.continuationValue_eventSum hno_joint τ y i hnt,
    G.continuationValue_eventSum hno_joint ρ y i hnt]
  simp only [hτ, hρ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [hW e he]; ring

/-- **Reach-weighted one-shot atom (single-layer comparison, in residual form).** At any
information set `(i, ω)`, with `τ := oneShotSurgery σ σ' i ω` the one-shot surgery copying `σ'`'s
action at `(i, ω)`, the `reachProb σ'`-weighted residual `V_σ − V_τ` over the support is
nonnegative:

`0 ≤ ∑ x ∈ supp(i, ω), reachProb σ' x.1 · (V_σ(x.1) − V_τ(x.1))`.

Bridges the belief-weighted one-shot atom (`beliefWeighted_oneShot_step` for the info-set deviation
`τ`, which gives `∑ μ · (V_σ − V_τ) ≥ 0` with no positivity) to the reach-weighted recursion via
the division-free proportionality conversion `sum_mul_sum_proportional`, whose
cross-proportionality hypothesis is the `consistency_belief_tower` for `σ'` (with the unreachable
support nodes carrying both zero belief and zero reach, so the proportionality is automatic
there). -/
theorem reachWeighted_surgery_atom_nonneg (G : ExtensiveGame I E)
    (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (hone : IsSequentiallyRationalOneShot G a) (i : I) (ω : G.info.Obs i)
    (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i a.strategy σ') :
    0 ≤ ∑ x ∈ a.beliefs.support i ω,
        reachProb G.toExtensiveForm σ' x.1 *
          (G.continuationValue a.strategy x.1 i -
            G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i ω) x.1 i) := by
  classical
  set σ := a.strategy with hσ
  set μ := a.beliefs with hμ
  set τ := oneShotSurgery G.toExtensiveForm σ σ' i ω with hτ
  set S := μ.support i ω with hS
  -- The scoring function and the two weight families.
  set f : G.toExtensiveForm.InfoSet i ω → ℝ :=
    fun x => G.continuationValue σ x.1 i - G.continuationValue τ x.1 i with hf
  set w : G.toExtensiveForm.InfoSet i ω → ℝ :=
    fun x => reachProb G.toExtensiveForm σ' x.1 with hw
  set v : G.toExtensiveForm.InfoSet i ω → ℝ := fun x => μ.belief i ω x with hv
  -- Cross-proportionality of `w` (reach σ') and `v` (μ) on the support, via the belief tower.
  have hprop : ∀ y ∈ S, ∀ y' ∈ S, w y * v y' = w y' * v y := by
    intro y hy y' hy'
    by_cases hyr : G.toExtensiveForm.IsReachable y.1
    · by_cases hy'r : G.toExtensiveForm.IsReachable y'.1
      · -- both reachable: the consistency belief tower (in the form
        -- `μ y · reach σ' y' = μ y' · reach σ' y`).
        have htower := consistency_belief_tower G hpr hno_joint a hcons i ω σ' hdev
          y y' hy hy' hyr hy'r
        simp only [hw, hv]; linarith [htower]
      · -- `y'` unreachable ⇒ both `reach σ' y' = 0` and `μ y' = 0`.
        have hr0 : reachProb G.toExtensiveForm σ' y'.1 = 0 :=
          G.reachProb_eq_zero_of_not_isReachable σ' y'.1 hy'r
        have hb0 : μ.belief i ω y' = 0 :=
          belief_eq_zero_of_not_isReachable G a hcons i ω y' hy'r
        simp only [hw, hv, hr0, hb0, mul_zero, zero_mul]
    · -- `y` unreachable ⇒ both `reach σ' y = 0` and `μ y = 0`.
      have hr0 : reachProb G.toExtensiveForm σ' y.1 = 0 :=
        G.reachProb_eq_zero_of_not_isReachable σ' y.1 hyr
      have hb0 : μ.belief i ω y = 0 :=
        belief_eq_zero_of_not_isReachable G a hcons i ω y hyr
      simp only [hw, hv, hr0, hb0, mul_zero, zero_mul]
  -- The proportional-conversion identity: `(∑ v)·(∑ w·f) = (∑ w)·(∑ v·f)`.
  have hconv := sum_mul_sum_proportional S w v f hprop
  -- The belief-weighted atom for the info-set deviation `τ`: `∑ μ·V_τ ≤ ∑ μ·V_σ`, i.e.
  -- `0 ≤ ∑ v·f`.
  have hatom : 0 ≤ ∑ x ∈ S, v x * f x := by
    have hstep := beliefWeighted_oneShot_step G a hone i ω τ
      (oneShotSurgery_isInfoSetDeviation G.toExtensiveForm σ σ' i ω)
    have : ∑ x ∈ S, v x * f x =
        (∑ x ∈ S, μ.belief i ω x * G.continuationValue σ x.1 i) -
          (∑ x ∈ S, μ.belief i ω x * G.continuationValue τ x.1 i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [hv, hf]; ring
    rw [this]; linarith [hstep]
  -- The goal is `0 ≤ ∑ w·f`. Cases on whether the support is empty.
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · simp [hSe]
  · -- `∑ v = 1` (belief sums to one on a nonempty info set), so `∑ w·f = (∑ w)·(∑ v·f) ≥ 0`.
    have hsumv : ∑ x ∈ S, v x = 1 := μ.belief_sum_one i ω hSne
    rw [hsumv, one_mul] at hconv
    have hsumw_nonneg : 0 ≤ ∑ x ∈ S, w x :=
      Finset.sum_nonneg (fun x _ => reachProb_nonneg G.toExtensiveForm σ' x.1)
    change 0 ≤ ∑ x ∈ S, w x * f x
    rw [hconv]
    exact mul_nonneg hsumw_nonneg hatom

omit [DecidableEq E] in
/-- **Terminal residual vanishes.** At a history `z` of length `≥ N` (terminal, by finite depth),
the continuation value is the terminal payoff regardless of strategy, so the residual
`V_σ z − V_{σ'} z` is `0`. -/
theorem continuationValue_residual_eq_zero_of_terminal (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (i : I) {z : List E} (hz : N ≤ z.length) :
    G.continuationValue σ z i - G.continuationValue σ' z i = 0 := by
  obtain ⟨p, hp⟩ := hfd z hz
  have hval : ∀ ρ : G.toExtensiveForm.BehavioralStrategy, G.continuationValue ρ z i = p i :=
    fun ρ => by rw [G.continuationValue_eq ρ z i]; simp only [hp, nodeStepValue_terminal]
  rw [hval σ, hval σ']; ring

/-- **Frontier coverage completeness.** A finset `F` of histories is coverage-complete for
`(i, σ')` if, whenever an `i`-mover `z ∈ F` belongs to information set `ω = observe i z`, every
positive-`σ'`-reach support node of `(i, ω)` also lies in `F` — the granularity at which the
per-information-set one-shot atom (over the *whole* support) applies to a frontier's contribution.
Standalone API: The final proof of the deviation principle advances by next-stop frontiers
(`ExtensiveForm.nextStops`) instead, whose blocks are complete by `LastStopAlign`. -/
def FrontierComplete (G : ExtensiveForm I E) (μ : BeliefSystem G) (i : I)
    (σ' : G.BehavioralStrategy) (F : Finset (List E)) : Prop :=
  ∀ z ∈ F, (G.tree.nodeKind z).movesAt i →
    ∀ x ∈ μ.support i (G.info.observe i z), 0 < reachProb G σ' x.1 → x.1 ∈ F

/-- **Reach-weighted residual peels to the children frontier.** For a *non-terminal* node `z`
(joint / general-chance excluded), the `reachProb σ'`-weighted residual `V_σ z − V_{σ'} z` equals
`δ` times the sum, over the emitted children, of the `reachProb σ'`-weighted children residuals —
*provided* `σ` and `σ'` share `σ'`'s head step probabilities at `z`. This is the non-`i` peel: Off
`i`, `σ = σ'` at the moving coordinates (`hdev` + `stepProb_congr_movers`), so the head weights
coincide and `weighted_peel` (with `W := reachProb σ'`, `τ := σ`, `ρ := σ'`) applies. -/
theorem reachWeighted_residual_peel_nonMover (G : ExtensiveGame I E) (i : I)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    {z : List E}
    (hnt : ∀ p : I → ℝ, G.toExtensiveForm.tree.nodeKind z ≠ .terminal p)
    (hσ : ∀ e, G.toExtensiveForm.stepProb σ z e = G.toExtensiveForm.stepProb σ' z e) :
    reachProb G.toExtensiveForm σ' z *
        (G.continuationValue σ z i - G.continuationValue σ' z i) =
      G.discount * ∑ e ∈ G.toExtensiveForm.emitImage z,
        reachProb G.toExtensiveForm σ' (z ++ [e]) *
          (G.continuationValue σ (z ++ [e]) i - G.continuationValue σ' (z ++ [e]) i) := by
  refine weighted_peel G i hno_joint σ' σ σ' (reachProb G.toExtensiveForm σ') hnt hσ
    (fun _ => rfl) (fun e _ => ?_)
  rw [reachProb_append G.toExtensiveForm σ' z [e],
    G.toExtensiveForm.finitePrefixProbFrom_cons σ' z e [],
    G.toExtensiveForm.finitePrefixProbFrom_nil σ' (z ++ [e]), mul_one]

/-! ### Surgery below an `i`-mover -/

/-- **Below an `i`-mover the surgery agrees with `σ` on continuation value.** At a reachable child
`z ++ [e]` of a reachable `i`-mover `z` (information set `ω = observe i z`), the one-shot surgery
`τ := oneShotSurgery σ σ' i ω` induces the same continuation value as `σ`. The surgery differs from
`σ` only at the `(i, ω)` coordinate, which is consulted only at an `i`-mover observing `ω`; by
`noRevisit` no reachable strict descendant of `z` is such a node (it would revisit `(i, ω)`), so
`continuationValue_congr_reachable` collapses the residual. -/
theorem oneShotSurgery_continuationValue_eq_below (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σ σ' : G.toExtensiveForm.BehavioralStrategy) (i : I) {z : List E}
    (hzr : G.toExtensiveForm.IsReachable z)
    (hzm : (G.toExtensiveForm.tree.nodeKind z).movesAt i) {e : E}
    (hcr : G.toExtensiveForm.IsReachable (z ++ [e])) (j : I) :
    G.continuationValue (oneShotSurgery G.toExtensiveForm σ σ' i (G.info.observe i z))
        (z ++ [e]) j =
      G.continuationValue σ (z ++ [e]) j := by
  set ω := G.info.observe i z with hω
  set τ := oneShotSurgery G.toExtensiveForm σ σ' i ω with hτ
  refine G.continuationValue_congr_reachable hfd hno_joint τ σ (z ++ [e]) j hcr
    (fun g hg hgr l hlm => ?_)
  -- `τ l obs' = σ l obs'` unless `(l, obs') = (i, ω)`; rule that out by `noRevisit`.
  by_cases hcase : (⟨l, G.info.observe l g⟩ : Σ k, G.info.Obs k) = ⟨i, ω⟩
  · -- `l = i` and `observe i g = ω`; then `g` is an `i`-mover at `ω`, a strict descendant of `z`
    -- in the same info set, contradicting `noRevisit`.
    obtain ⟨hli, hobseq⟩ := Sigma.mk.inj_iff.mp hcase
    subst hli
    have hgm : (G.tree.nodeKind g).movesAt l := hlm
    have hzpre : z <+: g := (List.prefix_append z [e]).trans hg
    have hgo : G.info.observe l g = ω := eq_of_heq hobseq
    have hzg : z = g := hpr.noRevisit l z g hzr hgr hzpre (by rw [hgo]) hzm hgm
    -- `z = g` but `z ++ [e] <+: g`, so `g.length ≥ z.length + 1 > z.length = g.length`.
    have hlen : (z ++ [e]).length ≤ g.length := hg.length_le
    rw [List.length_append, List.length_singleton] at hlen
    rw [← hzg] at hlen; omega
  · -- Off the `(i, ω)` coordinate the surgery equals `σ`.
    simp only [hτ, oneShotSurgery, if_neg hcase]

/-- At an `i`-mover `z` (information set `ω = observe i z`), the one-shot surgery
`τ := oneShotSurgery σ σ' i ω` shares `σ'`'s head step probabilities: At the `(i, ω)` coordinate
both read `σ'`'s action (`τ` by construction, `σ'` itself), and at every non-`i` coordinate both
read `σ`'s action (`τ` by construction, `σ'` because it is a unilateral `i`-deviation of `σ`). -/
theorem oneShotSurgery_stepProb_eq_of_movesAt (G : ExtensiveGame I E) (i : I)
    (σ σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i σ σ') {z : List E}
    (hzm : (G.toExtensiveForm.tree.nodeKind z).movesAt i) (e : E) :
    G.toExtensiveForm.stepProb (oneShotSurgery G.toExtensiveForm σ σ' i
        (G.info.observe i z)) z e =
      G.toExtensiveForm.stepProb σ' z e := by
  refine stepProb_congr_movers G.toExtensiveForm _ σ' z e (fun j hj => ?_)
  set ω := G.info.observe i z with hω
  by_cases hji : j = i
  · -- `j = i`: the coordinate is `(i, observe i z) = (i, ω)`, where the surgery copies `σ'`.
    subst hji
    rw [hω]
    simp only [oneShotSurgery, if_true]
  · -- `j ≠ i`: the surgery reads `σ`, and `σ' j _ = σ j _` since `σ'` is unilateral `i`-dev.
    have hne : (⟨j, G.info.observe j z⟩ : Σ k, G.info.Obs k) ≠ ⟨i, ω⟩ := by
      intro heq; exact hji (congrArg Sigma.fst heq)
    simp only [oneShotSurgery, if_neg hne]
    exact (hdev j (G.info.observe j z) hji).symm

end Econlib.GameTheory
