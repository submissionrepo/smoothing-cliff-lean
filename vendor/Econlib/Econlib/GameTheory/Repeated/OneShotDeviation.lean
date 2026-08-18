/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Repeated.Basic

/-!
# One-shot deviation principle for repeated games

For an infinite-horizon discounted repeated game, subgame perfection is equivalent to the absence
of profitable one-shot deviations (Fudenberg and Tirole 1991): A public strategy `σ` is a
subgame-perfect equilibrium iff at every public history `h`, no player `i` raises their
continuation value by changing their mixed action at `h` alone, holding `σ` fixed everywhere else.
The one-shot deviation predicate is the existing `IsInfoSetDeviation` of the perfect-information
lift — under perfect monitoring an information set is a public history — so no new deviation notion
is added.

## Main definitions

* `RepeatedGame.NoProfitableOneShotDeviation`: No player gains from any one-shot deviation at any
  public history.

## Main statements

* `RepeatedGame.IsSubgamePerfectEquilibrium_iff_noProfitableOneShotDeviation`: The one-shot
  deviation principle.

## Notes

The hard direction (no profitable one-shot deviation implies subgame perfection) is the
unimprovability argument for discounted dynamic programs. Locality (`continuationValue_congr`)
makes the continuation value at `h` depend on the strategy only through its actions at
continuations of `h`. Finite-depth deviations
(`NoProfitableOneShotDeviation.continuationValue_le_of_eq_of_le`) are handled by induction on the
deviation depth `T`. Continuity at infinity (`abs_continuationValue_sub_le_of_eq_of_lt`) bounds the
continuation values of strategies that agree for `T` periods within `2 · payoffBound · δ^T`.
Truncating an arbitrary unilateral deviation to its first `T` periods and letting `T → ∞` closes
the argument.

## References

* Fudenberg, Drew, and Jean Tirole. 1993. *Game Theory*. The MIT Press.

## Tags

repeated games, one-shot deviation principle, osdp, unimprovability, subgame perfection
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

namespace RepeatedGame

variable (R : RepeatedGame)

/-! ### Locality: Continuation values depend only on play at continuations -/

/-- The one-period expected stage payoff at `h` depends on the strategy only through its mixed
actions at `h` itself. -/
lemma stagePayoff_congr {σ τ : R.PublicStrategy} (h : R.stage.PublicHistory)
    (hagree : ∀ j : R.stage.Player, σ j h = τ j h) (i : R.stage.Player) :
    R.stagePayoff σ h i = R.stagePayoff τ h i := by
  -- `atHistory` is `simplexTransport` applied to `σ j h`; `hagree` rewrites under it by `congrArg`.
  have hat : ∀ j : R.stage.Player, R.atHistory σ j h = R.atHistory τ j h := by
    intro j
    simp only [atHistory]
    exact congrArg (simplexTransport (R.iChoiceType_eq j h)) (hagree j)
  unfold stagePayoff
  exact congrArg (R.stage.expectedPayoff i) (funext hat)

/-- The one-period profile distribution at `h` depends on the strategy only through its mixed
actions at `h` itself. -/
lemma stageProfileProb_congr {σ τ : R.PublicStrategy} (h : R.stage.PublicHistory)
    (hagree : ∀ j : R.stage.Player, σ j h = τ j h) (a : R.stage.ActionProfile) :
    R.stageProfileProb σ h a = R.stageProfileProb τ h a := by
  -- Same `simplexTransport` congruence, factor by factor in the product of marginals.
  unfold stageProfileProb
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have hat : R.atHistory σ j h = R.atHistory τ j h := by
    simp only [atHistory]
    exact congrArg (simplexTransport (R.iChoiceType_eq j h)) (hagree j)
  rw [hat]

/-- Path probabilities from `h` depend on the strategy only through its actions at the proper
prefixes of the continuation: Strict-length agreement suffices. -/
lemma publicHistoryProbFrom_congr {σ τ : R.PublicStrategy} :
    ∀ (suffix h : R.stage.PublicHistory),
      (∀ (j : R.stage.Player) (pre : R.stage.PublicHistory),
        pre.length < suffix.length → σ j (h ++ pre) = τ j (h ++ pre)) →
      R.publicHistoryProbFrom σ h suffix = R.publicHistoryProbFrom τ h suffix := by
  -- Induction on `suffix`; the head step is `stepProb_eq_stageProfileProb` plus
  -- `stageProfileProb_congr` at `pre = []`, the tail re-roots at `h ++ [c]`.
  intro suffix
  induction suffix with
  | nil => intro h _; rfl
  | cons c rest ih =>
    intro h hagree
    rw [publicHistoryProbFrom_cons, publicHistoryProbFrom_cons,
      R.stepProb_eq_stageProfileProb σ h c, R.stepProb_eq_stageProfileProb τ h c]
    -- Head factor: agreement at `pre = []`, i.e. at `h` itself (length `0 < (c::rest).length`).
    have hhead : R.stageProfileProb σ h c = R.stageProfileProb τ h c := by
      refine R.stageProfileProb_congr h (fun j => ?_) c
      have := hagree j [] (by simp)
      rwa [List.append_nil] at this
    -- Tail factor: re-root at `h ++ [c]`; agreement at `[c] ++ pre` for `pre.length < rest.length`.
    have htail : R.publicHistoryProbFrom σ (h ++ [c]) rest =
        R.publicHistoryProbFrom τ (h ++ [c]) rest := by
      refine ih (h ++ [c]) (fun j pre hpre => ?_)
      have hlen : ([c] ++ pre).length < (c :: rest).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have := hagree j ([c] ++ pre) hlen
      rwa [← List.append_assoc] at this
    rw [hhead, htail]

/-- The period-`t` expected payoff after `h` depends on the strategy only through its actions in
the first `t + 1` periods after `h` (depths `0, …, t`). -/
lemma periodExpectedPayoff_congr {σ τ : R.PublicStrategy} (h : R.stage.PublicHistory) (t : ℕ)
    (i : R.stage.Player)
    (hagree : ∀ (j : R.stage.Player) (suffix : R.stage.PublicHistory),
      suffix.length ≤ t → σ j (h ++ suffix) = τ j (h ++ suffix)) :
    R.periodExpectedPayoff σ h t i = R.periodExpectedPayoff τ h t i := by
  -- Each summand: `publicHistoryProbFrom_congr` (depths `< t`) times `stagePayoff_congr` at
  -- depth exactly `t`.
  unfold periodExpectedPayoff
  refine Finset.sum_congr rfl (fun suffix hsuffix => ?_)
  have hlen : suffix.length = t :=
    length_of_mem_HistoriesOfLength R.stage t suffix hsuffix
  -- Probability factor: strict-length agreement (`pre.length < suffix.length = t ≤ t`).
  have hprob : R.publicHistoryProbFrom σ h suffix = R.publicHistoryProbFrom τ h suffix := by
    refine R.publicHistoryProbFrom_congr suffix h (fun j pre hpre => ?_)
    exact hagree j pre (by omega)
  -- Stage-payoff factor: agreement at `suffix` itself (length `= t ≤ t`).
  have hstage : R.stagePayoff σ (h ++ suffix) i = R.stagePayoff τ (h ++ suffix) i := by
    refine R.stagePayoff_congr (h ++ suffix) (fun j => ?_) i
    exact hagree j suffix (by omega)
  rw [hprob, hstage]

/-- **Locality of continuation values.** Strategies that agree at every continuation of `h`
(including `h` itself) induce the same continuation value at `h`. Play at histories that do not
extend `h` is irrelevant. -/
lemma continuationValue_congr {σ τ : R.PublicStrategy} (h : R.stage.PublicHistory)
    (i : R.stage.Player)
    (hagree : ∀ (j : R.stage.Player) (suffix : R.stage.PublicHistory),
      σ j (h ++ suffix) = τ j (h ++ suffix)) :
    R.continuationValue σ h i = R.continuationValue τ h i := by
  -- `tsum_congr` over `periodExpectedPayoff_congr` at every `t`.
  unfold continuationValue
  congr 1
  refine tsum_congr (fun t => ?_)
  rw [R.periodExpectedPayoff_congr h t i (fun j suffix _ => hagree j suffix)]

/-! ### Continuity at infinity -/

/-- **Continuity at infinity.** Strategies that agree for the first `T` periods after `h` have
continuation values within `2 · payoffBound · δ^T`: The first `T` discounted period payoffs
coincide, and each tail is dominated by the geometric series
`(1 - δ) ∑_{t ≥ T} δ^t ·
payoffBound = δ^T · payoffBound`. -/
lemma abs_continuationValue_sub_le_of_eq_of_lt {σ τ : R.PublicStrategy}
    (h : R.stage.PublicHistory) (i : R.stage.Player) (T : ℕ)
    (hagree : ∀ (j : R.stage.Player) (suffix : R.stage.PublicHistory),
      suffix.length < T → σ j (h ++ suffix) = τ j (h ++ suffix)) :
    |R.continuationValue σ h i - R.continuationValue τ h i| ≤
      2 * R.payoffBound * R.discount ^ T := by
  -- Difference of the two `tsum`s: Terms `t < T` vanish by `periodExpectedPayoff_congr`
  -- (agreement up to depth `t ≤ T - 1 < T`), terms `t ≥ T` are bounded by
  -- `2 · payoffBound · δ^t` via `abs_periodExpectedPayoff_le_payoffBound`; sum the geometric
  -- tail.
  set δ := R.discount with hδ
  set B := R.payoffBound with hB
  have hδ_nonneg : 0 ≤ δ := R.discount_nonneg
  have hδ_lt_one : δ < 1 := R.discount_lt_one
  have h1mδ_nonneg : 0 ≤ 1 - δ := by linarith
  have h1mδ_pos : 0 < 1 - δ := by linarith
  -- The discounted period-payoff difference.
  set f : ℕ → ℝ := fun t => δ ^ t * (R.periodExpectedPayoff σ h t i -
    R.periodExpectedPayoff τ h t i) with hf
  -- Each strategy's discounted period series is summable.
  have hsumσ : Summable (fun t : ℕ => δ ^ t * R.periodExpectedPayoff σ h t i) :=
    R.summable_discount_periodExpectedPayoff σ h i
  have hsumτ : Summable (fun t : ℕ => δ ^ t * R.periodExpectedPayoff τ h t i) :=
    R.summable_discount_periodExpectedPayoff τ h i
  have hsumf : Summable f := by
    have := hsumσ.sub hsumτ
    refine this.congr (fun t => ?_)
    simp only [hf, mul_sub]
  -- The continuation-value difference is `(1 - δ) * ∑' f`.
  have hcv_diff : R.continuationValue σ h i - R.continuationValue τ h i =
      (1 - δ) * ∑' t : ℕ, f t := by
    unfold continuationValue
    rw [← hδ, ← mul_sub, ← hsumσ.tsum_sub hsumτ]
    congr 1
    refine tsum_congr (fun t => ?_)
    simp only [hf, mul_sub]
  -- Terms before `T` vanish: agreement up to depth `t ≤ T - 1 < T`.
  have hf_zero : ∀ t : ℕ, t < T → f t = 0 := by
    intro t ht
    have hpep : R.periodExpectedPayoff σ h t i = R.periodExpectedPayoff τ h t i :=
      R.periodExpectedPayoff_congr h t i
        (fun j suffix hlen => hagree j suffix (by omega))
    simp only [hf, hpep, sub_self, mul_zero]
  -- Each term is bounded by `δ^t * (2 * B)` (triangle + the uniform bound).
  have hf_abs_le : ∀ t : ℕ, |f t| ≤ δ ^ t * (2 * B) := by
    intro t
    rw [hf, abs_mul, abs_pow, abs_of_nonneg hδ_nonneg]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ_nonneg t)
    calc |R.periodExpectedPayoff σ h t i - R.periodExpectedPayoff τ h t i|
        ≤ |R.periodExpectedPayoff σ h t i| + |R.periodExpectedPayoff τ h t i| := abs_sub _ _
      _ ≤ B + B := add_le_add (R.abs_periodExpectedPayoff_le_payoffBound σ h t i)
          (R.abs_periodExpectedPayoff_le_payoffBound τ h t i)
      _ = 2 * B := by ring
  -- The geometric tail bound on the shifted series.
  have hgeom_shift : Summable (fun s : ℕ => δ ^ (T + s) * (2 * B)) := by
    have : Summable (fun s : ℕ => δ ^ s * (δ ^ T * (2 * B))) :=
      (summable_geometric_of_lt_one hδ_nonneg hδ_lt_one).mul_right _
    refine this.congr (fun s => ?_)
    rw [pow_add]; ring
  -- The shifted-tail tsum equals `δ^T * (1 - δ)⁻¹ * (2 * B)`.
  have htail_sum : (∑' s : ℕ, δ ^ (T + s) * (2 * B)) = δ ^ T * ((1 - δ)⁻¹ * (2 * B)) := by
    have hrw : (fun s : ℕ => δ ^ (T + s) * (2 * B)) =
        (fun s : ℕ => δ ^ T * (δ ^ s * (2 * B))) := by
      funext s; rw [pow_add]; ring
    rw [hrw, tsum_mul_left, tsum_mul_right,
      tsum_geometric_of_lt_one hδ_nonneg hδ_lt_one]
  -- Split `∑' f` at `T`; the head vanishes, so `∑' f = ∑' s, f (T + s)`.
  have hsplit : (∑' t : ℕ, f t) = ∑' s : ℕ, f (T + s) := by
    have hkey := (hsumf.sum_add_tsum_nat_add T)
    have hhead : (∑ t ∈ Finset.range T, f t) = 0 :=
      Finset.sum_eq_zero (fun t ht => hf_zero t (Finset.mem_range.mp ht))
    rw [hhead, zero_add] at hkey
    -- `hkey : ∑' (i : ℕ), f (i + T) = ∑' (i : ℕ), f i`; reorder `i + T` to `T + i`.
    rw [← hkey]
    refine tsum_congr (fun s => ?_)
    rw [Nat.add_comm]
  -- Bound `|∑' f| ≤ tail sum`.
  have hsumf_shift : Summable (fun s : ℕ => f (T + s)) := by
    have := (summable_nat_add_iff T).mpr hsumf
    refine this.congr (fun s => ?_)
    rw [Nat.add_comm]
  have habs_shift_summable : Summable (fun s : ℕ => |f (T + s)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun s => hf_abs_le (T + s)) hgeom_shift
  have htsum_abs_le : |∑' t : ℕ, f t| ≤ δ ^ T * ((1 - δ)⁻¹ * (2 * B)) := by
    rw [hsplit]
    calc |∑' s : ℕ, f (T + s)|
        ≤ ∑' s : ℕ, |f (T + s)| := by
          have := norm_tsum_le_tsum_norm
            (f := fun s : ℕ => f (T + s)) (by simpa [Real.norm_eq_abs] using habs_shift_summable)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' s : ℕ, δ ^ (T + s) * (2 * B) :=
          Summable.tsum_le_tsum (fun s => hf_abs_le (T + s)) habs_shift_summable hgeom_shift
      _ = δ ^ T * ((1 - δ)⁻¹ * (2 * B)) := htail_sum
  -- Multiply by the nonnegative normalization `(1 - δ)` and cancel the inverse.
  rw [hcv_diff, abs_mul, abs_of_nonneg h1mδ_nonneg]
  calc (1 - δ) * |∑' t : ℕ, f t|
      ≤ (1 - δ) * (δ ^ T * ((1 - δ)⁻¹ * (2 * B))) :=
        mul_le_mul_of_nonneg_left htsum_abs_le h1mδ_nonneg
    _ = 2 * B * δ ^ T := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (1 - δ) (δ ^ T), mul_assoc (δ ^ T) (1 - δ),
          mul_inv_cancel₀ (ne_of_gt h1mδ_pos), mul_one]
        ring

/-! ### The one-shot deviation principle -/

/-- **No profitable one-shot deviation.** At every public history `h`, every one-shot deviation (a
strategy differing from `σ` only in player `i`'s mixed action at `h`, which is exactly
`IsInfoSetDeviation` on the perfect-information lift) weakly lowers the deviator's continuation
value at `h`. -/
def NoProfitableOneShotDeviation (σ : R.PublicStrategy) : Prop :=
  ∀ (i : R.stage.Player) (h : R.stage.PublicHistory) (σ' : R.PublicStrategy),
    IsInfoSetDeviation R.toExtensiveForm i h σ σ' →
      R.continuationValue σ' h i ≤ R.continuationValue σ h i

variable {R}

/-- The easy direction of the one-shot deviation principle: One-shot deviations are unilateral
deviations, so subgame perfection rules them out. -/
theorem IsSubgamePerfectEquilibrium.noProfitableOneShotDeviation {σ : R.PublicStrategy}
    (hspe : R.IsSubgamePerfectEquilibrium σ) : R.NoProfitableOneShotDeviation σ := by
  -- `toExtensiveGame_infoSetDeviation_unilateral` converts the deviation, then apply `hspe` at
  -- the pair `(i, h)`.
  intro i h σ' hdev
  exact hspe (i, h) σ' (R.toExtensiveGame_infoSetDeviation_unilateral σ i h σ' hdev)

/-- **Finite-depth unimprovability.** If no one-shot deviation is profitable, then no unilateral
deviation by `i` that returns to `σ` after at most `T` periods beyond `h` is profitable at `h`. -/
theorem NoProfitableOneShotDeviation.continuationValue_le_of_eq_of_le {σ : R.PublicStrategy}
    (hOS : R.NoProfitableOneShotDeviation σ) {i : R.stage.Player} {σ' : R.PublicStrategy}
    (hdev : R.toExtensiveForm.unilateralDeviation i σ σ') (T : ℕ)
    (h : R.stage.PublicHistory)
    (hdepth : ∀ suffix : R.stage.PublicHistory, T ≤ suffix.length →
      σ' i (h ++ suffix) = σ i (h ++ suffix)) :
    R.continuationValue σ' h i ≤ R.continuationValue σ h i := by
  -- Induction on `T` generalizing `h`. Step: By `continuationValue_eq_step` and the inductive
  -- hypothesis at each `h ++ [c]` (weights `stageProfileProb` are nonnegative),
  -- `cv σ' h i ≤ (1-δ)·sp σ' h i + δ·∑ c, ssp σ' h c · cv σ (h++[c]) i`; the right side is the
  -- continuation value of the one-shot surgery `τ := σ except σ' i h at (i, h)` by
  -- `stagePayoff_congr`, `stageProfileProb_congr`, `continuationValue_congr`, and the one-step
  -- Bellman for `τ`; conclude by `hOS` at `(i, h)`.
  classical
  induction T generalizing h with
  | zero =>
    -- Depth-0 deviation: `σ'` already equals `σ` at every continuation of `h`, so locality applies.
    have hagree : ∀ (j : R.stage.Player) (suffix : R.stage.PublicHistory),
        σ' j (h ++ suffix) = σ j (h ++ suffix) := by
      intro j suffix
      rcases eq_or_ne j i with hji | hji
      · subst hji; exact hdepth suffix (Nat.zero_le _)
      · exact hdev j (h ++ suffix) hji
    exact le_of_eq (R.continuationValue_congr h i hagree)
  | succ T ih =>
    -- One-shot surgery at `(i, h)`: agree with `σ'` exactly at `(i, h)`, otherwise `σ`.
    set τ : R.PublicStrategy := fun j g =>
      if (⟨j, g⟩ : Σ k, R.toExtensiveForm.info.Obs k) = ⟨i, (h : R.toExtensiveForm.info.Obs i)⟩
        then σ' j g else σ j g with hτ
    -- `τ` is a one-shot info-set deviation of `σ` at `(i, h)`.
    have hτ_dev : IsInfoSetDeviation R.toExtensiveForm i h σ τ := by
      intro j g hjg
      simp only [hτ]
      rw [if_neg hjg]
    -- At `h`, `τ` coincides with `σ'` in every coordinate.
    have hτ_at_h : ∀ j : R.stage.Player, τ j h = σ' j h := by
      intro j
      rcases eq_or_ne j i with hji | hji
      · subst hji
        simp only [hτ, if_pos]
      · -- Off-deviator at `h`: `τ j h = σ j h = σ' j h` (`hdev`, reversed).
        have hne : (⟨j, (h : R.toExtensiveForm.info.Obs j)⟩ : Σ k, R.toExtensiveForm.info.Obs k)
            ≠ ⟨i, (h : R.toExtensiveForm.info.Obs i)⟩ := by
          intro heq
          exact hji (congrArg Sigma.fst heq)
        simp only [hτ]
        rw [if_neg hne]
        exact (hdev j h hji).symm
    -- At any strict extension `g = (h ++ [c]) ++ suffix` of `h`, `τ` coincides with `σ`.
    have hτ_at_ext : ∀ (c : R.stage.ActionProfile) (suffix : R.stage.PublicHistory)
        (j : R.stage.Player), τ j (h ++ [c] ++ suffix) = σ j (h ++ [c] ++ suffix) := by
      intro c suffix j
      have hlen : (h ++ [c] ++ suffix).length ≠ h.length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hne : (⟨j, ((h ++ [c] ++ suffix) : R.toExtensiveForm.info.Obs j)⟩ :
          Σ k, R.toExtensiveForm.info.Obs k) ≠ ⟨i, (h : R.toExtensiveForm.info.Obs i)⟩ := by
        intro heq
        rcases Sigma.mk.inj_iff.mp heq with ⟨_, hheq⟩
        exact hlen (congrArg List.length (eq_of_heq hheq))
      simp only [hτ]
      rw [if_neg hne]
    -- (i) Bellman at `h` for `σ'`.
    have hBellman_σ' : R.continuationValue σ' h i =
        (1 - R.discount) * R.stagePayoff σ' h i +
          R.discount * ∑ c : R.stage.ActionProfile,
            R.stageProfileProb σ' h c * R.continuationValue σ' (h ++ [c]) i :=
      R.continuationValue_eq_step σ' h i
    -- (ii) Inductive hypothesis at each `h ++ [c]`: deviation returns to `σ` after `T` periods.
    have hstep_le : ∀ c : R.stage.ActionProfile,
        R.continuationValue σ' (h ++ [c]) i ≤ R.continuationValue σ (h ++ [c]) i := by
      intro c
      refine ih (h ++ [c]) (fun suffix hsuffix => ?_)
      -- Re-root: `(h ++ [c]) ++ suffix = h ++ ([c] ++ suffix)` with length `≥ T + 1`.
      have hlen : T + 1 ≤ ([c] ++ suffix).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have := hdepth ([c] ++ suffix) hlen
      rwa [← List.append_assoc] at this
    -- (iii) Sum comparison, weighting by nonnegative `stageProfileProb σ' h c`.
    have hsum_le : ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ' h c * R.continuationValue σ' (h ++ [c]) i ≤
        ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ' h c * R.continuationValue σ (h ++ [c]) i :=
      Finset.sum_le_sum (fun c _ =>
        mul_le_mul_of_nonneg_left (hstep_le c) (R.stageProfileProb_nonneg σ' h c))
    -- (iv) `σ'` and `τ` agree at `h`, hence same stage payoff and profile distribution there.
    have hsp_eq : R.stagePayoff σ' h i = R.stagePayoff τ h i :=
      R.stagePayoff_congr h (fun j => (hτ_at_h j).symm) i
    have hssp_eq : ∀ c : R.stage.ActionProfile,
        R.stageProfileProb σ' h c = R.stageProfileProb τ h c :=
      fun c => R.stageProfileProb_congr h (fun j => (hτ_at_h j).symm) c
    -- (v) `σ` and `τ` agree at every continuation of `h ++ [c]`, hence same continuation value.
    have hcv_eq : ∀ c : R.stage.ActionProfile,
        R.continuationValue σ (h ++ [c]) i = R.continuationValue τ (h ++ [c]) i :=
      fun c => R.continuationValue_congr (h ++ [c]) i
        (fun j suffix => (hτ_at_ext c suffix j).symm)
    -- (vi) Bellman at `h` for `τ`, run backwards.
    have hBellman_τ : (1 - R.discount) * R.stagePayoff τ h i +
          R.discount * ∑ c : R.stage.ActionProfile,
            R.stageProfileProb τ h c * R.continuationValue τ (h ++ [c]) i =
        R.continuationValue τ h i :=
      (R.continuationValue_eq_step τ h i).symm
    -- (vii) `τ` is a one-shot deviation of `σ`, so by `hOS` it is unprofitable at `(i, h)`.
    have hτ_unprof : R.continuationValue τ h i ≤ R.continuationValue σ h i :=
      hOS i h τ hτ_dev
    -- The `σ`-weighted sum at `h` equals the `τ`-weighted sum (both rewrite term-by-term).
    have hsum_eq : ∑ c : R.stage.ActionProfile,
          R.stageProfileProb σ' h c * R.continuationValue σ (h ++ [c]) i =
        ∑ c : R.stage.ActionProfile,
          R.stageProfileProb τ h c * R.continuationValue τ (h ++ [c]) i :=
      Finset.sum_congr rfl (fun c _ => by rw [hssp_eq c, hcv_eq c])
    -- Assemble over opaque atoms: the discounted-sum step uses (iii), then (iv)-(vi) and (vii).
    have h1mδ : 0 ≤ 1 - R.discount := by linarith [R.discount_lt_one]
    have hstep : R.discount *
          ∑ c : R.stage.ActionProfile,
            R.stageProfileProb σ' h c * R.continuationValue σ' (h ++ [c]) i ≤
        R.discount *
          ∑ c : R.stage.ActionProfile,
            R.stageProfileProb σ' h c * R.continuationValue σ (h ++ [c]) i :=
      mul_le_mul_of_nonneg_left hsum_le R.discount_nonneg
    -- Chain: Bellman(σ') ≤ (peel) = Bellman(τ) = cv τ ≤ cv σ.
    rw [hBellman_σ']
    calc (1 - R.discount) * R.stagePayoff σ' h i +
            R.discount * ∑ c : R.stage.ActionProfile,
              R.stageProfileProb σ' h c * R.continuationValue σ' (h ++ [c]) i
        ≤ (1 - R.discount) * R.stagePayoff σ' h i +
            R.discount * ∑ c : R.stage.ActionProfile,
              R.stageProfileProb σ' h c * R.continuationValue σ (h ++ [c]) i := by linarith [hstep]
      _ = (1 - R.discount) * R.stagePayoff τ h i +
            R.discount * ∑ c : R.stage.ActionProfile,
              R.stageProfileProb τ h c * R.continuationValue τ (h ++ [c]) i := by
            rw [hsp_eq, hsum_eq]
      _ = R.continuationValue τ h i := hBellman_τ
      _ ≤ R.continuationValue σ h i := hτ_unprof

/-- The hard direction of the one-shot deviation principle: Unimprovability implies subgame
perfection. -/
theorem NoProfitableOneShotDeviation.isSubgamePerfectEquilibrium {σ : R.PublicStrategy}
    (hOS : R.NoProfitableOneShotDeviation σ) : R.IsSubgamePerfectEquilibrium σ := by
  -- For the truncation, replace `σ' i g` by `σ i g` at histories `g ⊇ h` with
  -- `g.length ≥ h.length + T` (classical decidability of the cutoff predicate is fine inside
  -- the proof). `δ^T → 0` since `0 ≤ δ < 1`.
  classical
  -- Unfold subgame perfection at the deviator pair `(i, h)`.
  rintro ⟨i, h⟩ σ' hdev
  rw [ge_iff_le]
  change R.continuationValue σ' h i ≤ R.continuationValue σ h i
  -- `hdev` reversed: `σ'` agrees with `σ` off the deviator.
  have hdev' : ∀ (j : R.stage.Player) (g : R.stage.PublicHistory), j ≠ i →
      σ' j g = σ j g := fun j g hji => hdev j g hji
  -- The depth-`T` truncation: follow `σ'` only on continuations of `h` shallower than `T`.
  set στ : ℕ → R.PublicStrategy := fun T j g =>
    if (j = i ∧ h <+: g ∧ g.length < h.length + T) then σ' j g else σ j g with hστ
  -- (a) Each truncation is a unilateral `i`-deviation of `σ`.
  have hστ_dev : ∀ T, R.toExtensiveForm.unilateralDeviation i σ (στ T) := by
    intro T j g hji
    simp only [hστ]
    rw [if_neg (fun hcond => hji hcond.1)]
  -- (b) Beyond depth `T`, the truncation has returned to `σ`.
  have hστ_deep : ∀ T (suffix : R.stage.PublicHistory), T ≤ suffix.length →
      στ T i (h ++ suffix) = σ i (h ++ suffix) := by
    intro T suffix hsuffix
    simp only [hστ]
    rw [if_neg]
    rintro ⟨_, _, hlen⟩
    simp only [List.length_append] at hlen
    omega
  -- (c) Within depth `T`, the truncation coincides with `σ'`.
  have hστ_shallow : ∀ T (j : R.stage.Player) (suffix : R.stage.PublicHistory),
      suffix.length < T → στ T j (h ++ suffix) = σ' j (h ++ suffix) := by
    intro T j suffix hsuffix
    rcases eq_or_ne j i with hji | hji
    · subst hji
      simp only [hστ]
      rw [if_pos]
      refine ⟨by trivial, List.prefix_append _ _, ?_⟩
      simp only [List.length_append]; omega
    · -- Off-deviator: truncation is `σ`, which equals `σ'` there by `hdev'`.
      simp only [hστ]
      rw [if_neg (fun hcond => hji hcond.1)]
      exact (hdev' j (h ++ suffix) hji).symm
  -- Finite-depth unimprovability: `cv (στ T) h i ≤ cv σ h i` for every `T`.
  have hfinite_le : ∀ T, R.continuationValue (στ T) h i ≤ R.continuationValue σ h i := by
    intro T
    exact hOS.continuationValue_le_of_eq_of_le (hστ_dev T) T h (hστ_deep T)
  -- Continuity at infinity: `|cv σ' h i − cv (στ T) h i| ≤ 2·B·δ^T`.
  have hcontinuity : ∀ T,
      |R.continuationValue σ' h i - R.continuationValue (στ T) h i| ≤
        2 * R.payoffBound * R.discount ^ T := by
    intro T
    refine R.abs_continuationValue_sub_le_of_eq_of_lt h i T (fun j suffix hsuffix => ?_)
    exact (hστ_shallow T j suffix hsuffix).symm
  -- For every `T`: `cv σ' h i ≤ cv σ h i + 2·B·δ^T`.
  have hbound : ∀ T, R.continuationValue σ' h i ≤
      R.continuationValue σ h i + 2 * R.payoffBound * R.discount ^ T := by
    intro T
    have h1 : R.continuationValue σ' h i - R.continuationValue (στ T) h i ≤
        2 * R.payoffBound * R.discount ^ T :=
      (abs_le.mp (hcontinuity T)).2
    have h2 := hfinite_le T
    linarith
  -- Let `T → ∞`: `2·B·δ^T → 0`, so the bound sequence tends to `cv σ h i`.
  have htend : Filter.Tendsto
      (fun T : ℕ => R.continuationValue σ h i + 2 * R.payoffBound * R.discount ^ T)
      Filter.atTop (nhds (R.continuationValue σ h i)) := by
    have hpow : Filter.Tendsto (fun T : ℕ => R.discount ^ T) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one R.discount_nonneg R.discount_lt_one
    have : Filter.Tendsto
        (fun T : ℕ => 2 * R.payoffBound * R.discount ^ T) Filter.atTop (nhds 0) := by
      have := hpow.const_mul (2 * R.payoffBound)
      simpa using this
    have := this.const_add (R.continuationValue σ h i)
    simpa using this
  -- `cv σ' h i ≤ cv σ h i` by comparing the constant sequence against the bound sequence.
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.Eventually.of_forall hbound)

variable (R)

/-- **One-shot deviation principle** for infinite-horizon discounted repeated games: A public
strategy is a subgame-perfect equilibrium iff no player has a profitable one-shot deviation at any
public history. -/
theorem IsSubgamePerfectEquilibrium_iff_noProfitableOneShotDeviation (σ : R.PublicStrategy) :
    R.IsSubgamePerfectEquilibrium σ ↔ R.NoProfitableOneShotDeviation σ :=
  ⟨IsSubgamePerfectEquilibrium.noProfitableOneShotDeviation,
    NoProfitableOneShotDeviation.isSubgamePerfectEquilibrium⟩

end RepeatedGame

end Econlib.GameTheory
