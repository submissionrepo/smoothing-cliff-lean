/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.SocialChoice
import Mathlib

/-!
# Strategy-Proofness Variants Non-Vacuity Witnesses

Compile-time semantic witnesses for `Econlib.SocialChoice.ChoiceFunction.Properties` and
`Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`. The three set-valued
strategy-proofness variants — optimistic (`StrategyProof`), pessimistic
(`StrategyProofPessimistic`), and Kelly (`StrategyProofKelly`) — are pairwise independent but the
optimistic+pessimistic pair jointly implies Kelly. These witnesses force the independence claim to
be *tabulated* on concrete data, catching the failure mode where a reversed variant inclusion
passes silently because separating rules are introduced but never evaluated.

## What each witness catches

* **`StrategyProofVariants` unfold** — `variants_pairwise_independent_unfold`: Re-derives the
  bundled six-component conjunction `strategyProof_variants_pairwise_independent`, but binds
  *concrete* local rules (`ruleA`, `ruleB`, `ruleC`, `ruleD`) into the existential witnesses rather
  than passing the library witnesses through untouched. Each conjunct is closed by the file's own
  `ruleX_strategyProof` / `ruleX_not_pessimistic` / … tabulation, so a re-ordering of the six
  conjuncts or a direction-flipped separation would fail to typecheck here.
* **Elected-set recomputation for Rule A** (`sepRule R {1,0} {1}`, `R : 2 ≻ 1 ≻ 0`):

  * `ruleA_winners_truthful` / `ruleA_winners_misreport`: The truthful report `R` elects `{1,0}`;
    the misreport `flatPref` elects `{1}`. A mis-keyed `if/else` in `sepRule` would swap them.
  * `ruleA_strategyProof` / `ruleA_not_pessimistic`: Rule A blocks the optimistic event
    (no `b ∈ {1}` strictly beats all of `{1,0}`, since `1 ⊁ 1`) but admits the pessimistic one
    (`a = 0 ∈ {1,0}` is strictly beaten by all of `{1}`, since `1 ≻ 0`). These confirm
    `strategyProof_sepRule_iff` and `strategyProofPessimistic_sepRule_iff` on real data.
  * `ruleA_pessimistic_event`: Explicitly exhibits the manipulation event for the pessimistic
    variant, using `flatPref_not_lt` to confirm it is not a `flatPref` artifact.
* **Elected-set recomputation for Rule B** (`sepRule R {0} {0,1}`):

  * `ruleB_winners_truthful` / `ruleB_winners_misreport`: Truthful wins `{0}`, misreport wins
    `{0,1}`.
  * `ruleB_pessimistic` / `ruleB_not_strategyProof`: Rule B blocks the pessimistic event
    (no `a ∈ {0}` is beaten by ALL of `{0,1}`, since `0 ⊁ 0`) but admits the optimistic one
    (`b = 1 ∈ {0,1}` strictly beats all of `{0}`, since `1 ≻ 0`). Exercises
    `strategyProof_sepRule_iff` and `strategyProofPessimistic_sepRule_iff` again in the opposite
    direction, catching a direction-flipped independence claim.
  * `ruleB_optimistic_event`: Exhibits the manipulation event for the optimistic variant.
* **Concrete Rules C and D** (`sepRule R {1} {2,0}`, `sepRule R {2,0} {1}`): Defined locally with
  their winner sets (`ruleC_winners_*`, `ruleD_winners_*`) and proved Kelly-SP (`ruleC_kelly`,
  `ruleD_kelly`) while failing opt-SP (`ruleC_not_strategyProof`) resp. pess-SP
  (`ruleD_not_pessimistic`). These bind into `ruleC_spec` / `ruleD_spec` and the
  `variants_pairwise_independent_unfold` re-derivation.
* **`strategyProof_iff_optimistic` bridge** — `ruleA_iff_optimistic_agrees`,
  `ruleA_to_optimistic`, `ruleA_from_optimistic`: On Rule A the two predicates are defeq via
  `Iff.rfl`; `ruleA_to_optimistic` proves the optimistic-named form *directly* from the optimistic
  manipulation-event calculation (not by importing `ruleA_strategyProof` through the bridge), so the
  round-trip is a genuine consistency check rather than a tautological re-export.
* **Kelly manipulation present for A and B** — `ruleA_not_kelly`, `ruleB_not_kelly`: The Kelly "NO"
  table entries for A and B are *proved*, not merely narrated. Both Kelly events fire: For A,
  `N = {1}` elementwise-dominates `O = {1,0}` (`1 ≽ 1`, `1 ≽ 0`) with the strict pair `1 ≻ 0`; for
  B, `N = {0,1}` elementwise-dominates `O = {0}` (`0 ≽ 0`, `1 ≽ 0`) with the strict pair `1 ≻ 0`.
  These force the weak-dominance conjunct of `KellyManip` to be exercised, not just the strict one.
* **`StrategyProof.strategyProofKelly_of_pessimistic` fired non-degenerately** —
  `jointRule_kellyFromJoint`: A *non-constant* rule (`sepRule R {2,1} {2,0}`, with distinct
  elected sets `O = {2,1} ≠ N = {2,0}`) satisfies optimistic *and* pessimistic SP, so the
  joint-implication theorem fires on a genuinely satisfied pessimistic premise over distinct winner
  sets — not on the degenerate `O = N` case where every event holds by irreflexivity alone.

## Data

* `R` — total preference `2 ≻ 1 ≻ 0` on `Fin 3`, realized as `preferenceOfUtilityIn id`.
* `flatPref` — the all-indifferent preference (all utilities 0, no strict comparisons).
* Five `sepRule` instances (`ruleA`–`ruleD`, `jointRule`), one for each separation pair, each on the
  single voter `Unit` with alternatives `Fin 3`.

Elected sets (hand-tabulated; used to document each witness):

| Rule  | Truthful `R` wins | Misreport `flatPref` wins | Opt-SP? | Pess-SP? | Kelly-SP? |
| ----- | ----------------- | ------------------------- | ------- | -------- | --------- |
| A     | `{1, 0}`          | `{1}`                     | YES     | NO       | NO        |
| B     | `{0}`             | `{0, 1}`                  | NO      | YES      | NO        |
| C     | `{1}`             | `{2, 0}`                  | NO      | YES      | YES       |
| D     | `{2, 0}`          | `{1}`                     | YES     | NO       | YES       |
| Joint | `{2, 1}`          | `{2, 0}`                  | YES     | YES      | YES       |

Opt/pess ⇒ Kelly (by `StrategyProof.strategyProofKelly_of_pessimistic`); `jointRule` witnesses this
on *distinct* nonempty winner sets `O = {2,1} ≠ N = {2,0}` (so the implication is exercised on a
genuine pessimistic premise, not the degenerate `O = N` where every event holds by irreflexivity).
Rules A and B witness opt ⬝ pess and vice-versa. Rules C and D witness kelly ⬝ opt and kelly ⬝ pess.

**`jointRule` event tabulation** (`O = {2,1}`, `N = {2,0}`, `R : 2 ≻ 1 ≻ 0`):

* Optimistic (`∃ b ∈ N, ∀ a ∈ O, b ≻ a`): `b = 2`: `2 ≻ 2`? NO. `b = 0`: `0 ≻ 2`? NO. → opt-SP.
* Pessimistic (`∃ a ∈ O, ∀ b ∈ N, b ≻ a`): `a = 2`: `2 ≻ 2`? NO. `a = 1`: need `2 ≻ 1` (YES) and
  `0 ≻ 1` (NO). → pess-SP.
* Kelly: weak-dom needs `0 ≽ 1` (i.e. `1 ≤ 0`), which is FALSE, so `KellyManip` fails directly too.
-/

noncomputable section

namespace EconlibTest.SocialChoice.ChoiceFunction

open Econlib.Preferences Econlib.SocialChoice Econlib.SocialChoice.ChoiceFunction

/-! ### Shared preference data -/

/-- `R` = total preference `2 ≻ 1 ≻ 0` on `Fin 3`. The underlying utility is the identity
(`i ↦ (i : ℕ)`) so the induced `PreferenceRel.lt` is the natural number order on indices. -/
private abbrev R : PreferenceRel (Fin 3) :=
  preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ))

/-- `R.lt 1 0` — 1 is strictly preferred to 0 under `R`. -/
private theorem R_lt_10 : R.lt 1 0 := by simp [R, preferenceOfUtilityIn_lt_iff]

/-- `R.lt 2 1` — 2 is strictly preferred to 1 under `R`. -/
private theorem R_lt_21 : R.lt 2 1 := by simp [R, preferenceOfUtilityIn_lt_iff]

/-- `R.lt 2 0` — 2 is strictly preferred to 0 under `R` (transitivity). -/
private theorem R_lt_20 : R.lt 2 0 := by simp [R, preferenceOfUtilityIn_lt_iff]

/-- `R.le 1 1` — reflexive weak preference (`1 ≽ 1`). Used in the Kelly weak-dominance conjunct. -/
private theorem R_le_11 : R.le 1 1 := by simp [R, preferenceOfUtilityIn_le_iff]

/-- `R.le 1 0` — `1 ≽ 0` (since `1 ≻ 0`). Weak-dominance ingredient for Rule A / Rule B Kelly. -/
private theorem R_le_10 : R.le 1 0 := by simp [R, preferenceOfUtilityIn_le_iff]

/-- `R.le 0 0` — reflexive weak preference (`0 ≽ 0`). Used in the Rule B Kelly weak dominance. -/
private theorem R_le_00 : R.le 0 0 := by simp [R, preferenceOfUtilityIn_le_iff]

/-- `R ≠ flatPref`: `R` has the strict comparison `1 ≻ 0`; `flatPref` has none. -/
private theorem R_ne_flatPref : R ≠ flatPref :=
  fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ R_lt_10)

/-! ### Section 2: Rule A — optimistic-SP, NOT pessimistic-SP, NOT Kelly-SP

**Elected sets (hand-tabulated):**

* Truthful report `R` wins: `O = {1, 0}` (two winners, `1` better)
* Misreport `flatPref` wins: `N = {1}` (singleton)

**Optimistic event check** (`∃ b ∈ {1}, ∀ a ∈ {1,0}, R.lt b a`):

* Candidate `b = 1`: Need `1 ≻ 1`? NO (strict irreflexivity). So `¬OptimisticManip` → SP holds.

**Pessimistic event check** (`∃ a ∈ {1,0}, ∀ b ∈ {1}, R.lt b a`):

* Candidate `a = 0`: Need `1 ≻ 0`? YES (`R_lt_10`). So `PessimisticManip` → NOT pess-SP.

**Kelly event check** (`∀ b ∈ {1}, ∀ a ∈ {1,0}, R.le b a`) ∧ (∃ strict):

* `b = 1`: `1 ≽ 1`? YES; `1 ≽ 0`? YES (since `1 ≻ 0`). So weak-dom holds.
* Strict witness: `b = 1, a = 0`, `1 ≻ 0`. So `KellyManip` → NOT Kelly-SP. -/

private abbrev ruleA : ChoiceFunction Unit (Fin 3) :=
  sepRule R ({1, 0} : Set (Fin 3)) ({1} : Set (Fin 3)) ⟨1, by simp⟩ (Set.singleton_nonempty 1)

/-- **`sepRule_winners_const` + `update_unit_const`**: Rule A elects `{1,0}` for the truthful
report `R`. This exercises `sepRule_winners_const` on a concrete preference; a swapped `if/else`
would return `{1}` instead. -/
theorem ruleA_winners_truthful :
    ruleA.winners (Function.const Unit R) = {1, 0} := by
  rw [sepRule_winners_const]
  exact if_pos rfl

/-- Rule A elects `{1}` for the misreport `flatPref`. -/
theorem ruleA_winners_misreport :
    ruleA.winners (Function.const Unit flatPref) = {1} := by
  rw [sepRule_winners_const]
  exact if_neg (Ne.symm R_ne_flatPref)

/-- **`strategyProof_sepRule_iff`**: Rule A is optimistically strategy-proof. The key step is that
the optimistic event fails: `b = 1 ∈ {1}` cannot satisfy `1 ≻ 1` (strict irreflexivity). -/
theorem ruleA_strategyProof : ruleA.StrategyProof := by
  rw [strategyProof_sepRule_iff R_ne_flatPref]
  -- Goal: ¬ OptimisticManip R {1,0} {1}, i.e., no b ∈ {1} beats every a ∈ {1,0}
  rintro ⟨b, hbN, hb⟩
  -- The only candidate is b = 1
  rw [Set.mem_singleton_iff] at hbN
  subst hbN
  -- But 1 ≻ 1 is irreflexive
  exact (R.lt_irrefl 1) (hb 1 (by simp))

/-- **`strategyProofPessimistic_sepRule_iff`**: Rule A is NOT pessimistically strategy-proof. The
pessimistic event holds: `a = 0 ∈ {1,0}` is beaten by every `b ∈ {1}` since `1 ≻ 0`. -/
theorem ruleA_not_pessimistic : ¬ ruleA.StrategyProofPessimistic := by
  rw [strategyProofPessimistic_sepRule_iff R_ne_flatPref, not_not]
  -- Exhibit the pessimistic event: a = 0, beaten by all b ∈ {1}
  exact ⟨0, by simp, fun b hb => by
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact R_lt_10⟩

/-- **Pessimistic event explicit witness.** Spelled out for documentation: The truthful winner
`a = 0` is strictly beaten by the sole misreport winner `b = 1`. `flatPref_not_lt` rules out any
confusion with the all-indifferent preference: `flatPref` cannot produce this strict ordering. -/
theorem ruleA_pessimistic_event : PessimisticManip R ({1, 0} : Set (Fin 3)) ({1} : Set (Fin 3)) :=
  ⟨0, by simp, fun b hb => by
    rw [Set.mem_singleton_iff] at hb; subst hb; exact R_lt_10⟩

/-- `flatPref` cannot replicate the pessimistic event: `1 ⊁ 0` under `flatPref`. -/
theorem flatPref_not_lt_1_0 : ¬ flatPref.lt 1 0 :=
  flatPref_not_lt 1 0

/-- **`strategyProofKelly_sepRule_iff`**: Rule A is NOT Kelly strategy-proof. The Kelly event holds:
`N = {1}` elementwise weakly dominates `O = {1,0}` — `b = 1` satisfies `1 ≽ 1` (`R_le_11`) and
`1 ≽ 0` (`R_le_10`) — with the strict comparison `1 ≻ 0` (`R_lt_10`). This proves the Kelly "NO"
table entry for Rule A, exercising the weak-dominance conjunct, not just the strict witness. -/
theorem ruleA_not_kelly : ¬ ruleA.StrategyProofKelly := by
  rw [strategyProofKelly_sepRule_iff R_ne_flatPref, not_not]
  refine ⟨fun b hb a ha => ?_, 1, by simp, 0, by simp, R_lt_10⟩
  -- weak dominance: the sole misreport winner b = 1 weakly beats every a ∈ {1, 0}
  rw [Set.mem_singleton_iff] at hb; subst hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact R_le_11
  · exact R_le_10

/-! ### Section 3: Rule B — pessimistic-SP, NOT optimistic-SP, NOT Kelly-SP

**Elected sets (hand-tabulated):**

* Truthful report `R` wins: `O = {0}` (singleton)
* Misreport `flatPref` wins: `N = {0, 1}`

**Optimistic event check** (`∃ b ∈ {0,1}, ∀ a ∈ {0}, R.lt b a`):

* Candidate `b = 1`: Need `1 ≻ 0`? YES (`R_lt_10`). So `OptimisticManip` → NOT opt-SP.

**Pessimistic event check** (`∃ a ∈ {0}, ∀ b ∈ {0,1}, R.lt b a`):

* Candidate `a = 0`: Need `0 ≻ 0`? NO (irreflexivity). So `¬PessimisticManip` → pess-SP holds.

**Kelly event check**: `{0,1}` weakly dominates `{0}` with strict?

* `b = 0, a = 0`: `0 ≽ 0`? YES. `b = 1, a = 0`: `1 ≽ 0`? YES (since `1 ≻ 0`). Strict: `1 ≻ 0`.
* So `KellyManip` → NOT Kelly-SP. -/

private abbrev ruleB : ChoiceFunction Unit (Fin 3) :=
  sepRule R ({0} : Set (Fin 3)) ({0, 1} : Set (Fin 3)) (Set.singleton_nonempty 0) ⟨0, by simp⟩

/-- Rule B elects `{0}` for the truthful report `R`. -/
theorem ruleB_winners_truthful :
    ruleB.winners (Function.const Unit R) = {0} := by
  rw [sepRule_winners_const]; exact if_pos rfl

/-- Rule B elects `{0, 1}` for the misreport `flatPref`. -/
theorem ruleB_winners_misreport :
    ruleB.winners (Function.const Unit flatPref) = {0, 1} := by
  rw [sepRule_winners_const]; exact if_neg (Ne.symm R_ne_flatPref)

/-- **`strategyProofPessimistic_sepRule_iff`**: Rule B is pessimistically strategy-proof. The
pessimistic event fails: `a = 0 ∈ {0}` cannot satisfy `0 ≻ 0` (strict irreflexivity). -/
theorem ruleB_pessimistic : ruleB.StrategyProofPessimistic := by
  rw [strategyProofPessimistic_sepRule_iff R_ne_flatPref]
  rintro ⟨a, haO, ha⟩
  rw [Set.mem_singleton_iff] at haO
  subst haO
  exact (R.lt_irrefl 0) (ha 0 (by simp))

/-- **`strategyProof_sepRule_iff`**: Rule B is NOT optimistically strategy-proof. The optimistic
event holds: `b = 1 ∈ {0,1}` strictly beats the sole truthful winner `0`. Exercising the opposite
direction from `ruleA_strategyProof` — this pair (A, B) witnesses that opt ⬝ pess. -/
theorem ruleB_not_strategyProof : ¬ ruleB.StrategyProof := by
  rw [strategyProof_sepRule_iff R_ne_flatPref, not_not]
  exact ⟨1, by simp, fun a ha => by
    rw [Set.mem_singleton_iff] at ha; subst ha; exact R_lt_10⟩

/-- **Optimistic event explicit witness.** `b = 1 ∈ {0,1}` strictly beats `a = 0 ∈ {0}` under `R`,
confirming the optimistic manipulation event. Paired with `ruleA_pessimistic_event` to show both
directions of the opt/pess separation have genuine data behind them. -/
theorem ruleB_optimistic_event : OptimisticManip R ({0} : Set (Fin 3)) ({0, 1} : Set (Fin 3)) :=
  ⟨1, by simp, fun a ha => by
    rw [Set.mem_singleton_iff] at ha; subst ha; exact R_lt_10⟩

/-- **`strategyProofKelly_sepRule_iff`**: Rule B is NOT Kelly strategy-proof. The Kelly event holds:
`N = {0,1}` elementwise weakly dominates `O = {0}` — every `b ∈ {0,1}` satisfies `b ≽ 0` (`0 ≽ 0`
via `R_le_00`, `1 ≽ 0` via `R_le_10`) — with the strict comparison `1 ≻ 0` (`R_lt_10`). This proves
the Kelly "NO" table entry for Rule B, exercising the weak-dominance conjunct over a two-element
`N`. -/
theorem ruleB_not_kelly : ¬ ruleB.StrategyProofKelly := by
  rw [strategyProofKelly_sepRule_iff R_ne_flatPref, not_not]
  refine ⟨fun b hb a ha => ?_, 1, by simp, 0, by simp, R_lt_10⟩
  -- weak dominance: every misreport winner b ∈ {0, 1} weakly beats the sole truthful winner a = 0
  rw [Set.mem_singleton_iff] at ha; subst ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · exact R_le_00
  · exact R_le_10

/-! ### Section 4: `strategyProof_iff_optimistic` bridge -/

/-- **`strategyProof_iff_optimistic`**: `StrategyProof` and `StrategyProofOptimistic` are
definitionally equal. On Rule A, converting between them is a no-op — confirming the bridge is
genuine identity, not a one-way implication. -/
theorem ruleA_iff_optimistic_agrees :
    ruleA.StrategyProof ↔ ruleA.StrategyProofOptimistic :=
  strategyProof_iff_optimistic ruleA

/-- The optimistic-named predicate `StrategyProofOptimistic` proved **directly** from the optimistic
manipulation-event calculation for Rule A — *not* by importing `ruleA_strategyProof` through the
bridge. We rewrite through `strategyProof_iff_optimistic` (so the goal becomes the optimistic
event's absence) and discharge it on the concrete data: `b = 1 ∈ {1}` cannot satisfy `1 ≻ 1`. This
makes the round-trip below a genuine consistency check rather than a tautological re-export. -/
theorem ruleA_to_optimistic : ruleA.StrategyProofOptimistic := by
  rw [← strategyProof_iff_optimistic, strategyProof_sepRule_iff R_ne_flatPref]
  rintro ⟨b, hbN, hb⟩
  rw [Set.mem_singleton_iff] at hbN; subst hbN
  exact (R.lt_irrefl 1) (hb 1 (by simp))

/-- The converse direction of the bridge: `StrategyProofOptimistic → StrategyProof` on Rule A,
recovering the original predicate from the independently-proved optimistic one. Together with
`ruleA_to_optimistic` this exercises both directions of `strategyProof_iff_optimistic`. -/
theorem ruleA_from_optimistic : ruleA.StrategyProof :=
  (strategyProof_iff_optimistic ruleA).mpr ruleA_to_optimistic

/-! ### Section 5: `StrategyProof.strategyProofKelly_of_pessimistic` fired non-degenerately

**The joint rule:** `sepRule R {2,1} {2,0}`. `domain = {const R, const flatPref}`; truthful report
`R` elects `O = {2, 1}`, the `flatPref` misreport elects `N = {2, 0}`. Crucially `O ≠ N` (they share
only `2`), so the joint implication is exercised on *distinct* nonempty winner sets, not the
degenerate `O = N` case where every manipulation event holds vacuously by strict irreflexivity.

**Elected sets (hand-tabulated):**

* Truthful `R` → `O = {2, 1}`; misreport `flatPref` → `N = {2, 0}`.

**Event checks under `R : 2 ≻ 1 ≻ 0`:**

* Optimistic (`∃ b ∈ {2,0}, ∀ a ∈ {2,1}, R.lt b a`): `b = 2`: `2 ≻ 2`? NO. `b = 0`: `0 ≻ 2`? NO.
  → opt-SP holds.
* Pessimistic (`∃ a ∈ {2,1}, ∀ b ∈ {2,0}, R.lt b a`): `a = 2`: `2 ≻ 2`? NO. `a = 1`: needs both
  `2 ≻ 1` (YES) and `0 ≻ 1` (NO). → pess-SP holds.
* Kelly: weak dominance needs `0 ≽ 1` (i.e. `1 ≤ 0`), which is FALSE — so `KellyManip` fails
  directly, confirming kelly-SP independently of the joint implication.

Because opt-SP and pess-SP both hold on these distinct sets,
`strategyProofKelly_of_pessimistic` fires non-degenerately. -/

private abbrev jointRule : ChoiceFunction Unit (Fin 3) :=
  sepRule R ({2, 1} : Set (Fin 3)) ({2, 0} : Set (Fin 3)) ⟨2, by simp⟩ ⟨2, by simp⟩

/-- The joint rule elects `O = {2, 1}` for the truthful report `R` — distinct from its misreport
winners `{2, 0}`, so the joint-implication witness is not the degenerate `O = N` case. -/
theorem jointRule_winners_truthful :
    jointRule.winners (Function.const Unit R) = {2, 1} := by
  rw [sepRule_winners_const]; exact if_pos rfl

/-- The joint rule elects `N = {2, 0}` for the misreport `flatPref`. -/
theorem jointRule_winners_misreport :
    jointRule.winners (Function.const Unit flatPref) = {2, 0} := by
  rw [sepRule_winners_const]; exact if_neg (Ne.symm R_ne_flatPref)

/-- The truthful and misreport winner sets genuinely differ: `{2, 1} ≠ {2, 0}` (they disagree on
`1`). This is what makes `jointRule_kellyFromJoint` a non-degenerate witness for the joint
implication. -/
theorem jointRule_winner_sets_distinct :
    jointRule.winners (Function.const Unit R) ≠
      jointRule.winners (Function.const Unit flatPref) := by
  rw [jointRule_winners_truthful, jointRule_winners_misreport]
  intro h
  -- `1 ∈ {2,1}` but `1 ∉ {2,0}`
  have h1 : (1 : Fin 3) ∈ ({2, 1} : Set (Fin 3)) := by simp
  rw [h] at h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h1 | h1 <;> exact absurd h1 (by decide)

/-- **The joint rule is optimistically strategy-proof.** No `b ∈ {2,0}` strictly beats every
`a ∈ {2,1}`: `b = 2` fails `2 ≻ 2`, and `b = 0` fails `0 ≻ 2`. -/
theorem jointRule_strategyProof : jointRule.StrategyProof := by
  rw [strategyProof_sepRule_iff R_ne_flatPref]
  rintro ⟨b, hbN, hb⟩
  -- `b` must dominate `a = 2 ∈ {2,1}`; both candidates fail.
  have hb2 : R.lt b 2 := hb 2 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbN
  rcases hbN with rfl | rfl
  · exact (R.lt_irrefl 2) hb2
  · rw [show ((0 : Fin 3)) = (0 : Fin 3) from rfl] at hb2
    -- `0 ≻ 2` is false: `2 ≤ 0` fails
    simp [R, preferenceOfUtilityIn_lt_iff] at hb2

/-- **The joint rule is pessimistically strategy-proof.** No `a ∈ {2,1}` is strictly beaten by every
`b ∈ {2,0}`: `a = 2` fails `2 ≻ 2`, and `a = 1` fails since `0 ≻ 1` is false. -/
theorem jointRule_pessimisticSP : jointRule.StrategyProofPessimistic := by
  rw [strategyProofPessimistic_sepRule_iff R_ne_flatPref]
  rintro ⟨a, haO, ha⟩
  -- every `b ∈ {2,0}` must beat `a`; in particular `b = 0` must, i.e. `0 ≻ a`.
  have ha0 : R.lt 0 a := ha 0 (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at haO
  rcases haO with rfl | rfl
  · -- `0 ≻ 2`? false
    simp [R, preferenceOfUtilityIn_lt_iff] at ha0
  · -- `0 ≻ 1`? false
    simp [R, preferenceOfUtilityIn_lt_iff] at ha0

/-- **`StrategyProof.strategyProofKelly_of_pessimistic` fired non-degenerately.** Both
`jointRule_strategyProof` and `jointRule_pessimisticSP` are genuinely proved on concrete data over
the *distinct* winner sets `O = {2,1} ≠ N = {2,0}` (`jointRule_winner_sets_distinct`), so the joint
implication fires on a real pessimistic premise rather than the degenerate `O = N` case where every
event holds by irreflexivity alone. -/
theorem jointRule_kellyFromJoint : jointRule.StrategyProofKelly :=
  jointRule_strategyProof.strategyProofKelly_of_pessimistic jointRule_pessimisticSP

/-- **`strategyProofKelly_sepRule_iff` direct verification.** The Kelly event also fails directly on
the distinct sets: weak dominance would require `0 ≽ 1` (i.e. `1 ≤ 0`), which is false, so the
weak-dominance conjunct of `KellyManip` cannot be discharged. This confirms
`jointRule_kellyFromJoint` via a second, independent route. -/
theorem jointRule_kellyDirect : jointRule.StrategyProofKelly := by
  rw [strategyProofKelly_sepRule_iff R_ne_flatPref]
  rintro ⟨hdom, -⟩
  -- weak dominance forces `0 ≽ 1` for `b = 0 ∈ {2,0}`, `a = 1 ∈ {2,1}`
  have h01 : R.le 0 1 := hdom 0 (by simp) 1 (by simp)
  rw [show R = preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) from rfl,
    preferenceOfUtilityIn_le_iff] at h01
  simp at h01

/-! ### Section 6: Rules C and D — Kelly-SP separates from opt and pess

Concrete `sepRule` instances, defined *in this file* so the winner sets and manipulation events are
tabulated locally rather than delegated to the library existential.

**Rule C** (`O = {1}`, `N = {2,0}`, `R : 2 ≻ 1 ≻ 0`): Kelly-SP but NOT opt-SP.

* Kelly (`(∀ b ∈ {2,0}, ∀ a ∈ {1}, b ≽ a) ∧ ∃ strict`): weak dominance needs `0 ≽ 1` (`1 ≤ 0`),
  which is FALSE → `¬KellyManip` → kelly-SP.
* Optimistic (`∃ b ∈ {2,0}, ∀ a ∈ {1}, b ≻ a`): `b = 2`: `2 ≻ 1`? YES → `OptimisticManip` →
  NOT opt-SP.

**Rule D** (`O = {2,0}`, `N = {1}`): Kelly-SP but NOT pess-SP.

* Kelly (`(∀ b ∈ {1}, ∀ a ∈ {2,0}, b ≽ a) ∧ ∃ strict`): weak dominance needs `1 ≽ 2` (`2 ≤ 1`),
  which is FALSE → `¬KellyManip` → kelly-SP.
* Pessimistic (`∃ a ∈ {2,0}, ∀ b ∈ {1}, b ≻ a`): `a = 0`: `1 ≻ 0`? YES → `PessimisticManip` →
  NOT pess-SP. -/

private abbrev ruleC : ChoiceFunction Unit (Fin 3) :=
  sepRule R ({1} : Set (Fin 3)) ({2, 0} : Set (Fin 3)) (Set.singleton_nonempty 1) ⟨2, by simp⟩

private abbrev ruleD : ChoiceFunction Unit (Fin 3) :=
  sepRule R ({2, 0} : Set (Fin 3)) ({1} : Set (Fin 3)) ⟨2, by simp⟩ (Set.singleton_nonempty 1)

/-- Rule C elects `{1}` for the truthful report `R`. -/
theorem ruleC_winners_truthful :
    ruleC.winners (Function.const Unit R) = {1} := by
  rw [sepRule_winners_const]; exact if_pos rfl

/-- Rule C elects `{2, 0}` for the misreport `flatPref`. -/
theorem ruleC_winners_misreport :
    ruleC.winners (Function.const Unit flatPref) = {2, 0} := by
  rw [sepRule_winners_const]; exact if_neg (Ne.symm R_ne_flatPref)

/-- **Rule C is Kelly strategy-proof.** Weak dominance of `{2,0}` over `{1}` fails: `0 ≽ 1` would
require `1 ≤ 0`, which is false. -/
theorem ruleC_kelly : ruleC.StrategyProofKelly := by
  rw [strategyProofKelly_sepRule_iff R_ne_flatPref]
  rintro ⟨hdom, -⟩
  have h01 : R.le 0 1 := hdom 0 (by simp) 1 (by simp)
  rw [show R = preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) from rfl,
    preferenceOfUtilityIn_le_iff] at h01
  simp at h01

/-- **Rule C is NOT optimistically strategy-proof.** The optimistic event holds: `b = 2 ∈ {2,0}`
strictly beats the sole truthful winner `1` (`2 ≻ 1`). -/
theorem ruleC_not_strategyProof : ¬ ruleC.StrategyProof := by
  rw [strategyProof_sepRule_iff R_ne_flatPref, not_not]
  exact ⟨2, by simp, fun a ha => by
    rw [Set.mem_singleton_iff] at ha; subst ha; exact R_lt_21⟩

/-- **`exists_kelly_not_strategyProof`, witnessed by the file's own Rule C.** Binds the concrete
locally-defined `ruleC` (with its tabulated winner sets and events) into the library existential,
so this conjunct of the pairwise-independence theorem is checked against real data, not a library
witness passed through untouched. -/
theorem ruleC_spec :
    ∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofKelly ∧ ¬ f.StrategyProof :=
  ⟨ruleC, ruleC_kelly, ruleC_not_strategyProof⟩

/-- Rule D elects `{2, 0}` for the truthful report `R`. -/
theorem ruleD_winners_truthful :
    ruleD.winners (Function.const Unit R) = {2, 0} := by
  rw [sepRule_winners_const]; exact if_pos rfl

/-- Rule D elects `{1}` for the misreport `flatPref`. -/
theorem ruleD_winners_misreport :
    ruleD.winners (Function.const Unit flatPref) = {1} := by
  rw [sepRule_winners_const]; exact if_neg (Ne.symm R_ne_flatPref)

/-- **Rule D is Kelly strategy-proof.** Weak dominance of `{1}` over `{2,0}` fails: `1 ≽ 2` would
require `2 ≤ 1`, which is false. -/
theorem ruleD_kelly : ruleD.StrategyProofKelly := by
  rw [strategyProofKelly_sepRule_iff R_ne_flatPref]
  rintro ⟨hdom, -⟩
  have h12 : R.le 1 2 := hdom 1 (by simp) 2 (by simp)
  rw [show R = preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) from rfl,
    preferenceOfUtilityIn_le_iff] at h12
  simp at h12

/-- **Rule D is NOT pessimistically strategy-proof.** The pessimistic event holds: `a = 0 ∈ {2,0}`
is strictly beaten by the sole misreport winner `1` (`1 ≻ 0`). -/
theorem ruleD_not_pessimistic : ¬ ruleD.StrategyProofPessimistic := by
  rw [strategyProofPessimistic_sepRule_iff R_ne_flatPref, not_not]
  exact ⟨0, by simp, fun b hb => by
    rw [Set.mem_singleton_iff] at hb; subst hb; exact R_lt_10⟩

/-- **`exists_kelly_not_pessimistic`, witnessed by the file's own Rule D.** Binds the concrete
locally-defined `ruleD` into the library existential, tabulating the winner sets and events here. -/
theorem ruleD_spec :
    ∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofKelly ∧ ¬ f.StrategyProofPessimistic :=
  ⟨ruleD, ruleD_kelly, ruleD_not_pessimistic⟩

/-- **`update_unit_const` exercised independently.** On a `Unit`-voter profile any unilateral
deviation replaces the whole profile by a constant. We prove the concrete instance *directly* by
extensionality and the `Unit` case split (`Function.update_self`), rather than invoking
`update_unit_const`, so this is a genuine check of the `Function.update`-on-`Unit` semantics that
underlies every `sepRule_iff` proof. -/
theorem update_unit_const_witness :
    Function.update (Function.const Unit R) () flatPref = Function.const Unit flatPref := by
  funext u
  obtain ⟨⟩ := u
  rw [Function.update_self]
  rfl

/-! ### Section 7: Bundled pairwise-independence theorem, re-derived from concrete local rules -/

/-- **`strategyProof_variants_pairwise_independent`, re-derived from this file's concrete rules.**
Rather than passing the library's existential witnesses through untouched, each of the six conjuncts
is closed by an explicit local `sepRule` together with its tabulated SP/non-SP proofs:

| Conjunct (X holds, Y fails) | Rule    | SP proof / non-SP proof                       |
| --------------------------- | ------- | --------------------------------------------- |
| opt ∧ ¬pess                  | `ruleA` | `ruleA_strategyProof` / `ruleA_not_pessimistic` |
| opt ∧ ¬Kelly                 | `ruleA` | `ruleA_strategyProof` / `ruleA_not_kelly`       |
| pess ∧ ¬opt                  | `ruleB` | `ruleB_pessimistic` / `ruleB_not_strategyProof` |
| pess ∧ ¬Kelly                | `ruleB` | `ruleB_pessimistic` / `ruleB_not_kelly`         |
| Kelly ∧ ¬opt                 | `ruleC` | `ruleC_kelly` / `ruleC_not_strategyProof`       |
| Kelly ∧ ¬pess                | `ruleD` | `ruleD_kelly` / `ruleD_not_pessimistic`         |

A re-ordering of the six conjuncts, or a direction-flipped separation, fails to typecheck here
because each slot demands a specific rule's specific SP property. This is strictly stronger than
re-destructuring the library bundle. -/
theorem variants_pairwise_independent_unfold :
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProof ∧ ¬ f.StrategyProofPessimistic) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProof ∧ ¬ f.StrategyProofKelly) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofPessimistic ∧ ¬ f.StrategyProof) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofPessimistic ∧ ¬ f.StrategyProofKelly) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofKelly ∧ ¬ f.StrategyProof) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), f.StrategyProofKelly ∧ ¬ f.StrategyProofPessimistic) :=
  ⟨⟨ruleA, ruleA_strategyProof, ruleA_not_pessimistic⟩,
    ⟨ruleA, ruleA_strategyProof, ruleA_not_kelly⟩,
    ⟨ruleB, ruleB_pessimistic, ruleB_not_strategyProof⟩,
    ⟨ruleB, ruleB_pessimistic, ruleB_not_kelly⟩,
    ⟨ruleC, ruleC_kelly, ruleC_not_strategyProof⟩,
    ⟨ruleD, ruleD_kelly, ruleD_not_pessimistic⟩⟩

end EconlibTest.SocialChoice.ChoiceFunction

end
