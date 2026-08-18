/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.SocialChoice
import Mathlib

/-!
# Preference-Profile Non-Vacuity Checks

Compile-time semantic witnesses for the `Econlib.SocialChoice.Profile` layer (`Basic`, `Domain`,
`Transform`). The profile substrate underlies every social-choice impossibility proof, and the
correctness of the `moveToTop` / `moveToBottom` / `swapPref` transforms and the `ParetoOptimal`
predicate is subtle enough to warrant concrete witnesses against specific utility data.

## What each witness catches

* **Domains + strictness** — `isStrict_of_injective_utilities`, `mem_strictDomain`,
  `strictDomain_subset_universalDomain`, `mem_universalDomain`: Verifies the Condorcet profile
  lands in both domains and is strict. The `universalDomain` checks are tautological `Set.univ`
  membership; `tiedProfile_universal_not_strict` adds the discriminating case — a *non*-strict
  profile that lies in `universalDomain` but **not** `strictDomain`.
* **ParetoOptimal positive case** — `c_paretoOptimal_in_Q`: In a unanimously-ranked profile `Q`
  (all voters: C ≻ b ≻ a), the top alternative `c = 2` is Pareto optimal. A vacuous definition or
  wrong quantifier direction breaks this.
* **ParetoOptimal negative case** — `a_not_paretoOptimal_in_Q`: `a = 0` is NOT Pareto optimal in
  `Q` because `b = 1` Pareto dominates it — every voter weakly prefers `b`, voter 0 strictly
  prefers `b`. A quantifier reversal (`∃` vs `¬ ∃`) breaks this.
* **ParetoOptimal with a dissenting voter** — `b_paretoDominates_a_in_D` (Section 2b): the *every
  voter weakly prefers* conjunct is exercised on a **non-unanimous** profile `D` where voter 1 is
  *indifferent* between `a` and `b` (`D_voter1_indifferent`). The companion
  `b_not_paretoDominates_a_in_D'` shows dominance *fails* once a voter opposes — proving the
  every-voter-weakly conjunct is load-bearing and "some voter strictly prefers" is insufficient.
* **`Profile.update_self` / `update_of_ne`** — pointwise update reads back the installed ballot and
  leaves other ballots unchanged.
* **`Profile.IsStrict.restrict` + `StrictPref.comap` + `comap_le_iff` / `comap_lt_iff`** —
  restricting the Condorcet profile to a two-element sub-type is strict and preserves pairwise
  comparisons. `restrict_voter0_a_le_b` / `restrict_voter0_a_lt_b` discharge the iffs on real data
  (voter 0 has `a ≻ b`, and *not* `b ≻ a`). Note `strictPref_preferenceOfUtilityIn` is the single
  direction injective ⇒ strict (not an iff); `not_strictPref_of_noninjective` checks the converse
  is genuinely needed via a tied utility.
* **`moveToTop`** — `atTop_moveToTop`, `moveToTop_le_of_ne` (relative order of non-top pair
  preserved), `StrictPref.moveToTop`, `moveToTop_le_iff`; the surviving `b`-vs-`c` order is checked
  *strictly* (`b_lt_c_in_R1_atop`).
* **`moveToBottom`** — `atBottom_moveToBottom`, `moveToBottom_le_of_ne`, `StrictPref.moveToBottom`,
  `moveToBottom_le_iff`; surviving order checked strictly (`b_lt_c_in_R0_abot`).
* **`swapPref`** — `swapPref_lt_iff_swap` flips exactly the swapped pair (direction check);
  `swapPref_le_left_a` / `swapPref_le_right_a` / `swapPref_le_left_c` / `swapPref_le_right_c`
  (b-vs-a/c positional facts), with the resulting `b`-vs-`a` and `c`-vs-`b` orders checked
  *strictly* (`b_lt_a_in_R0_swap`, `c_lt_b_in_R0_swap`); `StrictPref.swapPref`, `swapPref_le_iff`,
  `swapPref_lt_iff`.

## Data

Two profiles over `Fin 3` voters and `Fin 3` alternatives (`a = 0`, `b = 1`, `c = 2`):

**`P` — the Condorcet cycle:**

* voter 0: A ≻ b ≻ c  (utilities `[2, 1, 0]`)
* voter 1: B ≻ c ≻ a  (utilities `[0, 2, 1]`)
* voter 2: C ≻ a ≻ b  (utilities `[1, 0, 2]`)

**`Q` — unanimous c ≻ b ≻ a:**

* all 3 voters: C ≻ b ≻ a  (utilities `[0, 1, 2]`)

Under `Q`, `a = 0` is dominated by `b = 1` (Pareto dominated negative witness), while `c = 2` is
Pareto optimal.
-/

noncomputable section

namespace EconlibTest.SocialChoice.Profile

open Econlib.Preferences Econlib.SocialChoice

/-! ### Profile data -/

/-- Utility matrix for the Condorcet cycle. Row `i` is voter `i`'s utility vector. -/
private abbrev utilP : Fin 3 → Fin 3 → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: a ≻ b ≻ c
     ![0, 2, 1],   -- voter 1: b ≻ c ≻ a
     ![1, 0, 2] ]  -- voter 2: c ≻ a ≻ b

/-- The Condorcet cycle profile. -/
private abbrev P : Econlib.SocialChoice.Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilP i)

/-- Utility vector for the unanimous profile. All voters: C ≻ b ≻ a. -/
private abbrev utilQ : Fin 3 → ℕ := ![0, 1, 2]

/-- The unanimous c ≻ b ≻ a profile. -/
private abbrev Q : Econlib.SocialChoice.Profile (Fin 3) (Fin 3) :=
  fun _i => preferenceOfUtilityIn utilQ

-- Abbreviations for alternatives, to make witnesses self-documenting.
private abbrev a : Fin 3 := 0
private abbrev b : Fin 3 := 1
private abbrev c : Fin 3 := 2

/-! ### Section 1: Strictness and domains -/

/-- **Strictness of `P` via `isStrict_of_injective_utilities`.** Each `utilP i` is injective
(values `{0,1,2}` are all distinct by `decide`), so the Condorcet profile is strict. This exercises
`isStrict_of_injective_utilities` on concrete data and confirms the injectivity premise is
verified, not assumed. -/
theorem P_isStrict : Econlib.SocialChoice.Profile.IsStrict P :=
  isStrict_of_injective_utilities (fun i => by fin_cases i <;> decide)

/-- **`mem_strictDomain`** — the strict profile lands in `strictDomain`. -/
theorem P_mem_strictDomain : P ∈ strictDomain (Fin 3) (Fin 3) :=
  mem_strictDomain.mpr P_isStrict

/-- **`strictDomain_subset_universalDomain`** — `strictDomain` is a subset of `universalDomain`. -/
theorem P_mem_universalDomain_via_strict : P ∈ universalDomain (Fin 3) (Fin 3) :=
  strictDomain_subset_universalDomain P_mem_strictDomain

/-- **`mem_universalDomain`** — every profile is in `universalDomain` (trivially). -/
theorem P_mem_universalDomain : P ∈ universalDomain (Fin 3) (Fin 3) :=
  mem_universalDomain P

/-- **Discriminating domain witness: `universalDomain` ⊋ `strictDomain`.** The two `universalDomain`
membership checks above are tautological (`Set.univ`); they cannot detect a wrong domain definition.
This witness adds the distinguishing case — the *non-strict* tied profile `tiedProfile` (every voter
has `a ~ b`, utilities `[0, 0, 1]`) lies in `universalDomain` but **not** `strictDomain`, so the two
domains genuinely differ and `strictDomain ⊊ universalDomain` is proper. -/
theorem tiedProfile_universal_not_strict :
    (fun _ : Fin 3 => preferenceOfUtilityIn (![0, 0, 1] : Fin 3 → ℕ)) ∈
        universalDomain (Fin 3) (Fin 3) ∧
      (fun _ : Fin 3 => preferenceOfUtilityIn (![0, 0, 1] : Fin 3 → ℕ)) ∉
        strictDomain (Fin 3) (Fin 3) := by
  refine ⟨mem_universalDomain _, ?_⟩
  rw [mem_strictDomain]
  intro hstrict
  -- voter 0's ballot has `a ~ b` (both utility 0) yet `a ≠ b`, so it is not strict.
  have hindiff : (preferenceOfUtilityIn (![0, 0, 1] : Fin 3 → ℕ)).indiff 0 1 := by
    simp only [preferenceOfUtilityIn_indiff_iff]; decide
  exact absurd (hstrict 0 0 1 hindiff) (by decide)

/-! ### Section 2: Pareto optimality -/

/-- **`ParetoOptimal` positive witness.** `c = 2` is Pareto optimal in `Q` over the full set of
alternatives. Under `Q` all voters rank `c` at the top (utilities `[0,1,2]` — highest for `c`), so
no alternative Pareto dominates `c`: Any dominator would need every voter to weakly prefer it
(which fails for `c` as the top alt). This fires `ParetoOptimal`'s `¬ ∃ y, ...` clause on a profile
that actually has a Pareto optimum. -/
theorem c_paretoOptimal_in_Q : ParetoOptimal Q Set.univ c := by
  refine ⟨Set.mem_univ _, ?_⟩
  rintro ⟨y, -, hdom⟩
  -- `hdom : ParetoDominates Q y c`, i.e., every voter weakly prefers `y` and someone strictly.
  obtain ⟨hle, j, hlt⟩ := hdom
  -- Voter `j` strictly prefers `y` to `c`, so `utilQ c < utilQ y`.
  simp only [Q, preferenceOfUtilityIn_lt_iff] at hlt
  -- `utilQ c = utilQ 2 = 2` is the maximum; no `y` has `utilQ y > 2`.
  -- Reduce `c` to the literal `2` so `norm_num`/`decide` can evaluate matrix access.
  change (utilQ c < utilQ y) at hlt
  simp only [utilQ, show c = (2 : Fin 3) from rfl] at hlt
  fin_cases y <;> simp_all [utilQ]

/-- **`ParetoOptimal` negative witness.** `a = 0` is NOT Pareto optimal in `Q`: `b = 1` Pareto
dominates it. Every voter weakly prefers `b` to `a` (since `utilQ b = 1 > 0 =
utilQ a`) and voter 0
strictly prefers `b`. If the quantifier in `ParetoOptimal` were reversed (or `ParetoDominates`
required all-strict), this witness would fail. -/
theorem a_not_paretoOptimal_in_Q : ¬ ParetoOptimal Q Set.univ a := by
  intro ⟨_, hndom⟩
  apply hndom
  -- Witness: `b = 1` Pareto dominates `a = 0`.
  refine ⟨b, Set.mem_univ _, ?_, 0, ?_⟩
  · -- Every voter weakly prefers `b` to `a`.
    intro i
    simp only [Q, preferenceOfUtilityIn_le_iff, utilQ]
    fin_cases i <;> decide
  · -- Voter 0 strictly prefers `b` to `a`.
    simp only [Q, preferenceOfUtilityIn_lt_iff, utilQ]
    decide

/-! ### Section 2b: Pareto dominance with a dissenting (indifferent / opposed) voter

The Pareto witnesses above use the *unanimous* profile `Q`, so they would still pass for a broken
`ParetoDominates` defined merely as "*some* voter strictly prefers" — the "every voter weakly
prefers" conjunct is never stressed. We add a **non-unanimous** profile `D` where one voter is
indifferent and another opposes-then-agrees, so the `∀ i, b ≽ a` conjunct is genuinely load-bearing.

**`D` — `b = 1` dominates `a = 0` with a dissenting (indifferent) voter:**

* voter 0: `c ≻ b ≻ a`  (utilities `[0, 1, 2]`) — strictly prefers `b` to `a`
* voter 1: `a ~ b ≻ c`   (utilities `[1, 1, 0]`) — *indifferent* between `a` and `b`
* voter 2: `b ≻ c ≻ a`  (utilities `[0, 2, 1]`) — strictly prefers `b` to `a`

Every voter weakly prefers `b` to `a` (voter 1 only *weakly*, via indifference), and voters 0, 2
strictly, so `b` Pareto-dominates `a`. The indifferent voter 1 is exactly what an "all-strict"
mis-definition would reject. -/

/-- Utility matrix for the dissenting profile `D`. -/
private abbrev utilD : Fin 3 → Fin 3 → ℕ :=
  ![ ![0, 1, 2],   -- voter 0: c ≻ b ≻ a (b ≻ a strictly)
     ![1, 1, 0],   -- voter 1: a ~ b ≻ c (a ~ b: indifferent on the tested pair)
     ![0, 2, 1] ]  -- voter 2: b ≻ c ≻ a (b ≻ a strictly)

private abbrev D : Econlib.SocialChoice.Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilD i)

/-- **Voter 1 is genuinely indifferent** between `a` and `b` under `D` (`a ~ b`): the "every voter
weakly prefers" conjunct must accept indifference, not demand strictness. -/
theorem D_voter1_indifferent : (D 1).indiff a b := by
  simp only [D, utilD, preferenceOfUtilityIn_indiff_iff]
  decide

/-- **Pareto dominance with a dissenting voter.** `b = 1` Pareto-dominates `a = 0` under the
non-unanimous `D`: every voter weakly prefers `b` (voter 1 only via indifference `a ~ b`), and voter
0 strictly prefers `b`. This exercises the `∀ i, b ≽ a` conjunct against a voter who does *not*
strictly prefer `b` — a witness an "all-strict" mis-definition of `ParetoDominates` would fail. -/
theorem b_paretoDominates_a_in_D : ParetoDominates D b a := by
  refine ⟨?_, 0, ?_⟩
  · -- every voter weakly prefers `b` to `a`
    intro i
    simp only [D, preferenceOfUtilityIn_le_iff, utilD]
    fin_cases i <;> decide
  · -- voter 0 strictly prefers `b` to `a`
    simp only [D, preferenceOfUtilityIn_lt_iff, utilD]
    decide

/-- Consequently `a = 0` is **not** Pareto optimal under `D`, witnessed by the dominator `b`. -/
theorem a_not_paretoOptimal_in_D : ¬ ParetoOptimal D Set.univ a := by
  intro ⟨_, hndom⟩
  exact hndom ⟨b, Set.mem_univ _, b_paretoDominates_a_in_D⟩

/-! **`D'` — the "every voter weakly" conjunct is load-bearing.** If voter 1 *opposes* (`a ≻ b`)
instead of being indifferent, `b` no longer Pareto-dominates `a` — even though voter 0 still
*strictly* prefers `b`. So the "some voter strictly prefers" condition alone is **insufficient**:
the negative witness `b_not_paretoDominates_a_in_D'` proves the every-voter-weakly conjunct cannot
be dropped.

* voter 0: `c ≻ b ≻ a`  (utilities `[0, 1, 2]`) — strictly prefers `b` (so "some strict" holds)
* voter 1: `a ≻ b ≻ c`  (utilities `[2, 1, 0]`) — *opposes*: strictly prefers `a` to `b`
* voter 2: `b ≻ c ≻ a`  (utilities `[0, 2, 1]`) -/

private abbrev utilD' : Fin 3 → Fin 3 → ℕ :=
  ![ ![0, 1, 2],   -- voter 0: b ≻ a strictly
     ![2, 1, 0],   -- voter 1: a ≻ b (opposes b on the tested pair)
     ![0, 2, 1] ]  -- voter 2: b ≻ a strictly

private abbrev D' : Econlib.SocialChoice.Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilD' i)

/-- **Some voter strictly prefers `b` to `a` in `D'`** (voter 0) — so a "some-voter-strictly"
mis-definition of `ParetoDominates` would *wrongly* declare dominance here. -/
theorem D'_voter0_strict : (D' 0).lt b a := by
  simp only [D', utilD', preferenceOfUtilityIn_lt_iff]
  decide

/-- **`b` does NOT Pareto-dominate `a` in `D'`.** Voter 1 strictly prefers `a` to `b`, so the
`∀ i, b ≽ a` conjunct fails even though voter 0 strictly prefers `b`. This is the load-bearing check
that "every voter weakly prefers" is required — a definition using only "∃ strict" would
incorrectly conclude dominance. -/
theorem b_not_paretoDominates_a_in_D' : ¬ ParetoDominates D' b a := by
  rintro ⟨hle, -⟩
  -- voter 1 has `a ≻ b`, so `b ≽ a` fails for voter 1.
  have h1 : (D' 1).le b a := hle 1
  simp only [D', preferenceOfUtilityIn_le_iff, utilD'] at h1
  exact absurd h1 (by decide)

/-! ### Section 3: Profile.update_self / update_of_ne -/

/-- **`Profile.update_self`** — installing a new ballot and reading it back returns the new ballot.
The Condorcet profile updated at voter 1 with Q's ballot yields Q's ballot when queried at 1. -/
theorem update_self_witness :
    (P.update 1 (preferenceOfUtilityIn utilQ)) 1 = preferenceOfUtilityIn utilQ :=
  Econlib.SocialChoice.Profile.update_self P 1 _

/-- **`Profile.update_of_ne`** — the update does not touch other voters. -/
theorem update_of_ne_witness :
    (P.update 1 (preferenceOfUtilityIn utilQ)) 0 = P 0 :=
  Econlib.SocialChoice.Profile.update_of_ne P (by decide) _

/-! ### Section 4: Restriction, comap, strictness -/

-- Embed `Fin 2` into `Fin 3` by the inclusion `i ↦ i.castSucc` (0 ↦ 0, 1 ↦ 1).
-- This restricts P to the `{a, b}` sub-election.
private abbrev emb : Fin 2 → Fin 3 := Fin.castSucc

private theorem emb_injective : Function.Injective emb :=
  Fin.castSucc_injective _

/-- **`Profile.IsStrict.restrict`** — the Condorcet profile restricted to `{a, b}` is strict.
`P_isStrict` is the input; `emb_injective` ensures no two sub-alternatives collide. -/
theorem P_restrict_isStrict : (Econlib.SocialChoice.Profile.restrict emb P).IsStrict :=
  P_isStrict.restrict emb_injective

/-- **`PreferenceRel.comap_le_iff`** — the restricted ballot of voter 0 over `{a,b}` preserves the
`a ≻ b` ordering. Voter 0 has `utilP 0 = [2,1,0]`, so `a ≽ b` iff `utilP 0 b ≤ utilP 0 a` = `1 ≤ 2`
= true. -/
theorem comap_le_voter0_a_b :
    (Econlib.SocialChoice.Profile.restrict emb P 0).le 0 1 ↔ (P 0).le (emb 0) (emb 1) :=
  PreferenceRel.comap_le_iff emb (P 0) 0 1

/-- **Concrete evaluation of the restricted `le`.** Discharging the iff above on real data: voter 0
*does* weakly prefer `a` to `b` in the restricted ballot (`utilP 0 b = 1 ≤ 2 = utilP 0 a`). Without
this, a row change making `b ≻ a` would leave the iff witness typechecking while the docstring's
numeric anchor silently became false. -/
theorem restrict_voter0_a_le_b : (Econlib.SocialChoice.Profile.restrict emb P 0).le 0 1 := by
  rw [comap_le_voter0_a_b]
  change (P 0).le 0 1
  simp only [P, utilP, preferenceOfUtilityIn_le_iff]
  decide

/-- **`PreferenceRel.comap_lt_iff`** — voter 0 strictly prefers `a` to `b` in the restricted
ballot: `(P 0).lt (emb 0) (emb 1)` = `utilP 0 b < utilP 0 a` = `1 < 2` = true. -/
theorem comap_lt_voter0_a_b :
    (Econlib.SocialChoice.Profile.restrict emb P 0).lt 0 1 ↔ (P 0).lt (emb 0) (emb 1) :=
  PreferenceRel.comap_lt_iff emb (P 0) 0 1

/-- **Concrete evaluation of the restricted strict `lt`.** Voter 0 *strictly* prefers `a` to `b` in
the restricted ballot (`utilP 0 b = 1 < 2 = utilP 0 a`), and crucially does *not* have `b ≻ a`. This
pins the docstring's `a ≻ b` anchor to the actual utility data. -/
theorem restrict_voter0_a_lt_b :
    (Econlib.SocialChoice.Profile.restrict emb P 0).lt 0 1 ∧
      ¬ (Econlib.SocialChoice.Profile.restrict emb P 0).lt 1 0 := by
  constructor
  · rw [comap_lt_voter0_a_b]
    change (P 0).lt 0 1
    simp only [P, utilP, preferenceOfUtilityIn_lt_iff]; decide
  · -- `(restrict emb P 0).lt 1 0` is defeq to `(P 0).lt (emb 1) (emb 0)` via `comap_lt_iff`.
    change ¬ (P 0).lt (emb 1) (emb 0)
    simp only [emb, P, utilP, preferenceOfUtilityIn_lt_iff]; decide

/-- **`StrictPref.comap`** — voter 0's ballot restricted to `{a, b}` is strict (direct form). -/
theorem voter0_ballot_comap_strict :
    Econlib.SocialChoice.StrictPref ((P 0).comap emb) :=
  (P_isStrict 0).comap emb_injective

/-- **`strictPref_preferenceOfUtilityIn`** — if the utility is injective, the induced preference is
strict (the library lemma is this *one* direction only, not an iff). Verified concretely for voter
0's injective utility `[2,1,0]`. -/
theorem strictPref_voter0 :
    Econlib.SocialChoice.StrictPref (preferenceOfUtilityIn (utilP 0)) :=
  strictPref_preferenceOfUtilityIn (by decide)

/-- **Converse direction check via a non-injective utility.** The implication
`injective → strict` is genuinely one-directional in the sense that *strictness requires*
injectivity on the realized indifferences: the non-injective utility `[1, 1, 0]` (alternatives `0`
and `1` tie) induces a *non*-strict preference, since `0 ~ 1` is a non-reflexive indifference. This
confirms the hypothesis of `strictPref_preferenceOfUtilityIn` is load-bearing — dropping injectivity
breaks strictness. -/
theorem not_strictPref_of_noninjective :
    ¬ Econlib.SocialChoice.StrictPref (preferenceOfUtilityIn (![1, 1, 0] : Fin 3 → ℕ)) := by
  intro hstrict
  -- `0 ~ 1` under the tied utility, yet `0 ≠ 1`, contradicting strictness.
  have hindiff : (preferenceOfUtilityIn (![1, 1, 0] : Fin 3 → ℕ)).indiff 0 1 := by
    simp only [preferenceOfUtilityIn_indiff_iff]; decide
  exact absurd (hstrict 0 1 hindiff) (by decide)

/-! ### Section 5: MoveToTop -/

-- Apply `moveToTop` to voter 1's ballot (originally b ≻ c ≻ a) moving `a = 0` to the top.
-- After: a is at top, and b ≻ c relative order is preserved.
private abbrev R1_atop : PreferenceRel (Fin 3) := moveToTop (P 1) a

/-- **`atTop_moveToTop`** — after `moveToTop (P 1) a`, `a = 0` is strictly above every other
alternative. Direction: `∀ x ≠ a, a ≻ x`. A sign flip in the `moveToTop` definition would put `a`
at the bottom, breaking this. -/
theorem a_atTop_after_moveToTop : AtTop R1_atop a :=
  atTop_moveToTop (P 1) a

/-- **`moveToTop_le_iff`** — `R1_atop.le x y ↔ x = a ∨ (y ≠ a ∧ (P 1).le x y)`. -/
theorem moveToTop_le_iff_witness (x y : Fin 3) :
    R1_atop.le x y ↔ x = a ∨ (y ≠ a ∧ (P 1).le x y) :=
  moveToTop_le_iff (P 1) a x y

/-- **`moveToTop_le_of_ne` (relative order preserved).** `b = 1` and `c = 2` are unaffected by the
move-to-top: Voter 1 originally has `b ≻ c` (`utilP 1 = [0,2,1]`, `u(c)=1 < u(b)=2`), and this
ordering survives after `moveToTop`. -/
theorem moveToTop_preserves_b_c :
    R1_atop.le b c ↔ (P 1).le b c :=
  moveToTop_le_of_ne (by decide) (by decide)

/-- **The strict ordering is correct after the move.** Voter 1 has `b ≻ c` (`u(b)=2 > u(c)=1`), and
this *strict* ranking persists after moving `a` to the top (neither `b` nor `c` is `a`). We prove
the full `R1_atop.lt b c`, not just the weak `le`, so accidental indifference at `{b, c}` would be
caught. -/
theorem b_lt_c_in_R1_atop : R1_atop.lt b c := by
  refine ⟨?_, ?_⟩
  · -- `b ≽ c` survives the lift
    rw [moveToTop_le_of_ne (by decide) (by decide)]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide
  · -- `c ⊁ b`: `c ≽ b` is false (voter 1 strictly prefers `b`)
    rw [moveToTop_le_of_ne (by decide) (by decide)]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide

/-- **`StrictPref.moveToTop`** — the lifted preference is still strict. -/
theorem R1_atop_isStrict : Econlib.SocialChoice.StrictPref R1_atop :=
  (P_isStrict 1).moveToTop a

/-! ### Section 6: MoveToBottom -/

-- Apply `moveToBottom` to voter 0's ballot (originally a ≻ b ≻ c) moving `a = 0` to the bottom.
-- After: a is at bottom, b ≻ c relative order preserved.
private abbrev R0_abot : PreferenceRel (Fin 3) := moveToBottom (P 0) a

/-- **`atBottom_moveToBottom`** — after `moveToBottom (P 0) a`, `a = 0` is strictly below every
other alternative. -/
theorem a_atBottom_after_moveToBottom : AtBottom R0_abot a :=
  atBottom_moveToBottom (P 0) a

/-- **`moveToBottom_le_iff`** — the characterization of `R0_abot.le`. -/
theorem moveToBottom_le_iff_witness (x y : Fin 3) :
    R0_abot.le x y ↔ y = a ∨ (x ≠ a ∧ (P 0).le x y) :=
  moveToBottom_le_iff (P 0) a x y

/-- **`moveToBottom_le_of_ne` (relative order preserved).** `b = 1` and `c = 2` keep their voter-0
order under `moveToBottom`. Voter 0 has `b ≻ c` (`u(b)=1 > u(c)=0`). -/
theorem moveToBottom_preserves_b_c :
    R0_abot.le b c ↔ (P 0).le b c :=
  moveToBottom_le_of_ne (by decide) (by decide)

/-- **The strict ordering is correct after the move.** Voter 0 has `b ≻ c` (`u(b)=1 > u(c)=0`), and
this *strict* ranking persists under the bottom-move of `a` (neither `b` nor `c` is `a`). We prove
the full `R0_abot.lt b c`. -/
theorem b_lt_c_in_R0_abot : R0_abot.lt b c := by
  refine ⟨?_, ?_⟩
  · rw [moveToBottom_le_of_ne (by decide) (by decide)]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide
  · rw [moveToBottom_le_of_ne (by decide) (by decide)]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide

/-- **`StrictPref.moveToBottom`** — the lifted preference is still strict. -/
theorem R0_abot_isStrict : Econlib.SocialChoice.StrictPref R0_abot :=
  (P_isStrict 0).moveToBottom a

/-! ### Section 7: SwapPref -/

-- Apply `swapPref` to voter 0's ballot swapping `a = 0` and `c = 2`.
-- Original voter 0: a(u=2) ≻ b(u=1) ≻ c(u=0).
-- After swapPref(., a, c): labels a and c exchange → c(u=2) ≻ b(u=1) ≻ a(u=0).
private abbrev R0_swap : PreferenceRel (Fin 3) := swapPref (P 0) a c

/-- **`swapPref_lt_iff_swap` — the swapped pair flips direction.**
`(swapPref (P 0) a c).lt a c ↔ (P 0).lt c a`. Voter 0 has a ≻ b ≻ c (u(a)=2, u(c)=0), so
`(P 0).lt c a` means "c ≻ a in original" = `u(a) < u(c)` = `2 < 0` = FALSE. After the swap, a
occupies c's original bottom slot, so a ⊁ c in `R0_swap`. A direction reversal in `swapPref` would
erroneously make this true. -/
theorem swapPref_lt_iff_swap_witness :
    R0_swap.lt a c ↔ (P 0).lt c a :=
  swapPref_lt_iff_swap (P 0) a c

/-- **Positive direction: `c ≻ a` in `R0_swap`.** After swapping a and c, `c` occupies a's original
top slot (u=2), so c ≻ a. Concretely: `R0_swap.lt c a ↔ (P 0).lt a c ↔ u(c) < u(a) = 0 < 2` =
TRUE. -/
theorem c_lt_a_in_R0_swap : R0_swap.lt c a := by
  rw [swapPref_lt_iff (P 0) a c]
  simp only [Equiv.swap_apply_right, Equiv.swap_apply_left]
  -- Goal: (P 0).lt a c, i.e. u(c) < u(a) = 0 < 2.
  simp only [P, utilP, preferenceOfUtilityIn_lt_iff]
  decide

/-- **Negative check: `a ⊁ c` in `R0_swap`.** Since `swapPref_lt_iff_swap` gives
`R0_swap.lt a c ↔ (P 0).lt c a = FALSE` (voter 0 had a ≻ c, so c ⊁ a in the original), after the
swap `a` does NOT strictly dominate `c`. -/
theorem a_not_lt_c_in_R0_swap : ¬ R0_swap.lt a c := by
  rw [swapPref_lt_iff_swap_witness]
  -- (P 0).lt c a = u(a) < u(c) = 2 < 0 = false.
  simp only [P, utilP, preferenceOfUtilityIn_lt_iff]
  decide

/-- **`swapPref_le_iff`** — characterization via `Equiv.swap`. -/
theorem swapPref_le_iff_witness (x y : Fin 3) :
    R0_swap.le x y ↔ (P 0).le (Equiv.swap a c x) (Equiv.swap a c y) :=
  swapPref_le_iff (P 0) a c x y

/-- **`swapPref_lt_iff`** — strict-part characterization via `Equiv.swap`. -/
theorem swapPref_lt_iff_witness (x y : Fin 3) :
    R0_swap.lt x y ↔ (P 0).lt (Equiv.swap a c x) (Equiv.swap a c y) :=
  swapPref_lt_iff (P 0) a c x y

/-- **`swapPref_le_left_a`** — `(swapPref R a c).le a b ↔ R.le c b` for `b ∉ {a, c}`. Here:
`R0_swap.le a b ↔ (P 0).le c b`. Voter 0 has `b ≻ c` (`u(b)=1 > u(c)=0`), so `(P 0).le c b` = false
(c is NOT weakly preferred over b). So `R0_swap.le a b` = false: In the swapped preference, `a`'s
position (formerly c's) is below `b`. -/
theorem swapPref_le_left_a_witness :
    R0_swap.le a b ↔ (P 0).le c b :=
  swapPref_le_left_a (by decide) (by decide)

/-- Concretely: `R0_swap.le a b` is false (a is below b in the swapped preference). -/
theorem a_not_le_b_in_R0_swap : ¬ R0_swap.le a b := by
  rw [swapPref_le_left_a_witness]
  simp only [P, utilP, preferenceOfUtilityIn_le_iff]
  decide

/-- **`swapPref_le_right_a`** — `(swapPref R a c).le b a ↔ R.le b c` for `b ∉ {a, c}`. Here:
`R0_swap.le b a ↔ (P 0).le b c`. Voter 0 has `b ≻ c` (`u(c)=0 ≤ u(b)=1`), so `(P 0).le b c` = true.
So `b ≻ a` in the swapped preference (b above a's new slot). -/
theorem swapPref_le_right_a_witness :
    R0_swap.le b a ↔ (P 0).le b c :=
  swapPref_le_right_a (by decide) (by decide)

/-- Concretely: `b ≻ a` in `R0_swap` (b is *strictly* above a's new position). We prove the strict
`R0_swap.lt b a`: `b ≽ a` holds (`swapPref_le_right_a` reduces it to `(P 0).le b c`, true since
`b ≻ c`) and `a ⊁ b` (`a_not_le_b_in_R0_swap`). The prose's `b ≻ a` is now genuinely strict. -/
theorem b_lt_a_in_R0_swap : R0_swap.lt b a := by
  refine ⟨?_, a_not_le_b_in_R0_swap⟩
  rw [swapPref_le_right_a_witness]
  simp only [P, utilP, preferenceOfUtilityIn_le_iff]
  decide

/-- **`swapPref_le_left_c`** — `(swapPref R a c).le c b ↔ R.le a b` for `b ∉ {a, c}`.
`R0_swap.le c b ↔ (P 0).le a b`. Voter 0: `a ≻ b` (`u(b)=1 ≤ u(a)=2`), so `(P 0).le a b` = true. So
`c ≻ b` in the swapped preference (c occupies a's old top slot). -/
theorem swapPref_le_left_c_witness :
    R0_swap.le c b ↔ (P 0).le a b :=
  swapPref_le_left_c (by decide) (by decide)

/-- Concretely: `c ≻ b` in `R0_swap` (c is *strictly* above b). We prove the strict
`R0_swap.lt c b`: `c ≽ b` holds (`swapPref_le_left_c` reduces it to `(P 0).le a b`, true since
`a ≻ b`) and `b ⊁ c` (`b_not_le_c_in_R0_swap`). The prose's `c ≻ b` is now genuinely strict. -/
theorem c_lt_b_in_R0_swap : R0_swap.lt c b := by
  refine ⟨?_, ?_⟩
  · -- `c ≽ b`: reduces to `(P 0).le a b`, true since `a ≻ b`
    rw [swapPref_le_left_c_witness]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide
  · -- `b ⊁ c`: `b ≽ c` reduces to `(P 0).le b a`, false since `a ≻ b`
    rw [swapPref_le_right_c (a := a) (c := c) (by decide) (by decide)]
    simp only [P, utilP, preferenceOfUtilityIn_le_iff]; decide

/-- **`swapPref_le_right_c`** — `(swapPref R a c).le b c ↔ R.le b a` for `b ∉ {a, c}`.
`R0_swap.le b c ↔ (P 0).le b a`. Voter 0: `b ≺ a` (`u(a)=2 > u(b)=1`), so `(P 0).le b a` = false
(`b` is NOT weakly preferred over `a`). So `b` is not preferred to `c` in `R0_swap` (c has taken
a's top slot). -/
theorem swapPref_le_right_c_witness :
    R0_swap.le b c ↔ (P 0).le b a :=
  swapPref_le_right_c (by decide) (by decide)

/-- Concretely: `b` is NOT weakly preferred to `c` in `R0_swap` (c is above b). -/
theorem b_not_le_c_in_R0_swap : ¬ R0_swap.le b c := by
  rw [swapPref_le_right_c_witness]
  simp only [P, utilP, preferenceOfUtilityIn_le_iff]
  decide

/-- **`StrictPref.swapPref`** — the swapped preference is still strict. -/
theorem R0_swap_isStrict : Econlib.SocialChoice.StrictPref R0_swap :=
  (P_isStrict 0).swapPref a c

end EconlibTest.SocialChoice.Profile

end
