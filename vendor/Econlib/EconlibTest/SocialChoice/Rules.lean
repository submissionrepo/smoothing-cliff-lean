/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.SocialChoice
import EconlibExamples.SocialChoice.BordaPathologies
import Mathlib

/-!
# Aggregation-Rule Non-Vacuity Witnesses

Compile-time semantic witnesses for `Econlib.SocialChoice.Rule.*`,
`Econlib.SocialChoice.WelfareFunction.*`, and the generic scoring-rule layer (`Rule/Scoring.lean`,
`Rule/Resolute.lean`). Every theorem is tied to a hand-tabulated concrete electorate; the
tabulation appears in comments above each section so any mis-stated lemma or direction-flip fails
the numeric check rather than passing vacuously.

## What each section catches

* **§1 Borda tabulation** — `bordaScoreOf_eq_card`, `bordaScoringRule_scoreOf`,
  `bordaScoreOf_add_numStrictBetters`, `numStrictBetters_eq_card`, `numStrictBetters_eq_zero_iff`,
  `bordaScoreOf_swapPref`. Counting errors, off-by-ones, and direction flips in the filter
  predicates break these.
* **§2 Borda axioms** — `bordaWelfareFunction.WeakPareto` instantiated *and* consumed on
  `unanimousQ` (`bordaWelfareFunction_WeakPareto_Q_ca` proves `c ≻ a` from real data); the
  `bordaRel_lt_of_forall_lt` core lemma on a unanimous profile;
  `exists_strictProfile_bordaRel_not_lt_of_dictator` plus an *explicit* non-dictator witness on
  `cycleP` (`borda_no_dictator_voter0_cycleP`: voter 0 has `a ≻ b` but Borda ties them).
* **§3 Plurality counts** — `pluralityScore_eq_card`, `mem_pluralityWinners` (positive + negative),
  `pluralityWinners_nonempty`, `mem_pluralityWinners_iff_isTop`, and the *exact* winner set
  `pluralityWinners pluralP = {a}` (`pluralityWinners_pluralP_eq_singleton`). Wrong winner
  membership breaks these.
* **§4 Scoring-rule API** — `pluralityScoringRule_scoreOf`, `pluralityScoringRule_totalScore`,
  `pluralityScoringRule_aggregate_le_iff`, `bordaScoringRule_aggregate_le_iff`, with positive *and*
  negative directional checks (`*_a_le_b` / `*_not_b_le_a` on `pluralP`; `*_Q_c_le_a` /
  `*_Q_not_a_le_c` on the non-tie `unanimousQ`). Verifies scoring-rule and direct-count welfare
  functions agree on concrete profiles in *both* directions.
* **§5 Resolute Borda** — `mem_scoreArgmax` (positive + negative), `scoreWinner_mem`,
  `scoreWinner_max`, `scoreWinner_eq_of_strict_max`, `resoluteBorda_winners`,
  `resoluteBorda_domain`, and the **lex tie-break** fired on the `cycleP` three-way tie
  (`scoreWinner_bordaScore_cycleP_eq_a = a`, `resoluteBorda_winners_cycleP = {a}`) — the case a
  reversed tie-break would survive on the unique-maximizer `unanimousQ`.
* **§6 Majority / Condorcet** — `majorityCount_eq_card`, `majorityCount_comp_perm`,
  `majorityCount_update_add_one`, `majorityCount_update_le_of_not_lt`, `CondorcetWinner.beats`; the
  Condorcet cycle has NO winner (negative); the positive Condorcet winner on the BordaPathologies
  five-voter profile is rebuilt from **locally tabulated** majority counts
  (`condP_count_{0_1,1_0,0_2,2_0}`), not imported wholesale.
* **§7 Social order** — `socialLE`/`socialLT`/`socialIndiff` on `bordaWelfareFunction` with
  hand-checked Borda score comparisons; `socialIndiff` on a *nontrivial* tie of distinct
  alternatives (`bordaSWF_socialIndiff_cycleP_ab`, `a ~ b` from the `3 = 3` Borda totals), not just
  the trivial reflexive `a ~ a`.
* **§8 Welfare-function axioms** — `ParetoIndifference` TRUE on a projection SWF and FALSE on a
  constant SWF. **Test-only derivations** (not yet exported Econlib API):
  `bordaWelfareFunction_StrongPareto`, `bordaWelfareFunction_Anonymity` — see
  `backlog/sc-borda-properties-strongpareto-anonymity.md` for promotion to `BordaProperties.lean`.

## Data

Three shared profiles over `Fin 3` voters and `Fin 3` alternatives (`a=0`, `b=1`, `c=2`).

**`P` — the Condorcet cycle:** voter 0: A≻b≻c  (u=[2,1,0])  bordaScoreOf: A=2, b=1, c=0 voter 1:
B≻c≻a  (u=[0,2,1])  bordaScoreOf: B=2, c=1, a=0 voter 2: C≻a≻b  (u=[1,0,2])  bordaScoreOf: C=2,
a=1, b=0

Total bordaScore: A=3, b=3, c=3  (three-way tie)

numStrictBetters on voter 0 (a≻b≻c): A: 0,  b: 1,  c: 2 bordaScoreOf + numStrictBetters = 2 =
card(Fin 3) - 1 ✓

**`Q` — unanimous c≻b≻a  (u=[0,1,2] for every voter):** bordaScoreOf per voter: A=0, b=1, c=2 Total
bordaScore: A=0, b=3, c=6 bordaRel Q: C ≻ b ≻ a (strict total order)

**`S` — plurality test (3 voters, 3 alts):** voter 0: A≻b≻c  (u=[2,1,0])  topPick = a voter 1:
A≻c≻b  (u=[2,0,1])  topPick = a voter 2: B≻c≻a  (u=[0,2,1])  topPick = b pluralityScore: A=2, b=1,
c=0  →  pluralityWinners = {a}
-/

noncomputable section

namespace EconlibTest.SocialChoice.Rules

open Econlib.Preferences Econlib.SocialChoice Econlib.SocialChoice.WelfareFunction

/-! ### Profile data -/

/-- Utility matrix for the Condorcet cycle. Row `i` is voter `i`'s utility vector. -/
def utilP : Fin 3 → Fin 3 → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: a ≻ b ≻ c
     ![0, 2, 1],   -- voter 1: b ≻ c ≻ a
     ![1, 0, 2] ]  -- voter 2: c ≻ a ≻ b

/-- The Condorcet cycle profile. -/
def cycleP : Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilP i)

/-- Unanimous c≻b≻a profile: All voters report utility `![0,1,2]`. -/
def unanimousQ : Profile (Fin 3) (Fin 3) :=
  fun _i => preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)

/-- Utility matrix for the plurality profile. -/
def utilS : Fin 3 → Fin 3 → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: a ≻ b ≻ c  (topPick = a)
     ![2, 0, 1],   -- voter 1: a ≻ c ≻ b  (topPick = a)
     ![0, 2, 1] ]  -- voter 2: b ≻ c ≻ a  (topPick = b)

/-- Plurality test profile. -/
def pluralP : Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilS i)

-- Abbreviations for alternatives
private abbrev a : Fin 3 := 0
private abbrev b : Fin 3 := 1
private abbrev c : Fin 3 := 2

-- Definitional equalities used as simp hints to unfold the abbreviations when omega/norm_num
-- cannot evaluate `![...] a` / `![...] b` / `![...] c` as opaque `private abbrev` indices.
private lemma ha : a = (0 : Fin 3) := rfl
private lemma hb : b = (1 : Fin 3) := rfl
private lemma hc : c = (2 : Fin 3) := rfl

private lemma cycleP_isStrict : Profile.IsStrict cycleP :=
  fun i => strictPref_preferenceOfUtilityIn (by fin_cases i <;> decide)

private lemma unanimousQ_isStrict : Profile.IsStrict unanimousQ :=
  fun _i => strictPref_preferenceOfUtilityIn (by decide)

private lemma pluralP_isStrict : Profile.IsStrict pluralP :=
  fun i => strictPref_preferenceOfUtilityIn (by fin_cases i <;> decide)

-- Borda-score helper specialized to `Fin 3` utilities.
private lemma bordaScoreOf_util_eq3 (u : Fin 3 → ℕ) (x : Fin 3)
    (s : Finset (Fin 3)) (h : ∀ bb : Fin 3, u bb < u x ↔ bb ∈ s) :
    bordaScoreOf (preferenceOfUtilityIn u) x = s.card :=
  bordaScoreOf_eq_card _ x s (fun bb => by rw [preferenceOfUtilityIn_lt_iff]; exact h bb)

-- Total Borda scores for `cycleP` (the three-way `3/3/3` tie), used by both §2 and §4.
private lemma cycleP_bordaScore_a : bordaScore cycleP a = 3 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (utilP 0)) a
      + bordaScoreOf (preferenceOfUtilityIn (utilP 1)) a
      + bordaScoreOf (preferenceOfUtilityIn (utilP 2)) a = 3
  rw [bordaScoreOf_util_eq3 (utilP 0) a {1, 2}
        (by intro bb; fin_cases bb <;> simp [utilP, ha]),
      bordaScoreOf_util_eq3 (utilP 1) a ∅
        (by intro bb; fin_cases bb <;> simp [utilP, ha]),
      bordaScoreOf_util_eq3 (utilP 2) a {1}
        (by intro bb; fin_cases bb <;> simp [utilP, ha])]
  decide

private lemma cycleP_bordaScore_b : bordaScore cycleP b = 3 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (utilP 0)) b
      + bordaScoreOf (preferenceOfUtilityIn (utilP 1)) b
      + bordaScoreOf (preferenceOfUtilityIn (utilP 2)) b = 3
  rw [bordaScoreOf_util_eq3 (utilP 0) b {2}
        (by intro bb; fin_cases bb <;> simp [utilP, hb]),
      bordaScoreOf_util_eq3 (utilP 1) b {2, 0}
        (by intro bb; fin_cases bb <;> simp [utilP, hb]),
      bordaScoreOf_util_eq3 (utilP 2) b ∅
        (by intro bb; fin_cases bb <;> simp [utilP, hb])]
  decide

private lemma cycleP_bordaScore_c : bordaScore cycleP c = 3 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (utilP 0)) c
      + bordaScoreOf (preferenceOfUtilityIn (utilP 1)) c
      + bordaScoreOf (preferenceOfUtilityIn (utilP 2)) c = 3
  rw [bordaScoreOf_util_eq3 (utilP 0) c ∅
        (by intro bb; fin_cases bb <;> simp [utilP, hc]),
      bordaScoreOf_util_eq3 (utilP 1) c {0}
        (by intro bb; fin_cases bb <;> simp [utilP, hc]),
      bordaScoreOf_util_eq3 (utilP 2) c {0, 1}
        (by intro bb; fin_cases bb <;> simp [utilP, hc])]
  decide

/-! ### §1 Borda tabulation -/

/-! Voter 0 ballot (a≻b≻c, u=[2,1,0]): BordaScoreOf(P0, a) = |{b : U(b) < 2}| = |{b=1,c=2}| = 2
bordaScoreOf(P0, b) = |{b : U(b) < 1}| = |{c=2}|     = 1 bordaScoreOf(P0, c) = |{b : U(b) < 0}| = ∅
= 0 numStrictBetters(P0, a) = 0, (P0, b) = 1, (P0, c) = 2 -/

/-- **`bordaScoreOf_eq_card` on voter 0, alt `a`.** `a` beats `{b,c}` → score 2. Off-by-one in the
filter predicate (`<` vs `≤`) would break this. -/
theorem bordaScoreOf_P0_a : bordaScoreOf (cycleP 0) a = 2 :=
  bordaScoreOf_util_eq3 (utilP 0) a {1, 2} (by intro bb; fin_cases bb <;> simp [utilP, ha])

/-- `b` beats `{c}` under voter 0 → score 1. -/
theorem bordaScoreOf_P0_b : bordaScoreOf (cycleP 0) b = 1 :=
  bordaScoreOf_util_eq3 (utilP 0) b {2} (by intro bb; fin_cases bb <;> simp [utilP, hb])

/-- `c` beats nobody under voter 0 → score 0. -/
theorem bordaScoreOf_P0_c : bordaScoreOf (cycleP 0) c = 0 :=
  bordaScoreOf_util_eq3 (utilP 0) c ∅ (by intro bb; fin_cases bb <;> simp [utilP, hc])

/-- **`numStrictBetters_eq_card`.** Under voter 0's ballot, the alternatives strictly above `b=1`
are exactly `{a=0}`, so the count is 1. -/
theorem numStrictBetters_P0_b :
    numStrictBetters (cycleP 0) b = 1 :=
  numStrictBetters_eq_card (cycleP 0) b {0} (by
    intro x; fin_cases x <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, hb])

/-- Alternatives strictly above `c=2` under voter 0 are `{a,b}` → count 2. -/
theorem numStrictBetters_P0_c :
    numStrictBetters (cycleP 0) c = 2 :=
  numStrictBetters_eq_card (cycleP 0) c {0, 1} (by
    intro x; fin_cases x <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, hc])

/-- Nobody is strictly above `a=0` under voter 0 → count 0. -/
theorem numStrictBetters_P0_a :
    numStrictBetters (cycleP 0) a = 0 :=
  numStrictBetters_eq_card (cycleP 0) a ∅ (by
    intro x; fin_cases x <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha])

/-- **`numStrictBetters_eq_zero_iff`.** `a=0` has zero strict-betters under voter 0 iff `a` weakly
dominates every alternative. Exercises the `↔ ∀ b, R.le a b` direction. -/
theorem numStrictBetters_P0_a_iff :
    numStrictBetters (cycleP 0) a = 0 ↔ ∀ bb : Fin 3, (cycleP 0).le a bb :=
  numStrictBetters_eq_zero_iff a

/-- Concrete: `a` weakly dominates everything under voter 0 (u(a)=2 is maximal). -/
theorem P0_a_weakly_dominates (bb : Fin 3) : (cycleP 0).le a bb := by
  have h := numStrictBetters_P0_a_iff.mp numStrictBetters_P0_a
  exact h bb

/-- **`bordaScoreOf_add_numStrictBetters`.** For any alternative on voter 0's strict ballot,
beaten-below + beaten-above = card - 1 = 2. a: 2+0=2 ✓  b: 1+1=2 ✓  c: 0+2=2 ✓ -/
theorem bordaScoreOf_add_numStrictBetters_P0 (x : Fin 3) :
    bordaScoreOf (cycleP 0) x + numStrictBetters (cycleP 0) x = Fintype.card (Fin 3) - 1 :=
  bordaScoreOf_add_numStrictBetters (cycleP_isStrict 0) x

/-- Numeric anchor for `b`: 1+1=2. -/
theorem bordaScoreOf_add_numStrictBetters_P0_b_num :
    bordaScoreOf (cycleP 0) b + numStrictBetters (cycleP 0) b = 2 := by
  rw [bordaScoreOf_P0_b, numStrictBetters_P0_b]

/-- **`bordaScoringRule_scoreOf`.** On voter 0's strict ballot, the scoring-rule score at `b`
equals the Borda count cast to ℝ. Numeric check: Score(rank 1) = 2-1-1 = 1 = bordaScoreOf. -/
theorem bordaScoringRule_scoreOf_P0 (x : Fin 3) :
    bordaScoringRule.scoreOf (cycleP 0) x = (bordaScoreOf (cycleP 0) x : ℝ) :=
  bordaScoringRule_scoreOf (cycleP_isStrict 0) x

/-- Numeric anchor: `bordaScoringRule.scoreOf (cycleP 0) b = 1`. -/
theorem bordaScoringRule_scoreOf_P0_b_num :
    bordaScoringRule.scoreOf (cycleP 0) b = 1 := by
  rw [bordaScoringRule_scoreOf_P0, bordaScoreOf_P0_b]; norm_cast

/-- **`bordaScoreOf_swapPref`.** After swapping `a` and `c` in voter 0's ballot (a≻b≻c → c≻b≻a),
`a` drops to the bottom (score 0) and `c` rises to the top (score 2). Formula:
`bordaScoreOf(swapPref R a c, z) = bordaScoreOf(R, swap a c z)`. z=a: Swap(a,c)(a)=c →
bordaScoreOf(P0,c)=0 ✓ z=c: Swap(a,c)(c)=a → bordaScoreOf(P0,a)=2 ✓ -/
theorem bordaScoreOf_swapPref_P0_a :
    bordaScoreOf (swapPref (cycleP 0) a c) a = bordaScoreOf (cycleP 0) (Equiv.swap a c a) :=
  bordaScoreOf_swapPref (cycleP 0) a c a

theorem bordaScoreOf_swapPref_P0_c :
    bordaScoreOf (swapPref (cycleP 0) a c) c = bordaScoreOf (cycleP 0) (Equiv.swap a c c) :=
  bordaScoreOf_swapPref (cycleP 0) a c c

/-- Numeric anchor: After swap, `a`'s Borda score is 0 (now at the bottom). -/
theorem bordaScoreOf_swapPref_P0_a_num :
    bordaScoreOf (swapPref (cycleP 0) a c) a = 0 := by
  rw [bordaScoreOf_swapPref_P0_a, Equiv.swap_apply_left, bordaScoreOf_P0_c]

/-- Numeric anchor: After swap, `c`'s Borda score is 2 (now at the top). -/
theorem bordaScoreOf_swapPref_P0_c_num :
    bordaScoreOf (swapPref (cycleP 0) a c) c = 2 := by
  rw [bordaScoreOf_swapPref_P0_c, Equiv.swap_apply_right, bordaScoreOf_P0_a]

/-! ### §2 Borda axioms -/

/-! Total Borda scores under `unanimousQ` (unanimous c≻b≻a, u=[0,1,2]): BordaScoreOf per voter:
A=0, b=1, c=2 Total bordaScore: A=0, b=3, c=6

WeakPareto check: All voters rank c ≻ a (u(c)=2 > 0=u(a)) → bordaRel Q has c ≻ a. -/

private lemma Q_bordaScore_a : bordaScore unanimousQ a = 0 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) a
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) a
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) a = 0
  rw [bordaScoreOf_util_eq3 ![0, 1, 2] a ∅ (by decide)]; decide

private lemma Q_bordaScore_b : bordaScore unanimousQ b = 3 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) b
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) b
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) b = 3
  rw [bordaScoreOf_util_eq3 ![0, 1, 2] b {0} (by decide)]; decide

private lemma Q_bordaScore_c : bordaScore unanimousQ c = 6 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) c
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) c
      + bordaScoreOf (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)) c = 6
  rw [bordaScoreOf_util_eq3 ![0, 1, 2] c {0, 1} (by decide)]; decide

/-- **`bordaRel_lt_of_forall_lt` on unanimousQ.** All voters rank c ≻ a, so Borda aggregate
strictly ranks c above a. A vacuous `Nonempty Voter` guard breaks this. -/
theorem bordaRel_Q_c_lt_a : (bordaRel unanimousQ).lt c a :=
  bordaRel_lt_of_forall_lt unanimousQ (fun _i => by
    simp [unanimousQ, preferenceOfUtilityIn_lt_iff, ha, hc])

/-- Numeric sanity: BordaScore Q c = 6 > 0 = bordaScore Q a. -/
theorem bordaRel_Q_c_lt_a_via_scores : (bordaRel unanimousQ).lt c a := by
  rw [bordaRel, preferenceOfUtilityIn_lt_iff, Q_bordaScore_a, Q_bordaScore_c]; norm_num

/-- **`bordaWelfareFunction.WeakPareto` instance.** The library theorem is instantiated at `Fin 3`
× `Fin 3`. -/
theorem bordaWelfareFunction_WeakPareto_instance :
    (bordaWelfareFunction (Voter := Fin 3) (Alt := Fin 3)).WeakPareto :=
  bordaWelfareFunction.WeakPareto

/-- **`bordaWelfareFunction.WeakPareto` consumed on `unanimousQ`.** Feeding the unanimous profile
`unanimousQ` (every voter `c ≻ b ≻ a`) and its strict-domain membership into Weak Pareto: since all
voters strictly prefer `c` to `a`, society does too — `c ≻ a` under `bordaRel unanimousQ` (Borda
scores `c = 6 > 0 = a`). This exercises the axiom on a concrete electorate, not just its type. -/
theorem bordaWelfareFunction_WeakPareto_Q_ca :
    (bordaWelfareFunction (Voter := Fin 3) (Alt := Fin 3)).aggregate unanimousQ |>.lt c a := by
  refine bordaWelfareFunction_WeakPareto_instance unanimousQ
    (mem_strictDomain.mpr unanimousQ_isStrict) c a (fun i => ?_)
  simp [unanimousQ, preferenceOfUtilityIn_lt_iff, ha, hc]

/-- **`exists_strictProfile_bordaRel_not_lt_of_dictator` instantiation.** For voter `0` over a
3-voter 3-alt electorate, there exists a strict profile where voter 0 strictly prefers some `x`
over `y` but society under Borda does NOT. -/
theorem borda_no_dictator_voter0 :
    ∃ P' : Profile (Fin 3) (Fin 3), Profile.IsStrict P' ∧ ∃ x y : Fin 3,
      (P' 0).lt x y ∧ ¬ (bordaRel P').lt x y :=
  exists_strictProfile_bordaRel_not_lt_of_dictator (by decide) (by decide) 0

/-- **Explicit non-dictator witness on the Condorcet cycle `cycleP`.** Voter 0 is the "lone fan" of
`a` over `b`: voter 0's ballot is `a ≻ b ≻ c` (so `(cycleP 0).lt a b`), yet Borda *ties* `a` and `b`
at score `3` each (`cycleP_bordaScore_a = cycleP_bordaScore_b = 3`), so `bordaRel cycleP` does
**not** rank `a ≻ b`. A concrete instance of `borda_no_dictator_voter0` — voter 0's preference is
not imposed on society, so Borda is no dictatorship. -/
theorem borda_no_dictator_voter0_cycleP :
    (cycleP 0).lt a b ∧ ¬ (bordaRel cycleP).lt a b := by
  refine ⟨?_, ?_⟩
  · -- voter 0 has `a ≻ b` (u(a)=2 > u(b)=1)
    simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb]
  · -- Borda ties them: `a ⊁ b` since `bordaScore a = 3 = bordaScore b`
    rw [bordaRel, preferenceOfUtilityIn_lt_iff, cycleP_bordaScore_a, cycleP_bordaScore_b]
    norm_num

/-! ### §3 Plurality counts -/

/-! Profile `pluralP`: TopPick(P0) = a  (u(a)=2 maximal; a=0 is lex-min of {a}) topPick(P1) = a
(u(a)=2 maximal) topPick(P2) = b  (u(b)=2 maximal)

pluralityScore(S, a) = |{0,1}| = 2 pluralityScore(S, b) = |{2}|   = 1 pluralityScore(S, c) = 0

pluralityWinners(S) = {a}  (unique score-maximum) -/

private lemma topPick_P0 : topPick (pluralP 0) = a :=
  topPick_eq (pluralP_isStrict 0) (by
    intro bb; fin_cases bb <;> simp [pluralP, utilS, preferenceOfUtilityIn_le_iff, ha])

private lemma topPick_P1 : topPick (pluralP 1) = a :=
  topPick_eq (pluralP_isStrict 1) (by
    intro bb; fin_cases bb <;> simp [pluralP, utilS, preferenceOfUtilityIn_le_iff, ha])

private lemma topPick_P2 : topPick (pluralP 2) = b :=
  topPick_eq (pluralP_isStrict 2) (by
    intro bb; fin_cases bb <;> simp [pluralP, utilS, preferenceOfUtilityIn_le_iff, hb])

/-- **`pluralityScore_eq_card` — `a` scores 2.** Voters 0 and 1 both pick `a` as top pick. A
direction flip in `topPick` membership breaks this. -/
theorem pluralityScore_pluralP_a : pluralityScore pluralP a = 2 :=
  pluralityScore_eq_card pluralP a {0, 1} (by
    intro i; fin_cases i <;>
      simp [topPick_P0, topPick_P1, topPick_P2])

/-- `b` scores 1 (only voter 2). -/
theorem pluralityScore_pluralP_b : pluralityScore pluralP b = 1 :=
  pluralityScore_eq_card pluralP b {2} (by
    intro i; fin_cases i <;>
      simp [topPick_P0, topPick_P1, topPick_P2])

/-- `c` scores 0. -/
theorem pluralityScore_pluralP_c : pluralityScore pluralP c = 0 :=
  pluralityScore_eq_card pluralP c ∅ (by
    intro i
    fin_cases i
    · -- i = 0: topPick (pluralP 0) = a ≠ c, and 0 ∉ ∅.
      suffices topPick (pluralP 0) ≠ c by simp [this]
      rw [topPick_P0]; decide
    · -- i = 1: topPick (pluralP 1) = a ≠ c, and 1 ∉ ∅.
      suffices topPick (pluralP 1) ≠ c by simp [this]
      rw [topPick_P1]; decide
    · -- i = 2: topPick (pluralP 2) = b ≠ c, and 2 ∉ ∅.
      suffices topPick (pluralP 2) ≠ c by simp [this]
      rw [topPick_P2]; decide)

/-- **`mem_pluralityWinners` positive check.** `a` is a winner: Score 2 ≥ all others. -/
theorem a_mem_pluralityWinners : a ∈ pluralityWinners pluralP := by
  rw [mem_pluralityWinners]
  intro bb; fin_cases bb <;>
    simp [pluralityScore_pluralP_a, pluralityScore_pluralP_b, pluralityScore_pluralP_c]

/-- **`mem_pluralityWinners` negative check.** `b` is NOT a winner (score 1 < 2 = score a). -/
theorem b_not_mem_pluralityWinners : b ∉ pluralityWinners pluralP := by
  rw [mem_pluralityWinners]
  push Not
  exact ⟨a, by simp [pluralityScore_pluralP_a, pluralityScore_pluralP_b]⟩

/-- **`pluralityWinners_nonempty`.** Every nonempty fintype has at least one winner. -/
theorem pluralityWinners_nonempty_witness : (pluralityWinners pluralP).Nonempty :=
  pluralityWinners_nonempty pluralP

/-- `c` is NOT a plurality winner of `pluralP` (score 0 < 2 = score a). -/
theorem c_not_mem_pluralityWinners : c ∉ pluralityWinners pluralP := by
  rw [mem_pluralityWinners]
  push Not
  exact ⟨a, by simp [pluralityScore_pluralP_a, pluralityScore_pluralP_c]⟩

/-- **The exact plurality winner set is `{a}`.** Strengthening the bare nonemptiness check:
`pluralityWinners pluralP = {a}` (scores `a = 2 > b = 1 > c = 0`, a unique maximizer). This pins the
full winner set, ruling out wrong definitions like `univ` that nonemptiness alone would admit. -/
theorem pluralityWinners_pluralP_eq_singleton : pluralityWinners pluralP = {a} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨a_mem_pluralityWinners, fun x hx => ?_⟩
  -- any winner `x` must be `a`; `b` and `c` are excluded by their lower scores.
  fin_cases x
  · rfl
  · exact absurd hx b_not_mem_pluralityWinners
  · exact absurd hx c_not_mem_pluralityWinners

/-- **`mem_pluralityWinners_iff_isTop`.** `a` is a plurality winner iff it weakly dominates every
alternative in `pluralityRel pluralP`. -/
theorem a_mem_pluralityWinners_iff_isTop :
    a ∈ pluralityWinners pluralP ↔ ∀ bb : Fin 3, (pluralityRel pluralP).le a bb :=
  mem_pluralityWinners_iff_isTop

/-- Numeric verification of dominance: `a` weakly dominates all in `pluralityRel`. -/
theorem pluralityRel_a_dominates (bb : Fin 3) : (pluralityRel pluralP).le a bb := by
  rw [pluralityRel, preferenceOfUtilityIn_le_iff]
  fin_cases bb <;>
    simp [pluralityScore_pluralP_a, pluralityScore_pluralP_b, pluralityScore_pluralP_c]

/-! ### §4 Scoring-rule API -/

/-! Profile `pluralP` strict. Voter 0's ballot (a≻b≻c, u=[2,1,0]): TopPick = a  →
pluralityScoringRule.scoreOf(P0, a) = score(0) = 1 pluralityScoringRule.scoreOf(P0, b) = score(1) =
0 totalScore(pluralP, a) = 1+1+0 = 2.0 = pluralityScore a ✓ -/

/-- **`pluralityScoringRule_scoreOf` on voter 0's ballot.** `a=0` is voter 0's top pick. -/
theorem pluralityScoringRule_scoreOf_P0_a :
    pluralityScoringRule.scoreOf (pluralP 0) a = if topPick (pluralP 0) = a then 1 else 0 :=
  pluralityScoringRule_scoreOf (pluralP_isStrict 0) a

/-- Concretely: Score is 1. -/
theorem pluralityScoringRule_scoreOf_P0_a_num :
    pluralityScoringRule.scoreOf (pluralP 0) a = 1 := by
  rw [pluralityScoringRule_scoreOf_P0_a, topPick_P0]; simp

/-- Voter 0 does not pick `b`, so its plurality scoring score is 0. -/
theorem pluralityScoringRule_scoreOf_P0_b_zero :
    pluralityScoringRule.scoreOf (pluralP 0) b = 0 := by
  rw [pluralityScoringRule_scoreOf (pluralP_isStrict 0) b, topPick_P0]
  norm_num

/-- **`pluralityScoringRule_totalScore`.** Total scoring-rule score equals `pluralityScore` cast to
ℝ. -/
theorem pluralityScoringRule_totalScore_a :
    pluralityScoringRule.totalScore pluralP a = (pluralityScore pluralP a : ℝ) :=
  pluralityScoringRule_totalScore pluralP_isStrict a

/-- Numeric anchor: 2.0. -/
theorem pluralityScoringRule_totalScore_a_num :
    pluralityScoringRule.totalScore pluralP a = 2 := by
  rw [pluralityScoringRule_totalScore_a, pluralityScore_pluralP_a]; norm_cast

/-- **`pluralityScoringRule_aggregate_le_iff`.** Plurality scoring rule's welfare aggregate agrees
with `pluralityRel` on every pair over `pluralP`. -/
theorem pluralityScoringRule_aggregate_le_iff_pluralP (x y : Fin 3) :
    (pluralityScoringRule.toWelfareFunction.aggregate pluralP).le x y ↔
      (pluralityRel pluralP).le x y :=
  pluralityScoringRule_aggregate_le_iff pluralP_isStrict x y

/-- **Positive directional check.** The plurality scoring-rule aggregate ranks `a ≻ b` on `pluralP`
(`a` scores 2, `b` scores 1): the aggregate `le a b` holds. -/
theorem pluralityScoringRule_aggregate_a_le_b :
    (pluralityScoringRule.toWelfareFunction.aggregate pluralP).le a b := by
  rw [pluralityScoringRule_aggregate_le_iff_pluralP, pluralityRel, preferenceOfUtilityIn_le_iff,
    pluralityScore_pluralP_a, pluralityScore_pluralP_b]
  norm_num

/-- **Negative directional check.** The plurality scoring-rule aggregate does **not** rank `b ≽ a`
(it would require `score a ≤ score b`, i.e. `2 ≤ 1`). A reversed comparison would wrongly make this
hold. -/
theorem pluralityScoringRule_aggregate_not_b_le_a :
    ¬ (pluralityScoringRule.toWelfareFunction.aggregate pluralP).le b a := by
  rw [pluralityScoringRule_aggregate_le_iff_pluralP, pluralityRel, preferenceOfUtilityIn_le_iff,
    pluralityScore_pluralP_a, pluralityScore_pluralP_b]
  norm_num

/-- **`bordaScoringRule_aggregate_le_iff`.** Borda scoring rule's welfare aggregate agrees with
`bordaRel` on every pair over `cycleP`. -/
theorem bordaScoringRule_aggregate_le_iff_cycleP (x y : Fin 3) :
    (bordaScoringRule.toWelfareFunction.aggregate cycleP).le x y ↔ (bordaRel cycleP).le x y :=
  bordaScoringRule_aggregate_le_iff cycleP_isStrict x y

/-- Numeric check at a **tie**: `a ≤ b` in `bordaScoringRule`'s aggregate (on `cycleP`, where `a`
and `b` both score 3). This only checks the equality boundary; the non-tie directional checks below
on `unanimousQ` are the discriminating ones. -/
theorem bordaScoringRule_aggregate_le_iff_cycleP_ab :
    (bordaScoringRule.toWelfareFunction.aggregate cycleP).le a b := by
  rw [bordaScoringRule_aggregate_le_iff_cycleP a b, bordaRel, preferenceOfUtilityIn_le_iff,
    cycleP_bordaScore_a, cycleP_bordaScore_b]

/-- **Non-tie positive directional check on `unanimousQ`.** The Borda scoring-rule aggregate ranks
`c ≻ a` (Borda scores `c = 6 > 0 = a`): the aggregate `le c a` holds. -/
theorem bordaScoringRule_aggregate_Q_c_le_a :
    (bordaScoringRule.toWelfareFunction.aggregate unanimousQ).le c a := by
  rw [bordaScoringRule_aggregate_le_iff unanimousQ_isStrict c a, bordaRel,
    preferenceOfUtilityIn_le_iff, Q_bordaScore_a, Q_bordaScore_c]
  norm_num

/-- **Non-tie negative directional check on `unanimousQ`.** The Borda scoring-rule aggregate does
**not** rank `a ≽ c` (it would require `score c ≤ score a`, i.e. `6 ≤ 0`). On the non-tie profile a
swapped order or reversed comparison would surface here — unlike the `cycleP` tie check above. -/
theorem bordaScoringRule_aggregate_Q_not_a_le_c :
    ¬ (bordaScoringRule.toWelfareFunction.aggregate unanimousQ).le a c := by
  rw [bordaScoringRule_aggregate_le_iff unanimousQ_isStrict a c, bordaRel,
    preferenceOfUtilityIn_le_iff, Q_bordaScore_a, Q_bordaScore_c]
  norm_num

/-! ### §5 Resolute Borda -/

/-! Profile `unanimousQ` (unanimous c≻b≻a): BordaScore: A=0, b=3, c=6. scoreArgmax(bordaScore Q) =
{c}  (c is the unique strict maximizer) scoreWinner = c  (tie-break irrelevant) -/

private lemma Q_bordaScore_strict_max :
    ∀ bb : Fin 3, bb ≠ c → bordaScore unanimousQ bb < bordaScore unanimousQ c := by
  intro bb hb
  fin_cases bb
  · -- bb = a=0: score 0 < 6
    norm_num [Q_bordaScore_a, Q_bordaScore_c]
  · -- bb = b=1: score 3 < 6
    norm_num [Q_bordaScore_b, Q_bordaScore_c]
  · -- bb = c=2: excluded by hb
    exact absurd rfl hb

/-- **`mem_scoreArgmax` positive check.** `c=2` is in the Borda argmax under unanimousQ. -/
theorem c_mem_scoreArgmax_Q : c ∈ scoreArgmax (bordaScore unanimousQ) := by
  rw [mem_scoreArgmax]
  intro bb; fin_cases bb <;>
    simp [Q_bordaScore_a, Q_bordaScore_b, Q_bordaScore_c]

/-- **`mem_scoreArgmax` negative check.** `a=0` is NOT in the argmax: Score 0 < 6. -/
theorem a_not_mem_scoreArgmax_Q : a ∉ scoreArgmax (bordaScore unanimousQ) := by
  rw [mem_scoreArgmax]; push Not
  exact ⟨c, by rw [Q_bordaScore_a, Q_bordaScore_c]; norm_num⟩

/-- **`scoreWinner_mem`.** The resolute winner is a score-maximizer. -/
theorem scoreWinner_bordaScore_Q_mem :
    scoreWinner (bordaScore unanimousQ) ∈ scoreArgmax (bordaScore unanimousQ) :=
  scoreWinner_mem (bordaScore unanimousQ)

/-- **`scoreWinner_max`.** Every alternative scores ≤ the resolute winner. -/
theorem scoreWinner_bordaScore_Q_max (bb : Fin 3) :
    bordaScore unanimousQ bb ≤ bordaScore unanimousQ (scoreWinner (bordaScore unanimousQ)) :=
  scoreWinner_max (bordaScore unanimousQ) bb

/-- **`scoreWinner_eq_of_strict_max`.** `c=2` is the unique strict maximizer, so the resolute
winner is exactly `c`. -/
theorem scoreWinner_bordaScore_Q_eq_c :
    scoreWinner (bordaScore unanimousQ) = c :=
  scoreWinner_eq_of_strict_max (bordaScore unanimousQ) (bordaScore unanimousQ) (fun _ => rfl)
    Q_bordaScore_strict_max

/-- **`resoluteBorda_winners`.** The resolute-Borda winner set at unanimousQ is `{c}`. -/
theorem resoluteBorda_winners_Q :
    (resoluteBorda (Voter := Fin 3)).winners unanimousQ = {c} := by
  rw [resoluteBorda_winners, scoreWinner_bordaScore_Q_eq_c]

/-! #### The lexicographic tie-break, exercised on the `cycleP` three-way tie

`unanimousQ` has a *unique* strict maximizer (`c`), so the lex tie-break never fires there — a
reversed `min'`/`max'` tie-break would survive `scoreWinner_bordaScore_Q_eq_c`. The Condorcet cycle
`cycleP` has Borda scores `a = b = c = 3` (a perfect three-way tie), so its `scoreArgmax` is the
*whole* alternative set and the tie-break must pick the lexicographic minimum `a = 0`. -/

/-- The Borda argmax on `cycleP` is the full alternative set (all three score 3). -/
theorem cycleP_scoreArgmax_univ :
    scoreArgmax (bordaScore cycleP) = (Finset.univ : Finset (Fin 3)) := by
  apply Finset.eq_univ_of_forall
  intro x
  rw [mem_scoreArgmax]
  intro bb
  fin_cases x <;> fin_cases bb <;>
    simp [cycleP_bordaScore_a, cycleP_bordaScore_b, cycleP_bordaScore_c]

/-- **The tie-break fires and picks the lex-min `a = 0`.** On the three-way Borda tie of `cycleP`,
`scoreWinner (bordaScore cycleP) = a`: the argmax is all of `{0,1,2}`, so the resolute rule's
lexicographic `min'` tie-break returns `0`. A reversed tie-break (lex-max) would return `2` and fail
here — the case the unique-maximizer `unanimousQ` witness cannot catch. -/
theorem scoreWinner_bordaScore_cycleP_eq_a :
    scoreWinner (bordaScore cycleP) = a := by
  -- `scoreWinner = min' (scoreArgmax …)`; `0 ∈ argmax` (it is `univ`), and `0` is the bottom of
  -- `Fin 3`, so the lex-min is `0 = a` by antisymmetry.
  have h0mem : (0 : Fin 3) ∈ scoreArgmax (bordaScore cycleP) := by
    rw [cycleP_scoreArgmax_univ]; exact Finset.mem_univ _
  refine le_antisymm ?_ (Fin.zero_le _)
  exact Finset.min'_le _ 0 h0mem

/-- The resolute-Borda winner set on the cyclic tie `cycleP` is the lex-min singleton `{a}`. -/
theorem resoluteBorda_winners_cycleP :
    (resoluteBorda (Voter := Fin 3)).winners cycleP = {a} := by
  rw [resoluteBorda_winners, scoreWinner_bordaScore_cycleP_eq_a]

/-- **`resoluteBorda_domain`.** The resolute Borda domain is the strict domain. -/
theorem resoluteBorda_domain_eq :
    (resoluteBorda (Voter := Fin 3) (Alt := Fin 3)).domain = strictDomain (Fin 3) (Fin 3) :=
  resoluteBorda_domain

/-- `unanimousQ` lives in the resolute Borda domain. -/
theorem Q_mem_resoluteBorda_domain :
    unanimousQ ∈ (resoluteBorda (Voter := Fin 3)).domain :=
  resoluteBorda_domain_eq ▸ mem_strictDomain.mpr unanimousQ_isStrict

/-! ### §6 Majority / Condorcet -/

/-! Profile `cycleP` (Condorcet cycle, 3 voters): MajorityCount P a b = |{0,2}| = 2  (voters 0 and
2 rank a≻b) majorityCount P b a = |{1}|   = 1 majorityCount P b c = |{0,1}| = 2 majorityCount P c b
= |{2}|   = 1 majorityCount P c a = |{1,2}| = 2 majorityCount P a c = |{0}|   = 1

pairwiseMajority: A beats b, b beats c, c beats a  → CYCLE No Condorcet winner.

Positive case: BordaPathologies.condP (5 voters), x=0 is Condorcet winner. -/

/-- **`majorityCount_eq_card` — a beats b, 2:1.** Voters who rank a≻b: {0,2}. -/
theorem majorityCount_cycleP_ab : majorityCount cycleP a b = 2 :=
  majorityCount_eq_card cycleP a b {0, 2} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb])

theorem majorityCount_cycleP_ba : majorityCount cycleP b a = 1 :=
  majorityCount_eq_card cycleP b a {1} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb])

theorem majorityCount_cycleP_bc : majorityCount cycleP b c = 2 :=
  majorityCount_eq_card cycleP b c {0, 1} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, hb, hc])

theorem majorityCount_cycleP_cb : majorityCount cycleP c b = 1 :=
  majorityCount_eq_card cycleP c b {2} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, hb, hc])

theorem majorityCount_cycleP_ca : majorityCount cycleP c a = 2 :=
  majorityCount_eq_card cycleP c a {1, 2} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hc])

theorem majorityCount_cycleP_ac : majorityCount cycleP a c = 1 :=
  majorityCount_eq_card cycleP a c {0} (by
    intro i; fin_cases i <;> simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hc])

/-- **The majority relation cycles on `cycleP`.** -/
theorem cycleP_majority_cycles :
    pairwiseMajority cycleP a b ∧ pairwiseMajority cycleP b c ∧ pairwiseMajority cycleP c a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairwiseMajority, majorityCount_cycleP_ba, majorityCount_cycleP_ab]; norm_num
  · rw [pairwiseMajority, majorityCount_cycleP_cb, majorityCount_cycleP_bc]; norm_num
  · rw [pairwiseMajority, majorityCount_cycleP_ac, majorityCount_cycleP_ca]; norm_num

/-- **No Condorcet winner.** The cycle means every alternative is beaten by some rival. -/
theorem cycleP_no_condorcet_winner : ¬ ∃ x : Fin 3, CondorcetWinner cycleP x := by
  obtain ⟨hab, hbc, hca⟩ := cycleP_majority_cycles
  rintro ⟨x, hx⟩
  fin_cases x
  · exact absurd (hx.beats (y := c) (by decide)) (lt_asymm hca)
  · exact absurd (hx.beats (y := a) (by decide)) (lt_asymm hab)
  · exact absurd (hx.beats (y := b) (by decide)) (lt_asymm hbc)

/-- **`CondorcetWinner.beats` exercise (negative).** `a` is beaten by `c` in `cycleP`, so `a` is
NOT a Condorcet winner. -/
theorem a_not_condorcet_winner_cycleP : ¬ CondorcetWinner cycleP a :=
  fun h => absurd (h.beats (y := c) (by decide)) (lt_asymm cycleP_majority_cycles.2.2)

/-! #### Condorcet winner, locally tabulated on `condP`

The positive Condorcet case reuses `BordaPathologies.condP` (5 voters, 3 alternatives: three rank
`x ≻ y ≻ z`, two rank `y ≻ z ≻ x`). Rather than importing `condorcet_winner_x` wholesale, we
recompute the four pairwise majority counts **here**:

| pair      | supporting voters | count |
| --------- | ----------------- | ----- |
| `x ≻ y`   | `{0, 1, 2}`       | 3     |
| `y ≻ x`   | `{3, 4}`          | 2     |
| `x ≻ z`   | `{0, 1, 2}`       | 3     |
| `z ≻ x`   | `{3, 4}`          | 2     |

So `x = 0` beats each rival 3 to 2 and is the Condorcet winner. -/

private abbrev condP : Profile (Fin 5) (Fin 3) :=
  EconlibExamples.SocialChoice.BordaPathologies.condP

/-- Local count: 3 voters rank `x ≻ y` in `condP`. -/
theorem condP_count_0_1 : majorityCount condP 0 1 = 3 :=
  majorityCount_eq_card condP 0 1 {0, 1, 2}
    (by intro i; fin_cases i <;>
      simp [condP, EconlibExamples.SocialChoice.BordaPathologies.condP,
        preferenceOfUtilityIn_lt_iff])

/-- Local count: only 2 voters rank `y ≻ x` in `condP`. -/
theorem condP_count_1_0 : majorityCount condP 1 0 = 2 :=
  majorityCount_eq_card condP 1 0 {3, 4}
    (by intro i; fin_cases i <;>
      simp [condP, EconlibExamples.SocialChoice.BordaPathologies.condP,
        preferenceOfUtilityIn_lt_iff])

/-- Local count: 3 voters rank `x ≻ z` in `condP`. -/
theorem condP_count_0_2 : majorityCount condP 0 2 = 3 :=
  majorityCount_eq_card condP 0 2 {0, 1, 2}
    (by intro i; fin_cases i <;>
      simp [condP, EconlibExamples.SocialChoice.BordaPathologies.condP,
        preferenceOfUtilityIn_lt_iff])

/-- Local count: only 2 voters rank `z ≻ x` in `condP`. -/
theorem condP_count_2_0 : majorityCount condP 2 0 = 2 :=
  majorityCount_eq_card condP 2 0 {3, 4}
    (by intro i; fin_cases i <;>
      simp [condP, EconlibExamples.SocialChoice.BordaPathologies.condP,
        preferenceOfUtilityIn_lt_iff])

/-- **`CondorcetWinner.beats` at x vs y, from local counts.** `x = 0` beats `y = 1` pairwise: 3 > 2
(`condP_count_0_1`, `condP_count_1_0`), recomputed in this file. -/
theorem condP_x_beats_y : pairwiseMajority condP 0 1 := by
  rw [pairwiseMajority, condP_count_1_0, condP_count_0_1]; norm_num

/-- `x = 0` beats `z = 2` pairwise: 3 > 2 (`condP_count_0_2`, `condP_count_2_0`). -/
theorem condP_x_beats_z : pairwiseMajority condP 0 2 := by
  rw [pairwiseMajority, condP_count_2_0, condP_count_0_2]; norm_num

/-- **Condorcet winner positive case, proved from the local counts.** `x = 0` beats both rivals 3:2
(`condP_x_beats_y`, `condP_x_beats_z`), so it is the Condorcet winner of `condP` — established here
from the locally-tabulated majority counts, not imported from `BordaPathologies`. -/
theorem condP_condorcet_winner_x : CondorcetWinner condP 0 := by
  intro y hy
  fin_cases y
  · exact absurd rfl hy
  · exact condP_x_beats_y
  · exact condP_x_beats_z

/-- **`majorityCount_comp_perm`.** Swapping voters 0 and 1 in `cycleP` leaves the a-vs-b count
unchanged (it's still 2). -/
theorem majorityCount_cycleP_perm_swap_ab :
    majorityCount (cycleP ∘ Equiv.swap (0 : Fin 3) 1) a b = majorityCount cycleP a b :=
  majorityCount_comp_perm cycleP (Equiv.swap 0 1) a b

/-- Concretely: The count is still 2 after the permutation. -/
theorem majorityCount_cycleP_perm_swap_ab_num :
    majorityCount (cycleP ∘ Equiv.swap (0 : Fin 3) 1) a b = 2 := by
  rw [majorityCount_cycleP_perm_swap_ab, majorityCount_cycleP_ab]

/-- **`majorityCount_update_add_one`.** Voter 1 in `cycleP` ranks b≻c≻a (does NOT rank a≻b: U(a)=0
< u(b)=2). Switching voter 1 to voter 0's ballot (a≻b≻c) adds one a≻b supporter. -/
theorem majorityCount_update_add_one_voter1 :
    majorityCount (Function.update cycleP 1 (cycleP 0)) a b =
      majorityCount cycleP a b + 1 :=
  majorityCount_update_add_one
    (by simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb])
    (by simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb])

/-- Numeric check: 2+1=3. -/
theorem majorityCount_update_add_one_voter1_num :
    majorityCount (Function.update cycleP 1 (cycleP 0)) a b = 3 := by
  rw [majorityCount_update_add_one_voter1, majorityCount_cycleP_ab]

/-- **`majorityCount_update_le_of_not_lt`.** Switching voter 1 to `unanimousQ`'s ballot (c≻b≻a,
u=[0,1,2]), which does NOT rank a≻b (u(a)=0 < u(b)=1 → b≻a), does not raise the a-over-b count. -/
theorem majorityCount_update_le_voter1_to_Q :
    majorityCount (Function.update cycleP 1
      (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ))) a b ≤
      majorityCount cycleP a b :=
  majorityCount_update_le_of_not_lt (by simp [preferenceOfUtilityIn_lt_iff, ha, hb])

/-! ### §7 Social order (socialLE / socialLT / socialIndiff) -/

/-! Profile `unanimousQ` (Borda scores: A=0, b=3, c=6): SocialLE  Q c a: TRUE  (0 ≤ 6) socialLT  Q
c a: TRUE  (0 < 6) socialLE  Q a c: FALSE (6 ≤ 0 is false) socialIndiff Q a a: TRUE  (reflexivity)
socialIndiff Q b a: FALSE (3 ≠ 0) -/

private abbrev borda3SWF : WelfareFunction (Fin 3) (Fin 3) :=
  bordaWelfareFunction (Voter := Fin 3) (Alt := Fin 3)

/-- **`socialLE` positive check.** Society weakly prefers `c` to `a` under unanimousQ. -/
theorem bordaSWF_socialLE_Q_ca : borda3SWF.socialLE unanimousQ c a := by
  change (bordaRel unanimousQ).le c a
  rw [bordaRel, preferenceOfUtilityIn_le_iff, Q_bordaScore_a, Q_bordaScore_c]; norm_num

/-- **`socialLT` positive check.** Society strictly prefers `c` to `a` (6 > 0). -/
theorem bordaSWF_socialLT_Q_ca : borda3SWF.socialLT unanimousQ c a := by
  change (bordaRel unanimousQ).lt c a
  rw [bordaRel, preferenceOfUtilityIn_lt_iff, Q_bordaScore_a, Q_bordaScore_c]; norm_num

/-- **`socialLT` for b-vs-a.** Society strictly prefers `b` to `a` (3 > 0). -/
theorem bordaSWF_socialLT_Q_ba : borda3SWF.socialLT unanimousQ b a := by
  change (bordaRel unanimousQ).lt b a
  rw [bordaRel, preferenceOfUtilityIn_lt_iff, Q_bordaScore_a, Q_bordaScore_b]; norm_num

/-- **`socialLE` negative check.** Society does NOT weakly prefer `a` to `c`. -/
theorem bordaSWF_socialLE_Q_ac_false : ¬ borda3SWF.socialLE unanimousQ a c := by
  change ¬ (bordaRel unanimousQ).le a c
  rw [bordaRel, preferenceOfUtilityIn_le_iff, Q_bordaScore_a, Q_bordaScore_c]; norm_num

/-- **`socialIndiff` reflexivity check.** Society is indifferent between any alternative and itself.
This is a tautology (`a ~ a` for *any* preference); the *nontrivial* tie is exercised next. -/
theorem bordaSWF_socialIndiff_Q_aa : borda3SWF.socialIndiff unanimousQ a a :=
  PreferenceRel.indiff_refl (bordaRel unanimousQ) a

/-- **`socialIndiff` nontrivial-tie check.** On the Condorcet cycle `cycleP`, Borda *ties* the
distinct alternatives `a` and `b` (both score 3, `cycleP_bordaScore_a = cycleP_bordaScore_b`), so
society is genuinely indifferent between two *different* alternatives — not the trivial `a ~ a`. A
broken `socialIndiff` (or a Borda-score miscount) would fail here even though it would survive the
reflexivity check above. -/
theorem bordaSWF_socialIndiff_cycleP_ab : borda3SWF.socialIndiff cycleP a b := by
  change (bordaRel cycleP).indiff a b
  rw [bordaRel, preferenceOfUtilityIn_indiff_iff, cycleP_bordaScore_a, cycleP_bordaScore_b]

/-- **`socialIndiff` negative check.** Society is NOT indifferent between `b` and `a` (Borda scores
3 ≠ 0). -/
theorem bordaSWF_socialIndiff_Q_ba_false : ¬ borda3SWF.socialIndiff unanimousQ b a := by
  change ¬ (bordaRel unanimousQ).indiff b a
  intro h
  rw [bordaRel, preferenceOfUtilityIn_indiff_iff, Q_bordaScore_a, Q_bordaScore_b] at h
  norm_num at h

/-! ### §8 Welfare-function axioms (StrongPareto / ParetoIndifference / Anonymity) -/

/-! **StrongPareto TRUE: BordaWelfareFunction.** Key sub-lemma: On the strict domain, if
`(Pi).le x y` then `bordaScoreOf(Pi, y) ≤ bordaScoreOf(Pi, x)`. Proof: Strictness gives a linear
order, so `R.le x y` either means `R.lt x y` (strict preference → score strictly higher by
`bordaScoreOf_lt_of_lt`) or `x = y` (indifference on strict pref → equality).

**ParetoIndifference TRUE: Voter-0 projection SWF (`projSWF3`).** If all voters are indifferent
between `x` and `y`, so is voter 0, and the projection SWF inherits voter 0's ballot.

**ParetoIndifference FALSE: Constant SWF (`constRankSWF`).** Build a profile where all voters are
indifferent between `a` and `b` (constant utility 0). The constant SWF always ranks `b ≻ a`
(utility = index, b=1 > 0=a), so it's not indifferent.

**Anonymity TRUE: BordaWelfareFunction.** Borda aggregate is
`bordaRel P = preferenceOfUtilityIn (bordaScore P)` where
`bordaScore P x = ∑ i, bordaScoreOf (P i) x`. A permutation reorders the sum; `Finset.sum_equiv`
gives invariance.

**Anonymity FALSE: Voter-0 projection SWF.** Swapping voters 0 and 1 in `cycleP` (where they have
different ballots) changes the aggregate from voter 0's ballot to voter 1's ballot, falsifying
anonymity. -/

/-- On the strict domain, weak preference implies Borda score dominance. -/
private lemma bordaScoreOf_le_of_le_strict {R : PreferenceRel (Fin 3)} (hR : StrictPref R)
    {x y : Fin 3} (h : R.le x y) :
    bordaScoreOf R y ≤ bordaScoreOf R x := by
  rcases eq_or_ne x y with rfl | hne
  · -- x = y: equal scores.
    exact le_refl _
  · -- x ≠ y, so strict pref gives x ≻ y or y ≻ x.
    rcases hR.lt_or_lt_of_ne hne with hlt | hlt
    · -- R.lt x y: strict, Borda score strictly increases.
      exact (bordaScoreOf_lt_of_lt R hlt).le
    · -- R.lt y x: means R.le y x ∧ ¬ R.le x y, which contradicts h.
      exact absurd h hlt.2

/-- **`StrongPareto` on `bordaWelfareFunction` — a test-only derivation.** If all voters weakly
prefer `x` to `y` and at least one strictly does, then `bordaScore P x > bordaScore P y`, so
`bordaRel P` strictly ranks `x` above `y`.

Note: this is *not* an existing exported Econlib declaration — `BordaProperties.lean` currently
exports only `bordaWelfareFunction.WeakPareto` and `bordaWelfareFunction.nonDictatorship`. This
proof lives in the test namespace as a derivation; promoting it to the library is tracked in
`backlog/sc-borda-properties-strongpareto-anonymity.md`. -/
theorem bordaWelfareFunction_StrongPareto :
    StrongPareto (bordaWelfareFunction (Voter := Fin 3) (Alt := Fin 3)) := by
  intro PP hPP x y hle hlt
  rw [show bordaWelfareFunction.aggregate PP = bordaRel PP from rfl,
    bordaRel, preferenceOfUtilityIn_lt_iff]
  simp only [bordaScore]
  obtain ⟨i₀, hlt₀⟩ := hlt
  apply Finset.sum_lt_sum
  · intro i _
    exact bordaScoreOf_le_of_le_strict (mem_strictDomain.mp hPP i) (hle i)
  · exact ⟨i₀, Finset.mem_univ _, bordaScoreOf_lt_of_lt (PP i₀) hlt₀⟩

/-- Concrete exercise: StrongPareto on unanimousQ for pair (c, a). -/
theorem bordaSWF_StrongPareto_Q_ca :
    borda3SWF.socialLT unanimousQ c a :=
  bordaWelfareFunction_StrongPareto unanimousQ (mem_strictDomain.mpr unanimousQ_isStrict) c a
    (fun i => by simp [unanimousQ, preferenceOfUtilityIn_le_iff, ha, hc])
    ⟨0, by simp [unanimousQ, preferenceOfUtilityIn_lt_iff, ha, hc]⟩

/-- A voter-0 projection SWF on `Fin 3`. -/
private def projSWF3 : WelfareFunction (Fin 3) (Fin 3) where
  domain := Set.univ
  aggregate := fun PP => PP 0

/-- **`ParetoIndifference` TRUE on `projSWF3`.** If all voters are indifferent between `x` and `y`,
voter 0 is indifferent too, and `projSWF3` inherits voter 0's ballot. -/
-- `_PP`, `_x`, `_y`: signature binders required by `ParetoIndifference`; unused in proof.
theorem projSWF3_paretoIndifference : ParetoIndifference projSWF3 :=
  fun _PP _ _x _y hindiff => hindiff 0

/-- A constant SWF that always ranks by alternative index (b=1 ≻ a=0). -/
private def constRankSWF : WelfareFunction (Fin 3) (Fin 3) where
  domain := Set.univ
  aggregate := fun _ => preferenceOfUtilityIn (fun x : Fin 3 => (x : ℕ))

/-- **`ParetoIndifference` FALSE on `constRankSWF`.** Build a profile where all voters are
indifferent between `a=0` and `b=1` (constant utility 0). The constant SWF always ranks `b ≻ a`
(index 1 > 0), so it is NOT indifferent — ParetoIndifference fails. -/
theorem constRankSWF_not_ParetoIndifference : ¬ ParetoIndifference constRankSWF := by
  intro h
  -- Profile where all voters use constant utility 0 (everyone indifferent everywhere).
  let PP : Profile (Fin 3) (Fin 3) := fun _ => preferenceOfUtilityIn (fun _ : Fin 3 => 0)
  have hindiff : ∀ i : Fin 3, (PP i).indiff a b := by
    intro _i; simp [PP, preferenceOfUtilityIn_indiff_iff]
  have hsoc := h PP (Set.mem_univ _) a b hindiff
  -- constRankSWF says b ≻ a via index: the aggregate's `.le a b` = (b_idx ≤ a_idx) = false.
  simp only [constRankSWF, PreferenceRel.indiff, preferenceOfUtilityIn_le_iff] at hsoc
  -- hsoc = (↑b ≤ ↑a ∧ ↑a ≤ ↑b) where a=0, b=1, so hsoc.1 : 1 ≤ 0 is false.
  exact absurd hsoc.1 (by norm_num)

/-- **`WelfareFunction.Anonymity` on `bordaWelfareFunction` — a test-only derivation.** Permuting
voters reorders the Borda sum, leaving the total and hence `bordaRel` unchanged.

Note: as with `bordaWelfareFunction_StrongPareto`, this is *not* an existing exported Econlib
declaration; it is derived here in the test namespace. Promotion to `BordaProperties.lean` is
tracked in `backlog/sc-borda-properties-strongpareto-anonymity.md`. -/
theorem bordaWelfareFunction_Anonymity :
    (bordaWelfareFunction (Voter := Fin 3) (Alt := Fin 3)).Anonymity := by
  intro PP _ σ _
  -- The aggregate is `bordaRel`, so we need `bordaRel (PP ∘ σ) = bordaRel PP`.
  change bordaRel (PP ∘ σ) = bordaRel PP
  -- Both are `preferenceOfUtilityIn (bordaScore ·)`, so it suffices that
  -- `bordaScore (PP ∘ σ) = bordaScore PP` pointwise.
  suffices h : ∀ x, bordaScore (PP ∘ σ) x = bordaScore PP x by
    simp only [bordaRel, h]
  intro x
  simp only [bordaScore, Function.comp]
  exact Finset.sum_equiv σ (by simp) (by simp)

/-- **`WelfareFunction.Anonymity` FALSE on `projSWF3`.** Swapping voters 0 and 1 in `cycleP`
(different ballots: Voter 0 has a≻b≻c, voter 1 has b≻c≻a) changes the aggregate from voter 0's
ballot to voter 1's ballot. -/
theorem projSWF3_not_Anonymity : ¬ projSWF3.Anonymity := by
  intro h
  have heq := h cycleP (Set.mem_univ _) (Equiv.swap 0 1) (Set.mem_univ _)
  -- heq: projSWF3.aggregate (cycleP ∘ Equiv.swap 0 1) = projSWF3.aggregate cycleP
  -- Before: aggregate cycleP = cycleP 0  (voter 0: a≻b≻c)
  -- After:  aggregate (cycleP ∘ swap 0 1) = (cycleP ∘ swap 0 1) 0 = cycleP (swap 0 1 0) = cycleP 1
  -- Voter 0 has a≻b≻c so (cycleP 0).lt a b is TRUE.
  -- Voter 1 has b≻c≻a so (cycleP 1).lt a b is FALSE.
  have h0_ab : (cycleP 0).lt a b := by
    simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb]
  -- After swap, the aggregate is cycleP 1.
  have h_after : projSWF3.aggregate (cycleP ∘ Equiv.swap (0 : Fin 3) 1) = cycleP 1 := by
    simp [projSWF3, Function.comp, Equiv.swap_apply_left]
  -- Before swap, the aggregate is cycleP 0.
  have h_before : projSWF3.aggregate cycleP = cycleP 0 := rfl
  -- Combining: cycleP 1 = cycleP 0, so (cycleP 1).lt a b is TRUE.
  have h10 : cycleP 1 = cycleP 0 := by rw [← h_after, heq, h_before]
  -- But (cycleP 1).lt a b is FALSE: voter 1 has b≻c≻a, u(a)=0 < u(b)=2 means b≻a not a≻b.
  have h1_not_ab : ¬ (cycleP 1).lt a b := by
    simp [cycleP, utilP, preferenceOfUtilityIn_lt_iff, ha, hb]
  exact h1_not_ab (h10 ▸ h0_ab)

end EconlibTest.SocialChoice.Rules

end
