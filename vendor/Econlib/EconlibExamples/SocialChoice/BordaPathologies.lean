import Mathlib
import Econlib

/-!
# Pathologies of the Borda Count: It Violates IIA and the Condorcet Criterion

The **Borda count** — each voter awards `card − 1` points to their top alternative, `card − 2` to
the next, down to `0` for the bottom, and society ranks by total points — is the canonical
*positional* voting rule, championed by Jean-Charles de Borda in the 1780s against Condorcet's
pairwise method. It is appealing (it uses the whole ranking, not just the top choice) but it fails
two properties social choice cares about, and this file exhibits both failures on concrete
electorates. The IIA failure (Part 1) is the Arrow-relevant one — it is precisely why Borda, a
non-dictatorial Paretian rule, does not evade Arrow's impossibility theorem. The Condorcet
failure (Part 2) is a separate defect, about pairwise majority rather than Arrow's axioms.

## 1. Borda violates Independence of Irrelevant Alternatives (IIA)

Arrow's **IIA** demands that society's relative ranking of `x` and `y` depend only on how each voter
ranks `x` against `y` — not on where some third, "irrelevant" alternative `z` sits. Borda violates
this because moving `z` changes the points `x` and `y` collect even when no voter changes their
`x`-vs-`y` opinion.

We use two voters over `Alt = {x, y, z} = {0, 1, 2}`. In both profiles voter `0` ranks `x ≻ y` and
voter `1` ranks `y ≻ x` — the `x`-vs-`y` pattern is identical across the two profiles. Only `z`
moves:

  * `iiaP`: voter 0 `x ≻ z ≻ y`, voter 1 `y ≻ x ≻ z`.  Borda points `x = 2+1 = 3 > y = 0+2 = 2`,
    so society ranks `x ≻ y`.
  * `iiaQ`: voter 0 `z ≻ x ≻ y`, voter 1 `y ≻ z ≻ x`.  Borda points `x = 1+0 = 1 < y = 0+2 = 2`,
    so society ranks `y ≻ x`.

Same `x`-vs-`y` opinions, opposite social verdict: IIA fails.

## 2. Borda violates the Condorcet criterion

A **Condorcet winner** beats every rival in a pairwise majority. The *Condorcet criterion* asks a
rule to elect such a winner when one exists. Borda can override it. We use five voters over
`{x, y, z} = {0, 1, 2}`:

  * 3 voters: `x ≻ y ≻ z`,
  * 2 voters: `y ≻ z ≻ x`.

Here `x` beats `y` (3 to 2) and beats `z` (3 to 2), so `x` is the Condorcet winner. But Borda points
are `x = 3·2 + 2·0 = 6` and `y = 3·1 + 2·2 = 7`: Borda strictly prefers `y` to the Condorcet winner
`x`. A centrist `y`, never anyone's last choice, accumulates more points than the majority's
favorite.

## Main definitions and theorems

- `iiaP`, `iiaQ : Profile (Fin 2) (Fin 3)` — the two IIA-witness profiles.
- `borda_not_IIA : ¬ (bordaWelfareFunction (Voter := Fin 2) (Alt := Fin 3)).IIA`.
- `condP : Profile (Fin 5) (Fin 3)` — the Condorcet-criterion-witness profile.
- `condorcet_winner_x : CondorcetWinner condP 0` — `x` beats every rival pairwise.
- `borda_overrides_condorcet : (bordaRel condP).lt 1 0` — yet Borda strictly ranks `y` above `x`.
- `borda_violates_condorcet : CondorcetWinner condP 0 ∧ (bordaRel condP).lt 1 0` — the two together.
- `borda_winners_exclude_condorcet_winner` — the choice-rule form: the Borda winner set
  `scoreArgmax (bordaScore condP)` equals `{y}`, so the Condorcet winner `x` is not a Borda winner.
- `resoluteBorda_elects_non_condorcet` — the canonical resolute Borda rule selects `y = 1` on
  `condP`, together with `CondorcetWinner condP 0` and `0 ≠ 1`, so the elected alternative is
  provably the non-Condorcet winner.

The last two upgrade the failure from a statement about the social *ranking* (`bordaRel`) to one
about the actual *choice* (winner set / resolute selection), which is what "Borda fails the
Condorcet criterion" properly means.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.BordaPathologies

open Econlib.Preferences Econlib.SocialChoice

/-- Three alternatives `x = 0`, `y = 1`, `z = 2`. -/
abbrev Alt := Fin 3

-- ===========================================================================
-- Part 1: Borda violates IIA
-- ===========================================================================

/-- Two voters for the IIA witness. -/
abbrev Voter₂ := Fin 2

/-- Profile `iiaP`: voter 0 ranks `x ≻ z ≻ y`, voter 1 ranks `y ≻ x ≻ z`. (Utilities index the
alternatives `x = 0, y = 1, z = 2`; higher is more preferred.) -/
def iiaP : Profile Voter₂ Alt :=
  ![ preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ),   -- voter 0: x ≻ z ≻ y
     preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ) ]  -- voter 1: y ≻ x ≻ z

/-- Profile `iiaQ`: voter 0 ranks `z ≻ x ≻ y`, voter 1 ranks `y ≻ z ≻ x`. Each voter's `x`-vs-`y`
order is unchanged from `iiaP` (voter 0 still `x ≻ y`, voter 1 still `y ≻ x`); only `z` moved. -/
def iiaQ : Profile Voter₂ Alt :=
  ![ preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ),   -- voter 0: z ≻ x ≻ y
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ) ]  -- voter 1: y ≻ z ≻ x

/-- Both IIA-witness profiles lie in the strict domain: distinct integer utilities make every
voter's ranking strict. -/
private lemma iiaP_isStrict : Profile.IsStrict iiaP := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

private lemma iiaQ_isStrict : Profile.IsStrict iiaQ := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

/-- Every voter ranks `x = 0` against `y = 1` identically in `iiaP` and `iiaQ`: voter 0 strictly
prefers `x` in both, voter 1 strictly prefers `y` in both. Only the irrelevant alternative `z`
moved. This is the IIA hypothesis for the pair `{x, y}`. -/
private lemma iia_agree (i : Voter₂) :
    ((iiaP i).le 0 1 ↔ (iiaQ i).le 0 1) ∧ ((iiaP i).le 1 0 ↔ (iiaQ i).le 1 0) := by
  fin_cases i <;>
    exact ⟨by simp [iiaP, iiaQ, preferenceOfUtilityIn_le_iff],
      by simp [iiaP, iiaQ, preferenceOfUtilityIn_le_iff]⟩

/-- Borda scores in `iiaP`: `x = 0` collects `2 + 1 = 3`, `y = 1` collects `0 + 2 = 2`. -/
private lemma iiaP_bordaScore_x : bordaScore iiaP 0 = 3 := by
  rw [bordaScore_eq_sum_card iiaP 0 ![{1, 2}, {2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [iiaP, preferenceOfUtilityIn_lt_iff])]
  decide

private lemma iiaP_bordaScore_y : bordaScore iiaP 1 = 2 := by
  rw [bordaScore_eq_sum_card iiaP 1 ![∅, {0, 2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [iiaP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores in `iiaQ`: `x = 0` collects `1 + 0 = 1`, `y = 1` collects `0 + 2 = 2`. -/
private lemma iiaQ_bordaScore_x : bordaScore iiaQ 0 = 1 := by
  rw [bordaScore_eq_sum_card iiaQ 0 ![{1}, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [iiaQ, preferenceOfUtilityIn_lt_iff])]
  decide

private lemma iiaQ_bordaScore_y : bordaScore iiaQ 1 = 2 := by
  rw [bordaScore_eq_sum_card iiaQ 1 ![∅, {0, 2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [iiaQ, preferenceOfUtilityIn_lt_iff])]
  decide

/-- **Borda violates IIA.** The Borda welfare function's social ranking of `{x, y}` flips between
`iiaP` (where `x ≻ y`) and `iiaQ` (where `y ≻ x`) even though every voter ranks `x` against `y`
identically in the two profiles — only the irrelevant alternative `z` moved. Hence Borda fails
Arrow's Independence of Irrelevant Alternatives. -/
theorem borda_not_IIA :
    ¬ (bordaWelfareFunction (Voter := Voter₂) (Alt := Alt)).IIA := by
  intro hIIA
  -- Instantiate IIA at the witness pair: same `{x,y}` opinions force agreement on `x` vs `y`.
  have hmemP : iiaP ∈ (bordaWelfareFunction (Voter := Voter₂) (Alt := Alt)).domain :=
    mem_strictDomain.mpr iiaP_isStrict
  have hmemQ : iiaQ ∈ (bordaWelfareFunction (Voter := Voter₂) (Alt := Alt)).domain :=
    mem_strictDomain.mpr iiaQ_isStrict
  have hsame := (hIIA iiaP iiaQ hmemP hmemQ 0 1 iia_agree).1
  -- Society ranks `x ≽ y` under `iiaP` (scores `3 ≥ 2`) but not under `iiaQ` (scores `1 < 2`).
  have hP : (bordaRel iiaP).le 0 1 := by
    rw [bordaRel, preferenceOfUtilityIn_le_iff, iiaP_bordaScore_x, iiaP_bordaScore_y]; norm_num
  have hQ : ¬ (bordaRel iiaQ).le 0 1 := by
    rw [bordaRel, preferenceOfUtilityIn_le_iff, iiaQ_bordaScore_x, iiaQ_bordaScore_y]; norm_num
  exact hQ (hsame.mp hP)

-- ===========================================================================
-- Part 2: Borda violates the Condorcet criterion
-- ===========================================================================

/-- Five voters for the Condorcet witness. -/
abbrev Voter₅ := Fin 5

/-- Profile `condP`: three voters rank `x ≻ y ≻ z` and two rank `y ≻ z ≻ x`. Alternative `x = 0`
is the Condorcet winner (beating `y` and `z`, 3 to 2), but `y = 1` is the Borda winner. -/
def condP : Profile Voter₅ Alt :=
  ![ preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 0: x ≻ y ≻ z
     preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 1: x ≻ y ≻ z
     preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 2: x ≻ y ≻ z
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ),   -- voter 3: y ≻ z ≻ x
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ) ]  -- voter 4: y ≻ z ≻ x

/-- `x = 0` is a Condorcet winner of `condP`: it beats `y` and `z` in pairwise majority votes
(three voters to two in each case). -/
theorem condorcet_winner_x : CondorcetWinner condP 0 := by
  -- The three `x ≻ y ≻ z` voters `{0,1,2}` favor `x` over either rival; the two `y ≻ z ≻ x` voters
  -- `{3,4}` favor each rival over `x`. So `x` beats both `y` and `z` by `3` to `2`.
  intro y hy
  fin_cases y
  · exact absurd rfl hy            -- `y = 0 = x` is excluded by `hy`
  · -- `x = 0` versus `y = 1`: forward set `{0,1,2}`, reverse set `{3,4}`.
    change pairwiseMajority condP 0 1
    have hfwd : majorityCount condP 0 1 = 3 :=
      majorityCount_eq_card condP 0 1 {0, 1, 2} (by intro i; fin_cases i <;> simp [condP])
    have hrev : majorityCount condP 1 0 = 2 :=
      majorityCount_eq_card condP 1 0 {3, 4} (by intro i; fin_cases i <;> simp [condP])
    rw [pairwiseMajority, hrev, hfwd]; norm_num
  · -- `x = 0` versus `z = 2`: forward set `{0,1,2}`, reverse set `{3,4}`.
    change pairwiseMajority condP 0 2
    have hfwd : majorityCount condP 0 2 = 3 :=
      majorityCount_eq_card condP 0 2 {0, 1, 2} (by intro i; fin_cases i <;> simp [condP])
    have hrev : majorityCount condP 2 0 = 2 :=
      majorityCount_eq_card condP 2 0 {3, 4} (by intro i; fin_cases i <;> simp [condP])
    rw [pairwiseMajority, hrev, hfwd]; norm_num

/-- Total Borda score of `x = 0` is `6 = 3·2 + 2·0`. -/
private lemma cond_bordaScore_x : bordaScore condP 0 = 6 := by
  rw [bordaScore_eq_sum_card condP 0 ![{1, 2}, {1, 2}, {1, 2}, ∅, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [condP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Total Borda score of `y = 1` is `7 = 3·1 + 2·2`. -/
private lemma cond_bordaScore_y : bordaScore condP 1 = 7 := by
  rw [bordaScore_eq_sum_card condP 1 ![{2}, {2}, {2}, {0, 2}, {0, 2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [condP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Yet the Borda rule strictly ranks `y = 1` above the Condorcet winner `x = 0`: Borda points are
`x = 6` and `y = 7`. -/
theorem borda_overrides_condorcet : (bordaRel condP).lt 1 0 := by
  -- `bordaRel` ranks by total Borda score, so `y ≻ x` reduces to `score x < score y`, i.e. `6 < 7`.
  rw [bordaRel, preferenceOfUtilityIn_lt_iff, cond_bordaScore_x, cond_bordaScore_y]
  norm_num

/-- **Borda violates the Condorcet criterion.** The profile `condP` has a Condorcet winner `x`, yet
the Borda count strictly prefers `y` to `x` — so Borda does not, in general, elect the Condorcet
winner. -/
theorem borda_violates_condorcet :
    CondorcetWinner condP 0 ∧ (bordaRel condP).lt 1 0 :=
  ⟨condorcet_winner_x, borda_overrides_condorcet⟩

-- ===========================================================================
-- The choice-rule failure: the Borda winner set excludes the Condorcet winner
-- ===========================================================================

/-- Total Borda score of `z = 2` is `2 = 3·0 + 2·1`. -/
private lemma cond_bordaScore_z : bordaScore condP 2 = 2 := by
  rw [bordaScore_eq_sum_card condP 2 ![∅, ∅, ∅, {0}, {0}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [condP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- The Condorcet-witness profile is strict (distinct integer utilities), so it lies in the strict
domain on which the canonical scoring/resolute Borda rules are defined. -/
private lemma condP_isStrict : Profile.IsStrict condP := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

/-- `y = 1` strictly out-scores every other alternative under Borda: `x = 6`, `z = 2`, both below
`y = 7`. This is the strict-maximizer fact behind the winner-set and resolute-winner theorems. -/
private lemma bordaScore_condP_strict_max :
    ∀ b : Alt, b ≠ 1 → bordaScore condP b < bordaScore condP 1 := by
  intro b hb
  fin_cases b
  · change bordaScore condP 0 < bordaScore condP 1
    rw [cond_bordaScore_x, cond_bordaScore_y]; norm_num   -- `x = 6 < 7`
  · exact absurd rfl hb                                    -- `b = y` is excluded
  · change bordaScore condP 2 < bordaScore condP 1
    rw [cond_bordaScore_z, cond_bordaScore_y]; norm_num   -- `z = 2 < 7`

/-- **The Borda winner set excludes the Condorcet winner.** Ranking by total Borda score, the unique
score-maximizer is `y = 1` (`scoreArgmax (bordaScore condP) = {1}`), so the Condorcet winner `x = 0`
is not a Borda winner. This is the choice-rule form of the Condorcet-criterion failure: not merely
that the social *ranking* puts `y` above `x`, but that the Borda *winner set* omits the Condorcet
winner entirely. -/
theorem borda_winners_exclude_condorcet_winner :
    scoreArgmax (bordaScore condP) = {1} ∧ (0 : Alt) ∉ scoreArgmax (bordaScore condP) := by
  have hargmax : scoreArgmax (bordaScore condP) = {1} := by
    ext a
    rw [mem_scoreArgmax, Finset.mem_singleton]
    constructor
    · -- A maximizer cannot score below `y`, so it must be `y`.
      intro hmax
      by_contra ha
      exact absurd (hmax 1) (not_le.mpr (bordaScore_condP_strict_max a ha))
    · -- `y` dominates every alternative, so it is a maximizer.
      rintro rfl b
      rcases eq_or_ne b 1 with rfl | hb
      · exact le_rfl
      · exact (bordaScore_condP_strict_max b hb).le
  exact ⟨hargmax, by rw [hargmax]; decide⟩

/-- **Resolute Borda elects the non-Condorcet winner.** The canonical resolute Borda rule
(`resoluteBorda`, rank by total Borda score and break ties lexicographically) selects `y = 1` on
`condP`, while the Condorcet winner is `x = 0` (`CondorcetWinner condP 0`) and `0 ≠ 1` — so the
elected alternative is provably not the Condorcet winner. The tie-break never fires here — `y` is
the *strict* top-scorer — so the selection is forced. -/
theorem resoluteBorda_elects_non_condorcet :
    (resoluteBorda (Voter := Voter₅)).winners condP = {1} ∧
      condP ∈ (resoluteBorda (Voter := Voter₅)).domain ∧
      CondorcetWinner condP 0 ∧ (0 : Alt) ≠ 1 := by
  refine ⟨?_, mem_strictDomain.mpr condP_isStrict, condorcet_winner_x, by decide⟩
  rw [resoluteBorda_winners,
    scoreWinner_eq_of_strict_max (bordaScore condP) (bordaScore condP) (fun _ => rfl)
      bordaScore_condP_strict_max]

end EconlibExamples.SocialChoice.BordaPathologies

end
