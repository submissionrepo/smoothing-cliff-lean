import Mathlib
import Econlib

/-!
# The Spoiler Effect: Plurality Can Elect the Condorcet Loser

**Plurality rule** ("first past the post") elects whichever alternative is the top choice of the
most voters. It is the most widely used voting rule in the world, and the most criticized: when
several similar candidates split a majority's vote, plurality can hand victory to a candidate the
same majority would reject head-to-head. This is the *spoiler effect* / vote-splitting, the engine
behind Duverger's law and perennial "third-party spoiler" debates.

This file exhibits the worst case on a concrete electorate, in both of its guises. Statically,
plurality elects the **Condorcet loser** — the alternative that loses every pairwise majority
contest — while the Condorcet winner is passed over entirely. Counterfactually, the spoiler is
real: delete candidate `C` from the race — provably changing no voter's `A`-vs-`B` opinion — and
the plurality winner flips from `A` to `B` (`spoiler_effect`).

Crucially, this electorate is **single-peaked** under the natural order `A < B < C`
(`condP_singlePeaked`), so Black's median-voter theorem applies and guarantees a Condorcet winner
(here `B`). Single-peakedness therefore does not immunize an electorate against the spoiler effect:
Black's theorem constrains pairwise majority, not plurality
(`singlePeaked_yet_plurality_elects_loser`).

## The model

Seven voters, `Voter := Fin 7`, choose among `Alt := {A, B, C} = {0, 1, 2}`. The electorate splits
into three blocs of strict rankings:

  * 3 voters: `A ≻ B ≻ C`,
  * 2 voters: `B ≻ C ≻ A`,
  * 2 voters: `C ≻ B ≻ A`.

`A` is the favorite of the largest bloc (3 voters), but `B` and `C` are both more broadly
acceptable — `A` is the last choice of the four voters who do not lead with it.

## The mathematics

**Plurality.** Top choices are `A` (3 voters), `B` (2 voters), `C` (2 voters), so the plurality
score of `A` is `3`, strictly more than `B`'s and `C`'s `2`. `A` is the unique plurality winner.

**Pairwise majorities.** Yet `A` loses every head-to-head:

  * `B` vs `A`: `B ≻ A` for the 4 voters in the last two blocs, `A ≻ B` for only 3 ⟹ `B` beats `A`.
  * `C` vs `A`: `C ≻ A` for the same 4 voters ⟹ `C` beats `A`.
  * `B` vs `C`: `B ≻ C` for the first two blocs (5 voters), `C ≻ B` for 2 ⟹ `B` beats `C`.

So `B` beats both `A` and `C`: **`B` is the Condorcet winner.** And `A` is beaten by both `B` and
`C`: **`A` is the Condorcet loser.** Plurality elects exactly the candidate a majority ranks
below every alternative.

**Single-peakedness does not rescue plurality.** Order the alternatives naturally as `A < B < C`.
Then every bloc is single-peaked (`condP_singlePeaked`): each ranking falls off monotonically on
both sides of its top choice — the `A`-bloc peaks at the left end `A`, the `C`-bloc at the right end
`C`, and the `B`-bloc at the interior point `B` (with `A` and `C` both ranked below `B`). So Black's
median-voter theorem (`Econlib.SocialChoice.exists_condorcetWinner_of_singlePeaked`) does apply
here — and it delivers exactly what it promises: a Condorcet winner, the median peak `B`
(`condorcet_winner_B`). What Black's theorem rules out is a *pairwise-majority* cycle; it says
nothing about *plurality*. Plurality can still elect the Condorcet loser `A` on this single-peaked
domain (`singlePeaked_yet_plurality_elects_loser`). The spoiler pathology is a failure of plurality,
not a failure of the single-peaked structure.

**The counterfactual.** Restrict the same electorate to the two-candidate race `{A, B}` —
formally, each ballot becomes the voter's `condP` utilities composed with the embedding
`keep : Fin 2 → Alt`, so `restricted_agrees` proves every `A`-vs-`B` comparison is literally
unchanged. The `C`-bloc's first-place votes transfer to `B`, the scores flip from
`A = 3 > B = 2 = C` to `A = 3 < B = 4`, and `B` becomes the unique winner
(`plurality_winner_without_C`). Candidate `C` never had a chance itself: it is a pure spoiler, and
`spoiler_effect` packages the full before/after verdict.

## Main definitions and theorems

- `condP : Profile (Fin 7) (Fin 3)` — the three-bloc electorate above.
- `plurality_winner_A : pluralityWinners condP = {0}` — `A` is the unique plurality winner.
- `condorcet_winner_B : CondorcetWinner condP 1` — `B` beats every rival pairwise.
- `A_is_condorcet_loser : pairwiseMajority condP 1 0 ∧ pairwiseMajority condP 2 0` — `A` loses to
  both `B` and `C`.
- `plurality_elects_condorcet_loser` — the bundled static verdict: `A` wins plurality, `B` is the
  Condorcet winner, and `A` loses every head-to-head — plurality fails the Condorcet criterion and
  elects the Condorcet loser.
- `condP_singlePeaked : (i : Voter) → SinglePeakedRel (condP i)` — every bloc is single-peaked under
  the natural order `A < B < C`, with peak equal to each voter's top pick.
- `black_delivers_condorcet_winner_B` — Black's median-voter theorem
  (`exists_condorcetWinner_of_singlePeaked`) applied to `condP_singlePeaked` returns a
  Condorcet winner, determined to be `B`; the cross-check that the prose claim is a real corollary.
- `singlePeaked_yet_plurality_elects_loser` — the corrected economic point: the domain is
  single-peaked (so Black's theorem applies and yields the Condorcet winner `B`), yet plurality
  still elects the Condorcet loser `A`. Black constrains pairwise majority, not plurality.
- `restrictedP : Profile (Fin 7) (Fin 2)` — the same electorate with `C` deleted.
- `restricted_agrees` — deleting `C` provably changes no voter's `A`-vs-`B` opinion.
- `plurality_winner_without_C : pluralityWinners restrictedP = {1}` — without `C`, `B` wins.
- `spoiler_effect` — the counterfactual verdict: `A` wins with `C` in the race, `B` wins without,
  on provably identical `A`-vs-`B` ballots.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.PluralitySpoiler

open Econlib.Preferences Econlib.SocialChoice

/-- Seven voters. -/
abbrev Voter := Fin 7

/-- Three candidates `A = 0`, `B = 1`, `C = 2`. The `LinearOrder` on `Fin 3` is what lets us speak
of single-peakedness under the natural order `A < B < C` (`condP_singlePeaked`); plurality itself
breaks no ties — `pluralityWinners` returns the full set of score-maximizers (here a singleton). -/
abbrev Alt := Fin 3

/-- The three-bloc profile: voters `0,1,2` rank `A ≻ B ≻ C`; voters `3,4` rank `B ≻ C ≻ A`; voters
`5,6` rank `C ≻ B ≻ A`. Utilities index `A = 0, B = 1, C = 2`, higher being more preferred. -/
def condP : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 0: A ≻ B ≻ C
     preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 1: A ≻ B ≻ C
     preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 2: A ≻ B ≻ C
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ),   -- voter 3: B ≻ C ≻ A
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ),   -- voter 4: B ≻ C ≻ A
     preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ),   -- voter 5: C ≻ B ≻ A
     preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ) ]  -- voter 6: C ≻ B ≻ A

/-- The integer utility vector backing voter `i`'s ranking in `condP`. Reading `condP i` off this
table lets every per-voter computation reduce to arithmetic on `util i`. -/
private def util : Voter → Alt → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: A ≻ B ≻ C
     ![2, 1, 0],   -- voter 1: A ≻ B ≻ C
     ![2, 1, 0],   -- voter 2: A ≻ B ≻ C
     ![0, 2, 1],   -- voter 3: B ≻ C ≻ A
     ![0, 2, 1],   -- voter 4: B ≻ C ≻ A
     ![0, 1, 2],   -- voter 5: C ≻ B ≻ A
     ![0, 1, 2] ]  -- voter 6: C ≻ B ≻ A

/-- `condP i` is the ordinal preference induced by `util i`. -/
private lemma condP_eq (i : Voter) : condP i = preferenceOfUtilityIn (util i) := by
  fin_cases i <;> rfl

/-- Voter `i` strictly prefers `x` to `y` in `condP` iff `util i y < util i x`. -/
private lemma lt_iff (i : Voter) (x y : Alt) : (condP i).lt x y ↔ util i y < util i x := by
  rw [condP_eq]; exact preferenceOfUtilityIn_lt_iff (util i) x y

/-- `majorityCount condP x y` equals the cardinality of any explicit voter set capturing "strictly
prefers `x` to `y`" in `condP`. -/
private lemma count_eq (x y : Alt) (s : Finset Voter)
    (h : ∀ i : Voter, (condP i).lt x y ↔ i ∈ s) : majorityCount condP x y = s.card :=
  majorityCount_eq_card condP x y s h

/-- Top pick in `condP` per voter: `A`-bloc → `0`, `B`-bloc → `1`, `C`-bloc → `2`. -/
private lemma topPick_condP (i : Voter) :
    topPick (condP i) = (![0, 0, 0, 1, 1, 2, 2] : Voter → Alt) i := by
  rw [condP_eq]
  fin_cases i <;>
    · refine topPick_eq (strictPref_preferenceOfUtilityIn (by decide)) ?_
      simp only [preferenceOfUtilityIn_le_iff]
      decide

/-- `pluralityScore condP a` equals the cardinality of any explicit voter set capturing "top pick
is `a`" in `condP`. -/
private lemma score_eq (a : Alt) (s : Finset Voter)
    (h : ∀ i : Voter, topPick (condP i) = a ↔ i ∈ s) : pluralityScore condP a = s.card :=
  pluralityScore_eq_card condP a s h

-- ===========================================================================
-- Plurality elects A
-- ===========================================================================

/-- **`A` is the unique plurality winner.** Its plurality score is `3` (the three voters who lead
with `A`), strictly more than the `2` apiece collected by `B` and `C`. -/
theorem plurality_winner_A : pluralityWinners condP = {0} := by
  have sA : pluralityScore condP 0 = 3 :=
    score_eq 0 {0, 1, 2} (by intro i; fin_cases i <;> simp [topPick_condP])
  have sB : pluralityScore condP 1 = 2 :=
    score_eq 1 {3, 4} (by intro i; fin_cases i <;> simp [topPick_condP])
  have sC : pluralityScore condP 2 = 2 :=
    score_eq 2 {5, 6} (by intro i; fin_cases i <;> simp [topPick_condP])
  ext a; rw [Finset.mem_singleton, mem_pluralityWinners]
  fin_cases a
  · exact ⟨fun _ => rfl, fun _ b => by fin_cases b <;> simp [sA, sB, sC]⟩
  · exact ⟨fun h => absurd (h 0) (by simp [sA, sB]), fun h => absurd h (by decide)⟩
  · exact ⟨fun h => absurd (h 0) (by simp [sA, sC]), fun h => absurd h (by decide)⟩

-- ===========================================================================
-- B is the Condorcet winner, A the Condorcet loser
-- ===========================================================================

/-- **`B` is the Condorcet winner.** It beats `A` (four votes to three) and `C` (five votes to two)
in pairwise majority contests, so it defeats every rival head-to-head. -/
theorem condorcet_winner_B : CondorcetWinner condP 1 := by
  have mBA : majorityCount condP 1 0 = 4 :=
    count_eq 1 0 {3, 4, 5, 6} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mAB : majorityCount condP 0 1 = 3 :=
    count_eq 0 1 {0, 1, 2} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mBC : majorityCount condP 1 2 = 5 :=
    count_eq 1 2 {0, 1, 2, 3, 4} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mCB : majorityCount condP 2 1 = 2 :=
    count_eq 2 1 {5, 6} (by intro i; fin_cases i <;> simp [lt_iff, util])
  intro y hy
  fin_cases y
  · -- `B` vs `A`
    change pairwiseMajority condP 1 0
    rw [pairwiseMajority, mAB, mBA]; norm_num
  · -- `y = B` is excluded by `hy : B ≠ B`
    exact absurd rfl hy
  · -- `B` vs `C`
    change pairwiseMajority condP 1 2
    rw [pairwiseMajority, mCB, mBC]; norm_num

/-- **`A` is the Condorcet loser.** Both `B` and `C` beat `A` in a pairwise majority (four votes to
three each), so `A` loses every head-to-head contest. -/
theorem A_is_condorcet_loser :
    pairwiseMajority condP 1 0 ∧ pairwiseMajority condP 2 0 := by
  have mBA : majorityCount condP 1 0 = 4 :=
    count_eq 1 0 {3, 4, 5, 6} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mAB : majorityCount condP 0 1 = 3 :=
    count_eq 0 1 {0, 1, 2} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mCA : majorityCount condP 2 0 = 4 :=
    count_eq 2 0 {3, 4, 5, 6} (by intro i; fin_cases i <;> simp [lt_iff, util])
  have mAC : majorityCount condP 0 2 = 3 :=
    count_eq 0 2 {0, 1, 2} (by intro i; fin_cases i <;> simp [lt_iff, util])
  refine ⟨?_, ?_⟩
  · rw [pairwiseMajority, mAB, mBA]; norm_num
  · rw [pairwiseMajority, mAC, mCA]; norm_num

-- ===========================================================================
-- The spoiler verdict
-- ===========================================================================

/-- **Plurality elects the Condorcet loser.** The unique plurality winner is `A`; the Condorcet
winner is `B ≠ A`; and `A` is beaten by both rivals head-to-head — the full Condorcet-loser
verdict in one statement. Plurality therefore violates the Condorcet criterion in the strongest
possible way. -/
theorem plurality_elects_condorcet_loser :
    pluralityWinners condP = {0} ∧ CondorcetWinner condP 1 ∧
      pairwiseMajority condP 1 0 ∧ pairwiseMajority condP 2 0 :=
  ⟨plurality_winner_A, condorcet_winner_B, A_is_condorcet_loser.1, A_is_condorcet_loser.2⟩

-- ===========================================================================
-- The domain is single-peaked, so Black's theorem applies
-- ===========================================================================

/-- Per-voter single-peakedness of `condP` under the natural order `A < B < C` on `Fin 3`. Each
bloc's ranking declines monotonically away from its peak: the `A`-bloc peaks at the left end `A`,
the `C`-bloc at the right end `C`, and the `B`-bloc at the interior point `B`. The peak vector is
exactly each voter's `topPick` (`topPick_condP`). -/
def condP_singlePeaked (i : Voter) : SinglePeakedRel (condP i) where
  peak := (![0, 0, 0, 1, 1, 2, 2] : Voter → Alt) i
  left_of_peak x y h1 h2 := by
    -- Each `(bloc, x < y ≤ peak)` reduces to a `util` comparison; live pairs hold, the rest are
    -- vacuous because the order constraint on this bloc's peak fails.
    fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all [lt_iff, util]
  right_of_peak x y h1 h2 := by
    fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all [lt_iff, util]

/-- **Black's theorem applies: it delivers the Condorcet winner `B`.** Because `condP` is
single-peaked (`condP_singlePeaked`) and the electorate `Fin 7` is odd and nonempty, the library's
`exists_condorcetWinner_of_singlePeaked` fires and produces a Condorcet winner; that winner is
determined to be `B = 1` by the directly-proved `condorcet_winner_B` (two distinct Condorcet
winners would each beat the other, impossible). This is the formal content behind the prose claim
that Black's median-voter theorem "applies and delivers `B`" — the cross-check analogous to
`ArrowDictatorship.arrow_recovers_dictator_zero`. -/
theorem black_delivers_condorcet_winner_B :
    ∃ m : Alt, CondorcetWinner condP m ∧ m = 1 := by
  obtain ⟨m, hm⟩ :=
    exists_condorcetWinner_of_singlePeaked condP_singlePeaked (by rw [Fintype.card_fin]; decide)
  refine ⟨m, hm, ?_⟩
  by_contra hne
  -- `m` and `B` would each be a Condorcet winner, so each beats the other — a contradiction.
  have h1 : pairwiseMajority condP m 1 := hm.beats (Ne.symm hne)
  have h2 : pairwiseMajority condP 1 m := condorcet_winner_B.beats hne
  rw [pairwiseMajority] at h1 h2
  omega

/-- **Single-peakedness does not save plurality.** `condP` is single-peaked under `A < B < C`
(`condP_singlePeaked`), so Black's median-voter theorem
(`Econlib.SocialChoice.exists_condorcetWinner_of_singlePeaked`) applies and guarantees a Condorcet
winner — here `B` (`condorcet_winner_B`). Yet plurality still elects the Condorcet loser `A`
(`plurality_winner_A`), beaten head-to-head by both `B` and `C`. Black's theorem constrains
*pairwise majority* — it rules out majority cycles and delivers a Condorcet winner — but it places
no constraint on *plurality*, which is exactly why the spoiler pathology survives even on a
single-peaked domain. The `Nonempty` wrapper records that the single-peaked witness
`condP_singlePeaked` exists while keeping the conjunction `Prop`-valued. -/
theorem singlePeaked_yet_plurality_elects_loser :
    Nonempty (∀ i, SinglePeakedRel (condP i))
      ∧ CondorcetWinner condP 1
      ∧ pluralityWinners condP = {0}
      ∧ pairwiseMajority condP 1 0 ∧ pairwiseMajority condP 2 0 :=
  ⟨⟨condP_singlePeaked⟩, condorcet_winner_B, plurality_winner_A,
    A_is_condorcet_loser.1, A_is_condorcet_loser.2⟩

-- ===========================================================================
-- The spoiler counterfactual: delete C and the plurality winner flips
-- ===========================================================================

/-- The embedding of the two-candidate race `{A, B}` into the full field `{A, B, C}`. -/
def keep : Fin 2 → Alt := Fin.castLE (by omega)

/-- `keep` is injective, so restricting along it preserves strictness. -/
private lemma keep_injective : Function.Injective keep :=
  (Fin.castLE_injective _)

/-- The C-free electorate: the same seven voters with the same ballots, restricted along the
embedding `keep : {A, B} ↪ {A, B, C}` (`Profile.restrict`). Each voter's `A`-vs-`B` opinion is
untouched by construction — `restricted_agrees` makes this formal. -/
def restrictedP : Profile Voter (Fin 2) :=
  Profile.restrict keep condP

/-- **Removing `C` changes nobody's `A`-vs-`B` opinion**: voter `i` ranks `x ≻ y` in the
two-candidate race iff they rank the corresponding candidates that way in the full race. The two
profiles are provably the same electorate, not merely similar-looking tables — a direct instance of
the library's restriction-agreement lemma `Profile.restrict_lt_iff`. -/
theorem restricted_agrees (i : Voter) (x y : Fin 2) :
    (restrictedP i).lt x y ↔ (condP i).lt (keep x) (keep y) :=
  Profile.restrict_lt_iff keep condP i x y

/-- Each restricted ballot is strict — `keep` is injective, so the restriction of every (strict)
`condP` ballot stays strict (`StrictPref.comap`). -/
private lemma restrictedP_strict (i : Voter) : StrictPref (restrictedP i) := by
  rw [restrictedP, Profile.restrict, condP_eq i]
  refine (strictPref_preferenceOfUtilityIn ?_).comap keep_injective
  fin_cases i <;> decide

/-- Top picks without `C`: the `A`-bloc still leads with `A`, while the `B`-bloc *and the former
`C`-bloc* now lead with `B` — the anti-`A` vote is no longer split. -/
private lemma topPick_restrictedP (i : Voter) :
    topPick (restrictedP i) = (![0, 0, 0, 1, 1, 1, 1] : Voter → Fin 2) i := by
  fin_cases i <;>
    · refine topPick_eq (restrictedP_strict _) ?_
      simp only [restrictedP, Profile.restrict, PreferenceRel.comap_le_iff, condP_eq,
        preferenceOfUtilityIn_le_iff]
      decide

/-- `pluralityScore restrictedP a` equals the cardinality of any explicit voter set capturing "top
pick is `a`" in `restrictedP`. -/
private lemma rscore_eq (a : Fin 2) (s : Finset Voter)
    (h : ∀ i : Voter, topPick (restrictedP i) = a ↔ i ∈ s) :
    pluralityScore restrictedP a = s.card :=
  pluralityScore_eq_card restrictedP a s h

/-- **Without the spoiler, `B` wins.** Restricted to `{A, B}`, the former `C`-bloc's first-place
votes transfer to `B`: scores become `A = 3 < B = 4`, and `B` is the unique plurality winner. -/
theorem plurality_winner_without_C : pluralityWinners restrictedP = {1} := by
  have sA : pluralityScore restrictedP 0 = 3 :=
    rscore_eq 0 {0, 1, 2} (by intro i; fin_cases i <;> simp [topPick_restrictedP])
  have sB : pluralityScore restrictedP 1 = 4 :=
    rscore_eq 1 {3, 4, 5, 6} (by intro i; fin_cases i <;> simp [topPick_restrictedP])
  ext a; rw [Finset.mem_singleton, mem_pluralityWinners]
  fin_cases a
  · exact ⟨fun h => absurd (h 1) (by simp [sA, sB]), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ b => by fin_cases b <;> simp [sA, sB]⟩

/-- **The spoiler effect, literally.** With `C` in the race the plurality winner is `A`; delete `C`
— provably changing no voter's `A`-vs-`B` opinion (`restricted_agrees`) — and the plurality winner
flips to `B`. `C` never stood a chance itself (its score `2` trails throughout): it is a pure
spoiler. -/
theorem spoiler_effect :
    pluralityWinners condP = {0} ∧ pluralityWinners restrictedP = {1} ∧
      ∀ i : Voter, ∀ x y : Fin 2, ((restrictedP i).lt x y ↔ (condP i).lt (keep x) (keep y)) :=
  ⟨plurality_winner_A, plurality_winner_without_C, restricted_agrees⟩

end EconlibExamples.SocialChoice.PluralitySpoiler

end
