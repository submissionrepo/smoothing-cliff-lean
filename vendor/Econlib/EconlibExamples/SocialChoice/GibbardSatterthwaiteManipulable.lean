import Mathlib
import Econlib

/-!
# Gibbard–Satterthwaite: Every Reasonable Voting Rule Is Manipulable

The Gibbard–Satterthwaite theorem is the strategic twin of Arrow's: any **resolute** social choice
rule on three or more alternatives that is **surjective** (every alternative can win) and
**non-dictatorial** must be **manipulable** — some voter, in some profile, can get a strictly better
outcome by misreporting their preferences. Strategy-proofness, surjectivity, and non-dictatorship
are mutually incompatible.

This file makes the conclusion concrete and formal: it builds a perfectly natural rule — the
**Borda count made resolute** by a lexicographic tie-break, on the strict domain — and connects it
to the theorem from both ends. From below, it exhibits an explicit, beneficial manipulation
(`resoluteBorda_not_strategyProof`). From above, it proves the rule resolute, surjective, and
**non-dictatorial**, so the library's `gibbard_satterthwaite` itself forces manipulability
(`gibbardSatterthwaite_guarantees_manipulation`): the displayed manipulation is not a lucky
accident but an instance of the theorem's guarantee.

## The model

Three voters `Voter := Fin 3` choose among three alternatives `Alt := {x, y, z} = {0, 1, 2}`. Every
*strict* profile is admissible — the Gibbard–Satterthwaite domain. `resoluteBorda` ranks
alternatives by total Borda score and returns the *lexicographically smallest* top-scorer as the
unique winner (the tie-break makes the rule resolute — exactly one winner on every profile).

## The manipulation

Voter `0`'s **true** preference is `x ≻ y ≻ z`. Consider the truthful profile

  * voter 0: `x ≻ y ≻ z`,
  * voter 1: `y ≻ x ≻ z`,
  * voter 2: `y ≻ x ≻ z`.

Borda scores are `x = 4`, `y = 5`, `z = 0`, so the sincere winner is **`y`** — voter 0's second
choice. Now voter 0 **buries** `y`, misreporting `x ≻ z ≻ y` (sinking `y` from second to last).
Against the unchanged ballots of voters 1 and 2 the scores become `x = 4`, `y = 4`, `z = 1`; the
`x`–`y` tie is broken lexicographically to **`x`**. Voter 0 has converted the outcome from `y` to
`x`, and `x` is voter 0's top choice: the misreport is strictly profitable. The rule is
not strategy-proof.

## The mathematics

`resoluteBorda` is a bona fide `ChoiceFunction` on `strictDomain`: its winner-set `{bordaWinner P}`
is always a singleton (`bordaWinner` is the `min'` of the nonempty set of Borda-maximizers), so the
rule is resolute. It is surjective (rank an alternative first unanimously — by a strict ballot —
and it wins). It is non-dictatorial: at `truthfulP` the winner `y` is not voter 0's weak top, and
at the split-tops profile `splitP` (scores `x = 4 > y = 3 > z = 2`) the winner `x` is neither
voter 1's nor voter 2's. The manipulation refutes strategy-proofness directly: the post-misreport
winner `x` is one voter 0 strictly prefers to every truthful winner (the only truthful winner being
`y`). Independently, `gibbard_satterthwaite` applied to the rule's resoluteness, surjectivity, and
non-dictatorship refutes strategy-proofness again — the formal version of "the theorem guarantees a
manipulation."

## Main definitions and theorems

- `resoluteBorda : ChoiceFunction (Fin 3) (Fin 3)` — Borda count with lexicographic tie-break, on
  the strict domain.
- `resoluteBorda_resolute : ∀ P ∈ resoluteBorda.domain, (resoluteBorda.winners P).Subsingleton`.
- `resoluteBorda_surjective : resoluteBorda.Surjective`.
- `truthful_winner_is_y : bordaWinner truthfulP = 1` — sincere voting elects `y`.
- `manipulated_winner_is_x : bordaWinner (Function.update truthfulP 0 buryY) = 0` — burying `y`
  elects `x`.
- `resoluteBorda_not_strategyProof : ¬ resoluteBorda.StrategyProof` — voter 0's misreport is a
  strictly profitable manipulation, so the rule is not strategy-proof.
- `resoluteBorda_not_dictatorial : ¬ ∃ i, resoluteBorda.IsDictator i` — no voter's ballot always
  tops the winner.
- `gibbardSatterthwaite_guarantees_manipulation : ¬ resoluteBorda.StrategyProof` — the same
  conclusion derived from the library's `gibbard_satterthwaite`: resolute + surjective +
  strategy-proof would force a dictator, which `resoluteBorda` does not have.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable

open Econlib.Preferences Econlib.SocialChoice

/-- Three voters. -/
abbrev Voter := Fin 3

/-- Three alternatives `x = 0`, `y = 1`, `z = 2`; the `LinearOrder` on `Fin 3` supplies the
lexicographic tie-break. -/
abbrev Alt := Fin 3

/-- The resolute Borda winner: the lexicographically smallest alternative of maximal Borda score.
A thin alias for the upstream `scoreWinner (bordaScore P)` — the argmax-and-tie-break machinery now
lives in `Econlib.SocialChoice.Rule.Resolute`. -/
abbrev bordaWinner (P : Profile Voter Alt) : Alt := scoreWinner (bordaScore P)

/-- **Borda count with a lexicographic tie-break**, as a resolute social choice function on the
strict domain (the Gibbard–Satterthwaite setting): every strict profile is admissible, and the
unique winner is `bordaWinner P`. This is the upstream canonical `resoluteBorda`. -/
abbrev resoluteBorda : ChoiceFunction Voter Alt := Econlib.SocialChoice.resoluteBorda

/-- If the Borda scores under `P` are exactly `s` and `w` strictly maximizes `s`, then `w` is the
resolute Borda winner. A direct application of the upstream `scoreWinner_eq_of_strict_max`. -/
private lemma bordaWinner_eq_of_strict_max (P : Profile Voter Alt) (s : Alt → ℕ)
    (hs : ∀ a, bordaScore P a = s a) {w : Alt} (hw : ∀ b, b ≠ w → s b < s w) :
    bordaWinner P = w :=
  scoreWinner_eq_of_strict_max (bordaScore P) s hs hw

/-- The rule is **resolute**: every admissible profile has at most one winner (in fact exactly one),
since the winner-set is the singleton `{bordaWinner P}`. -/
theorem resoluteBorda_resolute :
    ∀ P ∈ resoluteBorda.domain, (resoluteBorda.winners P).Subsingleton :=
  ChoiceFunction.resoluteOf_resolute _ _

-- ===========================================================================
-- Surjectivity
-- ===========================================================================

/-- The strict "spotlight" utility for `a`: `a` gets `3`, every rival `b` keeps its index value
`(b : ℕ) ≤ 2`. The utility is injective — so the induced ranking is a *strict* preference, keeping
the profile inside `strictDomain` — and `a` is ranked first. -/
private def spotlightU (a : Alt) : Alt → ℕ := fun b => if b = a then 3 else (b : ℕ)

/-- `spotlightU a` is injective: rivals carry their distinct index values `≤ 2`, and `a` alone
carries `3`. -/
private lemma spotlightU_injective (a : Alt) : Function.Injective (spotlightU a) := by
  fin_cases a <;> decide

/-- The unanimous strict profile in which all three voters use `spotlightU a`. -/
private def unanimousFor (a : Alt) : Profile Voter Alt :=
  fun _ => preferenceOfUtilityIn (spotlightU a)

/-- `unanimousFor a` is strict: every ballot is induced by the injective `spotlightU a`. -/
private lemma unanimousFor_strict (a : Alt) : unanimousFor a ∈ strictDomain Voter Alt :=
  isStrict_of_injective_utilities (fun _ => spotlightU_injective a)

/-- Borda scores of a unanimous three-voter profile with beaten-set `s` equal `3 * s.card`: a thin
corollary of the upstream `bordaScore_const` (three identical ballots ⇒ `3 ×` the per-voter score)
and `bordaScoreOf_utility_eq_card` (the per-voter score is `s.card`). -/
private lemma unanimous_bordaScore_eq (u : Alt → ℕ) (c : Alt) (s : Finset Alt)
    (h : ∀ b : Alt, u b < u c ↔ b ∈ s) :
    bordaScore (fun _ : Voter => preferenceOfUtilityIn u) c = 3 * s.card := by
  rw [bordaScore_const, bordaScoreOf_utility_eq_card u c s h, Fintype.card_fin]

/-- The Borda winner of the unanimous spotlight profile is the spotlighted alternative `a`: it
scores `6` while the two rivals score `0` and `3`. -/
private lemma unanimous_bordaWinner (a : Alt) : bordaWinner (unanimousFor a) = a := by
  fin_cases a
  · refine bordaWinner_eq_of_strict_max _ ![6, 0, 3] (fun c => ?_) (by decide)
    fin_cases c
    · exact unanimous_bordaScore_eq _ _ {1, 2} (by decide)
    · exact unanimous_bordaScore_eq _ _ ∅ (by decide)
    · exact unanimous_bordaScore_eq _ _ {1} (by decide)
  · refine bordaWinner_eq_of_strict_max _ ![0, 6, 3] (fun c => ?_) (by decide)
    fin_cases c
    · exact unanimous_bordaScore_eq _ _ ∅ (by decide)
    · exact unanimous_bordaScore_eq _ _ {0, 2} (by decide)
    · exact unanimous_bordaScore_eq _ _ {0} (by decide)
  · refine bordaWinner_eq_of_strict_max _ ![0, 3, 6] (fun c => ?_) (by decide)
    fin_cases c
    · exact unanimous_bordaScore_eq _ _ ∅ (by decide)
    · exact unanimous_bordaScore_eq _ _ {0} (by decide)
    · exact unanimous_bordaScore_eq _ _ {0, 1} (by decide)

/-- **Surjectivity.** Every alternative wins for some strict profile — e.g. the profile in which
all three voters rank it first. So no alternative is excluded a priori. -/
theorem resoluteBorda_surjective : resoluteBorda.Surjective := by
  intro a
  refine ⟨unanimousFor a, unanimousFor_strict a, ?_⟩
  rw [resoluteBorda_winners, Set.mem_singleton_iff]
  exact (unanimous_bordaWinner a).symm

-- ===========================================================================
-- The concrete manipulation
-- ===========================================================================

/-- The truthful profile: voter 0 sincerely ranks `x ≻ y ≻ z`, voters 1 and 2 rank `y ≻ x ≻ z`.
Sincere Borda scores are `x = 4`, `y = 5`, `z = 0`. -/
def truthfulP : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 0 (true): x ≻ y ≻ z
     preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ),   -- voter 1: y ≻ x ≻ z
     preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ) ]  -- voter 2: y ≻ x ≻ z

/-- Voter 0's misreport: `x ≻ z ≻ y`, which buries `y` from second place to last. -/
def buryY : PreferenceRel Alt := preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ)

/-- `truthfulP` is a strict profile: every ballot is induced by an injective utility vector. -/
lemma truthfulP_strict : truthfulP ∈ strictDomain Voter Alt := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

/-- Borda scores under `truthfulP`: `x = 0` collects `2 + 1 + 1 = 4`. -/
private lemma truthfulP_bordaScore_x : bordaScore truthfulP 0 = 4 := by
  rw [bordaScore_eq_sum_card truthfulP 0 ![{1, 2}, {2}, {2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [truthfulP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under `truthfulP`: `y = 1` collects `1 + 2 + 2 = 5`. -/
private lemma truthfulP_bordaScore_y : bordaScore truthfulP 1 = 5 := by
  rw [bordaScore_eq_sum_card truthfulP 1 ![{2}, {0, 2}, {0, 2}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [truthfulP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under `truthfulP`: `z = 2` collects `0 + 0 + 0 = 0`. -/
private lemma truthfulP_bordaScore_z : bordaScore truthfulP 2 = 0 := by
  rw [bordaScore_eq_sum_card truthfulP 2 ![∅, ∅, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [truthfulP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- **Sincere voting elects `y`.** Under truthful reporting the Borda winner is `y = 1` (scores
`x = 4`, `y = 5`, `z = 0`) — only voter 0's second choice. `y` strictly maximizes the Borda score,
so the resolute winner is `y` with no tie-break needed. -/
theorem truthful_winner_is_y : bordaWinner truthfulP = 1 := by
  refine bordaWinner_eq_of_strict_max _ ![4, 5, 0] (fun c => ?_) (by decide)
  fin_cases c
  · exact truthfulP_bordaScore_x
  · exact truthfulP_bordaScore_y
  · exact truthfulP_bordaScore_z

/-- The manipulated profile is `buryY` at voter 0, unchanged from `truthfulP` at voters 1 and 2. -/
private lemma manip_eval (i : Voter) :
    (Function.update truthfulP 0 buryY) i =
      ![ buryY,
         preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ),
         preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ) ] i := by
  fin_cases i
  · simp [Function.update_self]
  · rw [Function.update_of_ne (by decide)]; rfl
  · rw [Function.update_of_ne (by decide)]; rfl

/-- The manipulated profile is still strict: voter 0's misreport `buryY` is induced by the
injective utility `![2, 0, 1]`, and the other ballots are unchanged from `truthfulP`. -/
lemma manipP_strict : Function.update truthfulP 0 buryY ∈ strictDomain Voter Alt := by
  intro i
  rw [manip_eval i]
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

/-- Borda scores under the manipulated profile: `x = 0` collects `2 + 1 + 1 = 4`. -/
private lemma manip_bordaScore_x : bordaScore (Function.update truthfulP 0 buryY) 0 = 4 := by
  rw [bordaScore_eq_sum_card _ 0 ![{1, 2}, {2}, {2}]
    (by intro i b; rw [manip_eval i]; fin_cases i <;> fin_cases b <;>
      simp [buryY, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under the manipulated profile: `y = 1` collects `0 + 2 + 2 = 4`. -/
private lemma manip_bordaScore_y : bordaScore (Function.update truthfulP 0 buryY) 1 = 4 := by
  rw [bordaScore_eq_sum_card _ 1 ![∅, {0, 2}, {0, 2}]
    (by intro i b; rw [manip_eval i]; fin_cases i <;> fin_cases b <;>
      simp [buryY, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under the manipulated profile: `z = 2` collects `1 + 0 + 0 = 1`. -/
private lemma manip_bordaScore_z : bordaScore (Function.update truthfulP 0 buryY) 2 = 1 := by
  rw [bordaScore_eq_sum_card _ 2 ![{1}, ∅, ∅]
    (by intro i b; rw [manip_eval i]; fin_cases i <;> fin_cases b <;>
      simp [buryY, preferenceOfUtilityIn_lt_iff])]
  decide

/-- The Borda-maximizer set under the manipulated profile is `{x, y} = {0, 1}`: both `x` and `y`
score `4`, beating `z`'s score of `1`. Unlike the truthful profile this is a *tie*, so the
resolute winner is decided by the `min'` tie-break rather than a strict maximizer. -/
private lemma manip_bordaArgmax :
    scoreArgmax (bordaScore (Function.update truthfulP 0 buryY)) = {0, 1} := by
  ext a
  simp only [mem_scoreArgmax, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hmax
    have h0 := hmax 0
    rw [manip_bordaScore_x] at h0
    fin_cases a <;>
      simp only [Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, manip_bordaScore_x,
        manip_bordaScore_y, manip_bordaScore_z, true_or, or_true] at h0 ⊢
    all_goals omega
  · rintro (rfl | rfl) b <;>
      fin_cases b <;>
      simp only [Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk, manip_bordaScore_x,
        manip_bordaScore_y, manip_bordaScore_z] <;>
      omega

/-- **Burying `y` elects `x`.** When voter 0 misreports `x ≻ z ≻ y`, scores become `x = 4`, `y = 4`,
`z = 1`, and the `x`–`y` tie breaks lexicographically to `x = 0`. -/
theorem manipulated_winner_is_x :
    bordaWinner (Function.update truthfulP 0 buryY) = 0 := by
  rw [show bordaWinner (Function.update truthfulP 0 buryY)
        = scoreWinner (bordaScore (Function.update truthfulP 0 buryY)) from rfl, scoreWinner]
  simp only [manip_bordaArgmax]
  decide

/-- **`resoluteBorda` is not strategy-proof.** Voter 0 can misreport `x ≻ z ≻ y` to convert the
sincere winner `y` into `x` — their top choice. -/
theorem resoluteBorda_not_strategyProof : ¬ resoluteBorda.StrategyProof := by
  intro hSP
  have hno := hSP truthfulP truthfulP_strict 0 buryY manipP_strict
  refine hno ⟨0, ?_, ?_⟩
  · rw [resoluteBorda_winners, Set.mem_singleton_iff]
    exact manipulated_winner_is_x.symm
  · intro a ha
    rw [resoluteBorda_winners, Set.mem_singleton_iff] at ha
    have ha1 : a = 1 := ha.trans truthful_winner_is_y
    subst ha1
    change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).lt 0 1
    rw [preferenceOfUtilityIn_lt_iff]
    decide

-- ===========================================================================
-- Non-dictatorship and the formal Gibbard–Satterthwaite guarantee
-- ===========================================================================

/-- A profile splitting the three voters' top choices: voter 0 leads with `x`, voter 1 with `y`,
voter 2 with `z`. Borda scores are `x = 4 > y = 3 > z = 2`, so the winner `x` tops nobody's ballot
but voter 0's — which is exactly what refutes dictatorship for voters 1 and 2. -/
def splitP : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 0: x ≻ y ≻ z
     preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ),   -- voter 1: y ≻ x ≻ z
     preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ) ]  -- voter 2: z ≻ x ≻ y

/-- `splitP` is a strict profile: every ballot is induced by an injective utility vector. -/
lemma splitP_strict : splitP ∈ strictDomain Voter Alt := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

/-- Borda scores under `splitP`: `x = 0` collects `2 + 1 + 1 = 4`. -/
private lemma splitP_bordaScore_x : bordaScore splitP 0 = 4 := by
  rw [bordaScore_eq_sum_card splitP 0 ![{1, 2}, {2}, {1}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [splitP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under `splitP`: `y = 1` collects `1 + 2 + 0 = 3`. -/
private lemma splitP_bordaScore_y : bordaScore splitP 1 = 3 := by
  rw [bordaScore_eq_sum_card splitP 1 ![{2}, {0, 2}, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [splitP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- Borda scores under `splitP`: `z = 2` collects `0 + 0 + 2 = 2`. -/
private lemma splitP_bordaScore_z : bordaScore splitP 2 = 2 := by
  rw [bordaScore_eq_sum_card splitP 2 ![∅, ∅, {0, 1}]
    (by intro i b; fin_cases i <;> fin_cases b <;> simp [splitP, preferenceOfUtilityIn_lt_iff])]
  decide

/-- The Borda winner of `splitP` is `x = 0`: it strictly maximizes the scores `(4, 3, 2)`. -/
lemma splitP_bordaWinner : bordaWinner splitP = 0 := by
  refine bordaWinner_eq_of_strict_max _ ![4, 3, 2] (fun c => ?_) (by decide)
  fin_cases c
  · exact splitP_bordaScore_x
  · exact splitP_bordaScore_y
  · exact splitP_bordaScore_z

/-- **`resoluteBorda` is non-dictatorial.** No voter's ballot always tops the winner: voter `0` is
overruled at `truthfulP` (winner `y`, but voter 0 ranks `x ≻ y`), and voters `1` and `2` are
overruled at `splitP` (winner `x`, but voter 1 ranks `y ≻ x` and voter 2 ranks `z ≻ x`). -/
theorem resoluteBorda_not_dictatorial : ¬ ∃ i : Voter, resoluteBorda.IsDictator i := by
  rintro ⟨i, hi⟩
  fin_cases i
  · -- Voter 0 at `truthfulP`: the winner `y = 1` is not weakly preferred to `x = 0`.
    -- `IsDictator` makes the winners-set voter 0's top set, so the winner `1` is `0`-top.
    have hmem : (1 : Alt) ∈ resoluteBorda.winners truthfulP := by
      rw [resoluteBorda_winners, Set.mem_singleton_iff]; exact truthful_winner_is_y.symm
    rw [hi truthfulP truthfulP_strict, Set.mem_setOf_eq] at hmem
    have h := hmem 0
    change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).le 1 0 at h
    rw [preferenceOfUtilityIn_le_iff] at h
    exact absurd h (by decide)
  · -- Voter 1 at `splitP`: the winner `x = 0` is not weakly preferred to `y = 1`.
    have hmem : (0 : Alt) ∈ resoluteBorda.winners splitP := by
      rw [resoluteBorda_winners, Set.mem_singleton_iff]; exact splitP_bordaWinner.symm
    rw [hi splitP splitP_strict, Set.mem_setOf_eq] at hmem
    have h := hmem 1
    change (preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ)).le 0 1 at h
    rw [preferenceOfUtilityIn_le_iff] at h
    exact absurd h (by decide)
  · -- Voter 2 at `splitP`: the winner `x = 0` is not weakly preferred to `z = 2`.
    have hmem : (0 : Alt) ∈ resoluteBorda.winners splitP := by
      rw [resoluteBorda_winners, Set.mem_singleton_iff]; exact splitP_bordaWinner.symm
    rw [hi splitP splitP_strict, Set.mem_setOf_eq] at hmem
    have h := hmem 2
    change (preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ)).le 0 2 at h
    rw [preferenceOfUtilityIn_le_iff] at h
    exact absurd h (by decide)

/-- **The Gibbard–Satterthwaite guarantee, formally.** `resoluteBorda` is a resolute, surjective
social choice function on the strict domain over three alternatives, so were it strategy-proof the
library's `gibbard_satterthwaite` would make some voter a dictator — contradicting
`resoluteBorda_not_dictatorial`. The theorem therefore guarantees that a profitable manipulation
exists; `resoluteBorda_not_strategyProof` above displays one concretely. -/
theorem gibbardSatterthwaite_guarantees_manipulation : ¬ resoluteBorda.StrategyProof :=
  fun hSP =>
    resoluteBorda_not_dictatorial
      (gibbard_satterthwaite (by decide) resoluteBorda rfl resoluteBorda_resolute hSP
        resoluteBorda_surjective)

end EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable

end
