import Mathlib
import Econlib

/-!
# Condorcet's Paradox: Majority Rule Can Cycle

Condorcet's **paradox of voting** (1785) is the foundational impossibility result of social choice:
pairwise majority rule, applied to three or more voters with perfectly reasonable individual
preferences, can produce a *cyclic* social ranking — society prefers `a` to `b`, `b` to `c`, and
`c` to `a` — so that **no alternative beats all others** in head-to-head majority votes. There is no
Condorcet winner. This is the pathology that single-peakedness rules out (cf. Black's median-voter
theorem in `EconlibExamples/Preferences/MedianVoter.lean`, where an odd single-peaked electorate is
guaranteed a Condorcet winner) and that ultimately motivates Arrow's impossibility theorem.

## The model

Three voters, `Voter := Fin 3`, rank three alternatives, `Alt := Fin 3`, written `a = 0`, `b = 1`,
`c = 2`. Each voter has a *strict* linear ranking, encoded as the ordinal preference induced by a
distinct integer utility (`preferenceOfUtilityIn`, where a higher number means more preferred). The
profile is the classic Latin-square cycle:

  * voter `0`: `a ≻ b ≻ c`   (utilities `a=2, b=1, c=0`)
  * voter `1`: `b ≻ c ≻ a`   (utilities `b=2, c=1, a=0`)
  * voter `2`: `c ≻ a ≻ b`   (utilities `c=2, a=1, b=0`)

## The mathematics

`majorityCount P x y` counts the voters who strictly rank `x ≻ y`, and `pairwiseMajority P x y`
holds when strictly more voters rank `x ≻ y` than `y ≻ x`. On this profile each ordered "forward"
pair splits the electorate two-to-one:

  * `a ≻ b` for voters `{0, 2}` but `b ≻ a` only for `{1}`  ⟹  `pairwiseMajority P a b`,
  * `b ≻ c` for voters `{0, 1}` but `c ≻ b` only for `{2}`  ⟹  `pairwiseMajority P b c`,
  * `c ≻ a` for voters `{1, 2}` but `a ≻ c` only for `{0}`  ⟹  `pairwiseMajority P c a`.

The three pairwise verdicts form a `2:1` cycle `a → b → c → a`. Because a Condorcet winner must beat
every other alternative, and here every alternative is itself beaten by one rival (`a` by `c`, `b`
by `a`, `c` by `b`), no Condorcet winner can exist.

## Main definitions and theorems

- `P : Profile (Fin 3) (Fin 3)` — the cyclic preference profile above.
- `P_isStrict : Profile.IsStrict P` — every individual ranking is a strict linear order.
- `majority_cycles : pairwiseMajority P a b ∧ pairwiseMajority P b c ∧ pairwiseMajority P c a` —
  the social majority relation cycles.
- `no_condorcet_winner : ¬ ∃ x, CondorcetWinner P x` — no alternative beats all others pairwise.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.CondorcetParadox

open Econlib.Preferences Econlib.SocialChoice

/-- The three voters, an electorate of size three. -/
abbrev Voter := Fin 3

/-- The three alternatives `a = 0`, `b = 1`, `c = 2`. -/
abbrev Alt := Fin 3

/-- The cyclic preference profile. Voter `i`'s ranking is the ordinal preference induced by the
integer utility vector `util i`: voter `0` ranks `a ≻ b ≻ c`, voter `1` ranks `b ≻ c ≻ a`, and
voter `2` ranks `c ≻ a ≻ b`. Distinct integer utilities make each voter's preference strict. -/
def util : Voter → Alt → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: a ≻ b ≻ c
     ![0, 2, 1],   -- voter 1: b ≻ c ≻ a
     ![1, 0, 2] ]  -- voter 2: c ≻ a ≻ b

/-- The Condorcet profile: voter `i` orders the alternatives by `util i` (higher = better). -/
def P : Profile Voter Alt := fun i => preferenceOfUtilityIn (util i)

/-- Every ballot is a *strict* linear order: each `util i` is injective (distinct integer
utilities), so the induced preference has no ties. The paradox therefore arises from perfectly
well-behaved strict individual rankings, not from any indifference artifact. -/
theorem P_isStrict : Profile.IsStrict P := by
  intro i
  fin_cases i <;> exact strictPref_preferenceOfUtilityIn (by decide)

-- ===========================================================================
-- The majority relation cycles
-- ===========================================================================

/-- **Condorcet's cyclic majorities.** A strict majority prefers `a` to `b`, a strict majority
prefers `b` to `c`, and a strict majority prefers `c` to `a`. The pairwise-majority relation —
which is not required to be transitive — closes into a three-cycle, exactly the configuration that
makes "majority rule" ill-defined as a social ordering. -/
theorem majority_cycles :
    pairwiseMajority P 0 1 ∧ pairwiseMajority P 1 2 ∧ pairwiseMajority P 2 0 := by
  -- Each "forward" majority count is `2`, each "reverse" count is `1`; the explicit winning sets
  -- are read off `util` and verified voter by voter via the membership-characterization lemma
  -- `majorityCount_eq_card` (strict preference reads off the utilities by
  -- `preferenceOfUtilityIn_lt_iff`).
  have m01 : majorityCount P 0 1 = 2 :=
    majorityCount_eq_card P 0 1 {0, 2} (by intro i; fin_cases i <;> simp [P, util])
  have m10 : majorityCount P 1 0 = 1 :=
    majorityCount_eq_card P 1 0 {1} (by intro i; fin_cases i <;> simp [P, util])
  have m12 : majorityCount P 1 2 = 2 :=
    majorityCount_eq_card P 1 2 {0, 1} (by intro i; fin_cases i <;> simp [P, util])
  have m21 : majorityCount P 2 1 = 1 :=
    majorityCount_eq_card P 2 1 {2} (by intro i; fin_cases i <;> simp [P, util])
  have m20 : majorityCount P 2 0 = 2 :=
    majorityCount_eq_card P 2 0 {1, 2} (by intro i; fin_cases i <;> simp [P, util])
  have m02 : majorityCount P 0 2 = 1 :=
    majorityCount_eq_card P 0 2 {0} (by intro i; fin_cases i <;> simp [P, util])
  refine ⟨?_, ?_, ?_⟩
  · rw [pairwiseMajority, m10, m01]; norm_num
  · rw [pairwiseMajority, m21, m12]; norm_num
  · rw [pairwiseMajority, m02, m20]; norm_num

-- ===========================================================================
-- No Condorcet winner exists
-- ===========================================================================

/-- **No Condorcet winner.** Because the pairwise-majority relation cycles, every alternative is
beaten by some rival, so none can defeat all others: there is no Condorcet winner. This is the
sharp sense in which majority rule "fails" on an unrestricted domain — the obstruction Black's
median-voter theorem removes by assuming single-peaked preferences. -/
theorem no_condorcet_winner : ¬ ∃ x : Alt, CondorcetWinner P x := by
  obtain ⟨c0, c1, c2⟩ := majority_cycles
  rintro ⟨x, hx⟩
  -- Each alternative is beaten by one rival, so its Condorcet claim against that rival contradicts
  -- the cycle: `a` loses to `c`, `b` loses to `a`, `c` loses to `b`.
  fin_cases x
  · exact absurd (hx 2 (by decide)) (lt_asymm c2)   -- `a = 0` would beat `c = 2`, but `c` beats `a`
  · exact absurd (hx 0 (by decide)) (lt_asymm c0)   -- `b = 1` would beat `a = 0`, but `a` beats `b`
  · exact absurd (hx 1 (by decide)) (lt_asymm c1)   -- `c = 2` would beat `b = 1`, but `b` beats `c`

end EconlibExamples.SocialChoice.CondorcetParadox

end
