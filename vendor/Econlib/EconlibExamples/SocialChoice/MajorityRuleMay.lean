import Mathlib
import Econlib

/-!
# May's Theorem: Majority Rule Is the Anonymous, Neutral, Positively Responsive Rule

For exactly **two** alternatives, the cycling pathologies of Condorcet and the impossibilities of
Arrow and Gibbard–Satterthwaite all vanish, and a clean **characterization** takes their place.
Kenneth May's theorem (1952) says: a social choice function on two alternatives satisfies

  * **Anonymity** — voters are treated symmetrically (only the vote totals matter),
  * **Neutrality** — the two alternatives are treated symmetrically, and
  * **Positive responsiveness** — if a winning/tied alternative gains a supporter, it wins outright,

**if and only if it is simple majority rule.** May's theorem is the axiomatic justification of "one
person, one vote, majority wins."

This file does the forward, constructive half on a concrete electorate: it builds simple majority
rule as an honest `ChoiceFunction`, verifies all three May axioms, and then invokes the library's
`may_strict_majority_wins` to conclude that whenever one alternative has a strict majority it is the
unique winner. The converse, hard half — that the three axioms force a rule to be majority
rule — is the upstream `winners_eq_majorityRule`, specialized here as `maj_characterization`: every
**full-domain** choice function meeting the axioms agrees with `majorityRule` on every profile.
(Universal domain is a maintained hypothesis throughout — both `maj_characterization` and the
`iff` form `maj_characterization_iff` carry the explicit `hDom : ∀ Q, Q ∈ f.domain`; May's theorem
is a statement about rules defined on every profile.)

## The model

Three voters `Voter := Fin 3` choose between two alternatives `Alt := Fin 2`. **Majority rule**
`majorityRule` admits every profile and declares `x` a winner exactly when at least as many voters
rank `x` above the other alternative as rank the other above `x`:

  `winners P = { x | majorityCount P (otherFin2 x) x ≤ majorityCount P x (otherFin2 x) }`.

A strict majority for `x` makes `{x}` the sole winner; an exact tie makes both alternatives win.
Ballots are full weak preferences, so indifference is allowed and ties are possible
(an all-indifferent profile elects both alternatives, odd electorate notwithstanding). On *strict*
ballots, however, oddness bites: the two majority counts split the odd total `3`, a tie is
arithmetically impossible, and the winner is always unique — `strict_profile_unique_winner` proves
exactly this.

## The mathematics

  * **Anonymity** holds because `majorityCount` is a cardinality of a voter set, invariant under
    permuting voters.
  * **Neutrality** (with respect to `relabelProfile`, the relabeling of the two alternatives) holds
    because swapping the alternatives swaps the two majority counts — formalized upstream by
    `majorityCount_relabel_swap`.
  * **Positive responsiveness** holds because a voter switching toward `x` increments
    `majorityCount P x (otherFin2 x)` by one (`majorityCount_indiffAt_*`), breaking any tie in `x`'s
    favor.

With the three axioms and full domain in hand, `may_strict_majority_wins` delivers the conclusion.

## Main definitions and theorems

- `majorityRule : ChoiceFunction (Fin 3) (Fin 2)` — simple majority rule with ties.
- `maj_full_domain : ∀ Q, Q ∈ majorityRule.domain` — every profile is admissible.
- `maj_anonymity : majorityRule.Anonymity`.
- `maj_neutrality : majorityRule.Neutrality relabelProfile`.
- `maj_positiveResponsiveness : ∀ x y, majorityRule.PositiveResponsiveness x y`.
- `strict_majority_wins` — May's conclusion: a strict-majority alternative is the unique winner.
- `maj_characterization` — May's converse half: any **full-domain** rule (`hDom`) meeting the three
  axioms agrees with `majorityRule` everywhere.
- `maj_characterization_iff` — the full "if and only if", again under the full-domain hypothesis
  `hDom`: the three axioms hold iff the rule is simple majority rule.
- `strict_profile_unique_winner` — the odd-electorate bonus: on strict ballots the majority counts
  split `3`, so a tie is impossible and the winner is always unique.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.MajorityRuleMay

open Econlib.Preferences Econlib.SocialChoice

/-- Three voters. The May axioms below hold for any finite electorate — no proof uses `3` — but
oddness buys a bonus: on strict ballots the two majority counts split an odd total, so a strict
majority always exists and the winner is unique (`strict_profile_unique_winner`). Ballots with
indifference can still tie (an all-indifferent profile elects both alternatives). -/
abbrev Voter := Fin 3

/-- Two alternatives — the domain of May's theorem. -/
abbrev Alt := Fin 2

/-- **Simple majority rule** on this electorate — the upstream canonical `majorityRule` on two
alternatives, instantiated at `Voter := Fin 3`. Every profile is admissible, and the winners are
the (weakly) majority-preferred alternatives: a strict majority yields a singleton, an exact split
yields both. The three May axioms (`majorityRule_anonymity`, `majorityRule_neutrality`,
`majorityRule_positiveResponsiveness`) and the strict-majority conclusion are all proved upstream in
`Econlib.SocialChoice.May`; this file specialises them and adds the odd-electorate bonus below. -/
abbrev majorityRule : ChoiceFunction Voter Alt := Econlib.SocialChoice.majorityRule

/-- Every profile is admissible under majority rule. -/
theorem maj_full_domain : ∀ Q : Profile Voter Alt, Q ∈ majorityRule.domain :=
  majorityRule_full_domain

/-- **Anonymity.** Permuting the voters leaves the winners-set unchanged. -/
theorem maj_anonymity : majorityRule.Anonymity := majorityRule_anonymity

/-- **Neutrality.** Relabeling the two alternatives commutes with majority rule. -/
theorem maj_neutrality : majorityRule.Neutrality relabelProfile := majorityRule_neutrality

/-- **Positive responsiveness.** If `x` is winning or tied and one voter shifts strictly toward `x`,
then `x` becomes the unique winner. -/
theorem maj_positiveResponsiveness :
    ∀ x y : Alt, majorityRule.PositiveResponsiveness x y := majorityRule_positiveResponsiveness

/-- **May's theorem, conclusion.** Whenever strictly more voters prefer `winner` to the other
alternative than the reverse, `winner` is the unique social choice under majority rule. -/
theorem strict_majority_wins
    (P : Profile Voter Alt) {winner : Alt}
    (h_majority : majorityCount P (otherFin2 winner) winner
      < majorityCount P winner (otherFin2 winner)) :
    majorityRule.winners P = {winner} :=
  majorityRule_strict_majority_wins P h_majority

/-- **May's theorem, converse half.** The three axioms do not merely describe majority rule — they
determine it: any choice function `f` on this electorate satisfying anonymity, neutrality, and
positive responsiveness over the full domain agrees with `majorityRule` on the winners of every
profile. This is the hard direction, specializing the upstream `winners_eq_majorityRule`; the full
"if and only if" is `maj_characterization_iff` below. -/
theorem maj_characterization
    (f : ChoiceFunction Voter Alt)
    (hAnon : f.Anonymity)
    (hNeut : f.Neutrality relabelProfile)
    (hPosResp : ∀ x y : Alt, f.PositiveResponsiveness x y)
    (hDom : ∀ Q : Profile Voter Alt, Q ∈ f.domain)
    (P : Profile Voter Alt) :
    f.winners P = majorityRule.winners P :=
  winners_eq_majorityRule f hAnon hNeut hPosResp hDom P

/-- **May's theorem, the iff.** On this three-voter, two-alternative electorate, a
full-domain choice function `f` satisfies anonymity, neutrality, and positive responsiveness if and
only if it is simple majority rule (agrees with `majorityRule` on every profile). Both directions
come bundled from the upstream packaged characterization `may_characterization`: the converse
(axioms ⟹ majority rule) is `maj_characterization` above, and the easy direction (majority rule
satisfies the axioms) is inherited through the pointwise agreement. This is the "if and only if"
promised in the title. -/
theorem maj_characterization_iff
    (f : ChoiceFunction Voter Alt)
    (hDom : ∀ Q : Profile Voter Alt, Q ∈ f.domain) :
    (f.Anonymity ∧ f.Neutrality relabelProfile ∧ ∀ x y : Alt, f.PositiveResponsiveness x y)
      ↔ ∀ P : Profile Voter Alt, f.winners P = majorityRule.winners P :=
  Econlib.SocialChoice.may_characterization f hDom

-- ===========================================================================
-- Odd strict electorates never tie
-- ===========================================================================

/-- On a strict ballot over two alternatives, every voter strictly ranks one over the other:
"not `0 ≻ 1`" and "`1 ≻ 0`" coincide. (With indifference allowed this fails — an indifferent
voter ranks neither — which is why the no-tie theorem below needs the strict domain.) -/
private lemma strict_dichotomy {P : Profile Voter Alt} (hP : Profile.IsStrict P) (i : Voter) :
    ¬ (P i).lt 0 1 ↔ (P i).lt 1 0 := by
  constructor
  · -- Trichotomy minus indifference (strictness) minus the refuted direction leaves `1 ≻ 0`.
    intro h
    rcases StrictPref.lt_or_lt_of_ne (hP i) (show (0 : Alt) ≠ 1 by decide) with h' | h'
    · exact absurd h' h
    · exact h'
  · exact fun h => (P i).not_lt_both h

/-- On a strict profile the two majority counts partition the electorate:
`#(0 ≻ 1) + #(1 ≻ 0) = 3`. -/
private lemma strict_count_sum {P : Profile Voter Alt} (hP : Profile.IsStrict P) :
    majorityCount P 0 1 + majorityCount P 1 0 = 3 := by
  classical
  rw [majorityCount_eq_card P 0 1 (Finset.univ.filter fun i => (P i).lt 0 1) (fun i => by simp),
    majorityCount_eq_card P 1 0 (Finset.univ.filter fun i => ¬ (P i).lt 0 1) (fun i => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (strict_dichotomy hP i).symm),
    Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

/-- **Odd strict electorates never tie.** With three voters casting strict ballots, the two
majority counts split the odd total `3` and so cannot be equal: some alternative always commands a
strict majority, and by `strict_majority_wins` it is the unique winner. This is the formal
content of "an odd electorate has no ties" — and the strictness hypothesis is essential, since an
all-indifferent profile ties the counts at `0` and elects both alternatives. -/
theorem strict_profile_unique_winner (P : Profile Voter Alt)
    (hP : P ∈ strictDomain Voter Alt) :
    ∃ w : Alt, majorityRule.winners P = {w} := by
  have hsum : majorityCount P 0 1 + majorityCount P 1 0 = 3 := strict_count_sum hP
  rcases Nat.lt_or_ge (majorityCount P 0 1) (majorityCount P 1 0) with h | h
  · -- `1` commands the strict majority.
    exact ⟨1, strict_majority_wins P (by rwa [otherFin2_one])⟩
  · -- The counts cannot tie (their sum is odd), so `0` commands the strict majority.
    refine ⟨0, strict_majority_wins P ?_⟩
    rw [otherFin2_zero]
    omega

end EconlibExamples.SocialChoice.MajorityRuleMay

end
