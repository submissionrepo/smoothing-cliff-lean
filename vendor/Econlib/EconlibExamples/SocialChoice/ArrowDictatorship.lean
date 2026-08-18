/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Mathlib
import Econlib

/-!
# Arrow's Theorem Is Tight: All Four Axioms Are Necessary

Arrow's impossibility theorem says that for a finite, nonempty electorate choosing among three or
more alternatives, no social welfare function can satisfy universal domain, Weak Pareto,
Independence of Irrelevant Alternatives, and non-dictatorship simultaneously — one of the four
must give. The theorem (`arrow_impossibility` in
`Econlib.SocialChoice`) is usually read as a negative result, but it has a sharp positive
corollary: Its hypothesis set is mutually independent. Drop any single axiom and the
remaining three become perfectly consistent.

This file proves all four independences with explicit witnesses on three voters and three
alternatives:

* **Drop non-dictatorship** — the **projection** rule `projSWF` ("society = voter `0`"): Weak
  Pareto, IIA, universal domain, and voter `0` dictates. Moreover the dictator is *unique*
  (`proj_dictator_eq_zero`).
* **Drop Weak Pareto** — the **constant** rule `constSWF` (society always reports the fixed ranking
  `2 ≻ 1 ≻ 0`): Trivially IIA, and dictator-free since no voter is ever consulted; it tramples
  unanimity (`const_not_weakPareto`).
* **Drop IIA** — the **Borda** rule `bordaSWF` on the universal domain: Weakly Paretian (a
  unanimous strict preference strictly raises every summand of the score) and non-dictatorial (two
  voters outscore one); its IIA failure `borda_not_IIA` is witnessed here on `bordaIIA_P` /
  `bordaIIA_Q`, where moving an irrelevant alternative flips society's verdict on `{x, y}` (the
  two-voter analog lives in `EconlibExamples/SocialChoice/BordaPathologies.lean`).
* **Drop universal domain** — the **singleton-domain** rule `soloSWF`: One admissible profile,
  whose lone unanimous comparison `a ≻ b` the social ranking `(a ~ c) ≻ b` honors — Weak Pareto
  holds *non-vacuously* — while IIA is automatic and every voter breaks some tie society keeps, so
  nobody dictates.

The capstone `arrow_axioms_mutually_independent` packages the four witnesses, making "every one of
Arrow's four hypotheses is logically necessary" a theorem rather than prose. As a closing
cross-check we feed the projection rule back into `arrow_impossibility` and recover the dictator
the theorem promises — voter `0`, by uniqueness (`arrow_recovers_dictator_zero`).

## The model

Three voters `Voter := Fin 3` rank three alternatives `Alt := Fin 3`. The **projection** social
welfare function `projSWF` has the universal domain (every profile is admissible) and aggregates by
copying voter `0`'s preference relation verbatim: `aggregate P := P 0`. The other three witnesses
(`constSWF`, `bordaSWF`, `soloSWF`) live on the same electorate.

## The mathematics

For the projection rule each property is immediate from its structure:

* **Weak Pareto.** If *every* voter strictly prefers `x` to `y`, then in particular voter `0` does,
  and society's ranking is voter `0`'s — so society strictly prefers `x` to `y`.
* **IIA.** Society's ranking of `{x, y}` is voter `0`'s ranking of `{x, y}`, which depends only on
  voter `0`'s `x`-vs-`y` opinion — a fortiori only on the profile's `x`-vs-`y` data.
* **Dictatorship.** Voter `0`'s strict preferences *are* society's, by definition. Conversely a
  voter `i ≠ 0` can be outvoted (pit `i` against voter `0`), so voter `0` is the *only* dictator.

For the Borda witness, Weak Pareto rests on the upstream `bordaScoreOf_lt_of_lt` (strict preference
strictly increases the per-voter Borda score) summed across the electorate; non-dictatorship pits a
lone fan of `0 ≻ 1 ≻ 2` against two voters reporting `1 ≻ 0 ≻ 2`, whose ballots drive `1`'s total
score (`5`) above `0`'s (`4`). For the singleton-domain witness, the profile is chosen so the
voters split on every pair except `a ≻ b`, which society respects.

Since `Fin 3` has three alternatives, `arrow_impossibility` applies to `projSWF` (universal domain,
Weak Pareto, IIA) and yields some dictator — voter `0`, by uniqueness.

## Main definitions and theorems

* `projSWF : WelfareFunction (Fin 3) (Fin 3)` — society copies voter `0`'s ranking.
* `proj_weakPareto : projSWF.WeakPareto`, `proj_IIA : projSWF.IIA`,
  `proj_isDictator_zero : projSWF.IsDictator 0`.
* `proj_not_nonDictatorship : ¬ projSWF.NonDictatorship` — the rule is dictatorial.
* `proj_dictator_eq_zero` / `proj_isDictator_iff` — voter `0` is the *unique* dictator.
* `constSWF`, `const_IIA`, `const_nonDictatorship`, `const_not_weakPareto` — the drop-Weak-Pareto
  witness.
* `bordaSWF`, `borda_weakPareto`, `borda_nonDictatorship`, `borda_not_IIA` — the drop-IIA witness.
* `soloSWF`, `solo_weakPareto`, `solo_IIA`, `solo_nonDictatorship`, `solo_not_universalDomain` —
  the drop-universal-domain witness.
* `arrow_axioms_minus_nondictatorship_consistent`, `arrow_axioms_minus_weakPareto_consistent`,
  `arrow_axioms_minus_IIA_consistent`, `arrow_axioms_minus_universalDomain_consistent` — the four
  three-axiom bundles.
* `arrow_axioms_mutually_independent` — the capstone: Dropping any single Arrow axiom leaves the
  other three consistent and makes the dropped axiom fail, so each is independent.
* `arrow_recovers_dictator` / `arrow_recovers_dictator_zero` — `arrow_impossibility` applied to
  `projSWF` returns a dictator, necessarily voter `0`.
-/

noncomputable section

namespace EconlibExamples.SocialChoice.ArrowDictatorship

open Econlib.Preferences Econlib.SocialChoice

/-- Three voters. -/
abbrev Voter := Fin 3

/-- Three alternatives — enough for Arrow's theorem (`3 ≤ card Alt`). -/
abbrev Alt := Fin 3

/-- The **projection** social welfare function: Admissible on every profile, and society's ranking
is voter `0`'s ranking. This is the canonical dictatorship. -/
def projSWF : WelfareFunction Voter Alt where
  domain := universalDomain Voter Alt
  aggregate := fun P => P 0

/-! ## The Projection Satisfies Weak Pareto, IIA, and Is a Dictatorship -/

/-- **Weak Pareto.** If every voter strictly prefers `x` to `y`, so does the projection. -/
theorem proj_weakPareto : projSWF.WeakPareto := by
  intro P _hP x y h
  exact h 0

/-- **IIA.** The projection satisfies Independence of Irrelevant Alternatives. -/
theorem proj_IIA : projSWF.IIA := by
  intro P Q _hP _hQ x y h
  exact h 0

/-- **Voter `0` is a dictator** of the projection rule. -/
theorem proj_isDictator_zero : projSWF.IsDictator 0 := by
  intro P _hP x y h
  exact h

/-- The projection is *dictatorial*: It is not a non-dictatorship, since voter `0` dictates. -/
theorem proj_not_nonDictatorship : ¬ projSWF.NonDictatorship :=
  fun h => h ⟨0, proj_isDictator_zero⟩

/-- Voter `0` is the **unique** dictator of the projection rule: Any dictator must equal `0`. -/
theorem proj_dictator_eq_zero (i : Voter) (hi : projSWF.IsDictator i) : i = 0 := by
  by_contra hne
  set Pi : Profile Voter Alt := fun j =>
    if j = i then preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ)
    else preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)
  have hballot : Pi i = preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ) := if_pos rfl
  have hzero : Pi 0 = preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ) :=
    if_neg fun h => hne h.symm
  have h := hi Pi (Set.mem_univ _) 1 0
    (by rw [hballot, preferenceOfUtilityIn_lt_iff]; decide)
  change (Pi 0).lt 1 0 at h
  rw [hzero, preferenceOfUtilityIn_lt_iff] at h
  exact absurd h (by decide)

/-- Dictatorship of the projection rule determines the dictator exactly: Voter `i` dictates iff
`i = 0`. -/
theorem proj_isDictator_iff (i : Voter) : projSWF.IsDictator i ↔ i = 0 :=
  ⟨proj_dictator_eq_zero i, fun h => h ▸ proj_isDictator_zero⟩

/-! ## Dropping Weak Pareto: The Constant Rule -/

/-- The **constant** social welfare function: Society always reports the fixed ranking `2 ≻ 1 ≻ 0`
(utility = index), regardless of the profile. It is trivially IIA and dictator-free — no voter
influences anything — but it tramples unanimity, so Weak Pareto fails. -/
def constSWF : WelfareFunction Voter Alt where
  domain := universalDomain Voter Alt
  aggregate := fun _ => preferenceOfUtilityIn (fun a : Alt => (a : ℕ))

/-- **IIA for the constant rule.** The social ranking never changes, so it trivially depends only
on the profile's `x`-vs-`y` data. -/
theorem const_IIA : constSWF.IIA :=
  fun _ _ _ _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- **The constant rule is non-dictatorial.** No voter's strict preference is ever consulted: At
the unanimous profile `0 ≻ 1 ≻ 2`, any would-be dictator ranks `0 ≻ 2`, but the fixed social
ranking says `2 ≻ 0`. -/
theorem const_nonDictatorship : constSWF.NonDictatorship := by
  rintro ⟨i, hi⟩
  have h := hi (fun _ => preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)) (Set.mem_univ _) 0 2
    (by change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).lt 0 2
        rw [preferenceOfUtilityIn_lt_iff]; decide)
  change (preferenceOfUtilityIn (fun a : Alt => (a : ℕ))).lt 0 2 at h
  rw [preferenceOfUtilityIn_lt_iff] at h
  exact absurd h (by decide)

/-- **The constant rule violates Weak Pareto**: Everyone ranks `0 ≻ 2`, but the fixed social
ranking says `2 ≻ 0`. -/
theorem const_not_weakPareto : ¬ constSWF.WeakPareto := by
  intro hWP
  have h := hWP (fun _ => preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)) (Set.mem_univ _) 0 2
    (fun _ => by
      change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).lt 0 2
      rw [preferenceOfUtilityIn_lt_iff]; decide)
  change (preferenceOfUtilityIn (fun a : Alt => (a : ℕ))).lt 0 2 at h
  rw [preferenceOfUtilityIn_lt_iff] at h
  exact absurd h (by decide)

/-- **Arrow's axioms minus Weak Pareto are consistent**: The constant rule has universal domain,
satisfies IIA, and is non-dictatorial. -/
theorem arrow_axioms_minus_weakPareto_consistent :
    universalDomain Voter Alt ⊆ constSWF.domain ∧ constSWF.IIA ∧ constSWF.NonDictatorship :=
  ⟨subset_refl _, const_IIA, const_nonDictatorship⟩

/-! ## Dropping IIA: The Borda Rule -/

/-- The **Borda** social welfare function on the universal domain: Society ranks by total Borda
score (`bordaRel`). It is Weakly Paretian — unanimous strict preference strictly raises every
voter's contribution to the score — and non-dictatorial — two voters outscore one — but it violates
IIA (exhibited on concrete electorates in `EconlibExamples/SocialChoice/BordaPathologies.lean`). -/
def bordaSWF : WelfareFunction Voter Alt where
  domain := universalDomain Voter Alt
  aggregate := bordaRel

/-- **Weak Pareto for Borda.** If every voter ranks `x ≻ y`, so does society under the Borda
welfare function — a one-liner over the upstream domain-free core `bordaRel_lt_of_forall_lt`. -/
theorem borda_weakPareto : bordaSWF.WeakPareto :=
  fun P _ _ _ h => bordaRel_lt_of_forall_lt P h

/-- **Borda is non-dictatorial.** With three voters, a majority can always outscore one: Society
does not always defer to any single voter's strict preferences. The witness comes from the upstream
domain-free core `exists_strictProfile_bordaRel_not_lt_of_dictator`, which builds a strict (hence
universally admissible) overruling profile for `2 ≤ #Voter ∧ 2 ≤ #Alt`. -/
theorem borda_nonDictatorship : bordaSWF.NonDictatorship := by
  rintro ⟨i, hi⟩
  obtain ⟨P, _, x, y, hxy, hnot⟩ :=
    exists_strictProfile_bordaRel_not_lt_of_dictator (Voter := Voter) (Alt := Alt)
      (by decide) (by decide) i
  exact hnot (hi P (Set.mem_univ _) x y hxy)

/-- IIA-witness profile `P` for the Borda rule on three voters. Voters `0` and `1` reproduce the
two-voter flip of `BordaPathologies` (voter 0 `x ≻ z ≻ y`, voter 1 `y ≻ x ≻ z`); voter `2` ranks
`z ≻ x ~ y`, contributing zero Borda points to both `x` and `y`. Society scores `x = 2+1+0 = 3`
against `y = 0+2+0 = 2`, so `x ≻ y`. -/
def bordaIIA_P : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ),   -- voter 0: x ≻ z ≻ y
     preferenceOfUtilityIn (![1, 2, 0] : Alt → ℕ),   -- voter 1: y ≻ x ≻ z
     preferenceOfUtilityIn (![0, 0, 1] : Alt → ℕ) ]  -- voter 2: z ≻ x ~ y

/-- IIA-witness profile `Q`: Each voter's `x`-vs-`y` opinion is unchanged from `bordaIIA_P` (voter
0 still `x ≻ y`, voter 1 still `y ≻ x`, voter 2 still `x ~ y`); only the irrelevant alternative `z`
moves. Society now scores `x = 1+0+0 = 1` against `y = 0+2+0 = 2`, so `y ≻ x` — the verdict
flips. -/
def bordaIIA_Q : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ),   -- voter 0: z ≻ x ≻ y
     preferenceOfUtilityIn (![0, 2, 1] : Alt → ℕ),   -- voter 1: y ≻ z ≻ x
     preferenceOfUtilityIn (![0, 0, 1] : Alt → ℕ) ]  -- voter 2: z ≻ x ~ y

/-- Every voter ranks `x = 0` against `y = 1` identically in `bordaIIA_P` and `bordaIIA_Q`: This is
the IIA hypothesis for the pair `{x, y}`. Only the irrelevant alternative `z` moved. -/
private lemma bordaIIA_agree (i : Voter) :
    ((bordaIIA_P i).le 0 1 ↔ (bordaIIA_Q i).le 0 1)
      ∧ ((bordaIIA_P i).le 1 0 ↔ (bordaIIA_Q i).le 1 0) := by
  fin_cases i <;>
    exact ⟨by simp [bordaIIA_P, bordaIIA_Q, preferenceOfUtilityIn_le_iff],
      by simp [bordaIIA_P, bordaIIA_Q, preferenceOfUtilityIn_le_iff]⟩

private lemma bordaIIA_P_score_x : bordaScore bordaIIA_P 0 = 3 := by
  rw [bordaScore_eq_sum_card bordaIIA_P 0 ![{1, 2}, {2}, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;>
      simp [bordaIIA_P, preferenceOfUtilityIn_lt_iff])]
  decide

private lemma bordaIIA_P_score_y : bordaScore bordaIIA_P 1 = 2 := by
  rw [bordaScore_eq_sum_card bordaIIA_P 1 ![∅, {0, 2}, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;>
      simp [bordaIIA_P, preferenceOfUtilityIn_lt_iff])]
  decide

private lemma bordaIIA_Q_score_x : bordaScore bordaIIA_Q 0 = 1 := by
  rw [bordaScore_eq_sum_card bordaIIA_Q 0 ![{1}, ∅, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;>
      simp [bordaIIA_Q, preferenceOfUtilityIn_lt_iff])]
  decide

private lemma bordaIIA_Q_score_y : bordaScore bordaIIA_Q 1 = 2 := by
  rw [bordaScore_eq_sum_card bordaIIA_Q 1 ![∅, {0, 2}, ∅]
    (by intro i b; fin_cases i <;> fin_cases b <;>
      simp [bordaIIA_Q, preferenceOfUtilityIn_lt_iff])]
  decide

/-- **Borda violates IIA.** Society's ranking of `{x, y}` flips between `bordaIIA_P` (where
`x ≻ y`) and `bordaIIA_Q` (where `y ≻ x`) even though every voter ranks `x` against `y` identically
in the two profiles — only the irrelevant alternative `z` moved. This is the drop-IIA witness's
*failure* of the axiom it drops, the analog of `BordaPathologies.borda_not_IIA` for the three-voter
rule `bordaSWF`. -/
theorem borda_not_IIA : ¬ bordaSWF.IIA := by
  intro hIIA
  -- Both profiles are admissible (universal domain), so IIA applies to the pair `{x, y}`.
  have hsame := (hIIA bordaIIA_P bordaIIA_Q (Set.mem_univ _) (Set.mem_univ _) 0 1 bordaIIA_agree).1
  -- Society ranks `x ≽ y` under `P` (scores `3 ≥ 2`) but not under `Q` (scores `1 < 2`).
  have hP : (bordaRel bordaIIA_P).le 0 1 := by
    rw [bordaRel, preferenceOfUtilityIn_le_iff, bordaIIA_P_score_x, bordaIIA_P_score_y]; norm_num
  have hQ : ¬ (bordaRel bordaIIA_Q).le 0 1 := by
    rw [bordaRel, preferenceOfUtilityIn_le_iff, bordaIIA_Q_score_x, bordaIIA_Q_score_y]; norm_num
  exact hQ (hsame.mp hP)

/-- **Arrow's axioms minus IIA are consistent**: The Borda rule has universal domain, satisfies
Weak Pareto, and is non-dictatorial. -/
theorem arrow_axioms_minus_IIA_consistent :
    universalDomain Voter Alt ⊆ bordaSWF.domain ∧ bordaSWF.WeakPareto
      ∧ bordaSWF.NonDictatorship :=
  ⟨subset_refl _, borda_weakPareto, borda_nonDictatorship⟩

/-! ## Dropping Universal Domain: A Singleton-Domain Rule -/

/-- The single admissible profile of the restricted-domain witness: Voters rank `a ≻ b ≻ c`,
`a ≻ c ≻ b`, and `c ≻ a ≻ b`. The only unanimous strict comparison is `a ≻ b`. -/
def soloProfile : Profile Voter Alt :=
  ![ preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ),   -- voter 0: a ≻ b ≻ c
     preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ),   -- voter 1: a ≻ c ≻ b
     preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ) ]  -- voter 2: c ≻ a ≻ b

/-- The **restricted-domain** social welfare function: Only `soloProfile` is admissible, and
society reports `(a ~ c) ≻ b` — honoring the unanimous `a ≻ b` (so Weak Pareto holds with real
content) while tying exactly the comparisons on which the voters split, so nobody dictates. -/
def soloSWF : WelfareFunction Voter Alt where
  domain := {soloProfile}
  aggregate := fun _ => preferenceOfUtilityIn (![1, 0, 1] : Alt → ℕ)

/-- **Weak Pareto on the restricted domain** — non-vacuously: The lone unanimous comparison is
`a ≻ b` (voters split on the other pairs), and the social ranking `(a ~ c) ≻ b` honors it. -/
theorem solo_weakPareto : soloSWF.WeakPareto := by
  rintro P rfl x y h
  -- Read voters 1 and 2's strict verdicts off their utility vectors; their joint strict agreement
  -- narrows the candidate pairs to `(a, b)` and `(c, b)` — a superset of the lone unanimous pair
  -- `a ≻ b` (voter 0 ranks `b ≻ c`, so `(c, b)` is not unanimous) — both of which society ranks
  -- strictly.
  have h1 : (![2, 0, 1] : Alt → ℕ) y < ![2, 0, 1] x := by
    have hv := h 1
    rwa [show soloProfile 1 = preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ) from rfl,
      preferenceOfUtilityIn_lt_iff] at hv
  have h2 : (![1, 0, 2] : Alt → ℕ) y < ![1, 0, 2] x := by
    have hv := h 2
    rwa [show soloProfile 2 = preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ) from rfl,
      preferenceOfUtilityIn_lt_iff] at hv
  change (preferenceOfUtilityIn (![1, 0, 1] : Alt → ℕ)).lt x y
  rw [preferenceOfUtilityIn_lt_iff]
  fin_cases x <;> fin_cases y <;> revert h1 h2 <;> decide

/-- **IIA on the restricted domain.** With a single admissible profile, the two profiles being
compared coincide, so the social verdicts trivially agree. -/
theorem solo_IIA : soloSWF.IIA := by
  rintro P Q rfl rfl x y _
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **The restricted-domain rule is non-dictatorial.** No voter's strict preferences are honored
across the board: voter 0 ranks `b ≻ c` but society *reverses* it to `c ≻ b`, while voters 1 and 2
each break a comparison society ties (voter 1 ranks `a ≻ c`, voter 2 ranks `c ≻ a`, and society ties
`a ~ c`). Either way each voter is overruled on some pair, so none dictates. -/
theorem solo_nonDictatorship : soloSWF.NonDictatorship := by
  rintro ⟨i, hi⟩
  fin_cases i
  · -- Voter 0 ranks `b ≻ c`, but society ranks `c ≻ b`.
    have h := hi soloProfile rfl 1 2
      (by change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).lt 1 2
          rw [preferenceOfUtilityIn_lt_iff]; decide)
    change (preferenceOfUtilityIn (![1, 0, 1] : Alt → ℕ)).lt 1 2 at h
    rw [preferenceOfUtilityIn_lt_iff] at h
    exact absurd h (by decide)
  · -- Voter 1 ranks `a ≻ c`, but society ties them.
    have h := hi soloProfile rfl 0 2
      (by change (preferenceOfUtilityIn (![2, 0, 1] : Alt → ℕ)).lt 0 2
          rw [preferenceOfUtilityIn_lt_iff]; decide)
    change (preferenceOfUtilityIn (![1, 0, 1] : Alt → ℕ)).lt 0 2 at h
    rw [preferenceOfUtilityIn_lt_iff] at h
    exact absurd h (by decide)
  · -- Voter 2 ranks `c ≻ a`, but society ties them.
    have h := hi soloProfile rfl 2 0
      (by change (preferenceOfUtilityIn (![1, 0, 2] : Alt → ℕ)).lt 2 0
          rw [preferenceOfUtilityIn_lt_iff]; decide)
    change (preferenceOfUtilityIn (![1, 0, 1] : Alt → ℕ)).lt 2 0 at h
    rw [preferenceOfUtilityIn_lt_iff] at h
    exact absurd h (by decide)

/-- **The restricted-domain rule drops universal domain**: The unanimous profile
`c ≻ b ≻ a` is inadmissible (it differs from `soloProfile` already at voter `0`). -/
theorem solo_not_universalDomain : ¬ universalDomain Voter Alt ⊆ soloSWF.domain := by
  intro hsub
  have hmem : (fun _ : Voter => preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ)) = soloProfile :=
    hsub (Set.mem_univ _)
  have hzero := congrFun hmem 0
  have hle : (preferenceOfUtilityIn (![0, 1, 2] : Alt → ℕ)).le 1 0 := by
    rw [preferenceOfUtilityIn_le_iff]; decide
  rw [hzero] at hle
  change (preferenceOfUtilityIn (![2, 1, 0] : Alt → ℕ)).le 1 0 at hle
  rw [preferenceOfUtilityIn_le_iff] at hle
  exact absurd hle (by decide)

/-- **Arrow's axioms minus universal domain are consistent**: The singleton-domain rule satisfies
Weak Pareto (non-vacuously), IIA, and non-dictatorship on its restricted domain. -/
theorem arrow_axioms_minus_universalDomain_consistent :
    soloSWF.WeakPareto ∧ soloSWF.IIA ∧ soloSWF.NonDictatorship :=
  ⟨solo_weakPareto, solo_IIA, solo_nonDictatorship⟩

/-! ## Tightness of Arrow's Theorem -/

/-- **Arrow's axioms minus non-dictatorship are consistent.** The projection rule simultaneously
satisfies universal domain, Weak Pareto, IIA, and admits a dictator. So Arrow's impossibility is
tight in the non-dictatorship direction: Weakening the conclusion to allow a dictator makes the
remaining axioms mutually consistent. -/
theorem arrow_axioms_minus_nondictatorship_consistent :
    universalDomain Voter Alt ⊆ projSWF.domain ∧ projSWF.WeakPareto ∧ projSWF.IIA
      ∧ ∃ i : Voter, projSWF.IsDictator i :=
  ⟨subset_refl _, proj_weakPareto, proj_IIA, ⟨0, proj_isDictator_zero⟩⟩

/-- **Arrow's four hypotheses are mutually independent.** Dropping any single one of universal
domain, Weak Pareto, IIA, or non-dictatorship leaves the remaining three jointly satisfiable while
the dropped axiom fails — each independence witnessed by an explicit rule on three
voters and three alternatives:

* drop **non-dictatorship** — the projection rule `projSWF`, which is dictatorial
  (`¬ projSWF.NonDictatorship`);
* drop **Weak Pareto** — the constant rule `constSWF`, which tramples unanimity
  (`¬ constSWF.WeakPareto`);
* drop **IIA** — the Borda rule `bordaSWF`, whose social verdict on a pair flips when an irrelevant
  alternative moves (`¬ bordaSWF.IIA`);
* drop **universal domain** — the singleton-domain rule `soloSWF`, which is not defined on every
  profile (`¬ universalDomain ⊆ soloSWF.domain`).

So every one of Arrow's four hypotheses is logically necessary: No three of them already produce
the impossibility, and each is independently violable while the other three hold. -/
theorem arrow_axioms_mutually_independent :
    -- drop non-dictatorship: the projection rule satisfies the other three and is dictatorial
    (universalDomain Voter Alt ⊆ projSWF.domain ∧ projSWF.WeakPareto ∧ projSWF.IIA
        ∧ ¬ projSWF.NonDictatorship) ∧
    -- drop Weak Pareto: the constant rule satisfies the other three and fails Weak Pareto
    (universalDomain Voter Alt ⊆ constSWF.domain ∧ constSWF.IIA ∧ constSWF.NonDictatorship
        ∧ ¬ constSWF.WeakPareto) ∧
    -- drop IIA: the Borda rule satisfies the other three and fails IIA
    (universalDomain Voter Alt ⊆ bordaSWF.domain ∧ bordaSWF.WeakPareto ∧ bordaSWF.NonDictatorship
        ∧ ¬ bordaSWF.IIA) ∧
    -- drop universal domain: the singleton-domain rule satisfies the other three and lacks it
    (soloSWF.WeakPareto ∧ soloSWF.IIA ∧ soloSWF.NonDictatorship
        ∧ ¬ universalDomain Voter Alt ⊆ soloSWF.domain) :=
  ⟨⟨subset_refl _, proj_weakPareto, proj_IIA, proj_not_nonDictatorship⟩,
    ⟨arrow_axioms_minus_weakPareto_consistent.1, arrow_axioms_minus_weakPareto_consistent.2.1,
      arrow_axioms_minus_weakPareto_consistent.2.2, const_not_weakPareto⟩,
    ⟨arrow_axioms_minus_IIA_consistent.1, arrow_axioms_minus_IIA_consistent.2.1,
      arrow_axioms_minus_IIA_consistent.2.2, borda_not_IIA⟩,
    ⟨solo_weakPareto, solo_IIA, solo_nonDictatorship, solo_not_universalDomain⟩⟩

/-- **Cross-check via `arrow_impossibility`.** Because `Alt = Fin 3` has three alternatives and
`projSWF` satisfies universal domain, Weak Pareto, and IIA, Arrow's theorem applies and returns a
dictator. -/
theorem arrow_recovers_dictator : ∃ i : Voter, projSWF.IsDictator i :=
  arrow_impossibility (by decide) projSWF (subset_refl _) proj_weakPareto proj_IIA

/-- **The recovered dictator is voter `0`.** By the uniqueness theorem `proj_dictator_eq_zero`,
whatever dictator Arrow's theorem returns for the projection rule can only be voter `0`. -/
theorem arrow_recovers_dictator_zero :
    ∃ i : Voter, projSWF.IsDictator i ∧ i = 0 := by
  obtain ⟨i, hi⟩ := arrow_recovers_dictator
  exact ⟨i, hi, proj_dictator_eq_zero i hi⟩

end EconlibExamples.SocialChoice.ArrowDictatorship

end
