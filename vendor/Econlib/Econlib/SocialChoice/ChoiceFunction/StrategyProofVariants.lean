/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.ChoiceFunction.Properties

/-!
# The set-valued strategy-proofness variants are pairwise independent

`Econlib.SocialChoice.ChoiceFunction.Properties` defines three set-extensions of strategy-proofness
for a set-valued choice rule — `StrategyProof` (= optimistic / Gärdenfors),
`StrategyProofPessimistic` (min-element), and `StrategyProofKelly` (cautious / elementwise
dominance) — and proves they coincide on resolute (singleton-valued) rules
(`strategyProof_variants_iff_of_resolute`). It also records the single general implication among
the underlying manipulation events, `kellyManip_imp_optimistic_or_pessimistic`.

This file establishes the converse negative facts: For set-valued rules no single variant implies
another, in either direction (Duggan and Schwartz 2000; Kelly 1977; Gärdenfors 1976). For every
ordered pair `(X, Y)` of distinct variants there is a rule satisfying `X` but not `Y`, so the three
are **pairwise logically independent** and none is the weakest. The headline theorem is
`strategyProof_variants_pairwise_independent`. This is sharp: The optimistic and pessimistic
variants jointly imply the Kelly one (`StrategyProof.strategyProofKelly_of_pessimistic`), so
pairwise independence does not extend to a joint independence.

## Main definitions

* `flatPref`: The all-indifferent preference on `Fin 3`, used as the misreport report.
* `sepRule`: The single-voter, two-profile separating rule built from `(R, O, N)`.

## Main statements

* `strategyProof_variants_pairwise_independent`: The six non-implications, bundled.
* `exists_strategyProof_not_pessimistic`, `exists_strategyProof_not_kelly`,
  `exists_pessimistic_not_strategyProof`, `exists_pessimistic_not_kelly`,
  `exists_kelly_not_strategyProof`, `exists_kelly_not_pessimistic`: The individual separations.

## Notes

Every separating rule is an instance of `sepRule R O N`: A single voter (`Unit`), three
alternatives (`Fin 3`), and a two-profile admissible domain `{const R, const flatPref}`. The
truthful profile reports `R` and wins the set `O`; the misreport profile reports the
all-indifferent preference `flatPref` and wins `N`. Because `flatPref` has no strict comparisons,
every transition except the truthful-to-misreport one is automatically harmless, so the rule's
strategy-proofness under each extension reduces to a single forward manipulation event on
`(R, O, N)` — see `strategyProof_sepRule_iff`, `strategyProofPessimistic_sepRule_iff`,
`strategyProofKelly_sepRule_iff`. The four concrete `(R, O, N)` choices realize the truth-tables
needed to separate all six pairs.

## References

* Duggan, John, and Thomas Schwartz. 2000. “Strategic Manipulability Without Resoluteness or Shared
  Beliefs: Gibbard-Satterthwaite Generalized.” *Social Choice and Welfare* 17 (1): 85–93.
  [https://doi.org/10.1007/pl00007177](https://doi.org/10.1007/pl00007177).
* Gärdenfors, Peter. 1976. “Manipulation of Social Choice Functions.” *Journal of Economic Theory*
  13 (2): 217–28. [https://doi.org/10.1016/0022-0531(76)90016-8](https://doi.org/10.1016/0022-0531(76)90016-8).
* Kelly, Jerry S. 1977. “Strategy-Proofness and Social Choice Functions Without Singlevaluedness.”
  *Econometrica* 45 (2): 439. [https://doi.org/10.2307/1911220](https://doi.org/10.2307/1911220).

## Tags

social choice, strategy-proofness, duggan-schwartz, kelly, set extension, manipulation
-/

@[expose] public section

namespace Econlib.SocialChoice.ChoiceFunction

open Econlib.Preferences Econlib.SocialChoice

/-- The all-indifferent preference on `Fin 3`: Every alternative carries utility `0`, so no strict
comparison holds. Used as the "misreport" report in `sepRule`. -/
def flatPref : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun _ => (0 : ℕ))

/-- `flatPref` has no strict preferences. -/
@[simp] lemma flatPref_not_lt (x y : Fin 3) : ¬ flatPref.lt x y := by
  simp [flatPref]

open Classical in
/-- The separating rule for a truthful report `R` winning `O` and a `flatPref` misreport winning
`N`. Single voter `Unit`; admissible domain is the two constant profiles. The winner map branches
on `Q () = R`, an undecidable equality of preferences, so it is constructed with classical choice;
this is local to the counterexample and leaks no `DecidableEq` instance into the rule's type. -/
def sepRule (R : PreferenceRel (Fin 3)) (O N : Set (Fin 3))
    (hO : O.Nonempty) (hN : N.Nonempty) : ChoiceFunction Unit (Fin 3) where
  domain := {Function.const Unit R, Function.const Unit flatPref}
  winners Q := if Q () = R then O else N
  winners_nonempty := by
    rintro Q -
    by_cases h : Q () = R
    · rw [if_pos h]; exact hO
    · rw [if_neg h]; exact hN

variable {R : PreferenceRel (Fin 3)} {O N : Set (Fin 3)} {hO : O.Nonempty} {hN : N.Nonempty}

open Classical in
/-- Evaluation of `sepRule` winners on a constant profile. -/
lemma sepRule_winners_const (S : PreferenceRel (Fin 3)) :
    (sepRule R O N hO hN).winners (Function.const Unit S) = if S = R then O else N := by
  simp only [sepRule, Function.const_apply]
  congr 1

/-- On `Unit`, a unilateral deviation replaces the whole profile by a constant. -/
lemma update_unit_const (Q : Profile Unit (Fin 3)) (R' : PreferenceRel (Fin 3)) :
    Function.update Q () R' = Function.const Unit R' := by
  funext u
  rcases u with ⟨⟩
  simp [Function.update_self]

/-- A `sepRule` is optimistically strategy-proof iff its single forward manipulation event is
absent. -/
lemma strategyProof_sepRule_iff (hRf : R ≠ flatPref) :
    StrategyProof (sepRule R O N hO hN) ↔ ¬ OptimisticManip R O N := by
  set f := sepRule R O N hO hN with hf
  -- The two admissible profiles and their winner sets.
  have hwR : f.winners (Function.const Unit R) = O := by
    rw [hf, sepRule_winners_const]; exact if_pos rfl
  have hwF : f.winners (Function.const Unit flatPref) = N := by
    rw [hf, sepRule_winners_const]; exact if_neg (Ne.symm hRf)
  have hmemR : Function.const Unit R ∈ f.domain := Set.mem_insert _ _
  have hmemF : Function.const Unit flatPref ∈ f.domain :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  constructor
  · -- Strategy-proofness forbids the truthful-to-misreport optimistic manipulation.
    intro hsp hopt
    have := hsp (Function.const Unit R) hmemR () flatPref
      (by rw [update_unit_const]; exact hmemF)
    rw [update_unit_const, Function.const_apply, hwR, hwF] at this
    exact this hopt
  · -- The only non-vacuous transition is truthful-to-misreport; rule it out.
    intro hno P hP i R' hupd hev
    rcases i with ⟨⟩
    rw [update_unit_const] at hupd hev
    -- `P` is one of the two constant profiles; the deviation is to a constant `R'`.
    rcases (Set.mem_insert_iff.mp hP) with hPR | hPF
    all_goals rcases (Set.mem_insert_iff.mp hupd) with hR' | hR'
    · -- truthful R, deviate to R: judged by R, O → O
      subst hPR
      rw [Function.const_apply, hwR] at hev
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [this, hwR] at hev
      obtain ⟨b, hbO, hb⟩ := hev
      exact (R.lt_irrefl b) (hb b hbO)
    · -- truthful R, deviate to flatPref: judged by R, O → N
      subst hPR
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwR, this, hwF] at hev
      exact hno hev
    · -- truthful flatPref, deviate to R: judged by flatPref, N → O
      subst hPF
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [Function.const_apply, hwF, this, hwR] at hev
      obtain ⟨b, _, hb⟩ := hev
      obtain ⟨a, haN⟩ := hN
      exact flatPref_not_lt b a (hb a haN)
    · -- truthful flatPref, deviate to flatPref: judged by flatPref, N → N
      subst hPF
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwF, this, hwF] at hev
      obtain ⟨b, _, hb⟩ := hev
      obtain ⟨a, haN⟩ := hN
      exact flatPref_not_lt b a (hb a haN)

/-- A `sepRule` is pessimistically strategy-proof iff its single forward manipulation event is
absent. -/
lemma strategyProofPessimistic_sepRule_iff (hRf : R ≠ flatPref) :
    StrategyProofPessimistic (sepRule R O N hO hN) ↔ ¬ PessimisticManip R O N := by
  set f := sepRule R O N hO hN with hf
  have hwR : f.winners (Function.const Unit R) = O := by
    rw [hf, sepRule_winners_const]; exact if_pos rfl
  have hwF : f.winners (Function.const Unit flatPref) = N := by
    rw [hf, sepRule_winners_const]; exact if_neg (Ne.symm hRf)
  have hmemR : Function.const Unit R ∈ f.domain := Set.mem_insert _ _
  have hmemF : Function.const Unit flatPref ∈ f.domain :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  constructor
  · intro hsp hpess
    have := hsp (Function.const Unit R) hmemR () flatPref
      (by rw [update_unit_const]; exact hmemF)
    rw [update_unit_const, Function.const_apply, hwR, hwF] at this
    exact this hpess
  · intro hno P hP i R' hupd hev
    rcases i with ⟨⟩
    rw [update_unit_const] at hupd hev
    rcases (Set.mem_insert_iff.mp hP) with hPR | hPF
    all_goals rcases (Set.mem_insert_iff.mp hupd) with hR' | hR'
    · -- truthful R, deviate to R: judged by R, O → O
      subst hPR
      rw [Function.const_apply, hwR] at hev
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [this, hwR] at hev
      obtain ⟨a, haO, ha⟩ := hev
      exact (R.lt_irrefl a) (ha a haO)
    · -- truthful R, deviate to flatPref: judged by R, O → N
      subst hPR
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwR, this, hwF] at hev
      exact hno hev
    · -- truthful flatPref, deviate to R: judged by flatPref, N → O
      subst hPF
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [Function.const_apply, hwF, this, hwR] at hev
      obtain ⟨a, _, ha⟩ := hev
      obtain ⟨b, hbO⟩ := hO
      exact flatPref_not_lt b a (ha b hbO)
    · -- truthful flatPref, deviate to flatPref: judged by flatPref, N → N
      subst hPF
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwF, this, hwF] at hev
      obtain ⟨a, _, ha⟩ := hev
      obtain ⟨b, hbN⟩ := hN
      exact flatPref_not_lt b a (ha b hbN)

/-- A `sepRule` is Kelly strategy-proof iff its single forward manipulation event is absent. -/
lemma strategyProofKelly_sepRule_iff (hRf : R ≠ flatPref) :
    StrategyProofKelly (sepRule R O N hO hN) ↔ ¬ KellyManip R O N := by
  set f := sepRule R O N hO hN with hf
  have hwR : f.winners (Function.const Unit R) = O := by
    rw [hf, sepRule_winners_const]; exact if_pos rfl
  have hwF : f.winners (Function.const Unit flatPref) = N := by
    rw [hf, sepRule_winners_const]; exact if_neg (Ne.symm hRf)
  have hmemR : Function.const Unit R ∈ f.domain := Set.mem_insert _ _
  have hmemF : Function.const Unit flatPref ∈ f.domain :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  constructor
  · intro hsp hkel
    have := hsp (Function.const Unit R) hmemR () flatPref
      (by rw [update_unit_const]; exact hmemF)
    rw [update_unit_const, Function.const_apply, hwR, hwF] at this
    exact this hkel
  · intro hno P hP i R' hupd hev
    rcases i with ⟨⟩
    rw [update_unit_const] at hupd hev
    rcases (Set.mem_insert_iff.mp hP) with hPR | hPF
    all_goals rcases (Set.mem_insert_iff.mp hupd) with hR' | hR'
    · -- truthful R, deviate to R: judged by R, O → O
      subst hPR
      rw [Function.const_apply, hwR] at hev
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [this, hwR] at hev
      obtain ⟨hdom, b, hbO, a, haO, hlt⟩ := hev
      exact hlt.2 (hdom a haO b hbO)
    · -- truthful R, deviate to flatPref: judged by R, O → N
      subst hPR
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwR, this, hwF] at hev
      exact hno hev
    · -- truthful flatPref, deviate to R: judged by flatPref, N → O
      subst hPF
      have : Function.const Unit R' = Function.const Unit R := hR'
      rw [Function.const_apply, hwF, this, hwR] at hev
      obtain ⟨_, b, _, a, _, hlt⟩ := hev
      exact flatPref_not_lt b a hlt
    · -- truthful flatPref, deviate to flatPref: judged by flatPref, N → N
      subst hPF
      have : Function.const Unit R' = Function.const Unit flatPref := Set.mem_singleton_iff.mp hR'
      rw [Function.const_apply, hwF, this, hwF] at hev
      obtain ⟨_, b, _, a, _, hlt⟩ := hev
      exact flatPref_not_lt b a hlt

/-! ### The four separating rules

Utilities encode the orderings; `Set` literals over `Fin 3` give the winner sets. -/

/-- Witnesses **optimistic ⇒ pessimistic** and **optimistic ⇒ Kelly** both fail: The rule blocks
the optimistic event (`O = {1,0}`, `N = {1}`, with `1 ≻ 0`) but admits the pessimistic and Kelly
ones. -/
theorem exists_strategyProof_not_pessimistic :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProof f ∧ ¬ StrategyProofPessimistic f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({1, 0} : Set (Fin 3)) ({1} : Set (Fin 3))
    ⟨1, by simp⟩ (Set.singleton_nonempty 1), ?_, ?_⟩
  · -- optimistic event absent: `1` cannot strictly beat itself
    rw [strategyProof_sepRule_iff hRf]
    rintro ⟨b, hbN, hb⟩
    rw [Set.mem_singleton_iff] at hbN; subst hbN
    exact (R.lt_irrefl 1) (hb 1 (by simp))
  · -- pessimistic event present: worst of `{1,0}` is `0`, strictly below every `b ∈ {1}`
    rw [strategyProofPessimistic_sepRule_iff hRf, not_not]
    exact ⟨0, by simp, fun b hb => by
      rw [Set.mem_singleton_iff] at hb; subst hb; rw [hR]; simp⟩

theorem exists_strategyProof_not_kelly :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProof f ∧ ¬ StrategyProofKelly f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({1, 0} : Set (Fin 3)) ({1} : Set (Fin 3))
    ⟨1, by simp⟩ (Set.singleton_nonempty 1), ?_, ?_⟩
  · -- optimistic event absent: `1` cannot strictly beat itself
    rw [strategyProof_sepRule_iff hRf]
    rintro ⟨b, hbN, hb⟩
    rw [Set.mem_singleton_iff] at hbN; subst hbN
    exact (R.lt_irrefl 1) (hb 1 (by simp))
  · -- Kelly event present: `{1}` weakly dominates `{1,0}` with the strict pair `1 ≻ 0`
    rw [strategyProofKelly_sepRule_iff hRf, not_not]
    refine ⟨fun b hb a ha => ?_, 1, by simp, 0, by simp, hlt10⟩
    rw [Set.mem_singleton_iff] at hb; subst hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> · rw [hR]; simp

/-- Witnesses **pessimistic ⇒ optimistic** and **pessimistic ⇒ Kelly** both fail (`O = {0}`,
`N = {0,1}`, with `1 ≻ 0`). -/
theorem exists_pessimistic_not_strategyProof :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProofPessimistic f ∧ ¬ StrategyProof f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({0} : Set (Fin 3)) ({0, 1} : Set (Fin 3))
    (Set.singleton_nonempty 0) ⟨0, by simp⟩, ?_, ?_⟩
  · -- pessimistic event absent: the sole old winner `0` is not beaten by `0 ∈ {0,1}`
    rw [strategyProofPessimistic_sepRule_iff hRf]
    rintro ⟨a, haO, ha⟩
    rw [Set.mem_singleton_iff] at haO; subst haO
    exact (R.lt_irrefl 0) (ha 0 (by simp))
  · -- optimistic event present: `1 ∈ {0,1}` strictly beats the sole old winner `0`
    rw [strategyProof_sepRule_iff hRf, not_not]
    exact ⟨1, by simp, fun a ha => by
      rw [Set.mem_singleton_iff] at ha; subst ha; exact hlt10⟩

theorem exists_pessimistic_not_kelly :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProofPessimistic f ∧ ¬ StrategyProofKelly f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({0} : Set (Fin 3)) ({0, 1} : Set (Fin 3))
    (Set.singleton_nonempty 0) ⟨0, by simp⟩, ?_, ?_⟩
  · -- pessimistic event absent: the sole old winner `0` is not beaten by `0 ∈ {0,1}`
    rw [strategyProofPessimistic_sepRule_iff hRf]
    rintro ⟨a, haO, ha⟩
    rw [Set.mem_singleton_iff] at haO; subst haO
    exact (R.lt_irrefl 0) (ha 0 (by simp))
  · -- Kelly event present: `{0,1}` weakly dominates `{0}` with the strict pair `1 ≻ 0`
    rw [strategyProofKelly_sepRule_iff hRf, not_not]
    refine ⟨fun b hb a ha => ?_, 1, by simp, 0, by simp, hlt10⟩
    rw [Set.mem_singleton_iff] at ha; subst ha
    rw [hR]; simp

/-- Witnesses **Kelly ⇒ optimistic** fails (`O = {1}`, `N = {2,0}`, with `2 ≻ 1 ≻ 0`). -/
theorem exists_kelly_not_strategyProof :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProofKelly f ∧ ¬ StrategyProof f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hlt21 : R.lt 2 1 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({1} : Set (Fin 3)) ({2, 0} : Set (Fin 3))
    (Set.singleton_nonempty 1) ⟨2, by simp⟩, ?_, ?_⟩
  · -- Kelly event absent: weak dominance fails since `0 ∈ {2,0}` is not ≽ `1 ∈ {1}`
    rw [strategyProofKelly_sepRule_iff hRf]
    rintro ⟨hdom, -⟩
    have h01 : R.le 0 1 := hdom 0 (by simp) 1 (by simp)
    rw [hR, preferenceOfUtilityIn_le_iff] at h01
    simp at h01
  · -- optimistic event present: `2 ∈ {2,0}` strictly beats the sole old winner `1`
    rw [strategyProof_sepRule_iff hRf, not_not]
    exact ⟨2, by simp, fun a ha => by
      rw [Set.mem_singleton_iff] at ha; subst ha; exact hlt21⟩

/-- Witnesses **Kelly ⇒ pessimistic** fails (`O = {2,0}`, `N = {1}`, with `2 ≻ 1 ≻ 0`). -/
theorem exists_kelly_not_pessimistic :
    ∃ f : ChoiceFunction Unit (Fin 3), StrategyProofKelly f ∧ ¬ StrategyProofPessimistic f := by
  set R : PreferenceRel (Fin 3) := preferenceOfUtilityIn (fun i : Fin 3 => (i : ℕ)) with hR
  have hlt10 : R.lt 1 0 := by rw [hR]; simp
  have hRf : R ≠ flatPref := fun h => flatPref_not_lt (1 : Fin 3) 0 (h ▸ hlt10)
  refine ⟨sepRule R ({2, 0} : Set (Fin 3)) ({1} : Set (Fin 3))
    ⟨2, by simp⟩ (Set.singleton_nonempty 1), ?_, ?_⟩
  · -- Kelly event absent: weak dominance fails since `1 ∈ {1}` is not ≽ `2 ∈ {2,0}`
    rw [strategyProofKelly_sepRule_iff hRf]
    rintro ⟨hdom, -⟩
    have h12 : R.le 1 2 := hdom 1 (by simp) 2 (by simp)
    rw [hR, preferenceOfUtilityIn_le_iff] at h12
    simp at h12
  · -- pessimistic event present: worst of `{2,0}` is `0`, strictly below every `b ∈ {1}`
    rw [strategyProofPessimistic_sepRule_iff hRf, not_not]
    exact ⟨0, by simp, fun b hb => by
      rw [Set.mem_singleton_iff] at hb; subst hb; exact hlt10⟩

/-- **The three set-valued strategy-proofness variants are pairwise logically independent.** For
each ordered pair of distinct variants there is a (single-voter, three-alternative) rule satisfying
the first but not the second. In particular no single variant implies another — there is no
ordering, and the optimistic notion is not the weakest. (The variants are not jointly independent,
however: Optimistic and pessimistic together imply Kelly, via
`StrategyProof.strategyProofKelly_of_pessimistic`.) The variants coincide only on resolute rules
(`strategyProof_variants_iff_of_resolute`). -/
theorem strategyProof_variants_pairwise_independent :
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProof f ∧ ¬ StrategyProofPessimistic f) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProof f ∧ ¬ StrategyProofKelly f) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProofPessimistic f ∧ ¬ StrategyProof f) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProofPessimistic f ∧ ¬ StrategyProofKelly f) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProofKelly f ∧ ¬ StrategyProof f) ∧
    (∃ f : ChoiceFunction Unit (Fin 3), StrategyProofKelly f ∧ ¬ StrategyProofPessimistic f) :=
  ⟨exists_strategyProof_not_pessimistic, exists_strategyProof_not_kelly,
    exists_pessimistic_not_strategyProof, exists_pessimistic_not_kelly,
    exists_kelly_not_strategyProof, exists_kelly_not_pessimistic⟩

end Econlib.SocialChoice.ChoiceFunction
