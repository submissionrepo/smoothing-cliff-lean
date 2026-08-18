/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Properties of social choice functions

Standard properties for set-valued (non-resolute) social choice functions. The two headline
properties are `StrategyProof` (no voter benefits from misreporting) and `Surjective` (every
alternative is attainable for some profile); these are the hypotheses of Gibbard–Satterthwaite.

Because the rule is set-valued, "benefits from misreporting" depends on how a voter compares
outcome sets. `StrategyProof` is the **optimistic** (max-element / Gärdenfors) extension; the
**pessimistic** (min-element) `StrategyProofPessimistic` and **Kelly** (cautious / elementwise
dominance) `StrategyProofKelly` extensions are also provided (Duggan and Schwartz 2000; Kelly 1977;
Gärdenfors 1976). `Anonymity`, `Neutrality`, and `PositiveResponsiveness` are the conditions
characterizing majority rule on two alternatives (May 1952).

## Main definitions

* `OptimisticManip`, `PessimisticManip`, `KellyManip`: The three set-extension manipulation events
* `StrategyProof`: No voter benefits from unilateral misreport (the optimistic extension)
* `StrategyProofOptimistic`: Optimistic (max-element / Gärdenfors) extension; equals `StrategyProof`
* `StrategyProofPessimistic`: Pessimistic (min-element) extension
* `StrategyProofKelly`: Kelly (cautious / elementwise-dominance) extension
* `Surjective`: Every alternative is a winner under some profile
* `IsDictator`: The winners-set is exactly a single voter's set of most-preferred alternatives
* `Anonymity`: The winners-set is invariant under voter permutations
* `Neutrality`: Relabeling alternatives permutes the winners-set correspondingly
* `PositiveResponsiveness`: A shift toward a tied alternative makes it the sole winner

## Main statements

* `kellyManip_imp_optimistic_or_pessimistic`: The only general implication among the three events
* `StrategyProof.strategyProofKelly_of_pessimistic`: Optimistic and pessimistic jointly imply Kelly
* `strategyProof_variants_iff_of_resolute`: All three variants coincide on resolute rules

## Notes

The three strategy-proofness variants are **pairwise logically independent** for set-valued rules:
No single variant implies another, in either direction, so none is the weakest (the separating
rules are `strategyProof_variants_pairwise_independent` in
`Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`). The optimistic and pessimistic
variants together imply the Kelly variant (`StrategyProof.strategyProofKelly_of_pessimistic`),
because a Kelly manipulation forces an optimistic or a pessimistic one
(`kellyManip_imp_optimistic_or_pessimistic`). All three coincide on resolute (singleton-valued)
rules (`strategyProof_variants_iff_of_resolute`), and the resolute Gibbard–Satterthwaite
development consumes the optimistic notion, with `StrategyProof = StrategyProofOptimistic`.

## References

* Duggan, John, and Thomas Schwartz. 2000. “Strategic Manipulability Without Resoluteness or Shared
  Beliefs: Gibbard-Satterthwaite Generalized.” *Social Choice and Welfare* 17 (1): 85–93.
  [https://doi.org/10.1007/pl00007177](https://doi.org/10.1007/pl00007177).
* Gärdenfors, Peter. 1976. “Manipulation of Social Choice Functions.” *Journal of Economic Theory*
  13 (2): 217–28. [https://doi.org/10.1016/0022-0531(76)90016-8](https://doi.org/10.1016/0022-0531(76)90016-8).
* Kelly, Jerry S. 1977. “Strategy-Proofness and Social Choice Functions Without Singlevaluedness.”
  *Econometrica* 45 (2): 439. [https://doi.org/10.2307/1911220](https://doi.org/10.2307/1911220).
* May, Kenneth O. 1952. “A Set of Independent Necessary and Sufficient Conditions for Simple
  Majority Decision.” *Econometrica* 20 (4): 680. [https://doi.org/10.2307/1907651](https://doi.org/10.2307/1907651).

## Tags

social choice, strategy-proofness, anonymity, neutrality, gibbard-satterthwaite, may's theorem
-/

@[expose] public section

namespace Econlib.SocialChoice.ChoiceFunction

open Econlib.Preferences Econlib.SocialChoice

variable {Voter Alt : Type*}

/-! ### Set-extension manipulation events

A set-valued rule returns a set of winners, so "voter `i` benefits from a unilateral misreport"
is only well-posed once we fix how `i` compares the truthful winners `O` against the misreport
winners `N`, every comparison judged by `i`'s truthful preference `R`. The three standard
set-extensions (Duggan and Schwartz 2000; Kelly 1977; Gärdenfors 1976) name three manipulation
events; the corresponding strategy-proofness variant below is the statement that the event never
occurs on the admissible domain. The events are stated abstractly on `(R, O, N)` so the
(non-)implications among them (`kellyManip_imp_optimistic_or_pessimistic` and the separation
examples in `Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`) are facts about a total
preorder, independent of any particular rule. -/

/-- **Optimistic (max-element / Gärdenfors) manipulation event.** Some misreport winner `b ∈ N` is
strictly preferred to every truthful winner `a ∈ O`: A voter who values a set by its single best
element profits. -/
def OptimisticManip (R : PreferenceRel Alt) (O N : Set Alt) : Prop :=
  ∃ b ∈ N, ∀ a ∈ O, R.lt b a

/-- **Pessimistic (min-element) manipulation event.** Some truthful winner `a ∈ O` is strictly
beaten by every misreport winner `b ∈ N` — equivalently the worst reachable misreport winner
strictly improves on the worst truthful winner: A voter who values a set by its single worst
element profits. -/
def PessimisticManip (R : PreferenceRel Alt) (O N : Set Alt) : Prop :=
  ∃ a ∈ O, ∀ b ∈ N, R.lt b a

/-- **Kelly (cautious / elementwise-dominance) manipulation event.** Every misreport winner `b ∈ N`
is weakly preferred to every truthful winner `a ∈ O`, with at least one strict comparison: The
misreport set weakly set-dominates the truthful set. The weak-dominance conjunct rules in only the
manipulations a maximally cautious voter would undertake; the strictness witness rules out the case
where `N` and `O` are merely indifferent. -/
def KellyManip (R : PreferenceRel Alt) (O N : Set Alt) : Prop :=
  (∀ b ∈ N, ∀ a ∈ O, R.le b a) ∧ (∃ b ∈ N, ∃ a ∈ O, R.lt b a)

/-- **The only general implication among the three events.** A Kelly manipulation forces either an
optimistic or a pessimistic one: If every misreport winner weakly beats every truthful winner and
the two sets are not wholly indifferent, then some misreport winner strictly beats every truthful
winner, or some truthful winner is strictly beaten by every misreport winner. (No other implication
holds — see the separation examples in
`Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`.)

The statement requires no finiteness or extremal-element assumption and holds for arbitrary —
possibly infinite — winner sets. -/
theorem kellyManip_imp_optimistic_or_pessimistic {R : PreferenceRel Alt} {O N : Set Alt}
    (h : KellyManip R O N) : OptimisticManip R O N ∨ PessimisticManip R O N := by
  obtain ⟨hdom, b0, hb0, a0, ha0, hlt⟩ := h
  by_contra hcon
  simp only [not_or, OptimisticManip, PessimisticManip] at hcon
  push Not at hcon
  obtain ⟨hnopt, hnpess⟩ := hcon
  -- ¬optimistic at the strict witness `b₀` yields an old winner `a₁` with `b₀ ⋩ a₁`,
  -- hence `a₁ ~ b₀`.
  obtain ⟨a1, ha1, hna1⟩ := hnopt b0 hb0
  have hle_a1b0 : R.le a1 b0 := by
    by_contra hc; exact hna1 ⟨hdom b0 hb0 a1 ha1, hc⟩
  -- so `a₁ ≽ b₀ ≻ a₀`, giving `a₁ ≻ a₀`.
  have ha1_lt_a0 : R.lt a1 a0 := PreferenceRel.lt_of_le_of_lt R hle_a1b0 hlt
  -- ¬pessimistic at `a₀` yields a new winner `b₁` with `b₁ ⋩ a₀`, hence `a₀ ~ b₁`.
  obtain ⟨b1, hb1, hnb1⟩ := hnpess a0 ha0
  have hle_a0b1 : R.le a0 b1 := by
    by_contra hc; exact hnb1 ⟨hdom b1 hb1 a0 ha0, hc⟩
  -- weak dominance `b₁ ≽ a₁` then chains to `a₀ ≽ a₁`, contradicting `a₁ ≻ a₀`.
  have hle_a0a1 : R.le a0 a1 := R.le_trans a0 b1 a1 hle_a0b1 (hdom b1 hb1 a1 ha1)
  exact ha1_lt_a0.2 hle_a0a1

/-- **Strategy-proofness.** No voter strictly prefers any post-misreport winner over every truthful
winner.

This is the **optimistic** set-valued extension (the max-element / Gärdenfors reading): A voter who
compares outcome sets by their single most-preferred reachable element manipulates exactly when
some misreport winner strictly beats every truthful winner. It is reproduced under the explicit
name `StrategyProofOptimistic` below, and is the notion consumed by the resolute
Gibbard–Satterthwaite development. -/
def StrategyProof [DecidableEq Voter] (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ i : Voter, ∀ R' : PreferenceRel Alt,
    Function.update P i R' ∈ f.domain →
    ¬ OptimisticManip (P i) (f.winners P) (f.winners (Function.update P i R'))

/-! ### Set-valued strategy-proofness variants

Each variant below blocks the corresponding manipulation event (`OptimisticManip`,
`PessimisticManip`, `KellyManip`) on the whole admissible domain. The resolute
Gibbard–Satterthwaite results rely on the optimistic notion. The variants are **pairwise logically
independent** in general — no single variant implies another, so none is the weakest — though the
optimistic and pessimistic variants do jointly imply the Kelly one
(`StrategyProof.strategyProofKelly_of_pessimistic`); and all three coincide on resolute rules. See
`strategyProof_variants_iff_of_resolute` and, for the separations,
`Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`. -/

/-- **Optimistic strategy-proofness** (max-element / Gärdenfors extension; Duggan and Schwartz
2000; Gärdenfors 1976). A voter who ranks outcome sets by their single most-preferred element gains
by misreporting exactly when some misreport winner `b ∈ N` is strictly preferred to every truthful
winner `a ∈ O`. This predicate blocks that manipulation.

This has, by design, the same body as `StrategyProof` (see `strategyProof_iff_optimistic`); the
named form makes the optimistic reading explicit when contrasting it with the pessimistic and Kelly
variants. -/
def StrategyProofOptimistic [DecidableEq Voter] (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ i : Voter, ∀ R' : PreferenceRel Alt,
    Function.update P i R' ∈ f.domain →
    ¬ OptimisticManip (P i) (f.winners P) (f.winners (Function.update P i R'))

/-- The existing `StrategyProof` predicate is the optimistic (max-element / Gärdenfors)
set-extension: The two definitions are definitionally equal. -/
lemma strategyProof_iff_optimistic [DecidableEq Voter] (f : ChoiceFunction Voter Alt) :
    StrategyProof f ↔ StrategyProofOptimistic f := Iff.rfl

/-- **Pessimistic strategy-proofness** (min-element extension; Duggan and Schwartz 2000). A voter
who ranks outcome sets by their single least-preferred element gains by misreporting exactly when
some truthful winner `a ∈ O` is strictly beaten by every misreport winner `b ∈ N` — i.e. the worst
reachable misreport outcome strictly improves on the worst truthful outcome. This predicate blocks
that manipulation. -/
def StrategyProofPessimistic [DecidableEq Voter] (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ i : Voter, ∀ R' : PreferenceRel Alt,
    Function.update P i R' ∈ f.domain →
    ¬ PessimisticManip (P i) (f.winners P) (f.winners (Function.update P i R'))

/-- **Kelly (cautious) strategy-proofness** (Kelly 1977 elementwise-dominance extension). A voter
who only counts a misreport as profitable when the new winner set weakly set-dominates the old
gains exactly when every misreport winner `b ∈ N` is weakly preferred to every truthful winner
`a ∈ O` and at least one of those comparisons is strict. This predicate blocks that manipulation.

The weak-dominance conjunct `∀ b ∈ N, ∀ a ∈ O, (P i).le b a` reads "every new winner is weakly
preferred to every old winner"; the strictness witness `∃ b ∈ N, ∃ a ∈ O, (P i).lt b a` rules out
the case where the two sets are merely indifferent. -/
def StrategyProofKelly [DecidableEq Voter] (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ P ∈ f.domain, ∀ i : Voter, ∀ R' : PreferenceRel Alt,
    Function.update P i R' ∈ f.domain →
    ¬ KellyManip (P i) (f.winners P) (f.winners (Function.update P i R'))

/-- **The optimistic and pessimistic variants jointly imply the Kelly variant.** This is the
rule-level shadow of `kellyManip_imp_optimistic_or_pessimistic`: Blocking both the optimistic and
the pessimistic manipulation on every transition blocks the Kelly one, since a Kelly manipulation
always contains one of the other two. It is the only implication among the variants — no single one
implies another (`strategyProof_variants_pairwise_independent` in
`Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants`), so in particular this joint
implication cannot be split into a one-sided one. -/
theorem StrategyProof.strategyProofKelly_of_pessimistic [DecidableEq Voter]
    {f : ChoiceFunction Voter Alt} (hopt : StrategyProof f) (hpess : StrategyProofPessimistic f) :
    StrategyProofKelly f := by
  intro P hP i R' hupd hkelly
  rcases kellyManip_imp_optimistic_or_pessimistic hkelly with ho | hp
  · exact hopt P hP i R' hupd ho
  · exact hpess P hP i R' hupd hp

/-- **Surjectivity.** Every alternative is a winner of some admissible profile. -/
def Surjective (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ a : Alt, ∃ P, P ∈ f.domain ∧ a ∈ f.winners P

/-- Voter `i` is a choice-function dictator: On every admissible profile the winners-set is exactly
voter `i`'s set of most-preferred alternatives `{a | ∀ b, (P i).le a b}`. This is an equality, not
merely an inclusion: Every winner is `i`-top (winners are among `i`'s best), and every `i`-top
alternative is selected (`i`'s best are all winners). -/
def IsDictator (f : ChoiceFunction Voter Alt) (i : Voter) : Prop :=
  ∀ P ∈ f.domain, f.winners P = {a | ∀ b : Alt, (P i).le a b}

/-- **Anonymity.** Permuting voters does not change the winners-set. -/
def Anonymity [DecidableEq Voter] (f : ChoiceFunction Voter Alt) : Prop :=
  ∀ P : Profile Voter Alt, P ∈ f.domain → ∀ σ : Equiv.Perm Voter,
    (P ∘ σ) ∈ f.domain → f.winners (P ∘ σ) = f.winners P

/-- **Neutrality.** Relabeling alternatives commutes with the choice rule: Applying a permutation
`τ` of `Alt` to every voter's ranking permutes the winners-set by `τ`. -/
def Neutrality (f : ChoiceFunction Voter Alt)
    (apply : Equiv.Perm Alt → Profile Voter Alt → Profile Voter Alt) : Prop :=
  ∀ P : Profile Voter Alt, P ∈ f.domain → ∀ τ : Equiv.Perm Alt,
    apply τ P ∈ f.domain → f.winners (apply τ P) = τ '' (f.winners P)

/-- **Positive responsiveness** (May 1952). If `x` ties or wins under profile `P` (`x ∈ winners P`,
the "tied-or-winning" disjunction) and one voter performs a ceteris paribus shift strictly toward
`x` over `y` — flipping only the `x`-vs-`y` comparison from "not `x ≻ y`" to "`x ≻ y`" while
leaving every other pairwise comparison of that voter's ballot untouched — then `x` is the sole
winner under the updated profile.

The final hypothesis is the ceteris-paribus clause: `R'` agrees with `P i` on every ordered pair
except `(x, y)` and `(y, x)`. Without it the predicate would demand the `{x}` outcome even for
ballot changes that scramble unrelated comparisons, which is strictly stronger than — and
unfaithful to — May's monotonicity axiom. On a two-alternative space the clause is vacuous (only
the `x`-vs-`y` comparison is non-reflexive), so it does not alter the May characterization, which
lives at `Fin 2`. -/
def PositiveResponsiveness [DecidableEq Voter]
    (f : ChoiceFunction Voter Alt) (x y : Alt) : Prop :=
  ∀ P : Profile Voter Alt, P ∈ f.domain → x ∈ f.winners P →
    ∀ i : Voter, ∀ R' : PreferenceRel Alt,
      Function.update P i R' ∈ f.domain →
      ¬ (P i).lt x y → R'.lt x y →
      (∀ a b : Alt, ¬ (a = x ∧ b = y) → ¬ (a = y ∧ b = x) → (R'.le a b ↔ (P i).le a b)) →
      f.winners (Function.update P i R') = {x}

/-! ### The variants coincide on resolute rules

A choice rule is **resolute** when every admissible profile has a singleton winner set; the
resolute Gibbard–Satterthwaite development (`resoluteBorda`, `ChoiceFunction.resoluteOf`) lives
here. On a singleton outcome set the "best", "worst", and "elementwise" readings of a set collapse
to its unique element, so all three set-extensions of strategy-proofness become the same condition.
We take resoluteness as a hypothesis (`∀ P ∈ f.domain, (f.winners P).Subsingleton`) rather than a
new field, so the bridge applies to any rule one can prove single-valued. -/

/-- On a nonempty, single-valued winner set `f.winners P`, both bounded quantifiers over the set
reduce to a statement about its unique element `w`: The set equals `{w}`. This is the workhorse for
the resolute bridge below; it is stated per-profile so it applies equally to the truthful profile
`P` and the misreport `Function.update P i R'`. -/
private lemma eq_singleton_of_resolute {f : ChoiceFunction Voter Alt} {P : Profile Voter Alt}
    (hP : P ∈ f.domain) (hres : ∀ P ∈ f.domain, (f.winners P).Subsingleton) :
    ∃ w, f.winners P = {w} := by
  obtain ⟨w, hw⟩ := f.winners_nonempty P hP
  exact ⟨w, (hres P hP).eq_singleton_of_mem hw⟩

/-- **On resolute (single-valued) rules the three set-valued strategy-proofness extensions
coincide.** Optimistic strategy-proofness (`StrategyProof`) is equivalent to both the pessimistic
and the Kelly variant once every admissible winner set is a singleton: On `O = {wₒ}`, `N = {wₙ}`
each blocked manipulation event reduces to the single comparison `wₙ ≻ wₒ`, so the predicates have
the same content. This is why the resolute Gibbard–Satterthwaite results may freely consume the
optimistic notion. -/
theorem strategyProof_variants_iff_of_resolute [DecidableEq Voter] {f : ChoiceFunction Voter Alt}
    (hres : ∀ P ∈ f.domain, (f.winners P).Subsingleton) :
    (StrategyProof f ↔ StrategyProofPessimistic f) ∧
      (StrategyProof f ↔ StrategyProofKelly f) := by
  have key : ∀ P ∈ f.domain, ∀ (i : Voter) (R' : PreferenceRel Alt),
      Function.update P i R' ∈ f.domain →
      ∃ wo wn,
        (OptimisticManip (P i) (f.winners P) (f.winners (Function.update P i R'))
          ↔ (P i).lt wn wo) ∧
        (PessimisticManip (P i) (f.winners P) (f.winners (Function.update P i R'))
          ↔ (P i).lt wn wo) ∧
        (KellyManip (P i) (f.winners P) (f.winners (Function.update P i R'))
          ↔ (P i).lt wn wo) := by
    intro P hP i R' hupd
    obtain ⟨wo, hO⟩ := eq_singleton_of_resolute hP hres
    obtain ⟨wn, hN⟩ := eq_singleton_of_resolute hupd hres
    refine ⟨wo, wn, ?_, ?_, ?_⟩
    · rw [hO, hN]; simp [OptimisticManip, Set.mem_singleton_iff]
    · rw [hO, hN]; simp [PessimisticManip, Set.mem_singleton_iff]
    · -- The weak-dominance conjunct `wₙ ≽ wₒ` is implied by `wₙ ≻ wₒ`,
      -- so the Kelly conjunction collapses to the strict comparison.
      rw [hO, hN]
      simp only [KellyManip, Set.mem_singleton_iff, forall_eq, exists_eq_left]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  refine ⟨?_, ?_⟩
  · constructor
    · intro h P hP i R' hupd hpess
      obtain ⟨wo, wn, hopt, hpe, _⟩ := key P hP i R' hupd
      exact h P hP i R' hupd (hopt.2 (hpe.1 hpess))
    · intro h P hP i R' hupd hopt
      obtain ⟨wo, wn, ho, hpe, _⟩ := key P hP i R' hupd
      exact h P hP i R' hupd (hpe.2 (ho.1 hopt))
  · constructor
    · intro h P hP i R' hupd hkel
      obtain ⟨wo, wn, hopt, _, hk⟩ := key P hP i R' hupd
      exact h P hP i R' hupd (hopt.2 (hk.1 hkel))
    · intro h P hP i R' hupd hopt
      obtain ⟨wo, wn, ho, _, hk⟩ := key P hP i R' hupd
      exact h P hP i R' hupd (hk.2 (ho.1 hopt))

/-- **Optimistic and pessimistic strategy-proofness coincide on resolute rules.** A direct
corollary of `strategyProof_variants_iff_of_resolute`, stated in the named (optimistic) form: When
every admissible winner set is a singleton, blocking the best-element manipulation is the same as
blocking the worst-element manipulation. -/
lemma StrategyProofOptimistic.pessimistic_of_resolute [DecidableEq Voter]
    {f : ChoiceFunction Voter Alt}
    (hres : ∀ P ∈ f.domain, (f.winners P).Subsingleton) :
    StrategyProofOptimistic f ↔ StrategyProofPessimistic f :=
  (strategyProof_iff_optimistic f).symm.trans (strategyProof_variants_iff_of_resolute hres).1

/-- **Optimistic and Kelly strategy-proofness coincide on resolute rules.** The Kelly companion of
`StrategyProofOptimistic.pessimistic_of_resolute`. -/
lemma StrategyProofOptimistic.kelly_of_resolute [DecidableEq Voter]
    {f : ChoiceFunction Voter Alt}
    (hres : ∀ P ∈ f.domain, (f.winners P).Subsingleton) :
    StrategyProofOptimistic f ↔ StrategyProofKelly f :=
  (strategyProof_iff_optimistic f).symm.trans (strategyProof_variants_iff_of_resolute hres).2

end Econlib.SocialChoice.ChoiceFunction
