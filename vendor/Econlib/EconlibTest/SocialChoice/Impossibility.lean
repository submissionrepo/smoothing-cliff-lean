/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import EconlibExamples.SocialChoice.ArrowDictatorship
import EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable
import EconlibExamples.SocialChoice.MajorityRuleMay
import Mathlib

/-!
# Impossibility-Theorem Non-Vacuity Checks (Arrow, Gibbard–Satterthwaite, May)

Compile-time semantic witnesses for the internal scaffolding of the three impossibility-theorem
files `Econlib/SocialChoice/{Arrow, GibbardSatterthwaite, May}.lean`. Impossibility theorems have a
characteristic failure mode: A *hypothesis that is never discharged on a concrete profile that
actually satisfies it* is vacuously safe — a bug in the hypothesis set (too strong to ever hold, or
pointing the wrong way) goes unnoticed because the headline theorem only ever consumes it
abstractly. Each witness here therefore **discharges the hypotheses on real data**, hand-tabulated
electorates whose Borda scores / majority counts are spelled out before the statement, and checks
that the conclusion is the one the name claims.

The witnessed rules and electorates are imported from the `EconlibExamples` siblings (`projSWF`,
`resoluteBorda`, `majorityRule`, and their concrete profiles) so that this file adds *only*
internal-scaffolding coverage, not new economic content.

## What each chunk catches

### Chunk 1 — Arrow (`decisive_univ` + three-rank pivot machinery)

* **`decisive_univ`** — exercised against `projSWF`, which genuinely satisfies `WeakPareto`,
  confirming the universe coalition is decisive over a concrete pair on the concrete electorate. A
  direction reversal in the `IsDecisive` predicate (society prefers `y` to `x` instead of `x` to
  `y`) would surface here.
* **`StrictPref.threeRank` / `threeRank_lt_xy` / `threeRank_lt_yz` / `threeRank_lt_xz`** — the
  three-rank `x ≻ y ≻ z` construction on voter 1's Condorcet ballot, confirming the constructed
  ordering is exactly the one the names claim (top = `x`, middle = `y`, bottom = `z`).
* **`topRank_lt_of_ne` / `bottomRank_lt_of_ne`** — `x`-at-top / `x`-at-bottom direction checks.
* **`strictRefPref_isStrict`** — the canonical index-ordered reference preference is strict.

### Chunk 2 — Gibbard–Satterthwaite (the deepest gap)

The **headline finding**: Every Arrow-reduction bridge lemma
(`weakPareto_welfareFunctionOfChoiceFunction`, `iia_welfareFunctionOfChoiceFunction`,
`aggregateOfChoiceFunction_le`, `choiceFunction_dictator_of_welfareFunction_dictator`,
`choiceFunction_winner_isTop_of_welfareFunction_dictator`, `maskin_step_strict_top`,
`chooseWinner_eq_or_lt`, `pareto_phase_x_at_top`, `pareto_property`, `winner_lift_in_pair`,
`winner_liftTriple_in_triple`) carries `hSP : f.StrategyProof` as a hypothesis, and the bridge
*constructor* `welfareFunctionOfChoiceFunction` itself takes `hSP`/`hSur` as construction
parameters. For `resoluteBorda` the strategy-proofness hypothesis is provably *unsatisfiable*
(`resoluteBorda_not_strategyProof`) — so on that rule these lemmas can never fire. The non-vacuity
content is therefore split:

* **Resolute-winner API with no `hSP`** (`chooseWinner_mem`, `winners_eq_singleton`,
  `chooseWinner_eq_iff`) — discharged directly on `resoluteBorda`. `chooseWinner_truthful_eq_y`
  *recomputes* the Borda score table `![4,5,0]` locally (`truthful_score_{x,y,z}`) rather than
  importing the example anchor `truthful_winner_is_y`.
* **Lift scaffolding with no `hSP`** (`liftPairOf_*`, `liftTripleOf_*`, `hybridProfile_*`,
  `StrictPref.liftPairOf`, `liftPair_mem_domain`, `update_mem_strictDomain`,
  `profile_isStrict_of_mem_domain`) — discharged on `resoluteBorda`'s strict domain. The triple-lift
  witnesses on `Fin 3` are supplemented by a **proper-subset** `Fin 4` triple lift
  (`liftTripleOf_outsider_below_*`, `liftTripleOf_demotes_native_top`,
  `liftTripleOf_inside_order_preserved`) that genuinely exercises the "outsider strictly below the
  lifted triple" behavior — untestable when the triple is the whole `Fin 3` universe.
* **The `hSP`-gated bridge** — discharged on a genuinely strategy-proof rule `dictatorRule0`
  ("elect voter 0's top alternative"), built here as a `resoluteOf` rule on the same strict domain.
  The bridge then constructs a real SWF, `weakPareto_welfareFunctionOfChoiceFunction` /
  `iia_welfareFunctionOfChoiceFunction` hold on real data, and
  `choiceFunction_dictator_of_welfareFunction_dictator` recovers voter 0 as the choice-function
  dictator. Its premise `bridge_swf_dictator0` is proved **directly** from `dictatorRule0`'s
  definition (via `dictator0_liftPair_winner` + `aggregateOfChoiceFunction_le`), *not* via the
  transfer lemma itself — so the transfer is genuinely consumed, not circular. The phase/deviation
  witnesses use the **decisive voter 0**: `bridge_pareto_phase_x_at_top` moves voter 0's *bottom*
  alternative `2` to the top (flipping the winner `0 → 2`, `bridge_pareto_phase_changes_winner`),
  and `bridge_chooseWinner_eq_or_lt` has voter 0 reverse their ballot so the winner genuinely
  changes (`0 → 2`) and the *non-equality* disjunct of `chooseWinner_eq_or_lt` is exercised. The
  *failure* of `hSP` for `resoluteBorda` is recorded as `resoluteBorda_bridge_hyp_fails`, the
  explicit non-vacuity content.

### Chunk 3 — May (the hard converse + the tie boundary)

* **The hard converse on a non-defeq wrapper.** `wrapMajRule` phrases the weak-majority test through
  `¬ (… < …)` rather than `… ≤ …`, so its winner sets are *not* definitionally `majorityRule`'s. We
  prove it satisfies anonymity, neutrality, and positive responsiveness (transported through the
  pointwise agreement `wrapMajWinners_eq`) and feed it to `winners_eq_majorityRule` /
  `may_characterization`: the conclusion `wrapMajRule.winners P = majorityRule.winners P` is then a
  genuine, non-`rfl` equality (`converse_winners_eq_majorityRule`, anchored to `{0}` on `strictMaj`
  via `converse_wrapMajRule_strictMaj_eq_zero`), and `may_characterization_recovers_axioms` uses the
  backward `.mpr` to reconstruct the axioms from that agreement. The four `majRule_*` axiom theorems
  remain as the easy-direction discharge.
* **`majorityRule_strict_majority_wins`** on a concrete `Fin 2` profile with a hand-counted strict
  majority, and **`tied_profile_winners_univ`** on an exact tie — checking the elected set flips
  correctly across the tie boundary (where a `<` vs `≤` bug in `majorityCount` hides).
* **`majWinners` / `mem_majWinners_iff` / `may_strict_majority_wins_aux`** witnessed on the same
  data.

## Data

All electorates reuse the `EconlibExamples` definitions:

* Chunk 1: The Condorcet cycle `Profile.P` is reconstructed locally as `condorcet` over `Fin 3`
  voters / `Fin 3` alternatives (`a=0, b=1, c=2`).
* Chunk 2: `resoluteBorda`, `truthfulP`, `splitP` from `GibbardSatterthwaiteManipulable`.
* Chunk 3: Two `Fin 3`-voter `Fin 2`-alternative profiles — `strictMaj` (a 2-vs-1 strict majority
  for alternative `0`) and `tied` (an exact 0–0 indifferent tie).
-/

noncomputable section

namespace EconlibTest.SocialChoice.Impossibility

open Econlib.Preferences Econlib.SocialChoice

/-! ## Chunk 1 — Arrow: `decisive_univ` and the three-rank pivot machinery

The electorate is the Condorcet cycle on three voters and three alternatives
(`a=0, b=1, c=2`):

* voter 0: `a ≻ b ≻ c`  (utilities `[2, 1, 0]`)
* voter 1: `b ≻ c ≻ a`  (utilities `[0, 2, 1]`)
* voter 2: `c ≻ a ≻ b`  (utilities `[1, 0, 2]`)

This is the standard Arrow/Condorcet electorate; it is strict, hence universally admissible. -/

namespace Arrow

open EconlibExamples.SocialChoice.ArrowDictatorship

/-- Utility matrix for the Condorcet cycle. Row `i` is voter `i`'s utility vector. -/
private abbrev utilCond : Fin 3 → Fin 3 → ℕ :=
  ![ ![2, 1, 0],   -- voter 0: a ≻ b ≻ c
     ![0, 2, 1],   -- voter 1: b ≻ c ≻ a
     ![1, 0, 2] ]  -- voter 2: c ≻ a ≻ b

/-- The Condorcet cycle profile, on the `projSWF` electorate (three voters, three alternatives). -/
private abbrev condorcet : Profile (Fin 3) (Fin 3) :=
  fun i => preferenceOfUtilityIn (utilCond i)

-- Alternative labels, for self-documenting witnesses.
private abbrev a : Fin 3 := 0
private abbrev b : Fin 3 := 1
private abbrev c : Fin 3 := 2

/-- **`decisive_univ` against `projSWF`.** The projection rule genuinely satisfies `WeakPareto`
(`proj_weakPareto`), so the universe coalition is decisive over the pair `(a, b)`: On every
admissible profile where *every* voter strictly prefers `a` to `b`, society does too. This
discharges `decisive_univ`'s `hPar` hypothesis on a real rule and confirms the conclusion's
direction is `a ≻ b` (society agrees with the unanimity), not its reverse. -/
theorem projSWF_decisive_univ_a_b :
    IsDecisive projSWF (Finset.univ : Finset (Fin 3)) a b :=
  decisive_univ proj_weakPareto a b

/-- **Direction check of `decisive_univ` on concrete data.** Feed the unanimous-`a ≻ b` profile
(every voter ranks `a` strictly above `b`) into the decisive coalition and read off society's
verdict: Society strictly prefers `a` to `b`. A reversal in `IsDecisive` (concluding `b ≻ a`) would
make this `projSWF_decisive_univ_a_b` application yield the wrong strict comparison and fail the
`decide`. -/
theorem projSWF_decisive_univ_direction :
    (projSWF.aggregate (fun _ => preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ))).lt a b := by
  -- Every voter strictly prefers `a` to `b` under the unanimous ballot `a ≻ b ≻ c`.
  refine projSWF_decisive_univ_a_b _ (Set.mem_univ _) (fun i _ => ?_)
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 1
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- The three-rank construction `threeRank (condorcet 1) a b c` applied to voter 1's ballot
`b ≻ c ≻ a`. By construction this places `a` at the top, `b` next, and `c` at the bottom —
overriding voter 1's native ordering. -/
private abbrev cond1_abc : PreferenceRel (Fin 3) := threeRank (condorcet 1) a b c

/-- **`threeRank_lt_xy`** — in `threeRank R a b c`, `a` is strictly above `b`. Direction check: The
*first* argument after `R` is the new top alternative. -/
theorem threeRank_lt_a_b : cond1_abc.lt a b :=
  threeRank_lt_xy (by decide) (by decide)

/-- **`threeRank_lt_yz`** — in `threeRank R a b c`, `b` is strictly above `c`. The *middle*
argument sits above the *bottom* argument. -/
theorem threeRank_lt_b_c : cond1_abc.lt b c :=
  threeRank_lt_yz (by decide) (by decide) (by decide)

/-- **`threeRank_lt_xz`** — in `threeRank R a b c`, `a` is strictly above `c` (top above bottom).
Together with the two lemmas above this confirms the constructed order is exactly `a ≻ b ≻ c`. -/
theorem threeRank_lt_a_c : cond1_abc.lt a c :=
  threeRank_lt_xz (by decide) (by decide)

/-- **`StrictPref.threeRank`** — the three-rank lift of a strict ballot is strict. Voter 1's
Condorcet ballot is strict (injective utilities `[0,2,1]`), so the constructed `a ≻ b ≻ c` ranking
is a genuine strict order. -/
theorem cond1_abc_isStrict : StrictPref cond1_abc :=
  (strictPref_preferenceOfUtilityIn
    (by decide : Function.Injective (![0, 2, 1] : Fin 3 → ℕ))).threeRank a b c

/-- **`topRank_lt_of_ne`** — `topRank R a` puts `a` strictly above every other alternative. Here
voter 1's ballot with `a` moved to the top: `a ≻ b`. -/
theorem topRank_lt_a_b : (topRank (condorcet 1) a).lt a b :=
  topRank_lt_of_ne (condorcet 1) (by decide)

/-- **`bottomRank_lt_of_ne`** — `bottomRank R a` puts every other alternative strictly above `a`.
Here voter 1's ballot with `a` moved to the bottom: `b ≻ a` (direction: The *other* alternative is
on top). -/
theorem bottomRank_lt_b_a : (bottomRank (condorcet 1) a).lt b a :=
  bottomRank_lt_of_ne (condorcet 1) (by decide)

/-- **`strictRefPref_isStrict`** — the canonical index-ordered reference preference on `Fin 3` is
strict (it is induced by the injective `Fintype.equivFin`). This is the seed used in
`group_contraction_strict`. -/
theorem strictRefPref_isStrict_fin3 : StrictPref (strictRefPref : PreferenceRel (Fin 3)) :=
  strictRefPref_isStrict

end Arrow

/-! ## Chunk 2 — Gibbard–Satterthwaite

All witnesses reuse `resoluteBorda` (Borda count + lexicographic tie-break, strict domain,
three voters / three alternatives) and its hand-tabulated profiles from
`GibbardSatterthwaiteManipulable`. Recall the truthful electorate `truthfulP`:

* voter 0: `x ≻ y ≻ z`  (Borda contributions: `x=2, y=1, z=0`)
* voter 1: `y ≻ x ≻ z`  (`y=2, x=1, z=0`)
* voter 2: `y ≻ x ≻ z`  (`y=2, x=1, z=0`)

Total Borda scores: `x = 4`, `y = 5`, `z = 0`, so the resolute winner is `y = 1`
(`truthful_winner_is_y`, no tie-break needed). -/

namespace GS

open EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable

/-- Local alias for the example's resolute Borda rule (disambiguates from
`Econlib.SocialChoice.resoluteBorda`, to which it is definitionally equal). -/
private abbrev resBorda : ChoiceFunction (Fin 3) (Fin 3) :=
  EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable.resoluteBorda

/-- Resoluteness witness, reused below: Every admissible profile has a subsingleton winner set. -/
private theorem resBorda_resolute :
    ∀ P ∈ resBorda.domain, (resBorda.winners P).Subsingleton :=
  resoluteBorda_resolute

/-! ### Resolute-winner API (no strategy-proofness needed) -/

/-- **`chooseWinner_mem`** on `resoluteBorda` at `truthfulP`. The canonical winner extracted from
the nonempty singleton winner-set is a genuine member of `winners truthfulP`. -/
theorem chooseWinner_mem_truthful :
    chooseWinner resBorda resBorda_resolute truthfulP truthfulP_strict
      ∈ resBorda.winners truthfulP :=
  chooseWinner_mem resBorda resBorda_resolute truthfulP truthfulP_strict

/-- **`winners_eq_singleton`** on `resoluteBorda` at `truthfulP`. The winner-set is literally the
singleton of the chosen winner — the resolute structure made explicit on real data. -/
theorem winners_eq_singleton_truthful :
    resBorda.winners truthfulP
      = {chooseWinner resBorda resBorda_resolute truthfulP truthfulP_strict} :=
  winners_eq_singleton resBorda resBorda_resolute truthfulP truthfulP_strict

/-! #### Local Borda tabulation for `truthfulP`

We recompute the Borda scores *in this file* rather than importing `truthful_winner_is_y`, so the
arithmetic table is checked here. Recall `truthfulP`'s ballots and per-alternative beaten-sets
(an alternative's individual Borda score = the number of alternatives it strictly beats):

| Voter | ballot (utilities)     | beats under `x=0` | beats under `y=1` | beats under `z=2` |
| ----- | ---------------------- | ----------------- | ----------------- | ----------------- |
| 0     | `x ≻ y ≻ z` (`[2,1,0]`)| `{y,z}` → 2       | `{z}` → 1         | `∅` → 0           |
| 1     | `y ≻ x ≻ z` (`[1,2,0]`)| `{z}` → 1         | `{x,z}` → 2       | `∅` → 0           |
| 2     | `y ≻ x ≻ z` (`[1,2,0]`)| `{z}` → 1         | `{x,z}` → 2       | `∅` → 0           |

Totals: `bordaScore x = 4`, `bordaScore y = 5`, `bordaScore z = 0`, so `y = 1` is the strict
maximizer and the resolute winner. -/

/-- Local recomputation: `bordaScore truthfulP 0 = 4` (`x` beats `{y,z},{z},{z}` = `2+1+1`). -/
private lemma truthful_score_x : bordaScore truthfulP 0 = 4 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)) 0
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 0
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 0 = 4
  rw [bordaScoreOf_utility_eq_card _ 0 {1, 2} (by decide),
    bordaScoreOf_utility_eq_card _ 0 {2} (by decide)]
  decide

/-- Local recomputation: `bordaScore truthfulP 1 = 5` (`y` beats `{z},{x,z},{x,z}` = `1+2+2`). -/
private lemma truthful_score_y : bordaScore truthfulP 1 = 5 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)) 1
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 1
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 1 = 5
  rw [bordaScoreOf_utility_eq_card _ 1 {2} (by decide),
    bordaScoreOf_utility_eq_card _ 1 {0, 2} (by decide)]
  decide

/-- Local recomputation: `bordaScore truthfulP 2 = 0` (`z` beats nobody). -/
private lemma truthful_score_z : bordaScore truthfulP 2 = 0 := by
  rw [bordaScore, Fin.sum_univ_three]
  change bordaScoreOf (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)) 2
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 2
      + bordaScoreOf (preferenceOfUtilityIn (![1, 2, 0] : Fin 3 → ℕ)) 2 = 0
  rw [bordaScoreOf_utility_eq_card _ 2 ∅ (by decide),
    bordaScoreOf_utility_eq_card _ 2 ∅ (by decide)]
  decide

/-- **`chooseWinner_eq_iff` + locally recomputed Borda table.** The chosen winner of `truthfulP` is
`y = 1`. We derive `scoreWinner (bordaScore truthfulP) = 1` from the local score table
`![4, 5, 0]` (`truthful_score_{x,y,z}`) via `scoreWinner_eq_of_strict_max`, *without* importing
`truthful_winner_is_y` — so the arithmetic anchor is independently checked here. Membership of `1`
in `winners truthfulP = {scoreWinner (bordaScore truthfulP)}` then forces `chooseWinner … = 1`. -/
theorem chooseWinner_truthful_eq_y :
    chooseWinner resBorda resBorda_resolute truthfulP truthfulP_strict = 1 := by
  -- The resolute winner is the strict score-maximizer `1`, computed from the local table.
  have hwin : scoreWinner (bordaScore truthfulP) = 1 := by
    refine scoreWinner_eq_of_strict_max (bordaScore truthfulP) ![4, 5, 0] (fun c => ?_)
      (by decide)
    fin_cases c
    · exact truthful_score_x
    · exact truthful_score_y
    · exact truthful_score_z
  rw [chooseWinner_eq_iff resBorda resBorda_resolute truthfulP truthfulP_strict 1,
    resoluteBorda_winners, Set.mem_singleton_iff]
  exact hwin.symm

/-! ### Lift scaffolding on the strict domain (no strategy-proofness needed)

These exercise the pair/triple/hybrid lift machinery directly on `resoluteBorda`'s strict
domain. `truthfulP`'s voter-0 ballot `x ≻ y ≻ z` is the strict reference ballot. -/

/-- **`profile_isStrict_of_mem_domain`** — domain membership implies strictness, since
`resoluteBorda.domain = strictDomain`. Recovered on `truthfulP`. -/
theorem truthful_isStrict_via_domain : Profile.IsStrict truthfulP :=
  profile_isStrict_of_mem_domain (f := resBorda) rfl truthfulP_strict

/-- **`StrictPref.liftPairOf`** — lifting the unordered pair `{x, y}` to the top of voter 0's
strict ballot preserves strictness. -/
theorem liftPairOf_voter0_isStrict :
    StrictPref (liftPairOf (truthfulP 0) 0 1) :=
  (strictPref_preferenceOfUtilityIn
    (by decide : Function.Injective (![2, 1, 0] : Fin 3 → ℕ))).liftPairOf 0 1

/-- **`liftPairOf_lt_xy` direction check.** In `liftPairOf (truthfulP 0) x y`, the lifted pair
keeps voter 0's native `x`-vs-`y` order: `x ≻ y` iff voter 0 had `x ≻ y`. Voter 0's ballot is
`x ≻ y ≻ z` (utilities `[2,1,0]`), so this holds. -/
theorem liftPairOf_voter0_lt_xy :
    (liftPairOf (truthfulP 0) 0 1).lt 0 1 := by
  rw [liftPairOf_lt_xy]
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 1
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- **`liftPairOf_lt_top_outside` direction check.** Both lifted alternatives sit strictly above
any outside alternative. With `{x, y}` lifted, `x ≻ z` regardless of voter 0's native ranking of
`z`. -/
theorem liftPairOf_voter0_x_above_z :
    (liftPairOf (truthfulP 0) 0 1).lt 0 2 :=
  liftPairOf_lt_top_outside (by decide) (by decide)

/-- **`liftPair_mem_domain`** — lifting a pair across the whole profile keeps it in the strict
domain. -/
theorem liftPair_truthful_mem_domain :
    liftPair truthfulP 0 1 ∈ resBorda.domain :=
  liftPair_mem_domain (f := resBorda) rfl truthfulP_strict 0 1

/-- **`StrictPref.liftTripleOf`** — lifting a triple to the top of voter 0's strict ballot
preserves strictness. -/
theorem liftTripleOf_voter0_isStrict :
    StrictPref (liftTripleOf (truthfulP 0) 0 1 2) :=
  (strictPref_preferenceOfUtilityIn
    (by decide : Function.Injective (![2, 1, 0] : Fin 3 → ℕ))).liftTripleOf 0 1 2

/-- **`liftTripleOf_lt_top` direction check.** Inside the lifted triple, the native order is
preserved: `x ≻ y` because voter 0 ranks `x ≻ y`. -/
theorem liftTripleOf_voter0_lt_xy :
    (liftTripleOf (truthfulP 0) 0 1 2).lt 0 1 := by
  rw [liftTripleOf_lt_top (by tauto) (by tauto)]
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 1
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- **`liftTriple_mem_domain`** — lifting a triple across the whole profile keeps it strict. -/
theorem liftTriple_truthful_mem_domain :
    liftTriple truthfulP 0 1 2 ∈ resBorda.domain :=
  liftTriple_mem_domain (f := resBorda) rfl truthfulP_strict 0 1 2

/-! #### Proper-subset triple lift (`Fin 4`): the outsider really sits below the triple

The triple-lift witnesses above all use the triple `{0,1,2}` on `Fin 3`, which is the *whole*
alternative set, so the "outside alternatives are strictly below the lifted triple" behavior is
never exercised (there is no outsider). We add a `Fin 4` witness with a *proper* triple `{0,1,2}`
and outside alternative `3`.

The seed ballot `outsiderTop = preferenceOfUtilityIn (![0, 1, 2, 3] : Fin 4 → ℕ)` ranks
`3 ≻ 2 ≻ 1 ≻ 0` — so alternative `3` is the native *favorite*. Lifting `{0,1,2}` to the top must
override that and bury `3` strictly below all of `{0,1,2}`. Within the triple the native order
`2 ≻ 1 ≻ 0` is preserved. -/

/-- The `Fin 4` seed ballot `3 ≻ 2 ≻ 1 ≻ 0`: alternative `3` (the outsider for the triple `{0,1,2}`)
is the native top. -/
private abbrev outsiderTop : PreferenceRel (Fin 4) :=
  preferenceOfUtilityIn (![0, 1, 2, 3] : Fin 4 → ℕ)

/-- **`liftTripleOf_lt_top_outside` on a proper subset.** After lifting `{0,1,2}` to the top, the
outsider `3` is strictly *below* each triple member — even though `3` was the native favorite. This
is the behavior the full-set `Fin 3` witnesses cannot test. -/
theorem liftTripleOf_outsider_below_0 :
    (liftTripleOf outsiderTop 0 1 2).lt 0 3 :=
  liftTripleOf_lt_top_outside (by tauto) (by decide)

/-- The outsider `3` is strictly below the triple member `2` as well (and symmetrically `1`),
confirming all three triple members dominate the outsider. -/
theorem liftTripleOf_outsider_below_2 :
    (liftTripleOf outsiderTop 0 1 2).lt 2 3 :=
  liftTripleOf_lt_top_outside (by tauto) (by decide)

/-- **The native top `3` is genuinely demoted.** In the seed ballot `3 ≻ 0` (utility `3 > 0`), but
in the lifted ballot the order flips to `0 ≻ 3`: the lift overrides the native ranking for the
outsider. This is the load-bearing check that the proper-subset triple is doing real work. -/
theorem liftTripleOf_demotes_native_top :
    outsiderTop.lt 3 0 ∧ ¬ (liftTripleOf outsiderTop 0 1 2).lt 3 0 := by
  refine ⟨?_, ?_⟩
  · -- native: `3 ≻ 0` since `u 3 = 3 > 0 = u 0`
    rw [preferenceOfUtilityIn_lt_iff]; decide
  · -- lifted: `3` (outsider) is not strictly above `0` (triple member)
    exact fun h => h.2 (liftTripleOf_le_top_outside (by tauto) (by decide))

/-- **`liftTripleOf_lt_top` on the proper subset.** Within the lifted triple the native order is
preserved: `2 ≻ 1` (utility `2 > 1`) survives the lift. -/
theorem liftTripleOf_inside_order_preserved :
    (liftTripleOf outsiderTop 0 1 2).lt 2 1 := by
  rw [liftTripleOf_lt_top (by tauto) (by tauto)]
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- **`StrictPref.liftTripleOf` on the proper subset.** Lifting a proper triple of a strict ballot
stays strict (`![0,1,2,3]` is injective). -/
theorem liftTripleOf_outsider_isStrict :
    StrictPref (liftTripleOf outsiderTop 0 1 2) :=
  (strictPref_preferenceOfUtilityIn
    (by decide : Function.Injective (![0, 1, 2, 3] : Fin 4 → ℕ))).liftTripleOf 0 1 2

/-- **`update_mem_strictDomain`** — replacing voter 0's strict ballot with another strict ballot
(`buryY = x ≻ z ≻ y`) keeps the profile strict. This is the strictness companion of the GS
manipulation step. -/
theorem update_truthful_buryY_isStrict :
    Profile.IsStrict (Function.update truthfulP 0 buryY) :=
  update_mem_strictDomain (truthful_isStrict_via_domain) 0
    (strictPref_preferenceOfUtilityIn (by decide : Function.Injective (![2, 0, 1] : Fin 3 → ℕ)))

/-- **`hybridProfile_empty`** — the hybrid of `truthfulP` and `splitP` over the empty coalition is
`truthfulP` (nobody switched to the second profile yet). -/
theorem hybrid_empty_eq_truthful :
    hybridProfile truthfulP splitP ∅ = truthfulP :=
  hybridProfile_empty truthfulP splitP

/-- **`hybridProfile_univ`** — the hybrid over the full coalition is `splitP` (everybody
switched). -/
theorem hybrid_univ_eq_split :
    hybridProfile truthfulP splitP Finset.univ = splitP :=
  hybridProfile_univ truthfulP splitP

/-- **`hybridProfile_isStrict`** — interpolating between two strict profiles stays strict, for any
coalition `S`. Witnessed at `S = {0}` (voter 0 has switched to `splitP`, voters 1 and 2 still on
`truthfulP`). -/
theorem hybrid_isStrict_at_zero :
    (hybridProfile truthfulP splitP {0}).IsStrict :=
  hybridProfile_isStrict truthfulP_strict splitP_strict {0}

/-- **`hybridProfile_mem_domain`** — the hybrid is admissible whenever both endpoints are. -/
theorem hybrid_mem_domain_at_zero :
    hybridProfile truthfulP splitP {0} ∈ resBorda.domain :=
  hybridProfile_mem_domain (f := resBorda) rfl truthfulP_strict splitP_strict {0}

/-! ### The strategy-proofness barrier — the headline non-vacuity finding

Every Arrow-reduction bridge lemma (and the bridge constructor
`welfareFunctionOfChoiceFunction` itself) carries `hSP : f.StrategyProof`. The
Gibbard–Satterthwaite example proves `resoluteBorda_not_strategyProof`, so on `resoluteBorda`
*none* of these lemmas can ever fire — the hypothesis is unsatisfiable. That is exactly the
non-vacuity worry for an impossibility theorem, so we record the obstruction explicitly: A profile
and a misreport on which the optimistic-manipulation event holds (voter 0 buries `y` to turn the
sincere winner `y` into the strictly preferred `x`), which is precisely the negation of
`StrategyProof`. -/

/-- **The bridge hypothesis fails for `resoluteBorda` — explicit witness.** `resoluteBorda` is
*not* strategy-proof: Voter 0, whose truthful winner is `y`, misreports `buryY = x ≻ z ≻ y` to make
the winner `x`, which they strictly prefer. So every bridge lemma requiring `hSP : f.StrategyProof`
(`weakPareto_welfareFunctionOfChoiceFunction`, `iia_welfareFunctionOfChoiceFunction`,
`aggregateOfChoiceFunction_le`, the two dictator-transfer lemmas, `maskin_step_strict_top`,
`chooseWinner_eq_or_lt`, `pareto_phase_x_at_top`, `pareto_property`, `winner_lift_in_pair`,
`winner_liftTriple_in_triple`) has an *unsatisfiable* hypothesis on this rule. They are discharged
positively on the genuinely strategy-proof `dictatorRule0` below instead. -/
theorem resoluteBorda_bridge_hyp_fails : ¬ resBorda.StrategyProof :=
  resoluteBorda_not_strategyProof

/-! ### A genuinely strategy-proof rule for the `hSP`-gated bridge

`dictatorRule0` elects voter 0's strict top alternative (the resolute rule scoring each
alternative by voter 0's *individual* Borda score `bordaScoreOf (P 0)`). On a strict ballot the top
alternative strictly maximizes the individual Borda score, so the winner is voter 0's top. This
rule is resolute, surjective, and — because society always hands voter 0 their genuine favorite —
strategy proof. It is therefore the natural carrier for the `hSP`-gated bridge lemmas, on which
their hypotheses are *satisfiable*. (Gibbard–Satterthwaite is not violated: `dictatorRule0` is a
dictatorship, exactly the escape hatch the theorem permits.) -/
def dictatorRule0 : ChoiceFunction (Fin 3) (Fin 3) :=
  ChoiceFunction.resoluteOf (strictDomain (Fin 3) (Fin 3)) (fun P => bordaScoreOf (P 0))

/-- The winner of `dictatorRule0` on `P` is voter 0's individual Borda-best. -/
private lemma dictator0_winner (P : Profile (Fin 3) (Fin 3)) :
    dictatorRule0.winners P = {scoreWinner (bordaScoreOf (P 0))} := rfl

/-- `dictatorRule0`'s domain is the strict domain. -/
private lemma dictator0_domain : dictatorRule0.domain = strictDomain (Fin 3) (Fin 3) := rfl

/-- `dictatorRule0` is resolute. -/
private theorem dictator0_resolute :
    ∀ P ∈ dictatorRule0.domain, (dictatorRule0.winners P).Subsingleton :=
  ChoiceFunction.resoluteOf_resolute _ _

/-- **Key structural fact.** On a strict ballot, the `dictatorRule0` winner is voter 0's *top*: It
is weakly above every alternative under `P 0`. If some `a` were strictly above the winner `w`
(`a ≻ w` under voter 0), then `bordaScoreOf (P 0) w < bordaScoreOf (P 0) a` by
`bordaScoreOf_lt_of_lt`, contradicting `w`'s score-maximality (`scoreWinner_max`). -/
theorem dictator0_winner_isTop {P : Profile (Fin 3) (Fin 3)} (hP : P ∈ dictatorRule0.domain)
    (a : Fin 3) : (P 0).le (scoreWinner (bordaScoreOf (P 0))) a := by
  set w := scoreWinner (bordaScoreOf (P 0)) with hw
  by_contra hnle
  -- Strictness + totality: `¬ w ≤ a` means `a ≻ w`.
  have hstrict : StrictPref (P 0) := (profile_isStrict_of_mem_domain (f := dictatorRule0) rfl hP) 0
  have hlt : (P 0).lt a w := by
    rcases (P 0).le_total w a with h | h
    · exact absurd h hnle
    · exact ⟨h, hnle⟩
  have hscore : bordaScoreOf (P 0) w < bordaScoreOf (P 0) a := bordaScoreOf_lt_of_lt (P 0) hlt
  exact absurd (scoreWinner_max (bordaScoreOf (P 0)) a) (not_le.mpr (hw ▸ hscore))

/-- **The `dictatorRule0` winner equals voter 0's strict top.** If voter 0 strictly prefers `w` to
every other alternative, then `w` is the rule's winner (it strictly maximizes voter 0's individual
Borda score). The reusable identification behind the surjectivity and Maskin witnesses. -/
theorem dictator0_winner_eq {P : Profile (Fin 3) (Fin 3)} {w : Fin 3}
    (hw : ∀ b : Fin 3, b ≠ w → (P 0).lt w b) :
    scoreWinner (bordaScoreOf (P 0)) = w :=
  scoreWinner_eq_of_strict_max _ (bordaScoreOf (P 0)) (fun _ => rfl)
    (fun b hb => bordaScoreOf_lt_of_lt (P 0) (hw b hb))

/-- **Surjectivity of `dictatorRule0`.** Every alternative wins for some strict profile — take the
unanimous spotlight profile where voter 0 ranks it first (utility `3` for `a`, its index `≤ 2` for
the rivals). -/
theorem dictator0_surjective : dictatorRule0.Surjective := by
  intro a
  -- The unanimous spotlight profile is strict and ranks `a` first for voter 0.
  refine ⟨fun _ => preferenceOfUtilityIn (fun b : Fin 3 => if b = a then 3 else (b : ℕ)),
    ?_, ?_⟩
  · exact isStrict_of_injective_utilities (fun _ => by fin_cases a <;> decide)
  · rw [dictator0_winner, Set.mem_singleton_iff]
    -- Voter 0 ranks `a` strictly first (score 3 vs ≤ 2), so `a` is the individual Borda-best.
    refine (dictator0_winner_eq
      (P := fun _ => preferenceOfUtilityIn (fun b : Fin 3 => if b = a then 3 else (b : ℕ)))
      (w := a) (fun b hb => ?_)).symm
    rw [preferenceOfUtilityIn_lt_iff]
    fin_cases a <;> (fin_cases b <;> simp_all)

/-- **`dictatorRule0` is strategy-proof.** Society always elects voter 0's genuine top alternative,
so no voter can profit by misreporting. The optimistic-manipulation event on the singleton winner
sets `{w}` (truthful) and `{w'}` (misreport) reduces to `(P i).lt w' w` — but `w` is voter 0's top
(`dictator0_winner_isTop`), so for voter 0 the new winner `w'` cannot be strictly above `w`; for
voters `i ≠ 0` the score (hence the winner) does not change at all, so `w' = w`. -/
theorem dictator0_strategyProof : dictatorRule0.StrategyProof := by
  intro P hP i R' hP'
  -- Unfold the optimistic-manipulation event on the two singleton winner sets.
  rw [dictator0_winner, dictator0_winner]
  rintro ⟨bw, hbw, hmanip⟩
  rw [Set.mem_singleton_iff] at hbw
  subst hbw
  have hold := hmanip _ (Set.mem_singleton _)
  -- `hold : (P i).lt w' w` where `w` is voter 0's top and `w'` the misreport winner.
  by_cases hi0 : i = 0
  · -- Voter 0: the misreport winner `w'` would be strictly above voter 0's true top `w` — absurd.
    subst hi0
    exact hold.2 (dictator0_winner_isTop hP _)
  · -- Voter `i ≠ 0`: the score depends only on voter 0, unchanged by the update, so `w' = w`.
    have heq : (Function.update P i R') 0 = P 0 := Function.update_of_ne (Ne.symm hi0) _ _
    rw [heq] at hold
    exact hold.2 ((P i).le_refl _)

/-! ### The `hSP`-gated bridge, discharged on `dictatorRule0`

With `dictatorRule0` resolute, surjective, strategy-proof and on the strict domain, every
bridge hypothesis is satisfiable, so the Arrow-reduction lemmas fire on real data. -/

/-- **`weakPareto_welfareFunctionOfChoiceFunction`** — the SWF the bridge constructs from
`dictatorRule0` satisfies Weak Pareto. Discharges all four bridge hypotheses (`hRes`, `hDomEq`,
`hSP`, `hSur`) on a real rule. -/
theorem bridge_weakPareto :
    (welfareFunctionOfChoiceFunction dictatorRule0 dictator0_resolute rfl
      dictator0_strategyProof dictator0_surjective).WeakPareto :=
  weakPareto_welfareFunctionOfChoiceFunction dictator0_resolute rfl
    dictator0_strategyProof dictator0_surjective

/-- **`iia_welfareFunctionOfChoiceFunction`** — the constructed SWF satisfies IIA. -/
theorem bridge_iia :
    (welfareFunctionOfChoiceFunction dictatorRule0 dictator0_resolute rfl
      dictator0_strategyProof dictator0_surjective).IIA :=
  iia_welfareFunctionOfChoiceFunction dictator0_resolute rfl
    dictator0_strategyProof dictator0_surjective

/-- **`aggregateOfChoiceFunction_le`** — the social `le` of the constructed SWF unfolds to the
pair-lift characterization, here on the strict profile `truthfulP'` (voter 0 ranks `x ≻ y ≻ z`). -/
theorem bridge_aggregate_le (u v : Fin 3) :
    (aggregateOfChoiceFunction dictatorRule0 dictator0_resolute rfl
        dictator0_strategyProof dictator0_surjective truthfulP).le u v ↔
      u = v ∨ u ∈ dictatorRule0.winners (liftPair truthfulP u v) :=
  aggregateOfChoiceFunction_le dictator0_resolute rfl dictator0_strategyProof
    dictator0_surjective (truthfulP_strict) u v

/-- **The `dictatorRule0` winner of a pair-lift is voter 0's preferred member of the pair.** If
voter 0 strictly prefers `x` to `y` (`(P 0).lt x y`), then after lifting `{x, y}` to the top of
every ballot, voter 0's ballot has `x` as its strict top (`x ≻ y` is preserved by
`liftPairOf_lt_xy`, and `x` beats every outsider by `liftPairOf_lt_top_outside`), so the dictator
elects `x`: `dictatorRule0.winners (liftPair P x y) = {x}`. This is the structural fact that lets us
read off the bridge SWF's dictatorship *directly* from `dictatorRule0`'s definition, with no appeal
to the choice-function transfer lemma. -/
private theorem dictator0_liftPair_winner {P : Profile (Fin 3) (Fin 3)} {x y : Fin 3}
    (hxy : (P 0).lt x y) :
    dictatorRule0.winners (liftPair P x y) = {x} := by
  rw [dictator0_winner]
  congr 1
  -- `x` is voter 0's strict top in the lifted ballot, so it is the individual Borda-best.
  refine dictator0_winner_eq (P := liftPair P x y) (w := x) (fun b hb => ?_)
  change (liftPairOf (P 0) x y).lt x b
  rcases eq_or_ne b y with rfl | hby
  · -- `b = y`: the native `x ≻ y` ranking is preserved by the lift.
    rw [liftPairOf_lt_xy]; exact hxy
  · -- `b ∉ {x, y}`: both lifted alternatives sit strictly above every outsider.
    exact liftPairOf_lt_top_outside hb hby

/-- **The bridge SWF has voter 0 as a welfare-function dictator — proved directly.** We unfold the
`IsDictator` obligation `(P 0).lt x y → (aggregate P).lt x y` through `aggregateOfChoiceFunction_le`
and discharge each side with `dictator0_liftPair_winner`: the social `le x y` holds because `x` is
the pair-lift winner, and `le y x` fails because the (swapped, hence identical) pair-lift winner is
`x ≠ y`. This consumes only `dictatorRule0`'s own definition, *not*
`choiceFunction_dictator_of_welfareFunction_dictator`, so the transfer lemma below is genuinely
tested rather than used to prove its own premise. -/
private theorem bridge_swf_dictator0 :
    (welfareFunctionOfChoiceFunction dictatorRule0 dictator0_resolute rfl
      dictator0_strategyProof dictator0_surjective).IsDictator 0 := by
  intro P hP x y hxy
  -- `hP : P ∈ welfareFunction.domain = dictatorRule0.domain`.
  have hPdom : P ∈ dictatorRule0.domain := hP
  have hxy_ne : x ≠ y := hxy.2 ∘ (fun h => h ▸ (P 0).le_refl x)
  refine ⟨?_, ?_⟩
  · -- social `le x y`: `x` is the pair-lift winner `{x}`.
    rw [show (welfareFunctionOfChoiceFunction dictatorRule0 dictator0_resolute rfl
        dictator0_strategyProof dictator0_surjective).aggregate
        = aggregateOfChoiceFunction dictatorRule0 dictator0_resolute rfl
          dictator0_strategyProof dictator0_surjective from rfl,
      aggregateOfChoiceFunction_le dictator0_resolute rfl dictator0_strategyProof
        dictator0_surjective hPdom x y]
    right
    rw [dictator0_liftPair_winner hxy]; rfl
  · -- social `¬ le y x`: the (swapped) pair-lift winner is `x`, so `y ∉ {x}`.
    rw [show (welfareFunctionOfChoiceFunction dictatorRule0 dictator0_resolute rfl
        dictator0_strategyProof dictator0_surjective).aggregate
        = aggregateOfChoiceFunction dictatorRule0 dictator0_resolute rfl
          dictator0_strategyProof dictator0_surjective from rfl,
      aggregateOfChoiceFunction_le dictator0_resolute rfl dictator0_strategyProof
        dictator0_surjective hPdom y x]
    rintro (hyx | hymem)
    · exact hxy_ne hyx.symm
    · rw [liftPair_swap, dictator0_liftPair_winner hxy, Set.mem_singleton_iff] at hymem
      exact hxy_ne hymem.symm

/-- **`choiceFunction_dictator_of_welfareFunction_dictator`** — a welfare-function dictator of the
bridge SWF is a choice-function dictator of `dictatorRule0`. The premise `bridge_swf_dictator0` is
proved *independently* (directly from `dictatorRule0`'s definition, not via this transfer lemma), so
this genuinely consumes the transfer: it recovers voter 0 as the choice-function dictator, an
*equality* of winner sets that is strictly more than the welfare-function form. -/
theorem bridge_dictator_transfer : dictatorRule0.IsDictator 0 :=
  choiceFunction_dictator_of_welfareFunction_dictator dictator0_resolute rfl
    dictator0_strategyProof dictator0_surjective 0 bridge_swf_dictator0

/-- **`choiceFunction_winner_isTop_of_welfareFunction_dictator`** — under the bridge SWF dictator,
every choice-function winner is voter 0's top. Discharged on `truthfulP`. -/
theorem bridge_winner_isTop :
    ∀ w ∈ dictatorRule0.winners truthfulP, ∀ a : Fin 3, (truthfulP 0).le w a :=
  choiceFunction_winner_isTop_of_welfareFunction_dictator dictator0_resolute rfl
    dictator0_strategyProof dictator0_surjective 0 bridge_swf_dictator0 truthfulP truthfulP_strict

/-- **`maskin_step_strict_top`** — when a voter raises the winner `w` to a strict top in their
ballot, the strategy-proof rule keeps electing `w`. Discharged on `dictatorRule0`: Voter 1 raises
`dictatorRule0`'s winner `0` (voter 0's top) to a strict top in their own ballot; the winner is
unchanged because it depends only on voter 0. -/
theorem bridge_maskin_step :
    chooseWinner dictatorRule0 dictator0_resolute
        (Function.update truthfulP 1 (preferenceOfUtilityIn (![2, 0, 1] : Fin 3 → ℕ)))
        (update_mem_strictDomain (truthful_isStrict_via_domain) 1
          (strictPref_preferenceOfUtilityIn (by decide))) = 0 := by
  -- The winner of `dictatorRule0` on the truthful profile is voter 0's top `0`.
  have hwin0 : (0 : Fin 3) ∈ dictatorRule0.winners truthfulP := by
    rw [dictator0_winner, Set.mem_singleton_iff]
    refine (dictator0_winner_eq (fun b hb => ?_)).symm
    change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 b
    rw [preferenceOfUtilityIn_lt_iff]
    fin_cases b <;> simp_all
  exact maskin_step_strict_top dictator0_resolute dictator0_strategyProof truthfulP_strict 1
    (preferenceOfUtilityIn (![2, 0, 1] : Fin 3 → ℕ)) _ 0 hwin0 (fun a ha => by
      change (preferenceOfUtilityIn (![2, 0, 1] : Fin 3 → ℕ)).lt 0 a
      rw [preferenceOfUtilityIn_lt_iff]
      fin_cases a <;> simp_all)

/-- **`winner_lift_in_pair`** — after lifting the pair `{x, y}` to the top, the strategy-proof rule
elects one of `{x, y}`. Discharged on `dictatorRule0` and `truthfulP` for the pair `{0, 1}`. -/
theorem bridge_winner_lift_in_pair :
    dictatorRule0.winners (liftPair truthfulP 0 1) ⊆ {0, 1} :=
  winner_lift_in_pair dictator0_resolute rfl dictator0_strategyProof dictator0_surjective
    truthfulP_strict 0 1 (by decide)

/-- **`winner_liftTriple_in_triple`** — after lifting the triple `{x, y, z}` to the top, the winner
lies in `{x, y, z}`. On `Fin 3` the triple `{0,1,2}` is the *whole* alternative set, so this
inclusion is automatically the universe and tests nothing about outsiders; the genuine
"outsider strictly below the lifted triple" behavior is instead checked by the `Fin 4`
proper-subset witnesses above (`liftTripleOf_outsider_below_*`, `liftTripleOf_demotes_native_top`).
We keep this as the API-shape check for the `dictatorRule0` bridge and strengthen it next. -/
theorem bridge_winner_liftTriple_in_triple :
    dictatorRule0.winners (liftTriple truthfulP 0 1 2) ⊆ {0, 1, 2} :=
  winner_liftTriple_in_triple dictator0_resolute rfl dictator0_strategyProof
    dictator0_surjective truthfulP_strict 0 1 2

/-- **The concrete triple-lift winner is `0`.** Strengthening the trivial subset above: lifting the
(full) triple `{0,1,2}` to the top preserves voter 0's native order `0 ≻ 1 ≻ 2`, so `0` stays voter
0's top and the dictator elects exactly `{0}` — not merely "something in `{0,1,2}`". A tie-break or
score bug that elected `1` or `2` would fail here even though it would survive the subset check. -/
theorem bridge_winner_liftTriple_eq_zero :
    dictatorRule0.winners (liftTriple truthfulP 0 1 2) = {0} := by
  rw [dictator0_winner]
  congr 1
  refine dictator0_winner_eq (P := liftTriple truthfulP 0 1 2) (w := 0) (fun b hb => ?_)
  change (liftTripleOf (truthfulP 0) 0 1 2).lt 0 b
  -- `b ∈ {1, 2}` (the triple), where the native `0 ≻ b` order is preserved.
  rw [liftTripleOf_lt_top (by tauto) (by fin_cases b <;> tauto)]
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 b
  rw [preferenceOfUtilityIn_lt_iff]
  fin_cases b <;> simp_all

/-- **`pareto_phase_x_at_top`** — moving alternative `x` to the top of every ballot makes `x` a
winner. Discharged for `x = 2` on `truthfulP`: voter 0's truthful ballot is `0 ≻ 1 ≻ 2`, so `2` is
voter 0's *bottom* — moving it to the top genuinely changes voter 0's (decisive) ballot, exercising
the phase-change machinery. (Using `x = 0`, voter 0's existing top, would leave the decisive ballot
untouched and test nothing.) -/
theorem bridge_pareto_phase_x_at_top :
    (2 : Fin 3) ∈ dictatorRule0.winners (fun i => moveToTop (truthfulP i) 2) :=
  pareto_phase_x_at_top dictator0_resolute rfl dictator0_strategyProof dictator0_surjective
    truthfulP_strict 2

/-- **The phase change is real: the winner flips from `0` to `2`.** Before moving `2` to the top the
`dictatorRule0` winner is `0` (voter 0's truthful top, `bridge_winner_liftTriple_eq_zero`'s analog),
and `2 ≠ 0`. So `bridge_pareto_phase_x_at_top` genuinely changed the elected alternative —
confirming voter 0's ballot, not just an inert outer ballot, was moved. -/
theorem bridge_pareto_phase_changes_winner :
    (2 : Fin 3) ∈ dictatorRule0.winners (fun i => moveToTop (truthfulP i) 2) ∧
      (2 : Fin 3) ∉ dictatorRule0.winners truthfulP := by
  refine ⟨bridge_pareto_phase_x_at_top, ?_⟩
  -- The truthful winner is voter 0's top `0`, so `2 ∉ {0}`.
  rw [dictator0_winner, Set.mem_singleton_iff]
  -- `scoreWinner (bordaScore… truthfulP 0) = 0` since voter 0 ranks `0` strictly first.
  have hwin0 : scoreWinner (bordaScoreOf (truthfulP 0)) = 0 := by
    refine dictator0_winner_eq (P := truthfulP) (fun b hb => ?_)
    change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 b
    rw [preferenceOfUtilityIn_lt_iff]
    fin_cases b <;> simp_all
  rw [hwin0]; decide

/-- **`pareto_property`** — if every voter strictly prefers `x` to `y`, then `y` is not a winner.
Discharged on a profile where all three voters rank `0 ≻ 1`: The unanimous ballot `0 ≻ 1 ≻ 2`. -/
theorem bridge_pareto_property :
    (1 : Fin 3) ∉ dictatorRule0.winners
      (fun _ => preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)) := by
  refine pareto_property dictator0_resolute rfl dictator0_strategyProof dictator0_surjective
    (isStrict_of_injective_utilities (fun _ => by decide)) 0 1 (fun i => ?_)
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 1
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- **Voter 0's winner-changing misreport** `devR0 = preferenceOfUtilityIn ![0,1,2]` (`2 ≻ 1 ≻ 0`).
This is voter 0's *reversal* of their truthful `0 ≻ 1 ≻ 2` ballot, so it moves `dictatorRule0`'s
winner from `0` to `2`. (Voter 1, used in the original witness, is ignored by `dictatorRule0` and
would leave the winner unchanged — landing only in the trivial equality disjunct.) -/
private abbrev devR0 : PreferenceRel (Fin 3) := preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)

private theorem devR0_strict : StrictPref devR0 :=
  strictPref_preferenceOfUtilityIn (by decide : Function.Injective (![0, 1, 2] : Fin 3 → ℕ))

/-- The misreport profile `Function.update truthfulP 0 devR0` is strict, hence admissible. -/
private theorem dev_mem_domain :
    Function.update truthfulP 0 devR0 ∈ dictatorRule0.domain :=
  update_mem_strictDomain truthful_isStrict_via_domain 0 devR0_strict

/-- The truthful `dictatorRule0` winner is voter 0's top `0`. -/
private theorem chooseWinner_truthful_eq_zero :
    chooseWinner dictatorRule0 dictator0_resolute truthfulP truthfulP_strict = 0 := by
  rw [chooseWinner_eq_iff dictatorRule0 dictator0_resolute truthfulP truthfulP_strict 0,
    dictator0_winner, Set.mem_singleton_iff]
  refine (dictator0_winner_eq (P := truthfulP) (fun b hb => ?_)).symm
  change (preferenceOfUtilityIn (![2, 1, 0] : Fin 3 → ℕ)).lt 0 b
  rw [preferenceOfUtilityIn_lt_iff]; fin_cases b <;> simp_all

/-- The misreport `dictatorRule0` winner is voter 0's *new* top `2` (voter 0 now ranks `2 ≻ 1 ≻ 0`).
The winner genuinely moved from `0` to `2`. -/
private theorem chooseWinner_dev_eq_two :
    chooseWinner dictatorRule0 dictator0_resolute (Function.update truthfulP 0 devR0)
      dev_mem_domain = 2 := by
  rw [chooseWinner_eq_iff dictatorRule0 dictator0_resolute _ dev_mem_domain 2,
    dictator0_winner, Set.mem_singleton_iff]
  refine (dictator0_winner_eq (P := Function.update truthfulP 0 devR0) (fun b hb => ?_)).symm
  rw [Function.update_self]
  change (preferenceOfUtilityIn (![0, 1, 2] : Fin 3 → ℕ)).lt 2 b
  rw [preferenceOfUtilityIn_lt_iff]; fin_cases b <;> simp_all

/-- **`chooseWinner_eq_or_lt` landing in the *non-equality* disjunct.** Discharged on
`dictatorRule0` where **voter 0** (the decisive voter) reverses their ballot. The winner genuinely
changes from `0` to `2` (`chooseWinner_truthful_eq_zero`, `chooseWinner_dev_eq_two`), so the
equality disjunct is *false* and the witness exercises the strategy-proofness conjunct: voter 0 did
not truthfully rank the new winner `2` above the old winner `0` (`¬ (truthfulP 0).lt 2 0`, since
truthfully `0 ≻ 2`), and the misreport does not rank the old winner `0` above the new `2`
(`¬ devR0.lt 0 2`, since `2 ≻ 0` under `devR0`). A sign error in either non-deviation conjunct would
surface here. -/
theorem bridge_chooseWinner_eq_or_lt :
    ¬ (truthfulP 0).lt 2 0 ∧ ¬ devR0.lt 0 2 := by
  have hor := chooseWinner_eq_or_lt dictator0_resolute dictator0_strategyProof truthfulP_strict 0
    devR0 dev_mem_domain
  simp only [chooseWinner_truthful_eq_zero, chooseWinner_dev_eq_two] at hor
  rcases hor with heq | hlt
  · -- equality disjunct is false: `0 ≠ 2`
    exact absurd heq (by decide)
  · exact hlt

end GS

/-! ## Chunk 3 — May's theorem

Two profiles over three voters and two alternatives (`Fin 2`, alternatives `0` and `1`):

**`strictMaj` — a 2-vs-1 strict majority for alternative `0`:**

* voter 0: `0 ≻ 1`  (utilities `[1, 0]`)
* voter 1: `0 ≻ 1`  (utilities `[1, 0]`)
* voter 2: `1 ≻ 0`  (utilities `[0, 1]`)

Majority counts: `majorityCount strictMaj 0 1 = 2` (voters 0, 1), `majorityCount strictMaj 1 0 = 1`
(voter 2). Since `otherFin2 0 = 1`, the strict-majority hypothesis
`majorityCount (otherFin2 0) 0 < majorityCount 0 (otherFin2 0)` reads `1 < 2` — alternative `0`
wins outright: `winners = {0}`.

**`tied` — an exact 0–0 tie (all voters indifferent):**

* all three voters: `0 ~ 1`  (utilities `[0, 0]`)

Majority counts: `majorityCount tied 0 1 = 0 = majorityCount tied 1 0` — an exact tie, so *both*
alternatives win: `winners = {0, 1}`. The two profiles sit on opposite sides of the tie boundary
where a `<`-vs-`≤` bug in `majorityCount` would hide. -/

namespace May

open EconlibExamples.SocialChoice.MajorityRuleMay

/-- Local alias for the example's majority rule (disambiguates from
`Econlib.SocialChoice.majorityRule`, to which it is definitionally equal). -/
private abbrev majRule : ChoiceFunction (Fin 3) (Fin 2) :=
  EconlibExamples.SocialChoice.MajorityRuleMay.majorityRule

/-- 2-vs-1 strict-majority profile for alternative `0`: Voters 0, 1 rank `0 ≻ 1`, voter 2 the
reverse. -/
private def strictMaj : Profile (Fin 3) (Fin 2) :=
  ![ preferenceOfUtilityIn (![1, 0] : Fin 2 → ℕ),   -- voter 0: 0 ≻ 1
     preferenceOfUtilityIn (![1, 0] : Fin 2 → ℕ),   -- voter 1: 0 ≻ 1
     preferenceOfUtilityIn (![0, 1] : Fin 2 → ℕ) ]  -- voter 2: 1 ≻ 0

/-- Exact-tie profile: Every voter is indifferent between the two alternatives. -/
private def tied : Profile (Fin 3) (Fin 2) :=
  fun _ => preferenceOfUtilityIn (![0, 0] : Fin 2 → ℕ)

/-! ### The four axiom theorems, discharged and fed to the hard converse -/

/-- **`majorityRule_full_domain`** — every profile is admissible under majority rule. -/
theorem majRule_full_domain : ∀ Q : Profile (Fin 3) (Fin 2), Q ∈ majRule.domain :=
  majorityRule_full_domain

/-- **`majorityRule_anonymity`** — permuting voters does not change the winners. -/
theorem majRule_anonymity : majRule.Anonymity := majorityRule_anonymity

/-- **`majorityRule_neutrality`** — relabeling the two alternatives commutes with majority rule. -/
theorem majRule_neutrality : majRule.Neutrality relabelProfile := majorityRule_neutrality

/-- **`majorityRule_positiveResponsiveness`** — a strict shift toward a tied/winning alternative
makes it the unique winner. -/
theorem majRule_positiveResponsiveness :
    ∀ x y : Fin 2, majRule.PositiveResponsiveness x y :=
  majorityRule_positiveResponsiveness

/-! ### A non-defeq wrapper rule, so the hard converse proves something non-trivial

The earlier draft fed `majRule` itself into `winners_eq_majorityRule`, making the conclusion
`majRule.winners P = majRule.winners P` — a tautology that exercises neither the hard converse nor
the backward direction of the iff. We instead build `wrapMajRule`, a rule whose `winners` body is
*syntactically different* from `majWinners` (it phrases the weak-majority test through `¬ … < …`
rather than `… ≤ …`), so its winner sets are **not** definitionally `majorityRule`'s. We then prove
`wrapMajRule` satisfies the three May axioms (by transporting `majorityRule`'s axioms through the
pointwise agreement `wrapMajWinners P = majWinners P`), and feed it to the hard converse — whose
conclusion `wrapMajRule.winners P = majorityRule.winners P` is now a genuine, non-`rfl` equality. -/

/-- The wrapper's winner set, phrased via `¬ (… < …)` instead of `… ≤ …`. By `not_lt` this is
pointwise equal to `majWinners`, but it is not the same syntactic body. -/
private def wrapMajWinners (P : Profile (Fin 3) (Fin 2)) : Set (Fin 2) :=
  { x | ¬ majorityCount P x (otherFin2 x) < majorityCount P (otherFin2 x) x }

/-- **Pointwise agreement** `wrapMajWinners P = majWinners P`, via `not_lt`. This is a *theorem*,
not `rfl`: the two sets are extensionally equal but built from different predicates. -/
private theorem wrapMajWinners_eq (P : Profile (Fin 3) (Fin 2)) :
    wrapMajWinners P = majWinners P := by
  ext x
  rw [wrapMajWinners, Set.mem_setOf_eq, mem_majWinners_iff, not_lt]

/-- The non-defeq wrapper majority rule: full domain, winners `wrapMajWinners`. Its winner sets
coincide with `majorityRule`'s only up to the proved `wrapMajWinners_eq`, never definitionally. -/
private def wrapMajRule : ChoiceFunction (Fin 3) (Fin 2) where
  domain := Set.univ
  winners := wrapMajWinners
  winners_nonempty := by
    intro P _
    rw [wrapMajWinners_eq]
    exact (majorityRule (Voter := Fin 3)).winners_nonempty P (Set.mem_univ _)

private theorem wrapMajRule_winners (P : Profile (Fin 3) (Fin 2)) :
    wrapMajRule.winners P = wrapMajWinners P := rfl

private theorem wrapMajRule_full_domain :
    ∀ Q : Profile (Fin 3) (Fin 2), Q ∈ wrapMajRule.domain :=
  fun _ => Set.mem_univ _

/-- **The wrapper satisfies anonymity** — transported from `majorityRule_anonymity` through the
pointwise agreement. -/
private theorem wrapMajRule_anonymity : wrapMajRule.Anonymity := by
  intro P _ σ _
  rw [wrapMajRule_winners, wrapMajRule_winners, wrapMajWinners_eq, wrapMajWinners_eq]
  exact majorityRule_anonymity P (majorityRule_full_domain P) σ (majorityRule_full_domain _)

/-- **The wrapper satisfies neutrality** — transported from `majorityRule_neutrality`. -/
private theorem wrapMajRule_neutrality : wrapMajRule.Neutrality relabelProfile := by
  intro P _ τ _
  rw [wrapMajRule_winners, wrapMajWinners_eq]
  rw [show τ '' wrapMajRule.winners P = τ '' majWinners P by
    rw [wrapMajRule_winners, wrapMajWinners_eq]]
  exact majorityRule_neutrality P (majorityRule_full_domain P) τ (majorityRule_full_domain _)

/-- **The wrapper satisfies positive responsiveness** — transported from
`majorityRule_positiveResponsiveness`. -/
private theorem wrapMajRule_positiveResponsiveness :
    ∀ x y : Fin 2, wrapMajRule.PositiveResponsiveness x y := by
  intro x y P _ hx i R' _ hnlt hlt hcp
  rw [wrapMajRule_winners, wrapMajWinners_eq] at hx ⊢
  exact majorityRule_positiveResponsiveness x y P (majorityRule_full_domain P) hx i R'
    (majorityRule_full_domain _) hnlt hlt hcp

/-- **The hard converse `winners_eq_majorityRule`, fed a genuinely different rule.** `wrapMajRule`
is not definitionally `majorityRule`, yet it satisfies the three axioms, so the converse forces
`wrapMajRule.winners strictMaj = majorityRule.winners strictMaj` — a non-trivial equality
(`= {0}`, by `strictMaj_winner_is_zero` below). This exercises the hard converse direction, not a
`rfl`. -/
theorem converse_winners_eq_majorityRule :
    wrapMajRule.winners strictMaj = (Econlib.SocialChoice.majorityRule (Voter := Fin 3)).winners
      strictMaj :=
  winners_eq_majorityRule wrapMajRule wrapMajRule_anonymity wrapMajRule_neutrality
    wrapMajRule_positiveResponsiveness wrapMajRule_full_domain strictMaj

/-- **The full `may_characterization` iff on the non-defeq wrapper.** The three May axioms hold for
`wrapMajRule` *iff* it agrees with `majorityRule` on every profile. Here the right side
`∀ P, wrapMajRule.winners P = majorityRule.winners P` is a genuine pointwise-agreement claim (not
`rfl`, since `wrapMajRule ≠ majorityRule` definitionally), so both directions of the iff are
non-trivial. -/
theorem may_characterization_holds :
    (wrapMajRule.Anonymity ∧ wrapMajRule.Neutrality relabelProfile
        ∧ ∀ x y : Fin 2, wrapMajRule.PositiveResponsiveness x y)
      ↔ ∀ P : Profile (Fin 3) (Fin 2),
          wrapMajRule.winners P = (Econlib.SocialChoice.majorityRule (Voter := Fin 3)).winners P :=
  Econlib.SocialChoice.may_characterization wrapMajRule wrapMajRule_full_domain

/-- **The backward direction `.mpr` recovers the axioms.** From the (non-trivial) pointwise
agreement of `wrapMajRule` with `majorityRule`, `may_characterization.mpr` reconstructs the three
axioms — exercising the easy direction of the iff on a rule that is not syntactically majority rule.
The agreement hypothesis is discharged via `wrapMajWinners_eq` (`wrapMajRule.winners = majWinners =
majorityRule.winners`). -/
theorem may_characterization_recovers_axioms :
    wrapMajRule.Anonymity ∧ wrapMajRule.Neutrality relabelProfile
      ∧ ∀ x y : Fin 2, wrapMajRule.PositiveResponsiveness x y :=
  may_characterization_holds.mpr (fun P => by
    rw [wrapMajRule_winners, wrapMajWinners_eq]
    rfl)

/-! ### The tie boundary: Strict majority vs exact tie -/

/-- The two majority counts of `strictMaj`, hand-counted: `0` is preferred to `1` by voters 0 and 1
(count `2`), `1` is preferred to `0` by voter 2 (count `1`). -/
private lemma strictMaj_count_0_1 : majorityCount strictMaj 0 1 = 2 := by
  rw [majorityCount_eq_card strictMaj 0 1 ({0, 1} : Finset (Fin 3)) (fun i => ?_)]
  · decide
  · fin_cases i <;>
      simp [strictMaj, preferenceOfUtilityIn_lt_iff]

private lemma strictMaj_count_1_0 : majorityCount strictMaj 1 0 = 1 := by
  rw [majorityCount_eq_card strictMaj 1 0 ({2} : Finset (Fin 3)) (fun i => ?_)]
  · decide
  · fin_cases i <;>
      simp [strictMaj, preferenceOfUtilityIn_lt_iff]

/-- **`majorityRule_strict_majority_wins` on `strictMaj`.** A hand-counted strict majority
(`majorityCount 1 0 = 1 < 2 = majorityCount 0 1`, equivalently `otherFin2 0 = 1` so
`majorityCount (otherFin2 0) 0 < majorityCount 0 (otherFin2 0)`) makes `0` the *unique* winner.
This is the place a `<` vs `≤` bug in `majorityCount` would surface — a `≤` would wrongly admit the
tied case. -/
theorem strictMaj_winner_is_zero : majRule.winners strictMaj = {0} := by
  apply majorityRule_strict_majority_wins strictMaj
  rw [otherFin2_zero, strictMaj_count_0_1, strictMaj_count_1_0]
  decide

/-- **The wrapper's recovered winner is concretely `{0}`.** Combining the hard converse
`converse_winners_eq_majorityRule` (which forces `wrapMajRule.winners strictMaj =
majorityRule.winners strictMaj`) with the hand-counted strict-majority winner
`majRule.winners strictMaj = {0}`, the non-defeq wrapper's winners on `strictMaj` are exactly `{0}`.
So the non-trivial agreement is anchored to real data. -/
theorem converse_wrapMajRule_strictMaj_eq_zero :
    wrapMajRule.winners strictMaj = {0} := by
  rw [converse_winners_eq_majorityRule]
  exact strictMaj_winner_is_zero

/-- The two majority counts of `tied` are both `0`: No voter strictly prefers either alternative. -/
private lemma tied_count_0_1 : majorityCount tied 0 1 = 0 := by
  rw [majorityCount_eq_card tied 0 1 (∅ : Finset (Fin 3)) (fun i => ?_)]
  · decide
  · simp [tied, preferenceOfUtilityIn_lt_iff]

private lemma tied_count_1_0 : majorityCount tied 1 0 = 0 := by
  rw [majorityCount_eq_card tied 1 0 (∅ : Finset (Fin 3)) (fun i => ?_)]
  · decide
  · simp [tied, preferenceOfUtilityIn_lt_iff]

/-- **`tied_profile_winners_univ` on `tied`.** At an exact tie
(`majorityCount 0 1 = 0 =
majorityCount 1 0`) the winners-set is *both* alternatives `{0, 1}` — the
strict inequality of `strictMaj_winner_is_zero` has flipped to an equality, and the elected set
correspondingly jumps from the singleton `{0}` to the full set `{0, otherFin2 0} = {0, 1}`.
Crossing the tie boundary flips the winner set exactly as May's theorem requires. -/
theorem tied_winner_is_univ : majRule.winners tied = {0, otherFin2 0} := by
  apply tied_profile_winners_univ majRule majRule_anonymity majRule_neutrality majRule_full_domain
  rw [otherFin2_zero, tied_count_0_1, tied_count_1_0]

/-- **`may_strict_majority_wins_aux` on `strictMaj`.** The arithmetic form of the strict-majority
conclusion: With `majorityCount 0 1 = majorityCount 1 0 + D + 1` for `D = 0` (`2 = 1 + 0 + 1`), `0`
is the unique winner. This is the inductive engine behind `strict_majority_wins`, witnessed on real
counts. -/
theorem strictMaj_winner_via_aux : majRule.winners strictMaj = {0} := by
  apply may_strict_majority_wins_aux majRule majRule_anonymity majRule_neutrality
    majRule_positiveResponsiveness majRule_full_domain 0 strictMaj 0
  rw [otherFin2_zero, strictMaj_count_0_1, strictMaj_count_1_0]

/-- **`majWinners` / `mem_majWinners_iff` direction check.** Alternative `0` is in the bare
`majWinners` set of `strictMaj` exactly because
`majorityCount (otherFin2 0) 0 ≤ majorityCount 0
(otherFin2 0)` reads `1 ≤ 2`. The `≤` here is the
*weak* majority criterion — at a tie it would admit both alternatives (consistent with
`tied_winner_is_univ`), while a strict majority admits the winner. -/
theorem zero_mem_majWinners_strictMaj : (0 : Fin 2) ∈ majWinners strictMaj := by
  rw [mem_majWinners_iff, otherFin2_zero, strictMaj_count_0_1, strictMaj_count_1_0]
  decide

/-- And alternative `1` is *not* a `majWinners` member of `strictMaj`:
`majorityCount (otherFin2 1)
1 ≤ majorityCount 1 (otherFin2 1)` reads `2 ≤ 1`, which is false. The
losing alternative is correctly excluded — the direction of the `≤` in `mem_majWinners_iff` is
right. -/
theorem one_not_mem_majWinners_strictMaj : (1 : Fin 2) ∉ majWinners strictMaj := by
  rw [mem_majWinners_iff, otherFin2_one, strictMaj_count_0_1, strictMaj_count_1_0]
  decide

end May

end EconlibTest.SocialChoice.Impossibility

end
