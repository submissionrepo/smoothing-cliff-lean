/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# The Prisoner's Dilemma: Strict Dominance, Unique Pure Nash, and Pareto Loss

The Prisoner's Dilemma is the canonical illustration of how individually rational play can destroy
collectively profitable outcomes. Two suspects, interrogated separately, each face the choice of
cooperating with the other (staying silent) or defecting (testifying against the partner). For each
player, defection strictly dominates cooperation against *every* fixed action of the opponent — so
any rational player defects no matter what they believe the other will do. The unique pure-strategy
Nash equilibrium is mutual defection `(D, D)`, even though mutual cooperation `(C, C)` would have
made both players strictly better off. The dilemma exhibits a sharp gap between individual
rationality and collective welfare: The Nash outcome is Pareto- dominated by an outcome both
players prefer.

We adopt the classical payoff calibration `T = 5 > R = 3 > P = 1 > S = 0`, satisfying the
Prisoner's Dilemma inequalities `T > R > P > S` (so defection is dominant) and the iterated- PD
inequality `2R > T + S` (so cooperation is jointly efficient). Concretely:

|               | C (cooperate) | D (defect) |
| ------------- | ------------: | ---------: |
| C (cooperate) | (3, 3)        | (0, 5)     |
| D (defect)    | (5, 0)        | (1, 1)     |

This file is the tutorial worked example for Econlib's `FiniteStrategicGame` API. Three results do
the heavy lifting:

* `prisonersDilemma_D_strictly_dominant` — pointwise strict dominance of defection over
  cooperation, regardless of the opponent's action.
* `prisonersDilemma_DD_is_pure_nash` and `prisonersDilemma_pure_nash_unique` — mutual defection is
  the unique pure-strategy Nash equilibrium, by direct case analysis on `Fin 2 → Fin 2`.
* `prisonersDilemma_CC_pareto_dominates_DD` — both players strictly prefer mutual cooperation to
  mutual defection. Combined with the Nash characterization, this is the welfare paradox.
* `prisonersDilemma_CC_jointly_efficient` — mutual cooperation maximizes total surplus over all
  profiles, the formal content of `2R > T + S`.

We also push past existence to the mixed equilibrium itself. `prisonersDilemma_mixed_nash_exists`
records Nash's existence theorem (`FiniteStrategicGame.exists_mixedNash`) as a one-liner; then,
because defection is strictly dominant, `prisonersDilemma_mixed_nash_defect` and
`prisonersDilemma_mixed_nash_unique` prove that *every* mixed Nash equilibrium places unit mass on
`D` for each player and hence equals the pure mutual-defection profile `defectMixedProfile`. The
strictness propagates through the linear `expectedPayoff`: any cooperating mass is a strictly
profitable deviation to defect.

The pure-case proofs reduce to `decide` / `simp` / `fin_cases` over the four-element profile space
`Fin 2 → Fin 2`; the mixed-uniqueness proof adds closed-form expected payoffs (`sum_action_profile`)
and a short `linarith`/`nlinarith` argument against the simplex constraints.
-/

noncomputable section

namespace EconlibExamples.GameTheory.PrisonersDilemma

open Econlib.GameTheory

/-! ## The Game -/

/-- **The Prisoner's Dilemma.** Two players each pick an action in `Fin 2`, where `0` denotes
*cooperate* (`C`) and `1` denotes *defect* (`D`). Payoffs follow the standard PD calibration
`T = 5`, `R = 3`, `P = 1`, `S = 0`: A player who defects against a cooperator earns the temptation
payoff `T`; mutual cooperation yields the reward `R`; mutual defection yields the punishment `P`;
cooperating against a defector yields the sucker payoff `S`. Built via `FiniteStrategicGame.mkFin`
and marked `abbrev` so the carriers `prisonersDilemma.Player` and `prisonersDilemma.Action i`
reduce to `Fin 2` for numeric literals and `fin_cases`. -/
abbrev prisonersDilemma : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 2) fun i s =>
    -- Player `i` looks at their own action `s i` and the opponent's action `s (1 - i)`.
    -- The four cases below name the payoff entries `(C, C) ↦ R`, `(C, D) ↦ S`, `(D, C) ↦ T`,
    -- `(D, D) ↦ P` from player `i`'s perspective.
    if s i = 0 then
      if s (1 - i) = 0 then 3 else 0   -- (C, C) ↦ R = 3; (C, D) ↦ S = 0
    else
      if s (1 - i) = 0 then 5 else 1   -- (D, C) ↦ T = 5; (D, D) ↦ P = 1

/-! ## Named Pure Profiles -/

/-- The all-cooperate profile `(C, C)`. -/
def cooperateProfile : prisonersDilemma.ActionProfile := fun _ => (0 : Fin 2)

/-- The all-defect profile `(D, D)`. -/
def defectProfile : prisonersDilemma.ActionProfile := fun _ => (1 : Fin 2)

/-! ## Strict Dominance of Defection -/

/-- **Strict dominance.** For every player `i` and every profile `s`, defecting yields a strictly
higher payoff than cooperating, holding the opponent's action fixed. This is the operational
content of "defection is a strictly dominant strategy". Because the result holds *pointwise* in the
opponent's choice, it implies that defection is a best response to every belief over the opponent's
action — pure or mixed. -/
theorem prisonersDilemma_D_strictly_dominant
    (i : Fin 2) (s : prisonersDilemma.ActionProfile) :
    prisonersDilemma.payoff i (Function.update s i (1 : Fin 2)) >
      prisonersDilemma.payoff i (Function.update s i (0 : Fin 2)) := by
  -- The opponent index `1 - i` is distinct from the player's own index `i`, so updates at
  -- coordinate `i` leave coordinate `1 - i` untouched.
  have hne : (1 - i) ≠ i := by fin_cases i <;> decide
  -- Case on the opponent's action: payoffs `5 > 3` (opp cooperates) or `1 > 0` (opp defects).
  by_cases hop : s (1 - i) = (0 : Fin 2) <;>
    norm_num [Function.update_of_ne hne, hop]

/-! ## Pure Nash Equilibrium: Existence and Uniqueness -/

/-- **Mutual defection is a pure Nash equilibrium.** No unilateral deviation from `(D, D)` is
profitable: Any player switching from `D` to `C` against a defecting opponent moves from the
punishment payoff `P = 1` to the sucker payoff `S = 0`, a strict loss. The proof enumerates the
four `(i, aᵢ)` cases by `fin_cases` after unfolding `IsNash` to its concrete best-response form. -/
theorem prisonersDilemma_DD_is_pure_nash :
    prisonersDilemma.IsNash defectProfile := by
  -- Unfold to the concrete inequality on payoffs.
  rw [StrategicGame.isNash_iff]
  intro i aᵢ
  -- The deviation profile `update defectProfile i aᵢ` is fully determined by `i` and `aᵢ`,
  -- both ranging over `Fin 2`. Enumerate all four cases.
  fin_cases i <;> fin_cases aᵢ <;>
    simp [prisonersDilemma, defectProfile, Function.update_self]

/-- **Uniqueness of the pure Nash equilibrium.** Every pure-strategy Nash equilibrium of the
Prisoner's Dilemma equals the all-defect profile. We enumerate the four pure profiles
`(C,C), (C,D), (D,C), (D,D)` over `Fin 2 → Fin 2`: Only `(D, D)` survives the unilateral- deviation
check, because in any profile containing a cooperator, that cooperator strictly gains by switching
to `D`. The proof leverages `decide` after reducing `IsNash` to a concrete quantifier over
`Fin 2 → Fin 2`. -/
theorem prisonersDilemma_pure_nash_unique (s : prisonersDilemma.ActionProfile)
    (hs : prisonersDilemma.IsNash s) : s = defectProfile := by
  -- `IsNash s` unfolds to `∀ i aᵢ, payoff i s ≥ payoff i (update s i aᵢ)`.
  rw [StrategicGame.isNash_iff] at hs
  -- Each coordinate of `s` is in `Fin 2`; if any player cooperates, they would gain by switching.
  -- We show `s 0 = 1` and `s 1 = 1` by deriving a contradiction from cooperation.
  -- The proof for each coordinate `j ∈ {0, 1}`: if `s j = 0` (cooperate), the strict-dominance
  -- lemma at player `j` says deviating to `1` strictly improves payoff, contradicting `hs`.
  have hcoord : ∀ j : Fin 2, s j = (1 : Fin 2) := by
    intro j
    -- `s j` is a `Fin 2` value (the carrier reduces through `mkFin`): if it is not `0`
    -- (cooperate), it is `1` (defect). Rule out cooperation by dominance.
    refine Fin.eq_one_of_ne_zero (s j) fun hC => ?_
    have hdev := hs j (1 : Fin 2)
    have hgt := prisonersDilemma_D_strictly_dominant j s
    -- `s j = 0`, so updating coordinate `j` to `0` is the identity.
    have hupd0 : Function.update s j (0 : Fin 2) = s := by
      rw [← hC, Function.update_eq_self]
    rw [hupd0] at hgt
    linarith
  -- Both coordinates equal `1`, so `s = defectProfile`.
  funext j
  exact hcoord j

/-! ## Pareto Inefficiency of the Unique Equilibrium -/

/-- **Pareto dominance of cooperation.** Both players strictly prefer the all-cooperate profile
`(C, C)` to the all-defect profile `(D, D)`: Every player earns `R = 3` under mutual cooperation
versus `P = 1` under mutual defection. Combined with `prisonersDilemma_pure_nash_unique`, this is
the welfare paradox: The unique pure Nash equilibrium of the Prisoner's Dilemma is Pareto-
dominated by an outcome both players prefer. -/
theorem prisonersDilemma_CC_pareto_dominates_DD :
    ∀ i : Fin 2,
      prisonersDilemma.payoff i cooperateProfile >
        prisonersDilemma.payoff i defectProfile := by
  intro i
  fin_cases i <;> simp [cooperateProfile, defectProfile]

/-- **Joint efficiency of cooperation.** Mutual cooperation maximizes the sum of the two players'
payoffs over *all* action profiles: No profile delivers more total surplus than `(C, C)`'s `2R = 6`.
This is the formal content of the `2R > T + S` (and `2R > 2P`) calibration — the surplus ranking
`(C,C) = 6 > (C,D) = (D,C) = 5 > (D,D) = 2` — and is what makes the equilibrium `(D, D)` a
welfare loss. -/
theorem prisonersDilemma_CC_jointly_efficient (s : prisonersDilemma.ActionProfile) :
    prisonersDilemma.payoff 0 s + prisonersDilemma.payoff 1 s ≤
      prisonersDilemma.payoff 0 cooperateProfile + prisonersDilemma.payoff 1 cooperateProfile := by
  -- Mutual cooperation's joint payoff is `2R = 6`.
  have hcc : prisonersDilemma.payoff 0 cooperateProfile
      + prisonersDilemma.payoff 1 cooperateProfile = 6 := by norm_num [cooperateProfile]
  rw [hcc]
  -- The payoff to each player depends only on `(s 0, s 1)`, so reduce `s` to the literal
  -- `![s 0, s 1]` and enumerate the four cases.
  have hrw : ∀ i : Fin 2, prisonersDilemma.payoff i s = prisonersDilemma.payoff i ![s 0, s 1] := by
    intro i; congr 1; funext k; fin_cases k <;> rfl
  rw [hrw 0, hrw 1]
  obtain ⟨a, ha⟩ : ∃ a : Fin 2, s 0 = a := ⟨s 0, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, s 1 = b := ⟨s 1, rfl⟩
  rw [ha, hb]
  fin_cases a <;> fin_cases b <;> norm_num [prisonersDilemma]

/-! ## Mixed Nash Existence -/

/-- **Mixed Nash existence.** As a finite strategic game, the Prisoner's Dilemma admits a mixed-
strategy Nash equilibrium by Nash's existence theorem (`FiniteStrategicGame.exists_mixedNash`,
proved via Kakutani's fixed-point theorem in Econlib). Because defection strictly dominates
cooperation pointwise, the mixed equilibrium in fact places unit mass on `D` for each player and
coincides with the pure equilibrium `(D, D)`; we record only the existence statement here. -/
theorem prisonersDilemma_mixed_nash_exists :
    ∃ σ : prisonersDilemma.MixedStrategy, FiniteStrategicGame.IsMixedNash σ :=
  prisonersDilemma.exists_mixedNash

/-! ## Mixed Nash Uniqueness: Unit Mass on Defection

Existence by Nash's theorem leaves open *which* profile is the equilibrium. Because defection is
strictly dominant pointwise, the strictness propagates through the linear `expectedPayoff`: at any
mixed profile a player who assigns positive weight to cooperation can strictly improve by shifting
that weight to defection. We make this concrete and prove that *every* mixed Nash equilibrium places
unit mass on `D` for each player, hence coincides with the pure mutual-defection profile.

The proof mirrors the sibling `MatchingPennies.lean`: enumerate the four pure profiles with a
`sum_action_profile` helper to get closed forms for each player's expected payoff, read off the
deviation payoffs at the pure `D`-vertex via `Function.update`, then feed the Nash inequality plus
the simplex constraints to `nlinarith`/`linarith`. -/

/-- Player 0 of the Prisoner's Dilemma. -/
abbrev p0 : prisonersDilemma.Player := 0

/-- Player 1 of the Prisoner's Dilemma. -/
abbrev p1 : prisonersDilemma.Player := 1

/-- The pure mutual-defection profile, viewed as a (degenerate) mixed strategy: each player places
unit mass on the defect action `1 : Fin 2`. This is the mixed-strategy avatar of `defectProfile`. -/
def defectMixedProfile : prisonersDilemma.MixedStrategy := fun _ => stdSimplex.vertex (1 : Fin 2)

/-- For any `f : (Fin 2 → Fin 2) → ℝ`, the sum over all four `Fin 2 → Fin 2` profiles equals the
four-term sum over the explicit profiles `(0,0), (0,1), (1,0), (1,1)`. Workhorse for evaluating
`expectedPayoff` by hand: the four-profile specialization of the general `sum_piFinTwo` (in
`Econlib.Math.Combinatorics.Fin2`), expanding the iterated `∑ a, ∑ b` over `Fin 2` with
`Fin.sum_univ_two`. -/
lemma sum_action_profile (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ s : Fin 2 → Fin 2, f s
      = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [sum_piFinTwo]
  simp [Fin.sum_univ_two]
  ring

/-- Closed form for player 0's expected payoff at an arbitrary mixed profile `σ`. Reading the PD
matrix from player 0's perspective (own action is coordinate `0`, opponent is coordinate `1`):
`(C,C) ↦ 3`, `(C,D) ↦ 0`, `(D,C) ↦ 5`, `(D,D) ↦ 1`. -/
lemma expectedPayoff_p0_closed (σ : prisonersDilemma.MixedStrategy) :
    prisonersDilemma.expectedPayoff p0 σ
      = 3 * (σ 0) 0 * (σ 1) 0 + 5 * (σ 0) 1 * (σ 1) 0 + (σ 0) 1 * (σ 1) 1 := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j)) * prisonersDilemma.payoff p0 s)]
  -- Expand `∏ j, (σ j) (s j) = (σ 0) (s 0) * (σ 1) (s 1)`, reduce the opponent index `1 - p0 = 1`,
  -- and evaluate the vector literals at each coordinate.
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
             show ((1 : prisonersDilemma.Player) - p0 = 1) from by decide]
  -- Decide the residual `Fin 2` equality tests inside the unfolded `payoff` and sum by `ring`.
  simp only [show ((1 : Fin 2) = 0) ↔ False from by decide, if_false, if_true]
  ring

/-- Closed form for player 1's expected payoff at an arbitrary mixed profile `σ`. Player 1's own
action is coordinate `1` and the opponent is coordinate `0`, so `(C,C) ↦ 3`, `(D,C) ↦ 0` (own
cooperates, opponent defects ⇒ sucker), `(C,D) ↦ 5` (own defects, opponent cooperates ⇒ temptation),
`(D,D) ↦ 1`. -/
lemma expectedPayoff_p1_closed (σ : prisonersDilemma.MixedStrategy) :
    prisonersDilemma.expectedPayoff p1 σ
      = 3 * (σ 0) 0 * (σ 1) 0 + 5 * (σ 0) 0 * (σ 1) 1 + (σ 0) 1 * (σ 1) 1 := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j)) * prisonersDilemma.payoff p1 s)]
  -- Player 1's own action is coordinate `1`; reduce the opponent index `1 - p1 = 0` and evaluate.
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
             show ((1 : prisonersDilemma.Player) - p1 = 0) from by decide]
  -- Discharge each residual `Fin 2` equality test, then sum by `ring`.
  simp only [show ((1 : Fin 2) = 0) ↔ False from by decide, if_false, if_true]
  ring

/-- Player 0's payoff after deviating to the pure vertex `a` (opponent's coordinate untouched). -/
lemma dev_p0_payoff (σ : prisonersDilemma.MixedStrategy) (a : Fin 2) :
    prisonersDilemma.expectedPayoff p0 (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a))
      = 3 * (stdSimplex.vertex (S := ℝ) a) 0 * (σ 1) 0
        + 5 * (stdSimplex.vertex (S := ℝ) a) 1 * (σ 1) 0
        + (stdSimplex.vertex (S := ℝ) a) 1 * (σ 1) 1 := by
  rw [expectedPayoff_p0_closed,
      show (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a)) 0
          = stdSimplex.vertex (S := ℝ) a from Function.update_self ..,
      show (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a)) 1
          = σ 1 from Function.update_of_ne (by decide) _ _]

/-- Player 1's payoff after deviating to the pure vertex `a` (opponent's coordinate untouched). -/
lemma dev_p1_payoff (σ : prisonersDilemma.MixedStrategy) (a : Fin 2) :
    prisonersDilemma.expectedPayoff p1 (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a))
      = 3 * (σ 0) 0 * (stdSimplex.vertex (S := ℝ) a) 0
        + 5 * (σ 0) 0 * (stdSimplex.vertex (S := ℝ) a) 1
        + (σ 0) 1 * (stdSimplex.vertex (S := ℝ) a) 1 := by
  rw [expectedPayoff_p1_closed,
      show (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a)) 0
          = σ 0 from Function.update_of_ne (by decide) _ _,
      show (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a)) 1
          = stdSimplex.vertex (S := ℝ) a from Function.update_self ..]

/-- **Mixed Nash equilibria put unit mass on Defect.** In any mixed Nash equilibrium `σ`, each
player assigns probability one to the defect action `1`. This is the mixed-strategy form of strict
dominance: a cooperating mass would be a strictly profitable deviation to defect. -/
theorem prisonersDilemma_mixed_nash_defect
    (σ : prisonersDilemma.MixedStrategy) (hσ : FiniteStrategicGame.IsMixedNash σ)
    (i : prisonersDilemma.Player) : (σ i) 1 = 1 := by
  rw [FiniteStrategicGame.isMixedNash_iff] at hσ
  -- Vertex coordinates: `vertex 1 = (0, 1)` (defect places unit mass on action `1`).
  have hv1_0 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) 0 = 0 :=
    stdSimplex.vertex_apply_ne (by decide)
  have hv1_1 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) 1 = 1 := stdSimplex.vertex_apply_self 1
  -- Simplex nonnegativity and normalization for each player's distribution.
  have hnn0_0 : 0 ≤ (σ 0) 0 := (σ 0).2.1 0
  have hnn1_0 : 0 ≤ (σ 1) 0 := (σ 1).2.1 0
  have hnn1_1 : 0 ≤ (σ 1) 1 := (σ 1).2.1 1
  have hsum0 : (σ 0) 0 + (σ 0) 1 = 1 := by
    have := (σ 0).2.2; rwa [Fin.sum_univ_two] at this
  have hsum1 : (σ 1) 0 + (σ 1) 1 = 1 := by
    have := (σ 1).2.2; rwa [Fin.sum_univ_two] at this
  -- Eliminate the defect coordinates against the cooperate ones via normalization, so the only
  -- atoms left are `(σ 0) 0` and `(σ 1) 0` and their product.
  have he01 : (σ 0) 1 = 1 - (σ 0) 0 := by linarith
  have he11 : (σ 1) 1 = 1 - (σ 1) 0 := by linarith
  -- Player 0's defect-deviation inequality forces no cooperating mass: `(σ 0) 0 = 0`.
  -- After substitution `hdev` reads `(σ0)0 * ((σ1)0 + 1) ≤ 0`; the bracket is `≥ 1 > 0` and
  -- `(σ0)0 ≥ 0`, so `(σ0)0 = 0`.
  have hc0 : (σ 0) 0 = 0 := by
    have hdev := hσ p0 (stdSimplex.vertex (S := ℝ) (1 : Fin 2))
    rw [expectedPayoff_p0_closed, dev_p0_payoff, hv1_0, hv1_1, he01, he11] at hdev
    nlinarith [mul_nonneg hnn0_0 hnn1_0, hnn0_0, hnn1_0]
  -- Player 1's defect-deviation inequality symmetrically forces `(σ 1) 0 = 0`.
  have hc1 : (σ 1) 0 = 0 := by
    have hdev := hσ p1 (stdSimplex.vertex (S := ℝ) (1 : Fin 2))
    rw [expectedPayoff_p1_closed, dev_p1_payoff, hv1_0, hv1_1, he01, he11] at hdev
    nlinarith [mul_nonneg hnn1_0 hnn0_0, hnn1_0, hnn0_0]
  -- Each player's cooperate mass vanishes, so by normalization the defect mass is one.
  have hd0 : (σ 0) 1 = 1 := by linarith
  have hd1 : (σ 1) 1 = 1 := by linarith
  fin_cases i
  · exact hd0
  · exact hd1

/-- **Uniqueness of the mixed Nash equilibrium.** Every mixed Nash equilibrium of the Prisoner's
Dilemma equals the pure mutual-defection profile `defectMixedProfile`. Because defection is strictly
dominant, the equilibrium places unit mass on `D` for each player
(`prisonersDilemma_mixed_nash_defect`), which determines the distribution coordinate by coordinate:
action `0` (cooperate) carries mass `0` and action `1` (defect) carries mass `1`, matching
`stdSimplex.vertex 1`. -/
theorem prisonersDilemma_mixed_nash_unique
    (σ : prisonersDilemma.MixedStrategy) (hσ : FiniteStrategicGame.IsMixedNash σ) :
    σ = defectMixedProfile := by
  -- Each player puts unit mass on defection; convert to the cooperate coordinate via normalization.
  have hdefect : ∀ i : prisonersDilemma.Player, (σ i) 1 = 1 :=
    fun i => prisonersDilemma_mixed_nash_defect σ hσ i
  funext i
  apply Subtype.ext
  funext x
  -- The cooperate coordinate of `σ i` vanishes by normalization against the unit defect mass.
  have hsum : (σ i) 0 + (σ i) 1 = 1 := by
    have := (σ i).2.2; rwa [Fin.sum_univ_two] at this
  have hcoop : (σ i) 0 = 0 := by have := hdefect i; linarith
  -- `defectMixedProfile i = stdSimplex.vertex 1`, whose coordinates are `0 ↦ 0`, `1 ↦ 1`.
  -- Match each coordinate of `σ i` against it: cooperate ↦ `0` (hcoop), defect ↦ `1` (hdefect).
  -- `simp only [defectMixedProfile]` exposes the vertex; the `@[simp]` vertex-evaluation lemmas
  -- reduce its coordinate, and `exact` closes through the `⟨k, _⟩`-vs-literal defeq.
  fin_cases x <;>
    simp only [defectMixedProfile]
  · exact hcoop
  · exact hdefect i

end EconlibExamples.GameTheory.PrisonersDilemma

end
