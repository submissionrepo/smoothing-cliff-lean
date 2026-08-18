/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.CorrelatedCournot
import Mathlib

/-!
# Bayesian Nash Equilibrium — Non-Vacuity Checks

Compile-time semantic witnesses for the finite Bayesian-game layer
(`Econlib.GameTheory.Strategic.Bayesian.{Game, MixedBNE, PureBNE, Dominant}`) and the cheaply
reachable pieces of the measurable layer (`…Bayesian.Measurable.Game`), anchored on a hand-solved
finite Bayesian game and on the imported correlated-Gaussian Cournot game.

## The finite Bayesian game `bg` (hand-solved)

Two players `Fin 2`, each with type space `Fin 2` and action space `Fin 2`. The common prior puts
mass `1/2` on each of `(θ₀, θ₁) = (0,0)` and `(0,1)`, and mass `0` on the two profiles with
`θ₀ = 1`. So:

* **player 0's type 1 has prior marginal `0`** — a genuine zero-prior type, used to fire the
  `interimPayoff*_eq_zero_of_marginal_not_pos` junk-value conventions;
* player 1's two types each have marginal `1/2 > 0` — positive-prior types where the incentive
  constraints bind.

Payoffs: Player 0 gets `1` for playing action `1` and `0` for action `0` (action `1` is **strictly
dominant**, independent of type and opponent); player 1's payoff is the **constant `5`** (player 1
is fully indifferent). Hence:

* the pure profile `s⋆ i θ = 1` (always action `1`) is a **weakly dominant strategy** — strictly
  for player 0, weakly for the indifferent player 1 — so it is a BNE (`IsDominantStrategy.isBNE`);
* the mixed profile `σ⋆` with player 0 pure on `1` and **player 1 uniform `(1/2,1/2)`** is a mixed
  BNE in which player 1's *both* actions lie in the support and are interim-indifferent (each
  yields the constant `5`) — the semantic content of `mixedBNE_indifference`.

The failure modes these catch: A best-response *direction reversal* would reject the dominant
profile; a *vacuous marginal-positivity* hypothesis is checked by exhibiting both a zero-prior type
(player 0 type 1, where the conventions return `0`) and positive-prior types (player 1); a
*player/type index swap* in the interim operators would corrupt the constant-`5` indifference.
-/

noncomputable section

namespace EconlibTest.GameTheory.StrategicBayesian

open Econlib.GameTheory Econlib.Probability
open scoped BigOperators

/-! ## The finite Bayesian game and its prior -/

/-- The common prior: Mass `1/2` on the two type profiles with `θ₀ = 0`, mass `0` elsewhere. Built
as a `FinDist (Π _ : Fin 2, Fin 2)` directly. -/
def priorPMF : (∀ _ : Fin 2, Fin 2) → ℝ :=
  fun θ => if θ 0 = 0 then 1 / 2 else 0

/-- The prior as a `TypeDist`. -/
def bgPrior : TypeDist (Fin 2) (fun _ => Fin 2) where
  pmf := priorPMF
  nonneg := fun θ => by unfold priorPMF; split <;> norm_num
  sum_one := by
    -- Four profiles; the two with `θ₀ = 0` carry `1/2` each, the others `0`. Enumerate via the
    -- `(Fin 2 → Fin 2) ≃ Fin 2 × Fin 2` equivalence and decide the `θ 0 = 0` test pointwise.
    change ∑ θ : (∀ _ : Fin 2, Fin 2), priorPMF θ = 1
    rw [← (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [priorPMF, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.sum_univ_two]
    norm_num

/-- **The hand-solved finite Bayesian game.** Player 0's action `1` is strictly dominant (payoff
`1` vs. `0`); player 1 is indifferent (constant payoff `5`). Marked `@[reducible]` so the carriers
`bg.Player`, `bg.Theta i`, `bg.Action i` reduce to `Fin 2` for numeric literals and `fin_cases`. -/
@[reducible] def bg : FinBayesianGame where
  Player := Fin 2
  Theta := fun _ => Fin 2
  Action := fun _ => Fin 2
  payoff := fun i a _θ => if i = 0 then (if a 0 = 1 then 1 else 0) else 5
  prior := bgPrior

@[simp] theorem bg_payoff (i : Fin 2) (a : ∀ _ : Fin 2, Fin 2) (θ : ∀ _ : Fin 2, Fin 2) :
    bg.payoff i a θ = if i = 0 then (if a 0 = 1 then 1 else 0) else 5 := rfl

/-- The always-action-`1` pure strategy profile. -/
def domStrat : bg.PureStrategy := fun _ _ => (1 : Fin 2)

/-! ## Prior marginals: The zero-prior and positive-prior types

These anchor the marginal-positivity zero-conventions: Player 0's type `1` is a genuine
zero-prior type, while player 1's two types each have marginal `1/2`. -/

/-- Enumerate a sum over `(Fin 2 → Fin 2)` of a real function as the four explicit profiles. -/
private lemma sum_typeProfile (f : (∀ _ : Fin 2, Fin 2) → ℝ) :
    ∑ θ : (∀ _ : Fin 2, Fin 2), f θ = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [piFinTwoEquiv_symm_apply, Fin.sum_univ_two]
  have e00 : (Fin.cons 0 (Fin.cons 0 finZeroElim) : Fin 2 → Fin 2) = ![0, 0] := by
    funext k; fin_cases k <;> rfl
  have e01 : (Fin.cons 0 (Fin.cons 1 finZeroElim) : Fin 2 → Fin 2) = ![0, 1] := by
    funext k; fin_cases k <;> rfl
  have e10 : (Fin.cons 1 (Fin.cons 0 finZeroElim) : Fin 2 → Fin 2) = ![1, 0] := by
    funext k; fin_cases k <;> rfl
  have e11 : (Fin.cons 1 (Fin.cons 1 finZeroElim) : Fin 2 → Fin 2) = ![1, 1] := by
    funext k; fin_cases k <;> rfl
  rw [e00, e01, e10, e11]; ring

/-- **Zero-prior type.** Player 0's type `1` has prior marginal `0`: The prior never puts
`θ₀ = 1`. -/
theorem bg_marginal_p0_type1 : bg.prior.marginalD 0 (1 : Fin 2) = 0 := by
  change FinDist.marginalD bgPrior 0 1 = 0
  rw [FinDist.marginalD, Finset.sum_filter]
  rw [sum_typeProfile (fun θ => if θ 0 = 1 then bgPrior θ else 0)]
  change (if (![0,0] : Fin 2 → Fin 2) 0 = 1 then bgPrior ![0,0] else 0)
      + (if (![0,1] : Fin 2 → Fin 2) 0 = 1 then bgPrior ![0,1] else 0)
      + (if (![1,0] : Fin 2 → Fin 2) 0 = 1 then bgPrior ![1,0] else 0)
      + (if (![1,1] : Fin 2 → Fin 2) 0 = 1 then bgPrior ![1,1] else 0) = 0
  norm_num [bgPrior, priorPMF]

/-- **Positive-prior type.** Player 1's type `0` has prior marginal `1/2`. -/
theorem bg_marginal_p1_type0 : bg.prior.marginalD 1 (0 : Fin 2) = 1 / 2 := by
  change FinDist.marginalD bgPrior 1 0 = 1 / 2
  rw [FinDist.marginalD, Finset.sum_filter]
  rw [sum_typeProfile (fun θ => if θ 1 = 0 then bgPrior θ else 0)]
  change (if (![0,0] : Fin 2 → Fin 2) 1 = 0 then bgPrior ![0,0] else 0)
      + (if (![0,1] : Fin 2 → Fin 2) 1 = 0 then bgPrior ![0,1] else 0)
      + (if (![1,0] : Fin 2 → Fin 2) 1 = 0 then bgPrior ![1,0] else 0)
      + (if (![1,1] : Fin 2 → Fin 2) 1 = 0 then bgPrior ![1,1] else 0) = 1 / 2
  norm_num [bgPrior, priorPMF]

/-- Player 1's type `0` has *positive* prior marginal — the hypothesis of the BNE characterization
is satisfiable. -/
theorem bg_marginal_p1_type0_pos : 0 < bg.prior.marginalD 1 (0 : Fin 2) := by
  rw [bg_marginal_p1_type0]; norm_num

/-- **Positive-prior type (the *second* player-1 type).** Player 1's type `1` also has prior
marginal `1/2` — closing the header's claim that *both* player-1 types have marginal `1/2`. -/
theorem bg_marginal_p1_type1 : bg.prior.marginalD 1 (1 : Fin 2) = 1 / 2 := by
  change FinDist.marginalD bgPrior 1 1 = 1 / 2
  rw [FinDist.marginalD, Finset.sum_filter]
  rw [sum_typeProfile (fun θ => if θ 1 = 1 then bgPrior θ else 0)]
  change (if (![0,0] : Fin 2 → Fin 2) 1 = 1 then bgPrior ![0,0] else 0)
      + (if (![0,1] : Fin 2 → Fin 2) 1 = 1 then bgPrior ![0,1] else 0)
      + (if (![1,0] : Fin 2 → Fin 2) 1 = 1 then bgPrior ![1,0] else 0)
      + (if (![1,1] : Fin 2 → Fin 2) 1 = 1 then bgPrior ![1,1] else 0) = 1 / 2
  norm_num [bgPrior, priorPMF]

/-- Player 1's type `1` also has *positive* prior marginal `1/2`. -/
theorem bg_marginal_p1_type1_pos : 0 < bg.prior.marginalD 1 (1 : Fin 2) := by
  rw [bg_marginal_p1_type1]; norm_num

/-! ## Dominant strategy ⇒ pure BNE -/

/-- **`domStrat` is weakly dominant.** Action `1` is a best response for every player, type
profile, and opponent-action profile — strictly for player 0 (`1 ≥ 0/1`), weakly for the
indifferent player 1 (`5 ≥ 5`). -/
theorem domStrat_isDominant : bg.IsDominantStrategy domStrat := by
  intro i θ a a_i
  -- `domStrat i (θ i) = 1`; the RHS payoff is `1` for player 0 and `5` for player 1.
  by_cases hi : i = 0
  · -- Player 0: own coordinate is `0`; both updates touch coordinate `0`, RHS sets it to `1`.
    subst hi
    simp only [domStrat, Function.update_self]
    -- RHS `= 1` (the updated `0`-coordinate is `1`); LHS `∈ {0,1}`.
    split_ifs <;> norm_num
  · -- Player 1: the `i = 0` test is false, both payoffs are the constant `5`.
    simp only [domStrat, if_neg hi, le_refl]

/-- `IsDominantStrategy.isBNE`: The dominant strategy `domStrat` is a (pure) Bayesian Nash
equilibrium. Dominance is the *strict* incentive for player 0; the implication is non-vacuous. -/
theorem domStrat_isBNE : bg.IsBNE domStrat :=
  domStrat_isDominant.isBNE

/-- **Negative check (cooperate-equivalent deviation is worse for player 0).** Player 0 deviating
to action `0` at type `0` strictly lowers its realized payoff (`1 → 0`), against any opponent
action and type. This is the strict edge of dominance. -/
theorem bg_p0_deviation_worse (θ a : ∀ _ : Fin 2, Fin 2) :
    bg.payoff 0 (Function.update a 0 (0 : Fin 2)) θ <
      bg.payoff 0 (Function.update a 0 (1 : Fin 2)) θ := by
  simp only [Function.update_self,
    show ((0 : Fin 2) = 1) ↔ False from by decide, if_false]
  norm_num

/-! ## Pure BNE substrate -/

/-- `bnePred_swap_iff`: A pure-BNE deviation at `⟨i, θ_i⟩` changes the strategy only at that
player–type pair. -/
theorem bg_bnePred_swap_iff (p : Σ i, bg.Theta i) (s s' : bg.PureStrategy) :
    bg.bnePred.swap p s s' ↔ ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, bg.Theta k) ≠ p → s' j θ_j = s j θ_j :=
  FinBayesianGame.bnePred_swap_iff ..

/-- `bnePred_value_eq`: The substrate value is the interim payoff of the prescribed action. -/
theorem bg_bnePred_value_eq (p : Σ i, bg.Theta i) (s : bg.PureStrategy) :
    bg.bnePred.value p s = bg.interimPayoffAction p.1 p.2 (s p.1 p.2) s :=
  FinBayesianGame.bnePred_value_eq ..

/-! ## Interim payoff operators and the marginal-positivity zero-conventions -/

/-- `interimPayoff_eq_interimPayoffAction`: The equilibrium interim payoff is the interim payoff at
the prescribed action. -/
theorem bg_interimPayoff_eq (i : bg.Player) (θ_i : bg.Theta i) (s : bg.PureStrategy) :
    bg.interimPayoff i θ_i s = bg.interimPayoffAction i θ_i (s i θ_i) s :=
  bg.interimPayoff_eq_interimPayoffAction i θ_i s

/-- **Zero-convention (pure).** At player 0's zero-prior type `1`, every pure deviation's interim
payoff is `0` — the conditional is the junk-zero distribution. The hypothesis `¬ 0 < marginalD`
fires on a *witnessed* zero-prior type, not vacuously. -/
theorem bg_interimPayoffAction_zero_at_zeroPrior (a_i : bg.Action 0) (s : bg.PureStrategy) :
    bg.interimPayoffAction 0 (1 : Fin 2) a_i s = 0 :=
  bg.interimPayoffAction_eq_zero_of_marginal_not_pos 0 1 a_i s
    (by rw [bg_marginal_p0_type1]; exact lt_irrefl 0)

/-- **Zero-convention (mixed).** Same junk-zero behavior for the mixed interim payoff at the
zero-prior type. -/
theorem bg_interimPayoffMixed_zero_at_zeroPrior (a_i : bg.Action 0)
    (σ : bg.MixedBehavioralStrategy) :
    bg.interimPayoffMixed 0 (1 : Fin 2) a_i σ = 0 :=
  bg.interimPayoffMixed_eq_zero_of_marginal_not_pos 0 1 a_i σ
    (by rw [bg_marginal_p0_type1]; exact lt_irrefl 0)

/-- `interimPayoffMixed_eq_of_agree`: The mixed interim payoff depends only on the *other*
player–type pairs. Two strategies agreeing off `(1, θ₁)` give the same player-1 interim payoff. -/
theorem bg_interimPayoffMixed_eq_of_agree (θ_i : bg.Theta 1) (a_i : bg.Action 1)
    (σ₁ σ₂ : bg.MixedBehavioralStrategy)
    (h : ∀ (j : bg.Player) (θ_j : bg.Theta j),
      (⟨j, θ_j⟩ : Σ k, bg.Theta k) ≠ ⟨1, θ_i⟩ → σ₁ j θ_j = σ₂ j θ_j) :
    bg.interimPayoffMixed 1 θ_i a_i σ₁ = bg.interimPayoffMixed 1 θ_i a_i σ₂ :=
  bg.interimPayoffMixed_eq_of_agree 1 θ_i a_i σ₁ σ₂ h

/-- `interimPayoffMixed_pureToMixed`: A pure strategy embedded as a Dirac mixed strategy recovers
the pure interim payoff. -/
theorem bg_interimPayoffMixed_pureToMixed (s : bg.PureStrategy) (i : bg.Player) (θ_i : bg.Theta i)
    (a_i : bg.Action i) :
    bg.interimPayoffMixed i θ_i a_i (bg.pureToMixed s) = bg.interimPayoffAction i θ_i a_i s :=
  bg.interimPayoffMixed_pureToMixed s i θ_i a_i

/-! ## Mixed BNE: Substrate, the pure↔mixed bridge, and existence -/

/-- `mixedBnePred_swap_iff`: A mixed-BNE deviation changes the profile only at the deviator
player–type pair. -/
theorem bg_mixedBnePred_swap_iff (p : Σ i, bg.Theta i)
    (σ σ' : bg.MixedBehavioralStrategy) :
    bg.mixedBnePred.swap p σ σ' ↔
      ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, bg.Theta k) ≠ p → σ' j θ_j = σ j θ_j :=
  FinBayesianGame.mixedBnePred_swap_iff ..

/-- `mixedBnePred_value_eq`: The substrate value is the interim mixed-action payoff. -/
theorem bg_mixedBnePred_value_eq (p : Σ i, bg.Theta i) (σ : bg.MixedBehavioralStrategy) :
    bg.mixedBnePred.value p σ = bg.interimPayoffMixedAction p.1 p.2 (σ p.1 p.2) σ :=
  FinBayesianGame.mixedBnePred_value_eq ..

/-- `pureBNE_implies_mixedBNE`: The dominant pure BNE embeds as a (degenerate) mixed BNE. -/
theorem bg_pureBNE_implies_mixedBNE : bg.IsMixedBNE (bg.pureToMixed domStrat) :=
  bg.pureBNE_implies_mixedBNE domStrat domStrat_isBNE

/-- `mixedBNE_of_pure_implies_pureBNE`: The converse — a mixed BNE that is pure-valued is a pure
BNE. Round-tripping the dominant strategy recovers `domStrat`'s pure-BNE status. -/
theorem bg_mixedBNE_of_pure_implies_pureBNE : bg.IsBNE domStrat :=
  bg.mixedBNE_of_pure_implies_pureBNE (bg.pureToMixed domStrat) bg_pureBNE_implies_mixedBNE
    domStrat (fun _ _ => rfl)

/-- `mixedBNE_support_ge` (player 1, indifferent): In the embedded mixed BNE, player 1's
full-support action `1` is a best reply. *Caveat:* player 1 is *indifferent* (constant payoff `5`),
not playing a dominant action — so this inequality binds at *equality* (`5 ≥ 5`) and does not pin
a direction. The strict, direction-sensitive support-ge witness is `bg_mixedBNE_support_ge_p0`
(player 0, `1 ≥ 0`) below. -/
theorem bg_mixedBNE_support_ge (θ_i : bg.Theta 1) (a : bg.Action 1) :
    bg.interimPayoffMixed 1 θ_i 1 (bg.pureToMixed domStrat) ≥
      bg.interimPayoffMixed 1 θ_i a (bg.pureToMixed domStrat) := by
  refine bg.mixedBNE_support_ge (bg.pureToMixed domStrat) bg_pureBNE_implies_mixedBNE 1 θ_i 1 a ?_
  change (0 : ℝ) < (bg.pureToMixed domStrat 1 θ_i) 1
  simp only [FinBayesianGame.pureToMixed, domStrat, stdSimplex.vertex_apply_self]; norm_num


/-- `expandedMixed_eq_interimPayoffMixed`: The expanded-game mixed payoff of a pure-action
deviation equals the Bayesian interim mixed payoff — the bridge between the expanded strategic game
and the interim view. -/
theorem bg_expandedMixed_eq (m : bg.expandedGame.MixedStrategy) (i : bg.Player) (θ_i : bg.Theta i)
    (a_i : bg.Action i) :
    bg.expandedGame.expectedPayoff ⟨i, θ_i⟩
      (Function.update m ⟨i, θ_i⟩ (stdSimplex.vertex a_i)) =
      bg.interimPayoffMixed i θ_i a_i (fun j θ_j => m ⟨j, θ_j⟩) :=
  bg.expandedMixed_eq_interimPayoffMixed m i θ_i a_i

/-- `exists_mixedBNE`: The finite Bayesian game admits a mixed behavioral BNE. This is the
*abstract* existence endpoint (opaque witness — finite mixed-BNE existence is robust to many wrong
payoff conventions, including sign reversal); the *concrete* witness identification is
`bg_exists_mixedBNE_witness` (binding to `σ⋆`), defined after `mixedStar_isMixedBNE`. -/
theorem bg_exists_mixedBNE : ∃ σ : bg.MixedBehavioralStrategy, bg.IsMixedBNE σ :=
  bg.exists_mixedBNE

/-! ## The genuinely mixed BNE and support indifference (`mixedBNE_indifference`)

The dominant pure equilibrium has degenerate per-type support. To exercise
`mixedBNE_indifference` *non-trivially* — two distinct support actions that are interim-indifferent
— we build the mixed BNE `σ⋆` in which player 0 plays the dominant action `1` purely and **player 1
randomizes uniformly**. Player 1 is indifferent (constant payoff `5`), so the uniform mix is
optimal and *both* of its actions sit in the support. -/

/-- The uniform mixed action on `Fin 2`. -/
def uniformAct : stdSimplex ℝ (Fin 2) :=
  ⟨fun _ => 1 / 2, by refine ⟨fun _ => by norm_num, ?_⟩; rw [Fin.sum_univ_two]; norm_num⟩

/-- The mixed BNE `σ⋆`: Player 0 pure on `1`, player 1 uniform. -/
def mixedStar : bg.MixedBehavioralStrategy :=
  fun i _ => if i = 0 then stdSimplex.vertex (1 : Fin 2) else uniformAct

/-- The product over the opponent index `erase 1 = {0}` is just player 0's mass. -/
private lemma prod_erase_one (θ a : ∀ _ : Fin 2, Fin 2) :
    (∏ j ∈ Finset.univ.erase (1 : Fin 2), (mixedStar j (θ j)) (a j))
      = (mixedStar 0 (θ 0)) (a 0) := by
  rw [show (Finset.univ.erase (1 : Fin 2)) = {0} from by decide, Finset.prod_singleton]

/-- The fiber sum of player 0's mass over the free coordinate `a 0` is the total mass `1`. -/
private lemma fiber_sum_p0 (θ : ∀ _ : Fin 2, Fin 2) (a_1 : Fin 2) :
    (∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 1 = a_1),
      (mixedStar 0 (θ 0)) (a 0)) = 1 := by
  rw [show (∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 1 = a_1),
        (mixedStar 0 (θ 0)) (a 0)) = ∑ a0 : Fin 2, (mixedStar 0 (θ 0)) a0 from by
    apply Finset.sum_nbij' (fun a => a 0) (fun a0 => ![a0, a_1])
    · intro a _; exact Finset.mem_univ _
    · intro a0 _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      funext k; fin_cases k <;> simp_all
    · intro a0 _; rfl
    · intro a _; rfl]
  exact (mixedStar 0 (θ 0)).2.2

/-- **Player 1's interim mixed payoff under `σ⋆` is the constant `5`** on every positive-prior
type, for *either* action — the source of support indifference. `payoff 1 = 5`, the action-fiber
sum of player 0's mass is `1`, and the conditional sums to `1` on a positive-prior type. -/
theorem mixedStar_interim_p1 (θ_1 : bg.Theta 1) (hpos : 0 < bg.prior.marginalD 1 θ_1)
    (a_1 : bg.Action 1) :
    bg.interimPayoffMixed 1 θ_1 a_1 mixedStar = 5 := by
  rw [FinBayesianGame.interimPayoffMixed]
  -- The inner action sum is `5` for every `θ` (constant payoff × unit player-0 mass).
  have hinner : ∀ θ : ∀ _ : Fin 2, Fin 2,
      ∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 1 = a_1),
        (∏ j ∈ Finset.univ.erase 1, (mixedStar j (θ j)) (a j)) * bg.payoff 1 a θ = 5 := by
    intro θ
    -- `payoff 1 a θ` reduces to the constant `5` (`(1 : Fin 2) = 0` is false).
    simp only [show ((1 : Fin 2) = 0) ↔ False from by decide, if_false, prod_erase_one]
    rw [← Finset.sum_mul, fiber_sum_p0 θ a_1, one_mul]
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  -- The conditional sums to `1` over the `θ 1 = θ_1` fiber on a positive-prior type.
  rw [show (∑ θ ∈ Finset.univ.filter (fun θ : ∀ _ : Fin 2, Fin 2 => θ 1 = θ_1),
        bg.prior.condProbD 1 θ_1 θ) = 1 from by
    rw [show (∑ θ ∈ Finset.univ.filter (fun θ : ∀ _ : Fin 2, Fin 2 => θ 1 = θ_1),
          bg.prior.condProbD 1 θ_1 θ) = ∑ θ : ∀ _ : Fin 2, Fin 2, bg.prior.condProbD 1 θ_1 θ from by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases hθ : θ 1 = θ_1
      · rw [if_pos hθ]
      · rw [if_neg hθ, FinDist.condProbD_of_ne _ _ _ hθ]]
    exact FinDist.condProbD_sum_one_of_pos bgPrior 1 θ_1 hpos]
  norm_num

/-- The product over the opponent index `erase 0 = {1}` is just player 1's mass. -/
private lemma prod_erase_zero (θ a : ∀ _ : Fin 2, Fin 2) :
    (∏ j ∈ Finset.univ.erase (0 : Fin 2), (mixedStar j (θ j)) (a j))
      = (mixedStar 1 (θ 1)) (a 1) := by
  rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from by decide, Finset.prod_singleton]

/-- The fiber sum of player 1's mass over the free coordinate `a 1` is the total mass `1`. -/
private lemma fiber_sum_p1 (θ : ∀ _ : Fin 2, Fin 2) (a_0 : Fin 2) :
    (∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 0 = a_0),
      (mixedStar 1 (θ 1)) (a 1)) = 1 := by
  rw [show (∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 0 = a_0),
        (mixedStar 1 (θ 1)) (a 1)) = ∑ a1 : Fin 2, (mixedStar 1 (θ 1)) a1 from by
    apply Finset.sum_nbij' (fun a => a 1) (fun a1 => ![a_0, a1])
    · intro a _; exact Finset.mem_univ _
    · intro a1 _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      funext k; fin_cases k <;> simp_all
    · intro a1 _; rfl
    · intro a _; rfl]
  exact (mixedStar 1 (θ 1)).2.2

/-- **Player 0's interim mixed payoff under `σ⋆`** at its positive-prior type `0`: Action `1` pays
`1`, action `0` pays `0` (the strict dominance, now in interim mixed form). -/
theorem mixedStar_interim_p0 (a_0 : bg.Action 0) :
    bg.interimPayoffMixed 0 (0 : Fin 2) a_0 mixedStar = (if a_0 = 1 then 1 else 0) := by
  rw [FinBayesianGame.interimPayoffMixed]
  -- Reduce each inner action-fiber sum to the constant `if a_0 = 1 then 1 else 0`.
  rw [Finset.sum_congr rfl (g := fun θ => bg.prior.condProbD 0 0 θ * (if a_0 = 1 then 1 else 0))
    (fun θ _ => by
      congr 1
      -- On the fiber `a 0 = a_0`, the payoff is the constant `if a_0 = 1 then 1 else 0`.
      rw [show (∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 0 = a_0),
            (∏ j ∈ Finset.univ.erase 0, (mixedStar j (θ j)) (a j)) * bg.payoff 0 a θ)
          = ∑ a ∈ Finset.univ.filter (fun a : ∀ _ : Fin 2, Fin 2 => a 0 = a_0),
            (mixedStar 1 (θ 1)) (a 1) * (if a_0 = 1 then 1 else 0) from by
        refine Finset.sum_congr rfl fun a ha => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        rw [prod_erase_zero]
        simp only [if_true, ha]]
      rw [← Finset.sum_mul, fiber_sum_p1 θ a_0, one_mul])]
  rw [← Finset.sum_mul]
  rw [show (∑ θ ∈ Finset.univ.filter (fun θ : ∀ _ : Fin 2, Fin 2 => θ 0 = 0),
        bg.prior.condProbD 0 0 θ) = 1 from by
    rw [show (∑ θ ∈ Finset.univ.filter (fun θ : ∀ _ : Fin 2, Fin 2 => θ 0 = 0),
          bg.prior.condProbD 0 0 θ) = ∑ θ : ∀ _ : Fin 2, Fin 2, bg.prior.condProbD 0 0 θ from by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases hθ : θ 0 = 0
      · rw [if_pos hθ]
      · rw [if_neg hθ, FinDist.condProbD_of_ne _ _ _ hθ]]
    refine FinDist.condProbD_sum_one_of_pos bgPrior 0 0 ?_
    rw [show bgPrior = bg.prior from rfl]
    -- player 0's type `0` is the support: marginal `1`.
    have : bg.prior.marginalD 0 (0 : Fin 2) = 1 := by
      have h1 := bg_marginal_p0_type1
      have hsum : bg.prior.marginalD 0 (0 : Fin 2) + bg.prior.marginalD 0 (1 : Fin 2) = 1 := by
        have := FinDist.marginalD_sum_one bgPrior 0
        rwa [Fin.sum_univ_two] at this
      rw [h1] at hsum; linarith
    rw [this]; norm_num]
  rw [one_mul]

/-- **`σ⋆` is a mixed BNE.** Player 0's dominant action is optimal at its positive-prior type;
player 1 is indifferent (every deviation also pays `5`). The other (zero-prior) type carries no
constraint in `IsMixedBNE_iff`. -/
theorem mixedStar_isMixedBNE : bg.IsMixedBNE mixedStar := by
  rw [bg.IsMixedBNE_iff]
  intro i θ_i _hpos y
  rw [FinBayesianGame.interimPayoffMixedAction, FinBayesianGame.interimPayoffMixedAction]
  by_cases hi : i = 0
  · -- Player 0: only type `0` is positive-prior (type `1` is excluded by `_hpos`); action `1`
    -- pays `1`, action `0` pays `0`, so `(σ⋆ 0 0)(1) = 1 ≥ y(1)`.
    subst hi
    have hθ0 : θ_i = 0 := by
      fin_cases θ_i
      · rfl
      · refine absurd _hpos (not_lt.mpr ?_)
        change bg.prior.marginalD 0 (1 : Fin 2) ≤ 0
        rw [bg_marginal_p0_type1]
    subst hθ0
    simp_rw [mixedStar_interim_p0]
    -- LHS `= (σ⋆ 0 0)(1) = 1`; RHS `= y(1) ≤ 1`.
    have hstar : (mixedStar 0 (0 : Fin 2)) = stdSimplex.vertex (1 : Fin 2) := by
      simp only [mixedStar, if_true]
    rw [hstar]
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [stdSimplex.vertex_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      stdSimplex.vertex_apply_self, show ((0 : Fin 2) = 1) ↔ False from by decide,
      if_false, if_true]
    -- `0·0 + 1·1 = 1 ≥ y(0)·0 + y(1)·1 = y(1)`, and `y(1) ≤ 1`.
    have hy1 : (y : Fin 2 → ℝ) 1 ≤ 1 := by
      have hsum : (y : Fin 2 → ℝ) 0 + (y : Fin 2 → ℝ) 1 = 1 := by
        have := y.2.2; rwa [Fin.sum_univ_two] at this
      have hy0 : 0 ≤ (y : Fin 2 → ℝ) 0 := y.2.1 0
      linarith
    nlinarith [hy1]
  · -- Player 1: indifferent — both sides equal `5` (LHS at `σ⋆ 1 θ_i`, RHS at any `y`).
    have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    simp_rw [mixedStar_interim_p1 θ_i _hpos]
    -- LHS `= ∑ (σ⋆ 1 θ_i)(a)·5 = 5`; RHS `= ∑ y(a)·5 = 5`.
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [show (∑ a, (mixedStar 1 θ_i) a) = 1 from (mixedStar 1 θ_i).2.2,
        show (∑ a, (y : Fin 2 → ℝ) a) = 1 from y.2.2]

/-- Player 1's uniform action has *both* actions in its support: Each carries mass `1/2 > 0`. -/
theorem mixedStar_p1_support_full (θ_1 : bg.Theta 1) (a_1 : bg.Action 1) :
    0 < (mixedStar 1 θ_1) a_1 := by
  simp only [mixedStar, show ((1 : Fin 2) = 0) ↔ False from by decide, if_false]
  change (0 : ℝ) < (uniformAct : Fin 2 → ℝ) a_1
  change (0 : ℝ) < 1 / 2
  norm_num

/-- **Concrete mixed-BNE existence witness.** `σ⋆` (player 0 pure on `1`, player 1 uniform) *is* a
mixed BNE — binding the existential of `bg_exists_mixedBNE` to a named, hand-verified equilibrium
rather than the abstract existence theorem's opaque selection. -/
theorem bg_exists_mixedBNE_witness : ∃ σ : bg.MixedBehavioralStrategy, bg.IsMixedBNE σ :=
  ⟨mixedStar, mixedStar_isMixedBNE⟩

/-- **The semantic heart: `mixedBNE_indifference`.** In the mixed BNE `σ⋆`, player 1's two support
actions `0` and `1` yield *equal* interim payoffs (both `5`) at every positive-prior type. This is
the substantive content of mixed equilibrium: A player randomizing over several actions must be
exactly indifferent among them. A player/type index swap or a direction reversal would break the
equality. -/
-- `_hpos` fixes the contract to a *positive-prior* type — the non-vacuity point.
-- `mixedBNE_indifference` derives indifference from support positivity, so the marginal is unused.
theorem mixedStar_indifference (θ_1 : bg.Theta 1) (_hpos : 0 < bg.prior.marginalD 1 θ_1) :
    bg.interimPayoffMixed 1 θ_1 0 mixedStar = bg.interimPayoffMixed 1 θ_1 1 mixedStar :=
  bg.mixedBNE_indifference mixedStar mixedStar_isMixedBNE 1 θ_1 0 1
    (mixedStar_p1_support_full θ_1 0) (mixedStar_p1_support_full θ_1 1)

/-- And the indifference value is the hand-computed `5` (anchoring the direction). -/
theorem mixedStar_indifference_value (θ_1 : bg.Theta 1) (hpos : 0 < bg.prior.marginalD 1 θ_1) :
    bg.interimPayoffMixed 1 θ_1 0 mixedStar = 5 :=
  mixedStar_interim_p1 θ_1 hpos 0

/-- **Indifference discharged at player 1's type `0`** (positive prior `bg_marginal_p1_type0_pos`):
both support actions pay `5`. -/
theorem mixedStar_indifference_type0 :
    bg.interimPayoffMixed 1 (0 : Fin 2) 0 mixedStar =
      bg.interimPayoffMixed 1 (0 : Fin 2) 1 mixedStar :=
  mixedStar_indifference 0 bg_marginal_p1_type0_pos

/-- **Indifference discharged at player 1's type `1`** (positive prior `bg_marginal_p1_type1_pos`):
both support actions pay `5`. With `mixedStar_indifference_type0` this closes the header's claim
that *both* player-1 types are interim-indifferent at `σ⋆`, not just type `0`. -/
theorem mixedStar_indifference_type1 :
    bg.interimPayoffMixed 1 (1 : Fin 2) 0 mixedStar =
      bg.interimPayoffMixed 1 (1 : Fin 2) 1 mixedStar :=
  mixedStar_indifference 1 bg_marginal_p1_type1_pos

/-- `mixedBNE_support_ge` on `σ⋆`, player 1: a support action of player 1 weakly dominates the
*other* action — *here with equality* (`5 = 5`, player 1 is indifferent), exercising the support
best-reply property on genuine two-action support. The strict direction guard is the player-0
witness below. -/
theorem mixedStar_support_ge (θ_1 : bg.Theta 1) :
    bg.interimPayoffMixed 1 θ_1 0 mixedStar ≥ bg.interimPayoffMixed 1 θ_1 1 mixedStar :=
  bg.mixedBNE_support_ge mixedStar mixedStar_isMixedBNE 1 θ_1 0 1
    (mixedStar_p1_support_full θ_1 0)

/-- **`mixedBNE_support_ge` (player 0, strict direction guard).** At player 0's positive-prior type
`0`, its full-support action `1` *strictly* beats action `0`: interim payoffs `1 > 0` under the
mixed BNE `σ⋆` (`mixedStar_interim_p0`). This is the direction-sensitive support-ge witness — a
best-response direction reversal (or a dominance-sign flip) would make `0 ≥ 1` and fail here, unlike
player 1's degenerate `5 ≥ 5`. -/
theorem mixedStar_support_ge_p0_strict :
    bg.interimPayoffMixed 0 (0 : Fin 2) 0 mixedStar <
      bg.interimPayoffMixed 0 (0 : Fin 2) 1 mixedStar := by
  rw [mixedStar_interim_p0 0, mixedStar_interim_p0 1]
  norm_num

/-! ## Measurable / continuous-type layer (chunk 4) — cheaply reachable pieces

The measurable Bayesian-game stack `Measurable.{Game, PureBNE, Interim}` is **transitively
exercised** by the imported `CorrelatedCournot.linearStrategy_isBNE`, whose proof drives
`MeasBayesianGame.IsBNE`, `isBNE_of_ae_interim`, `condProfile`, `ae_condProfile_eval`,
`interimPayoff_ae_eq_interimPayoffAction`, `interimPayoffAction`, `marginalType`, and the
integrability route through `integrable_exAntePayoff_of_bdd`'s siblings. *Scope note:* the Cournot
example goes through the pure measurable / interim path; it does **not** touch the *distributional*
(`DistStrategy`, `IsDistBNE`) or *mixed-extension* (`mixedExtension`) modules, so those are not
covered here. Below we additionally pin the small `Measurable.Game` projections directly on the
Cournot game, which the example uses only implicitly. -/

section CournotMeasurable

open CorrelatedCournot

variable (a μ₀ : ℝ) {v₀ v : ℝ}

/-- `actionProfile_apply`: The induced action profile reads off each player's strategy at its type.
On the Cournot game this is the linear schedule `qᵢ(θᵢ) = αᵢ + βᵢ·θᵢ`. -/
theorem cournot_actionProfile_apply (hv₀ : 0 < v₀) (hv : 0 < v)
    (θ : Fin 2 → ℝ) (j : Fin 2) :
    (game a μ₀ hv₀ hv).actionProfile (linearStrategy a μ₀ hv₀ hv) θ j
      = coeffA a μ₀ v₀ v j + coeffB v₀ v j * θ j := by
  rw [MeasBayesianGame.actionProfile_apply, linearStrategy_apply]

/-- `replace_self`: Replacing player `i`'s component and reading it back returns the new
component. -/
theorem cournot_replace_self (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2)
    (f : {f : ℝ → ℝ // Measurable f}) :
    (game a μ₀ hv₀ hv).replace (linearStrategy a μ₀ hv₀ hv) i f i = f :=
  MeasBayesianGame.replace_self ..

/-- `replace_of_ne`: Replacing player `i`'s component leaves a *different* player `j ≠ i`
untouched. Index-swap protection: Player 1's schedule is unchanged when we replace player 0's. -/
theorem cournot_replace_of_ne (hv₀ : 0 < v₀) (hv : 0 < v)
    (f : {f : ℝ → ℝ // Measurable f}) :
    (game a μ₀ hv₀ hv).replace (linearStrategy a μ₀ hv₀ hv) 0 f 1
      = linearStrategy a μ₀ hv₀ hv 1 :=
  MeasBayesianGame.replace_of_ne (game a μ₀ hv₀ hv) (linearStrategy a μ₀ hv₀ hv) 0 f
    (show (1 : Fin 2) ≠ 0 by decide)

/-- `measurable_actionProfile`: The induced action profile is measurable in the type profile (so
the ex-ante payoff integrand built from a `Strategy` is automatically measurable). -/
theorem cournot_measurable_actionProfile (hv₀ : 0 < v₀) (hv : 0 < v) :
    Measurable (fun θ : Fin 2 → ℝ =>
      (game a μ₀ hv₀ hv).actionProfile (linearStrategy a μ₀ hv₀ hv) θ) :=
  (game a μ₀ hv₀ hv).measurable_actionProfile (linearStrategy a μ₀ hv₀ hv)

/-- `measurable_payoff_comp`: The ex-ante payoff integrand is measurable. -/
theorem cournot_measurable_payoff_comp (hv₀ : 0 < v₀) (hv : 0 < v) (i : Fin 2) :
    Measurable (fun θ : Fin 2 → ℝ =>
      (game a μ₀ hv₀ hv).payoff i
        ((game a μ₀ hv₀ hv).actionProfile (linearStrategy a μ₀ hv₀ hv) θ) θ) :=
  (game a μ₀ hv₀ hv).measurable_payoff_comp i (linearStrategy a μ₀ hv₀ hv)

/-- **Transitive coverage anchor.** `linearStrategy_isBNE` (imported) certifies the linear schedule
as a `MeasBayesianGame.IsBNE`, driving the measurable *interim* stack (`Measurable.{Game, PureBNE,
Interim}`) — *not* the distributional or mixed-extension modules. We restate it here as the consumer
witness. -/
theorem cournot_isBNE (hv₀ : 0 < v₀) (hv : 0 < v) :
    (game a μ₀ hv₀ hv).IsBNE (linearStrategy a μ₀ hv₀ hv) :=
  linearStrategy_isBNE a μ₀ hv₀ hv

end CournotMeasurable

end EconlibTest.GameTheory.StrategicBayesian

end
