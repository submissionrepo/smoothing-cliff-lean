/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Measure-theoretic Bayesian games and ex-ante payoffs

This file defines `MeasBayesianGame`, the continuous-type sibling of `FinBayesianGame` (Harsanyi
1967–68). Players are finite, but each player's type and action spaces are arbitrary measurable
spaces (standard Borel on the type side, so the common prior can be disintegrated coordinatewise),
the common prior is a probability `Measure` over the type-profile space — correlated types are
allowed, the prior need not be a product — and payoffs are integrated rather than summed.

Strategies are deterministic, bundled as measurable maps (`MeasBayesianGame.Strategy`), so the
payoff integrands are always measurable: A non-measurable strategy is not expressible. These are
**pure** strategies; behavioral and mixed strategies arise as pure strategies of the mixed
extension (see `Measurable.MixedExtension`). The ex-ante payoff
`exAntePayoff i s = ∫ θ, payoff i (actionProfile s θ) θ ∂prior` is the value functional that the
Bayesian Nash predicate (in `Measurable.PureBNE`) plugs into the abstract `EquilibriumProblem`
spine, mirroring the finite stack's `interimPayoffAction`.

## Main definitions

* `MeasBayesianGame`: Finite players, measurable type and action spaces, a measure-valued common
  prior, and a jointly measurable payoff.
* `MeasBayesianGame.Strategy`: Pure (deterministic) measurable strategy profiles.
* `MeasBayesianGame.actionProfile`: The action profile induced by a strategy and a type profile.
* `MeasBayesianGame.exAntePayoff`: Ex-ante expected payoff of a strategy profile.

## Main statements

* `MeasBayesianGame.measurable_actionProfile`: The induced action profile is measurable in the type
  profile.
* `MeasBayesianGame.measurable_payoff_comp`: The ex-ante payoff integrand is measurable.
* `MeasBayesianGame.integrable_exAntePayoff_of_bdd`: A bounded measurable payoff is integrable
  against the prior, so its ex-ante payoff is a true integral, not a junk-zero Bochner value.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, continuous types, ex-ante payoff, measurable strategies
-/

@[expose] public section

open MeasureTheory Function

noncomputable section
namespace Econlib.GameTheory

/-- A measure-theoretic Bayesian game with a finite set of players, arbitrary measurable type and
action spaces, and a common prior given by a probability measure over the type-profile space.

The type spaces are required to be standard Borel so that the prior can be disintegrated along each
coordinate (used to define interim payoffs in `Measurable.Interim`). The prior is an arbitrary
probability measure on `Π i, Theta i`; correlation across players is permitted. -/
structure MeasBayesianGame where
  /-- The (finite) set of players. -/
  Player : Type*
  [instFintypePlayer : Fintype Player]
  [instDecEqPlayer : DecidableEq Player]
  /-- Each player's type space. -/
  Theta : Player → Type*
  [instMeasTheta : ∀ i, MeasurableSpace (Theta i)]
  [instSBTheta : ∀ i, StandardBorelSpace (Theta i)]
  [instNeTheta : ∀ i, Nonempty (Theta i)]
  /-- Each player's action space. -/
  Action : Player → Type*
  [instMeasAction : ∀ i, MeasurableSpace (Action i)]
  /-- The common prior over type profiles. Correlated types are allowed. -/
  prior : MeasureTheory.Measure (Π i, Theta i)
  [instProbPrior : MeasureTheory.IsProbabilityMeasure prior]
  /-- Payoff to player `i` given an action profile and a type profile. -/
  payoff : Player → (Π i, Action i) → (Π i, Theta i) → ℝ
  /-- Payoffs are jointly measurable in the action and type profiles. -/
  measurable_payoff : ∀ i,
    Measurable (fun p : (Π j, Action j) × (Π j, Theta j) => payoff i p.1 p.2)

attribute [instance] MeasBayesianGame.instFintypePlayer MeasBayesianGame.instDecEqPlayer
  MeasBayesianGame.instMeasTheta MeasBayesianGame.instSBTheta MeasBayesianGame.instNeTheta
  MeasBayesianGame.instMeasAction MeasBayesianGame.instProbPrior

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- A type profile. -/
abbrev TypeProfile := Π i, G.Theta i

/-- An action profile. -/
abbrev ActionProfile := Π i, G.Action i

/-- A **pure** measurable strategy profile: Each player chooses a deterministic measurable map from
its type to its action. Measurability is bundled into the type, so an ex-ante payoff integrand
built from a `Strategy` is automatically measurable. Behavioral (randomized) strategies are the
pure strategies of the mixed extension — see `Measurable.MixedExtension`. -/
def Strategy := ∀ i, {f : G.Theta i → G.Action i // Measurable f}

instance : CoeFun G.Strategy (fun _ => ∀ i, G.Theta i → G.Action i) where
  coe s i := (s i).1

/-- The action profile induced by strategy `s` at type profile `θ`. -/
def actionProfile (s : G.Strategy) (θ : G.TypeProfile) : G.ActionProfile :=
  fun j => (s j).1 (θ j)

@[simp] lemma actionProfile_apply (s : G.Strategy) (θ : G.TypeProfile) (j : G.Player) :
    G.actionProfile s θ j = (s j).1 (θ j) := rfl

/-- The induced action profile is measurable in the type profile. -/
lemma measurable_actionProfile (s : G.Strategy) :
    Measurable (fun θ : G.TypeProfile => G.actionProfile s θ) := by
  refine measurable_pi_lambda _ fun j => ?_
  exact (s j).2.comp (measurable_pi_apply j)

/-- The ex-ante payoff integrand `θ ↦ payoff i (actionProfile s θ) θ` is measurable. -/
lemma measurable_payoff_comp (i : G.Player) (s : G.Strategy) :
    Measurable (fun θ : G.TypeProfile => G.payoff i (G.actionProfile s θ) θ) :=
  (G.measurable_payoff i).comp ((G.measurable_actionProfile s).prodMk measurable_id)

/-- The **ex-ante expected payoff** of player `i` under strategy profile `s`: The payoff integrated
against the common prior over type profiles. -/
def exAntePayoff (i : G.Player) (s : G.Strategy) : ℝ :=
  ∫ θ, G.payoff i (G.actionProfile s θ) θ ∂G.prior

/-- Replace player `i`'s component of a strategy profile, keeping the others fixed. -/
def replace (s : G.Strategy) (i : G.Player)
    (f : {f : G.Theta i → G.Action i // Measurable f}) : G.Strategy :=
  Function.update s i f

@[simp] lemma replace_self (s : G.Strategy) (i : G.Player)
    (f : {f : G.Theta i → G.Action i // Measurable f}) :
    G.replace s i f i = f := Function.update_self ..

lemma replace_of_ne (s : G.Strategy) (i : G.Player)
    (f : {f : G.Theta i → G.Action i // Measurable f}) {j : G.Player} (h : j ≠ i) :
    G.replace s i f j = s j := Function.update_of_ne h ..

/-- A bounded measurable payoff integrand is integrable against the (probability) prior, so the
ex-ante payoff is a true integral rather than the junk-zero value of a non-integrable Bochner
integral. Auctions and compact-action games satisfy the bound per strategy profile. -/
lemma integrable_exAntePayoff_of_bdd (i : G.Player) (s : G.Strategy) {C : ℝ}
    (hC : ∀ θ, |G.payoff i (G.actionProfile s θ) θ| ≤ C) :
    Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior := by
  refine ⟨(G.measurable_payoff_comp i s).aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs]
  exact hC θ

end MeasBayesianGame

end Econlib.GameTheory
end
