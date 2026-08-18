/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Interim
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Econlib.Math.MeasureTheory.PiCompProd
public import Econlib.Math.Probability.KernelPi

/-!
# Distributional strategies for measure-theoretic Bayesian games

Milgrom and Weber (1985) represent a player's randomized behavior in a Bayesian game by a
**distributional strategy**: A joint probability law on the player's type–action square whose type
marginal is the player's true type distribution (the marginal of the common prior). This file
defines distributional strategies for `MeasBayesianGame`, their induced outcome law, expected
payoffs, and the distributional Bayesian Nash equilibrium predicate `IsDistBNE` as an
`EquilibriumProblem`.

## Main definitions

* `MeasBayesianGame.DistStrategy`: A joint type–action law with the correct type marginal.
* `MeasBayesianGame.outcome`: The joint law on type and action profiles induced by a distributional
  profile.
* `MeasBayesianGame.distPayoff`: Expected payoff under a distributional profile.
* `MeasBayesianGame.IsDistBNE`: Distributional Bayesian Nash equilibrium.

## Main statements

* `MeasBayesianGame.outcome_eq_compProd`: Outcome semantics depend only on the strategies' laws;
  any measurable disintegration computes the outcome.
* `MeasBayesianGame.distPayoff_toDistStrategy`: The induced distributional profile of a pure
  strategy profile earns the pure ex-ante payoff.

## Notes

The common prior may correlate types, so the joint type–action law induced by a distributional
profile is not the product of the players' strategies. Conditionally on the type profile `θ`,
players randomize independently, each according to the disintegration (`Measure.condKernel`) of
their distributional strategy at their own coordinate `θ i`, giving
`outcome σ = prior ⊗ₘ (⊗ᵢ (σ i).kernel (θ i))`. This depends on each `σ i` only through its law,
not the choice of disintegration (`outcome_eq_compProd`), and requires no absolute-continuity
assumption. Under Milgrom and Weber's "absolutely continuous information" (R2) this outcome
integral coincides with their density form `∫ u·g d(⊗ᵢ σᵢ)`.

As in `Measurable.PureBNE`, a unilateral deviation counts only when its payoff integrand is
integrable against the deviated outcome law, guarding against junk-zero Bochner values.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

bayesian games, distributional strategies, milgrom-weber, disintegration
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- A **distributional strategy** for player `i`: A joint probability law on the player's
type–action square whose type marginal is the player's marginal type distribution (Milgrom–Weber).
The marginal constraint is part of the type, so a semantically invalid distributional strategy is
not expressible. -/
structure DistStrategy (i : G.Player) where
  /-- The joint type–action law. -/
  law : Measure (G.Theta i × G.Action i)
  [instProbLaw : IsProbabilityMeasure law]
  /-- The type marginal is the player's true type distribution. -/
  marginal_fst : law.map Prod.fst = G.marginalType i

attribute [instance] DistStrategy.instProbLaw

/-- A profile of distributional strategies. -/
abbrev DistProfile := ∀ i, G.DistStrategy i

variable {G}

/-- The type marginal of a distributional strategy, as `Measure.fst`. -/
lemma DistStrategy.fst_law {i : G.Player} (σ : G.DistStrategy i) :
    σ.law.fst = G.marginalType i := σ.marginal_fst

section Kernel

variable [∀ i, StandardBorelSpace (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- The **behavioral kernel** of a distributional strategy: The disintegration of its law along the
type coordinate. -/
def DistStrategy.kernel {i : G.Player} (σ : G.DistStrategy i) :
    Kernel (G.Theta i) (G.Action i) :=
  σ.law.condKernel

instance {i : G.Player} (σ : G.DistStrategy i) : IsMarkovKernel σ.kernel := by
  unfold DistStrategy.kernel; infer_instance

/-- A distributional strategy is recovered from its type marginal and behavioral kernel. -/
lemma DistStrategy.law_eq_compProd {i : G.Player} (σ : G.DistStrategy i) :
    σ.law = (G.marginalType i) ⊗ₘ σ.kernel := by
  -- `Measure.compProd_fst_condKernel` plus the marginal constraint.
  rw [← σ.fst_law]
  exact (σ.law.disintegrate σ.law.condKernel).symm

variable (G)

/-- The **conditional action kernel** of a distributional profile: Given a type profile, players
randomize independently, each according to its behavioral kernel evaluated at its own coordinate. -/
def actionKernel (σ : G.DistProfile) : Kernel G.TypeProfile G.ActionProfile :=
  Kernel.pi (fun i => (σ i).kernel.comap (fun θ => θ i) (measurable_pi_apply i))

instance (σ : G.DistProfile) : IsMarkovKernel (G.actionKernel σ) := by
  unfold actionKernel; infer_instance

/-- The **outcome law** of a distributional profile: The joint distribution of the type profile
(drawn from the common prior) and the action profile (drawn conditionally independently from the
behavioral kernels). Correlation across types is inherited from the prior. -/
def outcome (σ : G.DistProfile) : Measure (G.TypeProfile × G.ActionProfile) :=
  G.prior ⊗ₘ G.actionKernel σ

instance (σ : G.DistProfile) : IsProbabilityMeasure (G.outcome σ) := by
  unfold outcome; infer_instance

/-- **Outcome semantics are disintegration-independent**: If each `σ i` factors as
`marginalType i ⊗ₘ κ i` for measurable Markov kernels `κ i`, then the outcome is computed by the
`κ i` — the canonical `condKernel` in the definition is immaterial. -/
theorem outcome_eq_compProd (σ : G.DistProfile)
    (κ : ∀ i, Kernel (G.Theta i) (G.Action i)) [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (σ i).law = (G.marginalType i) ⊗ₘ κ i) :
    G.outcome σ =
      G.prior ⊗ₘ Kernel.pi (fun i => (κ i).comap (fun θ => θ i) (measurable_pi_apply i)) := by
  have hae : ∀ i, ∀ᵐ θ ∂G.prior, κ i (θ i) = (σ i).kernel (θ i) := by
    intro i
    have hfst : (σ i).law = (σ i).law.fst ⊗ₘ κ i := by rw [(σ i).fst_law]; exact hκ i
    have huniq : ∀ᵐ t ∂(σ i).law.fst, κ i t = (σ i).law.condKernel t :=
      ProbabilityTheory.eq_condKernel_of_measure_eq_compProd (κ i) hfst
    rw [(σ i).fst_law] at huniq
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable huniq
  have hall : ∀ᵐ θ ∂G.prior, ∀ i, κ i (θ i) = (σ i).kernel (θ i) := ae_all_iff.2 hae
  refine Measure.compProd_congr ?_
  filter_upwards [hall] with θ hθ
  simp only [Kernel.pi_apply, Kernel.comap_apply]
  exact congrArg Measure.pi (funext fun i => (hθ i).symm)

/-- **Expected payoff** of player `i` under a distributional profile: The payoff integrated against
the outcome law. -/
def distPayoff (i : G.Player) (σ : G.DistProfile) : ℝ :=
  ∫ p, G.payoff i p.2 p.1 ∂(G.outcome σ)

/-- The equilibrium problem associated with distributional Bayesian Nash equilibrium. The deviator
index is a player; a legal deviation rewrites only that player's distributional strategy and keeps
the payoff integrand integrable against the deviated outcome; the value is the player's expected
payoff. -/
def distBnePred : EquilibriumProblem where
  S := G.DistProfile
  I := G.Player
  swap := fun i σ σ' =>
    (∀ j, j ≠ i → σ' j = σ j) ∧
      Integrable (fun p => G.payoff i p.2 p.1) (G.outcome σ')
  value := fun i σ => G.distPayoff i σ

/-- **Distributional Bayesian Nash equilibrium** (Milgrom–Weber): No player can raise its expected
payoff by a unilateral (integrable) deviation of its distributional strategy, and the incumbent
profile's own payoff integrand is integrable against the incumbent outcome for every player.

As in `MeasBayesianGame.IsBNE`, the incumbent-integrability conjunct is not redundant: The
deviation guard gates only profiles a player may deviate to, never the incumbent, so without it a
non- integrable incumbent integrand (Bochner value `0`) could spuriously pass the predicate. -/
structure IsDistBNE (σ : G.DistProfile) : Prop where
  /-- No player has a profitable unilateral integrable deviation. -/
  isEquilibrium : G.distBnePred.IsEquilibrium σ
  /-- The incumbent outcome's payoff integrand is integrable for every player. -/
  integrable : ∀ i, Integrable (fun p => G.payoff i p.2 p.1) (G.outcome σ)

@[simp] lemma distBnePred_swap_iff (i : G.Player) (σ σ' : G.DistProfile) :
    G.distBnePred.swap i σ σ' ↔
      (∀ j, j ≠ i → σ' j = σ j) ∧
        Integrable (fun p => G.payoff i p.2 p.1) (G.outcome σ') := Iff.rfl

@[simp] lemma distBnePred_value_eq (i : G.Player) (σ : G.DistProfile) :
    G.distBnePred.value i σ = G.distPayoff i σ := rfl

/-- Unfolded characterization of `IsDistBNE`: The best-response condition over unilateral
integrable deviations, together with incumbent-outcome integrability for every player. -/
theorem isDistBNE_iff (σ : G.DistProfile) :
    G.IsDistBNE σ ↔
      (∀ (i : G.Player) (σ' : G.DistProfile), (∀ j, j ≠ i → σ' j = σ j) →
        Integrable (fun p => G.payoff i p.2 p.1) (G.outcome σ') →
          G.distPayoff i σ ≥ G.distPayoff i σ') ∧
      (∀ i, Integrable (fun p => G.payoff i p.2 p.1) (G.outcome σ)) := by
  constructor
  · rintro ⟨h, hint⟩
    exact ⟨fun i σ' hagree hintd => h i σ' ⟨hagree, hintd⟩, hint⟩
  · rintro ⟨h, hint⟩
    exact ⟨fun i σ' hσ' => h i σ' hσ'.1 hσ'.2, hint⟩

end Kernel

section Pure

variable (G)

/-- The marginal constraint of the distributional strategy induced by a measurable pure strategy. -/
lemma map_graph_fst (i : G.Player) (f : {f : G.Theta i → G.Action i // Measurable f}) :
    ((G.marginalType i).map (fun t => (t, f.1 t))).map Prod.fst = G.marginalType i := by
  rw [Measure.map_map measurable_fst (measurable_id'.prodMk f.2)]
  exact Measure.map_id

/-- The **distributional strategy induced by a pure strategy**: The law of `(t, f t)` under the
marginal type distribution — the graph measure of `f`. -/
def toDistStrategy (i : G.Player) (f : {f : G.Theta i → G.Action i // Measurable f}) :
    G.DistStrategy i :=
  letI : IsProbabilityMeasure ((G.marginalType i).map (fun t => (t, f.1 t))) :=
    Measure.isProbabilityMeasure_map (measurable_id.prodMk f.2).aemeasurable
  { law := (G.marginalType i).map (fun t => (t, f.1 t))
    marginal_fst := G.map_graph_fst i f }

/-- **Payoff consistency of the pure-to-distributional embedding**: The induced distributional
profile of a pure strategy profile earns exactly the pure ex-ante payoff. No integrability is
needed: The outcome of the induced profile is the pushforward of the prior along
`θ ↦ (θ, actionProfile s θ)`, so the two integrals coincide. -/
theorem distPayoff_toDistStrategy [∀ i, StandardBorelSpace (G.Action i)]
    [∀ i, Nonempty (G.Action i)] (i : G.Player) (s : G.Strategy) :
    G.distPayoff i (fun j => G.toDistStrategy j (s j)) = G.exAntePayoff i s := by
  have hlaw : ∀ j, (G.toDistStrategy j (s j)).law
      = (G.marginalType j) ⊗ₘ Kernel.deterministic (s j).1 (s j).2 := by
    intro j
    rw [Measure.compProd_deterministic]
    rfl
  have houtcome : G.outcome (fun j => G.toDistStrategy j (s j))
      = G.prior.map (fun θ => (θ, G.actionProfile s θ)) := by
    rw [G.outcome_eq_compProd _ (fun j => Kernel.deterministic (s j).1 (s j).2) hlaw]
    have hker : Kernel.pi (fun j => (Kernel.deterministic (s j).1 (s j).2).comap
          (fun θ : G.TypeProfile => θ j) (measurable_pi_apply j))
        = Kernel.deterministic (G.actionProfile s) (G.measurable_actionProfile s) := by
      refine Kernel.ext fun θ => ?_
      rw [Kernel.pi_apply, Kernel.deterministic_apply]
      simp only [Kernel.comap_apply, Kernel.deterministic_apply]
      exact Measure.pi_dirac _
    rw [hker, Measure.compProd_deterministic]
  have hpayoff_meas : Measurable (fun p : G.TypeProfile × G.ActionProfile =>
      G.payoff i p.2 p.1) :=
    (G.measurable_payoff i).comp (measurable_snd.prodMk measurable_fst)
  rw [distPayoff, houtcome,
    integral_map (measurable_id'.prodMk (G.measurable_actionProfile s)).aemeasurable
      hpayoff_meas.aestronglyMeasurable]
  rfl

end Pure

end MeasBayesianGame

end Econlib.GameTheory
end
