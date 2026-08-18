/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Existence

/-!
# The mixed extension of a measure-theoretic Bayesian game

The **mixed extension** of a `MeasBayesianGame` replaces each action space by the space of
probability measures over it and integrates payoffs over the (conditionally independent) action
lotteries. A pure measurable strategy of the mixed extension is exactly a **behavioral strategy**
of the original game — definitionally a measurable map from types to action lotteries
(`Theta i → ProbabilityMeasure (Action i)`), which `lotteryKernel` packages as the corresponding
Markov kernel. So `MeasBayesianGame.IsBNE` applied to the mixed extension is behavioral Bayesian
Nash equilibrium, with no new equilibrium notion needed.

This file relates distributional equilibria back to `MeasBayesianGame.IsBNE`: Every distributional
profile disintegrates into a behavioral profile of the mixed extension with the same expected
payoffs, so a distributional equilibrium disintegrates into a (pure) BNE of the mixed extension,
and combining this with `exists_isDistBNE` gives Milgrom–Weber existence in behavioral form. A
distributional equilibrium induced by a pure strategy profile certifies that profile as a BNE of
the original game.

## Main definitions

* `MeasBayesianGame.mixedExtension`: The mixed extension game.
* `MeasBayesianGame.DistStrategy.mixedStrategy`: The behavioral (mixed-extension) strategy
  disintegrating a distributional strategy.
* `MeasBayesianGame.mixedToDist`: The distributional profile induced by a mixed-extension strategy
  profile.

## Main statements

* `MeasBayesianGame.mixedExtension_isBNE_of_isDistBNE`: Distributional equilibria disintegrate into
  pure BNE of the mixed extension.
* `MeasBayesianGame.exists_mixedExtension_isBNE`: Milgrom–Weber existence in behavioral form.
* `MeasBayesianGame.isBNE_of_isDistBNE_toDistStrategy`: Pure-profile distributional equilibria
  certify pure BNE.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

bayesian games, mixed extension, behavioral strategies, milgrom-weber
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- The mixed-extension payoff integrand is jointly measurable in the lottery profile and the type
profile. -/
lemma measurable_mixedPayoff (i : G.Player) :
    Measurable (fun p : (Π j, ProbabilityMeasure (G.Action j)) × G.TypeProfile =>
      ∫ a, G.payoff i a p.2 ∂(Measure.pi fun j => (p.1 j : Measure (G.Action j)))) := by
  let evalKer : ∀ j, Kernel (Π k, ProbabilityMeasure (G.Action k)) (G.Action j) := fun j =>
    ⟨fun σ => (σ j : Measure (G.Action j)),
      measurable_subtype_coe.comp (measurable_pi_apply j)⟩
  haveI : ∀ j, IsMarkovKernel (evalKer j) := fun j => ⟨fun σ => (σ j).2⟩
  let K : Kernel ((Π j, ProbabilityMeasure (G.Action j)) × G.TypeProfile) G.ActionProfile :=
    (Kernel.pi evalKer).comap Prod.fst measurable_fst
  have hf : StronglyMeasurable
      (fun q : ((Π j, ProbabilityMeasure (G.Action j)) × G.TypeProfile) × G.ActionProfile =>
        G.payoff i q.2 q.1.2) :=
    (G.measurable_payoff i).stronglyMeasurable.comp_measurable
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hgoal : (fun p : (Π j, ProbabilityMeasure (G.Action j)) × G.TypeProfile =>
        ∫ a, G.payoff i a p.2 ∂(Measure.pi fun j => (p.1 j : Measure (G.Action j)))) =
      fun p => ∫ a, G.payoff i a p.2 ∂(K p) := rfl
  rw [hgoal]
  exact (StronglyMeasurable.integral_kernel_prod_right' hf).measurable

/-- The **mixed extension**: The measure-theoretic Bayesian game whose actions are probability
measures over the original actions and whose payoffs integrate the original payoffs over the
players' (independent) action lotteries. Its pure measurable strategies are exactly behavioral
strategies of the original game — measurable maps `Theta i → ProbabilityMeasure (Action i)`, which
`lotteryKernel` packages as the corresponding Markov kernels. -/
def mixedExtension : MeasBayesianGame where
  Player := G.Player
  Theta := G.Theta
  Action := fun i => ProbabilityMeasure (G.Action i)
  prior := G.prior
  payoff := fun i σ θ => ∫ a, G.payoff i a θ ∂(Measure.pi fun j => (σ j : Measure (G.Action j)))
  measurable_payoff := G.measurable_mixedPayoff

/-- The mixed-extension payoff is the original payoff integrated over the players' independent
action lotteries. -/
@[simp] lemma mixedExtension_payoff (i : G.Player) (σ : Π j, ProbabilityMeasure (G.Action j))
    (θ : G.TypeProfile) :
    G.mixedExtension.payoff i σ θ =
      ∫ a, G.payoff i a θ ∂(Measure.pi fun j => (σ j : Measure (G.Action j))) := rfl

/-- The mixed extension inherits the original game's common prior. -/
@[simp] lemma mixedExtension_prior : G.mixedExtension.prior = G.prior := rfl

/-- The mixed-extension payoff inherits the original game's payoff bound: A probability average of
values bounded by `C` is itself bounded by `C`. -/
lemma abs_mixedExtension_payoff_le (i : G.Player) {C : ℝ}
    (hbdd : ∀ a θ, |G.payoff i a θ| ≤ C) (σ : Π j, ProbabilityMeasure (G.Action j))
    (θ : G.TypeProfile) : |G.mixedExtension.payoff i σ θ| ≤ C := by
  rw [mixedExtension_payoff, ← Real.norm_eq_abs]
  have hle := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun j => (σ j : Measure (G.Action j))) (f := fun a => G.payoff i a θ)
    (C := C) (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hbdd a θ)
  simpa using hle

variable {G}
variable [∀ i, StandardBorelSpace (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- The **behavioral strategy disintegrating a distributional strategy**, as a pure measurable
strategy of the mixed extension: The type-indexed family of conditional action lotteries. -/
def DistStrategy.mixedStrategy {i : G.Player} (σ : G.DistStrategy i) :
    {f : G.Theta i → ProbabilityMeasure (G.Action i) // Measurable f} :=
  ⟨fun t => ⟨σ.kernel t, inferInstance⟩, σ.kernel.measurable.subtype_mk⟩

variable (G)

/-- The action-lottery kernel packaged in a measurable family of action lotteries (a
mixed-extension strategy component). -/
def lotteryKernel {i : G.Player}
    (f : {f : G.Theta i → ProbabilityMeasure (G.Action i) // Measurable f}) :
    Kernel (G.Theta i) (G.Action i) :=
  ⟨fun t => (f.1 t : Measure (G.Action i)), measurable_subtype_coe.comp f.2⟩

instance {i : G.Player} (f : {f : G.Theta i → ProbabilityMeasure (G.Action i) // Measurable f}) :
    IsMarkovKernel (lotteryKernel (G := G) f) :=
  ⟨fun t => (f.1 t).2⟩

/-- The distributional profile induced by a mixed-extension (behavioral) strategy profile: Each
player's marginal type law coupled with its action-lottery kernel. -/
def mixedToDist (s : G.mixedExtension.Strategy) : G.DistProfile := fun i =>
  { law := (G.marginalType i) ⊗ₘ lotteryKernel (G := G) (s i)
    marginal_fst := Measure.fst_compProd (G.marginalType i) (lotteryKernel (G := G) (s i)) }

/-- **Payoff consistency of disintegration**: A mixed-extension strategy profile earns the same
ex-ante payoff as its induced distributional profile. -/
lemma mixedExtension_exAntePayoff_eq (i : G.Player) (s : G.mixedExtension.Strategy)
    {C : ℝ} (hbdd : ∀ a θ, |G.payoff i a θ| ≤ C) :
    G.mixedExtension.exAntePayoff i s = G.distPayoff i (G.mixedToDist s) := by
  -- Fix the index to `G.Player` (rather than the defeq `G.mixedExtension.Player`) so the product
  -- kernel's Markov/S-finite instances resolve.
  set κ : ∀ j : G.Player, Kernel (G.Theta j) (G.Action j) :=
    fun j => lotteryKernel (G := G) (s j) with hκdef
  have hκ : ∀ j, (G.mixedToDist s j).law = (G.marginalType j) ⊗ₘ κ j := fun _ => rfl
  have houtcome : G.outcome (G.mixedToDist s) =
      G.prior ⊗ₘ Kernel.pi
        (fun j => (κ j).comap (fun θ => θ j) (measurable_pi_apply j)) :=
    G.outcome_eq_compProd (G.mixedToDist s) κ hκ
  have hpayoff_meas : Measurable (fun p : G.TypeProfile × G.ActionProfile =>
      G.payoff i p.2 p.1) :=
    (G.measurable_payoff i).comp (measurable_snd.prodMk measurable_fst)
  have hint : Integrable (fun p => G.payoff i p.2 p.1) (G.outcome (G.mixedToDist s)) := by
    refine ⟨hpayoff_meas.aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hbdd p.2 p.1
  rw [houtcome] at hint
  unfold distPayoff
  rw [houtcome, Measure.integral_compProd hint, exAntePayoff]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [mixedExtension_payoff, actionProfile, Kernel.pi_apply, Kernel.comap_apply]
  rfl

/-- Distributional strategies are determined by their joint law: Equal laws force equal
strategies. -/
lemma DistStrategy.ext {G : MeasBayesianGame} {i : G.Player} {τ τ' : G.DistStrategy i}
    (h : τ.law = τ'.law) : τ = τ' := by
  cases τ; cases τ'; subst h; rfl

/-- The behavioral kernel of a distributional strategy is exactly the lottery kernel of its
disintegrating mixed-extension strategy. -/
lemma lotteryKernel_mixedStrategy {i : G.Player} (σ : G.DistStrategy i) :
    lotteryKernel (G := G) σ.mixedStrategy = σ.kernel := by
  refine Kernel.ext fun t => ?_
  rfl

/-- The distributional profile recovered from the disintegration of `σ` is `σ` itself. -/
lemma mixedToDist_mixedStrategy (σ : G.DistProfile) :
    (G.mixedToDist (fun i => (σ i).mixedStrategy)) = σ := by
  funext i
  refine DistStrategy.ext ?_
  change (G.marginalType i) ⊗ₘ lotteryKernel (G := G) (σ i).mixedStrategy = (σ i).law
  rw [lotteryKernel_mixedStrategy, ← (σ i).law_eq_compProd]

/-- **Distributional equilibria disintegrate into behavioral equilibria**: If a distributional
profile is a distributional BNE of a game with bounded payoffs, its disintegration is a (pure) BNE
of the mixed extension — i.e. a behavioral Bayesian Nash equilibrium. -/
theorem mixedExtension_isBNE_of_isDistBNE
    (hbdd : ∀ i, ∃ C, ∀ a θ, |G.payoff i a θ| ≤ C)
    {σ : G.DistProfile} (hσ : G.IsDistBNE σ) :
    G.mixedExtension.IsBNE (fun i => (σ i).mixedStrategy) := by
  rw [isBNE_iff]
  refine ⟨fun i s' hagree _hs'int => ?_, fun i => ?_⟩
  -- Incumbent integrability: the mixed payoff inherits the boundedness of `G`'s payoff.
  on_goal 2 =>
    obtain ⟨C, hC⟩ := hbdd i
    exact G.mixedExtension.integrable_exAntePayoff_of_bdd i _
      (fun θ => G.abs_mixedExtension_payoff_le i hC _ θ)
  -- intentionally unused: boundedness supplies all integrability
  obtain ⟨C, hC⟩ := hbdd i
  have hagree' : ∀ j, j ≠ i → G.mixedToDist s' j = σ j := by
    intro j hj
    refine DistStrategy.ext ?_
    change (G.marginalType j) ⊗ₘ lotteryKernel (G := G) (s' j) = (σ j).law
    rw [hagree j hj, lotteryKernel_mixedStrategy, ← (σ j).law_eq_compProd]
  have hint' : Integrable (fun p => G.payoff i p.2 p.1) (G.outcome (G.mixedToDist s')) := by
    refine ⟨((G.measurable_payoff i).comp
      (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hC p.2 p.1
  have hdom := ((G.isDistBNE_iff σ).1 hσ).1 i (G.mixedToDist s') hagree' hint'
  rw [ge_iff_le, G.mixedExtension_exAntePayoff_eq i s' (fun a θ => hC a θ),
    G.mixedExtension_exAntePayoff_eq i (fun j => (σ j).mixedStrategy) (fun a θ => hC a θ),
    G.mixedToDist_mixedStrategy σ]
  exact hdom

/-- **Milgrom–Weber existence, behavioral form** (Milgrom and Weber 1985). Under the hypotheses of
`exists_isDistBNE`, the mixed extension has a pure Bayesian Nash equilibrium — that is, the game
has a behavioral-strategy equilibrium in the sense of `MeasBayesianGame.IsBNE` applied to the mixed
extension. -/
theorem exists_mixedExtension_isBNE
    [∀ i, TopologicalSpace (G.Action i)] [∀ i, CompactSpace (G.Action i)]
    [∀ i, TopologicalSpace.MetrizableSpace (G.Action i)] [∀ i, BorelSpace (G.Action i)]
    (hbdd : ∀ i, ∃ C, ∀ a θ, |G.payoff i a θ| ≤ C)
    (hcont : ∀ i θ, Continuous fun a => G.payoff i a θ)
    (hac : G.prior ≪ Measure.pi fun i => G.marginalType i) :
    ∃ s : G.mixedExtension.Strategy, G.mixedExtension.IsBNE s := by
  obtain ⟨σ, hσ⟩ := G.exists_isDistBNE hbdd hcont hac
  exact ⟨fun i => (σ i).mixedStrategy, G.mixedExtension_isBNE_of_isDistBNE hbdd hσ⟩

/-- **Pure-profile certification**: If the distributional profile induced by a pure strategy
profile is a distributional BNE of a game with bounded payoffs, then the pure profile is a Bayesian
Nash equilibrium of the original game. -/
theorem isBNE_of_isDistBNE_toDistStrategy
    (hbdd : ∀ i, ∃ C, ∀ a θ, |G.payoff i a θ| ≤ C) (s : G.Strategy)
    (hσ : G.IsDistBNE (fun i => G.toDistStrategy i (s i))) :
    G.IsBNE s := by
  rw [isBNE_iff]
  refine ⟨fun i s' hagree _hs'int => ?_, fun i => ?_⟩
  -- Incumbent integrability of the original game follows from boundedness.
  on_goal 2 =>
    obtain ⟨C, hC⟩ := hbdd i
    exact G.integrable_exAntePayoff_of_bdd i s (fun θ => hC _ θ)
  -- intentionally unused: `distPayoff_toDistStrategy` is unconditional and boundedness supplies
  -- all integrability
  obtain ⟨C, hC⟩ := hbdd i
  have hagree' : ∀ j, j ≠ i →
      G.toDistStrategy j (s' j) = G.toDistStrategy j (s j) := fun j hj => by
    rw [hagree j hj]
  have hint' : Integrable (fun p => G.payoff i p.2 p.1)
      (G.outcome (fun j => G.toDistStrategy j (s' j))) := by
    refine ⟨((G.measurable_payoff i).comp
      (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hC p.2 p.1
  have hdom := ((G.isDistBNE_iff _).1 hσ).1 i (fun j => G.toDistStrategy j (s' j)) hagree' hint'
  have heq_s : G.distPayoff i (fun j => G.toDistStrategy j (s j)) = G.exAntePayoff i s :=
    G.distPayoff_toDistStrategy i s
  have heq_s' : G.distPayoff i (fun j => G.toDistStrategy j (s' j)) = G.exAntePayoff i s' :=
    G.distPayoff_toDistStrategy i s'
  rw [ge_iff_le, heq_s', heq_s] at hdom
  exact hdom

end MeasBayesianGame

end Econlib.GameTheory
end
