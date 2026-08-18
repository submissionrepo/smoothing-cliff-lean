/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Distributional
public import Econlib.Math.MeasureTheory.PiCompProd
public import Econlib.Math.MeasureTheory.PiProdCongr

/-!
# The Milgrom–Weber density representation of distributional payoffs

Under **absolutely continuous information** (Milgrom and Weber's R2: The common prior is absolutely
continuous with respect to the product of its marginals), expected payoffs under a distributional
profile admit the Milgrom–Weber integral representation

`∫ f d(outcome σ) = ∫ f(t, a) · g(t) d(⊗ᵢ σᵢ)`,

where `g = d(prior)/d(⊗ᵢ ηᵢ)` is the information density. The left side is the disintegration-based
outcome semantics of distributional strategies; the right side is an integral against the product
of the players' distributional-strategy laws.

## Main statements

* `MeasBayesianGame.integral_outcome_eq_density`: The density representation of outcome integrals.

## Notes

The statement isolates the role of absolute continuity: It converts the disintegration-based
outcome law into the density-weighted product-law expression used for continuity arguments.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

bayesian games, distributional strategies, milgrom-weber, absolutely continuous information,
radon-nikodym
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- The **information density** of Milgrom–Weber's "absolutely continuous information": The
Radon–Nikodym derivative of the common prior with respect to the product of its marginals, as a
real-valued function. -/
def informationDensity : G.TypeProfile → ℝ :=
  fun θ => (G.prior.rnDeriv (Measure.pi fun i => G.marginalType i) θ).toReal

/-- The information density is integrable against the product of the marginals. -/
lemma integrable_informationDensity :
    Integrable G.informationDensity (Measure.pi fun i => G.marginalType i) :=
  Measure.integrable_toReal_rnDeriv

/-- Push a density across a measurable equivalence: Weighting before mapping equals mapping then
weighting by the transported density. -/
private lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    (μ.withDensity (fun a => ρ (e a))).map e = (μ.map e).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← setLIntegral_map hs hρ e.measurable]

variable [∀ i, StandardBorelSpace (G.Action i)] [∀ i, Nonempty (G.Action i)]

/-- **The Milgrom–Weber density representation.** Under absolutely continuous information (prior ≪
product of marginals), the outcome integral of any measurable function equals the density-weighted
integral against the product of the distributional strategies. No integrability is assumed: The two
sides are the same integral after a measure isomorphism and a density rewrite. -/
theorem integral_outcome_eq_density
    (hac : G.prior ≪ Measure.pi fun i => G.marginalType i)
    (σ : G.DistProfile) {f : G.TypeProfile × G.ActionProfile → ℝ}
    (hf : Measurable f) :
    ∫ p, f p ∂(G.outcome σ) =
      ∫ s, f (fun i => (s i).1, fun i => (s i).2) * G.informationDensity (fun i => (s i).1)
        ∂(Measure.pi fun i => (σ i).law) := by
  classical
  set ηhat := Measure.pi (fun i => G.marginalType i) with hηhat_def
  set g' : G.TypeProfile → ℝ≥0∞ := G.prior.rnDeriv ηhat with hg'_def
  have hg'_meas : Measurable g' := Measure.measurable_rnDeriv _ _
  set e := MeasurableEquiv.piProdEquivProdPi (X := G.Theta) (Y := G.Action) with he_def
  -- Radon–Nikodym: the prior is the density-weighted product of its marginals.
  have hprior : ηhat.withDensity g' = G.prior := Measure.withDensity_rnDeriv_eq _ _ hac
  -- Move the density across the disintegration.
  have houtcome : G.outcome σ = (ηhat ⊗ₘ G.actionKernel σ).withDensity (fun p => g' p.1) := by
    rw [outcome, ← hprior, Measure.withDensity_compProd_fst _ _ hg'_meas]
  -- The undensitied coupling is the reindexed product of the strategies' laws.
  have hcompProd_eq : ηhat ⊗ₘ G.actionKernel σ = (Measure.pi fun i => (σ i).law).map e := by
    have hpi : Measure.pi (fun i => (σ i).law) = (ηhat ⊗ₘ G.actionKernel σ).map e.symm := by
      calc Measure.pi (fun i => (σ i).law)
          = Measure.pi (fun i => (G.marginalType i) ⊗ₘ (σ i).kernel) :=
            congrArg Measure.pi (funext fun i => (σ i).law_eq_compProd)
        _ = (ηhat ⊗ₘ G.actionKernel σ).map e.symm := Measure.pi_compProd _ _
    rw [hpi, Measure.map_map e.measurable e.symm.measurable]
    simp
  -- The outcome is therefore the reindexed density-weighted product of the laws.
  have hgfst : Measurable fun p : (∀ i, G.Theta i) × (∀ i, G.Action i) => g' p.1 :=
    hg'_meas.comp measurable_fst
  have houtcome2 : G.outcome σ
      = ((Measure.pi fun i => (σ i).law).withDensity
          (fun s => g' (fun i => (s i).1))).map e := by
    rw [houtcome, hcompProd_eq, ← map_withDensity_equiv e _ hgfst]
    rfl
  -- The density is a.e. finite against the product of the laws (its type-block marginal is `η̂`).
  have hfin : ∀ᵐ s ∂(Measure.pi fun i => (σ i).law), g' (fun i => (s i).1) < ∞ := by
    have hηfin : ∀ᵐ t ∂ηhat, g' t < ∞ := Measure.rnDeriv_lt_top _ _
    have hmarg : (Measure.pi fun i => (σ i).law).map (fun s i => (s i).1) = ηhat := by
      haveI : ∀ i, SigmaFinite (((σ i).law).map Prod.fst) := fun i => by
        rw [(σ i).marginal_fst]; infer_instance
      rw [Measure.pi_map_pi (f := fun i => (Prod.fst : G.Theta i × G.Action i → G.Theta i))
        (fun i => measurable_fst.aemeasurable)]
      exact congrArg Measure.pi (funext fun i => (σ i).fst_law)
    rw [← hmarg] at hηfin
    exact ae_of_ae_map
      (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst).aemeasurable hηfin
  -- Change variables and convert the density weight into a real factor.
  have hg'comp : Measurable fun s : (∀ i, G.Theta i × G.Action i) => g' (fun i => (s i).1) :=
    hg'_meas.comp (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst)
  rw [houtcome2, integral_map e.measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hg'comp hfin _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  change (g' fun i => (s i).1).toReal • f (e s) =
    f (fun i => (s i).1, fun i => (s i).2) * G.informationDensity fun i => (s i).1
  have he_app : e s = (fun i => (s i).1, fun i => (s i).2) := rfl
  rw [he_app, smul_eq_mul, mul_comm]
  rfl

end MeasBayesianGame

end Econlib.GameTheory
end
