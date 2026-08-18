/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.PureBNE
public import Econlib.Math.MeasureTheory.VonNeumannSelection

/-!
# Interim payoffs and the almost-everywhere characterization of BNE

This file develops the **interim** viewpoint on Bayesian Nash equilibrium for `MeasBayesianGame`
(Harsanyi 1967-68). It defines the conditional expected payoff of a player given its own type by
disintegrating the common prior along that player's coordinate (Mathlib's `condDistrib`), and
proves that ex-ante optimality is implied by — and, under standard Borel action spaces, equivalent
to — almost-everywhere interim best response.

## Main definitions

* `MeasBayesianGame.marginalType`: A player's marginal type distribution.
* `MeasBayesianGame.condProfile`: Conditional law of the type profile given a player's type.
* `MeasBayesianGame.interimPayoff` / `interimPayoffAction`: Interim expected payoff under the
  equilibrium strategy / under a single pure deviation action.

## Main statements

* `MeasBayesianGame.exAntePayoff_eq_integral_interimPayoff`: Law of total expectation.
* `MeasBayesianGame.measurable_interimPayoffAction`: Joint measurability of the deviation interim
  payoff in (type, action).
* `MeasBayesianGame.isBNE_of_ae_interim`: A.e. interim best response ⇒ BNE.
* `MeasBayesianGame.isBNE_of_best_response_on_ae_set`: Best response on a co-null set of types ⇒
  BNE (the first-price auction entry point).
* `MeasBayesianGame.ae_interim_of_isBNE`: BNE ⇒ a.e. interim best response, for standard Borel
  action spaces (von Neumann measurable selection of an improving deviation).
* `MeasBayesianGame.isBNE_iff_ae_interim`: The full a.e. characterization.

## Notes

The conditional law `condProfile i` is defined only up to `marginalType i`-a.e. equivalence (every
`condDistrib` concentration fact is `=ᵐ`, never pointwise). All interim identities here are
therefore a.e. statements, and the characterization quantifies `∀ᵐ θ_i` — the continuum analog of
the finite stack's positive-marginal support guard.

The converse `ae_interim_of_isBNE` (BNE ⇒ a.e. interim best response) carries an interim-level
integrability guard `hdev`: For a.e. type, the deviation integrand of every action is
`condProfile`-integrable. Per-action prior-integrability (the natural ex-ante guard) is strictly
too weak, because its a.e.-exceptional set of types depends on the action; a worked counterexample
(types and actions uniform on `[0,1]`, payoff `1{a_i = θ_i} · (1/θ_j) − ε`) is recorded in
`DesignNotes/MeasBNEInterimIntegrabilityGuard.md`. Bounded payoffs satisfy `hdev` trivially, since
`condProfile` is a Markov kernel.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, continuous types, interim payoff, disintegration, bayesian nash equilibrium
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function

open scoped ENNReal

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- A player's **marginal type distribution**: The pushforward of the common prior along that
player's coordinate. -/
def marginalType (i : G.Player) : MeasureTheory.Measure (G.Theta i) :=
  G.prior.map (fun θ => θ i)

/-- The marginal type distribution is a probability measure. -/
instance (i : G.Player) : IsProbabilityMeasure (G.marginalType i) := by
  unfold marginalType
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

/-- The **conditional law of the type profile** given player `i`'s type, obtained by disintegrating
the common prior along coordinate `i`. For almost every `θ_i`, `condProfile i θ_i` is a probability
measure on type profiles concentrated on profiles whose `i`-th coordinate is `θ_i`. -/
def condProfile (i : G.Player) : ProbabilityTheory.Kernel (G.Theta i) G.TypeProfile :=
  condDistrib id (fun θ => θ i) G.prior

instance (i : G.Player) : IsMarkovKernel (G.condProfile i) := by
  unfold condProfile; infer_instance

/-- **Interim expected payoff** for player `i` of type `θ_i` under strategy profile `s`: The payoff
integrated against the conditional law of the profile given `i`'s type. -/
def interimPayoff (i : G.Player) (θ_i : G.Theta i) (s : G.Strategy) : ℝ :=
  ∫ θ, G.payoff i (G.actionProfile s θ) θ ∂(G.condProfile i θ_i)

/-- **Interim payoff under a pure deviation**: Player `i` of type `θ_i` plays action `a_i` while
all others follow `s`. -/
def interimPayoffAction (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i) (s : G.Strategy) : ℝ :=
  ∫ θ, G.payoff i (Function.update (G.actionProfile s θ) i a_i) θ ∂(G.condProfile i θ_i)

/-- **Fiber concentration.** For almost every type `θ_i`, the conditional law of the profile given
`i`'s type is concentrated on profiles whose `i`-th coordinate is `θ_i`. This is the a.e. — never
pointwise — content of disintegration along coordinate `i`. -/
theorem ae_condProfile_eval (i : G.Player) :
    ∀ᵐ θ_i ∂(G.marginalType i), ∀ᵐ θ ∂(G.condProfile i θ_i), θ i = θ_i := by
  have hX : Measurable (fun θ : G.TypeProfile => θ i) := measurable_pi_apply i
  have hpair : Measurable (fun θ : G.TypeProfile => (θ i, θ)) := hX.prodMk measurable_id
  have hjoint : (G.marginalType i).compProd (G.condProfile i)
      = G.prior.map (fun θ => (θ i, θ)) := by
    unfold marginalType condProfile
    exact compProd_map_condDistrib aemeasurable_id
  -- `MeasurableEq` requires the Polish topology: `upgradeStandardBorel` supplies it.
  have hdiag : MeasurableSet {x : G.Theta i × G.TypeProfile | x.2 i = x.1} := by
    letI := upgradeStandardBorel (G.Theta i)
    exact measurableSet_eq_fun measurable_snd.eval measurable_fst
  have hcompProd : ∀ᵐ x ∂((G.marginalType i).compProd (G.condProfile i)), x.2 i = x.1 := by
    rw [hjoint, ae_map_iff hpair.aemeasurable hdiag]
    exact ae_of_all _ fun θ => rfl
  exact Measure.ae_ae_of_ae_compProd hcompProd

/-- **Law of total expectation**: Ex-ante payoff is the marginal average of interim payoffs. -/
theorem exAntePayoff_eq_integral_interimPayoff (i : G.Player) (s : G.Strategy)
    (hint : Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior) :
    G.exAntePayoff i s = ∫ θ_i, G.interimPayoff i θ_i s ∂(G.marginalType i) := by
  set F : G.Theta i × G.TypeProfile → ℝ := fun p => G.payoff i (G.actionProfile s p.2) p.2 with hF
  have hFmeas : Measurable F :=
    (G.measurable_payoff i).comp
      ((G.measurable_actionProfile s).comp measurable_snd |>.prodMk measurable_snd)
  have hpair : Measurable (fun θ : G.TypeProfile => (θ i, θ)) :=
    (measurable_pi_apply i).prodMk measurable_id
  have hjoint : (G.marginalType i).compProd (G.condProfile i)
      = G.prior.map (fun θ => (θ i, θ)) := by
    unfold marginalType condProfile
    exact compProd_map_condDistrib aemeasurable_id
  have hFint : Integrable F ((G.marginalType i).compProd (G.condProfile i)) := by
    rw [hjoint, integrable_map_measure hFmeas.aestronglyMeasurable hpair.aemeasurable]
    exact hint
  rw [exAntePayoff]
  have hxv : (∫ θ, G.payoff i (G.actionProfile s θ) θ ∂G.prior)
      = ∫ p, F p ∂((G.marginalType i).compProd (G.condProfile i)) := by
    rw [hjoint, integral_map hpair.aemeasurable hFmeas.aestronglyMeasurable]
  rw [hxv, Measure.integral_compProd hFint]
  rfl

/-- The interim integrand of player `i` is integrable in the type, marginally. -/
theorem integrable_interimPayoff (i : G.Player) (s : G.Strategy)
    (hint : Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior) :
    Integrable (fun θ_i => G.interimPayoff i θ_i s) (G.marginalType i) := by
  set F : G.Theta i × G.TypeProfile → ℝ := fun p => G.payoff i (G.actionProfile s p.2) p.2 with hF
  have hFmeas : Measurable F :=
    (G.measurable_payoff i).comp
      ((G.measurable_actionProfile s).comp measurable_snd |>.prodMk measurable_snd)
  have hX : Measurable (fun θ : G.TypeProfile => θ i) := measurable_pi_apply i
  have hpair : Measurable (fun θ : G.TypeProfile => (θ i, θ)) := hX.prodMk measurable_id
  have hFint : Integrable F (G.prior.map (fun θ => (θ i, θ))) := by
    rw [integrable_map_measure hFmeas.aestronglyMeasurable hpair.aemeasurable]
    exact hint
  have hcomp : Integrable
      (fun θ : G.TypeProfile => ∫ y, F (θ i, y) ∂(G.condProfile i (θ i))) G.prior :=
    hFint.integral_condDistrib hX.aemeasurable aemeasurable_id
  rw [marginalType, integrable_map_measure ?_ hX.aemeasurable]
  · exact hcomp
  · have := AEStronglyMeasurable.integral_condDistrib_map
      (Y := id) (X := fun θ : G.TypeProfile => θ i)
      (μ := G.prior) (f := F) aemeasurable_id hFmeas.aestronglyMeasurable
    rw [← marginalType] at this ⊢
    exact this

/-- The interim payoff is measurable in the player's type: The kernel integral of a jointly
measurable integrand against the Markov kernel `condProfile i`. -/
theorem measurable_interimPayoff (i : G.Player) (s : G.Strategy) :
    Measurable fun θ_i => G.interimPayoff i θ_i s := by
  have hF : StronglyMeasurable (fun θ => G.payoff i (G.actionProfile s θ) θ) :=
    (G.measurable_payoff_comp i s).stronglyMeasurable
  exact (StronglyMeasurable.integral_kernel hF (κ := G.condProfile i)).measurable

/-- **Joint measurability of the interim deviation payoff** in (type, action): The integrand is
jointly measurable via `Function.update`, and the kernel `condProfile i` (pulled back along
`Prod.fst`) preserves joint measurability of parametrized integrals. -/
theorem measurable_interimPayoffAction (i : G.Player) (s : G.Strategy) :
    Measurable fun p : G.Theta i × G.Action i => G.interimPayoffAction i p.1 p.2 s := by
  let κ : Kernel (G.Theta i × G.Action i) G.TypeProfile :=
    (G.condProfile i).comap Prod.fst measurable_fst
  have hf : StronglyMeasurable
      (fun q : (G.Theta i × G.Action i) × G.TypeProfile =>
        G.payoff i (Function.update (G.actionProfile s q.2) i q.1.2) q.2) := by
    have hpair : Measurable (fun q : (G.Theta i × G.Action i) × G.TypeProfile =>
        (Function.update (G.actionProfile s q.2) i q.1.2, q.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact measurable_update'.comp
        ((G.measurable_actionProfile s |>.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact (G.measurable_payoff i).stronglyMeasurable.comp_measurable hpair
  have hgoal : (fun p : G.Theta i × G.Action i => G.interimPayoffAction i p.1 p.2 s) =
      fun p => ∫ θ, G.payoff i (Function.update (G.actionProfile s θ) i p.2) θ ∂(κ p) := by
    ext p; simp only [interimPayoffAction, κ, Kernel.comap_apply]
  rw [hgoal]
  exact (StronglyMeasurable.integral_kernel_prod_right' hf).measurable

/-- Joint measurability of the **conditional absolute deviation mass**: The `∫⁻`-norm of the
deviation integrand against `condProfile i`, as a function of (type, action). This is the
truncation handle for the integrability of a selected deviation in `ae_interim_of_isBNE`. -/
theorem measurable_lintegral_enorm_deviation (i : G.Player) (s : G.Strategy) :
    Measurable fun p : G.Theta i × G.Action i =>
      ∫⁻ θ, ‖G.payoff i (Function.update (G.actionProfile s θ) i p.2) θ‖ₑ
        ∂(G.condProfile i p.1) := by
  let κ : Kernel (G.Theta i × G.Action i) G.TypeProfile :=
    (G.condProfile i).comap Prod.fst measurable_fst
  have hgoal : (fun p : G.Theta i × G.Action i =>
        ∫⁻ θ, ‖G.payoff i (Function.update (G.actionProfile s θ) i p.2) θ‖ₑ
          ∂(G.condProfile i p.1)) =
      fun p => ∫⁻ θ,
        ‖G.payoff i (Function.update (G.actionProfile s θ) i p.2) θ‖ₑ ∂(κ p) := by
    ext p; simp only [κ, Kernel.comap_apply]
  rw [hgoal]
  have hf : Measurable (fun q : (G.Theta i × G.Action i) × G.TypeProfile =>
      ‖G.payoff i (Function.update (G.actionProfile s q.2) i q.1.2) q.2‖ₑ) := by
    have hpair : Measurable (fun q : (G.Theta i × G.Action i) × G.TypeProfile =>
        (Function.update (G.actionProfile s q.2) i q.1.2, q.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      exact measurable_update'.comp
        ((G.measurable_actionProfile s |>.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact ((G.measurable_payoff i).comp hpair).enorm
  exact Measurable.lintegral_kernel_prod_right' hf

/-- **Disintegration of a lower integral along player `i`'s coordinate**: The `∫⁻` analog of the
law of total expectation. No integrability side conditions — this is what makes it the right tool
to *establish* prior-integrability of a deviation from conditional bounds. -/
theorem lintegral_marginalType_condProfile (i : G.Player) {F : G.TypeProfile → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ θ_i, ∫⁻ θ, F θ ∂(G.condProfile i θ_i) ∂(G.marginalType i) = ∫⁻ θ, F θ ∂G.prior := by
  have hpair : Measurable (fun θ : G.TypeProfile => (θ i, θ)) :=
    (measurable_pi_apply i).prodMk measurable_id
  have hjoint : (G.marginalType i).compProd (G.condProfile i)
      = G.prior.map (fun θ => (θ i, θ)) := by
    unfold marginalType condProfile
    exact compProd_map_condDistrib aemeasurable_id
  have hstep : ∫⁻ θ_i, ∫⁻ θ, F θ ∂(G.condProfile i θ_i) ∂(G.marginalType i)
      = ∫⁻ p : G.Theta i × G.TypeProfile, F p.2
          ∂((G.marginalType i).compProd (G.condProfile i)) :=
    (Measure.lintegral_compProd (hF.comp measurable_snd)).symm
  rw [hstep, hjoint]
  exact MeasureTheory.lintegral_map (hF.comp measurable_snd) hpair

/-- **Deviation interim equals the action form, a.e.** If `s'` agrees with `s` off player `i`, then
for almost every type `θ_i`, the interim payoff of `s'` equals the interim payoff of `s` with `i`'s
action overwritten by `s'`'s action at `θ_i`. The fiber concentration makes the two integrands
agree a.e. The no-deviation case `s' = s` is the self-identity. -/
theorem interimPayoff_ae_eq_interimPayoffAction (i : G.Player) (s s' : G.Strategy)
    (hagree : ∀ j, j ≠ i → s' j = s j) :
    ∀ᵐ θ_i ∂(G.marginalType i),
      G.interimPayoff i θ_i s' = G.interimPayoffAction i θ_i ((s' i).1 θ_i) s := by
  filter_upwards [G.ae_condProfile_eval i] with θ_i hfiber
  unfold interimPayoff interimPayoffAction
  refine integral_congr_ae ?_
  filter_upwards [hfiber] with θ hθ
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    change (s' j).1 (θ j) = (s' j).1 θ_i
    rw [hθ]
  · rw [Function.update_of_ne hj]
    change (s' j).1 (θ j) = (s j).1 (θ j)
    rw [hagree j hj]

/-- **Sufficiency (`⇐`).** If, for every player, almost every type plays an interim best response
(no single action beats the equilibrium action in interim expectation), then the profile is a
Bayesian Nash equilibrium. This is unconditional and is the direction the first-price auction
uses. -/
theorem isBNE_of_ae_interim (s : G.Strategy)
    (hint : ∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior)
    (hbr : ∀ i, ∀ᵐ θ_i ∂(G.marginalType i), ∀ a_i : G.Action i,
      G.interimPayoff i θ_i s ≥ G.interimPayoffAction i θ_i a_i s) :
    G.IsBNE s := by
  rw [isBNE_iff]
  -- The incumbent-integrability conjunct of `IsBNE` is exactly `hint`.
  refine ⟨fun i s' hagree hs'int => ?_, hint⟩
  rw [ge_iff_le,
    G.exAntePayoff_eq_integral_interimPayoff i s' hs'int,
    G.exAntePayoff_eq_integral_interimPayoff i s (hint i)]
  refine integral_mono_ae (G.integrable_interimPayoff i s' hs'int)
    (G.integrable_interimPayoff i s (hint i)) ?_
  filter_upwards [G.interimPayoff_ae_eq_interimPayoffAction i s s' hagree, hbr i]
    with θ_i hθ_eq hθ_br
  rw [hθ_eq]
  exact hθ_br ((s' i).1 θ_i)

/-- **Support bridge (auction entry point).** If for each player there is a co-null set of types on
which the equilibrium strategy is an interim best response against every action, then the profile
is a Bayesian Nash equilibrium. The first-price auction supplies best response on all of
`[θlo, θhi]`, whose complement is prior-null. -/
theorem isBNE_of_best_response_on_ae_set (s : G.Strategy)
    (hint : ∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior)
    (T : ∀ i, Set (G.Theta i)) (hT : ∀ i, G.marginalType i (T i)ᶜ = 0)
    (hbr : ∀ i, ∀ θ_i ∈ T i, ∀ a_i : G.Action i,
      G.interimPayoff i θ_i s ≥ G.interimPayoffAction i θ_i a_i s) :
    G.IsBNE s := by
  refine G.isBNE_of_ae_interim s hint fun i => ?_
  have hae : ∀ᵐ θ_i ∂(G.marginalType i), θ_i ∈ T i := mem_ae_iff.mpr (hT i)
  filter_upwards [hae] with θ_i hθ_i
  exact hbr i θ_i hθ_i

/-- **Necessity (`⇒`).** Every Bayesian Nash equilibrium with standard Borel action spaces plays an
interim best response at almost every type, against all actions simultaneously.

The guard `hdev` is interim-level: Its quantifier order
`∀ᵐ θ_i, ∀ a_i, Integrable … (condProfile i θ_i)` — one conull set of types protecting all actions
at once — is strictly stronger than per-action prior-integrability, which is insufficient (see the
module docstring and `DesignNotes/MeasBNEInterimIntegrabilityGuard.md`). -/
theorem ae_interim_of_isBNE [∀ i, StandardBorelSpace (G.Action i)] (s : G.Strategy)
    (hbne : G.IsBNE s)
    (hdev : ∀ i, ∀ᵐ θ_i ∂(G.marginalType i), ∀ a_i : G.Action i,
      Integrable (fun θ => G.payoff i (Function.update (G.actionProfile s θ) i a_i) θ)
        (G.condProfile i θ_i)) :
    ∀ i, ∀ᵐ θ_i ∂(G.marginalType i), ∀ a_i : G.Action i,
      G.interimPayoff i θ_i s ≥ G.interimPayoffAction i θ_i a_i s := by
  -- Incumbent integrability is bundled into `IsBNE`; project it out.
  have hint : ∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior :=
    ((G.isBNE_iff s).mp hbne).2
  intro i
  haveI hAne : Nonempty (G.Action i) := ⟨(s i).1 (Classical.arbitrary (G.Theta i))⟩
  by_contra hviol
  rw [ae_iff] at hviol
  have hpos : 0 < G.marginalType i
      {θ_i | ∃ a_i, G.interimPayoff i θ_i s < G.interimPayoffAction i θ_i a_i s} := by
    have hVeq : {θ_i | ¬ ∀ a_i : G.Action i,
        G.interimPayoff i θ_i s ≥ G.interimPayoffAction i θ_i a_i s} =
        {θ_i | ∃ a_i, G.interimPayoff i θ_i s < G.interimPayoffAction i θ_i a_i s} := by
      ext θ_i; simp [not_forall, not_le]
    rw [hVeq] at hviol
    exact pos_iff_ne_zero.mpr hviol
  -- Von Neumann selection: assemble the type-dependent improving actions into a single measurable
  -- choice `d₀` improving on a set `T` of positive measure.
  obtain ⟨d₀, hd₀_meas, hT_pos⟩ :=
    MeasureTheory.exists_measurable_improving_selection
      (f := fun θ_i a_i => G.interimPayoffAction i θ_i a_i s)
      (G.measurable_interimPayoffAction i s)
      (G.measurable_interimPayoff i s) (G.marginalType i) hpos
  set T : Set (G.Theta i) :=
    {θ_i | G.interimPayoff i θ_i s < G.interimPayoffAction i θ_i (d₀ θ_i) s} with hTdef
  have hT_meas : MeasurableSet T :=
    measurableSet_lt (G.measurable_interimPayoff i s)
      ((G.measurable_interimPayoffAction i s).comp (measurable_id.prodMk hd₀_meas))
  set hMass : G.Theta i → ℝ≥0∞ := fun θ_i =>
    ∫⁻ θ, ‖G.payoff i (Function.update (G.actionProfile s θ) i (d₀ θ_i)) θ‖ₑ
      ∂(G.condProfile i θ_i) with hMassdef
  have hMass_meas : Measurable hMass :=
    (G.measurable_lintegral_enorm_deviation i s).comp (measurable_id.prodMk hd₀_meas)
  have hMass_fin_ae : ∀ᵐ θ_i ∂(G.marginalType i), hMass θ_i < ∞ := by
    filter_upwards [hdev i] with θ_i hθ
    exact hasFiniteIntegral_iff_enorm.mp (hθ (d₀ θ_i)).2
  -- Truncate by mass level: some `M` retains positive measure on the improvement set, since
  -- a.e. finiteness of `hMass` implies `T` is covered by the truncated pieces.
  have hSM_ex : ∃ M : ℕ, 0 < G.marginalType i (T ∩ {θ_i | hMass θ_i ≤ M}) := by
    by_contra hall
    push Not at hall
    have hnull : ∀ M : ℕ, G.marginalType i (T ∩ {θ_i | hMass θ_i ≤ M}) = 0 :=
      fun M => le_antisymm (hall M) (zero_le)
    have hcover : T ≤ᵐ[G.marginalType i] ⋃ M : ℕ, T ∩ {θ_i | hMass θ_i ≤ M} := by
      filter_upwards [hMass_fin_ae] with θ_i hfin hT
      obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hfin.ne
      exact Set.mem_iUnion.mpr ⟨M, hT, hM.le⟩
    have hTnull : G.marginalType i T = 0 :=
      le_antisymm ((measure_mono_ae hcover).trans (measure_iUnion_null hnull).le) (zero_le)
    exact absurd hTnull hT_pos.ne'
  obtain ⟨M, hSM_pos⟩ := hSM_ex
  set SM : Set (G.Theta i) := T ∩ {θ_i | hMass θ_i ≤ M} with hSMdef
  have hSM_meas : MeasurableSet SM := hT_meas.inter (hMass_meas measurableSet_Iic)
  classical
  set d : G.Theta i → G.Action i := SM.piecewise d₀ ((s i).1) with hddef
  have hd_meas : Measurable d := Measurable.piecewise hSM_meas hd₀_meas (s i).2
  set s' : G.Strategy := G.replace s i ⟨d, hd_meas⟩ with hs'def
  have hs'i : s' i = ⟨d, hd_meas⟩ := G.replace_self s i _
  have hagree : ∀ j, j ≠ i → s' j = s j := fun j hj => G.replace_of_ne s i _ hj
  -- Conditional mass bound: on `SM` the deviation plays `d₀` with mass ≤ M; off `SM` it plays
  -- the equilibrium action and the update is inert on the fiber.
  have hbound : ∀ᵐ θ_i ∂(G.marginalType i),
      (∫⁻ θ, ‖G.payoff i (G.actionProfile s' θ) θ‖ₑ ∂(G.condProfile i θ_i)) ≤
        M + ∫⁻ θ, ‖G.payoff i (G.actionProfile s θ) θ‖ₑ ∂(G.condProfile i θ_i) := by
    filter_upwards [G.ae_condProfile_eval i] with θ_i hfiber
    have henorm_eq : ∫⁻ θ, ‖G.payoff i (G.actionProfile s' θ) θ‖ₑ ∂(G.condProfile i θ_i) =
        ∫⁻ θ, ‖G.payoff i (Function.update (G.actionProfile s θ) i (d θ_i)) θ‖ₑ
          ∂(G.condProfile i θ_i) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfiber] with θ hθ
      have hprofile : G.actionProfile s' θ = Function.update (G.actionProfile s θ) i (d θ_i) := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, G.actionProfile_apply, hs'i]
          exact congrArg d hθ
        · rw [Function.update_of_ne hj, G.actionProfile_apply, G.actionProfile_apply,
            hagree j hj]
      rw [hprofile]
    rw [henorm_eq]
    by_cases hmem : θ_i ∈ SM
    · have hdv : d θ_i = d₀ θ_i := Set.piecewise_eq_of_mem _ _ _ hmem
      rw [hdv]; exact le_add_right hmem.2
    · have hdv : d θ_i = (s i).1 θ_i := Set.piecewise_eq_of_notMem _ _ _ hmem
      rw [hdv]
      have hinert : ∫⁻ θ, ‖G.payoff i (Function.update (G.actionProfile s θ) i ((s i).1 θ_i)) θ‖ₑ
          ∂(G.condProfile i θ_i) =
          ∫⁻ θ, ‖G.payoff i (G.actionProfile s θ) θ‖ₑ ∂(G.condProfile i θ_i) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfiber] with θ hθ
        have hupdate : Function.update (G.actionProfile s θ) i ((s i).1 θ_i) =
            G.actionProfile s θ := by
          rw [← hθ, ← G.actionProfile_apply s θ i]
          exact Function.update_eq_self i (G.actionProfile s θ)
        rw [hupdate]
      rw [hinert]
      exact le_add_self
  have hs'_int : Integrable (fun θ => G.payoff i (G.actionProfile s' θ) θ) G.prior := by
    refine ⟨(G.measurable_payoff_comp i s').aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      ← G.lintegral_marginalType_condProfile i (G.measurable_payoff_comp i s').enorm]
    have hequil_fin :
        ∫⁻ θ_i, ∫⁻ θ, ‖G.payoff i (G.actionProfile s θ) θ‖ₑ ∂(G.condProfile i θ_i)
          ∂(G.marginalType i) < ∞ := by
      rw [G.lintegral_marginalType_condProfile i (G.measurable_payoff_comp i s).enorm]
      exact hasFiniteIntegral_iff_enorm.mp (hint i).2
    calc ∫⁻ θ_i, ∫⁻ θ, ‖G.payoff i (G.actionProfile s' θ) θ‖ₑ ∂(G.condProfile i θ_i)
          ∂(G.marginalType i)
        ≤ ∫⁻ θ_i, (M + ∫⁻ θ, ‖G.payoff i (G.actionProfile s θ) θ‖ₑ ∂(G.condProfile i θ_i))
          ∂(G.marginalType i) := lintegral_mono_ae hbound
      _ = M + ∫⁻ θ_i, ∫⁻ θ, ‖G.payoff i (G.actionProfile s θ) θ‖ₑ ∂(G.condProfile i θ_i)
          ∂(G.marginalType i) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top M, hequil_fin⟩
  have hae_s' : ∀ᵐ θ_i ∂(G.marginalType i),
      G.interimPayoff i θ_i s' = G.interimPayoffAction i θ_i (d θ_i) s := by
    filter_upwards [G.interimPayoff_ae_eq_interimPayoffAction i s s' hagree] with θ_i hθ
    rw [hθ, hs'i]
  have hae_s : ∀ᵐ θ_i ∂(G.marginalType i),
      G.interimPayoff i θ_i s = G.interimPayoffAction i θ_i ((s i).1 θ_i) s :=
    G.interimPayoff_ae_eq_interimPayoffAction i s s (fun _ _ => rfl)
  have hge_ae : ∀ᵐ θ_i ∂(G.marginalType i),
      G.interimPayoff i θ_i s ≤ G.interimPayoff i θ_i s' := by
    filter_upwards [hae_s', hae_s] with θ_i h1 h2
    rw [h1]
    by_cases hmem : θ_i ∈ SM
    · have hdv : d θ_i = d₀ θ_i := Set.piecewise_eq_of_mem _ _ _ hmem
      rw [hdv]
      exact le_of_lt hmem.1
    · have hdv : d θ_i = (s i).1 θ_i := Set.piecewise_eq_of_notMem _ _ _ hmem
      rw [hdv, ← h2]
  have hstrict_ae : ∀ᵐ θ_i ∂(G.marginalType i), θ_i ∈ SM →
      G.interimPayoff i θ_i s < G.interimPayoff i θ_i s' := by
    filter_upwards [hae_s'] with θ_i h1 hmem
    have hdv : d θ_i = d₀ θ_i := Set.piecewise_eq_of_mem _ _ _ hmem
    rw [h1, hdv]
    exact hmem.1
  have hint_s' : Integrable (fun θ_i => G.interimPayoff i θ_i s') (G.marginalType i) :=
    G.integrable_interimPayoff i s' hs'_int
  have hint_s : Integrable (fun θ_i => G.interimPayoff i θ_i s) (G.marginalType i) :=
    G.integrable_interimPayoff i s (hint i)
  have hdiff_nonneg : 0 ≤ᵐ[G.marginalType i]
      fun θ_i => G.interimPayoff i θ_i s' - G.interimPayoff i θ_i s := by
    filter_upwards [hge_ae] with θ_i hθ
    exact sub_nonneg.mpr hθ
  have hsupp_pos : 0 < G.marginalType i
      (Function.support fun θ_i => G.interimPayoff i θ_i s' - G.interimPayoff i θ_i s) := by
    refine hSM_pos.trans_le (measure_mono_ae ?_)
    filter_upwards [hstrict_ae] with θ_i hθ hmem
    exact (sub_pos.mpr (hθ hmem)).ne'
  have hint_pos : 0 < ∫ θ_i, (G.interimPayoff i θ_i s' - G.interimPayoff i θ_i s)
      ∂(G.marginalType i) :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg (hint_s'.sub hint_s)).mpr hsupp_pos
  rw [integral_sub hint_s' hint_s, sub_pos] at hint_pos
  have hexa : G.exAntePayoff i s < G.exAntePayoff i s' := by
    rw [G.exAntePayoff_eq_integral_interimPayoff i s (hint i),
      G.exAntePayoff_eq_integral_interimPayoff i s' hs'_int]
    exact hint_pos
  exact absurd (((G.isBNE_iff s).mp hbne).1 i s' hagree hs'_int) (not_le.mpr hexa)

/-- **The canonical characterization.** A strategy profile of a game with standard Borel action
spaces is a Bayesian Nash equilibrium iff, for every player, almost every type plays an interim
best response. The interim-level integrability guard `hdev` keeps the unguarded `∀ a_i` form sound
(no junk-zero interim payoff from a non-integrable action at a.e. type); bounded payoffs satisfy it
trivially. `⇐` is `isBNE_of_ae_interim` (which needs neither the guard nor the standard Borel
structure); `⇒` is `ae_interim_of_isBNE` via von Neumann measurable selection. -/
theorem isBNE_iff_ae_interim [∀ i, StandardBorelSpace (G.Action i)] (s : G.Strategy)
    (hint : ∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior)
    (hdev : ∀ i, ∀ᵐ θ_i ∂(G.marginalType i), ∀ a_i : G.Action i,
      Integrable (fun θ => G.payoff i (Function.update (G.actionProfile s θ) i a_i) θ)
        (G.condProfile i θ_i)) :
    G.IsBNE s ↔
      ∀ i, ∀ᵐ θ_i ∂(G.marginalType i), ∀ a_i : G.Action i,
        G.interimPayoff i θ_i s ≥ G.interimPayoffAction i θ_i a_i s :=
  ⟨fun hbne => G.ae_interim_of_isBNE s hbne hdev, fun hbr => G.isBNE_of_ae_interim s hint hbr⟩

end MeasBayesianGame

end Econlib.GameTheory
end
