/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Interim
public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.FirstPriceGame

/-!
# The symmetric first-price auction as a `MeasBayesianGame`

This file wires the first-price auction's equilibrium (`AuctionEnv.firstPriceBid_isEquilibriumBid`,
a best-response statement against every bid) into the canonical continuous-type **Bayes–Nash
equilibrium** predicate `GameTheory.MeasBayesianGame.IsBNE` (Vickrey 1961; Riley and Samuelson
1981).

The symmetric IID **first-price auction** is presented as a `MeasBayesianGame`: Players `Fin n`,
type and action (bid) spaces `ℝ`, common prior the IID product `jointLaw`, and the pay-your-bid
ex-post payoff `(θ i − b i) · x b i`. The symmetric schedule `firstPriceBid` is a `Strategy`, and
`firstPriceBid_isBNE` shows it is an `IsBNE`.

## Main definitions

* `AuctionEnv.firstPriceMeasGame` — the symmetric IID auction as a `MeasBayesianGame`.
* `AuctionEnv.firstPriceStrategy` — the symmetric equilibrium bid schedule as a `Strategy`.

## Main statements

* `AuctionEnv.exAnte_eq_integral_devPayoff` — ex-ante payoff of a rivals-at-`σ` deviation as a
  single integral of `firstPriceDevPayoff` against `base.dist`.
* `AuctionEnv.firstPriceBid_isBNE` — the symmetric schedule is a Bayes–Nash equilibrium in the
  canonical `MeasBayesianGame.IsBNE` sense.

## Notes

Because the prior is a product (bidders are independent), the ex-ante payoff of any deviation that
keeps rivals at `σ` marginalizes to `∫ firstPriceDevPayoff i t (deviation t) ∂base.dist`. The
per-type best-response lemma then dominates the deviation on the support `[θlo, θhi]`, where
`base.dist` is supported, so the ex-ante inequality follows by monotonicity of the integral.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).
* Riley, John G., and William F. Samuelson. 1981. “Optimal Auctions.” *The American Economic
  Review* 71 (3): 381–92.

## Tags

auction, first-price, bayes-nash equilibrium, continuous types
-/

@[expose] public section

open Set MeasureTheory Function Econlib.GameTheory Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionEnv

variable (A : AuctionEnv)

/-- The symmetric IID first-price auction as a measure-theoretic Bayesian game: Players `Fin n`,
type and bid spaces `ℝ`, common prior the IID product `jointLaw`, and the pay-your-bid ex-post
payoff `(θ i − b i) · x b i` (value minus own bid, times the winning indicator). -/
def firstPriceMeasGame : MeasBayesianGame where
  Player := Fin A.n
  Theta := fun _ => ℝ
  Action := fun _ => ℝ
  prior := A.jointLaw
  payoff := fun i b θ => (θ i - b i) * A.highestValueAlloc.x b i
  measurable_payoff := fun i => by
    have h1 : Measurable (fun p : (Fin A.n → ℝ) × (Fin A.n → ℝ) => p.2 i - p.1 i) :=
      ((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp measurable_fst)
    have h2 : Measurable (fun p : (Fin A.n → ℝ) × (Fin A.n → ℝ) => A.highestValueAlloc.x p.1 i) :=
      (A.highestValueAlloc.measurable i).comp measurable_fst
    exact h1.mul h2

@[simp] lemma firstPriceMeasGame_payoff (i : Fin A.n) (b θ : Fin A.n → ℝ) :
    A.firstPriceMeasGame.payoff i b θ = (θ i - b i) * A.highestValueAlloc.x b i := rfl

/-- The symmetric equilibrium bid schedule `σ = firstPriceBid`, packaged as a measurable strategy
profile of the auction game. -/
def firstPriceStrategy : A.firstPriceMeasGame.Strategy :=
  fun _ => ⟨fun t => A.base.firstPriceBid A.n t, A.base.firstPriceBid_measurable A.n⟩

/-- The ex-ante deviation integrand for a measurable bid schedule `b`: The value-bid spread times
the winning indicator, with coordinate `i` of the equilibrium bid profile overwritten by `b (θ i)`.
This is the integrand of `exAntePayoff` once a rivals-at-`σ` deviation has been reduced. -/
def firstPriceDevIntegrand (i : Fin A.n) (b : ℝ → ℝ) (θ : A.Profile) : ℝ :=
  (θ i - b (θ i)) * A.highestValueAlloc.x (update (A.firstPriceBidProfile θ) i (b (θ i))) i

/-- The ex-ante deviation integrand is measurable when the bid schedule `b` is. -/
lemma measurable_firstPriceDevIntegrand (i : Fin A.n) {b : ℝ → ℝ} (hb : Measurable b) :
    Measurable (A.firstPriceDevIntegrand i b) := by
  have hbi : Measurable (fun θ : A.Profile => b (θ i)) := hb.comp (measurable_pi_apply i)
  have hH : Measurable (fun θ : A.Profile => θ i - b (θ i)) :=
    (measurable_pi_apply i).sub hbi
  have hprofile : Measurable (fun θ : A.Profile => A.firstPriceBidProfile θ) :=
    measurable_pi_lambda _ fun j =>
      (A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply j)
  -- `θ ↦ update (bidProfile θ) i (b (θ i))` is measurable: both arguments of `update` are.
  have hupd : Measurable (fun θ : A.Profile =>
      update (A.firstPriceBidProfile θ) i (b (θ i))) := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      exact hbi
    · simp only [Function.update_of_ne hj]
      exact (measurable_pi_apply j).comp hprofile
  exact hH.mul ((A.highestValueAlloc.measurable i).comp hupd)

/-- **Inner integral factorization.** Freezing coordinate `i` at `t` and integrating the rivals
out, the ex-ante deviation integrand integrates to the value-bid spread `(t − b t)` times the
interim winning probability of bid `b t` — the interim deviation payoff
`firstPriceDevPayoff i t (b t)`. -/
lemma integral_firstPriceDevIntegrand_update (i : Fin A.n) (b : ℝ → ℝ) (t : ℝ) :
    ∫ θ', A.firstPriceDevIntegrand i b (update θ' i t) ∂A.jointLaw
      = A.firstPriceDevPayoff i t (b t) := by
  -- The bid profile of `update θ' i t` off `i` is that of `θ'`; coordinate `i` is overwritten.
  have hprof : ∀ θ' : A.Profile,
      update (A.firstPriceBidProfile (update θ' i t)) i (b t)
        = update (A.firstPriceBidProfile θ') i (b t) := by
    intro θ'
    funext j
    by_cases hj : j = i
    · subst hj; rw [update_self, update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, firstPriceBidProfile_apply,
        firstPriceBidProfile_apply, Function.update_of_ne hj]
  -- The frozen integrand is `(t − b t)` times the win-prob integrand, independent of `θ' i`.
  have hpoint : ∀ θ' : A.Profile, A.firstPriceDevIntegrand i b (update θ' i t)
      = (t - b t) * A.highestValueAlloc.x (update (A.firstPriceBidProfile θ') i (b t)) i := by
    intro θ'
    simp only [firstPriceDevIntegrand, update_self, hprof θ']
  simp only [hpoint]
  rw [integral_const_mul, ← firstPriceWinProb, firstPriceDevPayoff_def]

/-- The interim winning probability is measurable in the submitted bid: It is a parametric integral
of a jointly measurable integrand over the (sigma-finite) joint law. -/
lemma measurable_firstPriceWinProb (i : Fin A.n) : Measurable (A.firstPriceWinProb i) := by
  -- The integrand `(b, θ) ↦ x (update (σ∘θ) i b) i` is jointly measurable.
  have hprofile : Measurable (fun θ : A.Profile => A.firstPriceBidProfile θ) :=
    measurable_pi_lambda _ fun j =>
      (A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply j)
  have hjoint : Measurable (fun p : ℝ × A.Profile =>
      A.highestValueAlloc.x (update (A.firstPriceBidProfile p.2) i p.1) i) := by
    refine (A.highestValueAlloc.measurable i).comp ?_
    refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j = i
    · subst hj; simp only [update_self]; exact measurable_fst
    · simp only [Function.update_of_ne hj]
      exact (measurable_pi_apply j).comp (hprofile.comp measurable_snd)
  exact (hjoint.stronglyMeasurable.integral_prod_right (ν := A.jointLaw)).measurable

/-- **Mass equality across the coordinate split.** The total `‖·‖ₑ`-mass of the ex-ante deviation
integrand against the joint law equals the total mass of the interim deviation payoff against
`base.dist`: The rivals integrate out of the nonnegative winning indicator into the winning
probability. -/
lemma lintegral_enorm_firstPriceDevIntegrand (i : Fin A.n) {b : ℝ → ℝ} (hb : Measurable b) :
    ∫⁻ θ, ‖A.firstPriceDevIntegrand i b θ‖ₑ ∂A.jointLaw
      = ∫⁻ t, ‖A.firstPriceDevPayoff i t (b t)‖ₑ ∂A.base.dist.toMeasure := by
  -- The enorm of the integrand is measurable.
  have hmeas : Measurable (fun θ => ‖A.firstPriceDevIntegrand i b θ‖ₑ) :=
    (A.measurable_firstPriceDevIntegrand i hb).enorm
  -- Inner mass: freezing coordinate `i` at `t`, the enorm factors and the rivals integrate out.
  have hinner : ∀ t : ℝ, ∫⁻ θ', ‖A.firstPriceDevIntegrand i b (update θ' i t)‖ₑ ∂A.jointLaw
      = ‖A.firstPriceDevPayoff i t (b t)‖ₑ := by
    intro t
    -- The frozen integrand factors into the spread `(t − b t)` times the win indicator.
    have hpoint : ∀ θ' : A.Profile, ‖A.firstPriceDevIntegrand i b (update θ' i t)‖ₑ
        = ‖(t - b t)‖ₑ * ENNReal.ofReal
            (A.highestValueAlloc.x (update (A.firstPriceBidProfile θ') i (b t)) i) := by
      intro θ'
      have hprof : update (A.firstPriceBidProfile (update θ' i t)) i (b t)
          = update (A.firstPriceBidProfile θ') i (b t) := by
        funext j
        by_cases hj : j = i
        · subst hj; rw [update_self, update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, firstPriceBidProfile_apply,
            firstPriceBidProfile_apply, Function.update_of_ne hj]
      rw [firstPriceDevIntegrand, update_self, hprof, enorm_mul,
        Real.enorm_eq_ofReal (A.highestValueAlloc.nonneg _ i)]
    simp only [hpoint]
    rw [lintegral_const_mul _ (A.measurable_firstPriceWinProb_integrand i (b t)).ennreal_ofReal]
    -- The remaining lower integral of the nonnegative win indicator is the winning probability.
    rw [← ofReal_integral_eq_lintegral_ofReal
      (A.integrable_firstPriceWinProb_integrand i (b t))
      (ae_of_all _ fun θ' => A.highestValueAlloc.nonneg _ i),
      ← firstPriceWinProb, firstPriceDevPayoff_def, enorm_mul,
      Real.enorm_eq_ofReal (A.firstPriceWinProb_nonneg i (b t))]
  -- Apply the Tonelli reduction and rewrite the inner masses.
  rw [jointLaw_def, ContDist.lintegral_piMeasure_reduce i hmeas]
  refine lintegral_congr fun t => ?_
  rw [← jointLaw_def]
  exact hinner t

/-- The marginalized interim deviation payoff `t ↦ (t − b t) · W(b t)` is measurable when the bid
schedule `b` is: The value-bid spread is measurable and the winning probability is measurable in
the submitted bid. -/
lemma measurable_firstPriceDevPayoff_comp (i : Fin A.n) {b : ℝ → ℝ} (hb : Measurable b) :
    Measurable (fun t => A.firstPriceDevPayoff i t (b t)) := by
  simp only [firstPriceDevPayoff_def]
  exact (measurable_id.sub hb).mul ((A.measurable_firstPriceWinProb i).comp hb)

/-- **Integrability transfers across the coordinate split.** The ex-ante deviation integrand is
integrable against the joint law iff the marginalized interim deviation payoff is integrable
against `base.dist`. -/
lemma integrable_firstPriceDevIntegrand_iff (i : Fin A.n) {b : ℝ → ℝ} (hb : Measurable b) :
    Integrable (A.firstPriceDevIntegrand i b) A.jointLaw
      ↔ Integrable (fun t => A.firstPriceDevPayoff i t (b t)) A.base.dist.toMeasure := by
  rw [Integrable, Integrable,
    hasFiniteIntegral_iff_enorm, hasFiniteIntegral_iff_enorm,
    A.lintegral_enorm_firstPriceDevIntegrand i hb]
  constructor
  · exact fun h => ⟨(A.measurable_firstPriceDevPayoff_comp i hb).aestronglyMeasurable, h.2⟩
  · exact fun h => ⟨(A.measurable_firstPriceDevIntegrand i hb).aestronglyMeasurable, h.2⟩

/-- **Ex-ante payoff of a rivals-at-`σ` deviation, marginalized.** When player `i` deviates to the
measurable schedule `s' i` and all rivals keep bidding `σ`, the ex-ante payoff equals the average
over `i`'s own type of the interim deviation payoff `firstPriceDevPayoff`, a single integral
against `base.dist`. -/
theorem exAnte_eq_integral_devPayoff (i : Fin A.n) (s' : A.firstPriceMeasGame.Strategy)
    (hagree : ∀ j, j ≠ i → s' j = A.firstPriceStrategy j) :
    A.firstPriceMeasGame.exAntePayoff i s'
      = ∫ t, A.firstPriceDevPayoff i t ((s' i).1 t) ∂A.base.dist.toMeasure := by
  -- The action profile of a rivals-at-`σ` deviation overwrites coordinate `i` of `σ ∘ θ`.
  have hact : ∀ θ : A.Profile, A.firstPriceMeasGame.actionProfile s' θ
      = update (A.firstPriceBidProfile θ) i ((s' i).1 (θ i)) := by
    intro θ
    funext j
    by_cases hj : j = i
    · subst hj; rw [MeasBayesianGame.actionProfile_apply, update_self]
    · rw [MeasBayesianGame.actionProfile_apply]
      rw [show update (A.firstPriceBidProfile θ) i ((s' i).1 (θ i)) j
            = A.firstPriceBidProfile θ j from Function.update_of_ne hj _ _]
      rw [firstPriceBidProfile_apply,
        show (s' j).1 = (A.firstPriceStrategy j).1 from congrArg Subtype.val (hagree j hj),
        firstPriceStrategy]
  -- The ex-ante integrand is the ex-ante deviation integrand for the bid schedule `(s' i).1`.
  have hexpand : A.firstPriceMeasGame.exAntePayoff i s'
      = ∫ θ, A.firstPriceDevIntegrand i ((s' i).1) θ ∂A.jointLaw := by
    rw [MeasBayesianGame.exAntePayoff]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [firstPriceMeasGame_payoff, hact θ, update_self, firstPriceDevIntegrand]
  rw [hexpand]
  -- Integrability is equivalent on both sides; split on it and use Fubini or the junk-zero values.
  by_cases hint : Integrable (fun t => A.firstPriceDevPayoff i t ((s' i).1 t)) A.base.dist.toMeasure
  · -- Integrable: the rivals integrate out via the Bochner reduction.
    have hintθ : Integrable (A.firstPriceDevIntegrand i ((s' i).1)) A.jointLaw :=
      (A.integrable_firstPriceDevIntegrand_iff i (s' i).2).mpr hint
    rw [jointLaw_def, ContDist.integral_piMeasure_reduce i hintθ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [← jointLaw_def, A.integral_firstPriceDevIntegrand_update i ((s' i).1) t]
  · -- Not integrable: both Bochner integrals are the junk-zero value.
    rw [integral_undef ((A.integrable_firstPriceDevIntegrand_iff i (s' i).2).not.mpr hint),
      integral_undef hint]

/-- The ex-ante integrand of the symmetric equilibrium strategy is integrable against the joint
law: On the support the value-bid spread lies in a fixed window and the winning indicator is in
`[0, 1]`. -/
theorem integrable_exAnte_firstPriceStrategy (i : Fin A.n) :
    Integrable (fun θ => A.firstPriceMeasGame.payoff i
      (A.firstPriceMeasGame.actionProfile A.firstPriceStrategy θ) θ) A.jointLaw := by
  -- Under the symmetric schedule the action profile is the equilibrium bid profile `σ ∘ θ`.
  have hact : ∀ θ : A.Profile,
      A.firstPriceMeasGame.actionProfile A.firstPriceStrategy θ = A.firstPriceBidProfile θ := by
    intro θ; funext j; rfl
  -- The integrand is `(θ i − σ(θ i)) · x (σ ∘ θ) i`.
  have hf : (fun θ => A.firstPriceMeasGame.payoff i
        (A.firstPriceMeasGame.actionProfile A.firstPriceStrategy θ) θ)
      = fun θ => (θ i - A.base.firstPriceBid A.n (θ i))
          * A.highestValueAlloc.x (A.firstPriceBidProfile θ) i := by
    funext θ; rw [firstPriceMeasGame_payoff, hact θ, firstPriceBidProfile_apply]
  rw [hf]
  -- Measurability: a measurable spread times the measurable winner indicator.
  have hbid : Measurable (fun θ : A.Profile => θ i - A.base.firstPriceBid A.n (θ i)) :=
    (measurable_pi_apply i).sub
      ((A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply i))
  have hprofile : Measurable (fun θ : A.Profile => A.firstPriceBidProfile θ) :=
    measurable_pi_lambda _ fun j =>
      (A.base.firstPriceBid_measurable A.n).comp (measurable_pi_apply j)
  have hmeas : Measurable (fun θ : A.Profile => (θ i - A.base.firstPriceBid A.n (θ i))
      * A.highestValueAlloc.x (A.firstPriceBidProfile θ) i) :=
    hbid.mul ((A.highestValueAlloc.measurable i).comp hprofile)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  -- The spread `t ↦ t − σ(t)` is continuous, hence bounded by some `C` on the compact type box.
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := A.base.θlo) (b := A.base.θhi)).exists_bound_of_continuousOn
    (f := fun t => t - A.base.firstPriceBid A.n t)
    (continuousOn_id.sub (A.base.firstPriceBid_continuousOn A.n))
  -- A.e. the type lies in the box; there the spread is bounded and the indicator is in `[0, 1]`.
  haveI : IsProbabilityMeasure A.jointLaw := inferInstance
  refine HasFiniteIntegral.of_bounded (μ := A.jointLaw) (C := C) ?_
  filter_upwards [A.ae_forall_mem_Icc] with θ hθ
  have hC' : ‖θ i - A.base.firstPriceBid A.n (θ i)‖ ≤ C := hC (θ i) (hθ i)
  have hx0 : 0 ≤ A.highestValueAlloc.x (A.firstPriceBidProfile θ) i :=
    A.highestValueAlloc.nonneg _ i
  have hx1 : A.highestValueAlloc.x (A.firstPriceBidProfile θ) i ≤ 1 :=
    A.highestValueAlloc.le_one _ i
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) hC'
  rw [Real.norm_eq_abs, abs_mul]
  calc |θ i - A.base.firstPriceBid A.n (θ i)|
        * |A.highestValueAlloc.x (A.firstPriceBidProfile θ) i|
      ≤ C * 1 := by
        refine mul_le_mul (by rwa [← Real.norm_eq_abs]) ?_ (abs_nonneg _) hCnn
        rw [abs_of_nonneg hx0]; exact hx1
    _ = C := mul_one C

/-- The marginalized interim deviation payoff is integrable against `base.dist`, given that the
deviation's ex-ante payoff is integrable: Marginalizing an integrable function keeps it
integrable. -/
theorem integrable_devPayoff (i : Fin A.n) (s' : A.firstPriceMeasGame.Strategy)
    (hagree : ∀ j, j ≠ i → s' j = A.firstPriceStrategy j)
    (hint : Integrable (fun θ => A.firstPriceMeasGame.payoff i
      (A.firstPriceMeasGame.actionProfile s' θ) θ) A.jointLaw) :
    Integrable (fun t => A.firstPriceDevPayoff i t ((s' i).1 t)) A.base.dist.toMeasure := by
  -- The ex-ante integrand is the ex-ante deviation integrand for the bid schedule `(s' i).1`.
  have hact : ∀ θ : A.Profile, A.firstPriceMeasGame.actionProfile s' θ
      = update (A.firstPriceBidProfile θ) i ((s' i).1 (θ i)) := by
    intro θ
    funext j
    by_cases hj : j = i
    · subst hj; rw [MeasBayesianGame.actionProfile_apply, update_self]
    · rw [MeasBayesianGame.actionProfile_apply]
      rw [show update (A.firstPriceBidProfile θ) i ((s' i).1 (θ i)) j
            = A.firstPriceBidProfile θ j from Function.update_of_ne hj _ _]
      rw [firstPriceBidProfile_apply,
        show (s' j).1 = (A.firstPriceStrategy j).1 from congrArg Subtype.val (hagree j hj),
        firstPriceStrategy]
  -- Rewrite `hint` into integrability of the ex-ante deviation integrand.
  have hintθ : Integrable (A.firstPriceDevIntegrand i ((s' i).1)) A.jointLaw := by
    refine hint.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [firstPriceMeasGame_payoff, hact θ, update_self, firstPriceDevIntegrand]
  -- Integrability transfers across the coordinate split.
  exact (A.integrable_firstPriceDevIntegrand_iff i (s' i).2).mp hintθ

/-- **The symmetric schedule is a Bayes–Nash equilibrium** in the canonical
`MeasBayesianGame.IsBNE` sense. -/
theorem firstPriceBid_isBNE (hn : 2 ≤ A.n) :
    A.firstPriceMeasGame.IsBNE A.firstPriceStrategy := by
  rw [MeasBayesianGame.isBNE_iff]
  -- Incumbent integrability is the symmetric-schedule ex-ante integrand bound.
  refine ⟨fun i s' hagree hint => ?_, fun i => A.integrable_exAnte_firstPriceStrategy i⟩
  rw [ge_iff_le, A.exAnte_eq_integral_devPayoff i s' hagree,
    A.exAnte_eq_integral_devPayoff i A.firstPriceStrategy (fun _ _ => rfl)]
  refine integral_mono_ae (A.integrable_devPayoff i s' hagree hint)
    (A.integrable_devPayoff i A.firstPriceStrategy (fun _ _ => rfl)
      (A.integrable_exAnte_firstPriceStrategy i)) ?_
  -- A.e. the type lies in `[θlo, θhi]`, where the equilibrium bid beats every bid.
  have hsupp : ∀ᵐ t ∂A.base.dist.toMeasure, t ∈ Icc A.base.θlo A.base.θhi :=
    mem_ae_iff.mpr A.base.toMeasure_compl_Icc_eq_zero
  filter_upwards [hsupp] with t ht
  exact A.firstPriceBid_isEquilibriumBid hn i ht ((s' i).1 t)
end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter

end
