/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.DualAttainment
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.KRStrongDuality
public import Econlib.Probability.ProbDist.Borel

/-!
# Full disclosure and no disclosure: Conditions (F) and (N)

The two extreme information structures — *full disclosure* and *no disclosure* — have explicit
named conditions for optimality under strong duality.  Both follow from complementary slackness
once dual attainment is in hand.

* **(F) — full disclosure** is optimal at *every* prior iff `V` lies below the linear functional
  `μ ↦ ∫ V(δ_ω) dμ(ω)` at every `μ ∈ Δ(Ω)`.  Geometrically, the function `ω ↦ V(δ_ω)`, viewed as a
  price function on `Ω`, is dual feasible for `V`.
* **(N) — no disclosure** is optimal at the prior `μ₀` iff `V` is *superdifferentiable* at `μ₀`.

Both conditions are characterizing equivalences, but at different scopes.  Condition (N) is
*local*, so its equivalence is pointwise at a fixed `μ₀`.  Condition (F) is a *global* bound on
`V`, so the matching equivalence ranges over all priors: It is necessary that full disclosure
attain the value at every prior, not merely at one.  (At a single degenerate prior full disclosure
is trivially optimal while (F) may fail, so a pointwise converse for (F) would need a full-support
hypothesis.)

## Main definitions

* `IsBelowFullDisclosureValue` — `V` is bounded by the linear functional `μ ↦ ∫ V(δ_ω) dμ(ω)`
  (Condition (F)). No-disclosure optimality is characterized via the existing
  `IsSuperdifferentiable` (Condition (N)).
* `tauF` — the full-disclosure meta-distribution, the pushforward of the prior along `ω ↦ δ_ω`.

## Main statements

* `noDisclosureOptimal_of_isSuperdifferentiable` — (N) ⇒ no disclosure attains the persuasion value.
* `isSuperdifferentiable_of_noDisclosureOptimal` — converse, under `KR`-Lipschitz `V`.
* `noDisclosureOptimal_iff_isSuperdifferentiable` — the no-disclosure characterization (N).
* `fullDisclosureOptimal_of_isBelowFullDisclosureValue` — (F) ⇒ full disclosure attains the
  persuasion value (at any prior).
* `isBelowFullDisclosureValue_of_fullDisclosureOptimal` — converse: Full disclosure optimal at
  every prior ⇒ (F).
* `fullDisclosureOptimal_iff_isBelowFullDisclosureValue` — the full-disclosure characterization (F).

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Section 3.4.

## Tags

persuasion, duality, full disclosure, no disclosure
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction NNReal
open scoped Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

open Econlib.Probability
open Econlib.Optimization.OptimalTransport

section ExtremeStructures

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

/-- `diracProba`'s underlying measure is the Dirac measure.  Stated with its own type variable so
it specializes both to `Ω` and to `ProbDist Ω`. -/
private lemma diracProba_toMeasure_eq {X : Type*} [MeasurableSpace X] (x : X) :
    (MeasureTheory.diracProba x : ProbDist X).toMeasure = MeasureTheory.Measure.dirac x := by
  simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [SecondCountableTopology Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- The primal value of no disclosure is `V` evaluated at the prior. -/
private lemma primalValue_diracProba_eq {V : ProbDist Ω → ℝ} (hV_meas : Measurable V)
    (μ₀ : ProbDist Ω) :
    primalValue V (MeasureTheory.diracProba μ₀) = V μ₀ := by
  unfold primalValue
  rw [diracProba_toMeasure_eq]
  exact MeasureTheory.integral_dirac' _ _ hV_meas.stronglyMeasurable

omit [CompactSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- The expected value of `q` under the Dirac posterior `δ_ω` is `q ω`. -/
private lemma expect_diracProba_eq (ω : Ω) (q : Ω → ℝ) :
    ProbDist.expect (MeasureTheory.diracProba ω) q = q ω := by
  unfold ProbDist.expect
  rw [diracProba_toMeasure_eq]
  exact MeasureTheory.integral_dirac _ _

omit [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The dual value is a lower bound for the dual objective at any feasible price. -/
private lemma dualValue_le_dualObjective {V : ProbDist Ω → ℝ} {μ₀ : ProbDist Ω} {p : Ω → ℝ}
    (hp_feas : p ∈ feasibleDual V) : dualValue V μ₀ ≤ dualObjective μ₀ p :=
  csInf_le ⟨V μ₀, by rintro _ ⟨q, hq, rfl⟩; exact hq.majorizes μ₀⟩ ⟨p, hp_feas, rfl⟩

/-! ## Condition (N) — no disclosure -/

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- **Sufficiency for no disclosure: Condition (N) ⇒ τ_N optimal.**

If `V` is superdifferentiable at `μ₀`, then no disclosure attains the persuasion-problem value:
`primalValue V (diracProba μ₀) = concaveClosure V μ₀`. -/
theorem noDisclosureOptimal_of_isSuperdifferentiable
    {V : ProbDist Ω → ℝ}
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) {μ₀ : ProbDist Ω}
    (hN : IsSuperdifferentiable V μ₀) :
    primalValue V (MeasureTheory.diracProba μ₀) = concaveClosure V μ₀ := by
  rw [primalValue_diracProba_eq hV_usc.measurable]
  refine le_antisymm (le_concaveClosure hV_bdd hV_usc μ₀) ?_
  obtain ⟨p, hp⟩ := hN
  have h_gap : concaveClosure V μ₀ = dualValue V μ₀ :=
    noDualityGap hV_bdd hV_usc μ₀
  rw [h_gap]
  have hp_feas : p ∈ feasibleDual V := ⟨hp.lipschitz, hp.majorizes⟩
  have h_inf_le : dualValue V μ₀ ≤ dualObjective μ₀ p := dualValue_le_dualObjective hp_feas
  have h_p_eq_V : dualObjective μ₀ p = V μ₀ := hp.value_eq.symm
  linarith

/-- **Necessity for no disclosure: τ_N optimal ⇒ condition (N).**

If `V` is `KR`-Lipschitz on `Δ(Ω)` and no disclosure attains the persuasion-problem value at `μ₀`,
then `V` is superdifferentiable at `μ₀`. -/
theorem isSuperdifferentiable_of_noDisclosureOptimal
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hV_lip : IsKRLipschitz V L)
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) {μ₀ : ProbDist Ω}
    (hopt : primalValue V (MeasureTheory.diracProba μ₀) = concaveClosure V μ₀) :
    IsSuperdifferentiable V μ₀ := by
  have h_V_eq_closure : V μ₀ = concaveClosure V μ₀ :=
    primalValue_diracProba_eq hV_usc.measurable μ₀ ▸ hopt
  obtain ⟨_, _, ⟨p, hp_feas, hp_value⟩⟩ :=
    strongDuality_of_isKRLipschitz hL hV_usc.measurable hV_bdd hV_usc hV_lip μ₀
  refine ⟨p, hp_feas.lipschitz, ?_, hp_feas.majorizes⟩
  have h_gap : concaveClosure V μ₀ = dualValue V μ₀ :=
    noDualityGap hV_bdd hV_usc μ₀
  have h_dual_eq : dualObjective μ₀ p = V μ₀ := by
    rw [hp_value, ← h_gap, ← h_V_eq_closure]
  exact h_dual_eq.symm

/-- **Characterization of no disclosure.**

Under `KR`-Lipschitz `V`, no disclosure attains the persuasion-problem value at `μ₀` if and only if
`V` is superdifferentiable at `μ₀` (Condition (N)). -/
theorem noDisclosureOptimal_iff_isSuperdifferentiable
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hV_lip : IsKRLipschitz V L)
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω) :
    primalValue V (MeasureTheory.diracProba μ₀) = concaveClosure V μ₀
      ↔ IsSuperdifferentiable V μ₀ :=
  ⟨isSuperdifferentiable_of_noDisclosureOptimal hL hV_lip hV_bdd hV_usc,
   noDisclosureOptimal_of_isSuperdifferentiable hV_bdd hV_usc⟩

/-! ## Condition (F) — full disclosure -/

/-- **Condition (F).**  `V` lies below the linear functional that attaches weight `V(δ_ω)` at each
`ω ∈ Ω`:

`V(μ) ≤ ∫ V(δ_ω) dμ(ω)`,  for every `μ ∈ Δ(Ω)`.

This characterizes when *full disclosure* — the meta-distribution `τ_F := μ₀.map diracProba`
putting all mass on Dirac posteriors — attains the persuasion-problem value: It is sufficient at
any single prior, and (being a global bound on `V`) necessary once full disclosure is optimal at
every prior. See `fullDisclosureOptimal_iff_isBelowFullDisclosureValue`. -/
def IsBelowFullDisclosureValue (V : ProbDist Ω → ℝ) : Prop :=
  ∀ μ : ProbDist Ω, V μ ≤ ∫ ω, V (MeasureTheory.diracProba ω) ∂μ.toMeasure

/-- The **full-disclosure meta-distribution** `τ_F`: Pushforward of the prior `μ₀` along the
embedding `ω ↦ δ_ω`. -/
noncomputable def tauF (μ₀ : ProbDist Ω) : ProbDist (ProbDist Ω) :=
  ProbDist.map μ₀ MeasureTheory.diracProba MeasureTheory.continuous_diracProba.measurable

omit [Inhabited Ω] in
/-- The full-disclosure meta-distribution is Bayes-plausible: Averaging over Dirac posteriors
recovers the prior. -/
theorem isBayesPlausible_tauF (μ₀ : ProbDist Ω) : IsBayesPlausible μ₀ (tauF μ₀) := by
  intro f
  unfold tauF
  have hcont_diracProba_meas :
      Measurable (fun ω : Ω => MeasureTheory.diracProba ω) :=
    MeasureTheory.continuous_diracProba.measurable
  have hexpect_meas :
      AEStronglyMeasurable (fun ν : ProbDist Ω => ProbDist.expect ν f)
        ((ProbDist.map μ₀ _ hcont_diracProba_meas).toMeasure) := by
    apply Continuous.aestronglyMeasurable
    simpa [ProbDist.expect] using
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
        (X := Ω) f)
  rw [show ∫ ν, ProbDist.expect ν f
        ∂(ProbDist.map μ₀ MeasureTheory.diracProba hcont_diracProba_meas).toMeasure
      = ∫ ω, ProbDist.expect (MeasureTheory.diracProba ω) f ∂μ₀.toMeasure from by
        rw [ProbDist.map_toMeasure]
        exact MeasureTheory.integral_map hcont_diracProba_meas.aemeasurable hexpect_meas]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  exact expect_diracProba_eq ω f

omit [Inhabited Ω] in
/-- The **primal value** of full disclosure is the integral of `V(δ_ω)` against the prior. -/
theorem primalValue_tauF
    {V : ProbDist Ω → ℝ} (hV_meas : Measurable V) (μ₀ : ProbDist Ω) :
    primalValue V (tauF μ₀) = ∫ ω, V (MeasureTheory.diracProba ω) ∂μ₀.toMeasure := by
  unfold primalValue tauF
  rw [ProbDist.map_toMeasure]
  exact MeasureTheory.integral_map
    MeasureTheory.continuous_diracProba.measurable.aemeasurable
    hV_meas.aestronglyMeasurable

omit [Inhabited Ω] in
/-- **Sufficiency for full disclosure: Condition (F) ⇒ τ_F optimal.**

If `V` is `KR`-Lipschitz and Condition (F) holds, then full disclosure attains the
persuasion-problem value: `primalValue V (tauF μ₀) = concaveClosure V μ₀`. -/
theorem fullDisclosureOptimal_of_isBelowFullDisclosureValue
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hV_lip : IsKRLipschitz V L)
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) (μ₀ : ProbDist Ω)
    (hF : IsBelowFullDisclosureValue V) :
    primalValue V (tauF μ₀) = concaveClosure V μ₀ := by
  have hV_meas : Measurable V := hV_usc.measurable
  rw [primalValue_tauF hV_meas]
  have h_lower : ∫ ω, V (MeasureTheory.diracProba ω) ∂μ₀.toMeasure ≤ concaveClosure V μ₀ := by
    rw [← primalValue_tauF hV_meas]
    refine le_csSup ?_ ⟨tauF μ₀, isBayesPlausible_tauF μ₀, rfl⟩
    obtain ⟨M, hM⟩ := hV_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨τ, _, rfl⟩
    unfold primalValue
    have hV_int : Integrable V τ.toMeasure := by
      refine ⟨hV_meas.aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const M).mono' ?_
      refine Filter.Eventually.of_forall fun ν => ?_
      simp only [Real.norm_eq_abs]
      exact hM ν
    calc ∫ ν, V ν ∂τ.toMeasure
        ≤ ∫ _, M ∂τ.toMeasure :=
          integral_mono hV_int (integrable_const _) (fun ν => (abs_le.mp (hM ν)).2)
      _ = M := by simp
  have h_upper : concaveClosure V μ₀ ≤ ∫ ω, V (MeasureTheory.diracProba ω) ∂μ₀.toMeasure := by
    set p_F : Ω → ℝ := fun ω => V (MeasureTheory.diracProba ω) with hp_F_def
    have hp_F_lip : ∃ K : NNReal, LipschitzWith K p_F := by
      refine ⟨L.toNNReal, ?_⟩
      refine LipschitzWith.of_dist_le_mul (fun ω₁ ω₂ => ?_)
      have h_kr : krDist (MeasureTheory.diracProba ω₁) (MeasureTheory.diracProba ω₂)
          ≤ dist ω₁ ω₂ := by
        refine csSup_le ⟨0, fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by simp), ?_⟩ ?_
        · simp [ProbDist.expect]
        rintro _ ⟨q, hq_lip, rfl⟩
        have hq_diff : ProbDist.expect (MeasureTheory.diracProba ω₁) q
            - ProbDist.expect (MeasureTheory.diracProba ω₂) q
            = q ω₁ - q ω₂ := by
          rw [expect_diracProba_eq, expect_diracProba_eq]
        rw [hq_diff]
        have h := hq_lip.dist_le_mul ω₁ ω₂
        rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
        exact (abs_le.mp h).2
      have h_V_diff : V (MeasureTheory.diracProba ω₁) - V (MeasureTheory.diracProba ω₂)
          ≤ L * krDist (MeasureTheory.diracProba ω₁) (MeasureTheory.diracProba ω₂) :=
        hV_lip _ _
      have h_V_diff_sym : V (MeasureTheory.diracProba ω₂) - V (MeasureTheory.diracProba ω₁)
          ≤ L * krDist (MeasureTheory.diracProba ω₂) (MeasureTheory.diracProba ω₁) :=
        hV_lip _ _
      rw [krDist_comm] at h_V_diff_sym
      have h_kr_nn : 0 ≤ krDist (MeasureTheory.diracProba ω₁) (MeasureTheory.diracProba ω₂) :=
        krDist_nonneg _ _
      have h_dist_ω : 0 ≤ dist ω₁ ω₂ := dist_nonneg
      rw [Real.dist_eq, abs_le]
      have hL_kr_le : L * krDist (MeasureTheory.diracProba ω₁) (MeasureTheory.diracProba ω₂)
          ≤ L * dist ω₁ ω₂ := mul_le_mul_of_nonneg_left h_kr hL
      have hLnn_eq : ((L.toNNReal : NNReal) : ℝ) * dist ω₁ ω₂ = L * dist ω₁ ω₂ := by
        rw [Real.coe_toNNReal _ hL]
      rw [hLnn_eq]
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    have hp_F_maj : ∀ μ : ProbDist Ω, V μ ≤ ProbDist.expect μ p_F := hF
    have hp_F_feas : p_F ∈ feasibleDual V := ⟨hp_F_lip, hp_F_maj⟩
    have h_gap : concaveClosure V μ₀ = dualValue V μ₀ :=
      noDualityGap hV_bdd hV_usc μ₀
    rw [h_gap]
    exact dualValue_le_dualObjective hp_F_feas
  exact le_antisymm h_lower h_upper

omit [Inhabited Ω] in
/-- **Necessity for full disclosure: τ_F optimal everywhere ⇒ Condition (F).**

If full disclosure attains the persuasion-problem value at *every* prior, then Condition (F) holds.
The point is that optimality at `μ` gives `∫ V(δ_ω) dμ = concaveClosure V μ ≥ V μ`, which is
exactly (F) evaluated at `μ`.

Necessity is stated across all priors rather than at a single `μ₀` because (F) is a *global*
condition on `V` (a bound at every posterior), in contrast to the *local* Condition (N).  A
pointwise converse "full disclosure optimal at `μ₀` ⇒ (F)" is false without a full-support
hypothesis on `μ₀`: At a degenerate prior full disclosure is trivially optimal yet (F) can fail. -/
theorem isBelowFullDisclosureValue_of_fullDisclosureOptimal
    {V : ProbDist Ω → ℝ}
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V)
    (hopt : ∀ μ : ProbDist Ω, primalValue V (tauF μ) = concaveClosure V μ) :
    IsBelowFullDisclosureValue V := fun μ =>
  calc V μ ≤ concaveClosure V μ := le_concaveClosure hV_bdd hV_usc μ
    _ = primalValue V (tauF μ) := (hopt μ).symm
    _ = ∫ ω, V (MeasureTheory.diracProba ω) ∂μ.toMeasure := primalValue_tauF hV_usc.measurable μ

omit [Inhabited Ω] in
/-- **Characterization of full disclosure (Condition (F)).**

Under `KR`-Lipschitz `V`, full disclosure attains the persuasion-problem value at *every* prior if
and only if Condition (F) holds.  Unlike the no-disclosure characterization, which is pointwise at
a fixed `μ₀` (because Condition (N) is local), this equivalence ranges over all priors because (F)
is a global condition on `V`. -/
theorem fullDisclosureOptimal_iff_isBelowFullDisclosureValue
    {V : ProbDist Ω → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hV_lip : IsKRLipschitz V L)
    (hV_bdd : ∃ M, ∀ μ : ProbDist Ω, |V μ| ≤ M)
    (hV_usc : UpperSemicontinuous V) :
    (∀ μ : ProbDist Ω, primalValue V (tauF μ) = concaveClosure V μ)
      ↔ IsBelowFullDisclosureValue V :=
  ⟨isBelowFullDisclosureValue_of_fullDisclosureOptimal hV_bdd hV_usc,
   fun hF μ => fullDisclosureOptimal_of_isBelowFullDisclosureValue hL hV_lip hV_bdd hV_usc μ hF⟩

end ExtremeStructures

end Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
