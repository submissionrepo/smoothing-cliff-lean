/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.MechanismDesign.ProsecutorJudge
import Mathlib

/-!
# Persuasion duality and finite KG splitting: Non-vacuity witnesses

Compile-time semantic witnesses for two slices of
`Econlib.MechanismDesign.InformationDesign.Persuasion`:

* **Chunk 1 — Kantorovich–Rubinstein duality** (`Duality/*`). The general-`Ω` persuasion-duality
  stack (`IsBayesPlausible`, `feasiblePrimal`, `primalValue`, `concaveClosure`, `IsDualFeasible`,
  `dualObjective`, `dualValue`, `IsSupergradient`, `IsSuperdifferentiable`, `HasBoundedSteepness`,
  `weakDuality`, `strongDuality_of_isKRLipschitz`, `noDualityGap`, `complementarySlackness`,
  `dualAttainment_TFAE`, `concaveClosure_jensen`, the two extreme structures) is forced through a
  **concrete compact metric state space** `Ω = [0,1]` and two genuinely distinct payoffs:

  * a **linear** `V_lin μ = 𝔼_μ[x]` — *concave* in the belief, hence **no-disclosure optimal**
    (superdifferentiable everywhere, the coordinate price `x` is its own supergradient);
  * a **convex** `V_sq μ = (𝔼_μ[x])²` — **full-disclosure optimal** (`IsBelowFullDisclosureValue`,
    the Jensen gap `(𝔼 x)² ≤ 𝔼[x²]`). The two extreme cases catch the two direction reversals the
    duality is prone to: A concave payoff whose *no-disclosure* optimum is mistaken for full
    disclosure, and a convex payoff the other way.
* **Chunk 2 — finite KG splitting** (`Finite/*`). The Kamenica–Gentzkow step-function machinery
  (`BayesPlausible_def`, `expectedSenderPayoff_def`, `concaveClosure_ge`, `concavification_finite`,
  `achievable_with_bounded_signals`, `strategic_ambiguity_finite`, `exists_signal_from_splitting`,
  `posterior_signalFromSplitting`, and the named binary-optimal-signal API
  `binarySignal_achieves_stepClosure`, `stepOptimalSplitting_bayesPlausible`,
  `posteriorOrPrior_stepOptimalSignal`, `stepOptimalSignal_π_apply`,
  `stepOptimalSignal_π_one_eq_pure`, the `stepOptimalWeights`/`stepOptimalBeliefs` support facts)
  is exercised on the **prosecutor–judge `3/10` prior** of
  `EconlibExamples.MechanismDesign.ProsecutorJudge`. The binary signal **attains** the step concave
  closure `3/5` (equality, not a one-sided bound); the splitting posteriors **average back to the
  prior** (an exact Bayes-plausibility equality); and `concavification_finite` is checked to bound
  *every* feasible payoff — including a suboptimal full-disclosure signal — from above, catching a
  `≤`/`≥` flip.

## What each direction reversal would break

* **Concave closure is an upper bound.** `prosecutorJudge_concavification_upper` evaluates the
  concavification on full disclosure (`3/10 ≤ 3/5`) and on the optimal signal (`3/5 ≤ 3/5`): A
  lower-bound mis-statement would let full disclosure exceed it.
* **Bayes plausibility is an exact mean equality.** `stepOptimalSplitting_bayesPlausible_witness`
  checks the splitting weights `(2/5, 3/5)` and beliefs average to `(7/10, 3/10)` exactly.
* **Value attains the bound.** `binarySignal_achieves_stepClosure_witness` is an *equality*
  `expectedSenderPayoff = stepConcaveClosure = 3/5`.
* **No-disclosure vs. full-disclosure (numeric, on a nondegenerate prior).** On the symmetric
  two-point prior `1/2·δ₀ + 1/2·δ₁` the two regimes give *genuinely different* values:
  `Vsq_fullDisclosure_strictly_beats_noDisclosure` (convex `V_sq`: full disclosure `1/2 > 1/4`) and
  `Vconc_noDisclosure_strictly_beats_fullDisclosure` (concave `V_conc`: no disclosure
  `−1/4 > −1/2`). Swapping the two regimes would pick the strictly worse value in at least one
  direction (a degenerate Dirac prior would have hidden this — full and no disclosure would
  coincide).
* **Weak duality is a strict gap on a strictly-majorizing price.**
  `primalValue_lt_dualObjective_strict` exhibits `1/2 < 3/2` for the shifted dual price `g + 1`; the
  coordinate price `g` gives only the equality case `1/2 = 1/2`, unable to catch a `dual ≤ primal`
  flip.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.PersuasionFinite

open MeasureTheory Set BoundedContinuousFunction NNReal ProbabilityTheory
open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
open Econlib.Optimization.OptimalTransport

/-! ## Chunk 1: Kantorovich–Rubinstein persuasion duality on `Ω = [0,1]`

The duality stack quantifies over a compact metric state space. We instantiate it on the
concrete unit interval `Ω = Set.Icc 0 1`, the simplest compact metric space carrying every instance
the stack needs (`PseudoMetricSpace`, `BorelSpace`, `CompactSpace`, `T2Space`,
`SecondCountableTopology`, `PseudoMetrizableSpace`, `Inhabited`). The state of the world is a
number in `[0,1]`, beliefs are probability laws on it, and the coordinate map `g x = x` is the
canonical `1`-Lipschitz price. -/

/-- The concrete state space: The unit interval, a compact metric space. -/
private abbrev Ω := Set.Icc (0 : ℝ) 1

instance : Inhabited Ω := ⟨⟨0, by norm_num⟩⟩

/-- The coordinate price function `g x = x` on `[0,1]`. It is `1`-Lipschitz, bounded in `[0,1]`,
and serves both as the linear payoff and as the canonical dual price. -/
private def g : Ω → ℝ := fun x => (x : ℝ)

private lemma g_lip : LipschitzWith 1 g := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [g, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]; rfl

private lemma g_cont : Continuous g := g_lip.continuous

/-- `g` packaged as a bounded continuous function on the compact `Ω`. -/
private def gBCF : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨g, g_cont⟩

private lemma g_mem_Icc : ∀ x : Ω, g x ∈ Set.Icc (0 : ℝ) 1 := fun x => ⟨x.2.1, x.2.2⟩

private lemma g_bdd : ∀ x : Ω, |g x| ≤ 1 := fun x =>
  abs_le.mpr ⟨by linarith [(g_mem_Icc x).1], (g_mem_Icc x).2⟩

/-! ### The linear (concave) payoff `V_lin μ = 𝔼_μ[x]`

A belief's mean. It is its own supergradient everywhere, so **no disclosure** is optimal for
it. -/

/-- The linear sender value: The posterior mean of the state. -/
private def Vlin : ProbDist Ω → ℝ := fun μ => ProbDist.expect μ g

/-- `V_lin` is continuous (weak-* continuity of integrating a bounded continuous function). -/
private lemma Vlin_cont : Continuous Vlin :=
  (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (X := Ω) gBCF).congr (fun _ => rfl)

private lemma Vlin_usc : UpperSemicontinuous Vlin := Vlin_cont.upperSemicontinuous

/-- `V_lin` is bounded in `[-1, 1]` (its values are posterior means of a `[0,1]`-valued state). -/
private lemma Vlin_bdd : ∃ M, ∀ μ : ProbDist Ω, |Vlin μ| ≤ M := by
  refine ⟨1, fun μ => ?_⟩
  have hint : Integrable g μ.toMeasure := gBCF.integrable μ.toMeasure
  rw [Vlin, ProbDist.expect, abs_le]
  refine ⟨?_, ?_⟩
  · calc (-1 : ℝ) = ∫ _, (-1 : ℝ) ∂μ.toMeasure := by simp
      _ ≤ ∫ x, g x ∂μ.toMeasure :=
          integral_mono (integrable_const _) hint (fun x => (abs_le.mp (g_bdd x)).1)
  · calc ∫ x, g x ∂μ.toMeasure ≤ ∫ _, (1 : ℝ) ∂μ.toMeasure :=
          integral_mono hint (integrable_const _) (fun x => (abs_le.mp (g_bdd x)).2)
      _ = 1 := by simp

/-- **`V_lin` is `1`-KR-Lipschitz.** Differences of posterior means are bounded by the
Kantorovich–Rubinstein distance with the same constant — this is exactly what feeds strong duality
and dual attainment. -/
private lemma Vlin_krlip : IsKRLipschitz Vlin 1 := fun μ ν => by
  simpa [Vlin] using expect_sub_le_kr_lipschitz (p := g) (K := 1) g_lip μ ν

/-- `V_lin` at a Dirac belief is the state's coordinate. -/
private lemma Vlin_dirac (ω : Ω) : Vlin (MeasureTheory.diracProba ω) = g ω := by
  unfold Vlin
  rw [ProbDist.expect,
    show (MeasureTheory.diracProba ω : ProbDist Ω).toMeasure = MeasureTheory.Measure.dirac ω from by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure],
    MeasureTheory.integral_dirac]

/-- **The coordinate price `g` is a supergradient of `V_lin` at every prior** — the no-disclosure
witness. Tightness `V_lin μ₀ = 𝔼_{μ₀} g` is definitional, and the majorization `V_lin μ ≤ 𝔼_μ g`
holds with equality, so a linear payoff supports itself. -/
private lemma Vlin_isSupergradient (μ₀ : ProbDist Ω) : IsSupergradient Vlin μ₀ g :=
  ⟨⟨1, g_lip⟩, rfl, fun _ => le_refl _⟩

private lemma Vlin_superdiff (μ₀ : ProbDist Ω) : IsSuperdifferentiable Vlin μ₀ :=
  ⟨g, Vlin_isSupergradient μ₀⟩

/-! ### The squared (convex) payoff `V_sq μ = (𝔼_μ[x])²`

A convex function of the mean. By Jensen `(𝔼 x)² ≤ 𝔼[x²]`, so `V_sq` lies below its
full-disclosure value everywhere: **full disclosure** is optimal for it. -/

/-- The convex sender value: The square of the posterior mean. -/
private def Vsq : ProbDist Ω → ℝ := fun μ => (ProbDist.expect μ g) ^ 2

/-- `V_sq` is continuous. -/
private lemma Vsq_cont : Continuous Vsq := Vlin_cont.pow 2

private lemma Vsq_usc : UpperSemicontinuous Vsq := Vsq_cont.upperSemicontinuous

/-- `V_sq` is bounded in `[0,1]`. -/
private lemma Vsq_bdd : ∃ M, ∀ μ : ProbDist Ω, |Vsq μ| ≤ M := by
  obtain ⟨M, hM⟩ := Vlin_bdd
  refine ⟨M ^ 2, fun μ => ?_⟩
  rw [Vsq, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM μ) 2

/-- `V_sq` at a Dirac belief is the square of the state's coordinate. -/
private lemma Vsq_diracProba (ω : Ω) : Vsq (MeasureTheory.diracProba ω) = g ω ^ 2 := by
  unfold Vsq; rw [show ProbDist.expect (MeasureTheory.diracProba ω) g = g ω from Vlin_dirac ω]

private lemma g_memLp (μ : ProbDist Ω) : MemLp g 2 μ.toMeasure :=
  memLp_of_bounded (Filter.Eventually.of_forall g_mem_Icc) g_cont.aestronglyMeasurable 2

/-- **`V_sq` is below its full-disclosure value** (Condition (F)). For every belief `μ`,
`V_sq μ = (𝔼_μ x)² ≤ 𝔼_μ[x²] = ∫ V_sq(δ_ω) dμ(ω)` — the Jensen gap, equivalently the nonnegativity
of the variance. This is precisely the convex-payoff direction: Revealing the state can only
help. -/
private lemma Vsq_belowFull : IsBelowFullDisclosureValue Vsq := by
  intro μ
  rw [show (∫ ω, Vsq (MeasureTheory.diracProba ω) ∂μ.toMeasure) = ∫ ω, g ω ^ 2 ∂μ.toMeasure from
    integral_congr_ae (Filter.Eventually.of_forall fun ω => Vsq_diracProba ω)]
  have hvar := variance_eq_sub (μ := μ.toMeasure) (g_memLp μ)
  have hvnn := variance_nonneg g μ.toMeasure
  rw [hvar] at hvnn
  unfold Vsq
  rw [show ProbDist.expect μ g = μ.toMeasure[g] from rfl,
    show μ.toMeasure[g ^ 2] = ∫ ω, g ω ^ 2 ∂μ.toMeasure from by simp [Pi.pow_apply]] at *
  linarith

/-! ### The concrete prior and the headline duality witnesses

We use a **nondegenerate symmetric two-point prior** `μ₀ = 1/2·δ₀ + 1/2·δ₁` on `[0,1]`. Its mean is
`1/2`, so the `V_lin` anchors are unchanged, but nondegeneracy is *load-bearing* for the
extreme-structure discrimination: under it, for the convex `V_sq` full disclosure (value `1/2`)
strictly beats no disclosure (value `1/4`), and for a strictly concave payoff the reverse strict
inequality holds. A degenerate Dirac prior would make full and no disclosure coincide, hiding the
direction reversals. The duality theorems also run on this real data. -/

/-- The endpoint `0 ∈ [0,1]`. -/
private def pt0 : Ω := ⟨0, by norm_num⟩

/-- The endpoint `1 ∈ [0,1]`. -/
private def pt1 : Ω := ⟨1, by norm_num⟩

/-- The symmetric two-point weights `(1/2, 1/2)` on the endpoints. -/
private def priorWeights : FinDist (Fin 2) :=
  ⟨![1 / 2, 1 / 2], by intro i; fin_cases i <;> norm_num, by simp [Fin.sum_univ_succ]; norm_num⟩

/-- The two endpoint Dirac masses. -/
private def priorComponents : Fin 2 → ProbDist Ω := ![ProbDist.dirac pt0, ProbDist.dirac pt1]

/-- The prior: the symmetric two-point law `μ₀ = 1/2·δ₀ + 1/2·δ₁` (mean `1/2`). -/
private def prior : ProbDist Ω := ProbDist.finMixture priorWeights priorComponents

/-- The full-disclosure prior over posteriors is Bayes-plausible (`IsBayesPlausible` /
`feasiblePrimal`): Averaging the Dirac posteriors `δ_ω` recovers the prior. -/
theorem isBayesPlausible_tauF_witness : IsBayesPlausible prior (tauF prior) :=
  isBayesPlausible_tauF prior

theorem tauF_mem_feasiblePrimal_witness : tauF prior ∈ feasiblePrimal prior :=
  isBayesPlausible_tauF prior

/-- The shifted dual price `g + 1`: still `1`-Lipschitz, and a **strict** majorant of `V_lin`. -/
private def gPlusOne : Ω → ℝ := fun x => g x + 1

private lemma gPlusOne_lip : LipschitzWith 1 gPlusOne := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [gPlusOne, g, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]
  rw [show ((x : ℝ) + 1) - ((y : ℝ) + 1) = (x : ℝ) - (y : ℝ) from by ring]

/-- `𝔼_μ (g + 1) = 𝔼_μ g + 1`. -/
private lemma expect_gPlusOne (μ : ProbDist Ω) :
    ProbDist.expect μ gPlusOne = ProbDist.expect μ g + 1 := by
  have hint : Integrable g μ.toMeasure := gBCF.integrable μ.toMeasure
  rw [ProbDist.expect, ProbDist.expect,
    show (∫ x, gPlusOne x ∂μ.toMeasure) = ∫ x, (g x + 1) ∂μ.toMeasure from rfl,
    integral_add hint (integrable_const _), integral_const]
  simp

/-- `g + 1` is dual-feasible for `V_lin` and majorizes it **strictly**: `V_lin μ = 𝔼_μ g <
𝔼_μ g + 1 = 𝔼_μ (g + 1)`. -/
private lemma gPlusOne_dualFeasible : IsDualFeasible Vlin gPlusOne := by
  refine ⟨⟨1, gPlusOne_lip⟩, fun μ => ?_⟩
  rw [Vlin, expect_gPlusOne]; linarith

/-- **Pairwise weak duality, with a strictly-majorizing price**
(`primalValue_le_dualObjective_of_feasible`): the primal payoff of the full-disclosure
meta-distribution for `V_lin` is below the dual objective of the **strict** majorant `g + 1`. The
inequality is `primal = 1/2 < 3/2 = dual` — a *strict* gap, so a flipped inequality
(`dual ≤ primal`) genuinely fails (the equality case at the coordinate price `g` could not catch
that flip). -/
theorem primalValue_le_dualObjective_witness :
    primalValue Vlin (tauF prior) ≤ dualObjective prior gPlusOne := by
  have hg_int : Integrable Vlin (tauF prior).toMeasure := by
    obtain ⟨M, hM⟩ := Vlin_bdd
    exact MeasureTheory.Integrable.of_bound Vlin_usc.measurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
  have hexpect_int :
      Integrable (fun μ : ProbDist Ω => ProbDist.expect μ gPlusOne) (tauF prior).toMeasure := by
    obtain ⟨M, hM⟩ := Vlin_bdd
    have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ gPlusOne) :=
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := Ω)
        (lipschitzToBounded gPlusOne_dualFeasible.lipschitz)).congr (fun _ => rfl)
    refine MeasureTheory.Integrable.of_bound hcont.measurable.aestronglyMeasurable
      (M + 1) (Filter.Eventually.of_forall fun μ => ?_)
    rw [Real.norm_eq_abs, expect_gPlusOne]
    have := hM μ; rw [Vlin] at this
    calc |ProbDist.expect μ g + 1| ≤ |ProbDist.expect μ g| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ M + 1 := by rw [abs_one]; linarith [this]
  exact primalValue_le_dualObjective_of_feasible hg_int hexpect_int
    (isBayesPlausible_tauF prior) gPlusOne_dualFeasible

/-- The prior mean `𝔼_{μ₀} g = 1/2·g(0) + 1/2·g(1) = 1/2·0 + 1/2·1 = 1/2`. -/
private lemma expect_prior_g : ProbDist.expect prior g = 1 / 2 := by
  rw [show prior = ProbDist.finMixture priorWeights priorComponents from rfl,
    ProbDist.expect_finMixture priorWeights priorComponents g (fun i => gBCF.integrable _),
    Fin.sum_univ_two]
  change priorWeights.pmf 0 * ProbDist.expect (priorComponents 0) g
      + priorWeights.pmf 1 * ProbDist.expect (priorComponents 1) g = 1 / 2
  rw [show priorComponents 0 = ProbDist.dirac pt0 from rfl,
    show priorComponents 1 = ProbDist.dirac pt1 from rfl, ProbDist.expect_dirac,
    ProbDist.expect_dirac]
  change (1 / 2 : ℝ) * g pt0 + (1 / 2 : ℝ) * g pt1 = 1 / 2
  rw [g, g]; norm_num [pt0, pt1]

/-- The primal value of full disclosure for `V_lin` is the prior mean `1/2`. -/
theorem primalValue_Vlin_tauF_eq : primalValue Vlin (tauF prior) = 1 / 2 := by
  rw [primalValue, show tauF prior = ProbDist.map prior MeasureTheory.diracProba
      MeasureTheory.continuous_diracProba.measurable from rfl,
    show (ProbDist.map prior MeasureTheory.diracProba
        MeasureTheory.continuous_diracProba.measurable : ProbDist (ProbDist Ω)).toMeasure
      = Measure.map MeasureTheory.diracProba prior.toMeasure from rfl,
    MeasureTheory.integral_map MeasureTheory.continuous_diracProba.measurable.aemeasurable
      Vlin_usc.measurable.aestronglyMeasurable,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => Vlin_dirac ω)]
  exact expect_prior_g

/-- The dual objective of `g + 1` at the prior is `3/2 = 𝔼_{δ_{1/2}}(g + 1) = 1/2 + 1`. -/
theorem dualObjective_gPlusOne_eq : dualObjective prior gPlusOne = 3 / 2 := by
  rw [dualObjective, expect_gPlusOne, expect_prior_g]; norm_num

/-- **The weak-duality gap is strict** on this strictly-majorizing pair: `1/2 < 3/2`. The
coordinate price `g` gives an *equality* `1/2 = 1/2` (also valid weak duality, but unable to catch
a `dual ≤ primal` flip); the shifted price `g + 1` exhibits the genuine strict gap. -/
theorem primalValue_lt_dualObjective_strict :
    primalValue Vlin (tauF prior) < dualObjective prior gPlusOne := by
  rw [primalValue_Vlin_tauF_eq, dualObjective_gPlusOne_eq]; norm_num

/-- **No duality gap** for `V_lin`: `concaveClosure = dualValue` at the prior. This is the strong
form `concaveClosure V μ₀ = dualValue V μ₀`, the headline Dworczak–Kolotilin equality, on real
data. -/
theorem noDualityGap_Vlin_witness : concaveClosure Vlin prior = dualValue Vlin prior :=
  noDualityGap Vlin_bdd Vlin_usc prior

/-- **Weak duality, global form** (`weakDuality`): `concaveClosure V_lin ≤ dualValue V_lin`. This
invokes `weakDuality` **directly** (not `noDualityGap`), discharging its four hypotheses concretely:
`feasiblePrimal` is nonempty (full disclosure `τ_F`), `feasibleDual` is nonempty (`g + 1` is dual
feasible), and `V_lin` / `μ ↦ 𝔼_μ p` are `τ`-integrable for every feasible pair (bounded
measurable on the compact `Ω`). A broken or removed `weakDuality` declaration is now caught. -/
theorem weakDuality_Vlin_witness : concaveClosure Vlin prior ≤ dualValue Vlin prior := by
  refine weakDuality (V := Vlin) (μ₀ := prior)
    ⟨tauF prior, isBayesPlausible_tauF prior⟩ ⟨gPlusOne, gPlusOne_dualFeasible⟩
    (fun τ _ => ?_) (fun τ _ p hp => ?_)
  · obtain ⟨M, hM⟩ := Vlin_bdd
    exact MeasureTheory.Integrable.of_bound Vlin_usc.measurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
  · -- `μ ↦ 𝔼_μ p` is bounded continuous for the dual-feasible (hence Lipschitz, bounded) `p`.
    have hcont : Continuous (fun μ : ProbDist Ω => ProbDist.expect μ p) :=
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := Ω)
        (lipschitzToBounded hp.lipschitz)).congr (fun _ => rfl)
    set pBCF := lipschitzToBounded hp.lipschitz with hpBCF
    -- `|p x| = ‖pBCF x‖ ≤ ‖pBCF‖` pointwise, so `μ ↦ 𝔼_μ p` is bounded by `‖pBCF‖`.
    have hp_bdd : ∀ x : Ω, |p x| ≤ ‖pBCF‖ := fun x => by
      rw [← Real.norm_eq_abs, show p x = pBCF x from rfl]; exact pBCF.norm_coe_le_norm x
    exact MeasureTheory.Integrable.of_bound hcont.measurable.aestronglyMeasurable
      ‖pBCF‖ (Filter.Eventually.of_forall fun μ => by
        rw [Real.norm_eq_abs, ProbDist.expect, abs_le]
        have hint : Integrable p μ.toMeasure := pBCF.integrable _
        constructor
        · calc -‖pBCF‖ = ∫ _, -‖pBCF‖ ∂μ.toMeasure := by simp
            _ ≤ ∫ x, p x ∂μ.toMeasure :=
                integral_mono (integrable_const _) hint (fun x => (abs_le.mp (hp_bdd x)).1)
        · calc ∫ x, p x ∂μ.toMeasure ≤ ∫ _, ‖pBCF‖ ∂μ.toMeasure :=
                integral_mono hint (integrable_const _) (fun x => (abs_le.mp (hp_bdd x)).2)
            _ = ‖pBCF‖ := by simp)

/-- **Strong duality from a KR-Lipschitz objective** (`strongDuality_of_isKRLipschitz`): The gap
closes, the primal supremum is attained, and the dual infimum is attained by a Lipschitz price. -/
theorem strongDuality_Vlin_witness :
    concaveClosure Vlin prior = dualValue Vlin prior ∧
    (∃ τ ∈ feasiblePrimal prior, primalValue Vlin τ = concaveClosure Vlin prior) ∧
    (∃ p ∈ feasibleDual Vlin, dualObjective prior p = dualValue Vlin prior) :=
  strongDuality_of_isKRLipschitz (L := 1) (by norm_num) Vlin_usc.measurable Vlin_bdd Vlin_usc
    Vlin_krlip prior

/-- **No duality gap and primal attainment** (`noDualityGap_and_primalAttainment`): The gap closes
*and* `concaveClosure` is attained by a Bayes-plausible `τ`. -/
theorem noDualityGap_and_primalAttainment_witness :
    concaveClosure Vlin prior = dualValue Vlin prior ∧
    ∃ τ ∈ feasiblePrimal prior, primalValue Vlin τ = concaveClosure Vlin prior :=
  noDualityGap_and_primalAttainment Vlin_bdd Vlin_usc prior

/-- **Primal attainment** (`primalAttainment`): The concave closure is attained by some
Bayes-plausible distribution of posteriors. -/
theorem primalAttainment_witness :
    ∃ τ ∈ feasiblePrimal prior, primalValue Vlin τ = concaveClosure Vlin prior :=
  primalAttainment Vlin_bdd Vlin_usc prior

/-- **Dual-attainment TFAE** (`dualAttainment_TFAE`): Superdifferentiability of `V̂`, bounded
steepness, and dual attainment are equivalent at the prior. -/
theorem dualAttainment_TFAE_witness :
    List.TFAE [
      IsSuperdifferentiable (concaveClosure Vlin) prior,
      ∃ L : ℝ, HasBoundedSteepness (concaveClosure Vlin) prior L,
      ∃ p ∈ feasibleDual Vlin, dualObjective prior p = dualValue Vlin prior] :=
  dualAttainment_TFAE Vlin_bdd Vlin_usc prior

/-- **Jensen for the concave closure** (`concaveClosure_jensen`): Averaging `V̂` under any
Bayes-plausible meta-distribution does not exceed `V̂` at the prior (concavity of the closure). -/
theorem concaveClosure_jensen_witness
    {τ : ProbDist (ProbDist Ω)} (hτ : IsBayesPlausible prior τ) :
    ∫ μ, concaveClosure Vlin μ ∂τ.toMeasure ≤ concaveClosure Vlin prior :=
  concaveClosure_jensen Vlin Vlin_bdd Vlin_usc hτ

/-- **Concave closure dominates the payoff** (`le_concaveClosure`): `V_lin μ ≤ V̂_lin μ` — the
concave closure is an **upper** envelope, never a lower one. -/
theorem le_concaveClosure_witness (μ : ProbDist Ω) : Vlin μ ≤ concaveClosure Vlin μ :=
  le_concaveClosure Vlin_bdd Vlin_usc μ

/-- **Complementary slackness** (`complementarySlackness`): The gap on the
`(full-disclosure τ_F, coordinate price g)` pair closes iff `V_lin μ = 𝔼_μ g` holds `τ_F`-a.e.;
here both sides are *definitionally equal*, so the slackness condition holds everywhere and the gap
closes. -/
theorem complementarySlackness_witness :
    primalValue Vlin (tauF prior) = dualObjective prior g ↔
      (∀ᵐ μ ∂(tauF prior).toMeasure, Vlin μ = ProbDist.expect μ g) := by
  have hV_int : Integrable Vlin (tauF prior).toMeasure := by
    obtain ⟨M, hM⟩ := Vlin_bdd
    exact MeasureTheory.Integrable.of_bound Vlin_usc.measurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun μ => by simpa using hM μ)
  exact complementarySlackness hV_int hV_int (isBayesPlausible_tauF prior)
    ⟨⟨1, g_lip⟩, fun _ => le_refl _⟩

/-- **No disclosure is optimal for the concave (linear) payoff**
(`noDisclosureOptimal_iff_isSuperdifferentiable`): `V_lin` is superdifferentiable at the prior, so
the no-disclosure meta-distribution `δ_{μ₀}` attains the persuasion value
`primalValue V_lin (δ_{μ₀}) = concaveClosure V_lin μ₀`. This is the **concave** extreme
structure. -/
theorem noDisclosureOptimal_Vlin_witness :
    primalValue Vlin (MeasureTheory.diracProba prior) = concaveClosure Vlin prior :=
  (noDisclosureOptimal_iff_isSuperdifferentiable (L := 1) (by norm_num) Vlin_krlip Vlin_bdd
    Vlin_usc prior).mpr (Vlin_superdiff prior)

/-- The no-disclosure persuasion value for `V_lin` is the prior mean `1/2` (the concave closure
evaluates to the mean, no information is gained). -/
theorem concaveClosure_Vlin_eq : concaveClosure Vlin prior = 1 / 2 := by
  rw [← noDisclosureOptimal_Vlin_witness,
    show primalValue Vlin (MeasureTheory.diracProba prior) = Vlin prior from by
      unfold primalValue
      rw [show (MeasureTheory.diracProba prior : ProbDist (ProbDist Ω)).toMeasure
            = MeasureTheory.Measure.dirac prior from by
          simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure],
        MeasureTheory.integral_dirac' _ _ Vlin_usc.measurable.stronglyMeasurable],
    show Vlin prior = ProbDist.expect prior g from rfl, expect_prior_g]

/-- `V_sq` is `2`-KR-Lipschitz. From `(𝔼 x)² − (𝔼 y)² = (𝔼 x + 𝔼 y)(𝔼 x − 𝔼 y)`, with the mean sum
in `[0, 2]` and the mean difference bounded by `krDist`. The constant is `2`, not `1` — the slope
of `t ↦ t²` is `2` at the right endpoint. -/
private lemma Vsq_krlip : IsKRLipschitz Vsq 2 := by
  intro μ ν
  have hdiff : ProbDist.expect μ g - ProbDist.expect ν g ≤ krDist μ ν := by
    simpa using expect_sub_le_kr_lipschitz (p := g) (K := 1) g_lip μ ν
  have hbound : ∀ ξ : ProbDist Ω, ProbDist.expect ξ g ∈ Set.Icc (0 : ℝ) 1 := by
    intro ξ
    refine ⟨by rw [ProbDist.expect]; exact integral_nonneg fun x => (g_mem_Icc x).1, ?_⟩
    rw [ProbDist.expect]
    calc ∫ x, g x ∂ξ.toMeasure ≤ ∫ _, (1 : ℝ) ∂ξ.toMeasure :=
          integral_mono (gBCF.integrable _) (integrable_const _) fun x => (g_mem_Icc x).2
      _ = 1 := by simp
  have hμ := hbound μ
  have hν := hbound ν
  have hkr_nn : 0 ≤ krDist μ ν := krDist_nonneg μ ν
  simp only [Vsq]
  -- Case split on the sign of the mean difference.
  rcases le_or_gt 0 (ProbDist.expect μ g - ProbDist.expect ν g) with hd | hd
  · nlinarith [mul_le_mul (show ProbDist.expect μ g + ProbDist.expect ν g ≤ 2 by
        have := hμ.2; have := hν.2; linarith) hdiff hd (by norm_num : (0 : ℝ) ≤ 2)]
  · nlinarith [hμ.1, hν.1, hμ.2, hν.2]

/-- **Full disclosure is optimal for the convex (squared) payoff**
(`fullDisclosureOptimal_of_isBelowFullDisclosureValue`): Since `V_sq` lies below its
full-disclosure value, the full-disclosure meta-distribution `τ_F` attains the persuasion value
`primalValue V_sq τ_F = concaveClosure V_sq μ₀`. This is the **convex** extreme structure — the
opposite of `V_lin`. -/
theorem fullDisclosureOptimal_Vsq_witness :
    primalValue Vsq (tauF prior) = concaveClosure Vsq prior :=
  fullDisclosureOptimal_of_isBelowFullDisclosureValue (L := 2) (by norm_num) Vsq_krlip
    Vsq_bdd Vsq_usc prior Vsq_belowFull

/-! ### Numeric extreme-structure discrimination on the nondegenerate prior

The structural witnesses above are correct but, on a degenerate prior, full and no disclosure
coincide and the *direction* of the optimum is untested. Here we compute both extreme objectives
**numerically** on `μ₀ = 1/2·δ₀ + 1/2·δ₁`, exhibiting genuinely different values:

* convex `V_sq`: full disclosure `1/2`, no disclosure `1/4` → full disclosure strictly wins;
* strictly concave `V_conc = −V_sq`: full disclosure `−1/2`, no disclosure `−1/4` → no disclosure
  strictly wins.

A swap of the two regimes would pick the wrong value in at least one case. -/

/-- The strictly concave payoff `V_conc μ = −(𝔼_μ x)²` (negative of `V_sq`). -/
private def Vconc : ProbDist Ω → ℝ := fun μ => -(ProbDist.expect μ g) ^ 2

/-- `V_conc μ = −Vsq μ`. -/
private lemma Vconc_eq (μ : ProbDist Ω) : Vconc μ = -Vsq μ := rfl

/-- `Vsq` (resp. `Vconc`) at a Dirac belief is `g ω ^ 2` (resp. `−g ω ^ 2`). The no-disclosure
objective at the prior reads off `Vsq prior = (1/2)² = 1/4`. -/
private lemma noDisclosure_Vsq : primalValue Vsq (MeasureTheory.diracProba prior) = 1 / 4 := by
  rw [primalValue, show (MeasureTheory.diracProba prior : ProbDist (ProbDist Ω)).toMeasure
      = MeasureTheory.Measure.dirac prior from by
        simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure],
    MeasureTheory.integral_dirac' _ _ Vsq_usc.measurable.stronglyMeasurable,
    show Vsq prior = (ProbDist.expect prior g) ^ 2 from rfl, expect_prior_g]
  norm_num

private lemma Vconc_cont : Continuous Vconc := Vsq_cont.neg

/-- The no-disclosure objective for the concave `V_conc` is `−1/4`. -/
private lemma noDisclosure_Vconc :
    primalValue Vconc (MeasureTheory.diracProba prior) = -(1 / 4) := by
  rw [primalValue, show (MeasureTheory.diracProba prior : ProbDist (ProbDist Ω)).toMeasure
      = MeasureTheory.Measure.dirac prior from by
        simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure],
    MeasureTheory.integral_dirac' _ _ Vconc_cont.stronglyMeasurable,
    show Vconc prior = -(ProbDist.expect prior g) ^ 2 from rfl, expect_prior_g]
  norm_num

/-- The full-disclosure objective `∫ ω, V(δ_ω) ∂μ₀` for a value `V` whose Dirac-composition
`ω ↦ V(δ_ω)` is continuous, on the two-point prior: `1/2·V(δ₀) + 1/2·V(δ₁)`. -/
private lemma fullDisclosure_eval {V : ProbDist Ω → ℝ} (hV : Measurable V)
    (hVc : Continuous (fun ω : Ω => V (MeasureTheory.diracProba ω))) :
    primalValue V (tauF prior)
      = 1 / 2 * V (MeasureTheory.diracProba pt0) + 1 / 2 * V (MeasureTheory.diracProba pt1) := by
  rw [Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.primalValue_tauF hV prior,
    show prior = ProbDist.finMixture priorWeights priorComponents from rfl]
  -- `∫ ω, V(δ_ω) dμ₀ = ∑ i w_i V(δ_{pt i})` (each component is a Dirac, integrand continuous).
  rw [show (∫ ω, V (MeasureTheory.diracProba ω)
        ∂(ProbDist.finMixture priorWeights priorComponents).toMeasure)
      = ProbDist.expect (ProbDist.finMixture priorWeights priorComponents)
          (fun ω => V (MeasureTheory.diracProba ω)) from rfl,
    ProbDist.expect_finMixture priorWeights priorComponents
      (fun ω => V (MeasureTheory.diracProba ω))
      (fun i => (hVc.comp continuous_id).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)),
    Fin.sum_univ_two]
  change priorWeights.pmf 0 * ProbDist.expect (priorComponents 0)
        (fun ω => V (MeasureTheory.diracProba ω))
      + priorWeights.pmf 1 * ProbDist.expect (priorComponents 1)
        (fun ω => V (MeasureTheory.diracProba ω))
      = 1 / 2 * V (MeasureTheory.diracProba pt0) + 1 / 2 * V (MeasureTheory.diracProba pt1)
  rw [show priorComponents 0 = ProbDist.dirac pt0 from rfl,
    show priorComponents 1 = ProbDist.dirac pt1 from rfl, ProbDist.expect_dirac,
    ProbDist.expect_dirac]
  change (1 / 2 : ℝ) * V (MeasureTheory.diracProba pt0)
      + (1 / 2 : ℝ) * V (MeasureTheory.diracProba pt1)
      = 1 / 2 * V (MeasureTheory.diracProba pt0) + 1 / 2 * V (MeasureTheory.diracProba pt1)
  rfl

/-- The full-disclosure objective for the convex `V_sq` is `1/2·0² + 1/2·1² = 1/2`. -/
private lemma fullDisclosure_Vsq : primalValue Vsq (tauF prior) = 1 / 2 := by
  rw [fullDisclosure_eval Vsq_usc.measurable
    (by simpa only [Vsq_diracProba] using g_cont.pow 2),
    Vsq_diracProba, Vsq_diracProba]
  norm_num [g, pt0, pt1]

/-- The full-disclosure objective for the concave `V_conc` is `1/2·(−0²) + 1/2·(−1²) = −1/2`. -/
private lemma fullDisclosure_Vconc : primalValue Vconc (tauF prior) = -(1 / 2) := by
  rw [fullDisclosure_eval Vconc_cont.measurable
    (by simp only [show (fun ω : Ω => Vconc (MeasureTheory.diracProba ω))
        = fun ω => -(g ω) ^ 2 from funext fun ω => by
          rw [Vconc_eq, Vsq_diracProba]]; exact (g_cont.pow 2).neg)]
  rw [show Vconc (MeasureTheory.diracProba pt0) = -(g pt0) ^ 2 from by
      rw [Vconc_eq, Vsq_diracProba],
    show Vconc (MeasureTheory.diracProba pt1) = -(g pt1) ^ 2 from by
      rw [Vconc_eq, Vsq_diracProba]]
  norm_num [g, pt0, pt1]

/-- **Convex payoff: full disclosure strictly beats no disclosure** (`1/4 < 1/2`). For `V_sq` the
sender wants to reveal: the full-disclosure objective `1/2` strictly exceeds the no-disclosure
objective `1/4`. A regime swap mistaking the *convex* optimum for no disclosure would pick the
strictly smaller `1/4`. -/
theorem Vsq_fullDisclosure_strictly_beats_noDisclosure :
    primalValue Vsq (MeasureTheory.diracProba prior) < primalValue Vsq (tauF prior) := by
  rw [noDisclosure_Vsq, fullDisclosure_Vsq]; norm_num

/-- **Strictly concave payoff: no disclosure strictly beats full disclosure** (`−1/2 < −1/4`). For
`V_conc` the sender wants to conceal: the no-disclosure objective `−1/4` strictly exceeds the
full-disclosure objective `−1/2`. Together with the convex case this shows the two regimes give
**genuinely different** optima — a swap would be caught in at least one direction. -/
theorem Vconc_noDisclosure_strictly_beats_fullDisclosure :
    primalValue Vconc (tauF prior) < primalValue Vconc (MeasureTheory.diracProba prior) := by
  rw [fullDisclosure_Vconc, noDisclosure_Vconc]; norm_num

/-! ## Chunk 2: Finite KG splitting on the prosecutor–judge `3/10` prior

We reuse `EconlibExamples.MechanismDesign.ProsecutorJudge`'s prior `Pr(guilty) = 3/10`,
conviction threshold `1/2`, and the named optimal binary signal. (The number `3/7` that appears in
the source is the *innocent-state convict likelihood* `π(convict | innocent)`, **not** the prior.)
The witnesses confirm the splitting averages back to the prior, the binary signal attains the step
concave closure, and `concavification_finite` upper-bounds every feasible payoff. -/

open EconlibExamples.MechanismDesign.ProsecutorJudge renaming prior → pjPrior,
  threshold → pjThreshold, prior_full_supp → pjPriorFullSupp,
  prior_below_threshold → pjPriorBelow, optimalInvestigation → pjOptimal
open EconlibExamples.MechanismDesign.ProsecutorJudge (fullDisclosure fullDisclosure_payoff)
open Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

/-- The conviction threshold `1/2` is strictly positive. -/
private lemma htp : (0 : ℝ) < pjThreshold := by norm_num [pjThreshold]

/-- The conviction threshold `1/2` is below one. -/
private lemma htl : pjThreshold < 1 := by norm_num [pjThreshold]

/-- **Bayes-plausibility as an exact mean equality** (`BayesPlausible_def`): Every signal structure
— here the prosecutor's optimal investigation — has its posteriors average back to the prior. The
defining identity is a strict equality on each state, not an inequality. -/
theorem bayesPlausible_def_witness :
    BayesPlausible pjPrior pjOptimal ↔
      ∀ θ, pjPrior.pmf θ =
        ∑ s, if _ : 0 < pjPrior.signalMarginal pjOptimal.π s
             then pjPrior.signalMarginal pjOptimal.π s *
               (pjPrior.posteriorOrPrior pjOptimal.π s).pmf θ
             else 0 :=
  BayesPlausible_def pjPrior pjOptimal

/-- **The optimal investigation's posteriors average back to the prior**
(`SignalStructure.bayesPlausible`): the concrete `BayesPlausible pjPrior pjOptimal` fact (not merely
the `Iff.rfl` unfold). Combined with the numeric splitting anchors below, this is the load-bearing
Bayes-plausibility content. -/
theorem bayesPlausible_pjOptimal_witness : BayesPlausible pjPrior pjOptimal :=
  SignalStructure.bayesPlausible pjPrior pjOptimal

/-- **The optimal splitting is Bayes-plausible** (`stepOptimalSplitting_bayesPlausible`): The
splitting weights `(2/5, 3/5)` against beliefs `(δ_innocent, (1/2, 1/2))` average to the
prior `(7/10, 3/10)` **exactly**. A normalization bug would make the posteriors miss the prior. -/
theorem stepOptimalSplitting_bayesPlausible_witness :
    ∀ i, ∑ s, (stepOptimalWeights pjThreshold htp pjPrior pjPriorBelow).pmf s *
        (stepOptimalBeliefs pjThreshold htp htl s).pmf i
      = pjPrior.pmf i :=
  stepOptimalSplitting_bayesPlausible pjThreshold htp
    htl pjPrior pjPriorBelow

/-- The two splitting weights are `2/5` (no-act) and `3/5` (act), summing to the convict
probability. Anchored evaluation of `stepOptimalWeights`. -/
theorem stepOptimalWeights_witness :
    (stepOptimalWeights pjThreshold htp pjPrior pjPriorBelow).pmf 0 = 2 / 5 ∧
    (stepOptimalWeights pjThreshold htp pjPrior pjPriorBelow).pmf 1 = 3 / 5 := by
  refine ⟨?_, ?_⟩
  · rw [stepOptimalWeights_pmf_zero]; norm_num [pjThreshold]
  · rw [stepOptimalWeights_pmf_one]; norm_num [pjThreshold]

/-- The act-belief puts exactly `1/2` on guilt (the threshold posterior); the no-act belief is
certain of innocence. Anchored evaluation of `stepOptimalBeliefs`. -/
theorem stepOptimalBeliefs_witness :
    (stepOptimalBeliefs pjThreshold htp htl 1).pmf 1
        = 1 / 2 ∧
    stepOptimalBeliefs pjThreshold htp htl 0
        = FinDist.pure 0 := by
  refine ⟨?_, rfl⟩
  rw [stepOptimalBeliefs_one_pmf_one]; norm_num [pjThreshold]

/-- **The posteriors of the optimal signal are the splitting beliefs**
(`posteriorOrPrior_stepOptimalSignal`): On each message the totalized posterior equals the
prescribed belief. -/
theorem posteriorOrPrior_stepOptimalSignal_witness (s : Fin 2) :
    pjPrior.posteriorOrPrior pjOptimal.π s
      = stepOptimalBeliefs pjThreshold htp htl s :=
  posteriorOrPrior_stepOptimalSignal pjThreshold htp
    htl pjPrior pjPriorFullSupp pjPriorBelow s

/-- **The optimal signal's likelihood in closed form** (`stepOptimalSignal_π_apply`): The realized
splitting `π(s | θ) = w(s) μ_s(θ) / p(θ)`, evaluated on the convict message at the guilty state. -/
theorem stepOptimalSignal_π_apply_witness :
    (pjOptimal.π 1).pmf 1
      = (stepOptimalWeights pjThreshold htp pjPrior pjPriorBelow).pmf 1
          * (stepOptimalBeliefs pjThreshold htp htl 1).pmf 1
          / pjPrior.pmf 1 :=
  stepOptimalSignal_π_apply pjThreshold htp htl
    pjPrior pjPriorFullSupp pjPriorBelow 1 1

/-- **All four likelihood entries of the optimal signal**, the load-bearing values being the
**off-diagonal** ones (a `(1,1)` diagonal check alone survives a transposition/argument swap):

* `π(convict | guilty) = 1` and `π(acquit | guilty) = 0` (guilty is always convicted);
* `π(convict | innocent) = 3/7` and `π(acquit | innocent) = 4/7` (the partial-pooling rate).

The asymmetric `3/7` and the exact `0` catch any swapped-argument or transposed-row bug. -/
theorem stepOptimalSignal_π_all_entries_witness :
    (pjOptimal.π 1).pmf 1 = 1 ∧ (pjOptimal.π 1).pmf 0 = 0 ∧
    (pjOptimal.π 0).pmf 1 = 3 / 7 ∧ (pjOptimal.π 0).pmf 0 = 4 / 7 := by
  refine ⟨?_, ?_,
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_innocent_convict,
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_innocent_acquit⟩
  · rw [EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_guilty,
      FinDist.pure_apply_self]
  · rw [EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_guilty]
    exact FinDist.pure_apply_ne (by decide)

/-- **A guilty defendant is reported "convict" for sure** (`stepOptimalSignal_π_one_eq_pure`): The
likelihood row at the high state is the point mass on the act signal. -/
theorem stepOptimalSignal_π_one_eq_pure_witness : pjOptimal.π 1 = FinDist.pure 1 :=
  stepOptimalSignal_π_one_eq_pure pjThreshold htp
    htl pjPrior pjPriorFullSupp pjPriorBelow

/-- **A binary signal attains the step concave closure** (`binarySignal_achieves_stepClosure`):
There is a Bayes-plausible binary signal whose sender value **equals** the step concave closure
`3/5` — equality, not a one-sided bound (no under- or over-shoot). -/
theorem binarySignal_achieves_stepClosure_witness :
    ∃ σ : SignalStructure 2 2,
      BayesPlausible pjPrior σ ∧
      expectedSenderPayoff pjPrior σ (stepPayoff pjThreshold)
        = stepConcaveClosure pjThreshold pjPrior :=
  binarySignal_achieves_stepClosure pjThreshold htp
    htl pjPrior pjPriorFullSupp pjPriorBelow

/-- The optimal binary signal attains `3/5` and the step concave closure is `3/5`: The attained
value equals the concavification — the Kamenica–Gentzkow optimum. -/
theorem binarySignal_value_eq_three_fifths :
    expectedSenderPayoff pjPrior pjOptimal (stepPayoff pjThreshold) = 3 / 5 := by
  rw [show expectedSenderPayoff pjPrior pjOptimal (stepPayoff pjThreshold)
        = stepConcaveClosure pjThreshold pjPrior from
      stepOptimalSignal_payoff pjThreshold htp htl
        pjPrior pjPriorFullSupp pjPriorBelow,
    stepConcaveClosure, if_neg (not_le.mpr pjPriorBelow)]
  norm_num [pjThreshold, pjPrior]

/-- **`expectedSenderPayoff` definitional unfold** (`expectedSenderPayoff_def`): The sender value
is a marginal-weighted sum of the payoff at each on-path posterior. -/
theorem expectedSenderPayoff_def_witness :
    expectedSenderPayoff pjPrior pjOptimal (stepPayoff pjThreshold)
      = ∑ s, if _ : 0 < pjPrior.signalMarginal pjOptimal.π s
             then pjPrior.signalMarginal pjOptimal.π s *
               stepPayoff pjThreshold (pjPrior.posteriorOrPrior pjOptimal.π s)
             else 0 :=
  expectedSenderPayoff_def pjPrior pjOptimal (stepPayoff pjThreshold)

/-- The acquit posterior (signal `0`) earns step payoff `0` (it is certain of innocence, guilt
probability `0 < 1/2`); the convict posterior (signal `1`) earns `1` (guilt probability `1/2 ≥
1/2`, the threshold). -/
private lemma stepPayoff_posterior_zero :
    stepPayoff pjThreshold (pjPrior.posteriorOrPrior pjOptimal.π 0) = 0 := by
  rw [posteriorOrPrior_stepOptimalSignal_witness 0, stepPayoff,
    show stepOptimalBeliefs pjThreshold htp htl 0 = FinDist.pure 0 from rfl,
    FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [if_neg (by norm_num [pjThreshold])]

private lemma stepPayoff_posterior_one :
    stepPayoff pjThreshold (pjPrior.posteriorOrPrior pjOptimal.π 1) = 1 := by
  rw [posteriorOrPrior_stepOptimalSignal_witness 1, stepPayoff,
    stepOptimalBeliefs_one_pmf_one pjThreshold htp htl, if_pos (by norm_num [pjThreshold])]

/-- **Anchored payoff decomposition**: the expected sender payoff is the marginal-weighted sum
`2/5·0 + 3/5·1 = 3/5` — acquit marginal `2/5` times payoff `0`, plus convict marginal `3/5` times
payoff `1`. This exercises the *components* (each marginal and each on-path posterior payoff), not
just the definitional folding of `expectedSenderPayoff`. -/
theorem expectedSenderPayoff_decomposition_witness :
    expectedSenderPayoff pjPrior pjOptimal (stepPayoff pjThreshold)
      = 2 / 5 * 0 + 3 / 5 * 1 := by
  rw [expectedSenderPayoff_def, Fin.sum_univ_two]
  have hm0 : pjPrior.signalMarginal pjOptimal.π 0 = 2 / 5 :=
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_acquits_prob
  have hm1 : pjPrior.signalMarginal pjOptimal.π 1 = 3 / 5 :=
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_convicts_prob
  rw [dif_pos (by rw [hm0]; norm_num), dif_pos (by rw [hm1]; norm_num),
    hm0, hm1, stepPayoff_posterior_zero, stepPayoff_posterior_one]

/-- **The concavification (general finite `concaveClosure`) equals the step concave closure `3/5`**
(`stepConcaveClosure_eq`): On the `3/10` prior the general concave-closure supremum collapses to the
closed form. -/
theorem concaveClosure_eq_three_fifths :
    concaveClosure (stepPayoff pjThreshold) pjPrior = 3 / 5 := by
  rw [stepConcaveClosure_eq pjThreshold htp htl
    pjPrior pjPriorFullSupp pjPriorBelow, stepConcaveClosure, if_neg (not_le.mpr pjPriorBelow)]
  norm_num [pjThreshold, pjPrior]

/-- **The trivial (no-signal) splitting is below the concave closure** (`concaveClosure_ge`):
`stepPayoff prior ≤ concaveClosure`. Here the no-information payoff `0` sits below the optimum
`3/5`, witnessing that the closure is an **upper** envelope. -/
theorem concaveClosure_ge_witness :
    stepPayoff pjThreshold pjPrior ≤ concaveClosure (stepPayoff pjThreshold) pjPrior := by
  apply concaveClosure_ge
  -- The feasible set is bounded above by `1`: `stepPayoff ≤ 1` and the weights sum to one.
  refine ⟨1, ?_⟩
  rintro E ⟨m, weights, beliefs, _, rfl⟩
  calc weights.expect (fun s => stepPayoff pjThreshold (beliefs s))
      = ∑ s, weights.pmf s * stepPayoff pjThreshold (beliefs s) := rfl
    _ ≤ ∑ s, weights.pmf s * 1 :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (by unfold stepPayoff; split_ifs <;> linarith) (weights.nonneg s)
    _ = 1 := by simp [weights.sum_one]

/-- **Concavification is an upper bound on every feasible payoff**, checked against *two* signals:
The optimal investigation (which attains `3/5`) and full disclosure (which earns the strictly
smaller `3/10`). A `≤`/`≥` flip would let full disclosure exceed the concavification. -/
theorem prosecutorJudge_concavification_upper :
    expectedSenderPayoff pjPrior pjOptimal (stepPayoff pjThreshold)
        ≤ concaveClosure (stepPayoff pjThreshold) pjPrior ∧
    expectedSenderPayoff pjPrior fullDisclosure (stepPayoff pjThreshold)
        ≤ concaveClosure (stepPayoff pjThreshold) pjPrior := by
  refine ⟨?_, ?_⟩
  · rw [binarySignal_value_eq_three_fifths, concaveClosure_eq_three_fifths]
  · rw [fullDisclosure_payoff, concaveClosure_eq_three_fifths]; norm_num

/-- The suboptimal benchmark, anchored: Full disclosure earns `3/10`, strictly below the
concavification `3/5`. Catches a concave closure that equals (rather than strictly dominates) the
full-disclosure value on this non-concave payoff. -/
theorem fullDisclosure_strictly_below_concavification :
    expectedSenderPayoff pjPrior fullDisclosure (stepPayoff pjThreshold)
      < concaveClosure (stepPayoff pjThreshold) pjPrior := by
  rw [fullDisclosure_payoff, concaveClosure_eq_three_fifths]; norm_num

/-! ### The general finite-splitting API (Caratheodory, NoInformation, Splitting) -/

/-- **Concavification with finitely many signals** (`concavification_finite`): The concave closure
equals the supremum over splittings with at most `n + 1 = 3` messages — the dimension reduction. -/
theorem concavification_finite_witness :
    concaveClosure (stepPayoff pjThreshold) pjPrior = sSup { E |
      ∃ (weights : FinDist (Fin 3)) (beliefs : Fin 3 → FinDist (Fin 2)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = pjPrior.pmf i) ∧
      E = weights.expect (fun s => stepPayoff pjThreshold (beliefs s)) } :=
  concavification_finite pjPrior (stepPayoff pjThreshold)

/-- A redundant `4`-signal splitting: four equally-weighted copies of the prior. Bayes-plausible
since `∑ s (1/4)·prior.pmf i = prior.pmf i`. -/
private def fourSignalWeights : FinDist (Fin 4) :=
  ⟨![1/4, 1/4, 1/4, 1/4], by intro i; fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_succ]; norm_num⟩

private def fourSignalBeliefs : Fin 4 → FinDist (Fin 2) := fun _ => pjPrior

private lemma fourSignal_bayesPlausible :
    ∀ i, ∑ s, fourSignalWeights.pmf s * (fourSignalBeliefs s).pmf i = pjPrior.pmf i := by
  intro i
  rw [Fin.sum_univ_four]
  change fourSignalWeights.pmf 0 * pjPrior.pmf i + fourSignalWeights.pmf 1 * pjPrior.pmf i
      + fourSignalWeights.pmf 2 * pjPrior.pmf i + fourSignalWeights.pmf 3 * pjPrior.pmf i
      = pjPrior.pmf i
  change (1/4 : ℝ) * pjPrior.pmf i + (1/4 : ℝ) * pjPrior.pmf i
      + (1/4 : ℝ) * pjPrior.pmf i + (1/4 : ℝ) * pjPrior.pmf i = pjPrior.pmf i
  ring

/-- **Every achievable payoff is achievable with `≤ 3` signals**
(`achievable_with_bounded_signals`). To genuinely exercise the **Carathéodory dimension reduction**
we start from a `4`-signal (redundant) splitting — four equally-weighted copies of the prior, a
valid Bayes-plausible splitting with `4 > n + 1 = 3` messages — and reduce it to `≤ 3` signals
while preserving the payoff. (The previous witness started from a `2`-signal splitting, already
within the bound, so it tested no reduction.) -/
theorem achievable_with_bounded_signals_witness :
    ∃ (weights' : FinDist (Fin 3)) (beliefs' : Fin 3 → FinDist (Fin 2)),
      (∀ i, ∑ s, weights'.pmf s * (beliefs' s).pmf i = pjPrior.pmf i) ∧
      weights'.expect (fun s => stepPayoff pjThreshold (beliefs' s)) =
        fourSignalWeights.expect (fun s => stepPayoff pjThreshold (fourSignalBeliefs s)) :=
  achievable_with_bounded_signals pjPrior (stepPayoff pjThreshold) 4
    fourSignalWeights fourSignalBeliefs fourSignal_bayesPlausible

/-- A **strictly concave, nonconstant** payoff on the belief simplex:
`v_conc μ = μ.pmf 1 · (1 − μ.pmf 1) = p − p²`. As a function of the guilt posterior `p` this is the
downward parabola peaking at `p = 1/2`; it is concave because `p ↦ p²` is convex. -/
private def vJensen : FinDist (Fin 2) → ℝ := fun μ => μ.pmf 1 * (1 - μ.pmf 1)

/-- `v_conc` is concave on the simplex: for any Bayes-plausible splitting with guilt posteriors
`p_s` averaging to `p`, `∑ w_s (p_s − p_s²) = p − ∑ w_s p_s² ≤ p − p² = v_conc(μ)`, using the
convex-Jensen bound `p² = (∑ w_s p_s)² ≤ ∑ w_s p_s²`. -/
private lemma vJensen_concaveOnSimplex : ConcaveOnSimplex vJensen := by
  intro k weights beliefs μ h_bp
  have hbp1 := h_bp 1
  -- `∑ s w_s p_s = μ.pmf 1`, with `p_s = (beliefs s).pmf 1`.
  have hjensen : (μ.pmf 1) ^ 2 ≤ ∑ s, weights.pmf s * ((beliefs s).pmf 1) ^ 2 := by
    have h := (convexOn_pow (𝕜 := ℝ) 2).map_sum_le (t := Finset.univ)
      (w := fun s => weights.pmf s) (p := fun s => (beliefs s).pmf 1)
      (fun s _ => weights.nonneg s) (by simpa using weights.sum_one)
      (fun s _ => (beliefs s).nonneg 1)
    rw [← hbp1]
    calc (∑ s, weights.pmf s * (beliefs s).pmf 1) ^ 2
        = (∑ s, weights.pmf s • (beliefs s).pmf 1) ^ 2 := by simp [smul_eq_mul]
      _ ≤ ∑ s, weights.pmf s • ((beliefs s).pmf 1) ^ 2 := h
      _ = ∑ s, weights.pmf s * ((beliefs s).pmf 1) ^ 2 := by simp [smul_eq_mul]
  -- Expand `v_conc` and finish.
  have hexpand : ∑ s, weights.pmf s * vJensen (beliefs s)
      = (∑ s, weights.pmf s * (beliefs s).pmf 1)
        - ∑ s, weights.pmf s * ((beliefs s).pmf 1) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [vJensen]; ring
  change ∑ s, weights.pmf s * vJensen (beliefs s) ≤ μ.pmf 1 * (1 - μ.pmf 1)
  rw [hexpand, hbp1]; nlinarith [hjensen]

/-- The no-information value of `v_conc` at the prior is `(3/10)·(7/10) = 21/100`. -/
private lemma vJensen_prior : vJensen pjPrior = 21 / 100 := by
  rw [vJensen, EconlibExamples.MechanismDesign.ProsecutorJudge.prior_pmf_one]; norm_num

/-- **Strategic ambiguity, finite case** (`strategic_ambiguity_finite`): a genuinely *concave,
nonconstant* payoff `v_conc μ = p(1 − p)` cannot beat no information. The optimal investigation
earns at most the no-information value `v_conc(prior) = 21/100`. (The previous witness used the
constant-`0` payoff, where `0 ≤ 0` also reversed — it could not catch the claimed direction
flip.) -/
theorem strategic_ambiguity_finite_witness :
    expectedSenderPayoff pjPrior pjOptimal vJensen ≤ vJensen pjPrior :=
  strategic_ambiguity_finite pjPrior pjOptimal vJensen vJensen_concaveOnSimplex

/-- **Strict Jensen loss for the concave payoff**: the optimal investigation earns
`2/5·v(δ_inn) + 3/5·v(conv) = 2/5·0 + 3/5·(1/4) = 3/20 = 15/100`, **strictly below** the
no-information value `21/100`. This is the genuine "concave ⇒ disclosure strictly hurts" content the
constant-`0` payoff could not exhibit. -/
theorem strategic_ambiguity_strict_loss :
    expectedSenderPayoff pjPrior pjOptimal vJensen < vJensen pjPrior := by
  rw [expectedSenderPayoff_def, Fin.sum_univ_two, vJensen_prior]
  have hm0 : pjPrior.signalMarginal pjOptimal.π 0 = 2 / 5 :=
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_acquits_prob
  have hm1 : pjPrior.signalMarginal pjOptimal.π 1 = 3 / 5 :=
    EconlibExamples.MechanismDesign.ProsecutorJudge.optimalInvestigation_convicts_prob
  -- `v_conc(acquit posterior) = 0·1 = 0`; `v_conc(convict posterior) = (1/2)·(1/2) = 1/4`.
  have hv0 : vJensen (pjPrior.posteriorOrPrior pjOptimal.π 0) = 0 := by
    rw [posteriorOrPrior_stepOptimalSignal_witness 0, vJensen,
      show stepOptimalBeliefs pjThreshold htp htl 0 = FinDist.pure 0 from rfl,
      FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ 1)]; ring
  have hv1 : vJensen (pjPrior.posteriorOrPrior pjOptimal.π 1) = 1 / 4 := by
    rw [posteriorOrPrior_stepOptimalSignal_witness 1, vJensen,
      stepOptimalBeliefs_one_pmf_one pjThreshold htp htl]; norm_num [pjThreshold]
  rw [dif_pos (by rw [hm0]; norm_num), dif_pos (by rw [hm1]; norm_num),
    hm0, hm1, hv0, hv1]; norm_num

/-- **Existence of a signal from a splitting** (`exists_signal_from_splitting`): The optimal
splitting (weights `(2/5, 3/5)`) is realized as a Bayes-plausible signal structure whose posteriors
recover the prescribed beliefs on every positive-marginal message. -/
theorem exists_signal_from_splitting_witness :
    ∃ σ : SignalStructure 2 2,
      BayesPlausible pjPrior σ ∧
      ∀ s, (hs : 0 < pjPrior.signalMarginal σ.π s) →
        pjPrior.posterior σ.π s hs
          = stepOptimalBeliefs pjThreshold htp htl s :=
  exists_signal_from_splitting pjPrior 2
    (stepOptimalWeights pjThreshold htp pjPrior pjPriorBelow)
    (stepOptimalBeliefs pjThreshold htp htl)
    (stepOptimalSplitting_bayesPlausible pjThreshold htp
    htl pjPrior pjPriorBelow)

end EconlibTest.MechanismDesign.PersuasionFinite

end
