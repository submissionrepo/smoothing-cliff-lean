/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Moment persuasion: Convex roof, joint-posterior bridge, and dual price witnesses

Compile-time semantic witnesses for `Econlib.MechanismDesign.InformationDesign.Persuasion.Moment`,
the deepest and least-consumed slice of the persuasion module. We instantiate the `MomentSetup`
framework on a concrete one-dimensional moment problem and exercise the convex-roof sandwich, the
Bayesian ↔ joint round-trip, the dual-price convexity, and the top-level optimal-joint existence.

## The concrete instance

* State space `Ω = [0,1]` (a compact metric space carrying every instance the framework needs:
  `MeasurableSpace`, `PseudoMetricSpace`, `BorelSpace`, `CompactSpace`, `T2Space`,
  `SecondCountableTopology`, `Inhabited`).
* Moment dimension `n = 1`; moment map `m ω = (ω,) ∈ ℝ¹` (the coordinate embedding), `1`-Lipschitz.
* Moment image set `X = {y ∈ ℝ¹ : y₀ ∈ [0,1]}` — a compact convex interval with nonempty interior;
  it is exactly the convex hull of `m(Ω)`, so **every** `y ∈ X` is the posterior moment of some
  posterior (the Bayes-plausibility feasibility hypothesis of `convexRoof_convexOn`).
* Sender values: the **linear** `v(x) = x₀` (`1`-Lipschitz, `C¹`, composed value `V(μ) = 𝔼_μ[ω]`,
  the posterior mean) for the roof / dual-price chunks, and the **strictly concave**
  `vconc(x) = −(clamp x₀)²` (`2`-Lipschitz, bounded in `[−1, 0]`, composed value `−(𝔼_μ[ω])²`) for
  the optimality chunk, so that the maximization is genuinely non-degenerate.
* Prior: the **asymmetric two-point law** `μ₀ = 1/4·δ₀ + 3/4·δ₁` (mean `3/4`). Nondegeneracy is
  load-bearing: it separates full disclosure (posteriors `δ₀, δ₁`, moments `0, 1`) from no
  disclosure (single posterior `μ₀`, moment `3/4`).

## What each chunk exercises

* **Convex roof / upper envelope** (`Moment/ConvexRoof`): `convexRoof_convexOn` (the roof `p̌` is
  convex on `X`), the concrete `p̌(y) = y₀` identity, `posteriorMoment_finMixture` (linearity, with
  the concrete asymmetric-mixture anchor `3/4`), and the **sandwich** `v ≤ upperEnvelope ≤ p̌` on
  `X`, all three terms anchored to the coordinate `y₀` and the slope-`1` (not slope-`0`) subgradient
  proved concretely (`upperEnvelope_eq_coord_witness`, `upperEnvelope_le_convexRoof_on_X_witness`).
* **Joint ↔ Bayesian round-trip** (`Moment/JointPosteriorBridge`): A Bayes-plausible distribution
  of posteriors maps to a **feasible joint** (`isFeasibleJoint_jointFromBayesian`, with its three
  components `marginal` / `fst_supportsOn` / `martingale`, the last via
  `jointFromBayesian_martingale`); the joint is the pushforward of the compProd
  (`jointFromBayesian_eq_map_compProd`); and a feasible joint maps **back** to a Bayes-plausible
  distribution (`isBayesPlausible_bayesianFromJoint`) — Bayes-plausibility is preserved in **both**
  directions. On the asymmetric prior the full-disclosure joint's objective is anchored numerically
  at `3/4` (`jointFromBayesian_objective_witness`).
* **Dual price** (`Moment/OptimalDualPriceStructural`): `pStar_convexOn` — the formula-`S`
  tangent-envelope dual price `p*` is convex on `X`.
* **Top-level optimality** (`Moment/DifferentiableUniqueness`): `exists_optimal_joint` for the
  strictly concave `vconc` — the moment primal value is **attained** by a feasible joint. The
  attainment is certified non-degenerate by a hand-computed strict Jensen gap: the no-disclosure
  objective `−9/16` strictly exceeds the full-disclosure objective `−3/4`, both being objectives of
  genuine feasible joints, so the `momentPrimal` supremum is a real maximization
  (`momentPrimal_ge_noDisclosure_witness`, `objective_strict_jensen_gap`).

## Direction-reversal catches

* `pStar ≥ v on X`, **not** `v ≥ pStar`: The dual price majorizes the value. The convex-roof
  sandwich `v ≤ upperEnvelope ≤ p̌` makes the majorization direction load-bearing.
* Bayes-plausibility is preserved **both ways** by the bridge: A reversed-marginal construction
  (taking the `X`-marginal as the `Ω`-marginal, say) would break `marginal` or
  `isBayesPlausible_bayesianFromJoint`.
* `posteriorMoment` is **linear** in the posterior (`posteriorMoment_finMixture`): A normalization
  bug in the mixture weights would break the mean-vector identity.
-/

noncomputable section

namespace EconlibTest.MechanismDesign.PersuasionMoment

open MeasureTheory Set BoundedContinuousFunction
open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality
open Econlib.Optimization.OptimalTransport

/-! ## The concrete one-dimensional moment setup -/

/-- State space: The unit interval `[0,1]`. -/
private abbrev Ω := Set.Icc (0 : ℝ) 1

instance : Inhabited Ω := ⟨⟨0, by norm_num⟩⟩

/-- The moment map `m ω = (ω,) ∈ ℝ¹` — the coordinate embedding of `[0,1]` into `ℝ¹`. -/
private def mmap : Ω → EuclideanSpace ℝ (Fin 1) :=
  fun ω => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (ω : ℝ))

private lemma mmap_apply (ω : Ω) (i : Fin 1) : (mmap ω) i = (ω : ℝ) := by
  simp [mmap, EuclideanSpace.equiv]

/-- The moment image set `X = {y : y₀ ∈ [0,1]}`, the `1`-D interval that is the convex hull of the
moment image of `[0,1]`. -/
private def Xset : Set (EuclideanSpace ℝ (Fin 1)) := {y | y 0 ∈ Icc (0 : ℝ) 1}

private lemma Xset_compact : IsCompact Xset := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Icc.preimage
      (by fun_prop : Continuous (fun y : EuclideanSpace ℝ (Fin 1) => y 0))
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    have hy' : y 0 ∈ Icc (0 : ℝ) 1 := hy
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_one,
      Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs, abs_le]
    exact ⟨by linarith [hy'.1, hy'.2], hy'.2⟩

private lemma Xset_convex : Convex ℝ Xset := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  simp only [Xset, mem_setOf_eq] at *
  rw [show (a • y₁ + b • y₂) 0 = a * y₁ 0 + b * y₂ 0 from by simp]
  exact ⟨by nlinarith [hy₁.1, hy₂.1], by nlinarith [hy₁.2, hy₂.2]⟩

private lemma Xset_interior : (interior Xset).Nonempty := by
  refine ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 / 2 : ℝ)), ?_⟩
  rw [mem_interior]
  refine ⟨(fun y : EuclideanSpace ℝ (Fin 1) => y 0) ⁻¹' Ioo (0 : ℝ) 1, ?_, ?_, ?_⟩
  · intro y hy; exact ⟨hy.1.le, hy.2.le⟩
  · exact isOpen_Ioo.preimage (by fun_prop)
  · simp [EuclideanSpace.equiv]; norm_num

/-- The endpoint `0 ∈ Ω = [0,1]`. -/
private def pt0 : Ω := ⟨0, by norm_num⟩

/-- The endpoint `1 ∈ Ω = [0,1]`. -/
private def pt1 : Ω := ⟨1, by norm_num⟩

/-- The asymmetric two-point weights `(1/4, 3/4)` on the endpoints `(0, 1)`. -/
private def priorWeights : FinDist (Fin 2) :=
  ⟨![1 / 4, 3 / 4], by intro i; fin_cases i <;> norm_num,
    by simp [Fin.sum_univ_succ]; norm_num⟩

/-- The two endpoint Dirac masses, indexed by `Fin 2`. -/
private def priorComponents : Fin 2 → ProbDist Ω := ![ProbDist.dirac pt0, ProbDist.dirac pt1]

/-- **The prior: a nondegenerate asymmetric two-point law** `μ₀ = 1/4·δ₀ + 3/4·δ₁`. Its prior mean
(posterior moment of the whole prior) is `1/4·0 + 3/4·1 = 3/4`, which separates full disclosure
(posteriors `δ₀, δ₁` with moments `0, 1`) from no disclosure (single posterior `μ₀` with moment
`3/4`). This replaces the degenerate point-mass prior the review flagged as collapsing the two
extreme structures. -/
private def priorDist : ProbDist Ω := ProbDist.finMixture priorWeights priorComponents

/-- The concrete moment-persuasion setup on `[0,1]` with the coordinate moment. -/
private def setup : MomentSetup Ω 1 where
  m := mmap
  m_continuous := by unfold mmap; fun_prop
  X := Xset
  X_compact := Xset_compact
  X_convex := Xset_convex
  X_interior := Xset_interior
  m_mem_X := by
    intro ω; show mmap ω ∈ Xset; rw [Xset, mem_setOf_eq, mmap_apply]; exact ω.2
  moment_surjOn_X := by
    -- Every `y ∈ X` is the posterior moment of the Dirac at the point with coordinate `y₀`.
    intro y hy
    have hy' : y 0 ∈ Icc (0 : ℝ) 1 := hy
    refine ⟨ProbDist.dirac ⟨y 0, hy'⟩, ?_⟩
    rw [ProbDist.dirac_toMeasure, integral_dirac]
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [mmap_apply]
  prior := priorDist

/-- Each moment coordinate is `1`-Lipschitz (`MomentSetup.IsCoordLipschitz`). -/
private lemma setup_coordLip : setup.IsCoordLipschitz := by
  intro _
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul]
  change dist (mmap x _) (mmap y _) ≤ dist x y
  rw [mmap_apply, mmap_apply, Real.dist_eq, Subtype.dist_eq, Real.dist_eq]

/-- **Every `y ∈ X` is a posterior moment** — the Bayes-plausibility feasibility now carried by the
`setup` itself (the `moment_surjOn_X` field). The matching posterior is the Dirac at the point with
coordinate `y₀`. -/
private lemma setup_feasible : ∀ y ∈ setup.X, ∃ μ : ProbDist Ω, setup.posteriorMoment μ = y :=
  setup.feasible

/-! ## The sender value `v(x) = x₀` -/

/-- The linear sender value: The first coordinate of the moment vector. Its composed value
`V(μ) = v(𝔼_μ[m]) = 𝔼_μ[ω]` is the posterior mean. -/
private def vcoord : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0

private lemma vcoord_lip : LipschitzWith 1 vcoord := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul, vcoord, Real.dist_eq]
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, Real.sqrt_sq_eq_abs]
  exact le_abs_self _

private lemma vcoord_cont : Continuous vcoord := vcoord_lip.continuous

private lemma vcoord_meas : Measurable vcoord := vcoord_cont.measurable

private lemma vcoord_contDiff : ContDiff ℝ 1 vcoord :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff

/-- The coordinate map `ω ↦ (ω : ℝ)` on `Ω`. -/
private def coe1 : Ω → ℝ := fun ω => (ω : ℝ)

private lemma coe1_cont : Continuous coe1 := by unfold coe1; fun_prop

private def coe1BCF : Ω →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨coe1, coe1_cont⟩

private lemma coe1_lip : LipschitzWith 1 coe1 := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  simp only [NNReal.coe_one, one_mul, coe1, Real.dist_eq, Subtype.dist_eq]; rfl

/-- The price `coe1` is literally the `0`-coordinate of the moment map. -/
private lemma coe1_eq_m_ofLp : (fun ω => (setup.m ω).ofLp 0) = coe1 := by
  funext ω; rw [show setup.m = mmap from rfl, mmap_apply]; rfl

/-- **The convex roof of `coe1` equals the bare coordinate on `X`.** Every feasible `μ` (one with
`posteriorMoment μ = y`) has `𝔼_μ[coe1] = (posteriorMoment μ)₀ = y₀`, so the defining infimum is
over the singleton `{y₀}` and reduces to `y₀`. This is the concrete fact that makes the slope-`1`
subgradient and the `v ≤ p̌` half of the sandwich load-bearing (replacing the impossible slope-`0`
hypothesis flagged by review). -/
private lemma convexRoof_coe1_eq {y : EuclideanSpace ℝ (Fin 1)} (hy : y ∈ setup.X) :
    convexRoof setup coe1 y = y 0 := by
  -- Every member of the defining set equals `y 0`, and the set is nonempty (`y` feasible).
  have h_set : {z : ℝ | ∃ μ : ProbDist Ω,
      setup.posteriorMoment μ = y ∧ z = ProbDist.expect μ coe1} = {y 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      rw [← coe1_eq_m_ofLp, ← setup.posteriorMoment_ofLp μ 0, hμ]
    · rintro rfl
      obtain ⟨μ, hμ⟩ := setup_feasible y hy
      exact ⟨μ, hμ, by rw [← coe1_eq_m_ofLp, ← setup.posteriorMoment_ofLp μ 0, hμ]⟩
  rw [show convexRoof setup coe1 y = sInf {z : ℝ | ∃ μ : ProbDist Ω,
      setup.posteriorMoment μ = y ∧ z = ProbDist.expect μ coe1} from rfl, h_set, csInf_singleton]

/-- The unit slope `e₀ = (1,) ∈ ℝ¹`, the gradient of the coordinate `y ↦ y₀`. -/
private def e0 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 : ℝ)

/-- The inner product against the unit slope reads off the first coordinate. -/
private lemma inner_e0 (v : EuclideanSpace ℝ (Fin 1)) : inner ℝ e0 v = v 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_one]
  simp [e0]

private lemma norm_e0 : ‖e0‖ = 1 := by rw [e0, PiLp.norm_single]; norm_num

/-- **The unit slope `e₀` is a subgradient of the roof on `X`.** Since `p̌ = coe1` coordinate on
`X` (`convexRoof_coe1_eq`), the supporting inequality `p̌ y ≥ p̌ x + ⟨e₀, y − x⟩` reads
`y₀ ≥ x₀ + (y₀ − x₀)`, an equality. This is the *true* subgradient (slope `1`), replacing the
impossible slope-`0` hypothesis the review flagged as making the witness vacuous. -/
private lemma e0_mem_subderiv {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ setup.X) :
    e0 ∈ SubderivWithinAt (convexRoof setup coe1) setup.X x := by
  intro y hy
  rw [convexRoof_coe1_eq hy, convexRoof_coe1_eq hx, inner_e0]
  have : (y - x) 0 = y 0 - x 0 := by simp
  rw [this]; ring_nf; rfl

/-! ### A globally bounded sender value and its posterior-mean composed value

`exists_optimal_joint` requires a *globally* bounded value, so for it we use the clamp
`v_clamp(x) = max 0 (min 1 x₀)` — globally bounded in `[0,1]`, `1`-Lipschitz, and equal to the
coordinate `x₀` on the moment image `X`. Since the posterior moment always lies in `X`
(`posteriorMoment_mem_X`), the composed value `V(μ) = v_clamp(𝔼_μ[m]) = 𝔼_μ[ω]` is the posterior
mean — weak-* continuous and bounded in `[0,1]`. -/

/-- The clamped sender value, globally bounded in `[0,1]`. -/
private def vclamp : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => max 0 (min 1 (x 0))

private lemma vclamp_lip : LipschitzWith 1 vclamp := vcoord_lip.const_min 1 |>.const_max 0

private lemma vclamp_cont : Continuous vclamp := vclamp_lip.continuous

private lemma vclamp_meas : Measurable vclamp := vclamp_cont.measurable

private lemma vclamp_bdd : ∃ M, ∀ x, |vclamp x| ≤ M :=
  ⟨1, fun x => abs_le.mpr
    ⟨by rw [vclamp]; linarith [le_max_left (0 : ℝ) (min 1 (x 0))],
     by rw [vclamp, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩⟩⟩

private lemma vclamp_usc : UpperSemicontinuous vclamp := vclamp_cont.upperSemicontinuous

/-- On the moment image `X`, the clamp equals the bare coordinate. -/
private lemma vclamp_eq_on_X {y : EuclideanSpace ℝ (Fin 1)} (hy : y 0 ∈ Icc (0 : ℝ) 1) :
    vclamp y = y 0 := by
  rw [vclamp, min_eq_right hy.2, max_eq_right hy.1]

/-- **The composed value of the clamp is the posterior mean** `V(μ) = 𝔼_μ[ω]`: The posterior moment
always lies in `X` (`posteriorMoment_mem_X`), so the clamp is inactive and reads off the single
coordinate, which is the posterior expectation of `m·₀ = ω`. -/
private lemma composedValue_vclamp (μ : ProbDist Ω) :
    setup.composedValue vclamp μ = ProbDist.expect μ coe1 := by
  unfold MomentSetup.composedValue
  have hmem : (setup.posteriorMoment μ) 0 ∈ Icc (0 : ℝ) 1 := setup.posteriorMoment_mem_X μ
  have hmcoe : (fun ω => (setup.m ω).ofLp 0) = coe1 := by
    funext ω; rw [show setup.m = mmap from rfl, mmap_apply]; rfl
  rw [vclamp_eq_on_X hmem,
    show (setup.posteriorMoment μ) 0 = (setup.posteriorMoment μ).ofLp 0 from rfl,
    setup.posteriorMoment_ofLp μ 0, hmcoe]

/-! ### A strictly concave clamped value, for genuine optimization

The linear value `vclamp` makes every feasible joint equally optimal, so a maximizer/minimizer
confusion in `exists_optimal_joint` would be invisible. We add the **strictly concave** clamped
value `vconc(x) = −(clamp x₀)²` (bounded in `[−1, 0]`, `2`-Lipschitz, continuous). Under it the
optimization is non-degenerate: by strict concavity no disclosure (objective `−(3/4)² = −9/16`)
strictly beats full disclosure (objective `1/4·(−0²) + 3/4·(−1²) = −3/4`), a strict Jensen loss
`−3/4 < −9/16`. -/

/-- The strictly concave clamped sender value `vconc(x) = −(clamp x₀)²`, bounded in `[−1, 0]`. -/
private def vconc : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => -(vclamp x) ^ 2

/-- `vconc` is `2`-Lipschitz: `|(clamp y₀)² − (clamp x₀)²| = |Δclamp|·|clamp y₀ + clamp x₀| ≤
|Δclamp|·2 ≤ 2·dist x y`, using `clamp ∈ [0,1]` and that `vclamp` is `1`-Lipschitz. -/
private lemma vconc_lip : LipschitzWith 2 vconc := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  have hcx : vclamp x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, by rw [vclamp, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩⟩
  have hcy : vclamp y ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, by rw [vclamp, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩⟩
  have hclamp_dist : dist (vclamp x) (vclamp y) ≤ dist x y := by
    have := vclamp_lip.dist_le_mul x y; simpa using this
  rw [Real.dist_eq, vconc, vconc]
  have h_factor : |(-(vclamp x) ^ 2) - (-(vclamp y) ^ 2)|
      = |vclamp x - vclamp y| * |vclamp x + vclamp y| := by
    rw [show (-(vclamp x) ^ 2) - (-(vclamp y) ^ 2)
      = (vclamp y - vclamp x) * (vclamp x + vclamp y) from by ring, abs_mul, abs_sub_comm]
  rw [h_factor]
  have h_sum_le : |vclamp x + vclamp y| ≤ 2 := by
    rw [abs_le]; constructor <;> [nlinarith [hcx.1, hcy.1]; nlinarith [hcx.2, hcy.2]]
  have h_diff : |vclamp x - vclamp y| ≤ dist x y := by rw [← Real.dist_eq]; exact hclamp_dist
  calc |vclamp x - vclamp y| * |vclamp x + vclamp y|
      ≤ dist x y * 2 := by
        apply mul_le_mul h_diff h_sum_le (abs_nonneg _) dist_nonneg
    _ = (2 : NNReal) * dist x y := by push_cast; ring

private lemma vconc_cont : Continuous vconc := vconc_lip.continuous

private lemma vconc_meas : Measurable vconc := vconc_cont.measurable

private lemma vconc_bdd : ∃ M, ∀ x, |vconc x| ≤ M := by
  refine ⟨1, fun x => ?_⟩
  have hcx : vclamp x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, by rw [vclamp, max_le_iff]; exact ⟨by norm_num, min_le_left _ _⟩⟩
  rw [vconc, abs_le]
  constructor <;> nlinarith [hcx.1, hcx.2]

private lemma vconc_usc : UpperSemicontinuous vconc := vconc_cont.upperSemicontinuous

/-- On the moment image `X`, `vconc` is the bare negative square `−(y₀)²`. -/
private lemma vconc_eq_on_X {y : EuclideanSpace ℝ (Fin 1)} (hy : y 0 ∈ Icc (0 : ℝ) 1) :
    vconc y = -(y 0) ^ 2 := by rw [vconc, vclamp_eq_on_X hy]

/-- The composed value of `vconc` is `−(posterior mean)²` (the posterior moment lies in `X`). -/
private lemma composedValue_vconc (μ : ProbDist Ω) :
    setup.composedValue vconc μ = -(ProbDist.expect μ coe1) ^ 2 := by
  unfold MomentSetup.composedValue
  have hmem : (setup.posteriorMoment μ) 0 ∈ Icc (0 : ℝ) 1 := setup.posteriorMoment_mem_X μ
  rw [vconc_eq_on_X hmem,
    show (setup.posteriorMoment μ) 0 = (setup.posteriorMoment μ).ofLp 0 from rfl,
    setup.posteriorMoment_ofLp μ 0, coe1_eq_m_ofLp]

private lemma composedValue_vconc_cont : Continuous (setup.composedValue vconc) := by
  rw [show setup.composedValue vconc = fun μ => -(ProbDist.expect μ coe1) ^ 2 from
    funext composedValue_vconc]
  refine (((MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (X := Ω) coe1BCF).congr (fun _ => rfl)).pow 2).neg

private lemma composedValue_vconc_usc : UpperSemicontinuous (setup.composedValue vconc) :=
  composedValue_vconc_cont.upperSemicontinuous

private lemma composedValue_vconc_bdd :
    ∃ M, ∀ μ : ProbDist Ω, |setup.composedValue vconc μ| ≤ M := by
  refine ⟨1, fun μ => ?_⟩
  rw [composedValue_vconc]
  have hint : Integrable coe1 μ.toMeasure := coe1BCF.integrable μ.toMeasure
  have h_mean_mem : ProbDist.expect μ coe1 ∈ Icc (0 : ℝ) 1 := by
    rw [ProbDist.expect]
    constructor
    · calc (0 : ℝ) = ∫ _, (0 : ℝ) ∂μ.toMeasure := by simp
        _ ≤ ∫ ω, coe1 ω ∂μ.toMeasure :=
            integral_mono (integrable_const _) hint (fun ω => by simp only [coe1]; exact ω.2.1)
    · calc ∫ ω, coe1 ω ∂μ.toMeasure ≤ ∫ _, (1 : ℝ) ∂μ.toMeasure :=
            integral_mono hint (integrable_const _) (fun ω => by simp only [coe1]; exact ω.2.2)
        _ = 1 := by simp
  rw [abs_le]
  constructor <;> nlinarith [h_mean_mem.1, h_mean_mem.2]

private lemma composedValue_cont : Continuous (setup.composedValue vclamp) := by
  rw [show setup.composedValue vclamp = fun μ => ProbDist.expect μ coe1 from
    funext composedValue_vclamp]
  exact (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (X := Ω) coe1BCF).congr (fun _ => rfl)

private lemma composedValue_usc : UpperSemicontinuous (setup.composedValue vclamp) :=
  composedValue_cont.upperSemicontinuous

private lemma composedValue_bdd : ∃ M, ∀ μ : ProbDist Ω, |setup.composedValue vclamp μ| ≤ M := by
  refine ⟨1, fun μ => ?_⟩
  rw [composedValue_vclamp]
  have hint : Integrable coe1 μ.toMeasure := coe1BCF.integrable μ.toMeasure
  rw [ProbDist.expect, abs_le]
  refine ⟨?_, ?_⟩
  · calc (-1 : ℝ) = ∫ _, (-1 : ℝ) ∂μ.toMeasure := by simp
      _ ≤ ∫ ω, coe1 ω ∂μ.toMeasure :=
          integral_mono (integrable_const _) hint
            (fun ω => by simp only [coe1]; linarith [ω.2.1])
  · calc ∫ ω, coe1 ω ∂μ.toMeasure ≤ ∫ _, (1 : ℝ) ∂μ.toMeasure :=
          integral_mono hint (integrable_const _)
            (fun ω => by simp only [coe1]; linarith [ω.2.2])
      _ = 1 := by simp

/-- **The prior mean is `3/4`**: `𝔼_{μ₀}[ω] = 1/4·0 + 3/4·1 = 3/4` for the asymmetric two-point
prior `μ₀ = 1/4·δ₀ + 3/4·δ₁`. This is the no-disclosure objective and the prior-moment anchor. -/
private lemma priorDist_mean : ProbDist.expect priorDist coe1 = 3 / 4 := by
  rw [show priorDist = ProbDist.finMixture priorWeights priorComponents from rfl,
    ProbDist.expect_finMixture priorWeights priorComponents coe1
      (fun i => coe1BCF.integrable _), Fin.sum_univ_two]
  change priorWeights.pmf 0 * ProbDist.expect (priorComponents 0) coe1
      + priorWeights.pmf 1 * ProbDist.expect (priorComponents 1) coe1 = 3 / 4
  rw [show priorComponents 0 = ProbDist.dirac pt0 from rfl,
    show priorComponents 1 = ProbDist.dirac pt1 from rfl,
    ProbDist.expect_dirac, ProbDist.expect_dirac]
  change (1 / 4 : ℝ) * (pt0 : ℝ) + (3 / 4 : ℝ) * (pt1 : ℝ) = 3 / 4
  norm_num [pt0, pt1]

/-! ## Chunk 5a: Convex roof and the upper-envelope sandwich -/

/-- **The posterior moment of a finite mixture is the mixture of posterior moments**
(`posteriorMoment_finMixture`): Linearity of `μ ↦ 𝔼_μ[m]`. A weight-normalization bug would break
this mean-vector identity. -/
theorem posteriorMoment_finMixture_witness {N : ℕ}
    (w : FinDist (Fin N)) (ds : Fin N → ProbDist Ω) :
    setup.posteriorMoment (ProbDist.finMixture w ds)
      = ∑ i, w.pmf i • setup.posteriorMoment (ds i) :=
  posteriorMoment_finMixture setup w ds

/-- **Concrete asymmetric mixture anchor**: the posterior moment of the prior
`μ₀ = 1/4·δ₀ + 3/4·δ₁` has `0`-coordinate exactly `1/4·0 + 3/4·1 = 3/4`. A weight-normalization
bug (e.g. swapping `1/4 ↔ 3/4`, giving `1/4`, or failing to normalize, giving anything else) is
caught by the asymmetric `3/4`. -/
theorem priorDist_posteriorMoment_witness :
    (setup.posteriorMoment priorDist) 0 = 3 / 4 := by
  rw [show priorDist = ProbDist.finMixture priorWeights priorComponents from rfl,
    posteriorMoment_finMixture setup priorWeights priorComponents]
  -- Each Dirac component has posterior moment `m(ptᵢ)`, whose `0`-coordinate is the endpoint.
  have hm0 : (setup.posteriorMoment (ProbDist.dirac pt0)) 0 = 0 := by
    rw [show (setup.posteriorMoment (ProbDist.dirac pt0)) 0
        = (setup.posteriorMoment (ProbDist.dirac pt0)).ofLp 0 from rfl,
      setup.posteriorMoment_ofLp, ProbDist.expect_dirac]
    rw [show setup.m = mmap from rfl, mmap_apply]; rfl
  have hm1 : (setup.posteriorMoment (ProbDist.dirac pt1)) 0 = 1 := by
    rw [show (setup.posteriorMoment (ProbDist.dirac pt1)) 0
        = (setup.posteriorMoment (ProbDist.dirac pt1)).ofLp 0 from rfl,
      setup.posteriorMoment_ofLp, ProbDist.expect_dirac]
    rw [show setup.m = mmap from rfl, mmap_apply]; rfl
  rw [Fin.sum_univ_two]
  change priorWeights.pmf 0 * (setup.posteriorMoment (priorComponents 0)) 0
      + priorWeights.pmf 1 * (setup.posteriorMoment (priorComponents 1)) 0 = 3 / 4
  rw [show priorComponents 0 = ProbDist.dirac pt0 from rfl,
    show priorComponents 1 = ProbDist.dirac pt1 from rfl, hm0, hm1]
  change (1 / 4 : ℝ) * 0 + (3 / 4 : ℝ) * 1 = 3 / 4
  norm_num

/-- **The convex roof is convex on `X`** (`convexRoof_convexOn`): The lower convex envelope
`p̌(y) = inf { 𝔼_μ[p] : 𝔼_μ[m] = y }` of a Lipschitz price `p` is a convex function on the moment
image `X` (using that every `y ∈ X` is a posterior moment). Witnessed for `p = coe1`. -/
theorem convexRoof_convexOn_witness :
    ConvexOn ℝ setup.X (convexRoof setup coe1) :=
  convexRoof_convexOn setup (L := 1) coe1_lip

/-- **The convex roof of `coe1` equals the coordinate on `X`** (the "lower roof" semantics anchor):
`p̌(y) = y₀` for every `y ∈ X`. A confusion of the *lower* roof with an *upper* envelope (which
here would also be `coe1`, but a sup/inf swap would break this on a nonlinear price) is caught by
the concrete equality. At `y = (1/2,)`: `p̌(1/2) = 1/2`. -/
theorem convexRoof_coe1_eq_witness {y : EuclideanSpace ℝ (Fin 1)} (hy : y ∈ setup.X) :
    convexRoof setup coe1 y = y 0 :=
  convexRoof_coe1_eq hy

/-- **The upper envelope dominates `v` on `X`** (`upperEnvelope_ge_v_on_X`): The supporting-affine
envelope `sup_x (v x + ⟨q x, y − x⟩)` lies above `v` on `X` (taking `x = y`). The lower half of the
`v ≤ upperEnvelope ≤ p̌` sandwich; witnessed with the **unit slope** `q = e₀` (not zero), so the
affine term `⟨e₀, y − x⟩ = y₀ − x₀` is exercised. -/
theorem upperEnvelope_ge_v_on_X_witness :
    ∀ y ∈ setup.X, vcoord y ≤ upperEnvelope setup vcoord (fun _ => e0) y :=
  upperEnvelope_ge_v_on_X setup vcoord_cont (K := 1) (fun _ => le_of_eq norm_e0)

/-- **The upper envelope at the unit slope reads off the coordinate** (the exact affine anchor):
with `q ≡ e₀` and `v = coe1`-coordinate, the supporting line `x ↦ v x + ⟨e₀, y − x⟩ = x₀ + (y₀ −
x₀) = y₀` is the *constant* `y₀`, so `upperEnvelope setup vcoord e₀ y = y₀`. This is exactly `p̌ y`,
making the sandwich `v ≤ upperEnvelope ≤ p̌` a genuine equality chain at `y` and catching any
sign/argument error in `inner (q x) (y − x)`. At `y = (1/2,)`: the envelope value is `1/2`. -/
theorem upperEnvelope_eq_coord_witness {y : EuclideanSpace ℝ (Fin 1)} (hy : y ∈ setup.X) :
    upperEnvelope setup vcoord (fun _ => e0) y = y 0 := by
  -- The image `{v x + ⟨e₀, y − x⟩ : x ∈ X}` is the constant singleton `{y₀}`.
  have h_const : (fun x : EuclideanSpace ℝ (Fin 1) =>
      vcoord x + inner ℝ e0 (y - x)) '' setup.X = {y 0} := by
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, rfl⟩
      rw [inner_e0, vcoord]
      have : (y - x) 0 = y 0 - x 0 := by simp
      rw [this]; ring
    · rintro rfl
      exact ⟨y, hy, by rw [inner_e0, vcoord]; simp⟩
  rw [show upperEnvelope setup vcoord (fun _ => e0) y
      = sSup ((fun x : EuclideanSpace ℝ (Fin 1) =>
        vcoord x + inner ℝ e0 (y - x)) '' setup.X) from rfl, h_const, csSup_singleton]

/-- **The upper envelope is below the convex roof on `X`** (`upperEnvelope_le_convexRoof_on_X`):
the upper half of the sandwich. We discharge **both** hypotheses concretely — the unit slope `e₀`
*is* a subgradient of the roof (`e0_mem_subderiv`, slope `1`), and `v = coe1 = p̌` so `v ≤ p̌`
(`convexRoof_coe1_eq`). No assumed hypotheses remain (the review flagged the previous slope-`0`
hypothesis as impossible, hence the theorem as vacuous). -/
theorem upperEnvelope_le_convexRoof_on_X_witness :
    ∀ y ∈ setup.X, upperEnvelope setup vcoord (fun _ => e0) y ≤ convexRoof setup coe1 y :=
  upperEnvelope_le_convexRoof_on_X setup
    (fun x hx => e0_mem_subderiv hx)
    (fun x hx => by rw [convexRoof_coe1_eq hx, vcoord])

/-! ## Chunk 5b: The dual price is convex -/

/-- **The formula-`S` dual price is convex on `X`** (`pStar_convexOn`): The tangent-envelope
candidate `p*(y) = sup_{x ∈ S} (v x + ∇v(x)·(y − x))` is convex on `X` for a `C¹` value `v` and any
active set `S ⊆ X`. Witnessed at `S = X`. -/
theorem pStar_convexOn_witness :
    ConvexOn ℝ setup.X (pStar vcoord setup.X) :=
  pStar_convexOn setup vcoord_contDiff subset_rfl

/-- **The dual price `p*` equals the value `v` on `X`** (the *majorization-direction* anchor): for
the linear value `vcoord x = x₀` the gradient is constant `∇vcoord = proj₀`, so every tangent
hyperplane `vcoord x + ∇vcoord(x)·(y − x) = x₀ + (y₀ − x₀) = y₀` collapses to the same value `y₀`,
giving `p*(y) = y₀ = vcoord y`. This is the load-bearing `p* ≥ v` direction (here an equality): a
sign flip in the tangent term `∇v(x)·(y − x)` — yielding `x₀ − (y₀ − x₀) = 2x₀ − y₀`, whose sup
over `x₀ ∈ [0,1]` is `max(0, 2 − y₀) ≠ y₀` — would break this. At `y = (1/2,)`: `p*(1/2) = 1/2`. -/
theorem pStar_eq_vcoord_witness {y : EuclideanSpace ℝ (Fin 1)} (hy : y ∈ setup.X) :
    pStar vcoord setup.X y = vcoord y := by
  -- `fderiv ℝ vcoord x = EuclideanSpace.proj 0`, so the tangent value is the constant `y₀`.
  have hfd : ∀ x : EuclideanSpace ℝ (Fin 1),
      fderiv ℝ vcoord x = (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := by
    intro x
    rw [show vcoord = ⇑(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) from by
      funext z; rw [EuclideanSpace.coe_proj]; rfl]
    exact ContinuousLinearMap.fderiv _
  have h_const : (fun x : EuclideanSpace ℝ (Fin 1) =>
      vcoord x + (fderiv ℝ vcoord x) (y - x)) '' setup.X = {y 0} := by
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, rfl⟩
      rw [hfd, EuclideanSpace.coe_proj, vcoord]
      simp only []
      have : (y - x).ofLp 0 = y.ofLp 0 - x.ofLp 0 := by simp
      rw [this]; ring
    · rintro rfl
      exact ⟨y, hy, by rw [hfd, EuclideanSpace.coe_proj, vcoord]; simp⟩
  rw [show pStar vcoord setup.X y = sSup ((fun x : EuclideanSpace ℝ (Fin 1) =>
      vcoord x + (fderiv ℝ vcoord x) (y - x)) '' setup.X) from rfl, h_const, csSup_singleton,
    vcoord]

/-! ## Chunk 5c: The joint ↔ Bayesian round-trip

A Bayes-plausible distribution of posteriors `τ` maps to a feasible joint and back, preserving
Bayes-plausibility in both directions. We anchor `τ` on the full-disclosure meta-distribution `τ_F`
(Dirac posteriors), which is Bayes-plausible for the prior by `isBayesPlausible_tauF`. -/

/-- The full-disclosure meta-distribution over posteriors, Bayes-plausible for the prior. -/
private def tauStar : ProbDist (ProbDist Ω) :=
  Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.tauF setup.prior

private lemma tauStar_bayesPlausible : IsBayesPlausible setup.prior tauStar :=
  isBayesPlausible_tauF setup.prior

/-- **The martingale test integral vanishes on `jointFromBayesian`**
(`jointFromBayesian_martingale`): For every bounded continuous test `φ` and coordinate `i`,
`∫ φ(x)·(m(ω)ᵢ − xᵢ) d(jointFromBayesian) = 0` — the joint's `X`-marginal is the posterior moment
of its `Ω`-section. -/
theorem jointFromBayesian_martingale_witness
    (φ : EuclideanSpace ℝ (Fin 1) → ℝ) (hφ_cont : Continuous φ)
    (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) (i : Fin 1) :
    ∫ p, φ p.1 * (setup.m p.2 i - p.1 i) ∂(jointFromBayesian setup tauStar).toMeasure = 0 :=
  jointFromBayesian_martingale setup tauStar φ hφ_cont hφ_bdd i

/-- **Forward bridge: A Bayes-plausible distribution maps to a feasible joint**
(`isFeasibleJoint_jointFromBayesian`): `jointFromBayesian setup τ_F` satisfies all three
feasibility conditions — `Ω`-marginal recovers the prior, `X`-marginal supported in `X`, martingale
constraint. -/
theorem isFeasibleJoint_jointFromBayesian_witness :
    IsFeasibleJoint setup (jointFromBayesian setup tauStar) :=
  isFeasibleJoint_jointFromBayesian setup tauStar_bayesPlausible

/-- **The joint is the pushforward of the compProd** (`jointFromBayesian_eq_map_compProd`): The
joint factors as `(E_{q.1}[m], q.2)`-pushforward of `τ ⊗ kernelEval`. -/
theorem jointFromBayesian_eq_map_compProd_witness :
    (jointFromBayesian setup tauStar).toMeasure
      = Measure.map (fun q : ProbDist Ω × Ω => (setup.posteriorMoment q.1, q.2))
          (tauStar.toMeasure.compProd (kernelEval Ω)) :=
  jointFromBayesian_eq_map_compProd setup tauStar

/-- **Backward bridge: A feasible joint maps to a Bayes-plausible distribution**
(`isBayesPlausible_bayesianFromJoint`): Disintegrating a feasible joint over its `X`-marginal
yields a Bayes-plausible distribution of posteriors. Together with the forward bridge this is the
**round-trip preservation of Bayes-plausibility in both directions**. -/
theorem isBayesPlausible_bayesianFromJoint_witness :
    IsBayesPlausible setup.prior
      (bayesianFromJoint setup (jointFromBayesian setup tauStar)) :=
  isBayesPlausible_bayesianFromJoint setup isFeasibleJoint_jointFromBayesian_witness

/-- **Concrete full-disclosure objective anchor on the asymmetric prior** `μ₀ = 1/4·δ₀ + 3/4·δ₁`:
the joint's value `∫ vclamp(x) d(jointFromBayesian setup τ_F)` equals the full-disclosure objective
`∫ ω, vclamp(m(ω)) dμ₀ = 𝔼_{μ₀}[ω] = 3/4`. This exercises the round-trip *numerically* on a
nondegenerate prior (full disclosure splits posteriors into `δ₀, δ₁` with moments `0, 1`, then
averages back to the prior moment `3/4`), catching the prior↔posterior-moment confusion the review
flagged for the degenerate point-mass prior. -/
theorem jointFromBayesian_objective_witness :
    ∫ p, vclamp p.1 ∂(jointFromBayesian setup tauStar).toMeasure = 3 / 4 := by
  -- The joint objective equals the posterior-formulation objective on `τ_F = tauF μ₀`.
  rw [integral_v_fst_jointFromBayesian setup tauStar vclamp_meas vclamp_bdd]
  -- `primalValue (composedValue vclamp) (tauF μ₀) = ∫ ω, composedValue vclamp (δ_ω) dμ₀`.
  rw [show tauStar = Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.tauF setup.prior
      from rfl,
    Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.primalValue_tauF
      composedValue_cont.measurable setup.prior]
  -- `composedValue vclamp (δ_ω) = 𝔼_{δ_ω}[ω] = (ω : ℝ) = coe1 ω`.
  have h_pt : ∀ ω : Ω, setup.composedValue vclamp (MeasureTheory.diracProba ω) = coe1 ω := by
    intro ω
    rw [composedValue_vclamp]
    show ProbDist.expect (MeasureTheory.diracProba ω) coe1 = coe1 ω
    rw [ProbDist.expect, show (MeasureTheory.diracProba ω : ProbDist Ω).toMeasure
        = MeasureTheory.Measure.dirac ω from by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure], integral_dirac]
  rw [show setup.prior = priorDist from rfl,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  exact priorDist_mean

/-! ## Chunk 5d: Top-level optimality — the primal value is attained

We state attainment for the **strictly concave** value `vconc`, not the linear `vclamp`, so the
optimization is genuinely non-degenerate (a maximizer/minimizer confusion would change the value).
The non-degeneracy is then certified concretely: two feasible joints — no disclosure and full
disclosure — yield *distinct* objectives `−9/16` and `−3/4`, a strict Jensen loss. -/

/-- **The moment primal value (strictly concave value) is attained by a feasible joint**
(`exists_optimal_joint`): the supremum defining `momentPrimal setup vconc` is achieved by some
feasible joint. Stated for the strictly concave `vconc` so that the feasible-objective set is
non-singleton (see `momentPrimal_ge_noDisclosure_witness` and `objective_strict_jensen_gap`), making
the maximization direction load-bearing.

All hypotheses are discharged from the concrete instance: `vconc` is globally `2`-Lipschitz,
measurable, bounded in `[−1, 0]`, USC; its composed value `V(μ) = −(𝔼_μ[ω])²` is weak-* continuous
(hence USC) and bounded; the moment map is coordinate-Lipschitz. -/
theorem exists_optimal_joint_witness :
    ∃ pi ∈ feasibleJoint setup, ∫ p, vconc p.1 ∂pi.toMeasure = momentPrimal setup vconc :=
  exists_optimal_joint setup setup_coordLip (L := 2) vconc_lip vconc_meas vconc_bdd
    vconc_usc composedValue_vconc_bdd composedValue_vconc_usc

/-- The no-disclosure meta-distribution `δ_{μ₀}` (Dirac at the prior), Bayes-plausible for `μ₀`. -/
private def noDisclosureMeta : ProbDist (ProbDist Ω) := MeasureTheory.diracProba setup.prior

private lemma noDisclosureMeta_bayesPlausible : IsBayesPlausible setup.prior noDisclosureMeta := by
  intro f
  have hcont : Continuous (fun ν : ProbDist Ω => ProbDist.expect ν f) := by
    simpa [ProbDist.expect] using
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := Ω) f)
  change ∫ ν, ProbDist.expect ν f
      ∂(MeasureTheory.diracProba setup.prior : ProbDist (ProbDist Ω)).toMeasure
      = ProbDist.expect setup.prior f
  rw [show (MeasureTheory.diracProba setup.prior : ProbDist (ProbDist Ω)).toMeasure
      = MeasureTheory.Measure.dirac setup.prior from by
    simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]]
  exact MeasureTheory.integral_dirac' _ _ hcont.stronglyMeasurable

/-- **No-disclosure objective under `vconc` is `−9/16`**: the single posterior is the prior `μ₀`
with mean `3/4`, so the objective is `composedValue vconc μ₀ = −(3/4)² = −9/16`. -/
theorem noDisclosure_objective_vconc_witness :
    ∫ p, vconc p.1 ∂(jointFromBayesian setup noDisclosureMeta).toMeasure = -(9 / 16) := by
  rw [integral_v_fst_jointFromBayesian setup noDisclosureMeta vconc_meas vconc_bdd]
  -- `primalValue (composedValue vconc) (δ_{μ₀}) = composedValue vconc μ₀`.
  rw [show primalValue (setup.composedValue vconc) noDisclosureMeta
      = setup.composedValue vconc setup.prior from by
    unfold primalValue noDisclosureMeta
    rw [show (MeasureTheory.diracProba setup.prior : ProbDist (ProbDist Ω)).toMeasure
        = MeasureTheory.Measure.dirac setup.prior from by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure]]
    exact MeasureTheory.integral_dirac' _ _ composedValue_vconc_cont.stronglyMeasurable]
  rw [composedValue_vconc, show setup.prior = priorDist from rfl, priorDist_mean]
  norm_num

/-- **Full-disclosure objective under `vconc` is `−3/4`**: posteriors split into `δ₀, δ₁` (means
`0, 1`), so the objective is `1/4·(−0²) + 3/4·(−1²) = −3/4`. -/
theorem fullDisclosure_objective_vconc_witness :
    ∫ p, vconc p.1 ∂(jointFromBayesian setup tauStar).toMeasure = -(3 / 4) := by
  rw [integral_v_fst_jointFromBayesian setup tauStar vconc_meas vconc_bdd,
    show tauStar = Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.tauF setup.prior
      from rfl,
    Econlib.MechanismDesign.InformationDesign.Persuasion.Duality.primalValue_tauF
      composedValue_vconc_cont.measurable setup.prior]
  -- `composedValue vconc (δ_ω) = −(coe1 ω)²`.
  have h_pt : ∀ ω : Ω, setup.composedValue vconc (MeasureTheory.diracProba ω)
      = -(coe1 ω) ^ 2 := by
    intro ω
    rw [composedValue_vconc]
    congr 2
    show ProbDist.expect (MeasureTheory.diracProba ω) coe1 = coe1 ω
    rw [ProbDist.expect, show (MeasureTheory.diracProba ω : ProbDist Ω).toMeasure
        = MeasureTheory.Measure.dirac ω from by
      simp [MeasureTheory.diracProba, ProbabilityMeasure.toMeasure], integral_dirac]
  rw [show setup.prior = priorDist from rfl,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  -- `∫ ω, −(coe1 ω)² dμ₀ = 1/4·(−0²) + 3/4·(−1²) = −3/4`.
  rw [show priorDist = ProbDist.finMixture priorWeights priorComponents from rfl]
  rw [show (∫ ω, -(coe1 ω) ^ 2 ∂(ProbDist.finMixture priorWeights priorComponents).toMeasure)
      = ProbDist.expect (ProbDist.finMixture priorWeights priorComponents)
          (fun ω => -(coe1 ω) ^ 2) from rfl,
    ProbDist.expect_finMixture priorWeights priorComponents (fun ω => -(coe1 ω) ^ 2)
      (fun i => by
        have : Continuous (fun ω : Ω => -(coe1 ω) ^ 2) := (coe1_cont.pow 2).neg
        exact (this.comp continuous_id).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)),
    Fin.sum_univ_two]
  change priorWeights.pmf 0 * ProbDist.expect (priorComponents 0) (fun ω => -(coe1 ω) ^ 2)
      + priorWeights.pmf 1 * ProbDist.expect (priorComponents 1) (fun ω => -(coe1 ω) ^ 2)
      = -(3 / 4)
  rw [show priorComponents 0 = ProbDist.dirac pt0 from rfl,
    show priorComponents 1 = ProbDist.dirac pt1 from rfl,
    ProbDist.expect_dirac, ProbDist.expect_dirac]
  change (1 / 4 : ℝ) * (-(coe1 pt0) ^ 2) + (3 / 4 : ℝ) * (-(coe1 pt1) ^ 2) = -(3 / 4)
  norm_num [coe1, pt0, pt1]

/-- **The moment primal value (strictly concave value) is bounded below by the no-disclosure
objective `−9/16`** — `momentPrimal` is a supremum over feasible joints, and the no-disclosure
joint is feasible. Combined with `objective_strict_jensen_gap` this certifies the optimization is
genuine: the maximum is at least the *strictly larger* of two distinct feasible objectives. -/
theorem momentPrimal_ge_noDisclosure_witness :
    -(9 / 16) ≤ momentPrimal setup vconc := by
  -- `-9/16` is the objective of the (feasible) no-disclosure joint, and `momentPrimal` is its sup.
  have h_obj : (-(9 / 16) : ℝ)
      = ∫ p, vconc p.1 ∂(jointFromBayesian setup noDisclosureMeta).toMeasure :=
    noDisclosure_objective_vconc_witness.symm
  have h_feas : jointFromBayesian setup noDisclosureMeta ∈ feasibleJoint setup :=
    isFeasibleJoint_jointFromBayesian setup noDisclosureMeta_bayesPlausible
  -- `momentPrimal` is bounded above (objectives are ≤ the value bound), so `le_csSup` applies.
  have h_bdd : BddAbove {y : ℝ | ∃ π ∈ feasibleJoint setup, y = ∫ p, vconc p.1 ∂π.toMeasure} := by
    obtain ⟨M, hM⟩ := vconc_bdd
    refine ⟨M, ?_⟩
    rintro y ⟨π, _, rfl⟩
    have hint : Integrable (fun p => vconc p.1) π.toMeasure := by
      refine ⟨(vconc_meas.comp measurable_fst).aestronglyMeasurable, ?_⟩
      refine (hasFiniteIntegral_const M).mono' (Filter.Eventually.of_forall fun p => ?_)
      simpa [Real.norm_eq_abs] using hM p.1
    calc ∫ p, vconc p.1 ∂π.toMeasure
        ≤ ∫ _, M ∂π.toMeasure :=
          integral_mono hint (integrable_const _) (fun p => (abs_le.mp (hM p.1)).2)
      _ = M := by simp
  rw [h_obj]
  exact le_csSup h_bdd ⟨jointFromBayesian setup noDisclosureMeta, h_feas, rfl⟩

/-- **Strict Jensen gap: no disclosure strictly beats full disclosure under the concave `vconc`**:
`−3/4 < −9/16`. Both objectives are achieved by genuine feasible joints, so the feasible-objective
set is non-singleton and the `momentPrimal` supremum is a real maximization — a maximizer ↔
minimizer swap would pick `−3/4` instead of (at least) `−9/16`. -/
theorem objective_strict_jensen_gap :
    (∫ p, vconc p.1 ∂(jointFromBayesian setup tauStar).toMeasure)
      < ∫ p, vconc p.1 ∂(jointFromBayesian setup noDisclosureMeta).toMeasure := by
  rw [fullDisclosure_objective_vconc_witness, noDisclosure_objective_vconc_witness]; norm_num

/-! ## Note on what is and is not directly witnessed here

The witnesses above exercise the shared spine — `MomentSetup`, `posteriorMoment`, `feasibleJoint`,
`momentPrimal`, `convexRoof`, `upperEnvelope`, `pStar`, `jointFromBayesian`, `bayesianFromJoint` —
on concrete real numbers, with hand-computed anchors at every chunk:

* convex-roof sandwich: `p̌(y) = upperEnvelope = y₀` and the slope-`1` subgradient (`convexRoof =
  coordinate`, `e₀ ∈ ∂p̌`, both proved, no assumed hypotheses);
* dual price: `p*(y) = y₀ = v y` (majorization direction, proved equality);
* joint ↔ Bayesian round-trip on the **asymmetric** prior `μ₀ = 1/4·δ₀ + 3/4·δ₁`, with the
  full-disclosure objective anchored numerically at `3/4`;
* top-level optimality for the **strictly concave** `vconc`, with the maximization certified
  non-degenerate by the strict Jensen gap `−3/4 < −9/16` between two genuine feasible joints.

The deeper dual-price / Bayes-plausible-selector / uniqueness lemmas
(`optimality_implies_pStar_majorizes`, `pbar_eq_pStar_on_active_support`,
`objective_eq_pStar_integral_of_conditionM`, `unique_optimal_joint_bayesPlausible`,
`exists_bayesPlausibleSelector_of_optimal_joint`, and the `ExtremePoints/*` /
`AuxiliaryOptimization/*` decls) are **not** restated here. Each consumes a *structured-price*
bundle (`HasMomentPrices`, `IsDualFeasible`, a.e. complementary slackness, `IsOpenPosMeasure`,
moment-image density) or the *differentiability-genericity* bundle
(`MomentSetup.IsDifferentiable`). Discharging those bundles
concretely amounts to reconstructing the optimal-dual-price machinery itself — their own source
proofs are the honest non-vacuous consumers, verified by the build. This file makes **no** claim of
exercising them transitively; it witnesses the reachable surface directly. -/

end EconlibTest.MechanismDesign.PersuasionMoment

end
