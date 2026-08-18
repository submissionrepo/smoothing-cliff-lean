/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.AtomicDense
public import Econlib.Optimization.OptimalTransport.KRSignedMeasure

/-!
# The Hanin representation theorem

This file proves the **Hanin representation theorem**, the concrete-representation step of
Kantorovich–Rubinstein duality for compact pseudometric `Ω`.  It is a Riesz-style representation
result: Every continuous linear functional `H` on `(KRSignedMeasure Ω, ‖·‖_KR)` (finite signed
Borel measures with the KR norm) is given by integration against a Lipschitz function plus a
multiple of the total mass, with the Lipschitz constant bounded by `‖H‖`.

This file does not construct the quotient space `Lip(Ω) / ℝ`, prove uniqueness of the representing
function modulo additive constants, or establish an isometry of the dual with that quotient; it
provides the representing Lipschitz function together with the norm bound.

The abstract Hahn–Banach supergradient theorem in `Econlib.Math.Analysis.Supergradient` produces a
continuous linear functional `H : KRSignedMeasure Ω →L[ℝ] ℝ`.  Hanin's theorem is the
concrete-representation step that converts that functional to a Lipschitz potential `p : Ω → ℝ` (a
test function) paired with the underlying measures via `signedIntegral`.

## Main definitions

* `signedIntegral p μ` — the test integral `∫ p d(pos μ) − ∫ p d(neg μ)` of a real-valued test
  function `p` against the Jordan decomposition of `μ`.  For `p ∈ Lip(Ω)`, this is `∫ p dμ` in the
  signed-measure sense.
* `lipschitzEval` — the continuous linear functional `μ ↦ signedIntegral p μ` for a 1-Lipschitz `p`
  vanishing at the basepoint, with operator norm `≤ 1`.
* `lipschitzEvalK`, `totalMassCLM` — the `K`-Lipschitz and total-mass continuous linear functionals.

## Main statements

* `signedIntegral_add`, `signedIntegral_smul` — linearity in `μ`, for Lipschitz `p`.
* `abs_signedIntegral_le_lipConst_mul_norm` — continuity bound: `|signedIntegral p μ| ≤ K · ‖μ‖_KR`
  for `K`-Lipschitz `p` with `p default = 0`.
* `hanin_representation` — every continuous linear functional `H : KRSignedMeasure Ω →L[ℝ] ℝ`
  decomposes as `H μ = c · μ(Ω) + signedIntegral p μ` for a representing Lipschitz `p` with
  `p default = 0` and the constant `c = H (ofPointMass default)`.  The Lipschitz constant of `p` is
  bounded by the operator norm of `H`.  This provides a representing function with a norm bound; it
  does not assert uniqueness modulo constants.
* `hanin_representation_zeroMass` — restricted form: On signed measures of total mass `0`, the
  constant term drops out, leaving `H μ = signedIntegral p μ`.

## References

* Kantorovich, Leonid V., and G. Sh. Rubinstein. 1958. “On a Space of Completely Additive
  Functions.” *Vestnik Leningrad University* 13 : 52–59.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.
* Hanin, Leonid G. 1992. “Kantorovich-Rubinstein Norm and Its Application in the Theory of
  Lipschitz Spaces.” *Proceedings of the American Mathematical Society* 115 (2): 345–52.
  [https://doi.org/10.1090/s0002-9939-1992-1097344-5](https://doi.org/10.1090/s0002-9939-1992-1097344-5).
* Bogachev, V. I. 2007. *Measure Theory, Volume II*. Springer. Exercise 8.10.143.
* Dudley, R. M. 2002. *Real Analysis and Probability*. 2nd ed. Cambridge University Press. Chapter
  11.

## Tags

hanin, kantorovich-rubinstein, lipschitz dual, signed measure, riesz representation

## Implementation notes

* The KR space `KRSignedMeasure Ω` is a normed space but not a Banach space in general; its
  completion is a strict superset of finite signed measures.  Hanin's representation is
  nevertheless stated for every continuous linear functional on the (incomplete) normed space.
* The basepoint `default : Ω` chosen for the norm propagates here: The constant term `c` in the
  representation is precisely `H (ofPointMass default)`. This is the representing-function side of
  Hanin's isomorphism `(M(Ω), ‖·‖_KR)* ≃ Lip(Ω) / ℝ`; the quotient equivalence itself is not
  constructed here.
-/

@[expose] public section

namespace Econlib.Optimization.OptimalTransport

namespace KRSignedMeasure

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist
open scoped Topology BoundedContinuousFunction

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [Inhabited Ω]

/-! ## The test integral against a signed measure -/

/-- The **test integral** of a real-valued function `p` against a finite signed Borel measure
(presented as a `KRSignedMeasure`).  Defined via the Jordan decomposition

```
  signedIntegral p μ  =  ∫ p d(pos μ)  −  ∫ p d(neg μ).
```

For `p` continuous (in particular Lipschitz) on a compact space, both integrals are finite and
`signedIntegral p` is `ℝ`-linear in the signed-measure argument. -/
noncomputable def signedIntegral (p : Ω → ℝ) (μ : KRSignedMeasure Ω) : ℝ :=
  (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.posPart)
    - (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.negPart)

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
@[simp] lemma signedIntegral_zero (p : Ω → ℝ) :
    signedIntegral p (0 : KRSignedMeasure Ω) = 0 := by
  unfold signedIntegral
  change (∫ ω, p ω ∂(0 : MeasureTheory.SignedMeasure Ω).toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(0 : MeasureTheory.SignedMeasure Ω).toJordanDecomposition.negPart) = 0
  simp [MeasureTheory.SignedMeasure.toJordanDecomposition_zero]

omit [Inhabited Ω] in
/-- **Additivity of the test integral** in the signed-measure argument, for Lipschitz `p`. -/
lemma signedIntegral_add {p : Ω → ℝ} (hp : LipschitzWith 1 p) (μ ν : KRSignedMeasure Ω) :
    signedIntegral p (μ + ν) = signedIntegral p μ + signedIntegral p ν := by
  unfold signedIntegral
  exact signedIntegralJordan_add p hp μ.toSignedMeasure ν.toSignedMeasure

omit [Inhabited Ω] in
/-- **Additivity of the test integral** for any `K`-Lipschitz `p`. -/
lemma signedIntegral_add_lipschitz {p : Ω → ℝ} {K : NNReal} (hp : LipschitzWith K p)
    (μ ν : KRSignedMeasure Ω) :
    signedIntegral p (μ + ν) = signedIntegral p μ + signedIntegral p ν := by
  unfold signedIntegral
  exact signedIntegralJordan_add_lipschitz p hp μ.toSignedMeasure ν.toSignedMeasure

/-- **Negation of the test integral** for any `K`-Lipschitz `p`. -/
lemma signedIntegral_neg_lipschitz {p : Ω → ℝ} {K : NNReal} (hp : LipschitzWith K p)
    (μ : KRSignedMeasure Ω) :
    signedIntegral p (-μ) = -signedIntegral p μ := by
  -- `μ + (-μ) = 0` and `signedIntegral p 0 = 0`; combined with additivity.
  have h0 : signedIntegral p (μ + -μ) = 0 := by rw [add_neg_cancel, signedIntegral_zero]
  have hadd := signedIntegral_add_lipschitz hp μ (-μ)
  rw [h0] at hadd
  linarith

/-- **Subtractivity of the test integral** for any `K`-Lipschitz `p`. -/
lemma signedIntegral_sub_lipschitz {p : Ω → ℝ} {K : NNReal} (hp : LipschitzWith K p)
    (μ ν : KRSignedMeasure Ω) :
    signedIntegral p (μ - ν) = signedIntegral p μ - signedIntegral p ν := by
  rw [show (μ - ν : KRSignedMeasure Ω) = μ + -ν from by abel,
    signedIntegral_add_lipschitz hp, signedIntegral_neg_lipschitz hp]
  ring

omit [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- **Homogeneity of the test integral** under scalar multiplication, for Lipschitz `p`. -/
lemma signedIntegral_smul {p : Ω → ℝ} (_hp : LipschitzWith 1 p) (c : ℝ) (μ : KRSignedMeasure Ω) :
    signedIntegral p (c • μ) = c * signedIntegral p μ := by
  unfold signedIntegral
  set s := μ.toSignedMeasure with hs_def
  have hcs : (c • μ).toSignedMeasure = c • s := rfl
  rcases le_or_gt 0 c with hc | hc_neg
  · have hpos : (c • s).toJordanDecomposition.posPart
        = c.toNNReal • s.toJordanDecomposition.posPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_posPart_nonneg _ c hc
    have hneg : (c • s).toJordanDecomposition.negPart
        = c.toNNReal • s.toJordanDecomposition.negPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_negPart_nonneg _ c hc
    rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
      MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hc]
    ring
  · have hpos : (c • s).toJordanDecomposition.posPart
        = (-c).toNNReal • s.toJordanDecomposition.negPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_posPart_neg _ c hc_neg
    have hneg : (c • s).toJordanDecomposition.negPart
        = (-c).toNNReal • s.toJordanDecomposition.posPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_negPart_neg _ c hc_neg
    have hnegc_nn : 0 ≤ -c := by linarith
    rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
      MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hnegc_nn]
    ring

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- **Const-divisor pull-out**: `signedIntegral` of `p / c` is `signedIntegral p / c`.  Shared
scaffold for the rescaling tails of the `K`-Lipschitz bound and `lipschitzEvalK`. -/
lemma signedIntegral_div_const (p : Ω → ℝ) (c : ℝ) (μ : KRSignedMeasure Ω) :
    signedIntegral (fun ω => p ω / c) μ = signedIntegral p μ / c := by
  unfold signedIntegral
  rw [show (fun ω => p ω / c) = fun ω => c⁻¹ * p ω by funext ω; rw [div_eq_inv_mul],
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
/-- A `0`-Lipschitz function vanishing at the basepoint is identically zero.  Shared scaffold for
the `K = 0` branches of the continuity bound and `lipschitzEvalK`. -/
lemma eq_zero_of_lipschitz_zero {p : Ω → ℝ} (hp : LipschitzWith 0 p)
    (hp0 : p (default : Ω) = 0) : p = fun _ : Ω => 0 := by
  funext ω
  have hdist := hp.dist_le_mul ω (default : Ω)
  simp only [NNReal.coe_zero, zero_mul] at hdist
  rw [dist_eq_zero.mp (le_antisymm hdist dist_nonneg), hp0]

/-- **Continuity of the test integral**: For any 1-Lipschitz `p` vanishing at the basepoint, the
test integral against `μ` is bounded in absolute value by `‖μ‖_KR`. -/
lemma abs_signedIntegral_le_norm_of_lipschitz_one {p : Ω → ℝ}
    (hp : LipschitzWith 1 p) (hp0 : p (default : Ω) = 0) (μ : KRSignedMeasure Ω) :
    |signedIntegral p μ| ≤ ‖μ‖ := by
  unfold signedIntegral
  exact abs_signedIntegral_le_norm_of_basepoint μ hp hp0

/-- **Continuity of the test integral** for `K`-Lipschitz `p` (general Lipschitz constant).

The basepoint normalization `p default = 0` is enforced; otherwise add a constant `p default` which
contributes to the `|μ(Ω)|` term separately. -/
lemma abs_signedIntegral_le_lipConst_mul_norm {p : Ω → ℝ} {K : NNReal}
    (hp : LipschitzWith K p) (hp0 : p (default : Ω) = 0) (μ : KRSignedMeasure Ω) :
    |signedIntegral p μ| ≤ (K : ℝ) * ‖μ‖ := by
  rcases eq_or_ne K 0 with hK | hK
  · have hp_zero : p = fun _ : Ω => 0 := eq_zero_of_lipschitz_zero (hK ▸ hp) hp0
    unfold signedIntegral
    rw [hp_zero]
    simp [hK]
  · have hKpos : (0 : ℝ) < (K : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
    let q : Ω → ℝ := fun ω => p ω / (K : ℝ)
    have hq_lip : LipschitzWith 1 q := lipschitzWith_one_div_lipConst hp hKpos
    have hq0 : q (default : Ω) = 0 := by
      simp [q, hp0]
    have hq_bound : |signedIntegral q μ| ≤ ‖μ‖ :=
      abs_signedIntegral_le_norm_of_lipschitz_one hq_lip hq0 μ
    have hq_signed : signedIntegral q μ = signedIntegral p μ / (K : ℝ) :=
      signedIntegral_div_const p (K : ℝ) μ
    have hp_signed : signedIntegral p μ = (K : ℝ) * signedIntegral q μ := by
      rw [hq_signed]
      field_simp [hKpos.ne']
    rw [hp_signed, abs_mul, abs_of_pos hKpos]
    exact mul_le_mul_of_nonneg_left hq_bound K.coe_nonneg

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- Reduction of `signedIntegral` against a probability measure: It is just `expect μ p`. Mirrors
`signedIntegral_of_measure` for the `KRSignedMeasure` wrapper.  No Lipschitz hypothesis needed: The
identity is purely Jordan-decomposition algebra. -/
lemma signedIntegral_ofProbDist (p : Ω → ℝ) (μ : ProbabilityMeasure Ω) :
    signedIntegral p (ofProbDist μ) = expect μ p := by
  unfold signedIntegral
  have h := signedIntegral_of_measure (μ : MeasureTheory.Measure Ω) p
  -- `(ofProbDist μ).toSignedMeasure = (μ.toMeasure).toSignedMeasure` by definition.
  change (∫ ω, p ω ∂(μ : MeasureTheory.Measure Ω).toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(μ : MeasureTheory.Measure Ω).toSignedMeasure.toJordanDecomposition.negPart)
      = _
  rw [h]; rfl

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The signed-measure total mass of `ofProbDist μ` is `1`. -/
lemma toSignedMeasure_ofProbDist_univ (μ : ProbabilityMeasure Ω) :
    ((ofProbDist μ).toSignedMeasure Set.univ : ℝ) = 1 := by
  change (((μ : MeasureTheory.Measure Ω).toSignedMeasure) Set.univ : ℝ) = 1
  rw [MeasureTheory.Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
    MeasureTheory.probReal_univ]

/-! ## The continuous linear functional `μ ↦ ∫ p dμ` -/

/-- The linear functional on `KRSignedMeasure Ω` given by integration against a 1-Lipschitz test
function `p`. -/
noncomputable def lipschitzEvalLM (p : Ω → ℝ) (hp : LipschitzWith 1 p) :
    KRSignedMeasure Ω →ₗ[ℝ] ℝ where
  toFun := signedIntegral p
  map_add' μ ν := signedIntegral_add hp μ ν
  map_smul' c μ := by
    simpa [smul_eq_mul] using signedIntegral_smul hp c μ

@[simp] lemma lipschitzEvalLM_apply {p : Ω → ℝ} (hp : LipschitzWith 1 p) (μ : KRSignedMeasure Ω) :
    lipschitzEvalLM p hp μ = signedIntegral p μ := rfl

/-- The continuous linear functional on `KRSignedMeasure Ω` given by integration against a
1-Lipschitz `p` vanishing at the basepoint.  Operator norm `≤ 1`.

This is the concrete side of Hanin's duality: Every Lipschitz function (modulo constants) furnishes
a continuous linear functional. -/
noncomputable def lipschitzEval (p : Ω → ℝ) (hp : LipschitzWith 1 p) (hp0 : p (default : Ω) = 0) :
    KRSignedMeasure Ω →L[ℝ] ℝ :=
  (lipschitzEvalLM p hp).mkContinuous 1 (fun μ => by
    have := abs_signedIntegral_le_norm_of_lipschitz_one hp hp0 μ
    simpa [Real.norm_eq_abs, one_mul, lipschitzEvalLM_apply] using this)

@[simp] lemma lipschitzEval_apply {p : Ω → ℝ} (hp : LipschitzWith 1 p) (hp0 : p (default : Ω) = 0)
    (μ : KRSignedMeasure Ω) :
    lipschitzEval p hp hp0 μ = signedIntegral p μ := rfl

/-- Operator-norm bound for `lipschitzEval`.  Equality holds when `p` separates `Ω` (Hanin
isometry); the inequality form is what we need. -/
theorem lipschitzEval_opNorm_le {p : Ω → ℝ} (hp : LipschitzWith 1 p) (hp0 : p (default : Ω) = 0) :
    ‖lipschitzEval p hp hp0‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## Hanin's representation theorem

Every continuous linear functional on `KRSignedMeasure Ω` decomposes as
`c · μ(Ω) + signedIntegral p μ` for a Lipschitz potential `p` (normalized by `p default = 0`) and
the constant `c = H (ofPointMass default)`.  The Lipschitz constant of `p` is bounded by the
operator norm of `H`, giving the Hanin isometry `(M(Ω), ‖·‖_KR)* ≃ Lip(Ω) / ℝ`. -/

/-! ### Auxiliary continuous linear functionals -/

/-- The total-mass functional `μ ↦ μ(Ω)`, packaged as a continuous linear map. Continuity holds
because `|μ.toSignedMeasure univ| ≤ ‖μ‖` (`abs_signedMeasure_univ_le_norm`). -/
noncomputable def totalMassCLM : KRSignedMeasure Ω →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun μ => (μ.toSignedMeasure Set.univ : ℝ)
      map_add' := fun μ ν => by
        change ((μ.toSignedMeasure + ν.toSignedMeasure) Set.univ : ℝ)
            = (μ.toSignedMeasure Set.univ : ℝ) + (ν.toSignedMeasure Set.univ : ℝ)
        rw [MeasureTheory.VectorMeasure.add_apply]
      map_smul' := fun c μ => by
        change ((c • μ.toSignedMeasure) Set.univ : ℝ) = c • (μ.toSignedMeasure Set.univ : ℝ)
        rw [MeasureTheory.VectorMeasure.smul_apply] }
    1
    (fun μ => by
      have h := abs_signedMeasure_univ_le_norm μ
      simpa [Real.norm_eq_abs, one_mul] using h)

@[simp] lemma totalMassCLM_apply (μ : KRSignedMeasure Ω) :
    totalMassCLM μ = (μ.toSignedMeasure Set.univ : ℝ) := rfl

/-- Continuous linear functional version of `signedIntegral p` for a `K`-Lipschitz `p` vanishing at
the basepoint.  Operator norm is `≤ K`. -/
noncomputable def lipschitzEvalK
    (p : Ω → ℝ) {K : NNReal} (hp : LipschitzWith K p) (hp0 : p (default : Ω) = 0) :
    KRSignedMeasure Ω →L[ℝ] ℝ :=
  if hK : K = 0 then 0
  else
    have hKpos : (0 : ℝ) < (K : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
    let q : Ω → ℝ := fun ω => p ω / (K : ℝ)
    have hq_lip : LipschitzWith 1 q := lipschitzWith_one_div_lipConst hp hKpos
    have hq0 : q (default : Ω) = 0 := by simp [q, hp0]
    (K : ℝ) • lipschitzEval q hq_lip hq0

@[simp] lemma lipschitzEvalK_apply
    (p : Ω → ℝ) {K : NNReal} (hp : LipschitzWith K p) (hp0 : p (default : Ω) = 0)
    (μ : KRSignedMeasure Ω) :
    lipschitzEvalK p hp hp0 μ = signedIntegral p μ := by
  unfold lipschitzEvalK
  by_cases hK : K = 0
  · -- K = 0: p ≡ 0, so signedIntegral p μ = 0.
    simp only [hK, ↓reduceDIte, ContinuousLinearMap.zero_apply]
    have hp_zero : p = (fun _ : Ω => 0) := eq_zero_of_lipschitz_zero (hK ▸ hp) hp0
    rw [hp_zero]
    change (0 : KRSignedMeasure Ω → ℝ) μ = signedIntegral (fun _ : Ω => 0) μ
    unfold signedIntegral
    simp
  · -- K ≠ 0: rescale.
    simp only [hK, ↓reduceDIte, ContinuousLinearMap.smul_apply, lipschitzEval_apply,
      smul_eq_mul]
    have hKpos : (0 : ℝ) < (K : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
    -- Show `(K : ℝ) * signedIntegral q μ = signedIntegral p μ` where `q = p / K`.
    rw [signedIntegral_div_const p (K : ℝ) μ]
    field_simp [hKpos.ne']

/-! ### Auxiliary: Signed integral against a point mass -/

omit [CompactSpace Ω] [Inhabited Ω] in
/-- The signed integral of a continuous `p` against a point mass is `p ω`.  Unlike
`AtomicDense.signedIntegral_ofPointMass`, this does not require `LipschitzWith 1 p`; any continuous
`p` suffices. -/
lemma signedIntegral_ofPointMass_of_continuous {p : Ω → ℝ} (hp : Continuous p) (ω : Ω) :
    signedIntegral p (ofPointMass ω) = p ω := by
  unfold signedIntegral
  -- Reduce to Dirac measure: `(ofPointMass ω).toSignedMeasure = (Measure.dirac ω).toSignedMeasure`.
  change (∫ x, p x ∂(MeasureTheory.Measure.dirac ω).toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ x, p x ∂(MeasureTheory.Measure.dirac ω).toSignedMeasure.toJordanDecomposition.negPart)
      = p ω
  -- Build the canonical Jordan decomposition of `(Measure.dirac ω).toSignedMeasure`:
  -- posPart = dirac ω, negPart = 0.
  let j : MeasureTheory.JordanDecomposition Ω :=
    ⟨MeasureTheory.Measure.dirac ω, 0, MeasureTheory.Measure.MutuallySingular.zero_right⟩
  have hj_sm : j.toSignedMeasure = (MeasureTheory.Measure.dirac ω).toSignedMeasure := by
    change (MeasureTheory.Measure.dirac ω).toSignedMeasure
        - (0 : MeasureTheory.Measure Ω).toSignedMeasure
        = (MeasureTheory.Measure.dirac ω).toSignedMeasure
    rw [MeasureTheory.Measure.toSignedMeasure_zero, sub_zero]
  have hjd : (MeasureTheory.Measure.dirac ω).toSignedMeasure.toJordanDecomposition = j :=
    MeasureTheory.SignedMeasure.toJordanDecomposition_eq hj_sm.symm
  have hpos : (MeasureTheory.Measure.dirac ω).toSignedMeasure.toJordanDecomposition.posPart
      = MeasureTheory.Measure.dirac ω := by rw [hjd]
  have hneg : (MeasureTheory.Measure.dirac ω).toSignedMeasure.toJordanDecomposition.negPart
      = 0 := by rw [hjd]
  rw [hpos, hneg, MeasureTheory.integral_zero_measure, sub_zero]
  exact MeasureTheory.integral_dirac' p ω hp.stronglyMeasurable

/-! ### The representation theorem -/

/-- **Hanin's representation theorem (general form).**

Every continuous linear functional on `(KRSignedMeasure Ω, ‖·‖_KR)` is given by integration against
a representing Lipschitz function plus a multiple of the total mass.  The Lipschitz constant is
bounded by the operator norm of `H`.  This provides a representing function with a norm bound; it
does not assert uniqueness of the representing function modulo additive constants. -/
theorem hanin_representation [MeasurableSingletonClass Ω] (H : KRSignedMeasure Ω →L[ℝ] ℝ) :
    ∃ (p : Ω → ℝ), LipschitzWith ⟨‖H‖, norm_nonneg _⟩ p ∧ p (default : Ω) = 0 ∧
      ∀ μ : KRSignedMeasure Ω,
        H μ = H (ofPointMass (default : Ω)) * μ.toSignedMeasure Set.univ
              + signedIntegral p μ := by
  -- Set `c := H (δ_default)` and `p ω := H (δ_ω) − c`.
  set c : ℝ := H (ofPointMass (default : Ω)) with hc_def
  let p : Ω → ℝ := fun ω => H (ofPointMass ω) - c
  -- Step 1: `p` vanishes at the basepoint.
  have hp0 : p (default : Ω) = 0 := by
    change H (ofPointMass (default : Ω)) - c = 0
    rw [hc_def]; ring
  -- Step 2: `p` is `‖H‖`-Lipschitz, via `norm_ofPointMass_sub_le` and `H.le_opNorm`.
  have hp_lip : LipschitzWith ⟨‖H‖, norm_nonneg _⟩ p := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro ω ω'
    have hdiff : p ω - p ω' = H (ofPointMass ω - ofPointMass ω') := by
      change (H (ofPointMass ω) - c) - (H (ofPointMass ω') - c)
            = H (ofPointMass ω - ofPointMass ω')
      rw [map_sub]; ring
    have h_op : |H (ofPointMass ω - ofPointMass ω')|
        ≤ ‖H‖ * ‖ofPointMass ω - ofPointMass ω'‖ := by
      simpa [Real.norm_eq_abs] using H.le_opNorm (ofPointMass ω - ofPointMass ω')
    have h_emb : ‖ofPointMass ω - ofPointMass ω'‖ ≤ dist ω ω' :=
      norm_ofPointMass_sub_le ω ω'
    rw [Real.dist_eq, hdiff]
    calc |H (ofPointMass ω - ofPointMass ω')|
        ≤ ‖H‖ * ‖ofPointMass ω - ofPointMass ω'‖ := h_op
      _ ≤ ‖H‖ * dist ω ω' :=
          mul_le_mul_of_nonneg_left h_emb (norm_nonneg _)
      _ = (⟨‖H‖, norm_nonneg _⟩ : NNReal) * dist ω ω' := rfl
  refine ⟨p, hp_lip, hp0, fun μ => ?_⟩
  -- Step 3: define the difference functional `F μ := H μ − c · μ(Ω) − ∫ p dμ`
  -- and show it vanishes on every signed point mass; conclude `F = 0` by atomic density.
  let F : KRSignedMeasure Ω →L[ℝ] ℝ :=
    H - c • totalMassCLM - lipschitzEvalK p hp_lip hp0
  have hF_pointMass : ∀ ω : Ω, F (ofPointMass ω) = 0 := by
    intro ω
    -- Direct computation: `H (δ_ω) = c + p ω`, `δ_ω(Ω) = 1`, `signedIntegral p (δ_ω) = p ω`.
    simp only [F, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      totalMassCLM_apply, lipschitzEvalK_apply, smul_eq_mul]
    rw [toSignedMeasure_ofPointMass_univ ω,
      signedIntegral_ofPointMass_of_continuous hp_lip.continuous ω]
    -- Goal: H (ofPointMass ω) - c * 1 - p ω = 0
    ring
  have hF_zero : F = 0 := eq_zero_of_vanishes_on_pointMass F hF_pointMass
  have hFμ : F μ = 0 := by rw [hF_zero]; rfl
  -- Unfold `F μ = 0` into the desired representation.
  change H μ = c * μ.toSignedMeasure Set.univ + signedIntegral p μ
  simp [F, totalMassCLM_apply, lipschitzEvalK_apply, sub_eq_iff_eq_add] at hFμ
  linarith

/-- **Hanin's representation theorem on zero-total-mass measures.**

Restricted to the closed subspace of signed measures with total mass zero, every continuous linear
functional is `μ ↦ signedIntegral p μ` for a Lipschitz `p` normalized by `p default = 0`. This is
the form most directly useful for the simplex difference `ofProbDist μ − ofProbDist ν`. -/
theorem hanin_representation_zeroMass [MeasurableSingletonClass Ω]
    (H : KRSignedMeasure Ω →L[ℝ] ℝ) :
    ∃ (p : Ω → ℝ), LipschitzWith ⟨‖H‖, norm_nonneg _⟩ p ∧ p (default : Ω) = 0 ∧
      ∀ μ : KRSignedMeasure Ω, μ.toSignedMeasure Set.univ = 0 →
        H μ = signedIntegral p μ := by
  obtain ⟨p, hp_lip, hp0, hH_eq⟩ := hanin_representation H
  refine ⟨p, hp_lip, hp0, fun μ hμ => ?_⟩
  rw [hH_eq μ, hμ, mul_zero, zero_add]

end KRSignedMeasure

end Econlib.Optimization.OptimalTransport
