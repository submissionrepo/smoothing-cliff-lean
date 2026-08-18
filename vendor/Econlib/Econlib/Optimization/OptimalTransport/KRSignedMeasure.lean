/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.KantorovichRubinstein
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Kantorovich–Rubinstein normed space of signed measures

This file equips the space `M(Ω)` of finite signed Borel measures on a compact pseudometric space
`Ω` with the **Kantorovich–Rubinstein norm**, making it a real normed vector space.  The
probability simplex `ProbabilityMeasure Ω` embeds into this space as a closed convex subset, and
the norm of `μ − ν` for two probability measures coincides with the existing `krDist μ ν`.

Following Hanin (1992), we use the basepoint formulation: Fix `ω₀ ∈ Ω` and define

```
  ‖μ‖_KR  :=  |μ(Ω)|  +  sup { ∫ p dμ : p ∈ Lip₁(Ω), p(ω₀) = 0 }.
```

The supremum on the right is finite because every 1-Lipschitz function vanishing at `ω₀` is bounded
in absolute value by `diam Ω` on the compact space `Ω`, and `μ` has finite total variation.
Different choices of basepoint give equivalent norms, and the same norm restricted to
zero-total-mass signed measures.

## Main definitions

* `KRSignedMeasure Ω` — wrapper structure over `MeasureTheory.SignedMeasure Ω`, used to install the
  KR-norm instances without colliding with any total-variation norm Mathlib may attach to signed
  measures.
* `KRSignedMeasure.krNorm` — the Kantorovich–Rubinstein norm.
* `KRSignedMeasure.ofProbDist` — embedding of the probability simplex into the KR normed space.
* `NormedAddCommGroup (KRSignedMeasure Ω)`, `NormedSpace ℝ (KRSignedMeasure Ω)` — the normed
  vector-space instances.

## Main statements

* `KRSignedMeasure.krNorm_indep_basepoint` — on zero-total-mass signed measures the norm is
  independent of the basepoint.
* `KRSignedMeasure.norm_ofProbDist_sub` — `‖ofProbDist μ − ofProbDist ν‖ = krDist μ ν`, recovering
  the project's existing KR distance.
* `KRSignedMeasure.convex_range_ofProbDist`, `KRSignedMeasure.isClosed_range_ofProbDist` — the
  image of the probability simplex is convex and closed.

## Notes

This space supports supergradient and Lipschitz-duality statements for functionals on probability
laws.

## References

* Kantorovich, Leonid V., and G. Sh. Rubinstein. 1958. “On a Space of Completely Additive
  Functions.” *Vestnik Leningrad University* 13 : 52–59.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.
* Hanin, Leonid G. 1992. “Kantorovich-Rubinstein Norm and Its Application in the Theory of
  Lipschitz Spaces.” *Proceedings of the American Mathematical Society* 115 (2): 345–52.
  [https://doi.org/10.1090/s0002-9939-1992-1097344-5](https://doi.org/10.1090/s0002-9939-1992-1097344-5).
* Bogachev, V. I. 2007. *Measure Theory, Volume II*. Springer. Exercise 8.10.143.

## Tags

kantorovich-rubinstein, wasserstein distance, signed measure, normed space, lipschitz dual
-/

@[expose] public section

namespace Econlib.Optimization.OptimalTransport

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist
open scoped Topology BoundedContinuousFunction Pointwise

/-! ## The wrapper type and its vector-space structure

We wrap `MeasureTheory.SignedMeasure Ω` so that we can install the KR norm without conflicting
with any total-variation norm instance provided by Mathlib. -/

/-- The space of finite signed Borel measures on a compact pseudometric space `Ω`, to be equipped
with the Kantorovich–Rubinstein norm. -/
structure KRSignedMeasure (Ω : Type*) [MeasurableSpace Ω] where
  /-- The underlying signed measure. -/
  toSignedMeasure : MeasureTheory.SignedMeasure Ω

namespace KRSignedMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

@[ext]
theorem ext {μ ν : KRSignedMeasure Ω}
    (h : μ.toSignedMeasure = ν.toSignedMeasure) : μ = ν := by
  cases μ; cases ν; congr

/-! ### Underlying algebraic structure

The data instances `Zero, Add, Neg, Sub, SMul ℕ, SMul ℤ, SMul ℝ` are projected through
`toSignedMeasure`; with these in place the `AddCommGroup` and `Module ℝ` instances follow from
`Function.Injective.addCommGroup` and `Function.Injective.module`. -/

instance : Zero (KRSignedMeasure Ω) := ⟨⟨0⟩⟩
instance : Add (KRSignedMeasure Ω) := ⟨fun μ ν => ⟨μ.toSignedMeasure + ν.toSignedMeasure⟩⟩
instance : Neg (KRSignedMeasure Ω) := ⟨fun μ => ⟨-μ.toSignedMeasure⟩⟩
instance : Sub (KRSignedMeasure Ω) := ⟨fun μ ν => ⟨μ.toSignedMeasure - ν.toSignedMeasure⟩⟩
instance : SMul ℕ (KRSignedMeasure Ω) := ⟨fun n μ => ⟨n • μ.toSignedMeasure⟩⟩
instance : SMul ℤ (KRSignedMeasure Ω) := ⟨fun n μ => ⟨n • μ.toSignedMeasure⟩⟩
noncomputable instance : SMul ℝ (KRSignedMeasure Ω) := ⟨fun c μ => ⟨c • μ.toSignedMeasure⟩⟩

instance : AddCommGroup (KRSignedMeasure Ω) :=
  Function.Injective.addCommGroup KRSignedMeasure.toSignedMeasure
    (fun _ _ h => ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable instance : Module ℝ (KRSignedMeasure Ω) :=
  Function.Injective.module ℝ
    { toFun := KRSignedMeasure.toSignedMeasure
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    (fun _ _ h => ext h) (fun _ _ => rfl)

/-! ## The Kantorovich–Rubinstein norm -/

variable [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
/-- Subtracting a constant preserves a Lipschitz constant. -/
lemma lipschitzWith_sub_const {p : Ω → ℝ} {K : NNReal} (hp : LipschitzWith K p) (c : ℝ) :
    LipschitzWith K (fun ω => p ω - c) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simpa [Real.dist_eq, sub_sub_sub_cancel_right] using hp.dist_le_mul a b

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
/-- Dividing a `K`-Lipschitz function by `K > 0` gives a 1-Lipschitz function. -/
lemma lipschitzWith_one_div_lipConst {p : Ω → ℝ} {K : NNReal} (hp : LipschitzWith K p)
    (hKpos : (0 : ℝ) < (K : ℝ)) : LipschitzWith 1 (fun ω => p ω / (K : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have hdist := hp.dist_le_mul a b
  have hq_dist : dist (p a / (K : ℝ)) (p b / (K : ℝ)) = dist (p a) (p b) / (K : ℝ) := by
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hKpos]
  rw [hq_dist, div_le_iff₀ hKpos]
  simpa [mul_comm] using hdist

/-- The KR norm of a finite signed Borel measure (Hanin 1992 form):

```
  ‖μ‖_KR  =  |μ(Ω)|  +  sup { ∫ p dμ : p ∈ Lip₁(Ω), p ω₀ = 0 },
```

where the integral against the signed measure `μ.toSignedMeasure` is taken with respect to its
Jordan decomposition.  On a compact space the supremum is finite, and the resulting norm is
independent of `ω₀` up to the constant-shift ambiguity that the `|μ(Ω)|` term absorbs. -/
noncomputable def krNorm (ω₀ : Ω) (μ : KRSignedMeasure Ω) : ℝ :=
  let s := μ.toSignedMeasure
  let pos := s.toJordanDecomposition.posPart
  let neg := s.toJordanDecomposition.negPart
  |s Set.univ| +
  sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
    x = (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)}

/-- On signed measures of total mass zero, the KR norm is independent of the basepoint.

Without the zero-total-mass hypothesis the basepoint matters: E.g. for `Ω = [0,1]` and `μ = δ_0`,
`krNorm 0 μ = 1` while `krNorm 1 μ = 2`. The shift `p ↦ p − p ω₁` only preserves `∫ p ds` when
`s(Ω) = 0`. -/
theorem krNorm_indep_basepoint (ω₀ ω₁ : Ω) (μ : KRSignedMeasure Ω)
    (hμ : μ.toSignedMeasure Set.univ = 0) :
    krNorm ω₀ μ = krNorm ω₁ μ := by
  -- Replacing `p` by `p − p ω₁` keeps the Lipschitz constant and shifts
  -- `∫ p dμ` by `p ω₁ · μ(univ) = 0`, so the two sup-sets coincide.
  set s := μ.toSignedMeasure with hs_def
  set pos := s.toJordanDecomposition.posPart with hpos_def
  set neg := s.toJordanDecomposition.negPart with hneg_def
  -- Total-mass identity: `s univ = pos.real univ - neg.real univ`.
  have hposneg : (pos.real Set.univ : ℝ) - neg.real Set.univ = 0 := by
    have hsum : s.toJordanDecomposition.toSignedMeasure = s :=
      MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s
    have happ : (s Set.univ : ℝ) = pos.real Set.univ - neg.real Set.univ := by
      have := MeasureTheory.Measure.toSignedMeasure_sub_apply
        (μ := pos) (ν := neg) (i := (Set.univ : Set Ω)) MeasurableSet.univ
      -- `s = pos.toSignedMeasure - neg.toSignedMeasure` by definition of
      -- `JordanDecomposition.toSignedMeasure`, combined with `hsum`.
      have hdef : s = pos.toSignedMeasure - neg.toSignedMeasure := hsum.symm
      rw [hdef]; exact this
    linarith [happ, hμ]
  -- Helper: every 1-Lipschitz `p` is integrable against the finite measures
  -- `pos` and `neg` (continuous on a compact space ⇒ bounded continuous).
  have hp_int : ∀ p : Ω → ℝ, LipschitzWith 1 p →
      MeasureTheory.Integrable p pos ∧ MeasureTheory.Integrable p neg :=
    fun p hp => by
      have hp_cont : Continuous p := hp.continuous
      let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp_cont⟩
      refine ⟨pBCF.integrable pos, pBCF.integrable neg⟩
  -- It suffices to show the two sup-sets are equal.
  have hset_eq :
      {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
        x = (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)}
      = {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₁ = 0 ∧
        x = (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)} := by
    ext x
    constructor
    · rintro ⟨p, hp_lip, _hp0, hxeq⟩
      -- Shift by `p ω₁`: `q := p - p ω₁` has `q ω₁ = 0`, is 1-Lipschitz, and
      -- `(∫ q dpos) - (∫ q dneg) = (∫ p dpos) - (∫ p dneg) - p ω₁ · (s univ) = …`.
      refine ⟨fun ω => p ω - p ω₁, ?_, ?_, ?_⟩
      · exact lipschitzWith_sub_const hp_lip (p ω₁)
      · simp
      · obtain ⟨hp_int_pos, hp_int_neg⟩ := hp_int p hp_lip
        have hint_pos :
            (∫ ω, p ω - p ω₁ ∂pos) = (∫ ω, p ω ∂pos) - p ω₁ * pos.real Set.univ := by
          rw [MeasureTheory.integral_sub hp_int_pos (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
        have hint_neg :
            (∫ ω, p ω - p ω₁ ∂neg) = (∫ ω, p ω ∂neg) - p ω₁ * neg.real Set.univ := by
          rw [MeasureTheory.integral_sub hp_int_neg (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
        rw [hint_pos, hint_neg, hxeq]
        have hzero : p ω₁ * (pos.real Set.univ - neg.real Set.univ) = 0 := by
          rw [hposneg]; ring
        linarith [hzero]
    · rintro ⟨p, hp_lip, _hp0, hxeq⟩
      -- Symmetric direction: shift by `p ω₀`.
      refine ⟨fun ω => p ω - p ω₀, ?_, ?_, ?_⟩
      · exact lipschitzWith_sub_const hp_lip (p ω₀)
      · simp
      · obtain ⟨hp_int_pos, hp_int_neg⟩ := hp_int p hp_lip
        have hint_pos :
            (∫ ω, p ω - p ω₀ ∂pos) = (∫ ω, p ω ∂pos) - p ω₀ * pos.real Set.univ := by
          rw [MeasureTheory.integral_sub hp_int_pos (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
        have hint_neg :
            (∫ ω, p ω - p ω₀ ∂neg) = (∫ ω, p ω ∂neg) - p ω₀ * neg.real Set.univ := by
          rw [MeasureTheory.integral_sub hp_int_neg (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
        rw [hint_pos, hint_neg, hxeq]
        have hzero : p ω₀ * (pos.real Set.univ - neg.real Set.univ) = 0 := by
          rw [hposneg]; ring
        linarith [hzero]
  -- Combine: both summands of `krNorm` agree.
  change |s Set.univ| + sSup _ = |s Set.univ| + sSup _
  rw [hset_eq]

end KRSignedMeasure

/-! ## Norm and vector-space instances

The norm is registered through Mathlib's `AddGroupNorm.toNormedAddCommGroup`, which takes an
`AddGroupNorm` (a fully-written record whose `toFun` is `krNorm` and whose Prop fields encode the
norm axioms) and packages it as a `NormedAddCommGroup` instance. -/

namespace KRSignedMeasure

variable {Ω : Type*} [MeasurableSpace Ω]
  [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω]

/-! ### Helper lemmas for the norm axioms -/

omit [Inhabited Ω] in
/-- Every 1-Lipschitz function `p` is integrable with respect to any finite measure on a compact
space (it is bounded continuous). -/
lemma integrable_of_lipschitz (p : Ω → ℝ) (hp : LipschitzWith 1 p)
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.Integrable p μ := by
  let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp.continuous⟩
  exact pBCF.integrable μ

omit [MeasurableSpace Ω] [BorelSpace Ω] [Inhabited Ω] in
/-- Pointwise bound on a 1-Lipschitz function vanishing at a basepoint, on a compact space:
`|p ω| ≤ Metric.diam Set.univ`. -/
lemma abs_le_diam_of_lipschitz_basepoint {p : Ω → ℝ} (hp : LipschitzWith 1 p)
    {ω₀ : Ω} (hp0 : p ω₀ = 0) (ω : Ω) :
    |p ω| ≤ Metric.diam (Set.univ : Set Ω) := by
  have hbdd : Bornology.IsBounded (Set.univ : Set Ω) := by
    rw [Bornology.isBounded_univ]; infer_instance
  have hdist : dist (p ω) (p ω₀) ≤ 1 * dist ω ω₀ := hp.dist_le_mul ω ω₀
  have hduniv : dist ω ω₀ ≤ Metric.diam (Set.univ : Set Ω) :=
    Metric.dist_le_diam_of_mem hbdd (Set.mem_univ _) (Set.mem_univ _)
  have : |p ω| = dist (p ω) (p ω₀) := by
    rw [hp0, Real.dist_eq, sub_zero]
  rw [this]
  linarith [hdist, hduniv]

omit [Inhabited Ω] in
/-- Generalized version: For `K`-Lipschitz `p`, the test integral is additive in the signed
measure.  The Lipschitz constant is only used to ensure integrability against the finite measures
appearing in the Jordan decompositions. -/
lemma signedIntegralJordan_add_lipschitz (p : Ω → ℝ) {K : NNReal} (hp : LipschitzWith K p)
    (s s' : MeasureTheory.SignedMeasure Ω) :
    (∫ ω, p ω ∂(s + s').toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(s + s').toJordanDecomposition.negPart) =
    ((∫ ω, p ω ∂s.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toJordanDecomposition.negPart))
    + ((∫ ω, p ω ∂s'.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s'.toJordanDecomposition.negPart)) := by
  set p₁ := s.toJordanDecomposition.posPart
  set n₁ := s.toJordanDecomposition.negPart
  set p₂ := s'.toJordanDecomposition.posPart
  set n₂ := s'.toJordanDecomposition.negPart
  set p₀ := (s + s').toJordanDecomposition.posPart
  set n₀ := (s + s').toJordanDecomposition.negPart
  have hs : p₁.toSignedMeasure - n₁.toSignedMeasure = s :=
    MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s
  have hs' : p₂.toSignedMeasure - n₂.toSignedMeasure = s' :=
    MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s'
  have hsum : p₀.toSignedMeasure - n₀.toSignedMeasure = s + s' :=
    MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition (s + s')
  have hSM_eq :
      (p₀ + n₁ + n₂).toSignedMeasure = (n₀ + p₁ + p₂).toSignedMeasure := by
    rw [MeasureTheory.Measure.toSignedMeasure_add,
      MeasureTheory.Measure.toSignedMeasure_add,
      MeasureTheory.Measure.toSignedMeasure_add,
      MeasureTheory.Measure.toSignedMeasure_add]
    have hcomb : p₀.toSignedMeasure - n₀.toSignedMeasure
        = (p₁.toSignedMeasure - n₁.toSignedMeasure)
          + (p₂.toSignedMeasure - n₂.toSignedMeasure) := by
      rw [hs, hs']; exact hsum
    linear_combination (norm := abel) hcomb
  have hMeas_eq : (p₀ + n₁ + n₂ : MeasureTheory.Measure Ω) = n₀ + p₁ + p₂ :=
    (MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff).mp hSM_eq
  -- Integrability of `p` against any finite measure on a compact space, via the bounded
  -- continuous packaging.
  have hp_int : ∀ (m : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure m],
      MeasureTheory.Integrable p m := by
    intro m _
    let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp.continuous⟩
    exact pBCF.integrable m
  have hp_p₀ : MeasureTheory.Integrable p p₀ := hp_int _
  have hp_n₀ : MeasureTheory.Integrable p n₀ := hp_int _
  have hp_p₁ : MeasureTheory.Integrable p p₁ := hp_int _
  have hp_n₁ : MeasureTheory.Integrable p n₁ := hp_int _
  have hp_p₂ : MeasureTheory.Integrable p p₂ := hp_int _
  have hp_n₂ : MeasureTheory.Integrable p n₂ := hp_int _
  have hLHS : (∫ ω, p ω ∂(p₀ + n₁ + n₂))
      = (∫ ω, p ω ∂p₀) + (∫ ω, p ω ∂n₁) + (∫ ω, p ω ∂n₂) := by
    rw [MeasureTheory.integral_add_measure (hp_p₀.add_measure hp_n₁) hp_n₂,
      MeasureTheory.integral_add_measure hp_p₀ hp_n₁]
  have hRHS : (∫ ω, p ω ∂(n₀ + p₁ + p₂))
      = (∫ ω, p ω ∂n₀) + (∫ ω, p ω ∂p₁) + (∫ ω, p ω ∂p₂) := by
    rw [MeasureTheory.integral_add_measure (hp_n₀.add_measure hp_p₁) hp_p₂,
      MeasureTheory.integral_add_measure hp_n₀ hp_p₁]
  have hint_eq :
      (∫ ω, p ω ∂(p₀ + n₁ + n₂)) = (∫ ω, p ω ∂(n₀ + p₁ + p₂)) := by
    rw [hMeas_eq]
  rw [hLHS, hRHS] at hint_eq
  linarith [hint_eq]

omit [Inhabited Ω] in
/-- The "test integral" `J(s, p) := ∫p dpos(s) - ∫p dneg(s)` is additive in the signed measure `s`,
for any 1-Lipschitz test function `p`. -/
lemma signedIntegralJordan_add (p : Ω → ℝ) (hp : LipschitzWith 1 p)
    (s s' : MeasureTheory.SignedMeasure Ω) :
    (∫ ω, p ω ∂(s + s').toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(s + s').toJordanDecomposition.negPart) =
    ((∫ ω, p ω ∂s.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toJordanDecomposition.negPart))
    + ((∫ ω, p ω ∂s'.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s'.toJordanDecomposition.negPart)) :=
  -- Special case `K = 1` of the general additivity lemma.
  signedIntegralJordan_add_lipschitz p hp s s'

omit [Inhabited Ω] in
/-- The set of test integrals `S(μ) := { J(s_μ, p) : p ∈ Lip₁, p ω₀ = 0 }` is bounded above by
`D * pos.real univ + D * neg.real univ`, where `D := Metric.diam Set.univ`. -/
lemma bddAbove_krNorm_set (ω₀ : Ω) (s : MeasureTheory.SignedMeasure Ω) :
    BddAbove {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} := by
  set pos := s.toJordanDecomposition.posPart
  set neg := s.toJordanDecomposition.negPart
  set D := Metric.diam (Set.univ : Set Ω)
  refine ⟨D * pos.real Set.univ + D * neg.real Set.univ, ?_⟩
  rintro x ⟨p, hp_lip, hp0, rfl⟩
  have hp_int_pos : MeasureTheory.Integrable p pos := integrable_of_lipschitz p hp_lip pos
  have hp_int_neg : MeasureTheory.Integrable p neg := integrable_of_lipschitz p hp_lip neg
  -- Bound `∫ p dpos ≤ ∫ |p| dpos ≤ ∫ D dpos = D * pos.real univ`.
  have hbound_pos : (∫ ω, p ω ∂pos) ≤ D * pos.real Set.univ := by
    have h1 : (∫ ω, p ω ∂pos) ≤ ∫ ω, |p ω| ∂pos := by
      calc (∫ ω, p ω ∂pos) ≤ |∫ ω, p ω ∂pos| := le_abs_self _
        _ ≤ ∫ ω, |p ω| ∂pos := MeasureTheory.abs_integral_le_integral_abs
    have h2 : (∫ ω, |p ω| ∂pos) ≤ ∫ _, D ∂pos := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const D) ?_
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · exact Filter.Eventually.of_forall
          (fun ω => abs_le_diam_of_lipschitz_basepoint hp_lip hp0 ω)
    have h3 : (∫ _, D ∂pos) = D * pos.real Set.univ := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.measureReal_def, mul_comm]
    linarith [h1, h2, h3]
  -- Bound `-∫ p dneg ≤ ∫ |p| dneg ≤ D * neg.real univ`.
  have hbound_neg : -(∫ ω, p ω ∂neg) ≤ D * neg.real Set.univ := by
    have h1 : -(∫ ω, p ω ∂neg) ≤ ∫ ω, |p ω| ∂neg := by
      calc -(∫ ω, p ω ∂neg) ≤ |∫ ω, p ω ∂neg| := neg_le_abs _
        _ ≤ ∫ ω, |p ω| ∂neg := MeasureTheory.abs_integral_le_integral_abs
    have h2 : (∫ ω, |p ω| ∂neg) ≤ ∫ _, D ∂neg := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ (MeasureTheory.integrable_const D) ?_
      · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
      · exact Filter.Eventually.of_forall
          (fun ω => abs_le_diam_of_lipschitz_basepoint hp_lip hp0 ω)
    have h3 : (∫ _, D ∂neg) = D * neg.real Set.univ := by
      rw [MeasureTheory.integral_const]
      simp [MeasureTheory.measureReal_def, mul_comm]
    linarith [h1, h2, h3]
  linarith [hbound_pos, hbound_neg]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The "metric-distance bump" `g(K, F) x := max 0 (1 - K * Metric.infDist x F)` is `K`-Lipschitz
on a metric space. Used as a Lipschitz approximation to the indicator of a closed set. -/
lemma lipschitz_metricBump (K : NNReal) (F : Set Ω) :
    LipschitzWith K (fun x : Ω => max 0 (1 - (K : ℝ) * Metric.infDist x F)) := by
  have h_inf : LipschitzWith 1 (fun x : Ω => Metric.infDist x F) :=
    Metric.lipschitz_infDist_pt F
  have h_mul : LipschitzWith K (fun x : Ω => (K : ℝ) * Metric.infDist x F) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have hab : dist (Metric.infDist a F) (Metric.infDist b F) ≤ 1 * dist a b :=
      h_inf.dist_le_mul a b
    have hd : dist ((K : ℝ) * Metric.infDist a F) ((K : ℝ) * Metric.infDist b F)
        = (K : ℝ) * dist (Metric.infDist a F) (Metric.infDist b F) := by
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg K.coe_nonneg]
    rw [hd]
    have := mul_le_mul_of_nonneg_left hab K.coe_nonneg
    linarith
  -- `1 - K * infDist · F` is K-Lipschitz: subtracting from a constant preserves Lipschitz.
  have h_sub : LipschitzWith K (fun x : Ω => 1 - (K : ℝ) * Metric.infDist x F) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have h := h_mul.dist_le_mul a b
    have hd : dist (1 - (K : ℝ) * Metric.infDist a F) (1 - (K : ℝ) * Metric.infDist b F)
        = dist ((K : ℝ) * Metric.infDist a F) ((K : ℝ) * Metric.infDist b F) := by
      rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm]
    rw [hd]; exact h
  -- `max 0` preserves Lipschitz constant.
  exact h_sub.const_max 0

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The metric-distance bump is bounded by 1. -/
lemma metricBump_le_one (K : NNReal) (F : Set Ω) (x : Ω) :
    max 0 (1 - (K : ℝ) * Metric.infDist x F) ≤ 1 := by
  rcases le_or_gt 0 (1 - (K : ℝ) * Metric.infDist x F) with h | h
  · simp only [max_eq_right h, tsub_le_iff_right, le_add_iff_nonneg_right]
    have : 0 ≤ (K : ℝ) * Metric.infDist x F :=
      mul_nonneg K.coe_nonneg Metric.infDist_nonneg
    linarith
  · simp [max_eq_left h.le]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The metric-distance bump is nonneg. -/
lemma metricBump_nonneg (K : NNReal) (F : Set Ω) (x : Ω) :
    0 ≤ max 0 (1 - (K : ℝ) * Metric.infDist x F) := le_max_left _ _

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- On a closed set `F`, the metric-distance bump equals 1. -/
lemma metricBump_eq_one_of_mem (K : NNReal) {F : Set Ω} {x : Ω} (hx : x ∈ F) :
    max 0 (1 - (K : ℝ) * Metric.infDist x F) = 1 := by
  rw [Metric.infDist_zero_of_mem hx]
  simp

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- Outside a closed set `F`, the metric-distance bump tends to 0 as the Lipschitz constant grows
(taking K = n along the natural numbers). -/
lemma tendsto_metricBump_of_notMem {F : Set Ω} (hF : IsClosed F) (hFne : F.Nonempty)
    {x : Ω} (hx : x ∉ F) :
    Filter.Tendsto
      (fun n : ℕ => max 0 (1 - (n : ℝ) * Metric.infDist x F))
      Filter.atTop (nhds 0) := by
  have hpos : 0 < Metric.infDist x F := (hF.notMem_iff_infDist_pos hFne).mp hx
  -- `(n : ℝ) * infDist x F → ∞` since `infDist x F > 0`.
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Metric.infDist x F)
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hpos
  -- For all sufficiently large `n`, `1 - n * infDist x F ≤ 0`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ (n : ℝ) * Metric.infDist x F :=
    h1.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hge : 1 ≤ (n : ℝ) * Metric.infDist x F := hN n hn
  have hle : 1 - (n : ℝ) * Metric.infDist x F ≤ 0 := by linarith
  have heq : max 0 (1 - (n : ℝ) * Metric.infDist x F) = 0 := max_eq_left hle
  rw [heq]; simp [hε]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The metric-distance bump converges pointwise to the indicator of a closed set, valued at the
closed set's domain. -/
lemma tendsto_metricBump_to_indicator {F : Set Ω} (hF : IsClosed F) (hFne : F.Nonempty) (x : Ω) :
    Filter.Tendsto (fun n : ℕ => max 0 (1 - (n : ℝ) * Metric.infDist x F))
      Filter.atTop (nhds (F.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ F
  · -- Constant 1.
    rw [Set.indicator_of_mem hx]
    have heq : ∀ n : ℕ, max 0 (1 - (n : ℝ) * Metric.infDist x F) = 1 :=
      fun n => metricBump_eq_one_of_mem (n : NNReal) hx
    simp_rw [heq]
    exact tendsto_const_nhds
  · -- Goes to 0.
    rw [Set.indicator_of_notMem hx]
    exact tendsto_metricBump_of_notMem hF hFne hx

omit [BorelSpace Ω] [CompactSpace Ω] in
/-- The KR norm of the zero signed measure is `0` (the `map_zero'` field of `krAddGroupNorm`). -/
lemma krNorm_map_zero : krNorm (default: Ω) 0 = 0 := by
  have hs : (0 : KRSignedMeasure Ω).toSignedMeasure = 0 := rfl
  have hpos : (0 : KRSignedMeasure Ω).toSignedMeasure.toJordanDecomposition.posPart = 0 := by
    rw [hs, MeasureTheory.SignedMeasure.toJordanDecomposition_zero,
      MeasureTheory.JordanDecomposition.zero_posPart]
  have hneg : (0 : KRSignedMeasure Ω).toSignedMeasure.toJordanDecomposition.negPart = 0 := by
    rw [hs, MeasureTheory.SignedMeasure.toJordanDecomposition_zero,
      MeasureTheory.JordanDecomposition.zero_negPart]
  simp only [krNorm, hs, MeasureTheory.SignedMeasure.toJordanDecomposition_zero,
    MeasureTheory.JordanDecomposition.zero_posPart,
    MeasureTheory.JordanDecomposition.zero_negPart,
    MeasureTheory.VectorMeasure.zero_apply, abs_zero,
    MeasureTheory.integral_zero_measure, sub_zero, zero_add]
  -- The set reduces to `{0}` since every Lipschitz `p` makes `(0 : ℝ) - 0 = 0`.
  have hset : {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧ x = 0}
      = {(0 : ℝ)} := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, _, rfl⟩; rfl
    · rintro rfl
      exact ⟨fun _ => 0, (LipschitzWith.const 0).weaken (by norm_num), rfl, rfl⟩
  rw [hset, csSup_singleton]

/-- Triangle inequality for the KR norm (the `add_le'` field of `krAddGroupNorm`). -/
lemma krNorm_add_le : ∀ (r s : KRSignedMeasure Ω),
    krNorm default (r + s) ≤ krNorm default r + krNorm default s := by
  -- Triangle inequality from sub-additivity of the supremum form.
  intro μ ν
  set sμ := μ.toSignedMeasure with hsμ
  set sν := ν.toSignedMeasure with hsν
  have hsum_def : (μ + ν).toSignedMeasure = sμ + sν := rfl
  -- Abbreviate the three test-integral sets.
  set Sμ : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂sμ.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂sμ.toJordanDecomposition.negPart)} with hSμ
  set Sν : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂sν.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂sν.toJordanDecomposition.negPart)} with hSν
  set Ssum : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂(sμ + sν).toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(sμ + sν).toJordanDecomposition.negPart)} with hSsum
  -- Boundedness of all three sup-sets.
  have hbdd_μ : BddAbove Sμ := bddAbove_krNorm_set (default : Ω) sμ
  have hbdd_ν : BddAbove Sν := bddAbove_krNorm_set (default : Ω) sν
  have hbdd_sum : BddAbove Ssum := bddAbove_krNorm_set (default : Ω) (sμ + sν)
  -- Nonemptiness: `p = 0` is 1-Lipschitz, vanishes at `default`, and contributes `0`.
  have hzero_lip : LipschitzWith 1 (fun _ : Ω => (0 : ℝ)) :=
    (LipschitzWith.const 0).weaken (by norm_num)
  have hne_μ : Sμ.Nonempty := ⟨0, fun _ => 0, hzero_lip, rfl, by simp⟩
  have hne_ν : Sν.Nonempty := ⟨0, fun _ => 0, hzero_lip, rfl, by simp⟩
  -- Nonempty for `Ssum` too.
  have hne_sum : Ssum.Nonempty := ⟨0, fun _ => 0, hzero_lip, rfl, by simp⟩
  -- Key: every `x ∈ Ssum` is bounded by `sSup Sμ + sSup Sν`.
  have hsum_le : sSup Ssum ≤ sSup Sμ + sSup Sν := by
    apply csSup_le hne_sum
    rintro x ⟨p, hp_lip, hp0, rfl⟩
    -- Decompose `J(s_{μ+ν}, p) = J(s_μ, p) + J(s_ν, p)`.
    rw [signedIntegralJordan_add p hp_lip sμ sν]
    -- Each term is `≤ sSup` of its respective set.
    have hJμ : (∫ ω, p ω ∂sμ.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂sμ.toJordanDecomposition.negPart) ∈ Sμ := ⟨p, hp_lip, hp0, rfl⟩
    have hJν : (∫ ω, p ω ∂sν.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂sν.toJordanDecomposition.negPart) ∈ Sν := ⟨p, hp_lip, hp0, rfl⟩
    have hμ_le : (∫ ω, p ω ∂sμ.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂sμ.toJordanDecomposition.negPart) ≤ sSup Sμ := le_csSup hbdd_μ hJμ
    have hν_le : (∫ ω, p ω ∂sν.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂sν.toJordanDecomposition.negPart) ≤ sSup Sν := le_csSup hbdd_ν hJν
    linarith [hμ_le, hν_le]
  -- Part 1: `|s_{μ+ν} univ| ≤ |s_μ univ| + |s_ν univ|`.
  have habs_le :
      |(sμ + sν) Set.univ| ≤ |sμ Set.univ| + |sν Set.univ| := by
    rw [MeasureTheory.VectorMeasure.add_apply]
    exact abs_add_le _ _
  change |(μ + ν).toSignedMeasure Set.univ| + sSup Ssum
      ≤ (|sμ Set.univ| + sSup Sμ) + (|sν Set.univ| + sSup Sν)
  rw [hsum_def]
  linarith [habs_le, hsum_le]

omit [BorelSpace Ω] [CompactSpace Ω] in
/-- The KR norm is invariant under negation (the `neg'` field of `krAddGroupNorm`). -/
lemma krNorm_neg : ∀ (r : KRSignedMeasure Ω), krNorm default (-r) = krNorm default r := by
  intro μ
  set s := μ.toSignedMeasure with hs_def
  have hns : (-μ).toSignedMeasure = -s := rfl
  -- Jordan parts swap under negation.
  have hpos_neg :
      (-s).toJordanDecomposition.posPart = s.toJordanDecomposition.negPart := by
    rw [MeasureTheory.SignedMeasure.toJordanDecomposition_neg,
      MeasureTheory.JordanDecomposition.neg_posPart]
  have hneg_neg :
      (-s).toJordanDecomposition.negPart = s.toJordanDecomposition.posPart := by
    rw [MeasureTheory.SignedMeasure.toJordanDecomposition_neg,
      MeasureTheory.JordanDecomposition.neg_negPart]
  -- The `|·(univ)|` term is unchanged: `|-(s univ)| = |s univ|`.
  have habs : |(-s) Set.univ| = |s Set.univ| := by
    rw [MeasureTheory.VectorMeasure.neg_apply, abs_neg]
  -- The two sup-sets coincide via `p ↔ −p`.
  have hset_eq :
      {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
        x = (∫ ω, p ω ∂(-s).toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂(-s).toJordanDecomposition.negPart)}
      = {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
        x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} := by
    ext x
    constructor
    · rintro ⟨p, hp_lip, hp0, hxeq⟩
      refine ⟨fun ω => -p ω, hp_lip.neg, ?_, ?_⟩
      · simp [hp0]
      · rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg]
        rw [hpos_neg, hneg_neg] at hxeq
        linarith
    · rintro ⟨p, hp_lip, hp0, hxeq⟩
      refine ⟨fun ω => -p ω, hp_lip.neg, ?_, ?_⟩
      · simp [hp0]
      · rw [hpos_neg, hneg_neg]
        rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg]
        linarith
  -- Unfold `(-μ).toSignedMeasure` to `-s` so the rewrites land.
  change |((-μ).toSignedMeasure) Set.univ| +
      sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
        x = (∫ ω, p ω ∂(-μ).toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂(-μ).toSignedMeasure.toJordanDecomposition.negPart)}
      = |s Set.univ| +
      sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
        x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)}
  rw [hns, habs, hset_eq]

/-- A signed measure with zero KR norm is the zero measure (the `eq_zero_of_map_eq_zero'` field of
`krAddGroupNorm`). -/
lemma krNorm_eq_zero_of_map_eq_zero : ∀ (x : KRSignedMeasure Ω),
    krNorm default x = 0 → x = 0  := by
  -- Strategy: from `krNorm μ = 0` we extract two pieces of information:
  --   (a) `s univ = 0` from `|s univ| = 0`;
  --   (b) `J(s, p) := ∫p dpos - ∫p dneg = 0` for all 1-Lipschitz `p` with `p (default) = 0`,
  --       from `sSup S(μ) = 0` plus `0 ∈ S(μ)` plus `p ↔ -p` symmetry.
  -- We then bootstrap (b) to: `J(s, q) = 0` for any Lipschitz `q` (any constant, no basepoint).
  -- Applying this to the metric-distance bumps `g_n F x := max 0 (1 - n * infDist x F)` and
  -- using DCT, we conclude `pos F = neg F` for all closed `F`. By the π-system extension
  -- theorem on the closed sets generating `borel Ω`, `pos = neg`. Finally, mutual singularity
  -- of the Jordan decomposition (`pos ⊥ neg`) combined with `pos = neg` forces `pos = neg = 0`,
  -- hence `s = 0`, hence `μ = 0`.
  intro μ hμ
  set s := μ.toSignedMeasure with hs_def
  set pos := s.toJordanDecomposition.posPart with hpos_def
  set neg := s.toJordanDecomposition.negPart with hneg_def
  -- Decompose `krNorm μ = 0` into the two summands.
  have hkr : |s Set.univ| + sSup {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
      p (default : Ω) = 0 ∧ x = (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)} = 0 := hμ
  -- Both summands are nonneg.
  have habs_nn : 0 ≤ |s Set.univ| := abs_nonneg _
  set S : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)} with hS_def
  have hzero_lip : LipschitzWith 1 (fun _ : Ω => (0 : ℝ)) :=
    (LipschitzWith.const 0).weaken (by norm_num)
  have h0_mem : (0 : ℝ) ∈ S := ⟨fun _ => 0, hzero_lip, rfl, by simp⟩
  have hS_ne : S.Nonempty := ⟨0, h0_mem⟩
  have hS_bdd : BddAbove S := bddAbove_krNorm_set (default : Ω) s
  have hsup_nn : 0 ≤ sSup S := le_csSup hS_bdd h0_mem
  -- Each is zero individually.
  have habs_zero : |s Set.univ| = 0 := by linarith
  have hsup_zero : sSup S = 0 := by linarith
  -- (a) `s univ = 0`.
  have hs_univ : s Set.univ = 0 := abs_eq_zero.mp habs_zero
  -- Convert to `pos.real univ = neg.real univ`.
  have hpos_eq_neg_real : (pos.real Set.univ : ℝ) = neg.real Set.univ := by
    have hsum : s.toJordanDecomposition.toSignedMeasure = s :=
      MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s
    have happ : (s Set.univ : ℝ) = pos.real Set.univ - neg.real Set.univ := by
      have := MeasureTheory.Measure.toSignedMeasure_sub_apply
        (μ := pos) (ν := neg) (i := (Set.univ : Set Ω)) MeasurableSet.univ
      have hdef : s = pos.toSignedMeasure - neg.toSignedMeasure := hsum.symm
      rw [hdef]; exact this
    linarith [happ, hs_univ]
  -- Helper: integrability of any 1-Lipschitz function against `pos`/`neg`.
  have hint_pos : ∀ p : Ω → ℝ, LipschitzWith 1 p → MeasureTheory.Integrable p pos :=
    fun p hp => integrable_of_lipschitz p hp pos
  have hint_neg : ∀ p : Ω → ℝ, LipschitzWith 1 p → MeasureTheory.Integrable p neg :=
    fun p hp => integrable_of_lipschitz p hp neg
  -- Helper: integrability of any K-Lipschitz function against `pos`/`neg`.
  have hint_pos_K : ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p →
      MeasureTheory.Integrable p pos := fun K p hp => by
    let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp.continuous⟩
    exact pBCF.integrable pos
  have hint_neg_K : ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p →
      MeasureTheory.Integrable p neg := fun K p hp => by
    let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp.continuous⟩
    exact pBCF.integrable neg
  -- (b) `J(s, p) ≤ 0` for any 1-Lipschitz `p` with `p (default) = 0`.
  have hJ_le : ∀ p : Ω → ℝ, LipschitzWith 1 p → p (default : Ω) = 0 →
      (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) ≤ 0 := by
    intro p hp_lip hp0
    have hmem : (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) ∈ S := ⟨p, hp_lip, hp0, rfl⟩
    have := le_csSup hS_bdd hmem
    linarith [hsup_zero]
  -- By `p ↔ -p` symmetry, `J(s, p) ≥ 0` too, hence `= 0`.
  have hJ_eq_zero_basepoint : ∀ p : Ω → ℝ, LipschitzWith 1 p → p (default : Ω) = 0 →
      (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) = 0 := by
    intro p hp_lip hp0
    have hupper : (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) ≤ 0 := hJ_le p hp_lip hp0
    -- Apply `hJ_le` to `-p`.
    have hneg_lip : LipschitzWith 1 (fun ω => -p ω) := hp_lip.neg
    have hneg_zero : (fun ω => -p ω) (default : Ω) = 0 := by simp [hp0]
    have hupper_neg :
        (∫ ω, -p ω ∂pos) - (∫ ω, -p ω ∂neg) ≤ 0 := hJ_le _ hneg_lip hneg_zero
    rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg] at hupper_neg
    linarith [hupper, hupper_neg]
  -- Drop the basepoint constraint: for any 1-Lipschitz `p`, `J(s, p) = 0`.
  have hJ_eq_zero_lip1 : ∀ p : Ω → ℝ, LipschitzWith 1 p →
      (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) = 0 := by
    intro p hp_lip
    let q : Ω → ℝ := fun ω => p ω - p (default : Ω)
    have hq_lip : LipschitzWith 1 q := lipschitzWith_sub_const hp_lip (p (default : Ω))
    have hq0 : q (default : Ω) = 0 := by simp [q]
    have hqJ : (∫ ω, q ω ∂pos) - (∫ ω, q ω ∂neg) = 0 := hJ_eq_zero_basepoint q hq_lip hq0
    have hpos_int : MeasureTheory.Integrable p pos := hint_pos p hp_lip
    have hneg_int : MeasureTheory.Integrable p neg := hint_neg p hp_lip
    have hqp_pos : (∫ ω, q ω ∂pos) = (∫ ω, p ω ∂pos) - p (default : Ω) * pos.real Set.univ := by
      change (∫ ω, p ω - p (default : Ω) ∂pos)
          = (∫ ω, p ω ∂pos) - p (default : Ω) * pos.real Set.univ
      rw [MeasureTheory.integral_sub hpos_int (MeasureTheory.integrable_const _)]
      simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
    have hqp_neg : (∫ ω, q ω ∂neg) = (∫ ω, p ω ∂neg) - p (default : Ω) * neg.real Set.univ := by
      change (∫ ω, p ω - p (default : Ω) ∂neg)
          = (∫ ω, p ω ∂neg) - p (default : Ω) * neg.real Set.univ
      rw [MeasureTheory.integral_sub hneg_int (MeasureTheory.integrable_const _)]
      simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
    rw [hqp_pos, hqp_neg] at hqJ
    have : p (default : Ω) * (pos.real Set.univ - neg.real Set.univ) = 0 := by
      rw [hpos_eq_neg_real]; ring
    linarith [hqJ, this]
  -- Scale: for any K-Lipschitz `p`, `J(s, p) = 0`.
  have hJ_eq_zero_lip : ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p →
      (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) = 0 := by
    intro K p hp
    rcases eq_or_ne K 0 with hK | hK
    · -- K = 0: `p` is constant.
      have hp_const : ∀ a b, p a = p b := by
        intro a b
        have := hp.dist_le_mul a b
        rw [hK] at this
        have : dist (p a) (p b) ≤ 0 := by simpa using this
        have habs : dist (p a) (p b) = 0 := le_antisymm this dist_nonneg
        exact (dist_eq_zero.mp habs)
      -- So `p ω = p default` for all ω.
      have hp_eq : (fun ω => p ω) = (fun _ => p (default : Ω)) := by
        funext ω; exact hp_const ω _
      have h_pos_int : (∫ ω, p ω ∂pos) = pos.real Set.univ * p (default : Ω) := by
        rw [hp_eq, MeasureTheory.integral_const]
        simp [MeasureTheory.measureReal_def]
      have h_neg_int : (∫ ω, p ω ∂neg) = neg.real Set.univ * p (default : Ω) := by
        rw [hp_eq, MeasureTheory.integral_const]
        simp [MeasureTheory.measureReal_def]
      rw [h_pos_int, h_neg_int, hpos_eq_neg_real]; ring
    · -- K > 0: scale `p` to `p / K`, which is 1-Lipschitz.
      have hKpos : (0 : ℝ) < (K : ℝ) := by
        have : (0 : NNReal) < K := pos_iff_ne_zero.mpr hK
        exact_mod_cast this
      let q : Ω → ℝ := fun ω => p ω / (K : ℝ)
      have hq_lip : LipschitzWith 1 q := lipschitzWith_one_div_lipConst hp hKpos
      have hqJ : (∫ ω, q ω ∂pos) - (∫ ω, q ω ∂neg) = 0 := hJ_eq_zero_lip1 q hq_lip
      have hp_pos_int := hint_pos_K K p hp
      have hp_neg_int := hint_neg_K K p hp
      have hq_p : (∫ ω, q ω ∂pos) = (∫ ω, p ω ∂pos) / (K : ℝ) := by
        change (∫ ω, p ω / (K : ℝ) ∂pos) = (∫ ω, p ω ∂pos) / (K : ℝ)
        rw [show (fun ω => p ω / (K : ℝ)) = (fun ω => (K : ℝ)⁻¹ * p ω) by
          funext ω; rw [div_eq_inv_mul]]
        rw [MeasureTheory.integral_const_mul, ← div_eq_inv_mul]
      have hq_n : (∫ ω, q ω ∂neg) = (∫ ω, p ω ∂neg) / (K : ℝ) := by
        change (∫ ω, p ω / (K : ℝ) ∂neg) = (∫ ω, p ω ∂neg) / (K : ℝ)
        rw [show (fun ω => p ω / (K : ℝ)) = (fun ω => (K : ℝ)⁻¹ * p ω) by
          funext ω; rw [div_eq_inv_mul]]
        rw [MeasureTheory.integral_const_mul, ← div_eq_inv_mul]
      rw [hq_p, hq_n] at hqJ
      have hsub : ((∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)) / (K : ℝ) = 0 := by
        rw [sub_div]; exact hqJ
      exact (div_eq_zero_iff.mp hsub).resolve_right (ne_of_gt hKpos)
  -- For any closed nonempty set F, the metric bumps `g_n` give `J(s, g_n) = 0`.
  have hJ_bump_zero : ∀ (n : ℕ) (F : Set Ω),
      (∫ ω, max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F) ∂pos)
        - (∫ ω, max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F) ∂neg) = 0 := by
    intro n F
    exact hJ_eq_zero_lip (n : NNReal) _ (lipschitz_metricBump (n : NNReal) F)
  -- For closed `F`, `pos.real F = neg.real F` via DCT.
  have hF_eq_real : ∀ {F : Set Ω}, IsClosed F → pos.real F = neg.real F := by
    intro F hF
    by_cases hFne : F.Nonempty
    · have hFmeas : MeasurableSet F := hF.measurableSet
      -- Define `g_n` and apply DCT.
      let g : ℕ → Ω → ℝ :=
        fun n ω => max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F)
      -- Each `g_n` is bounded by 1, nonneg, continuous.
      have hg_lip : ∀ n : ℕ, LipschitzWith (n : NNReal) (g n) :=
        fun n => lipschitz_metricBump (n : NNReal) F
      have hg_cont : ∀ n : ℕ, Continuous (g n) := fun n => (hg_lip n).continuous
      have hg_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (g n) pos :=
        fun n => (hg_cont n).aestronglyMeasurable
      have hg_meas_neg : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (g n) neg :=
        fun n => (hg_cont n).aestronglyMeasurable
      have hg_le_one : ∀ (n : ℕ) ω, ‖g n ω‖ ≤ 1 := by
        intro n ω
        change ‖max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F)‖ ≤ 1
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (metricBump_nonneg (n : NNReal) F ω)]
        exact metricBump_le_one (n : NNReal) F ω
      have hg_lim : ∀ ω,
          Filter.Tendsto (fun n => g n ω) Filter.atTop
            (nhds (F.indicator (fun _ => (1 : ℝ)) ω)) := by
        intro ω
        change Filter.Tendsto
          (fun n : ℕ => max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F))
          Filter.atTop _
        -- The bump in `tendsto_metricBump_to_indicator` uses `(n : ℝ)` directly; rewrite the
        -- coercion `((n : NNReal) : ℝ) = (n : ℝ)`.
        have hcast : ∀ n : ℕ, ((n : NNReal) : ℝ) = (n : ℝ) := fun n => by
          push_cast; rfl
        simp_rw [hcast]
        exact tendsto_metricBump_to_indicator hF hFne ω
      -- DCT for `pos`.
      have hint_indic_pos :
          Filter.Tendsto (fun n => ∫ ω, g n ω ∂pos) Filter.atTop
            (nhds (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos)) :=
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (bound := fun _ => 1)
          hg_meas (MeasureTheory.integrable_const 1)
          (fun n => Filter.Eventually.of_forall (fun ω => hg_le_one n ω))
          (Filter.Eventually.of_forall hg_lim)
      -- Similarly for `neg`.
      have hint_indic_neg :
          Filter.Tendsto (fun n => ∫ ω, g n ω ∂neg) Filter.atTop
            (nhds (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂neg)) :=
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (bound := fun _ => 1)
          hg_meas_neg (MeasureTheory.integrable_const 1)
          (fun n => Filter.Eventually.of_forall (fun ω => hg_le_one n ω))
          (Filter.Eventually.of_forall hg_lim)
      -- By `hJ_bump_zero`, `∫ g_n dpos = ∫ g_n dneg` for all `n`.
      have hg_eq : ∀ n, (∫ ω, g n ω ∂pos) = (∫ ω, g n ω ∂neg) := by
        intro n
        have := hJ_bump_zero n F
        linarith
      -- Hence the limits agree.
      have hlim_eq : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos)
          = (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂neg) := by
        have hint_indic_pos' :
            Filter.Tendsto (fun n => ∫ ω, g n ω ∂neg) Filter.atTop
              (nhds (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos)) := by
          convert hint_indic_pos using 1
          funext n; exact (hg_eq n).symm
        exact tendsto_nhds_unique hint_indic_pos' hint_indic_neg
      -- Identify `∫ indicator = measureReal`.
      have hpos_indic : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos) = pos.real F := by
        rw [MeasureTheory.integral_indicator hFmeas]
        simp [MeasureTheory.measureReal_def]
      have hneg_indic : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂neg) = neg.real F := by
        rw [MeasureTheory.integral_indicator hFmeas]
        simp [MeasureTheory.measureReal_def]
      rw [hpos_indic, hneg_indic] at hlim_eq
      exact hlim_eq
    · -- F empty.
      rw [Set.not_nonempty_iff_eq_empty] at hFne
      rw [hFne]
      simp [MeasureTheory.measureReal_def]
  -- Convert real-valued equality to ENNReal equality of finite measures.
  have hF_eq : ∀ {F : Set Ω}, IsClosed F → pos F = neg F := by
    intro F hF
    have hpos_lt : pos F ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    have hneg_lt : neg F ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    have hreal := hF_eq_real hF
    simp only [MeasureTheory.measureReal_def] at hreal
    exact (ENNReal.toReal_eq_toReal_iff' hpos_lt hneg_lt).mp hreal
  -- Apply π-system extension on closed sets.
  have hpos_eq_neg : pos = neg := by
    apply MeasureTheory.ext_of_generate_finite (C := {s : Set Ω | IsClosed s})
      (hC := isPiSystem_isClosed)
    · -- `m0 = generateFrom { closed sets }`.
      rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]
    · intro F hF
      exact hF_eq hF
    · exact hF_eq isClosed_univ
  -- Combine `pos = neg` with mutual singularity ⇒ `pos = 0` (and `neg = 0`).
  have hms : pos.MutuallySingular neg := s.toJordanDecomposition.mutuallySingular
  have hms' : pos.MutuallySingular pos := hpos_eq_neg ▸ hms
  have hpos_zero : pos = 0 := (MeasureTheory.Measure.MutuallySingular.self_iff pos).mp hms'
  have hneg_zero : neg = 0 := hpos_eq_neg ▸ hpos_zero
  -- Hence `s = 0`. The Jordan decomposition with both parts zero gives the zero signed measure.
  have hjd_zero : s.toJordanDecomposition = 0 := by
    apply MeasureTheory.JordanDecomposition.ext
    · exact hpos_zero
    · exact hneg_zero
  have hs_zero : s = 0 := by
    have hsum : s.toJordanDecomposition.toSignedMeasure = s :=
      MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition s
    rw [← hsum, hjd_zero, MeasureTheory.JordanDecomposition.toSignedMeasure_zero]
  -- Conclude `μ = 0`.
  apply KRSignedMeasure.ext
  exact hs_zero

/-- The Kantorovich–Rubinstein norm packaged as an `AddGroupNorm`, bundling the basepoint norm
`krNorm default` with its zero, triangle, negation, and definiteness axioms. -/
noncomputable def krAddGroupNorm : AddGroupNorm (KRSignedMeasure Ω) where
  toFun μ := krNorm (default : Ω) μ
  map_zero' := krNorm_map_zero
  add_le' := krNorm_add_le
  neg' := krNorm_neg
  eq_zero_of_map_eq_zero' := krNorm_eq_zero_of_map_eq_zero

/-- The Kantorovich–Rubinstein normed additive group structure on `KRSignedMeasure Ω`, induced by
`krAddGroupNorm`. -/
noncomputable instance : NormedAddCommGroup (KRSignedMeasure Ω) :=
  krAddGroupNorm.toNormedAddCommGroup

/-- The norm on `KRSignedMeasure Ω` is the basepoint KR norm `krNorm default`. -/
theorem norm_def (μ : KRSignedMeasure Ω) :
    ‖μ‖ = krNorm (default : Ω) μ := rfl

omit [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- The test-integral set `S(μ) = { J(s, p) : p ∈ Lip₁, p ω₀ = 0 }` is symmetric under negation:
`x ∈ S(μ) ↔ -x ∈ S(μ)`, since `p ↦ -p` preserves the Lipschitz/basepoint constraints and flips the
sign of the test integral. -/
lemma krNorm_set_neg_mem (ω₀ : Ω) (s : MeasureTheory.SignedMeasure Ω) {x : ℝ}
    (hx : x ∈ {y : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      y = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)}) :
    -x ∈ {y : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      y = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} := by
  obtain ⟨p, hp_lip, hp0, hxeq⟩ := hx
  refine ⟨fun ω => -p ω, hp_lip.neg, ?_, ?_⟩
  · simp [hp0]
  · rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg, hxeq]; ring

omit [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- For `c ≥ 0`, the test-integral set scales: `S(c • μ) = c • S(μ)` as subsets of `ℝ`. -/
lemma krNorm_set_smul_nonneg (ω₀ : Ω) {c : ℝ} (hc : 0 ≤ c) (μ : KRSignedMeasure Ω) :
    {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.negPart)}
      = c • {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.negPart)} := by
  set s := μ.toSignedMeasure with hs_def
  have hcs : (c • μ).toSignedMeasure = c • s := rfl
  -- Pos and neg parts under nonneg scaling.
  have hpos : (c • s).toJordanDecomposition.posPart = c.toNNReal • s.toJordanDecomposition.posPart
      := by
    rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
    exact MeasureTheory.JordanDecomposition.real_smul_posPart_nonneg _ c hc
  have hneg : (c • s).toJordanDecomposition.negPart = c.toNNReal • s.toJordanDecomposition.negPart
      := by
    rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
    exact MeasureTheory.JordanDecomposition.real_smul_negPart_nonneg _ c hc
  ext x
  constructor
  · rintro ⟨p, hp_lip, hp0, hxeq⟩
    refine ⟨(∫ ω, p ω ∂s.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toJordanDecomposition.negPart), ⟨p, hp_lip, hp0, rfl⟩, ?_⟩
    rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
      MeasureTheory.integral_smul_nnreal_measure] at hxeq
    -- `c.toNNReal • r = c.toNNReal.toReal · r = c · r` since `c ≥ 0`.
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hc] at hxeq
    change c • _ = x
    rw [smul_eq_mul, hxeq]; ring
  · rintro ⟨y, ⟨p, hp_lip, hp0, hyeq⟩, hxeq⟩
    refine ⟨p, hp_lip, hp0, ?_⟩
    rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
      MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hc]
    simp only [smul_eq_mul] at hxeq
    rw [← hxeq, hyeq]; ring

omit [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω] in
/-- For `c ≤ 0`, the test-integral set scales: `S(c • μ) = c • S(μ)` as subsets of `ℝ`. The pos/neg
parts of `c • s` swap and pick up the factor `(-c).toNNReal`. -/
lemma krNorm_set_smul_nonpos (ω₀ : Ω) {c : ℝ} (hc : c ≤ 0) (μ : KRSignedMeasure Ω) :
    {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.negPart)}
      = c • {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂μ.toSignedMeasure.toJordanDecomposition.negPart)} := by
  set s := μ.toSignedMeasure with hs_def
  have hcs : (c • μ).toSignedMeasure = c • s := rfl
  rcases eq_or_lt_of_le hc with hc0 | hc_neg
  · -- c = 0.
    subst hc0
    have h_zero : (0 : ℝ) • s = 0 := by simp
    -- Both sides reduce to `{0}` — `0 • S` = `{0}` since `S` is nonempty (contains 0).
    have hzero_lip : LipschitzWith 1 (fun _ : Ω => (0 : ℝ)) :=
      (LipschitzWith.const 0).weaken (by norm_num)
    set S : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
      x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} with hS_def
    have h0_mem_S : (0 : ℝ) ∈ S := ⟨fun _ => 0, hzero_lip, rfl, by simp⟩
    ext x
    constructor
    · rintro ⟨p, _, _, hxeq⟩
      rw [hcs, h_zero, MeasureTheory.SignedMeasure.toJordanDecomposition_zero,
        MeasureTheory.JordanDecomposition.zero_posPart,
        MeasureTheory.JordanDecomposition.zero_negPart] at hxeq
      simp at hxeq
      refine ⟨0, h0_mem_S, ?_⟩
      change (fun y => (0 : ℝ) • y) 0 = x
      simp [hxeq]
    · rintro ⟨y, _, hxeq⟩
      change (fun z => (0 : ℝ) • z) y = x at hxeq
      simp at hxeq
      refine ⟨fun _ => 0, hzero_lip, rfl, ?_⟩
      rw [hcs, h_zero, MeasureTheory.SignedMeasure.toJordanDecomposition_zero,
        MeasureTheory.JordanDecomposition.zero_posPart,
        MeasureTheory.JordanDecomposition.zero_negPart]
      simp [hxeq]
  · -- c < 0.
    have hpos : (c • s).toJordanDecomposition.posPart
        = (-c).toNNReal • s.toJordanDecomposition.negPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_posPart_neg _ c hc_neg
    have hneg : (c • s).toJordanDecomposition.negPart
        = (-c).toNNReal • s.toJordanDecomposition.posPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real]
      exact MeasureTheory.JordanDecomposition.real_smul_negPart_neg _ c hc_neg
    have hnegc_nn : 0 ≤ -c := by linarith
    ext x
    constructor
    · rintro ⟨p, hp_lip, hp0, hxeq⟩
      refine ⟨(∫ ω, p ω ∂s.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂s.toJordanDecomposition.negPart), ⟨p, hp_lip, hp0, rfl⟩, ?_⟩
      rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_smul_nnreal_measure] at hxeq
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hnegc_nn] at hxeq
      change c • _ = x
      rw [smul_eq_mul, hxeq]; ring
    · rintro ⟨y, ⟨p, hp_lip, hp0, hyeq⟩, hxeq⟩
      refine ⟨p, hp_lip, hp0, ?_⟩
      rw [hcs, hpos, hneg, MeasureTheory.integral_smul_nnreal_measure,
        MeasureTheory.integral_smul_nnreal_measure]
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ hnegc_nn]
      simp only [smul_eq_mul] at hxeq
      rw [← hxeq, hyeq]; ring

omit [Inhabited Ω] in
/-- Homogeneity of the KR norm: `krNorm ω₀ (c • μ) = |c| * krNorm ω₀ μ`. -/
lemma krNorm_smul (ω₀ : Ω) (c : ℝ) (μ : KRSignedMeasure Ω) :
    krNorm ω₀ (c • μ) = |c| * krNorm ω₀ μ := by
  set s := μ.toSignedMeasure with hs_def
  have hcs : (c • μ).toSignedMeasure = c • s := rfl
  -- Abbreviate the test-integral sets.
  set S : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
    x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} with hS_def
  set Sc : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p ω₀ = 0 ∧
    x = (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂(c • μ).toSignedMeasure.toJordanDecomposition.negPart)} with hSc_def
  -- Setup: nonemptiness, boundedness.
  have hzero_lip : LipschitzWith 1 (fun _ : Ω => (0 : ℝ)) :=
    (LipschitzWith.const 0).weaken (by norm_num)
  have h0_mem_S : (0 : ℝ) ∈ S := ⟨fun _ => 0, hzero_lip, rfl, by simp⟩
  have hS_ne : S.Nonempty := ⟨0, h0_mem_S⟩
  have hS_bdd : BddAbove S := bddAbove_krNorm_set ω₀ s
  -- Symmetry of `S` under negation, hence `sInf S = -sSup S`.
  have hS_sym : ∀ x ∈ S, -x ∈ S := fun x hx => krNorm_set_neg_mem ω₀ s hx
  -- The `|·univ|` term.
  have habs : |(c • μ).toSignedMeasure Set.univ| = |c| * |s Set.univ| := by
    rw [hcs, MeasureTheory.VectorMeasure.smul_apply, smul_eq_mul, abs_mul]
  -- Case on sign of `c`.
  rcases le_or_gt 0 c with hc | hc
  · -- c ≥ 0.
    have hSc_eq : Sc = c • S := krNorm_set_smul_nonneg ω₀ hc μ
    have hsup_eq : sSup Sc = c * sSup S := by
      rw [hSc_eq, Real.sSup_smul_of_nonneg hc]; rfl
    have habs_c : |c| = c := abs_of_nonneg hc
    change |(c • μ).toSignedMeasure Set.univ| + sSup Sc
      = |c| * (|s Set.univ| + sSup S)
    rw [habs, hsup_eq, habs_c]; ring
  · -- c < 0.
    have hc_le : c ≤ 0 := le_of_lt hc
    have hSc_eq : Sc = c • S := krNorm_set_smul_nonpos ω₀ hc_le μ
    -- `sInf S = -sSup S` from symmetry.
    have hS_bddBelow : BddBelow S := by
      obtain ⟨M, hM⟩ := hS_bdd
      refine ⟨-M, ?_⟩
      intro x hx
      have h_neg_x : -x ∈ S := hS_sym x hx
      have : -x ≤ M := hM h_neg_x
      linarith
    have hSinf : sInf S = -sSup S := by
      apply le_antisymm
      · -- sInf S ≤ -sSup S, i.e. sSup S ≤ -sInf S. Show -sInf S is an upper bound of S.
        have h_upper : ∀ y ∈ S, y ≤ -sInf S := by
          intro y hy
          have h_neg_y : -y ∈ S := hS_sym y hy
          have : sInf S ≤ -y := csInf_le hS_bddBelow h_neg_y
          linarith
        have h1 : sSup S ≤ -sInf S := csSup_le hS_ne h_upper
        linarith
      · -- -sSup S ≤ sInf S: `-sSup S` is a lower bound of S.
        apply le_csInf hS_ne
        intro x hx
        have h_neg_x : -x ∈ S := hS_sym x hx
        have : -x ≤ sSup S := le_csSup hS_bdd h_neg_x
        linarith
    have hsup_eq : sSup Sc = c * (-sSup S) := by
      rw [hSc_eq, Real.sSup_smul_of_nonpos hc_le, hSinf]; rfl
    have habs_c : |c| = -c := abs_of_neg hc
    change |(c • μ).toSignedMeasure Set.univ| + sSup Sc
      = |c| * (|s Set.univ| + sSup S)
    rw [habs, hsup_eq, habs_c]; ring

/-- `(KRSignedMeasure Ω, ‖·‖_KR)` is a real normed vector space. Homogeneity follows from linearity
of integration. -/
noncomputable instance : NormedSpace ℝ (KRSignedMeasure Ω) where
  norm_smul_le c μ := by
    -- `‖c • μ‖ = |c| · ‖μ‖` from linearity of the supremum/integral.
    rw [norm_def, norm_def, krNorm_smul]
    rfl
end KRSignedMeasure

/-! ## Embedding the probability simplex -/

namespace KRSignedMeasure

open MeasureTheory Set
open scoped Topology BoundedContinuousFunction Pointwise

variable {Ω : Type*} [MeasurableSpace Ω]
  [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω]
  [OpensMeasurableSpace Ω]

/-- Embedding of `ProbabilityMeasure Ω` into the KR normed space, via the inclusion of probability
measures into signed measures. -/
noncomputable def ofProbDist (μ : ProbabilityMeasure Ω) : KRSignedMeasure Ω where
  toSignedMeasure := (μ : MeasureTheory.Measure Ω).toSignedMeasure

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω]
  [OpensMeasurableSpace Ω] in
/-- The embedding `ofProbDist : ProbabilityMeasure Ω → KRSignedMeasure Ω` is injective.  Two
probability measures inducing the same signed measure must be equal: Their associated finite
measures coincide (by `Measure.toSignedMeasure_eq_toSignedMeasure_iff`), hence so do the underlying
`ProbabilityMeasure` records. -/
theorem injective_ofProbDist :
    Function.Injective (ofProbDist : ProbabilityMeasure Ω → KRSignedMeasure Ω) := by
  intro μ ν h
  have hsigned : (μ : MeasureTheory.Measure Ω).toSignedMeasure
      = (ν : MeasureTheory.Measure Ω).toSignedMeasure := by
    have := congrArg KRSignedMeasure.toSignedMeasure h
    simpa [ofProbDist] using this
  have hmeasure : (μ : MeasureTheory.Measure Ω) = (ν : MeasureTheory.Measure Ω) :=
    (MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff).mp hsigned
  -- `ProbabilityMeasure` injects into `Measure` via the coercion.
  exact MeasureTheory.ProbabilityMeasure.toMeasure_injective hmeasure

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [Inhabited Ω]
  [OpensMeasurableSpace Ω] in
/-- For a finite measure `m`, the Jordan decomposition of `m.toSignedMeasure` has positive part `m`
and negative part `0`. Hence the test integral `J(m.toSignedMeasure, p)` reduces to `∫ p dm` for
any test function `p`. -/
lemma signedIntegral_of_measure (m : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure m]
    (p : Ω → ℝ) :
    (∫ ω, p ω ∂m.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂m.toSignedMeasure.toJordanDecomposition.negPart) = ∫ ω, p ω ∂m := by
  -- Build the canonical Jordan decomposition for a positive finite measure:
  -- posPart = m, negPart = 0.
  let j : MeasureTheory.JordanDecomposition Ω :=
    ⟨m, 0, MeasureTheory.Measure.MutuallySingular.zero_right⟩
  -- `j.toSignedMeasure = m.toSignedMeasure` since `0.toSignedMeasure = 0`.
  have hj_sm : j.toSignedMeasure = m.toSignedMeasure := by
    change m.toSignedMeasure - (0 : MeasureTheory.Measure Ω).toSignedMeasure = m.toSignedMeasure
    rw [MeasureTheory.Measure.toSignedMeasure_zero, sub_zero]
  -- By uniqueness of the Jordan decomposition, recover `posPart = m`, `negPart = 0`.
  have hjd : m.toSignedMeasure.toJordanDecomposition = j :=
    MeasureTheory.SignedMeasure.toJordanDecomposition_eq hj_sm.symm
  have hpos : m.toSignedMeasure.toJordanDecomposition.posPart = m := by rw [hjd]
  have hneg : m.toSignedMeasure.toJordanDecomposition.negPart = 0 := by rw [hjd]
  rw [hpos, hneg, MeasureTheory.integral_zero_measure, sub_zero]

omit [OpensMeasurableSpace Ω] in
/-- The KR norm of a difference of probability measures coincides with the Kantorovich–Rubinstein
distance defined for `ProbabilityMeasure`. -/
theorem norm_ofProbDist_sub (μ ν : ProbabilityMeasure Ω) :
    ‖ofProbDist μ - ofProbDist ν‖ = krDist μ ν := by
  -- For probability measures the total mass of `μ − ν` is zero, killing
  -- the `|·(Ω)|` term; the remaining supremum is exactly `krDist μ ν` by
  -- definition.
  rw [norm_def]
  -- Abbreviations for the underlying signed measures.
  set sμ : MeasureTheory.SignedMeasure Ω := (μ : MeasureTheory.Measure Ω).toSignedMeasure with hsμ
  set sν : MeasureTheory.SignedMeasure Ω := (ν : MeasureTheory.Measure Ω).toSignedMeasure with hsν
  set s : MeasureTheory.SignedMeasure Ω := sμ - sν with hs_def
  have hs_eq : (ofProbDist μ - ofProbDist ν).toSignedMeasure = s := rfl
  -- Step 1: `|s univ| = 0` because probability measures have total mass 1.
  have hs_univ_zero : s Set.univ = 0 := by
    have h := MeasureTheory.Measure.toSignedMeasure_sub_apply
      (μ := (μ : MeasureTheory.Measure Ω)) (ν := (ν : MeasureTheory.Measure Ω))
      (i := (Set.univ : Set Ω)) MeasurableSet.univ
    rw [hs_def, hsμ, hsν, h, MeasureTheory.probReal_univ, MeasureTheory.probReal_univ, sub_self]
  -- Step 2: identify the test integral against `s` with the difference of expectations.
  have hJ : ∀ p : Ω → ℝ, LipschitzWith 1 p →
      (∫ ω, p ω ∂s.toJordanDecomposition.posPart) - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)
        = expect μ p - expect ν p := by
    intro p hp
    -- Rewrite `s = sμ + (-sν)` and apply additivity (`signedIntegralJordan_add`).
    have hs_add : s = sμ + (-sν) := by rw [hs_def]; abel
    have hadd := signedIntegralJordan_add p hp sμ (-sν)
    rw [← hs_add] at hadd
    -- For `-sν`, `posPart` and `negPart` swap, so `J(-sν, p) = -J(sν, p)`.
    have hneg_pos : (-sν).toJordanDecomposition.posPart = sν.toJordanDecomposition.negPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_neg]; rfl
    have hneg_neg : (-sν).toJordanDecomposition.negPart = sν.toJordanDecomposition.posPart := by
      rw [MeasureTheory.SignedMeasure.toJordanDecomposition_neg]; rfl
    rw [hneg_pos, hneg_neg] at hadd
    -- Replace the Jordan parts of `sμ` and `sν` with the underlying probability measures.
    -- `sμ = (↑μ).toSignedMeasure` is a `let`-bound abbreviation; the `change` below
    -- forces the displayed form so that `signedIntegral_of_measure` applies definitionally.
    have hμ := signedIntegral_of_measure (μ : MeasureTheory.Measure Ω) p
    have hν := signedIntegral_of_measure (ν : MeasureTheory.Measure Ω) p
    change
        (∫ ω, p ω ∂sμ.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂sμ.toJordanDecomposition.negPart) = ∫ ω, p ω ∂(μ : MeasureTheory.Measure Ω)
      at hμ
    change
        (∫ ω, p ω ∂sν.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂sν.toJordanDecomposition.negPart) = ∫ ω, p ω ∂(ν : MeasureTheory.Measure Ω)
      at hν
    -- `expect d p = ∫ x, p x ∂d.toMeasure`.
    change (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)
      = (∫ ω, p ω ∂(μ : MeasureTheory.Measure Ω)) - (∫ ω, p ω ∂(ν : MeasureTheory.Measure Ω))
    linarith [hadd, hμ, hν]
  -- Step 3: the basepointed sup-set equals the unconstrained one (used in `krDist`).
  set Sbase : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂s.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toJordanDecomposition.negPart)} with hSbase
  set Sfree : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧
    x = expect μ p - expect ν p} with hSfree
  have hset_eq : Sbase = Sfree := by
    ext x
    constructor
    · rintro ⟨p, hp_lip, _, rfl⟩
      exact ⟨p, hp_lip, hJ p hp_lip⟩
    · rintro ⟨p, hp_lip, hxeq⟩
      -- Shift by `p default`: define `q ω := p ω - p default`. Then `q ∈ Lip₁`, `q default = 0`.
      have hshift_lip : LipschitzWith 1 (fun ω => p ω - p (default : Ω)) :=
        lipschitzWith_sub_const hp_lip (p (default : Ω))
      refine ⟨fun ω => p ω - p (default : Ω), hshift_lip, ?_, ?_⟩
      · simp
      · -- The integral against `s` is invariant under the constant shift since `s univ = 0`.
        rw [hJ _ hshift_lip]
        -- `expect d (p - c) = expect d p - c` since `d.toMeasure univ = 1`.
        have hp_int_μ : MeasureTheory.Integrable p (μ : MeasureTheory.Measure Ω) :=
          integrable_of_lipschitz p hp_lip _
        have hp_int_ν : MeasureTheory.Integrable p (ν : MeasureTheory.Measure Ω) :=
          integrable_of_lipschitz p hp_lip _
        have hμ_shift :
            expect μ (fun ω => p ω - p (default : Ω))
              = expect μ p - p (default : Ω) := by
          change (∫ ω, p ω - p (default : Ω) ∂(μ : MeasureTheory.Measure Ω))
            = (∫ ω, p ω ∂(μ : MeasureTheory.Measure Ω)) - p (default : Ω)
          rw [MeasureTheory.integral_sub hp_int_μ (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def]
        have hν_shift :
            expect ν (fun ω => p ω - p (default : Ω))
              = expect ν p - p (default : Ω) := by
          change (∫ ω, p ω - p (default : Ω) ∂(ν : MeasureTheory.Measure Ω))
            = (∫ ω, p ω ∂(ν : MeasureTheory.Measure Ω)) - p (default : Ω)
          rw [MeasureTheory.integral_sub hp_int_ν (MeasureTheory.integrable_const _)]
          simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def]
        rw [hμ_shift, hν_shift, hxeq]; ring
  -- Step 4: combine to identify the KR norm with `krDist`.
  change |s Set.univ| + sSup Sbase = krDist μ ν
  rw [hs_univ_zero, abs_zero, zero_add, hset_eq]
  rfl

omit [OpensMeasurableSpace Ω] in
/-- The image of `ProbabilityMeasure Ω` is convex in the KR normed space. -/
theorem convex_range_ofProbDist :
    Convex ℝ (Set.range (ofProbDist (Ω := Ω))) := by
  -- Convex combinations of probability measures are probability measures, and
  -- `ofProbDist` is linear on the affine combination by `Measure.toSignedMeasure_smul`
  -- (with `NNReal` scalars) and `Measure.toSignedMeasure_add`.
  rintro _ ⟨μ₁, rfl⟩ _ ⟨μ₂, rfl⟩ a b ha hb hab
  -- Build the witness probability measure `ν = a • μ₁ + b • μ₂`.
  set m₁ : MeasureTheory.Measure Ω := (μ₁ : MeasureTheory.Measure Ω)
  set m₂ : MeasureTheory.Measure Ω := (μ₂ : MeasureTheory.Measure Ω)
  set aN : NNReal := a.toNNReal with haN_def
  set bN : NNReal := b.toNNReal with hbN_def
  have haN_coe : (aN : ℝ) = a := Real.coe_toNNReal a ha
  have hbN_coe : (bN : ℝ) = b := Real.coe_toNNReal b hb
  set m : MeasureTheory.Measure Ω := aN • m₁ + bN • m₂ with hm_def
  -- `m` is a probability measure: total mass `a · 1 + b · 1 = 1`.
  have hprob : MeasureTheory.IsProbabilityMeasure m := by
    refine ⟨?_⟩
    rw [hm_def, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.smul_apply, MeasureTheory.measure_univ,
      MeasureTheory.measure_univ]
    -- Convert `aN • 1` (NNReal acting on ENNReal) to `(aN : ENNReal)`.
    have hsumNN : aN + bN = 1 := by
      apply NNReal.eq
      rw [NNReal.coe_add, haN_coe, hbN_coe, NNReal.coe_one, hab]
    change (aN : ENNReal) • (1 : ENNReal) + (bN : ENNReal) • (1 : ENNReal) = 1
    rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.coe_add, hsumNN,
      ENNReal.coe_one]
  -- Promote `m` to a `ProbabilityMeasure`.
  refine ⟨⟨m, hprob⟩, ?_⟩
  -- Show equality of KRSignedMeasure via toSignedMeasure.
  apply KRSignedMeasure.ext
  -- LHS: `(ofProbDist ⟨m, hprob⟩).toSignedMeasure = m.toSignedMeasure`.
  -- RHS: `(a • ofProbDist μ₁ + b • ofProbDist μ₂).toSignedMeasure
  --      = a • m₁.toSignedMeasure + b • m₂.toSignedMeasure`.
  change m.toSignedMeasure = a • m₁.toSignedMeasure + b • m₂.toSignedMeasure
  -- Use `toSignedMeasure_add` and `toSignedMeasure_smul` (NNReal version).
  have h₁ : MeasureTheory.IsFiniteMeasure (aN • m₁) := inferInstance
  have h₂ : MeasureTheory.IsFiniteMeasure (bN • m₂) := inferInstance
  have hmsm : m.toSignedMeasure
      = (aN • m₁).toSignedMeasure + (bN • m₂).toSignedMeasure :=
    MeasureTheory.Measure.toSignedMeasure_add (aN • m₁) (bN • m₂)
  rw [hmsm, MeasureTheory.Measure.toSignedMeasure_smul m₁ aN,
    MeasureTheory.Measure.toSignedMeasure_smul m₂ bN]
  -- `(aN : NNReal) • s = ((aN : ℝ)) • s` and likewise for `bN`.
  rw [show (aN • m₁.toSignedMeasure : MeasureTheory.SignedMeasure Ω)
        = (aN : ℝ) • m₁.toSignedMeasure from NNReal.smul_def aN _,
      show (bN • m₂.toSignedMeasure : MeasureTheory.SignedMeasure Ω)
        = (bN : ℝ) • m₂.toSignedMeasure from NNReal.smul_def bN _,
      haN_coe, hbN_coe]

/-! ### Helpers for closedness of the probability simplex -/

omit [OpensMeasurableSpace Ω] in
/-- Pointwise bound `|s univ| ≤ ‖s‖_KR`: The total-mass term is one of the two summands of the KR
norm, and the supremum side is non-negative. -/
lemma abs_signedMeasure_univ_le_norm (s : KRSignedMeasure Ω) :
    |s.toSignedMeasure Set.univ| ≤ ‖s‖ := by
  rw [norm_def]
  -- `krNorm = |s univ| + sSup S`, with `0 ∈ S` (witnessed by `p = 0`), so `sSup S ≥ 0`.
  set S : Set ℝ := {x : ℝ | ∃ p : Ω → ℝ, LipschitzWith 1 p ∧ p (default : Ω) = 0 ∧
    x = (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart)} with hS_def
  have hzero_lip : LipschitzWith 1 (fun _ : Ω => (0 : ℝ)) :=
    (LipschitzWith.const 0).weaken (by norm_num)
  have h0_mem : (0 : ℝ) ∈ S := ⟨fun _ => 0, hzero_lip, rfl, by simp⟩
  have hS_bdd : BddAbove S := bddAbove_krNorm_set (default : Ω) s.toSignedMeasure
  have hsup_nn : 0 ≤ sSup S := le_csSup hS_bdd h0_mem
  change |s.toSignedMeasure Set.univ| ≤ |s.toSignedMeasure Set.univ| + sSup S
  linarith

omit [OpensMeasurableSpace Ω] in
/-- For a 1-Lipschitz `p` with `p default = 0`, the test integral against the limit's signed
measure is bounded by the KR norm: `|J(s, p)| ≤ ‖s‖_KR`. -/
lemma abs_signedIntegral_le_norm_of_basepoint (s : KRSignedMeasure Ω) {p : Ω → ℝ}
    (hp_lip : LipschitzWith 1 p) (hp0 : p (default : Ω) = 0) :
    |((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart))| ≤ ‖s‖ := by
  rw [norm_def]
  set S : Set ℝ := {x : ℝ | ∃ q : Ω → ℝ, LipschitzWith 1 q ∧ q (default : Ω) = 0 ∧
    x = (∫ ω, q ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, q ω ∂s.toSignedMeasure.toJordanDecomposition.negPart)} with hS_def
  have hJ_mem : ((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart)) ∈ S :=
    ⟨p, hp_lip, hp0, rfl⟩
  have hS_bdd : BddAbove S := bddAbove_krNorm_set (default : Ω) s.toSignedMeasure
  -- Symmetry: `-J(s, p)` also lies in `S` (replace `p` with `-p`).
  have hJ_neg_mem : -((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart)) ∈ S :=
    krNorm_set_neg_mem (default : Ω) s.toSignedMeasure hJ_mem
  -- `|J| ≤ sSup S` and `sSup S ≤ |s univ| + sSup S = ‖s‖`.
  have hJ_le : (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart) ≤ sSup S :=
    le_csSup hS_bdd hJ_mem
  have hJ_neg_le : -((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart)) ≤ sSup S :=
    le_csSup hS_bdd hJ_neg_mem
  have habs_le_sup : |((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
      - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart))| ≤ sSup S :=
    abs_le.mpr ⟨by linarith, hJ_le⟩
  have habs_nn : 0 ≤ |s.toSignedMeasure Set.univ| := abs_nonneg _
  change |((∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.posPart)
        - (∫ ω, p ω ∂s.toSignedMeasure.toJordanDecomposition.negPart))| ≤
      |s.toSignedMeasure Set.univ| + sSup S
  linarith

/-- The image of `ProbabilityMeasure Ω` is closed in the KR normed space. -/
theorem isClosed_range_ofProbDist :
    IsClosed (Set.range (ofProbDist (Ω := Ω))) := by
  apply IsSeqClosed.isClosed
  -- Sequential closure: given `μ_n : ProbabilityMeasure Ω`, `ofProbDist μ_n → s`, find `ν` with
  -- `ofProbDist ν = s`.
  intro x_n s hx_n_in_range hx_n_tendsto
  -- Extract `μ_n`.
  choose μ hμ using hx_n_in_range
  -- Setup: signed measure `S`, Jordan parts `pos` and `neg`.
  set S : MeasureTheory.SignedMeasure Ω := s.toSignedMeasure with hS_def
  set pos : MeasureTheory.Measure Ω := S.toJordanDecomposition.posPart with hpos_def
  set neg : MeasureTheory.Measure Ω := S.toJordanDecomposition.negPart with hneg_def
  have hpos_finite : MeasureTheory.IsFiniteMeasure pos := inferInstance
  have hneg_finite : MeasureTheory.IsFiniteMeasure neg := inferInstance
  -- The shifted sequence `s_n := x_n - s` tends to `0` in KR norm.
  have hdiff_norm : Filter.Tendsto (fun n => ‖x_n n - s‖) Filter.atTop (nhds 0) := by
    have h := hx_n_tendsto
    rw [Metric.tendsto_atTop] at h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    rwa [dist_eq_norm] at this
  -- ## Step 1: total mass = 1.
  -- `(x_n - s).toSignedMeasure univ → 0`.
  have htot_to_zero : Filter.Tendsto
      (fun n => (x_n n - s).toSignedMeasure Set.univ) Filter.atTop (nhds 0) := by
    -- `|·univ| ≤ ‖·‖_KR`.
    have h_abs_le : ∀ n, |(x_n n - s).toSignedMeasure Set.univ| ≤ ‖x_n n - s‖ :=
      fun n => abs_signedMeasure_univ_le_norm (x_n n - s)
    -- Squeeze.
    rw [Metric.tendsto_atTop] at hdiff_norm ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hdiff_norm ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := h_abs_le n
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    rw [abs_of_nonneg (norm_nonneg _)] at h1
    linarith
  -- For each n, `(ofProbDist (μ n)).toSignedMeasure univ = 1`.
  have htot_xn : ∀ n, (x_n n).toSignedMeasure Set.univ = 1 := by
    intro n
    rw [← hμ n]
    change ((μ n : MeasureTheory.Measure Ω).toSignedMeasure) Set.univ = 1
    rw [MeasureTheory.Measure.toSignedMeasure_apply_measurable MeasurableSet.univ,
      MeasureTheory.probReal_univ]
  -- Hence `S univ = 1`.
  have hS_univ_one : S Set.univ = 1 := by
    -- `(x_n - s) univ = (x_n) univ - s univ = 1 - S univ`.
    have hsub : ∀ n, (x_n n - s).toSignedMeasure Set.univ
        = (x_n n).toSignedMeasure Set.univ - S Set.univ := by
      intro n
      change ((x_n n).toSignedMeasure - S) Set.univ = _
      rw [MeasureTheory.VectorMeasure.sub_apply]
    have hconst : Filter.Tendsto (fun n => (x_n n - s).toSignedMeasure Set.univ)
        Filter.atTop (nhds (1 - S Set.univ)) := by
      have : (fun n => (x_n n - s).toSignedMeasure Set.univ)
          = (fun n => (1 : ℝ) - S Set.univ) := by
        funext n; rw [hsub n, htot_xn n]
      rw [this]; exact tendsto_const_nhds
    have := tendsto_nhds_unique htot_to_zero hconst
    linarith
  -- ## Step 2: For nonneg K-Lipschitz `q`, `J(S, q) ≥ 0`.
  -- We first prove this for K-Lipschitz `q` with `q (default) = 0` (continuity in `s`),
  -- then drop the basepoint condition using `S univ = 1`.
  -- Helper: a `0`-Lipschitz function vanishing at `default` is identically `0`.
  have hK0_const : ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p → p (default : Ω) = 0 →
      K = 0 → p = (fun _ => 0) := by
    intro K p hp_lip hp0 hK
    funext ω
    have h := hp_lip.dist_le_mul ω (default : Ω)
    rw [hK] at h
    have hle : dist (p ω) (p (default : Ω)) ≤ 0 := by simpa using h
    have habs : dist (p ω) (p (default : Ω)) = 0 := le_antisymm hle dist_nonneg
    have hpp := dist_eq_zero.mp habs
    rw [hp0] at hpp; exact hpp
  -- Helper: bound `|J(t, p)|` by `K · ‖t‖` for K-Lipschitz `p` with `p default = 0`.
  have habs_J_le_K_norm :
      ∀ (t : KRSignedMeasure Ω) (K : NNReal) (p : Ω → ℝ),
        LipschitzWith K p → p (default : Ω) = 0 →
        |((∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.negPart))| ≤ (K : ℝ) * ‖t‖ := by
    intro t K p hp_lip hp0
    rcases eq_or_ne K 0 with hK | hK
    · -- `K = 0`: `p` is constant, equals `p default = 0`, so `J = 0`.
      have hp_zero : p = (fun _ => 0) := hK0_const K p hp_lip hp0 hK
      rw [hp_zero]
      simp only [MeasureTheory.integral_zero, sub_self, abs_zero, ge_iff_le]
      have : (0 : ℝ) ≤ (K : ℝ) * ‖t‖ := by
        rw [hK]; simp
      linarith
    · -- `K > 0`: scale `p` by `1/K` to get a 1-Lipschitz function with the same basepoint.
      have hKpos : (0 : ℝ) < (K : ℝ) := by
        have : (0 : NNReal) < K := pos_iff_ne_zero.mpr hK
        exact_mod_cast this
      let q : Ω → ℝ := fun ω => p ω / (K : ℝ)
      have hq_lip : LipschitzWith 1 q := lipschitzWith_one_div_lipConst hp_lip hKpos
      have hq0 : q (default : Ω) = 0 := by simp [q, hp0]
      have hbound := abs_signedIntegral_le_norm_of_basepoint t hq_lip hq0
      -- `(∫ q dpos)/(K) - (∫ q dneg)/(K) = J(t, p)/K`.
      have hp_int_pos : MeasureTheory.Integrable p t.toSignedMeasure.toJordanDecomposition.posPart
          := by
        let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp_lip.continuous⟩
        exact pBCF.integrable _
      have hp_int_neg : MeasureTheory.Integrable p t.toSignedMeasure.toJordanDecomposition.negPart
          := by
        let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp_lip.continuous⟩
        exact pBCF.integrable _
      have hq_p : (∫ ω, q ω ∂t.toSignedMeasure.toJordanDecomposition.posPart)
          = (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.posPart) / (K : ℝ) := by
        change (∫ ω, p ω / (K : ℝ) ∂t.toSignedMeasure.toJordanDecomposition.posPart) = _
        rw [show (fun ω => p ω / (K : ℝ)) = (fun ω => (K : ℝ)⁻¹ * p ω) by
          funext ω; rw [div_eq_inv_mul]]
        rw [MeasureTheory.integral_const_mul, ← div_eq_inv_mul]
      have hq_n : (∫ ω, q ω ∂t.toSignedMeasure.toJordanDecomposition.negPart)
          = (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.negPart) / (K : ℝ) := by
        change (∫ ω, p ω / (K : ℝ) ∂t.toSignedMeasure.toJordanDecomposition.negPart) = _
        rw [show (fun ω => p ω / (K : ℝ)) = (fun ω => (K : ℝ)⁻¹ * p ω) by
          funext ω; rw [div_eq_inv_mul]]
        rw [MeasureTheory.integral_const_mul, ← div_eq_inv_mul]
      rw [hq_p, hq_n] at hbound
      have hsub : ((∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.negPart)) / (K : ℝ)
            = (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.posPart) / (K : ℝ)
            - (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.negPart) / (K : ℝ) := by
        rw [sub_div]
      rw [← hsub] at hbound
      rw [abs_div, abs_of_pos hKpos] at hbound
      rw [div_le_iff₀ hKpos] at hbound
      linarith
  -- Continuity of `J(·, p)` for K-Lipschitz `p` with `p default = 0`:
  -- `J(x_n, p) → J(s, p)` when `‖x_n - s‖ → 0`.
  have hJ_cts_basepoint :
      ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p → p (default : Ω) = 0 →
        Filter.Tendsto
          (fun n => (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
              - (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart))
          Filter.atTop
          (nhds ((∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg))) := by
    intro K p hp_lip hp0
    -- `J(x_n, p) - J(s, p) = J(x_n - s, p)` by additivity.
    have hadd : ∀ n,
        (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)
          - ((∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg))
        = (∫ ω, p ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.negPart) := by
      intro n
      -- `x_n n = (x_n n - s) + s` ⇒ `J(x_n, p) = J(x_n - s, p) + J(s, p)`.
      have heq : (x_n n).toSignedMeasure = (x_n n - s).toSignedMeasure + S := by
        change (x_n n).toSignedMeasure = ((x_n n).toSignedMeasure - S) + S
        simp_all only [sub_add_cancel, S, pos, neg]
      -- 1-Lipschitz scaled version, applied at K-Lipschitz level via inner machinery.
      -- We apply `signedIntegralJordan_add` directly.
      -- Need to use a 1-Lipschitz version: scale `p` to `p / K` if `K > 0`, else `p = 0`.
      -- Cleaner: prove the additivity directly for K-Lipschitz by factoring.
      rcases eq_or_ne K 0 with hK | hK
      · -- p ≡ 0.
        have hp_zero : p = (fun _ => 0) := hK0_const K p hp_lip hp0 hK
        rw [hp_zero]; simp
      · -- K > 0: rescale.
        have hKpos : (0 : ℝ) < (K : ℝ) := by
          have : (0 : NNReal) < K := pos_iff_ne_zero.mpr hK
          exact_mod_cast this
        let q : Ω → ℝ := fun ω => p ω / (K : ℝ)
        have hq_lip : LipschitzWith 1 q := lipschitzWith_one_div_lipConst hp_lip hKpos
        -- Apply additivity to `q`.
        have hadd_q := signedIntegralJordan_add q hq_lip (x_n n - s).toSignedMeasure S
        have heq_sm : (x_n n - s).toSignedMeasure + S = (x_n n).toSignedMeasure := by
          change (x_n n).toSignedMeasure - S + S = (x_n n).toSignedMeasure
          exact sub_add_cancel _ _
        rw [heq_sm] at hadd_q
        -- Translate q-integrals to p-integrals via `(K : ℝ)`.
        have hp_eq_Kq : p = fun ω => (K : ℝ) * q ω := by
          funext ω
          change p ω = (K : ℝ) * (p ω / (K : ℝ))
          field_simp
        -- Multiply both sides of hadd_q by K (and use linearity of integrals).
        -- Easier: rewrite all p-integrals in terms of q-integrals.
        have hp_int_xn_pos :
            (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
            = (K : ℝ) * (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        have hp_int_xn_neg :
            (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)
            = (K : ℝ) * (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        have hp_int_pos :
            (∫ ω, p ω ∂pos) = (K : ℝ) * (∫ ω, q ω ∂pos) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        have hp_int_neg :
            (∫ ω, p ω ∂neg) = (K : ℝ) * (∫ ω, q ω ∂neg) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        have hp_int_diff_pos :
            (∫ ω, p ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.posPart)
            = (K : ℝ) *
              (∫ ω, q ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.posPart) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        have hp_int_diff_neg :
            (∫ ω, p ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.negPart)
            = (K : ℝ) *
              (∫ ω, q ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.negPart) := by
          conv_lhs => rw [hp_eq_Kq]
          rw [MeasureTheory.integral_const_mul]
        rw [hp_int_xn_pos, hp_int_xn_neg, hp_int_pos, hp_int_neg,
          hp_int_diff_pos, hp_int_diff_neg]
        -- Unfold the `pos`/`neg` let-bindings so they match `S.toJordanDecomposition.{pos,neg}Part`
        -- in `hadd_q`, then close by `linear_combination`.
        change (K : ℝ) * (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
              - (K : ℝ) * (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)
              - ((K : ℝ) * (∫ ω, q ω ∂S.toJordanDecomposition.posPart)
                 - (K : ℝ) * (∫ ω, q ω ∂S.toJordanDecomposition.negPart))
            = (K : ℝ) * (∫ ω, q ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.posPart)
              - (K : ℝ) * (∫ ω, q ω ∂(x_n n - s).toSignedMeasure.toJordanDecomposition.negPart)
        linear_combination (K : ℝ) * hadd_q
    -- The squeeze: `|J(x_n - s, p)| ≤ K · ‖x_n - s‖ → 0`.
    rw [Metric.tendsto_atTop] at hdiff_norm
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Need `(K : ℝ) > 0` or `K = 0` cases.
    rcases eq_or_ne K 0 with hK | hK
    · -- K = 0 ⇒ `p ≡ 0`, hence both J's are zero.
      have hp_zero : p = (fun _ => 0) := hK0_const K p hp_lip hp0 hK
      refine ⟨0, fun n _ => ?_⟩
      rw [hp_zero]; simp [hε]
    · have hKpos : (0 : ℝ) < (K : ℝ) := by
        have : (0 : NNReal) < K := pos_iff_ne_zero.mpr hK
        exact_mod_cast this
      obtain ⟨N, hN⟩ := hdiff_norm (ε / (K : ℝ)) (div_pos hε hKpos)
      refine ⟨N, fun n hn => ?_⟩
      have h1 := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
      -- |J(x_n, p) - J(S, p)| ≤ K · ‖x_n - s‖ < K · (ε/K) = ε.
      have hbound := habs_J_le_K_norm (x_n n - s) K p hp_lip hp0
      rw [Real.dist_eq, hadd n]
      -- Now |J(x_n - s, p)| ≤ K · ‖x_n - s‖ < K · (ε/K) = ε.
      have hKε : (K : ℝ) * ‖x_n n - s‖ < ε := by
        rw [lt_div_iff₀ hKpos] at h1
        linarith
      linarith [hbound]
  -- Step 2b: For nonneg K-Lipschitz `p` (no basepoint requirement), `J(s, p) ≥ 0`.
  -- Strategy: shift `p ↦ p - p(default)`, recover via `S univ = 1`.
  have hJ_nonneg_lip :
      ∀ (K : NNReal) (p : Ω → ℝ), LipschitzWith K p → (∀ ω, 0 ≤ p ω) →
        0 ≤ (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg) := by
    intro K p hp_lip hp_nn
    -- For each n: `J(x_n, p) = ∫ p dμ_n ≥ 0`.
    have hJ_xn_nn : ∀ n,
        0 ≤ (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart) := by
      intro n
      -- Identify `x_n n = ofProbDist (μ n)`, so the test integral is `∫ p dμ_n ≥ 0`
      -- via `signedIntegral_of_measure`.
      have hmeas : (x_n n).toSignedMeasure
          = ((μ n : MeasureTheory.Measure Ω).toSignedMeasure) := by
        rw [(hμ n).symm]; rfl
      rw [hmeas, signedIntegral_of_measure (μ n : MeasureTheory.Measure Ω) p]
      exact MeasureTheory.integral_nonneg (fun ω => hp_nn ω)
    -- Now use continuity of `J(·, p)` to transfer non-negativity.
    -- Reduce to basepoint: `q ω = p ω - p(default)`.
    set c : ℝ := p (default : Ω) with hc_def
    let q : Ω → ℝ := fun ω => p ω - c
    have hq_lip : LipschitzWith K q := lipschitzWith_sub_const hp_lip c
    have hq0 : q (default : Ω) = 0 := by
      simp_all only [sub_nonneg, sub_self, S, pos, neg, c, q]
    -- `J(t, p) = J(t, q) + c · (pos.real univ - neg.real univ) = J(t, q) + c · (t univ)`.
    -- Apply this for `t = x_n` (with `t univ = 1`) and `t = S` (with `t univ = 1`).
    -- Hence J(x_n, p) = J(x_n, q) + c, J(S, p) = J(S, q) + c.
    -- So J(x_n, p) → J(S, p) iff J(x_n, q) → J(S, q), and the basepoint version applies.
    have hJ_split : ∀ (t : KRSignedMeasure Ω) (htu : t.toSignedMeasure Set.univ = 1),
        (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂t.toSignedMeasure.toJordanDecomposition.negPart)
        = ((∫ ω, q ω ∂t.toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, q ω ∂t.toSignedMeasure.toJordanDecomposition.negPart)) + c := by
      intro t htu
      set tpos := t.toSignedMeasure.toJordanDecomposition.posPart
      set tneg := t.toSignedMeasure.toJordanDecomposition.negPart
      have hp_int_pos : MeasureTheory.Integrable p tpos := by
        let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp_lip.continuous⟩
        exact pBCF.integrable _
      have hp_int_neg : MeasureTheory.Integrable p tneg := by
        let pBCF := BoundedContinuousFunction.mkOfCompact ⟨p, hp_lip.continuous⟩
        exact pBCF.integrable _
      have hq_pos_int : (∫ ω, q ω ∂tpos) = (∫ ω, p ω ∂tpos) - c * tpos.real Set.univ := by
        change (∫ ω, p ω - c ∂tpos) = _
        rw [MeasureTheory.integral_sub hp_int_pos (MeasureTheory.integrable_const _)]
        simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
      have hq_neg_int : (∫ ω, q ω ∂tneg) = (∫ ω, p ω ∂tneg) - c * tneg.real Set.univ := by
        change (∫ ω, p ω - c ∂tneg) = _
        rw [MeasureTheory.integral_sub hp_int_neg (MeasureTheory.integrable_const _)]
        simp [MeasureTheory.integral_const, MeasureTheory.measureReal_def, mul_comm]
      -- `tpos.real univ - tneg.real univ = t.toSignedMeasure univ = 1`.
      have hposneg : (tpos.real Set.univ : ℝ) - tneg.real Set.univ = 1 := by
        have hsum : t.toSignedMeasure.toJordanDecomposition.toSignedMeasure = t.toSignedMeasure :=
          MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition _
        have happ : (t.toSignedMeasure Set.univ : ℝ) = tpos.real Set.univ - tneg.real Set.univ := by
          have h2 := MeasureTheory.Measure.toSignedMeasure_sub_apply
            (μ := tpos) (ν := tneg) (i := (Set.univ : Set Ω)) MeasurableSet.univ
          have hdef : t.toSignedMeasure = tpos.toSignedMeasure - tneg.toSignedMeasure := hsum.symm
          rw [hdef]; exact h2
        linarith [happ, htu]
      rw [hq_pos_int, hq_neg_int]
      have : c * (tpos.real Set.univ - tneg.real Set.univ) = c := by
        rw [hposneg]; ring
      linarith [this]
    -- Substitute and conclude.
    have hJp_xn : ∀ n,
        (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)
        = ((∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)) + c :=
      fun n => hJ_split (x_n n) (htot_xn n)
    have hJp_S : (∫ ω, p ω ∂pos) - (∫ ω, p ω ∂neg)
        = ((∫ ω, q ω ∂pos) - (∫ ω, q ω ∂neg)) + c := hJ_split s hS_univ_one
    -- Continuity of `J(·, q)` for the basepoint version.
    have hJq_cts := hJ_cts_basepoint K q hq_lip hq0
    -- `J(x_n, p) = J(x_n, q) + c`, so `J(x_n, q) = J(x_n, p) - c → J(S, p) - c = J(S, q)`.
    have hJq_xn_eq : ∀ n,
        (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
          - (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)
        = ((∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
            - (∫ ω, p ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart)) - c := by
      intro n; linarith [hJp_xn n]
    -- Each `J(x_n, q) = J(x_n, p) - c ≥ -c`. Limit gives `J(S, q) ≥ -c`, i.e. `J(S, p) ≥ 0`.
    have hJq_xn_ge : ∀ n,
        -c ≤ (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.posPart)
              - (∫ ω, q ω ∂(x_n n).toSignedMeasure.toJordanDecomposition.negPart) := by
      intro n; rw [hJq_xn_eq n]; linarith [hJ_xn_nn n]
    have hJq_S_ge : -c ≤ (∫ ω, q ω ∂pos) - (∫ ω, q ω ∂neg) := by
      apply ge_of_tendsto hJq_cts
      exact Filter.Eventually.of_forall hJq_xn_ge
    linarith [hJp_S]
  -- ## Step 3: For closed nonempty `F`, `pos.real F ≥ neg.real F` via DCT.
  have hF_real_le : ∀ {F : Set Ω}, IsClosed F → neg.real F ≤ pos.real F := by
    intro F hF
    by_cases hFne : F.Nonempty
    · have hFmeas : MeasurableSet F := hF.measurableSet
      let g : ℕ → Ω → ℝ :=
        fun n ω => max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F)
      have hg_lip : ∀ n : ℕ, LipschitzWith (n : NNReal) (g n) :=
        fun n => lipschitz_metricBump (n : NNReal) F
      have hg_cont : ∀ n : ℕ, Continuous (g n) := fun n => (hg_lip n).continuous
      have hg_nn : ∀ n ω, 0 ≤ g n ω :=
        fun n ω => metricBump_nonneg (n : NNReal) F ω
      have hg_le_one : ∀ (n : ℕ) ω, ‖g n ω‖ ≤ 1 := by
        intro n ω
        change ‖max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F)‖ ≤ 1
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (metricBump_nonneg (n : NNReal) F ω)]
        exact metricBump_le_one (n : NNReal) F ω
      have hg_meas_pos : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (g n) pos :=
        fun n => (hg_cont n).aestronglyMeasurable
      have hg_meas_neg : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (g n) neg :=
        fun n => (hg_cont n).aestronglyMeasurable
      have hg_lim : ∀ ω,
          Filter.Tendsto (fun n => g n ω) Filter.atTop
            (nhds (F.indicator (fun _ => (1 : ℝ)) ω)) := by
        intro ω
        have hcast : ∀ n : ℕ, ((n : NNReal) : ℝ) = (n : ℝ) := fun n => by push_cast; rfl
        change Filter.Tendsto
          (fun n : ℕ => max 0 (1 - ((n : NNReal) : ℝ) * Metric.infDist ω F))
          Filter.atTop _
        simp_rw [hcast]
        exact tendsto_metricBump_to_indicator hF hFne ω
      -- DCT gives `∫ g_n dpos → pos.real F` and `∫ g_n dneg → neg.real F`.
      have hint_indic_pos :
          Filter.Tendsto (fun n => ∫ ω, g n ω ∂pos) Filter.atTop
            (nhds (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos)) :=
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (bound := fun _ => 1)
          hg_meas_pos (MeasureTheory.integrable_const 1)
          (fun n => Filter.Eventually.of_forall (fun ω => hg_le_one n ω))
          (Filter.Eventually.of_forall hg_lim)
      have hint_indic_neg :
          Filter.Tendsto (fun n => ∫ ω, g n ω ∂neg) Filter.atTop
            (nhds (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂neg)) :=
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (bound := fun _ => 1)
          hg_meas_neg (MeasureTheory.integrable_const 1)
          (fun n => Filter.Eventually.of_forall (fun ω => hg_le_one n ω))
          (Filter.Eventually.of_forall hg_lim)
      have hpos_indic : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂pos) = pos.real F := by
        rw [MeasureTheory.integral_indicator hFmeas]
        simp [MeasureTheory.measureReal_def]
      have hneg_indic : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂neg) = neg.real F := by
        rw [MeasureTheory.integral_indicator hFmeas]
        simp [MeasureTheory.measureReal_def]
      rw [hpos_indic] at hint_indic_pos
      rw [hneg_indic] at hint_indic_neg
      -- `J(s, g_n) ≥ 0` by Step 2b.
      have hJ_g_nn : ∀ n, 0 ≤ (∫ ω, g n ω ∂pos) - (∫ ω, g n ω ∂neg) :=
        fun n => hJ_nonneg_lip (n : NNReal) (g n) (hg_lip n) (hg_nn n)
      -- Take limits: `pos.real F - neg.real F ≥ 0`.
      have hdiff_lim :
          Filter.Tendsto (fun n => (∫ ω, g n ω ∂pos) - (∫ ω, g n ω ∂neg)) Filter.atTop
            (nhds (pos.real F - neg.real F)) :=
        hint_indic_pos.sub hint_indic_neg
      have : 0 ≤ pos.real F - neg.real F := by
        apply ge_of_tendsto hdiff_lim
        exact Filter.Eventually.of_forall hJ_g_nn
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hFne
      rw [hFne]; simp [MeasureTheory.measureReal_def]
  -- ## Step 4: extend to all measurable sets, then `neg = 0`.
  -- `pos` and `neg` are weakly regular (finite, pseudometric, Borel).
  have hF_le : ∀ {F : Set Ω}, IsClosed F → neg F ≤ pos F := by
    intro F hF
    have hreal := hF_real_le hF
    have hpos_lt : pos F ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    have hneg_lt : neg F ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def] at hreal
    rw [← ENNReal.toReal_le_toReal hneg_lt hpos_lt]; exact hreal
  -- Inner regularity: every measurable set `A` satisfies
  -- `neg A = sup { neg K : K ⊆ A, K closed }`, and each such `K` has `neg K ≤ pos K ≤ pos A`.
  have hneg_le_pos : ∀ {A : Set Ω}, MeasurableSet A → neg A ≤ pos A := by
    intro A hA
    -- `neg.WeaklyRegular` provides inner regularity by closed sets.
    have hwr_neg : neg.WeaklyRegular := inferInstance
    have hinner :
        neg.InnerRegularWRT IsClosed (fun s => MeasurableSet s ∧ neg s ≠ ⊤) :=
      hwr_neg.innerRegular_measurable
    have hAneg : neg A ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    -- For every `r < neg A`, find a closed `K ⊆ A` with `r < neg K`. Conclude `r < pos A`.
    -- Hence `neg A ≤ pos A`.
    by_contra hlt
    push Not at hlt
    -- `pos A < neg A`. Get `r` between them.
    obtain ⟨K, hKA, hK_closed, hK_lt⟩ := hinner ⟨hA, hAneg⟩ (pos A) hlt
    have hKpos : pos K ≤ pos A := MeasureTheory.measure_mono hKA
    have hK_neg_le_pos : neg K ≤ pos K := hF_le hK_closed
    have : neg K ≤ pos A := le_trans hK_neg_le_pos hKpos
    -- Contradicts `pos A < neg K`.
    exact absurd hK_lt (not_lt.mpr this)
  -- Now `neg = 0`. Use mutual singularity: there is a `null set U` of `pos` with `neg Uᶜ = 0`.
  -- So `neg` is supported on `U`, with `pos U = 0`. By the above, `neg U ≤ pos U = 0`.
  have hms : pos.MutuallySingular neg := S.toJordanDecomposition.mutuallySingular
  have hms_sym : neg.MutuallySingular pos := hms.symm
  -- `nullSet hms_sym` is a measurable set with `neg(nullSet) = 0` and `pos(nullSetᶜ) = 0`.
  set U : Set Ω := hms_sym.nullSet with hU_def
  have hU_meas : MeasurableSet U := hms_sym.measurableSet_nullSet
  have hneg_U : neg U = 0 := hms_sym.measure_nullSet
  have hpos_Uc : pos Uᶜ = 0 := hms_sym.measure_compl_nullSet
  have hUc_meas : MeasurableSet Uᶜ := hU_meas.compl
  -- `neg Uᶜ ≤ pos Uᶜ = 0`, so `neg Uᶜ = 0`.
  have hneg_Uc : neg Uᶜ = 0 := by
    have h := hneg_le_pos hUc_meas
    rw [hpos_Uc] at h
    exact le_antisymm h (zero_le)
  -- `neg = neg(U) + neg(Uᶜ) = 0 + 0 = 0`.
  have hneg_zero : neg = 0 := by
    apply MeasureTheory.Measure.ext
    intro A hA
    have hAU : A = (A ∩ U) ∪ (A ∩ Uᶜ) := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    have hAU_meas : MeasurableSet (A ∩ U) := hA.inter hU_meas
    have hAUc_meas : MeasurableSet (A ∩ Uᶜ) := hA.inter hUc_meas
    have hdisj : Disjoint (A ∩ U) (A ∩ Uᶜ) :=
      disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
    rw [hAU, MeasureTheory.measure_union hdisj hAUc_meas]
    have h1 : neg (A ∩ U) = 0 := by
      have : neg (A ∩ U) ≤ neg U := MeasureTheory.measure_mono Set.inter_subset_right
      rw [hneg_U] at this
      exact le_antisymm this (zero_le)
    have h2 : neg (A ∩ Uᶜ) = 0 := by
      have : neg (A ∩ Uᶜ) ≤ neg Uᶜ := MeasureTheory.measure_mono Set.inter_subset_right
      rw [hneg_Uc] at this
      exact le_antisymm this (zero_le)
    rw [h1, h2]
    simp
  -- ## Step 5: build `ν : ProbabilityMeasure Ω` with `ofProbDist ν = s`.
  -- `pos.toSignedMeasure = S`.
  have hS_eq_pos : S = pos.toSignedMeasure := by
    have hsum : S.toJordanDecomposition.toSignedMeasure = S :=
      MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition S
    -- `S = pos.toSignedMeasure - neg.toSignedMeasure`, and `neg = 0` ⇒ `neg.toSignedMeasure = 0`.
    have h : S = pos.toSignedMeasure - neg.toSignedMeasure := hsum.symm
    have hneg_sm : neg.toSignedMeasure = (0 : MeasureTheory.Measure Ω).toSignedMeasure := by
      congr 1
    rw [hneg_sm, MeasureTheory.Measure.toSignedMeasure_zero, sub_zero] at h
    exact h
  -- `pos univ = 1`.
  have hpos_univ : pos Set.univ = 1 := by
    -- `S univ = pos univ - neg univ = pos univ - 0 = pos univ` (in ℝ).
    have hsum : S.toJordanDecomposition.toSignedMeasure = S :=
      MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition S
    have happ : (S Set.univ : ℝ) = pos.real Set.univ - neg.real Set.univ := by
      have h2 := MeasureTheory.Measure.toSignedMeasure_sub_apply
        (μ := pos) (ν := neg) (i := (Set.univ : Set Ω)) MeasurableSet.univ
      have hdef : S = pos.toSignedMeasure - neg.toSignedMeasure := hsum.symm
      rw [hdef]; exact h2
    rw [hS_univ_one, hneg_zero, MeasureTheory.measureReal_def] at happ
    simp at happ
    -- happ : 1 = pos.real univ
    have hpos_real : pos.real Set.univ = 1 := happ.symm
    rw [MeasureTheory.measureReal_def] at hpos_real
    have hpos_ne_top : pos Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    rw [← ENNReal.toReal_one] at hpos_real
    exact (ENNReal.toReal_eq_toReal_iff' hpos_ne_top (by simp)).mp hpos_real
  -- Build `ν`.
  haveI hpos_isProb : MeasureTheory.IsProbabilityMeasure pos := ⟨hpos_univ⟩
  let ν : ProbabilityMeasure Ω := ⟨pos, hpos_isProb⟩
  refine ⟨ν, ?_⟩
  apply KRSignedMeasure.ext
  exact hS_eq_pos.symm

end KRSignedMeasure

end Econlib.Optimization.OptimalTransport
