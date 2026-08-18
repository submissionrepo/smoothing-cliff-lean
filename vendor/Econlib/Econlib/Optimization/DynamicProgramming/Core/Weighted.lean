/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.BellmanOperator

open Set

/-!
# Weighted dynamic programing

This module provides a weighted-sup-norm interface for dynamic programs whose state space is
unbounded. The main result is a weighted Blackwell contraction bound: Monotonicity plus discounting
with respect to a weight function (Boyd 1990; Blackwell 1965) implies contraction in the weighted
oscillation seminorm, and hence a unique weighted-bounded fixed point obtained as the pointwise
limit of iterating `T` from zero.

The module deliberately separates the analytic fixed-point construction from the order/algebraic
part. Applications instantiate `WeightedBlackwell` from a Bellman operator and obtain the
fixed-point certificate directly, without an external Banach hypothesis.

## Main definitions

* `Weight` — a strictly positive weight function normalized to be at least one.
* `WeightedBounded` — functions bounded by a scalar multiple of the weight.
* `weightedOscillation` — weighted sup-norm distance between two functions.
* `WeightedBlackwell` — a monotone, discounting Bellman operator with respect to a weight.
* `WeightedBlackwell.FixedPointCertificate` — a certified weighted-bounded, unique fixed point.
* `WeightedBlackwell.fixedPoint` — the pointwise limit of iterating `T` from zero.
* `WeightedBlackwell.fixedPointCertificate` — constructs the certificate from `WeightedBlackwell`.

## Main statements

* `WeightedBlackwell.oscillation_contraction` — a weighted Blackwell operator contracts the
  weighted oscillation by a factor of `β`.
* `WeightedBlackwell.fixedPoint_isFixedPt` — the limit function is a fixed point of `T`.
* `WeightedBlackwell.fixedPoint_unique` — uniqueness of weighted-bounded fixed points.

## Notes

At the constant weight `ω = Weight.one`, the hypotheses of `WeightedBlackwell` coincide with the
unweighted Blackwell conditions. The weighted interface is separate because unbounded state spaces
often require weighted-bounded functions rather than globally bounded functions.

## References

* Blackwell, David. 1965. “Discounted Dynamic Programing.” *The Annals of Mathematical Statistics*
  36 (1): 226–35. [https://doi.org/10.1214/aoms/1177700285](https://doi.org/10.1214/aoms/1177700285).
* Boud, John H., III. 1990. “Recursive Utility and the Ramsey Problem.” *Journal of Economic
  Theory* 50 (2): 326–45. [https://doi.org/10.1016/0022-0531(90)90006-6](https://doi.org/10.1016/0022-0531(90)90006-6).

## Tags

dynamic programing, weighted sup-norm, blackwell, contraction, fixed point, bellman operator
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

universe u

/-- A strictly positive weight function, normalized to be at least one.

The normalization makes uniformly bounded functions automatically weighted bounded and avoids
zero-denominator side conditions in weighted sup expressions. -/
structure Weight (S : Type u) where
  /-- The weight assigned to each state. -/
  toFun : S → ℝ
  /-- The weight is strictly positive. -/
  pos : ∀ s, 0 < toFun s
  /-- The weight is normalized to be at least one. -/
  one_le : ∀ s, 1 ≤ toFun s

namespace Weight

instance {S : Type u} : CoeFun (Weight S) (fun _ => S → ℝ) where
  coe ω := ω.toFun

@[simp] theorem coe_apply {S : Type u} (ω : Weight S) (s : S) :
    (ω : S → ℝ) s = ω.toFun s := rfl

/-- The constant-one weight. -/
def one (S : Type u) : Weight S where
  toFun := fun _ => 1
  pos := fun _ => by norm_num
  one_le := fun _ => le_rfl

end Weight

variable {S : Type u}

/-- A function is bounded relative to a weight if `|v s| ≤ C * ω s` for some nonnegative constant
`C`. -/
def WeightedBounded (ω : Weight S) (v : S → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |v s| ≤ C * ω s

namespace WeightedBounded

variable {ω : Weight S} {v w : S → ℝ}

/-- The zero function is weighted bounded. -/
theorem zero : WeightedBounded ω (fun _ : S => 0) :=
  ⟨0, le_rfl, fun s => by simp⟩

/-- A weighted multiple of the weight is weighted bounded. -/
theorem weight_mul (c : ℝ) : WeightedBounded ω (fun s : S => c * ω s) :=
  ⟨|c|, abs_nonneg c, fun s => by
    rw [abs_mul, abs_of_pos (ω.pos s)]⟩

/-- A uniformly bounded function is weighted bounded. -/
theorem of_uniformBound {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ s, |v s| ≤ B) : WeightedBounded ω v :=
  ⟨B, hB_nonneg, fun s => (hB s).trans (by
    have hω : 1 ≤ ω s := ω.one_le s
    nlinarith)⟩

/-- Negation preserves weighted boundedness. -/
theorem neg (hv : WeightedBounded ω v) :
    WeightedBounded ω (fun s => -v s) := by
  obtain ⟨C, hC, hbound⟩ := hv
  exact ⟨C, hC, fun s => by simpa using hbound s⟩

/-- Addition preserves weighted boundedness. -/
theorem add (hv : WeightedBounded ω v) (hw : WeightedBounded ω w) :
    WeightedBounded ω (fun s => v s + w s) := by
  obtain ⟨Cv, hCv, hvb⟩ := hv
  obtain ⟨Cw, hCw, hwb⟩ := hw
  refine ⟨Cv + Cw, add_nonneg hCv hCw, fun s => ?_⟩
  calc |v s + w s|
      ≤ |v s| + |w s| := abs_add_le _ _
    _ ≤ Cv * ω s + Cw * ω s := add_le_add (hvb s) (hwb s)
    _ = (Cv + Cw) * ω s := by ring

/-- Subtraction preserves weighted boundedness. -/
theorem sub (hv : WeightedBounded ω v) (hw : WeightedBounded ω w) :
    WeightedBounded ω (fun s => v s - w s) := by
  simpa [sub_eq_add_neg] using hv.add hw.neg

/-- Scalar multiplication preserves weighted boundedness. -/
theorem smul (c : ℝ) (hv : WeightedBounded ω v) :
    WeightedBounded ω (fun s => c * v s) := by
  obtain ⟨C, hC, hvb⟩ := hv
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, fun s => ?_⟩
  calc |c * v s|
      = |c| * |v s| := abs_mul _ _
    _ ≤ |c| * (C * ω s) := mul_le_mul_of_nonneg_left (hvb s) (abs_nonneg c)
    _ = (|c| * C) * ω s := by ring

/-- Weighted boundedness gives an upper bound for weighted pointwise ratios. -/
theorem range_div_bddAbove (hv : WeightedBounded ω v) :
    BddAbove (Set.range fun s => |v s| / ω s) := by
  obtain ⟨C, _hC, hbound⟩ := hv
  refine ⟨C, ?_⟩
  rintro r ⟨s, rfl⟩
  exact (div_le_iff₀ (ω.pos s)).mpr (hbound s)

end WeightedBounded

/-- Weighted oscillation of two functions: `sup_s |v s - w s| / ω s`. -/
noncomputable def weightedOscillation (ω : Weight S) (v w : S → ℝ) : ℝ :=
  sSup (Set.range fun s => |v s - w s| / ω s)

/-- A pointwise weighted-distance bound obtained from the weighted supremum. -/
theorem abs_sub_le_weightedOscillation_mul (ω : Weight S) {v w : S → ℝ}
    (hvw : WeightedBounded ω (fun s => v s - w s)) (s : S) :
    |v s - w s| ≤ weightedOscillation ω v w * ω s := by
  have hbdd := hvw.range_div_bddAbove
  have hle : |v s - w s| / ω s ≤ weightedOscillation ω v w :=
    le_csSup hbdd ⟨s, rfl⟩
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt (ω.pos s))
  rwa [div_mul_cancel₀ _ (ne_of_gt (ω.pos s))] at hmul

/-- Weighted Blackwell conditions for an operator.

The discounting axiom is written in weighted form: `T(v + cω) ≤ Tv + β cω` for `c ≥ 0`. -/
structure WeightedBlackwell (ω : Weight S) (T : (S → ℝ) → S → ℝ) (β : ℝ) where
  /-- The discount factor is nonnegative. -/
  beta_nonneg : 0 ≤ β
  /-- The discount factor is strictly below one. -/
  beta_lt_one : β < 1
  /-- The operator maps weighted-bounded functions to weighted-bounded functions. -/
  maps_weightedBounded :
    ∀ v : S → ℝ, WeightedBounded ω v → WeightedBounded ω (T v)
  /-- Monotonicity on weighted-bounded functions. -/
  monotone :
    ∀ v w : S → ℝ, WeightedBounded ω v → WeightedBounded ω w →
      (∀ s, v s ≤ w s) → ∀ s, T v s ≤ T w s
  /-- Weighted discounting. -/
  discounting :
    ∀ (v : S → ℝ) (c : ℝ), WeightedBounded ω v → 0 ≤ c →
      ∀ s, T (fun s' => v s' + c * ω s') s ≤ T v s + β * c * ω s

namespace WeightedBlackwell

variable {ω : Weight S} {T : (S → ℝ) → S → ℝ} {β : ℝ}

/-- The weighted oscillation is nonnegative whenever the compared functions have weighted-bounded
difference and the state space is nonempty. -/
theorem weightedOscillation_nonneg [Nonempty S] {v w : S → ℝ}
    (hvw : WeightedBounded ω (fun s => v s - w s)) :
    0 ≤ weightedOscillation ω v w := by
  let s : S := Classical.arbitrary S
  have hbdd := hvw.range_div_bddAbove
  have hle : |v s - w s| / ω s ≤ weightedOscillation ω v w :=
    le_csSup hbdd ⟨s, rfl⟩
  exact (div_nonneg (abs_nonneg _) (le_of_lt (ω.pos s))).trans hle

/-- Pointwise weighted contraction bound implied by the weighted Blackwell conditions. -/
theorem pointwise_abs_le (H : WeightedBlackwell ω T β) [Nonempty S] {v w : S → ℝ}
    (hv : WeightedBounded ω v) (hw : WeightedBounded ω w) (s : S) :
    |T v s - T w s| ≤ β * weightedOscillation ω v w * ω s := by
  set d := weightedOscillation ω v w
  have hvw : WeightedBounded ω (fun x => v x - w x) := hv.sub hw
  have hd : 0 ≤ d := weightedOscillation_nonneg hvw
  have h_bound_vw :
      ∀ x, v x ≤ w x + d * ω x := by
    intro x
    have h := abs_sub_le_weightedOscillation_mul ω hvw x
    have hleft : v x - w x ≤ d * ω x := (le_abs_self _).trans h
    linarith
  have h_bound_wv :
      ∀ x, w x ≤ v x + d * ω x := by
    intro x
    have h : |w x - v x| ≤ d * ω x := by
      simpa [d, abs_sub_comm] using
        (abs_sub_le_weightedOscillation_mul ω hvw x)
    have hleft : w x - v x ≤ d * ω x := (le_abs_self _).trans h
    linarith
  have hw_plus : WeightedBounded ω (fun x => w x + d * ω x) :=
    hw.add (WeightedBounded.weight_mul d)
  have hv_plus : WeightedBounded ω (fun x => v x + d * ω x) :=
    hv.add (WeightedBounded.weight_mul d)
  have h_upper : T v s ≤ T w s + β * d * ω s := by
    have hmono := WeightedBlackwell.monotone H v (fun x => w x + d * ω x)
      hv hw_plus h_bound_vw s
    have hdisc := WeightedBlackwell.discounting H w d hw hd s
    linarith
  have h_lower : T w s ≤ T v s + β * d * ω s := by
    have hmono := WeightedBlackwell.monotone H w (fun x => v x + d * ω x)
      hw hv_plus h_bound_wv s
    have hdisc := WeightedBlackwell.discounting H v d hv hd s
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Weighted Blackwell operators are contractions in weighted oscillation. -/
theorem oscillation_contraction (H : WeightedBlackwell ω T β) [Nonempty S] {v w : S → ℝ}
    (hv : WeightedBounded ω v) (hw : WeightedBounded ω w) :
    weightedOscillation ω (T v) (T w) ≤
      β * weightedOscillation ω v w := by
  have hTv := WeightedBlackwell.maps_weightedBounded H v hv
  have hTw := WeightedBlackwell.maps_weightedBounded H w hw
  have hbdd := (hTv.sub hTw).range_div_bddAbove
  apply csSup_le (Set.range_nonempty (fun s => |T v s - T w s| / ω s))
  rintro r ⟨s, rfl⟩
  have hpt := pointwise_abs_le H hv hw s
  rw [div_le_iff₀ (ω.pos s)]
  exact hpt

/-- **Monotone comparative statics of weighted-bounded fixed points.** The weighted-norm analog of
the bounded `fixedPoint_le_of_operator_le`. If `T₂` is a weighted Blackwell operator (so monotone
and weighted-discounting with factor `β < 1`), and `V₁`, `V₂` are weighted-bounded fixed points of
`T₁`, `T₂` with `T₁ V₁ ≤ T₂ V₁` pointwise, then `V₁ ≤ V₂` pointwise.

Only the larger operator `T₂` need satisfy the Blackwell conditions, and the operator order is
required only at the fixed point `V₁`. The proof bounds the weighted gap
`c := ⨆ s, (V₁ s − V₂ s) / ω s` above by `β · c⁺` through a single weighted discounting step, which
forces `c ≤ 0` — the unbounded-reward version of the engine driving the option-value comparative
statics. -/
theorem fixedPoint_le_of_operator_le [Nonempty S] {T₁ T₂ : (S → ℝ) → S → ℝ}
    (H₂ : WeightedBlackwell ω T₂ β) {V₁ V₂ : S → ℝ}
    (hV₁b : WeightedBounded ω V₁) (hV₂b : WeightedBounded ω V₂)
    (hV₁ : ∀ s, V₁ s = T₁ V₁ s) (hV₂ : ∀ s, V₂ s = T₂ V₂ s)
    (h_op : ∀ s, T₁ V₁ s ≤ T₂ V₁ s) :
    ∀ s, V₁ s ≤ V₂ s := by
  -- `c := ⨆ s, (V₁ s − V₂ s) / ω s` is bounded above since `V₁ − V₂` is weighted bounded.
  have hbdd : BddAbove (Set.range fun s => (V₁ s - V₂ s) / ω s) := by
    obtain ⟨C, _hC, hbound⟩ := hV₁b.sub hV₂b
    exact ⟨C, Set.forall_mem_range.mpr fun s =>
      (div_le_iff₀ (ω.pos s)).mpr ((le_abs_self _).trans (hbound s))⟩
  set c := ⨆ s, (V₁ s - V₂ s) / ω s with hc
  -- Pointwise: `V₁ s − V₂ s ≤ c · ω s`.
  have hpt_c : ∀ s, V₁ s - V₂ s ≤ c * ω s := fun s =>
    (div_le_iff₀ (ω.pos s)).mp (le_ciSup hbdd s)
  set cp := max c 0 with hcp
  have hcp0 : 0 ≤ cp := le_max_right _ _
  have hV1_le : ∀ t, V₁ t ≤ V₂ t + cp * ω t := fun t => by
    have h2 : c * ω t ≤ cp * ω t := mul_le_mul_of_nonneg_right (le_max_left c 0) (ω.pos t).le
    linarith [hpt_c t]
  have hV2cp_bdd : WeightedBounded ω (fun t => V₂ t + cp * ω t) :=
    hV₂b.add (WeightedBounded.weight_mul cp)
  -- One weighted discounting step bounds the pointwise gap: `V₁ s − V₂ s ≤ β · cp · ω s`.
  have hstep : ∀ s, V₁ s - V₂ s ≤ β * cp * ω s := by
    intro s
    have h1 : V₁ s ≤ T₂ V₁ s := (hV₁ s).le.trans (h_op s)
    have h2 : T₂ V₁ s ≤ T₂ (fun t => V₂ t + cp * ω t) s :=
      H₂.monotone V₁ _ hV₁b hV2cp_bdd hV1_le s
    have h3 : T₂ (fun t => V₂ t + cp * ω t) s ≤ T₂ V₂ s + β * cp * ω s :=
      H₂.discounting V₂ cp hV₂b hcp0 s
    have h4 : T₂ V₂ s = V₂ s := (hV₂ s).symm
    linarith
  have hc_le_βcp : c ≤ β * cp := ciSup_le fun s => (div_le_iff₀ (ω.pos s)).mpr (hstep s)
  -- `c ≤ β·cp` with `cp = max c 0` and `β < 1` forces `c ≤ 0`.
  have hc0 : c ≤ 0 := by
    rcases le_or_gt c 0 with h | h
    · exact h
    · exfalso
      rw [hcp, max_eq_left h.le] at hc_le_βcp
      nlinarith [mul_pos (show (0 : ℝ) < 1 - β by linarith [H₂.beta_lt_one]) h]
  exact fun s => by nlinarith [hpt_c s, hc0, (ω.pos s).le]

/-- A weighted fixed-point certificate for Bellman equations on unbounded states.

The uniqueness field is intentionally explicit: Different applications may import different
weighted Banach fixed-point theorems or obtain existence from a specialized result.  The
certificate standardizes the downstream API once existence is known. -/
structure FixedPointCertificate where
  /-- The fixed-point value function. -/
  value : S → ℝ
  /-- The fixed point is weighted bounded. -/
  weighted_bounded : WeightedBounded ω value
  /-- The weighted Bellman equation. -/
  fixed : ∀ s, value s = T value s
  /-- Uniqueness among weighted-bounded fixed points. -/
  unique :
    ∀ w : S → ℝ, WeightedBounded ω w → (∀ s, w s = T w s) → w = value

namespace FixedPointCertificate

/-- Any weighted-bounded fixed point equals the certified value function. -/
theorem eq_value (C : FixedPointCertificate (ω := ω) (T := T)) {w : S → ℝ}
    (hw : WeightedBounded ω w) (hfixed : ∀ s, w s = T w s) :
    w = C.value :=
  C.unique w hw hfixed

end FixedPointCertificate

/-! ## Existence of the weighted fixed point.

For a weighted Blackwell operator `T` on a nonempty state space, the iterated sequence `T^n 0`
is pointwise Cauchy, with summable consecutive differences dominated by a geometric series in `β`.
The pointwise limit is a weighted-bounded fixed point of `T`, and any other weighted-bounded fixed
point coincides with it.  This delivers the `FixedPointCertificate` directly from the
`WeightedBlackwell` data, without an external Banach hypothesis. -/

section Existence

variable {ω : Weight S} {T : (S → ℝ) → S → ℝ} {β : ℝ}

/-- Iteration of `T` starting from the zero function. -/
noncomputable def iter (T : (S → ℝ) → S → ℝ) : ℕ → S → ℝ :=
  fun n => T^[n] (fun _ => 0)

/-- The zeroth iterate is the zero function. -/
lemma iter_zero : iter T 0 = (fun _ : S => (0 : ℝ)) := rfl

/-- The successor iterate is `T` applied to the previous iterate. -/
lemma iter_succ (n : ℕ) : iter T (n + 1) = T (iter T n) :=
  Function.iterate_succ_apply' T n _

/-- Every iterate of `T` from zero is weighted bounded. -/
lemma iter_weightedBounded (H : WeightedBlackwell ω T β) :
    ∀ n, WeightedBounded ω (iter T n) := by
  intro n
  induction n with
  | zero => exact iter_zero (T := T) ▸ WeightedBounded.zero
  | succ n ih => exact iter_succ (T := T) n ▸ H.maps_weightedBounded _ ih

variable [Nonempty S]

/-- Consecutive iterates contract their weighted oscillation by a factor of `β`. -/
lemma iter_consec_oscillation_le (H : WeightedBlackwell ω T β) :
    ∀ n, weightedOscillation ω (iter T (n + 1)) (iter T n)
      ≤ β ^ n * weightedOscillation ω (iter T 1) (iter T 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iter_succ (T := T) (n + 1)]
    nth_rewrite 2 [iter_succ (T := T) n]
    calc weightedOscillation ω (T (iter T (n + 1))) (T (iter T n))
        ≤ β * weightedOscillation ω (iter T (n + 1)) (iter T n) :=
          H.oscillation_contraction
            (iter_weightedBounded H (n + 1)) (iter_weightedBounded H n)
      _ ≤ β * (β ^ n * weightedOscillation ω (iter T 1) (iter T 0)) :=
          mul_le_mul_of_nonneg_left ih H.beta_nonneg
      _ = β ^ (n + 1) * weightedOscillation ω (iter T 1) (iter T 0) := by ring

/-- Pointwise consecutive-iterate bound, scaled by the weight. -/
lemma iter_consec_pointwise_bound (H : WeightedBlackwell ω T β) (n : ℕ) (s : S) :
    |iter T (n + 1) s - iter T n s|
      ≤ β ^ n * weightedOscillation ω (iter T 1) (iter T 0) * ω s := by
  have hwb : WeightedBounded ω (fun s' => iter T (n + 1) s' - iter T n s') :=
    (iter_weightedBounded H (n + 1)).sub (iter_weightedBounded H n)
  have hle := abs_sub_le_weightedOscillation_mul ω hwb s
  refine hle.trans ?_
  exact mul_le_mul_of_nonneg_right (iter_consec_oscillation_le H n)
    (le_of_lt (ω.pos s))

omit [Nonempty S] in
/-- The geometric majorant `β^k · d₀ · ω s` is summable. -/
private lemma summable_geom_osc (H : WeightedBlackwell ω T β) (s : S) :
    Summable fun k => β ^ k * weightedOscillation ω (iter T 1) (iter T 0) * ω s := by
  -- Reassociate so the constant `d₀ · ω s` factors out of the geometric series in `β`.
  have hrw :
      (fun k : ℕ => β ^ k * weightedOscillation ω (iter T 1) (iter T 0) * ω s)
        = (fun k => β ^ k * (weightedOscillation ω (iter T 1) (iter T 0) * ω s)) := by
    funext k; ring
  rw [hrw]
  exact (summable_geometric_of_lt_one H.beta_nonneg H.beta_lt_one).mul_right _

/-- For each state, the iterate sequence has summable consecutive distances. -/
lemma iter_summable_consec_dist (H : WeightedBlackwell ω T β) (s : S) :
    Summable fun n => |iter T n s - iter T (n + 1) s| := by
  -- Dominate pointwise by the geometric series `β^n * d₀ * ω s`.
  apply Summable.of_nonneg_of_le
    (g := fun n => |iter T n s - iter T (n + 1) s|)
    (f := fun n => β ^ n * weightedOscillation ω (iter T 1) (iter T 0) * ω s)
  · intro _; exact abs_nonneg _
  · intro n
    rw [abs_sub_comm]
    exact iter_consec_pointwise_bound H n s
  · exact summable_geom_osc H s

/-- For each state, the iterate sequence is Cauchy in `ℝ`. -/
lemma iter_pointwise_cauchy (H : WeightedBlackwell ω T β) (s : S) :
    CauchySeq (fun n => iter T n s) := by
  refine cauchySeq_of_summable_dist ?_
  simpa [Real.dist_eq] using iter_summable_consec_dist H s

/-- The fixed-point value: The pointwise limit of iterating `T` from zero. The fixed-point property
is established by `fixedPoint_isFixedPt`. -/
-- `_H` is intentionally unused: it fixes the result to a specific operator `T`
-- so that downstream lemmas (`fixedPoint_isFixedPt`, `fixedPoint_unique`) read naturally.
noncomputable def fixedPoint (_H : WeightedBlackwell ω T β) : S → ℝ :=
  fun s => Filter.atTop.limUnder (fun n => iter T n s)

/-- At each state, the iterate sequence converges to the fixed-point value. -/
lemma iter_tendsto_fixedPoint (H : WeightedBlackwell ω T β) (s : S) :
    Filter.Tendsto (fun n => iter T n s) Filter.atTop (nhds (fixedPoint H s)) := by
  unfold fixedPoint
  exact (iter_pointwise_cauchy H s).tendsto_limUnder

omit [Nonempty S] in
/-- Geometric tail-sum identity used by `iter_dist_le_geometric`. -/
private lemma geometric_tail_sum (H : WeightedBlackwell ω T β) (c : ℝ) (n : ℕ) :
    (∑' k, β ^ (n + k) * c) = β ^ n * c / (1 - β) := by
  have hcongr : (fun k => β ^ (n + k) * c) = fun k => β ^ n * c * β ^ k := by
    funext k
    rw [pow_add]
    ring
  rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one H.beta_nonneg H.beta_lt_one,
    ← div_eq_mul_inv]

/-- Bound on consecutive distances of the iterate sequence as a `dist`. -/
private lemma iter_dist_consec_le (H : WeightedBlackwell ω T β) (k : ℕ) (s : S) :
    dist (iter T k s) (iter T (k + 1) s)
      ≤ β ^ k * weightedOscillation ω (iter T 1) (iter T 0) * ω s := by
  rw [Real.dist_eq, abs_sub_comm]
  exact iter_consec_pointwise_bound H k s

/-- Pointwise distance bound between an iterate and the limit. -/
lemma iter_dist_le_geometric (H : WeightedBlackwell ω T β) (n : ℕ) (s : S) :
    |iter T n s - fixedPoint H s|
      ≤ β ^ n * weightedOscillation ω (iter T 1) (iter T 0) * ω s / (1 - β) := by
  have hsum : Summable fun k =>
      β ^ k * weightedOscillation ω (iter T 1) (iter T 0) * ω s :=
    summable_geom_osc H s
  have key := dist_le_tsum_of_dist_le_of_tendsto
    (fun k => β ^ k * weightedOscillation ω (iter T 1) (iter T 0) * ω s)
    (fun k => iter_dist_consec_le H k s) hsum (iter_tendsto_fixedPoint H s) n
  rw [Real.dist_eq] at key
  refine key.trans ?_
  have hassoc :
      (∑' m, β ^ (n + m) * weightedOscillation ω (iter T 1) (iter T 0) * ω s)
        = (∑' m, β ^ (n + m) * (weightedOscillation ω (iter T 1) (iter T 0) * ω s)) := by
    apply tsum_congr
    intro m
    ring
  rw [hassoc,
    geometric_tail_sum H (weightedOscillation ω (iter T 1) (iter T 0) * ω s) n]
  exact le_of_eq (by ring)

/-- The fixed-point value is weighted bounded. -/
lemma fixedPoint_weightedBounded (H : WeightedBlackwell ω T β) :
    WeightedBounded ω (fixedPoint H) := by
  set d₀ := weightedOscillation ω (iter T 1) (iter T 0)
  refine ⟨d₀ / (1 - β), ?_, ?_⟩
  · have hβ : 0 < 1 - β := sub_pos.mpr H.beta_lt_one
    have hosc_nn : 0 ≤ d₀ := by
      have hwb : WeightedBounded ω (fun s' => iter T 1 s' - iter T 0 s') :=
        (iter_weightedBounded H 1).sub (iter_weightedBounded H 0)
      exact weightedOscillation_nonneg hwb
    exact div_nonneg hosc_nn hβ.le
  · intro s
    have h0 := iter_dist_le_geometric H 0 s
    have hiter0 : iter T 0 s = 0 := rfl
    rw [hiter0, zero_sub, abs_neg, pow_zero, one_mul] at h0
    rw [div_mul_eq_mul_div]
    exact h0

/-- The limit function is a fixed point of `T`. -/
lemma fixedPoint_isFixedPt (H : WeightedBlackwell ω T β) :
    ∀ s, fixedPoint H s = T (fixedPoint H) s := by
  intro s
  set d₀ := weightedOscillation ω (iter T 1) (iter T 0) with hd₀
  -- Step 1: `iter T (n + 1) s → fixedPoint H s` by reindexing the convergent iter sequence.
  have ha : Filter.Tendsto (fun n => iter T (n + 1) s) Filter.atTop
      (nhds (fixedPoint H s)) :=
    (iter_tendsto_fixedPoint H s).comp (Filter.tendsto_add_atTop_nat 1)
  -- Step 2: `T (iter T n) s → T (fixedPoint H) s` via the pointwise contraction bound.
  -- Bound: |T (iter T n) s - T (fixedPoint H) s| ≤ ω s · β · (β^n · d₀ / (1 - β)),
  -- which decays geometrically.
  have hbd_iter := iter_weightedBounded H
  have hbd_fp := fixedPoint_weightedBounded H
  have hosc_le : ∀ n,
      weightedOscillation ω (iter T n) (fixedPoint H) ≤ β ^ n * d₀ / (1 - β) := by
    intro n
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨s', rfl⟩
    have hpt' := iter_dist_le_geometric H n s'
    rw [← hd₀] at hpt'
    rw [div_le_iff₀ (ω.pos s'), div_mul_eq_mul_div]
    exact hpt'
  have hT_close : ∀ n,
      |T (iter T n) s - T (fixedPoint H) s| ≤ β * (β ^ n * d₀ / (1 - β)) * ω s := by
    intro n
    refine (H.pointwise_abs_le (hbd_iter n) hbd_fp s).trans ?_
    have h₁ := mul_le_mul_of_nonneg_left (hosc_le n) H.beta_nonneg
    exact mul_le_mul_of_nonneg_right h₁ (le_of_lt (ω.pos s))
  -- The bound `β · β^n · d₀ / (1 - β) · ω s` tends to zero.
  have hbd_tendsto : Filter.Tendsto
      (fun n => β * (β ^ n * d₀ / (1 - β)) * ω s) Filter.atTop (nhds 0) := by
    have hgeom : Filter.Tendsto (fun n : ℕ => β ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one H.beta_nonneg H.beta_lt_one
    have := hgeom.const_mul (β * (d₀ / (1 - β)) * ω s)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  -- Sandwich: the absolute difference tends to 0, hence the sequence converges.
  have hb : Filter.Tendsto (fun n => T (iter T n) s) Filter.atTop
      (nhds (T (fixedPoint H) s)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hbd_tendsto
    rw [Real.dist_eq]
    exact hT_close n
  -- `iter T (n + 1) = T (iter T n)`, so both sequences converge to the same limit.
  have hb' : Filter.Tendsto (fun n => iter T (n + 1) s) Filter.atTop
      (nhds (T (fixedPoint H) s)) := by
    refine hb.congr fun n => ?_
    rw [iter_succ (T := T) n]
  exact tendsto_nhds_unique ha hb'

/-- Any weighted-bounded fixed point of `T` equals the constructed fixed point. -/
lemma fixedPoint_unique (H : WeightedBlackwell ω T β)
    (w : S → ℝ) (hw : WeightedBounded ω w) (hwfix : ∀ s, w s = T w s) :
    w = fixedPoint H := by
  have hwb_diff : WeightedBounded ω (fun s => w s - fixedPoint H s) :=
    hw.sub (fixedPoint_weightedBounded H)
  have hosc_nn := weightedOscillation_nonneg hwb_diff
  have hheqw : w = T w := funext hwfix
  have hheqfp : fixedPoint H = T (fixedPoint H) := funext (fixedPoint_isFixedPt H)
  -- Both `w` and `fixedPoint H` are fixed points, so the oscillation contracts by `β < 1`,
  -- forcing it to zero.
  have hcontract :
      weightedOscillation ω w (fixedPoint H)
        ≤ β * weightedOscillation ω w (fixedPoint H) := by
    conv_lhs => rw [hheqw, hheqfp]
    exact H.oscillation_contraction hw (fixedPoint_weightedBounded H)
  have hosc_zero : weightedOscillation ω w (fixedPoint H) = 0 := by
    have hβ_lt : β < 1 := H.beta_lt_one
    nlinarith
  funext s
  have hpt := abs_sub_le_weightedOscillation_mul ω hwb_diff s
  rw [hosc_zero, zero_mul] at hpt
  have habs : |w s - fixedPoint H s| = 0 := le_antisymm hpt (abs_nonneg _)
  linarith [abs_eq_zero.mp habs]

/-- **Existence of the weighted fixed point.** Every weighted Blackwell operator on a nonempty
state space yields a `FixedPointCertificate`. -/
noncomputable def fixedPointCertificate (H : WeightedBlackwell ω T β) :
    FixedPointCertificate (ω := ω) (T := T) where
  value := fixedPoint H
  weighted_bounded := fixedPoint_weightedBounded H
  fixed := fixedPoint_isFixedPt H
  unique := fixedPoint_unique H

end Existence

end WeightedBlackwell

end Econlib.Optimization.DynamicProgramming
