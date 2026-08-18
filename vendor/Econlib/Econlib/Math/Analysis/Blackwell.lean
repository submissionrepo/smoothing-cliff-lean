/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Blackwell contraction and the bounded fixed-point core

This file proves the bounded Blackwell contraction theorem for operators on plain functions
`(S → ℝ) → S → ℝ`. An operator that is monotone and satisfies discounting with factor `β` admits a
pointwise sup-norm contraction estimate. Bounded plain functions embed into
`BoundedContinuousFunction` over `S` with the discrete topology — a complete metric space — so the
estimate upgrades to a `ContractingWith` certificate for the lifted operator.

The resulting API provides a named bounded fixed point, its fixed-point equation, uniqueness, and a
closed-invariant-set principle for transferring shape properties such as concavity or monotonicity
to the fixed point.

## Main definitions

* `Blackwell.UniformBounded` — uniform boundedness of a real-valued function.
* `Blackwell.liftBddFun` — the operator lifted to the space of bounded continuous functions.
* `Blackwell.bddFixedPoint` — the bounded fixed point, returned as a plain function.

## Main statements

* `Blackwell.abs_sub_le_of_monotone_discounting` — Blackwell's theorem: Monotonicity plus
  discounting imply the `β`-contraction estimate.
* `Blackwell.contractingWith_liftBddFun` — a contraction estimate on bounded plain functions yields
  a Banach contraction certificate on the lifted operator.
* `Blackwell.existsUnique_bdd_fixedPoint` — existence and uniqueness of the bounded fixed point.
* `Blackwell.isFixedPt_mem_of_isClosed` — shape transfer to the fixed point via a closed invariant
  set.
* `ContractingWith.fixedPoint_mem_of_isClosed` — the closed invariant set principle.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76). Corollary 1 to Theorem
  3.2.

## Tags

blackwell, contraction mapping, fixed point, bellman operator, bounded continuous functions
-/

@[expose] public section

/-! ## Closed invariant set principle

Stated for an arbitrary contraction on a complete metric space; the Blackwell layer below
specializes it to lifted operators on `BddFun`. -/

namespace ContractingWith

/-- **Closed Invariant Set Principle.** Let `f` be a contraction on a complete metric space. If `C`
is a nonempty closed subset with `f(C) ⊆ C`, then the unique fixed point lies in `C`. -/
theorem fixedPoint_mem_of_isClosed
    {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f)
    {C : Set α} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo f C C) :
    hf.fixedPoint f ∈ C := by
  obtain ⟨x₀, hx₀⟩ := hC_nonempty
  have hiter : ∀ n, f^[n] x₀ ∈ C := by
    intro n; induction n with
    | zero => exact hx₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hC_inv ih
  have htend := hf.tendsto_iterate_fixedPoint x₀
  exact hC_closed.mem_of_tendsto htend (Filter.Eventually.of_forall hiter)

/-- If `C` is closed and `f`-invariant, then every fixed point of `f` lies in `C`. -/
lemma isFixedPt_mem_of_isClosed
    {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f)
    {C : Set α} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo f C C)
    {x : α} (hx : Function.IsFixedPt f x) :
    x ∈ C := by
  rw [hf.fixedPoint_unique hx]
  exact ContractingWith.fixedPoint_mem_of_isClosed hf hC_nonempty hC_closed hC_inv

end ContractingWith

namespace Blackwell

universe u

variable {S : Type u}

/-! ## Blackwell's sufficient conditions

Stated for operators on plain functions `(S → ℝ) → S → ℝ`, with boundedness carried as an
explicit `UniformBounded` side condition — the form used throughout the dynamic-programing stack. -/

/-- Uniform boundedness of a real-valued function: A single bound `B` with `|v s| ≤ B` across all
of `S`. This is the side condition threaded through the bounded fixed-point core, and the
constant-weight case of `WeightedBounded` from
`Econlib.Optimization.DynamicProgramming.Core.Weighted`. Definitionally the bare existential, so
`obtain ⟨B, hB⟩ := hv` destructures it directly. -/
def UniformBounded (v : S → ℝ) : Prop :=
  ∃ B : ℝ, ∀ s, |v s| ≤ B

/-- The pointwise distance of two bounded functions is bounded above over the state space. -/
lemma bddAbove_range_abs_sub (v w : S → ℝ)
    (hBv : UniformBounded v) (hBw : UniformBounded w) :
    BddAbove (Set.range fun s => |v s - w s|) := by
  obtain ⟨Bv, hBv⟩ := hBv; obtain ⟨Bw, hBw⟩ := hBw
  exact ⟨Bv + Bw, Set.forall_mem_range.mpr fun s =>
    (abs_sub (v s) (w s)).trans (add_le_add (hBv s) (hBw s))⟩

/-- **Blackwell's theorem.** An operator on plain functions that is monotone and satisfies the
discounting property with factor `β` admits the pointwise `β`-contraction estimate in the sup
norm.

Both conditions are required only on bounded inputs, matching how Bellman operators provide them:
Monotonicity `v ≤ w → Tv ≤ Tw`, and discounting `T(v + c) ≤ Tv + βc` for constants `c ≥ 0`. No sign
condition on `β` is needed: Nonnegativity enters only through the discounting hypothesis. -/
theorem abs_sub_le_of_monotone_discounting
    {T : (S → ℝ) → S → ℝ} {β : ℝ}
    (h_mono : ∀ v w : S → ℝ, UniformBounded v → UniformBounded w →
      (∀ s, v s ≤ w s) → ∀ s, T v s ≤ T w s)
    (h_disc : ∀ (v : S → ℝ) (c : ℝ), UniformBounded v → 0 ≤ c →
      ∀ s, T (fun s' => v s' + c) s ≤ T v s + β * c)
    {v w : S → ℝ} (hv : UniformBounded v) (hw : UniformBounded w) (s : S) :
    |T v s - T w s| ≤ β * ⨆ t, |v t - w t| := by
  -- One-sided bound, symmetric in its two arguments: `a ≤ b + ⨆|a - b|` pointwise, so
  -- monotonicity + discounting give `T a s ≤ T b s + β * ⨆|a - b|`. Both halves of the `abs_le`
  -- split below are this bound with the roles of `v`, `w` swapped.
  have one_sided : ∀ a b : S → ℝ, (∃ B : ℝ, ∀ s, |a s| ≤ B) → (∃ B : ℝ, ∀ s, |b s| ≤ B) →
      T a s - T b s ≤ β * ⨆ t, |a t - b t| := by
    intro a b ha hb
    have hbdd := bddAbove_range_abs_sub a b ha hb
    set d := ⨆ t, |a t - b t| with hd_def
    have hd_nonneg : 0 ≤ d := (abs_nonneg _).trans (le_ciSup hbdd s)
    have hle : ∀ t, a t ≤ b t + d := fun t =>
      le_add_of_sub_left_le ((le_abs_self _).trans (le_ciSup hbdd t))
    have hb_add : ∃ B : ℝ, ∀ t, |b t + d| ≤ B := by
      obtain ⟨Bb, hBb⟩ := hb
      exact ⟨Bb + |d|, fun t =>
        (abs_add_le _ _).trans (add_le_add (hBb t) le_rfl)⟩
    have h1 : T a s ≤ T (fun t => b t + d) s := h_mono a _ ha hb_add hle s
    have h2 := h_disc b d hb hd_nonneg s
    linarith
  have hsup_comm : (⨆ t, |w t - v t|) = ⨆ t, |v t - w t| := by simp_rw [abs_sub_comm]
  rw [abs_le]
  refine ⟨?_, one_sided v w hv hw⟩
  have h := one_sided w v hw hv
  rw [hsup_comm] at h
  linarith

/-! ## The BCF bridge

Bounded plain functions `S → ℝ` embed into `BoundedContinuousFunction` over `S` equipped with
the discrete topology — a complete metric space under the sup norm — so Banach's fixed-point
theorem applies to lifted operators. -/

/-- Type alias for `S` with discrete topology, so every function `DState → ℝ` is continuous. This
lets us embed bounded `S → ℝ` functions into `BoundedContinuousFunction DState ℝ`, which is a
complete metric space under the sup norm.

Defined via `def` (not `abbrev`) so that `DState` gets its own topology instance (discrete) without
conflicting with any existing topology on `S`. -/
def DState : Type u := S

noncomputable instance instTopDState : TopologicalSpace (@DState S) := ⊥
instance instDiscDState : DiscreteTopology (@DState S) := ⟨rfl⟩
instance instNonemptyDState [Nonempty S] : Nonempty (@DState S) :=
  ⟨(Classical.arbitrary S : S)⟩

/-- Bounded continuous functions from `DState` to `ℝ` — i.e., bounded functions `S → ℝ` (continuity
is automatic from the discrete topology). -/
abbrev BddFun := BoundedContinuousFunction (@DState S) ℝ

/-- Embed a bounded function `S → ℝ` into the BCF space. -/
noncomputable def toBddFun (f : S → ℝ) (hf : UniformBounded f) :
    BoundedContinuousFunction (@DState S) ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (α := @DState S) (β := ℝ) f (2 * Exists.choose hf)
    (fun x y => by
      simp only [Real.dist_eq]
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub (f x) (f y)
        _ ≤ 2 * Exists.choose hf := by
            linarith [Exists.choose_spec hf x, Exists.choose_spec hf y])

/-- The embedding `toBddFun` coerces back to the original function. -/
lemma toBddFun_coe (f : S → ℝ) (hf : UniformBounded f) :
    (toBddFun f hf : DState → ℝ) = f := by
  ext x; exact BoundedContinuousFunction.mkOfDiscrete_apply _ _ _ _

/-- The embedding `toBddFun` agrees with the original function pointwise. -/
lemma toBddFun_apply (f : S → ℝ) (hf : UniformBounded f) (x : DState) :
    toBddFun f hf x = f x :=
  BoundedContinuousFunction.mkOfDiscrete_apply _ _ _ _

/-- Every bounded continuous function on `DState` is uniformly bounded as a plain function. -/
lemma bddFun_bounded (f : @BddFun S) : ∃ B : ℝ, ∀ s : S, |(f : DState → ℝ) s| ≤ B :=
  ⟨‖f‖, fun s => by
    have := BoundedContinuousFunction.norm_coe_le_norm f (s : DState)
    rwa [Real.norm_eq_abs] at this⟩

variable {T : (S → ℝ) → S → ℝ}

/-- Lift an operator on plain functions to the BCF space, given that it maps bounded functions to
bounded functions. -/
noncomputable def liftBddFun (T : (S → ℝ) → S → ℝ)
    (h_maps : ∀ v : S → ℝ, UniformBounded v → UniformBounded (T v)) :
    @BddFun S → @BddFun S :=
  fun f => toBddFun (T f) (h_maps f (bddFun_bounded f))

variable {h_maps : ∀ v : S → ℝ, UniformBounded v → UniformBounded (T v)}

/-- The lifted operator agrees with `T` pointwise. -/
lemma liftBddFun_apply (f : @BddFun S) (s : DState) :
    liftBddFun T h_maps f s = T f s :=
  toBddFun_apply _ _ _

/-- A pointwise sup-norm contraction estimate on bounded plain functions upgrades to a Banach
contraction certificate for the lifted operator on the BCF space. -/
theorem contractingWith_liftBddFun [Nonempty S] {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (h_contr : ∀ v w : S → ℝ, UniformBounded v → UniformBounded w →
      ∀ s, |T v s - T w s| ≤ β * ⨆ t, |v t - w t|) :
    ContractingWith ⟨β, hβ₀⟩ (liftBddFun T h_maps) := by
  refine ⟨by exact_mod_cast hβ₁, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  show dist (liftBddFun T h_maps f) (liftBddFun T h_maps g) ≤ β * dist f g
  rw [BoundedContinuousFunction.dist_le (mul_nonneg hβ₀ dist_nonneg)]
  intro s
  rw [Real.dist_eq, liftBddFun_apply, liftBddFun_apply]
  calc |T f s - T g s|
      ≤ β * ⨆ t, |(f : DState → ℝ) t - g t| :=
        h_contr f g (bddFun_bounded f) (bddFun_bounded g) s
    _ ≤ β * dist f g := by
        refine mul_le_mul_of_nonneg_left (ciSup_le fun t => ?_) hβ₀
        have := BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) t
        rwa [Real.dist_eq] at this

/-! ## The bounded fixed point and its lemma suite -/

section FixedPoint

variable {K : NNReal}

/-- The unique bounded fixed point of an operator with a Banach contraction certificate on the
lifted BCF space, returned as a plain function `S → ℝ`. -/
noncomputable def bddFixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) : S → ℝ :=
  ⇑(hc.fixedPoint (liftBddFun T h_maps))

/-- The bounded fixed point is uniformly bounded. -/
theorem bddFixedPoint_bounded (hc : ContractingWith K (liftBddFun T h_maps)) :
    UniformBounded (bddFixedPoint hc) :=
  bddFun_bounded _

/-- The bounded fixed point satisfies the fixed-point equation pointwise. -/
theorem bddFixedPoint_isFixedPt (hc : ContractingWith K (liftBddFun T h_maps)) (s : S) :
    bddFixedPoint hc s = T (bddFixedPoint hc) s := by
  have hfp : liftBddFun T h_maps (hc.fixedPoint _) = hc.fixedPoint _ :=
    hc.fixedPoint_isFixedPt
  -- The lifted operator agrees with `T` on coercions definitionally.
  exact (congr_fun (congr_arg DFunLike.coe hfp) s).symm

/-- Bounded fixed points of `T` lift to fixed points of the BCF-lifted operator. -/
theorem isFixedPt_liftBddFun {v : S → ℝ} (hv_bdd : UniformBounded v)
    (hv_fp : ∀ s, v s = T v s) :
    Function.IsFixedPt (liftBddFun T h_maps) (toBddFun v hv_bdd) := by
  change liftBddFun T h_maps (toBddFun v hv_bdd) = toBddFun v hv_bdd
  ext s
  exact (hv_fp s).symm

/-- Uniqueness: Any bounded fixed point of `T` equals `bddFixedPoint`. -/
theorem eq_bddFixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) {v : S → ℝ}
    (hv_bdd : UniformBounded v) (hv_fp : ∀ s, v s = T v s) :
    v = bddFixedPoint hc := by
  have heq : hc.fixedPoint (liftBddFun T h_maps) = toBddFun v hv_bdd :=
    hc.fixedPoint_unique' hc.fixedPoint_isFixedPt (isFixedPt_liftBddFun hv_bdd hv_fp)
  have h : v = ⇑(hc.fixedPoint (liftBddFun T h_maps)) := by
    rw [heq]; exact (toBddFun_coe v hv_bdd).symm
  exact h

/-- Existence and uniqueness of the bounded fixed point, packaged as `∃!`. -/
theorem existsUnique_bdd_fixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) :
    ∃! v : S → ℝ, UniformBounded v ∧ ∀ s, v s = T v s :=
  ⟨bddFixedPoint hc, ⟨bddFixedPoint_bounded hc, bddFixedPoint_isFixedPt hc⟩,
    fun _ ⟨hv_bdd, hv_fp⟩ => eq_bddFixedPoint hc hv_bdd hv_fp⟩

/-- **Shape transfer.** If `C ⊆ BddFun` is nonempty, closed, and invariant under the lifted
operator, then every bounded fixed point of `T` lies in `C`. This is how shape properties
(concavity, monotonicity, decreasing differences, …) transfer to value functions. -/
theorem isFixedPt_mem_of_isClosed (hc : ContractingWith K (liftBddFun T h_maps))
    {C : Set (@BddFun S)} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo (liftBddFun T h_maps) C C)
    {v : S → ℝ} (hv_bdd : UniformBounded v) (hv_fp : ∀ s, v s = T v s) :
    toBddFun v hv_bdd ∈ C :=
  hc.isFixedPt_mem_of_isClosed hC_nonempty hC_closed hC_inv
    (isFixedPt_liftBddFun hv_bdd hv_fp)

end FixedPoint

end Blackwell
