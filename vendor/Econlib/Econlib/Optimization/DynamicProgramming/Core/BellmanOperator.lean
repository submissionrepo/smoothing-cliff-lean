/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Blackwell
public import Econlib.Optimization.DynamicProgramming.Core.MDP
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bellman operator for deterministic dynamic programs

This file defines the **Bellman operator** for deterministic MDPs, proves its monotonicity and
discounting properties (Blackwell's sufficient conditions for a contraction), and lifts it to the
space of bounded functions. The bounded lift packages the Bellman equation as a fixed-point problem
for value-function existence and uniqueness.

## Main definitions

* `bellmanOperator`: The Bellman operator `Tv(s) = sup_{a ∈ Γ(s)} [u(s,a) + β·v(f(s,a))]`.
* `bellmanOperatorBddFun`: Lifts the Bellman operator to the space of bounded functions.

## Main statements

* `bellmanOperator_monotone`: The Bellman operator is monotone.
* `bellmanOperator_discounting`: The Bellman operator satisfies discounting with factor `β`.

## References

* Blackwell, David. 1965. “Discounted Dynamic Programing.” *The Annals of Mathematical Statistics*
  36 (1): 226–35. [https://doi.org/10.1214/aoms/1177700285](https://doi.org/10.1214/aoms/1177700285).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

bellman operator, dynamic programing, bounded functions, monotonicity, discounting
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell Econlib.Optimization

universe u_S
variable {S : Type u_S} {A : Type*} [Nonempty S]

/-! ## Bellman Operator -/

namespace UnboundedDetMDP

/-- The **Bellman set** at a state `s` for a continuation value `v`: The set of one-step values
`u(s,a) + β · v(f(s,a))` ranging over feasible actions `a ∈ Γ(s)`. The Bellman operator is its
supremum. -/
def bellmanSet (M : UnboundedDetMDP S A) (v : S → ℝ) (s : S) : Set ℝ :=
  {r : ℝ | ∃ a ∈ M.Γ s, r = M.reward s a + M.β * v (M.transition s a)}

@[simp] lemma mem_bellmanSet (M : UnboundedDetMDP S A) (v : S → ℝ) (s : S) (r : ℝ) :
    r ∈ M.bellmanSet v s ↔ ∃ a ∈ M.Γ s, r = M.reward s a + M.β * v (M.transition s a) :=
  Iff.rfl

/-- The **Bellman operator** for a deterministic MDP:
`(Tv)(s) = sup_{a ∈ Γ(s)} [u(s,a) + β · v(f(s,a))]`.

Defined on `UnboundedDetMDP` (no reward bound needed for the supremum to make sense pointwise); the
bounded `DetMDP` inherits it through the `DetMDP → UnboundedDetMDP` coercion, so dot-notation
`M.bellmanOperator` works for a bounded `M` as well. -/
noncomputable def bellmanOperator (M : UnboundedDetMDP S A) (v : S → ℝ) (s : S) : ℝ :=
  sSup (M.bellmanSet v s)

/-- The Bellman operator is the supremum of the Bellman set. -/
lemma bellmanOperator_eq (M : UnboundedDetMDP S A) (v : S → ℝ) (s : S) :
    M.bellmanOperator v s = sSup (M.bellmanSet v s) := rfl

/-- The Bellman set at a state is nonempty: Feasibility correspondences are nonempty. -/
lemma bellmanSet_nonempty (M : UnboundedDetMDP S A) (v : S → ℝ) (s : S) :
    (M.bellmanSet v s).Nonempty :=
  let ⟨a, ha⟩ := M.Γ_nonempty s; ⟨_, a, ha, rfl⟩

end UnboundedDetMDP

open UnboundedDetMDP

/-! ### Infrastructure lemmas -/

/-- The Bellman set is bounded above when the continuation value is bounded: The reward bound and
`v`'s bound dominate every one-step value. -/
lemma bellmanSet_bddAbove (M : DetMDP S A) (v : S → ℝ)
    (hV : UniformBounded v) (s : S) :
    BddAbove (M.bellmanSet v s) := by
  obtain ⟨Br, hBr⟩ := M.reward_bounded; obtain ⟨Bv, hBv⟩ := hV
  refine ⟨Br + |M.β| * Bv, fun r hr => ?_⟩
  obtain ⟨a, _, rfl⟩ := hr
  have h3 : |M.β * v (M.transition s a)| ≤ |M.β| * Bv := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hBv (M.transition s a)) (abs_nonneg _)
  linarith [hBr s a, le_abs_self (M.reward s a), le_abs_self (M.β * v (M.transition s a))]

/-- The Bellman operator maps uniformly bounded functions to uniformly bounded functions. -/
lemma bellmanOperator_bounded (M : DetMDP S A) (v : S → ℝ)
    (hV : UniformBounded v) :
    UniformBounded (M.bellmanOperator v) := by
  obtain ⟨Br, hBr⟩ := M.reward_bounded; obtain ⟨Bv, hBv⟩ := hV
  have helem : ∀ (s : S) (a : A),
      |M.reward s a + M.β * v (M.transition s a)| ≤ Br + |M.β| * Bv := by
    intro s a
    calc |M.reward s a + M.β * v (M.transition s a)|
        ≤ |M.reward s a| + |M.β * v (M.transition s a)| := abs_add_le _ _
      _ ≤ Br + |M.β| * Bv := by
          rw [abs_mul]
          exact add_le_add (hBr s a) (mul_le_mul_of_nonneg_left (hBv _) (abs_nonneg _))
  refine ⟨Br + |M.β| * Bv, fun s => ?_⟩
  unfold bellmanOperator
  rw [abs_le]
  have hne := M.bellmanSet_nonempty v s
  have hbdd := bellmanSet_bddAbove M v ⟨Bv, hBv⟩ s
  constructor
  · obtain ⟨_, a, ha_mem, rfl⟩ := hne
    linarith [le_csSup hbdd ⟨a, ha_mem, rfl⟩,
              neg_abs_le (M.reward s a + M.β * v (M.transition s a)), helem s a]
  · exact csSup_le hne (fun r hr => by
      obtain ⟨a, _, rfl⟩ := hr
      linarith [le_abs_self (M.reward s a + M.β * v (M.transition s a)), helem s a])

/-! ## Core Properties -/

/-- The Bellman operator is monotone: If `v ≤ w` pointwise, then `Tv ≤ Tw`. -/
lemma bellmanOperator_monotone (M : DetMDP S A) :
    ∀ v w : S → ℝ, UniformBounded w → (∀ s, v s ≤ w s) →
      ∀ s, M.bellmanOperator v s ≤ M.bellmanOperator w s := by
  intro v w hBw hvw s
  unfold bellmanOperator
  apply csSup_le (M.bellmanSet_nonempty v s)
  rintro r ⟨a, ha, rfl⟩
  apply le_csSup_of_le (bellmanSet_bddAbove M w hBw s) ⟨a, ha, rfl⟩
  linarith [mul_le_mul_of_nonneg_left (hvw (M.transition s a)) M.β_nonneg]

/-- The Bellman operator satisfies discounting with factor `β`. -/
lemma bellmanOperator_discounting (M : DetMDP S A) :
    ∀ (v : S → ℝ) (c : ℝ), UniformBounded v → 0 ≤ c →
      ∀ s, M.bellmanOperator (fun s' ↦ v s' + c) s ≤ M.bellmanOperator v s + M.β * c := by
  intro v c hBv hc s
  unfold bellmanOperator
  apply csSup_le (M.bellmanSet_nonempty (fun s' => v s' + c) s)
  rintro r ⟨a, ha, rfl⟩
  have hle : M.reward s a + M.β * v (M.transition s a) ≤ sSup (M.bellmanSet v s) :=
    le_csSup (bellmanSet_bddAbove M v hBv s) ⟨a, ha, rfl⟩
  have : M.reward s a + M.β * (v (M.transition s a) + c) =
      M.reward s a + M.β * v (M.transition s a) + M.β * c := by ring
  linarith

/-! ## BCF Lift

The BCF bridge machinery (`DState`, `BddFun`, `toBddFun`, `liftBddFun`) lives in
`Econlib.Math.Analysis.Blackwell`; here we instantiate the lift for the Bellman operator. -/

/-- Lift the Bellman operator to the BCF space. -/
noncomputable def bellmanOperatorBddFun (M : DetMDP S A) : @BddFun S → @BddFun S :=
  liftBddFun M.bellmanOperator (bellmanOperator_bounded M)

/-- The lifted Bellman operator agrees pointwise with the underlying `bellmanOperator`. -/
lemma bellmanOperatorBddFun_apply (M : DetMDP S A)
    (f : BddFun) (s : DState) :
    bellmanOperatorBddFun M f s = M.bellmanOperator f s :=
  liftBddFun_apply _ _

end Econlib.Optimization.DynamicProgramming
