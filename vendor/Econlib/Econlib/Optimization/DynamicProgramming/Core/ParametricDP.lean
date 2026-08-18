/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.BellmanOperator

/-!
# Parametric Dynamic Programing

Layered DP structures of increasing specificity:

* `ParametricDP S A` — generic discounted DP, extending `DetMDP` with strict positivity of `β`
* `DiscreteContDP n A` — mixed state `ℝ × Fin n` with a Markov transition matrix

## Main definitions

* `ParametricDP`: Generic discounted DP, extending `DetMDP` with strict positivity of `β`
* `DiscreteContDP`: DP with mixed continuous-discrete state `ℝ × Fin n` and a Markov transition
  matrix for the discrete component

## Main statements

* `ParametricDP.bellman_mono`: Blackwell's monotonicity condition
* `ParametricDP.bellman_discounting`: Blackwell's discounting condition

## Notes

`ParametricDP` extends `DetMDP` with positivity of `β` (not just non-negativity) to match the
economic convention `β ∈ (0, 1)`. The generic level inherits monotonicity and discounting from
`BellmanOperator.lean` and the Banach contraction from `Bellman.lean`.

## References

* Blackwell, David. 1965. “Discounted Dynamic Programing.” *The Annals of Mathematical Statistics*
  36 (1): 226–35. [https://doi.org/10.1214/aoms/1177700285](https://doi.org/10.1214/aoms/1177700285).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

dynamic programing, bellman operator, markov decision process, discounting
-/

@[expose] public section

open Blackwell Econlib.Probability

namespace Econlib.Optimization.DynamicProgramming

/-! ## Generic Parametric DP -/

/-- A generic parametric DP. This is `DetMDP` with the additional convention that `β > 0` (not just
`β ≥ 0`). For models where `β = 0` is meaningful, use `DetMDP` directly. -/
structure ParametricDP (S : Type*) (A : Type*) [Nonempty S]
    extends DetMDP S A where
  /-- Discount factor is strictly positive. -/
  β_pos : 0 < β

namespace ParametricDP

variable {S : Type*} {A : Type*} [Nonempty S]

/-- The Bellman operator, inherited from `DetMDP`. -/
noncomputable def bellman (D : ParametricDP S A)
    (v : S → ℝ) (s : S) : ℝ :=
  D.toDetMDP.bellmanOperator v s

/-- **Monotonicity (Blackwell condition 1).** `v ≤ w → Tv ≤ Tw`. -/
theorem bellman_mono (D : ParametricDP S A)
    (v w : S → ℝ) (hBw : UniformBounded w)
    (hvw : ∀ s, v s ≤ w s) :
    ∀ s, D.bellman v s ≤ D.bellman w s :=
  bellmanOperator_monotone D.toDetMDP v w hBw hvw

/-- **Discounting (Blackwell condition 2).** `T(v + c) ≤ Tv + βc` for `c ≥ 0`. -/
theorem bellman_discounting (D : ParametricDP S A)
    (v : S → ℝ) (c : ℝ) (hBv : UniformBounded v)
    (hc : 0 ≤ c) :
    ∀ s, D.bellman (fun s' => v s' + c) s ≤
      D.bellman v s + D.β * c :=
  bellmanOperator_discounting D.toDetMDP v c hBv hc

end ParametricDP

/-! ## Mixed Continuous-Discrete State -/

private instance (n : ℕ) [NeZero n] : Nonempty (ℝ × Fin n) :=
  ⟨(0, ⟨0, NeZero.pos n⟩)⟩

/-- A DP with mixed state `ℝ × Fin n`: A continuous component (e.g., wealth) and a discrete
component (e.g., income state) evolving according to a Markov transition matrix.

The transition matrix `trans` need only be a valid probability distribution (non-negative, sums to
1). Positive entries are NOT required at this level. -/
structure DiscreteContDP (n : ℕ) (A : Type*) [NeZero n]
    extends ParametricDP (ℝ × Fin n) A where
  /-- Markov transition matrix for the discrete state. -/
  trans : Fin n → Fin n → ℝ
  /-- Each row is a probability distribution. -/
  trans_prob : ∀ s, (∑ s', trans s s') = 1 ∧
    ∀ s', 0 ≤ trans s s'

namespace DiscreteContDP

variable {n : ℕ} {A : Type*} [NeZero n] (D : DiscreteContDP n A)

/-- Row sums to 1. -/
lemma trans_sum_one (s : Fin n) :
    ∑ s', D.trans s s' = 1 :=
  (D.trans_prob s).1

/-- Entries are non-negative. -/
lemma trans_nonneg (s s' : Fin n) :
    0 ≤ D.trans s s' :=
  (D.trans_prob s).2 s'

/-- Convert a row of the transition matrix to a `FinDist`. -/
noncomputable def toFinDist (s : Fin n) : FinDist (Fin n) where
  pmf := D.trans s
  nonneg := D.trans_nonneg s
  sum_one := D.trans_sum_one s

end DiscreteContDP

end Econlib.Optimization.DynamicProgramming
