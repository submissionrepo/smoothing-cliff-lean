/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.ContinuousSelection
public import Econlib.Optimization.MaximumTheorem
public import Econlib.Probability.Markov.Ergodic

/-!
# From an optimal policy to an endogenous Markov chain

`Econlib.Probability.EndogenousMarkovChain` packages the long-run dynamics induced by a given
continuous policy. This file supplies the optimality content: A model-agnostic optimization problem
whose optimal policy is continuous and from which an `EndogenousMarkovChain` is built.

At each current state `w` and shock transition `(s, s')`, the agent chooses the next-period
continuous state `w'` from a feasible set `feasible w s s' ⊆ [w_min, w_max]` to maximize a strictly
concave objective `obj w s s' ·`. Strict concavity forces the maximizer to be unique, Berge's
maximum theorem makes the maximizer correspondence upper hemicontinuous, and a continuous-selection
argument upgrades these to a continuous optimal policy. Feeding this policy to
`EndogenousMarkovChain` yields a stationary distribution of the optimally controlled economy.

## Main definitions

* `EndogenousPolicyProblem` — the optimization data (bounds, shock transition, feasible
  correspondence, strictly concave objective, with the regularity hypotheses Berge needs).
* `EndogenousPolicyProblem.policyFun` — the continuous optimal policy extracted via continuous
  selection.
* `EndogenousPolicyProblem.toEndogenousMarkovChain` — the induced chain.

## Main statements

* `EndogenousPolicyProblem.policyFun_mem` — the policy selects from the argmax.
* `EndogenousPolicyProblem.exists_stationary` — a stationary distribution under the optimal policy
  exists.

## Notes

The interface is model-agnostic: It asks only for the optimization primitives and their regularity,
not for any particular dynamic-programing structure (e.g. `CollateralDP`). A concrete model
satisfies the interface by exhibiting its feasible correspondence and objective.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

dynamic programing, markov chain, optimal policy, stationary distribution, continuous selection
-/

@[expose] public section

namespace Econlib.Optimization

open Set Econlib.Probability

/-- A model-agnostic dynamic optimization problem on `[w_min, w_max] × Fin n` whose optimal policy
induces an `EndogenousMarkovChain`.

At current continuous state `w`, current shock `s`, and next shock `s'`, the agent chooses the next
continuous state `w'` from `feasible w s s'` to maximize `obj w s s' ·`. The regularity fields are
exactly the hypotheses of Berge's maximum theorem plus strict concavity (for uniqueness of the
maximizer); together they make the optimal policy a continuous function. -/
structure EndogenousPolicyProblem (n : ℕ) where
  /-- Lower bound on the continuous state. -/
  w_min : ℝ
  /-- Upper bound on the continuous state. -/
  w_max : ℝ
  /-- The bounds are well-ordered. -/
  hw : w_min < w_max
  /-- Exogenous Markov transition for the discrete shock. -/
  discrete_trans : Fin n → FinDist (Fin n)
  /-- Feasible next-state correspondence at `(w, s, s')`. -/
  feasible : ℝ → Fin n → Fin n → Set ℝ
  /-- Objective to maximize over the next continuous state. -/
  obj : ℝ → Fin n → Fin n → ℝ → ℝ
  /-- Feasible choices stay inside the compact interval (yields `policy_range`). -/
  feasible_subset : ∀ w s s', feasible w s s' ⊆ Icc w_min w_max
  /-- The feasible set is nonempty (so a maximizer exists). -/
  feasible_nonempty : ∀ w s s', (feasible w s s').Nonempty
  /-- The feasible set is compact (so a maximizer is attained). -/
  feasible_compact : ∀ w s s', IsCompact (feasible w s s')
  /-- The feasible correspondence is upper hemicontinuous in the current state. -/
  feasible_uhc : ∀ s s', UpperHemicontinuous (fun w => feasible w s s')
  /-- The feasible correspondence is lower hemicontinuous in the current state. -/
  feasible_lhc : ∀ s s', LowerHemicontinuous (fun w => feasible w s s')
  /-- The objective is jointly continuous in the current and next continuous state. -/
  obj_cont : ∀ s s', Continuous (fun p : ℝ × ℝ => obj p.1 s s' p.2)
  /-- The objective is strictly concave in the choice variable (so the maximizer is unique). -/
  obj_strictConcave : ∀ w s s', StrictConcaveOn ℝ (feasible w s s') (fun w' => obj w s s' w')

namespace EndogenousPolicyProblem

variable {n : ℕ} (P : EndogenousPolicyProblem n)

/-- The objective slice `w' ↦ obj w s s' w'` is continuous. -/
lemma obj_slice_continuous (w : ℝ) (s s' : Fin n) :
    Continuous (fun w' => P.obj w s s' w') :=
  (P.obj_cont s s').comp (continuous_const.prodMk continuous_id)

/-- The optimal-choice correspondence at shock pair `(s, s')`, as a function of the current
state. -/
def argmaxCorr (s s' : Fin n) : ℝ → Set ℝ :=
  fun w => argmax (fun w' => P.obj w s s' w') (P.feasible w s s')

/-- A maximizer exists (Weierstrass: Continuous objective on a nonempty compact feasible set). -/
lemma argmaxCorr_nonempty (s s' : Fin n) (w : ℝ) : (P.argmaxCorr s s' w).Nonempty :=
  argmax_nonempty (P.feasible_compact w s s') (P.feasible_nonempty w s s')
    (P.obj_slice_continuous w s s').continuousOn

/-- The maximizer is unique (strict concavity). -/
lemma argmaxCorr_subsingleton (s s' : Fin n) (w : ℝ) : (P.argmaxCorr s s' w).Subsingleton :=
  argmax_subsingleton_of_strictConcaveOn (P.obj_strictConcave w s s')

/-- The optimal-choice correspondence is upper hemicontinuous (Berge's maximum theorem). -/
lemma argmaxCorr_uhc (s s' : Fin n) : UpperHemicontinuous (P.argmaxCorr s s') :=
  argmax_upperHemicontinuous (P.obj_cont s s') (P.feasible_uhc s s') (P.feasible_lhc s s')
    (fun w => P.feasible_compact w s s') (fun w => P.feasible_nonempty w s s')

/-- A continuous optimal policy exists: The unique maximizer varies continuously with the state. -/
lemma exists_policy (s s' : Fin n) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ w, g w ∈ P.argmaxCorr s s' w :=
  (P.argmaxCorr_uhc s s').exists_continuous_selection
    (P.argmaxCorr_nonempty s s') (P.argmaxCorr_subsingleton s s')

/-- The continuous optimal policy at shock pair `(s, s')`. -/
noncomputable def policyFun (s s' : Fin n) : ℝ → ℝ :=
  Classical.choose (P.exists_policy s s')

/-- The optimal policy is continuous. -/
lemma policyFun_continuous (s s' : Fin n) : Continuous (P.policyFun s s') :=
  (Classical.choose_spec (P.exists_policy s s')).1

/-- The optimal policy selects a maximizer of the objective. -/
lemma policyFun_mem (s s' : Fin n) (w : ℝ) : P.policyFun s s' w ∈ P.argmaxCorr s s' w :=
  (Classical.choose_spec (P.exists_policy s s')).2 w

/-- The optimal policy keeps the continuous state in `[w_min, w_max]`: A maximizer lies in the
feasible set, which is contained in the interval. -/
lemma policyFun_mem_Icc (s s' : Fin n) (w : ℝ) :
    P.policyFun s s' w ∈ Icc P.w_min P.w_max :=
  P.feasible_subset w s s' (P.policyFun_mem s s' w).1

/-- **The endogenous Markov chain induced by the optimal policy.** Its continuous component evolves
according to `policyFun`, the unique optimal choice, which is continuous and interval-valued. -/
noncomputable def toEndogenousMarkovChain : EndogenousMarkovChain n where
  w_min := P.w_min
  w_max := P.w_max
  hw := P.hw
  discrete_trans := P.discrete_trans
  policy := fun w s s' => P.policyFun s s' w
  policy_range := fun w s s' _ _ => P.policyFun_mem_Icc s s' w
  policy_cont := fun s s' => (P.policyFun_continuous s s').continuousOn

/-- **Stationary distribution under the optimal policy exists.** The optimally controlled economy
on `[w_min, w_max] × Fin n` admits an invariant probability measure, obtained by feeding the
continuous optimal policy to `EndogenousMarkovChain.exists_stationary`. -/
theorem exists_stationary [NeZero n] :
    ∃ μ : ProbDist (Icc P.w_min P.w_max × Fin n),
      ProbabilityTheory.Kernel.Invariant P.toEndogenousMarkovChain.toKernel μ.toMeasure :=
  P.toEndogenousMarkovChain.exists_stationary

end EndogenousPolicyProblem

end Econlib.Optimization
