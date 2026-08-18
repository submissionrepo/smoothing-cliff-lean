/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Optimization.EndogenousChainOptimalPolicy
import Mathlib

/-!
# Parametric DP / endogenous-chain non-vacuity witnesses

Compile-time semantic witnesses for the **parametric / endogenous-chain** dynamic-programming layer
(`ParametricDP`, `DiscreteContDP`, `EndogenousPolicyProblem`). Each abstract claim — the parametric
Bellman operator's monotonicity and discounting, the discrete-continuous transition distribution's
legality, and the continuous single-valued optimal selection — is forced through a concrete model.

## Anchoring models

* A tiny concrete `ParametricDP (Fin 2) (Fin 2)` and a `DiscreteContDP 2 (Fin 2)` for the generic
  Bellman/transition-distribution facts.
* The hand-solved `EndogenousPolicyProblem 2` of
  `EconlibExamples.Optimization.EndogenousChainOptimalPolicy` (objective `-(w')² + w·w'`, optimal
  policy `w' = w/2`) for the continuous single-valued selection stack.

## What each block catches

* **Parametric Bellman** — `ParametricDP.bellman_mono` / `_discounting` (exact endpoint values
  `T 0 = 1`, `T 1 = 3/2`, discounting gap `= β·c = 1`).
* **Discrete-continuous transition** — the transition-distribution facts on an *asymmetric* matrix
  (`trans_sum_one` / `trans_nonneg` / `toFinDist` with all four entries).
* **Endogenous-chain selection** — `argmaxCorr_uhc` / `argmaxCorr_nonempty` / `exists_policy` /
  `policyFun_continuous` / `policyFun_mem` / `policyFun_mem_Icc` confirm the continuous
  single-valued optimal selection. Its non-degeneracy is forced through the closed-form witnesses
  `policyFun_eq_half` (on `[0,1]`), `policyFun_not_constant`, and `policyFun_mem_Ioo`, so a
  degenerate constant-feasible-singleton would not pass.
-/

noncomputable section

namespace EconlibTest.Optimization.DPParametric

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Econlib.Probability Set Filter Topology

/-! ## Parametric DP + discrete-continuous transition + endogenous chain -/

/-- A tiny concrete `ParametricDP (Fin 2) (Fin 2)`: One feasible action, reward `1`, identity-ish
transition, discount `β = 1/2 > 0`. Carrier for the generic Bellman monotonicity/discounting facts
(which `DetMDP` provides but `ParametricDP` re-exposes under the `β > 0` convention). -/
private def paramDP : ParametricDP (Fin 2) (Fin 2) where
  Γ := fun _ => Set.univ
  reward := fun _ _ => 1
  transition := fun s _ => s
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => Set.univ_nonempty
  reward_bounded := ⟨1, fun _ _ => by norm_num⟩
  β_pos := by norm_num

/-- The Bellman set of `paramDP` at any continuation `v` and state `s` is the singleton
`{1 + (1/2)·v s}`: the only feasible action is in `univ`, the reward is the constant `1`, and the
transition `fun s _ => s` keeps the state, so the continuation is evaluated at `v s`. -/
private theorem paramDP_bellmanSet_eq (v : Fin 2 → ℝ) (s : Fin 2) :
    paramDP.toDetMDP.bellmanSet v s = {1 + (1 / 2) * v s} := by
  ext r
  simp only [UnboundedDetMDP.mem_bellmanSet, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, -, rfl⟩; rfl
  · rintro rfl; exact ⟨0, Set.mem_univ _, rfl⟩

/-- The Bellman operator of `paramDP` at `v` and `s` is exactly `1 + (1/2)·v s` (supremum of a
singleton). -/
private theorem paramDP_bellman_apply (v : Fin 2 → ℝ) (s : Fin 2) :
    paramDP.bellman v s = 1 + (1 / 2) * v s := by
  rw [ParametricDP.bellman, UnboundedDetMDP.bellmanOperator_eq, paramDP_bellmanSet_eq,
    csSup_singleton]

/-- **`ParametricDP.bellman_mono`: Monotonicity of the parametric Bellman operator, with exact
endpoint values.** Raising the continuation from `0` to `1` (pointwise) raises the image from
`T 0 s = 1` to `T 1 s = 3/2`; the inequality `1 ≤ 3/2` is therefore *strict*, not merely weak. A
Bellman operator that ignored or underweighted the continuation would not move the image at all. -/
private theorem param_bellman_mono (s : Fin 2) :
    paramDP.bellman (fun _ => 0) s = 1 ∧ paramDP.bellman (fun _ => 1) s = 3 / 2 ∧
      paramDP.bellman (fun _ => 0) s < paramDP.bellman (fun _ => 1) s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [paramDP_bellman_apply]; norm_num
  · rw [paramDP_bellman_apply]; norm_num
  · rw [paramDP_bellman_apply, paramDP_bellman_apply]; norm_num

/-- **`ParametricDP.bellman_discounting` pins the modulus to *exactly* `β = 1/2`.**
Adding `c = 2 ≥ 0`
to the continuation raises the image from `T 0 s = 1` to `T (0+2) s = 2` — a gap of *exactly*
`β · c = (1/2)·2 = 1`, attained with equality, not a loose upper bound. A continuation underweighted
by `β²` instead of `β` would give a strictly smaller gap and fail this equality. -/
private theorem param_bellman_discounting (s : Fin 2) :
    paramDP.bellman (fun s' => (fun _ => (0 : ℝ)) s' + 2) s = 2 ∧
      paramDP.bellman (fun s' => (fun _ => (0 : ℝ)) s' + 2) s -
        paramDP.bellman (fun _ => 0) s = paramDP.β * 2 := by
  constructor
  · rw [paramDP_bellman_apply]; norm_num
  · rw [paramDP_bellman_apply, paramDP_bellman_apply]; simp [paramDP]

/-- A tiny concrete `DiscreteContDP 2 (Fin 2)`: Mixed state `ℝ × Fin 2`, with an explicit `2×2`
Markov transition matrix `[[3/4, 1/4], [1/3, 2/3]]` (a legal, **asymmetric** probability matrix:
row `0` is `(3/4, 1/4)`, row `1` is `(1/3, 2/3)`, with distinct off-diagonal entries `1/4 ≠ 1/3`).
The asymmetry is deliberate — a transposed transition matrix or a swap of the current/successor
argument would change at least one of the four entries and be caught by `disc_toFinDist_apply`. -/
private def discDP : DiscreteContDP 2 (Fin 2) where
  Γ := fun _ => Set.univ
  reward := fun _ _ => 1
  transition := fun s _ => s
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => Set.univ_nonempty
  reward_bounded := ⟨1, fun _ _ => by norm_num⟩
  β_pos := by norm_num
  trans := fun s s' => (![![3 / 4, 1 / 4], ![1 / 3, 2 / 3]] : Fin 2 → Fin 2 → ℝ) s s'
  trans_prob := fun s => ⟨by fin_cases s <;> norm_num [Fin.sum_univ_two],
    fun s' => by fin_cases s <;> fin_cases s' <;> norm_num⟩

/-- **`DiscreteContDP.trans_sum_one`: Each transition row sums to one.** Both rows of the asymmetric
matrix are legal distributions: `3/4 + 1/4 = 1` and `1/3 + 2/3 = 1`. -/
private theorem disc_trans_sum_one (s : Fin 2) : ∑ s', discDP.trans s s' = 1 :=
  discDP.trans_sum_one s

/-- Both row sums spelled out: row `0` is `3/4 + 1/4 = 1`, row `1` is `1/3 + 2/3 = 1`. A
transposed matrix would still have both column sums equal to `1` here, but the *entrywise* check
`disc_toFinDist_apply` below distinguishes the rows. -/
private theorem disc_trans_row_sums :
    discDP.trans 0 0 + discDP.trans 0 1 = 1 ∧ discDP.trans 1 0 + discDP.trans 1 1 = 1 := by
  constructor <;> simp [discDP] <;> norm_num

/-- **`DiscreteContDP.trans_nonneg`: Transition entries are non-negative.** -/
private theorem disc_trans_nonneg (s s' : Fin 2) : 0 ≤ discDP.trans s s' :=
  discDP.trans_nonneg s s'

/-- **`DiscreteContDP.toFinDist`: A transition row is a legal `FinDist`, with all four entries
checked.** Row `0` is `(3/4, 1/4)` and row `1` is `(1/3, 2/3)`. Because the off-diagonal entries
differ (`1/4 ≠ 1/3`), this entrywise check rejects a transposed matrix or a current/successor swap —
e.g. a transpose would report `toFinDist 0` as `(3/4, 1/3)`, failing the second conjunct. -/
private theorem disc_toFinDist_apply :
    (discDP.toFinDist 0) 0 = 3 / 4 ∧ (discDP.toFinDist 0) 1 = 1 / 4 ∧
      (discDP.toFinDist 1) 0 = 1 / 3 ∧ (discDP.toFinDist 1) 1 = 2 / 3 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ### Endogenous-chain optimal selection (`-(w')² + w·w'`, policy `w/2`) -/

private abbrev endoP : EndogenousPolicyProblem 2 :=
  EconlibExamples.Optimization.EndogenousChainOptimalPolicy.problem

/-- **`EndogenousPolicyProblem.argmaxCorr_nonempty`: An optimal choice exists.** Weierstrass on the
nonempty compact feasible interval with a continuous objective. -/
private theorem endo_argmaxCorr_nonempty (s s' : Fin 2) (w : ℝ) :
    (endoP.argmaxCorr s s' w).Nonempty :=
  endoP.argmaxCorr_nonempty s s' w

/-- **`EndogenousPolicyProblem.argmaxCorr_uhc`: The optimal-choice correspondence is u.h.c.**
Berge's maximum theorem on the concrete problem — the upper hemicontinuity that, with
single-valuedness, yields a continuous selection. -/
private theorem endo_argmaxCorr_uhc (s s' : Fin 2) :
    UpperHemicontinuous (endoP.argmaxCorr s s') :=
  endoP.argmaxCorr_uhc s s'

/-- **`EndogenousPolicyProblem.argmaxCorr_subsingleton`: The optimal choice is unique.** Strict
concavity of `-(w')² + w·w'` makes the maximizer a singleton — the uniqueness input upgrading the
u.h.c. correspondence to a function. -/
private theorem endo_argmaxCorr_subsingleton (s s' : Fin 2) (w : ℝ) :
    (endoP.argmaxCorr s s' w).Subsingleton :=
  endoP.argmaxCorr_subsingleton s s' w

/-- **`EndogenousPolicyProblem.exists_policy`: A continuous single-valued optimal policy exists.**
The genuine production of the continuous selection from the u.h.c. + subsingleton argmax. -/
private theorem endo_exists_policy (s s' : Fin 2) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ w, g w ∈ endoP.argmaxCorr s s' w :=
  endoP.exists_policy s s'

/-- **`EndogenousPolicyProblem.policyFun_continuous`: The optimal policy is a continuous function.**
The selected feasible maximizer varies continuously in the endogenous state `w`. (Its closed form on
the state interval is identified by `endo_policyFun_eq_half` below.) -/
private theorem endo_policyFun_continuous (s s' : Fin 2) :
    Continuous (endoP.policyFun s s') :=
  endoP.policyFun_continuous s s'

/-- **`EndogenousPolicyProblem.policyFun_mem`: The optimal policy selects a maximizer.** Genuine
optimality — the policy value lies in the argmax at every state. -/
private theorem endo_policyFun_mem (s s' : Fin 2) (w : ℝ) :
    endoP.policyFun s s' w ∈ endoP.argmaxCorr s s' w :=
  endoP.policyFun_mem s s' w

/-- **`EndogenousPolicyProblem.policyFun_mem_Icc`: The selected feasible maximizer lies in the state
interval `[w_min, w_max] = [0, 1]`** for *every* real `w` — this is the input making the policy
induce a well-defined Markov chain on `[w_min, w_max] × Fin n`. Note the claim is interval
*membership of the selected maximizer*, which the feasibility clipping guarantees globally; it is
**not** the assertion `w/2 ∈ [0, 1]` for all real `w` (false, e.g. at `w = 3`). The closed form
`policy = w/2` holds only on the relevant state interval (`endo_policyFun_eq_half`). -/
private theorem endo_policyFun_mem_Icc (s s' : Fin 2) (w : ℝ) :
    endoP.policyFun s s' w ∈ Icc endoP.w_min endoP.w_max :=
  endoP.policyFun_mem_Icc s s' w

/-! ### Closed-form / non-degeneracy of the selected policy

The continuity/membership endpoints above also hold for a degenerate constant feasible singleton.
The imported example computes the *closed form* of the selected maximizer and certifies it is a
genuinely non-constant, interior-when-positive selection; we exercise those facts here so the
non-degeneracy is forced through this test, not merely asserted in the example. -/

/-- **`policyFun_eq_half`: The selected policy is *exactly* `w' = w / 2` on the state interval.**
On `w ∈ [0, 1]` the downward parabola `-(w')² + w·w'` peaks at `w' = w/2 ∈ [0, 1]`, so the unique
feasible maximizer is `w/2` — the genuine closed form, derived in the example from `policyFun_mem` +
argmax-uniqueness, not assumed. Outside `[0, 1]` the policy is clipped by feasibility (so the global
`w/2` reading of `endo_policyFun_mem_Icc` is *not* claimed). -/
private theorem endo_policyFun_eq_half (s s' : Fin 2) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    endoP.policyFun s s' w = w / 2 :=
  EconlibExamples.Optimization.EndogenousChainOptimalPolicy.policyFun_eq_half s s' hw

/-- **`policyFun_not_constant`: The optimal policy is genuinely non-constant** in the endogenous
state — value `0` at `w = 0` (`policyFun_zero`) and `1/2` at `w = 1` (`policyFun_one`). This rules
out the degenerate constant-feasible-singleton case the bare continuity/membership witnesses would
also satisfy: the induced Markov chain is not a disguised constant map. -/
private theorem endo_policyFun_not_constant (s s' : Fin 2) :
    endoP.policyFun s s' 0 ≠ endoP.policyFun s s' 1 :=
  EconlibExamples.Optimization.EndogenousChainOptimalPolicy.policyFun_not_constant s s'

/-- **`policyFun_mem_Ioo`: The selected maximizer is *interior* to `[0, 1]`** for every strictly
positive state `w ∈ (0, 1]`: `w/2 ∈ (0, 1)`. So the optimum is never a corner solution on the
positive part of the state interval (at `w = 0` it is the boundary point `0`). -/
private theorem endo_policyFun_mem_Ioo (s s' : Fin 2) {w : ℝ} (hw : w ∈ Ioc (0 : ℝ) 1) :
    endoP.policyFun s s' w ∈ Ioo (0 : ℝ) 1 :=
  EconlibExamples.Optimization.EndogenousChainOptimalPolicy.policyFun_mem_Ioo s s' hw

end EconlibTest.Optimization.DPParametric
