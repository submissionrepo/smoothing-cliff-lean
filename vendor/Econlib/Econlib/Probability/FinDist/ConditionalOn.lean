/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Conditioning a finite distribution on a `Set α`

This file defines conditioning primitives for finite distributions on events `e : Set α`. The
event-mass accessor `FinDist.probEvent` names `d.probEvent e` alongside the existing pointwise
`d.pmf x`, and the conditional distributions distinguish positive-mass events from totalized
junk-on-zero conventions.

## Main definitions

* `FinDist.probEvent`: Probability mass of an event `e : Set α`.
* `FinDist.condProb`: Pointwise real-valued conditional pmf. Returns `d.pmf x / d.probEvent e` when
  `x ∈ e ∧ 0 < d.probEvent e`, else `0`.
* `FinDist.conditionalOnOrSelf`: Totalized distribution-valued conditional. Falls back to `d`
  itself when `d.probEvent e = 0`.
* `FinDist.conditionalOn`: Distribution-valued **conditional distribution**, gated on positive
  event mass.

## Main statements

* `FinDist.condProb_sum_one_of_pos`: On positive event mass the conditional pmf sums to one.
* `FinDist.conditionalOn_apply_of_pos`: The conditional distribution evaluates to `condProb`.
* `FinDist.conditionalOnOrSelf_eq_self_of_zero`: On zero event mass the totalized conditional
  degenerates to the prior.

## Notes

`conditionalOn` carries a positive-event-mass hypothesis `0 < d.probEvent e`, the regime in which
it is a conditional distribution supported on `e`; the characterization lemma
`conditionalOn_apply_of_pos` holds under this hypothesis. `conditionalOnOrSelf` is the totalized
convention: It falls back to `d` itself when `d.probEvent e = 0` (junk-value, analogous to Bochner
integrals returning `0` on non-integrable inputs). A value read under the `…OrSelf` name on a
zero-mass event is the prior, not a conditional, so consumers must gate on positivity before
interpreting it as one.

## Tags

probability, finite distributions, conditional distribution, conditioning
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Probability mass of an event `e : Set α` under a finite distribution. -/
noncomputable def probEvent (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x

/-- Event mass is nonnegative. -/
lemma probEvent_nonneg (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    0 ≤ d.probEvent e :=
  Finset.sum_nonneg (fun x _ => d.nonneg x)

/-- Event mass as the filter-sum of masses over the points of `e`. -/
lemma probEvent_eq_sum_filter (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    d.probEvent e = ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x := rfl

/-- Indicator (full-`univ`) form of the event mass: `∑ x, if x ∈ e then d x else 0`. This is the
`findist_eval` evaluation form — with no `Finset.filter`, `Fin.sum_univ_n` applies directly, so
worked examples reduce a concrete `probEvent` to arithmetic without a `Finset.sum_filter` step. -/
@[findist_eval] lemma probEvent_eq_sum_ite (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] :
    d.probEvent e = ∑ x, if x ∈ e then d x else 0 := by
  rw [probEvent_eq_sum_filter, Finset.sum_filter]

/-- Pointwise real-valued conditional probability: `d.condProb e x = d.pmf x / d.probEvent e` when
`x ∈ e` and `0 < d.probEvent e`; `0` otherwise (junk-on-zero-measure). The coordinate-fiber
conditional `FinDist.condProbD` is the dependent-product wrapper over this. -/
noncomputable def condProb (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] (x : α) : ℝ :=
  if x ∈ e ∧ 0 < d.probEvent e then d x / d.probEvent e else 0

/-- Definitional `if`-form of `condProb`, in the `findist_eval` set: `simp [findist_eval]` unfolds
a concrete conditional pmf, then evaluates the `x ∈ e` guard and the `probEvent` normalizer (via
`probEvent_eq_sum_ite`) coordinatewise. Opt-in only (not global `@[simp]`), so proofs reasoning
abstractly about `condProb` are not silently expanded. -/
@[findist_eval] lemma condProb_eq_ite (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] (x : α) :
    d.condProb e x = if x ∈ e ∧ 0 < d.probEvent e then d x / d.probEvent e else 0 := rfl

/-- The pointwise conditional pmf is nonnegative. -/
lemma condProb_nonneg (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)] (x : α) :
    0 ≤ d.condProb e x := by
  unfold condProb
  split_ifs with h
  · exact div_nonneg (d.nonneg x) (le_of_lt h.2)
  · exact le_refl _

/-- The conditional pmf vanishes off the conditioning event. -/
lemma condProb_eq_zero_of_notMem (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hx : x ∉ e) : d.condProb e x = 0 :=
  if_neg fun h => hx h.1

/-- On positive event mass, the conditional pmf at a point of `e` is `d x / d.probEvent e`. -/
lemma condProb_eq_of_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hx : x ∈ e) (hpos : 0 < d.probEvent e) :
    d.condProb e x = d x / d.probEvent e := by
  unfold condProb
  rw [if_pos ⟨hx, hpos⟩]

/-- On positive event mass, the conditional pmf sums to one. -/
lemma condProb_sum_one_of_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hpos : 0 < d.probEvent e) :
    ∑ x : α, d.condProb e x = 1 := by
  -- The summand is nonzero only on `x ∈ e`; on that set it equals `d x / d.probEvent e`.
  have hrestrict : ∑ x : α, d.condProb e x =
      ∑ x ∈ Finset.univ.filter (fun x : α => x ∈ e), d x / d.probEvent e := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    -- `hpos` collapses the `condProb` guard to membership, matching the filter predicate.
    simp [condProb, hpos]
  rw [hrestrict, ← Finset.sum_div]
  simpa [probEvent_eq_sum_filter] using div_self (ne_of_gt hpos)

/-- On zero event mass, the conditional pmf is identically zero, so its sum is zero. -/
lemma condProb_sum_zero_of_not_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hnot : ¬ 0 < d.probEvent e) :
    ∑ x : α, d.condProb e x = 0 := by
  -- Every summand carries the `0 < probEvent` guard, which `hnot` falsifies.
  exact Finset.sum_eq_zero fun x _ => if_neg fun h => hnot h.2

/-- Totalized distribution-valued conditional: When `0 < d.probEvent e`, the conditional `FinDist`
supported on `e`. Falls back to `d` itself when `d.probEvent e = 0` (junk-value; consumers gate on
positivity before using). The positivity-gated form is `FinDist.conditionalOn`, which carries the
positive-mass hypothesis. -/
noncomputable def conditionalOnOrSelf (d : FinDist α) (e : Set α)
    [DecidablePred (· ∈ e)] : FinDist α :=
  if h : 0 < d.probEvent e then
    ⟨d.condProb e, d.condProb_nonneg e, d.condProb_sum_one_of_pos e h⟩
  else d

/-- Distribution-valued **conditional distribution**, gated on positive event mass.

The hypothesis `h_pos : 0 < d.probEvent e` is the positivity gate: It forces the regime in which
the result is a conditional distribution supported on `e`, and in which the characterization lemma
`conditionalOn_apply_of_pos` is valid. On the value level this agrees with `conditionalOnOrSelf`
(see the bridge lemma `conditionalOn_eq_orSelf`); the hypothesis means this name cannot be formed
on a zero-mass event. -/
noncomputable def conditionalOn (d : FinDist α) (e : Set α)
    [DecidablePred (· ∈ e)]
    -- `h_pos` is the positivity gate; load-bearing for `conditionalOn_apply_of_pos`.
    (_h_pos : 0 < d.probEvent e) : FinDist α :=
  d.conditionalOnOrSelf e

/-- The positivity-gated conditional agrees on the value level with the totalized `…OrSelf`
convention; the only difference is the load-bearing positivity gate. Applied explicitly (not
`@[simp]`) so that proofs working on `conditionalOn` are not silently rewritten to the totalized
form. -/
lemma conditionalOn_eq_orSelf (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (h_pos : 0 < d.probEvent e) :
    d.conditionalOn e h_pos = d.conditionalOnOrSelf e := rfl

/-- On positive event mass, the conditional distribution evaluates to the pointwise conditional pmf
`condProb`. In the `findist_eval` set so `simp [findist_eval]` rewrites a `conditionalOn` mass to
`condProb` (which then unfolds via `condProb_eq_ite`); the positivity gate `hpos` is bound by the
`conditionalOn` term, so it need not be re-supplied. -/
@[findist_eval] lemma conditionalOn_apply_of_pos (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hpos : 0 < d.probEvent e) (x : α) :
    (d.conditionalOn e hpos) x = d.condProb e x := by
  unfold conditionalOn conditionalOnOrSelf
  rw [dif_pos hpos]

/-- When the conditioning event has positive prior mass, the conditional distribution agrees with
the pointwise conditional pmf at `x`. -/
lemma conditionalOn_prob_eq (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    {x : α} (hpos : 0 < d.probEvent e) :
    (d.conditionalOn e hpos) x = d.condProb e x :=
  d.conditionalOn_apply_of_pos e hpos x

/-- When the conditioning event has zero prior mass, the totalized conditional degenerates to the
prior itself (junk-on-zero-measure convention). -/
lemma conditionalOnOrSelf_eq_self_of_zero (d : FinDist α) (e : Set α) [DecidablePred (· ∈ e)]
    (hzero : d.probEvent e = 0) :
    d.conditionalOnOrSelf e = d := by
  unfold conditionalOnOrSelf
  exact dif_neg (hzero ▸ lt_irrefl _)

/-- **Conditional event probability as a ratio.** On a positive-mass conditioning event `A`, the
mass that the conditional distribution `d.conditionalOn A` assigns to an event `B` is
`d.probEvent (A ∩ B) / d.probEvent A` — the elementary definition of `Pr(B ∣ A)`. -/
lemma probEvent_conditionalOn (d : FinDist α) (A B : Set α)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A ∩ B)]
    (hpos : 0 < d.probEvent A) :
    (d.conditionalOn A hpos).probEvent B = d.probEvent (A ∩ B) / d.probEvent A := by
  -- On positive prior mass, the conditional pmf is `if x ∈ A then d x / d.probEvent A else 0`.
  have hval : ∀ x : α, (d.conditionalOn A hpos) x =
      if x ∈ A then d x / d.probEvent A else 0 := by
    intro x
    rw [conditionalOn_apply_of_pos d A hpos x]
    unfold condProb
    simp [hpos]
  -- Expand `probEvent B` and substitute the pointwise conditional value.
  rw [probEvent_eq_sum_filter]
  simp_rw [hval]
  -- The `x ∈ A` branch survives; collect it as a sum over the intersection filter, then divide.
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_div,
    Finset.filter_filter]
  -- Identify `(filter (·∈B)).filter (·∈A)` with `filter (·∈ A ∩ B)`.
  rw [probEvent_eq_sum_filter (e := A ∩ B)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro x _
  simp [Set.mem_inter_iff, and_comm]

end FinDist
end Econlib.Probability
