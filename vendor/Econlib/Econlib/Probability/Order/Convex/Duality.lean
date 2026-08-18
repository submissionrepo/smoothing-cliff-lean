/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Convex.Basic

/-!
# Convex-order duality certificates

A reusable weak-duality layer for persuasion problems over probability laws on a compact real
interval `[a, b]` ordered by the **convex order** (the mean-preserving-spread order; Rothschild and
Stiglitz 1970). The primal maximizes a payoff's expectation over laws below a prior `G` in convex
order, and the dual minimizes the prior-expectation of a continuous convex price majorizing the
payoff (Dworczak and Martini 2019). The full strong-duality theorem is not asserted here; this file
provides weak duality together with optimality and contact-set certificates that hold whenever a
primal and a dual candidate attain a common value.

## Main definitions

* `PayoffOnIcc a b` — a payoff/price function bundled with its continuity on `[a, b]`.
* `IsConvexMajorantOnIcc a b v p` — `p` is convex on `[a, b]` and dominates `v` there.
* `contactSet a b v p` — the set where payoff equals price.
* `primalValueConvexOrder a b G v`, `dualValueConvexOrder a b G v` — the primal and dual values.
* `dualObjectiveConvexOrder G p` — the prior-expectation of a candidate price.

## Main statements

* `weakDuality`, `primalValueSet_le_dualValueSet` — a feasible payoff expectation is at most the
  dual price objective.
* `supportsOn_contactSet_of_eq_dualCertificate` — a feasible law meeting a dual price with equal
  value is supported on the contact set where payoff equals price.

## Notes

This module is complementary to `Econlib.Optimization.StrongDuality`, which handles scalar
inequality constraints over a compact convex subset of a real topological module via Slater
separation. Convex-order persuasion problems instead optimize over probability laws ordered by
infinitely many convex test inequalities, so they share only the primal / dual-objective /
dual-value naming discipline and the weak-duality certificates.

`ProbDist.expect` is a raw Bochner integral, so a nonmeasurable or nonintegrable function silently
returns the junk value `0`. Bundling `ContinuousOn` into `PayoffOnIcc` makes `expect` against a law
supported on `[a, b]` integrable (`ProbDist.integrable_of_supportsOn_Icc`), so a primal or dual
value cannot be formed from a junk expectation.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

convex order, mean-preserving spread, weak duality, convex majorant, contact set, persuasion
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability.Order.Convex.Duality

open Econlib.Probability

/-- A payoff/price function packaged with its continuity on `[a, b]`.

The bundled continuity is the regularity that makes `expect` a true integral: Continuity on the
compact `[a, b]` together with a law supported there yields integrability
(`ProbDist.integrable_of_supportsOn_Icc`). Because the value objects below consume `PayoffOnIcc`
rather than a bare `ℝ → ℝ`, a primal or dual value cannot be formed from a nonintegrable (junk)
expectation. -/
structure PayoffOnIcc (a b : ℝ) where
  /-- The underlying payoff/price function. -/
  toFun : ℝ → ℝ
  /-- The function is continuous on `[a, b]`, which makes `expect` a true integral against any law
  supported on `[a, b]`. -/
  continuousOn : ContinuousOn toFun (Set.Icc a b)

namespace PayoffOnIcc

instance {a b : ℝ} : CoeFun (PayoffOnIcc a b) (fun _ => ℝ → ℝ) := ⟨PayoffOnIcc.toFun⟩

@[simp] lemma coe_mk {a b : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    ⇑(PayoffOnIcc.mk f hf) = f := rfl

end PayoffOnIcc

/-- A continuous convex price function `p` that majorizes a payoff `v` on `[a,b]`.

The price's continuity on `[a, b]` is carried by the `PayoffOnIcc` bundle, so this predicate only
records the convexity and majorization constraints. -/
structure IsConvexMajorantOnIcc (a b : ℝ) (v p : PayoffOnIcc a b) : Prop where
  /-- The price function is convex on `[a, b]`. -/
  convex : ConvexOn ℝ (Icc a b) p
  /-- The price function dominates the payoff on `[a, b]`. -/
  majorizes : ∀ x ∈ Icc a b, v x ≤ p x

/-- Contact set between a payoff and a convex price on `[a,b]`. -/
def contactSet (a b : ℝ) (v p : PayoffOnIcc a b) : Set ℝ :=
  {x | x ∈ Icc a b ∧ v x = p x}

/-- Feasible expectation values for the convex-order primal problem. -/
def primalValueSet (a b : ℝ) (G : ProbDist ℝ) (v : PayoffOnIcc a b) : Set ℝ :=
  {y | ∃ π : ProbDist ℝ, ConvexOrderOnIcc a b π G ∧ y = π.expect v}

/-- Primal value: The order-theoretic supremum of payoff expectations over laws below `G` in convex
order.

This is a raw `sSup` over `primalValueSet`; it reads as "maximize payoff expectation" only when
that set is nonempty and bounded above (in a `ConditionallyCompleteLinearOrder` the sup of an empty
or unbounded set is junk). Those well-posedness conditions are exactly what the certificate layer
supplies — see `weakDuality` (the set is bounded above by any dual value, and is attained when a
feasible law meets a dual price with equal value) and `supportsOn_contactSet_of_eq_dualCertificate`
(such a tight law concentrates on the contact set). -/
noncomputable def primalValueConvexOrder (a b : ℝ) (G : ProbDist ℝ) (v : PayoffOnIcc a b) : ℝ :=
  sSup (primalValueSet a b G v)

/-- Dual objective at a candidate convex price: Expected price under the prior law. -/
noncomputable def dualObjectiveConvexOrder (G : ProbDist ℝ) (p : PayoffOnIcc a b) : ℝ :=
  G.expect p

/-- Feasible price values for the convex-order dual problem. -/
def dualValueSet (a b : ℝ) (G : ProbDist ℝ) (v : PayoffOnIcc a b) : Set ℝ :=
  {y | ∃ p : PayoffOnIcc a b, IsConvexMajorantOnIcc a b v p ∧
    y = dualObjectiveConvexOrder G p}

/-- Dual value: The order-theoretic infimum of expected prices over convex majorants of `v` under
the prior law.

This is a raw `sInf` over `dualValueSet`; it reads as "minimize the expected price" only when that
set is nonempty and bounded below (in a `ConditionallyCompleteLinearOrder` the inf of an empty or
unbounded set is junk). Those well-posedness conditions are supplied by the certificate lemmas —
see `weakDuality` and `primalValueSet_le_dualValueSet` (every dual value bounds the primal set from
above, so the dual set is nonempty whenever a convex majorant exists). -/
noncomputable def dualValueConvexOrder (a b : ℝ) (G : ProbDist ℝ) (v : PayoffOnIcc a b) : ℝ :=
  sInf (dualValueSet a b G v)

/-- The contact set is measurable because both functions are continuous on `[a,b]`. -/
lemma measurableSet_contactSet {a b : ℝ} (v p : PayoffOnIcc a b) :
    MeasurableSet (contactSet a b v p) := by
  unfold contactSet
  exact (isClosed_Icc.isClosed_eq v.continuousOn p.continuousOn).measurableSet

/-- A convex majorant bounds the expected payoff under any law supported on `[a,b]`. -/
lemma expect_payoff_le_expect_price_of_supportsOn
    {a b : ℝ} {π : ProbDist ℝ} {v p : PayoffOnIcc a b}
    (hπ : π.supportsOn (Icc a b))
    (hmajor : ∀ x ∈ Icc a b, v x ≤ p x) :
    π.expect v ≤ π.expect p := by
  have hv_int : Integrable v π.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hπ v.continuousOn
  have hp_int : Integrable p π.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hπ p.continuousOn
  have hle_ae : ∀ᵐ x ∂π.toMeasure, v x ≤ p x := by
    filter_upwards [π.ae_mem_of_supportsOn measurableSet_Icc hπ] with x hx
    exact hmajor x hx
  exact integral_mono_ae hv_int hp_int hle_ae

/-- Weak duality for a fixed feasible posterior law and a fixed convex price. -/
theorem weakDuality
    {a b : ℝ} {G π : ProbDist ℝ} {v p : PayoffOnIcc a b}
    (hπ : ConvexOrderOnIcc a b π G)
    (hp : IsConvexMajorantOnIcc a b v p) :
    π.expect v ≤ dualObjectiveConvexOrder G p :=
  (expect_payoff_le_expect_price_of_supportsOn hπ.support_left hp.majorizes).trans
    (hπ.convex_expect_le p hp.convex p.continuousOn)

/-- Membership form of weak duality for primal and dual feasible-value sets. -/
theorem primalValueSet_le_dualValueSet
    {a b : ℝ} {G : ProbDist ℝ} {v : PayoffOnIcc a b} :
    ∀ ⦃x y : ℝ⦄, x ∈ primalValueSet a b G v → y ∈ dualValueSet a b G v → x ≤ y := by
  intro x y hx hy
  rcases hx with ⟨π, hπ, rfl⟩
  rcases hy with ⟨p, hp, rfl⟩
  exact weakDuality hπ hp

/-- If a feasible law attains a convex price certificate, it is supported on the contact set where
payoff equals price. -/
theorem supportsOn_contactSet_of_eq_dualCertificate
    {a b : ℝ} {G π : ProbDist ℝ} {v p : PayoffOnIcc a b}
    (hπ : ConvexOrderOnIcc a b π G)
    (hp : IsConvexMajorantOnIcc a b v p)
    (heq : π.expect v = dualObjectiveConvexOrder G p) :
    π.supportsOn (contactSet a b v p) := by
  have hv_int : Integrable v π.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hπ.support_left v.continuousOn
  have hp_int : Integrable p π.toMeasure :=
    ProbDist.integrable_of_supportsOn_Icc hπ.support_left p.continuousOn
  have hnonneg : 0 ≤ᵐ[π.toMeasure] fun x => p x - v x := by
    filter_upwards [π.ae_mem_of_supportsOn measurableSet_Icc hπ.support_left] with x hx
    exact sub_nonneg.mpr (hp.majorizes x hx)
  have hdiff_int : Integrable (fun x => p x - v x) π.toMeasure := hp_int.sub hv_int
  have hprice_eq_π : π.expect p = G.expect p := by
    have hle : π.expect p ≤ G.expect p := hπ.convex_expect_le p hp.convex p.continuousOn
    have hpayoff_le_price : π.expect v ≤ π.expect p :=
      expect_payoff_le_expect_price_of_supportsOn hπ.support_left hp.majorizes
    -- `G.expect p = π.expect v` by the equality certificate, so the price bound transfers
    refine le_antisymm hle ?_
    rw [show G.expect p = π.expect v from heq.symm]
    exact hpayoff_le_price
  have hzero_int : ∫ x, (p x - v x) ∂π.toMeasure = 0 := by
    rw [integral_sub hp_int hv_int]
    change π.expect p - π.expect v = 0
    rw [hprice_eq_π]
    exact sub_eq_zero.mpr (show G.expect p = π.expect v from heq.symm)
  have hzero_ae : (fun x => p x - v x) =ᵐ[π.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hdiff_int).mp hzero_int
  have hcontact_ae : ∀ᵐ x ∂π.toMeasure, x ∈ contactSet a b v p := by
    filter_upwards
      [π.ae_mem_of_supportsOn measurableSet_Icc hπ.support_left, hzero_ae] with x hxI hx0
    unfold contactSet
    refine ⟨hxI, ?_⟩
    have : p x - v x = 0 := by simpa using hx0
    linarith
  exact ProbDist.supportsOn_of_ae_mem (measurableSet_contactSet v p) hcontact_ae

end Econlib.Probability.Order.Convex.Duality
