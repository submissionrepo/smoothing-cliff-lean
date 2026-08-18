/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.CDF
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Nth-order stochastic dominance: The core engine and general relation

This file is the base of the stochastic-dominance hierarchy under `Order/`. It defines, in layers
of increasing strength: The iterated integrated-CDF hierarchy `integratedCDF`; the bare order
relation `IntegratedCDFTower`, the integrated-CDF tower inequality without the lower-tail
integrability witnesses; the per-order finiteness witnesses `CDF.IntegrableTailsUpTo`; and the
witness-bundled general relations `CDF.NOSD` (CDF level) and `NOSD` (on `ProbDist`).

By convention the order count starts at `1`, so `IntegratedCDFTower 1 F G` is pointwise CDF
dominance, `IntegratedCDFTower 2 F G` the bare inequality `∫_{Iic} F ≤ ∫_{Iic} G`, and
`IntegratedCDFTower 0` is `True` (aligning the recursion with the conventional numbering).

## Main definitions

* `integratedCDF` — the `n`-fold integrated CDF primitive.
* `CDF.IntegrableTails`, `CDF.IntegrableTailsUpTo` — the lower-tail finiteness witnesses.
* `IntegratedCDFTower` — the bare integrated-CDF tower inequality.
* `CDF.NOSD`, `NOSD` — `n`th-order stochastic dominance at the CDF level and on `ProbDist ℝ`.

## Main statements

* `CDF.integrableTailsUpTo_two` — at order `2` the witness reduces to `CDF.IntegrableTails`.
* `IntegratedCDFTower.step` — advancing the bare tower inequality one order under local
  integrability.
* `CDF.NOSD.trans`, `CDF.NOSD.refl` — the witness-bundled relation is a preorder.

## Notes

`IntegratedCDFTower` is not the user-facing relation: At order `≥ 2` the bare inequality can hold
vacuously via the Bochner junk value `0` when a CDF fails to be integrable on a lower tail (an
infinite-`E[X⁻]` law). `CDF.NOSD n`/`NOSD n` pair it with `CDF.IntegrableTailsUpTo n`, making a
vacuous comparison inexpressible — those are what consumers should cite. The named specializations
`FOSD` (`= NOSD 1`) and `SOSD` (`= NOSD 2`), together with their order-specific characterization
theory, live in the sibling `Order/FOSD/` and `Order/SOSD/` folders, which build on this core.

## Tags

stochastic dominance, integrated cdf, second-order stochastic dominance, sosd, nosd
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

/-- `integratedCDF n F x` is the `n`-fold integrated CDF primitive of `F`. At level `0`, it is just
`F x`. -/
noncomputable def integratedCDF : ℕ → CDF → ℝ → ℝ
  | 0, F, x => F x
  | n + 1, F, x => ∫ t in Iic x, integratedCDF n F t

/-- The level-`0` integrated CDF is the CDF itself. -/
@[simp] lemma integratedCDF_zero (F : CDF) (x : ℝ) :
    integratedCDF 0 F x = F x := rfl

/-- The level-`(n+1)` integrated CDF is the lower-tail integral of the level-`n` one. -/
@[simp] lemma integratedCDF_succ (n : ℕ) (F : CDF) (x : ℝ) :
    integratedCDF (n + 1) F x = ∫ t in Iic x, integratedCDF n F t := rfl

/-- A CDF has **integrable lower tails** when `⇑F` is integrable on every `Iic x` (equivalently
`E[X⁻] < ∞`). This is the finiteness witness that makes `∫_{Iic x} F` the partial integral rather
than the junk `0` a Bochner integral returns off `Integrable`; second-order dominance bundles it so
a vacuous comparison is inexpressible. -/
def CDF.IntegrableTails (F : CDF) : Prop :=
  ∀ x, IntegrableOn (⇑F) (Iic x)

/-- A continuous CDF that vanishes on `(-∞, 0]` has integrable lower tails: Below any cutoff its
mass sits in a bounded interval. -/
lemma CDF.integrableTails_of_continuous_of_zero {F : CDF} (hF_cont : Continuous ⇑F)
    (hF_zero : ∀ x, x ≤ 0 → ⇑F x = 0) : F.IntegrableTails := by
  intro x
  rcases le_total x 0 with hx | hx
  · -- `F = 0` on all of `Iic x`
    exact (integrableOn_zero (μ := volume) (s := Iic x)).congr_fun
      (fun t ht => (hF_zero t (le_trans ht hx)).symm) measurableSet_Iic
  · -- split `Iic x = Iic 0 ∪ Ioc 0 x`; `F = 0` on the first, continuous-bounded on the second
    rw [← Set.Iic_union_Ioc_eq_Iic hx]
    refine IntegrableOn.union ?_ ?_
    · exact (integrableOn_zero (μ := volume) (s := Iic 0)).congr_fun
        (fun t ht => (hF_zero t ht).symm) measurableSet_Iic
    · exact hF_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- `F.IntegrableTailsUpTo n` is the finiteness witness bundle for order-`n` dominance. Order `n`
compares the level-`(n-1)` integrated CDFs, whose construction nests integrals of
`integratedCDF 0, …, integratedCDF (n-2)`; requiring each of those integrands to be `IntegrableOn`
every lower tail `Iic x` makes every nested comparison a partial integral rather than the Bochner
junk value `0`. The condition is vacuous for `n ≤ 1` (FOSD is pointwise, no integral) and at
`n = 2` reduces to `F.IntegrableTails` (see `integrableTailsUpTo_two`). -/
def CDF.IntegrableTailsUpTo (n : ℕ) (F : CDF) : Prop :=
  ∀ j, j + 2 ≤ n → ∀ x, IntegrableOn (integratedCDF j F) (Iic x)

/-- The order-`0` tail witness is vacuous. -/
@[simp] lemma CDF.integrableTailsUpTo_zero (F : CDF) : F.IntegrableTailsUpTo 0 ↔ True := by
  simp only [CDF.IntegrableTailsUpTo, iff_true]
  intro j hj; omega

/-- The order-`1` tail witness is vacuous: First-order dominance involves no integral. -/
@[simp] lemma CDF.integrableTailsUpTo_one (F : CDF) : F.IntegrableTailsUpTo 1 ↔ True := by
  simp only [CDF.IntegrableTailsUpTo, iff_true]
  intro j hj; omega

/-- At order `2` the tower witness is exactly the single lower-tail witness `CDF.IntegrableTails`:
The only integrand nested in the order-`2` comparison is `integratedCDF 0 F = F`. -/
lemma CDF.integrableTailsUpTo_two (F : CDF) : F.IntegrableTailsUpTo 2 ↔ F.IntegrableTails := by
  constructor
  · intro h x; exact h 0 (by norm_num) x
  · intro h j hj
    obtain rfl : j = 0 := by omega
    exact h

/-- `IntegratedCDFTower n F G` is the bare integrated-CDF tower inequality at order `n` — the
analytic engine, without the lower-tail integrability witnesses (those are bundled in `CDF.NOSD`).
The conventional counting starts at `1`, so `IntegratedCDFTower 1` is pointwise CDF dominance and
`IntegratedCDFTower 2` the bare `∫_{Iic} F ≤ ∫_{Iic} G`. -/
def IntegratedCDFTower : ℕ → CDF → CDF → Prop
  | 0, _, _ => True
  | n + 1, F, G => ∀ x, integratedCDF n F x ≤ integratedCDF n G x

namespace IntegratedCDFTower

/-- The order-`0` tower inequality is vacuously true. -/
@[simp] lemma zero_iff (F G : CDF) : IntegratedCDFTower 0 F G ↔ True := by
  rfl

/-- The order-`(n+1)` tower inequality compares the level-`n` integrated CDFs pointwise. -/
@[simp] lemma succ_iff (n : ℕ) (F G : CDF) :
    IntegratedCDFTower (n + 1) F G ↔ ∀ x, integratedCDF n F x ≤ integratedCDF n G x := by
  rfl

/-- The bare tower inequality is reflexive. -/
lemma refl (n : ℕ) (F : CDF) : IntegratedCDFTower n F F := by
  cases n with
  | zero => trivial
  | succ n => exact fun _ => le_rfl

/-- The bare tower inequality is transitive. -/
lemma trans {n : ℕ} {F G H : CDF} (hFG : IntegratedCDFTower n F G)
    (hGH : IntegratedCDFTower n G H) : IntegratedCDFTower n F H := by
  cases n with
  | zero => trivial
  | succ n => exact fun x => le_trans (hFG x) (hGH x)

/-- Every iterated integrated CDF is nonnegative. -/
lemma integratedCDF_nonneg (n : ℕ) (F : CDF) : ∀ x, 0 ≤ integratedCDF n F x := by
  induction n with
  | zero =>
      intro x
      exact (F.range x).1
  | succ n ih =>
      intro x
      simpa only [integratedCDF] using
        (integral_nonneg_of_ae (ae_restrict_of_ae (ae_of_all _ fun t => ih t)))

/-- Advancing one order: If the level-`n` integrated CDFs are ordered and the right-hand side is
integrable on every `Iic x`, then the bare tower inequality lifts from order `n + 1` to `n + 2`. -/
lemma step {n : ℕ} {F G : CDF} (h : IntegratedCDFTower (n + 1) F G)
    (hG : ∀ x, IntegrableOn (integratedCDF n G) (Iic x)) :
    IntegratedCDFTower (n + 2) F G := by
  intro x
  exact integral_mono_of_nonneg
    (ae_restrict_of_ae (ae_of_all _ fun t => integratedCDF_nonneg n F t))
    (hG x)
    (ae_restrict_of_ae (ae_of_all _ fun t => h t))

/-- At order `1` the tower inequality is pointwise CDF dominance. -/
@[simp] lemma one_iff {F G : CDF} : IntegratedCDFTower 1 F G ↔ ∀ x, F x ≤ G x := by
  rfl

/-- At order `2` the tower inequality is the integrated-CDF comparison `∫_{Iic} F ≤ ∫_{Iic} G`. -/
@[simp] lemma two_iff {F G : CDF} : IntegratedCDFTower 2 F G ↔
    ∀ x, ∫ t in Iic x, F t ≤ ∫ t in Iic x, G t := by
  rfl

end IntegratedCDFTower

/-- **Nth-order stochastic dominance at the CDF level** — the witness-bundled analytic engine.
Pairs the bare integrated-CDF tower inequality `IntegratedCDFTower n F G` with the lower-tail
integrability witnesses `IntegrableTailsUpTo n` for both CDFs, so every nested comparison is
between partial integrals rather than the Bochner junk value `0`. At order `2` this is `CDF.SOSD`
(in `Order/SOSD/Basic.lean`); at order `1` the witnesses are vacuous and it reduces to pointwise
CDF dominance (FOSD). -/
structure CDF.NOSD (n : ℕ) (F G : CDF) : Prop where
  /-- The dominated CDF has the order-`n` tower of integrable lower tails. -/
  tails_left : F.IntegrableTailsUpTo n
  /-- The dominating CDF has the order-`n` tower of integrable lower tails. -/
  tails_right : G.IntegrableTailsUpTo n
  /-- The underlying bare integrated-CDF tower inequality. -/
  tower : IntegratedCDFTower n F G

namespace CDF.NOSD

/-- Assemble `CDF.NOSD` from the tower witnesses and the bare inequality. -/
lemma mk' {n : ℕ} {F G : CDF} (hF : F.IntegrableTailsUpTo n) (hG : G.IntegrableTailsUpTo n)
    (h : IntegratedCDFTower n F G) : CDF.NOSD n F G := ⟨hF, hG, h⟩

/-- The witness-bundled relation is reflexive once the tail witness is supplied. -/
lemma refl {n : ℕ} {F : CDF} (hF : F.IntegrableTailsUpTo n) : CDF.NOSD n F F :=
  ⟨hF, hF, IntegratedCDFTower.refl n F⟩

/-- The witness-bundled relation is transitive. -/
lemma trans {n : ℕ} {F G H : CDF} (h1 : CDF.NOSD n F G) (h2 : CDF.NOSD n G H) : CDF.NOSD n F H :=
  ⟨h1.tails_left, h2.tails_right, IntegratedCDFTower.trans h1.tower h2.tower⟩

end CDF.NOSD

/-- **Nth-order stochastic dominance** on `ProbDist ℝ`, the witness-bundled CDF-level relation
`CDF.NOSD` of the associated CDFs. By the conventional counting `NOSD 1` is FOSD (`nosd_one_iff`)
and `NOSD 2` is `SOSD` (`nosd_two_iff`, definitionally) — both bridges live in
`Order/SOSD/Basic.lean`, downstream of the FOSD/SOSD specializations. The lower-tail finiteness
witnesses are folded in at every order, so a vacuous comparison is inexpressible. -/
def NOSD (n : ℕ) (μ ν : ProbDist ℝ) : Prop :=
  CDF.NOSD n (CDF.ofProbDist μ) (CDF.ofProbDist ν)

end Econlib.Probability
