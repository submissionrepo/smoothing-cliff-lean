/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Environment
public import Econlib.Probability.ContDist.Product

/-!
# Symmetric IID auctions: Environment and ex-post allocations

The multi-agent counterpart of the single-agent `ScreeningEnv` (Myerson 1981). In the **symmetric
independent-private-values** model, `n` bidders draw their values independently from one shared
continuous distribution; their joint law is the IID product `base.dist.piMeasure n` on `Fin n → ℝ`.

An **ex-post allocation rule** assigns each bidder a probability of receiving the item as a
function of the full profile, subject to feasibility (`∑ᵢ xᵢ ≤ 1`: At most one unit is allocated)
and nonnegativity. The **reduced-form interim allocation** `interimAlloc X i` integrates out the
other bidders' types; it is an `AllocationRule` for the shared `ScreeningEnv`.

## Main definitions

* `AuctionEnv` — `n` bidders (`0 < n`) sharing a `ScreeningEnv` (`base`).
* `AuctionEnv.jointLaw` — the IID product measure on profiles `Fin n → ℝ`.
* `ExPostAlloc` — a feasible, nonnegative, measurable ex-post allocation.
* `ExPostAlloc.interimAlloc` — bidder `i`'s reduced-form interim allocation (conditional
  expectation over the other bidders' types).
* `ExPostAlloc.reducedAlloc` — bidder `i`'s interim allocation as an `AllocationRule base`.

## Main statements

* `AuctionEnv.map_eval_jointLaw` — marginalizing the joint IID law along a coordinate recovers the
  shared per-bidder law.
* `AuctionEnv.ae_forall_mem_Icc` — almost every profile lies in the type box.
* `AuctionEnv.integrable_comp_eval` — a bounded measurable function of one bidder's type is
  integrable against the joint law.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, symmetric, independent private values, reduced form, Myerson
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

/-- A **symmetric IID auction environment**: `n` bidders (with `0 < n`) whose values are drawn
independently from one shared single-parameter environment `base`. -/
structure AuctionEnv where
  /-- The number of bidders. -/
  n : ℕ
  /-- There is at least one bidder. -/
  hn : 0 < n
  /-- The shared per-bidder screening environment (symmetric, identical distributions). -/
  base : ScreeningEnv

namespace AuctionEnv

variable (A : AuctionEnv)

/-- A profile of bidder types. -/
abbrev Profile := Fin A.n → ℝ

/-- The joint law of the `n` IID bidder values: The product of `base.dist` over `Fin n`. -/
def jointLaw : Measure A.Profile := A.base.dist.piMeasure A.n

@[simp] lemma jointLaw_def : A.jointLaw = A.base.dist.piMeasure A.n := rfl

instance : IsProbabilityMeasure A.jointLaw :=
  A.base.dist.isProbabilityMeasure_piMeasure A.n

/-- Marginalizing the joint IID law along bidder `i`'s coordinate recovers the shared per-bidder
law. -/
lemma map_eval_jointLaw (i : Fin A.n) :
    Measure.map (Function.eval i) A.jointLaw = A.base.dist.toMeasure := by
  haveI : IsProbabilityMeasure A.base.dist.toMeasure := A.base.dist.toMeasure_isProbability
  rw [jointLaw_def, ContDist.piMeasure, Measure.pi_map_eval]
  have hprod : (∏ _j ∈ Finset.univ.erase i, A.base.dist.toMeasure Set.univ) = 1 :=
    Finset.prod_eq_one fun _ _ => measure_univ
  rw [hprod, one_smul]

/-- **Almost every profile lies in the type box.** Under the joint IID law, almost surely every
bidder's value lies in the type interval (the shared density vanishes off it). -/
lemma ae_forall_mem_Icc :
    ∀ᵐ θ ∂A.jointLaw, ∀ j, θ j ∈ Icc A.base.θlo A.base.θhi := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  rw [ae_iff]
  have heq : {θ : A.Profile | ¬ θ j ∈ Icc A.base.θlo A.base.θhi}
      = Function.eval j ⁻¹' (Icc A.base.θlo A.base.θhi)ᶜ := rfl
  rw [heq, ← Measure.map_apply (measurable_pi_apply j) measurableSet_Icc.compl,
    A.map_eval_jointLaw j]
  exact A.base.toMeasure_compl_Icc_eq_zero

/-- **Almost every profile lies in the open type box.** Under the joint IID law, almost surely
every bidder's value lies in the *open* type interval: The closed and open intervals differ only at
the two endpoints, which carry no mass (the shared law is atomless). -/
lemma ae_forall_mem_Ioo :
    ∀ᵐ θ ∂A.jointLaw, ∀ j, θ j ∈ Ioo A.base.θlo A.base.θhi := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  rw [ae_iff]
  have heq : {θ : A.Profile | ¬ θ j ∈ Ioo A.base.θlo A.base.θhi}
      = Function.eval j ⁻¹' (Ioo A.base.θlo A.base.θhi)ᶜ := rfl
  rw [heq, ← Measure.map_apply (measurable_pi_apply j) measurableSet_Ioo.compl,
    A.map_eval_jointLaw j]
  exact A.base.toMeasure_compl_Ioo_eq_zero

/-- **A bounded function of one bidder's type is integrable against the joint law.** A function `g`
of bidder `i`'s type alone, measurable and bounded on the type interval, is integrable against the
joint law: The shared density vanishes off the interval, so only the bounded part matters. -/
lemma integrable_comp_eval {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hbound : ∀ t ∈ Icc A.base.θlo A.base.θhi, |g t| ≤ C) (i : Fin A.n) :
    Integrable (fun θ => g (θ i)) A.jointLaw := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbound A.base.θlo A.base.θlo_mem_types)
  -- Integrability against the per-bidder law: off the interval the density kills `g`, on the
  -- interval `g` is bounded.
  have hdg : Integrable (fun t => A.base.dist.density t * g t) := by
    have heq : (fun t => A.base.dist.density t * g t)
        = fun t => (Icc A.base.θlo A.base.θhi).indicator g t * A.base.dist.density t := by
      funext t
      by_cases ht : t ∈ Icc A.base.θlo A.base.θhi
      · rw [Set.indicator_of_mem ht, mul_comm]
      · rw [Set.indicator_of_notMem ht, A.base.density_eq_zero_of_notMem ht, zero_mul, mul_zero]
    rw [heq]
    refine A.base.dist.integrable.bdd_mul
      (f := (Icc A.base.θlo A.base.θhi).indicator g) (c := C)
      ((hg.indicator measurableSet_Icc).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs]
    by_cases ht : t ∈ Icc A.base.θlo A.base.θhi
    · rw [Set.indicator_of_mem ht]; exact hbound t ht
    · rw [Set.indicator_of_notMem ht, abs_zero]; exact hC0
  have hg_toMeasure : Integrable g A.base.dist.toMeasure :=
    (A.base.dist.integrable_toMeasure_iff).mpr hdg
  have hiff := integrable_map_measure (g := g) (f := Function.eval i)
    (by rw [A.map_eval_jointLaw i]; exact hg_toMeasure.aestronglyMeasurable)
    (measurable_pi_apply i).aemeasurable
  rw [A.map_eval_jointLaw i] at hiff
  exact hiff.mp hg_toMeasure

end AuctionEnv

/-- An **ex-post allocation rule** for an auction: Each bidder's probability of winning as a
function of the full type profile. Feasibility (`∑ᵢ xᵢ ≤ 1`) and nonnegativity make `x θ` a
sub-probability vector — at most one unit of the good is awarded. Measurability is carried so the
reduced-form integrals are well-defined, rather than the silent `0` a Bochner integral returns on a
non-integrable integrand. -/
structure ExPostAlloc (A : AuctionEnv) where
  /-- The allocation: `x θ i` is bidder `i`'s winning probability at profile `θ`. -/
  x : A.Profile → Fin A.n → ℝ
  /-- Allocations are nonnegative. -/
  nonneg : ∀ θ i, 0 ≤ x θ i
  /-- At most one unit is allocated. -/
  feasible : ∀ θ, ∑ i, x θ i ≤ 1
  /-- Each bidder's allocation is measurable in the profile. -/
  measurable : ∀ i, Measurable (fun θ => x θ i)

namespace ExPostAlloc

variable {A : AuctionEnv} (X : ExPostAlloc A)

/-- Each bidder's ex-post allocation is at most one. -/
lemma le_one (θ : A.Profile) (i : Fin A.n) : X.x θ i ≤ 1 :=
  le_trans (Finset.single_le_sum (fun j _ => X.nonneg θ j) (Finset.mem_univ i)) (X.feasible θ)

/-- The integrand of the reduced form, `θ ↦ x (update θ i t) i`, is measurable. -/
lemma measurable_interim_integrand (i : Fin A.n) (t : ℝ) :
    Measurable (fun θ => X.x (update θ i t) i) :=
  (X.measurable i).comp measurable_update_left

/-- The integrand of the reduced form is integrable against the joint law. -/
lemma integrable_interim_integrand (i : Fin A.n) (t : ℝ) :
    Integrable (fun θ => X.x (update θ i t) i) A.jointLaw := by
  refine ⟨(X.measurable_interim_integrand i t).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) (ae_of_all _ fun θ => ?_)⟩
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [X.nonneg (update θ i t) i], X.le_one (update θ i t) i⟩

/-- **Reduced-form interim allocation** of bidder `i` at type `t`: The expected probability that
`i` wins, conditional on `θ i = t`, averaged over the other bidders' types. -/
def interimAlloc (i : Fin A.n) (t : ℝ) : ℝ :=
  ∫ θ, X.x (update θ i t) i ∂A.jointLaw

lemma interimAlloc_def (i : Fin A.n) (t : ℝ) :
    X.interimAlloc i t = ∫ θ, X.x (update θ i t) i ∂A.jointLaw := rfl

lemma interimAlloc_nonneg (i : Fin A.n) (t : ℝ) : 0 ≤ X.interimAlloc i t :=
  integral_nonneg (fun θ => X.nonneg (update θ i t) i)

lemma interimAlloc_le_one (i : Fin A.n) (t : ℝ) : X.interimAlloc i t ≤ 1 := by
  calc X.interimAlloc i t
      ≤ ∫ _θ, (1 : ℝ) ∂A.jointLaw :=
        integral_mono (X.integrable_interim_integrand i t) (integrable_const 1)
          (fun θ => X.le_one (update θ i t) i)
    _ = 1 := by simp

/-- Bidder `i`'s reduced-form interim allocation packaged as an `AllocationRule` for the shared
`ScreeningEnv`. -/
def reducedAlloc (i : Fin A.n) : AllocationRule A.base where
  x := X.interimAlloc i
  nonneg := X.interimAlloc_nonneg i
  le_one := X.interimAlloc_le_one i

@[simp] lemma reducedAlloc_x (i : Fin A.n) (t : ℝ) :
    (X.reducedAlloc i).x t = X.interimAlloc i t := rfl

end ExPostAlloc

end Econlib.MechanismDesign.Transfers.SingleParameter
