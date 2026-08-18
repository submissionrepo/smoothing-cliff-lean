/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Convex.StdSimplex
public import Econlib.Probability.FinDist.ConditionalOn
public import Econlib.Probability.FinDist.Expect
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# `FinDist` ↔ `stdSimplex` bridge and the dependent-product API

`FinDist α` carries the same data as a point of Mathlib's `stdSimplex ℝ α`. This file provides the
`toSimplex`/`ofSimplex` equivalence, the topology induced from the simplex embedding (under which
`FinDist α` is a compact Hausdorff first-countable space with continuous evaluation), and the
dependent-product distribution `productD` over `∀ i, β i` together with its coordinate marginals
and conditionals.

## Main definitions

* `FinDist.toSimplex` / `FinDist.ofSimplex` — the data-preserving maps between `FinDist α` and
  `stdSimplex ℝ α`.
* `FinDist.homeoSimplex` — the homeomorphism `FinDist α ≃ₜ stdSimplex ℝ α`.
* `FinDist.productD` — the product distribution over a dependent finite profile space `∀ i, β i`.
* `FinDist.marginalD` — the coordinate marginal mass `d.marginalD i b` of value `b` at coordinate
  `i`.
* `FinDist.condProbD` — the pointwise conditional probability given coordinate `i` has value `b`.

## Main statements

* `FinDist.continuous_pmf` / `FinDist.continuous_pmf_apply` — evaluation is continuous.
* `FinDist.marginalD_sum_one` — the coordinate marginals sum to one.
* `FinDist.probEvent_coordFiber` — the mass of a coordinate fiber is the coordinate marginal.
* `FinDist.condProbD_sum_one_of_pos` — the coordinate conditional sums to one on a positive-mass
  fiber.

## Notes

The instances `CompactSpace`, `T2Space`, and `FirstCountableTopology` on `FinDist α` are
transported from the simplex; together they give sequential compactness for finite distribution
spaces. `condProbD` is junk-on-zero-measure: It returns `0` everywhere when the conditioning
marginal is not positive (`condProbD_eq_zero_of_not_pos`), matching `condProb`.

## Tags

probability, finite distributions, simplex, product distribution, marginal, conditional probability
-/

@[expose] public section

open BigOperators Topology

namespace Econlib.Probability
namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Bridge to Mathlib's standard simplex -/

/-- Embed `FinDist α` into the standard probability simplex. -/
def toSimplex (d : FinDist α) : stdSimplex ℝ α := ⟨d.pmf, d.nonneg, d.sum_one⟩

/-- Recover a `FinDist α` from a point on the standard simplex. -/
def ofSimplex (s : stdSimplex ℝ α) : FinDist α := ⟨s.1, s.2.1, s.2.2⟩

/-- The underlying function of `d.toSimplex` is the pmf of `d`. -/
@[simp] lemma toSimplex_coe (d : FinDist α) : ((d.toSimplex : stdSimplex ℝ α) : α → ℝ) = d.pmf :=
  rfl

/-- The pmf of `ofSimplex s` is the underlying function of `s`. -/
@[simp] lemma ofSimplex_pmf (s : stdSimplex ℝ α) : (FinDist.ofSimplex s).pmf = (s : α → ℝ) := rfl

/-- `ofSimplex` is a left inverse of `toSimplex`. -/
@[simp] lemma ofSimplex_toSimplex (d : FinDist α) : ofSimplex (toSimplex d) = d := by ext a; rfl

/-- `ofSimplex` is a right inverse of `toSimplex`. -/
@[simp] lemma toSimplex_ofSimplex (s : stdSimplex ℝ α) : toSimplex (ofSimplex s) = s := by
  ext a; rfl

/-! ## Topology induced from the simplex embedding -/

instance : TopologicalSpace (FinDist α) := TopologicalSpace.induced toSimplex inferInstance

/-- The embedding `toSimplex` is continuous (it carries the induced topology). -/
lemma continuous_toSimplex : Continuous (toSimplex : FinDist α → stdSimplex ℝ α) :=
  continuous_induced_dom

/-- `FinDist α` is homeomorphic to the compact standard simplex. -/
def homeoSimplex : FinDist α ≃ₜ stdSimplex ℝ α where
  toFun := toSimplex
  invFun := ofSimplex
  left_inv := ofSimplex_toSimplex
  right_inv := toSimplex_ofSimplex
  continuous_toFun := continuous_toSimplex
  continuous_invFun := continuous_induced_rng.mpr (by
    have h : (toSimplex ∘ ofSimplex : stdSimplex ℝ α → stdSimplex ℝ α) = id :=
      funext toSimplex_ofSimplex
    rw [h]; exact continuous_id)

instance : CompactSpace (FinDist α) := homeoSimplex.symm.compactSpace

/-- `FinDist α` is Hausdorff, transported from the simplex. -/
instance : T2Space (FinDist α) := homeoSimplex.isEmbedding.t2Space

/-- `FinDist α` is first-countable, transported from the simplex; with compactness this gives
sequential compactness. -/
instance : FirstCountableTopology (FinDist α) :=
  homeoSimplex.isInducing.firstCountableTopology

/-- The embedding `toSimplex` is injective. -/
lemma toSimplex_injective : Function.Injective (toSimplex : FinDist α → stdSimplex ℝ α) :=
  homeoSimplex.injective

/-- Evaluation `d ↦ d.pmf` is continuous. -/
lemma continuous_pmf : Continuous (fun d : FinDist α => d.pmf) :=
  continuous_subtype_val.comp continuous_toSimplex

/-- Pointwise evaluation `d ↦ d.pmf a` is continuous. -/
lemma continuous_pmf_apply (a : α) : Continuous (fun d : FinDist α => d.pmf a) :=
  (continuous_apply a).comp continuous_pmf

end FinDist

/-! ## Dependent products of finite distributions -/

namespace FinDist

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- Product distribution over a dependent finite profile space. -/
noncomputable def productD (d : ∀ i, FinDist (β i)) : FinDist (∀ i, β i) where
  pmf x := ∏ i, d i (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (d i).nonneg (x i)
  sum_one := by
    have h : ∑ x : (∀ i, β i), ∏ i, d i (x i) = ∏ i, ∑ b : β i, d i b := by
      rw [← Fintype.piFinset_univ]
      exact (Finset.prod_univ_sum (fun _ => Finset.univ) (fun i b => d i b)).symm
    rw [h]
    exact Finset.prod_eq_one (fun i _ => (d i).sum_one)

/-- Marginal mass of a coordinate value under a distribution on dependent finite profiles. -/
noncomputable def marginalD (d : FinDist (∀ i, β i)) (i : ι) (b : β i) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : (∀ i, β i) => x i = b), d x

/-- The coordinate marginal is nonnegative. -/
lemma marginalD_nonneg (d : FinDist (∀ i, β i)) (i : ι) (b : β i) :
    0 ≤ marginalD d i b :=
  Finset.sum_nonneg fun x _ => d.nonneg x

/-- The coordinate marginals at coordinate `i` sum to one. -/
lemma marginalD_sum_one (d : FinDist (∀ i, β i)) (i : ι) :
    ∑ b : β i, marginalD d i b = 1 := by
  simp_rw [marginalD]
  rw [Finset.sum_fiberwise Finset.univ (fun x : (∀ i, β i) => x i) (fun x => d x)]
  exact d.sum_one

/-- The event mass of a coordinate fiber `{y | y i = b}` is the coordinate marginal. This bridges
the generic conditioning API (`probEvent`/`condProb`) to the dependent-product marginal. -/
lemma probEvent_coordFiber (d : FinDist (∀ i, β i)) (i : ι) (b : β i) :
    d.probEvent {y | y i = b} = d.marginalD i b := by
  unfold probEvent marginalD
  exact Finset.sum_congr (Finset.filter_congr fun x _ => Iff.rfl) fun x _ => rfl

/-- Pointwise conditional probability of a profile given coordinate `i` has value `b`: `condProb`
at the coordinate fiber `{y | y i = b}`. Returns `d x / d.marginalD i b` when `x i = b` and the
marginal is positive, and `0` otherwise (junk-on-zero-measure, matching `condProb`). -/
noncomputable def condProbD (d : FinDist (∀ i, β i)) (i : ι) (b : β i) (x : ∀ j, β j) : ℝ :=
  d.condProb {y | y i = b} x

/-- The coordinate conditional is nonnegative. -/
lemma condProbD_nonneg (d : FinDist (∀ i, β i)) (i : ι) (b : β i) (x : ∀ j, β j) :
    0 ≤ d.condProbD i b x :=
  d.condProb_nonneg _ x

/-- A profile off the coordinate fiber `{y | y i = b}` has zero conditional probability. -/
@[simp] lemma condProbD_of_ne (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    {x : ∀ j, β j} (hx : x i ≠ b) : d.condProbD i b x = 0 :=
  d.condProb_eq_zero_of_notMem _ hx

/-- On the coordinate fiber with positive marginal, the conditional is `d x / d.marginalD i b`. -/
lemma condProbD_eq_of_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    {x : ∀ j, β j} (hx : x i = b) (hpos : 0 < d.marginalD i b) :
    d.condProbD i b x = d x / d.marginalD i b := by
  rw [condProbD, ← probEvent_coordFiber d i b] at *
  exact d.condProb_eq_of_pos _ hx hpos

/-- The coordinate conditional vanishes everywhere when the conditioning marginal is not positive
(junk-on-zero-measure). -/
lemma condProbD_eq_zero_of_not_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (x : ∀ j, β j) (hnot : ¬ 0 < d.marginalD i b) :
    d.condProbD i b x = 0 :=
  if_neg fun h => hnot (probEvent_coordFiber d i b ▸ h.2)

/-- On a positive-mass coordinate fiber the conditional distribution sums to one. -/
lemma condProbD_sum_one_of_pos (d : FinDist (∀ i, β i)) (i : ι) (b : β i)
    (hpos : 0 < d.marginalD i b) :
    ∑ x : ∀ j, β j, d.condProbD i b x = 1 :=
  d.condProb_sum_one_of_pos _ (probEvent_coordFiber d i b ▸ hpos)

end FinDist

end Econlib.Probability
