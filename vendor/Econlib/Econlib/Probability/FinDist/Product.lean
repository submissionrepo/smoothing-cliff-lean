/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Map

/-!
# Products of finite distributions

This file defines product distributions on finite product types and proves the marginal and bind
identities.

## Main definitions

* `FinDist.product`: Product of two finite distributions.

## Main statements

* `FinDist.map_fst_product`: First marginal of a product distribution.
* `FinDist.map_snd_product`: Second marginal of a product distribution.
* `FinDist.product_eq_bind`: Product as a bind construction.

## Tags

probability, finite distributions, product
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Independent **product distribution** of two finite distributions, a law on `α × β` with pmf
`(a, b) ↦ d₁ a * d₂ b`. Composes with `map`/`bind`, and its marginals are `map`s. -/
noncomputable def product (d₁ : FinDist α) (d₂ : FinDist β) : FinDist (α × β) where
  pmf p := d₁ p.1 * d₂ p.2
  nonneg p := mul_nonneg (d₁.nonneg p.1) (d₂.nonneg p.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, d₂.sum_one, mul_one]
    exact d₁.sum_one

/-- Pointwise mass of a product distribution: The product of the factor masses. -/
@[simp] lemma product_apply (d₁ : FinDist α) (d₂ : FinDist β) (p : α × β) :
    (d₁.product d₂) p = d₁ p.1 * d₂ p.2 := rfl

/-- The first marginal of a product is the first factor. -/
lemma map_fst_product (d₁ : FinDist α) (d₂ : FinDist β) :
    (d₁.product d₂).map Prod.fst = d₁ := by
  ext a
  simp only [map_apply, product_apply]
  rw [show (Finset.univ.filter (fun p : α × β => p.1 = a))
        = ({a} : Finset α) ×ˢ (Finset.univ : Finset β) by
    ext ⟨x, y⟩; simp [eq_comm]]
  rw [Finset.sum_product, Finset.sum_singleton]
  simp_rw [← Finset.mul_sum, d₂.sum_one, mul_one]

/-- The second marginal of a product is the second factor. -/
lemma map_snd_product (d₁ : FinDist α) (d₂ : FinDist β) :
    (d₁.product d₂).map Prod.snd = d₂ := by
  ext b
  simp only [map_apply, product_apply]
  rw [show (Finset.univ.filter (fun p : α × β => p.2 = b))
        = (Finset.univ : Finset α) ×ˢ ({b} : Finset β) by
    ext ⟨x, y⟩; simp [eq_comm]]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_singleton]
  rw [← Finset.sum_mul, d₁.sum_one, one_mul]

/-- The product is `bind` of the first factor into the `map` placing the second factor's draw
alongside. Exhibits `product` as a derived monadic construction. -/
lemma product_eq_bind (d₁ : FinDist α) (d₂ : FinDist β) :
    d₁.product d₂ = d₁.bind (fun a => d₂.map (fun b => (a, b))) := by
  ext p
  obtain ⟨x, y⟩ := p
  simp only [product_apply, bind_apply, map_apply]
  -- ∑ a, d₁ a * (∑ b ∈ filter ((a,b) = (x,y)), d₂ b) = d₁ x * d₂ y
  rw [Finset.sum_eq_single x]
  · rw [show (Finset.univ.filter (fun b : β => (x, b) = (x, y))) = ({y} : Finset β) by
      ext b; simp [Prod.ext_iff]]
    rw [Finset.sum_singleton]
  · intro a _ ha
    rw [Finset.sum_eq_zero
      (fun b hb => absurd (congrArg Prod.fst (Finset.mem_filter.mp hb).2) ha), mul_zero]
  · intro hx; exact absurd (Finset.mem_univ x) hx

end FinDist
end Econlib.Probability
