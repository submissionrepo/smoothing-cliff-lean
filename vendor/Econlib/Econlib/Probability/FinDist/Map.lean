/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Expect

/-!
# `FinDist.map` and `FinDist.bind` — the monadic operations

`FinDist` carries the same monad structure as `PMF`: `pure` (the point mass, in
`FinDist/Basic.lean`), `map` (deterministic pushforward along a function), and `bind` (averaging a
family of laws). The typed product `FinDist α → FinDist β → FinDist (α × β)` is derived from these
in `FinDist/Product.lean`.

## Main definitions

* `FinDist.map` — pushforward of `d` along `f : α → β`.
* `FinDist.bind` — mixes the family `f a : FinDist β` with weights `d a`.

## Main statements

* `FinDist.expect_map` — change-of-variables rule for the pushforward.
* `FinDist.expect_bind` — expectation distributes over `bind`.
* `FinDist.map_eq_bind` — `map` is `bind` into `pure`.

## Tags

probability, finite distributions, pushforward, bind, monad
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ## `map` -/

/-- Pushforward of a finite distribution along a deterministic map (the functor action; cf.
`PMF.map`). -/
noncomputable def map (d : FinDist α) (f : α → β) : FinDist β where
  pmf b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), d a
  nonneg _ := Finset.sum_nonneg fun a _ => d.nonneg a
  sum_one := by
    rw [Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (g := f) (f := fun a => d a)
      (fun _ _ => Finset.mem_univ _)]
    exact d.sum_one

/-- The pushforward mass at `b` is the total mass of the fiber `f⁻¹{b}` (filter form). A plain
lemma — the simp-normal form is the indicator `map_apply'`; this filtered spelling is for explicit
`rw` / `simp only [map_apply]` callers that want the fiber sum. -/
lemma map_apply (d : FinDist α) (f : α → β) (b : β) :
    (d.map f) b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), d a :=
  rfl

/-- Indicator (full-`univ`) form of the pushforward mass: `∑ a, if f a = b then d a else 0`. This
is both the `@[simp]` normal form and the `findist_eval` evaluation form — with no `Finset.filter`,
`Fin.sum_univ_n` applies directly, removing the `Finset.sum_filter` step the filtered `map_apply`
would otherwise force. -/
@[simp, findist_eval] lemma map_apply' (d : FinDist α) (f : α → β) (b : β) :
    (d.map f) b = ∑ a, if f a = b then d a else 0 := by
  rw [map_apply, Finset.sum_filter]

/-- **Change of variables.** Expectation under the pushforward equals expectation against the
composed function. -/
@[simp] lemma expect_map (d : FinDist α) (f : α → β) (g : β → ℝ) :
    (d.map f).expect g = d.expect (g ∘ f) := by
  unfold expect
  have step1 : ∀ b : β,
      (d.map f) b * g b
        = ∑ a ∈ Finset.univ.filter (fun a => f a = b), d a * g (f a) := by
    intro b
    rw [map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rw [ha.2]
  simp_rw [step1]
  exact Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset β)) (g := f) (f := fun a => d a * g (f a))
    (fun _ _ => Finset.mem_univ _)

/-- The pushforward along the identity is the original distribution. -/
@[simp] lemma map_id (d : FinDist α) : d.map id = d := by
  ext b
  rw [map_apply, show (Finset.univ.filter (fun a => id a = b)) = ({b} : Finset α) by
    ext a; simp [eq_comm], Finset.sum_singleton]

/-! ## `bind` -/

/-- Monadic bind: Average the family `f : α → FinDist β` against the weights of `d` (cf.
`PMF.bind`). -/
noncomputable def bind (d : FinDist α) (f : α → FinDist β) : FinDist β where
  pmf b := ∑ a, d a * (f a) b
  nonneg _ := Finset.sum_nonneg fun a _ => mul_nonneg (d.nonneg a) ((f a).nonneg _)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have h : ∀ a, ∑ b, (f a) b = 1 := fun a => (f a).sum_one
    simp_rw [h, mul_one]
    exact d.sum_one

/-- The mass of `bind d f` at `b` is the `d`-weighted average of `f a` at `b`. In the
`findist_eval` set: The right side is already a full-`univ` sum, so `Fin.sum_univ_n` evaluates it
without a `Finset.filter` detour. -/
@[simp, findist_eval] lemma bind_apply (d : FinDist α) (f : α → FinDist β) (b : β) :
    (d.bind f) b = ∑ a, d a * (f a) b :=
  rfl

/-- Expectation distributes over `bind`: `𝔼_{d.bind f}[g] = 𝔼_d[a ↦ 𝔼_{f a}[g]]`. -/
lemma expect_bind (d : FinDist α) (f : α → FinDist β) (g : β → ℝ) :
    (d.bind f).expect g = d.expect (fun a => (f a).expect g) := by
  simp only [expect, bind_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `bind` of a point mass evaluates the family. -/
@[simp] lemma pure_bind (a : α) (f : α → FinDist β) : (FinDist.pure a).bind f = f a := by
  ext b
  rw [bind_apply]
  simp only [pure]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl, one_mul]
  · intro a' _ ha'; rw [if_neg (Ne.symm ha'), zero_mul]
  · intro ha; exact absurd (Finset.mem_univ a) ha

/-- `bind` into `pure` is the identity. -/
@[simp] lemma bind_pure (d : FinDist α) : d.bind FinDist.pure = d := by
  ext b
  rw [bind_apply]
  simp only [pure]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl, mul_one]
  · intro a _ ha; rw [if_neg ha, mul_zero]
  · intro hb; exact absurd (Finset.mem_univ b) hb

/-- `map` is `bind` into `pure`. -/
lemma map_eq_bind (d : FinDist α) (f : α → β) :
    d.map f = d.bind (fun a => FinDist.pure (f a)) := by
  ext b
  rw [map_apply, bind_apply]
  simp only [pure, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = b
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

end FinDist
end Econlib.Probability
