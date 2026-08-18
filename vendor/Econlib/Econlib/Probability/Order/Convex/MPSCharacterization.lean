/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConcaveHingeInterpolation
public import Econlib.Probability.FinDist.Shortfall
public import Econlib.Probability.Order.Convex.MPS

/-!
# The Rothschild–Stiglitz characterization of mean-preserving spreads

`FinDist.IsMPS d ds y` is defined by a universal concave test: Equal means and
`E_ds[f ∘ y] ≤ E_d[f ∘ y]` for every concave `f`. The Rothschild–Stiglitz (1970) content is that
this universal quantifier collapses to a one-parameter family of dispersion tests, the lower hinges
`x ↦ max (t - x) 0`. Their expectations are the **expected shortfall** below the cutoff `t`,
`E[(t - y)⁺]`, so the characterization reads: `ds` is a mean-preserving spread of `d` iff the means
agree and at every cutoff `t` the spread has weakly larger expected shortfall.

## Main statements

* `FinDist.concave_expect_le_of_shortfall_le` — the nontrivial direction: Hinge tests suffice for
  the concave order.
* `FinDist.isMPS_iff_shortfall` — `IsMPS d ds y` iff equal means and weakly larger
  `expectedShortfall` at every cutoff.
* `FinDist.shortfall_iff_concave_expect_le` — given equal means, the shortfall condition is
  equivalent to the universal concave-preference conclusion.

## Notes

The dispersion statistic `E[(t - y)⁺]` is `FinDist.expectedShortfall`
(`Econlib.Probability.FinDist.Shortfall`), whose identity with the discrete integrated CDF is
`FinDist.expectedShortfall_eq_sum_lt`; the characterizations are stated through it.

## References

* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

mean-preserving spread, rothschild-stiglitz, second-order stochastic dominance, integrated cdf,
expected shortfall, hinge
-/

@[expose] public section

namespace Econlib.Probability

open Finset BigOperators

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Hinge tests suffice for the concave order**, the nontrivial Rothschild–Stiglitz direction. If
`d` and `ds` have equal means of `y` and at every cutoff `t` the expected shortfall `E[(t - y)⁺]`
is weakly larger under `ds`, then every function concave on `ℝ` has weakly lower expectation under
`ds`. -/
theorem concave_expect_le_of_shortfall_le (d ds : FinDist α) (y : α → ℝ)
    (hmean : ds.expect y = d.expect y)
    (hshortfall : ∀ t : ℝ, d.expectedShortfall y t ≤ ds.expectedShortfall y t)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) :
    ds.expect (f ∘ y) ≤ d.expect (f ∘ y) := by
  simp only [FinDist.expectedShortfall_eq] at hshortfall
  -- A `FinDist` forces `α` to be nonempty (its masses sum to one), so the value grid is nonempty.
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hsum : (∑ a : α, d.pmf a) = 0 := by rw [Finset.univ_eq_empty, Finset.sum_empty]
    rw [d.sum_one] at hsum
    exact one_ne_zero hsum
  -- The sorted distinct outcome values form a strictly increasing grid `vEmb`.
  set T : Finset ℝ := Finset.image y Finset.univ with hT
  have hTne : T.Nonempty := by
    obtain ⟨a⟩ := hne
    exact ⟨y a, Finset.mem_image_of_mem y (Finset.mem_univ a)⟩
  obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 :=
    ⟨T.card - 1, by have := hTne.card_pos; omega⟩
  set vEmb : Fin (k + 1) ↪o ℝ := T.orderEmbOfFin hk with hvEmb
  have hvmono : StrictMono (vEmb : Fin (k + 1) → ℝ) := vEmb.strictMono
  -- Affine-minus-hinges representation of `f` on the grid (the heart, Task 1).
  obtain ⟨A, B, c, hc_nonneg, hgrid⟩ :=
    ConcaveOn.exists_affine_hinge_interpolation hvmono hf (fun _ => Set.mem_univ _)
  -- Every outcome value `y a` is a grid point, so the representation holds at `y a`.
  have hrange : Set.range (vEmb : Fin (k + 1) → ℝ) = ↑T := T.range_orderEmbOfFin hk
  have hpoint : ∀ a : α, f (y a) = A + B * y a - ∑ j, c j * max ((vEmb j) - y a) 0 := by
    intro a
    have hmem : y a ∈ T := Finset.mem_image_of_mem y (Finset.mem_univ a)
    have : y a ∈ Set.range (vEmb : Fin (k + 1) → ℝ) := by rw [hrange]; exact hmem
    obtain ⟨m, hm⟩ := this
    rw [← hm]; exact hgrid m
  -- Linearity of `expect` turns the pointwise representation into one over the whole distribution.
  have hexpand : ∀ μ : FinDist α, μ.expect (f ∘ y) =
      A + B * μ.expect y - ∑ j, c j * μ.expect (fun a => max ((vEmb j) - y a) 0) := by
    intro μ
    -- Expand the inner hinge expectations into double sums and `expect y` into a sum.
    rw [FinDist.expect_eq_sum, FinDist.expect_eq_sum]
    have hinner : ∀ j, μ.expect (fun a => max ((vEmb j) - y a) 0) =
        ∑ a, μ.pmf a * max ((vEmb j) - y a) 0 := fun j => FinDist.expect_eq_sum _ _
    simp_rw [hinner]
    -- Substitute the grid identity at each outcome, then distribute the finite sums.
    have hstep : ∀ a, μ.pmf a * (f ∘ y) a =
        A * μ.pmf a + B * (μ.pmf a * y a) -
          ∑ j, c j * (μ.pmf a * max ((vEmb j) - y a) 0) := by
      intro a
      rw [Function.comp_apply, hpoint a, mul_sub, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl; intro j _; ring
    rw [Finset.sum_congr rfl (fun a _ => hstep a),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, μ.sum_one, mul_one, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  -- The difference is a nonnegative combination of the shortfall gaps.
  rw [hexpand d, hexpand ds, hmean]
  have hgap : 0 ≤ ∑ j, c j *
      (ds.expect (fun a => max ((vEmb j) - y a) 0) -
        d.expect (fun a => max ((vEmb j) - y a) 0)) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hc_nonneg j) (by linarith [hshortfall (vEmb j)])
  -- Split the combined gap sum into the two hinge-expectation sums.
  have hsub : ∀ j, c j * (ds.expect (fun a => max ((vEmb j) - y a) 0) -
        d.expect (fun a => max ((vEmb j) - y a) 0)) =
      c j * ds.expect (fun a => max ((vEmb j) - y a) 0) -
        c j * d.expect (fun a => max ((vEmb j) - y a) 0) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hsub j), Finset.sum_sub_distrib] at hgap
  linarith

/-- **The Rothschild–Stiglitz characterization of mean-preserving spreads.** `ds` is a
mean-preserving spread of `d` if and only if the means agree and, at every cutoff `t`, the expected
shortfall `E[(t - y)⁺]` — the discrete integrated CDF — is weakly larger under `ds`. -/
theorem isMPS_iff_shortfall (d ds : FinDist α) (y : α → ℝ) :
    FinDist.IsMPS d ds y ↔
      ds.expect y = d.expect y ∧
      ∀ t : ℝ, d.expectedShortfall y t ≤ ds.expectedShortfall y t := by
  simp only [FinDist.expectedShortfall_eq]
  constructor
  · -- Forward: equal means is a field; the shortfall test is the convex hinge `max (t - ·) 0`.
    intro h
    refine ⟨h.same_mean, fun t => ?_⟩
    have hge := h.convex_expect_ge (fun z => max (t - z) 0) (convexOn_hinge_left t)
    simpa only [Function.comp_def] using hge
  · -- Reverse: package equal means with the hard direction.
    rintro ⟨hmean, hshort⟩
    refine ⟨hmean, fun f hf => concave_expect_le_of_shortfall_le d ds y hmean ?_ f hf⟩
    simpa only [FinDist.expectedShortfall_eq] using hshort

/-- **Rothschild–Stiglitz, headline form.** Given equal means, the dispersion condition — weakly
larger expected shortfall at every cutoff — holds if and only if every risk averter, that is every
agent with a concave payoff, weakly prefers `d` to `ds`. -/
theorem shortfall_iff_concave_expect_le (d ds : FinDist α) (y : α → ℝ)
    (hmean : ds.expect y = d.expect y) :
    (∀ t : ℝ, d.expectedShortfall y t ≤ ds.expectedShortfall y t) ↔
      (∀ f : ℝ → ℝ, ConcaveOn ℝ Set.univ f → ds.expect (f ∘ y) ≤ d.expect (f ∘ y)) := by
  simp only [FinDist.expectedShortfall_eq]
  constructor
  · -- Forward: the hard direction (hinge tests suffice for the concave order).
    intro hshort f hf
    refine concave_expect_le_of_shortfall_le d ds y hmean ?_ f hf
    simpa only [FinDist.expectedShortfall_eq] using hshort
  · -- Reverse: test the concave hypothesis on `-(max (t - ·) 0)`, then negate the inequality.
    intro H t
    have hconc := H (-(fun z => max (t - z) 0)) (convexOn_hinge_left t).neg
    simpa only [FinDist.expect, Pi.neg_apply, Function.comp_def,
      mul_neg, sum_neg_distrib, neg_le_neg_iff] using hconc

end FinDist

end Econlib.Probability
