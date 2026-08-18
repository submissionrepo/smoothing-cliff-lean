/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConcaveHingeInterpolation
public import Econlib.Math.Analysis.Convex.FunctionSum
public import Econlib.Math.Analysis.HingeConvex
public import Econlib.Probability.Order.Strassen

/-!
# Discrete Strassen's theorem (general finite support)

`Strassen/Discrete.lean` proves the discrete Strassen theorem only for the uniform,
equal-cardinality special case (`DiscreteLaw.exists_martingaleCoupling_uniform`). This file removes
those restrictions: Any two finitely-supported laws in **convex order** — with arbitrary weights
and arbitrary (possibly unequal) atom counts — admit a **martingale coupling**.

## Main statements

* `DiscreteLaw.expect_eq` — expectation against a finitely-supported law is the weighted atom sum.
* `DiscreteLaw.exists_martingaleCoupling` — **general discrete Strassen**: Finitely-supported laws
  in convex order admit a martingale coupling, with no uniformity or equal-cardinality hypotheses.

## Notes

The result is a corollary of the continuous theorem
`exists_martingaleCoupling_of_convexOrderOnIcc`. A finitely-supported law is a `ProbDist ℝ`
supported on the compact interval spanned by its atoms, so the only work is the bridge
`convexOrderOnIcc_toProbDist_of_convexOrder`, which upgrades the finitary convex order (tested
against functions convex on all of `ℝ`) to the interval convex order (tested against functions
convex on `[a, b]`) via the affine-minus-hinges grid interpolation
`ConcaveOn.exists_affine_hinge_interpolation`.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, convex order, martingale coupling, mean-preserving spread
-/

@[expose] public section

open MeasureTheory Set Finset BigOperators

namespace Econlib.Probability

namespace DiscreteLaw

/-- Expectation of a strongly-measurable `f` against a finitely-supported law is the weighted sum
of its values at the atoms. -/
lemma expect_eq (p : DiscreteLaw) {f : ℝ → ℝ} (hf : StronglyMeasurable f) :
    p.toProbDist.expect f = ∑ i, p.weight i * f (p.atom i) := by
  unfold ProbDist.expect
  rw [DiscreteLaw.toProbDist_toMeasure]
  rw [integral_finset_sum_measure (fun i _ =>
    (integrable_dirac' hf (a := p.atom i) ENNReal.coe_lt_top).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hf, ENNReal.toReal_ofReal (p.weight_nonneg i),
    smul_eq_mul]

/-- `id`-expectation against a finitely-supported law is its mean. -/
lemma expect_id_eq_mean (p : DiscreteLaw) : p.toProbDist.expect id = p.mean := by
  rw [expect_eq p stronglyMeasurable_id]
  simp only [id_eq]
  rfl

/-- A finitely-supported law is supported on the (finite) set of its atom values. -/
lemma toProbDist_supportsOn_range (p : DiscreteLaw) :
    p.toProbDist.supportsOn (Set.range p.atom) :=
  p.toProbDist_supportsOn_of_atoms_mem (Set.finite_range p.atom).measurableSet
    (fun i => Set.mem_range_self i)

/-- The index set of a finitely-supported law is nonempty (its weights sum to one). -/
lemma univ_nonempty (p : DiscreteLaw) : (Finset.univ : Finset (Fin p.n)).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hsum := p.weight_sum
  rw [h, Finset.sum_empty] at hsum
  exact one_ne_zero hsum.symm

end DiscreteLaw

/-- The finitary convex order on finitely-supported laws implies the interval convex order of their
`ProbDist` embeddings, over the interval spanned by all atoms. -/
lemma convexOrderOnIcc_toProbDist_of_convexOrder {p q : DiscreteLaw}
    (h : DiscreteLaw.ConvexOrder p q) :
    ∃ a b : ℝ, ConvexOrderOnIcc a b p.toProbDist q.toProbDist := by
  classical
  set S : Finset ℝ := Finset.image p.atom Finset.univ ∪ Finset.image q.atom Finset.univ with hS
  have hpmem : ∀ i, p.atom i ∈ S :=
    fun i => Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hqmem : ∀ j, q.atom j ∈ S :=
    fun j => Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hSne : S.Nonempty := by
    obtain ⟨i, -⟩ := p.univ_nonempty
    exact ⟨p.atom i, hpmem i⟩
  refine ⟨S.min' hSne, S.max' hSne, ?_, ?_, ?_, ?_⟩
  · -- p supported on [min, max]
    exact p.toProbDist_supportsOn_of_atoms_mem measurableSet_Icc
      (fun i => ⟨S.min'_le _ (hpmem i), S.le_max' _ (hpmem i)⟩)
  · -- q supported on [min, max]
    exact q.toProbDist_supportsOn_of_atoms_mem measurableSet_Icc
      (fun j => ⟨S.min'_le _ (hqmem j), S.le_max' _ (hqmem j)⟩)
  · -- equal means
    rw [DiscreteLaw.expect_id_eq_mean, DiscreteLaw.expect_id_eq_mean]
    exact h.mean_eq
  · -- the convex test
    -- `_hφcont` is required by the `ConvexOrderOnIcc` contract but unused here: the
    -- interpolation bridge replaces `φ` with a globally-defined `g`, matching only at atoms.
    intro φ hφcvx _hφcont
    -- Enumerate the atom values as a strictly increasing grid `v`.
    obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by have := hSne.card_pos; omega⟩
    set vEmb : Fin (k + 1) ↪o ℝ := S.orderEmbOfFin hk with hvEmb
    set v : Fin (k + 1) → ℝ := (vEmb : Fin (k + 1) → ℝ) with hv
    have hv_mono : StrictMono v := vEmb.strictMono
    have hv_range : Set.range v = ↑S := S.range_orderEmbOfFin hk
    have hvmemS : ∀ m, v m ∈ S := fun m => by
      have hmr : v m ∈ Set.range v := ⟨m, rfl⟩
      rw [hv_range, Finset.mem_coe] at hmr; exact hmr
    have hmem : ∀ m, v m ∈ Set.Icc (S.min' hSne) (S.max' hSne) :=
      fun m => ⟨S.min'_le _ (hvmemS m), S.le_max' _ (hvmemS m)⟩
    -- Affine-minus-hinges interpolation of `-φ` on the grid.
    obtain ⟨A, B, c, hc, hgrid⟩ :=
      ConcaveOn.exists_affine_hinge_interpolation hv_mono hφcvx.neg hmem
    -- `g` is convex on all of `ℝ` and matches `φ` on the grid.
    set g : ℝ → ℝ := fun x => -A - B * x + ∑ j, c j * max (v j - x) 0 with hg
    have hg_cvx : ConvexOn ℝ Set.univ g := by
      have h_aff : ConvexOn ℝ Set.univ (fun x : ℝ => -A - B * x) := by
        have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => -B * x) := by
          have hmap := LinearMap.convexOn ((-B) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) convex_univ
          have he : (⇑((-B) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) = (fun x : ℝ => -B * x) := by
            funext x; simp [LinearMap.smul_apply, smul_eq_mul]
          rwa [he] at hmap
        simpa [sub_eq_add_neg, add_comm] using hlin.add_const (-A)
      have h_sum : ConvexOn ℝ Set.univ (fun x : ℝ => ∑ j, c j * max (v j - x) 0) :=
        ConvexOn.fun_sum convex_univ (fun j _ => by
          simpa [smul_eq_mul] using (convexOn_hinge_left (v j)).smul (hc j))
      simpa [hg] using h_aff.add h_sum
    have hg_meas : Measurable g :=
      (measurable_const.sub (measurable_const.mul measurable_id)).add
        (Finset.measurable_sum _ (fun j _ =>
          measurable_const.mul ((measurable_const.sub measurable_id).max measurable_const)))
    have hφg_S : ∀ x ∈ S, φ x = g x := by
      intro x hx
      have hxrange : x ∈ Set.range v := by rw [hv_range]; exact Finset.mem_coe.mpr hx
      obtain ⟨m, rfl⟩ := hxrange
      have hgm := hgrid m
      rw [Pi.neg_apply] at hgm
      simp only [hg]
      linarith [hgm]
    have hφg_p : φ =ᵐ[p.toProbDist.toMeasure] g := by
      filter_upwards [p.toProbDist.ae_mem_of_supportsOn
        (Set.finite_range p.atom).measurableSet p.toProbDist_supportsOn_range] with x hx
      obtain ⟨i, rfl⟩ := hx
      exact hφg_S _ (hpmem i)
    have hφg_q : φ =ᵐ[q.toProbDist.toMeasure] g := by
      filter_upwards [q.toProbDist.ae_mem_of_supportsOn
        (Set.finite_range q.atom).measurableSet q.toProbDist_supportsOn_range] with x hx
      obtain ⟨j, rfl⟩ := hx
      exact hφg_S _ (hqmem j)
    calc p.toProbDist.expect φ
        = p.toProbDist.expect g := integral_congr_ae hφg_p
      _ = ∑ i, p.weight i * g (p.atom i) := DiscreteLaw.expect_eq p hg_meas.stronglyMeasurable
      _ ≤ ∑ j, q.weight j * g (q.atom j) := h g hg_cvx
      _ = q.toProbDist.expect g := (DiscreteLaw.expect_eq q hg_meas.stronglyMeasurable).symm
      _ = q.toProbDist.expect φ := (integral_congr_ae hφg_q).symm

/-- **Discrete Strassen (general finite support).** Two finitely-supported real laws in convex
order admit a martingale coupling — no uniformity or equal-cardinality hypotheses.

This is an existence statement, obtained from the continuous theorem; the uniform equal-cardinality
case `DiscreteLaw.exists_martingaleCoupling_uniform` additionally yields an *explicit* coupling
built from a bistochastic martingale matrix. -/
theorem DiscreteLaw.exists_martingaleCoupling (p q : DiscreteLaw)
    (h : DiscreteLaw.ConvexOrder p q) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling p.toProbDist q.toProbDist π := by
  obtain ⟨a, b, hcx⟩ := convexOrderOnIcc_toProbDist_of_convexOrder h
  exact exists_martingaleCoupling_of_convexOrderOnIcc a b hcx

end Econlib.Probability
