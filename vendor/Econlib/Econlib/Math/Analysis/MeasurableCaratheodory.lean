/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ExtremePointsGDelta
public import Econlib.Math.MeasureTheory.MeasurableSelection
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Measurable extremal selectors in finite dimension

For a measurable multifunction `F : Y → Set (EuclideanSpace ℝ (Fin n))` with closed graph, uniform
compact bound, and convex fibers, this file proves measurable selector results for the
extreme-points multifunction:

* joint measurability of `y ↦ extremePoints (F y)`;
* measurable lex-min/lex-max selectors;
* measurable ray-length and exit-point selectors;
* a measurable single-direction descent vector at a measurable base point.

Together these selectors provide measurable extreme-point and descent-direction choices for
finite-dimensional compact convex correspondences.

## Main results

* `measurable_lexMin_of_closedGraph` — measurable lex-max selector.
* `measurable_max_ray_length` — measurable max ray-length.
* `measurable_exit_point` — measurable exit point.
* `measurableSet_extremePoints_graph` — joint Borel measurability of the extreme-points
  multifunction.
* `measurable_relTangentSpace_graph` — Borel measurability of the relative-tangent-space graph.
* `measurable_dim_relTangentSpace` — measurable dimension of the relative tangent space.
* `exists_measurable_descent_direction` — measurable single descent direction at a measurable base
  point.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology Pointwise InnerProductSpace

/-! ## Measurable extremal selectors -/

/-! ### Measurable max of a single coordinate

For a closed-graph compact-bound multifunction `F`, the supremum of the `i`-th coordinate over
`F y` is measurable in `y`.  This is a direct specialization of
`measurable_sSup_image_of_closedGraph_compactBound`. The lex-max point's `i`-th coordinate is built
by recursively iterating this with appropriately shrunk fibers. -/

/-- The supremum of the `i`-th coordinate over a closed-graph compact-bound multifunction is
measurable. -/
lemma measurable_sSup_coord_of_closedGraph
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (i : Fin n) :
    Measurable
      (fun y => sSup ((fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) '' F y)) :=
  MeasureTheory.measurable_sSup_image_of_closedGraph_compactBound
    hK_compact hF_sub_K hF_graph_closed (PiLp.continuous_apply 2 _ i)

/-! ### Measurable lex-max selector

For a closed-graph compact-bound multifunction `F : Y → Set (EuclideanSpace ℝ (Fin n))`, the
**lex-max** point — the point of `F y` lexicographically maximizing its coordinates
`(x₀, x₁, …, x_{n-1})` — is measurable in `y`. When each fiber is convex, the lex-max point is an
extreme point of `F y`. -/

/-- Internal recursive lex-max selector.

Same hypotheses as the public `measurable_lexMin_of_closedGraph`, but states the recursion on the
target dimension `n` explicitly, quantifying over `Y, F, K` so the induction hypothesis applies to
the expanded base space `Y × ℝ`. -/
private theorem measurable_lexMax_aux :
    ∀ (n : ℕ) {Y : Type*}
    [_inst1 : MeasurableSpace Y] [_inst2 : TopologicalSpace Y]
    [_inst3 : OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))},
    IsCompact K → (∀ y, F y ⊆ K) →
    IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} →
    ∃ f : Y → EuclideanSpace ℝ (Fin n), Measurable f ∧
      (∀ y, (F y).Nonempty → f y ∈ F y) ∧
      (∀ y, ∀ x ∈ F y, ∀ i : Fin n,
        (∀ j : Fin n, j < i → x.ofLp j = (f y).ofLp j) →
        x.ofLp i ≤ (f y).ofLp i) := by
  intro n
  induction n with
  | zero =>
    intro Y _ _ _ F K _ _ _
    refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · intro y hF_ne
      obtain ⟨x, hx⟩ := hF_ne
      rwa [Subsingleton.elim (0 : EuclideanSpace ℝ (Fin 0)) x]
    · intro _ _ _ i _
      exact i.elim0
  | succ n ih =>
    intro Y _ _ _ F K hK_compact hF_sub_K hF_graph_closed
    let m₀ : Y → ℝ := fun y =>
      sSup ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => x.ofLp 0) '' F y)
    have hm₀_meas : Measurable m₀ :=
      MeasureTheory.measurable_sSup_image_of_closedGraph_compactBound
        hK_compact hF_sub_K hF_graph_closed (PiLp.continuous_apply 2 _ 0)
    let cons : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
      fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
    have h_cons_cont : Continuous cons := by
      change Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (Matrix.vecCons p.1 (WithLp.ofLp p.2)))
      exact (PiLp.continuous_toLp 2 _).comp
        (continuous_fst.matrixVecCons ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
    let pi_tail : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
      fun x => WithLp.toLp 2 (fun i : Fin n => x.ofLp i.succ)
    have h_pi_tail_cont : Continuous pi_tail :=
      (PiLp.continuous_toLp 2 _).comp
        (continuous_pi (fun i => PiLp.continuous_apply 2 _ i.succ))
    -- `pi_tail` is a right inverse to `cons` on the tail.
    have h_pi_tail_cons : ∀ c x', pi_tail (cons (c, x')) = x' := by
      intro c x'
      apply WithLp.ofLp_injective 2
      funext i
      rfl
    -- `cons (m₀, ·)` lands in `F y` whenever the first coord is achieved.
    have h_cons_left_inv : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))),
        cons (x.ofLp 0, pi_tail x) = x := by
      intro x
      apply WithLp.ofLp_injective 2
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j; rfl
    let K' : Set (EuclideanSpace ℝ (Fin n)) := pi_tail '' K
    have hK'_compact : IsCompact K' := hK_compact.image h_pi_tail_cont
    let F' : Y × ℝ → Set (EuclideanSpace ℝ (Fin n)) :=
      fun yc => {x' | cons (yc.2, x') ∈ F yc.1}
    have hF'_sub : ∀ yc, F' yc ⊆ K' := by
      intro yc x' hx'
      refine ⟨cons (yc.2, x'), hF_sub_K _ hx', h_pi_tail_cons _ _⟩
    have hF'_graph_closed :
        IsClosed {p : (Y × ℝ) × EuclideanSpace ℝ (Fin n) | p.2 ∈ F' p.1} := by
      have h_cont : Continuous (fun p : (Y × ℝ) × EuclideanSpace ℝ (Fin n) =>
          (p.1.1, cons (p.1.2, p.2))) :=
        (continuous_fst.comp continuous_fst).prodMk
          (h_cons_cont.comp
            ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      have h_eq :
          {p : (Y × ℝ) × EuclideanSpace ℝ (Fin n) | p.2 ∈ F' p.1}
            = (fun p : (Y × ℝ) × EuclideanSpace ℝ (Fin n) =>
                (p.1.1, cons (p.1.2, p.2))) ⁻¹'
              {q : Y × EuclideanSpace ℝ (Fin (n + 1)) | q.2 ∈ F q.1} := by
        ext p; simp [F']
      rw [h_eq]
      exact hF_graph_closed.preimage h_cont
    obtain ⟨g, hg_meas, hg_mem, hg_lex⟩ := ih hK'_compact hF'_sub hF'_graph_closed
    refine ⟨fun y => cons (m₀ y, g (y, m₀ y)), ?_, ?_, ?_⟩
    · -- Measurability: `f = cons ∘ (m₀, g ∘ (id, m₀))`.
      apply h_cons_cont.measurable.comp
      exact hm₀_meas.prodMk (hg_meas.comp (measurable_id.prodMk hm₀_meas))
    · -- Pointwise membership.
      intro y hFy_ne
      -- `F y` compact, so the coord-0 sup is achieved by some `x* ∈ F y`.
      have hFy_compact : IsCompact (F y) :=
        MeasureTheory.isCompact_fibre_of_closedGraph_compactBound
          hK_compact hF_sub_K hF_graph_closed y
      have h_image_compact :
          IsCompact ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => x.ofLp 0) '' F y) :=
        hFy_compact.image (PiLp.continuous_apply 2 _ 0)
      have h_image_ne :
          ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => x.ofLp 0) '' F y).Nonempty :=
        hFy_ne.image _
      have h_image_bdd :
          BddAbove ((fun x : EuclideanSpace ℝ (Fin (n + 1)) => x.ofLp 0) '' F y) :=
        h_image_compact.bddAbove
      obtain ⟨xMaxVal, hxMaxVal_mem, hxMaxVal_max⟩ :=
        h_image_compact.exists_isMaxOn h_image_ne continuousOn_id
      obtain ⟨x_star, hx_star_in, hx_star_proj⟩ := hxMaxVal_mem
      -- `m₀ y = x_star.ofLp 0`.
      have h_m₀_eq : m₀ y = x_star.ofLp 0 := by
        apply le_antisymm
        · refine csSup_le h_image_ne ?_
          rintro v ⟨w, hw_F, rfl⟩
          have h_le : (id (w.ofLp 0) : ℝ) ≤ id xMaxVal := hxMaxVal_max ⟨w, hw_F, rfl⟩
          simp only [id] at h_le
          calc w.ofLp 0 ≤ xMaxVal := h_le
            _ = x_star.ofLp 0 := hx_star_proj.symm
        · exact le_csSup h_image_bdd ⟨x_star, hx_star_in, rfl⟩
      -- `F' (y, m₀ y)` is nonempty (witness: `pi_tail x_star`).
      have hF'_ne : (F' (y, m₀ y)).Nonempty := by
        refine ⟨pi_tail x_star, ?_⟩
        change cons (m₀ y, pi_tail x_star) ∈ F y
        rw [h_m₀_eq, h_cons_left_inv]
        exact hx_star_in
      have hg_in : g (y, m₀ y) ∈ F' (y, m₀ y) := hg_mem _ hF'_ne
      exact hg_in
    · -- Lex-max property.
      intro y x hx i
      cases i using Fin.cases with
      | zero =>
        intro _
        -- `(cons (m₀ y, ·)).ofLp 0` reduces to `m₀ y`; goal becomes `x.ofLp 0 ≤ m₀ y`.
        change x.ofLp 0 ≤ m₀ y
        apply le_csSup
        · have hFy_compact : IsCompact (F y) :=
            MeasureTheory.isCompact_fibre_of_closedGraph_compactBound
              hK_compact hF_sub_K hF_graph_closed y
          exact (hFy_compact.image (PiLp.continuous_apply 2 _ 0)).bddAbove
        · exact ⟨x, hx, rfl⟩
      | succ k =>
        intro h_agree
        -- `(cons (m₀ y, g (y, m₀ y))).ofLp k.succ` reduces to `(g (y, m₀ y)).ofLp k`.
        change x.ofLp k.succ ≤ (g (y, m₀ y)).ofLp k
        -- From `h_agree` at index `0`: `x.ofLp 0 = m₀ y`.
        have h_agree_0 : x.ofLp 0 = m₀ y := h_agree 0 (Fin.succ_pos k)
        -- `pi_tail x ∈ F' (y, m₀ y)`: rebuild `x` from `(m₀ y, pi_tail x)`.
        have h_pi_tail_in : pi_tail x ∈ F' (y, m₀ y) := by
          change cons (m₀ y, pi_tail x) ∈ F y
          rw [← h_agree_0, h_cons_left_inv]
          exact hx
        -- `pi_tail x` agrees with `g (y, m₀ y)` on the first `k` coords.
        have h_pi_agree : ∀ j' : Fin n, j' < k →
            (pi_tail x).ofLp j' = (g (y, m₀ y)).ofLp j' := by
          intro j' hj'
          have hj'_succ : j'.succ < k.succ := Fin.succ_lt_succ_iff.mpr hj'
          exact h_agree j'.succ hj'_succ
        exact hg_lex (y, m₀ y) (pi_tail x) h_pi_tail_in k h_pi_agree

/-- Measurable lex-extreme selector (lex-max).

For a closed-graph compact-bound `F : Y → Set (EuclideanSpace ℝ (Fin n))`, there exists a
measurable `f : Y → EuclideanSpace ℝ (Fin n)` with `f y ∈ F y` whenever `F y` is nonempty.

This selector is in fact the **lex-max** point of `F y` (the point that lexicographically maximizes
its coordinates).  The companion lemma `measurable_lexMin_isExtreme` strengthens this to give that
`f y` is an extreme point of `F y` when each fiber is convex. -/
lemma measurable_lexMin_of_closedGraph
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) :
    ∃ f : Y → EuclideanSpace ℝ (Fin n), Measurable f ∧
      (∀ y, (F y).Nonempty → f y ∈ F y) := by
  obtain ⟨f, hf_meas, hf_mem, _⟩ :=
    measurable_lexMax_aux n hK_compact hF_sub_K hF_graph_closed
  exact ⟨f, hf_meas, hf_mem⟩

/-- Lex-max selector is an extreme point on convex fibers.

If additionally `F y` is convex for each `y`, then the lex-max selector `f y` of `F y` is an
extreme point of `F y` whenever `F y` is nonempty. -/
lemma measurable_lexMin_isExtreme
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    -- Convexity of each fibre is part of the theorem's mathematical content (see docstring),
    -- even though the lex-order argument below does not need to invoke it directly.
    (_hF_convex : ∀ y, Convex ℝ (F y)) :
    ∃ f : Y → EuclideanSpace ℝ (Fin n), Measurable f ∧
      (∀ y, (F y).Nonempty → f y ∈ Set.extremePoints ℝ (F y)) := by
  obtain ⟨f, hf_meas, hf_mem, hf_lex⟩ :=
    measurable_lexMax_aux n hK_compact hF_sub_K hF_graph_closed
  refine ⟨f, hf_meas, ?_⟩
  intro y hFy_ne
  refine ⟨hf_mem y hFy_ne, ?_⟩
  intro a ha b hb hab
  obtain ⟨α, β, hα_pos, hβ_pos, hsum, hcomb⟩ := hab
  classical
  have h_a_eq_b : a = b := by
    by_contra hab_neq
    -- Smallest disagreement index via `Finset.min'`.
    let S : Finset (Fin n) := Finset.univ.filter (fun i => a.ofLp i ≠ b.ofLp i)
    have hS_ne : S.Nonempty := by
      by_contra hS_emp
      apply hab_neq
      apply WithLp.ofLp_injective 2
      funext i
      by_contra h_neq
      exact hS_emp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_neq⟩⟩
    let i := S.min' hS_ne
    have hi_mem : i ∈ S := S.min'_mem hS_ne
    have hi_neq : a.ofLp i ≠ b.ofLp i := (Finset.mem_filter.mp hi_mem).2
    have h_min : ∀ j : Fin n, j < i → a.ofLp j = b.ofLp j := by
      intro j hj
      by_contra hj_neq
      have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_neq⟩
      exact absurd (S.min'_le j hj_mem) (not_le.mpr hj)
    -- For `j < i`: `(f y).ofLp j = a.ofLp j = b.ofLp j` (convex combo).
    have h_fy_eq_a_below : ∀ j : Fin n, j < i → (f y).ofLp j = a.ofLp j := by
      intro j hj
      have h_eq_ab : a.ofLp j = b.ofLp j := h_min j hj
      have h1 : (f y).ofLp j = α * a.ofLp j + β * b.ofLp j := by
        rw [← hcomb]; rfl
      rw [h1, ← h_eq_ab]
      have hring : α * a.ofLp j + β * a.ofLp j = (α + β) * a.ofLp j := by ring
      rw [hring, hsum, one_mul]
    rcases lt_or_gt_of_ne hi_neq with hi_lt | hi_gt
    · -- `a.ofLp i < b.ofLp i`: apply lex-max to `b`.
      have h_b_agree : ∀ j : Fin n, j < i → b.ofLp j = (f y).ofLp j := by
        intro j hj; rw [← h_min j hj]; exact (h_fy_eq_a_below j hj).symm
      have h_b_le_f : b.ofLp i ≤ (f y).ofLp i := hf_lex y b hb i h_b_agree
      have h_f_i : (f y).ofLp i = α * a.ofLp i + β * b.ofLp i := by
        rw [← hcomb]; rfl
      have h_f_lt_b : (f y).ofLp i < b.ofLp i := by
        rw [h_f_i]
        have hβ : β = 1 - α := by linarith
        have key : α * a.ofLp i + β * b.ofLp i =
            b.ofLp i - α * (b.ofLp i - a.ofLp i) := by rw [hβ]; ring
        rw [key]
        have h_pos : 0 < α * (b.ofLp i - a.ofLp i) := mul_pos hα_pos (by linarith)
        linarith
      linarith
    · -- Symmetric: `b.ofLp i < a.ofLp i`.  Apply lex-max to `a`.
      have h_a_agree : ∀ j : Fin n, j < i → a.ofLp j = (f y).ofLp j := by
        intro j hj; exact (h_fy_eq_a_below j hj).symm
      have h_a_le_f : a.ofLp i ≤ (f y).ofLp i := hf_lex y a ha i h_a_agree
      have h_f_i : (f y).ofLp i = α * a.ofLp i + β * b.ofLp i := by
        rw [← hcomb]; rfl
      have h_f_lt_a : (f y).ofLp i < a.ofLp i := by
        rw [h_f_i]
        have hα : α = 1 - β := by linarith
        have key : α * a.ofLp i + β * b.ofLp i =
            a.ofLp i - β * (a.ofLp i - b.ofLp i) := by rw [hα]; ring
        rw [key]
        have h_pos : 0 < β * (a.ofLp i - b.ofLp i) := mul_pos hβ_pos (by linarith)
        linarith
      linarith
  rw [h_a_eq_b] at hcomb
  have h_b_eq_fy : b = f y := by
    have h : (α + β) • b = f y := by rw [add_smul]; exact hcomb
    rwa [hsum, one_smul] at h
  exact h_a_eq_b.trans h_b_eq_fy

/-! ### Measurable max ray-length and exit point

For a closed-graph compact-bound `F` and measurable `z, d : Y → EuclideanSpace
ℝ (Fin n)` with
`z(y) ∈ F y`, the maximum `t ≥ 0` such that `z(y) + t·d(y)
∈ F(y)` is measurable in `y`.  The exit
point `z(y) + max-t(y) · d(y)` is then measurable as well, and lies in `F y` (by closedness). -/

/-- Per-rational predicate measurability.

For each rational `q ≥ 0`, the set `{y : z y + q·d y ∈ F y}` is measurable when `z`, `d` are
measurable and `F` has closed graph.  Used by `measurable_max_ray_length`. -/
lemma measurableSet_ray_in_fibre
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z d : Y → EuclideanSpace ℝ (Fin n)}
    (hz_meas : Measurable z) (hd_meas : Measurable d)
    (t : ℝ) :
    MeasurableSet {y : Y | z y + t • d y ∈ F y} := by
  have h_map : Measurable (fun y : Y => (y, z y + t • d y)) :=
    measurable_id.prodMk (hz_meas.add ((measurable_const).smul hd_meas))
  exact h_map hF_graph_closed.measurableSet

/-- Measurable max ray-length.

The hypothesis `hz_in_F : ∀ y, z y ∈ F y` ensures `0 ∈ Gy` always, so `Gy` is either `[0, b]`
(bounded) or `[0, ∞)` (when `d y = 0`).  Without this hypothesis, the singleton tangent case
`Gy = {a}` with irrational `a > 0` defeats rational density. -/
lemma measurable_max_ray_length
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    -- Compactness of the ambient bound `K` is carried for symmetry with the rest of the
    -- measurable-Carathéodory pipeline; boundedness of `Gy` here comes from convexity and
    -- `hF_graph_closed` alone.
    (_hK_compact : IsCompact K)
    (_hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z d : Y → EuclideanSpace ℝ (Fin n)}
    (hz_meas : Measurable z) (hd_meas : Measurable d)
    (hz_in_F : ∀ y, z y ∈ F y) :
    Measurable fun y => sSup {t : ℝ | 0 ≤ t ∧ z y + t • d y ∈ F y} := by
  -- Define the countable rational family using `Set.indicator` (avoids
  -- decidability issues with F-membership).
  set g : ℚ → Y → ℝ := fun q y =>
    {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y}.indicator
      (fun _ => (q : ℝ)) y with hg_def
  -- (1) Each g q is measurable.
  have hg_meas : ∀ q : ℚ, Measurable (g q) := by
    intro q
    have h_set_meas :
        MeasurableSet {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y} := by
      by_cases hq : (0 : ℝ) ≤ (q : ℝ)
      · have h_eq : {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y}
            = {y : Y | z y + (q : ℝ) • d y ∈ F y} := by
          ext y; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hq, h⟩⟩
        rw [h_eq]
        exact measurableSet_ray_in_fibre hF_graph_closed hz_meas hd_meas _
      · have h_eq : {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y}
            = ∅ := by
          ext y; exact ⟨fun ⟨h, _⟩ => (hq h).elim, fun h => h.elim⟩
        rw [h_eq]; exact MeasurableSet.empty
    exact (measurable_const : Measurable (fun _ : Y => (q : ℝ))).indicator h_set_meas
  -- Helper: evaluate `g q y` as `q` when `q` lies in `Gy ∩ [0,∞)`, else `0`.
  have h_g_eval_in : ∀ (q : ℚ) (y : Y),
      (0 : ℝ) ≤ (q : ℝ) → z y + (q : ℝ) • d y ∈ F y → g q y = (q : ℝ) := by
    intro q y hq h_in
    change {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y}.indicator
      (fun _ => (q : ℝ)) y = (q : ℝ)
    have h_mem : y ∈ {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y} :=
      ⟨hq, h_in⟩
    exact Set.indicator_of_mem h_mem (fun _ => (q : ℝ))
  have h_g_eval_out : ∀ (q : ℚ) (y : Y),
      ¬ ((0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y) → g q y = 0 := by
    intro q y h
    change {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y}.indicator
      (fun _ => (q : ℝ)) y = 0
    have h_notMem : y ∉ {y : Y | (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y} := h
    exact Set.indicator_of_notMem h_notMem (fun _ => (q : ℝ))
  -- (2) Pointwise identity sSup Gy = ⨆ q, g q y.
  have h_pt_eq : ∀ y,
      sSup {t : ℝ | 0 ≤ t ∧ z y + t • d y ∈ F y} = ⨆ q : ℚ, g q y := by
    intro y
    set Gy : Set ℝ := {t : ℝ | 0 ≤ t ∧ z y + t • d y ∈ F y} with hGy_def
    -- 0 ∈ Gy.
    have h0 : (0 : ℝ) ∈ Gy := by
      refine ⟨le_refl _, ?_⟩
      change z y + (0 : ℝ) • d y ∈ F y
      rw [zero_smul, add_zero]; exact hz_in_F y
    -- Segment property: t ∈ Gy → [0, t] ⊆ Gy.
    have h_seg : ∀ t ∈ Gy, ∀ s, 0 ≤ s → s ≤ t → s ∈ Gy := by
      intro t ht s hs0 hst
      have ht0 : 0 ≤ t := ht.1
      have ht_in : z y + t • d y ∈ F y := ht.2
      refine ⟨hs0, ?_⟩
      by_cases ht_eq : t = 0
      · have hs_eq : s = 0 := le_antisymm (ht_eq ▸ hst) hs0
        rw [hs_eq, zero_smul, add_zero]; exact hz_in_F y
      · have ht_pos : (0 : ℝ) < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
        set lam : ℝ := s / t with hlam_def
        have hlam0 : 0 ≤ lam := div_nonneg hs0 ht0
        have hlam1 : lam ≤ 1 := (div_le_one ht_pos).mpr hst
        have hμ0 : 0 ≤ 1 - lam := by linarith
        have h_sum : (1 - lam) + lam = 1 := by ring
        have hlamt : lam * t = s := by
          rw [hlam_def]; exact div_mul_cancel₀ s ht_eq
        have h_comb :
            z y + s • d y = (1 - lam) • z y + lam • (z y + t • d y) := by
          rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul,
            smul_smul, hlamt]
        rw [h_comb]
        exact hF_convex y (hz_in_F y) ht_in hμ0 hlam0 h_sum
    -- Density: every t > 0 in Gy is the limit of rational q ∈ Gy from below.
    have h_density : ∀ t ∈ Gy, ∀ ε > (0 : ℝ),
        ∃ q : ℚ, (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ∈ Gy ∧ t - ε < (q : ℝ) := by
      intro t ht ε hε
      obtain ⟨q, hq_lo, hq_hi⟩ := exists_rat_btwn (sub_lt_self t hε)
      -- max with 0 if needed.
      by_cases hq_pos : (0 : ℝ) ≤ (q : ℝ)
      · refine ⟨q, hq_pos, h_seg t ht (q : ℝ) hq_pos hq_hi.le, hq_lo⟩
      · -- q < 0; pick q' = 0 instead (since t - ε < 0 ≤ t).
        push Not at hq_pos
        refine ⟨0, ?_, ?_, ?_⟩
        · rw [Rat.cast_zero]
        · show ((0 : ℚ) : ℝ) ∈ Gy
          rw [Rat.cast_zero]; exact h0
        · rw [Rat.cast_zero]; linarith [ht.1]
    -- Case A: BddAbove Gy.
    by_cases h_bdd : BddAbove Gy
    · set b : ℝ := sSup Gy with hb_def
      have h_nonempty : Gy.Nonempty := ⟨0, h0⟩
      have hb_ub : ∀ t ∈ Gy, t ≤ b := fun t ht => le_csSup h_bdd ht
      have hb_nonneg : 0 ≤ b := hb_ub 0 h0
      -- Each `g q y` is bounded by `b`: either `q` is achieved (value `q ≤ b`) or `g q y = 0 ≤ b`.
      have h_g_le_b : ∀ q : ℚ, g q y ≤ b := by
        intro q
        by_cases h_cond : (0 : ℝ) ≤ (q : ℝ) ∧ z y + (q : ℝ) • d y ∈ F y
        · rw [h_g_eval_in q y h_cond.1 h_cond.2]
          exact hb_ub (q : ℝ) ⟨h_cond.1, h_cond.2⟩
        · rw [h_g_eval_out q y h_cond]; exact hb_nonneg
      -- Range of `g ·  y` is bounded by `b`.
      have h_bdd_range : BddAbove (Set.range (fun q : ℚ => g q y)) :=
        ⟨b, by rintro x ⟨q, rfl⟩; exact h_g_le_b q⟩
      apply le_antisymm
      · -- b ≤ ⨆ q, g q y.
        refine le_of_forall_lt_imp_le_of_dense ?_
        intro c hc_lt
        obtain ⟨t, ht_in, ht_gt⟩ := exists_lt_of_lt_csSup h_nonempty hc_lt
        -- Approximate t by rational q with c < q ≤ t, taking q ≥ 0.
        -- Case split on whether c ≥ 0.
        by_cases hc_nonneg : 0 ≤ c
        · obtain ⟨q, hqc, hqt⟩ := exists_rat_btwn ht_gt
          have hq_pos : (0 : ℝ) ≤ (q : ℝ) := le_trans hc_nonneg hqc.le
          have hq_in_Gy : (q : ℝ) ∈ Gy := h_seg t ht_in (q : ℝ) hq_pos hqt.le
          have h_g : g q y = (q : ℝ) := h_g_eval_in q y hq_pos hq_in_Gy.2
          calc c ≤ (q : ℝ) := hqc.le
            _ = g q y := h_g.symm
            _ ≤ ⨆ q : ℚ, g q y := le_ciSup h_bdd_range q
        · push Not at hc_nonneg
          -- c < 0; use q = 0.  The indicator value at `q = 0` is `0` regardless of membership.
          have h_g0 : g 0 y = 0 :=
            Set.indicator_apply_eq_zero.mpr (fun _ => by rw [Rat.cast_zero])
          calc c ≤ 0 := hc_nonneg.le
            _ = g 0 y := h_g0.symm
            _ ≤ ⨆ q : ℚ, g q y := le_ciSup h_bdd_range 0
      · -- ⨆ q ≤ b.
        exact ciSup_le h_g_le_b
    · -- Case B: Gy is unbounded above.  sSup = 0 by convention.
      have h_sSup_zero : sSup Gy = 0 := csSup_of_not_bddAbove h_bdd |>.trans Real.sSup_empty
      -- Range g_q is also unbounded.
      have h_range_unbdd : ¬ BddAbove (Set.range (fun q : ℚ => g q y)) := by
        intro ⟨B, hB⟩
        apply h_bdd
        refine ⟨B + 1, fun t ht => ?_⟩
        -- Approximate t by rational q ∈ Gy via segment with ε = 1.
        rcases h_density t ht 1 (by norm_num) with ⟨q, hq0, hq_in_Gy, hq_gt⟩
        have h_g : g q y = (q : ℝ) := h_g_eval_in q y hq0 hq_in_Gy.2
        have h_q_le : (q : ℝ) ≤ B := h_g ▸ hB ⟨q, rfl⟩
        linarith
      have h_iSup_zero : (⨆ q : ℚ, g q y) = 0 := by
        rw [iSup, csSup_of_not_bddAbove h_range_unbdd, Real.sSup_empty]
      rw [h_sSup_zero, h_iSup_zero]
  -- (3) Conclude.
  have h_funeq : (fun y => sSup {t : ℝ | 0 ≤ t ∧ z y + t • d y ∈ F y})
      = fun y => ⨆ q : ℚ, g q y := funext h_pt_eq
  rw [h_funeq]
  exact Measurable.iSup hg_meas

/-- Measurable exit point along a ray.

Given a measurable seed point `z` with `z y ∈ F y` and direction `d`, define
`exit y := z y + (max ray length at y) • d y`.  By closedness of `F y`, the exit point lies in
`F y`. -/
lemma measurable_exit_point
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z d : Y → EuclideanSpace ℝ (Fin n)}
    (hz_meas : Measurable z) (hd_meas : Measurable d)
    (hz_in_F : ∀ y, z y ∈ F y) :
    ∃ exit : Y → EuclideanSpace ℝ (Fin n), Measurable exit ∧
      (∀ y, exit y ∈ F y) := by
  -- exit y := z y + (max ray length) · d y.
  set t : Y → ℝ := fun y => sSup {s : ℝ | 0 ≤ s ∧ z y + s • d y ∈ F y} with ht_def
  have ht_meas : Measurable t :=
    measurable_max_ray_length hK_compact hF_sub_K hF_graph_closed hF_convex
      hz_meas hd_meas hz_in_F
  refine ⟨fun y => z y + t y • d y, ?_, ?_⟩
  · exact hz_meas.add (ht_meas.smul hd_meas)
  · intro y
    change z y + t y • d y ∈ F y
    -- Show t y ∈ Gy, hence z y + t y • d y ∈ F y.
    set Gy : Set ℝ := {s : ℝ | 0 ≤ s ∧ z y + s • d y ∈ F y} with hGy_def
    have h0 : (0 : ℝ) ∈ Gy := by
      refine ⟨le_refl _, ?_⟩
      change z y + (0 : ℝ) • d y ∈ F y
      rw [zero_smul, add_zero]; exact hz_in_F y
    -- F y is closed (slice of closed graph).
    have hF_y_closed : IsClosed (F y) := by
      have h_slice : F y = {x : EuclideanSpace ℝ (Fin n) |
          (y, x) ∈ {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}} := by
        ext x; simp
      rw [h_slice]
      exact hF_graph_closed.preimage (continuous_const.prodMk continuous_id)
    -- Gy is closed: preimage of closed F y under continuous map intersected
    -- with closed [0, ∞).
    have hGy_closed : IsClosed Gy := by
      have h_line_cont : Continuous (fun s : ℝ => z y + s • d y) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have h_preimage : IsClosed ((fun s : ℝ => z y + s • d y) ⁻¹' F y) :=
        hF_y_closed.preimage h_line_cont
      have h_Ici : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
      have h_eq : Gy = Set.Ici (0 : ℝ) ∩ (fun s : ℝ => z y + s • d y) ⁻¹' F y := rfl
      rw [h_eq]
      exact h_Ici.inter h_preimage
    by_cases h_bdd : BddAbove Gy
    · -- Bounded: t y = sSup Gy ∈ Gy by closedness.
      have ht_mem : t y ∈ Gy := hGy_closed.csSup_mem ⟨0, h0⟩ h_bdd
      exact ht_mem.2
    · -- Unbounded: t y = 0 by Real convention, so exit y = z y ∈ F y.
      have ht_zero : t y = 0 :=
        (csSup_of_not_bddAbove h_bdd).trans Real.sSup_empty
      rw [ht_zero, zero_smul, add_zero]
      exact hz_in_F y

/-! ## Joint measurability of extreme points -/

/-- Internal: The joint "non-extreme-at-scale `k`" multifunction.

`{(y, x) | x ∈ nonExtremeAtScale (F y) k}` has closed graph in `Y × ℝⁿ` by the tube-lemma machinery
in `MeasurableSelection.lean`. -/
private lemma isClosed_nonExtremeAtScale_graph
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (k : ℕ) :
    IsClosed
      {q : Y × EuclideanSpace ℝ (Fin n) |
        q.2 ∈ nonExtremeAtScale (F q.1) k} := by
  -- Multifunction G : (Y × ℝⁿ) → Set (ℝⁿ × ℝⁿ),
  --   G (y, x) := {(p₁, p₂) ∈ F y × F y | 1/(k+1) ≤ ‖p₁-p₂‖ ∧ mid p₁ p₂ = x}.
  -- G compact-bound by K × K, closed graph; "G nonempty" iff (y, x) is in
  -- the parametric `nonExtremeAtScale` graph.
  set G : Y × EuclideanSpace ℝ (Fin n) →
      Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun q => {p | p.1 ∈ F q.1 ∧ p.2 ∈ F q.1 ∧
      (1 : ℝ) / (k + 1) ≤ ‖p.1 - p.2‖ ∧ mid p.1 p.2 = q.2} with hG_def
  have hKK_compact : IsCompact (K ×ˢ K) := hK_compact.prod hK_compact
  have hG_sub : ∀ q, G q ⊆ K ×ˢ K := by
    intro q p ⟨hp1, hp2, _, _⟩
    exact ⟨hF_sub_K q.1 hp1, hF_sub_K q.1 hp2⟩
  have hG_graph_closed :
      IsClosed {r : (Y × EuclideanSpace ℝ (Fin n)) ×
                    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
        r.2 ∈ G r.1} := by
    have h_proj_y := continuous_fst.comp
      (continuous_fst (X := Y × EuclideanSpace ℝ (Fin n))
        (Y := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    have h_proj_x := continuous_snd.comp
      (continuous_fst (X := Y × EuclideanSpace ℝ (Fin n))
        (Y := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    have h_proj_p1 := continuous_fst.comp
      (continuous_snd (X := Y × EuclideanSpace ℝ (Fin n))
        (Y := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    have h_proj_p2 := continuous_snd.comp
      (continuous_snd (X := Y × EuclideanSpace ℝ (Fin n))
        (Y := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    have h1 :
        IsClosed {r : (Y × EuclideanSpace ℝ (Fin n)) ×
                    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
            r.2.1 ∈ F r.1.1} :=
      hF_graph_closed.preimage (h_proj_y.prodMk h_proj_p1)
    have h2 :
        IsClosed {r : (Y × EuclideanSpace ℝ (Fin n)) ×
                    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
            r.2.2 ∈ F r.1.1} :=
      hF_graph_closed.preimage (h_proj_y.prodMk h_proj_p2)
    have h3 :
        IsClosed {r : (Y × EuclideanSpace ℝ (Fin n)) ×
                    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
            (1 : ℝ) / (k + 1) ≤ ‖r.2.1 - r.2.2‖} :=
      isClosed_le continuous_const (h_proj_p1.sub h_proj_p2).norm
    have h_mid_cont : Continuous (fun r : (Y × EuclideanSpace ℝ (Fin n)) ×
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
            mid r.2.1 r.2.2) :=
      mid_continuous.comp (h_proj_p1.prodMk h_proj_p2)
    have h4 :
        IsClosed {r : (Y × EuclideanSpace ℝ (Fin n)) ×
                    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) |
            mid r.2.1 r.2.2 = r.1.2} :=
      isClosed_eq h_mid_cont h_proj_x
    have h_set_eq :
        {r : (Y × EuclideanSpace ℝ (Fin n)) ×
              (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) | r.2 ∈ G r.1}
          = ({r | r.2.1 ∈ F r.1.1} ∩ {r | r.2.2 ∈ F r.1.1}) ∩
              ({r | (1 : ℝ) / (k + 1) ≤ ‖r.2.1 - r.2.2‖} ∩
                {r | mid r.2.1 r.2.2 = r.1.2}) := by
      ext r
      simp only [hG_def, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [h_set_eq]
    exact (h1.inter h2).inter (h3.inter h4)
  have h_inter :=
    MeasureTheory.isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
      hKK_compact hG_sub hG_graph_closed (C := Set.univ) isClosed_univ
  have h_eq :
      {q : Y × EuclideanSpace ℝ (Fin n) | (G q ∩ Set.univ).Nonempty}
        = {q : Y × EuclideanSpace ℝ (Fin n) |
          q.2 ∈ nonExtremeAtScale (F q.1) k} := by
    ext q
    simp only [hG_def, Set.inter_univ, Set.mem_setOf_eq, nonExtremeAtScale,
      Set.mem_image]
    constructor
    · rintro ⟨⟨p₁, p₂⟩, hp1, hp2, hdist, hmid⟩
      exact ⟨(p₁, p₂), ⟨hp1, hp2, hdist⟩, hmid⟩
    · rintro ⟨⟨p₁, p₂⟩, ⟨hp1, hp2, hdist⟩, hmid⟩
      exact ⟨(p₁, p₂), hp1, hp2, hdist, hmid⟩
  rw [← h_eq]
  exact h_inter

/-- Joint Borel measurability of the extreme-points multifunction.

For closed-graph compact-bound convex-valued `F`, the graph `{(y, ω) | ω ∈ extremePoints (F y)}` is
Borel-measurable in `Y × ℝⁿ`. -/
lemma measurableSet_extremePoints_graph
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y)) :
    MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ Set.extremePoints ℝ (F p.1)} := by
  have h_eq :
      {p : Y × EuclideanSpace ℝ (Fin n) |
          p.2 ∈ Set.extremePoints ℝ (F p.1)}
        = {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} \
            ⋃ k : ℕ,
              {q : Y × EuclideanSpace ℝ (Fin n) |
                q.2 ∈ nonExtremeAtScale (F q.1) k} := by
    ext p
    have hpoint := extremePoints_eq_diff_iUnion (hF_convex p.1)
    simp only [Set.ext_iff] at hpoint
    have := hpoint p.2
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq] at this ⊢
    exact this
  rw [h_eq]
  refine hF_graph_closed.measurableSet.diff ?_
  refine MeasurableSet.iUnion fun k => ?_
  exact
    (isClosed_nonExtremeAtScale_graph hK_compact hF_sub_K
      hF_graph_closed k).measurableSet

/-! ## Measurable face peeling -/

/-- Measurable relative tangent space.

For closed-graph compact-bound `F` and measurable `z(y) ∈ F y`, the graph
`{(y, v) | ∃ ε > 0, z y + ε•v ∈ F y ∧ z y - ε•v ∈ F y}` is Borel-measurable in `Y × ℝⁿ`. -/
lemma measurable_relTangentSpace_graph
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    -- Compactness of the ambient bound `K` is carried for symmetry with the rest of the
    -- measurable-Carathéodory pipeline; this lemma only needs the closed graph and convexity.
    (_hK_compact : IsCompact K)
    (_hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z : Y → EuclideanSpace ℝ (Fin n)}
    (hz_meas : Measurable z) (hz_mem : ∀ y, z y ∈ F y) :
    MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) |
        ∃ ε > (0 : ℝ), z p.1 + ε • p.2 ∈ F p.1 ∧ z p.1 - ε • p.2 ∈ F p.1} := by
  -- Rewrite the ∃-set as ⋃ over k : ℕ of "ε = 1/(k+1)" instances.
  have hF_meas : MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} :=
    hF_graph_closed.measurableSet
  -- For each k, the set with ε = 1/(k+1) is measurable.
  have h_per_k : ∀ k : ℕ,
      MeasurableSet
        {p : Y × EuclideanSpace ℝ (Fin n) |
          z p.1 + (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1 ∧
          z p.1 - (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1} := by
    intro k
    -- Map 1: (y, v) ↦ (y, z y + (1/(k+1))·v).
    have h_map1 : Measurable (fun p : Y × EuclideanSpace ℝ (Fin n) =>
        (p.1, z p.1 + (1 / ((k : ℝ) + 1)) • p.2)) := by
      refine measurable_fst.prodMk ?_
      exact (hz_meas.comp measurable_fst).add
        ((measurable_const).smul measurable_snd)
    have h_set1 : MeasurableSet
        {p : Y × EuclideanSpace ℝ (Fin n) |
          z p.1 + (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1} := h_map1 hF_meas
    have h_map2 : Measurable (fun p : Y × EuclideanSpace ℝ (Fin n) =>
        (p.1, z p.1 - (1 / ((k : ℝ) + 1)) • p.2)) := by
      refine measurable_fst.prodMk ?_
      exact (hz_meas.comp measurable_fst).sub
        ((measurable_const).smul measurable_snd)
    have h_set2 : MeasurableSet
        {p : Y × EuclideanSpace ℝ (Fin n) |
          z p.1 - (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1} := h_map2 hF_meas
    exact h_set1.inter h_set2
  -- The ∃-set equals the countable union of per-k sets.
  have h_eq :
      {p : Y × EuclideanSpace ℝ (Fin n) |
          ∃ ε > (0 : ℝ), z p.1 + ε • p.2 ∈ F p.1 ∧ z p.1 - ε • p.2 ∈ F p.1}
        = ⋃ k : ℕ, {p : Y × EuclideanSpace ℝ (Fin n) |
            z p.1 + (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1 ∧
            z p.1 - (1 / ((k : ℝ) + 1)) • p.2 ∈ F p.1} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨ε, hε_pos, hε_plus, hε_minus⟩
      -- Pick k : ℕ such that 1/(k+1) ≤ ε.
      obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
      have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h_inv_le : 1 / ((k : ℝ) + 1) ≤ ε := by
        rw [div_le_iff₀ hk1_pos]
        rw [div_lt_iff₀ hε_pos] at hk
        nlinarith
      have h_inv_pos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      -- By convexity: z y + (1/(k+1))·v is on the segment from z y to z y + ε·v.
      -- Specifically, with α := (1/(k+1)) / ε ∈ [0, 1]:
      --   z y + (1/(k+1))·v = (1-α) z y + α (z y + ε·v).
      refine ⟨k, ?_, ?_⟩
      · -- z y + (1/(k+1))•v ∈ F y via convex combination
        set α : ℝ := (1 / ((k : ℝ) + 1)) / ε with hα_def
        have hα_nonneg : 0 ≤ α := by positivity
        have hα_le_one : α ≤ 1 := by
          rw [hα_def, div_le_one hε_pos]; exact h_inv_le
        have h_combo :
            z p.1 + (1 / ((k : ℝ) + 1)) • p.2
              = (1 - α) • z p.1 + α • (z p.1 + ε • p.2) := by
          have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
          simp only [hα_def, smul_add, sub_smul, one_smul]
          have h1 : (1 / ((k : ℝ) + 1) / ε) • (ε • p.2) =
              (1 / ((k : ℝ) + 1)) • p.2 := by
            rw [smul_smul, div_mul_cancel₀ _ hε_ne]
          rw [← h1]; module
        rw [h_combo]
        exact hF_convex p.1 (hz_mem p.1) hε_plus (by linarith)
          hα_nonneg (by linarith)
      · -- z y - (1/(k+1))•v ∈ F y, similar
        set α : ℝ := (1 / ((k : ℝ) + 1)) / ε with hα_def
        have hα_nonneg : 0 ≤ α := by positivity
        have hα_le_one : α ≤ 1 := by
          rw [hα_def, div_le_one hε_pos]; exact h_inv_le
        have h_combo :
            z p.1 - (1 / ((k : ℝ) + 1)) • p.2
              = (1 - α) • z p.1 + α • (z p.1 - ε • p.2) := by
          have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
          simp only [hα_def, smul_sub, sub_smul, one_smul]
          have h1 : (1 / ((k : ℝ) + 1) / ε) • (ε • p.2) =
              (1 / ((k : ℝ) + 1)) • p.2 := by
            rw [smul_smul, div_mul_cancel₀ _ hε_ne]
          rw [← h1]; module
        rw [h_combo]
        exact hF_convex p.1 (hz_mem p.1) hε_minus (by linarith)
          hα_nonneg (by linarith)
    · rintro ⟨k, hk⟩
      exact ⟨1 / ((k : ℝ) + 1), by positivity, hk.1, hk.2⟩
  rw [h_eq]
  exact MeasurableSet.iUnion h_per_k

/-! ### Measurable dimension of the relative tangent space

For closed-graph compact-bound convex-valued `F` and any point `z ∈ ℝⁿ`, the relative tangent
space `T(y, z) := {v | ∃ ε > 0, z + ε•v ∈ F y ∧ z - ε•v ∈ F y}` is a linear subspace of `ℝⁿ`. The
joint dimension function `(y, z) ↦ dim T(y, z)` is Borel-measurable on `Y × ℝⁿ`; composing with a
measurable `z : Y → ℝⁿ` gives `y ↦ dim T(y, z y)`. -/

/-- The Gram determinant of a `k`-tuple `v : Fin k → ℝⁿ`.

`gramDet v = det ⟨v_i, v_j⟩_{i,j}` is continuous, nonnegative, and positive iff the `v_i` are
linearly independent. -/
private noncomputable def gramDet {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Matrix.gram ℝ v).det

private lemma continuous_gramDet {n k : ℕ} :
    Continuous fun v : Fin k → EuclideanSpace ℝ (Fin n) => gramDet v := by
  unfold gramDet
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  -- Each entry `Matrix.gram ℝ v i j = ⟨v i, v j⟩` is continuous in v.
  have h_eq : (fun v : Fin k → EuclideanSpace ℝ (Fin n) => Matrix.gram (𝕜 := ℝ) v i j)
      = fun v => @inner ℝ _ _ (v i) (v j) := by
    funext v; exact Matrix.gram_apply v i j
  rw [h_eq]
  exact (continuous_apply i).inner (continuous_apply j)

private lemma linearIndependent_iff_gramDet_pos {n k : ℕ}
    (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    LinearIndependent ℝ v ↔ 0 < gramDet v := by
  unfold gramDet
  constructor
  · intro hv
    exact (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  · intro h_det
    -- Gram is PosSemidef + det ≠ 0 → PosDef → LinearIndependent.
    have h_PS : (Matrix.gram ℝ v).PosSemidef := Matrix.posSemidef_gram ℝ v
    have h_unit : IsUnit (Matrix.gram ℝ v).det := isUnit_iff_ne_zero.mpr (ne_of_gt h_det)
    have h_PD : (Matrix.gram ℝ v).PosDef :=
      h_PS.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr h_unit)
    exact Matrix.posDef_gram_iff_linearIndependent.mp h_PD

private lemma isClosed_setOf_gramDet_ge {n k : ℕ} (ε : ℝ) :
    IsClosed {v : Fin k → EuclideanSpace ℝ (Fin n) | gramDet v ≥ ε} :=
  (isClosed_Ici (a := ε)).preimage continuous_gramDet

/-- For each `m`, the "scale-`1/(m+1)`" relative tangent set has closed graph in `(Y × ℝⁿ) × ℝⁿ`,
treating `z ∈ ℝⁿ` as a free coordinate. -/
private lemma isClosed_graph_Tm
    {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (m : ℕ) :
    IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
      q.1.2 + (1 / ((m : ℝ) + 1)) • q.2 ∈ F q.1.1 ∧
      q.1.2 - (1 / ((m : ℝ) + 1)) • q.2 ∈ F q.1.1} := by
  have h_plus :
      IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
        q.1.2 + (1 / ((m : ℝ) + 1)) • q.2 ∈ F q.1.1} := by
    have h_cont : Continuous (fun q : (Y × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => (q.1.1, q.1.2 + (1 / ((m : ℝ) + 1)) • q.2)) := by
      refine Continuous.prodMk ?_ ?_
      · exact (continuous_fst.comp continuous_fst)
      · exact (continuous_snd.comp continuous_fst).add
          (continuous_const.smul continuous_snd)
    exact hF_graph_closed.preimage h_cont
  have h_minus :
      IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
        q.1.2 - (1 / ((m : ℝ) + 1)) • q.2 ∈ F q.1.1} := by
    have h_cont : Continuous (fun q : (Y × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) => (q.1.1, q.1.2 - (1 / ((m : ℝ) + 1)) • q.2)) := by
      refine Continuous.prodMk ?_ ?_
      · exact (continuous_fst.comp continuous_fst)
      · exact (continuous_snd.comp continuous_fst).sub
          (continuous_const.smul continuous_snd)
    exact hF_graph_closed.preimage h_cont
  exact h_plus.inter h_minus

/-- The set `{v : Fin k → ℝⁿ | ∀ i, p.2 + 1/(m+1) v i ∈ F p.1 ∧ p.2 - 1/(m+1) v i ∈ F p.1}`,
parametrised over `p : Y × ℝⁿ`, has closed graph in `(Y × ℝⁿ) × (Fin k → ℝⁿ)`. -/
private lemma isClosed_graph_TmPow
    {n k : ℕ} {Y : Type*} [TopologicalSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (m : ℕ) :
    IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) × (Fin k → EuclideanSpace ℝ (Fin n)) |
      ∀ i, q.1.2 + (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1 ∧
           q.1.2 - (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1} := by
  rw [show {q : (Y × EuclideanSpace ℝ (Fin n)) × (Fin k → EuclideanSpace ℝ (Fin n)) |
        ∀ i, q.1.2 + (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1 ∧
             q.1.2 - (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1}
        = ⋂ i : Fin k, {q | q.1.2 + (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1 ∧
                            q.1.2 - (1 / ((m : ℝ) + 1)) • q.2 i ∈ F q.1.1}
        from by ext q; simp]
  refine isClosed_iInter fun i => ?_
  -- pull back along `q ↦ ((q.1.1, q.1.2 ± 1/(m+1) q.2 i), q.2 i)` not needed;
  -- reuse `isClosed_graph_Tm` via the continuous map projecting out the i-th vector.
  have h_proj : Continuous
      (fun q : (Y × EuclideanSpace ℝ (Fin n)) × (Fin k → EuclideanSpace ℝ (Fin n)) =>
        (q.1, q.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  exact (isClosed_graph_Tm hF_graph_closed m).preimage h_proj

/-- Uniform compact bound for the "scale-`1/(m+1)`" relative tangent set.

If `z + 1/(m+1) v ∈ K` and `z - 1/(m+1) v ∈ K`, then
`v = ((m+1)/2) · [(z + 1/(m+1) v) - (z - 1/(m+1) v)] ∈ ((m+1)/2) (K - K)`.

This bound is uniform — it does *not* require `z ∈ K`. -/
private noncomputable def TmUniformBound {n : ℕ}
    (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (((m : ℝ) + 1) / 2) • (K - K)

private lemma isCompact_TmUniformBound {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K) (m : ℕ) :
    IsCompact (TmUniformBound m K) := by
  unfold TmUniformBound
  -- K - K = image of K × K under (·-·); compact via continuous image.
  have h_image : (K : Set (EuclideanSpace ℝ (Fin n))) - K
      = (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 - p.2) '' (K ×ˢ K) := by
    ext x
    simp only [Set.mem_image, Set.mem_prod, Prod.exists, Set.mem_sub]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [h_image]
  exact ((hK_compact.prod hK_compact).image (continuous_fst.sub continuous_snd)).smul _

private lemma TmPow_sub_TmUniformBound {n k : ℕ} {Y : Type*}
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hF_sub_K : ∀ y, F y ⊆ K)
    (m : ℕ) :
    ∀ p : Y × EuclideanSpace ℝ (Fin n),
      {v : Fin k → EuclideanSpace ℝ (Fin n) |
        ∀ i, p.2 + (1 / ((m : ℝ) + 1)) • v i ∈ F p.1 ∧
             p.2 - (1 / ((m : ℝ) + 1)) • v i ∈ F p.1}
        ⊆ Set.pi Set.univ (fun _ => TmUniformBound m K) := by
  intro p v hv i _
  rcases hv i with ⟨h_plus, h_minus⟩
  -- v_i = ((m+1)/2) · [(z + 1/(m+1) v_i) - (z - 1/(m+1) v_i)].
  refine ⟨(p.2 + (1 / ((m : ℝ) + 1)) • v i) - (p.2 - (1 / ((m : ℝ) + 1)) • v i),
          ⟨_, hF_sub_K _ h_plus, _, hF_sub_K _ h_minus, rfl⟩, ?_⟩
  -- Algebra: ((m+1)/2) · (2 · (1/(m+1)) v) = v.
  have hmp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmp_ne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hmp
  simp only
  have h_simp :
      ((m : ℝ) + 1) / 2 *
        (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1)) = 1 := by
    field_simp; ring
  have h_smul :
      (((m : ℝ) + 1) / 2) •
        ((p.2 + (1 / ((m : ℝ) + 1)) • v i) - (p.2 - (1 / ((m : ℝ) + 1)) • v i))
        = (((m : ℝ) + 1) / 2 *
            (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1))) • v i := by
    rw [smul_sub, smul_add, smul_sub]
    module
  rw [h_smul, h_simp, one_smul]

/-- The jointly-closed Fσ building block for `measurable_finrank_relTangent`.

For
each
`m, k : ℕ`
and
`ε : ℝ`,
the
set
`{(y, z') | ∃ v : Fin k → ℝⁿ, (∀ i, z' + 1/(m+1) v i ∈ F y ∧ z' - 1/(m+1) v i ∈ F y)
   ∧ gramDet v ≥ ε}`
is closed in `Y × ℝⁿ`. -/
private lemma isClosed_existsTmPow_gramDet_ge
    {n k : ℕ} {Y : Type*} [TopologicalSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (m : ℕ) (ε : ℝ) :
    IsClosed {p : Y × EuclideanSpace ℝ (Fin n) |
      ∃ v : Fin k → EuclideanSpace ℝ (Fin n),
        (∀ i, p.2 + (1 / ((m : ℝ) + 1)) • v i ∈ F p.1 ∧
              p.2 - (1 / ((m : ℝ) + 1)) • v i ∈ F p.1) ∧
        gramDet v ≥ ε} := by
  set G : (Y × EuclideanSpace ℝ (Fin n)) → Set (Fin k → EuclideanSpace ℝ (Fin n)) :=
    fun p => {v | ∀ i, p.2 + (1 / ((m : ℝ) + 1)) • v i ∈ F p.1 ∧
                       p.2 - (1 / ((m : ℝ) + 1)) • v i ∈ F p.1} with hG
  have hG_graph : IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) ×
      (Fin k → EuclideanSpace ℝ (Fin n)) | q.2 ∈ G q.1} :=
    isClosed_graph_TmPow hF_graph_closed m
  have hG_bound : ∀ p, G p ⊆ Set.pi Set.univ (fun _ : Fin k => TmUniformBound m K) :=
    TmPow_sub_TmUniformBound hF_sub_K m
  have hKpi_compact : IsCompact (Set.pi Set.univ
      (fun _ : Fin k => TmUniformBound m K)) :=
    isCompact_univ_pi (fun _ => isCompact_TmUniformBound hK_compact m)
  have hC_closed : IsClosed {v : Fin k → EuclideanSpace ℝ (Fin n) | gramDet v ≥ ε} :=
    isClosed_setOf_gramDet_ge ε
  have h := MeasureTheory.isClosed_setOf_inter_nonempty_of_closedGraph_compactBound
    hKpi_compact hG_bound hG_graph hC_closed
  convert h using 1

/-- Level-set characterization of `finrank` of the joint relative tangent space.

`{(y, z') | finrank (Submodule.span ℝ T(y, z')) ≥ k}` equals a countable union over `m, q` of the
closed sets `{(y, z') | ∃ v : Fin k → ℝⁿ in T_m(y, z')^k, gramDet v ≥ 1/(q+1)}`, hence is `Fσ` and
measurable. Convexity of `F` is used for the inclusion that scales an independent `k`-tuple into a
common `T_m`. -/
private lemma measurableSet_finrank_ge_joint
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    (k : ℕ) :
    MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) |
        k ≤ Module.finrank ℝ
          (Submodule.span ℝ
            {v : EuclideanSpace ℝ (Fin n) |
              ∃ ε > (0 : ℝ), p.2 + ε • v ∈ F p.1 ∧ p.2 - ε • v ∈ F p.1})} := by
  -- Express LHS as a countable Fσ-union, each piece given by
  -- `isClosed_existsTmPow_gramDet_ge`.
  set T : (Y × EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun p => {v | ∃ ε > (0 : ℝ), p.2 + ε • v ∈ F p.1 ∧ p.2 - ε • v ∈ F p.1} with hT
  set Tm : ℕ → (Y × EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun m p => {v | p.2 + (1 / ((m : ℝ) + 1)) • v ∈ F p.1 ∧
                    p.2 - (1 / ((m : ℝ) + 1)) • v ∈ F p.1} with hTm
  have h_eq :
      {p : Y × EuclideanSpace ℝ (Fin n) |
          k ≤ Module.finrank ℝ (Submodule.span ℝ (T p))}
        = ⋃ m : ℕ, ⋃ q : ℕ,
          {p : Y × EuclideanSpace ℝ (Fin n) |
            ∃ v : Fin k → EuclideanSpace ℝ (Fin n),
              (∀ i, v i ∈ Tm m p) ∧ gramDet v ≥ 1 / ((q : ℝ) + 1)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · -- Forward: k ≤ finrank → ∃ m q v, ...
      intro hk
      -- Case k = 0: vacuous family suffices.
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · refine ⟨0, 0, Fin.elim0, fun i => i.elim0, ?_⟩
        unfold gramDet
        simp
      -- Case k ≥ 1.
      haveI : Nonempty (Fin k) := ⟨⟨0, hk_pos⟩⟩
      have hT_nonempty : (T p).Nonempty := by
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty] at h
        rw [h, Submodule.span_empty, finrank_bot] at hk
        omega
      obtain ⟨v0, ε0, hε0_pos, hε0_plus, hε0_minus⟩ := hT_nonempty
      have hp2_mem : p.2 ∈ F p.1 := by
        have h_eq : p.2 = (1/2 : ℝ) • (p.2 + ε0 • v0) + (1/2 : ℝ) • (p.2 - ε0 • v0) := by
          module
        rw [h_eq]
        exact hF_convex _ hε0_plus hε0_minus
          (by norm_num) (by norm_num) (by norm_num)
      obtain ⟨b, hb_sub, hb_span, hb_indep⟩ := exists_linearIndependent ℝ (T p)
      haveI : Module.Finite ℝ (EuclideanSpace ℝ (Fin n)) := inferInstance
      have hb_finite_type : Finite b := LinearIndependent.finite hb_indep
      have hb_finite : b.Finite := Set.toFinite b
      haveI : Fintype b := hb_finite.fintype
      have h_card_eq :
          hb_finite.toFinset.card = Module.finrank ℝ (Submodule.span ℝ (T p)) := by
        rw [Set.Finite.card_toFinset, ← hb_span,
            finrank_span_set_eq_card (s := b) hb_indep, Set.toFinset_card]
      have h_card_ge : k ≤ hb_finite.toFinset.card := h_card_eq.symm ▸ hk
      obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq h_card_ge
      let φ : Fin k ≃ (t : Finset (EuclideanSpace ℝ (Fin n))) :=
        (Finset.equivFinOfCardEq ht_card).symm
      let v : Fin k → EuclideanSpace ℝ (Fin n) := fun i => ((φ i) : EuclideanSpace ℝ (Fin n))
      have hv_in_T : ∀ i, v i ∈ T p := by
        intro i
        have h_in_t : (v i) ∈ t := (φ i).2
        have h_in_bf : (v i) ∈ hb_finite.toFinset := ht_sub h_in_t
        exact hb_sub (hb_finite.mem_toFinset.mp h_in_bf)
      have hv_indep : LinearIndependent ℝ v := by
        -- `v = (Subtype.val : b → V) ∘ e` for an injective `e : Fin k → b`.
        let e : Fin k → b := fun i =>
          ⟨v i, hb_finite.mem_toFinset.mp (ht_sub (φ i).2)⟩
        have h_inj : Function.Injective e := by
          intro i j hij
          apply φ.injective
          apply Subtype.ext
          have h_val : (e i).val = (e j).val := by rw [hij]
          exact h_val
        have : LinearIndependent ℝ (Subtype.val ∘ e) := hb_indep.comp e h_inj
        exact this
      have hv_data : ∀ i, ∃ ε : ℝ, 0 < ε ∧
          p.2 + ε • v i ∈ F p.1 ∧ p.2 - ε • v i ∈ F p.1 := fun i => hv_in_T i
      choose ε hε_pos hε_plus hε_minus using hv_data
      have hε_min_pos : (0 : ℝ) < Finset.univ.inf' Finset.univ_nonempty ε := by
        rw [Finset.lt_inf'_iff]
        intro i _; exact hε_pos i
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε_min_pos
      have hm_le : ∀ i, 1 / ((m : ℝ) + 1) ≤ ε i := by
        intro i
        have h_inf : Finset.univ.inf' Finset.univ_nonempty ε ≤ ε i :=
          Finset.inf'_le _ (Finset.mem_univ i)
        linarith
      have hv_in_Tm : ∀ i, v i ∈ Tm m p := by
        intro i
        rw [hTm, Set.mem_setOf_eq]
        have h_t_div_mem :
            (1 / ((m : ℝ) + 1)) / ε i ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (by positivity) (le_of_lt (hε_pos i)), ?_⟩
          rw [div_le_one (hε_pos i)]
          exact hm_le i
        refine ⟨?_, ?_⟩
        · -- `p.2 + 1/(m+1) • v i ∈ F p.1`.
          have h_xy_in : p.2 + (ε i • v i) ∈ F p.1 := hε_plus i
          have h_scaled :=
            (hF_convex p.1).add_smul_mem hp2_mem h_xy_in h_t_div_mem
          rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt (hε_pos i))] at h_scaled
          exact h_scaled
        · -- `p.2 - 1/(m+1) • v i ∈ F p.1`.
          have h_xy_in : p.2 + (ε i • (-v i)) ∈ F p.1 := by
            rw [smul_neg, ← sub_eq_add_neg]; exact hε_minus i
          have h_scaled :=
            (hF_convex p.1).add_smul_mem hp2_mem h_xy_in h_t_div_mem
          rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt (hε_pos i)), smul_neg,
              ← sub_eq_add_neg] at h_scaled
          exact h_scaled
      have h_gram_pos : 0 < gramDet v :=
        (linearIndependent_iff_gramDet_pos v).mp hv_indep
      obtain ⟨q, hq⟩ := exists_nat_one_div_lt h_gram_pos
      exact ⟨m, q, v, hv_in_Tm, le_of_lt hq⟩
    · -- Backward: from a Gram-positive `v ∈ Tm m p^k`, conclude k ≤ finrank (span T(p)).
      rintro ⟨m, q, v, hv, hg⟩
      have hq_pos : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
      have h_pos : 0 < gramDet v := lt_of_lt_of_le hq_pos hg
      have h_indep : LinearIndependent ℝ v :=
        (linearIndependent_iff_gramDet_pos v).mpr h_pos
      have h_v_in_T : ∀ i, v i ∈ T p := fun i =>
        ⟨1 / ((m : ℝ) + 1), by positivity, (hv i).1, (hv i).2⟩
      have h_range_sub : Set.range v ⊆ (Submodule.span ℝ (T p) : Set _) := by
        rintro _ ⟨i, rfl⟩; exact Submodule.subset_span (h_v_in_T i)
      have h_span_le : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (T p) :=
        Submodule.span_le.mpr h_range_sub
      have h_finrank_eq :
          Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = k := by
        rw [finrank_span_eq_card h_indep, Fintype.card_fin]
      calc k = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := h_finrank_eq.symm
           _ ≤ Module.finrank ℝ (Submodule.span ℝ (T p)) :=
              Submodule.finrank_mono h_span_le
  rw [h_eq]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun q => ?_
  refine (isClosed_existsTmPow_gramDet_ge hK_compact hF_sub_K hF_graph_closed
    m (1 / ((q : ℝ) + 1))).measurableSet

/-- Dimension of the relative tangent space is Borel-measurable.

For closed-graph compact-bound convex-valued `F` and measurable `z y ∈ F y`, the function
`y ↦ dim T(y)` is Borel-measurable, where
`T(y) := {v | ∃ ε > 0, z y + ε•v ∈ F y ∧ z y - ε•v ∈ F y}`. -/
lemma measurable_dim_relTangentSpace
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z : Y → EuclideanSpace ℝ (Fin n)}
    -- `z y ∈ F y` is required by `measurable_relTangentSpace_graph`'s statement of `T(y)`
    -- (see docstring); the finrank-level-set argument below only needs `z` measurable.
    (hz_meas : Measurable z) (_hz_mem : ∀ y, z y ∈ F y) :
    Measurable (fun y => Module.finrank ℝ
        (Submodule.span ℝ
          {v : EuclideanSpace ℝ (Fin n) |
            ∃ ε > (0 : ℝ), z y + ε • v ∈ F y ∧ z y - ε • v ∈ F y})) := by
  -- Reduce to: each level set `{y | finrank ≥ k}` is measurable.
  refine measurable_to_countable' fun ℓ => ?_
  -- Helper: measurable level set, obtained by pulling back the joint Fσ via
  -- `y ↦ (y, z y)` (measurable since `z` is).
  have h_meas_ge : ∀ k, MeasurableSet
      {y : Y | k ≤ Module.finrank ℝ
        (Submodule.span ℝ
          {v : EuclideanSpace ℝ (Fin n) |
            ∃ ε > (0 : ℝ), z y + ε • v ∈ F y ∧ z y - ε • v ∈ F y})} := by
    intro k
    have h_joint := measurableSet_finrank_ge_joint hK_compact hF_sub_K hF_graph_closed
      hF_convex k
    have h_map : Measurable (fun y : Y => (y, z y)) :=
      measurable_id.prodMk hz_meas
    exact h_map h_joint
  -- Use h_meas_ge to express the singleton preimage as `≥ ℓ` minus `≥ ℓ+1`.
  have h_eq :
      (fun y => Module.finrank ℝ
        (Submodule.span ℝ
          {v : EuclideanSpace ℝ (Fin n) |
            ∃ ε > (0 : ℝ), z y + ε • v ∈ F y ∧ z y - ε • v ∈ F y})) ⁻¹' {ℓ}
        = {y : Y | ℓ ≤ Module.finrank ℝ
            (Submodule.span ℝ
              {v : EuclideanSpace ℝ (Fin n) |
                ∃ ε > (0 : ℝ), z y + ε • v ∈ F y ∧ z y - ε • v ∈ F y})} ∩
          {y : Y | (ℓ + 1) ≤ Module.finrank ℝ
            (Submodule.span ℝ
              {v : EuclideanSpace ℝ (Fin n) |
                ∃ ε > (0 : ℝ), z y + ε • v ∈ F y ∧ z y - ε • v ∈ F y})}ᶜ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    omega
  rw [h_eq]
  exact (h_meas_ge ℓ).inter (h_meas_ge (ℓ + 1)).compl

/-! ### Measurable descent direction

A measurable choice of descent direction `d y ∈ T(y)` with `d y = 0` exactly when `T(y) = {0}`
— equivalently, when `z y` is already an extreme point of `F y`. -/

/-- Non-degeneracy of lex-max for symmetric sets.

If `S ⊆ ℝⁿ` is closed under negation and contains `0`, and `g ∈ S` satisfies the lex-max property
`∀ x ∈ S, ∀ i, agreement on first i-1
coords ⟹ x_i ≤ g_i`, then `g = 0 ↔ S = {0}`. -/
private lemma lexMax_eq_zero_iff_singleton
    {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (h_zero : (0 : EuclideanSpace ℝ (Fin n)) ∈ S)
    (h_sym : ∀ v ∈ S, -v ∈ S)
    {g : EuclideanSpace ℝ (Fin n)} (hg_mem : g ∈ S)
    (hg_lex : ∀ x ∈ S, ∀ i : Fin n,
      (∀ j : Fin n, j < i → x.ofLp j = g.ofLp j) → x.ofLp i ≤ g.ofLp i) :
    g = 0 ↔ S = {0} := by
  refine ⟨fun hg_zero => ?_, fun hS_eq => ?_⟩
  · -- Forward: g = 0 ⟹ S = {0}.
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨h_zero, fun v hv => ?_⟩
    apply WithLp.ofLp_injective 2
    rw [WithLp.ofLp_zero]
    funext i
    -- Strong induction on `i.val`: show `v.ofLp j = 0` for `j.val < k`.
    have h_all : ∀ k : ℕ, ∀ j : Fin n, j.val < k → v.ofLp j = 0 := by
      intro k
      induction k with
      | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
      | succ k ih =>
        intro j hj
        by_cases hj_lt : j.val < k
        · exact ih j hj_lt
        · -- j.val = k.  Apply lex-max with full agreement on prior coords.
          have hj_eq : j.val = k := by omega
          have hg_j : g.ofLp j = 0 := by
            rw [hg_zero, WithLp.ofLp_zero]; rfl
          have h_agree : ∀ j' : Fin n, j' < j → v.ofLp j' = g.ofLp j' := by
            intro j' hj'_lt
            have h_lt_k : j'.val < k := hj_eq ▸ hj'_lt
            have hg_j' : g.ofLp j' = 0 := by
              rw [hg_zero, WithLp.ofLp_zero]; rfl
            rw [ih j' h_lt_k, hg_j']
          have h_neg_agree : ∀ j' : Fin n, j' < j → (-v).ofLp j' = g.ofLp j' := by
            intro j' hj'_lt
            have h_lt_k : j'.val < k := hj_eq ▸ hj'_lt
            have hg_j' : g.ofLp j' = 0 := by
              rw [hg_zero, WithLp.ofLp_zero]; rfl
            rw [WithLp.ofLp_neg, Pi.neg_apply, ih j' h_lt_k, hg_j']
            ring
          have h_v_le : v.ofLp j ≤ g.ofLp j := hg_lex v hv j h_agree
          have h_negv_le : (-v).ofLp j ≤ g.ofLp j :=
            hg_lex (-v) (h_sym v hv) j h_neg_agree
          rw [WithLp.ofLp_neg, hg_j] at h_negv_le
          rw [hg_j] at h_v_le
          have h_neg_apply : (-v.ofLp) j = -(v.ofLp j) := rfl
          rw [h_neg_apply] at h_negv_le
          linarith
    -- The constant zero function evaluated at `i`.
    change v.ofLp i = (0 : Fin n → ℝ) i
    have h_zero_i : (0 : Fin n → ℝ) i = 0 := rfl
    rw [h_zero_i]
    exact h_all (n + 1) i (Nat.lt_succ_of_lt i.isLt)
  · -- Backward: S = {0} ⟹ g = 0 (since g ∈ S).
    rw [hS_eq] at hg_mem
    exact hg_mem

/-- Joint-space lex-max selector for the multifunction `H_m(p) = {v : p.2 ± (1/(m+1))·v ∈ F p.1}`
over `p ∈ Y × ℝⁿ`.

Returns a measurable `g : Y × ℝⁿ → ℝⁿ` with `g p ∈ H_m(p)` whenever `H_m(p)` is non-empty (in
particular when `p.2 ∈ F p.1`), and the lex-max property `x.ofLp i ≤ (g p).ofLp i` whenever
`x ∈ H_m(p)` agrees with `g p` on the first `i-1` coords. -/
private lemma exists_lexMax_TmDir_joint
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (m : ℕ) :
    ∃ g : Y × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable g ∧
      (∀ p : Y × EuclideanSpace ℝ (Fin n), p.2 ∈ F p.1 →
        p.2 + (1 / ((m : ℝ) + 1)) • g p ∈ F p.1 ∧
        p.2 - (1 / ((m : ℝ) + 1)) • g p ∈ F p.1) ∧
      (∀ p : Y × EuclideanSpace ℝ (Fin n),
        ∀ v : EuclideanSpace ℝ (Fin n),
        p.2 + (1 / ((m : ℝ) + 1)) • v ∈ F p.1 →
        p.2 - (1 / ((m : ℝ) + 1)) • v ∈ F p.1 →
        ∀ i : Fin n,
          (∀ j : Fin n, j < i → v.ofLp j = (g p).ofLp j) →
          v.ofLp i ≤ (g p).ofLp i) := by
  -- Multifunction `H` over the joint base `Y × ℝⁿ`.
  set H : Y × EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun p => {v | p.2 + (1 / ((m : ℝ) + 1)) • v ∈ F p.1 ∧
                  p.2 - (1 / ((m : ℝ) + 1)) • v ∈ F p.1} with hH_def
  -- Closed graph in `(Y × ℝⁿ) × ℝⁿ`.
  have hH_graph_closed :
      IsClosed {q : (Y × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
        q.2 ∈ H q.1} := isClosed_graph_Tm hF_graph_closed m
  -- Compact bound: `H p ⊆ TmUniformBound m K`.
  have hH_sub : ∀ p : Y × EuclideanSpace ℝ (Fin n),
      H p ⊆ TmUniformBound m K := by
    intro p v hv
    obtain ⟨h_plus, h_minus⟩ := hv
    -- `v = ((m+1)/2) · [(p.2 + (1/(m+1))v) - (p.2 - (1/(m+1))v)]`.
    refine ⟨(p.2 + (1 / ((m : ℝ) + 1)) • v) - (p.2 - (1 / ((m : ℝ) + 1)) • v),
            ⟨_, hF_sub_K _ h_plus, _, hF_sub_K _ h_minus, rfl⟩, ?_⟩
    have hmp_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
    have h_simp :
        ((m : ℝ) + 1) / 2 *
          (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1)) = 1 := by
      field_simp; ring
    have h_smul :
        (((m : ℝ) + 1) / 2) •
          ((p.2 + (1 / ((m : ℝ) + 1)) • v) - (p.2 - (1 / ((m : ℝ) + 1)) • v))
          = (((m : ℝ) + 1) / 2 *
              (1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1))) • v := by
      rw [smul_sub, smul_add, smul_sub]
      module
    change (((m : ℝ) + 1) / 2) •
        ((p.2 + (1 / ((m : ℝ) + 1)) • v) - (p.2 - (1 / ((m : ℝ) + 1)) • v)) = v
    rw [h_smul, h_simp, one_smul]
  have hTm_compact : IsCompact (TmUniformBound m K) :=
    isCompact_TmUniformBound hK_compact m
  -- Apply `measurable_lexMax_aux` to the joint multifunction.
  obtain ⟨g, hg_meas, hg_mem, hg_lex⟩ :=
    measurable_lexMax_aux n hTm_compact hH_sub hH_graph_closed
  refine ⟨g, hg_meas, ?_, ?_⟩
  · -- When `p.2 ∈ F p.1`, `0 ∈ H p`, so `H p` non-empty.
    intro p hp_mem
    have h_zero_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ H p := by
      refine ⟨?_, ?_⟩
      · show p.2 + (1 / ((m : ℝ) + 1)) • (0 : EuclideanSpace ℝ (Fin n)) ∈ F p.1
        rw [smul_zero, add_zero]; exact hp_mem
      · show p.2 - (1 / ((m : ℝ) + 1)) • (0 : EuclideanSpace ℝ (Fin n)) ∈ F p.1
        rw [smul_zero, sub_zero]; exact hp_mem
    exact hg_mem p ⟨0, h_zero_mem⟩
  · -- Lex-max property.
    intro p v h_plus h_minus i h_agree
    exact hg_lex p v ⟨h_plus, h_minus⟩ i h_agree

/-- Measurable single descent direction at `z y`.

For closed-graph compact-bound convex `F` and measurable `z(y) ∈ F y`, there is a measurable
`d : Y → ℝⁿ` such that

* `∃ ε > 0, z y ± ε • d y ∈ F y` (so `d y ∈ T(y)` whenever `d y ≠ 0`);
* `z y ∉ extremePoints (F y) ⟹ d y ≠ 0`. -/
lemma exists_measurable_descent_direction
    {n : ℕ} {Y : Type*}
    [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (hF_convex : ∀ y, Convex ℝ (F y))
    {z : Y → EuclideanSpace ℝ (Fin n)}
    (hz_meas : Measurable z) (hz_mem : ∀ y, z y ∈ F y) :
    ∃ d : Y → EuclideanSpace ℝ (Fin n),
      Measurable d ∧
      (∀ y, ∃ ε > (0 : ℝ), z y + ε • d y ∈ F y ∧ z y - ε • d y ∈ F y) ∧
      (∀ y, z y ∉ Set.extremePoints ℝ (F y) → d y ≠ 0) := by
  classical
  choose g hg_meas hg_in hg_lex using
    (fun m : ℕ => exists_lexMax_TmDir_joint hK_compact hF_sub_K hF_graph_closed m)
  set ĝ : ℕ → Y → EuclideanSpace ℝ (Fin n) := fun m y => g m (y, z y) with hĝ_def
  have hĝ_meas : ∀ m, Measurable (ĝ m) := fun m =>
    (hg_meas m).comp (measurable_id.prodMk hz_meas)
  have hĝ_in : ∀ (m : ℕ) (y : Y),
      z y + (1 / ((m : ℝ) + 1)) • ĝ m y ∈ F y ∧
      z y - (1 / ((m : ℝ) + 1)) • ĝ m y ∈ F y :=
    fun m y => hg_in m (y, z y) (hz_mem y)
  set r : ℕ → Y → Prop :=
    fun m y => ĝ m y ≠ 0 ∨ (m = 0 ∧ ∀ k, ĝ k y = 0) with hr_def
  have hr_all : ∀ y, ∃ m, r m y := by
    intro y
    by_cases hy : ∃ m, ĝ m y ≠ 0
    · obtain ⟨m, hm⟩ := hy
      exact ⟨m, Or.inl hm⟩
    · refine ⟨0, Or.inr ⟨rfl, fun k => ?_⟩⟩
      by_contra hk; exact hy ⟨k, hk⟩
  -- Each `{y | r m y}` is measurable.
  have h_nonzero_meas : ∀ m, MeasurableSet {y : Y | ĝ m y ≠ 0} := by
    intro m
    have : MeasurableSet ((ĝ m) ⁻¹' ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ)) :=
      (hĝ_meas m) isClosed_singleton.measurableSet.compl
    convert this using 1
  have hr_meas : ∀ m, MeasurableSet {y : Y | r m y} := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have h_compl_A : MeasurableSet {y : Y | ∀ k, ĝ k y = 0} := by
        have h_eq : {y : Y | ∀ k, ĝ k y = 0} = ⋂ k, {y : Y | ĝ k y = 0} := by
          ext y; simp
        rw [h_eq]
        refine MeasurableSet.iInter fun k => ?_
        have : MeasurableSet ((ĝ k) ⁻¹' ({(0 : EuclideanSpace ℝ (Fin n))})) :=
          (hĝ_meas k) isClosed_singleton.measurableSet
        convert this using 1
      have h_eq :
          {y : Y | r 0 y} =
            {y : Y | ĝ 0 y ≠ 0} ∪ {y : Y | ∀ k, ĝ k y = 0} := by
        ext y; simp [r]
      rw [h_eq]
      exact (h_nonzero_meas 0).union h_compl_A
    · have h_eq : {y : Y | r m y} = {y : Y | ĝ m y ≠ 0} := by
        ext y; simp [r, hm]
      rw [h_eq]
      exact h_nonzero_meas m
  refine ⟨fun y => ĝ (Nat.find (hr_all y)) y, ?_, ?_, ?_⟩
  · -- Measurability via `Measurable.find`.
    exact Measurable.find hĝ_meas hr_meas hr_all
  · -- Existence of `ε > 0` with `z ± ε • d ∈ F`.
    intro y
    refine ⟨1 / ((Nat.find (hr_all y) : ℝ) + 1), by positivity, ?_, ?_⟩
    · exact (hĝ_in (Nat.find (hr_all y)) y).1
    · exact (hĝ_in (Nat.find (hr_all y)) y).2
  · -- `z y ∉ extremePoints (F y) ⟹ d y ≠ 0`.
    intro y h_not_ex
    -- Lemma: if `∀ m, ĝ m y = 0`, then `z y` is extreme.  Contrapositive
    -- gives `∃ m, ĝ m y ≠ 0`.
    have h_exists_nontrivial : ∃ m, ĝ m y ≠ 0 := by
      by_contra h_all_zero
      push Not at h_all_zero
      -- By `lexMax_eq_zero_iff_singleton` applied to `T_m^{dir}(y, z y)`:
      -- `T_m^{dir}(y, z y) = {0}` for all `m`.
      have h_Tm_singleton : ∀ m : ℕ,
          {v : EuclideanSpace ℝ (Fin n) |
              z y + (1 / ((m : ℝ) + 1)) • v ∈ F y ∧
              z y - (1 / ((m : ℝ) + 1)) • v ∈ F y} = {0} := by
        intro m
        set S : Set (EuclideanSpace ℝ (Fin n)) :=
          {v | z y + (1 / ((m : ℝ) + 1)) • v ∈ F y ∧
               z y - (1 / ((m : ℝ) + 1)) • v ∈ F y} with hS_def
        have h_zero_in_S : (0 : EuclideanSpace ℝ (Fin n)) ∈ S := by
          refine ⟨?_, ?_⟩
          · rw [smul_zero, add_zero]; exact hz_mem y
          · rw [smul_zero, sub_zero]; exact hz_mem y
        have h_sym : ∀ w ∈ S, -w ∈ S := by
          intro w hw
          obtain ⟨hw1, hw2⟩ := hw
          refine ⟨?_, ?_⟩
          · rw [smul_neg, ← sub_eq_add_neg]; exact hw2
          · rw [smul_neg, sub_neg_eq_add]; exact hw1
        have hg_mem_S : ĝ m y ∈ S := hĝ_in m y
        have hg_lex_S : ∀ x ∈ S, ∀ i : Fin n,
            (∀ j : Fin n, j < i → x.ofLp j = (ĝ m y).ofLp j) →
            x.ofLp i ≤ (ĝ m y).ofLp i := by
          intro x hx i h_agree
          obtain ⟨hx_plus, hx_minus⟩ := hx
          exact hg_lex m (y, z y) x hx_plus hx_minus i h_agree
        exact
          (lexMax_eq_zero_iff_singleton h_zero_in_S h_sym hg_mem_S hg_lex_S).mp
            (h_all_zero m)
      -- Show `z y` is extreme.  Mathlib's `extremePoints` characterization:
      -- the membership goal here is `a = z y` (single equation).
      apply h_not_ex
      refine ⟨hz_mem y, ?_⟩
      intro a ha b hb hab
      obtain ⟨α, β, hα_pos, hβ_pos, hsum, hcomb⟩ := hab
      have h_a_eq_b : a = b := by
        by_contra h_ne_ab
        set v : EuclideanSpace ℝ (Fin n) := a - b with hv_def
        have hv_ne : v ≠ 0 := sub_ne_zero.mpr h_ne_ab
        set ε : ℝ := min α β with hε_def
        have hε_pos : 0 < ε := lt_min hα_pos hβ_pos
        obtain ⟨m, hm_inv⟩ := exists_nat_one_div_lt hε_pos
        have h_le_α : (1 / ((m : ℝ) + 1)) ≤ α :=
          le_of_lt (hm_inv.trans_le (min_le_left _ _))
        have h_le_β : (1 / ((m : ℝ) + 1)) ≤ β :=
          le_of_lt (hm_inv.trans_le (min_le_right _ _))
        have h_inv_pos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        -- `z y + (1/(m+1)) v = (α + 1/(m+1)) a + (β - 1/(m+1)) b ∈ F y`.
        have h_plus : z y + (1 / ((m : ℝ) + 1)) • v ∈ F y := by
          have h_combo :
              z y + (1 / ((m : ℝ) + 1)) • v
                = (α + (1 / ((m : ℝ) + 1))) • a + (β - (1 / ((m : ℝ) + 1))) • b := by
            rw [hv_def, smul_sub, ← hcomb]
            module
          rw [h_combo]
          exact hF_convex y ha hb (by linarith) (by linarith) (by linarith)
        have h_minus : z y - (1 / ((m : ℝ) + 1)) • v ∈ F y := by
          have h_combo :
              z y - (1 / ((m : ℝ) + 1)) • v
                = (α - (1 / ((m : ℝ) + 1))) • a + (β + (1 / ((m : ℝ) + 1))) • b := by
            rw [hv_def, smul_sub, ← hcomb]
            module
          rw [h_combo]
          exact hF_convex y ha hb (by linarith) (by linarith) (by linarith)
        have hv_in : v ∈ ({v : EuclideanSpace ℝ (Fin n) |
            z y + (1 / ((m : ℝ) + 1)) • v ∈ F y ∧
            z y - (1 / ((m : ℝ) + 1)) • v ∈ F y}) := ⟨h_plus, h_minus⟩
        rw [h_Tm_singleton m] at hv_in
        exact hv_ne hv_in
      rw [h_a_eq_b] at hcomb
      have h_b_eq_zy : b = z y := by
        have h_sum_smul : (α + β) • b = z y := by rw [add_smul]; exact hcomb
        rwa [hsum, one_smul] at h_sum_smul
      exact h_a_eq_b.trans h_b_eq_zy
    -- Conclude `ĝ (Nat.find _) y ≠ 0`.
    have h_r_find : r (Nat.find (hr_all y)) y := Nat.find_spec (hr_all y)
    cases h_r_find with
    | inl h_nonzero => exact h_nonzero
    | inr h_all =>
      obtain ⟨_, h_all_zero_k⟩ := h_all
      obtain ⟨m₀, hm₀⟩ := h_exists_nontrivial
      exact absurd (h_all_zero_k m₀) hm₀

/-! ### Pointwise face-descent facts

At the *exit point* of a ray through `z` in a measurable descent direction `d`, the relative
tangent space loses at least one dimension.

* `relTangentSubmodule` — the relative tangent set is a submodule.
* `relTangentSubmodule_subset_of_exit` — `T(z') ⊆ T(z)`.
* `direction_notMem_relTangentSubmodule_at_exit` — `d ∉ T(z')`.
* `finrank_relTangentSubmodule_lt_at_exit` — strict drop in `finrank`. -/

/-- Helper: On a convex set `F` with `z ∈ F` and `z ± ε • v ∈ F`, the "line segment"
`{z + s • v : |s| ≤ ε}` lies in `F`. -/
lemma mem_F_of_abs_smul_le
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z v : EuclideanSpace ℝ (Fin n)} (hz : z ∈ F)
    {ε : ℝ} (hε : 0 < ε)
    (hv_plus : z + ε • v ∈ F) (hv_minus : z - ε • v ∈ F)
    {s : ℝ} (hs_le : |s| ≤ ε) :
    z + s • v ∈ F := by
  rcases le_or_gt 0 s with hs_nn | hs_neg
  · -- 0 ≤ s ≤ ε.  Use convex combo of `z` and `z + ε v`.
    have h_s_le_ε : s ≤ ε := (abs_of_nonneg hs_nn) ▸ hs_le
    have h_t : s / ε ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hs_nn hε.le, ?_⟩
      rw [div_le_one hε]; exact h_s_le_ε
    have h_apply : z + (s / ε) • (ε • v) ∈ F :=
      hF_convex.add_smul_mem hz hv_plus h_t
    have h_simp : (s / ε) • (ε • v) = s • v := by
      rw [smul_smul, div_mul_cancel₀ _ hε.ne']
    rwa [h_simp] at h_apply
  · -- -ε ≤ s < 0.  Use convex combo of `z` and `z - ε v`.
    have h_neg_s_pos : 0 < -s := neg_pos.mpr hs_neg
    have h_neg_s_le_ε : -s ≤ ε := (abs_of_neg hs_neg) ▸ hs_le
    have h_t : (-s) / ε ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg h_neg_s_pos.le hε.le, ?_⟩
      rw [div_le_one hε]; exact h_neg_s_le_ε
    have hv_minus' : z + (- (ε • v)) ∈ F := by
      rw [← sub_eq_add_neg]; exact hv_minus
    have h_apply : z + ((-s) / ε) • (- (ε • v)) ∈ F :=
      hF_convex.add_smul_mem hz hv_minus' h_t
    have h_simp : ((-s) / ε) • (- (ε • v)) = s • v := by
      rw [smul_neg, smul_smul, div_mul_cancel₀ _ hε.ne', neg_smul, neg_neg]
    rwa [h_simp] at h_apply

/-- **Relative tangent submodule** at `z ∈ F` for a convex set `F ⊆ ℝⁿ`.

Carrier: `{v | ∃ ε > 0, z ± ε • v ∈ F}`.  By convexity of `F`, this set is closed under scalar
multiplication and addition. -/
def relTangentSubmodule
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z : EuclideanSpace ℝ (Fin n)} (hz_in_F : z ∈ F) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {v | ∃ ε > (0 : ℝ), z + ε • v ∈ F ∧ z - ε • v ∈ F}
  zero_mem' := by
    refine ⟨1, one_pos, ?_, ?_⟩
    · simpa using hz_in_F
    · simpa using hz_in_F
  add_mem' := by
    intro v w ⟨εv, hεv_pos, hv_plus, hv_minus⟩ ⟨εw, hεw_pos, hw_plus, hw_minus⟩
    set δ : ℝ := min εv εw / 2 with hδ_def
    have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
    have h2δ_pos : 0 < 2 * δ := by positivity
    have h2δ_le_εv : 2 * δ ≤ εv := by
      rw [hδ_def, show (2 : ℝ) * (min εv εw / 2) = min εv εw from by ring]
      exact min_le_left _ _
    have h2δ_le_εw : 2 * δ ≤ εw := by
      rw [hδ_def, show (2 : ℝ) * (min εv εw / 2) = min εv εw from by ring]
      exact min_le_right _ _
    have h_zv_plus : z + (2 * δ) • v ∈ F :=
      mem_F_of_abs_smul_le hF_convex hz_in_F hεv_pos hv_plus hv_minus
        (by rw [abs_of_pos h2δ_pos]; exact h2δ_le_εv)
    have h_zv_minus : z - (2 * δ) • v ∈ F := by
      have h_eq : z - (2 * δ) • v = z + (-(2 * δ)) • v := by
        rw [neg_smul, ← sub_eq_add_neg]
      rw [h_eq]
      exact mem_F_of_abs_smul_le hF_convex hz_in_F hεv_pos hv_plus hv_minus
        (by rw [abs_neg, abs_of_pos h2δ_pos]; exact h2δ_le_εv)
    have h_zw_plus : z + (2 * δ) • w ∈ F :=
      mem_F_of_abs_smul_le hF_convex hz_in_F hεw_pos hw_plus hw_minus
        (by rw [abs_of_pos h2δ_pos]; exact h2δ_le_εw)
    have h_zw_minus : z - (2 * δ) • w ∈ F := by
      have h_eq : z - (2 * δ) • w = z + (-(2 * δ)) • w := by
        rw [neg_smul, ← sub_eq_add_neg]
      rw [h_eq]
      exact mem_F_of_abs_smul_le hF_convex hz_in_F hεw_pos hw_plus hw_minus
        (by rw [abs_neg, abs_of_pos h2δ_pos]; exact h2δ_le_εw)
    refine ⟨δ, hδ_pos, ?_, ?_⟩
    · -- z + δ • (v + w) = (1/2) • (z + 2δ • v) + (1/2) • (z + 2δ • w)
      have h_eq : z + δ • (v + w) =
          (1/2 : ℝ) • (z + (2 * δ) • v) + (1/2 : ℝ) • (z + (2 * δ) • w) := by
        module
      rw [h_eq]
      exact hF_convex h_zv_plus h_zw_plus (by norm_num) (by norm_num) (by norm_num)
    · -- z - δ • (v + w) = (1/2) • (z - 2δ • v) + (1/2) • (z - 2δ • w)
      have h_eq : z - δ • (v + w) =
          (1/2 : ℝ) • (z - (2 * δ) • v) + (1/2 : ℝ) • (z - (2 * δ) • w) := by
        module
      rw [h_eq]
      exact hF_convex h_zv_minus h_zw_minus (by norm_num) (by norm_num) (by norm_num)
  smul_mem' := by
    intro c v ⟨ε, hε_pos, hv_plus, hv_minus⟩
    -- Set ε' := ε / (1 + |c|) > 0 and reduce to `mem_F_of_abs_smul_le`.
    refine ⟨ε / (1 + |c|), by positivity, ?_, ?_⟩
    · -- z + (ε/(1+|c|)) • (c • v) ∈ F.
      -- Rewrite the smul: ε' • (c • v) = (ε' * c) • v.
      have h_eq : (ε / (1 + |c|)) • (c • v) = (ε / (1 + |c|) * c) • v := by
        rw [smul_smul]
      rw [h_eq]
      -- Bound |ε/(1+|c|) * c| ≤ ε.
      have h_abs_le : |ε / (1 + |c|) * c| ≤ ε := by
        rw [abs_mul, abs_div, abs_of_pos hε_pos, abs_of_pos (by positivity : (0:ℝ) < 1 + |c|)]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 1 + |c|)]
        have := abs_nonneg c
        nlinarith
      exact mem_F_of_abs_smul_le hF_convex hz_in_F hε_pos hv_plus hv_minus h_abs_le
    · -- z - (ε/(1+|c|)) • (c • v) ∈ F.
      have h_eq : -(ε / (1 + |c|)) • (c • v) = (-(ε / (1 + |c|) * c)) • v := by
        rw [neg_smul, smul_smul, ← neg_smul]
      have h_eq' : z - (ε / (1 + |c|)) • (c • v) = z + (-(ε / (1 + |c|) * c)) • v := by
        rw [sub_eq_add_neg, ← neg_smul]; rw [h_eq]
      rw [h_eq']
      have h_abs_le : |-(ε / (1 + |c|) * c)| ≤ ε := by
        rw [abs_neg, abs_mul, abs_div, abs_of_pos hε_pos,
          abs_of_pos (by positivity : (0:ℝ) < 1 + |c|)]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 1 + |c|)]
        have := abs_nonneg c
        nlinarith
      exact mem_F_of_abs_smul_le hF_convex hz_in_F hε_pos hv_plus hv_minus h_abs_le

/-- Bridge: `Submodule.span ℝ` of the relative tangent set equals the relative tangent submodule
(as `Submodule.span` of a submodule's carrier equals the submodule). -/
lemma span_relTangentSet_eq
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z : EuclideanSpace ℝ (Fin n)} (hz_in_F : z ∈ F) :
    Submodule.span ℝ {v : EuclideanSpace ℝ (Fin n) |
        ∃ ε > (0 : ℝ), z + ε • v ∈ F ∧ z - ε • v ∈ F}
      = relTangentSubmodule hF_convex hz_in_F :=
  Submodule.span_eq (relTangentSubmodule hF_convex hz_in_F)

/-- The relative tangent submodule at the exit point `z + r • d` is contained in the relative
tangent submodule at `z`.

For `r ≥ 0` (the case relevant to the ray-exit construction): Given a tangent direction `v` at
`z + r • d` with witness `ε > 0`, combine `z - ε₀ • d` and `(z + r • d) ± ε • v` with weights
`ν := r/(ε₀ + r)` and `1 - ν = ε₀/(ε₀ + r)`.  This convex combination cancels the `d` component and
yields `z ± δ • v ∈ F` with `δ := ε * ε₀/(ε₀ + r) > 0`. -/
lemma relTangentSubmodule_subset_of_exit
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z : EuclideanSpace ℝ (Fin n)} (hz_in_F : z ∈ F)
    {d : EuclideanSpace ℝ (Fin n)}
    {ε₀ : ℝ} (hε₀_pos : 0 < ε₀)
    (hd_minus : z - ε₀ • d ∈ F)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_in_F : z + r • d ∈ F) :
    relTangentSubmodule hF_convex hr_in_F
      ≤ relTangentSubmodule hF_convex hz_in_F := by
  intro v hv
  obtain ⟨ε, hε_pos, hv_plus_z', hv_minus_z'⟩ := hv
  set ν : ℝ := r / (ε₀ + r) with hν_def
  have h_denom_pos : 0 < ε₀ + r := by linarith
  have h_denom_ne : (ε₀ + r) ≠ 0 := h_denom_pos.ne'
  have hν_nn : 0 ≤ ν := by rw [hν_def]; positivity
  have hν_le_one : ν ≤ 1 := by
    rw [hν_def, div_le_one h_denom_pos]; linarith
  have h_one_sub_ν_nn : 0 ≤ 1 - ν := by linarith
  set δ : ℝ := ε * ε₀ / (ε₀ + r) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  refine ⟨δ, hδ_pos, ?_, ?_⟩
  · -- z + δ • v = ν • (z - ε₀ • d) + (1 - ν) • ((z + r • d) + ε • v).
    have h_combo :
        z + δ • v = ν • (z - ε₀ • d) + (1 - ν) • ((z + r • d) + ε • v) := by
      rw [hδ_def, hν_def]
      match_scalars <;> field_simp <;> ring
    rw [h_combo]
    exact hF_convex hd_minus hv_plus_z' hν_nn h_one_sub_ν_nn (by ring)
  · -- z - δ • v = ν • (z - ε₀ • d) + (1 - ν) • ((z + r • d) - ε • v).
    have h_combo :
        z - δ • v = ν • (z - ε₀ • d) + (1 - ν) • ((z + r • d) - ε • v) := by
      rw [hδ_def, hν_def]
      match_scalars <;> field_simp <;> ring
    rw [h_combo]
    exact hF_convex hd_minus hv_minus_z' hν_nn h_one_sub_ν_nn (by ring)

/-- The descent direction `d` does not lie in the relative tangent submodule at the exit point
`z + r • d`.

Direct from maximality: Any `ε > 0` with `(z + r • d) + ε • d ∈ F` yields `z + (r + ε) • d ∈ F`
with `r + ε > r`, contradicting maximality of `r`. -/
lemma direction_notMem_relTangentSubmodule_at_exit
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z : EuclideanSpace ℝ (Fin n)}
    {d : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr_in_F : z + r • d ∈ F)
    (hr_max : ∀ t : ℝ, z + t • d ∈ F → t ≤ r) :
    d ∉ relTangentSubmodule hF_convex hr_in_F := by
  intro h_mem
  obtain ⟨ε, hε_pos, hd_plus_at_z', _⟩ := h_mem
  -- Rewrite `(z + r • d) + ε • d = z + (r + ε) • d`.
  have h_eq : (z + r • d) + ε • d = z + (r + ε) • d := by module
  rw [h_eq] at hd_plus_at_z'
  have h_le : r + ε ≤ r := hr_max (r + ε) hd_plus_at_z'
  linarith

/-- **Pointwise dim drop** along a descent direction in `T(z)`.

If `d ∈ T(z)` is a nonzero direction with `z ± ε₀ • d ∈ F` and `r` is the maximum ray length, then
`T(z + r • d) ⊊ T(z)` strictly, so `finrank` drops. -/
lemma finrank_relTangentSubmodule_lt_at_exit
    {n : ℕ} {F : Set (EuclideanSpace ℝ (Fin n))} (hF_convex : Convex ℝ F)
    {z : EuclideanSpace ℝ (Fin n)} (hz_in_F : z ∈ F)
    {d : EuclideanSpace ℝ (Fin n)}
    {ε₀ : ℝ} (hε₀_pos : 0 < ε₀)
    (hd_plus : z + ε₀ • d ∈ F) (hd_minus : z - ε₀ • d ∈ F)
    {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_in_F : z + r • d ∈ F)
    (hr_max : ∀ t : ℝ, z + t • d ∈ F → t ≤ r) :
    Module.finrank ℝ (relTangentSubmodule hF_convex hr_in_F)
      < Module.finrank ℝ (relTangentSubmodule hF_convex hz_in_F) := by
  have h_le : relTangentSubmodule hF_convex hr_in_F
                ≤ relTangentSubmodule hF_convex hz_in_F :=
    relTangentSubmodule_subset_of_exit hF_convex hz_in_F hε₀_pos hd_minus hr_nonneg hr_in_F
  have h_d_in_Tz : d ∈ relTangentSubmodule hF_convex hz_in_F :=
    ⟨ε₀, hε₀_pos, hd_plus, hd_minus⟩
  have h_d_notin_Tz' : d ∉ relTangentSubmodule hF_convex hr_in_F :=
    direction_notMem_relTangentSubmodule_at_exit hF_convex hr_in_F hr_max
  have h_lt : relTangentSubmodule hF_convex hr_in_F
                < relTangentSubmodule hF_convex hz_in_F := by
    refine lt_of_le_of_ne h_le ?_
    intro h_eq
    apply h_d_notin_Tz'
    rw [h_eq]
    exact h_d_in_Tz
  exact Submodule.finrank_lt_finrank_of_lt h_lt
