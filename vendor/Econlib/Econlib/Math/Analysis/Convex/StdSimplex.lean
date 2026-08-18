/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Vertex evaluation, transport, and trembles on the standard simplex

Extensions to Mathlib's `stdSimplex ℝ α`: An `Inhabited` instance selecting the default vertex,
elementary vertex-evaluation lemmas, coordinatewise transport across heterogeneously equal simplex
elements, and the barycentric **tremble** perturbation `(1 - ε) • p + ε • uniform` together with
its positivity and coordinatewise-convergence lemmas.

## Main definitions

* `stdSimplex.instInhabited` — picks the vertex of the default index as the default point.
* `stdSimplex.tremble` — the barycentric perturbation `(1 - ε) • p + ε • uniform`.

## Main statements

* `stdSimplex.vertex_apply_self`, `vertex_apply_eq`, `vertex_apply_ne` — vertex evaluation.
* `stdSimplex.heq_val` — coordinatewise evaluation transports across `HEq` simplex elements.
* `stdSimplex.tremble_val_pos` — for `0 < ε` the tremble is totally mixed.
* `stdSimplex.tremble_val_tendsto` — the tremble converges coordinatewise to `p` as `ε → 0`.

## Tags

standard simplex, vertex, convex, tremble, totally mixed
-/

@[expose] public section

/-- The `Inhabited` data instance for `stdSimplex ℝ α`, picking the vertex at `default`. -/
noncomputable instance stdSimplex.instInhabited {α : Type*} [Fintype α] [DecidableEq α]
    [Inhabited α] : Inhabited (stdSimplex ℝ α) := ⟨stdSimplex.vertex default⟩

/-- A vertex evaluates to `1` at its own index. -/
@[simp] lemma stdSimplex.vertex_apply_self {α : Type*} [Fintype α] [DecidableEq α] (i : α) :
    (stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ α) i = 1 := by
  rw [stdSimplex.vertex_coe, Pi.single_apply, if_pos rfl]

/-- A vertex evaluates to `1` at any index equal to its own. -/
@[simp] lemma stdSimplex.vertex_apply_eq {α : Type*} [Fintype α] [DecidableEq α] {i j : α}
    (h : i = j) :
    (stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ α) j = 1 := by
  subst h; exact stdSimplex.vertex_apply_self i

/-- A vertex evaluates to `0` away from its index. -/
@[simp] lemma stdSimplex.vertex_apply_ne {α : Type*} [Fintype α] [DecidableEq α] {i j : α}
    (h : i ≠ j) :
    (stdSimplex.vertex (S := ℝ) i : stdSimplex ℝ α) j = 0 := by
  rw [stdSimplex.vertex_coe, Pi.single_apply, if_neg (Ne.symm h)]

/-- A vertex-weighted sum collapses to the function value at the vertex's index: The simplex point
`stdSimplex.vertex a` puts unit mass on `a`. -/
lemma stdSimplex.vertex_sum_mul {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f : α → ℝ) :
    ∑ b, (stdSimplex.vertex a : stdSimplex ℝ α) b * f b = f a := by
  simp [stdSimplex.vertex, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]

/-- If `α = β` and `s : stdSimplex ℝ α` is heterogeneously equal to `t : stdSimplex ℝ β`, then
`s.val c = t.val (heq ▸ c)` for every `c : α`. -/
theorem stdSimplex.heq_val {α β : Type u} [instA : Fintype α] [instB : Fintype β]
    (heq : α = β) (s : stdSimplex ℝ α) (t : stdSimplex ℝ β) (hst : HEq s t) (c : α) :
    s.val c = t.val (heq ▸ c) := by
  subst heq
  obtain rfl : instA = instB := Subsingleton.elim _ _
  obtain rfl : s = t := eq_of_heq hst
  rfl

/-- The subtype of simplex points transports across equality of index types. The explicit lemma
keeps dependent congruence proofs from unfolding `stdSimplex` into heterogeneous `Set` equalities
before the index type has been aligned. -/
theorem stdSimplex.coeSort_eq {α β : Type u} [instA : Fintype α] [instB : Fintype β]
    (heq : α = β) : ↥(stdSimplex ℝ α) = ↥(stdSimplex ℝ β) := by
  subst heq
  obtain rfl : instA = instB := Subsingleton.elim _ _
  rfl

/-- Two simplex-value applications over equal index types agree when the simplices and the
arguments are heterogeneously equal. -/
theorem stdSimplex.val_congr_heq {T₁ T₂ : Type u} [instA : Fintype T₁] [instB : Fintype T₂]
    (hT : T₁ = T₂) (s₁ : stdSimplex ℝ T₁) (s₂ : stdSimplex ℝ T₂) (a₁ : T₁) (a₂ : T₂)
    (hs : HEq s₁ s₂) (ha : HEq a₁ a₂) : s₁.val a₁ = s₂.val a₂ := by
  subst hT
  obtain rfl : instA = instB := Subsingleton.elim _ _
  obtain rfl : s₁ = s₂ := eq_of_heq hs
  obtain rfl : a₁ = a₂ := eq_of_heq ha
  rfl

/-! ## Trembles: Barycentric perturbation toward the uniform point -/

/-- The **tremble** of a simplex point `p` at rate `ε`: The convex combination
`(1 - ε) • p + ε • uniform`, where `uniform` is the barycenter of the simplex. -/
noncomputable def stdSimplex.tremble {α : Type*} [Fintype α] [Nonempty α] (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (p : stdSimplex ℝ α) : stdSimplex ℝ α :=
  ⟨fun c => (1 - ε) * p.val c + ε * (Fintype.card α : ℝ)⁻¹,
    fun c => add_nonneg (mul_nonneg (by linarith) (p.2.1 c))
      (mul_nonneg hε0 (by positivity)),
    by
      have hsum : ∑ c, p.val c = 1 := p.2.2
      have hcard : (Fintype.card α : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_pos.ne'
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      field_simp
      ring⟩

/-- Coordinate evaluation of a tremble. -/
@[simp] lemma stdSimplex.tremble_val {α : Type*} [Fintype α] [Nonempty α] (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (p : stdSimplex ℝ α) (c : α) :
    (stdSimplex.tremble ε hε0 hε1 p).val c = (1 - ε) * p.val c + ε * (Fintype.card α : ℝ)⁻¹ :=
  rfl

/-- For a strictly positive tremble rate, every coordinate of the tremble is strictly positive —
the tremble is totally mixed. -/
lemma stdSimplex.tremble_val_pos {α : Type*} [Fintype α] [Nonempty α] {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (p : stdSimplex ℝ α) (c : α) :
    0 < (stdSimplex.tremble ε hε.le hε1 p).val c := by
  have hp : 0 ≤ p.val c := p.2.1 c
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have h1ε : (0 : ℝ) ≤ 1 - ε := by linarith
  calc (0 : ℝ) < ε * (Fintype.card α : ℝ)⁻¹ := mul_pos hε hcard
    _ ≤ (1 - ε) * p.val c + ε * (Fintype.card α : ℝ)⁻¹ := by nlinarith

/-- As the tremble rate tends to `0`, the tremble converges coordinatewise back to the original
simplex point. -/
lemma stdSimplex.tremble_val_tendsto {α : Type*} [Fintype α] [Nonempty α] {ε : ℕ → ℝ}
    (hε0 : ∀ n, 0 ≤ ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) (p : stdSimplex ℝ α) (c : α) :
    Filter.Tendsto (fun n => (stdSimplex.tremble (ε n) (hε0 n) (hε1 n) p).val c)
      Filter.atTop (nhds (p.val c)) := by
  simp only [stdSimplex.tremble_val]
  have hlim' : Filter.Tendsto
      (fun n => (1 - ε n) * p.val c + ε n * (Fintype.card α : ℝ)⁻¹) Filter.atTop
      (nhds ((1 - 0) * p.val c + 0 * (Fintype.card α : ℝ)⁻¹)) :=
    (((tendsto_const_nhds.sub hlim).mul tendsto_const_nhds).add (hlim.mul tendsto_const_nhds))
  simpa using hlim'
