/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Unconstrained Optimization Foundations

Argmax existence and structure for continuous functions on compact sets, together with the
topology-free value function.

## Main definitions

* `valueFunction`: Supremum of `f` over a set `S`.
* `argmax`: The set of maximizers of `f` over `S`.

## Main statements

* `argmax_nonempty`: A continuous function on a nonempty compact set attains its maximum.
* `argmax_compact`: The argmax set of a continuous function on a compact set is compact.
* `valueFunction_eq_of_mem_argmax`: The value function equals `f` at any maximizer.
* `argmax_convex`: The argmax set of a quasiconcave function is convex.
* `image_val_argmax_univ`: Transport of `argmax` between a subtype and its ambient set.

## Tags

optimization, argmax, value function, compact, continuous
-/

@[expose] public section

namespace Econlib.Optimization

/-- The value function: Supremum of `f` over `S`. -/
noncomputable def valueFunction {X : Type*} (f : X → ℝ) (S : Set X) : ℝ :=
  sSup (f '' S)

/-- **Value evaluation from a greatest image element.** If `v` is the greatest element of the image
`f '' S`, then the value function equals `v`. -/
lemma valueFunction_eq_of_isGreatest {X : Type*} {f : X → ℝ} {S : Set X} {v : ℝ}
    (hv : IsGreatest (f '' S) v) :
    valueFunction f S = v :=
  hv.csSup_eq

/-- **Value evaluation at an attained maximizer.** If `x ∈ S` maximizes `f` over `S`, then
`valueFunction f S = f x`. The attained form of `valueFunction_eq_of_isGreatest`. -/
lemma valueFunction_eq_of_mem_isMaxOn {X : Type*} {f : X → ℝ} {S : Set X} {x : X}
    (hx_mem : x ∈ S) (hx_max : IsMaxOn f S x) :
    valueFunction f S = f x := by
  refine valueFunction_eq_of_isGreatest ⟨⟨x, hx_mem, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hx_max hz

section Generic

variable {X : Type*} [TopologicalSpace X]

/-- The set of maximizers of `f` over `S`. -/
def argmax (f : X → ℝ) (S : Set X) : Set X :=
  {x ∈ S | IsMaxOn f S x}

/-- Argmax existence: A continuous function on a nonempty compact set attains its maximum. -/
lemma argmax_nonempty {f : X → ℝ} {S : Set X}
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ContinuousOn f S) :
    (argmax f S).Nonempty :=
  h_compact.exists_isMaxOn h_nonempty h_cont

/-- The argmax of a continuous function on a compact set is itself compact. -/
lemma argmax_compact {f : X → ℝ} {S : Set X}
    (h_compact : IsCompact S)
    (h_cont : ContinuousOn f S) :
    IsCompact (argmax f S) := by
  have hfS : Continuous (S.restrict f) := h_cont.restrict
  set A := {p : S | ∀ q : S, S.restrict f q ≤ S.restrict f p} with hA_def
  have hA : IsClosed A := by
    simp_rw [hA_def, Set.setOf_forall]
    exact isClosed_iInter fun q => isClosed_le continuous_const hfS
  have hAcompact : IsCompact A := by
    have hSuniv : IsCompact (Set.univ : Set S) := by
      rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype]
    exact hSuniv.of_isClosed_subset hA (Set.subset_univ _)
  suffices h : argmax f S = Subtype.val '' A by
    rw [h]; exact hAcompact.image continuous_subtype_val
  ext x; simp only [hA_def, argmax, Set.mem_image, Set.mem_setOf_eq, Set.restrict]
  constructor
  · rintro ⟨hx, hmax⟩; exact ⟨⟨x, hx⟩, fun q => hmax q.2, rfl⟩
  · rintro ⟨⟨y, hy⟩, hmax, rfl⟩; exact ⟨hy, fun z hz => hmax ⟨z, hz⟩⟩

/-- On a nonempty compact set, the value function equals `f` evaluated at any maximizer. -/
lemma valueFunction_eq_of_mem_argmax {f : X → ℝ} {S : Set X} {x : X}
    (h_compact : IsCompact S)
    (h_nonempty : S.Nonempty)
    (h_cont : ContinuousOn f S)
    (hx : x ∈ argmax f S) :
    f x = valueFunction f S := by
  unfold valueFunction
  apply le_antisymm
  · exact le_csSup (h_compact.image_of_continuousOn h_cont).bddAbove ⟨x, hx.1, rfl⟩
  · exact csSup_le (h_nonempty.image f) (fun _ ⟨y, hy, hfy⟩ => hfy ▸ hx.2 hy)

omit [TopologicalSpace X] in
/-- Transport `argmax` between the subtype `↑S` (with trivial constraint set `Set.univ`) and the
ambient set `S`: If `f` agrees with `g` on `S`, the image of the subtype-level argmax under the
inclusion is the ambient argmax. -/
lemma image_val_argmax_univ {S : Set X} {g : ↑S → ℝ} {f : X → ℝ}
    (h : ∀ z : ↑S, g z = f z.1) :
    Subtype.val '' argmax g Set.univ = argmax f S := by
  ext v
  constructor
  · rintro ⟨w, ⟨-, hw_max⟩, rfl⟩
    exact ⟨w.2, fun z hz => by simpa only [h] using hw_max (Set.mem_univ (⟨z, hz⟩ : ↑S))⟩
  · rintro ⟨hv, hv_max⟩
    exact ⟨⟨v, hv⟩, ⟨Set.mem_univ _, fun z _ => by simpa only [h] using hv_max z.2⟩, rfl⟩

end Generic

section Convexity

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- The argmax set of a quasiconcave function is convex. No attainment or topology is needed. -/
lemma argmax_convex {f : E → ℝ} {S : Set E} (hf : QuasiconcaveOn 𝕜 S f) :
    Convex 𝕜 (argmax f S) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hf.convex hx.1 hy.1 ha hb hab, fun z hz => ?_⟩
  -- The superlevel set at `f z` is convex and contains both maximizers.
  exact (hf (f z) ⟨hx.1, hx.2 hz⟩ ⟨hy.1, hy.2 hz⟩ ha hb hab).2

end Convexity

section StrictConcave

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- **Single-valued argmax from strict concavity.** A strictly concave objective on a (convex) set
has at most one maximizer: `argmax f S` is a subsingleton. -/
lemma argmax_subsingleton_of_strictConcaveOn {f : E → ℝ} {S : Set E}
    (hf : StrictConcaveOn ℝ S f) :
    (argmax f S).Subsingleton :=
  fun _ ⟨hx_mem, hx_max⟩ _ ⟨hy_mem, hy_max⟩ =>
    hf.eq_of_isMaxOn hx_max hy_max hx_mem hy_mem

/-- **Singleton argmax from strict concavity plus an exhibited maximizer.** If `f` is strictly
concave on `S` and `x ∈ S` maximizes `f` over `S`, then `x` is the unique maximizer:
`argmax f S = {x}`. -/
lemma argmax_eq_singleton {f : E → ℝ} {S : Set E} {x : E}
    (hf : StrictConcaveOn ℝ S f) (hx_mem : x ∈ S) (hx_max : IsMaxOn f S x) :
    argmax f S = {x} := by
  have hx_argmax : x ∈ argmax f S := ⟨hx_mem, hx_max⟩
  exact (argmax_subsingleton_of_strictConcaveOn hf).eq_singleton_of_mem hx_argmax

end StrictConcave

end Econlib.Optimization
