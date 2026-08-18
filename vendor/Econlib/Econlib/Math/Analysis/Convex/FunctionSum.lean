/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Convex.Function

/-!
# Convexity and concavity of finite sums

A finite sum of convex (concave) functions is convex (concave), in both the unapplied
(`∑ i ∈ t, f i`) and applied (`fun x => ∑ i ∈ t, f i x`) forms. These are the `Finset`-indexed
closures of Mathlib's binary `ConvexOn.add`.

## Main statements

* `ConvexOn.sum`, `ConvexOn.fun_sum` — finite sums of convex functions are convex.
* `ConcaveOn.sum`, `ConcaveOn.fun_sum` — finite sums of concave functions are concave.

## Tags

convex function, concave function, finite sum
-/

@[expose] public section

variable {𝕜 E β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid β]
  [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {t : Finset ι}
  {f : ι → E → β}

theorem ConvexOn.sum (hs : Convex 𝕜 s) (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) :
    ConvexOn 𝕜 s (∑ i ∈ t, f i) := by
  induction t using Finset.cons_induction with
  | empty => simpa only [Finset.sum_empty] using convexOn_const (0 : β) hs
  | cons a t hat ih =>
    rw [Finset.sum_cons]
    exact (hf a (Finset.mem_cons_self a t)).add (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

theorem ConcaveOn.sum (hs : Convex 𝕜 s) (hf : ∀ i ∈ t, ConcaveOn 𝕜 s (f i)) :
    ConcaveOn 𝕜 s (∑ i ∈ t, f i) :=
  ConvexOn.sum (β := βᵒᵈ) hs hf

theorem ConvexOn.fun_sum (hs : Convex 𝕜 s) (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) :
    ConvexOn 𝕜 s fun x => ∑ i ∈ t, f i x :=
  Finset.sum_fn t f ▸ ConvexOn.sum hs hf

theorem ConcaveOn.fun_sum (hs : Convex 𝕜 s) (hf : ∀ i ∈ t, ConcaveOn 𝕜 s (f i)) :
    ConcaveOn 𝕜 s fun x => ∑ i ∈ t, f i x :=
  Finset.sum_fn t f ▸ ConcaveOn.sum hs hf
