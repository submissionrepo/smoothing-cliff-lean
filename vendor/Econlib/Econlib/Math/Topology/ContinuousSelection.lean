/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Continuous selection from a single-valued upper-hemicontinuous correspondence

Berge's maximum theorem outputs the `argmax` as an `UpperHemicontinuous` correspondence
`Φ : X → Set Y`, never as a function, so even when the maximizer is unique (e.g. under strict
concavity) the conclusion is set-valued. This file shows that when the correspondence is
single-valued (each `Φ x` a nonempty subsingleton), its unique selection is a continuous function.

A strictly concave dynamic-programing problem has a unique optimal policy. Berge gives upper
hemicontinuity of the policy correspondence, which this result upgrades to a continuous policy
function.

## Main statements

* `UpperHemicontinuous.exists_continuous_selection` — a nonempty, subsingleton-valued upper-
  hemicontinuous correspondence admits a continuous selection.

## Tags

continuous selection, upper hemicontinuous, correspondence, policy function
-/

@[expose] public section

open Set Filter Topology

/-- **Continuous selection from a single-valued upper-hemicontinuous correspondence.** If
`Φ : X → Set Y` is upper hemicontinuous and each value `Φ x` is a nonempty subsingleton (a single
point), then the map sending `x` to that point is continuous and selects from `Φ`.

This bridges Berge's set-valued `argmax` output to a continuous policy function under a uniqueness
hypothesis (e.g. strict concavity of the objective). No compactness or separation hypothesis is
required. -/
theorem UpperHemicontinuous.exists_continuous_selection {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Φ : X → Set Y} (huhc : UpperHemicontinuous Φ)
    (hne : ∀ x, (Φ x).Nonempty) (hsub : ∀ x, (Φ x).Subsingleton) :
    ∃ g : X → Y, Continuous g ∧ ∀ x, g x ∈ Φ x := by
  -- The selection picks the unique element of each fiber.
  refine ⟨fun x => (hne x).choose, ?_, fun x => (hne x).choose_spec⟩
  set g : X → Y := fun x => (hne x).choose with hg
  have hg_mem : ∀ x, g x ∈ Φ x := fun x => (hne x).choose_spec
  -- Single-valuedness: each fiber is the singleton at its selected point.
  have hfx : ∀ x, Φ x = {g x} := fun x =>
    eq_singleton_iff_unique_mem.mpr ⟨hg_mem x, fun y hy => hsub x hy (hg_mem x)⟩
  -- Continuity via open preimages: `g ⁻¹' u` is the upper inverse `{x | Φ x ⊆ u}`, which UHC keeps
  -- open for every open `u`.
  rw [continuous_def]
  intro u hu
  have hpre : g ⁻¹' u = Φ ⁻¹' (Iic u) := by
    ext x
    simp only [mem_preimage, mem_Iic, le_eq_subset, hfx x, singleton_subset_iff]
  rw [hpre]
  exact (upperHemicontinuous_iff_isOpen_preimage_Iic.mp huhc) u hu
