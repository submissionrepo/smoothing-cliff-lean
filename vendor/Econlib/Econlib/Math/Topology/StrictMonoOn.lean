/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Images and inverses of strictly monotone functions on `ℝ`

A continuous, strictly monotone function on an open subset of `ℝ` is an open map onto its image,
and its (set-restricted) inverse is continuous at each point of the image. These are the
open-mapping and continuous-inverse facts underlying Debreu's utility representation theorem.

## Main results

* `StrictMonoOn.isOpen_image` — the image of an open set under a continuous, strictly monotone map.
* `StrictMonoOn.continuousAt_invFunOn` — continuity of the inverse on the image.
-/

@[expose] public section

open Set Filter Topology

/-- A continuous, strictly monotone function on an open subset of `ℝ` has an open image. -/
lemma StrictMonoOn.isOpen_image
    {s : Set ℝ} (hs : IsOpen s) {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g s) (hg_mono : StrictMonoOn g s) :
    IsOpen (g '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  rw [Metric.isOpen_iff] at hs
  obtain ⟨ε, hε, hball⟩ := hs x hx
  set a := x - ε / 2
  set b := x + ε / 2
  have hab : a < b := by simp [a, b]; linarith
  have haxb : x ∈ Set.Ioo a b := by
    simp only [Set.mem_Ioo, a, b]; constructor <;> linarith
  have hIcc_sub : Set.Icc a b ⊆ s := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [a, b, Set.mem_Icc] at hz
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hIoo_sub : Set.Ioo a b ⊆ s := Set.Ioo_subset_Icc_self.trans hIcc_sub
  have hg_cont' : ContinuousOn g (Set.Icc a b) := hg_cont.mono hIcc_sub
  have hg_mono' : StrictMonoOn g (Set.Icc a b) := hg_mono.mono hIcc_sub
  have h_image : g '' Set.Ioo a b = Set.Ioo (g a) (g b) := by
    apply Set.Subset.antisymm
    · exact hg_mono'.image_Ioo_subset
    · exact intermediate_value_Ioo hab.le hg_cont'
  have hgx : g x ∈ Set.Ioo (g a) (g b) := by
    constructor
    · exact hg_mono (hIcc_sub (Set.left_mem_Icc.mpr hab.le)) hx haxb.1
    · exact hg_mono hx (hIcc_sub (Set.right_mem_Icc.mpr hab.le)) haxb.2
  have h_sub : Set.Ioo (g a) (g b) ⊆ g '' s := by
    rw [← h_image]
    exact Set.image_mono hIoo_sub
  exact mem_nhds_iff.mpr ⟨Set.Ioo (g a) (g b), h_sub, isOpen_Ioo, hgx⟩

/-- The inverse of a continuous, strictly monotone function on an open subset of `ℝ` is continuous
at each point of the image. -/
lemma StrictMonoOn.continuousAt_invFunOn {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hf_cont : ContinuousOn f s) (hf_mono : StrictMonoOn f s)
    {y : ℝ} (hy : y ∈ f '' s) :
    ContinuousAt (Function.invFunOn f s) y := by
  have hinj := hf_mono.injOn
  rw [ContinuousAt, Filter.Tendsto, Filter.le_def]
  intro V hV
  rw [Filter.mem_map]
  obtain ⟨U, hUV, hU_open, hx_mem⟩ := mem_nhds_iff.mp hV
  set W := U ∩ s
  have hW_open : IsOpen W := hU_open.inter hs
  have hx_in_W : Function.invFunOn f s y ∈ W :=
    ⟨hx_mem, Function.invFunOn_mem hy⟩
  have hfW_open : IsOpen (f '' W) :=
    StrictMonoOn.isOpen_image hW_open
      (hf_cont.mono Set.inter_subset_right) (hf_mono.mono Set.inter_subset_right)
  have hy_in_fW : y ∈ f '' W :=
    ⟨Function.invFunOn f s y, hx_in_W, Function.invFunOn_eq hy⟩
  apply mem_nhds_iff.mpr
  refine ⟨f '' W, ?_, hfW_open, hy_in_fW⟩
  rintro z ⟨w, ⟨hw_U, hw_s⟩, rfl⟩
  change Function.invFunOn f s (f w) ∈ V
  have h_eq : Function.invFunOn f s (f w) = w :=
    hinj (Function.invFunOn_mem ⟨w, hw_s, rfl⟩) hw_s (Function.invFunOn_eq ⟨w, hw_s, rfl⟩)
  rw [h_eq]; exact hUV hw_U
