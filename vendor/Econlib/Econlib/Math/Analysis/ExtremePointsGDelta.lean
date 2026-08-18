/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Extreme points of a compact convex set are Gδ

For a compact convex set `K` in a real normed space `E`, the set of extreme points
`Set.extremePoints ℝ K` is a Gδ set, and therefore Borel measurable.

## Main definitions

* `mid` — the convex midpoint `(1/2) • (x + y)`, written without the `Invertible 2` ceremony of
  `midpoint`.
* `nonExtremeAtScale` — the set of midpoints of two points of `K` separated by at least `1/(n+1)`.

## Main statements

* `isGδ_extremePoints_of_compact_convex` — extreme points form a Gδ set.
* `measurableSet_extremePoints_of_compact_convex` — extreme points form a Borel-measurable set.

## Notes

Mathlib provides the closure version of the Krein–Milman theorem in
`Mathlib.Analysis.Convex.KreinMilman` but not the Gδ statement; this file supplies it.

## Tags

extreme point, gδ, borel measurable, compact convex, krein–milman
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convex midpoint, written without the `Invertible 2` ceremony of `midpoint`.  In a real vector
space `mid x y = (1/2) • (x + y)`. -/
noncomputable def mid (x y : E) : E := (1 / 2 : ℝ) • (x + y)

/-- The midpoint map `(x, y) ↦ mid x y` is continuous. -/
lemma mid_continuous : Continuous (fun p : E × E => mid p.1 p.2) := by
  unfold mid
  exact continuous_const.smul (continuous_fst.add continuous_snd)

/-- The midpoint of two points of a convex set lies in the set. -/
lemma mid_mem_of_convex {K : Set E} (hK : Convex ℝ K) {y z : E}
    (hy : y ∈ K) (hz : z ∈ K) : mid y z ∈ K := by
  unfold mid
  -- (1/2) • (y + z) = (1/2) • y + (1/2) • z; use convexity with a = b = 1/2.
  rw [smul_add]
  exact hK hy hz (by norm_num) (by norm_num) (by norm_num)

/-- The midpoint of two distinct points lies in their open segment. -/
-- `hyz` is unused in the proof (the construction works even for `y = z`) but is kept so the
-- statement matches the mathematical meaning of "midpoint of two distinct points" at call sites.
lemma mid_mem_openSegment {y z : E} (_hyz : y ≠ z) :
    mid y z ∈ openSegment ℝ y z := by
  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold mid
  rw [smul_add]

/-- The set of points that are midpoints (in the sense of `mid`) of two points of `K` separated by
at least `1/(n+1)`. -/
def nonExtremeAtScale (K : Set E) (n : ℕ) : Set E :=
  (fun p : E × E => mid p.1 p.2) ''
    {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖}

/-- For compact `K`, the set `nonExtremeAtScale K n` is closed, being the continuous image of a
compact set. -/
lemma isClosed_nonExtremeAtScale {K : Set E} (hK : IsCompact K) (n : ℕ) :
    IsClosed (nonExtremeAtScale K n) := by
  -- nonExtremeAtScale K n is the image of the compact set
  --   {p ∈ K ×ˢ K | 1/(n+1) ≤ ‖p.1 - p.2‖}
  -- under the continuous midpoint map.
  have h_subset_cl :
      IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖} := by
    have h1 : IsClosed {p : E × E | p.1 ∈ K} :=
      hK.isClosed.preimage continuous_fst
    have h2 : IsClosed {p : E × E | p.2 ∈ K} :=
      hK.isClosed.preimage continuous_snd
    have h3 : IsClosed {p : E × E | (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖} := by
      have h_cont : Continuous (fun p : E × E => ‖p.1 - p.2‖) :=
        (continuous_fst.sub continuous_snd).norm
      exact isClosed_le continuous_const h_cont
    have h_eq :
        {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖}
          = ({p | p.1 ∈ K} ∩ {p | p.2 ∈ K}) ∩ {p | (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖} := by
      ext p; simp [and_assoc]
    rw [h_eq]
    exact (h1.inter h2).inter h3
  have h_compact_KK : IsCompact (K ×ˢ K) := hK.prod hK
  have h_subset : {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖}
      ⊆ K ×ˢ K := by
    rintro ⟨y, z⟩ ⟨hy, hz, _⟩
    exact ⟨hy, hz⟩
  have h_compact :
      IsCompact {p : E × E | p.1 ∈ K ∧ p.2 ∈ K ∧ (1 : ℝ) / (n + 1) ≤ ‖p.1 - p.2‖} :=
    h_compact_KK.of_isClosed_subset h_subset_cl h_subset
  exact (h_compact.image mid_continuous).isClosed

/-- A non-extreme point of a convex set is the midpoint of two distinct points of the set. -/
lemma exists_mid_of_not_extremePoint {K : Set E} (hK_convex : Convex ℝ K)
    {x : E} (hxK : x ∈ K) (hx_not_ext : x ∉ Set.extremePoints ℝ K) :
    ∃ y ∈ K, ∃ z ∈ K, y ≠ z ∧ mid y z = x := by
  rw [mem_extremePoints_iff_left] at hx_not_ext
  push Not at hx_not_ext
  obtain ⟨x₁, hx₁, x₂, hx₂, hx_open, hx₁_ne⟩ := hx_not_ext hxK
  obtain ⟨a, b, ha, hb, hab, hx_eq⟩ := hx_open
  have hx₁_ne_x₂ : x₁ ≠ x₂ := by
    intro hx_eq_12
    apply hx₁_ne
    rw [← hx_eq, hx_eq_12, ← add_smul, hab, one_smul]
  set r : ℝ := min a b with hr_def
  have hr_pos : 0 < r := lt_min ha hb
  have hr_le_a : r ≤ a := min_le_left a b
  have hr_le_b : r ≤ b := min_le_right a b
  set y' : E := (a - r) • x₁ + (b + r) • x₂ with hy'_def
  set z' : E := (a + r) • x₁ + (b - r) • x₂ with hz'_def
  have ha_minus_r : 0 ≤ a - r := sub_nonneg.mpr hr_le_a
  have hb_minus_r : 0 ≤ b - r := sub_nonneg.mpr hr_le_b
  have ha_plus_r : 0 ≤ a + r := add_nonneg ha.le hr_pos.le
  have hb_plus_r : 0 ≤ b + r := add_nonneg hb.le hr_pos.le
  have h_sum_y : (a - r) + (b + r) = 1 := by linarith
  have h_sum_z : (a + r) + (b - r) = 1 := by linarith
  have hy'_K : y' ∈ K := hK_convex hx₁ hx₂ ha_minus_r hb_plus_r h_sum_y
  have hz'_K : z' ∈ K := hK_convex hx₁ hx₂ ha_plus_r hb_minus_r h_sum_z
  refine ⟨y', hy'_K, z', hz'_K, ?_, ?_⟩
  · -- y' - z' = -(2r) • (x₁ - x₂); r > 0, x₁ ≠ x₂ ⇒ y' ≠ z'.
    intro h_eq
    have h_sub_zero : y' - z' = 0 := by rw [h_eq, sub_self]
    have h_diff_eq : y' - z' = (-(2 * r)) • (x₁ - x₂) := by
      simp only [hy'_def, hz'_def, smul_sub]
      module
    rw [h_diff_eq] at h_sub_zero
    have h2r_ne : -(2 * r) ≠ 0 := neg_ne_zero.mpr (by positivity)
    rw [smul_eq_zero] at h_sub_zero
    rcases h_sub_zero with h | h
    · exact h2r_ne h
    · exact hx₁_ne_x₂ (sub_eq_zero.mp h)
  · -- mid y' z' = (1/2) • (y' + z') = a • x₁ + b • x₂ = x.
    unfold mid
    have h_add_eq : (1 / 2 : ℝ) • (y' + z') = a • x₁ + b • x₂ := by
      simp only [hy'_def, hz'_def]
      module
    rw [h_add_eq]
    exact hx_eq

/-- The set of extreme points of `K` equals `K` minus the union of the "non-extreme at scale `n`"
sets. -/
lemma extremePoints_eq_diff_iUnion {K : Set E} (hK_convex : Convex ℝ K) :
    Set.extremePoints ℝ K = K \ ⋃ n, nonExtremeAtScale K n := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro hx_in
    rw [mem_iUnion] at hx_in
    obtain ⟨n, ⟨⟨y, z⟩, ⟨hy, hz, hyz⟩, h_mid⟩⟩ := hx_in
    -- mid y z = x ∈ openSegment y z; extremality forces y = x and z = x,
    -- so y = z, contradicting ‖y - z‖ ≥ 1/(n+1) > 0.
    have hyz_pos : 0 < ‖y - z‖ := by
      have h1 : 0 < (1 : ℝ) / (n + 1) := by positivity
      linarith
    have hy_ne_z : y ≠ z := norm_sub_pos_iff.mp hyz_pos
    have h_open : x ∈ openSegment ℝ y z := by
      rw [← h_mid]; exact mid_mem_openSegment hy_ne_z
    have hx_full := mem_extremePoints.mp hx
    obtain ⟨_, h_imp⟩ := hx_full
    obtain ⟨hy_eq, hz_eq⟩ := h_imp y hy z hz h_open
    exact hy_ne_z (hy_eq.trans hz_eq.symm)
  · rintro ⟨hxK, hx_not_in⟩
    rw [mem_iUnion, not_exists] at hx_not_in
    by_contra hx_not_ext
    obtain ⟨y, hy, z, hz, hy_ne_z, h_mid⟩ :=
      exists_mid_of_not_extremePoint hK_convex hxK hx_not_ext
    have hyz_pos : 0 < ‖y - z‖ := by
      rw [norm_sub_pos_iff]; exact hy_ne_z
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖y - z‖)
    have h_le : (1 : ℝ) / (n + 1) ≤ ‖y - z‖ := by
      have hn1_pos : (0 : ℝ) < n + 1 := by positivity
      rw [div_le_iff₀ hn1_pos]
      rw [div_lt_iff₀ hyz_pos] at hn
      nlinarith
    apply hx_not_in n
    refine ⟨(y, z), ⟨hy, hz, h_le⟩, h_mid⟩

/-- For a compact convex set `K` in a real normed space, the set of extreme points is a Gδ set. -/
theorem isGδ_extremePoints_of_compact_convex {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    IsGδ (Set.extremePoints ℝ K) := by
  rw [extremePoints_eq_diff_iUnion hK_convex]
  rw [show K \ ⋃ n, nonExtremeAtScale K n
      = K ∩ ⋂ n, (nonExtremeAtScale K n)ᶜ from by
    rw [diff_eq, compl_iUnion]]
  refine hK_compact.isClosed.isGδ.inter (.iInter fun n => ?_)
  exact (isClosed_nonExtremeAtScale hK_compact n).isOpen_compl.isGδ

/-- For a compact convex set `K` in a real normed space, the set of extreme points is Borel
measurable. -/
theorem measurableSet_extremePoints_of_compact_convex
    [MeasurableSpace E] [BorelSpace E] {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) :
    MeasurableSet (Set.extremePoints ℝ K) :=
  (isGδ_extremePoints_of_compact_convex hK_compact hK_convex).measurableSet
