/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Real.StarOrdered

/-!
# Cauchy mean-value packaging: Secant slopes and concavity

For a parametrized planar curve `(ψ, φ)` whose derivative ratio `φ'/ψ'` is antitone and with
`ψ' > 0`, the Cauchy mean-value theorem turns the antitone derivative ratio into antitone secant
slopes, and hence into concavity of the function `s` defined by `s ∘ ψ = φ`. This packages the
classical "monotone derivative ratio ⇒ concave" argument in a form convenient for representing a
value function as a concave function of a reparametrizing coordinate.

## Main statements

* `secantRatio_antitone_of_derivRatio_antitone` — antitone `φ'/ψ'` (with `ψ' > 0`) yields antitone
  secant slopes of the curve `(ψ, φ)`.
* `concaveOn_image_of_derivRatio_antitone` — under the same hypotheses, the function `s` with
  `s (ψ x) = φ x` is concave on `[ψ a, ψ b]`.

## Tags

Cauchy mean value theorem, secant slope, concavity, derivative ratio
-/

@[expose] public section

open Set

/-- A continuous function on `[a, b]` with positive derivative on the open interior is strictly
monotone on `[a, b]`. Shared scaffolding for the Cauchy-MVT secant and concavity results. -/
private theorem strictMonoOn_Icc_of_deriv_pos {a b : ℝ} {ψ : ℝ → ℝ}
    (hψ_cont : ContinuousOn ψ (Icc a b))
    (hψ_deriv_pos : ∀ t ∈ Ioo a b, 0 < deriv ψ t) :
    StrictMonoOn ψ (Icc a b) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _) hψ_cont fun t ht =>
    hψ_deriv_pos t (by simpa [interior_Icc] using ht)

/-- Cauchy mean-value packaging: If `φ'/ψ'` is antitone on `(a, b)` and `ψ' > 0` there, then the
secant slopes of the parametrized curve `(ψ, φ)` are antitone in the parameter.

Concretely, for `a ≤ x < y < z ≤ b`, `(φ z - φ y) / (ψ z - ψ y) ≤ (φ y - φ x) / (ψ y - ψ x)`. -/
theorem secantRatio_antitone_of_derivRatio_antitone {a b : ℝ}
    {φ ψ : ℝ → ℝ}
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hψ_cont : ContinuousOn ψ (Icc a b))
    (hφ_diff : DifferentiableOn ℝ φ (Ioo a b))
    (hψ_diff : DifferentiableOn ℝ ψ (Ioo a b))
    (hψ_deriv_pos : ∀ t ∈ Ioo a b, 0 < deriv ψ t)
    (h_ratio_anti :
      AntitoneOn (fun t => deriv φ t / deriv ψ t) (Ioo a b))
    {x y z : ℝ} (hx : x ∈ Icc a b) (hz : z ∈ Icc a b)
    (hxy : x < y) (hyz : y < z) :
    (φ z - φ y) / (ψ z - ψ y) ≤ (φ y - φ x) / (ψ y - ψ x) := by
  have hxz : x < z := lt_trans hxy hyz
  have hy_mem : y ∈ Icc a b := ⟨le_trans hx.1 (le_of_lt hxy), le_trans (le_of_lt hyz) hz.2⟩
  -- Restrict continuity / differentiability to the two subintervals.
  have hxy_sub_Icc : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy_mem.2
  have hyz_sub_Icc : Icc y z ⊆ Icc a b := Icc_subset_Icc hy_mem.1 hz.2
  have hxy_sub_Ioo : Ioo x y ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_le_of_lt hx.1 ht.1, lt_of_lt_of_le ht.2 hy_mem.2⟩
  have hyz_sub_Ioo : Ioo y z ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_le_of_lt hy_mem.1 ht.1, lt_of_lt_of_le ht.2 hz.2⟩
  -- Cauchy MVT on [x, y]
  obtain ⟨c₁, hc₁_mem, hc₁_eq⟩ :=
    exists_ratio_deriv_eq_ratio_slope φ hxy
      (hφ_cont.mono hxy_sub_Icc)
      (hφ_diff.mono hxy_sub_Ioo)
      ψ
      (hψ_cont.mono hxy_sub_Icc)
      (hψ_diff.mono hxy_sub_Ioo)
  -- Cauchy MVT on [y, z]
  obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ :=
    exists_ratio_deriv_eq_ratio_slope φ hyz
      (hφ_cont.mono hyz_sub_Icc)
      (hφ_diff.mono hyz_sub_Ioo)
      ψ
      (hψ_cont.mono hyz_sub_Icc)
      (hψ_diff.mono hyz_sub_Ioo)
  -- Translate the points back to (a, b).
  have hc₁_ab : c₁ ∈ Ioo a b := hxy_sub_Ioo hc₁_mem
  have hc₂_ab : c₂ ∈ Ioo a b := hyz_sub_Ioo hc₂_mem
  -- ψ' > 0 at the two intermediate points.
  have hψ'c₁_pos : 0 < deriv ψ c₁ := hψ_deriv_pos c₁ hc₁_ab
  have hψ'c₂_pos : 0 < deriv ψ c₂ := hψ_deriv_pos c₂ hc₂_ab
  -- ψ is strictly monotone on [a, b], hence ψ y - ψ x > 0 and ψ z - ψ y > 0.
  have hψ_strictMono : StrictMonoOn ψ (Icc a b) :=
    strictMonoOn_Icc_of_deriv_pos hψ_cont hψ_deriv_pos
  have hψyx_pos : 0 < ψ y - ψ x := by
    have : ψ x < ψ y := hψ_strictMono hx hy_mem hxy
    linarith
  have hψzy_pos : 0 < ψ z - ψ y := by
    have : ψ y < ψ z := hψ_strictMono hy_mem hz hyz
    linarith
  -- Rewrite each secant slope as the derivative ratio at the intermediate point.
  have h_left :
      (φ y - φ x) / (ψ y - ψ x) = deriv φ c₁ / deriv ψ c₁ := by
    have hmul : (ψ y - ψ x) * deriv φ c₁ = (φ y - φ x) * deriv ψ c₁ := hc₁_eq
    field_simp [hψyx_pos.ne', hψ'c₁_pos.ne'] at hmul ⊢
    linarith
  have h_right :
      (φ z - φ y) / (ψ z - ψ y) = deriv φ c₂ / deriv ψ c₂ := by
    have hmul : (ψ z - ψ y) * deriv φ c₂ = (φ z - φ y) * deriv ψ c₂ := hc₂_eq
    field_simp [hψzy_pos.ne', hψ'c₂_pos.ne'] at hmul ⊢
    linarith
  -- Compare via antitonicity of the ratio: c₁ < y < c₂, so c₁ ≤ c₂.
  have hc₁_le_c₂ : c₁ ≤ c₂ := le_of_lt (lt_trans hc₁_mem.2 hc₂_mem.1)
  have h_anti :
      deriv φ c₂ / deriv ψ c₂ ≤ deriv φ c₁ / deriv ψ c₁ :=
    h_ratio_anti hc₁_ab hc₂_ab hc₁_le_c₂
  rw [h_left, h_right]
  exact h_anti

/-- Parametrized concavity result: If `ψ` is a strictly monotone continuous map on `[a, b]`, `φ`
and `ψ` are differentiable on `(a, b)` with `ψ' > 0`, the derivative ratio `φ'/ψ'` is antitone on
`(a, b)`, and `s` agrees with `φ ∘ ψ⁻¹` on the image (i.e. `s ∘ ψ = φ` on `[a, b]`), then `s` is
concave on the image interval `[ψ a, ψ b]`. -/
theorem concaveOn_image_of_derivRatio_antitone {a b : ℝ} (hab : a ≤ b)
    {φ ψ s : ℝ → ℝ}
    (hφ_cont : ContinuousOn φ (Icc a b))
    (hψ_cont : ContinuousOn ψ (Icc a b))
    (hφ_diff : DifferentiableOn ℝ φ (Ioo a b))
    (hψ_diff : DifferentiableOn ℝ ψ (Ioo a b))
    (hψ_deriv_pos : ∀ t ∈ Ioo a b, 0 < deriv ψ t)
    (h_ratio_anti :
      AntitoneOn (fun t => deriv φ t / deriv ψ t) (Ioo a b))
    (h_eq : ∀ x ∈ Icc a b, s (ψ x) = φ x) :
    ConcaveOn ℝ (Icc (ψ a) (ψ b)) s := by
  have hψ_strictMono : StrictMonoOn ψ (Icc a b) :=
    strictMonoOn_Icc_of_deriv_pos hψ_cont hψ_deriv_pos
  have h_image : ψ '' Icc a b = Icc (ψ a) (ψ b) :=
    hψ_cont.image_Icc_of_monotoneOn hab hψ_strictMono.monotoneOn
  refine concaveOn_of_slope_anti_adjacent (convex_Icc _ _) ?_
  intro μx μy μz hμx hμz hμxy hμyz
  -- Pull μ values back to the parameter [a, b] via the IVT.
  have hμx_image : μx ∈ ψ '' Icc a b := by rw [h_image]; exact hμx
  have hμz_image : μz ∈ ψ '' Icc a b := by rw [h_image]; exact hμz
  have hμy_image : μy ∈ ψ '' Icc a b := by
    rw [h_image]
    exact ⟨le_trans hμx.1 (le_of_lt hμxy), le_trans (le_of_lt hμyz) hμz.2⟩
  obtain ⟨tx, htx_mem, htx_eq⟩ := hμx_image
  obtain ⟨ty, hty_mem, hty_eq⟩ := hμy_image
  obtain ⟨tz, htz_mem, htz_eq⟩ := hμz_image
  -- Strict monotonicity of ψ transfers the order μx < μy < μz to tx < ty < tz.
  have htxy : tx < ty :=
    (hψ_strictMono.lt_iff_lt htx_mem hty_mem).mp (by rw [htx_eq, hty_eq]; exact hμxy)
  have htyz : ty < tz :=
    (hψ_strictMono.lt_iff_lt hty_mem htz_mem).mp (by rw [hty_eq, htz_eq]; exact hμyz)
  -- Translate s-values to φ-values via h_eq.
  have hsx : s μx = φ tx := by rw [← htx_eq]; exact h_eq tx htx_mem
  have hsy : s μy = φ ty := by rw [← hty_eq]; exact h_eq ty hty_mem
  have hsz : s μz = φ tz := by rw [← htz_eq]; exact h_eq tz htz_mem
  -- Translate μ-differences to ψ-differences.
  have hΔxy : μy - μx = ψ ty - ψ tx := by rw [← htx_eq, ← hty_eq]
  have hΔyz : μz - μy = ψ tz - ψ ty := by rw [← hty_eq, ← htz_eq]
  rw [hsx, hsy, hsz, hΔxy, hΔyz]
  exact secantRatio_antitone_of_derivRatio_antitone
    hφ_cont hψ_cont hφ_diff hψ_diff hψ_deriv_pos h_ratio_anti
    htx_mem htz_mem htxy htyz
