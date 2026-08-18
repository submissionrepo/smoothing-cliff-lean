/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexRightDeriv

/-!
# Bounded-derivative approximation of continuous convex functions

A convex function on `[a, b]` that is additionally continuous on the closed interval can still have
unbounded one-sided derivatives at the endpoints (e.g. `φ(x) = -√x` on `[0, 1]`, whose right
derivative tends to `-∞` at `0`). This file approximates such functions by convex functions whose
right-derivative image is bounded on the interior.

This file closes that gap by approximation. For `φ` convex and continuous on `[a, b]` the **affine
truncation** `affineTrunc` agrees with `φ` on an inner interval `[c, d] ⊆ (a, b)` and is extended
affinely outside, with the boundary right-derivatives as slopes. Each truncation is convex,
continuous, and has bounded right-derivative image, and along an inner sequence `[c, d] ↑ (a, b)`
the truncations are uniformly bounded and converge pointwise to `φ` on `[a, b]`.

## Main definitions

* `ConvexOn.affineTrunc` — the affine truncation of `φ` to `[c, d]` with prescribed boundary slopes.

## Main statements

* `ConvexOn.exists_seq_bddRightDeriv_tendsto` — every continuous convex `φ` on `[a, b]` is a
  uniformly bounded pointwise limit on `[a, b]` of convex functions, continuous on `[a, b]`, with
  bounded right-derivative image on `(a, b)`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Function Topology

variable {φ : ℝ → ℝ} {a b : ℝ}

namespace ConvexOn

/-- The affine truncation of `φ` to `[c, d]`: Equal to `φ` on `[c, d]`, and extended outside by the
affine functions with slopes `sc` (left of `c`) and `sd` (right of `d`) matching `φ` at the
endpoints. When `sc`/`sd` are the right-derivatives of a convex `φ` at `c`/`d`, this is convex with
right-derivative image contained in `[sc, sd]`. -/
noncomputable def affineTrunc (φ : ℝ → ℝ) (c d sc sd : ℝ) : ℝ → ℝ :=
  fun t =>
    if t < c then φ c + sc * (t - c)
    else if d < t then φ d + sd * (t - d)
    else φ t

/-- On the inner interval `[c, d]`, the affine truncation agrees with `φ`. -/
@[simp] lemma affineTrunc_of_mem {c d sc sd t : ℝ} (hct : c ≤ t) (htd : t ≤ d) :
    affineTrunc φ c d sc sd t = φ t := by
  unfold affineTrunc
  rw [if_neg (not_lt.mpr hct), if_neg (not_lt.mpr htd)]

/-- Left of `c`, the affine truncation is the line through `(c, φ c)` with slope `sc`. -/
lemma affineTrunc_of_lt {c d sc sd t : ℝ} (h : t < c) :
    affineTrunc φ c d sc sd t = φ c + sc * (t - c) := by
  unfold affineTrunc; rw [if_pos h]

/-- Right of `d`, the affine truncation is the line through `(d, φ d)` with slope `sd`. -/
lemma affineTrunc_of_gt {c d sc sd t : ℝ} (hcd : c ≤ d) (h : d < t) :
    affineTrunc φ c d sc sd t = φ d + sd * (t - d) := by
  unfold affineTrunc
  rw [if_neg (not_lt.mpr (le_trans hcd h.le)), if_pos h]

/-- A convex function lies above its right-derivative support line at an interior point. -/
private lemma support_line_le {g : ℝ → ℝ} (hg : ConvexOn ℝ (Icc a b) g)
    {m t : ℝ} (hm : m ∈ Ioo a b) (ht : t ∈ Icc a b) :
    g m + (derivWithin g (Ioi m) m) * (t - m) ≤ g t := by
  have hmI : m ∈ interior (Icc a b) := by rw [interior_Icc]; exact hm
  set R := derivWithin g (Ioi m) m with hRdef
  rcases lt_trichotomy t m with htm | rfl | hmt
  · -- t < m : use slope g t m ≤ leftDeriv g m ≤ R
    have hslope : slope g t m ≤ derivWithin g (Iio m) m :=
      hg.slope_le_leftDeriv_of_mem_interior ht hmI htm
    have hld : derivWithin g (Iio m) m ≤ R := hg.leftDeriv_le_rightDeriv_of_mem_interior hmI
    have hslope' : (g m - g t) / (m - t) ≤ R := by
      have : slope g t m = (g m - g t) / (m - t) := by
        rw [slope_def_field]
      rw [this] at hslope; linarith
    have hmt_pos : 0 < m - t := by linarith
    rw [div_le_iff₀ hmt_pos] at hslope'
    nlinarith [hslope']
  · simp
  · -- m < t : use R ≤ slope g m t
    have hslope : R ≤ slope g m t :=
      hg.rightDeriv_le_slope_of_mem_interior hmI ht hmt
    have hslope' : R ≤ (g t - g m) / (t - m) := by
      have : slope g m t = (g t - g m) / (t - m) := by rw [slope_def_field]
      rw [this] at hslope; exact hslope
    have hmt_pos : 0 < t - m := by linarith
    rw [le_div_iff₀ hmt_pos] at hslope'
    nlinarith [hslope']

/-- The affine truncation is convex on all of `ℝ`. -/
private lemma affineTrunc_convexOn (hφ : ConvexOn ℝ (Icc a b) φ)
    {c d : ℝ} (hac : a < c) (hcd : c < d) (hdb : d < b) :
    ConvexOn ℝ univ (affineTrunc φ c d (derivWithin φ (Ioi c) c) (derivWithin φ (Ioi d) d)) := by
  set R : ℝ → ℝ := fun x => derivWithin φ (Ioi x) x with hRdef
  set sc := R c with hsc
  set sd := R d with hsd
  set g := affineTrunc φ c d sc sd with hg
  have hcI : c ∈ Ioo a b := ⟨hac, lt_trans hcd hdb⟩
  have hdI : d ∈ Ioo a b := ⟨lt_trans hac hcd, hdb⟩
  have hcIic : c ∈ Icc a b := ⟨hac.le, (lt_trans hcd hdb).le⟩
  have hdIic : d ∈ Icc a b := ⟨(lt_trans hac hcd).le, hdb.le⟩
  -- monotonicity of R on the interior
  have hRmono : MonotoneOn R (Ioo a b) := by
    rw [← interior_Icc]; exact hφ.monotoneOn_rightDeriv
  have hsc_sd : sc ≤ sd := hRmono hcI hdI hcd.le
  -- φ's support line at c, d below φ on [a,b]
  have hSc : ∀ t ∈ Icc a b, φ c + sc * (t - c) ≤ φ t := fun t ht => support_line_le hφ hcI ht
  have hSd : ∀ t ∈ Icc a b, φ d + sd * (t - d) ≤ φ t := fun t ht => support_line_le hφ hdI ht
  -- Fact (A): the left support line ℓc lies below g everywhere.
  have hA : ∀ t : ℝ, φ c + sc * (t - c) ≤ g t := by
    intro t
    rcases lt_trichotomy t c with htc | htc | hct
    · rw [hg, affineTrunc_of_lt htc]
    · rw [htc, hg, affineTrunc_of_mem (le_refl c) hcd.le]; simp
    · rcases le_or_gt t d with htd | hdt
      · rw [hg, affineTrunc_of_mem hct.le htd]
        exact hSc t ⟨le_trans hac.le hct.le, le_trans htd hdb.le⟩
      · rw [hg, affineTrunc_of_gt hcd.le hdt]
        have hcd_le := hSc d hdIic
        nlinarith [hcd_le, hsc_sd, sub_pos.mpr hdt]
  -- Fact (B): the right support line ℓd lies below g everywhere.
  have hB : ∀ t : ℝ, φ d + sd * (t - d) ≤ g t := by
    intro t
    rcases lt_trichotomy t d with htd | htd | hdt
    · rcases lt_or_ge t c with htc | hct
      · rw [hg, affineTrunc_of_lt htc]
        have hdc_le := hSd c hcIic
        nlinarith [hdc_le, hsc_sd, sub_pos.mpr htc]
      · rw [hg, affineTrunc_of_mem hct htd.le]
        exact hSd t ⟨le_trans hac.le hct, le_trans htd.le hdb.le⟩
    · rw [htd, hg, affineTrunc_of_mem hcd.le (le_refl d)]; simp
    · rw [hg, affineTrunc_of_gt hcd.le hdt]
  -- Fact (C): for an interior y in (c,d), φ's support line at y lies below g.
  have hC : ∀ y : ℝ, c < y → y < d → ∀ t : ℝ, φ y + R y * (t - y) ≤ g t := by
    intro y hcy hyd t
    have hyI : y ∈ Ioo a b := ⟨lt_trans hac hcy, lt_trans hyd hdb⟩
    have hyIic : y ∈ Icc a b := ⟨hyI.1.le, hyI.2.le⟩
    have hSy : ∀ s ∈ Icc a b, φ y + R y * (s - y) ≤ φ s := fun s hs => support_line_le hφ hyI hs
    have hsc_sy : sc ≤ R y := hRmono hcI hyI hcy.le
    have hsy_sd : R y ≤ sd := hRmono hyI hdI hyd.le
    rcases lt_trichotomy t c with htc | htc | hct
    · rw [hg, affineTrunc_of_lt htc]
      have hyc := hSy c hcIic
      nlinarith [hyc, hsc_sy, sub_pos.mpr htc]
    · rw [htc, hg, affineTrunc_of_mem (le_refl c) hcd.le]
      exact hSy c hcIic
    · rcases le_or_gt t d with htd | hdt
      · rw [hg, affineTrunc_of_mem hct.le htd]
        exact hSy t ⟨le_trans hac.le hct.le, le_trans htd hdb.le⟩
      · rw [hg, affineTrunc_of_gt hcd.le hdt]
        have hyd' := hSy d hdIic
        nlinarith [hyd', hsy_sd, sub_pos.mpr hdt]
  -- Convexity via monotone adjacent slopes.
  apply convexOn_of_slope_mono_adjacent (convex_univ)
  intro x y z _ _ hxy hyz
  -- pick a subgradient μ at y and the corresponding support line below g
  have key : ∃ μ : ℝ, (∀ t : ℝ, g y + μ * (t - y) ≤ g t) := by
    rcases le_or_gt y c with hyc | hcy
    · refine ⟨sc, fun t => ?_⟩
      have hgy : g y = φ c + sc * (y - c) := by
        rcases lt_or_eq_of_le hyc with hyc' | hyc'
        · rw [hg, affineTrunc_of_lt hyc']
        · rw [hyc', hg, affineTrunc_of_mem (le_refl c) hcd.le]; ring
      rw [hgy]
      have := hA t; nlinarith [this]
    · rcases lt_or_ge y d with hyd | hdy
      · refine ⟨R y, fun t => ?_⟩
        have hgy : g y = φ y := by
          rw [hg, affineTrunc_of_mem hcy.le hyd.le]
        rw [hgy]
        exact hC y hcy hyd t
      · refine ⟨sd, fun t => ?_⟩
        have hgy : g y = φ d + sd * (y - d) := by
          rcases lt_or_eq_of_le hdy with hdy' | hdy'
          · rw [hg, affineTrunc_of_gt hcd.le hdy']
          · rw [← hdy', hg, affineTrunc_of_mem hcd.le (le_refl d)]; ring
        rw [hgy]
        have := hB t; nlinarith [this]
  obtain ⟨μ, hμ⟩ := key
  -- the difference quotients are sandwiched by μ
  have hsxy : (g y - g x) / (y - x) ≤ μ := by
    have hx := hμ x
    rw [div_le_iff₀ (by linarith : 0 < y - x)]
    nlinarith [hx]
  have hsyz : μ ≤ (g z - g y) / (z - y) := by
    have hz := hμ z
    rw [le_div_iff₀ (by linarith : 0 < z - y)]
    nlinarith [hz]
  linarith [hsxy, hsyz]

/-- The affine truncation is continuous on `[a, b]`. -/
private lemma affineTrunc_continuousOn
    (hcont : ContinuousOn φ (Icc a b)) {c d sc sd : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) :
    ContinuousOn (affineTrunc φ c d sc sd) (Icc a b) := by
  have hℓc : Continuous (fun t => φ c + sc * (t - c)) := by fun_prop
  have hℓd : Continuous (fun t => φ d + sd * (t - d)) := by fun_prop
  have hac' : a ≤ c := hac.le
  have hcd' : c ≤ d := hcd.le
  have hdb' : d ≤ b := hdb.le
  -- ContinuousOn on the left affine piece [a, c].
  have hL : ContinuousOn (affineTrunc φ c d sc sd) (Icc a c) := by
    apply (hℓc.continuousOn).congr
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htc | htc
    · rw [affineTrunc_of_lt htc]
    · rw [htc, affineTrunc_of_mem (le_refl c) hcd']
      simp
  -- ContinuousOn on the middle piece [c, d], where it equals φ.
  have hM : ContinuousOn (affineTrunc φ c d sc sd) (Icc c d) := by
    apply (hcont.mono ?_).congr
    · intro t ht; rw [affineTrunc_of_mem ht.1 ht.2]
    · exact Icc_subset_Icc hac' hdb'
  -- ContinuousOn on the right affine piece [d, b].
  have hRr : ContinuousOn (affineTrunc φ c d sc sd) (Icc d b) := by
    apply (hℓd.continuousOn).congr
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hdt | hdt
    · rw [affineTrunc_of_gt hcd' hdt]
    · rw [← hdt, affineTrunc_of_mem hcd' (le_refl d)]
      simp
  -- Glue the three closed pieces.
  have hLM : ContinuousOn (affineTrunc φ c d sc sd) (Icc a d) := by
    rw [← Set.Icc_union_Icc_eq_Icc hac' hcd']
    exact hL.union_of_isClosed hM isClosed_Icc isClosed_Icc
  have : ContinuousOn (affineTrunc φ c d sc sd) (Icc a b) := by
    rw [← Set.Icc_union_Icc_eq_Icc (le_trans hac' hcd') hdb']
    exact hLM.union_of_isClosed hRr isClosed_Icc isClosed_Icc
  exact this

/-- The affine truncation lies below `φ` on `[a, b]` (support lines below the graph). -/
private lemma affineTrunc_le (hφ : ConvexOn ℝ (Icc a b) φ)
    {c d : ℝ} (hac : a < c) (hcd : c < d) (hdb : d < b) {t : ℝ} (ht : t ∈ Icc a b) :
    affineTrunc φ c d (derivWithin φ (Ioi c) c) (derivWithin φ (Ioi d) d) t ≤ φ t := by
  have hcoo : c ∈ Ioo a b := ⟨hac, lt_trans hcd hdb⟩
  have hdoo : d ∈ Ioo a b := ⟨lt_trans hac hcd, hdb⟩
  rcases lt_or_ge t c with htc | hct
  · rw [affineTrunc_of_lt htc]
    exact support_line_le hφ hcoo ht
  · rcases le_or_gt t d with htd | hdt
    · rw [affineTrunc_of_mem hct htd]
    · rw [affineTrunc_of_gt hcd.le hdt]
      exact support_line_le hφ hdoo ht

/-- On the left affine tail `x < c`, the right derivative of the truncation is the slope `sc`. -/
private lemma affineTrunc_hasDerivWithinAt_left {c d sc sd x : ℝ} (hxc : x < c) :
    HasDerivWithinAt (affineTrunc φ c d sc sd) sc (Ioi x) x := by
  have hbase : HasDerivWithinAt (fun t => φ c + sc * (t - c)) sc (Ioi x) x := by
    have : HasDerivAt (fun t => φ c + sc * (t - c)) sc x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul sc |>.const_add (φ c)
    exact this.hasDerivWithinAt
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [eventually_mem_nhdsWithin.mono (fun y hy => hy),
      (eventually_nhdsWithin_of_eventually_nhds (isOpen_Iio.eventually_mem hxc))] with t _ htc
    exact affineTrunc_of_lt htc
  · exact affineTrunc_of_lt hxc

/-- On the right affine tail `d < x`, the right derivative of the truncation is the slope `sd`. -/
private lemma affineTrunc_hasDerivWithinAt_right {c d sc sd x : ℝ} (hcd : c ≤ d) (hdx : d ≤ x) :
    HasDerivWithinAt (affineTrunc φ c d sc sd) sd (Ioi x) x := by
  have hbase : HasDerivWithinAt (fun t => φ d + sd * (t - d)) sd (Ioi x) x := by
    have : HasDerivAt (fun t => φ d + sd * (t - d)) sd x := by
      simpa using ((hasDerivAt_id x).sub_const d).const_mul sd |>.const_add (φ d)
    exact this.hasDerivWithinAt
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with t htx
    exact affineTrunc_of_gt hcd (lt_of_le_of_lt hdx htx)
  · rcases lt_or_eq_of_le hdx with hdx' | hdx'
    · exact affineTrunc_of_gt hcd hdx'
    · rw [← hdx', affineTrunc_of_mem hcd (le_refl d)]; ring

/-- On the interior `c ≤ x < d`, the right derivative of the truncation equals that of `φ`. -/
private lemma affineTrunc_hasDerivWithinAt_mid (hφ : ConvexOn ℝ (Icc a b) φ)
    {c d : ℝ} (hac : a < c) (hdb : d < b) {sc sd x : ℝ}
    (hcx : c ≤ x) (hxd : x < d) :
    HasDerivWithinAt (affineTrunc φ c d sc sd) (derivWithin φ (Ioi x) x) (Ioi x) x := by
  have hxI : x ∈ interior (Icc a b) := by
    rw [interior_Icc]
    exact ⟨lt_of_lt_of_le hac hcx, lt_trans hxd hdb⟩
  have hbase : HasDerivWithinAt φ (derivWithin φ (Ioi x) x) (Ioi x) x :=
    hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hxI
  apply hbase.congr_of_eventuallyEq
  · filter_upwards [(eventually_nhdsWithin_of_eventually_nhds
      (isOpen_Iio.eventually_mem hxd)),
      self_mem_nhdsWithin] with t htd htx
    exact affineTrunc_of_mem (le_trans hcx (le_of_lt htx)) (le_of_lt htd)
  · exact affineTrunc_of_mem hcx (le_of_lt hxd)

/-- **Bounded-derivative approximation of a continuous convex function.**

For `φ` convex and continuous on `[a, b]` (`a < b`), there is a sequence `φₙ` of functions, each
convex and continuous on `[a, b]` with bounded right-derivative image on `(a, b)`, uniformly
bounded on `[a, b]`, converging to `φ` pointwise on `[a, b]`. -/
theorem exists_seq_bddRightDeriv_tendsto
    (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b) (hcont : ContinuousOn φ (Icc a b)) :
    ∃ (φₙ : ℕ → ℝ → ℝ) (M : ℝ),
      (∀ n, ConvexOn ℝ (Icc a b) (φₙ n)) ∧
      (∀ n, ContinuousOn (φₙ n) (Icc a b)) ∧
      (∀ n, BddBelow ((fun x => derivWithin (φₙ n) (Ioi x) x) '' Ioo a b)) ∧
      (∀ n, BddAbove ((fun x => derivWithin (φₙ n) (Ioi x) x) '' Ioo a b)) ∧
      (∀ n, ∀ x ∈ Icc a b, |φₙ n x| ≤ M) ∧
      (∀ x ∈ Icc a b, Tendsto (fun n => φₙ n x) atTop (𝓝 (φ x))) := by
  set R : ℝ → ℝ := fun x => derivWithin φ (Ioi x) x with hR
  -- Inner sequence: c n = a + (b-a)/(n+3), d n = b - (b-a)/(n+3), shrinking to the endpoints.
  set c : ℕ → ℝ := fun n => a + (b - a) / (n + 3) with hc_def
  set d : ℕ → ℝ := fun n => b - (b - a) / (n + 3) with hd_def
  set m : ℝ := (a + b) / 2 with hm_def
  have hba : (0:ℝ) < b - a := by linarith
  -- Positivity and ordering facts for the inner sequence.
  have hpos : ∀ n : ℕ, (0:ℝ) < (b - a) / (n + 3) := by
    intro n; positivity
  have hac : ∀ n : ℕ, a < c n := by
    intro n; have := hpos n; simp only [hc_def]; linarith
  have hkey : ∀ n : ℕ, (b - a) / (n + 3) < (b - a) / 2 := by
    intro n
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hba, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hcm : ∀ n : ℕ, c n < m := by
    intro n
    have := hkey n; simp only [hc_def, hm_def]; linarith
  have hmd : ∀ n : ℕ, m < d n := by
    intro n
    have := hkey n; simp only [hd_def, hm_def]; linarith
  have hcd : ∀ n : ℕ, c n < d n := fun n => lt_trans (hcm n) (hmd n)
  have hdb : ∀ n : ℕ, d n < b := by
    intro n; have := hpos n; simp only [hd_def]; linarith
  have hmem_m : m ∈ Ioo a b := ⟨by simp only [hm_def]; linarith, by simp only [hm_def]; linarith⟩
  -- The approximating sequence.
  set φₙ : ℕ → ℝ → ℝ := fun n => affineTrunc φ (c n) (d n) (R (c n)) (R (d n)) with hφₙ_def
  -- Convexity (on Icc a b, restricted from univ).
  have hconv : ∀ n, ConvexOn ℝ (Icc a b) (φₙ n) := by
    intro n
    exact (affineTrunc_convexOn hφ (hac n) (hcd n) (hdb n)).subset (subset_univ _) (convex_Icc a b)
  -- Continuity.
  have hcontφₙ : ∀ n, ContinuousOn (φₙ n) (Icc a b) := by
    intro n
    exact affineTrunc_continuousOn hcont (hac n) (hcd n) (hdb n)
  -- monotonicity of R on the interior
  have hRmono : MonotoneOn R (Ioo a b) := by
    rw [← interior_Icc]; exact hφ.monotoneOn_rightDeriv
  -- The right derivative of φₙ n at an interior point lies in [R (c n), R (d n)].
  have hderiv_mem : ∀ n, ∀ x ∈ Ioo a b,
      R (c n) ≤ derivWithin (φₙ n) (Ioi x) x ∧ derivWithin (φₙ n) (Ioi x) x ≤ R (d n) := by
    intro n x hx
    have hcnI : c n ∈ Ioo a b := ⟨hac n, lt_trans (hcd n) (hdb n)⟩
    have hdnI : d n ∈ Ioo a b := ⟨lt_trans (hac n) (hcd n), hdb n⟩
    have hsc_sd : R (c n) ≤ R (d n) := hRmono hcnI hdnI (hcd n).le
    have huniq : UniqueDiffWithinAt ℝ (Ioi x) x := uniqueDiffWithinAt_Ioi x
    have hgoal : φₙ n = affineTrunc φ (c n) (d n) (R (c n)) (R (d n)) := rfl
    rw [hgoal]
    rcases lt_or_ge x (c n) with hxc | hcx
    · have hd : derivWithin (affineTrunc φ (c n) (d n) (R (c n)) (R (d n))) (Ioi x) x = R (c n) :=
        (affineTrunc_hasDerivWithinAt_left (φ := φ) (d := d n) (sc := R (c n)) (sd := R (d n))
          hxc).derivWithin huniq
      rw [hd]; exact ⟨le_rfl, hsc_sd⟩
    · rcases lt_or_ge x (d n) with hxd | hdx
      · have hd : derivWithin (affineTrunc φ (c n) (d n) (R (c n)) (R (d n))) (Ioi x) x
            = derivWithin φ (Ioi x) x :=
          (affineTrunc_hasDerivWithinAt_mid hφ (hac n) (hdb n) (sc := R (c n)) (sd := R (d n))
            hcx hxd).derivWithin huniq
        rw [hd]
        exact ⟨hRmono hcnI hx hcx, hRmono hx hdnI hxd.le⟩
      · have hd : derivWithin (affineTrunc φ (c n) (d n) (R (c n)) (R (d n))) (Ioi x) x = R (d n) :=
          (affineTrunc_hasDerivWithinAt_right (φ := φ) (c := c n) (sc := R (c n))
            (hcd n).le hdx).derivWithin huniq
        rw [hd]; exact ⟨hsc_sd, le_rfl⟩
  -- derivWithin at m equals R m (used for the uniform lower bound).
  have hderiv_at_m : ∀ n, derivWithin (φₙ n) (Ioi m) m = R m := by
    intro n
    have huniq : UniqueDiffWithinAt ℝ (Ioi m) m := uniqueDiffWithinAt_Ioi m
    have hgoal : φₙ n = affineTrunc φ (c n) (d n) (R (c n)) (R (d n)) := rfl
    rw [hgoal]
    exact (affineTrunc_hasDerivWithinAt_mid hφ (hac n) (hdb n) (sc := R (c n)) (sd := R (d n))
      (hcm n).le (hmd n)).derivWithin huniq
  -- Bounds on φ over the compact interval.
  obtain ⟨Cφ, hCφ⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hcont
  -- The fixed midpoint support line and its bound.
  set ℓ : ℝ → ℝ := fun t => φ m + R m * (t - m) with hℓ_def
  have hℓ_cont : ContinuousOn ℓ (Icc a b) := by
    apply Continuous.continuousOn; simp only [hℓ_def]; fun_prop
  obtain ⟨Cℓ, hCℓ⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hℓ_cont
  -- Uniform bound.
  set M : ℝ := Cφ ⊔ Cℓ with hM_def
  refine ⟨φₙ, M, hconv, hcontφₙ, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨R (c n), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hderiv_mem n x hx).1
  · intro n
    refine ⟨R (d n), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hderiv_mem n x hx).2
  · intro n x hx
    have hupper : φₙ n x ≤ Cφ :=
      le_trans (affineTrunc_le hφ (hac n) (hcd n) (hdb n) hx) (le_of_abs_le (hCφ x hx))
    -- Lower bound: φₙ n x ≥ ℓ x ≥ -Cℓ, using the support line at m.
    have hsupp : ℓ x ≤ φₙ n x := by
      have := support_line_le (hconv n) hmem_m hx
      rw [hderiv_at_m n] at this
      have hφₙm : φₙ n m = φ m := by
        simp only [hφₙ_def]
        exact affineTrunc_of_mem (le_of_lt (hcm n)) (le_of_lt (hmd n))
      rw [hφₙm] at this
      simpa only [hℓ_def] using this
    have hlower : -Cℓ ≤ φₙ n x := le_trans (neg_le_of_abs_le (hCℓ x hx)) hsupp
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · calc -M ≤ -Cℓ := by simp only [hM_def]; rw [neg_le_neg_iff]; exact le_sup_right
      _ ≤ φₙ n x := hlower
    · calc φₙ n x ≤ Cφ := hupper
      _ ≤ M := le_sup_left
  · intro x hx
    -- Half-widths (b-a)/(n+3) → 0 as n → ∞, so [c n, d n] expands to (a, b).
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
    have hwidth : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 3)) atTop (𝓝 0) :=
      tendsto_bdd_div_atTop_nhds_zero (Filter.Eventually.of_forall fun _ => le_refl (b - a))
        (Filter.Eventually.of_forall fun _ => le_refl (b - a)) hden
    have hca : Tendsto c atTop (𝓝 a) := by
      have h : Tendsto (fun n : ℕ => a + (b - a) / ((n : ℝ) + 3)) atTop (𝓝 (a + 0)) :=
        (tendsto_const_nhds (x := a)).add hwidth
      rw [add_zero] at h
      simpa only [hc_def] using h
    have hdb_lim : Tendsto d atTop (𝓝 b) := by
      have h : Tendsto (fun n : ℕ => b - (b - a) / ((n : ℝ) + 3)) atTop (𝓝 (b - 0)) :=
        (tendsto_const_nhds (x := b)).sub hwidth
      rw [sub_zero] at h
      simpa only [hd_def] using h
    rcases eq_or_lt_of_le hx.1 with hxa | hax
    · -- x = a: squeeze via the explicit lower bound L n = φ(cₙ) - slope(cₙ,m)*(cₙ-a)
      subst hxa
      have hub : ∀ n, φₙ n a ≤ φ a :=
        fun n => affineTrunc_le hφ (hac n) (hcd n) (hdb n) hx
      set L : ℕ → ℝ := fun n => φ (c n) - (φ m - φ (c n)) * (c n - a) / (m - c n) with hL_def
      have hlb : ∀ n, L n ≤ φₙ n a := by
        intro n
        have hcnI : c n ∈ Ioo a b := ⟨hac n, lt_trans (hcd n) (hdb n)⟩
        have hslope : R (c n) ≤ slope φ (c n) m :=
          hφ.rightDeriv_le_slope_of_mem_interior (by rw [interior_Icc]; exact hcnI)
            ⟨hmem_m.1.le, hmem_m.2.le⟩ (hcm n)
        have hslope_eq : slope φ (c n) m = (φ m - φ (c n)) / (m - c n) := by rw [slope_def_field]
        rw [hslope_eq] at hslope
        have hcx_pos : (0:ℝ) ≤ c n - a := by have := hac n; linarith
        have hmcn_pos : (0:ℝ) < m - c n := by have := hcm n; linarith
        have hslope_clr : R (c n) * (m - c n) ≤ φ m - φ (c n) :=
          (le_div_iff₀ hmcn_pos).mp hslope
        have hval : φₙ n a = φ (c n) + R (c n) * (a - c n) := by
          simp only [hφₙ_def]
          exact affineTrunc_of_lt (hac n)
        rw [hval, hL_def]
        simp only
        have hYle : R (c n) * (c n - a) ≤ (φ m - φ (c n)) * (c n - a) / (m - c n) := by
          rw [le_div_iff₀ hmcn_pos]
          nlinarith [mul_le_mul_of_nonneg_right hslope_clr hcx_pos]
        linarith [hYle]
      have hcont_a : Tendsto (fun n => φ (c n)) atTop (𝓝 (φ a)) := by
        have hcwa : ContinuousWithinAt φ (Icc a b) a := hcont a hx
        have hc_in : Tendsto c atTop (𝓝[Icc a b] a) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨hca, Filter.Eventually.of_forall fun n =>
            ⟨(hac n).le, (lt_trans (hcd n) (hdb n)).le⟩⟩
        exact hcwa.tendsto.comp hc_in
      have hL_lim : Tendsto L atTop (𝓝 (φ a)) := by
        have hnum : Tendsto (fun n => (φ m - φ (c n)) * (c n - a)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun n => φ m - φ (c n)) atTop (𝓝 (φ m - φ a)) :=
            tendsto_const_nhds.sub hcont_a
          have h2 : Tendsto (fun n => c n - a) atTop (𝓝 0) := by
            have := hca.sub_const a; simpa using this
          have := h1.mul h2; simpa using this
        have hden2 : Tendsto (fun n => m - c n) atTop (𝓝 (m - a)) :=
          tendsto_const_nhds.sub hca
        have hquot : Tendsto (fun n => (φ m - φ (c n)) * (c n - a) / (m - c n)) atTop (𝓝 0) := by
          have hmx : m - a ≠ 0 := by have := hmem_m.1; linarith
          have := hnum.div hden2 hmx
          simpa using this
        have := hcont_a.sub hquot
        simpa [hL_def] using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL_lim
        (tendsto_const_nhds) (Filter.Eventually.of_forall hlb) (Filter.Eventually.of_forall hub)
    rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · -- x = b: symmetric to x = a (subst eliminates b, keeping x = old b)
      subst hxb
      have hub : ∀ n, φₙ n x ≤ φ x :=
        fun n => affineTrunc_le hφ (hac n) (hcd n) (hdb n) hx
      set L : ℕ → ℝ := fun n => φ (d n) - (φ m - φ (d n)) * (x - d n) / (d n - m) with hL_def
      have hlb : ∀ n, L n ≤ φₙ n x := by
        intro n
        have hdnI : d n ∈ Ioo a x := ⟨lt_trans (hac n) (hcd n), hdb n⟩
        have hsl : slope φ m (d n) ≤ R (d n) := by
          have h1 : slope φ m (d n) ≤ derivWithin φ (Iio (d n)) (d n) :=
            hφ.slope_le_leftDeriv_of_mem_interior ⟨hmem_m.1.le, hmem_m.2.le⟩
              (by rw [interior_Icc]; exact hdnI) (hmd n)
          exact le_trans h1 (hφ.leftDeriv_le_rightDeriv_of_mem_interior
            (by rw [interior_Icc]; exact hdnI))
        have hslope_eq : slope φ m (d n) = (φ (d n) - φ m) / (d n - m) := by rw [slope_def_field]
        rw [hslope_eq] at hsl
        have hxd_pos : (0:ℝ) ≤ x - d n := by have := hdb n; linarith
        have hdm_pos : (0:ℝ) < d n - m := by have := hmd n; linarith
        have hsl_clr : φ (d n) - φ m ≤ R (d n) * (d n - m) :=
          (div_le_iff₀ hdm_pos).mp hsl
        have hval : φₙ n x = φ (d n) + R (d n) * (x - d n) := by
          simp only [hφₙ_def]
          exact affineTrunc_of_gt (hcd n).le (hdb n)
        rw [hval, hL_def]
        simp only
        have hYle : (φ m - φ (d n)) * (x - d n) / (d n - m) ≥ - (R (d n) * (x - d n)) := by
          rw [ge_iff_le, le_div_iff₀ hdm_pos]
          nlinarith [mul_le_mul_of_nonneg_right hsl_clr hxd_pos]
        linarith [hYle]
      have hcont_b : Tendsto (fun n => φ (d n)) atTop (𝓝 (φ x)) := by
        have hcwa : ContinuousWithinAt φ (Icc a x) x := hcont x hx
        have hd_in : Tendsto d atTop (𝓝[Icc a x] x) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨hdb_lim, Filter.Eventually.of_forall fun n =>
            ⟨(lt_trans (hac n) (hcd n)).le, (hdb n).le⟩⟩
        exact hcwa.tendsto.comp hd_in
      have hL_lim : Tendsto L atTop (𝓝 (φ x)) := by
        have hnum : Tendsto (fun n => (φ m - φ (d n)) * (x - d n)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun n => φ m - φ (d n)) atTop (𝓝 (φ m - φ x)) :=
            tendsto_const_nhds.sub hcont_b
          have h2 : Tendsto (fun n => x - d n) atTop (𝓝 0) := by
            have := (tendsto_const_nhds (x := x)).sub hdb_lim; simpa using this
          have := h1.mul h2; simpa using this
        have hden2 : Tendsto (fun n => d n - m) atTop (𝓝 (x - m)) :=
          hdb_lim.sub_const m
        have hquot : Tendsto (fun n => (φ m - φ (d n)) * (x - d n) / (d n - m)) atTop (𝓝 0) := by
          have hbm : x - m ≠ 0 := by have := hmem_m.2; linarith
          have := hnum.div hden2 hbm
          simpa using this
        have := hcont_b.sub hquot
        simpa [hL_def] using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL_lim
        (tendsto_const_nhds) (Filter.Eventually.of_forall hlb) (Filter.Eventually.of_forall hub)
    · -- a < x < b: eventually φₙ n x = φ x once [c n, d n] swallows x
      have heq : ∀ᶠ n in atTop, φₙ n x = φ x := by
        have hcx : ∀ᶠ n in atTop, c n < x := hca.eventually (eventually_lt_nhds hax)
        have hxd : ∀ᶠ n in atTop, x < d n := hdb_lim.eventually (eventually_gt_nhds hxb)
        filter_upwards [hcx, hxd] with n hcn hdn
        simp only [hφₙ_def]
        exact affineTrunc_of_mem hcn.le hdn.le
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [heq] with n h
      exact h.symm

end ConvexOn

end
