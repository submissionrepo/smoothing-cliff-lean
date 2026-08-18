/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Brouwer

/-!
# Schauder fixed-point theorem

Every continuous self-map of a nonempty compact convex subset of a normed space (not necessarily
finite-dimensional) has a fixed point.

## Main definitions

* `schauderWeight` — the distance-based bump weight `max(0, ε - ‖y - c‖)`
* `schauderProjection` — the weighted average of finitely many centers approximating a point

## Main statements

* `brouwer_convexHull_finset` — Brouwer's fixed-point theorem for the convex hull of a finite set
* `approxFixedPoint_schauder` — existence of `ε`-approximate fixed points on a compact convex set
* `schauderFixedPoint` — Schauder's fixed-point theorem in a normed space

## Tags

schauder, fixed point, projection
-/

@[expose] public section

open Filter Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Schauder weights -/

/-- The Schauder bump weight: `max(0, ε - ‖y - c‖)`. Positive exactly when `y ∈ ball c ε`. -/
noncomputable def schauderWeight (ε : ℝ) (c y : E) : ℝ := max 0 (ε - ‖y - c‖)

omit [NormedSpace ℝ E] in
lemma schauderWeight_nonneg (ε : ℝ) (c y : E) : 0 ≤ schauderWeight ε c y :=
  le_max_left 0 _

omit [NormedSpace ℝ E] in
lemma schauderWeight_pos_of_mem_ball {ε : ℝ} {c y : E} (h : y ∈ Metric.ball c ε) :
    0 < schauderWeight ε c y := by
  simp only [schauderWeight, lt_max_iff]
  -- ε - ‖y - c‖ > 0 ⟺ ‖y - c‖ < ε ⟺ dist y c < ε, which is `mem_ball`
  right
  rw [sub_pos, ← dist_eq_norm]
  exact Metric.mem_ball.mp h

omit [NormedSpace ℝ E] in
lemma schauderWeight_eq_zero_of_not_mem_ball {ε : ℝ} {c y : E}
    (h : y ∉ Metric.ball c ε) : schauderWeight ε c y = 0 := by
  simp only [schauderWeight, max_eq_left_iff, sub_nonpos]
  rw [Metric.mem_ball, not_lt, dist_eq_norm] at h
  exact h

omit [NormedSpace ℝ E] in
lemma continuous_schauderWeight (ε : ℝ) (c : E) : Continuous (schauderWeight ε c) := by
  unfold schauderWeight
  exact continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)

/-! ### Schauder projection -/

omit [NormedSpace ℝ E] in
/-- The sum of Schauder weights is positive for any point covered by the balls. -/
lemma schauderWeight_sum_pos {ε : ℝ} {t : Finset E} {y : E}
    (hcover : y ∈ ⋃ c ∈ t, Metric.ball c ε) :
    0 < ∑ c ∈ t, schauderWeight ε c y := by
  rw [Set.mem_iUnion₂] at hcover
  obtain ⟨c, hct, hcy⟩ := hcover
  exact Finset.sum_pos' (fun i _ => schauderWeight_nonneg ε i y)
    ⟨c, hct, schauderWeight_pos_of_mem_ball hcy⟩

/-- The Schauder projection: A weighted average of the centers `c ∈ t`, with weights
`max(0, ε - ‖y - c‖)`. Maps any covered point into `convexHull ℝ ↑t`. -/
noncomputable def schauderProjection (ε : ℝ) (t : Finset E) (y : E) : E :=
  t.centerMass (fun c => schauderWeight ε c y) id

/-- The Schauder projection lies in the convex hull of the centers. -/
lemma schauderProjection_mem_convexHull {ε : ℝ} {t : Finset E} {y : E}
    (hcover : y ∈ ⋃ c ∈ t, Metric.ball c ε) :
    schauderProjection ε t y ∈ convexHull ℝ (↑t : Set E) :=
  Finset.centerMass_id_mem_convexHull t
    (fun c _ => schauderWeight_nonneg ε c y) (schauderWeight_sum_pos hcover)

/-- The Schauder projection is within ε of the original point. -/
-- `hε` is kept in the signature to match `schauderProjection_mem_convexHull` and callers'
-- expectations, though the proof only needs `hcover` (positivity is implicit in the ball cover).
lemma schauderProjection_dist {ε : ℝ} (_hε : 0 < ε) {t : Finset E} {y : E}
    (hcover : y ∈ ⋃ c ∈ t, Metric.ball c ε) :
    ‖schauderProjection ε t y - y‖ < ε := by
  -- p(y) is a convex combination of cᵢ's within ε of y
  -- ‖p(y) - y‖ = ‖∑ αᵢ(cᵢ - y)‖ ≤ ∑ αᵢ‖cᵢ - y‖ < ∑ αᵢ · ε = ε
  have hS := schauderWeight_sum_pos hcover
  have hS_inv_pos : 0 < (∑ c ∈ t, schauderWeight ε c y)⁻¹ :=
    inv_pos.mpr hS
  -- The normalized weights αᵢ = wᵢ / S
  let α (c : E) := (∑ c ∈ t, schauderWeight ε c y)⁻¹ * schauderWeight ε c y
  have hα_nonneg : ∀ c ∈ t, 0 ≤ α c :=
    fun c _ => mul_nonneg (le_of_lt hS_inv_pos) (schauderWeight_nonneg ε c y)
  have hα_sum : ∑ c ∈ t, α c = 1 := by
    simp only [α, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hS)
  -- p(y) = ∑ αᵢ cᵢ
  have hpy : schauderProjection ε t y = ∑ c ∈ t, α c • c := by
    simp only [schauderProjection, Finset.centerMass, α]
    rw [Finset.smul_sum]
    congr 1
    ext c
    rw [mul_smul, id]
  -- p(y) - y = ∑ αᵢ (cᵢ - y)
  have hpy_sub : schauderProjection ε t y - y = ∑ c ∈ t, α c • (c - y) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hα_sum, one_smul, hpy]
  rw [hpy_sub]
  calc ‖∑ c ∈ t, α c • (c - y)‖
      ≤ ∑ c ∈ t, ‖α c • (c - y)‖ := norm_sum_le t _
    _ = ∑ c ∈ t, α c * ‖c - y‖ := by
        apply Finset.sum_congr rfl; intro c hc
        rw [norm_smul, Real.norm_of_nonneg (hα_nonneg c hc)]
    _ < ∑ c ∈ t, α c * ε := by
        apply Finset.sum_lt_sum
        · intro c hc
          by_cases hw : schauderWeight ε c y = 0
          · have hα0 : α c = 0 := by simp only [α, hw, mul_zero]
            rw [hα0, zero_mul, zero_mul]
          · apply mul_le_mul_of_nonneg_left _ (hα_nonneg c hc)
            have hcb : y ∈ Metric.ball c ε := by
              by_contra h; exact hw (schauderWeight_eq_zero_of_not_mem_ball h)
            rw [Metric.mem_ball', dist_eq_norm] at hcb
            exact le_of_lt hcb
        · -- At least one center has y in its ball with positive weight
          rw [Set.mem_iUnion₂] at hcover
          obtain ⟨c₀, hc₀t, hc₀y⟩ := hcover
          exact ⟨c₀, hc₀t, by
            apply mul_lt_mul_of_pos_left _ (by
              simp only [α]; exact mul_pos hS_inv_pos (schauderWeight_pos_of_mem_ball hc₀y))
            rw [Metric.mem_ball', dist_eq_norm] at hc₀y
            exact hc₀y⟩
    _ = ε := by rw [← Finset.sum_mul, hα_sum, one_mul]

/-- The Schauder projection is continuous on any set covered by the balls. -/
-- `hε` is kept in the signature for symmetry with `schauderProjection_dist`, though continuity
-- here follows from `hcover` alone.
lemma continuousOn_schauderProjection {ε : ℝ} (_hε : 0 < ε) {t : Finset E}
    {K : Set E} (hcover : K ⊆ ⋃ c ∈ t, Metric.ball c ε) :
    ContinuousOn (schauderProjection ε t) K := by
  -- centerMass = S⁻¹ • ∑ wᵢ • cᵢ where S = ∑ wᵢ is continuous and positive on K
  unfold schauderProjection Finset.centerMass
  apply ContinuousOn.smul
  · apply ContinuousOn.inv₀
    · exact continuousOn_finset_sum t fun c _ =>
        (continuous_schauderWeight ε c).continuousOn
    · intro y hy
      exact ne_of_gt (schauderWeight_sum_pos (hcover hy))
  · exact continuousOn_finset_sum t fun c _ =>
      ((continuous_schauderWeight ε c).continuousOn.smul continuousOn_const)

/-! ### Brouwer on finite convex hulls -/

/-- **Brouwer's fixed-point theorem for a finite convex hull**: Any continuous self-map of the
convex hull of a nonempty finite set in a normed space has a fixed point. -/
theorem brouwer_convexHull_finset
    (t : Finset E) (ht : t.Nonempty)
    (f : C(convexHull ℝ (↑t : Set E), convexHull ℝ (↑t : Set E))) :
    ∃ x, f x = x := by
  -- Pick x₀ ∈ t. Let W = span{tᵢ - x₀}, finite-dimensional.
  -- D = {w ∈ W | w + x₀ ∈ convexHull ↑t} is compact convex nonempty in W.
  -- g(w) = f(w + x₀) - x₀ is a continuous self-map of D; Brouwer gives a fixed point.
  obtain ⟨x₀, hx₀⟩ := ht
  let W := Submodule.span ℝ ((· - x₀) '' (↑t : Set E))
  haveI : FiniteDimensional ℝ W :=
    FiniteDimensional.span_of_finite ℝ (t.finite_toSet.image (· - x₀))
  haveI : ProperSpace W := FiniteDimensional.proper_real W
  let C := convexHull ℝ (↑t : Set E)
  have hC_compact : IsCompact C := t.finite_toSet.isCompact_convexHull ℝ
  have hC_convex : Convex ℝ C := convex_convexHull ℝ _
  have hmem_W : ∀ x ∈ C, x - x₀ ∈ (W : Set E) := by
    intro x hx
    -- x is in convexHull ℝ ↑t. The map (· - x₀) sends ↑t into W,
    -- and W is convex, so the image of the convex hull is in W.
    have hsub : (· - x₀) '' (↑t : Set E) ⊆ (W : Set E) := by
      rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span (Set.mem_image_of_mem _ hz)
    -- x - x₀ ∈ convexHull ℝ ((· - x₀) '' ↑t) ⊆ W
    have hx_shifted : x - x₀ ∈ convexHull ℝ ((· - x₀) '' (↑t : Set E)) := by
      let τ : E →ᵃ[ℝ] E := AffineMap.id ℝ E - AffineMap.const ℝ E x₀
      have : (· - x₀) = τ := rfl
      rw [this, ← AffineMap.image_convexHull]
      exact Set.mem_image_of_mem τ hx
    exact convexHull_min hsub W.convex hx_shifted
  -- D ⊆ W: the translated C
  let φ : W → E := fun w => (w : E) + x₀
  have hφ : Continuous φ := continuous_subtype_val.add continuous_const
  let D : Set W := φ ⁻¹' C
  have hD_closed : IsClosed D := hC_compact.isClosed.preimage hφ
  have hD_bounded : Bornology.IsBounded D := by
    rw [Metric.isBounded_iff_subset_ball 0]
    obtain ⟨R, hR⟩ := hC_compact.isBounded.subset_ball x₀
    refine ⟨R, fun w hw => ?_⟩
    have hφw : φ w ∈ Metric.ball x₀ R := hR hw
    rw [Metric.mem_ball] at hφw
    -- dist w 0 = ‖w‖ = dist (w + x₀) x₀ = dist (φ w) x₀ < R, via translation invariance
    calc dist w 0 = dist ((w : E) + x₀) x₀ := by
          rw [Subtype.dist_eq, Submodule.coe_zero, ← dist_add_right (w : E) 0 x₀, zero_add]
      _ < R := hφw
  have hD_compact : IsCompact D :=
    Metric.isCompact_of_isClosed_isBounded hD_closed hD_bounded
  have hD_convex : Convex ℝ D := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    change (↑(a • w₁ + b • w₂) : E) + x₀ ∈ C
    have : (↑(a • w₁ + b • w₂) : E) + x₀ =
        a • ((w₁ : E) + x₀) + b • ((w₂ : E) + x₀) := by
      simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
      rw [show a • (w₁ : E) + a • x₀ + (b • (w₂ : E) + b • x₀) =
        a • (w₁ : E) + b • (w₂ : E) + (a • x₀ + b • x₀) from by abel]
      rw [← add_smul, hab, one_smul]
    rw [this]
    exact hC_convex hw₁ hw₂ ha hb hab
  have hD_ne : D.Nonempty := by
    exact ⟨⟨0, Submodule.zero_mem W⟩, by
      change (0 : E) + x₀ ∈ C
      simp only [zero_add]
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hx₀)⟩
  -- Build g : D → D, the conjugate of f
  let g : D → D := fun ⟨w, hw⟩ =>
    ⟨⟨(f ⟨φ w, hw⟩ : E) - x₀, hmem_W _ (f ⟨φ w, hw⟩).2⟩,
     by
       change (f ⟨φ w, hw⟩ : E) - x₀ + x₀ ∈ C
       simpa only [sub_add_cancel] using (f ⟨φ w, hw⟩).2⟩
  have hg_cont : Continuous g := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    -- Need: Continuous (fun (d : D) => (f ⟨φ d, d.2⟩ : E) - x₀)
    -- This is (Subtype.val ∘ f ∘ (fun d => ⟨φ d, d.2⟩)) - const x₀
    -- The map d ↦ ⟨φ d, d.2⟩ : D → C is continuous (φ restricted to D lands in C by definition)
    -- d ↦ φ(d) : D → E is continuous
    have h1 : Continuous (fun d : D => φ (d : W)) := hφ.comp continuous_subtype_val
    -- d ↦ ⟨φ(d), d.2⟩ : D → C is continuous
    have h2 : Continuous (fun d : D => (⟨φ (d : W), d.2⟩ : C)) :=
      h1.subtype_mk _
    -- d ↦ f(⟨φ(d), d.2⟩) : D → C is continuous
    have h3 : Continuous (fun d : D => f (⟨φ (d : W), d.2⟩ : C)) :=
      f.continuous.comp h2
    -- d ↦ (f(⟨φ(d), d.2⟩) : E) - x₀ : D → E is continuous
    exact (continuous_subtype_val.comp h3).sub continuous_const
  obtain ⟨⟨w, hw⟩, hfp⟩ := brouwerFixedPoint D hD_convex hD_compact hD_ne ⟨g, hg_cont⟩
  -- g(w) = w means f(w + x₀) - x₀ = w, so f(w + x₀) = w + x₀
  use ⟨φ w, hw⟩
  apply Subtype.ext
  -- Need: (f ⟨φ w, hw⟩ : E) = φ w, i.e., f(w + x₀) = w + x₀
  -- From hfp: g(w) = w, which gives f(φ w) - x₀ = w (as elements of W)
  have h1 : (f ⟨φ w, hw⟩ : E) - x₀ = (w : E) :=
    Subtype.ext_iff.mp (Subtype.ext_iff.mp hfp)
  rwa [sub_eq_iff_eq_add] at h1

/-! ### Approximate fixed points -/

/-- For each `ε > 0`, a continuous self-map of a compact convex set has an `ε`-approximate fixed
point. -/
lemma approxFixedPoint_schauder
    {K : Set E} (hcvx : Convex ℝ K) (hcmpct : IsCompact K) (hne : K.Nonempty)
    (f : C(K, K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : K, ‖(f x : E) - (x : E)‖ < ε := by
  -- Get finite ε-cover from compactness
  obtain ⟨t_set, ht_sub, ht_fin, ht_cover⟩ := finite_cover_balls_of_compact hcmpct hε
  let t := ht_fin.toFinset
  have ht_coe : (↑t : Set E) = t_set := Set.Finite.coe_toFinset ht_fin
  have ht_ne : t.Nonempty := by
    -- a point of K is covered by some ball centered in t_set = ↑t, so t is nonempty
    rw [← Finset.coe_nonempty, ht_coe]
    obtain ⟨x, hx⟩ := hne
    obtain ⟨c, hc, -⟩ := Set.mem_iUnion₂.mp (ht_cover hx)
    exact ⟨c, hc⟩
  have ht_sub' : (↑t : Set E) ⊆ K := by rw [ht_coe]; exact ht_sub
  have hC_sub : convexHull ℝ (↑t : Set E) ⊆ K := convexHull_min ht_sub' hcvx
  have ht_cover' : K ⊆ ⋃ c ∈ t, Metric.ball c ε := by
    intro x hx
    have := ht_cover hx
    simp only [Set.mem_iUnion] at this ⊢
    obtain ⟨c, hc, hcx⟩ := this
    exact ⟨c, (Set.Finite.mem_toFinset ht_fin).mpr hc, hcx⟩
  -- Build g : convexHull ↑t → convexHull ↑t by g(x) = p(f(x))
  -- where p is the Schauder projection
  let C := convexHull ℝ (↑t : Set E)
  -- For any x ∈ K, f(x) ∈ K, so f(x) is covered, so p(f(x)) ∈ C
  have hfx_cover : ∀ x : K, (f x : E) ∈ ⋃ c ∈ t, Metric.ball c ε :=
    fun x => ht_cover' (f x).2
  let g : C → C := fun ⟨x, hx⟩ =>
    let x' : K := ⟨x, hC_sub hx⟩
    ⟨schauderProjection ε t (f x' : E),
     schauderProjection_mem_convexHull (hfx_cover x')⟩
  have hg_cont : Continuous g := by
    apply Continuous.subtype_mk
    -- schauderProjection ε t ∘ (Subtype.val ∘ f ∘ inclusion) is continuous
    -- The inclusion C ↪ K is continuous, f is continuous, Subtype.val is continuous,
    -- and schauderProjection is continuous on K (which is covered by the balls)
    have h_incl : Continuous (fun x : C => (⟨(x : E), hC_sub x.2⟩ : K)) :=
      continuous_subtype_val.subtype_mk _
    have h_fval : Continuous (fun x : C => (f ⟨(x : E), hC_sub x.2⟩ : E)) :=
      continuous_subtype_val.comp (f.continuous.comp h_incl)
    exact (continuousOn_schauderProjection hε ht_cover').comp_continuous h_fval
      (fun x => (f ⟨(x : E), hC_sub x.2⟩).2)
  obtain ⟨⟨x, hx⟩, hfp⟩ := brouwer_convexHull_finset t ht_ne ⟨g, hg_cont⟩
  -- x₀ is a fixed point of g, meaning p(f(x₀)) = x₀
  -- So ‖f(x₀) - x₀‖ = ‖f(x₀) - p(f(x₀))‖ < ε
  use ⟨x, hC_sub hx⟩
  have hfp_val : schauderProjection ε t (f ⟨x, hC_sub hx⟩ : E) = x :=
    congr_arg Subtype.val hfp
  -- ‖f(x) - x‖ = ‖f(x) - p(f(x))‖ < ε
  change ‖(f ⟨x, hC_sub hx⟩ : E) - x‖ < ε
  calc ‖(f ⟨x, hC_sub hx⟩ : E) - x‖
      = ‖(f ⟨x, hC_sub hx⟩ : E) - schauderProjection ε t (f ⟨x, hC_sub hx⟩ : E)‖ := by
        rw [hfp_val]
    _ = ‖schauderProjection ε t (f ⟨x, hC_sub hx⟩ : E) - (f ⟨x, hC_sub hx⟩ : E)‖ :=
        norm_sub_rev _ _
    _ < ε := schauderProjection_dist hε (hfx_cover ⟨x, hC_sub hx⟩)

/-! ### Main theorem -/

/-- **Schauder Fixed-Point Theorem**: Every continuous function mapping a nonempty compact convex
subset of a normed space to itself has a fixed point. -/
theorem schauderFixedPoint
    (K : Set E) (hcvx : Convex ℝ K) (hcmpct : IsCompact K) (hne : K.Nonempty)
    (f : C(K, K)) : ∃ x, f x = x := by
  -- Get ε-approximate fixed points for ε = 1/(n+1)
  choose x hx using fun n : ℕ =>
    approxFixedPoint_schauder hcvx hcmpct hne f (1 / (↑n + 1)) (Nat.one_div_pos_of_nat)
  -- Extract cluster point via ultrafilter
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : ↑u ≤ (atTop : Filter ℕ) := Ultrafilter.of_le atTop
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcmpct
  obtain ⟨x_star, -, hx_lim⟩ :=
    isCompact_univ.ultrafilter_le_nhds (u.map x) (by simp)
  use x_star
  -- xₙ → x* in E
  have h_lim_x : Tendsto (fun n => (x n : E)) u (nhds (x_star : E)) :=
    continuous_subtype_val.tendsto x_star |>.comp hx_lim
  -- dist(f(xₙ), xₙ) → 0
  have h_dist_zero : Tendsto (fun n => dist (x n : E) (f (x n) : E)) u (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hu
    · exact Eventually.of_forall fun n => dist_nonneg
    · exact Eventually.of_forall fun n => by
        rw [dist_eq_norm, norm_sub_rev]; exact le_of_lt (hx n)
  -- f(xₙ) → x*
  have h_lim_fx : Tendsto (fun n => (f (x n) : E)) u (nhds (x_star : E)) :=
    tendsto_of_tendsto_of_dist h_lim_x h_dist_zero
  -- f(xₙ) → f(x*) by continuity
  have h_lim_fx' : Tendsto (fun n => (f (x n) : E)) u (nhds (f x_star : E)) :=
    (continuous_subtype_val.comp f.continuous).tendsto x_star |>.comp hx_lim
  exact Subtype.ext (tendsto_nhds_unique h_lim_fx' h_lim_fx)
