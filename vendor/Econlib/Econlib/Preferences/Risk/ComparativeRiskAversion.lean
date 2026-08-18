/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Risk.ArrowPratt
public import Econlib.Preferences.Risk.CertaintyEquivalent

open Set Filter Topology

/-!
# Comparative risk aversion

This file develops Pratt's comparison of risk aversion across agents. One agent is **more risk
averse** than another on a shared domain when its utility is an increasing concave transform of the
other's. For twice-differentiable utilities this is characterized by a pointwise ordering of the
Arrow–Pratt absolute coefficients, and it implies a lower certainty equivalent for any lottery
whose outcomes lie in the shared domain, given certainty-equivalent witnesses for both agents that
also lie in the domain.

## Main definitions

* `MoreRiskAverseOn` — `u` is an increasing concave transform of `v` on a domain.

## Main statements

* `more_risk_averse_iff_absoluteRiskAversion_ge` — being more risk averse is equivalent to a
  pointwise-larger Arrow–Pratt absolute coefficient (Pratt 1964).
* `MoreRiskAverseOn.le_certaintyEquivalent` — for a lottery valued in the shared domain, with
  certainty-equivalent witnesses for both agents lying in the domain, the more risk-averse agent's
  certainty equivalent is at or below that of the less risk-averse agent.
* `concaveOn_iff_second_deriv_nonpos` — on an open convex set, a twice-differentiable function is
  concave iff its second derivative is nonpositive.

## References

* Pratt, John W. 1964. “Risk Aversion in the Small and in the Large.” *Econometrica* 32 (1/2): 122.
  [https://doi.org/10.2307/1913738](https://doi.org/10.2307/1913738).

## Tags

comparative risk aversion, concave transform, arrow-pratt, certainty equivalent
-/

@[expose] public section

namespace Econlib.Preferences

/-- If `Set.EqOn f.u (g ∘ v.u) v.domain` and `v.u` has a twice-differentiable inverse, then `g` is
twice differentiable on the image `v.u '' v.domain`, with first and second derivatives supplied
existentially. -/
lemma transformation_twice_diff (f v : TwiceDiffUtility)
    (h_same_domain : f.domain = v.domain)
    (g : ℝ → ℝ)
    (hg_eq : Set.EqOn f.u (g ∘ v.u) v.domain) :
    ∃ g' g'' : ℝ → ℝ,
      (∀ y ∈ v.u '' v.domain, HasDerivAt g (g' y) y) ∧
      (∀ y ∈ v.u '' v.domain, HasDerivAt g' (g'' y) y) := by
  obtain ⟨v_inv, v_inv', v_inv'', hv_left, hv_right, hv_deriv₁, hv_deriv₂⟩ :=
    v.exists_inverse_twice_diff
  have hg_eq_comp : ∀ y ∈ v.u '' v.domain, g y = f.u (v_inv y) := by
    rintro y ⟨x, hx, rfl⟩
    rw [hv_left x hx]; exact (hg_eq hx).symm
  have hg_ev : ∀ y ∈ v.u '' v.domain, g =ᶠ[nhds y] fun z => f.u (v_inv z) := by
    intro y hy
    exact (v.image_domain_open.eventually_mem hy).mono (fun z hz => hg_eq_comp z hz)
  have hv_inv_mem : ∀ y ∈ v.u '' v.domain, v_inv y ∈ f.domain := by
    rintro y ⟨x, hx, rfl⟩; rw [hv_left x hx, h_same_domain]; exact hx
  set g' := fun y => f.u' (v_inv y) * v_inv' y
  set g'' := fun y => f.u'' (v_inv y) * v_inv' y * v_inv' y + f.u' (v_inv y) * v_inv'' y
  refine ⟨g', g'', ?_, ?_⟩
  · intro y hy
    have h_comp : HasDerivAt (fun z => f.u (v_inv z)) (f.u' (v_inv y) * v_inv' y) y :=
      (f.has_deriv _ (hv_inv_mem y hy)).comp y (hv_deriv₁ y hy)
    exact h_comp.congr_of_eventuallyEq (hg_ev y hy)
  · intro y hy
    have h_chain_u' : HasDerivAt (fun z => f.u' (v_inv z)) (f.u'' (v_inv y) * v_inv' y) y :=
      (f.has_second_deriv _ (hv_inv_mem y hy)).comp y (hv_deriv₁ y hy)
    exact h_chain_u'.mul (hv_deriv₂ y hy)

/-! ### Second-derivative characterization of concavity on open convex sets -/

/-- If `g'` is antitone on an open set and has pointwise derivative `g''`, then `g'' ≤ 0`. -/
lemma deriv_nonpos_of_antitoneOn {s : Set ℝ} (hs_open : IsOpen s)
    {g' g'' : ℝ → ℝ} (h_anti : AntitoneOn g' s)
    (hg'' : ∀ x ∈ s, HasDerivAt g' (g'' x) x)
    {x : ℝ} (hx : x ∈ s) : g'' x ≤ 0 := by
  have h_tendsto_pos : Filter.Tendsto (fun t => t⁻¹ • (g' (x + t) - g' x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g'' x)) :=
    (hg'' x hx).tendsto_slope_zero.mono_left
      (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs_open x hx
  apply le_of_tendsto h_tendsto_pos
  apply Filter.Eventually.mono (Ioo_mem_nhdsGT hε)
  intro t ⟨ht_pos, ht_lt⟩
  have hxt : x + t ∈ s :=
    hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  simp only [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr ht_pos))
    (by linarith [h_anti hx hxt (by linarith : x ≤ x + t)])

/-- On an open convex set, a twice-differentiable function is concave if and only if its second
derivative is nonpositive everywhere on that set. -/
lemma concaveOn_iff_second_deriv_nonpos
    {s : Set ℝ} (hs_open : IsOpen s) (hs_convex : Convex ℝ s)
    {g g' g'' : ℝ → ℝ}
    (hg' : ∀ x ∈ s, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ s, HasDerivAt g' (g'' x) x) :
    ConcaveOn ℝ s g ↔ ∀ x ∈ s, g'' x ≤ 0 := by
  have hg_diff : DifferentiableOn ℝ g s :=
    fun x hx => (hg' x hx).differentiableAt.differentiableWithinAt
  have h_deriv_eq : ∀ x ∈ s, deriv g x = g' x :=
    fun x hx => (hg' x hx).deriv
  have hg'_diff : DifferentiableOn ℝ g' s :=
    fun x hx => (hg'' x hx).differentiableAt.differentiableWithinAt
  have h_deriv_g_diff : DifferentiableOn ℝ (deriv g) s :=
    hg'_diff.congr (fun x hx => h_deriv_eq x hx)
  have h_deriv2_eq : ∀ x ∈ s, deriv^[2] g x = g'' x := by
    intro x hx
    change deriv (deriv g) x = g'' x
    rw [Filter.EventuallyEq.deriv_eq
      ((hs_open.eventually_mem hx).mono (fun y hy => h_deriv_eq y hy))]
    exact (hg'' x hx).deriv
  constructor
  · intro hconc x hx
    have h_anti : AntitoneOn (derivWithin g s) s :=
      hconc.antitoneOn_derivWithin hg_diff
    have h_anti_g' : AntitoneOn g' s := by
      intro a ha b hb hab
      have := h_anti ha hb hab
      rwa [derivWithin_of_isOpen hs_open ha, derivWithin_of_isOpen hs_open hb,
           h_deriv_eq a ha, h_deriv_eq b hb] at this
    exact deriv_nonpos_of_antitoneOn hs_open h_anti_g' hg'' hx
  · intro h_nonpos
    exact concaveOn_of_deriv2_nonpos' hs_convex hg_diff h_deriv_g_diff
      (fun x hx => (h_deriv2_eq x hx).symm ▸ h_nonpos x hx)

/-- Agent with utility `u` is more risk averse than agent with utility `v` on domain `D` if
`u = g ∘ v` on `D` for some function `g` that is strictly increasing and concave on the image of
`D`. The monotonicity clause is part of Pratt's definition: Without it a decreasing concave `g`
(e.g. an affine `g y = -y`) would reverse preferences over sure outcomes while still satisfying the
concavity clause, so dropping it would classify a preference-reversing agent as more risk averse. -/
def MoreRiskAverseOn (u v : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∃ g : ℝ → ℝ, StrictMonoOn g (v '' D) ∧ ConcaveOn ℝ (v '' D) g ∧ Set.EqOn u (g ∘ v) D

/-- On the shared open domain, `f.u'` agrees with `fun y => t'(v.u y) * v.u' y` in a neighborhood
of every point. -/
lemma first_deriv_eq_nhds (f v : TwiceDiffUtility) (t t' : ℝ → ℝ)
    (x : ℝ) (hx_f : x ∈ f.domain)
    (ht_comp : Set.EqOn f.u (t ∘ v.u) v.domain)
    (h_t_deriv : ∀ y ∈ v.u '' v.domain, HasDerivAt t (t' y) y)
    (h_same_domain : f.domain = v.domain) :
    f.u' =ᶠ[nhds x] fun y => t' (v.u y) * v.u' y := by
  have h_mem : f.domain ∈ nhds x := f.domain_open.mem_nhds hx_f
  exact Filter.Eventually.mono h_mem fun y hy => by
    have hy_v : y ∈ v.domain := h_same_domain ▸ hy
    have hd_f : HasDerivAt f.u (f.u' y) y := f.has_deriv y hy
    have hd_comp : HasDerivAt (t ∘ v.u) (t' (v.u y) * v.u' y) y :=
      HasDerivAt.comp y
      (h_t_deriv (v.u y) (mem_image_of_mem v.u hy_v))
      (v.has_deriv y hy_v)
    have hd_f_alt : HasDerivAt f.u (t' (v.u y) * v.u' y) y :=
      hd_comp.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (v.domain_open.mem_nhds hy_v) ht_comp)
    exact hd_f.unique hd_f_alt

/-- Second derivative chain rule: `f.u'' x = t''(v x)·(v' x)² + t'(v x)·v'' x`. -/
lemma second_deriv_chain_rule (f v : TwiceDiffUtility) (t t' t'' : ℝ → ℝ)
    (x : ℝ) (hx_f : x ∈ f.domain) (hx_v : x ∈ v.domain)
    (h_t_derivs : ∀ y ∈ v.u '' v.domain, HasDerivAt t (t' y) y ∧ HasDerivAt t' (t'' y) y)
    (h_eq_nhds : f.u' =ᶠ[nhds x] fun y => t' (v.u y) * v.u' y) :
    f.u'' x = t'' (v.u x) * (v.u' x) ^ 2 + t' (v.u x) * v.u'' x := by
  have hd_f'' : HasDerivAt f.u' (f.u'' x) x := f.has_second_deriv x hx_f
  have hd_comp_t' : HasDerivAt (t' ∘ v.u) (t'' (v.u x) * v.u' x) x :=
    HasDerivAt.comp x
    (h_t_derivs (v.u x) (mem_image_of_mem v.u hx_v)).2
    (v.has_deriv x hx_v)
  have hd_prod : HasDerivAt (fun y => t' (v.u y) * v.u' y)
      (t'' (v.u x) * v.u' x * v.u' x + t' (v.u x) * v.u'' x) x :=
    HasDerivAt.mul hd_comp_t' (v.has_second_deriv x hx_v)
  have hd_alt : HasDerivAt f.u'
      (t'' (v.u x) * v.u' x * v.u' x + t' (v.u x) * v.u'' x) x :=
    hd_prod.congr_of_eventuallyEq h_eq_nhds
  rw [hd_f''.unique hd_alt]; ring

/-- Given `f.u = t ∘ v.u` on the shared domain, the absolute risk aversion difference at `x` equals
`-(t''(v x) · v'(x)) / t'(v x)`, and `t'(v x) > 0`. -/
lemma absoluteRiskAversion_diff_eq (f v : TwiceDiffUtility)
    (h_same_domain : f.domain = v.domain)
    (t t' t'' : ℝ → ℝ) (ht_comp : Set.EqOn f.u (t ∘ v.u) v.domain)
    (ht_deriv₁ : ∀ y ∈ v.u '' v.domain, HasDerivAt t (t' y) y)
    (ht_deriv₂ : ∀ y ∈ v.u '' v.domain, HasDerivAt t' (t'' y) y)
    (x : ℝ) (hx_f : x ∈ f.domain) (hx_v : x ∈ v.domain) :
    (0 < t' (v.u x)) ∧
    (f.u' x = t' (v.u x) * v.u' x) ∧
    (f.u'' x = t'' (v.u x) * (v.u' x) ^ 2 + t' (v.u x) * v.u'' x) ∧
    (f.absoluteRiskAversion x hx_f - v.absoluteRiskAversion x hx_v =
      -(t'' (v.u x) * v.u' x) / t' (v.u x)) := by
  have h_eq_nhds : f.u' =ᶠ[nhds x] fun y => t' (v.u y) * v.u' y :=
    first_deriv_eq_nhds f v t t' x hx_f ht_comp ht_deriv₁ h_same_domain
  have hu'_eq : f.u' x = t' (v.u x) * v.u' x := h_eq_nhds.eq_of_nhds
  have hu''_eq : f.u'' x = t'' (v.u x) * (v.u' x) ^ 2 + t' (v.u x) * v.u'' x :=
    second_deriv_chain_rule f v t t' t'' x hx_f hx_v
      (fun y hy => ⟨ht_deriv₁ y hy, ht_deriv₂ y hy⟩) h_eq_nhds
  have hv'_pos : 0 < v.u' x := v.u'_pos x hx_v
  have hf'_pos : 0 < f.u' x := f.u'_pos x hx_f
  have hprod_pos : 0 < t' (v.u x) * v.u' x := by simpa [hu'_eq] using hf'_pos
  have ht'_pos : 0 < t' (v.u x) := pos_of_mul_pos_left hprod_pos hv'_pos.le
  exact ⟨ht'_pos, hu'_eq, hu''_eq, by
    dsimp [TwiceDiffUtility.absoluteRiskAversion]
    rw [hu'_eq, hu''_eq]
    field_simp [show t' (v.u x) ≠ 0 by linarith, show v.u' x ≠ 0 by linarith]
    ring⟩

/-- **Pratt's comparison theorem** (Pratt 1964). On a shared domain, `f` is more risk averse than
`v` — that is, `f.u` is an increasing concave transform of `v.u` — if and only if `f`'s Arrow–Pratt
absolute coefficient dominates `v`'s at every point. -/
theorem more_risk_averse_iff_absoluteRiskAversion_ge (f v : TwiceDiffUtility)
    (h_same_domain : f.domain = v.domain) :
    MoreRiskAverseOn f.u v.u v.domain ↔
      ∀ x (hx_f : x ∈ f.domain) (hx_v : x ∈ v.domain),
        f.absoluteRiskAversion x hx_f ≥ v.absoluteRiskAversion x hx_v := by
  constructor
  · rintro ⟨t, _, ht_concave, ht_comp⟩ x hx_f hx_v
    obtain ⟨t', t'', ht_deriv₁, ht_deriv₂⟩ :=
      transformation_twice_diff f v h_same_domain t ht_comp
    obtain ⟨ht'_pos, _, _, hdiff⟩ :=
      absoluteRiskAversion_diff_eq f v h_same_domain t t' t'' ht_comp
        ht_deriv₁ ht_deriv₂ x hx_f hx_v
    have ht''_nonpos : t'' (v.u x) ≤ 0 :=
      (concaveOn_iff_second_deriv_nonpos v.image_domain_open v.image_domain_convex
        ht_deriv₁ ht_deriv₂).mp ht_concave (v.u x) ⟨x, hx_v, rfl⟩
    have hv'_pos : 0 < v.u' x := v.u'_pos x hx_v
    have h_rhs_nonneg : 0 ≤ -(t'' (v.u x) * v.u' x) / t' (v.u x) :=
      div_nonneg (by linarith [mul_nonpos_of_nonpos_of_nonneg ht''_nonpos hv'_pos.le]) ht'_pos.le
    linarith
  · intro h_ara
    obtain ⟨v_inv, _, _, hv_left, _, _, _⟩ := v.exists_inverse_twice_diff
    let g : ℝ → ℝ := fun y => f.u (v_inv y)
    have h_eqOn : Set.EqOn f.u (g ∘ v.u) v.domain := by
      intro x hx; dsimp [g]; rw [hv_left x hx]
    obtain ⟨g', g'', hg_deriv₁, hg_deriv₂⟩ :=
      transformation_twice_diff f v h_same_domain g h_eqOn
    -- At each image point `g` has positive first derivative (so it is strictly increasing, the
    -- monotonicity Pratt's definition requires) and nonpositive second derivative (so it is
    -- concave); both fall out of the same first-derivative / ARA computation.
    have hg_props : ∀ y ∈ v.u '' v.domain, 0 < g' y ∧ g'' y ≤ 0 := by
      rintro y ⟨x, hx_v, rfl⟩
      have hx_f : x ∈ f.domain := h_same_domain ▸ hx_v
      obtain ⟨hg'_pos, _, _, hdiff⟩ :=
        absoluteRiskAversion_diff_eq f v h_same_domain g g' g'' h_eqOn
          hg_deriv₁ hg_deriv₂ x hx_f hx_v
      have hv'_pos : 0 < v.u' x := v.u'_pos x hx_v
      refine ⟨hg'_pos, ?_⟩
      have h_num_nonneg : 0 ≤ -(g'' (v.u x) * v.u' x) := by
        have hdiff_nonneg : 0 ≤ -(g'' (v.u x) * v.u' x) / g' (v.u x) := by
          rw [← hdiff]; linarith [h_ara x hx_f hx_v]
        simpa using (le_div_iff₀ hg'_pos).mp hdiff_nonneg
      exact nonpos_of_mul_nonpos_right (by linarith) hv'_pos
    have hg_strictMono : StrictMonoOn g (v.u '' v.domain) :=
      strictMonoOn_of_deriv_pos v.image_domain_convex
        (fun y hy => (hg_deriv₁ y hy).continuousAt.continuousWithinAt)
        (fun y hy => by
          have hy' : y ∈ v.u '' v.domain := interior_subset hy
          rw [(hg_deriv₁ y hy').deriv]; exact (hg_props y hy').1)
    exact ⟨g, hg_strictMono,
      (concaveOn_iff_second_deriv_nonpos v.image_domain_open v.image_domain_convex
        hg_deriv₁ hg_deriv₂).mpr (fun y hy => (hg_props y hy).2), h_eqOn⟩

/-- A more risk-averse agent assigns a lower certainty equivalent: If `f` is more risk averse than
`v` on their shared domain, the lottery's outcomes lie in that domain, and `cu`, `cv` are
certainty-equivalent witnesses for `f` and `v` that also lie in the domain, then `f`'s certainty
equivalent `cu` is at most `v`'s certainty equivalent `cv`. -/
lemma MoreRiskAverseOn.le_certaintyEquivalent {n : ℕ}
    (f v : TwiceDiffUtility)
    (h_same_domain : f.domain = v.domain)
    (L : FinLottery n)
    (hx : ∀ i, L.outcome i ∈ v.domain)
    (h_more : MoreRiskAverseOn f.u v.u v.domain)
    (cu cv : ℝ)
    (hcu_dom : cu ∈ f.domain) (hcv_dom : cv ∈ v.domain)
    (hcu : IsCertaintyEquivalent f.u L cu)
    (hcv : IsCertaintyEquivalent v.u L cv) :
    cu ≤ cv := by
  rcases h_more with ⟨g, _, hg_concave, hg_comp⟩
  have eq_u_cu : f.u cu = ∑ i, L.prob.pmf i * f.u (L.outcome i) := hcu
  have eq_v_cv : v.u cv = ∑ i, L.prob.pmf i * v.u (L.outcome i) := hcv
  have h_jensen :
      ∑ i, L.prob.pmf i * g (v.u (L.outcome i)) ≤ g (∑ i, L.prob.pmf i * v.u (L.outcome i)) := by
    have h_smul :
        ∑ i, L.prob.pmf i • g (v.u (L.outcome i)) ≤ g (∑ i, L.prob.pmf i • v.u (L.outcome i)) :=
      ConcaveOn.le_map_sum hg_concave
      (by intro i hi; exact L.prob.nonneg i)
      L.prob.sum_one
      (fun i a ↦ mem_image_of_mem v.u (hx i))
    simpa only [smul_eq_mul] using h_smul
  have h1 : f.u cu = ∑ i, L.prob.pmf i * g (v.u (L.outcome i)) := by
    rw [eq_u_cu]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hg_comp (hx i), Function.comp]
  have h2 : g (∑ i, L.prob.pmf i * v.u (L.outcome i)) = g (v.u cv) := by rw [← eq_v_cv]
  have h3 : g (v.u cv) = f.u cv := (hg_comp hcv_dom).symm
  rw [← h1, h2, h3] at h_jensen
  have hcv_f : cv ∈ f.domain := h_same_domain ▸ hcv_dom
  exact (f.strictMonoOn_u.le_iff_le hcu_dom hcv_f).mp h_jensen

end Econlib.Preferences
