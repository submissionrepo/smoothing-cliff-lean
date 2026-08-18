/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Supergradients of concave functions on normed spaces

This file develops the Hahn–Banach style **supergradient theorem** for concave functions on convex
subsets of a (real) normed space.  Concretely, given a concave upper-semicontinuous function
`f : E → ℝ` on a closed convex set `K`, with a one-sided slope bound (bounded steepness) at a
distinguished point `x₀ ∈ K`, there exists a continuous linear functional `H : E →L[ℝ] ℝ` with
operator norm `≤ L` whose induced affine majorant is tight at `x₀`:

```
  f(x) - f(x₀)  ≤  H(x - x₀)            for all x ∈ K,
  ‖H‖_op        ≤  L.
```

## Main statements

* `ConcaveOn.exists_supergradient_of_boundedSteepness` — the supergradient theorem stated above.

## Notes

The result captures the abstract content of a supporting-hyperplane duality — existence of a
supporting hyperplane — without committing to any specific representation of the dual space.
Concrete dual representations (e.g. identifying `(M(Ω), ‖·‖_KR)*` with `Lip(Ω)/ℝ`) belong to
separate files.

## References

* Gale, D. 1967. “A Geometric Duality Theorem with Economic Applications.” *The Review of Economic
  Studies* 34 (1): 19–24. [https://doi.org/10.2307/2296568](https://doi.org/10.2307/2296568).
* Rudin, Walter. 1991. *Functional Analysis*. McGraw-Hill.

## Tags

supergradient, hahn–banach, concave function, supporting hyperplane, duality
-/

@[expose] public section

open Set Topology

namespace ConcaveOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Supergradient theorem (Hahn–Banach form).**

A concave upper-semicontinuous function on a closed convex subset of a real normed space, with
one-sided slope bounded by `L` at the distinguished point `x₀`, admits a continuous linear majorant
of operator norm at most `L` that is tight at `x₀`. -/
theorem exists_supergradient_of_boundedSteepness
    {K : Set E} (hK_conv : Convex ℝ K)
    {f : E → ℝ} (hf_conc : ConcaveOn ℝ K f)
    {x₀ : E} (hx₀ : x₀ ∈ K) {L : ℝ} (hL : 0 ≤ L)
    (hsteep : ∀ x ∈ K, f x - f x₀ ≤ L * ‖x - x₀‖) :
    ∃ H : E →L[ℝ] ℝ, ‖H‖ ≤ L ∧ ∀ x ∈ K, f x - f x₀ ≤ H (x - x₀) := by
  set A : Set (E × ℝ) := {p : E × ℝ | L * ‖p.1‖ < p.2} with hA_def
  set B : Set (E × ℝ) := {p : E × ℝ | x₀ + p.1 ∈ K ∧ p.2 ≤ f (x₀ + p.1) - f x₀}
    with hB_def
  have hA_open : IsOpen A := by
    have hcont : Continuous (fun p : E × ℝ => L * ‖p.1‖ - p.2) :=
      (continuous_const.mul continuous_norm.fst').sub continuous_snd
    have : A = {p : E × ℝ | L * ‖p.1‖ - p.2 < 0} := by
      ext p; simp [A, sub_neg]
    rw [this]
    exact hcont.isOpen_preimage _ isOpen_Iio
  have hA_conv : Convex ℝ A := by
    intro p hp q hq a b ha hb hab
    have hp' : L * ‖p.1‖ < p.2 := hp
    have hq' : L * ‖q.1‖ < q.2 := hq
    change L * ‖(a • p + b • q).1‖ < (a • p + b • q).2
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have h_norm : ‖a • p.1 + b • q.1‖ ≤ a * ‖p.1‖ + b * ‖q.1‖ := by
      calc ‖a • p.1 + b • q.1‖
          ≤ ‖a • p.1‖ + ‖b • q.1‖ := norm_add_le _ _
        _ = a * ‖p.1‖ + b * ‖q.1‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    have h1 : L * ‖a • p.1 + b • q.1‖ ≤ a * (L * ‖p.1‖) + b * (L * ‖q.1‖) := by
      have := mul_le_mul_of_nonneg_left h_norm hL
      nlinarith
    rcases ha.lt_or_eq with ha_pos | ha_eq
    · -- a > 0: a*(L*‖p.1‖) < a*p.2
      have hap : a * (L * ‖p.1‖) < a * p.2 := mul_lt_mul_of_pos_left hp' ha_pos
      have hbq : b * (L * ‖q.1‖) ≤ b * q.2 :=
        mul_le_mul_of_nonneg_left hq'.le hb
      linarith
    · -- a = 0, so b = 1 > 0
      have hb_pos : 0 < b := by linarith [ha_eq]
      have hbq : b * (L * ‖q.1‖) < b * q.2 := mul_lt_mul_of_pos_left hq' hb_pos
      have hap : a * (L * ‖p.1‖) ≤ a * p.2 :=
        mul_le_mul_of_nonneg_left hp'.le ha
      linarith
  have hB_conv : Convex ℝ B := by
    intro p hp q hq a b ha hb hab
    obtain ⟨hp_mem, hp_le⟩ := hp
    obtain ⟨hq_mem, hq_le⟩ := hq
    -- The convex combination of perturbations recenters as a convex combination in `K`.
    have h_eq : x₀ + (a • p + b • q).1 = a • (x₀ + p.1) + b • (x₀ + q.1) := by
      change x₀ + (a • p.1 + b • q.1) = a • (x₀ + p.1) + b • (x₀ + q.1)
      rw [smul_add, smul_add]
      have hx_split : x₀ = a • x₀ + b • x₀ := by
        rw [← add_smul, hab, one_smul]
      conv_lhs => rw [hx_split]
      abel
    refine ⟨?_, ?_⟩
    · rw [h_eq]
      exact hK_conv hp_mem hq_mem ha hb hab
    · change (a • p + b • q).2 ≤ f (x₀ + (a • p + b • q).1) - f x₀
      rw [h_eq]
      have h_conc := hf_conc.2 hp_mem hq_mem ha hb hab
      have h_smul1 : a * p.2 ≤ a * (f (x₀ + p.1) - f x₀) :=
        mul_le_mul_of_nonneg_left hp_le ha
      have h_smul2 : b * q.2 ≤ b * (f (x₀ + q.1) - f x₀) :=
        mul_le_mul_of_nonneg_left hq_le hb
      simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
      have h_conc' : a * f (x₀ + p.1) + b * f (x₀ + q.1) ≤
          f (a • (x₀ + p.1) + b • (x₀ + q.1)) := by
        simpa [smul_eq_mul] using h_conc
      have hab1 : a * f x₀ + b * f x₀ = f x₀ := by
        rw [← add_mul, hab]; ring
      linarith
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ⟨v, t⟩ hA_mem ⟨hB_mem1, hB_mem2⟩
    have h1 : L * ‖v‖ < t := hA_mem
    have h2 : t ≤ f (x₀ + v) - f x₀ := hB_mem2
    have h3 : f (x₀ + v) - f x₀ ≤ L * ‖(x₀ + v) - x₀‖ := hsteep _ hB_mem1
    have h4 : (x₀ + v) - x₀ = v := by abel
    rw [h4] at h3
    linarith
  obtain ⟨Φ, u, hΦ_A, hΦ_B⟩ := geometric_hahn_banach_open hA_conv hA_open hB_conv hAB_disj
  have h_00_B : ((0 : E), (0 : ℝ)) ∈ B := by
    refine ⟨?_, ?_⟩
    · simp [hx₀]
    · simp
  have hu_le : u ≤ Φ ((0 : E), (0 : ℝ)) := hΦ_B _ h_00_B
  have h_phi_00 : Φ ((0 : E), (0 : ℝ)) = 0 := map_zero Φ
  rw [h_phi_00] at hu_le
  have hu_ge : (0 : ℝ) ≤ u := by
    have h_seq_A : ∀ n : ℕ, ((0 : E), (1 / (n + 1 : ℝ))) ∈ A := by
      intro n
      change L * ‖(0 : E)‖ < 1 / (n + 1 : ℝ)
      simp only [norm_zero, mul_zero, one_div, inv_pos]
      positivity
    have h_seq_lt : ∀ n : ℕ, Φ ((0 : E), (1 / (n + 1 : ℝ))) < u :=
      fun n => hΦ_A _ (h_seq_A n)
    have h_lim : Filter.Tendsto (fun n : ℕ => Φ ((0 : E), (1 / (n + 1 : ℝ))))
        Filter.atTop (nhds (Φ ((0 : E), (0 : ℝ)))) := by
      apply Φ.continuous.tendsto _ |>.comp
      apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    rw [h_phi_00] at h_lim
    exact le_of_tendsto' h_lim (fun n => (h_seq_lt n).le)
  have hu_eq : u = 0 := le_antisymm hu_le hu_ge
  let G : E →L[ℝ] ℝ := Φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := Φ ((0 : E), (1 : ℝ))
  have hΦ_decomp : ∀ (v : E) (t : ℝ), Φ (v, t) = G v + t * c := by
    intro v t
    have h1 : (v, t) = (v, (0 : ℝ)) + ((0 : E), t) := by simp
    have h2 : ((0 : E), t) = t • ((0 : E), (1 : ℝ)) := by simp
    rw [h1, map_add, h2, map_smul]
    rfl
  have h_01_A : ((0 : E), (1 : ℝ)) ∈ A := by change L * ‖(0 : E)‖ < 1; simp
  have hc_neg : c < 0 := hu_eq ▸ hΦ_A _ h_01_A
  set d : ℝ := -c with hd_def
  have hd_pos : 0 < d := by simp [d]; linarith
  set H : E →L[ℝ] ℝ := d⁻¹ • G with hH_def
  have h_HvL : ∀ v : E, H v ≤ L * ‖v‖ := by
    intro v
    have h_forall : ∀ ε > 0, G v < (L * ‖v‖ + ε) * d := by
      intro ε hε
      have h_in_A : (v, L * ‖v‖ + ε) ∈ A := by change L * ‖v‖ < L * ‖v‖ + ε; linarith
      have hΦlt := hΦ_A _ h_in_A
      rw [hu_eq, hΦ_decomp] at hΦlt
      have : G v < -(L * ‖v‖ + ε) * c := by linarith
      have hd_eq : (L * ‖v‖ + ε) * d = -(L * ‖v‖ + ε) * c := by simp [d]; ring
      linarith
    have h_le : G v ≤ L * ‖v‖ * d := by
      by_contra h
      push Not at h
      set δ : ℝ := G v - L * ‖v‖ * d with hδ_def
      have hδ_pos : 0 < δ := by simp [δ]; linarith
      have hε_pos : 0 < δ / (2 * d) := by positivity
      have hε_d : (δ / (2 * d)) * d = δ / 2 := by field_simp
      have := h_forall (δ / (2 * d)) hε_pos
      have h_expand : (L * ‖v‖ + δ / (2 * d)) * d = L * ‖v‖ * d + δ / 2 := by
        rw [add_mul, hε_d]
      rw [h_expand] at this
      linarith
    have hH_apply : H v = d⁻¹ * G v := by
      rfl
    rw [hH_apply]
    have : d⁻¹ * G v ≤ d⁻¹ * (L * ‖v‖ * d) :=
      mul_le_mul_of_nonneg_left h_le (inv_nonneg.mpr hd_pos.le)
    have h_simp : d⁻¹ * (L * ‖v‖ * d) = L * ‖v‖ := by
      field_simp
    linarith
  have h_supgrad : ∀ x ∈ K, f x - f x₀ ≤ H (x - x₀) := by
    intro x hx
    set v : E := x - x₀ with hv_def
    set t : ℝ := f x - f x₀ with ht_def
    have h_x_eq : x₀ + v = x := by simp [v]
    have h_in_B : (v, t) ∈ B := by
      refine ⟨?_, ?_⟩
      · rw [h_x_eq]; exact hx
      · rw [h_x_eq]
    have hΦge := hΦ_B _ h_in_B
    rw [hu_eq, hΦ_decomp] at hΦge
    have h_td : t * d ≤ G v := by simp [d]; linarith
    have hH_apply : H v = d⁻¹ * G v := by rfl
    have h_div : t ≤ d⁻¹ * G v := by
      have hd_inv_pos : 0 < d⁻¹ := inv_pos.mpr hd_pos
      have h1 : d⁻¹ * (t * d) ≤ d⁻¹ * G v :=
        mul_le_mul_of_nonneg_left h_td hd_inv_pos.le
      have h_simp : d⁻¹ * (t * d) = t := by field_simp
      linarith
    rw [hH_apply]
    exact h_div
  refine ⟨H, ?_, h_supgrad⟩
  refine ContinuousLinearMap.opNorm_le_bound H hL ?_
  intro v
  have h_pos : H v ≤ L * ‖v‖ := h_HvL v
  have h_neg : H (-v) ≤ L * ‖v‖ := by
    have := h_HvL (-v)
    rwa [norm_neg] at this
  have h_neg' : -H v ≤ L * ‖v‖ := by
    rw [map_neg] at h_neg; linarith
  exact abs_le.mpr ⟨by linarith, h_pos⟩

end ConcaveOn
