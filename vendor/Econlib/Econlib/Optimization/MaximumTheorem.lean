/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Berge's Maximum Theorem

The **maximum theorem** (Berge 1963). When an objective function `f : Θ → X → ℝ` is jointly
continuous and the constraint correspondence `Φ : Θ → Set X` is continuous (upper and lower
hemicontinuous), compact-valued, and nonempty-valued, then:

1. The value function `V(θ) = sup_{x ∈ Φ(θ)} f(θ, x)` is continuous.
2. The argmax correspondence `X*(θ) = argmax_{Φ(θ)} f(θ, ·)` is upper hemicontinuous.
3. The argmax correspondence is compact-valued.

## Main statements

* `valueFunction_continuous`: The value function is continuous.
* `argmax_upperHemicontinuous`: The argmax correspondence is upper hemicontinuous.
* `argmax_isCompact`: The argmax correspondence is compact-valued.

## References

* Berge, Claude. 1963. *Topological Spaces*. Translated by E. M. Patterson. Macmillan.

## Tags

berge maximum theorem, value function, argmax, hemicontinuous, compact-valued
-/

@[expose] public section

namespace Econlib.Optimization

variable {Θ X : Type*} [TopologicalSpace Θ] [TopologicalSpace X]

section BergeTheorems

variable {f : Θ → X → ℝ} {Φ : Θ → Set X}

private lemma berge_continuous_slice
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2)) (θ : Θ) : Continuous (f θ) :=
  hf_cont.comp (Continuous.prodMk_right θ)

private lemma berge_continuousOn_slice
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2)) (θ : Θ) : ContinuousOn (f θ) (Φ θ) :=
  (berge_continuous_slice hf_cont θ).continuousOn

private lemma berge_image_bddAbove
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_compact : ∀ θ, IsCompact (Φ θ)) (θ : Θ) : BddAbove (f θ '' Φ θ) :=
  ((hΦ_compact θ).image (berge_continuous_slice hf_cont θ)).bddAbove

/-- **Berge Part 3**: The argmax correspondence is compact-valued. -/
theorem argmax_isCompact
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_compact : ∀ θ, IsCompact (Φ θ)) (θ : Θ) :
    IsCompact (argmax (f θ) (Φ θ)) :=
  argmax_compact (hΦ_compact θ) (berge_continuousOn_slice hf_cont θ)

/-- The value function equals `f θ x` at any maximizer `x`. -/
private lemma value_eq_at_maximizer
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_compact : ∀ θ, IsCompact (Φ θ))
    (hΦ_nonempty : ∀ θ, (Φ θ).Nonempty)
    (θ : Θ) (x : X) (hx : x ∈ argmax (f θ) (Φ θ)) :
    f θ x = valueFunction (f θ) (Φ θ) :=
  valueFunction_eq_of_mem_argmax (hΦ_compact θ) (hΦ_nonempty θ)
    (berge_continuousOn_slice hf_cont θ) hx

/-- The value function is upper semicontinuous. -/
lemma valueFunction_upperSemicontinuous
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_uhc : UpperHemicontinuous Φ)
    (hΦ_compact : ∀ θ, IsCompact (Φ θ))
    (hΦ_nonempty : ∀ θ, (Φ θ).Nonempty) :
    UpperSemicontinuous (fun θ => valueFunction (f θ) (Φ θ)) := by
  intro θ₀ b hb
  set g := fun p : Θ × X => f p.1 p.2
  have hW : IsOpen (g ⁻¹' Set.Iio b) := isOpen_Iio.preimage hf_cont
  have hsubW : {θ₀} ×ˢ Φ θ₀ ⊆ g ⁻¹' Set.Iio b := by
    rintro ⟨θ, x⟩ ⟨rfl, hxΦ⟩
    exact lt_of_le_of_lt
      (le_csSup (berge_image_bddAbove hf_cont hΦ_compact θ) ⟨x, hxΦ, rfl⟩) hb
  obtain ⟨U, W, hU_open, hW_open, hθ₀U, hΦW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton (hΦ_compact θ₀) hW hsubW
  filter_upwards [hΦ_uhc.forall_isOpen θ₀ W hW_open hΦW,
    hU_open.mem_nhds (hθ₀U (Set.mem_singleton θ₀))] with θ hΦW' hθU
  obtain ⟨x_max, hx_max_mem, hx_max⟩ :=
    (hΦ_compact θ).exists_isMaxOn (hΦ_nonempty θ) (berge_continuousOn_slice hf_cont θ)
  have h_eq := (value_eq_at_maximizer hf_cont hΦ_compact hΦ_nonempty θ x_max
    ⟨hx_max_mem, hx_max⟩).symm
  rw [h_eq]
  exact hUW (Set.mk_mem_prod hθU (hΦW' hx_max_mem))

/-- The value function is lower semicontinuous. -/
lemma valueFunction_lowerSemicontinuous
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_lhc : LowerHemicontinuous Φ)
    (hΦ_compact : ∀ θ, IsCompact (Φ θ))
    (hΦ_nonempty : ∀ θ, (Φ θ).Nonempty) :
    LowerSemicontinuous (fun θ => valueFunction (f θ) (Φ θ)) := by
  intro θ₀ a ha
  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ :=
    (hΦ_compact θ₀).exists_isMaxOn (hΦ_nonempty θ₀) (berge_continuousOn_slice hf_cont θ₀)
  have hx₀_val : f θ₀ x₀ = valueFunction (f θ₀) (Φ θ₀) :=
    value_eq_at_maximizer hf_cont hΦ_compact hΦ_nonempty θ₀ x₀
      ⟨hx₀_mem, hx₀_max⟩
  set g := fun p : Θ × X => f p.1 p.2
  have hpair_mem : a < g (θ₀, x₀) := by change a < f θ₀ x₀; linarith [hx₀_val]
  have hopen : IsOpen (g ⁻¹' Set.Ioi a) := isOpen_Ioi.preimage hf_cont
  obtain ⟨N, V_set, hN_open, hV_open, hθ₀N, hx₀V, hNV⟩ :=
    isOpen_prod_iff.mp hopen θ₀ x₀ hpair_mem
  have hΦ_inter : (Φ θ₀ ∩ V_set).Nonempty := ⟨x₀, hx₀_mem, hx₀V⟩
  have h_lhc_open :=
    lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl.mp hΦ_lhc V_set hV_open
  have hθ₀_in : θ₀ ∈ (Φ ⁻¹' Set.Iic V_setᶜ)ᶜ := by
    intro hmem
    rw [Set.mem_preimage, Set.mem_Iic] at hmem
    obtain ⟨x, hxΦ, hxV⟩ := hΦ_inter
    exact hmem hxΦ hxV
  filter_upwards [hN_open.mem_nhds hθ₀N, h_lhc_open.mem_nhds hθ₀_in] with θ hθN hθ_lhc
  have ⟨x_θ, hx_θ_Φ, hx_θ_V⟩ : (Φ θ ∩ V_set).Nonempty := by
    by_contra h_empty
    apply hθ_lhc
    rw [Set.mem_preimage, Set.mem_Iic]
    intro x hxΦ hxV
    exact h_empty ⟨x, hxΦ, hxV⟩
  exact lt_of_lt_of_le (hNV (Set.mk_mem_prod hθN hx_θ_V))
    (le_csSup (berge_image_bddAbove hf_cont hΦ_compact θ) ⟨x_θ, hx_θ_Φ, rfl⟩)

/-- **Berge Part 1**: The value function is continuous. -/
theorem valueFunction_continuous
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_uhc : UpperHemicontinuous Φ)
    (hΦ_lhc : LowerHemicontinuous Φ)
    (hΦ_compact : ∀ θ, IsCompact (Φ θ))
    (hΦ_nonempty : ∀ θ, (Φ θ).Nonempty) :
    Continuous (fun θ => valueFunction (f θ) (Φ θ)) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨valueFunction_lowerSemicontinuous hf_cont hΦ_lhc hΦ_compact hΦ_nonempty,
     valueFunction_upperSemicontinuous hf_cont hΦ_uhc hΦ_compact hΦ_nonempty⟩

/-- **Berge Part 2**: The argmax correspondence is upper hemicontinuous. -/
theorem argmax_upperHemicontinuous [T2Space X]
    (hf_cont : Continuous (fun p : Θ × X => f p.1 p.2))
    (hΦ_uhc : UpperHemicontinuous Φ)
    (hΦ_lhc : LowerHemicontinuous Φ)
    (hΦ_compact : ∀ θ, IsCompact (Φ θ))
    (hΦ_nonempty : ∀ θ, (Φ θ).Nonempty) :
    UpperHemicontinuous (fun θ => argmax (f θ) (Φ θ)) := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  intro θ₀ U hU_open hX_sub_U
  by_cases hcase : Φ θ₀ ⊆ U
  · exact (hΦ_uhc.forall_isOpen θ₀ U hU_open hcase).mono fun θ hθ x hx => hθ hx.1
  · rw [Set.not_subset] at hcase
    set gap : Θ × X → ℝ := fun p => valueFunction (f p.1) (Φ p.1) - f p.1 p.2
    have hgap_cont : Continuous gap :=
      ((valueFunction_continuous hf_cont hΦ_uhc hΦ_lhc hΦ_compact hΦ_nonempty).comp
        continuous_fst).sub hf_cont
    set K := Φ θ₀ ∩ Uᶜ
    have hK_compact : IsCompact K := (hΦ_compact θ₀).inter_right hU_open.isClosed_compl
    have hK_pos : ∀ x ∈ K, (0 : ℝ) < gap (θ₀, x) := by
      intro x ⟨hxΦ, hxU⟩
      have hx_not_max : ¬ IsMaxOn (f θ₀) (Φ θ₀) x :=
        fun h_max => hxU (hX_sub_U ⟨hxΦ, h_max⟩)
      unfold IsMaxOn IsMaxFilter at hx_not_max
      rw [Filter.eventually_principal] at hx_not_max
      push Not at hx_not_max
      obtain ⟨y, hyΦ, hfy⟩ := hx_not_max
      have h_le : f θ₀ y ≤ valueFunction (f θ₀) (Φ θ₀) :=
        le_csSup (berge_image_bddAbove hf_cont hΦ_compact θ₀)
          (Set.mem_image_of_mem (f θ₀) hyΦ)
      linarith
    have hW_open : IsOpen (gap ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage hgap_cont
    have hsubW : {θ₀} ×ˢ K ⊆ gap ⁻¹' Set.Ioi 0 := by
      rintro ⟨θ, x⟩ ⟨rfl, hxK⟩
      exact hK_pos x hxK
    obtain ⟨N, W, hN_open, hW_open', hθ₀N, hKW, hNW⟩ :=
      generalized_tube_lemma isCompact_singleton hK_compact hW_open hsubW
    have hΦ_sub_UW : Φ θ₀ ⊆ U ∪ W := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Set.mem_union_left W hxU
      · exact Set.mem_union_right U (hKW ⟨hx, hxU⟩)
    filter_upwards [hΦ_uhc.forall_isOpen θ₀ (U ∪ W) (hU_open.union hW_open') hΦ_sub_UW,
      hN_open.mem_nhds (hθ₀N (Set.mem_singleton θ₀))] with θ hΦUW hθN
    intro x ⟨hxΦ, hx_max⟩
    rcases hΦUW hxΦ with hxU | hxW
    · exact hxU
    · have hgpos : (0 : ℝ) < gap (θ, x) := hNW (Set.mk_mem_prod hθN hxW)
      have hx_val : f θ x = valueFunction (f θ) (Φ θ) :=
        value_eq_at_maximizer hf_cont hΦ_compact hΦ_nonempty θ x ⟨hxΦ, hx_max⟩
      have : gap (θ, x) = valueFunction (f θ) (Φ θ) - f θ x := rfl
      linarith

end BergeTheorems

end Econlib.Optimization
