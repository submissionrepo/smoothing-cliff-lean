/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-!
# Chebyshev's integral inequality

**Chebyshev's integral inequality** for real-valued functions that monovary or antivary on a
measurable set `s` of finite measure: If `f` and `g` monovary on `s`, then
`(∫_s f)(∫_s g) ≤ μ(s) · ∫_s fg`, with the reverse inequality when they antivary. Each case also
has a strict form when the product `(f x - f y)(g x - g y)` is nonzero on a set of positive product
measure.

## Main statements

* `MeasureTheory.MonovaryOn.setIntegral_mul_setIntegral_le_measureReal_mul_setIntegral` — monovary
  case: `(∫_s f)(∫_s g) ≤ μ(s) · ∫_s fg`.
* `MeasureTheory.MonovaryOn.setIntegral_mul_setIntegral_lt_measureReal_mul_setIntegral` — strict
  monovary case.
* `MeasureTheory.AntivaryOn.measureReal_mul_setIntegral_le_setIntegral_mul_setIntegral` — antivary
  case: `μ(s) · ∫_s fg ≤ (∫_s f)(∫_s g)`.
* `MeasureTheory.AntivaryOn.measureReal_mul_setIntegral_lt_setIntegral_mul_setIntegral` — strict
  antivary case.

## Tags

chebyshev, integral, monovary, antivary, inequality
-/

@[expose] public section

namespace MeasureTheory

/-- The iterated integral of `(f x - f y)(g x - g y)` over `s × s` expands to
`2 μ(s) ∫_s fg - 2 (∫_s f)(∫_s g)`. -/
lemma setIntegral_setIntegral_sub_mul_sub
    (hμs : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : IntegrableOn (fun x ↦ f x * g x) s μ) :
    ∫ x in s, ∫ y in s, (f x - f y) * (g x - g y) ∂μ ∂μ =
      2 * μ.real s * (∫ x in s, f x * g x ∂μ) -
      2 * (∫ x in s, f x ∂μ) * (∫ x in s, g x ∂μ) := by
  have h_expand : ∀ x y, (f x - f y) * (g x - g y) =
      f x * g x - f x * g y - f y * g x + f y * g y := by
    intro x y; ring
  simp_rw [h_expand]
  -- Simplify the inner integral for a fixed x
  have inner_eq : ∀ x, ∫ y in s, (f x * g x - f x * g y - f y * g x + f y * g y) ∂μ =
      μ.real s * (f x * g x) - f x * (∫ y in s, g y ∂μ) -
      (∫ y in s, f y ∂μ) * g x + ∫ y in s, f y * g y ∂μ := by
    intro x
    have hi1 : IntegrableOn (fun _ ↦ f x * g x) s μ := integrableOn_const (hs := hμs)
    have hi2 : IntegrableOn (fun y ↦ f x * g y) s μ := hg.const_mul (f x)
    have hi3 : IntegrableOn (fun y ↦ f y * g x) s μ := hf.mul_const (g x)
    have hi4 : IntegrableOn (fun y ↦ f y * g y) s μ := hfg
    have h1 := integral_add ((hi1.sub' hi2).sub' hi3) hi4
    have h2 := integral_sub (hi1.sub' hi2) hi3
    have h3 := integral_sub hi1 hi2
    rw [h1, h2, h3, setIntegral_const, smul_eq_mul, integral_const_mul, integral_mul_const]
  simp_rw [inner_eq]
  -- Simplify the outer integral
  set If := ∫ x in s, f x ∂μ
  set Ig := ∫ x in s, g x ∂μ
  set Ifg := ∫ x in s, f x * g x ∂μ
  set ms := μ.real s
  have ho1 : IntegrableOn (fun x ↦ ms * (f x * g x)) s μ := hfg.const_mul ms
  have ho2 : IntegrableOn (fun x ↦ f x * Ig) s μ := hf.mul_const Ig
  have ho3 : IntegrableOn (fun x ↦ If * g x) s μ := hg.const_mul If
  have ho4 : IntegrableOn (fun _ ↦ Ifg) s μ := integrableOn_const (hs := hμs)
  have k1 := integral_add ((ho1.sub' ho2).sub' ho3) ho4
  have k2 := integral_sub (ho1.sub' ho2) ho3
  have k3 := integral_sub ho1 ho2
  rw [k1, k2, k3, integral_const_mul, integral_mul_const, integral_const_mul,
      setIntegral_const, smul_eq_mul]
  ring

end MeasureTheory

variable {s : Set α} {f g : α → ℝ} [SFinite μ]

/-! ### Chebyshev's inequality, monovary case -/
namespace MonovaryOn

/-- **Chebyshev's integral inequality** (monovary case): If `f` and `g` monovary on `s`, then
`(∫_s f)(∫_s g) ≤ μ(s) · ∫_s fg`. -/
theorem setIntegral_mul_setIntegral_le_measureReal_mul_setIntegral
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (h_mono : MonovaryOn f g s)
    (hint : IntegrableOn (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2))
      (s ×ˢ s) (μ.prod μ)) :
    (∫ x in s, f x ∂μ) * (∫ x in s, g x ∂μ) ≤
      μ.real s * ∫ x in s, f x * g x ∂μ := by
  -- Apply Fubini to rewrite the product integral as an iterated integral
  have h_fubini : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      ∫ x in s, ∫ y in s, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    setIntegral_prod (fun p ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) hint
  -- The integrand is pointwise non-negative by monovariance
  have h_pos : 0 ≤ ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) := by
    apply setIntegral_nonneg (hs.prod hs)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h_mono.sub_mul_sub_nonneg hy hx
  -- Use the algebraic expansion
  have h_expand := setIntegral_setIntegral_sub_mul_sub hμs hf hg hfg
  -- Conclude by linear arithmetic
  linarith

/-- **Chebyshev's integral inequality** (strict monovary case): If `f` and `g` monovary on `s` and
`(f x - f y)(g x - g y)` is nonzero on a set of positive product measure, then
`(∫_s f)(∫_s g) < μ(s) · ∫_s fg`. -/
theorem setIntegral_mul_setIntegral_lt_measureReal_mul_setIntegral
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (h_mono : MonovaryOn f g s)
    (hint : IntegrableOn (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2))
      (s ×ˢ s) (μ.prod μ))
    (h_strict : 0 < (μ.prod μ) (Function.support (fun p : α × α ↦
      (f p.1 - f p.2) * (g p.1 - g p.2)) ∩ (s ×ˢ s))) :
    (∫ x in s, f x ∂μ) * (∫ x in s, g x ∂μ) <
      μ.real s * ∫ x in s, f x * g x ∂μ := by
  have h_ae_nonneg : 0 ≤ᶠ[ae ((μ.prod μ).restrict (s ×ˢ s))]
      (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) := by
    apply ae_restrict_of_forall_mem (hs.prod hs)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h_mono.sub_mul_sub_nonneg hy hx
  have h_pos : 0 < ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae h_ae_nonneg hint]
    exact h_strict
  have h_fubini : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      ∫ x in s, ∫ y in s, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    setIntegral_prod (fun p ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) hint
  have h_expand := setIntegral_setIntegral_sub_mul_sub hμs hf hg hfg
  linarith

end MonovaryOn

/-! ### Chebyshev's inequality, antivary case -/
namespace AntivaryOn

/-- **Chebyshev's integral inequality** (antivary case): If `f` and `g` antivary on `s`, then
`μ(s) · ∫_s fg ≤ (∫_s f)(∫_s g)`. -/
theorem measureReal_mul_setIntegral_le_setIntegral_mul_setIntegral
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (h_anti : AntivaryOn f g s)
    (hint : IntegrableOn (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2))
      (s ×ˢ s) (μ.prod μ)) :
    μ.real s * ∫ x in s, f x * g x ∂μ ≤
      (∫ x in s, f x ∂μ) * (∫ x in s, g x ∂μ) := by
  have h_fubini : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      ∫ x in s, ∫ y in s, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    setIntegral_prod (fun p ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) hint
  have h_neg : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) ≤ 0 := by
    apply setIntegral_nonpos (hs.prod hs)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h_anti.sub_mul_sub_nonpos hy hx
  have h_expand := setIntegral_setIntegral_sub_mul_sub hμs hf hg hfg
  linarith

/-- **Chebyshev's integral inequality** (strict antivary case): If `f` and `g` antivary on `s` and
`(f x - f y)(g x - g y)` is nonzero on a set of positive product measure, then
`μ(s) · ∫_s fg < (∫_s f)(∫_s g)`. -/
theorem measureReal_mul_setIntegral_lt_setIntegral_mul_setIntegral
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (h_anti : AntivaryOn f g s)
    (hint : IntegrableOn (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2))
      (s ×ˢ s) (μ.prod μ))
    (h_strict : 0 < (μ.prod μ) (Function.support (fun p : α × α ↦
      (f p.1 - f p.2) * (g p.1 - g p.2)) ∩ (s ×ˢ s))) :
    μ.real s * ∫ x in s, f x * g x ∂μ <
      (∫ x in s, f x ∂μ) * (∫ x in s, g x ∂μ) := by
  -- Negate to reduce to the nonneg/pos case
  have h_ae_nonneg : 0 ≤ᶠ[ae ((μ.prod μ).restrict (s ×ˢ s))]
      (fun p : α × α ↦ -((f p.1 - f p.2) * (g p.1 - g p.2))) := by
    apply ae_restrict_of_forall_mem (hs.prod hs)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact neg_nonneg.mpr (h_anti.sub_mul_sub_nonpos hy hx)
  have hint_neg : IntegrableOn (fun p : α × α ↦ -((f p.1 - f p.2) * (g p.1 - g p.2)))
      (s ×ˢ s) (μ.prod μ) := hint.neg
  have h_supp : Function.support (fun p : α × α ↦ -((f p.1 - f p.2) * (g p.1 - g p.2))) =
      Function.support (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) := by
    ext p; simp [Function.mem_support]
  have h_neg_pos : 0 < ∫ p in s ×ˢ s, -((f p.1 - f p.2) * (g p.1 - g p.2)) ∂(μ.prod μ) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae h_ae_nonneg hint_neg, h_supp]
    exact h_strict
  -- Convert ∫ -h to -∫ h
  have h_neg : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) < 0 := by
    linarith [integral_neg (μ := (μ.prod μ).restrict (s ×ˢ s))
      (fun p : α × α ↦ (f p.1 - f p.2) * (g p.1 - g p.2))]
  -- Fubini + expansion
  have h_fubini : ∫ p in s ×ˢ s, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      ∫ x in s, ∫ y in s, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    setIntegral_prod (fun p ↦ (f p.1 - f p.2) * (g p.1 - g p.2)) hint
  have h_expand := setIntegral_setIntegral_sub_mul_sub hμs hf hg hfg
  linarith

end AntivaryOn
