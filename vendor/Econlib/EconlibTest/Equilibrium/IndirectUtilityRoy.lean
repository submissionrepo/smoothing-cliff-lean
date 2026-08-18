/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Equilibrium
import EconlibExamples.Equilibrium.CobbDouglasRoy
import Mathlib

/-!
# Indirect utility and Roy's identity — non-vacuity / sign checks

Compile-time semantic witnesses for the consumer-duality layer
(`Econlib.Equilibrium.IndirectUtility` and `Econlib.Equilibrium.RoyIdentity`), anchored on the
concrete two-good Cobb–Douglas consumer of `EconlibExamples.Equilibrium.CobbDouglasRoy`.

The canonical failure mode caught here is the **Roy sign/derivative flip**: Roy's identity recovers
Marshallian demand as `x*_l = −(∂v/∂p_l)/(∂v/∂w)`, and both the minus sign and the placement of the
two partials are the entire content — drop the minus (or swap `∂/∂p` with `∂/∂w`) and the identity
reads something wrong. The witnesses force the identity through a hand-solved instance where every
quantity is a clean rational, then anchor the two partial derivatives separately so the cancelation
is forced through real numbers.

The instance is anchored at an **asymmetric** price/wealth point so that the swap `∂/∂p ↔ ∂/∂w` is
numerically discriminating (at a symmetric unit point both partials and demand collapse to `1`, so
the swap is invisible — that is the bug this anchor is chosen to expose). Over `Fin 2` with
`α = (1/2, 1/2)` (so `u = √(x·y)`, the symmetric Cobb–Douglas):

* prices `p = (1, 4)`, wealth `w = 4`;
* Marshallian demand `x* = (a·w/p_x, (1−a)·w/p_y) = (1/2·4/1, 1/2·4/4) = (2, 1/2)` — **asymmetric**;
* indirect utility `v(p, w) = w · (a/p_x)^a · ((1−a)/p_y)^(1−a) = 4 · (1/2)^(1/2) · (1/8)^(1/2)`,
  which equals `4 · √(1/16) = 1`;
* `∂v/∂w = v/w = 1/4`, `∂v/∂p_x = −a·v/p_x = −1/2`, `∂v/∂p_y = −(1−a)·v/p_y = −1/8`;
* Roy good `x`: `−(∂v/∂p_x)/(∂v/∂w) = −(−1/2)/(1/4) = 2 = x*_x` (minus sign in the right place);
* Roy good `y`: `−(∂v/∂p_y)/(∂v/∂w) = −(−1/8)/(1/4) = 1/2 = x*_y`.

The **swapped** formula `−(∂v/∂w)/(∂v/∂p_x) = −(1/4)/(−1/2) = 1/2 ≠ 2 = x*_x` is now caught: it
disagrees with demand on good `x`. The `roy_sign_check` witnesses consume the actual derivative
anchors (`roy_wealth_deriv_anchor`, `roy_price_deriv_anchor`, `roy_price_deriv_anchor_1`) and the
demand anchors, so a broken Roy theorem would fail them.

A wealth/price swap in the budget constraint would break `indirectUtility_mono_wealth` (more wealth
must weakly *raise* `v`); we anchor that monotonicity at `w = 2 < 4` as well.
-/

noncomputable section

namespace EconlibTest.Equilibrium.IndirectUtilityRoy

open Econlib.Equilibrium Econlib.Equilibrium.Roy Econlib.Preferences Econlib.Optimization
open EconlibExamples.Equilibrium.CobbDouglasRoy
open Matrix ContinuousLinearMap

/-! ## The concrete symmetric Cobb–Douglas consumer -/

/-- The symmetric two-good Cobb–Douglas consumer with `α = (1/2, 1/2)`, i.e. `u = √(x·y)`. -/
private def cd : CobbDouglasUtility 2 where
  α := ![1 / 2, 1 / 2]
  α_pos := by intro i; fin_cases i <;> norm_num

/-- The concrete price vector `p = (1, 4)` (asymmetric, to discriminate derivative swaps). -/
private abbrev p : Fin 2 → ℝ := ![1, 4]

/-- The concrete wealth `w = 4`. -/
private abbrev w : ℝ := 4

private theorem hp_pos : ∀ l, 0 < p l := by intro l; fin_cases l <;> norm_num

private theorem hw_pos : (0 : ℝ) < w := by norm_num

/-! ## Indirect-utility characterization, attainment, and monotonicity -/

/-- **Value characterization.** `indirectUtility u p w = u x` at the closed-form maximizer. -/
theorem indirectUtility_eq_witness :
    indirectUtility cd.uTotal p w = cd.uTotal (cdDemand cd (p, w)) :=
  indirectUtility_cdDemand cd (by norm_num) hp_pos hw_pos

/-- **Attainment of the maximizer.** A budget-feasible maximizer exists. -/
theorem exists_isMaxOn_witness :
    ∃ x ∈ budgetSetAt p w, IsMaxOn cd.uTotal (budgetSetAt p w) x :=
  exists_isMaxOn_budgetSetAt cd.uTotal_continuous hp_pos hw_pos.le

/-- **The indirect utility is attained.** A budget-feasible bundle realizes the value. -/
theorem exists_eq_indirectUtility_witness :
    ∃ x ∈ budgetSetAt p w, indirectUtility cd.uTotal p w = cd.uTotal x :=
  exists_eq_indirectUtility cd.uTotal_continuous hp_pos hw_pos.le

/-- **Monotonicity in wealth.** More wealth weakly raises `v`, anchored at `w = 2 < 4`. -/
theorem indirectUtility_mono_wealth_witness :
    indirectUtility cd.uTotal p 2 ≤ indirectUtility cd.uTotal p 4 :=
  indirectUtility_mono_wealth cd.uTotal_continuous hp_pos (by norm_num) (by norm_num)

/-- **Argmax characterization.** Preference-based demand equals utility maximization. -/
theorem mem_argmaxRel_iff_witness {x : Fin 2 → ℝ} :
    x ∈ argmaxRel (preferenceOfUtilityIn cd.uTotal) (budgetSetAt p w)
      ↔ x ∈ budgetSetAt p w ∧ IsMaxOn cd.uTotal (budgetSetAt p w) x :=
  mem_argmaxRel_preferenceOfUtilityIn_iff

/-! ## Roy derivative inputs (`Roy.*`) on the concrete objective/budget -/

/-- **`dotL_apply` on the concrete price covector.** `dotL p y = p ⬝ᵥ y`. -/
theorem dotL_apply_witness (y : Fin 2 → ℝ) : dotL p y = p ⬝ᵥ y :=
  dotL_apply p y

/-- **Objective differentiability.** The UMP objective `(x, θ) ↦ u x` is jointly differentiable. -/
theorem hasFDerivAt_obj_witness :
    HasFDerivAt
      (fun pr : (Fin 2 → ℝ) × Param 2 => obj cd.uTotal pr.1 pr.2)
      (objFDeriv (dotL fun l => cd.α l / cdDemand cd (p, w) l * cd.uTotal (cdDemand cd (p, w))))
      (cdDemand cd (p, w), (p, w)) := by
  have hx_pos : ∀ l, 0 < cdDemand cd (p, w) l := by
    intro l
    have hA : 0 < ∑ i, cd.α i := by
      simp only [cd, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    exact div_pos (mul_pos (div_pos (cd.α_pos l) hA) hw_pos) (hp_pos l)
  exact hasFDerivAt_obj (hasFDerivAt_uTotal_pos cd hx_pos) (p, w)

/-- **Budget differentiability.** The budget constraint is jointly differentiable. -/
theorem hasFDerivAt_budget_witness :
    HasFDerivAt
      (fun pr : (Fin 2 → ℝ) × Param 2 => con none pr.1 pr.2)
      (conFDeriv (cdDemand cd (p, w)) p none) (cdDemand cd (p, w), (p, w)) :=
  hasFDerivAt_budget (cdDemand cd (p, w)) p w

/-- **All constraints differentiable.** Every UMP constraint is jointly differentiable. -/
theorem hasFDerivAt_con_witness (i : CIdx 2) :
    HasFDerivAt
      (fun pr : (Fin 2 → ℝ) × Param 2 => con i pr.1 pr.2)
      (conFDeriv (cdDemand cd (p, w)) p i) (cdDemand cd (p, w), (p, w)) :=
  hasFDerivAt_con (cdDemand cd (p, w)) p w i

/-! ## The Roy sign check on the closed form -/

/-- **Demand anchor (good x).** `x*_x = a·w/p_x = 1/2·4/1 = 2`. -/
theorem cdDemand_anchor : cdDemand cd (p, w) 0 = 2 := by
  simp only [cdDemand, cd, p, w, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Demand anchor (good y).** `x*_y = (1−a)·w/p_y = 1/2·4/4 = 1/2`. -/
theorem cdDemand_anchor_1 : cdDemand cd (p, w) 1 = 1 / 2 := by
  simp only [cdDemand, cd, p, w, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Indirect-utility anchor.** `v(p, w) = w·(a/p_x)^a·((1−a)/p_y)^(1−a)
= 4·(1/2)^(1/2)·(1/8)^(1/2) = 1`. -/
theorem indirectUtility_anchor : indirectUtility cd.uTotal p w = 1 := by
  rw [indirectUtility_eq_witness]
  -- demand is `(2, 1/2)`, so `u = max(2,0)^(1/2)·max(1/2,0)^(1/2) = (2·1/2)^(1/2) = 1`
  have hd0 : cdDemand cd (p, w) 0 = 2 := cdDemand_anchor
  have hd1 : cdDemand cd (p, w) 1 = 1 / 2 := cdDemand_anchor_1
  rw [CobbDouglasUtility.uTotal_def, Fin.prod_univ_two, hd0, hd1]
  simp only [cd, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [max_eq_left (by norm_num), max_eq_left (by norm_num),
    ← Real.mul_rpow (by norm_num) (by norm_num)]
  norm_num

/-- **Roy's identity (value-function form), concrete.** The identity from
`cobbDouglas_roy_identity_indirectUtility`, instantiated on the concrete consumer. -/
theorem roy_identity_witness :
    ∀ l, cdDemand cd (p, w) l
      = - (deriv (fun w' => indirectUtility cd.uTotal p w') w)⁻¹ *
          (fderiv ℝ (fun q => indirectUtility cd.uTotal q w) p (Pi.single l 1)) :=
  cobbDouglas_roy_identity_indirectUtility cd (by norm_num) hp_pos hw_pos

/-- **The wealth partial.** `∂v/∂w = v/w = 1/4` at the anchor. -/
theorem roy_wealth_deriv_anchor :
    deriv (fun w' => indirectUtility cd.uTotal p w') w = 1 / 4 := by
  -- Near `w = 4`, the value along the wealth slice equals the linear closed form `w' ↦ w'/4`.
  -- (demand coords `w'/2` and `w'/8`;
  --  `uTotal = (w'/2)^(1/2)·(w'/8)^(1/2) = (w'²/16)^(1/2) = w'/4`).
  have hslice : (fun w' => indirectUtility cd.uTotal p w') =ᶠ[nhds w] (fun w' => w' / 4) := by
    filter_upwards [Ioi_mem_nhds hw_pos] with w' hw'
    have hw'pos : 0 < w' := hw'
    rw [indirectUtility_cdDemand cd (by norm_num) hp_pos hw'pos]
    have hd0 : cdDemand cd (p, w') 0 = w' / 2 := by
      simp only [cdDemand, cd, p, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]; norm_num; ring
    have hd1 : cdDemand cd (p, w') 1 = w' / 8 := by
      simp only [cdDemand, cd, p, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one]; norm_num; ring
    rw [CobbDouglasUtility.uTotal_def, Fin.prod_univ_two, hd0, hd1]
    simp only [cd, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [max_eq_left (by positivity), max_eq_left (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    rw [show w' / 2 * (w' / 8) = (w' / 4) ^ 2 by ring, ← Real.rpow_natCast (w' / 4) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hslice.deriv_eq, deriv_div_const, deriv_id'']

/-- The price slice `q ↦ v(q, w)` agrees near `p` with the closed form
`q ↦ 2·(q 0)^(−1/2)·(q 1)^(−1/2)` (each demand coord is `(1/2)·w/q l = 2/q l` at `w = 4`, and
`(2/q l)^(1/2) = 2^(1/2)·(q l)^(−1/2)`, with the two `2^(1/2)` factors collapsing to `2`). -/
private theorem price_slice_closed :
    (fun q : Fin 2 → ℝ => indirectUtility cd.uTotal q w)
      =ᶠ[nhds p]
      (fun q : Fin 2 → ℝ => 2 * ((q 0) ^ (-(1 / 2) : ℝ) * (q 1) ^ (-(1 / 2) : ℝ))) := by
  have hposev : ∀ᶠ q : Fin 2 → ℝ in nhds p, ∀ l, 0 < q l :=
    Filter.eventually_all.2 fun l =>
      (continuous_apply l).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (hp_pos l))
  filter_upwards [hposev] with q hq
  rw [indirectUtility_cdDemand cd (by norm_num) hq hw_pos]
  have hd0 : cdDemand cd (q, w) 0 = 2 / q 0 := by
    simp only [cdDemand, cd, w, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]; norm_num
  have hd1 : cdDemand cd (q, w) 1 = 2 / q 1 := by
    simp only [cdDemand, cd, w, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]; norm_num
  rw [CobbDouglasUtility.uTotal_def, Fin.prod_univ_two, hd0, hd1]
  simp only [cd, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [max_eq_left (by have := hq 0; positivity), max_eq_left (by have := hq 1; positivity)]
  -- `(2/q l)^(1/2) = 2^(1/2)·(q l)^(−1/2)`, then `2^(1/2)·2^(1/2) = 2`.
  rw [Real.div_rpow (by norm_num) (hq 0).le, Real.div_rpow (by norm_num) (hq 1).le]
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg (hq 0).le, ← Real.rpow_neg (hq 1).le]
  have h2 : (2 : ℝ) ^ ((1 : ℝ) * 2⁻¹) * (2 : ℝ) ^ ((1 : ℝ) * 2⁻¹) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  -- regroup the two `2^(1/2)` factors and collapse them via `h2`.
  rw [show (2 : ℝ) ^ ((1 : ℝ) * 2⁻¹) * (q 0) ^ (-((1 : ℝ) * 2⁻¹)) *
        ((2 : ℝ) ^ ((1 : ℝ) * 2⁻¹) * (q 1) ^ (-((1 : ℝ) * 2⁻¹)))
      = ((2 : ℝ) ^ ((1 : ℝ) * 2⁻¹) * (2 : ℝ) ^ ((1 : ℝ) * 2⁻¹)) *
        ((q 0) ^ (-((1 : ℝ) * 2⁻¹)) * (q 1) ^ (-((1 : ℝ) * 2⁻¹))) by ring, h2]

/-- **The price partial (good x).** `∂v/∂p_x = −a·v/p_x = −1/2` at the anchor. -/
theorem roy_price_deriv_anchor :
    fderiv ℝ (fun q => indirectUtility cd.uTotal q w) p (Pi.single 0 1) = -(1 / 2) := by
  -- Transport the `fderiv` to the closed form, pull out the constant `2`, then differentiate the
  -- product of powers via the coordinate projection and the power rule (no inverse rule needed).
  rw [price_slice_closed.fderiv_eq]
  have hp0 : p 0 = 1 := rfl
  have hp1 : p 1 = 4 := rfl
  have hfac0 : HasFDerivAt (fun q : Fin 2 → ℝ => (q 0) ^ (-(1 / 2) : ℝ))
      ((-(1 / 2) * (p 0) ^ (-(1 / 2) - 1 : ℝ)) • proj (R := ℝ) (φ := fun _ => ℝ) 0) p :=
    ((proj (R := ℝ) (φ := fun _ => ℝ) 0).hasFDerivAt).rpow_const
      (Or.inl (by rw [hp0]; norm_num))
  have hfac1 : HasFDerivAt (fun q : Fin 2 → ℝ => (q 1) ^ (-(1 / 2) : ℝ))
      ((-(1 / 2) * (p 1) ^ (-(1 / 2) - 1 : ℝ)) • proj (R := ℝ) (φ := fun _ => ℝ) 1) p :=
    ((proj (R := ℝ) (φ := fun _ => ℝ) 1).hasFDerivAt).rpow_const
      (Or.inl (by rw [hp1]; norm_num))
  have hgrad : HasFDerivAt
      (fun q : Fin 2 → ℝ => 2 * ((q 0) ^ (-(1 / 2) : ℝ) * (q 1) ^ (-(1 / 2) : ℝ)))
      ((2 : ℝ) • ((p 0) ^ (-(1 / 2) : ℝ) • (-(1 / 2) * (p 1) ^ (-(1 / 2) - 1 : ℝ)) •
          proj (R := ℝ) (φ := fun _ => ℝ) 1
        + (p 1) ^ (-(1 / 2) : ℝ) • (-(1 / 2) * (p 0) ^ (-(1 / 2) - 1 : ℝ)) •
          proj (R := ℝ) (φ := fun _ => ℝ) 0)) p := (hfac0.mul hfac1).const_mul 2
  rw [hgrad.fderiv]
  -- Evaluate the product-rule covector at the direction `Pi.single 0 1`.
  -- The `q 1` factor's derivative kills this direction (`proj 1 (single 0 1) = 0`); the `q 0`
  -- factor contributes `2·4^(−1/2)·(−1/2·1^(−3/2)) = 2·(1/2)·(−1/2) = −1/2`.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, hp0, hp1,
    Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [show (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast 2 2,
      ← Real.rpow_mul (by norm_num)]; norm_num [Real.rpow_neg]]
  norm_num

/-- **The price partial (good y).** `∂v/∂p_y = −(1−a)·v/p_y = −1/8` at the anchor (asymmetric:
distinct from `∂v/∂p_x = −1/2`, so a good-coordinate swap is caught). -/
theorem roy_price_deriv_anchor_1 :
    fderiv ℝ (fun q => indirectUtility cd.uTotal q w) p (Pi.single 1 1) = -(1 / 8) := by
  rw [price_slice_closed.fderiv_eq]
  have hp0 : p 0 = 1 := rfl
  have hp1 : p 1 = 4 := rfl
  have hfac0 : HasFDerivAt (fun q : Fin 2 → ℝ => (q 0) ^ (-(1 / 2) : ℝ))
      ((-(1 / 2) * (p 0) ^ (-(1 / 2) - 1 : ℝ)) • proj (R := ℝ) (φ := fun _ => ℝ) 0) p :=
    ((proj (R := ℝ) (φ := fun _ => ℝ) 0).hasFDerivAt).rpow_const
      (Or.inl (by rw [hp0]; norm_num))
  have hfac1 : HasFDerivAt (fun q : Fin 2 → ℝ => (q 1) ^ (-(1 / 2) : ℝ))
      ((-(1 / 2) * (p 1) ^ (-(1 / 2) - 1 : ℝ)) • proj (R := ℝ) (φ := fun _ => ℝ) 1) p :=
    ((proj (R := ℝ) (φ := fun _ => ℝ) 1).hasFDerivAt).rpow_const
      (Or.inl (by rw [hp1]; norm_num))
  have hgrad : HasFDerivAt
      (fun q : Fin 2 → ℝ => 2 * ((q 0) ^ (-(1 / 2) : ℝ) * (q 1) ^ (-(1 / 2) : ℝ)))
      ((2 : ℝ) • ((p 0) ^ (-(1 / 2) : ℝ) • (-(1 / 2) * (p 1) ^ (-(1 / 2) - 1 : ℝ)) •
          proj (R := ℝ) (φ := fun _ => ℝ) 1
        + (p 1) ^ (-(1 / 2) : ℝ) • (-(1 / 2) * (p 0) ^ (-(1 / 2) - 1 : ℝ)) •
          proj (R := ℝ) (φ := fun _ => ℝ) 0)) p := (hfac0.mul hfac1).const_mul 2
  rw [hgrad.fderiv]
  -- Direction `Pi.single 1 1`: the `q 0` factor's derivative is killed (`proj 0 (single 1 1) = 0`);
  -- the `q 1` factor contributes `2·1^(−1/2)·(−1/2·4^(−3/2)) = 2·1·(−1/2)·(1/8) = −1/8`.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, hp0, hp1,
    Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rw [show (4 : ℝ) ^ (-(1 / 2) - 1 : ℝ) = 1 / 8 by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast 2 2,
      ← Real.rpow_mul (by norm_num)]; norm_num [Real.rpow_neg]]
  norm_num

/-- Instantiates `roy_identity_indirectUtility` directly (not the example wrapper) on the concrete
symmetric Cobb–Douglas consumer, verifying the value-function form of Roy's identity. -/
theorem roy_identity_indirectUtility_witness :
    ∀ l, cdDemand cd (p, w) l
      = - (deriv (fun w' => indirectUtility cd.uTotal p w') w)⁻¹ *
          (fderiv ℝ (fun q => indirectUtility cd.uTotal q w) p (Pi.single l 1)) := by
  haveI : Nonempty (Fin 2) := Fin.pos_iff_nonempty.mp (by norm_num)
  have hA : 0 < ∑ i, cd.α i := Finset.sum_pos (fun i _ => cd.α_pos i) Finset.univ_nonempty
  -- Demand is strictly interior.
  have hx_pos : ∀ l, 0 < cdDemand cd (p, w) l := fun l =>
    div_pos (mul_pos (div_pos (cd.α_pos l) hA) hw_pos) (hp_pos l)
  -- Demand is a budget-feasible maximizer.
  have hmem : cdDemand cd (p, w)
      ∈ argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt p w) := by
    rw [cd.argmaxRel_budgetSetAt (by norm_num) hp_pos hw_pos]
    exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hxmem, hmax⟩ := mem_argmaxRel_preferenceOfUtilityIn_iff.mp hmem
  -- Gradient of `uTotal` at demand.
  have hu : HasFDerivAt cd.uTotal
      (dotL fun l => cd.α l / cdDemand cd (p, w) l * cd.uTotal (cdDemand cd (p, w)))
      (cdDemand cd (p, w)) := hasFDerivAt_uTotal_pos cd hx_pos
  -- Demand smoothness.
  have hxs : HasFDerivAt (cdDemand cd) (fderiv ℝ (cdDemand cd) (p, w)) (p, w) :=
    (differentiableAt_cdDemand cd hp_pos w).hasFDerivAt
  -- Budget binds along the demand selection near `(p, w)`.
  have hbinds : ∀ᶠ θ in nhds ((p, w) : Param 2), θ.1 ⬝ᵥ cdDemand cd θ = θ.2 := by
    have hposev : ∀ᶠ θ in nhds ((p, w) : Param 2), ∀ l, 0 < θ.1 l :=
      Filter.eventually_all.2 fun l =>
        ((continuous_apply l).comp continuous_fst).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds (hp_pos l))
    have hsum1 : ∑ l, cd.α l / (∑ i, cd.α i) = 1 := by rw [← Finset.sum_div, div_self hA.ne']
    filter_upwards [hposev] with θ hθ
    have key : (∑ l, θ.1 l * cdDemand cd θ l) = (∑ l, cd.α l / (∑ i, cd.α i)) * θ.2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [cdDemand]
      field_simp [(hθ l).ne']
    rw [dotProduct, key, hsum1, one_mul]
  -- Interior demand never hits a nonnegativity wall.
  have hcorner : ∀ l, cdDemand cd (p, w) l = 0 →
      (∀ᶠ θ in nhds ((p, w) : Param 2), cdDemand cd θ l = 0) := fun l hl =>
    absurd hl (hx_pos l).ne'
  -- Extract KKT multipliers.
  obtain ⟨lam, hlam_nonneg, hcs_budget, hcs_nonneg, hstat⟩ :=
    kkt_of_isMaxOn_budget hu hxmem hmax
  -- The budget multiplier is strictly positive.
  have hlamB : 0 < lam none := by
    set x₀ := cdDemand cd (p, w)
    set g : Fin 2 → ℝ := fun l => cd.α l / x₀ l * cd.uTotal x₀
    have hsome0 : ∀ l, lam (some l) = 0 := fun l =>
      (mul_eq_zero.mp (hcs_nonneg l)).resolve_right (hx_pos l).ne'
    have hobj_red : (objFDeriv (dotL g)).comp (inl ℝ (Fin 2 → ℝ) (Param 2)) = dotL g := by
      ext d; simp [objFDeriv]
    have hcon_none : (conFDeriv x₀ p none).comp (inl ℝ (Fin 2 → ℝ) (Param 2)) = dotL p := by
      ext d; simp [conFDeriv]
    have hcon_some : ∀ l, (conFDeriv x₀ p (some l)).comp (inl ℝ (Fin 2 → ℝ) (Param 2))
        = -(proj (R := ℝ) (φ := fun _ => ℝ) l) := by
      intro l; ext d; simp [conFDeriv]
    have hDu_eq : dotL g = lam none • dotL p := by
      rw [← hobj_red, hstat, Fintype.sum_option, hcon_none]
      simp only [hcon_some, hsome0, zero_smul, Finset.sum_const_zero, add_zero]
    obtain ⟨k⟩ : Nonempty (Fin 2) := inferInstance
    have hk : g k = lam none * p k := by
      have := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] ℝ => T (Pi.single k 1)) hDu_eq
      simpa [dotL_apply, dotProduct_single] using this
    have hgk_pos : 0 < g k :=
      mul_pos (div_pos (cd.α_pos k) (hx_pos k)) (cd.uTotal_pos_iff.mpr hx_pos)
    rw [eq_div_of_mul_eq (hp_pos k).ne' hk.symm]
    exact div_pos hgk_pos (hp_pos k)
  -- Build the `h_bind` hypothesis for `roy_identity_indirectUtility`.
  have h_bind : ∀ i, lam i = 0 ∨
      (∀ᶠ θ in nhds ((p, w) : Param 2), con i (cdDemand cd θ) θ = 0) := by
    intro i
    cases i with
    | none => exact Or.inr (by filter_upwards [hbinds] with θ hθ; simp [con, hθ])
    | some l =>
        by_cases hxl : cdDemand cd (p, w) l = 0
        · exact Or.inr (by
            filter_upwards [hcorner l hxl] with θ hθ; simp [con, hθ])
        · exact Or.inl (by
            have := hcs_nonneg l
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hxl)
  -- Local optimality near `(p, w)`: `cdDemand cd θ` is budget-feasible and maximal nearby.
  have hloc : ∀ᶠ θ in nhds ((p, w) : Param 2),
      cdDemand cd θ ∈ budgetSetAt θ.1 θ.2 ∧
        IsMaxOn cd.uTotal (budgetSetAt θ.1 θ.2) (cdDemand cd θ) := by
    have hposev : ∀ᶠ θ in nhds ((p, w) : Param 2), ∀ l, 0 < θ.1 l :=
      Filter.eventually_all.2 fun l =>
        ((continuous_apply l).comp continuous_fst).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds (hp_pos l))
    have hwev : ∀ᶠ θ in nhds ((p, w) : Param 2), 0 < θ.2 :=
      continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hw_pos)
    filter_upwards [hposev, hwev] with θ hθp hθw
    have hmem_θ : cdDemand cd θ
        ∈ argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt θ.1 θ.2) := by
      rw [cd.argmaxRel_budgetSetAt (by norm_num) hθp hθw]
      exact Set.mem_singleton_iff.mpr rfl
    exact mem_argmaxRel_preferenceOfUtilityIn_iff.mp hmem_θ
  -- Local value-equality: `uTotal (cdDemand cd θ) = indirectUtility u θ.1 θ.2` near `(p, w)`.
  have hval : ∀ᶠ θ in nhds ((p, w) : Param 2),
      cd.uTotal (cdDemand cd θ) = indirectUtility cd.uTotal θ.1 θ.2 :=
    eventuallyEq_indirectUtility_of_localMaxOn (cdDemand cd) hloc
  -- Apply `roy_identity_indirectUtility` directly.
  exact roy_identity_indirectUtility cd.uTotal (cdDemand cd) lam p w hlamB _
    hu _ hxs hstat h_bind hval

/-- **Sign check (good x).** Feed the *actual* Roy identity witness through the independently
computed derivative anchors: `x*_x = −(∂v/∂w)⁻¹·(∂v/∂p_x) = −(1/4)⁻¹·(−1/2) = 2 = x*_x`. The minus
sign and the two-partial placement are both forced — a broken Roy theorem, a dropped minus, or a
`∂/∂p ↔ ∂/∂w` swap would make the left side disagree with the demand anchor `= 2`. -/
theorem roy_sign_check :
    cdDemand cd (p, w) 0 = - ((1 / 4 : ℝ))⁻¹ * (-(1 / 2)) := by
  have h := roy_identity_indirectUtility_witness 0
  rw [roy_wealth_deriv_anchor, roy_price_deriv_anchor] at h
  exact h

/-- **Sign check (good y).** The same identity for good `y` through its anchors:
`x*_y = −(∂v/∂w)⁻¹·(∂v/∂p_y) = −(1/4)⁻¹·(−1/8) = 1/2 = x*_y`. -/
theorem roy_sign_check_1 :
    cdDemand cd (p, w) 1 = - ((1 / 4 : ℝ))⁻¹ * (-(1 / 8)) := by
  have h := roy_identity_indirectUtility_witness 1
  rw [roy_wealth_deriv_anchor, roy_price_deriv_anchor_1] at h
  exact h

/-- **Discrimination check.** The Roy-recovered demand for good `x` equals the true demand `2`,
while
the **swapped** formula `−(∂v/∂w)/(∂v/∂p_x) = −(1/4)/(−1/2) = 1/2` does *not* — confirming this
asymmetric anchor catches the `∂/∂p ↔ ∂/∂w` swap (it would have been invisible at a symmetric unit
point, where both equal `1`). -/
theorem roy_swap_discriminates :
    cdDemand cd (p, w) 0 ≠ - ((-(1 / 2) : ℝ))⁻¹ * (1 / 4) := by
  rw [cdDemand_anchor]; norm_num

end EconlibTest.Equilibrium.IndirectUtilityRoy

end
