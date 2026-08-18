import Mathlib
import Econlib

/-!
# Roy's identity for Cobb–Douglas demand (acceptance instance)

This is the **non-vacuity witness** for the library's Roy's-identity API
(`Econlib.Equilibrium.roy_identity_of_isMaxOn`): the abstract regularity hypotheses are discharged
end-to-end for the canonical smooth example, Cobb–Douglas, whose interior demand has the textbook
closed form `x*_l(p,w) = (α_l / ∑α) · w / p_l` (`Econlib.Equilibrium.CobbDouglasUtility`,
`argmaxRel_budgetSetAt`).

The two analytic inputs are proved here as standalone facts:

* `hasFDerivAt_uTotal_pos` — the Cobb–Douglas gradient on the positive orthant, `∇u(x)_l =
  α_l / x_l · u(x)` (the truncated `uTotal` agrees with the smooth power product near an interior
  point, where the finite product rule applies).
* `differentiableAt_cdDemand` — smoothness of the closed-form demand in `(p, w)`.

With these, every hypothesis of `roy_identity_of_isMaxOn` is dischargeable: the budget binds along
the whole demand selection (`hbinds`), interior demand never touches a nonnegativity wall so those
constraints are vacuous (`hcorner`), and the budget multiplier is positive because interior
stationarity forces `∇u = λ p` with `∇u ≫ 0` (`hlampos`). The payoff `cobbDouglas_roy_identity`
is Roy's identity for Cobb–Douglas demand.

## Main statements

* `cobbDouglas_roy_identity` — Roy's identity holds along the closed-form Cobb–Douglas demand
  selection (the derivatives are of `uTotal ∘ cdDemand`).
* `cobbDouglas_roy_identity_indirectUtility` — the same identity stated with the indirect
  utility (value function) `indirectUtility cd.uTotal` in both derivative slots, via the
  neighborhood value-equality `v(p,w) = u(x*(p,w))`.
-/

namespace EconlibExamples.Equilibrium.CobbDouglasRoy

open Econlib.Equilibrium Econlib.Equilibrium.Roy Econlib.Preferences Econlib.Optimization
open Matrix ContinuousLinearMap

variable {L : ℕ}

/-! ## The Cobb–Douglas gradient on the interior -/

/-- **Cobb–Douglas gradient.** At a strictly positive bundle the (total) Cobb–Douglas utility is
differentiable with gradient `∇u(x)_l = α_l / x_l · u(x)`, packaged as the covector
`dotL (fun l => α_l / x_l · u(x))`. Near an interior point the truncation `max · 0` is inert, so
`uTotal` agrees with the smooth power product `∏ l, (x l)^(α l)` and the finite product rule
applies. -/
lemma hasFDerivAt_uTotal_pos (cd : CobbDouglasUtility L) {x : Fin L → ℝ} (hx : ∀ l, 0 < x l) :
    HasFDerivAt cd.uTotal (dotL fun l => cd.α l / x l * cd.uTotal x) x := by
  -- Near `x` every coordinate stays positive, so `uTotal` is the smooth power product there.
  have hpos_ev : ∀ᶠ y in nhds x, ∀ l, 0 < y l :=
    Filter.eventually_all.2 fun l =>
      (continuous_apply l).continuousAt.preimage_mem_nhds (Ioi_mem_nhds (hx l))
  -- Coordinatewise power rule.
  have hcoord : ∀ l : Fin L,
      HasFDerivAt (fun y : Fin L → ℝ => (y l) ^ (cd.α l))
        ((cd.α l * x l ^ (cd.α l - 1)) • proj (R := ℝ) (φ := fun _ => ℝ) l) x := by
    intro l
    exact (Real.hasDerivAt_rpow_const (p := cd.α l) (Or.inl (hx l).ne')).comp_hasFDerivAt x
      (proj (R := ℝ) (φ := fun _ => ℝ) l).hasFDerivAt
  -- Finite product rule for `∏ l, (y l)^(α l)`.
  have hprod := HasFDerivAt.finset_prod (u := (Finset.univ : Finset (Fin L)))
    (g := fun l (y : Fin L → ℝ) => (y l) ^ cd.α l)
    (g' := fun l => (cd.α l * x l ^ (cd.α l - 1)) • proj (R := ℝ) (φ := fun _ => ℝ) l)
    (fun l _ => hcoord l)
  refine (hprod.congr_of_eventuallyEq
    (hpos_ev.mono fun y hy => cd.uTotal_eq_prod_of_pos hy)).congr_fderiv
    (Finset.sum_congr rfl fun l _ => ?_)
  rw [smul_smul, cd.uTotal_eq_prod_of_pos hx,
    ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ cd.α j) (Finset.mem_univ l),
    Real.rpow_sub (hx l) (cd.α l) 1, Real.rpow_one]
  congr 1
  ring

/-! ## The closed-form Cobb–Douglas demand and its smoothness -/

/-- The closed-form Cobb–Douglas Marshallian demand **formula**: spend the normalized weight
`α_l / ∑α` of wealth on good `l`. This is a bare algebraic expression (total division, no
hypotheses); it coincides with the actual budget-set argmax — the singleton value of
`CobbDouglasUtility.argmaxRel_budgetSetAt` — only under the positive-price/positive-wealth
hypotheses imposed downstream. -/
noncomputable def cdDemand (cd : CobbDouglasUtility L) (θ : Param L) (l : Fin L) : ℝ :=
  cd.α l / (∑ i, cd.α i) * θ.2 / θ.1 l

/-- The closed-form Cobb–Douglas demand is differentiable in prices and wealth at strictly positive
prices (each coordinate is `(α_l/∑α) · w / p_l`, a ratio with nonvanishing denominator). -/
lemma differentiableAt_cdDemand (cd : CobbDouglasUtility L) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) (w : ℝ) : DifferentiableAt ℝ (cdDemand cd) (p, w) := by
  refine differentiableAt_pi'' fun l => ?_
  have h1 : DifferentiableAt ℝ (fun θ : Param L => θ.1 l) (p, w) :=
    ((proj (R := ℝ) (φ := fun _ => ℝ) l).comp (fst ℝ (Fin L → ℝ) ℝ)).differentiableAt
  have hnum : DifferentiableAt ℝ (fun θ : Param L => cd.α l / (∑ i, cd.α i) * θ.2) (p, w) :=
    (differentiableAt_const _).mul differentiableAt_snd
  exact hnum.mul (h1.inv (hp l).ne')

/-! ## The acceptance instance -/

/-- **Roy's identity for Cobb–Douglas demand** (selection form). For any Cobb–Douglas consumer
(`hL : 0 < L` goods) at strictly positive prices `p` and wealth `w > 0`, the closed-form Marshallian
demand satisfies Roy's identity with the derivatives taken of the utility *along the closed-form
demand selection* `uTotal ∘ cdDemand`:
`x*_l(p,w) = −(∂_{p_l}(u∘x*))/(∂_w(u∘x*))`. This certifies that `roy_identity_of_isMaxOn` is
non-vacuous. The value-function form — with the indirect utility `v = indirectUtility` in
place of `u∘x*` — is `cobbDouglas_roy_identity_indirectUtility`. -/
theorem cobbDouglas_roy_identity (cd : CobbDouglasUtility L) (hL : 0 < L) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 < w) :
    ∀ l, cdDemand cd (p, w) l
      = - (deriv (fun w' => cd.uTotal (cdDemand cd (p, w'))) w)⁻¹ *
          (fderiv ℝ (fun q => cd.uTotal (cdDemand cd (q, w))) p (Pi.single l 1)) := by
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  have hA : 0 < ∑ i, cd.α i := Finset.sum_pos (fun i _ => cd.α_pos i) Finset.univ_nonempty
  -- The demand is strictly interior.
  have hx_pos : ∀ l, 0 < cdDemand cd (p, w) l := fun l =>
    div_pos (mul_pos (div_pos (cd.α_pos l) hA) hw) (hp l)
  -- Demand is a budget-feasible maximizer (via the closed-form argmax).
  have hmem : cdDemand cd (p, w)
      ∈ argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt p w) := by
    rw [cd.argmaxRel_budgetSetAt hL hp hw]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hxmem, hmax⟩ := mem_argmaxRel_preferenceOfUtilityIn_iff.mp hmem
  -- The Cobb–Douglas gradient at the demand point.
  have hu : HasFDerivAt cd.uTotal
      (dotL fun l => cd.α l / cdDemand cd (p, w) l * cd.uTotal (cdDemand cd (p, w)))
      (cdDemand cd (p, w)) := hasFDerivAt_uTotal_pos cd hx_pos
  -- Demand smoothness.
  have hxs : HasFDerivAt (cdDemand cd) (fderiv ℝ (cdDemand cd) (p, w)) (p, w) :=
    (differentiableAt_cdDemand cd hp w).hasFDerivAt
  -- Budget binds along the whole demand selection near `(p, w)`.
  have hbinds : ∀ᶠ θ in nhds ((p, w) : Param L), θ.1 ⬝ᵥ cdDemand cd θ = θ.2 := by
    have hposev : ∀ᶠ θ in nhds ((p, w) : Param L), ∀ l, 0 < θ.1 l :=
      Filter.eventually_all.2 fun l =>
        ((continuous_apply l).comp continuous_fst).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds (hp l))
    have hsum1 : ∑ l, cd.α l / (∑ i, cd.α i) = 1 := by rw [← Finset.sum_div, div_self hA.ne']
    filter_upwards [hposev] with θ hθ
    have key : (∑ l, θ.1 l * cdDemand cd θ l) = (∑ l, cd.α l / (∑ i, cd.α i)) * θ.2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [cdDemand]
      field_simp [(hθ l).ne']
    rw [dotProduct, key, hsum1, one_mul]
  -- Interior demand never hits a nonnegativity wall, so those constraints are vacuous.
  have hcorner : ∀ l, cdDemand cd (p, w) l = 0 →
      (∀ᶠ θ in nhds ((p, w) : Param L), cdDemand cd θ l = 0) := fun l hl =>
    absurd hl (hx_pos l).ne'
  -- The budget multiplier is strictly positive: interior stationarity forces `∇u = λ p`, `∇u ≫ 0`.
  have hlampos : ∀ lam : CIdx L → ℝ,
      (objFDeriv (dotL fun l =>
          cd.α l / cdDemand cd (p, w) l * cd.uTotal (cdDemand cd (p, w)))).comp
          (inl ℝ (Fin L → ℝ) (Param L))
        = ∑ i, lam i • (conFDeriv (cdDemand cd (p, w)) p i).comp (inl ℝ (Fin L → ℝ) (Param L)) →
      lam none * (p ⬝ᵥ cdDemand cd (p, w) - w) = 0 →
      (∀ l, lam (some l) * cdDemand cd (p, w) l = 0) → (∀ i, 0 ≤ lam i) → 0 < lam none := by
    intro lam hstat _ hcs_n _
    set x₀ := cdDemand cd (p, w) with hx₀
    set g : Fin L → ℝ := fun l => cd.α l / x₀ l * cd.uTotal x₀ with hg
    -- Interior ⇒ all nonnegativity multipliers vanish.
    have hsome0 : ∀ l, lam (some l) = 0 := fun l =>
      (mul_eq_zero.mp (hcs_n l)).resolve_right (hx_pos l).ne'
    -- Reduce the joint stationarity to its `x`-component.
    have hobj_red : (objFDeriv (dotL g)).comp (inl ℝ (Fin L → ℝ) (Param L)) = dotL g := by
      ext d; simp [objFDeriv]
    have hcon_none : (conFDeriv x₀ p none).comp (inl ℝ (Fin L → ℝ) (Param L)) = dotL p := by
      ext d; simp [conFDeriv]
    have hcon_some : ∀ l, (conFDeriv x₀ p (some l)).comp (inl ℝ (Fin L → ℝ) (Param L))
        = -(proj (R := ℝ) (φ := fun _ => ℝ) l) := by
      intro l; ext d; simp [conFDeriv]
    have hDu_eq : dotL g = lam none • dotL p := by
      rw [← hobj_red, hstat, Fintype.sum_option, hcon_none]
      simp only [hcon_some, hsome0, zero_smul, Finset.sum_const_zero, add_zero]
    -- Evaluate at a coordinate `e_k`: `∇u_k = λ p_k`.
    obtain ⟨k⟩ : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
    have hk : g k = lam none * p k := by
      have := congrArg (fun T : (Fin L → ℝ) →L[ℝ] ℝ => T (Pi.single k 1)) hDu_eq
      simpa [dotL_apply, dotProduct_single] using this
    have hgk_pos : 0 < g k :=
      mul_pos (div_pos (cd.α_pos k) (hx_pos k)) (cd.uTotal_pos_iff.mpr hx_pos)
    rw [eq_div_of_mul_eq (hp k).ne' hk.symm]
    exact div_pos hgk_pos (hp k)
  -- Assemble Roy's identity from the maximizer interface.
  exact roy_identity_of_isMaxOn (cdDemand cd) hu hxmem hmax hxs hbinds hcorner hlampos

/-- The Cobb–Douglas indirect utility is realized along the closed-form demand: at positive wealth
`v(p,w) = u(x*(p,w))` (the value characterization `indirectUtility_eq_of_isMaxOn` applied to the
closed-form argmax). -/
lemma indirectUtility_cdDemand (cd : CobbDouglasUtility L) (hL : 0 < L) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 < w) :
    indirectUtility cd.uTotal p w = cd.uTotal (cdDemand cd (p, w)) := by
  have hmem : cdDemand cd (p, w)
      ∈ argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt p w) := by
    rw [cd.argmaxRel_budgetSetAt hL hp hw]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hxmem, hmax⟩ := mem_argmaxRel_preferenceOfUtilityIn_iff.mp hmem
  exact indirectUtility_eq_of_isMaxOn hxmem hmax

/-- **The wealth-derivative in Roy's identity is `∂v/∂w`.** Near positive wealth the value along the
Cobb–Douglas demand coincides with the indirect utility, so the `deriv` appearing in
`cobbDouglas_roy_identity` is literally the marginal indirect utility of wealth. -/
lemma cobbDouglas_roy_wealth_deriv (cd : CobbDouglasUtility L) (hL : 0 < L) {p : Fin L → ℝ}
    (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 < w) :
    deriv (fun w' => cd.uTotal (cdDemand cd (p, w'))) w
      = deriv (indirectUtility cd.uTotal p) w := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioi_mem_nhds hw] with w' hw'
  exact (indirectUtility_cdDemand cd hL hp hw').symm

/-- **Roy's identity for Cobb–Douglas demand** (value-function form). The identity of
`cobbDouglas_roy_identity` holds verbatim with the indirect utility (value function)
`indirectUtility cd.uTotal` in place of `uTotal ∘ cdDemand` in both derivative slots:
`x*_l(p,w) = −(∂v/∂p_l)/(∂v/∂w)`. Near `(p, w)` the closed-form demand is a budget-feasible
maximizer (prices and wealth stay positive, so `argmaxRel_budgetSetAt` applies pointwise), hence
`uTotal (cdDemand θ) = indirectUtility cd.uTotal θ.1 θ.2` throughout a neighborhood
(`eventuallyEq_indirectUtility_of_localMaxOn`); eventually-equal functions share `deriv`/`fderiv`,
so the two derivative slots transport from the selection form. -/
theorem cobbDouglas_roy_identity_indirectUtility (cd : CobbDouglasUtility L) (hL : 0 < L)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 < w) :
    ∀ l, cdDemand cd (p, w) l
      = - (deriv (fun w' => indirectUtility cd.uTotal p w') w)⁻¹ *
          (fderiv ℝ (fun q => indirectUtility cd.uTotal q w) p (Pi.single l 1)) := by
  -- The closed-form demand is a budget-feasible maximizer throughout a neighborhood of `(p, w)`.
  have hloc : ∀ᶠ θ in nhds ((p, w) : Param L),
      cdDemand cd θ ∈ budgetSetAt θ.1 θ.2 ∧ IsMaxOn cd.uTotal (budgetSetAt θ.1 θ.2) (cdDemand cd θ)
      := by
    have hposev : ∀ᶠ θ in nhds ((p, w) : Param L), ∀ l, 0 < θ.1 l :=
      Filter.eventually_all.2 fun l =>
        ((continuous_apply l).comp continuous_fst).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds (hp l))
    have hwev : ∀ᶠ θ in nhds ((p, w) : Param L), 0 < θ.2 :=
      continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hw)
    filter_upwards [hposev, hwev] with θ hθp hθw
    have hmem : cdDemand cd θ
        ∈ argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt θ.1 θ.2) := by
      rw [cd.argmaxRel_budgetSetAt hL hθp hθw]; exact Set.mem_singleton_iff.mpr rfl
    exact mem_argmaxRel_preferenceOfUtilityIn_iff.mp hmem
  -- Value equality near `(p, w)`, and the resulting agreement of the two derivative slots.
  have hvalEq : (fun θ => cd.uTotal (cdDemand cd θ))
      =ᶠ[nhds ((p, w) : Param L)] (fun θ : Param L => indirectUtility cd.uTotal θ.1 θ.2) :=
    eventuallyEq_indirectUtility_of_localMaxOn (cdDemand cd) hloc
  have hval_w : (fun w' => cd.uTotal (cdDemand cd (p, w')))
      =ᶠ[nhds w] (fun w' => indirectUtility cd.uTotal p w') :=
    hvalEq.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto' w (p, w) rfl)
  have hval_p : (fun q => cd.uTotal (cdDemand cd (q, w)))
      =ᶠ[nhds p] (fun q => indirectUtility cd.uTotal q w) :=
    hvalEq.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto' p (p, w) rfl)
  intro l
  have hkkt := cobbDouglas_roy_identity cd hL hp hw l
  rw [hval_w.deriv_eq, hval_p.fderiv_eq] at hkkt
  exact hkkt

end EconlibExamples.Equilibrium.CobbDouglasRoy
