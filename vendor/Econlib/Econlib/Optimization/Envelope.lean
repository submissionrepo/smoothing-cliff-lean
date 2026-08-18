/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Danskin

/-!
# Economic Corollaries of Danskin's Theorem

Hotelling's lemma, Shephard's lemma, and the algebraic core of Roy's identity, obtained as
corollaries of Danskin's theorem in the smooth case with a unique optimizer.

## Main definitions

* `profitObjective`, `profitFunction`: The profit objective `⟪p, y⟫ - c(y)` and its supremum over
  outputs.
* `expendObjective`, `negExpendFunction`: The negated expenditure objective `-⟪p, x⟫` and its
  supremum over bundles.

## Main statements

* `hasGradientAt_profitFunction`: The gradient of the profit function with respect to prices equals
  the supply vector.
* `hasGradientAt_negExpendFunction`: The gradient of the negated expenditure function equals the
  negated Hicksian demand.
* `gradient_indirectUtility_of_expenditure_chain`: A calculus identity. Given the
  expenditure/indirect-utility duality and the total chain-rule decomposition of expenditure, the
  price-gradient of indirect utility is `-(∂v/∂w) · x_star`.
* `argmax_iSup_eq_setOf_isMaxOn`: The `iSup`-based argmax of `Danskin` agrees with the
  `IsMaxOn`-based `Econlib.Optimization.argmax` over `Set.univ` when the range is bounded above.

## Notes

`gradient_indirectUtility_of_expenditure_chain` is the algebraic core behind Roy's identity, not a
self-contained Roy's identity: `x_star` is an arbitrary function and the chain-rule hypothesis
already supplies the Shephard term. The Roy's identity in which `x_star` is the Marshallian demand
of a utility-maximization problem and the identity is derived is
`Econlib.Equilibrium.Roy.roy_identity`, obtained from the constrained envelope theorem
`Econlib.Optimization.hasFDerivAt_constrainedValue`.

## Tags

envelope theorem, hotelling's lemma, shephard's lemma, duality
-/

@[expose] public section

open Set Filter Topology InnerProductSpace
open Danskin

namespace Econlib.Optimization.Envelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient of the linear functional `w ↦ ⟪w, c⟫` is `c`. Shared scaffolding for the
profit/expenditure objectives, whose gradients differ only by a sign. -/
private lemma hasGradientAt_inner_left (c q : E) :
    HasGradientAt (fun w ↦ @inner ℝ E _ w c) c q := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((innerSLFlip ℝ) c).hasFDerivAt using 1
  ext w; erw [toDual_apply_apply, innerSLFlip_apply_apply, real_inner_comm]

/-! ### Hotelling's Lemma -/

section Hotelling

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
variable (Y_embed : Y → E) (cost : Y → ℝ)

/-- Profit objective: `π(p, y) = ⟪p, y⟫ - c(y)`. -/
noncomputable def profitObjective (p : E) (y : Y) : ℝ :=
  @inner ℝ E _ p (Y_embed y) - cost y

/-- Profit function: `Π(p) = sup_y π(p, y)`. -/
noncomputable def profitFunction (p : E) : ℝ :=
  valueFunction (profitObjective Y_embed cost) p

omit [CompleteSpace E] [CompactSpace Y] [Nonempty Y] in
/-- **Continuity of the profit objective in the output, at a fixed price.** With continuous
`Y_embed` and `cost`, the map `y ↦ π(p, y)` is continuous — `⟪p, ·⟫` is continuous (it is a
restriction of `continuous_inner`) and `cost` is continuous by hypothesis. This is the building
block consumers feed to `isCompact_range`/`bddAbove` so the supremum `Π(p)` is a true least upper
bound rather than the junk value of an unbounded `iSup`. -/
lemma profitObjective_continuous_right
    (h_cost_cont : Continuous cost) (h_embed_cont : Continuous Y_embed) (p : E) :
    Continuous (fun y : Y ↦ profitObjective Y_embed cost p y) := by
  unfold profitObjective
  exact (continuous_const.inner h_embed_cont).sub h_cost_cont

/-- **The profit objective on the line.** When prices and outputs are scalars (`E = ℝ`), the
abstract inner product `⟪p, y⟫` is ordinary multiplication, so the objective collapses to the
familiar `π(p, y) = p · (Y_embed y) − c(y)`. Tagged `@[simp]` so one-dimensional consumers never
have to unfold the `InnerProductSpace ℝ ℝ` instance by hand. -/
@[simp] lemma profitObjective_real {Y : Type*} (Y_embed : Y → ℝ) (cost : Y → ℝ) (p : ℝ) (y : Y) :
    profitObjective Y_embed cost p y = p * Y_embed y - cost y := by
  rw [profitObjective, mul_comm]; rfl

/-- **Hotelling's Lemma.** If the profit-maximizing output `y*` is unique at prices `p`, then the
profit function is differentiable at `p` with gradient equal to `y*`'s production vector.

Economically: The supply function equals the gradient of the profit function. -/
theorem hasGradientAt_profitFunction {X : Set E}
    (hX_open : IsOpen X)
    (h_cost_cont : Continuous cost) (h_embed_cont : Continuous Y_embed)
    (p : E) (hp : p ∈ X) (y_star : Y)
    (h_unique : argmax_iSup (profitObjective Y_embed cost) p = {y_star}) :
    HasGradientAt (profitFunction Y_embed cost) (Y_embed y_star) p := by
  apply hasGradientAt_iSup_of_unique (profitObjective Y_embed cost) (fun _ y ↦ Y_embed y) X
      hX_open ?_ ?_ ?_ p hp y_star h_unique
  · -- joint continuity of profitObjective on X × univ
    unfold ContinuousOnProd profitObjective
    apply ContinuousOn.sub
    · exact (continuous_inner.comp
        (continuous_fst.prodMk (h_embed_cont.comp continuous_snd))).continuousOn
    · exact (h_cost_cont.comp continuous_snd).continuousOn
  · -- gradient of p ↦ ⟪p, Y_embed y⟫ - cost y is Y_embed y
    intro y q _
    unfold profitObjective
    have h_inner := hasGradientAt_inner_left (Y_embed y) q
    have h_const : HasGradientAt (fun _ : E ↦ cost y) 0 q := hasGradientAt_const q (cost y)
    convert (h_inner.hasFDerivAt.sub h_const.hasFDerivAt).hasGradientAt using 1
    simp
  · exact (h_embed_cont.comp continuous_snd).continuousOn

end Hotelling

/-! ### Shephard's Lemma -/

section Shephard

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
variable (Y_embed : Y → E)

/-- Expenditure objective (negated for sup form): `-e(p, x) = -⟪p, x⟫`. -/
noncomputable def expendObjective (p : E) (x : Y) : ℝ :=
  -@inner ℝ E _ p (Y_embed x)

/-- Negated expenditure function: `-e(p) = sup_x (-⟪p, x⟫)`. -/
noncomputable def negExpendFunction (p : E) : ℝ :=
  valueFunction (expendObjective Y_embed) p

/-- **Shephard's Lemma.** If the expenditure-minimizing bundle `x*` is unique at prices `p`, then
the negated expenditure function is differentiable at `p` with gradient `-x*`.

Equivalently, `∇_p e(p, u) = x*(p, u)` (the Hicksian demand). -/
theorem hasGradientAt_negExpendFunction {X : Set E}
    (hX_open : IsOpen X)
    (h_embed_cont : Continuous Y_embed)
    (p : E) (hp : p ∈ X) (x_star : Y)
    (h_unique : argmax_iSup (expendObjective Y_embed) p = {x_star}) :
    HasGradientAt (negExpendFunction Y_embed) (-(Y_embed x_star)) p := by
  apply hasGradientAt_iSup_of_unique (expendObjective Y_embed) (fun _ x ↦ -(Y_embed x)) X
      hX_open ?_ ?_ ?_ p hp x_star h_unique
  · -- joint continuity of expendObjective on X × univ
    unfold ContinuousOnProd expendObjective
    exact (continuous_inner.comp
      (continuous_fst.prodMk (h_embed_cont.comp continuous_snd))).neg.continuousOn
  · -- gradient of p ↦ -⟪p, Y_embed x⟫ is -(Y_embed x)
    intro x q _
    unfold expendObjective
    have h_inner := hasGradientAt_inner_left (Y_embed x) q
    convert h_inner.hasFDerivAt.neg.hasGradientAt using 1
    simp
  · exact (h_embed_cont.comp continuous_snd).neg.continuousOn

end Shephard

/-! ### Indirect-utility gradient from the expenditure chain rule

The algebraic identity underlying Roy's identity. This is not a self-contained Roy's identity:
`x_star` is an arbitrary function, and the chain-rule hypothesis `h_chain` already inserts
`toDual (x_star p w)` as the price-gradient of expenditure (the Shephard term). There is no
utility-maximization problem, budget set, or demand correspondence here.

The Roy's identity in which `x_star` is the Marshallian demand of a utility-maximization problem
and the identity is derived, not assumed, is `Econlib.Equilibrium.Roy.roy_identity`, obtained by
instantiating the constrained-value envelope theorem
`Econlib.Optimization.hasFDerivAt_constrainedValue` at the consumer's problem. -/

/-- **Indirect-utility gradient from the expenditure chain rule** (a calculus identity, not a
self-contained Roy's identity — see the section note). Given indirect utility `v(p, w)`,
expenditure `e(p, u)` satisfying the duality identity `e(p, v(p, w)) = w`, and the total chain-rule
decomposition `h_chain` of `q ↦ e(q, v(q, w))` (which supplies the Shephard term
`toDual (x_star p w)` for an arbitrary `x_star`), the price-gradient of `v` is
`∇_p v(p, w) = -(∂v/∂w) · x_star(p, w)`.

The hypotheses `h_de_du` and `h_chain` encode differentiability of `e` in its utility argument and
the total chain rule decomposition for `q ↦ e(q, v(q, w))`. -/
theorem gradient_indirectUtility_of_expenditure_chain
    (v : E → ℝ → ℝ) (e : E → ℝ → ℝ) (x_star : E → ℝ → E)
    (p : E) (w u : ℝ) (hu : u = v p w)
    (h_ident : ∀ q w', e q (v q w') = w')
    (h_dv_dp : DifferentiableAt ℝ (fun q ↦ v q w) p)
    (h_dv_dw : HasDerivAt (fun w' ↦ v p w') (deriv (fun w' ↦ v p w') w) w)
    -- Differentiability of expenditure in the utility argument at (p, u)
    (h_de_du : HasDerivAt (fun u' ↦ e p u') (deriv (fun u' ↦ e p u') u) u)
    -- Chain rule decomposition: total FDeriv of q ↦ e(q, v(q,w)) =
    --   (Shephard: ∇_q e at fixed u) + (∂e/∂u) · (FDeriv of q ↦ v(q,w))
    (h_chain : HasFDerivAt (fun q ↦ e q (v q w))
      ((toDual ℝ E) (x_star p w) + (deriv (fun u' ↦ e p u') u) •
        (fderiv ℝ (fun q ↦ v q w) p)) p) :
    gradient (fun q ↦ v q w) p =
      -(deriv (fun w' ↦ v p w') w) • x_star p w := by
  set dvdw := deriv (fun w' ↦ v p w') w
  set dedu := deriv (fun u' ↦ e p u') u
  -- Step 1: The composite e(q, v(q,w)) = w is constant, so its FDeriv is 0
  have h_const : HasFDerivAt (fun q ↦ e q (v q w)) (0 : E →L[ℝ] ℝ) p := by
    have : (fun q ↦ e q (v q w)) = fun _ ↦ w := funext (fun q ↦ h_ident q w)
    rw [this]; exact hasFDerivAt_const w p
  -- Step 2: By uniqueness of FDeriv, toDual(x*) + dedu • fderiv(v) = 0
  have h_eq : (0 : StrongDual ℝ E) =
      (toDual ℝ E) (x_star p w) + dedu • (fderiv ℝ (fun q ↦ v q w) p) :=
    h_const.unique h_chain
  -- Step 3: From the identity e(p, v(p, w')) = w' for all w', derive dedu · dvdw = 1
  have h_inv : HasDerivAt (fun w' ↦ e p (v p w')) 1 w := by
    have : (fun w' ↦ e p (v p w')) = id := funext (fun w' ↦ h_ident p w')
    rw [this]; exact hasDerivAt_id w
  have h_de_du' : HasDerivAt (fun u' ↦ e p u') dedu (v p w) := by rwa [← hu]
  have h_comp_chain : HasDerivAt (fun w' ↦ e p (v p w')) (dedu * dvdw) w :=
    h_de_du'.comp w h_dv_dw
  have h_prod_one : dedu * dvdw = 1 := h_comp_chain.unique h_inv
  have hc_ne : dedu ≠ 0 := by intro hc0; simp [hc0] at h_prod_one
  -- Step 4: dedu⁻¹ = dvdw (inverse function relationship)
  have hc_inv : dedu⁻¹ = dvdw := by field_simp at h_prod_one ⊢; linarith
  -- Step 5: Substitute fderiv = toDual(gradient) and solve for the gradient
  rw [h_dv_dp.hasGradientAt.hasFDerivAt.fderiv] at h_eq
  have h_solve : (toDual ℝ E) (gradient (fun q ↦ v q w) p) =
      -(dvdw • (toDual ℝ E) (x_star p w)) := by
    have h' := h_eq.symm
    have hA := add_eq_zero_iff_eq_neg.mp h'
    calc (toDual ℝ E) (gradient (fun q ↦ v q w) p)
        = dedu⁻¹ • (dedu • (toDual ℝ E) (gradient (fun q ↦ v q w) p)) :=
          (inv_smul_smul₀ hc_ne _).symm
      _ = dedu⁻¹ • (-(toDual ℝ E) (x_star p w)) := by congr 1; simp [hA]
      _ = -(dvdw • (toDual ℝ E) (x_star p w)) := by rw [smul_neg, hc_inv]
  -- Step 6: Conclude via injectivity of toDual
  apply (toDual ℝ E).injective
  rw [h_solve]
  simp only [neg_smul, map_neg, map_smul]

/-! ### Bridge: `Danskin.argmax_iSup` ↔ `Econlib.Optimization.argmax`

`Danskin.argmax_iSup f x` (type-level, `{z | f x z = ⨆ z', f x z'}`) equals
`Econlib.Optimization.argmax (f x) Set.univ` (set-based, `{z ∈ univ | IsMaxOn (f x) univ z}`) when
the range is bounded above (automatic for compact `Z` with continuous `f x`). -/

/-- The iSup-based argmax equals the IsMaxOn-based argmax over `Set.univ`. This bridges
`Danskin.argmax_iSup` with `Econlib.Optimization.argmax`. -/
lemma argmax_iSup_eq_setOf_isMaxOn {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]
    (f : E → Z → ℝ) (x : E) (hbdd : BddAbove (Set.range (f x))) :
    argmax_iSup f x = {z ∈ Set.univ | IsMaxOn (f x) Set.univ z} := by
  ext z
  simp only [argmax_iSup, valueFunction, Set.mem_setOf_eq, Set.mem_univ, true_and, IsMaxOn,
    IsMaxFilter, Filter.eventually_principal, true_implies]
  constructor
  · intro hz y; rw [hz]; exact le_ciSup hbdd y
  · intro hz; exact le_antisymm (le_ciSup hbdd z) (ciSup_le fun z' => hz z')

end Econlib.Optimization.Envelope
