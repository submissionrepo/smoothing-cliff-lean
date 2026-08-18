/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Constrained optimization: The smooth envelope (sensitivity) theorem

For a parametrized family of constrained problems `max_x f(x, θ)  s.t.  gᵢ(x, θ) ≤ 0  (i : ι)`,
with parameter `θ`, selection `xs : F → E`, and KKT multipliers `lam : ι → ℝ`, the envelope theorem
computes the derivative of the path value `V(θ) = f(xs θ, θ)` in the parameter:

`∂_θ V = ∂_θ f − Σᵢ lamᵢ · ∂_θ gᵢ`   (partials at `(xs θ₀, θ₀)`, holding `x` fixed).

The economic content is that the indirect effect of `θ` through the choice `xs θ` cancels: It is
absorbed by stationarity of the Lagrangian and the binding constraints. The smooth selection `xs`
enters as a hypothesis (`HasFDerivAt xs Dxs θ₀`), so the result needs no implicit-function theorem
or second-order conditions.

## Main definitions

* `feasibleSet` — the inequality-feasible set `{x | ∀ i, g i x θ ≤ 0}` at parameter `θ`.
* `constrainedMaxValue` — the value function: The supremum of the objective over the feasible set
  at a given parameter.

## Main statements

* `hasFDerivAt_constrainedValue` — the envelope path identity, stated for continuous linear maps
  over arbitrary normed spaces (no inner-product structure required).
* `constrainedMaxValue_eq_of_isMaxOn` — at a feasible maximizer the supremum is attained, so the
  value function equals the objective value there.
* `hasFDerivAt_constrainedMaxValue` — the envelope identity for the value function, under the local
  value-equality hypothesis delivered by local feasibility and optimality.
* `hasFDerivAt_constrainedMaxValue_of_localMaxOn` — the same, taking local optimality of the
  selection directly.

## Notes

`hasFDerivAt_constrainedValue` is a path identity, not yet a value theorem: It differentiates the
objective along the selection `θ ↦ f (xs θ) θ`, and its hypotheses are purely analytic
(differentiability of `xs`, Lagrangian stationarity `h_stat`, active-set persistence `h_bind`).
They do not assume feasibility, optimality, or that `f (xs θ) θ` equals a maximized value. When the
selection is a feasible maximizer throughout a neighborhood, the path value and the value function
`constrainedMaxValue` agree near `θ₀`, and `hasFDerivAt_constrainedMaxValue` transports the path
identity to differentiate the value function itself. This mirrors the indirect-utility /
Roy's-identity split in `Econlib.Equilibrium.IndirectUtility`.

Derivatives are Fréchet derivatives (`HasFDerivAt`) and continuous linear maps. Joint
differentiability of `f` and each `gᵢ` is supplied as `HasFDerivAt` of the uncurried map on
`E × F`; the parameter partials are recovered by precomposition with the canonical inclusions
`inl : E →L[ℝ] E × F` and `inr : F →L[ℝ] E × F`. Stationarity is the functional equation
`∂ₓf = Σ lamᵢ • ∂ₓgᵢ`. The binding hypothesis `h_bind` says each constraint is either slack
(`lamᵢ = 0`) or stays active along the selection (`gᵢ(xs η, η) = 0` near `θ₀`).

## Tags

envelope theorem, sensitivity, constrained optimization, value function, fréchet derivative
-/

@[expose] public section

open ContinuousLinearMap Filter Topology

namespace Econlib.Optimization

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- **Envelope (sensitivity) path identity for a parametrized constrained program.**

Given objective `f`, inequality constraints `g`, a differentiable selection `xs` with KKT
multipliers `lam`, the path value `θ ↦ f (xs θ) θ` is differentiable at `θ₀` with derivative equal
to the partial parameter-derivative of the Lagrangian, the indirect selection effect having
canceled.

The hypotheses are purely differential (smoothness of `xs`, stationarity, active-set persistence)
and do not assume feasibility, optimality, or that `f (xs θ) θ` equals a maximized value. It
therefore differentiates the objective along the selection, not the value function
`constrainedMaxValue`. For the value-function statement, see `hasFDerivAt_constrainedMaxValue`.

* `hf`, `hg` — joint differentiability of `f` and each `gᵢ` at `(xs θ₀, θ₀)` (uncurried on
  `E × F`); the `x`- and `θ`-partials are `Df.comp (inl ..)` and `Df.comp (inr ..)`.
* `hxs` — the selection is differentiable at `θ₀` (smooth-selection regularity).
* `h_stat` — Lagrangian stationarity in `x`: `∂ₓf = Σᵢ lamᵢ • ∂ₓgᵢ`.
* `h_bind` — complementary slackness / active-set persistence: Each constraint is slack
  (`lamᵢ = 0`) or remains binding along the selection near `θ₀`. -/
theorem hasFDerivAt_constrainedValue
    (f : E → F → ℝ) (g : ι → E → F → ℝ) (xs : F → E) (lam : ι → ℝ) (θ₀ : F)
    (Df : (E × F) →L[ℝ] ℝ) (Dg : ι → (E × F) →L[ℝ] ℝ) (Dxs : F →L[ℝ] E)
    (hf : HasFDerivAt (fun p : E × F => f p.1 p.2) Df (xs θ₀, θ₀))
    (hg : ∀ i, HasFDerivAt (fun p : E × F => g i p.1 p.2) (Dg i) (xs θ₀, θ₀))
    (hxs : HasFDerivAt xs Dxs θ₀)
    (h_stat : Df.comp (inl ℝ E F) = ∑ i, lam i • (Dg i).comp (inl ℝ E F))
    (h_bind : ∀ i, lam i = 0 ∨ (∀ᶠ η in 𝓝 θ₀, g i (xs η) η = 0)) :
    HasFDerivAt (fun η => f (xs η) η)
      (Df.comp (inr ℝ E F) - ∑ i, lam i • (Dg i).comp (inr ℝ E F)) θ₀ := by
  have hΦ : HasFDerivAt (fun η => (xs η, η)) (Dxs.prod (ContinuousLinearMap.id ℝ F)) θ₀ :=
    hxs.prodMk (hasFDerivAt_id θ₀)
  -- `Dxs.prod id = inl ∘ Dxs + inr`, so the chain rule splits into x- and θ-partials.
  have h_split : Dxs.prod (ContinuousLinearMap.id ℝ F)
      = (inl ℝ E F).comp Dxs + inr ℝ E F := by
    ext η <;> simp
  -- Chain rule: `DV = (∂ₓf) ∘ Dxs + ∂_θf`.
  have hV : HasFDerivAt (fun η => f (xs η) η)
      ((Df.comp (inl ℝ E F)).comp Dxs + Df.comp (inr ℝ E F)) θ₀ := by
    -- `apply` (goal in `∘`-form) defuses the higher-order-unification trap that the term-mode
    -- `hf.comp θ₀ hΦ` falls into (it mis-guesses the inner map as `Prod.mk (xs θ₀)`).
    have hV0 : HasFDerivAt ((fun p : E × F => f p.1 p.2) ∘ fun η => (xs η, η))
        (Df.comp (Dxs.prod (ContinuousLinearMap.id ℝ F))) θ₀ := by
      apply HasFDerivAt.comp
      · exact hf
      · exact hΦ
    rwa [h_split, comp_add, ← comp_assoc] at hV0
  -- For each active constraint the function `θ ↦ gᵢ(xs η, η)` is locally constant at `0`,
  -- so `(∂ₓgᵢ) ∘ Dxs = −∂_θgᵢ`.
  have h_active : ∀ i, lam i • ((Dg i).comp (inl ℝ E F)).comp Dxs
      = - (lam i • (Dg i).comp (inr ℝ E F)) := by
    intro i
    rcases h_bind i with hlam | hbind
    · simp [hlam]
    · have hGi : HasFDerivAt ((fun p : E × F => g i p.1 p.2) ∘ fun η => (xs η, η))
          ((Dg i).comp (Dxs.prod (ContinuousLinearMap.id ℝ F))) θ₀ := by
        apply HasFDerivAt.comp
        · exact hg i
        · exact hΦ
      have heq : ((fun p : E × F => g i p.1 p.2) ∘ fun η => (xs η, η))
          =ᶠ[𝓝 θ₀] (fun _ => (0 : ℝ)) := by
        filter_upwards [hbind] with η hη; exact hη
      have hGi0 : HasFDerivAt ((fun p : E × F => g i p.1 p.2) ∘ fun η => (xs η, η)) 0 θ₀ :=
        (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) θ₀).congr_of_eventuallyEq heq
      have hz : (Dg i).comp (Dxs.prod (ContinuousLinearMap.id ℝ F)) = 0 := hGi.unique hGi0
      rw [h_split, comp_add, ← comp_assoc] at hz
      have hneg : ((Dg i).comp (inl ℝ E F)).comp Dxs = - (Dg i).comp (inr ℝ E F) :=
        eq_neg_of_add_eq_zero_left hz
      rw [hneg, smul_neg]
  -- Stationarity lets us replace `(∂ₓf) ∘ Dxs` with `−Σ lamᵢ ∂_θgᵢ`, cancelling the indirect
  -- effect.
  have hcancel : (Df.comp (inl ℝ E F)).comp Dxs = - ∑ i, lam i • (Dg i).comp (inr ℝ E F) := by
    rw [h_stat, finset_sum_comp, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_comp]; exact h_active i
  rw [hcancel] at hV
  rwa [neg_add_eq_sub] at hV

/-! ### The value function and its derivative

`hasFDerivAt_constrainedValue` above differentiates the objective along the selection `xs`. The
value function is the supremum of the objective over the feasible set; it agrees with the path
value at a feasible maximizer, and the path identity transports across that local agreement. -/

/-- **The feasible set** of the constrained program at parameter `θ`: The bundles `x` satisfying
every inequality constraint `g i x θ ≤ 0`. -/
def feasibleSet (g : ι → E → F → ℝ) (θ : F) : Set E := {x | ∀ i, g i x θ ≤ 0}

/-- **The constrained-maximum value function**: The supremum of the objective `f (·) θ` over the
feasible set at parameter `θ`. Unlike the path value `f (xs θ) θ`, this is the maximized value of
the constrained program, independent of any selection.

As with any `sSup` over a possibly empty or unbounded set, this returns junk when the supremum is
not attained; `constrainedMaxValue_eq_of_isMaxOn` fixes it to the objective value at any feasible
maximizer. -/
noncomputable def constrainedMaxValue (f : E → F → ℝ) (g : ι → E → F → ℝ) (θ : F) : ℝ :=
  sSup ((fun x => f x θ) '' feasibleSet g θ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] in
/-- **The value function equals the objective at any feasible maximizer.** If `xs θ` is feasible
and maximizes the objective over the feasible set, the defining supremum is attained there, so
`constrainedMaxValue f g θ = f (xs θ) θ`. This is the `⨆`-over-feasible analog of
`Econlib.Equilibrium.indirectUtility_eq_of_isMaxOn`. -/
lemma constrainedMaxValue_eq_of_isMaxOn {f : E → F → ℝ} {g : ι → E → F → ℝ} {θ : F} {x : E}
    (hx_feas : x ∈ feasibleSet g θ) (hx_max : IsMaxOn (fun x => f x θ) (feasibleSet g θ) x) :
    constrainedMaxValue f g θ = f x θ :=
  IsGreatest.csSup_eq
    ⟨⟨x, hx_feas, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact (isMaxOn_iff.mp hx_max) y hy⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] [Fintype ι] in
/-- **Local optimality of the selection yields value-equality.** If, throughout a neighborhood of
`θ₀`, the selection `xs η` is a feasible maximizer of the objective over `feasibleSet g η`, then
the path value `f (xs η) η` equals the value function `constrainedMaxValue f g η` eventually. This
is exactly the value-equality hypothesis consumed by `hasFDerivAt_constrainedMaxValue`. -/
lemma eventuallyEq_constrainedMaxValue_of_localMaxOn {f : E → F → ℝ} {g : ι → E → F → ℝ}
    {xs : F → E} {θ₀ : F}
    (hloc : ∀ᶠ η in 𝓝 θ₀,
      xs η ∈ feasibleSet g η ∧ IsMaxOn (fun x => f x η) (feasibleSet g η) (xs η)) :
    (fun η => f (xs η) η) =ᶠ[𝓝 θ₀] constrainedMaxValue f g :=
  hloc.mono fun _ hη => (constrainedMaxValue_eq_of_isMaxOn hη.1 hη.2).symm

/-- **Envelope (sensitivity) theorem for the value function.** With the same KKT, stationarity, and
binding data as `hasFDerivAt_constrainedValue`, plus the local value-equality hypothesis `hval` —
which says the path value `f (xs η) η` agrees with the value function `constrainedMaxValue f g η`
throughout a neighborhood of `θ₀`, as delivered by local feasibility and optimality of the
selection (`eventuallyEq_constrainedMaxValue_of_localMaxOn`) — the value function itself is
differentiable at `θ₀` with the envelope derivative:

`∂_θ (constrainedMaxValue f g) = ∂_θ f − Σᵢ lamᵢ · ∂_θ gᵢ`   (partials at `(xs θ₀, θ₀)`). -/
theorem hasFDerivAt_constrainedMaxValue
    (f : E → F → ℝ) (g : ι → E → F → ℝ) (xs : F → E) (lam : ι → ℝ) (θ₀ : F)
    (Df : (E × F) →L[ℝ] ℝ) (Dg : ι → (E × F) →L[ℝ] ℝ) (Dxs : F →L[ℝ] E)
    (hf : HasFDerivAt (fun p : E × F => f p.1 p.2) Df (xs θ₀, θ₀))
    (hg : ∀ i, HasFDerivAt (fun p : E × F => g i p.1 p.2) (Dg i) (xs θ₀, θ₀))
    (hxs : HasFDerivAt xs Dxs θ₀)
    (h_stat : Df.comp (inl ℝ E F) = ∑ i, lam i • (Dg i).comp (inl ℝ E F))
    (h_bind : ∀ i, lam i = 0 ∨ (∀ᶠ η in 𝓝 θ₀, g i (xs η) η = 0))
    (hval : (fun η => f (xs η) η) =ᶠ[𝓝 θ₀] constrainedMaxValue f g) :
    HasFDerivAt (constrainedMaxValue f g)
      (Df.comp (inr ℝ E F) - ∑ i, lam i • (Dg i).comp (inr ℝ E F)) θ₀ :=
  (hasFDerivAt_constrainedValue f g xs lam θ₀ Df Dg Dxs hf hg hxs h_stat h_bind)
    |>.congr_of_eventuallyEq hval.symm

/-- **Envelope theorem for the value function, from local optimality.** Bundled form of
`hasFDerivAt_constrainedMaxValue` that takes the local-optimality hypothesis `hloc` — the selection
`xs η` is a feasible maximizer throughout a neighborhood of `θ₀` — directly, rather than the
distilled value-equality `hval`. A consumer with local optimality of the selection thus obtains the
value-function derivative in one shot. -/
theorem hasFDerivAt_constrainedMaxValue_of_localMaxOn
    (f : E → F → ℝ) (g : ι → E → F → ℝ) (xs : F → E) (lam : ι → ℝ) (θ₀ : F)
    (Df : (E × F) →L[ℝ] ℝ) (Dg : ι → (E × F) →L[ℝ] ℝ) (Dxs : F →L[ℝ] E)
    (hf : HasFDerivAt (fun p : E × F => f p.1 p.2) Df (xs θ₀, θ₀))
    (hg : ∀ i, HasFDerivAt (fun p : E × F => g i p.1 p.2) (Dg i) (xs θ₀, θ₀))
    (hxs : HasFDerivAt xs Dxs θ₀)
    (h_stat : Df.comp (inl ℝ E F) = ∑ i, lam i • (Dg i).comp (inl ℝ E F))
    (h_bind : ∀ i, lam i = 0 ∨ (∀ᶠ η in 𝓝 θ₀, g i (xs η) η = 0))
    (hloc : ∀ᶠ η in 𝓝 θ₀,
      xs η ∈ feasibleSet g η ∧ IsMaxOn (fun x => f x η) (feasibleSet g η) (xs η)) :
    HasFDerivAt (constrainedMaxValue f g)
      (Df.comp (inr ℝ E F) - ∑ i, lam i • (Dg i).comp (inr ℝ E F)) θ₀ :=
  hasFDerivAt_constrainedMaxValue f g xs lam θ₀ Df Dg Dxs hf hg hxs h_stat h_bind
    (eventuallyEq_constrainedMaxValue_of_localMaxOn hloc)

end Econlib.Optimization
