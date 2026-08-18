/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.Supermodular
public import Econlib.Optimization.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Parametric Comparative Statics of the Value Function

Monotonicity, supermodularity, and threshold-domination lemmas for the value function
`V(θ) = valueFunction (u θ) S = sSup ((u θ) '' S)` in the parameter `θ`. These results underpin
comparative statics in political economy: How optimal payoffs respond to changes in fundamentals.

## Main statements

* `valueFunction_monotone_of_monotone`: The value function is monotone in `θ` when the payoff
  `u(·, x)` is monotone for each `x ∈ S`.
* `valueFunction_supermodular`: The value function is supermodular in `(θ, ψ)` when the payoff is
  supermodular on the product lattice and `S` is a sublattice.
* `binding_threshold_lt_of_domination`: Pointwise domination of payoff functions implies a strictly
  lower binding threshold.
* `strictAntiOn_apply_lt_of_binding_lt`: A strictly lower binding threshold yields a strictly
  higher value under any anti-monotone function.

## References

* Topkis, Donald M. 1978. “Minimizing a Submodular Function on a Lattice.” *Operations Research* 26
  (2): 305–21. [https://doi.org/10.1287/opre.26.2.305](https://doi.org/10.1287/opre.26.2.305).
* Milgrom, Paul, and Chris Shannon. 1994. “Monotone Comparative Statics.” *Econometrica* 62 (1):
  157. [https://doi.org/10.2307/2951479](https://doi.org/10.2307/2951479).

## Tags

comparative statics, value function, supermodularity, topkis, monotone
-/

@[expose] public section

namespace Econlib.Optimization

variable {Θ : Type*} {X : Type*}

section ValueMonotone

variable [Preorder Θ]

/-- The value function `V(θ) = valueFunction (u θ) S` is monotone in `θ` when `u(·, x)` is monotone
in `θ` for each `x ∈ S`. -/
lemma valueFunction_monotone_of_monotone {u : Θ → X → ℝ} {S : Set X}
    (hS : S.Nonempty)
    (h_mono : ∀ x ∈ S, Monotone (fun θ => u θ x))
    (h_bdd : ∀ θ, BddAbove (u θ '' S)) :
    Monotone (fun θ => valueFunction (u θ) S) := by
  intro θ₁ θ₂ hθ
  unfold valueFunction
  apply csSup_le (hS.image _)
  rintro r ⟨x, hx, rfl⟩
  exact le_csSup_of_le (h_bdd θ₂) ⟨x, hx, rfl⟩ (h_mono x hx hθ)

end ValueMonotone

section TopkisValue

variable {Ψ : Type*} [LinearOrder Θ] [LinearOrder Ψ] [LinearOrder X]

/-- **Value function supermodularity** (Topkis 1978; Milgrom and Shannon 1994): If `u(θ, ψ, x)` is
supermodular on `Θ × Ψ × X` and `S ⊆ X` is a sublattice (closed under `⊔` and `⊓`), then the value
function `V(θ, ψ) = valueFunction (u θ ψ) S` is supermodular in `(θ, ψ)`.

The hypothesis `h_prod_super` uses `⊔`/`⊓` (componentwise max/min on linear orders) so it handles
all pairs of points without requiring a fixed coordinate ordering. -/
theorem valueFunction_supermodular {u : Θ → Ψ → X → ℝ} {S : Set X}
    (h_prod_super : ∀ (θ θ' : Θ) (ψ ψ' : Ψ) (x x' : X),
      u (θ ⊔ θ') (ψ ⊔ ψ') (x ⊔ x') + u (θ ⊓ θ') (ψ ⊓ ψ') (x ⊓ x') ≥
      u θ ψ x + u θ' ψ' x')
    (h_sublattice : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ⊔ x₂ ∈ S ∧ x₁ ⊓ x₂ ∈ S)
    (hS : S.Nonempty)
    (h_bdd : ∀ θ ψ, BddAbove ((u θ ψ) '' S)) :
    Supermodular (fun θ ψ => valueFunction (u θ ψ) S) := by
  intro θ₁ θ₂ ψ₁ ψ₂ hθ hψ
  unfold valueFunction
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- x₁ ε/2-optimal for (θ₂, ψ₁), x₂ for (θ₁, ψ₂)
  obtain ⟨_, ⟨x₁, hx₁_mem, rfl⟩, hx₁_near⟩ :=
    exists_lt_of_lt_csSup (hS.image (u θ₂ ψ₁)) (sub_lt_self _ hε2)
  obtain ⟨_, ⟨x₂, hx₂_mem, rfl⟩, hx₂_near⟩ :=
    exists_lt_of_lt_csSup (hS.image (u θ₁ ψ₂)) (sub_lt_self _ hε2)
  obtain ⟨h_sup_mem, h_inf_mem⟩ := h_sublattice x₁ hx₁_mem x₂ hx₂_mem
  -- V dominates feasible points
  have hV₂₂ : u θ₂ ψ₂ (x₁ ⊔ x₂) ≤ sSup ((u θ₂ ψ₂) '' S) :=
    le_csSup (h_bdd θ₂ ψ₂) ⟨x₁ ⊔ x₂, h_sup_mem, rfl⟩
  have hV₁₁ : u θ₁ ψ₁ (x₁ ⊓ x₂) ≤ sSup ((u θ₁ ψ₁) '' S) :=
    le_csSup (h_bdd θ₁ ψ₁) ⟨x₁ ⊓ x₂, h_inf_mem, rfl⟩
  -- Product supermodularity at (θ₂,ψ₁,x₁) and (θ₁,ψ₂,x₂) gives
  -- u(θ₂,ψ₂,x₁⊔x₂) + u(θ₁,ψ₁,x₁⊓x₂) ≥ u(θ₂,ψ₁,x₁) + u(θ₁,ψ₂,x₂)
  have hkey : u θ₂ ψ₂ (x₁ ⊔ x₂) + u θ₁ ψ₁ (x₁ ⊓ x₂) ≥
      u θ₂ ψ₁ x₁ + u θ₁ ψ₂ x₂ := by
    have := h_prod_super θ₂ θ₁ ψ₁ ψ₂ x₁ x₂
    simp only [sup_eq_left.mpr hθ, inf_eq_right.mpr hθ,
               sup_eq_right.mpr hψ, inf_eq_left.mpr hψ] at this
    linarith
  linarith

end TopkisValue

section BindingThreshold

open Set

/-- **Monotone binding comparison under pointwise domination.** If `F` and `G` are strictly
increasing on `[a, b)`, each binds at the threshold `t` (`F u_F = t`, `G u_G = t`), and `F`
strictly dominates `G` pointwise on `[a, b)`, then `F`'s binding point is strictly below `G`'s:
`u_F < u_G`.

Application: If reform quality `F` strictly exceeds no-reform quality `G` at every action, then the
reform threshold is strictly below the no-reform threshold. -/
theorem binding_threshold_lt_of_domination
    {F G : ℝ → ℝ} {a b t u_F u_G : ℝ}
    -- recorded for the symmetric specification (fixes `u_F` as the unique
    -- preimage of `t` under `F`); the conclusion goes through `hG_mono` alone
    (_hF_mono : StrictMonoOn F (Ico a b))
    (hG_mono : StrictMonoOn G (Ico a b))
    (hu_F : u_F ∈ Ico a b) (hu_G : u_G ∈ Ico a b)
    (hF_bind : F u_F = t)
    (hG_bind : G u_G = t)
    (h_dom : ∀ x ∈ Ico a b, G x < F x) :
    u_F < u_G := by
  have hGuF_lt : G u_F < G u_G :=
    calc G u_F < F u_F := h_dom u_F hu_F
      _ = t := hF_bind
      _ = G u_G := hG_bind.symm
  exact (hG_mono.lt_iff_lt hu_F hu_G).mp hGuF_lt

/-- Anti-monotone consequence: If the binding threshold is lower, any strictly decreasing function
evaluated there is higher. -/
theorem strictAntiOn_apply_lt_of_binding_lt
    {h : ℝ → ℝ} {a b u₁ u₂ : ℝ}
    (hh_anti : StrictAntiOn h (Ico a b))
    (hu₁ : u₁ ∈ Ico a b) (hu₂ : u₂ ∈ Ico a b)
    (hlt : u₁ < u₂) :
    h u₂ < h u₁ :=
  hh_anti hu₁ hu₂ hlt

end BindingThreshold

end Econlib.Optimization
