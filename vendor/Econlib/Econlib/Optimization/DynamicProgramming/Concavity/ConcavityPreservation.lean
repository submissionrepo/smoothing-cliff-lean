/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Convex.FunctionSum
public import Econlib.Math.Order.CsSup
public import Econlib.Optimization.DynamicProgramming.Concavity.ClosedInvariantSet
public import Econlib.Probability.FinDist.Expect
public import Mathlib.Analysis.Convex.Function

/-!
# Concavity preservation under the Bellman operator

The Bellman operator preserves concavity of value functions under appropriate conditions on the
reward function, feasibility correspondence, and transition function (Stokey, Lucas, and Prescott
1989). Combined with the closed-invariant-set principle, this implies the unique fixed point (the
value function) is concave.

## Main definitions

* `ConcaveDPData` — hypotheses for concavity preservation in a deterministic DP (`S = A = ℝ`):
  Convex domain, convex-graph feasibility correspondence, jointly concave reward, affine transition.
* `ConcaveFiniteDPData` — analogous data for a finite stochastic DP.

## Main statements

### Deterministic case (`S = ℝ`)

* `bellmanOperator_concave` — if `v` is concave, `Tv` is concave.
* `valueFunction_concave` — the value function `v*` is concave.
* `bellmanOperator_strictConcave` — strict concavity preservation.
* `valueFunction_strictConcave` — `v*` is strictly concave.

### Finite stochastic case

* `finiteBellmanOperator_concave_in_action` — the Bellman objective is concave in the action.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76). Theorems 9.6–9.8.

## Tags

dynamic programing, bellman operator, concavity, value function
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell UnboundedDetMDP

open Set

/-! ## Deterministic Concavity Preservation (S = ℝ) -/

section Deterministic

/-- Hypotheses for concavity preservation in a deterministic DP with `S = A = ℝ`.

Following Stokey, Lucas, and Prescott (1989), §9.1: Convex domain, feasibility correspondence with
convex graph, jointly concave reward, and affine transition that maps the graph back into the
domain.

The affine transition assumption is standard in applications (e.g., neoclassical growth:
`f(w,a) = a` or `f(w,a) = F(a)`) and ensures `v ∘ f` is concave when `v` is concave, without
requiring monotonicity of `v`. -/
structure ConcaveDPData extends DetMDP ℝ ℝ where
  /-- Domain: Convex subset of ℝ -/
  domain : Set ℝ
  /-- Domain is convex -/
  domain_convex : Convex ℝ domain
  /-- Graph-convexity of the feasibility correspondence -/
  Γ_graph_convex :
    ∀ ⦃w w' : ℝ⦄ ⦃a a' : ℝ⦄ ⦃α : ℝ⦄,
      w ∈ domain → w' ∈ domain →
      a ∈ toDetMDP.Γ w → a' ∈ toDetMDP.Γ w' →
      0 ≤ α → α ≤ 1 →
      α • a + (1 - α) • a' ∈
        toDetMDP.Γ (α • w + (1 - α) • w')
  /-- Joint concavity of the reward on the graph of Γ -/
  reward_concave :
    ConcaveOn ℝ
      {p : ℝ × ℝ | p.1 ∈ domain ∧ p.2 ∈ toDetMDP.Γ p.1}
      (fun p => toDetMDP.reward p.1 p.2)
  /-- Concavity of the transition (part of affine) -/
  transition_concave :
    ConcaveOn ℝ
      {p : ℝ × ℝ | p.1 ∈ domain ∧ p.2 ∈ toDetMDP.Γ p.1}
      (fun p => toDetMDP.transition p.1 p.2)
  /-- Convexity of the transition (together with concavity, makes it affine on the graph) -/
  transition_convex :
    ConvexOn ℝ
      {p : ℝ × ℝ | p.1 ∈ domain ∧ p.2 ∈ toDetMDP.Γ p.1}
      (fun p => toDetMDP.transition p.1 p.2)
  /-- Transition maps feasible pairs in the domain back into the domain -/
  transition_domain :
    ∀ w ∈ domain, ∀ a ∈ toDetMDP.Γ w,
      toDetMDP.transition w a ∈ domain

/-- The transition is affine: For `(w₁,a₁), (w₂,a₂)` in the graph of Γ and `α ∈ [0,1]`,
`f(α·(w₁,a₁) + (1-α)·(w₂,a₂)) = α·f(w₁,a₁) + (1-α)·f(w₂,a₂)`. -/
lemma ConcaveDPData.transition_affine (D : ConcaveDPData)
    {p q : ℝ × ℝ}
    (hp : p.1 ∈ D.domain ∧ p.2 ∈ D.toDetMDP.Γ p.1)
    (hq : q.1 ∈ D.domain ∧ q.2 ∈ D.toDetMDP.Γ q.1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun r : ℝ × ℝ => D.toDetMDP.transition r.1 r.2)
      (a • p + b • q) =
    a • D.toDetMDP.transition p.1 p.2 +
      b • D.toDetMDP.transition q.1 q.2 := by
  have hc := D.transition_concave.2 hp hq ha hb hab
  have hv := D.transition_convex.2 hp hq ha hb hab
  linarith

/-! ### Construction helpers for product-box DP data

A modeler instantiating `ConcaveDPData` with a constant feasibility correspondence `Γ ≡ A` over
a convex domain meets a graph set of the shape `{p | p.1 ∈ Dom ∧ p.2 ∈ A}`. These helpers retire
the boilerplate of proving that set convex and of lifting one-coordinate concavities and a linear
transition onto it, so the fields `reward_concave`, `transition_concave`, and `transition_convex`
reduce to the underlying one-dimensional facts. -/

namespace ConcaveDPData

/-- The graph of a constant feasibility correspondence `Γ ≡ A` over a domain `Dom` is convex when
both `Dom` and `A` are convex: It is the product `Dom ×ˢ A`. Retires the `hbox`/`hconv` block of a
product-box `ConcaveDPData` instance. -/
lemma convex_graph_const {Dom A : Set ℝ} (hDom : Convex ℝ Dom) (hA : Convex ℝ A) :
    Convex ℝ {p : ℝ × ℝ | p.1 ∈ Dom ∧ p.2 ∈ A} :=
  hDom.prod hA

/-- Lift a concavity in the state coordinate `g p.1` onto a convex subset `G` of the product space,
given that every point of `G` has its state coordinate in `g`'s domain `S`. The
`comp_linearMap`-via-`LinearMap.fst` step shared by product-box `reward_concave` proofs. -/
lemma concaveOn_fst {G : Set (ℝ × ℝ)} (hG : Convex ℝ G) {S : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ S g) (hsub : ∀ p ∈ G, p.1 ∈ S) :
    ConcaveOn ℝ G (fun p : ℝ × ℝ => g p.1) :=
  (hg.comp_linearMap (LinearMap.fst ℝ ℝ ℝ)).subset (fun p hp => hsub p hp) hG

/-- Lift a concavity in the action coordinate `g p.2` onto a convex subset `G` of the product
space, given that every point of `G` has its action coordinate in `g`'s domain `A`. The
action-coordinate analog of `concaveOn_fst`, via `LinearMap.snd`. -/
lemma concaveOn_snd {G : Set (ℝ × ℝ)} (hG : Convex ℝ G) {A : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ A g) (hsub : ∀ p ∈ G, p.2 ∈ A) :
    ConcaveOn ℝ G (fun p : ℝ × ℝ => g p.2) :=
  (hg.comp_linearMap (LinearMap.snd ℝ ℝ ℝ)).subset (fun p hp => hsub p hp) hG

/-- A transition that agrees on a convex set `G` with a linear map `L : ℝ × ℝ →ₗ[ℝ] ℝ` is both
concave and convex there — i.e. affine — discharging `transition_concave` and `transition_convex`
together. The `LinearMap.snd` transition `f(w,a) = a` and the midpoint `f(w,a) = (w+a)/2` are the
common instances. -/
lemma concaveOn_convexOn_of_eqOn_linearMap {G : Set (ℝ × ℝ)} (hG : Convex ℝ G)
    (L : ℝ × ℝ →ₗ[ℝ] ℝ) {f : ℝ × ℝ → ℝ} (hf : Set.EqOn f (⇑L) G) :
    ConcaveOn ℝ G f ∧ ConvexOn ℝ G f :=
  ⟨(L.concaveOn hG).congr hf.symm, (L.convexOn hG).congr hf.symm⟩

end ConcaveDPData

variable (D : ConcaveDPData)

/-- **Concavity preservation (Bellman operator, deterministic).** If `v : ℝ → ℝ` is concave on
`D.domain`, then `Tv` is concave on `D.domain` (Stokey, Lucas, and Prescott 1989, Theorem 9.6). -/
theorem bellmanOperator_concave
    (v : ℝ → ℝ) (hv : ConcaveOn ℝ D.domain v)
    (hv_bdd : UniformBounded v) :
    ConcaveOn ℝ D.domain
      (D.toDetMDP.bellmanOperator v) := by
  constructor
  · exact D.domain_convex
  · intro w₁ hw₁ w₂ hw₂ α β hα hβ hαβ
    simp only [smul_eq_mul]
    unfold bellmanOperator
    apply mul_csSup_add_mul_csSup_le hα hβ
      (D.toDetMDP.bellmanSet_nonempty v w₁)
      (D.toDetMDP.bellmanSet_nonempty v w₂)
      (bellmanSet_bddAbove D.toDetMDP v hv_bdd w₁)
      (bellmanSet_bddAbove D.toDetMDP v hv_bdd w₂)
    rintro r₁ ⟨a₁, ha₁, rfl⟩ r₂ ⟨a₂, ha₂, rfl⟩
    -- `Γ_graph_convex` uses `(1 - α)` notation; convert via `β = 1 - α`
    have hβ_eq : β = 1 - α := by linarith
    set ā := α * a₁ + β * a₂ with hā_def
    set wbar := α * w₁ + β * w₂ with hwbar_def
    have hā : ā ∈ D.toDetMDP.Γ wbar := by
      have h := D.Γ_graph_convex hw₁ hw₂ ha₁ ha₂ hα (by linarith : α ≤ 1)
      simp only [smul_eq_mul] at h
      rwa [show (1 : ℝ) - α = β from by linarith] at h
    have helem : D.toDetMDP.reward wbar ā +
        D.toDetMDP.β * v (D.toDetMDP.transition wbar ā) ≤
        sSup (D.toDetMDP.bellmanSet v wbar) :=
      le_csSup (bellmanSet_bddAbove D.toDetMDP v hv_bdd wbar)
        ⟨ā, hā, rfl⟩
    suffices hsuff :
        α * (D.toDetMDP.reward w₁ a₁ +
          D.toDetMDP.β * v (D.toDetMDP.transition w₁ a₁)) +
        β * (D.toDetMDP.reward w₂ a₂ +
          D.toDetMDP.β * v (D.toDetMDP.transition w₂ a₂)) ≤
        D.toDetMDP.reward wbar ā +
          D.toDetMDP.β * v (D.toDetMDP.transition wbar ā) by
      linarith
    have hp : ((w₁, a₁) : ℝ × ℝ) ∈
        {p : ℝ × ℝ | p.1 ∈ D.domain ∧ p.2 ∈ D.toDetMDP.Γ p.1} :=
      ⟨hw₁, ha₁⟩
    have hq : ((w₂, a₂) : ℝ × ℝ) ∈
        {p : ℝ × ℝ | p.1 ∈ D.domain ∧ p.2 ∈ D.toDetMDP.Γ p.1} :=
      ⟨hw₂, ha₂⟩
    have hrew : α * D.toDetMDP.reward w₁ a₁ +
        β * D.toDetMDP.reward w₂ a₂ ≤
        D.toDetMDP.reward wbar ā := by
      have h := D.reward_concave.2 hp hq hα hβ hαβ
      simpa only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add, smul_eq_mul] using h
    have htrans : D.toDetMDP.transition wbar ā =
        α * D.toDetMDP.transition w₁ a₁ +
          β * D.toDetMDP.transition w₂ a₂ := by
      have h := D.transition_affine hp hq hα hβ hαβ
      simpa only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add, smul_eq_mul] using h
    have hf₁_dom : D.toDetMDP.transition w₁ a₁ ∈ D.domain :=
      D.transition_domain w₁ hw₁ a₁ ha₁
    have hf₂_dom : D.toDetMDP.transition w₂ a₂ ∈ D.domain :=
      D.transition_domain w₂ hw₂ a₂ ha₂
    have hval : α * v (D.toDetMDP.transition w₁ a₁) +
        β * v (D.toDetMDP.transition w₂ a₂) ≤
        v (D.toDetMDP.transition wbar ā) := by
      rw [htrans]
      have h := hv.2 hf₁_dom hf₂_dom hα hβ hαβ
      simpa only [smul_eq_mul] using h
    nlinarith [mul_le_mul_of_nonneg_left hval D.toDetMDP.β_nonneg]

/-- **Concavity of the value function (deterministic DP).** The unique fixed point of the Bellman
operator is concave on `D.domain` (Stokey, Lucas, and Prescott 1989, corollary to Theorem 9.6). -/
theorem valueFunction_concave :
    ∀ (v : ℝ → ℝ), UniformBounded v →
      (∀ s, v s = D.toDetMDP.bellmanOperator v s) →
      ConcaveOn ℝ D.domain v := by
  intro v hv_bdd hv_fp
  -- Apply the Closed Invariant Set Principle to
  -- `C = {f : BddFun | ConcaveOn ℝ D.domain f}`.
  set C : Set (@BddFun ℝ) :=
    {f | ConcaveOn ℝ D.domain (f : DState → ℝ)}
  have hC_ne : C.Nonempty := by
    exact ⟨0, concaveOn_const 0 D.domain_convex⟩
  -- Closedness: the concavity inequality is preserved under sup-norm limits.
  have hC_closed : IsClosed C := by
    apply isClosed_of_closure_subset
    intro f hf
    refine ⟨D.domain_convex, fun x hx y hy a b ha hb hab => ?_⟩
    by_contra h_neg
    push Not at h_neg
    set ε := a • (f : DState → ℝ) x + b • (f : DState → ℝ) y -
      (f : DState → ℝ) (a • x + b • y)
    have hε : 0 < ε := by linarith
    rw [Metric.mem_closure_iff] at hf
    obtain ⟨g, hg_mem, hg_dist⟩ := hf (ε / 3) (by linarith)
    have hg_conc : ConcaveOn ℝ D.domain (g : DState → ℝ) := hg_mem
    have hg_ineq := hg_conc.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hg_ineq
    have hclose : ∀ z : @DState ℝ, |(f : DState → ℝ) z -
        (g : DState → ℝ) z| < ε / 3 := by
      intro z
      have := BoundedContinuousFunction.dist_coe_le_dist z
        (α := @DState ℝ) (β := ℝ) (f := f) (g := g)
      rw [Real.dist_eq] at this
      linarith [this, hg_dist]
    have hx' := hclose x
    have hy' := hclose y
    have hm' := hclose (a • x + b • y)
    rw [abs_lt] at hx' hy' hm'
    -- Each of the three evaluation points is `ε/3`-close to `g`;
    -- the concavity of `g` plus `a + b = 1` forces `ε ≤ 2ε/3`.
    have : ε ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 := by
      have h1 : a * ((f : DState → ℝ) x - (g : DState → ℝ) x) ≤
          a * (ε / 3) := by
        exact mul_le_mul_of_nonneg_left hx'.2.le ha
      have h2 : b * ((f : DState → ℝ) y - (g : DState → ℝ) y) ≤
          b * (ε / 3) := by
        exact mul_le_mul_of_nonneg_left hy'.2.le hb
      have h3 : (g : DState → ℝ) (a • x + b • y) -
          (f : DState → ℝ) (a • x + b • y) ≤ ε / 3 := by
        linarith [hm'.1]
      have key : ε = a * ((f : DState → ℝ) x - (g : DState → ℝ) x) +
          b * ((f : DState → ℝ) y - (g : DState → ℝ) y) +
          ((g : DState → ℝ) (a • x + b • y) -
            (f : DState → ℝ) (a • x + b • y)) +
          (a * (g : DState → ℝ) x + b * (g : DState → ℝ) y -
            (g : DState → ℝ) (a • x + b • y)) := by
        simp only [ε, smul_eq_mul]; ring
      calc ε = _ := key
        _ ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 +
            (a * (g : DState → ℝ) x + b * (g : DState → ℝ) y -
              (g : DState → ℝ) (a • x + b • y)) := by
          linarith
        _ ≤ a * (ε / 3) + b * (ε / 3) + ε / 3 + 0 := by
          have hgi := hg_ineq
          simp only [smul_eq_mul] at hgi ⊢
          linarith
        _ = a * (ε / 3) + b * (ε / 3) + ε / 3 := by ring
    have : (a + b + 1) * (ε / 3) = 2 * ε / 3 := by
      rw [hab]; ring
    linarith
  have hC_inv : Set.MapsTo (bellmanOperatorBddFun D.toDetMDP) C C := by
    intro f hf
    change ConcaveOn ℝ D.domain ((bellmanOperatorBddFun D.toDetMDP f : DState → ℝ))
    simp only [show (bellmanOperatorBddFun D.toDetMDP f : DState → ℝ) =
      D.toDetMDP.bellmanOperator f from by
        ext s; exact bellmanOperatorBddFun_apply D.toDetMDP f s]
    exact bellmanOperator_concave D f hf (bddFun_bounded f)
  have hv_mem : toBddFun v hv_bdd ∈ C :=
    D.toDetMDP.isFixedPt_mem_closedInvariant hC_ne hC_closed hC_inv hv_bdd hv_fp
  have hconc : ConcaveOn ℝ D.domain (toBddFun v hv_bdd : DState → ℝ) := hv_mem
  rwa [show (toBddFun v hv_bdd : DState → ℝ) = v from toBddFun_coe v hv_bdd] at hconc

/-- **Strict concavity preservation (Bellman operator).** If `v` is concave and the reward is
strictly concave, then `Tv` is strictly concave on `D.domain`. Requires compactness of `Γ` and
continuity of the objective so the argmax is attained (Stokey, Lucas, and Prescott 1989, Theorem
9.8). -/
theorem bellmanOperator_strictConcave
    (h_strict :
      StrictConcaveOn ℝ
        {p : ℝ × ℝ | p.1 ∈ D.domain ∧
          p.2 ∈ D.toDetMDP.Γ p.1}
        (fun p => D.toDetMDP.reward p.1 p.2))
    (v : ℝ → ℝ) (hv : ConcaveOn ℝ D.domain v)
    (hv_bdd : UniformBounded v)
    (h_compact : ∀ w ∈ D.domain,
      IsCompact (D.toDetMDP.Γ w))
    (h_cont : ∀ w ∈ D.domain,
      ContinuousOn
        (fun a => D.toDetMDP.reward w a +
          D.toDetMDP.β * v (D.toDetMDP.transition w a))
        (D.toDetMDP.Γ w)) :
    StrictConcaveOn ℝ D.domain
      (D.toDetMDP.bellmanOperator v) := by
  refine ⟨D.domain_convex,
    fun w₁ hw₁ w₂ hw₂ hw_ne α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  have ⟨a₁, ha₁, hmax₁⟩ := (h_compact w₁ hw₁).exists_isMaxOn
    (D.toDetMDP.Γ_nonempty w₁) (h_cont w₁ hw₁)
  have ⟨a₂, ha₂, hmax₂⟩ := (h_compact w₂ hw₂).exists_isMaxOn
    (D.toDetMDP.Γ_nonempty w₂) (h_cont w₂ hw₂)
  have hTv₁ : D.toDetMDP.bellmanOperator v w₁ =
      D.toDetMDP.reward w₁ a₁ +
        D.toDetMDP.β * v (D.toDetMDP.transition w₁ a₁) := by
    unfold bellmanOperator
    apply le_antisymm
    · exact csSup_le (D.toDetMDP.bellmanSet_nonempty v w₁)
        (fun r ⟨a, ha, hr⟩ => hr ▸ hmax₁ ha)
    · exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v hv_bdd w₁)
        ⟨a₁, ha₁, rfl⟩
  have hTv₂ : D.toDetMDP.bellmanOperator v w₂ =
      D.toDetMDP.reward w₂ a₂ +
        D.toDetMDP.β * v (D.toDetMDP.transition w₂ a₂) := by
    unfold bellmanOperator
    apply le_antisymm
    · exact csSup_le (D.toDetMDP.bellmanSet_nonempty v w₂)
        (fun r ⟨a, ha, hr⟩ => hr ▸ hmax₂ ha)
    · exact le_csSup
        (bellmanSet_bddAbove D.toDetMDP v hv_bdd w₂)
        ⟨a₂, ha₂, rfl⟩
  rw [hTv₁, hTv₂]
  set wbar := α * w₁ + β * w₂
  set ā := α * a₁ + β * a₂
  have hβ_eq : β = 1 - α := by linarith
  have hā : ā ∈ D.toDetMDP.Γ wbar := by
    simp only [ā, wbar, hβ_eq]
    exact D.Γ_graph_convex hw₁ hw₂ ha₁ ha₂
      (le_of_lt hα) (by linarith)
  have hTv_bar :
      D.toDetMDP.reward wbar ā +
        D.toDetMDP.β * v (D.toDetMDP.transition wbar ā) ≤
      D.toDetMDP.bellmanOperator v wbar := by
    unfold bellmanOperator
    exact le_csSup
      (bellmanSet_bddAbove D.toDetMDP v hv_bdd wbar)
      ⟨ā, hā, rfl⟩
  have hp : ((w₁, a₁) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | p.1 ∈ D.domain ∧
        p.2 ∈ D.toDetMDP.Γ p.1} := ⟨hw₁, ha₁⟩
  have hq : ((w₂, a₂) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | p.1 ∈ D.domain ∧
        p.2 ∈ D.toDetMDP.Γ p.1} := ⟨hw₂, ha₂⟩
  have hpq : (w₁, a₁) ≠ (w₂, a₂) := by
    intro h; exact hw_ne (Prod.ext_iff.mp h).1
  have hrew_strict :
      α * D.toDetMDP.reward w₁ a₁ +
        β * D.toDetMDP.reward w₂ a₂ <
      D.toDetMDP.reward wbar ā := by
    have := h_strict.2 hp hq hpq hα hβ hαβ
    simpa only [Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul] using this
  have htrans : D.toDetMDP.transition wbar ā =
      α * D.toDetMDP.transition w₁ a₁ +
        β * D.toDetMDP.transition w₂ a₂ := by
    have := D.transition_affine hp hq
      (le_of_lt hα) (le_of_lt hβ) hαβ
    simpa only [Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, smul_eq_mul] using this
  have hf₁_dom := D.transition_domain w₁ hw₁ a₁ ha₁
  have hf₂_dom := D.transition_domain w₂ hw₂ a₂ ha₂
  have hval :
      α * v (D.toDetMDP.transition w₁ a₁) +
        β * v (D.toDetMDP.transition w₂ a₂) ≤
      v (D.toDetMDP.transition wbar ā) := by
    rw [htrans]
    have h := hv.2 hf₁_dom hf₂_dom (le_of_lt hα)
      (le_of_lt hβ) hαβ
    simpa only [smul_eq_mul] using h
  -- Strict inequality from `hrew_strict`; weak inequality from `hval`
  calc α * (D.toDetMDP.reward w₁ a₁ +
          D.toDetMDP.β * v (D.toDetMDP.transition w₁ a₁)) +
        β * (D.toDetMDP.reward w₂ a₂ +
          D.toDetMDP.β * v (D.toDetMDP.transition w₂ a₂))
      < D.toDetMDP.reward wbar ā +
          D.toDetMDP.β *
            v (D.toDetMDP.transition wbar ā) := by
        nlinarith [mul_le_mul_of_nonneg_left hval
          D.toDetMDP.β_nonneg]
    _ ≤ D.toDetMDP.bellmanOperator v wbar := hTv_bar

/-- **Strict concavity of the value function.** Under strict concavity of the reward (with
compactness of `Γ` and continuity of the objective for argmax attainment), the unique fixed point
of the Bellman operator is strictly concave (Stokey, Lucas, and Prescott 1989, Theorem 9.8). -/
theorem valueFunction_strictConcave
    (h_strict :
      StrictConcaveOn ℝ
        {p : ℝ × ℝ | p.1 ∈ D.domain ∧
          p.2 ∈ D.toDetMDP.Γ p.1}
        (fun p => D.toDetMDP.reward p.1 p.2))
    (h_compact : ∀ w ∈ D.domain,
      IsCompact (D.toDetMDP.Γ w))
    (h_cont : ∀ (v : ℝ → ℝ), UniformBounded v →
      ∀ w ∈ D.domain, ContinuousOn
        (fun a => D.toDetMDP.reward w a +
          D.toDetMDP.β * v (D.toDetMDP.transition w a))
        (D.toDetMDP.Γ w)) :
    ∀ (v : ℝ → ℝ), UniformBounded v →
      (∀ s, v s = D.toDetMDP.bellmanOperator v s) →
      StrictConcaveOn ℝ D.domain v := by
  intro v hv_bdd hv_fp
  have hv_concave := valueFunction_concave D v hv_bdd hv_fp
  have hTv_strict :=
    bellmanOperator_strictConcave D h_strict v
      hv_concave hv_bdd h_compact (h_cont v hv_bdd)
  have heq : D.toDetMDP.bellmanOperator v = v :=
    funext (fun s => (hv_fp s).symm)
  rwa [heq] at hTv_strict

end Deterministic

/-! ## Finite Stochastic Concavity Preservation -/

section FiniteStochastic

open Econlib.Probability BigOperators

/-- Hypotheses for concavity preservation in a finite stochastic DP with state space `Fin n` and
action space `ℝ`. -/
structure ConcaveFiniteDPData (n : ℕ) where
  /-- The underlying finite MDP -/
  toFinMDP : FinMDP n ℝ
  /-- Feasible sets are convex -/
  Γ_convex : ∀ s, Convex ℝ (toFinMDP.Γ s)
  /-- Reward is concave in the action for each state -/
  reward_concave :
    ∀ s, ConcaveOn ℝ (toFinMDP.Γ s)
      (toFinMDP.reward s)
  /-- Transition probabilities are concave in the action -/
  transition_weights_concave :
    ∀ (s : Fin n) (i : Fin n),
      ConcaveOn ℝ (toFinMDP.Γ s)
        (fun a => (toFinMDP.transition s a).pmf i)

/-- The expected continuation value `𝔼[v]` is concave in the action when the transition weights are
concave in the action and `v ≥ 0`. -/
lemma ConcaveFiniteDPData.expect_concaveOn {n : ℕ}
    (D : ConcaveFiniteDPData n) (s : Fin n)
    (v : Fin n → ℝ) (hv_nonneg : ∀ i, 0 ≤ v i) :
    ConcaveOn ℝ (D.toFinMDP.Γ s)
      (fun a =>
        FinDist.expect (D.toFinMDP.transition s a)
          v) := by
  unfold FinDist.expect
  simp_rw [mul_comm _ (v _)]
  have hS := D.Γ_convex s
  have h_each : ∀ i ∈ Finset.univ,
      ConcaveOn ℝ (D.toFinMDP.Γ s)
        (fun a => v i * (D.toFinMDP.transition s a).pmf i) :=
    fun i _ => ConcaveOn.smul (hv_nonneg i)
      (D.transition_weights_concave s i)
  exact ConcaveOn.fun_sum hS h_each

/-- **Concavity of the Bellman objective (finite stochastic).** When the continuation value is
nonnegative (`hv_nonneg`), the Bellman objective is concave in the action for each state.
Finite-state version of Stokey, Lucas, and Prescott (1989), Theorem 9.7. -/
theorem finiteBellmanOperator_concave_in_action {n : ℕ}
    (D : ConcaveFiniteDPData n) (v : Fin n → ℝ)
    (hv_nonneg : ∀ i, 0 ≤ v i) (s : Fin n) :
    ConcaveOn ℝ (D.toFinMDP.Γ s)
      (fun a =>
        D.toFinMDP.reward s a +
          D.toFinMDP.β *
            FinDist.expect
              (D.toFinMDP.transition s a) v) := by
  have h_expect :=
    ConcaveFiniteDPData.expect_concaveOn D s v
      hv_nonneg
  exact (D.reward_concave s).add
    (h_expect.smul D.toFinMDP.β_nonneg)

end FiniteStochastic

end Econlib.Optimization.DynamicProgramming
