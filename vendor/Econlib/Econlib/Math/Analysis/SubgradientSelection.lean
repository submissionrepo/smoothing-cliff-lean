/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Danskin
public import Econlib.Math.Analysis.Supergradient
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Optlib.Convex.Subgradient

/-!
# Measurable selection of subgradients

Given a convex `L`-Lipschitz function `f` on a compact convex set `K ⊆ EuclideanSpace ℝ (Fin n)`
with nonempty interior, this file constructs a Borel-measurable map
`g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)` selecting the *minimum-norm subgradient*
of `f` at each point of `K`.

The subgradient set itself, and its closedness/convexity, are reused from
`Econlib.Math.Analysis.Danskin` (`SubderivWithinAt`).  Nonemptiness on `K` is obtained by
translating the Hahn–Banach supergradient theorem
`ConcaveOn.exists_supergradient_of_boundedSteepness` from `Econlib.Math.Analysis.Supergradient` to
the convex (subgradient) side.

## Main statements

* `ConvexOn.exists_subgradient_on_compactConvex` — nonemptiness of `SubderivWithinAt f K x` for `f`
  convex `L`-Lipschitz on closed convex `K`, with norm bound `‖p‖ ≤ L`.
* `ConvexOn.exists_minNormSubgrad` — pointwise selection of the unique minimum-norm subgradient via
  Hilbert-space projection.
* `ConvexOn.exists_measurable_subgradient_selection` — Borel-measurable selection of subgradients
  with uniform norm bound.

## References

* Aliprantis, Charalambos D., and Kim C. Border. 2007. *Infinite Dimensional Analysis*. Springer.
* Rockafellar, Ralph Tyrrell. 1997. *Convex Analysis*. Princeton University Press.

## Tags

subgradient, measurable selection, minimum-norm subgradient, lipschitz, convex
-/

@[expose] public section

open Set Topology

variable {n : ℕ}

/-- **Pointwise subgradient existence on a closed convex set.**

For a convex `L`-Lipschitz function `f` on a closed convex subset `K` of a real inner product
space, the subdifferential `SubderivWithinAt f K x` is nonempty at every `x ∈ K`, and contains an
element of norm at most `L`. -/
theorem ConvexOn.exists_subgradient_on_compactConvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK_conv : Convex ℝ K)
    {f : E → ℝ} (hf_conv : ConvexOn ℝ K f)
    {L : ℝ} (hL : 0 ≤ L) (hf_lip : LipschitzOnWith L.toNNReal f K)
    {x : E} (hx : x ∈ K) :
    ∃ p ∈ SubderivWithinAt f K x, ‖p‖ ≤ L := by
  -- Step 1: bounded steepness for -f at x.
  -- From Lipschitz: dist (f y) (f x) ≤ L.toNNReal * dist y x, and
  -- (-f) y - (-f) x = f x - f y ≤ |f x - f y| = dist (f x) (f y) ≤ L * ‖y - x‖.
  have hsteep : ∀ y ∈ K, (-f) y - (-f) x ≤ L * ‖y - x‖ := by
    intro y hy
    simp only [Pi.neg_apply]
    -- dist (f x) (f y) ≤ L.toNNReal * dist x y (Lipschitz)
    have hdist : dist (f x) (f y) ≤ ↑L.toNNReal * dist x y :=
      hf_lip.dist_le_mul x hx y hy
    rw [Real.coe_toNNReal L hL, Real.dist_eq, dist_eq_norm] at hdist
    -- |f x - f y| ≥ f x - f y, and ‖x - y‖ = ‖y - x‖ by norm_sub_rev.
    rw [norm_sub_rev] at hdist
    linarith [le_abs_self (f x - f y)]
  -- Step 2: apply supergradient theorem to -f.
  obtain ⟨H, hHnorm, h_supgrad⟩ :=
    ConcaveOn.exists_supergradient_of_boundedSteepness hK_conv hf_conv.neg hx hL hsteep
  -- Step 3: Riesz-represent -H as a vector p ∈ E.
  -- toDual_symm_apply: inner ℝ ((toDual ℝ E).symm y) v = y v
  -- So with p := (toDual ℝ E).symm (-H), we get inner ℝ p v = (-H) v = -(H v).
  let p : E := (InnerProductSpace.toDual ℝ E).symm (-H)
  refine ⟨p, ?_, ?_⟩
  · -- Subgradient inequality: f x + ⟪p, y - x⟫ ≤ f y for all y ∈ K.
    intro y hy
    -- p = (toDual ℝ E).symm (-H), so inner ℝ p (y - x) = (-H) (y - x).
    have h_inner : @inner ℝ E _ p (y - x) = (-H) (y - x) := by
      simp only [p]; rw [InnerProductSpace.toDual_symm_apply]
    rw [h_inner]
    -- h_supgrad gives: (-f) y - (-f) x ≤ H (y - x)
    -- i.e. f x - f y ≤ H (y - x), i.e. -(H (y - x)) ≤ f y - f x
    have hsg := h_supgrad y hy
    simp only [Pi.neg_apply] at hsg
    simp only [ContinuousLinearMap.neg_apply]
    linarith
  · -- Norm bound: ‖p‖ = ‖(toDual ℝ E).symm (-H)‖ = ‖-H‖ = ‖H‖ ≤ L.
    simp only [p]
    rw [LinearIsometryEquiv.norm_map]
    rw [norm_neg]
    exact hHnorm

/-- **Closed graph of the subdifferential intersected with a ball.**

Let `K` be a closed subset of an inner product space and `f` continuous on `K`. The set
`{(x, p) : x ∈ K ∧ p ∈ ∂f K x ∧ ‖p‖ ≤ L}` is closed in `E × E`. -/
lemma SubderivWithinAt.graph_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hK_closed : IsClosed K)
    {f : E → ℝ} (hf_cont : ContinuousOn f K)
    (L : ℝ) :
    IsClosed { q : E × E | q.1 ∈ K ∧ q.2 ∈ SubderivWithinAt f K q.1
                            ∧ ‖q.2‖ ≤ L } := by
  -- Decompose: condition is the conjunction of three closed conditions.
  -- (a) x := q.1 ∈ K (closed)
  -- (b) ∀ y ∈ K, f x + ⟨p, y - x⟩ ≤ f y (intersection of half-spaces)
  -- (c) ‖p‖ ≤ L (closed)
  have hA : IsClosed { q : E × E | q.1 ∈ K } :=
    hK_closed.preimage continuous_fst
  have hC : IsClosed { q : E × E | ‖q.2‖ ≤ L } :=
    isClosed_le (continuous_norm.comp continuous_snd) continuous_const
  -- For each y ∈ K, define the closed slab T_y = {q : q.1 ∈ K ∧
  --   f q.1 + ⟨q.2, y - q.1⟩ ≤ f y}.  Each T_y is closed because the function
  -- q ↦ f q.1 + ⟨q.2, y - q.1⟩ - f y is continuous on hA, so its preimage of Iic 0
  -- intersected with hA is closed.
  set S := { q : E × E | q.1 ∈ K ∧ q.2 ∈ SubderivWithinAt f K q.1 ∧ ‖q.2‖ ≤ L }
  have hS_eq : S = (({ q : E × E | q.1 ∈ K }) ∩ ({ q : E × E | ‖q.2‖ ≤ L }))
      ∩ ⋂ (y ∈ K), { q : E × E | q.1 ∈ K ∧
          f q.1 + @inner ℝ E _ q.2 (y - q.1) ≤ f y } := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SubderivWithinAt, S]
    refine ⟨?_, ?_⟩
    · rintro ⟨hxK, hsub, hnorm⟩
      refine ⟨⟨hxK, hnorm⟩, ?_⟩
      intro y hy
      exact ⟨hxK, hsub y hy⟩
    · rintro ⟨⟨hxK, hnorm⟩, hsub⟩
      refine ⟨hxK, ?_, hnorm⟩
      intro y hy
      exact (hsub y hy).2
  rw [hS_eq]
  refine IsClosed.inter (hA.inter hC) ?_
  refine isClosed_iInter (fun y => ?_)
  refine isClosed_iInter (fun hy => ?_)
  -- T_y is closed: it's hA intersected with the preimage of Iic 0 under a function
  -- continuous on hA.
  have hcont_on : ContinuousOn (fun q : E × E =>
      f q.1 + @inner ℝ E _ q.2 (y - q.1) - f y) ({ q : E × E | q.1 ∈ K }) := by
    have h1 : ContinuousOn (fun q : E × E => f q.1) ({ q : E × E | q.1 ∈ K }) :=
      hf_cont.comp continuous_fst.continuousOn fun _ hq => hq
    have h2 : Continuous (fun q : E × E => @inner ℝ E _ q.2 (y - q.1)) :=
      continuous_inner.comp (continuous_snd.prodMk (continuous_const.sub continuous_fst))
    exact (h1.add h2.continuousOn).sub continuousOn_const
  have h_preim_closed :
      IsClosed (({ q : E × E | q.1 ∈ K }) ∩
        ((fun q : E × E => f q.1 + @inner ℝ E _ q.2 (y - q.1) - f y) ⁻¹' Set.Iic 0)) :=
    hcont_on.preimage_isClosed_of_isClosed hA isClosed_Iic
  convert h_preim_closed using 1
  ext q
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
  constructor <;> rintro ⟨hx, hineq⟩ <;> exact ⟨hx, by linarith⟩

/-- **Minimum-norm subgradient is unique.**

The subdifferential admits a unique minimum-norm element — namely the projection of `0` onto
`SubderivWithinAt f K x` in the Hilbert-space sense. -/
theorem ConvexOn.exists_minNormSubgrad
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK_conv : Convex ℝ K)
    {f : E → ℝ} (hf_conv : ConvexOn ℝ K f)
    {L : ℝ} (hL : 0 ≤ L) (hf_lip : LipschitzOnWith L.toNNReal f K)
    {x : E} (hx : x ∈ K) :
    ∃! p, p ∈ SubderivWithinAt f K x ∧
      ∀ q ∈ SubderivWithinAt f K x, ‖p‖ ≤ ‖q‖ := by
  set S := SubderivWithinAt f K x with hS_def
  -- Closed, convex, nonempty subset of a complete inner product space.
  have hS_closed : IsClosed S := SubderivWithinAt.isClosed x
  have hS_complete : IsComplete S := hS_closed.isComplete
  have hS_convex : Convex ℝ S := SubderivWithinAt.convex x hx
  obtain ⟨p₀, hp₀_mem, _⟩ :=
    ConvexOn.exists_subgradient_on_compactConvex hK_conv hf_conv hL hf_lip hx
  have hS_nonempty : S.Nonempty := ⟨p₀, hp₀_mem⟩
  -- Project 0 onto S: get p ∈ S with ‖0 - p‖ = ⨅ w : S, ‖0 - w‖.
  obtain ⟨p, hp_mem, hp_eq⟩ :=
    exists_norm_eq_iInf_of_complete_convex (F := E) hS_nonempty hS_complete hS_convex 0
  -- Rewrite ‖0 - ·‖ as ‖·‖.
  have hp_norm_eq : ‖p‖ = ⨅ w : S, ‖(w : E)‖ := by
    have h1 : ‖(0 : E) - p‖ = ‖p‖ := by rw [zero_sub, norm_neg]
    have h2 : (⨅ w : S, ‖(0 : E) - (w : E)‖) = ⨅ w : S, ‖(w : E)‖ := by
      refine iInf_congr (fun w => ?_)
      rw [zero_sub, norm_neg]
    rw [h1] at hp_eq
    rw [hp_eq, h2]
  -- BddBelow for the iInf.
  have hBdd : BddBelow (Set.range (fun w : S => ‖(w : E)‖)) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  -- Minimum-norm property: ∀ q ∈ S, ‖p‖ ≤ ‖q‖.
  have hp_min : ∀ q ∈ S, ‖p‖ ≤ ‖q‖ := by
    intro q hq
    rw [hp_norm_eq]
    exact ciInf_le hBdd ⟨q, hq⟩
  refine ⟨p, ⟨hp_mem, hp_min⟩, ?_⟩
  -- Uniqueness via parallelogram law.
  rintro p' ⟨hp'_mem, hp'_min⟩
  -- Both minimal, so equal norms.
  have hnorm_eq : ‖p'‖ = ‖p‖ :=
    le_antisymm (hp'_min p hp_mem) (hp_min p' hp'_mem)
  set m := ‖p‖ with hm_def
  have hm_nn : 0 ≤ m := norm_nonneg _
  -- Midpoint (1/2)•p + (1/2)•p' lies in S.
  have hmid_mem : ((1/2 : ℝ) • p + (1/2 : ℝ) • p') ∈ S :=
    hS_convex hp_mem hp'_mem (by norm_num) (by norm_num) (by norm_num)
  -- m ≤ ‖midpoint‖.
  have hmid_lb : m ≤ ‖(1/2 : ℝ) • p + (1/2 : ℝ) • p'‖ := hp_min _ hmid_mem
  -- ‖(1/2)p + (1/2)p'‖ = (1/2) ‖p + p'‖.
  have hmid_eq : ‖(1/2 : ℝ) • p + (1/2 : ℝ) • p'‖ = (1/2) * ‖p + p'‖ := by
    rw [← smul_add, norm_smul]
    simp
  -- Hence 2m ≤ ‖p + p'‖.
  have h2m_le : 2 * m ≤ ‖p + p'‖ := by rw [hmid_eq] at hmid_lb; linarith
  -- Square: 4m² ≤ ‖p + p'‖².
  have h4m_sq : 4 * m ^ 2 ≤ ‖p + p'‖ ^ 2 := by nlinarith [h2m_le, hm_nn]
  -- Parallelogram law: ‖p+p'‖² + ‖p-p'‖² = 2(‖p‖² + ‖p'‖²) = 4m².
  have hpara : ‖p + p'‖ ^ 2 + ‖p - p'‖ ^ 2 = 2 * (‖p‖ ^ 2 + ‖p'‖ ^ 2) :=
    parallelogram_law_with_norm ℝ p p'
  have hrhs : 2 * (‖p‖ ^ 2 + ‖p'‖ ^ 2) = 4 * m ^ 2 := by
    rw [hnorm_eq, ← hm_def]; ring
  -- Hence ‖p - p'‖² ≤ 0, so ‖p - p'‖ = 0, so p = p'.
  have hsub_sq : ‖p - p'‖ ^ 2 = 0 := le_antisymm (by linarith [hpara, hrhs]) (sq_nonneg _)
  have hp_eq_p' : p - p' = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hsub_sq)
  exact (sub_eq_zero.mp hp_eq_p').symm

/-- **Measurable selection of subgradients of a convex Lipschitz function.**

Let `K ⊆ EuclideanSpace ℝ (Fin n)` be a compact convex set with nonempty interior, and let
`f : EuclideanSpace ℝ (Fin n) → ℝ` be convex and `L`-Lipschitz on `K`.  Then there exists a
Borel-measurable `g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)` with

* `‖g x‖ ≤ L` for every `x`;
* `g x ∈ SubderivWithinAt f K x` for every `x ∈ K`, equivalently `f x + ⟨g x, y − x⟩ ≤ f y` for all
  `y ∈ K`. -/
theorem ConvexOn.exists_measurable_subgradient_selection
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ} (hL : 0 ≤ L)
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (_hK_int : (interior K).Nonempty)
    (hf_conv : ConvexOn ℝ K f)
    (hf_lip : LipschitzOnWith L.toNNReal f K) :
    ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧
      ∀ x ∈ K, ∀ y ∈ K, f x + inner ℝ (g x) (y - x) ≤ f y := by
  -- Pointwise selection of the unique minimum-norm subgradient via `Classical.choose`,
  -- with default value `0` outside `K`.
  classical
  -- For each `x ∈ K`, `exists_minNormSubgrad` provides a unique min-norm subgradient.
  -- We package this as a function `gK : ↥K → EuclideanSpace ℝ (Fin n)`.
  let gK : ↥K → EuclideanSpace ℝ (Fin n) := fun x =>
    Classical.choose
      (ConvexOn.exists_minNormSubgrad hK_convex hf_conv hL hf_lip x.2).exists
  have hgK_spec : ∀ x : ↥K,
      gK x ∈ SubderivWithinAt f K (x : EuclideanSpace ℝ (Fin n)) ∧
      ∀ q ∈ SubderivWithinAt f K (x : EuclideanSpace ℝ (Fin n)), ‖gK x‖ ≤ ‖q‖ := by
    intro x
    exact Classical.choose_spec
      (ConvexOn.exists_minNormSubgrad hK_convex hf_conv hL hf_lip x.2).exists
  -- Define `g` on the whole space with default `0` off `K`.
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => if hx : x ∈ K then gK ⟨x, hx⟩ else 0
  -- Set up shorthands and Γ data, used by the measurability proof.
  set Γ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    { q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        q.1 ∈ K ∧ q.2 ∈ SubderivWithinAt f K q.1 ∧ ‖q.2‖ ≤ L }
    with hΓ_def
  have hf_cont : ContinuousOn f K := hf_lip.continuousOn
  have hΓ_closed : IsClosed Γ :=
    SubderivWithinAt.graph_isClosed hK_compact.isClosed hf_cont L
  have hΓ_subset : Γ ⊆ K ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) L := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hq.2.2
  have hKL_compact : IsCompact (K ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) L) :=
    hK_compact.prod (isCompact_closedBall _ _)
  have hΓ_compact : IsCompact Γ :=
    hKL_compact.of_isClosed_subset hΓ_closed hΓ_subset
  -- The min-norm value function: m(x) = inf {‖p‖² : (x, p) ∈ Γ}.
  -- For x ∈ K, m x = ‖gK ⟨x, _⟩‖² (attained); for x ∉ K, the inf is over ∅
  -- and Lean returns 0 (the `sInf` junk value).
  set mFn : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x =>
        sInf
          ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) ''
            (Γ ∩ {q | q.1 = x}))
    with hmFn_def
  have hmFn_eq : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K),
      mFn x = ‖gK ⟨x, hx⟩‖ ^ 2 := by
    intro x hx
    have hgK_mem : gK ⟨x, hx⟩ ∈ SubderivWithinAt f K x :=
      (hgK_spec ⟨x, hx⟩).1
    obtain ⟨w, hw_mem, hw_norm⟩ :=
      ConvexOn.exists_subgradient_on_compactConvex hK_convex hf_conv hL hf_lip hx
    have hgK_norm : ‖gK ⟨x, hx⟩‖ ≤ L :=
      le_trans ((hgK_spec ⟨x, hx⟩).2 w hw_mem) hw_norm
    have hgK_in_set :
        (x, gK ⟨x, hx⟩) ∈
          Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | q.1 = x} :=
      ⟨⟨hx, hgK_mem, hgK_norm⟩, rfl⟩
    have hImage_nonempty :
        ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) ''
          (Γ ∩ {q | q.1 = x})).Nonempty :=
      ⟨‖gK ⟨x, hx⟩‖^2, ⟨_, hgK_in_set, rfl⟩⟩
    have hLB :
        ∀ y ∈
          ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) ''
            (Γ ∩ {q | q.1 = x})),
          ‖gK ⟨x, hx⟩‖^2 ≤ y := by
      rintro y ⟨q, ⟨hqΓ, hq_eq⟩, rfl⟩
      have hq2_mem : q.2 ∈ SubderivWithinAt f K x := by
        have := hqΓ.2.1; rw [hq_eq] at this; exact this
      have h := (hgK_spec ⟨x, hx⟩).2 _ hq2_mem
      have hgnn : 0 ≤ ‖gK ⟨x, hx⟩‖ := norm_nonneg _
      have hqnn : 0 ≤ ‖q.2‖ := norm_nonneg _
      nlinarith
    have hUB :
        ‖gK ⟨x, hx⟩‖^2 ∈
          ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2) ''
            (Γ ∩ {q | q.1 = x})) :=
      ⟨_, hgK_in_set, rfl⟩
    refine le_antisymm
      (csInf_le ⟨0, ?_⟩ hUB)
      (le_csInf hImage_nonempty hLB)
    rintro _ ⟨q, _, rfl⟩
    exact sq_nonneg _
  -- For x ∉ K, the image is empty and `sInf ∅ = 0`.
  have hmFn_off : ∀ x, x ∉ K → mFn x = 0 := by
    intro x hx
    have h_empty : Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | q.1 = x} = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hqΓ, rfl⟩
      exact hx hqΓ.1
    simp only [mFn, h_empty, Set.image_empty, Real.sInf_empty]
  -- Borel measurability of `mFn`: for each c, `mFn ⁻¹' Iic c` is Borel.
  -- We show the level set K ∩ {x : mFn x ≤ c} is closed (via projection of compact).
  have hmFn_level_closed :
      ∀ c : ℝ, IsClosed (K ∩ {x : EuclideanSpace ℝ (Fin n) | mFn x ≤ c}) := by
    intro c
    have hSet_eq : K ∩ {x : EuclideanSpace ℝ (Fin n) | mFn x ≤ c} =
        Prod.fst ''
          (Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            ‖q.2‖^2 ≤ c}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image, Prod.exists]
      constructor
      · rintro ⟨hxK, hmle⟩
        rw [hmFn_eq x hxK] at hmle
        obtain ⟨w, hw_mem, hw_norm⟩ :=
          ConvexOn.exists_subgradient_on_compactConvex hK_convex hf_conv hL hf_lip hxK
        have hgK_norm : ‖gK ⟨x, hxK⟩‖ ≤ L :=
          le_trans ((hgK_spec ⟨x, hxK⟩).2 w hw_mem) hw_norm
        exact ⟨x, gK ⟨x, hxK⟩,
          ⟨⟨hxK, (hgK_spec ⟨x, hxK⟩).1, hgK_norm⟩, hmle⟩, rfl⟩
      · rintro ⟨a, b, ⟨hΓab, hbsq⟩, rfl⟩
        refine ⟨hΓab.1, ?_⟩
        rw [hmFn_eq a hΓab.1]
        have hb_mem : b ∈ SubderivWithinAt f K a := hΓab.2.1
        have hge := (hgK_spec ⟨a, hΓab.1⟩).2 _ hb_mem
        have hg_nn : 0 ≤ ‖gK ⟨a, hΓab.1⟩‖ := norm_nonneg _
        have hb_nn : 0 ≤ ‖b‖ := norm_nonneg _
        nlinarith
    rw [hSet_eq]
    have hclosed_inter :
        IsClosed
          (Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            ‖q.2‖^2 ≤ c}) :=
      hΓ_closed.inter
        (isClosed_le ((continuous_norm.comp continuous_snd).pow 2) continuous_const)
    have hcompact :
        IsCompact
          (Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            ‖q.2‖^2 ≤ c}) :=
      hΓ_compact.of_isClosed_subset hclosed_inter Set.inter_subset_left
    exact (hcompact.image continuous_fst).isClosed
  have hKmeas : MeasurableSet K := hK_compact.isClosed.measurableSet
  -- mFn is Borel measurable: use `measurable_of_Iic` and split on K vs Kᶜ.
  have hmFn_meas : Measurable mFn := by
    refine measurable_of_Iic (fun c => ?_)
    -- mFn ⁻¹' Iic c = (K ∩ mFn ⁻¹' Iic c) ∪ (Kᶜ ∩ {x | (0 : ℝ) ≤ c}).
    have heq : mFn ⁻¹' Set.Iic c =
        (K ∩ mFn ⁻¹' Set.Iic c) ∪ (Kᶜ ∩ {_x | (0 : ℝ) ≤ c}) := by
      ext x
      by_cases hxK : x ∈ K
      · simp [hxK]
      · simp [Set.mem_preimage, hxK, hmFn_off x hxK, Set.mem_Iic]
    rw [heq]
    refine MeasurableSet.union (hmFn_level_closed c).measurableSet ?_
    by_cases h0 : (0 : ℝ) ≤ c
    · have : (Kᶜ ∩ {_x : EuclideanSpace ℝ (Fin n) | (0 : ℝ) ≤ c}) = Kᶜ := by
        ext x; simp [h0]
      rw [this]; exact hKmeas.compl
    · have : (Kᶜ ∩ {_x : EuclideanSpace ℝ (Fin n) | (0 : ℝ) ≤ c}) = ∅ := by
        ext x; simp [h0]
      rw [this]; exact MeasurableSet.empty
  -- Define the graph Γ_min as a Borel set: {q ∈ Γ : ‖q.2‖² ≤ mFn q.1}.
  set Γ_min : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    Γ ∩ {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | ‖q.2‖^2 ≤ mFn q.1}
    with hΓ_min_def
  have hΓ_min_meas : MeasurableSet Γ_min := by
    refine hΓ_closed.measurableSet.inter ?_
    have hfun_meas :
        Measurable
          (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖q.2‖^2 - mFn q.1) := by
      exact (((continuous_norm.comp continuous_snd).pow 2).measurable).sub
        (hmFn_meas.comp measurable_fst)
    have :
        {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) | ‖q.2‖^2 ≤ mFn q.1} =
          (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖q.2‖^2 - mFn q.1) ⁻¹' Set.Iic 0 := by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, sub_nonpos]
    rw [this]
    exact hfun_meas measurableSet_Iic
  -- Γ_min has singleton fibers indexed by K (via Lemma C uniqueness).
  -- Specifically, q ∈ Γ_min ↔ q.1 ∈ K ∧ q.2 = g q.1.
  have hΓ_min_iff :
      ∀ q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        q ∈ Γ_min ↔ q.1 ∈ K ∧ q.2 = g q.1 := by
    intro q
    refine ⟨?_, ?_⟩
    · rintro ⟨hqΓ, hsq⟩
      have hxK : q.1 ∈ K := hqΓ.1
      refine ⟨hxK, ?_⟩
      -- ‖q.2‖² ≤ mFn q.1 = ‖gK ⟨q.1, hxK⟩‖²; combined with q.2 ∈ ∂f gives equality.
      have hsq2 : ‖q.2‖^2 ≤ ‖gK ⟨q.1, hxK⟩‖^2 := by
        rw [← hmFn_eq q.1 hxK]; exact hsq
      have h_q2_mem : q.2 ∈ SubderivWithinAt f K q.1 := hqΓ.2.1
      have h_ge : ‖gK ⟨q.1, hxK⟩‖ ≤ ‖q.2‖ := (hgK_spec ⟨q.1, hxK⟩).2 _ h_q2_mem
      have hgnn : 0 ≤ ‖gK ⟨q.1, hxK⟩‖ := norm_nonneg _
      have hqnn : 0 ≤ ‖q.2‖ := norm_nonneg _
      have h_le : ‖q.2‖ ≤ ‖gK ⟨q.1, hxK⟩‖ := by nlinarith
      have hnorm_eq : ‖q.2‖ = ‖gK ⟨q.1, hxK⟩‖ := le_antisymm h_le h_ge
      -- Apply Lemma C uniqueness.
      obtain ⟨_, _, huniq⟩ :=
        ConvexOn.exists_minNormSubgrad hK_convex hf_conv hL hf_lip hxK
      have hgK_mem_sub : gK ⟨q.1, hxK⟩ ∈ SubderivWithinAt f K q.1 :=
        (hgK_spec ⟨q.1, hxK⟩).1
      have hq2_min : ∀ q' ∈ SubderivWithinAt f K q.1, ‖q.2‖ ≤ ‖q'‖ := by
        intro q' hq'
        rw [hnorm_eq]; exact (hgK_spec ⟨q.1, hxK⟩).2 q' hq'
      have hgK_min : ∀ q' ∈ SubderivWithinAt f K q.1, ‖gK ⟨q.1, hxK⟩‖ ≤ ‖q'‖ :=
        (hgK_spec ⟨q.1, hxK⟩).2
      have heq1 := huniq q.2 ⟨h_q2_mem, hq2_min⟩
      have heq2 := huniq (gK ⟨q.1, hxK⟩) ⟨hgK_mem_sub, hgK_min⟩
      have hgeq : g q.1 = gK ⟨q.1, hxK⟩ := by simp only [g, dif_pos hxK]
      rw [hgeq]; exact heq1.trans heq2.symm
    · rintro ⟨hxK, hq2⟩
      have hgeq : g q.1 = gK ⟨q.1, hxK⟩ := by simp only [g, dif_pos hxK]
      rw [hgeq] at hq2
      have hgK_mem : gK ⟨q.1, hxK⟩ ∈ SubderivWithinAt f K q.1 :=
        (hgK_spec ⟨q.1, hxK⟩).1
      obtain ⟨w, hw_mem, hw_norm⟩ :=
        ConvexOn.exists_subgradient_on_compactConvex hK_convex hf_conv hL hf_lip hxK
      have hgK_norm : ‖gK ⟨q.1, hxK⟩‖ ≤ L :=
        le_trans ((hgK_spec ⟨q.1, hxK⟩).2 w hw_mem) hw_norm
      refine ⟨⟨hxK, hq2 ▸ hgK_mem, hq2 ▸ hgK_norm⟩, ?_⟩
      change ‖q.2‖^2 ≤ mFn q.1
      rw [hq2, ← hmFn_eq q.1 hxK]
  -- π₁ : Γ_min → EuclideanSpace ℝ (Fin n) is continuous and injective.
  have hπ_inj :
      Set.InjOn
        (Prod.fst :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n)) Γ_min := by
    intro q hq q' hq' h_eq
    rw [Prod.mk.injEq]
    refine ⟨h_eq, ?_⟩
    have h1 := (hΓ_min_iff q).mp hq
    have h2 := (hΓ_min_iff q').mp hq'
    rw [h1.2, h2.2, h_eq]
  refine ⟨g, ?_, ?_, ?_⟩
  · -- Measurability of `g`.
    refine measurable_of_isClosed (fun C hC => ?_)
    have hpreim_eq : g ⁻¹' C = (g ⁻¹' C ∩ K) ∪ (g ⁻¹' C ∩ Kᶜ) := by
      ext x; constructor
      · intro hx; by_cases hxK : x ∈ K
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr ⟨hx, hxK⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    rw [hpreim_eq]
    refine MeasurableSet.union ?_ ?_
    · -- g⁻¹(C) ∩ K = π_1 '' (Γ_min ∩ univ ×ˢ C).
      have hSet_eq : g ⁻¹' C ∩ K = Prod.fst '' (Γ_min ∩ Set.univ ×ˢ C) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.mem_prod,
          Set.mem_univ, true_and, Prod.exists]
        constructor
        · rintro ⟨hxC, hxK⟩
          refine ⟨x, g x, ⟨?_, hxC⟩, rfl⟩
          exact (hΓ_min_iff (x, g x)).mpr ⟨hxK, rfl⟩
        · rintro ⟨a, b, ⟨hab_min, hb_C⟩, rfl⟩
          have hab_iff := (hΓ_min_iff (a, b)).mp hab_min
          refine ⟨?_, hab_iff.1⟩
          rw [← hab_iff.2]; exact hb_C
      rw [hSet_eq]
      have hSet_meas : MeasurableSet (Γ_min ∩ Set.univ ×ˢ C) :=
        hΓ_min_meas.inter (MeasurableSet.univ.prod hC.measurableSet)
      have hπ_cont' :
          ContinuousOn
            (Prod.fst :
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
                EuclideanSpace ℝ (Fin n)) (Γ_min ∩ Set.univ ×ˢ C) :=
        continuous_fst.continuousOn
      have hπ_inj' :
          Set.InjOn
            (Prod.fst :
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
                EuclideanSpace ℝ (Fin n)) (Γ_min ∩ Set.univ ×ˢ C) :=
        hπ_inj.mono Set.inter_subset_left
      exact hSet_meas.image_of_continuousOn_injOn hπ_cont' hπ_inj'
    · -- g⁻¹(C) ∩ Kᶜ.
      by_cases h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ C
      · have hSet_eq : g ⁻¹' C ∩ Kᶜ = Kᶜ := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
          refine ⟨fun h => h.2, fun hxK => ⟨?_, hxK⟩⟩
          have hg_eq : g x = 0 := by simp only [g, dif_neg hxK]
          rw [hg_eq]; exact h0
        rw [hSet_eq]; exact hKmeas.compl
      · have hSet_eq : g ⁻¹' C ∩ Kᶜ = ∅ := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro hxC hxK
          have hg_eq : g x = 0 := by simp only [g, dif_neg hxK]
          rw [hg_eq] at hxC; exact h0 hxC
        rw [hSet_eq]; exact MeasurableSet.empty
  · -- Norm bound `‖g x‖ ≤ L`.
    intro x
    by_cases hx : x ∈ K
    · -- For `x ∈ K`: use that `gK ⟨x, hx⟩` is min-norm and Lemma A gives a witness
      -- with norm `≤ L`.
      have hg_eq : g x = gK ⟨x, hx⟩ := by
        simp only [g, dif_pos hx]
      rw [hg_eq]
      obtain ⟨q, hq_mem, hq_norm⟩ :=
        ConvexOn.exists_subgradient_on_compactConvex hK_convex hf_conv hL hf_lip hx
      exact le_trans ((hgK_spec ⟨x, hx⟩).2 q hq_mem) hq_norm
    · -- For `x ∉ K`: `g x = 0` and `‖0‖ = 0 ≤ L`.
      have hg_eq : g x = 0 := by simp only [g, dif_neg hx]
      rw [hg_eq, norm_zero]
      exact hL
  · -- Subgradient inequality.
    intro x hx y hy
    have hg_eq : g x = gK ⟨x, hx⟩ := by simp only [g, dif_pos hx]
    rw [hg_eq]
    exact (hgK_spec ⟨x, hx⟩).1 y hy
