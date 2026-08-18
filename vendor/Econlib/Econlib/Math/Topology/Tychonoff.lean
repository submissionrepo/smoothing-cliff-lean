/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Brouwer
public import Mathlib.Topology.PartitionOfUnity

/-!
# Tychonoff fixed-point theorem

Every continuous self-map of a nonempty compact convex subset of a locally convex topological
vector space has a fixed point. This generalizes the Schauder fixed-point theorem from normed
spaces to locally convex topological vector spaces.

## Main statements

* `approxFixedPoint_locallyConvex` — existence of approximate fixed points with error in a given
  neighborhood of `0`
* `tychonoffFixedPoint` — Tychonoff's fixed-point theorem in a locally convex topological vector
  space

## Tags

tychonoff, schauder, fixed point, locally convex space
-/

@[expose] public section

open Filter Set Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [LocallyConvexSpace ℝ E]

/-! ### Approximate fixed points in locally convex TVS -/

omit [T2Space E] [LocallyConvexSpace ℝ E] in
/-- For any open convex neighborhood `U` of `0`, a continuous self-map of a compact convex set has
an approximate fixed point with error in `U`: Some `x` with `f x - x ∈ U`. -/
lemma approxFixedPoint_locallyConvex
    {K : Set E} (hcvx : Convex ℝ K) (hcmpct : IsCompact K) (hne : K.Nonempty)
    (f : C(K, K)) (U : Set E) (hU : U ∈ 𝓝 (0 : E)) (hUopen : IsOpen U)
    (hUcvx : Convex ℝ U) :
    ∃ x : K, (f x : E) - (x : E) ∈ U := by
  -- Strategy: cover K by translates {xᵢ + U}, build partition of unity, define
  -- "coordinate map" σ : K → stdSimplex (Fin m) using the weights, and "evaluation map"
  -- φ : (Fin m → ℝ) → E by ∑ αᵢ • xᵢ. Then g = σ ∘ f ∘ φ|_Δ : Δ → Δ is continuous.
  -- Brouwer on the simplex in ℝ^m gives a fixed point α₀, and φ(α₀) is the approx FP.
  have h0U : (0 : E) ∈ U := mem_of_mem_nhds hU
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcmpct
  -- Finite open cover of K
  obtain ⟨F, hF_sub, hF_cover⟩ := hcmpct.elim_nhds_subcover
    (fun x : E => { y | y - x ∈ U })
    (fun x _ => by
      -- {y | y - x ∈ U} = (· + x) '' U, open since U is open and translation is a homeomorphism
      exact (hUopen.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp [h0U]))
  -- I = ↥F as a Fintype, indexing the cover centers
  let I := ↥F
  haveI : NormalSpace K :=
    NormalSpace.of_compactSpace_r1Space (X := K)
  haveI : ParacompactSpace K := paracompact_of_compact
  -- The open cover indexed by F
  let Ucover : F → Set K := fun i =>
    Subtype.val ⁻¹' { y | y - (i : E) ∈ U }
  have hUcover_open : ∀ i, IsOpen (Ucover i) := fun i =>
    (continuous_subtype_val.sub continuous_const).isOpen_preimage U hUopen
  have hUcover_covers : (Set.univ : Set K) ⊆ ⋃ i, Ucover i := by
    intro y _
    simp only [Set.mem_iUnion] at *
    obtain ⟨x, hxF, hxy⟩ := Set.mem_iUnion₂.mp (hF_cover y.2)
    exact ⟨⟨x, hxF⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ Ucover
    hUcover_open hUcover_covers
  -- ρ is a partition of unity: ρᵢ : K → ℝ, ρᵢ ≥ 0, ∑ ρᵢ = 1, supp ρᵢ ⊆ Ucover i
  -- Define σ : K → stdSimplex ℝ I using the weights
  let σ : K → stdSimplex ℝ I := fun y =>
    ⟨fun i => ρ i y, fun i => ρ.nonneg i y, by
      have := ρ.sum_eq_one (mem_univ y)
      rwa [finsum_eq_sum_of_fintype] at this⟩
  have hσ_cont : Continuous σ := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (ρ i).continuous
  -- Define φ : (F → ℝ) → E by φ(α) = ∑ αᵢ • xᵢ
  let centers : F → E := fun i => (i : E)
  let φ : (F → ℝ) → E := fun α => ∑ i : F, α i • centers i
  have hφ_cont : Continuous φ := continuous_finset_sum Finset.univ fun i _ =>
    (continuous_apply i).smul continuous_const
  -- φ(σ(y)) = p(y) = ∑ ρᵢ(y) • xᵢ, a continuous selection
  -- For y ∈ K, y - p(y) = ∑ ρᵢ(y)(y - xᵢ) ∈ U (convex combination of elements of U)
  -- φ maps stdSimplex into convexHull ↑{xᵢ} ⊆ K
  have hφ_simplex_sub_K : ∀ α ∈ stdSimplex ℝ I, φ α ∈ K := by
    intro α hα
    exact hcvx.sum_mem (fun i _ => hα.1 i) hα.2 (fun i _ => hF_sub i.1 i.2)
  -- g = σ ∘ f ∘ (φ restricted to Δ as K-valued) : Δ → Δ
  let Δ := stdSimplex ℝ I
  let g : Δ → Δ := fun ⟨α, hα⟩ =>
    σ (f ⟨φ α, hφ_simplex_sub_K α hα⟩)
  have hg_cont : Continuous g :=
    hσ_cont.comp (f.continuous.comp ((hφ_cont.comp continuous_subtype_val).subtype_mk _))
  -- Δ is compact convex nonempty in the FD normed space (F → ℝ)
  have hΔ_compact : IsCompact Δ := isCompact_stdSimplex ℝ I
  have hΔ_convex : Convex ℝ Δ := convex_stdSimplex _ _
  have hΔ_ne : (Δ : Set (I → ℝ)).Nonempty := by
    have hF_ne : F.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; obtain ⟨y, hy⟩ := hne; have := hF_cover hy; simp [h] at this
    haveI : Nonempty I := hF_ne.coe_sort
    exact ⟨fun _ => (Fintype.card I : ℝ)⁻¹, fun _ => by positivity, by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀]
      exact Nat.cast_ne_zero.mpr (Fintype.card_pos (α := I)).ne'⟩
  -- Apply Brouwer to get α₀ with g(α₀) = α₀
  haveI : FiniteDimensional ℝ (I → ℝ) := inferInstance
  obtain ⟨⟨α₀, hα₀⟩, hfp⟩ := brouwerFixedPoint Δ hΔ_convex hΔ_compact hΔ_ne ⟨g, hg_cont⟩
  -- x₀ = φ(α₀) ∈ K, and σ(f(x₀)) = α₀
  let x₀ : K := ⟨φ α₀, hφ_simplex_sub_K α₀ hα₀⟩
  use x₀
  -- g(α₀) = α₀ means σ(f(x₀)) = α₀
  -- g(α₀) = α₀ means σ(f(x₀)) = ⟨α₀, hα₀⟩
  have hσfx₀ : σ (f x₀) = ⟨α₀, hα₀⟩ := hfp
  -- φ(σ(f(x₀))) = φ(α₀) = x₀.val, so p(f(x₀)) = x₀.val
  -- f(x₀) - x₀ = f(x₀) - p(f(x₀)) = f(x₀) - φ(σ(f(x₀))) = f(x₀) - φ(α₀)
  -- But φ(σ(y)) = ∑ ρᵢ(y) • xᵢ, and y - φ(σ(y)) = ∑ ρᵢ(y)(y - xᵢ) ∈ U
  -- (since ρᵢ(y) > 0 ⟹ y ∈ supp ρᵢ ⊆ Ucover i ⟹ y - xᵢ ∈ U, and U is convex)
  have key : ∀ y : K, (y : E) - φ (σ y) ∈ U := by
    intro y
    change (y : E) - ∑ i, ρ i y • centers i ∈ U
    -- y = ∑ ρᵢ(y) • y (since ∑ ρᵢ = 1)
    have hsum1 : ∑ i : F, ρ i y = 1 := by
      rw [← finsum_eq_sum_of_fintype]; exact ρ.sum_eq_one (mem_univ y)
    rw [show (y : E) = ∑ i : F, ρ i y • (y : E)
      from by rw [← Finset.sum_smul, hsum1, one_smul]]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    -- ∑ ρᵢ(y) • (y - xᵢ) ∈ U (convex combination of elements of U)
    -- For i with ρᵢ(y) ≠ 0, subordination gives (y - xᵢ) ∈ U.
    -- For i with ρᵢ(y) = 0, the summand vanishes. Replace those points with 0 ∈ U.
    have hsubord : ∀ i : F, ρ i y ≠ 0 → (↑y : E) - centers i ∈ U := fun i hi =>
      hρ i (subset_tsupport _ (Function.mem_support.mpr hi))
    -- Rewrite the sum: replace (y - xᵢ) by 0 when ρᵢ(y) = 0 (summand is 0 either way)
    have hsame : ∀ i, ρ i y • ((↑y : E) - centers i) =
        ρ i y • (if ρ i y = 0 then (0 : E) else (↑y : E) - centers i) := by
      intro i; split_ifs with h <;> simp [h]
    simp_rw [hsame]
    apply hUcvx.sum_mem
    · intro i _; exact ρ.nonneg i y
    · exact hsum1
    · intro i _
      split_ifs with h
      · exact h0U
      · exact hsubord i h
  -- Apply: f(x₀) - x₀ = f(x₀) - φ(σ(f(x₀))) = f(x₀) - φ(α₀)
  have hkey := key (f x₀)
  -- φ(σ(f(x₀))) = φ(α₀) = x₀.val
  -- hσfx₀ : σ (f x₀) = ⟨α₀, hα₀⟩, so ↑(σ (f x₀)) = α₀
  have hφσ : φ ↑(σ (f x₀)) = (x₀ : E) :=
    congrArg φ (congrArg Subtype.val hσfx₀)
  rwa [hφσ] at hkey

/-! ### Main theorem -/

/-- **Tychonoff's fixed-point theorem**: Every continuous self-map of a nonempty compact convex
subset of a locally convex topological vector space has a fixed point. -/
theorem tychonoffFixedPoint
    (K : Set E) (hcvx : Convex ℝ K) (hcmpct : IsCompact K) (hne : K.Nonempty)
    (f : C(K, K)) : ∃ x, f x = x := by
  -- Error map e(x) = f(x) - x
  let e : K → E := fun x => (f x : E) - (x : E)
  have he_cont : Continuous e :=
    (continuous_subtype_val.comp f.continuous).sub continuous_subtype_val
  -- For V open convex ∈ 𝓝 0, S(V) = {x : K | e(x) ∈ closure V} is closed nonempty
  let S : Set E → Set K := fun V => e ⁻¹' closure V
  have hS_closed : ∀ V, IsClosed (S V) := fun V => isClosed_closure.preimage he_cont
  -- Each S(V) is nonempty for open convex V ∈ 𝓝 0
  have hS_ne : ∀ V, IsOpen V → Convex ℝ V → V ∈ 𝓝 (0 : E) → (S V).Nonempty := by
    intro V hVo hVc hVn
    obtain ⟨x, hx⟩ := approxFixedPoint_locallyConvex hcvx hcmpct hne f V hVn hVo hVc
    exact ⟨x, subset_closure hx⟩
  -- Use IsCompact.nonempty_iInter for the FIP on K
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcmpct
  -- We work with the basis of open convex neighborhoods of 0
  -- The key: ⋂ {closure V | V open convex, V ∈ 𝓝 0} = {0} in a T2 TVS
  -- (since T2 topological groups are T3/regular)
  -- Any x* with e(x*) ∈ ⋂ closure V must have e(x*) = 0, i.e., f(x*) = x*
  -- Proof by contradiction: if e(x) ≠ 0, by T3 regularity find open V ∈ 𝓝 0
  -- with e(x) ∉ closure V, contradicting x ∈ S(V).
  suffices ∃ x : K, ∀ V, IsOpen V → Convex ℝ V → V ∈ 𝓝 (0 : E) → e x ∈ closure V by
    obtain ⟨x, hx⟩ := this
    use x
    apply Subtype.ext
    -- e(x) = f(x) - x. We need f(x) = x, i.e., e(x) = 0
    suffices e x = 0 by simpa [e, sub_eq_zero] using this
    -- In a T2 TVS (which is T3), ⋂ {closure V | ...} = {0}
    by_contra h
    -- e(x) ≠ 0, so by regularity, find disjoint open sets separating 0 and e(x)
    haveI : RegularSpace E := IsTopologicalAddGroup.regularSpace E
    -- {e(x)}ᶜ is open (T2) and contains 0 (since e(x) ≠ 0), so {e(x)}ᶜ ∈ 𝓝 0
    have h_nhds : ({e x}ᶜ : Set E) ∈ 𝓝 (0 : E) :=
      isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm h))
    -- By regularity, find closed t ∈ 𝓝 0 with t ⊆ {e(x)}ᶜ
    obtain ⟨t, ht_nhds, ht_closed, ht_sub⟩ := exists_mem_nhds_isClosed_subset h_nhds
    -- By local convexity, find open convex V ∈ 𝓝 0 with V ⊆ t
    obtain ⟨V, ⟨hV_nhds, hV_cvx⟩, hV_sub⟩ :=
      (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (0 : E)).mem_iff.mp ht_nhds
    -- `interior V` is open, convex (interior of a convex set in a TVS), and a neighborhood of `0`.
    have hV_open : IsOpen (interior V) := isOpen_interior
    have hV'_nhds : interior V ∈ 𝓝 (0 : E) := interior_mem_nhds.mpr hV_nhds
    have hV'_cvx : Convex ℝ (interior V) := hV_cvx.interior
    -- e(x) ∈ closure (interior V) by hx (since interior V is open, convex, ∈ 𝓝 0)
    have h_in : e x ∈ closure (interior V) :=
      hx (interior V) hV_open hV'_cvx hV'_nhds
    -- But closure (interior V) ⊆ closure V ⊆ t ⊆ {e(x)}ᶜ
    -- closure (interior V) ⊆ closure V ⊆ t ⊆ {e x}ᶜ contradicts e x ∈ closure (interior V)
    have h_closure_sub : closure (interior V) ⊆ t :=
      (closure_mono interior_subset).trans (closure_minimal hV_sub ht_closed)
    exact ht_sub (h_closure_sub h_in) rfl
  -- FIP argument: the family {S(V)} of closed subsets of compact K has FIP,
  -- so the intersection is nonempty.
  -- Each `S V` is closed and nonempty in the compact space `K`, and every finite intersection
  -- `⋂ᵢ S (Vᵢ)` contains `S W` for an open convex `W ⊆ ⋂ᵢ Vᵢ`. By the finite intersection
  -- property, `⋂ S V` is nonempty.
  by_contra h_empty
  push Not at h_empty
  -- h_empty: ∀ x : K, ∃ V, IsOpen V ∧ Convex ℝ V ∧ V ∈ 𝓝 0 ∧ e x ∉ closure V
  -- For each x, (closure V)ᶜ is an open neighborhood of e(x), so e⁻¹((closure V)ᶜ) is open
  -- These form an open cover of K; extract finite subcover
  choose V hVo hVc hVn hVnot using h_empty
  -- {(S (V x))ᶜ | x} is an open cover of K; hVnot witnesses membership
  have hcover_open : ∀ x : K, IsOpen ((S (V x))ᶜ) :=
    fun x => (hS_closed (V x)).isOpen_compl
  -- By compactness, extract finite subcover
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : K => (S (V x))ᶜ) hcover_open
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hVnot x⟩)
  -- W = ⋂ V(xᵢ) is open (finite intersection) and ∈ 𝓝 0
  let W := ⋂ x ∈ F, V x
  have hW_nhds : W ∈ 𝓝 (0 : E) := by
    apply Filter.biInter_mem F.finite_toSet |>.mpr
    intro x _; exact hVn x
  -- Find open convex W' ⊆ W with W' ∈ 𝓝 0
  obtain ⟨W', ⟨hW'_nhds, hW'_cvx⟩, hW'_sub⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (0 : E)).mem_iff.mp hW_nhds
  have hW'_open : IsOpen (interior W') := isOpen_interior
  have hW'_cvx' : Convex ℝ (interior W') := hW'_cvx.interior
  have hW'_nhds' : interior W' ∈ 𝓝 (0 : E) := interior_mem_nhds.mpr hW'_nhds
  -- S(interior W') is nonempty
  obtain ⟨x₀, hx₀⟩ := hS_ne (interior W') hW'_open hW'_cvx' hW'_nhds'
  -- x₀ ∈ S(interior W') means e(x₀) ∈ closure (interior W') ⊆ closure W' ⊆
  -- closure (V xᵢ) for each i.
  -- So x₀ ∈ S(V xᵢ) for each xᵢ ∈ F
  have hx₀_in_all : ∀ x ∈ F, x₀ ∈ S (V x) := by
    intro x hxF
    apply closure_mono (interior_subset.trans (hW'_sub.trans _)) hx₀
    exact Set.biInter_subset_of_mem hxF
  -- But x₀ ∈ ⋃ (S(V xᵢ))ᶜ by the finite cover
  obtain ⟨x, hxF, hx_not⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x₀))
  exact hx_not (hx₀_in_all x hxF)
