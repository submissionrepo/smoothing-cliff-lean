/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Equilibrium.RoyIdentity
public import Mathlib
public import Optlib.Convex.Farkas

/-!
# Consumer duality: KKT for the UMP and Roy's identity for actual demand

This file defines indirect utility for the utility-maximization problem over `budgetSetAt p w` and
relates actual maximizers to Roy's identity. The value `indirectUtility u p w` is the supremum of
`u` over the budget set; at strictly positive prices and nonnegative wealth it is attained for
continuous utilities and it is monotone in wealth.

The file also gives KKT conditions for a differentiable utility maximizer on the linear budget set
with nonnegativity constraints. The multiplier statement is then combined with `Roy.roy_identity`
to obtain Roy's identity for an actual smooth demand selection, and a second statement rewrites the
identity in terms of the indirect-utility value function when the selection agrees locally with the
value function.

## Main definitions

* `indirectUtility` — the value of the UMP at prices `p`, wealth `w`.

## Main statements

* `indirectUtility_eq_of_isMaxOn`, `exists_eq_indirectUtility`, `indirectUtility_mono_wealth` —
  value characterization, attainment, and monotonicity in wealth.
* `exists_nonneg_combination_of_polar` — finite Farkas lemma on `Fin L → ℝ`.
* `kkt_of_isMaxOn_budget` — KKT necessity for the UMP.
* `roy_identity_of_isMaxOn` — Roy's identity for a smooth utility maximizer, in terms of the
  utility `u ∘ xstar` of the demand selection.
* `eventuallyEq_indirectUtility_of_localMaxOn` — local optimality of the selection yields the
  value-equality `u ∘ xstar = indirectUtility` near `(p, w)`.
* `roy_identity_indirectUtility` — Roy's identity stated directly in terms of the value function
  `indirectUtility`, under the local value-equality hypothesis.
* `mem_argmaxRel_preferenceOfUtilityIn_iff` — bridge between `argmaxRel` and `IsMaxOn`.

## References

* Roy, Rene. 1947. “La Distribution Du Revenu Entre Les Divers Biens.” *Econometrica* 15 (3): 205.
  [https://doi.org/10.2307/1905479](https://doi.org/10.2307/1905479).

## Tags

indirect utility, roy's identity, kkt conditions, farkas lemma, consumer theory
-/

@[expose] public section

open ContinuousLinearMap Matrix Econlib.Optimization Econlib.Equilibrium.Roy

namespace Econlib.Equilibrium

variable {L : ℕ}

/-- **Indirect utility**: The value of the utility-maximization problem at prices `p`, wealth
`w`. -/
noncomputable def indirectUtility (u : (Fin L → ℝ) → ℝ) (p : Fin L → ℝ) (w : ℝ) : ℝ :=
  sSup (u '' budgetSetAt p w)

/-! ### Value characterization of the indirect utility

The defining `sSup` is attained at any budget-feasible maximizer, and is attained whenever the
budget set is compact (strictly positive prices) and `u` is continuous; it is monotone in wealth.
These let `indirectUtility` be read as the value function. -/

/-- **The indirect utility is the utility of any budget-feasible maximizer.** The defining supremum
is attained at `x`, so `indirectUtility u p w = u x`. -/
lemma indirectUtility_eq_of_isMaxOn {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {w : ℝ}
    {x : Fin L → ℝ} (hx : x ∈ budgetSetAt p w) (hmax : IsMaxOn u (budgetSetAt p w) x) :
    indirectUtility u p w = u x :=
  IsGreatest.csSup_eq ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact (isMaxOn_iff.mp hmax) y hy⟩

/-- **Attainment.** At strictly positive prices and nonnegative wealth the budget set is compact
and nonempty, so a continuous utility attains its maximum on it. -/
lemma exists_isMaxOn_budgetSetAt {u : (Fin L → ℝ) → ℝ} (hu : Continuous u)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 ≤ w) :
    ∃ x ∈ budgetSetAt p w, IsMaxOn u (budgetSetAt p w) x :=
  (isCompact_budgetSetAt_of_pos_prices hp w).exists_isMaxOn
    ⟨0, fun l => le_refl 0, by rw [dotProduct_zero]; exact hw⟩ hu.continuousOn

/-- **The indirect utility is attained.** At strictly positive prices and nonnegative wealth, there
is a budget-feasible bundle whose utility equals `indirectUtility u p w`. -/
lemma exists_eq_indirectUtility {u : (Fin L → ℝ) → ℝ} (hu : Continuous u)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w : ℝ} (hw : 0 ≤ w) :
    ∃ x ∈ budgetSetAt p w, indirectUtility u p w = u x := by
  obtain ⟨x, hx, hxmax⟩ := exists_isMaxOn_budgetSetAt hu hp hw
  exact ⟨x, hx, indirectUtility_eq_of_isMaxOn hx hxmax⟩

/-- **Monotonicity in wealth.** A richer consumer is weakly better off: A larger budget set
contains the optimizer of the smaller one. -/
lemma indirectUtility_mono_wealth {u : (Fin L → ℝ) → ℝ} (hu : Continuous u)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) {w w' : ℝ} (hw : 0 ≤ w) (hww' : w ≤ w') :
    indirectUtility u p w ≤ indirectUtility u p w' := by
  obtain ⟨x, hx, hxmax⟩ := exists_isMaxOn_budgetSetAt hu hp hw
  obtain ⟨x', hx', hx'max⟩ := exists_isMaxOn_budgetSetAt hu hp (hw.trans hww')
  rw [indirectUtility_eq_of_isMaxOn hx hxmax, indirectUtility_eq_of_isMaxOn hx' hx'max]
  exact (isMaxOn_iff.mp hx'max) x ⟨hx.1, hx.2.trans hww'⟩

/-- **Finite Farkas lemma on `Fin L → ℝ`** (theorem of alternatives, conic form). If a covector `c`
is nonpositive against every direction `d` on which all generators `g i` are nonpositive (i.e. `c`
lies in the polar of the polar cone of the generators), then `c` is a nonnegative combination of
the generators: `c = ∑ i, μ i • g i` with `μ ≥ 0`. -/
theorem exists_nonneg_combination_of_polar {ι : Type*} [Fintype ι]
    (g : ι → (Fin L → ℝ)) (c : Fin L → ℝ)
    (hpolar : ∀ d : Fin L → ℝ, (∀ i, g i ⬝ᵥ d ≤ 0) → c ⬝ᵥ d ≤ 0) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ c = ∑ i, μ i • g i := by
  classical
  -- Realize in `EuclideanSpace ℝ (Fin L)` via the linear equivalence `toEL`; enumerate `ι` by
  -- `Fin m` to get `ℕ`-indexed generators for `Farkas`. The polar hypothesis translates to
  -- Farkas' alternative after the substitution `d ↦ −z`.
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let toEL : (Fin L → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin L) := (WithLp.linearEquiv 2 ℝ _).symm
  let toE : (Fin L → ℝ) → EuclideanSpace ℝ (Fin L) := toEL
  let b : ℕ → EuclideanSpace ℝ (Fin L) := fun k =>
    if h : k < m then toE (g (e.symm ⟨k, h⟩)) else 0
  let a : ℕ → EuclideanSpace ℝ (Fin L) := fun _ => 0
  have hinner : ∀ (u : Fin L → ℝ) (z : EuclideanSpace ℝ (Fin L)),
      inner ℝ (toE u) z = u ⬝ᵥ z.ofLp := by
    intro u z
    rw [PiLp.inner_apply]
    simp only [toE, toEL, WithLp.linearEquiv_symm_apply, dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hfarkas := Farkas (τ := (∅ : Finset ℕ)) (σ := Finset.range m) (a := a) (b := b)
    (c := toE c)
  have halt : ¬ (∃ z : EuclideanSpace ℝ (Fin L),
      (∀ i ∈ (∅ : Finset ℕ), inner ℝ (a i) z = (0 : ℝ)) ∧
      (∀ i ∈ Finset.range m, inner ℝ (b i) z ≥ (0 : ℝ)) ∧ inner ℝ (toE c) z < (0 : ℝ)) := by
    rintro ⟨z, -, hz_gen, hz_c⟩
    set d : Fin L → ℝ := -z.ofLp with hd
    have hgen : ∀ i, g i ⬝ᵥ d ≤ 0 := by
      intro i
      have hi : (e i : ℕ) ∈ Finset.range m := Finset.mem_range.2 (e i).isLt
      have := hz_gen (e i : ℕ) hi
      have hbi : b (e i : ℕ) = toE (g i) := by
        simp only [b, (e i).isLt, dif_pos, Fin.eta, Equiv.symm_apply_apply]
      rw [hbi, hinner] at this
      rw [hd, dotProduct_neg]
      linarith
    have hc := hpolar d hgen
    have hcz : inner ℝ (toE c) z = - (c ⬝ᵥ d) := by
      rw [hinner, hd, dotProduct_neg]; ring
    rw [hcz] at hz_c
    linarith
  obtain ⟨lam, mu, hmu_nonneg, hsum⟩ := hfarkas.mpr halt
  have hmem : ∀ i : ι, (e i : ℕ) ∈ Finset.range m := fun i => Finset.mem_range.2 (e i).isLt
  let eσ : ι ≃ {k // k ∈ Finset.range m} :=
    { toFun := fun i => ⟨e i, hmem i⟩
      invFun := fun k => e.symm ⟨k.1, Finset.mem_range.1 k.2⟩
      left_inv := fun i => by simp
      right_inv := fun k => by simp }
  refine ⟨fun i => mu (eσ i), fun i => hmu_nonneg _, ?_⟩
  have htoE_inj : Function.Injective toE := toEL.injective
  apply htoE_inj
  have htoE_sum : toE (∑ i : ι, mu (eσ i) • g i) = ∑ i : ι, mu (eσ i) • toE (g i) := by
    simp only [toE, map_sum, map_smul]
  rw [htoE_sum, hsum, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  refine (Fintype.sum_equiv eσ _ _ ?_).symm
  intro i
  have hcoe : (eσ i : ℕ) = (e i : ℕ) := rfl
  have hbi : b (eσ i : ℕ) = toE (g i) := by
    rw [hcoe]
    change (if h : (e i : ℕ) < m then toE (g (e.symm ⟨(e i : ℕ), h⟩)) else 0) = toE (g i)
    rw [dif_pos (e i).isLt]
    congr 1
    rw [Fin.eta, Equiv.symm_apply_apply]
  rw [hbi]

/-- **KKT necessity for the UMP.** If `x` maximizes a differentiable utility `u` over the budget
set, there exist nonnegative multipliers `lam : Option (Fin L) → ℝ` (`none` for the budget,
`some l` for nonnegativity of good `l`) satisfying complementary slackness and Lagrangian
stationarity `∇u = lam none • p − Σ_l lam (some l) • e_l`. -/
theorem kkt_of_isMaxOn_budget {u : (Fin L → ℝ) → ℝ} {p : Fin L → ℝ} {w : ℝ} {x : Fin L → ℝ}
    {Du : (Fin L → ℝ) →L[ℝ] ℝ}
    (hu : HasFDerivAt u Du x)
    (hx : x ∈ budgetSetAt p w)
    (hmax : IsMaxOn u (budgetSetAt p w) x) :
    ∃ lam : Roy.CIdx L → ℝ, (∀ i, 0 ≤ lam i) ∧
      lam none * (p ⬝ᵥ x - w) = 0 ∧ (∀ l, lam (some l) * x l = 0) ∧
      (Roy.objFDeriv Du).comp (inl ℝ (Fin L → ℝ) (Roy.Param L))
        = ∑ i, lam i • (Roy.conFDeriv x p i).comp (inl ℝ (Fin L → ℝ) (Roy.Param L)) := by
  -- Reduction: the `x`-inclusion `inl` collapses parameter parts, leaving pure `x`-derivatives.
  have hobj_red : (Roy.objFDeriv Du).comp (inl ℝ (Fin L → ℝ) (Roy.Param L)) = Du := by
    ext d; simp [Roy.objFDeriv]
  have hcon_none_red :
      (Roy.conFDeriv x p none).comp (inl ℝ (Fin L → ℝ) (Roy.Param L)) = Roy.dotL p := by
    ext d; simp [Roy.conFDeriv]
  have hcon_some_red : ∀ l : Fin L,
      (Roy.conFDeriv x p (some l)).comp (inl ℝ (Fin L → ℝ) (Roy.Param L))
        = -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l) := by
    intro l; ext d; simp [Roy.conFDeriv]
  -- Variational inequality: the directional derivative toward any feasible point is nonpositive.
  have hVI : ∀ y ∈ budgetSetAt p w, Du (y - x) ≤ 0 := by
    intro y hy
    have hseg : segment ℝ x y ⊆ budgetSetAt p w :=
      (budgetSetAt_convex p w).segment_subset hx hy
    have htan : y - x ∈ posTangentConeAt (budgetSetAt p w) x :=
      sub_mem_posTangentConeAt_of_segment_subset hseg
    exact hmax.localize.hasFDerivWithinAt_nonpos hu.hasFDerivWithinAt htan
  -- Cone form: `Du d ≤ 0` for every direction `d` respecting the active constraints.
  -- For small `t > 0`, `x + t d` is feasible: nonnegativity persists (active sign or positivity)
  -- and the budget persists (binding case uses `p ⬝ᵥ d ≤ 0`; slack case uses continuity).
  have hVIcone : ∀ d : Fin L → ℝ,
      (p ⬝ᵥ x = w → p ⬝ᵥ d ≤ 0) → (∀ l, x l = 0 → 0 ≤ d l) → Du d ≤ 0 := by
    intro d hbud hcoord
    have hcoord_ev : ∀ l : Fin L, ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ x l + t * d l := by
      intro l
      rcases eq_or_lt_of_le (hx.1 l) with hxl | hxl
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have hdl : 0 ≤ d l := hcoord l hxl.symm
        have : 0 ≤ t * d l := mul_nonneg (le_of_lt ht) hdl
        rw [← hxl]; linarith
      · have hcont : ContinuousAt (fun t : ℝ => x l + t * d l) 0 := by fun_prop
        have hpos : (0 : ℝ) < x l + (0 : ℝ) * d l := by simpa using hxl
        have := hcont.eventually (eventually_gt_nhds hpos)
        filter_upwards [nhdsWithin_le_nhds this] with t ht
        exact le_of_lt ht
    have hbud_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), p ⬝ᵥ (x + t • d) ≤ w := by
      have hexp : ∀ t : ℝ, p ⬝ᵥ (x + t • d) = p ⬝ᵥ x + t * (p ⬝ᵥ d) := by
        intro t; rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      rcases eq_or_lt_of_le hx.2 with hbind | hslack
      · filter_upwards [self_mem_nhdsWithin] with t ht
        rw [hexp]
        have hpd : p ⬝ᵥ d ≤ 0 := hbud hbind
        have : t * (p ⬝ᵥ d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) hpd
        linarith [hbind]
      · have hcont : ContinuousAt (fun t : ℝ => p ⬝ᵥ x + t * (p ⬝ᵥ d)) 0 := by fun_prop
        have hlt : p ⬝ᵥ x + (0 : ℝ) * (p ⬝ᵥ d) < w := by simpa using hslack
        have := hcont.eventually (eventually_lt_nhds hlt)
        filter_upwards [nhdsWithin_le_nhds this] with t ht
        rw [hexp]; exact le_of_lt ht
    have hfeas_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + t • d ∈ budgetSetAt p w := by
      have hall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ l, 0 ≤ x l + t * d l :=
        Filter.eventually_all.2 hcoord_ev
      filter_upwards [hall, hbud_ev] with t hnn hbudt
      refine ⟨fun l => ?_, hbudt⟩
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hnn l
    obtain ⟨t, hfeas, ht_pos⟩ := (hfeas_ev.and self_mem_nhdsWithin).exists
    have hDu_t : Du (t • d) ≤ 0 := by simpa using hVI (x + t • d) hfeas
    have hDu_lin : Du (t • d) = t * Du d := by rw [map_smul, smul_eq_mul]
    rw [hDu_lin] at hDu_t
    have htpos : 0 < t := Set.mem_Ioi.mp ht_pos
    by_contra hpos
    push Not at hpos
    exact absurd hDu_t (not_le.2 (mul_pos htpos hpos))
  -- Farkas: `Du` lies in the cone of active constraint normals, giving nonnegative multipliers.
  obtain ⟨lam, hlam_nonneg, hcs_budget, hcs_nonneg, hstat⟩ :
      ∃ lam : Roy.CIdx L → ℝ, (∀ i, 0 ≤ lam i) ∧
        lam none * (p ⬝ᵥ x - w) = 0 ∧ (∀ l, lam (some l) * x l = 0) ∧
        Du = lam none • Roy.dotL p
              - ∑ l, lam (some l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l) := by
    classical
    -- Represent `Du` as the dot product with its Riesz vector `gu`.
    set gu : Fin L → ℝ := fun l => Du (Pi.single l (1 : ℝ)) with hgu
    have hDu_dot : ∀ d : Fin L → ℝ, Du d = gu ⬝ᵥ d := by
      intro d
      have hdecomp : d = ∑ l, d l • (Pi.single l (1 : ℝ) : Fin L → ℝ) := by
        ext k; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
      conv_lhs => rw [hdecomp]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct, hgu]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
    -- The stationarity identity for CLMs follows from the vector identity for `gu`.
    have hstat_of_vec : ∀ lam : Roy.CIdx L → ℝ,
        gu = lam none • p - ∑ l, lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ) →
        Du = lam none • Roy.dotL p
              - ∑ l, lam (some l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l) := by
      intro lam hvec
      ext d
      rw [hDu_dot, hvec]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sum_apply, dotL_apply, ContinuousLinearMap.proj_apply,
        sub_dotProduct, sum_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul,
        one_mul]
    by_cases hbind : p ⬝ᵥ x = w
    · -- Budget binds: generators are `p` and `−e_l` for active `l`.
      let ι : Type := Option {l : Fin L // x l = 0}
      let g : ι → (Fin L → ℝ) := fun i =>
        match i with
        | none => p
        | some l => -Pi.single (l : Fin L) (1 : ℝ)
      have hpolar : ∀ d : Fin L → ℝ, (∀ i, g i ⬝ᵥ d ≤ 0) → gu ⬝ᵥ d ≤ 0 := by
        intro d hd
        have hpd : p ⬝ᵥ d ≤ 0 := hd none
        have hact : ∀ l, x l = 0 → 0 ≤ d l := by
          intro l hl
          have := hd (some ⟨l, hl⟩)
          simp only [g, neg_dotProduct, single_dotProduct, one_mul] at this
          linarith
        have := hVIcone d (fun _ => hpd) hact
        rwa [hDu_dot] at this
      obtain ⟨μ, hμ_nonneg, hμ_sum⟩ :=
        exists_nonneg_combination_of_polar (ι := ι) g gu hpolar
      set lam : Roy.CIdx L → ℝ := fun i =>
        match i with
        | none => μ none
        | some l => if h : x l = 0 then μ (some ⟨l, h⟩) else 0 with hlam_def
      have hlam_none : lam none = μ none := rfl
      have hlam_some : ∀ l : Fin L, lam (some l) = if h : x l = 0 then μ (some ⟨l, h⟩) else 0 :=
        fun l => rfl
      refine ⟨lam, ?_, ?_, ?_, ?_⟩
      · rintro (_ | l)
        · rw [hlam_none]; exact hμ_nonneg none
        · rw [hlam_some]; split
          · exact hμ_nonneg _
          · exact le_refl 0
      · rw [hlam_none]; simp [hbind]
      · intro l; rw [hlam_some]; split
        · next h => simp [h]
        · simp
      · refine hstat_of_vec lam ?_
        -- Inactive coordinates have `lam (some l) = 0`; reindex the active-set sum over `ι`.
        have hsumeq : ∑ l : Fin L, lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ)
            = ∑ x_1 : {l // x l = 0},
                μ (some x_1) • (Pi.single (x_1 : Fin L) (1 : ℝ) : Fin L → ℝ) := by
          have hfilter : ∑ l : Fin L, lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ)
              = ∑ l ∈ Finset.univ.filter (fun l => x l = 0),
                  lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ) := by
            refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
            intro l _ hl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
            simp only [hlam_some, dif_neg hl, zero_smul]
          rw [hfilter, Finset.sum_subtype (p := fun l => x l = 0)
              (Finset.univ.filter (fun l => x l = 0))
              (fun l => by simp) (fun l => lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ))]
          refine Finset.sum_congr rfl fun x_1 _ => ?_
          simp only [hlam_some, dif_pos x_1.2]
        rw [hμ_sum, Fintype.sum_option]
        simp only [g, hlam_none, smul_neg, ← Finset.sum_neg_distrib, sub_eq_add_neg, hsumeq]
    · -- Budget slack: budget multiplier is `0`; only nonnegativity generators for active `l`.
      let ι : Type := {l : Fin L // x l = 0}
      let g : ι → (Fin L → ℝ) := fun l => -Pi.single (l : Fin L) (1 : ℝ)
      have hpolar : ∀ d : Fin L → ℝ, (∀ i, g i ⬝ᵥ d ≤ 0) → gu ⬝ᵥ d ≤ 0 := by
        intro d hd
        have hact : ∀ l, x l = 0 → 0 ≤ d l := by
          intro l hl
          have := hd ⟨l, hl⟩
          simp only [g, neg_dotProduct, single_dotProduct, one_mul] at this
          linarith
        have := hVIcone d (fun hcontra => absurd hcontra hbind) hact
        rwa [hDu_dot] at this
      obtain ⟨μ, hμ_nonneg, hμ_sum⟩ :=
        exists_nonneg_combination_of_polar (ι := ι) g gu hpolar
      set lam : Roy.CIdx L → ℝ := fun i =>
        match i with
        | none => 0
        | some l => if h : x l = 0 then μ ⟨l, h⟩ else 0 with hlam_def
      have hlam_none : lam none = 0 := rfl
      have hlam_some : ∀ l : Fin L, lam (some l) = if h : x l = 0 then μ ⟨l, h⟩ else 0 :=
        fun l => rfl
      refine ⟨lam, ?_, ?_, ?_, ?_⟩
      · rintro (_ | l)
        · rw [hlam_none]
        · rw [hlam_some]; split
          · exact hμ_nonneg _
          · exact le_refl 0
      · rw [hlam_none]; ring
      · intro l; rw [hlam_some]; split
        · next h => simp [h]
        · simp
      · refine hstat_of_vec lam ?_
        have hsumeq : ∑ l : Fin L, lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ)
            = ∑ x_1 : {l // x l = 0}, μ x_1 • (Pi.single (x_1 : Fin L) (1 : ℝ) : Fin L → ℝ) := by
          have hfilter : ∑ l : Fin L, lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ)
              = ∑ l ∈ Finset.univ.filter (fun l => x l = 0),
                  lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ) := by
            refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
            intro l _ hl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
            simp only [hlam_some, dif_neg hl, zero_smul]
          rw [hfilter, Finset.sum_subtype (p := fun l => x l = 0)
              (Finset.univ.filter (fun l => x l = 0))
              (fun l => by simp) (fun l => lam (some l) • (Pi.single l (1 : ℝ) : Fin L → ℝ))]
          refine Finset.sum_congr rfl fun x_1 _ => ?_
          simp only [hlam_some, dif_pos x_1.2]
        rw [hμ_sum, hlam_none, zero_smul, zero_sub, hsumeq, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x_1 _ => ?_
        simp only [g, smul_neg]
  refine ⟨lam, hlam_nonneg, hcs_budget, hcs_nonneg, ?_⟩
  rw [hobj_red, Fintype.sum_option, hcon_none_red]
  simp only [hcon_some_red]
  rw [hstat, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp only [smul_neg]

/-- **Roy's Identity for an actual maximizer** (componentwise), in terms of the utility of the
demand selection. If `xstar` selects, near `(p, w)`, a maximizer of a smooth utility over the
budget set, the budget always binds (local nonsatiation), active nonnegativity constraints persist
along the selection, and the budget multiplier is positive, then Roy's identity holds with
`v q w'
:= u (xstar (q, w'))`. The hypotheses `hxs`, `hbinds`, `hcorner`, and `hlampos` are the
standard regularity conditions on demand.

This differentiates `u ∘ xstar`. To obtain the identity for the value function `indirectUtility`,
combine with `eventuallyEq_indirectUtility_of_localMaxOn` and use `roy_identity_indirectUtility`,
or supply local optimality of the selection directly. -/
theorem roy_identity_of_isMaxOn {u : (Fin L → ℝ) → ℝ} (xstar : Roy.Param L → (Fin L → ℝ))
    {p : Fin L → ℝ} {w : ℝ} {Du : (Fin L → ℝ) →L[ℝ] ℝ} {Dxs : Roy.Param L →L[ℝ] (Fin L → ℝ)}
    (hu : HasFDerivAt u Du (xstar (p, w)))
    (hx : xstar (p, w) ∈ budgetSetAt p w)
    (hmax : IsMaxOn u (budgetSetAt p w) (xstar (p, w)))
    (hxs : HasFDerivAt xstar Dxs (p, w))
    -- budget binds along the whole selection near `(p,w)` (local nonsatiation):
    (hbinds : ∀ᶠ θ in nhds (p, w), θ.1 ⬝ᵥ xstar θ = θ.2)
    -- active nonnegativity constraints persist along the selection (strict complementarity):
    (hcorner : ∀ l, xstar (p, w) l = 0 → (∀ᶠ θ in nhds (p, w), xstar θ l = 0))
    -- the budget multiplier is strictly positive (wealth strictly valuable):
    (hlampos : ∀ lam : Roy.CIdx L → ℝ,
      (Roy.objFDeriv Du).comp (inl ℝ (Fin L → ℝ) (Roy.Param L))
        = ∑ i, lam i • (Roy.conFDeriv (xstar (p, w)) p i).comp (inl ℝ (Fin L → ℝ) (Roy.Param L)) →
      lam none * (p ⬝ᵥ xstar (p, w) - w) = 0 → (∀ l, lam (some l) * xstar (p, w) l = 0) →
      (∀ i, 0 ≤ lam i) → 0 < lam none) :
    ∀ l, xstar (p, w) l
      = - (deriv (fun w' => u (xstar (p, w'))) w)⁻¹ *
          (fderiv ℝ (fun q => u (xstar (q, w))) p (Pi.single l 1)) := by
  obtain ⟨lam, hlam_nonneg, hcs_budget, hcs_nonneg, hstat⟩ := kkt_of_isMaxOn_budget hu hx hmax
  have hlamB : 0 < lam none := hlampos lam hstat hcs_budget hcs_nonneg hlam_nonneg
  have hbind : ∀ i, lam i = 0 ∨ (∀ᶠ θ in nhds (p, w), Roy.con i (xstar θ) θ = 0) := by
    intro i
    cases i with
    | none => exact Or.inr (by filter_upwards [hbinds] with θ hθ; simp [Roy.con, hθ])
    | some l =>
        by_cases hxl : xstar (p, w) l = 0
        · exact Or.inr (by filter_upwards [hcorner l hxl] with θ hθ; simp [Roy.con, hθ])
        · exact Or.inl (by
            have := hcs_nonneg l
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · exact absurd h hxl)
  exact Roy.roy_identity u xstar lam p w hlamB Du hu Dxs hxs hstat hbind

/-- **Local optimality of the selection yields value-equality.** If, throughout a neighborhood of
`(p, w)`, the selection `xstar θ` is a budget-feasible maximizer of `u` over `budgetSetAt θ.1 θ.2`,
then `u (xstar θ)` equals the indirect-utility value `indirectUtility u θ.1 θ.2` eventually. This
is exactly the value-equality hypothesis consumed by `roy_identity_indirectUtility`. -/
lemma eventuallyEq_indirectUtility_of_localMaxOn {u : (Fin L → ℝ) → ℝ}
    (xstar : Roy.Param L → (Fin L → ℝ)) {p : Fin L → ℝ} {w : ℝ}
    (hloc : ∀ᶠ θ in nhds (p, w),
      xstar θ ∈ budgetSetAt θ.1 θ.2 ∧ IsMaxOn u (budgetSetAt θ.1 θ.2) (xstar θ)) :
    ∀ᶠ θ in nhds (p, w), u (xstar θ) = indirectUtility u θ.1 θ.2 := by
  filter_upwards [hloc] with θ hθ
  exact (indirectUtility_eq_of_isMaxOn hθ.1 hθ.2).symm

/-- **Roy's Identity for the indirect-utility value function** (componentwise) (Roy 1947). With the
same KKT/stationarity/binding data as `Roy.roy_identity`, plus the local value-equality hypothesis
`hval` — which says the selection's utility `u (xstar θ)` agrees with the value function
`indirectUtility u θ.1 θ.2` throughout a neighborhood of `(p, w)`, as delivered by local
feasibility and optimality of the selection (`eventuallyEq_indirectUtility_of_localMaxOn`) — Roy's
identity holds with the value function `indirectUtility` in place of `u ∘ xstar`:

`x*_l(p, w) = − (∂/∂w indirectUtility u p w)⁻¹ · (∂/∂p_l indirectUtility u p w)`. -/
theorem roy_identity_indirectUtility
    (u : (Fin L → ℝ) → ℝ)
    (xstar : Roy.Param L → (Fin L → ℝ)) (lam : Roy.CIdx L → ℝ)
    (p : Fin L → ℝ) (w : ℝ)
    (hlamB : 0 < lam none)
    (Du : (Fin L → ℝ) →L[ℝ] ℝ)
    (hu : HasFDerivAt u Du (xstar (p, w)))
    (Dxs : Roy.Param L →L[ℝ] (Fin L → ℝ))
    (hxs : HasFDerivAt xstar Dxs (p, w))
    (h_stat : (Roy.objFDeriv Du).comp (inl ℝ (Fin L → ℝ) (Roy.Param L))
      = ∑ i, lam i • (Roy.conFDeriv (xstar (p, w)) p i).comp (inl ℝ (Fin L → ℝ) (Roy.Param L)))
    (h_bind : ∀ i, lam i = 0 ∨
      (∀ᶠ θ in nhds (p, w), Roy.con i (xstar θ) θ = 0))
    -- local value-equality: the selection's utility equals the indirect utility near `(p, w)`:
    (hval : ∀ᶠ θ in nhds (p, w), u (xstar θ) = indirectUtility u θ.1 θ.2) :
    ∀ l, xstar (p, w) l
      = - (deriv (fun w' => indirectUtility u p w') w)⁻¹ *
          (fderiv ℝ (fun q => indirectUtility u q w) p (Pi.single l 1)) := by
  -- View `hval` as an `EventuallyEq` between the two functions of `θ`.
  have hvalEq : (fun θ => u (xstar θ))
      =ᶠ[nhds (p, w)] (fun θ : Roy.Param L => indirectUtility u θ.1 θ.2) := hval
  -- The wealth slice `w' ↦ (p, w')` and the price slice `q ↦ (q, w)` are continuous and map their
  -- base point to `(p, w)`, so they pull `nhds (p, w)` back to `nhds w` / `nhds p`. Composing
  -- `hvalEq` along them turns it into the two slice value-equalities.
  have hval_w : (fun w' => u (xstar (p, w'))) =ᶠ[nhds w] (fun w' => indirectUtility u p w') :=
    hvalEq.comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto' w (p, w) rfl)
  have hval_p : (fun q => u (xstar (q, w))) =ᶠ[nhds p] (fun q => indirectUtility u q w) :=
    hvalEq.comp_tendsto
      ((continuous_id.prodMk continuous_const).tendsto' p (p, w) rfl)
  -- Eventually-equal functions share `deriv` / `fderiv`, so the KKT-path conclusion transports.
  intro l
  have hkkt := Roy.roy_identity u xstar lam p w hlamB Du hu Dxs hxs h_stat h_bind l
  rw [hval_w.deriv_eq, hval_p.fderiv_eq] at hkkt
  exact hkkt

/-- **Bridge to the `Economy` demand correspondence.** For a utility-induced preference
`preferenceOfUtilityIn u`, membership in the greatest-element demand set `argmaxRel` is exactly
budget-feasible utility maximization. So an agent whose preference is represented by `u` demands a
maximizer of `u` over its budget set, and `roy_identity_of_isMaxOn` applies to its
`Economy.demand`. -/
lemma mem_argmaxRel_preferenceOfUtilityIn_iff {u : (Fin L → ℝ) → ℝ} {S : Set (Fin L → ℝ)}
    {x : Fin L → ℝ} :
    x ∈ Econlib.Optimization.argmaxRel (Econlib.Preferences.preferenceOfUtilityIn u) S
      ↔ x ∈ S ∧ IsMaxOn u S x := by
  constructor
  · rintro ⟨hxS, hmax⟩
    exact ⟨hxS, isMaxOn_iff.2 fun y hy =>
      (Econlib.Preferences.preferenceOfUtilityIn_le_iff u x y).mp (hmax y hy)⟩
  · rintro ⟨hxS, hmax⟩
    exact ⟨hxS, fun y hy =>
      (Econlib.Preferences.preferenceOfUtilityIn_le_iff u x y).mpr (isMaxOn_iff.1 hmax y hy)⟩

end Econlib.Equilibrium
