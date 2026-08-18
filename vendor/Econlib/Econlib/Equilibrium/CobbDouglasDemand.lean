/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Equilibrium.Economy
public import Econlib.Preferences.Utility.CobbDouglas
public import Mathlib.Analysis.MeanInequalities

/-!
# Cobb–Douglas demand

This file gives the closed-form demand correspondence for Cobb-Douglas utility. With at least one
commodity, strictly positive prices `p`, and strictly positive wealth `w`, the preference-maximal
budget-feasible bundle is unique. For each good `l`, the consumer spends the normalized share
`α l / ∑ i, α i` of wealth on that good, so demand is `l ↦ (α l / ∑ i, α i) * w / p l`.

The economy-level theorem specializes this formula to an `Economy` whose agent `a` has Cobb-Douglas
preferences. At strictly positive prices and strictly positive endowment wealth `p ⬝ᵥ E.endow a`,
`E.demand p a` is the singleton containing the same expenditure-share bundle.

## Main statements

* `CobbDouglasUtility.argmaxRel_budgetSetAt` — the budget-set argmax is the singleton
  expenditure-share bundle.
* `Economy.demand_eq_singleton_of_cobbDouglas` — the same formula for an `Economy`'s demand
  correspondence at endowment wealth.

## References

* Cobb, Charles W., and Paul H. Douglas. 1928. “A Theory of Production.” *American Economic Review*
  18 (1): 139–65.

## Tags

cobb-douglas, demand, expenditure share, unique maximizer
-/

@[expose] public section

namespace Econlib.Equilibrium

open Matrix Econlib.Preferences

variable {L : ℕ}

/-! ## Weighted AM–GM over the budget

Helpers phrased for abstract normalized weights `β` (strictly positive, summing to one); the
main theorem instantiates `β l := cd.α l / ∑ i, cd.α i`. -/

/-- **Substituted-coordinate factorization.** For nonnegative `y`, the weighted geometric mean
factors through the substituted coordinates `z l = p l * y l / β l`. -/
private lemma prod_rpow_factor {β p y : Fin L → ℝ}
    (hβ : ∀ l, 0 < β l) (hp : ∀ l, 0 < p l) (hy : ∀ l, 0 ≤ y l) :
    ∏ l, y l ^ β l
      = (∏ l, (p l * y l / β l) ^ β l) * ∏ l, (β l / p l) ^ β l := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Real.mul_rpow (div_nonneg (mul_nonneg (hp l).le (hy l)) (hβ l).le)
    (div_nonneg (hβ l).le (hp l).le)]
  congr 1
  field_simp [(hβ l).ne', (hp l).ne']

/-- The weighted sum of substituted coordinates is the bundle's value. -/
private lemma sum_smul_substituted {β p y : Fin L → ℝ} (hβ : ∀ l, 0 < β l) :
    ∑ l, β l * (p l * y l / β l) = p ⬝ᵥ y := by
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun l _ => by
    rw [mul_comm (β l), div_mul_cancel₀ _ (hβ l).ne']

/-- **Budget bound for weighted geometric means.** For nonnegative `y` and normalized weights `β`,
`∏ (y l)^(β l) ≤ (p ⬝ᵥ y) * ∏ (β l / p l)^(β l)`. This is weighted AM–GM in the substituted
coordinates. -/
private lemma prod_rpow_le_dotProduct_mul {β p y : Fin L → ℝ}
    (hβ : ∀ l, 0 < β l) (hβ1 : ∑ l, β l = 1) (hp : ∀ l, 0 < p l) (hy : ∀ l, 0 ≤ y l) :
    ∏ l, y l ^ β l ≤ (p ⬝ᵥ y) * ∏ l, (β l / p l) ^ β l := by
  rw [prod_rpow_factor hβ hp hy]
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hβ l).le (hp l).le) _)
  calc ∏ l, (p l * y l / β l) ^ β l
      ≤ ∑ l, β l * (p l * y l / β l) :=
        Real.geom_mean_le_arith_mean_weighted Finset.univ β _ (fun l _ => (hβ l).le) hβ1
          (fun l _ => div_nonneg (mul_nonneg (hp l).le (hy l)) (hβ l).le)
    _ = p ⬝ᵥ y := sum_smul_substituted hβ

/-- **The expenditure-share bundle attains the budget bound.** -/
private lemma prod_rpow_shareBundle {β p : Fin L → ℝ} {w : ℝ}
    (hβ : ∀ l, 0 < β l) (hβ1 : ∑ l, β l = 1) (hp : ∀ l, 0 < p l) (hw : 0 < w) :
    ∏ l, (β l * w / p l) ^ β l = w * ∏ l, (β l / p l) ^ β l := by
  calc ∏ l, (β l * w / p l) ^ β l
      = ∏ l, (w ^ β l * (β l / p l) ^ β l) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← Real.mul_rpow hw.le (div_nonneg (hβ l).le (hp l).le)]
        congr 1
        ring
    _ = (∏ l, w ^ β l) * ∏ l, (β l / p l) ^ β l := Finset.prod_mul_distrib
    _ = w * ∏ l, (β l / p l) ^ β l := by
        rw [← Real.rpow_sum_of_pos hw, hβ1, Real.rpow_one]

/-- **Equality forces the expenditure-share bundle.** If a budget-feasible `y` attains the budget
bound, the AM–GM equality characterization forces the substituted coordinates constant, i.e.
`y l = β l * w / p l`. Budget binding (`p ⬝ᵥ y = w`) is forced by the same equality chain, so it is
not a hypothesis. -/
private lemma eq_share_of_prod_rpow_eq {β p y : Fin L → ℝ} {w : ℝ}
    (hβ : ∀ l, 0 < β l) (hβ1 : ∑ l, β l = 1) (hp : ∀ l, 0 < p l) (hy : ∀ l, 0 ≤ y l)
    (hbud : p ⬝ᵥ y ≤ w)
    (heq : ∏ l, y l ^ β l = w * ∏ l, (β l / p l) ^ β l) :
    y = fun l => β l * w / p l := by
  have hC_pos : 0 < ∏ l, (β l / p l) ^ β l :=
    Finset.prod_pos fun l _ => Real.rpow_pos_of_pos (div_pos (hβ l) (hp l)) _
  have hz_nonneg : ∀ l, 0 ≤ p l * y l / β l :=
    fun l => div_nonneg (mul_nonneg (hp l).le (hy l)) (hβ l).le
  -- Cancel the constant factor: the substituted geometric mean equals `w`.
  have hgm_eq_w : ∏ l, (p l * y l / β l) ^ β l = w := by
    have hfac : (∏ l, (p l * y l / β l) ^ β l) * ∏ l, (β l / p l) ^ β l
        = w * ∏ l, (β l / p l) ^ β l := by
      rw [← prod_rpow_factor hβ hp hy]; exact heq
    exact mul_right_cancel₀ hC_pos.ne' hfac
  -- Sandwich: the arithmetic mean is squeezed at `w`, so the budget binds.
  have ham_eq_w : ∑ l, β l * (p l * y l / β l) = w := by
    have hle : ∑ l, β l * (p l * y l / β l) ≤ w := by
      rw [sum_smul_substituted hβ]; exact hbud
    have hge : w ≤ ∑ l, β l * (p l * y l / β l) := by
      rw [← hgm_eq_w]
      exact Real.geom_mean_le_arith_mean_weighted Finset.univ β _ (fun l _ => (hβ l).le) hβ1
        (fun l _ => hz_nonneg l)
    linarith
  -- AM–GM equality characterization: substituted coordinates are constant at `w`.
  have hz_const := (Real.geom_mean_eq_arith_mean_weighted_iff' Finset.univ β _
    (fun l _ => hβ l) hβ1 (fun l _ => hz_nonneg l)).mp (by rw [hgm_eq_w, ham_eq_w])
  funext l
  have hzl : p l * y l / β l = w := by rw [hz_const l (Finset.mem_univ l), ham_eq_w]
  have hpy : p l * y l = w * β l := by
    field_simp [(hβ l).ne'] at hzl
    linarith
  field_simp [(hp l).ne']
  linarith

/-! ## The Cobb–Douglas factorization -/

/-- **Normalized-exponent factorization of `uTotal`.** For nonnegative `y`,
`uTotal y = (∏ l, (y l)^(β l))^A` with `A := ∑ α` and `β l := α l / A`. Off the positive orthant
both sides vanish (some factor has base `0` and positive exponent), so no interiority is needed. -/
private lemma uTotal_eq_prod_rpow (cd : CobbDouglasUtility L) (hL : 0 < L)
    {y : Fin L → ℝ} (hy : ∀ l, 0 ≤ y l) :
    cd.uTotal y = (∏ l, y l ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) := by
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  have hA_pos : 0 < ∑ i, cd.α i := Finset.sum_pos (fun i _ => cd.α_pos i) Finset.univ_nonempty
  calc cd.uTotal y = ∏ l, y l ^ cd.α l := by
        rw [cd.uTotal_def]
        exact Finset.prod_congr rfl fun l _ => by rw [max_eq_left (hy l)]
    _ = ∏ l, (y l ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← Real.rpow_mul (hy l), div_mul_cancel₀ _ hA_pos.ne']
    _ = (∏ l, y l ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) :=
        Real.finset_prod_rpow _ _ (fun l _ => Real.rpow_nonneg (hy l) _) _

end Econlib.Equilibrium

/-! ## Main statements -/

namespace Econlib.Preferences.CobbDouglasUtility

open Matrix Econlib.Equilibrium Econlib.Preferences

variable {L : ℕ}

/-- **Cobb–Douglas demand, budget-set form.** At strictly positive prices and wealth, the set of
preference-maximal bundles on the budget set is the singleton **expenditure-share bundle**
`l ↦ (α l / ∑ α) * w / p l`: The consumer spends the normalized weight of good `l` on good `l`. -/
theorem argmaxRel_budgetSetAt (cd : CobbDouglasUtility L) (hL : 0 < L)
    {p : Fin L → ℝ} {w : ℝ} (hp : ∀ l, 0 < p l) (hw : 0 < w) :
    Optimization.argmaxRel (preferenceOfRealUtility cd.uTotal) (budgetSetAt p w)
      = {fun l => (cd.α l / ∑ i, cd.α i) * w / p l} := by
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hL
  have hA_pos : 0 < ∑ i, cd.α i := Finset.sum_pos (fun i _ => cd.α_pos i) Finset.univ_nonempty
  have hβ_pos : ∀ l, 0 < cd.α l / ∑ i, cd.α i := fun l => div_pos (cd.α_pos l) hA_pos
  have hβ_sum : ∑ l, cd.α l / ∑ i, cd.α i = 1 := by
    rw [← Finset.sum_div, div_self hA_pos.ne']
  have hC_nonneg : 0 ≤ ∏ l, ((cd.α l / ∑ i, cd.α i) / p l) ^ (cd.α l / ∑ i, cd.α i) :=
    Finset.prod_nonneg fun l _ => Real.rpow_nonneg (div_nonneg (hβ_pos l).le (hp l).le) _
  -- The share bundle is affordable and exhausts the budget.
  have hxhat_nonneg : ∀ l, 0 ≤ (cd.α l / ∑ i, cd.α i) * w / p l :=
    fun l => (div_pos (mul_pos (hβ_pos l) hw) (hp l)).le
  have hxhat_dot : p ⬝ᵥ (fun l => (cd.α l / ∑ i, cd.α i) * w / p l) = w := by
    simp only [dotProduct]
    have hterm : ∀ l ∈ Finset.univ, p l * ((cd.α l / ∑ i, cd.α i) * w / p l)
        = cd.α l / (∑ i, cd.α i) * w := fun l _ => by
      field_simp [(hp l).ne']
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hβ_sum, one_mul]
  have hxhat_mem : (fun l => (cd.α l / ∑ i, cd.α i) * w / p l) ∈ budgetSetAt p w :=
    ⟨hxhat_nonneg, le_of_eq hxhat_dot⟩
  -- The share bundle's utility, in factored form.
  have hxhat_val : cd.uTotal (fun l => (cd.α l / ∑ i, cd.α i) * w / p l)
      = (w * ∏ l, ((cd.α l / ∑ i, cd.α i) / p l) ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) := by
    rw [uTotal_eq_prod_rpow cd hL hxhat_nonneg]
    congr 1
    exact prod_rpow_shareBundle hβ_pos hβ_sum hp hw
  -- Every budget-feasible bundle is weakly worse.
  have hle_xhat : ∀ y ∈ budgetSetAt p w,
      cd.uTotal y ≤ cd.uTotal (fun l => (cd.α l / ∑ i, cd.α i) * w / p l) := by
    intro y hy
    rw [uTotal_eq_prod_rpow cd hL hy.1, hxhat_val]
    refine Real.rpow_le_rpow (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (hy.1 l) _)
      ((prod_rpow_le_dotProduct_mul hβ_pos hβ_sum hp hy.1).trans ?_) hA_pos.le
    exact mul_le_mul_of_nonneg_right hy.2 hC_nonneg
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨hxhat_mem, fun y hy => hle_xhat y hy⟩, ?_⟩
  rintro y ⟨hy_mem, hy_max⟩
  -- An argmax bundle ties the share bundle in utility, hence equals it.
  have hval_eq : cd.uTotal y
      = (w * ∏ l, ((cd.α l / ∑ i, cd.α i) / p l) ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) := by
    rw [← hxhat_val]
    exact le_antisymm (hle_xhat y hy_mem) (hy_max _ hxhat_mem)
  have hpow_eq : (∏ l, y l ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i)
      = (w * ∏ l, ((cd.α l / ∑ i, cd.α i) / p l) ^ (cd.α l / ∑ i, cd.α i)) ^ (∑ i, cd.α i) := by
    rw [← uTotal_eq_prod_rpow cd hL hy_mem.1]
    exact hval_eq
  have hbase_eq : ∏ l, y l ^ (cd.α l / ∑ i, cd.α i)
      = w * ∏ l, ((cd.α l / ∑ i, cd.α i) / p l) ^ (cd.α l / ∑ i, cd.α i) :=
    Real.rpow_left_injOn hA_pos.ne'
      (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (hy_mem.1 l) _)
      (mul_nonneg hw.le hC_nonneg) hpow_eq
  exact eq_share_of_prod_rpow_eq hβ_pos hβ_sum hp hy_mem.1 hy_mem.2 hbase_eq

end Econlib.Preferences.CobbDouglasUtility

namespace Econlib.Equilibrium

open Matrix Econlib.Preferences

variable {L : ℕ}

/-- **Cobb–Douglas demand for an economy.** An agent with Cobb–Douglas preferences and strictly
positive wealth demands exactly the expenditure-share bundle at any strictly positive price. -/
theorem Economy.demand_eq_singleton_of_cobbDouglas (E : Economy L) (hL : 0 < L) (a : E.Agents)
    (cd : CobbDouglasUtility L) (hpref : E.pref a = preferenceOfRealUtility cd.uTotal)
    {p : Fin L → ℝ} (hp : ∀ l, 0 < p l) (hw : 0 < p ⬝ᵥ E.endow a) :
    E.demand p a = {fun l => (cd.α l / ∑ i, cd.α i) * (p ⬝ᵥ E.endow a) / p l} := by
  change Optimization.argmaxRel (E.pref a) (E.budgetSet p a) = _
  rw [hpref]
  exact cd.argmaxRel_budgetSetAt hL hp hw

end Econlib.Equilibrium

end
