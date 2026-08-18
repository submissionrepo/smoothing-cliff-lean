/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A firm-connected two-agent production economy

The regression guard for **production irreducibility** (`IrreducibleProd`). Two agents are each
endowed with one unit of **labor** (good `0`) and nothing else, and both have Cobb–Douglas tastes
over labor and **output** (good `1`). They jointly own a single constant-returns firm that converts
labor into output (the Robinson Crusoe labor cone). With boundary endowments and Cobb–Douglas
preferences the pure-exchange economy is **disconnected**: Neither agent can reach a
positive-output bundle by trade alone, since no output exists in anyone's endowment. We prove

* `firmConnected_not_irreducible` — the exchange `Irreducible` predicate **fails** here, and
* `firmConnected_irreducibleProd` — the firm-aware `IrreducibleProd` predicate **holds**,

so the firm does real work: It is the channel through which one agent's labor becomes a good the
other wants. This is exactly the multi-agent connectedness that `Irreducible E.toEconomy` cannot
express, and the witness that `IrreducibleProd` is non-vestigial.

Because the predicate holds, the **general existence theorem** `exists_equilibrium_prod` —
re-proved on `IrreducibleProd` — delivers a Walrasian equilibrium for an economy the
consumption-only theorem cannot reach (`firmConnected_equilibrium_exists`).

## The model

* Goods: `0` = labor (an input), `1` = output. `Agents = Fin 2`, `Firms = Unit`.
* Endowment `(1, 0)` for both agents; each owns half the firm (`share = 1/2`, summing to one).
* Technology `Y = {y | y₀ ≤ 0 ∧ y₁ + y₀ ≤ 0}`: The labor cone (irreversible via the `y₀ ≤ 0` cut).
* Preferences `u x = x₀^{1/2} x₁^{1/2}` (symmetric Cobb–Douglas; `0` on the orthant boundary).

## Tags

walrasian equilibrium, production economy, irreducibility, cobb-douglas, arrow-debreu
-/

noncomputable section

namespace EconlibExamples.Equilibrium.FirmConnected

open Econlib.Equilibrium Econlib.Preferences Matrix

/-! ## The technology and the economy -/

/-- The labor-only activity cone: Labor (good `0`) is an input, output (good `1`) is bounded by the
labor used. This is the upstream `laborConeTech` (the same cone as Robinson Crusoe's firm). -/
abbrev laborTech : Technology 2 := laborConeTech

/-- Symmetric Cobb–Douglas tastes: Equal weights `1/2` on labor and output. -/
def fcU : CobbDouglasUtility 2 := ⟨![1/2, 1/2], by intro i; fin_cases i <;> norm_num⟩

/-- The firm-connected two-agent production economy. Both agents hold one unit of labor and share
the single firm equally. -/
def firmConnected : ProductionEconomy 2 where
  Agents := Fin 2
  pref := fun _ => preferenceOfRealUtility fcU.uTotal
  endow := fun _ => ![1, 0]
  endow_mem := fun _ l => by fin_cases l <;> simp
  Firms := Unit
  tech := fun _ => laborTech
  share := fun _ _ => 1 / 2
  share_nonneg := fun _ _ => by norm_num
  share_sum := fun _ => by simp

/-! ## The technology is regular -/

/-- The labor cone satisfies every `RegularTechnology` field. This is the upstream
`laborConeTech_regular` (the same cone, and proof, as Robinson Crusoe's firm). -/
theorem laborTech_regular : RegularTechnology laborTech := laborConeTech_regular

/-- The labor cone is closed under addition (the two half-space inequalities add). Used to feasibly
*increment* the current production by the labor ray `(-1, 1)`. This is the upstream
`laborConeTech_add_mem`. -/
theorem laborTech_add_mem {a b : Fin 2 → ℝ} (ha : a ∈ laborTech.Y) (hb : b ∈ laborTech.Y) :
    a + b ∈ laborTech.Y := laborConeTech_add_mem ha hb

/-- The labor ray `(-1, 1)` lies in the cone. This is the upstream `laborConeRay_mem`. -/
theorem laborRay_mem : (![-1, 1] : Fin 2 → ℝ) ∈ laborTech.Y := laborConeRay_mem

/-! ## Consumption-side regularity -/

/-- The consumption side is regular: Cobb–Douglas preferences with a nonzero endowment. The
endowment `(1,0)` is not strictly positive (output is produced-only), so we assemble the
`RegularEconomy` bundle by hand from the Cobb–Douglas lemmas rather than via
`RegularEconomy.ofCobbDouglas` (which demands strictly positive endowments — and would re-make the
economy exchange-irreducible). -/
theorem firmConnected_regular_econ : RegularEconomy firmConnected.toEconomy where
  contPref := fun _ => continuousPref_preferenceOfRealUtility fcU.uTotal_continuous
  convex := fun _ => fcU.uTotal_quasiconcave.toConvexPreference
  mono := fun _ => fcU.uTotal_strictMonoToInterior
  desirable := fun _ => fcU.uTotal_boundaryAvoiding.toDesirable fcU.uTotal_strictMonoToInterior
  endow_ne := fun _ hzero => by
    have h := congr_fun hzero 0
    simp [firmConnected] at h

/-- The single firm admits no aggregate recession (with one firm this is just the plan's
nonnegativity, killed by `no_free_lunch`; identical to the Crusoe argument). -/
theorem firmConnected_no_aggregate_recession : ∀ d : firmConnected.Firms → Fin 2 → ℝ,
    (∀ j, ∀ t : ℝ, 0 ≤ t → t • d j ∈ (firmConnected.tech j).Y) →
      (∀ l, 0 ≤ ∑ j, d j l) → ∀ j, d j = 0 := by
  haveI : Unique firmConnected.Firms := inferInstanceAs (Unique Unit)
  intro d hray hagg j
  have hmem : d default ∈ laborTech.Y := by simpa using hray default 1 zero_le_one
  have hnn : ∀ l, 0 ≤ d default l := fun l => by
    have h := hagg l; rwa [Fintype.sum_unique] at h
  have hzero : d default = 0 := laborTech_regular.no_free_lunch _ hmem hnn
  rw [Unique.eq_default j]; exact hzero

/-- The full Arrow–Debreu regularity bundle for the firm-connected economy. -/
theorem firmConnected_regular_prod : RegularProductionEconomy firmConnected where
  toRegularEconomy := firmConnected_regular_econ
  techReg := fun _ => laborTech_regular
  no_aggregate_recession := firmConnected_no_aggregate_recession

/-! ## The exchange economy is not irreducible -/

/-- **Exchange irreducibility fails.** At the allocation where each agent consumes its labor
endowment `(1,0)`, split agent `0` (the improving coalition) from agent `1` (the donor): The
donor's endowment is pure labor, so the resource bound forces any improvement to have **zero
output**. But a Cobb–Douglas bundle with zero output has utility `0`, the same as the labor bundle
— no strict improvement is possible by trade alone. This is the disconnection the firm repairs. -/
theorem firmConnected_not_irreducible : ¬ Irreducible firmConnected.toEconomy := by
  intro h
  haveI : DecidableEq firmConnected.toEconomy.Agents := inferInstanceAs (DecidableEq (Fin 2))
  -- Agent `0` is the improving coalition; agent `1` the (labor-only) donor.
  set xbad : Fin 2 → (Fin 2 → ℝ) := fun _ => ![1, 0] with hxbad
  have hxbad_nn : ∀ i l, 0 ≤ xbad i l := fun i l => by fin_cases l <;> simp [hxbad]
  have hIR : ∀ i, xbad i ≽[firmConnected.pref i] firmConnected.endow i := fun i =>
    le_refl _
  have hne : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  obtain ⟨y', ⟨hy'0_nn, hy'0_pref⟩, hy'_res⟩ :=
    h.improve_singletons xbad hxbad_nn hIR (0 : Fin 2) (1 : Fin 2) hne
  -- Agent `0` ∈ S strictly improves, yet the resource bound at good `1` forces `y' 0 1 = 0`.
  have hres1 := hy'_res 1
  have hendow1 : firmConnected.toEconomy.endow (1 : Fin 2) 1 = 0 := by simp [firmConnected]
  have hxbad1 : xbad (0 : Fin 2) 1 = 0 := by simp [hxbad]
  have hy'0_1_zero : y' (0 : Fin 2) 1 = 0 :=
    le_antisymm (by rw [hxbad1, hendow1] at hres1; linarith) (hy'0_nn 1)
  have huy' : fcU.uTotal (y' (0 : Fin 2)) = 0 :=
    fcU.uTotal_eq_zero_of_nonpos (i := 1) (le_of_eq hy'0_1_zero)
  have hux : fcU.uTotal (xbad (0 : Fin 2)) = 0 :=
    fcU.uTotal_eq_zero_of_nonpos (i := 1) (le_of_eq hxbad1)
  -- `y' 0 ≻ xbad 0` means `uTotal (xbad 0) < uTotal (y' 0)`, i.e. `0 < 0`.
  rw [show firmConnected.pref (0 : Fin 2) = preferenceOfRealUtility fcU.uTotal from rfl,
    preferenceOfUtilityIn_lt_iff] at hy'0_pref
  rw [huy', hux] at hy'0_pref
  exact lt_irrefl 0 hy'0_pref

/-! ## Production irreducibility holds -/

/-- **Production irreducibility holds.** For any individually-rational consumption `x` and any
feasible current plan `y`, the improving coalition `S` is handed the consumption `x · + (1/2, 1/2)`
and the firm deviation `y + (-1, 1)` (feasible, since the cone is closed under the labor ray). With
two agents `S` and `T` are singletons, and the increment `(1/2)·(-1, 1)` plus the donor's labor
exactly affords the interior bump `(1/2, 1/2)` — strictly Cobb–Douglas-better. -/
theorem firmConnected_irreducibleProd : IrreducibleProd firmConnected := by
  -- `_hIR` is the predicate's individual-rationality hypothesis; this witness improves over any
  -- nonnegative `x`, so it is unused here.
  refine ⟨fun x y hx_nn _hIR hy_mem S T hS hT hdisj => ?_⟩
  classical
  -- Improving consumption and deviating production.
  refine ⟨fun i l => x i l + 1 / 2, fun f => y f + (![-1, 1] : Fin 2 → ℝ), ?_, ?_, ?_⟩
  · -- the deviation `y f + (-1,1)` is feasible
    exact fun f => laborTech_add_mem (hy_mem f) laborRay_mem
  · -- every member of `S` is interior and strictly better off
    intro i _hi
    refine ⟨fun l => by have := hx_nn i l; linarith, ?_⟩
    have hle : x i ≤ fun l => x i l + 1 / 2 := fun l => by simp
    have hne : x i ≠ fun l => x i l + 1 / 2 := fun heq => by
      have := congr_fun heq 0; simp at this
    have hpos : ∀ l, 0 < (fun l => x i l + 1 / 2) l := fun l => by
      have := hx_nn i l; simp only; linarith
    exact fcU.uTotal_strictMonoToInterior.strictMono hle hne hpos
  · -- the resource inequality: in `Fin 2`, `S` and `T` are forced to be singletons
    have hcards : S.card = 1 ∧ T.card = 1 := by
      have hu : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hdisj
      have hcard_le_univ : (S ∪ T).card ≤ Fintype.card firmConnected.Agents := Finset.card_le_univ _
      have hcard_agents : Fintype.card firmConnected.Agents = 2 := rfl
      have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
      have h2 : 1 ≤ T.card := Finset.card_pos.mpr hT
      omega
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hcards.1
    obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcards.2
    haveI : Unique firmConnected.Firms := inferInstanceAs (Unique Unit)
    -- Reduce the singleton/unique sums and the production increment, then split into the two goods
    -- (literal `0`, `1`) so the matrix entries evaluate. The donor's labor plus `S`'s share of the
    -- labor→output conversion exactly affords the interior bump `(1/2, 1/2)`.
    simp only [Finset.sum_singleton, Fintype.sum_unique, Pi.add_apply, add_sub_cancel_left]
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;>
      · simp only [firmConnected, Matrix.cons_val_zero, Matrix.cons_val_one]
        linarith

/-! ## Existence via the general theorem -/

/-- **The positive-wealth seed.** At any simplex price where the firm can produce, labor is valued
positively (`0 < p 0`): The only price zeroing it is `(0,1)`, where the free labor ray makes supply
empty. (Same free-input discharge as Robinson Crusoe.) -/
theorem firmConnected_endow_valued (p : Fin 2 → ℝ) (hp : p ∈ priceSimplex 2)
    (hsupp : ∀ j, ((firmConnected.tech j).supply p).Nonempty) :
    ∃ a, 0 < p ⬝ᵥ firmConnected.endow a := by
  haveI : Unique firmConnected.Firms := inferInstanceAs (Unique Unit)
  refine ⟨(0 : Fin 2), ?_⟩
  have hp_nn : ∀ l, 0 ≤ p l := fun l => hp.1 l
  have hval : p ⬝ᵥ firmConnected.endow (0 : Fin 2) = p 0 := by
    change (∑ i, p i * (![1, 0] : Fin 2 → ℝ) i) = p 0
    rw [Fin.sum_univ_two]; simp
  rw [hval]
  rcases (hp_nn 0).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hp0 : p 0 = 0 := hzero.symm
    have hp1 : p 1 = 1 := by
      have hs := hp.2
      rw [Fin.sum_univ_two, hp0] at hs; linarith
    have hray : ∀ t : ℝ, 0 ≤ t → t • (![-1, 1] : Fin 2 → ℝ) ∈ laborTech.Y :=
      fun _ ht => laborConeRay_smul_mem ht
    have hposd : 0 < p ⬝ᵥ (![-1, 1] : Fin 2 → ℝ) := by
      have hd : p ⬝ᵥ (![-1, 1] : Fin 2 → ℝ) = -p 0 + p 1 := by
        change (∑ i, p i * (![-1, 1] : Fin 2 → ℝ) i) = -p 0 + p 1
        rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      rw [hd, hp0, hp1]; norm_num
    have hempty : laborTech.supply p = ∅ := laborTech.supply_eq_empty_of_free_input hray hposd
    obtain ⟨z, hz⟩ := hsupp default
    rw [show (firmConnected.tech default).supply p = laborTech.supply p from rfl, hempty] at hz
    exact Set.notMem_empty z hz

/-- **Existence of a Walrasian equilibrium with production** for the firm-connected economy, via
the general `exists_equilibrium_prod` re-proved on `IrreducibleProd`. The exchange `Irreducible`
predicate fails here (`firmConnected_not_irreducible`), so this equilibrium is beyond the
reach of the consumption-only existence theorem. -/
theorem firmConnected_equilibrium_exists :
    Nonempty (WalrasianEquilibriumWithProduction firmConnected) :=
  firmConnected.exists_equilibrium_prod (inferInstanceAs (Nonempty (Fin 2)))
    firmConnected_regular_prod firmConnected_irreducibleProd (by norm_num)
    firmConnected_endow_valued

end EconlibExamples.Equilibrium.FirmConnected

end
