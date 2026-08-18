/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.PiProdCongr
public import Econlib.Math.Probability.KernelPi

/-!
# Products of disintegrated measures

Interchange lemmas between finite products (`Measure.pi`, `Kernel.pi`) and disintegrations
(`Measure.compProd`), used to pass between the two presentations of the joint type–action law of a
distributional-strategy profile in Bayesian games:

* a product of Dirac measures is the Dirac measure of the point profile;
* a product of disintegrated measures `⊗ᵢ (μ i ⊗ₘ κ i)` is the disintegration of the products, up
  to the reindexing `(∀ i, X i × Y i) ≃ᵐ (∀ i, X i) × (∀ i, Y i)`;
* a density on the base of a disintegration can be moved across the disintegration:
  `(μ.withDensity ρ) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (ρ ∘ fst)`.

## Main statements

* `MeasureTheory.Measure.pi_dirac`: Products of Diracs.
* `MeasureTheory.Measure.pi_compProd`: Products of disintegrations.
* `MeasureTheory.Measure.withDensity_compProd_fst`: Base change by a density.

## Tags

product measure, disintegration, kernel, density
-/

@[expose] public section

open scoped ENNReal
open ProbabilityTheory

namespace MeasureTheory.Measure

/-- A finite product of Dirac measures is the Dirac measure at the point profile. -/
theorem pi_dirac {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (x : ∀ i, X i) :
    Measure.pi (fun i => Measure.dirac (x i)) = Measure.dirac x := by
  refine Measure.pi_eq (μ := fun i => Measure.dirac (x i)) (μ' := Measure.dirac x)
    fun s hs => ?_
  classical
  rw [dirac_apply' _ (MeasurableSet.univ_pi hs)]
  have hprod : ∀ i, (Measure.dirac (x i)) (s i) = Set.indicator (s i) 1 (x i) := fun i =>
    dirac_apply' _ (hs i)
  simp only [hprod]
  by_cases hx : x ∈ Set.pi Set.univ s
  · rw [Set.indicator_of_mem hx]
    have : ∀ i, Set.indicator (s i) (1 : X i → ℝ≥0∞) (x i) = 1 := fun i =>
      Set.indicator_of_mem (hx i (Set.mem_univ i)) 1
    simp [this]
  · rw [Set.indicator_of_notMem hx]
    have hnot : ¬∀ i, x i ∈ s i := fun h => hx (Set.mem_univ_pi.mpr h)
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    simp [Set.indicator_of_notMem hi]

/-- Tonelli for a finite product over `Fin n`: The integral of a product of one-coordinate
functions factorizes. The `ℝ≥0∞` analog of `integral_fin_nat_prod_eq_prod`. -/
private theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {ν : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (ν i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, f i x ∂(ν i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
              f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
              ∂((ν 0).prod (Measure.pi (fun i ↦ ν i.succ))) := by
            rw [← ((measurePreserving_piFinSuccAbove ν 0).symm).lintegral_comp_emb
              (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
            congr 1
            ext a
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂ν 0)
              * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(ν i.succ) := by
            rw [← n_ih (fun i => f (Fin.succ i)) (fun i => hf _), ← lintegral_prod_mul]
            · exact (hf 0).aemeasurable
            · exact (Finset.measurable_prod _ fun i _ =>
                (hf _).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(ν i) := by rw [Fin.prod_univ_succ]

/-- Tonelli for a finite product over an arbitrary `Fintype`: The integral of a product of
one-coordinate functions factorizes. The `ℝ≥0∞` analog of `integral_fintype_prod_eq_prod`. -/
private theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {ν : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, f i x ∂(ν i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf _)

variable {ι : Type*} [Fintype ι] {X Y : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]

/-- **Products of disintegrations.** The product of disintegrated probability measures
`⊗ᵢ (μ i ⊗ₘ κ i)` equals the disintegration of the product base by the product kernel, transported
along the reindexing `(∀ i, X i × Y i) ≃ᵐ (∀ i, X i) × (∀ i, Y i)`. -/
theorem pi_compProd (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    Measure.pi (fun i => (μ i) ⊗ₘ (κ i)) =
      ((Measure.pi μ) ⊗ₘ
          Kernel.pi (fun i => (κ i).comap (fun x => x i) (measurable_pi_apply i))).map
        (MeasurableEquiv.piProdEquivProdPi (X := X) (Y := Y)).symm := by
  classical
  haveI : ∀ i, IsProbabilityMeasure ((μ i) ⊗ₘ (κ i)) := fun i => inferInstance
  refine Measure.pi_eq fun s hs => ?_
  set f : (i : ι) → X i → ℝ≥0∞ := fun i t => κ i t (Prod.mk t ⁻¹' s i) with hf_def
  have hf_meas : ∀ i, Measurable (f i) := fun i =>
    Kernel.measurable_kernel_prodMk_left (hs i)
  have hLHS : ∀ i, ((μ i) ⊗ₘ (κ i)) (s i) = ∫⁻ t, f i t ∂(μ i) := fun i =>
    Measure.compProd_apply (hs i)
  set κπ : Kernel (∀ i, X i) (∀ i, Y i) :=
    Kernel.pi (fun i => (κ i).comap (fun x => x i) (measurable_pi_apply i)) with hκπ_def
  have hRHS : (((Measure.pi μ) ⊗ₘ κπ).map
      (MeasurableEquiv.piProdEquivProdPi (X := X) (Y := Y)).symm) (Set.pi Set.univ s)
      = ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) := by
    set T : Set ((∀ i, X i) × (∀ i, Y i)) :=
      (MeasurableEquiv.piProdEquivProdPi (X := X) (Y := Y)).symm ⁻¹' (Set.pi Set.univ s)
      with hT_def
    have hT_eq : T = {p | ∀ i, (p.1 i, p.2 i) ∈ s i} := by
      ext p
      simp only [hT_def, Set.mem_preimage, MeasurableEquiv.piProdEquivProdPi_symm_apply,
        Set.mem_univ_pi, Set.mem_setOf_eq]
    have hT_meas : MeasurableSet T := by
      rw [hT_eq, Set.setOf_forall]
      exact MeasurableSet.iInter fun i =>
        ((((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)) (hs i))
    rw [MeasurableEquiv.map_apply, ← hT_def, Measure.compProd_apply hT_meas]
    refine lintegral_congr fun x => ?_
    have hsection : (Prod.mk x ⁻¹' T) = Set.pi Set.univ (fun i => Prod.mk (x i) ⁻¹' s i) := by
      ext y
      simp only [Set.mem_preimage, hT_eq, Set.mem_setOf_eq, Set.mem_univ_pi]
    rw [hsection, Kernel.pi_apply, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Kernel.comap_apply']
  rw [hRHS, lintegral_fintype_prod_eq_prod f hf_meas]
  exact Finset.prod_congr rfl fun i _ => (hLHS i).symm

/-- **Base change by a density across a disintegration**: Weighting the base of a disintegration is
the same as weighting the disintegrated measure through the first coordinate. -/
theorem withDensity_compProd_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    {ρ : α → ℝ≥0∞} (hρ : Measurable ρ) :
    (μ.withDensity ρ) ⊗ₘ κ = ((μ ⊗ₘ κ).withDensity fun p => ρ p.1) := by
  refine Measure.ext fun s hs => ?_
  have hsec : Measurable fun a => κ a (Prod.mk a ⁻¹' s) :=
    Kernel.measurable_kernel_prodMk_left hs
  rw [Measure.compProd_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hρ hsec]
  have hindf : Measurable fun p : α × β => s.indicator (fun q => ρ q.1) p :=
    (hρ.comp measurable_fst).indicator hs
  rw [withDensity_apply _ hs,
    ← lintegral_indicator hs,
    Measure.lintegral_compProd hindf]
  refine lintegral_congr fun a => ?_
  have hinner : (fun b => (s.indicator (fun p => ρ p.1) (a, b)))
      = (Prod.mk a ⁻¹' s).indicator (fun _ => ρ a) := by
    funext b
    by_cases hb : (a, b) ∈ s
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (by simpa using hb)]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (by simpa using hb)]
  rw [hinner, lintegral_indicator (measurable_prodMk_left hs), setLIntegral_const]
  simp [Pi.mul_apply]

end MeasureTheory.Measure
