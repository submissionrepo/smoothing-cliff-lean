/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `ProbDist` Non-Vacuity Checks

Compile-time semantic witnesses for the measure-backed base carrier `Econlib.Probability.ProbDist`
(and the abstract `ProbLaw` spine). `ProbDist` is the type every other distribution bridges into,
so these double as integration tests for the bridges.

The witnesses are anchored on Dirac laws on `ℝ` (`dirac 3`, and the product `dirac 1 ⊗ dirac 2`),
where every integral and conditional collapses to a point and can be checked against an
independently-computed value. The disintegration witnesses check both *fst/snd orientations*: The
conditional of the second coordinate given the first recovers the second-coordinate law (`dirac 2`,
not `dirac 1`), and — mirror-image — the conditional of the first given the second recovers
`dirac 1`, not `dirac 2`.

Beyond the point-mass core, this file exercises:

* the **coupling** API (`exists_coupling`, the canonical product coupling, and the product-support
  concentration lemmas `IsCoupling.supportsOn_prod_set` / `_Icc_prod`);
* the **weak-topology / Prokhorov** path (`isTight_of_supportsOn_Icc_prod` and
  `exists_weak_limit_of_supportsOn_Icc_prod` on a box-supported sequence);
* the **Feller-kernel** machinery (`IsFellerKernel.boundedContinuousFunction_integral_kernel` and
  `ProbabilityMeasure.injective_toIntegralFunctional`) on the deterministic Dirac kernel `a ↦ δ_a`,
  whose Feller property is the genuinely non-trivial `continuous_diracProba` (a constant kernel
  would make the property vacuous);
* the **subtype restriction** bridge (`toSubtype_toMeasure`); and
* the **`SupportedProbDist`** bridges (`toProbDist_eq`, `expect_eq`, `widen_law`,
  `expect_id_mem_Icc`, `dirac`).
-/

noncomputable section

namespace EconlibTest.Probability.ProbDist

open Econlib.Probability MeasureTheory ProbabilityTheory Set

section expectation

/-- **Dirac expectation is evaluation.** `E_{δ₃}[id] = 3`. -/
theorem dirac_expect : (ProbDist.dirac (3 : ℝ)).expect id = 3 := by
  simp [ProbDist.expect_dirac]

/-- **Nonnegative integrand ⇒ nonnegative expectation** (the `ProbDist` form). -/
theorem dirac_expect_nonneg : 0 ≤ (ProbDist.dirac (3 : ℝ)).expect (fun x => x ^ 2) :=
  ProbDist.expect_nonneg _ _ (fun x => sq_nonneg x)

/-- **Pushforward change of variables.** Mapping `δ₃` through `x ↦ 2x` and integrating `id` gives
`2·3 = 6`. -/
theorem dirac_map_expect :
    (ProbDist.map (ProbDist.dirac (3 : ℝ)) (fun x => 2 * x)
      (measurable_id.const_mul 2)).expect id = 6 := by
  rw [ProbDist.expect_map _ _ _ _ measurable_id.aestronglyMeasurable]
  simp only [id_eq, ProbDist.expect_dirac]
  norm_num

/-- `toMeasure` of a Dirac law is the Dirac measure. -/
theorem dirac_toMeasure_witness :
    (ProbDist.dirac (3 : ℝ)).toMeasure = Measure.dirac 3 := ProbDist.dirac_toMeasure 3

end expectation

section support

/-- **`supportsOn univ` is available** (API smoke test). This is tautological for every probability
law — `univ` carries full mass — so it is an availability check, not a semantic support guard; the
real support content is in `dirac_supportsOn_Icc` below (a *proper* set containing the atom). -/
theorem dirac_supportsOn_univ : (ProbDist.dirac (3 : ℝ)).supportsOn univ :=
  ProbDist.supportsOn_univ _

/-- **Dirac support.** `δ₃` is supported on any measurable set containing `3`, e.g. `[2,4]`. -/
theorem dirac_supportsOn_Icc : (ProbDist.dirac (3 : ℝ)).supportsOn (Icc 2 4) :=
  ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num)

/-- **Mean stays in the support hull.** A law supported on `[2,4]` has its mean in `[2,4]` — here
`E[id] = 3 ∈ [2,4]`. Catches a vacuous support claim. -/
theorem dirac_expect_mem_Icc : (ProbDist.dirac (3 : ℝ)).expect id ∈ Icc 2 4 :=
  ProbDist.expect_mem_Icc dirac_supportsOn_Icc

/-- **Integrability from bounded support.** `id` is integrable against a law on `[2,4]`. -/
theorem dirac_integrable_id : Integrable id (ProbDist.dirac (3 : ℝ)).toMeasure :=
  ProbDist.integrable_id_of_supportsOn_Icc dirac_supportsOn_Icc

end support

section mixture

/-- An **asymmetric** `1/4`-`3/4` mixture of `δ₁` and `δ₅`. Both the weights (`1/4 ≠ 3/4`) and the
atoms (`1 ≠ 5`) are asymmetric, so a component-order transpose or weight-atom misalignment moves the
mean — unlike a `50/50`-on-`{1,3}` mixture, where the swap is invisible. -/
private abbrev mix : ProbDist ℝ :=
  ProbDist.finMixture (finDist% ![1 / 4, 3 / 4]) ![ProbDist.dirac 1, ProbDist.dirac 5]

/-- **Mixture expectation decomposes** into the weighted component means: `(1/4)·1 + (3/4)·5 = 4`. A
component/weight transpose would give `(3/4)·1 + (1/4)·5 = 2`, so this catches the misalignment. -/
theorem mix_expect : mix.expect id = 4 := by
  have hint : ∀ i, Integrable id
      ((![ProbDist.dirac 1, ProbDist.dirac 5] : Fin 2 → ProbDist ℝ) i).toMeasure := by
    intro i
    fin_cases i
    · simpa using ProbDist.integrable_id_of_supportsOn_Icc
        (ProbDist.supportsOn_dirac (x := (1 : ℝ)) measurableSet_Icc
          (show (1 : ℝ) ∈ Icc 0 2 by norm_num))
    · simpa using ProbDist.integrable_id_of_supportsOn_Icc
        (ProbDist.supportsOn_dirac (x := (5 : ℝ)) measurableSet_Icc
          (show (5 : ℝ) ∈ Icc 4 6 by norm_num))
  rw [ProbDist.expect_finMixture _ _ _ hint]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ProbDist.expect_dirac, FinDist.ofVec_pmf]
  norm_num

end mixture

section probLaw

/-- **Abstract-law expectation nonneg** (`ProbLaw.expect_nonneg`), exercised through the `ProbDist`
spine instance. -/
theorem probLaw_expect_nonneg :
    0 ≤ ProbLaw.expect (ProbDist.dirac (3 : ℝ)) (fun x => x ^ 2) :=
  ProbLaw.expect_nonneg _ _ (fun x => sq_nonneg x)

end probLaw

section borel

/-- **The Borel instance is genuinely available** on a compact carrier `ProbDist (Fin 2)` (the
`ProbabilityMeasure` Borel structure requires `[CompactSpace]`, so this exercises the instance on a
finite — hence compact — state space). -/
theorem borelSpace_probDist : BorelSpace (ProbDist (Fin 2)) := inferInstance

end borel

section disintegration

/-- A product law `δ₁ ⊗ δ₂` on `ℝ × ℝ`. -/
private abbrev piProd : ProbDist (ℝ × ℝ) := (ProbDist.dirac (1 : ℝ)).prod (ProbDist.dirac 2)

/-- **Disintegration identity:** `fst(π) ⊗ condFst(π) = π`. -/
theorem condFst_compProd_witness :
    piProd.toMeasure.fst.compProd piProd.toMeasure.condKernel = piProd.toMeasure :=
  ProbDist.condFst_compProd piProd

/-- **fst/snd orientation.** The conditional of the *second* coordinate given the first recovers
the second-coordinate law `δ₂` — not `δ₁`. A swap of the two coordinates in the disintegration
would return `δ₁` here. -/
theorem condFst_recovers_second :
    (ProbDist.condFst piProd 1).toMeasure = (ProbDist.dirac (2 : ℝ)).toMeasure := by
  have hfst : piProd.toMeasure.fst = (ProbDist.dirac (1 : ℝ)).toMeasure := by
    simp [piProd, ProbDist.prod_toMeasure, ProbDist.dirac_toMeasure, Measure.fst_prod]
  have hne : piProd.toMeasure.fst {(1 : ℝ)} ≠ 0 := by
    rw [hfst, ProbDist.dirac_toMeasure, Measure.dirac_apply_of_mem (mem_singleton _)]
    norm_num
  ext s hs
  rw [ProbDist.condFst_apply_of_ne_zero piProd hne s, hfst]
  simp [piProd, ProbDist.prod_toMeasure, ProbDist.dirac_toMeasure, Measure.prod_prod,
    mem_singleton_iff]

/-- **snd/fst orientation — the mirror of `condFst_recovers_second`.** The conditional of the
*first* coordinate given the second recovers the first-coordinate law `δ₁` — not `δ₂`. The
`condSnd` formula routes through `Measure.map Prod.swap`, so a sign/orientation bug there would
return `δ₂` here instead. This is exactly the mirror of the `condFst` witness above (which recovers
`δ₂`), so the two together pin both disintegration directions. -/
theorem condSnd_recovers_first :
    (ProbDist.condSnd piProd 2).toMeasure = (ProbDist.dirac (1 : ℝ)).toMeasure := by
  -- The swapped law `swap (δ₁ ⊗ δ₂)` has second marginal `δ₁` and first marginal `δ₂`.
  have hsnd : piProd.toMeasure.snd = (ProbDist.dirac (2 : ℝ)).toMeasure := by
    simp [piProd, ProbDist.prod_toMeasure, ProbDist.dirac_toMeasure, Measure.snd_prod]
  have hne : piProd.toMeasure.snd {(2 : ℝ)} ≠ 0 := by
    rw [hsnd, ProbDist.dirac_toMeasure, Measure.dirac_apply_of_mem (mem_singleton _)]
    norm_num
  ext s hs
  rw [ProbDist.condSnd_apply_of_ne_zero piProd hne s, hsnd]
  -- `map swap (δ₁ ⊗ δ₂) ({2} ×ˢ s) = (δ₁ ⊗ δ₂) (s ×ˢ {2})`, evaluated at the Diracs.
  rw [Measure.map_apply measurable_swap (measurableSet_singleton _ |>.prod hs)]
  simp [piProd, ProbDist.prod_toMeasure, ProbDist.dirac_toMeasure, Measure.prod_prod,
    Set.preimage_swap_prod, mem_singleton_iff]

end disintegration

section coupling

/-- The first law `δ₁`, supported on `[0,2]`. -/
private abbrev μcoup : ProbDist ℝ := ProbDist.dirac 1

/-- The second law `δ₃`, supported on `[2,4]` (and on `[0,4]`). -/
private abbrev νcoup : ProbDist ℝ := ProbDist.dirac 3

/-- **A coupling exists** for any two laws. We exhibit the witness explicitly via `exists_coupling`
on `δ₁`, `δ₃`. Catches a vacuous existence claim. -/
theorem coupling_exists : ∃ π : ProbDist (ℝ × ℝ), IsCoupling μcoup νcoup π :=
  exists_coupling μcoup νcoup

/-- The canonical product coupling `δ₁ ⊗ δ₃` is a coupling: Its marginals are `δ₁` and `δ₃`. -/
theorem prod_is_coupling : IsCoupling μcoup νcoup (μcoup.prod νcoup) :=
  ProbDist.prod_isCoupling μcoup νcoup

/-- **A coupling concentrates on the product of the marginal supports.** Since `δ₁` is supported on
`{1} ⊆ [0,2]` and `δ₃` on `{3} ⊆ [2,4]`, every coupling puts full mass on `[0,2] ×ˢ [2,4]`. A
coupling that leaked mass off the product support would fail this. -/
theorem coupling_supportsOn_prod_set :
    (μcoup.prod νcoup).toMeasure (Icc 0 2 ×ˢ Icc 2 4) = 1 :=
  (ProbDist.prod_isCoupling μcoup νcoup).supportsOn_prod_set
    measurableSet_Icc measurableSet_Icc
    (ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num))
    (ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num))

/-- **The common-interval form.** With both marginals supported on `[0,4]`, the coupling puts full
mass on the square `[0,4] ×ˢ [0,4]`. -/
theorem coupling_supportsOn_Icc_prod :
    (μcoup.prod νcoup).toMeasure (Icc 0 4 ×ˢ Icc 0 4) = 1 :=
  (ProbDist.prod_isCoupling μcoup νcoup).supportsOn_Icc_prod
    (ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num))
    (ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num))

end coupling

section weakTopology

/-- A constant sequence of point masses `δ₍₀,₀₎ : ProbabilityMeasure (ℝ × ℝ)`, every term supported
on the box `[-1,1] ×ˢ [-1,1]`. -/
private abbrev boxSeq : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun _ => diracProba (0, 0)

/-- Each term of the sequence puts full mass on the box `[-1,1] ×ˢ [-1,1]`. -/
private theorem boxSeq_supp (n : ℕ) :
    (boxSeq n).toMeasure (Icc (-1) 1 ×ˢ Icc (-1) 1) = 1 := by
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩
  simp only [boxSeq, diracProba_toMeasure_apply_of_mem hmem]

/-- **Tightness from a uniform box support.** A sequence of laws all concentrated on the same
compact box `[-1,1] ×ˢ [-1,1]` is a tight family. Catches a vacuous tightness claim (a tight family
of the empty set, or of all of `ℝ × ℝ`, would be uninformative). -/
theorem boxSeq_isTight :
    IsTightMeasureSet {ρ : Measure (ℝ × ℝ) | ∃ n : ℕ, (boxSeq n).toMeasure = ρ} :=
  isTight_of_supportsOn_Icc_prod (-1) 1 boxSeq boxSeq_supp

/-- **A weak limit exists** for a uniformly-box-supported sequence, and the limit still puts full
mass on the box. This is the Prokhorov/weak-compactness endpoint: Tightness ⇒ a weakly convergent
subsequence whose limit inherits the box support. -/
theorem boxSeq_exists_weak_limit :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (πInf : ProbabilityMeasure (ℝ × ℝ)),
      Filter.Tendsto (fun n => boxSeq (φ n)) Filter.atTop (nhds πInf) ∧
        πInf.toMeasure (Icc (-1) 1 ×ˢ Icc (-1) 1) = 1 :=
  exists_weak_limit_of_supportsOn_Icc_prod (-1) 1 boxSeq boxSeq_supp

end weakTopology

section stationary

open ProbabilityTheory

/-- The **Dirac (deterministic-identity) kernel** on `ℝ`: `a ↦ δ_a`. -/
private abbrev diracKernel : Kernel ℝ ℝ := Kernel.deterministic id measurable_id

/-- The Dirac kernel is a genuine **Feller kernel**: Its measure-valued map `a ↦ δ_a` is continuous
in the weak-* topology. This is *not* vacuous — unlike a constant kernel (whose map is a constant
function), continuity here is the nontrivial fact `MeasureTheory.continuous_diracProba`, which
genuinely uses the topology of `ℝ`. -/
instance diracKernel_isFeller : IsFellerKernel diracKernel := by
  refine ⟨?_⟩
  -- `a ↦ ⟨δ_a, _⟩` is exactly `diracProba`, which is continuous.
  have heq : (diracKernel).toProbabilityMeasure = fun a => diracProba a := by
    funext a
    apply Subtype.ext
    simp only [Kernel.toProbabilityMeasure, diracKernel, Kernel.deterministic_apply, id_eq,
      diracProba]
  rw [heq]
  exact continuous_diracProba

/-- **Integrating a BCF against the Feller kernel evaluates it pointwise.** For the Dirac kernel,
`∫ f d(δ_a) = f a`, so `boundedContinuousFunction_integral_kernel` returns `f` itself. This
exercises the Feller integral construction and confirms it computes the right value. -/
theorem diracKernel_integral_eval (f : BoundedContinuousFunction ℝ ℝ) (a : ℝ) :
    IsFellerKernel.boundedContinuousFunction_integral_kernel diracKernel f a = f a := by
  simp only [IsFellerKernel.boundedContinuousFunction_integral_kernel,
    BoundedContinuousFunction.coe_mk, diracKernel, Kernel.deterministic_apply, id_eq,
    integral_dirac]

/-- **The integral functional separates distinct laws.** `ProbabilityMeasure.toIntegralFunctional`
(`f ↦ ∫ f`) is injective, so the distinct point masses `δ₁` and `δ₂` have distinct functionals. We
exercise injectivity *contrapositively*: assuming the functionals agree forces `δ₁ = δ₂` via
`injective_toIntegralFunctional`, contradicting `1 ≠ 2`. (This checks the injectivity direction of
the embedding; it does not itself exhibit the separating bounded-continuous function — see
`diracKernel_integral_eval`, which shows `∫ f dδ_a = f a`, the mechanism by which any BCF with
`f 1 ≠ f 2` separates them.) -/
theorem diracProba_toIntegralFunctional_injective_witness :
    ProbabilityMeasure.toIntegralFunctional (diracProba (1 : ℝ)) ≠
      ProbabilityMeasure.toIntegralFunctional (diracProba (2 : ℝ)) := by
  intro hcontra
  -- Injectivity would force `δ₁ = δ₂`, contradicting `1 ≠ 2`.
  have hdirac_eq : diracProba (1 : ℝ) = diracProba 2 :=
    ProbabilityMeasure.injective_toIntegralFunctional hcontra
  have : (1 : ℝ) = 2 := injective_diracProba hdirac_eq
  norm_num at this

end stationary

section subtype

/-- **Restricting a Dirac to its support.** `δ₃` viewed on the subtype `↑(Icc 2 4)` has, as its
measure, the `comap` of `δ₃` along the inclusion. `toSubtype_toMeasure` is the bridge that makes
the restriction measure-correct; this checks it on a concrete law with mass `1` on `[2,4]`. -/
theorem dirac_toSubtype_toMeasure :
    ((ProbDist.dirac (3 : ℝ)).toSubtype measurableSet_Icc
        (by rw [ProbDist.dirac_toMeasure, Measure.dirac_apply_of_mem (show (3 : ℝ) ∈ Icc 2 4 by
          norm_num)])).toMeasure
      = Measure.comap Subtype.val (ProbDist.dirac (3 : ℝ)).toMeasure :=
  ProbDist.toSubtype_toMeasure _ _ _

end subtype

section supported

/-- A bundled law `δ₃` recorded as supported on `[2,4]`. -/
private abbrev sd : SupportedProbDist (Icc (2 : ℝ) 4) :=
  SupportedProbDist.dirac measurableSet_Icc (show (3 : ℝ) ∈ Icc 2 4 by norm_num)

/-- **The `ProbLaw` projection recovers the bundled law.** `toProbDist_eq` says the abstract
`ProbLaw.toProbDist` view of a `SupportedProbDist` is its underlying `.law`. -/
theorem sd_toProbDist_eq : ProbLaw.toProbDist sd = sd.law :=
  SupportedProbDist.toProbDist_eq sd

/-- **Bundled expectation agrees with the underlying-law expectation.**
`E_{sd}[id] = E_{δ₃}[id]`. -/
theorem sd_expect_eq : sd.expect id = sd.law.expect id :=
  SupportedProbDist.expect_eq sd id

/-- And it computes: The bundled mean of `δ₃` is `3`. -/
theorem sd_expect_id : sd.expect id = 3 := by
  rw [SupportedProbDist.expect_eq]
  simp [sd, SupportedProbDist.dirac, ProbDist.expect_dirac]

/-- **Widening the recorded support preserves the law.** Re-recording `sd` as supported on the
larger `[0,5]` leaves the underlying law `δ₃` unchanged. -/
theorem sd_widen_law :
    (sd.widen (show Icc (2 : ℝ) 4 ⊆ Icc 0 5 by
      intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).law = sd.law :=
  SupportedProbDist.widen_law _ sd

/-- **The bundled mean stays in the recorded interval** — no side hypothesis needed.
`E[id] = 3 ∈
[2,4]`. Catches a vacuous support record. -/
theorem sd_expect_id_mem_Icc : sd.expect id ∈ Icc (2 : ℝ) 4 :=
  SupportedProbDist.expect_id_mem_Icc sd

end supported

section support2

/-- **`ae_mem_of_supportsOn` round-trip — forward direction.** A law supported on `[2,4]` has
a.e.-mass there: The ae-filter of `δ₃` is concentrated on `[2,4]`. -/
theorem dirac_ae_mem_of_supportsOn :
    ∀ᵐ x ∂(ProbDist.dirac (3 : ℝ)).toMeasure, x ∈ Icc (2 : ℝ) 4 :=
  ProbDist.ae_mem_of_supportsOn measurableSet_Icc dirac_supportsOn_Icc

/-- **`supportsOn_of_ae_mem` — backward direction**, fed an *independently* proved a.e. fact. To
avoid round-tripping through the forward `ae_mem_of_supportsOn`, the a.e.-membership `∀ᵐ x ∂δ₃,
x ∈ [2,4]` is established directly from the Dirac measure: `δ₃` puts all mass on `3 ∈ [2,4]`, so
a.e. `x = 3 ∈ [2,4]`. Then `supportsOn_of_ae_mem` recovers the support claim — genuinely exercising
the backward bridge without leaning on its forward partner. -/
theorem dirac_supportsOn_of_ae_mem : (ProbDist.dirac (3 : ℝ)).supportsOn (Icc 2 4) := by
  apply ProbDist.supportsOn_of_ae_mem measurableSet_Icc
  -- Direct: a.e. against `δ₃`, `x = 3`, and `3 ∈ [2,4]`.
  rw [ProbDist.dirac_toMeasure]
  refine (MeasureTheory.ae_dirac_iff measurableSet_Icc).mpr ?_
  norm_num

/-- **`supportsOn_map` — pushforward support.** The law `δ₃` is supported on `[2,4]`. Shifting by
`+1` maps `[2,4]` into `[3,5]`; the image law `δ₄` is supported on `[3,5]`. A wrong image-set
convention in `supportsOn_map` would fail this. -/
theorem map_supportsOn_Icc35 :
    (ProbDist.map (ProbDist.dirac (3 : ℝ)) (· + 1)
      (measurable_id.add measurable_const)).supportsOn (Icc 3 5) := by
  apply ProbDist.supportsOn_map (measurable_id.add measurable_const) measurableSet_Icc
  -- Need: ∀ᵐ x ∂(δ₃), x + 1 ∈ [3,5]. Since δ₃ is a.e. in [2,4], x+1 ∈ [3,5].
  filter_upwards [dirac_ae_mem_of_supportsOn] with x hx
  simp only [id_eq, mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

/-- **`supportsOn_finMixture`.** Both `δ₁` and `δ₅` are supported on `[0,6]`; the `1/4`-`3/4`
mixture is therefore also supported on `[0,6]`. A union-support bug (requiring all mass on a
component support rather than the common superset) would break this. -/
theorem mix_supportsOn_Icc06 : mix.supportsOn (Icc 0 6) := by
  apply ProbDist.supportsOn_finMixture _ _ measurableSet_Icc
  intro i
  fin_cases i
  · exact ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num : (1 : ℝ) ∈ Icc 0 6)
  · exact ProbDist.supportsOn_dirac measurableSet_Icc (by norm_num : (5 : ℝ) ∈ Icc 0 6)

/-- **`integrable_of_supportsOn_Icc` on a non-`id` function.** `f = x^2` is continuous on `[2,4]`,
so it is integrable against `δ₃` (which has support `[2,4]`). The `id` case is already covered by
`dirac_integrable_id`; this witness exercises the general-`f` branch. -/
theorem dirac_integrable_sq :
    Integrable (fun x => x ^ 2) (ProbDist.dirac (3 : ℝ)).toMeasure :=
  ProbDist.integrable_of_supportsOn_Icc dirac_supportsOn_Icc
    (continuous_pow 2).continuousOn

end support2

section bind

/-- **`bind_toMeasure` identity, with the concrete pushed measure.** Bind `δ₁` through the constant
kernel `fun _ => δ₂`. The underlying measure of the result is `δ₂ = Measure.dirac 2`: binding the
unit mass at `1` through the constant kernel collapses to the kernel's value. The RHS is the
*explicit* `Measure.dirac 2`, not just the raw `Measure.bind` expression, so a wrong
`bind_toMeasure` reduction (returning the base measure `δ₁`) is caught. -/
theorem bind_toMeasure_witness :
    (ProbDist.bind (ProbDist.dirac (1 : ℝ)) (fun _ => ProbDist.dirac (2 : ℝ))
      measurable_const).toMeasure
      = (Measure.dirac 2 : Measure ℝ) := by
  rw [ProbDist.bind_toMeasure]
  simp only [ProbDist.dirac_toMeasure]
  rw [Measure.dirac_bind (by fun_prop)]

end bind

section disintegration2

/-- **`condFst_toMeasure` — the ProbDist wrapper reduces to `Measure.condKernel`.** The toMeasure
of `condFst piProd 1` is exactly `piProd.toMeasure.condKernel 1` — the underlying Mathlib
conditional kernel. Catches an extra layer of wrapping or a definition mismatch. -/
theorem condFst_toMeasure_witness :
    (ProbDist.condFst piProd (1 : ℝ)).toMeasure
      = piProd.toMeasure.condKernel 1 :=
  ProbDist.condFst_toMeasure piProd 1

/-- **`condFst_measurable` — measurability of the conditional kernel map.** The function
`a ↦ (condFst piProd a).toMeasure` is measurable. We record a non-trivial application:
Measurability holds for the product law `δ₁ ⊗ δ₂`, not only in the abstract. -/
theorem condFst_measurable_witness :
    Measurable (fun a : ℝ => (ProbDist.condFst piProd a).toMeasure) :=
  ProbDist.condFst_measurable piProd

/-- **`condSnd_toMeasure` — the ProbDist wrapper for the snd conditional reduces to
`(map swap π).condKernel`.** The toMeasure of `condSnd piProd 2` is the condKernel of the swapped
law `map Prod.swap piProd` evaluated at `2`. Catches a wrong swap direction or an unreduced
definition. -/
theorem condSnd_toMeasure_witness :
    (ProbDist.condSnd piProd (2 : ℝ)).toMeasure
      = (Measure.map Prod.swap piProd.toMeasure).condKernel 2 :=
  ProbDist.condSnd_toMeasure piProd 2

/-- **`condSnd_measurable` — measurability of the snd conditional kernel map.** -/
theorem condSnd_measurable_witness :
    Measurable (fun b : ℝ => (ProbDist.condSnd piProd b).toMeasure) :=
  ProbDist.condSnd_measurable piProd

/-- **`condSnd_compProd` — symmetric disintegration identity.**
`snd(π) ⊗ condKernel(swap π) = swap π`. For `piProd = δ₁ ⊗ δ₂`, the swapped law is `δ₂ ⊗ δ₁`, its
second marginal is `δ₁`, so the compProd reconstructs `δ₂ ⊗ δ₁`. A swap error would produce
`δ₁ ⊗ δ₂` here instead, which differs. Together with `condFst_compProd_witness` above, this pins
both disintegration orientations. -/
theorem condSnd_compProd_witness :
    piProd.toMeasure.snd.compProd
        (Measure.map Prod.swap piProd.toMeasure).condKernel
      = Measure.map Prod.swap piProd.toMeasure :=
  ProbDist.condSnd_compProd piProd

end disintegration2

section strictExpect

/-- **`expect_lt` — strict upper bound from mass concentration.** For `δ₃`, `f = id`, `c = 4`:
`id ≤ 4` a.e. because `δ₃` concentrates at `3 ∈ [2,4]`. The atom `{3}` carries measure `1 > 0`, and
`id 3 = 3 < 4`. Hence `E_{δ₃}[id] < 4`. Hand-check: `E[id] = 3 < 4`. A sign flip (returning `≥`
instead of `<`) would break this. -/
theorem dirac_expect_lt : (ProbDist.dirac (3 : ℝ)).expect id < 4 := by
  -- id ≤ 4 ae: δ₃ is supported on [2,4], so ae x ∈ [2,4], hence x ≤ 4.
  have hle : ∀ᵐ x ∂(ProbDist.dirac (3 : ℝ)).toMeasure, id x ≤ 4 := by
    filter_upwards [ProbDist.ae_mem_of_supportsOn measurableSet_Icc dirac_supportsOn_Icc] with x hx
    exact hx.2
  -- δ₃({3}) = 1 > 0.
  have hpos : 0 < (ProbDist.dirac (3 : ℝ)).toMeasure {(3 : ℝ)} := by
    rw [ProbDist.dirac_toMeasure, Measure.dirac_apply_of_mem (mem_singleton _)]; norm_num
  exact ProbDist.expect_lt _ _ _ hle dirac_integrable_id hpos
    (fun x hx => by simp only [mem_singleton_iff] at hx; simp only [id_eq]; linarith)

/-- **`lt_expect` — strict lower bound from mass concentration.** For `δ₃`, `f = id`, `c = 2`:
`2 ≤ id` a.e. because `δ₃` concentrates at `3 ∈ [2,4]` so `2 ≤ x` a.e. The atom `{3}` has positive
measure and `2 < id 3 = 3`. Hence `2 < E_{δ₃}[id]`. Hand-check: `2 < 3`. A direction flip
(returning `≤` instead of `<`) would break this. -/
theorem dirac_lt_expect : (2 : ℝ) < (ProbDist.dirac (3 : ℝ)).expect id := by
  -- 2 ≤ id ae: δ₃ is supported on [2,4], so ae x ∈ [2,4], hence 2 ≤ x.
  have hle : ∀ᵐ x ∂(ProbDist.dirac (3 : ℝ)).toMeasure, (2 : ℝ) ≤ id x := by
    filter_upwards [ProbDist.ae_mem_of_supportsOn measurableSet_Icc dirac_supportsOn_Icc] with x hx
    exact hx.1
  have hpos : 0 < (ProbDist.dirac (3 : ℝ)).toMeasure {(3 : ℝ)} := by
    rw [ProbDist.dirac_toMeasure, Measure.dirac_apply_of_mem (mem_singleton _)]; norm_num
  exact ProbDist.lt_expect _ _ _ hle dirac_integrable_id hpos
    (fun x hx => by simp only [mem_singleton_iff] at hx; simp only [id_eq]; linarith)

end strictExpect

section mapToMeasure

/-- **`map_toMeasure` — the underlying measure of a pushforward is the concrete `δ₄`.**
Mapping `δ₃` through `x ↦ x + 1` gives a `ProbDist` whose underlying measure is `Measure.dirac 4`
(since the atom `3` maps to `3 + 1 = 4`). The RHS is the *explicit* `Measure.dirac 4`, not just
the raw `Measure.map` expression, so a wrong unfolding of `ProbDist.map` or a shift error is
caught. -/
theorem map_toMeasure_witness :
    (ProbDist.map (ProbDist.dirac (3 : ℝ)) (· + 1)
      (measurable_id.add measurable_const)).toMeasure
      = (Measure.dirac 4 : Measure ℝ) := by
  rw [ProbDist.map_toMeasure, ProbDist.dirac_toMeasure, Measure.map_dirac' (by fun_prop)]
  norm_num

end mapToMeasure

section supportedIntegrable

/-- **`SupportedProbDist.integrable_of_continuousOn`.** The function `x^2` is continuous on
`[2,4]`, so it is integrable against the underlying law of the supported-Dirac `sd`. -/
theorem sd_integrable_sq :
    Integrable (fun x => x ^ 2) sd.law.toMeasure :=
  SupportedProbDist.integrable_of_continuousOn sd (continuous_pow 2).continuousOn

/-- **`SupportedProbDist.integrable_id`.** The identity is integrable against the law of `sd`, no
extra hypotheses needed. This is the bundled analog of `dirac_integrable_id`. -/
theorem sd_integrable_id : Integrable id sd.law.toMeasure :=
  SupportedProbDist.integrable_id sd

end supportedIntegrable

end EconlibTest.Probability.ProbDist

end
