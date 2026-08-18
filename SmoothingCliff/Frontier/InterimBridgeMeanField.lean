import SmoothingCliff.Frontier.PopulationProgram
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The finite-market upper bound through interim curves

This file formalizes part (i) of Theorem `thm:meanfield` in
`Smoothing_the_Cliff_ITCS.tex`: for every `n`, every slot count `K_n` and every
rule in the certified class `C^n_S`, per-capita welfare is bounded by the value
of the one-dimensional population program at per-capita mass
`W̄_n = w₁ K_n / n`.

The environment is the paper's: agents `ι` (a `Fintype` with at least one
element) draw values i.i.d. from a Borel law `F` on `ℝ`, so the profile law is
the product measure `profileLaw F = Measure.pi fun _ => F`.  A rule
`x : (ι → ℝ) → ι → ℝ` belongs to `CertifiedRule w₁ 𝒮 K` when each coordinate
`b ↦ x b i` is measurable, `x` takes values in `[0, w₁]`, each own coordinate
map `v ↦ x (b[i ↦ v]) i` is `𝒮`-Lipschitz uniformly in the opponents, and the
capacity constraint `∑ i, x b i ≤ w₁ K` holds pointwise.

Agent `i`'s **interim curve** integrates the opponents out,
`ξ i v = ∫ x (b[i ↦ v]) i db`, and the per-capita value is
`V_n(x) = n⁻¹ ∑ i ∫ v ξ i v dF`.  The results are

* `interimCurve_curveShape`: each interim curve is an admissible curve, i.e.
  it lands in `[0, w₁]` and is `𝒮`-Lipschitz (hence measurable);
* `averageInterimCurve_curveShape` and `averageInterimCurve_mass_le`: the
  average curve `ξ̄ = n⁻¹ ∑ i ξ i` is admissible and has ex-ante mass at most
  `W̄_n`, so it is feasible for the population program;
* `perCapitaValue_eq_curveWelfare`: `V_n(x) = ∫ v ξ̄ v dF`;
* `certifiedRule_le_populationValue` and
  `certifiedRule_le_postedRamp`: the resulting bound
  `V_n(x) ≤ V*(W̄_n)`, stated both against the supremum defining `V*` and,
  through `postedRamp_solves_population_program`, against the explicit ramp
  that attains it.

The bridge that makes the reduction exact is
`measurePreserving_updateSelf`: replacing coordinate `i` of an i.i.d. profile
by an independent `F`-draw reproduces the i.i.d. profile law.  It is proved
from `MeasureTheory.Measure.pi_eq` on measurable rectangles, and yields the
marginal identifications `curveMass_interimCurve` (`∫ ξ i dF = ∫ x b i db`) and
`interimCurve_value_integral` (`∫ v ξ i v dF = ∫ b i · x b i db`).  The latter
shows that the per-capita value defined through interim curves is the paper's
`n⁻¹ E[∑ i v_i x_i(v)]` (`perCapitaValue_eq_expectedWelfare`), so nothing is
assumed about the reduction that the paper performs.

Integrability of the value-weighted integrand comes from a finite first moment
of `F` (`Integrable id F`), which the paper's bounded value range `[r, b̄]`
implies; this matches the convention of
`SmoothingCliff.Frontier.PopulationProgram`.  Two further conventions are
inherited from that file.  Measurability is recorded coordinatewise
(`∀ i, Measurable fun b => x b i`), which on a finite agent set with the
discrete structure on `ι` is the paper's joint measurability.  The own-bid
Lipschitz bound is imposed on all of `ℝ` rather than on the eligible region
`[r, b̄]` alone, because the population program of
`SmoothingCliff.Frontier.PopulationProgram` is stated for globally defined
curves; the two agree on the support of `F`.
-/

open MeasureTheory

open scoped BigOperators

namespace SmoothingCliff.Frontier

variable {ι : Type*}

/-! ### The i.i.d. environment and the certified class -/

/-- The i.i.d. profile law: one independent `F`-draw per agent. -/
noncomputable def profileLaw [Fintype ι] (F : Measure ℝ) : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => F

instance instIsProbabilityMeasureProfileLaw [Fintype ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] : IsProbabilityMeasure (profileLaw (ι := ι) F) := by
  unfold profileLaw
  infer_instance

/-- The paper's certified class `C^n_S`: jointly measurable interim rules with
values in `[0, w₁]`, `𝒮`-Lipschitz in the own coordinate uniformly in the
opponents, and satisfying the capacity constraint `∑ i x i ≤ w₁ K` pointwise.
Neither anonymity nor monotonicity is imposed. -/
structure CertifiedRule [Fintype ι] [DecidableEq ι] (weight sensitivity : NNReal)
    (slots : ℝ) (x : (ι → ℝ) → ι → ℝ) : Prop where
  measurable : ∀ i, Measurable fun b => x b i
  nonneg : ∀ b i, 0 ≤ x b i
  le_weight : ∀ b i, x b i ≤ (weight : ℝ)
  ownLipschitz : ∀ (i : ι) (b : ι → ℝ),
    LipschitzWith sensitivity fun v => x (Function.update b i v) i
  capacity : ∀ b, ∑ i, x b i ≤ (weight : ℝ) * slots

/-- Agent `i`'s interim allocation curve: the opponents are integrated out
while the own coordinate is held at `v`. -/
noncomputable def interimCurve [Fintype ι] [DecidableEq ι] (F : Measure ℝ)
    (x : (ι → ℝ) → ι → ℝ) (i : ι) (v : ℝ) : ℝ :=
  ∫ b, x (Function.update b i v) i ∂profileLaw F

/-- The population average of the interim curves. -/
noncomputable def averageInterimCurve [Fintype ι] [DecidableEq ι] (F : Measure ℝ)
    (x : (ι → ℝ) → ι → ℝ) (v : ℝ) : ℝ :=
  (∑ i, interimCurve F x i v) / Fintype.card ι

/-- Per-capita expected welfare at truthful bids, written through the interim
curves. -/
noncomputable def perCapitaValue [Fintype ι] [DecidableEq ι] (F : Measure ℝ)
    (x : (ι → ℝ) → ι → ℝ) : ℝ :=
  (∑ i, ∫ v, v * interimCurve F x i v ∂F) / Fintype.card ι

/-! ### Shape of the interim curves -/

namespace CertifiedRule

variable [Fintype ι] [DecidableEq ι] {weight sensitivity : NNReal} {slots : ℝ}
  {x : (ι → ℝ) → ι → ℝ}

theorem measurable_section (hx : CertifiedRule weight sensitivity slots x)
    (i : ι) (v : ℝ) : Measurable fun b : ι → ℝ => x (Function.update b i v) i := by
  have hupd : Measurable fun b : ι → ℝ => Function.update b i v :=
    measurable_update_left
  exact (hx.measurable i).comp hupd

theorem integrable_coord (hx : CertifiedRule weight sensitivity slots x)
    (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι) :
    Integrable (fun b : ι → ℝ => x b i) (profileLaw F) := by
  refine (integrable_const (weight : ℝ)).mono'
    (hx.measurable i).aestronglyMeasurable ?_
  filter_upwards with b
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.nonneg b i)]
  exact hx.le_weight b i

theorem integrable_section (hx : CertifiedRule weight sensitivity slots x)
    (F : Measure ℝ) [IsProbabilityMeasure F] (i : ι) (v : ℝ) :
    Integrable (fun b : ι → ℝ => x (Function.update b i v) i) (profileLaw F) := by
  refine (integrable_const (weight : ℝ)).mono'
    (hx.measurable_section i v).aestronglyMeasurable ?_
  filter_upwards with b
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.nonneg _ i)]
  exact hx.le_weight _ i

end CertifiedRule

variable [Fintype ι] [DecidableEq ι]

theorem interimCurve_nonneg (F : Measure ℝ) {weight sensitivity : NNReal}
    {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) (v : ℝ) :
    0 ≤ interimCurve F x i v :=
  integral_nonneg fun _ => hx.nonneg _ i

theorem interimCurve_le_weight (F : Measure ℝ) [IsProbabilityMeasure F]
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) (v : ℝ) :
    interimCurve F x i v ≤ (weight : ℝ) := by
  have hmono := integral_mono (hx.integrable_section F i v)
    (integrable_const (weight : ℝ)) (fun _ => hx.le_weight _ i)
  simpa [interimCurve] using hmono

theorem interimCurve_lipschitz (F : Measure ℝ) [IsProbabilityMeasure F]
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) :
    LipschitzWith sensitivity (interimCurve F x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro v v'
  rw [Real.dist_eq, Real.dist_eq]
  have h1 := hx.integrable_section F i v
  have h2 := hx.integrable_section F i v'
  have hpoint : ∀ b : ι → ℝ,
      |x (Function.update b i v) i - x (Function.update b i v') i|
        ≤ (sensitivity : ℝ) * |v - v'| := by
    intro b
    simpa [Real.dist_eq] using (hx.ownLipschitz i b).dist_le_mul v v'
  calc |interimCurve F x i v - interimCurve F x i v'|
      = |∫ b, (x (Function.update b i v) i
            - x (Function.update b i v') i) ∂profileLaw F| := by
        rw [interimCurve, interimCurve, integral_sub h1 h2]
    _ ≤ ∫ b, |x (Function.update b i v) i
            - x (Function.update b i v') i| ∂profileLaw F :=
        abs_integral_le_integral_abs
    _ ≤ (sensitivity : ℝ) * |v - v'| := by
        have hmono := integral_mono (h1.sub h2).abs
          (integrable_const ((sensitivity : ℝ) * |v - v'|)) hpoint
        simpa using hmono

/-- Each interim curve is an admissible population curve. -/
theorem interimCurve_curveShape (F : Measure ℝ) [IsProbabilityMeasure F]
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) :
    CurveShape weight sensitivity (interimCurve F x i) :=
  { nonneg := interimCurve_nonneg F hx i
    le_weight := interimCurve_le_weight F hx i
    lipschitz := interimCurve_lipschitz F hx i }

/-! ### Shape of the average curve -/

theorem averageInterimCurve_nonneg [Nonempty ι] (F : Measure ℝ)
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (v : ℝ) :
    0 ≤ averageInterimCurve F x v := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => interimCurve_nonneg F hx i v) hn.le

theorem averageInterimCurve_le_weight [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {weight sensitivity : NNReal} {slots : ℝ}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x)
    (v : ℝ) : averageInterimCurve F x v ≤ (weight : ℝ) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [averageInterimCurve, div_le_iff₀ hn]
  calc (∑ i, interimCurve F x i v) ≤ ∑ _i : ι, (weight : ℝ) :=
        Finset.sum_le_sum fun i _ => interimCurve_le_weight F hx i v
    _ = (weight : ℝ) * Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem averageInterimCurve_lipschitz [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {weight sensitivity : NNReal} {slots : ℝ}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x) :
    LipschitzWith sensitivity (averageInterimCurve F x) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply LipschitzWith.of_dist_le_mul
  intro v v'
  rw [Real.dist_eq, Real.dist_eq]
  have hterm : ∀ i : ι, |interimCurve F x i v - interimCurve F x i v'|
      ≤ (sensitivity : ℝ) * |v - v'| := by
    intro i
    simpa [Real.dist_eq] using (interimCurve_lipschitz F hx i).dist_le_mul v v'
  have hsum : |∑ i, (interimCurve F x i v - interimCurve F x i v')|
      ≤ (Fintype.card ι : ℝ) * ((sensitivity : ℝ) * |v - v'|) := by
    calc |∑ i, (interimCurve F x i v - interimCurve F x i v')|
        ≤ ∑ i, |interimCurve F x i v - interimCurve F x i v'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, (sensitivity : ℝ) * |v - v'| :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card ι : ℝ) * ((sensitivity : ℝ) * |v - v'|) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [averageInterimCurve, averageInterimCurve, div_sub_div_same, abs_div,
    abs_of_pos hn, div_le_iff₀ hn]
  rw [mul_comm ((Fintype.card ι : ℝ)) ((sensitivity : ℝ) * |v - v'|)] at hsum
  simpa [Finset.sum_sub_distrib] using hsum

/-- The average interim curve is an admissible population curve. -/
theorem averageInterimCurve_curveShape [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {weight sensitivity : NNReal} {slots : ℝ}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x) :
    CurveShape weight sensitivity (averageInterimCurve F x) :=
  { nonneg := averageInterimCurve_nonneg F hx
    le_weight := averageInterimCurve_le_weight F hx
    lipschitz := averageInterimCurve_lipschitz F hx }

/-! ### The marginal bridge -/

/-- Replacing agent `i`'s coordinate in an i.i.d. profile by an independent
`F`-draw reproduces the i.i.d. profile law.  This is the marginal
identification behind the interim reduction. -/
theorem measurePreserving_updateSelf (F : Measure ℝ) [IsProbabilityMeasure F]
    (i : ι) :
    MeasurePreserving (fun p : ℝ × (ι → ℝ) => Function.update p.2 i p.1)
      (F.prod (profileLaw F)) (profileLaw F) := by
  have hmeas : Measurable (fun p : ℝ × (ι → ℝ) => Function.update p.2 i p.1) :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  refine ⟨hmeas, ?_⟩
  unfold profileLaw
  refine (Measure.pi_eq ?_).symm
  intro s hs
  have hpre : (fun p : ℝ × (ι → ℝ) => Function.update p.2 i p.1) ⁻¹'
      Set.pi Set.univ s
      = s i ×ˢ Set.pi Set.univ (Function.update s i (Set.univ : Set ℝ)) := by
    ext p
    constructor
    · intro hp
      have hp' : ∀ j, Function.update p.2 i p.1 j ∈ s j := by
        simpa [Set.mem_preimage, Set.mem_univ_pi] using hp
      refine ⟨?_, ?_⟩
      · simpa using hp' i
      · intro j _
        by_cases hj : j = i
        · subst hj; simp
        · simpa [Function.update_of_ne hj] using hp' j
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using h1
      · have := h2 j (Set.mem_univ j)
        rw [Function.update_of_ne hj] at this
        simpa [Function.update_of_ne hj] using this
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod,
    Measure.pi_pi]
  have hrest : ∀ j ∈ Finset.univ.erase i,
      F (Function.update s i (Set.univ : Set ℝ) j) = F (s j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hleft : (∏ j, F (Function.update s i (Set.univ : Set ℝ) j))
      = ∏ j ∈ Finset.univ.erase i, F (s j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => F (Function.update s i (Set.univ : Set ℝ) j)) (Finset.mem_univ i)]
    rw [Function.update_self, measure_univ, one_mul]
    exact Finset.prod_congr rfl hrest
  rw [hleft, Finset.mul_prod_erase Finset.univ (fun j => F (s j))
    (Finset.mem_univ i)]

/-- The ex-ante mass of an interim curve is the rule's expected allocation to
that agent. -/
theorem curveMass_interimCurve (F : Measure ℝ) [IsProbabilityMeasure F]
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) :
    curveMass F (interimCurve F x i) = ∫ b, x b i ∂profileLaw F := by
  have hT := measurePreserving_updateSelf (ι := ι) F i
  have hintegrable : Integrable
      (fun p : ℝ × (ι → ℝ) => x (Function.update p.2 i p.1) i)
      (F.prod (profileLaw F)) := by
    refine (integrable_const (weight : ℝ)).mono'
      ((hx.measurable i).comp hT.measurable).aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.nonneg _ i)]
    exact hx.le_weight _ i
  have hFubini := integral_integral
    (f := fun (v : ℝ) (b : ι → ℝ) => x (Function.update b i v) i) hintegrable
  have hmap : (∫ b, x b i ∂profileLaw F)
      = ∫ p, x (Function.update p.2 i p.1) i ∂(F.prod (profileLaw F)) := by
    conv_lhs => rw [← hT.map_eq]
    exact integral_map hT.measurable.aemeasurable
      (hx.measurable i).aestronglyMeasurable
  rw [curveMass, hmap]
  simpa [Function.uncurry] using hFubini

/-- The value-weighted interim integral is the rule's expected value-weighted
allocation to that agent. -/
theorem interimCurve_value_integral (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) (i : ι) :
    (∫ v, v * interimCurve F x i v ∂F) = ∫ b, b i * x b i ∂profileLaw F := by
  have hT := measurePreserving_updateSelf (ι := ι) F i
  have hmeasg : Measurable fun b : ι → ℝ => b i * x b i :=
    (measurable_pi_apply i).mul (hx.measurable i)
  have hbound : Integrable (fun p : ℝ × (ι → ℝ) => |p.1| * (weight : ℝ))
      (F.prod (profileLaw F)) :=
    (hFirstMoment.abs.mul_const (weight : ℝ)).comp_fst _
  have hintegrable : Integrable
      (fun p : ℝ × (ι → ℝ) => p.1 * x (Function.update p.2 i p.1) i)
      (F.prod (profileLaw F)) := by
    refine hbound.mono' ?_ ?_
    · exact (measurable_fst.mul ((hx.measurable i).comp
        hT.measurable)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul]
      have habs : |x (Function.update p.2 i p.1) i| ≤ (weight : ℝ) := by
        rw [abs_of_nonneg (hx.nonneg _ i)]
        exact hx.le_weight _ i
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg p.1)
  have hFubini := integral_integral
    (f := fun (v : ℝ) (b : ι → ℝ) => v * x (Function.update b i v) i) hintegrable
  have hpull : ∀ v : ℝ, v * interimCurve F x i v
      = ∫ b, v * x (Function.update b i v) i ∂profileLaw F := by
    intro v
    rw [interimCurve, integral_const_mul]
  have hmap : (∫ b, b i * x b i ∂profileLaw F)
      = ∫ p, p.1 * x (Function.update p.2 i p.1) i
          ∂(F.prod (profileLaw F)) := by
    conv_lhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable hmeasg.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with p
    simp
  rw [hmap]
  calc (∫ v, v * interimCurve F x i v ∂F)
      = ∫ v, (∫ b, v * x (Function.update b i v) i ∂profileLaw F) ∂F :=
        integral_congr_ae (Filter.Eventually.of_forall hpull)
    _ = ∫ p, p.1 * x (Function.update p.2 i p.1) i
          ∂(F.prod (profileLaw F)) := by
        simpa [Function.uncurry] using hFubini

/-! ### Feasibility of the average curve and the reduction -/

/-- Integrating the pointwise capacity constraint bounds the ex-ante mass of
the average interim curve by the per-capita priority mass `W̄_n = w₁ K / n`. -/
theorem averageInterimCurve_mass_le [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {weight sensitivity : NNReal} {slots : ℝ}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x) :
    curveMass F (averageInterimCurve F x)
      ≤ (weight : ℝ) * slots / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hint : ∀ i : ι, Integrable (interimCurve F x i) F := fun i =>
    (interimCurve_curveShape F hx i).integrable F
  have hmassSum : curveMass F (averageInterimCurve F x)
      = (∑ i, curveMass F (interimCurve F x i)) / Fintype.card ι := by
    unfold curveMass averageInterimCurve
    rw [integral_div, integral_finsetSum _ fun i _ => hint i]
  have hcoord : (∑ i, curveMass F (interimCurve F x i))
      = ∫ b, ∑ i, x b i ∂profileLaw F := by
    rw [integral_finsetSum _ fun i _ => hx.integrable_coord F i]
    exact Finset.sum_congr rfl fun i _ => curveMass_interimCurve F hx i
  have hcap : (∫ b, ∑ i, x b i ∂profileLaw F) ≤ (weight : ℝ) * slots := by
    have hmono := integral_mono
      (integrable_finsetSum _ fun i _ => hx.integrable_coord F i)
      (integrable_const ((weight : ℝ) * slots)) hx.capacity
    simpa using hmono
  rw [hmassSum, hcoord]
  exact div_le_div_of_nonneg_right hcap hn.le

/-- The average interim curve is feasible for the population program at
per-capita mass `W̄_n`. -/
theorem averageInterimCurve_curveFeasible [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {weight sensitivity : NNReal} {slots : ℝ}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x) :
    CurveFeasible F weight sensitivity ((weight : ℝ) * slots / Fintype.card ι)
      (averageInterimCurve F x) :=
  { toCurveShape := averageInterimCurve_curveShape F hx
    mass_le := averageInterimCurve_mass_le F hx }

/-- Per-capita value is the population value of the average interim curve. -/
theorem perCapitaValue_eq_curveWelfare [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) :
    perCapitaValue F x = curveWelfare F (averageInterimCurve F x) := by
  have hint : ∀ i : ι, Integrable (fun v => v * interimCurve F x i v) F :=
    fun i => (interimCurve_curveShape F hx i).integrable_value_mul F hFirstMoment
  unfold perCapitaValue curveWelfare averageInterimCurve
  rw [← integral_finsetSum _ fun i _ => hint i, ← integral_div]
  apply integral_congr_ae
  filter_upwards with v
  rw [← mul_div_assoc, Finset.mul_sum]

/-- The paper's primitive definition of per-capita welfare,
`n⁻¹ E[∑ i v_i x_i(v)]`, agrees with the interim-curve definition. -/
theorem perCapitaValue_eq_expectedWelfare [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) :
    perCapitaValue F x
      = (∫ b, ∑ i, b i * x b i ∂profileLaw F) / Fintype.card ι := by
  unfold perCapitaValue
  congr 1
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ =>
      interimCurve_value_integral F hFirstMoment hx i
  · intro i _
    have hbound : Integrable (fun b : ι → ℝ => |b i| * (weight : ℝ))
        (profileLaw F) := by
      have hcoord : Integrable (fun b : ι → ℝ => b i) (profileLaw F) := by
        unfold profileLaw
        exact ((measurePreserving_eval (fun _ : ι => F) i).integrable_comp
          hFirstMoment.aestronglyMeasurable).2 hFirstMoment
      exact hcoord.abs.mul_const _
    refine hbound.mono' (((measurable_pi_apply i).mul
      (hx.measurable i)).aestronglyMeasurable) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_mul]
    have hb : |x b i| ≤ (weight : ℝ) := by
      rw [abs_of_nonneg (hx.nonneg b i)]
      exact hx.le_weight b i
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-! ### Part (i) of Theorem `thm:meanfield` -/

/-- The value of the one-dimensional population program at per-capita mass
`massCap`. -/
noncomputable def populationValue (F : Measure ℝ) (weight sensitivity : NNReal)
    (massCap : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ ξ : ℝ → ℝ,
    CurveFeasible F weight sensitivity massCap ξ ∧ z = curveWelfare F ξ}

theorem populationValues_bddAbove (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (weight sensitivity : NNReal) (massCap : ℝ) :
    BddAbove {z : ℝ | ∃ ξ : ℝ → ℝ,
      CurveFeasible F weight sensitivity massCap ξ ∧ z = curveWelfare F ξ} := by
  refine ⟨(weight : ℝ) * ∫ v, |v| ∂F, ?_⟩
  rintro z ⟨ξ, hξ, rfl⟩
  have hmono := integral_mono (hξ.toCurveShape.integrable_value_mul F hFirstMoment)
    (hFirstMoment.abs.const_mul (weight : ℝ)) ?_
  · simpa [curveWelfare, integral_const_mul] using hmono
  · intro v
    calc v * ξ v ≤ |v * ξ v| := le_abs_self _
      _ = |v| * |ξ v| := abs_mul v (ξ v)
      _ ≤ |v| * (weight : ℝ) :=
        mul_le_mul_of_nonneg_left (hξ.toCurveShape.abs_le v) (abs_nonneg v)
      _ = (weight : ℝ) * |v| := mul_comm _ _

/-- **Part (i) of Theorem `thm:meanfield`.**  For every finite agent set, every
slot count and every rule in the certified class, per-capita welfare is at most
the value of the population program at per-capita priority mass
`W̄_n = w₁ K / n`. -/
theorem certifiedRule_le_populationValue [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {weight sensitivity : NNReal} {slots : ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : CertifiedRule weight sensitivity slots x) :
    perCapitaValue F x
      ≤ populationValue F weight sensitivity
          ((weight : ℝ) * slots / Fintype.card ι) := by
  rw [perCapitaValue_eq_curveWelfare F hFirstMoment hx]
  exact le_csSup
    (populationValues_bddAbove F hFirstMoment weight sensitivity _)
    ⟨averageInterimCurve F x, averageInterimCurve_curveFeasible F hx, rfl⟩

/-- Part (i) against the explicit optimizer: composing the interim reduction
with `postedRamp_solves_population_program` bounds per-capita welfare of every
certified rule by the value of the calibrated posted ramp. -/
theorem certifiedRule_le_postedRamp [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (weight sensitivity : NNReal)
    (hSensitivity : 0 < sensitivity) (slots threshold : ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F)
    (hThreshold : 0 ≤ threshold)
    (hRampMass : curveMass F (postedRamp weight sensitivity threshold)
      = min ((weight : ℝ) * slots / Fintype.card ι) (weight : ℝ))
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule weight sensitivity slots x) :
    perCapitaValue F x
      ≤ curveWelfare F (postedRamp weight sensitivity threshold) := by
  rw [perCapitaValue_eq_curveWelfare F hFirstMoment hx]
  exact postedRamp_solves_population_program F weight sensitivity hSensitivity
    ((weight : ℝ) * slots / Fintype.card ι) threshold hFirstMoment hThreshold
    hRampMass (averageInterimCurve_curveFeasible F hx)

/-! ### The hypotheses are jointly satisfiable -/

/-- A witness that `certifiedRule_le_postedRamp` is not vacuous: one agent, the
Dirac law at `1`, unit weight and sensitivity, half a slot, threshold `1/2` and
the zero rule satisfy every hypothesis at once. -/
example : perCapitaValue (ι := Fin 1) (Measure.dirac (1 : ℝ)) (fun _ _ => 0)
    ≤ curveWelfare (Measure.dirac (1 : ℝ)) (postedRamp 1 1 (1 / 2)) := by
  refine certifiedRule_le_postedRamp (ι := Fin 1) (Measure.dirac (1 : ℝ)) 1 1
    (by norm_num) (1 / 2) (1 / 2) (integrable_dirac (by simp)) (by norm_num)
    ?_ ?_
  · unfold curveMass
    rw [integral_dirac, postedRamp, clampWeight_eq_of_mem] <;> norm_num
  · exact
      { measurable := fun _ => measurable_const
        nonneg := fun _ _ => le_refl 0
        le_weight := fun _ _ => by norm_num
        ownLipschitz := fun _ _ =>
          (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)
        capacity := fun _ => by norm_num }

end SmoothingCliff.Frontier
