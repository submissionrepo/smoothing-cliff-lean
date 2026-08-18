import SmoothingCliff.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Translation-invariant sequential Luce intensities

This file formalizes Proposition `prop:axiomatization`.  Eligible bids are
written as `reserve + x`, where `x : NNReal`, so continuity, positivity, and
strict monotonicity are required only on the paper's eligible half-line.

The proof has two explicit reductions.  Translation invariance of Luce odds is
equivalent to a multiplicative cocycle.  Taking logs turns that cocycle into a
continuous additive map on `NNReal`; extending it to an additive map on `ℝ`
then identifies it with multiplication by a strictly positive constant.
-/

namespace SmoothingCliff.Mechanism

noncomputable section

/-- The intensity at an eligible bid, parametrized by its nonnegative distance
above the reserve. -/
def EligibleIntensity (reserve : ℝ) (alpha : ℝ → ℝ) (x : NNReal) : ℝ :=
  alpha (reserve + (x : ℝ))

/-- Common bid translations leave every pairwise Luce odds ratio unchanged. -/
def TranslationRatioInvariant (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∀ x y c : NNReal,
    EligibleIntensity reserve alpha (x + c) /
        EligibleIntensity reserve alpha (y + c) =
      EligibleIntensity reserve alpha x / EligibleIntensity reserve alpha y

/-- Product form of translation invariance, obtained by comparing an eligible
bid with the reserve itself. -/
def TranslationCocycle (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∀ x c : NNReal,
    EligibleIntensity reserve alpha (x + c) *
        EligibleIntensity reserve alpha 0 =
      EligibleIntensity reserve alpha x * EligibleIntensity reserve alpha c

/-- With positive intensities, invariance of all Luce odds is exactly the
multiplicative translation cocycle. -/
theorem ratio_iff_cocycle
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x) :
    TranslationRatioInvariant reserve alpha ↔
      TranslationCocycle reserve alpha := by
  constructor
  · intro h x c
    have hr := h x 0 c
    have hr' :
        EligibleIntensity reserve alpha (x + c) /
            EligibleIntensity reserve alpha c =
          EligibleIntensity reserve alpha x /
            EligibleIntensity reserve alpha 0 := by
      simpa using hr
    exact (div_eq_div_iff (ne_of_gt (hpos c))
      (ne_of_gt (hpos 0))).mp hr'
  · intro h x y c
    have hxc := h x c
    have hyc := h y c
    have h0 : EligibleIntensity reserve alpha 0 ≠ 0 := ne_of_gt (hpos 0)
    have ex :
        EligibleIntensity reserve alpha (x + c) =
          EligibleIntensity reserve alpha x *
            EligibleIntensity reserve alpha c /
              EligibleIntensity reserve alpha 0 :=
      (eq_div_iff h0).2 hxc
    have ey :
        EligibleIntensity reserve alpha (y + c) =
          EligibleIntensity reserve alpha y *
            EligibleIntensity reserve alpha c /
              EligibleIntensity reserve alpha 0 :=
      (eq_div_iff h0).2 hyc
    apply (div_eq_div_iff (ne_of_gt (hpos (y + c)))
      (ne_of_gt (hpos y))).2
    rw [ex, ey]
    ring

/-- Extend an additive map on the nonnegative reals to the whole real line by
subtracting its values on the positive and negative parts. -/
def positivePartExtension (f : NNReal →+ ℝ) (x : ℝ) : ℝ :=
  f x.toNNReal - f (-x).toNNReal

theorem positive_negative_parts_add (x y : ℝ) :
    (x + y).toNNReal + (-x).toNNReal + (-y).toNNReal =
      (-(x + y)).toNNReal + x.toNNReal + y.toNNReal := by
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal']
  have hx := posPart_sub_negPart x
  have hy := posPart_sub_negPart y
  have hxy := posPart_sub_negPart (x + y)
  change max x 0 - max (-x) 0 = x at hx
  change max y 0 - max (-y) 0 = y at hy
  change max (x + y) 0 - max (-(x + y)) 0 = x + y at hxy
  linarith

theorem positivePartExtension_add (f : NNReal →+ ℝ) (x y : ℝ) :
    positivePartExtension f (x + y) =
      positivePartExtension f x + positivePartExtension f y := by
  have h := congrArg f (positive_negative_parts_add x y)
  simp only [map_add] at h
  dsimp [positivePartExtension]
  linarith

def additiveExtension (f : NNReal →+ ℝ) : ℝ →+ ℝ where
  toFun := positivePartExtension f
  map_zero' := by simp [positivePartExtension]
  map_add' := positivePartExtension_add f

theorem additiveExtension_coe (f : NNReal →+ ℝ) (x : NNReal) :
    additiveExtension f (x : ℝ) = f x := by
  change f ((x : ℝ).toNNReal) - f (-(x : ℝ)).toNNReal = f x
  rw [Real.toNNReal_coe,
    Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg)]
  simp

/-- The continuous Cauchy theorem on the nonnegative half-line. -/
theorem continuous_nnreal_additive_linear
    (f : NNReal →+ ℝ) (hf : Continuous f) (x : NNReal) :
    f x = (x : ℝ) * f 1 := by
  have hto : Continuous Real.toNNReal :=
    ContinuousMap.continuous_toFun ContinuousMap.realToNNReal
  have hext : Continuous (additiveExtension f) := by
    exact (hf.comp hto).sub (hf.comp (hto.comp continuous_neg))
  have hmap := map_real_smul (additiveExtension f) hext (x : ℝ) (1 : ℝ)
  have hone : additiveExtension f (1 : ℝ) = f (1 : NNReal) := by
    simpa using additiveExtension_coe f (1 : NNReal)
  rw [hone] at hmap
  simpa [smul_eq_mul, additiveExtension_coe] using hmap

noncomputable def logIncrementHom
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcoc : TranslationCocycle reserve alpha) : NNReal →+ ℝ where
  toFun x :=
    Real.log (EligibleIntensity reserve alpha x) -
      Real.log (EligibleIntensity reserve alpha 0)
  map_zero' := by simp
  map_add' := by
    intro x y
    have h := congrArg Real.log (hcoc x y)
    rw [Real.log_mul (ne_of_gt (hpos (x + y))) (ne_of_gt (hpos 0)),
      Real.log_mul (ne_of_gt (hpos x)) (ne_of_gt (hpos y))] at h
    linarith

/-- A positive, continuous, strictly increasing solution of the translation
cocycle is exponential in distance above the reserve. -/
theorem normalized_exponential_of_cocycle
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcont : Continuous (EligibleIntensity reserve alpha))
    (hstrict : StrictMono (EligibleIntensity reserve alpha))
    (hcoc : TranslationCocycle reserve alpha) :
    ∃ slope : ℝ, 0 < slope ∧
      ∀ x : NNReal,
        EligibleIntensity reserve alpha x =
          EligibleIntensity reserve alpha 0 *
            Real.exp (slope * (x : ℝ)) := by
  let f := logIncrementHom hpos hcoc
  have hf : Continuous f := by
    exact (hcont.log fun x => ne_of_gt (hpos x)).sub continuous_const
  let slope := f 1
  have hslope : 0 < slope := by
    have ha := hstrict (show (0 : NNReal) < 1 by norm_num)
    have hl := Real.log_lt_log (hpos 0) ha
    change 0 < Real.log (EligibleIntensity reserve alpha 1) -
      Real.log (EligibleIntensity reserve alpha 0)
    linarith
  refine ⟨slope, hslope, ?_⟩
  intro x
  have hlin := continuous_nnreal_additive_linear f hf x
  have hlog :
      Real.log (EligibleIntensity reserve alpha x) =
        Real.log (EligibleIntensity reserve alpha 0) +
          slope * (x : ℝ) := by
    change Real.log (EligibleIntensity reserve alpha x) -
        Real.log (EligibleIntensity reserve alpha 0) =
      (x : ℝ) * slope at hlin
    linarith
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_add, Real.exp_log (hpos x),
    Real.exp_log (hpos 0)] at hexp
  exact hexp

/-- The paper's exponential conclusion on the eligible region.  The constant
`c0` is strictly positive and `tau` is a finite, strictly positive
temperature. -/
def ExponentialOnEligible (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∃ c0 tau : ℝ, 0 < c0 ∧ 0 < tau ∧
    ∀ x : NNReal,
      EligibleIntensity reserve alpha x =
        c0 * Real.exp ((reserve + (x : ℝ)) / tau)

theorem exponential_on_eligible_of_normalized
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    {slope : ℝ} (hslope : 0 < slope)
    (h : ∀ x : NNReal,
      EligibleIntensity reserve alpha x =
        EligibleIntensity reserve alpha 0 *
          Real.exp (slope * (x : ℝ))) :
    ExponentialOnEligible reserve alpha := by
  let c0 := EligibleIntensity reserve alpha 0 *
    Real.exp (-reserve * slope)
  let tau := 1 / slope
  have hc0 : 0 < c0 := by
    dsimp [c0]
    exact mul_pos (hpos 0) (Real.exp_pos _)
  have htau : 0 < tau := one_div_pos.mpr hslope
  refine ⟨c0, tau, hc0, htau, ?_⟩
  intro x
  rw [h x]
  have hexp :
      Real.exp (-reserve * slope) *
          Real.exp ((reserve + (x : ℝ)) / tau) =
        Real.exp (slope * (x : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [tau]
    field_simp [ne_of_gt hslope]
    ring
  dsimp [c0]
  rw [mul_assoc, hexp]

theorem ratio_invariant_of_exponential_on_eligible
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (h : ExponentialOnEligible reserve alpha) :
    TranslationRatioInvariant reserve alpha := by
  rcases h with ⟨c0, tau, hc0, htau, hform⟩
  intro x y c
  rw [hform (x + c), hform (y + c), hform x, hform y]
  have hxc :
      Real.exp ((reserve + ((x + c : NNReal) : ℝ)) / tau) =
        Real.exp ((reserve + (x : ℝ)) / tau) *
          Real.exp ((c : ℝ) / tau) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    field_simp [ne_of_gt htau]
    ring
  have hyc :
      Real.exp ((reserve + ((y + c : NNReal) : ℝ)) / tau) =
        Real.exp ((reserve + (y : ℝ)) / tau) *
          Real.exp ((c : ℝ) / tau) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    field_simp [ne_of_gt htau]
    ring
  rw [hxc, hyc]
  field_simp [ne_of_gt hc0]

/-- Functional-equation core of Proposition `prop:axiomatization`. -/
theorem translation_ratio_invariance_iff_exponential
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcont : Continuous (EligibleIntensity reserve alpha))
    (hstrict : StrictMono (EligibleIntensity reserve alpha)) :
    TranslationRatioInvariant reserve alpha ↔
      ExponentialOnEligible reserve alpha := by
  constructor
  · intro hratio
    have hcoc := (ratio_iff_cocycle hpos).mp hratio
    rcases normalized_exponential_of_cocycle hpos hcont hstrict hcoc with
      ⟨slope, hslope, hform⟩
    exact exponential_on_eligible_of_normalized hpos hslope hform
  · exact ratio_invariant_of_exponential_on_eligible

open scoped BigOperators

/-- Add the same nonnegative amount to every eligible bid offset. -/
def translateOffsets {ι : Type*} (offsets : ι → NNReal) (c : NNReal) :
    ι → NNReal :=
  fun i => offsets i + c

/-- A single conditional choice probability in a sequential Luce process. -/
def luceStageProbability {ι : Type*} [DecidableEq ι]
    (reserve : ℝ) (alpha : ℝ → ℝ)
    (offsets : ι → NNReal) (remaining : Finset ι) (i : ι) : ℝ :=
  EligibleIntensity reserve alpha (offsets i) /
    ∑ j ∈ remaining, EligibleIntensity reserve alpha (offsets j)

/-- Translation invariance of every finite Luce stage distribution.  `Fin n`
is without loss for a finite participant set. -/
def LuceStageTranslationInvariant (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (offsets : Fin n → NNReal) (remaining : Finset (Fin n))
    (i : Fin n), i ∈ remaining → ∀ c : NNReal,
      luceStageProbability reserve alpha (translateOffsets offsets c)
          remaining i =
        luceStageProbability reserve alpha offsets remaining i

theorem luceStageProbability_translate
    {ι : Type*} [DecidableEq ι]
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcoc : TranslationCocycle reserve alpha)
    (offsets : ι → NNReal) (remaining : Finset ι) (i : ι)
    (hi : i ∈ remaining) (c : NNReal) :
    luceStageProbability reserve alpha (translateOffsets offsets c) remaining i =
      luceStageProbability reserve alpha offsets remaining i := by
  let q := EligibleIntensity reserve alpha c /
    EligibleIntensity reserve alpha 0
  have hq : 0 < q := div_pos (hpos c) (hpos 0)
  have hscale : ∀ z : NNReal,
      EligibleIntensity reserve alpha (z + c) =
        EligibleIntensity reserve alpha z * q := by
    intro z
    dsimp [q]
    simpa [mul_div_assoc] using
      (eq_div_iff (ne_of_gt (hpos 0))).2 (hcoc z c)
  have hsum :
      (∑ j ∈ remaining,
          EligibleIntensity reserve alpha (offsets j + c)) =
        (∑ j ∈ remaining,
          EligibleIntensity reserve alpha (offsets j)) * q := by
    simp_rw [hscale]
    rw [Finset.sum_mul]
  have hden :
      0 < ∑ j ∈ remaining,
        EligibleIntensity reserve alpha (offsets j) := by
    exact Finset.sum_pos' (fun j _ => le_of_lt (hpos (offsets j)))
      ⟨i, hi, hpos (offsets i)⟩
  simp only [luceStageProbability, translateOffsets]
  rw [hscale, hsum]
  field_simp [ne_of_gt hq, ne_of_gt hden]

theorem stage_translation_invariant_of_ratio
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hratio : TranslationRatioInvariant reserve alpha) :
    LuceStageTranslationInvariant reserve alpha := by
  intro n offsets remaining i hi c
  exact luceStageProbability_translate hpos
    ((ratio_iff_cocycle hpos).mp hratio) offsets remaining i hi c

theorem ratio_of_stage_translation_invariant
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hstage : LuceStageTranslationInvariant reserve alpha) :
    TranslationRatioInvariant reserve alpha := by
  intro x y c
  let offsets : Fin 2 → NNReal := fun i => if i = 0 then x else y
  have hi : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) :=
    Finset.mem_univ _
  have h := hstage 2 offsets Finset.univ 0 hi c
  have hchoice :
      EligibleIntensity reserve alpha (x + c) /
          (EligibleIntensity reserve alpha (x + c) +
            EligibleIntensity reserve alpha (y + c)) =
        EligibleIntensity reserve alpha x /
          (EligibleIntensity reserve alpha x +
            EligibleIntensity reserve alpha y) := by
    simpa [luceStageProbability, translateOffsets, offsets,
      Fin.sum_univ_two] using h
  have hdenC : 0 <
      EligibleIntensity reserve alpha (x + c) +
        EligibleIntensity reserve alpha (y + c) :=
    add_pos (hpos (x + c)) (hpos (y + c))
  have hden : 0 <
      EligibleIntensity reserve alpha x +
        EligibleIntensity reserve alpha y :=
    add_pos (hpos x) (hpos y)
  have hcross :=
    (div_eq_div_iff (ne_of_gt hdenC) (ne_of_gt hden)).mp hchoice
  apply (div_eq_div_iff (ne_of_gt (hpos (y + c)))
    (ne_of_gt (hpos y))).2
  nlinarith

/-- Proposition `prop:axiomatization` at the level of the stage distributions
whose products define every sequential-Luce ranking probability. -/
theorem translation_invariance_pins_down_exponential
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcont : Continuous (EligibleIntensity reserve alpha))
    (hstrict : StrictMono (EligibleIntensity reserve alpha)) :
    LuceStageTranslationInvariant reserve alpha ↔
      ExponentialOnEligible reserve alpha := by
  rw [← translation_ratio_invariance_iff_exponential hpos hcont hstrict]
  exact ⟨ratio_of_stage_translation_invariant hpos,
    stage_translation_invariant_of_ratio hpos⟩

/-- An ordered tuple is valid if each selected agent remains available at its
stage. -/
def ValidLuceOrder {ι : Type*} [DecidableEq ι] :
    Finset ι → List ι → Prop
  | _, [] => True
  | remaining, i :: order =>
      i ∈ remaining ∧ ValidLuceOrder (remaining.erase i) order

/-- Product of conditional Luce probabilities along an ordered tuple. -/
def sequentialLuceProbabilityAux {ι : Type*} [DecidableEq ι]
    (reserve : ℝ) (alpha : ℝ → ℝ) (offsets : ι → NNReal) :
    Finset ι → List ι → ℝ
  | _, [] => 1
  | remaining, i :: order =>
      luceStageProbability reserve alpha offsets remaining i *
        sequentialLuceProbabilityAux reserve alpha offsets
          (remaining.erase i) order

/-- Probability of an ordered tuple under sequential Luce sampling without
replacement. -/
def sequentialLuceProbability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reserve : ℝ) (alpha : ℝ → ℝ)
    (offsets : ι → NNReal) (order : List ι) : ℝ :=
  sequentialLuceProbabilityAux reserve alpha offsets Finset.univ order

theorem sequentialLuceProbabilityAux_translate
    {ι : Type*} [DecidableEq ι]
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcoc : TranslationCocycle reserve alpha)
    (offsets : ι → NNReal) (c : NNReal)
    (remaining : Finset ι) (order : List ι)
    (hvalid : ValidLuceOrder remaining order) :
    sequentialLuceProbabilityAux reserve alpha
        (translateOffsets offsets c) remaining order =
      sequentialLuceProbabilityAux reserve alpha offsets remaining order := by
  induction order generalizing remaining with
  | nil =>
      simp [sequentialLuceProbabilityAux]
  | cons i order ih =>
      rcases hvalid with ⟨hi, htail⟩
      simp only [sequentialLuceProbabilityAux]
      rw [luceStageProbability_translate hpos hcoc offsets remaining i hi c,
        ih (remaining := remaining.erase i) htail]

/-- Common translations preserve every valid ordered-tuple probability, hence
the full sequential-Luce ranking distribution. -/
theorem sequentialLuceProbability_translate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hratio : TranslationRatioInvariant reserve alpha)
    (offsets : ι → NNReal) (c : NNReal) (order : List ι)
    (hvalid : ValidLuceOrder Finset.univ order) :
    sequentialLuceProbability reserve alpha (translateOffsets offsets c) order =
      sequentialLuceProbability reserve alpha offsets order := by
  exact sequentialLuceProbabilityAux_translate hpos
    ((ratio_iff_cocycle hpos).mp hratio) offsets c Finset.univ order hvalid

/-- Common translations preserve the probability of every valid ordered tuple
in every finite sequential Luce process. -/
def SequentialLuceTranslationInvariant
    (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (offsets : Fin n → NNReal) (c : NNReal)
    (order : List (Fin n)),
      ValidLuceOrder Finset.univ order →
        sequentialLuceProbability reserve alpha
            (translateOffsets offsets c) order =
          sequentialLuceProbability reserve alpha offsets order

theorem sequential_translation_invariant_of_ratio
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hratio : TranslationRatioInvariant reserve alpha) :
    SequentialLuceTranslationInvariant reserve alpha := by
  intro n offsets c order hvalid
  exact sequentialLuceProbability_translate hpos hratio
    offsets c order hvalid

/-- Binary full rankings recover every pairwise Luce odds ratio, so invariance
of the complete ranking distribution is not weaker than stage invariance. -/
theorem ratio_of_sequential_translation_invariant
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hseq : SequentialLuceTranslationInvariant reserve alpha) :
    TranslationRatioInvariant reserve alpha := by
  intro x y c
  let offsets : Fin 2 → NNReal := fun i => if i = 0 then x else y
  have hvalid :
      ValidLuceOrder (Finset.univ : Finset (Fin 2))
        [(0 : Fin 2), (1 : Fin 2)] := by
    simp [ValidLuceOrder]
  have h := hseq 2 offsets c [(0 : Fin 2), (1 : Fin 2)] hvalid
  have hchoice :
      EligibleIntensity reserve alpha (x + c) /
          (EligibleIntensity reserve alpha (x + c) +
            EligibleIntensity reserve alpha (y + c)) =
        EligibleIntensity reserve alpha x /
          (EligibleIntensity reserve alpha x +
            EligibleIntensity reserve alpha y) := by
    simpa [sequentialLuceProbability, sequentialLuceProbabilityAux,
      luceStageProbability, translateOffsets, offsets, Fin.sum_univ_two,
      ne_of_gt (hpos (y + c)), ne_of_gt (hpos y)] using h
  have hdenC : 0 <
      EligibleIntensity reserve alpha (x + c) +
        EligibleIntensity reserve alpha (y + c) :=
    add_pos (hpos (x + c)) (hpos (y + c))
  have hden : 0 <
      EligibleIntensity reserve alpha x +
        EligibleIntensity reserve alpha y :=
    add_pos (hpos x) (hpos y)
  have hcross :=
    (div_eq_div_iff (ne_of_gt hdenC) (ne_of_gt hden)).mp hchoice
  apply (div_eq_div_iff (ne_of_gt (hpos (y + c)))
    (ne_of_gt (hpos y))).2
  nlinarith

/-- Exact formal statement of Proposition `prop:axiomatization`: within the
positive, continuous, strictly increasing sequential Luce class on eligible
bids, translation invariance of the full ranking distribution holds exactly
for the positive finite-temperature exponential family. -/
theorem translation_invariant_rankings_iff_exponential
    {reserve : ℝ} {alpha : ℝ → ℝ}
    (hpos : ∀ x : NNReal, 0 < EligibleIntensity reserve alpha x)
    (hcont : Continuous (EligibleIntensity reserve alpha))
    (hstrict : StrictMono (EligibleIntensity reserve alpha)) :
    SequentialLuceTranslationInvariant reserve alpha ↔
      ExponentialOnEligible reserve alpha := by
  rw [← translation_ratio_invariance_iff_exponential hpos hcont hstrict]
  exact ⟨ratio_of_sequential_translation_invariant hpos,
    sequential_translation_invariant_of_ratio hpos⟩

end

end SmoothingCliff.Mechanism
