import SmoothingCliff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The two-bidder pointwise frontier

Formal target: Proposition `prop:frontier2` in
`Smoothing_the_Cliff_ITCS.tex`. The declaration is initially split into named
atomic lemmas so that the paper statement can later be assembled without
weakening any premise or conclusion.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

/-- The logistic function used by the two-bidder one-slot PL rule. -/
noncomputable abbrev logistic : ℝ → ℝ := Real.sigmoid

/-- Clamp a real number to the interval `[0, weight]`. -/
noncomputable def clampWeight (weight : NNReal) (z : ℝ) : ℝ :=
  Set.projIcc 0 (weight : ℝ) weight.coe_nonneg z

/-- The paper's capped-linear allocation to bidder 1. -/
noncomputable def cappedLinearFirst (weight sensitivity : NNReal) (b₁ b₂ : ℝ) : ℝ :=
  clampWeight weight (weight / 2 + sensitivity * (b₁ - b₂))

/-- The other member of a two-agent population. -/
def otherBidder (i : Fin 2) : Fin 2 :=
  Equiv.swap (0 : Fin 2) 1 i

/-- The capped-linear two-bidder reduced-form rule. -/
noncomputable def cappedLinearRule {reserve : ℝ} (weight sensitivity : NNReal) :
    InterimRule (Fin 2) reserve :=
  fun b i => cappedLinearFirst weight sensitivity (b i) (b (otherBidder i))

/-- The two-bidder one-slot PL rule at temperature `temperature`. -/
noncomputable def plTwoBidderRule {reserve : ℝ} (weight : NNReal) (temperature : ℝ) :
    InterimRule (Fin 2) reserve :=
  fun b i => weight * logistic
    (((b i : ℝ) - (b (otherBidder i) : ℝ)) / temperature)

@[simp] theorem otherBidder_zero : otherBidder 0 = 1 := by
  simp [otherBidder]

@[simp] theorem otherBidder_one : otherBidder 1 = 0 := by
  simp [otherBidder]

theorem otherBidder_ne (i : Fin 2) : otherBidder i ≠ i := by
  fin_cases i <;> simp [otherBidder]

theorem otherBidder_equivariant (π : Equiv.Perm (Fin 2)) (i : Fin 2) :
    otherBidder (π i) = π (otherBidder i) := by
  apply Fin.eq_of_val_eq
  have hleft : otherBidder (π i) ≠ π i := otherBidder_ne (π i)
  have hright : π (otherBidder i) ≠ π i := by
    exact fun h => otherBidder_ne i (π.injective h)
  omega

theorem clampWeight_nonneg (weight : NNReal) (z : ℝ) :
    0 ≤ clampWeight weight z := by
  exact (Set.projIcc 0 (weight : ℝ) weight.coe_nonneg z).property.1

theorem clampWeight_le (weight : NNReal) (z : ℝ) :
    clampWeight weight z ≤ weight := by
  exact (Set.projIcc 0 (weight : ℝ) weight.coe_nonneg z).property.2

theorem clampWeight_monotone (weight : NNReal) :
    Monotone (clampWeight weight) := by
  intro a b hab
  simp only [clampWeight, Set.coe_projIcc]
  exact max_le_max_left 0 (min_le_min_left (weight : ℝ) hab)

theorem clampWeight_reflect (weight : NNReal) (z : ℝ) :
    clampWeight weight ((weight : ℝ) - z) =
      (weight : ℝ) - clampWeight weight z := by
  simp only [clampWeight, Set.coe_projIcc]
  by_cases hz : z ≤ 0
  · have hzw : z ≤ (weight : ℝ) := hz.trans weight.coe_nonneg
    have hw : (weight : ℝ) ≤ (weight : ℝ) - z := by linarith
    rw [min_eq_left hw, min_eq_right hzw, max_eq_left hz,
      max_eq_right weight.coe_nonneg]
    ring
  · have hzpos : 0 < z := lt_of_not_ge hz
    by_cases hzw : z ≤ (weight : ℝ)
    · have hsub0 : 0 ≤ (weight : ℝ) - z := sub_nonneg.mpr hzw
      have hsubw : (weight : ℝ) - z ≤ (weight : ℝ) := by linarith
      rw [min_eq_right hsubw, max_eq_right hsub0,
        min_eq_right hzw, max_eq_right hzpos.le]
    · have hwz : (weight : ℝ) < z := lt_of_not_ge hzw
      have hsub : (weight : ℝ) - z ≤ 0 := by linarith
      rw [min_eq_right (hsub.trans weight.coe_nonneg), max_eq_left hsub,
        min_eq_left hwz.le, max_eq_right weight.coe_nonneg]
      ring

theorem clampWeight_lipschitz (weight : NNReal) :
    LipschitzWith 1 (clampWeight weight) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
    (Set.abs_projIcc_sub_projIcc weight.coe_nonneg :
      |clampWeight weight c - clampWeight weight d| ≤ |c - d|)

/-- The exact assumptions on the reduced-form class in Proposition
`prop:frontier2`. -/
structure TwoBidderAdmissible {reserve : ℝ} (weight sensitivity : NNReal)
    (x : InterimRule (Fin 2) reserve) : Prop where
  anonymous : Anonymous x
  monotone : OwnMonotone x
  lipschitz : OwnLipschitz sensitivity x
  feasible : OneSlotFeasible (weight : ℝ) x

/-- Analytic core of Proposition `prop:frontier2(ii)`. -/
theorem logistic_lt_capped_tangent (u : ℝ) (hu : 0 < u) :
    logistic u < min (1 / 2 + u / 4) 1 := by
  apply lt_min
  · have hderiv :
        ∀ x ∈ interior (Set.Icc (0 : ℝ) u),
          deriv Real.sigmoid x < (1 : ℝ) / 4 := by
      intro x hx
      rw [interior_Icc] at hx
      have hxpos : 0 < x := hx.1
      have hsHalf : (1 : ℝ) / 2 < Real.sigmoid x := by
        have hmono := Real.sigmoid_strictMono hxpos
        simpa [Real.sigmoid_zero] using hmono
      have hpos : 0 < 2 * Real.sigmoid x - 1 := by
        linarith
      have hsq : 0 < (2 * Real.sigmoid x - 1) ^ 2 :=
        sq_pos_of_pos hpos
      rw [Real.deriv_sigmoid]
      nlinarith
    have hmvt :=
      (convex_Icc (0 : ℝ) u).image_sub_lt_mul_sub_of_deriv_lt
        continuous_sigmoid.continuousOn
        differentiable_sigmoid.differentiableOn
        hderiv
        0 ⟨le_rfl, hu.le⟩
        u ⟨hu.le, le_rfl⟩
        hu
    rw [Real.sigmoid_zero] at hmvt
    norm_num at hmvt ⊢
    linarith
  · exact Real.sigmoid_lt_one u

/-- Envelope part of Proposition `prop:frontier2(i)`, stated directly for the
two allocation coordinates. -/
theorem twoBidder_envelope
    {reserve : ℝ} {weight sensitivity : NNReal}
    (x : InterimRule (Fin 2) reserve)
    (hAnon : Anonymous x)
    (hLip : OwnLipschitz sensitivity x)
    (hFeas : OneSlotFeasible (weight : ℝ) x)
    (b : EligibleProfile (Fin 2) reserve)
    (hOrder : (b 1 : ℝ) ≤ (b 0 : ℝ)) :
    x b 0 ≤ min ((weight : ℝ) / 2 + sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))) weight := by
  let bt : EligibleProfile (Fin 2) reserve := updateBid b 0 (b 1)
  have hbt_relabel :
      relabelProfile (Equiv.swap (0 : Fin 2) 1) bt = bt := by
    funext i
    fin_cases i <;> simp [bt, updateBid, relabelProfile]
  have hTie : x bt 0 = x bt 1 := by
    have h := hAnon (Equiv.swap (0 : Fin 2) 1) bt 0
    rw [hbt_relabel] at h
    simpa using h.symm
  have hTieSum := hFeas.2 bt
  rw [Fin.sum_univ_two] at hTieSum
  have hTieBound : x bt 0 ≤ weight / 2 := by
    linarith
  have hself : updateBid b 0 (b 0) = b := by
    funext i
    fin_cases i <;> simp [updateBid]
  have hdist := (hLip b 0).dist_le_mul (b 0) (b 1)
  rw [hself] at hdist
  have hdist' :
      |x b 0 - x bt 0| ≤
        (sensitivity : ℝ) * ((b 0 : ℝ) - (b 1 : ℝ)) := by
    simpa [bt, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hOrder)] using hdist
  have hEnvelope :
      x b 0 ≤ weight / 2 +
        (sensitivity : ℝ) * ((b 0 : ℝ) - (b 1 : ℝ)) := by
    have habs : x b 0 - x bt 0 ≤ |x b 0 - x bt 0| := le_abs_self _
    linarith
  have hWeight : x b 0 ≤ weight := by
    have hnonneg := hFeas.1 b 1
    have hsum := hFeas.2 b
    rw [Fin.sum_univ_two] at hsum
    linarith
  exact le_min hEnvelope hWeight

/-- Symmetric form of `twoBidder_envelope` for bidder 1. -/
theorem twoBidder_envelope_second
    {reserve : ℝ} {weight sensitivity : NNReal}
    (x : InterimRule (Fin 2) reserve)
    (hAnon : Anonymous x)
    (hLip : OwnLipschitz sensitivity x)
    (hFeas : OneSlotFeasible (weight : ℝ) x)
    (b : EligibleProfile (Fin 2) reserve)
    (hOrder : (b 0 : ℝ) ≤ (b 1 : ℝ)) :
    x b 1 ≤ min ((weight : ℝ) / 2 +
      sensitivity * ((b 1 : ℝ) - (b 0 : ℝ))) weight := by
  let π : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let bs : EligibleProfile (Fin 2) reserve := relabelProfile π b
  have hbsOrder : (bs 1 : ℝ) ≤ (bs 0 : ℝ) := by
    simpa [bs, π, relabelProfile] using hOrder
  have h := twoBidder_envelope x hAnon hLip hFeas bs hbsOrder
  have hanon := hAnon π b 1
  have hπ : π 1 = 0 := by simp [π]
  have hbs0 : (bs 0 : ℝ) = (b 1 : ℝ) := by
    simp [bs, π, relabelProfile]
  have hbs1 : (bs 1 : ℝ) = (b 0 : ℝ) := by
    simp [bs, π, relabelProfile]
  rw [hπ] at hanon
  rw [hanon] at h
  simpa [hbs0, hbs1] using h

/-- At an ordered profile, the capped-linear rule reaches bidder 0's envelope. -/
theorem cappedLinear_eq_envelope_first
    {reserve : ℝ} (weight sensitivity : NNReal)
    (b : EligibleProfile (Fin 2) reserve)
    (hOrder : (b 1 : ℝ) ≤ (b 0 : ℝ)) :
    cappedLinearRule weight sensitivity b 0 =
      min ((weight : ℝ) / 2 +
        sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))) weight := by
  have hz : 0 ≤ (weight : ℝ) / 2 +
      sensitivity * ((b 0 : ℝ) - (b 1 : ℝ)) := by
    positivity
  simp only [cappedLinearRule, cappedLinearFirst, otherBidder_zero,
    clampWeight, Set.coe_projIcc]
  rw [max_eq_right (le_min weight.coe_nonneg hz), min_comm]

/-- At the reverse ordering, the capped-linear rule reaches bidder 1's envelope. -/
theorem cappedLinear_eq_envelope_second
    {reserve : ℝ} (weight sensitivity : NNReal)
    (b : EligibleProfile (Fin 2) reserve)
    (hOrder : (b 0 : ℝ) ≤ (b 1 : ℝ)) :
    cappedLinearRule weight sensitivity b 1 =
      min ((weight : ℝ) / 2 +
        sensitivity * ((b 1 : ℝ) - (b 0 : ℝ))) weight := by
  have hz : 0 ≤ (weight : ℝ) / 2 +
      sensitivity * ((b 1 : ℝ) - (b 0 : ℝ)) := by
    positivity
  simp only [cappedLinearRule, cappedLinearFirst, otherBidder_one,
    clampWeight, Set.coe_projIcc]
  rw [max_eq_right (le_min weight.coe_nonneg hz), min_comm]

/-- The capped-linear rule allocates all available priority mass. -/
theorem cappedLinear_noWaste
    {reserve : ℝ} (weight sensitivity : NNReal) :
    OneSlotNoWaste (weight : ℝ)
      (cappedLinearRule (reserve := reserve) weight sensitivity) := by
  intro b
  rw [Fin.sum_univ_two]
  simp only [cappedLinearRule, cappedLinearFirst, otherBidder_zero,
    otherBidder_one]
  let z : ℝ :=
    (weight : ℝ) / 2 + sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))
  have hcomp :
      (weight : ℝ) / 2 +
          sensitivity * ((b 1 : ℝ) - (b 0 : ℝ)) =
        (weight : ℝ) - z := by
    dsimp [z]
    ring
  rw [hcomp, clampWeight_reflect]
  linarith

/-- The capped-linear rule belongs to the admissible class. -/
theorem cappedLinear_admissible
    {reserve : ℝ} (weight sensitivity : NNReal) :
    TwoBidderAdmissible (reserve := reserve) weight sensitivity
      (cappedLinearRule (reserve := reserve) weight sensitivity) := by
  constructor
  · intro π b i
    simp only [cappedLinearRule, cappedLinearFirst, relabelProfile]
    rw [otherBidder_equivariant]
    simp
  · intro b i z z' hzz'
    apply clampWeight_monotone weight
    simp [updateBid, otherBidder_ne]
    have hzzReal : (z : ℝ) ≤ (z' : ℝ) := hzz'
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right hzzReal _) sensitivity.coe_nonneg
  · intro b i
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    have hclamp := (clampWeight_lipschitz weight).dist_le_mul
      ((weight : ℝ) / 2 +
        sensitivity * ((z : ℝ) - (b (otherBidder i) : ℝ)))
      ((weight : ℝ) / 2 +
        sensitivity * ((z' : ℝ) - (b (otherBidder i) : ℝ)))
    simp [cappedLinearRule, cappedLinearFirst, updateBid, otherBidder_ne]
    calc
      dist
          (clampWeight weight
            ((weight : ℝ) / 2 +
              sensitivity * ((z : ℝ) - (b (otherBidder i) : ℝ))))
          (clampWeight weight
            ((weight : ℝ) / 2 +
              sensitivity * ((z' : ℝ) - (b (otherBidder i) : ℝ)))) ≤
          dist
            ((weight : ℝ) / 2 +
              sensitivity * ((z : ℝ) - (b (otherBidder i) : ℝ)))
            ((weight : ℝ) / 2 +
              sensitivity * ((z' : ℝ) - (b (otherBidder i) : ℝ))) := by
            simpa only [NNReal.coe_one, one_mul] using hclamp
      _ = (sensitivity : ℝ) * dist z z' := by
        rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
        have halg :
            (weight : ℝ) / 2 +
                  sensitivity * ((z : ℝ) - (b (otherBidder i) : ℝ)) -
                ((weight : ℝ) / 2 +
                  sensitivity * ((z' : ℝ) - (b (otherBidder i) : ℝ))) =
              (sensitivity : ℝ) * ((z : ℝ) - (z' : ℝ)) := by
          ring
        rw [halg, abs_mul, abs_of_nonneg sensitivity.coe_nonneg]
  · constructor
    · intro b i
      exact clampWeight_nonneg weight _
    · intro b
      exact (cappedLinear_noWaste weight sensitivity b).le

/-- Pointwise welfare optimality of the capped-linear rule within the admissible
class. The nonnegative-reserve premise is used only to rule out gains from
discarding allocation mass when values are negative. -/
theorem twoBidder_cappedLinear_welfare_optimal
    {reserve : ℝ} {weight sensitivity : NNReal}
    (hReserve : 0 ≤ reserve)
    (x : InterimRule (Fin 2) reserve)
    (hx : TwoBidderAdmissible weight sensitivity x)
    (values : EligibleProfile (Fin 2) reserve) :
    welfare x values ≤
      welfare (cappedLinearRule (reserve := reserve) weight sensitivity) values := by
  have hv0 : 0 ≤ (values 0 : ℝ) :=
    hReserve.trans (values 0).property
  have hv1 : 0 ≤ (values 1 : ℝ) :=
    hReserve.trans (values 1).property
  have hxsum := hx.feasible.2 values
  rw [Fin.sum_univ_two] at hxsum
  have hysum := cappedLinear_noWaste weight sensitivity values
  rw [Fin.sum_univ_two] at hysum
  rcases le_total (values 1 : ℝ) (values 0 : ℝ) with h10 | h01
  · have hbound :=
      twoBidder_envelope x hx.anonymous hx.lipschitz hx.feasible values h10
    have hy0 := cappedLinear_eq_envelope_first weight sensitivity values h10
    have hxy0 :
        x values 0 ≤ cappedLinearRule weight sensitivity values 0 := by
      rw [hy0]
      exact hbound
    have hprod1 :
        0 ≤ ((values 0 : ℝ) - (values 1 : ℝ)) *
          (cappedLinearRule weight sensitivity values 0 - x values 0) :=
      mul_nonneg (sub_nonneg.mpr h10) (sub_nonneg.mpr hxy0)
    have hprod2 :
        0 ≤ (values 1 : ℝ) *
          ((weight : ℝ) - x values 0 - x values 1) :=
      mul_nonneg hv1 (by linarith)
    simp only [welfare, Fin.sum_univ_two]
    nlinarith
  · have hbound :=
      twoBidder_envelope_second x hx.anonymous hx.lipschitz hx.feasible values h01
    have hy1 := cappedLinear_eq_envelope_second weight sensitivity values h01
    have hxy1 :
        x values 1 ≤ cappedLinearRule weight sensitivity values 1 := by
      rw [hy1]
      exact hbound
    have hprod1 :
        0 ≤ ((values 1 : ℝ) - (values 0 : ℝ)) *
          (cappedLinearRule weight sensitivity values 1 - x values 1) :=
      mul_nonneg (sub_nonneg.mpr h01) (sub_nonneg.mpr hxy1)
    have hprod2 :
        0 ≤ (values 0 : ℝ) *
          ((weight : ℝ) - x values 0 - x values 1) :=
      mul_nonneg hv0 (by linarith)
    simp only [welfare, Fin.sum_univ_two]
    nlinarith

/-- At the temperature that matches the local slope bound, PL is strictly below
the capped-linear frontier at every strictly ordered profile. -/
theorem pl_strictly_below_cappedLinear
    {reserve : ℝ} {weight sensitivity : NNReal}
    (hWeight : 0 < (weight : ℝ))
    (hSensitivity : 0 < (sensitivity : ℝ))
    (b : EligibleProfile (Fin 2) reserve)
    (hOrder : (b 1 : ℝ) < (b 0 : ℝ)) :
    plTwoBidderRule weight (weight / (4 * sensitivity)) b 0 <
      cappedLinearRule weight sensitivity b 0 := by
  let u : ℝ :=
    4 * (sensitivity : ℝ) * ((b 0 : ℝ) - (b 1 : ℝ)) / (weight : ℝ)
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hlog := logistic_lt_capped_tangent u hu
  have hmul := mul_lt_mul_of_pos_left hlog hWeight
  have hPLArg :
      ((b 0 : ℝ) - (b 1 : ℝ)) /
          ((weight : ℝ) / (4 * (sensitivity : ℝ))) = u := by
    dsimp [u]
    field_simp
  have hScale :
      (weight : ℝ) * (1 / 2 + u / 4) =
        (weight : ℝ) / 2 +
          sensitivity * ((b 0 : ℝ) - (b 1 : ℝ)) := by
    dsimp [u]
    field_simp
  have hScaledMin :
      (weight : ℝ) * min (1 / 2 + u / 4) 1 =
        min ((weight : ℝ) / 2 +
          sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))) weight := by
    by_cases hle : 1 / 2 + u / 4 ≤ 1
    · have hzle :
          (weight : ℝ) / 2 +
              sensitivity * ((b 0 : ℝ) - (b 1 : ℝ)) ≤ weight := by
        have hm := mul_le_mul_of_nonneg_left hle hWeight.le
        rw [hScale] at hm
        simpa using hm
      rw [min_eq_left hle, min_eq_left hzle]
      exact hScale
    · have hrev : 1 ≤ 1 / 2 + u / 4 := le_of_not_ge hle
      have hzrev :
          (weight : ℝ) ≤
            (weight : ℝ) / 2 +
              sensitivity * ((b 0 : ℝ) - (b 1 : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_left hrev hWeight.le
        rw [hScale] at hm
        simpa using hm
      rw [min_eq_right hrev, min_eq_right hzrev]
      ring
  rw [cappedLinear_eq_envelope_first weight sensitivity b hOrder.le]
  change (weight : ℝ) * logistic
      (((b 0 : ℝ) - (b 1 : ℝ)) /
        ((weight : ℝ) / (4 * (sensitivity : ℝ)))) <
      min ((weight : ℝ) / 2 +
        sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))) weight
  rw [hPLArg, ← hScaledMin]
  exact hmul

/-- Paper-level two-bidder frontier target. The conjunction mirrors the
envelope, attainability, pointwise-welfare, and strict-PL claims in both parts
of Proposition `prop:frontier2`. -/
theorem twoBidder_frontier
    {reserve : ℝ} {weight sensitivity : NNReal}
    (hReserve : 0 ≤ reserve) (hWeight : 0 < (weight : ℝ))
    (hSensitivity : 0 < (sensitivity : ℝ)) :
    (∀ (x : InterimRule (Fin 2) reserve),
        TwoBidderAdmissible weight sensitivity x →
        ∀ (b : EligibleProfile (Fin 2) reserve),
          (b 1 : ℝ) ≤ (b 0 : ℝ) →
          x b 0 ≤
            min ((weight : ℝ) / 2 + sensitivity * ((b 0 : ℝ) - (b 1 : ℝ))) weight) ∧
    TwoBidderAdmissible (reserve := reserve) weight sensitivity
      (cappedLinearRule (reserve := reserve) weight sensitivity) ∧
    (∀ (x : InterimRule (Fin 2) reserve),
        TwoBidderAdmissible weight sensitivity x →
        ∀ values : EligibleProfile (Fin 2) reserve,
          welfare x values ≤
            welfare (cappedLinearRule (reserve := reserve) weight sensitivity) values) ∧
    (∀ b : EligibleProfile (Fin 2) reserve,
        (b 1 : ℝ) < (b 0 : ℝ) →
        plTwoBidderRule weight (weight / (4 * sensitivity)) b 0 <
          cappedLinearRule weight sensitivity b 0) := by
  refine ⟨?_, cappedLinear_admissible weight sensitivity, ?_, ?_⟩
  · intro x hx b hOrder
    exact twoBidder_envelope x hx.anonymous hx.lipschitz hx.feasible b hOrder
  · intro x hx values
    exact twoBidder_cappedLinear_welfare_optimal hReserve x hx values
  · exact pl_strictly_below_cappedLinear hWeight hSensitivity

end SmoothingCliff.Frontier
