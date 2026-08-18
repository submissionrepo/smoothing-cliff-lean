import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Extremality of the exponential Luce intensity

This file formalizes the calculus part of `prop:luceopt` and its complete
one-slot consequence.  `EligibleC1Intensity` exposes a continuous derivative
witness, so its last field is literally the paper's logarithmic-derivative
cap.  The principal ratio theorem does not assume the desired ordering.

For a finite eligible profile, the exponential intensity is an increasing
multiplicative tilt of every admissible intensity.  A weighted association
identity then proves the resulting one-slot Luce welfare comparison.

The paper's general sequential top-`K` claim additionally needs a formal
ranking-without-replacement construction and an upper-set coupling for every
top-`k` prefix.  That coupling is intentionally not postulated here, so this
file makes no general-`K` claim.
-/

open scoped BigOperators

namespace SmoothingCliff.LuceOptimality

/-- An increasing positive differentiable Luce intensity on the eligible half-line,
with logarithmic derivative bounded by `1 / τ`.

The function `dα` is an explicit derivative witness; no continuity of the
derivative is assumed. -/
def EligibleC1Intensity (reserve τ : ℝ) (α dα : ℝ → ℝ) : Prop :=
  (∀ b, HasDerivAt α (dα b) b) ∧
  MonotoneOn α (Set.Ici reserve) ∧
  (∀ b, reserve ≤ b → 0 < α b) ∧
  ∀ b, reserve ≤ b → dα b / α b ≤ 1 / τ

/-- The logarithmic-derivative cap integrates to the sharp pairwise intensity
ratio bound on any two eligible bids. -/
theorem intensity_ratio_le_exponential (reserve τ : ℝ) (α dα : ℝ → ℝ)
    (_htau : 0 < τ) (hI : EligibleC1Intensity reserve τ α dα)
    {a b : ℝ} (ha : reserve ≤ a) (hab : a ≤ b) :
    α b / α a ≤ Real.exp ((b - a) / τ) := by
  have hb : reserve ≤ b := ha.trans hab
  let f : ℝ → ℝ := fun z => Real.log (α z)
  have hfcont : ContinuousOn f (Set.Ici reserve) := by
    intro z hz
    exact ((hI.1 z).continuousAt.log
      (ne_of_gt (hI.2.2.1 z hz))).continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Ici reserve)) := by
    intro z hz
    have hz' : reserve ≤ z := le_of_lt (by simpa using hz)
    exact ((hI.1 z).log
      (ne_of_gt (hI.2.2.1 z hz'))).differentiableAt.differentiableWithinAt
  have hfcap : ∀ z ∈ interior (Set.Ici reserve), deriv f z ≤ 1 / τ := by
    intro z hz
    have hz' : reserve ≤ z := le_of_lt (by simpa using hz)
    have hd := (hI.1 z).log (ne_of_gt (hI.2.2.1 z hz'))
    rw [hd.deriv]
    exact hI.2.2.2 z hz'
  have hlog := (convex_Ici reserve).image_sub_le_mul_sub_of_deriv_le
    hfcont hfdiff hfcap a ha b hb hab
  have hexp := Real.exp_le_exp.mpr hlog
  simpa [f, Real.exp_sub, Real.exp_log (hI.2.2.1 b hb),
    Real.exp_log (hI.2.2.1 a ha), div_eq_mul_inv, mul_comm] using hexp

/-- The paper's reserve-normalized exponential intensity. -/
noncomputable def exponentialIntensity (reserve τ b : ℝ) : ℝ :=
  Real.exp ((b - reserve) / τ)

/-- The pointwise multiplicative factor that turns `α` into the exponential
intensity. -/
noncomputable def relativeExponentialTilt
    (reserve τ : ℝ) (α : ℝ → ℝ) (b : ℝ) : ℝ :=
  exponentialIntensity reserve τ b / α b

theorem relativeExponentialTilt_pos (reserve τ : ℝ) (α dα : ℝ → ℝ)
    (hI : EligibleC1Intensity reserve τ α dα)
    {b : ℝ} (hb : reserve ≤ b) :
    0 < relativeExponentialTilt reserve τ α b := by
  exact div_pos (Real.exp_pos _) (hI.2.2.1 b hb)

/-- Among eligible bids, the exponential rule is an increasing multiplicative
tilt of every admissible intensity. -/
theorem relativeExponentialTilt_mono (reserve τ : ℝ) (α dα : ℝ → ℝ)
    (htau : 0 < τ) (hI : EligibleC1Intensity reserve τ α dα)
    {a b : ℝ} (ha : reserve ≤ a) (hab : a ≤ b) :
    relativeExponentialTilt reserve τ α a ≤
      relativeExponentialTilt reserve τ α b := by
  have hb : reserve ≤ b := ha.trans hab
  have hαa : 0 < α a := hI.2.2.1 a ha
  have hαb : 0 < α b := hI.2.2.1 b hb
  have hratio :=
    intensity_ratio_le_exponential reserve τ α dα htau hI ha hab
  have habα : α b ≤ α a * Real.exp ((b - a) / τ) := by
    simpa [mul_comm] using (div_le_iff₀ hαa).mp hratio
  apply (div_le_div_iff₀ hαa hαb).2
  calc
    exponentialIntensity reserve τ a * α b
        ≤ exponentialIntensity reserve τ a *
          (α a * Real.exp ((b - a) / τ)) :=
      mul_le_mul_of_nonneg_left habα (Real.exp_pos _).le
    _ = (Real.exp ((a - reserve) / τ) *
          Real.exp ((b - a) / τ)) * α a := by
      simp only [exponentialIntensity]
      ring
    _ = Real.exp (((a - reserve) / τ) + ((b - a) / τ)) * α a := by
      rw [Real.exp_add]
    _ = exponentialIntensity reserve τ b * α a := by
      simp only [exponentialIntensity]
      congr 2
      ring

private lemma doubleSum_product {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, ∑ j, a i * b j) = (∑ i, a i) * (∑ j, b j) := by
  simpa using (Finset.sum_mul_sum Finset.univ Finset.univ a b).symm

/-- A weighted finite association inequality, proved from the nonnegative
double sum of pairwise products. -/
theorem weighted_association {ι : Type*} [Fintype ι]
    (β v q : ι → ℝ) (hβ : ∀ i, 0 ≤ β i) (hvq : Monovary v q) :
    (∑ i, β i * v i) * (∑ i, β i * q i) ≤
      (∑ i, β i) * (∑ i, β i * q i * v i) := by
  have hterm : ∀ i j, 0 ≤ β i * β j * ((v i - v j) * (q i - q j)) := by
    intro i j
    exact mul_nonneg (mul_nonneg (hβ i) (hβ j))
      (hvq.sub_mul_sub_nonneg j i)
  have hsum : 0 ≤ ∑ i, ∑ j,
      β i * β j * ((v i - v j) * (q i - q j)) := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hterm i j
  have hA :
      (∑ i, ∑ j, β i * β j * v i * q i) =
        (∑ i, β i * q i * v i) * (∑ j, β j) := by
    calc
      _ = ∑ i, ∑ j, (β i * q i * v i) * β j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := doubleSum_product (fun i => β i * q i * v i) β
  have hB :
      (∑ i, ∑ j, β i * β j * v j * q j) =
        (∑ i, β i) * (∑ j, β j * q j * v j) := by
    calc
      _ = ∑ i, ∑ j, β i * (β j * q j * v j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := doubleSum_product β (fun j => β j * q j * v j)
  have hC :
      (∑ i, ∑ j, β i * β j * v i * q j) =
        (∑ i, β i * v i) * (∑ j, β j * q j) := by
    calc
      _ = ∑ i, ∑ j, (β i * v i) * (β j * q j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := doubleSum_product (fun i => β i * v i)
        (fun j => β j * q j)
  have hD :
      (∑ i, ∑ j, β i * β j * v j * q i) =
        (∑ i, β i * q i) * (∑ j, β j * v j) := by
    calc
      _ = ∑ i, ∑ j, (β i * q i) * (β j * v j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := doubleSum_product (fun i => β i * q i)
        (fun j => β j * v j)
  have hid :
      (∑ i, ∑ j, β i * β j * ((v i - v j) * (q i - q j))) =
        2 * ((∑ i, β i) * (∑ i, β i * q i * v i) -
          (∑ i, β i * v i) * (∑ i, β i * q i)) := by
    ring_nf
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hA, hB, hC, hD]
    ring
  rw [hid] at hsum
  linarith

/-- Expected weighted welfare under the one-slot Luce choice rule. -/
noncomputable def oneSlotLuceWelfare {ι : Type*} [Fintype ι]
    (weight : ℝ) (v intensity : ι → ℝ) : ℝ :=
  weight * ((∑ i, intensity i * v i) / ∑ i, intensity i)

/-- An increasing positive multiplicative tilt weakly improves one-slot Luce
welfare.  The conclusion follows from `weighted_association`, rather than being
assumed as stochastic dominance. -/
theorem oneSlotLuceWelfare_tilt_mono {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight : ℝ) (v β q : ι → ℝ) (hweight : 0 ≤ weight)
    (hβ : ∀ i, 0 < β i) (hq : ∀ i, 0 < q i) (hvq : Monovary v q) :
    oneSlotLuceWelfare weight v β ≤
      oneSlotLuceWelfare weight v (fun i => β i * q i) := by
  have hsumβ : 0 < ∑ i, β i :=
    Finset.sum_pos (fun i _ => hβ i) Finset.univ_nonempty
  have hsumβq : 0 < ∑ i, β i * q i :=
    Finset.sum_pos (fun i _ => mul_pos (hβ i) (hq i))
      Finset.univ_nonempty
  apply mul_le_mul_of_nonneg_left _ hweight
  apply (div_le_div_iff₀ hsumβ hsumβq).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    weighted_association β v q (fun i => (hβ i).le) hvq

/-- Complete `K = 1` specialization of `prop:luceopt`: for every finite,
nonempty eligible profile and every nonnegative position weight, the
reserve-normalized exponential intensity weakly maximizes expected welfare
among admissible intensities. -/
theorem exponential_oneSlot_welfare_optimal
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (reserve τ weight : ℝ) (v : ι → ℝ) (α dα : ℝ → ℝ)
    (htau : 0 < τ) (hweight : 0 ≤ weight)
    (heligible : ∀ i, reserve ≤ v i)
    (hI : EligibleC1Intensity reserve τ α dα) :
    oneSlotLuceWelfare weight v (fun i => α (v i)) ≤
      oneSlotLuceWelfare weight v
        (fun i => exponentialIntensity reserve τ (v i)) := by
  let β : ι → ℝ := fun i => α (v i)
  let q : ι → ℝ := fun i => relativeExponentialTilt reserve τ α (v i)
  have hβ : ∀ i, 0 < β i := fun i => hI.2.2.1 (v i) (heligible i)
  have hq : ∀ i, 0 < q i := fun i =>
    relativeExponentialTilt_pos reserve τ α dα hI (heligible i)
  have hvq : Monovary v q := by
    intro i j hqij
    by_contra hvij
    have hvji : v j ≤ v i := (not_le.mp hvij).le
    have hqji : q j ≤ q i :=
      relativeExponentialTilt_mono reserve τ α dα htau hI
        (heligible j) hvji
    exact (not_lt_of_ge hqji) hqij
  have htilt :=
    oneSlotLuceWelfare_tilt_mono weight v β q hweight hβ hq hvq
  have hproduct : (fun i => β i * q i) =
      (fun i => exponentialIntensity reserve τ (v i)) := by
    funext i
    dsimp [β, q, relativeExponentialTilt]
    have hne : α (v i) ≠ 0 :=
      ne_of_gt (hI.2.2.1 (v i) (heligible i))
    field_simp
  simpa [β, hproduct] using htilt

end SmoothingCliff.LuceOptimality
