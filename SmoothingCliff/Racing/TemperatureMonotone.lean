import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# One-slot PL welfare is non-increasing in the temperature

Formal target: the final clause of Proposition `prop:netsurplus_n` in
`Smoothing_the_Cliff_ITCS.tex`.  With `K = 1` and inverse temperature
`s = 1 / tau`, allocation shares are the softmax weights of the values and
expected welfare per unit of slot weight is the softmax mean.  Its derivative
in `s` is the softmax variance, hence non-negative, so welfare is
non-decreasing in `s` and non-increasing in `tau`.

The reserve cancels from every share, so the reserve-adjusted intensities of
the paper and the plain softmax weights used here define the same allocation.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Softmax partition function at inverse temperature `s`. -/
def softmaxPartition (value : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, Real.exp (s * value j)

/-- Softmax first moment. -/
def softmaxFirstMoment (value : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, value j * Real.exp (s * value j)

/-- Softmax second moment. -/
def softmaxSecondMoment (value : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, value j ^ 2 * Real.exp (s * value j)

/-- Expected one-slot welfare per unit of slot weight: the softmax mean. -/
def softmaxMean (value : ι → ℝ) (s : ℝ) : ℝ :=
  softmaxFirstMoment value s / softmaxPartition value s

/-- The softmax variance, written as the second moment times the partition
minus the squared first moment, over the squared partition. -/
def softmaxVariance (value : ι → ℝ) (s : ℝ) : ℝ :=
  (softmaxSecondMoment value s * softmaxPartition value s -
      softmaxFirstMoment value s * softmaxFirstMoment value s) /
    softmaxPartition value s ^ 2

theorem softmaxPartition_pos [Nonempty ι] (value : ι → ℝ) (s : ℝ) :
    0 < softmaxPartition value s :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- The reserve cancels from the paper's allocation shares, so the
reserve-adjusted intensities and the plain softmax weights agree. -/
theorem reserveAdjusted_share_eq_softmax_share [Nonempty ι]
    (value : ι → ℝ) (reserve tau : ℝ) (hTau : tau ≠ 0) (i : ι) :
    Real.exp ((value i - reserve) / tau) /
        (∑ j, Real.exp ((value j - reserve) / tau)) =
      Real.exp ((1 / tau) * value i) /
        softmaxPartition value (1 / tau) := by
  have hsplit : ∀ j : ι,
      Real.exp ((value j - reserve) / tau) =
        Real.exp (-(reserve / tau)) * Real.exp ((1 / tau) * value j) := by
    intro j
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hshift : Real.exp (-(reserve / tau)) ≠ 0 := (Real.exp_pos _).ne'
  simp only [hsplit, softmaxPartition, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hshift]

omit [Fintype ι] in
/-- Derivative of a single softmax term. -/
theorem hasDerivAt_softmaxTerm (value : ι → ℝ) (s : ℝ) (j : ι) :
    HasDerivAt (fun t : ℝ => Real.exp (t * value j))
      (value j * Real.exp (s * value j)) s := by
  have hlin : HasDerivAt (fun t : ℝ => t * value j) (value j) s := by
    simpa using (hasDerivAt_id s).mul_const (value j)
  simpa [mul_comm] using hlin.exp

theorem hasDerivAt_softmaxPartition (value : ι → ℝ) (s : ℝ) :
    HasDerivAt (softmaxPartition value) (softmaxFirstMoment value s) s :=
  HasDerivAt.fun_sum fun j _ => hasDerivAt_softmaxTerm value s j

theorem hasDerivAt_softmaxFirstMoment (value : ι → ℝ) (s : ℝ) :
    HasDerivAt (softmaxFirstMoment value) (softmaxSecondMoment value s) s := by
  refine HasDerivAt.fun_sum fun j _ => ?_
  have hmul := (hasDerivAt_softmaxTerm value s j).const_mul (value j)
  convert hmul using 1
  ring

/-- The softmax mean has derivative equal to the softmax variance. -/
theorem hasDerivAt_softmaxMean [Nonempty ι] (value : ι → ℝ) (s : ℝ) :
    HasDerivAt (softmaxMean value) (softmaxVariance value s) s :=
  HasDerivAt.fun_div (hasDerivAt_softmaxFirstMoment value s)
    (hasDerivAt_softmaxPartition value s)
    (softmaxPartition_pos value s).ne'

/-- Cauchy--Schwarz in the softmax weights. -/
theorem softmaxFirstMoment_sq_le (value : ι → ℝ) (s : ℝ) :
    softmaxFirstMoment value s ^ 2 ≤
      softmaxSecondMoment value s * softmaxPartition value s :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun _ _ => by positivity) (fun _ _ => (Real.exp_pos _).le)
    (fun _ _ => le_of_eq (by ring))

theorem softmaxVariance_nonneg [Nonempty ι] (value : ι → ℝ) (s : ℝ) :
    0 ≤ softmaxVariance value s := by
  have hZ : 0 < softmaxPartition value s := softmaxPartition_pos value s
  have hCS := softmaxFirstMoment_sq_le value s
  have hnum : 0 ≤ softmaxSecondMoment value s * softmaxPartition value s -
      softmaxFirstMoment value s * softmaxFirstMoment value s := by
    nlinarith [hCS]
  unfold softmaxVariance
  positivity

/-- Expected one-slot welfare per unit of slot weight is non-decreasing in the
inverse temperature. -/
theorem softmaxMean_monotone [Nonempty ι] (value : ι → ℝ) :
    Monotone (softmaxMean value) :=
  monotone_of_hasDerivAt_nonneg (f' := softmaxVariance value)
    (fun s => hasDerivAt_softmaxMean value s)
    (fun s => softmaxVariance_nonneg value s)

/-- The final clause of `prop:netsurplus_n`: with one slot, expected welfare is
non-increasing in the temperature on the positive temperatures, so a
welfare-maximizing temperature can be taken at or below any certified level. -/
theorem softmaxMean_inverse_antitoneOn [Nonempty ι] (value : ι → ℝ) :
    AntitoneOn (fun tau : ℝ => softmaxMean value (1 / tau)) (Set.Ioi 0) := by
  intro tau₁ h₁ tau₂ _ hle
  exact softmaxMean_monotone value
    (one_div_le_one_div_of_le (Set.mem_Ioi.mp h₁) hle)

end

end SmoothingCliff.Racing
