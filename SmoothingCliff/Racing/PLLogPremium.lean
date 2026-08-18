import SmoothingCliff.Racing.WelfareLoss
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logarithmic one-slot PL welfare premium

This file formalizes part (iii) of Theorem `thm:pos`.  A market with one
distinguished leader and `m` trailers is represented by `Option ι`, where
`m = Fintype.card ι`.  The value of trailer `i` is

`base - tau * gap i`.

The file first connects this parametrization to the actual finite
Plackett--Luce probabilities from `WelfareLoss.lean`.  It then proves the exact
loss formula

`w tau * (sum_i gap_i exp(-gap_i)) / (1 + sum_i exp(-gap_i))`

and a normalized logarithmic bound.  Substituting the paper's matched
certificate `tau = w / (4 S)` gives its stated constant.  Finally, the profile
with all `m` trailers tied `tau * log m` below the leader is evaluated exactly.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Values for a finite one-leader profile.  `none` is the leader and
`some i` is trailer `i`, whose cardinal gap from the leader is
`tau * gap i`. -/
def oneLeaderPLValue {ι : Type*} (base tau : ℝ) (gap : ι → ℝ) : Option ι → ℝ
  | none => base
  | some i => base - tau * gap i

/-- Welfare under the genuine finite one-slot PL probabilities for the
one-leader profile. -/
def oneLeaderPLWelfare {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base tau weight : ℝ) (gap : ι → ℝ) : ℝ :=
  oneSlotPLWelfare (Finset.univ : Finset (Option ι))
    (oneLeaderPLValue base tau gap) tau weight

/-- The scale appearing in the paper, with `m` equal to the number of
trailers (and hence `m = n - 1`). -/
def plLogScale (ι : Type*) [Fintype ι] : ℝ :=
  max 1 (Real.log (Fintype.card ι : ℝ))

/-- The temperature selected by the paper's matched one-slot certificate. -/
def matchedPLTemperature (weight sensitivity : ℝ) : ℝ :=
  weight / (4 * sensitivity)

/-- At positive temperature, the distinguished coordinate is indeed highest
whenever every normalized gap is nonnegative. -/
theorem oneLeaderPLValue_trailer_le_leader
    {ι : Type*} (base tau : ℝ) (gap : ι → ℝ)
    (htau : 0 ≤ tau) (hgap : ∀ i, 0 ≤ gap i) (i : ι) :
    oneLeaderPLValue base tau gap (some i) ≤
      oneLeaderPLValue base tau gap none := by
  simp only [oneLeaderPLValue]
  exact sub_le_self _ (mul_nonneg htau (hgap i))

/-- The leader's raw finite PL probability, rewritten in normalized gap
coordinates. -/
theorem oneLeaderPLProbability_leader
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base tau : ℝ) (gap : ι → ℝ) (htau : tau ≠ 0) :
    oneSlotPLProbability (Finset.univ : Finset (Option ι))
        (oneLeaderPLValue base tau gap) tau none =
      1 / (1 + ∑ i, Real.exp (-gap i)) := by
  simp only [oneSlotPLProbability, oneLeaderPLValue]
  simp only [Fintype.sum_option]
  have hexp : ∀ i, Real.exp ((base - tau * gap i) / tau) =
      Real.exp (base / tau) * Real.exp (-gap i) := by
    intro i
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hexp]
  rw [← Finset.mul_sum]
  have hE : Real.exp (base / tau) ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp

/-- Each trailer's raw finite PL probability, rewritten in normalized gap
coordinates.  Together with `oneLeaderPLProbability_leader`, this proves that
the weights are exactly `1 : exp(-gap i)`, rather than postulating that
normalized formula. -/
theorem oneLeaderPLProbability_trailer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base tau : ℝ) (gap : ι → ℝ) (htau : tau ≠ 0) (i : ι) :
    oneSlotPLProbability (Finset.univ : Finset (Option ι))
        (oneLeaderPLValue base tau gap) tau (some i) =
      Real.exp (-gap i) / (1 + ∑ j, Real.exp (-gap j)) := by
  simp only [oneSlotPLProbability, oneLeaderPLValue]
  simp only [Fintype.sum_option]
  have hexp : ∀ j, Real.exp ((base - tau * gap j) / tau) =
      Real.exp (base / tau) * Real.exp (-gap j) := by
    intro j
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [hexp]
  rw [← Finset.mul_sum]
  have hE : Real.exp (base / tau) ≠ 0 := ne_of_gt (Real.exp_pos _)
  field_simp

/-- Exact strict-priority-minus-PL welfare difference for a finite one-leader
profile.  This is derived from the raw PL probabilities and expected welfare,
not supplied as an assumption. -/
theorem oneLeaderPLWelfare_premium_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base tau weight : ℝ) (gap : ι → ℝ) (htau : tau ≠ 0) :
    weight * base - oneLeaderPLWelfare base tau weight gap =
      weight * tau *
        ((∑ i, gap i * Real.exp (-gap i)) /
          (1 + ∑ i, Real.exp (-gap i))) := by
  unfold oneLeaderPLWelfare
  change weight * oneLeaderPLValue base tau gap none -
      oneSlotPLWelfare (Finset.univ : Finset (Option ι))
        (oneLeaderPLValue base tau gap) tau weight = _
  rw [oneSlot_welfare_gap_identity
    (Finset.univ : Finset (Option ι)) (oneLeaderPLValue base tau gap)
    tau weight none (Finset.univ_nonempty)]
  simp only [Fintype.sum_option, oneLeaderPLValue, sub_self, zero_mul, zero_add]
  simp_rw [oneLeaderPLProbability_trailer base tau gap htau]
  have hden : 1 + ∑ j, Real.exp (-gap j) ≠ 0 := by
    positivity
  field_simp
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  field_simp
  ring

/-- On `[1, infinity)`, `x * exp (-x)` is antitone.  The proof uses only
`1 + d ≤ exp d`, avoiding a differentiability side argument. -/
theorem mul_exp_neg_le_of_one_le {a x : ℝ} (ha : 1 ≤ a) (hax : a ≤ x) :
    x * Real.exp (-x) ≤ a * Real.exp (-a) := by
  have hd : 0 ≤ x - a := sub_nonneg.mpr hax
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  have he : 1 + (x - a) ≤ Real.exp (x - a) := by
    simpa [add_comm] using Real.add_one_le_exp (x - a)
  have hscale :
      a * (1 + (x - a)) ≤ a * Real.exp (x - a) :=
    mul_le_mul_of_nonneg_left he ha0
  have hsmall : x ≤ a * (1 + (x - a)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hd]
  have hxle : x ≤ a * Real.exp (x - a) := hsmall.trans hscale
  calc
    x * Real.exp (-x) ≤
        (a * Real.exp (x - a)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hxle (Real.exp_pos _).le
    _ = a * Real.exp (-a) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf

/-- Exact normalized analytic core.  For `m` trailers, the normalized PL loss
is at most `max {1, log m}`.  This is a factor-two strengthening of the bound
used in the paper; the paper's displayed constant follows below as a direct
corollary.

The proof sets `L = max {1, log m}`.  If `u ≤ L`, then
`u exp(-u) ≤ L exp(-u)`.  If `u > L`, tail monotonicity and
`exp(-L) ≤ 1/m` give `u exp(-u) ≤ L/m`.  Summing the pointwise bound
`u exp(-u) ≤ L exp(-u) + L/m` yields `numerator ≤ L * denominator`. -/
theorem normalizedPLLogPremium_le
    {ι : Type*} [Fintype ι] [Nonempty ι] (gap : ι → ℝ) :
    (∑ i, gap i * Real.exp (-gap i)) /
        (1 + ∑ i, Real.exp (-gap i)) ≤ plLogScale ι := by
  let m : ℝ := Fintype.card ι
  let L : ℝ := max 1 (Real.log m)
  have hmNat : 0 < Fintype.card ι := Fintype.card_pos
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hmNat
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogL : Real.log m ≤ L := le_max_right _ _
  have hexpL : Real.exp (-L) ≤ 1 / m := by
    calc
      Real.exp (-L) ≤ Real.exp (-Real.log m) :=
        Real.exp_le_exp.mpr (neg_le_neg hlogL)
      _ = 1 / m := by
        rw [Real.exp_neg, Real.exp_log hm]
        simp only [one_div]
  have hpoint (i : ι) :
      gap i * Real.exp (-gap i) ≤
        L * Real.exp (-gap i) + L / m := by
    by_cases hi : gap i ≤ L
    · have hfirst :
          gap i * Real.exp (-gap i) ≤ L * Real.exp (-gap i) :=
        mul_le_mul_of_nonneg_right hi (Real.exp_pos _).le
      have hLm : 0 ≤ L / m := div_nonneg hL0 hm.le
      linarith
    · have htail := mul_exp_neg_le_of_one_le hL1 (le_of_not_ge hi)
      have hscale : L * Real.exp (-L) ≤ L * (1 / m) :=
        mul_le_mul_of_nonneg_left hexpL hL0
      have hbound : gap i * Real.exp (-gap i) ≤ L / m := by
        calc
          gap i * Real.exp (-gap i) ≤ L * Real.exp (-L) := htail
          _ ≤ L * (1 / m) := hscale
          _ = L / m := by ring
      have hfirst : 0 ≤ L * Real.exp (-gap i) :=
        mul_nonneg hL0 (Real.exp_pos _).le
      linarith
  have hsum :
      (∑ i, gap i * Real.exp (-gap i)) ≤
        L * (∑ i, Real.exp (-gap i)) + L := by
    calc
      (∑ i, gap i * Real.exp (-gap i)) ≤
          ∑ i, (L * Real.exp (-gap i) + L / m) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = L * (∑ i, Real.exp (-gap i)) + L := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        dsimp [m]
        field_simp
  have hden : 0 < 1 + ∑ i, Real.exp (-gap i) := by
    positivity
  have hratio :
      (∑ i, gap i * Real.exp (-gap i)) /
          (1 + ∑ i, Real.exp (-gap i)) ≤ L := by
    apply (div_le_iff₀ hden).2
    calc
      (∑ i, gap i * Real.exp (-gap i)) ≤
          L * (∑ i, Real.exp (-gap i)) + L := hsum
      _ = L * (1 + ∑ i, Real.exp (-gap i)) := by ring
  simpa [plLogScale, L, m] using hratio

/-- For a genuine leader profile, the exact PL premium is nonnegative and
obeys the sharper coefficient-one logarithmic upper bound. -/
theorem oneLeaderPLWelfare_premium_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base tau weight : ℝ) (gap : ι → ℝ)
    (htau : 0 < tau) (hweight : 0 ≤ weight)
    (hgap : ∀ i, 0 ≤ gap i) :
    0 ≤ weight * base - oneLeaderPLWelfare base tau weight gap ∧
    weight * base - oneLeaderPLWelfare base tau weight gap ≤
      weight * tau * plLogScale ι := by
  rw [oneLeaderPLWelfare_premium_eq base tau weight gap (ne_of_gt htau)]
  constructor
  · apply mul_nonneg (mul_nonneg hweight htau.le)
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (hgap i) (Real.exp_pos _).le
    · positivity
  · exact mul_le_mul_of_nonneg_left (normalizedPLLogPremium_le gap)
      (mul_nonneg hweight htau.le)

/-- The paper's direct-temperature upper bound.  It deliberately states the
paper's (looser) factor `2`, even though
`oneLeaderPLWelfare_premium_bounds` proves factor `1`. -/
theorem oneLeaderPLWelfare_premium_le_paper
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base tau weight : ℝ) (gap : ι → ℝ)
    (htau : 0 < tau) (hweight : 0 ≤ weight)
    (hgap : ∀ i, 0 ≤ gap i) :
    weight * base - oneLeaderPLWelfare base tau weight gap ≤
      2 * weight * tau * plLogScale ι := by
  have hsharp :=
    (oneLeaderPLWelfare_premium_bounds base tau weight gap
      htau hweight hgap).2
  have hscale : 0 ≤ weight * tau * plLogScale ι :=
    mul_nonneg (mul_nonneg hweight htau.le)
      (le_trans (by norm_num) (le_max_left 1
        (Real.log (Fintype.card ι : ℝ))))
  nlinarith

/-- The upper bound in Theorem `thm:pos(iii)`: substituting
`tau = w / (4 S)` into the finite PL welfare expression gives
`w^2 /(2 S) * max {1, log(n-1)}`. -/
theorem matched_oneLeaderPLWelfare_premium_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base weight sensitivity : ℝ) (gap : ι → ℝ)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    (hgap : ∀ i, 0 ≤ gap i) :
    weight * base -
        oneLeaderPLWelfare base (matchedPLTemperature weight sensitivity)
          weight gap ≤
      weight ^ 2 / (2 * sensitivity) * plLogScale ι := by
  have htau : 0 < matchedPLTemperature weight sensitivity := by
    unfold matchedPLTemperature
    positivity
  have h := oneLeaderPLWelfare_premium_le_paper
    base (matchedPLTemperature weight sensitivity) weight gap
    htau hweight.le hgap
  calc
    weight * base -
        oneLeaderPLWelfare base (matchedPLTemperature weight sensitivity)
          weight gap ≤
        2 * weight * matchedPLTemperature weight sensitivity *
          plLogScale ι := h
    _ = weight ^ 2 / (2 * sensitivity) * plLogScale ι := by
      unfold matchedPLTemperature
      field_simp
      ring

/-- The exact finite-PL loss at the lower-bound witness: all `m` trailers are
tied `tau * log m` below the leader.  The total trailer PL mass is exactly
one half. -/
theorem tiedLogTrailers_PLWelfare_premium_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base tau weight : ℝ) (htau : tau ≠ 0) :
    weight * base -
        oneLeaderPLWelfare base tau weight
          (fun _ : ι => Real.log (Fintype.card ι : ℝ)) =
      weight * tau * Real.log (Fintype.card ι : ℝ) / 2 := by
  rw [oneLeaderPLWelfare_premium_eq base tau weight _ htau]
  have hmNat : 0 < Fintype.card ι := Fintype.card_pos
  have hm : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hmNat
  simp_rw [Real.exp_neg, Real.exp_log hm]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp
  ring

/-- The exact lower-bound witness after substituting the matched certificate:
`w^2 log(n-1)/(8S)`.  Since this is the loss of an explicit finite PL profile,
it supplies the paper's worst-case lower bound. -/
theorem matched_tiedLogTrailers_PLWelfare_premium_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base weight sensitivity : ℝ)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity) :
    weight * base -
        oneLeaderPLWelfare base (matchedPLTemperature weight sensitivity)
          weight (fun _ : ι => Real.log (Fintype.card ι : ℝ)) =
      weight ^ 2 * Real.log (Fintype.card ι : ℝ) /
        (8 * sensitivity) := by
  have htau : matchedPLTemperature weight sensitivity ≠ 0 := by
    apply ne_of_gt
    unfold matchedPLTemperature
    positivity
  rw [tiedLogTrailers_PLWelfare_premium_eq base
    (matchedPLTemperature weight sensitivity) weight htau]
  unfold matchedPLTemperature
  field_simp
  ring

/-- For at least two trailers, the explicit matched-certificate witness has
strictly positive welfare loss. -/
theorem matched_tiedLogTrailers_PLWelfare_premium_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (base weight sensitivity : ℝ)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    (hcard : 1 < Fintype.card ι) :
    0 < weight * base -
      oneLeaderPLWelfare base (matchedPLTemperature weight sensitivity)
        weight (fun _ : ι => Real.log (Fintype.card ι : ℝ)) := by
  rw [matched_tiedLogTrailers_PLWelfare_premium_eq
    base weight sensitivity hweight hsensitivity]
  have hcardReal : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  have hlog : 0 < Real.log (Fintype.card ι : ℝ) := Real.log_pos hcardReal
  positivity

end

end SmoothingCliff.Racing
