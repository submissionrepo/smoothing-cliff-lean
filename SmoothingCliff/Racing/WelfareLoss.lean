import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# One-slot Plackett--Luce welfare loss

This file formalizes the analytic inequality and the one-slot specialization of
Lemma `lem:welfareloss`.  It derives the welfare-gap identity from the exact
finite Plackett--Luce probabilities and then proves the paper's sharper
`(n - 1) w₁ τ / e` bound.  The adjacent-inversion argument needed for the
general multi-slot pairwise bound is deliberately kept separate.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- One-slot PL choice probability with scores `value / tau`. -/
def oneSlotPLProbability {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau : ℝ) (i : ι) : ℝ :=
  Real.exp (value i / tau) / ∑ j ∈ s, Real.exp (value j / tau)

/-- Expected one-slot PL welfare. -/
def oneSlotPLWelfare {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau weight : ℝ) : ℝ :=
  weight * ∑ i ∈ s, value i * oneSlotPLProbability s value tau i

theorem sum_oneSlotPLProbability_eq_one
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau : ℝ) (hs : s.Nonempty) :
    ∑ i ∈ s, oneSlotPLProbability s value tau i = 1 := by
  have hdenpos : 0 < ∑ j ∈ s, Real.exp (value j / tau) := by
    rcases hs with ⟨j, hj⟩
    exact Finset.sum_pos' (fun k _ => (Real.exp_pos _).le)
      ⟨j, hj, Real.exp_pos _⟩
  simp only [oneSlotPLProbability]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hdenpos)

/-- Strict-priority welfare minus PL welfare is the probability-weighted sum
of gaps from a highest-valued agent. -/
theorem oneSlot_welfare_gap_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau weight : ℝ) (top : ι)
    (hs : s.Nonempty) :
    weight * value top - oneSlotPLWelfare s value tau weight =
      weight * ∑ i ∈ s,
        (value top - value i) * oneSlotPLProbability s value tau i := by
  have hprob := sum_oneSlotPLProbability_eq_one s value tau hs
  have hin :
      value top -
          ∑ i ∈ s, value i * oneSlotPLProbability s value tau i =
        ∑ i ∈ s,
          (value top - value i) * oneSlotPLProbability s value tau i := by
    calc
      value top - ∑ i ∈ s,
          value i * oneSlotPLProbability s value tau i =
          value top * (∑ i ∈ s, oneSlotPLProbability s value tau i) -
            ∑ i ∈ s,
              value i * oneSlotPLProbability s value tau i := by
        rw [hprob]
        ring
      _ = (∑ i ∈ s,
            value top * oneSlotPLProbability s value tau i) -
            ∑ i ∈ s,
              value i * oneSlotPLProbability s value tau i := by
        rw [Finset.mul_sum]
      _ = ∑ i ∈ s,
            (value top * oneSlotPLProbability s value tau i -
              value i * oneSlotPLProbability s value tau i) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ s,
            (value top - value i) * oneSlotPLProbability s value tau i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  unfold oneSlotPLWelfare
  rw [← mul_sub, hin]

/-- The elementary maximum `x exp(-x) ≤ 1/e`. -/
theorem mul_exp_neg_le_inv_exp_one (x : ℝ) :
    x * Real.exp (-x) ≤ 1 / Real.exp 1 := by
  rw [Real.exp_neg]
  change x / Real.exp x ≤ 1 / Real.exp 1
  apply (div_le_div_iff₀ (Real.exp_pos x) (Real.exp_pos 1)).2
  simpa [mul_comm] using (Real.exp_one_mul_le_exp (x := x))

/-- The paper's per-pair analytic estimate
`delta * sigmoid (-delta/tau) ≤ tau/e`. -/
theorem gap_mul_sigmoid_le_tau_div_exp_one
    (delta tau : ℝ) (hdelta : 0 ≤ delta) (htau : 0 < tau) :
    delta * Real.sigmoid (-delta / tau) ≤ tau / Real.exp 1 := by
  have hx : 0 ≤ delta / tau := div_nonneg hdelta htau.le
  have hse :
      Real.sigmoid (delta / tau) * Real.exp (-(delta / tau)) ≤
        1 * Real.exp (-(delta / tau)) :=
    mul_le_mul_of_nonneg_right (Real.sigmoid_le_one _)
      (Real.exp_pos _).le
  have hm :
      delta / tau * Real.sigmoid (-(delta / tau)) ≤
        1 / Real.exp 1 := by
    calc
      delta / tau * Real.sigmoid (-(delta / tau)) =
          delta / tau *
            (Real.sigmoid (delta / tau) * Real.exp (-(delta / tau))) := by
        rw [Real.sigmoid_mul_rexp_neg]
      _ ≤ delta / tau * (1 * Real.exp (-(delta / tau))) :=
        mul_le_mul_of_nonneg_left hse hx
      _ = delta / tau * Real.exp (-(delta / tau)) := by ring
      _ ≤ 1 / Real.exp 1 := mul_exp_neg_le_inv_exp_one _
  calc
    delta * Real.sigmoid (-delta / tau) =
        tau * ((delta / tau) * Real.sigmoid (-delta / tau)) := by
      field_simp [ne_of_gt htau]
    _ ≤ tau * (1 / Real.exp 1) := by
      apply mul_le_mul_of_nonneg_left _ htau.le
      simpa only [neg_div] using hm
    _ = tau / Real.exp 1 := by ring

theorem oneSlotPLProbability_le_exp_neg_gap
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau : ℝ) (top i : ι)
    (htopmem : top ∈ s) :
    oneSlotPLProbability s value tau i ≤
      Real.exp (-(value top - value i) / tau) := by
  have hsum :
      Real.exp (value top / tau) ≤
        ∑ j ∈ s, Real.exp (value j / tau) := by
    exact Finset.single_le_sum
      (f := fun j => Real.exp (value j / tau))
      (fun j _ => (Real.exp_pos _).le) htopmem
  unfold oneSlotPLProbability
  calc
    Real.exp (value i / tau) /
        ∑ j ∈ s, Real.exp (value j / tau) ≤
        Real.exp (value i / tau) / Real.exp (value top / tau) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le
        (Real.exp_pos _) hsum
    _ = Real.exp (-(value top - value i) / tau) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- One-slot part of Lemma `lem:welfareloss`.  The natural-number expression
`s.card - 1` is coerced as a unit, avoiding a real-valued truncated-subtraction
ambiguity. -/
theorem oneSlot_pl_welfare_loss_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (value : ι → ℝ) (tau weight : ℝ) (top : ι)
    (hs : s.Nonempty) (htopmem : top ∈ s)
    (htop : ∀ i ∈ s, value i ≤ value top)
    (htau : 0 < tau) (hweight : 0 ≤ weight) :
    weight * value top - oneSlotPLWelfare s value tau weight ≤
      (s.card - 1 : ℕ) * (weight * tau / Real.exp 1) := by
  rw [oneSlot_welfare_gap_identity s value tau weight top hs]
  have hterm : ∀ i ∈ s,
      weight * ((value top - value i) *
          oneSlotPLProbability s value tau i) ≤
        weight * tau / Real.exp 1 := by
    intro i hi
    have hgap : 0 ≤ value top - value i := sub_nonneg.mpr (htop i hi)
    have hp := oneSlotPLProbability_le_exp_neg_gap
      s value tau top i htopmem
    have hmul :
        (value top - value i) * oneSlotPLProbability s value tau i ≤
          (value top - value i) *
            Real.exp (-(value top - value i) / tau) :=
      mul_le_mul_of_nonneg_left hp hgap
    have hx :
        (value top - value i) *
            Real.exp (-(value top - value i) / tau) ≤
          tau / Real.exp 1 := by
      let x := (value top - value i) / tau
      have hm := mul_exp_neg_le_inv_exp_one x
      have hscaled := mul_le_mul_of_nonneg_left hm htau.le
      dsimp [x] at hscaled
      have heq :
          tau * (((value top - value i) / tau) *
            Real.exp (-((value top - value i) / tau))) =
            (value top - value i) *
              Real.exp (-(value top - value i) / tau) := by
        field_simp [ne_of_gt htau]
      rw [heq] at hscaled
      calc
        (value top - value i) *
            Real.exp (-(value top - value i) / tau) ≤
            tau * (1 / Real.exp 1) := by
          simpa only [neg_div] using hscaled
        _ = tau / Real.exp 1 := by ring
    have hw := mul_le_mul_of_nonneg_left (hmul.trans hx) hweight
    simpa [mul_div_assoc] using hw
  have herase :
      ∑ i ∈ s.erase top,
          weight * ((value top - value i) *
            oneSlotPLProbability s value tau i) ≤
        ∑ _i ∈ s.erase top, weight * tau / Real.exp 1 :=
    Finset.sum_le_sum fun i hi => hterm i (Finset.mem_of_mem_erase hi)
  calc
    weight * ∑ i ∈ s,
        (value top - value i) * oneSlotPLProbability s value tau i =
        ∑ i ∈ s.erase top,
          weight * ((value top - value i) *
            oneSlotPLProbability s value tau i) := by
      rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ htopmem]
      simp
    _ ≤ ∑ _i ∈ s.erase top, weight * tau / Real.exp 1 := herase
    _ = (s.card - 1 : ℕ) * (weight * tau / Real.exp 1) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem htopmem]

end

end SmoothingCliff.Racing
