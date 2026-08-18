import SmoothingCliff.Racing.UniformLimit

/-!
# Continuity in the rate vector and the high-temperature limit

`UniformLimit.lean` computes the endpoint: at equal rates every agent's interim
allocation is the allocated priority mass over the number of agents.  This file
supplies the convergence to that endpoint, which is the remaining analytic step
of the high-temperature clause of Proposition `prop:revenue`.

The recursive Plackett--Luce mass is a finite composition of coordinate
projections, sums and one division whose denominator is positive, so it is
continuous in the rate vector wherever the rates are positive.  The
reserve-adjusted rates converge to a common value as the temperature grows, so
the interim allocations converge to their equal-rate value.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

open Filter Topology

noncomputable section

/-- Removing a chosen agent is continuous in the rate vector. -/
theorem continuous_removeChosenRate {n : ℕ} (first : Fin (n + 1)) :
    Continuous fun rate : Fin (n + 1) → ℝ => removeChosenRate rate first := by
  refine continuous_pi fun i => ?_
  exact continuous_apply _

/-- The recursive mass is continuous in the rate vector at every strictly
positive rate. -/
theorem plPermutationMass_continuousAt :
    ∀ (n : ℕ) (base : Fin n → ℝ), (∀ i, 0 < base i) →
      ∀ ranking : Equiv.Perm (Fin n),
        ContinuousAt (fun rate : Fin n → ℝ => plPermutationMass n rate ranking)
          base := by
  intro n
  induction n with
  | zero =>
    intro base _ ranking
    simpa [plPermutationMass] using continuousAt_const
  | succ m ih =>
    intro base hbase ranking
    have hsumpos : 0 < ∑ i, base i :=
      Finset.sum_pos (fun i _ => hbase i) Finset.univ_nonempty
    have hnum : ContinuousAt
        (fun rate : Fin (m + 1) → ℝ => rate (Equiv.Perm.decomposeFin ranking).1)
        base := (continuous_apply _).continuousAt
    have hden : ContinuousAt
        (fun rate : Fin (m + 1) → ℝ => ∑ i, rate i) base :=
      (continuous_finsetSum Finset.univ fun i _ => continuous_apply i).continuousAt
    have hratio : ContinuousAt
        (fun rate : Fin (m + 1) → ℝ =>
          rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i) base :=
      hnum.div hden (ne_of_gt hsumpos)
    have hremovepos : ∀ i,
        0 < removeChosenRate base (Equiv.Perm.decomposeFin ranking).1 i :=
      fun i => hbase _
    have hremove : ContinuousAt
        (fun rate : Fin (m + 1) → ℝ =>
          removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1) base :=
      (continuous_removeChosenRate
        (Equiv.Perm.decomposeFin ranking).1).continuousAt
    have hinner : ContinuousAt
        (fun rate : Fin (m + 1) → ℝ =>
          plPermutationMass m
            (removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1)
            (Equiv.Perm.decomposeFin ranking).2) base := by
      apply ContinuousAt.comp
        (g := fun r : Fin m → ℝ =>
          plPermutationMass m r (Equiv.Perm.decomposeFin ranking).2)
        (f := fun rate : Fin (m + 1) → ℝ =>
          removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1)
      · exact ih _ hremovepos _
      · exact hremove
    simpa [plPermutationMass] using hratio.mul hinner

/-- Interim allocation written directly on the rate vector. -/
def plRateInterim {n : ℕ} (rate : Fin n → ℝ) (weight : ℕ → ℝ)
    (agent : Fin n) : ℝ :=
  ∑ ranking : Equiv.Perm (Fin n),
    plPermutationMass n rate ranking * weight (ranking.symm agent)

theorem plRateInterim_eq {n : ℕ} (rate : Fin n → ℝ) (hrate : ∀ i, 0 < rate i)
    (weight : ℕ → ℝ) (agent : Fin n) :
    plRateInterim rate weight agent =
      rankingInterimPriority (plPermutationLaw n rate hrate) weight agent :=
  rfl

theorem plRateInterim_continuousAt {n : ℕ} {base : Fin n → ℝ}
    (hbase : ∀ i, 0 < base i) (weight : ℕ → ℝ) (agent : Fin n) :
    ContinuousAt (fun rate => plRateInterim rate weight agent) base := by
  unfold ContinuousAt plRateInterim
  exact tendsto_finsetSum Finset.univ fun ranking _ =>
    (plPermutationMass_continuousAt n base hbase ranking).mul continuousAt_const

/-- The reserve-adjusted rates converge to a common value as the temperature
grows. -/
theorem shiftedExponentialRate_tendsto_one {n : ℕ}
    (value : Fin n → ℝ) (reference : ℝ) :
    Tendsto (fun tau : ℝ => shiftedExponentialRate value reference tau)
      atTop (nhds fun _ => (1 : ℝ)) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hquot : Tendsto (fun tau : ℝ => (value i - reference) / tau) atTop
      (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hquot
  simpa [shiftedExponentialRate, Function.comp] using hexp

/-- **The high-temperature clause of `prop:revenue`, allocation half.**  As the
temperature grows each agent's interim allocation converges to the allocated
priority mass divided by the number of agents. -/
theorem plRateInterim_tendsto_uniform {n : ℕ}
    (value : Fin (n + 1) → ℝ) (reference : ℝ) (weight : ℕ → ℝ)
    (agent : Fin (n + 1)) :
    Tendsto (fun tau : ℝ =>
        plRateInterim (shiftedExponentialRate value reference tau) weight agent)
      atTop
      (nhds ((∑ position : Fin (n + 1), weight position) / (n + 1 : ℝ))) := by
  have hone : ∀ _i : Fin (n + 1), (0 : ℝ) < 1 := fun _ => one_pos
  have hcont := plRateInterim_continuousAt (base := fun _ : Fin (n + 1) => (1 : ℝ))
    hone weight agent
  have hlim := shiftedExponentialRate_tendsto_one value reference
  have hcomp := hcont.tendsto.comp hlim
  have hval : plRateInterim (fun _ : Fin (n + 1) => (1 : ℝ)) weight agent =
      (∑ position : Fin (n + 1), weight position) / (n + 1 : ℝ) := by
    rw [plRateInterim_eq _ hone]
    exact rankingInterimPriority_const_eq weight hone agent
  rw [hval] at hcomp
  exact hcomp

end

end SmoothingCliff.Racing
