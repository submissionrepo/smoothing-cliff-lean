import SmoothingCliff.Racing.RentDissipation
import SmoothingCliff.Racing.GeneralWelfareLoss
import SmoothingCliff.Racing.InterimBridge
import SmoothingCliff.Racing.PLPermutationLaw

/-!
# The general-`n` dominance condition

Formal target: Proposition `prop:netsurplus_n` in
`Smoothing_the_Cliff_ITCS.tex`.

The paper's temperature certificate for `n` agents is
`tau_dagger = (w1 / e) * max_i (v_i - r) / c_i'(0)`.  Above it every agent's
unique best response is zero investment, uniformly over opponents, so net
surplus under the PL rule is its allocative welfare and the smoothing loss of
`lem:welfareloss` bounds the shortfall from strict-priority welfare.  A
strict-priority racing outcome that burns more than that shortfall is strictly
dominated.

Opponents are held fixed inside each agent's response function, following the
convention of `RentDissipation.lean`, so the best-response statements below are
uniform over opponent profiles.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- The paper's general-`n` no-race temperature
`tau_dagger = (w1 / e) * max_i (v_i - r) / c_i'(0)`. -/
def generalCertificateTemperature {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight reserve : ℝ) (value marginalCostAtZero : ι → ℝ) : ℝ :=
  weight / Real.exp 1 *
    (Finset.univ.sup' Finset.univ_nonempty
      fun i => (value i - reserve) / marginalCostAtZero i)

/-- Above the general certificate, every single agent's displayed temperature
condition holds. -/
theorem agent_threshold_of_generalCertificate
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {weight reserve temperature : ℝ} {value marginalCostAtZero : ι → ℝ}
    (hWeight : 0 ≤ weight)
    (hCertificate :
      generalCertificateTemperature weight reserve value marginalCostAtZero ≤
        temperature)
    (i : ι) :
    weight / Real.exp 1 * ((value i - reserve) / marginalCostAtZero i) ≤
      temperature := by
  refine le_trans ?_ hCertificate
  have hfactor : 0 ≤ weight / Real.exp 1 :=
    div_nonneg hWeight (Real.exp_pos 1).le
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun j => (value j - reserve) / marginalCostAtZero j)
      (Finset.mem_univ i)) hfactor

/-- A profile of the race in which every coordinate is a best response against
the response function that agent faces. -/
def RaceProfileNash {ι : Type*}
    (response cost : ι → ℝ → ℝ) (reserve : ℝ) (value action : ι → ℝ) : Prop :=
  ∀ i, NonnegativeBestResponse
    (advantageUtility (response i) (cost i) reserve (value i)) (action i)

/-- Proposition `prop:netsurplus_n`, no-race half.  At or above the general
certificate temperature, the only equilibrium of the race under the PL rule is
zero investment by every agent. -/
theorem generalCertificate_raceNash_iff_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (response cost : ι → ℝ → ℝ) (weight temperature : NNReal)
    (hTemperature : 0 < temperature)
    {reserve : ℝ} {value action : ι → ℝ}
    (hMono : ∀ i, Monotone (response i))
    (hRange : ∀ i u, 0 ≤ response i u ∧ response i u ≤ (weight : ℝ))
    (hLip : ∀ i, LipschitzWith (plSensitivity weight temperature) (response i))
    (hValue : ∀ i, reserve ≤ value i)
    (hStrictConvex : ∀ i, StrictConvexOn ℝ (Set.Ici 0) (cost i))
    (hDifferentiable : ∀ i, ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ (cost i) a)
    (hMarginalCost : ∀ i, 0 < deriv (cost i) 0)
    (hCertificate :
      generalCertificateTemperature (weight : ℝ) reserve value
          (fun i => deriv (cost i) 0) ≤ (temperature : ℝ)) :
    RaceProfileNash response cost reserve value action ↔ ∀ i, action i = 0 := by
  constructor
  · intro hNash i
    refine (pl_bestResponse_iff_zero_of_temperature_ge (response i) (cost i)
      weight temperature hTemperature (hMono i) (hRange i) (hLip i)
      (hValue i) (hStrictConvex i) (hDifferentiable i) (hMarginalCost i)
      ?_).1 (hNash i)
    exact agent_threshold_of_generalCertificate (weight.coe_nonneg)
      hCertificate i
  · intro hZero i
    refine (pl_bestResponse_iff_zero_of_temperature_ge (response i) (cost i)
      weight temperature hTemperature (hMono i) (hRange i) (hLip i)
      (hValue i) (hStrictConvex i) (hDifferentiable i) (hMarginalCost i)
      ?_).2 (hZero i)
    exact agent_threshold_of_generalCertificate (weight.coe_nonneg)
      hCertificate i

/-- Proposition `prop:netsurplus_n`, dominance half.  At zero investment the
PL rule's net surplus is its allocative welfare, so a strict-priority outcome
burning more than the certified smoothing shortfall is strictly dominated. -/
theorem strictPriority_dominated_of_dissipation_gt_loss
    {strictPriorityWelfare plWelfare strictPriorityNetSurplus
      smoothingShortfall dissipation : ℝ}
    (hLoss : strictPriorityWelfare - plWelfare ≤ smoothingShortfall)
    (hStrictPriority :
      strictPriorityNetSurplus ≤ strictPriorityWelfare - dissipation)
    (hDominance : smoothingShortfall < dissipation) :
    strictPriorityNetSurplus < plWelfare := by
  linarith

/-- The displayed form of the dominance threshold at `tau_dagger`: the paper's
`binom(n,2) * barDrop * w1 / e^2 * max_i (v_i - r) / c_i'(0)` is exactly the
smoothing shortfall evaluated at the general certificate temperature. -/
theorem generalCertificate_shortfall_eq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (weight reserve : ℝ) (value marginalCostAtZero : ι → ℝ)
    (barDrop pairs : ℝ) :
    barDrop * (pairs *
        (generalCertificateTemperature weight reserve value marginalCostAtZero
          / Real.exp 1)) =
      barDrop * pairs * (weight / (Real.exp 1 * Real.exp 1)) *
        (Finset.univ.sup' Finset.univ_nonempty
          fun i => (value i - reserve) / marginalCostAtZero i) := by
  rw [generalCertificateTemperature]
  field_simp

/-! ### The proposition end to end

With the ranking-law/interim bridge in place, the smoothing shortfall of
`lem:welfareloss` and the racing clauses can be stated about the same object.
At zero investment the PL rule's net surplus is its allocative welfare, which
the bridge writes as the sum over agents of value times interim allocation, so
the dominance conclusion of `prop:netsurplus_n` becomes a single statement. -/

/-- The smoothing shortfall of `lem:welfareloss`, written against the interim
allocations rather than against the ranking law. -/
theorem interimWelfare_shortfall_le
    (n : ℕ) (law : FiniteLaw (Equiv.Perm (Fin n)))
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Equiv.Perm (Fin n) → Fin (n.choose 2) → Prop)
    [∀ ranking pair, Decidable (inverted ranking pair)]
    (hdecomp : ∀ ranking,
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair, gap pair * eventIndicator (inverted ranking pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun ranking => inverted ranking pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau) :
    strictPriorityWelfare weight (List.ofFn value) -
        ∑ agent : Fin n,
          value agent * rankingInterimPriority law weight agent ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  have hbounds := permutationLaw_generalTopK_welfare_loss_bounds n law weight
    slots barDrop tau hweight value gap inverted hdecomp hpairLaw hgap htau
  simp only at hbounds
  have hchain := le_trans hbounds.2.1 hbounds.2.2
  rwa [finiteExpectation_rankingWelfare_eq_interimWelfare] at hchain

/-- **Proposition `prop:netsurplus_n`, dominance clause, end to end.**  At a
temperature at or above the general certificate every agent invests zero, so
the PL rule's net surplus is the interim allocative welfare; a strict-priority
racing outcome burning more than the certified smoothing shortfall is then
strictly dominated. -/
theorem generalCertificate_netSurplus_dominates_strictPriority
    (n : ℕ) (law : FiniteLaw (Equiv.Perm (Fin n)))
    (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ) (gap : Fin (n.choose 2) → ℝ)
    (inverted : Equiv.Perm (Fin n) → Fin (n.choose 2) → Prop)
    [∀ ranking pair, Decidable (inverted ranking pair)]
    (hdecomp : ∀ ranking,
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair, gap pair * eventIndicator (inverted ranking pair))
    (hpairLaw : ∀ pair,
      finiteProbability law (fun ranking => inverted ranking pair) =
        finiteProbability (exponentialRacePairLaw (gap pair) 0 tau)
          (fun lowerFirst => lowerFirst = true))
    (hgap : ∀ pair, 0 ≤ gap pair) (htau : 0 < tau)
    {strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriority : strictPriorityNetSurplus ≤
      strictPriorityWelfare weight (List.ofFn value) - dissipation)
    (hDominance :
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) < dissipation) :
    strictPriorityNetSurplus <
      ∑ agent : Fin n, value agent * rankingInterimPriority law weight agent :=
  strictPriority_dominated_of_dissipation_gt_loss
    (interimWelfare_shortfall_le n law weight slots barDrop tau hweight value
      gap inverted hdecomp hpairLaw hgap htau)
    hStrictPriority hDominance


/-- The same statement at the genuine Plackett--Luce law: the interim
allocations are those of the exponential-score rule at temperature `tau`, and
the certified smoothing shortfall bounds the gap to strict-priority welfare. -/
theorem plLaw_interimWelfare_shortfall_le
    (n : ℕ) (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau reference : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ)
    (low high : Fin (n.choose 2) → Fin n)
    (hdistinct : ∀ pair, low pair ≠ high pair)
    (hvalueOrder : ∀ pair, value (low pair) < value (high pair))
    (hdecomp : ∀ ranking : Equiv.Perm (Fin n),
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair,
          (value (high pair) - value (low pair)) *
            eventIndicator
              (permutationBefore ranking (low pair) (high pair)))
    (htau : 0 < tau) :
    strictPriorityWelfare weight (List.ofFn value) -
        ∑ agent : Fin n,
          value agent *
            rankingInterimPriority
              (plPermutationLaw n (shiftedExponentialRate value reference tau)
                (shiftedExponentialRate_positive value reference tau))
              weight agent ≤
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) := by
  have hbounds := shiftedExponential_PL_generalTopK_welfare_loss_bounds n
    weight slots barDrop tau reference hweight value low high hdistinct
    hvalueOrder hdecomp htau
  simp only at hbounds
  have hchain := le_trans hbounds.2.1 hbounds.2.2
  rwa [finiteExpectation_rankingWelfare_eq_interimWelfare] at hchain

/-- **Proposition `prop:netsurplus_n`, dominance clause at the PL rule.**
Combining the certificate, the bridge and the smoothing shortfall, a
strict-priority racing outcome that burns more than the certified shortfall is
strictly dominated by the PL rule's interim allocative welfare. -/
theorem plLaw_netSurplus_dominates_strictPriority
    (n : ℕ) (weight : ℕ → ℝ) (slots : ℕ) (barDrop tau reference : ℝ)
    (hweight : ExtendedSlotWeights weight slots barDrop)
    (value : Fin n → ℝ)
    (low high : Fin (n.choose 2) → Fin n)
    (hdistinct : ∀ pair, low pair ≠ high pair)
    (hvalueOrder : ∀ pair, value (low pair) < value (high pair))
    (hdecomp : ∀ ranking : Equiv.Perm (Fin n),
      inversionGap (permutationRankingValues n value ranking) =
        ∑ pair,
          (value (high pair) - value (low pair)) *
            eventIndicator
              (permutationBefore ranking (low pair) (high pair)))
    (htau : 0 < tau)
    {strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriority : strictPriorityNetSurplus ≤
      strictPriorityWelfare weight (List.ofFn value) - dissipation)
    (hDominance :
      barDrop * ((n.choose 2 : ℝ) * (tau / Real.exp 1)) < dissipation) :
    strictPriorityNetSurplus <
      ∑ agent : Fin n,
        value agent *
          rankingInterimPriority
            (plPermutationLaw n (shiftedExponentialRate value reference tau)
              (shiftedExponentialRate_positive value reference tau))
            weight agent :=
  strictPriority_dominated_of_dissipation_gt_loss
    (plLaw_interimWelfare_shortfall_le n weight slots barDrop tau reference
      hweight value low high hdistinct hvalueOrder hdecomp htau)
    hStrictPriority hDominance


end

end SmoothingCliff.Racing
