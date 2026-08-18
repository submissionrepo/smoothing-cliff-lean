import SmoothingCliff.Basic
import SmoothingCliff.Mechanism.Intensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Rank and interim monotonicity of the PL exponential race

This file formalizes Lemmas `lem:rank_monotonicity` and
`lem:interim_monotonicity` from *Smoothing the Cliff*.  Agents receive a real
arrival key and are ranked by increasing key, with the fixed linear order on
agents breaking the probability-zero ties.  Thus `raceRank` is a genuine
zero-based finite rank, rather than an assumed coupling conclusion.

For the Plackett--Luce race, a common nonnegative shock `E_j` produces the key
`E_j / exp ((b_j - reserve) / temperature)`.  Raising one bid only lowers that
agent's key.  We prove the resulting pathwise rank and realized-allocation
inequalities, first-order stochastic dominance under an arbitrary probability
law for the common shocks, and the Bochner-integral bridge to interim expected
priority.  The standard iid `Exp(1)` law is a specialization of this law-free
common-shock argument.
-/

namespace SmoothingCliff.Mechanism

/-- Agent `j` arrives before `i`; the agent order is a deterministic tie-break. -/
def ArrivesBefore {ι : Type*} [LinearOrder ι]
    (key : ι → ℝ) (j i : ι) : Prop :=
  key j < key i ∨ (key j = key i ∧ j < i)

/-- Zero-based rank in a finite race.  Rank zero is first. -/
noncomputable def raceRank {ι : Type*} [Fintype ι] [LinearOrder ι]
    (key : ι → ℝ) (i : ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => ArrivesBefore key j i).card

/-- If only agent `i`'s arrival key falls, her finite realized rank cannot get
worse.  This is the deterministic combinatorial core of the common-key
coupling. -/
theorem raceRank_mono_own
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (oldKey newKey : ι → ℝ) (i : ι)
    (hOwn : newKey i ≤ oldKey i)
    (hOther : ∀ j, j ≠ i → newKey j = oldKey j) :
    raceRank newKey i ≤ raceRank oldKey i := by
  classical
  unfold raceRank
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  by_cases hji : j = i
  · subst j
    simp [ArrivesBefore] at hj
  · have hjkey := hOther j hji
    rcases hj with hlt | ⟨heq, hjlt⟩
    · left
      calc
        oldKey j = newKey j := hjkey.symm
        _ < newKey i := hlt
        _ ≤ oldKey i := hOwn
    · have hle : oldKey j ≤ oldKey i := by
        calc
          oldKey j = newKey j := hjkey.symm
          _ = newKey i := heq
          _ ≤ oldKey i := hOwn
      rcases hle.eq_or_lt with hEq | hLt
      · exact Or.inr ⟨hEq, hjlt⟩
      · exact Or.inl hLt

/-- Arrival key in the common `Exp(1)` representation of a PL race. -/
noncomputable def exponentialRaceKey {ι : Type*}
    (reserve temperature : ℝ) (shock bids : ι → ℝ) (j : ι) : ℝ :=
  shock j / luceIntensity reserve temperature (bids j)

/-- With a common nonnegative exponential shock, increasing intensity lowers
the arrival key. -/
theorem exponentialRaceKey_own_mono
    (reserve temperature shock a b : ℝ)
    (hShock : 0 ≤ shock) (hTemperature : 0 < temperature)
    (hab : a ≤ b) :
    shock / luceIntensity reserve temperature b ≤
      shock / luceIntensity reserve temperature a := by
  exact div_le_div_of_nonneg_left hShock (luceIntensity_pos _ _ _)
    (luceIntensity_mono reserve temperature a b hTemperature hab)

/-- Pathwise form of Lemma `lem:rank_monotonicity`.  Both reports inhabit the
eligible half-line; all opponents and all common shocks are held fixed. -/
theorem plRankMonotonicityPathwise
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (temperature : ℝ)
    (shock bids : ι → ℝ) (i : ι)
    (z z' : EligibleBid reserve)
    (hShock : 0 ≤ shock i)
    (hTemperature : 0 < temperature) (hzz' : z ≤ z') :
    raceRank
        (exponentialRaceKey reserve temperature shock
          (Function.update bids i (z' : ℝ))) i ≤
      raceRank
        (exponentialRaceKey reserve temperature shock
          (Function.update bids i (z : ℝ))) i := by
  apply raceRank_mono_own _ _ i
  · simp only [exponentialRaceKey, Function.update_self]
    exact exponentialRaceKey_own_mono reserve temperature (shock i)
      (z : ℝ) (z' : ℝ) hShock hTemperature hzz'
  · intro j hji
    simp only [exponentialRaceKey]
    rw [Function.update_of_ne hji, Function.update_of_ne hji]

/-- First-order stochastic improvement for ranks, where a smaller rank is
better.  At every cutoff, the improved rank has at least as much probability
mass in the top ranks. -/
def RankFOSD {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (better worse : Ω → ℕ) : Prop :=
  ∀ cutoff, μ {ω | worse ω ≤ cutoff} ≤ μ {ω | better ω ≤ cutoff}

theorem rankFOSD_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (better worse : Ω → ℕ)
    (hRank : ∀ ω, better ω ≤ worse ω) :
    RankFOSD μ better worse := by
  intro cutoff
  apply MeasureTheory.measure_mono
  intro ω hω
  exact (hRank ω).trans hω

/-- Probability-law version of Lemma `lem:rank_monotonicity`.  The proof uses
the explicit common-shock race above, and not stochastic dominance as an
assumption. -/
theorem plRankFirstOrderDominance
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (temperature : ℝ) (shock : Ω → ι → ℝ)
    (bids : ι → ℝ) (i : ι)
    (hShock : ∀ ω, 0 ≤ shock ω i)
    (hTemperature : 0 < temperature)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    RankFOSD μ
      (fun ω => raceRank
        (exponentialRaceKey reserve temperature (shock ω)
          (Function.update bids i (z' : ℝ))) i)
      (fun ω => raceRank
        (exponentialRaceKey reserve temperature (shock ω)
          (Function.update bids i (z : ℝ))) i) := by
  apply rankFOSD_of_pointwise
  intro ω
  exact plRankMonotonicityPathwise temperature (shock ω) bids i z z'
    (hShock ω) hTemperature hzz'

/-- Priority weight at a zero-based rank.  Ranks outside the first `slots`
positions receive zero. -/
def priorityAtRank
    (slotWeight : ℕ → ℝ) (slots rank : ℕ) : ℝ :=
  if rank < slots then slotWeight rank else 0

/-- Extending nonnegative, nonincreasing slot weights by zero preserves the
order: a better rank gets weakly more realized priority. -/
theorem priorityAtRank_antitone
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k) :
    Antitone (priorityAtRank slotWeight slots) := by
  intro better worse hbw
  unfold priorityAtRank
  by_cases hw : worse < slots
  · have hb : better < slots := lt_of_le_of_lt hbw hw
    simp only [if_pos hb, if_pos hw]
    exact hWeight hbw
  · simp only [if_neg hw]
    by_cases hb : better < slots
    · simp only [if_pos hb]
      exact hNonneg better
    · simp [hb]

theorem priorityAtRank_bounds
    (slotWeight : ℕ → ℝ) (slots rank : ℕ)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k) :
    priorityAtRank slotWeight slots rank ∈ Set.Icc 0 (slotWeight 0) := by
  unfold priorityAtRank
  split
  · exact ⟨hNonneg rank, hWeight (Nat.zero_le rank)⟩
  · exact ⟨le_rfl, hNonneg 0⟩

/-- Realized priority in the common-shock PL race at an eligible own bid. -/
noncomputable def plEligibleRealizedPriority
    {Ω ι : Type*} [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (temperature : ℝ)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (bid : EligibleBid reserve) (ω : Ω) : ℝ :=
  priorityAtRank slotWeight slots
    (raceRank
      (exponentialRaceKey reserve temperature (shock ω)
        (Function.update bids i (bid : ℝ))) i)

/-- Nonincreasing slot weights turn pathwise rank improvement into pathwise
realized-allocation improvement. -/
theorem plRealizedPriority_mono
    {Ω ι : Type*} [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (temperature : ℝ)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (hShock : ∀ ω, 0 ≤ shock ω i)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    ∀ ω,
      plEligibleRealizedPriority temperature slotWeight slots
          shock bids i z ω ≤
        plEligibleRealizedPriority temperature slotWeight slots
          shock bids i z' ω := by
  intro ω
  exact priorityAtRank_antitone slotWeight slots hWeight hNonneg
    (plRankMonotonicityPathwise temperature (shock ω) bids i z z'
      (hShock ω) hTemperature hzz')

theorem plEligibleRealizedPriority_bounds
    {Ω ι : Type*} [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (temperature : ℝ)
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k)
    (bid : EligibleBid reserve) (ω : Ω) :
    plEligibleRealizedPriority temperature slotWeight slots
        shock bids i bid ω ∈ Set.Icc 0 (slotWeight 0) :=
  priorityAtRank_bounds slotWeight slots _ hWeight hNonneg

/-- Interim expected priority is the Bochner expectation of the realized
finite-rank allocation. -/
noncomputable def plEligibleInterimPriority
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (μ : MeasureTheory.Measure Ω)
    (temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (bid : EligibleBid reserve) : ℝ :=
  ∫ ω, plEligibleRealizedPriority temperature slotWeight slots
    shock bids i bid ω ∂μ

theorem plEligibleRealizedPriority_integrable
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k)
    (bid : EligibleBid reserve)
    (hMeasurable : AEMeasurable
      (plEligibleRealizedPriority temperature slotWeight slots
        shock bids i bid) μ) :
    MeasureTheory.Integrable
      (plEligibleRealizedPriority temperature slotWeight slots
        shock bids i bid) μ := by
  apply MeasureTheory.Integrable.of_mem_Icc 0 (slotWeight 0) hMeasurable
  filter_upwards with ω
  exact plEligibleRealizedPriority_bounds temperature slotWeight slots
    shock bids i hWeight hNonneg bid ω

/-- Eligible-region expectation bridge for Lemma
`lem:interim_monotonicity`.  Almost-everywhere measurability is the only
technical probability premise; boundedness and integrability follow from the
finite nonnegative slot weights. -/
theorem plEligibleInterimPriority_mono
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    {reserve : ℝ} (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (hShock : ∀ ω, 0 ≤ shock ω i)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k)
    (hMeasurable : ∀ bid : EligibleBid reserve,
      AEMeasurable
        (plEligibleRealizedPriority temperature slotWeight slots
          shock bids i bid) μ)
    (z z' : EligibleBid reserve) (hzz' : z ≤ z') :
    plEligibleInterimPriority μ temperature slotWeight slots
        shock bids i z ≤
      plEligibleInterimPriority μ temperature slotWeight slots
        shock bids i z' := by
  apply MeasureTheory.integral_mono
    (plEligibleRealizedPriority_integrable μ temperature slotWeight slots
      shock bids i hWeight hNonneg z (hMeasurable z))
    (plEligibleRealizedPriority_integrable μ temperature slotWeight slots
      shock bids i hWeight hNonneg z' (hMeasurable z'))
  exact plRealizedPriority_mono temperature slotWeight slots shock bids i
    hShock hTemperature hWeight hNonneg z z' hzz'

/-- Reserve screening: below the reserve allocation is zero; on the eligible
half-line it is the expected PL priority just defined. -/
noncomputable def plInterimPriority
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    (μ : MeasureTheory.Measure Ω)
    (reserve temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (bid : ℝ) : ℝ :=
  if h : reserve ≤ bid then
    plEligibleInterimPriority μ temperature slotWeight slots
      shock bids i ⟨bid, h⟩
  else 0

/-- Strictly below the reserve, interim allocation is identically zero. -/
theorem plInterimPriority_of_lt_reserve
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    (μ : MeasureTheory.Measure Ω)
    (reserve temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (bid : ℝ) (hBid : bid < reserve) :
    plInterimPriority μ reserve temperature slotWeight slots
      shock bids i bid = 0 := by
  simp [plInterimPriority, not_le.mpr hBid]

/-- Full form of Lemma `lem:interim_monotonicity`: for fixed opponents and a
common probability law for the shocks, reserve-screened expected priority is
nondecreasing in the own bid and vanishes below the reserve. -/
theorem plInterimPriority_monotone
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι]
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (reserve temperature : ℝ) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (shock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (hShock : ∀ ω, 0 ≤ shock ω i)
    (hTemperature : 0 < temperature)
    (hWeight : Antitone slotWeight)
    (hNonneg : ∀ k, 0 ≤ slotWeight k)
    (hMeasurable : ∀ bid : EligibleBid reserve,
      AEMeasurable
        (plEligibleRealizedPriority temperature slotWeight slots
          shock bids i bid) μ) :
    Monotone
      (plInterimPriority μ reserve temperature slotWeight slots
        shock bids i) := by
  intro a b hab
  by_cases ha : reserve ≤ a
  · have hb : reserve ≤ b := ha.trans hab
    simp only [plInterimPriority, dif_pos ha, dif_pos hb]
    exact plEligibleInterimPriority_mono μ temperature slotWeight slots
      shock bids i hShock hTemperature hWeight hNonneg hMeasurable
      ⟨a, ha⟩ ⟨b, hb⟩ hab
  · simp only [plInterimPriority, dif_neg ha]
    by_cases hb : reserve ≤ b
    · simp only [dif_pos hb]
      apply MeasureTheory.integral_nonneg
      intro ω
      exact (plEligibleRealizedPriority_bounds temperature slotWeight slots
        shock bids i hWeight hNonneg ⟨b, hb⟩ ω).1
    · simp [hb]

end SmoothingCliff.Mechanism
