import SmoothingCliff.Mechanism.RealizedPriorityBridge

/-!
# Comparing the two interim allocations on a product space

The final step of Theorem `thm:stability`.  All mathematical content is already
credentialed: away from ties the two realized priorities agree at every sample
point.  What is left is to compare the two integrals, which needs the own
coordinate to be independent of the opponents'.

The measure is therefore an opponent law times a unit exponential own
coordinate, and the shock family writes that coordinate into the bidder's slot.
The one piece of friction is that the order-statistic record carries a
nonnegativity proof: the pointwise identity produces the record built from the
full key vector, while the stability side uses the record built from the
opponents alone.  A congruence lemma removes it, since the record has a single
data field and the sorted opponent list never reads the bidder's own
coordinate.
-/

namespace SmoothingCliff.Mechanism

open MeasureTheory ProbabilityTheory Finset

/-- Two order-statistic records with the same thresholds are equal: the
remaining fields are proofs. -/
theorem ConditionedOpponentOrderStats.ext_threshold
    {first second : ConditionedOpponentOrderStats}
    (h : first.threshold = second.threshold) : first = second := by
  cases first
  cases second
  simp only at h
  subst h
  rfl

/-- The sorted opponent list never reads the bidder's own coordinate. -/
theorem sortedOpponentKeys_congr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {key keyAlt : ι → ℝ} {i : ι}
    (hAgree : ∀ j, j ≠ i → key j = keyAlt j) :
    sortedOpponentKeys key i = sortedOpponentKeys keyAlt i := by
  classical
  rw [sortedOpponentKeys, sortedOpponentKeys]
  congr 1
  refine Multiset.map_congr rfl fun j hj => ?_
  exact hAgree j (Finset.mem_erase.mp hj).1

/-- **The congruence lemma.**  Order-statistic records built from key vectors
agreeing off the bidder's own coordinate are equal, whatever nonnegativity
proofs they carry. -/
theorem opponentOrderStats_congr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {key keyAlt : ι → ℝ} {i : ι}
    (hKey : ∀ j, j ≠ i → 0 ≤ key j) (hKeyAlt : ∀ j, j ≠ i → 0 ≤ keyAlt j)
    (hAgree : ∀ j, j ≠ i → key j = keyAlt j) :
    opponentOrderStats key i hKey = opponentOrderStats keyAlt i hKeyAlt := by
  refine ConditionedOpponentOrderStats.ext_threshold ?_
  funext p
  rw [opponentOrderStats, opponentOrderStats,
    ConditionedOpponentOrderStats.ofSortedList_threshold,
    ConditionedOpponentOrderStats.ofSortedList_threshold]
  simp only [sortedOpponentKeys_congr hAgree]

/-- Writing the own coordinate of a product point into the bidder's slot. -/
def productShock {Ω ι : Type*} [DecidableEq ι]
    (opponentShock : Ω → ι → ℝ) (i : ι) : Ω × ℝ → ι → ℝ :=
  fun point => Function.update (opponentShock point.1) i point.2

@[simp] theorem productShock_self {Ω ι : Type*} [DecidableEq ι]
    (opponentShock : Ω → ι → ℝ) (i : ι) (point : Ω × ℝ) :
    productShock opponentShock i point i = point.2 := by
  simp [productShock]

theorem productShock_of_ne {Ω ι : Type*} [DecidableEq ι]
    (opponentShock : Ω → ι → ℝ) (i : ι) (point : Ω × ℝ) {j : ι} (hj : j ≠ i) :
    productShock opponentShock i point j = opponentShock point.1 j := by
  simp [productShock, Function.update_of_ne hj]

/-- The tie set is null for an arbitrary finite opponent index. -/
theorem eventually_no_tie_fintype
    {ι : Type*} [Fintype ι] (rate scale : ℝ) (hScale : scale ≠ 0)
    (threshold : ι → ℝ) :
    ∀ᵐ ownShock ∂(expMeasure rate), ∀ j : ι, ownShock / scale ≠ threshold j := by
  classical
  have hnull : expMeasure rate
      {ownShock : ℝ | ∃ j : ι, ownShock = scale * threshold j} = 0 := by
    refine measure_mono_null ?_
      (expMeasure_finset_null rate
        (Finset.image (fun j => scale * threshold j) Finset.univ))
    rintro x ⟨j, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hx
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, ?_⟩
  field_simp at hj
  linarith [hj]

end SmoothingCliff.Mechanism

namespace SmoothingCliff.Mechanism

open MeasureTheory ProbabilityTheory

/-- **Theorem `thm:stability`, representation identity.**  With the own
coordinate independent of the opponents', the rank-based interim allocation of
the monotonicity development equals the conditioned interim allocation that
carries the stability bounds. -/
theorem plEligibleInterimPriority_prod_eq_finiteRace
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    {reserve temperature : ℝ}
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (opponentShock : Ω → ι → ℝ) (bids : ι → ℝ) (i : ι)
    (bid : EligibleBid reserve) (slotWeight : ℕ → ℝ) (slots : ℕ)
    (hShock : ∀ ω j, j ≠ i → 0 ≤ opponentShock ω j)
    (hIntegrable : Integrable
      (fun point : Ω × ℝ =>
        plEligibleRealizedPriority temperature slotWeight slots
          (productShock opponentShock i) bids i bid point)
      (ν.prod (expMeasure 1))) :
    plEligibleInterimPriority (ν.prod (expMeasure 1)) temperature slotWeight
        slots (productShock opponentShock i) bids i bid =
      finiteRaceInterimPriority ν slotWeight slots
        (plOpponentOrderStats reserve temperature opponentShock bids i hShock)
        reserve temperature (bid : ℝ) := by
  classical
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hIntensity : (0 : ℝ) < luceIntensity reserve temperature (bid : ℝ) :=
    luceIntensity_pos _ _ _
  rw [plEligibleInterimPriority, integral_prod _ hIntegrable,
    finiteRaceInterimPriority]
  refine integral_congr_ae ?_
  filter_upwards with ω
  have hAgree : ∀ ownShock : ℝ, ∀ j, j ≠ i →
      exponentialRaceKey reserve temperature
          (productShock opponentShock i (ω, ownShock))
          (Function.update bids i (bid : ℝ)) j =
        exponentialRaceKey reserve temperature (opponentShock ω) bids j := by
    intro ownShock j hj
    rw [exponentialRaceKey, exponentialRaceKey,
      productShock_of_ne opponentShock i (ω, ownShock) hj,
      Function.update_of_ne hj]
  have hKeyNonneg : ∀ ownShock : ℝ, ∀ j, j ≠ i →
      0 ≤ exponentialRaceKey reserve temperature
        (productShock opponentShock i (ω, ownShock))
        (Function.update bids i (bid : ℝ)) j := by
    intro ownShock j hj
    rw [hAgree ownShock j hj, exponentialRaceKey]
    exact div_nonneg (hShock ω j hj) (luceIntensity_pos _ _ _).le
  have hOwn : ∀ ownShock : ℝ,
      exponentialRaceKey reserve temperature
          (productShock opponentShock i (ω, ownShock))
          (Function.update bids i (bid : ℝ)) i =
        ownShock / luceIntensity reserve temperature (bid : ℝ) := by
    intro ownShock
    rw [exponentialRaceKey, productShock_self, Function.update_self]
  refine integral_congr_ae ?_
  have hNoTieAe := eventually_no_tie_fintype (ι := {j : ι // j ≠ i}) 1
    (luceIntensity reserve temperature (bid : ℝ)) (ne_of_gt hIntensity)
    (fun j => exponentialRaceKey reserve temperature (opponentShock ω) bids j.1)
  filter_upwards [hNoTieAe] with ownShock hNoTie
  have hTie : ∀ j, j ≠ i →
      exponentialRaceKey reserve temperature
          (productShock opponentShock i (ω, ownShock))
          (Function.update bids i (bid : ℝ)) j ≠
        exponentialRaceKey reserve temperature
          (productShock opponentShock i (ω, ownShock))
          (Function.update bids i (bid : ℝ)) i := by
    intro j hj
    rw [hAgree ownShock j hj, hOwn ownShock]
    exact fun heq => hNoTie ⟨j, hj⟩ heq.symm
  have hpoint := plEligibleRealizedPriority_eq_conditionedFiniteRacePriority
    slotWeight slots
    (exponentialRaceKey reserve temperature
      (productShock opponentShock i (ω, ownShock))
      (Function.update bids i (bid : ℝ))) i
    (hKeyNonneg ownShock) hTie (((bid : ℝ) - reserve) / temperature)
  have hscore : Real.exp (((bid : ℝ) - reserve) / temperature) *
      exponentialRaceKey reserve temperature
        (productShock opponentShock i (ω, ownShock))
        (Function.update bids i (bid : ℝ)) i = ownShock := by
    rw [hOwn ownShock]
    rw [show Real.exp (((bid : ℝ) - reserve) / temperature) =
      luceIntensity reserve temperature (bid : ℝ) from rfl]
    field_simp
  rw [hscore] at hpoint
  have hstats : opponentOrderStats
      (exponentialRaceKey reserve temperature
        (productShock opponentShock i (ω, ownShock))
        (Function.update bids i (bid : ℝ))) i (hKeyNonneg ownShock) =
      plOpponentOrderStats reserve temperature opponentShock bids i hShock ω := by
    rw [plOpponentOrderStats]
    exact opponentOrderStats_congr _ _ (hAgree ownShock)
  rw [hstats] at hpoint
  simp only [plEligibleRealizedPriority]
  exact hpoint

end SmoothingCliff.Mechanism
