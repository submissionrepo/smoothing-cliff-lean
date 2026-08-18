import SmoothingCliff.Mechanism.StabilityBridge

/-!
# Ties against a finite opponent field are null

The stability development conditions on the opponents' arrival times and reads
the bidder's own rank off which interval her own exponential clock lands in.
The monotonicity development instead ranks by `raceRank`, which breaks ties by
the agent order.  Reconciling the two needs the tie set to be null, so that the
tie-break never fires.

That is what this file supplies.  The own clock is exponential, hence has no
atoms, so the finitely many values at which it could coincide with an opponent
form a null set.  This is the first of the three blocks needed to credential
Theorem `thm:stability` end to end; the remaining two are the rank-interval
identity and the Fubini split of the own coordinate from the opponents'.
-/

namespace SmoothingCliff.Mechanism

open MeasureTheory ProbabilityTheory

/-- The exponential law has no atoms: it is a density against Lebesgue
measure. -/
instance noAtoms_expMeasure (rate : ℝ) : NoAtoms (expMeasure rate) := by
  show NoAtoms (volume.withDensity (gammaPDF 1 rate))
  infer_instance

theorem expMeasure_singleton (rate point : ℝ) :
    expMeasure rate {point} = 0 :=
  measure_singleton point

/-- A finite set of tie values is null. -/
theorem expMeasure_finset_null (rate : ℝ) (ties : Finset ℝ) :
    expMeasure rate (↑ties : Set ℝ) = 0 :=
  Finset.measure_zero ties _

/-- The set of own-clock values that tie with one of finitely many opponent
thresholds is null. -/
theorem expMeasure_tie_range_null {m : ℕ} (rate : ℝ) (threshold : Fin m → ℝ) :
    expMeasure rate {ownShock : ℝ | ∃ j : Fin m, ownShock = threshold j} = 0 := by
  classical
  have hsubset :
      {ownShock : ℝ | ∃ j : Fin m, ownShock = threshold j} ⊆
        ↑(Finset.image threshold Finset.univ) := by
    rintro x ⟨j, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem threshold (Finset.mem_univ j))
  exact measure_mono_null hsubset (expMeasure_finset_null rate _)

/-- Scaled ties are null too: the own arrival time is the own clock divided by
the intensity, so a tie in arrival times is a tie in clock values. -/
theorem expMeasure_scaled_tie_range_null
    {m : ℕ} (rate scale : ℝ) (hScale : scale ≠ 0) (threshold : Fin m → ℝ) :
    expMeasure rate
        {ownShock : ℝ | ∃ j : Fin m, ownShock / scale = threshold j} = 0 := by
  have hrewrite :
      {ownShock : ℝ | ∃ j : Fin m, ownShock / scale = threshold j} =
        {ownShock : ℝ | ∃ j : Fin m, ownShock = scale * threshold j} := by
    ext x
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by field_simp at hj; linarith [hj]⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      rw [hj]
      field_simp
  rw [hrewrite]
  exact expMeasure_tie_range_null rate fun j => scale * threshold j

/-- Almost every own clock value avoids every opponent threshold. -/
theorem eventually_no_tie
    {m : ℕ} (rate scale : ℝ) (hScale : scale ≠ 0) (threshold : Fin m → ℝ) :
    ∀ᵐ ownShock ∂(expMeasure rate), ∀ j : Fin m,
      ownShock / scale ≠ threshold j := by
  have hnull := expMeasure_scaled_tie_range_null rate scale hScale threshold
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, hj⟩

end SmoothingCliff.Mechanism
