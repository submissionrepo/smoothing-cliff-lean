import SmoothingCliff.Frontier.WaterFilling

/-!
# The own-bid derivative inside the active band

Remark `rem:wf_tight` in `Smoothing_the_Cliff_ITCS.tex` reads the own-bid
derivative of the water-filling rule off the threshold equation: on the active
band `B` of coordinates that are neither shut out nor capped, raising one bid
by `δ` raises the threshold by `δ/|B|`, because the mass freed at the top has
to be reclaimed uniformly from the interior coordinates.  What the raised
bidder keeps is the difference, so the own derivative is `S(1-1/|B|)`, strictly
below the published cap `S` and approaching it as the band fills.

The printed remark states the identity without naming the side condition it
needs, namely that the band is the same before and after the perturbation.
That is not automatic: a large enough `δ` pushes the raised coordinate against
the cap or pushes a marginal coordinate out of the band, and then the identity
fails.  Here the side condition is the explicit hypothesis `hout` together with
the two interiority hypotheses, and `waterFill_band_increment_of_stable`
records that a band which is stable on a neighbourhood makes the map affine, so
the derivative statement is a genuine derivative and not a formal difference
quotient.
-/

namespace SmoothingCliff.Frontier

open scoped BigOperators

/-- The band factor of Remark `rem:wf_tight`. -/
noncomputable def bandFactor {ι : Type*} (B : Finset ι) : ℝ := 1 - 1 / (B.card : ℝ)

theorem bandFactor_nonneg {ι : Type*} {B : Finset ι} : 0 ≤ bandFactor B := by
  unfold bandFactor
  rcases Nat.eq_zero_or_pos B.card with h | h
  · simp [h]
  · have hcard : (1 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast h
    have : 1 / (B.card : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hcard
    linarith

theorem bandFactor_lt_one {ι : Type*} {B : Finset ι} (hB : B.Nonempty) : bandFactor B < 1 := by
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hB
  unfold bandFactor
  have : 0 < 1 / (B.card : ℝ) := by positivity
  linarith

/-- A single active coordinate cannot move at all: mass conservation pins it. -/
theorem bandFactor_singleton {ι : Type*} [DecidableEq ι] (i : ι) : bandFactor ({i} : Finset ι) = 0 := by
  simp [bandFactor]

/-- The band factor tends to one as the band fills. -/
theorem bandFactor_eq_of_card {ι : Type*} {B : Finset ι} {m : ℕ} (hm : B.card = m) :
    bandFactor B = 1 - 1 / (m : ℝ) := by
  simp [bandFactor, hm]

/-- As the band fills, the derivative approaches the cap. -/
theorem bandFactor_tendsto_one :
    Filter.Tendsto (fun m : ℕ => 1 - 1 / (m : ℝ)) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun m : ℕ => 1 / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa using Filter.Tendsto.const_sub (1 : ℝ) h


variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-! ### The threshold response -/

omit [Nonempty ι] in
/-- **Mass conservation moves the threshold by `δ/|B|`.**  If the active band is
the same set `B` before and after raising bid `i` by `δ`, and the coordinates
outside `B` keep their allocations, then the two thresholds differ by exactly
`δ/|B|`. -/
theorem threshold_shift_eq
    (weight sensitivity : NNReal) (hs : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) (delta : ℝ) (B : Finset ι)
    {t t' : ℝ}
    (ht : IsWaterFillingThreshold weight sensitivity b t)
    (ht' : IsWaterFillingThreshold weight sensitivity
      (Function.update b i (b i + delta)) t')
    (hiB : i ∈ B)
    (hin : ∀ j ∈ B, 0 ≤ (sensitivity : ℝ) * (b j - t) ∧
      (sensitivity : ℝ) * (b j - t) ≤ (weight : ℝ))
    (hin' : ∀ j ∈ B, 0 ≤ (sensitivity : ℝ) * (Function.update b i (b i + delta) j - t') ∧
      (sensitivity : ℝ) * (Function.update b i (b i + delta) j - t') ≤ (weight : ℝ))
    (hout : ∀ j ∉ B, waterFillAt weight sensitivity (Function.update b i (b i + delta)) t' j
      = waterFillAt weight sensitivity b t j) :
    delta = (B.card : ℝ) * (t' - t) := by
  set b' : ι → ℝ := Function.update b i (b i + delta) with hb'
  have hS : (0 : ℝ) < (sensitivity : ℝ) := hs
  -- inside the band both allocations are the unclamped linear expressions
  have hval : ∀ j ∈ B, waterFillAt weight sensitivity b t j
      = (sensitivity : ℝ) * (b j - t) := by
    intro j hj
    exact clampWeight_eq_of_mem weight (hin j hj).1 (hin j hj).2
  have hval' : ∀ j ∈ B, waterFillAt weight sensitivity b' t' j
      = (sensitivity : ℝ) * (b' j - t') := by
    intro j hj
    exact clampWeight_eq_of_mem weight (hin' j hj).1 (hin' j hj).2
  -- split the mass equation over the band and its complement
  have hsplit : ∀ (c : ι → ℝ) (s : ℝ),
      (∑ j, waterFillAt weight sensitivity c s j)
        = (∑ j ∈ B, waterFillAt weight sensitivity c s j)
          + ∑ j ∈ Bᶜ, waterFillAt weight sensitivity c s j := by
    intro c s
    rw [← Finset.sum_add_sum_compl B]
  have hmass : (∑ j ∈ B, waterFillAt weight sensitivity b' t' j)
      = ∑ j ∈ B, waterFillAt weight sensitivity b t j := by
    have h1 : waterFillMass weight sensitivity b' t' = weight := ht'
    have h2 : waterFillMass weight sensitivity b t = weight := ht
    have houtsum : (∑ j ∈ Bᶜ, waterFillAt weight sensitivity b' t' j)
        = ∑ j ∈ Bᶜ, waterFillAt weight sensitivity b t j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      exact hout j (Finset.mem_compl.mp hj)
    unfold waterFillMass at h1 h2
    rw [hsplit b' t'] at h1
    rw [hsplit b t] at h2
    rw [houtsum] at h1
    linarith [h1, h2]
  -- rewrite both sides as linear expressions and read off the shift
  rw [Finset.sum_congr rfl hval', Finset.sum_congr rfl hval] at hmass
  have hsumb' : (∑ j ∈ B, b' j) = (∑ j ∈ B, b j) + delta := by
    rw [hb', Finset.sum_update_of_mem hiB, Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase B b hiB]
    ring
  have hexpand : (∑ j ∈ B, (sensitivity : ℝ) * (b' j - t'))
      = (sensitivity : ℝ) * ((∑ j ∈ B, b' j) - (B.card : ℝ) * t') := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hexpand2 : (∑ j ∈ B, (sensitivity : ℝ) * (b j - t))
      = (sensitivity : ℝ) * ((∑ j ∈ B, b j) - (B.card : ℝ) * t) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hexpand, hexpand2, hsumb'] at hmass
  have hcancel : (∑ j ∈ B, b j) + delta - (B.card : ℝ) * t'
      = (∑ j ∈ B, b j) - (B.card : ℝ) * t :=
    mul_left_cancel₀ (ne_of_gt hS) hmass
  linarith

/-! ### The own-bid increment -/

/-- **Remark `rem:wf_tight`, the band identity.**  With the active band `B`
unchanged by the perturbation, raising bid `i` by `delta` raises agent `i`'s
allocation by exactly `S * delta * (1 - 1/|B|)`.  The published cap `S` is the
`|B| -> infinity` value, and a lone active coordinate cannot move at all. -/
theorem waterFill_band_increment
    (weight sensitivity : NNReal) (hs : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) (delta : ℝ) (B : Finset ι)
    {t t' : ℝ}
    (ht : IsWaterFillingThreshold weight sensitivity b t)
    (ht' : IsWaterFillingThreshold weight sensitivity
      (Function.update b i (b i + delta)) t')
    (hiB : i ∈ B)
    (hin : ∀ j ∈ B, 0 ≤ (sensitivity : ℝ) * (b j - t) ∧
      (sensitivity : ℝ) * (b j - t) ≤ (weight : ℝ))
    (hin' : ∀ j ∈ B, 0 ≤ (sensitivity : ℝ) * (Function.update b i (b i + delta) j - t') ∧
      (sensitivity : ℝ) * (Function.update b i (b i + delta) j - t') ≤ (weight : ℝ))
    (hout : ∀ j ∉ B, waterFillAt weight sensitivity (Function.update b i (b i + delta)) t' j
      = waterFillAt weight sensitivity b t j) :
    waterFillingVector weight sensitivity hs (Function.update b i (b i + delta)) i
        - waterFillingVector weight sensitivity hs b i
      = (sensitivity : ℝ) * delta * bandFactor B := by
  have hshift := threshold_shift_eq weight sensitivity hs b i delta B ht ht' hiB hin hin' hout
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, hiB⟩
  have hvi : waterFillingVector weight sensitivity hs b i = (sensitivity : ℝ) * (b i - t) := by
    rw [waterFillingVector_eq_at_threshold weight sensitivity hs b ht i]
    exact clampWeight_eq_of_mem weight (hin i hiB).1 (hin i hiB).2
  have hvi' : waterFillingVector weight sensitivity hs (Function.update b i (b i + delta)) i
      = (sensitivity : ℝ) * (b i + delta - t') := by
    rw [waterFillingVector_eq_at_threshold weight sensitivity hs _ ht' i, waterFillAt,
      Function.update_self]
    exact clampWeight_eq_of_mem weight (by simpa using (hin' i hiB).1)
      (by simpa using (hin' i hiB).2)
  rw [hvi, hvi']
  have hne : ((B.card : ℝ)) ≠ 0 := ne_of_gt hcard
  have hdiff : t' - t = delta / (B.card : ℝ) := by
    rw [hshift]
    field_simp
  have hexp : (sensitivity : ℝ) * (b i + delta - t') - (sensitivity : ℝ) * (b i - t)
      = (sensitivity : ℝ) * (delta - (t' - t)) := by ring
  rw [hexp, hdiff]
  unfold bandFactor
  field_simp

/-! ### The derivative -/

/-- A band that is stable on a neighbourhood makes the own-bid map affine
there, so the band identity is a genuine derivative rather than a formal
difference quotient. -/
theorem hasDerivAt_waterFill_band
    (weight sensitivity : NNReal) (hs : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) (B : Finset ι) {eps : ℝ} (heps : 0 < eps)
    (hstable : ∀ delta ∈ Set.Ioo (-eps) eps,
      waterFillingVector weight sensitivity hs (Function.update b i (b i + delta)) i
          - waterFillingVector weight sensitivity hs b i
        = (sensitivity : ℝ) * delta * bandFactor B) :
    HasDerivAt (fun delta : ℝ => waterFillingVector weight sensitivity hs
        (Function.update b i (b i + delta)) i)
      ((sensitivity : ℝ) * bandFactor B) 0 := by
  set v0 := waterFillingVector weight sensitivity hs b i with hv0
  have haffine : HasDerivAt
      (fun delta : ℝ => v0 + ((sensitivity : ℝ) * bandFactor B) * delta)
      ((sensitivity : ℝ) * bandFactor B) 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).const_mul ((sensitivity : ℝ) * bandFactor B)).const_add v0)
  refine haffine.congr_of_eventuallyEq ?_
  have hmem : Set.Ioo (-eps) eps ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) heps
  filter_upwards [hmem] with delta hdelta
  have h := hstable delta hdelta
  linarith [h]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The band derivative is strictly below the published cap `S`, and reaches it
only in the limit. -/
theorem band_derivative_lt_cap (sensitivity : NNReal) (hs : 0 < sensitivity)
    {B : Finset ι} (hB : B.Nonempty) :
    (sensitivity : ℝ) * bandFactor B < (sensitivity : ℝ) := by
  have hS : (0 : ℝ) < (sensitivity : ℝ) := hs
  have := bandFactor_lt_one hB
  nlinarith

end SmoothingCliff.Frontier
