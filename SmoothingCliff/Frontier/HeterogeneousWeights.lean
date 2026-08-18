import SmoothingCliff.Frontier.InterimBridgeMeanField

/-!
# Heterogeneous slot weights: part (i) at per-capita mass `∑_p w_p / n`

This file formalizes the **first clause** of Remark `rem:heteroweights` in
`Smoothing_the_Cliff_ITCS.tex`: with a declining weight profile
`w₁ ≥ w₂ ≥ ⋯ ≥ w_K ≥ 0`, part (i) of Theorem `thm:meanfield` holds verbatim with
per-capita priority mass `W̄_n := ∑_p w_p / n`.

The remark's own reason -- "the proof uses only the cap `x_i ≤ w₁` and total
mass" -- is what the formalization makes literal.  The certified class of
`SmoothingCliff.Frontier.InterimBridgeMeanField` already carries its capacity in
the separated form `∑ i, x b i ≤ w₁ * slots` with `slots : ℝ` a free real
parameter, so a declining profile is a value of that parameter rather than a new
theorem: `slots := (∑_p w_p) / w₁` gives `w₁ * slots = ∑_p w_p`
(`WeightProfile.top_mul_slots`, which covers the degenerate `w₁ = 0` too, where
antitonicity and nonnegativity force every weight to vanish).  Accordingly
`ProfileCertifiedRule` is stated in the paper's terms -- coordinatewise
measurable, values in `[0, w₁]`, `𝒮`-Lipschitz in the own coordinate uniformly in
the opponents, and `∑ i, x_i ≤ ∑_p w_p` pointwise -- and
`profileCertifiedRule_iff_certifiedRule` identifies it with an instance of the
existing class.  The two bounds

* `profileCertifiedRule_le_populationValue`: `V_n(x) ≤ V*(∑_p w_p / n)` at cap
  `w₁`, and
* `profileCertifiedRule_le_postedRamp`: the same against the explicit ramp
  calibrated to `min {∑_p w_p / n, w₁}`,

are that instance fed to `certifiedRule_le_populationValue` and
`certifiedRule_le_postedRamp`.  Nothing in the interim reduction is re-proved,
which is the precise sense in which part (i) holds "verbatim".

Equal weights are the profile `WeightProfile.const K w₁`: there the class is the
homogeneous certified class with `K` slots (`profileCertifiedRule_const_iff`) and
the mass is `W̄_n = w₁ K / n` (`WeightProfile.const_totalMass`), so
`profileCertifiedRule_const_le_populationValue` is the conclusion of
`certifiedRule_le_populationValue` verbatim, as the `example` following it
records.  Declining weights tighten the mass budget rather than loosen it:
`WeightProfile.totalMass_le_top_mul_card` gives `∑_p w_p ≤ w₁ K`.

**Scope.**  Only the first clause of `rem:heteroweights` is formalized -- the
upper bound at `W̄_n = ∑_p w_p / n` -- because the remark's second clause is an
explicitly open problem: once the ramp loads mass near `w₁`, implementability of
an interim vector as a lottery over ordered assignments adds the permutohedron
partial-sum constraints `∑_{top-k} x_(i) ≤ W_k` of Proposition `prop:squeeze`,
whose mean-field counterpart is the majorization family
`∫ (ξ - q)⁺ dF ≤ n⁻¹ ∑_p (w_p - q)⁺` for every `q ≥ 0`, and the paper leaves the
solution of that program (a composition of ramps, one per binding constraint)
open.  Nothing here asserts that the bound is attained for a strictly declining
profile; only that it is an upper bound.
-/

open MeasureTheory

open scoped BigOperators

namespace SmoothingCliff.Frontier

/-! ### Declining weight profiles -/

/-- A declining slot-weight profile `w₁ ≥ w₂ ≥ ⋯ ≥ w_K ≥ 0`, indexed from `0`, so
that `weight 0` is the paper's top weight `w₁`. -/
structure WeightProfile (K : ℕ) where
  /-- The weight attached to each slot. -/
  weight : Fin K → ℝ
  /-- Weights are nonnegative. -/
  nonneg : ∀ p, 0 ≤ weight p
  /-- Weights decline in the slot index. -/
  antitone : Antitone weight

namespace WeightProfile

section Basic

variable {K : ℕ} (w : WeightProfile K)

/-- Total priority mass `∑_p w_p` of the profile. -/
noncomputable def totalMass : ℝ := ∑ p, w.weight p

theorem totalMass_nonneg : 0 ≤ w.totalMass :=
  Finset.sum_nonneg fun p _ => w.nonneg p

variable [NeZero K]

/-- The top weight `w₁`, as a nonnegative real. -/
def top : NNReal := ⟨w.weight 0, w.nonneg 0⟩

@[simp] theorem coe_top : (w.top : ℝ) = w.weight 0 := rfl

/-- Every slot weight is at most the top weight: this is the only consequence of
declining weights that part (i) uses. -/
theorem le_top (p : Fin K) : w.weight p ≤ (w.top : ℝ) := w.antitone (Fin.zero_le p)

/-- A declining profile carries no more mass than `K` copies of the top weight,
so its per-capita cap `∑_p w_p / n` is never looser than `w₁ K / n`. -/
theorem totalMass_le_top_mul_card : w.totalMass ≤ (w.top : ℝ) * K := by
  calc w.totalMass ≤ ∑ _p : Fin K, (w.top : ℝ) :=
        Finset.sum_le_sum fun p _ => w.le_top p
    _ = (w.top : ℝ) * K := by simp [mul_comm]

/-- Total mass measured in units of the top weight: the slot count a uniform
profile at `w₁` would need in order to carry the same mass. -/
noncomputable def slots : ℝ := w.totalMass / w.top

theorem slots_nonneg : 0 ≤ w.slots :=
  div_nonneg w.totalMass_nonneg w.top.coe_nonneg

/-- `w₁ · (∑_p w_p / w₁) = ∑_p w_p`.  The degenerate case `w₁ = 0` is included:
there `w_p ≤ w₁ = 0 ≤ w_p` forces every weight to vanish, so both sides are `0`.
This identity is what turns a declining profile into an instance of the
homogeneous certified class. -/
theorem top_mul_slots : (w.top : ℝ) * w.slots = w.totalMass := by
  rcases eq_or_lt_of_le w.top.coe_nonneg with htop | htop
  · have hzero : w.totalMass = 0 := by
      refine le_antisymm ?_ w.totalMass_nonneg
      refine Finset.sum_nonpos fun p _ => ?_
      have hp := w.le_top p
      rw [← htop] at hp
      exact hp
    rw [← htop, hzero, zero_mul]
  · rw [slots, mul_div_cancel₀ _ (ne_of_gt htop)]

end Basic

section Const

/-- The equal-weight profile `w₁ = ⋯ = w_K = c`, the case of Theorem
`thm:meanfield` (i). -/
def const (K : ℕ) (c : NNReal) : WeightProfile K where
  weight := fun _ => (c : ℝ)
  nonneg := fun _ => c.coe_nonneg
  antitone := fun _ _ _ => le_rfl

@[simp] theorem const_weight (K : ℕ) (c : NNReal) (p : Fin K) :
    (const K c).weight p = (c : ℝ) := rfl

@[simp] theorem const_top (K : ℕ) [NeZero K] (c : NNReal) : (const K c).top = c := rfl

@[simp] theorem const_totalMass (K : ℕ) (c : NNReal) :
    (const K c).totalMass = (c : ℝ) * K := by
  simp [totalMass, mul_comm]

end Const

end WeightProfile

/-! ### The certified class of a declining profile -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's certified class `C^n_S` for a declining weight profile: rules
that are coordinatewise measurable, take values in `[0, w₁]`, are `𝒮`-Lipschitz in
the own coordinate uniformly in the opponents, and allocate at most the total
priority mass `∑_p w_p` at every bid profile.  Neither anonymity nor
monotonicity is imposed, exactly as in `CertifiedRule`. -/
structure ProfileCertifiedRule {K : ℕ} [NeZero K] (w : WeightProfile K)
    (sensitivity : NNReal) (x : (ι → ℝ) → ι → ℝ) : Prop where
  measurable : ∀ i, Measurable fun b => x b i
  nonneg : ∀ b i, 0 ≤ x b i
  le_topWeight : ∀ b i, x b i ≤ w.weight 0
  ownLipschitz : ∀ (i : ι) (b : ι → ℝ),
    LipschitzWith sensitivity fun v => x (Function.update b i v) i
  capacity : ∀ b, ∑ i, x b i ≤ w.totalMass

/-- The heterogeneous class **is** the homogeneous certified class at the top
weight with `slots = (∑_p w_p) / w₁`.  This is the content of the remark's "the
proof uses only the cap `x_i ≤ w₁` and total mass": the profile enters the
hypotheses of part (i) through those two numbers alone. -/
theorem profileCertifiedRule_iff_certifiedRule {K : ℕ} [NeZero K]
    (w : WeightProfile K) (sensitivity : NNReal) (x : (ι → ℝ) → ι → ℝ) :
    ProfileCertifiedRule w sensitivity x
      ↔ CertifiedRule w.top sensitivity w.slots x := by
  constructor
  · intro hx
    exact
      { measurable := hx.measurable
        nonneg := hx.nonneg
        le_weight := hx.le_topWeight
        ownLipschitz := hx.ownLipschitz
        capacity := fun b => by rw [w.top_mul_slots]; exact hx.capacity b }
  · intro hx
    exact
      { measurable := hx.measurable
        nonneg := hx.nonneg
        le_topWeight := hx.le_weight
        ownLipschitz := hx.ownLipschitz
        capacity := fun b => by
          have hb := hx.capacity b
          rwa [w.top_mul_slots] at hb }

/-! ### Part (i) for a declining profile -/

/-- **First clause of Remark `rem:heteroweights`.**  For a declining weight
profile `w₁ ≥ ⋯ ≥ w_K ≥ 0`, every finite agent set and every rule certified for
that profile, per-capita welfare is at most the value of the one-dimensional
population program run at cap `w₁` and per-capita priority mass
`W̄_n = ∑_p w_p / n`.  Only the first clause of the remark is formalized; the
majorization family raised by its second clause is open (module docstring). -/
theorem profileCertifiedRule_le_populationValue [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {K : ℕ} [NeZero K] {w : WeightProfile K} {sensitivity : NNReal}
    {x : (ι → ℝ) → ι → ℝ} (hx : ProfileCertifiedRule w sensitivity x) :
    perCapitaValue F x
      ≤ populationValue F w.top sensitivity (w.totalMass / Fintype.card ι) := by
  have hbound := certifiedRule_le_populationValue F hFirstMoment
    ((profileCertifiedRule_iff_certifiedRule w sensitivity x).mp hx)
  rwa [w.top_mul_slots] at hbound

/-- The declining-profile bound against the explicit optimizer: a posted ramp of
slope `𝒮` capped at the top weight `w₁` and calibrated to post mass
`min {∑_p w_p / n, w₁}` dominates every rule certified for the profile. -/
theorem profileCertifiedRule_le_postedRamp [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] {K : ℕ} [NeZero K] (w : WeightProfile K)
    (sensitivity : NNReal) (hSensitivity : 0 < sensitivity) (threshold : ℝ)
    (hFirstMoment : Integrable (fun v : ℝ => v) F) (hThreshold : 0 ≤ threshold)
    (hRampMass : curveMass F (postedRamp w.top sensitivity threshold)
      = min (w.totalMass / Fintype.card ι) (w.top : ℝ))
    {x : (ι → ℝ) → ι → ℝ} (hx : ProfileCertifiedRule w sensitivity x) :
    perCapitaValue F x
      ≤ curveWelfare F (postedRamp w.top sensitivity threshold) := by
  refine certifiedRule_le_postedRamp F w.top sensitivity hSensitivity w.slots
    threshold hFirstMoment hThreshold ?_
    ((profileCertifiedRule_iff_certifiedRule w sensitivity x).mp hx)
  rw [w.top_mul_slots]
  exact hRampMass

/-! ### Equal weights recover Theorem `thm:meanfield` (i) -/

/-- At the equal-weight profile the certified class is literally the homogeneous
one with `K` slots. -/
theorem profileCertifiedRule_const_iff {K : ℕ} [NeZero K] (c sensitivity : NNReal)
    (x : (ι → ℝ) → ι → ℝ) :
    ProfileCertifiedRule (WeightProfile.const K c) sensitivity x
      ↔ CertifiedRule c sensitivity K x := by
  constructor
  · intro hx
    exact
      { measurable := hx.measurable
        nonneg := hx.nonneg
        le_weight := hx.le_topWeight
        ownLipschitz := hx.ownLipschitz
        capacity := fun b => by
          have hb := hx.capacity b
          rwa [WeightProfile.const_totalMass] at hb }
  · intro hx
    exact
      { measurable := hx.measurable
        nonneg := hx.nonneg
        le_topWeight := hx.le_weight
        ownLipschitz := hx.ownLipschitz
        capacity := fun b => by
          rw [WeightProfile.const_totalMass]
          exact hx.capacity b }

/-- Equal weights recover part (i) with `W̄_n = w₁ K / n`. -/
theorem profileCertifiedRule_const_le_populationValue [Nonempty ι] (F : Measure ℝ)
    [IsProbabilityMeasure F] (hFirstMoment : Integrable (fun v : ℝ => v) F)
    {K : ℕ} [NeZero K] {c sensitivity : NNReal} {x : (ι → ℝ) → ι → ℝ}
    (hx : ProfileCertifiedRule (WeightProfile.const K c) sensitivity x) :
    perCapitaValue F x
      ≤ populationValue F c sensitivity ((c : ℝ) * K / Fintype.card ι) := by
  have hbound := profileCertifiedRule_le_populationValue F hFirstMoment hx
  rwa [WeightProfile.const_top, WeightProfile.const_totalMass] at hbound

/-- The recovery is exact rather than parallel: the conclusion above is the
conclusion of `certifiedRule_le_populationValue` at `slots = K`. -/
example [Nonempty ι] (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFirstMoment : Integrable (fun v : ℝ => v) F) {K : ℕ} {c sensitivity : NNReal}
    {x : (ι → ℝ) → ι → ℝ} (hx : CertifiedRule c sensitivity K x) :
    perCapitaValue F x
      ≤ populationValue F c sensitivity ((c : ℝ) * K / Fintype.card ι) :=
  certifiedRule_le_populationValue F hFirstMoment hx

/-! ### The hypotheses are jointly satisfiable -/

/-- A strictly declining two-slot profile `w₁ = 1 > w₂ = 1/2`. -/
noncomputable def testProfile : WeightProfile 2 where
  weight := ![1, 1 / 2]
  nonneg := by
    intro p
    fin_cases p <;> norm_num
  antitone := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
    norm_num

@[simp] theorem testProfile_weight_zero : testProfile.weight 0 = 1 := rfl

@[simp] theorem testProfile_totalMass : testProfile.totalMass = 3 / 2 := by
  simp [WeightProfile.totalMass, testProfile, Fin.sum_univ_two]
  norm_num

/-- A witness that `profileCertifiedRule_le_postedRamp` is not vacuous at a
genuinely heterogeneous profile: four agents, the two-slot profile
`w = (1, 1/2)`, the Dirac law at `1`, unit sensitivity, threshold `5/8` -- which
posts exactly the per-capita mass `(1 + 1/2)/4 = 3/8` -- and the zero rule. -/
example : perCapitaValue (ι := Fin 4) (Measure.dirac (1 : ℝ)) (fun _ _ => 0)
    ≤ curveWelfare (Measure.dirac (1 : ℝ))
        (postedRamp testProfile.top 1 (5 / 8)) := by
  refine profileCertifiedRule_le_postedRamp (ι := Fin 4) (Measure.dirac (1 : ℝ))
    testProfile 1 (by norm_num) (5 / 8) (integrable_dirac (by simp)) (by norm_num)
    ?_ ?_
  · unfold curveMass
    rw [integral_dirac, postedRamp, clampWeight_eq_of_mem] <;>
      simp <;> norm_num
  · exact
      { measurable := fun _ => measurable_const
        nonneg := fun _ _ => le_refl 0
        le_topWeight := fun _ _ => by norm_num [testProfile]
        ownLipschitz := fun _ _ =>
          (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)
        capacity := fun _ => by norm_num }

end SmoothingCliff.Frontier
