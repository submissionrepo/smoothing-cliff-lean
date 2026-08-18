/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `MixedDist` Non-Vacuity Checks

Compile-time semantic witnesses for the mixed (atoms + density) carrier
`Econlib.Probability.MixedDist`. The witnesses are anchored on:

* `mixed` — a genuinely mixed law: A `1/2` atom at `0` plus a `1/2`-weighted uniform density on
  `[0,1]` (so neither weight is `0` or `1`);
* `pureC = ofContDist (uniform 0 1)` — a pure continuous law (discrete weight `0`);
* `pureA = ofAtoms` — a pure atomic law (continuous weight `0`).

The weight split (`discrete + continuous = 1`, each strictly interior for `mixed`) is the
orientation-critical spot — a continuous/discrete weight swap would flip the pure-case values.
-/

noncomputable section

namespace EconlibTest.Probability.MixedDist

open Econlib.Probability MeasureTheory ProbabilityTheory Filter Topology

/-- The uniform density on `[0,1]`. -/
private abbrev cu : ContDist := ContDist.uniform 0 1 (by norm_num)

/-- A genuinely mixed law: A `1/2` atom at `0` plus a `1/2`-weighted uniform `[0,1]` density. -/
private abbrev mixed : MixedDist :=
  MixedDist.mk' ![0] ![1 / 2] cu (1 / 2)
    (fun i => by fin_cases i; norm_num)
    (by norm_num)
    (by norm_num [Fin.sum_univ_one])

/-- The pure continuous embedding of the uniform law. -/
private abbrev pureC : MixedDist := MixedDist.ofContDist cu

/-- A pure atomic law: Equal mass at `0` and `1`. -/
private abbrev pureA : MixedDist := MixedDist.ofAtoms ![0, 1] (finDist% ![1 / 2, 1 / 2])

section weights

/-- **Pure continuous ⇒ no atomic mass.** `ofContDist` carries discrete weight `0`, continuous
weight `1`. -/
theorem pureC_discreteWeight : pureC.discreteWeight = 0 := MixedDist.ofContDist_discreteWeight cu
theorem pureC_continuousWeight : pureC.continuousWeight = 1 :=
  MixedDist.ofContDist_continuousWeight cu

/-- **Pure atomic ⇒ no continuous mass** (the dual). -/
theorem pureA_discreteWeight : pureA.discreteWeight = 1 :=
  MixedDist.ofAtoms_discreteWeight _ _
theorem pureA_continuousWeight : pureA.continuousWeight = 0 :=
  MixedDist.ofAtoms_continuousWeight _ _

/-- **Interior continuous weight.** The mixed law puts mass `1/2` on its continuous part. -/
theorem mixed_continuousWeight : mixed.continuousWeight = 1 / 2 := by
  have hdens : mixed.density = fun x => (1 / 2 : ℝ) * cu.density x := rfl
  rw [MixedDist.continuousWeight, hdens, integral_const_mul, cu.integral_one, mul_one]

theorem mixed_discreteWeight : mixed.discreteWeight = 1 / 2 := by
  rw [MixedDist.discreteWeight_eq, mixed_continuousWeight]; norm_num

/-- **The weight split is genuinely interior**, `(1/2, 1/2)`, and sums to one — so this is a *bona
fide* mixed law, not a degenerate pure-discrete or pure-continuous one. The conjunction pins both
component weights to `1/2` (interiority), strengthening the bare normalization identity. -/
theorem mixed_weight_split :
    mixed.discreteWeight = 1 / 2 ∧ mixed.continuousWeight = 1 / 2 ∧
      mixed.discreteWeight + mixed.continuousWeight = 1 :=
  ⟨mixed_discreteWeight, mixed_continuousWeight, by
    rw [MixedDist.continuousWeight_eq]; ring⟩

end weights

section normalization

/-- **The mixed law is a genuine probability measure** (atomic + continuous masses sum to `1`). -/
theorem mixed_isProbability : IsProbabilityMeasure mixed.toMeasure :=
  mixed.toMeasure_isProbability

end normalization

section expectation

/-- **Continuous embedding preserves expectation.** `E_{ofContDist d}[f] = E_d[f]`. -/
theorem pureC_expect_id : pureC.expect id = cu.expect id := MixedDist.ofContDist_expect cu id

/-- **Atomic expectation is the mass-weighted point sum:** `½·0 + ½·1 = 1/2`. -/
theorem pureA_expect_id : pureA.expect id = 1 / 2 := by
  rw [MixedDist.ofAtoms_expect]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, id_eq,
    FinDist.ofVec_pmf]
  norm_num

/-- A nonnegative integrand has nonnegative mixed expectation. -/
theorem mixed_expect_nonneg : 0 ≤ mixed.expect (fun x => x ^ 2) :=
  mixed.expect_nonneg _ (fun x => sq_nonneg x)

/-- Expectation of a constant returns the constant (total mass is `1`). -/
theorem mixed_expect_const : mixed.expect (fun _ => 7) = 7 := mixed.expect_const 7

/-- The atom finsupp of `mixed` is exactly the single point mass `½` at `0`. -/
theorem mixed_atoms : mixed.atoms = Finsupp.single 0 (1 / 2) := by
  change (∑ i : Fin 1, Finsupp.single (![(0 : ℝ)] i) (![(1 / 2 : ℝ)] i)) = _
  rw [Fin.sum_univ_one]
  norm_num

/-- **The mixed mean is `1/4`.** Atomic part `½·0 = 0` plus continuous part
`½·E_unif[id] = ½·½ = 1/4`. This anchors the discrete/continuous decomposition: A weight swap (atom
mass `½` at `1`, density on the atom point) would move the mean. -/
theorem mixed_expect_id : mixed.expect id = 1 / 4 := by
  rw [MixedDist.expect_eq, mixed_atoms, Finsupp.sum_single_index (by simp)]
  -- Atomic part is `½·0 = 0`; the continuous integral is `½·E_unif[id] = ½·½`.
  have hdens : mixed.density = fun x => (1 / 2 : ℝ) * cu.density x := rfl
  have hcont : (∫ x, mixed.density x * id x) = 1 / 4 := by
    have hrw : (fun x => mixed.density x * id x)
        = fun x => (1 / 2 : ℝ) * (cu.density x * id x) := by
      funext x; rw [hdens]; ring
    rw [hrw, integral_const_mul, ← ContDist.expect_eq_integral, ContDist.uniform_expect]
    norm_num
  rw [hcont]; norm_num

/-- The mixed density is `½ · 1_{[0,1]}`, i.e. the indicator of `[0,1]` scaled by `½`. -/
private theorem mixed_density_eq_indicator :
    mixed.density = Set.indicator (Set.Icc 0 1) (fun _ => (1 / 2 : ℝ)) := by
  funext x
  change (1 / 2 : ℝ) * cu.density x = _
  rw [ContDist.uniform_density]
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · rw [if_pos hx, Set.indicator_of_mem hx]; norm_num
  · rw [if_neg hx, Set.indicator_of_notMem hx, mul_zero]

/-- For continuous `f`, `mixed.density · f` is `volume`-integrable: It is `½ · f` on the compact
`[0,1]` and zero elsewhere. This is the integrability side condition the expectation-algebra lemmas
demand. -/
private theorem mixed_density_mul_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun x => mixed.density x * f x) := by
  have hrw : (fun x => mixed.density x * f x)
      = Set.indicator (Set.Icc 0 1) (fun x => (1 / 2 : ℝ) * f x) := by
    funext x
    rw [mixed_density_eq_indicator]
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [hrw]
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
  exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc

/-- **Linearity (additivity).** `E[id + 1] = E[id] + E[1] = 1/4 + 1 = 5/4`. -/
theorem mixed_expect_add :
    mixed.expect (id + fun _ => 1) = 5 / 4 := by
  rw [mixed.expect_add id (fun _ => 1)
        (mixed_density_mul_integrable continuous_id)
        (mixed_density_mul_integrable continuous_const),
    mixed_expect_id, mixed.expect_const 1]
  norm_num

/-- **Linearity (scaling).** `E[3 • id] = 3·E[id] = 3·(1/4) = 3/4`. -/
theorem mixed_expect_smul : mixed.expect ((3 : ℝ) • id) = 3 / 4 := by
  rw [mixed.expect_smul 3 id, mixed_expect_id]; norm_num

/-- **Monotonicity.** `id ≤ id + 1` pointwise, so `E[id] ≤ E[id + 1]`, i.e. `1/4 ≤ 5/4`. -/
theorem mixed_expect_mono : mixed.expect id ≤ mixed.expect (fun x => x + 1) :=
  mixed.expect_mono (fun x => by simp only [id_eq]; linarith)
    (mixed_density_mul_integrable continuous_id)
    (mixed_density_mul_integrable (by fun_prop))

/-- The mixed second moment is `1/6`: Atomic `½·0² = 0` plus continuous
`½·E_unif[x²] = ½·(1/3) = 1/6`. -/
private theorem mixed_expect_sq : mixed.expect (fun x => x ^ 2) = 1 / 6 := by
  rw [MixedDist.expect_eq, mixed_atoms, Finsupp.sum_single_index (by simp)]
  -- `E_unif[x²] = Var_unif(id) + (E_unif[id])² = 1/12 + 1/4 = 1/3`.
  have hcu_sq : cu.expect (fun x => x ^ 2) = 1 / 3 := by
    have hvar : cu.variance id = cu.expect (fun x => x ^ 2) - (cu.expect id) ^ 2 := rfl
    rw [ContDist.uniform_variance, ContDist.uniform_expect] at hvar
    linarith
  have hdens : mixed.density = fun x => (1 / 2 : ℝ) * cu.density x := rfl
  have hcont : (∫ x, mixed.density x * x ^ 2) = 1 / 6 := by
    have hrw : (fun x => mixed.density x * x ^ 2)
        = fun x => (1 / 2 : ℝ) * (cu.density x * (fun y => y ^ 2) x) := by
      funext x; rw [hdens]; ring
    rw [hrw, integral_const_mul, ← ContDist.expect_eq_integral, hcu_sq]
    norm_num
  rw [hcont]; norm_num

/-- **Variance is `5/48`.** `Var = E[id²] − (E[id])² = 1/6 − (1/4)² = 5/48`. The atom at `0`
contributes nothing to `E[id²]`, so the spread comes entirely from the `½`-weighted uniform. -/
theorem mixed_variance_id : mixed.variance id = 5 / 48 := by
  have hvar : mixed.variance id = mixed.expect (fun x => x ^ 2) - (mixed.expect id) ^ 2 := rfl
  rw [hvar, mixed_expect_sq, mixed_expect_id]; norm_num

end expectation

section cdf

/-- The mixed CDF is monotone. -/
theorem mixed_cdf_mono : Monotone mixed.cdfFun := mixed.cdfFun_mono

/-- The mixed CDF is right-continuous. -/
theorem mixed_cdf_right_continuous (x : ℝ) :
    ContinuousWithinAt mixed.cdfFun (Set.Ici x) x := mixed.cdfFun_right_continuous x

/-- **CDF bottom endpoint:** `F(x) → 0` as `x → -∞`. -/
theorem mixed_cdf_tendsto_bot : Tendsto mixed.cdfFun atBot (𝓝 0) := mixed.cdfFun_tendsto_bot

/-- **CDF top endpoint:** `F(x) → 1` as `x → +∞`. -/
theorem mixed_cdf_tendsto_top : Tendsto mixed.cdfFun atTop (𝓝 1) := mixed.cdfFun_tendsto_top

/-- `discreteCDF` evaluated through the single atom at `0`: It is the atom weight `½` once the
threshold reaches `0`, and `0` strictly below. -/
private theorem mixed_discreteCDF (x : ℝ) :
    mixed.discreteCDF x = if (0 : ℝ) ≤ x then 1 / 2 else 0 := by
  rw [MixedDist.discreteCDF, mixed_atoms]
  rw [Finsupp.sum_single_index (by simp)]

/-- **Left of the atom the discrete CDF is `0`.** At `x = -1` no atom mass has accumulated. -/
theorem mixed_discreteCDF_below_atom : mixed.discreteCDF (-1) = 0 := by
  rw [mixed_discreteCDF, if_neg (by norm_num)]

/-- **At the atom the discrete CDF equals the accumulated atom mass `½`.** Compared with the
left-of-atom value `0`, the discrete CDF jumps by exactly the atom weight `½`. -/
theorem mixed_discreteCDF_at_atom : mixed.discreteCDF 0 = 1 / 2 := by
  rw [mixed_discreteCDF, if_pos le_rfl]

/-- **The discrete jump at the atom equals the atom mass `½`.** `discreteCDF 0 − discreteCDF(−1)`
isolates the point mass at `0`. -/
theorem mixed_discrete_jump :
    mixed.discreteCDF 0 - mixed.discreteCDF (-1) = 1 / 2 := by
  rw [mixed_discreteCDF_at_atom, mixed_discreteCDF_below_atom]; norm_num

/-- **The atomic measure of `(-∞, 0]` is the atom mass `½`** (`atomicMeasure_Iic`): The half-line
through the atom collects exactly its point mass. -/
theorem mixed_atomicMeasure_Iic_atom :
    mixed.atomicMeasure (Set.Iic 0) = ENNReal.ofReal (1 / 2) := by
  rw [MixedDist.atomicMeasure_Iic, mixed_discreteCDF_at_atom]

/-- **The continuous CDF does not jump at the atom:** `continuousCDF 0 = 0`, since the density is
absolutely continuous (the single point `{0}` has Lebesgue measure zero). Hence the entire CDF jump
at `0` comes from the atom. -/
theorem mixed_continuousCDF_at_atom : mixed.continuousCDF 0 = 0 := by
  rw [MixedDist.continuousCDF, mixed_density_eq_indicator]
  -- `∫_{(-∞,0]} ½·1_{[0,1]} = ½ · volume([0,1] ∩ Iic 0) = ½ · volume {0} = 0`.
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_restrict_apply measurableSet_Icc]
  -- `volume (Icc 0 1 ∩ Iic 0) = volume {0} = 0`.
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Iic 0 = {0} := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hy_ge, _⟩, hy_le⟩; exact le_antisymm hy_le hy_ge
    · rintro rfl; norm_num
  rw [hset, MeasureTheory.measureReal_def, Real.volume_singleton]; simp

/-- **The full CDF value at the atom is `½`** (`cdfFun = discreteCDF + continuousCDF`): The
discrete jump `½` plus a continuous part `0` that contributes nothing at the single point. -/
theorem mixed_cdfFun_at_atom : mixed.cdfFun 0 = 1 / 2 := by
  rw [MixedDist.cdfFun, mixed_discreteCDF_at_atom, mixed_continuousCDF_at_atom, add_zero]

end cdf

section measure

/-- **The total measure splits into atomic + continuous parts** (`toMeasure_eq`). -/
theorem mixed_toMeasure_eq :
    mixed.toMeasure = mixed.atomicMeasure + mixed.continuousMeasure := mixed.toMeasure_eq

/-- **The atomic part carries total mass `½`** (`atomicMeasure_univ = ofReal discreteWeight`). -/
theorem mixed_atomicMeasure_univ :
    mixed.atomicMeasure Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [MixedDist.atomicMeasure_univ, mixed_discreteWeight]

/-- **The continuous part carries total mass `½`**
(`continuousMeasure_univ = ofReal
continuousWeight`). Together with the atomic `½` this confirms
the normalization is non-vacuous. -/
theorem mixed_continuousMeasure_univ :
    mixed.continuousMeasure Set.univ = ENNReal.ofReal (1 / 2) := by
  rw [MixedDist.continuousMeasure_univ, mixed_continuousWeight]

/-- **The atomic + continuous univ masses sum to the full mass `1`.** A continuous/discrete weight
swap would still sum to `1` here, but the two halves being *equal* and *each* `½` is what pins the
mixture down. -/
theorem mixed_univ_mass_split :
    mixed.atomicMeasure Set.univ + mixed.continuousMeasure Set.univ = 1 := by
  rw [mixed_atomicMeasure_univ, mixed_continuousMeasure_univ,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- **The `ProbDist` embedding's measure is `toMeasure`** (`toProbDist_toMeasure`). -/
theorem mixed_toProbDist_toMeasure :
    (mixed.toProbDist : Measure ℝ) = mixed.toMeasure := mixed.toProbDist_toMeasure

/-- The atomic measure of `mixed` is exactly `½ · δ₀` (a single scaled Dirac at the atom). -/
private theorem mixed_atomicMeasure_eq :
    mixed.atomicMeasure = ENNReal.ofReal (1 / 2) • Measure.dirac 0 := by
  rw [MixedDist.atomicMeasure, mixed_atoms, Finsupp.sum_single_index (by simp)]

/-- `id` is integrable against `mixed.toMeasure`: Integrable on the finite atomic Dirac and on the
continuous (`withDensity`) part. The side condition for `expect_eq_measure_integral`. -/
private theorem mixed_id_integrable_toMeasure : Integrable id mixed.toMeasure := by
  rw [MixedDist.toMeasure_eq]
  refine (integrable_add_measure (μ := mixed.atomicMeasure) (ν := mixed.continuousMeasure)).mpr
    ⟨?_, ?_⟩
  · -- Atomic part is `½ · δ₀`; `id` is integrable against a (scaled) Dirac.
    rw [mixed_atomicMeasure_eq]
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  · -- Continuous part: `id` integrable since `density · id` is `volume`-integrable.
    rw [MixedDist.continuousMeasure,
      integrable_withDensity_iff_integrable_smul₀'
        mixed.density_integrable.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have hmul := mixed_density_mul_integrable (f := id) continuous_id
    refine hmul.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (mixed.density_nonneg x), id_eq, mul_comm]

/-- **`expect` agrees with integration against `toMeasure`** for the integrable observable `id`
(`expect_eq_measure_integral`), with the closed-form mean `1/4` pinned on *both* sides: the
`MixedDist.expect` value and the measure-theoretic integral `∫ x ∂toMeasure` are both equal to the
hand-computed `1/4`. -/
theorem mixed_expect_eq_measure_integral :
    mixed.expect id = ∫ x, id x ∂mixed.toMeasure ∧ (∫ x, id x ∂mixed.toMeasure) = 1 / 4 := by
  have hbridge := mixed.expect_eq_measure_integral id mixed_id_integrable_toMeasure
  exact ⟨hbridge, by rw [← hbridge, mixed_expect_id]⟩

end measure

section bayes

/-! Two posterior updates on `mixed`: An **uninformative** likelihood `ℓ ≡ 1` (which must recover
the prior weights) and an **informative** likelihood `ℓ = x²` (which rules out the atom at `0`,
where `ℓ` vanishes). Together they catch a posterior formula that ignores the likelihood or divides
by the wrong evidence. -/

/-- The density integral of `mixed` against `f` is `½ · E_unif[f]`, since the density is
`½ · 1_{[0,1]}`. -/
private theorem mixed_density_integral (f : ℝ → ℝ) :
    (∫ x, mixed.density x * f x) = (1 / 2 : ℝ) * cu.expect f := by
  have hdens : mixed.density = fun x => (1 / 2 : ℝ) * cu.density x := rfl
  rw [show (fun x => mixed.density x * f x)
      = fun x => (1 / 2 : ℝ) * (cu.density x * f x) from by funext x; rw [hdens]; ring,
    integral_const_mul, ← ContDist.expect_eq_integral]

/-! ### Uninformative update: `ℓ ≡ 1` recovers the prior -/

/-- The constant unit likelihood. -/
private abbrev lkOne : ℝ → ℝ := fun _ => 1

/-- **Evidence of an uninformative update is `1`** (it equals the prior total mass). -/
theorem mixed_evidence_one : mixed.evidence lkOne = 1 := by
  rw [MixedDist.evidence, mixed_atoms, Finsupp.sum_single_index (by simp),
    mixed_density_integral, cu.expect_const]
  norm_num

theorem mixed_evidence_one_pos : 0 < mixed.evidence lkOne := by
  rw [mixed_evidence_one]; norm_num

/-- `ℓ ≡ 1` is integrable against the density (constant times density). -/
private theorem lkOne_int : Integrable (fun x => mixed.density x * lkOne x) :=
  mixed_density_mul_integrable continuous_const

/-- **Uninformative update preserves the atom weight `½`** (`posterior_atoms_apply`). With `ℓ ≡ 1`
and evidence `1`, the posterior atom weight equals the prior `atoms 0 · 1 / 1 = ½`. -/
theorem mixed_posterior_one_atom :
    (mixed.posteriorOfLikelihood lkOne (fun _ => by norm_num) lkOne_int
        mixed_evidence_one_pos).atoms 0 = 1 / 2 := by
  rw [MixedDist.posterior_atoms_apply, mixed_evidence_one]
  -- `atoms 0 = ½`, `ℓ 0 = 1`, evidence `= 1`.
  have : mixed.atoms 0 = 1 / 2 := by rw [mixed_atoms, Finsupp.single_eq_same]
  rw [this]; norm_num

/-- **Posterior mean under an uninformative update equals the prior mean `1/4`**
(`posterior_expect`): `E_post[id] = E_prior[1·id]/1 = E_prior[id] = 1/4`. -/
theorem mixed_posterior_one_expect :
    (mixed.posteriorOfLikelihood lkOne (fun _ => by norm_num) lkOne_int
        mixed_evidence_one_pos).expect id = 1 / 4 := by
  rw [MixedDist.posterior_expect (f := id)
      (_hf_int := by
        have := mixed_density_mul_integrable (f := id) continuous_id
        refine this.congr (Filter.Eventually.of_forall fun x => by simp)),
    mixed_evidence_one]
  -- `E_prior[1·id] = E_prior[id] = 1/4`.
  rw [show (fun x => lkOne x * id x) = id from by funext x; simp, mixed_expect_id]
  norm_num

/-! ### Informative update: `ℓ = x²` rules out the atom at `0` -/

/-- The squared likelihood `ℓ(x) = x²` — vanishes exactly at the atom location `0`. -/
private abbrev lkSq : ℝ → ℝ := fun x => x ^ 2

/-- `ℓ = x²` is integrable against the density (continuous integrand on the compact support). -/
private theorem lkSq_int : Integrable (fun x => mixed.density x * lkSq x) :=
  mixed_density_mul_integrable (by fun_prop)

/-- **Evidence of the `x²` update is `1/6`.** Atomic part `½·0² = 0` (the atom is at `0`, where `ℓ`
vanishes) plus continuous `½·E_unif[x²] = ½·(1/3) = 1/6`. -/
theorem mixed_evidence_sq : mixed.evidence lkSq = 1 / 6 := by
  rw [MixedDist.evidence, mixed_atoms, Finsupp.sum_single_index (by simp),
    mixed_density_integral]
  -- `E_unif[x²] = 1/3`; atom contributes `½·0² = 0`.
  have hcu_sq : cu.expect lkSq = 1 / 3 := by
    have hvar : cu.variance id = cu.expect (fun x => x ^ 2) - (cu.expect id) ^ 2 := rfl
    rw [ContDist.uniform_variance, ContDist.uniform_expect] at hvar
    change cu.expect (fun x => x ^ 2) = 1 / 3
    linarith
  rw [hcu_sq]; norm_num

theorem mixed_evidence_sq_pos : 0 < mixed.evidence lkSq := by
  rw [mixed_evidence_sq]; norm_num

/-- **The informative update rules the atom out:** posterior atom weight at `0` is `0`, because
`ℓ(0) = 0`. A formula that ignored the likelihood would wrongly keep weight `½`. -/
theorem mixed_posterior_sq_atom :
    (mixed.posteriorOfLikelihood lkSq (fun x => sq_nonneg x) lkSq_int
        mixed_evidence_sq_pos).atoms 0 = 0 := by
  rw [MixedDist.posterior_atoms_apply]
  -- `ℓ 0 = 0²= 0`, so the whole numerator vanishes.
  change mixed.atoms 0 * (0 : ℝ) ^ 2 / mixed.evidence lkSq = 0
  norm_num

/-- **Posterior density under `x²`** is `prior density · x² / evidence = 3 · x² · 1_{[0,1]}`
(`posterior_density`). At `x = 1` (inside the support) this is `3·1·1 = 3`. -/
theorem mixed_posterior_sq_density_at_one :
    (mixed.posteriorOfLikelihood lkSq (fun x => sq_nonneg x) lkSq_int
        mixed_evidence_sq_pos).density 1 = 3 := by
  rw [MixedDist.posterior_density, mixed_evidence_sq]
  -- `density 1 = ½·cu.density 1 = ½·1 = ½`; so `½·1²/(1/6) = 3`.
  have hd1 : mixed.density 1 = 1 / 2 := by
    rw [mixed_density_eq_indicator, Set.indicator_of_mem (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
  rw [hd1]; norm_num

/-- **Posterior mean under the informative `x²` update is `3/4`** — the discriminating witness for
`posterior_expect` that the flat-likelihood `mixed_posterior_one_expect` cannot give. The `x²`
reweighting kills the atom at `0` and tilts mass toward the right of `[0,1]`, raising the mean from
the prior `1/4` to `3/4`. By the formula,
`E_post[id] = E_prior[x²·id]/evidence = E_prior[x³]/(1/6)`;
the prior third moment is `½·0³ + ½·∫₀¹x³ = ½·(1/4) = 1/8`,
so `E_post[id] = (1/8)/(1/6) = 3/4`. A
posterior that dropped the `* ℓ` factor or divided by the wrong evidence would miss this. -/
theorem mixed_posterior_sq_expect :
    (mixed.posteriorOfLikelihood lkSq (fun x => sq_nonneg x) lkSq_int
        mixed_evidence_sq_pos).expect id = 3 / 4 := by
  rw [MixedDist.posterior_expect (f := id)
      (_hf_int := by
        have := mixed_density_mul_integrable (f := fun x => lkSq x * id x) (by fun_prop)
        refine this.congr (Filter.Eventually.of_forall fun x => by simp [mul_assoc])),
    mixed_evidence_sq]
  -- `E_prior[x²·id] = E_prior[x³] = 1/8`.
  have hcube : mixed.expect (fun x => lkSq x * id x) = 1 / 8 := by
    rw [show (fun x => lkSq x * id x) = (fun x => x ^ 3) from by funext x; simp [lkSq]; ring]
    -- atomic `½·0³ = 0`; continuous `½·∫₀¹ x³ = ½·(1/4) = 1/8`.
    rw [MixedDist.expect_eq, mixed_atoms, Finsupp.sum_single_index (by simp)]
    -- The density integral is `½·cu.expect(x³)`; compute `cu.expect(x³) = 1/4`.
    have hdens3 : (∫ x, mixed.density x * (fun x => x ^ 3) x) =
        (1 / 2 : ℝ) * cu.expect (fun x => x ^ 3) :=
      mixed_density_integral (fun x => x ^ 3)
    have hcu3 : cu.expect (fun x => x ^ 3) = 1 / 4 := by
      rw [ContDist.expect_eq_integral]
      rw [show (fun x => cu.density x * x ^ 3)
          = Set.indicator (Set.Icc 0 1) (fun x => x ^ 3) from by
        funext x
        rw [cu, ContDist.uniform_density]
        by_cases hx : x ∈ Set.Icc (0:ℝ) 1
        · rw [if_pos (by simpa [Set.mem_Icc] using hx), Set.indicator_of_mem hx]; norm_num
        · rw [if_neg (by simpa [Set.mem_Icc] using hx), Set.indicator_of_notMem hx, zero_mul]]
      rw [integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_pow]
      norm_num
    rw [hdens3, hcu3]
    norm_num
  rw [hcube]; norm_num

end bayes

section mixture

/-! A concrete two-component mixture: the genuinely-mixed prior `mixed` (mean `1/4`) mixed at the
**asymmetric** weight `t = 1/3` with the pure point mass `atom1 = ofAtoms` at `1` (mean `1`). The
hand-computed mixture mean is `(1/3)·(1/4) + (2/3)·1 = 1/12 + 8/12 = 3/4`. The asymmetric weight is
essential: at `t = 1/2` the two component means `1/4` and `1` enter symmetrically, so a weight swap
`t ↔ 1 − t` would be invisible; at `t = 1/3` the swap gives `(2/3)·(1/4) + (1/3)·1 = 1/2 ≠ 3/4`. -/

/-- The pure atom at `1`, with all its mass on the single location `1` (mean `1`). -/
private abbrev atom1 : MixedDist := MixedDist.ofAtoms ![1] (finDist% ![1])

/-- The atom-at-`1` law has mean `1` (its only support point). -/
private theorem atom1_expect_id : atom1.expect id = 1 := by
  rw [MixedDist.ofAtoms_expect]
  simp

/-- The **asymmetric** mixing weight `t = 1/3 ∈ [0,1]`. -/
private abbrev thirdWeight : unitInterval := ⟨1 / 3, by norm_num⟩

/-- **`expect_mixture` — the mixed mean decomposes by the mixing weight.** The `1/3`-`2/3`
mixture of the mixed prior `mixed` (mean `1/4`) and the point mass `atom1` (mean `1`) has mean
`(1/3)·(1/4) + (2/3)·1 = 3/4`. The density-against-`id` integrability side conditions are discharged
concretely: `mixed` via `mixed_density_mul_integrable`, and `atom1` because its density is the zero
function. A weight swap (mixing at `t` vs `1 − t`) would move the mean to `1/2`, off `3/4`. -/
theorem mixed_expect_mixture :
    (MixedDist.mixture thirdWeight mixed atom1).expect id = 3 / 4 := by
  -- `mixed`'s density-against-`id` is integrable; `atom1`'s density is `0`, hence integrable.
  have hf₁ := mixed_density_mul_integrable (f := id) continuous_id
  have hf₂ : Integrable (fun x => atom1.density x * id x) := by
    simp only [atom1, MixedDist.ofAtoms, zero_mul]
    exact integrable_zero _ _ _
  rw [MixedDist.expect_mixture thirdWeight mixed atom1 id hf₁ hf₂, mixed_expect_id, atom1_expect_id]
  -- `(1/3)·(1/4) + (1 − 1/3)·1 = 3/4`.
  change (1 / 3 : ℝ) * (1 / 4) + (1 - 1 / 3) * 1 = 3 / 4
  norm_num

end mixture

end EconlibTest.Probability.MixedDist

end
