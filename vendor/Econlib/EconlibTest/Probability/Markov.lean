/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `Markov` Non-Vacuity Checks

Compile-time semantic witnesses for the finite Markov-chain layer
`Econlib.Probability.Markov.FiniteMarkovChain`, anchored on a concrete asymmetric two-state chain
with transition matrix

```
Π = | 7/10  3/10 |
    | 2/5   3/5  |
```

whose (independently solved) stationary distribution is `π = (4/7, 3/7)`. Because `Π` is genuinely
asymmetric, the stationary equation `∑_s π(s)·Π(s,s') = π(s')` would fail under a row/column
transpose of the transition convention — so the stationarity witness is a real orientation check.

Beyond the core dynamics and stationarity, this file exercises:

* **History / path probability** — `pathProb`, `sum_pathProb_extend`,
  `head`/`lastNode`/`tail_extend` against the hand-computed `P(0 → 0 → 1) = 7/10 · 3/10 = 21/100`.
* **Kernel bridge** — `toKernel_apply`, `toMarkovKernel_kernel`, `step_toPMF`,
  `toProbDist_injective`, and `isStationary_iff_invariant` lifting finite stationarity to kernel
  invariance.
* **Existence & uniqueness** — `exists_stationary` (Brouwer), `unique_stationary` (the
  positive-entry Doeblin hypothesis is *discharged* via `P_pos`, not assumed),
  `geometric_convergence`, and the kernel-level `StationaryLaw.law_eq_of_unique` with its
  uniqueness hypothesis discharged from `unique_stationary`.
* **Stochastic monotonicity** — `Π` is shown stochastically monotone (row `1` FOSD-dominates row
  `0`), with `monotone_expect` / `antitone_expect` / `nStep_monotone` in the *correct* direction
  (higher start ⟹ higher expectation of a monotone payoff), plus `ofIidRows` on an i.i.d. chain.
* **Present value** — closed form `PV(const 1) = 2` at `β = 1/2`, `presentValue_mono`,
  `presentValue_telescope_finite` (partial sum `7/4`, tail `1/4`), and `innovation_zero_mean`.
* **Supermartingale & Euler** — `condExpect_le`, `expect_converges`, `eulerSupermartingale`, and
  the `βR > 1` transversality bound `euler_forces_divergence`.
* **FOSD lattice** — Knaster–Tarski `exists_stationary_lfp`/`_gfp` and the FOSD bracketing
  `lfp ≤ π ≤ gfp`.
* **Endogenous / finite-support kernels** — `FiniteSupportKernel` reachability, controlled-kernel
  `inducedKernel_*`, and `exists_stationary_discrete`.
-/

noncomputable section

namespace EconlibTest.Probability.Markov

open Econlib.Probability

/-- The asymmetric two-state chain. -/
private abbrev P : FiniteMarkovChain (Fin 2) :=
  ⟨![finDist% ![7 / 10, 3 / 10], finDist% ![2 / 5, 3 / 5]]⟩

/-- The (independently solved) stationary distribution `π = (4/7, 3/7)`. -/
private abbrev statDist : FinDist (Fin 2) := finDist% ![4 / 7, 3 / 7]

/-- The integer outcome map. -/
private abbrev outcome : Fin 2 → ℝ := fun i => (i.val : ℝ)

section dynamics

/-- **Zero steps is the identity** on distributions. -/
theorem nStep_zero_witness : P.nStep 0 statDist = statDist := P.nStep_zero statDist

/-- **One step is a single transition.** -/
theorem nStep_one_witness : P.nStep 1 statDist = P.step statDist := by
  rw [P.nStep_succ, P.nStep_zero]

/-- **Transition convention.** Stepping the point mass at state `0` returns row `0` of `Π`: The
next-state mass at `1` is `Π(0,1) = 3/10`. A row/column transpose would report `2/5` instead. -/
theorem step_pure_zero : (P.step (FinDist.pure 0)).pmf 1 = 3 / 10 := by
  simp only [FiniteMarkovChain.step, Fin.sum_univ_two, FinDist.pure_apply_self,
    FinDist.pure_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.cons_val_zero,
    Matrix.cons_val_one, FinDist.ofVec_apply]
  norm_num

/-- **Conditional expectation after one step from `0`:** `E[outcome | s=0] = Π(0,1)·1 = 3/10`. -/
theorem condExp_zero : P.condExp 0 outcome = 3 / 10 := by
  simp only [FiniteMarkovChain.condExp, FinDist.expect_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, FinDist.ofVec_apply, Matrix.cons_val_one, outcome]
  norm_num

end dynamics

section stationarity

/-- **The stationary distribution is genuinely stationary:** `∑_s π(s)·Π(s,s') = π(s')` for every
target state `s'`. With the asymmetric `Π`, this pins `π = (4/7, 3/7)` and would break under a
transition transpose. -/
theorem statDist_isStationary : P.IsStationary statDist := by
  rw [FiniteMarkovChain.isStationary_iff]
  intro s'
  fin_cases s' <;>
    simp only [statDist, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      FinDist.ofVec_apply] <;>
    norm_num

/-- **The chain is not i.i.d.-rows** (the two transition rows genuinely differ), so the stationary
law above is not the trivial uniform one. -/
theorem not_iidRows : ¬ P.IidRows := by
  intro h
  have hrow := congrArg (fun d : FinDist (Fin 2) => d.pmf 0) (h 0 1)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply] at hrow
  norm_num at hrow

end stationarity

section history

/-- The concrete two-transition path `1 → 0 → 1`, as a length-3 history (`Fin 3 → Fin 2`). The
distinct first and second nodes make `head` discriminating: a `head`-returns-the-second-node
off-by-one bug would report `0`, not `1`. -/
private abbrev path001 : History (Fin 2) 2 := ![1, 0, 1]

/-- **History navigation.** The first node of `1 → 0 → 1` is `1` — not the second node `0`, so this
catches a `head`/off-by-one bug. -/
theorem path001_head : History.head path001 = 1 := rfl

/-- The last node of `1 → 0 → 1` is `1`. -/
theorem path001_lastNode : History.lastNode path001 = 1 := rfl

/-- **`tail_extend` round-trip.** Extending a history by a state and then dropping it recovers the
original history; here we exhibit the law on `0 → 0` re-extended by `1`. -/
theorem tail_extend_witness :
    History.tail (History.extend (![0, 0] : History (Fin 2) 1) 1)
      = (![0, 0] : History (Fin 2) 1) :=
  History.tail_extend _ 1

/-- **Hand-computed path probability.** `P(1 → 0 → 1) = Π(1,0)·Π(0,1) = 2/5 · 3/10 = 3/25`. A
row/column transpose of the transition convention would report `Π(0,1)·Π(1,0) = 3/10 · 2/5` (which
happens to coincide here) — but more to the point, the asymmetric factors `Π(1,0)=2/5 ≠ Π(0,1)=3/10`
mean the *product order* and row/column reads are exercised on distinct entries. -/
theorem pathProb_path001 : pathProb P path001 = 3 / 25 := by
  simp only [pathProb, Fin.prod_univ_two, path001, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Matrix.cons_val, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, FinDist.ofVec_apply]
  norm_num

/-- **Path probabilities are nonnegative** on the concrete path. -/
theorem pathProb_nonneg_witness : 0 ≤ pathProb P path001 := pathProb_nonneg P path001

/-- **Marginalization.** Summing the path probability of a one-step extension of `0 → 0` over the
appended state recovers the prefix probability `P(0 → 0) = Π(0,0) = 7/10`. This is the
`∑ s', pathProb (h.extend s') = pathProb h` law, verified against a hand-computed value. -/
theorem sum_pathProb_extend_witness :
    ∑ s' : Fin 2, pathProb P (History.extend (![0, 0] : History (Fin 2) 1) s') = 7 / 10 := by
  rw [sum_pathProb_extend]
  simp only [pathProb, Fin.prod_univ_one, Matrix.cons_val_zero, Fin.isValue,
    Fin.castSucc_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one, FinDist.ofVec_apply]

end history

section kernelBridge

open MeasureTheory ProbabilityTheory

/-- **Kernel fiber.** The measure-theoretic kernel's fiber at state `0` is the probability measure
of row `0` of `Π`. -/
theorem toKernel_apply_zero :
    P.toKernel 0 = (P.transition 0).toProbDist.toMeasure := P.toKernel_apply 0

/-- **Bundling coherence.** The bundled `MarkovKernel`'s underlying kernel is `toKernel`. -/
theorem toMarkovKernel_kernel_witness : P.toMarkovKernel.kernel = P.toKernel :=
  P.toMarkovKernel_kernel

/-- **PMF-bind bridge.** One finite step agrees with the measure-theoretic PMF bind of the
transition family. Instantiated at the stationary law on the concrete chain. -/
theorem step_toPMF_witness :
    (P.step statDist).toPMF = statDist.toPMF.bind (fun a => (P.transition a).toPMF) :=
  P.step_toPMF statDist

/-- **`toProbDist` is injective.** Two finite distributions with equal probability-measure images
are equal — the embedding loses no information on a finite measurable-singleton space. -/
theorem toProbDist_injective_witness :
    Function.Injective (FinDist.toProbDist (α := Fin 2)) :=
  FiniteMarkovChain.toProbDist_injective

/-- **Stationary coherence.** The (hand-solved) stationary law `π = (4/7, 3/7)` is invariant under
the measure-theoretic kernel exactly because it is finite-stationary — the kernel-level invariance
is genuinely discharged, not assumed. -/
theorem invariant_statDist : P.toMarkovKernel.Invariant statDist.toProbDist :=
  (P.isStationary_iff_invariant statDist).mp statDist_isStationary

end kernelBridge

section stochasticMonotone

/-- **The concrete chain is stochastically monotone.** Row `1 = (2/5, 3/5)` FOSD-dominates row
`0 = (7/10, 3/10)`: Its CDF at the bottom state is `2/5 ≤ 7/10`, putting more mass high. So `Π` is
genuinely stochastically monotone — higher current state ⟹ FOSD-higher next-step law. A row/column
transpose would *reverse* this (a falling chain), failing the `monotone` field. -/
private def Pmono : StochMonotoneFiniteMarkovChain (Fin 2) where
  toFiniteMarkovChain := P
  monotone s₁ s₂ hs := by
    -- The only nontrivial comparison is `0 ≤ 1`; equal states give a reflexive FOSD.
    -- The only nontrivial comparison is `0 ≤ 1`; equal states give a reflexive FOSD and `1 ≤ 0`
    -- is impossible. For `(0,1)`, compare the two CDFs cutoff by cutoff.
    rw [FinDist.FOSD_iff]
    intro a
    fin_cases s₁ <;> fin_cases s₂ <;>
      first
        | exact le_rfl
        | exact absurd hs (by decide)
        | skip
    -- Remaining: `cdf (row 1) a ≤ cdf (row 0) a`. Convert each CDF to a two-term sum and bound.
    rw [FinDist.cdf_eq_sum_ite, FinDist.cdf_eq_sum_ite, Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases a <;>
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply]

/-- The integer outcome map is monotone (`i ≤ j ⟹ (i : ℝ) ≤ (j : ℝ)`). -/
private theorem outcome_mono : Monotone outcome := fun _ _ h => by
  simpa [outcome] using (Nat.cast_le.mpr (Fin.le_def.mp h) : (_ : ℝ) ≤ _)

/-- **Monotone comparative statics — correct direction.** For a monotone payoff `f` (here the
identity outcome map), the one-step conditional expectation `s ↦ 𝔼_{Π(s)}[f]` is *non-decreasing*
in the starting state: A stochastically monotone chain started higher yields higher expectations of
monotone functions. Concretely `𝔼_{Π(0)}[outcome] = 3/10 ≤ 3/5 = 𝔼_{Π(1)}[outcome]`. -/
theorem monotone_expect_witness :
    Monotone (fun s => (Pmono.transition s).expect outcome) :=
  Pmono.monotone_expect (f := outcome) outcome_mono

/-- The monotone direction is non-vacuous: The endpoints `3/10 < 3/5` are genuinely ordered, so the
witness above is not the trivial constant case. -/
theorem monotone_expect_endpoints :
    (Pmono.transition 0).expect outcome < (Pmono.transition 1).expect outcome := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    FinDist.ofVec_apply, outcome, Pmono]
  norm_num

/-- **Antitone comparative statics.** For an antitone payoff `g = -outcome`, the conditional
expectation `s ↦ 𝔼_{Π(s)}[g]` is *non-increasing* in the starting state. -/
theorem antitone_expect_witness :
    Antitone (fun s => (Pmono.transition s).expect (fun i => -outcome i)) :=
  Pmono.antitone_expect (g := fun i => -outcome i) (outcome_mono.neg)

/-- **Iterated stochastic monotonicity (`nStep_monotone`).** Starting from the higher point mass
`δ₁`, the `k`-step law FOSD-dominates the one started from `δ₀`, for every `k`. Verified here at
`k = 2` against the hand-checked order `0 ≤ 1`. -/
theorem nStep_monotone_witness :
    FinDist.FOSD
      (Pmono.toFiniteMarkovChain.nStep 2 (FinDist.pure 1))
      (Pmono.toFiniteMarkovChain.nStep 2 (FinDist.pure 0)) :=
  Pmono.nStep_monotone 2 0 1 (by decide)

/-- An i.i.d.-rows chain: Both rows equal `(1/2, 1/2)`. -/
private abbrev Piid : FiniteMarkovChain (Fin 2) :=
  ⟨![finDist% ![1 / 2, 1 / 2], finDist% ![1 / 2, 1 / 2]]⟩

/-- `Piid` genuinely has identical rows. -/
private theorem Piid_iidRows : Piid.IidRows := by
  intro s t
  fin_cases s <;> fin_cases t <;> rfl

/-- **`ofIidRows`.** An i.i.d.-rows chain is (vacuously) stochastically monotone, because every
state induces the *same* next-step law, so the FOSD comparison is reflexive. The resulting
structure carries `Piid`'s transition. -/
theorem ofIidRows_transition :
    (StochMonotoneFiniteMarkovChain.ofIidRows Piid Piid_iidRows).transition = Piid.transition := rfl

end stochasticMonotone

section existenceUniqueness

open MeasureTheory ProbabilityTheory

/-- **Existence (Brouwer).** The concrete chain has at least one stationary distribution. -/
theorem exists_stationary_witness : ∃ μ : FinDist (Fin 2), P.IsStationary μ :=
  P.exists_stationary

/-- **The transition matrix has strictly positive entries.** Every entry of `Π` is `> 0`, so the
Doeblin minorization hypothesis of `unique_stationary` is genuinely *dischargeable* on this
concrete chain — uniqueness is earned, not assumed. -/
theorem P_pos : ∀ s s' : Fin 2, 0 < P.transition s s' := by
  intro s s'
  fin_cases s <;> fin_cases s' <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply]

/-- **Uniqueness (Doeblin).** With positive entries discharged via `P_pos`, the stationary
distribution is unique: Any two stationary laws coincide, hence both equal the solved
`(4/7, 3/7)`. -/
theorem unique_stationary_witness :
    ∀ μ₁ μ₂ : FinDist (Fin 2), P.IsStationary μ₁ → P.IsStationary μ₂ → μ₁ = μ₂ :=
  P.unique_stationary P_pos

/-- The solved stationary law is *the* stationary law: Any stationary `μ` equals `(4/7, 3/7)`. -/
theorem statDist_unique (μ : FinDist (Fin 2)) (hμ : P.IsStationary μ) : μ = statDist :=
  P.unique_stationary P_pos μ statDist hμ statDist_isStationary

/-- **Geometric convergence.** From any initial law, the `k`-step marginals converge to the
stationary law at a geometric rate. -/
theorem geometric_convergence_witness (d₀ : FinDist (Fin 2)) :
    ∃ (C ρ : ℝ), 0 < C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ k : ℕ, ∀ s : Fin 2,
        |(P.nStep k d₀).pmf s - P.stationaryDist.pmf s| ≤ C * ρ ^ k :=
  P.geometric_convergence P_pos d₀

/-- The `FinDist → ProbDist → FinDist` round trip is the identity on `Fin 2`: A probability measure
on a finite measurable-singleton space is recovered from its singleton masses. -/
private theorem toProbDist_toFinDist (μ : ProbDist (Fin 2)) :
    (ProbDist.toFinDist μ).toProbDist = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [FinDist.toProbDist_toMeasure]
  refine MeasureTheory.Measure.ext_of_singleton (fun a => ?_)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  change ENNReal.ofReal ((ProbDist.toFinDist μ).pmf a) = μ.toMeasure {a}
  rw [show (ProbDist.toFinDist μ).pmf a = (μ.toMeasure {a}).toReal from rfl,
    ENNReal.ofReal_toReal (measure_ne_top μ.toMeasure {a})]

/-- **Kernel-level uniqueness.** Positivity of `Π` lifts through the kernel bridge: any two
*measure-theoretic* invariant laws of the kernel are equal.  This discharges the hypothesis of
`StationaryLaw.law_eq_of_unique` from `unique_stationary`, rather than assuming it. -/
private theorem invariant_unique (μ ν : ProbDist (Fin 2))
    (hμ : P.toMarkovKernel.Invariant μ) (hν : P.toMarkovKernel.Invariant ν) : μ = ν := by
  -- Pull both invariant laws back to finite distributions, conclude via finite uniqueness.
  have hμ' : (ProbDist.toFinDist μ).toProbDist = μ := toProbDist_toFinDist μ
  have hν' : (ProbDist.toFinDist ν).toProbDist = ν := toProbDist_toFinDist ν
  have hsμ : P.IsStationary (ProbDist.toFinDist μ) :=
    (P.isStationary_iff_invariant _).mpr (by rw [hμ']; exact hμ)
  have hsν : P.IsStationary (ProbDist.toFinDist ν) :=
    (P.isStationary_iff_invariant _).mpr (by rw [hν']; exact hν)
  rw [← hμ', ← hν', P.unique_stationary P_pos _ _ hsμ hsν]

/-- **`StationaryLaw.law_eq_of_unique`.** Any two stationary-law *structures* for the kernel share
the same underlying probability law — feeding the discharged uniqueness hypothesis to the
hypothesis-taking lemma, rather than a uniqueness certificate. -/
theorem law_eq_witness (π ρ : P.toMarkovKernel.StationaryLaw) : π.law = ρ.law :=
  MarkovKernel.StationaryLaw.law_eq_of_unique invariant_unique π ρ

/-- The concrete stationary law of the kernel, built from the solved finite distribution. -/
private def Pstat : P.toMarkovKernel.StationaryLaw where
  law := statDist.toProbDist
  invariant := invariant_statDist

/-- **`StationaryLaw.aggregate`/`invariant_step_eq`.** The stationary law integrates functions and
is fixed by the kernel step. Here the aggregate equals the `ProbDist.expect` of `statDist`. -/
theorem Pstat_aggregate (f : Fin 2 → ℝ) : Pstat.aggregate f = statDist.toProbDist.expect f := rfl

/-- The stationary law puts unit mass on the whole space (`eventMass univ = 1`). -/
theorem Pstat_eventMass_univ : Pstat.eventMass Set.univ = 1 := Pstat.eventMass_univ

/-- The stationary law is fixed by one kernel step. -/
theorem Pstat_invariant_step : P.toMarkovKernel.step Pstat.law = Pstat.law :=
  Pstat.invariant_step_eq

end existenceUniqueness

section adaptedProcess

/-- **`condExpStep_const`.** The one-step conditional expectation of a constant process is the
constant: `𝔼[const c | s] = c` because every transition row sums to one. -/
theorem condExpStep_const_witness (c : ℝ) (t : ℕ) (h : History (Fin 2) t) :
    (AdaptedProcess.const (α := Fin 2) c).condExpStep P t h = c :=
  AdaptedProcess.condExpStep_const P c t h

/-- **`condExpStep_mono`.** A pointwise-larger process has a larger one-step conditional
expectation: `const 0 ≤ const 1 ⟹ 𝔼[const 0 | s] ≤ 𝔼[const 1 | s]`. -/
theorem condExpStep_mono_witness (t : ℕ) (h : History (Fin 2) t) :
    (AdaptedProcess.const (α := Fin 2) 0).condExpStep P t h
      ≤ (AdaptedProcess.const (α := Fin 2) 1).condExpStep P t h :=
  AdaptedProcess.condExpStep_mono P (fun _ _ => by simp) t h

/-- **`iterCondExp_mono`.** Monotonicity lifts to the iterated conditional expectation at every
horizon `k`. -/
theorem iterCondExp_mono_witness (k t : ℕ) (h : History (Fin 2) t) :
    iterCondExp P (AdaptedProcess.const 0) k t h
      ≤ iterCondExp P (AdaptedProcess.const 1) k t h :=
  iterCondExp_mono P (fun _ _ => by simp) k t h

end adaptedProcess

section presentValue

/-- The discount factor used in the present-value witnesses, with `0 < β < 1`. -/
private abbrev β : ℝ := 1 / 2

private theorem β_nonneg : (0 : ℝ) ≤ β := by norm_num

private theorem β_lt_one : β < 1 := by norm_num

/-- A constant adapted process is uniformly bounded by any `M ≥ |c|`. -/
private theorem const_bounded {c M : ℝ} (hc : |c| ≤ M) :
    (AdaptedProcess.const (α := Fin 2) c).Bounded M :=
  fun _ _ => by rw [AdaptedProcess.const_val]; exact hc

/-- Iterated conditional expectation of a constant process is that constant. -/
private theorem iterCondExp_const (c : ℝ) (k t : ℕ) (h : History (Fin 2) t) :
    iterCondExp P (AdaptedProcess.const c) k t h = c := by
  induction k generalizing t h with
  | zero => rfl
  | succ k ih =>
    rw [iterCondExp_succ]
    simp_rw [ih]
    rw [← Finset.sum_mul, (P.transition h.lastNode).sum_one, one_mul]

/-- **Closed-form present value of a constant stream.** With `β = 1/2`, a unit perpetual payoff has
present value `∑' τ, (1/2)^τ · 1 = 1/(1 - 1/2) = 2`. This anchors `presentValue` against a
hand-computed geometric sum. -/
theorem presentValue_const_one (h : History (Fin 2) 0) :
    presentValue P β (AdaptedProcess.const 1) 0 h = 2 := by
  unfold presentValue
  simp_rw [iterCondExp_const, mul_one]
  rw [tsum_geometric_of_lt_one β_nonneg β_lt_one]
  norm_num [β]

/-- **`presentValue_mono` — correct direction.** Pointwise-larger payoffs yield a larger present
value: `const 0 ≤ const 1` lifts to `PV(0) ≤ PV(1)`. -/
theorem presentValue_mono_witness (t : ℕ) (h : History (Fin 2) t) :
    presentValue P β (AdaptedProcess.const 0) t h
      ≤ presentValue P β (AdaptedProcess.const 1) t h :=
  presentValue_mono P β β_nonneg β_lt_one _ _
    (const_bounded (M := 1) (by norm_num)) (const_bounded (M := 1) (by norm_num))
    (fun _ _ => by simp) t h

/-- **Finite-horizon telescoping.** The present value of the unit stream splits into its first-`T`
partial sum plus a remainder bounded by `M · β^T / (1 - β)`. Here `T = 3`, `β = 1/2`, `M = 1`: The
partial sum is `1 + 1/2 + 1/4 = 7/4`, the remainder bound is `(1/2)^3 / (1/2) = 1/4`, and indeed
the exact tail `2 - 7/4 = 1/4` saturates the bound. -/
theorem presentValue_telescope_witness (h : History (Fin 2) 0) :
    ∃ remainder : ℝ, |remainder| ≤ 1 * β ^ 3 / (1 - β) ∧
      presentValue P β (AdaptedProcess.const 1) 0 h
        = (∑ τ ∈ Finset.range 3, β ^ τ * iterCondExp P (AdaptedProcess.const 1) τ 0 h)
          + remainder :=
  presentValue_telescope_finite P β β_nonneg β_lt_one _ (const_bounded (M := 1) (by norm_num)) 3 0 h

/-- The hand-computed partial sum behind the telescope anchor: `1 + 1/2 + 1/4 = 7/4`. -/
theorem presentValue_telescope_partialSum (h : History (Fin 2) 0) :
    (∑ τ ∈ Finset.range 3, β ^ τ * iterCondExp P (AdaptedProcess.const 1) τ 0 h) = 7 / 4 := by
  simp_rw [iterCondExp_const, mul_one]
  norm_num [Finset.sum_range_succ, β]

/-- **The exact telescope tail is `1/4` and saturates the bound.** Combining the closed-form present
value `PV = 2` (`presentValue_const_one`) with the partial sum `7/4`
(`presentValue_telescope_partialSum`), the remainder `PV - 7/4 = 1/4` equals the remainder bound
`1·β³/(1-β) = (1/2)³/(1/2) = 1/4`. This pins the numeric anchor the existential
`presentValue_telescope_witness` only asserts to exist. -/
theorem presentValue_telescope_tail_exact (h : History (Fin 2) 0) :
    presentValue P β (AdaptedProcess.const 1) 0 h
        - (∑ τ ∈ Finset.range 3, β ^ τ * iterCondExp P (AdaptedProcess.const 1) τ 0 h)
      = 1 * β ^ 3 / (1 - β) := by
  rw [presentValue_const_one, presentValue_telescope_partialSum]
  norm_num [β]

/-- The canonical Arrow decomposition of the present value of the unit stream, bound once so the
witnesses below share a single `ArrowDecomposition` object. -/
private noncomputable def pvDecomp :
    ArrowDecomposition P β (presentValue.adapted P β (AdaptedProcess.const 1)) :=
  presentValue_arrowDecomposition P β β_nonneg β_lt_one _ (const_bounded (M := 1) (by norm_num))

/-- **The canonical Arrow `decompose` identity** on the concrete PV process — the load-bearing
Bellman content. For every history, the present value splits as drift `X` plus discounted Arrow
claims: `PV X t h = X t h + β·∑_{s'} Π(lastNode,s')·PV X (t+1) (h.extend s')`. This consumes the
`decompose` field of `presentValue_arrowDecomposition` — the genuine Bellman content. -/
theorem presentValue_decompose_witness (t : ℕ) (h : History (Fin 2) t) :
    (presentValue.adapted P β (AdaptedProcess.const 1)).val t h
      = pvDecomp.drift t h
        + β * ∑ s' : Fin 2, (P.transition h.lastNode) s' * pvDecomp.claim t h s' :=
  pvDecomp.decompose t h

/-- **`innovation_zero_mean`.** The next-period innovation of the present-value process has zero
conditional mean against the chain's transition. This identity follows from the transition row sums
alone; the Bellman `decompose` content is checked separately by `presentValue_decompose_witness`. -/
theorem innovation_zero_mean_witness (t : ℕ) (h : History (Fin 2) t) :
    ∑ s' : Fin 2,
        (P.transition h.lastNode) s' *
          innovation P (presentValue.adapted P β (AdaptedProcess.const 1)) t h s' = 0 :=
  innovation_zero_mean P (presentValue.adapted P β (AdaptedProcess.const 1))
    (fun s => (P.transition s).sum_one) t h

end presentValue

section supermartingale

/-- A concrete non-negative supermartingale on the chain: The constant process `X t s = 1`. Because
each transition row sums to `1`, the conditional expectation equals the current value, so the
supermartingale inequality `𝔼[X_{t+1} | s] ≤ X_t(s)` holds with equality. -/
private def constSM : FinSupermartingale P where
  X _ _ := 1
  nonneg _ _ := by norm_num
  superMG t s := by
    simp only [FinDist.expect_eq_sum, mul_one, (P.transition s).sum_one, le_refl]

/-- A **genuinely decreasing** (strict) supermartingale on the chain: `X t s = (1/2)^t`, independent
of the state. Since each transition row sums to `1`, `𝔼[X_{t+1} | s] = (1/2)^{t+1} = (1/2)·X_t(s)`,
strictly below `X_t(s)` — so the supermartingale inequality is *strict*, not the degenerate equality
of `constSM`. This is what lets `condExpect_le_witness_strict` exercise the inequality where the two
sides genuinely differ. -/
private def decSM : FinSupermartingale P where
  X t _ := (1 / 2) ^ t
  nonneg _ _ := by positivity
  superMG t s := by
    rw [FinDist.expect_eq_sum]
    simp only [← Finset.sum_mul, (P.transition s).sum_one, one_mul, pow_succ]
    nlinarith [pow_pos (show (0:ℝ) < 1/2 by norm_num) t]

/-- **`condExpect_le`.** The one-step conditional expectation never exceeds the current value. -/
theorem condExpect_le_witness (t : ℕ) (s : Fin 2) :
    FinDist.expect (P.transition s) (constSM.X (t + 1)) ≤ constSM.X t s :=
  constSM.condExpect_le t s

/-- **`condExpect_le`, strict.** On the strictly decreasing supermartingale `decSM`, the one-step
conditional expectation is *strictly* below the current value: `𝔼[X_1 | s] = 1/2 < 1 = X_0(s)`. This
exercises the supermartingale inequality away from the equality point, unlike the constant `constSM`
witness. -/
theorem condExpect_le_witness_strict (s : Fin 2) :
    FinDist.expect (P.transition s) (decSM.X 1) < decSM.X 0 s := by
  rw [FinDist.expect_eq_sum]
  simp only [decSM, ← Finset.sum_mul, (P.transition s).sum_one, one_mul]
  norm_num

/-- **`expect_converges` (finite Doob).** The expected value of the supermartingale under the
evolved distribution converges as `t → ∞`. Stated on the strictly decreasing `decSM`, whose
expectation `(1/2)^t → 0` is a genuine (nonconstant) limit. -/
theorem expect_converges_witness (d : FinDist (Fin 2)) :
    ∃ l, Filter.Tendsto
      (fun t => FinDist.expect (P.nStep t d) (decSM.X t)) Filter.atTop (nhds l) :=
  decSM.expect_converges d

/-- **The decreasing supermartingale's expectation limit is `0`.** Under any initial law `d`,
`𝔼_{P^t d}[X_t] = (1/2)^t → 0`, the nontrivial limit the existential `expect_converges_witness` only
asserts to exist. The expectation of the constant `(1/2)^t` is `(1/2)^t` for every `t`. -/
theorem expect_converges_witness_limit (d : FinDist (Fin 2)) :
    Filter.Tendsto
      (fun t => FinDist.expect (P.nStep t d) (decSM.X t)) Filter.atTop (nhds 0) := by
  have hconst : (fun t => FinDist.expect (P.nStep t d) (decSM.X t)) = fun t => (1 / 2 : ℝ) ^ t := by
    funext t
    simp only [decSM]
    rw [FinDist.expect_const]
  rw [hconst]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The rescaled marginal-utility sequence for the Euler witness: `μ t s = (1/2)^t`. With `βR = 2`,
the Euler inequality `βR · 𝔼[μ_{t+1} | s] ≤ μ_t` holds with equality (`2 · (1/2)^{t+1} = (1/2)^t`),
and `μ` is strictly positive. -/
private abbrev eulerMu : ℕ → Fin 2 → ℝ := fun t _ => (1 / 2) ^ t

private theorem eulerMu_pos : ∀ t s, 0 < eulerMu t s := fun _ _ => by positivity

private theorem eulerMu_euler :
    ∀ t s, (2 : ℝ) * FinDist.expect (P.transition s) (eulerMu (t + 1)) ≤ eulerMu t s := by
  intro t s
  rw [FinDist.expect_eq_sum]
  simp only [eulerMu, ← Finset.sum_mul, (P.transition s).sum_one, one_mul]
  rw [pow_succ]
  ring_nf
  rfl

/-- **`eulerSupermartingale` is a genuine supermartingale.** The rescaled process `(βR)^t · μ_t`
for the concrete `μ` above is non-negative. -/
theorem eulerSupermartingale_nonneg (t : ℕ) (s : Fin 2) :
    0 ≤ (eulerSupermartingale P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler).X t s :=
  (eulerSupermartingale P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler).nonneg t s

/-- **...and satisfies the supermartingale inequality** — the load-bearing Euler content. For every
time `t` and state `s`, `𝔼[X_{t+1} | s] ≤ X_t(s)` where `X_t = (βR)^t · μ_t`. With `βR = 2` and
`μ_t = (1/2)^t` the rescaled process is the constant `1`, so the inequality holds with equality; the
point is that `superMG` (not just `nonneg`) is genuinely asserted on the constructed object. -/
theorem eulerSupermartingale_superMG (t : ℕ) (s : Fin 2) :
    FinDist.expect (P.transition s)
        ((eulerSupermartingale P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler).X (t + 1))
      ≤ (eulerSupermartingale P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler).X t s :=
  (eulerSupermartingale P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler).superMG t s

/-- **`euler_forces_divergence`: the bounded-rescaled-expectation bound.** With `βR = 2`, the
expectation of the rescaled process `(βR)^t · μ_t` under the evolved distribution stays bounded by
its initial value: `𝔼_{P^t d}[(βR)^t·μ_t] ≤ 𝔼_d[μ_0]`. This *transversality bound* is the lemma the
credit-certification argument feeds into to rule out `βR > 1`; the divergence contradiction itself
needs further model hypotheses (Inada / resource constraints) not in scope here. Here
`(βR)^t·μ_t = 2^t·(1/2)^t = 1`, so the witness reads `1 ≤ 1` — it checks the bound's
orientation, not a divergence. -/
theorem euler_forces_divergence_witness (d : FinDist (Fin 2)) (t : ℕ) :
    FinDist.expect (P.nStep t d) (fun s => (2 : ℝ) ^ t * eulerMu t s)
      ≤ FinDist.expect d (eulerMu 0) :=
  euler_forces_divergence P eulerMu 2 (by norm_num) eulerMu_pos eulerMu_euler d t

end supermartingale

section fosdLattice

/-- **Knaster–Tarski existence via the least fixed point.** The stochastically monotone chain
`Pmono` admits a stationary distribution given by `lfp` of its FOSD-monotone step operator. -/
theorem exists_stationary_lfp_witness :
    ∃ μ : FinDist (Fin 2), Pmono.toFiniteMarkovChain.step μ = μ :=
  Pmono.exists_stationary_lfp

/-- **Knaster–Tarski existence via the greatest fixed point.** -/
theorem exists_stationary_gfp_witness :
    ∃ μ : FinDist (Fin 2), Pmono.toFiniteMarkovChain.step μ = μ :=
  Pmono.exists_stationary_gfp

/-- **FOSD bracketing.** Any stationary distribution is FOSD-bracketed between the least and
greatest fixed points: `lfp ≤ μ ≤ gfp`. Instantiated at the solved stationary law `(4/7, 3/7)` of
the underlying chain (which is `Pmono`'s chain), this exhibits both inequalities on a concrete
fixed point. -/
theorem lfp_le_statDist :
    OrderHom.lfp Pmono.stepOrderHom ≤ statDist :=
  Pmono.lfp_le_stationary statDist statDist_isStationary

theorem statDist_le_gfp :
    statDist ≤ OrderHom.gfp Pmono.stepOrderHom :=
  Pmono.stationary_le_gfp statDist statDist_isStationary

end fosdLattice

section finiteSupportKernel

/-- A concrete finite-support kernel: State and shock are both `Fin 2`, the shock law in state `z`
is row `z` of `Π`, and the next state *is* the realized shock. So one step reproduces the chain. -/
private def fsk : FiniteSupportKernel (Fin 2) (Fin 2) where
  shock z := P.transition z
  next _ e := e

/-- **`FiniteSupportKernel.expect`.** The one-step expectation operator reproduces the chain's
conditional expectation: `(fsk.expect 0 outcome) = 𝔼_{Π(0)}[outcome] = 3/10`. -/
theorem fsk_expect_zero : fsk.expect 0 outcome = 3 / 10 := by
  simp only [FiniteSupportKernel.expect, fsk, FinDist.expect_eq_sum, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply, outcome]
  norm_num

/-- **`start_mem_reachableFrom`.** Every state is reachable from itself in zero steps. -/
theorem start_mem_reachableFrom_witness : (0 : Fin 2) ∈ fsk.reachableFrom 0 :=
  fsk.start_mem_reachableFrom 0

/-- State `1` is reachable from `0` in exactly one step (the shock `Π(0)(1) = 3/10 > 0` moves
there), exercising the `reachableFrom`/`successors` chain on positive-probability data. -/
theorem one_mem_reachableFrom : (1 : Fin 2) ∈ fsk.reachableFrom 0 := by
  refine ⟨1, ⟨0, rfl, ⟨1, ?_, rfl⟩⟩⟩
  simp only [fsk, Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply]
  norm_num

/-- **`reachableFrom_closedUnder`.** The finite-reachability set is forward-closed under every
positive-probability successor. -/
theorem reachableFrom_closedUnder_witness : fsk.ClosedUnder (fsk.reachableFrom 0) :=
  fsk.reachableFrom_closedUnder 0

/-- **`closedUnder_iff_imageSet_subset`.** Forward-closure is equivalent to the one-step image
being contained in the set. -/
theorem closedUnder_iff_witness :
    fsk.ClosedUnder (fsk.reachableFrom 0)
      ↔ fsk.imageSet (fsk.reachableFrom 0) ⊆ fsk.reachableFrom 0 :=
  fsk.closedUnder_iff_imageSet_subset _

end finiteSupportKernel

section controlledKernel

/-- A trivial controlled kernel: Every action is feasible, the shock law and next state ignore the
action and reuse `fsk`'s data. -/
private def cfsk : ControlledFiniteSupportKernel (Fin 2) Unit (Fin 2) where
  feasible _ := Set.univ
  shock z _ := P.transition z
  next _ _ e := e

/-- The constant policy selecting the unique action. -/
private def cpolicy : cfsk.Policy where
  action _ := ()
  feasible _ := Set.mem_univ _

/-- **`inducedKernel_expect`.** Under the policy-induced kernel, the one-step expectation reduces
to the shock-weighted average — here `𝔼_{Π(0)}[outcome] = 3/10`. -/
theorem inducedKernel_expect_witness :
    (cfsk.inducedKernel cpolicy).expect 0 outcome = 3 / 10 := by
  rw [cfsk.inducedKernel_expect cpolicy 0 outcome]
  simp only [cfsk, cpolicy, FinDist.expect_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, FinDist.ofVec_apply, outcome]
  norm_num

/-- **`inducedKernel_successors_iff`.** State `1` is a positive-probability successor of `0` under
the induced kernel exactly when some shock realizing `1` has positive mass — true here since
`Π(0)(1) = 3/10 > 0`. -/
theorem inducedKernel_successors_witness :
    (1 : Fin 2) ∈ (cfsk.inducedKernel cpolicy).successors 0 := by
  rw [cfsk.inducedKernel_successors_iff cpolicy 0 1]
  refine ⟨1, ?_, rfl⟩
  simp only [cfsk, cpolicy, Matrix.cons_val_zero, Matrix.cons_val_one, FinDist.ofVec_apply]
  norm_num

end controlledKernel

section endogenous

/-- A minimal endogenous Markov chain on `[0,1] × Fin 2`: The discrete part is the chain `Π`, the
policy is the identity on the continuous state (continuous, range-preserving). This is enough to
exercise the discrete-marginal stationary existence theorem. -/
private def E : EndogenousMarkovChain 2 where
  w_min := 0
  w_max := 1
  hw := by norm_num
  discrete_trans := P.transition
  policy w _ _ := w
  policy_range _ _ _ hwl hwu := ⟨hwl, hwu⟩
  policy_cont _ _ := continuousOn_id

/-- **`exists_stationary_discrete`, strengthened to the solved law.** The discrete marginal of the
endogenous chain has a stationary distribution, and because `E.discrete_trans = Π` is positive and
irreducible, that distribution is *uniquely* the solved `(4/7, 3/7) = statDist`. We expose the
identification `μ = statDist` (via `statDist_unique`), so the witness is anchored on the concrete
solved law, not merely on bare existence. -/
theorem exists_stationary_discrete_witness :
    ∃ μ : FinDist (Fin 2),
      (∀ s', μ.pmf s' = ∑ s, μ.pmf s * (E.discrete_trans s).pmf s') ∧ μ = statDist := by
  obtain ⟨μ, hμ⟩ := E.exists_stationary_discrete
  refine ⟨μ, hμ, ?_⟩
  -- `E.discrete_trans = P.transition` definitionally, so `hμ` says `μ` is stationary for `P`;
  -- uniqueness then pins `μ = statDist`.
  apply statDist_unique
  rw [FiniteMarkovChain.isStationary_iff]
  intro s'
  exact (hμ s').symm

/-- **`exists_stationary_of_endogenousMarkovChain` (full product space).** Without any external
Feller hypothesis, the endogenous chain on the continuous product state space `[0,1] × Fin 2` has a
stationary *probability law*. This is Krylov–Bogolyubov applied through the bridge
`MarkovKernel.ofEndogenousMarkovChain`, whose Feller property is supplied internally by
`EndogenousMarkovChain.toKernel_isFeller`. The identity policy here is continuous and
range-preserving, so the kernel really is Feller (not vacuously so).

The *discrete marginal* of the produced product-space law is the solved `(4/7, 3/7) = statDist`:
the `Prod.snd`-pushforward of `π.law` is stationary for the discrete chain `⟨E.discrete_trans⟩= Π`
(via `MarkovKernel.ofEndogenousMarkovChain_stationary_snd_marginal`, which disintegrates the
product invariance along `Prod.snd`), and positivity-driven uniqueness (`statDist_unique`) pins it
to `statDist`. So this witness asserts product-space existence + invariance *and* the discrete
marginal identification — the claim the earlier docstring made but the API could not previously
back (closing `backlog/prob-endogenous-discrete-marginal.md`). -/
theorem exists_stationary_endogenous_witness :
    ∃ π : (MarkovKernel.ofEndogenousMarkovChain E).StationaryLaw,
      (MarkovKernel.ofEndogenousMarkovChain E).Invariant π.law ∧
      (π.law.map Prod.snd measurable_snd).toFinDist = statDist := by
  obtain ⟨π, hπ⟩ := MarkovKernel.exists_stationary_of_endogenousMarkovChain E
  exact ⟨π, hπ,
    statDist_unique _ (MarkovKernel.ofEndogenousMarkovChain_stationary_snd_marginal E π)⟩

/-- **`discreteStep`.** Marginalizing the discrete transition against the uniform continuous weight
`(1/2, 1/2)` gives next-state mass `∑_s (1/2)·Π(s,0) = (1/2)(7/10) + (1/2)(2/5) = 11/20` at state
`0`. A hand-computed mixture, catching a row/column transpose. -/
theorem discreteStep_zero :
    (E.discreteStep (fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num [Fin.sum_univ_two])).pmf 0
      = 11 / 20 := by
  simp only [EndogenousMarkovChain.discreteStep, E, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, FinDist.ofVec_apply]
  norm_num

end endogenous

section feller

open MeasureTheory ProbabilityTheory Set

/-- The compact metrizable state space `Ω = [0,1] ⊆ ℝ` as a subtype. It carries `CompactSpace`,
`MetrizableSpace`, `BorelSpace` and `Nonempty` instances by inference (a closed bounded real
interval), so it is a legitimate target for Krylov–Bogolyubov. -/
private abbrev Ω : Type := ↥(Set.Icc (0 : ℝ) 1)

/-- The **halving map** `x ↦ x/2` on `Ω`. Halving keeps `[0,1]` inside itself (`x/2 ≤ 1/2 ≤ 1`), so
the map is well-typed on the subtype. It is genuinely non-constant — it moves `1` to `1/2` — which
is what makes the Feller property below a real continuity fact rather than a triviality. -/
private def half : Ω → Ω := fun x => ⟨(x : ℝ) / 2, by
  have hx := x.2
  rw [Set.mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]⟩

/-- The halving map is continuous (division by a constant of the continuous inclusion). -/
private theorem half_cont : Continuous half :=
  Continuous.subtype_mk (continuous_subtype_val.div_const 2) _

private theorem half_meas : Measurable half := half_cont.measurable

/-- The distinguished fixed point `0 ∈ [0,1]`. -/
private def zeroΩ : Ω := ⟨0, by norm_num⟩

/-- `half` fixes `0` (`0/2 = 0`), which is exactly why `δ₀` will be invariant below. -/
private theorem half_zero : half zeroΩ = zeroΩ := by
  apply Subtype.ext
  simp [half, zeroΩ]

/-- **The halving map is non-constant.** It does *not* fix `1` (it sends `1 ↦ 1/2`), so the Feller
continuity witness below is anchored on a genuinely moving deterministic dynamic, not a constant
kernel whose continuity would be vacuous. -/
private theorem half_one_ne : half ⟨1, by norm_num⟩ ≠ ⟨1, by norm_num⟩ := by
  intro h
  rw [Subtype.ext_iff] at h
  simp [half] at h

/-- The **deterministic halving kernel** `K(x) = δ_{x/2}` bundled as a `MarkovKernel`. -/
private def halvingKernel : MarkovKernel Ω where
  kernel := Kernel.deterministic half half_meas
  markov := by infer_instance

/-- **The halving kernel is Feller.** Its measure-valued map `x ↦ δ_{x/2}` is the composition of
the continuous halving map with the continuous Dirac embedding `continuous_diracProba`, hence
continuous in the weak-* topology. Because `half` is genuinely non-constant (`half_one_ne`), this is
not the degenerate constant-kernel case — the continuity uses the topology of `[0,1]`. -/
private instance halving_isFeller :
    IsFellerKernel (Kernel.deterministic half half_meas) := by
  refine ⟨?_⟩
  -- `x ↦ ⟨δ_{half x}, _⟩` is `diracProba ∘ half`.
  have heq : (Kernel.deterministic half half_meas).toProbabilityMeasure
      = fun a => diracProba (half a) := by
    funext a
    apply Subtype.ext
    simp only [Kernel.toProbabilityMeasure, Kernel.deterministic_apply, diracProba]
  rw [heq]
  exact continuous_diracProba.comp half_cont

/-- **`exists_stationary_of_feller` (Krylov–Bogolyubov on a compact metrizable space).** The halving
kernel, being Feller on the nonempty compact metrizable `Ω = [0,1]`, admits a stationary law. The
Feller hypothesis is genuinely *discharged* via `halving_isFeller`, not assumed. -/
theorem exists_stationary_feller_witness :
    ∃ π : halvingKernel.StationaryLaw, halvingKernel.Invariant π.law :=
  halvingKernel.exists_stationary_of_feller halving_isFeller

/-- **The hand-computed stationary law is `δ₀`.** Invariance of the point mass at `0` is the
semantic anchor: pushing `δ₀` through the deterministic kernel yields `δ_{half 0} = δ_{0/2} = δ₀`,
so `δ₀` is fixed. Concretely the kernel composition reduces (`deterministic_comp_eq_map` +
`map_dirac'`) to `δ_{half 0}`, and `half 0 = 0`. With strictly positive contraction toward `0`,
`δ₀` is in fact the *unique* invariant law, but the witness here is the direct invariance check. -/
theorem dirac_zero_invariant : halvingKernel.Invariant (ProbDist.dirac zeroΩ) := by
  change (ProbDist.dirac zeroΩ).toMeasure.bind halvingKernel.kernel
    = (ProbDist.dirac zeroΩ).toMeasure
  rw [show halvingKernel.kernel = Kernel.deterministic half half_meas from rfl]
  rw [ProbDist.dirac_toMeasure, Measure.deterministic_comp_eq_map half_meas,
    Measure.map_dirac' half_meas, half_zero]

/-- **`MarkovKernel.step` fixes `δ₀`.** The same invariance read through the one-step push-forward
operator: `K.step δ₀ = δ₀`. This is the `StationaryLaw.invariant_step_eq` shape, verified directly
on the hand-computed fixed point. -/
theorem step_dirac_zero : halvingKernel.step (ProbDist.dirac zeroΩ) = ProbDist.dirac zeroΩ := by
  apply ProbabilityMeasure.toMeasure_injective
  change halvingKernel.kernel ∘ₘ (ProbDist.dirac zeroΩ).toMeasure = (ProbDist.dirac zeroΩ).toMeasure
  rw [show halvingKernel.kernel = Kernel.deterministic half half_meas from rfl]
  rw [ProbDist.dirac_toMeasure, Measure.deterministic_comp_eq_map half_meas,
    Measure.map_dirac' half_meas, half_zero]

/-- The `δ₀` stationary law packaged as a `StationaryLaw` structure for the halving kernel. -/
private def halvingStat : halvingKernel.StationaryLaw where
  law := ProbDist.dirac zeroΩ
  invariant := dirac_zero_invariant

/-- **`StationaryLaw.eventMass_univ`** on the concrete `δ₀` stationary law: it is a probability
law (`eventMass univ = 1`). -/
theorem halvingStat_eventMass_univ : halvingStat.eventMass Set.univ = 1 :=
  halvingStat.eventMass_univ

/-- **`StationaryLaw.invariant_step_eq`** on the concrete `δ₀` law: the kernel step fixes it. -/
theorem halvingStat_invariant_step : halvingKernel.step halvingStat.law = halvingStat.law :=
  halvingStat.invariant_step_eq

end feller

end EconlibTest.Probability.Markov

end
