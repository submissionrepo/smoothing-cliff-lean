/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Caratheodory
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.NoInformation
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Splitting
public import Econlib.Probability.FinDist.Literal

open BigOperators Econlib.Probability Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

/-!
# Step-Function Persuasion

Concavification results for step-function payoffs in Bayesian persuasion.

A step-function payoff arises when the receiver takes a binary action based on whether the
posterior mean exceeds a threshold `t`. The sender's payoff is 1 if the receiver acts and 0
otherwise. This is the canonical structure in rating design, certification, and investment problems
(Kamenica and Gentzkow 2011).

## Main definitions

* `stepPayoff` — the step-function sender payoff parameterized by a threshold `t`
* `stepConcaveClosure` — the candidate concave-closure value for `stepPayoff t` (coincides with the
  true concave closure under `stepConcaveClosure_eq`'s hypotheses: `0 < t < 1`, full-support prior
  below threshold; not the concave closure for `t ≥ 1`)
* `stepOptimalSignal` — the Kamenica–Gentzkow optimal binary signal, defined via its
  Bayes-plausible splitting (`stepOptimalWeights`, `stepOptimalBeliefs`)

## Main statements

* `stepPayoff_not_concave` — the step function violates concavity on the simplex
* `expectedSenderPayoff_le_stepConcaveClosure` — no signal structure beats the concave closure
* `stepOptimalSignal_payoff` — the optimal binary signal achieves the concave closure
* `posterior_stepOptimalSignal` / `signalMarginal_stepOptimalSignal` — its posteriors are the
  splitting beliefs and its signal law is the splitting weights
* `binarySignal_achieves_stepClosure` — existence form: A binary signal achieves the closure
* `posterior_dichotomy_of_optimal` — equality case of the upper bound: An optimal signal moves
  every positive-probability posterior to exactly `t` or to `0`
* `eq_stepOptimalSignal_of_optimal` — uniqueness: Up to the labeling of messages,
  `stepOptimalSignal` is the only optimal binary signal
* `stepConcaveClosure_eq` — `stepConcaveClosure t` equals the concave closure of `stepPayoff t`

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, concavification, step function, binary signal
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

/-- The step-function payoff: 1 if `μ.pmf 1 ≥ t`, else 0. Here `μ.pmf 1` is the probability of the
high type under posterior `μ`. -/
noncomputable def stepPayoff (t : ℝ) (μ : FinDist (Fin 2)) : ℝ :=
  if μ.pmf 1 ≥ t then 1 else 0

/-- `stepPayoff` is `1` once the high-type mass `μ.pmf 1` reaches the threshold `t`. -/
lemma stepPayoff_eq_one_of_le {t : ℝ} {μ : FinDist (Fin 2)} (h : t ≤ μ.pmf 1) :
    stepPayoff t μ = 1 := by unfold stepPayoff; exact if_pos h

/-- `stepPayoff` is `0` while the high-type mass `μ.pmf 1` stays below the threshold `t`. -/
lemma stepPayoff_eq_zero_of_lt {t : ℝ} {μ : FinDist (Fin 2)} (h : μ.pmf 1 < t) :
    stepPayoff t μ = 0 := by unfold stepPayoff; exact if_neg (not_le.mpr h)

/-- The candidate concave-closure value for `stepPayoff t`: `1` when `μ.pmf 1 ≥ t`, else
`μ.pmf 1 / t`. This coincides with the true `concaveClosure` of `stepPayoff t` under the hypotheses
of `stepConcaveClosure_eq` (`0 < t < 1`, full-support prior, `prior.pmf 1 < t`); for `t ≥ 1` it is
*not* the concave closure (e.g. `t > 1` makes `stepPayoff t ≡ 0`, closure `0`, while this is
positive whenever `μ.pmf 1 > 0`). -/
noncomputable def stepConcaveClosure (t : ℝ) (μ : FinDist (Fin 2)) : ℝ :=
  if μ.pmf 1 ≥ t then 1 else μ.pmf 1 / t

/-- The step function is not concave on the simplex when `0 < t < 1`. -/
theorem stepPayoff_not_concave (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    ¬ ConcaveOnSimplex (stepPayoff t) := by
  intro h_conc
  have ht2_pos : 0 < t / 2 := by linarith
  have ht2_lt_one : t / 2 < 1 := by linarith
  let prior : FinDist (Fin 2) := finDist% ![1 - t / 2, t / 2]
  have h_prior_pmf1 : prior.pmf 1 = t / 2 := by
    simp [prior, Matrix.cons_val_one]
  let weights : FinDist (Fin 2) := prior
  let beliefs : Fin 2 → FinDist (Fin 2) := ![FinDist.pure 0, FinDist.pure 1]
  have h_beliefs_0 : beliefs 0 = FinDist.pure 0 := by simp [beliefs, Matrix.cons_val_zero]
  have h_beliefs_1 : beliefs 1 = FinDist.pure 1 := by simp [beliefs, Matrix.cons_val_one]
  have h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i := by
    intro i
    simp only [Fin.sum_univ_two]
    fin_cases i <;> simp [weights, beliefs, FinDist.pure, Matrix.cons_val_zero,
      Matrix.cons_val_one, prior]
  have h_val : weights.expect (fun s => stepPayoff t (beliefs s)) = t / 2 := by
    have hv0 : stepPayoff t (beliefs 0) = 0 := by
      rw [h_beliefs_0]; simp only [stepPayoff]
      rw [FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))]
      exact if_neg (not_le.mpr ht_pos)
    have hv1 : stepPayoff t (beliefs 1) = 1 := by
      rw [h_beliefs_1]; simp only [stepPayoff]
      rw [FinDist.pure_apply_self]
      exact if_pos (le_of_lt ht_lt)
    unfold FinDist.expect
    simp only [Fin.sum_univ_two, hv0, hv1, mul_zero, mul_one, zero_add]
    exact h_prior_pmf1
  have h_vprior : stepPayoff t prior = 0 := by
    unfold stepPayoff
    rw [h_prior_pmf1, if_neg (not_le.mpr (by linarith : t / 2 < t))]
  have h_ineq := h_conc 2 weights beliefs prior h_bp
  linarith [h_val, h_vprior]

/-- The step function is bounded pointwise by `μ.pmf 1 / t`. -/
lemma stepPayoff_le_div (t : ℝ) (ht_pos : 0 < t) (μ : FinDist (Fin 2)) :
    stepPayoff t μ ≤ μ.pmf 1 / t := by
  unfold stepPayoff
  split_ifs with h
  · rw [le_div_iff₀ ht_pos]; linarith
  · exact div_nonneg (μ.nonneg 1) (le_of_lt ht_pos)

/-- **The Kamenica–Gentzkow upper bound for the step payoff.** No signal structure — with any
number of messages — achieves an expected sender payoff above the concave closure: Bayes' rule caps
the sender at `stepConcaveClosure t prior`. -/
theorem expectedSenderPayoff_le_stepConcaveClosure {m : ℕ} (t : ℝ) (ht_pos : 0 < t)
    (prior : FinDist (Fin 2)) (σ : SignalStructure 2 m) :
    expectedSenderPayoff prior σ (stepPayoff t) ≤ stepConcaveClosure t prior := by
  unfold stepConcaveClosure
  split_ifs with h_above
  · -- Above the threshold the closure is `1`; bound each term by its marginal and sum to `1`.
    calc expectedSenderPayoff prior σ (stepPayoff t)
        ≤ ∑ s, prior.signalMarginal σ.π s := by
          rw [expectedSenderPayoff_def]
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases hs : 0 < prior.signalMarginal σ.π s
          · rw [dif_pos hs]
            have h_step_le_one : stepPayoff t (prior.posteriorOrPrior σ.π s) ≤ 1 := by
              unfold stepPayoff; split_ifs <;> norm_num
            calc prior.signalMarginal σ.π s * stepPayoff t (prior.posteriorOrPrior σ.π s)
                ≤ prior.signalMarginal σ.π s * 1 :=
                  mul_le_mul_of_nonneg_left h_step_le_one hs.le
              _ = prior.signalMarginal σ.π s := mul_one _
          · rw [dif_neg hs]
            exact (signalLaw prior σ).nonneg s
      _ = 1 := (signalLaw prior σ).sum_one
  · -- Below the threshold, bound termwise by `marginal * posterior / t` and collapse the sum to
    -- the prior via Bayes-plausibility.
    have h_bp := SignalStructure.bayesPlausible prior σ 1
    calc expectedSenderPayoff prior σ (stepPayoff t)
        ≤ ∑ s, (if _ : 0 < prior.signalMarginal σ.π s
                then prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf 1
                else 0) / t := by
          rw [expectedSenderPayoff_def]
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases hs : 0 < prior.signalMarginal σ.π s
          · rw [dif_pos hs, dif_pos hs, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (stepPayoff_le_div t ht_pos _) hs.le
          · rw [dif_neg hs, dif_neg hs, zero_div]
      _ = prior.pmf 1 / t := by rw [← Finset.sum_div, ← h_bp]

/-- The achievable-payoff set for the step function is bounded above by 1. -/
private lemma stepPayoff_bddAbove (t : ℝ) (prior : FinDist (Fin 2)) :
    BddAbove { E | ∃ (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin 2)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i) ∧
      E = weights.expect (fun s => stepPayoff t (beliefs s)) } := by
  use 1; rintro E ⟨m, weights, beliefs, _, rfl⟩
  calc weights.expect (fun s => stepPayoff t (beliefs s))
      = ∑ s, weights.pmf s * stepPayoff t (beliefs s) := rfl
    _ ≤ ∑ s, weights.pmf s * 1 :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (by unfold stepPayoff; split_ifs <;> linarith) (weights.nonneg s)
    _ = 1 := by simp [weights.sum_one]

/-! ## The optimal binary signal

When the prior sits below the threshold, the Kamenica–Gentzkow optimum is a Bayes-plausible
*splitting* of the prior: With total probability `p/t` the receiver is moved to the boundary
posterior `(1 - t, t)` — just enough belief to act — and with the remaining probability to
certainty of the low state. The **splitting** is the economic primitive; `signalFromSplitting`
realizes it as a likelihood, and the lemmas below derive its anatomy: Marginals
(`signalMarginal_stepOptimalSignal`), posteriors (`posterior_stepOptimalSignal`), the likelihood
rows in closed form (`stepOptimalSignal_π_one_eq_pure`, `stepOptimalSignal_π_zero_pmf_one`), and
the payoff (`stepOptimalSignal_payoff`). -/

/-- The weights of the optimal splitting: The act-signal (signal `1`) is sent with total
probability `p/t`. -/
noncomputable def stepOptimalWeights (t : ℝ) (ht_pos : 0 < t) (prior : FinDist (Fin 2))
    (h_prior_below : prior.pmf 1 < t) : FinDist (Fin 2) :=
  FinDist.ofVec ![1 - prior.pmf 1 / t, prior.pmf 1 / t]
    (by
      have h_ratio_nonneg : 0 ≤ prior.pmf 1 / t := div_nonneg (prior.nonneg 1) ht_pos.le
      have h_ratio_lt_one : prior.pmf 1 / t < 1 := (div_lt_one ht_pos).mpr h_prior_below
      intro i; fin_cases i <;> fin_dist_norm)
    (by fin_dist_norm)

@[simp] lemma stepOptimalWeights_pmf_zero (t : ℝ) (ht_pos : 0 < t) (prior : FinDist (Fin 2))
    (h_prior_below : prior.pmf 1 < t) :
    (stepOptimalWeights t ht_pos prior h_prior_below).pmf 0 = 1 - prior.pmf 1 / t := by
  simp [stepOptimalWeights]

@[simp] lemma stepOptimalWeights_pmf_one (t : ℝ) (ht_pos : 0 < t) (prior : FinDist (Fin 2))
    (h_prior_below : prior.pmf 1 < t) :
    (stepOptimalWeights t ht_pos prior h_prior_below).pmf 1 = prior.pmf 1 / t := by
  simp [stepOptimalWeights]

/-- Both signals of the optimal splitting have positive weight. -/
lemma stepOptimalWeights_pos (t : ℝ) (ht_pos : 0 < t) (prior : FinDist (Fin 2))
    (h_full_supp : ∀ θ, 0 < prior.pmf θ) (h_prior_below : prior.pmf 1 < t) (s : Fin 2) :
    0 < (stepOptimalWeights t ht_pos prior h_prior_below).pmf s := by
  have h_ratio_pos : 0 < prior.pmf 1 / t := div_pos (h_full_supp 1) ht_pos
  have h_ratio_lt_one : prior.pmf 1 / t < 1 := (div_lt_one ht_pos).mpr h_prior_below
  fin_cases s <;> simp [stepOptimalWeights] <;> linarith

/-- The posterior beliefs of the optimal splitting: Signal `0` carries certainty of the low state;
signal `1` carries the boundary posterior putting exactly `t` on the high state. -/
noncomputable def stepOptimalBeliefs (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    Fin 2 → FinDist (Fin 2) :=
  ![FinDist.pure 0,
    FinDist.ofVec ![1 - t, t]
      (by intro i; fin_cases i <;> fin_dist_norm)
      (by fin_dist_norm)]

@[simp] lemma stepOptimalBeliefs_zero (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    stepOptimalBeliefs t ht_pos ht_lt 0 = FinDist.pure 0 := rfl

@[simp] lemma stepOptimalBeliefs_one_pmf_zero (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    (stepOptimalBeliefs t ht_pos ht_lt 1).pmf 0 = 1 - t := by
  simp [stepOptimalBeliefs]

@[simp] lemma stepOptimalBeliefs_one_pmf_one (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    (stepOptimalBeliefs t ht_pos ht_lt 1).pmf 1 = t := by
  simp [stepOptimalBeliefs]

/-- **The optimal splitting is Bayes-plausible**: The boundary posterior `t` weighted by `p/t`
returns exactly the prior mass `p` on the high state. -/
lemma stepOptimalSplitting_bayesPlausible (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_prior_below : prior.pmf 1 < t) :
    ∀ i, ∑ s, (stepOptimalWeights t ht_pos prior h_prior_below).pmf s *
      (stepOptimalBeliefs t ht_pos ht_lt s).pmf i = prior.pmf i := by
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  -- On `Fin 2` the low-state mass is the complement of the high-state mass.
  have hq_eq : prior.pmf 0 = 1 - prior.pmf 1 := by
    have h_sum := prior.sum_one
    simp only [Fin.sum_univ_two] at h_sum; linarith
  intro i
  rw [Fin.sum_univ_two]
  fin_cases i
  · -- Low state: `(1 - p/t)·1 + (p/t)(1 - t) = 1 - p`.
    simp only [Fin.zero_eta, stepOptimalWeights_pmf_zero, stepOptimalWeights_pmf_one,
      stepOptimalBeliefs_zero, stepOptimalBeliefs_one_pmf_zero, FinDist.pure_apply_self, hq_eq]
    field_simp
    ring
  · -- High state: `(1 - p/t)·0 + (p/t)·t = p`.
    simp only [Fin.mk_one, stepOptimalWeights_pmf_zero, stepOptimalWeights_pmf_one,
      stepOptimalBeliefs_zero, stepOptimalBeliefs_one_pmf_one,
      FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ 1), mul_zero, zero_add]
    exact div_mul_cancel₀ _ ht_ne

/-- **The Kamenica–Gentzkow optimal binary signal for the step payoff.** Defined as the optimal
Bayes-plausible splitting of the prior (`stepOptimalWeights`, `stepOptimalBeliefs`) — the KG
primitive — realized as a likelihood by `signalFromSplitting`. By `stepOptimalSignal_payoff` it
achieves the concave closure, which by `expectedSenderPayoff_le_stepConcaveClosure` is the best
possible. -/
noncomputable def stepOptimalSignal (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (_h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) : SignalStructure 2 2 :=
  -- `_h_full_supp` is retained for the closed-form likelihood rows below
  -- (`stepOptimalSignal_π_apply` and friends divide by `prior.pmf θ`); the splitting realization
  -- itself no longer needs it.
  signalFromSplitting prior
    (stepOptimalWeights t ht_pos prior h_prior_below)
    (stepOptimalBeliefs t ht_pos ht_lt)
    (stepOptimalSplitting_bayesPlausible t ht_pos ht_lt prior h_prior_below)

/-- The optimal signal's likelihood in closed form: The realized splitting on the positive-prior
states, `π(s | θ) = w(s) μ_s(θ) / p(θ)`. Full support selects the positive-prior branch of
`signalFromSplitting` at every `θ`. -/
lemma stepOptimalSignal_π_apply (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) (θ s : Fin 2) :
    ((stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π θ).pmf s
      = (stepOptimalWeights t ht_pos prior h_prior_below).pmf s
          * (stepOptimalBeliefs t ht_pos ht_lt s).pmf θ / prior.pmf θ := by
  simp only [stepOptimalSignal, signalFromSplitting, dif_neg (ne_of_gt (h_full_supp θ))]

/-- The marginal signal law of the optimal signal is the splitting weights; in particular the
receiver acts with total probability `p/t`. -/
lemma signalMarginal_stepOptimalSignal (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) (s : Fin 2) :
    prior.signalMarginal (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π s
      = (stepOptimalWeights t ht_pos prior h_prior_below).pmf s :=
  signalMarginal_signalFromSplitting prior _ _ _ s

/-- **The posteriors of the optimal signal are exactly the splitting beliefs**: Certainty of the
low state on signal `0`, the boundary posterior `(1 - t, t)` on signal `1`. -/
lemma posterior_stepOptimalSignal (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) (s : Fin 2)
    (h_denom_pos : 0 < ∑ θ,
      prior.pmf θ *
        ((stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π θ).pmf s :=
      denom_pos_signalFromSplitting prior _ _ _ s
        (stepOptimalWeights_pos t ht_pos prior h_full_supp h_prior_below s)) :
    prior.posterior (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π s
        h_denom_pos
      = stepOptimalBeliefs t ht_pos ht_lt s :=
  posterior_signalFromSplitting prior _ _ _ s
    (stepOptimalWeights_pos t ht_pos prior h_full_supp h_prior_below s) h_denom_pos

/-- The `posteriorOrPrior` form of `posterior_stepOptimalSignal`, for consumers that reach the
optimal signal through the `expectedSenderPayoff` unfold (which uses `posteriorOrPrior`). On the
positive-marginal regime the two posteriors coincide. -/
lemma posteriorOrPrior_stepOptimalSignal (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) (s : Fin 2) :
    prior.posteriorOrPrior (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π s
      = stepOptimalBeliefs t ht_pos ht_lt s :=
  -- `posterior _ _ h` is by definition `posteriorOrPrior _ _`, so the result transports.
  posterior_stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below s

/-- In the low state the optimal signal sends the act-signal with probability
`α = p(1-t) / (t(1-p))` — the partial-pooling rate that drags the act-posterior down to exactly the
threshold. -/
lemma stepOptimalSignal_π_zero_pmf_one (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    ((stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π 0).pmf 1
      = prior.pmf 1 * (1 - t) / (t * (1 - prior.pmf 1)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hq_eq : prior.pmf 0 = 1 - prior.pmf 1 := by
    have h_sum := prior.sum_one
    simp only [Fin.sum_univ_two] at h_sum; linarith
  have hq_pos : 0 < 1 - prior.pmf 1 := hq_eq ▸ h_full_supp 0
  rw [stepOptimalSignal_π_apply, stepOptimalWeights_pmf_one, stepOptimalBeliefs_one_pmf_zero,
    hq_eq]
  field_simp

/-- In the low state the optimal signal stays silent with the complementary probability `1 - α`. -/
lemma stepOptimalSignal_π_zero_pmf_zero (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    ((stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π 0).pmf 0
      = 1 - prior.pmf 1 * (1 - t) / (t * (1 - prior.pmf 1)) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hq_eq : prior.pmf 0 = 1 - prior.pmf 1 := by
    have h_sum := prior.sum_one
    simp only [Fin.sum_univ_two] at h_sum; linarith
  have hq_pos : 0 < 1 - prior.pmf 1 := hq_eq ▸ h_full_supp 0
  rw [stepOptimalSignal_π_apply, stepOptimalWeights_pmf_zero, stepOptimalBeliefs_zero,
    FinDist.pure_apply_self, hq_eq]
  field_simp
  ring

/-- **In the high state the optimal signal acts for sure**: The likelihood row at the high state is
the point mass on the act-signal. Together with `stepOptimalSignal_π_zero_pmf_one` this is the
explicit investigation policy of Kamenica–Gentzkow's prosecutor. -/
lemma stepOptimalSignal_π_one_eq_pure (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π 1
      = FinDist.pure 1 := by
  -- `pmf 1 = (p/t)·t/p = 1` forces the whole row to the point mass.
  refine FinDist.eq_pure_of_pmf_eq_one ?_
  rw [stepOptimalSignal_π_apply, stepOptimalWeights_pmf_one, stepOptimalBeliefs_one_pmf_one,
    div_mul_cancel₀ _ (ne_of_gt ht_pos)]
  exact div_self (ne_of_gt (h_full_supp 1))

/-- **The optimal signal achieves the concave closure**: Its expected sender payoff is
`stepConcaveClosure t prior = p/t` — by `expectedSenderPayoff_le_stepConcaveClosure`, the best
possible over all signal structures. -/
theorem stepOptimalSignal_payoff (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    expectedSenderPayoff prior (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below)
      (stepPayoff t) = stepConcaveClosure t prior := by
  have h_marg := signalMarginal_stepOptimalSignal t ht_pos ht_lt prior h_full_supp
    h_prior_below
  have h_w_pos := stepOptimalWeights_pos t ht_pos prior h_full_supp h_prior_below
  have h_post := posteriorOrPrior_stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below
  have h_marg0_pos : 0 < prior.signalMarginal
      (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π 0 := by
    rw [h_marg 0]; exact h_w_pos 0
  have h_marg1_pos : 0 < prior.signalMarginal
      (stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below).π 1 := by
    rw [h_marg 1]; exact h_w_pos 1
  -- The silent signal's posterior is certain of the low state: the receiver does not act.
  have h_v0 : stepPayoff t (stepOptimalBeliefs t ht_pos ht_lt 0) = 0 := by
    rw [stepOptimalBeliefs_zero, stepPayoff,
      FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ 1), if_neg (not_le.mpr ht_pos)]
  -- The act-signal's posterior sits exactly at the threshold: the receiver acts.
  have h_v1 : stepPayoff t (stepOptimalBeliefs t ht_pos ht_lt 1) = 1 := by
    rw [stepPayoff, stepOptimalBeliefs_one_pmf_one, if_pos (le_refl t)]
  rw [expectedSenderPayoff_def, Fin.sum_univ_two, dif_pos h_marg0_pos, dif_pos h_marg1_pos,
    h_post 0, h_post 1, h_v0, h_v1, h_marg 0, h_marg 1,
    stepOptimalWeights_pmf_zero, stepOptimalWeights_pmf_one,
    stepConcaveClosure, if_neg (not_le.mpr h_prior_below)]
  ring

/-- A binary signal achieves the concave closure of the step function — existence form, witnessed
by `stepOptimalSignal`. -/
theorem binarySignal_achieves_stepClosure
    (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    ∃ σ : SignalStructure 2 2,
      BayesPlausible prior σ ∧
      expectedSenderPayoff prior σ (stepPayoff t) =
        stepConcaveClosure t prior :=
  ⟨stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below,
    SignalStructure.bayesPlausible prior _,
    stepOptimalSignal_payoff t ht_pos ht_lt prior h_full_supp h_prior_below⟩

/-! ## Uniqueness of the optimal signal

The equality case of `expectedSenderPayoff_le_stepConcaveClosure`: An optimal signal can waste
nothing. Termwise in the bound `𝟙[q_s ≥ t] ≤ q_s / t`, every message sent with positive probability
must move the posterior of the high state either to exactly the threshold `t` (act-messages — any
higher belief overshoots) or to `0` (no-act messages — any residual high-state mass is squandered).
For binary signals this determines the whole signal: Up to the labeling of messages,
`stepOptimalSignal` is the unique optimum (Kamenica and Gentzkow 2011). -/

/-- **Posterior dichotomy at the optimum.** If a signal — with any number of messages — attains the
concave closure, then every message of positive marginal probability induces a posterior
probability of the high state equal to `0` or to exactly the threshold `t`. -/
theorem posterior_dichotomy_of_optimal {m : ℕ} (t : ℝ) (ht_pos : 0 < t)
    (prior : FinDist (Fin 2)) (h_prior_below : prior.pmf 1 < t)
    (σ : SignalStructure 2 m)
    (h_opt : expectedSenderPayoff prior σ (stepPayoff t) = stepConcaveClosure t prior)
    (s : Fin m) (h_pos : 0 < prior.signalMarginal σ.π s) :
    (prior.posteriorOrPrior σ.π s).pmf 1 = 0 ∨ (prior.posteriorOrPrior σ.π s).pmf 1 = t := by
  -- Termwise the payoff summand is dominated by the Bayes summand over `t` (as in the proof of
  -- `expectedSenderPayoff_le_stepConcaveClosure`).
  have h_le : ∀ s' ∈ Finset.univ,
      (if _ : 0 < prior.signalMarginal σ.π s'
       then prior.signalMarginal σ.π s' * stepPayoff t (prior.posteriorOrPrior σ.π s') else 0)
      ≤ (if _ : 0 < prior.signalMarginal σ.π s'
         then prior.signalMarginal σ.π s' * (prior.posteriorOrPrior σ.π s').pmf 1 else 0) / t := by
    intro s' _
    by_cases hs' : 0 < prior.signalMarginal σ.π s'
    · rw [dif_pos hs', dif_pos hs', mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (stepPayoff_le_div t ht_pos _) hs'.le
    · rw [dif_neg hs', dif_neg hs', zero_div]
  -- Both totals equal `p/t`: the payoff by optimality, the Bayes sum by plausibility — so the
  -- termwise bound is an equality at every message.
  have h_bp := SignalStructure.bayesPlausible prior σ 1
  have h_sum_eq : ∑ s', (if _ : 0 < prior.signalMarginal σ.π s'
      then prior.signalMarginal σ.π s' * stepPayoff t (prior.posteriorOrPrior σ.π s') else 0)
      = ∑ s', (if _ : 0 < prior.signalMarginal σ.π s'
          then prior.signalMarginal σ.π s' * (prior.posteriorOrPrior σ.π s').pmf 1 else 0) / t := by
    rw [← Finset.sum_div, ← h_bp]
    calc ∑ s', (if _ : 0 < prior.signalMarginal σ.π s'
            then prior.signalMarginal σ.π s' * stepPayoff t (prior.posteriorOrPrior σ.π s') else 0)
        = expectedSenderPayoff prior σ (stepPayoff t) := (expectedSenderPayoff_def _ _ _).symm
      _ = stepConcaveClosure t prior := h_opt
      _ = prior.pmf 1 / t := by rw [stepConcaveClosure, if_neg (not_le.mpr h_prior_below)]
  have h_term := (Finset.sum_eq_sum_iff_of_le h_le).mp h_sum_eq s (Finset.mem_univ s)
  rw [dif_pos h_pos, dif_pos h_pos, stepPayoff] at h_term
  by_cases hq : (prior.posteriorOrPrior σ.π s).pmf 1 ≥ t
  · -- An act-message: `m_s · 1 = m_s · q_s / t` forces `q_s = t`.
    right
    rw [if_pos hq, mul_one, eq_div_iff (ne_of_gt ht_pos)] at h_term
    exact (mul_left_cancel₀ (ne_of_gt h_pos) h_term).symm
  · -- A no-act message: `0 = m_s · q_s / t` forces `q_s = 0`.
    left
    rw [if_neg hq, mul_zero] at h_term
    rcases div_eq_zero_iff.mp h_term.symm with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 (ne_of_gt h_pos)
      · exact h1
    · exact absurd h0 (ne_of_gt ht_pos)

/-- **The optimal binary signal is unique.** Any binary signal attaining the concave closure equals
`stepOptimalSignal` — once the labeling freedom is fixed by requiring message `1` to be the
act-message (`h_label`). The labeling hypothesis does double duty: A zero-marginal message `1`
would have its posterior default to the prior, which sits below `t`, so `h_label` also rules out
the degenerate single-message signal. -/
theorem eq_stepOptimalSignal_of_optimal (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t)
    (σ : SignalStructure 2 2)
    (h_opt : expectedSenderPayoff prior σ (stepPayoff t) = stepConcaveClosure t prior)
    (h_label : t ≤ (prior.posteriorOrPrior σ.π 1).pmf 1) :
    σ = stepOptimalSignal t ht_pos ht_lt prior h_full_supp h_prior_below := by
  have hp_pos : 0 < prior.pmf 1 := h_full_supp 1
  have h_marg_sum : prior.signalMarginal σ.π 0 + prior.signalMarginal σ.π 1 = 1 := by
    have h_law := (signalLaw prior σ).sum_one
    rwa [Fin.sum_univ_two] at h_law
  -- Message `1` has positive marginal: at zero marginal its posterior would default to the
  -- prior, which sits strictly below the threshold — contradicting `h_label`.
  have h_m1_pos : 0 < prior.signalMarginal σ.π 1 := by
    by_contra h
    have h_junk : prior.posteriorOrPrior σ.π 1 = prior :=
      FinDist.posteriorOrPrior_eq_prior_of_denom_nonpos prior σ.π 1
        (by rwa [← FinDist.signalMarginal_eq_sum])
    rw [h_junk] at h_label
    exact absurd h_label (not_le.mpr h_prior_below)
  -- The dichotomy plus `h_label` fix the act-posterior at exactly `t`.
  have h_q1 : (prior.posteriorOrPrior σ.π 1).pmf 1 = t := by
    rcases posterior_dichotomy_of_optimal t ht_pos prior h_prior_below σ h_opt 1 h_m1_pos
      with h0 | h1
    · rw [h0] at h_label; linarith
    · exact h1
  -- Bayes plausibility at the high state, with the act-posterior substituted.
  have h_bayes := SignalStructure.bayesPlausible prior σ 1
  rw [Fin.sum_univ_two, dif_pos h_m1_pos, h_q1] at h_bayes
  -- Message `0` has positive marginal: otherwise message `1` carries all the mass and Bayes
  -- forces `p = t`, contradicting `p < t`.
  have h_m0_pos : 0 < prior.signalMarginal σ.π 0 := by
    by_contra h
    rw [dif_neg h, zero_add] at h_bayes
    have h_m1_one : prior.signalMarginal σ.π 1 = 1 := by
      have h_m0_zero : prior.signalMarginal σ.π 0 = 0 :=
        le_antisymm (not_lt.mp h) ((signalLaw prior σ).nonneg 0)
      linarith
    rw [h_m1_one, one_mul] at h_bayes
    linarith
  rw [dif_pos h_m0_pos] at h_bayes
  -- The no-act posterior is certain of the low state: `q₀ = t` would force `p = t`.
  have h_q0 : (prior.posteriorOrPrior σ.π 0).pmf 1 = 0 := by
    rcases posterior_dichotomy_of_optimal t ht_pos prior h_prior_below σ h_opt 0 h_m0_pos
      with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at h_bayes
      have h_collapse : prior.signalMarginal σ.π 0 * t + prior.signalMarginal σ.π 1 * t
          = t := by
        have h_factor : prior.signalMarginal σ.π 0 * t + prior.signalMarginal σ.π 1 * t
            = (prior.signalMarginal σ.π 0 + prior.signalMarginal σ.π 1) * t := by ring
        rw [h_factor, h_marg_sum, one_mul]
      linarith
  -- Bayes now reads `p = m₁ · t`: the act-message carries exactly the weight `p/t`.
  rw [h_q0, mul_zero, zero_add] at h_bayes
  have h_m1 : prior.signalMarginal σ.π 1 = prior.pmf 1 / t := by
    rw [eq_comm, div_eq_iff (ne_of_gt ht_pos), eq_comm]
    exact h_bayes.symm
  have h_m0 : prior.signalMarginal σ.π 0 = 1 - prior.pmf 1 / t := by linarith
  -- The two posteriors coincide with the optimal splitting beliefs as full distributions.
  have h_post0 : prior.posteriorOrPrior σ.π 0 = FinDist.pure 0 := by
    refine FinDist.eq_pure_of_pmf_eq_one ?_
    have h_sum := (prior.posteriorOrPrior σ.π 0).sum_one
    rw [Fin.sum_univ_two] at h_sum
    linarith
  have h_post1 : prior.posteriorOrPrior σ.π 1 = stepOptimalBeliefs t ht_pos ht_lt 1 := by
    ext θ
    have h_sum := (prior.posteriorOrPrior σ.π 1).sum_one
    rw [Fin.sum_univ_two] at h_sum
    fin_cases θ
    · simp only [Fin.zero_eta, stepOptimalBeliefs_one_pmf_zero]
      linarith
    · simp only [Fin.mk_one, stepOptimalBeliefs_one_pmf_one]
      exact h_q1
  -- Package the marginals and posteriors uniformly over the two messages.
  have h_m_all : ∀ s, prior.signalMarginal σ.π s
      = (stepOptimalWeights t ht_pos prior h_prior_below).pmf s := by
    intro s
    fin_cases s
    · simp only [Fin.zero_eta, stepOptimalWeights_pmf_zero]; exact h_m0
    · simp only [Fin.mk_one, stepOptimalWeights_pmf_one]; exact h_m1
  have h_post_all : ∀ s, prior.posteriorOrPrior σ.π s = stepOptimalBeliefs t ht_pos ht_lt s := by
    intro s
    fin_cases s
    · simp only [Fin.zero_eta, stepOptimalBeliefs_zero]; exact h_post0
    · simp only [Fin.mk_one]; exact h_post1
  have h_marg_pos_all : ∀ s, 0 < prior.signalMarginal σ.π s := by
    intro s
    fin_cases s
    · exact h_m0_pos
    · exact h_m1_pos
  -- Bayes inversion: a positive-marginal posterior determines the likelihood at every state of
  -- full support, `π(s | θ) = m_s · q_s(θ) / p(θ)`.
  have h_inv : ∀ (s θ : Fin 2), (σ.π θ).pmf s
      = prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf θ / prior.pmf θ := by
    intro s θ
    rw [FinDist.posteriorOrPrior_apply prior σ.π s θ
      (by rw [← FinDist.signalMarginal_eq_sum]; exact h_marg_pos_all s),
      ← FinDist.signalMarginal_eq_sum]
    field_simp [ne_of_gt (h_full_supp θ), ne_of_gt (h_marg_pos_all s)]
  -- The likelihoods agree pointwise with the realized optimal splitting.
  apply SignalStructure.ext
  intro θ
  ext s
  rw [stepOptimalSignal_π_apply, h_inv s θ, h_m_all s, h_post_all s]

/-- `stepConcaveClosure t` equals the concave closure of `stepPayoff t`. -/
theorem stepConcaveClosure_eq (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1)
    (prior : FinDist (Fin 2)) (h_full_supp : ∀ θ, 0 < prior.pmf θ)
    (h_prior_below : prior.pmf 1 < t) :
    concaveClosure (stepPayoff t) prior =
      stepConcaveClosure t prior := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨stepPayoff t prior, 1, FinDist.pure 0, fun _ => prior,
        by intro i; simp [FinDist.pure],
        by simp [FinDist.expect, FinDist.pure]⟩
    · rintro E ⟨m, weights, beliefs, h_bp, rfl⟩
      simp only [stepConcaveClosure, if_neg (not_le.mpr h_prior_below)]
      calc weights.expect (fun s => stepPayoff t (beliefs s))
          = ∑ s, weights.pmf s * stepPayoff t (beliefs s) := rfl
        _ ≤ ∑ s, weights.pmf s * ((beliefs s).pmf 1 / t) :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
              (stepPayoff_le_div t ht_pos (beliefs s)) (weights.nonneg s)
        _ = (∑ s, weights.pmf s * (beliefs s).pmf 1) / t := by
            rw [Finset.sum_div]; simp_rw [mul_div_assoc]
        _ = prior.pmf 1 / t := by rw [h_bp 1]
  · rw [← stepOptimalSignal_payoff t ht_pos ht_lt prior h_full_supp h_prior_below]
    exact le_csSup (stepPayoff_bddAbove t prior)
      (expectedSenderPayoff_mem_achievableSet prior _ (stepPayoff t))

end Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
