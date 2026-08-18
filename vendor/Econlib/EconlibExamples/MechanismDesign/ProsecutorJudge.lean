/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Prosecutor-Judge (Kamenica-Gentzkow 2011): Optimal Persuasion Doubles the Conviction Rate

The prosecutor-judge game is the motivating example for **Bayesian persuasion** of Kamenica and
Gentzkow (2011). A sender (the *prosecutor*) commits to an information policy before the state is
realized; a receiver (the *judge*) observes the policy and its realized report, updates by Bayes'
rule, and best-responds. Although the judge knows that only 30% of defendants are guilty and that
the prosecutor's information policy is chosen to maximize convictions, the optimal policy induces
her to convict 60% of defendants, doubling the conviction rate of full disclosure.

This file instantiates the general finite-persuasion step-function API on the paper's numbers and
proves the full Kamenica-Gentzkow story: The closed-form value `3/5`, its attainment by an explicit
investigation, the matching upper bound over signals with arbitrarily many messages, uniqueness of
the optimal binary investigation, and the impossibility of fabricating evidence.

## The story

A defendant is either **innocent** or **guilty**; the prosecutor and the judge share the prior
`Pr(guilty) = 3/10`. The judge must **convict** or **acquit**:

* The judge gets utility `1` for the just action (that is, convicting the guilty, acquitting the
  innocent) and `0` otherwise, so she strictly prefers to convict once her posterior probability of
  guilt *exceeds* `1/2` and to acquit once it falls below. At the threshold `1/2` exactly she is
  **indifferent**; following Kamenica–Gentzkow we resolve that knife-edge in the Sender's favor
  (the Sender-preferred selection), so the judge convicts at posterior `1/2`. This tie-break is a
  modeling convention, not a derived fact — and it is load-bearing, since the optimal policy lands
  the convict posterior *exactly* at `1/2`.
* The prosecutor gets utility `1` whenever the judge convicts, guilty or not, and `0` otherwise.

The prosecutor cannot misreport findings, but he *can* choose what to look for: He commits in
advance to an investigation policy, represented by a distribution `π(signal | state)` over reports,
and the realized report is disclosed honestly. With no investigation the judge acquits everyone
(`3/10 < 1/2`) and the prosecutor earns `0`; a fully informative investigation convicts exactly the
guilty, earning `3/10`.

## The optimal investigation

From the perspective of the prosecutor, the optimal policy is partial pooling: Report "convict" for
sure when the defendant is guilty, and with probability `3/7` when innocent. On the convict report
the judge's posterior of guilt is dragged down to exactly the threshold `1/2` — just enough to
convict, with no conviction probability wasted on overshooting (KG observe that if the judge
strictly prefers to convict after the report, the prosecutor could increase his payoff by slightly
decreasing `π(i|innocent)`). The convict report arrives with total probability
`3/10 · 1 + 7/10 · 3/7 = 3/5`, i.e. the judge convicts 60% of defendants. Moreover this policy is
unique among binary investigations attaining the optimum value, *given the labeling convention that
signal `1` is the incriminating report* (`optimalInvestigation_unique`); the same policy with the
two signals relabeled also attains the optimum, so uniqueness is up to that relabeling.

## What concavification says

Kamenica and Gentzkow's central result is that the value of optimal persuasion is the **concave
closure** of the sender's payoff (as a function of the receiver's posterior) evaluated at the
prior. Here the prosecutor's payoff is the step function jumping from `0` to `1` at posterior
`1/2`. The step function is not concave, so disclosure creates a concave closure that interpolates
linearly from `(0, 0)` to `(1/2, 1)`. At the prior `3/10` it evaluates to `(3/10) / (1/2) = 3/5`.

The binding constraint is **Bayes plausibility**: Induced posteriors must average back to the
prior. This martingale constraint is what caps the value at the concave closure and rules out
fabrication: While a fabricated posterior certain of guilt would convict for sure (payoff `1`), no
Bayes-consistent signal can deliver it.

## What this file proves

We define the prior and the conviction threshold, then instantiate the general
`InformationDesign.Persuasion.Finite` step-function results on these numbers:

* `prosecutorJudge_optimal_value` and `prosecutorJudge_concaveClosure` — the concavification — the
  supremum over all Bayes-plausible splittings of the prior — equals `3/5`.
* `prosecutorJudge_payoff_le` — *optimality, upper half*: No signal, with any finite number of
  messages, achieves expected payoff above `3/5`.
* `prosecutorJudge_persuasion_gain` — *optimality, lower half*: The explicit investigation
  `optimalInvestigation` attains `3/5`.
* `optimalInvestigation_unique` — *uniqueness*: Any binary investigation attaining `3/5` is
  `optimalInvestigation`.
* `prosecutorJudge_no_fabrication` — *no fabrication*: Every investigation has an on-path report
  whose posterior falls short of certainty of guilt — always-convincing evidence is not
  Bayes-plausible.
* `fullDisclosure_payoff` and `prosecutorJudge_doubles` — *the headline benchmark*: Full disclosure
  convicts only the guilty (`3/10`), so optimal persuasion (`3/5`) exactly doubles it.

## Main definitions and theorems

* `prior : FinDist (Fin 2)` — the shared prior, `Pr(guilty) = 3/10` (state `1` is "guilty").
* `threshold : ℝ` — the judge's conviction threshold `1/2`.
* `prosecutorJudge_optimal_value` — the closed-form concave closure evaluates to `3/5`.
* `prosecutorJudge_concaveClosure` — `3/5` is the concavification (the Kamenica-Gentzkow value).
* `prosecutorJudge_payoff_le` — no signal with any number of messages exceeds `3/5`.
* `prosecutorJudge_payoff_not_concave` — the raw step payoff is not concave, which is *why*
  disclosure strictly helps.
* `optimalInvestigation : SignalStructure 2 2` — the explicit optimal investigation, with
  likelihoods `optimalInvestigation_guilty` (point mass on "convict"),
  `optimalInvestigation_innocent_convict` (`3/7`), and `optimalInvestigation_innocent_acquit`
  (`4/7`).
* `optimalInvestigation_convicts_prob` — the judge convicts with probability `3/5`.
* `optimalInvestigation_posterior_convict` / `optimalInvestigation_posterior_acquit` — the
  posterior of guilt is exactly `1/2` on the convict signal and `0` on the acquit signal.
* `prosecutorJudge_persuasion_gain` — the optimal investigation attains `3/5`.
* `optimalInvestigation_unique` — any binary investigation attaining `3/5` (with the convict signal
  labeled `1`) must be `optimalInvestigation`.
* `prosecutorJudge_no_fabrication` — the prosecutor cannot fabricate evidence: A fabricated
  posterior certain of guilt would convict for sure, but every investigation has an on-path report
  whose posterior is not certain of guilt — Bayes' rule forbids always-convincing evidence.
* `prosecutorJudge_no_information` / `prosecutorJudge_strict_gain` — with no information the
  prosecutor earns `0`, and the optimal investigation strictly beats it.
* `fullDisclosure : SignalStructure 2 2` — the fully-revealing investigation;
  `fullDisclosure_payoff` (`= 3/10`, convicts only the guilty) and `prosecutorJudge_doubles`
  (optimal persuasion doubles it).

## References

Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” American Economic Review 101
(6): 2590–615. https://doi.org/10.1257/aer.101.6.2590.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.ProsecutorJudge

open Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
open Econlib.Probability

/-- The shared prior: `P(innocent) = 7/10`, `P(guilty) = 3/10` (state `1` is "guilty"). -/
def prior : FinDist (Fin 2) := finDist% ![7/10, 3/10]

/-- The prosecutor's threshold: The judge convicts iff her posterior probability of guilt is at
least `1/2`. At exactly `1/2` the judge is indifferent; the weak inequality encodes the
Sender-preferred (convict-at-indifference) tie-break — see the module docstring. -/
def threshold : ℝ := 1 / 2

@[simp] lemma prior_pmf_one : prior.pmf 1 = 3 / 10 := by simp [prior]

@[simp] lemma prior_pmf_zero : prior.pmf 0 = 7 / 10 := by simp [prior]

lemma prior_full_supp : ∀ θ, 0 < prior.pmf θ := by
  intro θ; fin_cases θ <;> simp

lemma prior_below_threshold : prior.pmf 1 < threshold := by
  simp only [prior_pmf_one, threshold]; norm_num

/-- **The closed-form concave closure evaluates to `3/5`.** Since the prior probability of guilt
`3/10` falls short of the conviction threshold `1/2`, the concave closure interpolates linearly
from `(0, 0)` to `(1/2, 1)`, giving `(3/10) / (1/2) = 3/5`. -/
theorem prosecutorJudge_optimal_value :
    stepConcaveClosure threshold prior = 3 / 5 := by
  rw [stepConcaveClosure]
  rw [if_neg (by simp only [prior_pmf_one, threshold]; norm_num)]
  simp only [prior_pmf_one, threshold]; norm_num

/-- **`3/5` is the concavification — the Kamenica–Gentzkow optimal value.** The supremum of
expected sender payoffs over all Bayes-plausible splittings of the prior equals `3/5`. Together
with `prosecutorJudge_persuasion_gain` (attainment) and `prosecutorJudge_payoff_le` (no signal does
better), this certifies that `3/5` is the optimum, not merely an achievable value. -/
theorem prosecutorJudge_concaveClosure :
    concaveClosure (stepPayoff threshold) prior = 3 / 5 := by
  rw [stepConcaveClosure_eq threshold (by norm_num [threshold]) (by norm_num [threshold])
    prior prior_full_supp prior_below_threshold]
  exact prosecutorJudge_optimal_value

/-- **Optimality, upper half.** No signal structure with any finite number of messages achieves
expected sender payoff above `3/5`. -/
theorem prosecutorJudge_payoff_le {m : ℕ} (σ : SignalStructure 2 m) :
    expectedSenderPayoff prior σ (stepPayoff threshold) ≤ 3 / 5 :=
  prosecutorJudge_optimal_value ▸
    expectedSenderPayoff_le_stepConcaveClosure threshold (by norm_num [threshold]) prior σ

/-- **The raw step payoff is not concave** on the belief simplex — the structural reason disclosure
can help. (The *strict* gain over no information is the separate `prosecutorJudge_strict_gain`;
non-concavity alone is necessity, not the realized improvement.) -/
theorem prosecutorJudge_payoff_not_concave : ¬ ConcaveOnSimplex (stepPayoff threshold) :=
  stepPayoff_not_concave threshold (by norm_num [threshold]) (by norm_num [threshold])

/-! ## The optimal investigation

Kamenica–Gentzkow's optimal investigation is the partial-pooling policy that always reports
"convict" when the defendant is guilty and reports "convict" with probability `3/7` when innocent.
On the convict signal the judge's posterior of guilt lands exactly at the threshold `1/2`. No
conviction probability is wasted, and the judge convicts with total probability `3/5`. -/

/-- **The optimal investigation** (signal `0` is "acquit", signal `1` is "convict"): The
instantiation of `stepOptimalSignal` on the textbook numbers. Its likelihoods are
`π(g | guilty) = 1` and `π(g | innocent) = 3/7` — see the lemmas below. -/
def optimalInvestigation : SignalStructure 2 2 :=
  stepOptimalSignal threshold (by norm_num [threshold]) (by norm_num [threshold])
    prior prior_full_supp prior_below_threshold

/-- `π(g | innocent) = 3/7`: When the defendant is innocent, the investigation nevertheless reports
"convict" with probability `3/7` — the partial-pooling rate that drags the convict posterior down
to exactly the threshold. -/
@[simp] lemma optimalInvestigation_innocent_convict :
    (optimalInvestigation.π 0).pmf 1 = 3 / 7 := by
  unfold optimalInvestigation
  rw [stepOptimalSignal_π_zero_pmf_one]
  norm_num [threshold]

/-- `π(i | innocent) = 4/7`: When the defendant is innocent, the investigation reports "acquit"
with probability `4/7`. -/
@[simp] lemma optimalInvestigation_innocent_acquit :
    (optimalInvestigation.π 0).pmf 0 = 4 / 7 := by
  unfold optimalInvestigation
  rw [stepOptimalSignal_π_zero_pmf_zero]
  norm_num [threshold]

/-- `π(g | guilty) = 1`: A guilty defendant is reported "convict" for sure — the likelihood row at
guilt is the point mass on the convict signal. -/
@[simp] lemma optimalInvestigation_guilty :
    optimalInvestigation.π 1 = FinDist.pure 1 := by
  unfold optimalInvestigation
  exact stepOptimalSignal_π_one_eq_pure _ _ _ _ _ _

/-- **The judge convicts with probability `3/5`**: The marginal probability of the convict signal
under the optimal investigation. -/
theorem optimalInvestigation_convicts_prob :
    prior.signalMarginal optimalInvestigation.π 1 = 3 / 5 := by
  unfold optimalInvestigation
  rw [signalMarginal_stepOptimalSignal, stepOptimalWeights_pmf_one]
  norm_num [threshold]

/-- The judge acquits with the complementary probability `2/5`. -/
theorem optimalInvestigation_acquits_prob :
    prior.signalMarginal optimalInvestigation.π 0 = 2 / 5 := by
  unfold optimalInvestigation
  rw [signalMarginal_stepOptimalSignal, stepOptimalWeights_pmf_zero]
  norm_num [threshold]

/-- On the convict signal the judge's posterior probability of guilt is exactly the threshold
`1/2`: The investigation concedes no slack. -/
theorem optimalInvestigation_posterior_convict :
    (prior.posteriorOrPrior optimalInvestigation.π 1).pmf 1 = 1 / 2 := by
  unfold optimalInvestigation
  rw [posteriorOrPrior_stepOptimalSignal threshold (by norm_num [threshold])
      (by norm_num [threshold]) prior prior_full_supp prior_below_threshold 1,
    stepOptimalBeliefs_one_pmf_one]
  norm_num [threshold]

/-- On the acquit signal the judge is certain of innocence. -/
theorem optimalInvestigation_posterior_acquit :
    prior.posteriorOrPrior optimalInvestigation.π 0 = FinDist.pure 0 := by
  unfold optimalInvestigation
  rw [posteriorOrPrior_stepOptimalSignal threshold (by norm_num [threshold])
      (by norm_num [threshold]) prior prior_full_supp prior_below_threshold 0,
    stepOptimalBeliefs_zero]

/-- **Optimality, lower half: The optimal investigation attains `3/5`** — by
`prosecutorJudge_payoff_le`, the best possible. (Bayes plausibility holds for *every* signal
structure by construction — `SignalStructure.bayesPlausible` — so it is not a side condition
here.) -/
theorem prosecutorJudge_persuasion_gain :
    expectedSenderPayoff prior optimalInvestigation (stepPayoff threshold) = 3 / 5 := by
  unfold optimalInvestigation
  rw [stepOptimalSignal_payoff]
  exact prosecutorJudge_optimal_value

/-- **The optimal investigation is unique** (Kamenica–Gentzkow): Any binary investigation that
attains the optimal conviction payoff `3/5` — with the labeling convention that signal `1` is the
incriminating one (its posterior of guilt reaches the conviction threshold) — is
`optimalInvestigation`: It must report "convict" for sure on the guilty and with probability
exactly `3/7` on the innocent. -/
theorem optimalInvestigation_unique (σ : SignalStructure 2 2)
    (h_opt : expectedSenderPayoff prior σ (stepPayoff threshold) = 3 / 5)
    (h_label : threshold ≤ (prior.posteriorOrPrior σ.π 1).pmf 1) :
    σ = optimalInvestigation := by
  unfold optimalInvestigation
  exact eq_stepOptimalSignal_of_optimal threshold (by norm_num [threshold])
    (by norm_num [threshold]) prior prior_full_supp prior_below_threshold σ
    (h_opt.trans prosecutorJudge_optimal_value.symm) h_label

/-! ## No fabrication

Fabricated evidence — an investigation whose every report convinces the judge the defendant is
guilty for sure — would convict with probability one. The martingale constraint of Bayes' rule
makes such an investigation unrealizable: Posteriors must average back to the prior, which puts
mass `7/10` on innocence, so some on-path report must fail to certify guilt. (Within the formalism
every `SignalStructure` is automatically Bayes-plausible — `SignalStructure.bayesPlausible` is the
law of total probability — so "the fabricated signal is not Bayes-plausible" is rendered as: No
signal structure realizes it.) -/

/-- **The prosecutor cannot fabricate evidence.** Every investigation — with any number of reports
— has an on-path report whose posterior is *not* certain of guilt: Bayes plausibility requires the
posteriors to average back to the prior, which puts mass `7/10` on innocence. -/
theorem prosecutorJudge_no_fabrication {m : ℕ} (σ : SignalStructure 2 m) :
    ∃ s, 0 < prior.signalMarginal σ.π s ∧ prior.posteriorOrPrior σ.π s ≠ FinDist.pure 1 := by
  by_contra h_all
  -- Suppose every on-path posterior certified guilt.
  have h_post : ∀ s, 0 < prior.signalMarginal σ.π s →
      prior.posteriorOrPrior σ.π s = FinDist.pure 1 :=
    fun s hs => of_not_not fun hne => h_all ⟨s, hs, hne⟩
  -- Then total probability puts zero posterior mass on innocence ...
  have h_bp := SignalStructure.bayesPlausible prior σ 0
  have h_terms : ∀ s ∈ Finset.univ, (if _ : 0 < prior.signalMarginal σ.π s
      then prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf 0
      else 0) = 0 := by
    intro s _
    by_cases hs : 0 < prior.signalMarginal σ.π s
    · rw [dif_pos hs, h_post s hs, FinDist.pure_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero]
    · rw [dif_neg hs]
  -- ... contradicting the prior's `7/10`.
  rw [Finset.sum_eq_zero h_terms, prior_pmf_zero] at h_bp
  norm_num at h_bp

/-! ## The strict value of information -/

/-- **With no information the prosecutor earns `0`**: At the prior the judge acquits
(`3/10 < 1/2`). -/
theorem prosecutorJudge_no_information : stepPayoff threshold prior = 0 :=
  stepPayoff_eq_zero_of_lt prior_below_threshold

/-- **Persuasion strictly helps the prosecutor.** The optimal investigation's payoff of `3/5`
strictly exceeds the no-information payoff of `0`. -/
theorem prosecutorJudge_strict_gain :
    stepPayoff threshold prior
      < expectedSenderPayoff prior optimalInvestigation (stepPayoff threshold) := by
  rw [prosecutorJudge_persuasion_gain, prosecutorJudge_no_information]
  norm_num

/-! ## The full-disclosure benchmark: persuasion doubles the conviction rate

Full disclosure — the investigation that simply reports the realized state (`fullDisclosure`) —
convicts exactly the guilty: on the guilty report the judge is certain of guilt and convicts, on the
innocent report she is certain of innocence and acquits. So the prosecutor earns the prior guilt
probability `Pr(guilty) = 3/10`. The optimal investigation earns `3/5`, exactly double. This makes
the headline "doubles the conviction rate" a theorem (`prosecutorJudge_doubles`), not an aside. -/

/-- **Full disclosure**: the investigation that reports the true state (in state `θ` the report is
`θ` with certainty). Under it the judge learns guilt exactly, so she convicts only the guilty. -/
def fullDisclosure : SignalStructure 2 2 where
  π := fun θ => FinDist.pure θ

/-- Under full disclosure the marginal probability of report `s` is just the prior `Pr(state = s)`:
the report equals the state. -/
@[simp] lemma fullDisclosure_marginal (s : Fin 2) :
    prior.signalMarginal fullDisclosure.π s = prior.pmf s := by
  simp only [FinDist.signalMarginal_eq_sum, fullDisclosure, Fin.sum_univ_two, FinDist.pure_pmf]
  fin_cases s <;> simp

/-- Under full disclosure the judge's posterior of guilt is `1` on the guilty report and `0` on the
innocent report — perfect information about the state. -/
lemma fullDisclosure_posterior_pmf_one (s : Fin 2) :
    (prior.posteriorOrPrior fullDisclosure.π s).pmf 1 = if s = 1 then 1 else 0 := by
  have hmarg : (∑ θ', prior.pmf θ' * (fullDisclosure.π θ').pmf s) = prior.pmf s := by
    have h := fullDisclosure_marginal s; rwa [FinDist.signalMarginal_eq_sum] at h
  have hpos : 0 < ∑ θ', prior.pmf θ' * (fullDisclosure.π θ').pmf s := by
    rw [hmarg]; fin_cases s <;> simp
  rw [FinDist.posteriorOrPrior_apply prior fullDisclosure.π s 1 hpos, hmarg]
  simp only [fullDisclosure, FinDist.pure_pmf]
  fin_cases s <;> simp [prior_pmf_one]

/-- **Full disclosure convicts exactly the guilty**: the prosecutor's expected payoff under perfect
information is the prior guilt probability `3/10`. -/
theorem fullDisclosure_payoff :
    expectedSenderPayoff prior fullDisclosure (stepPayoff threshold) = 3 / 10 := by
  rw [expectedSenderPayoff_def, Fin.sum_univ_two]
  have hm0 : prior.signalMarginal fullDisclosure.π 0 = 7 / 10 := by
    rw [fullDisclosure_marginal, prior_pmf_zero]
  have hm1 : prior.signalMarginal fullDisclosure.π 1 = 3 / 10 := by
    rw [fullDisclosure_marginal, prior_pmf_one]
  -- The guilty report (`s = 1`) convicts; the innocent report (`s = 0`) does not.
  have hp0 : stepPayoff threshold (prior.posteriorOrPrior fullDisclosure.π 0) = 0 :=
    stepPayoff_eq_zero_of_lt (by rw [fullDisclosure_posterior_pmf_one 0, threshold]; norm_num)
  have hp1 : stepPayoff threshold (prior.posteriorOrPrior fullDisclosure.π 1) = 1 :=
    stepPayoff_eq_one_of_le (by rw [fullDisclosure_posterior_pmf_one 1, threshold]; norm_num)
  rw [dif_pos (by rw [hm0]; norm_num), dif_pos (by rw [hm1]; norm_num), hp0, hp1, hm0, hm1]
  norm_num

/-- **Optimal persuasion doubles the conviction rate of full disclosure.** The optimal investigation
convicts `3/5` of defendants; full disclosure convicts only the guilty `3/10`. The headline
Kamenica–Gentzkow comparison, as a theorem. -/
theorem prosecutorJudge_doubles :
    expectedSenderPayoff prior optimalInvestigation (stepPayoff threshold)
      = 2 * expectedSenderPayoff prior fullDisclosure (stepPayoff threshold) := by
  rw [prosecutorJudge_persuasion_gain, fullDisclosure_payoff]; norm_num

end EconlibExamples.MechanismDesign.ProsecutorJudge
