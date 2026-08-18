/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.PBE

/-!
# Separating assessments: Bayes consistency forces beliefs to point masses

In a **separating** assessment a message identifies its sender: When only type `θ₀` sends `m` with
positive probability, the Bayesian posterior at `m` is the point mass at `θ₀`, and under separation
plus a full-support prior this applies at every on-path message. Composed with Bayes consistency,
the equilibrium belief at type `θ₀`'s message is forced to `pure θ₀` — the receiver learns the type.

## Main statements

* `posterior_eq_pure_of_unique_sender`: A message sent only by `θ₀` has posterior `pure θ₀`.
* `IsSeparating.posterior_eq_pure`: Under a full-support prior, every on-path message's posterior
  is the point mass at its unique sender.
* `IsSeparating.belief_eq_pure`: Bayes consistency forces the equilibrium belief at a separating
  message to the point mass at its sender.

## Notes

For the two-type combinatorial fact that a separating strategy is a pair of opposite point masses,
see `FinDist.eq_pure_pair_of_disjoint_fin_two`.

## References

* Spence, Michael. 1973. “Job Market Signaling.” *The Quarterly Journal of Economics* 87 (3): 355.
  [https://doi.org/10.2307/1882010](https://doi.org/10.2307/1882010).
* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling games, separating equilibrium, bayes consistency, perfect bayesian equilibrium
-/

@[expose] public noncomputable section

open Econlib.Probability Econlib.GameTheory

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-- When only `θ₀` sends `m` with positive probability (and the prior supports `θ₀`), the posterior
at `m` is the point mass at `θ₀`: The message identifies the sender. -/
lemma posterior_eq_pure_of_unique_sender {σ : sg.SenderMixedStrategy} {m : sg.Msg}
    {θ₀ : sg.Theta} (hprior : 0 < sg.prior.pmf θ₀) (hpos : 0 < (σ θ₀).pmf m)
    (hzero : ∀ θ, θ ≠ θ₀ → (σ θ).pmf m = 0) :
    sg.posterior σ m = FinDist.pure θ₀ := by
  have hmarg_pos := sg.marginalProb_pos hprior hpos
  -- All marginal mass at `m` comes from `θ₀`.
  have hmarg_eq : sg.marginalProb σ m = sg.prior.pmf θ₀ * (σ θ₀).pmf m := by
    rw [marginalProb_eq_sum, Finset.sum_eq_single θ₀]
    · intro θ _ hθ
      rw [hzero θ hθ]
      ring
    · intro h
      exact absurd (Finset.mem_univ θ₀) h
  apply FinDist.ext
  intro θ
  rw [sg.posterior_apply σ m θ hmarg_pos, FinDist.pure_pmf]
  by_cases hθ : θ = θ₀
  · subst hθ
    rw [if_pos rfl, hmarg_eq]
    exact div_self (ne_of_gt (mul_pos hprior hpos))
  · rw [if_neg (fun h => hθ h.symm), hzero θ hθ]
    ring

/-- Under a separating strategy with a full-support prior, every on-path message's posterior is the
point mass at its (unique) sender. -/
lemma IsSeparating.posterior_eq_pure {sg : SignalingGame} {a : sg.SignalingAssessment}
    (hsep : sg.IsSeparating a) {m : sg.Msg} {θ₀ : sg.Theta}
    (hprior : 0 < sg.prior.pmf θ₀) (hpos : 0 < (a.senderStrategy θ₀).pmf m) :
    sg.posterior a.senderStrategy m = FinDist.pure θ₀ := by
  refine sg.posterior_eq_pure_of_unique_sender hprior hpos fun θ hθ => ?_
  -- Separation: `θ` and `θ₀` cannot both put positive mass on `m`.
  by_contra hne
  exact hsep θ θ₀ hθ m
    ⟨lt_of_le_of_ne ((a.senderStrategy θ).nonneg m) (Ne.symm hne), hpos⟩

/-- **Bayes consistency forces belief = point mass at separating messages.** The receiver learns
the type: At any message sent (with positive probability) only by `θ₀`, the equilibrium belief is
`pure θ₀`. -/
lemma IsSeparating.belief_eq_pure {sg : SignalingGame} {a : sg.SignalingAssessment}
    (hsep : sg.IsSeparating a) (hBC : sg.signalingBayesConsistent a)
    {m : sg.Msg} {θ₀ : sg.Theta}
    (hprior : 0 < sg.prior.pmf θ₀) (hpos : 0 < (a.senderStrategy θ₀).pmf m) :
    a.belief m = FinDist.pure θ₀ := by
  rw [hBC m (sg.marginalProb_pos hprior hpos)]
  exact hsep.posterior_eq_pure hprior hpos

end SignalingGame

end Econlib.GameTheory

end
