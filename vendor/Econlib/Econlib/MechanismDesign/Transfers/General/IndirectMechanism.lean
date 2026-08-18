/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.Dominant
public import Econlib.GameTheory.Strategic.Bayesian.PureBNE
public import Econlib.MechanismDesign.Transfers.General.SolutionConcepts

/-!
# Indirect mechanisms and Bayes–Nash equilibrium

An **indirect mechanism** equips each agent with a finite message space and maps message profiles
to an outcome and transfers. A pure message strategy `σ i : Theta i → Msg i` tells each agent-type
which message to send, and the solution concept is a Bayes–Nash equilibrium. An indirect mechanism
induces a Bayesian game (`inducedBayesianGame`), and `IsBNE σ` is defined as that game's
`Econlib.GameTheory.FinBayesianGame.IsBNE`.

## Main definitions

* `IndirectMechanism`: Finite message spaces, an outcome rule, and per-agent transfer rules.
* `IndirectMechanism.inducedBayesianGame`: The Bayesian game an indirect mechanism induces.
* `IndirectMechanism.interimUtility`: Interim expected utility of sending a message.
* `IndirectMechanism.IsBNE`: The induced game's Bayes–Nash equilibrium.
* `IndirectMechanism.IsDominantStrategy`: The induced game's dominant-strategy equilibrium.
* `IndirectMechanism.directify`: The direct mechanism realized by playing `σ`.
* `DirectMechanism.toIndirect`: A direct mechanism as the indirect mechanism whose messages are
  type reports.

## Main statements

* `interimUtility_eq_interimPayoffAction`: The bridge to `FinBayesianGame.interimPayoffAction`.
* `IsBNE_iff`: The interim best-response characterization in mechanism-design vocabulary.
* `IsDominantStrategy_iff`: The ex-post dominance characterization.
* `DirectMechanism.isBIC_iff_isBNE_truthful`: A direct mechanism is BIC exactly when truthful
  reporting is a Bayes–Nash equilibrium of its type-report form.
* `DirectMechanism.isDSIC_iff_isDominantStrategy_truthful`: A direct mechanism is DSIC exactly when
  truthful reporting is a dominant-strategy equilibrium of its type-report form.

## Notes

The mechanism-design-facing characterization of equilibrium — no agent-type prefers another message
in interim expectation — is `IsBNE_iff`; `IsDominantStrategy_iff` gives the ex-post reading. Both
follow from the corresponding `FinBayesianGame` characterizations.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, indirect mechanism, bayes-nash equilibrium, dominant strategy, revelation
principle
-/

@[expose] public section

open Function BigOperators Econlib.GameTheory

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment}

/-- An indirect (message-game) mechanism: Each agent has a finite message space, and a message
profile determines a social outcome and a monetary transfer for each agent. -/
structure IndirectMechanism (E : QuasilinearEnvironment) where
  /-- Agent `i`'s message space. -/
  Msg : E.Agent → Type*
  [instFintypeMsg : ∀ i, Fintype (Msg i)]
  [instDecEqMsg : ∀ i, DecidableEq (Msg i)]
  [instInhabitedMsg : ∀ i, Inhabited (Msg i)]
  /-- Outcome chosen at a message profile. -/
  outcome : (Π i, Msg i) → E.Outcome
  /-- Net money received by agent `i` at a message profile. -/
  pay : E.Agent → (Π i, Msg i) → ℝ

attribute [instance] IndirectMechanism.instFintypeMsg IndirectMechanism.instDecEqMsg
  IndirectMechanism.instInhabitedMsg

namespace IndirectMechanism

variable (Γ : IndirectMechanism E)

/-- A pure message strategy profile: Each agent-type chooses a message. -/
abbrev Strategy := (i : E.Agent) → E.Theta i → Γ.Msg i

/-- An indirect mechanism *is* a Bayesian game: Players are agents, types and actions are the type
and message spaces, the payoff is quasilinear in the transfer, and the prior is the common prior.
Equilibrium for the mechanism is defined as this game's Bayes–Nash equilibrium. -/
def inducedBayesianGame : FinBayesianGame where
  Player := E.Agent
  Theta := E.Theta
  Action := Γ.Msg
  payoff i a θ := E.value i (Γ.outcome a) (θ i) + Γ.pay i a
  prior := E.prior

@[simp] lemma inducedBayesianGame_prior : Γ.inducedBayesianGame.prior = E.prior := rfl

@[simp] lemma inducedBayesianGame_payoff (i : E.Agent) (a : Π j, Γ.Msg j) (θ : E.TypeProfile) :
    Γ.inducedBayesianGame.payoff i a θ = E.value i (Γ.outcome a) (θ i) + Γ.pay i a := rfl

/-- The message profile sent at type profile `θ` when every agent plays `σ`. -/
def msgProfile (σ : Γ.Strategy) (θ : E.TypeProfile) : Π i, Γ.Msg i :=
  fun j => σ j (θ j)

@[simp] lemma inducedBayesianGame_actionProfile (σ : Γ.Strategy) (θ : E.TypeProfile) :
    Γ.inducedBayesianGame.actionProfile σ θ = Γ.msgProfile σ θ := rfl

/-- Splicing a single agent's report through `σ` commutes with splicing its message. -/
lemma msgProfile_update (σ : Γ.Strategy) (i : E.Agent) (θ : E.TypeProfile) (θ_i' : E.Theta i) :
    Γ.msgProfile σ (update θ i θ_i') = update (Γ.msgProfile σ θ) i (σ i θ_i') := by
  funext j
  -- both sides agree pointwise: at `i` via `θ_i'`, elsewhere via `θ j`
  rcases eq_or_ne j i with h | h
  · subst h; simp [msgProfile]
  · simp [msgProfile, update_of_ne h]

/-- Interim expected utility of agent `i` with true type `θ_i` who sends message `m_i`, when the
others play `σ`. The expectation is over the others' types under the prior conditional on
`θ i = θ_i`. -/
def interimUtility (σ : Γ.Strategy) (i : E.Agent) (θ_i : E.Theta i) (m_i : Γ.Msg i) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : E.TypeProfile => θ i = θ_i),
    E.prior.condProbD i θ_i θ *
      (E.value i (Γ.outcome (update (Γ.msgProfile σ θ) i m_i)) (θ i)
        + Γ.pay i (update (Γ.msgProfile σ θ) i m_i))

/-- The mechanism's interim utility equals the induced game's interim payoff under a unilateral
message deviation. -/
lemma interimUtility_eq_interimPayoffAction
    (σ : Γ.Strategy) (i : E.Agent) (θ_i : E.Theta i) (m_i : Γ.Msg i) :
    Γ.interimUtility σ i θ_i m_i
      = Γ.inducedBayesianGame.interimPayoffAction i θ_i m_i σ := rfl

/-- Interim utility vanishes at zero-marginal types (junk value of the prior conditional). -/
lemma interimUtility_eq_zero_of_marginal_not_pos
    (σ : Γ.Strategy) (i : E.Agent) (θ_i : E.Theta i) (m_i : Γ.Msg i)
    (h : ¬ 0 < E.prior.marginalD i θ_i) :
    Γ.interimUtility σ i θ_i m_i = 0 := by
  unfold interimUtility
  refine Finset.sum_eq_zero fun θ _ => ?_
  rw [E.prior.condProbD_eq_zero_of_not_pos i θ_i θ h, zero_mul]

/-- **Bayes–Nash equilibrium of the mechanism**, defined as the induced game's BNE. -/
def IsBNE (σ : Γ.Strategy) : Prop :=
  Γ.inducedBayesianGame.IsBNE σ

/-- Mechanism-design characterization of equilibrium: Given the others play `σ`, every agent-type
with positive prior marginal weakly prefers its prescribed message to any other, in interim
expectation. Equivalent to `IsBNE` via the `FinBayesianGame` BNE characterization. -/
theorem IsBNE_iff (σ : Γ.Strategy) :
    Γ.IsBNE σ ↔
      ∀ (i : E.Agent) (θ_i : E.Theta i), 0 < E.prior.marginalD i θ_i →
        ∀ (m_i : Γ.Msg i),
          Γ.interimUtility σ i θ_i m_i ≤ Γ.interimUtility σ i θ_i (σ i θ_i) := by
  rw [IsBNE, FinBayesianGame.IsBNE_iff]
  exact Iff.rfl

/-- Mechanism equilibrium is a Nash equilibrium of the agent-normal-form (expanded) game. -/
theorem IsBNE_iff_isNash_expanded (σ : Γ.Strategy) :
    Γ.IsBNE σ ↔
      Γ.inducedBayesianGame.expandedGame.toStrategicGame.IsNash
        (Γ.inducedBayesianGame.toExpandedProfile σ) :=
  Γ.inducedBayesianGame.isBNE_iff_isNash_expanded σ

/-- **Dominant-strategy equilibrium of the mechanism**, defined as the induced game's. -/
def IsDominantStrategy (σ : Γ.Strategy) : Prop :=
  Γ.inducedBayesianGame.IsDominantStrategy σ

/-- Mechanism-design reading of dominant strategy: Ex-post, against any profile of others' messages
`a` and at any realized type profile `θ`, agent `i`'s prescribed message weakly beats any other. -/
theorem IsDominantStrategy_iff (σ : Γ.Strategy) :
    Γ.IsDominantStrategy σ ↔
      ∀ (i : E.Agent) (θ : E.TypeProfile) (a : Π j, Γ.Msg j) (m_i : Γ.Msg i),
        E.value i (Γ.outcome (update a i m_i)) (θ i) + Γ.pay i (update a i m_i)
          ≤ E.value i (Γ.outcome (update a i (σ i (θ i)))) (θ i)
              + Γ.pay i (update a i (σ i (θ i))) :=
  Iff.rfl

/-- The direct mechanism realized by playing strategy `σ`: Agents report types, which `σ`
translates to messages. -/
def directify (σ : Γ.Strategy) : DirectMechanism E where
  alloc θ := Γ.outcome (Γ.msgProfile σ θ)
  transfer i θ := Γ.pay i (Γ.msgProfile σ θ)

end IndirectMechanism

/-- A direct mechanism is the indirect mechanism whose message spaces are the type spaces: Agents
"message" by reporting a type, and the outcome/transfer rules act on the reported profile. -/
def DirectMechanism.toIndirect (M : DirectMechanism E) : IndirectMechanism E where
  Msg := E.Theta
  outcome := M.alloc
  pay i := M.transfer i

/-- Truthful reporting in the type-report form recovers the direct mechanism's interim utility. -/
@[simp] lemma DirectMechanism.toIndirect_interimUtility (M : DirectMechanism E)
    (i : E.Agent) (θ_i θ_i' : E.Theta i) :
    M.toIndirect.interimUtility (fun _ θ_j => θ_j) i θ_i θ_i' = M.interimUtility i θ_i θ_i' := rfl

/-- **Bayesian incentive compatibility is Bayes–Nash equilibrium of truthful reporting.** A direct
mechanism is BIC exactly when truth-telling is a Bayes–Nash equilibrium of its type-report form. -/
theorem DirectMechanism.isBIC_iff_isBNE_truthful (M : DirectMechanism E) :
    M.IsBIC ↔ M.toIndirect.IsBNE (fun _ θ_i => θ_i) := by
  rw [IndirectMechanism.IsBNE_iff]
  simp only [toIndirect_interimUtility]
  refine ⟨fun h i θ_i _ θ_i' => h i θ_i θ_i', fun h i θ_i θ_i' => ?_⟩
  by_cases hpos : 0 < E.prior.marginalD i θ_i
  · exact h i θ_i hpos θ_i'
  · rw [M.interimUtility_eq_zero_of_marginal_not_pos i θ_i θ_i' hpos]
    exact (M.interimUtility_eq_zero_of_marginal_not_pos i θ_i θ_i hpos).ge

/-- **Dominant-strategy incentive compatibility is a dominant-strategy equilibrium of truthful
reporting.** A direct mechanism is DSIC exactly when truth-telling is a (weakly) dominant strategy
of its type-report form. -/
theorem DirectMechanism.isDSIC_iff_isDominantStrategy_truthful (M : DirectMechanism E) :
    M.IsDSIC ↔ M.toIndirect.IsDominantStrategy (fun _ θ_i => θ_i) := by
  rw [IndirectMechanism.IsDominantStrategy_iff]
  refine ⟨fun h i θ a m_i => h i a (θ i) m_i, fun h i r θ_i θ_i' => ?_⟩
  simpa using h i (update r i θ_i) r θ_i'

end Econlib.MechanismDesign.Transfers.General
end
