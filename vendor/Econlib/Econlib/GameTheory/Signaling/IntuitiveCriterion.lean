/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.PBE

/-!
# Cho-Kreps intuitive criterion

The **intuitive criterion** (Cho and Kreps 1987) is a refinement of PBE for signaling games. It
restricts off-equilibrium beliefs by eliminating unreasonable inferences: If a type could never
benefit from deviating to an off-path message `m`, regardless of which receiver action — among
those that are a best response to some belief on the type space — the receiver chooses, then
beliefs at `m` should assign zero probability to that type.

The criterion has two parts in the original paper. The **belief restriction** (part 1): At every
off-path message `m` with a non-dominated type, off-path beliefs assign zero weight to
equilibrium-dominated types. **Receiver optimality on the non-dominated set** (part 2): The
receiver's action at `m` is a best response to some belief supported on the non-dominated types.

The consumer-facing refinement
`SurvivesIntuitiveCriterion a := sg.IsSignalingPBE a ∧
sg.passesICBeliefRestriction a` bundles the
belief restriction with PBE, which turns part 2 into a consequence rather than a precondition a
consumer might forget. `passesICBeliefRestriction` captures part 1 alone — a fact about an
assessment's beliefs that does not assume the assessment is a PBE.

## Main definitions

* `possibleReceiverActions`: `BR(T, m)` — pure actions that are a best response to some belief
  supported on `T ⊆ Θ`.
* `bestResponsePayoff`: The sender's best-case payoff at `m` over actions in `BR(T, m)`.
* `equilibriumDominated`: The predicate that a sender type cannot gain from an off-path message,
  given that the receiver only plays best responses to some belief on the full type space.
* `passesICBeliefRestriction`: The intuitive-criterion belief restriction, part 1 alone (guarded by
  the existence of a non-dominated type). It is not the full criterion.
* `SurvivesIntuitiveCriterion`: `IsSignalingPBE` bundled with the belief restriction. This is the
  consumer-facing refinement.
* `nonDominatedTypes`: The set of sender types not eliminated at an off-path message.

## Main statements

* `intuitive_criterion_vacuous`: When all sender types are equilibrium-dominated, the guarded
  antecedent of the criterion fails and no restriction is imposed.
* `intuitiveCriterion_eliminates_dominated_types`: Dominated sender types receive zero off-path
  belief whenever some type is non-dominated.
* `SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated`: Cho-Kreps part 2, derived — at an
  off-path message the receiver's mixed action is optimal in expectation against the
  non-dominated-supported belief.
* `SurvivesIntuitiveCriterion.receiver_supportAction_bestResponse_on_nonDominated`: Cho-Kreps part
  2 in textbook pure-action form — every action the receiver plays at an off-path message is a best
  response to a belief supported on the non-dominated types (a member of
  `possibleReceiverActions
  (nonDominatedTypes a m) m`).
* `pooling_profitable_deviation_contradicts_sender_optimality`: A pooling assessment with sender
  optimality cannot admit a profitable sender deviation.

## References

* Cho, In-Koo, and David M. Kreps. 1987. “Signaling Games and Stable Equilibria.” *The Quarterly
  Journal of Economics* 102 (2): 179. [https://doi.org/10.2307/1885060](https://doi.org/10.2307/1885060).

## Tags

signaling games, intuitive criterion, perfect bayesian equilibrium, off-path beliefs
-/

@[expose] public noncomputable section

open Econlib.Probability Econlib.GameTheory

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ## Receiver best responses to a belief

`receiverPosteriorPayoff` and `isReceiverBestResponse` live upstream in `Signaling.PBE`. -/

/-- `BR(T, m)` in Cho-Kreps notation: Pure receiver actions that are a best response to some belief
whose support lies in `T ⊆ Θ`. The intuitive criterion's domination test uses `T = Set.univ` (all
beliefs allowed). -/
def possibleReceiverActions (T : Set sg.Theta) (m : sg.Msg) : Set sg.Act :=
  { a | ∃ μ : FinDist sg.Theta,
      (∀ θ : sg.Theta, 0 < μ.pmf θ → θ ∈ T) ∧ sg.isReceiverBestResponse μ m a }

/-- Membership in `BR(T, m)` witnessed by a point belief: A best response to `pure θ` for some
`θ ∈ T` is a possible receiver action. Combine with `isReceiverBestResponse_pure_iff` to reduce the
witness obligation to a payoff-table check. -/
lemma mem_possibleReceiverActions_of_pure_belief {T : Set sg.Theta} {m : sg.Msg} {a : sg.Act}
    {θ : sg.Theta} (hθ : θ ∈ T)
    (hbr : sg.isReceiverBestResponse (FinDist.pure θ) m a) :
    a ∈ sg.possibleReceiverActions T m := by
  refine ⟨FinDist.pure θ, fun θ' hθ' => ?_, hbr⟩
  -- The point belief supports only θ itself.
  by_cases h : θ = θ'
  · exact h ▸ hθ
  · rw [FinDist.pure_apply_ne h] at hθ'
    exact absurd hθ' (lt_irrefl 0)

/-! ## The domination test

`equilibriumPayoff` lives upstream in `Signaling.PBE`. -/

/-- The Cho-Kreps best-case sender payoff at message `m`: The supremum of the sender's type-`θ`
payoff over receiver actions that are best responses to some belief supported on `T`.

For the intuitive criterion's equilibrium-dominance test, `T = Set.univ` (the receiver may hold any
belief). -/
def bestResponsePayoff (T : Set sg.Theta) (θ : sg.Theta) (m : sg.Msg) : ℝ :=
  sSup ((fun a => sg.payoff .sender θ m a) '' sg.possibleReceiverActions T m)

/-- When every action is a best response to some allowed belief — `BR(T, m)` is everything — the
Cho-Kreps best-case payoff is the supremum over all actions. In a finite game this evaluates via
`iSup_fin_two` and friends. -/
lemma bestResponsePayoff_eq_iSup_of_univ {T : Set sg.Theta} {m : sg.Msg}
    (h : sg.possibleReceiverActions T m = Set.univ) (θ : sg.Theta) :
    sg.bestResponsePayoff T θ m = ⨆ a : sg.Act, sg.payoff .sender θ m a := by
  unfold bestResponsePayoff
  rw [h, Set.image_univ]
  rfl

/-- Type `θ` is equilibrium-dominated at message `m`: The type's equilibrium payoff strictly
exceeds the best possible payoff from deviating to `m` against any receiver action that could be a
best response to some belief on the full type space.

Such a type would never rationally deviate to `m`, so the receiver should not assign positive
belief to `θ` upon observing `m`. -/
def equilibriumDominated (a : sg.SignalingAssessment) (m : sg.Msg) (θ : sg.Theta) : Prop :=
  sg.equilibriumPayoff a θ > sg.bestResponsePayoff Set.univ θ m

/-- The intuitive criterion's **belief restriction** (Cho-Kreps part 1, alone): At every off-path
message `m`, if some type is not equilibrium-dominated at `m`, then beliefs at `m` assign zero
weight to equilibrium-dominated types.

This is not the full intuitive criterion — it says nothing about receiver optimality (part 2). The
full refinement is `SurvivesIntuitiveCriterion`, which bundles this with `IsSignalingPBE`. Used on
its own, this predicate is the right tool for proving an equilibrium fails the criterion, since it
is a necessary condition.

The guard `(∃ θ, ¬ equilibriumDominated a m θ)` is essential: When every type is dominated at some
`m`, forcing the belief there to be zero on every type would contradict the FinDist sum-one
constraint. In this degenerate case Cho-Kreps imposes no restriction on beliefs. -/
def passesICBeliefRestriction (a : sg.SignalingAssessment) : Prop :=
  ∀ (m : sg.Msg), sg.isOffPath a m →
    (∃ θ : sg.Theta, ¬ sg.equilibriumDominated a m θ) →
    ∀ (θ : sg.Theta), sg.equilibriumDominated a m θ → (a.belief m).pmf θ = 0

/-- An assessment **survives the Cho-Kreps intuitive criterion**: It is a signaling PBE whose
off-path beliefs satisfy the IC belief restriction. This is the consumer-facing refinement.

Bundling `IsSignalingPBE` is what makes the criterion's second clause (receiver optimality against
a belief on the non-dominated set) a consequence rather than a side condition a consumer must
remember to compose — see `SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated`. -/
structure SurvivesIntuitiveCriterion (a : sg.SignalingAssessment) : Prop where
  /-- The assessment is a signaling perfect Bayesian equilibrium. -/
  isPBE : sg.IsSignalingPBE a
  /-- Off-path beliefs satisfy the intuitive-criterion belief restriction. -/
  passesIC : sg.passesICBeliefRestriction a

/-- The set of non-dominated types at an off-path message: Types that could potentially benefit
from deviating. -/
def nonDominatedTypes (a : sg.SignalingAssessment)
    (m : sg.Msg) : Set (sg.Theta) := { θ | ¬sg.equilibriumDominated a m θ }

/-- When all types are equilibrium-dominated at message `m`, the guarded antecedent of the
intuitive criterion fails, so the criterion imposes no constraint on beliefs at `m`. -/
lemma intuitive_criterion_vacuous (a : sg.SignalingAssessment)
    (m : sg.Msg) (h_all_dom : ∀ θ, sg.equilibriumDominated a m θ) :
    ¬ ∃ θ : sg.Theta, ¬ sg.equilibriumDominated a m θ := by
  rintro ⟨θ, hθ⟩
  exact hθ (h_all_dom θ)

/-- At an off-path message with at least one non-dominated type, the intuitive criterion assigns
zero belief to every equilibrium-dominated sender type. -/
theorem intuitiveCriterion_eliminates_dominated_types
    (a : sg.SignalingAssessment) (m : sg.Msg)
    (h_off : sg.isOffPath a m)
    (h_nonempty : ∃ θ, ¬ sg.equilibriumDominated a m θ)
    (hic : sg.passesICBeliefRestriction a) :
    ∀ θ, sg.equilibriumDominated a m θ → (a.belief m).pmf θ = 0 :=
  fun θ hdom => hic m h_off h_nonempty θ hdom

/-! ## Cho-Kreps clause 2: Receiver optimality against the belief

When the belief restriction is bundled with `IsSignalingPBE` (i.e.
`SurvivesIntuitiveCriterion`), the second clause of Cho-Kreps falls out as a theorem rather than a
hope: PBE gives the receiver Bayesian-optimal play against `a.belief m` at every message
(`IsSignalingPBE.receiver_bestResponse`, in `Signaling.PBE`), and the belief restriction confines
the support of `a.belief m` to the non-dominated types. The receiver is then a best response to a
belief on the non-dominated set. -/

/-- **Cho-Kreps clause 2, derived.** At an off-path message `m` with at least one non-dominated
type, a surviving assessment's belief is supported on the non-dominated types, and the receiver's
equilibrium (mixed) action there is a best response to that belief — it weakly dominates every pure
action. This is the receiver-optimality clause of Cho-Kreps, obtained from PBE optimality
(`IsSignalingPBE.receiver_bestResponse`) and the belief restriction without any extra hypothesis. -/
theorem SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated
    {sg : SignalingGame} {a : sg.SignalingAssessment} (h : sg.SurvivesIntuitiveCriterion a)
    (m : sg.Msg) (h_off : sg.isOffPath a m)
    (h_nonempty : ∃ θ, ¬ sg.equilibriumDominated a m θ) :
    (∀ θ, 0 < (a.belief m).pmf θ → θ ∈ sg.nonDominatedTypes a m) ∧
      ∀ a', sg.receiverPosteriorPayoff (a.belief m) m a' ≤
        (a.receiverStrategy m).expect
          (fun act => sg.receiverPosteriorPayoff (a.belief m) m act) := by
  refine ⟨fun θ hθ => ?_, h.1.receiver_bestResponse m⟩
  -- Support confinement: a dominated type would carry zero belief by the restriction, so any type
  -- with positive belief is non-dominated.
  intro hdom
  exact absurd (h.2 m h_off h_nonempty θ hdom) hθ.ne'

/-- **Cho-Kreps clause 2, pure-action form.** At an off-path message `m` with a non-dominated type,
every pure receiver action the surviving assessment actually plays at `m` — every action in the
support of `a.receiverStrategy m` — is a best response to a belief supported on the non-dominated
types: It lies in `possibleReceiverActions (nonDominatedTypes a m) m`, witnessed by the equilibrium
belief `a.belief m`.

This is the textbook support-action best-response statement of the criterion's second clause,
stated through `possibleReceiverActions`/`isReceiverBestResponse`. It strengthens the
in-expectation optimality of `receiver_optimal_on_nonDominated`: PBE gives in-expectation
optimality of the mixed action against `a.belief m`, and a mixture's expectation can dominate every
pure payoff only if each support action is itself a maximizer (`FinDist.eq_expect_of_pmf_pos`). -/
theorem SurvivesIntuitiveCriterion.receiver_supportAction_bestResponse_on_nonDominated
    {sg : SignalingGame} {a : sg.SignalingAssessment} (h : sg.SurvivesIntuitiveCriterion a)
    (m : sg.Msg) (h_off : sg.isOffPath a m)
    (h_nonempty : ∃ θ, ¬ sg.equilibriumDominated a m θ)
    {act : sg.Act} (h_supp : 0 < (a.receiverStrategy m).pmf act) :
    act ∈ sg.possibleReceiverActions (sg.nonDominatedTypes a m) m := by
  -- Witness belief: the equilibrium belief at `m`, which the restriction confines to the
  -- non-dominated set.
  refine ⟨a.belief m, ?_, ?_⟩
  · -- Support confinement, from clause 1.
    intro θ hθ hdom
    exact absurd (h.2 m h_off h_nonempty θ hdom) hθ.ne'
  · -- Best response: PBE optimality in expectation plus the support action attaining that
    -- expectation makes `act` a pointwise maximizer against `a.belief m`.
    intro a'
    have hopt := h.1.receiver_bestResponse m
    have hact : sg.receiverPosteriorPayoff (a.belief m) m act =
        (a.receiverStrategy m).expect
          (fun b => sg.receiverPosteriorPayoff (a.belief m) m b) :=
      FinDist.eq_expect_of_pmf_pos hopt h_supp
    rw [hact]
    exact hopt a'

/-! ## Pooling sender-deviation lemma -/

/-- A pooling PBE cannot also have a profitable deviation by a pooling type to another message,
because sender optimality already makes every on-support pooling message optimal.

Takes the sender-optimality fact as an explicit hypothesis; it is extractable from
`sg.IsSignalingPBE a` at the use site. -/
theorem pooling_profitable_deviation_contradicts_sender_optimality
    (a : sg.SignalingAssessment)
    (h_pool : sg.IsPooling a)
    (h_sender_opt : ∀ (θ : sg.Theta) (m : sg.Msg),
      (a.senderStrategy θ).pmf m > 0 →
      ∀ (m' : sg.Msg),
        sg.senderExpectedPayoff a.receiverStrategy θ m ≥
        sg.senderExpectedPayoff a.receiverStrategy θ m')
    (m_dev : sg.Msg)
    (θ_dev : sg.Theta)
    (h_dev_profitable : sg.senderExpectedPayoff a.receiverStrategy θ_dev m_dev
      > sg.equilibriumPayoff a θ_dev) :
    False := by
  obtain ⟨m_pool, hm_pool⟩ := h_pool
  have h1 := hm_pool θ_dev
  have h_zero : ∀ m, m ≠ m_pool → (a.senderStrategy θ_dev).pmf m = 0 := by
    intro m hm
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => (a.senderStrategy θ_dev).pmf i)
      (Finset.mem_univ m_pool)
    have hle3 := Finset.single_le_sum (f := (a.senderStrategy θ_dev).pmf)
      (fun j _ => (a.senderStrategy θ_dev).nonneg j)
      (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ m⟩)
    have hsum := (a.senderStrategy θ_dev).sum_one
    linarith [FinDist.nonneg (a.senderStrategy θ_dev) m]
  have h_eq_payoff : sg.equilibriumPayoff a θ_dev =
      sg.senderExpectedPayoff a.receiverStrategy θ_dev m_pool := by
    simp only [equilibriumPayoff, FinDist.expect_eq_sum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m_pool), h1, one_mul,
      Finset.sum_eq_zero (fun m hm => by
        rw [h_zero m (Finset.ne_of_mem_erase hm), zero_mul]), add_zero]
  have h_opt := h_sender_opt θ_dev m_pool (by rw [h1]; norm_num) m_dev
  linarith

end SignalingGame

end Econlib.GameTheory
end
