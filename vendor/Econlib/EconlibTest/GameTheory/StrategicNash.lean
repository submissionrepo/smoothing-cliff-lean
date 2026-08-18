/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.MatchingPennies
import EconlibExamples.GameTheory.PrisonersDilemma
import Mathlib

/-!
# Nash, Mixed Extension, Refinements, Correlated & Coordination — Non-Vacuity Checks

Compile-time semantic witnesses for the complete-information strategic layer
(`Econlib.GameTheory.Strategic.{Basic, Refinements, CorrelatedEquilibrium, Coordination}`),
anchored on two hand-solved games imported from `EconlibExamples`:

* **Matching pennies** — a 2×2 zero-sum game whose *only* Nash equilibrium is the uniform mixture
  `(1/2, 1/2)` with value `0` for both players, and which has *no* pure equilibrium.
* **Prisoner's dilemma** — `T=5 > R=3 > P=1 > S=0`, where defection (`1 : Fin 2`) strictly
  dominates cooperation, so mutual defection is the unique (pure and mixed) Nash equilibrium.

The failure modes these catch:

* **player/action index swaps** — `nashPred_swap_iff` / `mixedNashPred_swap_iff` deviations are at
  the deviating player's coordinate; a swap would let an opponent's coordinate move and break the
  uniqueness witnesses (`mp_mixed_nash_unique`, `pd_pure_nash_unique`, `pd_mixed_nash_unique`) and
  the no-pure-Nash witness `mp_no_pure_nash`; the player/action-transpose guard on `marginalD` is
  the asymmetric device `asymDevice` (`asymDevice_marginals_differ`, `1/3 ≠ 1/4`);
* **best-response direction reversals** — the equilibrium payoff must *weakly beat* every deviation
  (`≥`); a flipped `≤` would make the non-equilibrium pure profiles of matching pennies pass and
  the dominant-defect profile of PD fail;
* **vacuous refinements** — every trembling-hand-perfect / proper equilibrium must actually *be* a
  Nash equilibrium (`is_mixed_nash`), and the perturbation feasibility must force total mixedness
  (`isTotallyMixed_of_feasible`);
* **correlated-equilibrium marginals** — the product device `ofMixed` of a Nash mixture must be a
  correlated equilibrium with the *right* `(1/2, 1/2)` marginals (`nash_is_correlated`,
  `marginal_sum_one`);
* **coordination multiplicity** — opposing boundary payoff signs give two distinct symmetric
  equilibria plus an interior one (`SymCoordGame.multiple_equilibria`,
  `mixed_equilibrium_exists_BNE`), with strict monotonicity pinning interior uniqueness.
-/

noncomputable section

namespace EconlibTest.GameTheory.StrategicNash

open Econlib.GameTheory
open EconlibExamples.GameTheory.MatchingPennies (matchingPennies p0 p1 uniformProfile uniformAction)
open EconlibExamples.GameTheory.PrisonersDilemma
  (prisonersDilemma defectProfile defectMixedProfile cooperateProfile)

/-! ## `mkFin` projections and `ActionOf` instances

The smart constructor exposes the carriers as `Fin n` definitionally; the projection simp
lemmas and the per-player `Fintype`/`DecidableEq`/`Inhabited` instances are what let `fin_cases`,
`decide` and `Finset.univ` work over a concrete game's players and actions. -/

/-- `mkFin_Player`: The player carrier of matching pennies is `Fin 2`. -/
theorem mp_player_eq : matchingPennies.Player = Fin 2 := FiniteStrategicGame.mkFin_Player ..

/-- `mkFin_Action`: Each action space of matching pennies is `Fin 2`. -/
theorem mp_action_eq (i : matchingPennies.Player) : matchingPennies.Action i = Fin 2 :=
  FiniteStrategicGame.mkFin_Action ..

/-- The per-player `Fintype (Action i)` instance gives a 4-element profile space `Fin 2 → Fin 2`. -/
theorem mp_profile_card : Fintype.card matchingPennies.ActionProfile = 4 := by
  simp [FiniteStrategicGame.ActionProfile]

/-- The per-player `DecidableEq (Action i)` instance decides equality of actions: Heads `0` and
tails `1` are distinct, so `decide` closes the disequality. -/
theorem mp_actions_distinct : (0 : matchingPennies.Action p0) ≠ 1 := by decide

/-! ## Pure Nash: `nashPred` substrate and the no-pure-equilibrium witness -/

/-- `nashPred_swap_iff`: A legal pure deviation of `σ` by player `i` is exactly a single-coordinate
update at `i`. This is the *direction* check: Deviations move only the deviator's own action. -/
theorem mp_nashPred_swap_iff (i : matchingPennies.Player)
    (σ σ' : matchingPennies.ActionProfile) :
    matchingPennies.nashPred.swap i σ σ' ↔ ∃ a, σ' = Function.update σ i a :=
  StrategicGame.nashPred_swap_iff ..

/-- `nashPred_value_eq`: The substrate value of the pure-Nash problem is the raw payoff. -/
theorem mp_nashPred_value_eq (i : matchingPennies.Player) (σ : matchingPennies.ActionProfile) :
    matchingPennies.nashPred.value i σ = matchingPennies.payoff i σ :=
  StrategicGame.nashPred_value_eq ..

/-- **Negative check (one profile).** The all-heads profile `![0,0]` is *not* a pure Nash
equilibrium of matching pennies: Player 1 (the mismatch-winner) strictly gains by switching to
tails. A best-response *direction reversal* would wrongly accept this profile. -/
theorem mp_pure_profile_not_nash :
    ¬ matchingPennies.IsNash (![0, 0] : matchingPennies.ActionProfile) := by
  rw [StrategicGame.isNash_iff]
  intro h
  -- Player 1's deviation to tails `![0,1]` raises payoff from `-1` (match) to `1` (mismatch).
  have hdev := h p1 (1 : Fin 2)
  simp only [p1, matchingPennies, Function.update] at hdev
  norm_num at hdev

/-- **Negative check (no pure Nash at all).** Matching pennies has *no* pure-strategy Nash
equilibrium — the full no-pure-equilibrium claim the header advertises, not just a single profile.
For every pure profile the mismatch structure gives some player a strictly profitable deviation. -/
theorem mp_no_pure_nash :
    ¬ ∃ s : matchingPennies.ActionProfile, StrategicGame.IsNash _ s :=
  EconlibExamples.GameTheory.MatchingPennies.matchingPennies_no_pure_nash

/-! ## Mixed extension: `MixedStrategy`, `pureMixedStrategy`, `support`, linearity, existence -/

/-- A `MixedStrategy` is one `stdSimplex ℝ (Action i)` per player; the uniform profile is one. -/
theorem mp_uniformProfile_is_mixed : (uniformProfile : matchingPennies.MixedStrategy) p0
    = uniformAction := rfl

/-- `pureMixedStrategy`: The degenerate mixed strategy on a pure profile places unit mass on the
prescribed action. On the all-defect PD profile its defect coordinate carries mass `1`. -/
theorem pd_pureMixed_defect_mass :
    (prisonersDilemma.pureMixedStrategy defectProfile p0) (1 : Fin 2) = 1 := by
  simp only [FiniteStrategicGame.pureMixedStrategy, defectProfile]
  exact stdSimplex.vertex_apply_self 1

/-- `support`: The support of the uniform action is *both* coordinates (each carries mass
`1/2 > 0`), witnessing a genuinely mixed strategy rather than a degenerate one. -/
theorem mp_uniform_support_full (a : Fin 2) :
    a ∈ FiniteStrategicGame.support (G := matchingPennies) (i := p0) uniformAction := by
  change (0 : ℝ) < (uniformAction : Fin 2 → ℝ) a
  change (0 : ℝ) < 1 / 2
  norm_num

/-- `support`: The *defect* support of the degenerate PD profile is the single action `1`; the
cooperate action `0` is *not* in the support (mass `0`), the negative side of the support check. -/
theorem pd_defect_support_cooperate_excluded :
    (0 : Fin 2) ∉ FiniteStrategicGame.support (G := prisonersDilemma) (i := p0)
      (prisonersDilemma.pureMixedStrategy defectProfile p0) := by
  change ¬ (0 : ℝ) < (prisonersDilemma.pureMixedStrategy defectProfile p0) 0
  rw [FiniteStrategicGame.pureMixedStrategy, defectProfile,
    stdSimplex.vertex_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  exact lt_irrefl 0

/-- `expectedPayoff_linear` (matching pennies). The own-strategy expected payoff is the convex
combination of its pure-vertex deviations — linearity in the own mixed strategy, the engine behind
the indifference criterion. Stated on matching pennies at the uniform background `uniformProfile`
with an arbitrary own deviation `y`. -/
theorem mp_expectedPayoff_linear_witness
    (y : stdSimplex ℝ (matchingPennies.Action p0)) :
    matchingPennies.expectedPayoff p0 (Function.update uniformProfile p0 y) =
      ∑ s : matchingPennies.Action p0, y s *
        matchingPennies.expectedPayoff p0
          (Function.update uniformProfile p0 (stdSimplex.vertex (S := ℝ) s)) :=
  matchingPennies.expectedPayoff_linear p0 uniformProfile y

/-- `mixedNashPred_swap_iff`: A mixed deviation moves only the deviator's own simplex coordinate. -/
theorem mp_mixedNashPred_swap_iff (i : matchingPennies.Player)
    (σ σ' : matchingPennies.MixedStrategy) :
    matchingPennies.mixedNashPred.swap i σ σ' ↔
      ∃ y, σ' = Function.update σ i y :=
  FiniteStrategicGame.mixedNashPred_swap_iff ..

/-- `mixedNashPred_value_eq`: The substrate value of the mixed-Nash problem is the expected
payoff. -/
theorem mp_mixedNashPred_value_eq (i : matchingPennies.Player)
    (σ : matchingPennies.MixedStrategy) :
    matchingPennies.mixedNashPred.value i σ = matchingPennies.expectedPayoff i σ :=
  FiniteStrategicGame.mixedNashPred_value_eq ..

/-- `exists_mixedNash` (Nash's theorem): Matching pennies admits a mixed Nash equilibrium. This is
the *abstract* existence endpoint (opaque witness); the concrete witness binding and uniqueness are
`mp_uniform_witnesses_mixedNash` and `mp_mixed_nash_unique` below. -/
theorem mp_exists_mixedNash :
    ∃ σ : matchingPennies.MixedStrategy, FiniteStrategicGame.IsMixedNash σ :=
  matchingPennies.exists_mixedNash

/-- **Concrete existence witness.** The uniform profile `(1/2, 1/2)` *is* a mixed Nash equilibrium —
binding the existential to the hand-solved equilibrium. -/
theorem mp_uniform_witnesses_mixedNash :
    ∃ σ : matchingPennies.MixedStrategy, FiniteStrategicGame.IsMixedNash σ :=
  ⟨uniformProfile,
    EconlibExamples.GameTheory.MatchingPennies.matchingPennies_uniform_is_mixed_nash⟩

/-- **Mixed-Nash uniqueness (matching pennies).** *Every* mixed Nash equilibrium of matching pennies
equals the uniform profile — the equilibrium is unique, not merely existent. This is the uniqueness
witness the header advertises; a player/action swap would break it. -/
theorem mp_mixed_nash_unique (σ : matchingPennies.MixedStrategy)
    (hσ : FiniteStrategicGame.IsMixedNash σ) : σ = uniformProfile :=
  EconlibExamples.GameTheory.MatchingPennies.matchingPennies_mixed_nash_unique σ hσ

/-- **Pure-Nash uniqueness (PD).** Every *pure* Nash equilibrium of the Prisoner's Dilemma is mutual
defection `defectProfile`. -/
theorem pd_pure_nash_unique (s : prisonersDilemma.ActionProfile)
    (hs : prisonersDilemma.IsNash s) : s = defectProfile :=
  EconlibExamples.GameTheory.PrisonersDilemma.prisonersDilemma_pure_nash_unique s hs

/-- **Mixed-Nash uniqueness (PD).** Every *mixed* Nash equilibrium of the Prisoner's Dilemma places
unit mass on defection, i.e. equals `defectMixedProfile`. -/
theorem pd_mixed_nash_unique (σ : prisonersDilemma.MixedStrategy)
    (hσ : FiniteStrategicGame.IsMixedNash σ) : σ = defectMixedProfile :=
  EconlibExamples.GameTheory.PrisonersDilemma.prisonersDilemma_mixed_nash_unique σ hσ

/-- **Direction anchor (value `0`).** The uniform mixed Nash of matching pennies pays *exactly* `0`
to player 0 — the hand-computed equilibrium value. -/
theorem mp_uniform_value_zero : matchingPennies.expectedPayoff p0 uniformProfile = 0 :=
  EconlibExamples.GameTheory.MatchingPennies.expectedPayoff_uniform_zero p0

/-- **Negative check (cooperate not a best response in PD).** Against the all-defect profile,
deviating to *cooperate* (`0`) strictly *lowers* player 0's payoff (`P=1 → S=0`). This is the
strict pure-payoff inequality confirming the dominant-defect direction; the *mixed*-Nash consequence
(every mixed Nash places unit mass on defection) is `pd_mixed_nash_unique`. -/
theorem pd_cooperate_deviation_strictly_worse :
    prisonersDilemma.payoff p0 (Function.update defectProfile p0 (0 : Fin 2)) <
      prisonersDilemma.payoff p0 defectProfile := by
  simp [prisonersDilemma, p0, defectProfile, Function.update]

/-! ## Refinements: Trembles, THP, proper equilibrium

We exhibit a concrete strictly-positive tremble constraint on matching pennies — a uniform
lower bound of `1/4` on each of the two actions, which is feasible (`1/4 + 1/4 = 1/2 ≤ 1`) — and
confirm that the uniform profile satisfies it and is therefore forced to be totally mixed. Then we
exercise the substrate simp lemmas of the perturbed / THP / proper predicates and the structural
"refinement ⇒ Nash" endpoints. -/

/-- A strictly-positive, feasible tremble constraint on matching pennies: Each action of each
player gets lower bound `1/4`. -/
def mpTremble : matchingPennies.TrembleConstraint where
  lowerBound := fun _ _ => 1 / 4
  nonneg := fun _ _ => by norm_num
  feasible := fun _ => by rw [Fin.sum_univ_two]; norm_num

/-- The tremble constraint is strictly positive (every lower bound `> 0`). -/
theorem mpTremble_strictlyPositive :
    FiniteStrategicGame.TrembleConstraint.IsStrictlyPositive matchingPennies mpTremble :=
  fun _ _ => by simp only [mpTremble]; norm_num

/-- The uniform profile (mass `1/2 ≥ 1/4` per action) is feasible under the tremble constraint. -/
theorem mpTremble_uniform_feasible :
    FiniteStrategicGame.TrembleConstraint.FeasibleMixedStrategy
      (G := matchingPennies) mpTremble uniformProfile :=
  fun _ _ => by
    change (1 : ℝ) / 4 ≤ (uniformAction : Fin 2 → ℝ) _
    change (1 : ℝ) / 4 ≤ 1 / 2
    norm_num

/-- `isTotallyMixed_of_feasible`: A feasible strategy under a strictly-positive tremble is totally
mixed. The uniform profile thereby has *strictly positive* mass on every action — non-vacuously,
the hypothesis is satisfiable. -/
theorem mpTremble_uniform_totallyMixed :
    matchingPennies.IsTotallyMixed uniformProfile :=
  FiniteStrategicGame.MixedStrategy.isTotallyMixed_of_feasible matchingPennies
    mpTremble_strictlyPositive mpTremble_uniform_feasible

/-- `perturbedPred_swap_iff`: A perturbed-game deviation swaps to a *tremble-feasible* mixed action
at the deviator's coordinate — the feasibility side-condition distinguishes it from the
unrestricted mixed-Nash swap. -/
theorem mp_perturbedPred_swap_iff (i : matchingPennies.Player)
    (σ σ' : { σ : matchingPennies.MixedStrategy //
      FiniteStrategicGame.TrembleConstraint.FeasibleMixedStrategy (G := matchingPennies)
        mpTremble σ }) :
    (matchingPennies.perturbedPred mpTremble).swap i σ σ' ↔
      ∃ y, FiniteStrategicGame.TrembleConstraint.FeasibleMixedAction
        (G := matchingPennies) mpTremble i y ∧ σ'.1 = Function.update σ.1 i y :=
  FiniteStrategicGame.perturbedPred_swap_iff ..

/-- `perturbedPred_value_eq`: The perturbed-game value is the expected payoff of the underlying
unbundled profile. -/
theorem mp_perturbedPred_value_eq (i : matchingPennies.Player)
    (σ : { σ : matchingPennies.MixedStrategy //
      FiniteStrategicGame.TrembleConstraint.FeasibleMixedStrategy (G := matchingPennies)
        mpTremble σ }) :
    (matchingPennies.perturbedPred mpTremble).value i σ =
      matchingPennies.expectedPayoff i σ.1 :=
  FiniteStrategicGame.perturbedPred_value_eq ..

/-- `thpPred_swap_iff`: The THP deviation skeleton is the mixed-Nash one. -/
theorem mp_thpPred_swap_iff (i : matchingPennies.Player)
    (σ σ' : matchingPennies.MixedStrategy) :
    matchingPennies.thpPred.swap i σ σ' ↔ ∃ y, σ' = Function.update σ i y :=
  FiniteStrategicGame.thpPred_swap_iff ..

/-- `thpPred_value_eq`: The THP value is the expected payoff. -/
theorem mp_thpPred_value_eq (i : matchingPennies.Player) (σ : matchingPennies.MixedStrategy) :
    matchingPennies.thpPred.value i σ = matchingPennies.expectedPayoff i σ :=
  FiniteStrategicGame.thpPred_value_eq ..

/-- `thpPred_valid_iff`: The THP validity filter is the limit-of-perturbed-equilibria condition. -/
theorem mp_thpPred_valid_iff (σ : matchingPennies.MixedStrategy) :
    matchingPennies.thpPred.valid σ ↔ matchingPennies.IsTHPValid σ :=
  FiniteStrategicGame.thpPred_valid_iff ..

/-- `properPred_swap_iff` / `_value_eq` / `_valid_iff`: The proper-equilibrium substrate. -/
theorem mp_properPred_swap_iff (i : matchingPennies.Player)
    (σ σ' : matchingPennies.MixedStrategy) :
    matchingPennies.properPred.swap i σ σ' ↔ ∃ y, σ' = Function.update σ i y :=
  FiniteStrategicGame.properPred_swap_iff ..

theorem mp_properPred_value_eq (i : matchingPennies.Player) (σ : matchingPennies.MixedStrategy) :
    matchingPennies.properPred.value i σ = matchingPennies.expectedPayoff i σ :=
  FiniteStrategicGame.properPred_value_eq ..

theorem mp_properPred_valid_iff (σ : matchingPennies.MixedStrategy) :
    matchingPennies.properPred.valid σ ↔ matchingPennies.IsProperValid σ :=
  FiniteStrategicGame.properPred_valid_iff ..

/-- `IsPerturbedEquilibrium_iff`: A feasible profile is a perturbed equilibrium iff its bundled
lift is an equilibrium of `perturbedPred`. -/
theorem mp_IsPerturbedEquilibrium_iff (σ : matchingPennies.MixedStrategy) :
    matchingPennies.IsPerturbedEquilibrium mpTremble σ ↔
      ∃ hfeas, (matchingPennies.perturbedPred mpTremble).IsEquilibrium
        (⟨σ, hfeas⟩ : { σ : matchingPennies.MixedStrategy //
          FiniteStrategicGame.TrembleConstraint.FeasibleMixedStrategy (G := matchingPennies)
            mpTremble σ }) :=
  FiniteStrategicGame.IsPerturbedEquilibrium_iff ..

/-- `IsTremblingHandPerfect_iff`: THP matches the refinement predicate on `thpPred`. -/
theorem mp_IsTremblingHandPerfect_iff (σ : matchingPennies.MixedStrategy) :
    matchingPennies.IsTremblingHandPerfect σ ↔
      matchingPennies.thpPred.IsRefinedEquilibrium σ :=
  FiniteStrategicGame.IsTremblingHandPerfect_iff ..

/-- `IsProperEquilibrium_iff`: Proper equilibrium matches the refinement predicate on
`properPred`. -/
theorem mp_IsProperEquilibrium_iff (σ : matchingPennies.MixedStrategy) :
    matchingPennies.IsProperEquilibrium σ ↔
      matchingPennies.properPred.IsRefinedEquilibrium σ :=
  FiniteStrategicGame.IsProperEquilibrium_iff ..

/-- `IsTremblingHandPerfect.is_mixed_nash` (endpoint implication API check): Every THP equilibrium
*is* a mixed Nash equilibrium — the refinement is not vacuously broader than Nash. This checks the
implication's API shape on the abstract THP hypothesis; it does *not* exhibit a concrete THP
equilibrium of matching pennies (which would require constructing the trembling sequence). -/
theorem mp_thp_is_mixed_nash {σ : matchingPennies.MixedStrategy}
    (hσ : matchingPennies.IsTremblingHandPerfect σ) : FiniteStrategicGame.IsMixedNash σ :=
  hσ.is_mixed_nash

/-- `IsProperEquilibrium.is_mixed_nash` (endpoint implication API check): Every proper equilibrium
is a mixed Nash equilibrium. As above, this checks the implication on the abstract
proper-equilibrium hypothesis, not on a concretely constructed proper equilibrium. -/
theorem mp_proper_is_mixed_nash {σ : matchingPennies.MixedStrategy}
    (hσ : matchingPennies.IsProperEquilibrium σ) : FiniteStrategicGame.IsMixedNash σ :=
  hσ.is_mixed_nash

/-! ## Correlated equilibrium — the fully-uncovered file

We instantiate the entire `CorrelatedStrategy` / `IsCorrelatedEq` API on a concrete
*correlation device*: The independent product `ofMixed uniformProfile` on matching pennies, whose
joint puts mass `1/4` on each of the four profiles. Its player-0 marginal recovers the uniform
`(1/2, 1/2)` mixture, and `nash_is_correlated` certifies it as a correlated equilibrium (because
the uniform profile is a mixed Nash equilibrium). -/

/-- The independent correlation device induced by the uniform mixed Nash of matching pennies. -/
def mpDevice : CorrelatedStrategy matchingPennies :=
  CorrelatedStrategy.ofMixed uniformProfile

/-- `prob` / `nonneg`: The device assigns mass `1/4` to the all-heads profile `![0,0]`. The product
device factorizes `σ 0 (s 0) · σ 1 (s 1) = 1/2 · 1/2`. -/
theorem mpDevice_prob_hh : mpDevice.prob ![0, 0] = 1 / 4 := by
  simp only [mpDevice, CorrelatedStrategy.prob, CorrelatedStrategy.ofMixed,
    Econlib.Probability.FinDist.productD]
  change (∏ j : Fin 2, (uniformProfile j) ((![0, 0] : Fin 2 → Fin 2) j)) = 1 / 4
  rw [Fin.prod_univ_two]
  change (uniformAction : Fin 2 → ℝ) 0 * (uniformAction : Fin 2 → ℝ) 0 = 1 / 4
  have : (uniformAction : Fin 2 → ℝ) 0 = 1 / 2 := rfl
  rw [this]; norm_num

/-- `nonneg`: Every joint probability is nonnegative. -/
theorem mpDevice_nonneg (s : matchingPennies.ActionProfile) : 0 ≤ mpDevice.prob s :=
  mpDevice.nonneg s

/-- **Strict positivity (the advertised "here strictly positive").** Each of the four profiles
carries mass `1/2 · 1/2 = 1/4 > 0` under the uniform product device — a zero-mass bug would be
rejected by this strict bound (which the bare `nonneg` cannot catch). -/
theorem mpDevice_pos (s : matchingPennies.ActionProfile) : 0 < mpDevice.prob s := by
  simp only [mpDevice, CorrelatedStrategy.prob, CorrelatedStrategy.ofMixed,
    Econlib.Probability.FinDist.productD]
  change 0 < ∏ j : Fin 2, (uniformProfile j) ((s : Fin 2 → Fin 2) j)
  apply Finset.prod_pos
  intro j _
  change (0 : ℝ) < (uniformAction : Fin 2 → ℝ) _
  rw [show (uniformAction : Fin 2 → ℝ) (s j) = 1 / 2 from rfl]
  norm_num

/-- `sum_one`: The joint distribution is a probability distribution (masses sum to `1`). -/
theorem mpDevice_sum_one : ∑ s : matchingPennies.ActionProfile, mpDevice.prob s = 1 :=
  mpDevice.sum_one

/-- `marginal` / `marginal_sum_one`: Player 0's marginals over the two actions sum to `1`. -/
theorem mpDevice_marginal_sum_one :
    ∑ si : matchingPennies.Action p0, mpDevice.marginal p0 si = 1 :=
  mpDevice.marginal_sum_one p0

/-- `marginal_nonneg`: Marginal recommendation probabilities are nonnegative. -/
theorem mpDevice_marginal_nonneg (si : matchingPennies.Action p0) :
    0 ≤ mpDevice.marginal p0 si :=
  mpDevice.marginal_nonneg p0 si

/-! ### Asymmetric product device (player/action transpose guard)

The uniform device is *symmetric* in players and actions, so a player/action transpose in
`marginalD` would be invisible. We build an asymmetric product device — player 0 mixes `(1/3,
2/3)`, player 1 mixes `(1/4, 3/4)` — whose two marginals are *distinct* (`1/3 ≠ 1/4`), so a
transpose is detectable. -/

/-- Player 0's asymmetric mix `(1/3, 2/3)` on heads/tails. -/
def asymAction0 : stdSimplex ℝ (matchingPennies.Action p0) :=
  ⟨![1 / 3, 2 / 3], by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    rw [Fin.sum_univ_two]; norm_num⟩

/-- Player 1's asymmetric mix `(1/4, 3/4)` on heads/tails. -/
def asymAction1 : stdSimplex ℝ (matchingPennies.Action p1) :=
  ⟨![1 / 4, 3 / 4], by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    rw [Fin.sum_univ_two]; norm_num⟩

/-- The asymmetric mixed profile: player 0 mixes `(1/3, 2/3)`, player 1 mixes `(1/4, 3/4)`. -/
def asymProfile : matchingPennies.MixedStrategy :=
  fun i => if i = 0 then asymAction0 else asymAction1

/-- The asymmetric independent correlation device. -/
def asymDevice : CorrelatedStrategy matchingPennies := CorrelatedStrategy.ofMixed asymProfile

/-- **Player 0's asymmetric marginal is `1/3`.** The fiber `{s | s 0 = 0}` is `{![0,0], ![0,1]}`,
contributing `(1/3)(1/4) + (1/3)(3/4) = 1/3`. -/
theorem asymDevice_marginal0_heads : asymDevice.marginal p0 (0 : Fin 2) = 1 / 3 := by
  simp only [asymDevice, CorrelatedStrategy.marginal, CorrelatedStrategy.ofMixed,
    Econlib.Probability.FinDist.marginalD, Econlib.Probability.FinDist.productD]
  rw [show (Finset.univ.filter (fun s : Fin 2 → Fin 2 => s 0 = 0)) = {![0, 0], ![0, 1]} from by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hs0
      obtain ⟨b, hb⟩ : ∃ b : Fin 2, s 1 = b := ⟨s 1, rfl⟩
      fin_cases b
      · left; funext k; fin_cases k <;> simp_all
      · right; funext k; fin_cases k <;> simp_all
    · rintro (rfl | rfl) <;> rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, Fin.prod_univ_two, Fin.prod_univ_two]
  have e00 : (asymAction0 : Fin 2 → ℝ) 0 = 1 / 3 := rfl
  have e10 : (asymAction1 : Fin 2 → ℝ) 0 = 1 / 4 := rfl
  have e11 : (asymAction1 : Fin 2 → ℝ) 1 = 3 / 4 := rfl
  change ((asymAction0 : Fin 2 → ℝ) 0 * (asymAction1 : Fin 2 → ℝ) 0)
      + (asymAction0 : Fin 2 → ℝ) 0 * (asymAction1 : Fin 2 → ℝ) 1 = 1 / 3
  rw [e00, e10, e11]; norm_num

/-- **Player 1's asymmetric marginal is `1/4`.** The fiber `{s | s 1 = 0}` is `{![0,0], ![1,0]}`,
contributing `(1/3)(1/4) + (2/3)(1/4) = 1/4`. -/
theorem asymDevice_marginal1_heads : asymDevice.marginal p1 (0 : Fin 2) = 1 / 4 := by
  simp only [asymDevice, CorrelatedStrategy.marginal, CorrelatedStrategy.ofMixed,
    Econlib.Probability.FinDist.marginalD, Econlib.Probability.FinDist.productD]
  rw [show (Finset.univ.filter (fun s : Fin 2 → Fin 2 => s 1 = 0)) = {![0, 0], ![1, 0]} from by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hs1
      obtain ⟨b, hb⟩ : ∃ b : Fin 2, s 0 = b := ⟨s 0, rfl⟩
      fin_cases b
      · left; funext k; fin_cases k <;> simp_all
      · right; funext k; fin_cases k <;> simp_all
    · rintro (rfl | rfl) <;> rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, Fin.prod_univ_two, Fin.prod_univ_two]
  have e00 : (asymAction0 : Fin 2 → ℝ) 0 = 1 / 3 := rfl
  have e01 : (asymAction0 : Fin 2 → ℝ) 1 = 2 / 3 := rfl
  have e10 : (asymAction1 : Fin 2 → ℝ) 0 = 1 / 4 := rfl
  change ((asymAction0 : Fin 2 → ℝ) 0 * (asymAction1 : Fin 2 → ℝ) 0)
      + (asymAction0 : Fin 2 → ℝ) 1 * (asymAction1 : Fin 2 → ℝ) 0 = 1 / 4
  rw [e00, e01, e10]; norm_num

/-- **The two marginals differ (`1/3 ≠ 1/4`): transpose guard.** A player/action transpose in
`marginalD` would read player 1's marginal at player 0's slot (or swap the action coordinate),
crossing these two distinct values — caught here. The symmetric uniform device cannot detect
this. -/
theorem asymDevice_marginals_differ :
    asymDevice.marginal p0 (0 : Fin 2) ≠ asymDevice.marginal p1 (0 : Fin 2) := by
  rw [asymDevice_marginal0_heads, asymDevice_marginal1_heads]; norm_num

/-- **The product device recovers the uniform marginal.** Player 0's marginal on heads is exactly
`1/2` — the independent device's recommendation distribution *is* the original mixed strategy. The
*asymmetric* anchors `asymDevice_marginal0_heads`/`_marginal1_heads` (distinct `1/3 ≠ 1/4`) are the
actual transpose guard; this symmetric value alone could not catch a transpose. -/
theorem mpDevice_marginal_heads : mpDevice.marginal p0 (0 : Fin 2) = 1 / 2 := by
  simp only [mpDevice, CorrelatedStrategy.marginal, CorrelatedStrategy.ofMixed,
    Econlib.Probability.FinDist.marginalD, Econlib.Probability.FinDist.productD]
  -- The fiber `{s | s 0 = 0}` is `{![0,0], ![0,1]}`; each carries `1/2 · σ1(·)`, summing to `1/2`.
  rw [show (Finset.univ.filter (fun s : Fin 2 → Fin 2 => s 0 = 0)) =
      {![0, 0], ![0, 1]} from by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hs0
      obtain ⟨b, hb⟩ : ∃ b : Fin 2, s 1 = b := ⟨s 1, rfl⟩
      fin_cases b
      · left; funext k; fin_cases k <;> simp_all
      · right; funext k; fin_cases k <;> simp_all
    · rintro (rfl | rfl) <;> rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, Fin.prod_univ_two, Fin.prod_univ_two]
  change ((uniformAction : Fin 2 → ℝ) 0 * (uniformAction : Fin 2 → ℝ) 0)
      + (uniformAction : Fin 2 → ℝ) 0 * (uniformAction : Fin 2 → ℝ) 1 = 1 / 2
  have h0 : (uniformAction : Fin 2 → ℝ) 0 = 1 / 2 := rfl
  have h1 : (uniformAction : Fin 2 → ℝ) 1 = 1 / 2 := rfl
  rw [h0, h1]; norm_num

/-- `correlatedPred_swap_iff`: A correlated-equilibrium deviation fixes the joint distribution and
modifies only the deviator player-type's response at the recommended action. -/
theorem mp_correlatedPred_swap_iff (p : Σ i : matchingPennies.Player, matchingPennies.Action i)
    (μρ μρ' : CorrelatedStrategy matchingPennies × matchingPennies.ResponsePolicy) :
    matchingPennies.correlatedPred.swap p μρ μρ' ↔
      μρ'.1 = μρ.1 ∧ ∃ si', μρ'.2 = Function.update μρ.2 p.1
        (Function.update (μρ.2 p.1) p.2 si') :=
  correlatedPred_swap_iff ..

/-- `correlatedPred_value_eq`: The substrate value is the joint-weighted obedience payoff. -/
theorem mp_correlatedPred_value_eq (p : Σ i : matchingPennies.Player, matchingPennies.Action i)
    (μρ : CorrelatedStrategy matchingPennies × matchingPennies.ResponsePolicy) :
    matchingPennies.correlatedPred.value p μρ =
      ∑ s ∈ Finset.univ.filter (fun s => s p.1 = p.2),
        μρ.1.prob s * matchingPennies.payoff p.1 (Function.update s p.1 (μρ.2 p.1 p.2)) :=
  correlatedPred_value_eq ..

/-- **`nash_is_correlated`.** The uniform-Nash product device is a correlated equilibrium of
matching pennies. Every Nash mixture is a correlated equilibrium; here the witness is concrete and
non-trivial. -/
theorem mpDevice_isCorrelatedEq : IsCorrelatedEq mpDevice :=
  nash_is_correlated
    EconlibExamples.GameTheory.MatchingPennies.matchingPennies_uniform_is_mixed_nash

/-- `IsCorrelatedEq_iff`: The device satisfies the obedience inequality for every player and
recommendation/deviation pair. *Caveat:* on matching pennies' uniform device the obedience
inequality binds at *equality* (every action is a best response at the uniform mixture), so this
witness does not exercise a *strict* obedience gap. The strict direction is the dominant-defect
pure-payoff anchor `pd_cooperate_deviation_strictly_worse` (`S=0 < P=1`). -/
theorem mpDevice_obedience
    (i : matchingPennies.Player) (si si' : matchingPennies.Action i) :
    ∑ s ∈ Finset.univ.filter (fun s => s i = si), mpDevice.prob s * matchingPennies.payoff i s ≥
      ∑ s ∈ Finset.univ.filter (fun s => s i = si),
        mpDevice.prob s * matchingPennies.payoff i (Function.update s i si') :=
  (IsCorrelatedEq_iff mpDevice).mp mpDevice_isCorrelatedEq i si si'

/-- `exists_correlatedEq`: Matching pennies admits a correlated equilibrium. -/
theorem mp_exists_correlatedEq :
    ∃ μ : CorrelatedStrategy matchingPennies, IsCorrelatedEq μ :=
  exists_correlatedEq matchingPennies

/-! ## Symmetric coordination game (`SymCoordGame`)

`SymCoordGame` is the *one-dimensional population* form of a symmetric coordination game: The
action level `σ ∈ [0,1]` is the fraction acting, and `payoff σ` is the net benefit of acting when
others act with probability `σ`. We pick the strictly-monotone linear payoff `payoff σ = 2σ − 1`,
which has opposing boundary signs (`payoff 0 = −1 < 0`, `payoff 1 = 1 > 0`) and a unique interior
zero at the mixing probability `σ = 1/2`. -/

/-- The canonical strict symmetric coordination game with linear net payoff `2σ − 1`. -/
def coordGame : StrictSymCoordGame where
  payoff := fun σ => 2 * σ - 1
  continuous := (continuous_const.mul continuous_id).sub continuous_const |>.continuousOn
  monotone := fun a _ b _ hab => by simp only; linarith
  strictMono := fun a _ b _ hab => by simp only; linarith

/-- Boundary signs: `payoff 0 = −1 < 0` and `payoff 1 = 1 > 0` — the multiplicity precondition. -/
theorem coordGame_low : coordGame.payoff 0 < 0 := by simp [coordGame]
theorem coordGame_high : 0 < coordGame.payoff 1 := by simp [coordGame]

/-- `SymCoordGame.multiple_equilibria`: Under opposing boundary signs *both* boundary profiles `0`
and `1` are symmetric BNEs — the coordination-failure multiplicity. -/
theorem coordGame_multiple_equilibria :
    coordGame.isSymmetricBNE 0 ∧ coordGame.isSymmetricBNE 1 :=
  SymCoordGame.multiple_equilibria coordGame.toSymCoordGame coordGame_low coordGame_high

/-- `mixed_equilibrium_exists_BNE`: Between the two pure equilibria lies an interior mixed BNE (the
IVT zero). -/
theorem coordGame_interior_BNE :
    ∃ σ ∈ Set.Ioo (0 : ℝ) 1, coordGame.isSymmetricBNE σ :=
  SymCoordGame.mixed_equilibrium_exists_BNE coordGame.toSymCoordGame coordGame_low coordGame_high

/-- **Direction anchor.** The interior mixing equilibrium is `σ = 1/2`: `2·(1/2) − 1 = 0`, and it
lies in `(0,1)`. This is the hand-computed mixing probability. -/
theorem coordGame_half_is_BNE : coordGame.isSymmetricBNE (1 / 2) :=
  SymCoordGame.mixed_equilibrium_is_BNE coordGame.toSymCoordGame
    ⟨by norm_num, by norm_num⟩ (by simp [coordGame])

/-- `StrictSymCoordGame.mixed_equilibrium_unique`: Under strict monotonicity the interior mixed
equilibrium is unique. We feed it two interior zeros and recover their equality. -/
theorem coordGame_interior_unique {σ₁ σ₂ : ℝ}
    (hσ₁ : σ₁ ∈ Set.Ioo (0 : ℝ) 1) (hσ₂ : σ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (h₁ : coordGame.payoff σ₁ = 0) (h₂ : coordGame.payoff σ₂ = 0) : σ₁ = σ₂ :=
  coordGame.mixed_equilibrium_unique hσ₁ hσ₂ h₁ h₂

/-- **The interior zero is *exactly* `1/2`.** Any interior indifference point `σ ∈ (0,1)` with
`payoff σ = 0` must equal `1/2`: `2σ − 1 = 0 ⇒ σ = 1/2`. This connects the abstract uniqueness to
the concrete hand-computed mixing probability — `1/2` is the *only* interior mixing probability, not
merely "two zeros are equal". -/
theorem coordGame_interior_eq_half {σ : ℝ} (_hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (h : coordGame.payoff σ = 0) : σ = 1 / 2 := by
  have : 2 * σ - 1 = 0 := h
  linarith

end EconlibTest.GameTheory.StrategicNash

end
