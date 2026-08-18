/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.MatchingPennies
import Mathlib

/-!
# Nash / Kakutani Existence Spine — Non-Vacuity Checks

Compile-time semantic witnesses for the shared fixed-point substrate behind Nash existence
(`Econlib.GameTheory.Equilibrium.Existence`): The Kakutani-data inputs
`NashExistenceData.{mixedStrategySet_convex, _compact, _nonempty}` and
`NashExistenceData.bestResponseSet_{subset, nonempty, convex, closedGraph}`, plus the single-slice
symmetric variants `SymmetricExistenceData.symmetricBR_{subset, nonempty, convex, closedGraph}`.
These fixed-point preconditions are consumed only inside the abstract existence proofs and are
never exercised on concrete data, so a silently-empty best-response correspondence or a
direction-reversed payoff would pass the abstract theorems unnoticed.

We anchor on the canonical Kakutani data that the existence theorems actually route through —
`matchingPennies.toNashExistenceData` and a hand-solved symmetric coordination game's
`toSymmetricExistenceData` — rather than building a parallel construction.

## The games

* **Matching pennies** (`EconlibExamples`) — the 2×2 zero-sum game whose only Nash equilibrium is
  the uniform mixture `(1/2, 1/2)`. The matcher (player 0) wants `s 0 = s 1`; the mismatcher
  (player 1) wants `s 0 ≠ s 1`. Player 0's payoff at a profile is the product of net Heads biases
  `(σ₀(H) − σ₀(T))·(σ₁(H) − σ₁(T))`, so against a *uniform* opponent (net bias `0`) every own
  mixture pays `0` (total indifference — the whole simplex is a best response), while against a
  *pure Heads* opponent (net bias `+1`) player 0 strictly prefers pure Heads (the matcher matches);
  pure Tails is then *not* a best response — the negative-witness side of the direction check.
* **Symmetric coordination** — the single-action-type symmetric game with payoff matrix
  `[[1,0],[0,1]]` (coordinate to win). Its symmetric mixed equilibrium is the uniform population
  state `(1/2, 1/2)`, at which both pure actions are best responses; we exercise the diagonal
  best-response set there.

## Failure modes caught

* **vacuous / empty best-response correspondence** — `bestResponseSet_nonempty` and
  `symmetricBR_nonempty` are shown inhabited on concrete data (the equilibrium mixture is an actual
  member), not satisfied by an empty argmax that would make the Kakutani hypothesis vacuous;
* **payoff-sign / direction flip** — the best-response *content* is pinned: Against pure Heads the
  matcher's unique best response is pure Heads and pure Tails is explicitly excluded; a sign flip
  in the payoff would swap these.
-/

noncomputable section

namespace EconlibTest.GameTheory.Equilibrium

open Econlib.GameTheory
open EconlibExamples.GameTheory.MatchingPennies
  (matchingPennies p0 p1 heads tails uniformProfile uniformAction
   expectedPayoff_eq_zero_of_opp_uniform_p0 expectedPayoff_eq_zero_of_opp_uniform_p1
   dev_p0_payoff)

/-! ## The matching-pennies Kakutani data

`matchingPennies.toNashExistenceData` is the exact `NashExistenceData` that
`FiniteStrategicGame.exists_mixedNash` feeds to Kakutani: Per-player slice is the standard simplex
`stdSimplex ℝ (Fin 2)`, the ambient space is `Fin 2 → ℝ`, and the payoff is `expectedPayoff`. -/

/-- The canonical Kakutani data of matching pennies. -/
private abbrev mpData : NashExistenceData := matchingPennies.toNashExistenceData

/-- `mixedStrategySet_convex`: The raw strategy set (the product of the per-player simplices) is
convex — one of the three Kakutani-domain preconditions. -/
theorem mp_mixedStrategySet_convex : Convex ℝ mpData.mixedStrategySet :=
  mpData.mixedStrategySet_convex

/-- `mixedStrategySet_compact`: The raw strategy set is compact. -/
theorem mp_mixedStrategySet_compact : IsCompact mpData.mixedStrategySet :=
  mpData.mixedStrategySet_compact

/-- `mixedStrategySet_nonempty`: The raw strategy set is nonempty — the Kakutani domain is not the
empty set, so the fixed-point statement is non-vacuous. -/
theorem mp_mixedStrategySet_nonempty : mpData.mixedStrategySet.Nonempty :=
  mpData.mixedStrategySet_nonempty

/-- The uniform mixed profile, viewed as a raw point of `mixedStrategySet`. Each coordinate is the
underlying `Fin 2 → ℝ` pmf of `uniformAction`. -/
private def mpUniformRaw : ↑mpData.mixedStrategySet :=
  ⟨fun _ => (uniformAction : Fin 2 → ℝ), by
    intro i _
    exact (uniformProfile i).2⟩

/-- **Total indifference against a uniform opponent.** Updating the uniform profile at player `i`
with *any* mixed action `v` pays player `i` exactly `0`: The opponent's coordinate is untouched and
still uniform, so by `expectedPayoff_eq_zero_of_opp_uniform_*` the matcher/mismatcher is
indifferent across every own deviation. This is why the best-response set at the uniform background
is the *entire* slice — the defining indifference of an interior mixed equilibrium, and the engine
behind `mp_uniform_in_bestResponseSet` below. -/
theorem mp_indifferent_against_uniform (i : matchingPennies.Player)
    (v : stdSimplex ℝ (matchingPennies.Action i)) :
    matchingPennies.expectedPayoff i (Function.update uniformProfile i v) = 0 := by
  fin_cases i
  · apply expectedPayoff_eq_zero_of_opp_uniform_p0
    rw [Function.update_of_ne (show (p1 : matchingPennies.Player) ≠ _ by decide)]; rfl
  · apply expectedPayoff_eq_zero_of_opp_uniform_p1
    rw [Function.update_of_ne (show (p0 : matchingPennies.Player) ≠ _ by decide)]; rfl

/-! ## Best-response correspondence inputs at the equilibrium background

The four Kakutani-correspondence preconditions, evaluated at the uniform background
`mpUniformRaw`. These are stated unconditionally in the library; consuming them on concrete data
shows the fixed-point hypotheses are satisfiable rather than only abstractly assumed. The
semantically loaded one is `bestResponseSet_nonempty`: The correspondence is genuinely inhabited
(not a silently empty argmax), as witnessed below by an explicit member. -/

/-- **The equilibrium mixture is a best response to itself.** The uniform raw profile lies in its
own best-response set: Against a uniform opponent every own deviation pays `0`, so the uniform
mixture (paying `0`) is among the maximizers. This is the concrete, non-vacuous inhabitant of the
Kakutani correspondence — the fixed point `kakutaniFixedPoint` will land on. -/
theorem mp_uniform_in_bestResponseSet :
    mpUniformRaw.1 ∈ mpData.bestResponseSet mpUniformRaw := by
  refine ⟨mpUniformRaw.2, fun i z => ?_⟩
  change matchingPennies.expectedPayoff i (Function.update uniformProfile i _) ≥
    matchingPennies.expectedPayoff i (Function.update uniformProfile i z)
  rw [mp_indifferent_against_uniform i, mp_indifferent_against_uniform i z]

/-- `bestResponseSet_subset`: The best-response set at the uniform background lies inside the
strategy domain (every best response is a legal mixed profile). -/
theorem mp_bestResponseSet_subset :
    mpData.bestResponseSet mpUniformRaw ⊆ mpData.mixedStrategySet :=
  mpData.bestResponseSet_subset mpUniformRaw

/-- `bestResponseSet_nonempty`: The best-response set at the uniform background is nonempty — the
Kakutani precondition is satisfied, not vacuous. Witnessed *concretely* by the explicit member
`mp_uniform_in_bestResponseSet` (the equilibrium mixture), so the nonemptiness depends on real data,
not the abstract library lemma. -/
theorem mp_bestResponseSet_nonempty :
    (mpData.bestResponseSet mpUniformRaw).Nonempty :=
  ⟨mpUniformRaw.1, mp_uniform_in_bestResponseSet⟩

/-- `bestResponseSet_convex`: The best-response set at the uniform background is convex (the argmax
of an own-affine payoff over a convex slice). -/
theorem mp_bestResponseSet_convex :
    Convex ℝ (mpData.bestResponseSet mpUniformRaw) :=
  mpData.bestResponseSet_convex mpUniformRaw

/-- `bestResponseSet_closedGraph`: The best-response correspondence has a closed graph — the
remaining Kakutani precondition (upper hemicontinuity via Berge), now exercised on concrete data. -/
theorem mp_bestResponseSet_closedGraph :
    IsClosedGraph (fun x : ↑mpData.mixedStrategySet => mpData.bestResponseSet x) :=
  mpData.bestResponseSet_closedGraph

/-! ## Best-response *content*: Indifference vs. the direction check

The spine consumers above show the correspondence is well-formed; these witnesses pin its
*value*, catching a payoff-sign flip that the well-formedness lemmas would miss. -/

/-- A background mixed profile where player 1 (the opponent of player 0) plays pure **Heads**. Only
player 1's coordinate matters for player 0's best response. -/
private def mpHeadsBg : matchingPennies.MixedStrategy :=
  fun _ => stdSimplex.vertex (S := ℝ) (heads : Fin 2)

/-- The pure-Heads opponent coordinate of `mpHeadsBg` has net Heads bias `+1`. -/
private theorem mpHeadsBg_opp_bias :
    (mpHeadsBg 1) 0 - (mpHeadsBg 1) 1 = 1 := by
  change (stdSimplex.vertex (S := ℝ) (heads : Fin 2)) 0
      - (stdSimplex.vertex (S := ℝ) (heads : Fin 2)) 1 = 1
  rw [stdSimplex.vertex_apply_self,
    stdSimplex.vertex_apply_ne (show (heads : Fin 2) ≠ 1 by decide)]
  norm_num

/-- Player 0's payoff after deviating to pure **Heads** against a pure-Heads opponent is `+1`: The
matcher matches and wins. -/
private theorem mp_dev_heads_vs_heads :
    matchingPennies.expectedPayoff p0
      (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (heads : Fin 2))) = 1 := by
  rw [dev_p0_payoff, mpHeadsBg_opp_bias, stdSimplex.vertex_apply_self,
    stdSimplex.vertex_apply_ne (show (heads : Fin 2) ≠ 1 by decide)]
  norm_num

/-- Player 0's payoff after deviating to pure **Tails** against a pure-Heads opponent is `−1`: The
matcher mismatches and loses. -/
private theorem mp_dev_tails_vs_heads :
    matchingPennies.expectedPayoff p0
      (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (tails : Fin 2))) = -1 := by
  rw [dev_p0_payoff, mpHeadsBg_opp_bias,
    stdSimplex.vertex_apply_ne (show (tails : Fin 2) ≠ 0 by decide),
    stdSimplex.vertex_apply_self]
  norm_num

/-- **The direction check: The matcher matches.** Against a pure-Heads opponent, player 0 (the
matcher) strictly prefers pure Heads (`+1`) to pure Tails (`−1`). A payoff-sign flip would reverse
this and make the mismatcher win by matching. -/
theorem mp_heads_strictly_beats_tails_vs_heads :
    matchingPennies.expectedPayoff p0
      (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (tails : Fin 2))) <
    matchingPennies.expectedPayoff p0
      (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (heads : Fin 2))) := by
  rw [mp_dev_heads_vs_heads, mp_dev_tails_vs_heads]; norm_num

/-- **Pure Heads dominates every pure deviation against pure Heads.** No *pure* deviation of
player 0 beats the matching response: against a pure-Heads opponent, Heads (`+1`) weakly dominates
both pure actions. *Scope caveat:* this quantifies over the two *vertices* `a : Fin 2`, not the
full simplex. By linearity of `expectedPayoff` in the own strategy the vertices achieve the
extremes, so the full best-response statement follows informally — but that linearity step is *not*
formalized here; this theorem is the pure-deviation check, not a full `bestResponseSet`
membership. -/
theorem mp_heads_is_pure_best_response :
    ∀ a : Fin 2, matchingPennies.expectedPayoff p0
        (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (heads : Fin 2))) ≥
      matchingPennies.expectedPayoff p0
        (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) a)) := by
  intro a
  rw [mp_dev_heads_vs_heads]
  fin_cases a
  · exact ge_of_eq mp_dev_heads_vs_heads.symm
  · -- The `a = 1` vertex *is* pure Tails; its payoff `−1` is dominated by `+1`.
    have hval : matchingPennies.expectedPayoff p0
        (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (⟨1, by norm_num⟩ : Fin 2)))
        = -1 := mp_dev_tails_vs_heads
    rw [hval]; norm_num

/-- **Negative witness (pure-vertex optimality).** Pure **Tails** fails the pure-vertex optimality
condition against a pure-Heads opponent: the Heads deviation strictly improves on it (`−1 < +1`). So
no profile with player 0 playing pure Tails can be a best response to pure Heads — the matcher does
not mismatch. (As with the positive witness, this is stated over the two pure vertices, not full
`bestResponseSet` non-membership.) A sign-flipped payoff would wrongly admit Tails here. -/
theorem mp_tails_not_best_response_vs_heads :
    ¬ ∀ a : Fin 2, matchingPennies.expectedPayoff p0
        (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) (tails : Fin 2))) ≥
      matchingPennies.expectedPayoff p0
        (Function.update mpHeadsBg p0 (stdSimplex.vertex (S := ℝ) a)) := by
  intro h
  have hbad := h heads
  rw [mp_dev_tails_vs_heads, mp_dev_heads_vs_heads] at hbad
  norm_num at hbad

/-! ## Nash endpoint reachable from this data

The Kakutani-data inputs above are exactly what `FiniteStrategicGame.exists_mixedNash` feeds
the fixed-point theorem; consuming the endpoint once is an endpoint smoke test. -/

/-- `exists_mixedNash` (Nash's theorem): Matching pennies admits a mixed Nash equilibrium. This is
an endpoint smoke test — it does not mention `mpData` or identify the witness (the existence
theorem's selection is opaque), and would still pass if the endpoint were reproved through a
different route. The concrete equilibrium identification lives in `StrategicNash.lean`
(`mp_mixed_nash_unique`). -/
theorem mp_exists_mixedNash :
    ∃ σ : matchingPennies.MixedStrategy, FiniteStrategicGame.IsMixedNash σ :=
  matchingPennies.exists_mixedNash

/-! ## Symmetric spine: A coordination game

`coordSym` is the symmetric two-player coordination game on `Fin 2` with payoff `1` for
matching and `0` for mismatching (`payoff a b = if a = b then 1 else 0`). Its symmetric mixed
equilibrium is the uniform population state `(1/2, 1/2)`: Against a uniform opponent each pure
action pays `1/2`, so the population is indifferent (the *mixed*, symmetry-respecting equilibrium
that `exists_symmetricNash` produces). We exercise the single-slice Kakutani inputs at that
diagonal. -/

/-- The symmetric coordination game on `Fin 2`: Match to win. -/
def coordSym : SymmetricGame where
  Action := Fin 2
  payoff := fun a b => if a = b then 1 else 0

/-- The canonical single-slice Kakutani data of the coordination game (slice
`stdSimplex ℝ (Fin 2)`, asymmetric payoff `G.expectedPayoff own opp`). This is the data
`exists_symmetricNash` consumes. -/
private abbrev coordData : SymmetricExistenceData := coordSym.toSymmetricExistenceData

/-- The uniform population state, as a slice element of `coordData`. -/
private def coordUniform : ↑coordData.Slice :=
  ⟨fun _ => 1 / 2, by
    refine ⟨fun _ => by norm_num, ?_⟩
    change (∑ _i : Fin 2, (1 : ℝ) / 2) = 1
    rw [Fin.sum_univ_two]; norm_num⟩

/-- `coordSym.purePayoff a x = x a`: Only the matching opponent action contributes. *Caveat:* the
coordination payoff `if a = b then 1 else 0` is *symmetric* in `(a, b)`, so this witness cannot
detect an own/opponent transpose or a swapped payoff-argument bug — under a transpose the formula
reads the same. (Pinning the argument order would require a separate asymmetric-payoff symmetric
game; the matching-pennies anchors above already pin direction on the asymmetric side.) -/
private theorem coordSym_purePayoff (a : Fin 2) (x : coordSym.MixedStrategy) :
    coordSym.purePayoff a x = (x : Fin 2 → ℝ) a := by
  change (∑ b : Fin 2, (x : Fin 2 → ℝ) b * (if a = b then (1 : ℝ) else 0)) = (x : Fin 2 → ℝ) a
  rw [Fin.sum_univ_two]
  fin_cases a <;> norm_num

/-- **Indifference at the uniform diagonal.** Against the uniform opponent, *every* own population
state pays exactly `1/2`: `expectedPayoff own uniform = ∑ a own(a)·(1/2) = 1/2`. So the symmetric
best-response set at the uniform diagonal is the whole slice — the defining indifference of the
symmetric mixed equilibrium. -/
private theorem coordSym_expectedPayoff_vs_uniform (own : coordSym.MixedStrategy) :
    coordSym.expectedPayoff own coordUniform = 1 / 2 := by
  change (∑ a, (own : Fin 2 → ℝ) a * coordSym.purePayoff a coordUniform) = 1 / 2
  have hpp : ∀ a, coordSym.purePayoff a coordUniform = 1 / 2 := by
    intro a; rw [coordSym_purePayoff]; rfl
  simp_rw [hpp]
  rw [← Finset.sum_mul]
  have hsum : (∑ a, (own : Fin 2 → ℝ) a) = 1 := own.2.2
  rw [hsum]; norm_num

/-- **The uniform diagonal is a symmetric best response to itself.** The uniform population state
lies in its own symmetric best-response set: against a uniform opponent every own state pays `1/2`,
so the uniform state is among the maximizers. This is *one* concrete, non-vacuous inhabitant /
fixed point of the symmetric Kakutani correspondence (the coordination game also has the two pure
symmetric fixed points; this witness exhibits the uniform one, not "the one Kakutani selects"). -/
theorem coord_uniform_in_symmetricBR :
    coordUniform.1 ∈ coordData.symmetricBR coordUniform := by
  refine ⟨coordUniform.2, fun z => ?_⟩
  change coordSym.expectedPayoff coordUniform coordUniform ≥
    coordSym.expectedPayoff z coordUniform
  rw [coordSym_expectedPayoff_vs_uniform, coordSym_expectedPayoff_vs_uniform]

/-- `symmetricBR_subset`: The symmetric best-response set at the uniform diagonal lies inside the
slice (every best response is a legal population state). -/
theorem coord_symmetricBR_subset :
    coordData.symmetricBR coordUniform ⊆ coordData.Slice :=
  coordData.symmetricBR_subset coordUniform

/-- `symmetricBR_nonempty`: The symmetric best-response set at the uniform diagonal is nonempty —
the symmetric Kakutani precondition is satisfied, not vacuous. Witnessed *concretely* by the
explicit member `coord_uniform_in_symmetricBR`. -/
theorem coord_symmetricBR_nonempty :
    (coordData.symmetricBR coordUniform).Nonempty :=
  ⟨coordUniform.1, coord_uniform_in_symmetricBR⟩

/-- `symmetricBR_convex`: The symmetric best-response set at the uniform diagonal is convex. -/
theorem coord_symmetricBR_convex :
    Convex ℝ (coordData.symmetricBR coordUniform) :=
  coordData.symmetricBR_convex coordUniform

/-- `symmetricBR_closedGraph`: The symmetric best-response correspondence has a closed graph — the
final symmetric Kakutani precondition, exercised on concrete data. -/
theorem coord_symmetricBR_closedGraph :
    IsClosedGraph coordData.symmetricBR :=
  coordData.symmetricBR_closedGraph

/-! ## Symmetric Nash endpoint reachable from this data -/

/-- `exists_symmetricNash` on the same `coordData` substrate: The coordination game admits a
symmetric mixed Nash equilibrium. -/
theorem coord_exists_symmetricNash :
    ∃ x : coordSym.MixedStrategy, coordSym.IsSymmetricNash x :=
  coordSym.exists_symmetricNash

/-- The uniform population state *is* a symmetric Nash equilibrium of the coordination game: against
itself it pays `1/2`, and every deviation also pays `1/2` (pure indifference at the mixed
equilibrium). *Caveat:* because every deviation binds at `1/2`, this witness is
direction-insensitive on its own; the strict off-uniform direction guard is
`coord_heads_strictly_beats_tails_vs_heads` below (against pure Heads, own Heads pays
`1 > 0 = ` own Tails). -/
theorem coord_uniform_is_symmetricNash :
    coordSym.IsSymmetricNash coordUniform := by
  rw [coordSym.IsSymmetricNash_iff]
  intro y
  rw [coordSym_expectedPayoff_vs_uniform, coordSym_expectedPayoff_vs_uniform]

/-- The pure-Heads population state `(1, 0)` for the coordination game. -/
private def coordHeads : coordSym.MixedStrategy := stdSimplex.vertex (S := ℝ) (0 : Fin 2)

/-- Against a pure-Heads opponent, own Heads pays `1` (coordinate to win). -/
private theorem coord_heads_vs_heads : coordSym.purePayoff (0 : Fin 2) coordHeads = 1 := by
  rw [coordSym_purePayoff]; exact stdSimplex.vertex_apply_self (0 : Fin 2)

/-- Against a pure-Heads opponent, own Tails pays `0` (mismatch, lose). -/
private theorem coord_tails_vs_heads : coordSym.purePayoff (1 : Fin 2) coordHeads = 0 := by
  rw [coordSym_purePayoff]; exact stdSimplex.vertex_apply_ne (by decide : (0 : Fin 2) ≠ 1)

/-- **Strict off-uniform direction guard.** At the *pure-Heads* background (off the uniform
diagonal, where indifference no longer holds), own Heads strictly beats own Tails: `1 > 0`. A
payoff-sign flip (rewarding mismatch) would reverse this. This is the direction content the
uniform-diagonal indifference witness `coord_uniform_is_symmetricNash` cannot supply. -/
theorem coord_heads_strictly_beats_tails_vs_heads :
    coordSym.purePayoff (1 : Fin 2) coordHeads < coordSym.purePayoff (0 : Fin 2) coordHeads := by
  rw [coord_heads_vs_heads, coord_tails_vs_heads]; norm_num

end EconlibTest.GameTheory.Equilibrium

end
