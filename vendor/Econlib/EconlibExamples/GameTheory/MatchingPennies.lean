/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Matching Pennies: The Uniform Mixed Nash Equilibrium

Matching pennies is the canonical two-player, zero-sum game with no pure-strategy Nash equilibrium:
Any pure profile invites a profitable unilateral deviation. Its only equilibrium is in *mixed*
strategies, where each player randomizes uniformly over the two actions {Heads, Tails} (encoded
here as `Fin 2`).

This file tells the existence story twice, at two levels of effort. First, non-constructively:
*some* mixed Nash equilibrium exists, by a one-line invocation of the general existence theorem
`FiniteStrategicGame.exists_mixedNash` (Nash's theorem). Then constructively: We **exhibit** the
specific equilibrium — the uniform profile `σ⋆ j ↦ (1/2, 1/2)` — and verify that it satisfies the
equilibrium condition directly.

## The mathematics

Player 0 wins (+1) when actions match (`s 0 = s 1`); player 1 wins when they mismatch. Under the
uniform profile, *every* pure response of player `i` against the uniform mix of player `1 - i`
yields expected payoff zero, because the two equally weighted pure outcomes for the opponent
contribute exactly one +1 and one −1. The proof enters through Econlib's indifference criterion
`isMixedNash_of_vertex_indifference`, which packages the linearity argument
(`expectedPayoff_linear`): An arbitrary mixed deviation `y` is a convex combination of pure
deviations, so its payoff is `∑_s y s · 0 = 0`, matching the equilibrium payoff and giving the
required weak inequality.

## Main definitions and theorems

* `matchingPennies : FiniteStrategicGame` — the classical 2×2 zero-sum game.
* `matchingPennies_exists_mixedNash` — *some* mixed Nash equilibrium exists (non-constructive).
* `uniformProfile : matchingPennies.MixedStrategy` — both players play `(1/2, 1/2)`.
* `matchingPennies_uniform_is_mixed_nash` — the uniform profile is a mixed Nash equilibrium.
* `matchingPennies_mixed_nash_unique` — it is the *only* mixed Nash equilibrium.
* `matchingPennies_no_pure_nash` — no pure-strategy Nash equilibrium exists.
-/

noncomputable section

namespace EconlibExamples.GameTheory.MatchingPennies

open Econlib.GameTheory

/-! ## The Game -/

/-- **Matching pennies.** Two players each pick an action in `Fin 2`. Player 0 gets `+1` if the
choices match and `−1` if they differ; player 1's payoff is the opposite. This is the standard
zero-sum 2×2 normal-form game with no pure equilibrium. Built via `FiniteStrategicGame.mkFin` and
marked `abbrev` so that `(0 : matchingPennies.Player)` and `fin_cases (i : matchingPennies.Player)`
resolve directly through both projections. -/
abbrev matchingPennies : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 2) fun i s =>
    if i = 0 then
      if s 0 = s 1 then 1 else -1
    else
      if s 0 = s 1 then -1 else 1

/-- Player 0 of matching pennies. -/
abbrev p0 : matchingPennies.Player := 0

/-- Player 1 of matching pennies. -/
abbrev p1 : matchingPennies.Player := 1

/-- The heads action. Matching pennies only cares whether the two coins *match*, so the labels
never enter the payoff definition; we name them anyway so that concrete profiles below read as game
positions rather than numerology. -/
abbrev heads : Fin 2 := 0

/-- The tails action. -/
abbrev tails : Fin 2 := 1

/-! ## Sanity Checks: Pure Payoff Evaluation

Before proving anything, evaluate the payoff function on concrete profiles. Because
`matchingPennies` is a reducible `abbrev` over `mkFin`, `payoff` applied to literals is a closed
computation: Plain `simp` unfolds the definition and decides the embedded `Fin 2` equality tests.
An action profile is just a dependent function `(i : Player) → Action i`, which for `mkFin` games
is definitionally `Fin 2 → Fin 2` — so Mathlib's vector-literal notation `![heads, tails]` ("player
0 plays heads, player 1 plays tails") is accepted directly. Writing a couple of these `example`s is
cheap insurance against encoding the payoff matrix wrong. -/

example : matchingPennies.payoff p0 ![heads, heads] = 1 := by simp

example : matchingPennies.payoff p1 ![heads, heads] = -1 := by simp

example : matchingPennies.payoff p1 ![heads, tails] = 1 := by simp

/-! ## Non-Constructive Existence -/

/-- **Existence, the cheap way.** Some mixed Nash equilibrium of matching pennies exists.

This is the one-line invocation of Econlib's Nash existence theorem
(`FiniteStrategicGame.exists_mixedNash`, proved via Kakutani's fixed-point theorem). Note what it
does *not* require: No hypotheses at all beyond the game itself, because `FiniteStrategicGame`
carries finiteness of players and actions as structure fields. The price of generality is that the
witness `σ` is opaque — the theorem says nothing about *which* profile is the equilibrium. The
remainder of this file pays the constructive price and identifies the witness as the uniform
profile. -/
theorem matchingPennies_exists_mixedNash :
    ∃ σ : matchingPennies.MixedStrategy, FiniteStrategicGame.IsMixedNash σ :=
  matchingPennies.exists_mixedNash

/-! ## The Uniform Mixed Strategy -/

/-- The probability vector that places mass `1/2` on each of the two actions in `Fin 2`, packaged
as a point in the standard simplex `stdSimplex ℝ (Fin 2)`. This is the action distribution each
player uses in the uniform mixed profile.

API note: A mixed action in `FiniteStrategicGame` is a *subtype* element — the underlying pmf
`Fin 2 → ℝ` together with a proof of membership in the simplex, which unfolds to a conjunction of
pointwise nonnegativity and total mass one. The anonymous-constructor brackets `⟨_, _⟩` supply
both. -/
def uniformAction : stdSimplex ℝ (Fin 2) :=
  ⟨fun _ => 1 / 2, by
    -- Membership in `stdSimplex` is the conjunction `(∀ a, 0 ≤ pmf a) ∧ ∑ a, pmf a = 1`;
    -- `refine ⟨_, ?_⟩` splits it and `norm_num` handles the numerics.
    refine ⟨fun _ => by norm_num, ?_⟩
    -- `Fin.sum_univ_two` turns `∑ a : Fin 2, f a` into the literal `f 0 + f 1`; the simplex
    -- coordinates then sum to `1/2 + 1/2 = 1`.
    rw [Fin.sum_univ_two]; norm_num⟩

/-- The uniform mixed-strategy profile for matching pennies: Both players randomize uniformly over
their two actions. -/
def uniformProfile : matchingPennies.MixedStrategy :=
  fun _ => uniformAction

/-! ## Key Payoff Computations -/

/-- For any `f : (Fin 2 → Fin 2) → ℝ`, the sum over all four `Fin 2 → Fin 2` profiles equals the
four-term sum over the explicit profiles `(0,0), (0,1), (1,0), (1,1)`.

This is the workhorse for evaluating `expectedPayoff` by hand: Econlib defines the expected payoff
as a sum over *action profiles* (functions `(i : Player) → Action i`), and to compute it in a
concrete game you want that sum as an explicit finite enumeration. This is the four-profile
specialization of the general `sum_piFinTwo` (in `Econlib.Math.Combinatorics.Fin2`): expand the
iterated `∑ a, ∑ b` over `Fin 2` with `Fin.sum_univ_two` and normalize associativity. -/
lemma sum_action_profile (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ s : Fin 2 → Fin 2, f s
      = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [sum_piFinTwo]
  simp [Fin.sum_univ_two]
  ring

/-- Expected payoff to player 0 against a uniform player 1 is zero, regardless of what player 0
plays: The two equally weighted pure responses of player 1 contribute exactly one `+1` and one
`-1`. -/
lemma expectedPayoff_eq_zero_of_opp_uniform_p0
    (σ : matchingPennies.MixedStrategy) (hσ : σ p1 = uniformAction) :
    matchingPennies.expectedPayoff p0 σ = 0 := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  -- Enumerate the four profiles via the helper above. Note we must pass the summand explicitly:
  -- `rw` needs the motive spelled out because the binder `s` occurs under the sum.
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j))
        * matchingPennies.payoff p0 s)]
  -- Expand the product `∏ j, (σ j) (s j) = (σ 0) (s 0) * (σ 1) (s 1)`; the `Matrix.cons_val_*`
  -- lemmas evaluate the vector literals `![i, j]` at each coordinate.
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Replace `σ 1` (= `σ p1`) by `uniformAction`.
  have e0 : (σ 1) 0 = (1 / 2) := by rw [hσ]; rfl
  have e1 : (σ 1) 1 = (1 / 2) := by rw [hσ]; rfl
  rw [e0, e1]
  -- After `abbrev`-expansion of `matchingPennies`, each `payoff p0 ![i, j]` reduced
  -- inline. The decidable `Fin 2` equalities embedded in the resulting `if`s close
  -- by `decide`-fold; the residual linear combination sums to zero by `ring`.
  simp only [show ((0 : Fin 2) = 1) ↔ False from by decide,
             show ((1 : Fin 2) = 0) ↔ False from by decide,
             if_false, if_true]
  ring

/-- Symmetric statement for player 1: Same `rw [expectedPayoff_eq_sum]` → `sum_action_profile` →
coordinate-evaluation pipeline as the player-0 lemma, with the roles of the indices swapped. -/
lemma expectedPayoff_eq_zero_of_opp_uniform_p1
    (σ : matchingPennies.MixedStrategy) (hσ : σ p0 = uniformAction) :
    matchingPennies.expectedPayoff p1 σ = 0 := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j))
        * matchingPennies.payoff p1 s)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e0 : (σ 0) 0 = (1 / 2) := by
    change (σ p0) 0 = _; rw [hσ]; rfl
  have e1 : (σ 0) 1 = (1 / 2) := by
    change (σ p0) 1 = _; rw [hσ]; rfl
  rw [e0, e1]
  -- One extra wrinkle vs. the player-0 case: The payoff's outer `if i = 0` test does not reduce
  -- definitionally at `i = p1`, so we discharge it with an explicit decided iff.
  simp only [show p1 = (0 : matchingPennies.Player) ↔ False from by decide,
             show ((0 : Fin 2) = 1) ↔ False from by decide,
             if_false, if_true]
  ring

/-- The expected payoff to either player at the uniform profile is zero. -/
lemma expectedPayoff_uniform_zero (i : matchingPennies.Player) :
    matchingPennies.expectedPayoff i uniformProfile = 0 := by
  -- `i : matchingPennies.Player = Fin 2`. The `show Fin 2 from i` cast re-types `i` (up to
  -- defeq) so that `fin_cases` sees a `Fin 2` and can enumerate `i = 0`, `i = 1`.
  change matchingPennies.expectedPayoff (show Fin 2 from i) uniformProfile = 0
  fin_cases i
  · exact expectedPayoff_eq_zero_of_opp_uniform_p0 uniformProfile rfl
  · exact expectedPayoff_eq_zero_of_opp_uniform_p1 uniformProfile rfl

/-! ## Main Theorem: Uniform Profile Is a Mixed Nash Equilibrium -/

/-- **Main theorem.** The uniform mixed-strategy profile `(1/2, 1/2)` for each player is a mixed
Nash equilibrium of matching pennies.

*Proof outline.* We use the indifference characterization `isMixedNash_of_vertex_indifference`: At
the uniform profile, every player gets payoff zero against the opponent's uniform mix, regardless
of which pure action they deviate to. So the equilibrium payoff and every pure-deviation payoff are
both zero, satisfying the indifference hypothesis. -/
theorem matchingPennies_uniform_is_mixed_nash :
    FiniteStrategicGame.IsMixedNash (G := matchingPennies) uniformProfile := by
  -- The library does the heavy lifting: `isMixedNash_of_vertex_indifference` discharges
  -- "no mixed deviation profits" from the much weaker-looking "every *pure* deviation
  -- (a `stdSimplex.vertex`) yields exactly the equilibrium payoff", by linearity of
  -- `expectedPayoff` in own strategy (`expectedPayoff_linear`). For a concrete game this is
  -- the lemma to reach for: It reduces the equilibrium check to finitely many evaluations.
  apply FiniteStrategicGame.isMixedNash_of_vertex_indifference
  intro i a
  rw [expectedPayoff_uniform_zero i]
  -- Show: `expectedPayoff i (update uniformProfile i (vertex a)) = 0`. The opponent's
  -- coordinate is unchanged (still uniform), so the relevant zero-vs-opp-uniform lemma applies.
  symm
  change matchingPennies.expectedPayoff (show Fin 2 from i)
      (Function.update uniformProfile i (stdSimplex.vertex (S := ℝ) a)) = 0
  fin_cases i
  · apply expectedPayoff_eq_zero_of_opp_uniform_p0
    -- "The opponent's coordinate is untouched by my deviation" is, formally,
    -- `Function.update_of_ne` at the disequality `p1 ≠ p0` — decided by `decide` since
    -- players live in `Fin 2`. The closing `rfl` is `uniformProfile p1 = uniformAction`,
    -- true by definition.
    change Function.update uniformProfile (p0 : matchingPennies.Player)
      (stdSimplex.vertex (S := ℝ) a) p1 = uniformAction
    rw [Function.update_of_ne (by decide : (p1 : matchingPennies.Player) ≠ p0)]
    rfl
  · apply expectedPayoff_eq_zero_of_opp_uniform_p1
    change Function.update uniformProfile (p1 : matchingPennies.Player)
      (stdSimplex.vertex (S := ℝ) a) p0 = uniformAction
    rw [Function.update_of_ne (by decide : (p0 : matchingPennies.Player) ≠ p1)]
    rfl

/-! ## Uniqueness of the Mixed Equilibrium

Existence is only half the "only equilibrium" story. Here we close it: *every* mixed Nash
equilibrium of matching pennies is the uniform profile. The argument is purely linear once the
payoffs are in closed form. Writing the two players' net "Heads bias" as
`α = σ₀(H) − σ₀(T)` and `β = σ₁(H) − σ₁(T)`, player 0's equilibrium payoff is the product `α·β`
(`expectedPayoff_p0_closed`) and player 1's is `−α·β`. Player 0's two pure deviations pay `β` and
`−β`, so equilibrium forces `α·β ≥ β` and `α·β ≥ −β`. Symmetrically player 1's deviations force
`α·β ≤ α` and `α·β ≤ −α`. Treating the product `α·β` as a single unknown, these four linear
inequalities already force `α = β = 0` — both players uniform — with no nonlinear reasoning. -/

/-- Closed form for player 0's expected payoff at an arbitrary mixed profile `σ`: the product of the
two players' net Heads biases `(σ₀(H) − σ₀(T))·(σ₁(H) − σ₁(T))`. Enumerate the four pure profiles
with `sum_action_profile` and read off the `±1` payoff matrix. -/
lemma expectedPayoff_p0_closed (σ : matchingPennies.MixedStrategy) :
    matchingPennies.expectedPayoff p0 σ
      = ((σ 0) 0 - (σ 0) 1) * ((σ 1) 0 - (σ 1) 1) := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j)) * matchingPennies.payoff p0 s)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [show ((0 : Fin 2) = 1) ↔ False from by decide,
             show ((1 : Fin 2) = 0) ↔ False from by decide, if_false, if_true]
  ring

/-- Closed form for player 1's expected payoff: the negation of player 0's, since matching pennies
is zero-sum on this `±1` matrix. -/
lemma expectedPayoff_p1_closed (σ : matchingPennies.MixedStrategy) :
    matchingPennies.expectedPayoff p1 σ
      = -(((σ 0) 0 - (σ 0) 1) * ((σ 1) 0 - (σ 1) 1)) := by
  rw [FiniteStrategicGame.expectedPayoff_eq_sum]
  rw [sum_action_profile (fun s => (∏ j : Fin 2, (σ j) (s j)) * matchingPennies.payoff p1 s)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [show (p1 = (0 : matchingPennies.Player)) ↔ False from by decide,
             show ((0 : Fin 2) = 1) ↔ False from by decide, if_false, if_true]
  ring

/-- Player 0's payoff after deviating to the pure vertex `a`, against an *arbitrary* mixed profile
`σ` (player 1's coordinate `σ 1` is untouched by the deviation): the vertex's net bias times player
1's net bias. -/
lemma dev_p0_payoff (σ : matchingPennies.MixedStrategy) (a : Fin 2) :
    matchingPennies.expectedPayoff p0 (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a))
      = ((stdSimplex.vertex (S := ℝ) a) 0 - (stdSimplex.vertex (S := ℝ) a) 1)
        * ((σ 1) 0 - (σ 1) 1) := by
  rw [expectedPayoff_p0_closed,
      show (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a)) 0
          = stdSimplex.vertex (S := ℝ) a from Function.update_self ..,
      show (Function.update σ p0 (stdSimplex.vertex (S := ℝ) a)) 1
          = σ 1 from Function.update_of_ne (by decide) _ _]

/-- Player 1's payoff after deviating to the pure vertex `a`: player 0's net bias times the
vertex's net bias, negated. -/
lemma dev_p1_payoff (σ : matchingPennies.MixedStrategy) (a : Fin 2) :
    matchingPennies.expectedPayoff p1 (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a))
      = -(((σ 0) 0 - (σ 0) 1)
        * ((stdSimplex.vertex (S := ℝ) a) 0 - (stdSimplex.vertex (S := ℝ) a) 1)) := by
  rw [expectedPayoff_p1_closed,
      show (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a)) 0
          = σ 0 from Function.update_of_ne (by decide) _ _,
      show (Function.update σ p1 (stdSimplex.vertex (S := ℝ) a)) 1
          = stdSimplex.vertex (S := ℝ) a from Function.update_self ..]

/-- **Uniqueness of the mixed equilibrium.** The uniform profile is the *only* mixed Nash
equilibrium of matching pennies. -/
theorem matchingPennies_mixed_nash_unique
    (σ : matchingPennies.MixedStrategy)
    (hσ : FiniteStrategicGame.IsMixedNash σ) :
    σ = uniformProfile := by
  rw [FiniteStrategicGame.isMixedNash_iff] at hσ
  -- The two players' net Heads biases.
  set α := (σ 0) 0 - (σ 0) 1 with hα
  set β := (σ 1) 0 - (σ 1) 1 with hβ
  -- Equilibrium payoffs in closed form: `α·β` for player 0, `−α·β` for player 1.
  have hpay0 : matchingPennies.expectedPayoff p0 σ = α * β := expectedPayoff_p0_closed σ
  have hpay1 : matchingPennies.expectedPayoff p1 σ = -(α * β) := expectedPayoff_p1_closed σ
  -- Vertex coordinates: `vertex 0 = (1,0)`, `vertex 1 = (0,1)`.
  have hv0_0 : (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) 0 = 1 := stdSimplex.vertex_apply_self 0
  have hv0_1 : (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) 1 = 0 :=
    stdSimplex.vertex_apply_ne (by decide)
  have hv1_0 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) 0 = 0 :=
    stdSimplex.vertex_apply_ne (by decide)
  have hv1_1 : (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) 1 = 1 := stdSimplex.vertex_apply_self 1
  -- The four pure-vertex deviation inequalities from the Nash condition.
  have i1 : α * β ≥ β := by
    have := hσ p0 (stdSimplex.vertex (S := ℝ) (0 : Fin 2))
    rw [hpay0, dev_p0_payoff, hv0_0, hv0_1] at this; linarith
  have i2 : α * β ≥ -β := by
    have := hσ p0 (stdSimplex.vertex (S := ℝ) (1 : Fin 2))
    rw [hpay0, dev_p0_payoff, hv1_0, hv1_1] at this; linarith
  have i3 : α * β ≤ α := by
    have := hσ p1 (stdSimplex.vertex (S := ℝ) (0 : Fin 2))
    rw [hpay1, dev_p1_payoff, hv0_0, hv0_1] at this; linarith
  have i4 : α * β ≤ -α := by
    have := hσ p1 (stdSimplex.vertex (S := ℝ) (1 : Fin 2))
    rw [hpay1, dev_p1_payoff, hv1_0, hv1_1] at this; linarith
  -- Treating `α·β` as a single unknown, the four inequalities force `α = β = 0`: i.e. each
  -- player's net Heads bias vanishes.
  have hαdiff : (σ 0) 0 - (σ 0) 1 = 0 := by rw [← hα]; linarith
  have hβdiff : (σ 1) 0 - (σ 1) 1 = 0 := by rw [← hβ]; linarith
  -- Simplex normalization turns zero net bias into equal coordinates `= 1/2`.
  have hsum0 : (σ 0) 0 + (σ 0) 1 = 1 := by
    have := (σ 0).2.2; rwa [Fin.sum_univ_two] at this
  have hsum1 : (σ 1) 0 + (σ 1) 1 = 1 := by
    have := (σ 1).2.2; rwa [Fin.sum_univ_two] at this
  have c00 : (σ 0) 0 = 1 / 2 := by linarith
  have c01 : (σ 0) 1 = 1 / 2 := by linarith
  have c10 : (σ 1) 0 = 1 / 2 := by linarith
  have c11 : (σ 1) 1 = 1 / 2 := by linarith
  -- Conclude `σ = uniformProfile` coordinate by coordinate.
  funext i
  apply Subtype.ext
  funext x
  fin_cases i <;> fin_cases x <;>
    simp only [uniformProfile, uniformAction] <;>
    first | exact c00 | exact c01 | exact c10 | exact c11

/-! ## No Pure-Strategy Nash Equilibrium -/

-- `otherFin2`, `otherFin2_ne` are shipped by `Econlib.Math.Combinatorics` (Fin2.lean).
-- The involution-free corollary below has no exact upstream counterpart.
private lemma otherFin2_eq_of_ne (x y : Fin 2) (h : x ≠ y) : otherFin2 x = y := by
  fin_cases x <;> fin_cases y <;> simp_all [otherFin2]

/-- **No pure equilibrium.** Matching pennies has no pure-strategy Nash equilibrium. From any pure
profile `s`, the losing player has a strict incentive to flip their action: If `s 0 = s 1`, player
1 (the loser) gains by switching; if `s 0 ≠ s 1`, player 0 gains by switching. -/
theorem matchingPennies_no_pure_nash :
    ¬ ∃ s : matchingPennies.ActionProfile, StrategicGame.IsNash _ s := by
  rintro ⟨s, hs⟩
  -- `StrategicGame.isNash_iff` converts the bundled equilibrium predicate into its working
  -- form: For every player `i` and deviation `a`, the equilibrium payoff weakly beats the
  -- payoff at `Function.update s i a` (Econlib spells unilateral deviations with
  -- `Function.update` throughout, in both the pure and mixed theories).
  rw [StrategicGame.isNash_iff] at hs
  -- Carry `s p0`, `s p1` as `Fin 2` values explicitly.
  -- (Action 0 = Action 1 = Fin 2 definitionally.)
  by_cases h_match : (s p0 : Fin 2) = s p1
  · -- Player 1 currently gets `-1` (match). Deviating to `otherFin2 (s p1)` gives
    -- `+1` (mismatch). Note how the deviation inequality is obtained: `hs` is applied to the
    -- deviating player and the *concrete* deviating action.
    have h_dev : matchingPennies.payoff p1 s ≥ matchingPennies.payoff p1
        (Function.update s p1 (otherFin2 (s p1))) := hs p1 (otherFin2 (s p1))
    -- Both payoff evaluations below are `simp` computations: The `abbrev` lets `simp` unfold
    -- the payoff, the `Function.update_*` simp set evaluates the deviated profile at each
    -- player, and the supplied (dis)equality hypothesis decides the match test.
    have hpayoff : matchingPennies.payoff p1 s = -1 := by simp [p1, h_match]
    have hne : (s p0 : Fin 2) ≠ otherFin2 (s p1) := by rw [h_match]; exact (otherFin2_ne _).symm
    have hdev_payoff : matchingPennies.payoff p1
        (Function.update s p1 (otherFin2 (s p1))) = 1 := by simp [p1, hne]
    rw [hpayoff, hdev_payoff] at h_dev
    -- `-1 ≥ 1` is absurd; `linarith` closes it.
    linarith
  · -- Player 0 currently gets `-1` (mismatch). Deviating to `otherFin2 (s p0) = s p1`
    -- gives `+1` (match).
    have h_dev : matchingPennies.payoff p0 s ≥ matchingPennies.payoff p0
        (Function.update s p0 (otherFin2 (s p0))) :=
      hs p0 (otherFin2 (s p0))
    have hpayoff : matchingPennies.payoff p0 s = -1 := by simp [p0, h_match]
    have hflip : otherFin2 (s p0) = s p1 := otherFin2_eq_of_ne _ _ h_match
    have hdev_payoff : matchingPennies.payoff p0 (Function.update s p0 (otherFin2 (s p0))) = 1 := by
      simp [matchingPennies, p0, p1, hflip]
    rw [hpayoff, hdev_payoff] at h_dev
    linarith

end EconlibExamples.GameTheory.MatchingPennies

end
