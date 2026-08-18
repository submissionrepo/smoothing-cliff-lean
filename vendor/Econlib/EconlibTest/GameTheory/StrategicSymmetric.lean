/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import Mathlib

/-!
# Symmetric Games / ESS — Non-Vacuity Checks (Hawk–Dove)

Compile-time semantic witnesses for the symmetric-game / evolutionary-stability layer
(`Econlib.GameTheory.Strategic.Symmetric`), anchored on the **Hawk–Dove** game hand-solved below.

## The game and the ESS (hand-computed)

Resource value `V = 2`, fight cost `C = 4`. Action `0 = Hawk`, `1 = Dove`. The payoff to the *row*
player (own action vs. opponent action) is

|      | Hawk           | Dove      |
| ---- | -------------: | --------: |
| Hawk | `(V−C)/2 = −1` | `V = 2`   |
| Dove | `0`            | `V/2 = 1` |

Against a population state `x = (p, 1−p)`, the two pure payoffs are `u(Hawk, x) = 2 − 3p` and
`u(Dove, x) = 1 − p`; they are equal at `p = 1/2`, so the **mixed state `(1/2, 1/2)` is a symmetric
Nash equilibrium**. It is moreover an **ESS**: For any mutant `y = (q, 1−q)`,

`E[x, y] − E[y, y] = 2·(q − 1/2)² ≥ 0`,

strictly positive whenever `y ≠ x` (i.e. `q ≠ 1/2`). So `(1/2, 1/2)` resists every mutant invasion.

The failure modes these catch:

* a **symmetry-axis transpose** in `payoff a b` (reading the matrix `payoff b a`) would change
  `u(Hawk, x) = ∑_b x_b·payoff(b, Hawk)` to `x₀·(−1) + x₁·0 = −p` (not `2 − 3p`), moving the
  indifference point off `1/2`; the asymmetric off-axis anchors `purePayoff_hawk_vs_dove = 2` and
  `purePayoff_dove_vs_hawk = 0` pin the argument order, since a transpose would swap them;
* a **best-response direction reversal** would make the symmetric-Nash inequality fail; at the
  mixed equilibrium `half` every strategy is indifferent (`E[·, half] = 1/2`), so the strict
  direction is checked by the pure-profile negative witnesses `pureHawk_not_symmetricNash`
  (`0 > −1`) and `pureDove_not_symmetricNash` (`2 > 1`);
* a **vacuous ESS** (where no mutant is actually strictly worse) is ruled out by exhibiting the
  strict `2·(q−1/2)² > 0` gap and using it to prove `IsESS`, then `IsESS.is_symmetricNash`;
* a **replicator sign reversal** is caught by the off-equilibrium interior state `(1/4, 3/4)`, where
  the Hawk component grows (`replicator Hawk > 0`) and the Dove component shrinks
  (`replicator Dove < 0`).
-/

noncomputable section

namespace EconlibTest.GameTheory.StrategicSymmetric

open Econlib.GameTheory
open scoped BigOperators

/-! ## The Hawk–Dove game and the candidate ESS -/

/-- **Hawk–Dove** with `V = 2`, `C = 4`. Action `0 = Hawk`, `1 = Dove`; `payoff own opp` is the
row-player payoff. Marked `@[reducible]` so `hawkDove.Action` reduces to `Fin 2` for numeric
literals and `fin_cases`. -/
@[reducible] def hawkDove : SymmetricGame where
  Action := Fin 2
  payoff := fun a b =>
    if a = 0 then
      (if b = 0 then -1 else 2)   -- Hawk vs Hawk = (V−C)/2 = −1; Hawk vs Dove = V = 2
    else
      (if b = 0 then 0 else 1)    -- Dove vs Hawk = 0; Dove vs Dove = V/2 = 1

/-- The candidate ESS / mixed state `(1/2, 1/2)` over `{Hawk, Dove}`. -/
def half : hawkDove.MixedStrategy :=
  ⟨fun _ => 1 / 2, by
    refine ⟨fun _ => by norm_num, ?_⟩
    change ∑ _a : Fin 2, (1 : ℝ) / 2 = 1
    rw [Fin.sum_univ_two]; norm_num⟩

@[simp] theorem half_apply (a : Fin 2) : (half : Fin 2 → ℝ) a = 1 / 2 := rfl

/-! ## Closed forms for the symmetric payoff operators -/

/-- Pure payoff to action `a` against `x = (x₀, x₁)`: Read off the matrix and sum over the opponent
distribution. -/
theorem purePayoff_eq (a : Fin 2) (x : hawkDove.MixedStrategy) :
    hawkDove.purePayoff a x =
      (x : Fin 2 → ℝ) 0 * hawkDove.payoff a 0 + (x : Fin 2 → ℝ) 1 * hawkDove.payoff a 1 := by
  simp only [SymmetricGame.purePayoff, Fin.sum_univ_two]

/-- Expected payoff `E[x, y] = ∑ₐ xₐ · u(a, y)`, expanded over the two actions. -/
theorem expectedPayoff_eq (x y : hawkDove.MixedStrategy) :
    hawkDove.expectedPayoff x y =
      (x : Fin 2 → ℝ) 0 * hawkDove.purePayoff 0 y
        + (x : Fin 2 → ℝ) 1 * hawkDove.purePayoff 1 y := by
  simp only [SymmetricGame.expectedPayoff, Fin.sum_univ_two]

/-- **Fully expanded bilinear payoff.** With `hawkDove`'s entries
(`u(H,H)=−1, u(H,D)=2, u(D,H)=0, u(D,D)=1`), the expected payoff is the exact polynomial
`E[x, y] = x₀·(−y₀ + 2·y₁) + x₁·y₁` in the four coordinates. (Under the simplex constraints
`x₀+x₁ = y₀+y₁ = 1` this equals `1 + x₀ − y₀ − 2·x₀·y₀`.) This is the workhorse for the
indifference / ESS computations. -/
theorem expectedPayoff_poly (x y : hawkDove.MixedStrategy) :
    hawkDove.expectedPayoff x y =
      (x : Fin 2 → ℝ) 0 * ((y : Fin 2 → ℝ) 0 * (-1) + (y : Fin 2 → ℝ) 1 * 2)
        + (x : Fin 2 → ℝ) 1 * ((y : Fin 2 → ℝ) 0 * 0 + (y : Fin 2 → ℝ) 1 * 1) := by
  rw [expectedPayoff_eq, purePayoff_eq, purePayoff_eq]
  norm_num [hawkDove]

/-! ## The symmetric-Nash substrate -/

/-- `symmetricPred_swap_iff`: A symmetric-Nash deviation fixes the opponent coordinate `.2`. -/
theorem hd_symmetricPred_swap_iff (i : Fin 1)
    (p p' : hawkDove.MixedStrategy × hawkDove.MixedStrategy) :
    hawkDove.symmetricPred.swap i p p' ↔ p'.2 = p.2 :=
  SymmetricGame.symmetricPred_swap_iff ..

/-- `symmetricPred_value_eq`: The substrate value is the asymmetric expected payoff `E[p₁, p₂]`. -/
theorem hd_symmetricPred_value_eq (i : Fin 1)
    (p : hawkDove.MixedStrategy × hawkDove.MixedStrategy) :
    hawkDove.symmetricPred.value i p = hawkDove.expectedPayoff p.1 p.2 :=
  SymmetricGame.symmetricPred_value_eq ..

/-- `essPred_swap_iff` / `essPred_value_eq`: The ESS refinement inherits the symmetric deviation
skeleton and value. -/
theorem hd_essPred_swap_iff (i : Fin 1)
    (p p' : hawkDove.MixedStrategy × hawkDove.MixedStrategy) :
    hawkDove.essPred.swap i p p' ↔ p'.2 = p.2 :=
  SymmetricGame.essPred_swap_iff ..

theorem hd_essPred_value_eq (i : Fin 1)
    (p : hawkDove.MixedStrategy × hawkDove.MixedStrategy) :
    hawkDove.essPred.value i p = hawkDove.expectedPayoff p.1 p.2 :=
  SymmetricGame.essPred_value_eq ..

/-! ## The half mixture is a symmetric Nash and an ESS -/

/-- **`(1/2,1/2)` is a symmetric Nash equilibrium.** At the half state both pure payoffs equal
`1/2`, so no mutant `y` beats it: `E[y, x] = 1/2 = E[x, x]`. *Direction caveat:* at the mixed
equilibrium every strategy is indifferent (`E[y, half] = 1/2` for all `y`), so this witness alone
binds at equality and would survive a best-response *direction reversal*. The strict-direction guard
is supplied by the pure-profile negative witnesses `pureHawk_not_symmetricNash` and
`pureDove_not_symmetricNash` below, where the correct and reversed inequalities separate
strictly. -/
theorem half_isSymmetricNash : hawkDove.IsSymmetricNash half := by
  rw [hawkDove.IsSymmetricNash_iff]
  intro y
  -- `E[half, half] = 1/2`, and `E[y, half] = 1/2` for every `y` (both pure payoffs are `1/2`).
  rw [expectedPayoff_poly, expectedPayoff_poly]
  have hy : (y : Fin 2 → ℝ) 0 + (y : Fin 2 → ℝ) 1 = 1 := by
    have := y.2.2; rwa [Fin.sum_univ_two] at this
  have h0 : (half : Fin 2 → ℝ) 0 = 1 / 2 := rfl
  have h1 : (half : Fin 2 → ℝ) 1 = 1 / 2 := rfl
  rw [h0, h1]
  nlinarith [hy]

/-- The half mixture's self-payoff is the hand-computed value `E[x, x] = 1/2`. -/
theorem half_self_value : hawkDove.expectedPayoff half half = 1 / 2 := by
  rw [expectedPayoff_poly]
  have h0 : (half : Fin 2 → ℝ) 0 = 1 / 2 := rfl
  have h1 : (half : Fin 2 → ℝ) 1 = 1 / 2 := rfl
  rw [h0, h1]; norm_num

/-! ### Pure-profile negative witnesses (best-response direction guard)

At the mixed equilibrium `half` every strategy is indifferent, so the symmetric-Nash inequality
binds at equality and cannot detect a *reversed* best-response condition. The pure profiles below
separate the inequality strictly: pure Hawk is beaten by a Dove deviation (`0 > −1`), and pure Dove
is beaten by a Hawk deviation (`2 > 1`), so neither is a symmetric Nash. A reversed inequality would
*wrongly certify* them as equilibria — this is the direction guard. -/

/-- The pure-Hawk population state `(1, 0)` (unit mass on `Hawk`). -/
def pureHawk : hawkDove.MixedStrategy :=
  ⟨fun a => if a = 0 then 1 else 0, by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    change ∑ a : Fin 2, (if a = 0 then (1:ℝ) else 0) = 1
    rw [Fin.sum_univ_two]; norm_num⟩

/-- The pure-Dove population state `(0, 1)` (unit mass on `Dove`). -/
def pureDove : hawkDove.MixedStrategy :=
  ⟨fun a => if a = 1 then 1 else 0, by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    change ∑ a : Fin 2, (if a = 1 then (1:ℝ) else 0) = 1
    rw [Fin.sum_univ_two]; norm_num⟩

@[simp] theorem pureHawk_0 : (pureHawk : Fin 2 → ℝ) 0 = 1 := rfl
@[simp] theorem pureHawk_1 : (pureHawk : Fin 2 → ℝ) 1 = 0 := rfl
@[simp] theorem pureDove_0 : (pureDove : Fin 2 → ℝ) 0 = 0 := rfl
@[simp] theorem pureDove_1 : (pureDove : Fin 2 → ℝ) 1 = 1 := rfl

/-- **Off-axis pure payoff `u(Hawk, Dove) = 2` (transpose guard).** The Hawk-against-Dove payoff is
the temptation value `V = 2`. A symmetry-axis transpose (`payoff b a`) would instead read
`u(Dove, Hawk) = 0`, so this asymmetric anchor pins the argument order of `payoff`. -/
theorem purePayoff_hawk_vs_dove : hawkDove.purePayoff 0 pureDove = 2 := by
  rw [purePayoff_eq, pureDove_0, pureDove_1]; norm_num [hawkDove]

/-- **Off-axis pure payoff `u(Dove, Hawk) = 0` (transpose guard).** A transpose would read
`u(Hawk, Dove) = 2`, so together with `purePayoff_hawk_vs_dove` this distinguishes the two
off-diagonal entries. -/
theorem purePayoff_dove_vs_hawk : hawkDove.purePayoff 1 pureHawk = 0 := by
  rw [purePayoff_eq, pureHawk_0, pureHawk_1]; norm_num [hawkDove]

/-- **Pure Hawk is *not* a symmetric Nash.** Against a Hawk opponent, deviating to Dove pays
`u(Dove, Hawk) = 0`, strictly above the Hawk self-payoff `u(Hawk, Hawk) = −1`. The strict gap
`0 > −1` is exactly the direction that a reversed best-response inequality would flip. -/
theorem pureHawk_not_symmetricNash : ¬ hawkDove.IsSymmetricNash pureHawk := by
  rw [hawkDove.IsSymmetricNash_iff]
  intro h
  -- The Dove deviation gives `E[Dove, Hawk] = 0 > −1 = E[Hawk, Hawk]`, contradicting `≥`.
  have hbad := h pureDove
  rw [expectedPayoff_poly, expectedPayoff_poly] at hbad
  rw [pureHawk_0, pureHawk_1, pureDove_0, pureDove_1] at hbad
  norm_num at hbad

/-- **Pure Dove is *not* a symmetric Nash.** Against a Dove opponent, deviating to Hawk pays
`u(Hawk, Dove) = 2`, strictly above the Dove self-payoff `u(Dove, Dove) = 1`. -/
theorem pureDove_not_symmetricNash : ¬ hawkDove.IsSymmetricNash pureDove := by
  rw [hawkDove.IsSymmetricNash_iff]
  intro h
  -- The Hawk deviation gives `E[Hawk, Dove] = 2 > 1 = E[Dove, Dove]`, contradicting `≥`.
  have hbad := h pureHawk
  rw [expectedPayoff_poly, expectedPayoff_poly] at hbad
  rw [pureHawk_0, pureHawk_1, pureDove_0, pureDove_1] at hbad
  norm_num at hbad

/-- The ESS strict-gap identity `E[x, y] − E[y, y] = 2·(y₀ − 1/2)²`, where `x = (1/2,1/2)`. This is
the *engine* of evolutionary stability: Nonnegative always, and strictly positive iff `y ≠ x`. -/
theorem half_ess_gap (y : hawkDove.MixedStrategy) :
    hawkDove.expectedPayoff half y - hawkDove.expectedPayoff y y
      = 2 * ((y : Fin 2 → ℝ) 0 - 1 / 2) ^ 2 := by
  rw [expectedPayoff_poly, expectedPayoff_poly]
  have hy : (y : Fin 2 → ℝ) 0 + (y : Fin 2 → ℝ) 1 = 1 := by
    have := y.2.2; rwa [Fin.sum_univ_two] at this
  have h0 : (half : Fin 2 → ℝ) 0 = 1 / 2 := rfl
  have h1 : (half : Fin 2 → ℝ) 1 = 1 / 2 := rfl
  rw [h0, h1]
  nlinarith [hy]

/-- **`(1/2,1/2)` is an ESS.** Every mutant `y ≠ x` is strictly worse against itself than `x` is
against it — the strict gap `2·(y₀ − 1/2)² > 0` whenever `y ≠ x`. -/
theorem half_isESS : hawkDove.IsESS half := by
  refine ⟨half_isSymmetricNash, ?_⟩
  intro y hy_ne _hindiff
  -- The strict gap is positive because `y ≠ half` forces `y₀ ≠ 1/2`.
  have hy0_ne : (y : Fin 2 → ℝ) 0 ≠ 1 / 2 := by
    intro h
    apply hy_ne
    have hsum : (y : Fin 2 → ℝ) 0 + (y : Fin 2 → ℝ) 1 = 1 := by
      have := y.2.2; rwa [Fin.sum_univ_two] at this
    apply Subtype.ext
    funext a
    -- Both coordinates of `y` equal `1/2`: coordinate `0` by `h`, coordinate `1` by `hsum`.
    have h0 : (half : Fin 2 → ℝ) 0 = 1 / 2 := rfl
    have h1 : (half : Fin 2 → ℝ) 1 = 1 / 2 := rfl
    fin_cases a
    · change (y : Fin 2 → ℝ) 0 = (half : Fin 2 → ℝ) 0; rw [h, h0]
    · change (y : Fin 2 → ℝ) 1 = (half : Fin 2 → ℝ) 1; rw [h1]; linarith
  have hgap : hawkDove.expectedPayoff half y - hawkDove.expectedPayoff y y > 0 := by
    rw [half_ess_gap]
    have : 0 < ((y : Fin 2 → ℝ) 0 - 1 / 2) ^ 2 :=
      pow_two_pos_of_ne_zero (sub_ne_zero.mpr hy0_ne)
    linarith
  linarith

/-- `IsESS.is_symmetricNash`: The ESS is a symmetric Nash equilibrium (the refinement is not
vacuously broader). -/
theorem half_ess_is_symmetricNash : hawkDove.IsSymmetricNash half :=
  half_isESS.is_symmetricNash

/-- `IsESS_iff`: The ESS matches the refinement predicate on `essPred` at the diagonal. -/
theorem hd_IsESS_iff (x : hawkDove.MixedStrategy) :
    hawkDove.IsESS x ↔ hawkDove.essPred.IsRefinedEquilibrium (x, x) :=
  hawkDove.IsESS_iff x

/-- The half state, via the forward direction of `IsESS_iff`, *is* a refined equilibrium of
`essPred`. (This specializes the library iff in the `mp` direction; the reverse direction is
re-exported by the library theorem.) -/
theorem half_refined : hawkDove.essPred.IsRefinedEquilibrium (half, half) :=
  (hd_IsESS_iff half).mp half_isESS

/-! ## Replicator and the diagonal bridge -/

/-- `sum_replicator_eq_zero`: The replicator field has zero total mass at the half state (it is a
*flow on the simplex*, conserving total probability). *Sign caveat:* total-mass conservation is
sign-insensitive — a reversed replicator sign still sums to zero — so the dynamic *direction* is
checked separately by the component-sign witnesses `replicator_hawk_pos` / `replicator_dove_neg`
below at an off-equilibrium state. -/
theorem hd_sum_replicator_zero : ∑ a, hawkDove.replicator half a = 0 :=
  hawkDove.sum_replicator_eq_zero half

/-- The off-equilibrium interior population state `(1/4, 3/4)`, Hawk-deficient relative to the ESS
`(1/2, 1/2)`. -/
def quarter : hawkDove.MixedStrategy :=
  ⟨fun a => if a = 0 then 1/4 else 3/4, by
    refine ⟨fun a => by fin_cases a <;> norm_num, ?_⟩
    change ∑ a : Fin 2, (if a = 0 then (1:ℝ)/4 else 3/4) = 1
    rw [Fin.sum_univ_two]; norm_num⟩

@[simp] theorem quarter_0 : (quarter : Fin 2 → ℝ) 0 = 1/4 := rfl
@[simp] theorem quarter_1 : (quarter : Fin 2 → ℝ) 1 = 3/4 := rfl

/-- **Replicator Hawk component is strictly positive at `(1/4, 3/4)`** — Hawk grows. Hand
computation: `u(Hawk, x) = 2 − 3·(1/4) = 5/4`, `E[x, x] = 7/8`, so
`replicator Hawk = (1/4)·(5/4 − 7/8) = 3/32 > 0`. A reversed replicator sign would make this
negative; this is the dynamic-direction guard. -/
theorem replicator_hawk_pos : hawkDove.replicator quarter 0 > 0 := by
  unfold SymmetricGame.replicator
  rw [purePayoff_eq, expectedPayoff_poly]
  show (quarter : Fin 2 → ℝ) 0 * _ > 0
  rw [quarter_0, quarter_1]; norm_num [hawkDove]

/-- **Replicator Dove component is strictly negative at `(1/4, 3/4)`** — Dove shrinks. Hand
computation: `u(Dove, x) = 1 − 1/4 = 3/4`, `E[x, x] = 7/8`, so
`replicator Dove = (3/4)·(3/4 − 7/8) = −3/32 < 0`. With `replicator_hawk_pos` this pins the
direction of evolutionary flow toward the interior ESS. -/
theorem replicator_dove_neg : hawkDove.replicator quarter 1 < 0 := by
  unfold SymmetricGame.replicator
  rw [purePayoff_eq, expectedPayoff_poly]
  show (quarter : Fin 2 → ℝ) 1 * _ < 0
  rw [quarter_0, quarter_1]; norm_num [hawkDove]

/-- `isSymmetricNash_iff_diagonal_isMixedNash`: `x` is a symmetric Nash of `G` iff the constant
profile `fun _ => x` is a mixed Nash of the 2-player asymmetrization. For the half ESS this gives a
genuine mixed Nash of `hawkDove.toTwoPlayerGame`. -/
theorem hd_isSymmetricNash_iff_diagonal (x : hawkDove.MixedStrategy) :
    hawkDove.IsSymmetricNash x ↔ hawkDove.toTwoPlayerGame.IsMixedNash (fun _ => x) :=
  SymmetricGame.isSymmetricNash_iff_diagonal_isMixedNash hawkDove x

/-- The diagonal half profile is a mixed Nash of the two-player asymmetrization (forward direction
of `isSymmetricNash_iff_diagonal_isMixedNash`, specialized to the hand-solved half equilibrium). -/
theorem half_diagonal_isMixedNash :
    hawkDove.toTwoPlayerGame.IsMixedNash (fun _ => half) :=
  (hd_isSymmetricNash_iff_diagonal half).mp half_isSymmetricNash

/-- `exists_symmetricNash`: Hawk–Dove admits a symmetric Nash equilibrium, *witnessed concretely* by
the half ESS — so the existence claim is non-vacuously tied to the hand-solved equilibrium, not to
the abstract existence theorem. -/
theorem hd_exists_symmetricNash :
    ∃ x : hawkDove.MixedStrategy, hawkDove.IsSymmetricNash x :=
  ⟨half, half_isSymmetricNash⟩

end EconlibTest.GameTheory.StrategicSymmetric

end
