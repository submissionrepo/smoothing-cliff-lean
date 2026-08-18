/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.MajorityGame
import EconlibExamples.GameTheory.PrisonersDilemma
import Mathlib

/-!
# Cooperative TU-Game Non-Vacuity Checks

Compile-time semantic witnesses for the transferable-utility cooperative layer under
`Econlib.GameTheory.Cooperative` (the `Game`, `Core`, `Operations`, `Mobius`, `Shapley`,
`ValueRule`, `Balancedness`, `BalancedCore`, `StrategicBridge`, and `StrongEquilibrium` modules).
Cooperative-game facts are prone to silent *direction* errors — a balancedness sense reversal, a
coalition subset/superset swap in the unanimity basis, or a vacuously-satisfied convexity
hypothesis — so the witnesses fix concrete hand-computed games and check the intended direction.

Two carriers, both on `Fin 3`:

* `convex3` — the supermodular game `v(S) = |S|²`, with `v(∅) = 0`, `v(singleton) = 1`,
  `v(pair) = 4`, `v(univ) = 9`. It is *convex* (the binding coalition pair `{0,1}, {1,2}` gives
  `4 + 4 ≤ 9 + 1`), its Shapley value is `(3, 3, 3)` by symmetry, and `(3, 3, 3)` lies in its
  *nonempty* core (so the game is balanced).
* `majority3` — the simple majority game `v(S) = 1` iff `|S| ≥ 2` (imported from
  `EconlibExamples`). Its core is *empty* (the three two-player demands sum to `3 > 2`), so by the
  Bondareva–Shapley iff it is *not* balanced — the negative side of the balancedness witness.

For the strategic bridge we reuse `prisonersDilemma` (the α/β minimax theorem holds for every game)
and exhibit a concrete TU strong equilibrium on the *constant* game `payoff ≡ 1`, whose α-derived
TU game assigns `v(S) = |S|` and whose strong-equilibrium payoff vector lies in that core.

The failure modes these catch:

* **balancedness-direction reversal** — `convex3` is balanced *because* its core is nonempty, while
  `majority3` is *not* balanced *because* its core is empty; a flipped Bondareva–Shapley iff would
  classify them backwards;
* **coalition subset/superset swap** — the unanimity game `unanimity T` pays `1` only to coalitions
  *containing* `T` (`smul_unanimity_value_of_subset` vs. `_not_subset`), and the empty unanimity
  game pays `0` everywhere; a superset/subset swap would invert these;
* **vacuous convexity** — the convexity hypothesis of `shapleyValue_mem_core_of_convex` is
  discharged *concretely* (supermodularity hand-checked on the binding pair), not assumed, so the
  core-membership conclusion is non-vacuous;
* **Shapley axiom non-vacuity** — `shapleyValue_unique` is applied to an *arbitrary*
  axiom-satisfying
  rule `φ` (not the Shapley rule itself), forcing `φ convex3 i = 3` at every player; the four axioms
  are then discharged via Shapley (`shapley_satisfiesShapleyAxioms`), so the uniqueness
  characterization bites on a concrete convex game with a concrete numeric value.
-/

noncomputable section

namespace EconlibTest.GameTheory.Cooperative

open Econlib.GameTheory
open EconlibExamples.GameTheory.MajorityGame (majority3 majority3_core_empty)
open EconlibExamples.GameTheory.PrisonersDilemma (prisonersDilemma p0 p1)

/-! ## Carrier games -/

/-- **The convex carrier.** `v(S) = |S|²` on `Fin 3`. Supermodular, with Shapley value `(3,3,3)`
and a nonempty core containing `(3,3,3)`. -/
private def convex3 : TUGameOn (Fin 3) where
  value S := (S.card : ℝ) ^ 2
  value_empty := by simp

/-- The value of `convex3` is the squared cardinality, by definition. -/
private lemma convex3_value (S : Finset (Fin 3)) : convex3.value S = (S.card : ℝ) ^ 2 := rfl

/-- `v(univ) = 9` — the grand coalition is worth `3² = 9`. -/
private lemma convex3_value_univ : convex3.value (Finset.univ : Finset (Fin 3)) = 9 := by
  rw [convex3_value]; simp; norm_num

/-! ## Section 1 — Convexity, Shapley value, core membership

The Shapley value of `convex3` is `(3, 3, 3)`: Marginal contributions depend only on the
cardinality of the coalition joined (so symmetry forces equal shares) and efficiency forces them to
sum to `v(univ) = 9`. Convexity is supermodularity, hand-checked on the binding pair below; the
random-order theorem then places the Shapley value inside the core. -/

/-- **Convexity (supermodularity), discharged concretely.** `v(S) + v(T) ≤ v(S∪T) + v(S∩T)` follows
from `|S∪T| + |S∩T| = |S| + |T|` (cardinality inclusion–exclusion) and the discrete convexity
identity `m² + M² - p² - q² = 2(p - m)(q - m) ≥ 0` for `m = |S∩T| ≤ p, q ≤ M = |S∪T|`. This is the
non-vacuity of the convexity hypothesis fed to `shapleyValue_mem_core_of_convex`. -/
private theorem convex3_isConvex : convex3.IsConvex := by
  intro S T
  change (S.card : ℝ) ^ 2 + (T.card : ℝ) ^ 2 ≤ ((S ∪ T).card : ℝ) ^ 2 + ((S ∩ T).card : ℝ) ^ 2
  have hcard : ((S ∪ T).card : ℝ) + ((S ∩ T).card : ℝ) = (S.card : ℝ) + (T.card : ℝ) := by
    exact_mod_cast Finset.card_union_add_card_inter S T
  have hmS : ((S ∩ T).card : ℝ) ≤ (S.card : ℝ) :=
    by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hmT : ((S ∩ T).card : ℝ) ≤ (T.card : ℝ) :=
    by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  nlinarith [mul_nonneg (sub_nonneg.mpr hmS) (sub_nonneg.mpr hmT)]

/-- **The binding supermodular inequality, made explicit.** For the overlapping pairs `{0,1}` and
`{1,2}`, `v({0,1}) + v({1,2}) = 8 < 10 = v(univ) + v({1})`. A *strict* gap here certifies the game
is genuinely convex, not flat. -/
private theorem convex3_binding_pair :
    convex3.value {0, 1} + convex3.value {1, 2}
      < convex3.value ({0, 1} ∪ {1, 2}) + convex3.value ({0, 1} ∩ {1, 2}) := by
  rw [show ({0, 1} ∪ {1, 2} : Finset (Fin 3)) = Finset.univ from by decide,
    show ({0, 1} ∩ {1, 2} : Finset (Fin 3)) = {1} from by decide]
  simp only [convex3_value]
  rw [show ({0, 1} : Finset (Fin 3)).card = 2 from by decide,
    show ({1, 2} : Finset (Fin 3)).card = 2 from by decide,
    show ({1} : Finset (Fin 3)).card = 1 from by decide,
    show (Finset.univ : Finset (Fin 3)).card = 3 from by decide]
  norm_num

/-- **Marginal-contribution symmetry.** Adding `i` or `j` to a coalition containing neither raises
the cardinality by exactly one, so the marginal contributions agree. This is the hypothesis the
Shapley symmetry axiom consumes. -/
private theorem convex3_marginal_eq (i j : Fin 3) (S : Finset (Fin 3))
    (hiS : i ∉ S) (hjS : j ∉ S) :
    convex3.marginalContribution i S = convex3.marginalContribution j S := by
  unfold TUGameOn.marginalContribution
  have hi : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hiS
  have hj : (insert j S).card = S.card + 1 := Finset.card_insert_of_notMem hjS
  change ((insert i S).card : ℝ) ^ 2 - (S.card : ℝ) ^ 2
      = ((insert j S).card : ℝ) ^ 2 - (S.card : ℝ) ^ 2
  rw [hi, hj]

/-- All three Shapley values of `convex3` coincide (symmetry of the marginal contributions). -/
private theorem convex3_shapleyValue_eq (i j : Fin 3) :
    convex3.shapleyValue i = convex3.shapleyValue j :=
  ValueRule.shapley_satisfiesSymmetry.apply convex3
    (fun S _ _ => convex3_marginal_eq i j S ‹_› ‹_›)

/-- **Shapley value `= 3`.** By symmetry the three values are equal; by efficiency they sum to
`v(univ) = 9`; hence each is `3`. -/
private theorem convex3_shapleyValue (i : Fin 3) : convex3.shapleyValue i = 3 := by
  have hsym : ∀ k : Fin 3, convex3.shapleyValue k = convex3.shapleyValue 0 :=
    fun k => convex3_shapleyValue_eq k 0
  have heff : ∑ k : Fin 3, convex3.shapleyValue k = 9 := by
    have hE := ValueRule.shapley_satisfiesEfficiency.apply convex3
    rw [convex3_value_univ] at hE
    exact hE
  rw [Fin.sum_univ_three, hsym 0, hsym 1, hsym 2] at heff
  rw [hsym i]; linarith

/-- **Shapley uniqueness, as a discriminating numeric consequence.** This is the non-vacuous bite of
`shapleyValue_unique`. Rather than applying uniqueness to the Shapley rule itself (which would be
the definitionally reflexive `shapley convex3 = shapley convex3`), we take an *arbitrary* value rule
`φ` with the four Shapley axioms as hypotheses and conclude that `φ` must assign the *concrete value
`3`* to every player of `convex3`. The conclusion is a numeric value forced on an abstract rule —
not a tautology — so a flaw in `shapleyValue_unique` (e.g. a wrong Harsanyi coefficient) would
surface here. The axioms are jointly satisfiable: Shapley itself witnesses them
(`convex3_shapley_forces_three`), so the guard is non-vacuous. -/
private theorem convex3_anyShapleyAxiomRule_eq_three
    (φ : ValueRule (Fin 3))
    (heff : ValueRule.SatisfiesEfficiency φ)
    (hsym : ValueRule.SatisfiesSymmetry φ)
    (hdummy : ValueRule.SatisfiesDummy φ)
    (hlin : ValueRule.SatisfiesLinearity φ)
    (i : Fin 3) :
    φ convex3 i = 3 := by
  have h := convex3.shapleyValue_unique φ heff hsym hdummy hlin
  rw [congrFun h i, convex3_shapleyValue i]

/-- **Non-vacuity of the axiom hypotheses.** The four Shapley axioms are jointly satisfiable —
the Shapley rule satisfies them (`shapley_satisfiesShapleyAxioms`) — so the uniqueness consequence
above is not vacuously true. Discharging the axioms via Shapley forces the concrete value `3` at
every player of `convex3`. -/
private theorem convex3_shapley_forces_three (i : Fin 3) :
    (ValueRule.shapley : ValueRule (Fin 3)) convex3 i = 3 := by
  obtain ⟨heff, hsym, hdummy, hlin⟩ :=
    (ValueRule.shapley_satisfiesShapleyAxioms :
      (ValueRule.shapley : ValueRule (Fin 3)).SatisfiesShapleyAxioms)
  exact convex3_anyShapleyAxiomRule_eq_three ValueRule.shapley heff hsym hdummy hlin i

/-- **The Shapley value lies in the core of the convex game.** The random-order theorem
(`shapleyValue_mem_core_of_convex`) places `convex3.shapleyValue = (3,3,3)` inside the core. The
convexity hypothesis is discharged by `convex3_isConvex` — *not* assumed — so this is the genuine
non-vacuous content. -/
private theorem convex3_shapley_mem_core : convex3.IsCore convex3.shapleyValue :=
  convex3.shapleyValue_mem_core_of_convex convex3_isConvex

/-! ## Section 2 — Core ⇔ balancedness (Bondareva–Shapley)

The convex game is balanced (nonempty core, witness `(3,3,3)`); the majority game is *not*
balanced (empty core). Routing each through `core_nonempty_iff_balanced` in opposite directions
catches a sense reversal in the Bondareva–Shapley iff. We also exercise the imputation predicate,
the efficiency reformulation, and the finite Farkas coalition-coding machinery underneath. -/

/-- **A concrete core allocation of `convex3`.** The equal split `(3,3,3)` is efficient
(`3+3+3 = 9 = v(univ)`) and coalitionally rational (`|S|² ≤ 3|S|` since `|S| ≤ 3`). -/
private theorem convex3_core_witness : convex3.IsCore (fun _ => 3) := by
  refine ⟨?_, ?_⟩
  · change convex3.coalitionPayoff (fun _ => 3) convex3.grandCoalition
        = convex3.value convex3.grandCoalition
    change ∑ _i : Fin 3, (3 : ℝ) = convex3.value Finset.univ
    rw [convex3_value_univ, Fin.sum_univ_three]; norm_num
  · intro S
    change ((S.card : ℝ)) ^ 2 ≤ ∑ _i ∈ S, (3 : ℝ)
    rw [Finset.sum_const, nsmul_eq_mul]
    have hle : (S.card : ℝ) ≤ 3 := by
      have hcard := Finset.card_le_univ S
      simp only [Fintype.card_fin] at hcard
      exact_mod_cast hcard
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card, hle]

/-- **Strict core slack at a singleton (direction guard).** The coalitional-rationality inequality
`v(S) ≤ ∑_{i∈S} xᵢ` holds *strictly* at the singleton `{0}`: `v({0}) = 1 < 3 = x₀`. A *reversed*
core inequality (`∑ xᵢ ≤ v(S)`) would force `3 ≤ 1` and fail here, so this anchor distinguishes the
direction — unlike the constant-game witnesses below, where every coalition inequality binds at
equality. -/
private theorem convex3_core_strict_singleton :
    convex3.value {(0 : Fin 3)} < ∑ i ∈ ({0} : Finset (Fin 3)), (fun _ : Fin 3 => (3:ℝ)) i := by
  rw [Finset.sum_singleton]
  change ((({0} : Finset (Fin 3)).card : ℝ)) ^ 2 < 3
  simp

/-- **`(3,3,3)` is an imputation.** Efficient and individually rational (`v({i}) = 1 ≤ 3`). -/
private theorem convex3_imputation : convex3.IsImputation (fun _ => 3) := by
  refine ⟨convex3_core_witness.1, ?_⟩
  intro i
  change convex3.value {i} ≤ 3
  change ((({i} : Finset (Fin 3)).card : ℝ)) ^ 2 ≤ 3
  simp

/-- **Efficiency reformulation.** `IsEfficient x ↔ ∑ xᵢ = v(univ)` on `convex3`. -/
private theorem convex3_isEfficient_iff (x : convex3.PayoffVector) :
    convex3.IsEfficient x ↔ ∑ i : Fin 3, x i = convex3.value Finset.univ :=
  convex3.isEfficient_iff_sum_univ x

/-- **Forward direction (balanced because nonempty core).** Since `convex3` has the core allocation
`(3,3,3)`, the Bondareva–Shapley iff yields balancedness. -/
private theorem convex3_balanced : convex3.SatisfiesBalancedness :=
  (convex3.core_nonempty_iff_balanced).mp ⟨_, convex3_core_witness⟩

/-- **Converse direction (not balanced because empty core).** The majority game has *no* core
allocation (`majority3_core_empty`), so by the Bondareva–Shapley iff it fails balancedness. A
*reversed* iff would wrongly certify it balanced — this is the direction guard. -/
private theorem majority3_not_balanced : ¬ majority3.SatisfiesBalancedness := by
  intro hbal
  exact majority3_core_empty ((majority3.core_nonempty_iff_balanced).mpr hbal)

/-! ### Finite Farkas coalition-coding machinery

The Bondareva–Shapley proof routes through a finite linear program whose coalitions are encoded
as naturals. These witnesses exercise the coding interface directly; the deep LP internals
(`coreFeasible_iff_satisfiesBalancedInequalities`, the Farkas cone construction) are exercised
*transitively* by `convex3_balanced` / `majority3_not_balanced` above. -/

/-- `coalitionCode` is injective on `Fin 3` coalitions. -/
private theorem coalitionCode_inj : Function.Injective (coalitionCode (α := Fin 3)) :=
  coalitionCode_injective

/-- `coalitionDecode` inverts `coalitionCode`. -/
private theorem coalitionDecode_roundtrip (S : Finset (Fin 3)) :
    coalitionDecode (α := Fin 3) (coalitionCode S) = S :=
  coalitionDecode_code S

/-- The signed coalition-indicator collapses to the coalition sum. -/
private theorem coalition_indicator_neg (S : Finset (Fin 3)) (x : Fin 3 → ℝ) :
    (∑ i : Fin 3, (if i ∈ S then (-1 : ℝ) else 0) * x i) = -∑ i ∈ S, x i :=
  sum_coalition_indicator_neg S x

/-- The grand-coalition inner-product identity used in the Farkas encoding. -/
private theorem augVector_grand
    (r : ℝ) (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ Fin 3)))) :
    inner ℝ (augVector (α := Fin 3) r (fun _ => -1)) z
      = r * augScalar z - ∑ i : Fin 3, augPlayer z i :=
  inner_augVector_grand r z

/-- The per-coalition inner-product identity used in the Farkas encoding. -/
private theorem augVector_coalition (S : Finset (Fin 3))
    (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ Fin 3)))) :
    inner ℝ (augVector (α := Fin 3) (convex3.value S)
        (fun i => if i ∈ S then (-1 : ℝ) else 0)) z
      = convex3.value S * augScalar z - ∑ i ∈ S, augPlayer z i :=
  inner_augVector_coalition convex3.value S z

/-- Core feasibility is membership of the target vector in the slack-cone image. -/
private theorem coreFeasible_iff_target_mem :
    CoalitionCoreFeasible convex3.value ↔
      coreTarget convex3.value ∈
        (coreSlackCone (α := Fin 3)).toPointedCone.map
          (coreFeasibilityMap (α := Fin 3)).toLinearMap :=
  coalitionCoreFeasible_iff_coreTarget_mem convex3.value

/-! ## Section 3 — Value algebra and the unanimity / Harsanyi basis

Pointwise vector-space operations on TU games, the unanimity basis, and the Möbius (Harsanyi)
expansion. The unanimity witnesses catch a coalition subset/superset swap; the dividend anchor
(`convex3.harsanyiDividend {0} = 1`) catches a Möbius-sign error. -/

/-- A second concrete game to pair with `convex3` in the value algebra. -/
private def linear3 : TUGameOn (Fin 3) where
  value S := (S.card : ℝ)
  value_empty := by simp

/-- **Value of a sum is the sum of values.** `(convex3 + linear3)(S) = convex3(S) + linear3(S)`. -/
private theorem add_value_witness (S : Finset (Fin 3)) :
    (convex3.add linear3).value S = convex3.value S + linear3.value S :=
  TUGameOn.add_value convex3 linear3 S

/-- **Numeric anchor for `add_value`.** At the grand coalition: `9 + 3 = 12`. -/
private theorem add_value_univ :
    (convex3.add linear3).value Finset.univ = 12 := by
  rw [add_value_witness, convex3_value_univ]
  change (9 : ℝ) + ((Finset.univ : Finset (Fin 3)).card : ℝ) = 12
  simp; norm_num

/-- **Value of a scalar multiple.** `(2 • convex3)(S) = 2 · convex3(S)`. -/
private theorem smul_value_witness (S : Finset (Fin 3)) :
    (TUGameOn.smul 2 convex3).value S = 2 * convex3.value S :=
  TUGameOn.smul_value 2 convex3 S

/-- **The zero game.** `0(S) = 0`. -/
private theorem zero_value_witness (S : Finset (Fin 3)) :
    (TUGameOn.zero : TUGameOn (Fin 3)).value S = 0 :=
  TUGameOn.zero_value S

/-- **Value of a finite sum of games.** -/
private theorem sum_value_witness (S : Finset (Fin 3)) :
    (TUGameOn.sum (Finset.univ : Finset (Fin 2)) (fun _ => convex3)).value S
      = ∑ _k : Fin 2, convex3.value S :=
  TUGameOn.sum_value _ _ S

/-- `G + 0 = G`. -/
private theorem add_zero_witness : convex3.add TUGameOn.zero = convex3 :=
  TUGameOn.add_zero convex3

/-- `0 + G = G`. -/
private theorem zero_add_witness : (TUGameOn.zero : TUGameOn (Fin 3)).add convex3 = convex3 :=
  TUGameOn.zero_add convex3

/-- The empty sum is the zero game. -/
private theorem sum_empty_witness :
    TUGameOn.sum (∅ : Finset (Fin 2)) (fun _ => convex3) = TUGameOn.zero :=
  TUGameOn.sum_empty _

/-- **The empty unanimity game vanishes everywhere.** `unanimity ∅` is the zero game. -/
private theorem unanimity_empty_witness (S : Finset (Fin 3)) :
    (TUGameOn.unanimity (∅ : Finset (Fin 3))).value S = 0 :=
  TUGameOn.unanimity_value_of_not_nonempty (by simp)

/-- **Subset direction.** `unanimity {0,1}` (scaled by `5`) pays `5` to any coalition *containing*
`{0,1}` — e.g. the grand coalition. The subset hypothesis `{0,1} ⊆ S` is the load-bearing
direction; a superset swap would invert it. -/
private theorem smul_unanimity_subset_witness :
    (TUGameOn.smul 5 (TUGameOn.unanimity ({0, 1} : Finset (Fin 3)))).value Finset.univ = 5 :=
  TUGameOn.smul_unanimity_value_of_subset 5 (by decide) (by decide)

/-- **Not-subset direction (negative check).** `unanimity {0,1}` pays `0` to a coalition that does
*not* contain `{0,1}` — e.g. the singleton `{0}` (missing player `1`). -/
private theorem smul_unanimity_not_subset_witness :
    (TUGameOn.smul 5 (TUGameOn.unanimity ({0, 1} : Finset (Fin 3)))).value {0} = 0 :=
  TUGameOn.smul_unanimity_value_of_not_subset 5 (by decide)

/-- The Harsanyi dividend of the empty coalition vanishes. -/
private theorem harsanyiDividend_empty_witness : convex3.harsanyiDividend ∅ = 0 :=
  convex3.harsanyiDividend_empty

/-- **Harsanyi dividend anchor.** `δ_{0}(convex3) = 1`. Via Möbius inversion
(`sum_harsanyiDividend_eq_value` over the powerset `{∅, {0}}`), `δ_∅ + δ_{0} = v({0}) = 1` and
`δ_∅ = 0`, so `δ_{0} = 1`. This is the unanimity-basis coordinate of `convex3` at player `0`; a
Möbius-sign error would flip its sign. -/
private theorem convex3_harsanyiDividend_singleton : convex3.harsanyiDividend {0} = 1 := by
  have hsum := convex3.sum_harsanyiDividend_eq_value {(0 : Fin 3)}
  rw [show convex3.value {(0 : Fin 3)} = 1 from by
        change ((({0} : Finset (Fin 3)).card : ℝ)) ^ 2 = 1; simp] at hsum
  rw [show ({(0 : Fin 3)} : Finset (Fin 3)).powerset = {∅, {0}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, convex3.harsanyiDividend_empty,
    zero_add] at hsum
  exact hsum

/-- **Harsanyi (Möbius) expansion in unanimity-game form.** -/
private theorem harsanyiExpansion_value_witness (S : Finset (Fin 3)) :
    convex3.harsanyiExpansion.value S =
      ∑ T ∈ (Finset.univ : Finset (Fin 3)).powerset,
        convex3.harsanyiDividend T * (TUGameOn.unanimity T).value S :=
  convex3.harsanyiExpansion_value S

/-- **Harsanyi expansion in subset-sum form.** `(harsanyiExpansion G)(S) = ∑_{T ⊆ S} δ_T`. -/
private theorem harsanyiExpansion_eq_sum_subset_witness (S : Finset (Fin 3)) :
    convex3.harsanyiExpansion.value S = ∑ T ∈ S.powerset, convex3.harsanyiDividend T :=
  convex3.harsanyiExpansion_value_eq_sum_subset S

/-- **Game extensionality.** Two games with equal characteristic functions are equal. -/
private theorem ext_witness (G H : TUGameOn (Fin 3)) (h : ∀ S, G.value S = H.value S) : G = H :=
  TUGameOn.ext h

/-! ## Section 4 — Strategic bridge and strong equilibrium

The α/β-characteristic-function bridge and the strong-equilibrium ⇒ core implication. The
headline minimax equality `alphaChar_eq_betaChar` is exercised on the non-trivial coalition `{p0}`
of the prisoner's dilemma, with the shared minimax value *pinned to `1`* by the direct computations
`pd_alphaChar_singleton` and `pd_betaChar_singleton` (so an α/β swap is detectable);
`isTUStrongEquilibrium_implies_isCore` is instantiated on the *constant* game `payoff ≡ 1`, whose
α-derived TU game assigns `v(S) = |S|`. -/

/-! ### Numeric anchors for the PD singleton minimax value

The headline equality `alphaChar = betaChar` is symmetric and holds for *every* game, so on its own
it would survive an α/β swap. We pin the actual value `alphaChar {p0} = betaChar {p0} = 1` by a
direct minimax computation, which *is* direction-sensitive: it forces the
worst-case-against-defection payoff. Hand computation: for the singleton coalition `{p0}`, write
the coalition mixing weight on
*defect* as `s₁` and the complement weight on *defect* as `c₁`. The bilinear coalitional payoff is
`E = 3·s₀c₀ + 5·s₁c₀ + 1·s₁c₁` (the PD column for player `0`: `R=3` at `(C,C)`, `S=0` at `(C,D)`,
`T=5` at `(D,C)`, `P=1` at `(D,D)`). With `s₀+s₁=1`, `c₀+c₁=1` this is `E = s₁` at the
complement's worst response `c₁=1` (defect dominates the complement's punishment), so the inner inf
is `s₁`, maximized at `s₁=1` giving `alphaChar = 1`. Dually the inner sup is `5−4c₁`, minimized at
`c₁=1` giving `betaChar = 1`. -/

/-- The coalition-member subtype element for `{p0}` (player `0` inside the coalition). -/
private def pdCoalMem : {x : prisonersDilemma.Player // x ∈ ({p0} : Finset _)} := ⟨p0, by decide⟩

/-- The complement-member subtype element for `{p0}` (player `1`, outside the coalition). -/
private def pdCompMem : {x : prisonersDilemma.Player // x ∉ ({p0} : Finset _)} := ⟨p1, by decide⟩

/-- The coalition `{p0}` is a singleton, so its action profiles are determined by the single
member's choice: the action type is `Unique`-equivalent to `Fin 2`. -/
private instance pdCoalUnique :
    Unique {x : prisonersDilemma.Player // x ∈ ({p0} : Finset _)} where
  default := pdCoalMem
  uniq i := by
    apply Subtype.ext; have h := i.2; simp only [Finset.mem_singleton] at h; rw [h]; rfl

/-- The complement of `{p0}` is the singleton `{p1}`, so complement profiles are determined by
player `1`'s choice. -/
private instance pdCompUnique :
    Unique {x : prisonersDilemma.Player // x ∉ ({p0} : Finset _)} where
  default := pdCompMem
  uniq i := by
    apply Subtype.ext; have h := i.2; simp only [Finset.mem_singleton] at h
    have : (i : prisonersDilemma.Player) = 1 := by
      revert h; generalize (i : prisonersDilemma.Player) = v; revert v; decide
    rw [this]; rfl

/-- A sum over coalition action profiles splits into the cooperate (`0`) and defect (`1`)
profiles. -/
private lemma pd_sum_coal (g : prisonersDilemma.CoalitionAction {p0} → ℝ) :
    ∑ aS, g aS = g (fun _ => 0) + g (fun _ => 1) := by
  rw [← Equiv.sum_comp (Equiv.funUnique _ (Fin 2)).symm g, Fin.sum_univ_two]; rfl

/-- A sum over complement action profiles splits into the cooperate (`0`) and defect (`1`)
profiles. -/
private lemma pd_sum_comp (g : prisonersDilemma.ComplementAction {p0} → ℝ) :
    ∑ aC, g aC = g (fun _ => 0) + g (fun _ => 1) := by
  rw [← Equiv.sum_comp (Equiv.funUnique _ (Fin 2)).symm g, Fin.sum_univ_two]; rfl

/-- **Closed form of the coalition total payoff.** For coalition `{p0}`, the total is player `0`'s
payoff at the glued profile, read off the PD column. -/
private lemma pd_coalTotal (aS : prisonersDilemma.CoalitionAction {p0})
    (aC : prisonersDilemma.ComplementAction {p0}) :
    prisonersDilemma.coalitionTotalPayoff {p0} aS aC =
      (if aS pdCoalMem = 0 then (if aC pdCompMem = 0 then 3 else 0)
       else (if aC pdCompMem = 0 then 5 else 1)) := by
  unfold FiniteStrategicGame.coalitionTotalPayoff
  rw [Finset.sum_singleton]
  show prisonersDilemma.payoff p0 (prisonersDilemma.combine {p0} aS aC) = _
  have h0 : prisonersDilemma.combine {p0} aS aC p0 = aS pdCoalMem := by
    unfold FiniteStrategicGame.combine; simp [pdCoalMem]
  have h1 : prisonersDilemma.combine {p0} aS aC (1 - p0) = aC pdCompMem := by
    unfold FiniteStrategicGame.combine
    rw [show (1 - p0 : prisonersDilemma.Player) = p1 from by decide]
    rw [dif_neg (by decide)]; rfl
  change (if prisonersDilemma.combine {p0} aS aC p0 = 0 then
         (if prisonersDilemma.combine {p0} aS aC (1 - p0) = 0 then (3:ℝ) else 0)
       else
         (if prisonersDilemma.combine {p0} aS aC (1 - p0) = 0 then 5 else 1)) = _
  rw [h0, h1]

/-- **Bilinear closed form of the coalitional expected payoff** in the four mixing weights. -/
private lemma pd_expPay (σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}))
    (σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) :
    prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C
      = (σ_S : _ → ℝ) (fun _ => 0)
          * ((σ_C : _ → ℝ) (fun _ => 0) * 3 + (σ_C : _ → ℝ) (fun _ => 1) * 0)
      + (σ_S : _ → ℝ) (fun _ => 1)
          * ((σ_C : _ → ℝ) (fun _ => 0) * 5 + (σ_C : _ → ℝ) (fun _ => 1) * 1) := by
  unfold FiniteStrategicGame.coalitionExpectedPayoff
  rw [pd_sum_coal (fun aS => ∑ aC, (σ_S : _ → ℝ) aS * (σ_C : _ → ℝ) aC
      * prisonersDilemma.coalitionTotalPayoff {p0} aS aC)]
  rw [pd_sum_comp, pd_sum_comp]
  rw [pd_coalTotal (fun _ => 0) (fun _ => 0), pd_coalTotal (fun _ => 0) (fun _ => 1),
      pd_coalTotal (fun _ => 1) (fun _ => 0), pd_coalTotal (fun _ => 1) (fun _ => 1)]
  norm_num [pdCoalMem, pdCompMem]
  ring

/-- **Inner infimum (the value player `0` guarantees from a fixed mix `σ_S`).** Equals the defect
weight `s₁ = σ_S(defect)`: the complement's worst response is to defect (`c₁=1`), holding player `0`
to `s₁`. -/
private lemma pd_inner_inf_eq (σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0})) :
    sInf (Set.range (fun σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0}) =>
      prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C)) = (σ_S : _ → ℝ) (fun _ => 1) := by
  have hbdd := prisonersDilemma.coalitionExpectedPayoff_bddBelow_C {p0} σ_S
  apply le_antisymm
  · apply csInf_le hbdd
    refine ⟨stdSimplex.vertex (S := ℝ) (fun _ => (1 : Fin 2)), ?_⟩
    change prisonersDilemma.coalitionExpectedPayoff {p0} σ_S _ = _
    rw [pd_expPay]
    have hc1 : (stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)) :
        stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) (fun _ => 1) = 1 :=
      stdSimplex.vertex_apply_self _
    have hc0 : (stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)) :
        stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) (fun _ => 0) = 0 := by
      apply stdSimplex.vertex_apply_ne; intro h; exact absurd (congrFun h pdCompMem) (by decide)
    rw [hc1, hc0]; ring
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨σ_C, rfl⟩
    change (σ_S : _ → ℝ) (fun _ => 1) ≤ prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C
    rw [pd_expPay]
    have hs0 := stdSimplex.zero_le σ_S (fun _ => (0:Fin 2))
    have hs1 := stdSimplex.zero_le σ_S (fun _ => (1:Fin 2))
    have hc0 := stdSimplex.zero_le σ_C (fun _ => (0:Fin 2))
    have hc1 := stdSimplex.zero_le σ_C (fun _ => (1:Fin 2))
    have hcsum : (σ_C : _ → ℝ) (fun _ => 0) + (σ_C : _ → ℝ) (fun _ => 1) = 1 := by
      have := σ_C.2.2; rw [pd_sum_comp] at this; exact this
    nlinarith [mul_nonneg hs1 hc0, mul_nonneg hs0 hc0]

/-- **Inner supremum (the best the coalition can do against a fixed complement mix `σ_C`).** Equals
`5 − 4·c₁`: player `0`'s best response is pure defect, paying `5` against complement cooperation and
`1` against defection. -/
private lemma pd_inner_sup_eq (σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) :
    sSup (Set.range (fun σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}) =>
      prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C))
      = 5 - 4 * (σ_C : _ → ℝ) (fun _ => 1) := by
  have hbdd := prisonersDilemma.coalitionExpectedPayoff_bddAbove_S {p0} σ_C
  have hcsum : (σ_C : _ → ℝ) (fun _ => 0) + (σ_C : _ → ℝ) (fun _ => 1) = 1 := by
    have := σ_C.2.2; rw [pd_sum_comp] at this; exact this
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨σ_S, rfl⟩
    change prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C ≤ _
    rw [pd_expPay]
    have hs0 := stdSimplex.zero_le σ_S (fun _ => (0:Fin 2))
    have hs1 := stdSimplex.zero_le σ_S (fun _ => (1:Fin 2))
    have hc0 := stdSimplex.zero_le σ_C (fun _ => (0:Fin 2))
    have hc1 := stdSimplex.zero_le σ_C (fun _ => (1:Fin 2))
    have hssum : (σ_S : _ → ℝ) (fun _ => 0) + (σ_S : _ → ℝ) (fun _ => 1) = 1 := by
      have := σ_S.2.2; rw [pd_sum_coal] at this; exact this
    nlinarith [mul_nonneg hs0 hc0, mul_nonneg hs1 hc1, mul_nonneg hs0 hc1]
  · apply le_csSup hbdd
    refine ⟨stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)), ?_⟩
    change prisonersDilemma.coalitionExpectedPayoff {p0} _ σ_C = _
    rw [pd_expPay]
    have hs1 : (stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)) :
        stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0})) (fun _ => 1) = 1 :=
      stdSimplex.vertex_apply_self _
    have hs0 : (stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)) :
        stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0})) (fun _ => 0) = 0 := by
      apply stdSimplex.vertex_apply_ne; intro h; exact absurd (congrFun h pdCoalMem) (by decide)
    rw [hs1, hs0]; nlinarith [hcsum]

/-- **Numeric anchor (α).** `alphaChar {p0} = 1`: the maximin value player `0` can guarantee for the
singleton coalition is the punishment payoff `P = 1`. Direction-sensitive — a swap of α/β or a sign
error in the worst-case response would move this value. -/
private theorem pd_alphaChar_singleton : prisonersDilemma.alphaChar {p0} = 1 := by
  unfold FiniteStrategicGame.alphaChar
  have hset : (Set.range (fun σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}) =>
        sInf (Set.range (fun σ_C => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C))))
      = (Set.range (fun σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}) =>
        (σ_S : _ → ℝ) (fun _ => 1))) := by
    congr 1; funext σ_S; exact pd_inner_inf_eq σ_S
  rw [hset]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨σ_S, rfl⟩
    exact stdSimplex.le_one σ_S (fun _ => 1)
  · apply le_csSup
    · refine ⟨1, ?_⟩; rintro _ ⟨σ_S, rfl⟩; exact stdSimplex.le_one σ_S (fun _ => 1)
    · exact ⟨stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)), stdSimplex.vertex_apply_self _⟩

/-- **Numeric anchor (β).** `betaChar {p0} = 1`: the minimax value the complement can hold
player `0`
to is also `P = 1`. With `pd_alphaChar_singleton` this re-derives `α = β` *with the shared value
pinned to `1`*, so an α/β swap (or a wrong PD column) is now detectable. -/
private theorem pd_betaChar_singleton : prisonersDilemma.betaChar {p0} = 1 := by
  unfold FiniteStrategicGame.betaChar
  have hset : (Set.range (fun σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0}) =>
        sSup (Set.range (fun σ_S => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C))))
      = (Set.range (fun σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0}) =>
        5 - 4 * (σ_C : _ → ℝ) (fun _ => 1))) := by
    congr 1; funext σ_C; exact pd_inner_sup_eq σ_C
  rw [hset]
  apply le_antisymm
  · apply csInf_le
    · refine ⟨-3, ?_⟩; rintro _ ⟨σ_C, rfl⟩
      have hc1 := stdSimplex.le_one σ_C (fun _ => (1:Fin 2)); linarith
    · refine ⟨stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)), ?_⟩
      change (5:ℝ) - 4 * (stdSimplex.vertex (S := ℝ) (fun _ => (1:Fin 2)) :
          stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) (fun _ => 1) = 1
      rw [stdSimplex.vertex_apply_self]; ring
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨σ_C, rfl⟩
    have hc1 := stdSimplex.le_one σ_C (fun _ => (1:Fin 2)); linarith

/-- **Headline minimax equality (α = β), now anchored at the value `1`.** For the coalition `{p0}`
of the prisoner's dilemma, the value player `0` can guarantee equals the value the complement can
hold them to. The shared value is pinned to `1` by `pd_alphaChar_singleton` and
`pd_betaChar_singleton`, so this is no longer a symmetric tautology. Correlated mixing makes the
coalitional payoff bilinear, so Nash on the induced zero-sum game gives the saddle. -/
private theorem pd_alphaChar_eq_betaChar :
    prisonersDilemma.alphaChar {p0} = prisonersDilemma.betaChar {p0} :=
  prisonersDilemma.alphaChar_eq_betaChar {p0}

/-- Continuity of the coalitional expected payoff in the strategy pair. -/
private theorem pd_coalitionExpectedPayoff_continuous :
    Continuous (fun pr :
        stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}) ×
          stdSimplex ℝ (prisonersDilemma.ComplementAction {p0}) =>
      prisonersDilemma.coalitionExpectedPayoff {p0} pr.1 pr.2) :=
  prisonersDilemma.coalitionExpectedPayoff_continuous {p0}

/-- Bounded-above on the coalition-strategy slice (used for `betaChar`). -/
private theorem pd_bddAbove_S (σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) :
    BddAbove (Set.range (fun σ_S => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C)) :=
  prisonersDilemma.coalitionExpectedPayoff_bddAbove_S {p0} σ_C

/-- Bounded-below on the coalition-strategy slice. -/
private theorem pd_bddBelow_S (σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0})) :
    BddBelow (Set.range (fun σ_S => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C)) :=
  prisonersDilemma.coalitionExpectedPayoff_bddBelow_S {p0} σ_C

/-- The inner-inf set (whose sup is `alphaChar`) is bounded above. -/
private theorem pd_alphaChar_inner_bddAbove :
    BddAbove (Set.range (fun σ_S : stdSimplex ℝ (prisonersDilemma.CoalitionAction {p0}) =>
      sInf (Set.range (fun σ_C => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C)))) :=
  prisonersDilemma.alphaChar_inner_bddAbove {p0}

/-- The inner-sup set (whose inf is `betaChar`) is bounded below. -/
private theorem pd_betaChar_inner_bddBelow :
    BddBelow (Set.range (fun σ_C : stdSimplex ℝ (prisonersDilemma.ComplementAction {p0}) =>
      sSup (Set.range (fun σ_S => prisonersDilemma.coalitionExpectedPayoff {p0} σ_S σ_C)))) :=
  prisonersDilemma.betaChar_inner_bddBelow {p0}

/-- The induced zero-sum game's `expectedPayoff` for the coalition player (`false`) factors through
the coalitional expected payoff. -/
private theorem pd_inducedZeroSum_false (σ : (prisonersDilemma.inducedZeroSum {p0}).MixedStrategy) :
    (prisonersDilemma.inducedZeroSum {p0}).expectedPayoff false σ =
      prisonersDilemma.coalitionExpectedPayoff {p0} (σ false) (σ true) :=
  prisonersDilemma.inducedZeroSum_expectedPayoff_false {p0} σ

/-- The induced zero-sum game's `expectedPayoff` for the complement player (`true`) is the negation
(zero-sum). -/
private theorem pd_inducedZeroSum_true (σ : (prisonersDilemma.inducedZeroSum {p0}).MixedStrategy) :
    (prisonersDilemma.inducedZeroSum {p0}).expectedPayoff true σ =
      -prisonersDilemma.coalitionExpectedPayoff {p0} (σ false) (σ true) :=
  prisonersDilemma.inducedZeroSum_expectedPayoff_true {p0} σ

/-- The `InducedAction` `Fintype` instance resolves. -/
private instance pd_inducedAction_fintype (b : Bool) :
    Fintype (prisonersDilemma.inducedAction {p0} b) := inferInstance

/-- The `InducedAction` `DecidableEq` instance resolves. -/
private def pd_inducedAction_decEq (b : Bool) :
    DecidableEq (prisonersDilemma.inducedAction {p0} b) := inferInstance

/-- The `InducedAction` `Inhabited` instance resolves. -/
private instance pd_inducedAction_inhabited (b : Bool) :
    Inhabited (prisonersDilemma.inducedAction {p0} b) := inferInstance

/-! ### Strong equilibrium ⇒ core, on the constant game `payoff ≡ 1` -/

/-- **The constant carrier.** A 2-player game in which every player always earns `1`, regardless of
the profile. -/
private abbrev constGame : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 2) (fun _ _ => 1)

/-- The coalition total payoff in `constGame` is the constant `|S|`. -/
private lemma constGame_coalitionTotalPayoff (S : Finset constGame.Player)
    (aS : constGame.CoalitionAction S) (aC : constGame.ComplementAction S) :
    constGame.coalitionTotalPayoff S aS aC = (S.card : ℝ) := by
  unfold FiniteStrategicGame.coalitionTotalPayoff
  simp

/-- **The coalitional expected payoff is `|S|`** for any correlated strategy pair: Factor the
constant out and use that each simplex marginal sums to `1`. -/
private lemma constGame_coalitionExpectedPayoff (S : Finset constGame.Player)
    (σ_S : stdSimplex ℝ (constGame.CoalitionAction S))
    (σ_C : stdSimplex ℝ (constGame.ComplementAction S)) :
    constGame.coalitionExpectedPayoff S σ_S σ_C = (S.card : ℝ) := by
  unfold FiniteStrategicGame.coalitionExpectedPayoff
  simp_rw [constGame_coalitionTotalPayoff]
  have hS : ∑ aS : constGame.CoalitionAction S, (σ_S : _ → ℝ) aS = 1 := σ_S.2.2
  have hC : ∑ aC : constGame.ComplementAction S, (σ_C : _ → ℝ) aC = 1 := σ_C.2.2
  have hfactor : ∀ aS : constGame.CoalitionAction S,
      (∑ aC, (σ_S : _ → ℝ) aS * (σ_C : _ → ℝ) aC * (S.card : ℝ))
        = (σ_S : _ → ℝ) aS * (S.card : ℝ) := by
    intro aS
    rw [← Finset.sum_mul, ← Finset.mul_sum, hC, mul_one]
  rw [Finset.sum_congr rfl (fun aS _ => hfactor aS), ← Finset.sum_mul, hS, one_mul]

/-- **A TU strong equilibrium on the degenerate boundary.** Since every coalitional payoff equals
the constant `|S|`, no coalition can correlate-deviate to do better — every mixed-strategy profile
is a TU strong equilibrium. *Caveat (direction-insensitivity):* because the game is constant, the
strong-equilibrium inequality `coalitionExpectedPayoff σ_S' ≤ coalitionExpectedPayoff (marginal)`
binds at equality (`|S| = |S|`) for every deviation, so this witness exercises the
*satisfiability* of `IsTUStrongEquilibrium` on the boundary but does **not** distinguish the
inequality's direction. The strict-direction guard for the *core* inequality is supplied separately
by `convex3_core_strict_singleton` (`v({0}) = 1 < 3`). -/
private theorem constGame_strongEquilibrium (σ : constGame.MixedStrategy) :
    constGame.IsTUStrongEquilibrium σ := by
  intro S σ_S'
  rw [constGame_coalitionExpectedPayoff, constGame_coalitionExpectedPayoff]

/-- **The α-derived TU game is `v(S) = |S|`** (non-trivial: The grand coalition is worth `2`).
*Caveat:* because the underlying payoff is constant, this α-computation is direction-insensitive —
sup/inf order and coalition/complement roles all collapse to the same value `|S|`. The asymmetric
α-value computation that *does* pin the minimax direction is the PD singleton anchor
`pd_alphaChar_singleton` (`= 1`). -/
private theorem constGame_toTUGameOn_value (S : Finset constGame.Player) :
    constGame.toTUGameOn.value S = (S.card : ℝ) := by
  change constGame.alphaChar S = (S.card : ℝ)
  unfold FiniteStrategicGame.alphaChar
  simp_rw [constGame_coalitionExpectedPayoff]
  simp

/-- **Strong equilibrium ⇒ α-core, on the degenerate boundary.** The strong-equilibrium payoff
vector lies in the core of the α-derived TU game. The hypothesis is discharged concretely
(`constGame_strongEquilibrium`), and the resulting game `v(S) = |S|` is non-trivial, so the
*implication* `isTUStrongEquilibrium_implies_isCore` fires on real data. *Caveat:* on this constant
game both the strong-equilibrium premise and the core conclusion bind at equality, so the witness
does not distinguish the core inequality's direction; that strict-direction guard is supplied by
`convex3_core_strict_singleton`. -/
private theorem constGame_strongEq_mem_core (σ : constGame.MixedStrategy) :
    constGame.toTUGameOn.IsCore (constGame.payoffAtMixed σ) :=
  constGame.isTUStrongEquilibrium_implies_isCore (constGame_strongEquilibrium σ)

/-- The coalition marginal is the product of per-player marginals over the coalition. -/
private theorem pd_coalitionMarginal_apply (σ : prisonersDilemma.MixedStrategy)
    (aS : prisonersDilemma.CoalitionAction {p0}) :
    prisonersDilemma.coalitionMarginal {p0} σ aS
      = ∏ i : ({p0} : Finset prisonersDilemma.Player), σ i.val (aS i) :=
  prisonersDilemma.coalitionMarginal_apply {p0} σ aS

/-- The complement marginal is the product of per-player marginals over the complement. -/
private theorem pd_complementMarginal_apply (σ : prisonersDilemma.MixedStrategy)
    (aC : prisonersDilemma.ComplementAction {p0}) :
    prisonersDilemma.complementMarginal {p0} σ aC
      = ∏ i : {x : prisonersDilemma.Player // x ∉ ({p0} : Finset _)}, σ i.val (aC i) :=
  prisonersDilemma.complementMarginal_apply {p0} σ aC

/-- **The product-of-marginals identity.** Evaluating the bilinear coalitional payoff at the
product-of-marginals strategy recovers the sum of individual expected payoffs over the coalition. -/
private theorem pd_coalitionExpectedPayoff_at_marginals (σ : prisonersDilemma.MixedStrategy) :
    prisonersDilemma.coalitionExpectedPayoff {p0}
        (prisonersDilemma.coalitionMarginal {p0} σ) (prisonersDilemma.complementMarginal {p0} σ) =
      ∑ i ∈ ({p0} : Finset prisonersDilemma.Player), prisonersDilemma.expectedPayoff i σ :=
  prisonersDilemma.coalitionExpectedPayoff_at_marginals {p0} σ

/-- **Singleton complement at the grand coalition.** When `S = univ`, every complement strategy
coincides (the complement type is a subsingleton). -/
private theorem pd_complement_univ_subsingleton :
    Subsingleton (stdSimplex ℝ (prisonersDilemma.ComplementAction Finset.univ)) :=
  prisonersDilemma.complement_simplex_univ_subsingleton

end EconlibTest.GameTheory.Cooperative

end
