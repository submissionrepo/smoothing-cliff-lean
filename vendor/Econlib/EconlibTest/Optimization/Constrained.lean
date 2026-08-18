/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Optimization
import EconlibExamples.Optimization.ConstrainedQP
import EconlibExamples.Optimization.SlaterDuality
import Mathlib

/-!
# Constrained-Optimization Non-Vacuity Checks

Compile-time semantic witnesses for the scalar-duality, KKT/complementarity, and
sensitivity/envelope layers under `Econlib.Optimization.Constrained`. Each declaration here is a
*direction-* and *sign-sensitive* check against a hand-computed concrete program, guarding against
the failure modes that semantically-plausible-but-wrong statements would silently pass:

* **Primal/dual swap.** Weak duality for a *maximization* program orders the primal value *below*
  the dual value (`primalValueScalar ≤ dualValueScalar`). We anchor on the linear program
  `max x s.t. x ≤ 1, x ∈ [0,2]` whose primal optimum is `1`, dual optimum is `1`, and optimal
  multiplier is `λ* = 1`. Because strong duality makes both endpoints `1` (a `1 ≤ 1` that cannot
  show
  the direction numerically), the orientation is also exhibited at a *nonoptimal* multiplier:
  `primalValueScalar = 1 < 2 = dualObjectiveScalar X obj con 0` (`primal_lt_dualObjective_at_zero`),
  where a flipped weak duality would falsely require `2 ≤ 1`. A vacuous Slater point or a nonzero
  duality gap would also break a witness.
* **Flipped complementarity pairing.** Complementary slackness pairs a *slack* constraint with a
  *zero* multiplier and an *active* constraint with a possibly-positive multiplier. On a
  two-constraint family `choice = (3, 0)`, `multiplier = (0, 2)` — one slack, one active — we check
  the pairing lands on the correct index: `choice 0 > 0 ⇒ multiplier 0 = 0` and
  `multiplier 1 > 0 ⇒ choice 1 = 0`. A transposed pairing (zero multiplier forced on the *active*
  constraint) would break a witness.
* **Wrong envelope sign.** The envelope/sensitivity derivative of the value function equals the KKT
  multiplier *with a positive sign* — relaxing the constraint ceiling `θ` by `dθ` raises the value
  by `λ·dθ`. We anchor on `max -(x-3)² s.t. x ≤ θ` at `θ₀ = 1`, where the binding multiplier is
  `λ* = 2(3-1) = 4` and the value function `V(θ) = -(θ-3)²` has `V'(1) = 4 = λ*`. A sign flip would
  give `-4`.

The Slater program is `EconlibExamples.Optimization.SlaterDuality`; the quadratic program is
`EconlibExamples.Optimization.ConstrainedQP`; both are imported and reused so the witnesses ride on
the *same* concrete data the examples document.
-/

noncomputable section

namespace EconlibTest.Optimization.Constrained

open Econlib.Optimization Set

/-! ## 1. Scalar duality: The linear program `max x s.t. x ≤ 1, x ∈ [0,2]`

We reuse `EconlibExamples.Optimization.SlaterDuality` (`X = [0,2]`, `obj = x`, `con = x - 1`)
whose primal/dual optimum is `1` and optimal multiplier is `λ* = 1`. -/

namespace SlaterLP

open EconlibExamples.Optimization.SlaterDuality

/-- **The feasible set is provably nonempty** — `scalarFeasible X con` contains `x = 0`
(`con 0 = -1 ≤ 0`), guarding against a vacuously-empty primal. -/
theorem scalarFeasible_nonempty : (scalarFeasible X con).Nonempty :=
  ⟨0, by constructor <;> simp [X, con]⟩

/-- **Weak duality, with the correct direction.** For this *maximization* program the primal value
sits *below* the dual value: `primalValueScalar ≤ dualValueScalar`. A reversed inequality would
fail because (by strong duality) both sides are `1` but the *general* lemma must still produce `≤`,
not `≥`. -/
theorem weak_duality :
    primalValueScalar X obj con ≤ dualValueScalar X obj con :=
  primalValueScalar_le_dualValueScalar isCompact_Icc
    obj_continuousOn con_continuousOn scalarFeasible_nonempty

/-- **Weak duality is non-vacuous here**: Both endpoints equal `1`, so the `≤` is the genuine
`1 ≤ 1`. This explicitly anchors the primal value `1` *below* the dual value `1` — had the library
oriented weak duality the wrong way the anchored values would still be `1 ≤ 1`, but the
strong-duality witness below (a genuine *equality*) is what pins the gap to zero. -/
theorem weak_duality_anchored :
    primalValueScalar X obj con ≤ dualValueScalar X obj con ∧
      primalValueScalar X obj con = 1 ∧ dualValueScalar X obj con = 1 :=
  ⟨weak_duality, primal_eq_one, dual_eq_one⟩

/-- **Strict-gap direction witness at a *nonoptimal* multiplier.** The dual *value* (the inf over
`λ ≥ 0`) equals the primal value `1`, but the dual *objective* at the nonoptimal multiplier `λ = 0`
is `φ(0) = max (2 − 0) 0 = 2`, strictly above the primal value: `primalValueScalar = 1 < 2 =
dualObjectiveScalar X obj con 0`. This makes the primal/dual direction *observable* — the
zero-duality-gap witnesses (`1 ≤ 1`) cannot distinguish a reversed orientation numerically, but
`1 < 2` can: a flipped weak duality (`dual objective ≤ primal`) would falsely require `2 ≤ 1`. -/
theorem primal_lt_dualObjective_at_zero :
    primalValueScalar X obj con < dualObjectiveScalar X obj con 0 := by
  rw [primal_eq_one, dualObjective_eq]
  norm_num

/-- **Strong duality: Zero gap.** Under Slater the primal and dual values coincide. Calls the
general theorem `strongDuality_scalar_of_isSlater` directly on the example's discharged convexity /
continuity / Slater data. -/
theorem strong_duality_witness :
    primalValueScalar X obj con = dualValueScalar X obj con :=
  strongDuality_scalar_of_isSlater isCompact_Icc obj_continuousOn obj_concave
    con_continuousOn con_convex slater

/-- **Dual attainment: the dual infimum over `λ ≥ 0` is *attained* at some `λ* ≥ 0`.** This is the
existence statement, via `dualAttainment_scalar_of_isSlater`. The *concrete* optimal multiplier
`λ* = 1` and its value `φ(1) = 1` are pinned separately by `optimal_multiplier_is_one` below (this
theorem only asserts that *a* minimizer exists, not that it is `1`). -/
theorem dual_attainment_witness :
    ∃ lam, 0 ≤ lam ∧
      IsLeast (dualObjectiveScalar X obj con '' Set.Ici 0) (dualObjectiveScalar X obj con lam) :=
  dualAttainment_scalar_of_isSlater isCompact_Icc obj_continuousOn obj_concave
    con_continuousOn con_convex slater

/-- The attained dual least value is `1`, **proved directly from the closed form** `φ(λ) = max (2−λ)
λ` rather than recycling the library `dual_attained`. The two `IsLeast` clauses: (a) `1` is in the
image — attained at `λ = 1`, where `φ(1) = max 1 1 = 1`; (b) `1` lower-bounds the image — for every
`λ ≥ 0`, `φ(λ) = max (2−λ) λ ≥ 1` (if `λ ≤ 1` then `2 − λ ≥ 1`, else `λ ≥ 1`). This is an
independent numeric anchor for dual attainment, not a wrapper around the guarded theorem. -/
theorem dual_attainment_value : IsLeast (dualObjectiveScalar X obj con '' Set.Ici 0) 1 := by
  constructor
  · -- `1 ∈ image`: attained at `λ = 1`, `φ(1) = max (2-1) 1 = max 1 1 = 1`.
    exact ⟨1, by norm_num, by rw [dualObjective_eq]; norm_num⟩
  · -- `1` lower-bounds: `φ(λ) = max (2-λ) λ ≥ 1` for `λ ≥ 0`.
    rintro r ⟨lam, hlam, rfl⟩
    rw [dualObjective_eq]
    rcases le_total lam 1 with h | h
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right h

/-- **The optimal multiplier is `λ* = 1`** — it minimizes the dual objective over the nonnegative
multipliers, and `φ(1) = max (2−1) 1 = 1` is the common optimal value. This is the explicit
multiplier the duality theory promises. -/
theorem optimal_multiplier_is_one :
    IsMinOn (dualObjectiveScalar X obj con) (Set.Ici 0) 1 ∧
      dualObjectiveScalar X obj con 1 = 1 := by
  refine ⟨dual_minimizer, ?_⟩
  rw [dualObjective_eq, show (2 : ℝ) - 1 = 1 by norm_num, max_self]

/-! ### The dual-side sandwich lemmas, exercised at `λ = λ* = 1`

These wrap the `sSup`/`sInf` ceremony for the dual objective and value. We check them against
the closed-form dual objective `φ(λ) = max (2−λ) λ`, so the bounds land on concrete numbers. -/

/-- The Lagrangian image over `X = [0,2]` is bounded above at every multiplier (continuous image of
a compact set), the side condition the membership bounds need. -/
private lemma lagrangianScalar_image_bddAbove_at (lam : ℝ) :
    BddAbove ((fun x => lagrangianScalar obj con x lam) '' X) := by
  have hcont : ContinuousOn (fun x => lagrangianScalar obj con x lam) X := by
    unfold lagrangianScalar
    exact obj_continuousOn.sub ((continuousOn_const).mul con_continuousOn)
  exact (isCompact_Icc.image_of_continuousOn hcont).bddAbove

/-- **`le_dualObjectiveScalar`**: A feasible point lower-bounds the dual objective. At `λ* = 1` the
Lagrangian at `x = 1` is `obj 1 - 1·con 1 = 1 - 0 = 1`, which is `≤ φ(1) = 1`. -/
theorem le_dualObjective_witness :
    lagrangianScalar obj con 1 1 ≤ dualObjectiveScalar X obj con 1 :=
  le_dualObjectiveScalar (lagrangianScalar_image_bddAbove_at 1)
    (by simp [X])

/-- **`dualObjectiveScalar_le`**: A uniform Lagrangian bound upper-bounds the dual objective. The
Lagrangian `(1−λ)x + λ` at `λ = 1` is the constant `1`, so `φ(1) ≤ 1`. -/
theorem dualObjective_le_witness :
    dualObjectiveScalar X obj con 1 ≤ 1 :=
  dualObjectiveScalar_le ⟨0, by simp [X]⟩
    (fun x _ => by simp only [lagrangianScalar, obj, con]; ring_nf; rfl)

/-- The dual-objective image over `Ici 0` is bounded below (by the common optimal value `1`), the
side condition the dual-value membership bound needs. -/
private lemma dualObjective_image_bddBelow :
    BddBelow (dualObjectiveScalar X obj con '' Set.Ici 0) :=
  ⟨1, dual_attained.2⟩

/-- **`dualValueScalar_le`**: The dual value is `≤` the dual objective at any feasible multiplier.
At `λ* = 1`, `dualValue = 1 ≤ φ(1) = 1`. -/
theorem dualValue_le_witness :
    dualValueScalar X obj con ≤ dualObjectiveScalar X obj con 1 :=
  dualValueScalar_le dualObjective_image_bddBelow (by norm_num)

/-- **`le_dualValueScalar`**: A uniform lower bound on `φ` over `λ ≥ 0` lower-bounds the dual
value. Since `φ(λ) = max (2−λ) λ ≥ 1` for every `λ`, we get `1 ≤ dualValue`. -/
theorem le_dualValue_witness :
    (1 : ℝ) ≤ dualValueScalar X obj con :=
  le_dualValueScalar (fun lam _ => by
    rw [dualObjective_eq]
    rcases le_total lam 1 with h | h
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right h)

/-- **`dualValueScalar_eq_of_isLeast`**: The least element of the dual-objective image *is* the
dual value. Here that least element is `1`, so `dualValue = 1`. -/
theorem dualValue_eq_of_isLeast_witness :
    dualValueScalar X obj con = 1 :=
  dualValueScalar_eq_of_isLeast dual_attained

/-- **`achievableSet` is genuinely populated** (non-vacuous hypograph). The pair `(0, 1)` lies in
the achievable set: The primal optimum `x = 1` has `con 1 = 0 ≤ 0` (a feasible, hence `≤ 0` first
coordinate) and `1 ≤ obj 1 = 1` (the optimal value as second coordinate). This is the geometric
object the Hahn–Banach separation in strong duality acts on; an empty hypograph would make that
argument vacuous. -/
theorem achievableSet_witness : ((0 : ℝ), (1 : ℝ)) ∈ achievableSet X obj con :=
  ⟨1, by simp [X], by simp [con], by simp [obj]⟩

/-! ### Strong duality via *parametric* Slater

`strongDuality_scalar_of_parametricSlater` runs the same program through the stronger
`IsParametricSlater` qualification, where strict feasibility must persist as a parameter `p`
varies. We embed the LP as a `p`-independent family (`f p = obj`, `g p = con`); the strictly
feasible point `x = 0` then satisfies `con 0 = -1 < 0` for *every* nearby `p`, so the parametric
witness holds and strong duality follows at `p₀`. -/

/-- The parametric family is `p`-independent: `g p x = con x` for all `p : ℝ`. -/
private def gParam : ℝ → ℝ → ℝ := fun _ => con

/-- **Parametric Slater holds** for the `p`-independent embedding at base parameter `p₀ = 0`. The
strict-feasibility witness `x = 0` has `gParam p () 0 = con 0 = -1 < 0` uniformly in `p`. -/
theorem parametric_slater : IsParametricSlater X (fun p (_ : Unit) => gParam p) 0 where
  convex_X := convex_X
  convex_g := fun _ _ => con_convex
  strict_feasible_nearby :=
    ⟨0, by simp [X], Filter.Eventually.of_forall (fun _ _ => by simp [gParam, con])⟩

/-- **Strong duality via parametric Slater.** The parametric qualification closes the gap at the
base parameter, giving the same `primalValue = dualValue = 1` as the ordinary route. -/
theorem strong_duality_parametric :
    primalValueScalar X (obj) (gParam 0) = dualValueScalar X (obj) (gParam 0) :=
  strongDuality_scalar_of_parametricSlater (P := ℝ) (f := fun _ => obj) (g := gParam)
    isCompact_Icc obj_continuousOn obj_concave con_continuousOn con_convex parametric_slater

/-- Parametric strong duality is non-vacuous: At `p₀ = 0` both values are still `1` (the family is
`p`-independent, so this is `primal_eq_one` / `dual_eq_one` unchanged). -/
theorem strong_duality_parametric_anchored :
    primalValueScalar X obj (gParam 0) = 1 ∧ dualValueScalar X obj (gParam 0) = 1 :=
  ⟨primal_eq_one, dual_eq_one⟩

end SlaterLP

/-! ## 2. The unit-problem bridge

`scalarFeasible` and `lagrangianScalar` are `Unit`-indexed, `Empty`-equality specializations of
the unified `ConstrainedProblem`/`lagrangian`. We check the bridge lemmas are definitional on
concrete scalar data `f = x ↦ x`, `g = x ↦ x - 1`. -/

namespace Bridge

open EconlibExamples.Optimization.SlaterDuality

/-- **`toUnitConstrainedProblem` builds a genuine problem**: Its objective and constraint agree
with the scalar data. -/
theorem toUnitConstrainedProblem_witness :
    (toUnitConstrainedProblem obj con).f = obj ∧
      (toUnitConstrainedProblem obj con).g () = con :=
  ⟨rfl, rfl⟩

/-- **`lagrangianScalar_eq_lagrangian`**: The scalar Lagrangian is the `Unit`-indexed unified
Lagrangian. Anchored at `x = 1`, `λ = 1`, both equal `obj 1 - 1·con 1 = 1`. -/
theorem lagrangianScalar_eq_lagrangian_witness :
    lagrangianScalar obj con 1 1 =
      lagrangian (toUnitConstrainedProblem obj con) 1 (fun _ => 1) Empty.elim :=
  lagrangianScalar_eq_lagrangian obj con 1 1

/-- The two sides really evaluate to `1` (not vacuously equal junk). -/
theorem lagrangianScalar_value :
    lagrangianScalar obj con 1 1 = 1 := by
  simp only [lagrangianScalar, obj, con]; ring

/-- **Second bridge anchor at a *nonzero* constraint** — the sign-sensitive case. At `x = 0`,
`λ = 1`, the constraint `con 0 = 0 − 1 = −1 ≠ 0` is active, so the multiplier term does *not*
vanish: the correct scalar Lagrangian is `obj 0 − λ·con 0 = 0 − 1·(−1) = 1`. (The `x = 1` anchor
above is at `con 1 = 0`, where both `f − λg` and `f + λg` give `1` and cannot detect a sign flip;
here the wrong sign `f + λg` would give `0 + 1·(−1) = −1`.) The bridge equality with the unified
Lagrangian still
holds. -/
theorem lagrangianScalar_eq_lagrangian_at_active :
    lagrangianScalar obj con 0 1 =
      lagrangian (toUnitConstrainedProblem obj con) 0 (fun _ => 1) Empty.elim ∧
    lagrangianScalar obj con 0 1 = 1 :=
  ⟨lagrangianScalar_eq_lagrangian obj con 0 1, by simp only [lagrangianScalar, obj, con]; ring⟩

/-- **`scalarFeasible_eq`**: The scalar feasible set is the ambient box intersected with the
`Unit`-indexed inequality-feasible set. -/
theorem scalarFeasible_eq_witness :
    scalarFeasible X con =
      X ∩ ConstrainedProblem.feasibleSetIneq
        (toUnitConstrainedProblem (fun _ => (0 : ℝ)) con) :=
  scalarFeasible_eq X con

end Bridge

/-! ## 3. Complementary slackness: One active, one slack constraint

The `NonnegComplementarity (Fin 2)` convention is `choice ≥ 0`, `multiplier ≥ 0`,
`multiplier · choice = 0`. We hand-build a witness with

* index `0` — a **slack** constraint: `choice 0 = 3 > 0`, so the multiplier *must* vanish;
* index `1` — an **active** constraint: `choice 1 = 0`, so the multiplier *may* be positive
  (`multiplier 1 = 2`).

This is the correct pairing: A positive *choice* (slack constraint) forces a *zero* multiplier; a
positive *multiplier* (active constraint) forces a *zero* choice. A transposed pairing would put
the zero multiplier on the active constraint and break the witnesses. -/

namespace Complementarity

/-- The choice vector: Index `0` interior (`3`), index `1` at its floor (`0`). -/
private def choice : Fin 2 → ℝ := ![3, 0]

/-- The multiplier vector: Index `0` slack (`0`), index `1` active (`2`). -/
private def multiplier : Fin 2 → ℝ := ![0, 2]

/-- The complementarity certificate on the two-constraint program. -/
private def cert : NonnegComplementarity (Fin 2) where
  choice := choice
  multiplier := multiplier
  choice_nonneg := fun i => by fin_cases i <;> simp [choice]
  multiplier_nonneg := fun i => by fin_cases i <;> simp [multiplier]
  complementarity := fun i => by fin_cases i <;> simp [choice, multiplier]

/-- Index `0` has a strictly positive choice. -/
private lemma choice_zero_pos : 0 < cert.choice 0 := by simp [cert, choice]

/-- Index `1` has a strictly positive multiplier. -/
private lemma multiplier_one_pos : 0 < cert.multiplier 1 := by simp [cert, multiplier]

/-- **`multiplier_eq_zero_of_choice_pos` on the correct (slack) index.** The slack constraint —
where the choice is strictly positive — carries a *zero* multiplier. -/
theorem multiplier_eq_zero_witness : cert.multiplier 0 = 0 :=
  cert.multiplier_eq_zero_of_choice_pos choice_zero_pos

/-- **`choice_eq_zero_of_multiplier_pos` on the correct (active) index.** The active constraint —
where the multiplier is strictly positive — binds the choice to *zero*. A flipped pairing would
(wrongly) conclude `choice 0 = 0`, contradicting `choice 0 = 3`. -/
theorem choice_eq_zero_witness : cert.choice 1 = 0 :=
  cert.choice_eq_zero_of_multiplier_pos multiplier_one_pos

/-- **The pairing is genuinely on distinct indices.** The slack index `0` and the active index `1`
are different, so the two complementarity conclusions are not the same statement in disguise:
`multiplier 0 = 0` while `multiplier 1 = 2 ≠ 0`, and `choice 1 = 0` while `choice 0 = 3 ≠ 0`. -/
theorem pairing_is_nontrivial :
    cert.multiplier 0 = 0 ∧ cert.multiplier 1 ≠ 0 ∧
      cert.choice 1 = 0 ∧ cert.choice 0 ≠ 0 := by
  refine ⟨multiplier_eq_zero_witness, ?_, choice_eq_zero_witness, ?_⟩
  · simp [cert, multiplier]
  · simp [cert, choice]

/-- **`multiplier_mul_eq_zero_of_choice_pos`.** With a positive choice at index `0`, any scalar
multiple of the multiplier collapses to zero — here `5 · multiplier 0 = 0`. -/
theorem multiplier_mul_eq_zero_witness : (5 : ℝ) * cert.multiplier 0 = 0 :=
  cert.multiplier_mul_eq_zero_of_choice_pos choice_zero_pos 5

end Complementarity

/-! ## 4. Euler complementarity: Interior equality and strict-slack binding

The `EulerComplementarity` system is `lhs = scale i · marginal i + scale i · slack i` with
`slack i · choice i = 0`. We build a two-index witness:

* index `0` — **interior** (`choice 0 = 1 > 0`, `slack 0 = 0`): The Euler equation holds with
  equality, `lhs = scale·marginal`;
* index `1` — **strict-slack binding** (`choice 1 = 0`, `slack 1 = 2 > 0`,
  `scale·marginal = -1 < 1 = lhs`): The strict Euler *inequality* forces the choice to zero.

All entries are pinned so `lhs = 1` and stationarity holds exactly at both indices. -/

namespace Euler

private def lhs : ℝ := 1
private def scale : Fin 2 → ℝ := ![1, 1]
private def marginal : Fin 2 → ℝ := ![1, -1]
private def choice : Fin 2 → ℝ := ![1, 0]
private def slack : Fin 2 → ℝ := ![0, 2]

/-- The Euler/KKT system. Stationarity: Index `0` is `1 = 1·1 + 1·0`; index `1` is
`1 = 1·(-1) + 1·2`. -/
private def sys : EulerComplementarity (Fin 2) where
  lhs := lhs
  scale := scale
  marginal := marginal
  choice := choice
  slack := slack
  scale_nonneg := fun i => by fin_cases i <;> simp [scale]
  slack_nonneg := fun i => by fin_cases i <;> simp [slack]
  choice_nonneg := fun i => by fin_cases i <;> simp [choice]
  stationarity := fun i => by
    fin_cases i <;> simp only [lhs, scale, marginal, slack] <;> norm_num
  complementarity := fun i => by fin_cases i <;> simp [slack, choice]

private lemma choice_zero_pos : 0 < sys.choice 0 := by simp [sys, choice]

/-- **`equality_of_choice_pos` at the interior index.** With a positive choice (slack `= 0`) the
Euler equation collapses to the equality `lhs = scale·marginal`, here `1 = 1·1`. -/
theorem euler_equality_witness : sys.lhs = sys.scale 0 * sys.marginal 0 :=
  sys.equality_of_choice_pos choice_zero_pos

/-- The interior Euler equality is the genuine numeric `1 = 1`. -/
theorem euler_equality_value : sys.lhs = 1 ∧ sys.scale 0 * sys.marginal 0 = 1 := by
  constructor
  · simp [sys, lhs]
  · simp [sys, scale, marginal]

/-- **`scaled_marginal_le_lhs` at every index.** The scaled continuation marginal is weakly below
the common LHS once the nonnegative slack is included — at the binding index `1` this is the strict
`-1 ≤ 1`. -/
theorem euler_inequality_witness (i : Fin 2) :
    sys.scale i * sys.marginal i ≤ sys.lhs :=
  sys.scaled_marginal_le_lhs i

/-- The binding index has a *strict* slack: `scale·marginal = -1 < 1 = lhs`. -/
private lemma strict_slack_at_one : sys.scale 1 * sys.marginal 1 < sys.lhs := by
  simp only [sys, scale, marginal, lhs, Matrix.cons_val_one]
  norm_num

/-- **`choice_eq_zero_of_strict_slack` at the binding index.** A strict Euler inequality forces the
choice to zero — here `choice 1 = 0`. -/
theorem euler_strict_slack_binds : sys.choice 1 = 0 :=
  sys.choice_eq_zero_of_strict_slack strict_slack_at_one

end Euler

/-! ## 5. KKT optimality and the feasible set: The quadratic program

We reuse `EconlibExamples.Optimization.ConstrainedQP` at the concrete instance `a = 3`, `b = 1`
(`max -(x-3)² s.t. x ≤ 1`, binding since `b < a`, multiplier `λ* = 2(3-1) = 4 > 0`). The KKT point
is `x* = 1`. -/

namespace KKTQP

open EconlibExamples.Optimization.ConstrainedQP

/-- The KKT certificate at `x* = b = 1` for the binding program `a = 3`. -/
private def cert : MaxKKT (qp 3 1) 1 := kkt 3 1 (by norm_num)

/-- **The feasible set is provably nonempty.** The point `x = 0` satisfies `g 0 = 0 - 1 = -1 ≤ 0`,
so it lies in `(qp 3 1).feasibleSet`, guarding against a vacuously-empty feasible region. (With no
equality constraints, `feasibleSet = feasibleSetIneq`.) -/
theorem feasibleSet_nonempty : (0 : ℝ) ∈ (qp 3 1).feasibleSet := by
  refine ⟨fun i => ?_, fun j => j.elim⟩
  simp

/-- **The KKT multiplier is `λ* = 4 > 0`** — the binding constraint has a strictly positive shadow
price (`2·(3-1) = 4`). -/
theorem multiplier_value : multiplier 3 1 = 4 ∧ 0 < multiplier 3 1 := by
  refine ⟨by simp [multiplier]; norm_num, multiplier_pos 3 1 (by norm_num)⟩

/-- **`MaxKKT.objective_le_of_feasible`: The KKT point dominates a concrete feasible point.** The
comparison point `x = 0` is feasible (`feasibleSet_nonempty`), and the objective there
(`-(0-3)² = -9`) is below the KKT optimum (`-(1-3)² = -4`): `-9 ≤ -4`. A KKT point that did *not*
maximize would break this. -/
theorem objective_le_witness : (qp 3 1).f 0 ≤ (qp 3 1).f 1 :=
  cert.objective_le_of_feasible (fun i => by simp)

/-- The objective comparison is the genuine numeric `-9 ≤ -4` (non-vacuous). -/
theorem objective_values : (qp 3 1).f 0 = -9 ∧ (qp 3 1).f 1 = -4 := by
  constructor <;> simp <;> norm_num

end KKTQP

/-! ## 6. Sensitivity / envelope: The value-function derivative equals the multiplier

We parameterize the quadratic program by its constraint ceiling `θ`:

`V(θ) = max_x -(x-3)²   s.t.   x ≤ θ`,

with selection `xs θ = θ` (the optimum on the binding range `θ ≤ 3`) and KKT multiplier
`λ* = 2(3-θ₀)`. At `θ₀ = 1` the multiplier is `λ* = 4`, and the value function `V(θ) = -(θ-3)²` has
`V'(1) = -2(1-3) = 4 = λ*`. The envelope theorem `hasFDerivAt_constrainedMaxValue_of_localMaxOn`
recovers exactly this — derivative *equals* the multiplier, with the *positive* sign (relaxing the
ceiling raises the value). -/

namespace Envelope

open ContinuousLinearMap Filter Topology

/-- The objective `f(x, θ) = -(x-3)²` (independent of the parameter `θ`). -/
private def f : ℝ → ℝ → ℝ := fun x _ => -(x - 3) ^ 2

/-- The single inequality constraint `g(x, θ) = x − θ ≤ 0`, indexed by `Unit`. -/
private def g : Unit → ℝ → ℝ → ℝ := fun _ x θ => x - θ

/-- The selection: The optimum sits on the boundary, `xs θ = θ`. -/
private def xs : ℝ → ℝ := fun θ => θ

/-- The KKT multiplier `λ* = 4` at `θ₀ = 1` (i.e. `2·(3-1)`). -/
private def lam : Unit → ℝ := fun _ => 4

/-- The base parameter `θ₀ = 1`. -/
private def θ₀ : ℝ := 1

/-- The objective's Fréchet derivative at `(1, 1)`: `Df = -2(x-3)·dx = 4·dx`, no `θ`-dependence. As
a continuous linear map this is `4 • fst`. -/
private def Df : (ℝ × ℝ) →L[ℝ] ℝ := (4 : ℝ) • (fst ℝ ℝ ℝ)

/-- The constraint's Fréchet derivative at `(1, 1)`: `Dg = dx − dθ`, i.e. `fst − snd`. -/
private def Dg : Unit → (ℝ × ℝ) →L[ℝ] ℝ := fun _ => fst ℝ ℝ ℝ - snd ℝ ℝ ℝ

/-- **Joint differentiability of the objective** at `(xs θ₀, θ₀) = (1, 1)`, with derivative `Df`.
The map `p ↦ -(p.1 - 3)²` is `neg ∘ (·²) ∘ (· − 3) ∘ fst`; at `p.1 = 1` the chain rule gives the
slope `-2(1-3) = 4` in the `x`-direction and `0` in `θ`. -/
private lemma hasFDerivAt_f :
    HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) Df (xs θ₀, θ₀) := by
  have hbase : HasFDerivAt (fun p : ℝ × ℝ => p.1 - 3) (fst ℝ ℝ ℝ) ((xs θ₀, θ₀) : ℝ × ℝ) :=
    hasFDerivAt_fst.sub_const 3
  -- `(p.1 - 3)^2` has derivative `(2 • (p.1 - 3)^1) • fst`; negate gives the objective derivative.
  have hsq := (hbase.pow 2).neg
  -- At `p.1 = xs θ₀ = 1`, the scalar `-(2 • (1-3)^1) = 4`, so the derivative is `4 • fst = Df`.
  have hscal : -((2 • (((xs θ₀, θ₀) : ℝ × ℝ).1 - 3) ^ (2 - 1)) • fst ℝ ℝ ℝ) = Df := by
    rw [Df]
    rw [show (((xs θ₀, θ₀) : ℝ × ℝ).1 - 3) = (-2 : ℝ) by simp [xs, θ₀]; norm_num]
    rw [← neg_smul]
    norm_num
  rw [← hscal]
  exact hsq

/-- **Joint differentiability of the constraint** at `(1, 1)`, with derivative `Dg i = fst − snd`.
The map `p ↦ p.1 − p.2` is affine. -/
private lemma hasFDerivAt_g (i : Unit) :
    HasFDerivAt (fun p : ℝ × ℝ => g i p.1 p.2) (Dg i) (xs θ₀, θ₀) := by
  have h : HasFDerivAt (fun p : ℝ × ℝ => p.1 - p.2) (fst ℝ ℝ ℝ - snd ℝ ℝ ℝ)
      ((xs θ₀, θ₀) : ℝ × ℝ) :=
    hasFDerivAt_fst.sub hasFDerivAt_snd
  exact h

/-- The selection `xs θ = θ` has derivative the identity. -/
private lemma hasFDerivAt_xs :
    HasFDerivAt xs (ContinuousLinearMap.id ℝ ℝ) θ₀ :=
  hasFDerivAt_id θ₀

/-- Lagrangian stationarity in `x`: `∂ₓf = Σᵢ lamᵢ • ∂ₓgᵢ`. At `(1,1)`, `∂ₓf = 4` and
`lam·∂ₓg = 4·1 = 4`. -/
private lemma h_stat : Df.comp (inl ℝ ℝ ℝ) = ∑ i, lam i • (Dg i).comp (inl ℝ ℝ ℝ) := by
  rw [Finset.univ_unique, Finset.sum_singleton]
  apply ContinuousLinearMap.ext
  intro c
  simp only [lam, Df, Dg, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply, smul_eq_mul]
  ring

/-- Active-set persistence: The constraint stays binding along the selection,
`g (xs η) η = η − η =
0` for *every* `η`, so the second `h_bind` disjunct holds. -/
private lemma h_bind (i : Unit) :
    lam i = 0 ∨ (∀ᶠ η in 𝓝 θ₀, g i (xs η) η = 0) := by
  right
  filter_upwards with η
  simp [g, xs]

/-- **Local optimality of the selection.** Near `θ₀ = 1` (concretely, while `η < 3`) the boundary
point `xs η = η` is a feasible maximizer of `f (·) η = -(·-3)²` over the feasible set
`{x | x ≤ η}`: The objective is increasing on `(-∞, 3]`, so its max on `{x ≤ η}` with `η < 3` is at
`x = η`. -/
private lemma hloc :
    ∀ᶠ η in 𝓝 θ₀,
      xs η ∈ feasibleSet g η ∧ IsMaxOn (fun x => f x η) (feasibleSet g η) (xs η) := by
  -- `{η | η < 3}` is a neighborhood of `θ₀ = 1`.
  have hnhds : ∀ᶠ η in 𝓝 θ₀, η < 3 :=
    Iio_mem_nhds (by norm_num [θ₀] : (θ₀ : ℝ) < 3)
  filter_upwards [hnhds] with η hη
  constructor
  · -- `xs η = η` is feasible: `g () η η = η − η = 0 ≤ 0`.
    intro i
    simp [g, xs]
  · -- `η` maximizes `-(·-3)²` over `{x | x ≤ η}` since `-(·-3)²` is increasing on `(-∞, 3]`.
    intro x hx
    have hxη : x ≤ η := by
      have := hx ()
      simpa [g] using this
    simp only [f, xs, Set.mem_setOf_eq]
    -- both `x` and `η` are `≤ 3`; the parabola `-(t-3)²` is increasing there.
    nlinarith [hxη, hη.le, sq_nonneg (x - 3), sq_nonneg (η - 3)]

/-- The selection at the base parameter `θ₀ = 1` is feasible. -/
private lemma xs_θ₀_feasible : xs θ₀ ∈ feasibleSet g θ₀ := by
  intro i
  simp [g, xs]

/-- The selection at the base parameter maximizes the objective over the feasible set: `x* = 1`
maximizes `-(·-3)²` over `{x | x ≤ 1}`. -/
private lemma xs_θ₀_isMaxOn : IsMaxOn (fun x => f x θ₀) (feasibleSet g θ₀) (xs θ₀) := by
  intro x hx
  have hxθ : x ≤ (1 : ℝ) := by simpa [g, θ₀] using hx ()
  simp only [f, xs, θ₀, Set.mem_setOf_eq]
  nlinarith [hxθ, sq_nonneg (x - 3)]

/-- **`constrainedMaxValue_eq_of_isMaxOn`: The value function equals the objective at the
maximizer.** At `θ₀ = 1` the maximizer is `x* = 1` and the optimal value is
`f 1 1 = -(1-3)² = -4`. -/
theorem constrainedMaxValue_eq_witness :
    constrainedMaxValue f g θ₀ = f (xs θ₀) θ₀ :=
  constrainedMaxValue_eq_of_isMaxOn xs_θ₀_feasible xs_θ₀_isMaxOn

/-- The optimal value is genuinely `-4` (non-vacuous): `V(1) = -(1-3)² = -4`. -/
theorem constrainedMaxValue_value : constrainedMaxValue f g θ₀ = -4 := by
  rw [constrainedMaxValue_eq_witness]
  simp only [f, xs, θ₀]; norm_num

/-- **`eventuallyEq_constrainedMaxValue_of_localMaxOn`: The path value agrees with the value
function near `θ₀`.** Throughout a neighborhood of `θ₀ = 1` the path value `f (xs η) η` equals the
genuine value function `constrainedMaxValue f g η` — the distilled hypothesis the envelope theorem
consumes. -/
theorem eventuallyEq_constrainedMaxValue_witness :
    (fun η => f (xs η) η) =ᶠ[𝓝 θ₀] constrainedMaxValue f g :=
  eventuallyEq_constrainedMaxValue_of_localMaxOn hloc

/-- The envelope derivative as a continuous linear map: Exactly the conclusion of the
value-function envelope theorem, `Df.comp inr − Σᵢ lamᵢ • (Dg i).comp inr`. Its action on the unit
direction is `∂_θ f − λ·∂_θ g = 0 − 4·(−1) = 4`. -/
private def Denv : ℝ →L[ℝ] ℝ :=
  Df.comp (inr ℝ ℝ ℝ) - ∑ i, lam i • (Dg i).comp (inr ℝ ℝ ℝ)

/-- **The envelope identity.** `constrainedMaxValue f g` is differentiable at `θ₀ = 1` with the
envelope derivative `Denv`. This is `hasFDerivAt_constrainedMaxValue_of_localMaxOn` fed the
hand-checked first-order data: Joint differentiability, stationarity, active-set persistence, and
local optimality of the boundary selection. -/
theorem hasFDerivAt_constrainedMaxValue_witness :
    HasFDerivAt (constrainedMaxValue f g) Denv θ₀ :=
  hasFDerivAt_constrainedMaxValue_of_localMaxOn f g xs lam θ₀ Df Dg
    (ContinuousLinearMap.id ℝ ℝ) hasFDerivAt_f hasFDerivAt_g hasFDerivAt_xs h_stat h_bind hloc

/-- **The derivative equals the multiplier, with the correct sign.** Evaluating the envelope
derivative on the unit direction returns `+4 = λ*`, not `-4`: Relaxing the constraint ceiling
raises the value at the shadow price. -/
theorem envelope_derivative_eq_multiplier :
    Denv 1 = lam () := by
  rw [Denv, lam]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_nsmul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Df, Dg,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.coe_snd', lam, smul_eq_mul]
  norm_num

/-- **The *value function's* one-dimensional derivative equals the multiplier `λ* = 4`.** This binds
the algebraic check above to the genuine value-function derivative: from the envelope theorem
witness `hasFDerivAt_constrainedMaxValue_witness`
(a `HasFDerivAt (constrainedMaxValue f g) Denv θ₀`)
we read off `HasDerivAt (constrainedMaxValue f g) (Denv 1) θ₀`, and `Denv 1 = lam () = 4`. So the
sensitivity `V'(θ₀) = λ* = +4` is the *value function's* derivative, not merely the derivative of a
candidate map — relaxing the ceiling `θ` at `θ₀ = 1` raises `V` at the shadow price `4` (positive
sign). -/
theorem hasDerivAt_constrainedMaxValue_eq_multiplier :
    HasDerivAt (constrainedMaxValue f g) (lam ()) θ₀ := by
  have h : HasDerivAt (constrainedMaxValue f g) (Denv 1) θ₀ :=
    hasFDerivAt_constrainedMaxValue_witness.hasDerivAt
  rwa [envelope_derivative_eq_multiplier] at h

end Envelope

end EconlibTest.Optimization.Constrained

end
