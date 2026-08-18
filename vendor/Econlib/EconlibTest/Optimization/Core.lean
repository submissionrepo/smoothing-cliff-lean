/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Optimization
import EconlibExamples.Optimization.BudgetMaximumTheorem
import EconlibExamples.Optimization.HotellingProfit
import EconlibExamples.Optimization.MonopolyPricing
import Mathlib

/-!
# Optimization-core non-vacuity witnesses

Compile-time semantic witnesses for the `Econlib.Optimization` core files `Basic`,
`MaximumTheorem`, and `Envelope`. Every abstract argmax / value-function / envelope statement is
forced through a concrete optimization program with a *hand-computed* optimizer, value, and
gradient, so that a vacuous, off-by-the-wrong-extremum, or sign-flipped declaration cannot pass
silently.

The witnesses are anchored on three concrete programs already developed in `EconlibExamples`:

* the **monopoly profit** program `π(p) = (p − c)(a − b·p)` (`MonopolyPricing`), a strictly concave
  parabola with unique global maximizer `p* = (a + b·c)/(2·b)` — taken at the numbers `a = 4`,
  `b = 1`, `c = 0`, so `p* = 2` and `π(p*) = 4`;
* the single-good **budget correspondence** `Φ(p) = budgetSetAt p 1 = [0, 1/p]` with utility
  `√(x₀)` (`BudgetMaximumTheorem`), whose value function is the indirect utility and whose argmax
  is the singleton demand `{1/p}`;
* the single-output **firm profit** program `π(p, y) = p·y − y²/2` on `[0, ymax]`
  (`HotellingProfit`), whose profit-function gradient is the supply `y*(p) = p`.

## What each block catches

* **Argmax core (`Basic`)** — an *empty* argmax (vacuous existence), a value function that returns
  the wrong extremum (min instead of max), and a single-valuedness claim that quietly admits two
  maximizers. The strictly concave monopoly profit pins `argmax = {2}` and `valueFunction = 4`, the
  global *maximum*, not the unbounded-below minimum.
* **Maximum theorem (`MaximumTheorem`)** — a value-function continuity / argmax-UHC statement made
  vacuous by an *empty* argmax. The budget argmax is the genuine singleton `{1/p}` at every price
  (the UHC and compact-valued witnesses are *paired with* this singleton identity), and Berge's
  value conclusion is anchored to the indirect utility `√(1/p)` (`= 1` at `p = 1`) rather than only
  to continuity, so a min-instead-of-max bug returning `0` would be caught.
* **Envelope (`Envelope`)** — the *sign* of the value-function gradient. Hotelling: The profit
  gradient is `+y*` (output, positive in the output price), not `−y*`. Shephard: The negated
  expenditure gradient is `−x*` (Hicksian demand with the documented sign). Roy: the **calculus
  identity behind** Roy's identity (no consumer optimization is formalized — the `xstar` term is
  supplied to satisfy the theorem's hypotheses), with the price gradient of indirect utility
  carrying
  the **minus**, `∇_p v = −(∂v/∂w)·xstar`, anchored at `(p, w) = (2, 4)`. A flipped sign fails to
  typecheck against the hand-computed value here.
-/

noncomputable section

namespace EconlibTest.Optimization.Core

open Econlib.Optimization

/-! ## Block 1: Argmax core (`Basic.lean`)

Anchored on the monopoly profit `π(p) = (p − c)(a − b·p)` at `a = 4, b = 1, c = 0`, i.e.
`π(p) = p·(4 − p)`, a downward parabola with unique global maximizer `p* = 2` and value `π(2) = 4`.
Strict concavity (`StrictConcaveOn ℝ univ π`) makes the argmax a singleton. -/

open EconlibExamples.Optimization.MonopolyPricing (profit pStar profit_isMaxOn)

/-- The concrete monopoly profit `π(p) = p·(4 − p)` (linear demand `4 − p`, zero marginal cost). -/
private abbrev monoProfit : ℝ → ℝ := profit 4 1 0

/-- The hand-computed optimizer: `p* = (4 + 1·0)/(2·1) = 2`. -/
private abbrev monoStar : ℝ := pStar 4 1 0

/-- `p* = 2`, the cost/choke midpoint, evaluated. -/
theorem monoStar_eq : monoStar = 2 := by norm_num [monoStar, pStar]

/-- `π(2) = 2·(4 − 2) = 4`, the optimal value, evaluated. -/
theorem monoProfit_star_eq : monoProfit monoStar = 4 := by
  rw [monoStar_eq]; norm_num [monoProfit, profit]

/-- The optimizer globally maximizes profit over all prices (`MonopolyPricing.profit_isMaxOn`). -/
theorem monoStar_isMaxOn : IsMaxOn monoProfit Set.univ monoStar :=
  profit_isMaxOn 4 1 0 (by norm_num)

/-- The profit is **strictly concave** on the whole line: `π(p) = −p² + 4p`, with second derivative
`π″ ≡ −2 < 0`. This is the single-valuedness input for the argmax-uniqueness lemmas. -/
theorem monoProfit_strictConcaveOn : StrictConcaveOn ℝ Set.univ monoProfit := by
  have haff : monoProfit = fun p : ℝ => -p ^ 2 + 4 * p := by
    funext p; simp only [monoProfit, profit]; ring
  rw [haff]
  refine strictConcaveOn_univ_of_deriv2_neg (by fun_prop) (fun x => ?_)
  -- π′(p) = −2p + 4, π″ ≡ −2.
  have hd1 : deriv (fun p : ℝ => -p ^ 2 + 4 * p) = fun p => -2 * p + 4 := by
    funext p
    have h : HasDerivAt (fun p : ℝ => -p ^ 2 + 4 * p) (-2 * p + 4) p := by
      have hp2 : HasDerivAt (fun p : ℝ => -p ^ 2) (-(2 * p)) p := by
        simpa using ((hasDerivAt_pow 2 p).const_mul (-1 : ℝ))
      simpa using hp2.add ((hasDerivAt_id p).const_mul 4)
    exact h.deriv
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, hd1]
  have h2 : HasDerivAt (fun p : ℝ => -2 * p + 4) (-2) x := by
    simpa using ((hasDerivAt_id x).const_mul (-2)).add_const 4
  rw [h2.deriv]; norm_num

/-! ### Value-function evaluation lemmas

`valueFunction_eq_of_*` recover the optimal *value* `4`, the global maximum, from membership /
maximality data — catching a value function that silently returns the wrong extremum. -/

/-- `4` is the greatest element of the profit image `π '' univ`: It is attained at `p* = 2` and
bounds every value (`IsMaxOn`). This is the `IsGreatest` data `valueFunction_eq_of_isGreatest`
consumes. -/
theorem monoProfit_isGreatest : IsGreatest (monoProfit '' Set.univ) 4 := by
  refine ⟨⟨monoStar, Set.mem_univ _, monoProfit_star_eq⟩, ?_⟩
  rintro _ ⟨p, -, rfl⟩
  calc monoProfit p ≤ monoProfit monoStar := monoStar_isMaxOn (Set.mem_univ p)
    _ = 4 := monoProfit_star_eq

/-- **`valueFunction_eq_of_isGreatest`**: The value function reads the greatest image element,
`valueFunction π univ = 4`. -/
theorem valueFunction_eq_of_isGreatest_witness :
    valueFunction monoProfit Set.univ = 4 :=
  valueFunction_eq_of_isGreatest monoProfit_isGreatest

/-- **`valueFunction_eq_of_mem_isMaxOn`**: At the attained maximizer `p* = 2` the value function is
`π(2) = 4` — not the unbounded-below infimum. -/
theorem valueFunction_eq_of_mem_isMaxOn_witness :
    valueFunction monoProfit Set.univ = 4 := by
  rw [valueFunction_eq_of_mem_isMaxOn (Set.mem_univ monoStar) monoStar_isMaxOn]
  exact monoProfit_star_eq

/-! ### The argmax set on a compact interval

For the structural lemmas that require a compact domain (`argmax_nonempty`, `argmax_compact`)
we restrict to `S = [0, 4]`, which contains the interior maximizer `p* = 2`. Over `[0,4]` the
global maximum is still attained only at `2`, so `argmax = {2}`. -/

/-- The compact constraint set `[0, 4]` containing the optimizer. -/
private abbrev monoBox : Set ℝ := Set.Icc 0 4

/-- The optimizer lies in `[0, 4]`. -/
theorem monoStar_mem_box : monoStar ∈ monoBox := by
  rw [monoStar_eq]; exact ⟨by norm_num, by norm_num⟩

/-- `p* = 2` maximizes profit over the box (restricting the global maximum). -/
theorem monoStar_isMaxOn_box : IsMaxOn monoProfit monoBox monoStar :=
  fun p _ => monoStar_isMaxOn (Set.mem_univ p)

/-- Profit is continuous (a polynomial), the input the compact-domain lemmas need. -/
theorem monoProfit_continuous : Continuous monoProfit := by
  change Continuous (profit 4 1 0); unfold profit; fun_prop

/-- **`argmax_nonempty`**: A continuous function on the nonempty compact box `[0, 4]` attains its
maximum — the argmax is non-empty (catches a vacuous existence claim). -/
theorem argmax_nonempty_witness : (argmax monoProfit monoBox).Nonempty :=
  argmax_nonempty isCompact_Icc ⟨monoStar, monoStar_mem_box⟩ monoProfit_continuous.continuousOn

/-- **`argmax_compact`**: The argmax of the continuous profit on the compact box is compact. -/
theorem argmax_compact_witness : IsCompact (argmax monoProfit monoBox) :=
  argmax_compact isCompact_Icc monoProfit_continuous.continuousOn

/-- **`valueFunction_eq_of_mem_argmax`**: At any maximizer over the (nonempty compact) box the
value function equals the optimal value `π(2) = 4`. The maximizer `p* = 2` lies in the argmax. -/
theorem valueFunction_eq_of_mem_argmax_witness :
    valueFunction monoProfit monoBox = 4 := by
  have hmem : monoStar ∈ argmax monoProfit monoBox := ⟨monoStar_mem_box, monoStar_isMaxOn_box⟩
  rw [← valueFunction_eq_of_mem_argmax isCompact_Icc ⟨monoStar, monoStar_mem_box⟩
    monoProfit_continuous.continuousOn hmem]
  exact monoProfit_star_eq

/-! ### Single-valuedness and uniqueness

Strict concavity makes the argmax a subsingleton; with the exhibited maximizer it is the
singleton `{2}`. Catches a uniqueness claim that quietly admits a second maximizer. -/

/-- Profit is strictly concave on the box (restricting `monoProfit_strictConcaveOn`). -/
theorem monoProfit_strictConcaveOn_box : StrictConcaveOn ℝ monoBox monoProfit :=
  monoProfit_strictConcaveOn.subset (Set.subset_univ _) (convex_Icc 0 4)

/-- **`argmax_subsingleton_of_strictConcaveOn`**: Strict concavity forces at most one maximizer. -/
theorem argmax_subsingleton_witness : (argmax monoProfit monoBox).Subsingleton :=
  argmax_subsingleton_of_strictConcaveOn monoProfit_strictConcaveOn_box

/-- **`argmax_eq_singleton`**: The argmax is exactly the singleton `{2}` — the unique
profit-maximizing price. -/
theorem argmax_eq_singleton_witness : argmax monoProfit monoBox = {monoStar} :=
  argmax_eq_singleton monoProfit_strictConcaveOn_box monoStar_mem_box monoStar_isMaxOn_box

/-- The singleton, with the optimizer evaluated: `argmax = {2}`. -/
theorem argmax_eq_singleton_two : argmax monoProfit monoBox = {2} := by
  rw [argmax_eq_singleton_witness, monoStar_eq]

/-- **`argmax_convex`**: The argmax of the (quasiconcave) profit is convex. Strict concavity gives
concavity gives quasiconcavity; here the argmax is in fact the singleton `{2}`, trivially convex,
but the lemma is exercised on its genuine quasiconcavity hypothesis. -/
theorem argmax_convex_witness : Convex ℝ (argmax monoProfit monoBox) :=
  argmax_convex (monoProfit_strictConcaveOn_box.concaveOn.quasiconcaveOn)

/-- **`image_val_argmax_univ`**: Transport between the subtype-level argmax (objective defined only
on the slice `↑[0,4]`, constraint `univ`) and the ambient argmax on `[0, 4]`. The subtype objective
`g z = π z.1` agrees with `π` on the box, so its `univ`-argmax pushes forward to the ambient one. -/
theorem image_val_argmax_univ_witness :
    Subtype.val '' argmax (fun z : ↥monoBox => monoProfit z.1) Set.univ
      = argmax monoProfit monoBox :=
  image_val_argmax_univ (fun _ => rfl)

/-! ## Block 2: Berge's maximum theorem (`MaximumTheorem.lean`)

Anchored on the single-good budget correspondence `Φ(p) = budgetSetAt p 1 = [0, 1/p]` of
`BudgetMaximumTheorem`, with strictly concave utility `√(x₀)`. The argmax is the genuine singleton
`{1/p}` (full-expenditure demand), so the upper-hemicontinuity and compact-valuedness conclusions
land on a *non-empty* correspondence — UHC of an empty-valued correspondence would be vacuous. -/

open EconlibExamples.Optimization.BudgetMaximumTheorem
  (Price objective Φ objective_continuous Φ_upperHemicontinuous Φ_lowerHemicontinuous
   Φ_isCompact Φ_nonempty demand_eq_singleton demandBundle indirectUtility_eq)

/-- **The demand argmax is non-empty** at every price — in fact the singleton `{1/p}`. This is the
non-vacuity guard: It forces the Berge UHC / compact-valued conclusions below onto a correspondence
that is genuinely inhabited rather than empty. -/
theorem budget_argmax_nonempty (p : Price) : (argmax (objective p) (Φ p)).Nonempty := by
  rw [demand_eq_singleton p]; exact Set.singleton_nonempty _

/-- **`valueFunction_upperSemicontinuous`**: The indirect utility `p ↦ sup_{x ∈ Φ p} √(x₀)` is
upper semicontinuous in the price. -/
theorem valueFunction_upperSemicontinuous_witness :
    UpperSemicontinuous (fun p : Price => valueFunction (objective p) (Φ p)) :=
  valueFunction_upperSemicontinuous objective_continuous Φ_upperHemicontinuous Φ_isCompact
    Φ_nonempty

/-- **`valueFunction_lowerSemicontinuous`**: The indirect utility is lower semicontinuous. -/
theorem valueFunction_lowerSemicontinuous_witness :
    LowerSemicontinuous (fun p : Price => valueFunction (objective p) (Φ p)) :=
  valueFunction_lowerSemicontinuous objective_continuous Φ_lowerHemicontinuous Φ_isCompact
    Φ_nonempty

/-- **`valueFunction_continuous` (Berge Part 1)**: The indirect utility is continuous in price. -/
theorem valueFunction_continuous_witness :
    Continuous (fun p : Price => valueFunction (objective p) (Φ p)) :=
  valueFunction_continuous objective_continuous Φ_upperHemicontinuous Φ_lowerHemicontinuous
    Φ_isCompact Φ_nonempty

/-- **The Berge value function is the genuine indirect utility `√(1/p)`, not a wrong extremum.**
The continuity target is rewritten through `indirectUtility_eq` to the closed form
`p ↦ √(1/p.val 0)`, so the witness anchors Berge's *value* conclusion to the hand-computed indirect
utility — a bug that always returned the lower endpoint (value `√0 = 0`) would not be continuous as
this closed form, and in any case would not equal `√(1/p)`. -/
theorem valueFunction_eq_indirectUtility_witness :
    (fun p : Price => valueFunction (objective p) (Φ p)) =
      fun p : Price => Real.sqrt (1 / p.val 0) :=
  funext indirectUtility_eq

/-- **The indirect utility at the concrete price `p = 1` is `√1 = 1`** (a positive level, not the
`0` a min-instead-of-max bug would report). Discharges the value conclusion on actual data. -/
theorem indirectUtility_at_one :
    valueFunction (objective (⟨fun _ => 1, by norm_num⟩ : Price))
      (Φ (⟨fun _ => 1, by norm_num⟩ : Price)) = 1 := by
  rw [indirectUtility_eq]; norm_num

/-- **`argmax_isCompact` (Berge Part 3)**: The demand correspondence is compact-valued — *and the
value is the non-empty singleton* `{demandBundle p}`. The conjoined singleton identity is what makes
this non-vacuous: compactness alone would survive an empty-valued argmax bug (`∅` is compact), so we
exhibit the genuine demand. -/
theorem argmax_isCompact_witness (p : Price) :
    IsCompact (argmax (objective p) (Φ p)) ∧ argmax (objective p) (Φ p) = {demandBundle p} :=
  ⟨argmax_isCompact objective_continuous Φ_isCompact p, demand_eq_singleton p⟩

/-- **`argmax_upperHemicontinuous` (Berge Part 2)**: The demand correspondence is upper
hemicontinuous — *paired with* the singleton identity `∀ p, argmax = {demandBundle p}`. UHC of an
empty-valued correspondence is exactly the vacuity to guard against; the conjoined singleton fact
connects the UHC conclusion to a genuinely single-valued (non-empty) demand. -/
theorem argmax_upperHemicontinuous_witness :
    UpperHemicontinuous (fun p : Price => argmax (objective p) (Φ p)) ∧
      ∀ p : Price, argmax (objective p) (Φ p) = {demandBundle p} :=
  ⟨argmax_upperHemicontinuous objective_continuous Φ_upperHemicontinuous Φ_lowerHemicontinuous
      Φ_isCompact Φ_nonempty, demand_eq_singleton⟩

/-- The demand argmax is the singleton `{1/p}`, the witness that anchors the non-vacuity of the
hemicontinuity conclusions to a concrete single-valued demand. -/
theorem budget_argmax_eq_singleton (p : Price) :
    argmax (objective p) (Φ p) = {demandBundle p} :=
  demand_eq_singleton p

/-! ## Block 3: The envelope theorem stack (`Envelope.lean`)

The envelope **signs** are the content: Hotelling's profit gradient is `+y*` (supply,
increasing in the output price), Shephard's negated-expenditure gradient is `−x*` (so expenditure
gradient is the Hicksian demand `+x*`), and Roy's indirect-utility price gradient carries the
**minus**, `∇_p v = −(∂v/∂w)·x*`. Each is anchored on a hand-computed program. -/

open Econlib.Optimization.Envelope

/-! ### Hotelling: Profit gradient = optimal supply (positive sign)

The single-output firm `π(p, y) = p·y − y²/2` on `[0, ymax]` from `HotellingProfit`. We fix
`ymax = 2` and the interior price `p = 1`, where the unique optimal output is `y* = p = 1`, so the
profit gradient is `+1` — the supply, with the *positive* sign. -/

namespace Hotelling

open EconlibExamples.Optimization.HotellingProfit

/-- The concrete capacity `ymax = 2` is nonnegative (the instance the technology subtype needs). -/
instance : Fact ((0 : ℝ) ≤ 2) := ⟨by norm_num⟩

/-- The interior price `p = 1 ∈ (0, 2)` at which the firm's problem has a unique solution. -/
theorem one_mem_Ioo : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) 2 := ⟨by norm_num, by norm_num⟩

/-- The optimal supply at `p = 1` is `y* = 1`, the hand-computed interior maximizer
(`Y_embed (y_star) = p = 1`). -/
theorem supply_eq_one : Y_embed (y_star (ymax := 2) one_mem_Ioo) = 1 := rfl

/-- **`hasGradientAt_profitFunction` (Hotelling's lemma)**, anchored: The gradient of the profit
function `Π(p) = sup_y (p·y − y²/2)` at `p = 1` is the optimal supply `y* = 1`, a *positive*
quantity equal to the output price — not `−1`. A sign flip would make the gradient `−1` and fail to
match this. We discharge the upstream theorem's hypotheses directly (openness of the price set,
continuity of cost and embedding, the singleton-argmax fact). -/
theorem hasGradientAt_profitFunction_witness :
    HasGradientAt (profitFunction (Y_embed (ymax := 2)) (cost (ymax := 2))) 1 1 := by
  have h := hasGradientAt_profitFunction Y_embed cost isOpen_Ioo continuous_cost
    continuous_Y_embed (X := Set.Ioo 0 2) 1 one_mem_Ioo (y_star one_mem_Ioo)
    (argmax_eq_singleton one_mem_Ioo)
  rwa [supply_eq_one] at h

/-- **Scalar Hotelling, the positive-sign punchline**: `Π′(1) = y*(1) = 1 = p`. Differentiating the
maximized profit in the output price reads off the (positive) supply, *not* its negation. -/
theorem deriv_profitFunction_eq_one :
    deriv (profitFunction (Y_embed (ymax := 2)) (cost (ymax := 2))) 1 = 1 :=
  deriv_profitFunction (ymax := 2) one_mem_Ioo

/-- **`profitObjective` evaluation**: `π(p, y) = p·y − y²/2`, the direct objective the value
function maximizes — checked at `p = 1`, `y = 1`: `π(1,1) = 1 − 1/2 = 1/2`. -/
theorem profitObjective_at :
    profitObjective (Y_embed (ymax := 2)) (cost (ymax := 2)) 1 (y_star one_mem_Ioo) = 1 / 2 := by
  rw [profitObjective_apply]; norm_num [y_star]

/-- **`profitFunction` evaluation**: `Π(1) = sup_y (1·y − y²/2) = 1/2` (the value function at the
optimal supply `y* = 1`). This anchors the *level*, complementing the gradient. -/
theorem profitFunction_at :
    profitFunction (Y_embed (ymax := 2)) (cost (ymax := 2)) 1 = 1 / 2 := by
  rw [profitFunction, valueFunction_eq one_mem_Ioo]; norm_num

/-- **`argmax_iSup_eq_setOf_isMaxOn`** on the firm's profit objective at `p = 1`: The iSup-based
optimizer set coincides with the `IsMaxOn`-over-`univ` set. Boundedness of the objective range
comes from compactness of the technology set. -/
theorem argmax_iSup_eq_setOf_isMaxOn_witness :
    Danskin.argmax_iSup (profitObjective (Y_embed (ymax := 2)) (cost (ymax := 2))) 1
      = {z ∈ Set.univ | IsMaxOn
          (profitObjective (Y_embed (ymax := 2)) (cost (ymax := 2)) 1) Set.univ z} :=
  argmax_iSup_eq_setOf_isMaxOn _ 1 (bddAbove_profit 1)

end Hotelling

/-! ### Shephard: Expenditure gradient = Hicksian demand (the documented sign)

A one-good Hicksian consumer who must reach a fixed utility target, modeled as consuming
`x ∈ [1, 2]` (the lower corner `x = 1` is the cheapest way to hit the target). At any price `p > 0`
the expenditure-minimizing bundle is the corner `x* = 1`, so the **negated** expenditure function
`−e(p) = sup_x (−p·x)` has gradient `−x* = −1`; equivalently the expenditure gradient is `+x* = 1`,
the Hicksian demand. A sign flip would report the gradient as `+1` here. -/

namespace Shephard

/-- The Hicksian feasible set: Bundles `[1, 2]` reaching the utility target (the corner `1` is
cheapest). -/
abbrev HicksY : Type := ↥(Set.Icc (1 : ℝ) 2)

instance : CompactSpace HicksY := compactSpace_Icc 1 2

instance : Nonempty HicksY := ⟨⟨1, by norm_num⟩⟩

/-- The bundle embedding `x ↦ (x : ℝ)` (the produced/consumed quantity). -/
def embed : HicksY → ℝ := fun x => (x : ℝ)

/-- The embedding is continuous (the subtype coercion). -/
theorem embed_continuous : Continuous embed := continuous_subtype_val

/-- The Hicksian demand: The cheapest corner `x* = 1 ∈ [1, 2]`. -/
def x_star : HicksY := ⟨1, by norm_num⟩

/-- The Hicksian demand quantity is `1`. -/
@[simp] theorem embed_x_star : embed x_star = 1 := rfl

/-- `−p·x` for `p = 1` collapses to `−(x : ℝ)`, evaluated through `real_inner_real`. -/
theorem expendObjective_at (x : HicksY) :
    expendObjective embed 1 x = -(x : ℝ) := by
  simp only [expendObjective, embed, real_inner_real, one_mul]

/-- The objective range is bounded above on the compact technology set, so its supremum is a
genuine least upper bound. -/
theorem bddAbove_expend : BddAbove (Set.range (fun x : HicksY => expendObjective embed 1 x)) :=
  (isCompact_range ((Danskin.ContinuousOnProd.continuous_right
    (Z := HicksY)
    (by
      unfold Danskin.ContinuousOnProd expendObjective
      exact (continuous_inner.comp
        (continuous_fst.prodMk (embed_continuous.comp continuous_snd))).neg.continuousOn)
    1 (Set.mem_univ 1)))).bddAbove

/-- **The negated expenditure value at `p = 1` is `−1`.** The `≤` direction: Every `−(x:ℝ) ≤ −1`
since `x ≥ 1`; the `≥` direction evaluates at the corner `x* = 1`. -/
theorem valueFunction_expend_eq : Danskin.valueFunction (expendObjective embed) 1 = -1 := by
  apply le_antisymm
  · refine ciSup_le (fun x => ?_)
    rw [expendObjective_at]
    have hx : (1 : ℝ) ≤ (x : ℝ) := (Set.mem_Icc.mp x.2).1
    linarith
  · have hval : expendObjective embed 1 x_star = -1 := by rw [expendObjective_at]; rfl
    rw [← hval]
    exact le_ciSup bddAbove_expend x_star

/-- **The expenditure-minimizing bundle is unique**: The objective hits the value `−1` exactly at
the corner `x* = 1`. -/
theorem expend_eq_value_iff (x : HicksY) :
    expendObjective embed 1 x = -1 ↔ x = x_star := by
  rw [expendObjective_at]
  constructor
  · intro h
    refine Subtype.ext ?_
    change (x : ℝ) = 1
    linarith
  · intro h; subst h; rfl

/-- **The optimizer set is the singleton `{x*}`**, the hypothesis `hasGradientAt_negExpendFunction`
consumes. -/
theorem argmax_iSup_eq_singleton :
    Danskin.argmax_iSup (expendObjective embed) 1 = {x_star} := by
  ext x
  rw [Danskin.argmax_iSup, Set.mem_setOf_eq, valueFunction_expend_eq, Set.mem_singleton_iff]
  exact expend_eq_value_iff x

/-- **`hasGradientAt_negExpendFunction` (Shephard's lemma)**, anchored: The gradient of the negated
expenditure function `−e(p) = sup_x (−p·x)` at `p = 1` is `−x* = −1`. Equivalently `∇_p e = +1`,
the Hicksian demand — the documented sign. A flip would give `+1` for the negated function here. -/
theorem hasGradientAt_negExpendFunction_witness :
    HasGradientAt (negExpendFunction embed) (-1) 1 := by
  have h := hasGradientAt_negExpendFunction embed isOpen_Ioo embed_continuous (X := Set.Ioo 0 2)
    1 ⟨by norm_num, by norm_num⟩ x_star argmax_iSup_eq_singleton
  rwa [embed_x_star] at h

/-- **`negExpendFunction` evaluation**: `−e(1) = −1` (the value function at the optimal bundle),
anchoring the level alongside the gradient. -/
theorem negExpendFunction_at : negExpendFunction embed 1 = -1 :=
  valueFunction_expend_eq

end Shephard

/-! ### Roy: The calculus identity behind Roy's identity (minus sign)

This block exercises `gradient_indirectUtility_of_expenditure_chain` — the **calculus identity**
behind Roy's identity, *not* a full consumer-optimization derivation of demand. No budget set,
feasibility, or first-order condition is formalized here; `xstar`, `v`, `e` are supplied as
hand-built functions satisfying the theorem's algebraic hypotheses, and the content checked is the
**minus-sign chain-rule algebra**. We pick the globally-dual quasi-linear data so the strong
hypothesis `h_ident` of the theorem is genuinely satisfiable:

* indirect utility `v(p, w) = w − p²/2`,
* expenditure `e(p, u) = u + p²/2`  (so `e(q, v(q, w')) = w'` for *every* `q`),
* the `xstar(p, w) = p` term (the marginal cost `g′(p)` with `g(p) = p²/2`).

The chain rule then delivers Roy's identity with the **minus sign**:
`∇_p v(p, w) = −(∂v/∂w)·xstar(p, w)`. At `p₀ = 2` (any `w`) this reads `−2 = −(1)·2`: the price
gradient of indirect utility is the *negative* of the `xstar` term (since `∂v/∂w = 1`). A sign flip
would assert `+2 = (1)·2` and fail against the computed gradient `∂v/∂p = −p`. The identity is
uniform in wealth `w`; we additionally fix `w₀ = 4` to anchor one witness at a concrete `(p, w)`. -/

namespace Roy

/-- Indirect utility `v(p, w) = w − p²/2`. -/
def v : ℝ → ℝ → ℝ := fun p w => w - p ^ 2 / 2

/-- Expenditure `e(p, u) = u + p²/2`, the inverse of `v` in its second argument. -/
def e : ℝ → ℝ → ℝ := fun p u => u + p ^ 2 / 2

/-- The Shephard/`xstar` term `xstar(p, w) = p` entering the chain rule (the marginal cost `g′(p)`
with `g(p) = p²/2`). This is the function fed to the identity, not a demand derived from an
optimization problem. -/
def xstar : ℝ → ℝ → ℝ := fun p _ => p

/-- The fixed price at which the identity is anchored: `p₀ = 2`. -/
def p₀ : ℝ := 2

/-- The concrete wealth anchor `w₀ = 4` (the identity itself is uniform in `w`; `w₀` fixes one
witness at a definite `(p, w) = (2, 4)`). -/
def w₀ : ℝ := 4

/-- **Global duality `e(q, v(q, w')) = w'`** for every price `q`: The `p²/2` terms cancel. This is
the hypothesis `h_ident` and is what makes the chain witness non-vacuous (it would *fail* for the
ratio model `v = w/p`, `e = p·u` at `q = 0`). -/
theorem ident (q w' : ℝ) : e q (v q w') = w' := by
  simp only [e, v]; ring

/-- `q ↦ v(q, w)` is differentiable at every price (a polynomial). -/
theorem dv_dp (w : ℝ) : DifferentiableAt ℝ (fun q => v q w) p₀ := by
  unfold v; fun_prop

/-- `∂v/∂w = 1` at every wealth level: Indirect utility is increasing one-for-one in wealth. -/
theorem hasDerivAt_v_w (p w : ℝ) : HasDerivAt (fun w' => v p w') 1 w := by
  unfold v; simpa using (hasDerivAt_id w).sub_const (p ^ 2 / 2)

/-- `∂v/∂w = 1`: The wealth derivative of indirect utility, in `deriv` form. -/
theorem deriv_v_w (p w : ℝ) : deriv (fun w' => v p w') w = 1 :=
  (hasDerivAt_v_w p w).deriv

/-- `∂e/∂u = 1` at every utility level: Expenditure rises one-for-one with the target. -/
theorem hasDerivAt_e_u (p u : ℝ) : HasDerivAt (fun u' => e p u') 1 u := by
  unfold e; simpa using (hasDerivAt_id u).add_const (p ^ 2 / 2)

/-- `∂e/∂u = 1`: The utility derivative of expenditure, in `deriv` form. -/
theorem deriv_e_u (p u : ℝ) : deriv (fun u' => e p u') u = 1 :=
  (hasDerivAt_e_u p u).deriv

/-- `∂v/∂p = −p`: The price gradient of indirect utility (the quantity we are computing). -/
theorem hasDerivAt_v_p (w : ℝ) : HasDerivAt (fun q => v q w) (-p₀) p₀ := by
  unfold v
  have h : HasDerivAt (fun q : ℝ => q ^ 2 / 2) p₀ p₀ := by
    simpa using ((hasDerivAt_pow 2 p₀).div_const 2)
  simpa using (hasDerivAt_const p₀ w).sub h

/-- The fderiv of `q ↦ v(q, w)` at `p₀` is `toDual (−p₀)`, the dual of the price gradient. -/
theorem fderiv_v_p (w : ℝ) :
    fderiv ℝ (fun q => v q w) p₀ = (InnerProductSpace.toDual ℝ ℝ) (-p₀) := by
  rw [(hasDerivAt_v_p w).hasFDerivAt.fderiv]
  ext
  simp [InnerProductSpace.toDual_apply_apply, mul_comm]

/-- **The chain-rule decomposition `h_chain`.** The composite `q ↦ e(q, v(q, w))` is globally
constant (`= w` by `ident`), so its fderiv is `0`; the supplied Shephard-plus-continuation
expression `toDual(x*) + (∂e/∂u)·fderiv(v)` also equals `0`, namely
`toDual(p₀) + 1·toDual(−p₀) = toDual(0) = 0`. -/
theorem chain (w : ℝ) :
    HasFDerivAt (fun q => e q (v q w))
      ((InnerProductSpace.toDual ℝ ℝ) (xstar p₀ w)
        + (deriv (fun u' => e p₀ u') (v p₀ w)) • fderiv ℝ (fun q => v q w) p₀) p₀ := by
  have hconst : HasFDerivAt (fun q => e q (v q w)) (0 : ℝ →L[ℝ] ℝ) p₀ := by
    have hfun : (fun q => e q (v q w)) = fun _ => w := funext (fun q => ident q w)
    rw [hfun]; exact hasFDerivAt_const w p₀
  convert hconst using 1
  rw [deriv_e_u p₀ (v p₀ w), fderiv_v_p w, one_smul, xstar]
  -- toDual p₀ + toDual (−p₀) = toDual 0 = 0.
  rw [← map_add]
  simp

/-- **`gradient_indirectUtility_of_expenditure_chain` (Roy's identity, the minus sign)**, anchored:
At `p₀ = 2`, `w = 4` the price gradient of indirect utility is
`∇_p v = −(∂v/∂w)·x* = −(1)·x*(p₀, w)`. Combined with `xstar = p₀`, this is `−2`, the negative of
demand. -/
theorem gradient_indirectUtility_witness (w : ℝ) :
    gradient (fun q => v q w) p₀ = -(deriv (fun w' => v p₀ w') w) • xstar p₀ w :=
  gradient_indirectUtility_of_expenditure_chain v e xstar p₀ w (v p₀ w) rfl ident (dv_dp w)
    (deriv_v_w p₀ w ▸ hasDerivAt_v_w p₀ w)
    (deriv_e_u p₀ (v p₀ w) ▸ hasDerivAt_e_u p₀ (v p₀ w))
    (chain w)

/-- **The Roy gradient, evaluated**: `∇_p v(2, w) = −2 = −xstar(2, w)` (since `∂v/∂w = 1` and
`xstar(2, w) = 2`). The price gradient of indirect utility is *minus* the `xstar` term — the
documented sign. A flipped sign would give `+2` here. -/
theorem gradient_indirectUtility_eq (w : ℝ) : gradient (fun q => v q w) p₀ = -2 := by
  rw [gradient_indirectUtility_witness w, deriv_v_w p₀ w, xstar, p₀]
  simp

/-- **The Roy gradient at the concrete anchor `(p₀, w₀) = (2, 4)`**: `∇_p v(2, 4) = −2`. This pins
the witness at a definite price *and* wealth (the prose's `(2, 4)` anchor), specializing the
`w`-uniform identity to `w₀ = 4`. -/
theorem gradient_indirectUtility_at_w₀ : gradient (fun q => v q w₀) p₀ = -2 :=
  gradient_indirectUtility_eq w₀

end Roy

end EconlibTest.Optimization.Core

end
