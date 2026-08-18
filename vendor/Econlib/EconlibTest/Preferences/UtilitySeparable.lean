/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Mathlib

/-!
# Separable / Inverse Utility Non-Vacuity Checks

Compile-time semantic witnesses for the additively-separable optimization machinery
(`Separable.lean`), the differentiable-inverse machinery (`Differentiable.lean`), and quasilinear
utility (`Quasilinear.lean`). Each headline is anchored on a *concrete* utility with a
hand-computed optimum / inverse value.

Chunks exercised (3, 6 of `backlog/pref-utility-test-coverage.md`):

* **Separable decomposition over a product feasible set** (`Separable.lean`): A two-good separable
  utility with `√` (Inada) felicities and equal weights, over the *product* box
  `S = Icc 1 4 × Icc 1 4`. Because each felicity is strictly increasing, the per-good argmax is the
  upper corner `4`, so the joint argmax is the single corner `(4, 4)` (`isMaxOn_aggregate_pi_iff`,
  `argmax_aggregate_pi`). The product decomposition is genuinely *different* from the
  budget-coupled optimum already exercised in `SeparableOptimum.lean`: A product box has no shared
  constraint, so the goods decouple completely and each corner-maximizes independently.
* **Additively separable aggregate** (`AdditivelySeparableUtility.aggregate`): `∑ log` with unit
  weights, value-anchored.
* **Differentiable inverse** (`Differentiable.lean`): On the concrete strictly-monotone twice-diff
  utility `u(x) = 2x + 3` (domain `ℝ`), produce the inverse via `exists_inverse_twice_diff` and
  check it inverts at an explicit point — `u(1) = 5`, so the inverse maps `5 ↦ 1`.
* **Quasilinear** (`Quasilinear.lean`): The defining linear-transfer property
  `transfer_utility_increment` and the transfer-equivalence characterization on a concrete
  valuation `v(x) = x²`.

A hostile reviewer should agree these are genuine, direction-correct instances: The corner argmax
would move if a felicity's monotonicity were reversed, and the inverse round-trip would fail at the
numeric point if the inverse were mis-stated.
-/

noncomputable section

namespace EconlibTest.Preferences.UtilitySeparable

open Econlib.Preferences Econlib.Optimization
open Set Filter Topology

/-! ## Chunk 3a. Additively separable aggregate: `∑ log` with unit weights -/

section additivelySeparable

/-- A two-good additively separable utility: Log felicity in each good, with *asymmetric nonunit*
weights `(2, 3)`, so `aggregate (x, y) = 2·log x + 3·log y`. The asymmetry is deliberate: equal unit
weights with `log 1 = 0` would let a witness pass even if a coordinate were dropped, swapped, or the
weight ignored. -/
private def asu : AdditivelySeparableUtility (Fin 2) where
  component := fun _ => Real.log
  weight := ![2, 3]

/-- **`AdditivelySeparableUtility.aggregate`, asymmetric value anchor.** At the bundle
`(exp 1, exp 2)`, both summands are nonzero and the weights bite:
`aggregate = 2·log(e¹) + 3·log(e²) = 2·1 + 3·2 = 8`. Swapping the coordinates would give
`2·2 + 3·1 = 7`; dropping a weight would give `1 + 2 = 3` — so this anchor discriminates against the
swap / weight-drop bugs. -/
theorem asu_aggregate_at : asu.aggregate ![Real.exp 1, Real.exp 2] = 8 := by
  simp only [AdditivelySeparableUtility.aggregate, Fin.sum_univ_two, asu]
  rw [show (![Real.exp 1, Real.exp 2] : Fin 2 → ℝ) 0 = Real.exp 1 from rfl,
      show (![Real.exp 1, Real.exp 2] : Fin 2 → ℝ) 1 = Real.exp 2 from rfl,
      Real.log_exp, Real.log_exp]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

end additivelySeparable

/-! ## Chunk 3b. Separable decomposition over a product box

A two-good separable utility with `√` (Inada) felicities and *asymmetric* weights `(2, 3)`, over the
*asymmetric* product box `Icc 1 4 × Icc 1 9`. The asymmetry (different weights, different boxes,
different corner coordinates) is what makes the decomposition witnesses discriminate against
swapped-index / transposed-coordinate / wrong-factor bugs. Per-good objective `gᵢ(t) = βᵢ · √t` is
strictly increasing, so its argmax over `Icc 1 hᵢ` is the single upper corner `{hᵢ}`; the joint
argmax is therefore the *single* corner `{(4, 9)}`. -/

section separableProduct

/-- The two-good separable utility: Both goods have `√` felicity, with *asymmetric* weights `(2, 3)`
(good `0` weight `2`, good `1` weight `3`). -/
private def U : SeparableUtility (Fin 2) where
  component := fun _ => InadaUtility.sqrt
  weight := ![2, 3]

/-- The *asymmetric* product feasible box: `Icc 1 4` for good `0`, `Icc 1 9` for good `1`. -/
private def box : Fin 2 → Set ℝ := ![Icc 1 4, Icc 1 9]

/-- The corner bundle `(4, 9)` — the per-coordinate upper endpoints, which differ between goods. -/
private def corner : Fin 2 → ℝ := ![4, 9]

/-- The corner is feasible: It lies in the product box. -/
private lemma corner_mem : corner ∈ univ.pi box := by
  intro i _
  fin_cases i <;> simp [box, corner, Set.mem_Icc]

/-- The component objective unfolds to `βᵢ · √t` (the Inada `√` felicity weighted by `βᵢ`). -/
private lemma compObj_eq (i : Fin 2) (t : ℝ) :
    U.componentObjective i t = (U.weight i : ℝ) * Real.sqrt t := rfl

/-- Both Pareto weights are strictly positive (`2 > 0`, `3 > 0`). -/
private lemma weight_pos (i : Fin 2) : (0 : ℝ) < (U.weight i : ℝ) := by
  fin_cases i <;> simp [U]

/-- **`component_concaveOn`.** The weighted felicity `βᵢ · √` is concave on `(0, ∞)`. -/
theorem U_component_concave (i : Fin 2) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun c => (U.weight i : ℝ) * (U.component i).u c) :=
  U.component_concaveOn i

/-- **`component_strictConcaveOn`.** With strictly positive weight the felicity is *strictly*
concave (correct curvature direction). -/
theorem U_component_strictConcave (i : Fin 2) :
    StrictConcaveOn ℝ (Ioi (0 : ℝ)) (fun c => (U.weight i : ℝ) * (U.component i).u c) :=
  U.component_strictConcaveOn i (by fin_cases i <;> simp [U])

/-- **`positiveOrthant_convex`.** The positive orthant is convex. -/
theorem U_positiveOrthant_convex : Convex ℝ (SeparableUtility.positiveOrthant (Fin 2)) :=
  SeparableUtility.positiveOrthant_convex

/-- **`componentObjective`, nonunit-weight value anchors.** Because the weight is `≠ 1`, these
genuinely test the weight multiplication: `g₀(4) = 2·√4 = 4` and `g₁(9) = 3·√9 = 9`. A definition
`componentObjective i t := (U.component i).u t` that *dropped* the weight would give `2` and `3`
instead. -/
theorem U_componentObjective_0 : U.componentObjective 0 4 = 4 := by
  rw [compObj_eq]
  change ((![2, 3] : Fin 2 → NNReal) 0 : ℝ) * Real.sqrt 4 = 4
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [Matrix.cons_val_zero]

theorem U_componentObjective_1 : U.componentObjective 1 9 = 9 := by
  rw [compObj_eq]
  change ((![2, 3] : Fin 2 → NNReal) 1 : ℝ) * Real.sqrt 9 = 9
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [Matrix.cons_val_one]

/-- **`aggregate_eq_sum_componentObjective`, asymmetric value anchor.** The aggregate is the
coordinate sum of the per-good objectives; at the corner, `aggregate (4, 9) = 2·√4 + 3·√9 =
4 + 9 = 13`. The two summands differ (`4 ≠ 9`), so a swapped-coordinate aggregate would land on a
different number. -/
theorem U_aggregate_eq_sum : U.aggregate corner = 13 := by
  rw [U.aggregate_eq_sum_componentObjective]
  simp only [Fin.sum_univ_two, corner]
  rw [show (![4, 9] : Fin 2 → ℝ) 0 = 4 from rfl, show (![4, 9] : Fin 2 → ℝ) 1 = 9 from rfl,
    U_componentObjective_0, U_componentObjective_1]
  norm_num

/-- **Per-good argmax is the *single* upper corner.** For `gᵢ(t) = βᵢ √t` strictly increasing on the
positives, its set of maximizers over `Icc lo hi` (with `0 < lo ≤ hi`) is exactly `{hi}`: membership
is monotonicity, and uniqueness follows because any maximizer `s` has `√s = √hi`, hence `s = hi` by
injectivity of `√` on the nonnegatives. This is the per-good *uniqueness* the joint singleton below
rests on. -/
private lemma argmax_box_singleton (i : Fin 2) (lo hi : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hbox : box i = Icc lo hi) :
    argmax (U.componentObjective i) (box i) = {hi} := by
  ext s
  simp only [argmax, Set.mem_setOf_eq, Set.mem_singleton_iff, isMaxOn_iff, hbox]
  have hwp := weight_pos i
  constructor
  · rintro ⟨hs_mem, hmax⟩
    have hs : s ∈ Icc lo hi := hs_mem
    have hge := hmax hi ⟨hle, le_refl _⟩
    rw [compObj_eq, compObj_eq] at hge
    have hsle : Real.sqrt s ≤ Real.sqrt hi := Real.sqrt_le_sqrt hs.2
    have hsge : Real.sqrt hi ≤ Real.sqrt s := le_of_mul_le_mul_left hge hwp
    have heq : Real.sqrt s = Real.sqrt hi := le_antisymm hsle hsge
    exact (Real.sqrt_inj (le_trans hlo.le hs.1) (le_trans hlo.le hle)).mp heq
  · rintro rfl
    refine ⟨⟨hle, le_refl _⟩, ?_⟩
    intro t ht
    rw [compObj_eq, compObj_eq]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2) hwp.le

/-- Good `0`'s per-good argmax over `Icc 1 4` is the singleton `{4}`. -/
theorem U_argmax_0 : argmax (U.componentObjective 0) (box 0) = {4} :=
  argmax_box_singleton 0 1 4 (by norm_num) (by norm_num) rfl

/-- Good `1`'s per-good argmax over `Icc 1 9` is the singleton `{9}`. -/
theorem U_argmax_1 : argmax (U.componentObjective 1) (box 1) = {9} :=
  argmax_box_singleton 1 1 9 (by norm_num) (by norm_num) rfl

/-- The per-good `IsMaxOn` facts, read off the singleton argmaxes (membership in `{corner i}`). -/
private lemma U_isMaxOn_component (i : Fin 2) :
    IsMaxOn (U.componentObjective i) (box i) (corner i) := by
  fin_cases i
  · have : (4 : ℝ) ∈ argmax (U.componentObjective 0) (box 0) := by rw [U_argmax_0]; rfl
    exact this.2
  · have : (9 : ℝ) ∈ argmax (U.componentObjective 1) (box 1) := by rw [U_argmax_1]; rfl
    exact this.2

/-- **`isMaxOn_aggregate_pi_iff`, forward decomposition.** Over the product box, the corner jointly
maximizes the separable aggregate, *because* it maximizes each per-good objective. This is the
separable decomposition in action. -/
theorem U_corner_isMaxOn : IsMaxOn U.aggregate (univ.pi box) corner :=
  (U.isMaxOn_aggregate_pi_iff corner_mem).mpr U_isMaxOn_component

/-- Conversely, joint optimality of the corner forces each coordinate optimality (the `mp`
direction of the iff). -/
theorem U_corner_componentMax (i : Fin 2) : IsMaxOn (U.componentObjective i) (box i) (corner i) :=
  (U.isMaxOn_aggregate_pi_iff corner_mem).mp U_corner_isMaxOn i

/-- **`argmax_aggregate_pi`, the headline decomposition — as a *uniqueness* statement.** The joint
argmax of the separable aggregate over the product box is the **single** corner `{(4, 9)}` — not
just "the corner is *a* maximizer". The proof transports `argmax_aggregate_pi` (joint argmax =
product of per-good argmaxes) and the two per-good singletons `U_argmax_0 = {4}`,
`U_argmax_1 = {9}`, then identifies `univ.pi {4} × {9}` with the single point `(4, 9)`. This rules
out *extra*
maximizers, the gap the original membership-only witness left open. -/
theorem U_argmax_joint : argmax U.aggregate (univ.pi box) = {corner} := by
  rw [U.argmax_aggregate_pi,
    show (fun i => argmax (U.componentObjective i) (box i)) = (fun i => {corner i}) from by
      funext i; fin_cases i
      · exact U_argmax_0
      · exact U_argmax_1]
  ext c
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_singleton_iff]
  exact ⟨fun h => funext fun i => h i, fun h i => by rw [h]⟩

/-- **The corner is in the joint argmax** (the membership corollary of the singleton above). -/
theorem U_corner_in_argmax : corner ∈ argmax U.aggregate (univ.pi box) := by
  rw [U_argmax_joint]; rfl

/-- **`argmax_aggregate_pi`, product decomposition.** Transporting the corner through
`argmax_aggregate_pi`, it lands coordinatewise in each per-good argmax — the formal content of "the
joint optimum is the product of the independent per-good optima". -/
theorem U_corner_in_pi_argmax :
    corner ∈ univ.pi (fun i => argmax (U.componentObjective i) (box i)) := by
  rw [← U.argmax_aggregate_pi]
  exact U_corner_in_argmax

/-- Reading off one coordinate of the product-of-argmaxes: The corner's first good `4` is in the
per-good argmax of `g₀ = 2√` over `Icc 1 4`. -/
theorem U_corner_coord_argmax :
    corner 0 ∈ argmax (U.componentObjective 0) (box 0) :=
  U_corner_in_pi_argmax 0 (mem_univ 0)

/-- **`SeparableUtility.mem_budget`, positive direction.** The bundle `(1, 1)` lies in the
unit-price budget set at wealth `m = 3`: It is strictly positive and `1 + 1 = 2 ≤ 3`. -/
theorem U_mem_budget : (![1, 1] : Fin 2 → ℝ) ∈ U.budget 3 := by
  rw [SeparableUtility.mem_budget]
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> norm_num
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- **`mem_budget`, negative direction (affordability).** The bundle `(2, 2)` is *not* affordable at
wealth `3`: `2 + 2 = 4 > 3`. Catches a flipped budget `↔` on the expenditure constraint. -/
theorem U_not_mem_budget : (![2, 2] : Fin 2 → ℝ) ∉ U.budget 3 := by
  rw [SeparableUtility.mem_budget]
  push Not
  intro _
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **`mem_budget`, negative direction (strict-positivity boundary).** The bundle `(0, 1)` is
*affordable* (`0 + 1 = 1 ≤ 3`) yet *not* in the budget set, because the first coordinate is `0`, not
strictly positive. This guards the interiority half of `budget`: a definition using `0 ≤ cᵢ`, or
dropping positivity entirely, would wrongly admit `(0, 1)`. -/
theorem U_not_mem_budget_boundary : (![0, 1] : Fin 2 → ℝ) ∉ U.budget 3 := by
  rw [SeparableUtility.mem_budget]
  rintro ⟨hpos, -⟩
  have := hpos 0
  simp at this

/-- **`SeparableUtility.budget_convex`.** The unit-price budget set at wealth `3` is convex. -/
theorem U_budget_convex : Convex ℝ (U.budget 3) := U.budget_convex 3

/-- Two feasible bundles at wealth `4`: `(1, 1)` (cost `2`) and `(2, 1)` (cost `3`). -/
private def b1 : Fin 2 → ℝ := ![1, 1]
private def b2 : Fin 2 → ℝ := ![2, 1]

private lemma b1_mem : b1 ∈ U.budget 4 := by
  rw [SeparableUtility.mem_budget]
  exact ⟨fun i => by fin_cases i <;> simp [b1], by simp [b1, Fin.sum_univ_two]; norm_num⟩
private lemma b2_mem : b2 ∈ U.budget 4 := by
  rw [SeparableUtility.mem_budget]
  exact ⟨fun i => by fin_cases i <;> simp [b2], by simp [b2, Fin.sum_univ_two]; norm_num⟩

/-- **Concrete convex-combination membership (non-vacuity for `budget_convex`).** The `1/2`-midpoint
of the two feasible bundles `(1,1)` and `(2,1)` lies in the budget set at wealth `4` — exhibited
via `U.budget_convex` applied to the two memberships with weights `1/2, 1/2`. This is a genuine
nonempty convex-combination witness, not a smoke test of the (vacuously true for empty sets)
convexity lemma. -/
theorem U_budget_midpoint_mem :
    (((1 : ℝ) / 2) • b1 + ((1 : ℝ) / 2) • b2) ∈ U.budget 4 :=
  U.budget_convex 4 b1_mem b2_mem (by norm_num) (by norm_num) (by norm_num)

/-- The midpoint above is the concrete interior bundle `(3/2, 1)` — both coordinates positive, total
cost `5/2 ≤ 4`. -/
theorem U_budget_midpoint_value :
    (((1 : ℝ) / 2) • b1 + ((1 : ℝ) / 2) • b2) = ![3 / 2, 1] := by
  funext i; fin_cases i <;> simp [b1, b2] <;> norm_num

end separableProduct

/-! ## Chunk 3c. Two-good aggregate decomposition -/

section twoGood

/-- A genuine `TwoGoodUtility` (over `Good = nondurable | durable`): Both components `√`, weights
`(2, 3)`. -/
private def TG : TwoGoodUtility where
  component := fun _ => InadaUtility.sqrt
  weight := fun g => match g with
    | Good.nondurable => 2
    | Good.durable => 3

/-- **`TwoGoodUtility.aggregateCK_eq`, value anchor.** The aggregate decomposes as
`β_c · √c + β_k · √k`; at `(c, k) = (4, 9)` it is `2·√4 + 3·√9 = 2·2 + 3·3 = 13`. -/
theorem TG_aggregateCK_at : TG.aggregateCK 4 9 = 13 := by
  rw [TG.aggregateCK_eq]
  change (2 : ℝ) * Real.sqrt 4 + (3 : ℝ) * Real.sqrt 9 = 13
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
  norm_num

end twoGood

/-! ## Chunk 6a. Differentiable / inverse machinery

A concrete strictly-monotone twice-differentiable utility `u(x) = 2x + 3` on `domain = ℝ`, with
`u' ≡ 2 > 0` and `u'' ≡ 0`. We produce its inverse via `exists_inverse_twice_diff` and check it
inverts at an explicit point: `u(1) = 5`, so the inverse maps `5 ↦ 1`. -/

section differentiableInverse

/-- The affine utility `u(x) = 2x + 3`, `u' ≡ 2`, `u'' ≡ 0`, on the whole real line. -/
private def affine : TwiceDiffUtility where
  u := fun x => 2 * x + 3
  u' := fun _ => 2
  u'' := fun _ => 0
  domain := univ
  domain_open := isOpen_univ
  domain_convex := convex_univ
  domain_nonempty := univ_nonempty
  has_deriv := fun x _ => by
    simpa using ((hasDerivAt_id x).const_mul 2).add_const 3
  has_second_deriv := fun _ _ => hasDerivAt_const _ _
  u'_pos := fun _ _ => by norm_num

/-- `u(1) = 2·1 + 3 = 5`. -/
private lemma affine_u_one : affine.u 1 = 5 := by change (2 : ℝ) * 1 + 3 = 5; norm_num

/-- `1` is in the domain (`= univ`). -/
private lemma affine_one_mem : (1 : ℝ) ∈ affine.domain := mem_univ 1

/-- **`continuousOn_u`.** The affine utility is continuous on its domain. -/
theorem affine_continuousOn : ContinuousOn affine.u affine.domain := affine.continuousOn_u

/-- **`strictMonoOn_u`.** The affine utility is strictly monotone on its domain (derivative
`2 > 0`). -/
theorem affine_strictMonoOn : StrictMonoOn affine.u affine.domain := affine.strictMonoOn_u

/-- **`image_domain_open`.** The image `u '' ℝ` is open. -/
theorem affine_image_open : IsOpen (affine.u '' affine.domain) := affine.image_domain_open

/-- **`image_domain_convex`.** The image is convex. -/
theorem affine_image_convex : Convex ℝ (affine.u '' affine.domain) := affine.image_domain_convex

/-- **`image_domain_nonempty`.** The image is nonempty. -/
theorem affine_image_nonempty : (affine.u '' affine.domain).Nonempty := affine.image_domain_nonempty

/-- `5 = u(1)` lies in the image of the domain. -/
private lemma affine_five_mem : (5 : ℝ) ∈ affine.u '' affine.domain :=
  ⟨1, affine_one_mem, affine_u_one⟩

/-- The affine utility is surjective, so its image is all of `ℝ`. Used to show the inverse identity
holds on a *neighborhood* of `5` (needed to differentiate `u ∘ u_inv = id`). -/
private lemma affine_image_univ : affine.u '' affine.domain = univ := by
  apply eq_univ_of_forall
  intro y
  exact ⟨(y - 3) / 2, mem_univ _, by change 2 * ((y - 3) / 2) + 3 = y; ring⟩

/-- **`StrictMonoOn.isOpen_image` (the generic open-map lemma).** A
continuous strictly-monotone function on an open set is an open map; here the image of `ℝ` under
the affine utility is open. -/
theorem affine_open_map :
    IsOpen (affine.u '' affine.domain) :=
  StrictMonoOn.isOpen_image affine.domain_open
    affine.continuousOn_u affine.strictMonoOn_u

/-- **`StrictMonoOn.continuousAt_invFunOn`.** The pointwise inverse `invFunOn u ℝ` is continuous at
`5 ∈ u '' ℝ`. -/
theorem affine_continuousAt_invFunOn :
    ContinuousAt (Function.invFunOn affine.u affine.domain) 5 :=
  StrictMonoOn.continuousAt_invFunOn affine.domain_open affine.continuousOn_u affine.strictMonoOn_u
    affine_five_mem

/-- **`exists_inverse`, round-trip anchor.** The first-order inverse machinery yields a left
inverse `u_inv ∘ u = id` on the domain; applied at `x = 1` (with `u(1) = 5`) it gives
`u_inv 5 = 1`. -/
theorem affine_exists_inverse_at :
    ∃ u_inv : ℝ → ℝ, u_inv 5 = 1 ∧ (∀ y ∈ affine.u '' affine.domain, affine.u (u_inv y) = y) := by
  obtain ⟨u_inv, h_left, h_right, _h_deriv⟩ := affine.exists_inverse
  refine ⟨u_inv, ?_, h_right⟩
  -- `u_inv (u 1) = 1` and `u 1 = 5`, so `u_inv 5 = 1`.
  have := h_left 1 affine_one_mem
  rwa [affine_u_one] at this

/-- **`exists_inverse_twice_diff`, full round-trip with derivative anchors.** The
twice-differentiable inverse machinery produces `u_inv` together with its first and second
derivatives; this witness *consumes all of them*:

* `u_inv 5 = 1` (left inverse `h_left`, with `u(1) = 5`);
* `u(u_inv 5) = 5` — the **right** inverse, applied explicitly via `h_right 5`;
* `HasDerivAt u_inv (1/2) 5` — the first-derivative value is pinned to `1/2` by the inverse-function
  identity `(u ∘ u_inv)' (5) = 2 · u_inv'(5) = 1` (chain rule against the surjective `u`);
* `HasDerivAt u_inv' (u_inv'' 5) 5` and `u_inv'' 5 = 0` — the second derivative vanishes because
  `u_inv'` is locally constant `1/2` (since `u' ≡ 2`), so its derivative is `0`.

A wrong first-derivative formula, a wrong second derivative, or a bad right-inverse conjunct would
all be caught here. -/
theorem affine_exists_inverse_twice_diff_at :
    ∃ (u_inv u_inv' u_inv'' : ℝ → ℝ),
      u_inv 5 = 1 ∧ affine.u (u_inv 5) = 5 ∧
        HasDerivAt u_inv (1 / 2) 5 ∧
        HasDerivAt u_inv' (u_inv'' 5) 5 ∧ u_inv'' 5 = 0 := by
  obtain ⟨u_inv, u_inv', u_inv'', h_left, h_right, h1, h2⟩ := affine.exists_inverse_twice_diff
  have hinv5 : u_inv 5 = 1 := by have := h_left 1 affine_one_mem; rwa [affine_u_one] at this
  -- right inverse, applied explicitly.
  have hright5 : affine.u (u_inv 5) = 5 := h_right 5 affine_five_mem
  -- The inverse-function identity forces `u_inv' y = 1/2` for every `y` in the image.
  have hu_inv'_eq : ∀ y ∈ affine.u '' affine.domain, u_inv' y = 1 / 2 := by
    intro y hy
    have hderiv : HasDerivAt u_inv (u_inv' y) y := h1 y hy
    have hu_at : HasDerivAt affine.u 2 (u_inv y) := by
      simpa using affine.has_deriv (u_inv y) (mem_univ _)
    have hcomp : HasDerivAt (fun z => affine.u (u_inv z)) (2 * u_inv' y) y := hu_at.comp y hderiv
    have hev : (fun z => affine.u (u_inv z)) =ᶠ[nhds y] id := by
      filter_upwards [affine_image_univ ▸ isOpen_univ.mem_nhds (mem_univ y)] with z hz
      exact h_right z (affine_image_univ ▸ hz)
    have hid : HasDerivAt (fun z => affine.u (u_inv z)) 1 y :=
      (hasDerivAt_id y).congr_of_eventuallyEq hev
    have : 2 * u_inv' y = 1 := hcomp.unique hid
    linarith
  -- First-derivative anchor at `5`.
  have hderiv5 : HasDerivAt u_inv (1 / 2) 5 := (hu_inv'_eq 5 affine_five_mem) ▸ h1 5 affine_five_mem
  -- Second-derivative anchor: `u_inv'` is eventually `1/2`, so its derivative at `5` is `0`.
  have h2deriv : HasDerivAt u_inv' (u_inv'' 5) 5 := h2 5 affine_five_mem
  have hev' : u_inv' =ᶠ[nhds 5] (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [affine_image_univ ▸ isOpen_univ.mem_nhds (mem_univ (5 : ℝ))] with z hz
    exact hu_inv'_eq z (affine_image_univ ▸ hz)
  have hconst : HasDerivAt u_inv' 0 5 :=
    (hasDerivAt_const 5 (1 / 2 : ℝ)).congr_of_eventuallyEq hev'
  have hsd0 : u_inv'' 5 = 0 := h2deriv.unique hconst
  exact ⟨u_inv, u_inv', u_inv'', hinv5, hright5, hderiv5, h2deriv, hsd0⟩

end differentiableInverse

/-! ## Chunk 6b. Quasilinear utility

A concrete quasilinear utility with valuation `v(x) = x²`: `u(x, m) = x² + m`. We exercise the
defining linear-transfer property (`transfer_utility_increment`) and the transfer-equivalence
characterization (`transfer_equiv`).

**Semantic note.** `transfer_utility_increment` states `u(x, m + Δ) − u(x, m) = Δ`: The *utility
increment* from a transfer equals the transfer, independent of the consumption level `x`. This is
the linear-transfer (no-wealth-effect-on-marginal-utility) property that *underlies* the textbook
"no income effect on the non-numeraire demand" — it is the utility-level statement, not a demand
function statement (the file has no demand object). -/

section quasilinear

/-- The quasilinear utility with valuation `v(x) = x²`, so `u(x, m) = x² + m`. -/
private def Q : QuasilinearUtility ℝ where
  v := fun x => x ^ 2

/-- **`u_def`, value anchor.** `u(3, 5) = 3² + 5 = 14`. -/
theorem Q_u_def : Q.u 3 5 = 14 := by
  rw [Q.u_def]
  change (3 : ℝ) ^ 2 + 5 = 14
  norm_num

/-- **`transfer_utility_increment`, the defining property.** The utility increment from a
transfer `Δ` equals `Δ`, *regardless* of the consumption level `x` — here checked at
`x = 3, m = 5, Δ = 7`: `u(3, 12) − u(3, 5) = 7`. This level-independence is the utility-level
statement underlying the absence of an income effect. -/
theorem Q_no_income_effect (x m Δ : ℝ) : Q.u x (m + Δ) - Q.u x m = Δ :=
  Q.transfer_utility_increment x m Δ

/-- Concrete anchor of the no-income-effect identity. -/
theorem Q_no_income_effect_at : Q.u 3 (5 + 7) - Q.u 3 5 = 7 := Q_no_income_effect 3 5 7

/-- **`transfer_equiv`.** Two `(outcome, transfer)` pairs are indifferent iff the
valuation difference is offset by the opposite transfer difference. Here `(1, m₁) ~ (2, m₂)` iff
`v(1) − v(2) = m₂ − m₁`, i.e. `1 − 4 = m₂ − m₁`, i.e. `m₂ − m₁ = -3`. -/
theorem Q_transfer_equiv (m₁ m₂ : ℝ) :
    Q.u 1 m₁ = Q.u 2 m₂ ↔ Q.v 1 - Q.v 2 = m₂ - m₁ :=
  Q.transfer_equiv 1 2 m₁ m₂

/-- Value anchor for transfer equivalence, **`.mpr` direction** (valuation offset ⇒ utility
equality): `(1, 0) ~ (2, -3)` since `v(1) − v(2) = 1 − 4 = -3 = (-3) − 0`. -/
theorem Q_transfer_equiv_at : Q.u 1 0 = Q.u 2 (-3) := by
  rw [Q_transfer_equiv]
  change (1 : ℝ) ^ 2 - 2 ^ 2 = -3 - 0
  norm_num

/-- Transfer equivalence, **`.mp` direction** (utility equality ⇒ valuation offset): from the
indifference `Q.u 1 0 = Q.u 2 (-3)` recover the valuation/transfer relation
`v(1) − v(2) = (-3) − 0`. This exercises the reverse implication the value anchor above does not. -/
theorem Q_transfer_equiv_reverse : Q.v 1 - Q.v 2 = (-3) - 0 :=
  (Q_transfer_equiv 0 (-3)).mp Q_transfer_equiv_at

/-- **Negative transfer-equivalence anchor.** Without the compensating transfer the two pairs are
*not* indifferent: `(1, 0) ≁ (2, 0)`, because `v(1) − v(2) = 1 − 4 = -3 ≠ 0 = 0 − 0`. This guards
against a `transfer_equiv` that ignored the transfer difference. -/
theorem Q_not_transfer_equiv : Q.u 1 0 ≠ Q.u 2 0 := by
  rw [Ne, Q_transfer_equiv]
  change ¬ ((1 : ℝ) ^ 2 - 2 ^ 2 = 0 - 0)
  norm_num

end quasilinear

end EconlibTest.Preferences.UtilitySeparable

end
