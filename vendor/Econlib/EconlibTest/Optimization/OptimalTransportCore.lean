/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Optimal-transport core non-vacuity witnesses (KR distance, transport cost, couplings)

Compile-time semantic witnesses for the `Econlib.Optimization.OptimalTransport` core (`Coupling`,
`TransportCost`, `KantorovichRubinstein`).  Every abstract Kantorovich–Rubinstein / coupling
statement is forced through real numbers on **concrete diracs over the compact metric space**
`[0,1]` (the subtype `↥(Set.Icc (0:ℝ) 1)`), so the metric axioms, the cost-vs-distance bound, the
coupling marginal convention, and attainment all run on actual data rather than only an abstract
hypothesis.

The hand-computation that anchors every numeric claim:

* `δ₀ = dirac 0`, `δ₁ = dirac 1` on `[0,1]`, with `dist 0 1 = 1`.
* The **only** coupling of two diracs is the product `δ₀ ⊗ δ₁ = δ_(0,1)`, whose `dist`-cost is
  `dist 0 1 = 1`.  Hence the primal `krTransportCost δ₀ δ₁ ≤ 1`.
* The 1-Lipschitz potential `φ(x) = -x` gives `expect δ₀ φ - expect δ₁ φ = 0 - (-1) = 1`, so the
  dual `krDist δ₀ δ₁ ≥ 1`.
* Squeezing with the easy duality `krDist ≤ krTransportCost` forces both to the value `1`:
  `krDist δ₀ δ₁ = krTransportCost δ₀ δ₁ = 1`.

## What each block catches

* **Metric axioms** — a vacuous metric (`krDist δ₀ δ₁` is *strictly positive*, `= 1`, not `0`), a
  reflexivity/symmetry/triangle slip.  Anchored on a **nonzero** distance.
* **Cost vs distance** — a primal/dual inequality flip.  `krDist_le_krTransportCost` is checked in
  the correct direction (dual `≤` primal), and the duality gap is verified to be **zero** at the
  optimum.
* **Coupling marginals** — an fst/snd marginal swap.  The product coupling of the *distinct* laws
  `δ₀` (first factor) and `δ₁` (second factor) has fst-marginal `δ₀` and snd-marginal `δ₁`; a swap
  would put `δ₁` first.
* **Attainment** — a merely-bounded (non-attained) infimum.  `exists_optimal_coupling` produces an
  actual minimizing coupling whose `dist`-cost *equals* the primal infimum `krTransportCost δ₀ δ₁`
  (recorded against `krTransportCost`/`krDist`, not just `= 1`, so optimality is genuine).
* **`krTransportCost_triangle` argument order** — the via-point is the *middle* argument
  (`triangle μ ν ξ : cost μ ξ ≤ cost μ ν + cost ν ξ`); a transposed call is rejected by the
  elaborator here.
-/

noncomputable section

namespace EconlibTest.Optimization.OptimalTransportCore

open MeasureTheory Set BoundedContinuousFunction
open Econlib.Probability Econlib.Probability.ProbDist
open Econlib.Optimization.OptimalTransport

/-! ## The concrete compact metric carrier and its laws

`I01 = ↥[0,1]` is a compact, second-countable, Hausdorff, Borel metric space — exactly the
instance bundle the KR core requires.  `δ₀, δ₁, δ_½` are diracs at `0, 1, ½`. -/

/-- The unit interval `[0,1]` as a compact metric space (the KR carrier). -/
private abbrev I01 := (Set.Icc (0 : ℝ) 1)

/-- The endpoint `0 ∈ [0,1]`. -/
private def pt0 : I01 := ⟨0, by norm_num⟩

/-- The endpoint `1 ∈ [0,1]`. -/
private def pt1 : I01 := ⟨1, by norm_num⟩

/-- The midpoint `½ ∈ [0,1]` (an intermediate via-point for the triangle inequalities). -/
private def pthalf : I01 := ⟨1 / 2, by norm_num⟩

/-- The dirac `δ₀` at `0`. -/
private def d0 : ProbDist I01 := dirac pt0

/-- The dirac `δ₁` at `1`. -/
private def d1 : ProbDist I01 := dirac pt1

/-- The dirac `δ_½` at `½`. -/
private def dh : ProbDist I01 := dirac pthalf

/-- The distance between the two endpoints is `1` — the geometric anchor of every numeric claim. -/
private theorem dist_pt0_pt1 : dist pt0 pt1 = 1 := by
  rw [Subtype.dist_eq]; simp [pt0, pt1, Real.dist_eq]

/-- Every distance on `[0,1]` is bounded by the diameter `1` (a uniform cost bound, used to apply
the bounded-cost transport lemmas with `C = 1`). -/
private theorem dist_le_one (x y : I01) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq, Real.dist_eq]
  have hx := x.2; have hy := y.2
  simp only [Set.mem_Icc] at hx hy
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **The two laws are distinct.**  Separated by the coordinate test
`expect δ₀ id = 0 ≠ 1 = expect δ₁ id`.  This is the precondition that makes `krDist δ₀ δ₁ > 0` a
genuine separation rather than a vacuous `0 ≤ 0`. -/
private theorem d0_ne_d1 : d0 ≠ d1 := by
  intro h
  have hd : expect d0 (fun x : I01 => (x : ℝ)) = expect d1 (fun x : I01 => (x : ℝ)) := by rw [h]
  rw [d0, d1, expect_dirac, expect_dirac] at hd
  simp only [pt0, pt1] at hd
  norm_num at hd

/-! ## Block 1: The metric axioms on a nonzero anchor (`KantorovichRubinstein.lean`)

`krDist` is forced to be a genuine metric: Reflexive (`= 0` on the diagonal), nonnegative,
symmetric, triangular — and, crucially, **strictly positive** (`= 1`) between the *distinct* laws
`δ₀, δ₁`. -/

/-- **Reflexivity** (`krDist_self`): The KR distance from a law to itself is `0`. -/
private theorem krDist_self_witness : krDist d0 d0 = 0 := krDist_self d0

/-- **Nonnegativity** (`krDist_nonneg`). -/
private theorem krDist_nonneg_witness : (0 : ℝ) ≤ krDist d0 d1 := krDist_nonneg d0 d1

/-- **Symmetry** (`krDist_comm`): `krDist δ₀ δ₁ = krDist δ₁ δ₀`. -/
private theorem krDist_comm_witness : krDist d0 d1 = krDist d1 d0 := krDist_comm d0 d1

/-- **Triangle inequality** (`krDist_triangle`) routed through the midpoint `δ_½`. -/
private theorem krDist_triangle_witness :
    krDist d0 d1 ≤ krDist d0 dh + krDist dh d1 := krDist_triangle d0 d1 dh

/-! ## Block 2: Cost-vs-distance and strong duality at value `1`

The headline anchor: `krDist δ₀ δ₁ = krTransportCost δ₀ δ₁ = 1`, with both the dual lower bound
and the primal upper bound exhibited explicitly.  This catches a primal/dual inequality flip and a
vacuous metric in one shot. -/

/-- `δ₀ ⊗ δ₁ = δ_(0,1)` at the measure level: the *product* coupling of two diracs is the dirac on
the product point. (This identifies the product coupling specifically; it does not by itself assert
that it is the *only* coupling — the diracs leave no other choice, but that uniqueness is not what
is
proved here.) -/
private theorem prod_d0_d1 : (prod d0 d1).toMeasure = Measure.dirac (pt0, pt1) := by
  change (d0.toMeasure).prod (d1.toMeasure) = _
  rw [d0, d1, dirac_toMeasure, dirac_toMeasure]
  exact Measure.dirac_prod_dirac

/-- The `dist`-cost of the product coupling is `dist 0 1 = 1`. -/
private theorem cost_prod : ∫ z, dist z.1 z.2 ∂(prod d0 d1).toMeasure = 1 := by
  rw [prod_d0_d1, MeasureTheory.integral_dirac]
  exact dist_pt0_pt1

/-- The optimal Lipschitz potential `φ(x) = -x` (witnessing the dual). -/
private def phiNeg : I01 → ℝ := fun x => -(x : ℝ)

/-- `φ(x) = -x` is `1`-Lipschitz (the dual feasibility certificate). -/
private theorem phiNeg_lip : LipschitzWith 1 phiNeg := by
  intro x y
  simp only [phiNeg, edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [show |(-(x : ℝ)) - (-(y : ℝ))| = |(x : ℝ) - (y : ℝ)| by
    rw [show (-(x : ℝ)) - (-(y : ℝ)) = -((x : ℝ) - (y : ℝ)) by ring, abs_neg]]
  simp

/-- **Per-coupling Lipschitz bound** (`lipschitz_expect_sub_le_integral_dist`): On the product
coupling, the potential difference `expect δ₀ φ - expect δ₁ φ = 1` is bounded by the coupling's
`dist`-cost `1`.  This is the per-coupling form of the easy duality direction. -/
private theorem lipschitz_expect_sub_le_integral_dist_witness :
    expect d0 phiNeg - expect d1 phiNeg ≤ ∫ z, dist z.1 z.2 ∂(prod d0 d1).toMeasure :=
  lipschitz_expect_sub_le_integral_dist (prod_mem_couplings d0 d1) phiNeg_lip

/-- **Dual lower bound**: `krDist δ₀ δ₁ ≥ 1`, exhibited by the potential `φ(x) = -x`.  The set
defining the KR supremum contains the value `expect δ₀ φ - expect δ₁ φ = 1`. -/
private theorem kr_ge_one : (1 : ℝ) ≤ krDist d0 d1 := by
  have h : (1 : ℝ) = expect d0 phiNeg - expect d1 phiNeg := by
    rw [d0, d1, expect_dirac, expect_dirac]; simp [phiNeg, pt0, pt1]
  rw [h]
  exact le_csSup (bddAbove_krDist_setOf d0 d1) ⟨phiNeg, phiNeg_lip, rfl⟩

/-- **Primal upper bound** (`transportCost_le_integral_of_bdd`): `krTransportCost δ₀ δ₁ ≤ 1`,
exhibited by the product coupling whose cost is `1`. -/
private theorem krtc_le_one : krTransportCost d0 d1 ≤ 1 := by
  have hbd : krTransportCost d0 d1 ≤ ∫ z, dist z.1 z.2 ∂(prod d0 d1).toMeasure :=
    transportCost_le_integral_of_bdd continuous_dist.measurable d0 d1
      (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
      (fun z => dist_le_one z.1 z.2) (prod_mem_couplings d0 d1)
  rw [cost_prod] at hbd; exact hbd

/-- **Easy duality** (`krDist_le_krTransportCost`): The Lipschitz-sup (dual) form is bounded by the
coupling-inf (primal) form — in the correct direction `dual ≤ primal`.  A flip would put the
infimum below the supremum. -/
private theorem krDist_le_krTransportCost_witness :
    krDist d0 d1 ≤ krTransportCost d0 d1 := krDist_le_krTransportCost d0 d1

/-- **Strong duality, value `1`** (no gap): `krDist δ₀ δ₁ = 1`.  The dual `≥ 1` and the chain
`krDist ≤ krTransportCost ≤ 1` squeeze the distance to exactly `1`.  This is the *zero-gap*
verification: The dual sup equals the primal inf equals the hand-computed `1`. -/
private theorem krDist_eq_one : krDist d0 d1 = 1 :=
  le_antisymm (le_trans (krDist_le_krTransportCost d0 d1) krtc_le_one) kr_ge_one

/-- **Primal value `1`**: `krTransportCost δ₀ δ₁ = 1`, the transport-cost value between the two
Diracs.  This theorem proves only the value equality (not uniqueness of an optimal coupling).
Together with `krDist_eq_one` it confirms the duality gap is **zero**, not merely
`krDist ≤ krTransportCost`. -/
private theorem krTransportCost_eq_one : krTransportCost d0 d1 = 1 :=
  le_antisymm krtc_le_one (le_trans kr_ge_one (krDist_le_krTransportCost d0 d1))

/-- **The metric separates the distinct laws**: `0 < krDist δ₀ δ₁` (`= 1`), so `krDist` is *not*
vacuous.  This is the negative check the work item demands — a metric that returned `0` between
distinct laws would fail here. -/
private theorem krDist_pos_of_distinct : 0 < krDist d0 d1 := by
  rw [krDist_eq_one]; norm_num

/-! ## Block 3: The transport-cost form (`TransportCost.lean`) and attainment -/

/-- `couplingIntegrals` for the `dist` cost is **nonempty** (witnessed by the product coupling). -/
private theorem couplingIntegrals_nonempty_witness :
    (couplingIntegrals (fun p : I01 × I01 => dist p.1 p.2) d0 d1).Nonempty :=
  couplingIntegrals_nonempty _ d0 d1

/-- `couplingIntegrals` is **bounded below** under the uniform cost bound `dist ≤ 1`
(`couplingIntegrals_bddBelow_of_bdd`); this is what makes `transportCost`'s `sInf` non-junk. -/
private theorem couplingIntegrals_bddBelow_witness :
    BddBelow (couplingIntegrals (fun p : I01 × I01 => dist p.1 p.2) d0 d1) :=
  couplingIntegrals_bddBelow_of_bdd continuous_dist.measurable d0 d1
    (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
    (fun z => dist_le_one z.1 z.2)

/-- The `dist` cost on `[0,1]²` as a bounded continuous function (the argument the existence /
continuity lemmas consume). -/
private def distBCF : (I01 × I01) →ᵇ ℝ := mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩

/-- **Continuity of the coupling integral** (`continuous_integral_coupling`): `π ↦ ∫ dist dπ` is
weak-* continuous on `ProbDist ([0,1]²)`.  This is the compactness-theorem input behind
attainment. -/
private theorem continuous_integral_coupling_witness :
    Continuous (fun π : ProbDist (I01 × I01) => ∫ z, distBCF z ∂π.toMeasure) :=
  continuous_integral_coupling distBCF

/-- **Attainment of the transport infimum** (`exists_optimal_coupling`): For the bounded continuous
`dist` cost there is an actual minimizing coupling — the infimum is *attained*, not merely an
infimum.  Anchored: The attained value is the hand-computed `krTransportCost δ₀ δ₁ = 1`. -/
private theorem exists_optimal_coupling_witness :
    ∃ π ∈ couplings d0 d1,
      transportCost (fun z => distBCF z) d0 d1 = ∫ z, distBCF z ∂π.toMeasure :=
  exists_optimal_coupling distBCF d0 d1

/-- **The transport infimum is *attained* at the dual value `1`** — the genuine attainment
statement,
not merely "some coupling has cost `1`". There is a coupling `π` whose `dist`-cost equals the
*primal infimum* `krTransportCost d0 d1` (so `π` is optimal), and that common value is the
hand-computed `1`, which in turn equals the dual `krDist d0 d1` (zero gap). Stating the cost against
`krTransportCost`/`krDist` (not just `= 1`) is what records optimality. -/
private theorem optimal_coupling_value_one :
    ∃ π ∈ couplings d0 d1,
      krTransportCost d0 d1 = ∫ z, dist z.1 z.2 ∂π.toMeasure ∧
        krDist d0 d1 = ∫ z, dist z.1 z.2 ∂π.toMeasure ∧
        ∫ z, dist z.1 z.2 ∂π.toMeasure = 1 := by
  obtain ⟨π, hπ, hπ_eq⟩ := exists_optimal_coupling_witness
  -- `hπ_eq : krTransportCost d0 d1 = ∫ distBCF dπ`, with `distBCF z = dist z.1 z.2`.
  have hcost : krTransportCost d0 d1 = ∫ z, dist z.1 z.2 ∂π.toMeasure := by
    simpa [distBCF] using hπ_eq
  refine ⟨π, hπ, hcost, ?_, ?_⟩
  · rw [← hcost, krDist_eq_one, krTransportCost_eq_one]
  · rw [← hcost, krTransportCost_eq_one]

/-! ## Block 4: The transport-cost form's metric algebra -/

/-- **Symmetry of the transport cost** (`krTransportCost_comm`):
`krTransportCost δ₀ δ₁ =
krTransportCost δ₁ δ₀` (pushforward under `Prod.swap`). -/
private theorem krTransportCost_comm_witness :
    krTransportCost d0 d1 = krTransportCost d1 d0 := krTransportCost_comm d0 d1

/-- **Triangle inequality for the transport cost** (`krTransportCost_triangle`) routed through the
midpoint `δ_½`.  The via-point `δ_½` is the **middle** argument: `triangle μ ν ξ` proves
`cost μ ξ ≤ cost μ ν + cost ν ξ`.  Calling `krTransportCost_triangle d0 d1 dh` (transposing the
via-point to the end) is rejected by the elaborator — guards an argument-order slip. -/
private theorem krTransportCost_triangle_witness :
    krTransportCost d0 d1 ≤ krTransportCost d0 dh + krTransportCost dh d1 :=
  krTransportCost_triangle d0 dh d1

/-- **Gluing is legal** (`gluedPlan_mem_couplings`): Gluing a coupling of `(δ₀, δ_½)` and a
coupling of `(δ_½, δ₁)` over their common `δ_½` marginal yields a coupling of `(δ₀, δ₁)`.  This is
the construction feeding `krTransportCost_triangle`. -/
private theorem gluedPlan_mem_couplings_witness :
    gluedPlan dh (prod d0 dh) (prod dh d1) ∈ couplings d0 d1 :=
  gluedPlan_mem_couplings d0 dh d1 (prod_mem_couplings d0 dh) (prod_mem_couplings dh d1)

/-- **The glued plan's cost is subadditive** (`gluedPlan_cost_le`): The `dist`-cost of the glued
coupling is bounded by the sum of the two ingredient costs (the integrated `dist_triangle`). -/
private theorem gluedPlan_cost_le_witness :
    ∫ z, dist z.1 z.2 ∂(gluedPlan dh (prod d0 dh) (prod dh d1)).toMeasure
      ≤ ∫ z, dist z.1 z.2 ∂(prod d0 dh).toMeasure
        + ∫ z, dist z.1 z.2 ∂(prod dh d1).toMeasure :=
  gluedPlan_cost_le d0 dh d1 (prod_mem_couplings d0 dh) (prod_mem_couplings dh d1)

/-! ## Block 5: Barycenter convexity of `krDist`

`krDist_le_integral_krDist` / `_pair` bound the KR distance between barycenters by the average
KR distance.  Beyond the dirac plumbing checks (`τ = δ_{δ₁}`, where the inequality collapses to
`krDist δ₀ δ₁ ≤ krDist δ₀ δ₁`), we exercise the single-marginal form on a **genuine two-point
mixture over the space of laws** `τ = ½δ_{δ₀} + ½δ_{δ₁}`, whose barycenter is the nondegenerate
mixture `η = ½δ₀ + ½δ₁`, giving the *nontrivial* averaged bound
`krDist δ₀ η ≤ ½·krDist δ₀ δ₀ + ½·krDist δ₀ δ₁ = 1/2`. -/

/-- A point mass over the space of laws, atom at `δ₁`. -/
private def tau1 : ProbDist (ProbDist I01) := dirac d1

/-- **Single-marginal barycenter convexity, dirac plumbing** (`krDist_le_integral_krDist`): With
`τ = δ_{δ₁}` the barycenter is `δ₁`, and the inequality `krDist δ₀ δ₁ ≤ ∫ μ, krDist δ₀ μ ∂τ` holds
(both sides equal `krDist δ₀ δ₁`).  Forces the barycenter / integrability hypotheses through real
dirac integrals.  (The *nontrivial* averaged inequality is `krDist_le_integral_krDist_mixture`.) -/
private theorem krDist_le_integral_krDist_witness :
    krDist d0 d1 ≤ ∫ μ, krDist d0 μ ∂tau1.toMeasure := by
  refine krDist_le_integral_krDist d0 d1 tau1 ?_ ?_
  · intro f; rw [tau1, dirac_toMeasure, integral_dirac]
  · rw [tau1, dirac_toMeasure]; exact integrable_dirac enorm_lt_top

/-- The uniform simplex weight `(½, ½)`. -/
private def lamHalf : stdSimplex ℝ (Fin 2) :=
  ⟨![1 / 2, 1 / 2], by
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]; norm_num⟩

/-- A **genuine two-point mixture** over the space of laws: `τ = ½δ_{δ₀} + ½δ_{δ₁}` (not a point
mass). -/
private def tauMix : ProbDist (ProbDist I01) := finiteLaw ![d0, d1] lamHalf

/-- The nondegenerate barycenter of `tauMix`: `η = ½δ₀ + ½δ₁` on `[0,1]`. -/
private def etaMix : ProbDist I01 := finiteLaw ![pt0, pt1] lamHalf

/-- `μ ↦ expect μ f` is continuous on the law space for a bounded continuous `f` (portmanteau). -/
private theorem expect_continuous (f : I01 →ᵇ ℝ) :
    Continuous (fun μ : ProbDist I01 => expect μ f) := by
  simpa [expect] using
    MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (X := I01) f

/-- **The mixture barycenter identity.** Averaging any bounded-continuous test `f` against the
two-point mixture `τ = ½δ_{δ₀} + ½δ_{δ₁}` reproduces the test against the barycenter
`η = ½δ₀ + ½δ₁`:
`∫ μ, expect μ f ∂τ = ½·expect δ₀ f + ½·expect δ₁ f = ½f(0) + ½f(1) = expect η f`. -/
private theorem tauMix_avg (f : I01 →ᵇ ℝ) :
    ∫ μ, expect μ (fun x => f x) ∂tauMix.toMeasure = expect etaMix (fun x => f x) := by
  -- LHS = expect over `tauMix` of the (continuous, hence ae-measurable) map `μ ↦ expect μ f`.
  have hg_meas : AEStronglyMeasurable (fun μ : ProbDist I01 => expect μ (fun x => f x))
      tauMix.toMeasure := (expect_continuous f).aestronglyMeasurable
  have hlhs : ∫ μ, expect μ (fun x => f x) ∂tauMix.toMeasure
      = ∑ i, (lamHalf : Fin 2 → ℝ) i * expect (![d0, d1] i) (fun x => f x) := by
    rw [show (∫ μ, expect μ (fun x => f x) ∂tauMix.toMeasure)
        = expect tauMix (fun μ => expect μ (fun x => f x)) from rfl, tauMix,
      finiteLaw_expect _ lamHalf _ hg_meas]
  rw [hlhs, etaMix, finiteLaw_expect_boundedContinuous ![pt0, pt1] lamHalf f]
  -- both sides: `½·(expect δ₀ f) + ½·(expect δ₁ f) = ½·f(pt0) + ½·f(pt1)` via `expect_dirac`.
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, d0, d1,
    expect_dirac]

/-- **Single-marginal barycenter convexity on a nondegenerate mixture**
(`krDist_le_integral_krDist`):
With `τ = ½δ_{δ₀} + ½δ_{δ₁}` the barycenter is `η = ½δ₀ + ½δ₁`, and the inequality
`krDist δ₀ η ≤ ∫ μ, krDist δ₀ μ ∂τ` is a *genuine* convexity bound — the right-hand average is
`½·krDist δ₀ δ₀ + ½·krDist δ₀ δ₁ = 1/2`, not a tautological `krDist δ₀ δ₁ ≤ krDist δ₀ δ₁`. -/
private theorem krDist_le_integral_krDist_mixture :
    krDist d0 etaMix ≤ ∫ μ, krDist d0 μ ∂tauMix.toMeasure := by
  refine krDist_le_integral_krDist d0 etaMix tauMix (fun f => tauMix_avg f) ?_
  -- `μ ↦ krDist d0 μ` is bounded (by the KR diameter `1`) and measurable (LSC), hence integrable
  -- against the finite-mass `tauMix`.
  refine MeasureTheory.Integrable.mono' (integrable_const (1 : ℝ))
    ((krDist_lowerSemicontinuous.comp (Continuous.prodMk_right d0)).measurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun μ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (krDist_nonneg d0 μ)]
  exact le_trans (le_trans (krDist_le_krTransportCost d0 μ)
    (transportCost_le_integral_of_bdd continuous_dist.measurable d0 μ
      (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
      (fun z => dist_le_one z.1 z.2) (prod_mem_couplings d0 μ))) (by
    have hb : ∫ z, dist z.1 z.2 ∂(prod d0 μ).toMeasure ≤ ∫ _, (1 : ℝ) ∂(prod d0 μ).toMeasure := by
      apply integral_mono_ae
      · exact (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_dist⟩).integrable _
      · exact integrable_const 1
      · exact Filter.Eventually.of_forall (fun z => dist_le_one z.1 z.2)
    rwa [integral_const, probReal_univ, one_smul] at hb)

/-! ### Genuine pair-form barycenter convexity (non-Dirac `τ`, nonconstant `ν`)

The pair theorem `krDist_le_integral_krDist_pair` needs a *non-Dirac* law-over-laws `τ` and a
*nonconstant* measurable right-marginal family `ν`.  We take the asymmetric two-point mixture
`τ = ⅓δ_{δ₀} + ⅔δ_{δ₁}` (barycenter `μ₀ = ⅓δ₀ + ⅔δ₁`) and `ν = R_*` (pushforward by the interval
reflection `R(x) = 1 − x`, so `ν δ₀ = δ₁`, `ν δ₁ = δ₀` — genuinely nonconstant), whose
`τ`-barycenter is the *distinct* law `η₀ = ⅔δ₀ + ⅓δ₁`.  The resulting bound
`krDist μ₀ η₀ ≤ ∫ μ, krDist μ (ν μ) ∂τ` is a genuine convexity inequality between two different
barycenters, exercising both averaging hypotheses and the measurable family — none of which the
single-atom Dirac plumbing reached. -/

/-- The KR diameter bound on `[0,1]`: `krDist μ ν ≤ 1` (from
`krDist ≤ krTransportCost ≤ ∫ dist ≤ 1`). -/
private theorem krDist_le_one (μ ν : ProbDist I01) : krDist μ ν ≤ 1 := by
  refine le_trans (krDist_le_krTransportCost μ ν) ?_
  refine le_trans (transportCost_le_integral_of_bdd
    (c := fun p : I01 × I01 => dist p.1 p.2) continuous_dist.measurable μ ν
    (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
    (fun z => dist_le_one z.1 z.2) (prod_mem_couplings μ ν)) ?_
  have hb : ∫ z, dist z.1 z.2 ∂(prod μ ν).toMeasure ≤ ∫ _, (1 : ℝ) ∂(prod μ ν).toMeasure := by
    apply integral_mono_ae
    · exact (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_dist⟩).integrable _
    · exact integrable_const 1
    · exact Filter.Eventually.of_forall (fun z => dist_le_one z.1 z.2)
  rw [integral_const, probReal_univ, one_smul] at hb; exact hb

/-- The interval reflection `R(x) = 1 − x` on `[0,1]` (continuous, swaps the endpoints `0 ↔ 1`). -/
private def refl01 : I01 → I01 := fun x => ⟨1 - (x : ℝ), by
  have hx := x.2; simp only [Set.mem_Icc] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]⟩

private theorem refl01_continuous : Continuous refl01 :=
  Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _

private theorem refl01_pt0 : refl01 pt0 = pt1 := by apply Subtype.ext; simp [refl01, pt0, pt1]

private theorem refl01_pt1 : refl01 pt1 = pt0 := by apply Subtype.ext; simp [refl01, pt0, pt1]

/-- The **nonconstant** right-marginal family: pushforward of a law by the reflection `R`.
Genuinely nonconstant since `ν δ₀ = δ₁ ≠ δ₀ = ν δ₁`. -/
private def reflLaw : ProbDist I01 → ProbDist I01 :=
  fun μ => ProbDist.map μ refl01 refl01_continuous.measurable

private theorem reflLaw_continuous : Continuous reflLaw :=
  MeasureTheory.ProbabilityMeasure.continuous_map refl01_continuous

/-- The reflection precomposed into a bounded-continuous test (`f ∘ R`). -/
private def reflBCF (f : I01 →ᵇ ℝ) : I01 →ᵇ ℝ :=
  f.compContinuous ⟨refl01, refl01_continuous⟩

@[simp] private theorem reflBCF_apply (f : I01 →ᵇ ℝ) (x : I01) : reflBCF f x = f (refl01 x) := rfl

/-- Averaging a bounded-continuous law-functional `μ ↦ expect μ g` against a finite law over the law
space reproduces the weighted average over the atoms (the barycenter identity, general form). -/
private theorem finiteLaw_law_avg {m : ℕ} (atoms : Fin m → ProbDist I01)
    (lam : stdSimplex ℝ (Fin m)) (g : I01 →ᵇ ℝ) :
    ∫ μ, expect μ (fun x => g x) ∂(finiteLaw atoms lam).toMeasure
      = ∑ i, (lam : Fin m → ℝ) i * expect (atoms i) (fun x => g x) :=
  finiteLaw_expect atoms lam (fun μ => expect μ (fun x => g x))
    (expect_continuous g).aestronglyMeasurable

/-- The asymmetric simplex weight `(⅓, ⅔)`. -/
private def lamThird : stdSimplex ℝ (Fin 2) :=
  ⟨![1 / 3, 2 / 3], by
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]; norm_num⟩

/-- The non-Dirac law-over-laws `τ = ⅓δ_{δ₀} + ⅔δ_{δ₁}`. -/
private def tauAsym : ProbDist (ProbDist I01) := finiteLaw ![d0, d1] lamThird

/-- The barycenter of `τ`: `μ₀ = ⅓δ₀ + ⅔δ₁`. -/
private def mu0Asym : ProbDist I01 := finiteLaw ![pt0, pt1] lamThird

/-- The `ν`-pushed barycenter: `η₀ = ⅔δ₀ + ⅓δ₁` (the reflection swaps the atoms). -/
private def eta0Asym : ProbDist I01 := finiteLaw ![pt1, pt0] lamThird

/-- `τ` averages identity-tests to its barycenter `μ₀`: `∫ μ, expect μ f ∂τ = expect μ₀ f`. -/
private theorem tauAsym_avg_mu0 (f : I01 →ᵇ ℝ) :
    ∫ μ, expect μ (fun x => f x) ∂tauAsym.toMeasure = expect mu0Asym (fun x => f x) := by
  rw [tauAsym, finiteLaw_law_avg ![d0, d1] lamThird f, mu0Asym,
    finiteLaw_expect_boundedContinuous ![pt0, pt1] lamThird f,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, d0, d1, expect_dirac]

/-- `τ` averages `ν`-tests to the *distinct* barycenter `η₀`:
`∫ μ, expect (ν μ) f ∂τ = expect η₀ f`.
The reflection turns the `i`-th atom test `expect δ_{pt i} (f∘R) = f(R pt i)` into the swapped test,
so the right-marginal barycenter is `η₀ = ⅔δ₀ + ⅓δ₁`. -/
private theorem tauAsym_avg_eta0 (f : I01 →ᵇ ℝ) :
    ∫ μ, expect (reflLaw μ) (fun x => f x) ∂tauAsym.toMeasure
      = expect eta0Asym (fun x => f x) := by
  have hpt : ∀ μ : ProbDist I01,
      expect (reflLaw μ) (fun x => f x) = expect μ (fun x => reflBCF f x) := by
    intro μ
    simp only [reflLaw]
    rw [ProbDist.expect_map μ refl01 refl01_continuous.measurable (fun x => f x)
      f.continuous.aestronglyMeasurable]
    simp only [reflBCF_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), tauAsym,
    finiteLaw_law_avg ![d0, d1] lamThird (reflBCF f), eta0Asym,
    finiteLaw_expect_boundedContinuous ![pt1, pt0] lamThird f,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, d0, d1, expect_dirac, reflBCF_apply,
    refl01_pt0, refl01_pt1]

/-- **Genuine pair-form barycenter convexity** (`krDist_le_integral_krDist_pair`): with the
*non-Dirac* law-over-laws `τ = ⅓δ_{δ₀} + ⅔δ_{δ₁}` and the *nonconstant* measurable family `ν = R_*`
(reflection pushforward), the bound `krDist μ₀ η₀ ≤ ∫ μ, krDist μ (ν μ) ∂τ` relates the two
*distinct* barycenters `μ₀ = ⅓δ₀ + ⅔δ₁` and `η₀ = ⅔δ₀ + ⅓δ₁`.  Both averaging hypotheses and the
measurable right-marginal family are exercised on genuinely non-degenerate data — the strengthening
the work item asks for over the single-atom Dirac plumbing.  (The single-marginal nondegenerate
bound is `krDist_le_integral_krDist_mixture`.) -/
private theorem krDist_le_integral_krDist_pair_witness :
    krDist mu0Asym eta0Asym ≤ ∫ μ, krDist μ (reflLaw μ) ∂tauAsym.toMeasure := by
  refine krDist_le_integral_krDist_pair mu0Asym eta0Asym tauAsym
    (ν := reflLaw) reflLaw_continuous.measurable tauAsym_avg_mu0 tauAsym_avg_eta0 ?_
  -- `μ ↦ krDist μ (ν μ)` is bounded by the KR diameter `1` and measurable (LSC ∘ continuous).
  have hlsc : LowerSemicontinuous (fun μ : ProbDist I01 => krDist μ (reflLaw μ)) := by
    simpa [Function.comp] using
      krDist_lowerSemicontinuous.comp (continuous_id.prodMk reflLaw_continuous)
  refine MeasureTheory.Integrable.mono' (integrable_const (1 : ℝ))
    hlsc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun μ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (krDist_nonneg μ (reflLaw μ))]
  exact krDist_le_one μ (reflLaw μ)

/-! ## Block 6: Couplings — marginal orientation and compactness (`Coupling.lean`)

The coupling spine, with the **fst/snd marginal orientation** made explicit on the *distinct*
laws `δ₀, δ₁` (so a swap is detectable) and compactness (so the infimum is attained, not merely
bounded). -/

/-- **Membership form** (`mem_couplings`): `π ∈ couplings μ ν ↔ IsCoupling μ ν π`. This is a
definitional API-shape smoke test only; the *orientation* (which marginal is first) is checked
substantively by the explicit `prod_fst_marginal_is_d0` / `prod_snd_marginal_is_d1` theorems below
together with `d0_ne_d1`, not by this membership iff. -/
private theorem mem_couplings_witness :
    prod d0 d1 ∈ couplings d0 d1 ↔ IsCoupling d0 d1 (prod d0 d1) := mem_couplings

/-- **The independent (product) coupling is legal** (`prod_mem_couplings`). -/
private theorem prod_mem_couplings_witness : prod d0 d1 ∈ couplings d0 d1 :=
  prod_mem_couplings d0 d1

/-- **fst-marginal orientation**: The product coupling of the *distinct* laws `δ₀, δ₁` has
`Prod.fst`-marginal `δ₀` — the **first** law, not `δ₁`.  Because `δ₀ ≠ δ₁`, an fst/snd swap in the
coupling convention would land on `δ₁` here and be caught. -/
private theorem prod_fst_marginal_is_d0 :
    ProbDist.map (prod d0 d1) Prod.fst measurable_fst = d0 :=
  (prod_isCoupling d0 d1).fst_marginal

/-- **snd-marginal orientation**: The product coupling's `Prod.snd`-marginal is `δ₁` — the
**second** law.  Paired with `prod_fst_marginal_is_d0` and `d0_ne_d1` this fixes the orientation
unambiguously. -/
private theorem prod_snd_marginal_is_d1 :
    ProbDist.map (prod d0 d1) Prod.snd measurable_snd = d1 :=
  (prod_isCoupling d0 d1).snd_marginal

/-- **Non-emptiness** (`couplings_nonempty`): `Π(δ₀, δ₁)` is nonempty. -/
private theorem couplings_nonempty_witness : (couplings d0 d1).Nonempty :=
  couplings_nonempty d0 d1

/-- **Continuity of the fst-marginal map** (`continuous_fst_marginal`). -/
private theorem continuous_fst_marginal_witness :
    Continuous (fun π : ProbDist (I01 × I01) => ProbDist.map π Prod.fst measurable_fst) :=
  continuous_fst_marginal

/-- **Continuity of the snd-marginal map** (`continuous_snd_marginal`). -/
private theorem continuous_snd_marginal_witness :
    Continuous (fun π : ProbDist (I01 × I01) => ProbDist.map π Prod.snd measurable_snd) :=
  continuous_snd_marginal

/-- **Closedness** (`couplings_isClosed`): `Π(δ₀, δ₁)` is weak-* closed (a preimage of singletons
under the continuous marginal maps). -/
private theorem couplings_isClosed_witness : IsClosed (couplings d0 d1) :=
  couplings_isClosed d0 d1

/-- **Compactness** (`couplings_isCompact`): On the *compact* base `[0,1]`, `Π(δ₀, δ₁)` is weak-*
compact — the Prokhorov input that makes the transport infimum *attained* (cf.
`exists_optimal_coupling`), not merely bounded. -/
private theorem couplings_isCompact_witness : IsCompact (couplings d0 d1) :=
  couplings_isCompact d0 d1

end EconlibTest.Optimization.OptimalTransportCore

end
