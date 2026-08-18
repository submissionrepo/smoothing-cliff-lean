/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Optimal-transport duality non-vacuity witnesses (finite KR duality, KR norm, c-transform)

Compile-time semantic witnesses for the `Econlib.Optimization.OptimalTransport` duality layer
(`DualityFinite`, `KRSignedMeasure`, `LipschitzDual`, `AtomicDense`, `Atomization`,
`Discretization`, `CTransform`, `UpperLipschitzEnvelope`).  The witnesses run on **two concrete
finite problems**:

* The **2-point metric LP** on `Fin 2` with marginals `p = (1,0)`, `q = (0,1)` and cost matrix
  `d = [[0,1],[1,0]]` (the Hamming / `{0,1}` distance).  Hand-computation: The row/column sums
  force a **unique** coupling `π = [[0,1],[0,0]]` of primal cost `π₀₁·d₀₁ = 1`, so the primal
  infimum is `1`; finite KR duality then forces the dual supremum to `1` as well — the duality gap
  is **zero**.
* Concrete **diracs on the compact metric space** `[0,1]` (the subtype `↥(Set.Icc (0:ℝ) 1)`):
  `δ₀, δ₁, δ_½`.  These anchor the KR norm (`‖ofProbDist δ₀ − ofProbDist δ₁‖ = krDist δ₀ δ₁`), the
  Lipschitz-dual evaluation, the c-transform, atomization, discretization, and — the headline
  negative check — `krDist_pos_of_ne`: The KR metric *strictly separates* the distinct laws
  `δ₀, δ₁`.

## What each block catches

* **Strong duality on finite support** — a primal/dual direction reversal.
  `krDist_eq_krTransportCost_of_finsupp` is checked as an *equality* (zero gap), bridged back to the
  concrete value `1` on `δ₀, δ₁` (`krDist_krTransportCost_eq_one`), and the finite LP
  `fin_kr_duality`
  is anchored to the hand-computed common value `1`. The finite LP *vertex* itself is pinned: every
  feasible coupling equals `pi2 = [[0,1],[0,0]]` (`coupling_eq_pi2`), not just its cost.
* **KR norm vs distance** — `norm_ofProbDist_sub` recovers `krDist`; a norm/distance mismatch
  breaks it.  Norm scaling/triangle/neg are checked.
* **Lipschitz dual sign / Lipschitz constant** — `signedIntegral` linearity, the operator-norm
  bound `≤ 1`, and `|signedIntegral| ≤ K · ‖μ‖`. The dual is anchored on *nonzero* data:
  `signedIntegral φ (ι δ₁) = −1` and, on the zero-mass difference `μ = ι δ₀ − ι δ₁`
  (total mass `0`), `signedIntegral φ μ = (lipschitzEval φ) μ = 1` — the genuine KR dual value,
  not the tautological `0`.
* **Vacuous metric** — `krDist_pos_of_ne` / `krDist_eq_zero_iff` separate the distinct laws
  `δ₀, δ₁`.  A metric returning `0` between distinct laws fails here.
* **Coupling orientation under atomization** — `atomizeCoupling_isCoupling` has marginals
  `(μ, atomize μ)` in that order; the atomized law is *identified exactly* as `atomize δ_½ V = δ₀`
  (`atomize_dh_eq_d0`), and the atomization cost / KR distance / expectation displacement are
  computed
  *sharply* as `1/2` (the true mass movement from `½` to `0`), against the loose diameter bound `1`.
* **Envelope / discretization** — `upperLipschitzEnvelope Vid 1` is computed exactly (`= Vid`, with
  values `0` at `δ₀`, `1` at `δ₁`), and the nonuniform-weight swap `(1,0)` exhibits a *nonzero*
  reindexing push bound (`= 1`), which symmetric weights would erase.
-/

noncomputable section

namespace EconlibTest.Optimization.OptimalTransportDuality

open MeasureTheory Set BoundedContinuousFunction Matrix
open Econlib.Probability Econlib.Probability.ProbDist
open Econlib.Optimization.OptimalTransport
open Econlib.Optimization.OptimalTransport.KRSignedMeasure

/-! ## The concrete carriers

`I01 = ↥[0,1]` is the compact metric carrier; `default` is `0` so the KR-norm basepoint lemmas
(which evaluate at `default`) fire.  The 2-point LP lives on `Fin 2`. -/

/-- The unit interval `[0,1]` as a compact metric space (the KR carrier). -/
private abbrev I01 := (Set.Icc (0 : ℝ) 1)

/-- The endpoint `0 ∈ [0,1]`. -/
private def pt0 : I01 := ⟨0, by norm_num⟩

/-- The endpoint `1 ∈ [0,1]`. -/
private def pt1 : I01 := ⟨1, by norm_num⟩

/-- The midpoint `½ ∈ [0,1]`. -/
private def pthalf : I01 := ⟨1 / 2, by norm_num⟩

/-- Basepoint `0` for the KR norm: `default = 0`, so `‖μ‖ = krNorm 0 μ`. -/
private instance : Inhabited I01 := ⟨pt0⟩

/-- The dirac `δ₀` at `0`. -/
private def d0 : ProbDist I01 := dirac pt0

/-- The dirac `δ₁` at `1`. -/
private def d1 : ProbDist I01 := dirac pt1

/-- The dirac `δ_½` at `½`. -/
private def dh : ProbDist I01 := dirac pthalf

/-- Every distance on `[0,1]` is bounded by the diameter `1`. -/
private theorem dist_le_one (x y : I01) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq, Real.dist_eq]
  have hx := x.2; have hy := y.2
  simp only [Set.mem_Icc] at hx hy
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **The two laws are distinct** (the precondition for a non-vacuous KR separation): Separated by
the coordinate test `expect δ₀ id = 0 ≠ 1 = expect δ₁ id`. -/
private theorem d0_ne_d1 : d0 ≠ d1 := by
  intro h
  have hd : expect d0 (fun x : I01 => (x : ℝ)) = expect d1 (fun x : I01 => (x : ℝ)) := by rw [h]
  rw [d0, d1, expect_dirac, expect_dirac] at hd
  simp only [pt0, pt1] at hd
  norm_num at hd

/-! ## Block 1: Strong duality on finitely-supported laws (`DualityFinite.lean`)

The headline: `krDist δ₀ δ₁ = krTransportCost δ₀ δ₁` for laws supported on the finite set
`{0, 1}`.  Together with the value `1` (established in `OptimalTransportCore`), the duality gap is
**zero**. -/

/-- The two-element support `{0, 1} ⊆ [0,1]`. -/
private def Spts : Finset I01 := {pt0, pt1}

private theorem Spts_meas : MeasurableSet (Spts : Set I01) := Spts.finite_toSet.measurableSet

private theorem pt0_mem : pt0 ∈ (Spts : Set I01) := by
  rw [Finset.mem_coe]; exact Finset.mem_insert_self _ _

private theorem pt1_mem : pt1 ∈ (Spts : Set I01) := by
  rw [Finset.mem_coe]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- `δ₀` puts all its mass on the support `{0, 1}`. -/
private theorem d0_supp : d0.toMeasure (Spts : Set I01) = 1 := by
  rw [d0, dirac_toMeasure, Measure.dirac_apply' _ Spts_meas, Set.indicator_of_mem pt0_mem]; rfl

/-- `δ₁` puts all its mass on the support `{0, 1}`. -/
private theorem d1_supp : d1.toMeasure (Spts : Set I01) = 1 := by
  rw [d1, dirac_toMeasure, Measure.dirac_apply' _ Spts_meas, Set.indicator_of_mem pt1_mem]; rfl

/-- **Strong duality on a finite support** (`krDist_eq_krTransportCost_of_finsupp`): For laws
supported on one finite subset, the dual (`krDist`) and primal (`krTransportCost`) forms are
**equal** — the KR duality gap is *zero*, not merely `krDist ≤ krTransportCost`.  A primal/dual
direction reversal would make these unequal. -/
private theorem krDist_eq_krTransportCost_of_finsupp_witness :
    krDist d0 d1 = krTransportCost d0 d1 :=
  krDist_eq_krTransportCost_of_finsupp (S := Spts) d0 d1 d0_supp d1_supp

/-- The distance between the two endpoints is `1`. -/
private theorem dist_pt0_pt1 : dist pt0 pt1 = 1 := by
  rw [Subtype.dist_eq]; simp [pt0, pt1, Real.dist_eq]

/-- A `1`-Lipschitz potential `ψ(x) = -x` (the dual certificate exhibiting `krDist ≥ 1`). -/
private def psiNeg : I01 → ℝ := fun x => -(x : ℝ)

private theorem psiNeg_lip : LipschitzWith 1 psiNeg := by
  intro x y
  simp only [psiNeg, edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [show |(-(x : ℝ)) - (-(y : ℝ))| = |(x : ℝ) - (y : ℝ)| by
    rw [show (-(x : ℝ)) - (-(y : ℝ)) = -((x : ℝ) - (y : ℝ)) by ring, abs_neg]]
  simp

/-- The coordinate potential `pTilde(x) = x`, `1`-Lipschitz (the dual certificate for the sharp
atomization distances in Block 6, and the c-transform tests in Block 8). -/
private def pTilde : I01 → ℝ := fun x => (x : ℝ)

private theorem pTilde_lip : LipschitzWith (1 : ℝ).toNNReal pTilde := by
  have h1 : LipschitzWith 1 pTilde := by
    intro x y; simp only [pTilde, edist_dist, Subtype.dist_eq, Real.dist_eq]; simp
  simpa using h1

/-- **The finite LP value `1` is bridged back to the diracs `δ₀, δ₁` on `[0,1]`**:
`krDist δ₀ δ₁ = 1`
*and* `krTransportCost δ₀ δ₁ = 1`. The dual lower bound uses the potential `ψ(x) = -x`
(`expect δ₀ ψ − expect δ₁ ψ = 0 − (−1) = 1`), the primal upper bound uses the diameter `dist ≤ 1`,
and the easy duality `krDist ≤ krTransportCost` squeezes both to `1`. This is the concrete value the
finsupp-strong-duality witness above leaves abstract — a shared scaling error in both sides would
fail it. -/
private theorem krDist_krTransportCost_eq_one :
    krDist d0 d1 = 1 ∧ krTransportCost d0 d1 = 1 := by
  -- Dual lower bound: `krDist δ₀ δ₁ ≥ expect δ₀ ψ − expect δ₁ ψ = 1`.
  have hge : (1 : ℝ) ≤ krDist d0 d1 := by
    have h : (1 : ℝ) = expect d0 psiNeg - expect d1 psiNeg := by
      rw [d0, d1, expect_dirac, expect_dirac]; simp [psiNeg, pt0, pt1]
    rw [h]
    exact le_csSup (bddAbove_krDist_setOf d0 d1) ⟨psiNeg, psiNeg_lip, rfl⟩
  -- Primal upper bound: `krTransportCost δ₀ δ₁ ≤ ∫ dist d(δ₀⊗δ₁) = dist 0 1 = 1`.
  have hle : krTransportCost d0 d1 ≤ 1 := by
    have hbd : krTransportCost d0 d1 ≤ ∫ z, dist z.1 z.2 ∂(prod d0 d1).toMeasure :=
      transportCost_le_integral_of_bdd continuous_dist.measurable d0 d1
        (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
        (fun z => dist_le_one z.1 z.2) (prod_mem_couplings d0 d1)
    have hcost : ∫ z, dist z.1 z.2 ∂(prod d0 d1).toMeasure = 1 := by
      change ∫ z, dist z.1 z.2 ∂((d0.toMeasure).prod (d1.toMeasure)) = 1
      rw [d0, d1, dirac_toMeasure, dirac_toMeasure, Measure.dirac_prod_dirac,
        MeasureTheory.integral_dirac]
      exact dist_pt0_pt1
    rwa [hcost] at hbd
  have hkr_eq : krDist d0 d1 = 1 :=
    le_antisymm (le_trans (krDist_le_krTransportCost d0 d1) hle) hge
  exact ⟨hkr_eq, le_antisymm hle (le_trans hge (krDist_le_krTransportCost d0 d1))⟩

/-! ## Block 2: The finite Kantorovich–Rubinstein LP, anchored to value `1`

The 2-point metric LP: Marginals `p = (1,0)`, `q = (0,1)`, cost matrix `d = [[0,1],[1,0]]`.
The unique coupling has cost `1`; finite KR duality forces the dual supremum to `1`. -/

/-- First marginal `p = (1,0)`. -/
private def p2 : Fin 2 → ℝ := ![1, 0]

/-- Second marginal `q = (0,1)`. -/
private def q2 : Fin 2 → ℝ := ![0, 1]

/-- The cost matrix `d = [[0,1],[1,0]]` (the `{0,1}` metric). -/
private def d2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem p2_nonneg : ∀ i, 0 ≤ p2 i := by intro i; fin_cases i <;> norm_num [p2]
private theorem p2_sum : ∑ i, p2 i = 1 := by simp [p2, Fin.sum_univ_two]
private theorem q2_nonneg : ∀ i, 0 ≤ q2 i := by intro i; fin_cases i <;> norm_num [q2]
private theorem q2_sum : ∑ i, q2 i = 1 := by simp [q2, Fin.sum_univ_two]
private theorem d2_nonneg : ∀ i j, 0 ≤ d2 i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [d2]

/-- `d = [[0,1],[1,0]]` is a genuine finite metric cost (nonneg, zero-iff-diagonal, symmetric,
triangular). -/
private theorem d2_metric : IsFiniteMetricCost 2 d2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [d2]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [d2]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [d2]
  · intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [d2]

/-- **The finite coupling polytope is nonempty** (`finCouplings_nonempty`). -/
private theorem finCouplings_nonempty_witness : (finCouplings 2 p2 q2).Nonempty :=
  finCouplings_nonempty 2 p2 q2 p2_nonneg p2_sum q2_nonneg q2_sum

/-- **The finite coupling polytope is closed** (`finCouplings_isClosed`). -/
private theorem finCouplings_isClosed_witness : IsClosed (finCouplings 2 p2 q2) :=
  finCouplings_isClosed 2 p2 q2

/-- **The finite coupling polytope is compact** (`finCouplings_isCompact`) — the input that makes
the primal infimum attained. -/
private theorem finCouplings_isCompact_witness : IsCompact (finCouplings 2 p2 q2) :=
  finCouplings_isCompact 2 p2 q2

/-- **Finite Lipschitz potentials form a closed set** (`finLipschitz_isClosed`). -/
private theorem finLipschitz_isClosed_witness : IsClosed (finLipschitz 2 d2) :=
  finLipschitz_isClosed 2 d2

/-- **Normalized finite Lipschitz potentials are compact** (`finLipschitzZero_isCompact`) — the
input that makes the dual supremum attained. -/
private theorem finLipschitzZero_isCompact_witness : IsCompact (finLipschitzZero 2 d2) :=
  finLipschitzZero_isCompact 2 d2 d2_metric.nonneg d2_metric.symm d2_metric.triangle

/-- The unique coupling forced by the marginals: `π = [[0,1],[0,0]]`. -/
private def pi2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

private theorem pi2_mem : pi2 ∈ finCouplings 2 p2 q2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [pi2]
  · intro i; fin_cases i <;> simp [pi2, p2, Fin.sum_univ_two]
  · intro j; fin_cases j <;> simp [pi2, q2, Fin.sum_univ_two]

/-- **Every feasible coupling costs exactly `1`**: The marginals `(1,0)` / `(0,1)` force
`π 1 0 = 0`,
`π 0 0 = 0` and hence `π 0 1 = 1`; the primal cost is then `π₀₁·d₀₁ = 1`. (Cost equality — the
*matrix* uniqueness `π = pi2` is the stronger `coupling_eq_pi2` below.) -/
private theorem coupling_cost_eq_one (π : Matrix (Fin 2) (Fin 2) ℝ)
    (hπ : π ∈ finCouplings 2 p2 q2) : ∑ i, ∑ j, π i j * d2 i j = 1 := by
  obtain ⟨hnn, hrow, hcol⟩ := hπ
  have hr1 := hrow 1; have hc0 := hcol 0
  simp only [p2, q2, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.sum_univ_two] at hr1 hc0
  have h10 : π 1 0 = 0 := le_antisymm (by linarith [hnn 1 1]) (hnn 1 0)
  have h00 : π 0 0 = 0 := le_antisymm (by linarith [hnn 1 0]) (hnn 0 0)
  have hr0 := hrow 0
  simp only [p2, Matrix.cons_val_zero, Fin.sum_univ_two] at hr0
  have h01 : π 0 1 = 1 := by rw [h00] at hr0; linarith
  simp [d2, Fin.sum_univ_two, h00, h01, h10]

/-- **The coupling is genuinely *unique***: the marginals `(1,0)` / `(0,1)` force *every* feasible
coupling to equal the single vertex `pi2 = [[0,1],[0,0]]` entrywise — not merely to share its cost.
Row `1` sums to `0` (nonneg ⇒ `π 1 0 = π 1 1 = 0`), column `0` sums to `0` (⇒ `π 0 0 = 0`), and row
`0` then forces `π 0 1 = 1`. So the finite LP vertex itself is pinned, not just the optimal
value. -/
private theorem coupling_eq_pi2 (π : Matrix (Fin 2) (Fin 2) ℝ)
    (hπ : π ∈ finCouplings 2 p2 q2) : π = pi2 := by
  obtain ⟨hnn, hrow, hcol⟩ := hπ
  have hr1 := hrow 1; have hc0 := hcol 0
  simp only [p2, q2, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.sum_univ_two] at hr1 hc0
  have h10 : π 1 0 = 0 := le_antisymm (by linarith [hnn 1 1]) (hnn 1 0)
  have h11 : π 1 1 = 0 := le_antisymm (by linarith [hnn 1 0]) (hnn 1 1)
  have h00 : π 0 0 = 0 := le_antisymm (by linarith [hnn 1 0]) (hnn 0 0)
  have hr0 := hrow 0
  simp only [p2, Matrix.cons_val_zero, Fin.sum_univ_two] at hr0
  have h01 : π 0 1 = 1 := by rw [h00] at hr0; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [pi2, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The primal image is the singleton `{1}` (every coupling costs `1`). -/
private theorem primal_image_eq :
    (fun π : Matrix (Fin 2) (Fin 2) ℝ => ∑ i, ∑ j, π i j * d2 i j) '' finCouplings 2 p2 q2
      = {1} := by
  ext x
  constructor
  · rintro ⟨π, hπ, rfl⟩; exact coupling_cost_eq_one π hπ
  · rintro rfl; exact ⟨pi2, pi2_mem, coupling_cost_eq_one pi2 pi2_mem⟩

/-- **The primal infimum is `1`** (the hand-computed transport cost). -/
private theorem primal_inf_eq_one :
    sInf ((fun π : Matrix (Fin 2) (Fin 2) ℝ => ∑ i, ∑ j, π i j * d2 i j)
      '' finCouplings 2 p2 q2) = 1 := by
  rw [primal_image_eq, csInf_singleton]

/-- **Finite Kantorovich–Rubinstein duality** (`fin_kr_duality`): The dual supremum equals the
primal infimum.  Combined with `primal_inf_eq_one`, both equal the hand-computed `1`: The finite
duality gap is **zero**. -/
private theorem fin_kr_duality_witness :
    sSup ((fun φ : Fin 2 → ℝ => ∑ i, φ i * (p2 i - q2 i)) '' finLipschitz 2 d2) =
    sInf ((fun π : Matrix (Fin 2) (Fin 2) ℝ => ∑ i, ∑ j, π i j * d2 i j)
      '' finCouplings 2 p2 q2) :=
  fin_kr_duality 2 d2 d2_metric p2 q2 p2_nonneg p2_sum q2_nonneg q2_sum

/-- **The dual supremum is also `1`** — reading `fin_kr_duality_witness` against
`primal_inf_eq_one`.  This is the *zero-gap* certificate for the finite LP. -/
private theorem dual_sup_eq_one :
    sSup ((fun φ : Fin 2 → ℝ => ∑ i, φ i * (p2 i - q2 i)) '' finLipschitz 2 d2) = 1 := by
  rw [fin_kr_duality_witness, primal_inf_eq_one]

/-- **Farkas strict lower bound** (`fin_two_potential_strict_lower_bound`): Any `R` strictly below
the primal value `1` (here `R = 0`) is beaten by feasible two-potential dual variables.  Anchored
on `R = 0 < 1 = sInf primal`. -/
private theorem fin_two_potential_strict_lower_bound_witness :
    ∃ u v : Fin 2 → ℝ,
      (∀ i j, u i + v j ≤ d2 i j) ∧ (0 : ℝ) < (∑ i, u i * p2 i) + (∑ j, v j * q2 j) :=
  fin_two_potential_strict_lower_bound 2 d2 d2_nonneg p2 q2 p2_nonneg p2_sum q2_nonneg q2_sum 0
    (by rw [primal_inf_eq_one]; norm_num)

/-! ## Block 3: The Kantorovich–Rubinstein normed space of signed measures (`KRSignedMeasure.lean`)

The embedding `ofProbDist : ProbDist Ω → KRSignedMeasure Ω` and the KR norm.  The headline:
`‖ofProbDist δ₀ − ofProbDist δ₁‖ = krDist δ₀ δ₁`, recovering the KR distance from the norm. -/

/-- **Norm recovers the KR distance** (`norm_ofProbDist_sub`): `‖ι δ₀ − ι δ₁‖ = krDist δ₀ δ₁`.  A
norm/distance mismatch (e.g. total-variation instead of KR) would break this. -/
private theorem norm_ofProbDist_sub_witness :
    ‖ofProbDist d0 - ofProbDist d1‖ = krDist d0 d1 := norm_ofProbDist_sub d0 d1

/-- **The embedding is injective** (`injective_ofProbDist`): Distinct laws give distinct signed
measures. -/
private theorem injective_ofProbDist_witness :
    Function.Injective (ofProbDist : ProbDist I01 → KRSignedMeasure I01) := injective_ofProbDist

/-- **The image of the probability simplex is convex** (`convex_range_ofProbDist`). -/
private theorem convex_range_ofProbDist_witness :
    Convex ℝ (Set.range (ofProbDist : ProbDist I01 → KRSignedMeasure I01)) :=
  convex_range_ofProbDist

/-- **`ofProbDist` carries total mass `1`** (`toSignedMeasure_ofProbDist_univ`). -/
private theorem toSignedMeasure_ofProbDist_univ_witness :
    (ofProbDist d0).toSignedMeasure Set.univ = 1 := toSignedMeasure_ofProbDist_univ d0

/-- **The norm is the basepoint KR norm at `default = 0`** (`norm_def`). -/
private theorem norm_def_witness (μ : KRSignedMeasure I01) : ‖μ‖ = krNorm default μ := norm_def μ

/-- **Triangle inequality for the KR norm** (`krNorm_add_le`). -/
private theorem krNorm_add_le_witness (r s : KRSignedMeasure I01) :
    krNorm default (r + s) ≤ krNorm default r + krNorm default s := krNorm_add_le r s

/-- **The KR norm is even** (`krNorm_neg`). -/
private theorem krNorm_neg_witness (r : KRSignedMeasure I01) :
    krNorm default (-r) = krNorm default r := krNorm_neg r

/-- **Absolute homogeneity** (`krNorm_smul`): `krNorm (c • μ) = |c| · krNorm μ`. -/
private theorem krNorm_smul_witness (c : ℝ) (μ : KRSignedMeasure I01) :
    krNorm default (c • μ) = |c| * krNorm default μ := krNorm_smul default c μ

/-- **Basepoint independence on zero-mass measures** (`krNorm_indep_basepoint`): For a signed
measure of total mass `0`, the KR norm does not depend on the basepoint. -/
private theorem krNorm_indep_basepoint_witness (ω₁ : I01) (μ : KRSignedMeasure I01)
    (hμ : μ.toSignedMeasure Set.univ = 0) : krNorm default μ = krNorm ω₁ μ :=
  krNorm_indep_basepoint default ω₁ μ hμ

/-- **The KR norm of `0` is `0`** (`krNorm_map_zero`). -/
private theorem krNorm_map_zero_witness : krNorm default (0 : KRSignedMeasure I01) = 0 :=
  krNorm_map_zero

/-- **The KR norm separates from `0`** (`krNorm_eq_zero_of_map_eq_zero`): A signed measure of KR
norm `0` is the zero measure. -/
private theorem krNorm_eq_zero_of_map_eq_zero_witness (x : KRSignedMeasure I01) :
    krNorm default x = 0 → x = 0 := krNorm_eq_zero_of_map_eq_zero x

/-- **The KR-norm test set is bounded above** (`bddAbove_krNorm_set`) — the input that makes the
defining `sSup` non-junk. -/
private theorem bddAbove_krNorm_set_witness (s : SignedMeasure I01) :
    BddAbove
      {x : ℝ | ∃ p : I01 → ℝ, LipschitzWith 1 p ∧ p default = 0 ∧
        x = ∫ ω, p ω ∂s.toJordanDecomposition.posPart
          - ∫ ω, p ω ∂s.toJordanDecomposition.negPart} :=
  bddAbove_krNorm_set default s

/-! ## Block 4: The Lipschitz-evaluation dual (`LipschitzDual.lean`, `AtomicDense.lean`)

`signedIntegral p μ` evaluates a Lipschitz potential against a signed measure; `lipschitzEval`
packages it as a continuous linear functional with operator norm `≤ 1`. -/

/-- The optimal Lipschitz potential `φ(x) = -x` (with `φ 0 = φ default = 0`). -/
private def phiNeg : I01 → ℝ := fun x => -(x : ℝ)

/-- `φ(x) = -x` is `1`-Lipschitz. -/
private theorem phiNeg_lip : LipschitzWith 1 phiNeg := by
  intro x y
  simp only [phiNeg, edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [show |(-(x : ℝ)) - (-(y : ℝ))| = |(x : ℝ) - (y : ℝ)| by
    rw [show (-(x : ℝ)) - (-(y : ℝ)) = -((x : ℝ) - (y : ℝ)) by ring, abs_neg]]
  simp

/-- `φ(default) = φ(0) = 0` (the basepoint-vanishing condition for the dual functional). -/
private theorem phiNeg_zero : phiNeg default = 0 := by simp [phiNeg, default, pt0]

/-- **`signedIntegral` against `ofProbDist` is the expectation** (`signedIntegral_ofProbDist`). -/
private theorem signedIntegral_ofProbDist_witness :
    signedIntegral phiNeg (ofProbDist d0) = expect d0 phiNeg := signedIntegral_ofProbDist phiNeg d0

/-- **`signedIntegral` at the *nonzero* anchor `δ₁` is `−1`** — not the tautological `0` of the `δ₀`
case (where `φ(0) = 0`). With `φ(x) = −x`, `signedIntegral φ (ι δ₁) = expect δ₁ φ = φ(1) = −1`. A
sign-flipped or always-zero `signedIntegral` would fail here. -/
private theorem signedIntegral_ofProbDist_d1 :
    signedIntegral phiNeg (ofProbDist d1) = -1 := by
  rw [signedIntegral_ofProbDist phiNeg d1, d1, expect_dirac]
  simp [phiNeg, pt1]

/-- **`signedIntegral` on the zero-mass difference `ι δ₀ − ι δ₁` is `1`** — the value the KR dual
attains. By additivity/homogeneity, `signedIntegral φ (ι δ₀ − ι δ₁) = expect δ₀ φ − expect δ₁ φ =
0 − (−1) = 1`. This evaluates the functional on a genuinely nonzero (total-mass-`0`) measure, the
case the bare boundedness witnesses never reach. -/
private theorem signedIntegral_ofProbDist_diff :
    signedIntegral phiNeg (ofProbDist d0 - ofProbDist d1) = 1 := by
  rw [sub_eq_add_neg, signedIntegral_add phiNeg_lip,
    show -(ofProbDist d1) = (-1 : ℝ) • ofProbDist d1 by rw [neg_one_smul],
    signedIntegral_smul phiNeg_lip, signedIntegral_ofProbDist phiNeg d0,
    signedIntegral_ofProbDist phiNeg d1, d0, d1, expect_dirac, expect_dirac]
  simp [phiNeg, pt0, pt1]

/-- **`signedIntegral` of the zero measure is `0`** (`signedIntegral_zero`). -/
private theorem signedIntegral_zero_witness :
    signedIntegral phiNeg (0 : KRSignedMeasure I01) = 0 := signedIntegral_zero phiNeg

/-- **`signedIntegral` is additive** (`signedIntegral_add`) for a `1`-Lipschitz potential. -/
private theorem signedIntegral_add_witness (μ ν : KRSignedMeasure I01) :
    signedIntegral phiNeg (μ + ν) = signedIntegral phiNeg μ + signedIntegral phiNeg ν :=
  signedIntegral_add phiNeg_lip μ ν

/-- **`signedIntegral` is homogeneous** (`signedIntegral_smul`). -/
private theorem signedIntegral_smul_witness (c : ℝ) (μ : KRSignedMeasure I01) :
    signedIntegral phiNeg (c • μ) = c * signedIntegral phiNeg μ :=
  signedIntegral_smul phiNeg_lip c μ

/-- **The Lipschitz-evaluation functional has operator norm `≤ 1`** (`lipschitzEval_opNorm_le`): A
`1`-Lipschitz potential vanishing at the basepoint evaluates to a `1`-bounded functional — the
KR-duality bound. -/
private theorem lipschitzEval_opNorm_le_witness :
    ‖lipschitzEval phiNeg phiNeg_lip phiNeg_zero‖ ≤ 1 :=
  lipschitzEval_opNorm_le phiNeg_lip phiNeg_zero

/-- **`|signedIntegral| ≤ K · ‖μ‖`** (`abs_signedIntegral_le_lipConst_mul_norm`): The dual pairing
is bounded by the Lipschitz constant times the KR norm — the quantitative KR-duality bound. -/
private theorem abs_signedIntegral_le_lipConst_mul_norm_witness
    (K : NNReal) (p : I01 → ℝ) (hp : LipschitzWith K p) (hp0 : p default = 0)
    (μ : KRSignedMeasure I01) : |signedIntegral p μ| ≤ (K : ℝ) * ‖μ‖ :=
  abs_signedIntegral_le_lipConst_mul_norm hp hp0 μ

/-- **Hanin representation of a zero-mass functional** (`hanin_representation_zeroMass`): Every
continuous linear functional on the KR space is represented by a Lipschitz potential on zero-mass
measures.  Anchored on the concrete functional `lipschitzEval φ`. -/
private theorem hanin_representation_zeroMass_witness :
    ∃ p : I01 → ℝ,
      LipschitzWith ⟨‖lipschitzEval phiNeg phiNeg_lip phiNeg_zero‖, norm_nonneg _⟩ p ∧
      p (default : I01) = 0 ∧
      ∀ μ : KRSignedMeasure I01, μ.toSignedMeasure Set.univ = 0 →
        (lipschitzEval phiNeg phiNeg_lip phiNeg_zero) μ = signedIntegral p μ :=
  hanin_representation_zeroMass (lipschitzEval phiNeg phiNeg_lip phiNeg_zero)

/-- The zero-mass signed measure `μ = ι δ₀ − ι δ₁` (the difference of two probability laws). -/
private def muDiff : KRSignedMeasure I01 := ofProbDist d0 - ofProbDist d1

/-- **`μ = ι δ₀ − ι δ₁` has total mass `0`** — a genuinely nonzero element of the zero-mass subspace
on which the KR dual lives (`1 − 1 = 0`). -/
private theorem muDiff_zeroMass : muDiff.toSignedMeasure Set.univ = 0 := by
  change ((ofProbDist d0).toSignedMeasure - (ofProbDist d1).toSignedMeasure) Set.univ = 0
  rw [MeasureTheory.VectorMeasure.sub_apply, toSignedMeasure_ofProbDist_univ,
    toSignedMeasure_ofProbDist_univ, sub_self]

/-- **The Lipschitz dual functional *evaluates to `1`* on the nonzero zero-mass measure
`μ = ι δ₀ − ι δ₁`.** This is the missing anchor: the operator-norm bound `≤ 1` and the Hanin
representation are vacuous on the zero functional, but here the genuine functional
`lipschitzEval φ` (with `φ(x) = −x`) attains `(lipschitzEval φ) μ = signedIntegral φ μ = 1` — the KR
dual value — on a measure of total mass `0`. A sign-flipped or always-zero dual would fail. -/
private theorem lipschitzEval_muDiff_eq_one :
    (lipschitzEval phiNeg phiNeg_lip phiNeg_zero) muDiff = 1 := by
  rw [lipschitzEval_apply phiNeg_lip phiNeg_zero, muDiff, signedIntegral_ofProbDist_diff]

/-! ## Block 5: The atomic-density metric bumps (`KRSignedMeasure.lean`)

`metricBump K F x = max 0 (1 − K · infDist x F)` is the Lipschitz bump used to approximate
indicators.  It is `1` on `F`, nonnegative, `≤ 1`, and `0` far from `F`. -/

/-- **The metric bump is `1` on its set** (`metricBump_eq_one_of_mem`): At `0 ∈ {0}` the bump is
`1`. -/
private theorem metricBump_eq_one_of_mem_witness :
    max 0 (1 - ((1 : NNReal) : ℝ) * Metric.infDist pt0 ({pt0} : Set I01)) = 1 :=
  metricBump_eq_one_of_mem 1 (Set.mem_singleton _)

/-- **The metric bump is nonnegative** (`metricBump_nonneg`). -/
private theorem metricBump_nonneg_witness (x : I01) :
    (0 : ℝ) ≤ max 0 (1 - ((1 : NNReal) : ℝ) * Metric.infDist x ({pt0} : Set I01)) :=
  metricBump_nonneg 1 _ x

/-- **The metric bump is `≤ 1`** (`metricBump_le_one`). -/
private theorem metricBump_le_one_witness (x : I01) :
    max 0 (1 - ((1 : NNReal) : ℝ) * Metric.infDist x ({pt0} : Set I01)) ≤ 1 :=
  metricBump_le_one 1 _ x

/-- **The metric bump vanishes far from its set** (separation witness): At `1`,
`infDist 1 {0} = 1`, so `max 0 (1 − 1·1) = 0`.  This is what lets the bump approximate the
indicator of `{0}`. -/
private theorem metricBump_eq_zero_far :
    max 0 (1 - ((1 : NNReal) : ℝ) * Metric.infDist pt1 ({pt0} : Set I01)) = 0 := by
  have hd : Metric.infDist pt1 ({pt0} : Set I01) = 1 := by
    rw [Metric.infDist_singleton, Subtype.dist_eq, Real.dist_eq]; simp [pt0, pt1]
  rw [hd]; norm_num

/-! ## Block 6: Atomization (`Atomization.lean`)

Pushing a law onto a finite net via a measurable selector `V`.  We atomize `δ_½` through the
constant selector `V ≡ 0` onto `{0}`, giving `atomize δ_½ V = δ₀`.  The *uniform* selector radius
on `[0,1]` is the diameter `1` (attained at the far end `dist 1 0 = 1`), so the approximation lemmas
fire with `ε = 1`; at the actual mass point the displacement is the sharper `dist ½ 0 = ½`. -/

/-- The one-element net `{0}`. -/
private def Snet : Finset I01 := {pt0}

/-- The constant selector `V ≡ 0` onto `{0}` (measurable). -/
private def Vsel : I01 → Snet := fun _ => ⟨pt0, Finset.mem_singleton_self _⟩

private theorem Vsel_meas : Measurable Vsel := measurable_const

/-- The selector radius bound `dist x (V x) = dist x 0 ≤ 1` (the diameter of `[0,1]`); for the
atomized law `δ_½` the relevant point is `½`, with the sharper value `dist ½ 0 = ½`. -/
private theorem Vsel_radius : ∀ x : I01, dist x (Vsel x : I01) ≤ 1 := by
  intro x
  rw [Subtype.dist_eq, Real.dist_eq]
  have hx := x.2; simp only [Set.mem_Icc] at hx
  have hv : ((Vsel x : I01) : ℝ) = 0 := by simp [Vsel, pt0]
  rw [hv, abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- **The atomized law is supported on the net** (`atomize_support`): `atomize δ_½ V` lives on
`{0}`. -/
private theorem atomize_support_witness :
    (atomize dh Vsel Vsel_meas).toMeasure (Snet : Set I01) = 1 :=
  atomize_support dh Vsel Vsel_meas

/-- **The atomized law is *exactly* `δ₀`** — much stronger than "supported on `{0}`". The constant
selector `V ≡ 0` pushes the entire mass of `δ_½` onto the point `0`, so `atomize δ_½ V = δ₀`. (The
pushforward of any probability law under the constant map `· ↦ 0` is `δ₀`: `map (·↦0) μ =
μ(univ)·δ₀ = δ₀`.) Identifying the atomized law pins the discretization, not just its support. -/
private theorem atomize_dh_eq_d0 : atomize dh Vsel Vsel_meas = d0 := by
  apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
  -- `atomize dh Vsel = map dh (· ↦ pt0)`, whose pushforward measure is `δ_{pt0} = d0`.
  change (Econlib.Probability.ProbDist.map dh (fun x => (Vsel x : I01))
      Vsel_meas.subtype_val).toMeasure = d0.toMeasure
  rw [Econlib.Probability.ProbDist.map_toMeasure,
    show (fun x : I01 => (Vsel x : I01)) = fun _ => pt0 from rfl,
    MeasureTheory.Measure.map_const, MeasureTheory.measure_univ, one_smul, d0, dirac_toMeasure]

/-- **The graph coupling is a coupling** (`atomizeCoupling_isCoupling`): `(id, V)_* δ_½` is a
coupling of `δ_½` and its atomization — in the orientation `couplings μ (atomize μ V)` (first
marginal the *original* law, not the atomized one).  An fst/snd swap would reverse this. -/
private theorem atomizeCoupling_isCoupling_witness :
    atomizeCoupling dh Vsel Vsel_meas ∈ couplings dh (atomize dh Vsel Vsel_meas) :=
  atomizeCoupling_isCoupling dh Vsel Vsel_meas

/-- **Atomization moves transport cost by at most the *uniform* selector radius `1`**
(`atomize_krTransportCost_le`) — the diameter bound the general theorem delivers. -/
private theorem atomize_krTransportCost_le_witness :
    krTransportCost dh (atomize dh Vsel Vsel_meas) ≤ 1 :=
  atomize_krTransportCost_le dh Vsel Vsel_meas Vsel_radius

/-- **The *exact* transport cost of the atomization is `1/2`, not the loose bound `1`.** Because
`atomize δ_½ V = δ₀`, the cost is `krTransportCost δ_½ δ₀`, whose only coupling is `δ_(½,0)`
with cost
`dist(½, 0) = ½` — the actual mass displacement from `½` to `0`. The uniform-radius bound above only
gives `≤ 1`; this sharp value catches a factor-two error. -/
private theorem atomize_krTransportCost_eq_half :
    krTransportCost dh (atomize dh Vsel Vsel_meas) = 1 / 2 := by
  rw [atomize_dh_eq_d0]
  -- `krTransportCost δ_½ δ₀`: dual lower bound (φ(x) = x gives ½) squeezed against primal `≤ dist`.
  have hge : (1 / 2 : ℝ) ≤ krDist dh d0 := by
    have h : (1 / 2 : ℝ) = expect dh pTilde - expect d0 pTilde := by
      rw [dh, d0, expect_dirac, expect_dirac]; norm_num [pTilde, pthalf, pt0]
    rw [h]
    exact le_csSup (bddAbove_krDist_setOf dh d0)
      ⟨pTilde, by simpa using pTilde_lip, rfl⟩
  have hle : krTransportCost dh d0 ≤ 1 / 2 := by
    have hbd : krTransportCost dh d0 ≤ ∫ z, dist z.1 z.2 ∂(prod dh d0).toMeasure :=
      transportCost_le_integral_of_bdd continuous_dist.measurable dh d0
        (C := 1) (fun _ => le_trans (by norm_num) dist_nonneg)
        (fun z => dist_le_one z.1 z.2) (prod_mem_couplings dh d0)
    have hcost : ∫ z, dist z.1 z.2 ∂(prod dh d0).toMeasure = 1 / 2 := by
      change ∫ z, dist z.1 z.2 ∂((dh.toMeasure).prod (d0.toMeasure)) = 1 / 2
      rw [dh, d0, dirac_toMeasure, dirac_toMeasure, Measure.dirac_prod_dirac,
        MeasureTheory.integral_dirac, Subtype.dist_eq]
      norm_num [pthalf, pt0, Real.dist_eq]
    rwa [hcost] at hbd
  exact le_antisymm hle (le_trans hge (krDist_le_krTransportCost dh d0))

/-- **Atomization moves KR distance by at most the *uniform* selector radius `1`**
(`atomize_krDist_le`): The discrete-duality approximation error is controlled, so finite duality
transfers. -/
private theorem atomize_krDist_le_witness :
    krDist dh (atomize dh Vsel Vsel_meas) ≤ 1 :=
  atomize_krDist_le dh Vsel Vsel_meas Vsel_radius

/-- **The *exact* KR distance of the atomization is `1/2`.** Squeezing the dual `≥ ½` (via the
potential `pTilde(x) = x`) against the primal `≤ krTransportCost = ½` gives `krDist δ_½ δ₀ = ½`
— the
sharp mass displacement, against the loose `≤ 1` above. -/
private theorem atomize_krDist_eq_half :
    krDist dh (atomize dh Vsel Vsel_meas) = 1 / 2 := by
  rw [atomize_dh_eq_d0]
  -- primal cost is `1/2` (`atomize_krTransportCost_eq_half` after the same rewrite).
  have hcost : krTransportCost dh d0 = 1 / 2 := by
    have := atomize_krTransportCost_eq_half; rwa [atomize_dh_eq_d0] at this
  refine le_antisymm (le_trans (krDist_le_krTransportCost dh d0) (le_of_eq hcost)) ?_
  -- dual lower bound `≥ 1/2` via `pTilde(x) = x`.
  have h : (1 / 2 : ℝ) = expect dh pTilde - expect d0 pTilde := by
    rw [dh, d0, expect_dirac, expect_dirac]; norm_num [pTilde, pthalf, pt0]
  rw [h]
  exact le_csSup (bddAbove_krDist_setOf dh d0) ⟨pTilde, by simpa using pTilde_lip, rfl⟩

/-! ## Block 7: Discretization (`Discretization.lean`)

The finite law `∑ i, lam i • δ_{atom i}` carried by a simplex weight vector.  We use
`atom = (0, 1)` and `lam = (½, ½)`, so `finiteLaw = ½δ₀ + ½δ₁`. -/

/-- The two atoms `(0, 1)`. -/
private def atoms : Fin 2 → I01 := ![pt0, pt1]

/-- The uniform simplex weight `(½, ½)`. -/
private def lamHalf : stdSimplex ℝ (Fin 2) :=
  ⟨![1 / 2, 1 / 2], by
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]; norm_num⟩

/-- **Expectation against the simplex law** (`simplexToProbDist_expect`): `∑ lam i · f i`. -/
private theorem simplexToProbDist_expect_witness (f : Fin 2 → ℝ) :
    expect (simplexToProbDist lamHalf) f = ∑ i, (lamHalf : Fin 2 → ℝ) i * f i :=
  simplexToProbDist_expect lamHalf f

/-- **Expectation against the finite (pushed) law** (`finiteLaw_expect`): `∑ lam i · f (atom i)`. -/
private theorem finiteLaw_expect_witness (f : I01 → ℝ)
    (hf : AEStronglyMeasurable f (finiteLaw atoms lamHalf).toMeasure) :
    expect (finiteLaw atoms lamHalf) f = ∑ i, (lamHalf : Fin 2 → ℝ) i * f (atoms i) :=
  finiteLaw_expect atoms lamHalf f hf

/-- **Bounded-continuous expectation against the finite law**
(`finiteLaw_expect_boundedContinuous`). -/
private theorem finiteLaw_expect_boundedContinuous_witness (f : I01 →ᵇ ℝ) :
    expect (finiteLaw atoms lamHalf) f = ∑ i, (lamHalf : Fin 2 → ℝ) i * f (atoms i) :=
  finiteLaw_expect_boundedContinuous atoms lamHalf f

/-- **The finite law is continuous in the simplex weights** (`continuous_finiteLaw`). -/
private theorem continuous_finiteLaw_witness : Continuous (finiteLaw atoms) :=
  continuous_finiteLaw atoms

/-- **`simplexPush` reindexes a test sum** (`simplexPush_sum`). -/
private theorem simplexPush_sum_witness (κ : Fin 2 → Fin 2) (φ : Fin 2 → ℝ) :
    ∑ j, (simplexPush lamHalf κ : Fin 2 → ℝ) j * φ j = ∑ i, (lamHalf : Fin 2 → ℝ) i * φ (κ i) :=
  simplexPush_sum lamHalf κ φ

/-- **`simplexPush` reindexes a price sum** (`simplexPush_price_sum`). -/
private theorem simplexPush_price_sum_witness (κ : Fin 2 → Fin 2) (p : Fin 2 → ℝ) :
    ∑ j, p j * (simplexPush lamHalf κ : Fin 2 → ℝ) j = ∑ i, (lamHalf : Fin 2 → ℝ) i * p (κ i) :=
  simplexPush_price_sum lamHalf κ p

/-- **KR distance under reindexing** (`finiteLaw_krDist_push_le`): Reindexing the atoms by `κ`
moves the finite law by at most `∑ lam i · dist (atom i) (atom (κ i))`. -/
private theorem finiteLaw_krDist_push_le_witness (κ : Fin 2 → Fin 2) :
    krDist (finiteLaw atoms lamHalf) (finiteLaw atoms (simplexPush lamHalf κ))
      ≤ ∑ i, (lamHalf : Fin 2 → ℝ) i * dist (atoms i) (atoms (κ i)) :=
  finiteLaw_krDist_push_le atoms lamHalf κ

/-- The *nonuniform* simplex vector `(1, 0)` (all mass on atom `0`). -/
private def lamOne : stdSimplex ℝ (Fin 2) :=
  ⟨![1, 0], by
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]⟩

/-- The swap reindexing `κ = ![1, 0]` (exchanges the two atoms). -/
private def swapκ : Fin 2 → Fin 2 := ![1, 0]

/-- **The swap push bound is genuinely *nonzero* for a nonuniform law.** With `lam = (1, 0)` (all
mass on atom `0`), reindexing by the swap `κ = ![1, 0]` moves the mass onto atom `1`, and the push
bound `∑ lam i · dist(atom i, atom (κ i)) = 1·dist(0, 1) + 0·dist(1, 0) = dist(0, 1) = 1` — a
*nonzero* displacement. By contrast the symmetric weights `(½, ½)` give a swap bound `½·1 + ½·1 = 1`
but leave the law itself unchanged; the nonuniform vector is what makes the reindexing observable.
The general `finiteLaw_krDist_push_le_witness` then gives `krDist (push) ≤ 1` here. -/
private theorem finiteLaw_krDist_push_swap_bound_eq_one :
    (∑ i, (lamOne : Fin 2 → ℝ) i * dist (atoms i) (atoms (swapκ i))) = 1 ∧
      krDist (finiteLaw atoms lamOne) (finiteLaw atoms (simplexPush lamOne swapκ)) ≤ 1 := by
  have hbound : (∑ i, (lamOne : Fin 2 → ℝ) i * dist (atoms i) (atoms (swapκ i))) = 1 := by
    rw [Fin.sum_univ_two]
    have hl0 : (lamOne : Fin 2 → ℝ) 0 = 1 := rfl
    have hl1 : (lamOne : Fin 2 → ℝ) 1 = 0 := rfl
    have ha0 : atoms (swapκ 0) = pt1 := rfl
    have ha1 : atoms (swapκ 1) = pt0 := rfl
    rw [hl0, hl1, ha0, ha1]
    simp only [atoms, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, zero_mul, add_zero, dist_pt0_pt1]
  exact ⟨hbound, hbound ▸ finiteLaw_krDist_push_le atoms lamOne swapκ⟩

/-! ## Block 8: The finite `c`-transform (`CTransform.lean`)

`cConjugate atom L pRaw i = inf_j (pRaw j + L · dist (atom i) (atom j))` converts a raw affine
price into an `L`-Lipschitz one below it.  We use `atom = (0,1)`, `L = 1`, `pRaw = (0,2)`. -/

/-- A raw affine price vector over the atoms. -/
private def pRaw : Fin 2 → ℝ := ![0, 2]

/-- **The `c`-transform lies below the raw price** (`cConjugate_le_raw`): The conjugate never
exceeds the raw price at each atom. -/
private theorem cConjugate_le_raw_witness (i : Fin 2) : cConjugate atoms 1 pRaw i ≤ pRaw i :=
  cConjugate_le_raw i

/-- **The `c`-transform is `L`-Lipschitz on the atoms** (`cConjugate_lipschitz`). -/
private theorem cConjugate_lipschitz_witness :
    ∀ i j : Fin 2,
      cConjugate atoms 1 pRaw i - cConjugate atoms 1 pRaw j ≤ 1 * dist (atoms i) (atoms j) :=
  cConjugate_lipschitz (by norm_num)

/-- **The `c`-transform is `L`-Lipschitz (absolute form)** (`cConjugate_abs_sub_le`). -/
private theorem cConjugate_abs_sub_le_witness (i j : Fin 2) :
    |cConjugate atoms 1 pRaw i - cConjugate atoms 1 pRaw j| ≤ 1 * dist (atoms i) (atoms j) :=
  cConjugate_abs_sub_le (by norm_num) i j

/-! ### Genuine multi-atom atomization coordinates (a mass-splitting selector)

The single-atom net `{0}` forces `stdSimplex ℝ (Fin 1) = {1}`, so a coordinate membership there is
type-vacuous.  Here we atomize a genuine **two-point mixture** `splitLaw = ¼δ_{¼} + ¾δ_{¾}` through
a **threshold selector** `V(x) = 0` if `x ≤ ½`, else `1`, onto the two-atom net `Spts = {0, 1}`. The
selector routes the mass at `¼` to atom `0` and the mass at `¾` to atom `1`, so the atomized law is
the nondegenerate `¼δ₀ + ¾δ₁` and the coordinate vector is the genuine `(¼, ¾)` — both coordinates
in `(0,1)`, no longer type-forced. -/

/-- The point `¼ ∈ [0,1]` (off the net — its mass must be *moved* to an atom). -/
private def ptq : I01 := ⟨1 / 4, by norm_num⟩

/-- The point `¾ ∈ [0,1]` (off the net). -/
private def pt3q : I01 := ⟨3 / 4, by norm_num⟩

/-- The asymmetric simplex weight `(¼, ¾)`. -/
private def lam14 : stdSimplex ℝ (Fin 2) :=
  ⟨![1 / 4, 3 / 4], by
    refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
    simp [Fin.sum_univ_two]; norm_num⟩

/-- The genuine two-point mixture `splitLaw = ¼δ_{¼} + ¾δ_{¾}` (mass off the net atoms). -/
private def splitLaw : ProbDist I01 := finiteLaw ![ptq, pt3q] lam14

/-- Net atom `0` as an element of the net `Spts = {0,1}`. -/
private def a0 : Spts := ⟨pt0, Finset.mem_coe.mp pt0_mem⟩

/-- Net atom `1` as an element of the net `Spts`. -/
private def a1 : Spts := ⟨pt1, Finset.mem_coe.mp pt1_mem⟩

/-- The **mass-splitting threshold selector**: `V(x) = 0` for `x ≤ ½`, else `1`.  Genuinely two
valued (a continuous selector into the discrete net would be constant), routing `¼ ↦ 0`, `¾ ↦ 1`. -/
private def Vsplit : I01 → Spts := fun x => if (x : ℝ) ≤ 1 / 2 then a0 else a1

private theorem Vsplit_meas : Measurable Vsplit :=
  Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_const measurable_const

private theorem pt0_ne_pt1 : pt0 ≠ pt1 := by
  intro h; rw [Subtype.ext_iff] at h; norm_num [pt0, pt1] at h

/-- The net genuinely has **two** atoms, so `stdSimplex ℝ (Fin Spts.card) = stdSimplex ℝ (Fin 2)` is
a real `1`-dimensional simplex (not the singleton `Fin 1` case). -/
private theorem Spts_card : Spts.card = 2 := by
  rw [Spts, Finset.card_insert_of_notMem (by simp [Finset.mem_singleton, pt0_ne_pt1]),
    Finset.card_singleton]

/-- **The selector splits the mixture's mass across both atoms**: `atomize splitLaw V = ¼δ₀ + ¾δ₁`.
The threshold sends the mass at `¼` to atom `0` and the mass at `¾` to atom `1`, so the atomized law
is the genuine nondegenerate `(¼, ¾)` mixture — the mass-assignment / coordinate-ordering check the
single-atom Dirac net cannot perform (a swapped selector would give `¾δ₀ + ¼δ₁`). -/
private theorem atomize_split_eq :
    atomize splitLaw Vsplit Vsplit_meas = finiteLaw ![pt0, pt1] lam14 := by
  apply MeasureTheory.ProbabilityMeasure.toMeasure_injective
  have hcomp : (fun x : I01 => ((Vsplit x : I01))) ∘ (![ptq, pt3q] : Fin 2 → I01)
      = (![pt0, pt1] : Fin 2 → I01) := by
    have hVq : (Vsplit ptq : I01) = pt0 := by
      simp only [Vsplit]; rw [if_pos (by norm_num [ptq])]; rfl
    have hVq3 : (Vsplit pt3q : I01) = pt1 := by
      simp only [Vsplit]; rw [if_neg (by norm_num [pt3q])]; rfl
    funext i; fin_cases i
    · simpa [Function.comp] using hVq
    · simpa [Function.comp] using hVq3
  simp only [atomize, splitLaw, finiteLaw, ProbDist.map_toMeasure]
  rw [Measure.map_map Vsplit_meas.subtype_val (measurable_of_finite _), hcomp]

/-- **Atomization coordinates lie in the genuine `Fin 2` simplex**
(`atomize_coords_mem_stdSimplex`): atomizing the two-point mixture `splitLaw` through the threshold
selector `V` onto the two-atom net `Spts = {0,1}` gives the coordinate vector
`i ↦ splitLaw(V⁻¹{atom i})`, which lies in `stdSimplex ℝ (Fin Spts.card)` with `Spts.card = 2`
(`Spts_card`).  Unlike the single-atom case, this `1`-dimensional simplex membership is *not*
type-forced: it certifies the preimages partition with both masses nonnegative and summing to `1`.
The genuine `(¼, ¾)` split itself is identified by `atomize_split_eq`. -/
private theorem atomize_coords_mem_stdSimplex_witness :
    (fun i : Fin Spts.card => (splitLaw.toMeasure ((fun x : I01 => (Vsplit x : I01)) ⁻¹'
        {(Spts.equivFin.symm i : I01)})).toReal) ∈ stdSimplex ℝ (Fin Spts.card) :=
  atomize_coords_mem_stdSimplex splitLaw Vsplit Vsplit_meas

/-- **Expectation atomization bound** (`expect_atomize_bound`): Atomizing changes the expectation
of a Lipschitz test by at most `L · δ`.  Anchored on `pTilde` (`L = 1`) and the *uniform* selector
radius `δ = 1` (the diameter of `[0,1]`, the looser bound the general theorem uses). -/
private theorem expect_atomize_bound_witness :
    |expect dh pTilde - expect (atomize dh Vsel Vsel_meas) pTilde| ≤ 1 * 1 :=
  expect_atomize_bound Vsel Vsel_meas (by norm_num) pTilde_lip Vsel_radius dh

/-- **The *exact* expectation displacement is `1/2`, not the loose bound `1`.** Since
`atomize δ_½ V = δ₀` (`atomize_dh_eq_d0`), the test `pTilde(x) = x` moves from
`expect δ_½ pTilde = pTilde(½) = ½` to `expect δ₀ pTilde = pTilde(0) = 0`, a displacement of exactly
`½` — the actual mass movement from `½` to `0`. The uniform-radius witness above only delivers
`≤ 1`; this sharper anchor would catch a factor-two error in an intended sharp atomization
estimate. -/
private theorem expect_atomize_displacement_eq_half :
    |expect dh pTilde - expect (atomize dh Vsel Vsel_meas) pTilde| = 1 / 2 := by
  rw [atomize_dh_eq_d0, dh, d0, expect_dirac, expect_dirac]
  norm_num [pTilde, pthalf, pt0]

/-! ## Block 9: The upper-Lipschitz envelope and the vacuous-metric catch

(`UpperLipschitzEnvelope.lean`)

`upperLipschitzEnvelope V L` is the smallest `L`-KR-Lipschitz majorant of `V`.  We exercise it on
the bounded, continuous objective `V μ = expect μ id`, and end on the negative check
`krDist_pos_of_ne`. -/

/-- A concrete bounded continuous objective: `V μ = 𝔼_μ[id]` (the mean). -/
private def Vid : ProbDist I01 → ℝ := fun μ => expect μ (fun x : I01 => (x : ℝ))

private theorem Vid_cont : Continuous Vid := by
  unfold Vid
  simpa [expect] using
    MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (X := I01)
      (BoundedContinuousFunction.mkOfCompact ⟨fun x : I01 => (x : ℝ), continuous_subtype_val⟩)

private theorem Vid_usc : UpperSemicontinuous Vid := Vid_cont.upperSemicontinuous

private theorem Vid_le_one (μ : ProbDist I01) : Vid μ ≤ 1 := by
  unfold Vid expect
  calc ∫ x, (x : ℝ) ∂μ.toMeasure ≤ ∫ _, (1 : ℝ) ∂μ.toMeasure := by
        apply integral_mono_ae
        · exact (BoundedContinuousFunction.mkOfCompact
            ⟨fun x : I01 => (x : ℝ), continuous_subtype_val⟩).integrable μ.toMeasure
        · exact integrable_const 1
        · exact Filter.Eventually.of_forall (fun x => x.2.2)
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

private theorem Vid_bdd : ∃ M : ℝ, ∀ μ : ProbDist I01, |Vid μ| ≤ M :=
  ⟨1, fun μ => abs_le.mpr ⟨le_trans (by norm_num) (expect_nonneg μ _ (fun x => x.2.1)),
    Vid_le_one μ⟩⟩

private theorem Vid_bddAbove : BddAbove (Set.range Vid) :=
  ⟨1, by rintro _ ⟨μ, rfl⟩; exact Vid_le_one μ⟩

/-- The KR diameter bound `krDist μ ν ≤ 1` on `[0,1]` (from
`krDist ≤ krTransportCost ≤
∫ dist ≤ 1`). -/
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

/-- **`V` lies below its envelope** (`le_upperLipschitzEnvelope`). -/
private theorem le_upperLipschitzEnvelope_witness (μ : ProbDist I01) :
    Vid μ ≤ upperLipschitzEnvelope Vid 1 μ :=
  le_upperLipschitzEnvelope Vid_bddAbove (by norm_num) μ

/-- **`Vid` is already `1`-KR-Lipschitz.** `Vid μ = 𝔼_μ[id]` with `id = pTilde(x) = x` a
`1`-Lipschitz potential, so `Vid μ − Vid ν = expect μ pTilde − expect ν pTilde ≤ krDist μ ν` by the
KR dual. Hence its smallest `1`-KR-Lipschitz majorant is itself. -/
private theorem Vid_isKRLipschitz : IsKRLipschitz Vid 1 := by
  intro μ ν
  have hp : LipschitzWith 1 pTilde := by simpa using pTilde_lip
  have h : expect μ pTilde - expect ν pTilde ≤ krDist μ ν :=
    le_csSup (bddAbove_krDist_setOf μ ν) ⟨pTilde, hp, rfl⟩
  simpa [Vid, pTilde, one_mul] using h

/-- **The envelope of `Vid` is exactly `Vid`** (since `Vid` is already `1`-KR-Lipschitz): for every
law `μ`, `upperLipschitzEnvelope Vid 1 μ = Vid μ`. The sup `sSup {Vid ν − krDist μ ν}` is bounded
above by `Vid μ` (the KR-Lipschitz property `Vid ν − krDist μ ν ≤ Vid μ`) and attained at
`ν = μ`. -/
private theorem upperLipschitzEnvelope_Vid_eq (μ : ProbDist I01) :
    upperLipschitzEnvelope Vid 1 μ = Vid μ := by
  refine le_antisymm ?_ (le_upperLipschitzEnvelope_witness μ)
  refine csSup_le (upperLipschitzEnvelope_values_nonempty Vid 1 μ) ?_
  rintro y ⟨ν, rfl⟩
  -- `Vid ν − 1·krDist μ ν ≤ Vid μ` since `Vid ν − Vid μ ≤ krDist ν μ = krDist μ ν`.
  have h := Vid_isKRLipschitz ν μ
  rw [one_mul, krDist_comm ν μ] at h
  linarith

/-- **The envelope evaluated at `δ₀` is `0`** (the sharp value `le_upperLipschitzEnvelope` alone
does
not give): `upperLipschitzEnvelope Vid 1 δ₀ = Vid δ₀ = 𝔼_{δ₀}[id] = 0`. -/
private theorem upperLipschitzEnvelope_Vid_d0 : upperLipschitzEnvelope Vid 1 d0 = 0 := by
  rw [upperLipschitzEnvelope_Vid_eq, Vid, d0, expect_dirac]; simp [pt0]

/-- **The envelope evaluated at `δ₁` is `1`**: `upperLipschitzEnvelope Vid 1 δ₁ = Vid δ₁ =
𝔼_{δ₁}[id] = 1`. So the envelope is the genuine mean functional, not just *some* majorant — a
constant or sign-flipped majorant would fail these two values. -/
private theorem upperLipschitzEnvelope_Vid_d1 : upperLipschitzEnvelope Vid 1 d1 = 1 := by
  rw [upperLipschitzEnvelope_Vid_eq, Vid, d1, expect_dirac]; simp [pt1]

/-- **The envelope is `L`-KR-Lipschitz** (`upperLipschitzEnvelope_isKRLipschitz`). -/
private theorem upperLipschitzEnvelope_isKRLipschitz_witness :
    IsKRLipschitz (upperLipschitzEnvelope Vid 1) 1 :=
  upperLipschitzEnvelope_isKRLipschitz Vid_bddAbove (by norm_num)

/-- **The envelope is bounded** (`upperLipschitzEnvelope_bdd`): `|envelope| ≤ M + L·D` with
`M = 1`, `L = 1`, `D = 1` (the KR diameter bound). -/
private theorem upperLipschitzEnvelope_bdd_witness (μ : ProbDist I01) :
    |upperLipschitzEnvelope Vid 1 μ| ≤ 1 + 1 * 1 :=
  upperLipschitzEnvelope_bdd (L := 1) (M := 1) (D := 1)
    (by norm_num) (by norm_num) (fun μ => (abs_le.mpr
      ⟨le_trans (by norm_num) (expect_nonneg μ _ (fun x => x.2.1)), Vid_le_one μ⟩))
    krDist_le_one μ

/-- **The envelope is upper-semicontinuous** (`upperLipschitzEnvelope_usc`). -/
private theorem upperLipschitzEnvelope_usc_witness :
    UpperSemicontinuous (upperLipschitzEnvelope Vid 1) :=
  upperLipschitzEnvelope_usc Vid_bddAbove (by norm_num) Vid_usc

/-- **The finite objective is bounded** (`finiteObjective_bdd`). -/
private theorem finiteObjective_bdd_witness :
    ∃ M : ℝ, ∀ lam : Fin 2 → ℝ, |finiteObjective Vid atoms lam| ≤ M :=
  finiteObjective_bdd atoms Vid_bdd

/-- **The finite objective is upper-semicontinuous on the simplex** (`finiteObjective_usc`). -/
private theorem finiteObjective_usc_witness :
    UpperSemicontinuousOn (finiteObjective Vid atoms) (stdSimplex ℝ (Fin 2)) :=
  finiteObjective_usc atoms Vid_usc

/-- **The KR metric vanishes only on the diagonal** (`krDist_eq_zero_iff`):
`krDist μ ν = 0 ↔ μ = ν`.  A vacuous metric (always `0`) would make the `→` direction false. -/
private theorem krDist_eq_zero_iff_witness {μ ν : ProbDist I01} : krDist μ ν = 0 ↔ μ = ν :=
  krDist_eq_zero_iff

/-- **The KR metric strictly separates distinct laws** (`krDist_pos_of_ne`): `0 < krDist δ₀ δ₁`.
This is the central negative check the work item demands — the metric is *not* vacuous. -/
private theorem krDist_pos_of_ne_witness : 0 < krDist d0 d1 := krDist_pos_of_ne d0_ne_d1

end EconlibTest.Optimization.OptimalTransportDuality

end
