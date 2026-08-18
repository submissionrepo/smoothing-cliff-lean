/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.LinearAlgebra.FarkasCone

/-!
# Balanced collections and finite core feasibility

This file contains the finite linear-programing form of the Bondareva–Shapley theorem (Bondareva
1963; Shapley 1967) for an abstract value function `v : Finset α → ℝ` on a finite type. Core
feasibility — existence of a payoff vector that is efficient and gives every coalition at least its
value — is encoded as membership in the image of a slack cone, and a Farkas alternative identifies
its failure with a balanced collection of weights that strictly improves on the grand-coalition
value. Game-theoretic TU games specialize the main equivalence by taking `v` to be the
characteristic function.

## Main definitions

* `CoalitionCoreFeasible`: Existence of an efficient payoff vector dominating every coalition value.
* `IsBalancedCollection`: A balanced family of coalition weights.
* `SatisfiesBalancedInequalities`: The balancedness condition dual to core feasibility.
* `coreSlackCone`, `coreFeasibilityMap`, `coreTarget`: The Farkas encoding of core feasibility.

## Main statements

* `satisfiesBalancedInequalities_of_coreFeasible`: The weak-duality direction.
* `coreFeasible_iff_satisfiesBalancedInequalities`: The Bondareva–Shapley/Farkas equivalence.

## References

* Bondareva, Olga N. 1963. “Some Applications of Linear Programing Methods to the Theory of
  Cooperative Games.” *Problemy Kibernetiki* 10 : 119–39.
* Shapley, Lloyd S. 1967. “On Balanced Sets and Cores.” *Naval Research Logistics Quarterly* 14
  (4): 453–60. [https://doi.org/10.1002/nav.3800140404](https://doi.org/10.1002/nav.3800140404).

## Tags

cooperative game, balancedness, core, Bondareva–Shapley, Farkas
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

section CoalitionFarkasCoding

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A collision-free natural-number code for finite coalitions. This is only an indexing device for
Optlib's `Finset ℕ` Farkas theorem. -/
noncomputable def coalitionCode (S : Finset α) : ℕ := Nat.succ ((Fintype.equivFin (Finset α)) S).val

/-- The finite set of natural-number codes for all coalitions. -/
noncomputable def coalitionCodeSet : Finset ℕ :=
  (Finset.univ : Finset (Finset α)).image (coalitionCode (α := α))

/-- The finite set of natural-number codes for all nonempty coalitions. -/
noncomputable def nonemptyCoalitionCodeSet : Finset ℕ :=
  ((Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty)).image (coalitionCode (α := α))

omit [DecidableEq α] in
/-- The coalition code is injective. -/
theorem coalitionCode_injective :
    Function.Injective (coalitionCode (α := α)) := by
  intro S T hST
  dsimp [coalitionCode] at hST
  apply (Fintype.equivFin (Finset α)).injective
  ext
  exact Nat.succ.inj hST

omit [DecidableEq α] in
/-- Every coalition's code lies in the set of all coalition codes. -/
@[simp] theorem coalitionCode_mem (S : Finset α) :
    coalitionCode (α := α) S ∈ coalitionCodeSet (α := α) := by simp [coalitionCodeSet]

omit [DecidableEq α] in
/-- A nonempty coalition's code lies in the set of nonempty-coalition codes. -/
@[simp] theorem coalitionCode_mem_nonempty {S : Finset α} (hS : S.Nonempty) :
    coalitionCode (α := α) S ∈ nonemptyCoalitionCodeSet (α := α) := by
  exact Finset.mem_image.mpr ⟨S, by simp [hS], rfl⟩

omit [DecidableEq α] in
/-- A sum over the nonempty-coalition code set equals the sum over nonempty coalitions of the
function precomposed with the coalition code. -/
theorem sum_nonemptyCoalitionCodeSet {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) :
    (∑ k : nonemptyCoalitionCodeSet (α := α), f k) =
      ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
        f (coalitionCode (α := α) S) := by
  rw [← Finset.sum_subtype (s := nonemptyCoalitionCodeSet (α := α)) (h := fun k => Iff.rfl) f,
      nonemptyCoalitionCodeSet, Finset.sum_image]
  intro _ _ _ _ hST
  exact coalitionCode_injective (α := α) hST

/-- Decode a natural-number coalition code, defaulting to `∅` away from the finite code set. -/
noncomputable def coalitionDecode (k : ℕ) : Finset α :=
  if h : ∃ S : Finset α, coalitionCode (α := α) S = k then Classical.choose h else ∅

omit [DecidableEq α] in
/-- Decoding the code of a coalition recovers the coalition. -/
@[simp] theorem coalitionDecode_code (S : Finset α) :
    coalitionDecode (α := α) (coalitionCode (α := α) S) = S := by
  dsimp [coalitionDecode]
  rw [dif_pos ⟨S, rfl⟩]
  exact coalitionCode_injective (α := α) (Classical.choose_spec
    (show ∃ T : Finset α, coalitionCode (α := α) T = coalitionCode (α := α) S from ⟨S, rfl⟩))

/-- The inner product of a payoff vector with the negated indicator of `S` is minus the sum over
`S`. -/
theorem sum_coalition_indicator_neg (S : Finset α) (x : α → ℝ) :
    (∑ i : α, (if i ∈ S then (-1 : ℝ) else 0) * x i) = -∑ i ∈ S, x i := by
  simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_mem_eq, Finset.sum_neg_distrib]

omit [DecidableEq α] in
/-- Inner product against the augmented grand-coalition row: The scalar coordinate scaled by `r`
minus the total payoff over all players. -/
theorem inner_augVector_grand
    (r : ℝ) (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    inner ℝ (augVector (α := α) r (fun _ : α => -1)) z =
      r * augScalar z - ∑ i : α, augPlayer z i := by rw [inner_augVector]; aesop

/-- Inner product against the augmented row for coalition `S`: The scalar coordinate scaled by
`v S` minus the payoff summed over `S`. -/
theorem inner_augVector_coalition
    (v : Finset α → ℝ) (S : Finset α)
    (z : EuclideanSpace ℝ (Fin (Fintype.card (Unit ⊕ α)))) :
    inner ℝ
        (augVector (α := α) (v S)
          (fun i : α => if i ∈ S then (-1 : ℝ) else 0)) z =
      v S * augScalar z - ∑ i ∈ S, augPlayer z i := by
  rw [inner_augVector, sum_coalition_indicator_neg]
  ring

end CoalitionFarkasCoding

/-- The cone used in the finite Farkas encoding of core feasibility. The first coordinate is an
unrestricted payoff vector, while the second coordinate is a nonnegative slack vector indexed by
coalitions. -/
noncomputable def coreSlackCone :
    ProperCone ℝ ((α → ℝ) × (Finset α → ℝ)) :=
  (ProperCone.positive ℝ (Finset α → ℝ)).comap (ContinuousLinearMap.snd ℝ (α → ℝ) (Finset α → ℝ))

/-- The linear map sending a payoff vector and nonnegative coalition slacks to the grand-coalition
equality and all coalition equality right-hand sides. -/
noncomputable def coreFeasibilityMap :
    ((α → ℝ) × (Finset α → ℝ)) →L[ℝ] (ℝ × (Finset α → ℝ)) :=
  let L : ((α → ℝ) × (Finset α → ℝ)) →ₗ[ℝ] (ℝ × (Finset α → ℝ)) :=
    { toFun := fun p =>
        (∑ i : α, p.1 i, fun S : Finset α => ∑ i ∈ S, p.1 i - p.2 S)
      map_add' := by
        intro p q
        ext S
        all_goals simp [Finset.sum_add_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      map_smul' := by
        intro r p
        ext S
        all_goals simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.smul_snd,
          Real.ringHom_apply, Prod.smul_mk]
        · rw [Finset.mul_sum]
        · rw [← Finset.mul_sum S (fun i => p.1 i) r]; ring }
  LinearMap.toContinuousLinearMap L

/-- Right-hand side vector for the core feasibility system. -/
noncomputable def coreTarget (v : Finset α → ℝ) : ℝ × (Finset α → ℝ) := (v Finset.univ, v)

/-- Feasible core payoff vectors for a finite set system: Total payoff equals `v univ`, and every
coalition receives at least its value. -/
def CoalitionCoreFeasible (v : Finset α → ℝ) : Prop :=
  ∃ x : α → ℝ, (∑ i : α, x i = v Finset.univ) ∧ ∀ S : Finset α, v S ≤ ∑ i ∈ S, x i

omit [DecidableEq α] in
/-- Core feasibility is exact membership in the finite slack-cone image. -/
theorem coalitionCoreFeasible_iff_coreTarget_mem
    (v : Finset α → ℝ) :
    CoalitionCoreFeasible v ↔ coreTarget v ∈
      (coreSlackCone (α := α)).toPointedCone.map (coreFeasibilityMap (α := α)).toLinearMap := by
  constructor
  · rintro ⟨x, hx_eff, hx_core⟩
    let z : Finset α → ℝ := fun S => ∑ i ∈ S, x i - v S
    refine ⟨(x, z), ?_, ?_⟩
    · intro S
      dsimp [coreSlackCone, z]
      exact sub_nonneg.mpr (hx_core S)
    · ext S
      · simp [coreFeasibilityMap, coreTarget, hx_eff]
      · simp [coreFeasibilityMap, coreTarget, z]
  · rintro ⟨p, hp, hp_map⟩
    refine ⟨p.1, ?_, ?_⟩
    · have h := congrArg Prod.fst hp_map
      simpa [coreFeasibilityMap, coreTarget] using h
    · intro S
      have hS := congrFun (congrArg Prod.snd hp_map) S
      have hz : 0 ≤ p.2 S := by
        simpa [coreSlackCone] using hp S
      have hv_eq : v S = ∑ i ∈ S, p.1 i - p.2 S := by
        simpa [coreFeasibilityMap, coreTarget] using hS.symm
      rw [hv_eq]
      linarith

/-- A **balanced collection** of coalition weights: Nonnegative, and summing to one over the
coalitions containing each fixed player. -/
def IsBalancedCollection (w : Finset α → ℝ) : Prop :=
  (∀ S, 0 ≤ w S) ∧
    ∀ i : α, ∑ S ∈ Finset.univ.powerset.filter (fun S : Finset α => i ∈ S), w S = 1

/-- Balancedness condition dual to core feasibility. -/
def SatisfiesBalancedInequalities (v : Finset α → ℝ) : Prop :=
  ∀ w : Finset α → ℝ, IsBalancedCollection w →
    ∑ S ∈ Finset.univ.powerset, w S * v S ≤ v Finset.univ

/-- Core feasibility implies the balanced inequalities. This is the weak-duality direction of
Bondareva–Shapley. -/
theorem satisfiesBalancedInequalities_of_coreFeasible
    {v : Finset α → ℝ} (hcore : CoalitionCoreFeasible v) :
    SatisfiesBalancedInequalities v := by
  rintro w ⟨hw_nonneg, hw_bal⟩
  rcases hcore with ⟨x, hx_eff, hx_core⟩
  calc
    ∑ S ∈ (Finset.univ : Finset α).powerset, w S * v S
        ≤ ∑ S ∈ (Finset.univ : Finset α).powerset, w S * (∑ i ∈ S, x i) := by
          refine Finset.sum_le_sum ?_
          intro S hS
          exact mul_le_mul_of_nonneg_left (hx_core S) (hw_nonneg S)
    _ = ∑ i : α, x i := by
          calc
            ∑ S ∈ (Finset.univ : Finset α).powerset, w S * (∑ i ∈ S, x i)
                = ∑ i : α, ∑ S ∈ (Finset.univ : Finset α).powerset.filter
                    (fun S : Finset α => i ∈ S), w S * x i := by
                  simp_rw [Finset.mul_sum]
                  exact Finset.sum_comm' (fun S i => by simp)
              _ = ∑ i : α, x i := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [← Finset.sum_mul, hw_bal i, one_mul]
    _ = v Finset.univ := hx_eff

/-- On an empty player set, the balanced inequalities imply core feasibility (the unique payoff
vector is feasible). -/
theorem coalitionCoreFeasible_of_isEmpty
    [IsEmpty α] {v : Finset α → ℝ}
    (hbal : SatisfiesBalancedInequalities v) :
    CoalitionCoreFeasible v := by
  -- On an empty player set every nonnegative constant weight family is balanced
  -- (the per-player condition is vacuous).
  have hconst_bal : ∀ c : ℝ, 0 ≤ c → IsBalancedCollection (α := α) (fun _ => c) :=
    fun c hc => ⟨fun S => hc, fun i => isEmptyElim i⟩
  have hle0 : v Finset.univ ≤ 0 := by
    have htwo : 2 * v Finset.univ ≤ v Finset.univ := by
      simpa using hbal _ (hconst_bal 2 (by norm_num))
    linarith
  have hge0 : 0 ≤ v Finset.univ := by
    have hzero : 0 * v Finset.univ ≤ v Finset.univ := by
      simpa using hbal _ (hconst_bal 0 le_rfl)
    linarith
  have hzero_empty : v ∅ = 0 := by
    simpa [Finset.univ_eq_empty] using le_antisymm hle0 hge0
  refine ⟨fun i => isEmptyElim i, ?_, ?_⟩
  · simp [hzero_empty]
  · intro S
    have hS : S = Finset.univ := by
      ext i
      exact isEmptyElim i
    subst S
    simp [hzero_empty]

/-- With at least one player, the balanced inequalities force the empty coalition's value to be
nonpositive (apply the collection putting weight one on `∅` and on the grand coalition). -/
theorem empty_value_nonpos_of_satisfiesBalancedInequalities
    [Nonempty α] {v : Finset α → ℝ}
    (hbal : SatisfiesBalancedInequalities v) :
    v ∅ ≤ 0 := by
  let w : Finset α → ℝ := fun S => if S = ∅ then 1 else if S = Finset.univ then 1 else 0
  have hw : IsBalancedCollection (α := α) w := by
    constructor
    · intro S
      by_cases hS_empty : S = ∅
      · simp [w, hS_empty]
      · by_cases hS_univ : S = Finset.univ
        · simp [w, hS_univ]
        · simp [w, hS_empty, hS_univ]
    · intro i
      rw [Finset.sum_eq_single (Finset.univ : Finset α)]
      · simp [w]
      · intro S hS hSne
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        have hiS : i ∈ S := hS.2
        have hS_ne_empty : S ≠ ∅ := by
          intro h
          subst S
          simp at hiS
        simp [w, hS_ne_empty, hSne]
      · intro hnot
        exact absurd (by simp) hnot
  have hineq := hbal w hw
  have hsum :
      ∑ S ∈ (Finset.univ : Finset α).powerset, w S * v S =
        v ∅ + v Finset.univ := by
    rw [Finset.sum_eq_add_sum_diff_singleton (i := (∅ : Finset α))]
    · rw [Finset.sum_eq_single (Finset.univ : Finset α)]
      · simp [w]
      · intro S hS hSne
        have hS_ne_empty : S ≠ ∅ := by
          intro h
          subst S
          simp at hS
        simp [w, hS_ne_empty, hSne]
      · intro hnot
        rcases (inferInstance : Nonempty α) with ⟨i⟩
        exact absurd (by simp [Finset.ne_empty_of_mem (Finset.mem_univ i)]) hnot
    · simp
  rw [hsum] at hineq
  linarith

omit [DecidableEq α] in
/-- A scaled sub-solution yields a core-feasible payoff. If `t < 0`, the total of `y` equals
`v univ * t`, and each coalition's `y`-sum is at most `v S * t`, then the rescaled payoff `y i / t`
is efficient and dominates every coalition value. This is the primal half of the Farkas argument:
a certificate `z` for the alternative system produces `t := augScalar z` and `y := augPlayer z`
satisfying these hypotheses. -/
theorem coalitionCoreFeasible_of_scaled_subsolution {v : Finset α → ℝ}
    (t : ℝ) (y : α → ℝ) (ht : t < 0)
    (heff : ∑ i : α, y i = v Finset.univ * t)
    (hsub : ∀ S : Finset α, ∑ i ∈ S, y i ≤ v S * t) :
    CoalitionCoreFeasible v := by
  refine ⟨fun i => y i / t, ?_, ?_⟩
  · rw [← Finset.sum_div, heff, mul_div_assoc, div_self (ne_of_lt ht), mul_one]
  · intro S
    rw [← Finset.sum_div, le_div_iff_of_neg ht]
    linarith [hsub S]

/-- Normalizing a nonnegative coalition-weight family that covers every player with total weight
`d > 0` yields a balanced collection supported on nonempty coalitions. The weights `g S / d` are
nonnegative and, summed over the coalitions containing a fixed player, telescope to `d / d = 1`. -/
theorem isBalancedCollection_of_coverage {g : Finset α → ℝ} {d : ℝ}
    (hd : 0 < d) (hg : ∀ S : Finset α, S.Nonempty → 0 ≤ g S)
    (hcov : ∀ i : α,
      ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∈ S), g S = d) :
    IsBalancedCollection (fun S => if S.Nonempty then g S / d else 0) := by
  refine ⟨fun S => ?_, fun i => ?_⟩
  · by_cases hS : S.Nonempty
    · simp [hS, div_nonneg (hg S hS) hd.le]
    · simp [hS]
  · have hfilter : ∀ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∈ S),
        (if S.Nonempty then g S / d else 0) = g S / d := by
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      rw [if_pos ⟨i, hS.2⟩]
    rw [Finset.sum_congr rfl hfilter, ← Finset.sum_div, hcov i, div_self (ne_of_gt hd)]

omit [DecidableEq α] in
/-- The normalized coverage collection strictly beats the grand-coalition value whenever the scalar
Farkas row reads `1 = -d * v univ + ∑_{S ≠ ∅} g S * v S` with `d > 0`. Paired with
`isBalancedCollection_of_coverage`, this exhibits the balanced collection that witnesses the failure
of core feasibility. -/
theorem lt_weightedValue_of_coverage {v g : Finset α → ℝ} {d : ℝ} (hd : 0 < d)
    (hscalar : 1 = -d * v Finset.univ +
      ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty), g S * v S) :
    v Finset.univ <
      ∑ S ∈ (Finset.univ : Finset α).powerset, (if S.Nonempty then g S / d else 0) * v S := by
  have hpayoff :
      ∑ S ∈ (Finset.univ : Finset α).powerset, (if S.Nonempty then g S / d else 0) * v S =
        (∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty), g S * v S) / d := by
    rw [Finset.powerset_univ]
    calc
      ∑ S : Finset α, (if S.Nonempty then g S / d else 0) * v S
          = ∑ S : Finset α, if S.Nonempty then g S * v S / d else 0 := by
            refine Finset.sum_congr rfl (fun S _ => ?_)
            by_cases hS : S.Nonempty <;> simp [hS, div_mul_eq_mul_div]
        _ = ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
              g S * v S / d := by rw [Finset.sum_filter]
        _ = (∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
              g S * v S) / d := by rw [Finset.sum_div]
  rw [hpayoff, lt_div_iff₀ hd]
  nlinarith [hscalar]

/-- In the Farkas dual representation of an infeasible core, the multiplier `lambda` on the
efficiency row is strictly negative. Nonpositivity comes from the per-player rows (a sum of
nonpositive terms), and `lambda = 0` would force every coalition multiplier to vanish, collapsing
the scalar row to the false identity `1 = 0`. -/
theorem dual_efficiency_multiplier_neg [Nonempty α] {v : Finset α → ℝ} {lambda : ℝ}
    {mu : nonemptyCoalitionCodeSet (α := α) → ℝ} (hmu_nonneg : ∀ k, 0 ≤ mu k)
    (hscalar_rep : 1 = lambda * v Finset.univ +
      ∑ k : nonemptyCoalitionCodeSet (α := α), mu k * v (coalitionDecode (α := α) k))
    (hplayer_rep : ∀ i : α, 0 = -lambda +
      ∑ k : nonemptyCoalitionCodeSet (α := α),
        if i ∈ coalitionDecode (α := α) k then -mu k else 0) :
    lambda < 0 := by
  have hlambda_nonpos : lambda ≤ 0 := by
    obtain ⟨i⟩ := ‹Nonempty α›
    have hsum_nonpos :
        (∑ k : nonemptyCoalitionCodeSet (α := α),
          if i ∈ coalitionDecode (α := α) k then -mu k else 0) ≤ 0 :=
      Fintype.sum_nonpos (fun k => by
        by_cases hik : i ∈ coalitionDecode (α := α) k
        · simp [hik, hmu_nonneg k]
        · simp [hik])
    linarith [hplayer_rep i]
  have hlambda_ne_zero : lambda ≠ 0 := by
    intro hlambda_zero
    have hmu_zero : ∀ k, mu k = 0 := by
      intro k
      rcases Finset.mem_image.mp k.2 with ⟨S, hS_mem, hS_code⟩
      have hS_nonempty : S.Nonempty := by simpa using hS_mem
      rcases hS_nonempty with ⟨i, hiS⟩
      have hdecode : coalitionDecode (α := α) k = S := by rw [← hS_code]; simp
      have hsum_eq :
          (∑ kk : nonemptyCoalitionCodeSet (α := α),
            if i ∈ coalitionDecode (α := α) kk then -mu kk else 0) = 0 := by
        linarith [hplayer_rep i]
      have hnonpos :
          (fun kk : nonemptyCoalitionCodeSet (α := α) =>
            if i ∈ coalitionDecode (α := α) kk then -mu kk else 0) ≤ 0 := by
        intro kk
        by_cases hikk : i ∈ coalitionDecode (α := α) kk
        · simp [hikk, hmu_nonneg kk]
        · simp [hikk]
      have hterm := congrFun ((Fintype.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum_eq) k
      have : -mu k = 0 := by simpa [hdecode, hiS] using hterm
      linarith
    have hsum_zero :
        (∑ k : nonemptyCoalitionCodeSet (α := α), mu k * v (coalitionDecode (α := α) k)) = 0 := by
      simp [hmu_zero]
    rw [hsum_zero] at hscalar_rep
    simp [hlambda_zero] at hscalar_rep
  exact lt_of_le_of_ne hlambda_nonpos hlambda_ne_zero

/-- **Bondareva–Shapley/Farkas theorem** (Bondareva 1963; Shapley 1967) for finite coalition
systems: Core feasibility is equivalent to the balanced inequalities. -/
theorem coreFeasible_iff_satisfiesBalancedInequalities
    (v : Finset α → ℝ) :
    CoalitionCoreFeasible v ↔ SatisfiesBalancedInequalities v := by
  constructor
  · exact satisfiesBalancedInequalities_of_coreFeasible
  · intro hbal
    by_cases hα : Nonempty α
    · haveI : Nonempty α := hα
      let n := Fintype.card (Unit ⊕ α)
      let τ : Finset ℕ := {0}
      let σ : Finset ℕ := nonemptyCoalitionCodeSet (α := α)
      let a : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
        if k = 0 then augVector (α := α) (v Finset.univ) (fun _ : α => -1) else 0
      let b : ℕ → EuclideanSpace ℝ (Fin n) := fun k =>
        augVector (α := α) (v (coalitionDecode (α := α) k))
          (fun i : α => if i ∈ coalitionDecode (α := α) k then (-1 : ℝ) else 0)
      let c : EuclideanSpace ℝ (Fin n) := augVector (α := α) 1 (fun _ : α => 0)
      have hEmpty : v ∅ ≤ 0 := empty_value_nonpos_of_satisfiesBalancedInequalities (α := α) hbal
      by_contra hnot
      have hnotCore : ¬ CoalitionCoreFeasible v := hnot
      have hno : ¬ (∃ z : EuclideanSpace ℝ (Fin n),
          (∀ i ∈ τ, inner ℝ (a i) z = 0) ∧ (∀ i ∈ σ, inner ℝ (b i) z ≥ 0) ∧ inner ℝ c z < 0) := by
        rintro ⟨z, haz, hbz, hcz⟩
        apply hnotCore
        let t : ℝ := augScalar (α := α) z
        let y : α → ℝ := augPlayer (α := α) z
        have hc : t < 0 := by
          have hc_eq : inner ℝ c z = t := by dsimp [c, t]; rw [inner_augVector]; simp
          linarith
        refine coalitionCoreFeasible_of_scaled_subsolution t y hc ?_ ?_
        · -- the grand-coalition row forces total payoff `∑ y = v univ * t`
          have ha0 := haz 0 (by simp [τ])
          have ha0_inner :
              inner ℝ (augVector (α := α) (v Finset.univ) (fun _ : α => -1)) z = 0 := by
            simpa [a] using ha0
          have ha0' : v Finset.univ * t - ∑ i : α, y i = 0 := by
            simpa [t, y, inner_augVector_grand] using ha0_inner
          linarith
        · -- each nonempty coalition's row bounds its `y`-sum; the empty one uses `v ∅ ≤ 0`
          intro S
          by_cases hS : S.Nonempty
          · have hSmem : coalitionCode (α := α) S ∈ σ := by
              simpa [σ] using coalitionCode_mem_nonempty (α := α) hS
            have hbS := hbz (coalitionCode (α := α) S) hSmem
            have hbS_inner : 0 ≤ inner ℝ (augVector (α := α) (v S)
                (fun i : α => if i ∈ S then (-1 : ℝ) else 0)) z := by
              simpa [b] using hbS
            have hbS' : 0 ≤ v S * t - ∑ i ∈ S, y i := by
              simpa [t, y, inner_augVector_coalition] using hbS_inner
            linarith
          · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
            subst S
            simp only [Finset.sum_empty]
            nlinarith [hEmpty, hc]
      have hfarkas : ∃ (lam : τ → ℝ), ∃ (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧ c =
        Finset.sum Finset.univ (fun i ↦ lam i • a i) +
          Finset.sum Finset.univ (fun i ↦ mu i • b i) := by
        exact (Farkas (τ := τ) (σ := σ) (a := a) (b := b) (c := c)).mpr hno
      rcases hfarkas with ⟨lam, mu, hmu_nonneg, hc_rep⟩
      let lambda : ℝ := lam ⟨0, by simp [τ]⟩
      have hscalar_rep : 1 = lambda * v Finset.univ +
          ∑ k : σ, mu k * v (coalitionDecode (α := α) k) := by
        have h := congrArg (fun z => augScalar (α := α) z) hc_rep
        simpa [c, a, b, lambda, n, τ] using h
      have hplayer_rep (i : α) : 0 = -lambda + ∑ k : σ,
          if i ∈ coalitionDecode (α := α) k then -mu k else 0 := by
        have h := congrArg (fun z => augPlayer (α := α) z i) hc_rep
        simpa [c, a, b, lambda, n, τ] using h
      have hlambda_neg : lambda < 0 :=
        dual_efficiency_multiplier_neg hmu_nonneg hscalar_rep hplayer_rep
      let muAt : ℕ → ℝ := fun k => if hk : k ∈ σ then mu ⟨k, hk⟩ else 0
      have hscalar_coalitions : 1 = lambda * v Finset.univ +
        ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
          muAt (coalitionCode (α := α) S) * v S := by
        have hsum := sum_nonemptyCoalitionCodeSet (α := α)
          (f := fun k => muAt k * v (coalitionDecode (α := α) k))
        aesop
      have hplayer_coalitions (i : α) :
          0 = -lambda - ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∈ S),
            muAt (coalitionCode (α := α) S) := by
        have hsum := sum_nonemptyCoalitionCodeSet (α := α)
          (f := fun k => if i ∈ coalitionDecode (α := α) k then -muAt k else 0)
        have hplayer_muAt :
            0 = -lambda + ∑ k : σ, if i ∈ coalitionDecode (α := α) k then -muAt k else 0 := by
          simpa [muAt] using hplayer_rep i
        rw [hplayer_muAt]
        have hsum_codes : (∑ k : σ, if i ∈ coalitionDecode (α := α) k then -muAt k else 0) =
          ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
            (if i ∈ S then -muAt (coalitionCode (α := α) S) else 0) := by simpa [σ] using hsum
        calc
          -lambda + (∑ k : σ, if i ∈ coalitionDecode (α := α) k then -muAt k else 0)
            = -lambda + ∑ S ∈ (Finset.univ : Finset (Finset α)).filter (fun S => S.Nonempty),
              (if i ∈ S then -muAt (coalitionCode (α := α) S) else 0) := by
            rw [hsum_codes]
          _ = -lambda - ∑ S ∈ (Finset.univ : Finset α).powerset.filter (fun S : Finset α => i ∈ S),
              muAt (coalitionCode (α := α) S) := by
            have hfilter : (((Finset.univ : Finset (Finset α)).filter fun S => S.Nonempty).filter
                  (fun S : Finset α => i ∈ S)) =
                (Finset.univ : Finset (Finset α)).filter (fun S : Finset α => i ∈ S) := by
              ext S
              grind
            rw [Finset.powerset_univ, ← Finset.sum_filter, hfilter, Finset.sum_neg_distrib]
            ring
      let w : Finset α → ℝ := fun S =>
        if S.Nonempty then muAt (coalitionCode (α := α) S) / (-lambda) else 0
      have hw : IsBalancedCollection (α := α) w :=
        isBalancedCollection_of_coverage (g := fun S => muAt (coalitionCode (α := α) S))
          (d := -lambda) (neg_pos.mpr hlambda_neg) (fun S _ => by grind)
          (fun i => by linarith [hplayer_coalitions i])
      have hstrict : v Finset.univ < ∑ S ∈ (Finset.univ : Finset α).powerset, w S * v S :=
        lt_weightedValue_of_coverage (g := fun S => muAt (coalitionCode (α := α) S))
          (d := -lambda) (neg_pos.mpr hlambda_neg) (by rw [neg_neg]; exact hscalar_coalitions)
      linarith [hbal w hw]
    · haveI : IsEmpty α := ⟨fun i => hα ⟨i⟩⟩
      exact coalitionCoreFeasible_of_isEmpty (α := α) hbal

end Econlib.GameTheory
