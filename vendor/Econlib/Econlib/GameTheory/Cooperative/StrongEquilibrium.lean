/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Core
public import Econlib.GameTheory.Cooperative.StrategicBridge

/-!
# Strong equilibrium implies α-core membership

Given a `FiniteStrategicGame G`, a **TU strong equilibrium** is a mixed-strategy profile
`σ : G.MixedStrategy` such that no coalition `S` can correlate-deviate to improve its total
coalitional payoff against the complement's product-of-marginals strategy. This file shows that the
payoff vector `fun i => G.expectedPayoff i σ` of a TU strong equilibrium lies in the α-core of the
derived TU game `G.toTUGameOn` (Aumann 1959).

## Main definitions

* `FiniteStrategicGame.coalitionMarginal` and `FiniteStrategicGame.complementMarginal`: Product
  distributions induced by a mixed-strategy profile.
* `FiniteStrategicGame.IsTUStrongEquilibrium`: No coalition can profitably correlate-deviate
  against the complement marginals.
* `FiniteStrategicGame.payoffAtMixed`: The expected-payoff vector as a TU payoff vector.

## Main statements

* `FiniteStrategicGame.coalitionExpectedPayoff_at_marginals`: The product-of-marginals payoff
  identity.
* `FiniteStrategicGame.isTUStrongEquilibrium_implies_isCore`: A TU strong equilibrium induces an
  α-core allocation.

## Notes

The bridge to the α-core rests on the marginal-at-`σ` identity
`coalitionExpectedPayoff_at_marginals`: At the product-of-marginals strategy the bilinear
coalitional payoff factors through the original `expectedPayoff` of each player.

## References

* Aumann, Robert J. 1959. “Acceptable Points in General Cooperative n-Person Games.” In
  *Contributions to the Theory of Games, Volume IV*, edited by A. W. Tucker and R. D. Luce.
  Princeton University Press.

## Tags

cooperative game, strong equilibrium, core
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace FiniteStrategicGame

variable (G : FiniteStrategicGame) (S : Finset G.Player)

/-! ## Marginal distributions induced by a mixed-strategy profile -/

/-- The coalition's correlated joint mixed strategy at `σ`: The product distribution of the
marginals `σ i` for `i ∈ S`. -/
noncomputable def coalitionMarginal (σ : G.MixedStrategy) :
    stdSimplex ℝ (G.CoalitionAction S) :=
  ⟨fun aS => ∏ i : {x : G.Player // x ∈ S}, σ i.val (aS i),
    by
      refine ⟨fun aS => Finset.prod_nonneg (fun i _ => stdSimplex.zero_le _ _), ?_⟩
      rw [show ∑ aS : G.CoalitionAction S,
            ∏ i : {x : G.Player // x ∈ S}, σ i.val (aS i) =
          ∏ i : {x : G.Player // x ∈ S}, ∑ b : G.Action i.val, σ i.val b from ?_]
      · refine Finset.prod_eq_one (fun i _ => stdSimplex.sum_eq_one _)
      · rw [← Fintype.piFinset_univ]
        exact (Finset.prod_univ_sum (fun _ => Finset.univ) _).symm⟩

/-- The complement's correlated joint mixed strategy at `σ`. -/
noncomputable def complementMarginal (σ : G.MixedStrategy) :
    stdSimplex ℝ (G.ComplementAction S) :=
  ⟨fun aC => ∏ i : {x : G.Player // x ∉ S}, σ i.val (aC i),
    by
      refine ⟨fun aC => Finset.prod_nonneg (fun i _ => stdSimplex.zero_le _ _), ?_⟩
      rw [show ∑ aC : G.ComplementAction S,
            ∏ i : {x : G.Player // x ∉ S}, σ i.val (aC i) =
          ∏ i : {x : G.Player // x ∉ S}, ∑ b : G.Action i.val, σ i.val b from ?_]
      · refine Finset.prod_eq_one (fun i _ => stdSimplex.sum_eq_one _)
      · rw [← Fintype.piFinset_univ]
        exact (Finset.prod_univ_sum (fun _ => Finset.univ) _).symm⟩

/-- The coalition marginal evaluates to the product of player marginals over the coalition. -/
@[simp] lemma coalitionMarginal_apply (σ : G.MixedStrategy) (aS : G.CoalitionAction S) :
    G.coalitionMarginal S σ aS = ∏ i : {x : G.Player // x ∈ S}, σ i.val (aS i) := rfl

/-- The complement marginal evaluates to the product of player marginals over the complement. -/
@[simp] lemma complementMarginal_apply (σ : G.MixedStrategy) (aC : G.ComplementAction S) :
    G.complementMarginal S σ aC = ∏ i : {x : G.Player // x ∉ S}, σ i.val (aC i) := rfl

/-! ## Combine equivalence -/

/-- Bijection between coalition × complement profiles and full action profiles. The forward
direction is `combine`; the inverse extracts the restrictions. -/
def combineEquiv :
    G.CoalitionAction S × G.ComplementAction S ≃ G.ActionProfile where
  toFun p := G.combine S p.1 p.2
  invFun s := (fun i => s i.val, fun i => s i.val)
  left_inv := fun ⟨aS, aC⟩ => by
    refine Prod.ext ?_ ?_
    · funext ⟨i, hi⟩
      simp [combine, hi]
    · funext ⟨i, hi⟩
      simp [combine, hi]
  right_inv s := by
    funext i
    by_cases h : i ∈ S <;> simp [combine, h]

/-! ## Payoff at marginals -/

/-- The bilinear coalitional payoff at the product-of-marginals strategy equals the sum of expected
payoffs over the coalition. -/
lemma coalitionExpectedPayoff_at_marginals (σ : G.MixedStrategy) :
    G.coalitionExpectedPayoff S (G.coalitionMarginal S σ) (G.complementMarginal S σ) =
      ∑ i ∈ S, G.expectedPayoff i σ := by
  unfold coalitionExpectedPayoff coalitionTotalPayoff
  simp_rw [coalitionMarginal_apply, complementMarginal_apply, Finset.mul_sum]
  rw [← Finset.sum_product', Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold expectedPayoff
  refine Finset.sum_equiv (G.combineEquiv S) (fun _ => by simp) (fun p _ => ?_)
  obtain ⟨aS, aC⟩ := p
  congr 1
  have hS : ∀ i : {x : G.Player // x ∈ S},
      σ i.val (aS i) = σ i.val ((G.combineEquiv S) (aS, aC) i.val) := by
    intro ⟨i, hi⟩
    change σ i (aS ⟨i, hi⟩) = σ i (G.combine S aS aC i)
    simp [combine, hi]
  have hC : ∀ i : {x : G.Player // x ∉ S},
      σ i.val (aC i) = σ i.val ((G.combineEquiv S) (aS, aC) i.val) := by
    intro ⟨i, hi⟩
    change σ i (aC ⟨i, hi⟩) = σ i (G.combine S aS aC i)
    simp [combine, hi]
  rw [Finset.prod_congr rfl (fun i _ => hS i),
      Finset.prod_congr rfl (fun i _ => hC i)]
  set f : G.Player → ℝ := fun i => σ i ((G.combineEquiv S) (aS, aC) i)
  have hSprod : (∏ i : {x : G.Player // x ∈ S}, f i.val) = ∏ i ∈ S, f i :=
    (Finset.prod_subtype S (fun _ => Iff.rfl) f).symm
  have hCprod : (∏ i : {x : G.Player // x ∉ S}, f i.val) = ∏ i ∈ Sᶜ, f i :=
    (Finset.prod_subtype Sᶜ (fun _ => Finset.mem_compl) f).symm
  rw [hSprod, hCprod]
  exact Finset.prod_mul_prod_compl S f

/-! ## Singleton property of the complement type when `S = univ` -/

instance instSubsingletonComplementActionUniv :
    Subsingleton (G.ComplementAction Finset.univ) :=
  ⟨fun _ _ => funext (fun ⟨_, hx⟩ => (hx (Finset.mem_univ _)).elim)⟩

/-- For `S = Finset.univ`, every distribution on the complement (singleton) type is the same. -/
lemma complement_simplex_univ_subsingleton :
    Subsingleton (stdSimplex ℝ (G.ComplementAction Finset.univ)) := by
  refine ⟨fun σ τ => Subtype.ext (funext (fun aC => ?_))⟩
  have hone : ∀ ρ : stdSimplex ℝ (G.ComplementAction Finset.univ), ρ.val aC = 1 := by
    intro ρ
    have hsum := ρ.2.2
    rw [Finset.sum_eq_single aC
      (fun b _ hne => absurd (Subsingleton.elim b aC) hne)
      (fun h => (h (Finset.mem_univ _)).elim)] at hsum
    exact hsum
  rw [hone σ, hone τ]

/-! ## TU strong equilibrium and α-core membership -/

/-- A *TU strong equilibrium*: No coalition can correlate-deviate to improve its total expected
coalitional payoff against the complement playing its product-of-marginals strategy at `σ`. -/
def IsTUStrongEquilibrium (σ : G.MixedStrategy) : Prop :=
  ∀ S : Finset G.Player, ∀ σ_S' : stdSimplex ℝ (G.CoalitionAction S),
    G.coalitionExpectedPayoff S σ_S' (G.complementMarginal S σ) ≤
      G.coalitionExpectedPayoff S (G.coalitionMarginal S σ) (G.complementMarginal S σ)

/-- The payoff vector at a mixed-strategy profile, viewed as a payoff vector for the α-derived TU
game. -/
noncomputable def payoffAtMixed (σ : G.MixedStrategy) :
    G.toTUGameOn.PayoffVector :=
  fun i => G.expectedPayoff i σ

/-- Helper: From strong equilibrium, every coalition's α-value is bounded by the total expected
payoff over the coalition at `σ`. -/
private lemma alpha_le_sum_expPayoff_of_strong_eq
    {σ : G.MixedStrategy} (hσ : G.IsTUStrongEquilibrium σ) (S : Finset G.Player) :
    G.alphaChar S ≤ ∑ i ∈ S, G.expectedPayoff i σ := by
  unfold alphaChar
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨σ_S', rfl⟩
  calc sInf (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
            G.coalitionExpectedPayoff S σ_S' σ_C))
      ≤ G.coalitionExpectedPayoff S σ_S' (G.complementMarginal S σ) :=
        csInf_le (G.coalitionExpectedPayoff_bddBelow_C S σ_S')
          ⟨G.complementMarginal S σ, rfl⟩
    _ ≤ G.coalitionExpectedPayoff S (G.coalitionMarginal S σ)
            (G.complementMarginal S σ) := hσ S σ_S'
    _ = ∑ i ∈ S, G.expectedPayoff i σ := G.coalitionExpectedPayoff_at_marginals S σ

/-- A TU strong equilibrium has its payoff vector in the α-core of `toTUGameOn`. -/
theorem isTUStrongEquilibrium_implies_isCore
    {σ : G.MixedStrategy} (hσ : G.IsTUStrongEquilibrium σ) :
    G.toTUGameOn.IsCore (G.payoffAtMixed σ) := by
  refine ⟨?_, ?_⟩
  · change ∑ i, G.payoffAtMixed σ i = G.alphaChar Finset.univ
    unfold payoffAtMixed
    refine le_antisymm ?_ ?_
    · calc ∑ i, G.expectedPayoff i σ
          = G.coalitionExpectedPayoff Finset.univ (G.coalitionMarginal Finset.univ σ)
              (G.complementMarginal Finset.univ σ) :=
            (G.coalitionExpectedPayoff_at_marginals Finset.univ σ).symm
        _ ≤ G.alphaChar Finset.univ := by
            unfold alphaChar
            refine le_csSup (G.alphaChar_inner_bddAbove Finset.univ)
              ⟨G.coalitionMarginal Finset.univ σ, ?_⟩
            refine le_antisymm
              (csInf_le (G.coalitionExpectedPayoff_bddBelow_C Finset.univ _)
                ⟨G.complementMarginal Finset.univ σ, rfl⟩) ?_
            refine le_csInf (Set.range_nonempty _) ?_
            rintro _ ⟨σ_C, rfl⟩
            rw [G.complement_simplex_univ_subsingleton.elim σ_C
              (G.complementMarginal Finset.univ σ)]
    · simpa using G.alpha_le_sum_expPayoff_of_strong_eq hσ Finset.univ
  · intro S
    exact G.alpha_le_sum_expPayoff_of_strong_eq hσ S

end FiniteStrategicGame

end Econlib.GameTheory
