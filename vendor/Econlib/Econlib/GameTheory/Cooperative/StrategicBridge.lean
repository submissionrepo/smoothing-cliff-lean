/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Game
public import Econlib.GameTheory.Strategic.Basic

/-!
# Bridge: Cooperative TU games from strategic-form games

Given a `FiniteStrategicGame G`, the **α-characteristic function**
`v_α(S) = sup_{σ_S} inf_{σ_C} ∑_{i ∈ S} expectedPayoff i (σ_S, σ_C)` yields a `TUGameOn G.Player`,
where `σ_S, σ_C` range over correlated mixed strategies on the coalition's joint pure profile space
and the complement's joint profile space (Aumann 1959). Correlated mixing makes the payoff bilinear
in `(σ_S, σ_C)`, so the α- and β-characteristic functions coincide by minimax on the induced
two-player zero-sum game.

## Main definitions

* `FiniteStrategicGame.CoalitionAction` and `FiniteStrategicGame.ComplementAction`: Joint pure
  profile types for a coalition and its complement.
* `FiniteStrategicGame.alphaChar` and `FiniteStrategicGame.betaChar`: Lower and upper coalitional
  characteristic values.
* `FiniteStrategicGame.toTUGameOn`: The α-derived TU game.

## Main statements

* `FiniteStrategicGame.alphaChar_le_betaChar`: The weak minimax inequality.
* `FiniteStrategicGame.alphaChar_eq_betaChar`: Minimax equality via mixed Nash equilibrium in the
  induced zero-sum game.

## Notes

The minimax equality reuses `FiniteStrategicGame.exists_mixedNash`: A Nash equilibrium of the
induced two-player zero-sum game is a saddle point of the bilinear coalitional payoff.

## References

* Aumann, Robert J. 1959. “Acceptable Points in General Cooperative n-Person Games.” In
  *Contributions to the Theory of Games, Volume IV*, edited by A. W. Tucker and R. D. Luce.
  Princeton University Press.

## Tags

cooperative game, strategic game, minimax, characteristic function
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace FiniteStrategicGame

variable (G : FiniteStrategicGame) (S : Finset G.Player)

/-! ## Coalition action types -/

/-- The coalition's joint pure profile type: A function from the subtype of players in `S` to their
action sets. -/
abbrev CoalitionAction : Type _ := (i : {x : G.Player // x ∈ S}) → G.Action i.val

/-- The complement's joint pure profile type. -/
abbrev ComplementAction : Type _ := (i : {x : G.Player // x ∉ S}) → G.Action i.val

/-! ## Combining coalition and complement profiles -/

/-- Glue a coalition profile and a complement profile into a full pure profile. -/
def combine (aS : G.CoalitionAction S) (aC : G.ComplementAction S) : G.ActionProfile :=
  fun i => if h : i ∈ S then aS ⟨i, h⟩ else aC ⟨i, h⟩

/-- Total coalitional pure payoff: Sum of player payoffs over `S` at the combined profile. -/
def coalitionTotalPayoff (aS : G.CoalitionAction S) (aC : G.ComplementAction S) : ℝ :=
  ∑ i ∈ S, G.payoff i (G.combine S aS aC)

/-! ## Induced two-player zero-sum game -/

/-- Action type for the induced 2-player game, dispatched on `Bool`: `false` is the coalition,
`true` is the complement. -/
def inducedAction : Bool → Type _
  | false => G.CoalitionAction S
  | true => G.ComplementAction S

/-- Pure payoff for the induced 2-player zero-sum game. `false` (coalition) maximizes the
coalitional total; `true` (complement) maximizes its negation. -/
def inducedPayoff (b : Bool) (a : (b : Bool) → G.inducedAction S b) : ℝ :=
  let total := G.coalitionTotalPayoff S (a false) (a true)
  match b with
  | false => total
  | true  => -total

instance instInhabitedInducedAction : ∀ b : Bool, Inhabited (G.inducedAction S b)
  | false => ⟨fun _ => default⟩
  | true => ⟨fun _ => default⟩

instance instFintypeInducedAction : ∀ b : Bool, Fintype (G.inducedAction S b)
  | false => (inferInstance : Fintype (G.CoalitionAction S))
  | true => (inferInstance : Fintype (G.ComplementAction S))

instance instDecidableEqInducedAction : ∀ b : Bool, DecidableEq (G.inducedAction S b)
  | false => (inferInstance : DecidableEq (G.CoalitionAction S))
  | true => (inferInstance : DecidableEq (G.ComplementAction S))

/-- The induced 2-player zero-sum strategic game. -/
def inducedZeroSum : FiniteStrategicGame where
  Player := Bool
  Action := G.inducedAction S
  payoff := G.inducedPayoff S
  instInhabitedPlayer := ⟨false⟩
  instDecidableEqPlayer := instDecidableEqBool
  instInhabitedAction := inferInstance
  instFintypePlayer := inferInstance
  instFintypeAction := inferInstance
  instDecidableEqAction := inferInstance

/-! ## Mixed coalitional payoff and α/β characteristic functions -/

/-- Expected coalitional payoff under correlated mixed strategies `σ_S, σ_C`. The double sum ranges
over all pure coalition profiles `aS` and pure complement profiles `aC`, weighted by the product
`σ_S aS * σ_C aC`. -/
noncomputable def coalitionExpectedPayoff
    (σ_S : stdSimplex ℝ (G.CoalitionAction S))
    (σ_C : stdSimplex ℝ (G.ComplementAction S)) : ℝ :=
  ∑ aS : G.CoalitionAction S, ∑ aC : G.ComplementAction S,
    σ_S aS * σ_C aC * G.coalitionTotalPayoff S aS aC

/-- α-characteristic function: The value coalition `S` can guarantee against the worst correlated
complement response. -/
noncomputable def alphaChar : ℝ :=
  sSup (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
    sInf (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C))))

/-- β-characteristic function: The value the complement can hold the coalition to, under
best-response. -/
noncomputable def betaChar : ℝ :=
  sInf (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
    sSup (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C))))

/-! ## Continuity of the coalitional payoff -/

/-- The coalitional expected payoff is jointly continuous in the coalition and complement mixed
strategies. -/
lemma coalitionExpectedPayoff_continuous :
    Continuous (fun p :
        stdSimplex ℝ (G.CoalitionAction S) × stdSimplex ℝ (G.ComplementAction S) =>
      G.coalitionExpectedPayoff S p.1 p.2) := by
  unfold coalitionExpectedPayoff
  refine continuous_finset_sum _ (fun aS _ => ?_)
  refine continuous_finset_sum _ (fun aC _ => ?_)
  refine (Continuous.mul ?_ ?_).mul continuous_const
  · exact (continuous_apply aS).comp (continuous_subtype_val.comp continuous_fst)
  · exact (continuous_apply aC).comp (continuous_subtype_val.comp continuous_snd)

/-! ## Uniform bound on the coalitional payoff -/

/-- A uniform bound on `|coalitionExpectedPayoff|` independent of `σ_S, σ_C`. -/
noncomputable def coalitionPayoffBound : ℝ :=
  ∑ aS : G.CoalitionAction S, ∑ aC : G.ComplementAction S,
    |G.coalitionTotalPayoff S aS aC|

/-- The coalitional expected payoff is bounded in absolute value by `coalitionPayoffBound`,
uniformly in the strategies. -/
lemma abs_coalitionExpectedPayoff_le
    (σ_S : stdSimplex ℝ (G.CoalitionAction S))
    (σ_C : stdSimplex ℝ (G.ComplementAction S)) :
    |G.coalitionExpectedPayoff S σ_S σ_C| ≤ G.coalitionPayoffBound S := by
  unfold coalitionExpectedPayoff coalitionPayoffBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun aS _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum (fun aC _ => ?_)
  rw [abs_mul, abs_mul]
  have hσS : 0 ≤ σ_S aS := stdSimplex.zero_le σ_S aS
  have hσC : 0 ≤ σ_C aC := stdSimplex.zero_le σ_C aC
  have hσS_le : σ_S aS ≤ 1 := stdSimplex.le_one σ_S aS
  have hσC_le : σ_C aC ≤ 1 := stdSimplex.le_one σ_C aC
  rw [abs_of_nonneg hσS, abs_of_nonneg hσC]
  have hprod_le : σ_S aS * σ_C aC ≤ 1 := mul_le_one₀ hσS_le hσC hσC_le
  calc σ_S aS * σ_C aC * |G.coalitionTotalPayoff S aS aC|
      ≤ 1 * |G.coalitionTotalPayoff S aS aC| :=
        mul_le_mul_of_nonneg_right hprod_le (abs_nonneg _)
    _ = |G.coalitionTotalPayoff S aS aC| := one_mul _

/-- For fixed coalition strategy, the payoff is bounded above over complement strategies. -/
lemma coalitionExpectedPayoff_bddAbove_C
    (σ_S : stdSimplex ℝ (G.CoalitionAction S)) :
    BddAbove (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C)) := by
  refine ⟨G.coalitionPayoffBound S, ?_⟩
  rintro _ ⟨σ_C, rfl⟩
  exact (le_abs_self _).trans (G.abs_coalitionExpectedPayoff_le S σ_S σ_C)

/-- For fixed coalition strategy, the payoff is bounded below over complement strategies. -/
lemma coalitionExpectedPayoff_bddBelow_C
    (σ_S : stdSimplex ℝ (G.CoalitionAction S)) :
    BddBelow (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C)) := by
  refine ⟨-(G.coalitionPayoffBound S), ?_⟩
  rintro _ ⟨σ_C, rfl⟩
  linarith [neg_abs_le (G.coalitionExpectedPayoff S σ_S σ_C),
    G.abs_coalitionExpectedPayoff_le S σ_S σ_C]

/-- For fixed complement strategy, the payoff is bounded above over coalition strategies. -/
lemma coalitionExpectedPayoff_bddAbove_S
    (σ_C : stdSimplex ℝ (G.ComplementAction S)) :
    BddAbove (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C)) := by
  refine ⟨G.coalitionPayoffBound S, ?_⟩
  rintro _ ⟨σ_S, rfl⟩
  exact (le_abs_self _).trans (G.abs_coalitionExpectedPayoff_le S σ_S σ_C)

/-- For fixed complement strategy, the payoff is bounded below over coalition strategies. -/
lemma coalitionExpectedPayoff_bddBelow_S
    (σ_C : stdSimplex ℝ (G.ComplementAction S)) :
    BddBelow (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
      G.coalitionExpectedPayoff S σ_S σ_C)) := by
  refine ⟨-(G.coalitionPayoffBound S), ?_⟩
  rintro _ ⟨σ_S, rfl⟩
  linarith [neg_abs_le (G.coalitionExpectedPayoff S σ_S σ_C),
    G.abs_coalitionExpectedPayoff_le S σ_S σ_C]

/-- Bounded-above on the inner-inf set. -/
lemma alphaChar_inner_bddAbove :
    BddAbove (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
      sInf (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
        G.coalitionExpectedPayoff S σ_S σ_C)))) := by
  refine ⟨G.coalitionPayoffBound S, ?_⟩
  rintro _ ⟨σ_S, rfl⟩
  obtain ⟨σ_C₀⟩ : Nonempty (stdSimplex ℝ (G.ComplementAction S)) := inferInstance
  have hle : sInf (Set.range (fun σ_C => G.coalitionExpectedPayoff S σ_S σ_C)) ≤
      G.coalitionExpectedPayoff S σ_S σ_C₀ :=
    csInf_le (G.coalitionExpectedPayoff_bddBelow_C S σ_S) ⟨σ_C₀, rfl⟩
  exact hle.trans ((le_abs_self _).trans (G.abs_coalitionExpectedPayoff_le S σ_S σ_C₀))

/-- Bounded-below on the outer-sup set (used for `betaChar`). -/
lemma betaChar_inner_bddBelow :
    BddBelow (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction S) =>
      sSup (Set.range (fun σ_S : stdSimplex ℝ (G.CoalitionAction S) =>
        G.coalitionExpectedPayoff S σ_S σ_C)))) := by
  refine ⟨-(G.coalitionPayoffBound S), ?_⟩
  rintro _ ⟨σ_C, rfl⟩
  obtain ⟨σ_S₀⟩ : Nonempty (stdSimplex ℝ (G.CoalitionAction S)) := inferInstance
  have hge : G.coalitionExpectedPayoff S σ_S₀ σ_C ≤
      sSup (Set.range (fun σ_S => G.coalitionExpectedPayoff S σ_S σ_C)) :=
    le_csSup (G.coalitionExpectedPayoff_bddAbove_S S σ_C) ⟨σ_S₀, rfl⟩
  have hneg : -G.coalitionPayoffBound S ≤ G.coalitionExpectedPayoff S σ_S₀ σ_C := by
    linarith [neg_abs_le (G.coalitionExpectedPayoff S σ_S₀ σ_C),
      G.abs_coalitionExpectedPayoff_le S σ_S₀ σ_C]
  exact hneg.trans hge

/-! ## Bridging the induced game's `expectedPayoff` -/

/-- Equivalence between the induced game's strategy profile space and the coalition × complement
product. Used to flatten `expectedPayoff` on `inducedZeroSum`. -/
def boolPiEquivCoalitionProd :
    ((b : Bool) → G.inducedAction S b) ≃ G.CoalitionAction S × G.ComplementAction S where
  toFun f := (f false, f true)
  invFun p b := match b with | false => p.1 | true => p.2
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := rfl

/-- General reindexing: Any sum over the induced game's profile space equals the double sum over
coalition × complement. -/
private lemma sum_reindex_inducedProfile {β : Type*} [AddCommMonoid β]
    (F : ((b : Bool) → G.inducedAction S b) → β) :
    ∑ s : ((b : Bool) → G.inducedAction S b), F s =
      ∑ aS : G.CoalitionAction S, ∑ aC : G.ComplementAction S,
        F ((G.boolPiEquivCoalitionProd S).symm (aS, aC)) := by
  rw [← Finset.sum_product']
  refine Finset.sum_equiv (G.boolPiEquivCoalitionProd S)
    (fun s => by simp) (fun s _ => ?_)
  congr 1
  exact ((G.boolPiEquivCoalitionProd S).symm_apply_apply s).symm

/-- Bridge: The induced game's `expectedPayoff` for player `b` factors through the coalitional
expected payoff with the appropriate sign. -/
lemma inducedZeroSum_expectedPayoff_false
    (σ : (G.inducedZeroSum S).MixedStrategy) :
    (G.inducedZeroSum S).expectedPayoff false σ =
      G.coalitionExpectedPayoff S (σ false) (σ true) := by
  change (∑ s : ((b : Bool) → G.inducedAction S b), (∏ j, σ j (s j)) * G.inducedPayoff S false s) =
    G.coalitionExpectedPayoff S (σ false) (σ true)
  rw [G.sum_reindex_inducedProfile S
      (fun s => (∏ j, σ j (s j)) * G.inducedPayoff S false s)]
  unfold coalitionExpectedPayoff
  refine Finset.sum_congr rfl (fun aS _ => Finset.sum_congr rfl (fun aC _ => ?_))
  change (∏ b : Bool, σ b ((G.boolPiEquivCoalitionProd S).symm (aS, aC) b)) *
      G.inducedPayoff S false ((G.boolPiEquivCoalitionProd S).symm (aS, aC))
    = (σ false) aS * (σ true) aC * G.coalitionTotalPayoff S aS aC
  rw [Fintype.prod_bool]
  simp only [boolPiEquivCoalitionProd, Equiv.coe_fn_symm_mk]
  unfold inducedPayoff
  ring

/-- The induced game's `expectedPayoff` for the complement player is the negation of the
coalitional expected payoff. -/
lemma inducedZeroSum_expectedPayoff_true
    (σ : (G.inducedZeroSum S).MixedStrategy) :
    (G.inducedZeroSum S).expectedPayoff true σ =
      -G.coalitionExpectedPayoff S (σ false) (σ true) := by
  -- `inducedPayoff true` is the pointwise negation of `inducedPayoff false`, so the whole
  -- expected payoff negates; reuse the `false` bridge rather than re-running the reindexing.
  rw [← G.inducedZeroSum_expectedPayoff_false S σ]
  change (∑ s : ((b : Bool) → G.inducedAction S b),
      (∏ j, σ j (s j)) * G.inducedPayoff S true s) =
    -∑ s : ((b : Bool) → G.inducedAction S b),
      (∏ j, σ j (s j)) * G.inducedPayoff S false s
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun s _ => by unfold inducedPayoff; ring)

/-! ## Trivial minimax inequality α ≤ β -/

theorem alphaChar_le_betaChar : G.alphaChar S ≤ G.betaChar S := by
  unfold alphaChar betaChar
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨σ_S, rfl⟩
  refine le_csInf (Set.range_nonempty _) ?_
  rintro _ ⟨σ_C, rfl⟩
  calc sInf (Set.range (fun σ_C' : stdSimplex ℝ (G.ComplementAction S) =>
            G.coalitionExpectedPayoff S σ_S σ_C'))
      ≤ G.coalitionExpectedPayoff S σ_S σ_C :=
        csInf_le (G.coalitionExpectedPayoff_bddBelow_C S σ_S) ⟨σ_C, rfl⟩
    _ ≤ sSup (Set.range (fun σ_S' : stdSimplex ℝ (G.CoalitionAction S) =>
            G.coalitionExpectedPayoff S σ_S' σ_C)) :=
        le_csSup (G.coalitionExpectedPayoff_bddAbove_S S σ_C) ⟨σ_S, rfl⟩

/-! ## Minimax theorem α = β via Nash on the induced two-player zero-sum game -/

theorem alphaChar_eq_betaChar : G.alphaChar S = G.betaChar S := by
  refine le_antisymm (G.alphaChar_le_betaChar S) ?_
  obtain ⟨σ, hσ⟩ := (G.inducedZeroSum S).exists_mixedNash
  rw [isMixedNash_iff] at hσ
  have hcoal : ∀ y_S : stdSimplex ℝ (G.CoalitionAction S),
      G.coalitionExpectedPayoff S y_S (σ true) ≤
        G.coalitionExpectedPayoff S (σ false) (σ true) := by
    intro y_S
    have h := hσ false y_S
    rw [G.inducedZeroSum_expectedPayoff_false S σ,
        G.inducedZeroSum_expectedPayoff_false S (Function.update σ false y_S)] at h
    have hf : (Function.update σ false y_S) false = y_S := Function.update_self _ _ _
    have ht : (Function.update σ false y_S) true = σ true :=
      Function.update_of_ne (by simp) _ _
    rwa [hf, ht] at h
  have hcomp : ∀ y_C : stdSimplex ℝ (G.ComplementAction S),
      G.coalitionExpectedPayoff S (σ false) (σ true) ≤
        G.coalitionExpectedPayoff S (σ false) y_C := by
    intro y_C
    have h := hσ true y_C
    rw [G.inducedZeroSum_expectedPayoff_true S σ,
        G.inducedZeroSum_expectedPayoff_true S (Function.update σ true y_C)] at h
    have ht : (Function.update σ true y_C) true = y_C := Function.update_self _ _ _
    have hf : (Function.update σ true y_C) false = σ false :=
      Function.update_of_ne (by simp) _ _
    rw [hf, ht] at h
    linarith
  unfold alphaChar betaChar
  have hβ : sInf (Set.range (fun σ_C' : stdSimplex ℝ (G.ComplementAction S) =>
        sSup (Set.range (fun σ_S' : stdSimplex ℝ (G.CoalitionAction S) =>
          G.coalitionExpectedPayoff S σ_S' σ_C')))) ≤
      sSup (Set.range (fun σ_S' : stdSimplex ℝ (G.CoalitionAction S) =>
        G.coalitionExpectedPayoff S σ_S' (σ true))) :=
    csInf_le (G.betaChar_inner_bddBelow S) ⟨σ true, rfl⟩
  have hsup : sSup (Set.range (fun σ_S' : stdSimplex ℝ (G.CoalitionAction S) =>
        G.coalitionExpectedPayoff S σ_S' (σ true))) ≤
      G.coalitionExpectedPayoff S (σ false) (σ true) := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨σ_S', rfl⟩
    exact hcoal σ_S'
  have hinf : G.coalitionExpectedPayoff S (σ false) (σ true) ≤
      sInf (Set.range (fun σ_C' : stdSimplex ℝ (G.ComplementAction S) =>
        G.coalitionExpectedPayoff S (σ false) σ_C')) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨σ_C', rfl⟩
    exact hcomp σ_C'
  have hα : sInf (Set.range (fun σ_C' : stdSimplex ℝ (G.ComplementAction S) =>
        G.coalitionExpectedPayoff S (σ false) σ_C')) ≤
      sSup (Set.range (fun σ_S' : stdSimplex ℝ (G.CoalitionAction S) =>
        sInf (Set.range (fun σ_C' : stdSimplex ℝ (G.ComplementAction S) =>
          G.coalitionExpectedPayoff S σ_S' σ_C')))) :=
    le_csSup (G.alphaChar_inner_bddAbove S) ⟨σ false, rfl⟩
  linarith

/-! ## The α-derived TU game -/

/-- The α-derived TU game on `G.Player`. Coalition `S` is assigned the value it can guarantee under
correlated mixed coalition strategies, against the worst correlated mixed complement response. -/
noncomputable def toTUGameOn : TUGameOn G.Player where
  value S := G.alphaChar S
  value_empty := by
    change G.alphaChar ∅ = 0
    unfold alphaChar
    -- Over the empty coalition the total payoff sums over `∅`, so every expected payoff is `0`.
    have hzero : ∀ (σ_S : stdSimplex ℝ (G.CoalitionAction ∅))
        (σ_C : stdSimplex ℝ (G.ComplementAction ∅)),
        G.coalitionExpectedPayoff ∅ σ_S σ_C = 0 := by
      intro σ_S σ_C
      unfold coalitionExpectedPayoff coalitionTotalPayoff
      simp [Finset.sum_empty]
    -- Each inner range is the constant `0` map, so its `sInf` is `0`; likewise the outer `sSup`.
    have hinner : ∀ σ_S : stdSimplex ℝ (G.CoalitionAction ∅),
        sInf (Set.range (fun σ_C : stdSimplex ℝ (G.ComplementAction ∅) =>
          G.coalitionExpectedPayoff ∅ σ_S σ_C)) = 0 := by
      intro σ_S
      simp only [hzero σ_S, Set.range_const, csInf_singleton]
    simp only [hinner, Set.range_const, csSup_singleton]

end FiniteStrategicGame

end Econlib.GameTheory
