/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Mobius

/-!
# Value rules and the Shapley axioms

A *value rule* assigns a payoff vector to every fixed-player TU game. This file gives the abstract
definition together with the four Shapley axioms (efficiency, symmetry, dummy, additivity +
homogeneity = linearity; Shapley 1953), their bundled `SatisfiesShapleyAxioms`, and the
unanimity-game uniqueness lemmas that determine any axiom-satisfying rule on the unanimity basis.
These are the value-rule-level facts used to derive Shapley uniqueness in `Shapley.lean`.

## Main definitions

* `ValueRule`: A rule assigning payoff vectors to all games on a fixed player type.
* `ValueRule.SatisfiesEfficiency`, `ValueRule.SatisfiesSymmetry`, `ValueRule.SatisfiesDummy`, and
  `ValueRule.SatisfiesLinearity`: The Shapley axioms.
* `ValueRule.SatisfiesShapleyAxioms`: The bundled Shapley axiom predicate.

## Main statements

* `ValueRule.unanimity_unique`: Any rule satisfying efficiency, symmetry, and dummy agrees with
  Shapley shares on unanimity games.

## References

* Shapley, Lloyd S. 1953. “A Value for n-Person Games.” In *Contributions to the Theory of Games,
  Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

cooperative game, value rule, shapley axioms
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

/-- A value rule assigns a payoff vector to every game on a fixed player type. -/
abbrev ValueRule (Player : Type*) [Fintype Player] [DecidableEq Player] :=
  (G : TUGameOn Player) → Player → ℝ

namespace ValueRule

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Efficiency axiom for a value rule. -/
def SatisfiesEfficiency (φ : ValueRule Player) : Prop :=
  ∀ G : TUGameOn Player, ∑ i : Player, φ G i = G.value Finset.univ

/-- Symmetry axiom for a value rule. -/
def SatisfiesSymmetry (φ : ValueRule Player) : Prop :=
  ∀ (G : TUGameOn Player) (i j : Player),
    (∀ S, i ∉ S → j ∉ S →
      G.marginalContribution i S = G.marginalContribution j S) →
      φ G i = φ G j

/-- Dummy-player axiom for a value rule. -/
def SatisfiesDummy (φ : ValueRule Player) : Prop :=
  ∀ (G : TUGameOn Player) (i : Player),
    (∀ S, i ∉ S → G.marginalContribution i S = G.value {i}) →
      φ G i = G.value {i}

/-- Additivity axiom for a value rule. -/
def SatisfiesAdditivity (φ : ValueRule Player) : Prop :=
  ∀ (G H : TUGameOn Player) (i : Player),
    φ (G.add H) i = φ G i + φ H i

/-- Homogeneity axiom for a value rule.

This is the scalar part of linearity over real-valued games. -/
def SatisfiesHomogeneity (φ : ValueRule Player) : Prop :=
  ∀ (a : ℝ) (G : TUGameOn Player) (i : Player),
    φ (G.smul a) i = a * φ G i

/-- Linearity of a value rule over fixed-player TU games. -/
structure SatisfiesLinearity (φ : ValueRule Player) : Prop where
  /-- The value rule is additive over games. -/
  additivity : SatisfiesAdditivity φ
  /-- The value rule is homogeneous under scaling. -/
  homogeneity : SatisfiesHomogeneity φ

/-- The standard Shapley axioms for a value rule. -/
structure SatisfiesShapleyAxioms (φ : ValueRule Player) : Prop where
  /-- The value rule is efficient. -/
  efficiency : SatisfiesEfficiency φ
  /-- The value rule is symmetric. -/
  symmetry : SatisfiesSymmetry φ
  /-- The value rule satisfies the dummy-player axiom. -/
  dummy : SatisfiesDummy φ
  /-- The value rule is linear. -/
  linearity : SatisfiesLinearity φ

/-- Apply efficiency: The payoffs sum to the grand-coalition value. -/
theorem SatisfiesEfficiency.apply {φ : ValueRule Player}
    (hφ : SatisfiesEfficiency φ) (G : TUGameOn Player) :
    ∑ i : Player, φ G i = G.value Finset.univ :=
  hφ G

/-- Apply symmetry: Players with equal marginal contributions receive equal payoffs. -/
theorem SatisfiesSymmetry.apply {φ : ValueRule Player}
    (hφ : SatisfiesSymmetry φ) (G : TUGameOn Player) {i j : Player}
    (hij : ∀ S, i ∉ S → j ∉ S →
      G.marginalContribution i S = G.marginalContribution j S) :
    φ G i = φ G j :=
  hφ G i j hij

/-- Apply the dummy axiom: A dummy player receives its standalone value `G.value {i}`. -/
theorem SatisfiesDummy.apply {φ : ValueRule Player}
    (hφ : SatisfiesDummy φ) (G : TUGameOn Player) {i : Player}
    (hi : ∀ S, i ∉ S → G.marginalContribution i S = G.value {i}) :
    φ G i = G.value {i} :=
  hφ G i hi

/-- Apply additivity: The payoff at a sum of games is the sum of payoffs. -/
theorem SatisfiesAdditivity.apply {φ : ValueRule Player}
    (hφ : SatisfiesAdditivity φ) (G H : TUGameOn Player) (i : Player) :
    φ (G.add H) i = φ G i + φ H i :=
  hφ G H i

/-- Apply homogeneity: Scaling the game scales the payoff. -/
theorem SatisfiesHomogeneity.apply {φ : ValueRule Player}
    (hφ : SatisfiesHomogeneity φ) (a : ℝ) (G : TUGameOn Player) (i : Player) :
    φ (G.smul a) i = a * φ G i :=
  hφ a G i

/-- An additive value rule assigns the zero game the zero payoff. -/
theorem SatisfiesAdditivity.zero {φ : ValueRule Player}
    (hφ : SatisfiesAdditivity φ) (i : Player) :
    φ TUGameOn.zero i = 0 := by
  have h := hφ.apply TUGameOn.zero TUGameOn.zero i
  rw [TUGameOn.zero_add_zero] at h
  linarith

/-- Additivity extends to finite sums of games. -/
theorem SatisfiesAdditivity.sum {φ : ValueRule Player}
    (hφ : SatisfiesAdditivity φ) {ι : Type*}
    (I : Finset ι) (F : ι → TUGameOn Player) (i : Player) :
    φ (TUGameOn.sum I F) i = ∑ k ∈ I, φ (F k) i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [hφ.zero i]
  | insert k I hk hI =>
      rw [TUGameOn.sum_insert hk, hφ.apply, hI]
      simp [hk]

/-- A linear value rule applied to a game equals the dividend-weighted sum of its values on the
unanimity games. -/
theorem SatisfiesLinearity.harsanyiExpansion {φ : ValueRule Player}
    (hφ : SatisfiesLinearity φ) (G : TUGameOn Player) (i : Player) :
    φ G.harsanyiExpansion i =
      ∑ T ∈ (Finset.univ : Finset Player).powerset,
        G.harsanyiDividend T * φ (TUGameOn.unanimity T) i := by
  rw [TUGameOn.harsanyiExpansion, hφ.1.sum]
  exact Finset.sum_congr rfl fun T _ =>
    hφ.2.apply (G.harsanyiDividend T) (TUGameOn.unanimity T) i

/-! ## Unanimity-game uniqueness -/

/-- A player outside the carrier `T` is a dummy in the unanimity game, hence receives `0`. -/
theorem unanimity_value_of_not_mem
    {φ : ValueRule Player} (hdummy : SatisfiesDummy φ)
    {T : Finset Player} {i : Player} (hiT : i ∉ T) :
    φ (TUGameOn.unanimity T) i = 0 := by
  rw [hdummy.apply (TUGameOn.unanimity T)
    (fun S hiS => TUGameOn.unanimity_marginal_of_not_mem hiT S hiS)]
  exact TUGameOn.unanimity_singleton_of_not_mem hiT

/-- By symmetry, all carrier players of a unanimity game receive equal payoffs. -/
theorem unanimity_value_eq_of_mem
    {φ : ValueRule Player} (hsym : SatisfiesSymmetry φ)
    {T : Finset Player} {i j : Player} (hiT : i ∈ T) (hjT : j ∈ T) :
    φ (TUGameOn.unanimity T) i = φ (TUGameOn.unanimity T) j :=
  hsym.apply (TUGameOn.unanimity T)
    (TUGameOn.unanimity_marginal_eq_of_mem hiT hjT)

/-- A carrier player of a unanimity game receives the equal share `1 / |T|` under any value rule
satisfying efficiency, symmetry, and the dummy axiom. -/
theorem unanimity_value_of_mem
    {φ : ValueRule Player} (heff : SatisfiesEfficiency φ) (hsym : SatisfiesSymmetry φ)
    (hdummy : SatisfiesDummy φ)
    {T : Finset Player} {i : Player} (hiT : i ∈ T) :
    φ (TUGameOn.unanimity T) i = 1 / (T.card : ℝ) := by
  let U : TUGameOn Player := TUGameOn.unanimity T
  have hTnon : T.Nonempty := ⟨i, hiT⟩
  have hvalue_univ : U.value Finset.univ = 1 := by
    simp [U, TUGameOn.unanimity, hTnon]
  have houtside : ∀ j : Player, j ∉ T → φ U j = 0 :=
    fun j hjT => unanimity_value_of_not_mem hdummy hjT
  have hinside : ∀ j : Player, j ∈ T → φ U j = φ U i :=
    fun j hjT => unanimity_value_eq_of_mem hsym hjT hiT
  have hsum_support :
      Finset.sum T (fun j => φ U j) = ∑ j : Player, φ U j := by
    simpa using
      (Finset.sum_subset (s₁ := T) (s₂ := (Finset.univ : Finset Player))
        (fun _ _ => Finset.mem_univ _)
        (fun j _ hjT => houtside j hjT))
  have hsum_T : Finset.sum T (fun j => φ U j) = (T.card : ℝ) * φ U i := by
    calc
      Finset.sum T (fun j => φ U j)
          = Finset.sum T (fun _j => φ U i) := Finset.sum_congr rfl hinside
      _ = (T.card : ℝ) * φ U i := by rw [Finset.sum_const, nsmul_eq_mul]
  have heffU : ∑ j : Player, φ U j = 1 := by
    simpa [hvalue_univ] using heff.apply U
  have hmul : (T.card : ℝ) * φ U i = 1 := by
    rw [← hsum_T, hsum_support]
    simpa using heffU
  -- card·φUi = 1 directly gives φUi = 1/card, no nonvanishing side condition needed
  exact eq_one_div_of_mul_eq_one_right hmul

/-- Any value rule satisfying efficiency, symmetry, and the dummy axiom is determined on the
unanimity game of `T`: Carrier players split the value equally and outsiders receive `0`. -/
theorem unanimity_unique
    {φ : ValueRule Player} (heff : SatisfiesEfficiency φ) (hsym : SatisfiesSymmetry φ)
    (hdummy : SatisfiesDummy φ) (T : Finset Player) :
    φ (TUGameOn.unanimity T) =
      fun i => if i ∈ T then 1 / (T.card : ℝ) else 0 := by
  funext i
  by_cases hiT : i ∈ T
  · simp [hiT, unanimity_value_of_mem heff hsym hdummy hiT]
  · simp [hiT, unanimity_value_of_not_mem hdummy hiT]

end ValueRule

end Econlib.GameTheory
