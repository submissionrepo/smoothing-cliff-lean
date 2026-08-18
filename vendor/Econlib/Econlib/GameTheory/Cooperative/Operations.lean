/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Game
public import Econlib.Math.Combinatorics.BooleanMobius

/-!
# Operations on TU games

This file defines pointwise vector-space operations (`zero`, `add`, `smul`, `sum`), the
unanimity-game basis (`unanimity`), and per-coalition data attached to a game
(`marginalContribution`, `harsanyiDividend`). The simp lemmas unfold these definitions to their
concrete characteristic-function forms.

## Main definitions

* `TUGameOn.marginalContribution`: The incremental value of adding a player to a coalition.
* `TUGameOn.zero`, `TUGameOn.add`, `TUGameOn.smul`, `TUGameOn.sum`: Pointwise operations on TU
  games.
* `TUGameOn.unanimity`: The unanimity game for a coalition.
* `TUGameOn.harsanyiDividend`: The Boolean Möbius coefficient of a game.

## Main statements

* Simp lemmas for the values of the pointwise operations and unanimity games.

## References

* Harsanyi, John C. 1963. “A Simplified Bargaining Model for the n-Person Cooperative Game.”
  *International Economic Review* 4 (2): 194. [https://doi.org/10.2307/2525487](https://doi.org/10.2307/2525487).

## Tags

cooperative game, unanimity game, Harsanyi dividend
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- Marginal contribution of player `i` to coalition `S`. -/
def marginalContribution (G : TUGameOn Player) (i : Player) (S : Finset Player) : ℝ :=
  G.value (insert i S) - G.value S

/-- The zero fixed-player TU game. -/
def zero : TUGameOn Player where
  value _ := 0
  value_empty := rfl

/-- Pointwise sum of two fixed-player TU games. -/
def add (G H : TUGameOn Player) : TUGameOn Player where
  value S := G.value S + H.value S
  value_empty := by simp [G.value_empty, H.value_empty]

/-- Scalar multiple of a fixed-player TU game. -/
def smul (a : ℝ) (G : TUGameOn Player) : TUGameOn Player where
  value S := a * G.value S
  value_empty := by simp [G.value_empty]

/-- Finite pointwise sum of fixed-player TU games. -/
def sum {ι : Type*} (I : Finset ι) (F : ι → TUGameOn Player) : TUGameOn Player where
  value S := ∑ k ∈ I, (F k).value S
  value_empty := by simp [TUGameOn.value_empty]

/-- The unanimity game for coalition `T`.

It pays one exactly to coalitions containing `T`. The empty unanimity game is represented as the
zero game so that `value ∅ = 0` remains part of the structure. -/
def unanimity (T : Finset Player) : TUGameOn Player where
  value S := if T.Nonempty ∧ T ⊆ S then 1 else 0
  value_empty := by
    by_cases hT : T.Nonempty <;> simp [hT]; simp [Finset.nonempty_iff_ne_empty.mp hT]


/-- The Harsanyi dividend of coalition `T` (Harsanyi 1963): The Boolean Möbius coefficient of `G`
in the unanimity-game basis. -/
def harsanyiDividend (G : TUGameOn Player) (T : Finset Player) : ℝ :=
  Finset.booleanMobiusCoeff G.value T

@[simp] theorem zero_value (S : Finset Player) : (zero : TUGameOn Player).value S = 0 := rfl

@[simp] theorem add_value (G H : TUGameOn Player) (S : Finset Player) :
    (G.add H).value S = G.value S + H.value S := rfl

@[simp] theorem smul_value (a : ℝ) (G : TUGameOn Player) (S : Finset Player) :
    (smul a G).value S = a * G.value S := rfl

@[simp] theorem sum_value {ι : Type*} (I : Finset ι) (F : ι → TUGameOn Player) (S : Finset Player) :
  (sum I F).value S = ∑ k ∈ I, (F k).value S := rfl

@[simp] theorem unanimity_value_of_nonempty_subset {T S : Finset Player}
    (hT : T.Nonempty) (hTS : T ⊆ S) : (unanimity T).value S = 1 := by
  simp [unanimity, hT, hTS]

@[simp] theorem unanimity_value_of_not_nonempty {T S : Finset Player}
    (hT : ¬ T.Nonempty) : (unanimity T).value S = 0 := by
  simp [unanimity, hT]

@[simp] theorem unanimity_value_of_not_subset {T S : Finset Player}
    (hTS : ¬ T ⊆ S) : (unanimity T).value S = 0 := by
  simp [unanimity, hTS]

@[simp] theorem unanimity_value_def (T S : Finset Player) :
    (unanimity T).value S = if T.Nonempty ∧ T ⊆ S then 1 else 0 := rfl

theorem smul_unanimity_value_of_subset {T S : Finset Player} (a : ℝ)
    (hT : T.Nonempty) (hTS : T ⊆ S) : (smul a (unanimity T)).value S = a := by simp [hT, hTS]

theorem smul_unanimity_value_of_not_subset {T S : Finset Player} (a : ℝ)
    (hTS : ¬ T ⊆ S) : (smul a (unanimity T)).value S = 0 := by simp [hTS]

@[simp] theorem harsanyiDividend_empty (G : TUGameOn Player) : G.harsanyiDividend ∅ = 0 := by
  simp [harsanyiDividend, G.value_empty]

@[simp] theorem add_zero (G : TUGameOn Player) : G.add zero = G := by ext S; simp

@[simp] theorem zero_add (G : TUGameOn Player) : zero.add G = G := by ext S; simp

@[simp] theorem zero_add_zero : (zero : TUGameOn Player).add zero = zero := by ext S; simp

@[simp] theorem sum_empty {ι : Type*} (F : ι → TUGameOn Player) : sum ∅ F = zero := by
  ext S; simp [sum, zero]

theorem sum_insert {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {k : ι} (hk : k ∉ I) (F : ι → TUGameOn Player) : sum (insert k I) F = (F k).add (sum I F) := by
  ext S; simp [sum, hk]

/-! ## Unanimity-game marginal-contribution lemmas -/

theorem unanimity_singleton_of_not_mem {T : Finset Player} {i : Player} (hiT : i ∉ T) :
    (unanimity T).value {i} = 0 := by by_cases hT : T.Nonempty <;> aesop

theorem unanimity_marginal_of_not_mem {T : Finset Player} {i : Player}
    (hiT : i ∉ T) (S : Finset Player) (_hiS : i ∉ S) :
    (unanimity T).marginalContribution i S = (unanimity T).value {i} := by
  have hsingle : (unanimity T).value {i} = 0 :=
    unanimity_singleton_of_not_mem hiT
  -- `T ⊆ insert i S ↔ T ⊆ S` since `i ∉ T`, so the two coalition values agree and cancel.
  have hiff : T ⊆ insert i S ↔ T ⊆ S := by
    refine ⟨fun hsub x hxT => ?_, fun hsub x hxT => Finset.mem_insert_of_mem (hsub hxT)⟩
    rcases Finset.mem_insert.mp (hsub hxT) with rfl | hxS
    · exact False.elim (hiT hxT)
    · exact hxS
  simp only [marginalContribution, hsingle, unanimity_value_def, hiff, sub_self]

theorem unanimity_marginal_eq_of_mem {T : Finset Player} {i j : Player}
    (hiT : i ∈ T) (hjT : j ∈ T) :
    ∀ S, i ∉ S → j ∉ S →
      (unanimity T).marginalContribution i S =
        (unanimity T).marginalContribution j S := by
  intro S hiS hjS
  by_cases hij : i = j
  · subst hij; rfl
  · have hT : T.Nonempty := ⟨i, hiT⟩
    have hnotS : ¬ T ⊆ S := fun hsub => hiS (hsub hiT)
    have hnotInsertI : ¬ T ⊆ insert i S := by
      intro hsub
      have hjins : j ∈ insert i S := hsub hjT
      have hji : j ≠ i := fun hji => hij hji.symm
      simp [Finset.mem_insert, hji, hjS] at hjins
    have hnotInsertJ : ¬ T ⊆ insert j S := by
      intro hsub
      have hiins : i ∈ insert j S := hsub hiT
      simp [Finset.mem_insert, hij, hiS] at hiins
    unfold marginalContribution
    simp [unanimity, hT, hnotS, hnotInsertI, hnotInsertJ]

end TUGameOn

end Econlib.GameTheory
