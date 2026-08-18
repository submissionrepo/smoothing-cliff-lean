/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Maps of countable distributions

This file defines pushforwards of countable probability distributions along encodable maps and
records the basic identity and composition laws.

## Main definitions

* `CountDist.map`: Pushforward of a countable distribution.

## Main statements

* `CountDist.map_id`: Mapping by the identity leaves a distribution unchanged.
* `CountDist.map_comp`: Mapping respects function composition.

## Tags

probability, countable distributions, map
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace CountDist

/-- Pushforward of a countable distribution along a function, defined via Mathlib's `PMF.map`
across the `toPMF`/`ofPMF` bridge. -/
noncomputable def map {α β : Type*} [Encodable α] [Encodable β]
    (d : CountDist α) (f : α → β) : CountDist β :=
  ofPMF (d.toPMF.map f)

open Classical in
/-- The pushforward mass at `b` is the total prior mass on the fiber `f ⁻¹' {b}`. -/
@[simp] lemma map_apply {α β : Type*} [Encodable α] [Encodable β]
    (d : CountDist α) (f : α → β) (b : β) :
    (d.map f).pmf b = ∑' a, if b = f a then d.pmf a else 0 := by
  -- `(d.toPMF a).toReal` is definitionally `(ENNReal.ofReal (d.pmf a)).toReal`, i.e. `d.pmf a`
  have hreal : ∀ a : α, (d.toPMF a).toReal = d.pmf a := fun a =>
    ENNReal.toReal_ofReal (d.nonneg a)
  have htop : ∀ a : α, (if b = f a then d.toPMF a else 0) ≠ ⊤ := by
    intro a
    split_ifs with h
    · change ¬ENNReal.ofReal (d.pmf a) = ⊤
      simp
    · simp
  rw [map, ofPMF]
  change ((PMF.map f d.toPMF) b).toReal = ∑' a, if b = f a then d.pmf a else 0
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq htop]
  refine tsum_congr fun a => ?_
  split_ifs <;> simp [hreal]

/-- Pushing forward along the identity leaves the distribution unchanged. -/
@[simp] lemma map_id {α : Type*} [Encodable α] (d : CountDist α) :
    d.map id = d := by
  ext a
  rw [map_apply, tsum_eq_single a]
  · simp
  · intro a' ha'
    split_ifs with h
    · exact (ha' h.symm).elim
    · rfl

/-- Pushing forward along `f` then `g` equals pushing forward along `g ∘ f`. -/
lemma map_comp {α β γ : Type*} [Encodable α] [Encodable β] [Encodable γ]
    (d : CountDist α) (f : α → β) (g : β → γ) :
    (d.map f).map g = d.map (g ∘ f) := by
  have hpmf : ((d.map f).map g).toPMF = (d.map (g ∘ f)).toPMF := by
    simp [map, PMF.map_comp, toPMF_ofPMF]
  ext c
  -- both sides are `(toPMF · c).toReal`, a definitional `ofReal`/`toReal` round-trip back to `pmf`
  have hleft : (((d.map f).map g).toPMF c).toReal = ((d.map f).map g).pmf c :=
    ENNReal.toReal_ofReal (((d.map f).map g).nonneg c)
  have hright : ((d.map (g ∘ f)).toPMF c).toReal = (d.map (g ∘ f)).pmf c :=
    ENNReal.toReal_ofReal ((d.map (g ∘ f)).nonneg c)
  have hreal := congrArg (fun q : PMF γ => (q c).toReal) hpmf
  exact hleft.symm.trans (hreal.trans hright)

end CountDist
end Econlib.Probability
