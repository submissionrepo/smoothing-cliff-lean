/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Basic
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Disintegration of `ProbDist` joint laws

This file adapts the Mathlib **disintegration** and Giry-monad API so that results are packaged as
`ProbDist` rather than `Measure` or `Kernel` values. The Giry-monad bind `ProbDist.bind` gives the
marginal law of a mixture, and `ProbDist.condFst` / `ProbDist.condSnd` are the regular conditional
kernels obtained by disintegrating a joint law along its first or second marginal, which requires a
standard Borel hypothesis on the conditioned coordinate.

## Main definitions

* `ProbDist.bind d k hk` — the marginal law of `b` when `a ~ d` and `b ~ k a`.
* `ProbDist.condFst π a` — disintegration of `π : ProbDist (α × β)` along the first marginal,
  returning a `ProbDist β` for each `a : α`.  Requires `[StandardBorelSpace β]` and `[Nonempty β]`.
* `ProbDist.condSnd π b` — symmetric disintegration along the second marginal, returning a
  `ProbDist α` for each `b : β`.  Requires `[StandardBorelSpace α]` and `[Nonempty α]`.

## Main statements

* `ProbDist.condFst_compProd` — disintegration identity: `fst(π) ⊗ condFst π = π`.
* `ProbDist.condSnd_compProd` — symmetric disintegration identity.
* `ProbDist.condFst_apply_of_ne_zero` — pointwise value of `condFst` at an atom of the first
  marginal.
* `ProbDist.condSnd_apply_of_ne_zero` — pointwise value of `condSnd` at an atom of the second
  marginal.

## Notes

`condFst` and `condSnd` are **regular conditional probability kernels**, not pointwise conditional
laws. Each kernel is canonical only up to the marginal: It is determined almost everywhere by the
disintegration identity, and at an individual point its value equals the elementary conditional law
only when that point is an atom of the marginal (`condFst_apply_of_ne_zero`,
`condSnd_apply_of_ne_zero`). When the marginal is atomless, the value at any fixed point is an
arbitrary off-support representative. Consumers should reason through the disintegration identities
and the atom formula, never about values at arbitrary off-support points.

## Tags

probability, disintegration, conditional kernel, markov kernel
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.Probability

namespace ProbDist

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ### `bind` -/

/-- `bind d k hk` is the marginal law of `b` when `a ~ d` and `b ~ k a`. -/
noncomputable def bind (d : ProbDist α) (k : α → ProbDist β)
    (hk : Measurable (fun a => (k a).toMeasure)) : ProbDist β :=
  ⟨d.toMeasure.bind (fun a => (k a).toMeasure),
   isProbabilityMeasure_bind hk.aemeasurable
     (Filter.Eventually.of_forall fun a => (k a).prop)⟩

/-- `toMeasure` of `bind d k hk` reduces to `Measure.bind`. -/
@[simp] lemma bind_toMeasure (d : ProbDist α) (k : α → ProbDist β)
    (hk : Measurable (fun a => (k a).toMeasure)) :
    (bind d k hk).toMeasure = d.toMeasure.bind (fun a => (k a).toMeasure) := rfl

/-! ### `condFst` -/

/-- `condFst π` is a **regular conditional kernel** for the second coordinate of `π` given the
first. Requires `[StandardBorelSpace β]` so that the kernel value is a probability measure.

The kernel is canonical only `fst`-a.e.: `condFst π a` equals the elementary conditional law
"second coordinate given first `= a`" only when `{a}` is an atom of the first marginal — see
`condFst_apply_of_ne_zero`. Do not reason about values at off-support points. -/
noncomputable def condFst [StandardBorelSpace β] [Nonempty β]
    (π : ProbDist (α × β)) (a : α) : ProbDist β :=
  ⟨π.toMeasure.condKernel a, IsMarkovKernel.isProbabilityMeasure a⟩

/-- `toMeasure` of `condFst π a` reduces to `Measure.condKernel`. -/
@[simp] lemma condFst_toMeasure [StandardBorelSpace β] [Nonempty β]
    (π : ProbDist (α × β)) (a : α) :
    (condFst π a).toMeasure = π.toMeasure.condKernel a := rfl

/-- The function `a ↦ (condFst π a).toMeasure` is measurable. -/
lemma condFst_measurable [StandardBorelSpace β] [Nonempty β]
    (π : ProbDist (α × β)) :
    Measurable (fun a => (condFst π a).toMeasure) :=
  π.toMeasure.condKernel.measurable

/-- Disintegration identity in `compProd` form: The joint law equals the composition of the first
marginal with the conditional kernel. -/
lemma condFst_compProd [StandardBorelSpace β] [Nonempty β]
    (π : ProbDist (α × β)) :
    π.toMeasure.fst.compProd π.toMeasure.condKernel = π.toMeasure :=
  π.toMeasure.disintegrate _

/-- Pointwise value on atoms of the first marginal: If `{a}` carries positive mass under the first
marginal, then `condFst π a` is the elementary conditional law of the second coordinate given the
first equals `a`, namely `(π.fst {a})⁻¹ • π ({a} ×ˢ ·)`. This is the only setting in which the
pointwise reading is justified. -/
lemma condFst_apply_of_ne_zero [StandardBorelSpace β] [Nonempty β] [MeasurableSingletonClass α]
    (π : ProbDist (α × β)) {a : α} (ha : π.toMeasure.fst {a} ≠ 0) (s : Set β) :
    (condFst π a).toMeasure s = (π.toMeasure.fst {a})⁻¹ * π.toMeasure ({a} ×ˢ s) := by
  rw [condFst_toMeasure]
  exact π.toMeasure.condKernel_apply_of_ne_zero ha s

/-! ### `condSnd` -/

/-- `condSnd π` is the symmetric **regular conditional kernel** for the first coordinate of `π`
given the second.

The kernel is canonical only `snd`-a.e.: `condSnd π b` equals the elementary conditional law of the
first coordinate given the second equals `b` only when `{b}` is an atom of the second marginal —
see `condSnd_apply_of_ne_zero`. -/
noncomputable def condSnd [StandardBorelSpace α] [Nonempty α]
    (π : ProbDist (α × β)) (b : β) : ProbDist α :=
  condFst (ProbDist.map π Prod.swap measurable_swap) b

/-- `toMeasure` of `condSnd π b` reduces to `Measure.condKernel` of the swapped measure. -/
@[simp] lemma condSnd_toMeasure [StandardBorelSpace α] [Nonempty α]
    (π : ProbDist (α × β)) (b : β) :
    (condSnd π b).toMeasure
      = (Measure.map Prod.swap π.toMeasure).condKernel b := by
  simp [condSnd, ProbDist.map_toMeasure]

/-- The function `b ↦ (condSnd π b).toMeasure` is measurable. -/
lemma condSnd_measurable [StandardBorelSpace α] [Nonempty α]
    (π : ProbDist (α × β)) :
    Measurable (fun b => (condSnd π b).toMeasure) :=
  condFst_measurable _

/-- Symmetric disintegration identity: The swapped joint law equals the composition of the second
marginal with the conditional kernel `condSnd`.  This is the `condSnd` analog of
`condFst_compProd`. -/
lemma condSnd_compProd [StandardBorelSpace α] [Nonempty α]
    (π : ProbDist (α × β)) :
    π.toMeasure.snd.compProd (Measure.map Prod.swap π.toMeasure).condKernel
      = Measure.map Prod.swap π.toMeasure := by
  have h := condFst_compProd (ProbDist.map π Prod.swap measurable_swap)
  simp only [ProbDist.map_toMeasure, Measure.fst_map_swap] at h
  exact h

/-- Pointwise value on atoms of the second marginal: If `{b}` carries positive mass under the
second marginal, then `condSnd π b` is the elementary conditional law of the first coordinate given
the second equals `b`. This is the only setting in which the pointwise reading is justified. -/
lemma condSnd_apply_of_ne_zero [StandardBorelSpace α] [Nonempty α] [MeasurableSingletonClass β]
    (π : ProbDist (α × β)) {b : β} (hb : π.toMeasure.snd {b} ≠ 0) (s : Set α) :
    (condSnd π b).toMeasure s
      = (π.toMeasure.snd {b})⁻¹ * (Measure.map Prod.swap π.toMeasure) ({b} ×ˢ s) := by
  have hb' : (Measure.map Prod.swap π.toMeasure).fst {b} ≠ 0 := by
    rwa [Measure.fst_map_swap]
  have h := condFst_apply_of_ne_zero (ProbDist.map π Prod.swap measurable_swap) hb' s
  rw [ProbDist.map_toMeasure, Measure.fst_map_swap] at h
  exact h

end ProbDist

end Econlib.Probability
