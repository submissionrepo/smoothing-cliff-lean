/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Filter Topology PolishSpace

/-!
# Polish topology refinement for measurable functions

Given a Polish space `(Y, t)` with `BorelSpace Y` and a countable family of measurable functions
`f_i : Y → X_i` into second-countable opens-measurable spaces, this file produces a finer Polish
topology `t' ≤ t` on `Y` under which each `f_i` is continuous and the Borel σ-algebra is preserved
(`@borel _ t = @borel _ t'`).

The refinement preserves the measurable structure while making the chosen measurable observables
continuous, so closed-graph and compactness arguments can be carried out in the finer topology and
then transferred back through the shared Borel σ-algebra.

## Main statements

* `exists_finer_polish_continuous_countable` — a countable family of measurable functions becomes
  simultaneously continuous in a finer Polish topology preserving the Borel σ-algebra.
* `isClosed_prod_of_le_left` — lift a closed-graph statement on `α × β` from a coarser to a finer
  topology on the first factor.
* `borelSpace_of_borel_eq` — build `BorelSpace` for a refined topology with the same Borel
  σ-algebra as the section's original topology.

## Notes

Mathlib's order on `TopologicalSpace α` is "smaller = finer": `t' ≤ t` means `t'` has at least the
open sets of `t`. In the refinement use here, `t` is the original Polish topology and `t'` is the
refined (finer) Polish topology with `t' ≤ t`.

## Tags

polish space, borel sigma-algebra, refinement, measurable function, continuous
-/

@[expose] public section

namespace MeasureTheory

/-- A countable family of measurable functions from a Polish space into second-countable
opens-measurable codomains becomes simultaneously continuous after refining the source's topology
to a single finer Polish topology, with the Borel σ-algebra preserved. -/
theorem exists_finer_polish_continuous_countable
    {Y : Type*} [t : TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {ι : Type*} [Countable ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)] [∀ i, SecondCountableTopology (X i)]
    (f : ∀ i, Y → X i)
    (hf : ∀ i, Measurable (f i)) :
    ∃ t' : TopologicalSpace Y, t' ≤ t ∧ @PolishSpace Y t' ∧
      (∀ i, @Continuous Y (X i) t' _ (f i)) ∧
      @borel Y t' = @borel Y t := by
  -- For each `i`, a finer Polish topology making `f i` continuous.
  choose T hT_le hT_cont hT_polish using
    (fun i : ι => (hf i).exists_continuous)
  -- A single Polish topology finer than all the `T i`.
  obtain ⟨t', ht'_le_T, ht'_le_t, ht'_polish⟩ :
      ∃ t' : TopologicalSpace Y, (∀ i, t' ≤ T i) ∧ t' ≤ t ∧ @PolishSpace Y t' :=
    exists_polishSpace_forall_le (t := t) T hT_le hT_polish
  have hf_cont : ∀ i, @Continuous Y (X i) t' _ (f i) := by
    intro i
    exact @Continuous.comp Y Y (X i) t' (T i) _ id (f i)
      (hT_cont i) (continuous_id_of_le (ht'_le_T i))
  exact ⟨t', ht'_le_t, ht'_polish, hf_cont,
    MeasureTheory.borel_eq_borel_of_le ht'_polish inferInstance ht'_le_t⟩

/-- Lift a closed-graph statement on `α × β` from a coarser topology `t` on `α` to a finer topology
`t' ≤ t`. The second factor's topology is left to typeclass inference. -/
theorem isClosed_prod_of_le_left {α β : Type*} [TopologicalSpace β]
    {t t' : TopologicalSpace α} (h : t' ≤ t) {s : Set (α × β)}
    (hs : @IsClosed (α × β) (@instTopologicalSpaceProd α β t inferInstance) s) :
    @IsClosed (α × β) (@instTopologicalSpaceProd α β t' inferInstance) s :=
  hs.mono (TopologicalSpace.prod_mono h le_rfl)

/-- Construct a `BorelSpace` instance for a topology `t'` on `Y` whose Borel σ-algebra coincides
with that of the section's existing topology.  The proof combines the section's `[BorelSpace Y]`
(giving `‹MeasurableSpace Y› = borel` under the section topology) with the supplied `hborel`. -/
theorem borelSpace_of_borel_eq {Y : Type*}
    [m : MeasurableSpace Y] [t : TopologicalSpace Y] [BorelSpace Y]
    (t' : TopologicalSpace Y) (hborel : @borel Y t' = @borel Y t) :
    @BorelSpace Y t' m :=
  ⟨BorelSpace.measurable_eq.trans hborel.symm⟩

end MeasureTheory
