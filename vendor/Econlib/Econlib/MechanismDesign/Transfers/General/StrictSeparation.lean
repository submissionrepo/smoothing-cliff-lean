/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Allocation
public import Econlib.MechanismDesign.Transfers.General.TaxationPrinciple

/-!
# When a Groves mechanism strictly separates the allocation

The taxation-principle file defines `StrictlySeparatesAlloc`, the strict-incentive condition that
upgrades "the truthful menu entry is an optimal entry" to "it is the unique one"
(`menu_maximizer_unique`). That predicate is stated for an arbitrary `DirectMechanism`, so on its
own it gives no handle on which environments satisfy it. This file supplies a sufficient condition
for **Groves / VCG** mechanisms: Because a Groves agent's ex-post utility is
`totalValue
(efficientAlloc report) (own true type spliced in)` minus an own-report-independent
offset (`grovesMechanism_exPostUtility`), the offset cancels across any two own-reports and strict
separation reduces to a uniqueness statement about the true profile alone — a unique
total-value-maximizing outcome at `update r i θ_i` makes the mechanism strictly separate there.

## Main statements

* `efficientAlloc_eq_of_forall_lt`: A strict-unique total-value maximizer is the efficient
  allocation. (`efficientAlloc` is an opaque `Finite.exists_max.choose`; this lemma identifies the
  concrete winner.)
* `strictlySeparatesAlloc_of_unique_efficient`: A unique total-value maximizer at the true profile
  makes the Groves mechanism strictly separate there — the sufficient condition that discharges
  `menu_maximizer_unique` on concrete data.

## Notes

A public-good provision mechanism can fail strict separation: At the provision threshold the
"provide" and "don't provide" outcomes tie in total welfare, so the maximizer is not unique. A
single-item auction with a unique highest bidder, by contrast, separates (see the second-price
witness in `EconlibTest`).

## Tags

mechanism design, taxation principle, vcg, groves, strict incentive, unique implementation
-/

@[expose] public section

open Function

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment}

/-- A **strict-unique total-value maximizer is the efficient allocation.** `efficientAlloc` is
defined as an arbitrary maximizer (`Finite.exists_max.choose`), so it is opaque; this lemma
identifies the concrete winner: If outcome `o` strictly beats every other outcome at profile `θ`,
the efficient allocation must be `o`. -/
lemma efficientAlloc_eq_of_forall_lt (θ : E.TypeProfile) (o : E.Outcome)
    (h : ∀ o', o' ≠ o → E.totalValue o' θ < E.totalValue o θ) :
    E.efficientAlloc θ = o := by
  by_contra hne
  exact absurd (E.efficientAlloc_isMaxOn θ o) (not_le.mpr (h _ hne))

/-- **A Groves mechanism strictly separates at a profile with a unique efficient outcome.** If the
true profile `update r i θ_i` has a unique total-value-maximizing outcome (every other outcome is
strictly worse), then the Groves mechanism strictly separates the allocation at `(i, r, θ_i)`:
Every own-report inducing a different outcome yields strictly lower ex-post utility. This is the
sufficient condition that discharges `menu_maximizer_unique` on concrete data. -/
theorem strictlySeparatesAlloc_of_unique_efficient (g : GrovesData E)
    (i : E.Agent) (r : E.TypeProfile) (θ_i : E.Theta i)
    (huniq : ∀ o, o ≠ E.efficientAlloc (update r i θ_i) →
      E.totalValue o (update r i θ_i)
        < E.totalValue (E.efficientAlloc (update r i θ_i)) (update r i θ_i)) :
    StrictlySeparatesAlloc (grovesMechanism g) i r θ_i := by
  intro s hne
  -- Unfold both ex-post utilities; splicing the true type back in collapses the doubled `update`,
  -- and the own-report-independent offset is equal on the two reports, so it cancels.
  rw [grovesMechanism_exPostUtility, grovesMechanism_exPostUtility, update_idem, update_idem,
    g.h_indep i r s θ_i]
  -- What remains is strict dominance of the truthful winner over the misreport's winner.
  have hlt := huniq (E.efficientAlloc (update r i s)) hne
  linarith

end Econlib.MechanismDesign.Transfers.General
end
