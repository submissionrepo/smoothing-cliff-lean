/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.Groves.DSIC

/-!
# The Vickrey–Clarke–Groves mechanism

The **VCG mechanism** is the Groves mechanism whose offset is the **Clarke pivot**: The maximum
value the other agents could achieve in agent `i`'s absence. Each agent is charged the externality
its presence imposes on the rest. As a Groves mechanism it is efficient and dominant-strategy
incentive compatible; the pivot term additionally delivers no-deficit unconditionally, and ex-post
individual rationality under a participation condition (nonnegative valuations) — both proved in
`Groves.VCGProperties`.

## Main definitions

* `QuasilinearEnvironment.clarkePivot`: The maximal others-value `max_o welfareExcl i o report`.
* `vcgMechanism`: The Groves mechanism with the Clarke pivot offset.

## Main statements

* `welfareExcl_le_clarkePivot`: The pivot dominates the others-value at every outcome.
* `vcgMechanism_isEfficient`, `vcgMechanism_isDSIC`: Inherited from the Groves results.

## References

* Vickrey, William. 1961. “COUNTERSPECULATION, AUCTIONS, AND COMPETITIVE SEALED Tenders.” *The
  Journal of Finance* 16 (1): 8–37. [https://doi.org/10.1111/j.1540-6261.1961.tb02789.x](https://doi.org/10.1111/j.1540-6261.1961.tb02789.x).
* Clarke, Edward H. 1971. “Multipart Pricing of Public Goods.” *Public Choice* 11 (1): 17–33.
  [https://doi.org/10.1007/bf01726210](https://doi.org/10.1007/bf01726210).
* Groves, Theodore. 1973. “Incentives in Teams.” *Econometrica* 41 (4): 617.
  [https://doi.org/10.2307/1914085](https://doi.org/10.2307/1914085).

## Tags

vcg, vickrey, clarke pivot, dominant strategy
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

namespace QuasilinearEnvironment

variable (E : QuasilinearEnvironment)

/-- The **Clarke pivot** for agent `i` (Clarke 1971): The maximum value the other agents could
achieve at the reported profile, over all outcomes. Depends on the report only through the others'
coordinates. -/
def clarkePivot (i : E.Agent) (report : E.TypeProfile) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o => E.welfareExcl i o report)

/-- The Clarke pivot dominates the others-value at every outcome. -/
lemma welfareExcl_le_clarkePivot (i : E.Agent) (o : E.Outcome) (report : E.TypeProfile) :
    E.welfareExcl i o report ≤ E.clarkePivot i report :=
  Finset.le_sup' (fun o => E.welfareExcl i o report) (Finset.mem_univ o)

/-- The Clarke pivot is attained at some outcome. -/
lemma exists_clarkePivot_eq (i : E.Agent) (report : E.TypeProfile) :
    ∃ o, E.clarkePivot i report = E.welfareExcl i o report :=
  let ⟨o, _, ho⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun o => E.welfareExcl i o report)
  ⟨o, ho⟩

/-- The Clarke pivot ignores agent `i`'s own reported coordinate. -/
lemma clarkePivot_update (i : E.Agent) (r : E.TypeProfile) (x : E.Theta i) :
    E.clarkePivot i (update r i x) = E.clarkePivot i r := by
  simp only [clarkePivot, E.welfareExcl_update]

end QuasilinearEnvironment

variable {E : QuasilinearEnvironment}

/-- The Clarke pivot packaged as Groves offset data. -/
def vcgGrovesData (E : QuasilinearEnvironment) : GrovesData E where
  h := E.clarkePivot
  h_indep i r θ_i θ_i' := by rw [E.clarkePivot_update, E.clarkePivot_update]

/-- The **Vickrey–Clarke–Groves mechanism** (Vickrey 1961; Clarke 1971; Groves 1973): Efficient
allocation, Clarke-pivot transfers. -/
def vcgMechanism (E : QuasilinearEnvironment) : DirectMechanism E :=
  grovesMechanism (vcgGrovesData E)

/-- VCG allocates efficiently. -/
theorem vcgMechanism_isEfficient : (vcgMechanism E).IsEfficient :=
  grovesMechanism_isEfficient _

/-- VCG is dominant-strategy incentive compatible. -/
theorem vcgMechanism_isDSIC : (vcgMechanism E).IsDSIC :=
  grovesMechanism_isDSIC _

end Econlib.MechanismDesign.Transfers.General
end
