/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.CDF
public import Econlib.Probability.Distributions.Uniform

/-!
# Single-parameter screening: Environment and direct mechanisms

The single-agent screening model underlying Myerson's analysis. An agent has a one-dimensional
private type `θ` drawn from a continuous distribution on an interval `[θlo, θhi]`. A (direct)
mechanism offers an **allocation** `x : ℝ → [0,1]` (the probability of trade / quantity) and a
**payment** `p : ℝ → ℝ` as functions of the reported type. Utility is quasilinear and
single-crossing: An agent of type `θ` reporting `r` gets `θ · x(r) − p(r)`.

## Main definitions

* `ScreeningEnv` — the interval `[θlo, θhi]`, the type distribution, and regularity conditions
  (support inside the interval, strictly positive continuous density).
* `AllocationRule` — an allocation `x : ℝ → ℝ` valued in `[0,1]`.
* `DirectMechanism` — an `AllocationRule` together with a payment schedule.
* `DirectMechanism.interimUtil` — the agent's on-path utility `θ · x(θ) − p(θ)`.

## Notes

The payment `p` is money paid by the agent (utility `θ·x − p`). This is the opposite sign from the
finite, multi-agent transfer convention, where transfers are money received by agents.

## References

* Mirrlees, J. A. 1971. “An Exploration in the Theory of Optimum Income Taxation.” *The Review of
  Economic Studies* 38 (2): 175. [https://doi.org/10.2307/2296779](https://doi.org/10.2307/2296779).
* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

mechanism design, screening, single parameter, myerson, quasilinear
-/

@[expose] public section

open Set MeasureTheory

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

/-- A single-parameter screening environment: A type interval `[θlo, θhi]` with a continuous type
distribution and regularity conditions on the density. -/
structure ScreeningEnv where
  /-- Lowest type. -/
  θlo : ℝ
  /-- Highest type. -/
  θhi : ℝ
  /-- The type interval is nondegenerate. -/
  hθ : θlo < θhi
  /-- The type distribution. -/
  dist : Econlib.Probability.ContDist
  /-- The distribution is supported inside the type interval. -/
  supp_subset : ∀ x, 0 < dist.density x → x ∈ Icc θlo θhi
  /-- The density is strictly positive on the interval. -/
  density_pos : ∀ x ∈ Icc θlo θhi, 0 < dist.density x
  /-- The density is continuous on the interval. -/
  density_cont : ContinuousOn dist.density (Icc θlo θhi)

open Econlib.Probability in
/-- The **uniform screening environment** on `[a, b]` (`a < b`): The type is distributed uniformly
on the interval, with constant density `1 / (b - a)`. This bundles the `ScreeningEnv` field block —
support, strict positivity, and continuity of the density — for the uniform distribution in one
call, so consumers need not re-prove them. The on-interval CDF is `F(θ) = (θ − a) / (b − a)`
(`ContDist.uniform_cdf_of_mem`) and the density is `1 / (b − a)`
(`ContDist.uniform_density_of_mem`). -/
def ScreeningEnv.uniform (a b : ℝ) (hab : a < b) : ScreeningEnv where
  θlo := a
  θhi := b
  hθ := hab
  dist := ContDist.uniform a b hab
  supp_subset x hx := by
    by_contra hmem
    rw [ContDist.uniform_density_eq_zero_of_not_mem a b hab hmem] at hx
    exact lt_irrefl 0 hx
  density_pos x hx := by
    rw [ContDist.uniform_density_of_mem a b hab hx]
    exact div_pos one_pos (by linarith)
  density_cont :=
    continuousOn_const.congr fun x hx => ContDist.uniform_density_of_mem a b hab hx

@[simp] lemma ScreeningEnv.uniform_θlo (a b : ℝ) (hab : a < b) :
    (ScreeningEnv.uniform a b hab).θlo = a := rfl

@[simp] lemma ScreeningEnv.uniform_θhi (a b : ℝ) (hab : a < b) :
    (ScreeningEnv.uniform a b hab).θhi = b := rfl

@[simp] lemma ScreeningEnv.uniform_dist (a b : ℝ) (hab : a < b) :
    (ScreeningEnv.uniform a b hab).dist = Econlib.Probability.ContDist.uniform a b hab := rfl

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-- The type interval `[θlo, θhi]`. -/
def types : Set ℝ := Icc E.θlo E.θhi

@[simp] lemma mem_types {θ : ℝ} : θ ∈ E.types ↔ θ ∈ Icc E.θlo E.θhi := Iff.rfl

lemma θlo_mem_types : E.θlo ∈ E.types := ⟨le_refl _, E.hθ.le⟩

lemma θhi_mem_types : E.θhi ∈ E.types := ⟨E.hθ.le, le_refl _⟩

/-- The density vanishes outside the type interval (contrapositive of `supp_subset`). -/
lemma density_eq_zero_of_notMem {θ : ℝ} (hθ : θ ∉ Icc E.θlo E.θhi) : E.dist.density θ = 0 := by
  rcases (E.dist.nonneg θ).lt_or_eq with hpos | hzero
  · exact absurd (E.supp_subset θ hpos) hθ
  · exact hzero.symm

/-- The per-bidder law puts no mass outside the type interval. -/
lemma toMeasure_compl_Icc_eq_zero : E.dist.toMeasure (Icc E.θlo E.θhi)ᶜ = 0 := by
  have h0 : ∀ᵐ x ∂(volume.restrict (Icc E.θlo E.θhi)ᶜ),
      ENNReal.ofReal (E.dist.density x) = 0 := by
    refine (ae_restrict_iff' measurableSet_Icc.compl).mpr (ae_of_all _ fun x hx => ?_)
    rw [E.density_eq_zero_of_notMem hx, ENNReal.ofReal_zero]
  rw [E.dist.toMeasure_eq, withDensity_apply _ measurableSet_Icc.compl,
    lintegral_congr_ae h0, lintegral_zero]

/-- The per-bidder law puts no mass outside the **open** type interval either: The two endpoints
`θlo, θhi` carry no mass (the law is atomless), so the closed and open intervals agree almost
everywhere. -/
lemma toMeasure_compl_Ioo_eq_zero : E.dist.toMeasure (Ioo E.θlo E.θhi)ᶜ = 0 := by
  -- Off the open interval one is either off the closed interval or at an endpoint.
  have hsub : (Ioo E.θlo E.θhi)ᶜ ⊆ (Icc E.θlo E.θhi)ᶜ ∪ {E.θlo} ∪ {E.θhi} := by
    intro x hx
    by_cases hicc : x ∈ Icc E.θlo E.θhi
    · rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hx
      rcases hx with h | h
      · exact Or.inl (Or.inr (le_antisymm h hicc.1))
      · exact Or.inr (le_antisymm hicc.2 h)
    · exact Or.inl (Or.inl hicc)
  refine le_antisymm ((measure_mono hsub).trans_eq ?_) (zero_le)
  exact measure_union_null (measure_union_null E.toMeasure_compl_Icc_eq_zero
    (measure_singleton _)) (measure_singleton _)

end ScreeningEnv

/-- An allocation rule: The probability (or quantity) of allocation as a function of the reported
type, valued in `[0, 1]`. The `[0,1]` bound is part of the type, not a downstream hypothesis. -/
structure AllocationRule (E : ScreeningEnv) where
  /-- The allocation as a function of the reported type. -/
  x : ℝ → ℝ
  /-- Allocations are nonnegative. -/
  nonneg : ∀ θ, 0 ≤ x θ
  /-- Allocations are at most one. -/
  le_one : ∀ θ, x θ ≤ 1

/-- A direct (revelation) mechanism for a screening environment: An allocation rule together with a
payment schedule `p : ℝ → ℝ` (money paid by the agent). -/
structure DirectMechanism (E : ScreeningEnv) where
  /-- The allocation rule. -/
  alloc : AllocationRule E
  /-- The payment schedule (money paid by the agent). -/
  p : ℝ → ℝ

namespace DirectMechanism

variable {E : ScreeningEnv} (M : DirectMechanism E)

/-- The allocation function of the mechanism. -/
def x (θ : ℝ) : ℝ := M.alloc.x θ

@[simp] lemma x_def (θ : ℝ) : M.x θ = M.alloc.x θ := rfl

lemma x_nonneg (θ : ℝ) : 0 ≤ M.x θ := M.alloc.nonneg θ

lemma x_le_one (θ : ℝ) : M.x θ ≤ 1 := M.alloc.le_one θ

/-- The agent's on-path interim utility: A type-`θ` agent reporting truthfully receives
`θ · x(θ) − p(θ)`. -/
def interimUtil (θ : ℝ) : ℝ := θ * M.x θ - M.p θ

@[simp] lemma interimUtil_def (θ : ℝ) : M.interimUtil θ = θ * M.x θ - M.p θ := rfl

end DirectMechanism

end Econlib.MechanismDesign.Transfers.SingleParameter
