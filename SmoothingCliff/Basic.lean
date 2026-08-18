import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Field

/-!
# Reduced-form allocation rules on the eligible region

This file formalizes the common vocabulary used by the finite-market frontier
results in *Smoothing the Cliff*. An eligible bid is represented by the subtype
`Set.Ici reserve`, so the paper's restriction to the eligible region is carried
by the type rather than repeated as a side condition.
-/

open scoped BigOperators

namespace SmoothingCliff

/-- A bid weakly above the reserve. -/
abbrev EligibleBid (reserve : ℝ) := Set.Ici reserve

/-- A profile on which every participant is eligible. -/
abbrev EligibleProfile (ι : Type*) (reserve : ℝ) := ι → EligibleBid reserve

/-- An interim expected-priority rule on eligible profiles. -/
abbrev InterimRule (ι : Type*) (reserve : ℝ) :=
  EligibleProfile ι reserve → ι → ℝ

/-- Replace one coordinate of an eligible profile. -/
def updateBid {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (b : EligibleProfile ι reserve) (i : ι) (z : EligibleBid reserve) :
    EligibleProfile ι reserve :=
  Function.update b i z

/-- Relabel a profile by a permutation of the agents. -/
def relabelProfile {ι : Type*} {reserve : ℝ} (π : Equiv.Perm ι)
    (b : EligibleProfile ι reserve) : EligibleProfile ι reserve :=
  fun i => b (π.symm i)

/-- Equivariance of an interim rule under relabeling of agents. -/
def Anonymous {ι : Type*} {reserve : ℝ} (x : InterimRule ι reserve) : Prop :=
  ∀ (π : Equiv.Perm ι) (b : EligibleProfile ι reserve) (i : ι),
    x (relabelProfile π b) (π i) = x b i

/-- An agent's allocation is monotone in her own eligible bid. -/
def OwnMonotone {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) : Prop :=
  ∀ (b : EligibleProfile ι reserve) (i : ι),
    Monotone (fun z : EligibleBid reserve => x (updateBid b i z) i)

/-- An agent's allocation is Lipschitz in her own eligible bid. -/
def OwnLipschitz {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (sensitivity : NNReal) (x : InterimRule ι reserve) : Prop :=
  ∀ (b : EligibleProfile ι reserve) (i : ι),
    LipschitzWith sensitivity (fun z : EligibleBid reserve => x (updateBid b i z) i)

/-- Raising one agent's bid weakly lowers every other agent's allocation. -/
def CrossMonotone {ι : Type*} {reserve : ℝ} [DecidableEq ι]
    (x : InterimRule ι reserve) : Prop :=
  ∀ (b : EligibleProfile ι reserve) (i j : ι), i ≠ j →
    Antitone (fun z : EligibleBid reserve => x (updateBid b j z) i)

/-- One-slot feasibility for a reduced-form expected allocation. -/
def OneSlotFeasible {ι : Type*} {reserve : ℝ} [Fintype ι]
    (weight : ℝ) (x : InterimRule ι reserve) : Prop :=
  (∀ b i, 0 ≤ x b i) ∧ (∀ b, ∑ i, x b i ≤ weight)

/-- The one-slot rule assigns all available priority mass. -/
def OneSlotNoWaste {ι : Type*} {reserve : ℝ} [Fintype ι]
    (weight : ℝ) (x : InterimRule ι reserve) : Prop :=
  ∀ b, ∑ i, x b i = weight

/-- Welfare of a reduced-form allocation at a truthful eligible profile. -/
def welfare {ι : Type*} {reserve : ℝ} [Fintype ι]
    (x : InterimRule ι reserve) (values : EligibleProfile ι reserve) : ℝ :=
  ∑ i, (values i : ℝ) * x values i

end SmoothingCliff
