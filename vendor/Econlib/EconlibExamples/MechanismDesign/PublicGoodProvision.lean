/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Public-Good Provision (Clarke 1971): Efficient and Truthful, but Not Individually Rational

The pivotal mechanism of Clarke (1971) is the canonical application of VCG to public goods. A
community of `n + 1` agents decides whether to provide a single binary public good (a bridge, a
streetlight) whose cost is shared per capita. The mechanism selects provision of the public good
when aggregate value exceeds aggregate cost (with provision decided arbitrarily at exact
indifference — a tie-break the strict directions below sidestep), makes truthful reporting a
dominant strategy,
and ensures that the resulting Clarke taxes generate no deficit. But unlike the second-price
auction, it cannot promise that participation is worthwhile: An agent who values the good below its
cost share is made strictly worse off by efficient provision, and no Clarke tax compensates it.

This file instantiates the general Groves/VCG API on the provision environment and proves the full
story: The three VCG guarantees, the concrete provision rule "provide iff `∑ᵢ θᵢ ≥ (n+1)·d`" (up to
tie-breaking), and the failure of individual rationality, both as the general failure of the
participation condition and as a concrete two-agent profile where an untaxed agent ends up strictly
negative.

## The story

A community of `n + 1` agents must decide whether to provide a binary public good at per-capita
cost `d`:

* Agent `i` privately values the good at `θᵢ ∈ {0, …, V}`. If the good is provided, everyone enjoys
  it and bears the cost share, so `i`'s net valuation is `θᵢ − d`; otherwise it is `0`.
* The good should be provided exactly when aggregate value covers aggregate cost, `∑ᵢ θᵢ ≥ (n+1)·d`
  — total social value of provision is `(∑ᵢ θᵢ) − (n+1)·d`.
* The planner asks each agent to report its value, provides when the reported aggregate covers the
  cost, and charges each agent its Clarke pivot tax (the externality its report imposes on the
  others).

We model this as a `QuasilinearEnvironment` with outcome space `Bool` (provide / don't) and
valuation `value i o θᵢ = if o then θᵢ − d else 0`; the prior is irrelevant to the VCG guarantees,
which are all ex-post.

## Why participation fails

The Clarke tax of a *non-pivotal* agent is zero — it taxes influence, not consumption — so the
mechanism has no instrument to compensate an agent dragged into a provision it dislikes. With cost
share `d = 1` and values `(0, 3)`, provision is efficient (`3 > 2`) and is decided by agent `1`
alone; agent `0`, untaxed, consumes a good it values at `0` while bearing the cost share, netting
`(0 − 1) + 0 = −1 < 0`. Contrast the second-price auction, where every valuation is nonnegative
(the `ParticipationCondition`), opting out costs nothing, and VCG is ex-post individually rational
(`secondPriceAuction_isExPostIR`).

Note that **no deficit is about the Clarke taxes only**: The production cost is financed by the
cost shares baked into the valuations, not by the mechanism's transfers, so
`publicGood_isNoDeficit` is not budget balance for the public good — which VCG cannot deliver
(Green–Laffont 1977). Also, **the sign of `d` matters for the narrative**: While the generic
theorems hold for any `d : ℝ`, the IR tension presumes `0 < d`. For `d ≤ 0` the good is a
subsidized free lunch and the participation condition holds, while for `d > V` provision is never
efficient.

## What this file proves

* `publicGood_isEfficient`, `publicGood_isDSIC`, `publicGood_isNoDeficit` — *the VCG guarantees*:
  The provision decision maximizes total social value, truthful reporting is a dominant strategy
  (no free-riding by misreporting), and the Clarke taxes never require a subsidy.
* `publicGood_alloc_provide_of_lt` / `publicGood_alloc_abstain_of_lt` — *the concrete provision
  rule*: The good is provided when `(n+1)·d < ∑ᵢ θᵢ` and withheld when `∑ᵢ θᵢ < (n+1)·d`; the weak
  converses `publicGood_cost_le_of_provide` / `publicGood_value_le_of_abstain` are all that
  survives tie-breaking, since `efficientAlloc` chooses arbitrarily at exact indifference.
* `publicGood_not_participation` — *the participation condition fails* for every positive cost
  share: A zero-value agent nets `−d < 0` from provision.
* `publicGood_not_isExPostIR` — *ex-post IR fails*: At the witness profile provision is
  efficient, yet the zero-value agent — not pivotal, hence untaxed — nets `−1 < 0`.

## Main definitions and theorems

* `publicGood n V d : QuasilinearEnvironment` — `n + 1` agents, outcomes `Bool`, values in
  `Fin (V + 1)`, net valuation `θᵢ − d` under provision.
* `publicGood_isEfficient` / `publicGood_isDSIC` / `publicGood_isNoDeficit` — the general VCG
  theorems, instantiated.
* `publicGood_truthful_isDominantStrategy` — truthfulness through the cohesion bridge: A
  dominant-strategy equilibrium of the induced Bayesian game.
* `publicGood_totalValue_provide` / `publicGood_totalValue_abstain` /
  `publicGood_provision_efficient_iff` — provision is (weakly) efficient iff aggregate value covers
  aggregate cost.
* `publicGood_total_cost` — aggregate cost is `(n + 1)·d`.
* `publicGood_alloc_provide_of_lt` / `publicGood_alloc_abstain_of_lt` and converses
  `publicGood_cost_le_of_provide` / `publicGood_value_le_of_abstain` — the realized VCG allocation
  follows the cost–value comparison.
* `publicGood_not_participation` — `¬ ParticipationCondition` for `0 < d`.
* `irAgent`, `irProfile` — the witness: Two agents, values `(0, 3)`, cost share `1`, with
  `irProfile_alloc` (provision is efficient) and `irProfile_exPostUtility` (the zero-value agent's
  truthful ex-post utility is exactly `−1`).
* `publicGood_not_isExPostIR` — VCG public-good provision is not ex-post individually rational.

## References

Clarke, Edward H. 1971. “Multipart Pricing of Public Goods.” Public Choice 11 (1): 17–33.
https://doi.org/10.1007/BF01726210.

Green, Jerry, and Jean-Jacques Laffont. 1977. “Characterization of Satisfactory Mechanisms for the
Revelation of Preferences for Public Goods.” Econometrica 45 (2): 427–38.
https://doi.org/10.2307/1911219.
-/

noncomputable section

namespace EconlibExamples.MechanismDesign.PublicGoodProvision

open Econlib.MechanismDesign.Transfers.General
open Econlib.GameTheory Econlib.Probability

variable (n V : ℕ) (d : ℝ)

/-- **The public-good provision environment.** There are `n + 1` agents and two outcomes (`Bool`:
Provide or not); each agent reports a value in `Fin (V + 1)`. If the good is provided, agent `i`'s
net valuation is its value minus its per-capita cost share `d`; otherwise it is `0`. The prior is
irrelevant to the VCG guarantees. -/
def publicGood : QuasilinearEnvironment where
  Agent := Fin (n + 1)
  Outcome := Bool
  Theta := fun _ => Fin (V + 1)
  value _ o t := if o = true then ((t.val : ℝ) - d) else 0
  prior := FinDist.uniform

@[simp] lemma publicGood_value (i : Fin (n + 1)) (o : Bool) (t : Fin (V + 1)) :
    (publicGood n V d).value i o t = if o = true then ((t.val : ℝ) - d) else 0 := rfl

/-! ## The VCG guarantees, instantiated -/

/-- The provision decision is efficient: It maximizes total social value. -/
theorem publicGood_isEfficient : (vcgMechanism (publicGood n V d)).IsEfficient :=
  vcgMechanism_isEfficient

/-- Truthful reporting of one's value is a dominant strategy. -/
theorem publicGood_isDSIC : (vcgMechanism (publicGood n V d)).IsDSIC :=
  vcgMechanism_isDSIC

/-- The Clarke taxes never run a deficit. This concerns the *Clarke taxes only*: The production
cost is financed by the per-capita shares baked into the valuations, not by the mechanism's
transfers, so this is not budget balance for the public good (which VCG cannot deliver, per
Green–Laffont). -/
theorem publicGood_isNoDeficit : (vcgMechanism (publicGood n V d)).IsNoDeficit :=
  vcgMechanism_isNoDeficit

/-- Truthful reporting read through the cohesion bridge: It is a dominant-strategy equilibrium of
the induced Bayesian game. -/
theorem publicGood_truthful_isDominantStrategy :
    (vcgMechanism (publicGood n V d)).toIndirect.IsDominantStrategy (fun _ θ_i => θ_i) :=
  (DirectMechanism.isDSIC_iff_isDominantStrategy_truthful _).mp (publicGood_isDSIC n V d)

/-! ## Efficient provision iff value covers cost -/

/-- Total social value of providing the good is aggregate value minus aggregate cost. -/
lemma publicGood_totalValue_provide (θ : (publicGood n V d).TypeProfile) :
    (publicGood n V d).totalValue true θ
      = (∑ i, ((θ i).val : ℝ)) - ∑ _i : (publicGood n V d).Agent, d := by
  rw [QuasilinearEnvironment.totalValue]
  simp only [publicGood_value, if_true]
  rw [Finset.sum_sub_distrib]

/-- Not providing the good yields zero social value. -/
lemma publicGood_totalValue_abstain (θ : (publicGood n V d).TypeProfile) :
    (publicGood n V d).totalValue false θ = 0 := by
  rw [QuasilinearEnvironment.totalValue]
  simp only [publicGood_value, Bool.false_eq_true, if_false]
  exact Finset.sum_const_zero

/-- **Provision is (weakly) efficient exactly when aggregate value covers aggregate cost.** -/
theorem publicGood_provision_efficient_iff (θ : (publicGood n V d).TypeProfile) :
    (publicGood n V d).totalValue false θ ≤ (publicGood n V d).totalValue true θ
      ↔ (∑ _i : (publicGood n V d).Agent, d) ≤ ∑ i, ((θ i).val : ℝ) := by
  rw [publicGood_totalValue_provide, publicGood_totalValue_abstain, sub_nonneg]

/-! ## The concrete provision rule

What the VCG allocation *does*: Provide exactly when aggregate value `∑ᵢ θᵢ` covers aggregate
cost `(n+1)·d` — up to tie-breaking at exact indifference, where `efficientAlloc` is an arbitrary
choice of maximizer. Hence the clean directions: Strict inequality decides the allocation, and the
allocation implies the weak inequality. -/

/-- Aggregate cost is the per-capita share summed over the `n + 1` agents. -/
lemma publicGood_total_cost :
    (∑ _i : (publicGood n V d).Agent, d) = (n + 1 : ℝ) * d := by
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (publicGood n V d).Agent = n + 1 := Fintype.card_fin (n + 1)
  rw [hcard, nsmul_eq_mul]
  push_cast
  ring

/-- **Efficiency, restated as a cost–value comparison.** The four allocation/cost theorems below all
turn on one fact: when the realized VCG allocation is `b`, choosing `b` is efficient, so the value
at the opposite outcome `!b` cannot beat it. Each call site instantiates `b` and rewrites both
`totalValue`s (`publicGood_totalValue_provide`/`_abstain`) and the cost (`publicGood_total_cost`),
turning this into the signed surplus inequality: a realized abstention (`b = false`) gives
surplus ≤ 0, a realized provision (`b = true`) gives surplus ≥ 0. -/
private lemma publicGood_efficient_compare {θ : (publicGood n V d).TypeProfile} {b : Bool}
    (h : (vcgMechanism (publicGood n V d)).alloc θ = b) :
    (publicGood n V d).totalValue (!b) θ ≤ (publicGood n V d).totalValue b θ := by
  -- `(vcgMechanism _).alloc = efficientAlloc`, which is a maximizer, so it weakly beats `!b`.
  have hmax := (publicGood n V d).efficientAlloc_isMaxOn θ (!b)
  rwa [show (publicGood n V d).efficientAlloc θ = b from h] at hmax

/-- **If aggregate value strictly exceeds aggregate cost, the good is provided.** -/
theorem publicGood_alloc_provide_of_lt {θ : (publicGood n V d).TypeProfile}
    (h : (n + 1 : ℝ) * d < ∑ i, ((θ i).val : ℝ)) :
    (vcgMechanism (publicGood n V d)).alloc θ = true := by
  by_contra hne
  -- If the maximizer abstained, abstention would weakly beat provision — contradicting strictness.
  have hcmp := publicGood_efficient_compare n V d (Bool.eq_false_iff.mpr hne)
  rw [Bool.not_false, publicGood_totalValue_provide, publicGood_totalValue_abstain,
    publicGood_total_cost] at hcmp
  linarith

/-- **If aggregate cost strictly exceeds aggregate value, the good is not provided.** -/
theorem publicGood_alloc_abstain_of_lt {θ : (publicGood n V d).TypeProfile}
    (h : (∑ i, ((θ i).val : ℝ)) < (n + 1 : ℝ) * d) :
    (vcgMechanism (publicGood n V d)).alloc θ = false := by
  by_cases halloc : (vcgMechanism (publicGood n V d)).alloc θ = true
  · -- If the maximizer provided, provision would weakly beat abstention — contradicting strictness.
    have hcmp := publicGood_efficient_compare n V d halloc
    rw [Bool.not_true, publicGood_totalValue_abstain, publicGood_totalValue_provide,
      publicGood_total_cost] at hcmp
    linarith
  · exact Bool.eq_false_iff.mpr halloc

/-- **Provision implies aggregate value weakly covers aggregate cost** (the converse of
`publicGood_alloc_provide_of_lt`, weak because of tie-breaking at indifference). -/
theorem publicGood_cost_le_of_provide {θ : (publicGood n V d).TypeProfile}
    (h : (vcgMechanism (publicGood n V d)).alloc θ = true) :
    (n + 1 : ℝ) * d ≤ ∑ i, ((θ i).val : ℝ) := by
  have hcmp := publicGood_efficient_compare n V d h
  rw [Bool.not_true, publicGood_totalValue_abstain, publicGood_totalValue_provide,
    publicGood_total_cost] at hcmp
  linarith

/-- **Abstention implies aggregate cost weakly covers aggregate value** (the converse of
`publicGood_alloc_abstain_of_lt`, weak because of tie-breaking at indifference). -/
theorem publicGood_value_le_of_abstain {θ : (publicGood n V d).TypeProfile}
    (h : (vcgMechanism (publicGood n V d)).alloc θ = false) :
    (∑ i, ((θ i).val : ℝ)) ≤ (n + 1 : ℝ) * d := by
  have hcmp := publicGood_efficient_compare n V d h
  rw [Bool.not_false, publicGood_totalValue_provide, publicGood_totalValue_abstain,
    publicGood_total_cost] at hcmp
  linarith

/-! ## The IR failure

The well-known tension, formalized. With a positive cost share the participation condition
fails outright (a zero-value agent nets `−d < 0` from provision), and ex-post individual
rationality fails: We exhibit an environment and a profile where provision is efficient
yet an agent ends up with strictly negative utility. Contrast `SecondPriceAuction.lean`, where the
participation condition holds and VCG is ex-post IR. -/

/-- **The participation condition fails whenever the cost share is positive**: An agent of value
`0` nets `−d < 0` from provision, so the hypothesis of `vcgMechanism_isExPostIR` is unavailable —
the well-known public-goods tension. (For `d ≤ 0` — a subsidy — the condition holds and the tension
vanishes; the economic narrative presumes `0 < d`.) -/
theorem publicGood_not_participation (hd : 0 < d) :
    ¬ (publicGood n V d).ParticipationCondition := by
  intro hpart
  have h := hpart ⟨0, Nat.succ_pos n⟩ true ⟨0, Nat.succ_pos V⟩
  rw [publicGood_value] at h
  norm_num at h
  linarith

/-! ### A concrete ex-post IR violation

Two agents, values in `{0, …, 3}`, cost share `d = 1`, profile `θ = (0, 3)`. Provision is
efficient — aggregate value `3` exceeds aggregate cost `2` — and agent `0` is *not* pivotal (agent
`1` alone wants provision), so it pays no Clarke tax. Yet it consumes a good it values at `0` while
bearing its cost share: Ex-post utility `(0 − 1) + 0 = −1 < 0`. -/

/-- The zero-value agent of the witness. -/
def irAgent : (publicGood 1 3 1).Agent := ⟨0, by norm_num⟩

/-- The witness profile: Agent `0` values the good at `0`, agent `1` at `3`. -/
def irProfile : (publicGood 1 3 1).TypeProfile := ![0, 3]

/-- Aggregate value at the witness profile is `3`. -/
private lemma irProfile_sum : (∑ i, ((irProfile i).val : ℝ)) = 3 := by
  change (∑ i : Fin 2, ((irProfile i).val : ℝ)) = 3
  rw [Fin.sum_univ_two]
  norm_num [irProfile]

/-- At the witness profile the good is provided: `3 > 2`. -/
lemma irProfile_alloc : (vcgMechanism (publicGood 1 3 1)).alloc irProfile = true := by
  refine publicGood_alloc_provide_of_lt 1 3 1 ?_
  rw [irProfile_sum]
  norm_num

/-- The value accruing to the *other* agent (agent `1`, value `3`) at each outcome: `2` under
provision, `0` under abstention. -/
private lemma irProfile_welfareExcl (o : Bool) :
    (publicGood 1 3 1).welfareExcl irAgent o irProfile = if o = true then 2 else 0 := by
  rw [QuasilinearEnvironment.welfareExcl_def]
  refine (Finset.sum_eq_single_of_mem
      ((⟨1, by norm_num⟩ : (publicGood 1 3 1).Agent))
      (Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by norm_num [irAgent]), Finset.mem_univ _⟩)
      (fun j hj hne => ?_)).trans ?_
  · -- the erase set contains only agent 1.
    exfalso
    have hlt : j.val < 2 := j.isLt
    have h0 : j.val ≠ 0 := fun h => Finset.ne_of_mem_erase hj (Fin.ext h)
    have h1 : j.val ≠ 1 := fun h => hne (Fin.ext h)
    omega
  · -- agent 1's value: `3 − 1 = 2` under provision, `0` otherwise.
    rw [publicGood_value]
    have hval : (irProfile (⟨1, by norm_num⟩ : (publicGood 1 3 1).Agent)).val = 3 := rfl
    cases o <;> norm_num [hval]

/-- Agent `0` is not pivotal: The others' preferred outcome is provision either way, so the Clarke
pivot is the others' value under provision, `2`. -/
private lemma irProfile_clarkePivot :
    (publicGood 1 3 1).clarkePivot irAgent irProfile = 2 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨o, ho⟩ := (publicGood 1 3 1).exists_clarkePivot_eq irAgent irProfile
    rw [ho, irProfile_welfareExcl o]
    cases o <;> norm_num
  · have h := (publicGood 1 3 1).welfareExcl_le_clarkePivot irAgent true irProfile
    rw [irProfile_welfareExcl true] at h
    simpa using h

/-- **The zero-value agent's ex-post utility is exactly `−1`**: It pays no Clarke tax (it is not
pivotal) but consumes a good it values at `0` while bearing the cost share `1`. The non-pivotal
reduction is `vcgMechanism_exPostUtility_of_nonpivotal`: utility collapses to the agent's own
valuation of the efficient outcome, here `value irAgent true 0 = (0 − 1) = −1`. -/
lemma irProfile_exPostUtility :
    (vcgMechanism (publicGood 1 3 1)).exPostUtility irAgent irProfile (irProfile irAgent)
      = -1 := by
  -- Agent `0` is non-pivotal: the Clarke pivot (`2`) equals the others' value at the efficient
  -- (provision) outcome, so the convenience corollary strips the transfer entirely.
  have halloc : (publicGood 1 3 1).efficientAlloc irProfile = true := irProfile_alloc
  have hnonpiv : (publicGood 1 3 1).clarkePivot irAgent irProfile
      = (publicGood 1 3 1).welfareExcl irAgent
          ((publicGood 1 3 1).efficientAlloc irProfile) irProfile := by
    rw [irProfile_clarkePivot, halloc, irProfile_welfareExcl true, if_pos rfl]
  rw [vcgMechanism_exPostUtility_of_nonpivotal irAgent irProfile hnonpiv, halloc,
    publicGood_value]
  norm_num [irProfile, irAgent]

/-- **VCG public-good provision is not ex-post individually rational.** At the witness profile,
provision is efficient but the zero-value agent nets `−1 < 0` — the formal counterpart of the
docstring's "well-known tension", and the contrast with `secondPriceAuction_isExPostIR`. -/
theorem publicGood_not_isExPostIR :
    ¬ (vcgMechanism (publicGood 1 3 1)).IsExPostIR := by
  intro hIR
  have h := hIR irAgent irProfile
  rw [irProfile_exPostUtility] at h
  norm_num at h

end EconlibExamples.MechanismDesign.PublicGoodProvision
