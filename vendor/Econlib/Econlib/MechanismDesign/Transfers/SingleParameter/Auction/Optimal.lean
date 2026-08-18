/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.RevenueIdentity
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.Ironing

/-!
# Symmetric IID auctions: Revenue optimality

Myerson's revenue bound for symmetric IID auctions. The virtual surplus of any feasible allocation
satisfies `∑ᵢ ψ(θᵢ)·xᵢ(θ) ≤ max(0, maxᵢ ψ(θᵢ))` pointwise, so no individually rational,
incentive-compatible auction can raise more expected revenue than the integrated optimal virtual
surplus. This upper bound holds for *every* environment; replacing `ψ` by the ironed virtual value
`ψ̄` gives a second, likewise universal, upper bound. The two differ not in validity but in
*tightness*: The ironed bound is attained by an incentive-compatible auction for every environment,
whereas the raw bound is attained only under regularity, when the highest-`ψ` allocation is
monotone. Attainment is established separately in `Auction.Achievable`
(`exists_optimal_auction_regular`, `exists_optimal_auction_ironed`); this file proves only the
bounds.

## Main definitions

* `AuctionEnv.optimalVirtualSurplus`: Pointwise maximum virtual surplus over feasible allocations
* `AuctionEnv.ironedOptimalVirtualSurplus`: The ironed analog

## Main statements

* `ExPostAlloc.virtualSurplus_le_pointwise`: Pointwise virtual-surplus feasibility bound
* `AuctionMechanism.revenue_le_optimalVirtualSurplus`: Myerson's revenue bound (raw `ψ`; universal,
  tight only under regularity)
* `ExPostAlloc.ironedVirtualSurplus_le_pointwise`: Pointwise ironed virtual-surplus feasibility
  bound
* `AuctionMechanism.revenue_le_ironedOptimalVirtualSurplus`: Myerson's revenue bound (ironed `ψ̄`;
  universal and always tight)

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, mechanism design, virtual value, revenue optimality, Myerson, ironing
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace AuctionEnv

variable (A : AuctionEnv)

/-- `Fin A.n` is nonempty (there is at least one bidder). -/
lemma univ_nonempty : (Finset.univ : Finset (Fin A.n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp A.hn)

/-- The **pointwise optimal virtual surplus** at a profile: The single unit goes to the highest
virtual value if positive, else is withheld (value `0`). This is the per-profile maximum of
`∑ᵢ ψ(θᵢ)·xᵢ` over feasible allocations — the *unconstrained* optimum, dropping the monotonicity
(incentive-compatibility) constraint. Its integral is the revenue the optimal auction attains under
regularity (`exists_optimal_auction_regular`); for irregular environments it is only an upper
bound, weakly above the optimal revenue `∫ ironedOptimalVirtualSurplus`. -/
def optimalVirtualSurplus (θ : A.Profile) : ℝ :=
  max 0 (Finset.univ.sup' A.univ_nonempty (fun i => A.base.virtualValue (θ i)))

/-- Integrability of the pointwise optimal surplus `max 0 (supᵢ g(θ i))` against the joint law,
given that each coordinate `θ ↦ g(θ i)` is integrable. Shared by the regular and ironed bounds. -/
private lemma integrable_max_zero_sup'_coord {g : ℝ → ℝ}
    (hgint : ∀ i, Integrable (fun θ : A.Profile => g (θ i)) A.jointLaw) :
    Integrable (fun θ : A.Profile =>
      max 0 (Finset.univ.sup' A.univ_nonempty (fun i => g (θ i)))) A.jointLaw := by
  -- Dominate by `∑ᵢ |g(θ i)|`: the per-coordinate abs values are integrable.
  have habs : Integrable (fun θ : A.Profile => ∑ i, |g (θ i)|) A.jointLaw :=
    MeasureTheory.integrable_finset_sum _ (fun i _ => (hgint i).abs)
  have hsup_meas : AEStronglyMeasurable
      (fun θ : A.Profile => Finset.univ.sup' A.univ_nonempty (fun i => g (θ i))) A.jointLaw := by
    have hrw : (fun θ : A.Profile => Finset.univ.sup' A.univ_nonempty (fun i => g (θ i)))
        = Finset.univ.sup' A.univ_nonempty (fun (i : Fin A.n) (θ : A.Profile) => g (θ i)) := by
      funext θ; rw [Finset.sup'_apply]
    rw [hrw]
    exact Finset.sup'_induction (p := fun h => AEStronglyMeasurable h A.jointLaw)
      _ _ (fun a ha b hb => ha.sup hb) (fun i _ => (hgint i).aestronglyMeasurable)
  refine Integrable.mono' habs (aestronglyMeasurable_const.sup hsup_meas)
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  refine max_le (Finset.sum_nonneg fun i _ => abs_nonneg _) ?_
  refine Finset.sup'_le _ _ fun i _ => ?_
  exact le_trans (le_abs_self _)
    (Finset.single_le_sum (fun j _ => abs_nonneg (g (θ j))) (Finset.mem_univ i))

end AuctionEnv

namespace ExPostAlloc

variable {A : AuctionEnv} (X : ExPostAlloc A)

/-- **Pointwise virtual-surplus bound.** At every profile, the virtual surplus of any feasible
allocation is at most `optimalVirtualSurplus θ`. -/
theorem virtualSurplus_le_pointwise (θ : A.Profile) :
    ∑ i, A.base.virtualValue (θ i) * X.x θ i ≤ A.optimalVirtualSurplus θ := by
  set V := A.optimalVirtualSurplus θ with hV
  have hV0 : 0 ≤ V := le_max_left _ _
  have hψ_le : ∀ i, A.base.virtualValue (θ i) ≤ V :=
    fun i => le_trans (Finset.le_sup' (fun j => A.base.virtualValue (θ j)) (Finset.mem_univ i))
      (le_max_right _ _)
  calc ∑ i, A.base.virtualValue (θ i) * X.x θ i
      ≤ ∑ i, V * X.x θ i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hψ_le i) (X.nonneg θ i)
    _ = V * ∑ i, X.x θ i := by rw [Finset.mul_sum]
    _ ≤ V * 1 := mul_le_mul_of_nonneg_left (X.feasible θ) hV0
    _ = V := mul_one V

/-- `density · virtualValue` is integrable against Lebesgue measure. -/
private lemma integrable_density_mul_virtualValue :
    Integrable (fun x => A.base.dist.density x * A.base.virtualValue x) := by
  set E := A.base with hE
  set f := fun x => E.dist.density x * E.virtualValue x with hf
  have hEqOn : EqOn f (fun x => E.dist.density x * x - (1 - E.dist.cdf x)) (Icc E.θlo E.θhi) := by
    intro x hx
    have hpos : E.dist.density x ≠ 0 := ne_of_gt (E.density_pos x hx)
    simp only [hf, ScreeningEnv.virtualValue_def]
    field_simp
  have hcont_rhs : ContinuousOn (fun x => E.dist.density x * x - (1 - E.dist.cdf x))
      (Icc E.θlo E.θhi) :=
    (E.density_cont.mul continuousOn_id).sub
      (continuousOn_const.sub E.dist.cdf_continuous.continuousOn)
  have hcont : ContinuousOn f (Icc E.θlo E.θhi) := hcont_rhs.congr hEqOn
  -- `f` is supported on `[θlo, θhi]`: off the interval the density vanishes, so `f = 0`.
  have hsupp : ∀ x, f x = (Icc E.θlo E.θhi).indicator f x := by
    intro x
    by_cases hx : x ∈ Icc E.θlo E.θhi
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hf]
      simp only
      rw [E.density_eq_zero_of_notMem hx, zero_mul]
  have hIO : IntegrableOn f (Icc E.θlo E.θhi) :=
    hcont.integrableOn_compact isCompact_Icc
  exact (hIO.integrable_indicator measurableSet_Icc).congr
    (Filter.Eventually.of_forall fun x => (hsupp x).symm)

/-- The single-coordinate virtual value `θ ↦ ψ(θ i)` is integrable against the joint law. -/
private lemma integrable_virtualValue_coord (i : Fin A.n) :
    Integrable (fun θ => A.base.virtualValue (θ i)) A.jointLaw := by
  haveI : IsProbabilityMeasure A.base.dist.toMeasure := A.base.dist.toMeasure_isProbability
  have hψ_toMeasure : Integrable A.base.virtualValue A.base.dist.toMeasure :=
    (A.base.dist.integrable_toMeasure_iff).mpr (integrable_density_mul_virtualValue (A := A))
  have hmap : Measure.map (Function.eval i) A.jointLaw = A.base.dist.toMeasure := by
    rw [AuctionEnv.jointLaw_def, ContDist.piMeasure, Measure.pi_map_eval]
    have hprod : (∏ _j ∈ Finset.univ.erase i, A.base.dist.toMeasure Set.univ) = 1 :=
      Finset.prod_eq_one fun _ _ => measure_univ
    rw [hprod, one_smul]
  have hmeas : AEMeasurable (Function.eval i) A.jointLaw := (measurable_pi_apply i).aemeasurable
  have hiff := integrable_map_measure (g := A.base.virtualValue) (f := Function.eval i)
    (by rw [hmap]; exact hψ_toMeasure.aestronglyMeasurable) hmeas
  rw [hmap] at hiff
  exact hiff.mp hψ_toMeasure

/-- The ex-post virtual surplus `θ ↦ ψ(θ i) · xᵢ(θ)` is integrable against the joint law. -/
lemma integrable_virtualSurplus (i : Fin A.n) :
    Integrable (fun θ => A.base.virtualValue (θ i) * X.x θ i) A.jointLaw := by
  have hψ : Integrable (fun θ => A.base.virtualValue (θ i)) A.jointLaw :=
    integrable_virtualValue_coord (A := A) i
  have hbdd := hψ.bdd_mul (f := fun θ => X.x θ i) (c := 1) (X.measurable i).aestronglyMeasurable
    (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [X.nonneg θ i], X.le_one θ i⟩)
  exact hbdd.congr (Filter.Eventually.of_forall fun θ => mul_comm (X.x θ i) _)

/-- **Ex-post → interim virtual-surplus bridge.** Bidder `i`'s expected interim virtual surplus
equals the expectation of its ex-post virtual surplus. -/
theorem expected_virtualSurplus_eq (i : Fin A.n) :
    A.base.dist.expect (fun t => A.base.virtualValue t * X.interimAlloc i t)
      = ∫ θ, A.base.virtualValue (θ i) * X.x θ i ∂A.jointLaw := by
  have hint : Integrable (fun θ => A.base.virtualValue (θ i) * X.x θ i) A.jointLaw :=
    X.integrable_virtualSurplus i
  have hreduce := ContDist.integral_piMeasure_reduce (d := A.base.dist) (n := A.n) i
    (h := fun θ => A.base.virtualValue (θ i) * X.x θ i)
    (by rw [AuctionEnv.jointLaw_def] at hint; exact hint)
  rw [AuctionEnv.jointLaw_def]
  rw [A.base.dist.expect_eq_measure_integral, hreduce]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.update_self]
  rw [integral_const_mul]
  rfl

end ExPostAlloc

namespace AuctionMechanism

variable {A : AuctionEnv} (M : AuctionMechanism A)

/-- **Myerson's optimal-auction bound.** No individually rational, incentive-compatible auction
raises more expected revenue than the integrated optimal virtual surplus. Individual rationality —
not a zero-rent normalization — is what bounds revenue by virtual surplus, so the bound holds over
the full admissible class, with no regularity assumption.

This is an upper bound. It is *attained* — and so equals the optimal revenue — only under
regularity, when the highest-`ψ` allocation is monotone hence incentive-compatible
(`exists_optimal_auction_regular`). For irregular environments the bound is generally loose; the
ironed bound `revenue_le_ironedOptimalVirtualSurplus` is the one attained without regularity. -/
theorem revenue_le_optimalVirtualSurplus (hbic : M.IsBIC) (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw) ≤ ∫ θ, A.optimalVirtualSurplus θ ∂A.jointLaw := by
  set ψ := A.base.virtualValue with hψ
  have hint : ∀ i, Integrable (fun θ => ψ (θ i) * M.alloc.x θ i) A.jointLaw :=
    fun i => M.alloc.integrable_virtualSurplus i
  have heq : (∑ i, A.base.dist.expect (fun t => ψ t * M.alloc.interimAlloc i t))
      = ∫ θ, ∑ i, ψ (θ i) * M.alloc.x θ i ∂A.jointLaw := by
    rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => M.alloc.expected_virtualSurplus_eq i
  have hOptInt : Integrable (fun θ => A.optimalVirtualSurplus θ) A.jointLaw :=
    A.integrable_max_zero_sup'_coord
      (fun i => ExPostAlloc.integrable_virtualValue_coord (A := A) i)
  calc (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      ≤ ∑ i, A.base.dist.expect (fun t => ψ t * M.alloc.interimAlloc i t) :=
        M.expected_revenue_le_virtual_surplus hbic hbir
    _ = ∫ θ, ∑ i, ψ (θ i) * M.alloc.x θ i ∂A.jointLaw := heq
    _ ≤ ∫ θ, A.optimalVirtualSurplus θ ∂A.jointLaw :=
        integral_mono (MeasureTheory.integrable_finset_sum _ (fun i _ => hint i)) hOptInt
          (fun θ => M.alloc.virtualSurplus_le_pointwise θ)

end AuctionMechanism

/-! ### The ironed optimal bound (irregular environments)

The raw bound above already holds for every environment, but it is generally *not tight*:
Without regularity the highest-`ψ` rule is non-monotone, so no incentive-compatible auction attains
it. Replacing `ψ` by the ironed virtual value `ψ̄`, which is monotone for every environment, yields
a bound that *is* attained without any regularity assumption (`exists_optimal_auction_ironed`), and
so equals the optimal revenue. -/

namespace AuctionEnv

variable (A : AuctionEnv)

/-- The **ironed** pointwise optimal virtual surplus: `optimalVirtualSurplus` with `ψ̄` in place of
`ψ`. -/
def ironedOptimalVirtualSurplus (θ : A.Profile) : ℝ :=
  max 0 (Finset.univ.sup' A.univ_nonempty (fun i => A.base.ironedVirtualValue (θ i)))

end AuctionEnv

namespace ExPostAlloc

variable {A : AuctionEnv} (X : ExPostAlloc A)

/-- **Pointwise ironed virtual-surplus bound** (mirror of `virtualSurplus_le_pointwise` with
`ψ̄`). -/
theorem ironedVirtualSurplus_le_pointwise (θ : A.Profile) :
    ∑ i, A.base.ironedVirtualValue (θ i) * X.x θ i ≤ A.ironedOptimalVirtualSurplus θ := by
  set V := A.ironedOptimalVirtualSurplus θ with hV
  have hV0 : 0 ≤ V := le_max_left _ _
  have hψ_le : ∀ i, A.base.ironedVirtualValue (θ i) ≤ V :=
    fun i => le_trans (Finset.le_sup' (fun j => A.base.ironedVirtualValue (θ j))
      (Finset.mem_univ i)) (le_max_right _ _)
  calc ∑ i, A.base.ironedVirtualValue (θ i) * X.x θ i
      ≤ ∑ i, V * X.x θ i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hψ_le i) (X.nonneg θ i)
    _ = V * ∑ i, X.x θ i := by rw [Finset.mul_sum]
    _ ≤ V * 1 := mul_le_mul_of_nonneg_left (X.feasible θ) hV0
    _ = V := mul_one V

/-- The ironed virtual value `θ ↦ ψ̄(θ i)` is integrable against the joint law. -/
lemma integrable_ironedVirtualValue_coord (i : Fin A.n) :
    Integrable (fun θ => A.base.ironedVirtualValue (θ i)) A.jointLaw := by
  have hmeas : Measurable (fun θ : A.Profile => A.base.ironedVirtualValue (θ i)) :=
    ((A.base.ironedVVQuantile_monotone.measurable.comp
      A.base.dist.cdf_continuous.measurable)).comp (measurable_pi_apply i)
  set C := |A.base.ironedVVQuantile 0| + |A.base.ironedVVQuantile 1| with hC
  refine (integrable_const C).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  obtain ⟨h0, h1⟩ := A.base.ironedVirtualValue_bdd (θ i)
  rw [Real.norm_eq_abs, abs_le]
  refine ⟨?_, ?_⟩
  · -- `−C ≤ ψ̄`, since `ψ̄ ≥ ĥ(0) ≥ −|ĥ(0)| ≥ −C`.
    have hlo : -|A.base.ironedVVQuantile 0| ≤ A.base.ironedVirtualValue (θ i) :=
      le_trans (neg_abs_le _) h0
    have : |A.base.ironedVVQuantile 0| ≤ C := by
      rw [hC]; linarith [abs_nonneg (A.base.ironedVVQuantile 1)]
    linarith
  · -- `ψ̄ ≤ C`, since `ψ̄ ≤ ĥ(1) ≤ |ĥ(1)| ≤ C`.
    have hhi : A.base.ironedVirtualValue (θ i) ≤ |A.base.ironedVVQuantile 1| :=
      le_trans h1 (le_abs_self _)
    have : |A.base.ironedVVQuantile 1| ≤ C := by
      rw [hC]; linarith [abs_nonneg (A.base.ironedVVQuantile 0)]
    linarith

/-- The ex-post ironed virtual surplus `θ ↦ ψ̄(θ i)·xᵢ(θ)` is integrable against the joint law. -/
lemma integrable_ironedVirtualSurplus (i : Fin A.n) :
    Integrable (fun θ => A.base.ironedVirtualValue (θ i) * X.x θ i) A.jointLaw := by
  have hψ : Integrable (fun θ => A.base.ironedVirtualValue (θ i)) A.jointLaw :=
    integrable_ironedVirtualValue_coord (A := A) i
  have hbdd := hψ.bdd_mul (f := fun θ => X.x θ i) (c := 1)
    (X.measurable i).aestronglyMeasurable
    (ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [X.nonneg θ i], X.le_one θ i⟩)
  exact hbdd.congr (Filter.Eventually.of_forall fun θ => mul_comm (X.x θ i) _)

/-- **Ex-post → interim ironed virtual-surplus bridge** (ironed analog of
`expected_virtualSurplus_eq`). -/
theorem expected_ironedVirtualSurplus_eq (i : Fin A.n) :
    A.base.dist.expect (fun t => A.base.ironedVirtualValue t * X.interimAlloc i t)
      = ∫ θ, A.base.ironedVirtualValue (θ i) * X.x θ i ∂A.jointLaw := by
  have hint : Integrable (fun θ => A.base.ironedVirtualValue (θ i) * X.x θ i) A.jointLaw :=
    X.integrable_ironedVirtualSurplus i
  have hreduce := ContDist.integral_piMeasure_reduce (d := A.base.dist) (n := A.n) i
    (h := fun θ => A.base.ironedVirtualValue (θ i) * X.x θ i)
    (by rw [AuctionEnv.jointLaw_def] at hint; exact hint)
  rw [AuctionEnv.jointLaw_def]
  rw [A.base.dist.expect_eq_measure_integral, hreduce]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.update_self]
  rw [integral_const_mul]
  rfl

end ExPostAlloc

namespace AuctionEnv

variable (A : AuctionEnv)

/-- The ironed optimal virtual surplus is integrable against the joint law. -/
lemma integrable_ironedOptimalVirtualSurplus :
    Integrable (fun θ => A.ironedOptimalVirtualSurplus θ) A.jointLaw :=
  A.integrable_max_zero_sup'_coord
    (fun i => ExPostAlloc.integrable_ironedVirtualValue_coord (A := A) i)

end AuctionEnv

namespace AuctionMechanism

variable {A : AuctionEnv} (M : AuctionMechanism A)

/-- **Ironed optimal-auction bound.** Without any regularity assumption, no individually rational,
incentive-compatible auction raises more expected revenue than the integrated ironed optimal
virtual surplus. As in the raw case, individual rationality (not a zero-rent normalization) is what
bounds revenue by virtual surplus. Unlike the raw bound, this one is tight for every environment:
It is attained by an incentive-compatible auction (`exists_optimal_auction_ironed`), so it equals
the optimal revenue. -/
theorem revenue_le_ironedOptimalVirtualSurplus (hbic : M.IsBIC) (hbir : M.IsBIR) :
    (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      ≤ ∫ θ, A.ironedOptimalVirtualSurplus θ ∂A.jointLaw := by
  set ψ := A.base.virtualValue with hψ
  set ψbar := A.base.ironedVirtualValue with hψbar
  have hrev : (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      ≤ ∑ i, A.base.dist.expect (fun t => ψ t * M.alloc.interimAlloc i t) :=
    M.expected_revenue_le_virtual_surplus hbic hbir
  have hiron : ∀ i, A.base.dist.expect (fun t => ψ t * M.alloc.interimAlloc i t)
      ≤ A.base.dist.expect (fun t => ψbar t * M.alloc.interimAlloc i t) := by
    intro i
    have hmono_i : MonotoneAlloc (M.reducedMechanism i).alloc :=
      (M.reducedMechanism i).isBIC_implies_monotone (hbic i)
    have h := A.base.expected_virtualSurplus_le_ironed (M.reducedMechanism i) hmono_i
    simpa only [AuctionMechanism.reducedMechanism_x] using h
  have hbridge : ∑ i, A.base.dist.expect (fun t => ψbar t * M.alloc.interimAlloc i t)
      = ∫ θ, ∑ i, ψbar (θ i) * M.alloc.x θ i ∂A.jointLaw := by
    have hint : ∀ i, Integrable (fun θ => ψbar (θ i) * M.alloc.x θ i) A.jointLaw :=
      fun i => M.alloc.integrable_ironedVirtualSurplus i
    rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => M.alloc.expected_ironedVirtualSurplus_eq i
  calc (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
      ≤ ∑ i, A.base.dist.expect (fun t => ψ t * M.alloc.interimAlloc i t) := hrev
    _ ≤ ∑ i, A.base.dist.expect (fun t => ψbar t * M.alloc.interimAlloc i t) :=
        Finset.sum_le_sum fun i _ => hiron i
    _ = ∫ θ, ∑ i, ψbar (θ i) * M.alloc.x θ i ∂A.jointLaw := hbridge
    _ ≤ ∫ θ, A.ironedOptimalVirtualSurplus θ ∂A.jointLaw :=
        integral_mono
          (MeasureTheory.integrable_finset_sum _
            (fun i _ => M.alloc.integrable_ironedVirtualSurplus i))
          A.integrable_ironedOptimalVirtualSurplus
          (fun θ => M.alloc.ironedVirtualSurplus_le_pointwise θ)

end AuctionMechanism

namespace AuctionEnv

variable (A : AuctionEnv)

/-! ### Regularity collapses the two bounds -/

/-- **Regularity ⇒ ironing is pointwise inert (interior profiles).** When the base environment is
Myerson-regular, the ironed pointwise optimal virtual surplus equals the raw one at every profile
whose coordinates all lie strictly inside the type interval, because `ψ̄ = ψ` there
(`ScreeningEnv.ironedVirtualValue_eq_virtualValue_of_regular`). -/
lemma ironedOptimalVirtualSurplus_eq_optimalVirtualSurplus_of_regular
    (hreg : A.base.Regular) {θ : A.Profile}
    (hθ : ∀ i, θ i ∈ Ioo A.base.θlo A.base.θhi) :
    A.ironedOptimalVirtualSurplus θ = A.optimalVirtualSurplus θ := by
  unfold ironedOptimalVirtualSurplus optimalVirtualSurplus
  -- The inner per-coordinate functions coincide, so the `max 0 (sup' …)` wrappers match.
  have hfun : (fun i => A.base.ironedVirtualValue (θ i))
      = (fun i => A.base.virtualValue (θ i)) := by
    funext i
    exact A.base.ironedVirtualValue_eq_virtualValue_of_regular hreg (hθ i)
  rw [hfun]

/-- **Regularity collapses the two optimal-auction bounds.** Under Myerson regularity the
integrated ironed optimal virtual surplus equals the integrated raw optimal virtual surplus: The
two differ only on the boundary `{θlo, θhi}` of each coordinate, a null set under the atomless
joint law. Hence the raw bound (`AuctionMechanism.revenue_le_optimalVirtualSurplus`) and the ironed
bound (`AuctionMechanism.revenue_le_ironedOptimalVirtualSurplus`) share the same right-hand side,
so for regular environments the universally-valid ironed bound is no weaker than the raw one. -/
theorem integral_ironedOptimalVirtualSurplus_eq_of_regular (hreg : A.base.Regular) :
    ∫ θ, A.ironedOptimalVirtualSurplus θ ∂A.jointLaw
      = ∫ θ, A.optimalVirtualSurplus θ ∂A.jointLaw := by
  refine integral_congr_ae ?_
  filter_upwards [A.ae_forall_mem_Ioo] with θ hθ
  exact A.ironedOptimalVirtualSurplus_eq_optimalVirtualSurplus_of_regular hreg hθ

end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
