/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.SingleParameter.Auction.Optimal
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.MyersonLemma

/-!
# Symmetric IID auctions: Achievability of the optimal bound

This file constructs auctions that attain the optimal virtual surplus bounds established in
`Optimal.lean`. The **highest-value allocation** awards the unit to the bidder with the highest
score `v(θᵢ)`, if that score is nonnegative, breaking ties by least index. Built generically in a
score function `v`, it is instantiated with `v = ψ` (regular environments) and `v = ψ̄` (ironed,
all environments).

## Main definitions

* `AuctionEnv.highestAlloc v` — the ex-post allocation that awards the unit to the top scorer.
* `AuctionEnv.optimalAlloc` — highest-`ψ` allocation (regular case).
* `AuctionEnv.ironedAlloc` — highest-`ψ̄` allocation (general case).
* `ExPostAlloc.myersonMechanism` — pairs an ex-post allocation with Myerson payments.

## Main statements

* `highestAlloc_virtualSurplus_eq` — pointwise optimality: `∑ᵢ v(θᵢ)·xᵢ = max 0 (maxᵢ v(θᵢ))`.
* `highestAlloc_interimAlloc_monotoneOn` — when `v` is monotone on the type interval, each bidder's
  interim allocation is monotone (implementable by Myerson's lemma).
* `exists_optimal_auction_regular` — under regularity, an incentive-compatible, individually
  rational auction whose expected revenue equals the optimal virtual surplus bound.
* `exists_optimal_auction_ironed` — without any regularity assumption, an incentive-compatible,
  individually rational auction whose expected revenue equals the ironed optimal virtual surplus
  bound.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

auction, optimal auction, virtual surplus, Myerson, ironing, achievability
-/

@[expose] public section

open Set MeasureTheory Function Econlib.Probability

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ExPostAlloc

variable {A : AuctionEnv}

/-- The reduced-form interim allocation `interimAlloc i t = 𝔼_{θ₋ᵢ}[xᵢ]` is measurable in `t`. -/
lemma interimAlloc_measurable (X : ExPostAlloc A) (i : Fin A.n) :
    Measurable (X.interimAlloc i) := by
  have hupd : Measurable (fun p : ℝ × A.Profile => Function.update p.2 i p.1) :=
    measurable_update'.comp measurable_swap
  have hg : Measurable (fun p : ℝ × A.Profile => X.x (Function.update p.2 i p.1) i) :=
    (X.measurable i).comp hupd
  have hsm := hg.stronglyMeasurable.integral_prod_right' (ν := A.jointLaw)
  exact hsm.measurable

/-- The interim allocation is interval-integrable on every interval. -/
lemma intervalIntegrable_interimAlloc (X : ExPostAlloc A) (i : Fin A.n) (a b : ℝ) :
    IntervalIntegrable (X.interimAlloc i) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_
    (X.interimAlloc_measurable i).aestronglyMeasurable ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top.ne
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun t _ => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [X.interimAlloc_nonneg i t], X.interimAlloc_le_one i t⟩

end ExPostAlloc

namespace AuctionEnv

variable (A : AuctionEnv) (v : ℝ → ℝ)

/-- Bidder `i` is the **top bidder** at profile `θ` for the score `v`: Its score is nonnegative, no
bidder scores higher, and no lower-indexed bidder ties it. The lex tie-break makes the winner
unique. -/
@[mk_iff] structure IsTopBidder (θ : A.Profile) (i : Fin A.n) : Prop where
  /-- The winner's score is nonnegative. -/
  nonneg : 0 ≤ v (θ i)
  /-- No bidder scores strictly higher. -/
  is_max : ∀ j, v (θ j) ≤ v (θ i)
  /-- No lower-indexed bidder ties (the lex tie-break). -/
  lex_tiebreak : ∀ j, j < i → v (θ j) < v (θ i)

variable {A v}

/-- At most one bidder is the top bidder (the lex tie-break breaks ties). -/
lemma isTopBidder_unique {θ : A.Profile} {i i' : Fin A.n}
    (hi : A.IsTopBidder v θ i) (hi' : A.IsTopBidder v θ i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd (hi'.lex_tiebreak i hlt) (not_lt.mpr (hi.is_max i'))
  · exact heq
  · exact absurd (hi.lex_tiebreak i' hgt) (not_lt.mpr (hi'.is_max i))

variable (A v)

/-- The winner set `{θ | bidder i is top}` is measurable when `v` is measurable. -/
lemma measurableSet_isTopBidder (hv : Measurable v) (i : Fin A.n) :
    MeasurableSet {θ : A.Profile | A.IsTopBidder v θ i} := by
  have hvi : ∀ j : Fin A.n, Measurable (fun θ : A.Profile => v (θ j)) :=
    fun j => hv.comp (measurable_pi_apply j)
  have h1 : MeasurableSet {θ : A.Profile | 0 ≤ v (θ i)} :=
    measurableSet_le measurable_const (hvi i)
  have h2 : MeasurableSet {θ : A.Profile | ∀ j, v (θ j) ≤ v (θ i)} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hvi j) (hvi i))
  have h3 : MeasurableSet {θ : A.Profile | ∀ j, j < i → v (θ j) < v (θ i)} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter (fun j => ?_)
    rcases lt_or_ge j i with hji | hji
    · have heqj : {θ : A.Profile | j < i → v (θ j) < v (θ i)} = {θ | v (θ j) < v (θ i)} := by
        ext θ; simp only [mem_setOf_eq, imp_iff_right hji]
      rw [heqj]; exact measurableSet_lt (hvi j) (hvi i)
    · have huniv : {θ : A.Profile | j < i → v (θ j) < v (θ i)} = univ := by
        ext θ; simp only [mem_setOf_eq, mem_univ, iff_true]
        exact fun h => absurd h (not_lt.mpr hji)
      rw [huniv]; exact MeasurableSet.univ
  have heq : {θ : A.Profile | A.IsTopBidder v θ i}
      = {θ | 0 ≤ v (θ i)} ∩ {θ | ∀ j, v (θ j) ≤ v (θ i)}
        ∩ {θ | ∀ j, j < i → v (θ j) < v (θ i)} := by
    ext θ; simp only [isTopBidder_iff, mem_setOf_eq, mem_inter_iff]; tauto
  rw [heq]
  exact (h1.inter h2).inter h3

/-- The **highest-value allocation**: Award the unit to the top bidder for the score `v`. -/
def highestAlloc (hv : Measurable v) : ExPostAlloc A where
  x θ i := Set.indicator {θ' : A.Profile | A.IsTopBidder v θ' i} (fun _ => (1 : ℝ)) θ
  nonneg θ i := Set.indicator_nonneg (fun _ _ => zero_le_one) θ
  feasible θ := by
    by_cases hex : ∃ i, A.IsTopBidder v θ i
    · obtain ⟨w, hw⟩ := hex
      have hsum := Finset.sum_eq_single_of_mem (a := w) (Finset.mem_univ w)
        (f := fun i => Set.indicator {θ' : A.Profile | A.IsTopBidder v θ' i} (fun _ => (1 : ℝ)) θ)
        (fun i _ hiw => by
          dsimp only
          apply Set.indicator_of_notMem
          intro hmem; exact hiw (isTopBidder_unique hmem hw))
      have hval : (∑ i, Set.indicator {θ' : A.Profile | A.IsTopBidder v θ' i}
          (fun _ => (1 : ℝ)) θ) = 1 := by
        rw [hsum]; exact Set.indicator_of_mem hw (fun _ => (1 : ℝ))
      exact le_of_eq hval
    · push Not at hex
      have hzero : ∀ i, Set.indicator {θ' : A.Profile | A.IsTopBidder v θ' i}
          (fun _ => (1 : ℝ)) θ = 0 := by
        intro i; apply Set.indicator_of_notMem; exact hex i
      simp only [hzero, Finset.sum_const_zero]; exact zero_le_one
  measurable i := (measurable_const).indicator (A.measurableSet_isTopBidder v hv i)

variable {A v}

@[simp] lemma highestAlloc_x (hv : Measurable v) (θ : A.Profile) (i : Fin A.n) :
    (A.highestAlloc v hv).x θ i
      = Set.indicator {θ' : A.Profile | A.IsTopBidder v θ' i} (fun _ => (1 : ℝ)) θ := rfl

/-- The top bidder receives the whole unit. -/
lemma highestAlloc_x_of_top (hv : Measurable v) {θ : A.Profile} {i : Fin A.n}
    (h : A.IsTopBidder v θ i) : (A.highestAlloc v hv).x θ i = 1 := by
  rw [highestAlloc_x]; exact Set.indicator_of_mem h (fun _ => (1 : ℝ))

/-- A non-top bidder receives nothing. -/
lemma highestAlloc_x_of_not_top (hv : Measurable v) {θ : A.Profile} {i : Fin A.n}
    (h : ¬ A.IsTopBidder v θ i) : (A.highestAlloc v hv).x θ i = 0 := by
  rw [highestAlloc_x]; exact Set.indicator_of_notMem h (fun _ => (1 : ℝ))

/-- When the top score is nonnegative there is a least-index top bidder, and it attains the maximum
score. -/
lemma exists_isTopBidder_of_sup'_nonneg {θ : A.Profile}
    (hm : 0 ≤ Finset.univ.sup' A.univ_nonempty (fun i => v (θ i))) :
    ∃ w, A.IsTopBidder v θ w ∧
      v (θ w) = Finset.univ.sup' A.univ_nonempty (fun i => v (θ i)) := by
  set m := Finset.univ.sup' A.univ_nonempty (fun i => v (θ i)) with hm_def
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' A.univ_nonempty (fun i => v (θ i))
  set S := Finset.univ.filter (fun i => v (θ i) = m) with hS
  have hSne : S.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hi₀.symm⟩⟩
  refine ⟨S.min' hSne, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]; exact hm
  · intro j
    rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]
    exact Finset.le_sup' (fun i => v (θ i)) (Finset.mem_univ j)
  · intro j hjw
    rw [(Finset.mem_filter.mp (S.min'_mem hSne)).2]
    -- `j < min' S`, so `j ∉ S`, so `v(θ j) ≠ m`; with `v(θ j) ≤ m` this is strict.
    have hjnotS : j ∉ S := fun hjS => absurd (S.min'_le j hjS) (not_le.mpr hjw)
    have hjne : v (θ j) ≠ m :=
      fun h => hjnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    exact lt_of_le_of_ne (Finset.le_sup' (fun i => v (θ i)) (Finset.mem_univ j)) hjne
  · exact (Finset.mem_filter.mp (S.min'_mem hSne)).2

/-- **Pointwise optimality of the highest-value allocation.** At every profile its virtual surplus
attains the per-profile maximum `max 0 (maxᵢ v(θᵢ))`: The unit goes to the highest score if that is
nonnegative, else is withheld. -/
theorem highestAlloc_virtualSurplus_eq (hv : Measurable v) (θ : A.Profile) :
    ∑ i, v (θ i) * (A.highestAlloc v hv).x θ i
      = max 0 (Finset.univ.sup' A.univ_nonempty (fun i => v (θ i))) := by
  set m := Finset.univ.sup' A.univ_nonempty (fun i => v (θ i)) with hm_def
  by_cases hm : 0 ≤ m
  · obtain ⟨w, hw, hwm⟩ := exists_isTopBidder_of_sup'_nonneg (v := v) hm
    rw [max_eq_right hm]
    have hsum := Finset.sum_eq_single_of_mem (a := w) (Finset.mem_univ w)
      (f := fun i => v (θ i) * (A.highestAlloc v hv).x θ i)
      (fun i _ hiw => by
        dsimp only
        rw [highestAlloc_x_of_not_top hv (fun hmem => hiw (isTopBidder_unique hmem hw)), mul_zero])
    rw [hsum]
    dsimp only
    rw [highestAlloc_x_of_top hv hw, mul_one, hwm]
  · push Not at hm
    rw [max_eq_left hm.le]
    have hzero : ∀ i, v (θ i) * (A.highestAlloc v hv).x θ i = 0 := by
      intro i
      have hno : ¬ A.IsTopBidder v θ i := by
        intro hi
        exact absurd (le_trans hi.nonneg (Finset.le_sup' (fun j => v (θ j)) (Finset.mem_univ i)))
          (not_le.mpr hm)
      rw [highestAlloc_x_of_not_top hv hno, mul_zero]
    simp only [hzero, Finset.sum_const_zero]

/-- **Own-type monotonicity of the winner indicator.** If bidder `i` is the top bidder when it
reports `t`, it is still the top bidder reporting any higher type `t'` (within the type interval):
Raising its own score `v t ≤ v t'` only strengthens every comparison against the fixed rivals. -/
lemma isTopBidder_update_mono (hvmono : MonotoneOn v A.base.types) {θ : A.Profile} {i : Fin A.n}
    {t t' : ℝ} (ht : t ∈ A.base.types) (ht' : t' ∈ A.base.types) (htt' : t ≤ t')
    (h : A.IsTopBidder v (update θ i t) i) : A.IsTopBidder v (update θ i t') i := by
  have hvle : v t ≤ v t' := hvmono ht ht' htt'
  obtain ⟨h0, hmax, hlt⟩ := h
  rw [update_self] at h0 hmax hlt
  refine ⟨by rw [update_self]; linarith, fun j => ?_, fun j hji => ?_⟩
  · rw [update_self]
    by_cases hj : j = i
    · subst hj; rw [update_self]
    · rw [update_of_ne hj]
      have hj_le := hmax j
      rw [update_of_ne hj] at hj_le
      linarith
  · rw [update_self]
    have hjne : j ≠ i := ne_of_lt hji
    rw [update_of_ne hjne]
    have hj_lt := hlt j hji
    rw [update_of_ne hjne] at hj_lt
    linarith

/-- **Interim monotonicity of the highest-value allocation.** When the score `v` is monotone on the
type interval, each bidder's reduced-form interim allocation is monotone, hence implementable by
Myerson's lemma. -/
theorem highestAlloc_interimAlloc_monotoneOn (hv : Measurable v)
    (hvmono : MonotoneOn v A.base.types) (i : Fin A.n) :
    MonotoneOn ((A.highestAlloc v hv).interimAlloc i) A.base.types := by
  intro t ht t' ht' htt'
  rw [ExPostAlloc.interimAlloc_def, ExPostAlloc.interimAlloc_def]
  refine integral_mono ((A.highestAlloc v hv).integrable_interim_integrand i t)
    ((A.highestAlloc v hv).integrable_interim_integrand i t') (fun θ => ?_)
  by_cases h : A.IsTopBidder v (update θ i t) i
  · rw [highestAlloc_x_of_top hv h,
      highestAlloc_x_of_top hv (isTopBidder_update_mono hvmono ht ht' htt' h)]
  · rw [highestAlloc_x_of_not_top hv h]
    exact (A.highestAlloc v hv).nonneg (update θ i t') i

/-- The winner predicate depends on the own type only through the score. If `v t = v t'`, bidder
`i` is the top bidder reporting `t` exactly when it is reporting `t'` (every comparison is against
the common value `v t = v t'`, and the rivals' values are unchanged). -/
lemma isTopBidder_update_congr {θ : A.Profile} {i : Fin A.n} {t t' : ℝ} (h : v t = v t')
    (htop : A.IsTopBidder v (update θ i t) i) : A.IsTopBidder v (update θ i t') i := by
  obtain ⟨h0, hmax, hlt⟩ := htop
  rw [update_self] at h0 hmax hlt
  refine ⟨by rw [update_self, ← h]; exact h0, fun j => ?_, fun j hji => ?_⟩
  · rw [update_self, ← h]
    by_cases hj : j = i
    · subst hj; rw [update_self]; exact le_of_eq h.symm
    · rw [update_of_ne hj]; have := hmax j; rwa [update_of_ne hj] at this
  · rw [update_self, ← h]
    have hjne : j ≠ i := ne_of_lt hji
    rw [update_of_ne hjne]; have := hlt j hji; rwa [update_of_ne hjne] at this

/-- **The interim allocation is flat on level sets of the score.** If `v t = v t'`, the highest-`v`
rule gives bidder `i` the same interim winning probability at `t` and `t'`. Where the score is
constant, so is the interim allocation, which is the contact-set condition behind complementary
slackness. -/
lemma highestAlloc_interimAlloc_congr (hv : Measurable v) (i : Fin A.n) {t t' : ℝ}
    (h : v t = v t') :
    (A.highestAlloc v hv).interimAlloc i t = (A.highestAlloc v hv).interimAlloc i t' := by
  rw [ExPostAlloc.interimAlloc_def, ExPostAlloc.interimAlloc_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  dsimp only
  by_cases htop : A.IsTopBidder v (update θ i t) i
  · rw [highestAlloc_x_of_top hv htop,
      highestAlloc_x_of_top hv (isTopBidder_update_congr h htop)]
  · rw [highestAlloc_x_of_not_top hv htop,
      highestAlloc_x_of_not_top hv (fun htop' => htop (isTopBidder_update_congr h.symm htop'))]

/-- **Order-statistic reduced form.** For a strictly monotone score `v` (e.g. the value itself),
the highest-`v` allocation gives bidder `i` interim winning probability `F(t) ^ (n-1)`: Conditional
on its own value `t` (with `0 ≤ v t`, so the unit is awarded), `i` wins exactly when all `n − 1`
rivals draw below `t`, an event of IID probability `F(t) ^ (n-1)`. The lex tie-break is immaterial
because the shared law is atomless, so the strict/weak boundary `{θⱼ = t}` is null. This is the top
order-statistic distribution behind revenue equivalence in the symmetric IPV model. -/
theorem highestAlloc_interimAlloc_eq_cdf_pow (hv : Measurable v) (hsmono : StrictMono v)
    (i : Fin A.n) {t : ℝ} (hvt : 0 ≤ v t) :
    (A.highestAlloc v hv).interimAlloc i t = (A.base.dist.cdf t) ^ (A.n - 1) := by
  set d := A.base.dist with hd
  haveI : IsProbabilityMeasure d.toMeasure := d.toMeasure_isProbability
  haveI : NoAtoms d.toMeasure := d.toMeasure_eq ▸ noAtoms_withDensity _
  set W : Set A.Profile := {θ | A.IsTopBidder v (update θ i t) i} with hW
  -- The set S is the coordinate box: unconstrained at coordinate i; strict below t for lower
  -- indices (lex tie-break) and weak below t for higher indices.
  set S : Fin A.n → Set ℝ :=
    fun j => if j = i then univ else if j < i then Iio t else Iic t with hS
  have hWmeas : MeasurableSet W :=
    (A.measurableSet_isTopBidder v hv i).preimage measurable_update_left
  have hpt : ∀ θ, (A.highestAlloc v hv).x (update θ i t) i = W.indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    by_cases h : θ ∈ W
    · rw [highestAlloc_x_of_top hv h, Set.indicator_of_mem h]
    · rw [highestAlloc_x_of_not_top hv h, Set.indicator_of_notMem h]
  have hWS : W = Set.univ.pi S := by
    ext θ
    rw [Set.mem_univ_pi]
    constructor
    · rintro hθW j
      obtain ⟨_, hmax, hlt⟩ := hθW
      simp only [update_self] at hmax hlt
      simp only [hS]
      split_ifs with hji hjlt
      · exact Set.mem_univ _
      · have hv_lt := hlt j hjlt
        rw [update_of_ne (ne_of_lt hjlt)] at hv_lt
        exact Set.mem_Iio.mpr (hsmono.lt_iff_lt.mp hv_lt)
      · have hv_le := hmax j
        rw [update_of_ne hji] at hv_le
        exact Set.mem_Iic.mpr (hsmono.le_iff_le.mp hv_le)
    · intro hθ
      refine ⟨by rw [update_self]; exact hvt, fun j => ?_, fun j hji => ?_⟩
      · rw [update_self]
        by_cases hj : j = i
        · subst hj; rw [update_self]
        · rw [update_of_ne hj]
          have hsj := hθ j
          simp only [hS, if_neg hj] at hsj
          split_ifs at hsj with hjlt
          · exact le_of_lt (hsmono (Set.mem_Iio.mp hsj))
          · exact hsmono.le_iff_le.mpr (Set.mem_Iic.mp hsj)
      · rw [update_self]
        have hjne : j ≠ i := ne_of_lt hji
        rw [update_of_ne hjne]
        have hsj := hθ j
        simp only [hS, if_neg hjne, if_pos hji] at hsj
        exact hsmono (Set.mem_Iio.mp hsj)
  have hprod : (∏ j, d.toMeasure (S j)) = d.toMeasure (Iic t) ^ (A.n - 1) := by
    have hm : ∀ j ∈ Finset.univ.erase i, d.toMeasure (S j) = d.toMeasure (Iic t) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [hS, if_neg hji]
      split_ifs with hjlt
      · exact measure_congr Iio_ae_eq_Iic
      · rfl
    have hfi : d.toMeasure (S i) = 1 := by simp only [hS, if_pos rfl]; exact measure_univ
    calc ∏ j, d.toMeasure (S j)
        = d.toMeasure (S i) * ∏ j ∈ Finset.univ.erase i, d.toMeasure (S j) :=
          (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      _ = 1 * ∏ _j ∈ Finset.univ.erase i, d.toMeasure (Iic t) := by
          rw [hfi, Finset.prod_congr rfl hm]
      _ = d.toMeasure (Iic t) ^ (A.n - 1) := by
          rw [one_mul, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin]
  rw [ExPostAlloc.interimAlloc_def, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_indicator_const (1 : ℝ) hWmeas, smul_eq_mul, mul_one, measureReal_def, hWS]
  rw [show A.jointLaw = Measure.pi (fun _ : Fin A.n => d.toMeasure) from rfl, Measure.pi_pi, hprod,
    ENNReal.toReal_pow, d.toReal_measure_Iic_eq_cdf]

variable (A v)

/-- The **highest-value allocation with no withholding**: The unit always goes to the highest-value
bidder (least-index tie-break). Implemented as `highestAlloc` with the strictly monotone positive
score `Real.exp`: Positivity means the unit is never withheld (no reserve), and strict monotonicity
means the winner is the value-maximizer. This is the allocation shared by the standard auction
formats — first-price, second-price, all-pay — which differ only in their payment rules. -/
def highestValueAlloc : ExPostAlloc A := A.highestAlloc Real.exp Real.measurable_exp

/-- **Order-statistic reduced form, no sign condition.** Because the score `exp` is positive
everywhere, the highest-value allocation's interim winning probability is `F(t)^{n-1}` at every
type `t`. -/
@[simp] lemma highestValueAlloc_interimAlloc (i : Fin A.n) (t : ℝ) :
    A.highestValueAlloc.interimAlloc i t = (A.base.dist.cdf t) ^ (A.n - 1) :=
  AuctionEnv.highestAlloc_interimAlloc_eq_cdf_pow (A := A) Real.measurable_exp
    Real.exp_strictMono i (Real.exp_pos t).le

/-- Each bidder's reduced highest-value allocation is monotone (the score `exp` is monotone), so it
is implementable by Myerson's lemma. -/
lemma highestValueAlloc_reducedAlloc_monotone (i : Fin A.n) :
    MonotoneAlloc (A.highestValueAlloc.reducedAlloc i) :=
  A.highestAlloc_interimAlloc_monotoneOn Real.measurable_exp
    (Real.exp_monotone.monotoneOn _) i

variable {A}

/-- The top bidder receives the whole unit (highest-value specialization). -/
lemma highestValueAlloc_x_of_top {θ : A.Profile} {i : Fin A.n}
    (h : A.IsTopBidder Real.exp θ i) : A.highestValueAlloc.x θ i = 1 :=
  highestAlloc_x_of_top Real.measurable_exp h

/-- A non-top bidder receives nothing (highest-value specialization). -/
lemma highestValueAlloc_x_of_not_top {θ : A.Profile} {i : Fin A.n}
    (h : ¬ A.IsTopBidder Real.exp θ i) : A.highestValueAlloc.x θ i = 0 :=
  highestAlloc_x_of_not_top Real.measurable_exp h

variable (A)

/-- The **optimal ex-post allocation**: Award the unit to the highest virtual value `ψ` (if
nonnegative). -/
def optimalAlloc : ExPostAlloc A :=
  A.highestAlloc A.base.virtualValue A.base.virtualValue_measurable

/-- The **ironed optimal ex-post allocation**: Award the unit to the highest **ironed virtual
value** `ψ̄` (if nonnegative). Implementable for every environment, since `ψ̄` is always
monotone. -/
def ironedAlloc : ExPostAlloc A :=
  A.highestAlloc A.base.ironedVirtualValue A.base.ironedVirtualValue_measurable

end AuctionEnv

namespace ExPostAlloc

variable {A : AuctionEnv} (X : ExPostAlloc A)

/-- The reduced allocation's Myerson payment is measurable in the own report. -/
lemma reducedAlloc_myersonPayment_measurable (i : Fin A.n) :
    Measurable (X.reducedAlloc i).myersonPayment := by
  have hx : Measurable (X.interimAlloc i) := X.interimAlloc_measurable i
  have hprim : Continuous (fun t => ∫ s in A.base.θlo..t, X.interimAlloc i s) :=
    intervalIntegral.continuous_primitive
      (fun a b => X.intervalIntegrable_interimAlloc i a b) A.base.θlo
  unfold AllocationRule.myersonPayment
  simp only [ExPostAlloc.reducedAlloc_x]
  exact (measurable_id.mul hx).sub hprim.measurable

/-- The **Myerson auction mechanism** of an ex-post allocation `X`: Pair `X` with the per-bidder
Myerson payment of its reduced form. The ex-post payment depends on a bidder's report only through
its own type, so its interim form is exactly the reduced allocation's Myerson payment. Generic in
`X`, so the highest-`ψ` (regular) and highest-`ψ̄` (ironed) optimal auctions share this plumbing. -/
def myersonMechanism : AuctionMechanism A where
  alloc := X
  pay θ i := (X.reducedAlloc i).myersonPayment (θ i)
  pay_measurable i :=
    (X.reducedAlloc_myersonPayment_measurable i).comp (measurable_pi_apply i)
  pay_integrable i := by
    set g := (X.reducedAlloc i).myersonPayment with hg_def
    have hg_meas : Measurable g := X.reducedAlloc_myersonPayment_measurable i
    set C := max |A.base.θlo| |A.base.θhi| + (A.base.θhi - A.base.θlo) with hC_def
    have hg_bound : ∀ t ∈ Icc A.base.θlo A.base.θhi, |g t| ≤ C := by
      intro t ht
      rw [hg_def]
      simp only [AllocationRule.myersonPayment, ExPostAlloc.reducedAlloc_x]
      have ht_abs : |t| ≤ max |A.base.θlo| |A.base.θhi| := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · calc -(max |A.base.θlo| |A.base.θhi|) ≤ -|A.base.θlo| :=
                neg_le_neg (le_max_left _ _)
            _ ≤ A.base.θlo := neg_abs_le _
            _ ≤ t := ht.1
        · calc t ≤ A.base.θhi := ht.2
            _ ≤ |A.base.θhi| := le_abs_self _
            _ ≤ _ := le_max_right _ _
      have hxabs : |X.interimAlloc i t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [X.interimAlloc_nonneg i t], X.interimAlloc_le_one i t⟩
      have hint_abs : |∫ s in A.base.θlo..t, X.interimAlloc i s|
          ≤ A.base.θhi - A.base.θlo := by
        have hle := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := A.base.θlo) (b := t) (C := 1) (f := X.interimAlloc i)
          (fun s _ => by
            rw [Real.norm_eq_abs]
            exact (abs_le.mpr ⟨by linarith [X.interimAlloc_nonneg i s],
              X.interimAlloc_le_one i s⟩))
        rw [Real.norm_eq_abs] at hle
        calc |∫ s in A.base.θlo..t, X.interimAlloc i s|
            ≤ 1 * |t - A.base.θlo| := hle
          _ = |t - A.base.θlo| := one_mul _
          _ ≤ A.base.θhi - A.base.θlo := by
              rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
      calc |t * X.interimAlloc i t - ∫ s in A.base.θlo..t, X.interimAlloc i s|
          ≤ |t * X.interimAlloc i t| + |∫ s in A.base.θlo..t, X.interimAlloc i s| := abs_sub _ _
        _ ≤ max |A.base.θlo| |A.base.θhi| + (A.base.θhi - A.base.θlo) := by
              rw [abs_mul]
              exact add_le_add
                (le_trans (mul_le_of_le_one_right (abs_nonneg _) hxabs) ht_abs) hint_abs
    exact A.integrable_comp_eval hg_meas hg_bound i
  pay_measurable_update i t := by
    -- The Myerson payment depends on a bidder's report only through its own type, so splicing the
    -- report `t` into coordinate `i` makes the integrand the constant `myersonPayment t`.
    have heq : (fun θ : A.Profile => (X.reducedAlloc i).myersonPayment ((update θ i t) i))
        = fun _ : A.Profile => (X.reducedAlloc i).myersonPayment t := by
      funext θ; rw [update_self]
    rw [heq]; exact measurable_const
  pay_integrable_update i t := by
    -- The spliced integrand is the constant `myersonPayment t`, integrable against the probability
    -- measure `jointLaw`.
    have heq : (fun θ : A.Profile => (X.reducedAlloc i).myersonPayment ((update θ i t) i))
        = fun _ : A.Profile => (X.reducedAlloc i).myersonPayment t := by
      funext θ; rw [update_self]
    rw [heq]; exact integrable_const _

@[simp] lemma myersonMechanism_alloc : X.myersonMechanism.alloc = X := rfl

@[simp] lemma myersonMechanism_pay (θ : A.Profile) (i : Fin A.n) :
    X.myersonMechanism.pay θ i = (X.reducedAlloc i).myersonPayment (θ i) := rfl

/-- The interim payment is the reduced allocation's Myerson payment (the ex-post payment is
constant in the rivals' reports). -/
lemma myersonMechanism_interimPay (i : Fin A.n) :
    X.myersonMechanism.interimPay i = (X.reducedAlloc i).myersonPayment := by
  funext t
  rw [AuctionMechanism.interimPay_def]
  simp only [myersonMechanism_pay, Function.update_self]
  rw [integral_const]; simp

/-- The reduced mechanism is exactly the Myerson mechanism of the reduced allocation. -/
lemma myersonMechanism_reducedMechanism (i : Fin A.n) :
    X.myersonMechanism.reducedMechanism i = (X.reducedAlloc i).myersonMechanism := by
  rw [AuctionMechanism.reducedMechanism, myersonMechanism_interimPay]; rfl

/-- If every reduced allocation is monotone, the mechanism is incentive compatible. -/
lemma myersonMechanism_isBIC (hmono : ∀ i, MonotoneAlloc (X.reducedAlloc i)) :
    X.myersonMechanism.IsBIC := by
  intro i
  rw [myersonMechanism_reducedMechanism]
  exact (X.reducedAlloc i).monotone_implies_isBIC (hmono i)

/-- Every reduced mechanism has no rent at the lowest type. -/
lemma myersonMechanism_interimUtil_zero (i : Fin A.n) :
    (X.myersonMechanism.reducedMechanism i).interimUtil A.base.θlo = 0 := by
  rw [myersonMechanism_reducedMechanism, AllocationRule.interimUtil_myersonMechanism,
    intervalIntegral.integral_same]

/-- The Myerson auction mechanism is individually rational: Every reduced mechanism is IR (its
on-path interim utility is the integral of a nonnegative allocation). The constructed optimal
auctions therefore lie in the admissible BIC ∧ BIR class against which the revenue bound is
proved. -/
lemma myersonMechanism_BIR : X.myersonMechanism.IsBIR := by
  intro i
  rw [myersonMechanism_reducedMechanism]
  exact (X.reducedAlloc i).myersonMechanism_isBIR

/-- **Revenue of the Myerson auction mechanism.** Under monotone reduced allocations, expected
revenue equals the total expected raw virtual surplus `∑ᵢ 𝔼[ψ·x̄ᵢ]` (the revenue identity). -/
lemma myersonMechanism_revenue (hmono : ∀ i, MonotoneAlloc (X.reducedAlloc i)) :
    (∫ θ, ∑ i, X.myersonMechanism.pay θ i ∂A.jointLaw)
      = ∑ i, A.base.dist.expect (fun t => A.base.virtualValue t * X.interimAlloc i t) :=
  X.myersonMechanism.expected_revenue_eq_virtual_surplus
    (X.myersonMechanism_isBIC hmono) (X.myersonMechanism_interimUtil_zero)

/-- The total raw virtual surplus rewritten as a single integral of the pointwise surplus. -/
lemma sum_expect_virtualSurplus_eq :
    ∑ i, A.base.dist.expect (fun t => A.base.virtualValue t * X.interimAlloc i t)
      = ∫ θ, ∑ i, A.base.virtualValue (θ i) * X.x θ i ∂A.jointLaw := by
  have hint : ∀ i, Integrable
      (fun θ => A.base.virtualValue (θ i) * X.x θ i) A.jointLaw :=
    fun i => X.integrable_virtualSurplus i
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl fun i _ => X.expected_virtualSurplus_eq i

/-- The total *ironed* virtual surplus rewritten as a single integral of the pointwise ironed
surplus. -/
lemma sum_expect_ironedVirtualSurplus_eq :
    ∑ i, A.base.dist.expect (fun t => A.base.ironedVirtualValue t * X.interimAlloc i t)
      = ∫ θ, ∑ i, A.base.ironedVirtualValue (θ i) * X.x θ i ∂A.jointLaw := by
  have hint : ∀ i, Integrable
      (fun θ => A.base.ironedVirtualValue (θ i) * X.x θ i) A.jointLaw :=
    fun i => X.integrable_ironedVirtualSurplus i
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl fun i _ => X.expected_ironedVirtualSurplus_eq i

end ExPostAlloc

namespace AuctionEnv

variable (A : AuctionEnv)

/-- **Achievability of the optimal-auction bound (regular case)** (Myerson 1981). Under regularity
there exists an incentive-compatible, individually rational auction (with no rent at the lowest
type) whose expected revenue equals the optimal virtual surplus bound `∫ max(0, maxᵢ ψ(θᵢ))`. Since
this mechanism is BIC ∧ BIR and `revenue_le_optimalVirtualSurplus` bounds every BIC ∧ BIR auction
by the same integral, the two together determine the optimal revenue exactly over the full
admissible class. -/
theorem exists_optimal_auction_regular (hreg : A.base.Regular) :
    ∃ M : AuctionMechanism A, M.IsBIC ∧ M.IsBIR ∧
      (∀ i, (M.reducedMechanism i).interimUtil A.base.θlo = 0) ∧
      (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw) = ∫ θ, A.optimalVirtualSurplus θ ∂A.jointLaw := by
  have hmono : ∀ i, MonotoneAlloc (A.optimalAlloc.reducedAlloc i) :=
    fun i => A.highestAlloc_interimAlloc_monotoneOn A.base.virtualValue_measurable hreg i
  refine ⟨A.optimalAlloc.myersonMechanism, A.optimalAlloc.myersonMechanism_isBIC hmono,
    A.optimalAlloc.myersonMechanism_BIR,
    A.optimalAlloc.myersonMechanism_interimUtil_zero, ?_⟩
  rw [A.optimalAlloc.myersonMechanism_revenue hmono,
    A.optimalAlloc.sum_expect_virtualSurplus_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact A.highestAlloc_virtualSurplus_eq A.base.virtualValue_measurable θ

/-- **Complementary slackness — the ironing equality.** For the highest-ironed-value allocation,
the raw and ironed expected virtual surpluses coincide per bidder. The interim allocation is flat
on level sets of `ψ̄` (since bidder `i`'s winner status depends on its type only through `ψ̄(θᵢ)`),
which is the contact-set condition that closes the ironing gap. -/
lemma expected_rawSurplus_eq_ironedSurplus_ironedAlloc (i : Fin A.n) :
    A.base.dist.expect (fun t => A.base.virtualValue t * A.ironedAlloc.interimAlloc i t)
      = A.base.dist.expect
        (fun t => A.base.ironedVirtualValue t * A.ironedAlloc.interimAlloc i t) := by
  set M : DirectMechanism A.base :=
    ⟨A.ironedAlloc.reducedAlloc i, fun _ => 0⟩ with hM_def
  have hmono : MonotoneAlloc M.alloc :=
    A.highestAlloc_interimAlloc_monotoneOn A.base.ironedVirtualValue_measurable
      A.base.ironedVirtualValue_monotone i
  have hflat : ∀ {t t' : ℝ},
      A.base.ironedVirtualValue t = A.base.ironedVirtualValue t' → M.x t = M.x t' := by
    intro t t' h
    simpa [M] using A.highestAlloc_interimAlloc_congr A.base.ironedVirtualValue_measurable i h
  exact A.base.expected_virtualSurplus_eq_ironed M hmono hflat

/-- **Achievability of the ironed optimal-auction bound (general case)** (Myerson 1981). Without
any regularity assumption, there exists an incentive-compatible, individually rational auction
(with no rent at the lowest type) whose expected revenue equals the ironed optimal virtual surplus
bound `∫ max(0, maxᵢ ψ̄(θᵢ))`. Since this mechanism is BIC ∧ BIR and
`revenue_le_ironedOptimalVirtualSurplus` bounds every BIC ∧ BIR auction by the same integral, the
two together determine the optimal revenue exactly over the full admissible class, even for
irregular environments. -/
theorem exists_optimal_auction_ironed :
    ∃ M : AuctionMechanism A, M.IsBIC ∧ M.IsBIR ∧
      (∀ i, (M.reducedMechanism i).interimUtil A.base.θlo = 0) ∧
      (∫ θ, ∑ i, M.pay θ i ∂A.jointLaw)
        = ∫ θ, A.ironedOptimalVirtualSurplus θ ∂A.jointLaw := by
  have hmono : ∀ i, MonotoneAlloc (A.ironedAlloc.reducedAlloc i) :=
    fun i => A.highestAlloc_interimAlloc_monotoneOn A.base.ironedVirtualValue_measurable
      A.base.ironedVirtualValue_monotone i
  refine ⟨A.ironedAlloc.myersonMechanism, A.ironedAlloc.myersonMechanism_isBIC hmono,
    A.ironedAlloc.myersonMechanism_BIR,
    A.ironedAlloc.myersonMechanism_interimUtil_zero, ?_⟩
  rw [A.ironedAlloc.myersonMechanism_revenue hmono,
    Finset.sum_congr rfl (fun i _ => A.expected_rawSurplus_eq_ironedSurplus_ironedAlloc i),
    A.ironedAlloc.sum_expect_ironedVirtualSurplus_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact A.highestAlloc_virtualSurplus_eq A.base.ironedVirtualValue_measurable θ

end AuctionEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
