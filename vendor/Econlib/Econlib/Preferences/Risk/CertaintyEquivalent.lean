/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Risk.Basic
public import Econlib.Probability.FinDist.Basic
public import Econlib.Probability.FinDist.Expect
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# Certainty equivalents and risk premia

This file contains finite-lottery certainty equivalents and risk-premium lemmas.

Lotteries are bundled as `FinLottery n`: A vector of money `outcome`s paired with a `FinDist`
probability distribution. Because the probabilities live in `FinDist (Fin n)`, which bundles
nonnegativity and total mass one, invalid weights (negative, or not summing to one) are
inexpressible. Thus none of the certainty-equivalent or risk-premium lemmas below needs a separate
distribution hypothesis.

## Main definitions

* `FinLottery` — a finite money lottery: Outcomes `Fin n → ℝ` paired with a `FinDist (Fin n)`.
* `FinLottery.expectedValue` — the mean monetary value `∑ᵢ pᵢ·xᵢ` of a lottery, reusing the
  finite-distribution expectation `FinDist.expect`.
* `IsCertaintyEquivalent` — `c` is the certainty equivalent of a `FinLottery` under utility `u`.
* `riskPremium` — the expected value of a `FinLottery` minus its certainty equivalent.

## Main statements

* `certainty_equivalent_exists` / `certainty_equivalent_unique` — existence and uniqueness of the
  certainty equivalent.
* `certainty_equivalent_le_expected_value_of_concave` and its strict and affine variants — the
  Jensen ordering of the certainty equivalent against the expected value.
* `risk_premium_nonneg_of_concave` / `risk_premium_pos_of_strict_concave` — sign of the risk
  premium for (strictly) concave utility.
* The `RiskAverse.*`, `RiskLoving.*`, `RiskNeutral.*`, `StrictlyRiskAverse.*` bridges — the lottery
  content of the named risk-attitude predicates.

## References

* Pratt, John W. 1964. “Risk Aversion in the Small and in the Large.” *Econometrica* 32 (1/2): 122.
  [https://doi.org/10.2307/1913738](https://doi.org/10.2307/1913738).

## Tags

certainty equivalent, risk premium, Jensen's inequality, risk aversion, finite lottery
-/

@[expose] public section

open Set Filter Topology

namespace Econlib.Preferences

open Econlib.Probability

/-- A finite money lottery over `Fin n`: A vector of monetary `outcome`s paired with a valid
probability distribution `prob`. -/
structure FinLottery (n : ℕ) where
  /-- The monetary outcome attached to each state. -/
  outcome : Fin n → ℝ
  /-- The probability distribution over the states. -/
  prob : FinDist (Fin n)

/-- The expected (mean) monetary value of a lottery, `𝔼[X] = ∑ᵢ pᵢ·xᵢ`: The finite-distribution
expectation `FinDist.expect` of the outcome vector under the lottery's probabilities. -/
noncomputable def FinLottery.expectedValue {n : ℕ} (L : FinLottery n) : ℝ :=
  L.prob.expect L.outcome

/-- The expected value as the explicit `pmf`-weighted sum of outcomes. This is the
`Fin.sum_univ_*`/`norm_num`-friendly evaluation form. -/
@[simp] lemma FinLottery.expectedValue_eq_sum {n : ℕ} (L : FinLottery n) :
    L.expectedValue = ∑ i, L.prob.pmf i * L.outcome i := rfl

/-- `IsCertaintyEquivalent u L c` asserts that `c` is the certainty equivalent of the lottery `L`
under utility function `u`: The utility of `c` for sure equals the lottery's expected utility. -/
def IsCertaintyEquivalent {n : ℕ} (u : ℝ → ℝ) (L : FinLottery n) (c : ℝ) : Prop :=
  u c = ∑ i : Fin n, L.prob.pmf i * u (L.outcome i)

/-- Under a strictly monotone utility, the certainty equivalent of a lottery is unique. -/
lemma certainty_equivalent_unique {n : ℕ} {s : Set ℝ} {u : ℝ → ℝ} {L : FinLottery n} {c₁ c₂ : ℝ}
    (hu : StrictMonoOn u s)
    (hc1s : c₁ ∈ s) (hc2s : c₂ ∈ s)
    (hc1 : IsCertaintyEquivalent u L c₁)
    (hc2 : IsCertaintyEquivalent u L c₂) :
    c₁ = c₂ :=
  hu.injOn hc1s hc2s (hc1.trans hc2.symm)

/-- For any continuous utility function, a certainty equivalent exists for every finite lottery.
The proof applies the intermediate value theorem: The expected utility lies between the minimum and
maximum utility over the outcomes. -/
lemma certainty_equivalent_exists {n : ℕ} {u : ℝ → ℝ} {L : FinLottery n}
    (hu_cont : Continuous u) :
    ∃ c, IsCertaintyEquivalent u L c := by
  by_cases hn : n = 0
  · subst hn
    simpa using L.prob.sum_one
  · have h_univ : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn))
    let Sx := Finset.univ.image (fun i => L.outcome i)
    let x_min := Finset.min' Sx (Finset.image_nonempty.mpr h_univ)
    let x_max := Finset.max' Sx (Finset.image_nonempty.mpr h_univ)
    have h_min : ∀ i, x_min ≤ L.outcome i :=
      fun i => Finset.min'_le Sx _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h_max : ∀ i, L.outcome i ≤ x_max :=
      fun i => Finset.le_max' Sx _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    let Su := Finset.univ.image (fun i => u (L.outcome i))
    let u_min := Finset.min' Su (Finset.image_nonempty.mpr h_univ)
    let u_max := Finset.max' Su (Finset.image_nonempty.mpr h_univ)
    have hu_min : ∀ i, u_min ≤ u (L.outcome i) :=
      fun i => Finset.min'_le Su _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hu_max : ∀ i, u (L.outcome i) ≤ u_max :=
      fun i => Finset.le_max' Su _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    let Eu := ∑ i, L.prob.pmf i * u (L.outcome i)
    have h_Eu_ge : u_min ≤ Eu :=
      calc u_min = ∑ i, L.prob.pmf i * u_min := by
            rw [← Finset.sum_mul, L.prob.sum_one, one_mul]
        _ ≤ Eu := Finset.sum_le_sum
            fun i _ => mul_le_mul_of_nonneg_left (hu_min i) (L.prob.nonneg i)
    have h_Eu_le : Eu ≤ u_max :=
      calc Eu ≤ ∑ i, L.prob.pmf i * u_max :=
            Finset.sum_le_sum
              fun i _ => mul_le_mul_of_nonneg_left (hu_max i) (L.prob.nonneg i)
        _ = u_max := by rw [← Finset.sum_mul, L.prob.sum_one, one_mul]
    have hab : x_min ≤ x_max :=
      le_trans (h_min ⟨0, Nat.pos_of_ne_zero hn⟩) (h_max ⟨0, Nat.pos_of_ne_zero hn⟩)
    have h_conn : IsConnected (Set.Icc x_min x_max) := isConnected_Icc hab
    have h_img_conn : IsConnected (u '' Set.Icc x_min x_max) := h_conn.image u hu_cont.continuousOn
    have h_conv : Convex ℝ (u '' Set.Icc x_min x_max) := h_img_conn.isPreconnected.convex
    rcases Finset.mem_image.mp (Finset.min'_mem Su (Finset.image_nonempty.mpr h_univ)) with
      ⟨j, _, hj_eq⟩
    rcases Finset.mem_image.mp (Finset.max'_mem Su (Finset.image_nonempty.mpr h_univ)) with
      ⟨k, _, hk_eq⟩
    have h_uj_in : u (L.outcome j) ∈ u '' Set.Icc x_min x_max :=
      Set.mem_image_of_mem u ⟨h_min j, h_max j⟩
    have h_uk_in : u (L.outcome k) ∈ u '' Set.Icc x_min x_max :=
      Set.mem_image_of_mem u ⟨h_min k, h_max k⟩
    simp only [u_min] at h_Eu_ge
    simp only [u_max] at h_Eu_le
    have h_Eu_ge' : u (L.outcome j) ≤ Eu := hj_eq ▸ h_Eu_ge
    have h_Eu_le' : Eu ≤ u (L.outcome k) := hk_eq ▸ h_Eu_le
    obtain ⟨c, _, hc⟩ := h_conv.ordConnected.out h_uj_in h_uk_in ⟨h_Eu_ge', h_Eu_le'⟩
    exact ⟨c, hc⟩

/-- For a concave utility with strictly monotone restriction to `s`, the certainty equivalent of a
lottery with outcomes in `s` lies at or below the expected value. This is Jensen's inequality
stated in terms of the certainty equivalent. -/
lemma certainty_equivalent_le_expected_value_of_concave {n : ℕ} {s : Set ℝ} {u : ℝ → ℝ}
    {L : FinLottery n} {c : ℝ}
    (hu_mono : StrictMonoOn u s)
    (hu_concave : ConcaveOn ℝ s u)
    (hxs : ∀ i, L.outcome i ∈ s)
    (hcs : c ∈ s)
    (hc : IsCertaintyEquivalent u L c) :
    c ≤ L.expectedValue := by
  have hmean : (∑ i, L.prob.pmf i * L.outcome i) ∈ s := by
    simpa only [smul_eq_mul] using
      hu_concave.1.sum_mem (fun i _ => L.prob.nonneg i) L.prob.sum_one (fun i _ => hxs i)
  have h_jensen :
      ∑ i, L.prob.pmf i * u (L.outcome i) ≤ u (∑ i, L.prob.pmf i * L.outcome i) := by
    have h_smul : ∑ i, L.prob.pmf i • u (L.outcome i) ≤ u (∑ i, L.prob.pmf i • L.outcome i) :=
      hu_concave.le_map_sum
        (fun i _ => L.prob.nonneg i) L.prob.sum_one (fun i _ => hxs i)
    simpa only [smul_eq_mul] using h_smul
  have h_u_le : u c ≤ u (∑ i, L.prob.pmf i * L.outcome i) := hc ▸ h_jensen
  exact (hu_mono.le_iff_le hcs hmean).mp h_u_le

/-- For an affine utility `u z = a * z + b` with `a ≠ 0`, the certainty equivalent equals the
expected value of the lottery. -/
lemma certainty_equivalent_eq_expected_value_of_affine {n : ℕ} {u : ℝ → ℝ} {L : FinLottery n}
    {c : ℝ}
    (haffine : ∃ a b, a ≠ 0 ∧ ∀ z, u z = a * z + b)
    (hc : IsCertaintyEquivalent u L c) :
    c = L.expectedValue := by
  rcases haffine with ⟨a, b, h_ane, hab⟩
  have sum_eq :
      (∑ i, L.prob.pmf i * u (L.outcome i)) = a * (∑ i, L.prob.pmf i * L.outcome i) + b := by
    simp only [hab, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, L.prob.sum_one, one_mul,
      mul_left_comm a, Finset.mul_sum]
  have h_eq : a * c + b = a * (∑ i, L.prob.pmf i * L.outcome i) + b := by rw [← hab c, hc, sum_eq]
  exact (mul_right_inj' h_ane).mp (add_right_cancel h_eq)

/-- **Strict Jensen gap.** For a strictly concave utility and a non-degenerate lottery — two
outcomes with positive probability and distinct values — the certainty equivalent falls strictly
below the expected value. This is the strict companion of
`certainty_equivalent_le_expected_value_of_concave`; degenerate lotteries (all probability on one
value) are excluded because there the certainty equivalent equals the sure outcome. -/
lemma certainty_equivalent_lt_expected_value_of_strict_concave {n : ℕ} {s : Set ℝ} {u : ℝ → ℝ}
    {L : FinLottery n} {c : ℝ}
    (hu_mono : StrictMonoOn u s)
    (hu_concave : StrictConcaveOn ℝ s u)
    (hxs : ∀ i, L.outcome i ∈ s)
    (hcs : c ∈ s)
    (hnondeg : ∃ i j, 0 < L.prob.pmf i ∧ 0 < L.prob.pmf j ∧ L.outcome i ≠ L.outcome j)
    (hc : IsCertaintyEquivalent u L c) :
    c < L.expectedValue := by
  classical
  obtain ⟨i, j, hpi, hpj, hxij⟩ := hnondeg
  have hmean : (∑ k, L.prob.pmf k * L.outcome k) ∈ s := by
    simpa only [smul_eq_mul] using
      hu_concave.1.sum_mem (fun k _ => L.prob.nonneg k) L.prob.sum_one (fun k _ => hxs k)
  -- Restrict to the strict support so strict Jensen applies: off-support weights are zero.
  set t : Finset (Fin n) := {k | 0 < L.prob.pmf k} with ht
  have hmem_t : ∀ {k}, k ∈ t ↔ 0 < L.prob.pmf k := by simp [ht]
  have h_off_support : ∀ k ∈ Finset.univ, k ∉ t → L.prob.pmf k = 0 :=
    fun k _ hk => le_antisymm (not_lt.mp (hmem_t.not.mp hk)) (L.prob.nonneg k)
  have hsum_t : ∑ k ∈ t, L.prob.pmf k = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ t) h_off_support]
    exact L.prob.sum_one
  have h_jensen_t :
      ∑ k ∈ t, L.prob.pmf k • u (L.outcome k) < u (∑ k ∈ t, L.prob.pmf k • L.outcome k) :=
    hu_concave.lt_map_sum (fun k hk => hmem_t.mp hk) hsum_t
      (fun k _ => hxs k)
      ⟨i, hmem_t.mpr hpi, j, hmem_t.mpr hpj, hxij⟩
  have h_Eu_t : ∑ k ∈ t, L.prob.pmf k * u (L.outcome k) = ∑ k, L.prob.pmf k * u (L.outcome k) :=
    Finset.sum_subset (Finset.subset_univ t)
      (fun k hk hkt => by rw [h_off_support k hk hkt, zero_mul])
  have h_Ex_t : ∑ k ∈ t, L.prob.pmf k * L.outcome k = ∑ k, L.prob.pmf k * L.outcome k :=
    Finset.sum_subset (Finset.subset_univ t)
      (fun k hk hkt => by rw [h_off_support k hk hkt, zero_mul])
  have h_u_lt : u c < u (∑ k, L.prob.pmf k * L.outcome k) := by
    calc u c = ∑ k ∈ t, L.prob.pmf k * u (L.outcome k) := by rw [hc, h_Eu_t]
      _ < u (∑ k ∈ t, L.prob.pmf k * L.outcome k) := by simpa only [smul_eq_mul] using h_jensen_t
      _ = u (∑ k, L.prob.pmf k * L.outcome k) := by rw [h_Ex_t]
  exact (hu_mono.lt_iff_lt hcs hmean).mp h_u_lt

/-- The risk premium of a lottery is the difference between the expected value and the certainty
equivalent: `RP = 𝔼[X] - certainty equivalent`. For a risk-averse agent, `RP ≥ 0`. -/
noncomputable def riskPremium {n : ℕ} (L : FinLottery n) (c : ℝ) : ℝ :=
  L.expectedValue - c

/-- For a concave utility, the risk premium of any lottery is nonnegative. -/
lemma risk_premium_nonneg_of_concave {n : ℕ} {s : Set ℝ} {u : ℝ → ℝ} {L : FinLottery n}
    {c : ℝ}
    (hu_mono : StrictMonoOn u s)
    (hu_concave : ConcaveOn ℝ s u)
    (hxs : ∀ i, L.outcome i ∈ s)
    (hcs : c ∈ s)
    (hc : IsCertaintyEquivalent u L c) :
    0 ≤ riskPremium L c :=
  sub_nonneg.mpr (certainty_equivalent_le_expected_value_of_concave hu_mono hu_concave hxs hcs hc)

/-- For a strictly concave utility facing a non-degenerate lottery, the risk premium is strictly
positive: The agent strictly prefers the expected value for sure over the gamble, so shedding the
risk commands a positive price. Strict companion of `risk_premium_nonneg_of_concave`. -/
lemma risk_premium_pos_of_strict_concave {n : ℕ} {s : Set ℝ} {u : ℝ → ℝ} {L : FinLottery n}
    {c : ℝ}
    (hu_mono : StrictMonoOn u s)
    (hu_concave : StrictConcaveOn ℝ s u)
    (hxs : ∀ i, L.outcome i ∈ s)
    (hcs : c ∈ s)
    (hnondeg : ∃ i j, 0 < L.prob.pmf i ∧ 0 < L.prob.pmf j ∧ L.outcome i ≠ L.outcome j)
    (hc : IsCertaintyEquivalent u L c) :
    0 < riskPremium L c :=
  sub_pos.mpr
    (certainty_equivalent_lt_expected_value_of_strict_concave hu_mono hu_concave hxs hcs hnondeg hc)

/-! ## Risk-attitude predicates as lottery preferences

These bridges connect the named risk-attitude predicates of `Econlib.Preferences.Risk.Basic` to
their defining behavior over finite lotteries: A risk-averse agent prefers the sure expected value
to the gamble, a risk-loving agent prefers the gamble, and a risk-neutral agent is indifferent.
They are the formal content of those predicates' docstrings. -/

/-- A risk-averse agent values a lottery `L` with outcomes in its domain `S` at most as much as
receiving the expected value `∑ pᵢ·xᵢ` for sure: `∑ pᵢ·u(xᵢ) ≤ u(∑ pᵢ·xᵢ)`. This is Jensen's
inequality for the concave utility. -/
theorem RiskAverse.le_map_sum {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ} (h : RiskAverse u S)
    {L : FinLottery n} (hxS : ∀ i, L.outcome i ∈ S) :
    ∑ i, L.prob.pmf i * u (L.outcome i) ≤ u (∑ i, L.prob.pmf i * L.outcome i) := by
  have h_smul : ∑ i, L.prob.pmf i • u (L.outcome i) ≤ u (∑ i, L.prob.pmf i • L.outcome i) :=
    ConcaveOn.le_map_sum h (fun i _ => L.prob.nonneg i) L.prob.sum_one (fun i _ => hxS i)
  simpa only [smul_eq_mul] using h_smul

/-- For a risk-averse agent with strictly increasing utility, the certainty equivalent of any
lottery (outcomes in `S`) lies at or below its expected value. -/
theorem RiskAverse.certainty_equivalent_le_expected_value {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ}
    (h : RiskAverse u S) (hu_mono : StrictMonoOn u S) {L : FinLottery n} {c : ℝ}
    (hxS : ∀ i, L.outcome i ∈ S) (hcS : c ∈ S) (hc : IsCertaintyEquivalent u L c) :
    c ≤ L.expectedValue :=
  certainty_equivalent_le_expected_value_of_concave hu_mono h hxS hcS hc

/-- The risk premium of any lottery is nonnegative for a risk-averse agent with strictly increasing
utility: The agent will pay a nonnegative price to shed the risk. -/
theorem RiskAverse.risk_premium_nonneg {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ}
    (h : RiskAverse u S) (hu_mono : StrictMonoOn u S) {L : FinLottery n} {c : ℝ}
    (hxS : ∀ i, L.outcome i ∈ S) (hcS : c ∈ S) (hc : IsCertaintyEquivalent u L c) :
    0 ≤ riskPremium L c :=
  risk_premium_nonneg_of_concave hu_mono h hxS hcS hc

/-- For a strictly risk-averse agent facing a non-degenerate lottery, the risk premium is strictly
positive: The agent strictly prefers the sure expected value to the gamble. -/
theorem StrictlyRiskAverse.risk_premium_pos {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ}
    (h : StrictlyRiskAverse u S) (hu_mono : StrictMonoOn u S) {L : FinLottery n} {c : ℝ}
    (hxS : ∀ i, L.outcome i ∈ S) (hcS : c ∈ S)
    (hnondeg : ∃ i j, 0 < L.prob.pmf i ∧ 0 < L.prob.pmf j ∧ L.outcome i ≠ L.outcome j)
    (hc : IsCertaintyEquivalent u L c) :
    0 < riskPremium L c :=
  risk_premium_pos_of_strict_concave hu_mono h hxS hcS hnondeg hc

/-- A risk-loving agent values a lottery at least as much as its expected value for sure:
`u(∑ pᵢ·xᵢ) ≤ ∑ pᵢ·u(xᵢ)`. -/
theorem RiskLoving.le_map_sum {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ} (h : RiskLoving u S)
    {L : FinLottery n} (hxS : ∀ i, L.outcome i ∈ S) :
    u (∑ i, L.prob.pmf i * L.outcome i) ≤ ∑ i, L.prob.pmf i * u (L.outcome i) := by
  have h_smul : u (∑ i, L.prob.pmf i • L.outcome i) ≤ ∑ i, L.prob.pmf i • u (L.outcome i) :=
    ConvexOn.map_sum_le h (fun i _ => L.prob.nonneg i) L.prob.sum_one (fun i _ => hxS i)
  simpa only [smul_eq_mul] using h_smul

/-- A risk-neutral agent assigns a lottery exactly the utility of its expected value:
`∑ pᵢ·u(xᵢ) = u(∑ pᵢ·xᵢ)`. The expected value is required to lie in the domain `S` where affinity
holds. -/
theorem RiskNeutral.map_sum_eq {n : ℕ} {u : ℝ → ℝ} {S : Set ℝ} (h : RiskNeutral u S)
    {L : FinLottery n} (hxS : ∀ i, L.outcome i ∈ S)
    (hmean : (∑ i, L.prob.pmf i * L.outcome i) ∈ S) :
    ∑ i, L.prob.pmf i * u (L.outcome i) = u (∑ i, L.prob.pmf i * L.outcome i) := by
  obtain ⟨a, b, hab⟩ := h
  have hsum :
      ∑ i, L.prob.pmf i * u (L.outcome i) = a * (∑ i, L.prob.pmf i * L.outcome i) + b := by
    have : ∀ i, L.prob.pmf i * u (L.outcome i) = L.prob.pmf i * (a * L.outcome i + b) :=
      fun i => by rw [hab (L.outcome i) (hxS i)]
    simp only [this, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, L.prob.sum_one, one_mul,
      mul_left_comm a, Finset.mul_sum]
  rw [hsum, hab (∑ i, L.prob.pmf i * L.outcome i) hmean]

end Econlib.Preferences
