/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Algebra.BigOperators.AbelSummation
public import Econlib.Probability.FinDist.CDF
public import Econlib.Probability.FinDist.Expect
public import Econlib.Probability.FinDist.Simplex
public import Econlib.Probability.Order.FOSD.Basic
public import Mathlib.Data.Finset.Sort

/-!
# FOSD over finite distributions

Finite-state first-order stochastic dominance for `FinDist α` over an arbitrary finite linear
order. The relation `FinDist.FOSD` is defined in `FOSD.Basic` (masses ordered at every cutoff);
this file develops its theory: The unfolding through `FinDist.cdf`, the pure-distribution ordering,
and the equivalence between FOSD and ordering the expectations of all monotone payoffs (Hadar and
Russell 1969).

## Main statements

* `FinDist.FOSD_iff` — FOSD is CDF dominance at every cutoff.
* `FinDist.FOSD_pure` — point masses are FOSD-ordered by their support points.
* `FinDist.FOSD_expect_mono`, `FinDist.FOSD_expect_antitone` — FOSD orders expectations of monotone
  (resp. antitone) payoffs.
* `FinDist.FOSD_iff_expect_mono` — FOSD holds iff every monotone payoff is weakly preferred.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.

## Tags

first-order stochastic dominance, fosd, finite distribution, monotone, expectation
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability

open Econlib

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-! ## Characterization and pure distributions -/

/-- Finite FOSD unfolds to pointwise CDF dominance: `d₁` dominates `d₂` iff its CDF lies weakly
below `d₂`'s at every cutoff. -/
lemma FOSD_iff (d₁ d₂ : FinDist α) :
    FinDist.FOSD d₁ d₂ ↔ ∀ a, d₁.cdf a ≤ d₂.cdf a := Iff.rfl

/-- FOSD for pure distributions: `pure s₂` FOSD-dominates `pure s₁` when `s₁ ≤ s₂`. -/
lemma FOSD_pure {s₁ s₂ : α} (hs : s₁ ≤ s₂) :
    FinDist.FOSD (FinDist.pure s₂ : FinDist α) (FinDist.pure s₁) := by
  rw [FOSD_iff]
  intro a
  rw [FinDist.pure_cdf, FinDist.pure_cdf]
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (le_trans hs h1) h2
  · linarith
  · exact le_refl _

/-! ## Abel summation engine (`Fin n`) -/

/-- FOSD orders monotone expectations on `Fin n`: If `d₁` first-order stochastically dominates `d₂`
and `f` is monotone, then `E_{d₂}[f] ≤ E_{d₁}[f]`. The `Fin n` engine driving the general
finite-linear-order result. -/
private theorem FOSD_expect_mono_fin {n : ℕ}
    {d₁ d₂ : FinDist (Fin n)} (h : FinDist.FOSD d₁ d₂)
    {f : Fin n → ℝ} (hf : Monotone f) :
    FinDist.expect d₂ f ≤ FinDist.expect d₁ f := by
  rcases n with _ | m
  · simp [FinDist.expect, Finset.univ_eq_empty]
  -- n = m + 1
  unfold FinDist.expect
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  -- Extend d₁ - d₂ and f to ℕ-indexed functions for Abel summation
  let a : ℕ → ℝ := fun j =>
    if h : j < m + 1 then d₁.pmf ⟨j, h⟩ - d₂.pmf ⟨j, h⟩ else 0
  let f' : ℕ → ℝ := fun j =>
    if h : j < m + 1 then f ⟨j, h⟩ else f ⟨m, by omega⟩
  -- Convert Fin sum to range sum
  have hconv : ∑ i : Fin (m + 1), (d₁.pmf i - d₂.pmf i) * f i =
      ∑ i ∈ Finset.range (m + 1), a i * f' i := by
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1; ext ⟨i, hi⟩
    change (d₁.pmf ⟨i, hi⟩ - d₂.pmf ⟨i, hi⟩) * f ⟨i, hi⟩ = a i * f' i
    simp only [a, f', dif_pos hi]
  rw [hconv]
  -- Apply Abel summation
  rw [Finset.sum_range_mul_by_parts m a f']
  -- Boundary term: ∑ (d₁ - d₂) = 1 - 1 = 0
  have hsum_zero : ∑ i ∈ Finset.range (m + 1), a i = 0 := by
    have : ∑ i ∈ Finset.range (m + 1), a i =
        ∑ i : Fin (m + 1), (d₁.pmf i - d₂.pmf i) := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; ext ⟨i, hi⟩
      change a i = d₁.pmf ⟨i, hi⟩ - d₂.pmf ⟨i, hi⟩
      simp only [a, dif_pos hi]
    rw [this, Finset.sum_sub_distrib, d₁.sum_one, d₂.sum_one, sub_self]
  rw [hsum_zero, zero_mul, zero_sub, neg_nonneg]
  apply Finset.sum_nonpos
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  apply mul_nonpos_of_nonpos_of_nonneg
  · have hkm : k < m + 1 := by omega
    rw [Finset.sum_range_dite_eq_sum_filter (fun i => d₁.pmf i - d₂.pmf i) k hkm]
    rw [Finset.sum_sub_distrib]
    linarith [h ⟨k, hkm⟩]
  · change 0 ≤ f' (k + 1) - f' k
    have hk1 : k + 1 < m + 1 := by omega
    have hk0 : k < m + 1 := by omega
    simp only [f', dif_pos hk1, dif_pos hk0]
    exact sub_nonneg.mpr (hf (by simp [Fin.le_iff_val_le_val]))

/-! ## Monotone expectations over a finite linear order -/

/-- **FOSD raises expectations of monotone payoffs** on any finite ordered space. If `d₁`
first-order stochastically dominates `d₂` and `f` is monotone, then `𝔼_{d₂}[f] ≤ 𝔼_{d₁}[f]` (Hadar
and Russell 1969). -/
theorem FOSD_expect_mono {d₁ d₂ : FinDist α}
    (h : FinDist.FOSD d₁ d₂) {f : α → ℝ} (hf : Monotone f) :
    d₂.expect f ≤ d₁.expect f := by
  have hcard : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
  let e : Fin (Fintype.card α) ↪o α :=
    (Finset.univ : Finset α).orderEmbOfFin hcard
  have hmap_univ :
      Finset.map e.toEmbedding Finset.univ = (Finset.univ : Finset α) := by
    simp [e, Finset.map_orderEmbOfFin_univ (s := (Finset.univ : Finset α)) hcard]
  -- Reindex any sum over `α` along the order embedding `e`.
  have hsum_emb : ∀ g : α → ℝ,
      ∑ i : Fin (Fintype.card α), g (e i) = ∑ a : α, g a := by
    intro g
    have hsum_map := Finset.sum_map
      (s := (Finset.univ : Finset (Fin (Fintype.card α))))
      (e := e.toEmbedding) (f := g)
    rw [hmap_univ] at hsum_map
    exact hsum_map.symm
  have hsum_index : ∀ d : FinDist α,
      ∑ i : Fin (Fintype.card α), d (e i) = 1 := fun d => (hsum_emb (fun a => d a)).trans d.sum_one
  let d₁F : FinDist (Fin (Fintype.card α)) := {
    pmf i := d₁ (e i)
    nonneg i := d₁.nonneg (e i)
    sum_one := hsum_index d₁ }
  let d₂F : FinDist (Fin (Fintype.card α)) := {
    pmf i := d₂ (e i)
    nonneg i := d₂.nonneg (e i)
    sum_one := hsum_index d₂ }
  let fF : Fin (Fintype.card α) → ℝ := fun i => f (e i)
  have hcdf_index : ∀ (d : FinDist α) (k : Fin (Fintype.card α)),
      ∑ i ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k), d (e i) =
        d.cdf (e k) := by
    intro d k
    have hmap_filter :
        Finset.map e.toEmbedding
            (Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k)) =
          Finset.univ.filter (fun a : α => a ≤ e k) := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_map.mp ha with ⟨i, hi, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, e.monotone (Finset.mem_filter.mp hi).2⟩
      · intro ha
        have ha_le : a ≤ e k := (Finset.mem_filter.mp ha).2
        have ha_mem_map : a ∈ Finset.map e.toEmbedding Finset.univ := by
          simp [hmap_univ]
        rcases Finset.mem_map.mp ha_mem_map with ⟨i, hi, hi_eq⟩
        refine Finset.mem_map.mpr ⟨i, ?_, hi_eq⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        apply e.le_iff_le.mp
        simpa [← hi_eq] using ha_le
    have hsum_map := Finset.sum_map
      (s := Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k))
      (e := e.toEmbedding) (f := fun a : α => d a)
    rw [hmap_filter] at hsum_map
    exact hsum_map.symm
  have hF : FinDist.FOSD d₁F d₂F := by
    intro k
    change ∑ i ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k), d₁ (e i) ≤
      ∑ i ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k), d₂ (e i)
    rw [hcdf_index d₁ k, hcdf_index d₂ k]
    exact h (e k)
  have hfF : Monotone fF := fun i j hij => hf (e.monotone hij)
  have hfin := FOSD_expect_mono_fin hF hfF
  have hexpect_index : ∀ d : FinDist α,
      ∑ i : Fin (Fintype.card α), d (e i) * f (e i) =
        ∑ a : α, d a * f a := fun d => hsum_emb (fun a => d a * f a)
  simpa [FinDist.expect, FinDist.expect, d₁F, d₂F, fF,
    hexpect_index d₁, hexpect_index d₂] using hfin

/-- **FOSD lowers expectations of antitone payoffs** on any finite ordered space. -/
lemma FOSD_expect_antitone {d₁ d₂ : FinDist α}
    (h : FinDist.FOSD d₁ d₂) {g : α → ℝ} (hg : Antitone g) :
    d₁.expect g ≤ d₂.expect g := by
  have h_neg_mono : Monotone (-g) := hg.neg
  have h_neg := FinDist.FOSD_expect_mono h h_neg_mono
  simp only [FinDist.expect, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib, neg_le_neg_iff] at h_neg
  exact h_neg

/-! ## The converse: Threshold payoffs detect FOSD -/

/-- **Universal monotone preference implies FOSD.** If every monotone payoff has a weakly higher
expectation under `d₁` than under `d₂`, then `d₁` first-order stochastically dominates `d₂`.

The witnesses are the monotone threshold payoffs `x ↦ if x ≤ a then 0 else 1`, whose expectation is
`1 - cdf a`. -/
theorem FOSD_of_expect_mono {d₁ d₂ : FinDist α}
    (h : ∀ f : α → ℝ, Monotone f → d₂.expect f ≤ d₁.expect f) :
    FinDist.FOSD d₁ d₂ := by
  intro a
  -- The monotone threshold payoff at cutoff `a`.
  set f : α → ℝ := fun x => if x ≤ a then 0 else 1 with hf_def
  have hf_mono : Monotone f := by
    intro x x' hxx'
    by_cases hx'a : x' ≤ a
    · -- both at or below the cutoff: payoff 0 on both sides
      simp [hf_def, le_trans hxx' hx'a, hx'a]
    · -- above the cutoff the payoff is 1, the maximum value
      simp only [hf_def, if_neg hx'a]
      split_ifs <;> norm_num
  -- The threshold payoff's expectation is the mass above the cutoff, `1 - cdf a`.
  have hexpect_threshold : ∀ d : FinDist α, d.expect f = 1 - d.cdf a := by
    intro d
    have hsummand : ∀ x, d.pmf x * f x = d.pmf x - (if x ≤ a then d x else 0) := by
      intro x
      by_cases hxa : x ≤ a <;> simp [hf_def, hxa]
    calc d.expect f
        = ∑ x, (d.pmf x - if x ≤ a then d x else 0) :=
          Finset.sum_congr rfl fun x _ => hsummand x
      _ = (∑ x, d.pmf x) - ∑ x, (if x ≤ a then d x else 0) := by
          rw [Finset.sum_sub_distrib]
      _ = 1 - d.cdf a := by rw [d.sum_one, FinDist.cdf_eq_sum_ite]
  have hthreshold := h f hf_mono
  rw [hexpect_threshold d₁, hexpect_threshold d₂] at hthreshold
  -- The FOSD goal is the filter-sum spelling of the CDF comparison.
  change d₁.cdf a ≤ d₂.cdf a
  linarith

/-- **FOSD ⟺ all monotone payoffs ordered.** First-order stochastic dominance of `d₁` over `d₂`
holds exactly when every decision maker with a monotone valuation weakly prefers `d₁`. -/
theorem FOSD_iff_expect_mono (d₁ d₂ : FinDist α) :
    FinDist.FOSD d₁ d₂ ↔ ∀ f : α → ℝ, Monotone f → d₂.expect f ≤ d₁.expect f :=
  ⟨fun h _ hf => FOSD_expect_mono h hf, FOSD_of_expect_mono⟩

end FinDist

end Econlib.Probability
