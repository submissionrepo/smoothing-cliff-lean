/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.FOSD.FinDist
public import Mathlib.Data.Finset.Sort

/-!
# The FOSD complete lattice on `FinDist α`

For an arbitrary finite linear order `α`, the set `FinDist α` ordered by first-order stochastic
dominance forms a complete lattice. The order is built on the cumulative distribution function
`FinDist.cdf` (mass at or below a cutoff), and a distribution is recovered from its CDF by
`FinDist.ofCdf`.

## Main definitions

* `FinDist.ofCdf` — recover a distribution from a monotone, nonnegative CDF with maximal value `1`.
* `FinDist.fosdsSup` — the FOSD supremum of a set of distributions.

## Main statements

* `FinDist.cdf_injective` — a distribution is determined by its CDF.
* `FinDist.fosdPartialOrder` — the FOSD partial order on `FinDist α`.
* `FinDist.fosdCompleteLattice` — the complete lattice on `FinDist α` under FOSD.

## Notes

The Knaster–Tarski stationary-distribution consequences for stochastically monotone Markov chains
live in `Econlib.Probability.Markov.FOSDLattice`.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.

## Tags

first-order stochastic dominance, fosd, complete lattice, cdf
-/

@[expose] public noncomputable section

namespace Econlib.Probability

open Finset BigOperators

/-! ## `Fin n` arithmetic engine

The discrete-derivative correspondence between a distribution's PMF and its CDF, and the
recovery of a distribution from a CDF vector, are intrinsically `ℕ`-indexed. They are proved here
as `private` lemmas over `FinDist (Fin n)` (using the generic `FinDist.cdf`, which on `Fin n`
coincides with `∑_{i ≤ k} d.pmf i`) and transported to a general finite linear order below. -/

variable {n : ℕ}

/-- The predecessor index `i.val - 1` stays within bounds. -/
lemma fin_val_sub_lt (i : Fin n) : i.val - 1 < n :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt

private lemma FinDist.cdf_at_zero (d : FinDist (Fin n)) (h0 : 0 < n) :
    d.cdf ⟨0, h0⟩ = d.pmf ⟨0, h0⟩ := by
  simp only [cdf]
  have : univ.filter (fun j : Fin n => j ≤ ⟨0, h0⟩) = {⟨0, h0⟩} := by
    ext ⟨j, hj⟩; simp only [mem_filter, mem_univ, true_and, mem_singleton,
      Fin.le_iff_val_le_val, Fin.ext_iff]; omega
  rw [this, sum_singleton]

private lemma FinDist.cdf_step (d : FinDist (Fin n)) (k : ℕ) (hk1 : k + 1 < n) (hk : k < n) :
    d.cdf ⟨k + 1, hk1⟩ = d.cdf ⟨k, hk⟩ + d.pmf ⟨k + 1, hk1⟩ := by
  simp only [cdf]
  have hfilt : univ.filter (fun j : Fin n => j ≤ ⟨k + 1, hk1⟩) =
      (univ.filter (fun j : Fin n => j ≤ ⟨k, hk⟩)) ∪ {⟨k + 1, hk1⟩} := by
    ext ⟨j, hj⟩; simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton,
      Fin.le_iff_val_le_val, Fin.ext_iff]; omega
  have hdisj : Disjoint
      (univ.filter (fun j : Fin n => j ≤ ⟨k, hk⟩)) {⟨k + 1, hk1⟩} := by
    rw [disjoint_singleton_right]; simp only [mem_filter, Fin.le_iff_val_le_val]; omega
  rw [hfilt, sum_union hdisj, sum_singleton]

/-- PMF is the discrete derivative of the CDF. -/
private lemma FinDist.pmf_eq_cdf_diff (d : FinDist (Fin n)) (i : Fin n) :
    d.pmf i = d.cdf i -
      if _h : (i : ℕ) = 0 then 0 else d.cdf ⟨i.val - 1, fin_val_sub_lt i⟩ := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero =>
    simp only [↓reduceDIte, sub_zero]
    exact (d.cdf_at_zero hi).symm
  | succ k =>
    have hk : k < n := by omega
    have h0 : (⟨k + 1, hi⟩ : Fin n).val ≠ 0 := by simp
    simp only [h0, ↓reduceDIte]
    -- ⟨Fin.val ⟨k+1, hi⟩ - 1, _⟩ = ⟨k, hk⟩ by proof irrelevance (vals equal)
    have hfin : (⟨(⟨k + 1, hi⟩ : Fin n).val - 1, fin_val_sub_lt ⟨k + 1, hi⟩⟩ : Fin n) =
        ⟨k, hk⟩ := Fin.ext (by simp)
    rw [hfin]
    linarith [d.cdf_step k hi hk]

/-- Recover a `FinDist (Fin n)` from a monotone, nonnegative CDF vector with last value `1`. -/
def FinDist.ofCdfVec [NeZero n] (C : Fin n → ℝ)
    (hC_mono : Monotone C) (hC_nn : ∀ k, 0 ≤ C k)
    (hC_last : C ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩ = 1) : FinDist (Fin n) where
  pmf i := C i - if h : (i : ℕ) = 0 then 0 else C ⟨i.val - 1, fin_val_sub_lt i⟩
  nonneg i := by
    by_cases h0 : (i : ℕ) = 0
    · simp only [h0, ↓reduceDIte, sub_zero]; exact hC_nn i
    · simp only [h0, ↓reduceDIte]
      have : (⟨i.val - 1, fin_val_sub_lt i⟩ : Fin n) ≤ i :=
        Fin.mk_le_mk.mpr (Nat.sub_le _ _)
      linarith [hC_mono this]
  sum_one := by
    -- Telescope via sum_range_sub: ∑ (C(i) - C(i-1)) = C(last) - 0 = 1
    set g : ℕ → ℝ := fun j =>
      if j = 0 then 0 else if h : j - 1 < n then C ⟨j - 1, h⟩ else 1
    suffices hterm : ∀ i : Fin n,
        (C i - if h : (i : ℕ) = 0 then 0 else C ⟨i.val - 1, fin_val_sub_lt i⟩) =
        g (i.val + 1) - g i.val by
      simp_rw [hterm]
      have hrange := Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) n
      rw [hrange, Finset.sum_range_sub g n]
      simp only [g, show n ≠ 0 from NeZero.ne n, ↓reduceIte,
        show n - 1 < n from Nat.sub_one_lt (NeZero.ne n), ↓reduceDIte]; linarith
    intro ⟨i, hi⟩
    simp only [g]
    cases i with
    | zero =>
      simp only [↓reduceDIte, sub_zero, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte,
        show 1 - 1 = 0 by omega, show (0 : ℕ) < n from hi, ↓reduceDIte]
    | succ k =>
      have h0 : (⟨k + 1, hi⟩ : Fin n).val ≠ 0 := by simp
      simp only [h0, ↓reduceDIte, ↓reduceIte,
        show k + 1 + 1 ≠ 0 by omega,
        show k + 1 + 1 - 1 = k + 1 by omega, hi, ↓reduceDIte,
        show k + 1 - 1 = k by omega, show k < n by omega]
      -- simp has already closed the goal via Fin proof irrelevance

private lemma FinDist.ofCdfVec_cdf [NeZero n] (C : Fin n → ℝ)
    (hC_mono : Monotone C) (hC_nn : ∀ k, 0 ≤ C k)
    (hC_last : C ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩ = 1) :
    (FinDist.ofCdfVec C hC_mono hC_nn hC_last).cdf = C := by
  funext ⟨k, hk⟩
  induction k with
  | zero =>
    rw [FinDist.cdf_at_zero _ hk]
    change C ⟨0, hk⟩ - (if _h : (⟨0, hk⟩ : Fin n).val = 0 then 0
      else C ⟨(⟨0, hk⟩ : Fin n).val - 1, _⟩) = C ⟨0, hk⟩
    simp
  | succ k ih =>
    have hk' : k < n := by omega
    rw [FinDist.cdf_step _ k hk hk', ih hk']
    change C ⟨k, hk'⟩ + (C ⟨k + 1, hk⟩ - (if _h : (⟨k + 1, hk⟩ : Fin n).val = 0 then 0
      else C ⟨(⟨k + 1, hk⟩ : Fin n).val - 1, _⟩)) = C ⟨k + 1, hk⟩
    have h0 : (⟨k + 1, hk⟩ : Fin n).val ≠ 0 := by simp
    simp only [h0, ↓reduceDIte]
    -- The inner Fin element has val = k+1-1 = k, so C values match
    have : C (⟨(⟨k + 1, hk⟩ : Fin n).val - 1, fin_val_sub_lt ⟨k + 1, hk⟩⟩ : Fin n) =
        C ⟨k, hk'⟩ := congr_arg C (Fin.ext (by simp))
    linarith

/-! ## Transport along the order isomorphism `Fin (card α) ≃o α` -/

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Pull a distribution on `α` back to `Fin (card α)` along the order iso `e`. -/
def pullback (e : Fin (Fintype.card α) ≃o α) (d : FinDist α) :
    FinDist (Fin (Fintype.card α)) where
  pmf i := d (e i)
  nonneg i := d.nonneg (e i)
  sum_one := by
    have hsum := Fintype.sum_equiv e.toEquiv
      (fun i : Fin (Fintype.card α) => d (e i)) (fun a : α => d a) (by intro i; simp)
    exact hsum.trans d.sum_one

/-- Push a distribution on `Fin (card α)` forward to `α` along the order iso `e`. -/
def pushforward (e : Fin (Fintype.card α) ≃o α)
    (df : FinDist (Fin (Fintype.card α))) : FinDist α where
  pmf a := df (e.symm a)
  nonneg a := df.nonneg (e.symm a)
  sum_one := by
    have hsum := Fintype.sum_equiv e.symm.toEquiv
      (fun a : α => df (e.symm a)) (fun i : Fin (Fintype.card α) => df i) (by intro a; simp)
    exact hsum.trans df.sum_one

/-- The CDF transports: The pullback's CDF at `k` equals the original CDF at `e k`. The filters
correspond because `e` is an order isomorphism (`i ≤ k ↔ e i ≤ e k`). -/
lemma pullback_cdf (e : Fin (Fintype.card α) ≃o α) (d : FinDist α)
    (k : Fin (Fintype.card α)) :
    (pullback e d).cdf k = d.cdf (e k) := by
  change ∑ i ∈ univ.filter (fun j => j ≤ k), d (e i) =
    ∑ x ∈ univ.filter (fun y => y ≤ e k), d x
  apply Finset.sum_equiv e.toEquiv
  · intro i
    simp only [mem_filter, mem_univ, true_and, OrderIso.coe_toEquiv, e.le_iff_le]
  · intro i _; rfl

end FinDist

/-! ## CDF injectivity and recovery from a CDF over `α` -/

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- A distribution is determined by its CDF: Equal CDFs imply equal distributions. -/
lemma cdf_injective {d₁ d₂ : FinDist α}
    (h : ∀ a, d₁.cdf a = d₂.cdf a) : d₁ = d₂ := by
  -- A nonempty state space carries the distribution; `card α ≠ 0`.
  have hne : Nonempty α := by
    by_contra hempty
    have hempty' : IsEmpty α := ⟨fun a => hempty ⟨a⟩⟩
    have : (1 : ℝ) = 0 := by
      rw [← d₁.sum_one]
      exact Finset.sum_eq_zero fun i _ => hempty'.false i |>.elim
    norm_num at this
  letI : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  let e : Fin (Fintype.card α) ≃o α := Fintype.orderIsoFinOfCardEq α rfl
  -- The pullbacks have pointwise-equal CDFs, hence equal PMFs by the Fin discrete derivative.
  have hcdfFin : ∀ k, (pullback e d₁).cdf k = (pullback e d₂).cdf k := by
    intro k; rw [pullback_cdf, pullback_cdf]; exact h (e k)
  have hpmfFin : ∀ k, (pullback e d₁).pmf k = (pullback e d₂).pmf k := by
    intro k
    rw [(pullback e d₁).pmf_eq_cdf_diff k, (pullback e d₂).pmf_eq_cdf_diff k]
    split <;> simp only [hcdfFin]
  -- Pull pmf equality back through the surjective `e`.
  ext a
  have := hpmfFin (e.symm a)
  simpa [pullback, OrderIso.apply_symm_apply] using this

omit [DecidableEq α] in
/-- The canonical order iso `Fin (card α) ≃o α` sends the top index to the maximum of `α`. -/
lemma orderIso_top_eq_max [Nonempty α]
    (e : Fin (Fintype.card α) ≃o α) (htop : NeZero (Fintype.card α)) :
    e ⟨Fintype.card α - 1, Nat.sub_one_lt (NeZero.ne _)⟩ = univ.max' univ_nonempty := by
  apply le_antisymm
  · exact le_max' univ _ (mem_univ _)
  · -- `max' univ = e j` for some `j`, and `j.val ≤ card - 1`, so `max' univ ≤ e (top)`.
    obtain ⟨j, hj⟩ : ∃ j, e j = univ.max' univ_nonempty :=
      ⟨e.symm (univ.max' univ_nonempty), by rw [OrderIso.apply_symm_apply]⟩
    rw [← hj]
    exact e.monotone (Fin.mk_le_mk.mpr (by omega))

omit [DecidableEq α] in
/-- The CDF-vector hypotheses for `ofCdf`, packaged for reuse in `ofCdf` and `ofCdf_cdf`. -/
lemma ofCdf_last_aux [Nonempty α] (htop : NeZero (Fintype.card α))
    (e : Fin (Fintype.card α) ≃o α) (C : α → ℝ) (hmax : C (univ.max' univ_nonempty) = 1) :
    C (e ⟨Fintype.card α - 1, Nat.sub_one_lt (NeZero.ne _)⟩) = 1 := by
  rw [orderIso_top_eq_max e htop]; exact hmax

/-- Recover a distribution on `α` from a monotone, nonnegative CDF with maximal value `1`. -/
def ofCdf [Nonempty α] (C : α → ℝ) (hmono : Monotone C) (hnn : ∀ a, 0 ≤ C a)
    (hmax : C (univ.max' univ_nonempty) = 1) : FinDist α :=
  letI : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  let e : Fin (Fintype.card α) ≃o α := Fintype.orderIsoFinOfCardEq α rfl
  pushforward e (FinDist.ofCdfVec (fun i => C (e i))
    (fun _ _ hij => hmono (e.monotone hij))
    (fun i => hnn (e i))
    (ofCdf_last_aux ⟨Fintype.card_ne_zero⟩ e C hmax))

@[simp] lemma ofCdf_cdf [Nonempty α] (C : α → ℝ) (hmono : Monotone C) (hnn : ∀ a, 0 ≤ C a)
    (hmax : C (univ.max' univ_nonempty) = 1) :
    (ofCdf C hmono hnn hmax).cdf = C := by
  letI : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  let e : Fin (Fintype.card α) ≃o α := Fintype.orderIsoFinOfCardEq α rfl
  -- Abbreviate the underlying `Fin`-CDF vector.
  set CFin : FinDist (Fin (Fintype.card α)) :=
    FinDist.ofCdfVec (fun i => C (e i)) (fun _ _ hij => hmono (e.monotone hij))
      (fun i => hnn (e i)) (ofCdf_last_aux ⟨Fintype.card_ne_zero⟩ e C hmax) with hCFin
  have hpush : ofCdf C hmono hnn hmax = pushforward e CFin := rfl
  funext a
  -- Evaluate at `a = e (e.symm a)` and transport through the pullback CDF correspondence.
  have hpull : pullback e (pushforward e CFin) = CFin := by
    ext k; change CFin (e.symm (e k)) = CFin k; rw [OrderIso.symm_apply_apply]
  have key : (ofCdf C hmono hnn hmax).cdf (e (e.symm a)) = CFin.cdf (e.symm a) := by
    rw [hpush, ← pullback_cdf e (pushforward e CFin) (e.symm a), hpull]
  rw [OrderIso.apply_symm_apply] at key
  rw [key, hCFin, FinDist.ofCdfVec_cdf, OrderIso.apply_symm_apply]

end FinDist

/-! ## FOSD Partial Order -/

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Finite FOSD is reflexive. -/
lemma FinDist.FOSD_refl (d : FinDist α) : FinDist.FOSD d d :=
  fun _ => le_refl _

/-- Finite FOSD is transitive. -/
lemma FinDist.FOSD_trans {d₁ d₂ d₃ : FinDist α}
    (h₁ : FinDist.FOSD d₁ d₂) (h₂ : FinDist.FOSD d₂ d₃) :
    FinDist.FOSD d₁ d₃ :=
  fun a => le_trans (h₁ a) (h₂ a)

/-- Finite FOSD is antisymmetric: Mutual dominance forces equal CDFs, hence equal distributions. -/
lemma FinDist.FOSD_antisymm {d₁ d₂ : FinDist α}
    (h₁ : FinDist.FOSD d₁ d₂) (h₂ : FinDist.FOSD d₂ d₁) : d₁ = d₂ :=
  FinDist.cdf_injective fun a => le_antisymm (h₁ a) (h₂ a)

/-- FOSD partial order on `FinDist α`: Higher in FOSD means larger. -/
instance FinDist.fosdPartialOrder : PartialOrder (FinDist α) where
  le d₁ d₂ := FinDist.FOSD d₂ d₁
  le_refl d := FinDist.FOSD_refl d
  le_trans _ _ _ h₁ h₂ := FinDist.FOSD_trans h₂ h₁
  le_antisymm _ _ h₁ h₂ := FinDist.FOSD_antisymm h₂ h₁

/-- The partial-order `≤` unfolds to FOSD: `d₁ ≤ d₂` means `d₂` dominates `d₁`. -/
lemma FinDist.le_iff_fosd (d₁ d₂ : FinDist α) :
    d₁ ≤ d₂ ↔ FinDist.FOSD d₂ d₁ := Iff.rfl

/-- The partial-order `≤` unfolds to reverse CDF dominance at every cutoff. -/
lemma FinDist.le_iff_cdf_ge (d₁ d₂ : FinDist α) :
    d₁ ≤ d₂ ↔ ∀ k, d₂.cdf k ≤ d₁.cdf k := Iff.rfl

/-! ## Complete Lattice -/

section CompleteLattice
variable [Nonempty α]

open Classical in
/-- FOSD supremum: Pointwise infimum of CDFs (nonempty case) packaged back via `ofCdf`. -/
def FinDist.fosdsSup (S : Set (FinDist α)) : FinDist α :=
  if hne : S.Nonempty then
    FinDist.ofCdf
      (fun a => sInf ((fun d => d.cdf a) '' S))
      (by -- Monotone: inf of CDFs is monotone in the cutoff
        intro a₁ a₂ ha
        apply le_csInf (hne.image _)
        rintro _ ⟨d, hd, rfl⟩
        exact le_trans
          (csInf_le ⟨0, fun x ⟨d', _, hx⟩ => hx ▸ d'.cdf_nonneg a₁⟩ ⟨d, hd, rfl⟩)
          (d.cdf_mono ha))
      (by -- Nonneg
        intro a
        exact le_csInf (hne.image _) fun _ ⟨d, _, hx⟩ => hx ▸ d.cdf_nonneg a)
      (by -- Max value = 1: every CDF hits 1 at the maximum
        have : (fun d : FinDist α => d.cdf (univ.max' univ_nonempty)) '' S = {1} := by
          ext x; simp only [Set.mem_image, Set.mem_singleton_iff]
          exact ⟨fun ⟨d, _, hx⟩ => hx ▸ d.cdf_max,
                 fun hx => let ⟨d, hd⟩ := hne; ⟨d, hd, by rw [d.cdf_max]; exact hx.symm⟩⟩
        simp only [this, csInf_singleton])
  else
    FinDist.pure (univ.min' univ_nonempty)

/-- The FOSD supremum supplies the `SupSet` structure on `FinDist α`. -/
instance FinDist.instSupSet : SupSet (FinDist α) where
  sSup := FinDist.fosdsSup

open Classical in
/-- On a nonempty `S`, the FOSD supremum's CDF is the pointwise infimum of the members' CDFs. -/
lemma FinDist.fosdsSup_cdf_of_nonempty {S : Set (FinDist α)} (hne : S.Nonempty) (a : α) :
    (fosdsSup S).cdf a = sInf ((fun d => d.cdf a) '' S) := by
  have : (fosdsSup S).cdf = fun a => sInf ((fun d => d.cdf a) '' S) := by
    unfold fosdsSup; simp only [dif_pos hne]; exact ofCdf_cdf _ _ _ _
  exact congr_fun this a

open Classical in
/-- The FOSD supremum is the least upper bound of `S` in the FOSD order. -/
lemma FinDist.isLUB_fosdsSup (S : Set (FinDist α)) :
    IsLUB S (FinDist.fosdsSup S) := by
  constructor
  · -- Upper bound: the sup's CDF lies below each member's CDF
    intro d hd a
    have hne : S.Nonempty := ⟨d, hd⟩
    change (fosdsSup S).cdf a ≤ d.cdf a
    rw [fosdsSup_cdf_of_nonempty hne]
    exact csInf_le ⟨0, fun x ⟨d', _, hx⟩ => hx ▸ d'.cdf_nonneg a⟩ ⟨d, hd, rfl⟩
  · -- Least upper bound
    intro u hu a
    by_cases hne : S.Nonempty
    · change u.cdf a ≤ (fosdsSup S).cdf a
      rw [fosdsSup_cdf_of_nonempty hne]
      exact le_csInf (hne.image _) fun _ ⟨d, hd, hx⟩ => hx ▸ (hu hd) a
    · change u.cdf a ≤ (fosdsSup S).cdf a
      have : fosdsSup S = FinDist.pure (univ.min' univ_nonempty) := by
        unfold fosdsSup; exact dif_neg hne
      simp only [this, pure_min_cdf]; exact u.cdf_le_one a

/-- `FinDist α` is a complete lattice under first-order stochastic dominance. -/
instance FinDist.fosdCompleteLattice : CompleteLattice (FinDist α) :=
  completeLatticeOfSup (FinDist α) FinDist.isLUB_fosdsSup

end CompleteLattice

end Econlib.Probability

end
