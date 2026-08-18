/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.DirichletMultinomial.Basic
public import Econlib.Probability.FinDist.ConditionalOn

/-!
# Ordered draws: The exchangeable (Pólya-urn) sequence law behind the Dirichlet-Multinomial

The Dirichlet-Multinomial counts arise from an exchangeable sequence of individual category draws:
Draw `p ~ Dirichlet(α)`, then sample categories `θ₁, …, θ_ℓ` i.i.d. from `p`. Marginalizing out
`p`, the probability of a *specific ordered* sequence `s : Fin ℓ → Fin m` depends only on its
category counts and equals `B(count(s) + α) / B(α)` — the Pólya-urn / de Finetti form, with **no**
multinomial coefficient (that coefficient appears only when one collapses orderings into a count,
recovering `dirichletMultinomialPMF`).

This file builds that law as a `FinDist (Fin ℓ → Fin m)` and uses it to certify the closed-form
marginal and conditional category probabilities in `DirichletMultinomial.Basic`
(`dirichletMultinomialMarginal`, `dirichletMultinomialConditionalSame`,
`dirichletMultinomialConditionalDiff`) as genuine (conditional) probabilities of individual draws.

## Main definitions

* `seqCount`: The category occurrence counts of an ordered draw sequence.
* `orderedDrawPMF`: The Pólya-urn probability of one ordered sequence, `B(count + α) / B(α)`.
* `FinDist.dirichletPolya`: The ordered-draw law as a finite distribution on `Fin ℓ → Fin m`.

## Main statements

* `orderedDrawPMF_sum_one`: The ordered-draw law is a probability distribution (urn recursion).
* `dirichletMultinomialMarginal_eq_probEvent`: `π_k = Pr(θ₁ = k)` under the ordered-draw law.
* `dirichletMultinomialConditionalSame_eq_cond`, `dirichletMultinomialConditionalDiff_eq_cond`: The
  closed-form conditionals are the conditional probabilities `Pr(θ₂ = · ∣ θ₁ = k)`.

## Tags

dirichlet-multinomial, pólya urn, exchangeable sequence, de finetti, conditional probability
-/

@[expose] public section

open scoped BigOperators

namespace Econlib.Probability

variable {m ℓ : ℕ}

/-- The **category occurrence counts** of an ordered draw sequence: `seqCount s i` is the number of
positions `j` at which `s` draws category `i`. -/
def seqCount (s : Fin ℓ → Fin m) : Fin m → ℕ :=
  fun i => (Finset.univ.filter (fun j => s j = i)).card

/-- The occurrence counts of a length-`ℓ` sequence sum to `ℓ`. -/
lemma seqCount_sum (s : Fin ℓ → Fin m) : ∑ i, seqCount s i = ℓ := by
  -- Partition the `ℓ` positions by category: the fiber over `i` has card `seqCount s i`.
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin ℓ))) (t := (Finset.univ : Finset (Fin m)))
    (f := s) (fun a _ => Finset.mem_univ (s a))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- Appending a draw of category `i` increments that category's count by one and leaves the others
fixed: `seqCount (Fin.snoc s i) = seqCount s + eᵢ`. -/
lemma seqCount_snoc (s : Fin ℓ → Fin m) (i : Fin m) :
    seqCount (Fin.snoc s i : Fin (ℓ + 1) → Fin m) =
      fun j => seqCount s j + (if j = i then 1 else 0) := by
  funext j
  -- Write each fiber card as a sum of `0/1` indicators over the index set.
  simp only [seqCount, Finset.card_filter]
  -- Split `Fin (ℓ+1)` into `castSucc`-positions (matching `s`) and the last position (drawing `i`).
  rw [Fin.sum_univ_castSucc]
  congr 1
  · -- On `castSucc l'`, `Fin.snoc s i (castSucc l') = s l'`.
    refine Finset.sum_congr rfl (fun l' _ => ?_)
    rw [Fin.snoc_castSucc]
  · -- At `last ℓ`, `Fin.snoc s i (last ℓ) = i`; the indicator is `if i = j` ↦ `if j = i`.
    rw [Fin.snoc_last]
    congr 1
    exact propext eq_comm

/-- The **ordered-draw PMF**: The Pólya-urn probability of one ordered category sequence `s`, equal
to `B(count(s) + α) / B(α)`. Unlike `dirichletMultinomialPMF`, there is no multinomial coefficient
— this is the probability of a single *ordered* outcome, not of a count. -/
noncomputable def orderedDrawPMF (α : Fin m → ℝ) (s : Fin ℓ → Fin m) : ℝ :=
  multivariateBeta m (fun i => seqCount s i + α i) / multivariateBeta m α

/-- The ordered-draw PMF is strictly positive for positive concentration parameters: Both the
numerator `B(count(s) + α)` and the denominator `B(α)` are positive multivariate Beta values. -/
private lemma orderedDrawPMF_pos {α : Fin m → ℝ} (hα : ∀ i, 0 < α i) (hm : 0 < m)
    (s : Fin ℓ → Fin m) : 0 < orderedDrawPMF α s := by
  unfold orderedDrawPMF
  apply div_pos
  · exact multivariateBeta_pos hm (fun i => by positivity [hα i])
  · exact multivariateBeta_pos hm hα

/-- The ordered-draw PMF is nonnegative for positive concentration parameters. -/
lemma orderedDrawPMF_nonneg {α : Fin m → ℝ} (hα : ∀ i, 0 < α i) (hm : 0 < m)
    (s : Fin ℓ → Fin m) : 0 ≤ orderedDrawPMF α s :=
  le_of_lt (orderedDrawPMF_pos hα hm s)

/-- **Pólya-urn (Vandermonde) step for the multivariate Beta.** Summing the single-increment Beta
values `B(β + eᵢ)` over all categories `i` recovers `B(β)`: Each summand is `B(β) · (βᵢ / β₀)` by
`multivariateBeta_shift_ratio`, and `∑ᵢ βᵢ / β₀ = 1`. -/
private lemma sum_multivariateBeta_shift (d : DirichletDist m) (hm : 0 < m) :
    ∑ i, multivariateBeta m (d.shiftAlpha i 1) = multivariateBeta m d.alpha := by
  have hBα_ne : multivariateBeta m d.alpha ≠ 0 := multivariateBeta_ne_zero hm d.alpha_pos
  -- Each summand is `B(α) · (αᵢ / α₀)` after clearing the ratio lemma's denominator.
  have hterm : ∀ i, multivariateBeta m (d.shiftAlpha i 1) =
      multivariateBeta m d.alpha * (d.alpha i / d.alphaSum) := by
    intro i
    have h := d.multivariateBeta_shift_ratio hm i
    field_simp at h ⊢
    linarith [h]
  simp_rw [hterm, ← Finset.mul_sum]
  -- `∑ᵢ αᵢ / α₀ = α₀ / α₀ = 1`.
  rw [← Finset.sum_div]
  have hsum : ∑ i, d.alpha i = d.alphaSum := rfl
  rw [hsum, div_self (d.alphaSum_ne_zero hm), mul_one]

/-- **The ordered-draw law is a probability distribution.** Summing the Pólya-urn probabilities
over all ordered sequences of length `ℓ` gives one. Proved by induction on `ℓ`: Appending one more
draw sums the single-increment Beta ratios `∑ᵢ B(β + eᵢ)/B(β) = ∑ᵢ βᵢ/β₀ = 1`
(`DirichletDist.multivariateBeta_shift_ratio`). -/
lemma orderedDrawPMF_sum_one {α : Fin m → ℝ} (hα : ∀ i, 0 < α i) (hm : 0 < m) (ℓ : ℕ) :
    ∑ s : Fin ℓ → Fin m, orderedDrawPMF α s = 1 := by
  induction ℓ with
  | zero =>
    -- A `Fin 0 → Fin m` is unique (the empty function); its count is `0`, so PMF `= B(α)/B(α) = 1`.
    rw [Fintype.sum_unique]
    unfold orderedDrawPMF
    have hcount : (fun i => (seqCount (default : Fin 0 → Fin m) i : ℝ) + α i) = α := by
      funext i
      simp only [seqCount]
      have : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
      rw [this]
      simp
    rw [hcount, div_self (multivariateBeta_ne_zero hm hα)]
  | succ ℓ ih =>
    -- Reindex `Fin (ℓ+1) → Fin m` sequences via `Fin.snocEquiv`: a sequence is `Fin.snoc s' i`.
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (ℓ + 1) => Fin m))]
    rw [Fintype.sum_prod_type]
    -- The outer index of `snocEquiv` is the appended draw `i`, the inner is the prefix `s'`.
    rw [Finset.sum_comm]
    -- For each prefix `s'`, the inner sum over the appended draw collapses to `orderedDrawPMF s'`.
    rw [← ih]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    -- Package the prefix's count-shifted parameters as a Dirichlet distribution `d'`.
    set d' : DirichletDist m := ⟨fun j => seqCount s' j + α j, fun j => by positivity [hα j]⟩
      with hd'
    -- Each appended draw `i` shifts `d'` at coordinate `i` by one.
    have hinner : ∀ i, orderedDrawPMF α (Fin.snoc s' i : Fin (ℓ + 1) → Fin m) =
        multivariateBeta m (d'.shiftAlpha i 1) / multivariateBeta m α := by
      intro i
      unfold orderedDrawPMF
      congr 2
      funext j
      rw [seqCount_snoc]
      simp only [DirichletDist.shiftAlpha, hd']
      split_ifs with h <;> push_cast <;> ring
    have hreindex : ∀ i, (Fin.snocEquiv (fun _ : Fin (ℓ + 1) => Fin m)) (i, s') =
        (Fin.snoc s' i : Fin (ℓ + 1) → Fin m) := fun i => rfl
    simp_rw [hreindex, hinner]
    -- The inner sum is `(∑ᵢ B(d'.shift i 1)) / B(α) = B(d'.alpha) / B(α) = orderedDrawPMF s'`.
    rw [← Finset.sum_div, sum_multivariateBeta_shift d' hm]
    rfl

/-- The **ordered-draw (Pólya-urn) law** of length `ℓ` for a Dirichlet prior `d`: The exchangeable
sequence law on `Fin ℓ → Fin m` whose category counts are Dirichlet-Multinomial. -/
noncomputable def FinDist.dirichletPolya (d : DirichletDist m) (hm : 0 < m) (ℓ : ℕ) :
    FinDist (Fin ℓ → Fin m) where
  pmf := orderedDrawPMF d.alpha
  nonneg s := orderedDrawPMF_nonneg d.alpha_pos hm s
  sum_one := orderedDrawPMF_sum_one d.alpha_pos hm ℓ

/-- The PMF of `FinDist.dirichletPolya` at `s` is the ordered-draw probability. -/
@[simp] lemma FinDist.dirichletPolya_apply (d : DirichletDist m) (hm : 0 < m) (ℓ : ℕ)
    (s : Fin ℓ → Fin m) :
    (FinDist.dirichletPolya d hm ℓ).pmf s = orderedDrawPMF d.alpha s := rfl

/-- **The closed-form marginal is the first-draw probability.** Under the ordered-draw law the
probability that the first draw is category `k` equals `dirichletMultinomialMarginal`, i.e.
`α_k / α₀`. -/
theorem dirichletMultinomialMarginal_eq_probEvent (d : DirichletDist m) (hm : 0 < m) (k : Fin m) :
    (FinDist.dirichletPolya d hm 1).probEvent {s | s 0 = k} =
      dirichletMultinomialMarginal d.alpha k := by
  -- The single-draw event `{s 0 = k}` over `Fin 1 → Fin m` contains exactly `fun _ => k`.
  rw [FinDist.probEvent_eq_sum_filter]
  -- Collapse the filtered sum to the constant sequence `fun _ => k` via `Equiv.funUnique`.
  have hfilter : (Finset.univ.filter (fun s : Fin 1 → Fin m => s ∈ {s | s 0 = k})) =
      {(fun _ : Fin 1 => k)} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Finset.mem_singleton]
    constructor
    · intro h; funext j; rw [Subsingleton.elim j 0]; exact h
    · intro h; rw [h]
  rw [hfilter, Finset.sum_singleton, FinDist.dirichletPolya_apply]
  -- `seqCount (fun _ => k) = e_k`, so the count-shifted parameters are `d.shiftAlpha k 1`.
  unfold orderedDrawPMF
  have hcount : (fun j => (seqCount (fun _ : Fin 1 => k) j : ℝ) + d.alpha j) =
      d.shiftAlpha k 1 := by
    funext j
    simp only [DirichletDist.shiftAlpha]
    -- The single position `0` draws `k`, so the fiber over `j` is `{0}` iff `k = j`, else `∅`.
    have hsc : seqCount (fun _ : Fin 1 => k) j = if j = k then 1 else 0 := by
      simp only [seqCount, Finset.card_filter, Fin.sum_univ_one]
      by_cases h : j = k
      · simp [h]
      · rw [if_neg (fun hkj : k = j => h hkj.symm), if_neg h]
    rw [hsc]
    by_cases h : j = k <;> simp [h, add_comm]
  rw [hcount, d.multivariateBeta_shift_ratio hm k]
  rfl

/-- For a length-`2` sequence `s`, the category count at `j` is `[s 0 = j] + [s 1 = j]`. -/
private lemma seqCount_pair (s : Fin 2 → Fin m) (j : Fin m) :
    seqCount s j = (if s 0 = j then 1 else 0) + (if s 1 = j then 1 else 0) := by
  simp only [seqCount, Finset.card_filter, Fin.sum_univ_two]

/-- The constant-`k` first-coordinate marginal over `Fin 2 → Fin m`: The event `{s 0 = k}`
reindexes by the free second coordinate `s 1`, and summing the ordered-draw masses recovers the
single-increment Beta ratio `B(α + e_k) / B(α)`, i.e. `α_k / α₀`. -/
private lemma probEvent_first_eq (d : DirichletDist m) (hm : 0 < m) (k : Fin m) :
    (FinDist.dirichletPolya d hm 2).probEvent {s | s 0 = k} =
      multivariateBeta m (d.shiftAlpha k 1) / multivariateBeta m d.alpha := by
  rw [FinDist.probEvent_eq_sum_filter]
  -- Reindex the `{s 0 = k}` fiber by the second coordinate `t = s 1` via `finTwoArrowEquiv`.
  have hreindex : (Finset.univ.filter (fun s : Fin 2 → Fin m => s ∈ {s | s 0 = k})) =
      Finset.image (fun t : Fin m => ![k, t]) Finset.univ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Finset.mem_image]
    constructor
    · intro h
      exact ⟨s 1, by funext i; fin_cases i <;> simp [h]⟩
    · rintro ⟨t, _, rfl⟩; rfl
  rw [hreindex, Finset.sum_image (by
    intro a _ b _ hab
    have := congrArg (fun f => f 1) hab; simpa using this)]
  -- Package `α + e_k` as a Dirichlet distribution; the sum over `t` is the urn step on its base.
  set dk : DirichletDist m :=
    ⟨fun j => d.alpha j + (if k = j then 1 else 0), fun j => by positivity [d.alpha_pos j]⟩
    with hdk
  -- Each summand `orderedDrawPMF (![k,t]) = B(dk.shiftAlpha t 1) / B(α)`.
  have hterm : ∀ t : Fin m, (FinDist.dirichletPolya d hm 2).pmf (![k, t]) =
      multivariateBeta m (dk.shiftAlpha t 1) / multivariateBeta m d.alpha := by
    intro t
    rw [FinDist.dirichletPolya_apply]
    unfold orderedDrawPMF
    congr 2
    funext j
    rw [seqCount_pair]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      DirichletDist.shiftAlpha, hdk]
    push_cast
    -- Normalize the second indicator `t = j` to `j = t` to match the `shiftAlpha t` condition.
    rw [show (if t = j then (1 : ℝ) else 0) = (if j = t then 1 else 0) from by
      congr 1; exact propext eq_comm]
    split_ifs with h1 h2 <;> ring
  simp_rw [hterm, ← Finset.sum_div, sum_multivariateBeta_shift dk hm]
  -- `dk.alpha = α + e_k = d.shiftAlpha k 1`, so the numerator is `B(d.shiftAlpha k 1)`.
  congr 2
  funext j
  simp only [hdk, DirichletDist.shiftAlpha]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ring

/-- The first-draw event `{θ₁ = k}` has positive probability, so it can be conditioned on. -/
theorem dirichletPolya_first_probEvent_pos (d : DirichletDist m) (hm : 0 < m) (k : Fin m) :
    0 < (FinDist.dirichletPolya d hm 2).probEvent {s | s 0 = k} := by
  rw [FinDist.probEvent_eq_sum_filter]
  -- The filter is nonempty (contains `![k, k]`) and every ordered-draw mass is strictly positive.
  apply Finset.sum_pos
  · intro s _
    exact orderedDrawPMF_pos d.alpha_pos hm s
  · exact ⟨![k, k], by simp [Finset.mem_filter, Set.mem_setOf_eq]⟩

/-- The intersection event `{s 0 = k} ∩ {s 1 = t}` over `Fin 2 → Fin m` is the single sequence
`![k, t]`, so its mass under the ordered-draw law is `orderedDrawPMF d.alpha ![k, t]`. -/
private lemma probEvent_pair_inter (d : DirichletDist m) (hm : 0 < m) (k t : Fin m)
    [DecidablePred (· ∈ {s : Fin 2 → Fin m | s 0 = k} ∩ {s | s 1 = t})] :
    (FinDist.dirichletPolya d hm 2).probEvent
        ({s : Fin 2 → Fin m | s 0 = k} ∩ {s | s 1 = t}) =
      orderedDrawPMF d.alpha (![k, t]) := by
  rw [FinDist.probEvent_eq_sum_filter]
  have hfilter : (Finset.univ.filter
      (fun s : Fin 2 → Fin m => s ∈ {s : Fin 2 → Fin m | s 0 = k} ∩ {s | s 1 = t})) =
      {(![k, t] : Fin 2 → Fin m)} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
      Set.mem_setOf_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp [h0, h1]
    · rintro rfl; exact ⟨rfl, rfl⟩
  rw [hfilter, Finset.sum_singleton, FinDist.dirichletPolya_apply]

/-- The ordered-draw mass of a length-`2` sequence `![k, t]`, expressed through a shifted-Dirichlet
base `α + e_k`: Appending `t` to a single `k`-draw shifts that base at coordinate `t`. Used to read
off the conditional probabilities `Pr(θ₂ = · ∣ θ₁ = k)` as single-increment Beta ratios. -/
private lemma orderedDrawPMF_pair (d : DirichletDist m) (k t : Fin m) :
    orderedDrawPMF d.alpha (![k, t]) =
      multivariateBeta m
          ((⟨fun j => d.alpha j + (if k = j then 1 else 0),
            fun j => by positivity [d.alpha_pos j]⟩ : DirichletDist m).shiftAlpha t 1) /
        multivariateBeta m d.alpha := by
  set dk : DirichletDist m :=
    ⟨fun j => d.alpha j + (if k = j then 1 else 0), fun j => by positivity [d.alpha_pos j]⟩
    with hdk
  unfold orderedDrawPMF
  congr 2
  funext j
  rw [seqCount_pair]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    DirichletDist.shiftAlpha, hdk]
  push_cast
  rw [show (if t = j then (1 : ℝ) else 0) = (if j = t then 1 else 0) from by
    congr 1; exact propext eq_comm]
  split_ifs with h1 h2 <;> ring

/-- **The closed-form same-category conditional is a genuine conditional probability.** Under the
ordered-draw law, `Pr(θ₂ = k ∣ θ₁ = k) = dirichletMultinomialConditionalSame`, i.e.
`(α_k + 1)/(α₀ + 1)`. -/
theorem dirichletMultinomialConditionalSame_eq_cond (d : DirichletDist m) (hm : 0 < m) (k : Fin m) :
    ((FinDist.dirichletPolya d hm 2).conditionalOn {s | s 0 = k}
        (dirichletPolya_first_probEvent_pos d hm k)).probEvent {s | s 1 = k} =
      dirichletMultinomialConditionalSame d.alpha k := by
  -- Conditional event probability is `Pr({s 0 = k} ∩ {s 1 = k}) / Pr({s 0 = k})`.
  rw [FinDist.probEvent_conditionalOn]
  rw [probEvent_pair_inter d hm k k, probEvent_first_eq d hm k, orderedDrawPMF_pair d k k]
  -- Package the base `α + e_k`; the shift at `k` reads off `(α_k + 1)/(α₀ + 1)`.
  set dk : DirichletDist m :=
    ⟨fun j => d.alpha j + (if k = j then 1 else 0), fun j => by positivity [d.alpha_pos j]⟩
    with hdk
  -- The denominator `B(d.shiftAlpha k 1) = B(dk.alpha)`.
  have hden : d.shiftAlpha k 1 = dk.alpha := by
    funext j
    simp only [DirichletDist.shiftAlpha, hdk]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  rw [hden]
  -- `B(dk.shiftAlpha k 1) / B(α) / (B(dk.alpha) / B(α)) = B(dk.shiftAlpha k 1)/B(dk.alpha)`.
  rw [div_div_div_cancel_right₀ (multivariateBeta_ne_zero hm d.alpha_pos)]
  rw [dk.multivariateBeta_shift_ratio hm k]
  -- `dk.alpha k = α_k + 1`, `dk.alphaSum = α₀ + 1`.
  have hdkk : dk.alpha k = d.alpha k + 1 := by simp [hdk]
  have hdksum : dk.alphaSum = d.alphaSum + 1 := by
    simp only [DirichletDist.alphaSum, hdk]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq Finset.univ k (fun _ => (1 : ℝ))]
    simp
  rw [hdkk, hdksum]
  simp [dirichletMultinomialConditionalSame, DirichletDist.alphaSum]

/-- **The closed-form different-category conditional is a genuine conditional probability.** For
`k ≠ t`, under the ordered-draw law `Pr(θ₂ = t ∣ θ₁ = k) = dirichletMultinomialConditionalDiff`,
i.e. `α_t/(α₀ + 1)`. The hypothesis `k ≠ t` is load-bearing: For `k = t` the same-category formula
applies instead. -/
theorem dirichletMultinomialConditionalDiff_eq_cond (d : DirichletDist m) (hm : 0 < m)
    (k t : Fin m) (hkt : k ≠ t) :
    ((FinDist.dirichletPolya d hm 2).conditionalOn {s | s 0 = k}
        (dirichletPolya_first_probEvent_pos d hm k)).probEvent {s | s 1 = t} =
      dirichletMultinomialConditionalDiff d.alpha k t := by
  -- Conditional event probability is `Pr({s 0 = k} ∩ {s 1 = t}) / Pr({s 0 = k})`.
  rw [FinDist.probEvent_conditionalOn]
  rw [probEvent_pair_inter d hm k t, probEvent_first_eq d hm k, orderedDrawPMF_pair d k t]
  -- Package the base `α + e_k`; the shift at `t ≠ k` reads off `α_t/(α₀ + 1)`.
  set dk : DirichletDist m :=
    ⟨fun j => d.alpha j + (if k = j then 1 else 0), fun j => by positivity [d.alpha_pos j]⟩
    with hdk
  have hden : d.shiftAlpha k 1 = dk.alpha := by
    funext j
    simp only [DirichletDist.shiftAlpha, hdk]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  rw [hden]
  rw [div_div_div_cancel_right₀ (multivariateBeta_ne_zero hm d.alpha_pos)]
  rw [dk.multivariateBeta_shift_ratio hm t]
  -- `dk.alpha t = α_t` (since `k ≠ t`), `dk.alphaSum = α₀ + 1`.
  have hdkt : dk.alpha t = d.alpha t := by simp [hdk, hkt]
  have hdksum : dk.alphaSum = d.alphaSum + 1 := by
    simp only [DirichletDist.alphaSum, hdk]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq Finset.univ k (fun _ => (1 : ℝ))]
    simp
  rw [hdkt, hdksum]
  simp [dirichletMultinomialConditionalDiff, DirichletDist.alphaSum]

end Econlib.Probability
