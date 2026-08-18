/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Combinatorics.Fin2
public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Econlib.SocialChoice.ChoiceFunction.Properties
public import Econlib.SocialChoice.Rule.Majority
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.FinCases

/-!
# May's Theorem

May (1952) characterizes the majority rule on two alternatives: Any social choice function on a
2-alternative universal domain satisfying anonymity, neutrality, and positive responsiveness must
select the strict-majority winner when one exists, and must return both alternatives when votes are
exactly tied.

## Main definitions

* `otherFin2` — the complement of an alternative in `Fin 2`
* `swapFin2` — the permutation of `Fin 2` swapping the two alternatives
* `relabelPref`, `relabelProfile` — action of a permutation of `Fin 2` on preferences and profiles
* `indiffPref` — the total-indifference preference relation
* `indiffAt` — profile obtained by setting one voter to total indifference

## Main statements

* `tied_profile_winners_univ` — under anonymity and neutrality, a tied profile yields both
  alternatives as winners
* `may_strict_majority_wins` — under anonymity, neutrality, and positive responsiveness, a strict
  majority winner is the unique winner
* `winners_eq_majorityRule` — the hard converse direction: Any rule satisfying the three axioms on
  the universal domain agrees with `majorityRule` on every profile
* `may_characterization` — the full characterization packaged as a single iff: A full-domain rule
  satisfies anonymity, neutrality, and positive responsiveness iff it agrees with `majorityRule` on
  every profile (bundles `winners_eq_majorityRule` with the `majorityRule_*` axiom lemmas)

## References

* May, Kenneth O. 1952. “A Set of Independent Necessary and Sufficient Conditions for Simple
  Majority Decision.” *Econometrica* 20 (4): 680. [https://doi.org/10.2307/1907651](https://doi.org/10.2307/1907651).

## Tags

social choice, May's theorem, majority rule, anonymity, neutrality, positive responsiveness
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter : Type*} [DecidableEq Voter]

/-- Lift a permutation of `Fin 2` to act on a single voter's preference. -/
def relabelPref (τ : Equiv.Perm (Fin 2)) (R : PreferenceRel (Fin 2)) :
    PreferenceRel (Fin 2) where
  le := fun a b => R.le (τ.symm a) (τ.symm b)
  le_refl := fun _ => R.le_refl _
  le_trans := fun _ _ _ => R.le_trans _ _ _
  le_total := fun _ _ => R.le_total _ _

/-- Lift a permutation of `Fin 2` to act on a profile by relabeling each voter's preference. This
is the action used in the neutrality axiom. -/
def relabelProfile (τ : Equiv.Perm (Fin 2)) (P : Profile Voter (Fin 2)) :
    Profile Voter (Fin 2) :=
  fun i => relabelPref τ (P i)

/-- The total-indifference preference. -/
def indiffPref (Alt : Type*) : PreferenceRel Alt where
  le := fun _ _ => True
  le_refl := fun _ => trivial
  le_trans := fun _ _ _ _ _ => trivial
  le_total := fun _ _ => Or.inl trivial

@[simp] lemma indiffPref_not_lt {Alt : Type*} (x y : Alt) :
    ¬ (indiffPref Alt).lt x y := fun h => h.2 trivial

/-- A voter strictly preferring `x` to `y` does not strictly prefer `y` to `x`. -/
lemma not_lt_swap_of_lt {Alt : Type*} {R : PreferenceRel Alt} {x y : Alt}
    (h : R.lt x y) : ¬ R.lt y x := fun h' => h.2 h'.1

/-- Two `PreferenceRel`s are equal when their `le` relations agree pointwise. -/
lemma PreferenceRel.eq_of_le_iff {Alt : Type*} {R S : PreferenceRel Alt}
    (h : ∀ a b, R.le a b ↔ S.le a b) : R = S := by
  apply PreferenceRel.ext_le
  funext a b
  exact propext (h a b)

/-- On `Fin 2`, a strict preference relation `winner ≻ other` is determined by its `le` values. -/
lemma preferenceRel_fin2_eq_of_lt {x y : Fin 2} (hxy : x ≠ y)
    {R S : PreferenceRel (Fin 2)} (hR : R.lt x y) (hS : S.lt x y) :
    R = S := by
  apply PreferenceRel.eq_of_le_iff
  intro a b
  have hRle : R.le x y := hR.1
  have hRn : ¬ R.le y x := hR.2
  have hSle : S.le x y := hS.1
  have hSn : ¬ S.le y x := hS.2
  have hcases : ∀ z : Fin 2, z = x ∨ z = y := by
    intro z
    fin_cases z <;> fin_cases x <;> fin_cases y <;>
      first | (left; rfl) | (right; rfl) | (exact absurd rfl hxy)
  rcases hcases a with ha | ha <;> rcases hcases b with hb | hb <;>
    subst ha <;> subst hb
  · exact ⟨fun _ => S.le_refl _, fun _ => R.le_refl _⟩
  · exact ⟨fun _ => hSle, fun _ => hRle⟩
  · exact ⟨fun h => absurd h hRn, fun h => absurd h hSn⟩
  · exact ⟨fun _ => S.le_refl _, fun _ => R.le_refl _⟩

/-! ### Behavior of `relabelPref` and `relabelProfile` on `Fin 2`. -/

/-- On `Fin 2`, `relabelPref swapFin2` swaps strict preferences. -/
lemma relabelPref_swap_lt {R : PreferenceRel (Fin 2)} {x y : Fin 2} :
    (relabelPref swapFin2 R).lt x y ↔ R.lt (swapFin2 x) (swapFin2 y) := by
  unfold relabelPref PreferenceRel.lt
  simp only
  -- swapFin2.symm = swapFin2
  have hsymm : ∀ z, swapFin2.symm z = swapFin2 z := by
    intro z; fin_cases z <;> simp [swapFin2]
  rw [hsymm, hsymm]

/-- `relabelPref` is involutive when `τ` is. -/
lemma relabelPref_swap_swap (R : PreferenceRel (Fin 2)) :
    relabelPref swapFin2 (relabelPref swapFin2 R) = R := by
  apply PreferenceRel.eq_of_le_iff
  intro a b
  unfold relabelPref
  simp only
  have hsymm : ∀ z, swapFin2.symm z = swapFin2 z := by
    intro z; fin_cases z <;> simp [swapFin2]
  rw [hsymm, hsymm]
  fin_cases a <;> fin_cases b <;> simp [swapFin2]

/-- Relabeling a preference by the identity permutation leaves it unchanged. -/
@[simp] lemma relabelPref_one (R : PreferenceRel (Fin 2)) : relabelPref 1 R = R := by
  apply PreferenceRel.eq_of_le_iff
  intro a b
  simp [relabelPref]
  rfl

omit [DecidableEq Voter] in
/-- Relabeling a profile by the identity permutation leaves it unchanged. -/
@[simp] lemma relabelProfile_one (P : Profile Voter (Fin 2)) : relabelProfile 1 P = P := by
  funext i
  exact relabelPref_one (P i)

/-! ### Indifference characterization on `Fin 2`. -/

/-- On `Fin 2`, a preference is exactly one of: Strict winner≻other, strict other≻winner, or both
`winner ≼ other` and `other ≼ winner` (indifferent). -/
lemma fin2_pref_trichotomy (R : PreferenceRel (Fin 2)) (winner : Fin 2) :
    R.lt winner (otherFin2 winner) ∨ R.lt (otherFin2 winner) winner ∨
      (R.le winner (otherFin2 winner) ∧ R.le (otherFin2 winner) winner) := by
  rcases R.trichotomy winner (otherFin2 winner) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h.1, h.2⟩)

/-! ### Counting lemmas for `relabelProfile swapFin2`. -/

section RelabelCounts

variable [Fintype Voter]

omit [DecidableEq Voter] in
/-- The voters strictly preferring `winner` over `other` under `relabelProfile swapFin2 P` are
exactly those strictly preferring `other` over `winner` under `P`. -/
lemma majorityCount_relabel_swap (P : Profile Voter (Fin 2)) (x y : Fin 2) :
    majorityCount (relabelProfile swapFin2 P) x y =
      majorityCount P (swapFin2 x) (swapFin2 y) := by
  classical
  unfold majorityCount
  apply Finset.card_bij (fun i _ => i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact relabelPref_swap_lt.mp hi
  · intros; assumption
  · intro i hi
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact relabelPref_swap_lt.mpr hi

end RelabelCounts

/-! ### Indifferentiating a voter. -/

/-- Update `P` by setting voter `i` to total indifference. -/
def indiffAt (P : Profile Voter (Fin 2)) (i : Voter) :
    Profile Voter (Fin 2) :=
  Function.update P i (indiffPref _)

@[simp] lemma indiffAt_self (P : Profile Voter (Fin 2)) (i : Voter) :
    indiffAt P i i = indiffPref _ := by
  simp [indiffAt]

lemma indiffAt_of_ne (P : Profile Voter (Fin 2)) {i j : Voter} (h : i ≠ j) :
    indiffAt P i j = P j := by
  simp [indiffAt, Function.update_of_ne h.symm]

variable [Fintype Voter]

/-- Indifferentiating a voter who strictly prefers `x` over `y` decrements the corresponding
majority count by one. -/
lemma majorityCount_indiffAt_lt {P : Profile Voter (Fin 2)} {i : Voter}
    {x y : Fin 2} (hi : (P i).lt x y) :
    majorityCount (indiffAt P i) x y + 1 = majorityCount P x y := by
  classical
  unfold majorityCount
  have hfilter :
      (Finset.univ.filter
          (fun j : Voter => ((indiffAt P i) j).lt x y)) =
        (Finset.univ.filter (fun j : Voter => (P j).lt x y)).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · intro hj
      by_cases hji : j = i
      · subst hji; simp [indiffAt] at hj
      · refine ⟨hji, ?_⟩
        rw [indiffAt_of_ne P (Ne.symm hji)] at hj
        exact hj
    · rintro ⟨hji, hj⟩
      rw [indiffAt_of_ne P (Ne.symm hji)]
      exact hj
  rw [hfilter]
  have hi_mem :
      i ∈ Finset.univ.filter (fun j : Voter => (P j).lt x y) := by
    simp [hi]
  rw [Finset.card_erase_of_mem hi_mem]
  have hpos :
      0 < (Finset.univ.filter (fun j : Voter => (P j).lt x y)).card :=
    Finset.card_pos.mpr ⟨i, hi_mem⟩
  omega

/-- Indifferentiating a voter who is not strictly preferring `x` over `y` leaves the count
unchanged. -/
lemma majorityCount_indiffAt_not_lt {P : Profile Voter (Fin 2)} {i : Voter}
    {x y : Fin 2} (hi : ¬ (P i).lt x y) :
    majorityCount (indiffAt P i) x y = majorityCount P x y := by
  classical
  unfold majorityCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst hji
    simp [indiffAt, hi]
  · rw [indiffAt_of_ne P (Ne.symm hji)]

/-! ### Tied profile symmetry. -/

/-- Under anonymity and neutrality, a profile with equal counts of strict preferences for each
alternative yields winners-set `{winner, otherFin2 winner}`. -/
lemma tied_profile_winners_univ
    (f : ChoiceFunction Voter (Fin 2))
    (hAnon : ChoiceFunction.Anonymity f)
    (hNeut : ChoiceFunction.Neutrality f relabelProfile)
    (hDom : ∀ Q : Profile Voter (Fin 2), Q ∈ f.domain)
    (P' : Profile Voter (Fin 2))
    {winner : Fin 2}
    (hties : majorityCount P' winner (otherFin2 winner) =
             majorityCount P' (otherFin2 winner) winner) :
    f.winners P' = ({winner, otherFin2 winner} : Set (Fin 2)) := by
  classical
  set other := otherFin2 winner with hother_def
  set Sw := Finset.univ.filter (fun i : Voter => (P' i).lt winner other)
    with hSw_def
  set So := Finset.univ.filter (fun i : Voter => (P' i).lt other winner)
    with hSo_def
  have hSw_disj_So : Disjoint Sw So := by
    rw [Finset.disjoint_filter]
    intro i _ hi
    exact PreferenceRel.not_lt_both _ hi
  -- `Sw`/`So` are by definition the `majorityCount` filters, so `hties` is the card equality.
  have hcard : Sw.card = So.card := hties
  let φ : {x // x ∈ Sw} ≃ {x // x ∈ So} := Finset.equivOfCardEq hcard
  let σ : Voter → Voter := fun i =>
    if hSw : i ∈ Sw then (φ ⟨i, hSw⟩ : Voter)
    else if hSo : i ∈ So then (φ.symm ⟨i, hSo⟩ : Voter)
    else i
  have hσinv : Function.LeftInverse σ σ := by
    intro i
    by_cases hSw : i ∈ Sw
    · have hmem : (φ ⟨i, hSw⟩ : Voter) ∈ So := (φ ⟨i, hSw⟩).property
      have hnotSw : (φ ⟨i, hSw⟩ : Voter) ∉ Sw := by
        intro h
        exact (Finset.disjoint_left.mp hSw_disj_So) h hmem
      simp only [σ, hSw, dif_pos]
      simp only [hnotSw, dif_neg, not_false_eq_true]
      simp only [hmem, dif_pos]
      -- `⟨φ⟨i,_⟩, hmem⟩` is defeq to `φ⟨i,_⟩`, so `symm_apply_apply` closes it.
      rw [show φ.symm ⟨(φ ⟨i, hSw⟩ : Voter), hmem⟩ = ⟨i, hSw⟩ from
        Equiv.symm_apply_apply φ ⟨i, hSw⟩]
    · by_cases hSo : i ∈ So
      · have hmem : (φ.symm ⟨i, hSo⟩ : Voter) ∈ Sw := (φ.symm ⟨i, hSo⟩).property
        have hnotSo : (φ.symm ⟨i, hSo⟩ : Voter) ∉ So := by
          intro h
          exact (Finset.disjoint_right.mp hSw_disj_So) h hmem
        simp only [σ, hSw, dif_neg, not_false_eq_true]
        simp only [hSo, dif_pos]
        simp only [hmem, dif_pos]
        -- `⟨φ.symm⟨i,_⟩, hmem⟩` is defeq to `φ.symm⟨i,_⟩`, so `apply_symm_apply` closes it.
        rw [show φ ⟨(φ.symm ⟨i, hSo⟩ : Voter), hmem⟩ = ⟨i, hSo⟩ from
          Equiv.apply_symm_apply φ ⟨i, hSo⟩]
      · simp [σ, hSw, hSo]
  let σperm : Equiv.Perm Voter := ⟨σ, σ, hσinv, hσinv⟩
  have hswap_wo : swapFin2 winner = other := by rw [swapFin2_apply, hother_def]
  have hswap_ow : swapFin2 other = winner := by
    rw [swapFin2_apply, hother_def, otherFin2_otherFin2]
  -- Transfer a strict preference under `relabelProfile swapFin2`: `relabelPref_swap_lt` rewrites
  -- the goal through `swapFin2`, which swaps `winner` and `other`.
  have hRelLt : ∀ (j : Voter) {a b : Fin 2},
      (P' j).lt (swapFin2 a) (swapFin2 b) →
        (relabelProfile swapFin2 P' j).lt a b :=
    fun j _ _ h => relabelPref_swap_lt.mpr h
  have hkey : ∀ i : Voter,
      relabelProfile swapFin2 P' (σperm i) = P' i := by
    intro i
    by_cases hSw : i ∈ Sw
    · have hPi : (P' i).lt winner other := by
        rw [hSw_def] at hSw
        exact (Finset.mem_filter.mp hSw).2
      have hσi : σperm i = (φ ⟨i, hSw⟩ : Voter) := by
        change σ i = _
        simp only [σ, hSw, dif_pos]
      have hσi_So : σperm i ∈ So := hσi ▸ (φ ⟨i, hSw⟩).property
      have hPσi : (P' (σperm i)).lt other winner := by
        rw [hSo_def] at hσi_So
        exact (Finset.mem_filter.mp hσi_So).2
      have hRel : (relabelProfile swapFin2 P' (σperm i)).lt winner other :=
        hRelLt (σperm i) (by rw [hswap_wo, hswap_ow]; exact hPσi)
      have hne : winner ≠ other := by
        rw [hother_def]
        exact (otherFin2_ne winner).symm
      exact preferenceRel_fin2_eq_of_lt hne hRel hPi
    · by_cases hSo : i ∈ So
      · have hPi : (P' i).lt other winner := by
          rw [hSo_def] at hSo
          exact (Finset.mem_filter.mp hSo).2
        have hσi : σperm i = (φ.symm ⟨i, hSo⟩ : Voter) := by
          change σ i = _
          simp only [σ, hSw, dif_neg, not_false_eq_true]
          simp only [hSo, dif_pos]
        have hσi_Sw : σperm i ∈ Sw := hσi ▸ (φ.symm ⟨i, hSo⟩).property
        have hPσi : (P' (σperm i)).lt winner other := by
          rw [hSw_def] at hσi_Sw
          exact (Finset.mem_filter.mp hσi_Sw).2
        have hRel : (relabelProfile swapFin2 P' (σperm i)).lt other winner :=
          hRelLt (σperm i) (by rw [hswap_wo, hswap_ow]; exact hPσi)
        have hne : other ≠ winner := otherFin2_ne winner
        exact preferenceRel_fin2_eq_of_lt hne hRel hPi
      · have hσi : σperm i = i := by
          change σ i = _
          simp [σ, hSw, hSo]
        rw [hσi]
        rw [hSw_def] at hSw
        rw [hSo_def] at hSo
        have hPi_not_w : ¬ (P' i).lt winner other := by
          intro hlt
          exact hSw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        have hPi_not_o : ¬ (P' i).lt other winner := by
          intro hlt
          exact hSo (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        have hPi_le_wo : (P' i).le winner other := by
          rcases (P' i).le_total winner other with h | h
          · exact h
          · by_contra hwo
            exact hPi_not_o ⟨h, hwo⟩
        have hPi_le_ow : (P' i).le other winner := by
          rcases (P' i).le_total other winner with h | h
          · exact h
          · by_contra how
            exact hPi_not_w ⟨h, how⟩
        apply PreferenceRel.eq_of_le_iff
        intro a b
        unfold relabelProfile relabelPref
        simp only
        have hsymm : ∀ z, swapFin2.symm z = otherFin2 z := swapFin2_symm_apply
        rw [hsymm, hsymm]
        have hle_all : ∀ a' b' : Fin 2, (P' i).le a' b' := by
          intro a' b'
          fin_cases a' <;> fin_cases b' <;>
            first
              | exact (P' i).le_refl _
              | (rw [hother_def] at hPi_le_wo; rw [hother_def] at hPi_le_ow;
                 fin_cases winner <;> simp_all [otherFin2])
        exact ⟨fun _ => hle_all _ _, fun _ => hle_all _ _⟩
  have hcomp : (relabelProfile swapFin2 P') ∘ σperm = P' := by
    funext i; exact hkey i
  have hP'_dom : P' ∈ f.domain := hDom P'
  have hRel_dom : relabelProfile swapFin2 P' ∈ f.domain := hDom _
  have hComp_dom : (relabelProfile swapFin2 P') ∘ σperm ∈ f.domain := hDom _
  have hAn :=
    hAnon (relabelProfile swapFin2 P') hRel_dom σperm hComp_dom
  rw [hcomp] at hAn
  have hNe := hNeut P' hP'_dom swapFin2 hRel_dom
  have hinv : f.winners P' = swapFin2 '' f.winners P' := hAn.trans hNe
  obtain ⟨a, ha⟩ := f.winners_nonempty P' hP'_dom
  have hswapa : swapFin2 a ∈ f.winners P' := by
    rw [hinv]; exact ⟨a, ha, rfl⟩
  apply Set.eq_of_subset_of_subset
  · intro x _
    fin_cases x <;> fin_cases winner <;> simp [hother_def, otherFin2]
  · intro x _
    have hor : x = a ∨ x = swapFin2 a := by
      fin_cases x <;> fin_cases a <;>
        first | (left; rfl) | (right; simp [swapFin2])
    rcases hor with hxa | hxswap
    · exact hxa ▸ ha
    · exact hxswap ▸ hswapa

/-- Under anonymity, neutrality, and positive responsiveness on a universal domain, any profile
where `winner` strictly outpolls `otherFin2 winner` by `D + 1` has winners-set `{winner}`. -/
lemma may_strict_majority_wins_aux
    (f : ChoiceFunction Voter (Fin 2))
    (hAnon : ChoiceFunction.Anonymity f)
    (hNeut : ChoiceFunction.Neutrality f relabelProfile)
    (hPosResp : ∀ x y : Fin 2, ChoiceFunction.PositiveResponsiveness f x y)
    (hDom : ∀ Q : Profile Voter (Fin 2), Q ∈ f.domain) :
    ∀ (D : ℕ) (P : Profile Voter (Fin 2)) (winner : Fin 2),
      majorityCount P winner (otherFin2 winner) =
        majorityCount P (otherFin2 winner) winner + D + 1 →
      f.winners P = {winner} := by
  classical
  -- Pivot voter: a positive count of strict `winner ≻ other` preferences supplies a witness.
  have hpivot : ∀ (P : Profile Voter (Fin 2)) (winner : Fin 2),
      0 < majorityCount P winner (otherFin2 winner) →
        ∃ i : Voter, (P i).lt winner (otherFin2 winner) := by
    intro P winner hpos
    unfold majorityCount at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨i, hi⟩
  -- Reduction step: once the indifferentiated profile crowns `winner`, positive responsiveness
  -- transfers the win back to `P`, where the pivot voter strictly prefers `winner`.
  have hstep : ∀ (P : Profile Voter (Fin 2)) (winner : Fin 2) (i : Voter),
      (P i).lt winner (otherFin2 winner) →
        winner ∈ f.winners (indiffAt P i) → f.winners P = {winner} := by
    intro P winner i hi hwin_in
    set other := otherFin2 winner
    have hP'_dom : indiffAt P i ∈ f.domain := hDom _
    have hP'_i_not_lt : ¬ (indiffAt P i i).lt winner other := by
      rw [indiffAt_self]; exact indiffPref_not_lt _ _
    have hupdate_eq : Function.update (indiffAt P i) i (P i) = P := by
      rw [indiffAt]; simp [Function.update_idem]
    -- Ceteris paribus: restoring voter `i`'s ballot `P i` over the all-indifferent base touches
    -- only the `winner`-vs-`other` comparison; every other `Fin 2` comparison is reflexive.
    have hcet : ∀ a b : Fin 2, ¬ (a = winner ∧ b = other) → ¬ (a = other ∧ b = winner) →
        ((P i).le a b ↔ (indiffAt P i i).le a b) := by
      intro a b hne1 hne2
      have hab : a = b := fin2_eq_of_not_cross (o := other) (w := winner) rfl hne1 hne2
      subst hab
      rw [indiffAt_self]
      exact iff_of_true ((P i).le_refl _) trivial
    have hpr := hPosResp winner other _ hP'_dom hwin_in i (P i)
                  (hDom _) hP'_i_not_lt hi hcet
    rwa [hupdate_eq] at hpr
  intro D
  induction D with
  | zero =>
    intro P winner hgap
    set other := otherFin2 winner with hother_def
    have hpos : 0 < majorityCount P winner other := by omega
    obtain ⟨i, hi⟩ := hpivot P winner hpos
    set P' := indiffAt P i with hP'_def
    have hcount_w : majorityCount P' winner other + 1 =
                      majorityCount P winner other :=
      majorityCount_indiffAt_lt hi
    have hcount_o : majorityCount P' other winner =
                      majorityCount P other winner :=
      majorityCount_indiffAt_not_lt (not_lt_swap_of_lt hi)
    have hties : majorityCount P' winner other =
                   majorityCount P' other winner := by omega
    have hwin_set : f.winners P' = ({winner, other} : Set (Fin 2)) :=
      tied_profile_winners_univ f hAnon hNeut hDom P' hties
    exact hstep P winner i hi (hwin_set ▸ Or.inl rfl)
  | succ D ih =>
    intro P winner hgap
    set other := otherFin2 winner with hother_def
    have hpos : 0 < majorityCount P winner other := by omega
    obtain ⟨i, hi⟩ := hpivot P winner hpos
    set P' := indiffAt P i with hP'_def
    have hcount_w : majorityCount P' winner other + 1 =
                      majorityCount P winner other :=
      majorityCount_indiffAt_lt hi
    have hcount_o : majorityCount P' other winner =
                      majorityCount P other winner :=
      majorityCount_indiffAt_not_lt (not_lt_swap_of_lt hi)
    have hgap' : majorityCount P' winner other =
                   majorityCount P' other winner + D + 1 := by omega
    have hP'_winners : f.winners P' = {winner} := ih P' winner hgap'
    exact hstep P winner i hi (hP'_winners ▸ rfl)

/-- **May's theorem (May 1952), strict-majority direction.** If `f` satisfies anonymity,
neutrality, and (canonical) positive responsiveness on a universal domain, and `winner` strictly
out-polls `other` in pairwise majority count, then `winner` is the unique winner. -/
theorem may_strict_majority_wins
    (f : ChoiceFunction Voter (Fin 2))
    (hAnon : ChoiceFunction.Anonymity f)
    (hNeut : ChoiceFunction.Neutrality f relabelProfile)
    (hPosResp : ∀ x y : Fin 2, ChoiceFunction.PositiveResponsiveness f x y)
    (hDom : ∀ Q : Profile Voter (Fin 2), Q ∈ f.domain)
    (P : Profile Voter (Fin 2)) (_hP : P ∈ f.domain)
    {winner : Fin 2}
    (h_majority : majorityCount P (otherFin2 winner) winner <
                  majorityCount P winner (otherFin2 winner)) :
    f.winners P = {winner} := by
  set D := majorityCount P winner (otherFin2 winner) -
             majorityCount P (otherFin2 winner) winner - 1 with hD_def
  have hgap :
      majorityCount P winner (otherFin2 winner) =
        majorityCount P (otherFin2 winner) winner + D + 1 := by
    rw [hD_def]; omega
  exact may_strict_majority_wins_aux f hAnon hNeut hPosResp hDom D P winner hgap

/-! ### Canonical simple majority rule on two alternatives

Simple majority rule packaged as a `ChoiceFunction` on the full domain: `x` wins iff at least
as many voters rank `x` over the other alternative as rank the other over `x`. A strict majority
yields a singleton winners-set; an exact split yields both alternatives. The three May axioms hold
for any finite electorate, and `majorityRule_strict_majority_wins` specializes
`may_strict_majority_wins` to this rule. -/

section MajorityRule

/-- The winners-set of simple majority rule: `x` wins iff at least as many voters rank `x` over the
other alternative as rank the other over `x`. -/
def majWinners {Voter : Type*} [Fintype Voter] (P : Profile Voter (Fin 2)) : Set (Fin 2) :=
  { x | majorityCount P (otherFin2 x) x ≤ majorityCount P x (otherFin2 x) }

/-- **Simple majority rule** as a social choice function on two alternatives: Every profile is
admissible, and the winners are the (weakly) majority-preferred alternatives. -/
def majorityRule {Voter : Type*} [Fintype Voter] : ChoiceFunction Voter (Fin 2) where
  domain := Set.univ
  winners := majWinners
  winners_nonempty := by
    intro P _
    rcases le_total (majorityCount P 1 0) (majorityCount P 0 1) with h | h
    · exact ⟨0, by simpa only [majWinners, Set.mem_setOf_eq, otherFin2_zero] using h⟩
    · exact ⟨1, by simpa only [majWinners, Set.mem_setOf_eq, otherFin2_one] using h⟩

/-- Every profile is admissible under majority rule. -/
theorem majorityRule_full_domain {Voter : Type*} [Fintype Voter] :
    ∀ Q : Profile Voter (Fin 2), Q ∈ (majorityRule (Voter := Voter)).domain :=
  fun _ => Set.mem_univ _

/-- **Anonymity.** Permuting the voters leaves the winners-set unchanged, because `majorityCount`
is a cardinality of a voter set invariant under permutation. -/
theorem majorityRule_anonymity {Voter : Type*} [Fintype Voter] [DecidableEq Voter] :
    ChoiceFunction.Anonymity (majorityRule (Voter := Voter)) := by
  intro P _ σ _
  change majWinners (P ∘ σ) = majWinners P
  ext x
  simp only [majWinners, Set.mem_setOf_eq, majorityCount_comp_perm]

/-- Membership in the image of `otherFin2`: `x ∈ otherFin2 '' s ↔ otherFin2 x ∈ s`. -/
private lemma mem_otherFin2_image (s : Set (Fin 2)) (x : Fin 2) :
    x ∈ (fun a => otherFin2 a) '' s ↔ otherFin2 x ∈ s := by
  rw [Set.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [otherFin2_otherFin2]
  · intro hx
    exact ⟨otherFin2 x, hx, by rw [otherFin2_otherFin2]⟩

/-- **Neutrality.** Relabeling the two alternatives commutes with majority rule, because swapping
the alternatives swaps the two majority counts (`majorityCount_relabel_swap`). -/
theorem majorityRule_neutrality {Voter : Type*} [Fintype Voter] :
    ChoiceFunction.Neutrality (majorityRule (Voter := Voter)) relabelProfile := by
  intro P _ τ _
  change majWinners (relabelProfile τ P) = τ '' majWinners P
  rcases perm_fin2_eq τ with hτ | hτ
  · subst hτ
    rw [relabelProfile_one]
    simp [Equiv.Perm.coe_one]
  · subst hτ
    ext x
    simp only [majWinners, Set.mem_setOf_eq, majorityCount_relabel_swap,
      swapFin2_apply, otherFin2_otherFin2, mem_otherFin2_image]

/-- On `Fin 2`, two distinct alternatives are each the `otherFin2` of the other. -/
private lemma eq_other_of_ne {x y : Fin 2} (h : x ≠ y) : y = otherFin2 x := by
  fin_cases x <;> fin_cases y <;> simp_all [otherFin2]

/-- Membership in `majWinners` reads as the count inequality. -/
lemma mem_majWinners_iff {Voter : Type*} [Fintype Voter] (Q : Profile Voter (Fin 2)) (x : Fin 2) :
    x ∈ majWinners Q ↔ majorityCount Q (otherFin2 x) x ≤ majorityCount Q x (otherFin2 x) :=
  Iff.rfl

/-- **Positive responsiveness.** If `x` is winning or tied and one voter shifts strictly toward
`x`, then `x` becomes the unique winner: The shift raises the count for `x ≻ otherFin2 x` by
exactly one (`majorityCount_update_add_one`) while the reverse count cannot rise. -/
theorem majorityRule_positiveResponsiveness {Voter : Type*} [Fintype Voter] [DecidableEq Voter] :
    ∀ x y : Fin 2, ChoiceFunction.PositiveResponsiveness (majorityRule (Voter := Voter)) x y := by
  -- The ceteris-paribus hypothesis (final `_`) is not needed: the count-based proof only uses the
  -- `x`-vs-`y` shift directly.
  intro x y P _ hx i R' _ hPi hR' _
  -- If `x = y` the shift hypothesis `R'.lt x x` is impossible, so the claim is vacuous.
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy; exact absurd hR' (R'.lt_irrefl x)
  -- Otherwise `y` is the other alternative; write `o := otherFin2 x = y`.
  set o := otherFin2 x with ho_def
  have hyo : y = o := eq_other_of_ne hxy
  subst hyo
  set Q := Function.update P i R'
  have hxo_step : majorityCount Q x o = majorityCount P x o + 1 :=
    majorityCount_update_add_one hPi hR'
  have hcount_o_le : majorityCount Q o x ≤ majorityCount P o x :=
    majorityCount_update_le_of_not_lt (not_lt_swap_of_lt hR')
  have hx_win_P : majorityCount P o x ≤ majorityCount P x o := hx
  have hstrict : majorityCount Q o x < majorityCount Q x o := by omega
  rw [show (majorityRule (Voter := Voter)).winners Q = majWinners Q from rfl]
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · rw [mem_majWinners_iff, ← ho_def]; omega
  · intro z hz
    rcases eq_or_ne z x with hzx | hzx
    · exact hzx
    · exfalso
      have hzo : z = o := by rw [ho_def]; exact eq_other_of_ne hzx.symm
      rw [hzo, mem_majWinners_iff, otherFin2_otherFin2] at hz
      omega

/-- **May's conclusion for the canonical majority rule.** Whenever strictly more voters prefer
`winner` to the other alternative than the reverse, `winner` is the unique social choice. The
`DecidableEq Voter` needed by the anonymity/positive-responsiveness inputs is supplied classically;
the count-based conclusion is independent of which decidability instance is used. -/
theorem majorityRule_strict_majority_wins {Voter : Type*} [Fintype Voter]
    (P : Profile Voter (Fin 2)) {winner : Fin 2}
    (h_majority : majorityCount P (otherFin2 winner) winner
      < majorityCount P winner (otherFin2 winner)) :
    (majorityRule (Voter := Voter)).winners P = {winner} := by
  classical
  exact may_strict_majority_wins majorityRule majorityRule_anonymity majorityRule_neutrality
    majorityRule_positiveResponsiveness majorityRule_full_domain P
    (majorityRule_full_domain P) h_majority

/-- **May's theorem (May 1952), characterization.** Any choice function `f` satisfying anonymity,
neutrality, and positive responsiveness on the universal domain is simple majority rule: It agrees
with `majorityRule` on the winners-set of every profile. On two alternatives every profile is
either a strict majority for one side — where `may_strict_majority_wins` crowns the unique winner
for both `f` and `majorityRule` — or an exact tie — where `tied_profile_winners_univ` elects both
for each. This is the converse, "hard" direction of May (1952); the easy direction is that
`majorityRule` itself satisfies the axioms
(`majorityRule_anonymity`/`_neutrality`/`_positiveResponsiveness`). -/
theorem winners_eq_majorityRule {Voter : Type*} [Fintype Voter] [DecidableEq Voter]
    (f : ChoiceFunction Voter (Fin 2))
    (hAnon : ChoiceFunction.Anonymity f)
    (hNeut : ChoiceFunction.Neutrality f relabelProfile)
    (hPosResp : ∀ x y : Fin 2, ChoiceFunction.PositiveResponsiveness f x y)
    (hDom : ∀ Q : Profile Voter (Fin 2), Q ∈ f.domain)
    (P : Profile Voter (Fin 2)) :
    f.winners P = (majorityRule (Voter := Voter)).winners P := by
  rcases lt_trichotomy (majorityCount P 0 1) (majorityCount P 1 0) with h | h | h
  · -- `1` strictly out-polls `0`: both rules crown `1`.
    rw [may_strict_majority_wins f hAnon hNeut hPosResp hDom P (hDom P)
          (winner := 1) (by rwa [otherFin2_one]),
        majorityRule_strict_majority_wins (Voter := Voter) P
          (winner := 1) (by rwa [otherFin2_one])]
  · -- Exact tie: both rules elect both alternatives.
    rw [tied_profile_winners_univ f hAnon hNeut hDom P
          (winner := 0) (by rwa [otherFin2_zero]),
        tied_profile_winners_univ majorityRule majorityRule_anonymity
          majorityRule_neutrality majorityRule_full_domain P
          (winner := 0) (by rwa [otherFin2_zero])]
  · -- `0` strictly out-polls `1`: both rules crown `0`.
    rw [may_strict_majority_wins f hAnon hNeut hPosResp hDom P (hDom P)
          (winner := 0) (by rwa [otherFin2_zero]),
        majorityRule_strict_majority_wins (Voter := Voter) P
          (winner := 0) (by rwa [otherFin2_zero])]

/-- **May's theorem, packaged as an iff.** On two alternatives and the universal domain, a choice
function `f` satisfies anonymity, neutrality, and positive responsiveness if and only if it is
simple majority rule (it agrees with `majorityRule` on the winners-set of every profile).

This bundles both directions of May (1952) into a single characterization:

* (⟹) the hard converse direction `winners_eq_majorityRule`: The three axioms force `f` to be
  majority rule;
* (⟸) the easy direction: `majorityRule` itself satisfies the axioms (`majorityRule_anonymity` /
  `majorityRule_neutrality` / `majorityRule_positiveResponsiveness`), and each axiom is phrased
  purely through the winners-set, so it transports back along the pointwise agreement
  `f.winners P = majorityRule.winners P`. -/
theorem may_characterization {Voter : Type*} [Fintype Voter] [DecidableEq Voter]
    (f : ChoiceFunction Voter (Fin 2))
    (hDom : ∀ Q : Profile Voter (Fin 2), Q ∈ f.domain) :
    (ChoiceFunction.Anonymity f ∧ ChoiceFunction.Neutrality f relabelProfile ∧
        ∀ x y : Fin 2, ChoiceFunction.PositiveResponsiveness f x y)
      ↔ ∀ P : Profile Voter (Fin 2),
          f.winners P = (majorityRule (Voter := Voter)).winners P := by
  constructor
  · -- Hard direction: the axioms force `f` to be majority rule.
    rintro ⟨hAnon, hNeut, hPosResp⟩ P
    exact winners_eq_majorityRule f hAnon hNeut hPosResp hDom P
  · -- Easy direction: agreeing with `majorityRule` inherits its axioms (each is stated via
    -- `winners`, so rewriting through the agreement reduces to the `majorityRule_*` lemmas).
    intro hagree
    refine ⟨?_, ?_, ?_⟩
    · intro P _ σ _
      simp only [hagree]
      exact majorityRule_anonymity P (majorityRule_full_domain P) σ (majorityRule_full_domain _)
    · intro P _ τ _
      simp only [hagree]
      exact majorityRule_neutrality P (majorityRule_full_domain P) τ (majorityRule_full_domain _)
    · intro x y P _ hx i R' _ hnlt hlt hcp
      simp only [hagree] at hx ⊢
      exact majorityRule_positiveResponsiveness x y P (majorityRule_full_domain P) hx i R'
        (majorityRule_full_domain _) hnlt hlt hcp

end MajorityRule

end Econlib.SocialChoice
