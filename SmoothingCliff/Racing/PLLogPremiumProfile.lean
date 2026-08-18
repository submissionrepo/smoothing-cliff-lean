import SmoothingCliff.Racing.PLLogPremium

/-!
# Arbitrary-profile wrapper for the logarithmic PL premium

`PLLogPremium.lean` proves the exact bound for a canonical `Option`-indexed
one-leader profile.  This file supplies the finite reindexing step: choose any
highest-valued agent in an arbitrary finite profile, identify the remaining
agents with the `some` coordinates, and transport the genuine PL welfare sum
through that equivalence.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- A finite type is the disjoint union of a distinguished element and the
subtype of all other elements. -/
def optionNeEquiv {ι : Type*} [DecidableEq ι] (top : ι) :
    Option {i : ι // i ≠ top} ≃ ι where
  toFun
    | none => top
    | some i => i.1
  invFun i := if h : i = top then none else some ⟨i, h⟩
  left_inv x := by
    cases x with
    | none => simp
    | some i => simp [i.property]
  right_inv i := by
    by_cases h : i = top <;> simp [h]

/-- Raw one-slot PL probabilities are invariant under finite reindexing. -/
theorem oneSlotPLProbability_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (value : κ → ℝ) (tau : ℝ) (i : ι) :
    oneSlotPLProbability (Finset.univ : Finset ι) (value ∘ e) tau i =
      oneSlotPLProbability (Finset.univ : Finset κ) value tau (e i) := by
  unfold oneSlotPLProbability
  congr 1
  exact e.sum_comp (fun j => Real.exp (value j / tau))

/-- Expected one-slot PL welfare is invariant under finite reindexing. -/
theorem oneSlotPLWelfare_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (value : κ → ℝ) (tau weight : ℝ) :
    oneSlotPLWelfare (Finset.univ : Finset ι) (value ∘ e) tau weight =
      oneSlotPLWelfare (Finset.univ : Finset κ) value tau weight := by
  unfold oneSlotPLWelfare
  congr 1
  calc
    (∑ i : ι, value (e i) *
        oneSlotPLProbability Finset.univ (value ∘ e) tau i) =
      ∑ i : ι, value (e i) *
        oneSlotPLProbability Finset.univ value tau (e i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [oneSlotPLProbability_equiv e value tau i]
    _ = ∑ j : κ, value j *
        oneSlotPLProbability Finset.univ value tau j := by
          exact e.sum_comp
            (fun j => value j *
              oneSlotPLProbability Finset.univ value tau j)

theorem oneLeaderPLValue_eq_comp_optionNeEquiv
    {ι : Type*} [DecidableEq ι] (value : ι → ℝ) (top : ι) (tau : ℝ)
    (htau : tau ≠ 0) :
    oneLeaderPLValue (value top) tau
        (fun i : {j : ι // j ≠ top} =>
          (value top - value i.1) / tau) =
      value ∘ optionNeEquiv top := by
  funext x
  cases x with
  | none => rfl
  | some i =>
      simp only [oneLeaderPLValue, optionNeEquiv, Function.comp_apply]
      field_simp
      change value top - (value top - value i.1) = value i.1
      ring

/-- The paper's logarithmic PL upper bound for every finite profile with at
least two agents, not merely for an already-normalized one-leader family. -/
theorem arbitraryProfile_matched_PL_premium_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → ℝ) (top : ι) (weight sensitivity : ℝ)
    (hcard : 1 < Fintype.card ι)
    (htop : ∀ i, value i ≤ value top)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity) :
    weight * value top -
        oneSlotPLWelfare (Finset.univ : Finset ι) value
          (matchedPLTemperature weight sensitivity) weight ≤
      weight ^ 2 / (2 * sensitivity) *
        max 1 (Real.log ((Fintype.card ι - 1 : ℕ) : ℝ)) := by
  let tau := matchedPLTemperature weight sensitivity
  let gap : {j : ι // j ≠ top} → ℝ :=
    fun i => (value top - value i.1) / tau
  letI : Nonempty {j : ι // j ≠ top} := by
    rcases Fintype.exists_ne_of_one_lt_card hcard top with ⟨j, hj⟩
    exact ⟨⟨j, hj⟩⟩
  have htau : 0 < tau := by
    dsimp [tau, matchedPLTemperature]
    positivity
  have hgap : ∀ i, 0 ≤ gap i := by
    intro i
    exact div_nonneg (sub_nonneg.mpr (htop i.1)) htau.le
  have hbound := matched_oneLeaderPLWelfare_premium_le
    (ι := {j : ι // j ≠ top}) (value top) weight sensitivity gap
      hweight hsensitivity hgap
  have hvalue :
      oneLeaderPLValue (value top) tau gap =
        value ∘ optionNeEquiv top := by
    exact oneLeaderPLValue_eq_comp_optionNeEquiv
      value top tau (ne_of_gt htau)
  have hwelfare :
      oneLeaderPLWelfare (value top) tau weight gap =
        oneSlotPLWelfare (Finset.univ : Finset ι) value tau weight := by
    unfold oneLeaderPLWelfare
    rw [hvalue]
    exact oneSlotPLWelfare_equiv (optionNeEquiv top) value tau weight
  dsimp [tau] at hwelfare ⊢
  rw [← hwelfare]
  convert hbound using 1
  simp only [plLogScale]
  have hcardEq :
      Fintype.card {j : ι // j ≠ top} = Fintype.card ι - 1 :=
    Set.card_ne_eq top
  rw [hcardEq]

end

end SmoothingCliff.Racing
