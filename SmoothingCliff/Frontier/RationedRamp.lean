import SmoothingCliff.Frontier.MeanField

/-!
# The rationed-ramp rule

This file formalizes the mechanism half of Theorem `thm:meanfield` (iii) in
`Smoothing_the_Cliff_ITCS.tex`.  The rule posts the capped-linear ramp
`r_i = clip(S (b_i - t_n), 0, w₁)` and then scales the whole profile down to the
capacity `w₁ K_n` by the common multiplier `min {1, w₁ K_n / Σ_j r_j}`, read as
`1` when the denominator vanishes.

The multiplier is carried by `rationShare`, the one-coordinate branch form of
`rationedResponse` from `MeanField.lean`.  All comparative statics are proved
there, at the level of the scalar scores, and then transported to the interim
rule by the fact that the score is `S`-Lipschitz and monotone in the own bid.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff

noncomputable section

/-! ### The scalar rationing map -/

/-- One coordinate of the rationing map: the score `a` scaled by the paper's
multiplier `min {1, capacity / total}`, written as the branch that makes the
zero-denominator convention explicit. -/
noncomputable def rationShare (capacity a total : ℝ) : ℝ :=
  if total ≤ capacity then a else capacity * a / total

theorem rationedResponse_eq_rationShare {ι : Type*} [Fintype ι]
    (capacity : ℝ) (response : ι → ℝ) (i : ι) :
    rationedResponse capacity response i =
      rationShare capacity (response i) (∑ j, response j) := rfl

theorem rationShare_nonneg {capacity a total : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) :
    0 ≤ rationShare capacity a total := by
  simp only [rationShare]
  split_ifs with h
  · exact ha
  · have hTotal : 0 < total := hCapacity.trans_lt (lt_of_not_ge h)
    exact div_nonneg (mul_nonneg hCapacity ha) hTotal.le

theorem rationShare_le_self {capacity a total : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) :
    rationShare capacity a total ≤ a := by
  simp only [rationShare]
  split_ifs with h
  · exact le_rfl
  · have hlt : capacity < total := lt_of_not_ge h
    have hTotal : 0 < total := hCapacity.trans_lt hlt
    rw [div_le_iff₀ hTotal]
    nlinarith

/-- Raising the own score raises the rationed share: the numerator and the
denominator move together, and `capacity (total - a) / total²  ≥ 0`. -/
theorem rationShare_own_mono {capacity a a' s : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (haa : a ≤ a') (hs : 0 ≤ s) :
    rationShare capacity a (a + s) ≤ rationShare capacity a' (a' + s) := by
  have ha' : 0 ≤ a' := ha.trans haa
  simp only [rationShare]
  rcases le_or_gt (a + s) capacity with h₁ | h₁ <;>
    rcases le_or_gt (a' + s) capacity with h₂ | h₂
  · rw [if_pos h₁, if_pos h₂]
    exact haa
  · rw [if_pos h₁, if_neg (not_le.mpr h₂)]
    have hT' : 0 < a' + s := hCapacity.trans_lt h₂
    rw [le_div_iff₀ hT']
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha',
      mul_le_mul_of_nonneg_right haa hs]
  · exact absurd (le_trans (by linarith) h₂) (not_le.mpr h₁)
  · rw [if_neg (not_le.mpr h₁), if_neg (not_le.mpr h₂)]
    have hT : 0 < a + s := hCapacity.trans_lt h₁
    have hT' : 0 < a' + s := hCapacity.trans_lt h₂
    have hne : a + s ≠ 0 := ne_of_gt hT
    have hne' : a' + s ≠ 0 := ne_of_gt hT'
    have hEq : capacity * a' / (a' + s) - capacity * a / (a + s)
        = capacity * s * (a' - a) / ((a + s) * (a' + s)) := by
      field_simp
      ring
    have hpos : 0 ≤ capacity * s * (a' - a) / ((a + s) * (a' + s)) :=
      div_nonneg (mul_nonneg (mul_nonneg hCapacity hs) (sub_nonneg.mpr haa))
        (mul_pos hT hT').le
    linarith

/-- The rationed share is `1`-Lipschitz in the own score: the increment
`capacity (total - a) / total²` never exceeds one. -/
theorem rationShare_own_lipschitz {capacity a a' s : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (haa : a ≤ a') (hs : 0 ≤ s) :
    rationShare capacity a' (a' + s) - rationShare capacity a (a + s) ≤ a' - a := by
  have ha' : 0 ≤ a' := ha.trans haa
  simp only [rationShare]
  rcases le_or_gt (a + s) capacity with h₁ | h₁ <;>
    rcases le_or_gt (a' + s) capacity with h₂ | h₂
  · rw [if_pos h₁, if_pos h₂]
  · rw [if_pos h₁, if_neg (not_le.mpr h₂)]
    have hT' : 0 < a' + s := hCapacity.trans_lt h₂
    have hkey : capacity * a' / (a' + s) ≤ a' := by
      rw [div_le_iff₀ hT']
      nlinarith
    linarith
  · exact absurd (le_trans (by linarith) h₂) (not_le.mpr h₁)
  · rw [if_neg (not_le.mpr h₁), if_neg (not_le.mpr h₂)]
    have hT : 0 < a + s := hCapacity.trans_lt h₁
    have hT' : 0 < a' + s := hCapacity.trans_lt h₂
    have hne : a + s ≠ 0 := ne_of_gt hT
    have hne' : a' + s ≠ 0 := ne_of_gt hT'
    have hEq : capacity * a' / (a' + s) - capacity * a / (a + s)
        = capacity * s * (a' - a) / ((a + s) * (a' + s)) := by
      field_simp
      ring
    rw [hEq, div_le_iff₀ (mul_pos hT hT')]
    have hprod : capacity * s ≤ (a + s) * (a' + s) :=
      mul_le_mul h₁.le (by linarith) hs (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr haa)]

/-- Raising somebody else's score lowers the rationed share. -/
theorem rationShare_cross_antitone {capacity a c c' rest : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hcc : c ≤ c') :
    rationShare capacity a (c' + rest) ≤ rationShare capacity a (c + rest) := by
  have hc' : 0 ≤ c' := hc.trans hcc
  simp only [rationShare]
  rcases le_or_gt (c + rest) capacity with h₁ | h₁ <;>
    rcases le_or_gt (c' + rest) capacity with h₂ | h₂
  · rw [if_pos h₁, if_pos h₂]
  · rw [if_pos h₁, if_neg (not_le.mpr h₂)]
    have hT' : 0 < c' + rest := hCapacity.trans_lt h₂
    rw [div_le_iff₀ hT']
    nlinarith
  · exact absurd (le_trans (by linarith) h₂) (not_le.mpr h₁)
  · rw [if_neg (not_le.mpr h₁), if_neg (not_le.mpr h₂)]
    have hT : 0 < c + rest := hCapacity.trans_lt h₁
    have hT' : 0 < c' + rest := hCapacity.trans_lt h₂
    have hne : c + rest ≠ 0 := ne_of_gt hT
    have hne' : c' + rest ≠ 0 := ne_of_gt hT'
    have hEq : capacity * a / (c + rest) - capacity * a / (c' + rest)
        = capacity * a * (c' - c) / ((c + rest) * (c' + rest)) := by
      field_simp
      ring
    have hpos : 0 ≤ capacity * a * (c' - c) / ((c + rest) * (c' + rest)) :=
      div_nonneg (mul_nonneg (mul_nonneg hCapacity ha) (sub_nonneg.mpr hcc))
        (mul_pos hT hT').le
    linarith

/-- The cross drop is at most the rise that caused it: `capacity a / total² ≤ 1`. -/
theorem rationShare_cross_lipschitz {capacity a c c' rest : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (hrest : a ≤ rest)
    (hc : 0 ≤ c) (hcc : c ≤ c') :
    rationShare capacity a (c + rest) - rationShare capacity a (c' + rest) ≤ c' - c := by
  have hc' : 0 ≤ c' := hc.trans hcc
  simp only [rationShare]
  rcases le_or_gt (c + rest) capacity with h₁ | h₁ <;>
    rcases le_or_gt (c' + rest) capacity with h₂ | h₂
  · rw [if_pos h₁, if_pos h₂]
    linarith
  · rw [if_pos h₁, if_neg (not_le.mpr h₂)]
    have hT' : 0 < c' + rest := hCapacity.trans_lt h₂
    have hne' : c' + rest ≠ 0 := ne_of_gt hT'
    have hEq : a - capacity * a / (c' + rest)
        = (a * (c' + rest) - capacity * a) / (c' + rest) := by
      field_simp
    rw [hEq, div_le_iff₀ hT']
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha,
      mul_le_mul_of_nonneg_right (show a ≤ c' + rest by linarith)
        (show (0 : ℝ) ≤ c' - c by linarith)]
  · exact absurd (le_trans (by linarith) h₂) (not_le.mpr h₁)
  · rw [if_neg (not_le.mpr h₁), if_neg (not_le.mpr h₂)]
    have hT : 0 < c + rest := hCapacity.trans_lt h₁
    have hT' : 0 < c' + rest := hCapacity.trans_lt h₂
    have hne : c + rest ≠ 0 := ne_of_gt hT
    have hne' : c' + rest ≠ 0 := ne_of_gt hT'
    have hEq : capacity * a / (c + rest) - capacity * a / (c' + rest)
        = capacity * a * (c' - c) / ((c + rest) * (c' + rest)) := by
      field_simp
      ring
    rw [hEq, div_le_iff₀ (mul_pos hT hT')]
    have hprod : capacity * a ≤ (c + rest) * (c' + rest) :=
      mul_le_mul h₁.le (by linarith) ha (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hprod (show (0 : ℝ) ≤ c' - c by linarith)]

/-- The branch form is the paper's multiplier form: on a score that is part of
a nonnegative total, the rationed share is the score times `min {1, M / T}`. -/
theorem rationShare_eq_mul_min {capacity a total : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (hat : a ≤ total) :
    rationShare capacity a total = a * min 1 (capacity / total) := by
  rcases eq_or_lt_of_le (ha.trans hat) with h | h
  · have hzero : total = 0 := h.symm
    have ha0 : a = 0 := le_antisymm (hat.trans hzero.le) ha
    simp [rationShare, hzero, ha0, hCapacity]
  · simp only [rationShare]
    split_ifs with hle
    · rw [min_eq_left ((le_div_iff₀ h).mpr (by linarith)), mul_one]
    · rw [min_eq_right ((div_le_one h).mpr (le_of_not_ge hle))]
      ring

theorem rationShare_own_dist_le {capacity a a' s : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hs : 0 ≤ s) :
    |rationShare capacity a (a + s) - rationShare capacity a' (a' + s)| ≤ |a - a'| := by
  rcases le_total a a' with h | h
  · have hmono := rationShare_own_mono hCapacity ha h hs
    have hlip := rationShare_own_lipschitz hCapacity ha h hs
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have hmono := rationShare_own_mono hCapacity ha' h hs
    have hlip := rationShare_own_lipschitz hCapacity ha' h hs
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

theorem rationShare_cross_dist_le {capacity a c c' rest : ℝ}
    (hCapacity : 0 ≤ capacity) (ha : 0 ≤ a) (hrest : a ≤ rest)
    (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    |rationShare capacity a (c + rest) - rationShare capacity a (c' + rest)| ≤ |c - c'| := by
  rcases le_total c c' with h | h
  · have hanti := rationShare_cross_antitone (rest := rest) hCapacity ha hc h
    have hlip := rationShare_cross_lipschitz hCapacity ha hrest hc h
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have hanti := rationShare_cross_antitone (rest := rest) hCapacity ha hc' h
    have hlip := rationShare_cross_lipschitz hCapacity ha hrest hc' h
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-! ### The posted ramp is monotone in the bid -/

theorem postedRamp_monotone (weight sensitivity : NNReal) (threshold : ℝ) :
    Monotone (postedRamp weight sensitivity threshold) := by
  intro u v huv
  exact clampWeight_monotone weight
    (mul_le_mul_of_nonneg_left (sub_le_sub_right huv threshold) sensitivity.coe_nonneg)

theorem postedRamp_dist_le (weight sensitivity : NNReal) (threshold u v : ℝ) :
    |postedRamp weight sensitivity threshold u -
        postedRamp weight sensitivity threshold v| ≤ (sensitivity : ℝ) * |u - v| := by
  simpa [Real.dist_eq] using
    (postedRamp_lipschitz weight sensitivity threshold).dist_le_mul u v

/-! ### The rule -/

variable {ι : Type*} [Fintype ι] {reserve : ℝ}

/-- **The rationed-ramp rule** `x^{RR}` of Theorem `thm:meanfield` (iii). -/
noncomputable def rationedRampRule (weight sensitivity : NNReal)
    (capacity threshold : ℝ) : InterimRule ι reserve := fun b i =>
  rationedResponse capacity
    (fun j => postedRamp weight sensitivity threshold ((b j : EligibleBid reserve) : ℝ)) i

theorem rationedRampRule_apply (weight sensitivity : NNReal) (capacity threshold : ℝ)
    (b : EligibleProfile ι reserve) (i : ι) :
    rationedRampRule weight sensitivity capacity threshold b i
      = rationShare capacity
          (postedRamp weight sensitivity threshold ((b i : EligibleBid reserve) : ℝ))
          (∑ j, postedRamp weight sensitivity threshold
            ((b j : EligibleBid reserve) : ℝ)) := rfl

/-- The rule in the paper's own notation: the posted ramp times the common
multiplier `min {1, w₁ K_n / Σ_j r_j}`. -/
theorem rationedRampRule_eq_mul_min (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (b : EligibleProfile ι reserve) (i : ι) :
    rationedRampRule weight sensitivity capacity threshold b i
      = postedRamp weight sensitivity threshold ((b i : EligibleBid reserve) : ℝ)
        * min 1 (capacity / ∑ j, postedRamp weight sensitivity threshold
            ((b j : EligibleBid reserve) : ℝ)) := by
  rw [rationedRampRule_apply]
  exact rationShare_eq_mul_min hCapacity (postedRamp_nonneg _ _ _ _)
    (Finset.single_le_sum (f := fun k => postedRamp weight sensitivity threshold
        ((b k : EligibleBid reserve) : ℝ))
      (fun _ _ => postedRamp_nonneg _ _ _ _) (Finset.mem_univ i))

theorem rationedRampRule_nonneg (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (b : EligibleProfile ι reserve) (i : ι) :
    0 ≤ rationedRampRule weight sensitivity capacity threshold b i :=
  rationShare_nonneg hCapacity (postedRamp_nonneg _ _ _ _)

theorem rationedRampRule_le_weight (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (b : EligibleProfile ι reserve) (i : ι) :
    rationedRampRule weight sensitivity capacity threshold b i ≤ (weight : ℝ) :=
  (rationShare_le_self hCapacity (postedRamp_nonneg _ _ _ _)).trans
    (postedRamp_le _ _ _ _)

/-- The rationed-ramp rule never oversubscribes the capacity. -/
theorem rationedRampRule_total_le (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (b : EligibleProfile ι reserve) :
    ∑ i, rationedRampRule weight sensitivity capacity threshold b i ≤ capacity :=
  rationedResponse_total_le capacity _ hCapacity

theorem rationedRampRule_anonymous (weight sensitivity : NNReal)
    (capacity threshold : ℝ) :
    Anonymous (rationedRampRule (ι := ι) (reserve := reserve)
      weight sensitivity capacity threshold) := by
  intro π b i
  simp only [rationedRampRule, rationedResponse, relabelProfile]
  have hsum : ∑ j, postedRamp weight sensitivity threshold
        ((b (π.symm j) : EligibleBid reserve) : ℝ)
      = ∑ j, postedRamp weight sensitivity threshold
        ((b j : EligibleBid reserve) : ℝ) :=
    Equiv.sum_comp π.symm
      (fun j => postedRamp weight sensitivity threshold ((b j : EligibleBid reserve) : ℝ))
  rw [hsum]
  simp

/-! ### Comparative statics of the rule -/

variable [DecidableEq ι]

theorem sum_postedRamp_update (weight sensitivity : NNReal) (threshold : ℝ)
    (b : EligibleProfile ι reserve) (i : ι) (z : EligibleBid reserve) :
    ∑ k, postedRamp weight sensitivity threshold
        (((updateBid b i z) k : EligibleBid reserve) : ℝ)
      = postedRamp weight sensitivity threshold ((z : EligibleBid reserve) : ℝ)
        + ∑ k ∈ Finset.univ.erase i, postedRamp weight sensitivity threshold
            ((b k : EligibleBid reserve) : ℝ) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [updateBid]
  · exact Finset.sum_congr rfl fun k hk => by
      simp [updateBid, (Finset.mem_erase.mp hk).1]

/-- Own-coordinate normal form: the numerator and the denominator both move by
the own score. -/
theorem rationedRampRule_update_self (weight sensitivity : NNReal)
    (capacity threshold : ℝ) (b : EligibleProfile ι reserve) (i : ι)
    (z : EligibleBid reserve) :
    rationedRampRule weight sensitivity capacity threshold (updateBid b i z) i
      = rationShare capacity
          (postedRamp weight sensitivity threshold ((z : EligibleBid reserve) : ℝ))
          (postedRamp weight sensitivity threshold ((z : EligibleBid reserve) : ℝ)
            + ∑ k ∈ Finset.univ.erase i, postedRamp weight sensitivity threshold
                ((b k : EligibleBid reserve) : ℝ)) := by
  rw [rationedRampRule_apply, sum_postedRamp_update]
  simp only [updateBid, Function.update_self]

/-- Cross-coordinate normal form: only the denominator moves. -/
theorem rationedRampRule_update_other (weight sensitivity : NNReal)
    (capacity threshold : ℝ) (b : EligibleProfile ι reserve) {i j : ι} (hij : i ≠ j)
    (z : EligibleBid reserve) :
    rationedRampRule weight sensitivity capacity threshold (updateBid b j z) i
      = rationShare capacity
          (postedRamp weight sensitivity threshold ((b i : EligibleBid reserve) : ℝ))
          (postedRamp weight sensitivity threshold ((z : EligibleBid reserve) : ℝ)
            + ∑ k ∈ Finset.univ.erase j, postedRamp weight sensitivity threshold
                ((b k : EligibleBid reserve) : ℝ)) := by
  rw [rationedRampRule_apply, sum_postedRamp_update]
  simp only [updateBid, Function.update_of_ne hij]

theorem sum_erase_postedRamp_nonneg (weight sensitivity : NNReal) (threshold : ℝ)
    (b : EligibleProfile ι reserve) (i : ι) :
    0 ≤ ∑ k ∈ Finset.univ.erase i, postedRamp weight sensitivity threshold
        ((b k : EligibleBid reserve) : ℝ) :=
  Finset.sum_nonneg fun _ _ => postedRamp_nonneg _ _ _ _

theorem postedRamp_le_sum_erase (weight sensitivity : NNReal) (threshold : ℝ)
    (b : EligibleProfile ι reserve) {i j : ι} (hij : i ≠ j) :
    postedRamp weight sensitivity threshold ((b i : EligibleBid reserve) : ℝ)
      ≤ ∑ k ∈ Finset.univ.erase j, postedRamp weight sensitivity threshold
          ((b k : EligibleBid reserve) : ℝ) :=
  Finset.single_le_sum (f := fun k => postedRamp weight sensitivity threshold
      ((b k : EligibleBid reserve) : ℝ))
    (fun _ _ => postedRamp_nonneg _ _ _ _)
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

theorem rationedRampRule_ownMonotone (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) :
    OwnMonotone (rationedRampRule (ι := ι) (reserve := reserve)
      weight sensitivity capacity threshold) := by
  intro b i z w hzw
  dsimp only
  rw [rationedRampRule_update_self, rationedRampRule_update_self]
  exact rationShare_own_mono hCapacity (postedRamp_nonneg _ _ _ _)
    (postedRamp_monotone weight sensitivity threshold hzw)
    (sum_erase_postedRamp_nonneg weight sensitivity threshold b i)

theorem rationedRampRule_ownLipschitz (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) :
    OwnLipschitz sensitivity (rationedRampRule (ι := ι) (reserve := reserve)
      weight sensitivity capacity threshold) := by
  intro b i
  apply LipschitzWith.of_dist_le_mul
  intro z w
  dsimp only
  rw [Real.dist_eq, rationedRampRule_update_self, rationedRampRule_update_self]
  have hd : dist z w = |((z : EligibleBid reserve) : ℝ)
      - ((w : EligibleBid reserve) : ℝ)| := by
    simp [Subtype.dist_eq, Real.dist_eq]
  rw [hd]
  refine (rationShare_own_dist_le hCapacity (postedRamp_nonneg _ _ _ _)
    (postedRamp_nonneg _ _ _ _)
    (sum_erase_postedRamp_nonneg weight sensitivity threshold b i)).trans ?_
  exact postedRamp_dist_le weight sensitivity threshold _ _

theorem rationedRampRule_crossMonotone (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity) :
    CrossMonotone (rationedRampRule (ι := ι) (reserve := reserve)
      weight sensitivity capacity threshold) := by
  intro b i j hij z w hzw
  dsimp only
  rw [rationedRampRule_update_other _ _ _ _ _ hij,
    rationedRampRule_update_other _ _ _ _ _ hij]
  exact rationShare_cross_antitone hCapacity (postedRamp_nonneg _ _ _ _)
    (postedRamp_nonneg _ _ _ _)
    (postedRamp_monotone weight sensitivity threshold hzw)

/-- The rule is `S`-Lipschitz in every eligible coordinate, not only the own
one: this is the cross half of the Lipschitz claim in `thm:meanfield` (iii). -/
theorem rationedRampRule_crossLipschitz (weight sensitivity : NNReal) {capacity : ℝ}
    (threshold : ℝ) (hCapacity : 0 ≤ capacity)
    (b : EligibleProfile ι reserve) {i j : ι} (hij : i ≠ j)
    (z w : EligibleBid reserve) :
    |rationedRampRule weight sensitivity capacity threshold (updateBid b j z) i -
        rationedRampRule weight sensitivity capacity threshold (updateBid b j w) i|
      ≤ (sensitivity : ℝ) * |((z : EligibleBid reserve) : ℝ)
          - ((w : EligibleBid reserve) : ℝ)| := by
  rw [rationedRampRule_update_other _ _ _ _ _ hij,
    rationedRampRule_update_other _ _ _ _ _ hij]
  refine (rationShare_cross_dist_le hCapacity (postedRamp_nonneg _ _ _ _)
    (postedRamp_le_sum_erase weight sensitivity threshold b hij)
    (postedRamp_nonneg _ _ _ _) (postedRamp_nonneg _ _ _ _)).trans ?_
  exact postedRamp_dist_le weight sensitivity threshold _ _

/-! ### Finite-law achievability

The benchmark `V*` of Theorem `thm:meanfield` is the population programme run
on the ex-ante distribution of an agent's value: draw a state, then draw an
agent uniformly.  `pooledLaw` is exactly that distribution, so the finite-law
programme value over `Ω × ι` is the paper's `V*(W̄_n)` and the per-capita
welfare of a state-contingent rule is a `finiteCurveWelfare` over the same
space.  No extra bridge is needed to compare them.
-/

omit [DecidableEq ι]

/-- The ex-ante population law: draw a state from `law`, then an agent
uniformly. -/
noncomputable def pooledLaw {Ω : Type*} [Fintype Ω] [Nonempty ι]
    (law : FiniteLaw Ω) : FiniteLaw (Ω × ι) where
  probability := fun p => law.probability p.1 / (Fintype.card ι : ℝ)
  probability_nonneg := fun p =>
    div_nonneg (law.probability_nonneg p.1) (Nat.cast_nonneg _)
  probability_sum := by
    have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [Fintype.sum_prod_type]
    calc (∑ ω : Ω, ∑ _i : ι, law.probability ω / (Fintype.card ι : ℝ))
        = ∑ ω : Ω, law.probability ω := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
      _ = 1 := law.probability_sum

theorem finiteExpectation_pooledLaw {Ω : Type*} [Fintype Ω] [Nonempty ι]
    (law : FiniteLaw Ω) (f : Ω × ι → ℝ) :
    finiteExpectation (pooledLaw (ι := ι) law) f
      = finiteExpectation law (fun ω => ∑ i, f (ω, i)) / (Fintype.card ι : ℝ) := by
  simp only [finiteExpectation, pooledLaw]
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem finiteCurveMass_pooledLaw {Ω : Type*} [Fintype Ω] [Nonempty ι]
    (law : FiniteLaw Ω) (ξ : Ω × ι → ℝ) :
    finiteCurveMass (pooledLaw (ι := ι) law) ξ
      = finiteExpectation law (fun ω => ∑ i, ξ (ω, i)) / (Fintype.card ι : ℝ) :=
  finiteExpectation_pooledLaw law ξ

theorem finiteCurveWelfare_pooledLaw {Ω : Type*} [Fintype Ω] [Nonempty ι]
    (law : FiniteLaw Ω) (value ξ : Ω × ι → ℝ) :
    finiteCurveWelfare (pooledLaw (ι := ι) law) value ξ
      = finiteExpectation law (fun ω => ∑ i, value (ω, i) * ξ (ω, i))
        / (Fintype.card ι : ℝ) :=
  finiteExpectation_pooledLaw law (fun p => value p * ξ p)

theorem finiteExpectation_sub {Ω : Type*} [Fintype Ω]
    (law : FiniteLaw Ω) (f g : Ω → ℝ) :
    finiteExpectation law (fun ω => f ω - g ω)
      = finiteExpectation law f - finiteExpectation law g := by
  unfold finiteExpectation
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- The truthful eligible profile in state `ω`. -/
def truthfulProfile {Ω : Type*} (value : Ω → ι → ℝ)
    (hEligible : ∀ ω i, reserve ≤ value ω i) (ω : Ω) : EligibleProfile ι reserve :=
  fun i => ⟨value ω i, hEligible ω i⟩

theorem welfare_rationedRampRule_truthful {Ω : Type*} (value : Ω → ι → ℝ)
    (hEligible : ∀ ω i, reserve ≤ value ω i)
    (weight sensitivity : NNReal) (capacity threshold : ℝ) (ω : Ω) :
    welfare (rationedRampRule (reserve := reserve) weight sensitivity capacity threshold)
        (truthfulProfile value hEligible ω)
      = ∑ i, value ω i * rationedResponse capacity
          (fun j => postedRamp weight sensitivity threshold (value ω j)) i := rfl

/-- **Achievability.**  If the posted threshold clears the capacity in
expectation, the rationed-ramp rule loses at most `b̄ w₁ / (4 √n)` per capita
against the population-programme benchmark run on the ex-ante value
distribution. -/
theorem rationedRampRule_finiteLaw_achievability {Ω : Type*} [Fintype Ω] [Nonempty ι]
    (law : FiniteLaw Ω) (value : Ω → ι → ℝ)
    (hEligible : ∀ ω i, reserve ≤ value ω i)
    (weight sensitivity : NNReal) (capacity threshold upperValue : ℝ)
    (hCapacity : 0 ≤ capacity) (hUpper : 0 ≤ upperValue)
    (hValueNonneg : ∀ ω i, 0 ≤ value ω i)
    (hValueLe : ∀ ω i, value ω i ≤ upperValue)
    (hThreshold : threshold ≤ upperValue)
    (hClears : finiteExpectation law
      (fun ω => ∑ i, postedRamp weight sensitivity threshold (value ω i)) = capacity)
    (hSecond : finiteExpectation law
      (fun ω => ((∑ i, postedRamp weight sensitivity threshold (value ω i)) - capacity) ^ 2)
        ≤ (Fintype.card ι : ℝ) * (weight : ℝ) ^ 2 / 4) :
    finitePopulationValue (pooledLaw (ι := ι) law) (fun p => value p.1 p.2)
        weight sensitivity (capacity / (Fintype.card ι : ℝ))
      - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
    ≤ finiteExpectation law (fun ω =>
        welfare (rationedRampRule (reserve := reserve) weight sensitivity capacity threshold)
          (truthfulProfile value hEligible ω)) / (Fintype.card ι : ℝ) := by
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hRampMass : finiteCurveMass (pooledLaw (ι := ι) law)
      (fun p : Ω × ι => postedRamp weight sensitivity threshold (value p.1 p.2))
      = capacity / (Fintype.card ι : ℝ) := by
    have h : finiteCurveMass (pooledLaw (ι := ι) law)
        (fun p : Ω × ι => postedRamp weight sensitivity threshold (value p.1 p.2))
        = finiteExpectation law
            (fun ω => ∑ i, postedRamp weight sensitivity threshold (value ω i))
          / (Fintype.card ι : ℝ) := finiteCurveMass_pooledLaw law _
    rw [h, hClears]
  have hValueEq := finitePopulationValue_eq_postedRamp (pooledLaw (ι := ι) law)
    (fun p : Ω × ι => value p.1 p.2) weight sensitivity
    (capacity / (Fintype.card ι : ℝ)) threshold upperValue
    (fun p => hValueNonneg p.1 p.2) (fun p => hValueLe p.1 p.2) hUpper hThreshold
    hRampMass
  have hBenchmark : finitePopulationValue (pooledLaw (ι := ι) law)
      (fun p : Ω × ι => value p.1 p.2) weight sensitivity
        (capacity / (Fintype.card ι : ℝ))
      = finiteExpectation law
          (fun ω => ∑ i, value ω i *
            postedRamp weight sensitivity threshold (value ω i))
        / (Fintype.card ι : ℝ) := by
    rw [hValueEq]
    exact finiteCurveWelfare_pooledLaw law _ _
  have hrate := finite_rationing_perCapita_rate law value
    (fun ω i => postedRamp weight sensitivity threshold (value ω i))
    capacity upperValue (weight : ℝ) (Fintype.card ι) hnpos hCapacity hUpper
    weight.coe_nonneg hValueLe (fun _ _ => postedRamp_nonneg _ _ _ _) hClears hSecond
  have hrate' : finiteExpectation law
        (fun ω => (∑ i, value ω i *
            postedRamp weight sensitivity threshold (value ω i)) -
          ∑ i, value ω i * rationedResponse capacity
            (fun j => postedRamp weight sensitivity threshold (value ω j)) i)
        / (Fintype.card ι : ℝ)
      ≤ upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι)) := hrate
  rw [finiteExpectation_sub, sub_div] at hrate'
  have hwelfare : finiteExpectation law (fun ω =>
        welfare (rationedRampRule (reserve := reserve) weight sensitivity capacity threshold)
          (truthfulProfile value hEligible ω))
      = finiteExpectation law (fun ω => ∑ i, value ω i * rationedResponse capacity
          (fun j => postedRamp weight sensitivity threshold (value ω j)) i) := rfl
  rw [hBenchmark, hwelfare]
  linarith

end

end SmoothingCliff.Frontier
