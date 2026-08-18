import SmoothingCliff.Frontier.NoPointwiseOptimum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# The paper's second rank rule

Theorem `thm:impossibility` needs a second globally defined rule in `C`, one
that gives each tied leader at `R₂` the weight `W/n + (n-1)/n · S δ`.  The
paper builds it from the rank coefficients

  `α₁ = β := (n-1) S / n`,  `α_k = 2 β (n-k) / (k (n-2))`  for `2 ≤ k ≤ n-1`,

whose own slopes depend on the mover's rank, so unlike rule A it is not affine
in the scores.  This file writes it as a level density instead: at each level
`t` the agents above `t` share a gain and the agents below pay a loss, with
coefficients depending only on how many agents are above `t`.  Raising one bid
changes that density only on the level interval the bid crosses, which turns
every class property into a scalar monotonicity statement about the
coefficient profile.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- How many scores sit at or above the level `t`. -/
def levelCount (y : ι → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun j => t ≤ y j).card

theorem levelCount_le (y : ι → ℝ) (t : ℝ) : levelCount y t ≤ Fintype.card ι := by
  simpa [levelCount, Finset.card_univ] using
    Finset.card_le_card (Finset.filter_subset (fun j => t ≤ y j) Finset.univ)

theorem levelCount_eq_card_of_le (y : ι → ℝ) (t : ℝ) (h : ∀ j, t ≤ y j) :
    levelCount y t = Fintype.card ι := by
  simp [levelCount, Finset.filter_true_of_mem fun j _ => h j, Finset.card_univ]

theorem levelCount_eq_zero_of_lt (y : ι → ℝ) (t : ℝ) (h : ∀ j, y j < t) :
    levelCount y t = 0 := by
  simp only [levelCount, Finset.card_eq_zero]
  apply Finset.filter_false_of_mem
  intro j _
  exact not_le.mpr (h j)

/-- The real-valued count, used only to get measurability in `t`. -/
def levelCountReal (y : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ j, (if t ≤ y j then (1 : ℝ) else 0)

theorem levelCountReal_eq (y : ι → ℝ) (t : ℝ) :
    levelCountReal y t = (levelCount y t : ℝ) := by
  simp [levelCountReal, levelCount]

theorem measurable_levelCountReal (y : ι → ℝ) : Measurable (levelCountReal y) := by
  apply Finset.measurable_sum
  intro j _
  have h : (fun t => if t ≤ y j then (1 : ℝ) else 0)
      = Set.indicator (Set.Iic (y j)) (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : t ≤ y j <;> simp [Set.indicator, ht]
  rw [h]
  exact measurable_const.indicator measurableSet_Iic

theorem measurable_levelCount (y : ι → ℝ) : Measurable (levelCount y) := by
  have h : levelCount y = fun t => ⌊levelCountReal y t⌋₊ := by
    funext t
    rw [levelCountReal_eq, Nat.floor_natCast]
  rw [h]
  exact Nat.measurable_floor.comp (measurable_levelCountReal y)

/-- The level coefficient `κ`: zero when nobody is above the level, `S/n` at a
lone leader, and the constant `C = 2β/(n-2)` from rank two down. -/
def levelCoeff (n : ℕ) (sens : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else if k = 1 then sens / n
  else 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2))

/-- The level density of agent `i`: the agents at or above `t` share the gain
`κ · n/k`, everybody pays `κ`. -/
def levelDensity (n : ℕ) (sens : ℝ) (y : ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  levelCoeff n sens (levelCount y t) *
    ((n : ℝ) * (if t ≤ y i then (1 : ℝ) else 0) / (levelCount y t : ℝ) - 1)

/-! ### The coefficient profile

Everything the class properties need about rule B is contained in three scalar
statements: the loss coefficient `κ` is non-decreasing, the gain profile
`κ k (n/k - 1)` is non-increasing, and the own slope `κ r (n/r - 1) + κ (r-1)`
stays in `[0, S]`.  The last one is where `n ≥ 4` is used. -/

section Coeff

variable {n : ℕ} {sens : ℝ}

/-- The gain of an agent at or above a level with `k` agents above it. -/
def levelGain (n : ℕ) (sens : ℝ) (k : ℕ) : ℝ :=
  levelCoeff n sens k * ((n : ℝ) / k - 1)

theorem levelCoeff_zero (n : ℕ) (sens : ℝ) : levelCoeff n sens 0 = 0 := by
  simp [levelCoeff]

theorem levelCoeff_one (n : ℕ) (sens : ℝ) : levelCoeff n sens 1 = sens / n := by
  simp [levelCoeff]

theorem levelCoeff_of_two_le {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (sens : ℝ) :
    levelCoeff n sens k = 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2)) := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [levelCoeff, h0, h1]

theorem levelCoeff_nonneg (hn : 4 ≤ n) (hs : 0 ≤ sens) (k : ℕ) :
    0 ≤ levelCoeff n sens k := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [levelCoeff]
    · rw [levelCoeff_one]; positivity
  · rw [levelCoeff_of_two_le hk]
    apply div_nonneg
    · nlinarith
    · nlinarith

/-- The loss coefficient is at most `S`; this is `2(n-1) ≤ n(n-2)`, i.e. `n ≥ 4`. -/
theorem levelCoeff_le (hn : 4 ≤ n) (hs : 0 ≤ sens) (k : ℕ) :
    levelCoeff n sens k ≤ sens := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simpa [levelCoeff] using hs
    · rw [levelCoeff_one, div_le_iff₀ hnpos]; nlinarith
  · rw [levelCoeff_of_two_le hk,
      div_le_iff₀ (by nlinarith : (0:ℝ) < (n:ℝ) * ((n:ℝ) - 2))]
    nlinarith [mul_nonneg hs (by nlinarith : (0:ℝ) ≤ (n:ℝ)^2 - 4*(n:ℝ) + 2)]

/-- `κ` is non-decreasing below the top level. -/
theorem levelCoeff_mono (hn : 4 ≤ n) (hs : 0 ≤ sens) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k ≤ l) : levelCoeff n sens k ≤ levelCoeff n sens l := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 2) := by nlinarith
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · have hl1 : l = 1 := by omega
      subst hl1
      exact le_rfl
    · rw [levelCoeff_one, levelCoeff_of_two_le hl2, div_le_div_iff₀ hnpos hnn2]
      nlinarith [mul_nonneg (mul_nonneg hs hnpos.le) hnpos.le]
  · have hl2 : 2 ≤ l := le_trans hk2 hkl
    rw [levelCoeff_of_two_le hk2, levelCoeff_of_two_le hl2]

/-- The gain profile is non-increasing; the tight step is `α₂ = α₁`. -/
theorem levelGain_antitone (hn : 4 ≤ n) (hs : 0 ≤ sens) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k ≤ l) : levelGain n sens l ≤ levelGain n sens k := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 2) := by nlinarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn2ne : ((n : ℝ) - 2) ≠ 0 := by intro h; nlinarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hl1 : 1 ≤ l := le_trans hk hkl
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  have hklR : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hCnonneg : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2)) := by
    apply div_nonneg (by nlinarith) hnn2.le
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by omega
    subst hk1
    have hbeta : levelGain n sens 1 = ((n : ℝ) - 1) * sens / n := by
      rw [levelGain, levelCoeff_one]
      field_simp
      ring
    rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · have hl1' : l = 1 := by omega
      subst hl1'
      exact le_rfl
    · have hl2R : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      have hstep : (n : ℝ) / l - 1 ≤ ((n : ℝ) - 2) / 2 := by
        have h2l : (n : ℝ) / l ≤ (n : ℝ) / 2 :=
          div_le_div_of_nonneg_left (by linarith) (by norm_num) hl2R
        have : (n : ℝ) / 2 - 1 = ((n : ℝ) - 2) / 2 := by ring
        linarith
      have hmul := mul_le_mul_of_nonneg_left hstep hCnonneg
      have hCbeta : 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2))
            * (((n : ℝ) - 2) / 2) = ((n : ℝ) - 1) * sens / n := by
        field_simp
      rw [hbeta, levelGain, levelCoeff_of_two_le hl2]
      rw [hCbeta] at hmul
      exact hmul
  · have hl2 : 2 ≤ l := le_trans hk2 hkl
    have hfrac : (n : ℝ) / l - 1 ≤ (n : ℝ) / k - 1 := by
      have : (n : ℝ) / l ≤ (n : ℝ) / k :=
        div_le_div_of_nonneg_left (by linarith) hkpos hklR
      linarith
    rw [levelGain, levelGain, levelCoeff_of_two_le hk2, levelCoeff_of_two_le hl2]
    exact mul_le_mul_of_nonneg_left hfrac hCnonneg

theorem levelGain_nonneg (hn : 4 ≤ n) (hs : 0 ≤ sens) {k : ℕ} (hk : k ≤ n) :
    0 ≤ levelGain n sens k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · simp [levelGain, hk0, levelCoeff]
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    apply mul_nonneg (levelCoeff_nonneg hn hs k)
    rw [sub_nonneg, le_div_iff₀ hkR]
    linarith

end Coeff

/-! ### The level density -/

section Density

variable {n : ℕ} {sens : ℝ}

theorem levelDensity_of_not_le (y : ι → ℝ) (i : ι) {t : ℝ} (h : ¬ t ≤ y i) :
    levelDensity n sens y i t = -levelCoeff n sens (levelCount y t) := by
  simp [levelDensity, h]

theorem levelCount_pos_of_le (y : ι → ℝ) (i : ι) {t : ℝ} (h : t ≤ y i) :
    0 < levelCount y t := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [h]⟩

theorem levelDensity_of_le (y : ι → ℝ) (i : ι) {t : ℝ} (h : t ≤ y i) :
    levelDensity n sens y i t = levelGain n sens (levelCount y t) := by
  simp [levelDensity, levelGain, h]

theorem levelDensity_le (hn : 4 ≤ n) (hs : 0 ≤ sens) (hcard : Fintype.card ι = n)
    (y : ι → ℝ) (i : ι) (t : ℝ) : levelDensity n sens y i t ≤ sens := by
  by_cases h : t ≤ y i
  · rw [levelDensity_of_le y i h, levelGain]
    have hle : levelCount y t ≤ n := hcard ▸ levelCount_le y t
    have hpos : 0 < levelCount y t := levelCount_pos_of_le y i h
    have hposR : (0 : ℝ) < levelCount y t := by exact_mod_cast hpos
    have hleR : ((levelCount y t : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    have h1 : (n : ℝ) / (levelCount y t : ℝ) - 1 ≤ (n : ℝ) - 1 := by
      have hone : (1 : ℝ) ≤ (levelCount y t : ℝ) := by exact_mod_cast hpos
      have : (n : ℝ) / (levelCount y t : ℝ) ≤ (n : ℝ) := by
        rw [div_le_iff₀ hposR]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    -- the gain never exceeds `β ≤ S`
    have hgain : levelGain n sens (levelCount y t) ≤ levelGain n sens 1 :=
      levelGain_antitone hn hs (le_refl 1) hpos
    have hbeta : levelGain n sens 1 ≤ sens := by
      have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < n := by linarith
      rw [levelGain, levelCoeff_one]
      rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
      have : (n : ℝ) / (1 : ℕ) - 1 = (n : ℝ) - 1 := by norm_num
      rw [this]
      nlinarith
    rw [levelGain] at hgain
    linarith [hgain, hbeta]
  · rw [levelDensity_of_not_le y i h]
    have := levelCoeff_nonneg (n := n) (sens := sens) hn hs (levelCount y t)
    linarith

theorem neg_sens_le_levelDensity (hn : 4 ≤ n) (hs : 0 ≤ sens)
    (hcard : Fintype.card ι = n) (y : ι → ℝ) (i : ι) (t : ℝ) :
    -sens ≤ levelDensity n sens y i t := by
  by_cases h : t ≤ y i
  · rw [levelDensity_of_le y i h]
    have hle : levelCount y t ≤ n := hcard ▸ levelCount_le y t
    have := levelGain_nonneg (n := n) (sens := sens) hn hs (k := levelCount y t) hle
    linarith
  · rw [levelDensity_of_not_le y i h]
    have := levelCoeff_le (n := n) (sens := sens) hn hs (levelCount y t)
    linarith

theorem abs_levelDensity_le (hn : 4 ≤ n) (hs : 0 ≤ sens) (hcard : Fintype.card ι = n)
    (y : ι → ℝ) (i : ι) (t : ℝ) : |levelDensity n sens y i t| ≤ sens :=
  abs_le.mpr ⟨neg_sens_le_levelDensity hn hs hcard y i t, levelDensity_le hn hs hcard y i t⟩

/-- At every level the gains and the losses cancel. -/
theorem levelDensity_sum (hcard : Fintype.card ι = n) (sens : ℝ) (y : ι → ℝ) (t : ℝ) :
    ∑ i, levelDensity n sens y i t = 0 := by
  classical
  unfold levelDensity
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos (levelCount y t) with h0 | hpos
  · simp [h0, levelCoeff]
  · have hposR : (0 : ℝ) < levelCount y t := by exact_mod_cast hpos
    have hind : ∑ i, ((n : ℝ) * (if t ≤ y i then (1 : ℝ) else 0)
          / (levelCount y t : ℝ) - 1) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
      have h1 : ∑ i, (if t ≤ y i then (1 : ℝ) else 0) = (levelCount y t : ℝ) := by
        rw [← levelCountReal_eq]; rfl
      rw [h1, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one,
        mul_div_assoc, div_self (ne_of_gt hposR), mul_one, sub_self]
    rw [hind, mul_zero]

theorem measurable_levelDensity (n : ℕ) (sens : ℝ) (y : ι → ℝ) (i : ι) :
    Measurable (levelDensity n sens y i) := by
  have hcoeff : Measurable (fun k : ℕ => levelCoeff n sens k) := measurable_from_top
  have h1 : Measurable fun t => levelCoeff n sens (levelCount y t) :=
    hcoeff.comp (measurable_levelCount y)
  have h2 : Measurable fun t : ℝ => (if t ≤ y i then (1 : ℝ) else 0) := by
    have : (fun t : ℝ => if t ≤ y i then (1 : ℝ) else 0)
        = Set.indicator (Set.Iic (y i)) (fun _ => (1 : ℝ)) := by
      funext t
      by_cases ht : t ≤ y i <;> simp [Set.indicator, ht]
    rw [this]
    exact measurable_const.indicator measurableSet_Iic
  have h3 : Measurable fun t : ℝ => ((levelCount y t : ℕ) : ℝ) := by
    have heq : (fun t : ℝ => ((levelCount y t : ℕ) : ℝ)) = levelCountReal y := by
      funext t
      rw [levelCountReal_eq]
    rw [heq]
    exact measurable_levelCountReal y
  exact h1.mul (((measurable_const.mul h2).div h3).sub measurable_const)

theorem levelDensity_intervalIntegrable (hn : 4 ≤ n) (hs : 0 ≤ sens)
    (hcard : Fintype.card ι = n) (y : ι → ℝ) (i : ι) (a b : ℝ) :
    IntervalIntegrable (levelDensity n sens y i) MeasureTheory.volume a b := by
  constructor <;>
  · apply MeasureTheory.Measure.integrableOn_of_bounded (M := sens)
      (by simp) (measurable_levelDensity n sens y i).aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs]
    exact abs_levelDensity_le hn hs hcard y i t

end Density

/-! ### How one coordinate moves the density

Raising one score changes the level density only on the level interval the
score crossed.  On that interval the mover's own increment is the own slope
`κ r (n/r - 1) + κ (r-1)`, which lies in `[0, S]`, and every other agent's
increment is nonpositive by the two monotonicity facts. -/

section Update

variable [DecidableEq ι] {n : ℕ} {sens : ℝ}

theorem levelCount_update_of_le (y : ι → ℝ) (i : ι) {z t : ℝ} (hz : y i ≤ z)
    (ht : t ≤ y i) : levelCount (Function.update y i z) t = levelCount y t := by
  classical
  unfold levelCount
  congr 1
  apply Finset.filter_congr
  intro j _
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    constructor <;> intro _
    · exact ht
    · linarith
  · simp [Function.update_of_ne hj]

theorem levelCount_update_of_gt (y : ι → ℝ) (i : ι) {z t : ℝ} (hz : y i ≤ z)
    (ht : z < t) : levelCount (Function.update y i z) t = levelCount y t := by
  classical
  unfold levelCount
  congr 1
  apply Finset.filter_congr
  intro j _
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    constructor <;> intro h
    · linarith
    · linarith
  · simp [Function.update_of_ne hj]

theorem levelCount_update_mid (y : ι → ℝ) (i : ι) {z t : ℝ} (h1 : y i < t)
    (h2 : t ≤ z) :
    levelCount (Function.update y i z) t = levelCount y t + 1 := by
  classical
  have hset : (Finset.univ.filter fun j => t ≤ Function.update y i z j)
      = insert i (Finset.univ.filter fun j => t ≤ y j) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self, h2]
    · simp [hj]
  have hnot : i ∉ (Finset.univ.filter fun j => t ≤ y j) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_le.mpr h1
  unfold levelCount
  rw [hset, Finset.card_insert_of_notMem hnot]

theorem levelDensity_update_of_le (y : ι → ℝ) (i j : ι) {z t : ℝ} (hz : y i ≤ z)
    (ht : t ≤ y i) :
    levelDensity n sens (Function.update y i z) j t = levelDensity n sens y j t := by
  classical
  unfold levelDensity
  rw [levelCount_update_of_le y i hz ht]
  by_cases hj : j = i
  · subst hj
    have htz : t ≤ z := le_trans ht hz
    simp [Function.update_self, ht, htz]
  · rw [Function.update_of_ne hj]

theorem levelDensity_update_of_gt (y : ι → ℝ) (i j : ι) {z t : ℝ} (hz : y i ≤ z)
    (ht : z < t) :
    levelDensity n sens (Function.update y i z) j t = levelDensity n sens y j t := by
  classical
  unfold levelDensity
  rw [levelCount_update_of_gt y i hz ht]
  by_cases hj : j = i
  · subst hj
    have h1 : ¬ t ≤ z := not_le.mpr ht
    have h2 : ¬ t ≤ y j := fun h => h1 (le_trans h hz)
    simp [Function.update_self, h1, h2]
  · rw [Function.update_of_ne hj]

/-- The mover's own increment on the crossed interval is the own slope. -/
theorem levelDensity_update_self_mid (y : ι → ℝ) (i : ι) {z t : ℝ} (h1 : y i < t)
    (h2 : t ≤ z) :
    levelDensity n sens (Function.update y i z) i t - levelDensity n sens y i t
      = levelGain n sens (levelCount y t + 1) + levelCoeff n sens (levelCount y t) := by
  classical
  have hi : t ≤ Function.update y i z i := by simp [Function.update_self, h2]
  have hnew : levelDensity n sens (Function.update y i z) i t
      = levelGain n sens (levelCount y t + 1) := by
    rw [levelDensity_of_le (Function.update y i z) i hi,
      levelCount_update_mid y i h1 h2]
  have hold : levelDensity n sens y i t = -levelCoeff n sens (levelCount y t) :=
    levelDensity_of_not_le y i (not_le.mpr h1)
  rw [hnew, hold]
  ring

/-- Every other agent's increment on the crossed interval is nonpositive. -/
theorem levelDensity_update_other_mid (hn : 4 ≤ n) (hs : 0 ≤ sens)
    (y : ι → ℝ) {i j : ι} (hij : j ≠ i) {z t : ℝ}
    (h1 : y i < t) (h2 : t ≤ z) :
    levelDensity n sens (Function.update y i z) j t - levelDensity n sens y j t ≤ 0 := by
  classical
  have hyj : Function.update y i z j = y j := Function.update_of_ne hij _ _
  have hcount := levelCount_update_mid y i h1 h2
  by_cases hj : t ≤ y j
  · have hjnew : t ≤ Function.update y i z j := by rw [hyj]; exact hj
    rw [levelDensity_of_le (Function.update y i z) j hjnew, hcount,
      levelDensity_of_le y j hj]
    have hpos : 0 < levelCount y t := levelCount_pos_of_le y j hj
    have hmono := levelGain_antitone (n := n) (sens := sens) hn hs
      (k := levelCount y t) (l := levelCount y t + 1) hpos (Nat.le_succ _)
    linarith
  · have hjnew : ¬ t ≤ Function.update y i z j := by rw [hyj]; exact hj
    rw [levelDensity_of_not_le (Function.update y i z) j hjnew, hcount,
      levelDensity_of_not_le y j hj]
    rcases Nat.eq_zero_or_pos (levelCount y t) with h0 | hpos
    · rw [h0, levelCoeff_zero]
      have := levelCoeff_nonneg (n := n) (sens := sens) hn hs (0 + 1)
      linarith
    · have := levelCoeff_mono (n := n) (sens := sens) hn hs
        (k := levelCount y t) (l := levelCount y t + 1) hpos (Nat.le_succ _)
      linarith

/-- The own slope never exceeds `S`.  At a level with one agent above it the
slope is `β`, at two it is exactly `S`, and from three on it is `Cn/r`, which
`n ≥ 4` keeps below `S`. -/
theorem own_slope_le (hn : 4 ≤ n) (hs : 0 ≤ sens) {r : ℕ} (hr : r ≤ n) :
    levelGain n sens (r + 1) + levelCoeff n sens r ≤ sens := by
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn2ne : ((n : ℝ) - 2) ≠ 0 := by intro h; nlinarith
  have hnn2 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 2) := by nlinarith
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · interval_cases r
    · rw [levelGain, levelCoeff_zero, levelCoeff_one, add_zero]
      norm_num
      rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
      nlinarith
    · rw [levelGain, levelCoeff_of_two_le (by norm_num : 2 ≤ 1 + 1), levelCoeff_one]
      norm_num
      have hexp : 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2)) * ((n : ℝ) / 2 - 1)
          = ((n : ℝ) - 1) * sens / n := by
        field_simp
      have hsum : ((n : ℝ) - 1) * sens / n + sens / n = sens := by
        field_simp
        ring
      rw [hexp]
      linarith [hsum]
  · have hr1 : 2 ≤ r + 1 := by omega
    have hrR : (3 : ℝ) ≤ ((r : ℝ) + 1) := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    have hrn : ((r : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
      linarith
    rw [levelGain, levelCoeff_of_two_le hr1, levelCoeff_of_two_le hr2]
    have hcast : (((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
    have hexp : 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2))
          * ((n : ℝ) / ((r : ℝ) + 1) - 1)
        + 2 * ((n : ℝ) - 1) * sens / ((n : ℝ) * ((n : ℝ) - 2))
        = 2 * ((n : ℝ) - 1) * sens / (((n : ℝ) - 2) * ((r : ℝ) + 1)) := by
      field_simp
      ring
    rw [hexp, div_le_iff₀ (by nlinarith : (0:ℝ) < ((n : ℝ) - 2) * ((r : ℝ) + 1))]
    nlinarith [mul_nonneg hs (by nlinarith :
      (0:ℝ) ≤ ((n:ℝ) - 2) * ((r:ℝ) + 1) - 2 * ((n:ℝ) - 1))]

theorem own_slope_nonneg (hn : 4 ≤ n) (hs : 0 ≤ sens) {r : ℕ} (hr : r + 1 ≤ n) :
    0 ≤ levelGain n sens (r + 1) + levelCoeff n sens r :=
  add_nonneg (levelGain_nonneg hn hs hr) (levelCoeff_nonneg hn hs r)

end Update

/-! ### The rule -/

section Rule

variable [DecidableEq ι] {reserve : ℝ}

/-- **Rule B**: the paper's second rank rule, written as an integral of its
level density over the band. -/
def rankRuleB (totalWeight : ℝ) (sensitivity : NNReal) (v₀ δ : ℝ) :
    InterimRule ι reserve := fun b i =>
  totalWeight / Fintype.card ι +
    ∫ t in v₀..(v₀ + δ), levelDensity (Fintype.card ι) sensitivity
      (fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ)) i t

omit [Fintype ι] in
theorem clipScores_update (v₀ δ : ℝ) (b : EligibleProfile ι reserve) (i : ι)
    (z : EligibleBid reserve) :
    (fun j => clipBand v₀ δ ((updateBid b i z j : EligibleBid reserve) : ℝ))
      = Function.update (fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ)) i
          (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [updateBid]
  · simp [updateBid, Function.update_of_ne hj]

theorem levelCount_lt_card_of_not_le {y : ι → ℝ} {i : ι} {t : ℝ} (h : ¬ t ≤ y i) :
    levelCount y t + 1 ≤ Fintype.card ι := by
  classical
  have hsub : (Finset.univ.filter fun j => t ≤ y j) ⊆ Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hji
    exact h (hji ▸ hj)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hcard
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  unfold levelCount
  omega

/-- Pointwise bounds on the mover's increment. -/
theorem levelDensity_self_diff_bounds {sens : ℝ} (hn : 4 ≤ Fintype.card ι)
    (hs : 0 ≤ sens) (y : ι → ℝ) (i : ι) {z : ℝ} (hz : y i ≤ z) {t : ℝ}
    (ht : t ∈ Set.Icc (y i) z) :
    0 ≤ levelDensity (Fintype.card ι) sens (Function.update y i z) i t
          - levelDensity (Fintype.card ι) sens y i t ∧
      levelDensity (Fintype.card ι) sens (Function.update y i z) i t
          - levelDensity (Fintype.card ι) sens y i t ≤ sens := by
  by_cases hle : t ≤ y i
  · rw [levelDensity_update_of_le y i i hz hle, sub_self]
    exact ⟨le_rfl, hs⟩
  · have h1 : y i < t := not_le.mp hle
    have h2 : t ≤ z := ht.2
    rw [levelDensity_update_self_mid y i h1 h2]
    have hcount : levelCount y t + 1 ≤ Fintype.card ι :=
      levelCount_lt_card_of_not_le hle
    exact ⟨own_slope_nonneg hn hs hcount,
      own_slope_le hn hs (by omega : levelCount y t ≤ Fintype.card ι)⟩

/-- Pointwise bound on every other agent's increment. -/
theorem levelDensity_other_diff_nonpos {sens : ℝ} (hn : 4 ≤ Fintype.card ι)
    (hs : 0 ≤ sens) (y : ι → ℝ) {i j : ι} (hij : j ≠ i) {z : ℝ} (hz : y i ≤ z)
    {t : ℝ} (ht : t ∈ Set.Icc (y i) z) :
    levelDensity (Fintype.card ι) sens (Function.update y i z) j t
      - levelDensity (Fintype.card ι) sens y j t ≤ 0 := by
  by_cases hle : t ≤ y i
  · rw [levelDensity_update_of_le y i j hz hle, sub_self]
  · exact levelDensity_update_other_mid hn hs y hij (not_le.mp hle) ht.2

/-- Raising one score moves the integral only over the level interval it
crossed. -/
theorem rankRuleB_integral_diff {sens : ℝ} (hn : 4 ≤ Fintype.card ι) (hs : 0 ≤ sens)
    (y : ι → ℝ) (i j : ι) {z v₀ δ : ℝ} (hz : y i ≤ z)
    (hlow : v₀ ≤ y i) (hhigh : z ≤ v₀ + δ) :
    (∫ t in v₀..(v₀ + δ), levelDensity (Fintype.card ι) sens (Function.update y i z) j t)
        - ∫ t in v₀..(v₀ + δ), levelDensity (Fintype.card ι) sens y j t
      = ∫ t in (y i)..z, (levelDensity (Fintype.card ι) sens (Function.update y i z) j t
          - levelDensity (Fintype.card ι) sens y j t) := by
  have hint : ∀ (w : ι → ℝ) (a b : ℝ),
      IntervalIntegrable (levelDensity (Fintype.card ι) sens w j) MeasureTheory.volume a b :=
    fun w a b => levelDensity_intervalIntegrable hn hs rfl w j a b
  have hsplit1 :
      (∫ t in v₀..(y i), levelDensity (Fintype.card ι) sens (Function.update y i z) j t
          - levelDensity (Fintype.card ι) sens y j t) = 0 := by
    have hzero : ∀ t ∈ Set.uIcc v₀ (y i),
        levelDensity (Fintype.card ι) sens (Function.update y i z) j t
          - levelDensity (Fintype.card ι) sens y j t = 0 := by
      intro t ht
      have htle : t ≤ y i := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact h.2
        · exact le_trans h.2 hlow
      rw [levelDensity_update_of_le y i j hz htle, sub_self]
    rw [intervalIntegral.integral_congr hzero]
    simp
  have hsplit3 :
      (∫ t in z..(v₀ + δ), levelDensity (Fintype.card ι) sens (Function.update y i z) j t
          - levelDensity (Fintype.card ι) sens y j t) = 0 := by
    have hzero : ∀ᵐ t : ℝ, t ∈ Set.uIoc z (v₀ + δ) →
        levelDensity (Fintype.card ι) sens (Function.update y i z) j t
          - levelDensity (Fintype.card ι) sens y j t = 0 := by
      filter_upwards with t ht
      have htgt : z < t := by
        rcases Set.mem_uIoc.mp ht with h | h
        · exact h.1
        · exact lt_of_le_of_lt hhigh h.1
      rw [levelDensity_update_of_gt y i j hz htgt, sub_self]
    rw [intervalIntegral.integral_congr_ae hzero]
    simp
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (a := v₀) (b := y i) (c := z)
    ((hint (Function.update y i z) v₀ (y i)).sub (hint y v₀ (y i)))
    ((hint (Function.update y i z) (y i) z).sub (hint y (y i) z))
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (a := v₀) (b := z) (c := v₀ + δ)
    ((hint (Function.update y i z) v₀ z).sub (hint y v₀ z))
    ((hint (Function.update y i z) z (v₀ + δ)).sub (hint y z (v₀ + δ)))
  rw [← intervalIntegral.integral_sub (hint (Function.update y i z) v₀ (v₀ + δ))
    (hint y v₀ (v₀ + δ))]
  rw [hsplit1, zero_add] at hadd1
  rw [hsplit3, add_zero] at hadd2
  rw [← hadd2, ← hadd1]

end Rule

/-! ### Rule B is in the certified class -/

section Class

variable [DecidableEq ι] {reserve : ℝ} {capacity : ℕ → ℝ} {totalWeight : ℝ}
  {sensitivity : NNReal} {δ : ℝ}

omit [DecidableEq ι] in
theorem rankRuleB_abs_sub_le (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ)
    (b : EligibleProfile ι reserve) (i : ι) :
    |rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ b i
        - totalWeight / Fintype.card ι| ≤ (sensitivity : ℝ) * δ := by
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  set y : ι → ℝ := fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ) with hy
  have hbound : ∀ t ∈ Set.uIoc v₀ (v₀ + δ),
      ‖levelDensity (Fintype.card ι) (sensitivity : ℝ) y i t‖ ≤ (sensitivity : ℝ) := by
    intro t _
    rw [Real.norm_eq_abs]
    exact abs_levelDensity_le hn hs rfl y i t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [rankRuleB]
  simp only [add_sub_cancel_left]
  rw [← Real.norm_eq_abs]
  calc ‖∫ t in v₀..(v₀ + δ), levelDensity (Fintype.card ι) (sensitivity : ℝ) y i t‖
      ≤ (sensitivity : ℝ) * |v₀ + δ - v₀| := h
    _ = (sensitivity : ℝ) * δ := by rw [add_sub_cancel_left, abs_of_nonneg hδ]

omit [DecidableEq ι] in
theorem rankRuleB_noWaste (hn : 4 ≤ Fintype.card ι) (_hδ : 0 ≤ δ) (v₀ : ℝ) :
    OneSlotNoWaste totalWeight
      (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  intro b
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hcardpos : 0 < Fintype.card ι := by omega
  set y : ι → ℝ := fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ) with hy
  have hsum : ∑ i, (∫ t in v₀..(v₀ + δ),
      levelDensity (Fintype.card ι) (sensitivity : ℝ) y i t) = 0 := by
    rw [← intervalIntegral.integral_finsetSum
      (fun i _ => levelDensity_intervalIntegrable hn hs rfl y i v₀ (v₀ + δ))]
    have hzero : ∀ t ∈ Set.uIcc v₀ (v₀ + δ),
        ∑ i, levelDensity (Fintype.card ι) (sensitivity : ℝ) y i t = 0 :=
      fun t _ => levelDensity_sum rfl (sensitivity : ℝ) y t
    rw [intervalIntegral.integral_congr hzero]
    simp
  unfold rankRuleB
  rw [Finset.sum_add_distrib, hsum, add_zero, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

omit [DecidableEq ι] in
theorem rankRuleB_anonymous (v₀ δ : ℝ) :
    Anonymous (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  intro π b i
  unfold rankRuleB relabelProfile
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  unfold levelDensity
  have hcount : levelCount
      (fun j => clipBand v₀ δ ((b (π.symm j) : EligibleBid reserve) : ℝ)) t
      = levelCount (fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ)) t := by
    unfold levelCount
    apply Finset.card_equiv π.symm
    intro a
    simp
  rw [hcount]
  simp

omit [DecidableEq ι] in
theorem rankRuleB_nonneg (hn : 4 ≤ Fintype.card ι) (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (b : EligibleProfile ι reserve) (i : ι) :
    0 ≤ rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ b i := by
  have habs := rankRuleB_abs_sub_le (totalWeight := totalWeight)
    (sensitivity := sensitivity) hn hs.delta_pos.le v₀ b i
  have hbound := hs.sens_mul_delta_le
  have := abs_le.mp habs
  linarith [this.1]

omit [DecidableEq ι] in
theorem rankRuleB_subsetFeasible (hn : 4 ≤ Fintype.card ι) (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ) :
    SubsetFeasible capacity
      (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  classical
  intro b H
  have hδ : 0 ≤ δ := hs.delta_pos.le
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos H.card with hzero | hpos
  · have hH : H = ∅ := Finset.card_eq_zero.mp hzero
    subst hH
    simpa using hs.cap_zero
  · rcases eq_or_lt_of_le (Finset.card_le_univ H) with hfull | hlt
    · have hHuniv : H = Finset.univ := by
        apply Finset.eq_univ_of_card
        exact hfull
      subst hHuniv
      rw [rankRuleB_noWaste hn hδ v₀ b, ← hs.cap_total, Finset.card_univ]
    · have hkn1 : H.card ≤ Fintype.card ι - 1 := by omega
      have hband := hs.band_mul hpos hkn1
      have hpt : ∀ m ∈ H,
          rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ b m
            ≤ totalWeight / Fintype.card ι + (sensitivity : ℝ) * δ := by
        intro m _
        have := abs_le.mp (rankRuleB_abs_sub_le (totalWeight := totalWeight)
          (sensitivity := sensitivity) hn hδ v₀ b m)
        linarith [this.2]
      calc ∑ m ∈ H, rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ b m
          ≤ ∑ _m ∈ H, (totalWeight / Fintype.card ι + (sensitivity : ℝ) * δ) :=
            Finset.sum_le_sum hpt
        _ = (H.card : ℝ) * (totalWeight / Fintype.card ι)
              + (sensitivity : ℝ) * H.card * δ := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ capacity H.card := hband

end Class


/-! ### Monotonicity and the Lipschitz bound -/

section Monotone

variable [DecidableEq ι] {reserve : ℝ} {totalWeight : ℝ} {sensitivity : NNReal} {δ : ℝ}

/-- Moving one bid up moves each allocation by the integral of the density
increment over the crossed level interval. -/
theorem rankRuleB_update_diff (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ)
    (b : EligibleProfile ι reserve) (i j : ι) (z w : EligibleBid reserve)
    (hzw : ((z : EligibleBid reserve) : ℝ) ≤ ((w : EligibleBid reserve) : ℝ)) :
    rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
          (updateBid b i w) j
        - rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
          (updateBid b i z) j
      = ∫ t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
            ((w : EligibleBid reserve) : ℝ)),
          (levelDensity (Fintype.card ι) (sensitivity : ℝ)
              (Function.update
                (fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) i
                (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) j t
            - levelDensity (Fintype.card ι) (sensitivity : ℝ)
              (Function.update
                (fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) i
                (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) j t) := by
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  set y : ι → ℝ := fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) with hy
  set Y : ι → ℝ := Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))
    with hY
  have hYi : Y i = clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) := by
    simp [hY, Function.update_self]
  have hidem : Function.update Y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
      = Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) := by
    rw [hY, Function.update_idem]
  have hstep := rankRuleB_integral_diff (sens := (sensitivity : ℝ)) hn hs Y i j
    (z := clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) (v₀ := v₀) (δ := δ)
    (by rw [hYi]; exact clipBand_mono v₀ δ hzw)
    (by rw [hYi]; exact clipBand_ge v₀ δ _ hδ)
    (clipBand_le v₀ δ _)
  rw [hYi, hidem] at hstep
  unfold rankRuleB
  rw [clipScores_update, clipScores_update, ← hy, ← hY, add_sub_add_left_eq_sub]
  exact hstep

theorem rankRuleB_ownMonotone (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ) :
    OwnMonotone (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  intro b i z w hzw
  dsimp only
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hzwR : ((z : EligibleBid reserve) : ℝ) ≤ ((w : EligibleBid reserve) : ℝ) := hzw
  have hclip : clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
      ≤ clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) := clipBand_mono v₀ δ hzwR
  have hdiff := rankRuleB_update_diff (totalWeight := totalWeight)
    (sensitivity := sensitivity) hn hδ v₀ b i i z w hzwR
  set y : ι → ℝ := fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) with hy
  have hYi : (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
      = clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) := by
    simp [Function.update_self]
  have hidem : Function.update
        (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
        (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
      = Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) :=
    Function.update_idem _ _ _
  have hnonneg : 0 ≤ ∫ t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
        ((w : EligibleBid reserve) : ℝ)),
      (levelDensity (Fintype.card ι) (sensitivity : ℝ)
          (Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i t
        - levelDensity (Fintype.card ι) (sensitivity : ℝ)
          (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i t) := by
    apply intervalIntegral.integral_nonneg hclip
    intro t ht
    have hb := (levelDensity_self_diff_bounds (sens := (sensitivity : ℝ)) hn hs
      (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
      (z := clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
      (by rw [hYi]; exact hclip) (by rw [hYi]; exact ht)).1
    rw [hidem] at hb
    exact hb
  linarith [hdiff, hnonneg]

theorem rankRuleB_crossMonotone (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ) :
    CrossMonotone (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  intro b i j hij z w hzw
  dsimp only
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hzwR : ((z : EligibleBid reserve) : ℝ) ≤ ((w : EligibleBid reserve) : ℝ) := hzw
  have hclip : clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
      ≤ clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) := clipBand_mono v₀ δ hzwR
  have hdiff := rankRuleB_update_diff (totalWeight := totalWeight)
    (sensitivity := sensitivity) hn hδ v₀ b j i z w hzwR
  set y : ι → ℝ := fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) with hy
  have hYj : (Function.update y j (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) j
      = clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) := by
    simp [Function.update_self]
  have hidem : Function.update
        (Function.update y j (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) j
        (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
      = Function.update y j (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) :=
    Function.update_idem _ _ _
  have hint1 := levelDensity_intervalIntegrable (n := Fintype.card ι)
    (sens := (sensitivity : ℝ)) hn hs rfl
    (Function.update y j (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i
    (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))
    (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
  have hint2 := levelDensity_intervalIntegrable (n := Fintype.card ι)
    (sens := (sensitivity : ℝ)) hn hs rfl
    (Function.update y j (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
    (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))
    (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
  have hnonpos : (∫ t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
        ((w : EligibleBid reserve) : ℝ)),
      (levelDensity (Fintype.card ι) (sensitivity : ℝ)
          (Function.update y j (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i t
        - levelDensity (Fintype.card ι) (sensitivity : ℝ)
          (Function.update y j (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i t)) ≤ 0 := by
    have hzero : (∫ _t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
        ((w : EligibleBid reserve) : ℝ)), (0 : ℝ)) = 0 := by simp
    rw [← hzero]
    apply intervalIntegral.integral_mono_on hclip (hint1.sub hint2)
      intervalIntegrable_const
    intro t ht
    have hb := levelDensity_other_diff_nonpos (sens := (sensitivity : ℝ)) hn hs
      (Function.update y j (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) hij
      (z := clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
      (by rw [hYj]; exact hclip) (by rw [hYj]; exact ht)
    rw [hidem] at hb
    linarith
  linarith [hdiff, hnonpos]

theorem rankRuleB_ownLipschitz (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ) :
    OwnLipschitz sensitivity
      (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) := by
  have hs : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have key : ∀ (b : EligibleProfile ι reserve) (i : ι) (z w : EligibleBid reserve),
      ((z : EligibleBid reserve) : ℝ) ≤ ((w : EligibleBid reserve) : ℝ) →
      rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
            (updateBid b i w) i
          - rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
            (updateBid b i z) i
        ≤ (sensitivity : ℝ) * (((w : EligibleBid reserve) : ℝ)
            - ((z : EligibleBid reserve) : ℝ)) := by
    intro b i z w hzwR
    have hclip : clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
        ≤ clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) := clipBand_mono v₀ δ hzwR
    have hdiff := rankRuleB_update_diff (totalWeight := totalWeight)
      (sensitivity := sensitivity) hn hδ v₀ b i i z w hzwR
    set y : ι → ℝ := fun k => clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) with hy
    have hYi : (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
        = clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) := by
      simp [Function.update_self]
    have hidem : Function.update
          (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
          (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
        = Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) :=
      Function.update_idem _ _ _
    have hint1 := levelDensity_intervalIntegrable (n := Fintype.card ι)
      (sens := (sensitivity : ℝ)) hn hs rfl
      (Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i
      (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))
      (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
    have hint2 := levelDensity_intervalIntegrable (n := Fintype.card ι)
      (sens := (sensitivity : ℝ)) hn hs rfl
      (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
      (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))
      (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
    have hmono : (∫ t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
          ((w : EligibleBid reserve) : ℝ)),
        (levelDensity (Fintype.card ι) (sensitivity : ℝ)
            (Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i t
          - levelDensity (Fintype.card ι) (sensitivity : ℝ)
            (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i t))
        ≤ ∫ _t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
            ((w : EligibleBid reserve) : ℝ)), (sensitivity : ℝ) := by
      apply intervalIntegral.integral_mono_on hclip (hint1.sub hint2)
        intervalIntegrable_const
      intro t ht
      have hb := (levelDensity_self_diff_bounds (sens := (sensitivity : ℝ)) hn hs
        (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i
        (z := clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))
        (by rw [hYi]; exact hclip) (by rw [hYi]; exact ht)).2
      rw [hidem] at hb
      exact hb
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hclipdist : clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
        - clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
        ≤ ((w : EligibleBid reserve) : ℝ) - ((z : EligibleBid reserve) : ℝ) := by
      have habs := clipBand_dist_le v₀ δ ((w : EligibleBid reserve) : ℝ)
        ((z : EligibleBid reserve) : ℝ)
      have h1 : clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
          - clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) ≤
          |clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
            - clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)| := le_abs_self _
      have h2 : |((w : EligibleBid reserve) : ℝ) - ((z : EligibleBid reserve) : ℝ)|
          = ((w : EligibleBid reserve) : ℝ) - ((z : EligibleBid reserve) : ℝ) :=
        abs_of_nonneg (by linarith)
      rw [h2] at habs
      linarith
    have hfinal := mul_le_mul_of_nonneg_left hclipdist hs
    rw [hdiff]
    calc (∫ t in (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))..(clipBand v₀ δ
            ((w : EligibleBid reserve) : ℝ)),
          (levelDensity (Fintype.card ι) (sensitivity : ℝ)
              (Function.update y i (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ))) i t
            - levelDensity (Fintype.card ι) (sensitivity : ℝ)
              (Function.update y i (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ))) i t))
        ≤ (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
            - clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)) * (sensitivity : ℝ) := hmono
      _ = (sensitivity : ℝ) * (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
            - clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)) := by ring
      _ ≤ (sensitivity : ℝ) * (((w : EligibleBid reserve) : ℝ)
            - ((z : EligibleBid reserve) : ℝ)) := hfinal
  intro b i
  apply LipschitzWith.of_dist_le_mul
  intro z w
  dsimp only
  have hd : dist z w = |((z : EligibleBid reserve) : ℝ) - ((w : EligibleBid reserve) : ℝ)| := by
    simp [Subtype.dist_eq, Real.dist_eq]
  rw [Real.dist_eq, hd]
  rcases le_total ((z : EligibleBid reserve) : ℝ) ((w : EligibleBid reserve) : ℝ) with h | h
  · have hup := key b i z w h
    have hdown := rankRuleB_ownMonotone (totalWeight := totalWeight)
      (sensitivity := sensitivity) hn hδ v₀ b i (show z ≤ w from h)
    rw [abs_of_nonpos (by linarith : ((z : EligibleBid reserve) : ℝ)
      - ((w : EligibleBid reserve) : ℝ) ≤ 0), abs_sub_comm,
      abs_of_nonneg (by linarith [hdown] :
        (0:ℝ) ≤ rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
          (updateBid b i w) i
          - rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
            (updateBid b i z) i)]
    linarith
  · have hup := key b i w z h
    have hdown := rankRuleB_ownMonotone (totalWeight := totalWeight)
      (sensitivity := sensitivity) hn hδ v₀ b i (show w ≤ z from h)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ((z : EligibleBid reserve) : ℝ)
      - ((w : EligibleBid reserve) : ℝ)),
      abs_of_nonneg (by linarith [hdown] :
        (0:ℝ) ≤ rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
          (updateBid b i z) i
          - rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
            (updateBid b i w) i)]
    linarith

end Monotone

/-! ### Rule B is certified, and its value at the tied profile -/

section Final

variable [DecidableEq ι] {reserve : ℝ} {capacity : ℕ → ℝ} {totalWeight : ℝ}
  {sensitivity : NNReal} {δ : ℝ}

theorem rankRuleB_certified (hn : 4 ≤ Fintype.card ι) (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ) :
    Certified capacity totalWeight sensitivity
      (rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) where
  anon := rankRuleB_anonymous v₀ δ
  ownMono := rankRuleB_ownMonotone hn hs.delta_pos.le v₀
  ownLip := rankRuleB_ownLipschitz hn hs.delta_pos.le v₀
  crossMono := rankRuleB_crossMonotone hn hs.delta_pos.le v₀
  subsetFeasible := rankRuleB_subsetFeasible hn v₀ hs
  noWaste := rankRuleB_noWaste hn hs.delta_pos.le v₀
  nonneg := fun b i => rankRuleB_nonneg hn v₀ hs b i

/-- **Rule B gives each tied leader `W/n + (n-1)/n · S δ`.**  At the tied
profile exactly two agents sit above every level inside the band, so the
density is the constant `β = (n-1) S / n`. -/
theorem rankRuleB_tied_value (hn : 4 ≤ Fintype.card ι) (hδ : 0 ≤ δ) (v₀ : ℝ)
    (h₀ : reserve ≤ v₀) {lead second : ι} (hls : lead ≠ second) :
    rankRuleB (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
        (tiedProfile v₀ δ h₀ hδ lead second) second
      = totalWeight / Fintype.card ι
        + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this
  have hn4 : (4 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  set y : ι → ℝ := fun j =>
    clipBand v₀ δ ((tiedProfile v₀ δ h₀ hδ lead second j : EligibleBid reserve) : ℝ)
    with hy
  have hlead : y lead = v₀ + δ := by
    rw [hy]
    simp only
    rw [tiedProfile_lead (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hls]
    exact clipBand_eq_of_mem v₀ δ _ (by linarith) le_rfl
  have hsecond : y second = v₀ + δ := by
    rw [hy]
    simp only
    rw [tiedProfile_second]
    exact clipBand_eq_of_mem v₀ δ _ (by linarith) le_rfl
  have hother : ∀ j, j ≠ lead → j ≠ second → y j = v₀ := by
    intro j h1 h2
    rw [hy]
    simp only
    rw [tiedProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) h1 h2]
    exact clipBand_eq_of_mem v₀ δ _ le_rfl (by linarith)
  have hcount : ∀ t : ℝ, v₀ < t → t ≤ v₀ + δ → levelCount y t = 2 := by
    intro t ht1 ht2
    have hset : (Finset.univ.filter fun j => t ≤ y j) = {lead, second} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hj
        by_contra hcon
        push Not at hcon
        rw [hother j hcon.1 hcon.2] at hj
        linarith
      · rintro (rfl | rfl)
        · rw [hlead]; exact ht2
        · rw [hsecond]; exact ht2
    unfold levelCount
    rw [hset, Finset.card_insert_of_notMem (by simp [hls]), Finset.card_singleton]
  have hbeta : ∀ t : ℝ, v₀ < t → t ≤ v₀ + δ →
      levelDensity (Fintype.card ι) (sensitivity : ℝ) y second t
        = ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity := by
    intro t ht1 ht2
    have hle : t ≤ y second := by rw [hsecond]; exact ht2
    rw [levelDensity_of_le y second hle, hcount t ht1 ht2, levelGain,
      levelCoeff_of_two_le (le_refl 2)]
    have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [h2]
    have hne : ((Fintype.card ι : ℝ) - 2) ≠ 0 := by intro h; linarith
    have hcne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcardpos
    field_simp
  have hint : (∫ t in v₀..(v₀ + δ),
      levelDensity (Fintype.card ι) (sensitivity : ℝ) y second t)
      = δ * (((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity) := by
    have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc v₀ (v₀ + δ) →
        levelDensity (Fintype.card ι) (sensitivity : ℝ) y second t
          = ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity := by
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by linarith : v₀ ≤ v₀ + δ)] at ht
      exact hbeta t ht.1 ht.2
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const,
      smul_eq_mul]
    congr 1
    ring
  rw [rankRuleB, ← hy, hint]
  ring

end Final

/-! ### Theorem `thm:impossibility` -/

section Impossibility

variable [DecidableEq ι] {reserve : ℝ} {capacity : ℕ → ℝ} {totalWeight : ℝ}
  {sensitivity : NNReal} {δ : ℝ}

/-- **No pointwise welfare-optimal rule exists in `C`.** -/
theorem no_pointwise_optimum (hn4 : 4 ≤ Fintype.card ι) (v₀ : ℝ) (h₀ : reserve ≤ v₀)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    {lead second : ι} (hls : lead ≠ second) (x : InterimRule ι reserve)
    (hopt : PointwiseOptimal capacity totalWeight sensitivity x) : False :=
  no_pointwise_optimum_of_second_rule hs hn4 h₀ hls
    (rankRuleB totalWeight sensitivity v₀ δ) (rankRuleB_certified hn4 v₀ hs)
    (rankRuleB_tied_value hn4 hs.delta_pos.le v₀ h₀ hls) x hopt

/-- **Theorem `thm:impossibility` in full.**  For `n ≥ 4`, a positive
sensitivity and a band width strictly below `δ̄`: Proposition `prop:squeeze`
caps welfare at the two adjacent profiles; the `R₁` cap is attained by a
globally defined rule in `C`; every rule in `C` has shortfalls obeying
`2a + (n-1) b ≥ 2 S δ²`; a second globally defined rule in `C` gives each tied
leader at `R₂` the weight `W/n + (n-1)/n · S δ`, strictly more than any rule
attaining the `R₁` cap can give there; and consequently no rule in `C` is
pointwise welfare-optimal. -/
theorem thm_impossibility (hn4 : 4 ≤ Fintype.card ι) (v₀ : ℝ) (h₀ : reserve ≤ v₀)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    {lead second : ι} (hls : lead ≠ second) :
    (∀ x : InterimRule ι reserve, Certified capacity totalWeight sensitivity x →
        welfare x (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
          ≤ loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)) ∧
    (∀ x : InterimRule ι reserve, Certified capacity totalWeight sensitivity x →
        welfare x (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second)
          ≤ tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)) ∧
    (∃ y : InterimRule ι reserve, Certified capacity totalWeight sensitivity y ∧
        welfare y (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
          = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)) ∧
    (∀ x : InterimRule ι reserve, Certified capacity totalWeight sensitivity x →
        2 * (loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)
              - welfare x (loneProfile v₀ δ h₀ hs.delta_pos.le lead))
          + ((Fintype.card ι : ℝ) - 1)
              * (tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)
                  - welfare x (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second))
          ≥ 2 * sensitivity * δ ^ 2) ∧
    (∃ y : InterimRule ι reserve, Certified capacity totalWeight sensitivity y ∧
        y (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second) second
          = totalWeight / Fintype.card ι
            + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ) ∧
    (∀ x : InterimRule ι reserve, Certified capacity totalWeight sensitivity x →
        welfare x (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
            = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι) →
          x (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second) second
            < totalWeight / Fintype.card ι
              + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ) ∧
    ¬ ∃ x : InterimRule ι reserve,
        PointwiseOptimal capacity totalWeight sensitivity x := by
  obtain ⟨hcap1, hcap2, hattain, hshort, hceil⟩ :=
    impossibility_clauses hs hn4 h₀ hls
  refine ⟨hcap1, hcap2, hattain, hshort, ⟨rankRuleB totalWeight sensitivity v₀ δ,
    rankRuleB_certified hn4 v₀ hs,
    rankRuleB_tied_value hn4 hs.delta_pos.le v₀ h₀ hls⟩, hceil, ?_⟩
  rintro ⟨x, hx⟩
  exact no_pointwise_optimum hn4 v₀ h₀ hs hls x hx

end Impossibility

/-! ### The conclusion for any subclass carrying the two witnesses

The class `Certified` encodes assignment feasibility as the permutohedron
subset system, which is implied by, but not known here to imply, the paper's
"induced by a lottery over assignments".  A negative existential is not
monotone in the class, so the statement proved for `Certified` does not by
itself deliver the paper's statement for its own smaller class.  The theorem
below removes that dependence: it holds for EVERY class `D` that is contained
in `Certified` and contains the two rules the argument exhibits.  Instantiating
`D` at the paper's class needs exactly one fact -- that rule A and rule B are
lottery-implementable -- and nothing else. -/

section Subclass

variable [DecidableEq ι] {reserve : ℝ} {capacity : ℕ → ℝ} {totalWeight : ℝ}
  {sensitivity : NNReal} {δ : ℝ}

/-- Pointwise optimality inside an arbitrary class `D` of rules. -/
def PointwiseOptimalIn (D : InterimRule ι reserve → Prop)
    (x : InterimRule ι reserve) : Prop :=
  D x ∧ ∀ y : InterimRule ι reserve, D y →
    ∀ b : EligibleProfile ι reserve, welfare y b ≤ welfare x b

/-- **Theorem `thm:impossibility` for any admissible subclass.**  Let `D` be
any class of rules contained in `Certified` that contains the band-linear rule
A and the level-density rank rule B.  Then no rule in `D` is pointwise
welfare-optimal within `D`.  Taking `D = Certified` recovers
`no_pointwise_optimum`; taking `D` to be the paper's lottery class requires
only that the two exhibited rules belong to it. -/
theorem no_pointwise_optimum_in_subclass (hn4 : 4 ≤ Fintype.card ι) (v₀ : ℝ)
    (h₀ : reserve ≤ v₀)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    {lead second : ι} (hls : lead ≠ second)
    (D : InterimRule ι reserve → Prop)
    (hsub : ∀ y, D y → Certified capacity totalWeight sensitivity y)
    (hA : D (bandLinearRule totalWeight sensitivity v₀ δ))
    (hB : D (rankRuleB totalWeight sensitivity v₀ δ))
    (x : InterimRule ι reserve) (hopt : PointwiseOptimalIn D x) : False := by
  classical
  obtain ⟨hxD, hbest⟩ := hopt
  have hx := hsub x hxD
  have hδ : 0 < δ := hs.delta_pos
  have hn4' : (3 : ℝ) < (Fintype.card ι : ℝ) := by
    have : (4 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn4
    linarith
  set n : ℝ := (Fintype.card ι : ℝ) with hnd
  set u : ℝ := totalWeight / n with hu
  -- rule A pins the shortfall at `R₁` to zero
  have hAval := bandLinearRule_attains_loneCap (ι := ι) (reserve := reserve) v₀ hs h₀ lead
  have hattain : welfare x (loneProfile v₀ δ h₀ hδ.le lead)
      = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι) := by
    have hge := hbest _ hA (loneProfile v₀ δ h₀ hδ.le lead)
    rw [hAval] at hge
    have hle := welfare_loneProfile_le hx hs.cap_total v₀ δ h₀ hδ.le lead
    linarith
  -- hence its tied leaders at `R₂` fall strictly short of what rule B gives
  have hgap := tied_leader_lt_of_attains_loneCap hs hn4 h₀ hls hx hattain
  have hywelf : welfare (rankRuleB totalWeight sensitivity v₀ δ)
        (tiedProfile v₀ δ h₀ hδ.le lead second)
      = v₀ * totalWeight + 2 * δ * (u + (n - 1) / n * sensitivity * δ) := by
    rw [welfare_tiedProfile _ (rankRuleB_noWaste hn4 hδ.le v₀) v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq (rankRuleB_certified hn4 v₀ hs) v₀ δ h₀ hδ.le hls,
      rankRuleB_tied_value hn4 hδ.le v₀ h₀ hls]
    ring
  have hxwelf : welfare x (tiedProfile v₀ δ h₀ hδ.le lead second)
      = v₀ * totalWeight
        + 2 * δ * x (tiedProfile v₀ δ h₀ hδ.le lead second) second := by
    rw [welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hx v₀ δ h₀ hδ.le hls]
    ring
  have hcontra := hbest _ hB (tiedProfile v₀ δ h₀ hδ.le lead second)
  rw [hywelf, hxwelf] at hcontra
  nlinarith [hgap, hδ]

/-- `no_pointwise_optimum` is the case `D = Certified`. -/
theorem no_pointwise_optimum' (hn4 : 4 ≤ Fintype.card ι) (v₀ : ℝ)
    (h₀ : reserve ≤ v₀)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    {lead second : ι} (hls : lead ≠ second) (x : InterimRule ι reserve)
    (hopt : PointwiseOptimal capacity totalWeight sensitivity x) : False := by
  refine no_pointwise_optimum_in_subclass hn4 v₀ h₀ hs hls
    (Certified capacity totalWeight sensitivity) (fun _ h => h)
    (bandLinearRule_certified v₀ hs) (rankRuleB_certified hn4 v₀ hs) x ⟨hopt.1, hopt.2⟩

end Subclass

end

end SmoothingCliff.Frontier
