import SmoothingCliff.Racing.MixedRace

/-!
# The positive-payoff profiles of the strict-priority race

The converse half of `prop:sp_allequilibria` (iii).  The classification says
what a positive-payoff equilibrium must look like; this file checks that the
displayed profiles are equilibria.

Both strategies live on lattices spaced two contested bands apart, so their
returns are sums of truncated cells at every other rung.  One covering
inequality drives everything: the odd cells occupy at most half of any initial
segment, because pairing each with the even cell just below it recovers the
full partition that the lattice equilibrium already uses.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- Splitting an initial segment into its even and odd halves. -/
theorem sum_range_even_add_odd (f : ℕ → ℝ) :
    ∀ cells : ℕ,
      (∑ k ∈ Finset.range cells, f (2 * k)) +
          (∑ k ∈ Finset.range cells, f (2 * k + 1)) =
        ∑ j ∈ Finset.range (2 * cells), f j
  | 0 => by simp
  | cells + 1 => by
      have hindex : 2 * (cells + 1) = 2 * cells + 1 + 1 := by ring
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hindex,
        Finset.sum_range_succ, Finset.sum_range_succ,
        ← sum_range_even_add_odd f cells]
      ring

/-- The captured band falls as the rival's action rises. -/
theorem strictPriorityCapturedGap_antitone_rival
    {gap action first second : ℝ} (hle : first ≤ second) :
    strictPriorityCapturedGap gap action second ≤
      strictPriorityCapturedGap gap action first := by
  unfold strictPriorityCapturedGap
  refine min_le_min ?_ (le_refl gap)
  exact max_le_max (by linarith) (le_refl 0)

/-- **The covering inequality.**  Cells at every other rung, starting one band
up, occupy at most half of the initial segment. -/
theorem two_mul_sum_oddCell_le
    {gap action : ℝ} (hgap : 0 ≤ gap) (haction : 0 ≤ action) (cells : ℕ) :
    2 * (∑ k ∈ Finset.range cells,
        strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap)) ≤
      action := by
  have hcast : ∀ k : ℕ,
      strictPriorityCapturedGap gap action (((2 * k + 1 : ℕ) : ℝ) * gap) =
        strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap) := by
    intro k
    congr 1
    push_cast
    ring
  have hcastEven : ∀ k : ℕ,
      strictPriorityCapturedGap gap action (((2 * k : ℕ) : ℝ) * gap) =
        strictPriorityCapturedGap gap action ((2 * (k : ℝ)) * gap) := by
    intro k
    congr 1
    push_cast
    ring
  have hmono : ∀ k ∈ Finset.range cells,
      strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap) ≤
        strictPriorityCapturedGap gap action ((2 * (k : ℝ)) * gap) := by
    intro k _
    refine strictPriorityCapturedGap_antitone_rival ?_
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hsplit := sum_range_even_add_odd
    (fun j => strictPriorityCapturedGap gap action ((j : ℝ) * gap)) cells
  simp only [hcast, hcastEven] at hsplit
  rw [sum_strictPriorityCapturedGap_eq_min hgap haction (2 * cells)] at hsplit
  have hle := Finset.sum_le_sum hmono
  have hmin : min action (((2 * cells : ℕ) : ℝ) * gap) ≤ action :=
    min_le_left _ _
  linarith [hsplit, hle, hmin]

/-! ### The displayed profiles

Both carry the same multiset of masses: `2q` on all but one rung and a residual
on the remaining one.  The advantaged player puts the residual on its top rung,
the opponent on the origin.  Writing `nu` for the number of rungs, the window
`1/(2 nu) <= q <= 1/(2 nu - 1)` says exactly that the residual lies between `q`
and `2q`. -/

/-- The mass left over after the full rungs. -/
def profileResidual (rungs : ℕ) (q : ℝ) : ℝ := 1 - 2 * q * ((rungs : ℝ) - 1)

/-- The advantaged player's mass at the odd rung `2k+1`. -/
def oddMass (rungs : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  if k + 1 = rungs then profileResidual rungs q
  else if k < rungs then 2 * q else 0

/-- The opponent's mass at the even rung `2k`. -/
def evenMass (rungs : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then profileResidual rungs q
  else if k < rungs then 2 * q else 0

theorem sum_oddMass (rungs : ℕ) (hrungs : 1 ≤ rungs) (q : ℝ) :
    ∑ k ∈ Finset.range rungs, oddMass rungs q k = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrungs
  rw [show 1 + m = m + 1 by ring, Finset.sum_range_succ]
  have hlast : oddMass (m + 1) q m = profileResidual (m + 1) q := by
    simp [oddMass]
  have hrest : ∀ k ∈ Finset.range m, oddMass (m + 1) q k = 2 * q := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hne : k ≠ m := by omega
    have hlt : k < m + 1 := by omega
    simp [oddMass, hne, hlt]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hlast, profileResidual]
  push_cast
  ring

theorem sum_evenMass (rungs : ℕ) (hrungs : 1 ≤ rungs) (q : ℝ) :
    ∑ k ∈ Finset.range rungs, evenMass rungs q k = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrungs
  rw [show 1 + m = m + 1 by ring, Finset.sum_range_succ']
  have hzero : evenMass (m + 1) q 0 = profileResidual (m + 1) q := by
    simp [evenMass]
  have hrest : ∀ k ∈ Finset.range m, evenMass (m + 1) q (k + 1) = 2 * q := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hlt : k + 1 < m + 1 := by omega
    simp [evenMass, hlt]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hzero, profileResidual]
  push_cast
  ring

theorem oddMass_le (rungs : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hlower : profileResidual rungs q ≤ 2 * q) (k : ℕ) :
    oddMass rungs q k ≤ 2 * q := by
  unfold oddMass
  split_ifs with h1 h2
  · exact hlower
  · exact le_refl _
  · linarith

theorem evenMass_le (rungs : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hlower : profileResidual rungs q ≤ 2 * q) (k : ℕ) :
    evenMass rungs q k ≤ 2 * q := by
  unfold evenMass
  split_ifs with h1 h2
  · exact hlower
  · exact le_refl _
  · linarith

theorem oddMass_nonneg (rungs : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hupper : 0 ≤ profileResidual rungs q) (k : ℕ) :
    0 ≤ oddMass rungs q k := by
  unfold oddMass
  split_ifs with h1 h2
  · exact hupper
  · linarith
  · exact le_refl _

theorem evenMass_nonneg (rungs : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hupper : 0 ≤ profileResidual rungs q) (k : ℕ) :
    0 ≤ evenMass rungs q k := by
  unfold evenMass
  split_ifs with h1 h2
  · exact hupper
  · linarith
  · exact le_refl _

/-- The opponent's return against the advantaged player. -/
def oddExpectedCapturedGap (gap : ℝ) (rungs : ℕ) (q action : ℝ) : ℝ :=
  ∑ k ∈ Finset.range rungs,
    oddMass rungs q k *
      strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap)

/-- The advantaged player's return against the opponent. -/
def evenExpectedCapturedGap (gap : ℝ) (rungs : ℕ) (q action : ℝ) : ℝ :=
  ∑ k ∈ Finset.range rungs,
    evenMass rungs q k *
      strictPriorityCapturedGap gap action (2 * (k : ℝ) * gap)

/-- **The opponent never beats zero.**  Its return is at most the cost ratio
times the action. -/
theorem oddExpectedCapturedGap_le
    {gap q action : ℝ} {rungs : ℕ} (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (hlower : profileResidual rungs q ≤ 2 * q) (haction : 0 ≤ action) :
    oddExpectedCapturedGap gap rungs q action ≤ q * action := by
  have hterm : ∀ k ∈ Finset.range rungs,
      oddMass rungs q k *
          strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap) ≤
        2 * q *
          strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap) :=
    fun k _ => mul_le_mul_of_nonneg_right (oddMass_le rungs hq hlower k)
      (strictPriorityCapturedGap_nonneg hgap)
  have hcover := two_mul_sum_oddCell_le hgap haction rungs
  unfold oddExpectedCapturedGap
  calc ∑ k ∈ Finset.range rungs, oddMass rungs q k *
          strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap)
      ≤ ∑ k ∈ Finset.range rungs, 2 * q *
          strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap) :=
        Finset.sum_le_sum hterm
    _ = q * (2 * ∑ k ∈ Finset.range rungs,
          strictPriorityCapturedGap gap action ((2 * (k : ℝ) + 1) * gap)) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ q * action := mul_le_mul_of_nonneg_left hcover hq

/-- The opponent's return is exactly the cost ratio times the action at each of
its own rungs. -/
theorem oddExpectedCapturedGap_at_even
    {gap q : ℝ} {rungs m : ℕ} (hgap : 0 ≤ gap) (hm : m < rungs) :
    oddExpectedCapturedGap gap rungs q (2 * (m : ℝ) * gap) =
      q * (2 * (m : ℝ) * gap) := by
  have hlow : ∀ k ∈ Finset.Ico 0 m,
      oddMass rungs q k *
          strictPriorityCapturedGap gap (2 * (m : ℝ) * gap)
            ((2 * (k : ℝ) + 1) * gap) = 2 * q * gap := by
    intro k hk
    obtain ⟨-, hkm⟩ := Finset.mem_Ico.mp hk
    have hmass : oddMass rungs q k = 2 * q := by
      have hne : k + 1 ≠ rungs := by omega
      have hlt : k < rungs := by omega
      simp [oddMass, hne, hlt]
    have hkr : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm
    have hcell : strictPriorityCapturedGap gap (2 * (m : ℝ) * gap)
        ((2 * (k : ℝ) + 1) * gap) = gap := by
      unfold strictPriorityCapturedGap
      rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith)]
    rw [hmass, hcell]
  have hhigh : ∀ k ∈ Finset.Ico m rungs,
      oddMass rungs q k *
          strictPriorityCapturedGap gap (2 * (m : ℝ) * gap)
            ((2 * (k : ℝ) + 1) * gap) = 0 := by
    intro k hk
    obtain ⟨hmk, -⟩ := Finset.mem_Ico.mp hk
    have hkr : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hcell : strictPriorityCapturedGap gap (2 * (m : ℝ) * gap)
        ((2 * (k : ℝ) + 1) * gap) = 0 := by
      unfold strictPriorityCapturedGap
      rw [max_eq_right (by nlinarith), min_eq_left hgap]
    rw [hcell, mul_zero]
  unfold oddExpectedCapturedGap
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) (le_of_lt hm),
    Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh]
  simp only [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
  ring

/-- Shifting the action by one band turns an even cell into an odd one. -/
theorem strictPriorityCapturedGap_even_shift
    {gap action : ℝ} (hgap : 0 ≤ gap) (haction : 0 ≤ action) (k : ℕ) :
    strictPriorityCapturedGap gap action (2 * ((k : ℝ) + 1) * gap) =
      strictPriorityCapturedGap gap (max (action - gap) 0)
        ((2 * (k : ℝ) + 1) * gap) := by
  rcases le_or_gt gap action with hbig | hsmall
  · rw [max_eq_left (by linarith)]
    unfold strictPriorityCapturedGap
    congr 2
    ring
  · rw [max_eq_right (by linarith)]
    unfold strictPriorityCapturedGap
    have hkNonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [max_eq_right (by nlinarith), max_eq_right (by nlinarith)]

/-- **The advantaged player never beats its own payoff.**  Its return is at
most the cost ratio times the action, plus one band's worth of the residual net
of the cost ratio. -/
theorem evenExpectedCapturedGap_le
    {gap q action : ℝ} {rungs : ℕ} (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (hrungs : 1 ≤ rungs)
    (hupper : q ≤ profileResidual rungs q) (haction : 0 ≤ action) :
    evenExpectedCapturedGap gap rungs q action ≤
      q * action + gap * (profileResidual rungs q - q) := by
  obtain ⟨cells, rfl⟩ := Nat.exists_eq_add_of_le hrungs
  rw [show 1 + cells = cells + 1 by ring] at *
  have hshifted : (0 : ℝ) ≤ max (action - gap) 0 := le_max_right _ _
  have hzero : evenMass (cells + 1) q 0 *
      strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) =
        profileResidual (cells + 1) q * min action gap := by
    have hmass : evenMass (cells + 1) q 0 = profileResidual (cells + 1) q := by
      simp [evenMass]
    have hcell : strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) =
        min action gap := by
      unfold strictPriorityCapturedGap
      push_cast
      rw [show action - 2 * 0 * gap = action by ring, max_eq_left haction]
    rw [hmass, hcell]
  have hrest : ∀ k ∈ Finset.range cells,
      evenMass (cells + 1) q (k + 1) *
          strictPriorityCapturedGap gap action (2 * ((k : ℝ) + 1) * gap) =
        2 * q * strictPriorityCapturedGap gap (max (action - gap) 0)
          ((2 * (k : ℝ) + 1) * gap) := by
    intro k hk
    have hklt : k < cells := Finset.mem_range.mp hk
    have hmass : evenMass (cells + 1) q (k + 1) = 2 * q := by
      have hlt : k + 1 < cells + 1 := by omega
      simp [evenMass, hlt]
    rw [hmass, strictPriorityCapturedGap_even_shift hgap haction k]
  have hcover := two_mul_sum_oddCell_le hgap hshifted cells
  have hsplit : evenExpectedCapturedGap gap (cells + 1) q action =
      (∑ k ∈ Finset.range cells, evenMass (cells + 1) q (k + 1) *
          strictPriorityCapturedGap gap action (2 * ((k : ℝ) + 1) * gap)) +
        evenMass (cells + 1) q 0 *
          strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) := by
    unfold evenExpectedCapturedGap
    rw [Finset.sum_range_succ']
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    push_cast
    ring
  rw [hsplit, Finset.sum_congr rfl hrest, hzero, ← Finset.mul_sum]
  have hbound : 2 * q * (∑ k ∈ Finset.range cells,
      strictPriorityCapturedGap gap (max (action - gap) 0)
        ((2 * (k : ℝ) + 1) * gap)) ≤ q * max (action - gap) 0 := by
    nlinarith [hcover, hq]
  have hmin : min action gap ≤ action := min_le_left _ _
  have hminGap : min action gap ≤ gap := min_le_right _ _
  rcases le_or_gt gap action with hbig | hsmall
  · rw [max_eq_left (by linarith), min_eq_right hbig] at *
    nlinarith [hbound]
  · rw [max_eq_right (by linarith), min_eq_left (le_of_lt hsmall)] at *
    nlinarith [hbound, hupper]

/-- The advantaged player's return attains its bound at each of its own
rungs. -/
theorem evenExpectedCapturedGap_at_odd
    {gap q : ℝ} {rungs m : ℕ} (hgap : 0 ≤ gap) (hm : m < rungs) :
    evenExpectedCapturedGap gap rungs q ((2 * (m : ℝ) + 1) * gap) =
      q * ((2 * (m : ℝ) + 1) * gap) + gap * (profileResidual rungs q - q) := by
  have hlow : ∀ k ∈ Finset.Ico 0 (m + 1),
      evenMass rungs q k *
          strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
            (2 * (k : ℝ) * gap) = evenMass rungs q k * gap := by
    intro k hk
    obtain ⟨-, hkm⟩ := Finset.mem_Ico.mp hk
    have hkr : (k : ℝ) ≤ (m : ℝ) := by
      have : k ≤ m := by omega
      exact_mod_cast this
    have hcell : strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
        (2 * (k : ℝ) * gap) = gap := by
      unfold strictPriorityCapturedGap
      rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith)]
    rw [hcell]
  have hhigh : ∀ k ∈ Finset.Ico (m + 1) rungs,
      evenMass rungs q k *
          strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
            (2 * (k : ℝ) * gap) = 0 := by
    intro k hk
    obtain ⟨hmk, -⟩ := Finset.mem_Ico.mp hk
    have hkr : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
    have hcell : strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
        (2 * (k : ℝ) * gap) = 0 := by
      unfold strictPriorityCapturedGap
      rw [max_eq_right (by nlinarith), min_eq_left hgap]
    rw [hcell, mul_zero]
  have hmasses : ∑ k ∈ Finset.Ico 0 (m + 1), evenMass rungs q k =
      profileResidual rungs q + 2 * q * (m : ℝ) := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ']
    have hzero : evenMass rungs q 0 = profileResidual rungs q := by
      simp [evenMass]
    have hrest : ∀ k ∈ Finset.range m, evenMass rungs q (k + 1) = 2 * q := by
      intro k hk
      have hklt : k < m := Finset.mem_range.mp hk
      have hlt : k + 1 < rungs := by omega
      simp [evenMass, hlt]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hzero]
    ring
  unfold evenExpectedCapturedGap
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) hm,
    Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh,
    ← Finset.sum_mul, hmasses]
  simp only [Finset.sum_const_zero, add_zero, profileResidual]
  ring

/-! ### The window, and the equilibrium

The two conditions on the residual are the paper's window written on the mass
scale: the residual is at most twice the cost ratio exactly when the cost ratio
is at least `1/(2 nu)`, and at least the cost ratio exactly when it is at most
`1/(2 nu - 1)`. -/

theorem profileResidual_le_two_mul_iff (rungs : ℕ) (q : ℝ) :
    profileResidual rungs q ≤ 2 * q ↔ 1 ≤ 2 * q * (rungs : ℝ) := by
  unfold profileResidual
  constructor <;> intro h <;> nlinarith

theorem le_profileResidual_iff (rungs : ℕ) (q : ℝ) :
    q ≤ profileResidual rungs q ↔ (2 * (rungs : ℝ) - 1) * q ≤ 1 := by
  unfold profileResidual
  constructor <;> intro h <;> nlinarith

/-- The advantaged player's payoff in the paper's form. -/
theorem profileResidual_sub (rungs : ℕ) (q : ℝ) :
    profileResidual rungs q - q = 1 - (2 * (rungs : ℝ) - 1) * q := by
  unfold profileResidual
  ring

/-- **The displayed profiles are equilibria.**  On the closed window both
best-response conditions hold: the opponent never beats zero and is indifferent
across its own rungs, while the advantaged player never beats the band's worth
of the residual net of the cost ratio and is indifferent across its own rungs.
This is the converse half of `prop:sp_allequilibria` (iii). -/
theorem positiveProfile_equilibrium
    {gap q : ℝ} {rungs : ℕ} (hgap : 0 ≤ gap) (hq : 0 ≤ q) (hrungs : 1 ≤ rungs)
    (hwindowLow : 1 ≤ 2 * q * (rungs : ℝ))
    (hwindowHigh : (2 * (rungs : ℝ) - 1) * q ≤ 1) :
    ((∀ k, 0 ≤ oddMass rungs q k) ∧
        ∑ k ∈ Finset.range rungs, oddMass rungs q k = 1) ∧
      ((∀ k, 0 ≤ evenMass rungs q k) ∧
        ∑ k ∈ Finset.range rungs, evenMass rungs q k = 1) ∧
      (∀ action : ℝ, 0 ≤ action →
        oddExpectedCapturedGap gap rungs q action - q * action ≤ 0) ∧
      (∀ m : ℕ, m < rungs →
        oddExpectedCapturedGap gap rungs q (2 * (m : ℝ) * gap) -
          q * (2 * (m : ℝ) * gap) = 0) ∧
      (∀ action : ℝ, 0 ≤ action →
        evenExpectedCapturedGap gap rungs q action - q * action ≤
          gap * (1 - (2 * (rungs : ℝ) - 1) * q)) ∧
      (∀ m : ℕ, m < rungs →
        evenExpectedCapturedGap gap rungs q ((2 * (m : ℝ) + 1) * gap) -
          q * ((2 * (m : ℝ) + 1) * gap) =
            gap * (1 - (2 * (rungs : ℝ) - 1) * q)) := by
  have hlower : profileResidual rungs q ≤ 2 * q :=
    (profileResidual_le_two_mul_iff rungs q).mpr hwindowLow
  have hupper : q ≤ profileResidual rungs q :=
    (le_profileResidual_iff rungs q).mpr hwindowHigh
  have hnonneg : 0 ≤ profileResidual rungs q := le_trans hq hupper
  have hshape := profileResidual_sub rungs q
  refine ⟨⟨fun k => oddMass_nonneg rungs hq hnonneg k, sum_oddMass rungs hrungs q⟩,
    ⟨fun k => evenMass_nonneg rungs hq hnonneg k, sum_evenMass rungs hrungs q⟩,
    fun action haction => by
      have := oddExpectedCapturedGap_le (rungs := rungs) hgap hq hlower haction
      linarith,
    fun m hm => by
      rw [oddExpectedCapturedGap_at_even (q := q) hgap hm]
      ring,
    fun action haction => by
      have := evenExpectedCapturedGap_le (rungs := rungs) hgap hq hrungs hupper
        haction
      rw [hshape] at this
      linarith,
    fun m hm => by
      rw [evenExpectedCapturedGap_at_odd (q := q) hgap hm, hshape]
      ring⟩

/-! ### The boundary family

At the window's lower edge the advantaged player's masses are all twice the
cost ratio, since the residual then equals `2q`.  The opponent gains one more
rung and a free parameter: it moves mass `t` from that top rung down to the
origin.  Every member of the family is an equilibrium, with the advantaged
player's payoff the band times `t`. -/

/-- The opponent's mass at the even rung `2k` in the boundary family. -/
def boundaryEvenMass (rungs : ℕ) (q t : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then q + t
  else if k < rungs then 2 * q
  else if k = rungs then q - t else 0

theorem sum_boundaryEvenMass (rungs : ℕ) (hrungs : 1 ≤ rungs) (q t : ℝ) :
    ∑ k ∈ Finset.range (rungs + 1), boundaryEvenMass rungs q t k =
      2 * q * (rungs : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrungs
  rw [show 1 + m = m + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ']
  have htop : boundaryEvenMass (m + 1) q t (m + 1) = q - t := by
    simp [boundaryEvenMass]
  have hzero : boundaryEvenMass (m + 1) q t 0 = q + t := by
    simp [boundaryEvenMass]
  have hrest : ∀ k ∈ Finset.range m,
      boundaryEvenMass (m + 1) q t (k + 1) = 2 * q := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    have hlt : k + 1 < m + 1 := by omega
    simp [boundaryEvenMass, hlt]
  rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hzero, htop]
  push_cast
  ring

/-- Each mass past the origin is at most twice the cost ratio. -/
theorem boundaryEvenMass_le {rungs : ℕ} {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t)
    (k : ℕ) : boundaryEvenMass rungs q t (k + 1) ≤ 2 * q := by
  have hne : k + 1 ≠ 0 := by omega
  unfold boundaryEvenMass
  rw [if_neg hne]
  split_ifs <;> linarith

/-- The opponent's return in the boundary family. -/
def boundaryEvenExpectedCapturedGap
    (gap : ℝ) (rungs : ℕ) (q t action : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (rungs + 1),
    boundaryEvenMass rungs q t k *
      strictPriorityCapturedGap gap action (2 * (k : ℝ) * gap)

/-- **The advantaged player never beats the band times `t`.** -/
theorem boundaryEvenExpectedCapturedGap_le
    {gap q t action : ℝ} {rungs : ℕ} (hgap : 0 ≤ gap) (hq : 0 ≤ q)
    (ht : 0 ≤ t) (haction : 0 ≤ action) :
    boundaryEvenExpectedCapturedGap gap rungs q t action ≤
      q * action + gap * t := by
  have hshifted : (0 : ℝ) ≤ max (action - gap) 0 := le_max_right _ _
  have hzero : boundaryEvenMass rungs q t 0 *
      strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) =
        (q + t) * min action gap := by
    have hmass : boundaryEvenMass rungs q t 0 = q + t := by
      simp [boundaryEvenMass]
    have hcell : strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) =
        min action gap := by
      unfold strictPriorityCapturedGap
      push_cast
      rw [show action - 2 * 0 * gap = action by ring, max_eq_left haction]
    rw [hmass, hcell]
  have hrest : ∀ k ∈ Finset.range rungs,
      boundaryEvenMass rungs q t (k + 1) *
          strictPriorityCapturedGap gap action (2 * ((k : ℝ) + 1) * gap) ≤
        2 * q * strictPriorityCapturedGap gap (max (action - gap) 0)
          ((2 * (k : ℝ) + 1) * gap) := by
    intro k _
    rw [strictPriorityCapturedGap_even_shift hgap haction k]
    exact mul_le_mul_of_nonneg_right (boundaryEvenMass_le hq ht k)
      (strictPriorityCapturedGap_nonneg hgap)
  have hcover := two_mul_sum_oddCell_le hgap hshifted rungs
  have hsplit : boundaryEvenExpectedCapturedGap gap rungs q t action =
      (∑ k ∈ Finset.range rungs, boundaryEvenMass rungs q t (k + 1) *
          strictPriorityCapturedGap gap action (2 * ((k : ℝ) + 1) * gap)) +
        boundaryEvenMass rungs q t 0 *
          strictPriorityCapturedGap gap action (2 * ((0 : ℕ) : ℝ) * gap) := by
    unfold boundaryEvenExpectedCapturedGap
    rw [Finset.sum_range_succ']
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    push_cast
    ring
  have hsumBound := Finset.sum_le_sum hrest
  rw [← Finset.mul_sum] at hsumBound
  have hbound : 2 * q * (∑ k ∈ Finset.range rungs,
      strictPriorityCapturedGap gap (max (action - gap) 0)
        ((2 * (k : ℝ) + 1) * gap)) ≤ q * max (action - gap) 0 := by
    nlinarith [hcover, hq]
  rw [hsplit, hzero]
  rcases le_or_gt gap action with hbig | hsmall
  · rw [max_eq_left (by linarith), min_eq_right hbig] at *
    nlinarith [hsumBound, hbound]
  · rw [max_eq_right (by linarith), min_eq_left (le_of_lt hsmall)] at *
    nlinarith [hsumBound, hbound, ht]

/-- The bound is attained at each of the advantaged player's rungs. -/
theorem boundaryEvenExpectedCapturedGap_at_odd
    {gap q t : ℝ} {rungs m : ℕ} (hgap : 0 ≤ gap) (hm : m < rungs) :
    boundaryEvenExpectedCapturedGap gap rungs q t ((2 * (m : ℝ) + 1) * gap) =
      q * ((2 * (m : ℝ) + 1) * gap) + gap * t := by
  have hlow : ∀ k ∈ Finset.Ico 0 (m + 1),
      boundaryEvenMass rungs q t k *
          strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
            (2 * (k : ℝ) * gap) = boundaryEvenMass rungs q t k * gap := by
    intro k hk
    obtain ⟨-, hkm⟩ := Finset.mem_Ico.mp hk
    have hkr : (k : ℝ) ≤ (m : ℝ) := by
      have : k ≤ m := by omega
      exact_mod_cast this
    have hcell : strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
        (2 * (k : ℝ) * gap) = gap := by
      unfold strictPriorityCapturedGap
      rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith)]
    rw [hcell]
  have hhigh : ∀ k ∈ Finset.Ico (m + 1) (rungs + 1),
      boundaryEvenMass rungs q t k *
          strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
            (2 * (k : ℝ) * gap) = 0 := by
    intro k hk
    obtain ⟨hmk, -⟩ := Finset.mem_Ico.mp hk
    have hkr : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
    have hcell : strictPriorityCapturedGap gap ((2 * (m : ℝ) + 1) * gap)
        (2 * (k : ℝ) * gap) = 0 := by
      unfold strictPriorityCapturedGap
      rw [max_eq_right (by nlinarith), min_eq_left hgap]
    rw [hcell, mul_zero]
  have hmasses : ∑ k ∈ Finset.Ico 0 (m + 1), boundaryEvenMass rungs q t k =
      q + t + 2 * q * (m : ℝ) := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ']
    have hzero : boundaryEvenMass rungs q t 0 = q + t := by
      simp [boundaryEvenMass]
    have hrest : ∀ k ∈ Finset.range m,
        boundaryEvenMass rungs q t (k + 1) = 2 * q := by
      intro k hk
      have hklt : k < m := Finset.mem_range.mp hk
      have hlt : k + 1 < rungs := by omega
      simp [boundaryEvenMass, hlt]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hzero]
    ring
  unfold boundaryEvenExpectedCapturedGap
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega : m + 1 ≤ rungs + 1),
    Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh,
    ← Finset.sum_mul, hmasses]
  simp only [Finset.sum_const_zero, add_zero]
  ring

theorem boundaryEvenMass_nonneg {rungs : ℕ} {q t : ℝ} (hq : 0 ≤ q)
    (ht : 0 ≤ t) (htq : t ≤ q) (k : ℕ) : 0 ≤ boundaryEvenMass rungs q t k := by
  unfold boundaryEvenMass
  split_ifs <;> linarith

/-- At the window's lower edge the residual is exactly twice the cost ratio. -/
theorem profileResidual_at_boundary {rungs : ℕ} {q : ℝ}
    (hboundary : 2 * q * (rungs : ℝ) = 1) :
    profileResidual rungs q = 2 * q := by
  unfold profileResidual
  linarith [hboundary]

/-- **The boundary family are equilibria.**  At the window's lower edge the
opponent may move any mass up to the cost ratio from its top rung down to the
origin, and every member of the resulting family is an equilibrium with the
advantaged player's payoff the contested band times that mass. -/
theorem boundaryProfile_equilibrium
    {gap q t : ℝ} {rungs : ℕ} (hgap : 0 ≤ gap) (hq : 0 ≤ q) (hrungs : 1 ≤ rungs)
    (hboundary : 2 * q * (rungs : ℝ) = 1) (ht : 0 ≤ t) (htq : t ≤ q) :
    ((∀ k, 0 ≤ oddMass rungs q k) ∧
        ∑ k ∈ Finset.range rungs, oddMass rungs q k = 1) ∧
      ((∀ k, 0 ≤ boundaryEvenMass rungs q t k) ∧
        ∑ k ∈ Finset.range (rungs + 1), boundaryEvenMass rungs q t k = 1) ∧
      (∀ action : ℝ, 0 ≤ action →
        oddExpectedCapturedGap gap rungs q action - q * action ≤ 0) ∧
      (∀ m : ℕ, m < rungs →
        oddExpectedCapturedGap gap rungs q (2 * (m : ℝ) * gap) -
          q * (2 * (m : ℝ) * gap) = 0) ∧
      (∀ action : ℝ, 0 ≤ action →
        boundaryEvenExpectedCapturedGap gap rungs q t action - q * action ≤
          gap * t) ∧
      (∀ m : ℕ, m < rungs →
        boundaryEvenExpectedCapturedGap gap rungs q t ((2 * (m : ℝ) + 1) * gap) -
          q * ((2 * (m : ℝ) + 1) * gap) = gap * t) := by
  have hres := profileResidual_at_boundary (rungs := rungs) (q := q) hboundary
  have hlower : profileResidual rungs q ≤ 2 * q := le_of_eq hres
  have hnonneg : 0 ≤ profileResidual rungs q := by rw [hres]; linarith
  refine ⟨⟨fun k => oddMass_nonneg rungs hq hnonneg k,
      sum_oddMass rungs hrungs q⟩,
    ⟨fun k => boundaryEvenMass_nonneg hq ht htq k, ?_⟩,
    fun action haction => by
      have := oddExpectedCapturedGap_le (rungs := rungs) hgap hq hlower haction
      linarith,
    fun m hm => by
      rw [oddExpectedCapturedGap_at_even (q := q) hgap hm]
      ring,
    fun action haction => by
      have := boundaryEvenExpectedCapturedGap_le (rungs := rungs) hgap hq ht
        haction
      linarith,
    fun m hm => by
      rw [boundaryEvenExpectedCapturedGap_at_odd (q := q) (t := t) hgap hm]
      ring⟩
  rw [sum_boundaryEvenMass rungs hrungs q t]
  exact hboundary

end

end SmoothingCliff.Racing
