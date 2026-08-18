import SmoothingCliff.Mechanism.GeneralIntensity
import SmoothingCliff.Mechanism.OneSlotStability
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Structure of the published certificate

Remark `rem:constant` reads four claims off the certificate of
`thm:stability`: the bound sees the slot profile only through the top weight
and never through the total mass, the decrements telescope to that top weight,
the constant is uniform over slot counts and opponent profiles, and the naive
per-slot bound it improves on is larger by the factor `e ∑ w_p / w₁`.  The
remark closes by recording that at one slot the exact constant is `w₁/(4τ)`,
below the general certificate.

The first and third claims are negative ones, about what the bound does not
depend on.  A tautological rendering, that two profiles with the same top
weight give the same number, would say nothing, so they are stated here as a
worked contrast instead: a flat profile of `K` slots and a single-slot profile
carry the same certificate although their masses differ by a factor of `K`.
-/

namespace SmoothingCliff.Mechanism

open scoped BigOperators

/-! ### The decrements telescope -/

/-- Summation by parts leaves the top weight: with the profile terminating at
`slots`, the decrements `w_p - w_{p+1}` sum to `w 0`.  This is why the
certificate carries `w 0` and not `∑_p w_p`. -/
theorem sum_decrements_eq_top (w : ℕ → ℝ) (slots : ℕ) (hTerminal : w slots = 0) :
    ∑ p ∈ Finset.range slots, (w p - w (p + 1)) = w 0 := by
  rw [Finset.sum_range_sub' w slots, hTerminal, sub_zero]

/-! ### The certificate sees only the top weight -/

/-- A flat profile of `K` slots at weight `W`, terminating at `K`. -/
noncomputable def flatProfile (W : ℝ) (slots : ℕ) : ℕ → ℝ :=
  fun p => if p < slots then W else 0

theorem flatProfile_antitone {W : ℝ} (hW : 0 ≤ W) (slots : ℕ) :
    Antitone (flatProfile W slots) := by
  intro p q hpq
  unfold flatProfile
  by_cases hq : q < slots
  · rw [if_pos hq, if_pos (lt_of_le_of_lt hpq hq)]
  · rw [if_neg hq]
    by_cases hp : p < slots
    · rw [if_pos hp]; exact hW
    · rw [if_neg hp]

@[simp] theorem flatProfile_terminal (W : ℝ) (slots : ℕ) :
    flatProfile W slots slots = 0 := by
  simp [flatProfile]

theorem flatProfile_top {W : ℝ} {slots : ℕ} (hslots : 0 < slots) :
    flatProfile W slots 0 = W := by
  simp [flatProfile, hslots]

/-- The total mass of a flat profile grows with the slot count. -/
theorem flatProfile_mass (W : ℝ) (slots : ℕ) :
    ∑ p ∈ Finset.range slots, flatProfile W slots p = slots * W := by
  have hpt : ∀ p ∈ Finset.range slots, flatProfile W slots p = W := by
    intro p hp
    simp [flatProfile, Finset.mem_range.mp hp]
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The mass does not enter.**  A flat profile of `K` slots and a single-slot
profile at the same top weight satisfy the certificate with the same constant,
although their masses are `K W` and `W`.  Stating the claim as a contrast
rather than as an identity keeps it from being vacuous. -/
theorem certificate_independent_of_mass {W reserve temperature : ℝ}
    (hW : 0 ≤ W) (hTemperature : 0 < temperature) (slots : ℕ) (hslots : 0 < slots)
    (stats : ConditionedOpponentOrderStats) (a b : ℝ) :
    |conditionalBidPriority (flatProfile W slots) slots stats reserve temperature b -
        conditionalBidPriority (flatProfile W slots) slots stats reserve temperature a|
      ≤ W / (Real.exp 1 * temperature) * |b - a| ∧
    |conditionalBidPriority (flatProfile W 1) 1 stats reserve temperature b -
        conditionalBidPriority (flatProfile W 1) 1 stats reserve temperature a|
      ≤ W / (Real.exp 1 * temperature) * |b - a| := by
  constructor
  · have h := exponential_certificate (flatProfile W slots) slots stats
      (reserve := reserve) hTemperature
      (flatProfile_antitone hW slots) (flatProfile_terminal W slots) a b
    rwa [flatProfile_top hslots] at h
  · have h := exponential_certificate (flatProfile W 1) 1 stats
      (reserve := reserve) hTemperature
      (flatProfile_antitone hW 1) (flatProfile_terminal W 1) a b
    rwa [flatProfile_top Nat.one_pos] at h

/-! ### The factor over the naive per-slot bound -/

/-- The naive bound adds one `w_p/τ` per slot.  Against the certificate
`w₁/(e τ)` it is larger by exactly `e ∑_p w_p / w₁`, so a designer targeting a
fixed certificate may publish a temperature lower by that factor. -/
theorem naive_bound_ratio {mass top temperature : ℝ} (hTop : 0 < top)
    (hTemperature : 0 < temperature) :
    (mass / temperature) / (top / (Real.exp 1 * temperature))
      = Real.exp 1 * mass / top := by
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  field_simp

/-! ### One slot against the general certificate -/

/-- At one slot the exact constant `w₁/(4τ)` of `cor:tight-K1` is strictly
below the general certificate `w₁/(e τ)`, because `e < 4`. -/
theorem oneSlot_constant_lt_general {weight temperature : ℝ} (hWeight : 0 < weight)
    (hTemperature : 0 < temperature) :
    weight / (4 * temperature) < weight / (Real.exp 1 * temperature) := by
  have hexp : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hexppos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  apply div_lt_div_of_pos_left hWeight
  · positivity
  · nlinarith

end SmoothingCliff.Mechanism
