import SmoothingCliff.Frontier.WaterFilling

/-!
# The consistency gap: three-bidder constants (`prop:rho3`)

Formal content of Proposition `prop:rho3` in `Smoothing_the_Cliff_ITCS.tex`.

Certified here:
* the (T5) shortfall bridge, in normalized and in `(w₁, 𝒮)` units: shortfalls
  `a, b ≥ 0` with `6a + b ≥ w₁²/(48𝒮)` force `max a b ≥ w₁²/(336𝒮)`;
* the upper bound: one-slot welfare of any feasible rule never exceeds the
  strict-priority value, so at every profile the gap of water-filling to the
  class frontier is at most `w₁²/(4𝒮)`.

NOT formalized here, on their original credentials (see the manifest):
* the derivation of (T5) for every rule in `𝒞` (prose proof of
  `prop:threebidders`);
* the attainment claims (T6)/(T7), whose second witness is the 19×19 rational
  certificate checked by exact Python arithmetic
  (`n3_witness/verify_rational_witness.py`).
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

/-- The (T5) bridge in normalized units (`w₁ = 𝒮 = 1`): shortfalls obeying the
printed tradeoff `6a + b ≥ 1/48` cannot both be below `1/336`. -/
theorem shortfall_bridge {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hT5 : 1 / 48 ≤ 6 * a + b) : 1 / 336 ≤ max a b := by
  have hA : a ≤ max a b := le_max_left a b
  have hB : b ≤ max a b := le_max_right a b
  linarith

/-- The (T5) bridge in physical units: bids in `w₁/𝒮`, welfare in `w₁²/𝒮`. -/
theorem shortfall_bridge_units
    (weight sensitivity a b : ℝ)
    (hsens : 0 < sensitivity) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hT5 : weight ^ 2 / (48 * sensitivity) ≤ 6 * a + b) :
    weight ^ 2 / (336 * sensitivity) ≤ max a b := by
  have hA : a ≤ max a b := le_max_left a b
  have hB : b ≤ max a b := le_max_right a b
  have hkey : weight ^ 2 / (336 * sensitivity) =
      (weight ^ 2 / (48 * sensitivity)) / 7 := by
    field_simp
    ring
  rw [hkey]
  linarith

/-- One-slot welfare of any feasible rule is at most the strict-priority
value `w₁ · b_{(1)}`. -/
theorem oneSlot_welfare_le_strictPriority
    {ι : Type*} [Fintype ι] {reserve : ℝ} (hres : 0 ≤ reserve)
    (weight : ℝ) (x : InterimRule ι reserve)
    (hFeas : OneSlotFeasible weight x)
    (b : EligibleProfile ι reserve) (leader : ι)
    (hleader : ∀ i, (b i : ℝ) ≤ (b leader : ℝ)) :
    welfare x b ≤ weight * (b leader : ℝ) := by
  have hlead0 : (0 : ℝ) ≤ (b leader : ℝ) := le_trans hres (b leader).2
  calc welfare x b = ∑ i, (b i : ℝ) * x b i := rfl
    _ ≤ ∑ i, (b leader : ℝ) * x b i := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (hleader i) (hFeas.1 b i)
    _ = (b leader : ℝ) * ∑ i, x b i := by rw [Finset.mul_sum]
    _ ≤ (b leader : ℝ) * weight :=
        mul_le_mul_of_nonneg_left (hFeas.2 b) hlead0
    _ = weight * (b leader : ℝ) := mul_comm _ _

/-- Upper bound of `prop:rho3`: at every profile, every feasible one-slot rule
outperforms water-filling by at most `w₁²/(4𝒮)`; hence the consistency gap of
water-filling, and so `ρ_n(𝒮)`, is at most `w₁²/(4𝒮)`. -/
theorem rho3_upper_certificate
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {reserve : ℝ}
    (hres : 0 ≤ reserve)
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity)
    (y : InterimRule ι reserve) (hy : OneSlotFeasible (weight : ℝ) y)
    (b : EligibleProfile ι reserve) (leader : ι)
    (hleader : ∀ i, (b i : ℝ) ≤ (b leader : ℝ)) :
    welfare y b - welfare (waterFillingRule weight sensitivity hsens) b ≤
      (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  have h1 := oneSlot_welfare_le_strictPriority hres (weight : ℝ) y hy
    b leader hleader
  have h2 := waterFillingRule_welfare_loss_le weight sensitivity hweight hsens
    b leader hleader
  linarith

end SmoothingCliff.Frontier
