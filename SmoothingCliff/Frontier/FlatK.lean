import SmoothingCliff.Frontier.WaterFilling
import Mathlib.Algebra.Order.Chebyshev

/-!
# The inclusion-case capacity law (`prop:flatK`)

Formalization of Proposition `prop:flatK` in `Smoothing_the_Cliff_ITCS.tex`:
flat weights `w_p ≡ w₁` on `K` slots, per-agent cap `w₁`, total mass `K·w₁`.

* `flatK_leader_lower_bound_certificate` / `flatK_trailer_lower_bound_certificate`
  are part (i): the two-block adversarial profiles at the optimizing gaps.
* `flatK_waterFilling_loss_le` is the displaced-mass upper bound of part (ii).
* `flatK_twoBlock_mass` and `flatK_twoBlock_loss_eq` are the attainment half
  of part (ii): at the extremal two-block profile the `K`-slot water-filling
  mass identity holds at threshold `reserve`, and the loss equals the bound.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

open SmoothingCliff

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}

/-- Flat-`K` feasibility: nonnegative weights, per-agent cap, total mass at
most `slots · weight`. -/
def FlatKFeasible (slots : ℕ) (weight : ℝ)
    (x : InterimRule ι reserve) : Prop :=
  (∀ b i, 0 ≤ x b i) ∧ (∀ b i, x b i ≤ weight) ∧
    ∀ b, ∑ i, x b i ≤ (slots : ℝ) * weight

/-- Flat-`K` no waste: the rule assigns the full mass `slots · weight`. -/
def FlatKNoWaste (slots : ℕ) (weight : ℝ)
    (x : InterimRule ι reserve) : Prop :=
  ∀ b, ∑ i, x b i = (slots : ℝ) * weight

/-- Two-block eligible profile: agents in `T` bid `reserve + hi`, the rest
`reserve + lo`. -/
def blockProfile (reserve : ℝ) (T : Finset ι) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) : EligibleProfile ι reserve :=
  fun i => if i ∈ T then ⟨reserve + hi, le_add_of_nonneg_right hhi⟩
    else ⟨reserve + lo, le_add_of_nonneg_right hlo⟩

theorem blockProfile_coe (reserve : ℝ) (T : Finset ι) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (i : ι) :
    ((blockProfile reserve T lo hi hlo hhi i : EligibleBid reserve) : ℝ) =
      reserve + (if i ∈ T then hi else lo) := by
  unfold blockProfile
  by_cases hiT : i ∈ T <;> simp [hiT]

/-- The leader-bound optimizing gap `(n-K)·w₁ / (2n𝒮)`. -/
noncomputable def flatKLeaderDelta (n slots : ℕ)
    (weight sensitivity : NNReal) : ℝ :=
  (((n : ℝ) - slots) * weight) / (2 * n * sensitivity)

/-- The trailer-bound optimizing gap `K·w₁ / (2n𝒮)`. -/
noncomputable def flatKTrailerDelta (n slots : ℕ)
    (weight sensitivity : NNReal) : ℝ :=
  ((slots : ℝ) * weight) / (2 * (n : ℝ) * sensitivity)

theorem flatKLeaderDelta_nonneg (n slots : ℕ) (hslots : slots ≤ n)
    (weight sensitivity : NNReal) :
    0 ≤ flatKLeaderDelta n slots weight sensitivity := by
  unfold flatKLeaderDelta
  have hcast : (slots : ℝ) ≤ (n : ℝ) := by exact_mod_cast hslots
  have hnum : 0 ≤ ((n : ℝ) - slots) * weight :=
    mul_nonneg (by linarith) weight.coe_nonneg
  have hden : 0 ≤ 2 * (n : ℝ) * sensitivity := by positivity
  exact div_nonneg hnum hden

theorem flatKTrailerDelta_nonneg (n slots : ℕ)
    (weight sensitivity : NNReal) :
    0 ≤ flatKTrailerDelta n slots weight sensitivity := by
  unfold flatKTrailerDelta
  positivity

/-- Part (i), leader bound: on the profile with the `T`-block
`flatKLeaderDelta` above the rest, every rule in the flat-weight class `𝒞`
loses at least `K(n-K)²/n² · w₁²/(4𝒮)` against strict priority. -/
theorem flatK_leader_lower_bound_certificate
    (hres : 0 ≤ reserve)
    (slots : ℕ) (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hslots : 0 < slots) (hlt : slots < Fintype.card ι)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x) (hOwn : OwnMonotone x)
    (hCross : CrossMonotone x) (hLip : OwnLipschitz sensitivity x)
    (hFeas : FlatKFeasible slots (weight : ℝ) x)
    (T : Finset ι) (hT : T.card = slots) :
    (slots : ℝ) * weight *
        (reserve + flatKLeaderDelta (Fintype.card ι) slots weight sensitivity) -
      welfare x (blockProfile reserve T 0
        (flatKLeaderDelta (Fintype.card ι) slots weight sensitivity)
        le_rfl
        (flatKLeaderDelta_nonneg (Fintype.card ι) slots hlt.le
          weight sensitivity)) ≥
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) ^ 2 /
          ((Fintype.card ι : ℝ)) ^ 2 *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  have hnposN : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnposN
  have hslotsn : (slots : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hlt.le
  have hsne : (sensitivity : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hsens)
  set Δ : ℝ := flatKLeaderDelta (Fintype.card ι) slots weight sensitivity
    with hΔdef
  have hΔ0 : 0 ≤ Δ :=
    flatKLeaderDelta_nonneg (Fintype.card ι) slots hlt.le weight sensitivity
  set P : EligibleProfile ι reserve := blockProfile reserve T 0 Δ le_rfl hΔ0
    with hPdef
  have hPcoe : ∀ i, (P i : ℝ) = reserve + (if i ∈ T then Δ else 0) := by
    intro i
    rw [hPdef, blockProfile_coe]
  have hSubset : SubsetFeasible (fun _ => (slots : ℝ) * weight) x := by
    intro b H
    calc ∑ m ∈ H, x b m ≤ ∑ m, x b m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
          (fun m _ _ => hFeas.1 b m)
      _ ≤ (slots : ℝ) * weight := hFeas.2.2 b
  have hceil : ∀ i ∈ T, x P i ≤
      (slots : ℝ) * weight / (Fintype.card ι : ℝ) +
        (sensitivity : ℝ) * Δ := by
    intro i hiT
    have hPi : (P i : ℝ) = reserve + Δ := by
      rw [hPcoe i, if_pos hiT]
    have hz : ((⟨reserve, Set.left_mem_Ici⟩ : EligibleBid reserve) : ℝ) ≤ (P i : ℝ) := by
      rw [hPi]
      exact le_add_of_nonneg_right hΔ0
    have hAbove : ∀ m ∈ (Finset.univ : Finset ι),
        ((⟨reserve, Set.left_mem_Ici⟩ : EligibleBid reserve) : ℝ) ≤ (P m : ℝ) :=
      fun m _ => (P m).2
    have h := squeeze_ceiling_of_subset (fun _ => (slots : ℝ) * weight)
      sensitivity x hAnon hOwn hLip hCross hSubset P i Finset.univ
      (Finset.mem_univ i) ⟨reserve, Set.left_mem_Ici⟩ hz hAbove
    rw [Finset.card_univ, hPi] at h
    calc x P i ≤ (slots : ℝ) * weight / (Fintype.card ι : ℝ) +
        (sensitivity : ℝ) * (reserve + Δ -
          ((⟨reserve, Set.left_mem_Ici⟩ : EligibleBid reserve) : ℝ)) := h
      _ = (slots : ℝ) * weight / (Fintype.card ι : ℝ) +
          (sensitivity : ℝ) * Δ := by
        norm_num
  have hwelf : welfare x P ≤ reserve * ((slots : ℝ) * weight) +
      Δ * ((slots : ℝ) *
        ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
          (sensitivity : ℝ) * Δ)) := by
    have hstep : ∀ i : ι, (P i : ℝ) * x P i =
        reserve * x P i + (if i ∈ T then Δ * x P i else 0) := by
      intro i
      rw [hPcoe i]
      by_cases hiT : i ∈ T <;> simp [hiT] <;> ring
    calc welfare x P = ∑ i, (P i : ℝ) * x P i := rfl
      _ = ∑ i, (reserve * x P i + if i ∈ T then Δ * x P i else 0) :=
          Finset.sum_congr rfl fun i _ => hstep i
      _ = reserve * (∑ i, x P i) + ∑ i ∈ T, Δ * x P i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ ≤ reserve * ((slots : ℝ) * weight) +
          Δ * ((slots : ℝ) *
            ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
              (sensitivity : ℝ) * Δ)) := by
          have h1 : reserve * (∑ i, x P i) ≤
              reserve * ((slots : ℝ) * weight) :=
            mul_le_mul_of_nonneg_left (hFeas.2.2 P) hres
          have h2 : ∑ i ∈ T, Δ * x P i ≤
              Δ * ((slots : ℝ) *
                ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
                  (sensitivity : ℝ) * Δ)) := by
            calc ∑ i ∈ T, Δ * x P i ≤
                ∑ _i ∈ T, Δ * ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
                  (sensitivity : ℝ) * Δ) :=
                  Finset.sum_le_sum fun i hi =>
                    mul_le_mul_of_nonneg_left (hceil i hi) hΔ0
              _ = Δ * ((slots : ℝ) *
                  ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
                    (sensitivity : ℝ) * Δ)) := by
                  rw [Finset.sum_const, hT, nsmul_eq_mul]
                  ring
          linarith
  have hkey : Δ * (slots : ℝ) *
      (weight - (slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ) =
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) ^ 2 /
          ((Fintype.card ι : ℝ)) ^ 2 *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
    rw [hΔdef]
    unfold flatKLeaderDelta
    field_simp
    ring
  have hexpand : (slots : ℝ) * weight * (reserve + Δ) -
      (reserve * ((slots : ℝ) * weight) +
        Δ * ((slots : ℝ) *
          ((slots : ℝ) * weight / (Fintype.card ι : ℝ) +
            (sensitivity : ℝ) * Δ))) =
      Δ * (slots : ℝ) *
        (weight - (slots : ℝ) * weight / (Fintype.card ι : ℝ) -
          (sensitivity : ℝ) * Δ) := by
    ring
  linarith [hwelf, hkey.ge, hkey.le, hexpand.ge, hexpand.le]

/-- Part (i), trailer bound: on the profile with the complement of `T`
`flatKTrailerDelta` below the rest, every no-waste rule in the flat-weight
class `𝒞` loses at least `(n-K)K²/n² · w₁²/(4𝒮)`. -/
theorem flatK_trailer_lower_bound_certificate
    (hres : 0 ≤ reserve)
    (slots : ℕ) (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hslots : 0 < slots) (hlt : slots < Fintype.card ι)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x) (hOwn : OwnMonotone x)
    (hCross : CrossMonotone x) (hLip : OwnLipschitz sensitivity x)
    (hFeas : FlatKFeasible slots (weight : ℝ) x)
    (hNoWaste : FlatKNoWaste slots (weight : ℝ) x)
    (T : Finset ι) (hT : T.card = slots) :
    (slots : ℝ) * weight *
        (reserve + flatKTrailerDelta (Fintype.card ι) slots weight sensitivity) -
      welfare x (blockProfile reserve T 0
        (flatKTrailerDelta (Fintype.card ι) slots weight sensitivity)
        le_rfl
        (flatKTrailerDelta_nonneg (Fintype.card ι) slots weight sensitivity)) ≥
      ((Fintype.card ι : ℝ) - slots) * (slots : ℝ) ^ 2 /
          ((Fintype.card ι : ℝ)) ^ 2 *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  have hnposN : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnposN
  have : Nonempty ι := Fintype.card_pos_iff.mp hnposN
  have hslotsn : (slots : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hlt.le
  have hsne : (sensitivity : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hsens)
  set Δ : ℝ := flatKTrailerDelta (Fintype.card ι) slots weight sensitivity
    with hΔdef
  have hΔ0 : 0 ≤ Δ :=
    flatKTrailerDelta_nonneg (Fintype.card ι) slots weight sensitivity
  set P : EligibleProfile ι reserve := blockProfile reserve T 0 Δ le_rfl hΔ0
    with hPdef
  have hPcoe : ∀ i, (P i : ℝ) = reserve + (if i ∈ T then Δ else 0) := by
    intro i
    rw [hPdef, blockProfile_coe]
  obtain ⟨top, htopT⟩ : ∃ i, i ∈ T := by
    apply Finset.card_pos.mp
    rw [hT]
    exact hslots
  have hTopAll : ∀ m, (P m : ℝ) ≤ (P top : ℝ) := by
    intro m
    rw [hPcoe m, hPcoe top, if_pos htopT]
    by_cases hm : m ∈ T <;> simp [hm] <;> linarith
  have hfloor : ∀ j ∉ T,
      (slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ ≤ x P j := by
    intro j hjT
    have h := squeeze_floor_of_top (totalWeight := (slots : ℝ) * weight)
      sensitivity x hAnon hOwn hLip hCross hNoWaste P j top hTopAll
    have hPj : (P j : ℝ) = reserve := by
      rw [hPcoe j, if_neg hjT]
      ring
    have hPtop : (P top : ℝ) = reserve + Δ := by
      rw [hPcoe top, if_pos htopT]
    rw [hPj, hPtop] at h
    calc (slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ =
        (slots : ℝ) * weight / (Fintype.card ι : ℝ) -
          (sensitivity : ℝ) * (reserve + Δ - reserve) := by ring
      _ ≤ x P j := h
  have hwelf : welfare x P =
      (reserve + Δ) * ((slots : ℝ) * weight) -
        Δ * ∑ j ∈ Finset.univ \ T, x P j := by
    have hstep : ∀ i : ι, (P i : ℝ) * x P i =
        (reserve + Δ) * x P i -
          (if i ∈ Finset.univ \ T then Δ * x P i else 0) := by
      intro i
      rw [hPcoe i]
      by_cases hiT : i ∈ T <;>
        simp [hiT, Finset.mem_sdiff, Finset.mem_univ] <;> ring
    calc welfare x P = ∑ i, (P i : ℝ) * x P i := rfl
      _ = ∑ i, ((reserve + Δ) * x P i -
          if i ∈ Finset.univ \ T then Δ * x P i else 0) :=
          Finset.sum_congr rfl fun i _ => hstep i
      _ = (reserve + Δ) * (∑ i, x P i) -
          ∑ j ∈ Finset.univ \ T, Δ * x P j := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (reserve + Δ) * ((slots : ℝ) * weight) -
          Δ * ∑ j ∈ Finset.univ \ T, x P j := by
          rw [hNoWaste P, Finset.mul_sum]
  have hsumfloor : ((Fintype.card ι : ℝ) - slots) *
      ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ) ≤ ∑ j ∈ Finset.univ \ T, x P j := by
    have hcard : (((Finset.univ \ T).card : ℕ) : ℝ) =
        (Fintype.card ι : ℝ) - slots := by
      rw [Finset.card_univ_diff, hT, Nat.cast_sub hlt.le]
    calc ((Fintype.card ι : ℝ) - slots) *
        ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
          (sensitivity : ℝ) * Δ) =
        (((Finset.univ \ T).card : ℕ) : ℝ) *
          ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
            (sensitivity : ℝ) * Δ) := by rw [hcard]
      _ = ∑ _j ∈ Finset.univ \ T,
          ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
            (sensitivity : ℝ) * Δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.univ \ T, x P j :=
          Finset.sum_le_sum fun j hj =>
            hfloor j (Finset.mem_sdiff.mp hj).2
  have hkey : Δ * (((Fintype.card ι : ℝ) - slots) *
      ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ)) =
      ((Fintype.card ι : ℝ) - slots) * (slots : ℝ) ^ 2 /
          ((Fintype.card ι : ℝ)) ^ 2 *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
    rw [hΔdef]
    unfold flatKTrailerDelta
    field_simp
    ring
  have hΔsum : Δ * (((Fintype.card ι : ℝ) - slots) *
      ((slots : ℝ) * weight / (Fintype.card ι : ℝ) -
        (sensitivity : ℝ) * Δ)) ≤
      Δ * ∑ j ∈ Finset.univ \ T, x P j :=
    mul_le_mul_of_nonneg_left hsumfloor hΔ0
  have hgoal : (slots : ℝ) * weight * (reserve + Δ) - welfare x P =
      Δ * ∑ j ∈ Finset.univ \ T, x P j := by
    rw [hwelf]
    ring
  rw [ge_iff_le, ← hkey, hgoal]
  exact hΔsum

/-- Part (ii), displaced-mass upper bound: at any profile and any flat-`K`
water-filling threshold, the loss against the `T`-block benchmark is at most
`K(n-K)/n · w₁²/(4𝒮)` for EVERY set `T` of `K` agents; the strict-priority
welfare is the maximizing choice of `T`, so this is stronger than the printed
statement, which fixes the top-`K` set. -/
theorem flatK_waterFilling_loss_le
    (slots : ℕ) (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hslots : 0 < slots) (hlt : slots < Fintype.card ι)
    (b : EligibleProfile ι reserve) (t : ℝ)
    (ht : waterFillMass weight sensitivity (fun i => (b i : ℝ)) t =
      (slots : ℝ) * weight)
    (T : Finset ι) (hTcard : T.card = slots) :
    (∑ i ∈ T, (weight : ℝ) * (b i : ℝ)) -
      ∑ i, (b i : ℝ) *
        waterFillAt weight sensitivity (fun k => (b k : ℝ)) t i ≤
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) / (Fintype.card ι : ℝ) *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  have hnposN : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnposN
  have hKpos : (0 : ℝ) < (slots : ℝ) := by exact_mod_cast hslots
  have hnK : (0 : ℝ) < (Fintype.card ι : ℝ) - slots := by
    have : (slots : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hlt
    linarith
  have hs : (0 : ℝ) < (sensitivity : ℝ) := by exact_mod_cast hsens
  have hw0 : (0 : ℝ) ≤ (weight : ℝ) := weight.coe_nonneg
  set X : ι → ℝ := fun i =>
    waterFillAt weight sensitivity (fun k => (b k : ℝ)) t i with hX
  set y : ι → ℝ := fun i => (b i : ℝ) - t with hy
  have hXdef : ∀ i, X i = clampWeight weight ((sensitivity : ℝ) * y i) :=
    fun i => rfl
  have hX0 : ∀ i, 0 ≤ X i := fun i => by
    rw [hXdef]
    exact clampWeight_nonneg weight _
  have hXw : ∀ i, X i ≤ (weight : ℝ) := fun i => by
    rw [hXdef]
    exact clampWeight_le weight _
  have hclaimA : ∀ i, ((weight : ℝ) - X i) * y i ≤
      ((weight : ℝ) - X i) * X i / sensitivity := by
    intro i
    rcases le_total ((sensitivity : ℝ) * y i) 0 with hle | hposc
    · have hXi : X i = 0 := by
        rw [hXdef]
        exact clampWeight_eq_zero_of_nonpos weight hle
      have hyi : y i ≤ 0 := by nlinarith
      rw [hXi, sub_zero, mul_zero, zero_div]
      exact mul_nonpos_of_nonneg_of_nonpos hw0 hyi
    · rcases le_total (weight : ℝ) ((sensitivity : ℝ) * y i) with hcap | hmid
      · have hXi : X i = weight := by
          rw [hXdef]
          exact clampWeight_eq_weight_of_le weight hcap
        rw [hXi, sub_self, zero_mul, zero_mul, zero_div]
      · have hXi : X i = (sensitivity : ℝ) * y i := by
          rw [hXdef]
          exact clampWeight_eq_of_mem weight hposc hmid
        have heq : ((weight : ℝ) - X i) * y i =
            ((weight : ℝ) - X i) * X i / sensitivity := by
          rw [hXi]
          field_simp
          try ring
        exact heq.le
  have hclaimB : ∀ i, X i ^ 2 / sensitivity ≤ X i * y i := by
    intro i
    rcases le_total ((sensitivity : ℝ) * y i) 0 with hle | hposc
    · have hXi : X i = 0 := by
        rw [hXdef]
        exact clampWeight_eq_zero_of_nonpos weight hle
      rw [hXi]
      norm_num
    · rcases le_total (weight : ℝ) ((sensitivity : ℝ) * y i) with hcap | hmid
      · have hXi : X i = weight := by
          rw [hXdef]
          exact clampWeight_eq_weight_of_le weight hcap
        rw [hXi]
        rw [div_le_iff₀ hs]
        nlinarith
      · have hXi : X i = (sensitivity : ℝ) * y i := by
          rw [hXdef]
          exact clampWeight_eq_of_mem weight hposc hmid
        have heq : X i ^ 2 / sensitivity = X i * y i := by
          rw [hXi]
          field_simp
          try ring
        exact heq.le
  have hmassX : ∑ i, X i = (slots : ℝ) * weight := ht
  have hsplit : ∑ i ∈ Finset.univ \ T, X i + ∑ i ∈ T, X i = ∑ i, X i :=
    Finset.sum_sdiff (Finset.subset_univ T)
  set A : ℝ := ∑ i ∈ T, X i with hA
  set M : ℝ := ∑ i ∈ Finset.univ \ T, X i with hM
  have hAM : A + M = (slots : ℝ) * weight := by
    rw [hA, hM]
    linarith [hsplit, hmassX]
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => hX0 i
  have hbty : ∀ i, (b i : ℝ) = t + y i := by
    intro i
    rw [hy]
    ring
  have hsumT : ∑ i ∈ T, ((weight : ℝ) - X i) = (slots : ℝ) * weight - A := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hA]
  have hLoss : (∑ i ∈ T, (weight : ℝ) * (b i : ℝ)) -
      ∑ i, (b i : ℝ) * X i =
      (∑ i ∈ T, ((weight : ℝ) - X i) * y i) -
        (∑ i ∈ Finset.univ \ T, X i * y i) +
        t * ((slots : ℝ) * weight - A - M) := by
    have hsplit2 : ∑ i ∈ Finset.univ \ T, (b i : ℝ) * X i +
        ∑ i ∈ T, (b i : ℝ) * X i = ∑ i, (b i : ℝ) * X i :=
      Finset.sum_sdiff (Finset.subset_univ T)
    have hTpart : ∑ i ∈ T, ((weight : ℝ) * (b i : ℝ) - (b i : ℝ) * X i) =
        t * ((slots : ℝ) * weight - A) +
          ∑ i ∈ T, ((weight : ℝ) - X i) * y i := by
      calc ∑ i ∈ T, ((weight : ℝ) * (b i : ℝ) - (b i : ℝ) * X i) =
          ∑ i ∈ T, (t * ((weight : ℝ) - X i) +
            ((weight : ℝ) - X i) * y i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hbty i]
            ring
        _ = t * ∑ i ∈ T, ((weight : ℝ) - X i) +
            ∑ i ∈ T, ((weight : ℝ) - X i) * y i := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = t * ((slots : ℝ) * weight - A) +
            ∑ i ∈ T, ((weight : ℝ) - X i) * y i := by
            rw [hsumT]
    have hCpart : ∑ i ∈ Finset.univ \ T, (b i : ℝ) * X i =
        t * M + ∑ i ∈ Finset.univ \ T, X i * y i := by
      calc ∑ i ∈ Finset.univ \ T, (b i : ℝ) * X i =
          ∑ i ∈ Finset.univ \ T, (t * X i + X i * y i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hbty i]
            ring
        _ = t * ∑ i ∈ Finset.univ \ T, X i +
            ∑ i ∈ Finset.univ \ T, X i * y i := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = t * M + ∑ i ∈ Finset.univ \ T, X i * y i := by
            rw [hM]
    calc (∑ i ∈ T, (weight : ℝ) * (b i : ℝ)) - ∑ i, (b i : ℝ) * X i =
        (∑ i ∈ T, (weight : ℝ) * (b i : ℝ)) -
          (∑ i ∈ Finset.univ \ T, (b i : ℝ) * X i +
            ∑ i ∈ T, (b i : ℝ) * X i) := by rw [hsplit2]
      _ = (∑ i ∈ T, ((weight : ℝ) * (b i : ℝ) - (b i : ℝ) * X i)) -
          ∑ i ∈ Finset.univ \ T, (b i : ℝ) * X i := by
          rw [Finset.sum_sub_distrib]
          ring
      _ = (t * ((slots : ℝ) * weight - A) +
            ∑ i ∈ T, ((weight : ℝ) - X i) * y i) -
          (t * M + ∑ i ∈ Finset.univ \ T, X i * y i) := by
          rw [hTpart, hCpart]
      _ = (∑ i ∈ T, ((weight : ℝ) - X i) * y i) -
            (∑ i ∈ Finset.univ \ T, X i * y i) +
            t * ((slots : ℝ) * weight - A - M) := by
          ring
  have hzero : (slots : ℝ) * weight - A - M = 0 := by linarith [hAM]
  have hQbound : (∑ i ∈ T, ((weight : ℝ) - X i) * y i) -
      (∑ i ∈ Finset.univ \ T, X i * y i) ≤
      ((weight : ℝ) * A - (∑ i ∈ T, X i ^ 2) -
        (∑ i ∈ Finset.univ \ T, X i ^ 2)) / sensitivity := by
    have h1 : ∑ i ∈ T, ((weight : ℝ) - X i) * y i ≤
        (∑ i ∈ T, ((weight : ℝ) - X i) * X i) / sensitivity := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => hclaimA i
    have h2 : (∑ i ∈ Finset.univ \ T, X i ^ 2) / sensitivity ≤
        ∑ i ∈ Finset.univ \ T, X i * y i := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => hclaimB i
    have h3 : ∑ i ∈ T, ((weight : ℝ) - X i) * X i =
        (weight : ℝ) * A - ∑ i ∈ T, X i ^ 2 := by
      rw [hA, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hE : ((weight : ℝ) * A - (∑ i ∈ T, X i ^ 2) -
        (∑ i ∈ Finset.univ \ T, X i ^ 2)) / sensitivity =
        (∑ i ∈ T, ((weight : ℝ) - X i) * X i) / sensitivity -
          (∑ i ∈ Finset.univ \ T, X i ^ 2) / sensitivity := by
      rw [← h3, sub_div]
    rw [hE]
    linarith [h1, h2]
  have hCS_T : A ^ 2 ≤ (slots : ℝ) * ∑ i ∈ T, X i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := T) (f := X)
    rw [hTcard] at h
    exact_mod_cast h
  have hCS_M : M ^ 2 ≤ ((Fintype.card ι : ℝ) - slots) *
      ∑ i ∈ Finset.univ \ T, X i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ \ T) (f := X)
    have hcard : ((Finset.univ \ T).card : ℝ) =
        (Fintype.card ι : ℝ) - slots := by
      rw [Finset.card_univ_diff, hTcard, Nat.cast_sub hlt.le]
    calc M ^ 2 ≤ ((Finset.univ \ T).card : ℝ) *
        ∑ i ∈ Finset.univ \ T, X i ^ 2 := by exact_mod_cast h
      _ = ((Fintype.card ι : ℝ) - slots) *
          ∑ i ∈ Finset.univ \ T, X i ^ 2 := by rw [hcard]
  have hsq1 : A ^ 2 / (slots : ℝ) ≤ ∑ i ∈ T, X i ^ 2 :=
    (div_le_iff₀ hKpos).mpr (by linarith [hCS_T])
  have hsq2 : M ^ 2 / ((Fintype.card ι : ℝ) - slots) ≤
      ∑ i ∈ Finset.univ \ T, X i ^ 2 :=
    (div_le_iff₀ hnK).mpr (by linarith [hCS_M])
  have hMrw : (weight : ℝ) * A - A ^ 2 / (slots : ℝ) -
      M ^ 2 / ((Fintype.card ι : ℝ) - slots) =
      (weight : ℝ) * M - M ^ 2 * (Fintype.card ι : ℝ) /
        ((slots : ℝ) * ((Fintype.card ι : ℝ) - slots)) := by
    have hAeq : A = (slots : ℝ) * weight - M := by linarith [hAM]
    rw [hAeq]
    field_simp
    try ring
  have hM2 : (weight : ℝ) * M - M ^ 2 * (Fintype.card ι : ℝ) /
      ((slots : ℝ) * ((Fintype.card ι : ℝ) - slots)) ≤
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) * (weight : ℝ) ^ 2 /
        (4 * (Fintype.card ι : ℝ)) := by
    rw [← sub_nonneg]
    have hexpand : (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) *
        (weight : ℝ) ^ 2 / (4 * (Fintype.card ι : ℝ)) -
        ((weight : ℝ) * M - M ^ 2 * (Fintype.card ι : ℝ) /
          ((slots : ℝ) * ((Fintype.card ι : ℝ) - slots))) =
        ((slots : ℝ) * ((Fintype.card ι : ℝ) - slots) * (weight : ℝ) -
            2 * (Fintype.card ι : ℝ) * M) ^ 2 /
          (4 * (Fintype.card ι : ℝ) *
            ((slots : ℝ) * ((Fintype.card ι : ℝ) - slots))) := by
      field_simp
      try ring
    rw [hexpand]
    positivity
  have htarget : (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) *
      (weight : ℝ) ^ 2 / (4 * (Fintype.card ι : ℝ)) / sensitivity =
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) / (Fintype.card ι : ℝ) *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
    field_simp
    try ring
  calc (∑ i ∈ T, (weight : ℝ) * (b i : ℝ)) - ∑ i, (b i : ℝ) * X i =
      (∑ i ∈ T, ((weight : ℝ) - X i) * y i) -
        (∑ i ∈ Finset.univ \ T, X i * y i) := by
        rw [hLoss, hzero, mul_zero, add_zero]
    _ ≤ ((weight : ℝ) * A - (∑ i ∈ T, X i ^ 2) -
        (∑ i ∈ Finset.univ \ T, X i ^ 2)) / sensitivity := hQbound
    _ ≤ ((weight : ℝ) * A - A ^ 2 / (slots : ℝ) -
        M ^ 2 / ((Fintype.card ι : ℝ) - slots)) / sensitivity := by
        gcongr
    _ ≤ (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) * (weight : ℝ) ^ 2 /
        (4 * (Fintype.card ι : ℝ)) / sensitivity := by
        gcongr
        rw [hMrw]
        exact hM2
    _ = (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) / (Fintype.card ι : ℝ) *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := htarget

/-- The extremal in-block level `(n+K)·w₁/(2n𝒮)` above the threshold. -/
noncomputable def flatKInLevel (n slots : ℕ)
    (weight sensitivity : NNReal) : ℝ :=
  (((n : ℝ) + slots) * weight) / (2 * n * sensitivity)

/-- The extremal out-block level `K·w₁/(2n𝒮)` above the threshold. -/
noncomputable def flatKOutLevel (n slots : ℕ)
    (weight sensitivity : NNReal) : ℝ :=
  ((slots : ℝ) * weight) / (2 * (n : ℝ) * sensitivity)

/-- At the extremal two-block profile, `reserve` solves the flat-`K`
water-filling mass identity. -/
theorem flatK_twoBlock_mass
    (slots : ℕ) (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hslots : 0 < slots) (hlt : slots < Fintype.card ι)
    (T : Finset ι) (hTcard : T.card = slots) :
    waterFillMass weight sensitivity
      (fun i => ((blockProfile reserve T
        (flatKOutLevel (Fintype.card ι) slots weight sensitivity)
        (flatKInLevel (Fintype.card ι) slots weight sensitivity)
        (by unfold flatKOutLevel; positivity)
        (by unfold flatKInLevel; positivity) : EligibleProfile ι reserve)
          i : ℝ))
      reserve =
      (slots : ℝ) * weight := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
    exact_mod_cast this
  have hslotsn : (slots : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt.le
  set A : ℝ := (((n : ℝ) + slots) * weight) / (2 * n) with hA
  set B : ℝ := ((slots : ℝ) * weight) / (2 * n) with hB
  have hsne : (sensitivity : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hsens)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hin : (sensitivity : ℝ) * flatKInLevel n slots weight sensitivity = A := by
    unfold flatKInLevel
    rw [hA]
    field_simp
  have hout : (sensitivity : ℝ) * flatKOutLevel n slots weight sensitivity = B := by
    unfold flatKOutLevel
    rw [hB]
    field_simp
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hAw : A ≤ (weight : ℝ) := by
    rw [hA, div_le_iff₀ (by positivity)]
    nlinarith [weight.coe_nonneg]
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hBw : B ≤ (weight : ℝ) := by
    rw [hB, div_le_iff₀ (by positivity)]
    nlinarith [weight.coe_nonneg]
  have hclampIn : clampWeight weight
      ((sensitivity : ℝ) * flatKInLevel n slots weight sensitivity) = A := by
    rw [hin]
    exact clampWeight_eq_of_mem weight hA0 hAw
  have hclampOut : clampWeight weight
      ((sensitivity : ℝ) * flatKOutLevel n slots weight sensitivity) = B := by
    rw [hout]
    exact clampWeight_eq_of_mem weight hB0 hBw
  unfold waterFillMass waterFillAt
  calc (∑ i : ι, clampWeight weight ((sensitivity : ℝ) *
        (((blockProfile reserve T
          (flatKOutLevel n slots weight sensitivity)
          (flatKInLevel n slots weight sensitivity)
          (by unfold flatKOutLevel; positivity)
          (by unfold flatKInLevel; positivity) : EligibleProfile ι reserve)
            i : ℝ) - reserve)))
      = ∑ i : ι, (if i ∈ T then A else B) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [blockProfile_coe, add_sub_cancel_left, mul_ite,
          apply_ite (clampWeight weight), hclampIn, hclampOut]
    _ = (slots : ℝ) * weight := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
          Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
          Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.card_univ_diff, hTcard]
        rw [nsmul_eq_mul, nsmul_eq_mul, hA, hB]
        have hcast : ((n - slots : ℕ) : ℝ) = (n : ℝ) - slots := by
          rw [Nat.cast_sub hlt.le]
        rw [hcast]
        field_simp
        ring

/-- Attainment: at the extremal two-block profile the water-filling loss
equals `K(n-K)/n · w₁²/(4𝒮)`. -/
theorem flatK_twoBlock_loss_eq
    (slots : ℕ) (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hslots : 0 < slots) (hlt : slots < Fintype.card ι)
    (T : Finset ι) (hTcard : T.card = slots) :
    (∑ i ∈ T, (weight : ℝ) *
        ((blockProfile reserve T
          (flatKOutLevel (Fintype.card ι) slots weight sensitivity)
          (flatKInLevel (Fintype.card ι) slots weight sensitivity)
          (by unfold flatKOutLevel; positivity)
          (by unfold flatKInLevel; positivity) : EligibleProfile ι reserve)
            i : ℝ)) -
      ∑ i, ((blockProfile reserve T
          (flatKOutLevel (Fintype.card ι) slots weight sensitivity)
          (flatKInLevel (Fintype.card ι) slots weight sensitivity)
          (by unfold flatKOutLevel; positivity)
          (by unfold flatKInLevel; positivity) : EligibleProfile ι reserve)
            i : ℝ) *
        waterFillAt weight sensitivity
          (fun k => ((blockProfile reserve T
            (flatKOutLevel (Fintype.card ι) slots weight sensitivity)
            (flatKInLevel (Fintype.card ι) slots weight sensitivity)
            (by unfold flatKOutLevel; positivity)
            (by unfold flatKInLevel; positivity) : EligibleProfile ι reserve)
              k : ℝ))
          reserve i =
      (slots : ℝ) * ((Fintype.card ι : ℝ) - slots) / (Fintype.card ι : ℝ) *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  set n : ℕ := Fintype.card ι with hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
    exact_mod_cast this
  have hslotsn : (slots : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt.le
  have hsne : (sensitivity : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hsens)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  set A : ℝ := (((n : ℝ) + slots) * weight) / (2 * n) with hA
  set B : ℝ := ((slots : ℝ) * weight) / (2 * n) with hB
  have hin : (sensitivity : ℝ) * flatKInLevel n slots weight sensitivity = A := by
    unfold flatKInLevel
    rw [hA]
    field_simp
  have hout : (sensitivity : ℝ) * flatKOutLevel n slots weight sensitivity = B := by
    unfold flatKOutLevel
    rw [hB]
    field_simp
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hAw : A ≤ (weight : ℝ) := by
    rw [hA, div_le_iff₀ (by positivity)]
    nlinarith [weight.coe_nonneg]
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hBw : B ≤ (weight : ℝ) := by
    rw [hB, div_le_iff₀ (by positivity)]
    nlinarith [weight.coe_nonneg]
  have hclampIn : clampWeight weight
      ((sensitivity : ℝ) * flatKInLevel n slots weight sensitivity) = A := by
    rw [hin]
    exact clampWeight_eq_of_mem weight hA0 hAw
  have hclampOut : clampWeight weight
      ((sensitivity : ℝ) * flatKOutLevel n slots weight sensitivity) = B := by
    rw [hout]
    exact clampWeight_eq_of_mem weight hB0 hBw
  set P : EligibleProfile ι reserve := blockProfile reserve T
    (flatKOutLevel n slots weight sensitivity)
    (flatKInLevel n slots weight sensitivity)
    (by unfold flatKOutLevel; positivity)
    (by unfold flatKInLevel; positivity) with hPdef
  have hPcoe : ∀ i, (P i : ℝ) = reserve +
      (if i ∈ T then flatKInLevel n slots weight sensitivity
        else flatKOutLevel n slots weight sensitivity) := by
    intro i
    rw [hPdef, blockProfile_coe]
  have hXi : ∀ i, waterFillAt weight sensitivity
      (fun k => (P k : ℝ)) reserve i = if i ∈ T then A else B := by
    intro i
    show clampWeight weight ((sensitivity : ℝ) * ((P i : ℝ) - reserve)) =
      if i ∈ T then A else B
    rw [hPcoe i, add_sub_cancel_left, mul_ite,
      apply_ite (clampWeight weight), hclampIn, hclampOut]
  have h1 : (∑ i ∈ T, (weight : ℝ) * (P i : ℝ)) =
      (slots : ℝ) * weight *
        (reserve + flatKInLevel n slots weight sensitivity) := by
    have hconst : ∀ i ∈ T, (weight : ℝ) * (P i : ℝ) =
        weight * (reserve + flatKInLevel n slots weight sensitivity) := by
      intro i hi
      rw [hPcoe i, if_pos hi]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hTcard, nsmul_eq_mul]
    ring
  have h2 : (∑ i, (P i : ℝ) * waterFillAt weight sensitivity
      (fun k => (P k : ℝ)) reserve i) =
      (slots : ℝ) *
          ((reserve + flatKInLevel n slots weight sensitivity) * A) +
        ((n : ℝ) - slots) *
          ((reserve + flatKOutLevel n slots weight sensitivity) * B) := by
    calc (∑ i, (P i : ℝ) * waterFillAt weight sensitivity
        (fun k => (P k : ℝ)) reserve i) =
        ∑ i : ι, (if i ∈ T then
          (reserve + flatKInLevel n slots weight sensitivity) * A
          else (reserve + flatKOutLevel n slots weight sensitivity) * B) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hXi i, hPcoe i]
          by_cases hi : i ∈ T <;> simp [hi]
      _ = (slots : ℝ) *
            ((reserve + flatKInLevel n slots weight sensitivity) * A) +
          ((n : ℝ) - slots) *
            ((reserve + flatKOutLevel n slots weight sensitivity) * B) := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
            Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not,
            Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.card_univ_diff, hTcard]
          have hcast : ((n - slots : ℕ) : ℝ) = (n : ℝ) - slots := by
            rw [Nat.cast_sub hlt.le]
          rw [nsmul_eq_mul, nsmul_eq_mul, hcast]
  rw [h1, h2, hA, hB]
  unfold flatKInLevel flatKOutLevel
  field_simp
  ring

end SmoothingCliff.Frontier
