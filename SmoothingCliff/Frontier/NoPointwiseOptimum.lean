import SmoothingCliff.Frontier.Impossibility

/-!
# No pointwise welfare-optimal rule in the certified class

This file assembles Theorem `thm:impossibility` of `Smoothing_the_Cliff_ITCS.tex`
around the algebraic certificate of `Impossibility.lean`.  The paper's class
`C` is carried by `Certified`, whose feasibility clause is the subset system
`∑_{i ∈ H} x_i ≤ W_{|H|}` already used by Proposition `prop:squeeze`.

The two adjacent profiles are `loneProfile` (one leader `δ` above the common
level) and `tiedProfile` (two leaders).  The caps that `prop:squeeze` puts on
them, the exact shortfall identities, and the own-bid Lipschitz comparison
between them are proved here from class membership alone.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

noncomputable section

variable {ι : Type*} [DecidableEq ι] {reserve : ℝ}

/-- Membership in the paper's certified class `C`. -/
structure Certified [Fintype ι] (capacity : ℕ → ℝ) (totalWeight : ℝ)
    (sensitivity : NNReal) (x : InterimRule ι reserve) : Prop where
  anon : Anonymous x
  ownMono : OwnMonotone x
  ownLip : OwnLipschitz sensitivity x
  crossMono : CrossMonotone x
  subsetFeasible : SubsetFeasible capacity x
  noWaste : OneSlotNoWaste totalWeight x
  nonneg : ∀ b i, 0 ≤ x b i

/-- The common eligible level `v₀`. -/
def baseProfile (v₀ : ℝ) (h₀ : reserve ≤ v₀) : EligibleProfile ι reserve :=
  fun _ => ⟨v₀, h₀⟩

/-- The profile `R₁`: `lead` bids `v₀ + δ`, everybody else `v₀`. -/
def loneProfile (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) (lead : ι) :
    EligibleProfile ι reserve :=
  updateBid (baseProfile v₀ h₀) lead ⟨v₀ + δ, by
    simp only [Set.mem_Ici]; linarith⟩

/-- The profile `R₂`: `lead` and `second` both bid `v₀ + δ`. -/
def tiedProfile (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    (lead second : ι) : EligibleProfile ι reserve :=
  updateBid (loneProfile v₀ δ h₀ hδ lead) second ⟨v₀ + δ, by
    simp only [Set.mem_Ici]; linarith⟩

@[simp] theorem loneProfile_lead (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    (lead : ι) : ((loneProfile v₀ δ h₀ hδ lead lead : EligibleBid reserve) : ℝ)
      = v₀ + δ := by
  simp [loneProfile, updateBid]

@[simp] theorem loneProfile_other (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    {lead j : ι} (hj : j ≠ lead) :
    ((loneProfile v₀ δ h₀ hδ lead j : EligibleBid reserve) : ℝ) = v₀ := by
  simp [loneProfile, updateBid, hj, baseProfile]

@[simp] theorem tiedProfile_second (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    (lead second : ι) :
    ((tiedProfile v₀ δ h₀ hδ lead second second : EligibleBid reserve) : ℝ)
      = v₀ + δ := by
  simp [tiedProfile, updateBid]

@[simp] theorem tiedProfile_lead (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    {lead second : ι} (h : lead ≠ second) :
    ((tiedProfile v₀ δ h₀ hδ lead second lead : EligibleBid reserve) : ℝ)
      = v₀ + δ := by
  simp [tiedProfile, updateBid, h]

@[simp] theorem tiedProfile_other (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    {lead second j : ι} (h1 : j ≠ lead) (h2 : j ≠ second) :
    ((tiedProfile v₀ δ h₀ hδ lead second j : EligibleBid reserve) : ℝ) = v₀ := by
  simp [tiedProfile, updateBid, h1, h2, loneProfile, baseProfile]

/-- `R₂` is `R₁` with the second leader's own bid raised. -/
theorem tiedProfile_eq_update (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    (lead second : ι) :
    tiedProfile v₀ δ h₀ hδ lead second =
      updateBid (loneProfile v₀ δ h₀ hδ lead) second
        ⟨v₀ + δ, by simp only [Set.mem_Ici]; linarith⟩ := rfl

/-- `R₁` is itself the update of `R₁` at the second leader by the low bid. -/
theorem loneProfile_eq_update (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    {lead second : ι} (h : second ≠ lead) :
    loneProfile v₀ δ h₀ hδ lead =
      updateBid (loneProfile v₀ δ h₀ hδ lead) second ⟨v₀, h₀⟩ := by
  funext j
  by_cases hj : j = second
  · subst j
    apply Subtype.ext
    simp [updateBid, loneProfile, baseProfile, h]
  · simp [updateBid, hj]

/-! ### Welfare at the two profiles -/

variable [Fintype ι]

theorem welfare_loneProfile {totalWeight : ℝ} (x : InterimRule ι reserve)
    (hNo : OneSlotNoWaste totalWeight x) (v₀ δ : ℝ) (h₀ : reserve ≤ v₀)
    (hδ : 0 ≤ δ) (lead : ι) :
    welfare x (loneProfile v₀ δ h₀ hδ lead) =
      v₀ * totalWeight + δ * x (loneProfile v₀ δ h₀ hδ lead) lead := by
  classical
  set b := loneProfile v₀ δ h₀ hδ lead with hb
  have hval : ∀ j : ι, ((b j : EligibleBid reserve) : ℝ)
      = v₀ + (if j = lead then δ else 0) := by
    intro j
    by_cases hj : j = lead
    · subst j; simp [hb]
    · simp [hb, hj]
  unfold welfare
  calc
    ∑ j, ((b j : EligibleBid reserve) : ℝ) * x b j
        = ∑ j, (v₀ * x b j + (if j = lead then δ else 0) * x b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hval j]; ring
    _ = v₀ * (∑ j, x b j) + δ * x b lead := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          simp [ite_mul]
    _ = v₀ * totalWeight + δ * x b lead := by rw [hNo b]

theorem welfare_tiedProfile {totalWeight : ℝ} (x : InterimRule ι reserve)
    (hNo : OneSlotNoWaste totalWeight x) (v₀ δ : ℝ) (h₀ : reserve ≤ v₀)
    (hδ : 0 ≤ δ) {lead second : ι} (hls : lead ≠ second) :
    welfare x (tiedProfile v₀ δ h₀ hδ lead second) =
      v₀ * totalWeight + δ * (x (tiedProfile v₀ δ h₀ hδ lead second) lead
        + x (tiedProfile v₀ δ h₀ hδ lead second) second) := by
  classical
  set b := tiedProfile v₀ δ h₀ hδ lead second with hb
  have hval : ∀ j : ι, ((b j : EligibleBid reserve) : ℝ)
      = v₀ + (if j = lead then δ else 0) + (if j = second then δ else 0) := by
    intro j
    by_cases hj : j = lead
    · subst j; simp [hb, hls]
    · by_cases hj2 : j = second
      · subst j; simp [hb, hj]
      · simp [hb, hj, hj2]
  unfold welfare
  calc
    ∑ j, ((b j : EligibleBid reserve) : ℝ) * x b j
        = ∑ j, (v₀ * x b j + ((if j = lead then δ else 0) * x b j
            + (if j = second then δ else 0) * x b j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hval j]; ring
    _ = v₀ * (∑ j, x b j) + (δ * x b lead + δ * x b second) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          simp [ite_mul]
    _ = v₀ * totalWeight + δ * (x b lead + x b second) := by rw [hNo b]; ring

/-! ### The two caps of `prop:squeeze` -/

/-- The rank-one ceiling at `R₁`, taken over the full set of agents. -/
theorem loneProfile_leader_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (hCapTotal : capacity (Fintype.card ι) = totalWeight)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) (lead : ι) :
    x (loneProfile v₀ δ h₀ hδ lead) lead ≤
      totalWeight / Fintype.card ι + sensitivity * δ := by
  classical
  set b := loneProfile v₀ δ h₀ hδ lead with hb
  have hz : ((⟨v₀, h₀⟩ : EligibleBid reserve) : ℝ) ≤ ((b lead : EligibleBid reserve) : ℝ) := by
    simp [hb]; linarith
  have hAbove : ∀ m ∈ (Finset.univ : Finset ι),
      ((⟨v₀, h₀⟩ : EligibleBid reserve) : ℝ) ≤ ((b m : EligibleBid reserve) : ℝ) := by
    intro m _
    by_cases hm : m = lead
    · subst m; simpa [hb] using (by linarith : v₀ ≤ v₀ + δ)
    · simp [hb, loneProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hm]
  have h := squeeze_ceiling_of_subset capacity sensitivity x hx.anon hx.ownMono
    hx.ownLip hx.crossMono hx.subsetFeasible b lead Finset.univ (Finset.mem_univ _)
    ⟨v₀, h₀⟩ hz hAbove
  simpa [hb, hCapTotal] using h

/-- The same ceiling at `R₂`, applied to the second leader. -/
theorem tiedProfile_leader_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (hCapTotal : capacity (Fintype.card ι) = totalWeight)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) (lead second : ι) :
    x (tiedProfile v₀ δ h₀ hδ lead second) second ≤
      totalWeight / Fintype.card ι + sensitivity * δ := by
  classical
  set b := tiedProfile v₀ δ h₀ hδ lead second with hb
  have hz : ((⟨v₀, h₀⟩ : EligibleBid reserve) : ℝ)
      ≤ ((b second : EligibleBid reserve) : ℝ) := by
    simp [hb]; linarith
  have hAbove : ∀ m ∈ (Finset.univ : Finset ι),
      ((⟨v₀, h₀⟩ : EligibleBid reserve) : ℝ) ≤ ((b m : EligibleBid reserve) : ℝ) := by
    intro m _
    by_cases hm : m = second
    · subst m; simpa [hb] using (by linarith : v₀ ≤ v₀ + δ)
    · by_cases hm2 : m = lead
      · subst m
        simp [hb, tiedProfile_lead (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hm]
        linarith
      · simp [hb, tiedProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hm2 hm]
  have h := squeeze_ceiling_of_subset capacity sensitivity x hx.anon hx.ownMono
    hx.ownLip hx.crossMono hx.subsetFeasible b second Finset.univ (Finset.mem_univ _)
    ⟨v₀, h₀⟩ hz hAbove
  simpa [hb, hCapTotal] using h

/-! ### Mass identities and the own-bid comparison between the profiles -/

/-- At `R₁` the `n-1` trailers are tied, so the mass identity reads with a
single trailer allocation. -/
theorem loneProfile_mass {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) {lead trailer : ι}
    (h : trailer ≠ lead) :
    x (loneProfile v₀ δ h₀ hδ lead) lead
        + ((Fintype.card ι : ℝ) - 1) * x (loneProfile v₀ δ h₀ hδ lead) trailer
      = totalWeight := by
  classical
  set b := loneProfile v₀ δ h₀ hδ lead with hb
  have hEq : ∀ j ∈ Finset.univ.erase lead, x b j = x b trailer := by
    intro j hj
    have hjne : j ≠ lead := (Finset.mem_erase.mp hj).1
    refine allocation_eq_of_bid_eq x hx.anon b j trailer ?_
    rw [loneProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hjne,
      loneProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) h]
  have hcard : (Finset.univ.erase lead).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨lead⟩
  have hsum : ∑ j ∈ Finset.univ.erase lead, x b j
      = ((Fintype.card ι : ℝ) - 1) * x b trailer := by
    rw [Finset.sum_congr rfl hEq, Finset.sum_const, hcard, nsmul_eq_mul,
      Nat.cast_sub hpos, Nat.cast_one]
  have htot : x b lead + ∑ j ∈ Finset.univ.erase lead, x b j = totalWeight := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ lead)]
    exact hx.noWaste b
  rw [← hsum]; exact htot

/-- At `R₂` the two leaders are tied. -/
theorem tiedProfile_leaders_eq {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) {lead second : ι}
    (hls : lead ≠ second) :
    x (tiedProfile v₀ δ h₀ hδ lead second) lead
      = x (tiedProfile v₀ δ h₀ hδ lead second) second := by
  refine allocation_eq_of_bid_eq x hx.anon _ lead second ?_
  rw [tiedProfile_lead (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ) hls,
    tiedProfile_second]

/-- Own-bid Lipschitz between the two profiles: only the second leader's own
bid moves, and it moves by `δ`. -/
theorem tied_sub_lone_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) {lead second : ι}
    (hsl : second ≠ lead) :
    x (tiedProfile v₀ δ h₀ hδ lead second) second
        - x (loneProfile v₀ δ h₀ hδ lead) second ≤ sensitivity * δ := by
  classical
  set high : EligibleBid reserve := ⟨v₀ + δ, by simp only [Set.mem_Ici]; linarith⟩
  set low : EligibleBid reserve := ⟨v₀, h₀⟩
  have hdist := (hx.ownLip (loneProfile v₀ δ h₀ hδ lead) second).dist_le_mul high low
  have hlow : updateBid (loneProfile v₀ δ h₀ hδ lead) second low
      = loneProfile v₀ δ h₀ hδ lead :=
    (loneProfile_eq_update v₀ δ h₀ hδ hsl).symm
  have hhigh : updateBid (loneProfile v₀ δ h₀ hδ lead) second high
      = tiedProfile v₀ δ h₀ hδ lead second := rfl
  rw [hlow, hhigh] at hdist
  have hd : dist high low = δ := by
    simp [Subtype.dist_eq, Real.dist_eq, high, low, abs_of_nonneg hδ]
  rw [hd] at hdist
  have := abs_le.mp (by simpa [Real.dist_eq] using hdist)
  linarith [this.2]

/-! ### The caps and the shortfall inequality -/

/-- The welfare cap that `prop:squeeze` puts on `R₁`. -/
def loneCap (totalWeight : ℝ) (sensitivity : NNReal) (v₀ δ : ℝ) (n : ℕ) : ℝ :=
  v₀ * totalWeight + δ * (totalWeight / n + sensitivity * δ)

/-- The welfare cap that `prop:squeeze` puts on `R₂`. -/
def tiedCap (totalWeight : ℝ) (sensitivity : NNReal) (v₀ δ : ℝ) (n : ℕ) : ℝ :=
  v₀ * totalWeight + 2 * δ * (totalWeight / n + sensitivity * δ)

theorem welfare_loneProfile_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (hCapTotal : capacity (Fintype.card ι) = totalWeight)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) (lead : ι) :
    welfare x (loneProfile v₀ δ h₀ hδ lead)
      ≤ loneCap totalWeight sensitivity v₀ δ (Fintype.card ι) := by
  rw [welfare_loneProfile x hx.noWaste v₀ δ h₀ hδ lead, loneCap]
  have h := loneProfile_leader_le hx hCapTotal v₀ δ h₀ hδ lead
  nlinarith [h, hδ]

theorem welfare_tiedProfile_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (hCapTotal : capacity (Fintype.card ι) = totalWeight)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ) {lead second : ι}
    (hls : lead ≠ second) :
    welfare x (tiedProfile v₀ δ h₀ hδ lead second)
      ≤ tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι) := by
  rw [welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ hls, tiedCap,
    tiedProfile_leaders_eq hx v₀ δ h₀ hδ hls]
  have h := tiedProfile_leader_le hx hCapTotal v₀ δ h₀ hδ lead second
  nlinarith [h, hδ]

/-- **The shortfall inequality of `thm:impossibility`, discharged from class
membership.**  For every rule in `C`, the welfare shortfalls `a` and `b` from
the two caps satisfy `2a + (n-1) b ≥ 2 S δ²`. -/
theorem certified_shortfall {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {x : InterimRule ι reserve}
    (hx : Certified capacity totalWeight sensitivity x)
    (hn : 2 ≤ Fintype.card ι)
    (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 < δ) {lead second : ι}
    (hls : lead ≠ second) :
    2 * (loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)
          - welfare x (loneProfile v₀ δ h₀ hδ.le lead))
      + ((Fintype.card ι : ℝ) - 1)
          * (tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)
              - welfare x (tiedProfile v₀ δ h₀ hδ.le lead second))
      ≥ 2 * sensitivity * δ ^ 2 := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn'
  set u : ℝ := totalWeight / n with hu
  set L : ℝ := x (loneProfile v₀ δ h₀ hδ.le lead) lead with hL
  set T : ℝ := x (loneProfile v₀ δ h₀ hδ.le lead) second with hT
  set M : ℝ := x (tiedProfile v₀ δ h₀ hδ.le lead second) second with hM
  set a : ℝ := loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)
    - welfare x (loneProfile v₀ δ h₀ hδ.le lead) with ha
  set b : ℝ := tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)
    - welfare x (tiedProfile v₀ δ h₀ hδ.le lead second) with hb
  have h2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hnlt : (1 : ℝ) < n := by rw [hn']; linarith
  have hn0 : n ≠ 0 := by positivity
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have haval : a = δ * (u + sensitivity * δ - L) := by
    rw [ha, loneCap, welfare_loneProfile x hx.noWaste v₀ δ h₀ hδ.le lead, ← hL, ← hu]
    ring
  have hbval : b = 2 * δ * (u + sensitivity * δ - M) := by
    rw [hb, tiedCap, welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hx v₀ δ h₀ hδ.le hls, ← hM, ← hu]
    ring
  have hR1 : u + sensitivity * δ - a / δ ≤ L := by
    rw [haval]
    field_simp
    linarith
  have hR1Mass : L + (n - 1) * T = n * u := by
    have := loneProfile_mass hx v₀ δ h₀ hδ.le (lead := lead) (trailer := second)
      (Ne.symm hls)
    rw [hu]
    field_simp
    rw [← hL, ← hT] at this
    linarith [this]
  have hR2 : 2 * (u + sensitivity * δ) - b / δ ≤ 2 * M := by
    rw [hbval]
    field_simp
    linarith
  have hLip : M - T ≤ sensitivity * δ :=
    tied_sub_lone_le hx v₀ δ h₀ hδ.le (Ne.symm hls)
  exact adjacent_profile_shortfall hnlt hδ hR1 hR1Mass hR2 hLip

/-! ### Rule A: the band-linear rule attaining the `R₁` cap

The paper's first coefficient sequence `α_k^A = S (n-k)/(n-1)` produces the
rank rule that is linear in the clipped scores, so it has the closed form
below and needs no sorting. -/

/-- Clip a score into the band `[v₀, v₀ + δ]`. -/
def clipBand (v₀ δ t : ℝ) : ℝ := min (max t v₀) (v₀ + δ)

theorem clipBand_ge (v₀ δ t : ℝ) (hδ : 0 ≤ δ) : v₀ ≤ clipBand v₀ δ t :=
  le_min (le_max_right _ _) (by linarith)

theorem clipBand_le (v₀ δ t : ℝ) : clipBand v₀ δ t ≤ v₀ + δ := min_le_right _ _

theorem clipBand_mono (v₀ δ : ℝ) : Monotone (clipBand v₀ δ) := fun _ _ hst =>
  min_le_min (max_le_max hst le_rfl) le_rfl

theorem clipBand_lipschitz (v₀ δ : ℝ) : LipschitzWith 1 (clipBand v₀ δ) :=
  (LipschitzWith.id.max_const v₀).min_const (v₀ + δ)

theorem clipBand_dist_le (v₀ δ s t : ℝ) :
    |clipBand v₀ δ s - clipBand v₀ δ t| ≤ |s - t| := by
  have h := (clipBand_lipschitz v₀ δ).dist_le_mul s t
  simpa [Real.dist_eq] using h

theorem clipBand_eq_of_mem (v₀ δ t : ℝ) (h₁ : v₀ ≤ t) (h₂ : t ≤ v₀ + δ) :
    clipBand v₀ δ t = t := by
  rw [clipBand, max_eq_left h₁, min_eq_left h₂]

/-- **Rule A.**  In closed form, the paper's coefficients `α_k^A` give the rule
that is affine in the clipped scores with common slope `S n / (n-1)`. -/
def bandLinearRule (totalWeight : ℝ) (sensitivity : NNReal) (v₀ δ : ℝ) :
    InterimRule ι reserve := fun b i =>
  totalWeight / Fintype.card ι
    + ((sensitivity : ℝ) * Fintype.card ι / ((Fintype.card ι : ℝ) - 1))
      * (clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
          - (∑ j, clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ))
              / Fintype.card ι)

theorem sum_clipBand_update (v₀ δ : ℝ) (b : EligibleProfile ι reserve) (i : ι)
    (z : EligibleBid reserve) :
    ∑ k, clipBand v₀ δ (((updateBid b i z) k : EligibleBid reserve) : ℝ)
      = clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
        + ∑ k ∈ Finset.univ.erase i,
            clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp [updateBid]
  · exact Finset.sum_congr rfl fun k hk => by
      simp [updateBid, (Finset.mem_erase.mp hk).1]

/-- The own-coordinate normal form of rule A: an affine function of the own
clipped score with slope exactly `S`. -/
theorem bandLinearRule_update_self {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) (b : EligibleProfile ι reserve) (i : ι)
    (z : EligibleBid reserve) :
    bandLinearRule totalWeight sensitivity v₀ δ (updateBid b i z) i
      = totalWeight / Fintype.card ι
        + (sensitivity : ℝ) * clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
        - ((sensitivity : ℝ) / ((Fintype.card ι : ℝ) - 1))
            * ∑ k ∈ Finset.univ.erase i,
                clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) := by
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hn0 : ((Fintype.card ι : ℝ)) ≠ 0 := by positivity
  have hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hn2; norm_num at hn2
  unfold bandLinearRule
  rw [sum_clipBand_update, updateBid, Function.update_self]
  field_simp
  ring

/-- The cross-coordinate normal form of rule A. -/
theorem bandLinearRule_update_other {totalWeight : ℝ} {sensitivity : NNReal}
    (v₀ δ : ℝ) (b : EligibleProfile ι reserve) {i j : ι} (hij : i ≠ j)
    (z : EligibleBid reserve) :
    bandLinearRule totalWeight sensitivity v₀ δ (updateBid b j z) i
      = totalWeight / Fintype.card ι
        + ((sensitivity : ℝ) * Fintype.card ι / ((Fintype.card ι : ℝ) - 1))
          * (clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
              - (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
                  + ∑ k ∈ Finset.univ.erase j,
                      clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ))
                / Fintype.card ι) := by
  unfold bandLinearRule
  rw [sum_clipBand_update]
  congr 3
  simp [updateBid, hij]

omit [DecidableEq ι] in
theorem bandLinearRule_anonymous {totalWeight : ℝ} {sensitivity : NNReal}
    (v₀ δ : ℝ) : Anonymous (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  intro π b i
  unfold bandLinearRule relabelProfile
  have hsum : ∑ j, clipBand v₀ δ ((b (π.symm j) : EligibleBid reserve) : ℝ)
      = ∑ j, clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ) :=
    Equiv.sum_comp π.symm (fun j => clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ))
  rw [hsum]
  simp

theorem bandLinearRule_ownMonotone {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) :
    OwnMonotone (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  intro b i z w hzw
  dsimp only
  rw [bandLinearRule_update_self hn v₀ δ b i z,
    bandLinearRule_update_self hn v₀ δ b i w]
  have : clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
      ≤ clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) :=
    clipBand_mono v₀ δ hzw
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  nlinarith

theorem bandLinearRule_ownLipschitz {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) :
    OwnLipschitz sensitivity (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  intro b i
  apply LipschitzWith.of_dist_le_mul
  intro z w
  dsimp only
  rw [bandLinearRule_update_self hn v₀ δ b i z,
    bandLinearRule_update_self hn v₀ δ b i w]
  have hclip := clipBand_dist_le v₀ δ ((z : EligibleBid reserve) : ℝ)
    ((w : EligibleBid reserve) : ℝ)
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hd : dist z w = |((z : EligibleBid reserve) : ℝ)
      - ((w : EligibleBid reserve) : ℝ)| := by
    simp [Subtype.dist_eq, Real.dist_eq]
  rw [Real.dist_eq, hd]
  have : (totalWeight / Fintype.card ι
        + (sensitivity : ℝ) * clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
        - ((sensitivity : ℝ) / ((Fintype.card ι : ℝ) - 1))
            * ∑ k ∈ Finset.univ.erase i,
                clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ))
      - (totalWeight / Fintype.card ι
        + (sensitivity : ℝ) * clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
        - ((sensitivity : ℝ) / ((Fintype.card ι : ℝ) - 1))
            * ∑ k ∈ Finset.univ.erase i,
                clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ))
      = (sensitivity : ℝ) * (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
          - clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)) := by ring
  rw [this, abs_mul, abs_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left hclip hS

theorem bandLinearRule_crossMonotone {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) :
    CrossMonotone (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  intro b i j hij z w hzw
  dsimp only
  rw [bandLinearRule_update_other v₀ δ b hij w,
    bandLinearRule_update_other v₀ δ b hij z]
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hclip : clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
      ≤ clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) :=
    clipBand_mono v₀ δ hzw
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hc : (0 : ℝ) ≤ (sensitivity : ℝ) * Fintype.card ι
      / ((Fintype.card ι : ℝ) - 1) := by
    apply div_nonneg (by positivity)
    linarith
  have hstep : (clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
        - (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ) + ∑ k ∈ Finset.univ.erase j,
            clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) / Fintype.card ι)
      ≤ (clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
        - (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ) + ∑ k ∈ Finset.univ.erase j,
            clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) / Fintype.card ι) := by
    have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
    have hdiv : (clipBand v₀ δ ((z : EligibleBid reserve) : ℝ)
          + ∑ k ∈ Finset.univ.erase j,
              clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) / Fintype.card ι
        ≤ (clipBand v₀ δ ((w : EligibleBid reserve) : ℝ)
          + ∑ k ∈ Finset.univ.erase j,
              clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ)) / Fintype.card ι := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hpos.le)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hstep hc]

omit [DecidableEq ι] in
theorem bandLinearRule_noWaste {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) :
    OneSlotNoWaste totalWeight (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  intro b
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hn0 : ((Fintype.card ι : ℝ)) ≠ 0 := by positivity
  have hconst : ∑ _j : ι, ((∑ k, clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ))
        / Fintype.card ι)
      = ∑ k, clipBand v₀ δ ((b k : EligibleBid reserve) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  unfold bandLinearRule
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hconst,
    sub_self, mul_zero, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The standing hypotheses of `thm:impossibility`: at least two agents, a
positive band `δ` strictly below `δ̄`, and the capacity system `W_k`. -/
structure BandSetup (capacity : ℕ → ℝ) (totalWeight : ℝ) (sensitivity : NNReal)
    (n : ℕ) (δ : ℝ) : Prop where
  two_le : 2 ≤ n
  sens_pos : 0 < sensitivity
  delta_pos : 0 < δ
  cap_zero : 0 ≤ capacity 0
  cap_total : capacity n = totalWeight
  cap_pred_le : capacity (n - 1) ≤ totalWeight
  /-- `δ < δ̄ = S⁻¹ min_{1 ≤ k ≤ n-1} (W_k / k - W / n)`. -/
  band : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
    (sensitivity : ℝ) * δ < capacity k / k - totalWeight / n

theorem BandSetup.band_mul {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {n : ℕ} {δ : ℝ}
    (hs : BandSetup capacity totalWeight sensitivity n δ)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    (k : ℝ) * (totalWeight / n) + sensitivity * k * δ ≤ capacity k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have h := hs.band k hk1 hk2
  have := (mul_lt_mul_of_pos_left h hkpos)
  rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hkpos)] at this
  nlinarith

theorem bandLinearRule_subsetFeasible {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ : ℝ} (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ) :
    SubsetFeasible capacity (bandLinearRule (ι := ι) (reserve := reserve)
      totalWeight sensitivity v₀ δ) := by
  classical
  intro b H
  have hδ : 0 ≤ δ := hs.delta_pos.le
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two_le
  have hn0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  set n : ℝ := (Fintype.card ι : ℝ) with hnd
  set k : ℝ := (H.card : ℝ) with hkd
  set Zh : ℝ := ∑ m ∈ H, clipBand v₀ δ ((b m : EligibleBid reserve) : ℝ) with hZh
  set Z : ℝ := ∑ m, clipBand v₀ δ ((b m : EligibleBid reserve) : ℝ) with hZ
  have hsum : ∑ m ∈ H, bandLinearRule totalWeight sensitivity v₀ δ b m
      = k * (totalWeight / n) + ((sensitivity : ℝ) * n / (n - 1)) * (Zh - k * (Z / n)) := by
    unfold bandLinearRule
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul]
  have hZhle : Zh ≤ k * (v₀ + δ) := by
    rw [hZh, hkd]
    calc ∑ m ∈ H, clipBand v₀ δ ((b m : EligibleBid reserve) : ℝ)
        ≤ ∑ _m ∈ H, (v₀ + δ) := Finset.sum_le_sum fun m _ => clipBand_le v₀ δ _
      _ = (H.card : ℝ) * (v₀ + δ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcompl : Z - Zh = ∑ m ∈ Finset.univ \ H,
      clipBand v₀ δ ((b m : EligibleBid reserve) : ℝ) := by
    rw [hZ, hZh, ← Finset.sum_sdiff (Finset.subset_univ H)]
    ring
  have hcard : ((Finset.univ \ H).card : ℝ) = n - k := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hnd, hkd,
      Nat.cast_sub (Finset.card_le_univ H)]
  have hcomple : (n - k) * v₀ ≤ Z - Zh := by
    rw [hcompl, ← hcard]
    calc ((Finset.univ \ H).card : ℝ) * v₀
        = ∑ _m ∈ Finset.univ \ H, v₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ Finset.univ \ H, clipBand v₀ δ ((b m : EligibleBid reserve) : ℝ) :=
          Finset.sum_le_sum fun m _ => clipBand_ge v₀ δ _ hδ
  have hkle : k ≤ n := by
    rw [hkd, hnd]; exact_mod_cast Finset.card_le_univ H
  have hk0 : 0 ≤ k := by positivity
  have hkey : Zh - k * (Z / n) ≤ k * (n - k) * δ / n := by
    have hexp : Zh - k * (Z / n) = (1 - k / n) * Zh - (k / n) * (Z - Zh) := by
      field_simp
      ring
    have h1 : (1 - k / n) * Zh ≤ (1 - k / n) * (k * (v₀ + δ)) := by
      apply mul_le_mul_of_nonneg_left hZhle
      rw [sub_nonneg, div_le_one hn0]; exact hkle
    have h2 : (k / n) * ((n - k) * v₀) ≤ (k / n) * (Z - Zh) :=
      mul_le_mul_of_nonneg_left hcomple (by positivity)
    have : (1 - k / n) * (k * (v₀ + δ)) - (k / n) * ((n - k) * v₀)
        = k * (n - k) * δ / n := by field_simp; ring
    linarith [hexp ▸ (by linarith : (1 - k / n) * Zh - (k / n) * (Z - Zh)
      ≤ (1 - k / n) * (k * (v₀ + δ)) - (k / n) * ((n - k) * v₀))]
  have hcpos : (0 : ℝ) ≤ (sensitivity : ℝ) * n / (n - 1) := by positivity
  have hbound : ∑ m ∈ H, bandLinearRule totalWeight sensitivity v₀ δ b m
      ≤ k * (totalWeight / n) + (sensitivity : ℝ) * k * δ * ((n - k) / (n - 1)) := by
    rw [hsum]
    have := mul_le_mul_of_nonneg_left hkey hcpos
    have hid : ((sensitivity : ℝ) * n / (n - 1)) * (k * (n - k) * δ / n)
        = (sensitivity : ℝ) * k * δ * ((n - k) / (n - 1)) := by
      field_simp
    linarith [hid ▸ this]
  rcases Nat.eq_zero_or_pos H.card with hzero | hpos
  · have : H = ∅ := Finset.card_eq_zero.mp hzero
    subst this
    simpa using hs.cap_zero
  · rcases eq_or_lt_of_le (Finset.card_le_univ H) with hfull | hlt
    · have hkn : k = n := by rw [hkd, hnd]; exact_mod_cast hfull
      have hcap : capacity H.card = totalWeight := by
        rw [hfull]; exact hs.cap_total
      rw [hcap]
      have hmass : k * (totalWeight / n) = totalWeight := by
        rw [hkn]; field_simp
      have hzero : (sensitivity : ℝ) * k * δ * ((n - k) / (n - 1)) = 0 := by
        rw [hkn]; simp
      linarith [hbound, hmass, hzero]
    · have hkn1 : H.card ≤ Fintype.card ι - 1 := by
        omega
      have hband := hs.band_mul hpos hkn1
      have hratio : (n - k) / (n - 1) ≤ 1 := by
        rw [div_le_one hn1]
        have : (1 : ℝ) ≤ k := by
          rw [hkd]; exact_mod_cast hpos
        linarith
      have hnonneg : 0 ≤ (sensitivity : ℝ) * k * δ := by positivity
      calc ∑ m ∈ H, bandLinearRule totalWeight sensitivity v₀ δ b m
          ≤ k * (totalWeight / n) + (sensitivity : ℝ) * k * δ * ((n - k) / (n - 1)) := hbound
        _ ≤ k * (totalWeight / n) + (sensitivity : ℝ) * k * δ := by nlinarith
        _ ≤ capacity H.card := hband

/-- Below `δ̄` the whole band is worth at most one agent's equal share. -/
theorem BandSetup.sens_mul_delta_le {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {n : ℕ} {δ : ℝ}
    (hs : BandSetup capacity totalWeight sensitivity n δ) :
    (sensitivity : ℝ) * δ ≤ totalWeight / n := by
  have hnat := hs.two_le
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs.two_le
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : 1 ≤ n - 1 := by omega
  have h2 : n - 1 ≤ n - 1 := le_rfl
  have hband := hs.band_mul h1 h2
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [hcast] at hband
  have hpred := hs.cap_pred_le
  have hchain : ((n : ℝ) - 1) * (totalWeight / n)
      + (sensitivity : ℝ) * ((n : ℝ) - 1) * δ ≤ totalWeight := by
    calc ((n : ℝ) - 1) * (totalWeight / n)
          + (sensitivity : ℝ) * ((n : ℝ) - 1) * δ ≤ capacity (n - 1) := hband
      _ ≤ totalWeight := hpred
  have hsplit : ((n : ℝ) - 1) * (totalWeight / n) = totalWeight - totalWeight / n := by
    field_simp
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  have hδ : (0 : ℝ) ≤ δ := hs.delta_pos.le
  have hstep : (sensitivity : ℝ) * ((n : ℝ) - 1) * δ ≤ totalWeight / n := by
    rw [hsplit] at hchain
    linarith
  have hmono : (sensitivity : ℝ) * δ ≤ (sensitivity : ℝ) * ((n : ℝ) - 1) * δ := by
    nlinarith [mul_nonneg (mul_nonneg hS hδ) (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2)]
  linarith

theorem bandLinearRule_nonneg {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ : ℝ} (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (b : EligibleProfile ι reserve) (i : ι) :
    0 ≤ bandLinearRule (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ b i := by
  classical
  have hδ : 0 ≤ δ := hs.delta_pos.le
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two_le
  have hn0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  have hS : (0 : ℝ) ≤ (sensitivity : ℝ) := sensitivity.coe_nonneg
  set n : ℝ := (Fintype.card ι : ℝ) with hnd
  set Z : ℝ := ∑ j, clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ) with hZ
  have hcardErase : ((Finset.univ.erase i).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hnd,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩)]
    norm_num
  have hZle : Z ≤ clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ) + (n - 1) * (v₀ + δ) := by
    rw [hZ, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ)
        ≤ (n - 1) * (v₀ + δ) := by
      calc ∑ j ∈ Finset.univ.erase i, clipBand v₀ δ ((b j : EligibleBid reserve) : ℝ)
          ≤ ∑ _j ∈ Finset.univ.erase i, (v₀ + δ) :=
            Finset.sum_le_sum fun j _ => clipBand_le v₀ δ _
        _ = (n - 1) * (v₀ + δ) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardErase]
    linarith
  have hlow : v₀ ≤ clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ) :=
    clipBand_ge v₀ δ _ hδ
  have hdev : -((n - 1) * δ / n)
      ≤ clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ) - Z / n := by
    have hZbound : Z ≤ n * clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
        + (n - 1) * δ := by nlinarith [hZle, hlow]
    have hdiv : Z / n
        ≤ clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ) + (n - 1) * δ / n := by
      rw [div_le_iff₀ hn0]
      have hexp : (clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ)
            + (n - 1) * δ / n) * n
          = n * clipBand v₀ δ ((b i : EligibleBid reserve) : ℝ) + (n - 1) * δ := by
        field_simp
      rw [hexp]
      exact hZbound
    linarith
  have hcpos : (0 : ℝ) ≤ (sensitivity : ℝ) * n / (n - 1) := by positivity
  have hkey : (sensitivity : ℝ) * n / (n - 1) * (-((n - 1) * δ / n))
      = -((sensitivity : ℝ) * δ) := by
    field_simp
  have hmain := mul_le_mul_of_nonneg_left hdev hcpos
  rw [hkey] at hmain
  have hbound := hs.sens_mul_delta_le
  unfold bandLinearRule
  rw [← hZ, ← hnd]
  linarith

theorem bandLinearRule_certified {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ : ℝ} (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ) :
    Certified capacity totalWeight sensitivity
      (bandLinearRule (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ) where
  anon := bandLinearRule_anonymous v₀ δ
  ownMono := bandLinearRule_ownMonotone hs.two_le v₀ δ
  ownLip := bandLinearRule_ownLipschitz hs.two_le v₀ δ
  crossMono := bandLinearRule_crossMonotone hs.two_le v₀ δ
  subsetFeasible := bandLinearRule_subsetFeasible v₀ hs
  noWaste := bandLinearRule_noWaste hs.two_le v₀ δ
  nonneg := fun b i => bandLinearRule_nonneg v₀ hs b i

/-- **Rule A attains the `R₁` cap.** -/
theorem bandLinearRule_lone_value {totalWeight : ℝ} {sensitivity : NNReal}
    (hn : 2 ≤ Fintype.card ι) (v₀ δ : ℝ) (h₀ : reserve ≤ v₀) (hδ : 0 ≤ δ)
    (lead : ι) :
    bandLinearRule (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ
        (loneProfile v₀ δ h₀ hδ lead) lead
      = totalWeight / Fintype.card ι + sensitivity * δ := by
  classical
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hn1 : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hn2
    norm_num at hn2
  have hcardErase : ((Finset.univ.erase lead).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨lead⟩)]
    norm_num
  have hsum : ∑ j, clipBand v₀ δ
        ((loneProfile v₀ δ h₀ hδ lead j : EligibleBid reserve) : ℝ)
      = (Fintype.card ι : ℝ) * v₀ + δ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ lead)]
    have hlead : clipBand v₀ δ
        ((loneProfile v₀ δ h₀ hδ lead lead : EligibleBid reserve) : ℝ) = v₀ + δ := by
      rw [loneProfile_lead]
      exact clipBand_eq_of_mem v₀ δ _ (by linarith) le_rfl
    have hpt : ∀ j ∈ Finset.univ.erase lead, clipBand v₀ δ
        ((loneProfile v₀ δ h₀ hδ lead j : EligibleBid reserve) : ℝ) = v₀ := by
      intro j hj
      rw [loneProfile_other (v₀ := v₀) (δ := δ) (h₀ := h₀) (hδ := hδ)
        (Finset.mem_erase.mp hj).1]
      exact clipBand_eq_of_mem v₀ δ _ le_rfl (by linarith)
    have hrest : ∑ j ∈ Finset.univ.erase lead, clipBand v₀ δ
        ((loneProfile v₀ δ h₀ hδ lead j : EligibleBid reserve) : ℝ)
        = ((Fintype.card ι : ℝ) - 1) * v₀ := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, hcardErase]
    rw [hlead, hrest]; ring
  have hown : clipBand v₀ δ (v₀ + δ) = v₀ + δ :=
    clipBand_eq_of_mem v₀ δ _ (by linarith) le_rfl
  unfold bandLinearRule
  rw [hsum, loneProfile_lead, hown]
  field_simp
  ring

theorem bandLinearRule_attains_loneCap {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ : ℝ} (v₀ : ℝ)
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (h₀ : reserve ≤ v₀) (lead : ι) :
    welfare (bandLinearRule (ι := ι) (reserve := reserve) totalWeight sensitivity v₀ δ)
        (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
      = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι) := by
  rw [welfare_loneProfile _ (bandLinearRule_noWaste hs.two_le v₀ δ) v₀ δ h₀
      hs.delta_pos.le lead,
    bandLinearRule_lone_value hs.two_le v₀ δ h₀ hs.delta_pos.le lead, loneCap]

/-- **The `R₂` ceiling for `R₁`-cap attainers.**  A certified rule that attains
the `R₁` cap gives each tied leader at `R₂` strictly less than
`W/n + (n-1)/n · S δ`; this is the "strictly above" clause of
`thm:impossibility`. -/
theorem tied_leader_lt_of_attains_loneCap {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ v₀ : ℝ} {x : InterimRule ι reserve}
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (hn4 : 4 ≤ Fintype.card ι) (h₀ : reserve ≤ v₀) {lead second : ι}
    (hls : lead ≠ second)
    (hx : Certified capacity totalWeight sensitivity x)
    (hattain : welfare x (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
      = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)) :
    x (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second) second
      < totalWeight / Fintype.card ι
        + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ := by
  classical
  have hδ : 0 < δ := hs.delta_pos
  have hn4' : (3 : ℝ) < (Fintype.card ι : ℝ) := by
    have : (4 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn4
    linarith
  set n : ℝ := (Fintype.card ι : ℝ) with hnd
  set u : ℝ := totalWeight / n with hu
  have hshort := certified_shortfall hx hs.two_le v₀ δ h₀ hδ hls
  rw [hattain, sub_self] at hshort
  set b : ℝ := tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)
    - welfare x (tiedProfile v₀ δ h₀ hδ.le lead second) with hbdef
  have hb : 2 * (sensitivity : ℝ) * δ ^ 2 ≤ (n - 1) * b := by linarith
  set M : ℝ := x (tiedProfile v₀ δ h₀ hδ.le lead second) second with hM
  have hbval : b = 2 * δ * (u + sensitivity * δ - M) := by
    rw [hbdef, tiedCap, welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hx v₀ δ h₀ hδ.le hls, ← hM, ← hu]
    ring
  have hdef : 2 * M = 2 * (u + sensitivity * δ) - b / δ := by
    rw [hbval]
    field_simp
    ring
  exact tied_leader_strict_gap hn4' hs.sens_pos hδ hb hdef

/-! ### The pointwise conclusion -/
/-- **Theorem `thm:impossibility`, everything except the second rule.**  The
two caps, the attainment of the `R₁` cap inside `C`, the shortfall inequality,
and the strict `R₂` ceiling for any rule attaining the `R₁` cap. -/
theorem impossibility_clauses {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ v₀ : ℝ}
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (hn4 : 4 ≤ Fintype.card ι) (h₀ : reserve ≤ v₀) {lead second : ι}
    (hls : lead ≠ second) :
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
    (∀ x : InterimRule ι reserve, Certified capacity totalWeight sensitivity x →
        welfare x (loneProfile v₀ δ h₀ hs.delta_pos.le lead)
            = loneCap totalWeight sensitivity v₀ δ (Fintype.card ι) →
          x (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second) second
            < totalWeight / Fintype.card ι
              + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ) := by
  refine ⟨fun x hx => welfare_loneProfile_le hx hs.cap_total v₀ δ h₀ hs.delta_pos.le lead,
    fun x hx => welfare_tiedProfile_le hx hs.cap_total v₀ δ h₀ hs.delta_pos.le hls,
    ⟨bandLinearRule totalWeight sensitivity v₀ δ,
      bandLinearRule_certified v₀ hs,
      bandLinearRule_attains_loneCap v₀ hs h₀ lead⟩,
    fun x hx => certified_shortfall hx hs.two_le v₀ δ h₀ hs.delta_pos hls,
    fun x hx hattain => tied_leader_lt_of_attains_loneCap hs hn4 h₀ hls hx hattain⟩


/-- A rule is pointwise welfare-optimal in `C` when it weakly beats every other
certified rule at every profile. -/
def PointwiseOptimal (capacity : ℕ → ℝ) (totalWeight : ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve) : Prop :=
  Certified capacity totalWeight sensitivity x ∧
    ∀ y : InterimRule ι reserve, Certified capacity totalWeight sensitivity y →
      ∀ b : EligibleProfile ι reserve, welfare y b ≤ welfare x b

/-- **Theorem `thm:impossibility`, final step.**  Given the paper's second rule
`y` -- a certified rule giving each tied leader at `R₂` the weight
`W/n + (n-1)/n · S δ` -- no rule in `C` is pointwise welfare-optimal. -/
theorem no_pointwise_optimum_of_second_rule {capacity : ℕ → ℝ} {totalWeight : ℝ}
    {sensitivity : NNReal} {δ v₀ : ℝ}
    (hs : BandSetup capacity totalWeight sensitivity (Fintype.card ι) δ)
    (hn4 : 4 ≤ Fintype.card ι) (h₀ : reserve ≤ v₀) {lead second : ι}
    (hls : lead ≠ second)
    (y : InterimRule ι reserve)
    (hy : Certified capacity totalWeight sensitivity y)
    (hyval : y (tiedProfile v₀ δ h₀ hs.delta_pos.le lead second) second
      = totalWeight / Fintype.card ι
        + ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * sensitivity * δ)
    (x : InterimRule ι reserve)
    (hopt : PointwiseOptimal capacity totalWeight sensitivity x) :
    False := by
  classical
  obtain ⟨hx, hbest⟩ := hopt
  have hδ : 0 < δ := hs.delta_pos
  have hn2 : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two_le
  have hn4' : (3 : ℝ) < (Fintype.card ι : ℝ) := by
    have : (4 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn4
    linarith
  have hn0 : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  set n : ℝ := (Fintype.card ι : ℝ) with hnd
  set u : ℝ := totalWeight / n with hu
  -- rule A attains the `R₁` cap, so the optimal rule has zero shortfall there
  have hAcert := bandLinearRule_certified (ι := ι) (reserve := reserve) v₀ hs
  have hAval := bandLinearRule_attains_loneCap (ι := ι) (reserve := reserve) v₀ hs h₀ lead
  have hxlone : loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)
      ≤ welfare x (loneProfile v₀ δ h₀ hδ.le lead) := by
    have := hbest _ hAcert (loneProfile v₀ δ h₀ hδ.le lead)
    rw [hAval] at this
    exact this
  have hazero : loneCap totalWeight sensitivity v₀ δ (Fintype.card ι)
      - welfare x (loneProfile v₀ δ h₀ hδ.le lead) = 0 := by
    have hcap := welfare_loneProfile_le hx hs.cap_total v₀ δ h₀ hδ.le lead
    linarith
  -- the shortfall inequality then forces a strictly positive shortfall at `R₂`
  have hshort := certified_shortfall hx hs.two_le v₀ δ h₀ hδ hls
  set b : ℝ := tiedCap totalWeight sensitivity v₀ δ (Fintype.card ι)
    - welfare x (tiedProfile v₀ δ h₀ hδ.le lead second) with hbdef
  have hb : 2 * (sensitivity : ℝ) * δ ^ 2 ≤ (n - 1) * b := by
    rw [hazero] at hshort
    linarith
  set M : ℝ := x (tiedProfile v₀ δ h₀ hδ.le lead second) second with hM
  have hbval : b = 2 * δ * (u + sensitivity * δ - M) := by
    rw [hbdef, tiedCap, welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hx v₀ δ h₀ hδ.le hls, ← hM, ← hu]
    ring
  have hdef : 2 * M = 2 * (u + sensitivity * δ) - b / δ := by
    rw [hbval]
    field_simp
    ring
  have hgap : M < u + (n - 1) / n * sensitivity * δ :=
    tied_leader_strict_gap hn4' hs.sens_pos hδ hb hdef
  -- but the second rule does strictly better at `R₂`
  have hywelf : welfare y (tiedProfile v₀ δ h₀ hδ.le lead second)
      = v₀ * totalWeight + 2 * δ * (u + (n - 1) / n * sensitivity * δ) := by
    rw [welfare_tiedProfile y hy.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hy v₀ δ h₀ hδ.le hls, hyval]
    ring
  have hxwelf : welfare x (tiedProfile v₀ δ h₀ hδ.le lead second)
      = v₀ * totalWeight + 2 * δ * M := by
    rw [welfare_tiedProfile x hx.noWaste v₀ δ h₀ hδ.le hls,
      tiedProfile_leaders_eq hx v₀ δ h₀ hδ.le hls, ← hM]
    ring
  have hcontra := hbest y hy (tiedProfile v₀ δ h₀ hδ.le lead second)
  rw [hywelf, hxwelf] at hcontra
  nlinarith [hgap, hδ]

end

end SmoothingCliff.Frontier
