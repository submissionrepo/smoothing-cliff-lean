import SmoothingCliff.Basic

/-!
# Ordering and squeeze bounds

This file begins the formalization of Lemma `lem:ordering` and Proposition
`prop:squeeze` in `Smoothing_the_Cliff_ITCS.tex`.  The ordering lemma is stated
without choosing a sorting convention, so it applies directly to arbitrary
finite agent types and can later be reused by the rank-wise ceiling and floor
arguments.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

/-- Lemma `lem:ordering`: a strictly higher bidder receives weakly more
expected priority under anonymity, own-bid monotonicity, and cross-monotonicity.
-/
theorem allocation_ordering
    {ι : Type*} [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hCross : CrossMonotone x)
    (b : EligibleProfile ι reserve) (i j : ι)
    (hBid : (b j : ℝ) < (b i : ℝ)) :
    x b j ≤ x b i := by
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl (b i : ℝ)) hBid
  have hle : b j ≤ b i := hBid.le
  let bt : EligibleProfile ι reserve := updateBid b j (b i)
  let π : Equiv.Perm ι := Equiv.swap i j
  have hself : updateBid b j (b j) = b := by
    funext k
    simp [updateBid]
  have hRelabel : relabelProfile π bt = bt := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [relabelProfile, π, bt, updateBid, hij]
    · by_cases hkj : k = j
      · subst k
        simp [relabelProfile, π, bt, updateBid, hij]
      · have hswap : Equiv.swap i j k = k :=
          Equiv.swap_apply_of_ne_of_ne hki hkj
        simp [relabelProfile, π, bt, updateBid, hswap, hkj]
  have hTie : x bt j = x bt i := by
    have h := hAnon π bt j
    rw [hRelabel] at h
    simpa [π, hij] using h.symm
  have hOwnStep := hOwn b j hle
  change x (updateBid b j (b j)) j ≤
    x (updateBid b j (b i)) j at hOwnStep
  rw [hself] at hOwnStep
  change x b j ≤ x bt j at hOwnStep
  have hCrossStep := hCross b i j hij hle
  change x (updateBid b j (b i)) i ≤
    x (updateBid b j (b j)) i at hCrossStep
  rw [hself] at hCrossStep
  change x bt i ≤ x b i at hCrossStep
  linarith

/-- Anonymity forces equal allocation at an exact bid tie. -/
theorem allocation_eq_of_bid_eq
    {ι : Type*} [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve) (hAnon : Anonymous x)
    (b : EligibleProfile ι reserve) (i j : ι)
    (hBid : (b i : ℝ) = (b j : ℝ)) :
    x b i = x b j := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hbij : b i = b j := Subtype.ext hBid
    let π : Equiv.Perm ι := Equiv.swap i j
    have hRelabel : relabelProfile π b = b := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [relabelProfile, π, hbij]
      · by_cases hkj : k = j
        · subst k
          simp [relabelProfile, π, hbij]
        · have hswap : Equiv.swap i j k = k :=
            Equiv.swap_apply_of_ne_of_ne hki hkj
          simp [relabelProfile, π, hswap]
    have h := hAnon π b i
    rw [hRelabel] at h
    simpa [π, hij] using h.symm

/-- Weak form of `allocation_ordering`, including exact ties. -/
theorem allocation_ordering_weak
    {ι : Type*} [DecidableEq ι] {reserve : ℝ}
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hCross : CrossMonotone x)
    (b : EligibleProfile ι reserve) (i j : ι)
    (hBid : (b j : ℝ) ≤ (b i : ℝ)) :
    x b j ≤ x b i := by
  rcases hBid.lt_or_eq with hlt | heq
  · exact allocation_ordering x hAnon hOwn hCross b i j hlt
  · exact (allocation_eq_of_bid_eq x hAnon b j i heq).le

/-- Assignment-feasibility expressed by the rank-dependent upper bound on
every subset.  In the paper, `capacity k` is `W_k`, the sum of the largest
`min(k,K)` slot weights. -/
def SubsetFeasible {ι : Type*} {reserve : ℝ} [Fintype ι]
    (capacity : ℕ → ℝ) (x : InterimRule ι reserve) : Prop :=
  ∀ b H, ∑ m ∈ H, x b m ≤ capacity H.card

/-- Rank-free ceiling behind Proposition `prop:squeeze`.  A set `H` certifies
that at least `|H|` bidders, including `i`, weakly exceed the comparison bid
`z`. -/
theorem squeeze_ceiling_of_subset
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (capacity : ℕ → ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hSubset : SubsetFeasible capacity x)
    (b : EligibleProfile ι reserve) (i : ι)
    (H : Finset ι) (hi : i ∈ H)
    (z : EligibleBid reserve)
    (hz : (z : ℝ) ≤ (b i : ℝ))
    (hAbove : ∀ m ∈ H, (z : ℝ) ≤ (b m : ℝ)) :
    x b i ≤ capacity H.card / H.card +
      sensitivity * ((b i : ℝ) - (z : ℝ)) := by
  let bt : EligibleProfile ι reserve := updateBid b i z
  have hbt_i : bt i = z := by simp [bt, updateBid]
  have hbt_other (m : ι) (hmi : m ≠ i) : bt m = b m := by
    simp [bt, updateBid, hmi]
  have hEach : ∀ m ∈ H, x bt i ≤ x bt m := by
    intro m hm
    by_cases hmi : m = i
    · subst m
      exact le_rfl
    · apply allocation_ordering_weak x hAnon hOwn hCross bt m i
      rw [hbt_i, hbt_other m hmi]
      exact hAbove m hm
  have hCardPosNat : 0 < H.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hCardPos : (0 : ℝ) < H.card := by
    exact_mod_cast hCardPosNat
  have hSumLower :
      (H.card : ℝ) * x bt i ≤ ∑ m ∈ H, x bt m := by
    calc
      (H.card : ℝ) * x bt i = ∑ m ∈ H, x bt i := by simp
      _ ≤ ∑ m ∈ H, x bt m := by
        exact Finset.sum_le_sum fun m hm => hEach m hm
  have hAtLower : x bt i ≤ capacity H.card / H.card := by
    apply (le_div_iff₀ hCardPos).2
    calc
      x bt i * (H.card : ℝ) = (H.card : ℝ) * x bt i := by ring
      _ ≤ ∑ m ∈ H, x bt m := hSumLower
      _ ≤ capacity H.card := hSubset bt H
  have hself : updateBid b i (b i) = b := by
    funext m
    simp [updateBid]
  have hdist := (hLip b i).dist_le_mul (b i) z
  change dist (x (updateBid b i (b i)) i) (x (updateBid b i z) i) ≤
    (sensitivity : ℝ) * dist (b i) z at hdist
  rw [hself] at hdist
  change dist (x b i) (x bt i) ≤
    (sensitivity : ℝ) * dist (b i) z at hdist
  have hdist' :
      |x b i - x bt i| ≤
        (sensitivity : ℝ) * ((b i : ℝ) - (z : ℝ)) := by
    simpa [Real.dist_eq, Subtype.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hz)] using hdist
  have hside : x b i - x bt i ≤ |x b i - x bt i| := le_abs_self _
  linarith

/-- Rank-free floor behind Proposition `prop:squeeze`.  The witness `top`
certifies a highest bidder. -/
theorem squeeze_floor_of_top
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reserve totalWeight : ℝ} (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hNoWaste : OneSlotNoWaste totalWeight x)
    (b : EligibleProfile ι reserve) (i top : ι)
    (hTop : ∀ m, (b m : ℝ) ≤ (b top : ℝ)) :
    totalWeight / Fintype.card ι -
        sensitivity * ((b top : ℝ) - (b i : ℝ)) ≤ x b i := by
  let bt : EligibleProfile ι reserve := updateBid b i (b top)
  have hbt_i : bt i = b top := by simp [bt, updateBid]
  have hbt_other (m : ι) (hmi : m ≠ i) : bt m = b m := by
    simp [bt, updateBid, hmi]
  have hEach : ∀ m, x bt m ≤ x bt i := by
    intro m
    apply allocation_ordering_weak x hAnon hOwn hCross bt i m
    by_cases hmi : m = i
    · subst m
      exact le_rfl
    · rw [hbt_i, hbt_other m hmi]
      exact hTop m
  have hSumUpper :
      ∑ m, x bt m ≤ (Fintype.card ι : ℝ) * x bt i := by
    calc
      ∑ m, x bt m ≤ ∑ m, x bt i :=
        Finset.sum_le_sum fun m _ => hEach m
      _ = (Fintype.card ι : ℝ) * x bt i := by simp
  have hCardPosNat : 0 < Fintype.card ι := Fintype.card_pos
  have hCardPos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast hCardPosNat
  have hAtTop : totalWeight / Fintype.card ι ≤ x bt i := by
    apply (div_le_iff₀ hCardPos).2
    calc
      totalWeight = ∑ m, x bt m := (hNoWaste bt).symm
      _ ≤ (Fintype.card ι : ℝ) * x bt i := hSumUpper
      _ = x bt i * (Fintype.card ι : ℝ) := by ring
  have hself : updateBid b i (b i) = b := by
    funext m
    simp [updateBid]
  have hdist := (hLip b i).dist_le_mul (b top) (b i)
  change dist (x (updateBid b i (b top)) i)
      (x (updateBid b i (b i)) i) ≤
    (sensitivity : ℝ) * dist (b top) (b i) at hdist
  rw [hself] at hdist
  change dist (x bt i) (x b i) ≤
    (sensitivity : ℝ) * dist (b top) (b i) at hdist
  have hgap : (b i : ℝ) ≤ (b top : ℝ) := hTop i
  have hdist' :
      |x bt i - x b i| ≤
        (sensitivity : ℝ) * ((b top : ℝ) - (b i : ℝ)) := by
    simpa [Real.dist_eq, Subtype.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hgap)] using hdist
  have hside : x bt i - x b i ≤ |x bt i - x b i| := le_abs_self _
  linarith

/-- A profile together with a non-increasing enumeration of its agents.  Lean
uses zero-based ranks, so paper rank `j` is represented by index `j-1`. -/
structure RankedProfile (ι : Type*) [Fintype ι] (n : ℕ) (reserve : ℝ) where
  profile : EligibleProfile ι reserve
  ranking : Fin n ≃ ι
  sorted : Antitone (fun q => (profile (ranking q) : ℝ))

/-- The agents in ranks zero through `k`, inclusive. -/
def RankedProfile.prefixAgents
    {ι : Type*} [Fintype ι] {n : ℕ} {reserve : ℝ}
    (ranked : RankedProfile ι n reserve) (k : Fin n) : Finset ι :=
  Finset.univ.map
    ⟨fun q : Fin (k.val + 1) =>
        ranked.ranking
          (⟨q.val, Nat.lt_of_lt_of_le q.isLt
            (Nat.succ_le_iff.mpr k.isLt)⟩ : Fin n),
      by
        intro a b h
        apply Fin.ext
        have hab := congrArg Fin.val (ranked.ranking.injective h)
        exact hab⟩

/-- Ceiling half of Proposition `prop:squeeze`, in zero-based rank notation. -/
theorem ranked_squeeze_ceiling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {reserve : ℝ}
    (capacity : ℕ → ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hSubset : SubsetFeasible capacity x)
    (ranked : RankedProfile ι n reserve)
    (j k : Fin n) (hjk : j ≤ k) :
    x ranked.profile (ranked.ranking j) ≤
      capacity (k.val + 1) / (k.val + 1) +
        sensitivity *
          ((ranked.profile (ranked.ranking j) : ℝ) -
            (ranked.profile (ranked.ranking k) : ℝ)) := by
  let H := ranked.prefixAgents k
  have hi : ranked.ranking j ∈ H := by
    simp only [H, RankedProfile.prefixAgents, Finset.mem_map,
      Finset.mem_univ, true_and]
    refine ⟨⟨j.val, ?_⟩, ?_⟩
    · omega
    · simp
  have hz :
      (ranked.profile (ranked.ranking k) : ℝ) ≤
        (ranked.profile (ranked.ranking j) : ℝ) :=
    ranked.sorted hjk
  have hAbove :
      ∀ m ∈ H,
        (ranked.profile (ranked.ranking k) : ℝ) ≤
          (ranked.profile m : ℝ) := by
    intro m hm
    simp only [H, RankedProfile.prefixAgents, Finset.mem_map,
      Finset.mem_univ, true_and] at hm
    rcases hm with ⟨q, rfl⟩
    apply ranked.sorted
    exact Fin.mk_le_mk.mpr (Nat.le_of_lt_succ q.isLt)
  have h := squeeze_ceiling_of_subset capacity sensitivity x
    hAnon hOwn hLip hCross hSubset ranked.profile (ranked.ranking j)
    H hi (ranked.profile (ranked.ranking k)) hz hAbove
  simpa [H, RankedProfile.prefixAgents] using h

/-- Floor half of Proposition `prop:squeeze`, in zero-based rank notation. -/
theorem ranked_squeeze_floor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {reserve totalWeight : ℝ}
    (hn : 0 < n) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hNoWaste : OneSlotNoWaste totalWeight x)
    (ranked : RankedProfile ι n reserve)
    (j : Fin n) :
    totalWeight / n -
        sensitivity *
          ((ranked.profile (ranked.ranking ⟨0, hn⟩) : ℝ) -
            (ranked.profile (ranked.ranking j) : ℝ)) ≤
      x ranked.profile (ranked.ranking j) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let topIndex : Fin n := ⟨0, hn⟩
  have hTop :
      ∀ m, (ranked.profile m : ℝ) ≤
        (ranked.profile (ranked.ranking topIndex) : ℝ) := by
    intro m
    obtain ⟨q, rfl⟩ := ranked.ranking.surjective m
    exact ranked.sorted (Fin.zero_le q)
  letI : Nonempty ι := ⟨ranked.ranking topIndex⟩
  have h := squeeze_floor_of_top sensitivity x hAnon hOwn hLip hCross
    hNoWaste ranked.profile (ranked.ranking j) (ranked.ranking topIndex) hTop
  have hcard : Fintype.card ι = n := by
    simpa using (Fintype.card_congr ranked.ranking).symm
  simpa [hcard, topIndex] using h

/-- Proposition `prop:squeeze`: every certified rule obeys all rank-wise
ceilings and floors.  The conjunction is exactly the paper statement after
converting its one-based ranks to Lean's zero-based `Fin n`. -/
theorem ranked_squeeze_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} {reserve totalWeight : ℝ}
    (hn : 0 < n) (capacity : ℕ → ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hAnon : Anonymous x)
    (hOwn : OwnMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (hCross : CrossMonotone x)
    (hSubset : SubsetFeasible capacity x)
    (hNoWaste : OneSlotNoWaste totalWeight x)
    (ranked : RankedProfile ι n reserve) :
    (∀ (j k : Fin n), j ≤ k →
      x ranked.profile (ranked.ranking j) ≤
        capacity (k.val + 1) / (k.val + 1) +
          sensitivity *
            ((ranked.profile (ranked.ranking j) : ℝ) -
              (ranked.profile (ranked.ranking k) : ℝ))) ∧
    (∀ j : Fin n,
      totalWeight / n -
          sensitivity *
            ((ranked.profile (ranked.ranking ⟨0, hn⟩) : ℝ) -
              (ranked.profile (ranked.ranking j) : ℝ)) ≤
        x ranked.profile (ranked.ranking j)) := by
  constructor
  · intro j k hjk
    exact ranked_squeeze_ceiling capacity sensitivity x hAnon hOwn hLip
      hCross hSubset ranked j k hjk
  · intro j
    exact ranked_squeeze_floor hn sensitivity x hAnon hOwn hLip hCross
      hNoWaste ranked j

end SmoothingCliff.Frontier
