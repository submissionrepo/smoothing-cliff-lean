import SmoothingCliff.Frontier.RationedRamp
import Mathlib.Analysis.Convex.Combination

/-!
# Allocations are lotteries over feasible assignments

Theorem `thm:meanfield` runs with `K` slots of common weight `w₁`, so a
feasible assignment hands weight `w₁` to each member of a set of at most `K`
agents.  The implementability clause of part (iii) is then the uniform-matroid
decomposition: an allocation vector in `[0, w₁]` whose total is at most
`w₁ K` is a lottery over such assignments.  The paper cites systematic
sampling or Budish et al. (2013); the proof here is the direct induction on
the number of fractional coordinates, which is self-contained.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The allocation vector of the assignment that serves exactly `S`. -/
def slotVector (w : ℝ) (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then w else 0

/-- The feasible assignments: at most `K` agents served, each at weight `w`. -/
def SlotVectors (w : ℝ) (K : ℕ) : Set (ι → ℝ) :=
  {y | ∃ S : Finset ι, S.card ≤ K ∧ y = slotVector w S}

/-- The coordinates that are neither empty nor full. -/
noncomputable def fractionalSet (w : ℝ) (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => 0 < x i ∧ x i < w

omit [DecidableEq ι] in
theorem mem_fractionalSet {w : ℝ} {x : ι → ℝ} {i : ι} :
    i ∈ fractionalSet w x ↔ (0 < x i ∧ x i < w) := by
  simp [fractionalSet]

/-- With no fractional coordinate the vector is already an assignment. -/
theorem mem_slotVectors_of_fractionalSet_empty {w : ℝ} (hw : 0 < w) (K : ℕ)
    {x : ι → ℝ} (h0 : ∀ i, 0 ≤ x i) (hub : ∀ i, x i ≤ w)
    (hcap : ∑ i, x i ≤ w * K) (hempty : fractionalSet w x = ∅) :
    x ∈ SlotVectors w K := by
  classical
  have hzero_or_full : ∀ i, x i = 0 ∨ x i = w := by
    intro i
    by_contra hcon
    push Not at hcon
    have : i ∈ fractionalSet w x := by
      rw [mem_fractionalSet]
      exact ⟨lt_of_le_of_ne (h0 i) (Ne.symm hcon.1), lt_of_le_of_ne (hub i) hcon.2⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty i)
  set S : Finset ι := Finset.univ.filter fun i => x i = w with hS
  have hxS : x = slotVector w S := by
    funext i
    rw [slotVector]
    by_cases hi : x i = w
    · simp [hS, hi]
    · rcases hzero_or_full i with h | h
      · simp [hS, h]
      · exact absurd h hi
  have hsum : ∑ i, x i = w * S.card := by
    rw [hxS]
    unfold slotVector
    calc (∑ i, if i ∈ S then w else 0) = ∑ _i ∈ Finset.univ ∩ S, w :=
          Finset.sum_ite_mem Finset.univ S (fun _ => w)
      _ = ∑ _i ∈ S, w := by rw [Finset.univ_inter]
      _ = w * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨S, ?_, hxS⟩
  have : w * (S.card : ℝ) ≤ w * K := by rw [← hsum]; exact hcap
  have hle : (S.card : ℝ) ≤ (K : ℝ) := le_of_mul_le_mul_left this hw
  exact_mod_cast hle

/-- **The decomposition.**  Every allocation bounded by the slot weight whose
total respects the capacity is a lottery over feasible assignments. -/
theorem mem_convexHull_slotVectors {w : ℝ} (hw : 0 < w) (K : ℕ) :
    ∀ (m : ℕ) (x : ι → ℝ), (fractionalSet w x).card ≤ m → (∀ i, 0 ≤ x i) →
      (∀ i, x i ≤ w) → (∑ i, x i ≤ w * K) →
      x ∈ convexHull ℝ (SlotVectors w K) := by
  classical
  intro m
  induction m with
  | zero =>
    intro x hcard h0 hub hcap
    have hempty : fractionalSet w x = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact subset_convexHull ℝ _
      (mem_slotVectors_of_fractionalSet_empty hw K h0 hub hcap hempty)
  | succ m ih =>
    intro x hcard h0 hub hcap
    by_cases hempty : fractionalSet w x = ∅
    · exact subset_convexHull ℝ _
        (mem_slotVectors_of_fractionalSet_empty hw K h0 hub hcap hempty)
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    rw [mem_fractionalSet] at hi
    by_cases hother : ∃ j, j ≠ i ∧ 0 < x j ∧ x j < w
    · -- trade between two fractional coordinates: the total does not move
      obtain ⟨j, hji, hj⟩ := hother
      set tup : ℝ := min (w - x i) (x j) with htup
      set tdn : ℝ := min (x i) (w - x j) with htdn
      have htup_pos : 0 < tup := lt_min (by linarith [hi.2]) hj.1
      have htdn_pos : 0 < tdn := lt_min hi.1 (by linarith [hj.2])
      have htup_le1 : tup ≤ w - x i := by rw [htup]; exact min_le_left _ _
      have htup_le2 : tup ≤ x j := by rw [htup]; exact min_le_right _ _
      have htdn_le1 : tdn ≤ x i := by rw [htdn]; exact min_le_left _ _
      have htdn_le2 : tdn ≤ w - x j := by rw [htdn]; exact min_le_right _ _
      set y : ι → ℝ := Function.update (Function.update x i (x i + tup)) j (x j - tup)
        with hy
      set z : ι → ℝ := Function.update (Function.update x i (x i - tdn)) j (x j + tdn)
        with hz
      have hyi : y i = x i + tup := by
        rw [hy, Function.update_of_ne (Ne.symm hji), Function.update_self]
      have hyj : y j = x j - tup := by rw [hy, Function.update_self]
      have hyk : ∀ k, k ≠ i → k ≠ j → y k = x k := by
        intro k h1 h2
        rw [hy, Function.update_of_ne h2, Function.update_of_ne h1]
      have hzi : z i = x i - tdn := by
        rw [hz, Function.update_of_ne (Ne.symm hji), Function.update_self]
      have hzj : z j = x j + tdn := by rw [hz, Function.update_self]
      have hzk : ∀ k, k ≠ i → k ≠ j → z k = x k := by
        intro k h1 h2
        rw [hz, Function.update_of_ne h2, Function.update_of_ne h1]
      -- both endpoints are feasible
      have hy0 : ∀ k, 0 ≤ y k := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hyi]; linarith [h0 i]
        · by_cases h2 : k = j
          · rw [h2, hyj]; linarith
          · rw [hyk k h1 h2]; exact h0 k
      have hyub : ∀ k, y k ≤ w := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hyi]; linarith
        · by_cases h2 : k = j
          · rw [h2, hyj]; linarith [hub j]
          · rw [hyk k h1 h2]; exact hub k
      have hz0 : ∀ k, 0 ≤ z k := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hzi]; linarith
        · by_cases h2 : k = j
          · rw [h2, hzj]; linarith [h0 j]
          · rw [hzk k h1 h2]; exact h0 k
      have hzub : ∀ k, z k ≤ w := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hzi]; linarith [hub i]
        · by_cases h2 : k = j
          · rw [h2, hzj]; linarith
          · rw [hzk k h1 h2]; exact hub k
      have hsum_eq : ∀ v : ι → ℝ, (∀ k, k ≠ i → k ≠ j → v k = x k) →
          ∑ k, v k = (v i + v j) + ∑ k ∈ (Finset.univ.erase i).erase j, x k := by
        intro v hv
        rw [← Finset.add_sum_erase Finset.univ v (Finset.mem_univ i),
          ← Finset.add_sum_erase (Finset.univ.erase i) v
            (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
          Finset.sum_congr rfl (fun k hk => hv k
            (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk)).1
            (Finset.mem_erase.mp hk).1)]
        ring
      have hsumx := hsum_eq x (fun _ _ _ => rfl)
      have hsumy := hsum_eq y hyk
      have hsumz := hsum_eq z hzk
      have hycap : ∑ k, y k ≤ w * K := by
        rw [hsumy, hyi, hyj]
        rw [hsumx] at hcap
        linarith
      have hzcap : ∑ k, z k ≤ w * K := by
        rw [hsumz, hzi, hzj]
        rw [hsumx] at hcap
        linarith
      -- the fractional set strictly shrinks on both sides
      have hsub : ∀ v : ι → ℝ, (∀ k, k ≠ i → k ≠ j → v k = x k) →
          fractionalSet w v ⊆ fractionalSet w x := by
        intro v hv k hk
        rw [mem_fractionalSet] at hk ⊢
        by_cases h1 : k = i
        · rw [h1]; exact hi
        · by_cases h2 : k = j
          · rw [h2]; exact hj
          · rw [hv k h1 h2] at hk; exact hk
      have hdrop : ∀ v : ι → ℝ, (∀ k, k ≠ i → k ≠ j → v k = x k) →
          (v i = w ∨ v i = 0 ∨ v j = w ∨ v j = 0) →
          (fractionalSet w v).card < (fractionalSet w x).card := by
        intro v hv hone
        apply Finset.card_lt_card
        refine ⟨hsub v hv, ?_⟩
        intro hcon
        rcases hone with h | h | h | h
        · have := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          rw [mem_fractionalSet, h] at this
          exact absurd this.2 (lt_irrefl w)
        · have := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          rw [mem_fractionalSet, h] at this
          exact absurd this.1 (lt_irrefl 0)
        · have := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
          rw [mem_fractionalSet, h] at this
          exact absurd this.2 (lt_irrefl w)
        · have := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
          rw [mem_fractionalSet, h] at this
          exact absurd this.1 (lt_irrefl 0)
      have hycard : (fractionalSet w y).card < (fractionalSet w x).card := by
        refine hdrop y hyk ?_
        rcases min_cases (w - x i) (x j) with ⟨heq, _⟩ | ⟨heq, _⟩
        · left; rw [hyi, htup, heq]; ring
        · right; right; right; rw [hyj, htup, heq]; ring
      have hzcard : (fractionalSet w z).card < (fractionalSet w x).card := by
        refine hdrop z hzk ?_
        rcases min_cases (x i) (w - x j) with ⟨heq, _⟩ | ⟨heq, _⟩
        · right; left; rw [hzi, htdn, heq]; ring
        · right; right; left; rw [hzj, htdn, heq]; ring
      have hymem := ih y (by omega) hy0 hyub hycap
      have hzmem := ih z (by omega) hz0 hzub hzcap
      -- and `x` is the convex combination
      set θ : ℝ := tdn / (tup + tdn) with hθ
      have hsumpos : 0 < tup + tdn := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg htdn_pos.le hsumpos.le
      have hθ1 : θ ≤ 1 := by
        rw [hθ, div_le_one hsumpos]
        linarith
      have hcombo : x = θ • y + (1 - θ) • z := by
        funext k
        by_cases h1 : k = i
        · subst h1
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyi, hzi, hθ]
          field_simp
          ring
        · by_cases h2 : k = j
          · subst h2
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyj, hzj, hθ]
            field_simp
            ring
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyk k h1 h2, hzk k h1 h2]
            ring
      rw [hcombo]
      exact (convex_convexHull ℝ _) hymem hzmem hθ0 (by linarith) (by ring)
    · -- `i` is the only fractional coordinate: raise it or drop it
      have hzero_or_full : ∀ k, k ≠ i → x k = 0 ∨ x k = w := by
        intro k hk
        by_contra hcon
        push Not at hcon
        exact hother ⟨k, hk, lt_of_le_of_ne (h0 k) (Ne.symm hcon.1),
          lt_of_le_of_ne (hub k) hcon.2⟩
      set c : ℕ := ((Finset.univ.erase i).filter fun k => x k = w).card with hc
      have hrest : ∑ k ∈ Finset.univ.erase i, x k = w * c := by
        rw [hc]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i)
          (fun k => x k = w) x]
        have h1 : ∑ k ∈ (Finset.univ.erase i).filter fun k => x k = w, x k
            = w * (((Finset.univ.erase i).filter fun k => x k = w).card : ℝ) := by
          rw [Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.mp hk).2)]
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        have h2 : ∑ k ∈ (Finset.univ.erase i).filter (fun k => ¬ x k = w), x k = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hk1 := Finset.mem_filter.mp hk
          have hkne : k ≠ i := (Finset.mem_erase.mp hk1.1).1
          rcases hzero_or_full k hkne with h | h
          · exact h
          · exact absurd h hk1.2
        rw [h1, h2, add_zero]
      have hsplit : ∑ k, x k = x i + w * c := by
        rw [← Finset.add_sum_erase _ x (Finset.mem_univ i), hrest]
      have hcK : (c : ℝ) < K := by
        rw [hsplit] at hcap
        have : w * (c : ℝ) < w * K := by linarith [hi.1]
        exact lt_of_mul_lt_mul_left this hw.le
      have hcK' : c + 1 ≤ K := by
        have : c < K := by exact_mod_cast hcK
        omega
      set y : ι → ℝ := Function.update x i w with hy
      set z : ι → ℝ := Function.update x i 0 with hz
      have hyi : y i = w := by rw [hy, Function.update_self]
      have hzi : z i = 0 := by rw [hz, Function.update_self]
      have hyk : ∀ k, k ≠ i → y k = x k := fun k hk => by
        rw [hy, Function.update_of_ne hk]
      have hzk : ∀ k, k ≠ i → z k = x k := fun k hk => by
        rw [hz, Function.update_of_ne hk]
      have hy0 : ∀ k, 0 ≤ y k := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hyi]; exact hw.le
        · rw [hyk k h1]; exact h0 k
      have hyub : ∀ k, y k ≤ w := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hyi]
        · rw [hyk k h1]; exact hub k
      have hz0 : ∀ k, 0 ≤ z k := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hzi]
        · rw [hzk k h1]; exact h0 k
      have hzub : ∀ k, z k ≤ w := by
        intro k
        by_cases h1 : k = i
        · rw [h1, hzi]; exact hw.le
        · rw [hzk k h1]; exact hub k
      have hycap : ∑ k, y k ≤ w * K := by
        rw [← Finset.add_sum_erase _ y (Finset.mem_univ i), hyi,
          Finset.sum_congr rfl (fun k hk => hyk k (Finset.mem_erase.mp hk).1), hrest]
        have : w * ((c : ℝ) + 1) ≤ w * K := by
          apply mul_le_mul_of_nonneg_left _ hw.le
          exact_mod_cast hcK'
        linarith
      have hzcap : ∑ k, z k ≤ w * K := by
        rw [← Finset.add_sum_erase _ z (Finset.mem_univ i), hzi,
          Finset.sum_congr rfl (fun k hk => hzk k (Finset.mem_erase.mp hk).1), hrest]
        rw [hsplit] at hcap
        linarith [hi.1]
      have hsub : ∀ v : ι → ℝ, (∀ k, k ≠ i → v k = x k) →
          (v i = w ∨ v i = 0) →
          (fractionalSet w v).card < (fractionalSet w x).card := by
        intro v hv hone
        apply Finset.card_lt_card
        constructor
        · intro k hk
          rw [mem_fractionalSet] at hk ⊢
          by_cases h1 : k = i
          · rw [h1]; exact hi
          · rw [hv k h1] at hk; exact hk
        · intro hcon
          have := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          rw [mem_fractionalSet] at this
          rcases hone with h | h
          · rw [h] at this; exact absurd this.2 (lt_irrefl w)
          · rw [h] at this; exact absurd this.1 (lt_irrefl 0)
      have hycard := hsub y hyk (Or.inl hyi)
      have hzcard := hsub z hzk (Or.inr hzi)
      have hymem := ih y (by omega) hy0 hyub hycap
      have hzmem := ih z (by omega) hz0 hzub hzcap
      set θ : ℝ := x i / w with hθ
      have hθ0 : 0 ≤ θ := div_nonneg hi.1.le hw.le
      have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hw]; exact hi.2.le
      have hcombo : x = θ • y + (1 - θ) • z := by
        funext k
        by_cases h1 : k = i
        · subst h1
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyi, hzi, hθ]
          field_simp
          ring
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyk k h1, hzk k h1]
          ring
      rw [hcombo]
      exact (convex_convexHull ℝ _) hymem hzmem hθ0 (by linarith) (by ring)

/-- The decomposition in the form the paper uses. -/
theorem allocation_mem_convexHull_slotVectors {w : ℝ} (hw : 0 < w) (K : ℕ)
    {x : ι → ℝ} (h0 : ∀ i, 0 ≤ x i) (hub : ∀ i, x i ≤ w)
    (hcap : ∑ i, x i ≤ w * K) : x ∈ convexHull ℝ (SlotVectors w K) :=
  mem_convexHull_slotVectors hw K (fractionalSet w x).card x le_rfl h0 hub hcap

/-! ### The rationed ramp is such a lottery -/

section RationedRamp

variable {reserve : ℝ}

/-- **The implementability clause of `thm:meanfield` (iii).**  At every
eligible profile the rationed-ramp allocation is a lottery over assignments of
`K` slots of weight `w₁`, each selected agent receiving one slot. -/
theorem rationedRampRule_mem_convexHull_slotVectors {weight sensitivity : NNReal}
    (hw : 0 < (weight : ℝ)) (K : ℕ) (threshold : ℝ)
    (b : EligibleProfile ι reserve) :
    (fun i => rationedRampRule (ι := ι) (reserve := reserve) weight sensitivity
        ((weight : ℝ) * K) threshold b i)
      ∈ convexHull ℝ (SlotVectors (weight : ℝ) K) := by
  have hcap0 : (0 : ℝ) ≤ (weight : ℝ) * K := by positivity
  exact allocation_mem_convexHull_slotVectors hw K
    (fun i => rationedRampRule_nonneg weight sensitivity threshold hcap0 b i)
    (fun i => rationedRampRule_le_weight weight sensitivity threshold hcap0 b i)
    (rationedRampRule_total_le weight sensitivity threshold hcap0 b)

end RationedRamp

end SmoothingCliff.Frontier
