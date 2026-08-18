/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Order.Compact

/-!
# Ordered cutoff partitions

A finite ordered partition of a nondegenerate compact interval `[a, b]` by `K + 1` cutpoints
`a = c₀ ≤ c₁ ≤ … ≤ cₖ = b`, producing `K` cells indexed by `Fin K`. Cells are left-closed /
right-open (`Ico`) except the final cell, which is closed (`Icc`) so the union covers `[a, b]`.
Endpoint overlaps are a null set for any continuous density, so the choice between `Ico` and `Icc`
at shared cutpoints is immaterial for measure-theoretic purposes.

The endpoints are type-level parameters and the structure carries `a < b` as a field, so a
degenerate (`a = b`, hence `K = 0`) partition is unrepresentable.

## Main definitions

* `OrderedCutoffPartition` — a partition of `[a, b]` by ordered cutpoints.
* `OrderedCutoffPartition.cellClosed`, `cellHalfOpen` — the closed / half-open cells.
* `OrderedCutoffPartition.EtaSpaced` — cells are at least `η` wide.
* `partitionOfCutoffs` — build a partition from an `η`-spaced cutoff vector.

## Main statements

* `OrderedCutoffPartition.exists_unique_cellHalfOpen_of_mem_Icc` — each point lies in a unique cell.
* `etaSpaced_domain_isCompact` — the set of `η`-spaced cutoff vectors is compact.

## Tags

partition, cutoff, ordered, interval
-/

@[expose] public section

open MeasureTheory Set

/-- A finite ordered partition of `[a, b]` by `K + 1` cutpoints. -/
structure OrderedCutoffPartition (K : ℕ) (a b : ℝ) where
  /-- Ordered cutpoints defining the partition cells. -/
  cutoff : Fin (K + 1) → ℝ
  /-- The interval is nondegenerate. -/
  lt : a < b
  /-- The left endpoint is `a`. -/
  left_eq : cutoff 0 = a
  /-- The right endpoint is `b`. -/
  right_eq : cutoff ⟨K, Nat.lt_succ_self K⟩ = b
  /-- Cutpoints are weakly increasing. -/
  monotone : Monotone cutoff

namespace OrderedCutoffPartition

variable {K : ℕ} {a b : ℝ} (P : OrderedCutoffPartition K a b)

/-- Left endpoint of cell `j`. -/
noncomputable def leftEndpoint (j : Fin K) : ℝ := P.cutoff j.castSucc

/-- Right endpoint of cell `j`. -/
noncomputable def rightEndpoint (j : Fin K) : ℝ := P.cutoff j.succ

/-- Closed cell `j`: `[leftEndpoint j, rightEndpoint j]`. Used for conditional means (overlap at
endpoints is null). -/
noncomputable def cellClosed (j : Fin K) : Set ℝ :=
  Icc (P.leftEndpoint j) (P.rightEndpoint j)

/-- Half-open cell `j`: `Ico` except the final cell which is `Icc`, ensuring the cells partition
`[a, b]` exactly. -/
noncomputable def cellHalfOpen (j : Fin K) : Set ℝ :=
  if j.val + 1 = K
  then Icc (P.leftEndpoint j) (P.rightEndpoint j)
  else Ico (P.leftEndpoint j) (P.rightEndpoint j)

/-- `P` is `η`-spaced if every cell has width at least `η`. -/
def EtaSpaced (η : ℝ) : Prop :=
  ∀ j : Fin K, η ≤ P.rightEndpoint j - P.leftEndpoint j

/-! ## Basic monotonicity and endpoint bounds -/

/-- Consecutive cutpoints are weakly increasing. -/
lemma cutoff_le_succ (j : Fin K) : P.cutoff j.castSucc ≤ P.cutoff j.succ :=
  P.monotone (le_of_lt Fin.castSucc_lt_succ)

/-- Each cell's left endpoint is at most its right endpoint. -/
lemma leftEndpoint_le_rightEndpoint (j : Fin K) :
    P.leftEndpoint j ≤ P.rightEndpoint j :=
  P.cutoff_le_succ j

/-- Every left endpoint is at least the interval's left endpoint `a`. -/
lemma le_leftEndpoint (j : Fin K) : a ≤ P.leftEndpoint j := by
  have := P.monotone (Fin.zero_le j.castSucc)
  rwa [P.left_eq] at this

/-- Every right endpoint is at most the interval's right endpoint `b`. -/
lemma rightEndpoint_le (j : Fin K) : P.rightEndpoint j ≤ b := by
  have hsucc : j.succ ≤ ⟨K, Nat.lt_succ_self K⟩ := by
    simp [Fin.le_iff_val_le_val, j.isLt]
  have := P.monotone hsucc
  rwa [P.right_eq] at this

/-! ## Cell measurability and containment -/

/-- Each half-open cell is measurable. -/
lemma cellHalfOpen_measurable (j : Fin K) : MeasurableSet (P.cellHalfOpen j) := by
  unfold cellHalfOpen
  split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ico

/-- Each closed cell is contained in `[a, b]`. -/
lemma cellClosed_subset_Icc (j : Fin K) : P.cellClosed j ⊆ Icc a b :=
  Icc_subset_Icc (P.le_leftEndpoint j) (P.rightEndpoint_le j)

/-- Each half-open cell is contained in `[a, b]`. -/
lemma cellHalfOpen_subset_Icc (j : Fin K) : P.cellHalfOpen j ⊆ Icc a b := by
  unfold cellHalfOpen
  split_ifs
  · exact Icc_subset_Icc (P.le_leftEndpoint j) (P.rightEndpoint_le j)
  · exact Ico_subset_Icc_self.trans
      (Icc_subset_Icc (P.le_leftEndpoint j) (P.rightEndpoint_le j))

/-! ## Cell width positivity -/

/-- In an `η`-spaced partition with `η > 0`, every cell has positive width. -/
lemma cell_width_pos_of_eta {η : ℝ} (hη : P.EtaSpaced η) (hηpos : 0 < η) (j : Fin K) :
    P.leftEndpoint j < P.rightEndpoint j := by
  linarith [hη j]

/-! ## Unique half-open-cell assignment -/

/-- In an η-spaced partition, every `x ∈ [a, b]` belongs to exactly one half-open cell. -/
lemma exists_unique_cellHalfOpen_of_mem_Icc {η : ℝ} (hη : P.EtaSpaced η) (hηpos : 0 < η)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ∃! j : Fin K, x ∈ P.cellHalfOpen j := by
  -- K = 0 is impossible: from left_eq and right_eq with K=0, we'd have a = b.
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    -- With K = 0 the single cutpoint is both a (left_eq) and b (right_eq).
    exact absurd (P.left_eq.symm.trans P.right_eq) P.lt.ne
  -- K ≥ 1 case. Pick the largest i : Fin (K+1) with cutoff i ≤ x.
  let S : Finset (Fin (K + 1)) := Finset.univ.filter (fun i => P.cutoff i ≤ x)
  have hS_ne : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S, P.left_eq, hx.1]
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image S (fun i => i.val) hS_ne
  have hm_le : P.cutoff m ≤ x := (Finset.mem_filter.mp hm_mem).2
  -- Key property: for any i : Fin (K+1) with i.val > m.val, cutoff i > x.
  have hgt : ∀ i : Fin (K + 1), m.val < i.val → x < P.cutoff i := by
    intro i hi
    by_contra hle
    push Not at hle
    have hi_in : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
    have := hm_max i hi_in
    omega
  -- Now construct the witness j : Fin K.
  -- Case split: m = Fin.last K (i.e., m.val = K) or m.val < K.
  by_cases hmK : m.val = K
  · -- m is last; then x = b (since cutoff K = b and x ≤ b, but cutoff m ≤ x).
    -- Pick j = ⟨K-1, _⟩.
    have hcK : P.cutoff m = b := by
      have : m = ⟨K, Nat.lt_succ_self K⟩ := Fin.ext hmK
      rw [this]; exact P.right_eq
    have hxb : x = b := le_antisymm hx.2 (hcK ▸ hm_le)
    let j : Fin K := ⟨K - 1, Nat.sub_lt hKpos Nat.zero_lt_one⟩
    refine ⟨j, ?_, ?_⟩
    · -- x ∈ cellHalfOpen j. Cell j has j.val + 1 = K so it's Icc.
      have hjK : j.val + 1 = K := by simp [j]; omega
      change x ∈ if j.val + 1 = K then Icc (P.leftEndpoint j) (P.rightEndpoint j)
                                  else Ico (P.leftEndpoint j) (P.rightEndpoint j)
      rw [if_pos hjK]
      refine ⟨?_, ?_⟩
      · -- leftEndpoint j ≤ rightEndpoint j - η ≤ b = x (uses η > 0 and width ≥ η)
        rw [hxb]
        linarith [hη j, P.rightEndpoint_le j, hηpos]
      · -- x ≤ rightEndpoint j. j.succ has value K, so cutoff = b.
        have hj_succ : j.succ = ⟨K, Nat.lt_succ_self K⟩ := by
          apply Fin.ext
          simp [j]
          omega
        unfold OrderedCutoffPartition.rightEndpoint
        rw [hj_succ, P.right_eq]
        exact hx.2
    · -- Uniqueness
      intro j' hj'
      -- We need j' = j. Show j'.val = K - 1.
      apply Fin.ext
      -- For the contrary: if j'.val ≠ K-1, then j' < j or j' > j (impossible since j.val = K-1).
      have hj'_lt_K : j'.val < K := j'.isLt
      -- We know x ∈ cellHalfOpen j'.
      -- cell j' has either j'.val + 1 = K (Icc) or not (Ico).
      by_cases hj'K : j'.val + 1 = K
      · -- Both j and j' have val + 1 = K, so j'.val = K-1 = j.val.
        simp [j]; omega
      · -- j'.val + 1 < K, cell j' is Ico, so x < cutoff j'.succ.
        exfalso
        unfold OrderedCutoffPartition.cellHalfOpen at hj'
        rw [if_neg hj'K] at hj'
        have hxlt : x < P.cutoff j'.succ := hj'.2
        -- But x = b and cutoff j'.succ ≤ cutoff K = b.
        have h_succ_le : P.cutoff j'.succ ≤ b := by
          have hsucc_le : j'.succ ≤ ⟨K, Nat.lt_succ_self K⟩ := by
            rw [Fin.le_iff_val_le_val]
            simp only [Fin.val_succ]
            omega
          have := P.monotone hsucc_le
          rw [P.right_eq] at this
          exact this
        linarith [hxb]
  · -- m.val < K. Take j := ⟨m.val, _⟩.
    have hmval_lt : m.val < K := by
      have := Nat.lt_succ_iff.mp m.isLt
      omega
    let j : Fin K := ⟨m.val, hmval_lt⟩
    have hj_castSucc : j.castSucc = m := by
      apply Fin.ext; rfl
    refine ⟨j, ?_, ?_⟩
    · -- x ∈ cellHalfOpen j
      change x ∈ if j.val + 1 = K then Icc (P.leftEndpoint j) (P.rightEndpoint j)
                                  else Ico (P.leftEndpoint j) (P.rightEndpoint j)
      by_cases hjK : j.val + 1 = K
      · -- Last cell, Icc: leftEndpoint j ≤ x ≤ rightEndpoint j (= b)
        rw [if_pos hjK]
        refine ⟨?_, ?_⟩
        · change P.cutoff j.castSucc ≤ x
          rw [hj_castSucc]; exact hm_le
        · -- rightEndpoint j = cutoff j.succ; j.succ has val = K so it's the last index.
          have hjsucc : j.succ = ⟨K, Nat.lt_succ_self K⟩ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            exact hjK
          change P.cutoff j.succ ≥ x
          rw [hjsucc, P.right_eq]
          exact hx.2
      · -- Interior cell, Ico: leftEndpoint j ≤ x < rightEndpoint j
        rw [if_neg hjK]
        refine ⟨?_, ?_⟩
        · change P.cutoff j.castSucc ≤ x
          rw [hj_castSucc]; exact hm_le
        · -- x < cutoff j.succ. j.succ.val = m.val + 1 > m.val
          change x < P.cutoff j.succ
          apply hgt
          have : j.val = m.val := rfl
          rw [Fin.val_succ, this]
          exact Nat.lt_succ_self _
    · -- Uniqueness
      intro j' hj'
      apply Fin.ext
      -- We claim j'.val = m.val.
      -- Show j'.castSucc.val = m.val by squeeze.
      -- From x ∈ cell j', cutoff j'.castSucc ≤ x.
      have hle' : P.cutoff j'.castSucc ≤ x := by
        unfold OrderedCutoffPartition.cellHalfOpen at hj'
        split_ifs at hj' <;> exact hj'.1
      -- So j'.castSucc ∈ S, hence j'.castSucc.val ≤ m.val.
      have hj'_in : j'.castSucc ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle'⟩
      have hj'_le_m : j'.castSucc.val ≤ m.val := hm_max _ hj'_in
      -- Conversely, x < cutoff j'.succ if cell is Ico, or x ≤ cutoff j'.succ if Icc.
      -- Show `m.val ≤ j'.val`: by maximality of `m`, if
      -- `cutoff (j'.val + 1) ≤ x`, then `j'.val + 1 ≤ m.val`.
      -- Since `x ∈ cell j'`, either `x < cutoff j'.succ` or, in the last cell,
      -- `x ≤ cutoff j'.succ`.
      have hj'_le_m' : j'.val ≤ m.val := hj'_le_m
      by_cases hj'K : j'.val + 1 = K
      · -- Last cell case: x ≤ cutoff j'.succ = b. But m.val < K, so this doesn't directly help.
        -- From `j'.val ≤ m.val < K` and `j'.val + 1 = K`, get
        -- `m.val = K - 1 = j'.val`.
        have hjval : j'.val = K - 1 := by omega
        -- j.val is definitionally m.val; squeeze j'.val = K-1 against j'.val ≤ m.val < K.
        change j'.val = m.val
        omega
      · -- Interior cell: x < cutoff j'.succ.
        unfold OrderedCutoffPartition.cellHalfOpen at hj'
        rw [if_neg hj'K] at hj'
        have hxlt : x < P.cutoff j'.succ := hj'.2
        -- So j'.succ ∉ S (cutoff > x).
        have h_not_in : j'.succ ∉ S := by
          intro h
          have : P.cutoff j'.succ ≤ x := (Finset.mem_filter.mp h).2
          linarith
        -- So j'.succ.val > m.val (otherwise contradiction with cutoff x bound)
        -- Actually we need: m.val ≤ j'.val.
        -- By contradiction: if m.val > j'.val, then m.val ≥ j'.val + 1 = j'.succ.val.
        -- Since m ∈ S means cutoff m ≤ x. Need to show j'.val ≥ m.val.
        -- We have j'.val = j'.castSucc.val ≤ m.val. Need m.val ≤ j'.val.
        -- m ∈ S and m.val > j'.val ⇒ m.val ≥ j'.val + 1 = j'.succ.val.
        -- Monotonicity gives `cutoff j'.succ ≤ cutoff m ≤ x`, contradicting
        -- `cutoff j'.succ > x`.
        -- j.val is definitionally m.val; we have j'.val ≤ m.val and need equality.
        change j'.val = m.val
        by_contra hne
        push Not at hne
        -- hne : j'.val ≠ m.val. Combined with j'.val ≤ m.val (from hj'_le_m'), j'.val < m.val.
        have hlt : j'.val < m.val := lt_of_le_of_ne hj'_le_m' hne
        -- So j'.succ.val ≤ m.val.
        have hsv_le : (j'.succ.val : ℕ) ≤ m.val := by
          rw [Fin.val_succ]; omega
        have hmono : P.cutoff j'.succ ≤ P.cutoff m := P.monotone (by
          change (j'.succ : Fin (K+1)) ≤ m
          rw [Fin.le_iff_val_le_val]; exact hsv_le)
        linarith

end OrderedCutoffPartition

/-! ## Eta-spaced cutoff domain -/

/-- Predicate on raw cutoff vectors: `c` is the cutoff vector of an `OrderedCutoffPartition` —
weakly increasing with fixed endpoints `c 0 = a` and `c (last) = b` — whose cells are `η`-spaced
(each at least `η` wide). -/
def EtaSpacedCutoffs (K : ℕ) (a b η : ℝ) (c : Fin (K + 1) → ℝ) : Prop :=
  ∃ P : OrderedCutoffPartition K a b, P.cutoff = c ∧ P.EtaSpaced η

/-- Canonical partition associated to a cutoff vector in the eta-spaced domain. -/
noncomputable def partitionOfCutoffs {K : ℕ} {a b : ℝ} (η : ℝ)
    (c : {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K a b η c}) :
    OrderedCutoffPartition K a b :=
  Classical.choose c.2

/-- The partition built from a cutoff vector has that vector as its cutpoints. -/
lemma partitionOfCutoffs_cutoff {K : ℕ} {a b : ℝ} (η : ℝ)
    (c : {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K a b η c}) :
    (partitionOfCutoffs η c).cutoff = c.val :=
  (Classical.choose_spec c.2).1

/-- The partition built from an `η`-spaced cutoff vector is `η`-spaced. -/
lemma partitionOfCutoffs_etaSpaced {K : ℕ} {a b : ℝ} (η : ℝ)
    (c : {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K a b η c}) :
    (partitionOfCutoffs η c).EtaSpaced η :=
  (Classical.choose_spec c.2).2

/-- The eta-spaced cutoff domain is compact in `Fin (K+1) → ℝ` (pi-product topology). -/
lemma etaSpaced_domain_isCompact (K : ℕ) {a b : ℝ} (hab : a < b) (η : ℝ) :
    IsCompact {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K a b η c} := by
  -- Equivalent explicit characterization: c 0 = a, c last = b, monotone, gaps ≥ η.
  set S : Set (Fin (K + 1) → ℝ) := {c | EtaSpacedCutoffs K a b η c}
  -- The set is a subset of [a,b]^(K+1).
  have hSsub : S ⊆ Set.univ.pi (fun _ : Fin (K + 1) => Icc a b) := by
    intro c hc
    obtain ⟨P, hP, _⟩ := hc
    intro i _
    refine ⟨?_, ?_⟩
    · have h0 : (0 : Fin (K + 1)) ≤ i := Fin.zero_le _
      have := P.monotone h0
      rw [P.left_eq] at this
      rw [← hP]
      exact this
    · have hi : i ≤ ⟨K, Nat.lt_succ_self K⟩ := by
        simp [Fin.le_iff_val_le_val, Nat.lt_succ_iff.mp i.isLt]
      have := P.monotone hi
      rw [P.right_eq] at this
      rw [← hP]
      exact this
  -- The pi-cube is compact.
  have hCube : IsCompact (Set.univ.pi (fun _ : Fin (K + 1) => Icc a b)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  -- It suffices to show S is closed.
  refine hCube.of_isClosed_subset ?_ hSsub
  -- Closedness: S = (c 0 = a) ∩ (c last = b) ∩ Monotone ∩ (∀ j, η ≤ gap j).
  have hS_eq : S = {c | c 0 = a} ∩ {c | c ⟨K, Nat.lt_succ_self K⟩ = b}
      ∩ {c | ∀ i j : Fin (K + 1), i ≤ j → c i ≤ c j}
      ∩ {c | ∀ j : Fin K, η ≤ c j.succ - c j.castSucc} := by
    ext c
    constructor
    · rintro ⟨P, hP, hEta⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [← hP]; exact P.left_eq
      · rw [← hP]; exact P.right_eq
      · intro i j hij
        rw [← hP]; exact P.monotone hij
      · intro j
        have := hEta j
        unfold OrderedCutoffPartition.leftEndpoint OrderedCutoffPartition.rightEndpoint at this
        rw [hP] at this
        exact this
    · rintro ⟨⟨⟨h0, h1⟩, hmono⟩, hgap⟩
      refine ⟨{ cutoff := c, lt := hab, left_eq := h0, right_eq := h1, monotone := hmono },
        rfl, ?_⟩
      intro j
      exact hgap j
  rw [hS_eq]
  -- Each piece is closed.
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
  · -- {c | c 0 = a}
    exact isClosed_eq (continuous_apply _) continuous_const
  · -- {c | c last = b}
    exact isClosed_eq (continuous_apply _) continuous_const
  · -- Monotone
    rw [show {c : Fin (K + 1) → ℝ | ∀ i j : Fin (K + 1), i ≤ j → c i ≤ c j}
          = ⋂ (i : Fin (K + 1)) (j : Fin (K + 1)) (_ : i ≤ j), {c | c i ≤ c j} by
        ext c; simp]
    refine isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ => ?_)))
    exact isClosed_le (continuous_apply _) (continuous_apply _)
  · -- Gaps ≥ η
    rw [show {c : Fin (K + 1) → ℝ | ∀ j : Fin K, η ≤ c j.succ - c j.castSucc}
          = ⋂ (j : Fin K), {c | η ≤ c j.succ - c j.castSucc} by
        ext c; simp]
    refine isClosed_iInter (fun j => ?_)
    exact isClosed_le continuous_const
      ((continuous_apply _).sub (continuous_apply _))

/-- The eta-spaced cutoff domain is nonempty when `K * η ≤ b - a`: Witnessed by the uniform
partition `c j = a + j · (b - a) / K`. -/
lemma etaSpaced_domain_nonempty (K : ℕ) {a b : ℝ} (hab : a < b) (η : ℝ)
    (hK : 0 < K) (_hη : 0 ≤ η) (hKη : (K : ℝ) * η ≤ b - a) :
    {c : Fin (K + 1) → ℝ | EtaSpacedCutoffs K a b η c}.Nonempty := by
  -- Construct the uniform partition c j = a + j.val * (b - a) / K.
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  have hΔpos : 0 < (b - a) / (K : ℝ) := div_pos (sub_pos.mpr hab) hKR
  let c : Fin (K + 1) → ℝ := fun j => a + (j.val : ℝ) * ((b - a) / (K : ℝ))
  have hmono : Monotone c := by
    intro i j hij
    have : (i.val : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right this hΔpos.le)
  have hc0 : c 0 = a := by simp [c]
  have hcK : c ⟨K, Nat.lt_succ_self K⟩ = b := by
    change a + (K : ℝ) * ((b - a) / (K : ℝ)) = b
    field_simp
    ring
  let P : OrderedCutoffPartition K a b :=
    { cutoff := c
      lt := hab
      left_eq := hc0
      right_eq := hcK
      monotone := hmono }
  refine ⟨c, P, rfl, ?_⟩
  -- EtaSpaced check: each gap is (b-a)/K, and η ≤ (b-a)/K from K*η ≤ b-a.
  intro j
  unfold OrderedCutoffPartition.rightEndpoint OrderedCutoffPartition.leftEndpoint
  change η ≤ c j.succ - c j.castSucc
  have hgap : c j.succ - c j.castSucc = (b - a) / (K : ℝ) := by
    change (a + ((j.succ.val : ℕ) : ℝ) * ((b - a) / (K : ℝ)))
        - (a + ((j.castSucc.val : ℕ) : ℝ) * ((b - a) / (K : ℝ))) = (b - a) / (K : ℝ)
    rw [Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  rw [hgap, le_div_iff₀ hKR]
  linarith [hKη]
