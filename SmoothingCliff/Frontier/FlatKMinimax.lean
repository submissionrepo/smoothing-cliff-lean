import SmoothingCliff.Frontier.FlatK
import SmoothingCliff.Frontier.BandDerivative

/-!
# The all-capacity smooth-selection frontier

This file contains the formal proof atoms introduced with the finite-`K`
frontier in Proposition `prop:flatK`.  The older file `FlatK.lean` proves the
displaced-mass upper bound for capped-simplex projection.  Here we formalize
the new adjacent-profile lower certificate, the fixed-mass bridge from an
own-coordinate modulus to full-vector `L¹` movement, and the exact finite-
population modulus of water filling.
-/

open scoped BigOperators

namespace SmoothingCliff.Frontier

/-- Finite-dimensional `L¹` distance, written explicitly to keep the
smooth-selection certificate independent of a choice of normed-space
instance on function types. -/
noncomputable def finiteL1 {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ := ∑ i, |x i - y i|

theorem finiteL1_triangle {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) : finiteL1 x z ≤ finiteL1 x y + finiteL1 y z := by
  unfold finiteL1
  calc
    ∑ i, |x i - z i| ≤ ∑ i, (|x i - y i| + |y i - z i|) :=
      Finset.sum_le_sum fun i _ => by
        have heq : x i - z i = (x i - y i) + (y i - z i) := by ring
        rw [heq]
        exact abs_add_le _ _
    _ = ∑ i, |x i - y i| + ∑ i, |y i - z i| := Finset.sum_add_distrib

/-- Replace exactly the coordinates in `S` by those of `v`. -/
def replaceOn {ι β : Type*} [DecidableEq ι]
    (S : Finset ι) (u v : ι → β) : ι → β :=
  fun i => if i ∈ S then v i else u i

/-- Coordinatewise `L¹` bounds telescope to a full-vector bound. -/
theorem finiteL1_le_of_coordinate_bounds
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (p : (ι → β) → ι → ℝ) (cost : β → β → ℝ) (C : ℝ)
    (hcoord : ∀ u i z,
      finiteL1 (p (Function.update u i z)) (p u) ≤ C * cost z (u i))
    (u v : ι → β) :
    finiteL1 (p v) (p u) ≤ C * ∑ i, cost (v i) (u i) := by
  classical
  have hsubset : ∀ S : Finset ι,
      finiteL1 (p (replaceOn S u v)) (p u) ≤
        C * ∑ i ∈ S, cost (v i) (u i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        have hrep : replaceOn (∅ : Finset ι) u v = u := by
          funext i
          simp [replaceOn]
        rw [hrep]
        simp [finiteL1]
    | @insert i S hiS ih =>
        have hrep : replaceOn (insert i S) u v =
            Function.update (replaceOn S u v) i (v i) := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [replaceOn, hiS]
          · simp [replaceOn, hji]
        have hbase : replaceOn S u v i = u i := by simp [replaceOn, hiS]
        calc
          finiteL1 (p (replaceOn (insert i S) u v)) (p u) =
              finiteL1 (p (Function.update (replaceOn S u v) i (v i))) (p u) :=
            by rw [hrep]
          _ ≤ finiteL1 (p (Function.update (replaceOn S u v) i (v i)))
                (p (replaceOn S u v)) + finiteL1 (p (replaceOn S u v)) (p u) :=
            finiteL1_triangle _ _ _
          _ ≤ C * cost (v i) (replaceOn S u v i) +
                C * ∑ j ∈ S, cost (v j) (u j) := add_le_add
            (hcoord (replaceOn S u v) i (v i)) ih
          _ = C * ∑ j ∈ insert i S, cost (v j) (u j) := by
            rw [hbase, Finset.sum_insert hiS]
            ring
  have hfull := hsubset (Finset.univ : Finset ι)
  have hrep : replaceOn (Finset.univ : Finset ι) u v = v := by
    funext i
    simp [replaceOn]
  rw [hrep] at hfull
  simpa using hfull

/-! ## Symmetrization of direct-score rules -/

noncomputable instance permFintype
    {ι : Type*} [Fintype ι] : Fintype (Equiv.Perm ι) :=
  Fintype.ofFinite _

/-- Relabel a real vector by a candidate permutation. -/
def permuteVector {ι : Type*} (σ : Equiv.Perm ι) (u : ι → ℝ) : ι → ℝ :=
  fun i => u (σ.symm i)

theorem permuteVector_mul {ι : Type*} (σ τ : Equiv.Perm ι) (u : ι → ℝ) :
    permuteVector σ (permuteVector τ u) = permuteVector (σ * τ) u := by
  funext i
  unfold permuteVector
  congr 1

theorem finiteL1_permuteVector {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (u v : ι → ℝ) :
    finiteL1 (permuteVector σ u) (permuteVector σ v) = finiteL1 u v := by
  unfold finiteL1 permuteVector
  exact Equiv.sum_comp σ.symm (fun i => |u i - v i|)

/-- Right multiplication by a fixed permutation is a bijection of the
permutation group. -/
def permMulRight {ι : Type*} (τ : Equiv.Perm ι) :
    Equiv.Perm ι ≃ Equiv.Perm ι where
  toFun σ := σ * τ
  invFun σ := σ * τ⁻¹
  left_inv σ := by simp
  right_inv σ := by simp

/-- Conjugate a direct-score rule by a candidate permutation. -/
def conjugateScoreRule {ι : Type*}
    (p : (ι → ℝ) → ι → ℝ) (σ : Equiv.Perm ι) :
    (ι → ℝ) → ι → ℝ :=
  fun u i => p (permuteVector σ u) (σ i)

/-- Uniform average over all candidate relabelings. -/
noncomputable def symmetrizeScoreRule {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) : (ι → ℝ) → ι → ℝ :=
  fun u i =>
    (∑ σ : Equiv.Perm ι, conjugateScoreRule p σ u i) /
      (Fintype.card (Equiv.Perm ι) : ℝ)

theorem symmetrizeScoreRule_equivariant
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (τ : Equiv.Perm ι) (u : ι → ℝ) (i : ι) :
    symmetrizeScoreRule p (permuteVector τ u) (τ i) =
      symmetrizeScoreRule p u i := by
  unfold symmetrizeScoreRule conjugateScoreRule
  congr 1
  calc
    ∑ σ : Equiv.Perm ι, p (permuteVector σ (permuteVector τ u)) (σ (τ i)) =
        ∑ σ : Equiv.Perm ι, p (permuteVector (σ * τ) u) ((σ * τ) i) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [permuteVector_mul, Equiv.Perm.mul_apply]
    _ = ∑ ρ : Equiv.Perm ι, p (permuteVector ρ u) (ρ i) :=
      Equiv.sum_comp (permMulRight τ)
        (fun ρ : Equiv.Perm ι => p (permuteVector ρ u) (ρ i))

/-- Symmetrization preserves exact total mass. -/
theorem symmetrizeScoreRule_mass
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (mass : ℝ)
    (hMass : ∀ u, ∑ i, p u i = mass) (u : ι → ℝ) :
    ∑ i, symmetrizeScoreRule p u i = mass := by
  classical
  have hqNat : 0 < Fintype.card (Equiv.Perm ι) := Fintype.card_pos
  have hq : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hqNat)
  unfold symmetrizeScoreRule conjugateScoreRule
  rw [← Finset.sum_div, Finset.sum_comm]
  have hinner : ∀ σ : Equiv.Perm ι,
      ∑ i, p (permuteVector σ u) (σ i) = mass := by
    intro σ
    rw [Equiv.sum_comp σ]
    exact hMass (permuteVector σ u)
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ), Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  field_simp

/-- `L¹` distance between uniform averages is at most the average `L¹`
distance. -/
theorem finiteL1_uniformAverage_le
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (f g : α → ι → ℝ) :
    finiteL1
        (fun i => (∑ a, f a i) / (Fintype.card α : ℝ))
        (fun i => (∑ a, g a i) / (Fintype.card α : ℝ)) ≤
      (∑ a, finiteL1 (f a) (g a)) / (Fintype.card α : ℝ) := by
  classical
  have hqNat : 0 < Fintype.card α := Fintype.card_pos
  have hq : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hqNat
  unfold finiteL1
  have hpoint : ∀ i : ι,
      |(∑ a, f a i) / (Fintype.card α : ℝ) -
          (∑ a, g a i) / (Fintype.card α : ℝ)| ≤
        (∑ a, |f a i - g a i|) / (Fintype.card α : ℝ) := by
    intro i
    have hdiv : (∑ a, f a i) / (Fintype.card α : ℝ) -
        (∑ a, g a i) / (Fintype.card α : ℝ) =
        (∑ a, (f a i - g a i)) / (Fintype.card α : ℝ) := by
      rw [Finset.sum_sub_distrib]
      ring
    rw [hdiv]
    rw [abs_div, abs_of_pos hq]
    have habs : |∑ a, (f a i - g a i)| ≤ ∑ a, |f a i - g a i| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun a : α => f a i - g a i) Finset.univ)
    exact div_le_div_of_nonneg_right habs hq.le
  calc
    ∑ i, |(∑ a, f a i) / (Fintype.card α : ℝ) -
        (∑ a, g a i) / (Fintype.card α : ℝ)| ≤
        ∑ i, (∑ a, |f a i - g a i|) / (Fintype.card α : ℝ) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ a, ∑ i, |f a i - g a i|) / (Fintype.card α : ℝ) := by
      rw [← Finset.sum_div, Finset.sum_comm]

/-- Averaging over permutations preserves a full-vector `L¹` modulus. -/
theorem symmetrizeScoreRule_l1_le
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (Lambda : ℝ)
    (hLip : ∀ u v, finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (u v : ι → ℝ) :
    finiteL1 (symmetrizeScoreRule p u) (symmetrizeScoreRule p v) ≤
      Lambda * finiteL1 u v := by
  let f : Equiv.Perm ι → ι → ℝ := fun σ => conjugateScoreRule p σ u
  let g : Equiv.Perm ι → ι → ℝ := fun σ => conjugateScoreRule p σ v
  have havg := finiteL1_uniformAverage_le f g
  have hterm : ∀ σ : Equiv.Perm ι,
      finiteL1 (f σ) (g σ) ≤ Lambda * finiteL1 u v := by
    intro σ
    unfold f g conjugateScoreRule
    have hreindex : finiteL1
        (fun i => p (permuteVector σ u) (σ i))
        (fun i => p (permuteVector σ v) (σ i)) =
        finiteL1 (p (permuteVector σ u)) (p (permuteVector σ v)) := by
      unfold finiteL1
      exact Equiv.sum_comp σ
        (fun i => |p (permuteVector σ u) i - p (permuteVector σ v) i|)
    rw [hreindex]
    calc
      finiteL1 (p (permuteVector σ u)) (p (permuteVector σ v)) ≤
          Lambda * finiteL1 (permuteVector σ u) (permuteVector σ v) :=
        hLip _ _
      _ = Lambda * finiteL1 u v := by rw [finiteL1_permuteVector]
  have hsum : (∑ σ, finiteL1 (f σ) (g σ)) /
      (Fintype.card (Equiv.Perm ι) : ℝ) ≤ Lambda * finiteL1 u v := by
    calc
      (∑ σ, finiteL1 (f σ) (g σ)) /
          (Fintype.card (Equiv.Perm ι) : ℝ) ≤
          (∑ _σ : Equiv.Perm ι, Lambda * finiteL1 u v) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by
        gcongr with σ
        exact hterm σ
      _ = Lambda * finiteL1 u v := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        have hq : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by positivity
        field_simp
  exact havg.trans hsum

/-- Dot product of a marginal vector with its score profile. -/
noncomputable def scoreValue {ι : Type*} [Fintype ι]
    (allocation scores : ι → ℝ) : ℝ :=
  ∑ i, scores i * allocation i

def negateVector {ι : Type*} (u : ι → ℝ) : ι → ℝ := fun i => -u i

def oneMinusVector {ι : Type*} (u : ι → ℝ) : ι → ℝ := fun i => 1 - u i

def constantMinusVector {ι : Type*} (c : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i => c - u i

noncomputable def vectorSum {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  ∑ i, u i

/-- Score of a fixed candidate subset. -/
noncomputable def subsetScore {ι : Type*} (T : Finset ι) (u : ι → ℝ) : ℝ :=
  ∑ i ∈ T, u i

/-- The feasible `K`-subsets of a finite candidate set. -/
def kSubsets {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℕ) :
    Finset (Finset ι) :=
  (Finset.univ : Finset ι).powersetCard K

theorem kSubsets_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ℕ} (hK : K ≤ Fintype.card ι) : (kSubsets (ι := ι) K).Nonempty := by
  simpa [kSubsets] using
    (Finset.powersetCard_nonempty.mpr (by simpa using hK) :
      ((Finset.univ : Finset ι).powersetCard K).Nonempty)

/-- Deterministic top-`K` benchmark, defined as the maximum score of a
`K`-subset. -/
noncomputable def topKScore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (u : ι → ℝ) : ℝ :=
  let scores := (kSubsets (ι := ι) K).image (fun T => subsetScore T u)
  scores.max' ((kSubsets_nonempty hK).image _)

theorem subsetScore_le_topKScore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (u : ι → ℝ)
    (T : Finset ι) (hT : T.card = K) :
    subsetScore T u ≤ topKScore K hK u := by
  unfold topKScore
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  exact ⟨T, by simp [kSubsets, hT], rfl⟩

theorem exists_subsetScore_eq_topKScore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (u : ι → ℝ) :
    ∃ T : Finset ι, T.card = K ∧ subsetScore T u = topKScore K hK u := by
  unfold topKScore
  have hmem := Finset.max'_mem
    ((kSubsets (ι := ι) K).image (fun T => subsetScore T u))
    ((kSubsets_nonempty hK).image (fun T => subsetScore T u))
  rcases Finset.mem_image.mp hmem with ⟨T, hT, hscore⟩
  refine ⟨T, ?_, hscore⟩
  simpa [kSubsets] using hT

theorem subsetScore_map_permute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (T : Finset ι) (u : ι → ℝ) :
    subsetScore (T.map σ.toEmbedding) (permuteVector σ u) = subsetScore T u := by
  unfold subsetScore
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  simp [permuteVector]

theorem topKScore_permute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι)
    (σ : Equiv.Perm ι) (u : ι → ℝ) :
    topKScore K hK (permuteVector σ u) = topKScore K hK u := by
  obtain ⟨T, hTcard, hTscore⟩ := exists_subsetScore_eq_topKScore K hK u
  have hforward : topKScore K hK u ≤ topKScore K hK (permuteVector σ u) := by
    rw [← hTscore, ← subsetScore_map_permute σ T u]
    apply subsetScore_le_topKScore K hK
    simpa using hTcard
  obtain ⟨R, hRcard, hRscore⟩ :=
    exists_subsetScore_eq_topKScore K hK (permuteVector σ u)
  let T' : Finset ι := R.map (σ⁻¹).toEmbedding
  have hbackScore : subsetScore T' u = subsetScore R (permuteVector σ u) := by
    have h := subsetScore_map_permute (σ⁻¹) R (permuteVector σ u)
    simpa [T', permuteVector_mul] using h
  have hback : topKScore K hK (permuteVector σ u) ≤ topKScore K hK u := by
    rw [← hRscore, ← hbackScore]
    apply subsetScore_le_topKScore K hK
    simpa [T'] using hRcard
  exact le_antisymm hback hforward

theorem subsetScore_complement_negate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (u : ι → ℝ) :
    subsetScore ((Finset.univ : Finset ι) \ T) (negateVector u) =
      subsetScore T u - vectorSum u := by
  unfold subsetScore negateVector vectorSum
  have hsplit :
      ∑ i ∈ (Finset.univ : Finset ι) \ T, u i + ∑ i ∈ T, u i = ∑ i, u i :=
    Finset.sum_sdiff (Finset.subset_univ T)
  rw [show (∑ i ∈ (Finset.univ : Finset ι) \ T, -u i) =
    -(∑ i ∈ (Finset.univ : Finset ι) \ T, u i) by
      rw [← Finset.sum_neg_distrib]]
  linarith

theorem subsetScore_complement_oneMinus
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (T : Finset ι) (hT : T.card = K) (u : ι → ℝ) :
    subsetScore ((Finset.univ : Finset ι) \ T) (oneMinusVector u) =
      ((Fintype.card ι - K : ℕ) : ℝ) - vectorSum u + subsetScore T u := by
  unfold subsetScore oneMinusVector vectorSum
  have hsplit :
      ∑ i ∈ (Finset.univ : Finset ι) \ T, u i + ∑ i ∈ T, u i = ∑ i, u i :=
    Finset.sum_sdiff (Finset.subset_univ T)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ_diff, hT]
  linarith

/-- Negating scores exchanges selecting `K` candidates with excluding `K`
candidates.  This is the benchmark identity behind the `K ↔ n-K`
reduction on the unbounded score domain. -/
theorem topKScore_complement_negate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (u : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) (negateVector u) =
      topKScore K hK u - vectorSum u := by
  let Kc := Fintype.card ι - K
  have hKc : Kc ≤ Fintype.card ι := by
    dsimp [Kc]
    exact Nat.sub_le _ _
  obtain ⟨T, hTcard, hTscore⟩ := exists_subsetScore_eq_topKScore K hK u
  let R : Finset ι := (Finset.univ : Finset ι) \ T
  have hRcard : R.card = Kc := by
    rw [show R.card = ((Finset.univ : Finset ι) \ T).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
      hTcard]
  have hforward : topKScore K hK u - vectorSum u ≤
      topKScore Kc hKc (negateVector u) := by
    rw [← hTscore, ← subsetScore_complement_negate T u]
    exact subsetScore_le_topKScore Kc hKc _ R hRcard
  obtain ⟨R', hR'card, hR'score⟩ :=
    exists_subsetScore_eq_topKScore Kc hKc (negateVector u)
  let T' : Finset ι := (Finset.univ : Finset ι) \ R'
  have hT'card : T'.card = K := by
    rw [show T'.card = ((Finset.univ : Finset ι) \ R').card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ R'), Finset.card_univ,
      hR'card]
    exact Nat.sub_sub_self hK
  have hdouble : (Finset.univ : Finset ι) \ T' = R' := by
    ext i
    simp [T']
  have hbackScore : subsetScore R' (negateVector u) =
      subsetScore T' u - vectorSum u := by
    rw [← hdouble]
    exact subsetScore_complement_negate T' u
  have hback : topKScore Kc hKc (negateVector u) ≤
      topKScore K hK u - vectorSum u := by
    rw [← hR'score, hbackScore]
    exact sub_le_sub_right (subsetScore_le_topKScore K hK u T' hT'card) _
  exact le_antisymm hback hforward

/-- On the unit cube, complementing every score exchanges capacity `K` with
capacity `n-K` and adds the corresponding affine benchmark shift. -/
theorem topKScore_complement_oneMinus
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (u : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) (oneMinusVector u) =
      (((Fintype.card ι - K : ℕ) : ℝ) - vectorSum u) + topKScore K hK u := by
  let Kc := Fintype.card ι - K
  have hKc : Kc ≤ Fintype.card ι := by
    dsimp [Kc]
    exact Nat.sub_le _ _
  obtain ⟨T, hTcard, hTscore⟩ := exists_subsetScore_eq_topKScore K hK u
  let R : Finset ι := (Finset.univ : Finset ι) \ T
  have hRcard : R.card = Kc := by
    rw [show R.card = ((Finset.univ : Finset ι) \ T).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
      hTcard]
  have hforward : (((Kc : ℕ) : ℝ) - vectorSum u) + topKScore K hK u ≤
      topKScore Kc hKc (oneMinusVector u) := by
    rw [← hTscore]
    have hidentity := subsetScore_complement_oneMinus K T hTcard u
    rw [← show subsetScore R (oneMinusVector u) =
        ((Kc : ℕ) : ℝ) - vectorSum u + subsetScore T u by
      simpa [R, Kc] using hidentity]
    exact subsetScore_le_topKScore Kc hKc _ R hRcard
  obtain ⟨R', hR'card, hR'score⟩ :=
    exists_subsetScore_eq_topKScore Kc hKc (oneMinusVector u)
  let T' : Finset ι := (Finset.univ : Finset ι) \ R'
  have hT'card : T'.card = K := by
    rw [show T'.card = ((Finset.univ : Finset ι) \ R').card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ R'), Finset.card_univ,
      hR'card]
    exact Nat.sub_sub_self hK
  have hdouble : (Finset.univ : Finset ι) \ T' = R' := by
    ext i
    simp [T']
  have hbackScore : subsetScore R' (oneMinusVector u) =
      ((Kc : ℕ) : ℝ) - vectorSum u + subsetScore T' u := by
    rw [← hdouble]
    simpa [Kc] using subsetScore_complement_oneMinus K T' hT'card u
  have hback : topKScore Kc hKc (oneMinusVector u) ≤
      (((Kc : ℕ) : ℝ) - vectorSum u) + topKScore K hK u := by
    rw [← hR'score, hbackScore]
    linarith [subsetScore_le_topKScore K hK u T' hT'card]
  exact le_antisymm hback hforward

theorem topKScore_exclusion_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y =
      topKScore K hK (negateVector y) + vectorSum y := by
  have hdouble : negateVector (negateVector y) = y := by
    funext i
    simp [negateVector]
  have hsum : vectorSum (negateVector y) = -vectorSum y := by
    unfold vectorSum negateVector
    rw [← Finset.sum_neg_distrib]
  have h := topKScore_complement_negate K hK (negateVector y)
  rw [hdouble, hsum] at h
  linarith

theorem topKScore_cube_exclusion_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y =
      topKScore K hK (oneMinusVector y) +
        (((Fintype.card ι - K : ℕ) : ℝ) - vectorSum (oneMinusVector y)) := by
  have hdouble : oneMinusVector (oneMinusVector y) = y := by
    funext i
    simp [oneMinusVector]
  have h := topKScore_complement_oneMinus K hK (oneMinusVector y)
  rw [hdouble] at h
  linarith

theorem scoreValue_conjugateScoreRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    scoreValue (conjugateScoreRule p σ u) u =
      scoreValue (p (permuteVector σ u)) (permuteVector σ u) := by
  unfold scoreValue conjugateScoreRule
  calc
    ∑ i, u i * p (permuteVector σ u) (σ i) =
        ∑ i, permuteVector σ u (σ i) * p (permuteVector σ u) (σ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [permuteVector]
    _ = ∑ j, permuteVector σ u j * p (permuteVector σ u) j :=
      Equiv.sum_comp σ
        (fun j => permuteVector σ u j * p (permuteVector σ u) j)

/-- The value of the symmetrized rule is the average value of the original
rule on permuted profiles. -/
theorem scoreValue_symmetrizeScoreRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (u : ι → ℝ) :
    scoreValue (symmetrizeScoreRule p u) u =
      (∑ σ : Equiv.Perm ι,
        scoreValue (p (permuteVector σ u)) (permuteVector σ u)) /
          (Fintype.card (Equiv.Perm ι) : ℝ) := by
  classical
  unfold scoreValue symmetrizeScoreRule
  calc
    ∑ i, u i *
        ((∑ σ : Equiv.Perm ι, conjugateScoreRule p σ u i) /
          (Fintype.card (Equiv.Perm ι) : ℝ)) =
        ∑ i, (∑ σ : Equiv.Perm ι,
          u i * conjugateScoreRule p σ u i) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      ring
    _ =
        (∑ i, ∑ σ : Equiv.Perm ι,
          u i * conjugateScoreRule p σ u i) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by
      rw [Finset.sum_div]
    _ = (∑ σ : Equiv.Perm ι, ∑ i,
          u i * conjugateScoreRule p σ u i) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by rw [Finset.sum_comm]
    _ = (∑ σ : Equiv.Perm ι,
        scoreValue (p (permuteVector σ u)) (permuteVector σ u)) /
          (Fintype.card (Equiv.Perm ι) : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ hσ
      exact scoreValue_conjugateScoreRule p σ u

/-- For every permutation-invariant benchmark, regret of the symmetrized rule
is exactly average regret of the original rule over permuted profiles. -/
theorem symmetrizeScoreRule_regret_eq_average
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (benchmark : (ι → ℝ) → ℝ)
    (hInvariant : ∀ σ u, benchmark (permuteVector σ u) = benchmark u)
    (u : ι → ℝ) :
    benchmark u - scoreValue (symmetrizeScoreRule p u) u =
      (∑ σ : Equiv.Perm ι,
        (benchmark (permuteVector σ u) -
          scoreValue (p (permuteVector σ u)) (permuteVector σ u))) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by
  classical
  have hq : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by positivity
  rw [scoreValue_symmetrizeScoreRule]
  have hB : (∑ σ : Equiv.Perm ι, benchmark (permuteVector σ u)) =
      (Fintype.card (Equiv.Perm ι) : ℝ) * benchmark u := by
    rw [Finset.sum_congr rfl (fun σ _ => hInvariant σ u), Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ]
  rw [Finset.sum_sub_distrib, hB]
  field_simp

/-- Consequently, symmetrization does not increase worst-case regret. -/
theorem symmetrizeScoreRule_regret_le
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (benchmark : (ι → ℝ) → ℝ)
    (hInvariant : ∀ σ u, benchmark (permuteVector σ u) = benchmark u)
    (R : ℝ)
    (hRegret : ∀ u, benchmark u - scoreValue (p u) u ≤ R)
    (u : ι → ℝ) :
    benchmark u - scoreValue (symmetrizeScoreRule p u) u ≤ R := by
  rw [symmetrizeScoreRule_regret_eq_average p benchmark hInvariant u]
  have hq : (0 : ℝ) < (Fintype.card (Equiv.Perm ι) : ℝ) := by positivity
  rw [div_le_iff₀ hq]
  calc
    ∑ σ : Equiv.Perm ι,
        (benchmark (permuteVector σ u) -
          scoreValue (p (permuteVector σ u)) (permuteVector σ u)) ≤
        ∑ _σ : Equiv.Perm ι, R := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact hRegret (permuteVector σ u)
    _ = R * (Fintype.card (Equiv.Perm ι) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-! ### Symmetrization restricted to the unit cube -/

/-- Coordinatewise membership in the bounded score domain. -/
def InUnitCube {ι : Type*} (u : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ u i ∧ u i ≤ 1

theorem inUnitCube_permuteVector
    {ι : Type*} (σ : Equiv.Perm ι) {u : ι → ℝ}
    (hu : InUnitCube u) : InUnitCube (permuteVector σ u) := by
  intro i
  exact hu (σ.symm i)

theorem inUnitCube_oneMinusVector
    {ι : Type*} {u : ι → ℝ} (hu : InUnitCube u) :
    InUnitCube (oneMinusVector u) := by
  intro i
  have hi := hu i
  constructor <;> simp only [oneMinusVector] <;> linarith

/-- Local mass preservation suffices for symmetrization on the bounded score
domain; no extension of the rule outside the cube is used. -/
theorem symmetrizeScoreRule_mass_on_cube
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (mass : ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = mass)
    (u : ι → ℝ) (hu : InUnitCube u) :
    ∑ i, symmetrizeScoreRule p u i = mass := by
  classical
  have hqNat : 0 < Fintype.card (Equiv.Perm ι) := Fintype.card_pos
  have hq : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hqNat)
  unfold symmetrizeScoreRule conjugateScoreRule
  rw [← Finset.sum_div, Finset.sum_comm]
  have hinner : ∀ σ : Equiv.Perm ι,
      ∑ i, p (permuteVector σ u) (σ i) = mass := by
    intro σ
    rw [Equiv.sum_comp σ]
    exact hMass (permuteVector σ u) (inUnitCube_permuteVector σ hu)
  rw [Finset.sum_congr rfl (fun σ _ => hinner σ), Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  field_simp

/-- A modulus assumed only on the cube is preserved by symmetrization there. -/
theorem symmetrizeScoreRule_l1_le_on_cube
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (Lambda : ℝ)
    (hLip : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (u v : ι → ℝ) (hu : InUnitCube u) (hv : InUnitCube v) :
    finiteL1 (symmetrizeScoreRule p u) (symmetrizeScoreRule p v) ≤
      Lambda * finiteL1 u v := by
  let f : Equiv.Perm ι → ι → ℝ := fun σ => conjugateScoreRule p σ u
  let g : Equiv.Perm ι → ι → ℝ := fun σ => conjugateScoreRule p σ v
  have havg := finiteL1_uniformAverage_le f g
  have hterm : ∀ σ : Equiv.Perm ι,
      finiteL1 (f σ) (g σ) ≤ Lambda * finiteL1 u v := by
    intro σ
    unfold f g conjugateScoreRule
    have hreindex : finiteL1
        (fun i => p (permuteVector σ u) (σ i))
        (fun i => p (permuteVector σ v) (σ i)) =
        finiteL1 (p (permuteVector σ u)) (p (permuteVector σ v)) := by
      unfold finiteL1
      exact Equiv.sum_comp σ
        (fun i => |p (permuteVector σ u) i - p (permuteVector σ v) i|)
    rw [hreindex]
    calc
      finiteL1 (p (permuteVector σ u)) (p (permuteVector σ v)) ≤
          Lambda * finiteL1 (permuteVector σ u) (permuteVector σ v) :=
        hLip _ (inUnitCube_permuteVector σ hu) _
          (inUnitCube_permuteVector σ hv)
      _ = Lambda * finiteL1 u v := by rw [finiteL1_permuteVector]
  have hsum : (∑ σ, finiteL1 (f σ) (g σ)) /
      (Fintype.card (Equiv.Perm ι) : ℝ) ≤ Lambda * finiteL1 u v := by
    calc
      (∑ σ, finiteL1 (f σ) (g σ)) /
          (Fintype.card (Equiv.Perm ι) : ℝ) ≤
          (∑ _σ : Equiv.Perm ι, Lambda * finiteL1 u v) /
            (Fintype.card (Equiv.Perm ι) : ℝ) := by
        gcongr with σ
        exact hterm σ
      _ = Lambda * finiteL1 u v := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        have hq : (Fintype.card (Equiv.Perm ι) : ℝ) ≠ 0 := by positivity
        field_simp
  exact havg.trans hsum

/-- Uniform regret on the cube passes to the symmetrized rule at every cube
profile. -/
theorem symmetrizeScoreRule_regret_le_on_cube
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (benchmark : (ι → ℝ) → ℝ)
    (hInvariant : ∀ σ u, benchmark (permuteVector σ u) = benchmark u)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u → benchmark u - scoreValue (p u) u ≤ R)
    (u : ι → ℝ) (hu : InUnitCube u) :
    benchmark u - scoreValue (symmetrizeScoreRule p u) u ≤ R := by
  rw [symmetrizeScoreRule_regret_eq_average p benchmark hInvariant u]
  have hq : (0 : ℝ) < (Fintype.card (Equiv.Perm ι) : ℝ) := by positivity
  rw [div_le_iff₀ hq]
  calc
    ∑ σ : Equiv.Perm ι,
        (benchmark (permuteVector σ u) -
          scoreValue (p (permuteVector σ u)) (permuteVector σ u)) ≤
        ∑ _σ : Equiv.Perm ι, R := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact hRegret (permuteVector σ u) (inUnitCube_permuteVector σ hu)
    _ = R * (Fintype.card (Equiv.Perm ι) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-! ## Inclusion-exclusion complementation -/

/-- Exclusion transform on the unbounded score domain. -/
def excludeScoreRule {ι : Type*}
    (p : (ι → ℝ) → ι → ℝ) : (ι → ℝ) → ι → ℝ :=
  fun y i => 1 - p (negateVector y) i

/-- Exclusion transform on the unit cube. -/
def excludeCubeRule {ι : Type*}
    (p : (ι → ℝ) → ι → ℝ) : (ι → ℝ) → ι → ℝ :=
  fun y i => 1 - p (oneMinusVector y) i

/-- Local exclusion transform reflected about an arbitrary constant `c`. -/
def excludeAffineRule {ι : Type*}
    (p : (ι → ℝ) → ι → ℝ) (c : ℝ) : (ι → ℝ) → ι → ℝ :=
  fun y i => 1 - p (constantMinusVector c y) i

theorem excludeScoreRule_equivariant
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (σ : Equiv.Perm ι) (y : ι → ℝ) (i : ι) :
    excludeScoreRule p (permuteVector σ y) (σ i) = excludeScoreRule p y i := by
  have hcommute : negateVector (permuteVector σ y) =
      permuteVector σ (negateVector y) := by
    funext j
    simp [negateVector, permuteVector]
  unfold excludeScoreRule
  rw [hcommute, hEquivariant σ (negateVector y) i]

theorem excludeCubeRule_equivariant
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (σ : Equiv.Perm ι) (y : ι → ℝ) (i : ι) :
    excludeCubeRule p (permuteVector σ y) (σ i) = excludeCubeRule p y i := by
  have hcommute : oneMinusVector (permuteVector σ y) =
      permuteVector σ (oneMinusVector y) := by
    funext j
    simp [oneMinusVector, permuteVector]
  unfold excludeCubeRule
  rw [hcommute, hEquivariant σ (oneMinusVector y) i]

theorem excludeScoreRule_mass
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K) (y : ι → ℝ) :
    ∑ i, excludeScoreRule p y i = (Fintype.card ι : ℝ) - K := by
  unfold excludeScoreRule
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, hMass]
  ring

theorem excludeCubeRule_mass
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K) (y : ι → ℝ) :
    ∑ i, excludeCubeRule p y i = (Fintype.card ι : ℝ) - K := by
  unfold excludeCubeRule
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, hMass]
  ring

theorem finiteL1_negateVector {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    finiteL1 (negateVector u) (negateVector v) = finiteL1 u v := by
  unfold finiteL1 negateVector
  apply Finset.sum_congr rfl
  intro i hi
  rw [show -u i - -v i = -(u i - v i) by ring, abs_neg]

theorem finiteL1_oneMinusVector {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    finiteL1 (oneMinusVector u) (oneMinusVector v) = finiteL1 u v := by
  unfold finiteL1 oneMinusVector
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 - u i) - (1 - v i) = -(u i - v i) by ring, abs_neg]

theorem finiteL1_excludeScoreRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (u v : ι → ℝ) :
    finiteL1 (excludeScoreRule p u) (excludeScoreRule p v) =
      finiteL1 (p (negateVector u)) (p (negateVector v)) := by
  unfold finiteL1 excludeScoreRule
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 - p (negateVector u) i) - (1 - p (negateVector v) i) =
    -(p (negateVector u) i - p (negateVector v) i) by ring, abs_neg]

theorem finiteL1_excludeCubeRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (u v : ι → ℝ) :
    finiteL1 (excludeCubeRule p u) (excludeCubeRule p v) =
      finiteL1 (p (oneMinusVector u)) (p (oneMinusVector v)) := by
  unfold finiteL1 excludeCubeRule
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 - p (oneMinusVector u) i) - (1 - p (oneMinusVector v) i) =
    -(p (oneMinusVector u) i - p (oneMinusVector v) i) by ring, abs_neg]

/-- Both exclusion transforms preserve the full-vector modulus. -/
theorem excludeScoreRule_l1_le
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (Lambda : ℝ)
    (hLip : ∀ u v, finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (u v : ι → ℝ) :
    finiteL1 (excludeScoreRule p u) (excludeScoreRule p v) ≤
      Lambda * finiteL1 u v := by
  rw [finiteL1_excludeScoreRule]
  calc
    finiteL1 (p (negateVector u)) (p (negateVector v)) ≤
        Lambda * finiteL1 (negateVector u) (negateVector v) := hLip _ _
    _ = Lambda * finiteL1 u v := by rw [finiteL1_negateVector]

theorem excludeCubeRule_l1_le
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (Lambda : ℝ)
    (hLip : ∀ u v, finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (u v : ι → ℝ) :
    finiteL1 (excludeCubeRule p u) (excludeCubeRule p v) ≤
      Lambda * finiteL1 u v := by
  rw [finiteL1_excludeCubeRule]
  calc
    finiteL1 (p (oneMinusVector u)) (p (oneMinusVector v)) ≤
        Lambda * finiteL1 (oneMinusVector u) (oneMinusVector v) := hLip _ _
    _ = Lambda * finiteL1 u v := by rw [finiteL1_oneMinusVector]

theorem scoreValue_excludeScoreRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (y : ι → ℝ) :
    scoreValue (excludeScoreRule p y) y =
      vectorSum y + scoreValue (p (negateVector y)) (negateVector y) := by
  unfold scoreValue excludeScoreRule vectorSum negateVector
  calc
    ∑ i, y i * (1 - p (fun i => -y i) i) =
        ∑ i, (y i + (-y i) * p (fun i => -y i) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, y i + ∑ i, -y i * p (fun i => -y i) i :=
      Finset.sum_add_distrib

theorem scoreValue_excludeCubeRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K) (y : ι → ℝ) :
    scoreValue (excludeCubeRule p y) y =
      ((Fintype.card ι : ℝ) - K) - vectorSum (oneMinusVector y) +
        scoreValue (p (oneMinusVector y)) (oneMinusVector y) := by
  unfold scoreValue excludeCubeRule vectorSum oneMinusVector
  have hm := hMass (fun i => 1 - y i)
  calc
    ∑ i, y i * (1 - p (fun i => 1 - y i) i) =
        ∑ i, ((1 - p (fun i => 1 - y i) i) - (1 - y i) +
          (1 - y i) * p (fun i => 1 - y i) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Fintype.card ι : ℝ) - K - ∑ i, (1 - y i) +
        ∑ i, (1 - y i) * p (fun i => 1 - y i) i := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, hm]
      ring

/-- Profile-local version of the bounded exclusion value identity. -/
theorem scoreValue_excludeCubeRule_of_profile_mass
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (K : ℝ) (y : ι → ℝ)
    (hMass : ∑ i, p (oneMinusVector y) i = K) :
    scoreValue (excludeCubeRule p y) y =
      ((Fintype.card ι : ℝ) - K) - vectorSum (oneMinusVector y) +
        scoreValue (p (oneMinusVector y)) (oneMinusVector y) := by
  change ∑ i, p (fun i => 1 - y i) i = K at hMass
  unfold scoreValue excludeCubeRule vectorSum oneMinusVector
  calc
    ∑ i, y i * (1 - p (fun i => 1 - y i) i) =
        ∑ i, ((1 - p (fun i => 1 - y i) i) - (1 - y i) +
          (1 - y i) * p (fun i => 1 - y i) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (Fintype.card ι : ℝ) - K - ∑ i, (1 - y i) +
        ∑ i, (1 - y i) * p (fun i => 1 - y i) i := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, hMass]
      ring

/-- Regret is preserved by unbounded complementation whenever the benchmark
obeys the corresponding inclusion-exclusion identity. -/
theorem excludeScoreRule_regret_eq
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ)
    (benchmark benchmarkExc : (ι → ℝ) → ℝ)
    (hBenchmark : ∀ y,
      benchmarkExc y = benchmark (negateVector y) + vectorSum y)
    (y : ι → ℝ) :
    benchmarkExc y - scoreValue (excludeScoreRule p y) y =
      benchmark (negateVector y) -
        scoreValue (p (negateVector y)) (negateVector y) := by
  rw [hBenchmark, scoreValue_excludeScoreRule]
  ring

/-- Bounded-cube complementation preserves regret under the unit-reflection
benchmark identity. -/
theorem excludeCubeRule_regret_eq
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K)
    (benchmark benchmarkExc : (ι → ℝ) → ℝ)
    (hBenchmark : ∀ y,
      benchmarkExc y = benchmark (oneMinusVector y) +
        ((Fintype.card ι : ℝ) - K) - vectorSum (oneMinusVector y))
    (y : ι → ℝ) :
    benchmarkExc y - scoreValue (excludeCubeRule p y) y =
      benchmark (oneMinusVector y) -
        scoreValue (p (oneMinusVector y)) (oneMinusVector y) := by
  rw [hBenchmark, scoreValue_excludeCubeRule p K hMass]
  ring

theorem excludeScoreRule_topK_regret_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι)
    (p : (ι → ℝ) → ι → ℝ) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y -
        scoreValue (excludeScoreRule p y) y =
      topKScore K hK (negateVector y) -
        scoreValue (p (negateVector y)) (negateVector y) := by
  exact excludeScoreRule_regret_eq p (topKScore K hK)
    (topKScore (Fintype.card ι - K) (Nat.sub_le _ _))
    (topKScore_exclusion_identity K hK) y

theorem excludeCubeRule_topK_regret_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι)
    (p : (ι → ℝ) → ι → ℝ)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ)) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y -
        scoreValue (excludeCubeRule p y) y =
      topKScore K hK (oneMinusVector y) -
        scoreValue (p (oneMinusVector y)) (oneMinusVector y) := by
  apply excludeCubeRule_regret_eq p (K : ℝ) hMass (topKScore K hK)
    (topKScore (Fintype.card ι - K) (Nat.sub_le _ _))
  · intro z
    have h := topKScore_cube_exclusion_identity K hK z
    norm_num [Nat.cast_sub hK] at h
    convert h using 1
    all_goals ring

/-- Cube complementation needs the original mass identity only at the reflected
profile. -/
theorem excludeCubeRule_topK_regret_eq_of_profile_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι)
    (p : (ι → ℝ) → ι → ℝ) (y : ι → ℝ)
    (hMass : ∑ i, p (oneMinusVector y) i = (K : ℝ)) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y -
        scoreValue (excludeCubeRule p y) y =
      topKScore K hK (oneMinusVector y) -
        scoreValue (p (oneMinusVector y)) (oneMinusVector y) := by
  rw [topKScore_cube_exclusion_identity K hK y,
    scoreValue_excludeCubeRule_of_profile_mass p (K : ℝ) y hMass]
  norm_num [Nat.cast_sub hK]
  ring

theorem excludeAffineRule_equivariant
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (c : ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (σ : Equiv.Perm ι) (y : ι → ℝ) (i : ι) :
    excludeAffineRule p c (permuteVector σ y) (σ i) =
      excludeAffineRule p c y i := by
  have hcommute : constantMinusVector c (permuteVector σ y) =
      permuteVector σ (constantMinusVector c y) := by
    funext j
    simp [constantMinusVector, permuteVector]
  unfold excludeAffineRule
  rw [hcommute, hEquivariant σ (constantMinusVector c y) i]

theorem excludeAffineRule_mass
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (c K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K) (y : ι → ℝ) :
    ∑ i, excludeAffineRule p c y i = (Fintype.card ι : ℝ) - K := by
  unfold excludeAffineRule
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, hMass]
  ring

theorem finiteL1_constantMinusVector
    {ι : Type*} [Fintype ι] (c : ℝ) (u v : ι → ℝ) :
    finiteL1 (constantMinusVector c u) (constantMinusVector c v) =
      finiteL1 u v := by
  unfold finiteL1 constantMinusVector
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (c - u i) - (c - v i) = -(u i - v i) by ring, abs_neg]

theorem finiteL1_excludeAffineRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (c : ℝ) (u v : ι → ℝ) :
    finiteL1 (excludeAffineRule p c u) (excludeAffineRule p c v) =
      finiteL1 (p (constantMinusVector c u))
        (p (constantMinusVector c v)) := by
  unfold finiteL1 excludeAffineRule
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 - p (constantMinusVector c u) i) -
      (1 - p (constantMinusVector c v) i) =
    -(p (constantMinusVector c u) i - p (constantMinusVector c v) i) by ring,
    abs_neg]

theorem excludeAffineRule_l1_le
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (c Lambda : ℝ)
    (hLip : ∀ u v, finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (u v : ι → ℝ) :
    finiteL1 (excludeAffineRule p c u) (excludeAffineRule p c v) ≤
      Lambda * finiteL1 u v := by
  rw [finiteL1_excludeAffineRule]
  calc
    finiteL1 (p (constantMinusVector c u))
        (p (constantMinusVector c v)) ≤
      Lambda * finiteL1 (constantMinusVector c u) (constantMinusVector c v) :=
        hLip _ _
    _ = Lambda * finiteL1 u v := by rw [finiteL1_constantMinusVector]

/-- Reflection of the cube `[0,Delta]^n` about `r+Delta` stays entirely in
the eligible interval `[r,r+Delta]^n`. -/
theorem constantMinusVector_stays_eligible
    {ι : Type*} (r Delta : ℝ)
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ Delta) (i : ι) :
    r ≤ constantMinusVector (r + Delta) y i ∧
      constantMinusVector (r + Delta) y i ≤ r + Delta := by
  unfold constantMinusVector
  constructor <;> linarith [hy i |>.1, hy i |>.2]

theorem subsetScore_complement_constantMinus
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (T : Finset ι) (hT : T.card = K)
    (c : ℝ) (y : ι → ℝ) :
    subsetScore ((Finset.univ : Finset ι) \ T) y =
      subsetScore T (constantMinusVector c y) + vectorSum y - (K : ℝ) * c := by
  unfold subsetScore constantMinusVector vectorSum
  have hsplit :
      ∑ i ∈ (Finset.univ : Finset ι) \ T, y i + ∑ i ∈ T, y i = ∑ i, y i :=
    Finset.sum_sdiff (Finset.subset_univ T)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hT]
  linarith

theorem topKScore_affine_exclusion_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι) (c : ℝ) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y =
      topKScore K hK (constantMinusVector c y) + vectorSum y - (K : ℝ) * c := by
  let Kc := Fintype.card ι - K
  have hKc : Kc ≤ Fintype.card ι := by
    dsimp [Kc]
    exact Nat.sub_le _ _
  obtain ⟨T, hTcard, hTscore⟩ :=
    exists_subsetScore_eq_topKScore K hK (constantMinusVector c y)
  let R : Finset ι := (Finset.univ : Finset ι) \ T
  have hRcard : R.card = Kc := by
    rw [show R.card = ((Finset.univ : Finset ι) \ T).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
      hTcard]
  have hforward :
      topKScore K hK (constantMinusVector c y) + vectorSum y - (K : ℝ) * c ≤
        topKScore Kc hKc y := by
    rw [← hTscore, ← subsetScore_complement_constantMinus K T hTcard c y]
    exact subsetScore_le_topKScore Kc hKc y R hRcard
  obtain ⟨R', hR'card, hR'score⟩ := exists_subsetScore_eq_topKScore Kc hKc y
  let T' : Finset ι := (Finset.univ : Finset ι) \ R'
  have hT'card : T'.card = K := by
    rw [show T'.card = ((Finset.univ : Finset ι) \ R').card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ R'), Finset.card_univ,
      hR'card]
    exact Nat.sub_sub_self hK
  have hdouble : (Finset.univ : Finset ι) \ T' = R' := by
    ext i
    simp [T']
  have hbackScore : subsetScore R' y =
      subsetScore T' (constantMinusVector c y) + vectorSum y - (K : ℝ) * c := by
    rw [← hdouble]
    exact subsetScore_complement_constantMinus K T' hT'card c y
  have hback : topKScore Kc hKc y ≤
      topKScore K hK (constantMinusVector c y) + vectorSum y - (K : ℝ) * c := by
    rw [← hR'score, hbackScore]
    linarith [subsetScore_le_topKScore K hK (constantMinusVector c y) T' hT'card]
  exact le_antisymm hback hforward

theorem scoreValue_excludeAffineRule
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ) (c K : ℝ)
    (hMass : ∀ u, ∑ i, p u i = K) (y : ι → ℝ) :
    scoreValue (excludeAffineRule p c y) y =
      vectorSum y - c * K +
        scoreValue (p (constantMinusVector c y)) (constantMinusVector c y) := by
  unfold scoreValue excludeAffineRule vectorSum constantMinusVector
  have hm := hMass (fun i => c - y i)
  calc
    ∑ i, y i * (1 - p (fun i => c - y i) i) =
        ∑ i, (y i - c * p (fun i => c - y i) i +
          (c - y i) * p (fun i => c - y i) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, y i - c * K +
        ∑ i, (c - y i) * p (fun i => c - y i) i := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hm]

theorem excludeAffineRule_topK_regret_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ℕ) (hK : K ≤ Fintype.card ι)
    (p : (ι → ℝ) → ι → ℝ)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (c : ℝ) (y : ι → ℝ) :
    topKScore (Fintype.card ι - K) (Nat.sub_le _ _) y -
        scoreValue (excludeAffineRule p c y) y =
      topKScore K hK (constantMinusVector c y) -
        scoreValue (p (constantMinusVector c y)) (constantMinusVector c y) := by
  rw [topKScore_affine_exclusion_identity K hK c y,
    scoreValue_excludeAffineRule p c (K : ℝ) hMass]
  ring

/-! ## Equivariant two-block profiles -/

/-- A score profile with score `Delta` on `H` and zero off `H`. -/
def blockScore {ι : Type*} [DecidableEq ι]
    (H : Finset ι) (Delta : ℝ) : ι → ℝ :=
  fun i => if i ∈ H then Delta else 0

def adjacentMoving (n K : ℕ) (_hKpos : 1 ≤ K) (hKn : K < n) : Fin n :=
  ⟨K - 1, by omega⟩

def adjacentTrailer (n K : ℕ) (hKn : K < n) : Fin n :=
  ⟨K, hKn⟩

def adjacentMinusScore (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (Delta : ℝ) : Fin n → ℝ :=
  blockScore (Finset.Iio (adjacentMoving n K hKpos hKn)) Delta

def adjacentPlusScore (n K : ℕ) (_hKpos : 1 ≤ K) (hKn : K < n)
    (Delta : ℝ) : Fin n → ℝ :=
  blockScore (Finset.Iio (adjacentTrailer n K hKn)) Delta

theorem blockScore_inUnitCube
    {ι : Type*} [DecidableEq ι] (H : Finset ι) {Delta : ℝ}
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    InUnitCube (blockScore H Delta) := by
  intro i
  by_cases hi : i ∈ H <;> simp [blockScore, hi, hDelta0, hDelta1]

theorem adjacentMinusScore_inUnitCube
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n) {Delta : ℝ}
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    InUnitCube (adjacentMinusScore n K hKpos hKn Delta) := by
  exact blockScore_inUnitCube _ hDelta0 hDelta1

theorem adjacentPlusScore_inUnitCube
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n) {Delta : ℝ}
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    InUnitCube (adjacentPlusScore n K hKpos hKn Delta) := by
  exact blockScore_inUnitCube _ hDelta0 hDelta1

/-- An equivariant rule assigns equal marginals to candidates with equal
scores.  The proof applies the transposition of the two candidates. -/
theorem equivariantScoreRule_equal_of_score_eq
    {ι : Type*} [Fintype ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (u : ι → ℝ) (i j : ι) (hscore : u i = u j) :
    p u i = p u j := by
  classical
  let σ : Equiv.Perm ι := Equiv.swap i j
  have hprofile : permuteVector σ u = u := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [permuteVector, σ, hscore]
    · by_cases hkj : k = j
      · subst k
        simp [permuteVector, σ, hscore]
      · rw [show permuteVector σ u k = u ((Equiv.swap i j) k) by
          simp [permuteVector, σ]]
        rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hEquivariant σ u i
  rw [hprofile] at h
  simpa [σ] using h.symm

/-- On a two-block profile, equivariance makes the rule constant inside each
block. -/
theorem equivariantScoreRule_block_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (H : Finset ι) (Delta : ℝ) (i j : ι)
    (hsame : (i ∈ H) = (j ∈ H)) :
    p (blockScore H Delta) i = p (blockScore H Delta) j := by
  apply equivariantScoreRule_equal_of_score_eq p hEquivariant
  by_cases hi : i ∈ H
  · have hj : j ∈ H := hsame.mp hi
    simp [blockScore, hi, hj]
  · have hj : j ∉ H := by
      intro hj
      exact hi (hsame.mpr hj)
    simp [blockScore, hi, hj]

/-- Sum a rule that is constant on a finite block. -/
theorem sum_eq_card_mul_of_constant
    {ι : Type*} [Fintype ι]
    (S : Finset ι) (f : ι → ℝ) (c : ℝ)
    (hconstant : ∀ i ∈ S, f i = c) :
    ∑ i ∈ S, f i = (S.card : ℝ) * c := by
  calc
    ∑ i ∈ S, f i = ∑ _i ∈ S, c := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hconstant i hi
    _ = (S.card : ℝ) * c := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem equivariantScoreRule_sum_on_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (H : Finset ι) (Delta : ℝ) (representative : ι)
    (hRepresentative : representative ∈ H) :
    ∑ i ∈ H, p (blockScore H Delta) i =
      (H.card : ℝ) * p (blockScore H Delta) representative := by
  apply sum_eq_card_mul_of_constant
  intro i hi
  apply equivariantScoreRule_block_constant p hEquivariant
  simp [hi, hRepresentative]

theorem equivariantScoreRule_sum_off_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : (ι → ℝ) → ι → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm ι) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (H : Finset ι) (Delta : ℝ) (representative : ι)
    (hRepresentative : representative ∉ H) :
    ∑ i ∈ (Finset.univ : Finset ι) \ H, p (blockScore H Delta) i =
      (((Finset.univ : Finset ι) \ H).card : ℝ) *
        p (blockScore H Delta) representative := by
  apply sum_eq_card_mul_of_constant
  intro i hi
  have hiOff : i ∉ H := (Finset.mem_sdiff.mp hi).2
  apply equivariantScoreRule_block_constant p hEquivariant
  simp [hiOff, hRepresentative]

/-- Raising the `K`th coordinate turns the `(K-1)`-high block profile into the
`K`-high profile, so their score-space `L¹` distance is exactly the height of
that one raise. -/
theorem finiteL1_blockScore_Iio_adjacent
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) :
    finiteL1
        (blockScore (Finset.Iio (⟨K, hKn⟩ : Fin n)) Delta)
        (blockScore (Finset.Iio
          (⟨K - 1, by omega⟩ : Fin n)) Delta) = Delta := by
  classical
  let moving : Fin n := ⟨K - 1, by omega⟩
  let trailer : Fin n := ⟨K, hKn⟩
  unfold finiteL1
  rw [Finset.sum_eq_single moving]
  · have hmHigh : moving ∈ (Finset.Iio trailer : Finset (Fin n)) := by
      simp [moving, trailer]
      omega
    have hmLow : moving ∉ (Finset.Iio moving : Finset (Fin n)) := by simp
    simp [blockScore, moving, trailer, hmHigh, hmLow, abs_of_nonneg hDelta]
  · intro i hi hne
    have hmem :
        (i ∈ (Finset.Iio trailer : Finset (Fin n))) =
          (i ∈ (Finset.Iio moving : Finset (Fin n))) := by
      have hneVal : i.val ≠ K - 1 := by
        intro hval
        apply hne
        apply Fin.ext
        simpa [moving] using hval
      apply propext
      simp only [Finset.mem_Iio]
      dsimp only [trailer, moving]
      change i.val < K ↔ i.val < K - 1
      constructor <;> intro hlt <;> omega
    have hscore :
        blockScore (Finset.Iio trailer) Delta i =
          blockScore (Finset.Iio moving) Delta i := by
      by_cases hiT : i ∈ (Finset.Iio trailer : Finset (Fin n))
      · have hiM : i ∈ (Finset.Iio moving : Finset (Fin n)) := hmem.mp hiT
        simp [blockScore, hiT, hiM]
      · have hiM : i ∉ (Finset.Iio moving : Finset (Fin n)) := by
          intro hiM
          exact hiT (hmem.mpr hiM)
        simp [blockScore, hiT, hiM]
    rw [hscore, sub_self, abs_zero]
  · simp

/-- Equivariance turns the full marginal-vector movement between the adjacent
two-block profiles into the three scalar terms used in the lower bound. -/
theorem equivariantScoreRule_adjacent_l1_eq
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (Delta : ℝ) :
    let moving := adjacentMoving n K (by omega) hKn
    let trailer := adjacentTrailer n K hKn
    let first : Fin n := ⟨0, by omega⟩
    let uMinus := adjacentMinusScore n K (by omega) hKn Delta
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    finiteL1 (p uPlus) (p uMinus) =
      (((K - 1 : ℕ) : ℝ) * |p uPlus moving - p uMinus first|) +
        |p uPlus moving - p uMinus moving| +
        (((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving|) := by
  classical
  dsimp only
  let moving := adjacentMoving n K (by omega) hKn
  let trailer := adjacentTrailer n K hKn
  let first : Fin n := ⟨0, by omega⟩
  let Hminus : Finset (Fin n) := Finset.Iio moving
  let Hplus : Finset (Fin n) := Finset.Iio trailer
  let Lplus : Finset (Fin n) := Finset.univ \ Hplus
  let uMinus := adjacentMinusScore n K (by omega) hKn Delta
  let uPlus := adjacentPlusScore n K (by omega) hKn Delta
  have hmHigh : moving ∈ Hplus := by
    simp [moving, trailer, Hplus, adjacentMoving, adjacentTrailer]
    omega
  have hmLow : moving ∉ Hminus := by simp [Hminus]
  have htLow : trailer ∉ Hplus := by simp [Hplus]
  have hsubset : Hminus ⊆ Hplus := by
    intro i hi
    simp only [Hminus, Hplus, Finset.mem_Iio] at hi ⊢
    change i.val < K - 1 at hi
    change i.val < K
    omega
  have hHplus : Hplus = insert moving Hminus := by
    ext i
    simp only [Hplus, Hminus, Finset.mem_Iio, Finset.mem_insert]
    change i.val < K ↔ i = moving ∨ i.val < K - 1
    constructor
    · intro hi
      by_cases him : i.val = K - 1
      · left
        apply Fin.ext
        simpa using him
      · right
        omega
    · intro hi
      rcases hi with him | hi
      · subst i
        change K - 1 < K
        omega
      · omega
  have hHminusCard : Hminus.card = K - 1 := by
    simp [Hminus, moving, adjacentMoving]
  have hHplusCard : Hplus.card = K := by
    simp [Hplus, trailer, adjacentTrailer]
  have hLplusCard : Lplus.card = n - K := by
    rw [show Lplus.card = ((Finset.univ : Finset (Fin n)) \ Hplus).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ Hplus), Finset.card_univ,
      Fintype.card_fin, hHplusCard]
  have hplusOld : ∀ i ∈ Hminus, p uPlus i = p uPlus moving := by
    intro i hi
    have hiPlus : i ∈ Hplus := hsubset hi
    simpa [uPlus, adjacentPlusScore, Hplus, trailer] using
      (equivariantScoreRule_block_constant p hEquivariant Hplus Delta i moving
        (by simp [hiPlus, hmHigh]))
  have hminusOld : ∀ i ∈ Hminus, p uMinus i = p uMinus first := by
    intro i hi
    by_cases hKone : K = 1
    · have hiVal : i.val < K - 1 := by
        simpa only [Hminus, Finset.mem_Iio] using hi
      have : False := by omega
      exact this.elim
    · have hzHigh : first ∈ Hminus := by
        simp [first, moving, Hminus, adjacentMoving]
        omega
      simpa [uMinus, adjacentMinusScore, Hminus, moving] using
        (equivariantScoreRule_block_constant p hEquivariant Hminus Delta i first
          (by simp [hi, hzHigh]))
  have hplusLow : ∀ i ∈ Lplus, p uPlus i = p uPlus trailer := by
    intro i hi
    have hiLow : i ∉ Hplus := (Finset.mem_sdiff.mp hi).2
    simpa [uPlus, adjacentPlusScore, Hplus, trailer] using
      (equivariantScoreRule_block_constant p hEquivariant Hplus Delta i trailer
        (by simp [hiLow, htLow]))
  have hminusLow : ∀ i ∈ Lplus, p uMinus i = p uMinus moving := by
    intro i hi
    have hiNotPlus : i ∉ Hplus := (Finset.mem_sdiff.mp hi).2
    have hiNotMinus : i ∉ Hminus := by
      intro hiMinus
      exact hiNotPlus (hsubset hiMinus)
    simpa [uMinus, adjacentMinusScore, Hminus, moving] using
      (equivariantScoreRule_block_constant p hEquivariant Hminus Delta i moving
        (by simp [hiNotMinus, hmLow]))
  have hsumOld :
      ∑ i ∈ Hminus, |p uPlus i - p uMinus i| =
        (Hminus.card : ℝ) * |p uPlus moving - p uMinus first| := by
    apply sum_eq_card_mul_of_constant
    intro i hi
    rw [hplusOld i hi, hminusOld i hi]
  have hsumLow :
      ∑ i ∈ Lplus, |p uPlus i - p uMinus i| =
        (Lplus.card : ℝ) * |p uPlus trailer - p uMinus moving| := by
    apply sum_eq_card_mul_of_constant
    intro i hi
    rw [hplusLow i hi, hminusLow i hi]
  unfold finiteL1
  have hsplit := Finset.sum_sdiff (Finset.subset_univ Hplus)
    (f := fun i => |p uPlus i - p uMinus i|)
  calc
    ∑ i, |p uPlus i - p uMinus i| =
        (∑ i ∈ Lplus, |p uPlus i - p uMinus i|) +
          ∑ i ∈ Hplus, |p uPlus i - p uMinus i| := by
      change (∑ i, |p uPlus i - p uMinus i|) =
        (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Hplus,
          |p uPlus i - p uMinus i|) +
        ∑ i ∈ Hplus, |p uPlus i - p uMinus i|
      exact hsplit.symm
    _ = (∑ i ∈ Lplus, |p uPlus i - p uMinus i|) +
          (|p uPlus moving - p uMinus moving| +
            ∑ i ∈ Hminus, |p uPlus i - p uMinus i|) := by
      rw [hHplus, Finset.sum_insert hmLow]
    _ = (((K - 1 : ℕ) : ℝ) * |p uPlus moving - p uMinus first|) +
          |p uPlus moving - p uMinus moving| +
          (((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving|) := by
      rw [hsumOld, hsumLow, hHminusCard, hLplusCard]
      ring

/-- Exact mass at the two adjacent profiles becomes the two scalar mass
equations in the lower-bound certificate.  Only those two profiles are used. -/
theorem equivariantScoreRule_adjacent_mass_equations_of_profile_mass
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (Delta : ℝ)
    (hMassMinus : ∑ i, p (adjacentMinusScore n K hKpos hKn Delta) i = (K : ℝ))
    (hMassPlus : ∑ i, p (adjacentPlusScore n K hKpos hKn Delta) i = (K : ℝ)) :
    let moving := adjacentMoving n K (by omega) hKn
    let trailer := adjacentTrailer n K hKn
    let first : Fin n := ⟨0, by omega⟩
    let uMinus := adjacentMinusScore n K (by omega) hKn Delta
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    (((K : ℝ) - 1) * p uMinus first +
        (((n - K : ℕ) : ℝ) + 1) * p uMinus moving = (K : ℝ)) ∧
      ((K : ℝ) * p uPlus moving +
        ((n - K : ℕ) : ℝ) * p uPlus trailer = (K : ℝ)) := by
  classical
  dsimp only
  let moving := adjacentMoving n K (by omega) hKn
  let trailer := adjacentTrailer n K hKn
  let first : Fin n := ⟨0, by omega⟩
  let Hminus : Finset (Fin n) := Finset.Iio moving
  let Hplus : Finset (Fin n) := Finset.Iio trailer
  let Lminus : Finset (Fin n) := Finset.univ \ Hminus
  let Lplus : Finset (Fin n) := Finset.univ \ Hplus
  let uMinus := adjacentMinusScore n K (by omega) hKn Delta
  let uPlus := adjacentPlusScore n K (by omega) hKn Delta
  have hmMinusLow : moving ∉ Hminus := by simp [Hminus]
  have hmPlusHigh : moving ∈ Hplus := by
    simp [moving, trailer, Hplus, adjacentMoving, adjacentTrailer]
    omega
  have htLow : trailer ∉ Hplus := by simp [Hplus]
  have hHminusCard : Hminus.card = K - 1 := by
    simp [Hminus, moving, adjacentMoving]
  have hHplusCard : Hplus.card = K := by
    simp [Hplus, trailer, adjacentTrailer]
  have hLminusCard : Lminus.card = n - K + 1 := by
    rw [show Lminus.card = ((Finset.univ : Finset (Fin n)) \ Hminus).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ Hminus), Finset.card_univ,
      Fintype.card_fin, hHminusCard]
    omega
  have hLplusCard : Lplus.card = n - K := by
    rw [show Lplus.card = ((Finset.univ : Finset (Fin n)) \ Hplus).card by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ Hplus), Finset.card_univ,
      Fintype.card_fin, hHplusCard]
  have hsumHminus : ∑ i ∈ Hminus, p uMinus i =
      (Hminus.card : ℝ) * p uMinus first := by
    by_cases hKone : K = 1
    · have hEmpty : Hminus = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hiVal : i.val < K - 1 := by
          simpa only [Hminus, Finset.mem_Iio] using hi
        omega
      rw [hEmpty]
      simp
    · have hzHigh : first ∈ Hminus := by
        simp [first, moving, Hminus, adjacentMoving]
        omega
      simpa [uMinus, adjacentMinusScore, Hminus, moving] using
        equivariantScoreRule_sum_on_block p hEquivariant Hminus Delta first hzHigh
  have hsumLminus : ∑ i ∈ Lminus, p uMinus i =
      (Lminus.card : ℝ) * p uMinus moving := by
    simpa [uMinus, adjacentMinusScore, Hminus, moving, Lminus] using
      equivariantScoreRule_sum_off_block p hEquivariant Hminus Delta moving hmMinusLow
  have hsumHplus : ∑ i ∈ Hplus, p uPlus i =
      (Hplus.card : ℝ) * p uPlus moving := by
    simpa [uPlus, adjacentPlusScore, Hplus, trailer] using
      equivariantScoreRule_sum_on_block p hEquivariant Hplus Delta moving hmPlusHigh
  have hsumLplus : ∑ i ∈ Lplus, p uPlus i =
      (Lplus.card : ℝ) * p uPlus trailer := by
    simpa [uPlus, adjacentPlusScore, Hplus, trailer, Lplus] using
      equivariantScoreRule_sum_off_block p hEquivariant Hplus Delta trailer htLow
  have htotalMinus :
      (∑ i ∈ Lminus, p uMinus i) + ∑ i ∈ Hminus, p uMinus i = (K : ℝ) := by
    calc
      (∑ i ∈ Lminus, p uMinus i) + ∑ i ∈ Hminus, p uMinus i =
          ∑ i, p uMinus i := by
        change (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Hminus, p uMinus i) +
          ∑ i ∈ Hminus, p uMinus i = ∑ i, p uMinus i
        exact Finset.sum_sdiff (Finset.subset_univ Hminus)
          (f := fun i => p uMinus i)
      _ = (K : ℝ) := by simpa [uMinus] using hMassMinus
  have htotalPlus :
      (∑ i ∈ Lplus, p uPlus i) + ∑ i ∈ Hplus, p uPlus i = (K : ℝ) := by
    calc
      (∑ i ∈ Lplus, p uPlus i) + ∑ i ∈ Hplus, p uPlus i =
          ∑ i, p uPlus i := by
        change (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Hplus, p uPlus i) +
          ∑ i ∈ Hplus, p uPlus i = ∑ i, p uPlus i
        exact Finset.sum_sdiff (Finset.subset_univ Hplus)
          (f := fun i => p uPlus i)
      _ = (K : ℝ) := by simpa [uPlus] using hMassPlus
  rw [hsumLminus, hsumHminus, hLminusCard, hHminusCard] at htotalMinus
  rw [hsumLplus, hsumHplus, hLplusCard, hHplusCard] at htotalPlus
  constructor
  · norm_num [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_add] at htotalMinus ⊢
    linarith
  · linarith

/-- Global fixed mass is a convenient sufficient condition for the preceding
two-profile mass lemma. -/
theorem equivariantScoreRule_adjacent_mass_equations
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Delta : ℝ) :
    let moving := adjacentMoving n K (by omega) hKn
    let trailer := adjacentTrailer n K hKn
    let first : Fin n := ⟨0, by omega⟩
    let uMinus := adjacentMinusScore n K (by omega) hKn Delta
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    (((K : ℝ) - 1) * p uMinus first +
        (((n - K : ℕ) : ℝ) + 1) * p uMinus moving = (K : ℝ)) ∧
      ((K : ℝ) * p uPlus moving +
        ((n - K : ℕ) : ℝ) * p uPlus trailer = (K : ℝ)) := by
  exact equivariantScoreRule_adjacent_mass_equations_of_profile_mass
    n K hKpos hKn p hEquivariant Delta (hMass _) (hMass _)

/-! ## Adjacent-profile algebra -/

/-- The two exact-mass equations at the `(K-1)`-high and `K`-high profiles
imply the two reduced identities used in the adjacent-profile certificate.
The parameters are real-valued casts of the paper's cardinalities. -/
theorem flatK_adjacent_mass_identities
    (K Kc piHminus piLminus piHplus piLplus : ℝ)
    (hmassMinus : (K - 1) * piHminus + (Kc + 1) * piLminus = K)
    (hmassPlus : K * piHplus + Kc * piLplus = K) :
    let Gamma := (K + Kc) * piHplus - K
    let theta := (K - 1) * (piHminus - piHplus)
    (Kc + 1) * (piHplus - piLminus) = Gamma + theta ∧
      Kc * (Kc + 1) * (piLplus - piLminus) = Kc * theta - Gamma := by
  dsimp
  constructor
  · linarith
  · linear_combination (Kc + 1) * hmassPlus - Kc * hmassMinus

/-- Exact reduction of the three-block `L¹` movement to the paper's
`Gamma, theta` coordinates. -/
theorem flatK_adjacent_mass_reduction
    (K Kc piHminus piLminus piHplus piLplus : ℝ)
    (hK : 1 ≤ K) (hKc : 0 < Kc)
    (hmassMinus : (K - 1) * piHminus + (Kc + 1) * piLminus = K)
    (hmassPlus : K * piHplus + Kc * piLplus = K) :
    let Gamma := (K + Kc) * piHplus - K
    let theta := (K - 1) * (piHminus - piHplus)
    (K - 1) * |piHplus - piHminus| + |piHplus - piLminus| +
        Kc * |piLplus - piLminus| =
      |theta| +
        (|Gamma + theta| + |Kc * theta - Gamma|) / (Kc + 1) := by
  dsimp
  have hids := flatK_adjacent_mass_identities K Kc
    piHminus piLminus piHplus piLplus hmassMinus hmassPlus
  have hK0 : 0 ≤ K - 1 := by linarith
  have hden : 0 < Kc + 1 := by linarith
  have hterm1 : (K - 1) * |piHplus - piHminus| =
      |(K - 1) * (piHminus - piHplus)| := by
    rw [abs_mul, abs_of_nonneg hK0, abs_sub_comm]
  have hterm2 : |piHplus - piLminus| =
      |(K + Kc) * piHplus - K + (K - 1) * (piHminus - piHplus)| /
        (Kc + 1) := by
    calc
      |piHplus - piLminus| =
          ((Kc + 1) * |piHplus - piLminus|) / (Kc + 1) := by
        field_simp
      _ = |(Kc + 1) * (piHplus - piLminus)| / (Kc + 1) := by
        rw [abs_mul, abs_of_pos hden]
      _ = |(K + Kc) * piHplus - K +
          (K - 1) * (piHminus - piHplus)| / (Kc + 1) := by rw [hids.1]
  have hterm3 : Kc * |piLplus - piLminus| =
      |Kc * ((K - 1) * (piHminus - piHplus)) -
        ((K + Kc) * piHplus - K)| / (Kc + 1) := by
    calc
      Kc * |piLplus - piLminus| =
          (Kc * (Kc + 1) * |piLplus - piLminus|) / (Kc + 1) := by
        field_simp
      _ = |Kc * (Kc + 1) * (piLplus - piLminus)| / (Kc + 1) := by
        rw [abs_mul, abs_mul, abs_of_pos hKc, abs_of_pos hden]
      _ = |Kc * ((K - 1) * (piHminus - piHplus)) -
          ((K + Kc) * piHplus - K)| / (Kc + 1) := by rw [hids.2]
  rw [hterm1, hterm2, hterm3]
  ring

/-- Two triangle inequalities give the sharp lower bound on the reduced
adjacent-profile movement. -/
theorem flatK_adjacent_tv_lower
    (Gamma theta Kc : ℝ) (hGamma : 0 ≤ Gamma) (hKc : 0 ≤ Kc) :
    (Kc + 1) * |theta| + |Gamma + theta| + |Kc * theta - Gamma| ≥
      2 * Gamma := by
  have hfirst : Gamma ≤ |theta| + |Gamma + theta| := by
    calc
      Gamma = |Gamma| := (abs_of_nonneg hGamma).symm
      _ = |(Gamma + theta) + (-theta)| := by ring_nf
      _ ≤ |Gamma + theta| + |-theta| := abs_add_le _ _
      _ = |theta| + |Gamma + theta| := by rw [abs_neg]; ring
  have hsecond : Gamma ≤ Kc * |theta| + |Kc * theta - Gamma| := by
    calc
      Gamma = |Gamma| := (abs_of_nonneg hGamma).symm
      _ = |Kc * theta - (Kc * theta - Gamma)| := by ring_nf
      _ ≤ |Kc * theta| + |-(Kc * theta - Gamma)| := by
        simpa only [sub_eq_add_neg] using
          abs_add_le (Kc * theta) (-(Kc * theta - Gamma))
      _ = Kc * |theta| + |Kc * theta - Gamma| := by
        rw [abs_neg, abs_mul, abs_of_nonneg hKc]
  linarith

/-- Dividing the preceding inequality by `Kc+1` is the exact analytic step
that turns full-vector smoothness into a cap on the high-candidate
probability. -/
theorem flatK_adjacent_gamma_cap
    (Gamma theta Kc Lambda Delta movement : ℝ)
    (hGamma : 0 ≤ Gamma) (hKc : 0 ≤ Kc)
    (hmove : movement =
      |theta| + (|Gamma + theta| + |Kc * theta - Gamma|) / (Kc + 1))
    (hsmooth : movement ≤ Lambda * Delta) :
    Gamma ≤ (Kc + 1) * Lambda * Delta / 2 := by
  have hden : 0 < Kc + 1 := by linarith
  have htv := flatK_adjacent_tv_lower Gamma theta Kc hGamma hKc
  have hscaled : 2 * Gamma / (Kc + 1) ≤ movement := by
    calc
      2 * Gamma / (Kc + 1) ≤
          ((Kc + 1) * |theta| + |Gamma + theta| +
            |Kc * theta - Gamma|) / (Kc + 1) :=
        div_le_div_of_nonneg_right htv hden.le
      _ = movement := by
        rw [hmove]
        field_simp
        ring
  calc
    Gamma ≤ (Kc + 1) * movement / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      rw [div_le_iff₀ hden] at hscaled
      nlinarith
    _ ≤ (Kc + 1) * (Lambda * Delta) / 2 := by
      gcongr
    _ = (Kc + 1) * Lambda * Delta / 2 := by ring

/-- Probability form of the adjacent-profile cap. -/
theorem flatK_adjacent_probability_cap
    (n K Kc piHplus Lambda Delta : ℝ)
    (hn : 0 < n)
    (hcap : n * piHplus - K ≤ (Kc + 1) * Lambda * Delta / 2) :
    piHplus ≤ K / n + (Kc + 1) * Lambda * Delta / (2 * n) := by
  have hmain : piHplus ≤
      (K + (Kc + 1) * Lambda * Delta / 2) / n := by
    rw [le_div_iff₀ hn]
    linarith
  calc
    piHplus ≤ (K + (Kc + 1) * Lambda * Delta / 2) / n := hmain
    _ = K / n + (Kc + 1) * Lambda * Delta / (2 * n) := by
      field_simp

/-- The probability cap directly yields the one-branch regret quadratic. -/
theorem flatK_adjacent_regret_lower
    (n K Kc piHplus Lambda Delta : ℝ)
    (hn : n ≠ 0) (hK : 0 ≤ K) (hDelta : 0 ≤ Delta)
    (hsum : K + Kc = n)
    (hcap : piHplus ≤ K / n + (Kc + 1) * Lambda * Delta / (2 * n)) :
    K * Delta * (1 - piHplus) ≥
      K * Delta * (Kc / n - (Kc + 1) * Lambda * Delta / (2 * n)) := by
  have hone : 1 - (K / n + (Kc + 1) * Lambda * Delta / (2 * n)) =
      Kc / n - (Kc + 1) * Lambda * Delta / (2 * n) := by
    field_simp [hn]
    linarith
  have hmono : 1 - piHplus ≥
      1 - (K / n + (Kc + 1) * Lambda * Delta / (2 * n)) := by linarith
  rw [← hone]
  exact mul_le_mul_of_nonneg_left hmono (mul_nonneg hK hDelta)

/-- The one-branch quadratic at its unconstrained optimizer has the displayed
closed form. -/
theorem flatK_adjacent_regret_optimizer
    (n K Kc Lambda : ℝ)
    (hn : n ≠ 0) (hLambda : Lambda ≠ 0) (hKcp : Kc + 1 ≠ 0) :
    let Delta := Kc / (Lambda * (Kc + 1))
    K * Delta *
        (Kc / n - (Kc + 1) * Lambda * Delta / (2 * n)) =
      K * Kc ^ 2 / (2 * Lambda * n * (Kc + 1)) := by
  dsimp
  field_simp
  ring

/-- Complete scalar adjacent-profile certificate.  Its hypotheses are exactly
the two mass equations and the one-coordinate full-vector smoothness bound
obtained after symmetrization. -/
theorem flatK_adjacent_branch_certificate
    (n K Kc piHminus piLminus piHplus piLplus Lambda Delta : ℝ)
    (hn : 0 < n) (hsum : K + Kc = n)
    (hK : 1 ≤ K) (hKc : 0 < Kc)
    (hLambda : 0 ≤ Lambda) (hDelta : 0 ≤ Delta)
    (hmassMinus : (K - 1) * piHminus + (Kc + 1) * piLminus = K)
    (hmassPlus : K * piHplus + Kc * piLplus = K)
    (hsmooth :
      (K - 1) * |piHplus - piHminus| + |piHplus - piLminus| +
          Kc * |piLplus - piLminus| ≤ Lambda * Delta) :
    K * Delta * (1 - piHplus) ≥
      K * Delta * (Kc / n - (Kc + 1) * Lambda * Delta / (2 * n)) := by
  let Gamma := n * piHplus - K
  let theta := (K - 1) * (piHminus - piHplus)
  have hmove := flatK_adjacent_mass_reduction K Kc
    piHminus piLminus piHplus piLplus hK hKc hmassMinus hmassPlus
  have hmove' :
      (K - 1) * |piHplus - piHminus| + |piHplus - piLminus| +
          Kc * |piLplus - piLminus| =
        |theta| + (|Gamma + theta| + |Kc * theta - Gamma|) / (Kc + 1) := by
    simpa [Gamma, theta, hsum] using hmove
  have hcap : piHplus ≤
      K / n + (Kc + 1) * Lambda * Delta / (2 * n) := by
    by_cases hGamma : 0 ≤ Gamma
    · have hgammaCap : Gamma ≤ (Kc + 1) * Lambda * Delta / 2 := by
        apply flatK_adjacent_gamma_cap Gamma theta Kc Lambda Delta
          ((K - 1) * |piHplus - piHminus| + |piHplus - piLminus| +
            Kc * |piLplus - piLminus|)
        · exact hGamma
        · exact hKc.le
        · exact hmove'
        · exact hsmooth
      apply flatK_adjacent_probability_cap n K Kc piHplus Lambda Delta hn
      simpa [Gamma] using hgammaCap
    · have hbelow : piHplus ≤ K / n := by
        have : Gamma < 0 := lt_of_not_ge hGamma
        change n * piHplus - K < 0 at this
        rw [le_div_iff₀ hn]
        linarith
      have hextra : 0 ≤ (Kc + 1) * Lambda * Delta / (2 * n) := by positivity
      linarith
  exact flatK_adjacent_regret_lower n K Kc piHplus Lambda Delta
    hn.ne' (by linarith) hDelta hsum hcap

/-- The functional adjacent-profile lower bound needs mass and smoothness only
at the two displayed profiles.  This local form is the one used for the
bounded-score frontier. -/
theorem equivariantScoreRule_adjacent_branch_of_profile_bounds
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (Lambda Delta : ℝ) (hLambda : 0 ≤ Lambda) (hDelta : 0 ≤ Delta)
    (hMassMinus :
      ∑ i, p (adjacentMinusScore n K hKpos hKn Delta) i = (K : ℝ))
    (hMassPlus :
      ∑ i, p (adjacentPlusScore n K hKpos hKn Delta) i = (K : ℝ))
    (hSmooth : finiteL1
      (p (adjacentPlusScore n K hKpos hKn Delta))
      (p (adjacentMinusScore n K hKpos hKn Delta)) ≤
        Lambda * finiteL1
          (adjacentPlusScore n K hKpos hKn Delta)
          (adjacentMinusScore n K hKpos hKn Delta)) :
    let moving := adjacentMoving n K (by omega) hKn
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    (K : ℝ) * Delta * (1 - p uPlus moving) ≥
      (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) := by
  classical
  dsimp only
  let moving := adjacentMoving n K (by omega) hKn
  let trailer := adjacentTrailer n K hKn
  let first : Fin n := ⟨0, by omega⟩
  let uMinus := adjacentMinusScore n K (by omega) hKn Delta
  let uPlus := adjacentPlusScore n K (by omega) hKn Delta
  have hmassRaw := equivariantScoreRule_adjacent_mass_equations_of_profile_mass
    n K hKpos hKn p hEquivariant Delta hMassMinus hMassPlus
  dsimp only at hmassRaw
  have hmassMinus :
      ((K : ℝ) - 1) * p uMinus first +
          (((n - K : ℕ) : ℝ) + 1) * p uMinus moving = (K : ℝ) := by
    simpa [moving, first, uMinus] using hmassRaw.1
  have hmassPlus :
      (K : ℝ) * p uPlus moving +
          ((n - K : ℕ) : ℝ) * p uPlus trailer = (K : ℝ) := by
    simpa [moving, trailer, uPlus] using hmassRaw.2
  have hl1Raw := equivariantScoreRule_adjacent_l1_eq
    n K hKpos hKn p hEquivariant Delta
  dsimp only at hl1Raw
  have hl1 : finiteL1 (p uPlus) (p uMinus) =
      (((K - 1 : ℕ) : ℝ) * |p uPlus moving - p uMinus first|) +
        |p uPlus moving - p uMinus moving| +
        (((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving|) := by
    simpa [moving, trailer, first, uMinus, uPlus] using hl1Raw
  have hscoreL1 : finiteL1 uPlus uMinus = Delta := by
    simpa [uPlus, uMinus, adjacentPlusScore, adjacentMinusScore] using
      finiteL1_blockScore_Iio_adjacent n K (by omega) hKn Delta hDelta
  have hsmoothVector : finiteL1 (p uPlus) (p uMinus) ≤
      Lambda * finiteL1 uPlus uMinus := by
    simpa [uPlus, uMinus] using hSmooth
  rw [hscoreL1] at hsmoothVector
  norm_num [Nat.cast_sub (show 1 ≤ K by omega)] at hl1
  have hsmooth :
      ((K : ℝ) - 1) * |p uPlus moving - p uMinus first| +
        |p uPlus moving - p uMinus moving| +
        ((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving| ≤
          Lambda * Delta := by
    rw [← hl1]
    exact hsmoothVector
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hsumR : (K : ℝ) + ((n - K : ℕ) : ℝ) = (n : ℝ) := by
    norm_num [Nat.cast_sub (le_of_lt hKn)]
  have hKcR : 0 < ((n - K : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hKn)
  have hcertificate := flatK_adjacent_branch_certificate
    (n : ℝ) (K : ℝ) ((n - K : ℕ) : ℝ)
    (p uMinus first) (p uMinus moving) (p uPlus moving) (p uPlus trailer)
    Lambda Delta hnR hsumR (by exact_mod_cast (show 1 ≤ K by omega))
    hKcR hLambda hDelta hmassMinus hmassPlus hsmooth
  simpa [moving, uPlus] using hcertificate

/-- Functional adjacent-profile lower bound. Starting from an equivariant
fixed-mass rule with a global full-vector modulus, this theorem derives the
paper's scalar regret quadratic without assuming the four block marginals as
primitive data. -/
theorem equivariantScoreRule_adjacent_branch
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda Delta : ℝ) (hLambda : 0 ≤ Lambda) (hDelta : 0 ≤ Delta)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v) :
    let moving := adjacentMoving n K (by omega) hKn
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    (K : ℝ) * Delta * (1 - p uPlus moving) ≥
      (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) := by
  classical
  dsimp only
  let moving := adjacentMoving n K (by omega) hKn
  let trailer := adjacentTrailer n K hKn
  let first : Fin n := ⟨0, by omega⟩
  let uMinus := adjacentMinusScore n K (by omega) hKn Delta
  let uPlus := adjacentPlusScore n K (by omega) hKn Delta
  have hmassRaw := equivariantScoreRule_adjacent_mass_equations
    n K hKpos hKn p hEquivariant hMass Delta
  dsimp only at hmassRaw
  have hmassMinus :
      ((K : ℝ) - 1) * p uMinus first +
          (((n - K : ℕ) : ℝ) + 1) * p uMinus moving = (K : ℝ) := by
    simpa [moving, first, uMinus] using hmassRaw.1
  have hmassPlus :
      (K : ℝ) * p uPlus moving +
          ((n - K : ℕ) : ℝ) * p uPlus trailer = (K : ℝ) := by
    simpa [moving, trailer, uPlus] using hmassRaw.2
  have hl1Raw := equivariantScoreRule_adjacent_l1_eq
    n K hKpos hKn p hEquivariant Delta
  dsimp only at hl1Raw
  have hl1 : finiteL1 (p uPlus) (p uMinus) =
      (((K - 1 : ℕ) : ℝ) * |p uPlus moving - p uMinus first|) +
        |p uPlus moving - p uMinus moving| +
        (((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving|) := by
    simpa [moving, trailer, first, uMinus, uPlus] using hl1Raw
  have hscoreL1 : finiteL1 uPlus uMinus = Delta := by
    simpa [uPlus, uMinus, adjacentPlusScore, adjacentMinusScore] using
      finiteL1_blockScore_Iio_adjacent n K (by omega) hKn Delta hDelta
  have hsmoothVector := hLipschitz uPlus uMinus
  rw [hscoreL1] at hsmoothVector
  norm_num [Nat.cast_sub (show 1 ≤ K by omega)] at hl1
  have hsmooth :
      ((K : ℝ) - 1) * |p uPlus moving - p uMinus first| +
        |p uPlus moving - p uMinus moving| +
        ((n - K : ℕ) : ℝ) * |p uPlus trailer - p uMinus moving| ≤
          Lambda * Delta := by
    rw [← hl1]
    exact hsmoothVector
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hsumR : (K : ℝ) + ((n - K : ℕ) : ℝ) = (n : ℝ) := by
    norm_num [Nat.cast_sub (le_of_lt hKn)]
  have hKcR : 0 < ((n - K : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hKn)
  have hcertificate := flatK_adjacent_branch_certificate
    (n : ℝ) (K : ℝ) ((n - K : ℕ) : ℝ)
    (p uMinus first) (p uMinus moving) (p uPlus moving) (p uPlus trailer)
    Lambda Delta hnR hsumR (by exact_mod_cast (show 1 ≤ K by omega))
    hKcR hLambda hDelta hmassMinus hmassPlus
    hsmooth
  simpa [moving, uPlus] using hcertificate

/-- At the `K`-high witness profile, deterministic top-`K` value minus the
value of an equivariant rule is exactly `K * Delta * (1-pi_H)`. -/
theorem equivariantScoreRule_adjacent_regret_eq
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (Delta : ℝ) (hDelta : 0 ≤ Delta) :
    let moving := adjacentMoving n K hKpos hKn
    let uPlus := adjacentPlusScore n K hKpos hKn Delta
    topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (p uPlus) uPlus =
      (K : ℝ) * Delta * (1 - p uPlus moving) := by
  classical
  dsimp only
  let moving := adjacentMoving n K hKpos hKn
  let trailer := adjacentTrailer n K hKn
  let Hplus : Finset (Fin n) := Finset.Iio trailer
  let Lplus : Finset (Fin n) := Finset.univ \ Hplus
  let uPlus := adjacentPlusScore n K hKpos hKn Delta
  have hmHigh : moving ∈ Hplus := by
    simp [moving, trailer, Hplus, adjacentMoving, adjacentTrailer]
    omega
  have hHplusCard : Hplus.card = K := by
    simp [Hplus, trailer, adjacentTrailer]
  have hsubsetValue : subsetScore Hplus uPlus = (K : ℝ) * Delta := by
    unfold subsetScore
    calc
      ∑ i ∈ Hplus, uPlus i = ∑ _i ∈ Hplus, Delta := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [uPlus, adjacentPlusScore, Hplus, trailer, blockScore, hi]
      _ = (Hplus.card : ℝ) * Delta := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (K : ℝ) * Delta := by rw [hHplusCard]
  have htop : topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus =
      (K : ℝ) * Delta := by
    apply le_antisymm
    · obtain ⟨T, hTcard, hTscore⟩ :=
        exists_subsetScore_eq_topKScore K
          (by simpa using (le_of_lt hKn : K ≤ n)) uPlus
      rw [← hTscore]
      unfold subsetScore
      calc
        ∑ i ∈ T, uPlus i ≤ ∑ _i ∈ T, Delta := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hiPlus : i ∈ Hplus
          · simp [uPlus, adjacentPlusScore, Hplus, trailer, blockScore, hiPlus]
          · simp [uPlus, adjacentPlusScore, Hplus, trailer, blockScore,
              hiPlus, hDelta]
        _ = (T.card : ℝ) * Delta := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = (K : ℝ) * Delta := by rw [hTcard]
    · rw [← hsubsetValue]
      exact subsetScore_le_topKScore K
        (by simpa using (le_of_lt hKn : K ≤ n)) uPlus Hplus hHplusCard
  have hhighConstant : ∀ i ∈ Hplus, p uPlus i = p uPlus moving := by
    intro i hi
    simpa [uPlus, adjacentPlusScore, Hplus, trailer] using
      (equivariantScoreRule_block_constant p hEquivariant Hplus Delta i moving
        (by simp [hi, hmHigh]))
  have hsumHigh :
      ∑ i ∈ Hplus, uPlus i * p uPlus i =
        (K : ℝ) * (Delta * p uPlus moving) := by
    calc
      ∑ i ∈ Hplus, uPlus i * p uPlus i =
          ∑ _i ∈ Hplus, Delta * p uPlus moving := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hhighConstant i hi]
        simp [uPlus, adjacentPlusScore, Hplus, trailer, blockScore, hi]
      _ = (Hplus.card : ℝ) * (Delta * p uPlus moving) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (K : ℝ) * (Delta * p uPlus moving) := by rw [hHplusCard]
  have hsumLow : ∑ i ∈ Lplus, uPlus i * p uPlus i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiLow : i ∉ Hplus := (Finset.mem_sdiff.mp hi).2
    simp [uPlus, adjacentPlusScore, Hplus, trailer, blockScore, hiLow]
  have hvalue : scoreValue (p uPlus) uPlus =
      (K : ℝ) * (Delta * p uPlus moving) := by
    unfold scoreValue
    have hsplit := Finset.sum_sdiff (Finset.subset_univ Hplus)
      (f := fun i => uPlus i * p uPlus i)
    calc
      ∑ i, uPlus i * p uPlus i =
          (∑ i ∈ Lplus, uPlus i * p uPlus i) +
            ∑ i ∈ Hplus, uPlus i * p uPlus i := by
        change (∑ i, uPlus i * p uPlus i) =
          (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Hplus,
            uPlus i * p uPlus i) +
          ∑ i ∈ Hplus, uPlus i * p uPlus i
        exact hsplit.symm
      _ = (K : ℝ) * (Delta * p uPlus moving) := by
        rw [hsumLow, zero_add, hsumHigh]
  rw [htop, hvalue]
  ring

/-- The preceding functional certificate stated directly as regret against the
actual deterministic top-`K` benchmark. -/
theorem equivariantScoreRule_adjacent_regret_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda Delta : ℝ) (hLambda : 0 ≤ Lambda) (hDelta : 0 ≤ Delta)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v) :
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (p uPlus) uPlus ≥
      (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) := by
  dsimp only
  rw [equivariantScoreRule_adjacent_regret_eq n K (by omega) hKn p
    hEquivariant Delta hDelta]
  exact equivariantScoreRule_adjacent_branch n K hKpos hKn p hEquivariant
    hMass Lambda Delta hLambda hDelta hLipschitz

/-- The unbounded adjacent witness evaluated at the maximizing gap. -/
theorem equivariantScoreRule_adjacent_optimized_regret_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v) :
    let Delta := ((n - K : ℕ) : ℝ) /
      (Lambda * (((n - K : ℕ) : ℝ) + 1))
    let uPlus := adjacentPlusScore n K (by omega) hKn Delta
    topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (p uPlus) uPlus ≥
      (K : ℝ) * ((n - K : ℕ) : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * (((n - K : ℕ) : ℝ) + 1)) := by
  dsimp only
  let Delta := ((n - K : ℕ) : ℝ) /
    (Lambda * (((n - K : ℕ) : ℝ) + 1))
  let uPlus := adjacentPlusScore n K (by omega) hKn Delta
  have hKc : 0 < ((n - K : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hKn
  have hDelta : 0 ≤ Delta := by
    dsimp [Delta]
    positivity
  have hlower := equivariantScoreRule_adjacent_regret_lower
    n K hKpos hKn p hEquivariant hMass Lambda Delta hLambda.le hDelta hLipschitz
  dsimp only at hlower
  have hopt := flatK_adjacent_regret_optimizer
    (n : ℝ) (K : ℝ) ((n - K : ℕ) : ℝ) Lambda
    (by exact_mod_cast (show n ≠ 0 by omega)) hLambda.ne'
    (by positivity)
  dsimp only at hopt
  calc
    topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (p uPlus) uPlus ≥
      (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta /
            (2 * (n : ℝ))) := by
      simpa [uPlus, Delta] using hlower
    _ = (K : ℝ) * ((n - K : ℕ) : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * (((n - K : ℕ) : ℝ) + 1)) := by
      simpa [Delta] using hopt

/-- Mirror branch obtained by applying the adjacent witness to the exclusion
rule.  The conclusion is stated back in the original rule's regret units. -/
theorem equivariantScoreRule_complement_optimized_regret_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKcPos : 1 ≤ n - K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      p (permuteVector σ u) (σ i) = p u i)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v) :
    let Kc := n - K
    let Delta := (K : ℝ) / (Lambda * ((K : ℝ) + 1))
    let yPlus := adjacentPlusScore n Kc (by omega) (by omega) Delta
    let u := negateVector yPlus
    topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≥
      ((n - K : ℕ) : ℝ) * (K : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * ((K : ℝ) + 1)) := by
  classical
  dsimp only
  let Kc := n - K
  let Delta := (K : ℝ) / (Lambda * ((K : ℝ) + 1))
  let yPlus := adjacentPlusScore n Kc (by omega) (by omega) Delta
  let q := excludeScoreRule p
  have hKle : K ≤ n := le_of_lt hKn
  have hKcLt : Kc < n := by
    dsimp [Kc]
    omega
  have hqEquivariant : ∀ (σ : Equiv.Perm (Fin n)) y i,
      q (permuteVector σ y) (σ i) = q y i := by
    intro σ y i
    exact excludeScoreRule_equivariant p hEquivariant σ y i
  have hqMass : ∀ y, ∑ i, q y i = (Kc : ℝ) := by
    intro y
    have h := excludeScoreRule_mass p (K : ℝ) hMass y
    norm_num [Kc, Nat.cast_sub hKle] at h ⊢
    exact h
  have hqLip : ∀ y z, finiteL1 (q y) (q z) ≤ Lambda * finiteL1 y z := by
    intro y z
    exact excludeScoreRule_l1_le p Lambda hLipschitz y z
  have hqLower := equivariantScoreRule_adjacent_optimized_regret_lower
    n Kc hKcPos hKcLt q hqEquivariant hqMass Lambda hLambda hqLip
  dsimp only at hqLower
  have hNKc : n - Kc = K := by
    dsimp [Kc]
    exact Nat.sub_sub_self hKle
  have hqLower' :
      topKScore Kc (by simpa using (le_of_lt hKcLt : Kc ≤ n)) yPlus -
          scoreValue (q yPlus) yPlus ≥
        (Kc : ℝ) * (K : ℝ) ^ 2 /
          (2 * Lambda * (n : ℝ) * ((K : ℝ) + 1)) := by
    simpa [yPlus, Delta, hNKc] using hqLower
  have hregretEq := excludeScoreRule_topK_regret_eq
    K (by simpa using hKle) p yPlus
  have hregretEq' :
      topKScore Kc (by simpa using (le_of_lt hKcLt : Kc ≤ n)) yPlus -
          scoreValue (q yPlus) yPlus =
        topKScore K (by simpa using hKle) (negateVector yPlus) -
          scoreValue (p (negateVector yPlus)) (negateVector yPlus) := by
    simpa [Kc, q] using hregretEq
  rw [hregretEq'] at hqLower'
  simpa [Kc, Delta, yPlus] using hqLower'

/-- Analytic core of the interior-capacity minimax lower bound.  For an
arbitrary fixed-mass smooth rule, symmetrization produces two explicit
witnesses, one for selection and one for exclusion.  Any uniform regret bound
must dominate both branch constants. -/
theorem scoreRule_two_branch_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKcPos : 1 ≤ n - K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u,
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R) :
    ((K : ℝ) * ((n - K : ℕ) : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * (((n - K : ℕ) : ℝ) + 1)) ≤ R) ∧
      (((n - K : ℕ) : ℝ) * (K : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * ((K : ℝ) + 1)) ≤ R) := by
  classical
  let q := symmetrizeScoreRule p
  have hqEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      q (permuteVector σ u) (σ i) = q u i := by
    intro σ u i
    exact symmetrizeScoreRule_equivariant p σ u i
  have hqMass : ∀ u, ∑ i, q u i = (K : ℝ) := by
    intro u
    exact symmetrizeScoreRule_mass p (K : ℝ) hMass u
  have hqLip : ∀ u v,
      finiteL1 (q u) (q v) ≤ Lambda * finiteL1 u v := by
    intro u v
    exact symmetrizeScoreRule_l1_le p Lambda hLipschitz u v
  have hqRegret : ∀ u,
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (q u) u ≤ R := by
    intro u
    apply symmetrizeScoreRule_regret_le p
      (topKScore K (by simpa using (le_of_lt hKn : K ≤ n)))
      (fun σ z => topKScore_permute K
        (by simpa using (le_of_lt hKn : K ≤ n)) σ z)
      R hRegret u
  constructor
  · let Delta := ((n - K : ℕ) : ℝ) /
      (Lambda * (((n - K : ℕ) : ℝ) + 1))
    let u := adjacentPlusScore n K (by omega) hKn Delta
    have hlower := equivariantScoreRule_adjacent_optimized_regret_lower
      n K hKpos hKn q hqEquivariant hqMass Lambda hLambda hqLip
    dsimp only at hlower
    have hupper := hqRegret u
    have hlower' :
        (K : ℝ) * ((n - K : ℕ) : ℝ) ^ 2 /
            (2 * Lambda * (n : ℝ) * (((n - K : ℕ) : ℝ) + 1)) ≤
          topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
            scoreValue (q u) u := by
      simpa [u, Delta] using hlower
    exact hlower'.trans hupper
  · let Kc := n - K
    let Delta := (K : ℝ) / (Lambda * ((K : ℝ) + 1))
    let y := adjacentPlusScore n Kc (by omega) (by omega) Delta
    let u := negateVector y
    have hlower := equivariantScoreRule_complement_optimized_regret_lower
      n K hKpos hKcPos hKn q hqEquivariant hqMass Lambda hLambda hqLip
    dsimp only at hlower
    have hupper := hqRegret u
    have hlower' :
        ((n - K : ℕ) : ℝ) * (K : ℝ) ^ 2 /
            (2 * Lambda * (n : ℝ) * ((K : ℝ) + 1)) ≤
          topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
            scoreValue (q u) u := by
      simpa [Kc, Delta, y, u] using hlower
    exact hlower'.trans hupper

/-- All-capacity form of the unbounded minimax lower certificate.  This is the
`K_- K_+^2 / (2 Lambda n (K_+ + 1))` endpoint in Proposition `prop:flatK`,
stated for any rule with a uniform regret bound `R`. -/
theorem scoreRule_allCapacity_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLipschitz : ∀ u v,
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u,
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R) :
    let Kminus := min K (n - K)
    let Kplus := max K (n - K)
    (Kminus : ℝ) * (Kplus : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * ((Kplus : ℝ) + 1)) ≤ R := by
  dsimp only
  have hKcPos : 1 ≤ n - K := by omega
  have hbranches := scoreRule_two_branch_lower n K hKpos hKcPos hKn
    p hMass Lambda hLambda hLipschitz R hRegret
  by_cases horder : K ≤ n - K
  · simpa [min_eq_left horder, max_eq_right horder] using hbranches.1
  · have hreverse : n - K ≤ K := by omega
    simpa [min_eq_right hreverse, max_eq_left hreverse] using hbranches.2

/-! ## The bounded score cube -/

/-- A cube-domain rule must incur the adjacent-profile branch at every witness
height `Delta ∈ [0,1]`.  The proof symmetrizes only cube profiles, so it does
not assume an artificial Lipschitz extension to all of `ℝⁿ`. -/
theorem scoreRule_cube_adjacent_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (hLipschitz : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u →
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R)
    (Delta : ℝ) (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) ≤ R := by
  classical
  let q := symmetrizeScoreRule p
  let uMinus := adjacentMinusScore n K hKpos hKn Delta
  let uPlus := adjacentPlusScore n K hKpos hKn Delta
  have huMinus : InUnitCube uMinus := by
    simpa [uMinus] using adjacentMinusScore_inUnitCube
      n K hKpos hKn hDelta0 hDelta1
  have huPlus : InUnitCube uPlus := by
    simpa [uPlus] using adjacentPlusScore_inUnitCube
      n K hKpos hKn hDelta0 hDelta1
  have hqEquivariant : ∀ (σ : Equiv.Perm (Fin n)) u i,
      q (permuteVector σ u) (σ i) = q u i := by
    intro σ u i
    exact symmetrizeScoreRule_equivariant p σ u i
  have hqMassMinus : ∑ i, q uMinus i = (K : ℝ) := by
    exact symmetrizeScoreRule_mass_on_cube p (K : ℝ) hMass uMinus huMinus
  have hqMassPlus : ∑ i, q uPlus i = (K : ℝ) := by
    exact symmetrizeScoreRule_mass_on_cube p (K : ℝ) hMass uPlus huPlus
  have hqSmooth : finiteL1 (q uPlus) (q uMinus) ≤
      Lambda * finiteL1 uPlus uMinus := by
    exact symmetrizeScoreRule_l1_le_on_cube p Lambda hLipschitz
      uPlus uMinus huPlus huMinus
  have hbranch := equivariantScoreRule_adjacent_branch_of_profile_bounds
    n K hKpos hKn q hqEquivariant Lambda Delta hLambda hDelta0
    (by simpa [uMinus] using hqMassMinus)
    (by simpa [uPlus] using hqMassPlus)
    (by simpa [uPlus, uMinus] using hqSmooth)
  dsimp only at hbranch
  have hregretEq := equivariantScoreRule_adjacent_regret_eq
    n K hKpos hKn q hqEquivariant Delta hDelta0
  dsimp only at hregretEq
  have hbenchmarkInvariant : ∀ (σ : Equiv.Perm (Fin n)) u,
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n))
          (permuteVector σ u) =
        topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u := by
    intro σ u
    apply topKScore_permute
  have hqRegret :
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (q uPlus) uPlus ≤ R := by
    exact symmetrizeScoreRule_regret_le_on_cube p
      (topKScore K (by simpa using (le_of_lt hKn : K ≤ n)))
      hbenchmarkInvariant R hRegret uPlus huPlus
  let moving := adjacentMoving n K hKpos hKn
  calc
    (K : ℝ) * Delta *
        (((n - K : ℕ) : ℝ) / (n : ℝ) -
          (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) ≤
      (K : ℝ) * Delta * (1 - q uPlus moving) := by
        simpa [moving, uPlus] using hbranch
    _ = topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) uPlus -
        scoreValue (q uPlus) uPlus := by
      simpa [moving, uPlus] using hregretEq.symm
    _ ≤ R := hqRegret

/-- The reflected cube rule supplies the opposite adjacent-cardinality branch
without evaluating the original rule outside `[0,1]ⁿ`. -/
theorem scoreRule_cube_complement_adjacent_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (hLipschitz : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u →
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R)
    (Delta : ℝ) (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1) :
    ((n - K : ℕ) : ℝ) * Delta *
        ((K : ℝ) / (n : ℝ) -
          ((K : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) ≤ R := by
  classical
  let Kc := n - K
  let q := excludeCubeRule p
  have hKcpos : 1 ≤ Kc := by omega
  have hKclt : Kc < n := by omega
  have hKle : K ≤ n := le_of_lt hKn
  have hKcard : K ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hKle
  have hKccard : Kc ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using (le_of_lt hKclt : Kc ≤ n)
  have hqMass : ∀ y, InUnitCube y → ∑ i, q y i = (Kc : ℝ) := by
    intro y hy
    have hm := hMass (oneMinusVector y) (inUnitCube_oneMinusVector hy)
    unfold q excludeCubeRule
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, hm]
    norm_num [Kc, Nat.cast_sub hKle]
  have hqLip : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (q u) (q v) ≤ Lambda * finiteL1 u v := by
    intro u hu v hv
    unfold q
    rw [finiteL1_excludeCubeRule]
    calc
      finiteL1 (p (oneMinusVector u)) (p (oneMinusVector v)) ≤
          Lambda * finiteL1 (oneMinusVector u) (oneMinusVector v) :=
        hLipschitz _ (inUnitCube_oneMinusVector hu) _
          (inUnitCube_oneMinusVector hv)
      _ = Lambda * finiteL1 u v := by rw [finiteL1_oneMinusVector]
  have hqRegret : ∀ y, InUnitCube y →
      topKScore Kc hKccard y -
        scoreValue (q y) y ≤ R := by
    intro y hy
    have hyReflected := inUnitCube_oneMinusVector hy
    have hm := hMass (oneMinusVector y) hyReflected
    have heq := excludeCubeRule_topK_regret_eq_of_profile_mass
      K hKcard p y hm
    have horiginal := hRegret (oneMinusVector y) hyReflected
    simpa [q, Kc, Fintype.card_fin] using heq.trans_le horiginal
  have hbranch := scoreRule_cube_adjacent_lower
    n Kc hKcpos hKclt q hqMass Lambda hLambda hqLip R hqRegret
    Delta hDelta0 hDelta1
  simpa [Kc, Nat.sub_sub_self hKle] using hbranch

theorem flatK_adjacent_optimizer_le_one
    (Kc Lambda : ℝ) (hKc : 0 ≤ Kc) (hLambda : 0 < Lambda)
    (hThreshold : Kc / (Kc + 1) ≤ Lambda) :
    Kc / (Lambda * (Kc + 1)) ≤ 1 := by
  have hden : 0 < Kc + 1 := by linarith
  have hmul : Kc ≤ Lambda * (Kc + 1) :=
    (div_le_iff₀ hden).mp hThreshold
  exact (div_le_one (mul_pos hLambda hden)).mpr hmul

/-- High-smoothness branch of the bounded cube.  The unconstrained maximizing
adjacent gap lies inside the cube. -/
theorem scoreRule_cube_allCapacity_high_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 < Lambda)
    (hLipschitz : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u →
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R)
    (hThreshold :
      ((max K (n - K) : ℕ) : ℝ) /
          (((max K (n - K) : ℕ) : ℝ) + 1) ≤ Lambda) :
    ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
        (2 * Lambda * (n : ℝ) * (((max K (n - K) : ℕ) : ℝ) + 1)) ≤ R := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hKcPosNat : 1 ≤ n - K := by omega
  have hKc0 : 0 ≤ ((n - K : ℕ) : ℝ) := by positivity
  by_cases horder : K ≤ n - K
  · let Delta := ((n - K : ℕ) : ℝ) /
      (Lambda * (((n - K : ℕ) : ℝ) + 1))
    have hDelta0 : 0 ≤ Delta := by
      dsimp [Delta]
      positivity
    have hthreshold' : ((n - K : ℕ) : ℝ) /
        (((n - K : ℕ) : ℝ) + 1) ≤ Lambda := by
      simpa [max_eq_right horder] using hThreshold
    have hDelta1 : Delta ≤ 1 := by
      exact flatK_adjacent_optimizer_le_one _ _ hKc0 hLambda hthreshold'
    have hbranch := scoreRule_cube_adjacent_lower
      n K hKpos hKn p hMass Lambda hLambda.le hLipschitz R hRegret
      Delta hDelta0 hDelta1
    have hopt := flatK_adjacent_regret_optimizer
      (n : ℝ) (K : ℝ) ((n - K : ℕ) : ℝ) Lambda hn0 hLambda.ne'
      (by positivity)
    dsimp only at hopt
    calc
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
          (2 * Lambda * (n : ℝ) * (((max K (n - K) : ℕ) : ℝ) + 1)) =
        (K : ℝ) * Delta *
          (((n - K : ℕ) : ℝ) / (n : ℝ) -
            (((n - K : ℕ) : ℝ) + 1) * Lambda * Delta /
              (2 * (n : ℝ))) := by
        rw [min_eq_left horder, max_eq_right horder]
        exact hopt.symm
      _ ≤ R := hbranch
  · have hreverse : n - K ≤ K := by omega
    let Delta := (K : ℝ) / (Lambda * ((K : ℝ) + 1))
    have hDelta0 : 0 ≤ Delta := by
      dsimp [Delta]
      positivity
    have hthreshold' : (K : ℝ) / ((K : ℝ) + 1) ≤ Lambda := by
      simpa [max_eq_left hreverse] using hThreshold
    have hK0 : 0 ≤ (K : ℝ) := by positivity
    have hDelta1 : Delta ≤ 1 := by
      exact flatK_adjacent_optimizer_le_one _ _ hK0 hLambda hthreshold'
    have hbranch := scoreRule_cube_complement_adjacent_lower
      n K hKpos hKn p hMass Lambda hLambda.le hLipschitz R hRegret
      Delta hDelta0 hDelta1
    have hopt := flatK_adjacent_regret_optimizer
      (n : ℝ) ((n - K : ℕ) : ℝ) (K : ℝ) Lambda hn0 hLambda.ne'
      (by positivity)
    dsimp only at hopt
    calc
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
          (2 * Lambda * (n : ℝ) * (((max K (n - K) : ℕ) : ℝ) + 1)) =
        ((n - K : ℕ) : ℝ) * Delta *
          ((K : ℝ) / (n : ℝ) -
            ((K : ℝ) + 1) * Lambda * Delta / (2 * (n : ℝ))) := by
        rw [min_eq_right hreverse, max_eq_left hreverse]
        exact hopt.symm
      _ ≤ R := hbranch

/-- Low-smoothness branch of the bounded cube, obtained by placing the
adjacent witness at the full score diameter `Delta = 1`. -/
theorem scoreRule_cube_allCapacity_low_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (hLipschitz : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u →
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R) :
    ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
        (((max K (n - K) : ℕ) : ℝ) -
          (((max K (n - K) : ℕ) : ℝ) + 1) * Lambda / 2) ≤ R := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  by_cases horder : K ≤ n - K
  · have hbranch := scoreRule_cube_adjacent_lower
      n K hKpos hKn p hMass Lambda hLambda hLipschitz R hRegret
      1 (by norm_num) (by norm_num)
    calc
      ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
          (((max K (n - K) : ℕ) : ℝ) -
            (((max K (n - K) : ℕ) : ℝ) + 1) * Lambda / 2) =
        (K : ℝ) * 1 *
          (((n - K : ℕ) : ℝ) / (n : ℝ) -
            (((n - K : ℕ) : ℝ) + 1) * Lambda * 1 / (2 * (n : ℝ))) := by
        rw [min_eq_left horder, max_eq_right horder]
        field_simp [hn0]
      _ ≤ R := hbranch
  · have hreverse : n - K ≤ K := by omega
    have hbranch := scoreRule_cube_complement_adjacent_lower
      n K hKpos hKn p hMass Lambda hLambda hLipschitz R hRegret
      1 (by norm_num) (by norm_num)
    calc
      ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
          (((max K (n - K) : ℕ) : ℝ) -
            (((max K (n - K) : ℕ) : ℝ) + 1) * Lambda / 2) =
        ((n - K : ℕ) : ℝ) * 1 *
          ((K : ℝ) / (n : ℝ) -
            ((K : ℝ) + 1) * Lambda * 1 / (2 * (n : ℝ))) := by
        rw [min_eq_right hreverse, max_eq_left hreverse]
        field_simp [hn0]
      _ ≤ R := hbranch

/-- Complete two-regime lower certificate for the bounded score cube. -/
theorem scoreRule_cube_allCapacity_lower
    (n K : ℕ) (hKpos : 1 ≤ K) (hKn : K < n)
    (p : (Fin n → ℝ) → Fin n → ℝ)
    (hMass : ∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ))
    (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
    (hLipschitz : ∀ u, InUnitCube u → ∀ v, InUnitCube v →
      finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v)
    (R : ℝ)
    (hRegret : ∀ u, InUnitCube u →
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue (p u) u ≤ R) :
    ((((max K (n - K) : ℕ) : ℝ) /
          (((max K (n - K) : ℕ) : ℝ) + 1) ≤ Lambda) →
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
          (2 * Lambda * (n : ℝ) *
            (((max K (n - K) : ℕ) : ℝ) + 1)) ≤ R) ∧
    ((Lambda < ((max K (n - K) : ℕ) : ℝ) /
          (((max K (n - K) : ℕ) : ℝ) + 1)) →
      ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
          (((max K (n - K) : ℕ) : ℝ) -
            (((max K (n - K) : ℕ) : ℝ) + 1) * Lambda / 2) ≤ R) := by
  have hKplusPosNat : 0 < max K (n - K) := by omega
  have hKplusPos : 0 < ((max K (n - K) : ℕ) : ℝ) := by
    exact_mod_cast hKplusPosNat
  have hThresholdPos : 0 < ((max K (n - K) : ℕ) : ℝ) /
      (((max K (n - K) : ℕ) : ℝ) + 1) := by positivity
  constructor
  · intro hThreshold
    have hLambdaPos : 0 < Lambda := hThresholdPos.trans_le hThreshold
    exact scoreRule_cube_allCapacity_high_lower
      n K hKpos hKn p hMass Lambda hLambdaPos hLipschitz R hRegret hThreshold
  · intro _hLow
    exact scoreRule_cube_allCapacity_low_lower
      n K hKpos hKn p hMass Lambda hLambda hLipschitz R hRegret

/-! ## Exact-mass `L¹` bridge -/

/-- For a fixed-mass vector, if one coordinate rises and all others fall,
total `L¹` movement is exactly twice the mover's increase. -/
theorem fixedMass_l1_update_eq_twice
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x x' : ι → ℝ) (i : ι)
    (hmass : ∑ j, x' j = ∑ j, x j)
    (hi : x i ≤ x' i)
    (hother : ∀ j, j ≠ i → x' j ≤ x j) :
    ∑ j, |x' j - x j| = 2 * (x' i - x i) := by
  classical
  have hsplit' : ∑ j, x' j = x' i + ∑ j ∈ Finset.univ.erase i, x' j := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset ι) x' (Finset.mem_univ i)]
  have hsplit : ∑ j, x j = x i + ∑ j ∈ Finset.univ.erase i, x j := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset ι) x (Finset.mem_univ i)]
  have hbalance : ∑ j ∈ Finset.univ.erase i, (x j - x' j) = x' i - x i := by
    rw [Finset.sum_sub_distrib]
    linarith
  rw [← Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun j => |x' j - x j|) (Finset.mem_univ i)]
  rw [abs_of_nonneg (sub_nonneg.mpr hi)]
  have habs : ∀ j ∈ (Finset.univ : Finset ι).erase i,
      |x' j - x j| = x j - x' j := by
    intro j hj
    rw [abs_of_nonpos
      (sub_nonpos.mpr (hother j (Finset.ne_of_mem_erase hj)))]
    ring
  rw [Finset.sum_congr rfl habs, hbalance]
  ring

/-- Ordered one-coordinate version of the priority normalization. -/
theorem flatK_priority_l1_coordinate_le_of_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (slots : ℕ) (weight : ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hMass : FlatKNoWaste slots weight x)
    (hOwn : OwnMonotone x) (hCross : CrossMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) (hzz : z ≤ z') :
    ∑ j, |x (updateBid b i z') j - x (updateBid b i z) j| ≤
      2 * (sensitivity : ℝ) * |(z' : ℝ) - (z : ℝ)| := by
  classical
  have hupdate : updateBid (updateBid b i z) i z' = updateBid b i z' := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, Function.update, hji]
  have hself : updateBid (updateBid b i z) i z = updateBid b i z := by
    funext j
    by_cases hji : j = i <;> simp [updateBid, Function.update, hji]
  have hi : x (updateBid b i z) i ≤ x (updateBid b i z') i := by
    have h := hOwn (updateBid b i z) i hzz
    change x (updateBid (updateBid b i z) i z) i ≤
      x (updateBid (updateBid b i z) i z') i at h
    rwa [hself, hupdate] at h
  have hother : ∀ j, j ≠ i →
      x (updateBid b i z') j ≤ x (updateBid b i z) j := by
    intro j hji
    have h := hCross (updateBid b i z) j i hji hzz
    change x (updateBid (updateBid b i z) i z') j ≤
      x (updateBid (updateBid b i z) i z) j at h
    rwa [hself, hupdate] at h
  have hmass : ∑ j, x (updateBid b i z') j =
      ∑ j, x (updateBid b i z) j := by
    rw [hMass (updateBid b i z'), hMass (updateBid b i z)]
  rw [fixedMass_l1_update_eq_twice
    (fun j => x (updateBid b i z) j)
    (fun j => x (updateBid b i z') j) i hmass hi hother]
  have hlip := (hLip b i).dist_le_mul z' z
  rw [Subtype.dist_eq, Real.dist_eq] at hlip
  have hownBound : x (updateBid b i z') i - x (updateBid b i z) i ≤
      (sensitivity : ℝ) * |(z' : ℝ) - (z : ℝ)| := by
    rw [← abs_of_nonneg (sub_nonneg.mpr hi)]
    exact hlip
  nlinarith

/-- One-coordinate version of the priority normalization: exact mass and
cross-monotonicity turn the own-coordinate certificate into twice that bound
in full-vector `L¹`. -/
theorem flatK_priority_l1_coordinate_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (slots : ℕ) (weight : ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hMass : FlatKNoWaste slots weight x)
    (hOwn : OwnMonotone x) (hCross : CrossMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (b : EligibleProfile ι reserve) (i : ι)
    (z z' : EligibleBid reserve) :
    ∑ j, |x (updateBid b i z') j - x (updateBid b i z) j| ≤
      2 * (sensitivity : ℝ) * |(z' : ℝ) - (z : ℝ)| := by
  rcases le_total z z' with hzz | hzz
  · exact flatK_priority_l1_coordinate_le_of_le slots weight sensitivity x
      hMass hOwn hCross hLip b i z z' hzz
  · have hrev := flatK_priority_l1_coordinate_le_of_le slots weight sensitivity x
      hMass hOwn hCross hLip b i z' z hzz
    calc
      ∑ j, |x (updateBid b i z') j - x (updateBid b i z) j| =
          ∑ j, |x (updateBid b i z) j - x (updateBid b i z') j| := by
        apply Finset.sum_congr rfl
        intro j hj
        exact abs_sub_comm _ _
      _ ≤ 2 * (sensitivity : ℝ) * |(z : ℝ) - (z' : ℝ)| := hrev
      _ = 2 * (sensitivity : ℝ) * |(z' : ℝ) - (z : ℝ)| := by
        rw [abs_sub_comm]

/-- Telescoping the preceding coordinate estimate gives the full-vector
modulus `2S` on the eligible region. -/
theorem flatK_priority_fullVector_l1_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (slots : ℕ) (weight : ℝ) (sensitivity : NNReal)
    (x : InterimRule ι reserve)
    (hMass : FlatKNoWaste slots weight x)
    (hOwn : OwnMonotone x) (hCross : CrossMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (b b' : EligibleProfile ι reserve) :
    ∑ j, |x b' j - x b j| ≤
      2 * (sensitivity : ℝ) * ∑ i, |(b' i : ℝ) - (b i : ℝ)| := by
  let p : EligibleProfile ι reserve → ι → ℝ := x
  have hcoord : ∀ u i z,
      finiteL1 (p (Function.update u i z)) (p u) ≤
        (2 * (sensitivity : ℝ)) * |(z : ℝ) - (u i : ℝ)| := by
    intro u i z
    simpa [finiteL1, p, updateBid] using
      flatK_priority_l1_coordinate_le slots weight sensitivity x
        hMass hOwn hCross hLip u i (u i) z
  simpa [finiteL1, p] using
    finiteL1_le_of_coordinate_bounds p
      (fun z u : EligibleBid reserve => |(z : ℝ) - (u : ℝ)|)
      (2 * (sensitivity : ℝ)) hcoord b b'

/-- Probability normalization of the priority bridge, with modulus `2S/w₁`.
-/
theorem flatK_priority_probability_fullVector_l1_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {reserve : ℝ}
    (slots : ℕ) (weight : ℝ) (sensitivity : NNReal)
    (hweight : 0 < weight)
    (x : InterimRule ι reserve)
    (hMass : FlatKNoWaste slots weight x)
    (hOwn : OwnMonotone x) (hCross : CrossMonotone x)
    (hLip : OwnLipschitz sensitivity x)
    (b b' : EligibleProfile ι reserve) :
    ∑ j, |x b' j / weight - x b j / weight| ≤
      (2 * (sensitivity : ℝ) / weight) *
        ∑ i, |(b' i : ℝ) - (b i : ℝ)| := by
  have h := flatK_priority_fullVector_l1_le slots weight sensitivity x
    hMass hOwn hCross hLip b b'
  have hterm : ∀ j : ι,
      |x b' j / weight - x b j / weight| = |x b' j - x b j| / weight := by
    intro j
    rw [div_sub_div_same, abs_div, abs_of_pos hweight]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div]
  rw [div_le_iff₀ hweight]
  calc
    ∑ i, |x b' i - x b i| ≤
        2 * (sensitivity : ℝ) * ∑ i, |(b' i : ℝ) - (b i : ℝ)| := h
    _ = (2 * (sensitivity : ℝ) / weight *
          ∑ i, |(b' i : ℝ) - (b i : ℝ)|) * weight := by
      field_simp

/-! ## Exact finite-population modulus of water filling -/

/-- Thresholds producing the same total clipped mass induce the same
allocation vector, regardless of the value of that common target mass. -/
theorem waterFillAt_eq_of_equal_mass
    {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (b : ι → ℝ) {s t : ℝ}
    (hmass : waterFillMass weight sensitivity b s =
      waterFillMass weight sensitivity b t) (i : ι) :
    waterFillAt weight sensitivity b s i =
      waterFillAt weight sensitivity b t i := by
  rcases le_total s t with hst | hts
  · have hle : ∀ j ∈ Finset.univ,
        waterFillAt weight sensitivity b t j ≤
          waterFillAt weight sensitivity b s j := by
      intro j hj
      exact waterFillAt_antitone_threshold weight sensitivity b hst j
    exact ((Finset.sum_eq_sum_iff_of_le hle).mp hmass.symm i
      (Finset.mem_univ i)).symm
  · have hle : ∀ j ∈ Finset.univ,
        waterFillAt weight sensitivity b s j ≤
          waterFillAt weight sensitivity b t j := by
      intro j hj
      exact waterFillAt_antitone_threshold weight sensitivity b hts j
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hmass i (Finset.mem_univ i)

/-- Projection onto an interval cannot increase a one-sided increment. -/
theorem clampWeight_increment_le
    (weight : NNReal) {a c : ℝ} (hac : a ≤ c) :
    clampWeight weight c - clampWeight weight a ≤ c - a := by
  have hlip : |clampWeight weight a - clampWeight weight c| ≤ |a - c| :=
    Set.abs_projIcc_sub_projIcc weight.coe_nonneg
  have hclamp : clampWeight weight a ≤ clampWeight weight c :=
    clampWeight_monotone weight hac
  rw [abs_of_nonpos (sub_nonpos.mpr hclamp),
    abs_of_nonpos (sub_nonpos.mpr hac)] at hlip
  linarith

/-- If one score rises while the old and new water-filling thresholds assign
the same total mass, the mover's allocation increase is at most
`a·delta·(1-1/n)`.  This statement is independent of the target mass and hence
applies to every flat capacity. -/
theorem waterFillAt_own_increment_le_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal)
    (b : ι → ℝ) (i : ι) {z s t : ℝ}
    (hb : b i ≤ z)
    (hmass : waterFillMass weight sensitivity
        (Function.update b i z) t = waterFillMass weight sensitivity b s) :
    waterFillAt weight sensitivity (Function.update b i z) t i -
        waterFillAt weight sensitivity b s i ≤
      (sensitivity : ℝ) * (z - b i) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  classical
  have hnNat : 0 < Fintype.card ι := Fintype.card_pos
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnNat
  have hnOne : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hnNat
  have hfactor : 0 ≤ ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) :=
    div_nonneg (by linarith) hn.le
  rcases le_total s t with hst | hts
  · have hother : ∀ j, j ≠ i →
        waterFillAt weight sensitivity (Function.update b i z) t j ≤
          waterFillAt weight sensitivity b s j := by
      intro j hji
      exact waterFillAt_update_le_of_threshold_le weight sensitivity b i hst hji
    have hown : waterFillAt weight sensitivity b s i ≤
        waterFillAt weight sensitivity (Function.update b i z) t i := by
      by_contra hnot
      have hstrict : waterFillAt weight sensitivity (Function.update b i z) t i <
          waterFillAt weight sensitivity b s i := lt_of_not_ge hnot
      have hle : ∀ j ∈ (Finset.univ : Finset ι),
          waterFillAt weight sensitivity (Function.update b i z) t j ≤
            waterFillAt weight sensitivity b s j := by
        intro j hj
        by_cases hji : j = i
        · simpa [hji] using hstrict.le
        · exact hother j hji
      have hsumlt := Finset.sum_lt_sum hle
        ⟨i, Finset.mem_univ i, hstrict⟩
      unfold waterFillMass at hmass
      rw [hmass] at hsumlt
      exact (lt_irrefl _) hsumlt
    by_cases hdelta : t - s ≤ z - b i
    · have hrawOwn : (sensitivity : ℝ) * (b i - s) ≤
          (sensitivity : ℝ) * (z - t) := by
        apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
        linarith
      have hownCap :
          waterFillAt weight sensitivity (Function.update b i z) t i -
              waterFillAt weight sensitivity b s i ≤
            (sensitivity : ℝ) * ((z - b i) - (t - s)) := by
        simp only [waterFillAt, Function.update_self]
        calc
          clampWeight weight ((sensitivity : ℝ) * (z - t)) -
              clampWeight weight ((sensitivity : ℝ) * (b i - s)) ≤
              (sensitivity : ℝ) * (z - t) -
                (sensitivity : ℝ) * (b i - s) :=
            clampWeight_increment_le weight hrawOwn
          _ = (sensitivity : ℝ) * ((z - b i) - (t - s)) := by ring
      have hbalance :
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
              (waterFillAt weight sensitivity b s j -
                waterFillAt weight sensitivity (Function.update b i z) t j) =
            waterFillAt weight sensitivity (Function.update b i z) t i -
              waterFillAt weight sensitivity b s i := by
        have hsplitNew :
            ∑ j, waterFillAt weight sensitivity (Function.update b i z) t j =
              waterFillAt weight sensitivity (Function.update b i z) t i +
                ∑ j ∈ (Finset.univ : Finset ι).erase i,
                  waterFillAt weight sensitivity (Function.update b i z) t j := by
          rw [← Finset.add_sum_erase (Finset.univ : Finset ι)
            (waterFillAt weight sensitivity (Function.update b i z) t)
            (Finset.mem_univ i)]
        have hsplitOld :
            ∑ j, waterFillAt weight sensitivity b s j =
              waterFillAt weight sensitivity b s i +
                ∑ j ∈ (Finset.univ : Finset ι).erase i,
                  waterFillAt weight sensitivity b s j := by
          rw [← Finset.add_sum_erase (Finset.univ : Finset ι)
            (waterFillAt weight sensitivity b s) (Finset.mem_univ i)]
        unfold waterFillMass at hmass
        rw [Finset.sum_sub_distrib]
        linarith
      have hloss : ∀ j ∈ (Finset.univ : Finset ι).erase i,
          waterFillAt weight sensitivity b s j -
              waterFillAt weight sensitivity (Function.update b i z) t j ≤
            (sensitivity : ℝ) * (t - s) := by
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have hraw : (sensitivity : ℝ) * (b j - t) ≤
            (sensitivity : ℝ) * (b j - s) := by
          apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
          linarith
        change clampWeight weight ((sensitivity : ℝ) * (b j - s)) -
            clampWeight weight
              ((sensitivity : ℝ) * (Function.update b i z j - t)) ≤ _
        simp only [Function.update, hji]
        calc
          clampWeight weight ((sensitivity : ℝ) * (b j - s)) -
              clampWeight weight ((sensitivity : ℝ) * (b j - t)) ≤
              (sensitivity : ℝ) * (b j - s) -
                (sensitivity : ℝ) * (b j - t) :=
            clampWeight_increment_le weight hraw
          _ = (sensitivity : ℝ) * (t - s) := by ring
      have hcardErase :
          (((Finset.univ : Finset ι).erase i).card : ℝ) =
            (Fintype.card ι : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        rw [Nat.cast_sub (Nat.succ_le_iff.mpr hnNat)]
        norm_num
      have hothersCap :
          waterFillAt weight sensitivity (Function.update b i z) t i -
              waterFillAt weight sensitivity b s i ≤
            ((Fintype.card ι : ℝ) - 1) *
              ((sensitivity : ℝ) * (t - s)) := by
        rw [← hbalance]
        calc
          ∑ j ∈ (Finset.univ : Finset ι).erase i,
              (waterFillAt weight sensitivity b s j -
                waterFillAt weight sensitivity (Function.update b i z) t j) ≤
              ∑ _j ∈ (Finset.univ : Finset ι).erase i,
                (sensitivity : ℝ) * (t - s) :=
            Finset.sum_le_sum hloss
          _ = ((Fintype.card ι : ℝ) - 1) *
              ((sensitivity : ℝ) * (t - s)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardErase]
      have hscaled := mul_le_mul_of_nonneg_left hownCap
        (by linarith : 0 ≤ (Fintype.card ι : ℝ) - 1)
      have hgoal :
          waterFillAt weight sensitivity (Function.update b i z) t i -
              waterFillAt weight sensitivity b s i ≤
            (sensitivity : ℝ) * (z - b i) *
              ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by
        rw [le_div_iff₀ hn]
        nlinarith
      calc
        waterFillAt weight sensitivity (Function.update b i z) t i -
            waterFillAt weight sensitivity b s i ≤
            (sensitivity : ℝ) * (z - b i) *
              ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := hgoal
        _ = (sensitivity : ℝ) * (z - b i) *
            (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by ring
    · have hdelta' : z - b i < t - s := lt_of_not_ge hdelta
      have hle : ∀ j ∈ (Finset.univ : Finset ι),
          waterFillAt weight sensitivity (Function.update b i z) t j ≤
            waterFillAt weight sensitivity b s j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          apply clampWeight_monotone
          apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
          simp only [Function.update_self]
          linarith
        · exact hother j hji
      have heq : ∀ j,
          waterFillAt weight sensitivity (Function.update b i z) t j =
            waterFillAt weight sensitivity b s j := by
        unfold waterFillMass at hmass
        intro j
        exact (Finset.sum_eq_sum_iff_of_le hle).mp hmass j (Finset.mem_univ j)
      rw [heq i, sub_self]
      exact mul_nonneg (mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hb)) hfactor
  · have hle : ∀ j ∈ (Finset.univ : Finset ι),
        waterFillAt weight sensitivity b s j ≤
          waterFillAt weight sensitivity (Function.update b i z) t j := by
      intro j hj
      exact waterFillAt_le_update_of_threshold_le weight sensitivity b i hb hts j
    have heq : ∀ j, waterFillAt weight sensitivity b s j =
        waterFillAt weight sensitivity (Function.update b i z) t j := by
      unfold waterFillMass at hmass
      intro j
      exact (Finset.sum_eq_sum_iff_of_le hle).mp hmass.symm j (Finset.mem_univ j)
    rw [← heq i, sub_self]
    exact mul_nonneg (mul_nonneg sensitivity.coe_nonneg (sub_nonneg.mpr hb)) hfactor

/-- Equal total mass also fixes the sign pattern after a one-coordinate score
increase: the mover gains and every other coordinate loses. -/
theorem waterFillAt_update_signs_of_equal_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight sensitivity : NNReal)
    (b : ι → ℝ) (i : ι) {z s t : ℝ}
    (hb : b i ≤ z)
    (hmass : waterFillMass weight sensitivity
        (Function.update b i z) t = waterFillMass weight sensitivity b s) :
    waterFillAt weight sensitivity b s i ≤
        waterFillAt weight sensitivity (Function.update b i z) t i ∧
      ∀ j, j ≠ i →
        waterFillAt weight sensitivity (Function.update b i z) t j ≤
          waterFillAt weight sensitivity b s j := by
  classical
  rcases le_total s t with hst | hts
  · have hother : ∀ j, j ≠ i →
        waterFillAt weight sensitivity (Function.update b i z) t j ≤
          waterFillAt weight sensitivity b s j := by
      intro j hji
      exact waterFillAt_update_le_of_threshold_le weight sensitivity b i hst hji
    refine ⟨?_, hother⟩
    by_contra hnot
    have hstrict : waterFillAt weight sensitivity (Function.update b i z) t i <
        waterFillAt weight sensitivity b s i := lt_of_not_ge hnot
    have hle : ∀ j ∈ (Finset.univ : Finset ι),
        waterFillAt weight sensitivity (Function.update b i z) t j ≤
          waterFillAt weight sensitivity b s j := by
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hstrict.le
      · exact hother j hji
    have hsumlt := Finset.sum_lt_sum hle ⟨i, Finset.mem_univ i, hstrict⟩
    unfold waterFillMass at hmass
    rw [hmass] at hsumlt
    exact (lt_irrefl _) hsumlt
  · have hle : ∀ j ∈ (Finset.univ : Finset ι),
        waterFillAt weight sensitivity b s j ≤
          waterFillAt weight sensitivity (Function.update b i z) t j := by
      intro j hj
      exact waterFillAt_le_update_of_threshold_le weight sensitivity b i hb hts j
    have heq : ∀ j, waterFillAt weight sensitivity b s j =
        waterFillAt weight sensitivity (Function.update b i z) t j := by
      unfold waterFillMass at hmass
      intro j
      exact (Finset.sum_eq_sum_iff_of_le hle).mp hmass.symm j (Finset.mem_univ j)
    exact ⟨(heq i).le, fun j hji => (heq j).ge⟩

/-- Full-vector movement under one score change is at most twice the sharp
own-coordinate bound.  This is the projection side of the paper's modulus
normalization. -/
theorem waterFillAt_l1_update_le_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal)
    (b : ι → ℝ) (i : ι) {z s t : ℝ}
    (hb : b i ≤ z)
    (hmass : waterFillMass weight sensitivity
        (Function.update b i z) t = waterFillMass weight sensitivity b s) :
    ∑ j, |waterFillAt weight sensitivity (Function.update b i z) t j -
        waterFillAt weight sensitivity b s j| ≤
      2 * (sensitivity : ℝ) * (z - b i) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  have hsigns := waterFillAt_update_signs_of_equal_mass
    weight sensitivity b i hb hmass
  have hsum :
      ∑ j, waterFillAt weight sensitivity (Function.update b i z) t j =
        ∑ j, waterFillAt weight sensitivity b s j := by
    exact hmass
  rw [fixedMass_l1_update_eq_twice
    (waterFillAt weight sensitivity b s)
    (waterFillAt weight sensitivity (Function.update b i z) t) i
    hsum hsigns.1 hsigns.2]
  have hown := waterFillAt_own_increment_le_exact
    weight sensitivity b i hb hmass
  nlinarith

/-- A choice of a mass-solving threshold for every score profile defines the
flat-capacity projection rule. -/
noncomputable def waterFillingSelection
    {ι : Type*} [Fintype ι]
    (weight sensitivity : NNReal) (threshold : (ι → ℝ) → ℝ) :
    (ι → ℝ) → ι → ℝ :=
  fun u i => waterFillAt weight sensitivity u (threshold u) i

/-- One-coordinate full-vector modulus for any threshold selection that keeps
the assigned mass fixed. -/
theorem waterFillingSelection_l1_coordinate_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (threshold : (ι → ℝ) → ℝ) (mass : ℝ)
    (hMass : ∀ u, waterFillMass weight sensitivity u (threshold u) = mass)
    (u : ι → ℝ) (i : ι) (z : ℝ) :
    finiteL1
        (waterFillingSelection weight sensitivity threshold (Function.update u i z))
        (waterFillingSelection weight sensitivity threshold u) ≤
      2 * (sensitivity : ℝ) * |z - u i| *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  classical
  rcases le_total (u i) z with huz | huz
  · unfold finiteL1 waterFillingSelection
    have h := waterFillAt_l1_update_le_exact weight sensitivity u i huz
      ((hMass (Function.update u i z)).trans (hMass u).symm)
    rw [abs_of_nonneg (sub_nonneg.mpr huz)]
    nlinarith
  · have hrestore : Function.update (Function.update u i z) i (u i) = u := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have h := waterFillAt_l1_update_le_exact weight sensitivity
      (Function.update u i z) i (z := u i) (by simpa using huz)
      (by simpa [hrestore] using (hMass u).trans (hMass (Function.update u i z)).symm)
    unfold finiteL1 waterFillingSelection at ⊢
    simp only [Function.update_self] at h
    rw [hrestore] at h
    have hsymm :
        (∑ j, |waterFillAt weight sensitivity (Function.update u i z)
            (threshold (Function.update u i z)) j -
          waterFillAt weight sensitivity u (threshold u) j|) =
        ∑ j, |waterFillAt weight sensitivity u (threshold u) j -
          waterFillAt weight sensitivity (Function.update u i z)
            (threshold (Function.update u i z)) j| := by
      apply Finset.sum_congr rfl
      intro j hj
      exact abs_sub_comm _ _
    rw [hsymm, abs_of_nonpos (sub_nonpos.mpr huz)]
    nlinarith

/-- Telescoping gives the projection's full-vector modulus
`2a(1-1/n)`. -/
theorem waterFillingSelection_fullVector_l1_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (threshold : (ι → ℝ) → ℝ) (mass : ℝ)
    (hMass : ∀ u, waterFillMass weight sensitivity u (threshold u) = mass)
    (u v : ι → ℝ) :
    finiteL1 (waterFillingSelection weight sensitivity threshold v)
        (waterFillingSelection weight sensitivity threshold u) ≤
      (2 * (sensitivity : ℝ) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) *
          finiteL1 v u := by
  let p := waterFillingSelection weight sensitivity threshold
  have hcoord : ∀ q i z,
      finiteL1 (p (Function.update q i z)) (p q) ≤
        (2 * (sensitivity : ℝ) *
          (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) * |z - q i| := by
    intro q i z
    have h := waterFillingSelection_l1_coordinate_le
      weight sensitivity threshold mass hMass q i z
    nlinarith
  simpa [p, finiteL1] using
    finiteL1_le_of_coordinate_bounds p (fun z q : ℝ => |z - q|)
      (2 * (sensitivity : ℝ) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ))) hcoord u v

/-- Canonical one-slot water filling obeys the sharp finite-population
one-sided modulus. -/
theorem waterFillingVector_own_increment_le_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) {z : ℝ} (hb : b i ≤ z) :
    waterFillingVector weight sensitivity hsens (Function.update b i z) i -
        waterFillingVector weight sensitivity hsens b i ≤
      (sensitivity : ℝ) * (z - b i) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  let s := waterFillingThreshold weight sensitivity hsens b
  let t := waterFillingThreshold weight sensitivity hsens (Function.update b i z)
  have hs := waterFillingThreshold_spec weight sensitivity hsens b
  have ht := waterFillingThreshold_spec weight sensitivity hsens
    (Function.update b i z)
  rw [waterFillingVector_eq_at_threshold weight sensitivity hsens b hs i,
    waterFillingVector_eq_at_threshold weight sensitivity hsens
      (Function.update b i z) ht i]
  exact waterFillAt_own_increment_le_exact weight sensitivity b i hb
    (by exact ht.trans hs.symm)

/-- Symmetric two-sided form of the sharp own-coordinate modulus. -/
theorem waterFillingVector_own_lipschitz_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (b : ι → ℝ) (i : ι) (z z' : ℝ) :
    |waterFillingVector weight sensitivity hsens (Function.update b i z') i -
        waterFillingVector weight sensitivity hsens (Function.update b i z) i| ≤
      (sensitivity : ℝ) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) * |z' - z| := by
  rcases le_total z z' with hzz | hzz
  · have hupdate : Function.update (Function.update b i z) i z' =
        Function.update b i z' := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have hstep := waterFillingVector_own_increment_le_exact
      weight sensitivity hsens (Function.update b i z) i (z := z')
      (by simpa using hzz)
    have hmono := waterFillingVector_own_monotone
      weight sensitivity hsens (Function.update b i z) i (z := z')
      (by simpa using hzz)
    rw [hupdate] at hstep hmono
    simp [Function.update] at hstep
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hzz)]
    nlinarith
  · have hupdate : Function.update (Function.update b i z') i z =
        Function.update b i z := by
      funext j
      by_cases hji : j = i <;> simp [Function.update, hji]
    have hstep := waterFillingVector_own_increment_le_exact
      weight sensitivity hsens (Function.update b i z') i (z := z)
      (by simpa using hzz)
    have hmono := waterFillingVector_own_monotone
      weight sensitivity hsens (Function.update b i z') i (z := z)
      (by simpa using hzz)
    rw [hupdate] at hstep hmono
    simp [Function.update] at hstep
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hzz)]
    nlinarith

/-- Sharp own-coordinate upper modulus for an arbitrary threshold selector
that maintains any fixed total mass. -/
theorem waterFillingSelection_own_lipschitz_exact
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal) (threshold : (ι → ℝ) → ℝ) (mass : ℝ)
    (hMass : ∀ u, waterFillMass weight sensitivity u (threshold u) = mass)
    (u : ι → ℝ) (i : ι) (z z' : ℝ) :
    |waterFillingSelection weight sensitivity threshold (Function.update u i z') i -
        waterFillingSelection weight sensitivity threshold (Function.update u i z) i| ≤
      (sensitivity : ℝ) *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) * |z' - z| := by
  rcases le_total z z' with hzz | hzz
  · let b := Function.update u i z
    have hupdate : Function.update b i z' = Function.update u i z' := by
      funext j
      by_cases hji : j = i <;> simp [b, Function.update, hji]
    have hmassEq : waterFillMass weight sensitivity
        (Function.update b i z') (threshold (Function.update b i z')) =
      waterFillMass weight sensitivity b (threshold b) := by
      rw [hMass, hMass]
    have hstep := waterFillAt_own_increment_le_exact weight sensitivity b i
      (z := z') (by simpa [b] using hzz) hmassEq
    have hmono := (waterFillAt_update_signs_of_equal_mass weight sensitivity b i
      (z := z') (by simpa [b] using hzz) hmassEq).1
    unfold waterFillingSelection
    rw [hupdate] at hstep hmono
    simp [b] at hstep hmono
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hzz)]
    nlinarith
  · let b := Function.update u i z'
    have hupdate : Function.update b i z = Function.update u i z := by
      funext j
      by_cases hji : j = i <;> simp [b, Function.update, hji]
    have hmassEq : waterFillMass weight sensitivity
        (Function.update b i z) (threshold (Function.update b i z)) =
      waterFillMass weight sensitivity b (threshold b) := by
      rw [hMass, hMass]
    have hstep := waterFillAt_own_increment_le_exact weight sensitivity b i
      (z := z) (by simpa [b] using hzz) hmassEq
    have hmono := (waterFillAt_update_signs_of_equal_mass weight sensitivity b i
      (z := z) (by simpa [b] using hzz) hmassEq).1
    unfold waterFillingSelection
    rw [hupdate] at hstep hmono
    simp [b] at hstep hmono
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hzz)]
    nlinarith

set_option maxHeartbeats 800000 in
/-- For every flat capacity `1 ≤ K < n`, an all-way tie has a positive chord
that attains the factor `a(1-1/n)` for any threshold selector maintaining mass
`K * weight`.  This supplies the general-`K` tightness witness missing from the
one-slot canonical-threshold theorem below. -/
theorem waterFillingSelection_flatK_tie_attains_exact_modulus
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (slots : ℕ) (hslots : 1 ≤ slots) (hlt : slots < Fintype.card ι)
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (threshold : (ι → ℝ) → ℝ)
    (hMass : ∀ u, waterFillMass weight sensitivity u (threshold u) =
      (slots : ℝ) * (weight : ℝ)) (i : ι) :
    let delta : ℝ := (weight : ℝ) /
      (2 * (sensitivity : ℝ) * (Fintype.card ι : ℝ))
    0 < delta ∧
      waterFillingSelection weight sensitivity threshold
          (Function.update (fun _j : ι => (0 : ℝ)) i delta) i -
        waterFillingSelection weight sensitivity threshold
          (fun _j : ι => (0 : ℝ)) i =
      (sensitivity : ℝ) * delta *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  classical
  dsimp only
  set n : ℝ := (Fintype.card ι : ℝ) with hnDef
  set k : ℝ := (slots : ℝ) with hkDef
  set a : ℝ := (sensitivity : ℝ) with haDef
  set w : ℝ := (weight : ℝ) with hwDef
  have hn : 0 < n := by rw [hnDef]; positivity
  have hk : 0 < k := by rw [hkDef]; exact_mod_cast hslots
  have hkn : k < n := by rw [hkDef, hnDef]; exact_mod_cast hlt
  have hkOne : 1 ≤ k := by rw [hkDef]; exact_mod_cast hslots
  have hnTwo : 2 ≤ n := by
    rw [hnDef]
    exact_mod_cast (show 2 ≤ Fintype.card ι by omega)
  have hgap : 1 ≤ n - k := by
    rw [hnDef, hkDef, ← Nat.cast_sub (le_of_lt hlt)]
    exact_mod_cast (show 1 ≤ Fintype.card ι - slots by omega)
  have ha : 0 < a := by exact hsens
  have hw : 0 < w := by exact hweight
  set delta : ℝ := w / (2 * a * n) with hdeltaDef
  have hdelta : 0 < delta := by rw [hdeltaDef]; positivity
  set base : ℝ := w * k / n with hbaseDef
  set high : ℝ := w * (2 * k * n + n - 1) / (2 * n ^ 2) with hhighDef
  set low : ℝ := w * (2 * k * n - 1) / (2 * n ^ 2) with hlowDef
  set baseThreshold : ℝ := -(k * w) / (a * n) with hsDef
  set newThreshold : ℝ := baseThreshold + delta / n with htDef
  have hbase0 : 0 ≤ base := by rw [hbaseDef]; positivity
  have hbaseW : base ≤ w := by
    rw [hbaseDef, div_le_iff₀ hn]
    exact mul_le_mul_of_nonneg_left hkn.le hw.le
  have hden : 0 < 2 * n ^ 2 := by positivity
  have hhighNum0 : 0 ≤ 2 * k * n + n - 1 := by
    nlinarith [mul_nonneg hk.le hn.le]
  have hhighNumW : 2 * k * n + n - 1 ≤ 2 * n ^ 2 := by
    have hmul : 2 * n ≤ 2 * n * (n - k) := by
      calc
        2 * n = (2 * n) * 1 := by ring
        _ ≤ (2 * n) * (n - k) :=
          mul_le_mul_of_nonneg_left hgap (by positivity)
    nlinarith
  have hlowNum0 : 0 ≤ 2 * k * n - 1 := by
    have haux := mul_nonneg (sub_nonneg.mpr hkOne) (sub_nonneg.mpr hnTwo)
    nlinarith
  have hlowNumW : 2 * k * n - 1 ≤ 2 * n ^ 2 := by
    have hmul : k * n ≤ n * n := mul_le_mul_of_nonneg_right hkn.le hn.le
    nlinarith
  have hhigh0 : 0 ≤ high := by
    rw [hhighDef]
    exact div_nonneg (mul_nonneg hw.le hhighNum0) hden.le
  have hhighW : high ≤ w := by
    rw [hhighDef, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hhighNumW hw.le
  have hlow0 : 0 ≤ low := by
    rw [hlowDef]
    exact div_nonneg (mul_nonneg hw.le hlowNum0) hden.le
  have hlowW : low ≤ w := by
    rw [hlowDef, div_le_iff₀ hden]
    exact mul_le_mul_of_nonneg_left hlowNumW hw.le
  have hbaseRaw : ∀ j : ι,
      a * ((fun _q : ι => (0 : ℝ)) j - baseThreshold) = base := by
    intro j
    rw [hsDef, hbaseDef]
    field_simp
    ring
  have hbaseClamp : ∀ j : ι,
      waterFillAt weight sensitivity (fun _q : ι => (0 : ℝ))
        baseThreshold j = base := by
    intro j
    unfold waterFillAt
    rw [show (sensitivity : ℝ) = a from haDef.symm, hbaseRaw j]
    exact clampWeight_eq_of_mem weight hbase0 (by simpa [hwDef] using hbaseW)
  have hbaseMass : waterFillMass weight sensitivity
      (fun _q : ι => (0 : ℝ)) baseThreshold = (slots : ℝ) * (weight : ℝ) := by
    unfold waterFillMass
    calc
      ∑ j, waterFillAt weight sensitivity (fun _q : ι => (0 : ℝ))
          baseThreshold j = ∑ _j : ι, base :=
        Finset.sum_congr rfl fun j _ => hbaseClamp j
      _ = (slots : ℝ) * (weight : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← hnDef, ← hkDef, ← hwDef, hbaseDef]
        field_simp
  have hnewRaw : ∀ j : ι,
      a * (Function.update (fun _q : ι => (0 : ℝ)) i delta j - newThreshold) =
        if j = i then high else low := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, if_pos]
      rw [htDef, hsDef, hdeltaDef, hhighDef]
      field_simp
      ring
    · have hupdate : Function.update (fun _q : ι => (0 : ℝ)) i delta j = 0 := by
        simp [hji]
      rw [hupdate, if_neg hji, htDef, hsDef, hdeltaDef, hlowDef]
      field_simp
      ring
  have hnewClamp : ∀ j : ι,
      waterFillAt weight sensitivity
          (Function.update (fun _q : ι => (0 : ℝ)) i delta)
          newThreshold j = if j = i then high else low := by
    intro j
    unfold waterFillAt
    rw [show (sensitivity : ℝ) = a from haDef.symm, hnewRaw j]
    split_ifs
    · exact clampWeight_eq_of_mem weight hhigh0 (by simpa [hwDef] using hhighW)
    · exact clampWeight_eq_of_mem weight hlow0 (by simpa [hwDef] using hlowW)
  have hcardErase : (((Finset.univ : Finset ι).erase i).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), hnDef]
    norm_num
  have hnewMass : waterFillMass weight sensitivity
      (Function.update (fun _q : ι => (0 : ℝ)) i delta) newThreshold =
        (slots : ℝ) * (weight : ℝ) := by
    unfold waterFillMass
    calc
      ∑ j, waterFillAt weight sensitivity
          (Function.update (fun _q : ι => (0 : ℝ)) i delta)
          newThreshold j = ∑ j, (if j = i then high else low) :=
        Finset.sum_congr rfl fun j _ => hnewClamp j
      _ = high + ∑ _j ∈ (Finset.univ : Finset ι).erase i, low := by
        rw [← Finset.add_sum_erase (Finset.univ : Finset ι)
          (fun j => if j = i then high else low) (Finset.mem_univ i)]
        simp only [if_pos]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      _ = (slots : ℝ) * (weight : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardErase]
        rw [← hkDef, ← hwDef, hhighDef, hlowDef]
        field_simp
        ring
  have hselectedBase : waterFillingSelection weight sensitivity threshold
      (fun _q : ι => (0 : ℝ)) i = base := by
    unfold waterFillingSelection
    rw [waterFillAt_eq_of_equal_mass weight sensitivity
      (fun _q : ι => (0 : ℝ))
      ((hMass (fun _q : ι => (0 : ℝ))).trans hbaseMass.symm) i,
      hbaseClamp i]
  have hselectedHigh : waterFillingSelection weight sensitivity threshold
      (Function.update (fun _q : ι => (0 : ℝ)) i delta) i = high := by
    unfold waterFillingSelection
    rw [waterFillAt_eq_of_equal_mass weight sensitivity
      (Function.update (fun _q : ι => (0 : ℝ)) i delta)
      ((hMass (Function.update (fun _q : ι => (0 : ℝ)) i delta)).trans
        hnewMass.symm) i,
      hnewClamp i, if_pos rfl]
  constructor
  · exact hdelta
  · rw [hselectedHigh, hselectedBase]
    rw [hdeltaDef, hhighDef, hbaseDef]
    field_simp
    ring

set_option maxHeartbeats 800000 in
/-- At an interior all-way tie, one explicit positive score increment attains
the finite-population factor.  Together with
`waterFillingVector_own_lipschitz_exact`, this proves that the global modulus
is exactly `a(1-1/n)`. -/
theorem waterFillingVector_tie_attains_exact_modulus
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsens : 0 < sensitivity)
    (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    let delta : ℝ := (weight : ℝ) / (2 * (sensitivity : ℝ))
    0 < delta ∧
      waterFillingVector weight sensitivity hsens
          (Function.update (fun _j : ι => (0 : ℝ)) i delta) i -
        waterFillingVector weight sensitivity hsens (fun _j : ι => (0 : ℝ)) i =
      (sensitivity : ℝ) * delta *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) := by
  classical
  dsimp only
  set n : ℝ := (Fintype.card ι : ℝ) with hnDef
  set a : ℝ := (sensitivity : ℝ) with haDef
  set w : ℝ := (weight : ℝ) with hwDef
  set delta : ℝ := w / (2 * a) with hdeltaDef
  set baseThreshold : ℝ := -w / (a * n) with hsDef
  set newThreshold : ℝ := baseThreshold + delta / n with htDef
  have hn : 0 < n := by
    rw [hnDef]
    positivity
  have hnOne : 1 ≤ n := by
    rw [hnDef]
    exact_mod_cast le_trans (by norm_num : 1 ≤ 2) hcard
  have ha : 0 < a := by exact hsens
  have hw : 0 < w := by exact hweight
  have hdelta : 0 < delta := by rw [hdeltaDef]; positivity
  have hbaseRaw : ∀ j : ι,
      a * ((fun _k : ι => (0 : ℝ)) j - baseThreshold) = w / n := by
    intro j
    rw [hsDef]
    field_simp
    ring
  have hbase0 : 0 ≤ w / n := by positivity
  have hbaseW : w / n ≤ w := by
    rw [div_le_iff₀ hn]
    nlinarith
  have hbaseClamp : ∀ j : ι,
      waterFillAt weight sensitivity (fun _k : ι => (0 : ℝ)) baseThreshold j = w / n := by
    intro j
    unfold waterFillAt
    rw [show (sensitivity : ℝ) = a from haDef.symm,
      hbaseRaw j]
    exact clampWeight_eq_of_mem weight hbase0 (by simpa [hwDef] using hbaseW)
  have hbaseMass : IsWaterFillingThreshold weight sensitivity
      (fun _k : ι => (0 : ℝ)) baseThreshold := by
    unfold IsWaterFillingThreshold waterFillMass
    calc
      ∑ j, waterFillAt weight sensitivity (fun _k : ι => (0 : ℝ)) baseThreshold j =
          ∑ _j : ι, w / n := Finset.sum_congr rfl fun j _ => hbaseClamp j
      _ = (weight : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← hnDef, ← hwDef]
        field_simp
  set high : ℝ := w * (n + 1) / (2 * n) with hhighDef
  set low : ℝ := w / (2 * n) with hlowDef
  have hnewRaw : ∀ j : ι,
      a * (Function.update (fun _k : ι => (0 : ℝ)) i delta j - newThreshold) =
        if j = i then high else low := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self, if_pos]
      rw [htDef, hsDef, hdeltaDef, hhighDef]
      field_simp
      ring
    · have hupdate : Function.update (fun _k : ι => (0 : ℝ)) i delta j = 0 := by
        simp [hji]
      rw [hupdate]
      simp only [if_neg hji]
      rw [htDef, hsDef, hdeltaDef, hlowDef]
      field_simp
      ring
  have hhigh0 : 0 ≤ high := by rw [hhighDef]; positivity
  have hhighW : high ≤ w := by
    rw [hhighDef, div_le_iff₀ (mul_pos (by norm_num) hn)]
    nlinarith
  have hlow0 : 0 ≤ low := by rw [hlowDef]; positivity
  have hlowW : low ≤ w := by
    rw [hlowDef, div_le_iff₀ (mul_pos (by norm_num) hn)]
    nlinarith
  have hnewClamp : ∀ j : ι,
      waterFillAt weight sensitivity
          (Function.update (fun _k : ι => (0 : ℝ)) i delta) newThreshold j =
        if j = i then high else low := by
    intro j
    unfold waterFillAt
    rw [show (sensitivity : ℝ) = a from haDef.symm,
      hnewRaw j]
    split_ifs
    · exact clampWeight_eq_of_mem weight hhigh0 (by simpa [hwDef] using hhighW)
    · exact clampWeight_eq_of_mem weight hlow0 (by simpa [hwDef] using hlowW)
  have hcardErase : (((Finset.univ : Finset ι).erase i).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), hnDef]
    norm_num
  have hnewMass : IsWaterFillingThreshold weight sensitivity
      (Function.update (fun _k : ι => (0 : ℝ)) i delta) newThreshold := by
    unfold IsWaterFillingThreshold waterFillMass
    calc
      ∑ j, waterFillAt weight sensitivity
          (Function.update (fun _k : ι => (0 : ℝ)) i delta) newThreshold j =
          ∑ j, (if j = i then high else low) :=
        Finset.sum_congr rfl fun j _ => hnewClamp j
      _ = high + ∑ _j ∈ (Finset.univ : Finset ι).erase i, low := by
        rw [← Finset.add_sum_erase (Finset.univ : Finset ι)
          (fun j => if j = i then high else low) (Finset.mem_univ i)]
        simp only [if_pos]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      _ = w := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardErase, hhighDef, hlowDef]
        field_simp
        ring
      _ = (weight : ℝ) := hwDef
  have hin : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (sensitivity : ℝ) * ((fun _k : ι => (0 : ℝ)) j - baseThreshold) ∧
        (sensitivity : ℝ) * ((fun _k : ι => (0 : ℝ)) j - baseThreshold) ≤
          (weight : ℝ) := by
    intro j hj
    rw [show (sensitivity : ℝ) = a from haDef.symm, hbaseRaw j]
    exact ⟨hbase0, by simpa [hwDef] using hbaseW⟩
  have hin' : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (sensitivity : ℝ) *
          (Function.update (fun _k : ι => (0 : ℝ)) i delta j - newThreshold) ∧
        (sensitivity : ℝ) *
          (Function.update (fun _k : ι => (0 : ℝ)) i delta j - newThreshold) ≤
            (weight : ℝ) := by
    intro j hj
    rw [show (sensitivity : ℝ) = a from haDef.symm, hnewRaw j]
    split_ifs
    · exact ⟨hhigh0, by simpa [hwDef] using hhighW⟩
    · exact ⟨hlow0, by simpa [hwDef] using hlowW⟩
  have hnewMass' : IsWaterFillingThreshold weight sensitivity
      (Function.update (fun _k : ι => (0 : ℝ)) i
        ((fun _k : ι => (0 : ℝ)) i + delta)) newThreshold := by
    simpa using hnewMass
  have hin'' : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (sensitivity : ℝ) *
          (Function.update (fun _k : ι => (0 : ℝ)) i
            ((fun _k : ι => (0 : ℝ)) i + delta) j - newThreshold) ∧
        (sensitivity : ℝ) *
          (Function.update (fun _k : ι => (0 : ℝ)) i
            ((fun _k : ι => (0 : ℝ)) i + delta) j - newThreshold) ≤
            (weight : ℝ) := by
    simpa using hin'
  have hinc := waterFill_band_increment weight sensitivity hsens
    (fun _k : ι => (0 : ℝ)) i delta (Finset.univ : Finset ι)
    hbaseMass hnewMass' (Finset.mem_univ i) hin hin''
    (by intro j hj; simp at hj)
  have hband : bandFactor (Finset.univ : Finset ι) = (n - 1) / n := by
    unfold bandFactor
    rw [Finset.card_univ, ← hnDef]
    field_simp
  rw [hband] at hinc
  refine ⟨hdelta, ?_⟩
  simpa [haDef] using hinc

/-! ## Canonical flat-capacity threshold and projection rule -/

/-- For every target cardinality no larger than the population, a positive-
slope capped-simplex threshold exists.  Unlike the one-slot threshold in
`WaterFilling.lean`, this statement spends exactly `K * weight` units of mass.
-/
theorem exists_flatKWaterFillingThreshold
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ) :
    ∃ threshold,
      waterFillMass weight sensitivity u threshold =
        (slots : ℝ) * (weight : ℝ) := by
  obtain ⟨imax, himax⟩ := Finite.exists_max u
  obtain ⟨imin, himin⟩ := Finite.exists_min u
  have hzero : waterFillMass weight sensitivity u (u imax) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply clampWeight_eq_zero_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos sensitivity.coe_nonneg
      (sub_nonpos.mpr (himax i))
  let low : ℝ := u imin - (weight : ℝ) / (sensitivity : ℝ)
  have hsens0 : (sensitivity : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hsens
  have hall : ∀ i, waterFillAt weight sensitivity u low i = weight := by
    intro i
    apply clampWeight_eq_weight_of_le
    dsimp [low, waterFillAt]
    have hmin : 0 ≤ u i - u imin := sub_nonneg.mpr (himin i)
    calc
      (weight : ℝ) =
          (sensitivity : ℝ) * ((weight : ℝ) / (sensitivity : ℝ)) := by
            field_simp
      _ ≤ (sensitivity : ℝ) *
          (u i - u imin + (weight : ℝ) / (sensitivity : ℝ)) := by
            apply mul_le_mul_of_nonneg_left
            · linarith
            · exact sensitivity.coe_nonneg
      _ = (sensitivity : ℝ) *
          (u i - (u imin - (weight : ℝ) / (sensitivity : ℝ))) := by ring
  have hlow :
      (slots : ℝ) * (weight : ℝ) ≤
        waterFillMass weight sensitivity u low := by
    unfold waterFillMass
    rw [Finset.sum_congr rfl (fun i _ => hall i), Finset.sum_const,
      nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hslots) weight.coe_nonneg
  have htarget0 : 0 ≤ (slots : ℝ) * (weight : ℝ) := by positivity
  have hrange :
      (slots : ℝ) * (weight : ℝ) ∈
        Set.range (waterFillMass weight sensitivity u) := by
    apply mem_range_of_exists_le_of_exists_ge
    · exact continuous_waterFillMass weight sensitivity u
    · exact ⟨u imax, by rw [hzero]; exact htarget0⟩
    · exact ⟨low, hlow⟩
  exact hrange

/-- A canonical threshold for the flat-`K` capped-simplex projection. -/
noncomputable def flatKWaterFillingThreshold
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ) : ℝ :=
  Classical.choose
    (exists_flatKWaterFillingThreshold slots hslots weight sensitivity hsens u)

theorem flatKWaterFillingThreshold_spec
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ) :
    waterFillMass weight sensitivity u
        (flatKWaterFillingThreshold slots hslots weight sensitivity hsens u) =
      (slots : ℝ) * (weight : ℝ) :=
  Classical.choose_spec
    (exists_flatKWaterFillingThreshold slots hslots weight sensitivity hsens u)

/-- The canonical flat-capacity projection allocation. -/
noncomputable def flatKWaterFillingSelection
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) :
    (ι → ℝ) → ι → ℝ :=
  waterFillingSelection weight sensitivity
    (flatKWaterFillingThreshold slots hslots weight sensitivity hsens)

theorem flatKWaterFillingSelection_mass
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ) :
    ∑ i, flatKWaterFillingSelection slots hslots weight sensitivity hsens u i =
      (slots : ℝ) * (weight : ℝ) := by
  exact flatKWaterFillingThreshold_spec
    slots hslots weight sensitivity hsens u

theorem flatKWaterFillingSelection_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ)
    (i : ι) :
    0 ≤ flatKWaterFillingSelection slots hslots weight sensitivity hsens u i :=
  clampWeight_nonneg weight _

theorem flatKWaterFillingSelection_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (slots : ℕ) (hslots : slots ≤ Fintype.card ι)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity) (u : ι → ℝ)
    (i : ι) :
    flatKWaterFillingSelection slots hslots weight sensitivity hsens u i ≤ weight :=
  clampWeight_le weight _

/-- The flat-capacity projection has the displaced-mass regret bound on every
real score profile.  The proof lowers the reserve to the profile minimum, so
the eligible-profile theorem from `FlatK.lean` applies without restricting the
unbounded score domain. -/
theorem flatKWaterFillingSelection_regret_le
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) (u : Fin n → ℝ) :
    (weight : ℝ) *
        topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
        scoreValue
          (flatKWaterFillingSelection (ι := Fin n) K (by simpa using le_of_lt hKn)
            weight sensitivity hsens u) u ≤
      (K : ℝ) * ((n - K : ℕ) : ℝ) / (n : ℝ) *
        (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  obtain ⟨T, hTcard, hTscore⟩ :=
    exists_subsetScore_eq_topKScore K (by simpa using le_of_lt hKn) u
  obtain ⟨imin, himin⟩ := Finite.exists_min u
  let b : EligibleProfile (Fin n) (u imin) :=
    fun i => ⟨u i, himin i⟩
  let threshold := flatKWaterFillingThreshold (ι := Fin n) K
    (by simpa using le_of_lt hKn)
    weight sensitivity hsens u
  have hmass : waterFillMass weight sensitivity (fun i => (b i : ℝ)) threshold =
      (K : ℝ) * (weight : ℝ) := by
    simpa [b, threshold] using
      flatKWaterFillingThreshold_spec (ι := Fin n) K
        (by simpa using le_of_lt hKn)
        weight sensitivity hsens u
  have hbound := flatK_waterFilling_loss_le
    (ι := Fin n) (reserve := u imin) K weight sensitivity hweight hsens hKpos
    (by simpa using hKn)
    b threshold hmass T hTcard
  rw [← hTscore]
  simpa [b, threshold, scoreValue, subsetScore,
    flatKWaterFillingSelection, waterFillingSelection, Finset.sum_mul,
    Nat.cast_sub hKn.le, mul_comm] using hbound

set_option maxHeartbeats 2000000 in
/-- The displaced-mass upper bound is attained by the two-block profile, so it
is the exact worst-case regret of the canonical flat-capacity projection. -/
theorem flatKWaterFillingSelection_regret_attained
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (weight sensitivity : NNReal) (hweight : 0 < weight)
    (hsens : 0 < sensitivity) :
    ∃ u : Fin n → ℝ,
      (weight : ℝ) *
          topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue
            (flatKWaterFillingSelection (ι := Fin n) K
              (by simpa using le_of_lt hKn) weight sensitivity hsens u) u =
        (K : ℝ) * ((n - K : ℕ) : ℝ) / (n : ℝ) *
          (weight : ℝ) ^ 2 / (4 * (sensitivity : ℝ)) := by
  classical
  obtain ⟨T, hTuniv, hTcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n)))
      (n := K) (by simpa using (le_of_lt hKn : K ≤ n))
  let P : EligibleProfile (Fin n) 0 :=
    blockProfile 0 T
      (flatKOutLevel n K weight sensitivity)
      (flatKInLevel n K weight sensitivity)
      (by unfold flatKOutLevel; positivity)
      (by unfold flatKInLevel; positivity)
  let u : Fin n → ℝ := fun i => (P i : ℝ)
  have hu : ∀ i, u i = 0 +
      (if i ∈ T then flatKInLevel n K weight sensitivity
        else flatKOutLevel n K weight sensitivity) := by
    intro i
    exact blockProfile_coe 0 T
      (flatKOutLevel n K weight sensitivity)
      (flatKInLevel n K weight sensitivity) _ _ i
  have hlevels :
      flatKOutLevel n K weight sensitivity ≤
        flatKInLevel n K weight sensitivity := by
    unfold flatKOutLevel flatKInLevel
    have hnNat : 0 < n :=
      (lt_of_lt_of_le Nat.zero_lt_one hKpos).trans hKn
    have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
    have hs : (0 : ℝ) < sensitivity := by exact_mod_cast hsens
    have hw : (0 : ℝ) ≤ weight := weight.coe_nonneg
    field_simp
    nlinarith
  have htop : subsetScore T u =
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u := by
    obtain ⟨R, hRcard, hRscore⟩ :=
      exists_subsetScore_eq_topKScore K
        (by simpa using (le_of_lt hKn : K ≤ n)) u
    rw [← hRscore]
    have hpoint : ∀ i, u i ≤
        flatKInLevel n K weight sensitivity := by
      intro i
      by_cases hi : i ∈ T
      · rw [hu i, if_pos hi]
        simp
      · rw [hu i, if_neg hi]
        simpa using hlevels
    have hR : subsetScore R u ≤
        (K : ℝ) * flatKInLevel n K weight sensitivity := by
      unfold subsetScore
      calc
        ∑ i ∈ R, u i ≤
            ∑ _i ∈ R, flatKInLevel n K weight sensitivity :=
          Finset.sum_le_sum fun i hi => hpoint i
        _ = (K : ℝ) * flatKInLevel n K weight sensitivity := by
          rw [Finset.sum_const, hRcard, nsmul_eq_mul]
    have hT : subsetScore T u =
        (K : ℝ) * flatKInLevel n K weight sensitivity := by
      unfold subsetScore
      calc
        ∑ i ∈ T, u i =
            ∑ _i ∈ T, flatKInLevel n K weight sensitivity := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hu i, if_pos hi]
          ring
        _ = (K : ℝ) * flatKInLevel n K weight sensitivity := by
          rw [Finset.sum_const, hTcard, nsmul_eq_mul]
    have hTle := subsetScore_le_topKScore K
      (by simpa using (le_of_lt hKn : K ≤ n)) u T hTcard
    linarith
  have hexplicitMass := flatK_twoBlock_mass
    (reserve := (0 : ℝ)) (ι := Fin n) K weight sensitivity hweight hsens
    hKpos (by simpa using hKn) T hTcard
  have hselectedMass := flatKWaterFillingThreshold_spec (ι := Fin n) K
    (by simpa using le_of_lt hKn) weight sensitivity hsens u
  have halloc : ∀ i,
      flatKWaterFillingSelection (ι := Fin n) K
          (by simpa using le_of_lt hKn) weight sensitivity hsens u i =
        waterFillAt weight sensitivity u 0 i := by
    intro i
    unfold flatKWaterFillingSelection waterFillingSelection
    apply waterFillAt_eq_of_equal_mass
    simpa [u, P] using hselectedMass.trans hexplicitMass.symm
  have hloss := flatK_twoBlock_loss_eq
    (reserve := (0 : ℝ)) (ι := Fin n) K weight sensitivity hweight hsens
    hKpos (by simpa using hKn) T hTcard
  have hselectedEq :
      scoreValue
          (flatKWaterFillingSelection (ι := Fin n) K
            (by simpa using le_of_lt hKn) weight sensitivity hsens u) u =
        ∑ i, u i * waterFillAt weight sensitivity u 0 i := by
    unfold scoreValue
    apply Finset.sum_congr rfl
    intro i hi
    rw [halloc i]
  refine ⟨u, ?_⟩
  rw [← htop, hselectedEq]
  unfold subsetScore
  rw [Finset.mul_sum]
  simpa [u, P,
    Nat.cast_sub hKn.le, mul_comm] using hloss

/-! ## Spending the finite-population modulus slack -/

/-- Internal clip slope that spends the entire published own-coordinate
certificate in a population of size `n`. -/
noncomputable def budgetSpentSensitivity (n : ℕ) (certificate : NNReal) : NNReal :=
  ⟨(n : ℝ) * (certificate : ℝ) / ((n - 1 : ℕ) : ℝ),
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) certificate.coe_nonneg)
      (Nat.cast_nonneg (n - 1))⟩

@[simp] theorem budgetSpentSensitivity_coe (n : ℕ) (certificate : NNReal) :
    (budgetSpentSensitivity n certificate : ℝ) =
      (n : ℝ) * (certificate : ℝ) / ((n - 1 : ℕ) : ℝ) := by
  rfl

theorem budgetSpentSensitivity_pos
    (n : ℕ) (hn : 2 ≤ n) (certificate : NNReal) (hcert : 0 < certificate) :
    0 < budgetSpentSensitivity n certificate := by
  unfold budgetSpentSensitivity
  have hnReal : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hcertReal : (0 : ℝ) < (certificate : ℝ) := by
    exact_mod_cast hcert
  have hdenReal : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  exact div_pos (mul_pos hnReal hcertReal) hdenReal

/-- At the budget-spending slope, the canonical flat-capacity projection has
own-coordinate modulus at most the published certificate, and an all-way tie
attains that same coefficient for every `1 ≤ K < n`. -/
theorem budgetSpent_flatK_own_modulus_exact
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcert : 0 < certificate) (i : Fin n) :
    let slope := budgetSpentSensitivity n certificate
    let p := flatKWaterFillingSelection (ι := Fin n) K
      (by simpa using (le_of_lt hKn : K ≤ n)) weight slope
      (budgetSpentSensitivity_pos n (by omega) certificate hcert)
    (∀ (u : Fin n → ℝ) z z',
      |p (Function.update u i z') i - p (Function.update u i z) i| ≤
        (certificate : ℝ) * |z' - z|) ∧
    (∃ delta : ℝ, 0 < delta ∧
      p (Function.update (fun _j : Fin n => (0 : ℝ)) i delta) i -
          p (fun _j : Fin n => (0 : ℝ)) i =
        (certificate : ℝ) * delta) := by
  dsimp only
  have hnNat : 0 < n := (lt_of_lt_of_le Nat.zero_lt_one hKpos).trans hKn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hslope := budgetSpentSensitivity_pos n (by omega) certificate hcert
  have hmass : ∀ u : Fin n → ℝ,
      waterFillMass weight (budgetSpentSensitivity n certificate) u
          (flatKWaterFillingThreshold (ι := Fin n) K
            (by simpa using (le_of_lt hKn : K ≤ n)) weight
            (budgetSpentSensitivity n certificate) hslope u) =
        (K : ℝ) * (weight : ℝ) :=
    flatKWaterFillingThreshold_spec (ι := Fin n) K
      (by simpa using (le_of_lt hKn : K ≤ n)) weight
      (budgetSpentSensitivity n certificate) hslope
  constructor
  · intro u z z'
    have hupper := waterFillingSelection_own_lipschitz_exact
      weight (budgetSpentSensitivity n certificate)
      (flatKWaterFillingThreshold (ι := Fin n) K
        (by simpa using (le_of_lt hKn : K ≤ n)) weight
        (budgetSpentSensitivity n certificate) hslope)
      ((K : ℝ) * (weight : ℝ)) hmass u i z z'
    simp only [Fintype.card_fin] at hupper
    have hnOne : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hcoeff :
        (budgetSpentSensitivity n certificate : ℝ) *
            (((n : ℝ) - 1) / (n : ℝ)) = certificate := by
      rw [budgetSpentSensitivity_coe, hnSub]
      field_simp
    rw [hcoeff] at hupper
    exact hupper
  · have hattain := waterFillingSelection_flatK_tie_attains_exact_modulus
      K hKpos (by simpa using hKn) weight (budgetSpentSensitivity n certificate)
      hweight hslope
      (flatKWaterFillingThreshold (ι := Fin n) K
        (by simpa using (le_of_lt hKn : K ≤ n)) weight
        (budgetSpentSensitivity n certificate) hslope)
      hmass i
    dsimp only at hattain
    simp only [Fintype.card_fin] at hattain
    let delta : ℝ := (weight : ℝ) /
      (2 * (budgetSpentSensitivity n certificate : ℝ) * (n : ℝ))
    refine ⟨delta, by simpa [delta] using hattain.1, ?_⟩
    have hnOne : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hcoeff :
        (budgetSpentSensitivity n certificate : ℝ) *
            (((n : ℝ) - 1) / (n : ℝ)) = certificate := by
      rw [budgetSpentSensitivity_coe, hnSub]
      field_simp
    calc
      flatKWaterFillingSelection (ι := Fin n) K
            (by simpa using (le_of_lt hKn : K ≤ n)) weight
            (budgetSpentSensitivity n certificate) hslope
            (Function.update (fun _j : Fin n => (0 : ℝ)) i delta) i -
          flatKWaterFillingSelection (ι := Fin n) K
            (by simpa using (le_of_lt hKn : K ≤ n)) weight
            (budgetSpentSensitivity n certificate) hslope
            (fun _j : Fin n => (0 : ℝ)) i =
        (budgetSpentSensitivity n certificate : ℝ) * delta *
          (((n : ℝ) - 1) / (n : ℝ)) := by
            simpa [delta, flatKWaterFillingSelection] using hattain.2
      _ = ((budgetSpentSensitivity n certificate : ℝ) *
          (((n : ℝ) - 1) / (n : ℝ))) * delta := by ring
      _ = (certificate : ℝ) * delta := by rw [hcoeff]

/-- The same budget-spending projection has the exact displayed worst-case
flat-`K` inclusion loss. -/
theorem budgetSpent_flatK_regret_exact
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (weight certificate : NNReal) (hweight : 0 < weight)
    (hcert : 0 < certificate) :
    let slope := budgetSpentSensitivity n certificate
    let p := flatKWaterFillingSelection (ι := Fin n) K
      (by simpa using (le_of_lt hKn : K ≤ n)) weight slope
      (budgetSpentSensitivity_pos n (by omega) certificate hcert)
    (∀ u : Fin n → ℝ,
      (weight : ℝ) *
          topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue (p u) u ≤
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (n : ℝ) ^ 2 * (weight : ℝ) ^ 2 /
          (4 * (certificate : ℝ))) ∧
    (∃ u : Fin n → ℝ,
      (weight : ℝ) *
          topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue (p u) u =
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (n : ℝ) ^ 2 * (weight : ℝ) ^ 2 /
          (4 * (certificate : ℝ))) := by
  dsimp only
  have hslope := budgetSpentSensitivity_pos n (by omega) certificate hcert
  have hnNat : 0 < n := (lt_of_lt_of_le Nat.zero_lt_one hKpos).trans hKn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcertReal : (0 : ℝ) < certificate := by exact_mod_cast hcert
  have hnOne : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hscale :
      (K : ℝ) * ((n - K : ℕ) : ℝ) / (n : ℝ) *
          (weight : ℝ) ^ 2 /
          (4 * (budgetSpentSensitivity n certificate : ℝ)) =
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (n : ℝ) ^ 2 * (weight : ℝ) ^ 2 /
          (4 * (certificate : ℝ)) := by
    rw [budgetSpentSensitivity_coe, hnSub]
    field_simp
  constructor
  · intro u
    have h := flatKWaterFillingSelection_regret_le n K hKpos hKn
      weight (budgetSpentSensitivity n certificate) hweight hslope u
    rw [hscale] at h
    exact h
  · obtain ⟨u, hu⟩ := flatKWaterFillingSelection_regret_attained
      n K hKpos hKn weight (budgetSpentSensitivity n certificate)
      hweight hslope
    refine ⟨u, ?_⟩
    rw [hscale] at hu
    exact hu

set_option maxHeartbeats 1000000 in
/-- Profile-local one-slot spread bound.  It uses only exact mass,
order-preservation of the capped-simplex projection, and the fact that a
highest score receives at least the average allocation. -/
theorem flatKWaterFillingSelection_oneSlot_local_regret_le
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (weight sensitivity : NNReal) (hsens : 0 < sensitivity)
    (u : Fin n → ℝ) (leader trailer : Fin n)
    (hleader : ∀ i, u i ≤ u leader)
    (htrailer : ∀ i, u trailer ≤ u i) :
    let p := flatKWaterFillingSelection (ι := Fin n) 1
      (by simpa using (show 1 ≤ n by omega))
      weight sensitivity hsens
    (weight : ℝ) * u leader - scoreValue (p u) u ≤
      (weight : ℝ) * (1 - 1 / (n : ℝ)) *
        (u leader - u trailer) := by
  dsimp only
  let p : Fin n → ℝ := flatKWaterFillingSelection (ι := Fin n) 1
    (by simpa using (show 1 ≤ n by omega)) weight sensitivity hsens u
  have hmass : ∑ i, p i = (weight : ℝ) := by
    simpa [p] using flatKWaterFillingSelection_mass (ι := Fin n) 1
      (by simpa using (show 1 ≤ n by omega)) weight sensitivity hsens u
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    exact flatKWaterFillingSelection_nonneg (ι := Fin n) 1
      (by simpa using (show 1 ≤ n by omega)) weight sensitivity hsens u i
  have hpOrder : ∀ i, p i ≤ p leader := by
    intro i
    unfold p flatKWaterFillingSelection waterFillingSelection
    apply clampWeight_monotone
    apply mul_le_mul_of_nonneg_left _ sensitivity.coe_nonneg
    exact sub_le_sub_right (hleader i) _
  have hsumOrder : (weight : ℝ) ≤ (n : ℝ) * p leader := by
    have hsum : ∑ i, p i ≤ ∑ _i : Fin n, p leader :=
      Finset.sum_le_sum fun i hi => hpOrder i
    rw [hmass, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hsum
    exact hsum
  have hnReal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpAverage : (weight : ℝ) / (n : ℝ) ≤ p leader := by
    rw [div_le_iff₀ hnReal]
    simpa [mul_comm] using hsumOrder
  have hspread0 : 0 ≤ u leader - u trailer := by
    exact sub_nonneg.mpr (hleader trailer)
  have hregret :
      (weight : ℝ) * u leader - scoreValue p u =
        ∑ i, p i * (u leader - u i) := by
    unfold scoreValue
    rw [← hmass]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have herase :
      ∑ i, p i * (u leader - u i) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader,
          p i * (u leader - u i) := by
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
      (fun i => p i * (u leader - u i)) (Finset.mem_univ leader)]
    ring
  have hgap : ∀ i, u leader - u i ≤ u leader - u trailer := by
    intro i
    linarith [htrailer i]
  have hbound :
      ∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader,
          p i * (u leader - u i) ≤
        (u leader - u trailer) * ((weight : ℝ) - p leader) := by
    calc
      ∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader,
          p i * (u leader - u i) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader,
          p i * (u leader - u trailer) := by
            exact Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left (hgap i) (hp0 i)
      _ = (u leader - u trailer) *
          (∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader, p i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (u leader - u trailer) * ((weight : ℝ) - p leader) := by
            have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
              p (Finset.mem_univ leader)
            rw [hmass] at hsplit
            congr 1
            linarith
  rw [hregret, herase]
  calc
    ∑ i ∈ (Finset.univ : Finset (Fin n)).erase leader,
        p i * (u leader - u i) ≤
      (u leader - u trailer) * ((weight : ℝ) - p leader) := hbound
    _ ≤ (u leader - u trailer) *
        ((weight : ℝ) - (weight : ℝ) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hspread0
          linarith
    _ = (weight : ℝ) * (1 - 1 / (n : ℝ)) *
        (u leader - u trailer) := by ring

/-! ## The literal infimum-over-rules frontier -/

/-- Admissibility for the paper's normalized unbounded direct-score problem.
The range and exact-mass clauses say that every output lies in
`H_(n,K)`; the last clause is the full marginal-vector modulus. -/
def IsFlatKScoreRule
    (n K : ℕ) (Lambda : ℝ) (p : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  (∀ u i, 0 ≤ p u i ∧ p u i ≤ 1) ∧
  (∀ u, ∑ i, p u i = (K : ℝ)) ∧
  ∀ u v, finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v

def HasFlatKRegretBound
    (n K : ℕ) (hK : K ≤ n) (p : (Fin n → ℝ) → Fin n → ℝ)
    (R : ℝ) : Prop :=
  ∀ u, topKScore K (by simpa using hK) u - scoreValue (p u) u ≤ R

/-- The minimax frontier is written as the infimum of all uniform regret
bounds.  This formulation is definitionally equivalent to the displayed
`inf_p sup_u` and is more convenient for finite-dimensional certificates. -/
noncomputable def flatKScoreFrontier
    (n K : ℕ) (hK : K ≤ n) (Lambda : ℝ) : ℝ :=
  sInf {R : ℝ | ∃ p : (Fin n → ℝ) → Fin n → ℝ,
    IsFlatKScoreRule n K Lambda p ∧ HasFlatKRegretBound n K hK p R}

/-- Projection at slope `Lambda*n/[2(n-1)]`, expressed through the
budget-spending own-coordinate normalization `Lambda/2`. -/
noncomputable def flatKScoreProjection
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) (hLambda : 0 < Lambda) :
    (Fin n → ℝ) → Fin n → ℝ :=
  flatKWaterFillingSelection (ι := Fin n) K (by simpa using le_of_lt hKn)
    1 (budgetSpentSensitivity n (Lambda / 2))
    (budgetSpentSensitivity_pos n (by omega) (Lambda / 2) (by positivity))

set_option maxHeartbeats 1000000 in
/-- The normalized projection is an admissible full-vector-`Lambda` rule. -/
theorem flatKScoreProjection_admissible
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) (hLambda : 0 < Lambda) :
    IsFlatKScoreRule n K (Lambda : ℝ)
      (flatKScoreProjection n K hKpos hKn Lambda hLambda) := by
  have hslope := budgetSpentSensitivity_pos n (by omega)
    (Lambda / 2) (by positivity)
  have hmass : ∀ u : Fin n → ℝ,
      waterFillMass 1 (budgetSpentSensitivity n (Lambda / 2)) u
          (flatKWaterFillingThreshold (ι := Fin n) K
            (by simpa using (le_of_lt hKn : K ≤ n)) 1
            (budgetSpentSensitivity n (Lambda / 2)) hslope u) =
        (K : ℝ) := by
    intro u
    simpa using flatKWaterFillingThreshold_spec (ι := Fin n) K
      (by simpa using (le_of_lt hKn : K ≤ n)) 1
      (budgetSpentSensitivity n (Lambda / 2)) hslope u
  refine ⟨?_, hmass, ?_⟩
  · intro u i
    constructor
    · exact flatKWaterFillingSelection_nonneg (ι := Fin n) K
        (by simpa using (le_of_lt hKn : K ≤ n)) 1
        (budgetSpentSensitivity n (Lambda / 2)) hslope u i
    · simpa using flatKWaterFillingSelection_le (ι := Fin n) K
        (by simpa using (le_of_lt hKn : K ≤ n)) 1
        (budgetSpentSensitivity n (Lambda / 2)) hslope u i
  · intro u v
    have h := waterFillingSelection_fullVector_l1_le
      1 (budgetSpentSensitivity n (Lambda / 2))
      (flatKWaterFillingThreshold (ι := Fin n) K
        (by simpa using (le_of_lt hKn : K ≤ n)) 1
        (budgetSpentSensitivity n (Lambda / 2)) hslope)
      (K : ℝ) hmass v u
    simp only [Fintype.card_fin] at h
    have hnReal : (0 : ℝ) < n := by
      exact_mod_cast ((lt_of_lt_of_le Nat.zero_lt_one hKpos).trans hKn)
    have hnSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    have hcoeff :
        2 * (budgetSpentSensitivity n (Lambda / 2) : ℝ) *
            (((n : ℝ) - 1) / (n : ℝ)) = (Lambda : ℝ) := by
      rw [budgetSpentSensitivity_coe, hnSub]
      have hnOne : (n : ℝ) - 1 ≠ 0 := by
        have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        linarith
      field_simp
      simp [NNReal.coe_div]
      ring
    rw [hcoeff] at h
    simpa [flatKScoreProjection] using h

set_option maxHeartbeats 1000000 in
/-- Exact uniform regret bound and attainment for the normalized projection. -/
theorem flatKScoreProjection_regret_exact
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) (hLambda : 0 < Lambda) :
    let p := flatKScoreProjection n K hKpos hKn Lambda hLambda
    HasFlatKRegretBound n K (le_of_lt hKn) p
      ((K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
        (2 * (Lambda : ℝ) * (n : ℝ) ^ 2)) ∧
    (∃ u : Fin n → ℝ,
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue (p u) u =
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (2 * (Lambda : ℝ) * (n : ℝ) ^ 2)) := by
  dsimp only [HasFlatKRegretBound, flatKScoreProjection]
  have h := budgetSpent_flatK_regret_exact n K hKpos hKn
    1 (Lambda / 2) (by norm_num) (by positivity)
  dsimp only at h
  have hLambdaReal : (0 : ℝ) < Lambda := by exact_mod_cast hLambda
  have hscale :
      (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
            (n : ℝ) ^ 2 * (1 : ℝ) ^ 2 /
            (4 * ((Lambda / 2 : NNReal) : ℝ)) =
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (2 * (Lambda : ℝ) * (n : ℝ) ^ 2) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    field_simp
    ring
  constructor
  · intro u
    have hu := h.1 u
    calc
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue
            (flatKWaterFillingSelection (ι := Fin n) K
              (by simpa using (le_of_lt hKn : K ≤ n)) 1
              (budgetSpentSensitivity n (Lambda / 2))
              (budgetSpentSensitivity_pos n (by omega) (Lambda / 2)
                (by positivity)) u) u ≤
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
            (n : ℝ) ^ 2 * (1 : ℝ) ^ 2 /
            (4 * ((Lambda / 2 : NNReal) : ℝ)) := by simpa using hu
      _ = (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (2 * (Lambda : ℝ) * (n : ℝ) ^ 2) := hscale
  · obtain ⟨u, hu⟩ := h.2
    refine ⟨u, ?_⟩
    calc
      topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u -
          scoreValue
            (flatKWaterFillingSelection (ι := Fin n) K
              (by simpa using (le_of_lt hKn : K ≤ n)) 1
              (budgetSpentSensitivity n (Lambda / 2))
              (budgetSpentSensitivity_pos n (by omega) (Lambda / 2)
                (by positivity)) u) u =
        (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
            (n : ℝ) ^ 2 * (1 : ℝ) ^ 2 /
            (4 * ((Lambda / 2 : NNReal) : ℝ)) := by simpa using hu
      _ = (K : ℝ) * ((n - K : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) /
          (2 * (Lambda : ℝ) * (n : ℝ) ^ 2) := hscale

set_option maxHeartbeats 1000000 in
/-- Literal minimax sandwich for the unbounded normalized score frontier.  The
lower endpoint is universal over all admissible rules; the upper endpoint is
the exact worst-case regret of `flatKScoreProjection`. -/
theorem flatKScoreFrontier_sandwich
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) (hLambda : 0 < Lambda) :
    ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
        (2 * (Lambda : ℝ) * (n : ℝ) *
          (((max K (n - K) : ℕ) : ℝ) + 1)) ≤
      flatKScoreFrontier n K (le_of_lt hKn) (Lambda : ℝ) ∧
    flatKScoreFrontier n K (le_of_lt hKn) (Lambda : ℝ) ≤
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) *
        ((n - 1 : ℕ) : ℝ) /
          (2 * (Lambda : ℝ) * (n : ℝ) ^ 2) := by
  let L : ℝ :=
    ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
      (2 * (Lambda : ℝ) * (n : ℝ) *
        (((max K (n - K) : ℕ) : ℝ) + 1))
  let U : ℝ :=
    ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) *
      ((n - 1 : ℕ) : ℝ) /
        (2 * (Lambda : ℝ) * (n : ℝ) ^ 2)
  let p := flatKScoreProjection n K hKpos hKn Lambda hLambda
  have hp := flatKScoreProjection_admissible n K hKpos hKn Lambda hLambda
  have hpRegret := flatKScoreProjection_regret_exact
    n K hKpos hKn Lambda hLambda
  dsimp only at hpRegret
  have hprod :
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) =
        (K : ℝ) * ((n - K : ℕ) : ℝ) := by
    rcases le_total K (n - K) with hle | hge
    · rw [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hge, max_eq_left hge]
      ring
  have hpBound : HasFlatKRegretBound n K (le_of_lt hKn) p U := by
    intro u
    have hu := hpRegret.1 u
    dsimp [U]
    rw [hprod]
    exact hu
  let bounds : Set ℝ := {R : ℝ | ∃ q : (Fin n → ℝ) → Fin n → ℝ,
    IsFlatKScoreRule n K (Lambda : ℝ) q ∧
      HasFlatKRegretBound n K (le_of_lt hKn) q R}
  have hUmem : U ∈ bounds := by
    exact ⟨p, hp, hpBound⟩
  have hnonempty : bounds.Nonempty := ⟨U, hUmem⟩
  have hLambdaReal : (0 : ℝ) < Lambda := by exact_mod_cast hLambda
  have hlower : ∀ R ∈ bounds, L ≤ R := by
    intro R hR
    rcases hR with ⟨q, hq, hqRegret⟩
    have hcert := scoreRule_allCapacity_lower n K hKpos hKn q hq.2.1
      (Lambda : ℝ) hLambdaReal hq.2.2 R hqRegret
    exact hcert
  change L ≤ sInf bounds ∧ sInf bounds ≤ U
  constructor
  · exact le_csInf hnonempty hlower
  · exact csInf_le ⟨L, hlower⟩ hUmem

/-- Admissibility for the bounded score cube.  No extension of the rule or of
its modulus outside `[0,1]^n` is assumed. -/
def IsFlatKCubeRule
    (n K : ℕ) (Lambda : ℝ) (p : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  (∀ u, InUnitCube u → ∀ i, 0 ≤ p u i ∧ p u i ≤ 1) ∧
  (∀ u, InUnitCube u → ∑ i, p u i = (K : ℝ)) ∧
  ∀ u, InUnitCube u → ∀ v, InUnitCube v →
    finiteL1 (p u) (p v) ≤ Lambda * finiteL1 u v

def HasFlatKCubeRegretBound
    (n K : ℕ) (hK : K ≤ n) (p : (Fin n → ℝ) → Fin n → ℝ)
    (R : ℝ) : Prop :=
  ∀ u, InUnitCube u →
    topKScore K (by simpa using hK) u - scoreValue (p u) u ≤ R

noncomputable def flatKCubeFrontier
    (n K : ℕ) (hK : K ≤ n) (Lambda : ℝ) : ℝ :=
  sInf {R : ℝ | ∃ p : (Fin n → ℝ) → Fin n → ℝ,
    IsFlatKCubeRule n K Lambda p ∧ HasFlatKCubeRegretBound n K hK p R}

/-- The uniform rule witnesses nonemptiness of the bounded minimax problem,
including at zero modulus. -/
noncomputable def flatKConstantScoreRule
    (n K : ℕ) : (Fin n → ℝ) → Fin n → ℝ :=
  fun _u _i => (K : ℝ) / (n : ℝ)

set_option maxHeartbeats 1000000 in
theorem flatKConstantScoreRule_cube_certificate
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) :
    IsFlatKCubeRule n K (Lambda : ℝ) (flatKConstantScoreRule n K) ∧
      HasFlatKCubeRegretBound n K (le_of_lt hKn)
        (flatKConstantScoreRule n K) (K : ℝ) := by
  have hnNat : 0 < n := (lt_of_lt_of_le Nat.zero_lt_one hKpos).trans hKn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hKnonneg : (0 : ℝ) ≤ K := by positivity
  have hKleReal : (K : ℝ) ≤ n := by exact_mod_cast (le_of_lt hKn)
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro u hu i
      dsimp [flatKConstantScoreRule]
      exact ⟨div_nonneg hKnonneg hnReal.le,
        (div_le_one hnReal).mpr hKleReal⟩
    · intro u hu
      simp only [flatKConstantScoreRule, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · intro u hu v hv
      have hzero : finiteL1 (flatKConstantScoreRule n K u)
          (flatKConstantScoreRule n K v) = 0 := by
        simp [finiteL1, flatKConstantScoreRule]
      rw [hzero]
      apply mul_nonneg Lambda.coe_nonneg
      unfold finiteL1
      exact Finset.sum_nonneg fun i hi => abs_nonneg _
  · intro u hu
    have hscore0 : 0 ≤ scoreValue (flatKConstantScoreRule n K u) u := by
      unfold scoreValue flatKConstantScoreRule
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hu i).1 (div_nonneg hKnonneg hnReal.le)
    have htop : topKScore K (by simpa using (le_of_lt hKn : K ≤ n)) u ≤ K := by
      obtain ⟨T, hTcard, hTscore⟩ := exists_subsetScore_eq_topKScore K
        (by simpa using (le_of_lt hKn : K ≤ n)) u
      rw [← hTscore]
      unfold subsetScore
      calc
        ∑ i ∈ T, u i ≤ ∑ _i ∈ T, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => (hu i).2
        _ = (K : ℝ) := by
          rw [Finset.sum_const, hTcard, nsmul_eq_mul]
          ring
    linarith

set_option maxHeartbeats 1000000 in
/-- Literal two-regime lower bound for the minimax frontier on `[0,1]^n`. -/
theorem flatKCubeFrontier_lower
    (n K : ℕ) [NeZero n] (hKpos : 1 ≤ K) (hKn : K < n)
    (Lambda : NNReal) :
    ((((max K (n - K) : ℕ) : ℝ) /
          (((max K (n - K) : ℕ) : ℝ) + 1) ≤ (Lambda : ℝ)) →
      ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
          (2 * (Lambda : ℝ) * (n : ℝ) *
            (((max K (n - K) : ℕ) : ℝ) + 1)) ≤
        flatKCubeFrontier n K (le_of_lt hKn) (Lambda : ℝ)) ∧
    (((Lambda : ℝ) < ((max K (n - K) : ℕ) : ℝ) /
          (((max K (n - K) : ℕ) : ℝ) + 1)) →
      ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
          (((max K (n - K) : ℕ) : ℝ) -
            (((max K (n - K) : ℕ) : ℝ) + 1) * (Lambda : ℝ) / 2) ≤
        flatKCubeFrontier n K (le_of_lt hKn) (Lambda : ℝ)) := by
  let bounds : Set ℝ := {R : ℝ | ∃ p : (Fin n → ℝ) → Fin n → ℝ,
    IsFlatKCubeRule n K (Lambda : ℝ) p ∧
      HasFlatKCubeRegretBound n K (le_of_lt hKn) p R}
  have hconst := flatKConstantScoreRule_cube_certificate
    n K hKpos hKn Lambda
  have hKmem : (K : ℝ) ∈ bounds := ⟨flatKConstantScoreRule n K, hconst⟩
  have hnonempty : bounds.Nonempty := ⟨(K : ℝ), hKmem⟩
  have hall : ∀ R ∈ bounds,
      ((((max K (n - K) : ℕ) : ℝ) /
            (((max K (n - K) : ℕ) : ℝ) + 1) ≤ (Lambda : ℝ)) →
        ((min K (n - K) : ℕ) : ℝ) * ((max K (n - K) : ℕ) : ℝ) ^ 2 /
            (2 * (Lambda : ℝ) * (n : ℝ) *
              (((max K (n - K) : ℕ) : ℝ) + 1)) ≤ R) ∧
      (((Lambda : ℝ) < ((max K (n - K) : ℕ) : ℝ) /
            (((max K (n - K) : ℕ) : ℝ) + 1)) →
        ((min K (n - K) : ℕ) : ℝ) / (n : ℝ) *
            (((max K (n - K) : ℕ) : ℝ) -
              (((max K (n - K) : ℕ) : ℝ) + 1) * (Lambda : ℝ) / 2) ≤ R) := by
    intro R hR
    rcases hR with ⟨p, hp, hpRegret⟩
    exact scoreRule_cube_allCapacity_lower n K hKpos hKn p hp.2.1
      (Lambda : ℝ) Lambda.coe_nonneg hp.2.2 R hpRegret
  constructor
  · intro hhigh
    change _ ≤ sInf bounds
    apply le_csInf hnonempty
    intro R hR
    exact (hall R hR).1 hhigh
  · intro hlow
    change _ ≤ sInf bounds
    apply le_csInf hnonempty
    intro R hR
    exact (hall R hR).2 hlow

/-! ## Algebra of the near-exact sandwich -/

/-- The displayed ratio between the projection upper endpoint and the
adjacent-profile lower endpoint. -/
theorem flatK_frontier_ratio
    (n Kminus Kplus : ℝ)
    (hn : 0 < n) (hKm : 0 < Kminus) (hKp : 0 < Kplus)
    (hsum : Kminus + Kplus = n) :
    (Kminus * Kplus * (n - 1) / n ^ 2) /
        (Kminus * Kplus ^ 2 / (n * (Kplus + 1))) =
      1 + (Kminus - 1) / (n * Kplus) := by
  field_simp
  nlinarith

/-- The ratio error is at most `1/n` whenever the smaller capacity is no
larger than the larger capacity. -/
theorem flatK_frontier_ratio_error_le
    (n Kminus Kplus : ℝ)
    (hn : 0 < n) (hKplus : 0 < Kplus)
    (hsmall : Kminus ≤ Kplus) (hKminus : 1 ≤ Kminus) :
    0 ≤ (Kminus - 1) / (n * Kplus) ∧
      (Kminus - 1) / (n * Kplus) ≤ 1 / n := by
  constructor
  · positivity
  · rw [div_le_div_iff₀ (mul_pos hn hKplus) hn]
    nlinarith

end SmoothingCliff.Frontier
