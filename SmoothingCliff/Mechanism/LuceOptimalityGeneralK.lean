import SmoothingCliff.Mechanism.LuceOptimality
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic

/-!
# General-slot Luce optimality by a common-clock coupling

This file gives the general-`K` part of `P_luceopt`.  A finite sequential Luce
ranking is represented by the standard exponential-race construction: attach
one positive common clock to every bidder and sort `clock i / intensity i`.
The bidder index is a deterministic tie breaker.

The main deterministic coupling theorem says that multiplying intensities by
a positive factor comonotone with value increases the value sum in every
top-`k` prefix, for every positive clock realization.  Thus stochastic
dominance is a conclusion, not a premise.  Abel summation then lifts all prefix
inequalities to arbitrary nonincreasing nonnegative slot weights.  Since the
coupling is pointwise, integration works for every probability law on positive
clocks, in particular the iid unit-exponential law defining sequential Luce.
-/

open scoped BigOperators ENNReal
open SmoothingCliff.LuceOptimality

namespace SmoothingCliff.LuceOptimalityGeneralK

/-- Stable race key.  The second coordinate is only a deterministic tie
breaker; under iid exponential clocks ties have probability zero. -/
noncomputable def raceKey {ι : Type*} [LinearOrder ι]
    (clock intensity : ι → ℝ) (i : ι) : Lex (ℝ × ι) :=
  toLex (clock i / intensity i, i)

/-- The linear order on bidders induced by their stable race keys. -/
@[reducible] noncomputable def raceOrder {ι : Type*} [LinearOrder ι]
    (clock intensity : ι → ℝ) : LinearOrder ι :=
  LinearOrder.lift' (raceKey clock intensity) (by
    intro i j h
    exact congrArg (fun z => (ofLex z).2) h)

/-- Finite sequential Luce ranking in common exponential-clock form.  Sorting
the complete race produces a without-replacement ranking. -/
noncomputable def sequentialLuceRanking
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) : List ι :=
  letI := raceOrder clock intensity
  Finset.univ.sort (fun i j => i ≤ j)

theorem sequentialLuceRanking_nodup
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) :
    (sequentialLuceRanking clock intensity).Nodup := by
  unfold sequentialLuceRanking
  letI := raceOrder clock intensity
  exact Finset.sort_nodup _ _

theorem mem_sequentialLuceRanking
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) (i : ι) :
    i ∈ sequentialLuceRanking clock intensity := by
  unfold sequentialLuceRanking
  letI := raceOrder clock intensity
  exact (Finset.mem_sort _).2 (Finset.mem_univ i)

theorem sequentialLuceRanking_length
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) :
    (sequentialLuceRanking clock intensity).length = Fintype.card ι := by
  unfold sequentialLuceRanking
  letI := raceOrder clock intensity
  exact Finset.length_sort (s := Finset.univ) (fun i j : ι => i ≤ j)

theorem sequentialLuceRanking_pairwise
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) :
    List.Pairwise (fun i j => raceKey clock intensity i ≤
      raceKey clock intensity j) (sequentialLuceRanking clock intensity) := by
  unfold sequentialLuceRanking
  letI := raceOrder clock intensity
  change List.Pairwise (fun i j : ι => i ≤ j)
    (Finset.univ.sort (fun i j : ι => i ≤ j))
  exact Finset.pairwise_sort _ _

/-- The set of bidders in the first `k` positions of the sequential ranking. -/
noncomputable def sequentialLuceTopK
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) (k : ℕ) : Finset ι :=
  ((sequentialLuceRanking clock intensity).take k).toFinset

theorem sequentialLuceTopK_card
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) (k : ℕ) :
    (sequentialLuceTopK clock intensity k).card =
      min k (Fintype.card ι) := by
  rw [sequentialLuceTopK,
    List.toFinset_card_of_nodup
      (sequentialLuceRanking_nodup clock intensity).take,
    List.length_take]
  congr 1
  exact sequentialLuceRanking_length clock intensity

theorem raceKey_le_of_mem_topK_of_not_mem
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity : ι → ℝ) (k : ℕ) {i j : ι}
    (hi : i ∈ sequentialLuceTopK clock intensity k)
    (hj : j ∉ sequentialLuceTopK clock intensity k) :
    raceKey clock intensity i ≤ raceKey clock intensity j := by
  have hiTake : i ∈ (sequentialLuceRanking clock intensity).take k := by
    simpa [sequentialLuceTopK] using hi
  have hjNotTake : j ∉ (sequentialLuceRanking clock intensity).take k := by
    simpa [sequentialLuceTopK] using hj
  have hjAll : j ∈ sequentialLuceRanking clock intensity :=
    mem_sequentialLuceRanking clock intensity j
  have hjAppend : j ∈ (sequentialLuceRanking clock intensity).take k ++
      (sequentialLuceRanking clock intensity).drop k := by
    rw [List.take_append_drop]
    exact hjAll
  have hjDrop : j ∈ (sequentialLuceRanking clock intensity).drop k := by
    simp only [List.mem_append] at hjAppend
    exact hjAppend.resolve_left hjNotTake
  exact (sequentialLuceRanking_pairwise clock intensity).rel_of_mem_take_of_mem_drop
    hiTake hjDrop

/-- A crossing pair under a positive multiplicative tilt must have a strictly
larger tilt factor on the bidder entering the prefix. -/
private theorem crossing_tilt_strict
    {ι : Type*} [LinearOrder ι]
    (clock base tilt : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (hclock : ∀ z, 0 < clock z)
    (hbase : ∀ z, 0 < base z) (htilt : ∀ z, 0 < tilt z)
    (hOld : raceKey clock base i ≤ raceKey clock base j)
    (hNew : raceKey clock (fun z => base z * tilt z) j ≤
      raceKey clock (fun z => base z * tilt z) i) :
    tilt i < tilt j := by
  have hOldLex := Prod.Lex.toLex_le_toLex'.mp hOld
  have hxy : clock i / base i ≤ clock j / base j := hOldLex.1
  have hNewLex := Prod.Lex.toLex_le_toLex'.mp hNew
  have hDiv : (clock j / base j) / tilt j ≤
      (clock i / base i) / tilt i := by
    simpa [raceKey, div_div] using hNewLex.1
  have hx : 0 < clock i / base i := div_pos (hclock i) (hbase i)
  have hle : tilt i ≤ tilt j := by
    by_contra hn
    have hji : tilt j < tilt i := lt_of_not_ge hn
    have hCross : (clock j / base j) * tilt i ≤
        (clock i / base i) * tilt j :=
      (div_le_div_iff₀ (htilt j) (htilt i)).mp hDiv
    have hContra : (clock i / base i) * tilt j <
        (clock j / base j) * tilt i := calc
      (clock i / base i) * tilt j < (clock i / base i) * tilt i :=
        mul_lt_mul_of_pos_left hji hx
      _ ≤ (clock j / base j) * tilt i :=
        mul_le_mul_of_nonneg_right hxy (htilt i).le
    exact (not_lt_of_ge hCross) hContra
  apply lt_of_le_of_ne hle
  intro heq
  have hDiv' : (clock j / base j) / tilt j ≤
      (clock i / base i) / tilt j := by
    simpa [heq] using hDiv
  have hyx : clock j / base j ≤ clock i / base i :=
    (div_le_div_iff_of_pos_right (htilt j)).mp hDiv'
  have hScalar : clock i / base i = clock j / base j :=
    le_antisymm hxy hyx
  have hijLe : i ≤ j := hOldLex.2 hScalar
  have hScaled : clock j / (base j * tilt j) =
      clock i / (base i * tilt i) := by
    rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div]
    rw [← hScalar, heq]
  have hjiLe : j ≤ i := hNewLex.2 hScaled
  exact hij (le_antisymm hijLe hjiLe)

private theorem sum_le_sum_of_card_eq_of_cross
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (value : ι → ℝ) (hcard : A.card = B.card)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, value i ≤ value j) :
    ∑ i ∈ A, value i ≤ ∑ j ∈ B, value j := by
  let e : {x // x ∈ A} ≃ {x // x ∈ B} :=
    Fintype.equivOfCardEq (by simpa using hcard)
  rw [Finset.sum_subtype A (fun _ => Iff.rfl) value,
    Finset.sum_subtype B (fun _ => Iff.rfl) value]
  calc
    ∑ x : {x // x ∈ A}, value x ≤
        ∑ x : {x // x ∈ A}, value (e x) := by
      exact Finset.sum_le_sum fun x _ =>
        hcross x x.property (e x) (e x).property
    _ = ∑ y : {x // x ∈ B}, value y :=
      e.sum_comp (fun y => value y)

/-- Common-clock top-`k` dominance.  This is the coupling core of the general
`K` result: every realized prefix has weakly larger total value after a
positive tilt comonotone with value. -/
theorem topK_value_sum_tilt_mono
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock base tilt value : ι → ℝ) (k : ℕ)
    (hclock : ∀ i, 0 < clock i)
    (hbase : ∀ i, 0 < base i) (htilt : ∀ i, 0 < tilt i)
    (hcomonotone : Monovary value tilt) :
    ∑ i ∈ sequentialLuceTopK clock base k, value i ≤
      ∑ i ∈ sequentialLuceTopK clock (fun i => base i * tilt i) k,
        value i := by
  let S := sequentialLuceTopK clock base k
  let T := sequentialLuceTopK clock (fun i => base i * tilt i) k
  have hcard : S.card = T.card := by
    dsimp [S, T]
    rw [sequentialLuceTopK_card, sequentialLuceTopK_card]
  have hdiffCard : (S \ T).card = (T \ S).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, hcard]
    rw [Finset.inter_comm]
  have hcross : ∀ i ∈ S \ T, ∀ j ∈ T \ S, value i ≤ value j := by
    intro i hi j hj
    have hiS : i ∈ S := (Finset.mem_sdiff.mp hi).1
    have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
    have hjT : j ∈ T := (Finset.mem_sdiff.mp hj).1
    have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hiT hjT
    have hOld : raceKey clock base i ≤ raceKey clock base j :=
      raceKey_le_of_mem_topK_of_not_mem clock base k hiS hjS
    have hNew : raceKey clock (fun z => base z * tilt z) j ≤
        raceKey clock (fun z => base z * tilt z) i :=
      raceKey_le_of_mem_topK_of_not_mem clock
        (fun z => base z * tilt z) k hjT hiT
    exact hcomonotone
      (crossing_tilt_strict clock base tilt hij hclock hbase htilt hOld hNew)
  have hdiffSum : ∑ i ∈ S \ T, value i ≤ ∑ j ∈ T \ S, value j :=
    sum_le_sum_of_card_eq_of_cross (S \ T) (T \ S) value
      hdiffCard hcross
  have hS : ∑ i ∈ S, value i =
      (∑ i ∈ S \ T, value i) + ∑ i ∈ S ∩ T, value i := by
    have h := Finset.sum_sdiff (f := value)
      (Finset.inter_subset_left : S ∩ T ⊆ S)
    rw [show S \ (S ∩ T) = S \ T by ext; simp] at h
    exact h.symm
  have hT : ∑ i ∈ T, value i =
      (∑ i ∈ T \ S, value i) + ∑ i ∈ S ∩ T, value i := by
    have h := Finset.sum_sdiff (f := value)
      (Finset.inter_subset_right : S ∩ T ⊆ T)
    rw [show T \ (S ∩ T) = T \ S by ext; simp] at h
    exact h.symm
  dsimp [S, T] at hS hT ⊢
  rw [hS, hT]
  simpa [add_comm] using
    add_le_add_right hdiffSum
      (∑ i ∈ sequentialLuceTopK clock base k ∩
        sequentialLuceTopK clock (fun i => base i * tilt i) k, value i)

/-- Value at a rank, padded by zero beyond the finite ranking. -/
noncomputable def rankValueAt {ι : Type*}
    (ranking : List ι) (value : ι → ℝ) (rank : ℕ) : ℝ :=
  if h : rank < ranking.length then value (ranking.get ⟨rank, h⟩) else 0

private theorem sum_range_rankValueAt_eq
    {ι : Type*} (ranking : List ι) (value : ι → ℝ)
    (k : ℕ) (hk : k ≤ ranking.length) :
    (∑ t ∈ Finset.range k, rankValueAt ranking value t) =
      ((ranking.take k).map value).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkl : k < ranking.length := Nat.lt_of_succ_le hk
      rw [Finset.sum_range_succ, ih hkl.le]
      rw [show ((ranking.take (k + 1)).map value).sum =
          ((ranking.map value).take (k + 1)).sum by simp]
      rw [List.sum_take_succ (ranking.map value) k (by simpa using hkl)]
      simp [rankValueAt, hkl]

theorem topK_value_sum_eq_range
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity value : ι → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card ι) :
    (∑ i ∈ sequentialLuceTopK clock intensity k, value i) =
      ∑ t ∈ Finset.range k,
        rankValueAt (sequentialLuceRanking clock intensity) value t := by
  rw [sequentialLuceTopK,
    List.sum_toFinset value
      (sequentialLuceRanking_nodup clock intensity).take]
  symm
  apply sum_range_rankValueAt_eq
  simpa [sequentialLuceRanking_length] using hk

/-- Nonincreasing nonnegative slot weights, extended by zero at and after the
cutoff `K`.  Antitonicity and nonnegativity force the zero extension once
`weight K = 0`. -/
def AdmissibleSlotWeights (K : ℕ) (weight : ℕ → ℝ) : Prop :=
  Antitone weight ∧ (∀ t, 0 ≤ weight t) ∧ weight K = 0

/-- Direct total welfare of the first `K` positions in a realized sequential
Luce ranking. -/
noncomputable def sequentialLuceWelfare
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity value : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ Finset.range K, weight t *
    rankValueAt (sequentialLuceRanking clock intensity) value t

/-- Finite Abel summation with its boundary term. -/
theorem abel_sum_identity (x weight : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K,
      (weight k - weight (k + 1)) *
        (∑ t ∈ Finset.range (k + 1), x t)) =
      (∑ t ∈ Finset.range K, weight t * x t) -
        weight K * (∑ t ∈ Finset.range K, x t) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      ring

/-- Abel representation of realized total sequential-Luce welfare in terms of
top-prefix value sums. -/
theorem sequentialLuceWelfare_abel
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock intensity value : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ)
    (hK : K ≤ Fintype.card ι) (hzero : weight K = 0) :
    sequentialLuceWelfare clock intensity value weight K =
      ∑ k ∈ Finset.range K, (weight k - weight (k + 1)) *
        (∑ i ∈ sequentialLuceTopK clock intensity (k + 1), value i) := by
  let x : ℕ → ℝ :=
    rankValueAt (sequentialLuceRanking clock intensity) value
  have hAbel := abel_sum_identity x weight K
  rw [hzero, zero_mul, sub_zero] at hAbel
  rw [sequentialLuceWelfare]
  change (∑ t ∈ Finset.range K, weight t * x t) = _
  rw [← hAbel]
  apply Finset.sum_congr rfl
  intro k hk
  have hkK : k + 1 ≤ K := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
  rw [topK_value_sum_eq_range clock intensity value (k + 1)
    (hkK.trans hK)]

/-- General-`K` common-clock welfare dominance under an increasing positive
multiplicative tilt. -/
theorem sequentialLuceWelfare_tilt_mono
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clock base tilt value : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ)
    (hK : K ≤ Fintype.card ι)
    (hclock : ∀ i, 0 < clock i)
    (hbase : ∀ i, 0 < base i) (htilt : ∀ i, 0 < tilt i)
    (hcomonotone : Monovary value tilt)
    (hweight : AdmissibleSlotWeights K weight) :
    sequentialLuceWelfare clock base value weight K ≤
      sequentialLuceWelfare clock (fun i => base i * tilt i)
        value weight K := by
  rw [sequentialLuceWelfare_abel clock base value weight K hK hweight.2.2,
    sequentialLuceWelfare_abel clock (fun i => base i * tilt i)
      value weight K hK hweight.2.2]
  apply Finset.sum_le_sum
  intro k hk
  have hcoef : 0 ≤ weight k - weight (k + 1) :=
    sub_nonneg.mpr (hweight.1 (Nat.le_succ k))
  exact mul_le_mul_of_nonneg_left
    (topK_value_sum_tilt_mono clock base tilt value (k + 1)
      hclock hbase htilt hcomonotone) hcoef

/-- Full profile-by-profile general-`K` conclusion for the paper's exponential
intensity. -/
theorem exponential_sequentialLuceWelfare_optimal
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (reserve τ : ℝ) (value : ι → ℝ) (α dα : ℝ → ℝ)
    (clock : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ)
    (htau : 0 < τ) (hK : K ≤ Fintype.card ι)
    (heligible : ∀ i, reserve ≤ value i)
    (hclock : ∀ i, 0 < clock i)
    (hI : EligibleC1Intensity reserve τ α dα)
    (hweight : AdmissibleSlotWeights K weight) :
    sequentialLuceWelfare clock (fun i => α (value i)) value weight K ≤
      sequentialLuceWelfare clock
        (fun i => exponentialIntensity reserve τ (value i))
        value weight K := by
  let base : ι → ℝ := fun i => α (value i)
  let tilt : ι → ℝ := fun i =>
    relativeExponentialTilt reserve τ α (value i)
  have hbase : ∀ i, 0 < base i := fun i =>
    hI.2.2.1 (value i) (heligible i)
  have htilt : ∀ i, 0 < tilt i := fun i =>
    relativeExponentialTilt_pos reserve τ α dα hI (heligible i)
  have hcomonotone : Monovary value tilt := by
    intro i j htij
    by_contra hvij
    have hvji : value j ≤ value i := (not_le.mp hvij).le
    have htji : tilt j ≤ tilt i :=
      relativeExponentialTilt_mono reserve τ α dα htau hI
        (heligible j) hvji
    exact (not_lt_of_ge htji) htij
  have hWelfare := sequentialLuceWelfare_tilt_mono
    clock base tilt value weight K hK hclock hbase htilt hcomonotone hweight
  have hproduct : (fun i => base i * tilt i) =
      (fun i => exponentialIntensity reserve τ (value i)) := by
    funext i
    dsimp [base, tilt, relativeExponentialTilt]
    have hne : α (value i) ≠ 0 :=
      ne_of_gt (hI.2.2.1 (value i) (heligible i))
    field_simp
  rw [hproduct] at hWelfare
  simpa [base] using hWelfare

/-- Strictly positive clock values remove the null tie-at-zero issue from the
pointwise coupling. -/
abbrev StrictlyPositiveReal := {x : ℝ // 0 < x}

abbrev PositiveClockProfile (ι : Type*) := ι → StrictlyPositiveReal

/-- Repair the null nonpositive part of a real exponential clock to a fixed
positive value. -/
noncomputable def repairPositiveClock (x : ℝ) : StrictlyPositiveReal :=
  if hx : 0 < x then ⟨x, hx⟩ else ⟨1, zero_lt_one⟩

theorem measurable_repairPositiveClock : Measurable repairPositiveClock := by
  let f : ℝ → ℝ := fun x => if 0 < x then x else 1
  have hf : Measurable f := by
    exact Measurable.ite measurableSet_Ioi measurable_id measurable_const
  have hp : ∀ x, 0 < f x := by
    intro x
    simp only [f]
    split
    · assumption
    · exact zero_lt_one
  have hm : Measurable
      (fun x => (⟨f x, hp x⟩ : StrictlyPositiveReal)) := hf.subtype_mk
  convert hm using 1
  funext x
  apply Subtype.ext
  by_cases hx : 0 < x <;> simp [repairPositiveClock, f, hx]

/-- Unit exponential probability measure on the real line. -/
noncomputable def unitExponentialProbability :
    MeasureTheory.ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.expMeasure 1,
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos⟩

/-- Unit exponential clock pushed to the strictly positive clock space.  The
repair only changes the null nonpositive part of the exponential density. -/
noncomputable def positiveUnitExponentialProbability :
    MeasureTheory.ProbabilityMeasure StrictlyPositiveReal :=
  unitExponentialProbability.map measurable_repairPositiveClock.aemeasurable

/-- The concrete iid unit-exponential common-clock law for a finite profile. -/
noncomputable def iidUnitExponentialClockLaw
    (ι : Type*) [Fintype ι] :
    MeasureTheory.ProbabilityMeasure (PositiveClockProfile ι) :=
  MeasureTheory.ProbabilityMeasure.pi
    (fun _ => positiveUnitExponentialProbability)

/-- Extended expected welfare under a common probability law on positive
clocks.  Taking the iid unit-exponential law gives the usual sequential Luce
expected welfare. -/
noncomputable def expectedSequentialLuceWelfare
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clockLaw : MeasureTheory.ProbabilityMeasure (PositiveClockProfile ι))
    (intensity value : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ) : ENNReal :=
  ∫⁻ clock, ENNReal.ofReal
    (sequentialLuceWelfare (fun i => (clock i : ℝ)) intensity
      value weight K) ∂(clockLaw : MeasureTheory.Measure (PositiveClockProfile ι))

/-- Expected general-`K` dominance follows by integrating the pointwise common
clock coupling; no stochastic-order premise is used. -/
theorem expectedSequentialLuceWelfare_tilt_mono
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clockLaw : MeasureTheory.ProbabilityMeasure (PositiveClockProfile ι))
    (base tilt value : ι → ℝ) (weight : ℕ → ℝ) (K : ℕ)
    (hK : K ≤ Fintype.card ι)
    (hbase : ∀ i, 0 < base i) (htilt : ∀ i, 0 < tilt i)
    (hcomonotone : Monovary value tilt)
    (hweight : AdmissibleSlotWeights K weight) :
    expectedSequentialLuceWelfare clockLaw base value weight K ≤
      expectedSequentialLuceWelfare clockLaw (fun i => base i * tilt i)
        value weight K := by
  apply MeasureTheory.lintegral_mono
  intro clock
  apply ENNReal.ofReal_le_ofReal
  exact sequentialLuceWelfare_tilt_mono
    (fun i => (clock i : ℝ)) base tilt value weight K hK
    (fun i => (clock i).property) hbase htilt hcomonotone hweight

/-- General-`K` expected-welfare form of `P_luceopt`.  It holds for every
common positive-clock law, hence in particular for iid unit exponentials. -/
theorem exponential_expectedSequentialLuceWelfare_optimal
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (clockLaw : MeasureTheory.ProbabilityMeasure (PositiveClockProfile ι))
    (reserve τ : ℝ) (value : ι → ℝ) (α dα : ℝ → ℝ)
    (weight : ℕ → ℝ) (K : ℕ)
    (htau : 0 < τ) (hK : K ≤ Fintype.card ι)
    (heligible : ∀ i, reserve ≤ value i)
    (hI : EligibleC1Intensity reserve τ α dα)
    (hweight : AdmissibleSlotWeights K weight) :
    expectedSequentialLuceWelfare clockLaw (fun i => α (value i))
        value weight K ≤
      expectedSequentialLuceWelfare clockLaw
        (fun i => exponentialIntensity reserve τ (value i))
        value weight K := by
  apply MeasureTheory.lintegral_mono
  intro clock
  apply ENNReal.ofReal_le_ofReal
  exact exponential_sequentialLuceWelfare_optimal reserve τ value α dα
    (fun i => (clock i : ℝ)) weight K htau hK heligible
    (fun i => (clock i).property) hI hweight

/-- `P_luceopt` under the concrete iid unit-exponential race law. -/
theorem exponential_iidUnitExponential_expectedWelfare_optimal
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (reserve τ : ℝ) (value : ι → ℝ) (α dα : ℝ → ℝ)
    (weight : ℕ → ℝ) (K : ℕ)
    (htau : 0 < τ) (hK : K ≤ Fintype.card ι)
    (heligible : ∀ i, reserve ≤ value i)
    (hI : EligibleC1Intensity reserve τ α dα)
    (hweight : AdmissibleSlotWeights K weight) :
    expectedSequentialLuceWelfare (iidUnitExponentialClockLaw ι)
        (fun i => α (value i)) value weight K ≤
      expectedSequentialLuceWelfare (iidUnitExponentialClockLaw ι)
        (fun i => exponentialIntensity reserve τ (value i))
        value weight K :=
  exponential_expectedSequentialLuceWelfare_optimal
    (iidUnitExponentialClockLaw ι) reserve τ value α dα weight K
      htau hK heligible hI hweight

end SmoothingCliff.LuceOptimalityGeneralK
