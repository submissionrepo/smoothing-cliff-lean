import SmoothingCliff.Basic

/-!
# Pricing extraction

Formalization of Proposition `prop:extraction`.  The economic comparison is a
finite-sum inequality.  A separate complete-lattice lemma records the final
supremum/infimum step, so the pointwise argument and the minimax order argument
are both explicit.
-/

namespace SmoothingCliff.Frontier

open scoped BigOperators

/-- Welfare of a finite allocation evaluated at an arbitrary score. -/
def scoreWelfare {ι : Type*} [Fintype ι]
    (score allocation : ι → ℝ) : ℝ :=
  ∑ i, score i * allocation i

/-- One-slot strict-priority welfare when `top` is a highest-valued agent. -/
def strictPriorityScore {ι : Type*} [Fintype ι]
    (slotWeight : ℝ) (score : ι → ℝ) (top : ι) : ℝ :=
  score top * slotWeight

/-- Pointwise core of Proposition `prop:extraction`: discounting a
non-decreasing external-transfer share can only reduce the welfare gap to
strict priority. -/
theorem extraction_gap_le
    {ι : Type*} [Fintype ι]
    (values allocation : ι → ℝ) (top : ι)
    (slotWeight lambda : ℝ) (phi : ℝ → ℝ)
    (hLambda : 0 ≤ lambda)
    (hValues : ∀ i, 0 ≤ values i)
    (hTop : ∀ i, values i ≤ values top)
    (hPhiMono : Monotone phi)
    (hPhiRange : ∀ v, 0 ≤ v → phi v ∈ Set.Icc (0 : ℝ) 1)
    (hAlloc : ∀ i, 0 ≤ allocation i)
    (hMass : ∑ i, allocation i ≤ slotWeight) :
    strictPriorityScore slotWeight
          (fun i => (1 - lambda * phi (values i)) * values i) top -
        scoreWelfare
          (fun i => (1 - lambda * phi (values i)) * values i) allocation ≤
      strictPriorityScore slotWeight values top -
        scoreWelfare values allocation := by
  have hExtractNonneg : 0 ≤ phi (values top) * values top :=
    mul_nonneg (hPhiRange _ (hValues top)).1 (hValues top)
  have hEach : ∀ i, phi (values i) * values i ≤
      phi (values top) * values top := by
    intro i
    calc
      phi (values i) * values i ≤ phi (values i) * values top :=
        mul_le_mul_of_nonneg_left (hTop i) (hPhiRange _ (hValues i)).1
      _ ≤ phi (values top) * values top :=
        mul_le_mul_of_nonneg_right (hPhiMono (hTop i)) (hValues top)
  have hSum :
      ∑ i, (phi (values i) * values i) * allocation i ≤
        (phi (values top) * values top) * slotWeight := by
    calc
      ∑ i, (phi (values i) * values i) * allocation i ≤
          ∑ i, (phi (values top) * values top) * allocation i := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hEach i) (hAlloc i)
      _ = (phi (values top) * values top) * ∑ i, allocation i := by
        rw [Finset.mul_sum]
      _ ≤ (phi (values top) * values top) * slotWeight :=
        mul_le_mul_of_nonneg_left hMass hExtractNonneg
  have hScaled := mul_le_mul_of_nonneg_left hSum hLambda
  have hWeighted :
      ∑ i, ((1 - lambda * phi (values i)) * values i) * allocation i =
        ∑ i, values i * allocation i -
          lambda * ∑ i, (phi (values i) * values i) * allocation i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [strictPriorityScore, scoreWelfare]
  rw [hWeighted]
  ring_nf at hScaled ⊢
  linarith

/-- The purely order-theoretic step used after the pointwise comparison:
taking the worst profile and then the best rule preserves domination. -/
theorem minimax_loss_mono
    {Rule Profile L : Type*} [CompleteLattice L]
    (discounted undiscounted : Rule → Profile → L)
    (h : ∀ x p, discounted x p ≤ undiscounted x p) :
    (⨅ x, ⨆ p, discounted x p) ≤
      ⨅ x, ⨆ p, undiscounted x p := by
  apply iInf_mono
  intro x
  exact iSup_mono (h x)

/-- If the extraction share is constant, the strict-priority welfare gap is
scaled exactly by `1 - lambda * phi0`. -/
theorem constant_extraction_gap
    {ι : Type*} [Fintype ι]
    (values allocation : ι → ℝ) (top : ι)
    (slotWeight lambda phi0 : ℝ) :
    strictPriorityScore slotWeight
          (fun i => (1 - lambda * phi0) * values i) top -
        scoreWelfare (fun i => (1 - lambda * phi0) * values i) allocation =
      (1 - lambda * phi0) *
        (strictPriorityScore slotWeight values top -
          scoreWelfare values allocation) := by
  have hsum :
      (∑ i, ((1 - lambda * phi0) * values i) * allocation i) =
        (1 - lambda * phi0) * ∑ i, values i * allocation i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [strictPriorityScore, scoreWelfare]
  rw [hsum]
  ring

end SmoothingCliff.Frontier
