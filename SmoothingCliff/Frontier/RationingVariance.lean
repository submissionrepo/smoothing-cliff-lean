import SmoothingCliff.Frontier.RationedRamp

/-!
# The independence input behind the rationing rate

The achievability bound of Theorem `thm:meanfield` (iii) carries a
second-moment premise: the expected squared excess of the total ramp response
over the capacity is at most `n w₁² / 4`.  In the paper that premise is
independence -- the responses are iid and lie in `[0, w₁]`, so the variance of
their sum is `n` times a variance bounded by `w₁² / 4`.  This file supplies it:
the iid product of a finite law, its two marginal identities, the Popoviciu
bound, and the variance bound they give, so that the premise is a theorem
rather than a hypothesis once the responses are iid.
-/

namespace SmoothingCliff.Frontier

open SmoothingCliff

noncomputable section

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Elementary facts about finite expectations -/

theorem finiteExpectation_const {α : Type*} [Fintype α] (law : FiniteLaw α) (c : ℝ) :
    finiteExpectation law (fun _ => c) = c := by
  unfold finiteExpectation
  rw [← Finset.sum_mul, law.probability_sum, one_mul]

theorem finiteExpectation_congr {α : Type*} [Fintype α] (law : FiniteLaw α)
    {f g : α → ℝ} (h : ∀ a, f a = g a) :
    finiteExpectation law f = finiteExpectation law g :=
  Finset.sum_congr rfl fun a _ => by rw [h a]

theorem finiteExpectation_add {α : Type*} [Fintype α] (law : FiniteLaw α) (f g : α → ℝ) :
    finiteExpectation law (fun a => f a + g a)
      = finiteExpectation law f + finiteExpectation law g := by
  unfold finiteExpectation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem finiteExpectation_smul {α : Type*} [Fintype α] (law : FiniteLaw α) (c : ℝ)
    (f : α → ℝ) :
    finiteExpectation law (fun a => c * f a) = c * finiteExpectation law f := by
  unfold finiteExpectation
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem finiteExpectation_mono {α : Type*} [Fintype α] (law : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteExpectation law f ≤ finiteExpectation law g :=
  Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (h a) (law.probability_nonneg a)

omit [Fintype ι] in
theorem finiteExpectation_sum {α : Type*} [Fintype α] (law : FiniteLaw α)
    (s : Finset ι) (f : ι → α → ℝ) :
    finiteExpectation law (fun a => ∑ i ∈ s, f i a)
      = ∑ i ∈ s, finiteExpectation law (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [finiteExpectation]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ← ih, ← finiteExpectation_add]
    exact Finset.sum_congr rfl fun a _ => by dsimp only; rw [Finset.sum_insert hi]

/-- Popoviciu on a finite law: a variable in `[0, w]` has variance at most
`w² / 4`. -/
theorem finiteExpectation_sq_sub_le {α : Type*} [Fintype α] (law : FiniteLaw α)
    {w : ℝ} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a) (hub : ∀ a, f a ≤ w) :
    finiteExpectation law (fun a => (f a - finiteExpectation law f) ^ 2)
      ≤ w ^ 2 / 4 := by
  set μ : ℝ := finiteExpectation law f with hμ
  have hexpand : finiteExpectation law (fun a => (f a - μ) ^ 2)
      = finiteExpectation law (fun a => f a * f a) - μ ^ 2 := by
    have h1 : ∀ a, (f a - μ) ^ 2 = f a * f a + (-(2 * μ)) * f a + μ ^ 2 := by
      intro a; ring
    calc finiteExpectation law (fun a => (f a - μ) ^ 2)
        = finiteExpectation law (fun a => (f a * f a + (-(2 * μ)) * f a) + μ ^ 2) := by
          unfold finiteExpectation
          exact Finset.sum_congr rfl fun a _ => by dsimp only; rw [h1 a]
      _ = finiteExpectation law (fun a => f a * f a + (-(2 * μ)) * f a) + μ ^ 2 := by
          rw [finiteExpectation_add law (fun a => f a * f a + (-(2 * μ)) * f a)
            (fun _ => μ ^ 2), finiteExpectation_const]
      _ = finiteExpectation law (fun a => f a * f a)
            + (-(2 * μ)) * finiteExpectation law f + μ ^ 2 := by
          rw [finiteExpectation_add law (fun a => f a * f a) (fun a => (-(2 * μ)) * f a),
            finiteExpectation_smul]
      _ = finiteExpectation law (fun a => f a * f a) - μ ^ 2 := by rw [← hμ]; ring
  have hsq : finiteExpectation law (fun a => f a * f a) ≤ w * μ := by
    have := finiteExpectation_mono law (f := fun a => f a * f a) (g := fun a => w * f a)
      (fun a => mul_le_mul_of_nonneg_right (hub a) (h0 a))
    rwa [finiteExpectation_smul, ← hμ] at this
  have hμ0 : 0 ≤ μ := by
    rw [hμ]
    have := finiteExpectation_mono law (f := fun _ => (0 : ℝ)) (g := f) h0
    rwa [finiteExpectation_const] at this
  have hμw : μ ≤ w := by
    rw [hμ]
    have := finiteExpectation_mono law (f := f) (g := fun _ => w) hub
    rwa [finiteExpectation_const] at this
  rw [hexpand]
  nlinarith [sq_nonneg (w - 2 * μ)]

/-! ### The iid product law -/

/-- The iid product of a finite law over the agents. -/
def productLaw (law : FiniteLaw Ω) : FiniteLaw (ι → Ω) where
  probability := fun ω => ∏ i, law.probability (ω i)
  probability_nonneg := fun ω =>
    Finset.prod_nonneg fun i _ => law.probability_nonneg (ω i)
  probability_sum := by
    have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Ω))
      (fun (_ : ι) (a : Ω) => law.probability a)
    rw [Fintype.piFinset_univ] at h
    simp only [law.probability_sum, Finset.prod_const_one] at h
    exact h.symm

omit [DecidableEq Ω] in
/-- Marginal identity: a function of one coordinate integrates to the law's
own expectation. -/
theorem finiteExpectation_productLaw_single (law : FiniteLaw Ω) (i : ι) (h : Ω → ℝ) :
    finiteExpectation (productLaw (ι := ι) law) (fun ω => h (ω i))
      = finiteExpectation law h := by
  classical
  have habsorb : ∀ ω : ι → Ω,
      (∏ j, law.probability (ω j)) * h (ω i)
        = ∏ j, (if j = i then law.probability (ω j) * h (ω j)
            else law.probability (ω j)) := by
    intro ω
    rw [← Finset.mul_prod_erase Finset.univ
        (fun j => if j = i then law.probability (ω j) * h (ω j)
          else law.probability (ω j)) (Finset.mem_univ i), if_pos rfl,
      Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1),
      ← Finset.mul_prod_erase Finset.univ (fun j => law.probability (ω j))
        (Finset.mem_univ i)]
    ring
  unfold finiteExpectation productLaw
  simp only
  rw [Finset.sum_congr rfl (fun ω _ => habsorb ω), ← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Ω))
      (fun (m : ι) (a : Ω) => if m = i then law.probability a * h a
        else law.probability a)]
  rw [Finset.prod_eq_single i]
  · simp only [if_pos]
  · intro j _ hj
    simp only [if_neg hj]
    exact law.probability_sum
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

omit [DecidableEq Ω] in
/-- Marginal identity for two distinct coordinates: the product factorizes. -/
theorem finiteExpectation_productLaw_pair (law : FiniteLaw Ω) {i j : ι} (hij : i ≠ j)
    (h k : Ω → ℝ) :
    finiteExpectation (productLaw (ι := ι) law) (fun ω => h (ω i) * k (ω j))
      = finiteExpectation law h * finiteExpectation law k := by
  classical
  set F : ι → Ω → ℝ := fun m a =>
    if m = i then law.probability a * h a
    else if m = j then law.probability a * k a
    else law.probability a with hF
  have habsorb : ∀ ω : ι → Ω,
      (∏ m, law.probability (ω m)) * (h (ω i) * k (ω j)) = ∏ m, F m (ω m) := by
    intro ω
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun m => law.probability (ω m))
        (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun m => law.probability (ω m)) hj_mem,
      ← Finset.mul_prod_erase Finset.univ (fun m => F m (ω m)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun m => F m (ω m)) hj_mem]
    have hFi : F i (ω i) = law.probability (ω i) * h (ω i) := by simp [hF]
    have hFj : F j (ω j) = law.probability (ω j) * k (ω j) := by simp [hF, Ne.symm hij]
    have hrest : ∀ m ∈ (Finset.univ.erase i).erase j, F m (ω m) = law.probability (ω m) := by
      intro m hm
      have h1 : m ≠ j := (Finset.mem_erase.mp hm).1
      have h2 : m ≠ i := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1
      simp [hF, h1, h2]
    rw [hFi, hFj, Finset.prod_congr rfl hrest]
    ring
  unfold finiteExpectation productLaw
  simp only
  rw [Finset.sum_congr rfl (fun ω _ => habsorb ω), ← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Ω)) F]
  have hsum : ∀ m : ι, ∑ a, F m a
      = if m = i then finiteExpectation law h
        else if m = j then finiteExpectation law k else 1 := by
    intro m
    by_cases h1 : m = i
    · rw [if_pos h1]
      have hpt : ∀ a, F m a = law.probability a * h a := by
        intro a; rw [hF]; simp [h1]
      rw [Finset.sum_congr rfl (fun a _ => hpt a)]
      rfl
    · rw [if_neg h1]
      by_cases h2 : m = j
      · rw [if_pos h2]
        have hpt : ∀ a, F m a = law.probability a * k a := by
          intro a; rw [hF]; simp [h2, Ne.symm hij]
        rw [Finset.sum_congr rfl (fun a _ => hpt a)]
        rfl
      · rw [if_neg h2]
        have hpt : ∀ a, F m a = law.probability a := by
          intro a; rw [hF]; simp [h1, h2]
        rw [Finset.sum_congr rfl (fun a _ => hpt a)]
        exact law.probability_sum
  rw [Finset.prod_congr rfl (fun m _ => hsum m)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
  rw [Finset.prod_congr rfl (fun m hm => by
    rw [if_neg (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1,
      if_neg (Finset.mem_erase.mp hm).1])]
  simp only [Finset.prod_const_one, mul_one]
  rfl

/-! ### The variance bound

The assembly below never unfolds `finiteExpectation` on the function space
`ι → Ω`: the integrand is rearranged pointwise by `finiteExpectation_congr`
and everything after that goes through linearity and the two marginal
identities.  Unfolding the product sum instead is what makes the elaborator
diverge, since the Fintype on `ι → Ω` has `|Ω| ^ |ι|` elements.
-/

omit [DecidableEq Ω] in
/-- The total response has `n` times the coordinate mean. -/
theorem productLaw_expectation_sum (law : FiniteLaw Ω) (f : Ω → ℝ) :
    finiteExpectation (productLaw (ι := ι) law) (fun ω => ∑ i, f (ω i))
      = Fintype.card ι * finiteExpectation law f := by
  rw [finiteExpectation_sum (productLaw (ι := ι) law) Finset.univ
    (fun i ω => f (ω i))]
  rw [Finset.sum_congr rfl (fun i _ =>
    finiteExpectation_productLaw_single (ι := ι) law i f)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq Ω] in
/-- **Independence gives the paper's second-moment certificate.**  If the
coordinate response lies in `[0, w]`, the total deviates from its mean by at
most `n w² / 4` in mean square. -/
theorem productLaw_sq_deviation_le (law : FiniteLaw Ω) {w : ℝ} {f : Ω → ℝ}
    (h0 : ∀ a, 0 ≤ f a) (hub : ∀ a, f a ≤ w) :
    finiteExpectation (productLaw (ι := ι) law)
        (fun ω => ((∑ i, f (ω i))
          - Fintype.card ι * finiteExpectation law f) ^ 2)
      ≤ Fintype.card ι * w ^ 2 / 4 := by
  classical
  set μ : ℝ := finiteExpectation law f with hμ
  set g : Ω → ℝ := fun a => f a - μ with hg
  have hcentered : finiteExpectation law g = 0 := by
    have hsplit : finiteExpectation law g
        = finiteExpectation law f + finiteExpectation law (fun _ => -μ) := by
      rw [← finiteExpectation_add law f (fun _ => -μ)]
      exact finiteExpectation_congr law fun a => by rw [hg]; ring
    rw [hsplit, finiteExpectation_const law (-μ), ← hμ]
    ring
  have hpointwise : ∀ ω : ι → Ω,
      ((∑ i, f (ω i)) - Fintype.card ι * μ) ^ 2
        = ∑ i, ∑ j, g (ω i) * g (ω j) := by
    intro ω
    have hsplit : (∑ i, f (ω i)) - Fintype.card ι * μ = ∑ i, g (ω i) := by
      rw [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [hsplit, sq, Finset.sum_mul_sum]
  have hexp : finiteExpectation (productLaw (ι := ι) law)
      (fun ω => ((∑ i, f (ω i)) - Fintype.card ι * μ) ^ 2)
      = ∑ i, ∑ j, finiteExpectation (productLaw (ι := ι) law)
          (fun ω => g (ω i) * g (ω j)) := by
    rw [finiteExpectation_congr (productLaw (ι := ι) law) hpointwise,
      finiteExpectation_sum (productLaw (ι := ι) law) Finset.univ
        (fun i ω => ∑ j, g (ω i) * g (ω j))]
    exact Finset.sum_congr rfl fun i _ =>
      finiteExpectation_sum (productLaw (ι := ι) law) Finset.univ
        (fun j ω => g (ω i) * g (ω j))
  have hdiag : ∀ i : ι,
      finiteExpectation (productLaw (ι := ι) law) (fun ω => g (ω i) * g (ω i))
        ≤ w ^ 2 / 4 := by
    intro i
    rw [finiteExpectation_productLaw_single (ι := ι) law i (fun a => g a * g a)]
    have hpop := finiteExpectation_sq_sub_le law h0 hub
    rw [← hμ] at hpop
    calc finiteExpectation law (fun a => g a * g a)
        = finiteExpectation law (fun a => (f a - μ) ^ 2) :=
          finiteExpectation_congr law fun a => by rw [hg]; ring
      _ ≤ w ^ 2 / 4 := hpop
  have hinner : ∀ i : ι, ∑ j, finiteExpectation (productLaw (ι := ι) law)
      (fun ω => g (ω i) * g (ω j)) ≤ w ^ 2 / 4 := by
    intro i
    rw [Finset.sum_eq_single i]
    · exact hdiag i
    · intro j _ hj
      rw [finiteExpectation_productLaw_pair law (Ne.symm hj) g g, hcentered,
        mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  rw [hexp]
  calc ∑ i, ∑ j, finiteExpectation (productLaw (ι := ι) law)
        (fun ω => g (ω i) * g (ω j))
      ≤ ∑ _i : ι, w ^ 2 / 4 := Finset.sum_le_sum fun i _ => hinner i
    _ = Fintype.card ι * w ^ 2 / 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [DecidableEq Ω] in
/-- The certificate in the shape the achievability theorem consumes: once the
threshold clears the capacity in expectation, the second-moment premise is a
theorem rather than a hypothesis. -/
theorem productLaw_sq_excess_le (law : FiniteLaw Ω) {w c : ℝ} {f : Ω → ℝ}
    (h0 : ∀ a, 0 ≤ f a) (hub : ∀ a, f a ≤ w)
    (hclears : finiteExpectation (productLaw (ι := ι) law)
      (fun ω => ∑ i, f (ω i)) = c) :
    finiteExpectation (productLaw (ι := ι) law)
        (fun ω => ((∑ i, f (ω i)) - c) ^ 2)
      ≤ Fintype.card ι * w ^ 2 / 4 := by
  rw [productLaw_expectation_sum (ι := ι) law f] at hclears
  rw [← hclears]
  exact productLaw_sq_deviation_le (ι := ι) law h0 hub

/-! ### The achievability bound with no second-moment premise -/

section Achievability

variable {reserve : ℝ}

/-- **The rationing rate under iid values.**  Instantiating the finite-law
achievability bound at the product law discharges its second-moment premise,
so the paper's `O(n^{-1/2})` statement stands on independence alone. -/
theorem rationedRampRule_iid_achievability {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty ι] (p : FiniteLaw V) (val : V → ℝ) (hval : ∀ v, reserve ≤ val v)
    (weight sensitivity : NNReal) (capacity threshold upperValue : ℝ)
    (hCapacity : 0 ≤ capacity) (hUpper : 0 ≤ upperValue)
    (hValueNonneg : ∀ v, 0 ≤ val v) (hValueLe : ∀ v, val v ≤ upperValue)
    (hThreshold : threshold ≤ upperValue)
    (hClears : finiteExpectation (productLaw (ι := ι) p)
      (fun ω => ∑ i, postedRamp weight sensitivity threshold (val (ω i))) = capacity) :
    finitePopulationValue (pooledLaw (ι := ι) (productLaw (ι := ι) p))
        (fun q => val (q.1 q.2)) weight sensitivity (capacity / (Fintype.card ι : ℝ))
      - upperValue * (weight : ℝ) / (4 * Real.sqrt (Fintype.card ι))
    ≤ finiteExpectation (productLaw (ι := ι) p) (fun ω =>
        welfare (rationedRampRule (reserve := reserve) weight sensitivity capacity threshold)
          (truthfulProfile (fun ω i => val (ω i)) (fun ω i => hval (ω i)) ω))
        / (Fintype.card ι : ℝ) := by
  have hSecond := productLaw_sq_excess_le (ι := ι) p
    (w := (weight : ℝ)) (c := capacity)
    (f := fun v => postedRamp weight sensitivity threshold (val v))
    (fun v => postedRamp_nonneg weight sensitivity threshold (val v))
    (fun v => postedRamp_le weight sensitivity threshold (val v)) hClears
  exact rationedRampRule_finiteLaw_achievability (productLaw (ι := ι) p)
    (fun ω i => val (ω i)) (fun ω i => hval (ω i)) weight sensitivity capacity
    threshold upperValue hCapacity hUpper (fun ω i => hValueNonneg (ω i))
    (fun ω i => hValueLe (ω i)) hThreshold hClears hSecond

end Achievability

end

end SmoothingCliff.Frontier
