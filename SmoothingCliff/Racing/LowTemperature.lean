import SmoothingCliff.Racing.RateContinuity
import SmoothingCliff.Mechanism.Revenue
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Concentration of the Plackett--Luce law at low temperature

The low-temperature clause of Proposition `prop:revenue`.  As the temperature
falls the reserve-adjusted intensities separate geometrically, and the
Plackett--Luce law concentrates on the single ranking that sorts the agents by
their rates.

The bound proved here is explicit rather than asymptotic.  If along the ranking
every later rate is at most a factor `K` of every earlier one, then the mass of
that ranking is at least `1 - n(n-1)/(2K)`: each of the `n` draws loses at most
the number of agents still competing, divided by `K`, and those counts sum to
`n(n-1)/2`.  Sending `K` to infinity gives the concentration.

The recursion reads the rates along the ranking, so the whole argument is a
statement about the sequence `rate` composed with the ranking; the two bridge
lemmas below are what turn `decomposeFin` into that sequence.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- The first agent the recursion draws is the ranking's first agent. -/
theorem decomposeFin_fst_eq {n : ℕ} (ranking : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.decomposeFin ranking).1 = ranking 0 := by
  conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply ranking]
  rw [Equiv.Perm.decomposeFin_symm_apply_zero]

/-- The tail rates read along the tail ranking are the original rates read
along the original ranking, shifted by one. -/
theorem removeChosenRate_tail_eq {n : ℕ} (rate : Fin (n + 1) → ℝ)
    (ranking : Equiv.Perm (Fin (n + 1))) (x : Fin n) :
    removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1
        ((Equiv.Perm.decomposeFin ranking).2 x) =
      rate (ranking x.succ) := by
  conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply ranking]
  rw [Equiv.Perm.decomposeFin_symm_apply_succ]
  rfl

/-- The first draw takes at least the share `1 - n/K` when every other rate is
a factor `K` below the leader's. -/
theorem leadShare_ge {n : ℕ} (rate : Fin (n + 1) → ℝ) (lead : Fin (n + 1))
    {K : ℝ} (hK : 0 < K) (hpos : ∀ i, 0 < rate i)
    (hdom : ∀ i, i ≠ lead → rate i * K ≤ rate lead) :
    1 - (n : ℝ) / K ≤ rate lead / ∑ i, rate i := by
  classical
  have hsumpos : 0 < ∑ i, rate i :=
    Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  have hlead := hpos lead
  have herase : ∑ i ∈ Finset.univ.erase lead, rate i ≤
      (n : ℝ) * (rate lead / K) := by
    have hcard : (Finset.univ.erase lead).card = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ lead), Finset.card_univ,
        Fintype.card_fin]
      rfl
    have hbound : ∀ i ∈ Finset.univ.erase lead, rate i ≤ rate lead / K := by
      intro i hi
      rw [le_div_iff₀ hK]
      exact hdom i (Finset.mem_erase.mp hi).1
    calc ∑ i ∈ Finset.univ.erase lead, rate i
        ≤ ∑ _i ∈ Finset.univ.erase lead, rate lead / K :=
          Finset.sum_le_sum hbound
      _ = (n : ℝ) * (rate lead / K) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hsplit : ∑ i, rate i =
      rate lead + ∑ i ∈ Finset.univ.erase lead, rate i :=
    (Finset.add_sum_erase Finset.univ rate (Finset.mem_univ lead)).symm
  have hshuffle : (n : ℝ) * (rate lead / K) = rate lead * ((n : ℝ) / K) := by
    ring
  have hsumle : ∑ i, rate i ≤ rate lead * (1 + (n : ℝ) / K) := by
    rw [hsplit, mul_add, mul_one]
    linarith [herase, hshuffle]
  have hshare : (0 : ℝ) ≤ (n : ℝ) / K := by positivity
  rw [le_div_iff₀ hsumpos]
  rcases le_or_gt ((n : ℝ) / K) 1 with hsmall | hbig
  · nlinarith [mul_le_mul_of_nonneg_left hsumle
      (by linarith : (0 : ℝ) ≤ 1 - (n : ℝ) / K), sq_nonneg ((n : ℝ) / K),
      hlead]
  · nlinarith [hsumpos, hlead]

/-- **The concentration bound.**  If along the ranking every later rate is a
factor `K` below every earlier one, the ranking carries all but
`n(n-1)/(2K)` of the mass. -/
theorem plPermutationMass_ge_of_separated :
    ∀ (n : ℕ) (rate : Fin n → ℝ) (ranking : Equiv.Perm (Fin n)) (K : ℝ),
      0 < K → (∀ i, 0 < rate i) →
      (∀ k l : Fin n, k < l → rate (ranking l) * K ≤ rate (ranking k)) →
      1 - (n : ℝ) * ((n : ℝ) - 1) / (2 * K) ≤
        plPermutationMass n rate ranking := by
  intro n
  induction n with
  | zero =>
    intro rate ranking K hK _ _
    simp [plPermutationMass]
  | succ m ih =>
    intro rate ranking K hK hpos hsep
    classical
    have hlead : (Equiv.Perm.decomposeFin ranking).1 = ranking 0 :=
      decomposeFin_fst_eq ranking
    have hsumpos : 0 < ∑ i, rate i :=
      Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
    have hdom : ∀ i, i ≠ (Equiv.Perm.decomposeFin ranking).1 →
        rate i * K ≤ rate (Equiv.Perm.decomposeFin ranking).1 := by
      rw [hlead]
      intro i hne
      have hpre : ranking (ranking.symm i) = i := ranking.apply_symm_apply i
      have hzero : ranking.symm i ≠ 0 := by
        intro hcon
        exact hne (by rw [← hpre, hcon])
      have hlt : (0 : Fin (m + 1)) < ranking.symm i :=
        lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hzero)
      have hstep := hsep 0 (ranking.symm i) hlt
      rwa [hpre] at hstep
    have hshare : 1 - (m : ℝ) / K ≤
        rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i :=
      leadShare_ge rate (Equiv.Perm.decomposeFin ranking).1 hK hpos hdom
    have hshareLe :
        rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i ≤ 1 := by
      rw [div_le_one hsumpos]
      exact Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_univ _)
    have hshareNonneg :
        0 ≤ rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i :=
      div_nonneg (hpos _).le hsumpos.le
    have htailpos : ∀ i, 0 < removeChosenRate rate
        (Equiv.Perm.decomposeFin ranking).1 i := fun i => hpos _
    have htailsep : ∀ k l : Fin m, k < l →
        removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1
            ((Equiv.Perm.decomposeFin ranking).2 l) * K ≤
          removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1
            ((Equiv.Perm.decomposeFin ranking).2 k) := by
      intro k l hkl
      rw [removeChosenRate_tail_eq, removeChosenRate_tail_eq]
      exact hsep k.succ l.succ (Fin.succ_lt_succ_iff.mpr hkl)
    have htail := ih (removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1)
      (Equiv.Perm.decomposeFin ranking).2 K hK htailpos htailsep
    have htailNonneg := plPermutationMass_nonnegative m
      (removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1)
      (fun i => (htailpos i).le) (Equiv.Perm.decomposeFin ranking).2
    have hmnonneg : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · simp [hm]
      · have hone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
    have hbnonneg : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) / (2 * K) :=
      div_nonneg hmnonneg (by linarith)
    have hstep := mul_le_mul_of_nonneg_left htail hshareNonneg
    have hslack : (rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i) *
        ((m : ℝ) * ((m : ℝ) - 1) / (2 * K)) ≤
          (m : ℝ) * ((m : ℝ) - 1) / (2 * K) := by
      nlinarith [hshareLe, hbnonneg, hshareNonneg]
    have hprod :
        1 - (m : ℝ) / K - (m : ℝ) * ((m : ℝ) - 1) / (2 * K) ≤
          (rate (Equiv.Perm.decomposeFin ranking).1 / ∑ i, rate i) *
            plPermutationMass m
              (removeChosenRate rate (Equiv.Perm.decomposeFin ranking).1)
              (Equiv.Perm.decomposeFin ranking).2 := by
      nlinarith [hstep, hslack, hshare]
    have hcount : ((m : ℝ) + 1) * (((m : ℝ) + 1) - 1) / (2 * K) =
        (m : ℝ) / K + (m : ℝ) * ((m : ℝ) - 1) / (2 * K) := by
      field_simp
      ring
    rw [show ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 by push_cast; ring, hcount]
    simp only [plPermutationMass]
    linarith [hprod]

/-- The masses never exceed one. -/
theorem plPermutationMass_le_one
    {n : ℕ} (rate : Fin n → ℝ) (hpos : ∀ i, 0 < rate i)
    (ranking : Equiv.Perm (Fin n)) :
    plPermutationMass n rate ranking ≤ 1 := by
  classical
  have hsum := plPermutationMass_sum_one n rate hpos
  have hnonneg := plPermutationMass_nonnegative n rate (fun i => (hpos i).le)
  rw [← hsum]
  exact Finset.single_le_sum (fun other _ => hnonneg other) (Finset.mem_univ _)

/-- **The concentration bound at low temperature.**  Bids separated by at least
`delta` along the ranking give the ranking all but
`n(n-1)/(2 exp(delta/tau))` of the mass. -/
theorem plPermutationMass_exponential_ge
    {n : ℕ} (bid : Fin n → ℝ) (reserve temperature separation : ℝ)
    (htemperature : 0 < temperature)
    (ranking : Equiv.Perm (Fin n))
    (hgap : ∀ k l : Fin n, k < l →
      bid (ranking l) + separation ≤ bid (ranking k)) :
    1 - (n : ℝ) * ((n : ℝ) - 1) /
        (2 * Real.exp (separation / temperature)) ≤
      plPermutationMass n
        (fun i => Real.exp ((bid i - reserve) / temperature)) ranking := by
  refine plPermutationMass_ge_of_separated n _ ranking _
    (Real.exp_pos _) (fun i => Real.exp_pos _) ?_
  intro k l hkl
  have hstep := hgap k l hkl
  rw [← Real.exp_add, Real.exp_le_exp, ← add_div,
    div_le_div_iff_of_pos_right htemperature]
  linarith

/-- The bound in the form the payment identity consumes: any target slack is
reached once the separation factor is large enough. -/
theorem plPermutationMass_ge_one_sub
    {n : ℕ} (rate : Fin n → ℝ) (ranking : Equiv.Perm (Fin n))
    {K slack : ℝ} (hK : 0 < K) (hslack : 0 < slack)
    (hpos : ∀ i, 0 < rate i)
    (hsep : ∀ k l : Fin n, k < l → rate (ranking l) * K ≤ rate (ranking k))
    (hlarge : (n : ℝ) * ((n : ℝ) - 1) / (2 * slack) ≤ K) :
    1 - slack ≤ plPermutationMass n rate ranking := by
  have hbound := plPermutationMass_ge_of_separated n rate ranking K hK hpos hsep
  have hmnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
  have hratio : (n : ℝ) * ((n : ℝ) - 1) / (2 * K) ≤ slack := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * K)]
    have hcross : (n : ℝ) * ((n : ℝ) - 1) ≤ 2 * slack * K := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * slack)] at hlarge
      linarith
    linarith
  linarith

/-! ### The limit -/

open Filter Topology

/-- The separation factor diverges as the temperature vanishes. -/
theorem exp_separation_tendsto_atTop {separation : ℝ} (hsep : 0 < separation) :
    Tendsto (fun temperature : ℝ => Real.exp (separation / temperature))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  refine Real.tendsto_exp_atTop.comp ?_
  simpa [div_eq_mul_inv, mul_comm] using
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hsep

/-- **The low-temperature clause.**  With bids separated along the ranking, the
Plackett--Luce mass of that ranking tends to one as the temperature vanishes:
the rule converges to the deterministic rank-by-bid allocation. -/
theorem plPermutationMass_tendsto_one_of_separated
    {n : ℕ} (bid : Fin n → ℝ) (reserve separation : ℝ)
    (hsep : 0 < separation) (ranking : Equiv.Perm (Fin n))
    (hgap : ∀ k l : Fin n, k < l →
      bid (ranking l) + separation ≤ bid (ranking k)) :
    Tendsto (fun temperature : ℝ =>
        plPermutationMass n
          (fun i => Real.exp ((bid i - reserve) / temperature)) ranking)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hdiverge := exp_separation_tendsto_atTop hsep
  have hlower : Tendsto (fun temperature : ℝ =>
      1 - (n : ℝ) * ((n : ℝ) - 1) /
        (2 * Real.exp (separation / temperature)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hvanish : Tendsto (fun temperature : ℝ =>
        (n : ℝ) * ((n : ℝ) - 1) /
          (2 * Real.exp (separation / temperature)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_const_nhds.div_atTop (hdiverge.const_mul_atTop two_pos)
    simpa using tendsto_const_nhds.sub hvanish
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower
    tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with temperature htemperature
    exact plPermutationMass_exponential_ge bid reserve temperature separation
      htemperature ranking hgap
  · filter_upwards with temperature
    exact plPermutationMass_le_one _ (fun i => Real.exp_pos _) ranking

/-! ### From concentration to the interim allocation -/

/-- **The concentration transfer.**  A ranking law that puts mass `p` on one
ranking gives every agent an interim allocation within `(1-p)` times twice the
weight bound of that ranking's value. -/
theorem rankingInterimPriority_sub_abs_le
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n))) (weight : ℕ → ℝ)
    (agent : Fin n) (target : Equiv.Perm (Fin n)) {bound : ℝ}
    (hbound : ∀ k, |weight k| ≤ bound) :
    |rankingInterimPriority law weight agent - weight (target.symm agent)| ≤
      (1 - law.probability target) * (2 * bound) := by
  classical
  have hboundNonneg : 0 ≤ bound := le_trans (abs_nonneg (weight 0)) (hbound 0)
  have hkey : rankingInterimPriority law weight agent -
        weight (target.symm agent) =
      ∑ ranking, law.probability ranking *
        (weight (ranking.symm agent) - weight (target.symm agent)) := by
    simp only [rankingInterimPriority, finiteExpectation, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, law.probability_sum_one,
      one_mul]
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun ranking => law.probability ranking *
      (weight (ranking.symm agent) - weight (target.symm agent)))
    (Finset.mem_univ target)
  have hmass := Finset.add_sum_erase Finset.univ law.probability
    (Finset.mem_univ target)
  have hterm : ∀ ranking ∈ Finset.univ.erase target,
      |law.probability ranking *
          (weight (ranking.symm agent) - weight (target.symm agent))| ≤
        law.probability ranking * (2 * bound) := by
    intro ranking _
    rw [abs_mul, abs_of_nonneg (law.probability_nonnegative ranking)]
    refine mul_le_mul_of_nonneg_left ?_ (law.probability_nonnegative ranking)
    rw [abs_le]
    have hone := abs_le.mp (hbound (ranking.symm agent))
    have htwo := abs_le.mp (hbound (target.symm agent))
    constructor <;> linarith [hone.1, hone.2, htwo.1, htwo.2]
  have hrest : ∑ ranking ∈ Finset.univ.erase target, law.probability ranking =
      1 - law.probability target := by
    have := law.probability_sum_one
    linarith [hmass]
  rw [hkey, ← hsplit]
  simp only [sub_self, mul_zero, zero_add]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, hrest]

/-- **The low-temperature interim allocation.**  With bids separated along the
ranking, every agent's interim allocation converges to the weight of the slot
that ranking assigns: the deterministic rank-by-bid allocation. -/
theorem rankingInterimPriority_tendsto_of_separated
    {n : ℕ} (bid : Fin n → ℝ) (reserve separation : ℝ)
    (hsep : 0 < separation) (weight : ℕ → ℝ) {bound : ℝ}
    (hbound : ∀ k, |weight k| ≤ bound)
    (ranking : Equiv.Perm (Fin n)) (agent : Fin n)
    (hgap : ∀ k l : Fin n, k < l →
      bid (ranking l) + separation ≤ bid (ranking k)) :
    Tendsto (fun temperature : ℝ =>
        rankingInterimPriority
          (plPermutationLaw n
            (fun i => Real.exp ((bid i - reserve) / temperature))
            (fun _ => Real.exp_pos _))
          weight agent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (weight (ranking.symm agent))) := by
  have hmass := plPermutationMass_tendsto_one_of_separated bid reserve
    separation hsep ranking hgap
  have hslack : Tendsto (fun temperature : ℝ =>
      (1 - plPermutationMass n
          (fun i => Real.exp ((bid i - reserve) / temperature)) ranking) *
        (2 * bound))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).sub hmass
    simpa using this.mul tendsto_const_nhds
  have hdiff : Tendsto (fun temperature : ℝ =>
      rankingInterimPriority
          (plPermutationLaw n
            (fun i => Real.exp ((bid i - reserve) / temperature))
            (fun i => Real.exp_pos _))
          weight agent - weight (ranking.symm agent))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hslack
    filter_upwards with temperature
    rw [Real.norm_eq_abs]
    exact rankingInterimPriority_sub_abs_le _ weight agent ranking hbound
  simpa using hdiff.add_const (weight (ranking.symm agent))

/-! ### Untied bids supply the separation

The concentration hypothesis asks for a uniform gap along the ranking.  An
untied profile supplies one: sorting the bids downward makes the sequence
strictly decreasing, and the finitely many pairwise gaps have a positive
minimum. -/

/-- Sorting an untied profile downward. -/
def descendingSort {n : ℕ} (bid : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -bid i)

theorem descendingSort_strictAnti {n : ℕ} {bid : Fin n → ℝ}
    (hinj : Function.Injective bid) :
    StrictAnti (fun k => bid (descendingSort bid k)) := by
  have hmono : Monotone (fun k => -bid (descendingSort bid k)) :=
    Tuple.monotone_sort (fun i => -bid i)
  have hanti : Antitone (fun k => bid (descendingSort bid k)) := by
    intro a b hab
    have hstep := hmono hab
    simp only at hstep
    linarith
  exact hanti.strictAnti_of_injective
    (hinj.comp (descendingSort bid).injective)

/-- **The separation of an untied profile.**  Some positive gap separates every
earlier bid from every later one along the descending sort. -/
theorem exists_separation_of_injective {n : ℕ} {bid : Fin n → ℝ}
    (hinj : Function.Injective bid) :
    ∃ separation : ℝ, 0 < separation ∧
      ∀ k l : Fin n, k < l →
        bid (descendingSort bid l) + separation ≤
          bid (descendingSort bid k) := by
  classical
  have hanti := descendingSort_strictAnti hinj
  by_cases hpairs :
      (Finset.univ.filter fun pair : Fin n × Fin n => pair.1 < pair.2).Nonempty
  · obtain ⟨best, hbest, hmin⟩ := Finset.exists_min_image _
      (fun pair : Fin n × Fin n =>
        bid (descendingSort bid pair.1) - bid (descendingSort bid pair.2))
      hpairs
    refine ⟨bid (descendingSort bid best.1) - bid (descendingSort bid best.2),
      sub_pos.mpr (hanti (Finset.mem_filter.mp hbest).2), ?_⟩
    intro k l hkl
    have hstep := hmin (k, l)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩)
    simp only at hstep
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro k l hkl
    exact absurd ⟨(k, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩⟩ hpairs

/-- **The untied low-temperature limit.**  At any untied profile every agent's
interim allocation converges to the weight of the slot the bid order assigns. -/
theorem rankingInterimPriority_tendsto_of_injective
    {n : ℕ} {bid : Fin n → ℝ} (hinj : Function.Injective bid)
    (reserve : ℝ) (weight : ℕ → ℝ) {bound : ℝ}
    (hbound : ∀ k, |weight k| ≤ bound) (agent : Fin n) :
    Tendsto (fun temperature : ℝ =>
        rankingInterimPriority
          (plPermutationLaw n
            (fun i => Real.exp ((bid i - reserve) / temperature))
            (fun _ => Real.exp_pos _))
          weight agent)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (weight ((descendingSort bid).symm agent))) := by
  obtain ⟨separation, hsep, hgap⟩ := exists_separation_of_injective hinj
  exact rankingInterimPriority_tendsto_of_separated bid reserve separation hsep
    weight hbound (descendingSort bid) agent hgap

/-! ### What the payment bridge consumes

The dominated-convergence bridge of `Mechanism/Revenue.lean` asks for a
uniform bound on the allocation curve and pointwise convergence almost
everywhere on the integration interval.  The bound is immediate because the
interim allocation is a convex combination of weights, and the reports at which
the profile ties are finitely many, so the pointwise limit above holds off a
null set. -/

/-- The interim allocation inherits any bound on the weights. -/
theorem rankingInterimPriority_abs_le
    {n : ℕ} (law : FiniteLaw (Equiv.Perm (Fin n))) (weight : ℕ → ℝ)
    (agent : Fin n) {bound : ℝ} (hbound : ∀ k, |weight k| ≤ bound) :
    |rankingInterimPriority law weight agent| ≤ bound := by
  classical
  have hstep : |∑ ranking, law.probability ranking *
      weight (ranking.symm agent)| ≤
        ∑ ranking, law.probability ranking * bound := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro ranking _
    rw [abs_mul, abs_of_nonneg (law.probability_nonnegative ranking)]
    exact mul_le_mul_of_nonneg_left (hbound _)
      (law.probability_nonnegative ranking)
  rw [rankingInterimPriority, finiteExpectation]
  rw [← Finset.sum_mul, law.probability_sum_one, one_mul] at hstep
  exact hstep

/-- Only finitely many reports tie the profile, so the untied limit holds off a
null set of reports. -/
theorem tiedReports_subset {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (hoff : ∀ j k : Fin n, j ≠ agent → k ≠ agent → bid j = bid k → j = k) :
    {report : ℝ | ¬ Function.Injective (Function.update bid agent report)} ⊆
      ↑((Finset.univ.erase agent).image bid) := by
  classical
  intro report hreport
  by_contra hnot
  refine hreport ?_
  intro j k hjk
  by_cases hj : j = agent <;> by_cases hk : k = agent
  · rw [hj, hk]
  · exfalso
    rw [hj, Function.update_self, Function.update_of_ne hk] at hjk
    exact hnot (by
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, ?_, hjk.symm⟩)
      exact Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
  · exfalso
    rw [hk, Function.update_self, Function.update_of_ne hj] at hjk
    exact hnot (by
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, ?_, hjk⟩)
      exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  · rw [Function.update_of_ne hj, Function.update_of_ne hk] at hjk
    exact hoff j k hj hk hjk

theorem tiedReports_null {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (hoff : ∀ j k : Fin n, j ≠ agent → k ≠ agent → bid j = bid k → j = k) :
    MeasureTheory.volume
        {report : ℝ |
          ¬ Function.Injective (Function.update bid agent report)} = 0 :=
  MeasureTheory.measure_mono_null (tiedReports_subset bid agent hoff)
    (Set.Finite.measure_zero (Finset.finite_toSet _) _)

/-- **The curve-level limit off the ties.**  For almost every report the
interim allocation converges to the weight of the slot the bid order assigns at
that report. -/
theorem interimCurve_tendsto_ae
    {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n) (reserve : ℝ) (weight : ℕ → ℝ)
    {bound : ℝ} (hbound : ∀ k, |weight k| ≤ bound)
    (hoff : ∀ j k : Fin n, j ≠ agent → k ≠ agent → bid j = bid k → j = k) :
    ∀ᵐ report ∂MeasureTheory.volume,
      Tendsto (fun temperature : ℝ =>
          rankingInterimPriority
            (plPermutationLaw n
              (fun i => Real.exp
                ((Function.update bid agent report i - reserve) / temperature))
              (fun _ => Real.exp_pos _))
            weight agent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (weight
          ((descendingSort (Function.update bid agent report)).symm agent))) := by
  have hnull := tiedReports_null bid agent hoff
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro report hreport
  simp only [Set.mem_setOf_eq] at hreport ⊢
  intro hinj
  exact hreport
    (rankingInterimPriority_tendsto_of_injective hinj reserve weight hbound
      agent)

/-- The rate vector moves continuously with the report. -/
theorem continuous_updateRate {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (reserve temperature : ℝ) :
    Continuous fun report : ℝ => fun i : Fin n =>
      Real.exp
        ((Function.update bid agent report i - reserve) / temperature) := by
  refine continuous_pi fun i => ?_
  by_cases hagent : i = agent
  · subst hagent
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hagent]
    exact continuous_const

/-- **The allocation curve is continuous in the report.**  This is the
measurability the dominated-convergence bridge asks for. -/
theorem continuous_interimCurve {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (reserve temperature : ℝ) (weight : ℕ → ℝ) :
    Continuous fun report : ℝ =>
      rankingInterimPriority
        (plPermutationLaw n
          (fun i => Real.exp
            ((Function.update bid agent report i - reserve) / temperature))
          (fun _ => Real.exp_pos _))
        weight agent := by
  classical
  simp only [rankingInterimPriority, finiteExpectation, plPermutationLaw]
  refine continuous_finsetSum Finset.univ fun ranking _ => ?_
  refine Continuous.mul ?_ continuous_const
  rw [continuous_iff_continuousAt]
  intro report
  exact (plPermutationMass_continuousAt n _ (fun _ => Real.exp_pos _)
    ranking).comp
    (continuous_updateRate bid agent reserve temperature).continuousAt

theorem measurable_interimCurve {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (reserve temperature : ℝ) (weight : ℕ → ℝ) :
    Measurable fun report : ℝ =>
      rankingInterimPriority
        (plPermutationLaw n
          (fun i => Real.exp
            ((Function.update bid agent report i - reserve) / temperature))
          (fun _ => Real.exp_pos _))
        weight agent :=
  (continuous_interimCurve bid agent reserve temperature weight).measurable

/-! ### The payment limit

Everything the dominated-convergence bridge asks for is now available, so the
Myerson payment converges to the payment computed from the deterministic
rank-by-bid allocation.  That is the low-temperature clause of
`prop:revenue` at the level of one agent. -/

open Mechanism

/-- The allocation curve of one agent as a function of the temperature and the
report. -/
def plAllocationCurve {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (reserve : ℝ) (weight : ℕ → ℝ) (temperature report : ℝ) : ℝ :=
  rankingInterimPriority
    (plPermutationLaw n
      (fun i => Real.exp
        ((Function.update bid agent report i - reserve) / temperature))
      (fun _ => Real.exp_pos _))
    weight agent

/-- The deterministic rank-by-bid allocation curve. -/
def deterministicAllocationCurve {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n)
    (weight : ℕ → ℝ) (report : ℝ) : ℝ :=
  weight ((descendingSort (Function.update bid agent report)).symm agent)

/-- **The low-temperature payment limit.**  At an untied profile the agent's
Myerson payment under the Plackett--Luce rule converges, as the temperature
vanishes, to the payment computed from the deterministic rank-by-bid
allocation. -/
theorem myersonCurvePayment_tendsto_deterministic
    {n : ℕ} (bid : Fin n → ℝ) (agent : Fin n) (reserve : ℝ) (weight : ℕ → ℝ)
    {bound : ℝ} (hbound : ∀ k, |weight k| ≤ bound)
    (hinj : Function.Injective bid) :
    Tendsto (fun temperature : ℝ =>
        myersonCurvePayment reserve
          (plAllocationCurve bid agent reserve weight temperature) (bid agent))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (myersonCurvePayment reserve
        (deterministicAllocationCurve bid agent weight) (bid agent))) := by
  classical
  have hoff : ∀ j k : Fin n, j ≠ agent → k ≠ agent → bid j = bid k → j = k :=
    fun j k _ _ hjk => hinj hjk
  refine myersonCurvePayment_tendsto_of_dominated
    (fun temperature => plAllocationCurve bid agent reserve weight temperature)
    (deterministicAllocationCurve bid agent weight) (fun _ => bound)
    ?_ ?_ intervalIntegrable_const ?_ ?_
  · filter_upwards with temperature
    exact ((measurable_interimCurve bid agent reserve temperature
      weight).aestronglyMeasurable).restrict
  · filter_upwards with temperature
    filter_upwards with report _
    rw [Real.norm_eq_abs]
    exact rankingInterimPriority_abs_le _ weight agent hbound
  · filter_upwards [interimCurve_tendsto_ae bid agent reserve weight hbound
      hoff] with report hreport _
    exact hreport
  · have hupdate : Function.update bid agent (bid agent) = bid :=
      Function.update_eq_self agent bid
    have hlimit := rankingInterimPriority_tendsto_of_injective hinj reserve
      weight hbound agent
    simp only [plAllocationCurve, deterministicAllocationCurve, hupdate]
    exact hlimit

/-- **The low-temperature revenue limit.**  Summing over agents, expected
truthful revenue under the Plackett--Luce rule converges to the truthful
revenue of the deterministic rank-by-bid position auction.  This is clause (ii)
of `prop:revenue`. -/
theorem totalMyersonPayment_tendsto_deterministic
    {n : ℕ} (bid : Fin n → ℝ) (reserve : ℝ) (weight : ℕ → ℝ)
    {bound : ℝ} (hbound : ∀ k, |weight k| ≤ bound)
    (hinj : Function.Injective bid) :
    Tendsto (fun temperature : ℝ =>
        ∑ agent : Fin n, myersonCurvePayment reserve
          (plAllocationCurve bid agent reserve weight temperature) (bid agent))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ agent : Fin n, myersonCurvePayment reserve
        (deterministicAllocationCurve bid agent weight) (bid agent))) :=
  tendsto_finsetSum Finset.univ fun agent _ =>
    myersonCurvePayment_tendsto_deterministic bid agent reserve weight hbound
      hinj

end

end SmoothingCliff.Racing
