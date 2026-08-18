/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.BellmanOperator
public import Econlib.Probability.FinDist.Expect
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Stochastic Dynamic Programing

Extends the Bellman framework to stochastic transitions, connecting to Econlib's probability
module. Two variants are provided:

1. **Finite state**: Uses `FinDist (Fin n)` for transitions, expectation via `FinDist.expect`
2. **General**: Uses `MeasureTheory.Measure` for transitions, Bochner integration

The finite case is the workhorse for computational political economy (voting models, mechanism
design with discrete types). The general case provides the theoretical foundation and connects to
the continuous distribution theory in `Econlib.Probability`.

## Main definitions

* `finiteBellmanOperator`: Bellman operator for finite-state stochastic MDPs
* `stochBellmanOperator`: Bellman operator for general stochastic MDPs

## Main statements

* `FinMDP.bellmanOperator_existsUnique_fixedPoint`: Unique fixed point of the finite Bellman
  operator
* `stochBellmanOperator_contraction`: The stochastic Bellman operator is a contraction
* `StochMDP.bellmanOperator_existsUnique_fixedPoint`: Unique bounded fixed point of the stochastic
  Bellman operator
* `bellman_dirac_eq`: The stochastic operator on a Dirac-embedded MDP agrees with the deterministic
  Bellman operator

## References

* Blackwell, David. 1965. “Discounted Dynamic Programing.” *The Annals of Mathematical Statistics*
  36 (1): 226–35. [https://doi.org/10.1214/aoms/1177700285](https://doi.org/10.1214/aoms/1177700285).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

dynamic programing, bellman equation, markov decision process, stochastic, contraction mapping
-/

@[expose] public section

open Econlib.Probability MeasureTheory

namespace Econlib.Optimization.DynamicProgramming

open Blackwell UnboundedDetMDP

variable {A : Type*}

/-! ## Finite-State Bellman Operator -/

/-- The **Bellman operator** for a finite-state stochastic MDP:
`(Tv)(s) = sup_{a ∈ Γ(s)} [u(s,a) + β · 𝔼_{s' ~ Q(s,a)}[v(s')]]`

Expectation is computed via `FinDist.expect`. -/
noncomputable def finiteBellmanOperator {n : ℕ} (M : FinMDP n A)
    (v : Fin n → ℝ) (s : Fin n) : ℝ :=
  sSup {r : ℝ | ∃ a ∈ M.Γ s,
    r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' ↦ v s')}

/-! ### Infrastructure lemmas -/

/-- The finite Bellman set at `s` is nonempty (from `Γ_nonempty`). -/
lemma finiteBellmanSet_nonempty {n : ℕ} (M : FinMDP n A) (v : Fin n → ℝ) (s : Fin n) :
    {r : ℝ | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' ↦ v s')}.Nonempty :=
  let ⟨a, ha⟩ := M.Γ_nonempty s; ⟨_, a, ha, rfl⟩

/-- The finite Bellman set at `s` is bounded above when rewards are bounded. -/
lemma finiteBellmanSet_bddAbove {n : ℕ} (M : FinMDP n A) (v : Fin n → ℝ) (s : Fin n)
    (hR : ∃ B : ℝ, ∀ (s : Fin n) (a : A), |M.reward s a| ≤ B) :
    BddAbove {r : ℝ | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' ↦ v s')} := by
  obtain ⟨Br, hBr⟩ := hR
  -- `|v ·|` has finite range over `Fin n`, hence is bounded above.
  obtain ⟨Bv, hBv⟩ := (Finite.bddAbove_range (fun i => |v i|)).imp
    fun _ hub i => hub ⟨i, rfl⟩
  refine ⟨Br + |M.β| * Bv, fun r hr => ?_⟩
  obtain ⟨a, _, rfl⟩ := hr
  have hexp_le : FinDist.expect (M.transition s a) (fun s' => v s') ≤ Bv := by
    calc FinDist.expect (M.transition s a) (fun s' => v s')
        ≤ FinDist.expect (M.transition s a) (fun _ => Bv) :=
          FinDist.expect_mono _ _ _ (fun i => le_abs_self (v i) |>.trans (hBv i))
      _ = Bv := FinDist.expect_const _ _
  have hexp_ge : -Bv ≤ FinDist.expect (M.transition s a) (fun s' => v s') := by
    calc -Bv = FinDist.expect (M.transition s a) (fun _ => -Bv) :=
          (FinDist.expect_const _ _).symm
      _ ≤ FinDist.expect (M.transition s a) (fun s' => v s') :=
          FinDist.expect_mono _ _ _ (fun i => by linarith [neg_abs_le (v i), hBv i])
  have habs_exp : |FinDist.expect (M.transition s a) (fun s' => v s')| ≤ Bv :=
    abs_le.mpr ⟨hexp_ge, hexp_le⟩
  have h2 : |M.β * FinDist.expect (M.transition s a) (fun s' => v s')| ≤ |M.β| * Bv := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left habs_exp (abs_nonneg _)
  linarith [hBr s a, le_abs_self (M.reward s a),
    le_abs_self (M.β * FinDist.expect (M.transition s a) (fun s' => v s'))]

/-! ### Core Properties -/

/-- Monotonicity of the finite Bellman operator. -/
lemma finiteBellmanOperator_monotone {n : ℕ} (M : FinMDP n A)
    (hR : ∃ B : ℝ, ∀ (s : Fin n) (a : A), |M.reward s a| ≤ B) :
    ∀ v w : Fin n → ℝ, (∀ s, v s ≤ w s) →
      ∀ s, finiteBellmanOperator M v s ≤ finiteBellmanOperator M w s := by
  intro v w hvw s
  unfold finiteBellmanOperator
  apply csSup_le (finiteBellmanSet_nonempty M v s)
  rintro r ⟨a, ha, rfl⟩
  apply le_csSup_of_le (finiteBellmanSet_bddAbove M w s hR) ⟨a, ha, rfl⟩
  have hexp : FinDist.expect (M.transition s a) (fun s' => v s') ≤
      FinDist.expect (M.transition s a) (fun s' => w s') :=
    FinDist.expect_mono _ _ _ hvw
  linarith [mul_le_mul_of_nonneg_left hexp M.β_nonneg]

/-- Discounting property of the finite Bellman operator. -/
lemma finiteBellmanOperator_discounting {n : ℕ} (M : FinMDP n A)
    (hR : ∃ B : ℝ, ∀ (s : Fin n) (a : A), |M.reward s a| ≤ B) :
    ∀ (v : Fin n → ℝ) (c : ℝ), 0 ≤ c →
      ∀ s, finiteBellmanOperator M (fun s' ↦ v s' + c) s ≤
        finiteBellmanOperator M v s + M.β * c := by
  intro v c hc s
  unfold finiteBellmanOperator
  apply csSup_le (finiteBellmanSet_nonempty M (fun s' => v s' + c) s)
  rintro r ⟨a, ha, rfl⟩
  have hle : M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' => v s') ≤
      sSup {r | ∃ a ∈ M.Γ s,
        r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' => v s')} :=
    le_csSup (finiteBellmanSet_bddAbove M v s hR) ⟨a, ha, rfl⟩
  have hexp_add : FinDist.expect (M.transition s a) (fun s' => v s' + c) =
      FinDist.expect (M.transition s a) (fun s' => v s') + c := by
    rw [show (fun s' => v s' + c) = (fun s' => v s') + (fun _ => c) from rfl,
        FinDist.expect_add, FinDist.expect_const]
  rw [hexp_add]; linarith [mul_add M.β (FinDist.expect (M.transition s a) (fun s' => v s')) c]

/-- Every function on `Fin n` is bounded. Supplies the (vacuous) boundedness side conditions when
instantiating the shared Blackwell core on a finite state space. -/
private lemma finFun_bounded {n : ℕ} (v : Fin n → ℝ) : UniformBounded v :=
  (Finite.bddAbove_range fun s => |v s|).imp fun _ hub s => hub ⟨s, rfl⟩

/-- Pointwise sup-form contraction for the finite Bellman operator: Blackwell's theorem applied to
monotonicity and discounting. -/
lemma finiteBellmanOperator_apply_abs_sub_le {n : ℕ} (M : FinMDP n A) (v w : Fin n → ℝ)
    (s : Fin n) :
    |finiteBellmanOperator M v s - finiteBellmanOperator M w s| ≤ M.β * ⨆ t, |v t - w t| :=
  Blackwell.abs_sub_le_of_monotone_discounting
    (fun v w _ _ hvw => finiteBellmanOperator_monotone M M.reward_bounded v w hvw)
    (fun v c _ hc => finiteBellmanOperator_discounting M M.reward_bounded v c hc)
    (finFun_bounded v) (finFun_bounded w) s

/-- Pointwise contraction bound for the finite Bellman operator, in the metric of the `Pi` space
`Fin n → ℝ`. -/
lemma finiteBellmanOperator_pointwise_contraction {n : ℕ} (M : FinMDP n A) (v w : Fin n → ℝ)
    (s : Fin n) :
    dist (finiteBellmanOperator M v s) (finiteBellmanOperator M w s) ≤ M.β * dist v w := by
  haveI : Nonempty (Fin n) := ⟨s⟩
  rw [Real.dist_eq]
  calc |finiteBellmanOperator M v s - finiteBellmanOperator M w s|
      ≤ M.β * ⨆ t, |v t - w t| := finiteBellmanOperator_apply_abs_sub_le M v w s
    _ ≤ M.β * dist v w := by
        refine mul_le_mul_of_nonneg_left (ciSup_le fun t => ?_) M.β_nonneg
        rw [← Real.dist_eq]
        exact dist_le_pi_dist v w t

/-- There is a unique fixed point of the finite Bellman operator. -/
theorem FinMDP.bellmanOperator_existsUnique_fixedPoint {n : ℕ} (M : FinMDP n A) :
    ∃! v : Fin n → ℝ, ∀ s, v s = finiteBellmanOperator M v s := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨Fin.elim0, fun s => Fin.elim0 s,
      fun y _ => funext (fun i => Fin.elim0 i)⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    -- Boundedness is automatic on `Fin n`, so the core's bounded fixed point is the unique
    -- fixed point outright.
    have hc := Blackwell.contractingWith_liftBddFun
      (h_maps := fun v _ => finFun_bounded (finiteBellmanOperator M v))
      M.β_nonneg M.β_lt_one
      (fun v w _ _ s => finiteBellmanOperator_apply_abs_sub_le M v w s)
    exact ⟨Blackwell.bddFixedPoint hc, Blackwell.bddFixedPoint_isFixedPt hc,
      fun y hy => Blackwell.eq_bddFixedPoint hc (finFun_bounded y) hy⟩

/-- **Optimal action existence (pointwise).** If `v_star` is the unique fixed point of the finite
Bellman operator and `Γ(s)` is compact, then each state `s` has a feasible action achieving the
supremum in the Bellman equation. This is a `∀ s, ∃ a …` statement, not a stationary policy
function. -/
theorem FinMDP.exists_optimalAction {n : ℕ} [TopologicalSpace A] (M : FinMDP n A)
    (h_compact : ∀ s, IsCompact (M.Γ s))
    (v_star : Fin n → ℝ) (hv : ∀ s, v_star s = finiteBellmanOperator M v_star s)
    (h_cont : ∀ s, ContinuousOn (fun a => M.reward s a +
        M.β * FinDist.expect (M.transition s a) v_star) (M.Γ s)) :
    ∀ s, ∃ a ∈ M.Γ s,
      v_star s = M.reward s a + M.β * FinDist.expect (M.transition s a) v_star := by
  intro s
  set obj : A → ℝ := fun a => M.reward s a + M.β * FinDist.expect (M.transition s a) v_star
  obtain ⟨a, ha, hmax⟩ := (h_compact s).exists_isMaxOn (M.Γ_nonempty s) (h_cont s)
  refine ⟨a, ha, ?_⟩
  rw [hv s]; unfold finiteBellmanOperator
  have himg : obj '' (M.Γ s) = {r | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' => v_star s')} := by
    ext r; simp only [Set.mem_image, Set.mem_setOf_eq, obj, eq_comm]
  have hbdd : BddAbove {r | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * FinDist.expect (M.transition s a) (fun s' => v_star s')} := by
    rw [← himg]; exact ((h_compact s).image_of_continuousOn (h_cont s)).bddAbove
  have hne := finiteBellmanSet_nonempty M v_star s
  exact le_antisymm (csSup_le hne (fun r ⟨a', ha', hr⟩ => hr ▸ hmax ha'))
    (le_csSup hbdd ⟨a, ha, rfl⟩)

/-! ## General Stochastic Bellman Operator -/

/-- The **Bellman operator** for a general stochastic MDP with measure-valued transitions:
`(Tv)(s) = sup_{a ∈ Γ(s)} [u(s,a) + β · ∫ v(s') dQ(s,a)(s')]` -/
noncomputable def stochBellmanOperator (M : StochMDP)
    (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a ∈ M.Γ s,
    r = M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)}

/-- The stochastic Bellman set at `s` is nonempty (from `Γ_nonempty`). -/
lemma stochBellmanSet_nonempty (M : StochMDP) (v : ℝ → ℝ) (s : ℝ) :
    {r : ℝ | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)}.Nonempty :=
  let ⟨a, ha⟩ := M.Γ_nonempty s; ⟨_, a, ha, rfl⟩

/-- The stochastic Bellman set at `s` is bounded above when `v` is uniformly bounded and integrable
against each transition measure. -/
lemma stochBellmanSet_bddAbove (M : StochMDP) (v : ℝ → ℝ) (s : ℝ)
    (hBv : UniformBounded v)
    (hint : ∀ a, Integrable v (M.transition s a)) :
    BddAbove {r : ℝ | ∃ a ∈ M.Γ s,
      r = M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)} := by
  obtain ⟨Br, hBr⟩ := M.reward_bounded
  obtain ⟨Bv, hBv⟩ := hBv
  refine ⟨Br + |M.β| * Bv, fun r hr => ?_⟩
  obtain ⟨a, _, rfl⟩ := hr
  have habs_int : |∫ s', v s' ∂(M.transition s a)| ≤ Bv := by
    have := M.transition_prob s a
    calc |∫ s', v s' ∂(M.transition s a)|
        ≤ ∫ s', |v s'| ∂(M.transition s a) := norm_integral_le_integral_norm v
      _ ≤ ∫ _, Bv ∂(M.transition s a) :=
          integral_mono (hint a).norm (integrable_const Bv) (fun s => hBv s)
      _ = Bv := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have h2 : |M.β * ∫ s', v s' ∂(M.transition s a)| ≤ |M.β| * Bv := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left habs_int (abs_nonneg _)
  linarith [hBr s a, le_abs_self (M.reward s a),
    le_abs_self (M.β * ∫ s', v s' ∂(M.transition s a))]

/-- Monotonicity of the general stochastic Bellman operator. -/
lemma stochBellmanOperator_monotone (M : StochMDP) :
    ∀ v w : ℝ → ℝ,
      (∀ s a, Integrable v (M.transition s a)) →
      (∀ s a, Integrable w (M.transition s a)) →
      UniformBounded w →
      (∀ s, v s ≤ w s) →
      ∀ s, stochBellmanOperator M v s ≤ stochBellmanOperator M w s := by
  intro v w hv_int hw_int hBw hvw s
  unfold stochBellmanOperator
  apply csSup_le (stochBellmanSet_nonempty M v s)
  rintro r ⟨a, ha, rfl⟩
  apply le_csSup_of_le (stochBellmanSet_bddAbove M w s hBw (hw_int s)) ⟨a, ha, rfl⟩
  have := M.transition_prob s a
  have hint : ∫ s', v s' ∂(M.transition s a) ≤ ∫ s', w s' ∂(M.transition s a) :=
    integral_mono (hv_int s a) (hw_int s a) hvw
  linarith [mul_le_mul_of_nonneg_left hint M.β_nonneg]

/-- Discounting property of the general stochastic Bellman operator. -/
lemma stochBellmanOperator_discounting (M : StochMDP) :
    ∀ (v : ℝ → ℝ) (c : ℝ),
      (∀ s a, Integrable v (M.transition s a)) →
      UniformBounded v → 0 ≤ c →
      ∀ s, stochBellmanOperator M (fun s' => v s' + c) s ≤
        stochBellmanOperator M v s + M.β * c := by
  intro v c hv_int hBv hc s
  unfold stochBellmanOperator
  apply csSup_le (stochBellmanSet_nonempty M (fun s' => v s' + c) s)
  rintro r ⟨a, ha, rfl⟩
  have hle : M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a) ≤
      sSup {r | ∃ a ∈ M.Γ s, r = M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)} :=
    le_csSup (stochBellmanSet_bddAbove M v s hBv (hv_int s)) ⟨a, ha, rfl⟩
  -- The constant integrates to itself against a probability measure.
  have hint_add : ∫ s', (v s' + c) ∂(M.transition s a) =
      (∫ s', v s' ∂(M.transition s a)) + c := by
    have := M.transition_prob s a
    rw [integral_add (hv_int s a) (integrable_const c)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hint_add]
  linarith [mul_add M.β (∫ s', v s' ∂(M.transition s a)) c]

/-- The stochastic Bellman operator preserves boundedness. -/
lemma stochBellmanOperator_bounded (M : StochMDP) (v : ℝ → ℝ)
    (hBv : UniformBounded v)
    (hint : ∀ s a, Integrable v (M.transition s a)) :
    UniformBounded (stochBellmanOperator M v) := by
  obtain ⟨Br, hBr⟩ := M.reward_bounded
  obtain ⟨Bv, hBv⟩ := hBv
  refine ⟨Br + |M.β| * Bv, fun s => ?_⟩
  unfold stochBellmanOperator
  rw [abs_le]
  have hne := stochBellmanSet_nonempty M v s
  have hbdd := stochBellmanSet_bddAbove M v s ⟨Bv, hBv⟩ (hint s)
  have helem : ∀ a, |M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)| ≤ Br + |M.β| * Bv := by
    intro a
    have := M.transition_prob s a
    have habs_int : |∫ s', v s' ∂(M.transition s a)| ≤ Bv := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ s', v s' ∂(M.transition s a)‖
          ≤ ∫ s', ‖v s'‖ ∂(M.transition s a) := norm_integral_le_integral_norm _
        _ ≤ ∫ _, Bv ∂(M.transition s a) :=
            integral_mono (hint s a).norm (integrable_const Bv)
              (fun s => by rw [Real.norm_eq_abs]; exact hBv s)
        _ = Bv := by simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    calc |M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)|
        ≤ |M.reward s a| + |M.β * ∫ s', v s' ∂(M.transition s a)| := abs_add_le _ _
      _ ≤ Br + |M.β| * Bv := by
          rw [abs_mul]
          exact add_le_add (hBr s a) (mul_le_mul_of_nonneg_left habs_int (abs_nonneg _))
  constructor
  · obtain ⟨_, a, ha_mem, rfl⟩ := hne
    linarith [le_csSup hbdd ⟨a, ha_mem, rfl⟩,
              neg_abs_le (M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)), helem a]
  · exact csSup_le hne (fun r hr => by
      obtain ⟨a, _, rfl⟩ := hr
      linarith [le_abs_self (M.reward s a + M.β * ∫ s', v s' ∂(M.transition s a)), helem a])

/-- Pointwise contraction for the stochastic Bellman operator: `|Tv(s) - Tw(s)| ≤ β sup|v - w|`.
This is Blackwell's theorem applied to monotonicity and discounting; the blanket integrability
hypothesis `h_int` supplies their side conditions and holds e.g. whenever all bounded Borel
functions are integrable with respect to the transition measures. -/
lemma stochBellmanOperator_pointwise_contraction (M : StochMDP)
    (h_int : ∀ (u : ℝ → ℝ), UniformBounded u →
      ∀ s a, Integrable u (M.transition s a))
    (v w : ℝ → ℝ) (hBv : UniformBounded v) (hBw : UniformBounded w)
    (s : ℝ) :
    |stochBellmanOperator M v s - stochBellmanOperator M w s| ≤
      M.β * ⨆ s, |v s - w s| :=
  Blackwell.abs_sub_le_of_monotone_discounting
    (fun v w hv hw hvw =>
      stochBellmanOperator_monotone M v w (h_int v hv) (h_int w hw) hw hvw)
    (fun v c hv hc => stochBellmanOperator_discounting M v c (h_int v hv) hv hc)
    hBv hBw s

/-- The stochastic Bellman operator is a contraction with modulus `β` (Blackwell 1965). -/
theorem stochBellmanOperator_contraction (M : StochMDP)
    (h_int : ∀ (u : ℝ → ℝ), UniformBounded u →
      ∀ s a, Integrable u (M.transition s a))
    (v w : ℝ → ℝ) (hBv : UniformBounded v) (hBw : UniformBounded w) :
    ⨆ s, |stochBellmanOperator M v s - stochBellmanOperator M w s| ≤
      M.β * ⨆ s, |v s - w s| :=
  ciSup_le fun s => stochBellmanOperator_pointwise_contraction M h_int v w hBv hBw s

/-- **General Bellman fixed point**: There is a unique bounded value function satisfying the
stochastic Bellman equation. The hypothesis `h_int` holds whenever all bounded Borel functions are
integrable with respect to the transition measures. -/
theorem StochMDP.bellmanOperator_existsUnique_fixedPoint (M : StochMDP)
    (h_int : ∀ (v : ℝ → ℝ), UniformBounded v →
      ∀ s a, Integrable v (M.transition s a)) :
    ∃! v : ℝ → ℝ, UniformBounded v ∧
      ∀ s, v s = stochBellmanOperator M v s :=
  Blackwell.existsUnique_bdd_fixedPoint
    (Blackwell.contractingWith_liftBddFun
      (h_maps := fun v hv => stochBellmanOperator_bounded M v hv (h_int v hv))
      M.β_nonneg M.β_lt_one
      (fun v w hBv hBw s => stochBellmanOperator_pointwise_contraction M h_int v w hBv hBw s))

/-! ## Embedding: Deterministic into Stochastic -/

/-- Embed a deterministic MDP as a stochastic MDP with Dirac transitions. -/
noncomputable def DetMDP.toStochMDP (M : DetMDP ℝ ℝ) : StochMDP where
  Γ := M.Γ
  reward := M.reward
  transition s a := Measure.dirac (M.transition s a)
  β := M.β
  β_nonneg := M.β_nonneg
  β_lt_one := M.β_lt_one
  Γ_nonempty := M.Γ_nonempty
  reward_bounded := M.reward_bounded
  transition_prob _ _ := Measure.dirac.isProbabilityMeasure

/-- The stochastic Bellman operator on a Dirac-embedded MDP agrees with the deterministic Bellman
operator. -/
lemma bellman_dirac_eq (M : DetMDP ℝ ℝ) (v : ℝ → ℝ) (s : ℝ) :
    stochBellmanOperator M.toStochMDP v s = M.bellmanOperator v s := by
  unfold stochBellmanOperator bellmanOperator UnboundedDetMDP.bellmanSet DetMDP.toStochMDP
  -- The Dirac expectation collapses each integral to a point evaluation.
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, integral_dirac]

end Econlib.Optimization.DynamicProgramming
