/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Probability.Doeblin
public import Econlib.Math.Topology.Brouwer
public import Econlib.Probability.FinDist.Simplex
public import Econlib.Probability.Markov.Basic
public import Econlib.Probability.ProbDist.Stationary

/-!
# Ergodic theory for finite Markov chains

Existence, uniqueness, and convergence of stationary distributions for finite Markov chains over an
arbitrary finite state space `α`, packaged with `FiniteMarkovChain α`. Existence follows from
Brouwer's fixed-point theorem on the simplex. Under strictly positive transitions, the step
operator is a total-variation contraction (Doeblin's condition), giving a unique stationary
distribution to which every initial distribution converges geometrically. The final section treats
the endogenous Markov chain on `[w_min, w_max] × Fin n` induced by a fixed continuous policy.

## Main definitions

* `FiniteMarkovChain.stationaryDist` — the stationary distribution (a choice witness from
  `exists_stationary`).
* `EndogenousMarkovChain` — an endogenous chain on `[w_min, w_max] × Fin n` whose continuous
  component evolves under a given continuous policy.
* `EndogenousMarkovChain.toKernel` — the Markov kernel induced by the endogenous chain.

## Main statements

* `FiniteMarkovChain.exists_stationary` — every finite Markov chain on a nonempty finite state
  space has a stationary distribution.
* `FiniteMarkovChain.unique_stationary` — strictly positive transitions force the stationary
  distribution to be unique.
* `FiniteMarkovChain.geometric_convergence` / `geometric_convergence_to` — `P.nStep k d₀` converges
  geometrically to the stationary distribution.
* `EndogenousMarkovChain.toKernel_isFeller` — the endogenous kernel is Feller.
* `EndogenousMarkovChain.exists_stationary` — existence of an invariant probability measure on the
  product space.

## References

* Meyn, Sean P., and Richard L. Tweedie. 1993. *Markov Chains and Stochastic Stability*. Springer.

## Tags

markov chain, stationary distribution, ergodic, doeblin, geometric convergence, feller kernel
-/

@[expose] public section

namespace Econlib.Probability

open Finset BigOperators MeasureTheory

namespace FiniteMarkovChain

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : FiniteMarkovChain α)

/-! ## Existence via Brouwer's fixed-point theorem -/

/-- **Existence of stationary distribution.** Every finite Markov chain on a nonempty finite state
space has at least one stationary distribution. -/
theorem exists_stationary [Nonempty α] :
    ∃ μ : FinDist α, P.IsStationary μ := by
  letI : Inhabited α := ⟨Classical.choice ‹Nonempty α›⟩
  set S := (stdSimplex ℝ α : Set (α → ℝ))
  set stepF : (α → ℝ) → (α → ℝ) :=
    fun p s' => ∑ s, p s * P.transition s s'
  have hstepF_maps : ∀ p ∈ S, stepF p ∈ S := by
    intro p ⟨hp_nn, hp_sum⟩
    refine ⟨fun s' => Finset.sum_nonneg fun s _ =>
      mul_nonneg (hp_nn s) ((P.transition s).nonneg s'), ?_⟩
    change ∑ s', ∑ s, p s * P.transition s s' = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [show ∀ s, ∑ s', P.transition s s' = 1
      from fun s => (P.transition s).sum_one, mul_one]
    exact hp_sum
  have hstepF_cont : Continuous stepF := by
    apply continuous_pi
    intro s'
    exact continuous_finset_sum _ fun s _ =>
      (continuous_apply s).mul continuous_const
  have hS_cvx := convex_stdSimplex ℝ α
  have hS_cpt : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded
      (isClosed_stdSimplex _ α) (bounded_stdSimplex _)
  have hS_ne : S.Nonempty :=
    ⟨(default : stdSimplex ℝ α).1, (default : stdSimplex ℝ α).2⟩
  let f : C(↥S, ↥S) :=
    ⟨fun ⟨p, hp⟩ => ⟨stepF p, hstepF_maps p hp⟩,
      (hstepF_cont.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨⟨p, hp⟩, hfp⟩ := brouwerFixedPoint S hS_cvx hS_cpt hS_ne f
  refine ⟨⟨p, hp.1, hp.2⟩, ?_⟩
  ext s'
  have := congr_arg (fun x => (x : α → ℝ) s') (Subtype.ext_iff.mp hfp)
  simpa [f, stepF, IsStationary, step] using this

/-! ## Uniqueness under positive transitions -/

/-- **Doeblin minorization constant.** Strictly positive transitions admit a uniform lower bound
`ε ∈ (0, 1]` on every entry, namely the minimum entry over the finite nonempty product index. -/
private lemma exists_min_transition [Nonempty α]
    (hpos : ∀ s s', 0 < P.transition s s') :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s s', ε ≤ P.transition s s' := by
  obtain ⟨a⟩ := ‹Nonempty α›
  have hne : (Finset.univ (α := α) ×ˢ Finset.univ (α := α)).Nonempty :=
    ⟨(a, a), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
  refine ⟨Finset.inf' _ hne (fun p => P.transition p.1 p.2), ?_, ?_, ?_⟩
  · obtain ⟨⟨s₀, s₀'⟩, _, hmin⟩ :=
      Finset.exists_mem_eq_inf' hne (fun p => P.transition p.1 p.2)
    linarith [hpos s₀ s₀', hmin]
  · have hε_le_aa : Finset.inf' _ hne (fun p => P.transition p.1 p.2) ≤ P.transition a a :=
      Finset.inf'_le _ (show (a, a) ∈ Finset.univ ×ˢ Finset.univ from
        Finset.mem_product.mpr ⟨Finset.mem_univ a, Finset.mem_univ a⟩)
    linarith [hε_le_aa,
      Finset.single_le_sum (fun i _ => (P.transition a).nonneg i) (Finset.mem_univ a),
      (P.transition a).sum_one]
  · exact fun s s' => Finset.inf'_le _ (show (s, s') ∈ Finset.univ ×ˢ Finset.univ from
      Finset.mem_product.mpr ⟨Finset.mem_univ s, Finset.mem_univ s'⟩)

/-- **Uniqueness of stationary distribution.** If all transition probabilities are strictly
positive, the stationary distribution is unique. -/
theorem unique_stationary [Nonempty α]
    (hpos : ∀ s s', 0 < P.transition s s') :
    ∀ μ₁ μ₂ : FinDist α,
      P.IsStationary μ₁ → P.IsStationary μ₂ → μ₁ = μ₂ := by
  intro μ₁ μ₂ h₁ h₂
  -- Uniform Doeblin minorization: ε ≤ every transition entry.
  obtain ⟨ε, hε, -, hε_le⟩ := P.exists_min_transition hpos
  -- Stationarity makes the step a TV self-contraction, forcing TV = 0.
  have hcontract :
      tvDist μ₁.pmf μ₂.pmf ≤ (1 - ε) * tvDist μ₁.pmf μ₂.pmf := by
    calc tvDist μ₁.pmf μ₂.pmf
        = tvDist (P.step μ₁).pmf (P.step μ₂).pmf := by rw [h₁, h₂]
      _ = tvDist (fun s' => ∑ s, μ₁.pmf s * P.transition s s')
              (fun s' => ∑ s, μ₂.pmf s * P.transition s s') := rfl
      _ ≤ (1 - Fintype.card α * ε) * tvDist μ₁.pmf μ₂.pmf :=
          tvDist_step_le (fun s s' => P.transition s s')
            (fun s s' => (P.transition s).nonneg s')
            (fun s => (P.transition s).sum_one)
            ε hε hε_le μ₁.pmf μ₂.pmf
            (by rw [μ₁.sum_one, μ₂.sum_one])
      -- Coarsen the sharp `1 - card·ε` factor to `1 - ε` (`card α ≥ 1` since `α` is nonempty).
      _ ≤ (1 - ε) * tvDist μ₁.pmf μ₂.pmf := by
          apply mul_le_mul_of_nonneg_right _ (tvDist_nonneg _ _)
          have hcard1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
          nlinarith [mul_le_mul_of_nonneg_left hcard1 hε.le]
  have htv_zero : tvDist μ₁.pmf μ₂.pmf = 0 := by
    nlinarith [tvDist_nonneg μ₁.pmf μ₂.pmf]
  ext s
  exact congr_fun (tvDist_eq_zero_iff.mp htv_zero) s

/-- The stationary distribution (when it exists). -/
noncomputable def stationaryDist [Nonempty α] : FinDist α :=
  P.exists_stationary.choose

/-- `stationaryDist` is stationary for `P`. -/
lemma stationaryDist_isStationary [Nonempty α] :
    P.IsStationary P.stationaryDist :=
  P.exists_stationary.choose_spec

/-- **Geometric convergence.** For any initial distribution `d₀`, `P.nStep k d₀` converges to the
stationary distribution as `k → ∞`, geometrically, in total-variation/sup metric:
`‖P.nStep k d₀ - μ*‖ ≤ C · ρᵏ` for some `ρ < 1` and `C > 0`. -/
theorem geometric_convergence [Nonempty α]
    (hpos : ∀ s s', 0 < P.transition s s') (d₀ : FinDist α) :
    ∃ (C ρ : ℝ), 0 < C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ k : ℕ, ∀ s : α,
        |(P.nStep k d₀).pmf s - P.stationaryDist.pmf s| ≤ C * ρ ^ k := by
  -- Use Doeblin contraction with the uniform minorization constant ε.
  set μ := P.stationaryDist
  obtain ⟨ε, hε, hε1, hε_le⟩ := P.exists_min_transition hpos
  -- ρ = 1 - ε, C = 2: |d_k(s) - μ(s)| ≤ Σ|d_k - μ| = 2 TV(d_k, μ) ≤ 2(1-ε)^k.
  -- Bridge: the abstract iterate matches nStep.
  set stepF := fun (d : α → ℝ) (s' : α) =>
    ∑ s, d s * P.transition s s'
  have hiter_pmf : ∀ (k : ℕ) (d : FinDist α),
      Nat.iterate stepF k d.pmf = (P.nStep k d).pmf := by
    intro k d; induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, nStep_succ]; rfl
  -- Stationarity under iteration
  have hmu_stat := P.stationaryDist_isStationary
  have hmu_iter : ∀ k, Nat.iterate stepF k μ.pmf = μ.pmf := by
    intro k; rw [hiter_pmf]
    congr 1
    induction k with
    | zero => rfl
    | succ k ih => rw [nStep_succ, ih, hmu_stat]
  -- TV of probability vectors ≤ 1
  have htv_le_one : ∀ (a b : FinDist α), tvDist a.pmf b.pmf ≤ 1 := by
    intro a b; unfold tvDist
    have hle : ∑ i, |a.pmf i - b.pmf i| ≤ 2 :=
      calc ∑ i, |a.pmf i - b.pmf i|
          ≤ ∑ i, (a.pmf i + b.pmf i) :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_le]; constructor <;> linarith [a.nonneg i, b.nonneg i]
        _ = ∑ i, a.pmf i + ∑ i, b.pmf i := Finset.sum_add_distrib
        _ = 2 := by rw [a.sum_one, b.sum_one]; norm_num
    linarith
  refine ⟨2, 1 - ε, by positivity, by linarith, by linarith, fun k s => ?_⟩
  -- Apply iterated Doeblin contraction
  have htv_contract := tvDist_nStep_le
    (fun s s' => P.transition s s')
    (fun s s' => (P.transition s).nonneg s')
    (fun s => (P.transition s).sum_one)
    ε hε hε_le k d₀.pmf μ.pmf
    (by rw [d₀.sum_one, μ.sum_one])
  rw [hiter_pmf, hmu_iter] at htv_contract
  -- `tvDist_nStep_le` delivers the sharp `(1 - card·ε)ᵏ` factor; coarsen it to `(1 - ε)ᵏ`
  -- for the `ρ = 1 - ε` convergence rate. Stochasticity forces `card·ε ≤ 1`, so both factors
  -- lie in `[0,1]`.
  have hcardε_le_one : (Fintype.card α : ℝ) * ε ≤ 1 := by
    obtain ⟨s⟩ := (inferInstance : Nonempty α)
    calc (Fintype.card α : ℝ) * ε = ∑ _s' : α, ε := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ s', P.transition s s' := Finset.sum_le_sum (fun s' _ => hε_le s s')
      _ = 1 := (P.transition s).sum_one
  have hfac_nonneg : (0 : ℝ) ≤ 1 - Fintype.card α * ε := by linarith
  have hfac_le : (1 : ℝ) - Fintype.card α * ε ≤ 1 - ε := by
    have hcard1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
    nlinarith [mul_le_mul_of_nonneg_left hcard1 hε.le]
  replace htv_contract :
      tvDist (P.nStep k d₀).pmf μ.pmf ≤ (1 - ε) ^ k * tvDist d₀.pmf μ.pmf := by
    refine htv_contract.trans ?_
    apply mul_le_mul_of_nonneg_right _ (tvDist_nonneg _ _)
    exact pow_le_pow_left₀ hfac_nonneg hfac_le k
  -- Chain: |component| ≤ Σ|·| = 2 TV ≤ 2(1-ε)^k · TV₀ ≤ 2(1-ε)^k
  calc |(P.nStep k d₀).pmf s - μ.pmf s|
      ≤ ∑ i, |(P.nStep k d₀).pmf i - μ.pmf i| :=
        Finset.single_le_sum (f := fun i =>
          |(P.nStep k d₀).pmf i - μ.pmf i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ s)
    _ = 2 * tvDist (P.nStep k d₀).pmf μ.pmf := by
        unfold tvDist; ring
    _ ≤ 2 * ((1 - ε) ^ k * tvDist d₀.pmf μ.pmf) := by
        linarith
    _ ≤ 2 * ((1 - ε) ^ k * 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (htv_le_one d₀ μ)
          (pow_nonneg (by linarith) k)
    _ = 2 * (1 - ε) ^ k := by ring

/-- **Geometric convergence to a given stationary law.** Same bound as `geometric_convergence`, but
stated against any `μ` the user has already shown stationary, rather than the choice-witness
`stationaryDist`. Since positivity forces uniqueness, the two coincide; this removes the
`stationaryDist`/`unique_stationary` bridge at the call site. -/
theorem geometric_convergence_to [Nonempty α]
    (hpos : ∀ s s', 0 < P.transition s s') {μ : FinDist α} (hμ : P.IsStationary μ)
    (d₀ : FinDist α) :
    ∃ (C ρ : ℝ), 0 < C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ k : ℕ, ∀ s : α,
        |(P.nStep k d₀).pmf s - μ.pmf s| ≤ C * ρ ^ k := by
  rw [P.unique_stationary hpos μ P.stationaryDist hμ P.stationaryDist_isStationary]
  exact P.geometric_convergence hpos d₀

end FiniteMarkovChain

/-! ## Endogenous Markov chains -/

/-- An endogenous Markov chain on a compact state space `[w_min, w_max] × Fin n`, where the
continuous component evolves according to a given continuous policy and the discrete component
follows a Markov chain.

This is the chain induced once a policy has been fixed, e.g. the long-run dynamics of a dynamic
programing model after a policy is computed. The construction and all results below
(`toKernel_isMarkov`, `toKernel_isFeller`, `exists_stationary`) hold for any continuous policy;
optimality is not assumed here. To build this chain from an optimal policy, see the optimality
interface in `Optimization.DynamicProgramming.Core.EndogenousChain`, which discharges the
continuity and range obligations from a dynamic programing optimization. -/
structure EndogenousMarkovChain (n : ℕ) where
  /-- Lower bound on the continuous state. -/
  w_min : ℝ
  /-- Upper bound on the continuous state. -/
  w_max : ℝ
  /-- The bounds are well-ordered. -/
  hw : w_min < w_max
  /-- Transition for the discrete state. -/
  discrete_trans : Fin n → FinDist (Fin n)
  /-- Policy: Next-period continuous state as a function of the current continuous state and the
  next discrete state. Any continuous policy is admissible; it need not be optimal. -/
  policy : ℝ → Fin n → Fin n → ℝ
  /-- Policy maps into the compact interval. -/
  policy_range : ∀ w s s',
    w_min ≤ w → w ≤ w_max →
    w_min ≤ policy w s s' ∧ policy w s s' ≤ w_max
  /-- Policy is continuous in w for each (s, s'). -/
  policy_cont : ∀ s s',
    ContinuousOn (fun w => policy w s s')
      (Set.Icc w_min w_max)

namespace EndogenousMarkovChain

variable {n : ℕ} (E : EndogenousMarkovChain n)

/-- The one-step transition on the discrete component, marginalizing over the continuous state via
a given weighting function. -/
noncomputable def discreteStep (w_weight : Fin n → ℝ)
    (hw_nonneg : ∀ s, 0 ≤ w_weight s) (hw_sum : ∑ s, w_weight s = 1) :
    FinDist (Fin n) where
  pmf s' := ∑ s, w_weight s * (E.discrete_trans s).pmf s'
  nonneg s' := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hw_nonneg s) ((E.discrete_trans s).nonneg s')
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (E.discrete_trans _).sum_one, mul_one]
    exact hw_sum

/-- There exists a stationary distribution for the discrete marginal of the endogenous chain. See
`exists_stationary` for the full product-space result. -/
theorem exists_stationary_discrete [NeZero n] :
    ∃ μ : FinDist (Fin n), ∀ s', μ.pmf s' = ∑ s, μ.pmf s * (E.discrete_trans s).pmf s' := by
  haveI : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  let P : FiniteMarkovChain (Fin n) := ⟨E.discrete_trans⟩
  obtain ⟨μ, hμ⟩ := P.exists_stationary
  exact ⟨μ, fun s' => congr_arg (·.pmf s') hμ.symm⟩

/-! ### Full product-space stationarity -/

open MeasureTheory ProbabilityTheory Set

/-- The policy lifted to the subtype `Icc w_min w_max`. -/
noncomputable def policySubtype (w : Icc E.w_min E.w_max) (s s' : Fin n) :
    Icc E.w_min E.w_max :=
  ⟨E.policy w.1 s s', (E.policy_range w.1 s s' w.2.1 w.2.2).1,
   (E.policy_range w.1 s s' w.2.1 w.2.2).2⟩

/-- The transition measure at state `(w, s)`:
`∑_{s'} discrete_trans(s)(s') • δ_{(policySubtype(w,s,s'), s')}` -/
noncomputable def transitionMeasure (ws : Icc E.w_min E.w_max × Fin n) :
    Measure (Icc E.w_min E.w_max × Fin n) :=
  ∑ s', ENNReal.ofReal ((E.discrete_trans ws.2).pmf s') •
    Measure.dirac (E.policySubtype ws.1 ws.2 s', s')

/-- The Markov kernel on `Icc w_min w_max × Fin n` induced by the endogenous chain's discrete
transition and deterministic policy.

For state `(w, s)`, the kernel is:
`κ(w, s) = ∑_{s'} discrete_trans(s)(s') • δ_{(policy(w,s,s'), s')}` -/
noncomputable def toKernel :
    Kernel (Icc E.w_min E.w_max × Fin n) (Icc E.w_min E.w_max × Fin n) where
  toFun := E.transitionMeasure
  measurable' := by
    -- Factor through Fin n (countable) using measurable_from_prod_countable_left.
    -- For each fixed s : Fin n, the map w ↦ transitionMeasure (w, s) is measurable
    -- because it is a finite sum of constant • (dirac ∘ measurable_function).
    apply measurable_from_prod_countable_left
    intro s
    simp only [transitionMeasure]
    -- For fixed s, the map w ↦ ∑ s', c(s,s') • δ_{(g(w,s,s'), s')} is measurable.
    -- Use Measure.measurable_measure: check pointwise for each measurable set.
    rw [Measure.measurable_measure]
    intro A hA
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro s' _
    -- w ↦ ofReal(c) * δ_{(g(w), s')} A, where c is constant and g is measurable.
    apply Measurable.const_mul
    -- w ↦ δ_{(policySubtype w s s', s')} A is measurable
    have hpol : Measurable (fun w : Icc E.w_min E.w_max => E.policySubtype w s s') := by
      -- policySubtype is continuous (hence measurable) in w.
      -- ContinuousOn → Continuous on subtype → Measurable.
      apply Continuous.measurable
      apply continuous_induced_rng.mpr
      change Continuous (fun w : Icc E.w_min E.w_max => (E.policySubtype w s s').1)
      simp only [policySubtype, Subtype.coe_mk]
      exact (E.policy_cont s s').restrict
    have hm : Measurable (fun w : Icc E.w_min E.w_max =>
        Measure.dirac (E.policySubtype w s s', s')) :=
      Measure.measurable_dirac.comp (hpol.prodMk measurable_const)
    exact Measure.measurable_measure.mp hm A hA

/-- The endogenous kernel is a Markov kernel: Each fiber has total mass one. -/
instance toKernel_isMarkov : IsMarkovKernel E.toKernel := by
  constructor; intro ws
  constructor
  -- total mass = ∑_{s'} ofReal(trans(s)(s')) • 1 = ofReal(∑ trans(s)(s')) = 1
  change E.transitionMeasure ws Set.univ = 1
  simp only [transitionMeasure, Measure.coe_finset_sum,
    Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (E.discrete_trans ws.2).nonneg i)]
  rw [(E.discrete_trans ws.2).sum_one]
  simp

/-- The endogenous kernel is Feller: The map `(w, s) ↦ κ(w, s)` is continuous into
`ProbabilityMeasure`, because the policy is continuous in `w` and the discrete transitions are
locally constant in `s`. -/
theorem toKernel_isFeller : ProbabilityTheory.IsFellerKernel E.toKernel := by
  constructor
  -- Use the NNReal lintegral characterization of weak-* continuity.
  change Continuous E.toKernel.toProbabilityMeasure
  rw [show E.toKernel.toProbabilityMeasure = (fun ws =>
    (⟨E.toKernel ws, inferInstance⟩ : ProbabilityMeasure _)) from rfl]
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_lintegral]
  intro f
  -- Goal: Continuous (fun ws => ∫⁻ x, ↑(f x) ∂(E.toKernel ws))
  change Continuous (fun ws => ∫⁻ x, ↑(f x) ∂E.transitionMeasure ws)
  -- Unfold transitionMeasure and compute lintegral against sum of Diracs.
  simp only [transitionMeasure, lintegral_finset_sum_measure, lintegral_smul_measure,
    lintegral_dirac]
  -- Goal: Continuous (fun ws => ∑ s', c(ws.2,s') • f(g(ws), s'))
  -- Reduce via countable left (Fin n is discrete) to: for each fixed s,
  -- Continuous (fun w => ∑ s', c(s,s') • f(g(w,s,s'), s'))
  apply continuous_finset_sum
  intro s' _
  -- Each summand: ws ↦ ofReal(trans(ws.2)(s')) • ↑(f(policySubtype ws.1 ws.2 s', s'))
  -- On Icc × Fin n (Fin n discrete), continuous ↔ continuous in w for each s.
  rw [continuous_prod_of_discrete_right]
  intro s
  -- For fixed s: Continuous (fun w => ofReal(trans(s)(s')) • ↑(f(policySubtype w s s', s')))
  -- The coefficient is constant. smul for ENNReal is mul.
  simp only [smul_eq_mul]
  -- Continuous (fun w => c * g(w)) where c = ofReal(trans(s)(s'))
  -- policySubtype w s s' is continuous in w
  have hpol : Continuous (fun w : Icc E.w_min E.w_max => E.policySubtype w s s') := by
    apply continuous_induced_rng.mpr
    change Continuous (fun w : Icc E.w_min E.w_max => (E.policySubtype w s s').1)
    simp only [policySubtype, Subtype.coe_mk]
    exact (E.policy_cont s s').restrict
  have hf_cont : Continuous (fun w : Icc E.w_min E.w_max =>
      (↑(f (E.policySubtype w s s', s')) : ENNReal)) :=
    ENNReal.continuous_coe.comp (f.continuous.comp (hpol.prodMk continuous_const))
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp hf_cont

/-- **Existence of stationary distribution on the full product space.** For an endogenous Markov
chain on `[w_min, w_max] × Fin n`, there exists an invariant probability measure on the product. -/
theorem exists_stationary [NeZero n] :
    ∃ μ : ProbDist (Icc E.w_min E.w_max × Fin n),
      Kernel.Invariant E.toKernel μ.toMeasure := by
  have : Nonempty (Icc E.w_min E.w_max × Fin n) :=
    ⟨⟨⟨E.w_min, le_refl _, le_of_lt E.hw⟩, ⟨0, NeZero.pos n⟩⟩⟩
  haveI := E.toKernel_isFeller
  exact exists_invariant_probDist E.toKernel

end EndogenousMarkovChain

end Econlib.Probability
