/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.Bridge.Morphism

/-!
# Existence of a signaling PBE

Constructs a signaling PBE via the Kreps-Wilson trembling-hand approach: Solve perturbed signaling
Kakutani problems at a sequence `ε n ↘ 0`, extract a convergent subsequence in the compact joint
state `(Θ → Δ(Msg)) × (Msg → Δ(Act)) × (Msg → Δ(Θ))`, and bundle the limit directly as a signaling
assessment. The main statement is `exists_signalingPBE`.

The perturbation is agent-normal-form: Each `(sender, θ)` pair optimizes its own, prior-independent
payoff over the ε-perturbed simplex (`perturbedPayoff`, `deviatorSlice`). So the per-ε equilibrium
constrains the sender's strategy at every type — including zero-prior types — and sender optimality
at zero-prior types survives the limit with no Dirac-argmax patch. This matches the
sequential-rationality requirement of `IsSignalingPBE`, whose sender value is per-type and not
weighted by the prior.

The construction is the trembling-hand method: Equilibria of ε-perturbed games accumulate to a
limit assessment, here delivering the headline result `exists_signalingPBE`, a perfect Bayesian
equilibrium whose assessment is the limit of the perturbed equilibria. This construction does *not*
by itself supply a sequential-equilibrium consistency witness: Consistency requires a sequence of
totally-mixed *behavioral* strategies for the full extensive game, and the perturbed signaling
profiles here are agent-normal-form sender/receiver data, not that behavioral witness. The
strengthening to a sequential equilibrium — which constructs the additional receiver trembles
realizing the totally-mixed behavioral sequence — is proved separately, under a full-support prior,
in `Signaling.Bridge.SequentialEquilibrium` (`exists_signalingSequentialEquilibrium`,
`isSignalingSequentialEquilibrium_of_isSignalingPBE`).

## Main definitions

* `SignalingGame.epsSeq`: The ε-sequence `1 / (|Msg| * (n + 2))` driving the trembling-hand limit.
* `SignalingGame.JointState`: The compact joint state space for sender strategies, receiver
  strategies, and beliefs.
* `SignalingGame.profileSenderDist`: Extracts a sender mixed strategy from a perturbed profile.
* `SignalingGame.bundleProfile`: Bundles a per-ε equilibrium into a `JointState` including
  posterior beliefs.

## Main statements

* `SignalingGame.exists_signalingPBE`: Every signaling game admits a signaling PBE.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).
* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling game, perfect bayesian equilibrium, trembling hand, existence, kakutani
-/

@[expose] public noncomputable section

open Econlib.Probability

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ## Existence of a signaling PBE -/

/-! ### Helpers for `exists_signalingPBE` -/

variable (sg : SignalingGame) in
/-- ε-sequence for the trembling-hand limit: `ε n := 1 / (|Msg| * (n + 2))`. -/
noncomputable def epsSeq (n : ℕ) : ℝ :=
  1 / ((Fintype.card sg.Msg : ℝ) * (n + 2))

/-- The number of messages is positive as a real number. -/
lemma card_msg_pos : (0 : ℝ) < (Fintype.card sg.Msg : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- The denominator `|Msg| * (n + 2)` of `epsSeq n` is positive. -/
lemma epsSeq_denom_pos (n : ℕ) :
    (0 : ℝ) < (Fintype.card sg.Msg : ℝ) * ((n : ℝ) + 2) :=
  mul_pos sg.card_msg_pos (by positivity)

/-- `epsSeq n` is positive. -/
lemma epsSeq_pos (n : ℕ) : 0 < sg.epsSeq n :=
  div_pos one_pos (sg.epsSeq_denom_pos n)

/-- `epsSeq n` is nonnegative. -/
lemma epsSeq_nn (n : ℕ) : 0 ≤ sg.epsSeq n := (sg.epsSeq_pos n).le

/-- `epsSeq n` is at most `1 / |Msg|`, the uniform probability. -/
lemma epsSeq_le (n : ℕ) : sg.epsSeq n ≤ 1 / (Fintype.card sg.Msg : ℝ) := by
  unfold epsSeq
  rw [one_div, one_div]
  refine inv_anti₀ sg.card_msg_pos ?_
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  nlinarith [sg.card_msg_pos]

/-- `epsSeq n` tends to `0` as `n → ∞`. -/
lemma epsSeq_tendsto : Filter.Tendsto sg.epsSeq Filter.atTop (nhds 0) := by
  have h_denom_at_top :
      Filter.Tendsto (fun n : ℕ => (Fintype.card sg.Msg : ℝ) * ((n : ℝ) + 2))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop sg.card_msg_pos
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have h_inv := h_denom_at_top.inv_tendsto_atTop
  change Filter.Tendsto (fun n : ℕ => 1 / ((Fintype.card sg.Msg : ℝ) * ((n : ℝ) + 2)))
    Filter.atTop (nhds 0)
  simp_rw [one_div]
  exact h_inv

/-- ε-perturbation of a message distribution toward the tremble floor: `(1 - ε|Msg|)·y(m) + ε`
entrywise. Lies in `PerturbedSimplex ε` for `0 < ε ≤ 1/|Msg|` (`perturbApprox_mem`) and tends to
`y` entrywise as `ε → 0` (`perturbApprox_tendsto`); used to approximate arbitrary sender deviations
from inside the perturbed simplex. -/
private def perturbApprox (y : FinDist sg.Msg) (ε : ℝ) (m : sg.Msg) : ℝ :=
  (1 - ε * (Fintype.card sg.Msg : ℝ)) * y.pmf m + ε

private lemma perturbApprox_mem (y : FinDist sg.Msg) {ε : ℝ} (hε : 0 < ε)
    (hε_le : ε ≤ 1 / (Fintype.card sg.Msg : ℝ)) :
    sg.perturbApprox y ε ∈ PerturbedSimplex (α := sg.Msg) ε := by
  have hN_pos : (0 : ℝ) < (Fintype.card sg.Msg : ℝ) := sg.card_msg_pos
  have h_eps_N_le_one : ε * (Fintype.card sg.Msg : ℝ) ≤ 1 := by
    have h_mul : ε * (Fintype.card sg.Msg : ℝ) ≤
        (1 / (Fintype.card sg.Msg : ℝ)) * (Fintype.card sg.Msg : ℝ) :=
      mul_le_mul_of_nonneg_right hε_le hN_pos.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hN_pos)] at h_mul
  have h_one_minus_nn : 0 ≤ 1 - ε * (Fintype.card sg.Msg : ℝ) := by linarith
  have h_entry_nn (m : sg.Msg) : 0 ≤ sg.perturbApprox y ε m :=
    add_nonneg (mul_nonneg h_one_minus_nn (y.nonneg m)) hε.le
  refine ⟨⟨h_entry_nn, ?_⟩, fun m => ?_⟩
  · unfold perturbApprox
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, y.sum_one, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · have h_shift_nn : 0 ≤ (1 - ε * (Fintype.card sg.Msg : ℝ)) * y.pmf m :=
      mul_nonneg h_one_minus_nn (y.nonneg m)
    change ε ≤ (1 - ε * (Fintype.card sg.Msg : ℝ)) * y.pmf m + ε
    linarith

private lemma perturbApprox_tendsto (y : FinDist sg.Msg) {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) (m : sg.Msg) :
    Filter.Tendsto (fun n => sg.perturbApprox y (e n) m) Filter.atTop (nhds (y.pmf m)) := by
  have h_one_minus :
      Filter.Tendsto (fun n => 1 - e n * (Fintype.card sg.Msg : ℝ)) Filter.atTop
        (nhds (1 - 0 * (Fintype.card sg.Msg : ℝ))) :=
    tendsto_const_nhds.sub (he.mul_const _)
  unfold perturbApprox
  simpa using (h_one_minus.mul_const (y.pmf m)).add he

/-! ### Per-step perturbed equilibrium -/

/-- At each step `n`, the perturbed Kakutani data admits an equilibrium. This packages all steps
into a single sequence `σ : ℕ → ...` with the equilibrium property at each index. -/
lemma exists_perturbed_seq (sg : SignalingGame) :
    ∃ σ : ∀ n : ℕ, (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice (sg.epsSeq n) d),
      ∀ n : ℕ, (sg.toPerturbedNashExistenceData (sg.epsSeq n)
        (sg.epsSeq_nn n) (sg.epsSeq_le n)).toEquilibriumProblem.IsEquilibrium (σ n) := by
  classical
  have h_each : ∀ n : ℕ, ∃ σ_n : (d : sg.SignalingDeviator) →
      ↑(sg.deviatorSlice (sg.epsSeq n) d),
      (sg.toPerturbedNashExistenceData (sg.epsSeq n)
        (sg.epsSeq_nn n) (sg.epsSeq_le n)).toEquilibriumProblem.IsEquilibrium σ_n :=
    fun n => (sg.toPerturbedNashExistenceData (sg.epsSeq n)
      (sg.epsSeq_nn n) (sg.epsSeq_le n)).exists_equilibrium
  exact ⟨fun n => (h_each n).choose, fun n => (h_each n).choose_spec⟩

/-! ### Joint state space for the trembling-hand sequence -/

variable (sg : SignalingGame) in
/-- The joint state space: Sender raw strategies × receiver raw strategies × belief system. We pack
beliefs explicitly so we can extract subsequence-limits of posteriors at off-path messages; at
on-path messages, continuity will force the belief-limit to coincide with the posterior of the
limit sender strategy. -/
abbrev JointState : Type :=
  (sg.Theta → stdSimplex ℝ sg.Msg) ×
  (sg.Msg → stdSimplex ℝ sg.Act) ×
  (sg.Msg → FinDist sg.Theta)

/-- The joint state space is compact, as a finite product of compact simplices. -/
lemma jointState_compact :
    IsCompact (Set.univ : Set (JointState sg)) := by
  haveI : CompactSpace (stdSimplex ℝ sg.Msg) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ _)
  haveI : CompactSpace (stdSimplex ℝ sg.Act) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ _)
  exact isCompact_univ

/-- Sender strategy extracted from a perturbed profile as a `SenderMixedStrategy`
(`FinDist Msg`). -/
noncomputable def profileSenderDist (sg : SignalingGame) {ε : ℝ}
    (σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)) :
    sg.SenderMixedStrategy :=
  fun θ => FinDist.ofSimplex ⟨(σ (.sender θ)).val, (σ (.sender θ)).property.1⟩

/-- For a profile in the ε-perturbed slices with `ε > 0`, every message has positive marginal
probability under the extracted sender strategy. -/
private lemma marginalProb_pos_of_perturbed {ε : ℝ} (hε : 0 < ε)
    (σ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d)) (m : sg.Msg) :
    0 < sg.marginalProb (sg.profileSenderDist σ) m :=
  lt_of_lt_of_le hε
    (sg.marginalProbRaw_ge_eps_of_perturbed hε.le
      (fun θ' => (sg.profileSenderDist σ θ').pmf)
      (fun θ' => (σ (.sender θ')).property) m)

/-- Bundle a per-ε equilibrium profile into a joint state including the posterior beliefs. -/
noncomputable def bundleProfile (sg : SignalingGame) (n : ℕ)
    (σ_n : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice (sg.epsSeq n) d)) :
    JointState sg :=
  (fun θ => ⟨(σ_n (.sender θ)).val, (σ_n (.sender θ)).property.1⟩,
   fun m => σ_n (.receiver m),
   fun m => sg.posterior (sg.profileSenderDist σ_n) m)

/-- Closed form of the bundled belief at any message: With a positive perturbation every message is
on-path, so the bundled posterior is the Bayes quotient. -/
private lemma bundleProfile_belief_pmf (n : ℕ)
    (σ_n : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice (sg.epsSeq n) d)) (m : sg.Msg)
    (θ : sg.Theta) :
    ((sg.bundleProfile n σ_n).2.2 m).pmf θ =
      sg.prior.pmf θ * ((sg.bundleProfile n σ_n).1 θ).val m /
        sg.marginalProb (sg.profileSenderDist σ_n) m :=
  sg.posterior_apply (sg.profileSenderDist σ_n) m θ
    (sg.marginalProb_pos_of_perturbed (sg.epsSeq_pos n) σ_n m)

/-- Evaluate the perturbed Kakutani payoff at a receiver deviator: For any profile `τ` whose sender
slots agree with `σ`'s, the payoff factors as the (positive) sender marginal times the
`τ`-receiver-weighted posterior expected payoff. Instantiated at `τ := σ` and at a receiver-slot
update of `σ`. -/
private lemma perturbedPayoff_receiver_eq {ε : ℝ} (hε : 0 < ε)
    (σ τ : (d : sg.SignalingDeviator) → ↑(sg.deviatorSlice ε d))
    (hτ : ∀ θ, τ (.sender θ) = σ (.sender θ)) (m : sg.Msg) :
    sg.perturbedPayoff ε τ (.receiver m) =
      sg.marginalProb (sg.profileSenderDist σ) m *
        ∑ a : sg.Act, (τ (.receiver m)).val a *
          ∑ θ : sg.Theta, (sg.posterior (sg.profileSenderDist σ) m).pmf θ *
            sg.payoff .receiver θ m a := by
  have h_marg_pos := sg.marginalProb_pos_of_perturbed hε σ m
  have h_marg_ne := ne_of_gt h_marg_pos
  -- The posterior numerator rescales to marginal × posterior-weighted payoff.
  have h_PN (a : sg.Act) :
      sg.posteriorNumerator (sg.profileSenderRaw ε τ) m a =
        sg.marginalProb (sg.profileSenderDist σ) m *
          ∑ θ : sg.Theta, (sg.posterior (sg.profileSenderDist σ) m).pmf θ *
            sg.payoff .receiver θ m a := by
    unfold posteriorNumerator profileSenderRaw
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [sg.posterior_apply _ m θ h_marg_pos, hτ θ,
      show (sg.profileSenderDist σ θ).pmf = (σ (.sender θ)).val from rfl]
    field_simp
  unfold perturbedPayoff profileReceiverRaw
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [h_PN a]; ring

/-- Every signaling game admits a perfect Bayesian equilibrium. -/
theorem exists_signalingPBE (sg : SignalingGame) :
    ∃ a : sg.SignalingAssessment, sg.IsSignalingPBE a := by
  classical
  -- Solve the perturbed problems at `ε n ↘ 0`, bundle the solutions into the compact
  -- joint state, and extract a subsequence `φ` converging to `(σS_lim, σR_lim, μ_lim)`.
  obtain ⟨σ, hσ⟩ := sg.exists_perturbed_seq
  let B : ℕ → JointState sg := fun n => sg.bundleProfile n (σ n)
  obtain ⟨⟨σS_lim, σR_lim, μ_lim⟩, _, φ, hφ_mono, hφ_lim⟩ :=
    sg.jointState_compact.tendsto_subseq (fun n => Set.mem_univ (B n))
  have hS_lim : Filter.Tendsto (fun n => (B (φ n)).1) Filter.atTop (nhds σS_lim) :=
    (continuous_fst.tendsto _).comp hφ_lim
  have hRμ_lim :
      Filter.Tendsto (fun n => (B (φ n)).2) Filter.atTop (nhds (σR_lim, μ_lim)) :=
    (continuous_snd.tendsto _).comp hφ_lim
  have hR_lim : Filter.Tendsto (fun n => (B (φ n)).2.1) Filter.atTop (nhds σR_lim) :=
    (continuous_fst.tendsto _).comp hRμ_lim
  have hμ_lim : Filter.Tendsto (fun n => (B (φ n)).2.2) Filter.atTop (nhds μ_lim) :=
    (continuous_snd.tendsto _).comp hRμ_lim
  let σS_dist : sg.SenderMixedStrategy := fun θ => FinDist.ofSimplex (σS_lim θ)
  let σR_dist : sg.ReceiverMixedStrategy := fun m => FinDist.ofSimplex (σR_lim m)
  -- Pointwise continuity of evaluation: hoisted for use in both Bayes and rationality branches.
  have hSθ (θ : sg.Theta) :
      Filter.Tendsto (fun n => (B (φ n)).1 θ) Filter.atTop (nhds (σS_lim θ)) :=
    ((continuous_apply θ).tendsto _).comp hS_lim
  have hSθm (θ : sg.Theta) (m' : sg.Msg) :
      Filter.Tendsto (fun n => ((B (φ n)).1 θ).val m') Filter.atTop
        (nhds ((σS_lim θ).val m')) :=
    (((continuous_apply m').comp continuous_subtype_val).tendsto _).comp (hSθ θ)
  have hRm (m' : sg.Msg) :
      Filter.Tendsto (fun n => (B (φ n)).2.1 m') Filter.atTop (nhds (σR_lim m')) :=
    ((continuous_apply m').tendsto _).comp hR_lim
  have hRma (m' : sg.Msg) (a : sg.Act) :
      Filter.Tendsto (fun n => ((B (φ n)).2.1 m').val a) Filter.atTop
        (nhds ((σR_lim m').val a)) :=
    (((continuous_apply a).comp continuous_subtype_val).tendsto _).comp (hRm m')
  have hμθ (m' : sg.Msg) (θ : sg.Theta) :
      Filter.Tendsto (fun n => ((B (φ n)).2.2 m').pmf θ) Filter.atTop
        (nhds ((μ_lim m').pmf θ)) :=
    ((FinDist.continuous_pmf_apply θ).tendsto _).comp
      (((continuous_apply m').tendsto _).comp hμ_lim)
  -- The limit triple is the candidate assessment; Bayes consistency and rationality are the two
  -- remaining goals.
  refine ⟨⟨σS_dist, σR_dist, μ_lim⟩, ?_, ?_⟩
  · -- Bayes consistency: at a message with positive limit marginal, each perturbed
    -- belief is the Bayes quotient of its perturbed profile (every message is on-path), and the
    -- quotients converge to the Bayes quotient of the limit. Uniqueness of limits identifies
    -- `μ_lim m` with the posterior of `σS_dist`.
    intro m hm
    have h_marg_tendsto :
        Filter.Tendsto (fun n => sg.marginalProb (sg.profileSenderDist (σ (φ n))) m)
          Filter.atTop (nhds (sg.marginalProb σS_dist m)) := by
      unfold marginalProb
      refine tendsto_finset_sum _ (fun θ _ => ?_)
      exact (hSθm θ m).const_mul _
    apply FinDist.ext
    intro θ
    rw [sg.posterior_apply σS_dist m θ hm]
    have h_posterior_eq (n : ℕ) :
        ((B (φ n)).2.2 m).pmf θ =
        sg.prior.pmf θ * ((B (φ n)).1 θ).val m /
          sg.marginalProb (sg.profileSenderDist (σ (φ n))) m :=
      sg.bundleProfile_belief_pmf (φ n) (σ (φ n)) m θ
    have h_lhs_tendsto :
        Filter.Tendsto (fun n => ((B (φ n)).2.2 m).pmf θ) Filter.atTop
          (nhds (sg.prior.pmf θ * (σS_dist θ).pmf m / sg.marginalProb σS_dist m)) := by
      simp_rw [h_posterior_eq]
      exact ((hSθm θ m).const_mul _).div h_marg_tendsto (ne_of_gt hm)
    exact tendsto_nhds_unique (hμθ m θ) h_lhs_tendsto
  · -- Rationality against unilateral swaps, split into the sender and receiver deviator cases.
    intro d a' hswap
    rcases d with θ | m
    · -- Sender optimality at `θ`: the swap deviation `y` need not respect the tremble
      -- floor, so approximate it by `y_apx n` inside the `ε (φ n)`-perturbed simplex, compare
      -- against the perturbed equilibrium at each step, and pass to the limit.
      obtain ⟨hR_eq, _hμ_eq, _hS_other⟩ := hswap
      set y : FinDist sg.Msg := a'.senderStrategy θ
      let P_lim : sg.Msg → ℝ := fun m =>
        ∑ a : sg.Act, (σR_dist m).pmf a * sg.payoff .sender θ m a
      let P_seq : ℕ → sg.Msg → ℝ := fun n m =>
        ∑ a : sg.Act, ((B (φ n)).2.1 m).val a * sg.payoff .sender θ m a
      have hP_tendsto (m : sg.Msg) :
          Filter.Tendsto (fun n => P_seq n m) Filter.atTop (nhds (P_lim m)) :=
        tendsto_finset_sum _ (fun a _ => (hRma m a).mul_const _)
      -- Unfold the swap-payoff goal to weighted-sum form; the swap leaves the receiver
      -- strategy unchanged.
      change (∑ m : sg.Msg, (σS_dist θ).pmf m * sg.senderExpectedPayoff σR_dist θ m) ≥
        (∑ m : sg.Msg, (a'.senderStrategy θ).pmf m *
          sg.senderExpectedPayoff a'.receiverStrategy θ m)
      rw [show a'.receiverStrategy = σR_dist from hR_eq]
      -- Approximate `y` from inside the perturbed simplex by its tremble-floor perturbation.
      let y_apx : ℕ → sg.Msg → ℝ := fun n => sg.perturbApprox y (sg.epsSeq (φ n))
      have h_y_apx_mem (n : ℕ) :
          y_apx n ∈ PerturbedSimplex (α := sg.Msg) (sg.epsSeq (φ n)) :=
        sg.perturbApprox_mem y (sg.epsSeq_pos (φ n)) (sg.epsSeq_le (φ n))
      have h_y_apx_tendsto (m : sg.Msg) :
          Filter.Tendsto (fun n => y_apx n m) Filter.atTop (nhds (y.pmf m)) :=
        sg.perturbApprox_tendsto y (sg.epsSeq_tendsto.comp hφ_mono.tendsto_atTop) m
      have h_seq_ineq (n : ℕ) :
          (∑ m : sg.Msg, y_apx n m * P_seq n m) ≤
          (∑ m : sg.Msg, (sg.profileSenderDist (σ (φ n)) θ).pmf m * P_seq n m) := by
        have h_iso := hσ (φ n) (.sender θ)
          (Function.update (σ (φ n)) (.sender θ) ⟨y_apx n, h_y_apx_mem n⟩)
          ⟨⟨y_apx n, h_y_apx_mem n⟩, rfl⟩
        -- Up to defeq, the only step is evaluating the update at its own key.
        change (∑ m : sg.Msg, (sg.profileSenderDist (σ (φ n)) θ).pmf m * P_seq n m) ≥
          ∑ m : sg.Msg,
            (Function.update (σ (φ n)) (.sender θ) ⟨y_apx n, h_y_apx_mem n⟩
              (.sender θ)).val m * P_seq n m at h_iso
        rw [Function.update_self] at h_iso
        exact h_iso
      have h_lhs_lim :
          Filter.Tendsto (fun n => ∑ m : sg.Msg, y_apx n m * P_seq n m) Filter.atTop
            (nhds (∑ m : sg.Msg, y.pmf m * P_lim m)) :=
        tendsto_finset_sum _ (fun m _ => (h_y_apx_tendsto m).mul (hP_tendsto m))
      have h_rhs_lim :
          Filter.Tendsto (fun n => ∑ m : sg.Msg, (sg.profileSenderDist (σ (φ n)) θ).pmf m *
            P_seq n m) Filter.atTop
            (nhds (∑ m : sg.Msg, (σS_dist θ).pmf m * P_lim m)) :=
        tendsto_finset_sum _ (fun m _ => (hSθm θ m).mul (hP_tendsto m))
      exact le_of_tendsto_of_tendsto' h_lhs_lim h_rhs_lim h_seq_ineq
    · -- Receiver optimality at `m`: at each step the equilibrium response argmaxes the
      -- `posteriorNumerator`-weighted payoff; cancelling the positive marginal turns this into
      -- optimality for the posterior-weighted payoff `Q_seq`, which passes to the limit.
      obtain ⟨_hS_eq, hμ_eq, _hR_other⟩ := hswap
      set z : FinDist sg.Act := a'.receiverStrategy m
      let Q_lim : sg.Act → ℝ := fun act =>
        ∑ θ : sg.Theta, (μ_lim m).pmf θ * sg.payoff .receiver θ m act
      let Q_seq : ℕ → sg.Act → ℝ := fun n act =>
        ∑ θ : sg.Theta, ((B (φ n)).2.2 m).pmf θ * sg.payoff .receiver θ m act
      have hQ_tendsto (act : sg.Act) :
          Filter.Tendsto (fun n => Q_seq n act) Filter.atTop (nhds (Q_lim act)) :=
        tendsto_finset_sum _ (fun θ _ => (hμθ m θ).mul_const _)
      have h_marg_pos_n (n : ℕ) :
          0 < sg.marginalProb (sg.profileSenderDist (σ (φ n))) m :=
        sg.marginalProb_pos_of_perturbed (sg.epsSeq_pos (φ n)) (σ (φ n)) m
      have h_z_slice (n : ℕ) :
          z.pmf ∈ sg.deviatorSlice (sg.epsSeq (φ n)) (.receiver m) :=
        (⟨z.nonneg, z.sum_one⟩ : z.pmf ∈ stdSimplex ℝ sg.Act)
      have h_seq_ineq (n : ℕ) :
          (∑ act : sg.Act, z.pmf act * Q_seq n act) ≤
          (∑ act : sg.Act, ((B (φ n)).2.1 m).val act * Q_seq n act) := by
        have h_iso :
            sg.perturbedPayoff (sg.epsSeq (φ n))
              (Function.update (σ (φ n)) (.receiver m) ⟨z.pmf, h_z_slice n⟩) (.receiver m) ≤
            sg.perturbedPayoff (sg.epsSeq (φ n)) (σ (φ n)) (.receiver m) :=
          hσ (φ n) (.receiver m)
            (Function.update (σ (φ n)) (.receiver m) ⟨z.pmf, h_z_slice n⟩)
            ⟨⟨z.pmf, h_z_slice n⟩, rfl⟩
        rw [sg.perturbedPayoff_receiver_eq (sg.epsSeq_pos (φ n)) (σ (φ n)) _
              (fun θ' => Function.update_of_ne (by intro h; nomatch h) _ _) m,
            sg.perturbedPayoff_receiver_eq (sg.epsSeq_pos (φ n)) (σ (φ n)) (σ (φ n))
              (fun _ => rfl) m,
            Function.update_self] at h_iso
        exact le_of_mul_le_mul_left h_iso (h_marg_pos_n n)
      have h_lhs_lim :
          Filter.Tendsto (fun n => ∑ act : sg.Act, z.pmf act * Q_seq n act) Filter.atTop
            (nhds (∑ act : sg.Act, z.pmf act * Q_lim act)) :=
        tendsto_finset_sum _ (fun act _ => (hQ_tendsto act).const_mul _)
      have h_rhs_lim :
          Filter.Tendsto (fun n => ∑ act : sg.Act, ((B (φ n)).2.1 m).val act * Q_seq n act)
            Filter.atTop
            (nhds (∑ act : sg.Act, (σR_lim m).val act * Q_lim act)) :=
        tendsto_finset_sum _ (fun act _ => (hRma m act).mul (hQ_tendsto act))
      -- Unfold the swap-payoff goal to weighted-sum form; the swap leaves the belief unchanged.
      change (∑ θ : sg.Theta, (μ_lim m).pmf θ *
          ∑ act : sg.Act, (σR_dist m).pmf act * sg.payoff .receiver θ m act) ≥
        ∑ θ : sg.Theta, (a'.belief m).pmf θ *
          ∑ act : sg.Act, (a'.receiverStrategy m).pmf act * sg.payoff .receiver θ m act
      rw [show a'.belief = μ_lim from hμ_eq]
      -- Swap order of summation on each side to bring into the form `∑ act, ν act * Q_lim act`.
      have h_swap (ν : FinDist sg.Act) :
          (∑ θ : sg.Theta, (μ_lim m).pmf θ *
            ∑ act : sg.Act, ν.pmf act * sg.payoff .receiver θ m act) =
          ∑ act : sg.Act, ν.pmf act * Q_lim act := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun act _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun θ _ => ?_)
        ring
      rw [h_swap (σR_dist m), h_swap (a'.receiverStrategy m)]
      exact le_of_tendsto_of_tendsto' h_lhs_lim h_rhs_lim h_seq_ineq

end SignalingGame

end Econlib.GameTheory
