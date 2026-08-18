/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.SequentialEquilibrium
public import Econlib.GameTheory.Signaling.Bridge.Existence

/-!
# Signaling sequential equilibrium

This file proves sequential-equilibrium results for finite signaling games. The main theorem shows
that, under a full-support prior, every signaling PBE is a Kreps-Wilson sequential equilibrium in
the encoded extensive game; consequently every full-support signaling game admits a sequential
equilibrium. The file also proves the converse obstruction: A zero-prior sender type rules out
signaling sequential equilibrium.

## Main definitions

* `SignalingGame.IsSignalingSequentialEquilibrium`: The embedded assessment is a sequential
  equilibrium of the encoded extensive game (defined via the extensive-form notion, not in
  parallel).
* `SignalingGame.senderTremble` / `receiverTremble`: The trembling-hand perturbations.

## Main statements

* `SignalingGame.hasConsistentBeliefs_of_signalingBayesConsistent`: Bayes-consistent beliefs embed
  as Kreps–Wilson consistent beliefs (the consistency half of the coincidence).
* `SignalingGame.isSignalingSequentialEquilibrium_of_isSignalingPBE`: Every signaling PBE is a
  sequential equilibrium (Fudenberg–Tirole coincidence).
* `SignalingGame.exists_signalingSequentialEquilibrium`: Every full-support signaling game admits a
  sequential equilibrium.
* `SignalingGame.not_exists_isSignalingSequentialEquilibrium_of_prior_zero`: A signaling game with
  a zero-prior type admits no sequential equilibrium, so full support is necessary as well as
  sufficient.

## Notes

Every result here assumes a full-support prior `∀ θ, 0 < sg.prior.pmf θ`. This is not incidental:
The sender's own-type information set `[type θ]` has reach probability `prior θ` under every
behavioral strategy (nature's prior is a fixed chance node, not perturbed by trembles), so at a
zero-prior type that node is unreachable yet carries belief `1`, which no trembled posterior can
match. Hence `HasConsistentBeliefs` — and so sequential equilibrium — fails to exist without full
support. Full support is the standard signaling-game assumption. The necessity direction is proved
below as `not_exists_isSignalingSequentialEquilibrium_of_prior_zero`.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).
* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling game, sequential equilibrium, perfect Bayesian equilibrium, Fudenberg-Tirole, Kreps-Wilson
-/

@[expose] public noncomputable section

open Econlib.Probability

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ### A normalizing constructor for `FinDist` -/

/-- Build a `FinDist` from a nonnegative weight function with positive total mass by dividing
through by the total. -/
noncomputable def normPos {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hpos : 0 < ∑ a, w a) : FinDist α where
  pmf a := w a / (∑ b, w b)
  nonneg a := div_nonneg (hw a) hpos.le
  sum_one := by rw [← Finset.sum_div, div_self hpos.ne']

/-- The pmf of `normPos w hw hpos` at `a` is `w a / ∑ b, w b`. -/
@[simp] lemma normPos_pmf {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hpos : 0 < ∑ a, w a) (a : α) :
    (normPos w hw hpos).pmf a = w a / (∑ b, w b) := rfl

/-! ### The off-path tremble

For a target assessment `a`, the sender of type `θ` plays the perturbed strategy
`senderTremble a n θ`: The equilibrium weight plus a first-order nudge toward
`a.belief m / prior θ` that steers the off-path posterior toward `a.belief m`, plus a second-order
positive floor. -/

/-- Tremble-rate sequence `rate n := 1 / (n + 1)`. -/
noncomputable def trembleRate (n : ℕ) : ℝ := 1 / (n + 1)

/-- The tremble rate is strictly positive. -/
lemma trembleRate_pos (n : ℕ) : 0 < trembleRate n := by
  unfold trembleRate; positivity

/-- The tremble rate converges to `0`. -/
lemma trembleRate_tendsto : Filter.Tendsto trembleRate Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Off-path steering weight: `a.belief m θ / prior θ` when `θ` has positive prior, else `0`. The
guard keeps the definition total; the matching lemmas assume a full-support prior, under which the
guard is always taken. -/
noncomputable def tWeight (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) : ℝ :=
  if 0 < sg.prior.pmf θ then (a.belief m).pmf θ / sg.prior.pmf θ else 0

/-- The off-path steering weight is nonnegative. -/
lemma tWeight_nonneg (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) :
    0 ≤ sg.tWeight a θ m := by
  unfold tWeight
  split_ifs with h
  · exact div_nonneg ((a.belief m).nonneg θ) h.le
  · exact le_rfl

/-- Unnormalized sender tremble weight at step `n`. -/
noncomputable def senderWeight (a : sg.SignalingAssessment) (n : ℕ) (θ : sg.Theta) (m : sg.Msg) :
    ℝ :=
  (a.senderStrategy θ).pmf m + trembleRate n * sg.tWeight a θ m + (trembleRate n) ^ 2

/-- The unnormalized sender tremble weight is strictly positive. -/
lemma senderWeight_pos (a : sg.SignalingAssessment) (n : ℕ) (θ : sg.Theta) (m : sg.Msg) :
    0 < sg.senderWeight a n θ m := by
  have hbase : 0 ≤ (a.senderStrategy θ).pmf m := (a.senderStrategy θ).nonneg m
  have hnudge : 0 ≤ trembleRate n * sg.tWeight a θ m :=
    mul_nonneg (trembleRate_pos n).le (sg.tWeight_nonneg a θ m)
  have hfloor : 0 < (trembleRate n) ^ 2 := pow_pos (trembleRate_pos n) 2
  unfold senderWeight; linarith

/-- The total sender tremble weight `∑_m senderWeight a n θ m` is positive. -/
lemma senderWeight_sum_pos (a : sg.SignalingAssessment) (n : ℕ) (θ : sg.Theta) :
    0 < ∑ m, sg.senderWeight a n θ m :=
  Finset.sum_pos (fun m _ => sg.senderWeight_pos a n θ m) ⟨default, Finset.mem_univ _⟩

/-- The normalized sender tremble at type `θ`, step `n`. -/
noncomputable def senderTremble (a : sg.SignalingAssessment) (n : ℕ) (θ : sg.Theta) :
    FinDist sg.Msg :=
  normPos (sg.senderWeight a n θ) (fun m => (sg.senderWeight_pos a n θ m).le)
    (sg.senderWeight_sum_pos a n θ)

/-- The sender tremble assigns positive probability to every message. -/
lemma senderTremble_pos (a : sg.SignalingAssessment) (n : ℕ) (θ : sg.Theta) (m : sg.Msg) :
    0 < (sg.senderTremble a n θ).pmf m := by
  rw [senderTremble, normPos_pmf]
  exact div_pos (sg.senderWeight_pos a n θ m) (sg.senderWeight_sum_pos a n θ)

/-- The sender tremble bundled as a mixed strategy. -/
noncomputable def senderTrembleStrat (a : sg.SignalingAssessment) (n : ℕ) :
    sg.SenderMixedStrategy := fun θ => sg.senderTremble a n θ

/-! ### Convergence of the tremble -/

/-- The unnormalized sender tremble weight converges to the equilibrium weight. -/
lemma senderWeight_tendsto (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) :
    Filter.Tendsto (fun n => sg.senderWeight a n θ m) Filter.atTop
      (nhds ((a.senderStrategy θ).pmf m)) := by
  have h1 : Filter.Tendsto (fun n => trembleRate n * sg.tWeight a θ m) Filter.atTop (nhds 0) := by
    simpa using trembleRate_tendsto.mul_const (sg.tWeight a θ m)
  have h2 : Filter.Tendsto (fun n => (trembleRate n) ^ 2) Filter.atTop (nhds 0) := by
    simpa using trembleRate_tendsto.pow 2
  simpa [senderWeight] using
    ((tendsto_const_nhds (x := (a.senderStrategy θ).pmf m)).add h1).add h2

/-- The per-type normalizer converges to `1`. -/
lemma senderWeight_sum_tendsto (a : sg.SignalingAssessment) (θ : sg.Theta) :
    Filter.Tendsto (fun n => ∑ m, sg.senderWeight a n θ m) Filter.atTop (nhds 1) := by
  have h := tendsto_finset_sum Finset.univ (fun m _ => sg.senderWeight_tendsto a θ m)
  rwa [(a.senderStrategy θ).sum_one] at h

/-- The normalized sender tremble converges pointwise to the equilibrium sender strategy. -/
lemma senderTremble_tendsto (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) :
    Filter.Tendsto (fun n => (sg.senderTremble a n θ).pmf m) Filter.atTop
      (nhds ((a.senderStrategy θ).pmf m)) := by
  simp_rw [senderTremble, normPos_pmf]
  simpa using (sg.senderWeight_tendsto a θ m).div (sg.senderWeight_sum_tendsto a θ)
    (by norm_num)

/-- Under a full-support prior, the posterior induced by the sender tremble converges to the target
belief `a.belief m` at every message. -/
lemma senderTremble_posterior_tendsto (a : sg.SignalingAssessment)
    (hfull : ∀ θ, 0 < sg.prior.pmf θ) (hcons : sg.signalingBayesConsistent a)
    (m : sg.Msg) (θ : sg.Theta) :
    Filter.Tendsto (fun n => (sg.posterior (sg.senderTrembleStrat a n) m).pmf θ) Filter.atTop
      (nhds ((a.belief m).pmf θ)) := by
  -- `g n θ'` is the unnormalized joint mass `prior θ' · trembled likelihood at m`.
  set g : ℕ → sg.Theta → ℝ :=
    fun n θ' => sg.prior.pmf θ' * (sg.senderTremble a n θ').pmf m with hg_def
  have hmarg_eq : ∀ n, sg.marginalProb (sg.senderTrembleStrat a n) m = ∑ θ', g n θ' := by
    intro n; rfl
  have hmarg_pos : ∀ n, 0 < sg.marginalProb (sg.senderTrembleStrat a n) m := by
    intro n
    exact sg.marginalProb_pos (hfull default) (sg.senderTremble_pos a n default m)
  have hpost_ratio : ∀ n,
      (sg.posterior (sg.senderTrembleStrat a n) m).pmf θ = g n θ / (∑ θ', g n θ') := by
    intro n
    rw [sg.posterior_apply (sg.senderTrembleStrat a n) m θ (hmarg_pos n), hmarg_eq n]
    rfl
  simp_rw [hpost_ratio]
  by_cases hon : 0 < sg.marginalProb a.senderStrategy m
  · -- On-path: Bayes consistency fixes the target belief at the Bayesian ratio.
    have hnum : Filter.Tendsto (fun n => g n θ) Filter.atTop
        (nhds (sg.prior.pmf θ * (a.senderStrategy θ).pmf m)) :=
      (sg.senderTremble_tendsto a θ m).const_mul (sg.prior.pmf θ)
    have hden : Filter.Tendsto (fun n => ∑ θ', g n θ') Filter.atTop
        (nhds (sg.marginalProb a.senderStrategy m)) := by
      have h := tendsto_finset_sum (Finset.univ : Finset sg.Theta)
        (fun θ' _ => (sg.senderTremble_tendsto a θ' m).const_mul (sg.prior.pmf θ'))
      rwa [show (∑ θ', sg.prior.pmf θ' * (a.senderStrategy θ').pmf m)
        = sg.marginalProb a.senderStrategy m from rfl] at h
    have htarget : (a.belief m).pmf θ
        = sg.prior.pmf θ * (a.senderStrategy θ).pmf m / sg.marginalProb a.senderStrategy m := by
      rw [hcons m hon, sg.posterior_apply a.senderStrategy m θ hon]
    rw [htarget]
    exact hnum.div hden hon.ne'
  · -- Off-path: every equilibrium likelihood at `m` is zero, so the first-order nudge dominates.
    have hmarg_zero : sg.marginalProb a.senderStrategy m = 0 := by
      refine le_antisymm (le_of_not_gt hon) ?_
      rw [sg.marginalProb_eq_sum]
      exact Finset.sum_nonneg
        (fun θ' _ => mul_nonneg (sg.prior.nonneg θ') ((a.senderStrategy θ').nonneg m))
    have h_aSS_zero : ∀ θ', (a.senderStrategy θ').pmf m = 0 := by
      intro θ'
      have hsum_zero : ∑ θ'', sg.prior.pmf θ'' * (a.senderStrategy θ'').pmf m = 0 := by
        rw [← sg.marginalProb_eq_sum]; exact hmarg_zero
      have hterm : sg.prior.pmf θ' * (a.senderStrategy θ').pmf m = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun θ'' _ => mul_nonneg (sg.prior.nonneg θ'') ((a.senderStrategy θ'').nonneg m))).mp
          hsum_zero θ' (Finset.mem_univ θ')
      exact (mul_eq_zero.mp hterm).resolve_left (hfull θ').ne'
    -- Under full support, `prior θ' · tWeight a θ' m = (a.belief m).pmf θ'`.
    have h_prior_tWeight : ∀ θ', sg.prior.pmf θ' * sg.tWeight a θ' m = (a.belief m).pmf θ' := by
      intro θ'
      unfold tWeight
      rw [if_pos (hfull θ'), mul_div_cancel₀ _ (hfull θ').ne']
    have hW : ∀ n θ', sg.senderWeight a n θ' m
        = trembleRate n * sg.tWeight a θ' m + (trembleRate n) ^ 2 := by
      intro n θ'; unfold senderWeight; rw [h_aSS_zero θ', zero_add]
    set Z : ℕ → sg.Theta → ℝ := fun n θ' => ∑ b, sg.senderWeight a n θ' b with hZ_def
    -- `redNum` is the `trembleRate`-reduced posterior ratio; the rate factors cancel.
    set redNum : ℕ → sg.Theta → ℝ :=
      fun n θ' => ((a.belief m).pmf θ' + sg.prior.pmf θ' * trembleRate n) / Z n θ' with hred_def
    have hZ_pos : ∀ n θ', 0 < Z n θ' := fun n θ' => sg.senderWeight_sum_pos a n θ'
    have hg_red : ∀ n θ', g n θ' = trembleRate n * redNum n θ' := by
      intro n θ'
      rw [hg_def, hred_def]
      simp only
      rw [senderTremble, normPos_pmf,
        show (∑ b, sg.senderWeight a n θ' b) = Z n θ' from rfl, hW n θ',
        ← h_prior_tWeight θ']
      have hZne : Z n θ' ≠ 0 := (hZ_pos n θ').ne'
      field_simp
    have hpost_eq : ∀ n,
        g n θ / (∑ θ', g n θ') = redNum n θ / (∑ θ', redNum n θ') := by
      intro n
      rw [hg_red n θ,
        show (∑ θ', g n θ') = ∑ θ', trembleRate n * redNum n θ' from
          Finset.sum_congr rfl (fun θ' _ => hg_red n θ'),
        ← Finset.mul_sum]
      exact mul_div_mul_left _ _ (trembleRate_pos n).ne'
    simp_rw [hpost_eq]
    have hredNum_tendsto : ∀ θ', Filter.Tendsto (fun n => redNum n θ') Filter.atTop
        (nhds ((a.belief m).pmf θ')) := by
      intro θ'
      have hnum' : Filter.Tendsto
          (fun n => (a.belief m).pmf θ' + sg.prior.pmf θ' * trembleRate n) Filter.atTop
          (nhds ((a.belief m).pmf θ')) := by
        simpa using (tendsto_const_nhds (x := (a.belief m).pmf θ')).add
          (trembleRate_tendsto.const_mul (sg.prior.pmf θ'))
      have hden' : Filter.Tendsto (fun n => Z n θ') Filter.atTop (nhds 1) :=
        sg.senderWeight_sum_tendsto a θ'
      simpa [hred_def, div_one] using hnum'.div hden' one_ne_zero
    have hredDen_tendsto : Filter.Tendsto (fun n => ∑ θ', redNum n θ') Filter.atTop (nhds 1) := by
      have h := tendsto_finset_sum (Finset.univ : Finset sg.Theta)
        (fun θ' _ => hredNum_tendsto θ')
      rwa [(a.belief m).sum_one] at h
    simpa [div_one] using (hredNum_tendsto θ).div hredDen_tendsto one_ne_zero

/-! ### The receiver tremble -/

/-- Unnormalized receiver tremble weight: The equilibrium weight plus a positive floor. -/
noncomputable def receiverWeight (a : sg.SignalingAssessment) (n : ℕ) (m : sg.Msg) (act : sg.Act) :
    ℝ :=
  (a.receiverStrategy m).pmf act + trembleRate n

/-- The unnormalized receiver tremble weight is strictly positive. -/
lemma receiverWeight_pos (a : sg.SignalingAssessment) (n : ℕ) (m : sg.Msg) (act : sg.Act) :
    0 < sg.receiverWeight a n m act := by
  have := (a.receiverStrategy m).nonneg act
  unfold receiverWeight; linarith [trembleRate_pos n]

/-- The total receiver tremble weight is strictly positive. -/
lemma receiverWeight_sum_pos (a : sg.SignalingAssessment) (n : ℕ) (m : sg.Msg) :
    0 < ∑ act, sg.receiverWeight a n m act :=
  Finset.sum_pos (fun act _ => sg.receiverWeight_pos a n m act) ⟨default, Finset.mem_univ _⟩

/-- The normalized receiver tremble at message `m`, step `n`. -/
noncomputable def receiverTremble (a : sg.SignalingAssessment) (n : ℕ) (m : sg.Msg) :
    FinDist sg.Act :=
  normPos (sg.receiverWeight a n m) (fun act => (sg.receiverWeight_pos a n m act).le)
    (sg.receiverWeight_sum_pos a n m)

/-- The receiver tremble assigns positive probability to every action. -/
lemma receiverTremble_pos (a : sg.SignalingAssessment) (n : ℕ) (m : sg.Msg) (act : sg.Act) :
    0 < (sg.receiverTremble a n m).pmf act := by
  rw [receiverTremble, normPos_pmf]
  exact div_pos (sg.receiverWeight_pos a n m act) (sg.receiverWeight_sum_pos a n m)

/-- The receiver tremble bundled as a mixed strategy. -/
noncomputable def receiverTrembleStrat (a : sg.SignalingAssessment) (n : ℕ) :
    sg.ReceiverMixedStrategy := fun m => sg.receiverTremble a n m

/-- The unnormalized receiver weight converges to the equilibrium weight. -/
lemma receiverWeight_tendsto (a : sg.SignalingAssessment) (m : sg.Msg) (act : sg.Act) :
    Filter.Tendsto (fun n => sg.receiverWeight a n m act) Filter.atTop
      (nhds ((a.receiverStrategy m).pmf act)) := by
  simpa [receiverWeight] using
    (tendsto_const_nhds (x := (a.receiverStrategy m).pmf act)).add trembleRate_tendsto

/-- The receiver normalizer converges to `1`. -/
lemma receiverWeight_sum_tendsto (a : sg.SignalingAssessment) (m : sg.Msg) :
    Filter.Tendsto (fun n => ∑ act, sg.receiverWeight a n m act) Filter.atTop (nhds 1) := by
  have h := tendsto_finset_sum Finset.univ (fun act _ => sg.receiverWeight_tendsto a m act)
  rwa [(a.receiverStrategy m).sum_one] at h

/-- The normalized receiver tremble converges pointwise to the equilibrium receiver strategy. -/
lemma receiverTremble_tendsto (a : sg.SignalingAssessment) (m : sg.Msg) (act : sg.Act) :
    Filter.Tendsto (fun n => (sg.receiverTremble a n m).pmf act) Filter.atTop
      (nhds ((a.receiverStrategy m).pmf act)) := by
  simp_rw [receiverTremble, normPos_pmf]
  simpa using (sg.receiverWeight_tendsto a m act).div (sg.receiverWeight_sum_tendsto a m)
    (by norm_num)

/-! ### Assembling Kreps–Wilson consistency -/

/-- The per-step witnessing assessment: Sender strategy from `s n`, receiver tremble, and target
beliefs. -/
noncomputable def trembleAssessment (a : sg.SignalingAssessment) (s : ℕ → sg.SenderMixedStrategy)
    (n : ℕ) : sg.SignalingAssessment where
  senderStrategy := s n
  receiverStrategy := sg.receiverTrembleStrat a n
  belief := a.belief

/-! ### Step-probability value lemmas for embedded behavioral strategies -/

/-- `stepProb` at the root chance node: The prior's event mass. Independent of `b`. -/
private lemma stepProb_nil (b : sg.SignalingAssessment) (e : sg.Event) :
    (sg.toExtensiveForm).stepProb (b.toBehavioral) [] e
      = ∑ θ, if Event.type θ = e then sg.prior.pmf θ else 0 := by
  unfold ExtensiveForm.stepProb
  rfl

/-- `stepProb` at the sender node `[type θ]`: The sender's message mass. -/
private lemma stepProb_type (b : sg.SignalingAssessment) (θ : sg.Theta) (e : sg.Event) :
    (sg.toExtensiveForm).stepProb (b.toBehavioral) [Event.type θ] e
      = ∑ m, if Event.msg m = e then (b.senderStrategy θ).pmf m else 0 := by
  unfold ExtensiveForm.stepProb
  change ∑ m : sg.Msg, (if Event.msg m = e then
    ((b.toBehavioral).atHistory [Event.type θ]).val m else 0) = _
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hm : Event.msg m = e <;> simp only [hm, if_true, if_false]
  rfl

/-- `stepProb` at the receiver node `[type θ, msg m]`: The receiver's action mass. -/
private lemma stepProb_typeMsg (b : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg)
    (e : sg.Event) :
    (sg.toExtensiveForm).stepProb (b.toBehavioral) [Event.type θ, Event.msg m] e
      = ∑ act, if Event.act act = e then (b.receiverStrategy m).pmf act else 0 := by
  unfold ExtensiveForm.stepProb
  change ∑ act : sg.Act, (if Event.act act = e then
    ((b.toBehavioral).atHistory [Event.type θ, Event.msg m]).val act else 0) = _
  refine Finset.sum_congr rfl (fun act _ => ?_)
  by_cases hact : Event.act act = e <;> simp only [hact, if_true, if_false]
  rfl

/-- A guarded sequence `if P then f n else 0` converges to `if P then L else 0`. -/
private lemma tendsto_ite_zero {f : ℕ → ℝ} {L : ℝ} (P : Prop) [Decidable P]
    (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => if P then f n else 0) Filter.atTop (nhds (if P then L else 0)) := by
  by_cases hP : P <;> simp only [hP, if_true, if_false]
  · exact hf
  · exact tendsto_const_nhds

/-- The Bayesian posterior at the sender's own-type node `[type θ]` equals `1` whenever
`prior θ > 0`. -/
private lemma bayesBeliefAt_sender_eq_one (b : sg.SignalingAssessment) (θ : sg.Theta)
    (hprior : 0 < sg.prior.pmf θ) :
    bayesBeliefAt (sg.toExtensiveForm) (b.toBehavioral) (b.toBeliefSystem)
        .sender θ [Event.type θ] = 1 := by
  have hin : ((sg.toExtensiveForm).tree.nodeKind [Event.type θ]).movesAt .sender ∧
      (sg.toExtensiveForm).info.observe .sender [Event.type θ] = θ := ⟨rfl, rfl⟩
  have hinfo := sg.infoSetProb_sender b θ
  have hmem : (⟨[Event.type θ], hin⟩ : (sg.toExtensiveForm).InfoSet .sender θ) ∈
      (b.toBeliefSystem).support SignalingPlayer.sender θ := by
    change (⟨[Event.type θ], hin⟩ : (sg.toExtensiveForm).InfoSet .sender θ) ∈
      ({sg.senderInfoSet θ} : Finset ((sg.toExtensiveForm).InfoSet .sender θ))
    rw [Finset.mem_singleton]
    exact Subtype.ext rfl
  have hpos : 0 < infoSetProb (sg.toExtensiveForm) (b.toBehavioral) (b.toBeliefSystem) .sender θ :=
    hinfo ▸ hprior
  unfold bayesBeliefAt
  simp only [dif_pos hin, if_pos hmem, dif_pos hpos]
  rw [sg.reachProb_type b θ, hinfo, div_self hprior.ne']

/-- The Bayesian posterior at a receiver node `[type θ, msg m]` equals
`(posterior b.senderStrategy m).pmf θ` whenever `m` has positive marginal mass. -/
private lemma bayesBeliefAt_receiver_eq_posterior (b : sg.SignalingAssessment) (θ : sg.Theta)
    (m : sg.Msg) (hmarg : 0 < sg.marginalProb b.senderStrategy m) :
    bayesBeliefAt (sg.toExtensiveForm) (b.toBehavioral) (b.toBeliefSystem)
        .receiver m [Event.type θ, Event.msg m] = (sg.posterior b.senderStrategy m).pmf θ := by
  have hin : ((sg.toExtensiveForm).tree.nodeKind [Event.type θ, Event.msg m]).movesAt .receiver ∧
      (sg.toExtensiveForm).info.observe .receiver [Event.type θ, Event.msg m] = m := ⟨rfl, rfl⟩
  have hinfo := sg.infoSetProb_receiver b m
  have hmem : (⟨[Event.type θ, Event.msg m], hin⟩ :
      (sg.toExtensiveForm).InfoSet .receiver m) ∈
        (b.toBeliefSystem).support SignalingPlayer.receiver m := by
    change (⟨[Event.type θ, Event.msg m], hin⟩ :
        (sg.toExtensiveForm).InfoSet .receiver m) ∈ sg.receiverSupport m
    unfold receiverSupport
    rw [Finset.mem_image]
    exact ⟨θ, Finset.mem_univ _, Subtype.ext rfl⟩
  have hpos : 0 < infoSetProb (sg.toExtensiveForm) (b.toBehavioral) (b.toBeliefSystem)
      .receiver m := hinfo ▸ hmarg
  unfold bayesBeliefAt
  simp only [dif_pos hin, if_pos hmem, dif_pos hpos]
  rw [sg.reachProb_typeMsg b θ m, hinfo]
  exact (sg.posterior_apply b.senderStrategy m θ hmarg).symm

/-- Given a totally-mixed sender sequence converging pointwise to `a.senderStrategy` whose induced
posteriors converge to `a.belief`, the target assessment embeds as a Kreps–Wilson consistent
assessment. A full-support prior is required. -/
lemma hasConsistentBeliefs_toAssessment_of_senderTremble (a : sg.SignalingAssessment)
    (hfull : ∀ θ, 0 < sg.prior.pmf θ) (s : ℕ → sg.SenderMixedStrategy)
    (hs_pos : ∀ n θ m, 0 < (s n θ).pmf m)
    (hs_tendsto : ∀ θ m, Filter.Tendsto (fun n => (s n θ).pmf m) Filter.atTop
        (nhds ((a.senderStrategy θ).pmf m)))
    (hpost_tendsto : ∀ m θ, Filter.Tendsto (fun n => (sg.posterior (s n) m).pmf θ) Filter.atTop
        (nhds ((a.belief m).pmf θ))) :
    HasConsistentBeliefs sg.toExtensiveForm (a.toAssessment) := by
  classical
  refine ⟨fun n => (sg.trembleAssessment a s n).toBehavioral, ?_, ?_, ?_⟩
  · -- Condition 1: total mixedness.
    intro n i obs c
    simp only []
    cases i with
    | sender =>
      simp only [SignalingAssessment.toBehavioral_sender]
      exact hs_pos n obs c
    | receiver =>
      simp only [SignalingAssessment.toBehavioral_receiver]
      exact sg.receiverTremble_pos a n obs c
  · -- Condition 2: behavioral-strategy coordinate convergence.
    intro i obs c
    simp only [SignalingAssessment.toAssessment_strategy]
    cases i with
    | sender =>
      simp only [SignalingAssessment.toBehavioral_sender]
      exact hs_tendsto obs c
    | receiver =>
      simp only [SignalingAssessment.toBehavioral_receiver]
      exact sg.receiverTremble_tendsto a obs c
  · -- Condition 3: Bayesian-posterior convergence.
    intro i obs h
    simp only [SignalingAssessment.toAssessment_beliefs]
    cases i with
    | sender =>
      by_cases hin : ((sg.toExtensiveForm).tree.nodeKind h).movesAt .sender ∧
          (sg.toExtensiveForm).info.observe .sender h = obs
      · have hheq : h = [Event.type obs] := by
          obtain ⟨θ', hθ'⟩ := (sg.sender_movesAt_iff h).mp hin.1
          have hθobs : θ' = obs := by have := hin.2; rw [hθ'] at this; exact this
          rw [hθ', hθobs]
        rw [hheq]
        have hlim : (a.toBeliefSystem).prob .sender obs [Event.type obs] = 1 := by
          rw [BeliefSystem.prob_of_mem _ _ _ (⟨rfl, rfl⟩ :
            ((sg.toExtensiveForm).tree.nodeKind [Event.type obs]).movesAt .sender ∧
              (sg.toExtensiveForm).info.observe .sender [Event.type obs] = obs)]
          rfl
        have hval : ∀ n, bayesBeliefAt (sg.toExtensiveForm)
            ((sg.trembleAssessment a s n).toBehavioral) (a.toBeliefSystem)
            .sender obs [Event.type obs] = 1 := fun n =>
          sg.bayesBeliefAt_sender_eq_one (sg.trembleAssessment a s n) obs (hfull obs)
        rw [hlim]; simp_rw [hval]; exact tendsto_const_nhds
      · have hlim : (a.toBeliefSystem).prob .sender obs h = 0 :=
          BeliefSystem.prob_of_not_mem _ _ _ hin
        have hval : ∀ n, bayesBeliefAt (sg.toExtensiveForm)
            ((sg.trembleAssessment a s n).toBehavioral) (a.toBeliefSystem) .sender obs h = 0 :=
          fun n => by unfold bayesBeliefAt; rw [dif_neg hin]
        rw [hlim]; simp_rw [hval]; exact tendsto_const_nhds
    | receiver =>
      by_cases hin : ((sg.toExtensiveForm).tree.nodeKind h).movesAt .receiver ∧
          (sg.toExtensiveForm).info.observe .receiver h = obs
      · obtain ⟨θ, m', hθm⟩ := (sg.receiver_movesAt_iff h).mp hin.1
        have hmobs : m' = obs := by have := hin.2; rw [hθm] at this; exact this
        have hheq : h = [Event.type θ, Event.msg obs] := by rw [hθm, hmobs]
        rw [hheq]
        have hlim : (a.toBeliefSystem).prob .receiver obs [Event.type θ, Event.msg obs] =
            (a.belief obs).pmf θ := by
          rw [BeliefSystem.prob_of_mem _ _ _ (⟨rfl, rfl⟩ :
            ((sg.toExtensiveForm).tree.nodeKind [Event.type θ, Event.msg obs]).movesAt .receiver ∧
              (sg.toExtensiveForm).info.observe .receiver [Event.type θ, Event.msg obs] = obs)]
          rfl
        have hval : ∀ n, bayesBeliefAt (sg.toExtensiveForm)
            ((sg.trembleAssessment a s n).toBehavioral) (a.toBeliefSystem)
            .receiver obs [Event.type θ, Event.msg obs] = (sg.posterior (s n) obs).pmf θ := by
          intro n
          have hmarg : 0 < sg.marginalProb (s n) obs :=
            sg.marginalProb_pos (hfull θ) (hs_pos n θ obs)
          exact sg.bayesBeliefAt_receiver_eq_posterior (sg.trembleAssessment a s n) θ obs hmarg
        rw [hlim]; simp_rw [hval]; exact hpost_tendsto obs θ
      · have hlim : (a.toBeliefSystem).prob .receiver obs h = 0 :=
          BeliefSystem.prob_of_not_mem _ _ _ hin
        have hval : ∀ n, bayesBeliefAt (sg.toExtensiveForm)
            ((sg.trembleAssessment a s n).toBehavioral) (a.toBeliefSystem) .receiver obs h = 0 :=
          fun n => by unfold bayesBeliefAt; rw [dif_neg hin]
        rw [hlim]; simp_rw [hval]; exact tendsto_const_nhds

/-! ### The signaling sequential-equilibrium predicate and its existence -/

/-- A signaling assessment is a sequential equilibrium if its embedded assessment is a Kreps–Wilson
sequential equilibrium of the encoded extensive game. -/
def IsSignalingSequentialEquilibrium (sg : SignalingGame) (a : sg.SignalingAssessment) : Prop :=
  IsSequentialEquilibrium sg.toExtensiveGame (a.toAssessment)

/-- **Fudenberg–Tirole coincidence (consistency half).** Under a full-support prior, every
signaling assessment with Bayes-consistent beliefs embeds as a Kreps–Wilson consistent
assessment. -/
lemma hasConsistentBeliefs_of_signalingBayesConsistent (a : sg.SignalingAssessment)
    (hfull : ∀ θ, 0 < sg.prior.pmf θ) (hcons : sg.signalingBayesConsistent a) :
    HasConsistentBeliefs sg.toExtensiveForm (a.toAssessment) :=
  sg.hasConsistentBeliefs_toAssessment_of_senderTremble a hfull (sg.senderTrembleStrat a)
    (fun n θ m => sg.senderTremble_pos a n θ m)
    (fun θ m => sg.senderTremble_tendsto a θ m)
    (fun m θ => sg.senderTremble_posterior_tendsto a hfull hcons m θ)

/-- **Fudenberg–Tirole coincidence.** Under a full-support prior, every signaling PBE is a
sequential equilibrium of the encoded extensive game. -/
theorem isSignalingSequentialEquilibrium_of_isSignalingPBE (a : sg.SignalingAssessment)
    (hfull : ∀ θ, 0 < sg.prior.pmf θ) (h : sg.IsSignalingPBE a) :
    sg.IsSignalingSequentialEquilibrium a :=
  ⟨(IsPerfectBayesianEquilibrium.of_isSignalingPerfectBayesianEquilibrium_toAssessment h).1,
    sg.hasConsistentBeliefs_of_signalingBayesConsistent a hfull h.1⟩

/-- **Existence of a signaling sequential equilibrium.** Every full-support signaling game admits a
sequential equilibrium. -/
theorem exists_signalingSequentialEquilibrium (hfull : ∀ θ, 0 < sg.prior.pmf θ) :
    ∃ a : sg.SignalingAssessment, sg.IsSignalingSequentialEquilibrium a :=
  let ⟨a, ha⟩ := sg.exists_signalingPBE
  ⟨a, sg.isSignalingSequentialEquilibrium_of_isSignalingPBE a hfull ha⟩

/-! ### Necessity of the full-support prior

The full-support hypothesis `hfull` on every result above is not incidental. The sender's
own-type information set at a type `θ₀` is the singleton `{[type θ₀]}`, and `[type θ₀]` is
structurally reachable: Nature emits every type regardless of its probability (`emits` is
probability-free, the notion underlying `BeliefSystem.support_exhaustive`). So exhaustiveness
forces that singleton into the support of every assessment, where `belief_sum_one` fixes its belief
at `1`. Yet its probabilistic reach is `prior θ₀` under every behavioral strategy — nature is a
fixed chance node, never perturbed by player trembles — so when `prior θ₀ = 0` every trembled
Bayesian posterior there is `0`. No assessment can bridge `0` to `1`, so `HasConsistentBeliefs`,
and hence sequential equilibrium, fails to exist. Kreps–Wilson consistency disciplines beliefs only
through player trembles and so implicitly assumes full-support chance moves. -/

/-- `[type θ]` is structurally reachable for every type `θ`: Nature emits it, irrespective of the
prior weight `prior θ` (which may be zero). -/
lemma isReachable_type (θ : sg.Theta) :
    sg.toExtensiveForm.IsReachable [Event.type θ] := by
  have h := ExtensiveForm.IsReachable.step (G := sg.toExtensiveForm) []
    (Event.type θ) ExtensiveForm.IsReachable.root ⟨θ, rfl⟩
  simpa using h

/-- The root chance step is independent of the behavioral strategy, so the reach probability of
`[type θ]` is the prior weight on `θ` under any strategy (cf. `reachProb_type`, which is the
special case at the embedded strategy). -/
lemma reachProb_type_eq_prior (σ : sg.toExtensiveForm.BehavioralStrategy) (θ : sg.Theta) :
    reachProb sg.toExtensiveForm σ [Event.type θ] = sg.prior.pmf θ := by
  unfold reachProb ExtensiveForm.finitePrefixProb ExtensiveForm.finitePrefixProbFrom
    ExtensiveForm.stepProb
  change NodeKind.eventProb (sg.toExtensiveForm.tree.nodeKind []) _ (Event.type θ) * 1 = _
  rw [mul_one]
  change ∑ θ' : sg.Theta, (if Event.type θ' = Event.type θ then sg.prior.pmf θ' else 0)
    = sg.prior.pmf θ
  simp only [Event.type.injEq, Fintype.sum_ite_eq']

/-- The sender's information set at `θ` is the singleton `{[type θ]}`: Every history in it is
`[type θ]`. -/
lemma infoSet_sender_val (θ : sg.Theta) (x : sg.toExtensiveForm.InfoSet .sender θ) :
    x.1 = [Event.type θ] := by
  obtain ⟨θ', hθ'⟩ := (sg.sender_movesAt_iff x.1).mp x.2.1
  have hobs : sg.toExtensiveForm.info.observe .sender x.1 = θ := x.2.2
  rw [hθ'] at hobs ⊢
  simp only [toExtensiveForm_info, observe_sender_type] at hobs
  rw [hobs]

/-- In any assessment of the encoded game, the sender's belief at the on-its-own-type history
`[type θ]` is forced to `1`: The singleton information set is structurally reachable, so
`support_exhaustive` makes its support nonempty and `belief_sum_one` puts the whole mass there.
This holds with no hypothesis on the prior. -/
lemma prob_sender_type_eq_one (assess : Assessment sg.toExtensiveForm) (θ : sg.Theta) :
    assess.beliefs.prob .sender θ [Event.type θ] = 1 := by
  set μ := assess.beliefs with hμ
  have hx0_mem : sg.senderInfoSet θ ∈ μ.support .sender θ :=
    μ.support_exhaustive .sender θ (sg.senderInfoSet θ) (sg.isReachable_type θ)
  have hsupp_eq : μ.support .sender θ = {sg.senderInfoSet θ} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx0_mem, fun x _ => Subtype.ext (sg.infoSet_sender_val θ x)⟩
  have hsum := μ.belief_sum_one .sender θ ⟨_, hx0_mem⟩
  rw [hsupp_eq, Finset.sum_singleton] at hsum
  have hmem : (sg.toExtensiveForm.tree.nodeKind [Event.type θ]).movesAt .sender ∧
      sg.toExtensiveForm.info.observe .sender [Event.type θ] = θ := ⟨rfl, rfl⟩
  rw [BeliefSystem.prob_of_mem μ .sender θ hmem]
  exact hsum

/-- The information-set mass at the sender's type-`θ` node vanishes under every strategy when
`prior θ = 0`: Each (structurally present) history in the support is `[type θ]`, whose reach
probability is `prior θ = 0`. -/
lemma infoSetProb_sender_eq_zero (σ : sg.toExtensiveForm.BehavioralStrategy)
    (assess : Assessment sg.toExtensiveForm) (θ : sg.Theta) (h0 : sg.prior.pmf θ = 0) :
    infoSetProb sg.toExtensiveForm σ assess.beliefs .sender θ = 0 :=
  Finset.sum_eq_zero fun x _ => by
    rw [sg.infoSet_sender_val θ x, sg.reachProb_type_eq_prior σ θ, h0]

/-- Hence every Bayesian posterior at the sender's type-`θ` node is `0` (a zero-mass info set
receives zero), under any strategy, when `prior θ = 0`. -/
lemma bayesBeliefAt_sender_type_eq_zero (σ : sg.toExtensiveForm.BehavioralStrategy)
    (assess : Assessment sg.toExtensiveForm) (θ : sg.Theta) (h0 : sg.prior.pmf θ = 0) :
    bayesBeliefAt sg.toExtensiveForm σ assess.beliefs .sender θ [Event.type θ] = 0 := by
  have hz := sg.infoSetProb_sender_eq_zero σ assess θ h0
  unfold bayesBeliefAt
  split_ifs with h1 h2 h3
  · rw [hz] at h3; exact absurd h3 (lt_irrefl 0)
  all_goals rfl

/-- **Necessity of full support (consistency level).** When some type carries zero prior, no
assessment of the encoded extensive game has Kreps–Wilson consistent beliefs. The sender's belief
at that type's own node is forced to `1` (`prob_sender_type_eq_one`) while every trembled posterior
there is `0` (`bayesBeliefAt_sender_type_eq_zero`), and `0 → 1` is impossible. -/
theorem not_hasConsistentBeliefs_of_prior_zero
    (assess : Assessment sg.toExtensiveForm) (θ₀ : sg.Theta) (h0 : sg.prior.pmf θ₀ = 0) :
    ¬ HasConsistentBeliefs sg.toExtensiveForm assess := by
  rintro ⟨σseq, -, -, hbelief⟩
  have hb := hbelief .sender θ₀ [Event.type θ₀]
  rw [sg.prob_sender_type_eq_one assess θ₀] at hb
  have hzero : (fun n => bayesBeliefAt sg.toExtensiveForm (σseq n) assess.beliefs .sender θ₀
      [Event.type θ₀]) = fun _ => 0 :=
    funext fun n => sg.bayesBeliefAt_sender_type_eq_zero (σseq n) assess θ₀ h0
  rw [hzero] at hb
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hb).symm

/-- **Necessity of full support (equilibrium level).** A signaling game with a zero-prior type
admits no sequential equilibrium: The embedded assessment of any candidate would need consistent
beliefs, which `not_hasConsistentBeliefs_of_prior_zero` rules out. This is the converse companion
to `exists_signalingSequentialEquilibrium`: Full support is not just sufficient but necessary. -/
theorem not_exists_isSignalingSequentialEquilibrium_of_prior_zero
    (θ₀ : sg.Theta) (h0 : sg.prior.pmf θ₀ = 0) :
    ¬ ∃ a : sg.SignalingAssessment, sg.IsSignalingSequentialEquilibrium a := by
  rintro ⟨a, -, hcons⟩
  exact sg.not_hasConsistentBeliefs_of_prior_zero a.toAssessment θ₀ h0 hcons

end SignalingGame

end Econlib.GameTheory
