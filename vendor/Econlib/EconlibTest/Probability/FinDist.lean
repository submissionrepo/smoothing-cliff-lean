/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# `FinDist` Non-Vacuity Checks

Compile-time semantic witnesses for the finite-distribution carrier `Econlib.Probability.FinDist`.
`FinDist` is the most widely instantiated probability type in the library, so its API earns
concrete witnesses on small `Fin n` laws that would catch a misplaced unit mass, a reversed
conditioning/Bayes update, a broken monad law, or a CDF endpoint flip.

The witnesses are anchored on three concrete laws:

* `coin = ![1/4, 3/4]` over `Fin 2` — a biased two-point law (mean `3/4`, variance `3/16`);
* `d3 = ![1/6, 1/3, 1/2]` over `Fin 3` — a spread three-point law (mean `4/3`, variance `5/9`);
* `FinDist.pure k` — the Dirac point mass, the degenerate (zero-variance) reference.

Values are computed independently and pinned as literals, so an endpoint or direction error breaks
the build.
-/

noncomputable section

namespace EconlibTest.Probability.FinDist

open Econlib.Probability

/-- A biased coin: `P(0) = 1/4`, `P(1) = 3/4` over `Fin 2`. -/
private abbrev coin : FinDist (Fin 2) := finDist% ![1 / 4, 3 / 4]

/-- A spread three-point law `P = (1/6, 1/3, 1/2)` over `Fin 3`. -/
private abbrev d3 : FinDist (Fin 3) := finDist% ![1 / 6, 1 / 3, 1 / 2]

/-- The integer-valued outcome map `i ↦ (i : ℝ)` (read through `Fin.val`). -/
private abbrev outcome {n : ℕ} : Fin n → ℝ := fun i => (i.val : ℝ)

section diracAndPmf

/-- **Unit mass lands on the point.** `pure k` puts mass `1` at `k`. -/
theorem pure_apply_self_two : (FinDist.pure (1 : Fin 2)).pmf 1 = 1 :=
  FinDist.pure_apply_self 1

/-- **...and zero elsewhere.** A misplaced unit mass would break this. -/
theorem pure_apply_ne_two : (FinDist.pure (1 : Fin 2)).pmf 0 = 0 :=
  FinDist.pure_apply_ne (by decide)

/-- A law with a mass-one cell built independently of `pure`. -/
private abbrev fullMass : FinDist (Fin 2) := finDist% ![0, 1]

/-- **A mass-one cell forces the whole law to be the point mass there.** `fullMass = ![0,1]` is
built from its mass vector (not as `pure 1`); having `pmf 1 = 1`, it is *forced* to equal `pure 1`.
Unlike the syntactic `pure 1 = pure 1`, this exercises `eq_pure_of_pmf_eq_one` on a genuinely
distinct presentation. -/
theorem eq_pure_of_full_mass : fullMass = FinDist.pure (1 : Fin 2) :=
  FinDist.eq_pure_of_pmf_eq_one (show fullMass.pmf 1 = 1 by simp)

/-- The literal `coin` reads off its vector entries. -/
theorem coin_apply_zero : coin.pmf 0 = 1 / 4 := by simp
theorem coin_apply_one : coin.pmf 1 = 3 / 4 := by simp

/-- The two masses sum to one — the structural law of `FinDist (Fin 2)`. -/
theorem coin_sum : coin.pmf 0 + coin.pmf 1 = 1 := coin.sum_pmf_two

end diracAndPmf

section expectationAlgebra

/-- **Mean of the coin** is `3/4` — an outright mass-weighted average. -/
theorem coin_expect : coin.expect outcome = 3 / 4 := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_two]
  simp [outcome]

/-- **Mean of `d3`** is `0·1/6 + 1·1/3 + 2·1/2 = 4/3`. -/
theorem d3_expect : d3.expect outcome = 4 / 3 := by
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three]
  simp [outcome]; norm_num

/-- Expectation of a constant returns the constant (averaging is mass-normalized). -/
theorem coin_expect_const : coin.expect (fun _ => (7 : ℝ)) = 7 := coin.expect_const 7

/-- **Affine pushthrough.** `E[2·outcome + 1] = 2·E[outcome] + 1 = 5/2`. -/
theorem coin_expect_affine : coin.expect (fun i => 2 * outcome i + 1) = 5 / 2 := by
  rw [show (fun i => 2 * outcome i + 1) = (fun i => 2 * outcome i) + (fun _ => (1 : ℝ)) from rfl,
    coin.expect_add, coin.expect_const]
  rw [show (fun i => 2 * outcome i) = (2 : ℝ) • outcome from rfl, coin.expect_smul, coin_expect]
  norm_num

/-- A nonnegative integrand has nonnegative expectation. -/
theorem d3_expect_nonneg : 0 ≤ d3.expect (fun i => outcome i ^ 2) :=
  d3.expect_nonneg _ (fun _ => sq_nonneg _)

/-- **Monotone in the integrand.** Pointwise `outcome ≤ outcome + 1` lifts to the means. -/
theorem d3_expect_mono : d3.expect outcome ≤ d3.expect (fun i => outcome i + 1) :=
  d3.expect_mono _ _ (fun _ => by linarith)

end expectationAlgebra

section varianceAlgebra

/-- **Variance of the coin** is `E[X²] − E[X]² = 3/4 − 9/16 = 3/16`. -/
theorem coin_variance : coin.variance outcome = 3 / 16 := by
  rw [FinDist.variance_eq_expect_sub_sq, coin_expect]
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_two]
  simp [outcome]; norm_num

/-- **Variance of `d3`** is `7/3 − 16/9 = 5/9`. -/
theorem d3_variance : d3.variance outcome = 5 / 9 := by
  rw [FinDist.variance_eq_expect_sub_sq, d3_expect]
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_three]
  simp [outcome]; norm_num

/-- **A point mass has zero variance** — the degenerate reference. -/
theorem pure_variance : (FinDist.pure (1 : Fin 3)).variance outcome = 0 :=
  FinDist.variance_pure 1 outcome

/-- **Affine scaling of variance:** `Var(3·outcome + 5) = 9·Var(outcome)`. -/
theorem coin_variance_affine :
    coin.variance (fun i => 3 * outcome i + 5) = 9 * coin.variance outcome := by
  rw [coin.variance_affine 3 5 outcome]; norm_num

/-- **The coin's variance is strictly positive** (`3/16 > 0`), as befits a genuinely spread law. -/
theorem coin_variance_pos : 0 < coin.variance outcome := by
  rw [coin_variance]; norm_num

/-- **Variance vanishes iff constant on the support — the nonconstant side.** Because `coin` is
genuinely spread, `variance_eq_zero_iff` forces the failure of support-constancy: there is a
positive-mass cell (here `0`, with mass `1/4 > 0`) where `outcome` differs from the mean `3/4`. This
exercises the characterization `variance_eq_zero_iff`, not just the value. -/
theorem coin_not_constant_on_support : ¬ (∀ a, 0 < coin a → outcome a = coin.expect outcome) := by
  rw [← FinDist.variance_eq_zero_iff]
  exact coin_variance_pos.ne'

/-- Popoviciu: `outcome ∈ [0,1]` on `Fin 2`, so `Var ≤ ((1-0)/2)² = 1/4`. -/
theorem coin_variance_le_quarter :
    coin.variance outcome ≤ ((1 - 0) / 2) ^ 2 :=
  coin.variance_le_quarter_diam_sq outcome
    (fun s => by fin_cases s <;> norm_num [outcome, Set.mem_Icc])

end varianceAlgebra

section monadLaws

/-- A **nonconstant** bind family: branch `0 ↦ d3`, branch `1 ↦ pure 0`. With a constant family the
left-identity law `pure a >>= f = f a` would pass for *any* input point; the nonconstant family
makes it pin the *selected* branch `f 0 = d3`, catching a `bind` that used the wrong input
point. -/
private abbrev bindFam : Fin 2 → FinDist (Fin 3) :=
  fun i => if i = 0 then d3 else FinDist.pure 0

/-- **Left identity selects the right branch:** `pure 0 >>= bindFam = bindFam 0 = d3`. -/
theorem pure_bind_law :
    (FinDist.pure (0 : Fin 2)).bind bindFam = d3 := by
  rw [FinDist.pure_bind 0 bindFam]
  simp [bindFam]

/-- **...and from the other input point:** `pure 1 >>= bindFam = bindFam 1 = pure 0 ≠ d3`. This
distinguishes the two branches, confirming `bind` reads the genuine input point. -/
theorem pure_bind_law_other :
    (FinDist.pure (1 : Fin 2)).bind bindFam = FinDist.pure 0 := by
  rw [FinDist.pure_bind 1 bindFam]
  simp only [bindFam, if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- **Right identity:** `d >>= pure = d`. -/
theorem bind_pure_law : coin.bind FinDist.pure = coin :=
  FinDist.bind_pure coin

/-- **Functor identity:** `map id = id`. -/
theorem map_id_law : coin.map id = coin := FinDist.map_id coin

/-- **map as bind:** `map f = bind (pure ∘ f)`. -/
theorem map_eq_bind_law (f : Fin 2 → Fin 3) :
    coin.map f = coin.bind (fun a => FinDist.pure (f a)) :=
  FinDist.map_eq_bind coin f

/-- **Change of variables.** Pushing `coin` through the relabeling `i ↦ 2·i`, then taking the mean
of `outcome`, equals the mean of `i ↦ 2·outcome i` under `coin`: `2·(3/4) = 3/2`. -/
theorem expect_map_law :
    (coin.map (fun i : Fin 2 => (⟨2 * i.val, by omega⟩ : Fin 4))).expect outcome = 3 / 2 := by
  rw [FinDist.expect_map]
  simp only [FinDist.expect_eq_sum, Fin.sum_univ_two]
  simp [outcome]; norm_num

end monadLaws

section conditioning

/-- The event "outcome is nonzero" on `Fin 3`. A concrete `DecidablePred` instance is supplied so
the filtered event mass reduces by computation rather than through `Classical`. -/
private abbrev eNonzero : Set (Fin 3) := {x | x ≠ 0}

private instance : DecidablePred (· ∈ eNonzero) := fun x => decidable_of_iff (x ≠ 0) Iff.rfl

/-- The impossible-for-`pure 0` event `{1}` on `Fin 2`, with a concrete decidability instance. -/
private abbrev eOne : Set (Fin 2) := {x | x = 1}

private instance : DecidablePred (· ∈ eOne) := fun x => decidable_of_iff (x = 1) Iff.rfl

/-- **Event mass.** `P(X ≠ 0) = 1/3 + 1/2 = 5/6` under `d3`. -/
theorem d3_probEvent : d3.probEvent eNonzero = 5 / 6 := by
  rw [FinDist.probEvent_eq_sum_filter]
  have hf : (Finset.univ.filter (· ∈ eNonzero) : Finset (Fin 3)) = {1, 2} := by decide
  rw [hf, Finset.sum_pair (by decide)]
  simp only [d3, FinDist.ofVec_apply, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-- **Conditioning direction.** Given `X ≠ 0`, the conditional mass at `1` is
`(1/3)/(5/6) = 2/5` — the prior `1/3` renormalized over the surviving event, not the raw prior. -/
theorem d3_condProb_one :
    d3.condProb eNonzero 1 = (1 / 3) / (5 / 6) := by
  rw [FinDist.condProb_eq_of_pos d3 eNonzero (by decide) (by rw [d3_probEvent]; norm_num),
    d3_probEvent]
  simp only [d3, FinDist.ofVec_apply, Matrix.cons_val_one]
  norm_num

/-- The conditional pmf sums to one over a positive-mass event. -/
theorem d3_condProb_sum_one :
    ∑ x, d3.condProb eNonzero x = 1 :=
  d3.condProb_sum_one_of_pos eNonzero (by rw [d3_probEvent]; norm_num)

/-- **Degenerate zero-mass branch.** Conditioning `pure 0` on the impossible event `{1}` returns the
prior unchanged (junk-on-zero-measure convention). -/
theorem conditionalOn_zero_event :
    (FinDist.pure (0 : Fin 2)).conditionalOnOrSelf eOne = FinDist.pure 0 := by
  apply FinDist.conditionalOnOrSelf_eq_self_of_zero
  rw [FinDist.probEvent_eq_sum_filter]
  have hf : (Finset.univ.filter (· ∈ eOne) : Finset (Fin 2)) = {1} := by decide
  rw [hf, Finset.sum_singleton]
  exact FinDist.pure_apply_ne (by decide)

end conditioning

section bayes

/-- An **asymmetric** two-state prior `P(θ=0)=2/3`, `P(θ=1)=1/3`. -/
private abbrev prior2 : FinDist (Fin 2) := finDist% ![2 / 3, 1 / 3]

/-- **Asymmetric** two-state likelihood with distinct rows: `ℓ(·|0) = (3/4,1/4)` (informative),
`ℓ(·|1) = (1/2,1/2)` (uninformative). The non-symmetric matrix and nonuniform prior are what let the
posterior anchors catch a state↔signal transpose `(lk θ).pmf s` vs `(lk s).pmf θ`. -/
private abbrev lk2 : Fin 2 → FinDist (Fin 2) :=
  ![finDist% ![3 / 4, 1 / 4], finDist% ![1 / 2, 1 / 2]]

/-- The signal-`0` marginal is `(2/3)·(3/4) + (1/3)·(1/2) = 1/2 + 1/6 = 2/3 > 0`. -/
theorem bayes_denom_pos :
    0 < ∑ θ, prior2.pmf θ * (lk2 θ).pmf 0 := by
  simp only [Fin.sum_univ_two, prior2, lk2, FinDist.ofVec_pmf, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The signal-`1` marginal is `(2/3)·(1/4) + (1/3)·(1/2) = 1/6 + 1/6 = 1/3 > 0`. -/
theorem bayes_denom_one_pos :
    0 < ∑ θ, prior2.pmf θ * (lk2 θ).pmf 1 := by
  simp only [Fin.sum_univ_two, prior2, lk2, FinDist.ofVec_pmf, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **Posterior moves toward the matching state.** After signal `0`, the posterior on state `0`
rises from the prior `2/3` to `((2/3)·(3/4))/(2/3) = 3/4` — the *correct* update direction.
A swap of the likelihood rows or a flipped Bayes ratio would change it. -/
theorem posterior_direction :
    (prior2.posterior lk2 0 bayes_denom_pos).pmf 0 = 3 / 4 := by
  rw [FinDist.posterior_apply, FinDist.signalMarginal_eq_sum]
  simp only [Fin.sum_univ_two, prior2, lk2, FinDist.ofVec_pmf, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **Posterior on the off state after signal `0`:** `((1/3)·(1/2))/(2/3) = 1/4`; with the matching
value `3/4` the two posterior masses sum to one. -/
theorem posterior_off_state :
    (prior2.posterior lk2 0 bayes_denom_pos).pmf 1 = 1 / 4 := by
  rw [FinDist.posterior_apply, FinDist.signalMarginal_eq_sum]
  simp only [Fin.sum_univ_two, prior2, lk2, FinDist.ofVec_pmf, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **Posterior after the uninformative signal `1`:** `((2/3)·(1/4))/(1/3) = 1/2`. Signal `1` is
uninformative under this likelihood, so the posterior on `0` falls from the prior `2/3` to `1/2` —
distinct from the signal-`0` posterior `3/4`, so an ignore-signal implementation is refuted. -/
theorem posterior_signal_one :
    (prior2.posterior lk2 1 bayes_denom_one_pos).pmf 0 = 1 / 2 := by
  rw [FinDist.posterior_apply, FinDist.signalMarginal_eq_sum]
  simp only [Fin.sum_univ_two, prior2, lk2, FinDist.ofVec_pmf, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **Total probability** closes the loop: averaging the totalized posterior on state `0` over all
signals, weighted by their marginals, recovers the prior mass `prior2 0 = 2/3`. With the asymmetric
marginals `(2/3, 1/3)` and distinct posteriors `(3/4, 1/2)`, this genuinely averages two different
posteriors. -/
theorem total_probability_witness :
    ∑ s : Fin 2, (∑ θ, prior2.pmf θ * (lk2 θ).pmf s) *
      (prior2.posteriorOrPrior lk2 s).pmf 0 = prior2.pmf 0 :=
  FinDist.total_probability prior2 lk2 0

/-- **Bayes consistency:** posterior expectations average back to the prior expectation. -/
theorem bayes_consistent_witness :
    ∑ s : Fin 2, (∑ θ, prior2.pmf θ * (lk2 θ).pmf s) *
      (prior2.posteriorOrPrior lk2 s).expect outcome = prior2.expect outcome :=
  FinDist.bayes_consistent prior2 lk2 outcome

/-- Both signals of this model have positive marginal, supplying the positive-marginal hypothesis
of `total_probability_of_posterior`. -/
theorem marg2_pos (s : Fin 2) : 0 < prior2.signalMarginal lk2 s := by
  fin_cases s
  · simpa [FinDist.signalMarginal_eq_sum] using bayes_denom_pos
  · simpa [FinDist.signalMarginal_eq_sum] using bayes_denom_one_pos

/-- **Total probability, posterior form.** Since every signal has positive marginal here, the
`signalMarginal`-weighted `posterior` masses (the gated `FinDist.posterior`, not the totalized
`posteriorOrPrior`) average back to the prior — `total_probability_of_posterior` cited directly
against `posterior` objects. -/
theorem total_probability_of_posterior_witness :
    ∑ s : Fin 2, prior2.signalMarginal lk2 s * (prior2.posterior lk2 s (marg2_pos s)).pmf 0
      = prior2.pmf 0 :=
  FinDist.total_probability_of_posterior prior2 lk2 0 marg2_pos

/-- The signal-`0` marginal under the uninformative likelihood is `1·coin 0 = 1/4 > 0`. -/
private theorem unif_hden :
    0 < ∑ θ, prior2.pmf θ * ((fun _ => coin) θ).pmf 0 := by
  simp only [Fin.sum_univ_two, prior2, FinDist.ofVec_pmf, Matrix.cons_val_zero]
  norm_num

/-- **Uninformative likelihood leaves the prior unchanged.** If every state emits the same signal
law, the posterior equals the prior. -/
theorem posterior_uniform_witness :
    prior2.posterior (fun _ => coin) 0 unif_hden = prior2 :=
  FinDist.posterior_uniform_likelihood prior2 (fun _ => coin) 0 coin (fun _ => rfl)
    (by rw [coin_apply_zero]; norm_num) unif_hden

end bayes

section simplexBridge

/-- **Round trip `ofSimplex ∘ toSimplex = id`** on a concrete law. -/
theorem ofSimplex_toSimplex_coin : FinDist.ofSimplex (FinDist.toSimplex coin) = coin :=
  FinDist.ofSimplex_toSimplex coin

/-- **Round trip the other way** on the underlying simplex point. -/
theorem toSimplex_ofSimplex_coin :
    FinDist.toSimplex (FinDist.ofSimplex (FinDist.toSimplex coin)) = FinDist.toSimplex coin :=
  FinDist.toSimplex_ofSimplex _

end simplexBridge

section cdf

/-- **CDF lower endpoint.** `F(0) = P(X ≤ 0) = 1/6` under `d3`. -/
theorem d3_cdf_zero : d3.cdf 0 = 1 / 6 := by
  rw [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three]
  simp [d3]

/-- **CDF reaches one at the top.** `F(2) = 1`. -/
theorem d3_cdf_top : d3.cdf 2 = 1 := by
  rw [FinDist.cdf_eq_sum_ite, Fin.sum_univ_three]
  simp [d3]; norm_num

/-- The CDF is monotone. -/
theorem d3_cdf_mono : Monotone d3.cdf := d3.cdf_mono

/-- **Pure CDF is a step.** `pure 1` jumps from `0` (below `1`) to `1` (at/above `1`). -/
theorem pure_cdf_below : (FinDist.pure (1 : Fin 3)).cdf 0 = 0 := by
  rw [FinDist.pure_cdf, if_neg (by decide)]
theorem pure_cdf_at : (FinDist.pure (1 : Fin 3)).cdf 1 = 1 := by
  rw [FinDist.pure_cdf, if_pos (le_refl _)]

/-- **...and stays `1` strictly above the atom:** `F(2) = 1`. Together with `pure_cdf_at` this
covers the full "at *and* above" claim, not just the boundary `at` case. -/
theorem pure_cdf_above : (FinDist.pure (1 : Fin 3)).cdf 2 = 1 := by
  rw [FinDist.pure_cdf, if_pos (by decide)]

end cdf

section product

/-- **Independent product** factorizes the joint mass: `P(0,1) = 1/4 · 1/3`. -/
theorem product_apply_witness :
    (coin.product d3).pmf (0, 1) = (1 / 4) * (1 / 3) := by
  rw [FinDist.product_apply]
  simp [coin, d3]

/-- **First marginal** of the product recovers `coin`. -/
theorem map_fst_product_witness : (coin.product d3).map Prod.fst = coin :=
  FinDist.map_fst_product coin d3

end product

section shortfall

/-- **Expected shortfall is nonnegative.** -/
theorem shortfall_nonneg : 0 ≤ d3.expectedShortfall outcome (3 / 2) :=
  d3.expectedShortfall_nonneg outcome (3 / 2)

/-- **Lower-hinge value at cutoff `t = 3/2`.** Via the hinge form `E[max(t − y, 0)]`:
`(3/2 − 0)·1/6 + (3/2 − 1)·1/3 + 0 = 1/4 + 1/6 = 5/12`. -/
theorem shortfall_value : d3.expectedShortfall outcome (3 / 2) = 5 / 12 := by
  rw [FinDist.expectedShortfall_eq, FinDist.expect_eq_sum, Fin.sum_univ_three]
  simp [d3, outcome]; norm_num

/-- **The advertised integrated-CDF identity**, via `expectedShortfall_eq_sum_lt`. The expected
shortfall equals the *filtered* sum over states strictly below the cutoff: at `t = 3/2` the filter
`{a | outcome a < 3/2}` is exactly `{0, 1}`, and `∑_{a ∈ {0,1}} (3/2 − outcome a)·d3(a) =
(3/2)·(1/6) + (1/2)·(1/3) = 5/12`. This is the discrete integrated-CDF theorem the docstring
promises, not just the hinge value. -/
theorem shortfall_value_sum_lt : d3.expectedShortfall outcome (3 / 2) = 5 / 12 := by
  rw [FinDist.expectedShortfall_eq_sum_lt]
  have hfilter : (Finset.univ.filter (fun a : Fin 3 => outcome a < 3 / 2)) = {0, 1} := by
    ext a; fin_cases a <;> simp [outcome] <;> norm_num
  rw [hfilter, Finset.sum_pair (by decide)]
  simp only [d3, outcome, FinDist.ofVec_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end shortfall

end EconlibTest.Probability.FinDist

end
