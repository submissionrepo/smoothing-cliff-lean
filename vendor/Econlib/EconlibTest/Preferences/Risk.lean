/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Econlib.Probability.FinDist.Literal
import Mathlib

/-!
# Risk-attitude non-vacuity checks

Compile-time semantic witnesses for the `Econlib.Preferences.Risk` layer (the risk-attitude
predicates, the Arrow–Pratt characterization, the certainty-equivalent Jensen gap, and the
comparative-risk-aversion ordering). These three families of facts are the ones most prone to a
silent *direction* error — averse vs. loving, a sign flip in the risk premium, an inverted
comparative ordering — so each witness fixes a concrete utility and lottery and checks the
direction both ways.

What each block catches:

* **Predicate direction.** On the concave square root we confirm `RiskAverse` /
  `StrictlyRiskAverse` *hold* and `RiskLoving` *fails* (the averse-vs-loving reversal); on the
  convex `x ↦ x²` the roles flip; an affine `u` lands exactly on `RiskNeutral`. A predicate that
  secretly quantified over an empty class, or one whose concavity sense was reversed, would let the
  wrong side go through here.
* **Arrow–Pratt round-trip.** On the CARA agent `A(x) ≡ α` and on a CRRA agent `A(x) = γ/x`, fed
  through `risk_averse_iff_absoluteRiskAversion_nonneg`, `…_pos`, and `…_zero` (affine). A sign
  error in `A = -u''/u'` would flip the nonneg/pos test.
* **Certainty-equivalent gap.** On the discriminating fifty-fifty bet over `{1, 4}` the certainty
  equivalent of the square root agent is *exactly* `9/4`, strictly below the mean `5/2`, so the risk
  premium is the anchored positive number `1/4`; the strict gap is delivered *through* the named
  strict-Jensen lemma fed directly by `√` (which is only `StrictMonoOn` its domain `[0, ∞)`), and an
  affine agent collapses the gap to equality (zero premium). A reversed Jensen inequality, or a
  premium computed as `c − 𝔼[X]`, breaks the anchor.
* **Comparative ordering.** Two CRRA agents with `γ₁ = 2 > 1/2 = γ₂` have
  `A₁ = 2/x > (1/2)/x = A₂`, so the first is *more* risk averse, and over a common positive-outcome
  lottery its certainty equivalent is *lower* (`8/5 ≤ 9/4`). An inverted
  `more_risk_averse_iff_absoluteRiskAversion_ge`, or a CE consequence that raised rather than
  lowered the equivalent, fails here.
-/

noncomputable section

namespace EconlibTest.Preferences.Risk

open Econlib.Preferences
open Econlib.Probability
open scoped BigOperators

/-! ## 1. Predicate instantiation with direction checks

`RiskAverse`/`StrictlyRiskAverse`/`RiskNeutral`/`RiskLoving` are *definitionally* concavity /
affinity predicates (`Risk/Basic.lean`). The point of these witnesses is to fix the direction: A
strictly **concave** utility is averse and **not** loving; a **convex** utility is loving and
**not** averse; an **affine** utility is exactly neutral. -/

section Predicates

/-- The square-root utility is **risk averse** on the closed ray `[0, ∞)`: Definitionally
`ConcaveOn ℝ (Ici 0) √`. -/
theorem sqrt_riskAverse : RiskAverse Real.sqrt (Set.Ici 0) :=
  Real.strictConcaveOn_sqrt.concaveOn

/-- The square-root utility is **strictly** risk averse on `[0, ∞)`. -/
theorem sqrt_strictlyRiskAverse : StrictlyRiskAverse Real.sqrt (Set.Ici 0) :=
  Real.strictConcaveOn_sqrt

/-- **Negative check: The concave √ is NOT risk loving.** Convexity would force the chord to lie
above the graph, i.e. `√(1/2) ≤ (√0 + √1)/2 = 1/2`, but `√(1/2) > 1/2`. This is the witness that
catches an averse-vs-loving reversal in the predicate sense. -/
theorem sqrt_not_riskLoving : ¬ RiskLoving Real.sqrt (Set.Ici 0) := by
  intro hconvex
  -- Midpoint convexity at `0` and `1` with weights `1/2, 1/2`.
  have hmid := hconvex.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  -- `√(1/2) ≤ 1/2`.
  have hle : Real.sqrt (1/2) ≤ 1/2 := by
    simpa using hmid
  -- But `1/2 < √(1/2)` since `(1/2)² = 1/4 < 1/2`.
  have hlt : (1:ℝ)/2 < Real.sqrt (1/2) := by
    rw [show (1:ℝ)/2 = ((1:ℝ)/2) from rfl, Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- The convex utility `x ↦ x²` is **risk loving** on all of `ℝ`: Definitionally
`ConvexOn ℝ univ`. -/
theorem sq_riskLoving : RiskLoving (fun x => x ^ 2) Set.univ :=
  Even.convexOn_pow (by norm_num : Even 2)

/-- **Negative check: The convex `x²` is NOT risk averse.** Concavity would force
`(midpoint 0 2)² = 1 ≥ (0² + 2²)/2 = 2`, i.e. `1 ≥ 2`. This is the dual direction check. -/
theorem sq_not_riskAverse : ¬ RiskAverse (fun x => x ^ 2) Set.univ := by
  intro hconcave
  -- Midpoint concavity at `0` and `2` with weights `1/2, 1/2`: `1 ≥ 2`, contradiction.
  have hmid := hconcave.2 (Set.mem_univ 0) (Set.mem_univ 2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  norm_num at hmid

/-- An affine utility `u(x) = 2x + 3` is exactly **risk neutral** on all of `ℝ`. -/
theorem affine_riskNeutral : RiskNeutral (fun x => 2 * x + 3) Set.univ :=
  ⟨2, 3, fun _ _ => rfl⟩

end Predicates

/-! ## 2. Arrow–Pratt round-trip

The headline characterization is `A(x) = -u''(x)/u'(x) ≥ 0 ↔ ConcaveOn`. We exercise it on the
CARA agent (`A ≡ α`), the affine agent (`A ≡ 0 ↔ affine`), and confirm the closed-form endpoints
`absoluteRiskAversion_eq_alpha` / `relativeRiskAversion_eq_gamma`, plus the curvature lemmas that
sit behind the main theorem on a concrete `TwiceDiffUtility`. -/

section ArrowPratt

/-- The CARA agent with `α = 2`, packaged as a `TwiceDiffUtility` via `toTwiceDiffUtility`. -/
private def cara2 : ConstantAbsoluteRiskAversionUtility where
  α := 2
  α_pos := two_pos

/-- The affine `TwiceDiffUtility` `u(x) = 2x + 3`, `u' ≡ 2`, `u'' ≡ 0` on all of `ℝ`. The boundary
witness for `risk_neutral_iff_absoluteRiskAversion_zero` and `u'_eq_of_u''_zero`. -/
private def affine2 : TwiceDiffUtility where
  u x := 2 * x + 3
  u' _ := 2
  u'' _ := 0
  domain := Set.univ
  domain_open := isOpen_univ
  domain_convex := convex_univ
  domain_nonempty := Set.univ_nonempty
  has_deriv x _ := by
    simpa using (hasDerivAt_const_mul (x := x) (2 : ℝ)).add_const 3
  has_second_deriv x _ := hasDerivAt_const x 2
  u'_pos _ _ := by norm_num

/-- **Closed-form CARA endpoint.** `absoluteRiskAversion_eq_alpha`: The Arrow–Pratt coefficient of
the CARA agent is the constant `α = 2` at every wealth level. -/
theorem cara2_ara_eq (x : ℝ) :
    cara2.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_univ x) = 2 :=
  cara2.absoluteRiskAversion_eq_alpha x (Set.mem_univ x)

/-- **Arrow–Pratt → concavity (averse direction).** Feeding the constant `A ≡ 2 ≥ 0` through
`risk_averse_iff_absoluteRiskAversion_nonneg` recovers concavity of the CARA utility. -/
theorem cara2_concave :
    ConcaveOn ℝ cara2.toTwiceDiffUtility.domain cara2.toTwiceDiffUtility.u := by
  rw [← cara2.toTwiceDiffUtility.risk_averse_iff_absoluteRiskAversion_nonneg]
  intro x hx
  rw [cara2.absoluteRiskAversion_eq_alpha x hx]
  norm_num [cara2]

/-- **Strict Arrow–Pratt → strict concavity.** `A ≡ 2 > 0` with `u'' ≠ 0` everywhere gives strict
concavity through `strictly_risk_averse_iff_absoluteRiskAversion_pos`. -/
theorem cara2_strictConcave :
    StrictConcaveOn ℝ cara2.toTwiceDiffUtility.domain cara2.toTwiceDiffUtility.u := by
  have h_nz : ∀ x ∈ cara2.toTwiceDiffUtility.domain, cara2.toTwiceDiffUtility.u'' x ≠ 0 := by
    intro x _
    -- `u''(x) = -(2²)·exp(-2x) < 0 ≠ 0`.
    simp only [cara2, ConstantAbsoluteRiskAversionUtility.toTwiceDiffUtility]
    have hexp : 0 < Real.exp (-(2 : ℝ) * x) := Real.exp_pos _
    nlinarith [hexp]
  rw [← cara2.toTwiceDiffUtility.strictly_risk_averse_iff_absoluteRiskAversion_pos h_nz]
  intro x hx
  rw [cara2.absoluteRiskAversion_eq_alpha x hx]
  norm_num [cara2]

/-- Everywhere-nonzero second derivative of CARA, reused by the opposite-direction witnesses below.
`u''(x) = -(2²)·exp(-2x) < 0 ≠ 0`. -/
private theorem cara2_u''_nz :
    ∀ x ∈ cara2.toTwiceDiffUtility.domain, cara2.toTwiceDiffUtility.u'' x ≠ 0 := by
  intro x _
  simp only [cara2, ConstantAbsoluteRiskAversionUtility.toTwiceDiffUtility]
  have hexp : 0 < Real.exp (-(2 : ℝ) * x) := Real.exp_pos _
  nlinarith [hexp]

/-- **Opposite direction: concavity → `A ≥ 0`.** `cara2_concave` ran the iff the *other* way
(`A ≥ 0 ⇒ ConcaveOn`); here we feed the *independently proved* library concavity
`concaveOn_u` through the `.mpr` direction of
`risk_averse_iff_absoluteRiskAversion_nonneg` and recover `A ≥ 0`. This catches a regression in the
`ConcaveOn → A ≥ 0` half of the round-trip. -/
theorem cara2_ara_nonneg_of_concave :
    ∀ x (hx : x ∈ cara2.toTwiceDiffUtility.domain),
      0 ≤ cara2.toTwiceDiffUtility.absoluteRiskAversion x hx :=
  (cara2.toTwiceDiffUtility.risk_averse_iff_absoluteRiskAversion_nonneg).mpr
    cara2.concaveOn_u

/-- **Opposite direction: strict concavity → `A > 0`.** Feeds the independently proved
`cara2_strictConcave` through the `.mpr` direction of
`strictly_risk_averse_iff_absoluteRiskAversion_pos`, recovering `A > 0`. Catches a regression in the
`StrictConcaveOn → A > 0` half. -/
theorem cara2_ara_pos_of_strictConcave :
    ∀ x (hx : x ∈ cara2.toTwiceDiffUtility.domain),
      0 < cara2.toTwiceDiffUtility.absoluteRiskAversion x hx :=
  (cara2.toTwiceDiffUtility.strictly_risk_averse_iff_absoluteRiskAversion_pos cara2_u''_nz).mpr
    cara2_strictConcave

/-- **Affine ↔ zero Arrow–Pratt, reverse direction (affine ⇒ `A ≡ 0`).** The affine agent has
`A ≡ 0`, via the `.mpr` of `risk_neutral_iff_absoluteRiskAversion_zero`. -/
theorem affine2_ara_zero (x : ℝ) :
    affine2.absoluteRiskAversion x (Set.mem_univ x) = 0 := by
  -- Use the `← ` direction of the characterization: affinity forces `A ≡ 0`.
  have haffine : ∃ a b, ∀ x ∈ affine2.domain, affine2.u x = a * x + b :=
    ⟨2, 3, fun _ _ => rfl⟩
  exact (affine2.risk_neutral_iff_absoluteRiskAversion_zero.mpr haffine) x (Set.mem_univ x)

/-- **Opposite direction: `A ≡ 0` ⇒ affine.** Computes `A(x) = -u''/u' = -0/2 = 0` directly from
the affine agent's bundled fields and pushes it through the `.mp` direction of
`risk_neutral_iff_absoluteRiskAversion_zero`, recovering affinity. This exercises the
characterization's harder direction (the MVT-based constancy argument), not just the easy
`affine ⇒ A ≡ 0`. -/
theorem affine2_affine_of_ara_zero :
    ∃ a b, ∀ x ∈ affine2.domain, affine2.u x = a * x + b :=
  affine2.risk_neutral_iff_absoluteRiskAversion_zero.mp <| fun x _ => by
    simp only [TwiceDiffUtility.absoluteRiskAversion]; change -(0 : ℝ) / 2 = 0; norm_num

/-- **Curvature lemma `absoluteRiskAversion_nonneg_iff` at *nonzero* curvature.** On the affine
agent the iff degenerates to `0 ≤ 0 ↔ 0 ≤ 0`; here it is anchored on the CARA agent, whose
`A ≡ 2 > 0` and `u'' < 0` make *both* sides of `0 ≤ A(x) ↔ u''(x) ≤ 0` genuinely (and
non-degenerately) true. A sign flip in `A = -u''/u'` would desynchronize the two sides. -/
theorem cara2_ara_nonneg_iff (x : ℝ) :
    (0 ≤ cara2.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_univ x)) ↔
      cara2.toTwiceDiffUtility.u'' x ≤ 0 :=
  cara2.toTwiceDiffUtility.absoluteRiskAversion_nonneg_iff x (Set.mem_univ x)

/-- The CARA curvature iff resolves to a genuine *true ↔ true* with both sides strict, not the
degenerate `0 ≤ 0 ↔ 0 ≤ 0` of the affine case: `A(x) = 2 > 0` so `0 ≤ A(x)`, and `u''(x) < 0`. -/
theorem cara2_ara_nonneg_iff_resolved (x : ℝ) :
    (0 ≤ cara2.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_univ x)) ∧
      cara2.toTwiceDiffUtility.u'' x < 0 := by
  have hara : cara2.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_univ x) = 2 :=
    cara2.absoluteRiskAversion_eq_alpha x (Set.mem_univ x)
  refine ⟨by rw [hara]; norm_num, ?_⟩
  have := cara2_u''_nz x (Set.mem_univ x)
  -- `u'' x ≤ 0` (from the iff at this true LHS) plus `u'' x ≠ 0` gives strict negativity.
  have hle : cara2.toTwiceDiffUtility.u'' x ≤ 0 :=
    (cara2_ara_nonneg_iff x).mp (by rw [hara]; norm_num)
  exact lt_of_le_of_ne hle this

/-- **`absoluteRiskAversion_nonneg_iff` on the affine agent (degenerate companion).** Kept as an
explicit API-instantiation smoke test: here the iff reads `0 ≤ 0 ↔ 0 ≤ 0`. The discriminating
version is `cara2_ara_nonneg_iff` above. -/
theorem affine2_ara_nonneg_iff :
    (0 ≤ affine2.absoluteRiskAversion 1 (Set.mem_univ 1)) ↔ affine2.u'' 1 ≤ 0 :=
  affine2.absoluteRiskAversion_nonneg_iff 1 (Set.mem_univ 1)

/-- **Curvature lemma `u'_eq_of_u''_zero` (API instantiation).** The affine agent has `u'' ≡ 0`, so
its marginal utility is constant: `u'(0) = u'(1)`. (Both sides are `2`, so this is an
API-availability smoke test, not a discriminating anchor.) -/
theorem affine2_u'_const : affine2.u' 0 = affine2.u' 1 :=
  affine2.u'_eq_of_u''_zero (fun _ _ => rfl) (Set.mem_univ 0) (Set.mem_univ 1)

/-- **Curvature lemma `Icc_subset_domain` (API instantiation).** Between two domain points the whole
interval lies in the (here universal) domain. With `domain = univ` the containment `Icc 0 1 ⊆ univ`
is trivial — an API-availability smoke test. -/
theorem affine2_Icc_subset : Set.Icc (0:ℝ) 1 ⊆ affine2.domain :=
  affine2.Icc_subset_domain (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num)

/-- **Curvature lemma `u'_strict_anti` → `strict_concave_of_strict_anti_u'` chain is non-vacuous**
on CARA, whose `u''(x) < 0` everywhere makes `u'` strictly antitone and `u` strictly concave. -/
theorem cara2_strictAnti_u' :
    StrictAntiOn cara2.toTwiceDiffUtility.u' cara2.toTwiceDiffUtility.domain := by
  apply cara2.toTwiceDiffUtility.u'_strict_anti
  intro x _
  -- `u''(x) = -(2²)·exp(-2x) < 0`.
  simp only [cara2, ConstantAbsoluteRiskAversionUtility.toTwiceDiffUtility]
  have hexp : 0 < Real.exp (-(2 : ℝ) * x) := Real.exp_pos _
  nlinarith [hexp]

/-- The strict-concavity conclusion of the `strict_anti_u'` chain, on CARA. -/
theorem cara2_strictConcave_via_anti :
    StrictConcaveOn ℝ cara2.toTwiceDiffUtility.domain cara2.toTwiceDiffUtility.u :=
  cara2.toTwiceDiffUtility.strict_concave_of_strict_anti_u' cara2_strictAnti_u'

end ArrowPratt

/-! ## 3. Certainty-equivalent Jensen gap

The discriminating fifty-fifty bet `sqrtBet` over `{1, 4}` (mean `5/2`). On the square root agent
the certainty equivalent is *exactly* `9/4 < 5/2` (anchored), so the risk premium is the anchored
positive number `1/4`. The named strict-Jensen lemmas are exercised *directly* on `√`: since they
require only `StrictMonoOn √ (Ici 0)` (not global `StrictMono √`, which is false), `√` feeds them
with the outcomes and the certainty equivalent supplied as members of the domain `[0, ∞)`. The
affine agent's CE equals the mean (zero premium). -/

section CertaintyEquivalent

/-- The fair fifty-fifty money lottery over `Fin 2`: Prizes `![0, 1]` under the fair coin. -/
private def fairBet : FinLottery 2 where
  outcome := ![0, 1]
  prob := finDist% ![1 / 2, 1 / 2]

/-- The lottery is non-degenerate: Two distinct outcomes of positive probability. -/
private theorem fairBet_nondeg :
    ∃ i j, 0 < fairBet.prob.pmf i ∧ 0 < fairBet.prob.pmf j ∧
      fairBet.outcome i ≠ fairBet.outcome j :=
  ⟨0, 1, by norm_num [fairBet], by norm_num [fairBet], by norm_num [fairBet]⟩

/-- The mean of the fair bet is `1/2`. -/
private theorem fairBet_mean : ∑ i, fairBet.prob.pmf i * fairBet.outcome i = 1 / 2 := by
  simp [fairBet, Fin.sum_univ_two]

/-- A *discriminating* fifty-fifty lottery over `Fin 2` with prizes `![1, 4]`. Unlike `fairBet` over
`{0, 1}` — where `𝔼[X] = 𝔼[√X] = 1/2`, so a buggy CE using expected *wealth* in place of expected
*utility* gives the same answer — here `𝔼[X] = 5/2 ≠ 3/2 = 𝔼[√X]`, so the two readings of the CE
definition diverge. -/
private def sqrtBet : FinLottery 2 where
  outcome := ![1, 4]
  prob := finDist% ![1 / 2, 1 / 2]

/-- The mean of `sqrtBet` is `5/2` (`(1 + 4)/2`). -/
private theorem sqrtBet_mean : ∑ i, sqrtBet.prob.pmf i * sqrtBet.outcome i = 5 / 2 := by
  simp [sqrtBet, Fin.sum_univ_two]; norm_num

/-- `sqrtBet` is non-degenerate: Two distinct outcomes of positive probability. -/
private theorem sqrtBet_nondeg :
    ∃ i j, 0 < sqrtBet.prob.pmf i ∧ 0 < sqrtBet.prob.pmf j ∧
      sqrtBet.outcome i ≠ sqrtBet.outcome j :=
  ⟨0, 1, by norm_num [sqrtBet], by norm_num [sqrtBet], by norm_num [sqrtBet]⟩

/-- Both outcomes of `sqrtBet` lie in `√`'s strict-monotonicity / strict-concavity domain `[0, ∞)`,
the membership the weakened (`StrictMonoOn`-based) certainty-equivalent lemmas require. -/
private theorem sqrtBet_outcomes_mem : ∀ i, sqrtBet.outcome i ∈ Set.Ici (0 : ℝ) := by
  intro i; fin_cases i <;> norm_num [sqrtBet]

/-! ### Existence and uniqueness -/

/-- A certainty equivalent of the fair bet under `√` exists (continuity + IVT). -/
theorem sqrt_ce_exists : ∃ c, IsCertaintyEquivalent Real.sqrt fairBet c :=
  certainty_equivalent_exists Real.continuous_sqrt

/-- **The √ certainty equivalent of `sqrtBet` is exactly `9/4`.** Hand check: `𝔼[√X] = (√1 + √4)/2
= (1 + 2)/2 = 3/2`, and the unique `c` with `√c = 3/2` is `c = (3/2)² = 9/4`. This anchor
*discriminates* against a CE computed from expected wealth: that buggy reading would solve
`√c = 𝔼[X] = 5/2`, giving `c = 25/4 ≠ 9/4`. -/
theorem sqrt_ce_eq_quarter : IsCertaintyEquivalent Real.sqrt sqrtBet (9 / 4) := by
  unfold IsCertaintyEquivalent
  rw [show (9:ℝ)/4 = (3/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [sqrtBet, Fin.sum_univ_two, FinDist.ofVec_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.sqrt_one]
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **The anchored Jensen gap, through the named strict lemma on √.** The √ certainty equivalent
`9/4` is strictly below the mean `5/2` (`9/4 = 2.25 < 2.5`). This now goes *through*
`certainty_equivalent_lt_expected_value_of_strict_concave` fed directly by `√` — possible only
because that lemma takes `StrictMonoOn √ (Ici 0)` (`Real.strictMonoOn_sqrt`) rather than global
`StrictMono √` (which is false: `√` is constant `0` on the negatives). The certainty equivalent
`9/4` and the outcomes `{1, 4}` all lie in the domain `[0, ∞)`. -/
theorem sqrt_ce_lt_mean : (9 / 4 : ℝ) < ∑ i, sqrtBet.prob.pmf i * sqrtBet.outcome i :=
  certainty_equivalent_lt_expected_value_of_strict_concave Real.strictMonoOn_sqrt
    sqrt_strictlyRiskAverse sqrtBet_outcomes_mem (Set.mem_Ici.mpr (by norm_num))
    sqrtBet_nondeg sqrt_ce_eq_quarter

/-- **The anchored risk premium.** `riskPremium = 𝔼[X] − c = 5/2 − 9/4 = 1/4 > 0`. The sign and the
exact value catch a premium accidentally computed as `c − 𝔼[X]` (which would be `-1/4`). -/
theorem sqrt_riskPremium_eq_quarter : riskPremium sqrtBet (9 / 4) = 1 / 4 := by
  simp only [riskPremium, FinLottery.expectedValue_eq_sum]
  rw [sqrtBet_mean]; norm_num

/-! ### The named strict-Jensen lemmas, exercised directly on the √ agent

Because the certainty-equivalent lemmas now require only `StrictMonoOn u s` on the concavity domain
`s` — not global `StrictMono u` — the canonical strictly concave money utility `√`, which is
strictly increasing only on `[0, ∞)`, feeds them directly. The certainty equivalent `9/4` and the
outcomes `{1, 4}` of `sqrtBet` all live in `[0, ∞)`, so the membership side conditions discharge by
`norm_num`. (Previously these had to be routed through a globally strict-mono CARA surrogate; that
detour is no longer necessary.) -/

/-- **`certainty_equivalent_unique` on √.** Any two √ certainty equivalents of `sqrtBet` lying in
the domain `[0, ∞)` coincide. Strict monotonicity *on the domain* is all that uniqueness needs. -/
theorem sqrt_ce_unique {c₁ c₂ : ℝ} (hc₁s : c₁ ∈ Set.Ici (0 : ℝ)) (hc₂s : c₂ ∈ Set.Ici (0 : ℝ))
    (hc₁ : IsCertaintyEquivalent Real.sqrt sqrtBet c₁)
    (hc₂ : IsCertaintyEquivalent Real.sqrt sqrtBet c₂) : c₁ = c₂ :=
  certainty_equivalent_unique Real.strictMonoOn_sqrt hc₁s hc₂s hc₁ hc₂

/-- **`certainty_equivalent_unique` is non-vacuous** — the concrete √ CE `9/4` of `sqrtBet` is
forced unique among domain-valued certainty equivalents. -/
theorem sqrt_ce_unique_anchor {c : ℝ} (hcs : c ∈ Set.Ici (0 : ℝ))
    (hc : IsCertaintyEquivalent Real.sqrt sqrtBet c) : c = 9 / 4 :=
  sqrt_ce_unique hcs (Set.mem_Ici.mpr (by norm_num)) hc sqrt_ce_eq_quarter

/-- **`risk_premium_pos_of_strict_concave` is non-vacuous on √.** The √ risk premium of `sqrtBet` is
strictly positive, obtained through the named strict lemma fed directly by `√`. -/
theorem sqrt_riskPremium_pos : 0 < riskPremium sqrtBet (9 / 4) :=
  risk_premium_pos_of_strict_concave Real.strictMonoOn_sqrt sqrt_strictlyRiskAverse
    sqrtBet_outcomes_mem (Set.mem_Ici.mpr (by norm_num)) sqrtBet_nondeg sqrt_ce_eq_quarter

/-! ### Affine agent: Zero risk premium -/

/-- **The affine CE is concretely realized.** Hand check: `u(x) = 2x + 3`, so
`𝔼[u(X)] = (u 0 + u 1)/2 = (3 + 5)/2 = 4`, and `u(1/2) = 2·(1/2) + 3 = 4`; hence `1/2` is a
certainty equivalent. This discharges the CE hypothesis the affine theorems below assume, rather
than leaving it conditional. -/
theorem affine_ce_concrete : IsCertaintyEquivalent (fun x => 2 * x + 3) fairBet (1 / 2) := by
  unfold IsCertaintyEquivalent
  simp only [fairBet, Fin.sum_univ_two, FinDist.ofVec_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- **`certainty_equivalent_eq_expected_value_of_affine` is non-vacuous.** Under the affine utility
`u(x) = 2x + 3`, the CE equals the mean `1/2`. -/
theorem affine_ce_eq_mean {c : ℝ} (hc : IsCertaintyEquivalent (fun x => 2 * x + 3) fairBet c) :
    c = 1 / 2 := by
  have h := certainty_equivalent_eq_expected_value_of_affine
    (u := fun x => 2 * x + 3) (L := fairBet)
    ⟨2, 3, by norm_num, fun _ => rfl⟩ hc
  rwa [FinLottery.expectedValue_eq_sum, fairBet_mean] at h

/-- **The affine risk premium is exactly zero** — and this is now formalized, not merely claimed in
prose. The concrete CE `1/2` (from `affine_ce_concrete`) forces `riskPremium = 𝔼[X] − c =
1/2 − 1/2 = 0`. A risk-neutral agent pays nothing to shed risk. -/
theorem affine_riskPremium_zero : riskPremium fairBet (1 / 2) = 0 := by
  simp only [riskPremium, FinLottery.expectedValue_eq_sum]
  rw [fairBet_mean]; norm_num

/-! ### Predicate-level lottery wrappers -/

/-- **`RiskAverse.le_map_sum` (Jensen for the averse agent).** `𝔼[u(X)] ≤ u(𝔼[X])`. -/
theorem sqrt_le_map_sum :
    ∑ i, fairBet.prob.pmf i * Real.sqrt (fairBet.outcome i) ≤
      Real.sqrt (∑ i, fairBet.prob.pmf i * fairBet.outcome i) :=
  sqrt_riskAverse.le_map_sum (fun i => by fin_cases i <;> norm_num [fairBet])

/-- **`RiskAverse.certainty_equivalent_le_expected_value` on √.** The √ CE of `sqrtBet` (in the
domain `[0, ∞)`) is `≤` the mean. The predicate wrapper now takes `StrictMonoOn √ (Ici 0)`. -/
theorem sqrt_ce_le_mean {c : ℝ} (hcs : c ∈ Set.Ici (0 : ℝ))
    (hc : IsCertaintyEquivalent Real.sqrt sqrtBet c) :
    c ≤ ∑ i, sqrtBet.prob.pmf i * sqrtBet.outcome i :=
  sqrt_riskAverse.certainty_equivalent_le_expected_value
    Real.strictMonoOn_sqrt sqrtBet_outcomes_mem hcs hc

/-- **`RiskAverse.risk_premium_nonneg` on √.** √ premium `≥ 0`. -/
theorem sqrt_riskPremium_nonneg {c : ℝ} (hcs : c ∈ Set.Ici (0 : ℝ))
    (hc : IsCertaintyEquivalent Real.sqrt sqrtBet c) :
    0 ≤ riskPremium sqrtBet c :=
  sqrt_riskAverse.risk_premium_nonneg
    Real.strictMonoOn_sqrt sqrtBet_outcomes_mem hcs hc

/-- **`StrictlyRiskAverse.risk_premium_pos` on √ (predicate form).** Strict √ premium `> 0`. -/
theorem sqrt_riskPremium_pos_pred {c : ℝ} (hcs : c ∈ Set.Ici (0 : ℝ))
    (hc : IsCertaintyEquivalent Real.sqrt sqrtBet c) :
    0 < riskPremium sqrtBet c :=
  StrictlyRiskAverse.risk_premium_pos sqrt_strictlyRiskAverse
    Real.strictMonoOn_sqrt sqrtBet_outcomes_mem hcs sqrtBet_nondeg hc

/-- **`RiskLoving.le_map_sum` (Jensen for the loving agent).** `u(𝔼[X]) ≤ 𝔼[u(X)]` for `x²`. -/
theorem sq_le_map_sum :
    (fun x => x ^ 2) (∑ i, fairBet.prob.pmf i * fairBet.outcome i) ≤
      ∑ i, fairBet.prob.pmf i * (fun x => x ^ 2) (fairBet.outcome i) :=
  sq_riskLoving.le_map_sum (fun _ => Set.mem_univ _)

/-- **`RiskNeutral.map_sum_eq` (indifference for the neutral agent).** `𝔼[u(X)] = u(𝔼[X])` for the
affine `u`. -/
theorem affine_map_sum_eq :
    ∑ i, fairBet.prob.pmf i * (fun x => 2 * x + 3) (fairBet.outcome i) =
      (fun x => 2 * x + 3) (∑ i, fairBet.prob.pmf i * fairBet.outcome i) :=
  affine_riskNeutral.map_sum_eq (fun _ => Set.mem_univ _) (Set.mem_univ _)

end CertaintyEquivalent

/-! ## 4. Comparative ordering of two CRRA agents

Two CRRA agents with `γ₁ = 2 > 1/2 = γ₂`. CRRA absolute risk aversion is `A(x) = γ/x`, so the
higher-`γ` agent is pointwise more risk averse, and over a common positive-outcome lottery its
certainty equivalent is lower. -/

section Comparative

/-- The more risk-averse CRRA agent, `γ = 2`. -/
private def crraHi : ConstantRelativeRiskAversionUtility where
  γ := 2
  γ_pos := two_pos
  γ_ne_one := by norm_num

/-- The less risk-averse CRRA agent, `γ = 1/2`. -/
private def crraLo : ConstantRelativeRiskAversionUtility where
  γ := 1 / 2
  γ_pos := by norm_num
  γ_ne_one := by norm_num

/-- **`relativeRiskAversion_eq_gamma` round-trip.** The relative risk aversion of `crraHi` is the
constant `γ = 2` at every positive wealth level. -/
theorem crraHi_rra_eq (x : ℝ) (hx : 0 < x) :
    crraHi.toTwiceDiffUtility.relativeRiskAversion x (Set.mem_Ioi.mpr hx) = 2 :=
  crraHi.relativeRiskAversion_eq_gamma x hx

/-- The CRRA absolute risk aversion is `A(x) = γ/x`. Derived from `relativeRiskAversion = γ` and
the identity `relativeRiskAversion = x · absoluteRiskAversion`. -/
private theorem crra_ara_eq (c : ConstantRelativeRiskAversionUtility) (x : ℝ) (hx : 0 < x) :
    c.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_Ioi.mpr hx) = c.γ / x := by
  -- `A = -(u'')/(u') = -(-γ·x^(-γ-1))/x^(-γ) = γ·x^(-γ-1)/x^(-γ) = γ/x`.
  change -(c.toTwiceDiffUtility.u'' x) / c.toTwiceDiffUtility.u' x = c.γ / x
  have h_u' : c.toTwiceDiffUtility.u' x = x ^ (-c.γ) := dif_pos hx
  have h_u'' : c.toTwiceDiffUtility.u'' x = -c.γ * x ^ (-c.γ - 1) := dif_pos hx
  rw [h_u', h_u'']
  have hpow_ne : x ^ (-c.γ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hx_ne : x ≠ 0 := ne_of_gt hx
  -- `x^(-γ-1) = x^(-γ) · x⁻¹`, so `γ·x^(-γ-1)/x^(-γ) = γ/x`.
  have h_split : x ^ (-c.γ - 1) = x ^ (-c.γ) * x⁻¹ := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hx]; ring_nf
  rw [h_split]
  field_simp

theorem crraHi_ara_eq (x : ℝ) (hx : 0 < x) :
    crraHi.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_Ioi.mpr hx) = 2 / x :=
  crra_ara_eq crraHi x hx

theorem crraLo_ara_eq (x : ℝ) (hx : 0 < x) :
    crraLo.toTwiceDiffUtility.absoluteRiskAversion x (Set.mem_Ioi.mpr hx) = (1 / 2) / x :=
  crra_ara_eq crraLo x hx

private theorem crra_same_domain :
    crraHi.toTwiceDiffUtility.domain = crraLo.toTwiceDiffUtility.domain := rfl

/-- **`more_risk_averse_iff_absoluteRiskAversion_ge` orders the two agents correctly.** Pointwise
`A_hi(x) = 2/x ≥ (1/2)/x = A_lo(x)` on `(0, ∞)`, which *is* Pratt's `MoreRiskAverseOn`. -/
theorem crraHi_more_risk_averse :
    MoreRiskAverseOn crraHi.toTwiceDiffUtility.u crraLo.toTwiceDiffUtility.u
      crraLo.toTwiceDiffUtility.domain := by
  rw [more_risk_averse_iff_absoluteRiskAversion_ge _ _ crra_same_domain]
  intro x hx_hi hx_lo
  have hx : 0 < x := hx_lo
  rw [crraHi_ara_eq x hx, crraLo_ara_eq x hx]
  -- `2/x ≥ (1/2)/x` since `x > 0` and `1/2 ≤ 2`.
  rw [ge_iff_le]
  gcongr
  norm_num

/-- A common positive-outcome lottery `![1, 4]` under the fair coin. -/
private def posBet : FinLottery 2 where
  outcome := ![1, 4]
  prob := finDist% ![1 / 2, 1 / 2]

/-- Closed form of the `γ = 2` utility on the positive reals: `u_hi(y) = -y⁻¹`.
(`x^(1-2)/(1-2) =
x^(-1)/(-1) = -x⁻¹`.) -/
private theorem crraHi_u_eq (y : ℝ) (hy : 0 < y) :
    crraHi.toTwiceDiffUtility.u y = -y⁻¹ := by
  change (if hy : 0 < y then crraHi.u y hy else 0) = -y⁻¹
  rw [dif_pos hy, ConstantRelativeRiskAversionUtility.u_def]
  change y ^ (1 - (2 : ℝ)) / (1 - (2 : ℝ)) = -y⁻¹
  rw [show (1 - (2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- Closed form of the `γ = 1/2` utility on the positive reals: `u_lo(y) = 2·√y`.
(`x^(1-1/2)/(1-1/2)
= x^(1/2)/(1/2) = 2·√x`.) -/
private theorem crraLo_u_eq (y : ℝ) (hy : 0 < y) :
    crraLo.toTwiceDiffUtility.u y = 2 * Real.sqrt y := by
  change (if hy : 0 < y then crraLo.u y hy else 0) = 2 * Real.sqrt y
  rw [dif_pos hy, ConstantRelativeRiskAversionUtility.u_def]
  change y ^ (1 - (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) = 2 * Real.sqrt y
  rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  ring

/-- The high-`γ` certainty equivalent: `8/5`. (`u_hi(x) = -x⁻¹`, `𝔼[u] = -5/8`, `c` solves
`-c⁻¹ = -5/8`.) -/
theorem crraHi_ce_eq : IsCertaintyEquivalent crraHi.toTwiceDiffUtility.u posBet (8 / 5) := by
  unfold IsCertaintyEquivalent
  rw [crraHi_u_eq _ (by norm_num)]
  simp only [posBet, Fin.sum_univ_two, FinDist.ofVec_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [crraHi_u_eq _ (by norm_num), crraHi_u_eq _ (by norm_num)]
  norm_num

/-- The low-`γ` certainty equivalent: `9/4`. (`u_lo(x) = 2√x`, `𝔼[u] = 3`, `c` solves `2√c = 3`.) -/
theorem crraLo_ce_eq : IsCertaintyEquivalent crraLo.toTwiceDiffUtility.u posBet (9 / 4) := by
  unfold IsCertaintyEquivalent
  rw [crraLo_u_eq _ (by norm_num)]
  simp only [posBet, Fin.sum_univ_two, FinDist.ofVec_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [crraLo_u_eq _ (by norm_num), crraLo_u_eq _ (by norm_num)]
  rw [show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num), Real.sqrt_one]
  norm_num

/-- **`MoreRiskAverseOn.le_certaintyEquivalent`, full semantic package.** The exported
statement records the *entire* comparative claim rather than the bare arithmetic `8/5 ≤ 9/4`: the
high-`γ` agent is `MoreRiskAverseOn` the low-`γ` agent, `8/5` is the high-`γ` CE of `posBet`, `9/4`
is the low-`γ` CE, and — *the conclusion the comparative theorem delivers* — the more-averse
agent's CE is the lower one (`8/5 ≤ 9/4`). A reviewer reading the signature sees the comparative
content, not a free-standing inequality. -/
theorem crraHi_lower_ce :
    MoreRiskAverseOn crraHi.toTwiceDiffUtility.u crraLo.toTwiceDiffUtility.u
        crraLo.toTwiceDiffUtility.domain ∧
      IsCertaintyEquivalent crraHi.toTwiceDiffUtility.u posBet (8 / 5) ∧
      IsCertaintyEquivalent crraLo.toTwiceDiffUtility.u posBet (9 / 4) ∧
      (8 / 5 : ℝ) ≤ 9 / 4 :=
  ⟨crraHi_more_risk_averse, crraHi_ce_eq, crraLo_ce_eq,
   MoreRiskAverseOn.le_certaintyEquivalent
    crraHi.toTwiceDiffUtility crraLo.toTwiceDiffUtility crra_same_domain posBet
    (fun i => by
      fin_cases i <;>
        simp only [posBet, ConstantRelativeRiskAversionUtility.toTwiceDiffUtility,
          Set.mem_Ioi] <;>
        norm_num)
    crraHi_more_risk_averse (8 / 5) (9 / 4)
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by norm_num))
    crraHi_ce_eq crraLo_ce_eq⟩

end Comparative

end EconlibTest.Preferences.Risk
