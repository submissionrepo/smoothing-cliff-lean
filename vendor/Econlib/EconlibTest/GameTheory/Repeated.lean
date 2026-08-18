/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import Mathlib

/-!
# Repeated Games / Grim Trigger — Non-Vacuity & Discount-Threshold Checks

Compile-time semantic witnesses for the infinite-horizon discounted repeated-game layer
(`Econlib.GameTheory.Repeated.{Basic, OneShotDeviation, GrimTrigger}`), anchored on a
self-contained repeated Prisoner's Dilemma fixture defined below (a test never depends on an
example).

## The hand-computed economics

The stage game is the classical PD with `T = 5`, `R = 3`, `P = 1`, `S = 0` (`pd`), payoff to the
mover: `(C,C) ↦ 3`, `(D|C) ↦ 5`, `(C|D) ↦ 0`, `(D,D) ↦ 1`.

* **Minmax.** The opponent holds player `i` down by *defecting*; `i`'s best response to a defecting
  opponent is to defect, earning `P = 1`. So `MinmaxValue i = 1`, the mutual-defection payoff. The
  cooperative payoff `3` is strictly above `1` — IR is the *above-minmax* direction.
* **Discount threshold.** Along the clean (cooperative) path the normalized continuation value is
  `R = 3`. A one-shot deviation to defect yields `(1-δ)·T + δ·P = (1-δ)·5 + δ·1 = 5 - 4δ`, after
  which the opponent's grim trigger inflicts mutual defection forever. The deviation is
  *unprofitable* iff `5 - 4δ ≤ 3 ⟺ δ ≥ 1/2`. The threshold is **exactly `δ = 1/2`**.

We verify **both sides** of the threshold on the *same stage game* (so any reuse is honest):

* `repeatedPDpatient` at `δ = 3/4 > 1/2`: `5 - 4·(3/4) = 2 < 3`, grim trigger *is* an SPE
  (`grimTrigger_SPE_patient`, via the one-shot deviation principle on a strict-margin deviation).
* `repeatedPDimpatient` at `δ = 1/4 < 1/2`: `5 - 4·(1/4) = 4 > 3`, a one-shot defection at the
  empty (clean) history is *strictly profitable*, so grim trigger *fails* to be an SPE
  (`grimTrigger_not_SPE_impatient`).
* The boundary `δ = 1/2` (`repeatedPD`): Grim trigger is an SPE, derived from the library
  `grimTrigger_isSubgamePerfectEquilibrium`, where the defect deviation is *exactly* indifferent
  (`devDefect_indifferent_boundary`: Deviation value `= 3 = cv grimTrigger`).

## Failure modes caught

* **δ comparison-direction flip** (patient vs. impatient): The negative direction at `δ = 1/4` is
  the high-value witness — a reversed `IsSufficientlyPatient` (`δ ≤ δ₀` instead of `δ₀ ≤ δ`) or a
  flipped one-shot-deviation inequality would let the impatient game pass.
* **discount-bound endpoint flip**: The threshold is `δ ≥ 1/2`; both `3/4` and `1/4` sit on
  opposite sides, catching an off-by-the-endpoint error.
* **minmax above/below reversal**: IR requires `MinmaxValue i ≤ w i`; the cooperative `3 > 1`
  witness fails immediately if the inequality is reversed.
* **vacuous patience / summability**: `IsSufficientlyPatient` and
  `summable_discount_periodExpectedPayoff` genuinely use `δ < 1`.

The grim-trigger *strategy* `grimTrigger`, the `grimTriggerPure` rule and `IsClean` predicate are
thin local aliases of the library `RepeatedGame.{grimTriggerStrategy, grimTrigger, IsClean}` at the
PD's cooperative / defection profiles: They depend on the stage game only, not on the discount
factor, so the very same behavioral strategy serves all three discount factors.
-/

noncomputable section

namespace EconlibTest.GameTheory.Repeated

open Econlib.GameTheory
open scoped BigOperators

/-! ## The stage Prisoner's Dilemma and its repeated calibrations (self-contained fixtures)

These mirror `EconlibExamples.GameTheory.GrimTriggerPD` but are defined here so the test
depends on no example. The stage game `pd` is the classical 2×2 PD (`T = 5`, `R = 3`, `P = 1`,
`S = 0`); `repeatedPD` is its `δ = 1/2`-discounted repetition (the cooperation threshold). -/

/-- **Cooperate**, encoded as `0 : Fin 2`. -/
abbrev cooperate : Fin 2 := 0

/-- **Defect**, encoded as `1 : Fin 2`. -/
abbrev defect : Fin 2 := 1

/-- The Prisoner's Dilemma stage game. Two players each pick an action in `Fin 2` (`0 = cooperate`,
`1 = defect`). Payoffs follow the classical PD ranking `T > R > P > S` with `T = 5`, `R = 3`,
`P = 1`, `S = 0`: `(C, C) ↦ 3`, `(D|C) ↦ 5`, `(C|D) ↦ 0`, `(D, D) ↦ 1`. Built via
`FiniteStrategicGame.mkFin` so the carriers `pd.Player` and `pd.Action i` reduce to `Fin 2`. -/
abbrev pd : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 2) fun i s =>
    if s i = cooperate then
      if s (1 - i) = cooperate then (3 : ℝ) else 0   -- R if both C, S if I'm the sucker
    else
      if s (1 - i) = cooperate then (5 : ℝ) else 1   -- T if I defect alone, P if both D

/-- The all-cooperate action profile `(C, C)`. -/
def cooperativeProfile : pd.ActionProfile := fun _ => cooperate

/-- The all-defect action profile `(D, D)`. -/
def defectionProfile : pd.ActionProfile := fun _ => defect

/-- The infinitely repeated Prisoner's Dilemma at the boundary discount `δ = 1/2`. -/
def repeatedPD : RepeatedGame where
  stage := pd
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-! ## Grim-trigger aliases backed by the library API

`grimTriggerPure` is the library per-history pure rule `RepeatedGame.grimTrigger`;
`grimTrigger` is its `pureStrategy` lift `RepeatedGame.grimTriggerStrategy`; `IsClean` is the
library cleanliness predicate. All three are specialized to the PD's cooperative / defection
profiles. -/

/-- The grim-trigger pure rule: Play cooperate on clean histories, defect after any deviation. The
library `RepeatedGame.grimTrigger` at the PD's cooperative / defection profiles. -/
abbrev grimTriggerPure : (i : Fin 2) → pd.PublicHistory → Fin 2 :=
  repeatedPD.grimTrigger cooperativeProfile defectionProfile

/-- **Grim trigger** as a public strategy: The library `grimTriggerStrategy` lift of
`grimTriggerPure`. By construction `grimTrigger = repeatedPD.pureStrategy grimTriggerPure`. -/
abbrev grimTrigger : repeatedPD.PublicStrategy :=
  repeatedPD.grimTriggerStrategy cooperativeProfile defectionProfile

/-- A public history is **clean** when every realized profile equals the cooperative profile — the
library `RepeatedGame.IsClean` at the cooperative profile. -/
abbrev IsClean (h : pd.PublicHistory) : Prop := repeatedPD.IsClean cooperativeProfile h

/-! ## Two off-threshold calibrations of the repeated Prisoner's Dilemma

Both share the example's stage game `pd`, so they share `toGameTree`, `toExtensiveForm`,
`PublicStrategy`, and the entire grim-trigger strategy construction definitionally. Only the
discount factor — hence the continuation-value geometric series and the equilibrium verdict —
differs. -/

/-- The **patient** repeated PD at `δ = 3/4 > 1/2`: Above the cooperation threshold. -/
private def repeatedPDpatient : RepeatedGame where
  stage := pd
  discount := 3 / 4
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The **impatient** repeated PD at `δ = 1/4 < 1/2`: Below the cooperation threshold. -/
private def repeatedPDimpatient : RepeatedGame where
  stage := pd
  discount := 1 / 4
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-! ## Grim-trigger period payoffs and continuation values at general discount

The period-`t` expected payoff `periodExpectedPayoff` is **independent of the discount factor**
(it never touches `R.discount`), so along the grim-trigger path it equals the constant stage payoff
(`3` on clean histories, `1` on dirty ones) at *every* discount. The continuation value then
collapses the normalized geometric series to that same constant — for *any* `δ < 1`.

The generic content lives in the library `Econlib.GameTheory.Repeated.GrimTrigger`; the local
helpers below are thin PD-specific bridges that (a) reuse the library lemmas at the cooperative /
defection profiles and (b) compute the resulting `pd.payoff i …` into the numeric literals `3`
(clean) and `1` (dirty) that the witnesses below assert. -/

/-- The grim-trigger pure rule prescribes the cooperative profile on clean histories — the library
`RepeatedGame.grimTriggerProfile_of_isClean` at the PD profiles. -/
private lemma grimTriggerProfile_of_isClean {h : pd.PublicHistory} (hclean : IsClean h) :
    (fun j => grimTriggerPure j h) = cooperativeProfile :=
  RepeatedGame.grimTriggerProfile_of_isClean (R := repeatedPD) (cooperate := cooperativeProfile)
    (punish := defectionProfile) hclean

/-- The grim-trigger pure rule prescribes the defection profile on dirty histories — the library
`RepeatedGame.grimTriggerProfile_of_not_isClean` at the PD profiles. -/
private lemma grimTriggerProfile_of_not_isClean {h : pd.PublicHistory} (hdirty : ¬ IsClean h) :
    (fun j => grimTriggerPure j h) = defectionProfile :=
  RepeatedGame.grimTriggerProfile_of_not_isClean (R := repeatedPD) (cooperate := cooperativeProfile)
    (punish := defectionProfile) hdirty

/-- Cleanliness is preserved by appending the cooperative profile —
`RepeatedGame.isClean_append`. -/
private lemma isClean_append_coop {h : pd.PublicHistory} (hclean : IsClean h) :
    IsClean (h ++ [cooperativeProfile]) :=
  RepeatedGame.isClean_append (R := repeatedPD) (cooperate := cooperativeProfile) hclean

/-- Dirtiness is absorbing — `RepeatedGame.not_isClean_append`. -/
private lemma not_isClean_append {h : pd.PublicHistory} (hdirty : ¬ IsClean h)
    (a : pd.ActionProfile) : ¬ IsClean (h ++ [a]) :=
  RepeatedGame.not_isClean_append (R := repeatedPD) (cooperate := cooperativeProfile) hdirty a

/-- The empty history is clean — `RepeatedGame.isClean_nil`. -/
private lemma isClean_nil : IsClean ([] : pd.PublicHistory) :=
  RepeatedGame.isClean_nil (R := repeatedPD) cooperativeProfile

/-- The cooperative stage payoff is `R = 3`, for either player. -/
private lemma payoff_cooperativeProfile (i : Fin 2) : pd.payoff i cooperativeProfile = 3 := by
  fin_cases i <;> simp [cooperativeProfile, cooperate]

/-- The defection stage payoff is `P = 1`, for either player. -/
private lemma payoff_defectionProfile (i : Fin 2) : pd.payoff i defectionProfile = 1 := by
  fin_cases i <;> simp [defectionProfile, defect, cooperate]

/-- Along the grim-trigger path from a clean history, every period's expected payoff is `R = 3` —
the library `periodExpectedPayoff_grimTriggerStrategy_of_isClean` with the cooperative payoff
computed to `3`. -/
private lemma periodExpectedPayoff_grimTrigger_of_isClean (i : Fin 2)
    (t : ℕ) (h : pd.PublicHistory) (hclean : IsClean h) :
    repeatedPD.periodExpectedPayoff grimTrigger h t i = 3 := by
  rw [repeatedPD.periodExpectedPayoff_grimTriggerStrategy_of_isClean cooperativeProfile
    defectionProfile i t h hclean]
  exact payoff_cooperativeProfile i

/-- Along the grim-trigger path from a dirty history, every period's expected payoff is `P = 1` —
the library `periodExpectedPayoff_grimTriggerStrategy_of_not_isClean` with the punishment payoff
computed to `1`. -/
private lemma periodExpectedPayoff_grimTrigger_of_not_isClean (i : Fin 2)
    (t : ℕ) (h : pd.PublicHistory) (hdirty : ¬ IsClean h) :
    repeatedPD.periodExpectedPayoff grimTrigger h t i = 1 := by
  rw [repeatedPD.periodExpectedPayoff_grimTriggerStrategy_of_not_isClean cooperativeProfile
    defectionProfile i t h hdirty]
  exact payoff_defectionProfile i

/-! ### Grim-trigger continuation values at the three calibrations

The period payoffs transfer by `rfl` (discount-independent); the normalized geometric series
then yields `3` on clean histories and `1` on dirty ones, at every discount. The
`continuationValue_eq_step` witness (item 3) is the one-step Bellman recursion `V = (1-δ)·c + δ·V`
on the constant cooperation path, with fixed point `c = 3`. -/

/-- **`continuationValue_eq_step` on the cooperation path (item 3 anchor).** On a clean history the
one-step Bellman recursion holds with `V = 3`: `3 = (1-δ)·3 + δ·3`. Exercised at `δ = 3/4`. -/
theorem continuationValue_step_cooperation :
    repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2)
      = (1 - repeatedPDpatient.discount) * repeatedPDpatient.stagePayoff grimTrigger [] (0 : Fin 2)
        + repeatedPDpatient.discount * ∑ c : pd.ActionProfile,
            repeatedPDpatient.stageProfileProb grimTrigger [] c
              * repeatedPDpatient.continuationValue grimTrigger ([] ++ [c]) (0 : Fin 2) :=
  repeatedPDpatient.continuationValue_eq_step grimTrigger [] (0 : Fin 2)

/-- Grim-trigger continuation value on the patient (`δ = 3/4`) clean path is `3`. -/
theorem continuationValue_grimTrigger_patient_clean (h : pd.PublicHistory) (hclean : IsClean h)
    (i : Fin 2) : repeatedPDpatient.continuationValue grimTrigger h i = 3 :=
  (repeatedPDpatient.continuationValue_grimTriggerStrategy_of_isClean h hclean i).trans
    (payoff_cooperativeProfile i)

/-- Grim-trigger continuation value on the impatient (`δ = 1/4`) clean path is also `3`
(discount-independent on the constant path). -/
theorem continuationValue_grimTrigger_impatient_clean (h : pd.PublicHistory) (hclean : IsClean h)
    (i : Fin 2) : repeatedPDimpatient.continuationValue grimTrigger h i = 3 :=
  (repeatedPDimpatient.continuationValue_grimTriggerStrategy_of_isClean h hclean i).trans
    (payoff_cooperativeProfile i)

/-- Grim-trigger continuation value on a dirty history is `1`, at the **patient** (`δ = 3/4`)
calibration. The companion `..._impatient_dirty` and `..._boundary_dirty` discharge the other two
calibrations, so the "at every calibration" claim is witnessed in full. -/
theorem continuationValue_grimTrigger_patient_dirty (h : pd.PublicHistory) (hdirty : ¬ IsClean h)
    (i : Fin 2) : repeatedPDpatient.continuationValue grimTrigger h i = 1 :=
  (repeatedPDpatient.continuationValue_grimTriggerStrategy_of_not_isClean h hdirty i).trans
    (payoff_defectionProfile i)

/-- Grim-trigger continuation value on a dirty history is `1` at the **impatient** (`δ = 1/4`)
calibration (punishment is absorbing, the value is discount-independent on the constant path). -/
theorem continuationValue_grimTrigger_impatient_dirty (h : pd.PublicHistory) (hdirty : ¬ IsClean h)
    (i : Fin 2) : repeatedPDimpatient.continuationValue grimTrigger h i = 1 :=
  (repeatedPDimpatient.continuationValue_grimTriggerStrategy_of_not_isClean h hdirty i).trans
    (payoff_defectionProfile i)

/-- Grim-trigger continuation value on a dirty history is `1` at the **boundary** (`δ = 1/2`)
calibration. -/
theorem continuationValue_grimTrigger_boundary_dirty (h : pd.PublicHistory) (hdirty : ¬ IsClean h)
    (i : Fin 2) : repeatedPD.continuationValue grimTrigger h i = 1 :=
  (repeatedPD.continuationValue_grimTriggerStrategy_of_not_isClean h hdirty i).trans
    (payoff_defectionProfile i)

/-- Grim-trigger continuation value on a clean history is `3` at the **boundary** (`δ = 1/2`)
calibration — the cooperative payoff. -/
theorem continuationValue_grimTrigger_boundary_clean (h : pd.PublicHistory) (hclean : IsClean h)
    (i : Fin 2) : repeatedPD.continuationValue grimTrigger h i = 3 :=
  (repeatedPD.continuationValue_grimTriggerStrategy_of_isClean h hclean i).trans
    (payoff_cooperativeProfile i)

/-! ## Folk-theorem ingredients on the stage Prisoner's Dilemma

The minmax of the PD is the mutual-defection payoff `1`. The cooperative payoff vector `(3, 3)`
is feasible (generated by `(C, C)`) and *strictly* individually rational (`1 < 3`), the
folk-theorem target. We verify `MinmaxValue = 1` exactly, which forces the IR / full-dimensionality
witnesses to the correct *above-minmax* side. -/

/-- The cooperative payoff vector `(3, 3)` for the stage PD. -/
private def coopPayoff : repeatedPDpatient.PayoffVector := fun _ => 3

/-- A one-step lower bound: Defecting against any opponent profile pays at least the punishment
`P = 1`. -/
private lemma payoff_update_defect_ge (i : Fin 2) (a : pd.ActionProfile) :
    (1 : ℝ) ≤ pd.payoff i (Function.update a i defect) := by
  by_cases hop : a (1 - i) = cooperate <;> fin_cases i <;>
    simp_all [pd, FiniteStrategicGame.mkFin, Function.update, cooperate, defect]

/-- Against a defecting opponent, no own action pays more than the punishment `P = 1`. -/
private lemma payoff_update_defectProfile_le (i aᵢ : Fin 2) :
    pd.payoff i (Function.update defectionProfile i aᵢ) ≤ 1 := by
  fin_cases i <;> fin_cases aᵢ <;>
    simp [pd, FiniteStrategicGame.mkFin, Function.update, defectionProfile, defect, cooperate]

/-- **The PD minmax is the mutual-defection payoff `1`.** The opponent holds player `i` to `1` by
defecting (then `i`'s best response, defect, earns `P = 1`); no opponent profile can hold `i` below
`1` since defecting always secures at least `P = 1`. This is the *correct* benchmark: The
cooperative payoff `3` sits strictly above it. -/
theorem minmaxValue_eq_one (i : Fin 2) : repeatedPDpatient.MinmaxValue i = 1 := by
  unfold RepeatedGame.MinmaxValue
  apply le_antisymm
  · -- Opponent defects (`a = defectionProfile`): the best the deviator can do is `1`.
    refine (Finset.inf'_le _ (Finset.mem_univ defectionProfile)).trans ?_
    exact Finset.sup'_le _ _ (fun aᵢ _ => payoff_update_defectProfile_le i aᵢ)
  · -- For every opponent profile, defecting secures at least `1`, so the inner sup is at least `1`.
    refine Finset.le_inf' _ _ (fun a _ => ?_)
    exact le_trans (payoff_update_defect_ge i a)
      (Finset.le_sup' (fun aᵢ => pd.payoff i (Function.update a i aᵢ)) (Finset.mem_univ defect))

/-- **The cooperative payoff is feasible.** `(3, 3)` is generated by the pure profile `(C, C)`. -/
theorem coopPayoff_isFeasible :
    repeatedPDpatient.IsFeasiblePayoffSet {coopPayoff} := by
  rintro w (rfl : w = coopPayoff)
  refine ⟨cooperativeProfile, fun i => ?_⟩
  change (3 : ℝ) = pd.payoff i cooperativeProfile
  fin_cases i <;> simp [cooperativeProfile, cooperate]

/-- **The cooperative payoff is (weakly) individually rational.** `IsIndividuallyRationalPayoffSet`
is the *weak* benchmark `MinmaxValue i ≤ w i`; here `MinmaxValue i = 1 ≤ 3 = w i`, clearing the
minmax in the correct *above-minmax* direction. A reversed IR inequality (`w i ≤ MinmaxValue i`)
would demand `3 ≤ 1`, which fails. The companion `coopPayoff_strictly_above_minmax` upgrades this
to the *strict* anchor `1 < 3`. -/
theorem coopPayoff_isIndividuallyRational :
    repeatedPDpatient.IsIndividuallyRationalPayoffSet {coopPayoff} := by
  rintro w (rfl : w = coopPayoff) i
  rw [minmaxValue_eq_one i]
  norm_num [coopPayoff]

/-- **The cooperative payoff is *strictly* individually rational.** The strict anchor the predicate
`IsIndividuallyRationalPayoffSet` (which only gives `≤`) does not state on its own:
`MinmaxValue i = 1 < 3 = coopPayoff i` for every player. -/
theorem coopPayoff_strictly_above_minmax (i : Fin 2) :
    repeatedPDpatient.MinmaxValue i < coopPayoff i := by
  rw [minmaxValue_eq_one i]
  norm_num [coopPayoff]

/-- **Strict full-dimensionality witness.** The cooperative payoff strictly clears every minmax
bound (`1 < 3`), so it is a valid full-dimensional folk-theorem target for the 2-player PD. -/
theorem coopPayoff_hasFullDimensionalWitness :
    repeatedPDpatient.HasFullDimensionalPayoffWitness {coopPayoff} :=
  ⟨coopPayoff, rfl, fun i => by rw [minmaxValue_eq_one i]; norm_num [coopPayoff]⟩

/-- **The cooperative singleton is self-generating** at the patient discount — the *constant
fixed-point* case. The grim-trigger SPE payoff `(3, 3)` decomposes as "play `(C, C)` now, continue
with `(3, 3)`": `3 = (1-δ)·3 + δ·3`, with the continuation vector again in the set. Here the
current stage payoff (`3`) *equals* the continuation payoff (`3`), so this decomposition is
insensitive to swapping the current / continuation weights; the companion
`twoPointSet_isSelfGenerating` exhibits a genuine *non-constant* decomposition (current `3` ≠
continuation `1`) that is not. -/
theorem coopPayoff_isSelfGenerating :
    repeatedPDpatient.IsSelfGenerating {coopPayoff} := by
  rintro w (rfl : w = coopPayoff)
  refine ⟨cooperativeProfile, coopPayoff, rfl, fun i => ?_⟩
  have hpay : pd.payoff i cooperativeProfile = 3 := by
    fin_cases i <;> simp [cooperativeProfile, cooperate]
  have hδ : repeatedPDpatient.discount = 3 / 4 := rfl
  change (coopPayoff i) = (1 - repeatedPDpatient.discount) * pd.payoff i cooperativeProfile
    + repeatedPDpatient.discount * coopPayoff i
  rw [hpay, hδ]
  norm_num [coopPayoff]

/-- The mutual-defection (punishment) payoff vector `(1, 1)`. -/
private def punishPayoff : repeatedPDpatient.PayoffVector := fun _ => 1

/-- The "cooperate once, then punish forever" payoff vector `(3/2, 3/2)`. At `δ = 3/4` this is
`(1-δ)·3 + δ·1 = (1/4)·3 + (3/4)·1 = 3/2`: One cooperative stage (payoff `3`) followed by the
absorbing punishment continuation (`1`). The current stage payoff `3` differs from the continuation
`1`, so its self-generating decomposition is genuinely non-constant. -/
private def coopOnceThenPunish : repeatedPDpatient.PayoffVector := fun _ => 3 / 2

/-- **A genuinely non-constant self-generating witness** at the patient discount. The two-point set
`{(3/2, 3/2), (1, 1)}` is self-generating with a decomposition in which the current stage payoff
differs from the continuation:

* `(3/2, 3/2)` decomposes as "play `(C, C)` now (payoff `3`), continue at the punishment `(1, 1)`":
  `3/2 = (1-δ)·3 + δ·1` with current payoff `3 ≠ 1 = ` continuation — the non-constant case.
* `(1, 1)` decomposes as "play `(D, D)` now (payoff `1`), continue at `(1, 1)`": The absorbing
  fixed point. Both continuation vectors lie back in the set. Unlike `coopPayoff_isSelfGenerating`,
  swapping the current and continuation weights would change the first decomposition's value, so
  this witness actually stresses the recursive structure of `IsSelfGenerating`. -/
theorem twoPointSet_isSelfGenerating :
    repeatedPDpatient.IsSelfGenerating {coopOnceThenPunish, punishPayoff} := by
  have hδ : repeatedPDpatient.discount = 3 / 4 := rfl
  have hpay_coop : ∀ i : Fin 2, pd.payoff i cooperativeProfile = 3 := by
    intro i; fin_cases i <;> simp [cooperativeProfile, cooperate]
  have hpay_defect : ∀ i : Fin 2, pd.payoff i defectionProfile = 1 := by
    intro i; fin_cases i <;> simp [defectionProfile, defect, cooperate]
  rintro w (rfl | rfl)
  · -- `(3/2, 3/2)`: cooperate once (payoff `3`), continue at punishment `(1, 1)` — current ≠ cont.
    refine ⟨cooperativeProfile, punishPayoff, Or.inr rfl, fun i => ?_⟩
    change (coopOnceThenPunish i)
      = (1 - repeatedPDpatient.discount) * pd.payoff i cooperativeProfile
        + repeatedPDpatient.discount * punishPayoff i
    rw [hpay_coop i, hδ]
    norm_num [coopOnceThenPunish, punishPayoff]
  · -- `(1, 1)`: defect forever (payoff `1`), continue at `(1, 1)` — absorbing fixed point.
    refine ⟨defectionProfile, punishPayoff, Or.inr rfl, fun i => ?_⟩
    change (punishPayoff i) = (1 - repeatedPDpatient.discount) * pd.payoff i defectionProfile
      + repeatedPDpatient.discount * punishPayoff i
    rw [hpay_defect i, hδ]
    norm_num [punishPayoff]

/-- **Sufficient patience is non-vacuous and direction-correct.** The patient discount `δ = 3/4`
clears any threshold `δ₀ ≤ 3/4` with `δ₀ < 1` — here the cooperation threshold `δ₀ = 1/2`. The
predicate is `δ₀ ≤ R.discount` (threshold *below* the discount), the correct direction. -/
theorem isSufficientlyPatient_patient :
    repeatedPDpatient.IsSufficientlyPatient (1 / 2) := by
  refine ⟨by norm_num, ?_⟩
  show (1 / 2 : ℝ) ≤ repeatedPDpatient.discount
  norm_num [repeatedPDpatient]

/-- **The impatient discount fails the cooperation threshold.** `δ = 1/4 < 1/2`, so
`IsSufficientlyPatient (1/2)` is *false* for the impatient game — the high-value direction witness
that the threshold comparison is `δ₀ ≤ δ`, not `δ ≤ δ₀`. -/
theorem not_isSufficientlyPatient_impatient :
    ¬ repeatedPDimpatient.IsSufficientlyPatient (1 / 2) := by
  rintro ⟨_, hle⟩
  have : (1 / 2 : ℝ) ≤ 1 / 4 := hle
  norm_num at this

/-! ## The one-shot defection deviation and the impatient failure (the high-value witness)

We build the genuine one-shot deviation: Player `0` defects once at the empty (clean) history,
then reverts to grim trigger. This is an `IsInfoSetDeviation` of `grimTrigger` at `(0, [])`. At the
impatient discount `δ = 1/4` its continuation value is `(1-δ)·T + δ·P = 5 - 4δ = 4 > 3`, so it is
*strictly profitable*: `NoProfitableOneShotDeviation grimTrigger` is false, hence (by the one-shot
deviation principle) grim trigger is *not* an SPE. This is exactly the discount-bound endpoint flip
the threshold guards against.

The pure-rule lift `pureStrategy`, its vertex accessor `pureStrategy_heq_vertex`, and the
agree-implies-equal bridge `pureStrategy_eq_at` are the library `RepeatedGame.pureStrategy`,
`pureStrategy_apply_heq_vertex` and `pureStrategy_apply_eq_of_apply_eq` at `repeatedPD`; we alias
them locally so the concrete deviation proofs read against the PD names. -/

/-- The perfect-info public-strategy lift of a per-history pure rule — `repeatedPD.pureStrategy`.
`grimTrigger` is the instance `pureStrategy grimTriggerPure` (definitionally). -/
private abbrev pureStrategy (rule : (i : Fin 2) → pd.PublicHistory → Fin 2) :
    repeatedPD.PublicStrategy :=
  repeatedPD.pureStrategy rule

/-- The raw lifted strategy value at `(j, obs)` is heterogeneously equal to the prescribed vertex —
`repeatedPD.pureStrategy_apply_heq_vertex`. -/
private lemma pureStrategy_heq_vertex (rule : (i : Fin 2) → pd.PublicHistory → Fin 2)
    (j : Fin 2) (obs : pd.PublicHistory) :
    HEq (pureStrategy rule j obs) (stdSimplex.vertex (S := ℝ) (rule j obs)) :=
  repeatedPD.pureStrategy_apply_heq_vertex rule j obs

/-- `grimTrigger` is the `pureStrategy` lift of `grimTriggerPure` (definitional). -/
private lemma grimTrigger_eq : grimTrigger = pureStrategy grimTriggerPure := rfl

/-- Two pure rules agreeing at player `j`'s action at `obs` lift to equal raw strategy values —
`repeatedPD.pureStrategy_apply_eq_of_apply_eq`. -/
private lemma pureStrategy_eq_at (rule₁ rule₂ : (i : Fin 2) → pd.PublicHistory → Fin 2)
    (j : Fin 2) (obs : pd.PublicHistory) (hagree : rule₁ j obs = rule₂ j obs) :
    pureStrategy rule₁ j obs = pureStrategy rule₂ j obs :=
  repeatedPD.pureStrategy_apply_eq_of_apply_eq rule₁ rule₂ j obs hagree

/-- The one-shot defection rule: Player `0` defects at the empty history, grim trigger elsewhere. -/
private def devPure (i : Fin 2) (h : pd.PublicHistory) : Fin 2 :=
  if i = 0 ∧ h = [] then defect else grimTriggerPure i h

/-- The one-shot defection deviation strategy. -/
private def devDefect : repeatedPD.PublicStrategy := pureStrategy devPure

/-- The realized profile at `[]` under the deviation: Player `0` defects, player `1` cooperates
(the empty history is clean). -/
private def DC : pd.ActionProfile := fun j => if j = 0 then defect else cooperate

/-- The deviation prescribes profile `(D, C)` at the empty history. -/
private lemma devPure_at_nil : (fun j : pd.Player => devPure j []) = DC := by
  funext j
  unfold devPure DC
  by_cases hj : j = 0
  · simp [hj, defect]
  · rw [if_neg (fun h => hj h.1), if_neg hj]
    -- The empty history is clean, so grim trigger prescribes the cooperative action `cooperate`.
    exact RepeatedGame.grimTrigger_of_isClean (punish := defectionProfile) isClean_nil j

/-- `(D, C)` is not the cooperative profile, so `[(D, C)]` is dirty. -/
private lemma DC_ne_coop : DC ≠ cooperativeProfile := by
  intro h
  have := congrFun h 0
  unfold DC cooperativeProfile at this
  simp [defect, cooperate] at this

/-- The post-deviation history `[(D, C)]` is dirty. -/
private lemma not_isClean_DC : ¬ IsClean [DC] :=
  fun hc => DC_ne_coop (hc DC (List.mem_singleton.mpr rfl))

/-- The deviator's stage payoff at `(D, C)` is the temptation `T = 5`. -/
private lemma payoff_DC : pd.payoff (0 : Fin 2) DC = 5 := by
  unfold DC; simp [pd, FiniteStrategicGame.mkFin, defect, cooperate]

/-- **The deviation is a genuine one-shot info-set deviation** of grim trigger at `(0, [])`: It
agrees with grim trigger at every other `(player, observation)` coordinate. -/
theorem devDefect_isInfoSetDeviation :
    IsInfoSetDeviation repeatedPD.toExtensiveForm (0 : Fin 2) ([] : pd.PublicHistory)
      grimTrigger devDefect := by
  intro j obs hne
  change pureStrategy devPure j obs = grimTrigger j obs
  rw [grimTrigger_eq]
  refine pureStrategy_eq_at devPure grimTriggerPure j obs ?_
  unfold devPure
  split
  · rename_i hcond
    obtain ⟨hj0, hobs⟩ := hcond
    exact absurd (Sigma.ext hj0 (hobs ▸ HEq.refl _)) hne
  · rfl

/-- **Stage-profile mass of the deviation at the empty history: The `(D, C)` indicator.** The
deviation prescribes `(D, C)` deterministically, so the product of vertex marginals concentrates on
`DC` (the player-binder coincides through `devPure_at_nil`). Discount-independent — stated on
`repeatedPD`, transferred to the other calibrations by definitional equality. -/
private lemma stageProfileProb_devDefect_nil (a : pd.ActionProfile) :
    repeatedPD.stageProfileProb devDefect [] a = if a = DC then (1 : ℝ) else 0 := by
  classical
  unfold RepeatedGame.stageProfileProb
  have hfactor : ∀ j : pd.Player,
      (repeatedPD.atHistory devDefect j []) (a j)
        = if a j = devPure j [] then (1 : ℝ) else 0 := by
    intro j
    rw [show repeatedPD.atHistory devDefect j [] = stdSimplex.vertex (devPure j []) from
      eq_of_heq ((simplexTransport_heq _ _).trans (pureStrategy_heq_vertex devPure j []))]
    by_cases hj : a j = devPure j []
    · rw [if_pos hj]; exact stdSimplex.vertex_apply_eq hj.symm
    · rw [if_neg hj]; exact stdSimplex.vertex_apply_ne (fun heq => hj heq.symm)
  simp only [hfactor]
  by_cases ha : a = DC
  · rw [if_pos ha]
    exact Finset.prod_eq_one (fun j _ => by
      rw [if_pos (by rw [ha]; exact congrFun devPure_at_nil.symm j)])
  · rw [if_neg ha]
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ devPure j [] := by
      by_contra hcon; push Not at hcon
      exact ha (devPure_at_nil ▸ funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])

/-- The deviator's stage payoff at the empty history is the temptation `T = 5` (deterministic
`(D, C)`). Discount-independent. -/
private lemma stagePayoff_devDefect_nil :
    repeatedPD.stagePayoff devDefect [] (0 : Fin 2) = 5 := by
  rw [RepeatedGame.stagePayoff_eq_sum_stageProfileProb]
  simp only [stageProfileProb_devDefect_nil, ite_mul, one_mul, zero_mul]
  refine (Finset.sum_eq_single_of_mem DC (Finset.mem_univ _) (fun b _ hb => if_neg hb)).trans ?_
  rw [if_pos rfl]
  change pd.payoff (0 : Fin 2) DC = 5
  exact payoff_DC

/-- Beyond the empty history the deviation coincides with grim trigger (it only acts at `(0, [])`),
so its continuation value from `[(D, C)]` is the grim-trigger dirty value `1`. -/
private lemma devDefect_agree_ext (j : pd.Player) (suffix : pd.PublicHistory) :
    devDefect j ([DC] ++ suffix) = grimTrigger j ([DC] ++ suffix) := by
  change pureStrategy devPure j ([DC] ++ suffix) = grimTrigger j ([DC] ++ suffix)
  rw [grimTrigger_eq]
  refine pureStrategy_eq_at devPure grimTriggerPure j _ ?_
  unfold devPure
  rw [if_neg]
  rintro ⟨_, hnil⟩
  exact absurd hnil (by simp)

/-- The deviation's continuation value from `[(D, C)]` is the grim-trigger dirty value `1`, at the
impatient calibration (the post-deviation path follows grim trigger forever). -/
private lemma cv_devDefect_DC_impatient :
    repeatedPDimpatient.continuationValue devDefect [DC] (0 : Fin 2) = 1 := by
  refine repeatedPDimpatient.continuationValue_of_const (σ := devDefect) (h := [DC]) (0 : Fin 2) 1
    (fun t => ?_)
  rw [repeatedPDimpatient.periodExpectedPayoff_congr [DC] t (0 : Fin 2)
    (fun j suffix _ => devDefect_agree_ext j suffix)]
  exact periodExpectedPayoff_grimTrigger_of_not_isClean (0 : Fin 2) t [DC] not_isClean_DC

/-- The deviation's continuation value from `[(D, C)]` is `1` at the boundary calibration. -/
private lemma cv_devDefect_DC_boundary :
    repeatedPD.continuationValue devDefect [DC] (0 : Fin 2) = 1 := by
  refine repeatedPD.continuationValue_of_const (σ := devDefect) (h := [DC]) (0 : Fin 2) 1
    (fun t => ?_)
  rw [repeatedPD.periodExpectedPayoff_congr [DC] t (0 : Fin 2)
    (fun j suffix _ => devDefect_agree_ext j suffix)]
  exact periodExpectedPayoff_grimTrigger_of_not_isClean (0 : Fin 2) t [DC] not_isClean_DC

/-- **The deviation value at the impatient discount is `4`.** `(1-δ)·5 + δ·1 = 5 - 4·(1/4) = 4`,
strictly exceeding the cooperation value `3`. -/
theorem cv_devDefect_nil_eq_four :
    repeatedPDimpatient.continuationValue devDefect [] (0 : Fin 2) = 4 := by
  rw [repeatedPDimpatient.continuationValue_eq_step devDefect [] (0 : Fin 2)]
  -- `stagePayoff` and `stageProfileProb` are discount-free, so the `repeatedPD` helpers apply.
  have hsp : repeatedPDimpatient.stagePayoff devDefect [] (0 : Fin 2) = 5 :=
    stagePayoff_devDefect_nil
  rw [hsp]
  have hoff : ∀ b : pd.ActionProfile, b ≠ DC →
      repeatedPDimpatient.stageProfileProb devDefect [] b
        * repeatedPDimpatient.continuationValue devDefect ([] ++ [b]) (0 : Fin 2) = 0 := by
    intro b hb
    have hb0 : repeatedPDimpatient.stageProfileProb devDefect [] b
        = if b = DC then (1 : ℝ) else 0 := stageProfileProb_devDefect_nil b
    rw [hb0, if_neg hb, zero_mul]
  have hon : repeatedPDimpatient.stageProfileProb devDefect [] DC
      * repeatedPDimpatient.continuationValue devDefect ([] ++ [DC]) (0 : Fin 2) = 1 := by
    have hDC : repeatedPDimpatient.stageProfileProb devDefect [] DC
        = if DC = DC then (1 : ℝ) else 0 := stageProfileProb_devDefect_nil DC
    rw [hDC, if_pos rfl, one_mul]
    exact cv_devDefect_DC_impatient
  have hsum : (∑ c : repeatedPDimpatient.stage.ActionProfile,
      repeatedPDimpatient.stageProfileProb devDefect [] c
        * repeatedPDimpatient.continuationValue devDefect ([] ++ [c]) (0 : Fin 2)) = 1 :=
    (Finset.sum_eq_single_of_mem DC (Finset.mem_univ DC) (fun b _ hb => hoff b hb)).trans hon
  rw [hsum]
  have hδ : repeatedPDimpatient.discount = 1 / 4 := rfl
  rw [hδ]; norm_num

/-- Grim trigger's continuation value at the empty history (impatient game) is the cooperation
value `3`. -/
theorem cv_grimTrigger_nil_impatient :
    repeatedPDimpatient.continuationValue grimTrigger [] (0 : Fin 2) = 3 :=
  continuationValue_grimTrigger_impatient_clean [] isClean_nil 0

/-- **A profitable one-shot deviation exists at the impatient discount:** `4 > 3`. -/
theorem devDefect_profitable :
    repeatedPDimpatient.continuationValue grimTrigger [] (0 : Fin 2)
      < repeatedPDimpatient.continuationValue devDefect [] (0 : Fin 2) := by
  rw [cv_grimTrigger_nil_impatient, cv_devDefect_nil_eq_four]; norm_num

/-- **No-profitable-one-shot-deviation FAILS for grim trigger at `δ = 1/4`.** The one-shot
defection strictly raises the deviator's continuation value, so the unimprovability condition is
false. -/
theorem not_noProfitableOneShotDeviation_impatient :
    ¬ repeatedPDimpatient.NoProfitableOneShotDeviation grimTrigger := by
  intro hOS
  have hle := hOS (0 : Fin 2) [] devDefect devDefect_isInfoSetDeviation
  exact absurd hle (not_le.mpr devDefect_profitable)

/-- **Grim trigger is NOT a subgame-perfect equilibrium at the impatient discount `δ = 1/4`.** Via
the one-shot deviation principle, the existence of a profitable one-shot deviation rules out
subgame perfection. This is the negative side of the threshold: Cooperation collapses below
`δ = 1/2`. -/
theorem grimTrigger_not_SPE_impatient :
    ¬ repeatedPDimpatient.IsSubgamePerfectEquilibrium grimTrigger := by
  rw [RepeatedGame.IsSubgamePerfectEquilibrium_iff_noProfitableOneShotDeviation]
  exact not_noProfitableOneShotDeviation_impatient

/-! ## The positive side of the threshold and the one-shot deviation principle

At the boundary `δ = 1/2` grim trigger is an SPE (`grimTrigger_SPE_boundary`, via the library
one-shot deviation theorem). We instantiate the one-shot deviation principle on the concrete
profile, confirming the *no-profitable-deviation* side is non-vacuous: A defect deviation genuinely
exists and is ruled out. The contrast `SPE at δ = 1/2` / `not SPE at δ = 1/4` is the both-sides
threshold check. -/

/-- **The one-period calibration inequality at `δ = 1/2`.** For every player `i` and deviation
action `aᵢ`, the one-shot deviation payoff `(1 - δ)·payoff i (deviate to aᵢ) + δ·payoff i (D, D)`
does not exceed the cooperative payoff `payoff i (C, C)`. The boundary case (deviate to defect)
hits `(1/2)·5 + (1/2)·1 = 3`, exactly the cooperative payoff. -/
private lemma grimTrigger_calibrated (i : Fin 2) (aᵢ : Fin 2) :
    (1 - repeatedPD.discount) * pd.payoff i (Function.update cooperativeProfile i aᵢ)
      + repeatedPD.discount * pd.payoff i defectionProfile ≤ pd.payoff i cooperativeProfile := by
  have hδ : repeatedPD.discount = (1 / 2 : ℝ) := rfl
  rw [hδ]
  fin_cases i <;> fin_cases aᵢ <;>
    norm_num [pd, FiniteStrategicGame.mkFin, Function.update, cooperativeProfile, defectionProfile,
      cooperate, defect]

/-- **Mutual defection is a pure Nash equilibrium of the stage game** (the absorbing punishment). -/
private lemma pd_defectionProfile_is_nash : pd.IsNash defectionProfile := by
  rw [StrategicGame.isNash_iff]
  intro i aᵢ
  fin_cases i <;> fin_cases aᵢ <;>
    simp [pd, defectionProfile, Function.update_self, cooperate, defect]

/-- **Grim trigger is an SPE at the boundary discount `δ = 1/2`.** The library
`grimTrigger_isSubgamePerfectEquilibrium` upgrades the stage-Nash punishment
(`pd_defectionProfile_is_nash`) and the one-period calibration (`grimTrigger_calibrated`) to full
subgame perfection. At the threshold the one-shot defection is exactly indifferent, so cooperation
is sustained. -/
theorem grimTrigger_SPE_boundary :
    repeatedPD.IsSubgamePerfectEquilibrium grimTrigger :=
  repeatedPD.grimTrigger_isSubgamePerfectEquilibrium pd_defectionProfile_is_nash
    grimTrigger_calibrated

/-- **`IsSubgamePerfectEquilibrium_iff` (forward `.mp` direction).** Repeated-game subgame
perfection transports to the extensive-game predicate on the perfect-information lift; here we push
the boundary grim-trigger SPE *forward* through the iff. (Only the `.mp` direction is exercised —
this is the transport, not a both-sides claim.) -/
theorem grimTrigger_SPE_extensiveGame_boundary :
    repeatedPD.toExtensiveGame.IsSubgamePerfectEquilibrium grimTrigger :=
  (RepeatedGame.IsSubgamePerfectEquilibrium_iff repeatedPD grimTrigger).mp grimTrigger_SPE_boundary

/-- **The one-shot deviation principle, instantiated on grim trigger at the boundary discount.**
This is the *library iff itself* specialized to `(repeatedPD, grimTrigger)` — a declaration-level
restatement, not yet a non-vacuity check of either direction. The forward (`.mp`) direction is
exercised by `noProfitableOneShotDeviation_boundary` and the substantive backward (`.mpr`)
direction by `grimTrigger_SPE_from_noDeviation_boundary`. -/
theorem oneShotDeviationPrinciple_boundary :
    repeatedPD.IsSubgamePerfectEquilibrium grimTrigger
      ↔ repeatedPD.NoProfitableOneShotDeviation grimTrigger :=
  RepeatedGame.IsSubgamePerfectEquilibrium_iff_noProfitableOneShotDeviation repeatedPD grimTrigger

/-- **The no-profitable-deviation side is non-vacuous at the boundary** (forward `.mp` direction).
Grim trigger admits no profitable one-shot deviation at `δ = 1/2` — derived from the SPE via the
principle. In particular the defect deviation `devDefect` (which is profitable at `δ = 1/4`) is
here *unprofitable*: At the threshold the deviation is exactly indifferent. -/
theorem noProfitableOneShotDeviation_boundary :
    repeatedPD.NoProfitableOneShotDeviation grimTrigger :=
  (oneShotDeviationPrinciple_boundary.mp grimTrigger_SPE_boundary)

/-- **The substantive `.mpr` direction of the one-shot deviation principle at the boundary.** Going
*back* from `NoProfitableOneShotDeviation` to subgame perfection — the nontrivial half of the
principle (the forward half is just "deviations are unilateral"). Feeding the boundary
no-profitable-deviation witness through `.mpr` recovers the SPE, so the equivalence is non-vacuous
in the backward direction too, not only restated. -/
theorem grimTrigger_SPE_from_noDeviation_boundary :
    repeatedPD.IsSubgamePerfectEquilibrium grimTrigger :=
  oneShotDeviationPrinciple_boundary.mpr noProfitableOneShotDeviation_boundary

/-- **The boundary deviation value is exactly `3`.** `(1-δ)·5 + δ·1 = (1/2)·5 + (1/2)·1 = 3` at
`δ = 1/2`: The temptation gain is *exactly* canceled by discounted punishment. This is the
knife-edge the threshold sits on (`5 - 4δ = 3 ⟺ δ = 1/2`). -/
theorem cv_devDefect_nil_eq_three_boundary :
    repeatedPD.continuationValue devDefect [] (0 : Fin 2) = 3 := by
  rw [repeatedPD.continuationValue_eq_step devDefect [] (0 : Fin 2)]
  rw [show repeatedPD.stagePayoff devDefect [] (0 : Fin 2) = 5 from stagePayoff_devDefect_nil]
  have hoff : ∀ b : pd.ActionProfile, b ≠ DC →
      repeatedPD.stageProfileProb devDefect [] b
        * repeatedPD.continuationValue devDefect ([] ++ [b]) (0 : Fin 2) = 0 := by
    intro b hb
    rw [stageProfileProb_devDefect_nil b, if_neg hb, zero_mul]
  have hon : repeatedPD.stageProfileProb devDefect [] DC
      * repeatedPD.continuationValue devDefect ([] ++ [DC]) (0 : Fin 2) = 1 := by
    rw [stageProfileProb_devDefect_nil DC, if_pos rfl, one_mul]
    exact cv_devDefect_DC_boundary
  have hsum : (∑ c : repeatedPD.stage.ActionProfile,
      repeatedPD.stageProfileProb devDefect [] c
        * repeatedPD.continuationValue devDefect ([] ++ [c]) (0 : Fin 2)) = 1 :=
    (Finset.sum_eq_single_of_mem DC (Finset.mem_univ DC) (fun b _ hb => hoff b hb)).trans hon
  rw [hsum]
  have hδ : repeatedPD.discount = 1 / 2 := rfl
  rw [hδ]; norm_num

/-- **The boundary deviation is exactly indifferent.** At `δ = 1/2` the defect deviation earns
exactly `3 = cv grimTrigger [] 0` — neither strictly better nor worse. The deviation gain is fully
offset by discounted punishment, the knife-edge the threshold sits on. (The weak inequality
`≤ cv grimTrigger` is what `NoProfitableOneShotDeviation` gives; the equality below pins the
indifference.) -/
theorem devDefect_indifferent_boundary :
    repeatedPD.continuationValue devDefect [] (0 : Fin 2)
      = repeatedPD.continuationValue grimTrigger [] (0 : Fin 2) := by
  rw [cv_devDefect_nil_eq_three_boundary]
  -- Grim trigger's clean-path value at the boundary is the cooperative payoff `3`.
  exact (continuationValue_grimTrigger_boundary_clean [] isClean_nil 0).symm

/-- The boundary deviation is (weakly) unprofitable — the `NoProfitableOneShotDeviation` form,
equal to `cv grimTrigger` by `devDefect_indifferent_boundary`. -/
theorem devDefect_unprofitable_boundary :
    repeatedPD.continuationValue devDefect [] (0 : Fin 2)
      ≤ repeatedPD.continuationValue grimTrigger [] (0 : Fin 2) :=
  noProfitableOneShotDeviation_boundary (0 : Fin 2) [] devDefect devDefect_isInfoSetDeviation

/-! ## Continuation-value bounds and the discounting stack (item 3)

These exercise the uniform-bound / summability machinery on the concrete grim-trigger
continuation values. `payoffBound` is nonnegative; period payoffs and continuation values are
bounded by it; and `summable_discount_periodExpectedPayoff` genuinely uses `δ < 1`. -/

/-- `payoffBound` of the patient repeated PD is nonnegative. -/
theorem payoffBound_nonneg_patient : 0 ≤ repeatedPDpatient.payoffBound :=
  repeatedPDpatient.payoffBound_nonneg

/-- **`payoffBound` of the patient repeated PD is exactly `18`.** It is the total absolute payoff
mass `∑ᵢ ∑ₐ |payoff i a|`; each player's four PD cells `{3, 0, 5, 1}` sum (in absolute value) to
`9`, and the two players give `9 + 9 = 18`. This is the concrete literal the bound theorems below
compare against. -/
theorem payoffBound_eq_eighteen : repeatedPDpatient.payoffBound = 18 := by
  change (∑ i : pd.Player, ∑ a : pd.ActionProfile, |pd.payoff i a|) = 18
  -- The four action profiles are the four maps `Fin 2 → Fin 2`; sum them out explicitly.
  have hprofiles : ∀ i : pd.Player, (∑ a : pd.ActionProfile, |pd.payoff i a|)
      = |pd.payoff i ![0, 0]| + |pd.payoff i ![0, 1]|
        + |pd.payoff i ![1, 0]| + |pd.payoff i ![1, 1]| := by
    intro i
    rw [show (Finset.univ : Finset (Fin 2 → Fin 2))
        = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [Fin.sum_univ_two, hprofiles 0, hprofiles 1]
  norm_num [pd, FiniteStrategicGame.mkFin, cooperate, defect, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

/-- The grim-trigger period payoff is bounded by `payoffBound`: `|3| ≤ payoffBound`. -/
theorem abs_periodExpectedPayoff_le_payoffBound_patient (t : ℕ) :
    |repeatedPDpatient.periodExpectedPayoff grimTrigger [] t (0 : Fin 2)|
      ≤ repeatedPDpatient.payoffBound :=
  repeatedPDpatient.abs_periodExpectedPayoff_le_payoffBound grimTrigger [] t (0 : Fin 2)

/-- The grim-trigger continuation value is bounded by `payoffBound`: With value `3` on the clean
path, `|3| ≤ payoffBound`. -/
theorem abs_continuationValue_le_payoffBound_patient :
    |repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2)|
      ≤ repeatedPDpatient.payoffBound :=
  repeatedPDpatient.abs_continuationValue_le_payoffBound grimTrigger [] (0 : Fin 2)

/-- **The bound, fully instantiated against the literal: `|3| ≤ 18`.** The grim-trigger clean-path
continuation value `3` (in absolute value) clears the concrete payoff bound `18`. Both sides are
numeric literals here — no opaque `payoffBound`. -/
theorem abs_continuationValue_le_eighteen_patient :
    |repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2)| ≤ 18 := by
  have hcv : repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2) = 3 :=
    continuationValue_grimTrigger_patient_clean [] isClean_nil 0
  rw [hcv]; norm_num

/-- **Summability of the discounted period-payoff sequence** for grim trigger, which genuinely uses
`δ = 3/4 < 1` (the geometric comparison diverges at `δ ≥ 1`). -/
theorem summable_discount_periodExpectedPayoff_patient :
    Summable (fun t : ℕ =>
      repeatedPDpatient.discount ^ t
        * repeatedPDpatient.periodExpectedPayoff grimTrigger [] t (0 : Fin 2)) :=
  repeatedPDpatient.summable_discount_periodExpectedPayoff grimTrigger [] (0 : Fin 2)

/-! ## Stage-profile probability machinery on grim trigger

The grim-trigger stage masses form a genuine distribution (sum to one, nonnegative, ≤ one), the
one-step extensive-form probability equals the stage mass, and the stage payoff is the
mass-weighted sum of pure-action payoffs. -/

/-- The grim-trigger stage masses sum to one (product-of-marginals normalization). -/
theorem sum_stageProfileProb_grimTrigger (h : pd.PublicHistory) :
    ∑ a : pd.ActionProfile, repeatedPDpatient.stageProfileProb grimTrigger h a = 1 :=
  repeatedPDpatient.sum_stageProfileProb grimTrigger h

/-- The grim-trigger stage masses are nonnegative. -/
theorem stageProfileProb_grimTrigger_nonneg (h : pd.PublicHistory) (a : pd.ActionProfile) :
    0 ≤ repeatedPDpatient.stageProfileProb grimTrigger h a :=
  repeatedPDpatient.stageProfileProb_nonneg grimTrigger h a

/-- The grim-trigger stage masses are bounded by one. -/
theorem stageProfileProb_grimTrigger_le_one (h : pd.PublicHistory) (a : pd.ActionProfile) :
    repeatedPDpatient.stageProfileProb grimTrigger h a ≤ 1 :=
  repeatedPDpatient.stageProfileProb_le_one grimTrigger h a

/-- The extensive-form one-step probability equals the stage mass for grim trigger. -/
theorem stepProb_eq_stageProfileProb_grimTrigger (h : pd.PublicHistory) (a : pd.ActionProfile) :
    repeatedPDpatient.toExtensiveForm.stepProb grimTrigger h a
      = repeatedPDpatient.stageProfileProb grimTrigger h a :=
  repeatedPDpatient.stepProb_eq_stageProfileProb grimTrigger h a

/-- The grim-trigger stage payoff is the mass-weighted sum of pure-action payoffs. -/
theorem stagePayoff_eq_sum_stageProfileProb_grimTrigger (h : pd.PublicHistory) (i : Fin 2) :
    repeatedPDpatient.stagePayoff grimTrigger h i
      = ∑ c : pd.ActionProfile, repeatedPDpatient.stageProfileProb grimTrigger h c
          * pd.payoff i c :=
  repeatedPDpatient.stagePayoff_eq_sum_stageProfileProb grimTrigger h i

/-! ## Public paths, finite histories, and path probabilities

`PublicPath` (the infinite cooperation path), `HistoriesOfLength`, `publicHistoryProb`, and
`finiteHorizonContinuationValue` on a concrete length-2 history under grim trigger. The clean
length-2 history `[(C,C), (C,C)]` has probability `1` (the cooperative path is deterministic under
grim trigger). -/

/-- Grim-trigger stage mass on the patient game: The indicator of the prescribed profile — the
library `stageProfileProb_grimTriggerStrategy` at the PD profiles (discount-independent). -/
private lemma stageProfileProb_grimTrigger_patient (h : pd.PublicHistory) (a : pd.ActionProfile) :
    repeatedPDpatient.stageProfileProb grimTrigger h a
      = if a = (fun j => grimTriggerPure j h) then (1 : ℝ) else 0 :=
  repeatedPDpatient.stageProfileProb_grimTriggerStrategy cooperativeProfile defectionProfile h a

/-- **The prescribed clean-path profile has mass exactly `1`.** At the (clean) empty history grim
trigger plays `(C, C)` deterministically, so `stageProfileProb grimTrigger [] cooperativeProfile`
equals `1` — a concrete literal, not just the generic "sums to one". -/
theorem stageProfileProb_grimTrigger_nil_coop_eq_one :
    repeatedPDpatient.stageProfileProb grimTrigger [] cooperativeProfile = 1 := by
  rw [stageProfileProb_grimTrigger_patient, if_pos]
  exact (grimTriggerProfile_of_isClean isClean_nil).symm

/-- **A nonprescribed profile has mass exactly `0`.** At the (clean) empty history grim trigger
does *not* play `(D, D)`, so `stageProfileProb grimTrigger [] defectionProfile = 0`. Together with
the literal above, this shows the stage mass is the genuine point indicator on the prescribed
profile, not merely a normalized distribution. -/
theorem stageProfileProb_grimTrigger_nil_defect_eq_zero :
    repeatedPDpatient.stageProfileProb grimTrigger [] defectionProfile = 0 := by
  rw [stageProfileProb_grimTrigger_patient, if_neg]
  -- The prescribed clean-path profile is `(C, C)`, so it disagrees with `(D, D)` at player `0`:
  -- `defectionProfile 0 = defect` but `grimTriggerPure 0 [] = cooperate` (`[]` is vacuously clean).
  intro hcontra
  have h0 := congrFun hcontra 0
  simp only [defectionProfile, grimTriggerPure] at h0
  exact absurd h0 (by decide)

/-- The infinite all-cooperate public path. -/
private def coopPath : pd.PublicPath := fun _ => cooperativeProfile

/-- The length-2 clean history `[(C,C), (C,C)]`. -/
private def cleanLen2 : pd.PublicHistory := [cooperativeProfile, cooperativeProfile]

/-- **Definitional `rfl` check.** `cleanLen2` has length `2` — `[(C,C), (C,C)]` is a two-element
list by definition. (The genuine `HistoriesOfLength`/`PublicPath` content is in
`cleanLen2_mem_historiesOfLength` and `publicHistoryProb_cleanLen2` below, not here.) -/
theorem cleanLen2_length : cleanLen2.length = 2 := rfl

/-- **Definitional `rfl` check.** `cleanLen2` is the length-2 prefix of the infinite cooperative
path `coopPath`: `[coopPath 0, coopPath 1] = [(C,C), (C,C)]` holds by unfolding `coopPath` and
`cleanLen2` (both constantly `(C,C)`). A `rfl` identity, not a substantive `PublicPath` lemma. -/
theorem cleanLen2_eq_coopPath_prefix :
    cleanLen2 = [coopPath 0, coopPath 1] := rfl

/-- `cleanLen2` lies in `HistoriesOfLength 2`. -/
theorem cleanLen2_mem_historiesOfLength :
    cleanLen2 ∈ pd.HistoriesOfLength 2 := by
  unfold cleanLen2
  simp only [FiniteStrategicGame.HistoriesOfLength, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨[cooperativeProfile], ⟨[], rfl, cooperativeProfile, rfl⟩, cooperativeProfile, rfl⟩

/-- **The length-2 cooperative history has probability one under grim trigger.** The cooperative
path is deterministic, so each of the two `(C,C)` steps has mass `1`: `1·1 = 1`. -/
theorem publicHistoryProb_cleanLen2 :
    repeatedPDpatient.publicHistoryProb grimTrigger cleanLen2 = 1 := by
  change repeatedPDpatient.publicHistoryProbFrom grimTrigger []
    (cooperativeProfile :: cooperativeProfile :: []) = 1
  rw [RepeatedGame.publicHistoryProbFrom_cons, RepeatedGame.publicHistoryProbFrom_cons,
    RepeatedGame.publicHistoryProbFrom_nil, mul_one]
  simp only [repeatedPDpatient.stepProb_eq_stageProfileProb]
  have hstep0 : repeatedPDpatient.stageProfileProb grimTrigger [] cooperativeProfile = 1 := by
    rw [stageProfileProb_grimTrigger_patient]
    rw [if_pos]
    exact (grimTriggerProfile_of_isClean isClean_nil).symm
  have hstep1 : repeatedPDpatient.stageProfileProb grimTrigger ([] ++ [cooperativeProfile])
      cooperativeProfile = 1 := by
    rw [stageProfileProb_grimTrigger_patient]
    rw [if_pos]
    exact (grimTriggerProfile_of_isClean (isClean_append_coop isClean_nil)).symm
  rw [hstep0, one_mul]
  exact hstep1

/-- **`finiteHorizonContinuationValue` is non-vacuous.** The length-1 finite-horizon value of grim
trigger from the empty history weights each length-1 history by its grim-trigger path probability;
only the deterministic `(C,C)` continuation contributes, giving the symbolic form `(1-δ)·3`. The
numeric literal `3/4` (at `δ = 3/4`) is stated separately in
`finiteHorizonContinuationValue_len1_eq`, so this theorem does not bake the discount in. -/
theorem finiteHorizonContinuationValue_len1 :
    repeatedPDpatient.finiteHorizonContinuationValue grimTrigger [] 1 (0 : Fin 2)
      = (1 - repeatedPDpatient.discount) * 3 := by
  unfold RepeatedGame.finiteHorizonContinuationValue
  -- Decompose the length-1 sum by first action (`sum_HistoriesOfLength_succ_first_action`, `t=0`);
  -- `HistoriesOfLength 0 = {[]}` so each first-action term is just `a :: []`.
  rw [RepeatedGame.sum_HistoriesOfLength_succ_first_action repeatedPDpatient.stage 0
      (fun suffix => repeatedPDpatient.publicHistoryProbFrom grimTrigger [] suffix
        * repeatedPDpatient.discountedPrefixPayoff suffix (0 : Fin 2))]
  simp only [FiniteStrategicGame.HistoriesOfLength, Finset.sum_singleton]
  have hterm : ∀ a : pd.ActionProfile,
      repeatedPDpatient.publicHistoryProbFrom grimTrigger [] [a]
        * repeatedPDpatient.discountedPrefixPayoff [a] (0 : Fin 2)
        = repeatedPDpatient.stageProfileProb grimTrigger [] a
          * ((1 - repeatedPDpatient.discount) * pd.payoff (0 : Fin 2) a) := by
    intro a
    rw [RepeatedGame.publicHistoryProbFrom_cons, RepeatedGame.publicHistoryProbFrom_nil, mul_one,
      repeatedPDpatient.stepProb_eq_stageProfileProb grimTrigger [] a]
    -- `discountedPrefixPayoff [a] 0 = (1-δ)·payoff 0 a + δ·0`.
    simp only [RepeatedGame.discountedPrefixPayoff, mul_zero, add_zero]
    rfl
  -- Collapse to the cooperative survivor (`.trans`-keyed to the goal sum to match the instance).
  have hcoll : (∑ a : repeatedPDpatient.stage.ActionProfile,
      repeatedPDpatient.publicHistoryProbFrom grimTrigger [] [a]
        * repeatedPDpatient.discountedPrefixPayoff [a] (0 : Fin 2))
      = (1 - repeatedPDpatient.discount) * 3 := by
    refine (Finset.sum_congr rfl (fun a _ => hterm a)).trans ?_
    refine (Finset.sum_eq_single_of_mem cooperativeProfile (Finset.mem_univ _)
      (fun b _ hb => ?_)).trans ?_
    · rw [stageProfileProb_grimTrigger_patient]
      rw [if_neg (fun h => hb (h.trans (grimTriggerProfile_of_isClean isClean_nil))), zero_mul]
    · rw [stageProfileProb_grimTrigger_patient]
      rw [if_pos]
      · have hpay : pd.payoff (0 : Fin 2) cooperativeProfile = 3 := by
          simp [cooperativeProfile, cooperate]
        rw [one_mul, hpay]
      · exact (grimTriggerProfile_of_isClean isClean_nil).symm
  exact hcoll

/-- **The length-1 finite-horizon value is exactly `3/4`.** Plugging the patient discount `δ = 3/4`
into the symbolic value `(1-δ)·3`: `(1 - 3/4)·3 = (1/4)·3 = 3/4`. This is the numeric literal the
docstring of `finiteHorizonContinuationValue_len1` advertises. -/
theorem finiteHorizonContinuationValue_len1_eq :
    repeatedPDpatient.finiteHorizonContinuationValue grimTrigger [] 1 (0 : Fin 2) = 3 / 4 := by
  rw [finiteHorizonContinuationValue_len1]
  have hδ : repeatedPDpatient.discount = 3 / 4 := rfl
  rw [hδ]; norm_num

/-! ## Locality / congruence lemmas (item 1) on the concrete deviation

The deviation `devDefect` agrees with `grimTrigger` at every history except `(0, [])`. We
exercise each congruence lemma on this concrete pair: At the post-deviation history `[(D,C)]`
(where they agree on the head action and on all continuations), the stage payoff, stage masses,
path probabilities, period payoffs, and continuation values all coincide; and the
continuity-at-infinity bound is non-vacuous. -/

/-- `devDefect` and `grimTrigger` agree at every action of every player at any extension of
`[(D,C)]` — they differ only at `(0, [])`, and `[(D,C)] ++ suffix` is never `[]`. -/
private lemma devDefect_grimTrigger_agree (j : pd.Player) (suffix : pd.PublicHistory) :
    devDefect j ([DC] ++ suffix) = grimTrigger j ([DC] ++ suffix) :=
  devDefect_agree_ext j suffix

/-- **`stagePayoff_congr`.** Agreeing head actions give equal one-period stage payoffs. -/
theorem stagePayoff_congr_devDefect (i : Fin 2) :
    repeatedPDimpatient.stagePayoff devDefect [DC] i
      = repeatedPDimpatient.stagePayoff grimTrigger [DC] i :=
  repeatedPDimpatient.stagePayoff_congr [DC]
    (fun j => by simpa using devDefect_grimTrigger_agree j []) i

/-- **`stageProfileProb_congr`.** Agreeing head actions give equal stage masses. -/
theorem stageProfileProb_congr_devDefect (a : pd.ActionProfile) :
    repeatedPDimpatient.stageProfileProb devDefect [DC] a
      = repeatedPDimpatient.stageProfileProb grimTrigger [DC] a :=
  repeatedPDimpatient.stageProfileProb_congr [DC]
    (fun j => by simpa using devDefect_grimTrigger_agree j []) a

/-- **`publicHistoryProbFrom_congr`.** Agreeing on all proper prefixes gives equal path
probabilities (here over length-1 continuations of `[(D,C)]`). -/
theorem publicHistoryProbFrom_congr_devDefect (a : pd.ActionProfile) :
    repeatedPDimpatient.publicHistoryProbFrom devDefect [DC] [a]
      = repeatedPDimpatient.publicHistoryProbFrom grimTrigger [DC] [a] :=
  repeatedPDimpatient.publicHistoryProbFrom_congr [a] [DC]
    (fun j pre _ => by
      -- `[DC] ++ pre` is an extension of `[DC]`, so the strategies agree there.
      simpa using devDefect_grimTrigger_agree j pre)

/-- **`periodExpectedPayoff_congr`.** Agreeing on the first `t+1` periods after `[(D,C)]` gives
equal period-`t` expected payoffs. -/
theorem periodExpectedPayoff_congr_devDefect (t : ℕ) (i : Fin 2) :
    repeatedPDimpatient.periodExpectedPayoff devDefect [DC] t i
      = repeatedPDimpatient.periodExpectedPayoff grimTrigger [DC] t i :=
  repeatedPDimpatient.periodExpectedPayoff_congr [DC] t i
    (fun j suffix _ => devDefect_grimTrigger_agree j suffix)

/-- **`continuationValue_congr`.** Agreeing at every continuation of `[(D,C)]` gives equal
continuation values — both equal the grim-trigger dirty value `1`. -/
theorem continuationValue_congr_devDefect (i : Fin 2) :
    repeatedPDimpatient.continuationValue devDefect [DC] i
      = repeatedPDimpatient.continuationValue grimTrigger [DC] i :=
  repeatedPDimpatient.continuationValue_congr [DC] i
    (fun j suffix => devDefect_grimTrigger_agree j suffix)

/-- **`abs_continuationValue_sub_le_of_eq_of_lt` (continuity at infinity) — the degenerate agreeing
case.** Two strategies agreeing for the first `T` periods after a history have continuation values
within `2·payoffBound·δ^T`. Instantiated at `T = 3` on the agreeing pair (both grim trigger and the
deviation coincide on *all* extensions of `[(D,C)]`), the bound holds but the difference is in fact
`0` — so this instance does not stress the tail estimate. The companion
`abs_continuationValue_sub_pos_devDefect_nil` instantiates the same lemma on the genuinely
*differing* pair (at the empty history, where `devDefect` defects and grim trigger cooperates),
where the left-hand side is strictly positive (`= 1`). -/
theorem abs_continuationValue_sub_le_devDefect (i : Fin 2) :
    |repeatedPDimpatient.continuationValue devDefect [DC] i
        - repeatedPDimpatient.continuationValue grimTrigger [DC] i|
      ≤ 2 * repeatedPDimpatient.payoffBound * repeatedPDimpatient.discount ^ 3 :=
  repeatedPDimpatient.abs_continuationValue_sub_le_of_eq_of_lt [DC] i 3
    (fun j suffix _ => devDefect_grimTrigger_agree j suffix)

/-- **The same continuity-at-infinity lemma on a genuinely differing pair — strictly positive
gap.** At the empty history `devDefect` and grim trigger *disagree* already at depth `0` (the
deviation defects, grim trigger cooperates), so the only admissible horizon is `T = 0` (vacuous
agreement). The bound is then `2·payoffBound·δ^0 = 2·18 = 36`, while the actual continuation-value
gap is the genuine impatient temptation difference `|4 - 3| = 1 > 0`. Unlike the `[(D,C)]` instance
this stresses the tail estimate: The left-hand side is nonzero and the slack `1 ≤ 36` is real. -/
theorem abs_continuationValue_sub_pos_devDefect_nil :
    0 < |repeatedPDimpatient.continuationValue devDefect [] (0 : Fin 2)
          - repeatedPDimpatient.continuationValue grimTrigger [] (0 : Fin 2)|
      ∧ |repeatedPDimpatient.continuationValue devDefect [] (0 : Fin 2)
          - repeatedPDimpatient.continuationValue grimTrigger [] (0 : Fin 2)|
        ≤ 2 * repeatedPDimpatient.payoffBound * repeatedPDimpatient.discount ^ 0 := by
  refine ⟨?_, ?_⟩
  · -- The gap equals `|4 - 3| = 1 > 0`.
    rw [cv_devDefect_nil_eq_four, cv_grimTrigger_nil_impatient]
    norm_num
  · -- Vacuous agreement up to `T = 0`: no `suffix` has `length < 0`.
    exact repeatedPDimpatient.abs_continuationValue_sub_le_of_eq_of_lt [] (0 : Fin 2) 0
      (fun _ _ hlt => absurd hlt (Nat.not_lt_zero _))

/-! ## Extensive-form bridges -/

/-- **`toExtensiveForm_unilateralDeviation_iff`.** The repeated-game unilateral-deviation predicate
on the concrete profile unfolds to per-coordinate equality off the deviator. The one-shot defection
`devDefect` is a unilateral `0`-deviation of grim trigger (it agrees with grim trigger at every
coordinate of every other player). -/
theorem toExtensiveForm_unilateralDeviation_devDefect :
    repeatedPDimpatient.toExtensiveForm.unilateralDeviation (0 : Fin 2) grimTrigger devDefect := by
  rw [RepeatedGame.toExtensiveForm_unilateralDeviation_iff]
  intro j obs hj
  -- An info-set deviation is in particular a unilateral deviation; reuse the info-set witness.
  exact (devDefect_isInfoSetDeviation j obs (fun heq => hj (congrArg Sigma.fst heq)))

/-- **`IsPerfectBayesianEquilibrium_toExtensiveGame_of_IsSubgamePerfectEquilibrium`.** The boundary
grim-trigger SPE induces a perfect Bayesian equilibrium of the associated perfect-information
extensive game with singleton (trivial) beliefs. -/
theorem grimTrigger_isPBE_boundary :
    IsPerfectBayesianEquilibrium repeatedPD.toExtensiveGame
      { strategy := grimTrigger
        beliefs := trivialBeliefs repeatedPD.stage.Player repeatedPD.stage.ActionProfile
          repeatedPD.toGameTree } :=
  repeatedPD.IsPerfectBayesianEquilibrium_toExtensiveGame_of_IsSubgamePerfectEquilibrium
    grimTrigger grimTrigger_SPE_boundary

/-! ## The positive side of the threshold: Grim trigger is an SPE at `δ = 3/4`

At the *patient* discount `δ = 3/4 > 1/2` the one-shot defection is **strictly** unprofitable
(the deviation earns `5 - 4δ = 2 < 3` on the clean path). We re-derive the example's `private`
one-shot-deviation infrastructure (`sum_profiles_pin_opponent`, `expand_profile_sum`, the four
`payoff_update_*` leaves) on the patient game — they depend only on the stage game `pd`, not the
discount — and run the one-shot-deviation principle with the *strict*-side arithmetic at
`δ = 3/4`. -/

/-- **Opponent-pinning collapse** (patient re-derivation of the example's `private` analog). When
the opponent `opp ≠ i` plays the pure action `b`, a sum over stage profiles weighted by the
deviator's marginal `α` and the opponent's vertex indicator collapses to the two profiles in which
`opp` plays `b` and the deviator plays cooperate or defect. -/
private lemma sum_profiles_pin_opponent_patient (i opp : Fin 2) (hoi : opp ≠ i) (b : Fin 2)
    (α : Fin 2 → ℝ) (F : (Fin 2 → Fin 2) → ℝ) :
    (∑ s : Fin 2 → Fin 2,
        α (s i) * (if s opp = b then (1 : ℝ) else 0) * F s) =
      α cooperate * F (Function.update (fun _ => b) i cooperate)
        + α defect * F (Function.update (fun _ => b) i defect) := by
  have hexhaust : ∀ k : Fin 2, k = i ∨ k = opp := by
    intro k; fin_cases i <;> fin_cases opp <;> fin_cases k <;> simp_all
  have hne : (Function.update (fun _ => b) i cooperate)
      ≠ (Function.update (fun _ => b) i defect) := by
    intro hcontra
    have hci := congrFun hcontra i
    rw [Function.update_self, Function.update_self] at hci
    exact absurd hci (by decide)
  rw [Fintype.sum_eq_add (Function.update (fun _ => b) i cooperate)
        (Function.update (fun _ => b) i defect) hne ?_]
  · rw [Function.update_of_ne hoi, Function.update_of_ne hoi,
      Function.update_self, Function.update_self]
    simp only [if_true]
    ring
  · intro s ⟨hsc, hsd⟩
    by_cases hsopp : s opp = b
    · exfalso
      rcases (show s i = (0 : Fin 2) ∨ s i = (1 : Fin 2) by omega) with hsi | hsi
      · refine hsc (funext (fun k => ?_))
        rcases hexhaust k with rfl | rfl
        · rw [Function.update_self]; exact hsi
        · rw [Function.update_of_ne hoi]; exact hsopp
      · refine hsd (funext (fun k => ?_))
        rcases hexhaust k with rfl | rfl
        · rw [Function.update_self]; exact hsi
        · rw [Function.update_of_ne hoi]; exact hsopp
    · rw [if_neg hsopp, mul_zero, zero_mul]

/-- **Stage-expectation expansion** (patient re-derivation). The expected value of any continuation
functional `G` over stage profiles, under a deviator playing marginal `atHistory σ' i h` against an
opponent `opp ≠ i` who plays the vertex at `b`, collapses to the deviator's two pure responses. -/
private lemma expand_profile_sum_patient (i opp : Fin 2) (hoi : opp ≠ i)
    (h : pd.PublicHistory) (σ' : repeatedPDpatient.PublicStrategy) (b : Fin 2)
    (hb : repeatedPDpatient.atHistory σ' opp h = stdSimplex.vertex b)
    (G : repeatedPDpatient.stage.ActionProfile → ℝ) :
    (∑ c : repeatedPDpatient.stage.ActionProfile,
        repeatedPDpatient.stageProfileProb σ' h c * G c) =
      (repeatedPDpatient.atHistory σ' i h).val cooperate
          * G (Function.update (fun _ => b) i cooperate)
        + (repeatedPDpatient.atHistory σ' i h).val defect
          * G (Function.update (fun _ => b) i defect) := by
  have hrewrite : ∀ c : repeatedPDpatient.stage.ActionProfile,
      repeatedPDpatient.stageProfileProb σ' h c =
        (repeatedPDpatient.atHistory σ' i h).val (c i) * (if c opp = b then (1 : ℝ) else 0) := by
    intro c
    have hprodfac : repeatedPDpatient.stageProfileProb σ' h c =
        (repeatedPDpatient.atHistory σ' i h).val (c i)
          * (repeatedPDpatient.atHistory σ' opp h).val (c opp) :=
      Fintype.prod_eq_mul (f := fun k => (repeatedPDpatient.atHistory σ' k h).val (c k)) i opp
        (Ne.symm hoi)
        (fun x ⟨_, _⟩ => by
          exfalso; fin_cases i <;> fin_cases opp <;> fin_cases x <;> simp_all)
    have hopp_fac : (repeatedPDpatient.atHistory σ' opp h).val (c opp)
        = if c opp = b then (1 : ℝ) else 0 := by
      rw [hb]
      by_cases hco : c opp = b
      · rw [if_pos hco]; exact stdSimplex.vertex_apply_eq hco.symm
      · rw [if_neg hco]; exact stdSimplex.vertex_apply_ne (fun heq => hco heq.symm)
    rw [hprodfac, hopp_fac]
  simp only [hrewrite]
  exact sum_profiles_pin_opponent_patient i opp hoi b (repeatedPDpatient.atHistory σ' i h).val G

/-- Stage payoff to `i` when `i` cooperates and the opponent cooperates: The reward `R = 3`. -/
private lemma payoff_update_coop_coop_patient (i : Fin 2) :
    pd.payoff i (Function.update (fun _ => cooperate) i cooperate) = 3 := by
  fin_cases i <;> simp [pd, FiniteStrategicGame.mkFin, Function.update, cooperate]

/-- Stage payoff to `i` when `i` defects against a cooperating opponent: The temptation `T = 5`. -/
private lemma payoff_update_coop_defect_patient (i : Fin 2) :
    pd.payoff i (Function.update (fun _ => cooperate) i defect) = 5 := by
  fin_cases i <;> simp [pd, FiniteStrategicGame.mkFin, Function.update, cooperate, defect]

/-- Stage payoff to `i` when `i` cooperates against a defecting opponent: The sucker payoff
`S = 0`. -/
private lemma payoff_update_defect_coop_patient (i : Fin 2) :
    pd.payoff i (Function.update (fun _ => defect) i cooperate) = 0 := by
  fin_cases i <;> simp [pd, FiniteStrategicGame.mkFin, Function.update, cooperate, defect]

/-- Stage payoff to `i` when `i` defects and the opponent defects: The punishment `P = 1`. -/
private lemma payoff_update_defect_defect_patient (i : Fin 2) :
    pd.payoff i (Function.update (fun _ => defect) i defect) = 1 := by
  fin_cases i <;> simp [pd, FiniteStrategicGame.mkFin, Function.update, defect, cooperate]

/-- **No one-shot deviation against grim trigger is profitable at `δ = 3/4`.** On a clean history
the deviator mixing weight `α` onto defect earns `(1-δ)(3(1-α) + 5α) + δ(3(1-α) + 1α) = 3 - α ≤ 3`
— *strictly* below `3` whenever `α > 0`, since `5 - 4δ = 2 < 3`. The strict-margin anchor at the
pure defect (`α = 1`) is stated as `cv_devDefect_nil_patient_eq_two` and
`devDefect_strictly_unprofitable_patient`. On a dirty history the opponent defects forever and
punishment is absorbing, so cooperating with weight `β` earns
`(1-δ)((1-β)·1) + δ·1 = 1 - (1-δ)β ≤ 1`. -/
theorem noProfitableOneShotDeviation_grimTrigger_patient :
    repeatedPDpatient.NoProfitableOneShotDeviation grimTrigger := by
  intro i h σ' hdev
  -- Bellman one-step decomposition of the deviation's continuation value at `h`.
  rw [repeatedPDpatient.continuationValue_eq_step σ' h i]
  -- Locality: at every continuation of `h ++ [c]` the deviator already coincides with grim trigger.
  have hsucc : ∀ c : repeatedPDpatient.stage.ActionProfile,
      repeatedPDpatient.continuationValue σ' (h ++ [c]) i =
        repeatedPDpatient.continuationValue grimTrigger (h ++ [c]) i := by
    intro c
    refine repeatedPDpatient.continuationValue_congr (h ++ [c]) i (fun j suffix => ?_)
    refine hdev j ((h ++ [c]) ++ suffix) (fun hcontra => ?_)
    have hlen : ((h ++ [c]) ++ suffix).length = h.length := by
      have hlists : (h ++ [c]) ++ suffix = h := by
        have h2 := (Sigma.mk.inj_iff.mp hcontra).2
        exact eq_of_heq h2
      rw [hlists]
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  simp only [hsucc]
  have hδ : repeatedPDpatient.discount = 3 / 4 := rfl
  -- The deviator's marginal weights on cooperate / defect sum to one and are nonnegative.
  have hαsum : (repeatedPDpatient.atHistory σ' i h).val cooperate
      + (repeatedPDpatient.atHistory σ' i h).val defect = 1 := by
    have hsum : ∑ x : Fin 2, (repeatedPDpatient.atHistory σ' i h).val x = 1 :=
      (repeatedPDpatient.atHistory σ' i h).property.2
    rwa [Fin.sum_univ_two] at hsum
  have hα0_nn : 0 ≤ (repeatedPDpatient.atHistory σ' i h).val cooperate :=
    (repeatedPDpatient.atHistory σ' i h).property.1 cooperate
  have hα1_nn : 0 ≤ (repeatedPDpatient.atHistory σ' i h).val defect :=
    (repeatedPDpatient.atHistory σ' i h).property.1 defect
  -- The deviation is one-shot, so off the deviator the opponent's mixed action at `h` is the
  -- grim-trigger vertex.
  have hopp : ∀ j : Fin 2, j ≠ i →
      repeatedPDpatient.atHistory σ' j h = stdSimplex.vertex (grimTriggerPure j h) := by
    intro j hji
    have hσ'j : σ' j h = grimTrigger j h :=
      hdev j h (fun hcontra => hji (congrArg Sigma.fst hcontra))
    refine eq_of_heq ((simplexTransport_heq _ _).trans ?_)
    rw [hσ'j, grimTrigger_eq]
    exact pureStrategy_heq_vertex grimTriggerPure j h
  -- Fix the unique opponent index and rewrite the stage payoff as a weighted profile sum.
  obtain ⟨opp, hoi⟩ : ∃ opp : Fin 2, opp ≠ i := exists_ne (α := Fin 2) i
  rw [repeatedPDpatient.stagePayoff_eq_sum_stageProfileProb σ' h i]
  by_cases hclean : IsClean h
  · -- Clean: opponent cooperates; the deviator's defect weight strictly lowers the value below `3`.
    rw [continuationValue_grimTrigger_patient_clean h hclean i]
    have hb : repeatedPDpatient.atHistory σ' opp h = stdSimplex.vertex cooperate := by
      rw [hopp opp hoi, congrFun (grimTriggerProfile_of_isClean hclean) opp]; rfl
    rw [expand_profile_sum_patient i opp hoi h σ' cooperate hb (repeatedPDpatient.stage.payoff i),
      expand_profile_sum_patient i opp hoi h σ' cooperate hb
        (fun c => repeatedPDpatient.continuationValue grimTrigger (h ++ [c]) i)]
    set pc : repeatedPDpatient.stage.ActionProfile :=
      Function.update (fun _ => cooperate) i cooperate with hpc_def
    set pdf : repeatedPDpatient.stage.ActionProfile := Function.update (fun _ => cooperate) i defect
      with hpdf_def
    -- When the deviator also cooperates, the appended profile is the cooperative profile.
    have hpc_coop : pc = cooperativeProfile := by
      funext k; rw [hpc_def]; simp only [cooperativeProfile]; by_cases hk : k = i
      · rw [hk, Function.update_self]
      · rw [Function.update_of_ne hk]
    have hpdf_i : pdf i = defect := by rw [hpdf_def, Function.update_self]
    -- Evaluate the four leaves: payoffs `3`, `5` and continuation values `3`, `1`.
    have hpay_c : repeatedPDpatient.stage.payoff i pc = 3 := by
      rw [hpc_def]; exact payoff_update_coop_coop_patient i
    have hpay_d : repeatedPDpatient.stage.payoff i pdf = 5 := by
      rw [hpdf_def]; exact payoff_update_coop_defect_patient i
    have hcv_c : repeatedPDpatient.continuationValue grimTrigger (h ++ [pc]) i = 3 := by
      rw [hpc_coop]
      exact continuationValue_grimTrigger_patient_clean _ (isClean_append_coop hclean) i
    have hcv_d : repeatedPDpatient.continuationValue grimTrigger (h ++ [pdf]) i = 1 := by
      refine continuationValue_grimTrigger_patient_dirty _ (fun hclean' => ?_) i
      have hmem : pdf ∈ (h ++ [pdf]) :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      have heq := hclean' _ hmem
      rw [heq] at hpdf_i
      exact Fin.zero_ne_one hpdf_i
    rw [hpay_c, hpay_d, hcv_c, hcv_d, hδ]
    -- `(1/4)(3α0 + 5α1) + (3/4)(3α0 + 1α1) = 3α0 + 2α1 = 3 - α1 ≤ 3`.
    nlinarith [hαsum, hα0_nn, hα1_nn]
  · -- Dirty: opponent defects forever; punishment is absorbing, so any deviation earns `≤ 1`.
    rw [continuationValue_grimTrigger_patient_dirty h hclean i]
    have hb : repeatedPDpatient.atHistory σ' opp h = stdSimplex.vertex defect := by
      rw [hopp opp hoi, congrFun (grimTriggerProfile_of_not_isClean hclean) opp]; rfl
    rw [expand_profile_sum_patient i opp hoi h σ' defect hb (repeatedPDpatient.stage.payoff i),
      expand_profile_sum_patient i opp hoi h σ' defect hb
        (fun c => repeatedPDpatient.continuationValue grimTrigger (h ++ [c]) i)]
    set pc : repeatedPDpatient.stage.ActionProfile := Function.update (fun _ => defect) i cooperate
      with hpc_def
    set pdf : repeatedPDpatient.stage.ActionProfile := Function.update (fun _ => defect) i defect
      with hpdf_def
    -- Evaluate the four leaves: payoffs `0`, `1` and both continuation values `1` (absorbing).
    have hpay_c : repeatedPDpatient.stage.payoff i pc = 0 := by
      rw [hpc_def]; exact payoff_update_defect_coop_patient i
    have hpay_d : repeatedPDpatient.stage.payoff i pdf = 1 := by
      rw [hpdf_def]; exact payoff_update_defect_defect_patient i
    have hcv_c : repeatedPDpatient.continuationValue grimTrigger (h ++ [pc]) i = 1 :=
      continuationValue_grimTrigger_patient_dirty _ (not_isClean_append hclean pc) i
    have hcv_d : repeatedPDpatient.continuationValue grimTrigger (h ++ [pdf]) i = 1 :=
      continuationValue_grimTrigger_patient_dirty _ (not_isClean_append hclean pdf) i
    rw [hpay_c, hpay_d, hcv_c, hcv_d, hδ]
    -- `(1/4)(0·α0 + 1·α1) + (3/4)(α0 + α1) = 3/4 + α1/4 ≤ 1` since `α1 ≤ 1`.
    nlinarith [hαsum, hα0_nn, hα1_nn]

/-- The deviation's continuation value from `[(D, C)]` is the grim-trigger dirty value `1` at the
**patient** calibration (the post-deviation path follows grim trigger forever). -/
private lemma cv_devDefect_DC_patient :
    repeatedPDpatient.continuationValue devDefect [DC] (0 : Fin 2) = 1 := by
  refine repeatedPDpatient.continuationValue_of_const (σ := devDefect) (h := [DC]) (0 : Fin 2) 1
    (fun t => ?_)
  rw [repeatedPDpatient.periodExpectedPayoff_congr [DC] t (0 : Fin 2)
    (fun j suffix _ => devDefect_agree_ext j suffix)]
  exact periodExpectedPayoff_grimTrigger_of_not_isClean (0 : Fin 2) t [DC] not_isClean_DC

/-- **The strict patient deviation anchor: The defect deviation value is exactly `2`.** At
`δ = 3/4`, `(1-δ)·5 + δ·1 = 5 - 4·(3/4) = (1/4)·5 + (3/4)·1 = 2`. This is the value the prose of
`noProfitableOneShotDeviation_grimTrigger_patient` and `grimTrigger_SPE_patient` advertise but did
not previously state as a public theorem. It sits *strictly below* the cooperation value `3`. -/
theorem cv_devDefect_nil_patient_eq_two :
    repeatedPDpatient.continuationValue devDefect [] (0 : Fin 2) = 2 := by
  rw [repeatedPDpatient.continuationValue_eq_step devDefect [] (0 : Fin 2)]
  -- `stagePayoff` and `stageProfileProb` are discount-free, so the `repeatedPD` helpers apply by
  -- definitional equality (forced through explicitly-typed `have`s, not `rw`).
  rw [show repeatedPDpatient.stagePayoff devDefect [] (0 : Fin 2) = 5
    from stagePayoff_devDefect_nil]
  have hoff : ∀ b : pd.ActionProfile, b ≠ DC →
      repeatedPDpatient.stageProfileProb devDefect [] b
        * repeatedPDpatient.continuationValue devDefect ([] ++ [b]) (0 : Fin 2) = 0 := by
    intro b hb
    have hb0 : repeatedPDpatient.stageProfileProb devDefect [] b
        = if b = DC then (1 : ℝ) else 0 := stageProfileProb_devDefect_nil b
    rw [hb0, if_neg hb, zero_mul]
  have hon : repeatedPDpatient.stageProfileProb devDefect [] DC
      * repeatedPDpatient.continuationValue devDefect ([] ++ [DC]) (0 : Fin 2) = 1 := by
    have hDC : repeatedPDpatient.stageProfileProb devDefect [] DC
        = if DC = DC then (1 : ℝ) else 0 := stageProfileProb_devDefect_nil DC
    rw [hDC, if_pos rfl, one_mul]
    exact cv_devDefect_DC_patient
  have hsum : (∑ c : repeatedPDpatient.stage.ActionProfile,
      repeatedPDpatient.stageProfileProb devDefect [] c
        * repeatedPDpatient.continuationValue devDefect ([] ++ [c]) (0 : Fin 2)) = 1 :=
    (Finset.sum_eq_single_of_mem DC (Finset.mem_univ DC) (fun b _ hb => hoff b hb)).trans hon
  rw [hsum]
  have hδ : repeatedPDpatient.discount = 3 / 4 := rfl
  rw [hδ]; norm_num

/-- **The patient defect deviation is *strictly* unprofitable: `2 < 3`.** Above the threshold the
deviation's continuation value `2` is strictly below grim trigger's clean-path value `3` — the
strict-margin anchor (`5 - 4·(3/4) = 2 < 3`) that sustains cooperation at `δ = 3/4`. (Contrast the
boundary `δ = 1/2`, where the analogous value is exactly `3` — indifference; and the impatient
`δ = 1/4`, where it is `4 > 3` — strictly profitable.) -/
theorem devDefect_strictly_unprofitable_patient :
    repeatedPDpatient.continuationValue devDefect [] (0 : Fin 2)
      < repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2) := by
  have hgt : repeatedPDpatient.continuationValue grimTrigger [] (0 : Fin 2) = 3 :=
    continuationValue_grimTrigger_patient_clean [] isClean_nil 0
  rw [cv_devDefect_nil_patient_eq_two, hgt]
  norm_num

/-- **Grim trigger is a subgame-perfect equilibrium at the patient discount `δ = 3/4`.** Strictly
above the threshold `δ = 1/2`, no one-shot deviation is profitable: On clean histories the defect
deviation earns `(1-δ)·5 + δ·1 = 5 - 4δ = 2 < 3` (the strict anchor
`cv_devDefect_nil_patient_eq_two` / `devDefect_strictly_unprofitable_patient`), and on dirty
histories mutual defection is the static Nash. -/
theorem grimTrigger_SPE_patient :
    repeatedPDpatient.IsSubgamePerfectEquilibrium grimTrigger :=
  noProfitableOneShotDeviation_grimTrigger_patient.isSubgamePerfectEquilibrium

end EconlibTest.GameTheory.Repeated

end
