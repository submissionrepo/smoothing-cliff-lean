/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Arrow
public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Econlib.SocialChoice.ChoiceFunction.Properties
public import Econlib.SocialChoice.Profile.Transform
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Gibbard–Satterthwaite Theorem

On the strict-orders domain (Gibbard 1973, Satterthwaite 1975), every resolute social choice
function on at least three alternatives that is strategy-proof and surjective must have a dictator.

The theorem is established via reduction to Arrow's Impossibility Theorem. Given a resolute,
strategy-proof, surjective choice function `f` on the strict-orders domain, an auxiliary welfare
function `welfareFunctionOfChoiceFunction f` is constructed whose social ranking of `(x, y)` is
determined by the winner of `f` on the profile in which every voter has `{x, y}` lifted to the top.
This induced welfare function satisfies Weak Pareto and IIA, so Arrow's theorem yields a
welfare-function dictator, which is then lifted back to a choice-function dictator.

## Main definitions

* `chooseWinner`: The unique winner of a resolute choice function.
* `liftPairOf`, `liftPair`: Lift a pair `{x, y}` to the top of a preference or profile.
* `liftTripleOf`, `liftTriple`: Lift a triple `{u, v, w}` to the top of a preference or profile.
* `hybridProfile`: A profile that uses one source for voters in a set, another for the rest.
* `aggregateOfChoiceFunction`: The induced binary social ranking on pairs.
* `welfareFunctionOfChoiceFunction`: The induced welfare function.

## Main statements

* `pareto_property`: Surjective, strategy-proof resolute choice functions satisfy weak Pareto.
* `weakPareto_welfareFunctionOfChoiceFunction`: The induced welfare function satisfies Weak Pareto.
* `iia_welfareFunctionOfChoiceFunction`: The induced welfare function satisfies IIA.
* `choiceFunction_dictator_of_welfareFunction_dictator`: A dictator for the induced welfare
  function is also a dictator for the choice function.
* `gibbard_satterthwaite`: The main theorem.

## References

* Gibbard, Allan. 1973. “Manipulation of Voting Schemes: A General Result.” *Econometrica* 41 (4):
  587. [https://doi.org/10.2307/1914083](https://doi.org/10.2307/1914083).
* Satterthwaite, Mark Allen. 1975. “Strategy-Proofness and Arrow's Conditions: Existence and
  Correspondence Theorems for Voting Procedures and Social Welfare Functions.” *Journal of Economic
  Theory* 10 (2): 187–217. [https://doi.org/10.1016/0022-0531(75)90050-2](https://doi.org/10.1016/0022-0531(75)90050-2).

## Tags

social choice, strategy-proofness, gibbard-satterthwaite, dictator, arrow
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter Alt : Type*}

/-! ### Resolution: The unique winner -/

/-- The unique winner of a resolute choice function on an admissible profile. -/
noncomputable def chooseWinner
    (f : ChoiceFunction Voter Alt)
    -- resoluteness is not needed to pick a witness, only to prove it is the unique winner
    -- (see `chooseWinner_mem`/`winners_eq_singleton`); kept here so all call sites share
    -- one signature.
    (_hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (P : Profile Voter Alt) (hP : P ∈ f.domain) : Alt :=
  (f.winners_nonempty P hP).choose

lemma chooseWinner_mem
    (f : ChoiceFunction Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (P : Profile Voter Alt) (hP : P ∈ f.domain) :
    chooseWinner f hRes P hP ∈ f.winners P :=
  (f.winners_nonempty P hP).choose_spec

lemma winners_eq_singleton
    (f : ChoiceFunction Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (P : Profile Voter Alt) (hP : P ∈ f.domain) :
    f.winners P = {chooseWinner f hRes P hP} := by
  ext a
  rw [Set.mem_singleton_iff]
  refine ⟨fun ha => hRes P hP ha (chooseWinner_mem f hRes P hP), fun ha => ?_⟩
  rw [ha]; exact chooseWinner_mem f hRes P hP

lemma chooseWinner_eq_iff
    (f : ChoiceFunction Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (P : Profile Voter Alt) (hP : P ∈ f.domain) (a : Alt) :
    chooseWinner f hRes P hP = a ↔ a ∈ f.winners P := by
  constructor
  · intro h
    rw [← h]
    exact chooseWinner_mem f hRes P hP
  · intro h
    exact (hRes P hP (chooseWinner_mem f hRes P hP) h)

/-! ### The two-alternative lift

`liftPairOf R x y` puts `{x, y}` at the top of `R`, with their relative order matching `R`.
Everything else stays in its original relative order, and is strictly below both `x` and `y`. -/

variable [DecidableEq Alt]

/-- A preference relation that lifts the pair `{x, y}` to the top, preserving the (x, y) relative
order from `R` and the relative order of all other pairs. -/
def liftPairOf (R : PreferenceRel Alt) (x y : Alt) : PreferenceRel Alt where
  le u v :=
    if u = x ∨ u = y then
      if v = x ∨ v = y then R.le u v else True
    else
      if v = x ∨ v = y then False else R.le u v
  le_refl u := by
    by_cases hu : u = x ∨ u = y
    · simp only [hu, ↓reduceIte]
      exact R.le_refl u
    · simp only [hu, ↓reduceIte]
      exact R.le_refl u
  le_trans u v w huv hvw := by
    by_cases hu : u = x ∨ u = y
    · by_cases hv : v = x ∨ v = y
      · by_cases hw : w = x ∨ w = y
        · simp only [hu, hv, hw, if_true] at huv hvw ⊢
          exact R.le_trans u v w huv hvw
        · simp only [hu, hw, if_true, if_false]
      · -- u in top, v outside top.
        by_cases hw : w = x ∨ w = y
        · -- v outside, w in top → hvw is False, contradiction.
          simp only [hv, hw, if_false, if_true] at hvw
        · -- v outside, w outside: goal is u in top, w outside → True.
          simp only [hu, hw, if_true, if_false]
    · by_cases hv : v = x ∨ v = y
      · -- u outside, v in top: huv is False, contradiction.
        simp only [hu, hv, if_false, if_true] at huv
      · by_cases hw : w = x ∨ w = y
        · -- u outside, v outside, w in top: hvw is False, contradiction.
          simp only [hv, hw, if_false, if_true] at hvw
        · simp only [hu, hv, hw, if_false] at huv hvw ⊢
          exact R.le_trans u v w huv hvw
  le_total u v := by
    by_cases hu : u = x ∨ u = y
    · by_cases hv : v = x ∨ v = y
      · simp only [hu, hv, if_true]
        exact R.le_total u v
      · -- u in top, v out: u ≤ v gives True.
        left
        simp only [hu, hv, if_true, if_false]
    · by_cases hv : v = x ∨ v = y
      · -- u out, v in top: v ≤ u gives True.
        right
        simp only [hu, hv, if_true, if_false]
      · simp only [hu, hv, if_false]
        exact R.le_total u v

/-- The lift of a profile: Lift each voter's preference. -/
def liftPair (P : Profile Voter Alt) (x y : Alt) : Profile Voter Alt :=
  fun i => liftPairOf (P i) x y

/-- `liftPairOf` only depends on the unordered pair `{x, y}`. -/
lemma liftPairOf_swap (R : PreferenceRel Alt) (x y : Alt) :
    liftPairOf R y x = liftPairOf R x y := by
  apply PreferenceRel.ext_le
  funext a b
  -- The two relations differ only in the unordered-pair predicate `· = x ∨ · = y`, which is
  -- symmetric under swapping `x` and `y`; rewriting `or_comm` aligns the branch conditions.
  simp only [liftPairOf, or_comm (a := a = y), or_comm (a := b = y)]

/-- `liftPair` only depends on the unordered pair `{x, y}`. -/
lemma liftPair_swap (P : Profile Voter Alt) (x y : Alt) :
    liftPair P y x = liftPair P x y := by
  funext i
  exact liftPairOf_swap (P i) x y

/-- Membership-in-top-pair predicate. -/
private def InPair (x y u : Alt) : Prop := u = x ∨ u = y

/-- Unfolding lemma for `liftPairOf.le`. -/
@[simp] lemma liftPairOf_le_iff (R : PreferenceRel Alt) (x y u v : Alt) :
    (liftPairOf R x y).le u v ↔
      (if u = x ∨ u = y then
        if v = x ∨ v = y then R.le u v else True
      else
        if v = x ∨ v = y then False else R.le u v) := Iff.rfl

/-- In the lift, members of the top pair are weakly above non-members. -/
lemma liftPairOf_le_top_outside {R : PreferenceRel Alt} {x y u v : Alt}
    (hu : u = x ∨ u = y) (hv : ¬ (v = x ∨ v = y)) :
    (liftPairOf R x y).le u v := by
  simp [liftPairOf_le_iff, hu, hv]

/-- In the lift, non-members are not weakly above members of the top pair. -/
lemma liftPairOf_not_le_outside_top {R : PreferenceRel Alt} {x y u v : Alt}
    (hu : ¬ (u = x ∨ u = y)) (hv : v = x ∨ v = y) :
    ¬ (liftPairOf R x y).le u v := by
  simp [liftPairOf_le_iff, hu, hv]

/-- In the lift, the (x, y) pair has the same `le` as the original. -/
lemma liftPairOf_le_xy (R : PreferenceRel Alt) (x y : Alt) :
    (liftPairOf R x y).le x y ↔ R.le x y := by
  simp [liftPairOf_le_iff]

lemma liftPairOf_le_yx (R : PreferenceRel Alt) (x y : Alt) :
    (liftPairOf R x y).le y x ↔ R.le y x := by
  by_cases hyx : y = x
  · subst hyx
    simp [liftPairOf_le_iff]
  · simp [liftPairOf_le_iff, hyx]

/-- The strict (x, y) ranking is preserved by `liftPairOf`. -/
lemma liftPairOf_lt_xy (R : PreferenceRel Alt) (x y : Alt) :
    (liftPairOf R x y).lt x y ↔ R.lt x y := by
  unfold PreferenceRel.lt
  rw [liftPairOf_le_xy, liftPairOf_le_yx]

lemma liftPairOf_lt_yx (R : PreferenceRel Alt) (x y : Alt) :
    (liftPairOf R x y).lt y x ↔ R.lt y x := by
  unfold PreferenceRel.lt
  rw [liftPairOf_le_xy, liftPairOf_le_yx]

/-- In the lift, x is strictly above any alternative outside `{x, y}`. -/
lemma liftPairOf_lt_top_outside {R : PreferenceRel Alt} {x y w : Alt}
    (hwx : w ≠ x) (hwy : w ≠ y) :
    (liftPairOf R x y).lt x w := by
  have hwOut : ¬ (w = x ∨ w = y) := by rintro (h | h); exacts [hwx h, hwy h]
  refine ⟨?_, ?_⟩
  · exact liftPairOf_le_top_outside (Or.inl rfl) hwOut
  · exact liftPairOf_not_le_outside_top hwOut (Or.inl rfl)

lemma liftPairOf_lt_top_outside_y {R : PreferenceRel Alt} {x y w : Alt}
    (hwx : w ≠ x) (hwy : w ≠ y) :
    (liftPairOf R x y).lt y w := by
  have hwOut : ¬ (w = x ∨ w = y) := by rintro (h | h); exacts [hwx h, hwy h]
  refine ⟨?_, ?_⟩
  · exact liftPairOf_le_top_outside (Or.inr rfl) hwOut
  · exact liftPairOf_not_le_outside_top hwOut (Or.inr rfl)

/-! ### Strict-domain bridges -/

omit [DecidableEq Alt] in
/-- A profile in `f.domain = strictDomain` is strict. -/
lemma profile_isStrict_of_mem_domain
    {f : ChoiceFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt) {P : Profile Voter Alt}
    (hP : P ∈ f.domain) : Profile.IsStrict P := by
  rw [hDomEq] at hP; exact hP

/-- `liftPairOf` preserves strictness. -/
lemma StrictPref.liftPairOf {R : PreferenceRel Alt} (h : StrictPref R) (x y : Alt) :
    StrictPref (liftPairOf R x y) := by
  intro u v huv
  obtain ⟨h1, h2⟩ := huv
  rw [liftPairOf_le_iff] at h1 h2
  by_cases hu : u = x ∨ u = y
  · by_cases hv : v = x ∨ v = y
    · simp only [hu, hv, if_true] at h1 h2
      exact h u v ⟨h1, h2⟩
    · simp only [hu, hv, if_true, if_false] at h2
  · by_cases hv : v = x ∨ v = y
    · simp only [hu, hv, if_true, if_false] at h1
    · simp only [hu, hv, if_false] at h1 h2
      exact h u v ⟨h1, h2⟩

/-- `liftPair` preserves strictness pointwise. -/
lemma liftPair_isStrict {P : Profile Voter Alt} (hP : Profile.IsStrict P) (x y : Alt) :
    Profile.IsStrict (liftPair P x y) := fun i => (hP i).liftPairOf x y

/-- The lift `liftPair P x y` lies in `f.domain` whenever `P` does. -/
lemma liftPair_mem_domain
    {f : ChoiceFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt) {P : Profile Voter Alt}
    (hP : P ∈ f.domain) (x y : Alt) :
    liftPair P x y ∈ f.domain := by
  rw [hDomEq]
  exact liftPair_isStrict (profile_isStrict_of_mem_domain hDomEq hP) x y

omit [DecidableEq Alt] in
/-- The strictDomain is closed under pointwise updates by strict preferences. -/
lemma update_mem_strictDomain [DecidableEq Voter] {P : Profile Voter Alt}
    (hP : Profile.IsStrict P) (i : Voter) {R' : PreferenceRel Alt}
    (hR' : StrictPref R') :
    Profile.IsStrict (Function.update P i R') := by
  intro j
  by_cases hji : j = i
  · subst hji; simpa using hR'
  · simp only [Function.update, hji]; exact hP j

/-! ### Strategy-proofness consequences

The standard "Maskin monotonicity" lemma: Changing one voter's preference in a way that does
not move the current winner down (relative to other alternatives) does not change the winner. -/

variable [DecidableEq Voter]

omit [DecidableEq Alt] in
/-- **SP single-voter monotonicity (resolute form).** If voter `i` deviates from `P i` to `R'`, the
new winner `w'` either equals `w`, or neither `P i` ranks `w'` strictly above `w` nor does `R'`
rank `w` strictly above `w'`. -/
lemma chooseWinner_eq_or_lt
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hSP : ChoiceFunction.StrategyProof f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (i : Voter) (R' : PreferenceRel Alt)
    (hP' : Function.update P i R' ∈ f.domain) :
    let w := chooseWinner f hRes P hP
    let w' := chooseWinner f hRes (Function.update P i R') hP'
    w = w' ∨ (¬ (P i).lt w' w ∧ ¬ R'.lt w w') := by
  intro w w'
  have hSP1 := hSP P hP i R' hP'
  have hwP : w ∈ f.winners P := chooseWinner_mem f hRes P hP
  have hwP' : w' ∈ f.winners (Function.update P i R') := chooseWinner_mem f hRes _ hP'
  have hnot_lt_PiI : ¬ (P i).lt w' w := by
    intro h
    apply hSP1
    refine ⟨w', hwP', ?_⟩
    intro a ha
    rw [winners_eq_singleton f hRes P hP, Set.mem_singleton_iff] at ha
    rw [ha]
    exact h
  have hupd : Function.update (Function.update P i R') i (P i) = P := by
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [Function.update, hji]
  have hSP2 := hSP (Function.update P i R') hP' i (P i)
    (by rw [hupd]; exact hP)
  have hnot_lt_R' : ¬ R'.lt w w' := by
    intro h
    apply hSP2
    refine ⟨w, ?_, ?_⟩
    · rw [hupd]; exact hwP
    intro a ha
    rw [winners_eq_singleton f hRes _ hP', Set.mem_singleton_iff] at ha
    subst ha
    simp only [Function.update_self]
    exact h
  by_cases hww' : w = w'
  · exact Or.inl hww'
  · exact Or.inr ⟨hnot_lt_PiI, hnot_lt_R'⟩

/-! ### Pareto property of `f`

If every voter strictly prefers `x` to `y`, then `y` is not the winner. -/

/-- A "hybrid" profile: Voters in `S` use `Q i`, others use `P i`. -/
noncomputable def hybridProfile (P Q : Profile Voter Alt) (S : Finset Voter) :
    Profile Voter Alt :=
  fun i => if i ∈ S then Q i else P i

omit [DecidableEq Alt] in
@[simp] lemma hybridProfile_empty (P Q : Profile Voter Alt) :
    hybridProfile P Q ∅ = P := by
  funext i
  simp [hybridProfile]

omit [DecidableEq Alt] in
lemma hybridProfile_univ [Fintype Voter] (P Q : Profile Voter Alt) :
    hybridProfile P Q Finset.univ = Q := by
  funext i
  simp [hybridProfile]

omit [DecidableEq Alt] in
lemma hybridProfile_insert (P Q : Profile Voter Alt) (S : Finset Voter)
    (i : Voter) (hi : i ∉ S) :
    hybridProfile P Q (insert i S) = Function.update (hybridProfile P Q S) i (Q i) := by
  classical
  funext j
  by_cases hij : j = i
  · subst hij
    simp [hybridProfile, Function.update]
  · simp [hybridProfile, Function.update, hij, Finset.mem_insert]

omit [DecidableEq Alt] in
/-- The hybrid profile lies in the universal domain. -/
lemma hybridProfile_mem_universalDomain (P Q : Profile Voter Alt) (S : Finset Voter) :
    hybridProfile P Q S ∈ universalDomain Voter Alt := Set.mem_univ _

omit [DecidableEq Alt] in
/-- The hybrid profile is strict whenever both inputs are. -/
lemma hybridProfile_isStrict {P Q : Profile Voter Alt}
    (hP : Profile.IsStrict P) (hQ : Profile.IsStrict Q) (S : Finset Voter) :
    Profile.IsStrict (hybridProfile P Q S) := by
  intro i
  simp only [hybridProfile]
  by_cases hiS : i ∈ S
  · simp only [hiS, ↓reduceIte]; exact hQ i
  · simp only [hiS, ↓reduceIte]; exact hP i

omit [DecidableEq Alt] in
/-- Variant: `hybridProfile P Q S` lies in `f.domain` when `P, Q ∈ f.domain`. -/
lemma hybridProfile_mem_domain
    {f : ChoiceFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt)
    {P Q : Profile Voter Alt} (hP : P ∈ f.domain) (hQ : Q ∈ f.domain)
    (S : Finset Voter) :
    hybridProfile P Q S ∈ f.domain := by
  rw [hDomEq]
  exact hybridProfile_isStrict (profile_isStrict_of_mem_domain hDomEq hP)
    (profile_isStrict_of_mem_domain hDomEq hQ) S

omit [DecidableEq Alt] in
/-- **Strict Maskin step.** If `w` is the winner of `f` on `P` and voter `i` switches to a
preference `R'` that ranks `w` strictly above every other alternative, then `w` remains the winner
after the switch. -/
lemma maskin_step_strict_top
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hSP : ChoiceFunction.StrategyProof f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (i : Voter) (R' : PreferenceRel Alt)
    (hP' : Function.update P i R' ∈ f.domain)
    (w : Alt) (hw : w ∈ f.winners P)
    (hStrict : ∀ a : Alt, a ≠ w → R'.lt w a) :
    chooseWinner f hRes (Function.update P i R') hP' = w := by
  have h := chooseWinner_eq_or_lt (f := f) hRes hSP hP i R' hP'
  set w' := chooseWinner f hRes (Function.update P i R') hP'
  have hwEq : chooseWinner f hRes P hP = w := by
    rw [chooseWinner_eq_iff]; exact hw
  rw [hwEq] at h
  rcases h with heq | ⟨_, hnotR'⟩
  · exact heq.symm
  · by_contra hne
    have hne' : w' ≠ w := hne
    exact hnotR' (hStrict w' hne')

omit [DecidableEq Alt] in
/-- For any strict profile `P` and alternative `x`, if every voter has `x` at the strict top (i.e.,
the profile is `fun i => moveToTop (P i) x`), then `x` is a winner of `f`. -/
lemma pareto_phase_x_at_top
    [Finite Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (x : Alt) :
    x ∈ f.winners (fun i => moveToTop (P i) x) := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  -- Maskin-step walk from a winning base profile `A` to `moveToTop R x` at every voter: lifting `x`
  -- to the strict top one voter at a time keeps `x` the winner. Used for both legs below.
  have walkToTop : ∀ (A R : Profile Voter Alt), A ∈ f.domain → R ∈ f.domain →
      x ∈ f.winners A → x ∈ f.winners (fun i => moveToTop (R i) x) := by
    intro A R hA_dom hR_dom hxA
    have hR_strict : Profile.IsStrict R := profile_isStrict_of_mem_domain hDomEq hR_dom
    set B : Profile Voter Alt := fun i => moveToTop (R i) x with hB_def
    have hB_strict : Profile.IsStrict B := fun i => (hR_strict i).moveToTop x
    have hB_dom : B ∈ f.domain := by rw [hDomEq]; exact hB_strict
    -- Each Maskin step replaces voter `i`'s preference with `B i = moveToTop (R i) x`.
    have hWalk : ∀ S : Finset Voter, x ∈ f.winners (hybridProfile A B S) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        rw [hybridProfile_empty]; exact hxA
      | insert i S hi IH =>
        have hS_dom : hybridProfile A B S ∈ f.domain :=
          hybridProfile_mem_domain hDomEq hA_dom hB_dom S
        rw [hybridProfile_insert _ _ _ _ hi]
        have hUpd_dom : Function.update (hybridProfile A B S) i (B i) ∈ f.domain := by
          rw [hDomEq]
          exact update_mem_strictDomain
            (hybridProfile_isStrict (profile_isStrict_of_mem_domain hDomEq hA_dom) hB_strict S) i
            (hB_strict i)
        have hStrict : ∀ a : Alt, a ≠ x → (B i).lt x a := fun a ha =>
          atTop_moveToTop (R i) x a ha
        have hEq := maskin_step_strict_top hRes hSP hS_dom i (B i) hUpd_dom x IH hStrict
        rw [chooseWinner_eq_iff] at hEq
        exact hEq
    have := hWalk Finset.univ
    rwa [hybridProfile_univ] at this
  -- Pull `x` to the top of a surjectivity witness `Q` (giving `Qstar`), then bridge to goal `P`.
  obtain ⟨Q, hQ_dom, hxQ⟩ := hSur x
  have hQ_strict : Profile.IsStrict Q := profile_isStrict_of_mem_domain hDomEq hQ_dom
  have hQstar_dom : (fun i => moveToTop (Q i) x) ∈ f.domain := by
    rw [hDomEq]; exact fun i => (hQ_strict i).moveToTop x
  have hxQstar : x ∈ f.winners (fun i => moveToTop (Q i) x) := walkToTop Q Q hQ_dom hQ_dom hxQ
  exact walkToTop _ P hQstar_dom hP hxQstar

omit [DecidableEq Alt] in
/-- **Pareto property (strict-domain form).** If every voter strictly prefers `x` to `y` in a
strict profile `P`, then `y` is not the winner of `f` on `P`. -/
lemma pareto_property
    [Finite Voter] [Nonempty Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (x y : Alt)
    (hxy : ∀ i, (P i).lt x y) : y ∉ f.winners P := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  have hP_strict : Profile.IsStrict P := profile_isStrict_of_mem_domain hDomEq hP
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Voter)
  have hxy_ne : x ≠ y := by
    intro heq; subst heq
    exact (P i₀).lt_irrefl _ (hxy i₀)
  set Pstar : Profile Voter Alt := fun i => moveToTop (P i) x
  have hPstar_strict : Profile.IsStrict Pstar := fun i => (hP_strict i).moveToTop x
  have hPstar_dom : Pstar ∈ f.domain := by rw [hDomEq]; exact hPstar_strict
  have hxPstar : x ∈ f.winners Pstar :=
    pareto_phase_x_at_top hRes hDomEq hSP hSur hP x
  have hWalk : ∀ S : Finset Voter,
      chooseWinner f hRes (hybridProfile Pstar P S)
        (hybridProfile_mem_domain hDomEq hPstar_dom hP S) ≠ y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hEq : chooseWinner f hRes (hybridProfile Pstar P ∅)
          (hybridProfile_mem_domain hDomEq hPstar_dom hP ∅) = x := by
        rw [chooseWinner_eq_iff, hybridProfile_empty]; exact hxPstar
      rw [hEq]; exact hxy_ne
    | insert k S hk IH =>
      set HS : Profile Voter Alt := hybridProfile Pstar P S with hHS_def
      have hHS_dom : HS ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hPstar_dom hP S
      -- Inserting `k` updates voter `k`'s preference from `Pstar k` to `P k`, so the winner of the
      -- enlarged hybrid is `z'`, the Maskin one-step image of the winner `z` on `HS`.
      have hHSinsert_eq : hybridProfile Pstar P (insert k S) = Function.update HS k (P k) :=
        hHS_def ▸ hybridProfile_insert _ _ _ _ hk
      have hUpd_dom : Function.update HS k (P k) ∈ f.domain := hHSinsert_eq ▸
        hybridProfile_mem_domain hDomEq hPstar_dom hP (insert k S)
      set z := chooseWinner f hRes HS hHS_dom with hz_def
      set z' := chooseWinner f hRes (Function.update HS k (P k)) hUpd_dom with hz'_def
      have hgoal_eq : chooseWinner f hRes (hybridProfile Pstar P (insert k S))
          (hybridProfile_mem_domain hDomEq hPstar_dom hP (insert k S)) = z' := by
        rw [hz'_def]; congr 1
      rw [hgoal_eq]
      have hz_ne_y : z ≠ y := IH
      have hHS_k : HS k = Pstar k := by
        simp [hHS_def, hybridProfile, hk]
      have hOr := chooseWinner_eq_or_lt (f := f) hRes hSP hHS_dom k (P k) hUpd_dom
      simp only [← hz_def, ← hz'_def] at hOr
      rcases hOr with heq | ⟨hnot1, hnot2⟩
      · rw [← heq]; exact hz_ne_y
      · intro hzy
        have hzz' : z ≠ z' := fun h => hz_ne_y (h ▸ hzy)
        have hHSk_strict : StrictPref (HS k) := by
          rw [hHS_k]
          exact hPstar_strict k
        have hPk_strict : StrictPref (P k) := hP_strict k
        have h1 : (HS k).lt z z' := by
          rcases (HS k).trichotomy z' z with h | h | h
          · exact absurd h hnot1
          · exact h
          · exact absurd ((hHSk_strict z' z h).symm) hzz'
        have h2 : (P k).lt z' z := by
          rcases (P k).trichotomy z z' with h | h | h
          · exact absurd h hnot2
          · exact h
          · exact absurd (hPk_strict z z' h) hzz'
        rw [hzy] at h1 h2
        rw [hHS_k] at h1
        by_cases hzx : z = x
        · rw [hzx] at h2
          exact (hxy k).2 h2.1
        · have hzy_pk : (P k).lt z y := by
            unfold PreferenceRel.lt at h1 ⊢
            rw [moveToTop_le_of_ne hzx hxy_ne.symm] at h1
            constructor
            · exact h1.1
            · intro hyz
              apply h1.2
              rw [moveToTop_le_of_ne hxy_ne.symm hzx]
              exact hyz
          exact hzy_pk.2 h2.1
  intro hy
  apply hWalk Finset.univ
  rw [chooseWinner_eq_iff, hybridProfile_univ]
  exact hy

/-! ### Lift winner is in the top pair -/

/-- **Lifted winner lies in `{x, y}`.** Under the lift profile `liftPair P x y`, every winner of
`f` belongs to `{x, y}`. -/
lemma winner_lift_in_pair
    [Finite Voter] [Nonempty Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    -- x ≠ y is part of the "pair" specification but the proof below derives its
    -- contradiction from w ≠ x and w ≠ y alone, without needing x ≠ y itself.
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (x y : Alt) (_hxy : x ≠ y) :
    f.winners (liftPair P x y) ⊆ {x, y} := by
  intro w hw
  by_contra hwOut
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hwOut
  push Not at hwOut
  obtain ⟨hwx, hwy⟩ := hwOut
  have hAll_xw : ∀ i, ((liftPair P x y) i).lt x w := by
    intro i
    exact liftPairOf_lt_top_outside hwx hwy
  have hLift_dom : liftPair P x y ∈ f.domain := liftPair_mem_domain hDomEq hP x y
  exact pareto_property hRes hDomEq hSP hSur hLift_dom x w hAll_xw hw

/-! ### The three-alternative lift

`liftTripleOf R u v w` puts `{u, v, w}` at the top of `R`, with their relative order matching
`R`. The original relative order is preserved (strictly below all three). This is used to establish
transitivity of the choice-function-induced social ranking on the strict domain. -/

/-- A preference relation that lifts the triple `{u, v, w}` to the top, preserving the relative
order on `{u, v, w}` from `R` and the relative order of all other pairs. -/
def liftTripleOf (R : PreferenceRel Alt) (u v w : Alt) : PreferenceRel Alt where
  le a b :=
    if a = u ∨ a = v ∨ a = w then
      if b = u ∨ b = v ∨ b = w then R.le a b else True
    else
      if b = u ∨ b = v ∨ b = w then False else R.le a b
  le_refl a := by
    by_cases ha : a = u ∨ a = v ∨ a = w
    all_goals simp only [ha, ↓reduceIte]; exact R.le_refl a
  le_trans a b c hab hbc := by
    by_cases ha : a = u ∨ a = v ∨ a = w
    · by_cases hb : b = u ∨ b = v ∨ b = w
      · by_cases hc : c = u ∨ c = v ∨ c = w
        · simp only [ha, hb, hc, if_true] at hab hbc ⊢
          exact R.le_trans a b c hab hbc
        · simp only [ha, hc, if_true, if_false]
      · by_cases hc : c = u ∨ c = v ∨ c = w
        · simp only [hb, hc, if_false, if_true] at hbc
        · simp only [ha, hc, if_true, if_false]
    · by_cases hb : b = u ∨ b = v ∨ b = w
      · simp only [ha, hb, if_false, if_true] at hab
      · by_cases hc : c = u ∨ c = v ∨ c = w
        · simp only [hb, hc, if_false, if_true] at hbc
        · simp only [ha, hb, hc, if_false] at hab hbc ⊢
          exact R.le_trans a b c hab hbc
  le_total a b := by
    by_cases ha : a = u ∨ a = v ∨ a = w
    · by_cases hb : b = u ∨ b = v ∨ b = w
      · simp only [ha, hb, if_true]
        exact R.le_total a b
      · left; simp only [ha, hb, if_true, if_false]
    · by_cases hb : b = u ∨ b = v ∨ b = w
      · right; simp only [ha, hb, if_true, if_false]
      · simp only [ha, hb, if_false]
        exact R.le_total a b

/-- The three-alternative lift of a profile. -/
def liftTriple (P : Profile Voter Alt) (u v w : Alt) : Profile Voter Alt :=
  fun i => liftTripleOf (P i) u v w

/-- Unfolding lemma for `liftTripleOf.le`. -/
@[simp] lemma liftTripleOf_le_iff (R : PreferenceRel Alt) (u v w a b : Alt) :
    (liftTripleOf R u v w).le a b ↔
      (if a = u ∨ a = v ∨ a = w then
        if b = u ∨ b = v ∨ b = w then R.le a b else True
      else
        if b = u ∨ b = v ∨ b = w then False else R.le a b) := Iff.rfl

/-- In the triple lift, members of the top triple are weakly above non-members. -/
lemma liftTripleOf_le_top_outside {R : PreferenceRel Alt} {u v w a b : Alt}
    (ha : a = u ∨ a = v ∨ a = w) (hb : ¬ (b = u ∨ b = v ∨ b = w)) :
    (liftTripleOf R u v w).le a b := by
  simp [liftTripleOf_le_iff, ha, hb]

/-- In the triple lift, non-members are not weakly above top-triple members. -/
lemma liftTripleOf_not_le_outside_top {R : PreferenceRel Alt} {u v w a b : Alt}
    (ha : ¬ (a = u ∨ a = v ∨ a = w)) (hb : b = u ∨ b = v ∨ b = w) :
    ¬ (liftTripleOf R u v w).le a b := by
  simp [liftTripleOf_le_iff, ha, hb]

/-- In the triple lift, every top member is strictly above any alternative outside the triple. -/
lemma liftTripleOf_lt_top_outside {R : PreferenceRel Alt} {u v w a b : Alt}
    (ha : a = u ∨ a = v ∨ a = w) (hb : ¬ (b = u ∨ b = v ∨ b = w)) :
    (liftTripleOf R u v w).lt a b := by
  refine ⟨?_, ?_⟩
  · exact liftTripleOf_le_top_outside ha hb
  · exact liftTripleOf_not_le_outside_top hb ha

/-- The relative order on the top triple matches `R`. -/
lemma liftTripleOf_le_top {R : PreferenceRel Alt} {u v w a b : Alt}
    (ha : a = u ∨ a = v ∨ a = w) (hb : b = u ∨ b = v ∨ b = w) :
    (liftTripleOf R u v w).le a b ↔ R.le a b := by
  simp [liftTripleOf_le_iff, ha, hb]

/-- The strict order on the top triple matches `R`. -/
lemma liftTripleOf_lt_top {R : PreferenceRel Alt} {u v w a b : Alt}
    (ha : a = u ∨ a = v ∨ a = w) (hb : b = u ∨ b = v ∨ b = w) :
    (liftTripleOf R u v w).lt a b ↔ R.lt a b := by
  unfold PreferenceRel.lt
  rw [liftTripleOf_le_top ha hb, liftTripleOf_le_top hb ha]

/-- `liftTripleOf` preserves strictness. -/
lemma StrictPref.liftTripleOf {R : PreferenceRel Alt} (h : StrictPref R) (u v w : Alt) :
    StrictPref (liftTripleOf R u v w) := by
  intro a b hab
  obtain ⟨h1, h2⟩ := hab
  rw [liftTripleOf_le_iff] at h1 h2
  by_cases ha : a = u ∨ a = v ∨ a = w
  · by_cases hb : b = u ∨ b = v ∨ b = w
    · simp only [ha, hb, if_true] at h1 h2
      exact h a b ⟨h1, h2⟩
    · simp only [ha, hb, if_true, if_false] at h2
  · by_cases hb : b = u ∨ b = v ∨ b = w
    · simp only [ha, hb, if_true, if_false] at h1
    · simp only [ha, hb, if_false] at h1 h2
      exact h a b ⟨h1, h2⟩

omit [DecidableEq Voter] in
/-- `liftTriple` preserves strictness pointwise. -/
lemma liftTriple_isStrict {P : Profile Voter Alt} (hP : Profile.IsStrict P) (u v w : Alt) :
    Profile.IsStrict (liftTriple P u v w) := fun i => (hP i).liftTripleOf u v w

omit [DecidableEq Voter] in
/-- The lift `liftTriple P u v w` lies in `f.domain` whenever `P` does. -/
lemma liftTriple_mem_domain
    {f : ChoiceFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt) {P : Profile Voter Alt}
    (hP : P ∈ f.domain) (u v w : Alt) :
    liftTriple P u v w ∈ f.domain := by
  rw [hDomEq]
  exact liftTriple_isStrict (profile_isStrict_of_mem_domain hDomEq hP) u v w

/-! ### Triple Pareto and the bridge to pair lifts -/

/-- **Triple Pareto.** Under the triple lift, every winner lies in `{u, v, w}`. -/
lemma winner_liftTriple_in_triple
    [Finite Voter] [Nonempty Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (u v w : Alt) :
    f.winners (liftTriple P u v w) ⊆ ({u, v, w} : Set Alt) := by
  intro a ha
  by_contra hOut
  have hOut' : ¬ (a = u ∨ a = v ∨ a = w) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hOut
  have hAll_ua : ∀ i, ((liftTriple P u v w) i).lt u a := by
    intro i
    exact liftTripleOf_lt_top_outside (Or.inl rfl) hOut'
  have hLift_dom : liftTriple P u v w ∈ f.domain :=
    liftTriple_mem_domain hDomEq hP u v w
  exact pareto_property hRes hDomEq hSP hSur hLift_dom u a hAll_ua ha

/-- **Bridge lemma.** If `{a, b} ⊆ {u, v, w}`, `a ≠ b`, and the winner of `f` on
`liftTriple P u v w` lies in `{a, b}`, then the winner of `f` on `liftPair P a b` equals the winner
of `f` on `liftTriple P u v w`. -/
lemma chooseWinner_liftPair_eq_of_liftTriple_in_pair
    [Finite Voter] [Nonempty Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (u v w a b : Alt)
    (ha : a = u ∨ a = v ∨ a = w) (hb : b = u ∨ b = v ∨ b = w) (hab : a ≠ b)
    (hWin : chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = a ∨
            chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = b) :
    chooseWinner f hRes (liftPair P a b) (liftPair_mem_domain hDomEq hP a b) =
      chooseWinner f hRes (liftTriple P u v w)
        (liftTriple_mem_domain hDomEq hP u v w) := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  have hP_strict : Profile.IsStrict P := profile_isStrict_of_mem_domain hDomEq hP
  have hLP_strict : Profile.IsStrict (liftPair P a b) := liftPair_isStrict hP_strict a b
  have hLT_strict : Profile.IsStrict (liftTriple P u v w) :=
    liftTriple_isStrict hP_strict u v w
  set LP : Profile Voter Alt := liftPair P a b with hLP_def
  set LT : Profile Voter Alt := liftTriple P u v w with hLT_def
  have hLP_dom : LP ∈ f.domain := liftPair_mem_domain hDomEq hP a b
  have hLT_dom : LT ∈ f.domain := liftTriple_mem_domain hDomEq hP u v w
  set L := chooseWinner f hRes LT hLT_dom with hL_def
  have hL_in_pair : L = a ∨ L = b := by rw [hL_def] at hWin; exact hWin
  have ha' : a = u ∨ a = v ∨ a = w := ha
  have hb' : b = u ∨ b = v ∨ b = w := hb
  have hWalk : ∀ S : Finset Voter,
      L = chooseWinner f hRes (hybridProfile LT LP S)
        (hybridProfile_mem_domain hDomEq hLT_dom hLP_dom S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have heq : hybridProfile LT LP ∅ = LT := hybridProfile_empty _ _
      symm
      rw [chooseWinner_eq_iff, heq]
      rw [hL_def]; exact chooseWinner_mem f hRes LT hLT_dom
    | insert k S hk IH =>
      set H_S : Profile Voter Alt := hybridProfile LT LP S
      have hH_S_dom : H_S ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hLT_dom hLP_dom S
      set H_insert : Profile Voter Alt := hybridProfile LT LP (insert k S)
      have hH_insert_eq : H_insert = Function.update H_S k (LP k) :=
        hybridProfile_insert _ _ _ _ hk
      have hH_insert_dom : H_insert ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hLT_dom hLP_dom (insert k S)
      have hUpd_dom : Function.update H_S k (LP k) ∈ f.domain := by
        rw [← hH_insert_eq]; exact hH_insert_dom
      have hChoose_eq :
          chooseWinner f hRes (Function.update H_S k (LP k)) hUpd_dom =
          chooseWinner f hRes H_insert hH_insert_dom := by
        congr 1; exact hH_insert_eq.symm
      have hOr := chooseWinner_eq_or_lt (f := f) hRes hSP hH_S_dom k (LP k) hUpd_dom
      simp only at hOr
      rw [hChoose_eq] at hOr
      rw [← IH] at hOr
      obtain ⟨z', hz'_def⟩ : ∃ z', chooseWinner f hRes H_insert hH_insert_dom = z' :=
        ⟨_, rfl⟩
      rw [hz'_def] at hOr
      rw [show
        chooseWinner f hRes (hybridProfile LT LP (insert k S))
          (hybridProfile_mem_domain hDomEq hLT_dom hLP_dom (insert k S)) =
        chooseWinner f hRes H_insert hH_insert_dom from rfl,
        hz'_def]
      have hHS_k : H_S k = LT k := by simp [H_S, hybridProfile, hk]
      rcases hOr with heq | ⟨hnot1, hnot2⟩
      · exact heq
      · by_cases hLz' : L = z'
        · exact hLz'
        exfalso
        have hz'_mem : z' ∈ f.winners H_insert := by
          rw [← hz'_def]; exact chooseWinner_mem f hRes _ _
        have hH_insert_in_triple : f.winners H_insert ⊆ ({u, v, w} : Set Alt) := by
          intro c hc
          by_contra hcOut
          have hcOut' : ¬ (c = u ∨ c = v ∨ c = w) := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcOut
          have hca : c ≠ a := by
            intro hh; subst hh; exact hcOut' ha
          have hcb : c ≠ b := by
            intro hh; subst hh; exact hcOut' hb
          have hAll : ∀ i, (H_insert i).lt a c := by
            intro i
            by_cases hi : i ∈ insert k S
            · have hH_i : H_insert i = LP i := by
                simp [H_insert, hybridProfile, hi]
              rw [hH_i]
              exact liftPairOf_lt_top_outside hca hcb
            · have hH_i : H_insert i = LT i := by
                simp [H_insert, hybridProfile, hi]
              rw [hH_i]
              exact liftTripleOf_lt_top_outside ha hcOut'
          exact pareto_property hRes hDomEq hSP hSur hH_insert_dom a c hAll hc
        have hz'_or : z' = u ∨ z' = v ∨ z' = w := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
            hH_insert_in_triple hz'_mem
        have hLTk_strict : StrictPref (LT k) := hLT_strict k
        have hLPk_strict : StrictPref (LP k) := hLP_strict k
        · have h1 : (LT k).lt L z' := by
            rcases (LT k).trichotomy z' L with h | h | h
            · rw [← hHS_k] at h; exact absurd h hnot1
            · exact h
            exact absurd ((hLTk_strict z' L h).symm) hLz'
          have h2 : (LP k).lt z' L := by
            rcases (LP k).trichotomy L z' with h | h | h
            · exact absurd h hnot2
            · exact h
            · exact absurd (hLPk_strict L z' h) hLz'
          have hL_in_uvw : L = u ∨ L = v ∨ L = w := by
            rcases hL_in_pair with hLa | hLb
            · rw [hLa]; exact ha
            · rw [hLb]; exact hb
          rw [show LT k = liftTripleOf (P k) u v w from rfl,
              liftTripleOf_lt_top hL_in_uvw hz'_or] at h1
          have hL_in_ab : L = a ∨ L = b := hL_in_pair
          rcases hL_in_pair with hLa | hLb
          · have hz'a : z' ≠ a := by
              intro h; apply hLz'; rw [hLa, h]
            rw [hLa] at h1
            rw [show LP k = liftPairOf (P k) a b from rfl, hLa] at h2
            by_cases hz'b : z' = b
            · rw [hz'b] at h1 h2
              rw [liftPairOf_lt_yx] at h2
              exact h2.2 h1.1
            · have hz'OutPair : ¬ (z' = a ∨ z' = b) := by
                rintro (h | h); exacts [hz'a h, hz'b h]
              have hContra : ¬ (liftPairOf (P k) a b).le z' a :=
                liftPairOf_not_le_outside_top hz'OutPair (Or.inl rfl)
              exact hContra h2.1
          · have hz'b : z' ≠ b := by
              intro h; apply hLz'; rw [hLb, h]
            rw [hLb] at h1
            rw [show LP k = liftPairOf (P k) a b from rfl, hLb] at h2
            by_cases hz'a : z' = a
            · rw [hz'a] at h1 h2
              rw [liftPairOf_lt_xy] at h2
              exact h2.2 h1.1
            · have hz'OutPair : ¬ (z' = a ∨ z' = b) := by
                rintro (h | h); exacts [hz'a h, hz'b h]
              have hContra : ¬ (liftPairOf (P k) a b).le z' b :=
                liftPairOf_not_le_outside_top hz'OutPair (Or.inr rfl)
              exact hContra h2.1
  have hUniv := hWalk Finset.univ
  have hUnivProf : hybridProfile LT LP Finset.univ = LP := hybridProfile_univ _ _
  have hLP_choose : chooseWinner f hRes LP hLP_dom = L := by
    have hMem : L ∈ f.winners LP := by
      have : L ∈ f.winners (hybridProfile LT LP Finset.univ) := by
        rw [hUniv]; exact chooseWinner_mem f hRes _ _
      rwa [hUnivProf] at this
    exact hRes LP hLP_dom (chooseWinner_mem f hRes LP hLP_dom) hMem
  rw [show (liftPair_mem_domain hDomEq hP a b) = hLP_dom from rfl]
  rw [hLP_choose]

/-! ### The induced welfare function -/

/-- The induced binary social ranking for a strict profile `P`: Society weakly prefers `u` to `v`
iff `u = v` or `u` is the winner of `f` on the lift profile `liftPair P u v`. -/
noncomputable def aggregateOfChoiceFunction
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    (f : ChoiceFunction Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    (P : Profile Voter Alt) : PreferenceRel Alt :=
  haveI : Decidable (P ∈ f.domain) := Classical.dec _
  if hP : P ∈ f.domain then
    { le := fun u v => u = v ∨ u ∈ f.winners (liftPair P u v)
      le_refl := fun u => Or.inl rfl
      le_trans := fun u v w huv hvw => by
        by_cases huv_eq : u = v
        · subst huv_eq
          rcases hvw with hvw_eq | hvw_win
          · exact Or.inl hvw_eq
          · exact Or.inr hvw_win
        by_cases hvw_eq : v = w
        · subst hvw_eq
          exact huv
        by_cases huw_eq : u = w
        · exact Or.inl huw_eq
        rcases huv with huv_or | huv_win
        · exact absurd huv_or huv_eq
        rcases hvw with hvw_or | hvw_win
        · exact absurd hvw_or hvw_eq
        right
        have hLT_dom : liftTriple P u v w ∈ f.domain :=
          liftTriple_mem_domain hDomEq hP u v w
        have hTriple_subset : f.winners (liftTriple P u v w) ⊆ ({u, v, w} : Set Alt) :=
          winner_liftTriple_in_triple hRes hDomEq hSP hSur hP u v w
        set t := chooseWinner f hRes (liftTriple P u v w) hLT_dom with ht_def
        have ht_or : t = u ∨ t = v ∨ t = w := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
            hTriple_subset (chooseWinner_mem f hRes _ hLT_dom)
        have hu_in : u = u ∨ u = v ∨ u = w := Or.inl rfl
        have hv_in : v = u ∨ v = v ∨ v = w := Or.inr (Or.inl rfl)
        have hw_in : w = u ∨ w = v ∨ w = w := Or.inr (Or.inr rfl)
        have hcwLPuv : chooseWinner f hRes (liftPair P u v)
            (liftPair_mem_domain hDomEq hP u v) = u := by
          rw [chooseWinner_eq_iff]; exact huv_win
        have hcwLPvw : chooseWinner f hRes (liftPair P v w)
            (liftPair_mem_domain hDomEq hP v w) = v := by
          rw [chooseWinner_eq_iff]; exact hvw_win
        rcases ht_or with htu | htv | htw
        · have hWin_uw : chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = u ∨
              chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = w := by
            rw [← ht_def]; left; exact htu
          have hcwLPuw : chooseWinner f hRes (liftPair P u w)
              (liftPair_mem_domain hDomEq hP u w) = t :=
            chooseWinner_liftPair_eq_of_liftTriple_in_pair hRes hDomEq hSP hSur hP
              u v w u w hu_in hw_in huw_eq hWin_uw
          rw [chooseWinner_eq_iff] at hcwLPuw
          rw [htu] at hcwLPuw
          exact hcwLPuw
        · exfalso
          have hWin_uv : chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = u ∨
              chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = v := by
            rw [← ht_def]; right; exact htv
          have hcwLPuv' : chooseWinner f hRes (liftPair P u v)
              (liftPair_mem_domain hDomEq hP u v) = t :=
            chooseWinner_liftPair_eq_of_liftTriple_in_pair hRes hDomEq hSP hSur hP
              u v w u v hu_in hv_in huv_eq hWin_uv
          rw [hcwLPuv] at hcwLPuv'
          rw [htv] at hcwLPuv'
          exact huv_eq hcwLPuv'
        · exfalso
          have hWin_vw : chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = v ∨
              chooseWinner f hRes (liftTriple P u v w)
              (liftTriple_mem_domain hDomEq hP u v w) = w := by
            rw [← ht_def]; right; exact htw
          have hcwLPvw' : chooseWinner f hRes (liftPair P v w)
              (liftPair_mem_domain hDomEq hP v w) = t :=
            chooseWinner_liftPair_eq_of_liftTriple_in_pair hRes hDomEq hSP hSur hP
              u v w v w hv_in hw_in hvw_eq hWin_vw
          rw [hcwLPvw] at hcwLPvw'
          rw [htw] at hcwLPvw'
          exact hvw_eq hcwLPvw'
      le_total := fun u v => by
        by_cases huv : u = v
        · exact Or.inl (Or.inl huv)
        · have hLift_dom : liftPair P u v ∈ f.domain := liftPair_mem_domain hDomEq hP u v
          have hSubset : f.winners (liftPair P u v) ⊆ {u, v} :=
            winner_lift_in_pair hRes hDomEq hSP hSur hP u v huv
          obtain ⟨z, hz⟩ := f.winners_nonempty (liftPair P u v) hLift_dom
          have hz_pair := hSubset hz
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_pair
          have hSym : liftPair P v u = liftPair P u v := liftPair_swap P u v
          rcases hz_pair with hzu | hzv
          · rw [hzu] at hz
            exact Or.inl (Or.inr hz)
          · rw [hzv] at hz
            right; right
            rw [hSym]
            exact hz }
  else
    strictRefPref

/-- Unfolding lemma for `aggregateOfChoiceFunction` when `P ∈ f.domain`. -/
lemma aggregateOfChoiceFunction_le
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P : Profile Voter Alt} (hP : P ∈ f.domain) (u v : Alt) :
    (aggregateOfChoiceFunction f hRes hDomEq hSP hSur P).le u v ↔
      u = v ∨ u ∈ f.winners (liftPair P u v) := by
  unfold aggregateOfChoiceFunction
  classical
  simp [hP]

/-- The induced welfare function. -/
noncomputable def welfareFunctionOfChoiceFunction
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    (f : ChoiceFunction Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f) :
    WelfareFunction Voter Alt where
  domain := f.domain
  aggregate := aggregateOfChoiceFunction f hRes hDomEq hSP hSur

/-! ### Pareto and IIA on the induced welfare function -/

/-- The induced welfare function `welfareFunctionOfChoiceFunction f` satisfies Weak Pareto. -/
lemma weakPareto_welfareFunctionOfChoiceFunction
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f) :
    WelfareFunction.WeakPareto (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur) := by
  intro P hP x y hxy
  have hP' : P ∈ f.domain := hP
  have hxy_ne : x ≠ y := by
    intro h; subst h
    obtain ⟨i⟩ := (inferInstance : Nonempty Voter)
    exact (P i).lt_irrefl _ (hxy i)
  refine ⟨?_, ?_⟩
  · rw [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
      aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl,
      aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP']
    right
    have hLift_dom : liftPair P x y ∈ f.domain := liftPair_mem_domain hDomEq hP' x y
    have hSubset : f.winners (liftPair P x y) ⊆ {x, y} :=
      winner_lift_in_pair hRes hDomEq hSP hSur hP' x y hxy_ne
    obtain ⟨z, hz⟩ := f.winners_nonempty (liftPair P x y) hLift_dom
    have hz_pair := hSubset hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz_pair
    rcases hz_pair with hzx | hzy
    · rw [hzx] at hz; exact hz
    · exfalso
      rw [hzy] at hz
      have hAll_xy : ∀ i, ((liftPair P x y) i).lt x y := fun i => by
        rw [liftPair, liftPairOf_lt_xy]; exact hxy i
      exact pareto_property hRes hDomEq hSP hSur hLift_dom x y hAll_xy hz
  · intro h
    rw [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
      aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl] at h
    rw [aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP'] at h
    rcases h with hyx | hy
    · exact hxy_ne hyx.symm
    · have hLift_dom : liftPair P y x ∈ f.domain := liftPair_mem_domain hDomEq hP' y x
      have hAll_xy : ∀ i, ((liftPair P y x) i).lt x y := fun i => by
        rw [liftPair, liftPairOf_lt_yx]; exact hxy i
      exact pareto_property hRes hDomEq hSP hSur hLift_dom x y hAll_xy hy

/-- **Pairwise agreement preserves lift winners.** If `P, Q ∈ f.domain` agree on `(x, y)`
voter-by-voter, then `f.winners (liftPair P x y) = f.winners (liftPair Q x y)`. -/
lemma winners_liftPair_eq_of_pair_agree
    [Finite Voter] [Nonempty Voter]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    {P Q : Profile Voter Alt} (hP : P ∈ f.domain) (hQ : Q ∈ f.domain) (x y : Alt)
    (hxy_ne : x ≠ y)
    (hpair : ∀ i, ((P i).le x y ↔ (Q i).le x y) ∧ ((P i).le y x ↔ (Q i).le y x)) :
    f.winners (liftPair P x y) = f.winners (liftPair Q x y) := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  have hP_strict : Profile.IsStrict P := profile_isStrict_of_mem_domain hDomEq hP
  have hQ_strict : Profile.IsStrict Q := profile_isStrict_of_mem_domain hDomEq hQ
  have hLiftP_strict : Profile.IsStrict (liftPair P x y) := liftPair_isStrict hP_strict x y
  have hLiftQ_strict : Profile.IsStrict (liftPair Q x y) := liftPair_isStrict hQ_strict x y
  have hLiftP_dom : liftPair P x y ∈ f.domain := liftPair_mem_domain hDomEq hP x y
  have hLiftQ_dom : liftPair Q x y ∈ f.domain := liftPair_mem_domain hDomEq hQ x y
  obtain ⟨L, hL_eq⟩ : ∃ L, L = chooseWinner f hRes (liftPair P x y) hLiftP_dom :=
    ⟨_, rfl⟩
  have hL_mem : L ∈ f.winners (liftPair P x y) := by
    rw [hL_eq]; exact chooseWinner_mem f hRes _ hLiftP_dom
  have hL_in_pair : L ∈ ({x, y} : Set Alt) :=
    winner_lift_in_pair hRes hDomEq hSP hSur hP x y hxy_ne hL_mem
  have hWalk : ∀ S : Finset Voter,
      L = chooseWinner f hRes (hybridProfile (liftPair P x y) (liftPair Q x y) S)
        (hybridProfile_mem_domain hDomEq hLiftP_dom hLiftQ_dom S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have heq : hybridProfile (liftPair P x y) (liftPair Q x y) ∅ = liftPair P x y :=
        hybridProfile_empty _ _
      have hMem : L ∈ f.winners (hybridProfile (liftPair P x y) (liftPair Q x y) ∅) := by
        rw [heq]; exact hL_mem
      have h_dom := hybridProfile_mem_domain hDomEq hLiftP_dom hLiftQ_dom (∅ : Finset Voter)
      symm
      rw [chooseWinner_eq_iff]
      exact hMem
    | insert k S hk IH =>
      set H_S : Profile Voter Alt := hybridProfile (liftPair P x y) (liftPair Q x y) S
        with hH_S_def
      have hH_S_dom : H_S ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hLiftP_dom hLiftQ_dom S
      set H_insert : Profile Voter Alt :=
        hybridProfile (liftPair P x y) (liftPair Q x y) (insert k S) with hH_insert_def
      have hH_insert_eq : H_insert = Function.update H_S k (liftPair Q x y k) := by
        rw [hH_insert_def, hH_S_def]
        exact hybridProfile_insert _ _ _ _ hk
      have hH_insert_dom : H_insert ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hLiftP_dom hLiftQ_dom (insert k S)
      have hUpd_dom : Function.update H_S k (liftPair Q x y k) ∈ f.domain := by
        rw [← hH_insert_eq]; exact hH_insert_dom
      have hChoose_eq :
          chooseWinner f hRes (Function.update H_S k (liftPair Q x y k)) hUpd_dom =
          chooseWinner f hRes H_insert hH_insert_dom := by
        congr 1; exact hH_insert_eq.symm
      have hOr := chooseWinner_eq_or_lt (f := f) hRes hSP hH_S_dom k (liftPair Q x y k) hUpd_dom
      simp only at hOr
      rw [hChoose_eq] at hOr
      rw [← IH] at hOr
      obtain ⟨z', hz'_def⟩ : ∃ z', chooseWinner f hRes H_insert hH_insert_dom = z' := ⟨_, rfl⟩
      rw [hz'_def] at hOr
      rw [show
        chooseWinner f hRes (hybridProfile (liftPair P x y) (liftPair Q x y) (insert k S))
          (hybridProfile_mem_domain hDomEq hLiftP_dom hLiftQ_dom (insert k S)) =
        chooseWinner f hRes H_insert hH_insert_dom from rfl,
        hz'_def]
      have hHS_k : H_S k = liftPair P x y k := by
        simp [hH_S_def, hybridProfile, hk]
      rcases hOr with heq | ⟨hnot1, hnot2⟩
      · exact heq
      · have hz'_mem : z' ∈ f.winners H_insert := by
          rw [← hz'_def]; exact chooseWinner_mem f hRes _ _
        have hH_insert_in_pair : f.winners H_insert ⊆ {x, y} := by
          intro w hw
          by_contra hwOut
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hwOut
          push Not at hwOut
          obtain ⟨hwx, hwy⟩ := hwOut
          -- Every voter's preference in `H_insert` is some `liftPairOf · x y`, so `x` sits
          -- strictly above the outside alternative `w` regardless of which source the voter uses.
          have hAll_xw : ∀ i, (H_insert i).lt x w := by
            intro i
            have hI : H_insert i = liftPairOf ((if i ∈ insert k S then Q else P) i) x y := by
              by_cases hi : i ∈ insert k S <;> simp [hH_insert_def, hybridProfile, liftPair, hi]
            rw [hI]; exact liftPairOf_lt_top_outside hwx hwy
          exact pareto_property hRes hDomEq hSP hSur hH_insert_dom x w hAll_xw hw
        have hz'_in_pair : z' ∈ ({x, y} : Set Alt) := hH_insert_in_pair hz'_mem
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'_in_pair
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hL_in_pair
        by_cases hLz' : L = z'
        · exact hLz'
        · exfalso
          have hHSk_strict : StrictPref (H_S k) := by
            rw [hHS_k]; exact hLiftP_strict k
          have hQk_strict : StrictPref (liftPair Q x y k) := hLiftQ_strict k
          have h1 : (H_S k).lt L z' := by
            rcases (H_S k).trichotomy z' L with h | h | h
            · exact absurd h hnot1
            · exact h
            · exact absurd (hHSk_strict z' L h) (Ne.symm hLz')
          have h2 : (liftPair Q x y k).lt z' L := by
            rcases (liftPair Q x y k).trichotomy L z' with h | h | h
            · exact absurd h hnot2
            · exact h
            · exact absurd (hQk_strict L z' h) hLz'
          rw [hHS_k] at h1
          rcases hL_in_pair with hLx | hLy
          · rcases hz'_in_pair with hz'x | hz'y
            · exact hLz' (hLx.trans hz'x.symm)
            · rw [hLx, hz'y, liftPair, liftPairOf_lt_xy] at h1
              rw [hLx, hz'y, liftPair, liftPairOf_lt_yx] at h2
              have hP_le : (P k).le x y := h1.1
              have hQ_le : (Q k).le x y := (hpair k).1.mp hP_le
              exact h2.2 hQ_le
          · rcases hz'_in_pair with hz'x | hz'y
            · rw [hLy, hz'x, liftPair, liftPairOf_lt_yx] at h1
              rw [hLy, hz'x, liftPair, liftPairOf_lt_xy] at h2
              have hP_le : (P k).le y x := h1.1
              have hQ_le : (Q k).le y x := (hpair k).2.mp hP_le
              exact h2.2 hQ_le
            · exact hLz' (hLy.trans hz'y.symm)
  have hLeft : f.winners (liftPair P x y) = {L} := by
    rw [winners_eq_singleton f hRes _ hLiftP_dom, ← hL_eq]
  have hUniv := hWalk Finset.univ
  have hRight : f.winners (liftPair Q x y) = {L} := by
    have hUnivProf : hybridProfile (liftPair P x y) (liftPair Q x y) Finset.univ = liftPair Q x y :=
      hybridProfile_univ _ _
    have hMem : L ∈ f.winners (liftPair Q x y) := by
      have : L ∈ f.winners (hybridProfile (liftPair P x y) (liftPair Q x y) Finset.univ) := by
        rw [hUniv]; exact chooseWinner_mem f hRes _ _
      rwa [hUnivProf] at this
    have hCW_eq : chooseWinner f hRes (liftPair Q x y) hLiftQ_dom = L :=
      hRes (liftPair Q x y) hLiftQ_dom (chooseWinner_mem f hRes _ _) hMem
    rw [winners_eq_singleton f hRes _ hLiftQ_dom, hCW_eq]
  rw [hLeft, hRight]

/-- The induced welfare function `welfareFunctionOfChoiceFunction f` satisfies IIA. -/
lemma iia_welfareFunctionOfChoiceFunction
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f) :
    WelfareFunction.IIA (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur) := by
  intro P Q hP hQ x y hpair
  have hP' : P ∈ f.domain := hP
  have hQ' : Q ∈ f.domain := hQ
  by_cases hxy_ne : x = y
  · subst hxy_ne
    refine ⟨?_, ?_⟩ <;>
      exact Iff.intro
        (fun _ => ((welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate Q).le_refl x)
        (fun _ => ((welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P).le_refl x)
  · have hWin_xy_eq : f.winners (liftPair P x y) = f.winners (liftPair Q x y) :=
      winners_liftPair_eq_of_pair_agree hRes hDomEq hSP hSur hP' hQ' x y hxy_ne hpair
    have hpair_yx : ∀ i, ((P i).le y x ↔ (Q i).le y x) ∧ ((P i).le x y ↔ (Q i).le x y) :=
      fun i => ⟨(hpair i).2, (hpair i).1⟩
    have hWin_yx_eq : f.winners (liftPair P y x) = f.winners (liftPair Q y x) :=
      winners_liftPair_eq_of_pair_agree hRes hDomEq hSP hSur hP' hQ' y x (Ne.symm hxy_ne) hpair_yx
    refine ⟨?_, ?_⟩
    · simp only [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
        aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl,
        show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate Q =
        aggregateOfChoiceFunction f hRes hDomEq hSP hSur Q from rfl]
      rw [aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP',
          aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hQ']
      rw [hWin_xy_eq]
    · simp only [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
        aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl,
        show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate Q =
        aggregateOfChoiceFunction f hRes hDomEq hSP hSur Q from rfl]
      rw [aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP',
          aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hQ']
      rw [hWin_yx_eq]

/-! ### Lifting the dictator back

A welfare function dictator `i` for `welfareFunctionOfChoiceFunction f` is also a
choice-function dictator for `f`. -/

/-- The substantive half of the dictator transfer: If `i` is a welfare-function dictator for
`welfareFunctionOfChoiceFunction f`, then on every admissible profile every winner is `i`-top
(weakly preferred by `i` to every alternative). The full equality `IsDictator` follows by
`choiceFunction_dictator_of_welfareFunction_dictator`, which adds the reverse inclusion using
resoluteness and strictness. -/
lemma choiceFunction_winner_isTop_of_welfareFunction_dictator
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    (i : Voter)
    (hi : WelfareFunction.IsDictator (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur) i) :
      ∀ P ∈ f.domain, ∀ w ∈ f.winners P, ∀ a : Alt, (P i).le w a := by
  classical
  intro P hP w hw a
  by_contra hContra
  have hP_strict : Profile.IsStrict P := profile_isStrict_of_mem_domain hDomEq hP
  have hai_le : (P i).le a w := by
    rcases (P i).le_total w a with h | h
    · exact absurd h hContra
    · exact h
  have hai_lt : (P i).lt a w := ⟨hai_le, hContra⟩
  have haw_ne : a ≠ w := by
    intro h; subst h; exact hContra ((P i).le_refl _)
  have hSocLt : ((welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P).lt a w :=
    hi P hP a w hai_lt
  have hLift_dom : liftPair P a w ∈ f.domain := liftPair_mem_domain hDomEq hP a w
  have h_a_in : a ∈ f.winners (liftPair P a w) := by
    have h1 : ((welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P).le a w :=
      hSocLt.1
    rw [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
      aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl] at h1
    rw [aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP] at h1
    rcases h1 with hEq | h
    · exact absurd hEq haw_ne
    · exact h
  have h_w_not : w ∉ f.winners (liftPair P a w) := by
    intro hw_in
    apply hSocLt.2
    rw [show (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).aggregate P =
      aggregateOfChoiceFunction f hRes hDomEq hSP hSur P from rfl]
    rw [aggregateOfChoiceFunction_le hRes hDomEq hSP hSur hP]
    right
    rwa [liftPair_swap]
  have h_cw_lift_a : chooseWinner f hRes (liftPair P a w) hLift_dom = a := by
    rw [chooseWinner_eq_iff]; exact h_a_in
  have hWalk : ∀ S : Finset Voter,
      w ∈ f.winners (hybridProfile P (liftPair P a w) S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [hybridProfile_empty]; exact hw
    | insert k S hk IH =>
      set H_S : Profile Voter Alt := hybridProfile P (liftPair P a w) S
      have hLift_strict : Profile.IsStrict (liftPair P a w) := liftPair_isStrict hP_strict a w
      have hH_S_dom : H_S ∈ f.domain :=
        hybridProfile_mem_domain hDomEq hP hLift_dom S
      have hH_insert_eq : hybridProfile P (liftPair P a w) (insert k S) =
          Function.update H_S k (liftPair P a w k) := by
        exact hybridProfile_insert _ _ _ _ hk
      rw [hH_insert_eq]
      have hUpd_dom : Function.update H_S k (liftPair P a w k) ∈ f.domain := by
        rw [hDomEq]
        exact update_mem_strictDomain
          (by rw [hDomEq] at hH_S_dom; exact hH_S_dom) k (hLift_strict k)
      have hOr := chooseWinner_eq_or_lt (f := f) hRes hSP hH_S_dom k (liftPair P a w k) hUpd_dom
      simp only at hOr
      have hCW_S : chooseWinner f hRes H_S hH_S_dom = w := by
        rw [chooseWinner_eq_iff]; exact IH
      rw [hCW_S] at hOr
      obtain ⟨z', hz'_def⟩ : ∃ z',
          chooseWinner f hRes (Function.update H_S k (liftPair P a w k)) hUpd_dom = z' :=
        ⟨_, rfl⟩
      rw [hz'_def] at hOr
      have hz'_mem : z' ∈ f.winners (Function.update H_S k (liftPair P a w k)) := by
        rw [← hz'_def]; exact chooseWinner_mem _ _ _ _
      by_cases hzw : z' = w
      · subst hzw; exact hz'_mem
      · exfalso
        rcases hOr with heq | ⟨hnot1, hnot2⟩
        · exact hzw heq.symm
        · have hHS_k : H_S k = P k := by
            change (hybridProfile P (liftPair P a w) S) k = P k
            simp [hybridProfile, hk]
          have hPk_strict : StrictPref (P k) := hP_strict k
          have hLiftk_strict : StrictPref (liftPair P a w k) := hLift_strict k
          have h1 : (P k).lt w z' := by
            rw [hHS_k] at hnot1
            rcases (P k).trichotomy z' w with h | h | h
            · exact absurd h hnot1
            · exact h
            · exact absurd (hPk_strict z' w h) hzw
          have h2 : (liftPair P a w k).lt z' w := by
            rcases (liftPair P a w k).trichotomy w z' with h | h | h
            · exact absurd h hnot2
            · exact h
            · exact absurd (hLiftk_strict w z' h) (fun h => hzw h.symm)
          by_cases hza : z' = a
          · rw [hza, liftPair, liftPairOf_lt_xy] at h2
            rw [hza] at h1
            exact h1.2 h2.1
          · apply h2.2
            apply liftPairOf_le_top_outside (Or.inr rfl)
            rintro (h | h)
            · exact hza h
            · exact hzw h
  have hUniv := hWalk Finset.univ
  rw [hybridProfile_univ] at hUniv
  have : w = a := by
    have := hRes (liftPair P a w) hLift_dom hUniv h_a_in
    exact this
  exact haw_ne this.symm

/-- If `i` is a dictator for `welfareFunctionOfChoiceFunction f`, then `i` is also a dictator for
`f` (in the full equality sense: The winners-set is exactly `i`'s set of most-preferred
alternatives). The winner-is-top inclusion is
`choiceFunction_winner_isTop_of_welfareFunction_dictator`; the reverse inclusion follows because on
a strict profile `i`'s top set is a singleton and the resolute winners-set is a nonempty singleton,
so both sides collapse to the same `{w}`. -/
lemma choiceFunction_dictator_of_welfareFunction_dictator
    [Fintype Voter] [Nonempty Voter] [Fintype Alt]
    {f : ChoiceFunction Voter Alt}
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f)
    (i : Voter)
    (hi : WelfareFunction.IsDictator (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur) i) :
      ChoiceFunction.IsDictator f i := by
  classical
  intro P hP
  have hP_strict : Profile.IsStrict P := profile_isStrict_of_mem_domain hDomEq hP
  have hWinnerTop : ∀ w ∈ f.winners P, ∀ a : Alt, (P i).le w a :=
    choiceFunction_winner_isTop_of_welfareFunction_dictator hRes hDomEq hSP hSur i hi P hP
  -- Pick the (unique) winner `w`; it is `i`-top, and both the winners-set and `i`'s top set
  -- collapse to `{w}`.
  obtain ⟨w, hw⟩ := f.winners_nonempty P hP
  have hw_top : ∀ a : Alt, (P i).le w a := hWinnerTop w hw
  have hwin_eq : f.winners P = {w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    exact ⟨hw, fun z hz => hRes P hP hz hw⟩
  have htop_eq : {a : Alt | ∀ b : Alt, (P i).le a b} = {w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hw_top, fun a ha => ?_⟩
    -- `a` and `w` are both `i`-top, hence `i`-indifferent; strictness forces `a = w`.
    exact (hP_strict i) a w ⟨ha w, hw_top a⟩
  rw [hwin_eq, htop_eq]

/-! ### Main theorem -/

/-- **Gibbard–Satterthwaite Theorem (Gibbard 1973, Satterthwaite 1975).** On the strict-orders
domain, every resolute social choice function on at least three alternatives that is strategy-proof
and surjective must have a dictator. -/
theorem gibbard_satterthwaite
    {Voter : Type*} [Finite Voter] [DecidableEq Voter] [Nonempty Voter]
    {Alt : Type*} [Fintype Alt]
    (h3 : 3 ≤ Fintype.card Alt)
    (f : ChoiceFunction Voter Alt)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hRes : ∀ P ∈ f.domain, (f.winners P).Subsingleton)
    (hSP : ChoiceFunction.StrategyProof f)
    (hSur : ChoiceFunction.Surjective f) :
    ∃ i : Voter, ChoiceFunction.IsDictator f i := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  have hSwfDom : (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur).domain =
     strictDomain Voter Alt := hDomEq
  have hPar := weakPareto_welfareFunctionOfChoiceFunction hRes hDomEq hSP hSur
  have hIIA := iia_welfareFunctionOfChoiceFunction hRes hDomEq hSP hSur
  obtain ⟨i, hi⟩ := arrow_impossibility_strict_domain
    h3 (welfareFunctionOfChoiceFunction f hRes hDomEq hSP hSur) hSwfDom hPar hIIA
  exact ⟨i, choiceFunction_dictator_of_welfareFunction_dictator hRes hDomEq hSP hSur i hi⟩

end Econlib.SocialChoice
