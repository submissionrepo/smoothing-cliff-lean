/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Combinatorics.FintypeCard
public import Econlib.SocialChoice.Profile.Domain
public import Econlib.SocialChoice.Profile.Transform
public import Econlib.SocialChoice.WelfareFunction.Properties
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset

/-!
# Arrow's Impossibility Theorem

On the **universal domain** of weak-order profiles (where individual indifference is permitted),
every social welfare function on at least three alternatives that satisfies **Weak Pareto** and
**IIA** must have a dictator (Arrow 1963). The same conclusion holds on the strict-orders domain.

## Main definitions

* `IsDecisive` — a coalition is decisive over `(x, y)` if unanimous strict preference implies
  social strict preference.
* `IsAlmostDecisive` — a coalition is almost decisive when the conclusion holds under the
  additional assumption that all non-members strictly prefer `y` to `x`.

## Main statements

* `field_expansion_univ` / `field_expansion_strict` — almost-decisiveness over any pair upgrades to
  decisiveness over every pair (Field Expansion).
* `group_contraction_univ` / `group_contraction_strict` — a decisive coalition of size ≥ 2 contains
  a proper nonempty decisive subcoalition (Group Contraction).
* `arrow_impossibility` — the canonical universal-domain weak-order form.
* `arrow_impossibility_strict_domain` — the strict-orders specialization.

## References

* Arrow, Kenneth J. 1963. *Social Choice and Individual Values*. 2nd ed. Wiley.

## Tags

social choice, arrow, impossibility, welfare function, decisive, dictator
-/
@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter Alt : Type*}

/-! ### Decisive and almost-decisive coalitions -/

/-- A coalition `V` is **decisive** over an ordered pair `(x, y)` for `f` when, on every admissible
profile in which every member of `V` strictly prefers `x` to `y`, society also strictly prefers `x`
to `y`. -/
def IsDecisive (f : WelfareFunction Voter Alt) (V : Finset Voter)
    (x y : Alt) : Prop :=
  ∀ P ∈ f.domain, (∀ i ∈ V, (P i).lt x y) → (f.aggregate P).lt x y

/-- A coalition `V` is **almost decisive** over an ordered pair `(x, y)` for `f` when, on every
admissible profile in which every member of `V` strictly prefers `x` to `y` and every non-member
strictly prefers `y` to `x`, society strictly prefers `x` to `y`. -/
def IsAlmostDecisive (f : WelfareFunction Voter Alt) (V : Finset Voter)
    (x y : Alt) : Prop :=
  ∀ P ∈ f.domain,
    (∀ i ∈ V, (P i).lt x y) →
    (∀ i, i ∉ V → (P i).lt y x) →
    (f.aggregate P).lt x y

/-- Decisiveness implies almost-decisiveness. -/
lemma IsDecisive.isAlmostDecisive
    {f : WelfareFunction Voter Alt} {V : Finset Voter} {x y : Alt}
    (h : IsDecisive f V x y) : IsAlmostDecisive f V x y :=
  fun P hP hV _ => h P hP hV

/-! ### Pareto gives the universe coalition decisiveness -/

/-- **Weak Pareto** makes the universe coalition decisive over every pair. -/
lemma decisive_univ [Fintype Voter]
    {f : WelfareFunction Voter Alt}
    (hPar : WelfareFunction.WeakPareto f) (x y : Alt) :
    IsDecisive f (Finset.univ : Finset Voter) x y := by
  intro P hP hV
  exact hPar P hP x y (fun i => hV i (Finset.mem_univ i))

private lemma IIA_lt_iff
    {f : WelfareFunction Voter Alt}
    (hIIA : WelfareFunction.IIA f) (P Q : Profile Voter Alt)
    (hP : P ∈ f.domain) (hQ : Q ∈ f.domain) (x y : Alt)
    (hpair : ∀ i, ((P i).le x y ↔ (Q i).le x y) ∧ ((P i).le y x ↔ (Q i).le y x)) :
    (f.aggregate P).lt x y ↔ (f.aggregate Q).lt x y := by
  obtain ⟨hxy, hyx⟩ := hIIA P Q hP hQ x y hpair
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hxy.mp h1, ?_⟩
    intro h'
    exact h2 (hyx.mpr h')
  · rintro ⟨h1, h2⟩
    refine ⟨hxy.mpr h1, ?_⟩
    intro h'
    exact h2 (hyx.mp h')

/-- Strict preference over the same ordered pair in two relations yields the IIA `le`-comparison
pair: Both `le a b` sides hold and both `le b a` sides fail. -/
private lemma le_iff_pair_of_lt {R S : PreferenceRel Alt} {a b : Alt}
    (hR : R.lt a b) (hS : S.lt a b) :
    (R.le a b ↔ S.le a b) ∧ (R.le b a ↔ S.le b a) :=
  ⟨⟨fun _ => hS.1, fun _ => hR.1⟩, ⟨fun h => absurd h hR.2, fun h => absurd h hS.2⟩⟩

/-! ### Building three-rank preferences -/

/-- Three-rank construction: Place `x` at top, then `y` next, then `z` at bottom. Pairs not
involving `x, y, z` inherit from `R`. -/
def threeRank (R : PreferenceRel Alt) (x y z : Alt) : PreferenceRel Alt :=
  moveToTop (moveToTop (moveToBottom R z) y) x

/-- Two-rank construction with `x` strictly above everything else, other pairs preserved. -/
abbrev topRank (R : PreferenceRel Alt) (x : Alt) : PreferenceRel Alt :=
  moveToTop R x

/-- Two-rank construction with `x` at bottom. -/
abbrev bottomRank (R : PreferenceRel Alt) (x : Alt) : PreferenceRel Alt :=
  moveToBottom R x

/-- `topRank R x` puts `x` strictly above every other alternative. -/
lemma topRank_lt_of_ne (R : PreferenceRel Alt) {x y : Alt} (hyx : y ≠ x) :
    (topRank R x).lt x y := by
  have hAtTop := atTop_moveToTop R x
  exact hAtTop y hyx

/-- `bottomRank R x` puts every other alternative strictly above `x`. -/
lemma bottomRank_lt_of_ne (R : PreferenceRel Alt) {x y : Alt} (hyx : y ≠ x) :
    (bottomRank R x).lt y x := by
  have hAtBot := atBottom_moveToBottom R x
  exact hAtBot y hyx

/-- `threeRank` preserves strictness. -/
lemma StrictPref.threeRank {R : PreferenceRel Alt} (h : StrictPref R) (x y z : Alt) :
    StrictPref (threeRank R x y z) :=
  ((h.moveToBottom z).moveToTop y).moveToTop x

/-- A canonical strict reference preference on `Alt`: Rank alternatives by their `Fintype.equivFin`
index. Used to seed strict-profile constructions in `group_contraction_strict`. -/
noncomputable def strictRefPref [Fintype Alt] : PreferenceRel Alt :=
  preferenceOfUtilityIn (Fintype.equivFin Alt)

/-- `strictRefPref` is strict, since `Fintype.equivFin` is injective. -/
lemma strictRefPref_isStrict [Fintype Alt] : StrictPref (strictRefPref : PreferenceRel Alt) :=
  strictPref_preferenceOfUtilityIn (Fintype.equivFin Alt).injective

/-- The all-indifferent reference preference. Every pair is rated equal. Used to seed weak-order
constructions in `group_contraction_univ`. -/
def trivialRefPref : PreferenceRel Alt where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  le_total _ _ := Or.inl trivial

/-! Key facts about `threeRank R x y z` when `x, y, z` are pairwise distinct. -/

/-- In `threeRank R x y z`, `x` is strictly above `y`. -/
lemma threeRank_lt_xy {R : PreferenceRel Alt} {x y z : Alt}
    -- `hxz` kept for API symmetry with `threeRank_lt_yz`/`threeRank_lt_xz`; unused in this proof.
    (hxy : x ≠ y) (_hxz : x ≠ z) :
    (threeRank R x y z).lt x y := by
  unfold threeRank
  exact (atTop_moveToTop _ x) y (Ne.symm hxy)

/-- In `threeRank R x y z`, `y` is strictly above `z`. -/
lemma threeRank_lt_yz {R : PreferenceRel Alt} {x y z : Alt}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (threeRank R x y z).lt y z := by
  unfold threeRank
  have hyx : y ≠ x := Ne.symm hxy
  have hzx : z ≠ x := Ne.symm hxz
  have h_inner : (moveToTop (moveToBottom R z) y).lt y z :=
    (atTop_moveToTop _ y) z (Ne.symm hyz)
  refine ⟨?_, ?_⟩
  · rw [moveToTop_le_of_ne hyx hzx]
    exact h_inner.1
  · rw [moveToTop_le_of_ne hzx hyx]
    exact h_inner.2

/-- In `threeRank R x y z`, `x` is strictly above `z`. -/
lemma threeRank_lt_xz {R : PreferenceRel Alt} {x y z : Alt}
    -- `hxy` kept for API symmetry with `threeRank_lt_xy`/`threeRank_lt_yz`; unused in this proof.
    (_hxy : x ≠ y) (hxz : x ≠ z) :
    (threeRank R x y z).lt x z := by
  unfold threeRank
  exact (atTop_moveToTop _ x) z (Ne.symm hxz)

/-! ### Field Expansion -/

/-- **Sub-lemma A (universal domain).** Almost-decisive over `(x, y)` upgrades to decisive over
`(b, y)` for any `b ≠ x, y`, when `f` admits the universal domain. -/
private lemma fieldExpansion_subA_univ
    {f : WelfareFunction Voter Alt}
    (hDom : universalDomain Voter Alt ⊆ f.domain)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    {b : Alt} (hbx : b ≠ x) (hby : b ≠ y) :
    IsDecisive f V b y := by
  classical
  intro P hP hV
  let P' : Profile Voter Alt :=
    fun i => if i ∈ V then threeRank (P i) b x y else moveToBottom (P i) x
  have hP' : P' ∈ f.domain := hDom (Set.mem_univ _)
  have hP'_V_xy : ∀ i ∈ V, (P' i).lt x y := by
    intro i hi
    simp only [P', hi, if_true]
    exact threeRank_lt_yz hbx hby hxy
  have hP'_nonV_yx : ∀ i, i ∉ V → (P' i).lt y x := by
    intro i hi
    simp only [P', hi, if_false]
    exact bottomRank_lt_of_ne (P i) (Ne.symm hxy)
  have hSoc_xy : (f.aggregate P').lt x y := hDA P' hP' hP'_V_xy hP'_nonV_yx
  have hP'_all_bx : ∀ i, (P' i).lt b x := by
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact threeRank_lt_xy hbx hby
    · simp only [P', hi, if_false]
      exact bottomRank_lt_of_ne (P i) hbx
  have hSoc_bx : (f.aggregate P').lt b x := hPar P' hP' b x hP'_all_bx
  have hSoc_by_P' : (f.aggregate P').lt b y :=
    (f.aggregate P').lt_trans hSoc_bx hSoc_xy
  have hIIA_pair : ∀ i, ((P i).le b y ↔ (P' i).le b y) ∧
                        ((P i).le y b ↔ (P' i).le y b) := by
    intro i
    by_cases hi : i ∈ V
    · have hPi_lt_by : (P i).lt b y := hV i hi
      have hP'i_lt_by : (P' i).lt b y := by
        simp only [P', hi, if_true]
        exact threeRank_lt_xz hbx hby
      exact le_iff_pair_of_lt hPi_lt_by hP'i_lt_by
    · simp only [P', hi, if_false]
      refine ⟨(moveToBottom_le_of_ne hbx hxy.symm).symm,
              (moveToBottom_le_of_ne hxy.symm hbx).symm⟩
  exact (IIA_lt_iff hIIA P P' hP hP' b y hIIA_pair).mpr hSoc_by_P'

/-- **Sub-lemma B (universal domain).** Almost-decisive over `(x, y)` upgrades to decisive over
`(x, c)` for any `c ≠ x, y`, when `f` admits the universal domain. -/
private lemma fieldExpansion_subB_univ
    {f : WelfareFunction Voter Alt}
    (hDom : universalDomain Voter Alt ⊆ f.domain)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    {c : Alt} (hcx : c ≠ x) (hcy : c ≠ y) :
    IsDecisive f V x c := by
  classical
  intro P hP hV
  let P' : Profile Voter Alt :=
    fun i => if i ∈ V then threeRank (P i) x y c else moveToTop (P i) y
  have hP' : P' ∈ f.domain := hDom (Set.mem_univ _)
  have hP'_V_xy : ∀ i ∈ V, (P' i).lt x y := by
    intro i hi
    simp only [P', hi, if_true]
    exact threeRank_lt_xy hxy (Ne.symm hcx)
  have hP'_nonV_yx : ∀ i, i ∉ V → (P' i).lt y x := by
    intro i hi
    simp only [P', hi, if_false]
    exact (atTop_moveToTop (P i) y) x hxy
  have hSoc_xy : (f.aggregate P').lt x y := hDA P' hP' hP'_V_xy hP'_nonV_yx
  have hP'_all_yc : ∀ i, (P' i).lt y c := by
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact threeRank_lt_yz hxy (Ne.symm hcx) (Ne.symm hcy)
    · simp only [P', hi, if_false]
      exact (atTop_moveToTop (P i) y) c hcy
  have hSoc_yc : (f.aggregate P').lt y c := hPar P' hP' y c hP'_all_yc
  have hSoc_xc_P' : (f.aggregate P').lt x c :=
    (f.aggregate P').lt_trans hSoc_xy hSoc_yc
  have hIIA_pair : ∀ i, ((P i).le x c ↔ (P' i).le x c) ∧
                        ((P i).le c x ↔ (P' i).le c x) := by
    intro i
    by_cases hi : i ∈ V
    · have hPi_lt_xc : (P i).lt x c := hV i hi
      have hP'i_lt_xc : (P' i).lt x c := by
        simp only [P', hi, if_true]
        exact threeRank_lt_xz hxy (Ne.symm hcx)
      exact le_iff_pair_of_lt hPi_lt_xc hP'i_lt_xc
    · simp only [P', hi, if_false]
      refine ⟨(moveToTop_le_of_ne hxy hcy).symm,
              (moveToTop_le_of_ne hcy hxy).symm⟩
  exact (IIA_lt_iff hIIA P P' hP hP' x c hIIA_pair).mpr hSoc_xc_P'

/-- **Sub-lemma A (strict domain).** Almost-decisive over `(x, y)` upgrades to decisive over
`(b, y)` for any `b ≠ x, y`, when `f.domain = strictDomain`. -/
private lemma fieldExpansion_subA_strict
    {f : WelfareFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    {b : Alt} (hbx : b ≠ x) (hby : b ≠ y) :
    IsDecisive f V b y := by
  classical
  intro P hP hV
  let P' : Profile Voter Alt :=
    fun i => if i ∈ V then threeRank (P i) b x y else moveToBottom (P i) x
  have hP_strict : Profile.IsStrict P := by rw [hDomEq] at hP; exact hP
  have hP' : P' ∈ f.domain := by
    rw [hDomEq]
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact (hP_strict i).threeRank b x y
    · simp only [P', hi, if_false]
      exact (hP_strict i).moveToBottom x
  have hP'_V_xy : ∀ i ∈ V, (P' i).lt x y := by
    intro i hi
    simp only [P', hi, if_true]
    exact threeRank_lt_yz hbx hby hxy
  have hP'_nonV_yx : ∀ i, i ∉ V → (P' i).lt y x := by
    intro i hi
    simp only [P', hi, if_false]
    exact bottomRank_lt_of_ne (P i) (Ne.symm hxy)
  have hSoc_xy : (f.aggregate P').lt x y := hDA P' hP' hP'_V_xy hP'_nonV_yx
  have hP'_all_bx : ∀ i, (P' i).lt b x := by
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact threeRank_lt_xy hbx hby
    · simp only [P', hi, if_false]
      exact bottomRank_lt_of_ne (P i) hbx
  have hSoc_bx : (f.aggregate P').lt b x := hPar P' hP' b x hP'_all_bx
  have hSoc_by_P' : (f.aggregate P').lt b y :=
    (f.aggregate P').lt_trans hSoc_bx hSoc_xy
  have hIIA_pair : ∀ i, ((P i).le b y ↔ (P' i).le b y) ∧
                        ((P i).le y b ↔ (P' i).le y b) := by
    intro i
    by_cases hi : i ∈ V
    · have hPi_lt_by : (P i).lt b y := hV i hi
      have hP'i_lt_by : (P' i).lt b y := by
        simp only [P', hi, if_true]
        exact threeRank_lt_xz hbx hby
      exact le_iff_pair_of_lt hPi_lt_by hP'i_lt_by
    · simp only [P', hi, if_false]
      refine ⟨(moveToBottom_le_of_ne hbx hxy.symm).symm,
              (moveToBottom_le_of_ne hxy.symm hbx).symm⟩
  exact (IIA_lt_iff hIIA P P' hP hP' b y hIIA_pair).mpr hSoc_by_P'

/-- **Sub-lemma B (strict domain).** Almost-decisive over `(x, y)` upgrades to decisive over
`(x, c)` for any `c ≠ x, y`, when `f.domain = strictDomain`. -/
private lemma fieldExpansion_subB_strict
    {f : WelfareFunction Voter Alt}
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    {c : Alt} (hcx : c ≠ x) (hcy : c ≠ y) :
    IsDecisive f V x c := by
  classical
  intro P hP hV
  let P' : Profile Voter Alt :=
    fun i => if i ∈ V then threeRank (P i) x y c else moveToTop (P i) y
  have hP_strict : Profile.IsStrict P := by rw [hDomEq] at hP; exact hP
  have hP' : P' ∈ f.domain := by
    rw [hDomEq]
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact (hP_strict i).threeRank x y c
    · simp only [P', hi, if_false]
      exact (hP_strict i).moveToTop y
  have hP'_V_xy : ∀ i ∈ V, (P' i).lt x y := by
    intro i hi
    simp only [P', hi, if_true]
    exact threeRank_lt_xy hxy (Ne.symm hcx)
  have hP'_nonV_yx : ∀ i, i ∉ V → (P' i).lt y x := by
    intro i hi
    simp only [P', hi, if_false]
    exact (atTop_moveToTop (P i) y) x hxy
  have hSoc_xy : (f.aggregate P').lt x y := hDA P' hP' hP'_V_xy hP'_nonV_yx
  have hP'_all_yc : ∀ i, (P' i).lt y c := by
    intro i
    by_cases hi : i ∈ V
    · simp only [P', hi, if_true]
      exact threeRank_lt_yz hxy (Ne.symm hcx) (Ne.symm hcy)
    · simp only [P', hi, if_false]
      exact (atTop_moveToTop (P i) y) c hcy
  have hSoc_yc : (f.aggregate P').lt y c := hPar P' hP' y c hP'_all_yc
  have hSoc_xc_P' : (f.aggregate P').lt x c :=
    (f.aggregate P').lt_trans hSoc_xy hSoc_yc
  have hIIA_pair : ∀ i, ((P i).le x c ↔ (P' i).le x c) ∧
                        ((P i).le c x ↔ (P' i).le c x) := by
    intro i
    by_cases hi : i ∈ V
    · have hPi_lt_xc : (P i).lt x c := hV i hi
      have hP'i_lt_xc : (P' i).lt x c := by
        simp only [P', hi, if_true]
        exact threeRank_lt_xz hxy (Ne.symm hcx)
      exact le_iff_pair_of_lt hPi_lt_xc hP'i_lt_xc
    · simp only [P', hi, if_false]
      refine ⟨(moveToTop_le_of_ne hxy hcy).symm,
              (moveToTop_le_of_ne hcy hxy).symm⟩
  exact (IIA_lt_iff hIIA P P' hP hP' x c hIIA_pair).mpr hSoc_xc_P'

/-- **Field Expansion (Lemma 2, universal domain).** If `V` is almost decisive over some pair
`(x, y)` with `x ≠ y`, then `V` is decisive over every pair. -/
theorem field_expansion_univ
    {f : WelfareFunction Voter Alt}
    [Fintype Alt]
    (hDom : universalDomain Voter Alt ⊆ f.domain)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    (h3 : 3 ≤ Fintype.card Alt)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    (a b : Alt) (hab : a ≠ b) :
    IsDecisive f V a b := by
  classical
  obtain ⟨c, hcx, hcy⟩ := Fintype.exists_ne_of_three_le_card h3 x y
  have hD_xc : IsDecisive f V x c := fieldExpansion_subB_univ hDom hPar hIIA hxy hDA hcx hcy
  have hD_cy : IsDecisive f V c y := fieldExpansion_subA_univ hDom hPar hIIA hxy hDA hcx hcy
  have hxc : x ≠ c := Ne.symm hcx
  have hyc : y ≠ c := Ne.symm hcy
  have hD_yc : IsDecisive f V y c := by
    have hDA_xc := hD_xc.isAlmostDecisive
    exact fieldExpansion_subA_univ hDom hPar hIIA hxc hDA_xc (Ne.symm hxy) hyc
  have hD_xy : IsDecisive f V x y := by
    have hDA_xc := hD_xc.isAlmostDecisive
    exact fieldExpansion_subB_univ hDom hPar hIIA hxc hDA_xc (Ne.symm hxy) hyc
  have hD_cx : IsDecisive f V c x := by
    have hDA_cy := hD_cy.isAlmostDecisive
    exact fieldExpansion_subB_univ hDom hPar hIIA hcy hDA_cy hxc hxy
  have hD_yx : IsDecisive f V y x := by
    have hDA_yc := hD_yc.isAlmostDecisive
    exact fieldExpansion_subB_univ hDom hPar hIIA hyc hDA_yc hxy hxc
  have step_subA :
      ∀ {u v : Alt}, u ≠ v → IsDecisive f V u v →
        ∀ {a' : Alt}, a' ≠ u → a' ≠ v → IsDecisive f V a' v := by
    intro u v huv hDuv a' hau hav
    exact fieldExpansion_subA_univ hDom hPar hIIA huv hDuv.isAlmostDecisive hau hav
  have step_subB :
      ∀ {u v : Alt}, u ≠ v → IsDecisive f V u v →
        ∀ {b' : Alt}, b' ≠ u → b' ≠ v → IsDecisive f V u b' := by
    intro u v huv hDuv b' hbu hbv
    exact fieldExpansion_subB_univ hDom hPar hIIA huv hDuv.isAlmostDecisive hbu hbv
  by_cases hax : a = x
  · by_cases hby : b = y
    · rw [hax, hby]; exact hD_xy
    · by_cases hbc : b = c
      · rw [hax, hbc]; exact hD_xc
      · have hbx : b ≠ x := by intro h; subst h; exact hab hax
        rw [hax]
        exact step_subB hxc hD_xc hbx hbc
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · rw [hay, hbx]; exact hD_yx
      · by_cases hbc : b = c
        · rw [hay, hbc]; exact hD_yc
        · have hbx' : b ≠ x := hbx
          have hby : b ≠ y := by intro h; subst h; exact hab hay
          rw [hay]
          exact step_subB hyc hD_yc hby hbc
    · by_cases hac : a = c
      · by_cases hbx : b = x
        · rw [hac, hbx]; exact hD_cx
        · by_cases hby : b = y
          · rw [hac, hby]; exact hD_cy
          · have hbc : b ≠ c := by intro h; subst h; exact hab hac
            rw [hac]
            exact step_subB (Ne.symm hyc) hD_cy hbc hby
      · by_cases hbx : b = x
        · rw [hbx]
          exact step_subA hcx hD_cx hac hax
        · by_cases hby : b = y
          · rw [hby]
            exact step_subA (Ne.symm hyc) hD_cy hac hay
          · by_cases hbc : b = c
            · rw [hbc]
              exact step_subA hxc hD_xc hax hac
            · have hD_ax : IsDecisive f V a x := step_subA hcx hD_cx hac hax
              exact step_subB hax hD_ax (Ne.symm hab) hbx

/-- **Field Expansion (Lemma 2, strict domain).** If `V` is almost decisive over some pair `(x, y)`
with `x ≠ y`, then `V` is decisive over every pair. -/
theorem field_expansion_strict
    {f : WelfareFunction Voter Alt}
    [Fintype Alt]
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    (h3 : 3 ≤ Fintype.card Alt)
    {V : Finset Voter} {x y : Alt} (hxy : x ≠ y)
    (hDA : IsAlmostDecisive f V x y)
    (a b : Alt) (hab : a ≠ b) :
    IsDecisive f V a b := by
  classical
  obtain ⟨c, hcx, hcy⟩ := Fintype.exists_ne_of_three_le_card h3 x y
  have hD_xc : IsDecisive f V x c := fieldExpansion_subB_strict hDomEq hPar hIIA hxy hDA hcx hcy
  have hD_cy : IsDecisive f V c y := fieldExpansion_subA_strict hDomEq hPar hIIA hxy hDA hcx hcy
  have hxc : x ≠ c := Ne.symm hcx
  have hyc : y ≠ c := Ne.symm hcy
  have hD_yc : IsDecisive f V y c := by
    have hDA_xc := hD_xc.isAlmostDecisive
    exact fieldExpansion_subA_strict hDomEq hPar hIIA hxc hDA_xc (Ne.symm hxy) hyc
  have hD_xy : IsDecisive f V x y := by
    have hDA_xc := hD_xc.isAlmostDecisive
    exact fieldExpansion_subB_strict hDomEq hPar hIIA hxc hDA_xc (Ne.symm hxy) hyc
  have hD_cx : IsDecisive f V c x := by
    have hDA_cy := hD_cy.isAlmostDecisive
    exact fieldExpansion_subB_strict hDomEq hPar hIIA hcy hDA_cy hxc hxy
  have hD_yx : IsDecisive f V y x := by
    have hDA_yc := hD_yc.isAlmostDecisive
    exact fieldExpansion_subB_strict hDomEq hPar hIIA hyc hDA_yc hxy hxc
  have step_subA :
      ∀ {u v : Alt}, u ≠ v → IsDecisive f V u v →
        ∀ {a' : Alt}, a' ≠ u → a' ≠ v → IsDecisive f V a' v := by
    intro u v huv hDuv a' hau hav
    exact fieldExpansion_subA_strict hDomEq hPar hIIA huv hDuv.isAlmostDecisive hau hav
  have step_subB :
      ∀ {u v : Alt}, u ≠ v → IsDecisive f V u v →
        ∀ {b' : Alt}, b' ≠ u → b' ≠ v → IsDecisive f V u b' := by
    intro u v huv hDuv b' hbu hbv
    exact fieldExpansion_subB_strict hDomEq hPar hIIA huv hDuv.isAlmostDecisive hbu hbv
  by_cases hax : a = x
  · by_cases hby : b = y
    · rw [hax, hby]; exact hD_xy
    · by_cases hbc : b = c
      · rw [hax, hbc]; exact hD_xc
      · have hbx : b ≠ x := by intro h; subst h; exact hab hax
        rw [hax]
        exact step_subB hxc hD_xc hbx hbc
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · rw [hay, hbx]; exact hD_yx
      · by_cases hbc : b = c
        · rw [hay, hbc]; exact hD_yc
        · have hbx' : b ≠ x := hbx
          have hby : b ≠ y := by intro h; subst h; exact hab hay
          rw [hay]
          exact step_subB hyc hD_yc hby hbc
    · by_cases hac : a = c
      · by_cases hbx : b = x
        · rw [hac, hbx]; exact hD_cx
        · by_cases hby : b = y
          · rw [hac, hby]; exact hD_cy
          · have hbc : b ≠ c := by intro h; subst h; exact hab hac
            rw [hac]
            exact step_subB (Ne.symm hyc) hD_cy hbc hby
      · by_cases hbx : b = x
        · rw [hbx]
          exact step_subA hcx hD_cx hac hax
        · by_cases hby : b = y
          · rw [hby]
            exact step_subA (Ne.symm hyc) hD_cy hac hay
          · by_cases hbc : b = c
            · rw [hbc]
              exact step_subA hxc hD_xc hax hac
            · have hD_ax : IsDecisive f V a x := step_subA hcx hD_cx hac hax
              exact step_subB hax hD_ax (Ne.symm hab) hbx

/-! ### Group Contraction -/

/-- **Group Contraction (Lemma 3, universal domain).** If a coalition `V` of cardinality at least 2
is decisive over every pair, then some nonempty subset `V' ⊊ V` is decisive over every pair. -/
theorem group_contraction_univ
    {f : WelfareFunction Voter Alt}
    [Fintype Alt]
    (hDom : universalDomain Voter Alt ⊆ f.domain)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    (h3 : 3 ≤ Fintype.card Alt)
    {V : Finset Voter} (hV : 2 ≤ V.card)
    (hVdec : ∀ a b : Alt, a ≠ b → IsDecisive f V a b) :
    ∃ V' : Finset Voter, V' ⊂ V ∧ V'.Nonempty ∧
      ∀ a b : Alt, a ≠ b → IsDecisive f V' a b := by
  classical
  have hV_nonempty : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := hV_nonempty
  let V₁ : Finset Voter := {i₀}
  let V₂ : Finset Voter := V.erase i₀
  have hV₁_sub : V₁ ⊆ V := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    rw [hv]
    exact hi₀
  have hV₂_sub : V₂ ⊆ V := Finset.erase_subset _ _
  have hV₁_V₂_disjoint : Disjoint V₁ V₂ := by
    intro s h1 h2 v hv
    have hv1 := h1 hv
    have hv2 := h2 hv
    simp only [V₁, Finset.mem_singleton] at hv1
    simp only [V₂, Finset.mem_erase] at hv2
    exact absurd hv1 hv2.1
  have hV_eq : V₁ ∪ V₂ = V := by
    ext v
    simp only [Finset.mem_union, V₁, V₂, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, h⟩)
      · exact hi₀
      · exact h
    · intro hv
      by_cases h : v = i₀
      · exact Or.inl h
      · exact Or.inr ⟨h, hv⟩
  have hV₁_ne : V₁.Nonempty := ⟨i₀, by simp [V₁]⟩
  have hV₂_ne : V₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.union_empty] at hV_eq
    rw [← hV_eq] at hV
    simp [V₁] at hV
  have hV₁_ssub : V₁ ⊂ V := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hV₁_sub, ?_⟩
    intro h
    obtain ⟨v, hvV₂⟩ := hV₂_ne
    have hvV : v ∈ V := hV₂_sub hvV₂
    have hvV₁ : v ∈ V₁ := h ▸ hvV
    rw [Finset.mem_singleton] at hvV₁
    rw [hvV₁] at hvV₂
    simp only [V₂, Finset.mem_erase] at hvV₂
    exact hvV₂.1 rfl
  have hV₂_ssub : V₂ ⊂ V := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hV₂_sub, ?_⟩
    intro h
    have hi₀_V₂ : i₀ ∈ V₂ := h ▸ hi₀
    simp [V₂] at hi₀_V₂
  have hAlt_ne : Nonempty Alt := by rw [← Fintype.card_pos_iff]; omega
  obtain ⟨x⟩ := hAlt_ne
  obtain ⟨y, hyx⟩ : ∃ y : Alt, y ≠ x := by
    by_contra h
    push Not at h
    have : Fintype.card Alt ≤ 1 := by
      rw [Fintype.card_le_one_iff]; intro u v; rw [h u, h v]
    omega
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Alt, z ≠ x ∧ z ≠ y := Fintype.exists_ne_of_three_le_card h3 x y
  have hxy : x ≠ y := Ne.symm hyx
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  let R₀ : PreferenceRel Alt := trivialRefPref
  let P_star : Profile Voter Alt := fun i =>
    if i ∈ V₁ then threeRank R₀ x y z
    else if i ∈ V₂ then threeRank R₀ y z x
    else threeRank R₀ z x y
  have hP_star : P_star ∈ f.domain := hDom (Set.mem_univ _)
  have hAll_V_yz : ∀ i ∈ V, (P_star i).lt y z := by
    intro i hi
    by_cases hiV1 : i ∈ V₁
    · simp only [P_star, hiV1, if_true]
      exact threeRank_lt_yz hxy hxz hyz
    · have hiV2 : i ∈ V₂ :=
        (Finset.mem_union.mp (hV_eq ▸ hi)).resolve_left hiV1
      simp only [P_star, hiV1, hiV2, if_false, if_true]
      exact threeRank_lt_xy hyz (Ne.symm hxy)
  have hSoc_yz : (f.aggregate P_star).lt y z :=
    hVdec y z hyz P_star hP_star hAll_V_yz
  rcases (f.aggregate P_star).trichotomy x z with hSoc_xz | hSoc_zx | hSoc_xz_indiff
  · have hDA_V1_xz : IsAlmostDecisive f V₁ x z := by
      intro Q hQ hV1_Q hnonV1_Q
      have hpair : ∀ i, ((Q i).le x z ↔ (P_star i).le x z) ∧
                        ((Q i).le z x ↔ (P_star i).le z x) := by
        intro i
        by_cases hiV1 : i ∈ V₁
        · have hQ_xz : (Q i).lt x z := hV1_Q i hiV1
          have hPs_xz : (P_star i).lt x z := by
            simp only [P_star, hiV1, if_true]
            exact threeRank_lt_xz hxy hxz
          exact le_iff_pair_of_lt hQ_xz hPs_xz
        · have hQ_zx : (Q i).lt z x := hnonV1_Q i hiV1
          have hPs_zx : (P_star i).lt z x := by
            by_cases hiV2 : i ∈ V₂
            · simp only [P_star, hiV1, hiV2, if_false, if_true]
              exact threeRank_lt_yz hyz (Ne.symm hxy) (Ne.symm hxz)
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_xy (Ne.symm hxz) (Ne.symm hyz)
          exact (le_iff_pair_of_lt hQ_zx hPs_zx).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star x z hpair).mpr hSoc_xz
    refine ⟨V₁, hV₁_ssub, hV₁_ne, ?_⟩
    intro a b hab
    exact field_expansion_univ hDom hPar hIIA h3 hxz hDA_V1_xz a b hab
  · have hSoc_yx : (f.aggregate P_star).lt y x :=
      (f.aggregate P_star).lt_trans hSoc_yz hSoc_zx
    have hyx : y ≠ x := Ne.symm hxy
    have hDA_V2_yx : IsAlmostDecisive f V₂ y x := by
      intro Q hQ hV2_Q hnonV2_Q
      have hpair : ∀ i, ((Q i).le y x ↔ (P_star i).le y x) ∧
                        ((Q i).le x y ↔ (P_star i).le x y) := by
        intro i
        by_cases hiV2 : i ∈ V₂
        · have hQ_yx : (Q i).lt y x := hV2_Q i hiV2
          have hiV1 : i ∉ V₁ := fun hiV1 =>
            Finset.disjoint_left.mp hV₁_V₂_disjoint hiV1 hiV2
          have hPs_yx : (P_star i).lt y x := by
            simp only [P_star, hiV1, hiV2, if_false, if_true]
            exact threeRank_lt_xz hyz (Ne.symm hxy)
          exact le_iff_pair_of_lt hQ_yx hPs_yx
        · have hQ_xy : (Q i).lt x y := hnonV2_Q i hiV2
          have hPs_xy : (P_star i).lt x y := by
            by_cases hiV1 : i ∈ V₁
            · simp only [P_star, hiV1, if_true]
              exact threeRank_lt_xy hxy hxz
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_yz (Ne.symm hxz) (Ne.symm hyz) hxy
          exact (le_iff_pair_of_lt hQ_xy hPs_xy).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star y x hpair).mpr hSoc_yx
    refine ⟨V₂, hV₂_ssub, hV₂_ne, ?_⟩
    intro a b hab
    exact field_expansion_univ hDom hPar hIIA h3 hyx hDA_V2_yx a b hab
  · have hSoc_yx : (f.aggregate P_star).lt y x := by
      refine ⟨?_, ?_⟩
      · exact (f.aggregate P_star).le_trans _ _ _ hSoc_yz.1 hSoc_xz_indiff.2
      · intro h_xy
        have h_zy : (f.aggregate P_star).le z y :=
          (f.aggregate P_star).le_trans _ _ _ hSoc_xz_indiff.2 h_xy
        exact hSoc_yz.2 h_zy
    have hyx : y ≠ x := Ne.symm hxy
    have hDA_V2_yx : IsAlmostDecisive f V₂ y x := by
      intro Q hQ hV2_Q hnonV2_Q
      have hpair : ∀ i, ((Q i).le y x ↔ (P_star i).le y x) ∧
                        ((Q i).le x y ↔ (P_star i).le x y) := by
        intro i
        by_cases hiV2 : i ∈ V₂
        · have hQ_yx : (Q i).lt y x := hV2_Q i hiV2
          have hiV1 : i ∉ V₁ := fun hiV1 =>
            Finset.disjoint_left.mp hV₁_V₂_disjoint hiV1 hiV2
          have hPs_yx : (P_star i).lt y x := by
            simp only [P_star, hiV1, hiV2, if_false, if_true]
            exact threeRank_lt_xz hyz (Ne.symm hxy)
          exact le_iff_pair_of_lt hQ_yx hPs_yx
        · have hQ_xy : (Q i).lt x y := hnonV2_Q i hiV2
          have hPs_xy : (P_star i).lt x y := by
            by_cases hiV1 : i ∈ V₁
            · simp only [P_star, hiV1, if_true]
              exact threeRank_lt_xy hxy hxz
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_yz (Ne.symm hxz) (Ne.symm hyz) hxy
          exact (le_iff_pair_of_lt hQ_xy hPs_xy).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star y x hpair).mpr hSoc_yx
    refine ⟨V₂, hV₂_ssub, hV₂_ne, ?_⟩
    intro a b hab
    exact field_expansion_univ hDom hPar hIIA h3 hyx hDA_V2_yx a b hab

/-- **Group Contraction (Lemma 3, strict domain).** If a coalition `V` of cardinality at least 2 is
decisive over every pair, then some proper nonempty subset `V' ⊊ V` is decisive over every pair,
when `f.domain = strictDomain`. -/
theorem group_contraction_strict
    {f : WelfareFunction Voter Alt}
    [Fintype Alt]
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f)
    (h3 : 3 ≤ Fintype.card Alt)
    {V : Finset Voter} (hV : 2 ≤ V.card)
    (hVdec : ∀ a b : Alt, a ≠ b → IsDecisive f V a b) :
    ∃ V' : Finset Voter, V' ⊂ V ∧ V'.Nonempty ∧
      ∀ a b : Alt, a ≠ b → IsDecisive f V' a b := by
  classical
  have hV_nonempty : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₀, hi₀⟩ := hV_nonempty
  let V₁ : Finset Voter := {i₀}
  let V₂ : Finset Voter := V.erase i₀
  have hV₁_sub : V₁ ⊆ V := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    rw [hv]
    exact hi₀
  have hV₂_sub : V₂ ⊆ V := Finset.erase_subset _ _
  have hV₁_V₂_disjoint : Disjoint V₁ V₂ := by
    intro s h1 h2 v hv
    have hv1 := h1 hv
    have hv2 := h2 hv
    simp only [V₁, Finset.mem_singleton] at hv1
    simp only [V₂, Finset.mem_erase] at hv2
    exact absurd hv1 hv2.1
  have hV_eq : V₁ ∪ V₂ = V := by
    ext v
    simp only [Finset.mem_union, V₁, V₂, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, h⟩)
      · exact hi₀
      · exact h
    · intro hv
      by_cases h : v = i₀
      · exact Or.inl h
      · exact Or.inr ⟨h, hv⟩
  have hV₁_ne : V₁.Nonempty := ⟨i₀, by simp [V₁]⟩
  have hV₂_ne : V₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.union_empty] at hV_eq
    rw [← hV_eq] at hV
    simp [V₁] at hV
  have hV₁_ssub : V₁ ⊂ V := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hV₁_sub, ?_⟩
    intro h
    obtain ⟨v, hvV₂⟩ := hV₂_ne
    have hvV : v ∈ V := hV₂_sub hvV₂
    have hvV₁ : v ∈ V₁ := h ▸ hvV
    rw [Finset.mem_singleton] at hvV₁
    rw [hvV₁] at hvV₂
    simp only [V₂, Finset.mem_erase] at hvV₂
    exact hvV₂.1 rfl
  have hV₂_ssub : V₂ ⊂ V := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hV₂_sub, ?_⟩
    intro h
    have hi₀_V₂ : i₀ ∈ V₂ := h ▸ hi₀
    simp [V₂] at hi₀_V₂
  have hAlt_ne : Nonempty Alt := by rw [← Fintype.card_pos_iff]; omega
  obtain ⟨x⟩ := hAlt_ne
  obtain ⟨y, hyx⟩ : ∃ y : Alt, y ≠ x := by
    by_contra h
    push Not at h
    have : Fintype.card Alt ≤ 1 := by
      rw [Fintype.card_le_one_iff]; intro u v; rw [h u, h v]
    omega
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Alt, z ≠ x ∧ z ≠ y := Fintype.exists_ne_of_three_le_card h3 x y
  have hxy : x ≠ y := Ne.symm hyx
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  let R₀ : PreferenceRel Alt := strictRefPref
  have hR₀_strict : StrictPref R₀ := strictRefPref_isStrict
  let P_star : Profile Voter Alt := fun i =>
    if i ∈ V₁ then threeRank R₀ x y z
    else if i ∈ V₂ then threeRank R₀ y z x
    else threeRank R₀ z x y
  have hP_star : P_star ∈ f.domain := by
    rw [hDomEq]
    intro i
    by_cases hi1 : i ∈ V₁
    · simp only [P_star, hi1, if_true]
      exact hR₀_strict.threeRank x y z
    · by_cases hi2 : i ∈ V₂
      · simp only [P_star, hi1, hi2, if_false, if_true]
        exact hR₀_strict.threeRank y z x
      · simp only [P_star, hi1, hi2, if_false]
        exact hR₀_strict.threeRank z x y
  have hAll_V_yz : ∀ i ∈ V, (P_star i).lt y z := by
    intro i hi
    by_cases hiV1 : i ∈ V₁
    · simp only [P_star, hiV1, if_true]
      exact threeRank_lt_yz hxy hxz hyz
    · have hiV2 : i ∈ V₂ :=
        (Finset.mem_union.mp (hV_eq ▸ hi)).resolve_left hiV1
      simp only [P_star, hiV1, hiV2, if_false, if_true]
      exact threeRank_lt_xy hyz (Ne.symm hxy)
  have hSoc_yz : (f.aggregate P_star).lt y z :=
    hVdec y z hyz P_star hP_star hAll_V_yz
  rcases (f.aggregate P_star).trichotomy x z with hSoc_xz | hSoc_zx | hSoc_xz_indiff
  · have hDA_V1_xz : IsAlmostDecisive f V₁ x z := by
      intro Q hQ hV1_Q hnonV1_Q
      have hpair : ∀ i, ((Q i).le x z ↔ (P_star i).le x z) ∧
                        ((Q i).le z x ↔ (P_star i).le z x) := by
        intro i
        by_cases hiV1 : i ∈ V₁
        · have hQ_xz : (Q i).lt x z := hV1_Q i hiV1
          have hPs_xz : (P_star i).lt x z := by
            simp only [P_star, hiV1, if_true]
            exact threeRank_lt_xz hxy hxz
          exact le_iff_pair_of_lt hQ_xz hPs_xz
        · have hQ_zx : (Q i).lt z x := hnonV1_Q i hiV1
          have hPs_zx : (P_star i).lt z x := by
            by_cases hiV2 : i ∈ V₂
            · simp only [P_star, hiV1, hiV2, if_false, if_true]
              exact threeRank_lt_yz hyz (Ne.symm hxy) (Ne.symm hxz)
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_xy (Ne.symm hxz) (Ne.symm hyz)
          exact (le_iff_pair_of_lt hQ_zx hPs_zx).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star x z hpair).mpr hSoc_xz
    refine ⟨V₁, hV₁_ssub, hV₁_ne, ?_⟩
    intro a b hab
    exact field_expansion_strict hDomEq hPar hIIA h3 hxz hDA_V1_xz a b hab
  · have hSoc_yx : (f.aggregate P_star).lt y x :=
      (f.aggregate P_star).lt_trans hSoc_yz hSoc_zx
    have hyx : y ≠ x := Ne.symm hxy
    have hDA_V2_yx : IsAlmostDecisive f V₂ y x := by
      intro Q hQ hV2_Q hnonV2_Q
      have hpair : ∀ i, ((Q i).le y x ↔ (P_star i).le y x) ∧
                        ((Q i).le x y ↔ (P_star i).le x y) := by
        intro i
        by_cases hiV2 : i ∈ V₂
        · have hQ_yx : (Q i).lt y x := hV2_Q i hiV2
          have hiV1 : i ∉ V₁ := fun hiV1 =>
            Finset.disjoint_left.mp hV₁_V₂_disjoint hiV1 hiV2
          have hPs_yx : (P_star i).lt y x := by
            simp only [P_star, hiV1, hiV2, if_false, if_true]
            exact threeRank_lt_xz hyz (Ne.symm hxy)
          exact le_iff_pair_of_lt hQ_yx hPs_yx
        · have hQ_xy : (Q i).lt x y := hnonV2_Q i hiV2
          have hPs_xy : (P_star i).lt x y := by
            by_cases hiV1 : i ∈ V₁
            · simp only [P_star, hiV1, if_true]
              exact threeRank_lt_xy hxy hxz
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_yz (Ne.symm hxz) (Ne.symm hyz) hxy
          exact (le_iff_pair_of_lt hQ_xy hPs_xy).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star y x hpair).mpr hSoc_yx
    refine ⟨V₂, hV₂_ssub, hV₂_ne, ?_⟩
    intro a b hab
    exact field_expansion_strict hDomEq hPar hIIA h3 hyx hDA_V2_yx a b hab
  · have hSoc_yx : (f.aggregate P_star).lt y x := by
      refine ⟨?_, ?_⟩
      · exact (f.aggregate P_star).le_trans _ _ _ hSoc_yz.1 hSoc_xz_indiff.2
      · intro h_xy
        have h_zy : (f.aggregate P_star).le z y :=
          (f.aggregate P_star).le_trans _ _ _ hSoc_xz_indiff.2 h_xy
        exact hSoc_yz.2 h_zy
    have hyx : y ≠ x := Ne.symm hxy
    have hDA_V2_yx : IsAlmostDecisive f V₂ y x := by
      intro Q hQ hV2_Q hnonV2_Q
      have hpair : ∀ i, ((Q i).le y x ↔ (P_star i).le y x) ∧
                        ((Q i).le x y ↔ (P_star i).le x y) := by
        intro i
        by_cases hiV2 : i ∈ V₂
        · have hQ_yx : (Q i).lt y x := hV2_Q i hiV2
          have hiV1 : i ∉ V₁ := fun hiV1 =>
            Finset.disjoint_left.mp hV₁_V₂_disjoint hiV1 hiV2
          have hPs_yx : (P_star i).lt y x := by
            simp only [P_star, hiV1, hiV2, if_false, if_true]
            exact threeRank_lt_xz hyz (Ne.symm hxy)
          exact le_iff_pair_of_lt hQ_yx hPs_yx
        · have hQ_xy : (Q i).lt x y := hnonV2_Q i hiV2
          have hPs_xy : (P_star i).lt x y := by
            by_cases hiV1 : i ∈ V₁
            · simp only [P_star, hiV1, if_true]
              exact threeRank_lt_xy hxy hxz
            · simp only [P_star, hiV1, hiV2, if_false]
              exact threeRank_lt_yz (Ne.symm hxz) (Ne.symm hyz) hxy
          exact (le_iff_pair_of_lt hQ_xy hPs_xy).symm
      exact (IIA_lt_iff hIIA Q P_star hQ hP_star y x hpair).mpr hSoc_yx
    refine ⟨V₂, hV₂_ssub, hV₂_ne, ?_⟩
    intro a b hab
    exact field_expansion_strict hDomEq hPar hIIA h3 hyx hDA_V2_yx a b hab

/-! ### Main theorems -/

/-- **Arrow's Impossibility Theorem (Arrow 1963), canonical weak-order form.** On the universal
domain, every social welfare function on at least three alternatives that satisfies Weak Pareto and
IIA must have a dictator. -/
theorem arrow_impossibility
    [Fintype Alt] [Finite Voter] [Nonempty Voter]
    (h3 : 3 ≤ Fintype.card Alt)
    (f : WelfareFunction Voter Alt)
    (hDom : universalDomain Voter Alt ⊆ f.domain)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f) :
    ∃ i : Voter, WelfareFunction.IsDictator f i := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  let P : Finset Voter → Prop :=
    fun V => V.Nonempty ∧ ∀ a b : Alt, a ≠ b → IsDecisive f V a b
  have hP_univ : P (Finset.univ : Finset Voter) :=
    ⟨Finset.univ_nonempty, fun a b _ => decisive_univ hPar a b⟩
  let D' : Finset (Finset Voter) := (Finset.univ : Finset (Finset Voter)).filter P
  have h_univ_in_D' : (Finset.univ : Finset Voter) ∈ D' :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP_univ⟩
  have hD'_nonempty : D'.Nonempty := ⟨Finset.univ, h_univ_in_D'⟩
  obtain ⟨V, hV_in_D', hV_min⟩ :=
    Finset.exists_min_image D' (fun V => V.card) hD'_nonempty
  have hV_filter := Finset.mem_filter.mp hV_in_D'
  obtain ⟨_, hV_ne, hV_dec⟩ := hV_filter
  have hV_card_one : V.card = 1 := by
    by_contra h
    have h_ge_2 : 2 ≤ V.card := by
      have h_pos : 1 ≤ V.card := Finset.Nonempty.card_pos hV_ne
      omega
    obtain ⟨V', hV'_ssub, hV'_ne, hV'_dec⟩ :=
      group_contraction_univ hDom hPar hIIA h3 h_ge_2 hV_dec
    have hV'_in_D' : V' ∈ D' :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV'_ne, hV'_dec⟩
    have hV'_card_lt : V'.card < V.card := Finset.card_lt_card hV'_ssub
    have hmin := hV_min V' hV'_in_D'
    omega
  obtain ⟨i, hVi⟩ := Finset.card_eq_one.mp hV_card_one
  refine ⟨i, ?_⟩
  intro Q hQ a b hab
  have hab_ne : a ≠ b := by
    intro heq; subst heq; exact (Q i).lt_irrefl _ hab
  apply hV_dec a b hab_ne Q hQ
  intro j hj
  rw [hVi, Finset.mem_singleton] at hj
  exact hj ▸ hab

/-- **Arrow's Impossibility Theorem (Arrow 1963), strict-orders specialization.** On the
strict-orders domain, every social welfare function on at least three alternatives that satisfies
Weak Pareto and IIA must have a dictator. -/
theorem arrow_impossibility_strict_domain
    [Fintype Alt] [Finite Voter] [Nonempty Voter]
    (h3 : 3 ≤ Fintype.card Alt)
    (f : WelfareFunction Voter Alt)
    (hDomEq : f.domain = strictDomain Voter Alt)
    (hPar : WelfareFunction.WeakPareto f)
    (hIIA : WelfareFunction.IIA f) :
    ∃ i : Voter, WelfareFunction.IsDictator f i := by
  classical
  letI : Fintype Voter := Fintype.ofFinite Voter
  let P : Finset Voter → Prop :=
    fun V => V.Nonempty ∧ ∀ a b : Alt, a ≠ b → IsDecisive f V a b
  have hP_univ : P (Finset.univ : Finset Voter) :=
    ⟨Finset.univ_nonempty, fun a b _ => decisive_univ hPar a b⟩
  let D' : Finset (Finset Voter) := (Finset.univ : Finset (Finset Voter)).filter P
  have h_univ_in_D' : (Finset.univ : Finset Voter) ∈ D' :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP_univ⟩
  have hD'_nonempty : D'.Nonempty := ⟨Finset.univ, h_univ_in_D'⟩
  obtain ⟨V, hV_in_D', hV_min⟩ :=
    Finset.exists_min_image D' (fun V => V.card) hD'_nonempty
  have hV_filter := Finset.mem_filter.mp hV_in_D'
  obtain ⟨_, hV_ne, hV_dec⟩ := hV_filter
  have hV_card_one : V.card = 1 := by
    by_contra h
    have h_ge_2 : 2 ≤ V.card := by
      have h_pos : 1 ≤ V.card := Finset.Nonempty.card_pos hV_ne
      omega
    obtain ⟨V', hV'_ssub, hV'_ne, hV'_dec⟩ :=
      group_contraction_strict hDomEq hPar hIIA h3 h_ge_2 hV_dec
    have hV'_in_D' : V' ∈ D' :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV'_ne, hV'_dec⟩
    have hV'_card_lt : V'.card < V.card := Finset.card_lt_card hV'_ssub
    have hmin := hV_min V' hV'_in_D'
    omega
  obtain ⟨i, hVi⟩ := Finset.card_eq_one.mp hV_card_one
  refine ⟨i, ?_⟩
  intro Q hQ a b hab
  have hab_ne : a ≠ b := by
    intro heq; subst heq; exact (Q i).lt_irrefl _ hab
  apply hV_dec a b hab_ne Q hQ
  intro j hj
  rw [hVi, Finset.mem_singleton] at hj
  exact hj ▸ hab

end Econlib.SocialChoice
