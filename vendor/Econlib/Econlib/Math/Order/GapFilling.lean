/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.CountableLinearOrderEmbedding

/-!
# Open gaps in subsets of linear orders

This file defines open gaps in subsets of linear orders and the "has all open gaps" property for
subsets of `ℝ`. The central result is the gap-collapsing lemma: For any `S ⊆ ℝ` there is a strictly
monotone map `g : S → ℝ` whose range has all open gaps.

An order embedding into `ℝ` is continuous for the order topology precisely when its range has all
open gaps, which is the continuity step of Debreu's utility representation theorem.

## Main definitions

* `IsOpenGap` — an open gap `(a, b)` in `T`: Both endpoints in `T`, nothing in `T` strictly between.
* `HasAllOpenGaps` — every nondegenerate closed interval of reals missing from `T` and bounded by
  members of `T` lies inside some open gap `(a, b)` of `T`.

## Main statements

* `ge_of_mem_of_gap`, `le_of_mem_of_gap` — members of `T` past one endpoint of an empty gap lie at
  or beyond the other endpoint.
* `exists_countable_order_dense_augmented` — a countable order-dense subset of `S` that also
  contains the minimum of `S` when one exists.
* `exists_strictMono_hasAllOpenGaps_range` — the gap-collapsing lemma.

## Notes

The gap-collapsing lemma extends the bounded, gap-free function on a countable order-dense subset
`Z ⊆ S` (from `Econlib.Math.Order.CountableLinearOrderEmbedding`) to all of `S` by
`g s = sSup {f z | z ∈ Z, z ≤ s}`. True jumps in `S` become open gaps in `range g`.
-/

@[expose] public section

open Set

/-- An open gap of `T ⊆ α` is an interval `(a, b)` with `a, b ∈ T`, `a < b`, and no elements of `T`
strictly between them. -/
structure IsOpenGap {α : Type} [LinearOrder α] (T : Set α) (a b : α) : Prop where
  /-- The left endpoint is in `T`. -/
  left_mem : a ∈ T
  /-- The right endpoint is in `T`. -/
  right_mem : b ∈ T
  /-- The endpoints are strictly ordered. -/
  lt : a < b
  /-- No element of `T` lies strictly between the endpoints. -/
  disjoint : Set.Ioo a b ∩ T = ∅

/-- `T` has all open gaps if every non-degenerate closed interval of reals missing from `T` that is
bounded by members of `T` falls entirely inside some open gap `(a, b)` of `T`. -/
def HasAllOpenGaps (T : Set ℝ) : Prop :=
  ∀ r₁ r₂, r₁ < r₂ →
    Set.Icc r₁ r₂ ∩ T = ∅ →
    (∃ x ∈ T, x < r₁) →
    (∃ y ∈ T, r₂ < y) →
    ∃ a b, IsOpenGap T a b ∧ Set.Icc r₁ r₂ ⊆ Set.Ioo a b

/-! ### Gap arithmetic

If `Ioo a b ∩ T = ∅` (i.e. the gap is empty), then any member of `T` that is strictly past one
endpoint must be at or beyond the other. -/

lemma ge_of_mem_of_gap {T : Set ℝ} {a b t : ℝ}
    (ht : t ∈ T) (hgap : Set.Ioo a b ∩ T = ∅) (hlt : a < t) : b ≤ t := by
  by_contra h; push Not at h
  have : t ∈ Set.Ioo a b ∩ T := ⟨⟨hlt, h⟩, ht⟩; rw [hgap] at this; exact this

lemma le_of_mem_of_gap {T : Set ℝ} {a b t : ℝ}
    (ht : t ∈ T) (hgap : Set.Ioo a b ∩ T = ∅) (htb : t < b) : t ≤ a := by
  by_contra h; push Not at h
  have : t ∈ Set.Ioo a b ∩ T := ⟨⟨h, htb⟩, ht⟩; rw [hgap] at this; exact this

/-- The set of jumps of `S` — pairs `(x, y)` in `S` with `x < y` and nothing of `S` strictly
between — is countable, since each jump contains a distinct rational. -/
lemma countable_jumps (S : Set ℝ) :
    Set.Countable {p : ℝ × ℝ | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ Set.Ioo p.1 p.2 ∩ S = ∅} := by
  let J := {p : ℝ × ℝ | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ Set.Ioo p.1 p.2 ∩ S = ∅}
  have H : ∀ p : J, ∃ q : ℚ, (p : ℝ × ℝ).1 < (q : ℝ) ∧ (q : ℝ) < (p : ℝ × ℝ).2 :=
    fun ⟨_, hp⟩ => exists_rat_btwn hp.2.2.1
  choose f hf using H
  rw [← Set.countable_coe_iff]
  exact Function.Injective.countable (f := f) fun a b heq => by
    obtain ⟨⟨p1, p2⟩, hp⟩ := a
    obtain ⟨⟨q1, q2⟩, hq⟩ := b
    have hfp := hf ⟨(p1, p2), hp⟩
    have hfq := hf ⟨(q1, q2), hq⟩
    dsimp only at hfp hfq heq
    rw [heq] at hfp
    have absurd_mem {A : Set ℝ} {x : ℝ} (hA : A = ∅) (hx : x ∈ A) : False := by
      simp [hA] at hx
    have h1 : p1 = q1 := by
      rcases lt_trichotomy p1 q1 with h | h | h
      · exact absurd (absurd_mem hp.2.2.2 ⟨⟨h, lt_trans hfq.1 hfp.2⟩, hq.1⟩) id
      · exact h
      · exact absurd (absurd_mem hq.2.2.2 ⟨⟨h, lt_trans hfp.1 hfq.2⟩, hp.1⟩) id
    have h2 : p2 = q2 := by
      rcases lt_trichotomy p2 q2 with h | h | h
      · exact absurd (absurd_mem hq.2.2.2 ⟨⟨lt_trans hfq.1 hfp.2, h⟩, hp.2.1⟩) id
      · exact h
      · exact absurd (absurd_mem hp.2.2.2 ⟨⟨lt_trans hfp.1 hfq.2, h⟩, hq.2.1⟩) id
    exact Subtype.ext (Prod.ext h1 h2)

/-- For each rational interval hitting S, we can choose a witness. -/
lemma exists_rational_witnesses (S : Set ℝ) :
    ∃ Z₂ : Set ℝ, Z₂ ⊆ S ∧ Z₂.Countable ∧
      ∀ q₁ q₂ : ℚ, (q₁ : ℝ) < q₂ → (Set.Ioo (q₁ : ℝ) q₂ ∩ S).Nonempty →
        ∃ z ∈ Z₂, z ∈ Set.Ioo (q₁ : ℝ) q₂ := by
  let P := {p : ℚ × ℚ | (p.1 : ℝ) < p.2 ∧ (Ioo (p.1 : ℝ) p.2 ∩ S).Nonempty}
  have H : ∀ p : P, ∃ z, z ∈ Ioo (p.1.1 : ℝ) p.1.2 ∩ S := fun ⟨_, hp⟩ => hp.2
  choose f hf using H
  use range f
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact (hf p).2
  · exact countable_range f
  · intro q1 q2 hlt hne
    let p : P := ⟨(q1, q2), hlt, hne⟩
    exact ⟨f p, mem_range_self p, (hf p).1⟩

/-- Construction of the countable order-dense subset Z₀ ⊆ S. -/
lemma exists_countable_order_dense (S : Set ℝ) :
    ∃ Z : Set ℝ, Z ⊆ S ∧ Z.Countable ∧
      (∀ x y, x ∈ S → y ∈ S → x < y → Set.Ioo x y ∩ S = ∅ → x ∈ Z ∧ y ∈ Z) ∧
      (∀ x y, x ∈ S → y ∈ S → x < y →
        ∃ z ∈ Z, ∃ z' ∈ Z, x ≤ z ∧ z < z' ∧ z' ≤ y) := by
  let J := {p : ℝ × ℝ | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ Set.Ioo p.1 p.2 ∩ S = ∅}
  let Z₀ := (Prod.fst '' J) ∪ (Prod.snd '' J)
  have hZ₀_sub : Z₀ ⊆ S := by
    intro x hx; cases hx with
    | inl h => obtain ⟨p, hp, rfl⟩ := h; exact hp.1
    | inr h => obtain ⟨p, hp, rfl⟩ := h; exact hp.2.1
  have hZ₀_count : Z₀.Countable :=
    (countable_jumps S).image Prod.fst |>.union ((countable_jumps S).image Prod.snd)
  have hZ₀_jumps : ∀ x y, x ∈ S → y ∈ S → x < y → Set.Ioo x y ∩ S = ∅ →
      x ∈ Z₀ ∧ y ∈ Z₀ := fun x y hxS hyS hxy hgap =>
    ⟨Set.mem_union_left _ ⟨(x, y), ⟨hxS, hyS, hxy, hgap⟩, rfl⟩,
     Set.mem_union_right _ ⟨(x, y), ⟨hxS, hyS, hxy, hgap⟩, rfl⟩⟩
  obtain ⟨Z₂, hZ₂_sub, hZ₂_count, hZ₂_wit⟩ := exists_rational_witnesses S
  refine ⟨Z₀ ∪ Z₂, Set.union_subset hZ₀_sub hZ₂_sub,
         hZ₀_count.union hZ₂_count, ?_, ?_⟩
  · intro x y hxS hyS hxy hgap
    have := hZ₀_jumps x y hxS hyS hxy hgap
    exact ⟨Set.mem_union_left _ this.1, Set.mem_union_left _ this.2⟩
  · intro x y hxS hyS hxy
    by_cases hjump : Set.Ioo x y ∩ S = ∅
    · exact ⟨x, Set.mem_union_left _ (hZ₀_jumps x y hxS hyS hxy hjump).1,
             y, Set.mem_union_left _ (hZ₀_jumps x y hxS hyS hxy hjump).2,
             le_refl _, hxy, le_refl _⟩
    · rw [Set.eq_empty_iff_forall_notMem] at hjump; push Not at hjump
      obtain ⟨s, hs_ioo, hs_S⟩ := hjump
      obtain ⟨q₁, hxq₁, hq₁s⟩ := exists_rat_btwn hs_ioo.1
      obtain ⟨q₂, hsq₂, hq₂y⟩ := exists_rat_btwn hs_ioo.2
      have h₁ : (Set.Ioo (q₁ : ℝ) q₂ ∩ S).Nonempty := ⟨s, ⟨hq₁s, hsq₂⟩, hs_S⟩
      obtain ⟨z₁, hz₁_Z₂, hz₁_ioo⟩ := hZ₂_wit q₁ q₂ (lt_trans hq₁s hsq₂) h₁
      have hz₁_S : z₁ ∈ S := hZ₂_sub hz₁_Z₂
      have hz₁_xy : z₁ ∈ Set.Ioo x y := ⟨lt_trans hxq₁ hz₁_ioo.1, lt_trans hz₁_ioo.2 hq₂y⟩
      by_cases hjump₂ : Set.Ioo z₁ y ∩ S = ∅
      · exact ⟨z₁, Set.mem_union_left _ (hZ₀_jumps z₁ y hz₁_S hyS hz₁_xy.2 hjump₂).1,
               y, Set.mem_union_left _ (hZ₀_jumps z₁ y hz₁_S hyS hz₁_xy.2 hjump₂).2,
               hz₁_xy.1.le, hz₁_xy.2, le_refl _⟩
      · rw [Set.eq_empty_iff_forall_notMem] at hjump₂; push Not at hjump₂
        obtain ⟨s₂, hs₂_ioo, hs₂_S⟩ := hjump₂
        obtain ⟨q₃, hz₁q₃, hq₃s₂⟩ := exists_rat_btwn hs₂_ioo.1
        obtain ⟨q₄, hs₂q₄, hq₄y⟩ := exists_rat_btwn hs₂_ioo.2
        have h₃ : (Set.Ioo (q₃ : ℝ) q₄ ∩ S).Nonempty := ⟨s₂, ⟨hq₃s₂, hs₂q₄⟩, hs₂_S⟩
        obtain ⟨z₂, hz₂_Z₂, hz₂_ioo⟩ := hZ₂_wit q₃ q₄ (lt_trans hq₃s₂ hs₂q₄) h₃
        exact ⟨z₁, Set.mem_union_right _ hz₁_Z₂,
               z₂, Set.mem_union_right _ hz₂_Z₂,
               hz₁_xy.1.le, lt_trans hz₁q₃ hz₂_ioo.1, (lt_trans hz₂_ioo.2 hq₄y).le⟩

/-- A minor extension to `exists_countable_order_dense` which ensures that the constructed
countable order-dense subset `Z` contains the minimum element of `S` if it exists. This guarantees
that the set `{z ∈ Z | z ≤ s}` is always non-empty for any `s ∈ S`, which is essential for
extending the utility function via `sSup`. -/
lemma exists_countable_order_dense_augmented (S : Set ℝ) :
    ∃ Z : Set ℝ, Z ⊆ S ∧ Z.Countable ∧
      (∀ s ∈ S, (Z ∩ {z | z ≤ s}).Nonempty) ∧
      (∀ x y, x ∈ S → y ∈ S → x < y → Set.Ioo x y ∩ S = ∅ → x ∈ Z ∧ y ∈ Z) ∧
      (∀ x y, x ∈ S → y ∈ S → x < y →
        ∃ z ∈ Z, ∃ z' ∈ Z, x ≤ z ∧ z < z' ∧ z' ≤ y) := by
  obtain ⟨Z₀, hZ₀_sub, hZ₀_count, hZ₀_jumps, hZ₀_dense⟩ := exists_countable_order_dense S
  let Zmin := {s ∈ S | ∀ x ∈ S, s ≤ x}
  have hZmin_sub : Zmin ⊆ S := fun x hx => hx.1
  have hZmin_count : Zmin.Countable := by
    refine Set.Subsingleton.countable ?_
    intro a ha b hb
    exact le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  let Z := Z₀ ∪ Zmin
  use Z
  refine ⟨Set.union_subset hZ₀_sub hZmin_sub, hZ₀_count.union hZmin_count, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hmin : ∀ x ∈ S, s ≤ x
    · exact ⟨s, Set.mem_inter (Set.mem_union_right _ ⟨hs, hmin⟩) (le_refl s)⟩
    · push Not at hmin
      obtain ⟨x, hxS, hxs⟩ := hmin
      obtain ⟨z, hzZ, z', hz'Z, hxz, hzz', hz's⟩ := hZ₀_dense x s hxS hs hxs
      exact ⟨z, Set.mem_inter (Set.mem_union_left _ hzZ) (le_trans (le_of_lt hzz') hz's)⟩
  · intro x y hxS hyS hxy hgap
    obtain ⟨hx, hy⟩ := hZ₀_jumps x y hxS hyS hxy hgap
    exact ⟨Set.mem_union_left _ hx, Set.mem_union_left _ hy⟩
  · intro x y hxS hyS hxy
    obtain ⟨z, hzZ, z', hz'Z, hxz, hzz', hz'y⟩ := hZ₀_dense x y hxS hyS hxy
    exact ⟨z, Set.mem_union_left _ hzZ, z', Set.mem_union_left _ hz'Z, hxz, hzz', hz'y⟩

open Classical in
/-- **Gap-collapsing lemma:** for any `S ⊆ ℝ` there is a strictly monotone map `g : S → ℝ` whose
range has all open gaps. -/
theorem exists_strictMono_hasAllOpenGaps_range (S : Set ℝ) :
    ∃ g : S → ℝ, StrictMono g ∧ HasAllOpenGaps (Set.range g) := by
  obtain ⟨Z, hZ_sub, hZ_count, hZ_nonempty, hZ_jumps, hZ_dense⟩ :=
    exists_countable_order_dense_augmented S
  have hJ_count : (DebreuGap.JumpSet Z).Countable := DebreuGap.ZAug.jumpSet_countable Z
  obtain ⟨f, hf_mono, hf_bdd, hf_noGap⟩ :=
    DebreuGap.ZAug.exists_strictMono_bounded_noGap Z hZ_count
  -- ### Defining the Extension `g`
  -- We extend the bounded map `f` on the dense subset `Z` to the entire set `S`
  -- by taking the supremum of `f(z)` over all `z ∈ Z` with `z ≤ s`.
  let Z_le (s : S) : Set ↥Z := {z : ↥Z | (z : ℝ) ≤ (s : ℝ)}
  have hZ_le_nonempty : ∀ s : S, (Z_le s).Nonempty := by
    intro s
    obtain ⟨z, hzZ, hzs⟩ := hZ_nonempty (s : ℝ) s.2
    exact ⟨⟨z, hzZ⟩, hzs⟩
  let g : S → ℝ := fun s => sSup (f '' Z_le s)
  have hf_monotone : Monotone f := StrictMono.monotone hf_mono
  have hg_le : ∀ (s : S) (z : ↥Z), (z : ℝ) ≤ (s : ℝ) → f z ≤ g s := by
    intro s z hz
    apply le_csSup
    · use 1; rintro _ ⟨w, -, rfl⟩; exact (hf_bdd w).2
    · exact ⟨z, hz, rfl⟩
  have hg_ge : ∀ (s : S) (z : ↥Z), (s : ℝ) ≤ (z : ℝ) → g s ≤ f z := by
    intro s z hz
    apply csSup_le
    · exact (hZ_le_nonempty s).image f
    · rintro _ ⟨w, hw, rfl⟩
      exact hf_monotone (Subtype.coe_le_coe.mpr (le_trans hw hz))
  -- ### Strict Monotonicity of `g`
  -- For `s₁ < s₂`, the interval `(s₁, s₂)` either is an empty jump in `S` (in which case
  -- we use the endpoints from `Z₀`) or contains an element `x ∈ S` (allowing us to sandwich
  -- with elements from `Z`).
  have hg_mono : StrictMono g := by
    intro s₁ s₂ hs
    have hs₁s₂ : (s₁ : ℝ) < (s₂ : ℝ) := hs
    by_cases hgap : Set.Ioo (s₁ : ℝ) (s₂ : ℝ) ∩ S = ∅
    · obtain ⟨hz₁, hz₂⟩ := hZ_jumps (s₁ : ℝ) (s₂ : ℝ) s₁.2 s₂.2 hs₁s₂ hgap
      let hz1 : ↥Z := ⟨(s₁ : ℝ), hz₁⟩
      let hz2 : ↥Z := ⟨(s₂ : ℝ), hz₂⟩
      have h1 : g s₁ ≤ f hz1 := hg_ge s₁ hz1 (le_refl _)
      have h2 : f hz2 ≤ g s₂ := hg_le s₂ hz2 (le_refl _)
      have h3 : f hz1 < f hz2 := hf_mono hs₁s₂
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 h2)
    · rw [Set.eq_empty_iff_forall_notMem] at hgap; push Not at hgap
      obtain ⟨x, hx_ioo, hxS⟩ := hgap
      obtain ⟨z, hzZ, z', hz'Z, hxz, hzz', hz'x⟩ := hZ_dense (s₁ : ℝ) x s₁.2 hxS hx_ioo.1
      let hz : ↥Z := ⟨z, hzZ⟩
      let hz' : ↥Z := ⟨z', hz'Z⟩
      have h1 : g s₁ ≤ f hz := hg_ge s₁ hz hxz
      have h2 : f hz' ≤ g s₂ := hg_le s₂ hz' (le_trans hz'x hx_ioo.2.le)
      have h3 : f hz < f hz' := hf_mono hzz'
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 h2)
  -- `g` is monotone on the real-coercion order (the `≤` companion of `hg_mono`).
  have hg_mono_le : ∀ s₁ s₂ : S, (s₁ : ℝ) ≤ (s₂ : ℝ) → g s₁ ≤ g s₂ := by
    intro s₁ s₂ h
    rcases eq_or_lt_of_le h with heq | hlt
    · exact le_of_eq (congrArg g (Subtype.ext heq))
    · exact le_of_lt (hg_mono hlt)
  -- On `Z`, the sup-extension `g` agrees with `f` (sandwiched by `hg_le` and `hg_ge`).
  have hf_eq_g : ∀ z : ↥Z, f z = g ⟨(z : ℝ), hZ_sub z.2⟩ := fun z =>
    le_antisymm (hg_le ⟨(z : ℝ), hZ_sub z.2⟩ z (le_refl _))
      (hg_ge ⟨(z : ℝ), hZ_sub z.2⟩ z (le_refl _))
  -- ### The No-Gap Property for the Extension `g`
  -- We must show that any non-degenerate closed interval `[r₁, r₂]` missing from `range g`
  -- (and bounded by elements of `range g`) falls within a true open gap `(g(a_{max}), g(b_{min}))`.
  --
  -- If the corresponding Dedekind cut `(A, B)` on `Z` lacked a maximum or minimum,
  -- the `hf_noGap` property of `f` would collapse it to a point, forcing `r₁ = r₂`,
  -- which contradicts the assumption `r₁ < r₂`. Thus, the gap is real and comes from a jump in `S`.
  have hg_hasAll : HasAllOpenGaps (Set.range g) := by
    intro r₁ r₂ hr_lt hr_inter hx_exist hy_exist
    obtain ⟨x_val, ⟨sx, rfl⟩, hx⟩ := hx_exist
    obtain ⟨y_val, ⟨sy, rfl⟩, hy⟩ := hy_exist
    let S_down : Set S := {s | g s < r₁}
    let S_up : Set S := {s | r₂ < g s}
    have S_partition : ∀ s : S, s ∈ S_down ∨ s ∈ S_up := by
      intro s
      have h1 : g s ∉ Set.Icc r₁ r₂ := by
        intro h
        have : g s ∈ Set.Icc r₁ r₂ ∩ Set.range g := ⟨h, ⟨s, rfl⟩⟩
        rw [hr_inter] at this
        exact this
      simp only [Set.mem_Icc, not_and_or, not_le] at h1
      exact h1
    let A : Set ↥Z := {z : ↥Z | (⟨(z : ℝ), hZ_sub z.2⟩ : S) ∈ S_down}
    let B : Set ↥Z := {z : ↥Z | (⟨(z : ℝ), hZ_sub z.2⟩ : S) ∈ S_up}
    have hAB_univ : A ∪ B = Set.univ := by
      ext z
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      exact S_partition ⟨(z : ℝ), hZ_sub z.2⟩
    have hA_nonempty : A.Nonempty := by
      obtain ⟨z, hzZ, hzsx⟩ := hZ_nonempty (sx : ℝ) sx.2
      have hz_le : z ≤ (sx : ℝ) := hzsx
      let hzS : S := ⟨z, hZ_sub hzZ⟩
      have hgz_le : g hzS ≤ g sx := hg_mono_le hzS sx hz_le
      exact ⟨⟨z, hzZ⟩, lt_of_le_of_lt hgz_le hx⟩
    have hB_nonempty : B.Nonempty := by
      have hsy_sup : sSup (f '' Z_le sy) > r₂ := hy
      obtain ⟨w_val, ⟨w, hw, rfl⟩, hw_gt⟩ :=
        exists_lt_of_lt_csSup ((hZ_le_nonempty sy).image f) hsy_sup
      have hw_ge : f w ≤ g ⟨(w : ℝ), hZ_sub w.2⟩ := hg_le ⟨(w : ℝ), hZ_sub w.2⟩ w (le_refl _)
      exact ⟨w, show r₂ < g ⟨(w : ℝ), hZ_sub w.2⟩ from lt_of_lt_of_le hw_gt hw_ge⟩
    have hAB_lt : ∀ a ∈ A, ∀ b ∈ B, (a : ℝ) < (b : ℝ) := by
      intro a ha b hb
      have hga : g ⟨(a : ℝ), hZ_sub a.2⟩ < r₁ := ha
      have hgb : r₂ < g ⟨(b : ℝ), hZ_sub b.2⟩ := hb
      have hgab : g ⟨(a : ℝ), hZ_sub a.2⟩ < g ⟨(b : ℝ), hZ_sub b.2⟩ :=
        lt_trans hga (lt_trans hr_lt hgb)
      exact StrictMono.lt_iff_lt hg_mono |>.mp hgab
    have h_or_not : ¬ ((∀ a ∈ A, ∃ a' ∈ A, (a : ℝ) < (a' : ℝ)) ∨
                        (∀ b ∈ B, ∃ b' ∈ B, (b' : ℝ) < (b : ℝ))) := by
      intro h_or
      have h_eq := hf_noGap A B hAB_univ hA_nonempty hB_nonempty hAB_lt h_or
      have h_sup : sSup (f '' A) ≤ r₁ := by
        apply csSup_le (hA_nonempty.image _)
        rintro _ ⟨a, ha, rfl⟩
        rw [hf_eq_g a]
        exact le_of_lt ha
      have h_inf : r₂ ≤ sInf (f '' B) := by
        apply le_csInf (hB_nonempty.image _)
        rintro _ ⟨b, hb, rfl⟩
        rw [hf_eq_g b]
        exact le_of_lt hb
      rw [h_eq] at h_sup
      exact lt_irrefl _ (lt_of_lt_of_le hr_lt (le_trans h_inf h_sup))
    push Not at h_or_not
    obtain ⟨⟨a_max, ha_max_in, ha_max⟩, ⟨b_min, hb_min_in, hb_min⟩⟩ := h_or_not
    have hgap_S : Set.Ioo (a_max : ℝ) (b_min : ℝ) ∩ S = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro s ⟨⟨h_a_lt, h_lt_b⟩, hs_S⟩
      rcases S_partition ⟨s, hs_S⟩ with h_down | h_up
      · obtain ⟨z, hzZ, z', hz'Z, hxz, hzz', hz's⟩ :=
          hZ_dense (a_max:ℝ) s (hZ_sub a_max.2) hs_S h_a_lt
        have hz'A : (⟨z', hz'Z⟩ : ↥Z) ∈ A := by
          let hz'S : S := ⟨z', hZ_sub hz'Z⟩
          have h_le : g hz'S ≤ g ⟨s, hs_S⟩ := hg_mono_le hz'S ⟨s, hs_S⟩ hz's
          exact lt_of_le_of_lt h_le h_down
        have h_z'A_le := ha_max ⟨z', hz'Z⟩ hz'A
        have h_amax_lt_z' : (a_max : ℝ) < z' := lt_of_le_of_lt hxz hzz'
        exact lt_irrefl _ (lt_of_lt_of_le h_amax_lt_z' h_z'A_le)
      · obtain ⟨z, hzZ, z', hz'Z, hsz, hzz', hz'b⟩ :=
          hZ_dense s (b_min:ℝ) hs_S (hZ_sub b_min.2) h_lt_b
        have hzB : (⟨z, hzZ⟩ : ↥Z) ∈ B := by
          let hzS : S := ⟨z, hZ_sub hzZ⟩
          have h_le : g ⟨s, hs_S⟩ ≤ g hzS := hg_mono_le ⟨s, hs_S⟩ hzS hsz
          exact lt_of_lt_of_le h_up h_le
        have h_bmin_le_z := hb_min ⟨z, hzZ⟩ hzB
        have h_z_lt_bmin : z < (b_min : ℝ) := lt_of_lt_of_le hzz' hz'b
        exact lt_irrefl _ (lt_of_le_of_lt h_bmin_le_z h_z_lt_bmin)
    have hgap_range : Set.Ioo (g ⟨(a_max:ℝ), hZ_sub a_max.2⟩) (g ⟨(b_min:ℝ), hZ_sub b_min.2⟩)
      ∩ Set.range g = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨⟨h_ga_lt, h_lt_gb⟩, ⟨s, rfl⟩⟩
        have h_a_lt_s : (a_max : ℝ) < (s : ℝ) := StrictMono.lt_iff_lt hg_mono |>.mp h_ga_lt
        have h_s_lt_b : (s : ℝ) < (b_min : ℝ) := StrictMono.lt_iff_lt hg_mono |>.mp h_lt_gb
        have hs_ioo : (s : ℝ) ∈ Set.Ioo (a_max : ℝ) (b_min : ℝ) ∩ S := ⟨⟨h_a_lt_s, h_s_lt_b⟩, s.2⟩
        rw [hgap_S] at hs_ioo
        exact hs_ioo
    exact ⟨g ⟨(a_max:ℝ), hZ_sub a_max.2⟩, g ⟨(b_min:ℝ), hZ_sub b_min.2⟩,
      ⟨⟨⟨(a_max:ℝ), hZ_sub a_max.2⟩, rfl⟩,
       ⟨⟨(b_min:ℝ), hZ_sub b_min.2⟩, rfl⟩,
       lt_trans ha_max_in (lt_trans hr_lt hb_min_in),
       hgap_range⟩,
      fun y hy => ⟨lt_of_lt_of_le ha_max_in hy.1, lt_of_le_of_lt hy.2 hb_min_in⟩⟩
  exact ⟨g, hg_mono, hg_hasAll⟩
