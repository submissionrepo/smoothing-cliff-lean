/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Bounded order embedding of a countable subset of `ℝ`

Given a countable subset `Z ⊆ ℝ`, this file constructs a bounded strictly monotone `f : Z → ℝ` with
a no-gap property: For any Dedekind cut `A ∪ B = Z` with `A < B` where `A` has no maximum (or `B`
no minimum), `sSup f(A) = sInf f(B)`. This is the key ingredient for the gap-collapsing lemma
`exists_strictMono_hasAllOpenGaps_range` in `Econlib.Math.Order.GapFilling`.

## Main definitions

* `DebreuGap.boundH` — the bounding homeomorphism `H(x) = x/(1+|x|) : ℝ → (-1, 1)`.
* `DebreuGap.JumpSet` — pairs `(x, y)` in `Z` with `x < y` and no member of `Z` strictly between.
* `DebreuGap.ZAug` — `Z` augmented with rational tails and rational fillers in each jump, a
  countable dense linear order without endpoints.
* `DebreuGap.ZAug.origEmb` — the canonical order embedding `Z ↪o ZAug Z`.
* `DebreuGap.ZAug.constructF` — the bounded strictly monotone `f : Z → ℝ`.

## Main statements

* `DebreuGap.ZAug.exists_strictMono_bounded_noGap` — existence of `f` with strict monotonicity,
  range in `[-1, 1]`, and the no-gap property.

## Notes

The construction augments `Z` into `ZAug Z` — a countable dense linear order without endpoints —
and applies Cantor's isomorphism theorem (`Order.iso_of_countable_dense`) to obtain
`cantorIso : ZAug Z ≃o ℚ`. Composing with `boundH` and restricting to `Z` via `orig` gives `f`.
-/

@[expose] public section

noncomputable section

namespace DebreuGap

/-! ## Bounding homeomorphism H(x) = x/(1+|x|)

We need a strictly monotone map from `ℝ` into a bounded interval to ensure the final utility
function `f` is bounded. The map `H(x) = x/(1+|x|)` is a homeomorphism `ℝ → (-1, 1)` with inverse
`H⁻¹(y) = y/(1-|y|)`. Composing Cantor's isomorphism `cantorIso : ZAug Z ≃o ℚ` with `H ∘ ↑` gives
the bounded map `boundedMap : ZAug Z → (-1, 1)`.

The key auxiliary fact `exists_rat_boundH_between` shows that for any `α < β` in `(-1, 1)`, there
is a rational `q` with `α < H(q) < β` — this provides the density needed for the no-gap argument
below. -/

/-- The bounding homeomorphism `H(x) = x/(1+|x|) : ℝ → (-1, 1)`. -/
def boundH (x : ℝ) : ℝ := x / (1 + |x|)
/-- Inverse of `boundH`, defined on `(-1, 1)`: `H⁻¹(y) = y/(1-|y|)`. -/
def boundH_inv (y : ℝ) : ℝ := y / (1 - |y|)

lemma one_add_abs_pos (x : ℝ) : (0 : ℝ) < 1 + |x| := by linarith [abs_nonneg x]

lemma one_sub_abs_pos {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : (0 : ℝ) < 1 - |y| := by
  linarith [abs_lt.mpr (show -1 < y ∧ y < 1 from ⟨by linarith [hy.1], hy.2⟩)]

lemma boundH_strictMono : StrictMono boundH := by
  intro a b hab; simp only [boundH]
  rw [div_lt_div_iff₀ (one_add_abs_pos a) (one_add_abs_pos b)]
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]; nlinarith
  · linarith
  · rw [abs_of_neg ha, abs_of_nonneg hb]; nlinarith
  · rw [abs_of_neg ha, abs_of_neg hb]; nlinarith

lemma boundH_mem_Ioo (x : ℝ) : boundH x ∈ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · simp only [boundH]; have h := one_add_abs_pos x
    rw [show (-1 : ℝ) = -(1 + |x|) / (1 + |x|) from by rw [neg_div_self h.ne']]
    exact div_lt_div_of_pos_right (by nlinarith [neg_abs_le x]) h
  · simp only [boundH]; rw [div_lt_one (one_add_abs_pos x)]; linarith [le_abs_self x]

lemma boundH_left_inv {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    boundH (boundH_inv y) = y := by
  have h1 := one_sub_abs_pos hy
  simp only [boundH, boundH_inv, abs_div, abs_of_pos h1]; field_simp; ring

lemma boundH_inv_strictMono_on : StrictMonoOn boundH_inv (Set.Ioo (-1 : ℝ) 1) := by
  intro a ha b hb hab; simp only [boundH_inv]
  rw [div_lt_div_iff₀ (one_sub_abs_pos ha) (one_sub_abs_pos hb)]
  rcases le_or_gt 0 a with ha' | ha' <;> rcases le_or_gt 0 b with hb' | hb'
  · rw [abs_of_nonneg ha', abs_of_nonneg hb']; nlinarith
  · linarith
  · rw [abs_of_neg (not_le.mp (not_le.mpr ha')), abs_of_nonneg hb']
    nlinarith [ha.1, hb.2, sq_nonneg (a + b)]
  · rw [abs_of_neg (not_le.mp (not_le.mpr ha')), abs_of_neg (not_le.mp (not_le.mpr hb'))]; nlinarith

/-- Between any two points in `(-1, 1)`, there is a rational `q` with `H(q)` strictly between. This
combines density of `ℚ` in `ℝ` with the `boundH`/`boundH_inv` round-trip. -/
lemma exists_rat_boundH_between (α β : ℝ)
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1) (hβ : β ∈ Set.Ioo (-1 : ℝ) 1) (hab : α < β) :
    ∃ q : ℚ, α < boundH (↑q) ∧ boundH (↑q) < β := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (boundH_inv_strictMono_on hα hβ hab)
  exact ⟨q, (boundH_left_inv hα).symm ▸ boundH_strictMono hq1,
         (boundH_left_inv hβ) ▸ boundH_strictMono hq2⟩

/-! ## Jump set

A jump in `Z` is a pair `(x, y)` with `x < y` and no element of `Z` strictly between them.
Jumps are the gaps that must be filled to make the augmented order dense. -/

/-- The set of jump pairs in `Z`: Pairs `(x, y)` with `x, y ∈ Z`, `x < y`, and `(x, y) ∩ Z = ∅`. -/
def JumpSet (Z : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Z ∧ p.2 ∈ Z ∧ p.1 < p.2 ∧ Set.Ioo p.1 p.2 ∩ Z = ∅}

/-! ## The augmented type

`ZAug Z` is the countable dense linear order without endpoints obtained by augmenting `Z`. It
has four constructors: `left q` and `right q` provide rational tails below and above all of `Z`
(eliminating min/max), while `fill j q` inserts rationals into each jump `j` (forcing density). The
original elements embed via `orig z`.

Cantor's isomorphism theorem applies to `ZAug Z` because it is countable, densely ordered, and has
no endpoints — exactly the hypotheses of `Order.iso_of_countable_dense`. -/

/-- ZAug extends Z with rational tails (removing endpoints) and rational fillers in each jump
(forcing density).

Constructors:

* `left q`   : Left tail, below all of Z
* `orig z`   : Original element of Z
* `fill j q`  : Rational filler in jump j
* `right q`  : Right tail, above all of Z -/
inductive ZAug (Z : Set ℝ) where
  | left (q : ℚ)
  | orig (z : ↥Z)
  | fill (j : ↥(JumpSet Z)) (q : ℚ)
  | right (q : ℚ)

namespace ZAug

variable {Z : Set ℝ}

/-- For z ∈ Z and a jump (x,y), z sits outside the open interval: Z ≤ x or y ≤ z. -/
lemma le_fst_or_snd_le (z : ↥Z) (j : ↥(JumpSet Z)) :
    (z : ℝ) ≤ j.val.1 ∨ j.val.2 ≤ (z : ℝ) := by
  by_contra h; push Not at h
  have : (z : ℝ) ∈ Set.Ioo j.val.1 j.val.2 ∩ Z := ⟨⟨h.1, h.2⟩, z.property⟩
  simp only [j.property.2.2.2, Set.mem_empty_iff_false] at this

/-! ## Strict order on ZAug

We define `lt'` by case-splitting on pairs of constructors (16 cases). The ordering places
`left < orig < right`, with `fill j _` sitting in the gap at jump `j` (between `orig j.1` and
`orig j.2`). Two fills of the same jump are compared by their rational parameter; fills of
different jumps are compared by the jump positions.

`le'` is then `a = b ∨ lt' a b`. The proofs of trichotomy, transitivity, and irreflexivity are
mechanical case analyzes. -/

/-- Strict order on `ZAug Z`, defined by constructor case analysis. -/
def lt' : ZAug Z → ZAug Z → Prop
  | .left q₁, .left q₂ => q₁ < q₂
  | .left _, .orig _ => True
  | .left _, .fill _ _ => True
  | .left _, .right _ => True
  | .orig _, .left _ => False
  | .orig z₁, .orig z₂ => (z₁ : ℝ) < z₂
  | .orig z, .fill j _ => (z : ℝ) ≤ j.val.1
  | .orig _, .right _ => True
  | .fill _ _, .left _ => False
  | .fill j _, .orig z => j.val.2 ≤ (z : ℝ)
  | .fill j₁ q₁, .fill j₂ q₂ =>
      if j₁.val = j₂.val then q₁ < q₂ else j₁.val.2 ≤ j₂.val.1
  | .fill _ _, .right _ => True
  | .right _, .left _ => False
  | .right _, .orig _ => False
  | .right _, .fill _ _ => False
  | .right q₁, .right q₂ => q₁ < q₂

@[simp] lemma lt'_left_left (q₁ q₂ : ℚ) : lt' (ZAug.left (Z:=Z) q₁) (.left q₂) ↔ q₁ < q₂ := Iff.rfl
@[simp] lemma lt'_left_orig (q : ℚ) (z : ↥Z) : lt' (ZAug.left (Z:=Z) q) (.orig z) ↔ True := Iff.rfl
@[simp] lemma lt'_left_fill (q₁ : ℚ) (j : ↥(JumpSet Z)) (q₂ : ℚ) :
  lt' (ZAug.left (Z:=Z) q₁) (.fill j q₂) ↔ True := Iff.rfl
@[simp] lemma lt'_left_right (q₁ q₂ : ℚ) :
  lt' (ZAug.left (Z:=Z) q₁) (.right q₂) ↔ True := Iff.rfl
@[simp] lemma lt'_orig_left (z : ↥Z) (q : ℚ) :
  lt' (ZAug.orig (Z:=Z) z) (.left q) ↔ False := Iff.rfl
@[simp] lemma lt'_orig_orig (z₁ z₂ : ↥Z) :
  lt' (ZAug.orig (Z:=Z) z₁) (.orig z₂) ↔ (z₁ : ℝ) < z₂ := Iff.rfl
@[simp] lemma lt'_orig_fill (z : ↥Z) (j : ↥(JumpSet Z)) (q : ℚ) :
  lt' (ZAug.orig (Z:=Z) z) (.fill j q) ↔ (z : ℝ) ≤ j.val.1 := Iff.rfl
@[simp] lemma lt'_orig_right (z : ↥Z) (q : ℚ) :
  lt' (ZAug.orig (Z:=Z) z) (.right q) ↔ True := Iff.rfl
@[simp] lemma lt'_fill_left (j : ↥(JumpSet Z)) (q₁ q₂ : ℚ) :
  lt' (ZAug.fill (Z:=Z) j q₁) (.left q₂) ↔ False := Iff.rfl
@[simp] lemma lt'_fill_orig (j : ↥(JumpSet Z)) (q : ℚ) (z : ↥Z) :
  lt' (ZAug.fill (Z:=Z) j q) (.orig z) ↔ j.val.2 ≤ (z : ℝ) := Iff.rfl
@[simp] lemma lt'_fill_fill (j₁ j₂ : ↥(JumpSet Z)) (q₁ q₂ : ℚ) :
  lt' (ZAug.fill (Z:=Z) j₁ q₁) (.fill j₂ q₂) ↔
    if j₁.val = j₂.val then q₁ < q₂ else j₁.val.2 ≤ j₂.val.1 := Iff.rfl
@[simp] lemma lt'_fill_right (j : ↥(JumpSet Z)) (q₁ q₂ : ℚ) :
  lt' (ZAug.fill (Z:=Z) j q₁) (.right q₂) ↔ True := Iff.rfl
@[simp] lemma lt'_right_left (q₁ q₂ : ℚ) :
  lt' (ZAug.right (Z:=Z) q₁) (.left q₂) ↔ False := Iff.rfl
@[simp] lemma lt'_right_orig (q : ℚ) (z : ↥Z) :
  lt' (ZAug.right (Z:=Z) q) (.orig z) ↔ False := Iff.rfl
@[simp] lemma lt'_right_fill (q₁ : ℚ) (j : ↥(JumpSet Z)) (q₂ : ℚ) :
  lt' (ZAug.right (Z:=Z) q₁) (.fill j q₂) ↔ False := Iff.rfl
@[simp] lemma lt'_right_right (q₁ q₂ : ℚ) :
  lt' (ZAug.right (Z:=Z) q₁) (.right q₂) ↔ q₁ < q₂ := Iff.rfl

/-- Non-strict order: Equality or `lt'`. -/
def le' (a b : ZAug Z) : Prop := a = b ∨ lt' a b

/-! ### Trichotomy, transitivity, and irreflexivity

The core order-theoretic properties of `lt'` needed to assemble the `LinearOrder` instance. -/

lemma lt'_trichotomy (a b : ZAug Z) : lt' a b ∨ a = b ∨ lt' b a := by
  cases a <;> cases b <;>
    first | exact Or.inl trivial | exact Or.inr (Or.inr trivial) | skip
  -- left-left / right-right: rational trichotomy
  · next q₁ q₂ => simpa [lt'] using lt_trichotomy q₁ q₂
  -- orig-orig: real trichotomy on coercions
  · next z₁ z₂ =>
    rcases lt_trichotomy (z₁ : ℝ) z₂ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (congr_arg ZAug.orig (Subtype.ext h)))
    · exact Or.inr (Or.inr h)
  -- orig-fill / fill-orig: le_fst_or_snd_le
  · next z j _ =>
    rcases le_fst_or_snd_le z j with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · next j _ z =>
    rcases le_fst_or_snd_le z j with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  -- fill-fill: by_cases on jump equality, then rational trichotomy or le_fst_or_snd_le
  · next j₁ q₁ j₂ q₂ =>
    by_cases hj : j₁.val = j₂.val
    · have hsub : j₁ = j₂ := Subtype.ext hj; subst hsub
      simpa [lt'] using lt_trichotomy q₁ q₂
    · simp only [lt']; rw [if_neg hj, if_neg (fun h => hj h.symm)]
      rcases le_fst_or_snd_le ⟨j₁.val.2, j₁.property.2.1⟩ j₂ with h | h
      · exact Or.inl h
      · rcases le_fst_or_snd_le ⟨j₂.val.2, j₂.property.2.1⟩ j₁ with h' | h'
        · exact Or.inr (Or.inr h')
        · rcases le_fst_or_snd_le ⟨j₁.val.1, j₁.property.1⟩ j₂ with h₃ | h₃
          · rcases le_fst_or_snd_le ⟨j₂.val.1, j₂.property.1⟩ j₁ with h₄ | h₄
            · exact absurd (Prod.ext (le_antisymm h₃ h₄) (le_antisymm h' h)) hj
            · exact Or.inl h₄
          · exact Or.inr (Or.inr h₃)
  · next q₁ q₂ => simpa [lt'] using lt_trichotomy q₁ q₂

lemma fill_fill_lt'_trans {j₁ j₂ j₃ : ↥(JumpSet Z)} {q₁ q₂ q₃ : ℚ}
    (h1 : lt' (.fill j₁ q₁) (.fill j₂ q₂))
    (h2 : lt' (.fill j₂ q₂) (.fill j₃ q₃)) :
    lt' (.fill j₁ q₁) (.fill j₃ q₃) := by
  simp only [lt'_fill_fill] at *
  by_cases h12 : j₁.val = j₂.val <;> by_cases h23 : j₂.val = j₃.val <;>
    simp only [h12, h23, ite_true, ite_false] at h1 h2
  · rw [if_pos (h12.trans h23)]; exact lt_trans h1 h2
  · rw [if_neg (fun h => h23 (h12.symm.trans h))]; linarith [congrArg Prod.snd h12]
  · have h13 : j₁.val ≠ j₃.val := fun h => h12 (h.trans h23.symm)
    rw [if_neg h13]; simp only [h13, ite_false] at h1; linarith [congrArg Prod.fst h23]
  · by_cases h13 : j₁.val = j₃.val
    · exfalso; linarith [congrArg Prod.fst h13, j₁.property.2.2.1, j₂.property.2.2.1]
    · rw [if_neg h13]; linarith [j₂.property.2.2.1]

/-- Transitivity of lt'. -/
lemma lt'_trans {a b c : ZAug Z} : lt' a b → lt' b c → lt' a c := by
  intro h1 h2
  cases a <;> cases b <;> cases c <;> simp only [lt'] at * <;>
    first | trivial | contradiction | exact lt_trans h1 h2 | linarith | skip
  -- 5 remaining goals involve jumps; extract j.property.2.2.1 and use linarith
  · next _ j _ _ => linarith [j.property.2.2.1]
  · next _ j₁ _ j₂ _  =>
    split_ifs at h2 with heq
    · linarith [congrArg Prod.fst heq]
    · linarith [j₁.property.2.2.1]
  · next j₁ _ _ j₂ _ =>
    split_ifs with heq
    · exfalso; linarith [j₁.property.2.2.1, congrArg Prod.fst heq]
    · linarith
  · next j₁ _ j₂ _ _ =>
    split_ifs at h1 with heq
    · linarith [congrArg Prod.snd heq]
    · linarith [j₂.property.2.2.1]
  · next j₁ _ j₂ _ j₃ _ =>
    exact fill_fill_lt'_trans (by simp only [lt'_fill_fill]; exact h1)
      (by simp only [lt'_fill_fill]; exact h2)

/-- Irreflexivity of lt'. -/
lemma lt'_irrefl (a : ZAug Z) : ¬lt' a a := by cases a <;> simp [lt']

/-! ## LinearOrder instance -/

instance linearOrder : LinearOrder (ZAug Z) where
  le := le'
  lt := lt'
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h1 h2 := by
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · exact Or.inl rfl
    · exact Or.inr h2
    · exact Or.inr h1
    · exact Or.inr (lt'_trans h1 h2)
  le_antisymm _ _ h1 h2 := by
    rcases h1 with rfl | h1; · rfl
    rcases h2 with rfl | h2; · rfl
    exact absurd (lt'_trans h1 h2) (lt'_irrefl _)
  le_total a b := by
    rcases lt'_trichotomy a b with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
  lt_iff_le_not_ge a b :=
    ⟨fun h => ⟨Or.inr h, fun h' => by
      rcases h' with rfl | h'
      · exact lt'_irrefl _ h
      · exact lt'_irrefl _ (lt'_trans h h')⟩,
    fun ⟨h1, h2⟩ => by
      rcases h1 with rfl | h
      · exact absurd (Or.inl rfl) h2
      · exact h⟩
  toDecidableLE := fun _ _ => Classical.dec _
  toDecidableEq := fun _ _ => Classical.dec _
  toDecidableLT := fun _ _ => Classical.dec _

/-! ## Typeclass instances for Cantor's theorem

To apply `Order.iso_of_countable_dense`, `ZAug Z` must be `Countable`, `DenselyOrdered`,
`NoMinOrder`, `NoMaxOrder`, and `Nonempty`. Countability follows from the disjoint-sum encoding
`ℚ ⊕ Z ⊕ (JumpSet Z × ℚ) ⊕ ℚ`. The tails give no-min/no-max, and density is the interesting case:
Between two `orig` elements with no `orig` between them, their jump filler provides the witness. -/

/-- ZAug is countable: Disjoint union of ℚ, ↥Z, ↥(JumpSet Z) × ℚ, ℚ. -/
instance countable [Countable ↥Z] [Countable ↥(JumpSet Z)] :
    Countable (ZAug Z) := by
  apply Countable.of_equiv (ℚ ⊕ ↥Z ⊕ (↥(JumpSet Z) × ℚ) ⊕ ℚ)
  refine ⟨fun
      | .inl q => .left q
      | .inr (.inl z) => .orig z
      | .inr (.inr (.inl (j, q))) => .fill j q
      | .inr (.inr (.inr q)) => .right q,
    fun
      | .left q => .inl q
      | .orig z => .inr (.inl z)
      | .fill j q => .inr (.inr (.inl (j, q)))
      | .right q => .inr (.inr (.inr q)),
    fun x => by rcases x with q | z | ⟨j, q⟩ | q <;> rfl,
    fun x => by cases x <;> rfl⟩

instance nonempty : Nonempty (ZAug Z) := ⟨ZAug.left 0⟩

/-- `ZAug Z` has no minimum: The left tail extends below every element. -/
instance noMinOrder : NoMinOrder (ZAug Z) where
  exists_lt a := by
    match a with
    | .left q => exact ⟨.left (q - 1), show q - 1 < q by linarith⟩
    | .orig _ => exact ⟨.left 0, trivial⟩
    | .fill _ _ => exact ⟨.left 0, trivial⟩
    | .right _ => exact ⟨.left 0, trivial⟩

/-- `ZAug Z` has no maximum: The right tail extends above every element. -/
instance noMaxOrder : NoMaxOrder (ZAug Z) where
  exists_gt a := by
    match a with
    | .right q => exact ⟨.right (q + 1), show q < q + 1 by linarith⟩
    | .orig _ => exact ⟨.right 0, trivial⟩
    | .fill _ _ => exact ⟨.right 0, trivial⟩
    | .left _ => exact ⟨.right 0, trivial⟩

/-- `ZAug Z` is densely ordered: Between any two elements lies a third. -/
instance denselyOrdered : DenselyOrdered (ZAug Z) where
  dense a b hab := by
    match a, b with
    | .left q₁, .left q₂ =>
      obtain ⟨m, hm⟩ := exists_between (show q₁ < q₂ from hab)
      exact ⟨.left m, hm.1, hm.2⟩
    | .left q₁, .orig _ =>
      exact ⟨.left (q₁ + 1), show q₁ < q₁ + 1 by linarith, trivial⟩
    | .left q₁, .fill _ _ =>
      exact ⟨.left (q₁ + 1), show q₁ < q₁ + 1 by linarith, trivial⟩
    | .left q₁, .right _ =>
      exact ⟨.left (q₁ + 1), show q₁ < q₁ + 1 by linarith, trivial⟩
    | .orig z₁, .orig z₂ =>
      by_cases hgap : Set.Ioo (z₁ : ℝ) (z₂ : ℝ) ∩ Z = ∅
      · have hj : ((z₁ : ℝ), (z₂ : ℝ)) ∈ JumpSet Z :=
          ⟨z₁.property, z₂.property, hab, hgap⟩
        exact ⟨.fill ⟨_, hj⟩ 0,
               show (z₁ : ℝ) ≤ ((z₁ : ℝ), (z₂ : ℝ)).1 from le_refl _,
               show ((z₁ : ℝ), (z₂ : ℝ)).2 ≤ (z₂ : ℝ) from le_refl _⟩
      · rw [Set.eq_empty_iff_forall_notMem] at hgap; push Not at hgap
        obtain ⟨r, hr_ioo, hr_Z⟩ := hgap
        exact ⟨.orig ⟨r, hr_Z⟩, hr_ioo.1, hr_ioo.2⟩
    | .orig _, .fill j q =>
      refine ⟨.fill j (q - 1), hab, ?_⟩
      exact (lt'_fill_fill j j (q - 1) q).2 <| by
        simp only [↓reduceIte, sub_lt_self_iff, zero_lt_one]
    | .orig _, .right q =>
      exact ⟨.right (q - 1), trivial, show q - 1 < q by linarith⟩
    | .fill j q, .orig _ =>
      refine ⟨.fill j (q + 1), ?_, hab⟩
      exact (lt'_fill_fill j j q (q + 1)).2 <| by
        simp only [↓reduceIte, lt_add_iff_pos_right, zero_lt_one]
    | .fill j₁ q₁, .fill j₂ q₂ =>
      by_cases heq : j₁.val = j₂.val
      · have hsub : j₁ = j₂ := Subtype.ext heq; subst hsub
        have hlt : q₁ < q₂ := by
          simpa [if_pos rfl] using (lt'_fill_fill j₁ j₁ q₁ q₂).1 hab
        obtain ⟨m, hm⟩ := exists_between hlt
        refine ⟨.fill j₁ m, ?_, ?_⟩
        · exact (lt'_fill_fill j₁ j₁ q₁ m).2 <| by
            simpa [if_pos rfl] using hm.1
        · exact (lt'_fill_fill j₁ j₁ m q₂).2 <| by
            simpa [if_pos rfl] using hm.2
      · have hle : j₁.val.2 ≤ j₂.val.1 := by
          simpa [heq] using (lt'_fill_fill j₁ j₂ q₁ q₂).1 hab
        let z : ↥Z := ⟨j₂.val.1, j₂.property.1⟩
        refine ⟨.orig z, ?_, ?_⟩
        · exact (lt'_fill_orig j₁ q₁ z).2 hle
        · exact (lt'_orig_fill z j₂ q₂).2 le_rfl
    | .fill _ _, .right q =>
      exact ⟨.right (q - 1), trivial, show q - 1 < q by linarith⟩
    | .right q₁, .right q₂ =>
      obtain ⟨m, hm⟩ := exists_between (show q₁ < q₂ from hab)
      exact ⟨.right m, hm.1, hm.2⟩

/-! ## Order embedding Z ↪o ZAug

The `orig` constructor gives an order embedding `Z ↪o ZAug Z`. This is the inclusion through
which we restrict the final map `g : ZAug Z → ℝ` to obtain `f : Z → ℝ`. -/

/-- The canonical order embedding of Z into ZAug. -/
def origEmb : ↥Z ↪o ZAug Z where
  toFun := ZAug.orig
  inj' := by intro a b h; cases h; rfl
  map_rel_iff' := by
    intro a b
    change le' (ZAug.orig a) (ZAug.orig b) ↔ a ≤ b
    simp only [le', lt', ZAug.orig.injEq]
    constructor
    · rintro (rfl | h)
      · exact le_refl _
      · exact Subtype.coe_le_coe.mp (le_of_lt h)
    · intro h
      rcases eq_or_lt_of_le (Subtype.coe_le_coe.mpr h) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr h

/-! ## Constructing f via boundH ∘ ↑ ∘ cantorIso ∘ orig

With all typeclass instances in place, `Order.iso_of_countable_dense` gives
`cantorIso : ZAug Z ≃o ℚ`. The extended map `boundedMap = H ∘ ↑ ∘ cantorIso : ZAug Z → (-1, 1)` is
strictly monotone and has dense range in `(-1, 1)` (since `ℚ` is dense and `H` is a homeomorphism).
The utility function `constructF` restricts `boundedMap` to `Z` via `orig`. -/

/-- The Cantor isomorphism `cantorIso : ZAug Z ≃o ℚ`, obtained from
`Order.iso_of_countable_dense`. -/
def cantorIso (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)] : ZAug Z ≃o ℚ :=
  (Order.iso_of_countable_dense (ZAug Z) ℚ).some

/-- The bounded strictly-monotone map `ZAug Z → ℝ`, defined as `H(↑(cantorIso w))`; its range lies
in `(-1, 1)`. -/
def boundedMap (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)] (w : ZAug Z) : ℝ :=
  boundH (↑(cantorIso Z w))

/-- `f : Z → ℝ`, the restriction of `boundedMap` to `orig(Z)`. -/
def constructF (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)] (z : ↥Z) : ℝ :=
  boundedMap Z (.orig z)

lemma boundedMap_strictMono (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)] :
    StrictMono (boundedMap Z) :=
  fun _ _ h => boundH_strictMono (Rat.cast_lt.mpr ((cantorIso Z).strictMono h))

lemma boundedMap_mem_Ioo (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)]
    (w : ZAug Z) : boundedMap Z w ∈ Set.Ioo (-1 : ℝ) 1 := boundH_mem_Ioo _

lemma boundedMap_dense (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)]
    (α β : ℝ) (hα : α ∈ Set.Ioo (-1 : ℝ) 1) (hβ : β ∈ Set.Ioo (-1 : ℝ) 1) (hab : α < β) :
    ∃ w : ZAug Z, α < boundedMap Z w ∧ boundedMap Z w < β := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_boundH_between α β hα hβ hab
  exact ⟨(cantorIso Z).symm q, by
    simp only [boundedMap, OrderIso.apply_symm_apply]; exact ⟨hq1, hq2⟩⟩

lemma constructF_strictMono (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)] :
    StrictMono (constructF Z) :=
  fun _ _ h => boundedMap_strictMono Z (origEmb.strictMono h)

lemma constructF_bounded (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)]
    (z : ↥Z) : constructF Z z ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := boundedMap_mem_Ioo Z (.orig z); exact ⟨h.1.le, h.2.le⟩

/-! ## The no-gap property

The central property of `constructF`: For any Dedekind cut `A ∪ B = Z` with `A < B` where `A`
has no maximum or `B` no minimum, `sSup f(A) = sInf f(B)`. -/

/-- If `w : ZAug Z` lies strictly between all of `A` and all of `B`, then `A` has a maximum and `B`
has a minimum (only the `fill` constructor survives the case analysis). -/
lemma fill_forces_max_min
    (A B : Set ↥Z)
    (hunion : A ∪ B = Set.univ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (w : ZAug Z)
    (hw_above_A : ∀ a ∈ A, lt' (.orig a) w)
    (hw_below_B : ∀ b ∈ B, lt' w (.orig b)) :
    (∃ a ∈ A, ∀ a' ∈ A, (a' : ℝ) ≤ a) ∧
    (∃ b ∈ B, ∀ b' ∈ B, (b : ℝ) ≤ b') := by
  match w with
  | .left _ =>
    obtain ⟨a, ha⟩ := hA
    exact absurd (hw_above_A a ha) (by simp [lt'])
  | .right _ =>
    obtain ⟨b, hb⟩ := hB
    exact absurd (hw_below_B b hb) (by simp [lt'])
  | .orig z =>
    have hz : z ∈ A ∨ z ∈ B := by
      simpa [← hunion] using Set.mem_univ z
    rcases hz with ha | hb
    · exact absurd (hw_above_A z ha) (by simp [lt'])
    · exact absurd (hw_below_B z hb) (by simp [lt'])
  | .fill j q =>
    have hj1_mem : (⟨j.val.1, j.property.1⟩ : ↥Z) ∈ A ∨
                   (⟨j.val.1, j.property.1⟩ : ↥Z) ∈ B := by
      simpa [← hunion] using  Set.mem_univ (⟨j.val.1, j.property.1⟩ : ↥Z)
    have hj2_mem : (⟨j.val.2, j.property.2.1⟩ : ↥Z) ∈ A ∨
                   (⟨j.val.2, j.property.2.1⟩ : ↥Z) ∈ B := by
      simpa [← hunion] using (Set.mem_univ (⟨j.val.2, j.property.2.1⟩ : ↥Z))
    have hj1_A : (⟨j.val.1, j.property.1⟩ : ↥Z) ∈ A := by
      rcases hj1_mem with h | h
      · exact h
      · exfalso; have := hw_below_B _ h
        simp [lt'] at this; linarith [j.property.2.2.1]
    have hj2_B : (⟨j.val.2, j.property.2.1⟩ : ↥Z) ∈ B := by
      rcases hj2_mem with h | h
      · exfalso; have := hw_above_A _ h
        simp [lt'] at this; linarith [j.property.2.2.1]
      · exact h
    exact ⟨⟨⟨j.val.1, j.property.1⟩, hj1_A, hw_above_A⟩,
           ⟨⟨j.val.2, j.property.2.1⟩, hj2_B, hw_below_B⟩⟩

lemma noGap_aux (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)]
    (A B : Set ↥Z)
    (hunion : A ∪ B = Set.univ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h_strict : sSup (constructF Z '' A) < sInf (constructF Z '' B)) :
    (∃ a ∈ A, ∀ a' ∈ A, (a' : ℝ) ≤ a) ∧
    (∃ b ∈ B, ∀ b' ∈ B, (b : ℝ) ≤ b') := by
  -- Bounds
  obtain ⟨a₀, ha₀⟩ := hA; obtain ⟨b₀, hb₀⟩ := hB
  have hbddA : BddAbove (constructF Z '' A) :=
    ⟨1, fun y ⟨z, _, hz⟩ => hz ▸ (constructF_bounded Z z).2⟩
  have hbddB : BddBelow (constructF Z '' B) :=
    ⟨-1, fun y ⟨z, _, hz⟩ => hz ▸ (constructF_bounded Z z).1⟩
  have hsup_mem : sSup (constructF Z '' A) ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le (boundedMap_mem_Ioo Z (.orig a₀)).1 (le_csSup hbddA ⟨a₀, ha₀, rfl⟩)
    · have hlt_b₀ : sSup (constructF Z '' A) < constructF Z b₀ :=
        lt_of_lt_of_le h_strict (csInf_le hbddB ⟨b₀, hb₀, rfl⟩)
      exact lt_trans hlt_b₀ (boundedMap_mem_Ioo Z (.orig b₀)).2
  have hinf_mem : sInf (constructF Z '' B) ∈ Set.Ioo (-1 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact lt_trans hsup_mem.1 h_strict
    · exact lt_of_le_of_lt
        (csInf_le hbddB ⟨b₀, hb₀, rfl⟩)
        (boundedMap_mem_Ioo Z (.orig b₀)).2
  -- Find w
  obtain ⟨w, hw_gt, hw_lt⟩ := boundedMap_dense Z _ _ hsup_mem hinf_mem h_strict
  -- w is between all of A and all of B
  have hw_above_A : ∀ a ∈ A, lt' (.orig a) w := by
    intro a ha
    by_contra h_not
    rcases lt'_trichotomy (.orig a) w with h | rfl | h
    · exact h_not h
    · linarith [(le_csSup hbddA ⟨a, ha, rfl⟩ :
        boundedMap Z (.orig a) ≤ sSup (constructF Z '' A))]
    · linarith [boundedMap_strictMono Z h, (le_csSup hbddA ⟨a, ha, rfl⟩ :
        boundedMap Z (.orig a) ≤ sSup (constructF Z '' A))]
  have hw_below_B : ∀ b ∈ B, lt' w (.orig b) := by
    intro b hb
    by_contra h_not
    rcases lt'_trichotomy w (.orig b) with h | rfl | h
    · exact h_not h
    · linarith [(csInf_le hbddB ⟨b, hb, rfl⟩ :
        sInf (constructF Z '' B) ≤ boundedMap Z (.orig b))]
    · linarith [boundedMap_strictMono Z h, (csInf_le hbddB ⟨b, hb, rfl⟩ :
        sInf (constructF Z '' B) ≤ boundedMap Z (.orig b))]
  -- Lemma C
  exact fill_forces_max_min A B hunion ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ w hw_above_A hw_below_B

/-- The no-gap property: For a Dedekind cut `A ∪ B = Z` with `A < B` where `A` has no maximum or
`B` has no minimum, `sSup f(A) = sInf f(B)`. -/
lemma noGap (Z : Set ℝ) [Countable ↥Z] [Countable ↥(JumpSet Z)]
    (A B : Set ↥Z)
    (hunion : A ∪ B = Set.univ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hlt : ∀ a ∈ A, ∀ b ∈ B, (a : ℝ) < b)
    (hnomax_or_nomin : (∀ a ∈ A, ∃ a' ∈ A, (a : ℝ) < a') ∨ (∀ b ∈ B, ∃ b' ∈ B, (b' : ℝ) < b)) :
    sSup (constructF Z '' A) = sInf (constructF Z '' B) := by
  -- Step 1: sSup ≤ sInf
  have h_le : sSup (constructF Z '' A) ≤ sInf (constructF Z '' B) := by
    apply csSup_le (hA.image _)
    intro y hy; obtain ⟨a, ha, rfl⟩ := hy
    apply le_csInf (hB.image _)
    intro y' hy'; obtain ⟨b, hb, rfl⟩ := hy'
    exact le_of_lt (constructF_strictMono Z (Subtype.coe_lt_coe.mp (hlt a ha b hb)))
  -- Step 2: Assume strict inequality for contradiction
  by_contra h_ne
  have h_strict : sSup (constructF Z '' A) < sInf (constructF Z '' B) :=
    lt_of_le_of_ne h_le h_ne
  obtain ⟨hmax, hmin⟩ := noGap_aux Z A B hunion hA hB h_strict
  rcases hnomax_or_nomin with hnomax | hnomin
  · rcases hmax with ⟨a, haA, hmaxA⟩
    rcases hnomax a haA with ⟨a', ha'A, haa'⟩
    exact (not_lt_of_ge (hmaxA a' ha'A)) haa'
  · rcases hmin with ⟨b, hbB, hminB⟩
    rcases hnomin b hbB with ⟨b', hb'B, hbb'⟩
    exact (not_lt_of_ge (hminB b' hb'B)) hbb'

lemma jumpSet_countable (Z : Set ℝ) : (JumpSet Z).Countable := by
  have H : ∀ p : ↥(JumpSet Z), ∃ q : ℚ, (p : ℝ × ℝ).1 < (q : ℝ) ∧ (q : ℝ) < (p : ℝ × ℝ).2 :=
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

/-! ## Main interface

Packages `constructF_strictMono`, `constructF_bounded`, and `noGap` into the single existential
statement consumed by `exists_strictMono_hasAllOpenGaps_range` in `GapFilling.lean`. -/

/-- The bounded strictly increasing function with the no-gap property, packaged for consumption by
the open gap lemma. -/
theorem exists_strictMono_bounded_noGap (Z : Set ℝ) (hZ_count : Z.Countable) :
    ∃ f : ↥Z → ℝ,
      StrictMono f ∧
      (∀ z : ↥Z, f z ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∀ (A B : Set ↥Z),
        A ∪ B = Set.univ →
        A.Nonempty →
        B.Nonempty →
        (∀ a ∈ A, ∀ b ∈ B, (a : ℝ) < b) →
        (∀ a ∈ A, ∃ a' ∈ A, (a : ℝ) < a') ∨ (∀ b ∈ B, ∃ b' ∈ B, (b' : ℝ) < b) →
        sSup (f '' A) = sInf (f '' B)) := by
  haveI : Countable ↥Z := hZ_count.to_subtype
  haveI : Countable ↥(JumpSet Z) := by
    apply Set.Countable.to_subtype
    apply Set.Countable.mono _ (hZ_count.prod hZ_count)
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  exact ⟨constructF Z, constructF_strictMono Z, constructF_bounded Z, noGap Z⟩

end ZAug
end DebreuGap
