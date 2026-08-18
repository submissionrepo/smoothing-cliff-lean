/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Logic.Basic

/-!
# Heterogeneous reduction of dependent `Option.rec`

A dependent recursor `Option.rec` applied to its own scrutinee `x : Option α` reduces, up to
heterogeneous equality, to the appropriate branch once the scrutinee is known to be `some c` or
`none`. These are the bridge lemmas used when rewriting dependent navigators whose motive depends
on the equality proof `x = t`.

## Main results

* `Option.rec_apply_heq_some` — reduction to the `some` branch when `x = some c`.
* `Option.rec_apply_heq_none` — reduction to the `none` branch when `x = none`.

## Tags

option, dependent recursor, heterogeneous equality
-/

@[expose] public section

namespace Option

/-- A dependent `Option.rec` applied to its own scrutinee reduces, up to heterogeneous equality, to
the `some` branch when the scrutinee is known to be `some c`. -/
theorem rec_apply_heq_some
    {α : Type u} {C : Option α → Sort v}
    {x : Option α} {c : α}
    (noneBranch : x = none → C x)
    (someBranch : (a : α) → x = some a → C x)
    (h : x = some c) :
    HEq
      (Option.rec
        (motive := fun t : Option α => x = t → C x)
        noneBranch
        someBranch
        x rfl)
      (someBranch c h) := by
  cases h
  rfl

/-- A dependent `Option.rec` applied to its own scrutinee reduces, up to heterogeneous equality, to
the `none` branch when the scrutinee is known to be `none`. -/
theorem rec_apply_heq_none
    {α : Type u} {C : Option α → Sort v}
    {x : Option α}
    (noneBranch : x = none → C x)
    (someBranch : (a : α) → x = some a → C x)
    (h : x = none) :
    HEq
      (Option.rec
        (motive := fun t : Option α => x = t → C x)
        noneBranch
        someBranch
        x rfl)
      (noneBranch h) := by
  cases h
  rfl

end Option
