/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic

/-!
# Social choice functions

This file defines `ChoiceFunction`, a bundled type representing a social choice function that maps
preference profiles to a nonempty set of winning alternatives. Returning a `Set Alt` rather than a
single `Alt` allows the function to express ties; a rule whose winner set is always a singleton is
*resolute*.

## Main definitions

* `ChoiceFunction`: A social choice function on a specified admissible domain of profiles, carrying
  the winner correspondence and a proof that the winner set is nonempty on every admissible profile.

## Tags

social choice, choice function, voting
-/

@[expose] public section

namespace Econlib.SocialChoice

/-- A social choice function mapping preference profiles to a nonempty set of winning alternatives,
defined on an admissible domain of profiles. -/
structure ChoiceFunction (Voter Alt : Type*) where
  /-- The admissible set of profiles. -/
  domain : Set (Profile Voter Alt)
  /-- The (possibly multi-element) set of winners. -/
  winners : Profile Voter Alt → Set Alt
  /-- At least one alternative wins on every admissible profile. -/
  winners_nonempty : ∀ P ∈ domain, (winners P).Nonempty

end Econlib.SocialChoice
