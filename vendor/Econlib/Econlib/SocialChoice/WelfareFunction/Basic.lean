/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic

/-!
# Social welfare functions

A `WelfareFunction Voter Alt` aggregates a preference profile into a social weak preference
relation. The `domain` field carries the set of admissible profiles, supporting axiomatic
hypotheses such as universal domain.

## Main definitions

* `WelfareFunction`: A social welfare function with a domain of admissible profiles and an
  aggregation rule.
* `WelfareFunction.socialLE`: Society weakly prefers `x` to `y` under a given profile.
* `WelfareFunction.socialLT`: Society strictly prefers `x` to `y` under a given profile.
* `WelfareFunction.socialIndiff`: Society is indifferent between `x` and `y` under a given profile.

## Tags

social welfare function, preference aggregation, social choice
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

/-- A social welfare function aggregates a profile of individual preferences into a single social
preference. The `domain` field carries the admissible profiles. -/
structure WelfareFunction (Voter Alt : Type*) where
  /-- The admissible set of profiles. -/
  domain : Set (Profile Voter Alt)
  /-- The aggregation rule. Only meaningful for `P ∈ domain`. -/
  aggregate : Profile Voter Alt → PreferenceRel Alt

namespace WelfareFunction

variable {Voter Alt : Type*} (f : WelfareFunction Voter Alt)

/-- Society weakly prefers `x` to `y` under profile `P`. -/
def socialLE (P : Profile Voter Alt) (x y : Alt) : Prop :=
  x ≽[f.aggregate P] y

/-- Society strictly prefers `x` to `y` under profile `P`. -/
def socialLT (P : Profile Voter Alt) (x y : Alt) : Prop :=
  x ≻[f.aggregate P] y

/-- Society is indifferent between `x` and `y` under profile `P`. -/
def socialIndiff (P : Profile Voter Alt) (x y : Alt) : Prop :=
  (x ~[f.aggregate P] y)

end WelfareFunction

end Econlib.SocialChoice
