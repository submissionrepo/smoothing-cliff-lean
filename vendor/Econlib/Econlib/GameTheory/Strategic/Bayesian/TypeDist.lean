/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Simplex

/-!
# Type Distributions

A common prior over dependent type profiles for a Bayesian game (Harsanyi 1967–68) is a finite
distribution on the dependent product of player type spaces. `TypeDist` is an abbreviation for
`FinDist (Π i, Theta i)` so that game signatures read in domain language and the component-space
instances assemble the product instances in one place.

## Main definitions

* `TypeDist`: A common prior over type profiles, as a `FinDist` on the dependent product.

## Notes

All API comes from the carrier `FinDist`. Pointwise mass is function application, player marginals
are `FinDist.marginalD`, and the player-type conditional is `FinDist.condProbD` (pointwise, junk
value zero at zero-marginal types). The distribution-valued conditional is
`FinDist.conditionalOnOrSelf` (junk value the prior at zero-mass events), while
`FinDist.conditionalOn` gates on positive event mass.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, common prior, type distribution
-/

@[expose] public section

open Econlib.Probability

namespace Econlib.GameTheory

/-- Joint distribution over a dependent product of finite types: The common prior over type
profiles in a Bayesian game. Abbreviation for `FinDist (Π i, Theta i)`. -/
abbrev TypeDist (I : Type*) [Fintype I] [DecidableEq I]
    (Theta : I → Type*) [∀ i, Fintype (Theta i)] [∀ i, DecidableEq (Theta i)] :=
  FinDist (Π i, Theta i)

end Econlib.GameTheory
