/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic

/-!
# Profile domains

The admissible domain of a social-welfare or social-choice function is a set of profiles. Two
domains recur throughout the social-choice development: The **universal domain** of all profiles
and the **strict-orders domain** of profiles in which every voter has a strict preference.

## Main definitions

* `universalDomain` — the unrestricted set of all profiles.
* `strictDomain` — the profiles in which every ranking has no nontrivial indifference.

## Main statements

* `mem_universalDomain`, `mem_strictDomain` — membership unfoldings for the two domains.
* `strictDomain_subset_universalDomain` — the strict-orders domain is contained in the universal
  domain.

## Notes

The universal-domain form of Arrow's theorem (Arrow 1963), `arrow_impossibility`, is stated under
the richness hypothesis `universalDomain ⊆ f.domain`. The strict-orders form
`arrow_impossibility_strict_domain` and the Gibbard–Satterthwaite theorem (Gibbard 1973;
Satterthwaite 1975), `gibbard_satterthwaite`, are stated under `f.domain = strictDomain`.

## References

* Arrow, Kenneth J. 1963. *Social Choice and Individual Values*. 2nd ed. Wiley.
* Gibbard, Allan. 1973. “Manipulation of Voting Schemes: A General Result.” *Econometrica* 41 (4):
  587. [https://doi.org/10.2307/1914083](https://doi.org/10.2307/1914083).
* Satterthwaite, Mark Allen. 1975. “Strategy-Proofness and Arrow's Conditions: Existence and
  Correspondence Theorems for Voting Procedures and Social Welfare Functions.” *Journal of Economic
  Theory* 10 (2): 187–217. [https://doi.org/10.1016/0022-0531(75)90050-2](https://doi.org/10.1016/0022-0531(75)90050-2).

## Tags

social choice, profile domain, universal domain, strict orders, arrow, gibbard-satterthwaite
-/

@[expose] public section

namespace Econlib.SocialChoice

variable (Voter Alt : Type*)

/-- The unrestricted domain: Every profile is admissible. -/
def universalDomain : Set (Profile Voter Alt) := Set.univ

/-- The strict-orders domain: Profiles in which every ranking has no nontrivial indifference. -/
def strictDomain : Set (Profile Voter Alt) := { P | Profile.IsStrict P }

variable {Voter Alt}

@[simp] lemma mem_universalDomain (P : Profile Voter Alt) :
    P ∈ universalDomain Voter Alt := Set.mem_univ _

@[simp] lemma mem_strictDomain {P : Profile Voter Alt} :
    P ∈ strictDomain Voter Alt ↔ Profile.IsStrict P := Iff.rfl

lemma strictDomain_subset_universalDomain :
    strictDomain Voter Alt ⊆ universalDomain Voter Alt :=
  fun _ _ => Set.mem_univ _

end Econlib.SocialChoice
