/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Arrow
public import Econlib.SocialChoice.ChoiceFunction.Basic
public import Econlib.SocialChoice.ChoiceFunction.Properties
public import Econlib.SocialChoice.ChoiceFunction.StrategyProofVariants
public import Econlib.SocialChoice.GibbardSatterthwaite
public import Econlib.SocialChoice.May
public import Econlib.SocialChoice.MedianVoter
public import Econlib.SocialChoice.Profile.Basic
public import Econlib.SocialChoice.Profile.Domain
public import Econlib.SocialChoice.Profile.Transform
public import Econlib.SocialChoice.Rule.Borda
public import Econlib.SocialChoice.Rule.BordaProperties
public import Econlib.SocialChoice.Rule.Majority
public import Econlib.SocialChoice.Rule.Plurality
public import Econlib.SocialChoice.Rule.Resolute
public import Econlib.SocialChoice.Rule.Scoring
public import Econlib.SocialChoice.WelfareFunction.Basic
public import Econlib.SocialChoice.WelfareFunction.Properties

/-!
# Social choice library

This module collects Econlib's social-choice API. It exposes preference profiles and domains,
social welfare and social choice functions, voting rules, and the main impossibility and
characterization theorems for collective choice.

## Main topics

* Profiles and domains: Preference profiles, strict domains, and profile transformations used to
  build rankings with controlled top, bottom, and swapped alternatives.
* Choice and welfare functions: Set-valued choice rules, social welfare functions, strategy-proof
  variants, anonymity, neutrality, Pareto properties, IIA, and dictatoriality.
* Voting rules: Resolute scoring rules, Borda, plurality, pairwise majority, and Condorcet winners.
* Theorems: Arrow's impossibility theorem, Gibbard-Satterthwaite, May's theorem, and Black's median
  voter theorem.

## Tags

social choice, voting, arrow theorem, gibbard-satterthwaite, majority rule
-/
