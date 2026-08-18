import EconlibExamples.Preferences.CertaintyEquivalent
import EconlibExamples.Preferences.CobbDouglas
import EconlibExamples.Preferences.ComparativeRiskAversion
import EconlibExamples.Preferences.DebreuRepresentation
import EconlibExamples.Preferences.FiniteRepresentation
import EconlibExamples.Preferences.MedianVoter
import EconlibExamples.Preferences.MonotoneComparativeStatics
import EconlibExamples.Preferences.PrecautionarySaving
import EconlibExamples.Preferences.SeparableOptimum

/-!
# EconlibExamples.Preferences

Worked examples of canonical preference-theory results, formalized against the
`Econlib.Preferences` API. Each example file is a self-contained tutorial: it
constructs a textbook object, names the claim, and proves it using theorems that
already exist in the library.

Per-file index:
- `CertaintyEquivalent` — CARA utility: a certainty equivalent exists, lies below
  the expected value (Jensen gap), the risk premium is nonnegative, and the
  Arrow–Pratt coefficient equals the constant `α`
- `ComparativeRiskAversion` — two CARA agents: higher `α` ⇒ more risk averse ⇒
  lower certainty equivalent for the same gamble
- `CobbDouglas` — Cobb–Douglas preferences: log-linear form, degree-one
  homogeneity, quasiconcavity, strict monotonicity to the interior,
  boundary-avoidance, convex strict upper-contour sets
- `FiniteRepresentation` — a concrete 3-alternative preference admits both an
  ℕ-valued and an ℝ-valued utility representation
- `DebreuRepresentation` — a continuous preference on `ℝ` admits a continuous
  utility representation (Debreu), with open strict contour sets
- `MedianVoter` — Black's theorem on a concrete 3-voter electorate: the median
  ideal point is a Condorcet winner (general theorem lives in `Econlib.SocialChoice`)
- `SeparableOptimum` — additively separable utility with log felicities: strict
  concavity on the positive orthant and a unique interior first-order condition
- `MonotoneComparativeStatics` — Milgrom–Shannon / Topkis: a complementarity payoff
  with positive cross-partial ⇒ the optimal action is nondecreasing in the type
- `PrecautionarySaving` — two-period saving under prudence (`Econlib.Preferences.Prudent`):
  convex marginal utility ⇒ income risk raises expected marginal utility of saving (Jensen) ⇒
  a prudent consumer saves more under risk; made concrete for log utility
-/
