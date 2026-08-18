import EconlibExamples.Probability.EmploymentChain
import EconlibExamples.Probability.FirstOrderDominance
import EconlibExamples.Probability.GaussianSignal
import EconlibExamples.Probability.MontyHall
import EconlibExamples.Probability.RothschildStiglitz

/-!
# EconlibExamples.Probability

Worked examples of canonical probability and information-economics results, formalized
against the `Econlib.Probability` API. Each example file is a self-contained tutorial: it
constructs a textbook model, names the claim, and proves it.

Per-file index:
- `MontyHall` — finite Bayesian updating: switching wins with probability `2/3`
- `FirstOrderDominance` — FOSD ⇒ every monotone agent prefers the dominant lottery
- `RothschildStiglitz` — mean-preserving spread: every risk averter prefers the sure thing
- `EmploymentChain` — two-state Markov chain: unique stationary law, geometric ergodicity
- `GaussianSignal` — MLRP ⇒ FOSD ⇒ monotone comparative statics (Gaussian location family)
-/
