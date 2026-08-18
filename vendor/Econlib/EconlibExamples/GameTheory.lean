import EconlibExamples.GameTheory.BeerQuiche
import EconlibExamples.GameTheory.Centipede
import EconlibExamples.GameTheory.CorrelatedCournot
import EconlibExamples.GameTheory.GrimTriggerPD
import EconlibExamples.GameTheory.MajorityGame
import EconlibExamples.GameTheory.MatchingPennies
import EconlibExamples.GameTheory.PrisonersDilemma
import EconlibExamples.GameTheory.EntryDeterrence
import EconlibExamples.GameTheory.Rubinstein
import EconlibExamples.GameTheory.SpenceSignaling
import EconlibExamples.GameTheory.Stackelberg

/-!
# EconlibExamples.GameTheory

Worked examples of canonical games, formalized against the `Econlib.GameTheory`
API. Each example file is a self-contained tutorial: it constructs a textbook
game, names the equilibrium claim, and proves it.

Per-file index:
- `PrisonersDilemma` — strategic form: dominance, unique pure Nash, Pareto loss
- `MatchingPennies` — strategic form: uniform mixed Nash
- `MajorityGame` — cooperative TU: Shapley value, empty core
- `Centipede` — extensive form: backward-induction SPE (Rosenthal paradox)
- `Rubinstein` — alternating-offers bargaining: backward induction
- `Stackelberg` — quantity leadership (ternary nodes): first-mover advantage
- `EntryDeterrence` — Dixit capacity commitment (mixed arity): strategic
  overinvestment deters entry
- `BeerQuiche` — signaling: pooling PBE fails Intuitive Criterion (Cho–Kreps)
- `SpenceSignaling` — signaling: separating PBE existence
- `GrimTriggerPD` — repeated PD: grim trigger is a subgame-perfect equilibrium at the threshold
  discount, instantiating the library `RepeatedGame.grimTriggerStrategy` / one-shot deviation API
- `CorrelatedCournot` — correlated-Gaussian Bayesian Cournot duopoly: linear BNE
  via the measure-theoretic interim characterization (`isBNE_of_ae_interim`) and
  conjugate Gaussian conditional means
-/
