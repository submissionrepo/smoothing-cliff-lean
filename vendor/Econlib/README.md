# Econlib: A Lean 4 Library for Formal Political Economy

Econlib is a [Lean 4](https://leanprover.github.io/) library for formal political economy, built on [Mathlib](https://github.com/leanprover-community/mathlib4). It formalizes the core theory of preferences, probability, optimization, game theory, mechanism design, social choice, and general equilibrium. For more information, see the [paper](https://lean4.party/econlib.pdf).

## Contents

Econlib comprises nine top-level modules. All results are fully proved with no `sorry` or axioms beyond the standard three.

| Module | Anchors |
|--------|---------|
| **Preferences** | `PreferenceRel`, Debreu's continuous utility theorem, Arrow–Pratt risk aversion, CARA/CRRA/Inada/Cobb–Douglas/quasilinear families, single-peaked and single-crossing preferences |
| **Probability** | Unified distribution carriers (`FinDist`/`CountDist`/`ContDist`/`MixedDist`/`ProbDist`) on the `ProbLaw` spine; Markov chains; stochastic orders FOSD/SOSD/MLRP/MPS; Strassen's theorem; Bayesian updating; ~25 named distributions |
| **Optimization** | Berge's maximum theorem, KKT/Slater/strong duality, Topkis & Milgrom–Shannon monotone comparative statics, Bellman/contraction/value iteration, Benveniste–Scheinkman, Hotelling/Shephard/Roy, Kantorovich–Rubinstein duality |
| **GameTheory** | Nash existence (via Kakutani), Kuhn's theorem, perfect Bayesian and sequential equilibrium, the intuitive criterion, correlated/trembling-hand/proper equilibrium, repeated/evolutionary/cooperative games |
| **MechanismDesign** | Bayesian persuasion (Dworczak–Kolotilin): concavification, the Carathéodory bound, Kantorovich–Rubinstein strong duality, prices-for-moments |
| **SocialChoice** | Arrow's impossibility theorem, Gibbard–Satterthwaite, May's theorem, Black's median voter theorem, voting rules (Borda/plurality/scoring) |
| **Equilibrium** | Walrasian existence (Arrow–Debreu via Kakutani), the first and second welfare theorems, the core, Walras' law, and the Arrow–Debreu production layer |
| **Math** | Fixed-point theory (Brouwer/Kakutani/Schauder/Tychonoff), Sperner's lemma, Danskin's theorem, Stieltjes integration by parts, majorization, optimal transport, concavification |

## Installation

To install lean, see the [Lean website](https://lean-lang.org/install/). Once you have set up a project, add Econlib as a dependency in your `lakefile.toml`:

```toml
[[require]]
name = "econlib"
git = "https://github.com/danlyng/Econlib"
rev = "main"
```

Econlib pins Mathlib `v4.29.0` and the matching Lean toolchain; downstream projects should use the same versions.

## Building

```bash
lake exe cache get      # fetch prebuilt Mathlib artifacts (recommended)
lake build              # build the whole library
```

For convenience, a [`Justfile`](Justfile) is provided with recipes for building the library and generating the HTML documentation:

```bash
just build              # build the whole library
just docs               # generate the doc-gen4 HTML docs into ./docs
```

See [`just`](https://github.com/casey/just) for more information.

## Design principles

Econlib applies a small set of conventions across its modules. They are concerned first with guaranteeing correctness and validity — defending against the semantic drift where a result proves something other than, or weaker than, what its name and documentation claim — and only then with elegance and usability. In brief:

- **Every result must be exercised.** Every public result is exercised by a consumer outside the file that proves it — a worked model in `EconlibExamples` or a semantic witness in `EconlibTest` — guarding against theorems that typecheck but are unusable, vacuous, or misoriented.
- **Invalid constructs should be impossible to express.** An object's invariants are enforced by its type, not left as side conditions. A `BehavioralStrategy` indexed by information sets, for instance, cannot represent a strategy that distinguishes histories the player cannot tell apart.
- **Abstractions are built for working theorists.** The public surface exposes the object a theorist ordinarily writes down — preferences, payoffs, budgets, allocations, prices, transfers — not the most general mathematical encoding. More abstract representations remain available beneath the surface when a theorem needs them.
- **Model objects are passed explicitly.** Noncanonical economic and political content (an `Economy`, a `DirectMechanism`, a voter profile) is a named input to the model, not inferred by typeclass. Typeclasses remain in the supporting mathematics, where inference supplies genuinely canonical structure.
- **Results are discoverable.** A concept glossary, Mathlib-style naming, worked examples, and hosted tooling (Loogle, semantic search, and rendered docs at [lean4.party](https://lean4.party)) let a user locate a result, identify its assumptions, and see how to apply it without already knowing its name or location.

## Documentation

- [`GLOSSARY.md`](GLOSSARY.md) — definitions, notation, and which files contain which main results.
- [`EconlibExamples/`](EconlibExamples/) — self-contained examples showing the API in use.
- [`Hosted documentation`](https://lean4.party/docs) — online Mathlib-style documentation.

## License

Copyright 2026 Daniel Lyng

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this library except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
