# Smoothing the Cliff — Lean 4 formalization

Machine-checked development for the paper *Smoothing the Cliff: Priority
Mechanism Design under Allocation-Sensitivity Constraints* (double-blind
submission; this repository carries no author information).

## State of the development

- Lean 4.30.0, mathlib pinned at `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- 103 Lean source files and 1,397 theorem-or-lemma declarations in
  `SmoothingCliff/`, with no `sorry` anywhere and no custom axiom: every
  declaration rests only on Lean's standard `propext`, `Classical.choice`,
  and `Quot.sound`.
- All five theorems of the paper are certified. Of the 96 non-assumption
  statements tracked in the paper's manifest, 88 carry a machine-checked
  credential. The statement-by-statement manifest and the credential ledger
  ship with the paper's supplementary artifact rather than this repository.

## Build

Install [elan](https://github.com/leanprover/elan); then, from the
repository root:

    lake build

The toolchain is pinned by `lean-toolchain` and all dependencies by
`lake-manifest.json`. The economics library Econlib is vendored under
`vendor/Econlib` (see below), so the build is self-contained.

## What is not certified, and why

Eight tracked statements carry no Lean credential; none is a silent
omission.

- `prop:threebidders` and `lem:gridinterp` rest on a 19×19 rational witness
  checked in exact arithmetic outside Lean; the checker ships with the
  supplementary artifact.
- Clause (v) of `prop:sp_race`, existence of a mixed equilibrium, wants a
  Kakutani–Fan–Glicksberg theorem for locally convex spaces that neither
  Mathlib nor Econlib has.
- `prop:mechanism_runtime` is credentialed at the level of the counted-loop
  cost model, short of formalizing concrete heap and sampler
  implementations.
- `prop:rho3` has its constant bridge and its upper bound certified
  (`SmoothingCliff/Frontier/ConsistencyGap.lean`); its lower bound consumes
  the tradeoff and attainment facts from inside the three-bidder proof, so
  it inherits the witness's standing rather than a Lean credential.
- `cor:luceclass` has its premium half certified as a composition of the
  within-Luce optimality and the matched log-trailer witness
  (`SmoothingCliff/Mechanism/LuceClass.lean`); the equivalence half rests on
  the recorded one-slot derivative computation and is not separately
  composed.
- The clause of `rem:heteroweights` past its first sentence and the
  large-market limit half of `rem:plmeanfield` state problems the paper
  itself leaves open; whichever part of each makes a claim is credentialed.

## Where the formal statements differ from the printed ones

Three differences, each cutting in a definite direction.

1. Membership in the certified class is encoded by the permutohedron
   inequalities together with the total-mass identity, rather than by the
   existence of an inducing lottery. The universal clauses of `prop:squeeze`
   and `thm:impossibility` therefore come out proved for a class at least as
   large as the paper's, which makes them stronger than stated; the two
   attainment clauses point the other way.
2. The sandwich of `thm:meanfield` is certified at every population size;
   its concluding limit needs continuity of the program value in the mass
   cap and is not certified.
3. The displaced-mass bound of the inclusion-case capacity law `prop:flatK`
   (`SmoothingCliff/Frontier/FlatK.lean`) is certified for every K-subset
   benchmark, with no top-K hypothesis, so it is stronger than printed.

## Layout

- `SmoothingCliff/Basic.lean` — the reduced-form vocabulary: eligible
  profiles, interim rules, anonymity, monotonicity, Lipschitz caps,
  feasibility, welfare.
- `SmoothingCliff/Frontier/` — the welfare frontier under the cap: the
  two-bidder envelope, squeeze bounds, the pointwise impossibility, the
  minimax rate and water-filling, the inclusion-case capacity law, the
  consistency gap, and the large-market program.
- `SmoothingCliff/Mechanism/` — the Plackett–Luce rule: axiomatization,
  monotonicity and payments, own- and cross-bid stability certificates,
  within-Luce optimality, revenue and sybil bounds.
- `SmoothingCliff/Racing/` — the latency-investment game: the spread lemma,
  rent dissipation, the strict-priority equilibrium classification, net
  surplus, and the optimal published cap.
- `SmoothingCliff/Wrapper/` — the single-call payment wrapper certificates.

## Vendored dependency

`vendor/Econlib` is a port of
[Econlib](https://github.com/danlyng/Econlib) (Apache License 2.0, upstream
revision `003655c`) to Lean 4.30.0 / mathlib v4.30.0; the upstream
repository does not yet carry this port, so the ported sources are vendored
here with the upstream license preserved in place. The development imports
its single-parameter Myerson machinery
(`Econlib.MechanismDesign.Transfers.SingleParameter.Screening`) and its
equilibrium existence interface (`Econlib.GameTheory.Equilibrium.Existence`).

## License

The `SmoothingCliff/` development is released under this repository's MIT
license. The vendored `vendor/Econlib` retains its own Apache-2.0 license.
