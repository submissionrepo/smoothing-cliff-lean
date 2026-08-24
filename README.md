# Smoothing the Cliff — machine-checked proofs

Lean 4 development for the paper *Smoothing the Cliff: Welfare and Latency
Incentives in Priority Mechanisms* (double-blind submission;
this repository carries no author information). Shipped here are the Lean
sources, the manifest carrying one node per paper statement
(`factgraph.toml`) with its checker (`factgraph.py`), and the exact-arithmetic
certificate behind the three-bidder proposition (`n3_witness/`).

## What we checked

The development contains 104 Lean source files and 1,531 theorem or lemma
declarations under `SmoothingCliff/`. A clean build completes 3,576 jobs with
no errors. The sources contain no `sorry` and no custom axiom; every
credentialed statement rests only on Lean's standard foundational axioms
`propext`, `Classical.choice`, and `Quot.sound`. The manifest has 142
non-assumption nodes, of which 101 carry a Lean credential. All five theorem
nodes are among them.

The manifest records the remaining 41 nodes statement by statement. The
general-*n* and heterogeneous strict-priority equilibrium arguments remain
analytic, with scalar identities checked separately by SymPy and, where
applicable, Z3 and cvc5. `prop:threebidders` and `lem:gridinterp` use a 19×19
rational witness checked in exact arithmetic outside Lean. The runtime
proposition is certified only at the counted-loop cost-model level. The
utility interpretation of the sharp coefficient, the general-*n* near-tie
consequences, and several composed corollaries are not packaged as single
Lean declarations even when their inputs are credentialed. The two
large-market remarks retain the open parts identified in the paper.
Literature correspondences are source-checked rather than encoded as Lean
theorems.

**What a credential is attached to.** A credential is issued against a pair:
the statement of a node, and the set of premises it stands on. The manifest
stores a fingerprint of that pair and the checker recomputes it, so changing
a statement or rewiring a premise invalidates the credential mechanically,
with nobody having to remember to clear it. A formalization drifts away from
its paper quietly: the same English words come to rest on different
assumptions, and the credential ends up attached to a theorem nobody wrote.
The fingerprint turns that drift into a failed check.

## The manifest as a graph

The manifest is a directed graph. One vertex represents each paper statement,
and an edge from *P* to *Q* records that the paper's proof of *Q* uses *P*. At
this revision it has 156 vertices and 297 edges: 14 assumptions, 90 lemmas,
39 propositions, 5 theorems, and 8 corollaries. Thirty-one vertices are
sources and 33 are sinks. The graph is acyclic, and a manifest containing a
cycle fails to load.

A credential is issued against a vertex together with its in-edges. We
fingerprint the pair consisting of a node's statement and its sorted premise
set, so the record for `prop:squeeze` reads

    sha256:df8635bdb863 = sha256("Every rule in class C obeys the paper's
    rank-wise allocation ceilings and floors." |
    A_frontier_domain,A_frontier_rule,L_ordering)

Editing the statement moves the fingerprint, and so does adding a premise,
dropping one, or rerouting an edge. The next `check` then refuses the
credential. The figure draws the dependency cone of `thm:impossibility` from
the manifest: six vertices and nine edges. Edges run from premise to
conclusion, so reading upward follows the paper's argument. Dashed boxes are
assumptions, which carry no credential by construction. The three bold edges
are the in-neighbourhood `P_squeeze` is fingerprinted against. Cones
elsewhere in the manifest run much wider, with 40 statements downstream of
`A_pl_process`.

```mermaid
graph BT
  dom["A_frontier_domain"]:::assum
  rul["A_frontier_rule"]:::assum
  ord["L_ordering"]:::stmt
  squ["P_squeeze"]:::stmt
  adj["L_adjacent_shortfall"]:::stmt
  imp["T_impossibility"]:::thm
  dom ==> squ
  rul ==> squ
  ord ==> squ
  rul --> ord
  rul --> adj
  squ --> adj
  ord --> imp
  squ --> imp
  adj --> imp
  classDef assum fill:#eee,stroke:#888,stroke-dasharray: 4 3
  classDef stmt fill:#fff,stroke:#333
  classDef thm fill:#fff,stroke:#333,stroke-width:3px
```

**The two reachability queries.** Downstream, `blast <node>` returns the
descendant closure: what else falls if this statement falls. The assumptions
run large here. `A_pl_process`, the exponential-race process itself, reaches
40 of the 156 vertices. Upstream, `audit <node>` returns the ancestor closure
together with the credential state of every vertex in it, so we can see
whether the paper's route to a theorem passes through anything uncertified.
The longest chain in the graph runs 10 edges, from `A_pl_process` through the
tie-nullity, rank-interval and realized-priority bridges to `thm:stability`
and on to `cor:neartie_dominance`. At that length inspection stops being
reliable and the closure does the work.

**The manifest graph and Lean's.** Lean keeps a dependency graph of its own,
whose vertices are declarations, and enforces it directly: a Lean proof
cannot use a lemma that is not there. The verification work happens there,
and the manifest does none of it. What the manifest records is the *paper's*
argument structure. Keeping the two apart lets them disagree, and a
disagreement is informative. A theorem whose Lean proof is self-contained
still has premises in the paper; if those premises drift, the Lean credential
stays green while the manifest fingerprint breaks. Folding the two records
into one would lose that signal.

Degrees carry a different kind of information. The checker's `status` report
flags vertices with no descendants and four or more ancestors as costly but
load-bearing for nothing. Nothing about correctness follows: a corollary that
rests on a deep chain and supports nothing is fine as mathematics and
expensive as effort. We looked at each and kept all of them. The graph is
what raised the question.

## Verification layers

A reader who takes Lean coverage as the only measure of rigour will misread
what is here. The claims come in three kinds, and we pointed a different
instrument at each.

**Deductive claims, which we checked in Lean.** Theorems, propositions,
lemmas and the mathematical content of remarks all assert that something
follows from something else. A proof assistant helps most here, because the
failure it catches, a step that does not follow, is the failure a careful
reader slides past. All five theorems and 101 of the 142 non-assumption
statements tracked in the manifest are certified this way.

**Finite computations, which we checked in exact arithmetic.**
`prop:threebidders` is settled by a rational witness on a 19×19 grid, and
`lem:gridinterp` states the conditions that carry it to a rule in the
certified class. Checking a fixed finite table of rationals is not something
a proof assistant does better than exact rational arithmetic already does;
porting the checker into Lean would transcribe a computation without adding
information, since the arithmetic is exact and the table is fixed. That is
why the paper labels the proposition computer-assisted.

**Claims that are not deductive at all.** Three kinds of statement in the
paper sit outside the reach of any formal system, and their absence from the
manifest is not a hole in our coverage. The calibration to the Ethereum
builder auction reports facts about data, and whether the sampled slots are
representative is a question about the world rather than about a derivation.
The wedge table of `rem:plmeanfield` evaluates two closed forms at chosen
parameters; we can certify the formulas, not the choice of parameters. And
several remarks, on how to read the type, on the scope of the truthfulness
guarantee, and on adoption incentives, make no mathematical claim at all.
What a formalization can do for these is pin down which mathematical object
the discussion is about, and the manifest records that much.

## The exact-arithmetic certificate

`n3_witness/` holds the rational certificate behind `prop:threebidders`. The
file `n3_R2_rational.json` stores the allocation coordinates on the 19×19
sorted-gap grid as exact rationals, and `verify_rational_witness.py` checks
the conditions listed in `lem:gridinterp` using Python's standard-library
`Fraction` arithmetic, with no floating point anywhere: total mass, ordering,
the two tie conditions, directional monotonicity along each of the three
bid-motion directions, the per-step Lipschitz bounds, the outer-band
agreement that makes the clamped extension admissible, and attainment of the
target value. Running it from that directory,

    python verify_rational_witness.py

prints

    PASS: exact 19x19 rational certificate
    target allocation=(Fraction(11, 12), Fraction(1, 12), Fraction(0, 1)), welfare=29/24

which is the value V₂ = 29/24 the proposition needs at (g₁, g₂) = (1/2, 3/4).
The interpolation lemma then carries the finite table to a rule in the
certified class, and that lemma is the piece we would ask a reader to check
by hand, since it is where a finite object becomes a global one.

## How to rerun the checks

The toolchain is pinned: Lean `leanprover/lean4:v4.30.0` and Mathlib at
revision `c5ea00351c28` (tag `v4.30.0`), reached through Econlib, vendored
under `vendor/Econlib` so the build is self-contained (see below). From the
repository root:

    lake build

A clean build reports 3,576 jobs and exits zero. A single file typechecks on
its own with `lake env lean <file>`, in seconds, writing nothing.

A green build establishes neither of the next two properties, so we check
them separately. The first is that nothing was assumed:

    #print axioms SmoothingCliff.Frontier.thm_impossibility

should print exactly `[propext, Classical.choice, Quot.sound]`. If `sorryAx`
shows up in that list, some proof in the dependency closure is incomplete;
any other name means a custom axiom was admitted somewhere. The second is
that the manifest is telling the truth:

    python factgraph.py factgraph.toml check

recomputes every fingerprint, reports any credential whose statement or
premise set has moved since it was issued, and rejects dangling references
and cycles in the dependency graph.

## Paper statements and their Lean counterparts

The table pairs each numbered result with the declaration carrying its
credential. Where a result has several clauses we name the declaration that
assembles them, and the manifest records the per-clause lemmas. The manifest
contains the full statement-by-statement correspondence and premise graph.

| Paper statement | Lean declaration | File |
|---|---|---|
| `thm:pos` | `minimax_welfare_lower_bound_certificate`, `waterFillingRule_welfare_loss_le` | `Frontier/WaterFilling.lean` |
| `thm:stability` | `finiteExponentialRaceTopKStability` | `Mechanism/StabilityBridge.lean` |
| `thm:sybil` | `maximalCoalitionGain_le_integral` | `Mechanism/Sybil.lean` |
| `thm:impossibility` | `thm_impossibility`, `no_pointwise_optimum_in_subclass` | `Frontier/RankRuleB.lean` |
| `thm:meanfield` | `certifiedRule_le_populationValue` (i), `postedRamp_solves_population_program` (ii), `rationedRampMap_frontier_populationValue` (iii) | `Frontier/InterimBridgeMeanField.lean`, `Frontier/PopulationProgram.lean`, `Frontier/GeneralRationingRate.lean` |
| `prop:frontier2` | `twoBidder_frontier` | `Frontier/TwoBidder.lean` |
| `prop:squeeze` | `ranked_squeeze_bounds` | `Frontier/Squeeze.lean` |
| `prop:sharpcertificate` | `uniformCertificateCoefficients_eq` | `Racing/SharpCertificate.lean` |
| `prop:threebidders` | exact-arithmetic checker, outside Lean | `n3_witness/` |
| `prop:payment_identity` | `globalIsBIC_iff_paymentIdentity` | `Mechanism/Payments.lean` |
| `prop:revenue` | `totalPayment_tendsto_reserve_mul_mass` | `Mechanism/Revenue.lean` |
| `prop:extraction` | `extraction_gap_le` | `Frontier/Extraction.lean` |
| `prop:sp_mixed` | `latticeExpectedStrictPriorityPayoff` | `Racing/MixedRace.lean` |
| `prop:sp_allequilibria` | `positive_payoff_classification_unconditional`, `positiveProfile_equilibrium` | `Racing/NextSupport.lean`, `Racing/PositiveProfile.lean` |
| `prop:sp_floor` | `nash_dissipation_ge_prize_net_cost` | `Racing/BoundaryFloor.lean` |
| `prop:sp_floor_n` | scalar algebra checked by SymPy and SMT; equilibrium argument outside Lean | manifest nodes `L_general_n_*` |
| `prop:sp_floor_hetero` | scalar algebra checked by SymPy and SMT; equilibrium argument outside Lean | manifest nodes `L_hetero_*` |
| `prop:sp_mixed_n` | analytic root-cdf construction, outside Lean | manifest nodes `L_general_n_*` |
| `prop:sp_race` | pure clauses only (see above) | `Racing/RaceEquilibrium.lean` |
| `prop:exact_threshold` | `existsUnique_boundaryRunUpAverage_maximizer` | `Racing/RunUpAverage.lean` |
| `prop:netsurplus` | `heterogeneous_pureNash_netSurplus_le` | `Racing/NetSurplus.lean` |
| `prop:netsurplus_n` | `plLaw_netSurplus_dominates_strictPriority` | `Racing/NetSurplusGeneralN.lean` |
| `prop:rentdissipation` | three clauses, see manifest | `Racing/RentDissipation.lean` |
| `prop:optcert` | four clauses, see manifest | `Racing/OptimalCap.lean` |
| `prop:mechanism_runtime` | cost model only | `Mechanism/Runtime.lean` |
| `prop:budgetwf` | `budgetSpent_flatK_own_modulus_exact`, `budgetSpent_flatK_regret_exact`, `flatKWaterFillingSelection_oneSlot_local_regret_le` | `Frontier/FlatKMinimax.lean` |
| `prop:flatK` | `flatKScoreFrontier_sandwich`, `flatKCubeFrontier_lower`, `flatK_frontier_ratio`; original capacity law in `flatK_waterFilling_loss_le` | `Frontier/FlatKMinimax.lean`, `Frontier/FlatK.lean` |
| `prop:rho3` | constant bridge and upper bound: `shortfall_bridge_units`, `rho3_upper_certificate` | `Frontier/ConsistencyGap.lean` |
| `cor:ir` | `globalReservePayment_interimIR` | `Mechanism/Payments.lean` |
| `cor:tight-K1` | `oneSlotLuceAllocation_lipschitz_eligible` | `Mechanism/OneSlotStability.lean` |
| `cor:sharpspeed` | utility identity composed with `uniformCertificateCoefficients_eq`; no single wrapper declaration | `Racing/SharpCertificate.lean`, `Racing/Spread.lean` |
| `cor:neartie_dominance` | `neartie_dominance` | `Racing/NearTieDominance.lean` |
| `cor:neartie_region` | scalar algebra checked by SymPy and SMT; equilibrium inputs outside Lean | manifest nodes `C_neartie_region`, `L_neartie_*` |
| `cor:luceclass` | premium half: `luceClass_matched_log_premium` | `Mechanism/LuceClass.lean` |
| `rem:sybilsign` | `twoIdentityTruthfulGain_strictPriority_dichotomy` | `Mechanism/SybilStrictPriority.lean` |
| `rem:heteroweights` | first clause: `profileCertifiedRule_le_populationValue` | `Frontier/HeterogeneousWeights.lean` |
| `rem:plmeanfield` | feasibility and strictness: `plCurve_welfare_lt_populationValue` | `Frontier/PLMeanFieldCurve.lean` |
| `rem:rentcap` | `positive_payoff_le_cost_band_of_support` | `Racing/SupportBound.lean` |
| `rem:coercivity` | `rentDissipation_finite_supremum_counterexample` | `Racing/RentDissipationCounterexample.lean` |
| `rem:kernel` | `halfL1_scaleDensity_le_cg`, `uniform_not_le_varA_only` | `Wrapper/ScaleKernelTV.lean` |
| `rem:wf_tight` | `waterFill_band_increment`, `hasDerivAt_waterFill_band` | `Frontier/BandDerivative.lean` |
| `rem:constant` | `certificate_independent_of_mass`, `oneSlot_constant_lt_general` | `Mechanism/CertificateStructure.lean` |

## Where the Lean statement and the printed one differ

The following scope differences matter when reading the credentials.

**Feasibility of the certified class.** We encode membership in the certified
class by the permutohedron subset system Σᵢ∈H xᵢ ≤ W₍|H|₎ together with the
total-mass identity. The paper's own definition, existence of a lottery over
assignments inducing x, does not appear in the Lean statement. Every lottery
rule satisfies those inequalities, so the universal clauses of `prop:squeeze`
and `thm:impossibility` come out proved for a class at least as large as the
paper's, which makes them stronger than stated; the displaced-mass bound of
the inclusion-case capacity law `prop:flatK` is likewise certified for every
K-subset benchmark, with no top-K restriction, so it too is stronger than
printed. The two attainment clauses point the other way: exhibiting a rule in
the encoded class is weaker than exhibiting one in the paper's. Closing that
gap takes two steps. The first is Rado's theorem, that the permutohedron is
the convex hull of the permutations of the weight vector; Mathlib has
Birkhoff's theorem but not the majorization step before it, and we prove the
equal-weight case, the one the large-market section uses, by an induction on
fractional coordinates. The second is that a lottery has to be selected
measurably in the bid profile, which the paper does by fixing a lexicographic
basic feasible decomposition. A negative existential is not monotone in the
class, so this reaches the conclusion of `thm:impossibility` and not only its
attainment clauses, and we prove that conclusion for *every* class lying
between the two rules we exhibit and the encoded one. That reduces the whole
residue to a single statement: those two rules are lottery-implementable.

**The sharp incentive coefficient.** `prop:sharpcertificate` is formalized as
equality of the sets of admissible uniform window coefficients and uniform
Lipschitz coefficients for an arbitrary family of monotone allocation slices.
The extended-real supremum and infimum displayed in the paper present the
least common coefficient order-theoretically; they are not separate named
Lean declarations. `cor:sharpspeed` combines this equality with the utility
derivative identity. Its inputs are formalized, but the combined utility
statement is not packaged as one declaration.

**The flat-capacity minimax frontier.** The direct-score lower bounds in
`prop:flatK` are proved for every fixed-mass marginal rule satisfying the
stated full-vector modulus and uniform regret bound. The proof does not need
coordinate bounds. The bounded theorem assumes the rule only on `[0,1]^n`
and does not extend it beyond the cube. `prop:budgetwf` is formalized with its
exact general-*K* modulus, two-block worst case, and one-slot local spread
bound. Its displaced-mass inequality holds for every *K*-subset benchmark,
which is stronger than the printed top-*K* specialization.

**The limit in `thm:meanfield`.** We prove the sandwich
V\*(W̄ₙ) − b̄w₁/(4√n) ≤ Vₙ(xᴿᴿ) ≤ V\*(W̄ₙ) at every n. We do not state the
concluding sentence, that per-capita value converges along a sequence with
W̄ₙ → W̄, as a limit, because getting there needs continuity of the program
value in the mass cap, and we have not proved that.

**The scale-family total-variation bound.** The bound in `rem:kernel` is
certified by integrating its local total-variation rate. A direct comparison
of two scales pays for the moving support with the supremum of the density
near the endpoint, while the printed constant uses the endpoint limit. The
printed local-rate argument instead integrates along a chain of intermediate
scales, using the metric property of total variation. The Lean credential
therefore has the same hypotheses as the printed statement. Dropping the
boundary term remains false, with the uniform kernel as witness.

## Scope outside Lean

The 41 non-assumption nodes without a Lean credential fall into four groups.

**Analytic equilibrium arguments.** The general-*n* and heterogeneous
strict-priority results use compact-support comparisons, zero-payoff
classifications, shifted independent copies, and root-cdf equilibrium
constructions. Their closed-form identities and semialgebraic inequalities
have SymPy and dual-solver checks, while the measure-theoretic equilibrium
arguments remain in the paper proof. This group contains `prop:sp_floor_n`,
`prop:sp_floor_hetero`, and `prop:sp_mixed_n`, together with the general-*n*
near-tie corollaries.

**Finite and external checks.** `prop:threebidders` and `lem:gridinterp` use
the exact rational certificate described above. The mappings to the
Goldberg–Fanti–Shah frontier and to the order-statistic transformation in
Betto–Thomas are checked against the cited sources. These checks have their
own manifest layers and do not receive Lean tags.

**Library and implementation boundaries.** Clause (v) of `prop:sp_race` uses
an infinite-dimensional Kakutani–Fan–Glicksberg theorem not supplied by the
pinned libraries. Lottery implementability for declining slot weights uses
the majorization step in Rado's theorem and a measurable decomposition.
`prop:mechanism_runtime` is formalized through its counted-loop cost model;
concrete heaps, samplers, and random-number generators are outside the
development.

**Compositions and open endpoints.** Several corollaries combine credentialed
inputs without a separate wrapper declaration. The finite-*n* sandwich in
`thm:meanfield` is formalized, while its concluding limit would additionally
require continuity of the population program in its mass cap. The PL
large-market limit and the general declining-weight mean-field program remain
open as stated in the paper. The manifest distinguishes each of these cases
from an unrecorded omission.

## Findings

Formalization identified the following hypothesis, scope, and proof-route
issues. The printed statements and manifest incorporate the corresponding
repairs.

1. `prop:rentdissipation` (i) separates a hypothesis-free pointwise
   best-response bound from a uniform quantitative bound requiring unbounded
   marginal cost. `rem:coercivity` supplies a formal counterexample when that
   growth condition is dropped.
2. The strict-priority limit in `rem:sybilsign` depends on the opponents' top
   order statistic. It is zero when an opponent bids at least the coalition
   value and equals −w₁(v−r) against no eligible opponent. Both branches are
   formalized.
3. A positive-part monotonicity step requires the two ordering hypotheses now
   stated explicitly. The downstream burden result is correspondingly
   monotone on nonnegative caps.
4. The band derivative in `rem:wf_tight` requires the active band to remain
   unchanged; on a stable band the own-bid map is locally affine. The
   mass-independence claims in `rem:constant` are formalized as a comparison
   of two profiles.
5. `rem:kernel` uses the local-rate argument above. A direct two-scale
   argument has a different moving-support boundary term and does not certify
   the printed constant.
6. For K ≥ 2, lowering one of K leaders to the tie level does not produce an
   n-way tie. The two lower bounds in `prop:flatK` instead use
   `prop:squeeze`; the Lean proof follows the same dependency.

## Scope of a machine credential

First, a credential says a Lean statement follows from Mathlib and the
standard axioms. It does not say that the Lean statement is a faithful
rendering of the English one. The manifest makes that translation auditable
by storing the English statement, premise set, credential layer, and
discharging declaration for every node.

Second, none of this speaks to whether the modelling assumptions are the
right ones, and none of it reaches the empirical sections. The calibration to
the Ethereum builder auction, the numerical wedge table of `rem:plmeanfield`
and the complexity claims below the cost model are all outside the formal
development.

Third, the proofs in the artifact are independent reconstructions rather than
transcriptions. Where we prove the same statement by a different route, the
paper's appendix proof is the one to read for intuition and the Lean proof
the one that has been checked. Two of ours are shorter than the paper's, and
one, the level-density representation of the second rank rule in
`thm:impossibility`, replaces a rank-by-rank case analysis with two scalar
monotonicity facts.

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
- `factgraph.toml`, `factgraph.py` — the statement manifest and its checker.
- `n3_witness/` — the exact-arithmetic certificate for `prop:threebidders`.
- `vendor/Econlib` — vendored dependency, see below.

## Vendored dependency

`vendor/Econlib` is a port of
[Econlib](https://github.com/danlyng/Econlib) (Apache License 2.0, upstream
revision `003655c`) to Lean 4.30.0 / mathlib v4.30.0; the upstream repository
does not yet carry this port, so the ported sources are vendored here with
the upstream license preserved in place. The development imports its
single-parameter Myerson machinery
(`Econlib.MechanismDesign.Transfers.SingleParameter.Screening`) and its
equilibrium existence interface (`Econlib.GameTheory.Equilibrium.Existence`).

## License

The `SmoothingCliff/` development, the manifest and the witness checker are
released under this repository's MIT license. The vendored `vendor/Econlib`
retains its own Apache-2.0 license.
