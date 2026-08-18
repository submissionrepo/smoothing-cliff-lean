# Econlib — Concept Glossary

**Purpose.** Map economic and mathematical concepts (including common synonyms) to the modules and declarations that formalize them. If you are about to write a definition or theorem, grep this file first — most things you might want are already here.

**How to use.**
- Search by *concept name* (e.g., `MLRP`, `monotone likelihood ratio`, `Bayesian persuasion`).
- An entry lists (1) the canonical module path and (2) one or two anchor declarations.
- For exhaustive signatures within a top-level module, see `EconlibDoc/<TopLevel>.md` (auto-extracted from the build; index at `EconlibDoc/README.md`).

**Conventions.** Module paths are written `Econlib.X.Y.Z` and correspond to files `Econlib/X/Y/Z.lean`. Declaration names are fully qualified.

---

## Preferences and utility

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Preference relation; weak preference `≽`; strict preference `≻`; indifference `~` | `Econlib.Preferences.Basic` | `Econlib.Preferences.PreferenceRel`, `RepresentsRealPreference`, `preferenceOfRealUtility` |
| Monotone / strictly monotone preferences; desirability of goods (no free goods); boundary avoidance | `Econlib.Preferences.Geometry.Basic` | `StrictMonotonePreference`, `StrictMonoToInterior`, `BoundaryAvoiding`, `Desirable`, `StrictMonotonePreference.toDesirable`, `BoundaryAvoiding.toDesirable` |
| Continuous utility; Debreu's representation theorem; continuous preferences (closed contour sets) | `Econlib.Preferences.Representation.Debreu` | `ContinuousPreferenceRel`, `ContinuousPref`, `ContinuousPreferenceRel.ofContinuousPref`, `ContinuousPreferenceRel.ofContinuousUtility`, `ContinuousPreferenceRel.exists_continuous_utility_representation` |
| Single-peaked preferences | `Econlib.Preferences.SinglePeaked`, `Econlib.Preferences.Geometry.SinglePeaked` | — |
| Single-crossing (strict and weak); strict increasing differences; supermodular; Spence–Mirrlees | `Econlib.Preferences.SingleCrossing`, `Econlib.Preferences.Geometry.SingleCrossing` | `StrictIncreasingDifferences`, `CardinalSingleCrossing`, `WeakCardinalSingleCrossing`, `Supermodular.toWeakCardinalSingleCrossing`, `SingleCrossingRel` |
| Risk aversion (concave utility); risk loving / neutral | `Econlib.Preferences.RiskAversion`, `Econlib.Preferences.Risk.Basic` | `RiskAverse`, `StrictlyRiskAverse`, `RiskNeutral`, `RiskLoving`, `RiskAverse.le_map_sum`, `RiskAverse.certainty_equivalent_le_expected_value`, `risk_premium_pos_of_strict_concave` |
| Arrow–Pratt coefficient (absolute / relative risk aversion) | `Econlib.Preferences.Risk.ArrowPratt` | — |
| Certainty equivalent | `Econlib.Preferences.Risk.CertaintyEquivalent` | — |
| Comparative risk aversion | `Econlib.Preferences.Risk.ComparativeRiskAversion` | — |
| Prudence (third-derivative); precautionary saving | `Econlib.Preferences.Utility.Prudence` | `Prudent`, `prudent_iff_iteratedDeriv3_nonneg`, `prudent_of_iteratedDeriv3_nonneg` |
| CARA / CRRA / exponential / log / power utility | `Econlib.Preferences.Utility.RiskFamilies` | — |
| Cobb–Douglas utility | `Econlib.Preferences.Utility.CobbDouglas` | — |
| Inada conditions | `Econlib.Preferences.Utility.Inada`, `Econlib.Preferences.InadaUtility` | — |
| Linear / perfect-substitutes utility | `Econlib.Preferences.Utility.Linear` | `LinearUtility`, `LinearUtility.continuous_u`, `LinearUtility.quasiconcaveOn_u`, `LinearUtility.strictMonotonePreference` |
| Quasilinear utility; transferable utility | `Econlib.Preferences.Utility.Quasilinear` | `QuasilinearUtility`, `QuasilinearUtility.u`, `QuasilinearUtility.transfer_utility_increment` |
| Separable / additively separable utility | `Econlib.Preferences.Utility.Separable`, `Econlib.Preferences.SeparableUtility` | — |
| Differentiable utility (gradient, Hessian) | `Econlib.Preferences.Utility.Differentiable` | — |
| Positive utility families | `Econlib.Preferences.Utility.Positive` | — |
| Utility class registry (concave/monotone/etc.) | `Econlib.Preferences.UtilityClasses` | — |
| Finite preferences | `Econlib.Preferences.Finite`, `Econlib.Preferences.Representation.Finite` | — |

**Worked examples:** [`DebreuRepresentation`](EconlibExamples/Preferences/DebreuRepresentation.lean) (Debreu's theorem on an order-theoretically seeded ideal-point preference, plus the lexicographic non-representability counterexample `lexicographic_not_representable` — lex order on `ℝ × ℝ` is rational but admits no real-valued utility); [`PrecautionarySaving`](EconlibExamples/Preferences/PrecautionarySaving.lean) (two-period model: a prudent consumer saves more under income risk — `precautionary_saving` from `Prudent u`, instantiated for log utility).

## Probability — distributions and operations

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Finite-support distribution; pmf on finite type | `Econlib.Probability.FinDist.Basic`, `.CDF` | `Econlib.Probability.FinDist`, `FinDist.cdf` |
| Countable-support distribution | `Econlib.Probability.CountDist.Basic`, `.CDF` | `Econlib.Probability.CountDist`, `CountDist.cdf` |
| Continuous distribution; density; absolutely continuous | `Econlib.Probability.ContDist.Basic`, `.CDF`, `.OfPDF` | `Econlib.Probability.ContDist`, `ContDist.density`, `ContDist.cdf` |
| Mixed (atomic + continuous) distribution | `Econlib.Probability.MixedDist.Basic`, `.CDF` | `Econlib.Probability.MixedDist` |
| General probability distribution on measurable space | `Econlib.Probability.ProbDist.Basic` | `Econlib.Probability.ProbDist` |
| Probability-law spine (carrier → ProbDist); `toProbDist` | `Econlib.Probability.ProbLaw` | `ProbLaw`, `ProbLaw.toProbDist` |
| Expectation; `expect`; ∫ f dμ | `Econlib.Probability.{FinDist,CountDist,ContDist,MixedDist,ProbDist}.Expect` | `expect` (per carrier) + `*_eq_probDist_expect` coherence |
| Bayesian update; posterior; likelihood reweighting | `Econlib.Probability.Bayes`, `Econlib.Probability.{FinDist,CountDist,ContDist,MixedDist}.Bayes` | `posteriorOfLikelihood` (core), `posterior` (kernel-form wrapper) |
| Normal-normal conjugacy; signal extraction; posterior mean/variance closed form | `Econlib.Probability.Distributions.GaussianConjugate` | `gaussianPosteriorMean`, `gaussianPosteriorVariance`, `gaussianPDFReal_mul_factorization`, `ContDist.gaussian_posterior`, `ContDist.gaussianPosterior` |
| Gaussian noisy-signal joint law; Gaussian conditional law (`condDistrib` of a bivariate Gaussian is Gaussian); conditional means `E[x∣θ]=θ`, `E[θ∣x]=μ⋆(x)` | `Econlib.Probability.Distributions.GaussianConditional` | `gaussianNoisyLaw`, `locationKernel`, `posteriorKernel`, `gaussianNoisyLaw_map_swap`, `condDistrib_snd_fst_gaussianNoisyLaw`, `condDistrib_fst_snd_gaussianNoisyLaw`, `gaussianNoisy_integral_id_condDistrib_{snd_fst,fst_snd}` |
| Affine-coefficient identifiability under a nondegenerate Gaussian (a.e.-equal affine functions ⇒ equal intercept/slope; linear-regression coefficient identification) | `Econlib.Probability.Distributions.Gaussian` | `affine_eq_of_ae_eq_gaussianReal`, `gaussianVarianceNNReal`, `gaussianVarianceNNReal_ne_zero` |
| Pure / Dirac point mass | `Econlib.Probability.FinDist.Basic`, `Econlib.Probability.ProbDist.Dirac` | `FinDist.pure_apply` (simp), `FinDist.pure_pmf`, `FinDist.eq_pure_of_pmf_eq_one`, `FinDist.expect_of_pmf_eq_one`, `FinDist.eq_pure_pair_of_disjoint_fin_two`; mixtures-vs-maximizers: `FinDist.expect_le_expect_of_support_max`; named simp sets `findist_eval`/`signaling_eval` in `Econlib.Attributes` |
| Mixture / convex combination of distributions | `Econlib.Probability.FinDist.Mixture`, `MixedDist.Mixture`, `ProbDist.Mixture` | — |
| Product / independent joint | `Econlib.Probability.FinDist.Product`, `ProbDist.Product` | — |
| Pushforward; `map` / `bind` of distribution (monadic ops) | `Econlib.Probability.FinDist.Map`, `CountDist.Map`, `ProbDist.Map` | `map`, `bind` |
| Support of a distribution; supported on a set | `Econlib.Probability.ContDist.Support`, `ProbDist.Support` | `supportsOn` (generic over the measurable space) |
| Probability law bundled with its support (kills the floating `supportsOn` hypothesis) | `Econlib.Probability.SupportedProbDist` | `SupportedProbDist s`, `.widen` |
| Truncation of continuous distribution | `Econlib.Probability.ContDist.Truncate` | — |
| Coupling | `Econlib.Probability.ProbDist.Coupling`, `Econlib.Optimization.OptimalTransport.Coupling` | — |
| Variance | `Econlib.Probability.FinDist.Variance` | — |
| Uniform distribution (finite) | `Econlib.Probability.FinDist.Uniform`, `Econlib.Probability.Distributions.Continuous.Uniform` | — |
| Compact/half-line support of a named density (was the `Refinements` types) | density-level `ContDist.*_density_zero_outside` / `*_density_zero_of_neg` lemmas; measure-level `SupportedProbDist s` | — |

### Named distributions

Continuous: `Econlib.Probability.Distributions.Continuous.{Beta,Exponential,Gamma,Gaussian,Laplace,Logistic,LogNormal,Triangular,Uniform}` (Gaussian = Normal).

Discrete: `Econlib.Probability.Distributions.Discrete.{Bernoulli,Binomial,Geometric,Multinomial,Poisson,Dirichlet,DirichletMultinomial,BetaBinomial,Pochhammer}`.

Each distribution module typically contains `Basic` (definition + pmf/density) plus optional `CDF`, `Moments`, `ConvexOrder`, `SingleCrossing`, `Integral`, `Tail` submodules.

## Probability — stochastic orders

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| First-order stochastic dominance (FOSD) | `Econlib.Probability.Order.FOSD.{Basic,ExpectMono,FinDist,Stieltjes,ToSOSD}` | `Econlib.Probability.FOSD` (canonical, on `ProbDist`), `FinDist.FOSD` (combinatorial), `fosd_iff_integratedCDFTower_one`, `FinDist.fosd_iff` |
| Second-order stochastic dominance (SOSD); concave order | `Econlib.Probability.Order.SOSD.{Basic,Equivalence,DoubleIBP}` | `Econlib.Probability.SOSD` (canonical, on `ProbDist ℝ`; analytic engine `CDF.SOSD = CDF.NOSD 2` bundles `CDF.IntegrableTails`), `CDF.SOSD.expect_concave_mono`, `CDF.SOSD.iff_expect_concave`, `NOSD` (witness-bundled at every order; `nosd_two_iff`/`nosd_one_iff`) |
| Mollifier bridge for SOSD (smoothing argument) | `Econlib.Probability.Order.SOSD.Mollifier.{Basic,ExpectConcave}` | `sosd_expect_concave_mono_general` |
| Mean-preserving spread (MPS); Rothschild–Stiglitz | `Econlib.Probability.Order.Convex.MPS` | — |
| Convex order / increasing convex order | `Econlib.Probability.Order.Convex.{Basic,Topology,Duality,StopLoss}` | `ConvexOrderOnIcc` |
| Beta convex order under concentration change (SOSD + equal mean ⇒ convex order, full continuous-convex test class) | `Econlib.Probability.Distributions.Beta.ConvexOrder` | `betaWithMean_convexOrder`, `betaWithMean_convexOrderOnIcc`, `expect_le_of_sosd_of_mean_eq_of_convexOn_cont`, `expect_le_of_sosd_of_mean_eq_of_convexOn` |
| MLRP (monotone likelihood ratio property); MLR order; MLR dominance | `Econlib.Probability.Order.MLRP.{Basic,FOSD,Posterior,SingleCrossing}` | `ContDist.MLRPLe`, `HasMLRP`, `HasStrictMLRP`, `HasMonotoneLikelihoodRatio`, `HasStrictMonotoneLikelihoodRatio`, `ContDist.MLRPLe.fosd`, `HasMLRP.expectMonotone` |
| Strassen's theorem; dilation; martingale coupling | `Econlib.Probability.Order.Strassen.{Basic,Dilation,Discrete,DiscreteGeneral,Approximation,WeakLimit,CondMeanAtom}` | `DiscreteLaw.exists_martingaleCoupling` (general finite support), `DiscreteLaw.exists_martingaleCoupling_uniform` (uniform special case) |
| Stochastic dominance order `n`; integrated CDF tower | `Econlib.Probability.Order.Core.{Basic,IntegratedCDF,NegPut}` | `IntegratedCDFTower` (bare engine), `CDF.IntegrableTailsUpTo` (order-`n` tail witnesses), `CDF.NOSD`/`NOSD` (witness-bundled general relation) |
| Conditional-mean partition (Strassen-style discretization) | `Econlib.Probability.Order.Convex.ConditionalMeanPartition`, `.Topology` | — |
| Ordered cutoff partition | `Econlib.Probability.Partitions.OrderedCutoff` | — |

## Probability — dynamics

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Finite Markov chain (any finite state space); transition kernel; step operator | `Econlib.Probability.Markov.Basic` | `FiniteMarkovChain`, `FiniteMarkovChain.step` |
| Finite-support / endogenous-shock kernel | `Econlib.Probability.Markov.Endogenous` | `FiniteSupportKernel` |
| Stationary distribution / functional | `Econlib.Probability.ProbDist.Stationary`, `Econlib.Probability.Markov.Basic` | `StationaryFunctional`, `FiniteMarkovChain.IsStationary` |
| Ergodic theorem; existence/uniqueness/geometric convergence of stationary law | `Econlib.Probability.Markov.Ergodic` | `FiniteMarkovChain.exists_stationary`, `FiniteMarkovChain.unique_stationary`, `FiniteMarkovChain.geometric_convergence` |
| History process; sample path | `Econlib.Probability.Markov.History` | — |
| Adapted process | `Econlib.Probability.Markov.AdaptedProcess` | — |
| Supermartingale / submartingale | `Econlib.Probability.Markov.Supermartingale` | — |
| Stochastic monotonicity; monotone coupling of kernels | `Econlib.Probability.Markov.StochasticMonotone` | — |
| FOSD complete lattice on distributions; Knaster–Tarski stationary distribution (least/greatest fixed point) | `Econlib.Probability.Markov.FOSDLattice` | `FinDist.fosdCompleteLattice`, `StochMonotoneFiniteMarkovChain.exists_stationary_lfp` |
| Recover a distribution from its CDF; CDF injectivity | `Econlib.Probability.Order.FOSD.FinDistLattice` | `FinDist.ofCdf`, `FinDist.cdf_injective` |
| Endogenous shock structure | `Econlib.Probability.Markov.Endogenous` | — |
| Arrow decomposition of shocks | `Econlib.Probability.Markov.ArrowDecomposition` | — |
| Present-value functional | `Econlib.Probability.Markov.PresentValue` | — |
| Aggregation functional (consumer / market aggregator) | `Econlib.Probability.Aggregation.Functional` | `AggregateFunctional` |
| Weak convergence; portmanteau theorem | `Econlib.Probability.WeakConvergence.PortmanteauIntegral` | — |

## Optimization

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| argmax; value function `sup f`; argmax convexity (quasiconcave); argmax subtype transport | `Econlib.Optimization.Basic` | `Econlib.Optimization.argmax`, `valueFunction`, `argmax_convex`, `image_val_argmax_univ` |
| Maximum theorem (Berge); upper hemicontinuity | `Econlib.Optimization.MaximumTheorem` | — |
| Continuous selection (single-valued / subsingleton UHC correspondence ⇒ continuous function); continuous argmax under uniqueness | `Econlib.Math.Topology.ContinuousSelection` | `UpperHemicontinuous.exists_continuous_selection` |
| Comparative statics; value monotonicity / supermodularity | `Econlib.Optimization.ComparativeStatics`, `Econlib.Math.Order.Supermodular` | — |
| Topkis's theorem; monotone selection from argmax; Milgrom–Shannon; strong set order | `Econlib.Optimization.ComparativeStatics.MonotoneSelection`, `Econlib.Math.Order.StrongSetOrder` | `argmax_le_of_singleCrossing`, `argmax_strongSetOrder_of_singleCrossing`, `argmax_strongSetOrder_of_weakSingleCrossing`, `sSup_argmax_monotone_of_strictIncreasingDifferences` |
| KKT conditions (Karush–Kuhn–Tucker); KKT sufficiency (inequality-only and full equality-and-inequality) | `Econlib.Optimization.KKT`, `Econlib.Optimization.Constrained` | `ConstrainedProblem.isMaxOn_of_kkt_eq`, `ConstrainedProblem.isMaxOn_of_kkt`, `MaxKKTEq`, `MaxKKT`, `lagrangian` |
| Slater's constraint qualification | `Econlib.Optimization.Slater` | — |
| Strong duality (convex programming) | `Econlib.Optimization.StrongDuality` | — |
| Envelope theorem (smooth, Danskin unique-optimizer case); Hotelling's lemma; Shephard's lemma | `Econlib.Optimization.Envelope`, `Econlib.Math.Analysis.Danskin` | `hasGradientAt_profitFunction`, `hasGradientAt_negExpendFunction`, `gradient_indirectUtility_of_expenditure_chain` |
| Constrained-value envelope / sensitivity theorem (∂value/∂param = ∂Lagrangian/∂param; smooth selection) | `Econlib.Optimization.Constrained.Sensitivity` | `Econlib.Optimization.hasFDerivAt_constrainedValue` |
| Roy's identity (Marshallian demand `x*ₗ = −(∂v/∂pₗ)/(∂v/∂w)`); UMP KKT necessity; indirect utility (value API: attainment, wealth monotonicity) | `Econlib.Equilibrium.{RoyIdentity,IndirectUtility}` | `Econlib.Equilibrium.Roy.roy_identity`, `roy_identity_of_isMaxOn`, `kkt_of_isMaxOn_budget`, `indirectUtility`, `indirectUtility_eq_of_isMaxOn`, `exists_eq_indirectUtility`, `indirectUtility_mono_wealth`, `mem_argmaxRel_preferenceOfUtilityIn_iff` |
| Bellman operator; fixed point of contraction; value function (MDP) | `Econlib.Optimization.DynamicProgramming.Core.{Bellman,BellmanOperator}` | `bellmanOperator`, `DetMDP.valueFunction`, `bellmanOperator_contraction` |
| Deterministic MDP; finite/stochastic MDP | `Econlib.Optimization.DynamicProgramming.Core.MDP`, `.Stochastic` | `DetMDP`, `FiniteMDP`, `StochMDP` |
| Optimal policy / action existence; greedy stationary policy; weak dominance over feasible plans | `Econlib.Optimization.DynamicProgramming.Core.{Bellman,Optimality}` | `DetMDP.exists_optimalAction` (pointwise optimizer), `DetMDP.exists_optimalPolicy` (selected stationary policy function + dominance), `DetMDP.exists_optimalPolicy_valueFunction`, `stationary_policy_optimal` |
| Endogenous Markov chain from an optimal policy (continuous policy from strict concavity + Berge + continuous selection); stationary distribution under the optimal policy | `Econlib.Optimization.DynamicProgramming.Core.EndogenousChain` | `EndogenousPolicyProblem`, `EndogenousPolicyProblem.policyFun`, `EndogenousPolicyProblem.exists_stationary` |
| Benveniste–Scheinkman envelope (DP differentiability) | `Econlib.Optimization.DynamicProgramming.Concavity.BenvenisteScheinkman` | `ConcaveOn.differentiableAt_of_support`, `envelope_condition_dp`, `envelope_deriv_dp` (differentiability derived under frozen-successor transition); `envelope_*_dp_of_diffSucc` (general, successor-diff assumed) |
| Concavity preservation under Bellman | `Econlib.Optimization.DynamicProgramming.Concavity.ConcavityPreservation` | — |
| Value-function regularity (continuity, monotonicity) | `Econlib.Optimization.DynamicProgramming.Core.Regularity` | — |
| Parametric DP; comparative dynamics | `Econlib.Optimization.DynamicProgramming.Core.ParametricDP` | — |
| Weighted-sup DP (unbounded rewards); monotone comparative statics of weighted-bounded fixed points (unbounded-reward analogue of `fixedPoint_le_of_operator_le`); weighted value monotone in budget / collateral cap | `Econlib.Optimization.DynamicProgramming.Core.Weighted`, `Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetWeighted` | `WeightedBlackwell.fixedPoint_le_of_operator_le`, `StochBudgetData.{bellmanOp_le_of_bellmanSet_subset_weighted,weightedValueFunction_mono_of_bellmanOp_le}`, `insuranceBudgetSet_mono_cap`, `InsuranceDP.{toStochBudgetData_bellmanSet_mono_cap,insuranceValue_mono_cap}` | | — |
| Square-root (CRRA `γ=1/2`) Inada utility: closed-ray concave, continuous at `0`, slowly varying | `Econlib.Preferences.Utility.Sqrt` | `InadaUtility.sqrt`, `InadaUtility.sqrt_concaveOn_Ici`, `InadaUtility.sqrt_slowlyVarying` |
| Endogenous-default / option-value DP (foreclosure; `V = max(keep, vOut)` over `StochBudgetData`; piecewise-concave value; kink envelope = convex hull of branch gradients / Clarke generalized gradient); monotone comparative statics of bounded fixed points | `Econlib.Optimization.DynamicProgramming.Budget.OptionValueDP` | `StochBudgetData.{optionBellmanOp,optionValueFunction,optionValueFunction_eq_max,existsUnique_bdd_optionFixedPoint,defaultSet,defaultSet_antitone_keep,optionValueFunction_mono_of_bellmanOp_le,optionValueFunction_concaveOn_of_keep_dominant,optionValueFunction_concaveOn_of_vOut_dominant,hasDerivWithinAt_optionValueFunction_Ici,hasDerivWithinAt_optionValueFunction_Iic}`, `fixedPoint_le_of_operator_le`, `hasDerivWithinAt_max_Ici`, `hasDerivWithinAt_max_Iic`, `hasDerivAt_max_of_lt` |
| Closed invariant set; long-run dynamics | `Econlib.Optimization.DynamicProgramming.Concavity.ClosedInvariantSet` | — |

## Game theory — strategic (normal) form

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Normal-form game; mixed strategy; expected payoff | `Econlib.GameTheory.Nash`, `Econlib.GameTheory.Strategic.Basic` | `NormalFormGame`, `FinNormalFormGame`, `MixedStrategy`, `expectedPayoff` |
| Nash equilibrium (pure / mixed) | `Econlib.GameTheory.Nash` | `IsNashEquilibrium`, `IsMixedNashEquilibrium`, `exists_mixedNashEquilibrium` |
| Nash existence (Kakutani via best-response correspondence) | `Econlib.GameTheory.Existence`, `Econlib.GameTheory.Equilibrium.Existence` | `bestResponseSet`, `bestResponseSet_closedGraph` |
| Best-response correspondence | `Econlib.GameTheory.Nash` (`bestResponseSet`) | — |
| Bayesian game; type space; interim/ex ante | `Econlib.GameTheory.BayesianGame`, `Econlib.GameTheory.Strategic.Bayesian.{Game,TypeDist,PureBNE,MixedBNE}` | — |
| Bayesian Nash equilibrium (BNE) | `Econlib.GameTheory.Strategic.Bayesian.{PureBNE,MixedBNE}` | — |
| Continuous-type / measure-theoretic Bayesian game; ex-ante BNE; interim best response (a.e.); correlated prior; disintegration | `Econlib.GameTheory.Strategic.Bayesian.Measurable.{Game,PureBNE,Interim}` | `MeasBayesianGame`, `MeasBayesianGame.IsBNE`, `exAntePayoff`, `interimPayoff`, `isBNE_of_ae_interim`, `isBNE_of_best_response_on_ae_set`, `ae_interim_of_isBNE`, `isBNE_iff_ae_interim` |
| Distributional strategy (Milgrom–Weber); distributional BNE; outcome law; information density (absolutely continuous information, R2) | `Econlib.GameTheory.Strategic.Bayesian.Measurable.{Distributional,DistributionalRepr}` | `MeasBayesianGame.DistStrategy`, `IsDistBNE`, `outcome`, `distPayoff`, `outcome_eq_compProd`, `informationDensity`, `integral_outcome_eq_density` |
| BNE existence, continuous types (Milgrom–Weber existence theorem; Glicksberg) | `Econlib.GameTheory.Strategic.Bayesian.Measurable.Existence` | `MeasBayesianGame.exists_isDistBNE` |
| Mixed extension; behavioral strategy (kernel) BNE; behavioral existence; purification bridge | `Econlib.GameTheory.Strategic.Bayesian.Measurable.MixedExtension` | `MeasBayesianGame.mixedExtension`, `mixedExtension_isBNE_of_isDistBNE`, `exists_mixedExtension_isBNE`, `isBNE_of_isDistBNE_toDistStrategy` |
| Correlated equilibrium | `Econlib.GameTheory.CorrelatedEquilibrium`, `Econlib.GameTheory.Strategic.CorrelatedEquilibrium` | — |
| Trembling-hand / proper / perfect equilibrium | `Econlib.GameTheory.Strategic.Refinements` | — |
| Coordination game | `Econlib.GameTheory.CoordinationGame`, `Econlib.GameTheory.Strategic.Coordination` | — |
| Symmetric game | `Econlib.GameTheory.Strategic.Symmetric` | — |
| Simplex (mixed-strategy space) | `Econlib.GameTheory.Simplex`, `Econlib.Probability.FinDist.Simplex` | — |
| Equilibrium problem / refinement abstractions | `Econlib.GameTheory.Equilibrium.{Problem,Refinement}` | — |

**Worked examples:** [`PrisonersDilemma`](EconlibExamples/GameTheory/PrisonersDilemma.lean) (dominance, pure-Nash uniqueness, Pareto loss); [`MatchingPennies`](EconlibExamples/GameTheory/MatchingPennies.lean) (uniform mixed Nash via `isMixedNash_iff`).

## Game theory — extensive form

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Game tree; nodes; histories | `Econlib.GameTheory.ExtensiveForm.Core.{Tree,Node,Game}` | `GameTree` |
| Information set; information structure | `Econlib.GameTheory.ExtensiveForm.Core.Tree`, `Econlib.GameTheory.BeliefSystem` | `InfoStructure` |
| Belief system; assessment | `Econlib.GameTheory.{BeliefSystem,ExtensiveForm.Refinements.BeliefSystem}` | — |
| Behavioral strategy; pure strategy | `Econlib.GameTheory.ExtensiveForm.Core.{Strategy,PureStrategy}` | `BehavioralStrategy` |
| Reachable histories; reach probability | `Econlib.GameTheory.ExtensiveForm.Core.Reachable`, `Econlib.GameTheory.PBE` | `reachProbStep`, `reachableHistories` |
| Perfect recall (remembers own past info sets and actions; Kuhn 1953) | `Econlib.GameTheory.ExtensiveForm.Kuhn.PerfectRecall` | `FiniteExtensiveForm.IsPerfectRecall`, `iExperience`, `iRealizedAction`, `PerfectRecallFiniteExtensiveForm`, `IsPerfectRecall.lastStopAlign`, `IsPerfectRecall.reachCoherent` |
| Recall consequences (minimal hypotheses theorems consume; perfect recall implies each) | `Econlib.GameTheory.ExtensiveForm.Kuhn.{Recall,PerfectRecall}` | `ExtensiveForm.NoInfoSetRevisit`, `FiniteExtensiveForm.ActionRecall`, `ExtensiveForm.IsReachCoherent`, `ExtensiveForm.LastStopAlign`, `IsPerfectRecall.noInfoSetRevisit`, `IsPerfectRecall.actionRecall` |
| Kuhn's theorem (behavioral ↔ mixed under perfect recall) | `Econlib.GameTheory.ExtensiveForm.Kuhn.{Forward,Maps,Converse}` | `behavioralToMixed`, `behavioralFromMixed`, `PerfectRecallFiniteExtensiveForm.mixed_realizes_behavioral` (converse: mixed→behavioral realization-equivalent) |
| Per-player path consistency (realization weight of a pure strategy along a history); perfect recall via action recall | `Econlib.GameTheory.ExtensiveForm.Kuhn.PathConsistency` | `FiniteExtensiveForm.iPathConsistent`, `iPathConsistentFrom`, `iPathConsistent_append_singleton`, `IsPerfectRecall.actionRecall` |
| Strategic form of an extensive game | `Econlib.GameTheory.ExtensiveForm.Core.StrategicForm` | — |
| Subgame-perfect equilibrium (SPE) | `Econlib.GameTheory.SubgamePerfect`, `Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.SPE` | — |
| Backward induction (perfect-information) | `Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.{BackwardInduction,OneShot,Tree}` | `backwardInductionValue_decision_eq_of_strictArgmax` (strict-argmax value collapse; `bi_dominates` tactic discharges the dominance side goal at any arity) |
| Unique SPE; generic game (no payoff ties) | `Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.BackwardInduction` (`FinitePerfectInfoTree.IsGeneric`, `IsSubgamePerfectStrategy.eq_backwardInductionStrategy`), flat form in `…PerfectInfoTree.OneShot` | `IsGeneric`, `isGeneric_decision_of_pairwise_lt` (`bi_generic`/`bi_pairwise_ne` tactics discharge it) |
| Perfect Bayesian Equilibrium (PBE) | `Econlib.GameTheory.PBE`, `Econlib.GameTheory.ExtensiveForm.Refinements.PBE` | — |
| Sequential equilibrium | `Econlib.GameTheory.SequentialEquilibrium`, `Econlib.GameTheory.ExtensiveForm.Refinements.SequentialEquilibrium` | — |
| One-shot deviation principle (extensive form) | `Econlib.GameTheory.ExtensiveForm.Refinements.{ReachInvariance,OneShotDeviation}` | `isSequentiallyRational_of_oneShot`, `reachProb_infoSet_invariant_unilateral` |
| Chance / nature node | `Econlib.GameTheory.ExtensiveForm.Core.Node` | `ChanceSpec` |

**Worked examples:** [`Centipede`](EconlibExamples/GameTheory/Centipede.lean) (4-round Rosenthal centipede: backward-induction SPE Pareto-dominated by cooperation, and proven the *unique* SPE via genericity); [`Rubinstein`](EconlibExamples/GameTheory/Rubinstein.lean) (2-round alternating-offers bargaining, proposer advantage); [`Stackelberg`](EconlibExamples/GameTheory/Stackelberg.lean) (quantity leadership on ternary `Fin 3` nodes, first-mover advantage, unique SPE); [`EntryDeterrence`](EconlibExamples/GameTheory/EntryDeterrence.lean) (Dixit capacity commitment, mixed-arity tree with `Fin.castLEEmb` events, strategic overinvestment deters entry).

## Game theory — signaling and refinements

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Signaling game | `Econlib.GameTheory.SignalingGame`, `Econlib.GameTheory.Signaling.Basic` | — |
| Signaling PBE workhorse (pure-deviation sufficiency / one-shot deviation, best response to belief, equilibrium payoff) | `Econlib.GameTheory.Signaling.PBE` | `isSignalingPBE_of_pure`, `senderOptimal_of_pure`, `receiverOptimal_of_pure`, `IsSignalingPBE.sender_bestResponse`, `IsSignalingPBE.receiver_bestResponse`, `equilibriumPayoff` |
| Pooling equilibrium (pooled message, uninformative posterior) | `Econlib.GameTheory.Signaling.Pooling` | `pooling_bayesConsistent`, `pooling_posterior_eq_prior`, `equilibriumPayoff_pure_pure` |
| Separating equilibrium (belief pinned to type, receiver learns the type) | `Econlib.GameTheory.Signaling.Separating` | `IsSeparating.belief_eq_pure`, `posterior_eq_pure_of_unique_sender`; two-type combinatorics: `FinDist.eq_pure_pair_of_disjoint_fin_two` |
| Signaling extensive-form bridge | `Econlib.GameTheory.Signaling.Bridge.{Assessment,Existence,GameTree,Morphism}` | — |
| Signaling strategic-form (agent-normal-form) BNE bridge (every pure PBE is a BNE) | `Econlib.GameTheory.Signaling.Bridge.StrategicBNE` | `purePBEAssessment` (Dirac-strategy assessment), `isBNE_toBayesianPureStrategy_of_isSignalingPBE` (pure signaling PBE ⇒ `toFinBayesianGame.IsBNE` of the embedded `toBayesianPureStrategy`), `isBNE_of_isSignalingPBE_of_pure` (general: any assessment with pure strategies); interim closed forms `interimPayoffAction_{sender,receiver}_eq`, prior marginals `toFinBayesianGame_marginalD_{sender,receiver}`. One-directional (PBE refines BNE); mixed analogue is the Kuhn behavioral↔mixed problem (deferred, aq #305) |
| Signaling sequential equilibrium (Kreps–Wilson; full support sufficient *and* necessary) | `Econlib.GameTheory.Signaling.Bridge.SequentialEquilibrium` | `IsSignalingSequentialEquilibrium`, `isSignalingSequentialEquilibrium_of_isSignalingPBE` (Fudenberg–Tirole coincidence), `exists_signalingSequentialEquilibrium` (sufficiency); necessity of full support: `not_exists_isSignalingSequentialEquilibrium_of_prior_zero`, `not_hasConsistentBeliefs_of_prior_zero` (zero-prior type's own node is structurally reachable yet probabilistically unreachable, forcing belief `1` against posterior `0`) |
| Perturbation (Selten / KM trembles) | `Econlib.GameTheory.Signaling.Perturbation` | — |
| Intuitive criterion (Cho–Kreps) | `Econlib.GameTheory.IntuitiveCriterion`, `Econlib.GameTheory.Signaling.IntuitiveCriterion` | `SurvivesIntuitiveCriterion` (the refinement: PBE + belief restriction), `passesICBeliefRestriction` (part 1 alone), `SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated` (part 2, in-expectation, derived), `SurvivesIntuitiveCriterion.receiver_supportAction_bestResponse_on_nonDominated` (part 2, textbook pure-action best-response form) |

**Worked examples:** [`SpenceSignaling`](EconlibExamples/GameTheory/SpenceSignaling.lean) (separating PBE in a 2-type job-market model); [`BeerQuiche`](EconlibExamples/GameTheory/BeerQuiche.lean) (Cho–Kreps in full: both pooling PBEs proven, all-quiche fails the Intuitive Criterion, all-beer passes it, and no separating PBE exists).

## Game theory — cooperative / coalitional

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Coalitional game (TU game); characteristic function | `Econlib.GameTheory.Cooperative.{Game,Basic}` | — |
| Core of a TU game | `Econlib.GameTheory.Cooperative.Core` | — |
| Shapley value | `Econlib.GameTheory.Cooperative.Shapley` | — |
| Balanced collection; Bondareva–Shapley | `Econlib.GameTheory.Cooperative.Balancedness` | — |
| Strong equilibrium (Aumann) | `Econlib.GameTheory.Cooperative.StrongEquilibrium` | — |
| Operations on coalitional games | `Econlib.GameTheory.Cooperative.Operations` | — |
| Value rule axioms (efficiency, symmetry, additivity) | `Econlib.GameTheory.Cooperative.ValueRule` | — |
| Möbius inversion on coalition lattice | `Econlib.GameTheory.Cooperative.Mobius`, `Econlib.Math.Combinatorics.BooleanMobius` | — |
| Strategic-form ↔ cooperative bridge | `Econlib.GameTheory.Cooperative.{Bridge,StrategicBridge}` | — |

**Worked example:** [`MajorityGame`](EconlibExamples/GameTheory/MajorityGame.lean) (3-player simple-majority TU game: Shapley value `1/3` each by symmetry+efficiency, empty core).

## Game theory — other

| Concept | Module |
|---|---|
| Repeated games; trigger / folk theorems | `Econlib.GameTheory.Repeated.Basic` |
| One-shot deviation principle (OSDP; Blackwell unimprovability; single-period deviation) | `Econlib.GameTheory.Repeated.OneShotDeviation` (`RepeatedGame.IsSubgamePerfectEquilibrium_iff_noProfitableOneShotDeviation`, `RepeatedGame.NoProfitableOneShotDeviation`) |
| Continuation-value locality; continuity at infinity | `Econlib.GameTheory.Repeated.OneShotDeviation` (`RepeatedGame.continuationValue_congr`, `RepeatedGame.abs_continuationValue_sub_le_of_eq_of_lt`) |
| Evolutionary games | `Econlib.GameTheory.Evolutionary.Basic` |

**Worked example:** [`GrimTriggerPD`](EconlibExamples/GameTheory/GrimTriggerPD.lean) (repeated PD at the threshold discount δ=1/2; grim-trigger continuation values computed; `grimTrigger_is_SPE` proved via the one-shot deviation principle).

## Mechanism design — information design (Bayesian persuasion)

All persuasion modules live under the `Econlib.MechanismDesign.InformationDesign.Persuasion.*`
umbrella (sibling of `Econlib.MechanismDesign.Transfers.*`, the transfer-based VCG/Groves layer).

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Signal structure; sender's optimal information design | `…InformationDesign.Persuasion.Finite.Basic` | `SignalStructure`, `signalLaw`, `expectedSenderPayoff` (marginal via `FinDist.signalMarginal`) |
| Bayes-plausible posteriors (martingale condition) | `…InformationDesign.Persuasion.Finite.{Basic,Splitting}` | `BayesPlausible`, `signal_implies_BayesPlausible` |
| Concavification (concave closure of value); 1-D concave envelope | `…InformationDesign.Persuasion.Finite.Basic`, `…InformationDesign.Persuasion.Duality.Basic`, `Econlib.Math.Analysis.Concavification1D.{Defs,Envelope,EnvelopeDuality,OneGapBoundary,OneGapChord}` | `concaveClosure`, `dualValue`, `concaveEnvelope` (1-D) |
| Carathéodory bound (n+1 signal realizations suffice) | `…InformationDesign.Persuasion.Finite.Caratheodory` | `caratheodory_simplex` |
| Step-function / cutoff signal; optimal binary signal (partial pooling); uniqueness of the optimum | `…InformationDesign.Persuasion.Continuous.Threshold.{Basic,Cutoff,ConvexOrder}`, `…InformationDesign.Persuasion.Finite.StepFunction` | `stepPayoff`, `stepConcaveClosure`, `stepOptimalSignal`, `eq_stepOptimalSignal_of_optimal` |
| Sender objective and optimal signal on the line (convex-order feasibility); convex-price (Dworczak–Martini) optimality certificate; threshold cutoff optimal for excess-over-threshold payoff | `…InformationDesign.Persuasion.Continuous.Optimality`, `…InformationDesign.Persuasion.Continuous.Threshold.Optimality` | `IsFeasibleSignal`, `IsOptimalSignal`, `isOptimalSignal_of_convexMajorant`, `thresholdTwoPointLaw_isOptimal_excessOverThreshold` |
| Cutoff / pass-fail disclosure as a kernel experiment; Bayes posterior of a binary signal | `…InformationDesign.Persuasion.Continuous.Threshold.Experiment` | `cutoffExperiment`, `posteriorKernel_cutoffExperiment_ae`, `posteriorMeanLaw_cutoffExperiment` |
| Continuous-state persuasion; equal-mean (first-moment equality) law relation; full disclosure | `…InformationDesign.Persuasion.Continuous.{Basic,ConvexOrder}` | `signalLaw`, `posteriorLaw`, `posteriorMeanLaw`, `posteriorMeanLaw_id`, `HasEqualMean` |
| Convex-order duality (Dworczak–Kolotilin); primal/dual value | `…InformationDesign.Persuasion.Duality.{Basic,WeakDuality,StrongDuality,KRStrongDuality,DualAttainment,PrimalAttainment,Perturbation,ComplementarySlackness,ExtremeStructures,Supergradient}` | `primalValue`, `dualValue`, `dualObjective`, `weakDuality` |
| KR (Kantorovich–Rubinstein) strong duality | `…InformationDesign.Persuasion.Duality.KRStrongDuality`, `Econlib.Optimization.OptimalTransport.{KantorovichRubinstein,KRSignedMeasure}` | — |
| Dual approximation / discretization | `…InformationDesign.Persuasion.Duality.Discretization.{Basic,DualApproximation,NoDualityGap}` | — |
| Prices-for-moments (Kolotilin duality with moment constraints); uniqueness of the optimal joint via a Bayes-plausible selector | `…InformationDesign.Persuasion.Moment.{Basic,PricesForMoments,OptimalDualPrice,CompositionLipschitz,ConvexRoof,Differentiable,JointPosteriorBridge,MartingaleExtension}` | `composedValue`, `ConditionM` (bundles feasibility), `BayesPlausibleSelector`, `unique_optimal_joint_bayesPlausible` |
| No-information benchmark | `…InformationDesign.Persuasion.Finite.NoInformation` | — |

**Worked examples:** [`ProsecutorJudge`](EconlibExamples/MechanismDesign/ProsecutorJudge.lean) (Kamenica–Gentzkow prosecutor/judge: optimal binary signal, conviction probability `3/5`); [`GradeInflation`](EconlibExamples/MechanismDesign/GradeInflation.lean) (continuous persuasion, uniform ability prior, threshold employer: pass/fail at `2r−1` is optimal — universal bound `2(1−r)` over all kernel experiments, attained, double full disclosure).

## Mechanism design — transfers (quasilinear VCG / Groves)

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Quasilinear environment; direct/indirect mechanism | `…Transfers.General.{Environment,DirectMechanism,IndirectMechanism}` | `QuasilinearEnvironment`, `DirectMechanism`, `IndirectMechanism` |
| Incentive compatibility / IR / efficiency / budget balance | `…Transfers.General.SolutionConcepts` | `IsDSIC`, `IsBIC`, `IsExPostIR`, `IsEfficient`, `IsNoDeficit` |
| Revelation principle (Bayesian + dominant-strategy) | `…Transfers.General.RevelationPrinciple` | `directify_isBIC`, `directify_isDSIC` |
| Groves / VCG / Clarke pivot mechanism | `…Transfers.General.Groves.{Payments,DSIC,VCG,VCGProperties}` | `grovesMechanism`, `vcgMechanism`, `clarkePivot` |
| Taxation principle (Holmström) | `…Transfers.General.TaxationPrinciple` | `taxation_principle` |
| Strict separation ⇒ unique menu choice (VCG/Groves) | `…Transfers.General.StrictSeparation` | `strictlySeparatesAlloc_of_unique_efficient`, `efficientAlloc_eq_of_forall_lt` |
| Sign convention (`payment = -transfer`) | `…Transfers.General.Environment` | — |

## Mechanism design — single-parameter screening and auctions

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Screening environment; type interval; allocation rule; direct mechanism | `…Transfers.SingleParameter.Screening.Environment` | `ScreeningEnv`, `AllocationRule`, `DirectMechanism` |
| Incentive compatibility / IR (single-agent, interim) | `…Transfers.SingleParameter.Screening.Incentive` | `IsBIC`, `IsBIR`, `DirectMechanism.reportUtil` |
| Virtual value (`ψ = θ − (1−F)/f`); regularity | `…Transfers.SingleParameter.Screening.VirtualValue` | `ScreeningEnv.virtualValue`, `ScreeningEnv.Regular` |
| Myerson's lemma (monotone ⇒ implementable); Myerson payment | `…Transfers.SingleParameter.Screening.MyersonLemma` | `AllocationRule.myersonPayment`, `monotone_implies_isBIC` |
| Envelope formula; revenue identity (`𝔼[p] = 𝔼[ψ·x]`) | `…Transfers.SingleParameter.Screening.{Envelope,RevenueIdentity}` | `expected_revenue_eq_virtual_surplus` |
| Ironing (ironed virtual value `ψ̄`; convex envelope) | `…Transfers.SingleParameter.Screening.Ironing` | `ironedVirtualValue`, `expected_virtualSurplus_le_ironed` |
| Worked irregular ironing example (active ironing; `ψ̄ ≠ ψ`; bunching; nonzero gap) | `EconlibExamples.MechanismDesign.MyersonIroning` | `irr_vvQuantile`, `irrScreening_not_regular`, `irr_ironedVVQuantile_eq_ironed`, `integral_ironedVVQuantile_sub_vvQuantile_nonzero` |
| Revenue equivalence (screening level) | `…Transfers.SingleParameter.Screening.RevenueEquivalence` | `revenue_equivalence` |
| Symmetric IID auction environment; joint law; ex-post allocation; reduced form (interim allocation) | `…Transfers.SingleParameter.Auction.Environment` | `AuctionEnv`, `ExPostAlloc`, `ExPostAlloc.interimAlloc` |
| Auction mechanism; auction BIC/BIR; interim payment | `…Transfers.SingleParameter.Auction.Mechanism` | `AuctionMechanism`, `AuctionMechanism.IsBIC` |
| Highest-value / highest-score allocation; order statistic `F^{n−1}`; optimal (Myerson) auction; achievability | `…Transfers.SingleParameter.Auction.{Achievable,Optimal}` | `AuctionEnv.highestAlloc`, `highestAlloc_interimAlloc_eq_cdf_pow`, `ExPostAlloc.myersonMechanism`, `exists_optimal_auction_regular` |
| First-price auction: equilibrium bid (bid shading); mimicry best response | `…Transfers.SingleParameter.Auction.FirstPrice` | `ScreeningEnv.firstPriceBid`, `firstPriceBid_isBestResponse` |
| First-price auction, direct (reduced) representation as a mechanism (pay-your-bid; BIC; zero lowest-type rent) | `…Transfers.SingleParameter.Auction.FirstPriceMechanism` | `AuctionEnv.firstPriceMechanism`, `firstPriceMechanism_isBIC` |
| First-price auction as an indirect bid game; Bayes–Nash equilibrium bid against arbitrary deviations; bid win-probability/payoff; direct = game played truthfully | `…Transfers.SingleParameter.Auction.FirstPriceGame` | `AuctionEnv.firstPriceWinProb`, `firstPriceDevPayoff`, `IsBestBid`, `firstPriceBid_isEquilibriumBid`, `firstPriceMechanism_eq_equilibriumPayoff` |
| First-price auction as a `MeasBayesianGame`; symmetric schedule is a canonical `IsBNE` | `…Transfers.SingleParameter.Auction.FirstPriceBNE` | `AuctionEnv.firstPriceMeasGame`, `firstPriceStrategy`, `firstPriceBid_isBNE` |
| Second-price / Vickrey auction as a mechanism (pay the highest rival value; ex-post dominance ⇒ BIC; Vickrey interim payment = Myerson payment) | `…Transfers.SingleParameter.Auction.SecondPriceMechanism` | `AuctionEnv.secondPriceMechanism`, `secondPrice_pointwise_dominance`, `secondPriceMechanism_interimPay_eq_myersonPayment` |
| Revenue equivalence (auction level; equal interim allocations + same bottom rent ⇒ equal interim payments) | `…Transfers.SingleParameter.Auction.RevenueEquivalence` | `AuctionMechanism.revenue_equivalence` |
| Bilateral trade; Myerson–Satterthwaite impossibility | `…Transfers.Bilateral.{Environment,MyersonSatterthwaite}` | `BilateralEnv`, `myerson_satterthwaite` |

## Social choice and voting

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Social welfare function; profile | `Econlib.SocialChoice.{Profile.Basic,Profile.Domain,WelfareFunction.{Basic,Properties}}` | — |
| Arrow's impossibility (IIA, Pareto, non-dictatorship) | `Econlib.SocialChoice.Arrow` | — |
| Gibbard–Satterthwaite (strategy-proofness ⇒ dictatorship) | `Econlib.SocialChoice.GibbardSatterthwaite` | — |
| May's theorem (anonymous/neutral/positive majority) | `Econlib.SocialChoice.May` | `winners_eq_majorityRule`, `may_strict_majority_wins`, `tied_profile_winners_univ` |
| Median voter theorem (Black) | `Econlib.SocialChoice.MedianVoter` | — |
| Profile transformations (permutation, restriction) | `Econlib.SocialChoice.Profile.Transform` | — |
| Choice function; rationality axioms (α, β, WARP) | `Econlib.SocialChoice.ChoiceFunction.{Basic,Properties}` | — |
| Borda rule | `Econlib.SocialChoice.Rule.Borda` | — |
| Plurality rule | `Econlib.SocialChoice.Rule.Plurality` | — |
| Majority rule | `Econlib.SocialChoice.Rule.Majority` | — |
| Scoring rules (general) | `Econlib.SocialChoice.Rule.Scoring` | — |

## General equilibrium

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Preference-carried economy; endowment; nonnegative orthant | `Econlib.Equilibrium.{Economy,Basic}` | `Economy`, `RegularEconomy`, `nonnegOrthant` |
| Budget set; demand correspondence (= `argmaxRel`); demand homogeneity | `Econlib.Equilibrium.Economy` | `budgetSetAt`, `Economy.budgetSet`, `Economy.demand`, `Economy.demand_homogeneous` |
| Excess demand; market clearing; Walras' law | `Econlib.Equilibrium.{Economy,Existence,MarketClearing}` | `Economy.aggregateExcess`, `Economy.MarketClears`, `Economy.excessDemand`, `walras_law`, `ClearsMarket` |
| Walrasian / competitive equilibrium | `Econlib.Equilibrium.Economy` | `Economy.WalrasianEquilibrium` |
| Positive equilibrium prices (no free goods); exact clearing at positive prices | `Econlib.Equilibrium.Economy` | `Economy.WalrasianEquilibrium.price_pos`, `Economy.MarketClears.aggregateExcess_eq_zero` |
| Cobb–Douglas demand (closed form; expenditure shares; unique maximizer) | `Econlib.Equilibrium.CobbDouglasDemand` | `CobbDouglasUtility.argmaxRel_budgetSetAt`, `Economy.demand_eq_singleton_of_cobbDouglas` |
| Walrasian existence (Arrow–Debreu / Kakutani) | `Econlib.Equilibrium.Existence` | `Economy.exists_equilibrium`, `Economy.exists_truncated_fixed_point` |
| Feasible allocation; Pareto dominance / optimality | `Econlib.Equilibrium.Economy` | `Economy.Feasible`, `Economy.ParetoDominates`, `Economy.ParetoOptimal` |
| First / second welfare theorem (support always; budget-maximality only at positive-wealth agents) | `Econlib.Equilibrium.{Welfare,SecondWelfare}` | `Economy.WalrasianEquilibrium.paretoOptimal`, `Economy.ParetoOptimal.exists_supporting_price`, `Economy.ParetoOptimal.exists_quasiEquilibrium_price` |
| Second welfare theorem with lump-sum transfers (decentralize a Pareto optimum — in which every good is consumed and the relabeled economy is McKenzie-irreducible — as a real Walrasian equilibrium with balanced transfers) | `Econlib.Equilibrium.{Economy,SecondWelfare}` | `Economy.WalrasianEquilibriumWithTransfers`, `Economy.WalrasianEquilibriumWithTransfers.Decentralizes`, `Economy.transferEndow`, `Economy.ParetoOptimal.exists_walrasianEquilibriumWithTransfers`, `Economy.ParetoOptimal.aggregateExcess_value_zero` |
| Core (Edgeworth box; coalitional improvements) | `Econlib.Equilibrium.{Economy,Welfare}` | `Economy.Core`, `Economy.WalrasianEquilibrium.mem_core` |
| Production technology; profit / supply (= support function / face) | `Econlib.Equilibrium.Production.Technology` | `Technology`, `RegularTechnology`, `Technology.profit`, `Technology.supply`, `isCompact_attainable` |
| Free input ⇒ empty supply (rules out free-input / labor-economy limit prices) | `Econlib.Equilibrium.Production.Technology` | `Technology.supply_eq_empty_of_free_input` |
| Private-ownership production economy (Arrow–Debreu); ownership shares; augmented wealth | `Econlib.Equilibrium.Production.Economy` | `ProductionEconomy`, `RegularProductionEconomy`, `ProductionEconomy.wealth`, `ProductionEconomy.demand`, `WalrasianEquilibriumProd`, `walras_law_prod` |
| Production irreducibility (McKenzie, firm-connected; credits the coalition its share of the production *increment* `yf - y`, sound at any returns to scale; subsumes exchange `Irreducible`) | `Econlib.Equilibrium.Production.Economy` | `IrreducibleProd`, `Irreducible.toIrreducibleProd` |
| Welfare theorems with production (FWT robust to increasing returns; SWT; SWT with lump-sum transfers) | `Econlib.Equilibrium.Production.{Welfare,SecondWelfare}` | `WalrasianEquilibriumWithProduction.paretoOptimal`, `ProductionEconomy.ParetoOptimal.exists_supporting_price`, `WalrasianEquilibriumWithProductionAndTransfers`, `ProductionEconomy.ParetoOptimal.exists_walrasianEquilibriumWithProductionAndTransfers` |
| Walrasian existence with production (3-factor Kakutani; truncation-not-binding; admits labor economies via free-input seed `hendow_valued`; firm-connected via `IrreducibleProd`) | `Econlib.Equilibrium.Production.Existence` | `ProductionEconomy.exists_equilibrium_prod`, `exists_equilibrium_data_prod`, `quasi_to_walrasian_prod` |
| Robinson Crusoe (one-consumer one-firm labor economy; existence via free input) | `EconlibExamples.Equilibrium.RobinsonCrusoe` | `crusoe`, `crusoe_endow_valued`, `crusoe_equilibrium_exists` |
| Firm-connected two-agent production economy (regression guard: exchange `Irreducible` fails but `IrreducibleProd` holds via a shared labor→output firm) | `EconlibExamples.Equilibrium.FirmConnected` | `firmConnected`, `firmConnected_irreducibleProd`, `firmConnected_not_irreducible`, `firmConnected_equilibrium_exists` |
| Edgeworth box (Cobb–Douglas exchange; welfare theorems; equilibrium uniqueness) | `EconlibExamples.Equilibrium.CobbDouglasEdgeworth` | `edgeworthEquilibrium`, `edgeworth_pareto_optimal`, `edgeworth_unique` |
| Roy's identity worked end-to-end on Cobb–Douglas demand | `EconlibExamples.Equilibrium.CobbDouglasRoy` | `cobbDouglas_roy_identity`, `cdDemand` |
| Locally nonsatiated preferences | `Econlib.Preferences.Geometry.Nonsatiation` | `LocallyNonsatiated` |
| Limited enforcement / participation constraints | `Econlib.Equilibrium.LimitedEnforcement` | — |
| Aggregate accounting (wealth = consumption + capital, market clearing) | `Econlib.Equilibrium.AggregateAccounting` | `aggregate_accounting_of_stationarity_marketClearing` |

## Math — analysis and topology

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Brouwer's fixed-point theorem | `Econlib.Math.Topology.Brouwer` | — |
| Kakutani's fixed-point theorem (correspondences); closed graph (UHC bridge, subtype transfer) | `Econlib.Math.Topology.Kakutani` | `kakutaniFixedPoint`, `UpperHemicontinuous.isClosedGraph`, `IsClosedGraph.image_subtypeVal` |
| Kakutani–Fan–Glicksberg fixed point (set-valued, locally convex TVS; infinite-dimensional Kakutani) | `Econlib.Math.Topology.FanGlicksberg` | `fanGlicksbergFixedPoint`, `kakutaniFixedPoint_convexHull_finite` |
| Schauder's fixed-point theorem | `Econlib.Math.Topology.Schauder` | — |
| Tychonoff's theorem | `Econlib.Math.Topology.Tychonoff` | — |
| Convex set ↔ ball homeomorphism | `Econlib.Math.Topology.ConvexHomeomorph` | — |
| Sperner's lemma (cubical) | `Econlib.Math.Combinatorics.CubicalSperner` | — |
| Freudenthal triangulation | `Econlib.Math.Combinatorics.FreudenthalTriangulation` | — |
| Finite order / lattice combinatorics | `Econlib.Math.Combinatorics.FiniteOrder` | — |
| Boolean Möbius inversion | `Econlib.Math.Combinatorics.BooleanMobius` | — |
| Danskin's theorem (envelope) | `Econlib.Math.Analysis.Danskin` | — |
| Implicit function theorem | `Econlib.Math.Analysis.ImplicitFunction` | — |
| Cauchy mean-value theorem | `Econlib.Math.Analysis.CauchyMVT` | — |
| Subgradient / supergradient (convex analysis) | `Econlib.Math.Analysis.{SubgradientSelection,Supergradient}` | — |
| Fenchel–Moreau (finite-dimensional) | `Econlib.Math.Analysis.FiniteFenchelMoreau` | — |
| Convex reduction / right derivative of convex function; bounded-derivative approximation (affine truncation) | `Econlib.Math.Analysis.{ConvexReduction,ConvexRightDeriv,ConvexBddDerivApprox}` | `ConvexOn.rightDerivExtend`, `ConvexOn.ftc_rightDeriv`, `ConvexOn.exists_seq_bddRightDeriv_tendsto`, `ConvexOn.affineTrunc` |
| Convex integral representation | `Econlib.Math.Analysis.ConvexIntegralRepr` | — |
| Hinge / piecewise-linear convex | `Econlib.Math.Analysis.HingeConvex` | — |
| Concavification on ℝ (one-dimensional concave envelope) | `Econlib.Math.Analysis.Concavification1D.{Defs,Envelope,EnvelopeDuality,OneGapBoundary,OneGapChord}` | — |
| Beta integral identities | `Econlib.Math.Analysis.BetaIntegral` | — |
| Parametric integral; smooth parametric integral | `Econlib.Math.Analysis.{ParametricIntegral,SmoothParametricIntegral}` | — |
| Rademacher / absolute-continuity bridge | `Econlib.Math.Analysis.RademacherACBridge` | — |
| Blackwell sufficiency; bounded fixed-point core; closed invariant set principle | `Econlib.Math.Analysis.Blackwell` | `Blackwell.abs_sub_le_of_monotone_discounting`, `Blackwell.bddFixedPoint`, `ContractingWith.fixedPoint_mem_of_isClosed` |
| Scalar fixed point / IVT zero-finding | use Mathlib: `intermediate_value_Icc'`, `exists_mem_Icc_isFixedPt`, `isClosed_fixedPoints` | — |
| Interval order iso (real intervals) | `Econlib.Math.Analysis.IntervalOrderIso` | — |

## Math — measure theory and integration

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Fundamental theorem of calculus (FTC) | `Econlib.Math.MeasureTheory.FTC` | — |
| Stieltjes integration by parts | `Econlib.Math.MeasureTheory.StieltjesIBP` | — |
| Stieltjes absolute continuity | `Econlib.Math.MeasureTheory.StieltjesAbsCont` | — |
| Integral bridge (Lebesgue ↔ Stieltjes ↔ improper) | `Econlib.Math.MeasureTheory.IntegralBridge` | — |
| Quantile function; integral via quantile | `Econlib.Math.MeasureTheory.{Quantile,QuantileIntegral}` | — |
| Stop-loss transform | `Econlib.Math.MeasureTheory.{StopLoss,QuantileStopLoss}` | — |
| Cauchy–Schwarz (integral form) | `Econlib.Math.MeasureTheory.CauchySchwarz` | — |
| Chebyshev / Markov inequality | `Econlib.Math.MeasureTheory.Chebyshev` | — |
| Disintegration of measures | `Econlib.Math.MeasureTheory.Disintegration` | — |
| Doeblin coupling / minorization | `Econlib.Math.MeasureTheory.Doeblin` | — |
| Measurable selection (closed-graph, a.e.-singleton, ℝⁿ target) | `Econlib.Math.MeasureTheory.MeasurableSelection` | — |
| Measurable selection / von Neumann selection (standard Borel, section-nonempty relation); measurable improving deviation | `Econlib.Math.MeasureTheory.VonNeumannSelection` | `MeasurableSet.exists_measurable_selection_ae`, `exists_measurable_improving_selection` |
| Jankov–von Neumann uniformization; leftmost branch; Baire-space cylinders | `Econlib.Math.MeasureTheory.AnalyticUniformization` | `AnalyticSet.exists_uniformization`, `leftmostBranch_mem` |
| Universally measurable; Luzin's theorem (analytic sets are null-measurable); capacitability | `Econlib.Math.MeasureTheory.AnalyticNullMeasurable` | `AnalyticSet.nullMeasurableSet`, `NullMeasurableSet.of_generateFrom_analyticSet` |
| Lusin's continuity theorem (measurable ⇒ continuous on near-full compact); Carathéodory function packaging; Tietze slab approximation (Milgrom–Weber R1*) | `Econlib.Math.MeasureTheory.LusinContinuity` | `Measurable.exists_isCompact_continuousOn`, `measurable_continuousMapMk`, `exists_boundedContinuous_eqOn_compact_prod` |
| Product of Markov kernels (finite); kernel product | `Econlib.Math.Probability.KernelPi` | `ProbabilityTheory.Kernel.pi` |
| Product/disintegration interchange; product of compProds; density base change; product of Diracs | `Econlib.Math.MeasureTheory.PiCompProd` | `Measure.pi_compProd`, `Measure.withDensity_compProd_fst`, `Measure.pi_dirac` |
| Product-measure multilinearity (coordinate update) | `Econlib.Math.MeasureTheory.PiUpdate` | `Measure.pi_update_add`, `Measure.pi_update_smul` |
| Reindexing products of pairs (dependent) | `Econlib.Math.MeasureTheory.PiProdCongr` | `MeasurableEquiv.piProdEquivProdPi` |
| Distributional-strategy compactness (Prokhorov, fixed marginal, tightness); weak continuity of density-weighted payoffs (Milgrom–Weber continuity lemma) | `Econlib.Math.MeasureTheory.WeakConvergence.{FixedMarginal,FixedMarginalContinuity}` | `fixedFstMarginal`, `isCompact_fixedFstMarginal`, `continuousOn_integral_pi_of_fixedFstMarginal`, `integral_pi_update_convexCombo` |
| Weak-* dual embedding of probability measures (real pairing); locally convex weak dual | `Econlib.Math.MeasureTheory.WeakConvergence.ProbabilityMeasureWeakDual` | `ProbabilityMeasure.toWeakDualBCF`, `WeakDual.instLocallyConvexSpaceReal` |
| Simplex integration | `Econlib.Math.MeasureTheory.SimplexIntegral` | — |
| Optimal transport (general) | `Econlib.Optimization.OptimalTransport.{Coupling,TransportCost,Duality,DualityFinite}` | — |
| Atomic dense / atomization | `Econlib.Optimization.OptimalTransport.{AtomicDense,Atomization}` | — |
| Discretization (atom map, c-transform) | `Econlib.Optimization.OptimalTransport.Discretize.{AtomMap,CTransform}` | — |
| Upper-Lipschitz envelope | `Econlib.Optimization.OptimalTransport.UpperLipschitzEnvelope` | — |
| Hanin representation | `Econlib.Optimization.OptimalTransport.LipschitzDual` (`hanin_representation`) | — |
| Kantorovich–Rubinstein duality (Wasserstein-1) | `Econlib.Optimization.OptimalTransport.{KantorovichRubinstein,KRSignedMeasure}` | — |

## Math — order and linear algebra

| Concept (synonyms) | Module | Anchors |
|---|---|---|
| Supermodular function | `Econlib.Math.Order.Supermodular` | `Supermodular` |
| Strong set order (≤_s) | `Econlib.Math.Order.StrongSetOrder` | — |
| Fixed point of monotone map; Tarski | use Mathlib: `OrderHom.lfp`/`OrderHom.gfp` + `.monotone` (`Mathlib.Order.FixedPoints`) | — |
| Gap-filling for order embeddings | `Econlib.Math.Order.GapFilling` | — |
| Countable linear order embedding into ℝ | `Econlib.Math.Order.CountableLinearOrderEmbedding` | — |
| Majorization | `Econlib.Math.LinearAlgebra.Majorization` | — |
| Balanced core (cooperative games); Bondareva–Shapley | `Econlib.GameTheory.Cooperative.BalancedCore` | `Econlib.GameTheory.Cooperative.Balancedness` |

## Tactics

| Concept | Module |
|---|---|
| `integral_congr` helper | `Econlib.Tactic` |
