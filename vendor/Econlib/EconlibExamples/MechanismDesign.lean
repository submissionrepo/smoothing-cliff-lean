import EconlibExamples.MechanismDesign.GradeInflation
import EconlibExamples.MechanismDesign.MyersonIroning
import EconlibExamples.MechanismDesign.MyersonReserveUniform
import EconlibExamples.MechanismDesign.MyersonSatterthwaiteUniform
import EconlibExamples.MechanismDesign.ProsecutorJudge
import EconlibExamples.MechanismDesign.PublicGoodProvision
import EconlibExamples.MechanismDesign.SecondPriceAuction
import EconlibExamples.MechanismDesign.UniformRevenueEquivalence

/-!
# EconlibExamples.MechanismDesign

Worked examples of canonical mechanism-design problems, formalized against the
`Econlib.MechanismDesign` API. Each file constructs a textbook environment, names the guarantees,
and proves them — doubling as a regression test of the public entry points.

Per-file index:
- `ProsecutorJudge` — the Kamenica–Gentzkow prosecutor/judge: the optimal
  Bayes-plausible signal secures conviction with probability `3/5`, strictly above the
  no-information payoff, because the step payoff is not concave
- `GradeInflation` — continuous persuasion with a uniform ability prior and a
  threshold employer: the optimal grading policy is pass/fail at `2r − 1`, the pass grade's mean is
  exactly the hiring bar `r`, every experiment hires at most `2(1 − r)` (attained), exactly double
  full disclosure
- `SecondPriceAuction` — the two-bidder Vickrey auction is VCG: efficient, DSIC,
  ex-post IR, no-deficit; the winner pays the rival's (second-highest) bid
- `PublicGoodProvision` — the Clarke pivotal mechanism for a binary public good:
  efficient, DSIC, no-deficit; provision is efficient iff aggregate value covers aggregate cost
- `MyersonReserveUniform` — the uniform-`[0,1]` screening benchmark: virtual value
  `ψ(θ) = 2θ − 1`, regular, optimal reserve `1/2`
- `MyersonIroning` — an *irregular* `[0,3]` environment with density `(1+8θ)^{-1/2}`:
  the virtual value `ψ` is non-monotone, the convex-envelope ironing is active (`ψ̄ = −9/8 ≠ ψ` on
  the bunched region `q ∈ (0,1/4)`), and the cumulative ironing gap is nonzero — the foil to the
  regular uniform benchmark where every ironing identity is vacuous
- `UniformRevenueEquivalence` — symmetric `n`-bidder uniform IPV: the efficient
  auction's interim allocation is the top order statistic `t^(n-1)`, the first-price equilibrium bid
  is `(n−1)/n · θ` with truthful mimicking optimal, and the first- and second-price formats are
  revenue equivalent
- `MyersonSatterthwaiteUniform` — uniform-`[0,1]` buyer and seller: no incentive
  compatible, individually rational, ex-post efficient, weakly budget balanced mechanism exists (the
  Myerson–Satterthwaite impossibility), despite strictly positive expected gains from trade
-/
