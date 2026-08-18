import EconlibExamples.SocialChoice.CondorcetParadox
import EconlibExamples.SocialChoice.BordaPathologies
import EconlibExamples.SocialChoice.PluralitySpoiler
import EconlibExamples.SocialChoice.ArrowDictatorship
import EconlibExamples.SocialChoice.MajorityRuleMay
import EconlibExamples.SocialChoice.GibbardSatterthwaiteManipulable

/-!
# EconlibExamples.SocialChoice

Worked examples of canonical social-choice and voting results, formalized against the
`Econlib.SocialChoice` API. Each file is a self-contained tutorial: it constructs a concrete
electorate, names the textbook claim, and proves it using upstream declarations (no new
general-purpose theorems). Together they exercise the breadth of the API — the majority/Condorcet
primitives, the Borda and plurality rules, the welfare-function axioms (Arrow), the choice-function
axioms (May), and strategy-proofness (Gibbard–Satterthwaite).

Per-file index:
- `CondorcetParadox` — three voters in a Latin-square cycle: pairwise majority rule cycles
  (`a ≻ b ≻ c ≻ a`) and admits no Condorcet winner. The pathology single-peakedness rules out.
- `BordaPathologies` — the Borda count violates Arrow's IIA (a two-voter pair where moving an
  irrelevant alternative flips the social `x`-vs-`y` ranking) and the Condorcet criterion (a
  five-voter profile whose Condorcet winner Borda passes over).
- `PluralitySpoiler` — a seven-voter, three-bloc electorate where plurality elects the Condorcet
  *loser* while the Condorcet winner is passed over: the spoiler / vote-splitting effect.
- `ArrowDictatorship` — the projection "society = voter 0" is a dictatorship satisfying Weak Pareto
  and IIA, showing Arrow's axioms are consistent exactly when non-dictatorship is dropped.
- `MajorityRuleMay` — simple majority rule on two alternatives is anonymous, neutral, and positively
  responsive, so May's theorem yields that a strict majority is the unique winner.
- `GibbardSatterthwaiteManipulable` — the Borda count with a lexicographic tie-break is surjective
  and non-dictatorial, and a voter can profitably manipulate it by burying a rival: an explicit
  witness to Gibbard–Satterthwaite.
-/
