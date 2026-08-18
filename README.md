# Smoothing the Cliff Lean formalization

This is the paper-specific development for
`../Smoothing_the_Cliff_ITCS.tex`.

The project uses Lean 4.30.0 and the pinned local Econlib checkout. The local
EconCSLib checkout remains available through its own Lean-LSP MCP and is added
as a project dependency only when a paper declaration actually imports one of
its interfaces. Keeping unused dependencies out of the manifest prevents an
unrelated library pin from invalidating existing proof credentials.

No theorem counts as verified merely because a statement containing `sorry`
elaborates. A paper node receives a `lean` factgraph credential only after its
full source file has no errors and `lean_verify` reports no `sorryAx` or
unapproved custom axiom.
