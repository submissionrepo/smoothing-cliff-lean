# Three-bidder rational certificate

This directory contains the supplementary certificate used in Proposition
`prop:threebidders` of `Smoothing_the_Cliff_ITCS.tex`.

- `n3_R2_rational.json` stores the three allocation coordinates on the
  19 by 19 sorted-gap grid.
- `verify_rational_witness.py` checks all grid, interpolation-boundary, and
  target-attainment conditions with Python standard-library rational arithmetic.
- `../n3_witness_table.tex` renders the two free coordinates if printed tables
  are required by an archival version.

Run the exact check from this directory with:

```text
python verify_rational_witness.py
```
