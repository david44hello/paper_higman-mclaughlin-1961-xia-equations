# Xia's equations for the Higman–McLaughlin (1961) conjecture: exact counts and the two norm conditions — Lean 4 proof

The paper: https://doi.org/10.5281/zenodo.23874482

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone --branch v3.71 --single-branch https://github.com/david44hello/paper_higman-mclaughlin-1961-xia-equations.git
cd paper_higman-mclaughlin-1961-xia-equations/lean
./check.sh
```

Its last lines look like:

```
FINAL GATE PASS: placeholders only as whole bodies of the 0 listed OPEN rows; every other row PROVED or PROVED GIVEN; per-printed-claim table present.
PASS (final): project builds; source policy passes; the only gaps are the listed OPEN rows.
```

The Lean proof of Proposition 6.1 takes Xia's Proposition 1.2 (projective planes, not in Lean's library) as a stated hypothesis; Theorem 2.1 (Xia) and a bound of Thas and Zagier, which the paper cites, are quoted, not formalized; [AUDIT.md](AUDIT.md) and [AUDIT_NOTES.md](AUDIT_NOTES.md) name them.

Copyright (C) Dave Goel 2026--now. All rights reserved.
