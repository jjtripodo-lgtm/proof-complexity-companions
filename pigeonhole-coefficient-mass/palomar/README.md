# Palomar proof package: the pigeonhole coefficient-mass separation

This standalone Lean project contains the statement and proof of the
main diagonal separation from *How many pigeons make a refutation cheap?*
by John Tripodo. At m=2n, plain real-coefficient literal-weakening
refutations have mass at least exp(0.149n−8), and functional refutations
have mass at most 16n³. The underlying algebraic cost model is that of
[Potechin and Zhang (ICALP 2024)](https://doi.org/10.4230/LIPIcs.ICALP.2024.117).
Our [full paper companion](https://github.com/jjtripodo-lgtm/proof-complexity-companions/tree/d9142d22608987505ac743992eb9ec3c8de3ac8b/pigeonhole-coefficient-mass/lean)
checks both directions of the budget equivalence to that algebraic system
and the rest of the paper's principal results.

- `Challenge.lean`: self-contained mathematical statement; the deliberate
  theorem hole is required for the Comparator workflow.
- `Solution.lean`: the same statement with its proof, using only the standard axioms.
- `comparator.json`: compares the headline theorem and requests NanoDa replay.
- `formalization.yaml`: authorship, provenance, scope, and verification disclosure.

With the toolchain and dependencies at the pinned revisions:

```sh
lake build Challenge Solution
lake comparator --config comparator.json
```

Palomar's hosted verification, editorial decision, and registry entry are
separate. This package does not claim any of them have occurred.
