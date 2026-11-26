# Lean proofs for pigeonhole coefficient mass

This self-contained Lean 4 project checks the principal results of
*How Many Pigeons Make a Refutation Cheap?* by
John Tripodo, LGTM, meng. Laboratories. It formalizes the real-coefficient,
twin-literal Nullstellensatz cost model of
[Potechin and Zhang (ICALP 2024)](https://doi.org/10.4230/LIPIcs.ICALP.2024.117).

The proof works on the full Boolean board. The original algebraic
weakening model and the literal-cube model admit exactly the same mass
budgets; repeated literals can be condensed and conflicting terms
discarded. Free Boolean and twin identities do not contribute mass.

- `PHP.algebraic_diagonal_separation`: at twice as many pigeons as holes,
  plain proofs cost at least `exp(0.149 n − 8)`, whereas the functional
  system has an explicit certificate of mass at most `16 n³`.
- `PHP.bounded_ratio_exponential_real`, `PHP.plain_subexponential_iff`:
  plain exponential order at bounded ratios and the criterion for
  subexponential mass. The more precise all-ratio lower and many-pigeon
  upper bounds are included.
- `PHP.functional_matching_lower`, `PHP.functional_general_upper`,
  `PHP.functional_polynomial_threshold`: integral bounds and the exact
  polynomial window for the functional system. The corresponding
  asymptotics are checked.
- `PHP.plain_sharpened_rate`: a supplemental six-label refinement to
  `exp(0.162 n − 15)`, stronger asymptotically than the paper's rate.

## Reproduce

From this directory, with Lean 4.24.0 (see `lean-toolchain`), the pinned
dependencies in `lake-manifest.json`, and Python 3:

```sh
bash verify_paper.sh
```

The script builds the project and audits the named theorem declarations in
`PaperAudit.lean`. The only allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Neither a Palomar Comparator result
nor an independent human referee report is claimed here.

AI systems assisted development, checks and writing under human direction.
This does not determine the optimal plain mass across all growing ratios,
or whether plain polynomial mass is attainable.
