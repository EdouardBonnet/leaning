# Experimental exponent-eight route

This directory is intentionally outside the aggregate
`PolynomialGridMinor.lean` import.  It prepares a three-round recursive
version of Chuzhoy--Tan Section 5 without changing the proved degree-ten
endpoint.

The current modules are:

- `PRO56_READ_FIRST.md`: the mandatory status and task handoff for a Pro 5.6
  proof review;
- `PRO56_NEXT_EXPONENT.md`: the exact recurrence audit and seven-round
  exponent-eight-and-a-quarter task for the next Pro 5.6 pass;
- `ROADMAP.md`: completed proof chain and the remaining endpoint-integration
  steps;
- `EXPONENT8_MAP.md`: the exact source-to-Lean declaration and dependency
  map;
- `Lemma48Additive.lean`: the exact additive loss hidden in the existing
  Lemma 4.8 pruning proof;
- `LastHitSelection.lean`: bounded-fiber counting and distinct
  representative selection;
- `LastHitCrossbar.lean`: contracted-slice provenance, uncontracting,
  orientation toward `X`, last-hit truncation, and the crossbar construction;
- `Observation44RootProvenance.lean`: exact row--auxiliary incidence through
  both legal Observation 4.4 contractions, rooted finite descent, and the
  full-source-row producer for `SliceLocalizationInvariant`;
- `RootedSection42.lean`: rooted Observation 4.4 plus Theorem 4.6 and
  additive per-slice cleanup, packaged as the initial
  `RecursiveSliceLayer`, together with the persistent rooted recursion
  context;
- `Claim53Strong.lean`: the strengthened Claim 5.3 loss
  `|Q_bad| < 4 * g^4`;
- `Observation54Support.lean`, `Observation54Unique.lean`,
  `Observation54Cleanup.lean`, `Observation54Type2.lean`, and
  `Observation54Recursive.lean`: the exact-support-subtype proof of
  Observation 5.4, including hereditary perfect unique linkage and removal
  of discarded components;
- `Observation54Composition.lean`: extension over discarded rows,
  nonconsecutive slice composition, and exact-prefix coarsening;
- `Observation54Refinement.lean`: Observation 5.4 followed by Theorem 4.6,
  packaged as an ambient-row refinement;
- `RecursiveSlicing.lean`: the recursive data, arithmetic contracts, and
  persistent source-localization context;
- `ThreeRoundRecursion.lean`: the proved finite majority/small-slice recursion
  through all three rounds;
- `ThreeRoundParameters.lean`: explicit parameters with
  `C = 2^29`, `logExp = 1`, and threshold
  `C * g^8 * sqrt(g) * (log2(g) + 1)`;
- `AllHappyClusters.lean`: Theorem 4.11 applied to every large slice while
  retaining every connected happy cluster and the exact quarter-mass bound;
- `DyadicClusterClass.lean`: corrected division-free geometric grouping,
  with a closed upper endpoint for the final class;
- `ParentedClusterTable.lean`: parent-tagged cluster occurrences, monotone
  enumeration, and the strict-parent consequence of positive overlap;
- `Case1Section45Assembly.lean`: Theorem 4.15 and the existing row-gap
  connector construction for the parented cluster table;
- `Section5Assembly.lean`: all three majority-large exits, the all-small
  terminal exit, and the source-level rooted three-round producer
  `exists_reduced_weakPathOfSetsSystem_threeRound`;
- `LocalDichotomy.lean`: the complementary crossbar branch, exact
  factor-eight budget, reduced-graph minor transport, and the proved local
  `g^8 * sqrt(g) * log(g)` crossbar/strong-minor dichotomy;
- `GlobalDichotomy.lean`: transport through hairy Path-of-Sets Systems,
  cut-matching-game and Chekuri--Chuzhoy grid-minor consumers, and the
  parameterized treewidth theorem;
- `NumericalEndpoint.lean`: explicit target-dependent parameter choices,
  coefficient templates, and the closed
  `target^8 * sqrt(target) * polylog(target)` theorem;
- `AxiomAudit.lean`: the focused trust audit.

The exact source declarations and dependency information are recorded in
`EXPONENT8_MAP.md`.  A new proof-review conversation should begin with
`PRO56_READ_FIRST.md`.

The first exponent-eight-and-a-half milestone is fully formalized.  The exact
local threshold is carried through the hairy-system assembly and both
grid-minor branches, and `NumericalEndpoint.lean` makes explicit choices of
`ell`, `w`, `k`, `g`, and `r`.  Its final declaration is:

```text
polynomial_grid_minor_theorem_exponentEightAndHalf
```

It gives constants `K,b > 0` such that treewidth at least

```text
K * target^8 * sqrt(target) * (log_2 target)^b
```

forces a `target x target` grid minor for every `target >= 2`.

Nothing in this directory is imported by the public endpoint.  The remaining
work is review and an explicit decision to integrate this theorem publicly or
to continue toward exponent eight.  There is no project-specific axiom in the
experimental closure.
