# Read this first: exponent-eight-and-a-half handoff

This directory is an isolated formalization of a three-round recursive version
of Chuzhoy--Tan Section 5.  It targets the explicit local threshold

```text
2^29 * g^8 * sqrt(g) * (log2(g) + 1).
```

It does not modify or enter the import closure of the completed degree-ten
polynomial-grid-minor endpoint.

## Required reading order

Read:

1. `PRO56_READ_FIRST.md`;
2. `EXPONENT8_MAP.md`;
3. `RecursiveSlicing.lean`;
4. `ThreeRoundRecursion.lean`;
5. `ThreeRoundParameters.lean`;
6. `LocalDichotomy.lean`;
7. `GlobalDichotomy.lean`;
8. `NumericalEndpoint.lean`.

For work below exponent eight-and-a-half, continue with
`PRO56_NEXT_EXPONENT.md`.

The source is Chuzhoy--Tan, *Towards Tight(er) Bounds for the Excluded Grid
Theorem*, Section 5.2, especially pages 255--258 of the local
`grid-minor-theorem.pdf`.

## Proved packages: do not reprove them

All declarations in this section compile and have no project-specific axiom
in their transitive closure.

### Additive pruning and last-hit crossbar

`Lemma48Additive.lean` proves the division-free loss

```text
|Q \ Q'| * Dhat <= |R \ R'| * what.
```

`LastHitSelection.lean`, `LastHitCrossbar.lean`, and
`Observation44RootProvenance.lean` prove bounded-fibre selection,
orientation toward `X`, last-hit truncation in the original graph, and exact
row--auxiliary incidence through both legal Observation 4.4 contractions.

### Strengthened Claim 5.3

`Claim53Strong.lean` proves

```text
|Q_bad| < 4 * g^4
```

under the absence of a width-`g^2` crossbar.

### Observation 5.4

The exact-support-subtype implementation is in:

```text
Observation54Support.lean
Observation54Unique.lean
Observation54Cleanup.lean
Observation54Type2.lean
Observation54Recursive.lean
```

It proves:

```text
sliceSupport_spansVertices
sliceSupport_isUniqueLinkage
uniqueLinkage_preserved_by_auxiliary_deletion
restrict_separated_rows_isUniqueLinkage
observation54_type2_cleaned_slice
```

The proof handles arbitrary endpoint pairings, exact prefix/local/suffix edge
traces, induced support vertex subtypes, deletion of auxiliary edges, and
removal of discarded row components.

### Refinement composition and all three rounds

`Observation54Refinement.lean` invokes Observation 5.4 and Theorem 4.6 inside
one parent slice and extends the local cuts trivially over discarded rows.

`Observation54Composition.lean` proves:

```text
composeSelectedSliceRefinements
takePrefixCoarsening
```

including nonconsecutive selected parents and all initial, intermediate, and
final gaps.

`RootedSection42.lean` constructs a persistent
`RecursiveSlicingContext` from the rooted Observation 4.4 state.

`ThreeRoundRecursion.lean` proves:

```text
recursiveSlicingRound
threeRoundRecursiveSlicing
```

There is no recursive-slicing placeholder.

### Explicit parameters

`ThreeRoundParameters.lean` proves:

```text
ThreeRoundParameters.explicitExponentEightParameters
```

under

```text
2 <= g
N <= 64 * g^6
Dhat = 32 * g^4.
```

It supplies every finite parameter and verifies the three refinement budgets,
large-slice mass bounds, final pruning inequality, and the displayed
exponent-eight-and-a-half threshold with `C = 2^29` and `logExp = 1`.

## Trust status

Run:

```bash
lake build
lake env lean statements-and-proofs/Exponent8/AxiomAudit.lean
```

The experimental endpoint declarations report only:

```text
propext
Classical.choice
Quot.sound
```

Do not introduce a project axiom, `sorry`, `admit`, an unproved provider, or a
semantic input standing in for a paper theorem.

## Section 5 assembly is now proved

The former Tasks A--C are discharged in:

```text
AllHappyClusters.lean
DyadicClusterClass.lean
ParentedClusterTable.lean
Case1Section45Assembly.lean
Section5Assembly.lean
```

The large branch retains all Theorem 4.11 clusters, proves the corrected
dyadic mass class, orders cluster occurrences by their actual parent slice,
and invokes Theorem 4.15 plus `rowGapPacking`.  The final branch selects one
happy core directly from each already-proved additive cleanup.

The four-way consumer is:

```text
ThreeRoundRecursiveSlicingResult.weakPathOfSetsSystem
```

The actual pseudo-grid producer is:

```text
exists_reduced_weakPathOfSetsSystem_threeRound
```

It combines rooted Observation 4.4, the initial slicing, explicit parameters,
all three recursive rounds, and all four Section 5 exits.  Its output is a
weak path-of-sets system of length and width `g^2` in the constructed reduced
graph.  The endpoint audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## The 8.5 milestone is closed

`LocalDichotomy.lean` and `GlobalDichotomy.lean` now prove:

```text
crossbarDichotomyInput85_proved
gridMinor_or_gridMinor_of_hairy_pathOfSets85
containsGridMinor_of_treewidth_parameters85
```

The first theorem has the exact local threshold

```text
2^29 * g^8 * sqrt(g) * (log2(g)+1).
```

The second theorem discharges both outcomes using the proved cut-matching-game
and Chekuri--Chuzhoy consumers.  The third reaches the parameterized treewidth
stage, whose remaining hypotheses are explicit natural-number inequalities.

`NumericalEndpoint.lean` discharges those inequalities.  It constructs a
target-independent coefficient template, chooses `ell`, `w`, `k`, `g`, and
`r`, and proves the closed theorem

```text
polynomial_grid_minor_theorem_exponentEightAndHalf
```

with the exact displayed threshold

```text
K * target^8 * sqrt(target) * (log_2 target)^b.
```

The intermediate `sqrt(target)+1` estimate is absorbed by doubling `K` for
`target >= 2`.

## Remaining review task

Do not revisit the Section 5 combinatorics or graph-minor transports.  An
external review should now:

1. audit the square-root and logarithmic normalization in
   `NumericalEndpoint.lean`;
2. check that `PolynomialThresholdTemplate85.canonical` satisfies the exact
   constants expected by `containsGridMinor_of_treewidth_parameters85`;
3. rerun `AxiomAudit.lean`; and
4. decide separately whether to expose the isolated theorem through the
   public aggregate or pursue a lower exponent.

## Requested form for external proof review

For any genuinely missing bridge, provide:

1. the exact source statement and page;
2. the exact Lean declaration and existing imports;
3. a numbered natural-language proof with no “clearly” or “immediate”;
4. every finite-set, path-order, and cardinal inequality used;
5. the existing theorem consumed at each step; and
6. either a proof or a concrete counterexample if the proposed interface is
   too strong.
