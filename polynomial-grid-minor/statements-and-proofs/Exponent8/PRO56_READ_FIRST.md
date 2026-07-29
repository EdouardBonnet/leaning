# Read this first: exponent-eight-and-a-half handoff

This directory is an experimental, isolated formalization of a three-round
recursive version of Chuzhoy--Tan Section 5.  It targets a local threshold of
the form

```text
C * g^8 * sqrt(g) * (log g)^c.
```

It does not modify the completed degree-ten polynomial-grid-minor endpoint.

## Required reading order

Read these files in order:

1. `PRO56_READ_FIRST.md`;
2. `EXPONENT8_MAP.md`;
3. `RecursiveSlicing.lean`;
4. `Observation44RootProvenance.lean`;
5. `RootedSection42.lean`;
6. `LastHitCrossbar.lean`;
7. the source files specifically named by `EXPONENT8_MAP.md` for the task at
   hand.

For Observation 5.4 and recursive slicing, also read:

```text
../PseudoGridSlicingDefs.lean
../Observation44Reduction.lean
../PseudoGridSlicing.lean
```

and Chuzhoy--Tan Section 5.2, especially pages 255--258 of the local
grid-minor paper PDF.

## What is already proved

Do not reprove or replace the following packages.

### Additive Lemma 4.8

`Lemma48Additive.lean` refactors the existing pruning proof and proves the
division-free additive loss

```text
|Q \ Q'| * Dhat <= |R \ R'| * what.
```

The old half-retention conclusion is derived from this same pruning trace.

### Last-hit crossbar

`LastHitSelection.lean` and `LastHitCrossbar.lean` prove the bounded-fibre
last-hit argument, including:

- orientation toward `X`;
- existence and uniqueness of the last selected-row hit;
- selection of distinct owner rows;
- truncation of the original auxiliary paths;
- node-disjointness of the truncated paths; and
- construction of the crossbar in the original graph.

### Strengthened Claim 5.3

`Claim53Strong.lean` proves the `O(g^4)` loss:

```text
|Q_bad| < 4 * g^4
```

under the absence of a width-`g^2` crossbar.

### Contraction provenance

`Observation44RootProvenance.lean` proves:

```text
RootedObservation44State.contractCommonEdge_hit_iff
RootedObservation44State.contractOffRowEdge_hit_iff
RootedObservation44State.exists_reduced_of_pseudoGrid
RootedObservation44State.reduced_hit_iff_root_hit
RootedObservation44State.toSliceLocalizationInvariant_fullRows
```

The root auxiliary path is the fixed `PseudoGrid.qPath`, not an arbitrary
immediate parent.  The original row object used by the last-hit proof is the
whole fixed source row.  For a localized contracted path, strict-slice
incidence is equivalent to full contracted-row incidence by `PathInSlice`,
and rooted incidence then transfers it to the full source row.

Do not request lifted preimages of slice-boundary vertices.  They are neither
needed nor exported.

### Initial recursive layer

`RootedSection42.lean` proves:

```text
exists_initialRecursiveSliceLayer_of_pseudoGrid
Theorem41Setup.exists_initialRecursiveSliceLayer_of_pseudoGrid
```

These theorems combine rooted Observation 4.4, Theorem 4.6, additive cleanup
in every slice, and source-path localization into an actual initial
`RecursiveSliceLayer`.  The Theorem 4.1 wrapper derives disjointness of `X`
from every main path using the degree-one terminal assumptions.

## Trust status

Run:

```bash
lake build
lake env lean statements-and-proofs/Exponent8/AxiomAudit.lean
```

Every declaration listed above reports only:

```text
propext
Classical.choice
Quot.sound
```

The only project axiom in this directory is:

```text
SimpleGraph.Exponent8.threeRoundRecursiveSlicing
```

Do not introduce another project axiom.

## Immediate task for Pro 5.6: Observation 5.4

Give a source-faithful, Lean-oriented proof of the following proposed helper
lemmas:

```text
sliceSupport_spansVertices
alternate_slice_linkage_extends_to_global
sliceSupport_isUniqueLinkage
uniqueLinkage_preserved_by_auxiliary_deletion
restrict_separated_rows_isUniqueLinkage
observation54_type2_cleaned_slice
```

The proof must explicitly handle:

- the vertex subtype of the exact slice-support graph;
- extension of an arbitrary alternative local boundary linkage to a full
  alternative linkage;
- arbitrary endpoint pairings, not just the original row pairing;
- simplicity and node-disjointness after attaching row prefixes and suffixes;
- why deleting auxiliary paths preserves uniqueness;
- why retained and discarded rows lie in separate components; and
- why deleting discarded components preserves both spanning and uniqueness.

Audit whether the current recursive result can honestly retain the same
ambient `H`, `Rbar`, and `Qbar` at every depth by extending local cuts
trivially across discarded rows.  If it cannot, give the smallest corrected
dependent structure.  Do not conceal this issue behind an `Input`,
`Provider`, or proof-data hypothesis.

## Second task: composition of slicings

State and prove a Lean-oriented theorem named approximately:

```text
composeSelectedSliceRefinements
```

Its input should contain:

- a parent `M`-slicing;
- an ordered set of selected, possibly nonconsecutive parent slices;
- a local refinement of the retained rows in every selected slice;
- trivial local cuts on discarded rows; and
- localized auxiliary families of a common lower-bounded width.

Its output should be a single global slicing.  Explicitly prove:

- treatment of the gap before the first selected slice;
- treatment of every gap between selected slices;
- treatment of the final gap;
- flattening `(parent slice, local slice)` into one linear cut index;
- `cut_zero`, `cut_last`, and global cut monotonicity;
- strict `PathInSlice` localization after flattening;
- selection of exactly the requested number of slices from a lower bound;
  and
- preservation of `rowRoot`, `qParent`, and localized subfamilies.

## Third task: explicit parameters

Do not assume that `ThreeRoundParameters` is inhabited.  Give explicit
natural-number values for every field under:

```text
N <= 64 * g^6
Dhat = 32 * g^4
fanout = floor(sqrt g) + 1
g >= 2.
```

Verify every inequality recorded in `ThreeRoundParameters`, including all
three refinement budgets, the final assembly mass, and:

```text
8 * (m0 * w0 + (m0 + 1) * N)
  <= C * g^8 * sqrt(g) * (log2(g) + 1)^logExp.
```

If these fields are inconsistent, identify the first incompatible
inequality and compute the smallest exponent supported by the exact
three-round recurrence.

## Required form of the response

Do not use “clearly”, “immediate”, or asymptotic notation in place of a
finite inequality.  Supply:

1. exact proposed Lean declarations;
2. a numbered natural-language proof for each declaration;
3. every finite-set identity and endpoint/gluing invariant needed by Lean;
4. the existing declarations each proof consumes; and
5. an explicit statement of any genuine mathematical gap or necessary
   interface correction.
