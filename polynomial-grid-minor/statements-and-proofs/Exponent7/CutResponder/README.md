# Application-specific cut-responder route

This directory is a parallel consumer for the exponent-seven experiment.  It
does not replace:

- `../AlternatingMatchingRows.lean`;
- `../AlternatingMatchingGrid.lean`; or
- the frozen conditional endpoint
  `SimpleGraph.Exponent7.polynomial_grid_minor_theorem7`.

Those declarations remain regression-tested fallbacks.  The new route avoids
the generic prescribed-matching frontier and uses fresh strong-system clusters
to answer the bisections chosen by the existing cut-matching strategy.

## Mathematical status

The generic frontier was first audited in `GenericFrontierAudit.lean`.
The theorem

```text
cleanMatchingDichotomy_implies_arbitrary_terminal_matching
```

proves that its singleton-row specialization supplies arbitrary simultaneous
terminal matching routing unless a grid is already present.  This makes its
strength explicit and is why the new route does not try to prove it.

Tasks A and B are formalized in:

- `PrescribedBisectionRouting.lean`;
- `CrossingMatchingOrHub.lean`;
- `StrongClusterCutResponder.lean`; and
- `HubObstruction.lean`.

The routed paths are oriented, retain source and target labels, and have
ordered selected-row traces.  Each route is trimmed at a consecutive
side-changing transition.  A maximum support-disjoint occurrence family then
gives either a clean crossing batch or a labelled hub certificate.  The
transition paths are pairwise node-disjoint and internally avoid every active
selected row.

The abstract occurrence interface alone cannot resolve the hub branch:
`star_has_no_response_fraction` is a concrete star-family obstruction with
distinct source and target labels.  The exact sufficient additional property
used by the current proof is

```text
StrongClusterOccurrenceCapacityStatement reserve d.
```

It bounds the number of side-changing occurrences supported by one active
row and yields response constant `2*d`.  This is an interface obstruction, not
a counterexample to the strong-cluster theorem.

Task D was first completed conditional on the stronger residual proposition

```text
StrongClusterCleanActiveCutResponderStatement reserve responseConstant.
```

This statement answers arbitrary equal-size disjoint residual sides, and every
returned bridge is internally disjoint from the complete set of selected
global row traces.  That global cleanliness is exactly what makes peeling
compatible with contraction.

That interface is retained as a regression test, but it asks for a response
from the particular routing selected by `Classical.choose` inside
`strongClusterExplicitRouting`.  The corrected interface is

```text
StrongClusterCleanActiveCutResponderStatementV2
  reserve responseConstant.
```

Its response stores an existentially chosen `PrescribedBisectionRouting`
together with the clean batch.  The old statement implies V2; no converse is
assumed.  Parallel V2 theorems now cover the entire downstream chain below.

The proved downstream chain:

1. peels a perfect matching in at most
   `responseConstant * (log_2(g^2) + 1)` fresh clusters;
2. instantiates the existing adversarial cut-matching strategy;
3. retains a clean host path for every abstract matching edge;
4. contracts the selected global rows to obtain the abstract round family as
   a minor;
5. applies the existing half-expander-to-grid machinery;
6. feeds the resulting `O(log^2 g)` strong-system length through the
   amortized Section 5 pipeline and the unchanged global reductions.

## Kernel-checked endpoint

The corrected exact conditional endpoint is:

```lean
theorem polynomial_grid_minor_theorem_cleanResponderV2
    {reserve responseConstant : Nat}
    (hclean :
      StrongClusterCleanActiveCutResponderStatementV2
        reserve responseConstant)
    (hc : 0 < responseConstant)
    (hreserve : 0 < reserve) :
    exists K b, 0 < K /\ 0 < b /\
      forall G target,
        2 <= target ->
        K * target^6 * (Nat.log 2 target)^b <= treewidth G ->
        ContainsGridMinor G target
```

Lean therefore verifies polynomial exponent **6**, conditional on the one
ordinary responder proposition above.  This is stronger than the requested
exponent-seven milestone because the fresh-cluster cut-matching consumer needs
only quadratically logarithmic strong-system length.  The theorem is not yet
unconditional: `hclean` is a theorem argument, though it is not an axiom.

`RoutingDescentV2.lean` reduces that argument to one fixed-routing
improvement theorem.  Candidate routings are ordered by

```text
(routes.card * Fintype.card V + 1) * contactCount + totalLength.
```

Lean proves that fewer selected-row contacts strictly decrease this measure,
that equal contact count plus shorter total length also decreases it, and that

```text
StrongClusterRoutingImprovementStatement reserve responseConstant
```

implies the V2 responder by strong induction.  Therefore
`polynomial_grid_minor_theorem_of_routingImprovement` has the same degree-six
threshold.  The improvement statement is the current sole mathematical
frontier.

The compiled finite bounds include:

```text
cutResponderStrongLength cRound responseConstant coordinateOrder
  <= 3 * cRound * responseConstant
       * (log_2 coordinateOrder + 1)^2

cutResponderLocalThreshold pseudoScale cRound responseConstant coordinateOrder
  <= 2^39 * cRound * responseConstant
       * pseudoScale^6
       * (log_2 coordinateOrder + 1)^2
       * (log_2 pseudoScale + 1)^3.
```

## Verification

```bash
lake build \
  '«statements-and-proofs».Exponent7.CutResponder.CutResponderNumericalEndpointV2'

lake env lean \
  statements-and-proofs/Exponent7/CutResponder/AxiomAudit.lean

rg -n '^(axiom|unsafe|partial) |\\b(sorry|admit)\\b' \
  statements-and-proofs/Exponent7/CutResponder -g '*.lean'
```

The axiom audit prints only `propext`, `Classical.choice`, and `Quot.sound`.
