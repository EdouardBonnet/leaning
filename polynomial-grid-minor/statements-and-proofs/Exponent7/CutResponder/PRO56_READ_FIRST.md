# Pro 5.6 handoff: clean active cut responder

Read these files in order:

1. `GenericFrontierAudit.lean`
2. `PrescribedBisectionRouting.lean`
3. `CrossingMatchingOrHub.lean`
4. `StrongClusterCutResponder.lean`
5. `HubObstruction.lean`
6. `CleanResidualResponderV2.lean`
7. `RoutingDescentV2.lean`
8. `README.md`

Do not revisit the arithmetic, peeling, cut-matching strategy, minor
construction, or global propagation.  They are proved in Lean.

## Exact unresolved theorem

Supply a Lean-oriented proof, or a graph-level counterexample, for:

```lean
StrongClusterRoutingImprovementStatement
  reserve responseConstant
```

for some explicit positive constants.

The setting is not a generic node-well-linked terminal set.  It is one cluster
of a `StrongPathOfSetsSystem`, with:

- both nail sides node-well-linked;
- the two nail sides linked;
- a perfect internal linkage;
- connectedness;
- maximum degree at most four;
- `g^2` selected global rows;
- two explicit disjoint equal-size residual sides of a cut-matching
  bisection; and
- width at least `reserve * g^2`.

The input includes an arbitrary candidate `PrescribedBisectionRouting`.  If
that routing has no constant-fraction crossing family internally disjoint from
all selected global rows, the output must be a `g` by `g` grid minor or another
routing between the same terminal sets with strictly smaller
`routingMeasure`.

The measure lexicographically minimizes the number of selected row labels met
by all routes and then the total number of route edges.  Its arithmetic and
the strong-induction conversion to
`StrongClusterCleanActiveCutResponderStatementV2` are already proved.

## What is already proved

`strongCluster_crossingResponse_or_hubCertificate` gives either the required
active-row-clean crossing batch or a hub certificate.  The certificate retains:

- original source labels;
- distinct final target labels;
- the owner row of every occurrence;
- ordered attachment ranks on that row; and
- pairwise node-disjoint route suffixes.

`star_has_no_response_fraction` proves that this occurrence data alone cannot
force a constant-fraction endpoint-disjoint response: all occurrences may use
one hub.  Do not use the old `hubPairConnector`; it pairs tails and may create
a same-side edge.

`StrongClusterOccurrenceCapacityStatement reserve d` remains an exact
sufficient property for the old chosen routing, but maximum degree alone does
not imply it and it is no longer the target.

## Requested mathematical deliverable

For a routing minimizing `routingMeasure`, use the additional strong-system
geometry to resolve a high-multiplicity hub by one of:

1. deleting its coordinate from the active universe, with a recurrence proving
   constant-fraction progress;
2. moving the ordered suffixes through unused reserve rows;
3. extracting a grid from the hub and reserve rows; or
4. producing a rerouting with fewer selected-row contacts (or equal contacts
   and fewer edges).

Every claim must track endpoint labels and global-row internal cleanliness.
If the clean-active statement is false, give a concrete bounded-degree strong
path-of-sets cluster counterexample, not merely an abstract occurrence star,
and state the weakest additional source-faithful hypothesis that excludes it.

The downstream reward is already formalized: a proof of this one statement
instantiates `polynomial_grid_minor_theorem_of_routingImprovement` with
threshold `K * g^6 * (log_2 g)^b`.
