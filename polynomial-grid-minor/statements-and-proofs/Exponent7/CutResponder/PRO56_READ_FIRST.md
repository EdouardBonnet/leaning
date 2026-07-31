# Pro 5.6 handoff: clean active cut responder

Read these files in order:

1. `GenericFrontierAudit.lean`
2. `PrescribedBisectionRouting.lean`
3. `CrossingMatchingOrHub.lean`
4. `StrongClusterCutResponder.lean`
5. `HubObstruction.lean`
6. `CleanResidualResponder.lean`
7. `README.md`

Do not revisit the arithmetic, peeling, cut-matching strategy, minor
construction, or global propagation.  They are proved in Lean.

## Exact unresolved theorem

Supply a Lean-oriented proof, or a graph-level counterexample, for:

```lean
StrongClusterCleanActiveCutResponderStatement
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

The output may be a `g` by `g` grid minor.  Otherwise it must return a
constant-fraction crossing family whose paths are pairwise node-disjoint and
internally disjoint from the union of **all** selected global row traces.

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

`StrongClusterOccurrenceCapacityStatement reserve d` is an exact sufficient
extra hypothesis and yields response constant `2*d`.  It is not known to
follow from the current strong-cluster interface.

## Requested mathematical deliverable

Use the additional strong-system geometry to resolve a high-multiplicity hub
by one of:

1. deleting its coordinate from the active universe, with a recurrence proving
   constant-fraction progress;
2. moving the ordered suffixes through unused reserve rows;
3. extracting a grid from the hub and reserve rows; or
4. deriving a uniform occurrence-capacity bound from maximum degree and the
   two linked, node-well-linked nail sides.

Every claim must track endpoint labels and global-row internal cleanliness.
If the clean-active statement is false, give a concrete bounded-degree strong
path-of-sets cluster counterexample, not merely an abstract occurrence star,
and state the weakest additional source-faithful hypothesis that excludes it.

The downstream reward is already formalized: a proof of this one statement
instantiates an axiom-free excluded-grid theorem with threshold
`K * g^6 * (log_2 g)^b`.
