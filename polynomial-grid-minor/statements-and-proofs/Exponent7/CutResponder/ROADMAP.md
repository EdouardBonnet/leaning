# Cut-responder roadmap

## Complete

- [x] Freeze the generic prescribed-matching exponent-seven endpoint.
- [x] Prove that its singleton-row specialization implies arbitrary terminal
      matching routing.
- [x] Route an explicit bisection and retain source labels, target labels, and
      ordered selected-row traces.
- [x] Select consecutive side-changing transitions and prove crossing,
      pairwise node-disjointness, and active-row internal cleanliness.
- [x] Construct the crossing occurrence multigraph.
- [x] Prove the crossing-batch versus labelled-hub-certificate dichotomy.
- [x] Give a concrete star obstruction to resolving the hub from occurrence
      data alone.
- [x] Isolate the exact occurrence-capacity property that resolves the hub.
- [x] Formalize residual constant-fraction matching peeling.
- [x] Prove the logarithmic batch bound.
- [x] Allocate fresh clusters to every batch and every cut-matching round.
- [x] Instantiate the existing adversarial cut-matching strategy.
- [x] Build the auxiliary round family and prove its balanced-separator bound.
- [x] Prove that clean host paths realize the auxiliary graph as a minor.
- [x] Reuse the half-expander-to-grid theorem.
- [x] Preserve the old alternating-matching consumer as an independent
      fallback.
- [x] Propagate the new consumer through recursive Section 5, the pseudo-grid
      dichotomy, the hairy system, and treewidth.
- [x] Compile all scale inequalities and the conditional power-six endpoint.
- [x] Run the transitive axiom audit.
- [x] Correct the responder so its successful routing is existential data,
      rather than the particular witness selected by `Classical.choose`.
- [x] Prove that the old responder implies the corrected V2 responder.
- [x] Thread V2 through peeling, cut matching, the host minor, Section 5,
      every global reduction, and the exact degree-six endpoint.
- [x] Define the selected-row contact count, total routing length, and the
      bounded lexicographic natural-number routing measure.
- [x] Prove by strong induction that a fixed-routing rerouting-or-grid theorem
      implies the V2 responder.

## Sole mathematical frontier

Prove, for explicit positive constants `reserve` and `responseConstant`,

```lean
StrongClusterRoutingImprovementStatement
  reserve responseConstant.
```

For each fixed candidate routing whose clean response fails, this theorem must
return either the target grid or a routing between the same terminal sets with
strictly smaller `routingMeasure`.  The measure minimizes selected-row
incidence first and total edge length second.  Strong induction already turns
this theorem into the corrected existential responder.

Apply the proved crossing-batch/hub dichotomy to the candidate routing.  In
the hub branch, use the strong-cluster geometry to justify one of:

1. eliminate the hub row with a quantified constant-factor loss and recurse;
2. route the affected transitions through unused reserve rows while preserving
   global row cleanliness;
3. extract the target grid from high hub multiplicity; or
4. reroute with fewer selected-row contacts, or with equal contact count and
   smaller total length.

The abstract star obstruction in `HubObstruction.lean` shows that labels,
attachment order, and disjoint route suffixes alone are insufficient.

## Endpoint after the frontier

Once the improvement theorem above is proved, instantiate
`polynomial_grid_minor_theorem_of_routingImprovement` with it.  The resulting
unconditional threshold is

```text
K * g^6 * (log_2 g)^b.
```

This exponent is the output of compiled natural-number inequalities, not an
asymptotic extrapolation.
