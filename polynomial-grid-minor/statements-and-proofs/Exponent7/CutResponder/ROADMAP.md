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

## Sole mathematical frontier

Prove, for explicit positive constants `reserve` and `responseConstant`,

```lean
StrongClusterCleanActiveCutResponderStatement
  reserve responseConstant.
```

This is deliberately narrower than the old generic
`CleanMatchingDichotomyStatement`.  Its inputs are exactly those arising in a
cluster of a `StrongPathOfSetsSystem`: the two node-well-linked nail sides,
their linkage, connectedness, maximum degree four, the selected global rows,
and two equal-size disjoint residual coordinate sets.

Its successful response must contain a constant-fraction crossing batch whose
paths are internally disjoint from **all** selected global row traces.  The
global condition is necessary because batches are peeled sequentially and
then contracted together.

The current proof reaches a labelled hub certificate.  Any completion must
justify one of:

1. eliminate the hub row with a quantified constant-factor loss and recurse;
2. route the affected transitions through unused reserve rows while preserving
   global row cleanliness;
3. extract the target grid from high hub multiplicity; or
4. prove a bounded occurrence-capacity theorem from the strong-cluster and
   bounded-degree hypotheses.

The abstract star obstruction in `HubObstruction.lean` shows that labels,
attachment order, and disjoint route suffixes alone are insufficient.

## Endpoint after the frontier

Once the producer above is proved, instantiate
`polynomial_grid_minor_theorem_cleanResponder` with it.  The resulting
unconditional threshold is

```text
K * g^6 * (log_2 g)^b.
```

This exponent is the output of compiled natural-number inequalities, not an
asymptotic extrapolation.
