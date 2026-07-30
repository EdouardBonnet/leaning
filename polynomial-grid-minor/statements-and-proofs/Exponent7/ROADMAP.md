# Exponent-seven roadmap

## Completed

1. Rectangularize Theorem 4.15 so chain length and overlap width are distinct.
2. Refactor the large-slice Section 5 output to request a short, wide system.
3. Prove logarithmic-depth amortized recursive slicing with explicit additive
   losses and finite fuel.
4. Prove `cleanBridgeBatch_of_nodeWellLinked`, giving linearly many
   simultaneous clean bridges with a graph-chosen matching.
5. Formalize prescribed odd/even row matchings and prove that clean
   realizations in two clusters per column yield a grid minor.
6. Prove the short-wide Path-of-Sets-to-grid theorem from the exact
   prescribed-matching dichotomy.
7. Run rooted Observation 4.4, Theorem 4.6, recursive Section 5, and minor
   transport in the no-crossbar pseudo-grid branch.
8. Prove the local dichotomy:

   ```text
   q^2-crossbar OR g-grid
   ```

9. Propagate the local result through odd hairy-system clusters and discharge
   the all-crossbar case with the proved cut-matching-game theorem.
10. Choose the rounded power-of-two scale and prove:

    ```text
    exponentSevenLocalThreshold q ell
      <= 2^37 * q^6 * ell * (log_2 q + 1)^3
    ```

11. Close the conditional numerical endpoint:

    ```text
    K * g^7 * (log_2 g)^b <= treewidth G
      -> ContainsGridMinor G g
    ```

## Sole remaining mathematical theorem

Prove, for some explicit `reserve > 0`:

```lean
CleanMatchingDichotomyStatement reserve
```

This says that a sufficiently wide node-well-linked cluster either already
contains the target grid or realizes an arbitrary prescribed matching on the
selected rows by pairwise node-disjoint row-clean bridges.

The proved `cleanBridgeBatch_of_nodeWellLinked` supplies a linear-size clean
matching chosen by the graph.  What remains is endpoint control: convert that
matching to the prescribed odd/even matching, or extract the grid when the
conversion fails.

No slicing, arithmetic, contraction provenance, treewidth, minor, or global
stitching obligation remains behind this interface.
